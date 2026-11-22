module

public import LeanQbe.T.Examples.Kissat.FullSweepVarLemmas1

/-!
# Kissat `D-Full` SAT-Sweeping Top Shard — Part 2 (`Stage 4`)

Parametric `(Γ : Env)` `Func.wp` UNSAT-only proofs for:
2. `full_sweep_var` (`full_sweep_var_wp`, `Full.lean:484-535`)
3. `full_sweep_sat` (`full_sweep_sat_wp`, `Full.lean:537-554`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test
open FullSweepVarSpecs

private theorem bv32_add1_lt {x : BitVec 32} (h : x.toNat < 2 ^ 31) :
    (x + 1#32).toNat = x.toNat + 1 := by bv_omega

private theorem bv64_add1_lt {x : BitVec 64} (h : x.toNat < 2 ^ 63) :
    (x + 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  simp [Nat.mod_eq_of_lt (by omega : x.toNat + 1 < 2 ^ 64)]

/-! ## 1. `full_sweep_var_wp` (`Full.lean` #16) -/

section SweepVar
open FullSweepVarHelpers
open scoped FullArenaTactics FullSweepVarTactics

private theorem sweep_var_tmk_clear_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {sX : FullState}
    {R : Mem 64 → Prop} {nv : BitVec 32} {ws1' tmk' : List (BitVec 32)}
    {pWorkStk1 pTarjanMark : BitVec 64} {mX : Mem 64}
    {cont : Expr Val Cont rs}
    (hpws : pWorkStk1 = c.pWorkStk1) (hptmk : pTarjanMark = c.pTarjanMark)
    (hnv_mx : nv.toNat ≤ 2 * c.max_vars) (hinvX : FullDenseInvW c F0 F_cur sX)
    (hwsX : sX.scratch.work_stk1 = ws1') (htmkX : sX.scratch.tarjan_mark = tmk')
    (hconeX : ∀ i < nv.toNat, (sX.scratch.work_stk1[i]?.getD 0#32).toNat < sX.core.cur_vars)
    (htmk1' : ∀ u < sX.core.cur_vars, tmk'[u]?.getD 0#32 ≠ 0xFFFFFFFF#32 →
      ∃ k < nv.toNat, (ws1'[k]?.getD 0#32).toNat = u)
    (hmX : (FullMem c sX ⋆ R) mX)
    (hcont : ∀ (tmk_c : List (BitVec 32)) m_end,
      tmk_c.length = 2 * c.max_vars →
      (∀ u < sX.core.cur_vars, tmk_c[u]?.getD 0#32 = 0xFFFFFFFF#32) →
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
                                Expr.store (t := i32) (Arg.imm 0xFFFFFFFF) (Arg.var p_7.fst)
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
      (∀ u < sX.core.cur_vars, tmk_c[u]?.getD 0#32 ≠ 0xFFFFFFFF#32 →
        ∃ k, i.toNat ≤ k ∧ k < nv.toNat ∧ (ws1'[k]?.getD 0#32).toNat = u) ∧
      (FullMem c { sX with scratch := { sX.scratch with tarjan_mark := tmk_c } } ⋆ R) mi)
    (fun (i, ()) _ => nv.toNat - i.toNat)
    (fun Jc hLc => by
      fsv_steps
      exact hLc (0#32, ()) mX ⟨Nat.zero_le _, tmk',
        htmkX ▸ hinvX.1.scratch_ok.tarjan_mark_len,
        fun u hu hne => let ⟨k, hk, hwk⟩ := htmk1' u hu hne; ⟨k, Nat.zero_le _, hk, hwk⟩,
        htmkX_sym ▸ hmX⟩)
    (fun Jc (i, ()) mi ⟨hi_le, tmk_c, ht_len, ht_inv, hmi⟩ hLc => by
      c0_split
      · have hi_lt : i.toNat < nv.toNat := by c0_bound
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
          rw [hws_len]; simp only [BitVec.toNat_setWidth]; omega
        have hwsX_eq : ({ sX with scratch := { sX.scratch with tarjan_mark := tmk_c } } :
            FullState).scratch.work_stk1 = ws1' := hwsX
        have hgv_tmk : (BitVec.setWidth 64 (({ sX with scratch :=
            { sX.scratch with tarjan_mark := tmk_c } } :
            FullState).scratch.work_stk1[(BitVec.setWidth 64 i).toNat]'hi_ws)).toNat <
            ({ sX with scratch := { sX.scratch with tarjan_mark := tmk_c } } :
              FullState).scratch.tarjan_mark.length :=
          tmk_idx_lt hwsX_eq (by rw [← hwsX, hws_len]; omega)
            (by rw [ht_len]; exact hv_lt) hi_ws
        have hi1 : (i + 1#32).toNat = i.toNat + 1 := bv32_add1_lt (by omega)
        fsv_steps
        refine hLc (i + 1#32, ()) _ (by dsimp only; omega)
          ⟨by omega, _, List.length_set.trans ht_len,
            tmk_clear_step64 hi_lt hi1 hwsX_eq (by rw [← hwsX, hws_len]; omega)
              (by rw [ht_len]; exact hv_lt) ht_inv,
            by c0_frame⟩
      · exact hcont tmk_c mi ht_len (tmk_clear_done (by c0_bound) ht_inv) hmi)

private theorem sweep_var_add_bins_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    (haddB : EnvSpec Γ "full_add_bin" fullAddBinSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {sB : FullState}
    {R : Mem 64 → Prop} {nv nc : Nat} {ws1' tmk' : List (BitVec 32)}
    {hdrPtr : BitVec 64} {rl1 rl ol : BitVec 32} {mB : Mem 64}
    {Jret Jnext : Cont []}
    (hhdr : hdrPtr = c.hdr)
    (hinvB : FullDenseInvW c F0 F_cur sB)
    (hwsB : sB.scratch.work_stk1 = ws1') (htmkB : sB.scratch.tarjan_mark = tmk')
    (hconeB : FullSweepConeOk F_cur sB nv nc)
    (hent1 : (cnfOfClauses F_cur).EntailsClause (cnfClause [rl1.toNat, ol.toNat]))
    (hent2 : (cnfOfClauses F_cur).EntailsClause (cnfClause [rl.toNat, (ol ^^^ 1#32).toNat]))
    (hmB : (FullMem c sB ⋆ R) mB)
    (hJret : ∀ sX mX, FullDenseInvW c F0 F_cur sX → sX.core.cur_vars = sB.core.cur_vars →
      sX.core.fuel.toNat ≤ sB.core.fuel.toNat → sX.scratch.work_stk1 = ws1' →
      sX.scratch.tarjan_mark = tmk' → FullSweepConeOk F_cur sX nv nc →
      F0.Unsat → (FullMem c sX ⋆ R) mX → Jret () mX)
    (hJnext : ∀ sX mX, FullDenseInvW c F0 F_cur sX → sX.core.cur_vars = sB.core.cur_vars →
      sX.core.fuel.toNat ≤ sB.core.fuel.toNat → sX.scratch.work_stk1 = ws1' →
      sX.scratch.tarjan_mark = tmk' → FullSweepConeOk F_cur sX nv nc →
      (FullMem c sX ⋆ R) mX → Jnext () mX) :
    wp Γ Q X
      (Expr.call (as := [i64, i32, i32]) (rs := [i64]) "full_add_bin"
        (Arg.var hdrPtr, Arg.var rl1, Arg.var ol, ())
        fun (p : Tup Val [i64]) =>
        Expr.let_ (Op.mk (OpCode.cmp CmpOp.eq i64) (Arg.var p.fst, Arg.imm 20, ())) fun p =>
          Expr.jnz (Arg.var p.fst) (Expr.jump Jret ())
            (Expr.let_ (Op.mk (OpCode.xor i32) (Arg.var ol, Arg.imm 1, ())) fun p =>
              Expr.call (as := [i64, i32, i32]) (rs := [i64]) "full_add_bin"
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
                              (Expr.jump Jnext ()))))
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
  have hconeC : FullSweepConeOk F_cur sC nv nc :=
    hsC ▸ fullSweepConeOk_with_scratch hconeB rfl rfl rfl (fun _ _ => rfl)
  have hwsC : sC.scratch.work_stk1 = ws1' := by rw [hsC]; exact hwsB
  have htmkC : sC.scratch.tarjan_mark = tmk' := by rw [hsC]; exact htmkB
  have hcvC : sC.core.cur_vars = sB.core.cur_vars := by rw [hsC]
  have hfuelC : sC.core.fuel.toNat ≤ sB.core.fuel.toNat := by rw [hsC]; exact Nat.le_refl _
  have hmC' : (FullMem c sC ⋆ R) mC := hsC ▸ hmC
  c0_split
  · have hrb1_20 : rb1 = 20#64 := by c0_bound
    fsv_steps
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
    have hconeD : FullSweepConeOk F_cur sD nv nc :=
      hsD ▸ fullSweepConeOk_with_scratch hconeC rfl rfl rfl (fun _ _ => rfl)
    have hwsD : sD.scratch.work_stk1 = ws1' := by rw [hsD]; exact hwsC
    have htmkD : sD.scratch.tarjan_mark = tmk' := by rw [hsD]; exact htmkC
    have hcvD : sD.core.cur_vars = sB.core.cur_vars := by rw [hsD]; exact hcvC
    have hfuelD : sD.core.fuel.toNat ≤ sB.core.fuel.toNat := by rw [hsD]; exact hfuelC
    have hmD' : (FullMem c sD ⋆ R) mD := hsD ▸ hmD
    c0_split
    · have hrb2_20 : rb2 = 20#64 := by c0_bound
      fsv_steps
      exact hJret sD mD hinvD hcvD hfuelD hwsD htmkD hconeD (hrb2_uns hrb2_20).1 hmD'
    · fsv_steps
      exact hJnext _ _ (fullDenseInvW_with_sweep_cnt hinvD (sD.scratch.sweep_cnt + 1#64))
        hcvD hfuelD hwsD htmkD
        (fullSweepConeOk_with_scratch hconeD rfl rfl rfl (fun _ _ => rfl))
        (by assumption)

theorem full_sweep_var_wp (Γ : Env)
    (hcone : EnvSpec Γ "full_sweep_cone" fullSweepConeSpec)
    (hseed : EnvSpec Γ "full_sweep_seed_sim" fullSweepSeedSimSpec)
    (hdpll : EnvSpec Γ "full_sweep_dpll" fullSweepDpllSpec)
    (hrefine : EnvSpec Γ "full_sweep_refine" fullSweepRefineSpec)
    (haddU : EnvSpec Γ "full_add_unit" fullAddUnitSpec)
    (haddB : EnvSpec Γ "full_add_bin" fullAddBinSpec) :
    ∀ args m Q X, fullSweepVarSpec args m Q X →
      Func.wp Γ full_sweep_var_body args m Q X := by
  rintro ⟨h, root_v, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hinv, hcap, hroot_lt, htmk, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hinv.1.core_ok.cur_vars_le
  have hroot_lt31 : root_v.toNat < 2 ^ 31 := by omega
  fsv_steps
  c0_call hcone
  refine ⟨c, F0, F_cur, s, R, rfl, hinv, hcap, hroot_lt, htmk, hm, ?_⟩
  intro pk tmp' ws1' tmk' scr' rsz' m1 _ _ _ hinv1 hnv_pos hcone1 hws0 htmk1 hm1
  let s1 : FullState :=
    { s with
      core := { s.core with tmp := tmp' }
      scratch := { s.scratch with
        work_stk1 := ws1', tarjan_mark := tmk', scratch_buf := scr', res_sz := rsz' } }
  let nv : BitVec 32 := (pk &&& 0xFFFF#64).setWidth 32
  let nc : BitVec 32 := (pk >>> (16 : Nat)).setWidth 32
  have hnv_24 : nv.toNat ≤ 24 := by
    change ((pk &&& 0xFFFF#64).setWidth 32).toNat ≤ 24
    rw [bv64_to32_toNat _ (by have := hcone1.1; omega)]
    exact hcone1.1
  have hnc_64 : nc.toNat ≤ 64 := by
    change ((pk >>> 16).setWidth 32).toNat ≤ 64
    rw [bv64_to32_toNat _ (by have := hcone1.2.2.1; omega)]
    exact hcone1.2.2.1
  have hnv_eq : nv.toNat = (pk &&& 0xFFFF#64).toNat :=
    bv64_to32_toNat _ (by have := hcone1.1; omega)
  have hnc_eq : nc.toNat = (pk >>> (16 : Nat)).toNat :=
    bv64_to32_toNat _ (by have := hcone1.2.2.1; omega)
  have hnv_pos' : 1 ≤ nv.toNat := hnv_eq.symm ▸ hnv_pos
  have hcone1' : FullSweepConeOk F_cur s1 nv.toNat nc.toNat := by
    rw [hnv_eq, hnc_eq]; exact hcone1
  have hinv1' : FullDenseInvW c F0 F_cur s1 := hinv1
  have hws1_len : ws1'.length = 2 * c.max_vars := hinv1.1.scratch_ok.work_stk1_len
  have htmk1_len : tmk'.length = 2 * c.max_vars := hinv1.1.scratch_ok.tarjan_mark_len
  have htmk1' : ∀ v < s.core.cur_vars, tmk'[v]?.getD 0#32 ≠ 0xFFFFFFFF#32 →
      ∃ i < nv.toNat, (ws1'[i]?.getD 0#32).toNat = v :=
    fun v hv hne => let ⟨k, hk, hwk⟩ := htmk1 v hv hne; ⟨k, hnv_eq ▸ hk, hwk⟩
  have hnv_cv : nv.toNat ≤ s.core.cur_vars := hcone1'.2.1
  have hnv_mx : nv.toNat ≤ 2 * c.max_vars := by omega
  fsv_group
  -- Early exit: if (nv < 2u || nc == 0u)
  refine wp_join_group
    (fun (_ : Tup Val []) mJ => mJ = m1)
    (fun _ () mJ hmJ => by
      subst hmJ
      fsv_group
      refine sweep_var_tmk_clear_wp rfl rfl hnv_mx hinv1' rfl rfl hcone1'.2.2.2.2.2.1 htmk1' hm1 ?_
      intro tmk_c m_end ht_len ht_done hm_end
      fsv_steps
      exact hQ 1#64 _ m_end (fullDenseInvW_with_tmk hinv1' ht_len) rfl (Nat.le_refl _) ht_done
        (Or.inl rfl) (fun h => by cases h) hm_end)
    (fun Jflg hJflg => by
      fsv_steps
      · exact hJflg () m1 rfl
      · exact hJflg () m1 rfl
      · have hnv_ge2 : 2 ≤ nv.toNat := by
          have : ¬ nv.toNat < 2 := by c0_bound
          omega
        c0_call hseed
        refine ⟨c, F_cur, s1, R, rfl, hinv1'.1, hcap, hnv_pos', hcone1', hm1, ?_⟩
        intro rbit fuel2 scr2 rng2 sig2 m2 _ hlen2 hfuel2 hscr2 hcone2 hunsat2 hm2
        let s2 : FullState :=
          { s1 with
            core := { s1.core with fuel := fuel2 }
            scratch := { s1.scratch with scratch_buf := scr2, rng_state := rng2, sim_sig := sig2 } }
        have hinv2 : FullDenseInvW c F0 F_cur s2 :=
          fullDenseInvW_with_fuel_scratch hinv1' hlen2.scratch_ok rfl rfl
        c0_split
        · have hrbit_ff : rbit = 0xFFFFFFFF#32 := by c0_bound
          have hunsat_f0 : F0.Unsat := hinv2.2.1.ext_sound.2 (hunsat2 hrbit_ff)
          fsv_group
          refine sweep_var_tmk_clear_wp rfl rfl hnv_mx hinv2 rfl rfl
            hcone2.2.2.2.2.2.1 htmk1' hm2 ?_
          intro tmk_c m_end ht_len ht_done hm_end
          fsv_steps
          have hinv2' := fullDenseInvW_with_inconsistent
            (fullDenseInvW_with_tmk hinv2 ht_len) (hunsat2 hrbit_ff)
          exact hQ 20#64 _ _ hinv2' rfl hfuel2 ht_done (Or.inr rfl)
            (fun _ => hunsat_f0) (by assumption)
        · fsv_group
          -- smask := ...
          refine wp_join_group (ts := [i64])
            (fun (smask, ()) mJ2 => mJ2 = m2)
            (fun _ (smask, ()) mJ2 hmJ2 => by
              subst mJ2
              have hsig2_len : s2.scratch.sim_sig.length = c.max_vars :=
                hinv2.1.scratch_ok.sim_sig_len
              have hroot_sig : (BitVec.setWidth 64 root_v).toNat <
                  s2.scratch.sim_sig.length := by
                rw [hsig2_len]; simp only [BitVec.toNat_setWidth]; omega
              fsv_group
              -- Unit check block: if (rbit > 0 && (s0 == 0 || s0 == smask))
              refine wp_join_group (ts := [i32, i64])
                (fun (rbit3, smask3, ()) m3 =>
                  ∃ s3, FullDenseInvW c F0 F_cur s3 ∧
                    s3.core.cur_vars = s.core.cur_vars ∧
                    s3.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                    FullSweepConeOk F_cur s3 nv.toNat nc.toNat ∧
                    s3.scratch.work_stk1 = ws1' ∧
                    s3.scratch.tarjan_mark = tmk' ∧
                    (FullMem c s3 ⋆ R) m3)
                (fun _ x3 m3 h3 => by
                  rcases x3 with ⟨rbit3, smask3, ⟨⟩⟩
                  rcases h3 with ⟨s3, hinv3, hcv3, hfuel3, hcone3, hws3, htmk3, hm3⟩
                  fsv_group
                  refine wp_loop_inv (ts := [i32, i64, i32])
                    (fun (rbitL, smaskL, j, ()) ml =>
                      j.toNat ≤ nv.toNat ∧ ∃ sL,
                        FullDenseInvW c F0 F_cur sL ∧
                        sL.core.cur_vars = s.core.cur_vars ∧
                        sL.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                        FullSweepConeOk F_cur sL nv.toNat nc.toNat ∧
                        sL.scratch.work_stk1 = ws1' ∧
                        sL.scratch.tarjan_mark = tmk' ∧
                        (FullMem c sL ⋆ R) ml)
                    (fun (_, _, j, ()) _ => nv.toNat - j.toNat)
                    (fun JL hLoopL => by
                      fsv_steps
                      exact hLoopL (rbit3, smask3, 1#32, ()) m3
                        ⟨by simp; omega, s3, hinv3, hcv3, hfuel3, hcone3, hws3, htmk3, hm3⟩)
                    (fun JL (rbitL, smaskL, j, ()) ml
                        ⟨hj_le, sL, hinvL, hcvL, hfuelL, hconeL, hwsL, htmkL, hml⟩ hLoopL => by
                      c0_split
                      rotate_left 1
                      · -- ¬ j < nv
                        fsv_group
                        refine sweep_var_tmk_clear_wp rfl rfl hnv_mx hinvL hwsL htmkL
                          hconeL.2.2.2.2.2.1 (fun u hu => htmk1' u (hcvL ▸ hu)) hml ?_
                        intro tmk_c m_end ht_len ht_done hm_end
                        fsv_steps
                        exact hQ 1#64 _ m_end (fullDenseInvW_with_tmk hinvL ht_len) hcvL hfuelL
                          (hcvL ▸ ht_done) (Or.inl rfl) (fun h => by cases h) hm_end
                      c0_split
                      rotate_left 1
                      · -- ¬ inconsistent == 0
                        fsv_group
                        refine sweep_var_tmk_clear_wp rfl rfl hnv_mx hinvL hwsL htmkL
                          hconeL.2.2.2.2.2.1 (fun u hu => htmk1' u (hcvL ▸ hu)) hml ?_
                        intro tmk_c m_end ht_len ht_done hm_end
                        fsv_steps
                        exact hQ 1#64 _ m_end (fullDenseInvW_with_tmk hinvL ht_len) hcvL hfuelL
                          (hcvL ▸ ht_done) (Or.inl rfl) (fun h => by cases h) hm_end
                      -- Main j-loop body (j < nv ∧ inconsistent == 0)
                      have hj_lt : j.toNat < nv.toNat := by c0_bound
                      have hwsL_len := hinvL.1.scratch_ok.work_stk1_len
                      have hsigL_len := hinvL.1.scratch_ok.sim_sig_len
                      have hov_lt :
                          (ws1'[j.toNat]'(by rw [← hwsL]; omega)).toNat < s.core.cur_vars := by
                        have := hconeL.2.2.2.2.2.1 j.toNat hj_lt
                        rw [hwsL, List.getElem?_eq_getElem (by rw [hwsL] at hwsL_len; omega),
                          Option.getD_some] at this
                        omega
                      have hj1 : (j + 1#32).toNat = j.toNat + 1 := bv32_add1_lt (by omega)
                      have hj_ws : (BitVec.setWidth 64 j).toNat <
                          sL.scratch.work_stk1.length := by
                        rw [hwsL_len]; simp only [BitVec.toNat_setWidth]; omega
                      have hgv_sig : (BitVec.setWidth 64
                          (sL.scratch.work_stk1[(BitVec.setWidth 64 j).toNat]'hj_ws)).toNat <
                          sL.scratch.sim_sig.length :=
                        tmk_idx_lt hwsL (by rw [hws1_len]; omega)
                          (by rw [hsigL_len]; exact lt_of_lt_of_le hov_lt hcv_le) hj_ws
                      have hroot_sigL : (BitVec.setWidth 64 root_v).toNat <
                          sL.scratch.sim_sig.length := by
                        rw [hsigL_len]; simp only [BitVec.toNat_setWidth]; omega
                      fsv_group
                      refine wp_join_group (ts := [i32, i64])
                        (fun (rbitN, smaskN, ()) mN =>
                          ∃ sN, FullDenseInvW c F0 F_cur sN ∧
                            sN.core.cur_vars = s.core.cur_vars ∧
                            sN.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                            FullSweepConeOk F_cur sN nv.toNat nc.toNat ∧
                            sN.scratch.work_stk1 = ws1' ∧
                            sN.scratch.tarjan_mark = tmk' ∧
                            (FullMem c sN ⋆ R) mN)
                        (fun _ (rbitN, smaskN, ()) mN hN => by
                          rcases hN with ⟨sN, hinvN, hcvN, hfuelN, hconeN, hwsN, htmkN, hmN⟩
                          fsv_steps
                          exact hLoopL (rbitN, smaskN, j + 1#32, ()) mN (by dsimp only; omega)
                            ⟨by omega, sN, hinvN, hcvN, hfuelN, hconeN, hwsN, htmkN, hmN⟩)
                        (fun Jif hJif => by
                          let ov := ws1'[j.toNat]'(by rw [← hwsL]; omega)
                          have hov_lt31 : ov.toNat < 2 ^ 31 := lt_trans hov_lt (by omega)
                          have hws_eqL : sL.scratch.work_stk1.length = 2 * c.max_vars := hwsL_len
                          have hsig_eqL : sL.scratch.sim_sig.length = c.max_vars := hsigL_len
                          have hov_sig : ov.toNat < sL.scratch.sim_sig.length := by
                            rw [hsig_eqL]; exact lt_of_lt_of_le hov_lt hcv_le
                          have hroot_sig : root_v.toNat < sL.scratch.sim_sig.length := by
                            rw [hsig_eqL]; exact lt_of_lt_of_le hroot_lt hcv_le
                          c0_split
                          · fsv_group
                            refine wp_join_group (ts := [])
                              (fun (_ : Tup Val []) mJ => mJ = ml)
                              (fun _ () mJ hmJ => by
                                subst mJ
                                fsv_group
                                refine wp_join_group (ts := [i32])
                                  (fun (pol, ()) mP => mP = ml ∧ (pol = 0#32 ∨ pol = 1#32))
                                  (fun _ (pol, ()) mP ⟨hmP, hpol⟩ => by
                                    subst mP
                                    c0_call hdpll
                                    refine ⟨c, F_cur, sL, R, rfl, hinvL.1, hcap, hconeL, hml, ?_⟩
                                    intro d1 fuelA scrA rngA mA _ hlenA hfuelA hscrA hconeA0 hd1
                                      huns1 hmA
                                    obtain ⟨sA, hsA⟩ : ∃ sA : FullState, sA =
                                      { sL with
                                        core := { sL.core with fuel := fuelA }
                                        scratch := { sL.scratch with
                                          scratch_buf := scrA, rng_state := rngA } } := ⟨_, rfl⟩
                                    have hinvA : FullDenseInvW c F0 F_cur sA :=
                                      hsA ▸ fullDenseInvW_with_fuel_scratch hinvL hlenA.scratch_ok
                                        rfl rfl
                                    have hconeA : FullSweepConeOk F_cur sA nv.toNat nc.toNat :=
                                      hsA ▸ hconeA0
                                    have hlenA' : sA.LengthsOk c := hsA ▸ hlenA
                                    have hwsA : sA.scratch.work_stk1 = ws1' := by
                                      rw [hsA]; exact hwsL
                                    have htmkA : sA.scratch.tarjan_mark = tmk' := by
                                      rw [hsA]; exact htmkL
                                    have hcvA : sA.core.cur_vars = s.core.cur_vars := by
                                      rw [hsA]; exact hcvL
                                    have hfuelA0 : sA.core.fuel.toNat ≤ s.core.fuel.toNat := by
                                      rw [hsA]; exact Nat.le_trans hfuelA hfuelL
                                    have hmA1 : (FullMem c sA ⋆ R) mA := hsA ▸ hmA
                                    fsv_steps
                                    · -- d1 == 10 && rbitL < 64
                                      c0_call hrefine
                                      refine ⟨c, sA, R, rfl, hlenA', hcap, hnv_24, hnv_mx,
                                        hconeA.2.2.2.2.2.1, hmA1, ?_⟩
                                      intro sigA mA' hsigA hmA'
                                      have hrL64 : rbitL.toNat < 64 := by c0_bound
                                      have hrL64_w : (BitVec.setWidth 64 rbitL).toNat < 64 := by
                                        simp only [BitVec.toNat_setWidth]; omega
                                      have hrL1 : (rbitL + 1#32).toNat = rbitL.toNat + 1 :=
                                        bv32_add1_lt (by omega)
                                      fsv_steps
                                      fsv_unwind_j
                                      exact hJif _ mA' ⟨_, fullDenseInvW_after_refine hinvA hsigA,
                                        hcvA, hfuelA0,
                                        fullSweepConeOk_with_scratch hconeA rfl rfl rfl
                                          (fun _ _ => rfl),
                                        hwsA, htmkA, hmA'⟩
                                    · -- d1 == 10 && ¬ rbitL < 64
                                      fsv_unwind_j
                                      exact hJif (rbitL, smaskL, ()) mA
                                        ⟨sA, hinvA, hcvA, hfuelA0, hconeA, hwsA, htmkA, hmA1⟩
                                    · -- d1 == 20
                                      have hd1_20 : d1 = 20#64 := by c0_bound
                                      c0_call hdpll
                                      refine ⟨c, F_cur, sA, R, rfl, hlenA', hcap, hconeA, hmA1, ?_⟩
                                      intro d2 fuelB scrB rngB mB _ hlenB hfuelB hscrB hconeB0 hd2
                                        huns2 hmB
                                      obtain ⟨sB, hsB⟩ : ∃ sB : FullState, sB =
                                        { sA with
                                          core := { sA.core with fuel := fuelB }
                                          scratch := { sA.scratch with
                                            scratch_buf := scrB, rng_state := rngB } } := ⟨_, rfl⟩
                                      have hinvB : FullDenseInvW c F0 F_cur sB :=
                                        hsB ▸ fullDenseInvW_with_fuel_scratch hinvA
                                          hlenB.scratch_ok rfl rfl
                                      have hconeB : FullSweepConeOk F_cur sB nv.toNat nc.toNat :=
                                        hsB ▸ hconeB0
                                      have hlenB' : sB.LengthsOk c := hsB ▸ hlenB
                                      have hwsB : sB.scratch.work_stk1 = ws1' := by
                                        rw [hsB]; exact hwsA
                                      have htmkB : sB.scratch.tarjan_mark = tmk' := by
                                        rw [hsB]; exact htmkA
                                      have hcvB : sB.core.cur_vars = s.core.cur_vars := by
                                        rw [hsB]; exact hcvA
                                      have hfuelB0 : sB.core.fuel.toNat ≤ s.core.fuel.toNat := by
                                        rw [hsB]; exact Nat.le_trans hfuelB hfuelA0
                                      have hmB1 : (FullMem c sB ⋆ R) mB := hsB ▸ hmB
                                      fsv_steps
                                      · -- d2 == 10 && rbitL < 64
                                        c0_call hrefine
                                        refine ⟨c, sB, R, rfl, hlenB', hcap, hnv_24, hnv_mx,
                                          hconeB.2.2.2.2.2.1, hmB1, ?_⟩
                                        intro sigB mB' hsigB hmB'
                                        have hrL64_w : (BitVec.setWidth 64 rbitL).toNat < 64 := by
                                          have : rbitL.toNat < 64 := by c0_bound
                                          simp only [BitVec.toNat_setWidth]; omega
                                        fsv_steps
                                        fsv_unwind_j
                                        exact hJif _ mB' ⟨_, fullDenseInvW_after_refine hinvB hsigB,
                                          hcvB, hfuelB0,
                                          fullSweepConeOk_with_scratch hconeB rfl rfl rfl
                                            (fun _ _ => rfl),
                                          hwsB, htmkB, hmB'⟩
                                      · -- d2 == 10 && ¬ rbitL < 64
                                        fsv_unwind_j
                                        exact hJif (rbitL, smaskL, ()) mB
                                          ⟨sB, hinvB, hcvB, hfuelB0, hconeB, hwsB, htmkB, hmB1⟩
                                      · -- d2 == 20 -> full_add_bin
                                        have hd2_20 : d2 = 20#64 := by c0_bound
                                        have hent1 :=
                                          fullSweepDpllUnsat_bin1
                                            (root_v := root_v) (ov := ov) hnv_24 hj_lt
                                            (by rw [hwsL]; exact hws0)
                                            (by
                                              rw [hwsL, List.getElem?_eq_getElem
                                                (by rw [hwsL] at hwsL_len; omega),
                                                Option.getD_some])
                                            hpol (by omega) hov_lt31 (huns1 hd1_20)
                                        have hent2 :=
                                          fullSweepDpllUnsat_bin2
                                            (root_v := root_v) (ov := ov) hnv_24 hj_lt
                                            (by rw [hwsA]; exact hws0)
                                            (by
                                              rw [hwsA, List.getElem?_eq_getElem
                                                (by
                                                  have := hinvA.1.scratch_ok.work_stk1_len
                                                  rw [hwsA] at this; omega),
                                                Option.getD_some])
                                            hpol (by omega) hov_lt31 (huns2 hd2_20)
                                        have hov_eq :
                                            sL.scratch.work_stk1[(BitVec.setWidth 64 j).toNat]'(by
                                              rw [hwsL_len]; simp only [BitVec.toNat_setWidth]
                                              omega) = ov :=
                                          Option.some.inj (by
                                            simp only [BitVec.toNat_setWidth,
                                              Nat.mod_eq_of_lt (by omega : j.toNat < 2 ^ 64)]
                                            rw [← List.getElem?_eq_getElem, hwsL,
                                              List.getElem?_eq_getElem])
                                        have hent1' :
                                            (cnfOfClauses F_cur).EntailsClause (cnfClause
                                              [((root_v <<< (1 : Nat)) ^^^ 1#32).toNat,
                                                (((sL.scratch.work_stk1[
                                                  (BitVec.setWidth 64 j).toNat]'hj_ws) <<<
                                                  (1 : Nat)) ||| pol).toNat]) := by
                                          rw [hov_eq]; exact hent1
                                        have hent2' :
                                            (cnfOfClauses F_cur).EntailsClause (cnfClause
                                              [(root_v <<< (1 : Nat)).toNat,
                                                ((((sL.scratch.work_stk1[
                                                  (BitVec.setWidth 64 j).toNat]'hj_ws) <<<
                                                  (1 : Nat)) ||| pol) ^^^ 1#32).toNat]) := by
                                          rw [hov_eq]; exact hent2
                                        refine sweep_var_add_bins_wp haddB rfl hinvB hwsB htmkB
                                          hconeB hent1' hent2' hmB1
                                          (fun sX mX hinvX hcvX hfuelX hwsX htmkX hconeX hunsX
                                              hmX => by
                                            fsv_steps
                                            fsv_unwind_j
                                            fsv_group
                                            refine sweep_var_tmk_clear_wp rfl rfl hnv_mx hinvX
                                              hwsX htmkX hconeX.2.2.2.2.2.1
                                              (fun u hu => htmk1' u (hcvB ▸ hcvX ▸ hu)) hmX ?_
                                            intro tmk_c m_end ht_len ht_done hm_end
                                            fsv_steps
                                            exact hQ 20#64 _ m_end
                                              (fullDenseInvW_with_tmk hinvX ht_len)
                                              (hcvX.trans hcvB) (Nat.le_trans hfuelX hfuelB0)
                                              ht_done (Or.inr rfl) (fun _ => hunsX) hm_end)
                                          (fun sX mX hinvX hcvX hfuelX hwsX htmkX hconeX hmX => by
                                            fsv_steps
                                            fsv_unwind_j
                                            exact hJif (rbitL, smaskL, ()) mX
                                              ⟨sX, hinvX, hcvX.trans hcvB,
                                                Nat.le_trans hfuelX hfuelB0,
                                                hconeX, hwsX, htmkX, hmX⟩)
                                      · fsv_unwind_j
                                        exact hJif (rbitL, smaskL, ()) mB
                                          ⟨sB, hinvB, hcvB, hfuelB0, hconeB, hwsB, htmkB, hmB1⟩
                                    · fsv_unwind_j
                                      exact hJif (rbitL, smaskL, ()) mA
                                        ⟨sA, hinvA, hcvA, hfuelA0, hconeA, hwsA, htmkA, hmA1⟩)
                                  (fun Jpol hJpol => by
                                    fsv_steps
                                    · exact hJpol (0#32, ()) ml ⟨rfl, Or.inl rfl⟩
                                    · exact hJpol (1#32, ()) ml ⟨rfl, Or.inr rfl⟩))
                              (fun Jdo hdo => by
                                fsv_steps
                                · exact hdo () ml rfl
                                · exact hdo () ml rfl
                                · exact hJif (rbitL, smaskL, ()) ml
                                    ⟨sL, hinvL, hcvL, hfuelL, hconeL, hwsL, htmkL, hml⟩)
                          · fsv_steps
                            exact hJif (rbitL, smaskL, ()) ml
                              ⟨sL, hinvL, hcvL, hfuelL, hconeL, hwsL, htmkL, hml⟩)))
                (fun Ju hJu => by
                  c0_split
                  · fsv_group
                    refine wp_join_group (ts := [])
                      (fun (_ : Tup Val []) mJ => mJ = m2)
                      (fun _ () mJ hmJ => by
                        subst mJ
                        fsv_group
                        refine wp_join_group (ts := [i32])
                          (fun (test, ()) mT => mT = m2 ∧ (test = 0#32 ∨ test = 1#32))
                          (fun _ (test, ()) mT ⟨hmT, htest⟩ => by
                            subst mT
                            c0_call hdpll
                            refine ⟨c, F_cur, s2, R, rfl, hlen2, hcap, hcone2, hm2, ?_⟩
                            intro dU fuelU scrU rngU mU _ hlenU hfuelU hscrU hconeU0 hdU hunsU hmU
                            obtain ⟨sU, hsU⟩ : ∃ sU : FullState, sU =
                              { s2 with
                                core := { s2.core with fuel := fuelU }
                                scratch := { s2.scratch with
                                  scratch_buf := scrU, rng_state := rngU } } := ⟨_, rfl⟩
                            have hinvU : FullDenseInvW c F0 F_cur sU :=
                              hsU ▸ fullDenseInvW_with_fuel_scratch hinv2 hlenU.scratch_ok rfl rfl
                            have hconeU : FullSweepConeOk F_cur sU nv.toNat nc.toNat :=
                              hsU ▸ hconeU0
                            have hlenU' : sU.LengthsOk c := hsU ▸ hlenU
                            have hcvU : sU.core.cur_vars = s.core.cur_vars := by rw [hsU]
                            have hfuelU0 : sU.core.fuel.toNat ≤ s.core.fuel.toNat := by
                              rw [hsU]; exact Nat.le_trans hfuelU hfuel2
                            have hmU1 : (FullMem c sU ⋆ R) mU := hsU ▸ hmU
                            fsv_steps
                            · -- dU == 20
                              have hdU20 : dU = 20#64 := by c0_bound
                              have hentU := fullSweepDpllUnsat_unit hnv_ge2 hnv_24 hws0
                                htest hroot_lt31 (hunsU hdU20)
                              have hlitU_lt : ((root_v <<< (1 : Nat)) |||
                                  (1#32 - test)).toNat < 2 * sU.core.cur_vars := by
                                have h1sub : (1#32 - test).toNat < 2 := by
                                  rcases htest with rfl | rfl <;> decide
                                rw [bv32_shl1_or_pol root_v (1#32 - test) hroot_lt31 h1sub,
                                  bv32_1_sub_toNat test htest]
                                rw [hcvU]; omega
                              c0_call haddU
                              refine ⟨c, F0, F_cur, sU, R, rfl, hlenU', hinvU.2.1,
                                fun _ => hentU, hmU1, ?_⟩
                              intro okU valsU flagsU lvlU rsnsU trlU tpU teU propU clU
                                unassU unflU incU scU mV _ hlenV hwV hpresV hclV hokF
                                hokF2 hmV
                              obtain ⟨sV, hsV⟩ : ∃ sV : FullState, sV =
                                { sU with
                                  core := { sU.core with
                                    vals := valsU, flags := flagsU, lvl := lvlU,
                                    rsns := rsnsU, trl := trlU, trail_pos := tpU,
                                    trail_end := teU, propagated := propU, cur_level := clU,
                                    unassigned := unassU, unflushed := unflU,
                                    inconsistent := incU }
                                  scratch := scU } := ⟨_, rfl⟩
                              have hinvV := hsV ▸ fullDenseInvW_after_addUnit hinvU
                                { sU with
                                  core := { sU.core with
                                    vals := valsU, flags := flagsU, lvl := lvlU,
                                    rsns := rsnsU, trl := trlU, trail_pos := tpU,
                                    trail_end := teU, propagated := propU, cur_level := clU,
                                    unassigned := unassU, unflushed := unflU,
                                    inconsistent := incU }
                                  scratch := scU } rfl hlenV hwV hpresV hclV
                              have hconeV : FullSweepConeOk F_cur sV nv.toNat nc.toNat :=
                                hsV ▸ fullSweepConeOk_with_scratch hconeU rfl hpresV.2.1
                                  hpresV.2.2.2.2.2.2.1 (fun i hi => by rw [hpresV.2.2.2.2.1])
                              have hwsV : sV.scratch.work_stk1 = ws1' := by
                                rw [hsV]; exact hpresV.2.1.trans (by rw [hsU])
                              have htmkV : sV.scratch.tarjan_mark = tmk' := by
                                rw [hsV]; exact hpresV.2.2.2.1.trans (by rw [hsU])
                              have hcvV : sV.core.cur_vars = s.core.cur_vars := by
                                rw [hsV]; exact hcvU
                              have hfuelV0 : sV.core.fuel.toNat ≤ s.core.fuel.toNat := by
                                rw [hsV]; exact hfuelU0
                              have hmV1 : (FullMem c sV ⋆ R) mV := hsV ▸ hmV
                              c0_split
                              rotate_left 1
                              · -- !okU -> clear tmk and return 20
                                have hok_false : okU = false := by c0_bound
                                have hunsV : F0.Unsat := (hokF hlitU_lt hok_false).1
                                fsv_group
                                refine sweep_var_tmk_clear_wp rfl rfl hnv_mx hinvV hwsV htmkV
                                  hconeV.2.2.2.2.2.1 (fun u hu => htmk1' u (hcvV ▸ hu)) hmV1 ?_
                                intro tmk_c m_end ht_len ht_done hm_end
                                fsv_steps
                                exact hQ 20#64 _ m_end (fullDenseInvW_with_tmk hinvV ht_len) hcvV
                                  hfuelV0 (hcvV ▸ ht_done) (Or.inr rfl) (fun _ => hunsV) hm_end
                              · -- okU -> sweep_cnt++ and join
                                fsv_steps
                                fsv_unwind_j
                                exact hJu (rbit, smask, ()) _
                                  ⟨_, fullDenseInvW_with_sweep_cnt hinvV
                                      (sV.scratch.sweep_cnt + 1#64),
                                    hcvV, hfuelV0,
                                    fullSweepConeOk_with_scratch hconeV rfl rfl rfl
                                      (fun _ _ => rfl),
                                    hwsV, htmkV, by assumption⟩
                            · -- dU == 10 && rbit < 64
                              c0_call hrefine
                              refine ⟨c, sU, R, rfl, hlenU', hcap, hnv_24, hnv_mx,
                                hconeU.2.2.2.2.2.1, hmU1, ?_⟩
                              intro sigU mU' hsigU hmU'
                              have hr64_w : (BitVec.setWidth 64 rbit).toNat < 64 := by
                                have : rbit.toNat < 64 := by c0_bound
                                simp only [BitVec.toNat_setWidth]; omega
                              fsv_steps
                              fsv_unwind_j
                              exact hJu _ mU' ⟨_, fullDenseInvW_after_refine hinvU hsigU,
                                hcvU, hfuelU0, fullSweepConeOk_with_scratch hconeU rfl rfl rfl
                                  (fun _ _ => rfl),
                                by rw [hsU], by rw [hsU], hmU'⟩
                            · fsv_unwind_j
                              exact hJu (rbit, smask, ()) mU
                                ⟨sU, hinvU, hcvU, hfuelU0, hconeU, by rw [hsU], by rw [hsU],
                                  hmU1⟩
                            · fsv_unwind_j
                              exact hJu (rbit, smask, ()) mU
                                ⟨sU, hinvU, hcvU, hfuelU0, hconeU, by rw [hsU], by rw [hsU],
                                  hmU1⟩)
                          (fun Jtest hJtest => by
                            fsv_steps
                            · exact hJtest (0#32, ()) m2 ⟨rfl, Or.inl rfl⟩
                            · exact hJtest (1#32, ()) m2 ⟨rfl, Or.inr rfl⟩))
                      (fun Jdo hdo => by
                        fsv_steps
                        · exact hdo () m2 rfl
                        · exact hdo () m2 rfl
                        · exact hJu (rbit, smask, ()) m2
                            ⟨s2, hinv2, rfl, hfuel2, hcone2, rfl, rfl, hm2⟩)
                  · fsv_steps
                    exact hJu (rbit, smask, ()) m2 ⟨s2, hinv2, rfl, hfuel2, hcone2, rfl, rfl, hm2⟩))
            (fun Jsm hJsm => by
              c0_split
              · fsv_steps; exact hJsm _ m2 rfl
              · fsv_group
                refine wp_join_group (ts := [i64])
                  (fun (sm1, ()) m1 => m1 = m2)
                  (fun _ (sm1, ()) m1 hm1 => by subst m1; fsv_steps; exact hJsm _ m2 rfl)
                  (fun Jsm1 hJsm1 => by
                    c0_split
                    · fsv_steps; exact hJsm1 _ m2 rfl
                    · have hr64 : (BitVec.setWidth 64 rbit).toNat < 64 := by
                        have : ¬ 64 ≤ rbit.toNat := by c0_bound
                        simp [BitVec.toNat_setWidth]; omega
                      fsv_steps; exact hJsm1 _ m2 rfl)))

end SweepVar

/-! ## 2. `full_sweep_sat_wp` (`Full.lean` #17) -/

section SweepSat
open FullSweepVarHelpers
open scoped FullArenaTactics FullSweepVarTactics

theorem full_sweep_sat_wp (Γ : Env)
    (hbt : EnvSpec Γ "full_backtrack" fullBacktrackSpec)
    (henter : EnvSpec Γ "full_enter_dense" fullEnterDenseSpec)
    (hsvar : EnvSpec Γ "full_sweep_var" fullSweepVarSpec)
    (hreb : EnvSpec Γ "full_rebuild_watches" fullRebuildWatchesSpec)
    (hprop : EnvSpec Γ "full_propagate" fullPropagateSpec) :
    ∀ args m Q X, fullSweepSatSpec args m Q X →
      Func.wp Γ full_sweep_sat_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hinv.lengths.core_ok.cur_vars_le
  fsv_group
  -- 1. if (h->cur_level != 0) full_backtrack(h, 0)
  refine wp_join_group
    (fun (_u : Tup Val []) m1 => ∃ s1, FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel = s.core.fuel ∧ (FullMem c s1 ⋆ R) m1)
    (fun _ () m1 ⟨s1, hinv1, hlvl1, hfuel1, hm1⟩ => by
      fsv_steps
      -- 2. if (h->scratch_cap < 1152 || !full_enter_dense(h)) return 1
      c0_split
      · fsv_steps
        exact hQ 1#64 s1 m1 hinv1 hlvl1 (hfuel1 ▸ Nat.le_refl _) (Or.inl rfl)
          (fun h => by cases h) hm1
      · have hcap1 : 1152 ≤ c.scratch_cap := by
          have : ¬ c.scratch_cap < 1152 := by c0_bound
          omega
        c0_call henter
        refine ⟨c, F0, s1, R, rfl, hinv1, hm1, ?_⟩
        intro ok2 s2 m2 hlvl2 hfuel2 hdense2 hsparse2 hm2
        c0_split
        · -- ok2 = true
          have hok2 : ok2 = true := by c0_bound
          have hd2 := hdense2 hok2
          have hcv2_le := hd2.lengths.core_ok.cur_vars_le
          fsv_group
          -- 3. while (i < cv) { tmk[i] = -1; i++; }
          refine wp_loop_inv (ts := [i64])
            (fun (i, ()) m3 => i.toNat ≤ s2.core.cur_vars ∧ ∃ tmk3 : List (BitVec 32),
              tmk3.length = 2 * c.max_vars ∧
              (∀ v < i.toNat, tmk3[v]?.getD 0#32 = 0xFFFFFFFF#32) ∧
              (FullMem c { s2 with scratch := { s2.scratch with tarjan_mark := tmk3 } } ⋆ R) m3)
            (fun (i, ()) _ => s2.core.cur_vars - i.toNat)
            (fun Ji hLi => by
              fsv_steps
              exact hLi (0#64, ()) m2 ⟨Nat.zero_le _, s2.scratch.tarjan_mark,
                hd2.lengths.scratch_ok.tarjan_mark_len, (fun _ hv => by simp at hv), hm2⟩)
            (fun Ji (i, ()) m3 ⟨hi_le, tmk3, htmk3_len, htmk3_cov, hm3⟩ hLi => by
              c0_split
              · have hi_lt : i.toNat < s2.core.cur_vars := by c0_bound
                have hi1 : (i + 1#64).toNat = i.toNat + 1 := bv64_add1_lt (by omega)
                fsv_steps
                refine hLi (i + 1#64, ()) _ (by dsimp only; omega)
                  ⟨by omega, tmk3.set i.toNat 0xFFFFFFFF#32, ?_, ?_, ?_⟩
                · rw [List.length_set]; exact htmk3_len
                · intro v hv
                  by_cases hvi : v = i.toNat
                  · subst hvi; rw [List.getElem?_set_self (by omega)]; rfl
                  · rw [List.getElem?_set_ne (Ne.symm hvi)]; exact htmk3_cov v (by omega)
                · assumption
              · have hi_eq : i.toNat = s2.core.cur_vars := by
                  have : ¬ i.toNat < s2.core.cur_vars := by c0_bound
                  omega
                let s3 : FullState := { s2 with scratch := { s2.scratch with tarjan_mark := tmk3 } }
                have hd3 : FullDenseInv c F0 s3 := fullDenseInv_with_tmk hd2 htmk3_len
                have htmk3_all : ∀ v < s3.core.cur_vars,
                    s3.scratch.tarjan_mark[v]?.getD 0#32 = 0xFFFFFFFF#32 := by
                  intro v hv; exact htmk3_cov v (hi_eq ▸ hv)
                fsv_group
                -- 4. while (v < cv && budget > 0 && oom == 0 && fuel > 0)
                refine wp_join_group (ts := [i64, i64, i64])
                  (fun (_vB, _bB, resB, ()) mB => ∃ sB, FullDenseInv c F0 sB ∧
                    sB.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                    (resB = 1#64 ∨ resB = 20#64) ∧ (resB = 20#64 → F0.Unsat) ∧
                    (FullMem c sB ⋆ R) mB)
                  (fun _ (_vB, _bB, resB, ()) mB ⟨sB, hdB, hfuelB, hresB, hunsB, hmB⟩ => by
                    c0_call hreb
                    refine ⟨c, F0, sB, R, rfl, hdB, hmB, ?_⟩
                    intro rr sR mR hspR hlvlR hfuelR hrr_dom hrr_uns hmR
                    have hfuelR0 : sR.core.fuel.toNat ≤ s.core.fuel.toNat :=
                      Nat.le_trans hfuelR hfuelB
                    fsv_steps
                    · exact hQ 20#64 sR mR hspR hlvlR hfuelR0 (Or.inr rfl)
                        (fun _ => hunsB (by c0_bound)) hmR
                    · exact hQ 20#64 sR mR hspR hlvlR hfuelR0 (Or.inr rfl)
                        (fun _ => hrr_uns (by c0_bound)) hmR
                    · exact hQ 20#64 sR mR hspR hlvlR hfuelR0 (Or.inr rfl)
                        (fun _ => hspR.inconsistent_unsat (by c0_bound)) hmR
                    · obtain ⟨F_curR, hwR⟩ := hspR.exists_witness
                      c0_call hprop
                      refine ⟨c, F0, F_curR, sR, R, rfl, hwR.1, hwR.2.1, hwR.2.2.2.1,
                        hwR.2.2.2.2.2, hmR, ?_⟩
                      intro pr valsP flagsP lvlP rsnsP trlP tpP teP propP unassP unflP wvecP arenaP
                        wstkP wlenP wuP fuelP ctypeP crefP c0P c1P oomP scP mP _ hlenP hwP hndP
                        hpresP hteP hfuelP hsubP htrlP hpr_dom hpr0 hpr1 hpr2 hsameP hmP
                      let sP : FullState :=
                        { sR with
                          core := { sR.core with
                            vals := valsP, flags := flagsP, lvl := lvlP,
                            rsns := rsnsP, trl := trlP, trail_pos := tpP, trail_end := teP,
                            propagated := propP, unassigned := unassP, unflushed := unflP,
                            wvec := wvecP, arena := arenaP, wstk := wstkP, wlen := wlenP,
                            wusable := wuP, fuel := fuelP, confl_type := ctypeP,
                            confl_ref := crefP, confl_lit0 := c0P, confl_lit1 := c1P, oom := oomP }
                          scratch := scP }
                      have hspP :=
                        fullSparseInv_after_propagate hwR sP rfl hlenP hwP hndP hpresP hsubP
                      have hfuelP0 : sP.core.fuel.toNat ≤ s.core.fuel.toNat :=
                        Nat.le_trans hfuelP hfuelR0
                      c0_split
                      · fsv_steps
                        exact hQ 20#64 sP mP hspP hlvlR hfuelP0 (Or.inr rfl)
                          (fun _ => level0_unsat_of_conflict_okW hwP hlvlR
                            (hpr1 (by c0_bound)).2.2) hmP
                      · fsv_steps
                        exact hQ 1#64 sP mP hspP hlvlR hfuelP0 (Or.inl rfl)
                          (fun h => by cases h) hmP)
                  (fun Jbrk hJbrk => by
                    fsv_group
                    refine wp_loop_inv (ts := [i64, i64])
                      (fun (v, budget, ()) ml =>
                        v.toNat ≤ s3.core.cur_vars ∧ ∃ sL,
                          FullDenseInv c F0 sL ∧ sL.core.cur_vars = s3.core.cur_vars ∧
                          sL.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                          (∀ u < sL.core.cur_vars,
                            sL.scratch.tarjan_mark[u]?.getD 0#32 = 0xFFFFFFFF#32) ∧
                          (FullMem c sL ⋆ R) ml)
                      (fun (v, _, ()) _ => s3.core.cur_vars - v.toNat)
                      (fun Jv hLv => by
                        fsv_steps
                        exact hLv (0#64, 32#64, ()) m3
                          ⟨Nat.zero_le _, s3, hd3, rfl, hfuel2 ▸ hfuel1 ▸ Nat.le_refl _,
                            htmk3_all, hm3⟩)
                      (fun Jv (v, budget, ()) ml
                          ⟨hv_le, sL, hdL, hcvL, hfuelL, htmkL, hml⟩ hLv => by
                        c0_split
                        · c0_split
                          · c0_split
                            · c0_split
                              · have hv_lt : v.toNat < sL.core.cur_vars := by
                                  have h1 : v.toNat < s2.core.cur_vars % 2 ^ 64 := by c0_bound
                                  have hcv2 := hd2.lengths.core_ok.cur_vars_le
                                  rw [hcvL]; change v.toNat < s2.core.cur_vars; omega
                                have hcvL_le := hdL.lengths.core_ok.cur_vars_le
                                have h2v_lt : (v <<< (1 : Nat)).toNat < 2 * c.max_vars := by
                                  have : v.toNat < 2 ^ 63 := by omega
                                  have hshl : (v <<< (1 : Nat)).toNat = 2 * v.toNat := by
                                    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
                                    omega
                                  rw [hshl]; omega
                                have hv1 : (v + 1#64).toNat = v.toNat + 1 := bv64_add1_lt (by omega)
                                have hfl_len := hdL.lengths.core_ok.flags_len
                                have hv_fl : v.toNat < sL.core.flags.length := by omega
                                have h2v_vals : (v <<< (1 : Nat)).toNat < sL.core.vals.length := by
                                  have := hdL.lengths.core_ok.vals_len; omega
                                fsv_steps
                                · -- flagged active & sweep and unassigned -> sweep_var
                                  let sL' : FullState :=
                                    { sL with
                                      core := { sL.core with
                                        flags := sL.core.flags.set v.toNat
                                          ((sL.core.flags[v.toNat]'(by omega)) &&& ~~~1024#32) } }
                                  have hdL' : FullDenseInv c F0 sL' :=
                                    fullDenseInv_with_flags hdL (List.length_set.trans hfl_len)
                                  obtain ⟨F_curL, hwL⟩ := hdL'.exists_witness
                                  have hv32 : (v.setWidth 32).toNat < sL'.core.cur_vars := by
                                    rw [bv64_to32_toNat v (by omega)]; exact hv_lt
                                  c0_call hsvar
                                  refine ⟨c, F0, F_curL, sL', R, rfl, hwL, hcap1, hv32, htmkL,
                                    by assumption, ?_⟩
                                  intro rV sV mV hwV hcvV hfuelV htmkV hrV_dom hrV_uns hmV
                                  have hfuelV0 : sV.core.fuel.toNat ≤ s.core.fuel.toNat :=
                                    Nat.le_trans hfuelV hfuelL
                                  c0_split
                                  · -- rV == 20 -> break
                                    have hrV20 : rV = 20#64 := by c0_bound
                                    fsv_steps
                                    exact hJbrk (v, budget - 1#64, 20#64, ()) mV
                                      ⟨sV, hwV.toDense, hfuelV0, Or.inr rfl,
                                        (fun _ => hrV_uns hrV20), hmV⟩
                                  · -- rV != 20 -> continue
                                    fsv_steps
                                    try (apply hJ; fsv_steps)
                                    exact hLv (v + 1#64, budget - 1#64, ()) mV
                                      (by dsimp only; omega)
                                      ⟨by omega, sV, hwV.toDense, hcvV.trans hcvL, hfuelV0, htmkV,
                                        hmV⟩
                                all_goals
                                  exact hLv (v + 1#64, budget, ()) _ (by dsimp only; omega)
                                    ⟨by omega, sL, hdL, hcvL, hfuelL, htmkL, by assumption⟩
                              · fsv_steps
                                exact hJbrk (v, budget, 1#64, ()) ml
                                  ⟨sL, hdL, hfuelL, Or.inl rfl, (fun h => by cases h), hml⟩
                            · fsv_steps
                              exact hJbrk (v, budget, 1#64, ()) ml
                                ⟨sL, hdL, hfuelL, Or.inl rfl, (fun h => by cases h), hml⟩
                          · fsv_steps
                            exact hJbrk (v, budget, 1#64, ()) ml
                              ⟨sL, hdL, hfuelL, Or.inl rfl, (fun h => by cases h), hml⟩
                        · fsv_steps
                          exact hJbrk (v, budget, 1#64, ()) ml
                            ⟨sL, hdL, hfuelL, Or.inl rfl, (fun h => by cases h), hml⟩)))
        · -- ok2 = false
          have hok2 : ok2 = false := by c0_bound
          fsv_steps
          exact hQ 1#64 s2 m2 (hsparse2 hok2) hlvl2 (hfuel2 ▸ hfuel1 ▸ Nat.le_refl _)
            (Or.inl rfl) (fun h => by cases h) hm2)
    (fun Ju hJu => by
      fsv_steps
      · obtain ⟨F_cur, hspw⟩ := hinv.exists_witness
        have hcl_lt : s.core.cur_level < 2 ^ 64 := by
          have := hspw.2.1.cur_level_le; have := hinv.lengths.core_ok.trail_end_le; omega
        have hbt_lvl : 0 < c.max_vars := by
          have : s.core.cur_level ≠ 0 := by c0_bound
          have := hspw.2.1.cur_level_le; have := hinv.lengths.core_ok.trail_end_le; omega
        c0_call hbt
        refine ⟨c, s, R, rfl, hinv.lengths, hcl_lt, fun _ => hbt_lvl,
          hspw.2.1.trail_lits_lt, hm, ?_⟩
        intro vals1 lvl1 rsns1 trl1 tp1 te1 prop1 cl1 unass1 sc1 m1 _ hlen1 hte1 hprop1 hcl1
          hpres1 htrl1 hwinv1 hotfs1 hm1
        let s1 : FullState :=
          { s with
            core := { s.core with
              vals := vals1, lvl := lvl1, rsns := rsns1, trl := trl1,
              trail_pos := tp1, trail_end := te1, propagated := prop1, cur_level := cl1,
              unassigned := unass1 }
            scratch := sc1 }
        have hcl1_0 : cl1 = 0 := by simpa using hcl1
        have hw1 := hwinv1 F0 F_cur hspw.2.1 (Nat.zero_le _)
        have hsp1 := fullSparseInv_after_backtrack hspw s1 rfl hlen1 hpres1 hw1
        exact hJu () m1 ⟨s1, hsp1, hcl1_0, rfl, hm1⟩
      · have hl0 : s.core.cur_level = 0 := by
          obtain ⟨_, hspw⟩ := hinv.exists_witness
          have := hspw.2.1.cur_level_le; have := hinv.lengths.core_ok.trail_end_le
          have h := congrArg BitVec.toNat (by c0_bound : BitVec.ofNat 64 s.core.cur_level = 0)
          simp [Nat.mod_eq_of_lt (by omega : s.core.cur_level < 2 ^ 64)] at h
          exact h
        exact hJu () m ⟨s, hinv, hl0, rfl, hm⟩)

end SweepSat

end LeanQbe.T.Examples.Kissat.Full
