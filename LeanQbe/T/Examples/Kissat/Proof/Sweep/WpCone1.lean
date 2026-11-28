/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Sweep.WpCone0

/-!
# Occurrence-Watch & Clause-Scan Cone WP Proofs (`Proof.Sweep.WpCone1`)

Modular WP lemmas for the occurrence-clause subtree of
`Src.Sweep.full_m6_sweep_cone_body`:
1. `s13OccScanExpr` / `step13_cone_occ_scan_wp` (`idx < sz` literal scan loop).
2. `s13OccClauseExpr` / `step13_cone_occ_clause_wp` (scan + add-clause / rollback).
3. `s13OccWatchExpr` / `step13_cone_occ_watch_wp` (occurrence watch list loop).
4. `s13OccPassExpr` / `step13_cone_occ_pass_wp` (occurrence polarity loop `pol < 2`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Sweep

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Kitten
open scoped FullArenaTactics K6MemATactics FullK6DynMem

/-! ## 1. Local Helpers -/

private theorem s13_getElem_congr {α : Type _} {xs : List α} {i j : Nat} (heq : i = j)
    (hi : i < xs.length) (hj : j < xs.length) : xs[i]'hi = xs[j]'hj := by
  subst heq; rfl

private theorem s13_occ_hdr_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {cr sz : BitVec 32} (hbd : cr.toNat < st.core.arena.length)
    (hlen : FullState.LengthsOk c s) (hw : FullWitnessInv c F0 F_cur s.core)
    (hnd : FullArenaVarsNodup s) (har_eq : st.core.arena = s.core.arena)
    (hcr_ref : cr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hsz_eq : sz.toNat = fullArenaClauseSizeCore s.core cr.toNat)
    (hgr0 : st.core.arena[cr.toNat]'hbd &&& (0x00080000#32 ||| 0x00400000#32) = 0#32) :
    fullArenaClauseGarbCore s.core cr.toNat = false ∧
      cr.toNat + 3 + sz.toNat ≤ s.core.arena.length ∧
      sz.toNat ≤ s.core.cur_vars ∧
      cr.toNat + 3 + sz.toNat ≤ s.core.arena_len := by
  have hwf := hw.arena.refs_wf cr.toNat hcr_ref
  have har_len := hlen.core_ok.arena_len_arr
  have hal_le := hlen.core_ok.arena_len_le
  have hlen_al : cr.toNat + 3 + sz.toNat ≤ s.core.arena_len := by
    rw [hsz_eq]; have := hwf.2.2.1; have := hwf.2.2.2.1; omega
  have hlen_ar : cr.toNat + 3 + sz.toNat ≤ s.core.arena.length := by omega
  have hbd_s : cr.toNat < s.core.arena.length := har_eq ▸ hbd
  have hst_at : st.core.arena[cr.toNat]'hbd = s.core.arena[cr.toNat]'hbd_s := by
    rw [← Option.some_inj, ← List.getElem?_eq_getElem hbd,
      ← List.getElem?_eq_getElem hbd_s, har_eq]
  have hhdr_at : fullArenaHdrCore s.core cr.toNat = st.core.arena[cr.toNat]'hbd := by
    unfold fullArenaHdrCore
    rw [List.getElem?_eq_getElem hbd_s, Option.getD_some, hst_at]
  have hng : fullArenaClauseGarbCore s.core cr.toNat = false := by
    unfold fullArenaClauseGarbCore
    rw [hhdr_at]
    have hbit : st.core.arena[cr.toNat]'hbd &&& 524288#32 = 0#32 := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have hg := congrArg (fun z => z.getLsbD i) hgr0
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_zero] at hg ⊢
      by_cases hb : (524288#32 : BitVec 32).getLsbD i = true
      · simp_all
      · simp [hb]
    simp [hbit]
  have hnd_cl := hnd cr.toNat hcr_ref hng
  have hsz_le_cv : sz.toNat ≤ s.core.cur_vars := Nat.le_of_not_lt fun hcv_lt => by
    let f : Nat → Nat := fun i => (s.core.arena[cr.toNat + 3 + i]?.getD 0#32).toNat / 2
    have hlits_eq : fullArenaClauseLitsCore s.core cr.toNat =
        (List.range sz.toNat).map fun i => (s.core.arena[cr.toNat + 3 + i]?.getD 0#32).toNat := by
      rw [fullArenaClauseLitsCore, ← hsz_eq]
      apply List.ext_getElem
      · simp [List.length_take, List.length_drop]; omega
      · intro i h1 h2
        have hi : i < sz.toNat := by simpa using h2
        have hbi : cr.toNat + 3 + i < s.core.arena.length := by omega
        simp [List.getElem_take, List.getElem_drop, List.getElem?_eq_getElem hbi]
    have hlits_mem : ∀ i, i < sz.toNat →
        (s.core.arena[cr.toNat + 3 + i]?.getD 0#32).toNat ∈
          fullArenaClauseLitsCore s.core cr.toNat := by
      intro i hi; rw [hlits_eq]
      exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
    have hf_lt : ∀ i, i < sz.toNat → f i < s.core.cur_vars := by
      intro i hi
      have hm := hw.arena.lits_lt cr.toNat hcr_ref hng _ (hlits_mem i hi)
      dsimp only [f]; omega
    have hf_inj : ∀ i j, i < sz.toNat → j < sz.toNat → f i = f j → i = j := by
      intro i j hi hj heq
      have hnd_map : ((List.range sz.toNat).map f).Nodup := by
        have hnd2 := hnd_cl
        unfold fullArenaClauseLits at hnd2
        rw [hlits_eq, List.map_map] at hnd2
        simpa [Function.comp_def, f] using hnd2
      have hp := List.pairwise_iff_getElem.mp hnd_map
      have hi_len : i < ((List.range sz.toNat).map f).length := by simp; exact hi
      have hj_len : j < ((List.range sz.toNat).map f).length := by simp; exact hj
      rcases Nat.lt_trichotomy i j with hij | rfl | hij
      · exact absurd (by simpa only [List.getElem_map, List.getElem_range] using heq)
          (hp i j hi_len hj_len hij)
      · rfl
      · exact absurd (by simpa only [List.getElem_map, List.getElem_range] using heq.symm)
          (hp j i hj_len hi_len hij)
    have hctr : s.core.cur_vars < s.core.cur_vars :=
      m6_inj_lt_of_missing f (fun i j hi hj => hf_inj i j (by omega) (by omega))
        (fun i hi => hf_lt i (by omega)) (hf_lt s.core.cur_vars hcv_lt)
        (fun i hi hEq => by have := hf_inj i s.core.cur_vars (by omega) hcv_lt hEq; omega)
    omega
  exact ⟨hng, hlen_ar, hsz_le_cv, hlen_al⟩

private theorem s13_cone_clause_entails_filtered {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} {cr : BitVec 32}
    {ws tmp : List (BitVec 32)} {cnt : Nat}
    (hw : FullWitnessInv c F0 F_cur s.core) (hcl0 : s.core.cur_level = 0)
    (hcr : cr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hng : fullArenaClauseGarbCore s.core cr.toNat = false)
    (hcov : ∀ l ∈ fullArenaClauseLitsCore s.core cr.toNat,
      s.core.vals[l]?.getD 0#8 = 255#8 ∨
        l ∈ (tmp.take cnt).map (fun x => m6ConeLift ws x.toNat)) :
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((tmp.take cnt).map (fun x => m6ConeLift ws x.toNat))) := by
  rw [Std.Sat.CNF.entails_clause_def]
  intro α hα
  have hent := hw.arena.entails cr.toNat hcr hng
  rw [Std.Sat.CNF.entails_clause_def] at hent
  have hcl := hent α hα
  rw [← clauseEvalVal_iff] at hcl ⊢
  simp only [clauseEvalVal, List.any_eq_true] at hcl ⊢
  obtain ⟨l, hl_mem, hl_sat⟩ := hcl
  rcases hcov l hl_mem with hf | hl_in
  · have hnsat := m6_lvl0_false_not_sat hw hcl0
      (hw.arena.lits_lt cr.toNat hcr hng l hl_mem) hf hα
    rw [← clauseEvalVal_iff] at hnsat
    simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false] at hnsat
    exact absurd hl_sat hnsat
  · exact ⟨l, hl_in, hl_sat⟩

private theorem s13_scan_mask_upd_tmp {s st : FullState}
    (hag : AgreesExcept step13ConeMask s st) (tmp' : List (BitVec 32)) :
    AgreesExcept step13ConeMask s
      { st with core := { st.core with tmp := tmp' } } := by
  rcases st with ⟨c_st, sc_st⟩
  exact hag

private theorem s13_neg_lt_not_one {v : BitVec 8}
    (h0 : v.signExtend 32 = 0#32 → False)
    (h1 : (0#32 : BitVec 32).slt (v.signExtend 32) = true → False)
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 255#8) : v = 255#8 := by
  rcases hdom with rfl | rfl | rfl
  · exact absurd rfl h0
  · exact absurd (by decide) h1
  · rfl

/-! ## 2. Clause Literal Scan Loop (`occScan`) -/

@[expose] def s13OccScanExpr (pAr pVals pFl pTmk pTmp pWs : Val i64)
    (aCr aSz aPol aCv aCurTmk aMvC : Arg Val i32) (aLimW : Arg Val .bool)
    (aNvW : Arg Val i32)
    (k_drop : Val i32 → Arg Val .bool → Val i32 → Val i32 → Expr Val Cont [i64])
    (k_done : Val i32 → Arg Val .bool → Val i32 → Val i32 → Expr Val Cont [i64]) :
    Expr Val Cont [i64] :=
  Expr.group
    (fun Js =>
      Blocks.cons
        (fun p : Tup Val [i32, i32, i32] =>
          Expr.let_ (Op.mk (.cmp .ult i32 .bool rfl) (Arg.var p.snd.snd.fst, aSz, ())) fun pult =>
          Expr.jnz (Arg.var pult.fst)
            (Expr.let_ (Op.mk (.zext 32 64) (aCr, ())) fun pcrz =>
              Expr.let_ (Op.mk (.add i64) (Arg.var pcrz.fst, Arg.imm 3, ())) fun pcr3 =>
              Expr.let_ (Op.mk (.zext 32 64) (Arg.var p.snd.snd.fst, ())) fun pidxz =>
              Expr.let_ (Op.mk (.add i64) (Arg.var pcr3.fst, Arg.var pidxz.fst, ())) fun paid =>
              Expr.let_ (Op.mk (.mul i64) (Arg.var paid.fst, Arg.imm 4, ())) fun paoff =>
              Expr.let_ (Op.mk (.add i64) (Arg.var pAr, Arg.var paoff.fst, ())) fun pa =>
              Expr.load i32 (Arg.var pa.fst) fun pl =>
              Expr.let_ (Op.mk (.zext 32 64) (Arg.var pl, ())) fun plz =>
              Expr.let_ (Op.mk (.add i64) (Arg.var pVals, Arg.var plz.fst, ())) fun pv =>
              Expr.load i8 (Arg.var pv.fst) fun pval =>
              Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 0, ())) fun pz8 =>
              Expr.let_ (Op.mk (.sext 8 32) (Arg.var pval, ())) fun pvs =>
              Expr.let_ (Op.mk (.sext 8 32) (Arg.var pz8.fst, ())) fun pz32 =>
              Expr.let_ (Op.mk (.cmp .sgt i32 .bool rfl)
                (Arg.var pvs.fst, Arg.var pz32.fst, ())) fun psgt =>
              Expr.jnz (Arg.var psgt.fst)
                (k_drop p.fst aLimW p.snd.fst p.snd.snd.fst)
                (Expr.group
                  (fun _ => Blocks.cons
                    (fun q : Tup Val [i32, .bool, .bool, i32] =>
                      Expr.let_ (Op.mk (.add i32) (Arg.var p.snd.snd.fst, Arg.imm 1, ()))
                        fun pidx1 =>
                      Expr.jump Js.fst (Arg.var q.fst, Arg.var q.snd.snd.snd.fst,
                        Arg.var pidx1.fst, ()))
                    Blocks.nil)
                  fun Jn =>
                    Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 0, ())) fun qz8 =>
                    Expr.let_ (Op.mk (.sext 8 32) (Arg.var pval, ())) fun qvs =>
                    Expr.let_ (Op.mk (.sext 8 32) (Arg.var qz8.fst, ())) fun qz32 =>
                    Expr.let_ (Op.mk (.cmp .eq i32 .bool rfl)
                      (Arg.var qvs.fst, Arg.var qz32.fst, ())) fun qeq0 =>
                    Expr.jnz (Arg.var qeq0.fst)
                      (Expr.let_ (Op.mk (.lshr i32) (Arg.var pl, Arg.imm 1, ())) fun plv =>
                        Expr.let_ (Op.mk (.zext 32 64) (Arg.var plv.fst, ())) fun plvz =>
                        Expr.let_ (Op.mk (.mul i64) (Arg.var plvz.fst, Arg.imm 4, ())) fun pfloff =>
                        Expr.let_ (Op.mk (.add i64) (Arg.var pFl, Arg.var pfloff.fst, ()))
                          fun pfla =>
                        Expr.load i32 (Arg.var pfla.fst) fun pflv =>
                        Expr.let_ (Op.mk (.and i32) (Arg.var pflv, Arg.imm 1, ())) fun pfla1 =>
                        Expr.let_ (Op.mk (.cmp .eq i32 .bool rfl)
                          (Arg.var pfla1.fst, Arg.imm 0, ())) fun pfl0 =>
                        Expr.jnz (Arg.var pfl0.fst)
                          (k_drop p.fst aLimW p.snd.fst p.snd.snd.fst)
                          (Expr.let_ (Op.mk (.zext 32 64) (Arg.var plv.fst, ())) fun plvz2 =>
                            Expr.let_ (Op.mk (.mul i64) (Arg.var plvz2.fst, Arg.imm 4, ()))
                              fun ptmoff =>
                            Expr.let_ (Op.mk (.add i64) (Arg.var pTmk, Arg.var ptmoff.fst, ()))
                              fun ptma =>
                            Expr.load i32 (Arg.var ptma.fst) fun pltm =>
                            Expr.group
                              (fun _ => Blocks.cons
                                (fun _ : Tup Val [] =>
                                  Expr.group
                                    (fun _ => Blocks.cons
                                      (fun _ : Tup Val [] =>
                                        Expr.group
                                          (fun _ => Blocks.cons
                                            (fun u : Tup Val [i32, .bool, .bool] =>
                                              Expr.let_ (Op.mk (.zext 32 64)
                                                (Arg.var p.snd.fst, ())) fun pcz =>
                                              Expr.let_ (Op.mk (.mul i64)
                                                (Arg.var pcz.fst, Arg.imm 4, ())) fun pcoff =>
                                              Expr.let_ (Op.mk (.add i64)
                                                (Arg.var pTmp, Arg.var pcoff.fst, ())) fun pta =>
                                              Expr.let_ (Op.mk (.zext 32 64)
                                                (Arg.var plv.fst, ())) fun plvz3 =>
                                              Expr.let_ (Op.mk (.mul i64)
                                                (Arg.var plvz3.fst, Arg.imm 4, ())) fun ptoff3 =>
                                              Expr.let_ (Op.mk (.add i64)
                                                (Arg.var pTmk, Arg.var ptoff3.fst, ())) fun ptma3 =>
                                              Expr.load i32 (Arg.var ptma3.fst) fun ptmlv =>
                                              Expr.let_ (Op.mk (.sub i32)
                                                (Arg.var ptmlv, Arg.imm 1, ())) fun pt1 =>
                                              Expr.let_ (Op.mk (.shl i32)
                                                (Arg.var pt1.fst, Arg.imm 1, ())) fun ptsh =>
                                              Expr.let_ (Op.mk (.and i32)
                                                (Arg.var pl, Arg.imm 1, ())) fun plpol =>
                                              Expr.let_ (Op.mk (.or i32)
                                                (Arg.var ptsh.fst, Arg.var plpol.fst, ()))
                                                fun pnl =>
                                              Expr.store (t := i32) (Arg.var pnl.fst)
                                                (Arg.var pta.fst) <|
                                              Expr.let_ (Op.mk (.add i32)
                                                (Arg.var p.snd.fst, Arg.imm 1, ())) fun pcnt1 =>
                                              Expr.jump Jn.fst (Arg.var u.fst, Arg.var u.snd.fst,
                                                Arg.var u.snd.snd.fst, Arg.var pcnt1.fst, ()))
                                            Blocks.nil)
                                          fun Ju =>
                                            Expr.let_ (Op.mk (.cmp .eq i32 .bool rfl)
                                              (Arg.var pltm, Arg.imm 0, ())) fun pltm0 =>
                                            Expr.jnz (Arg.var pltm0.fst)
                                              (Expr.let_ (Op.mk (.cmp .uge i32 .bool rfl)
                                                (Arg.var p.fst, aMvC, ())) fun puge =>
                                                Expr.jnz (Arg.var puge.fst)
                                                  (k_drop p.fst (Arg.imm true) p.snd.fst
                                                    p.snd.snd.fst)
                                                  (Expr.let_ (Op.mk (.zext 32 64)
                                                    (Arg.var p.fst, ())) fun pnvz =>
                                                    Expr.let_ (Op.mk (.mul i64)
                                                      (Arg.var pnvz.fst, Arg.imm 4, ()))
                                                      fun pwsoff =>
                                                    Expr.let_ (Op.mk (.add i64)
                                                      (Arg.var pWs, Arg.var pwsoff.fst, ()))
                                                      fun pwsa =>
                                                    Expr.store (t := i32) (Arg.var plv.fst)
                                                      (Arg.var pwsa.fst) <|
                                                    Expr.let_ (Op.mk (.add i32)
                                                      (Arg.var p.fst, Arg.imm 1, ())) fun pnv1 =>
                                                    Expr.let_ (Op.mk (.zext 32 64)
                                                      (Arg.var plv.fst, ())) fun plvz4 =>
                                                    Expr.let_ (Op.mk (.mul i64)
                                                      (Arg.var plvz4.fst, Arg.imm 4, ()))
                                                      fun ptoff4 =>
                                                    Expr.let_ (Op.mk (.add i64)
                                                      (Arg.var pTmk, Arg.var ptoff4.fst, ()))
                                                      fun ptma4 =>
                                                    Expr.store (t := i32) (Arg.var pnv1.fst)
                                                      (Arg.var ptma4.fst) <|
                                                    Expr.jump Ju.fst (Arg.var pnv1.fst,
                                                      aLimW, Arg.imm false, ())))
                                              (Expr.jump Ju.fst
                                                (Arg.var p.fst, aLimW, Arg.imm false, ())))
                                      Blocks.nil)
                                    fun Jc =>
                                      Expr.let_ (Op.mk (.cmp .eq i32 .bool rfl)
                                        (Arg.var plv.fst, aCv, ())) fun peqcv =>
                                      Expr.jnz (Arg.var peqcv.fst)
                                        (Expr.let_ (Op.mk (.and i32)
                                          (Arg.var pl, Arg.imm 1, ())) fun pl1 =>
                                          Expr.let_ (Op.mk (.cmp .ult i32 .bool rfl)
                                            (Arg.var pl1.fst, aPol, ())) fun pultp =>
                                          Expr.jnz (Arg.var pultp.fst)
                                            (k_drop p.fst aLimW p.snd.fst p.snd.snd.fst)
                                            (Expr.jump Jc.fst ()))
                                        (Expr.jump Jc.fst ()))
                                Blocks.nil)
                              fun Jb =>
                                Expr.let_ (Op.mk (.cmp .ne i32 .bool rfl)
                                  (Arg.var pltm, Arg.imm 0, ())) fun pltmne =>
                                Expr.jnz (Arg.var pltmne.fst)
                                  (Expr.let_ (Op.mk (.cmp .ult i32 .bool rfl)
                                    (Arg.var pltm, aCurTmk, ())) fun pultt =>
                                    Expr.jnz (Arg.var pultt.fst)
                                      (k_drop p.fst aLimW p.snd.fst p.snd.snd.fst)
                                      (Expr.jump Jb.fst ()))
                                  (Expr.jump Jb.fst ())))
                      (Expr.jump Jn.fst
                        (Arg.var p.fst, aLimW, Arg.imm false, Arg.var p.snd.fst, ()))))
            (k_done p.fst aLimW p.snd.fst p.snd.snd.fst))
        Blocks.nil)
    fun Jscan => Expr.jump Jscan.fst (aNvW, Arg.imm 0, Arg.imm 0, ())

theorem step13_cone_occ_scan_wp {Γ : Env}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {L : K6Layout}
    {pAr pVals pFl pTmk pTmp pWs : Val i64}
    {mvC cr sz pol cv curTmk nvW : BitVec 32}
    {aCr aSz aPol aCv aCurTmk aMvC : Arg Val i32} {limW : Bool} {aLimW : Arg Val .bool}
    {aNvW : Arg Val i32} {qi_l : BitVec 32} {s stW : FullState}
    {nc_w : Nat} {R : Mem 64 → Prop} {m0 : Mem 64} {Q : Post [i64]} {X : XPost}
    {k_drop k_done : Val i32 → Arg Val .bool → Val i32 → Val i32 → Expr Val Cont [i64]}
    (hpAr : pAr = c.pArena) (hpVals : pVals = c.pVals) (hpFl : pFl = c.pFlags)
    (hpTmk : pTmk = c.pTarjanMark) (hpTmp : pTmp = c.pTmp) (hpWs : pWs = c.pWorkStk1)
    (haCr : aCr.val = cr) (haSz : aSz.val = sz) (_haPol : aPol.val = pol)
    (_haCv : aCv.val = cv) (_haCurTmk : aCurTmk.val = curTmk)
    (haMvC : aMvC.val = mvC) (haLimW : aLimW.val = limW) (haNvW : aNvW.val = nvW)
    (hlen_s : FullState.LengthsOk c s) (hw : FullWitnessInv c F0 F_cur s.core)
    (hnd_cl : ((fullArenaClauseLits s cr.toNat).map (· / 2)).Nodup)
    (hcr_ref : cr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hng : fullArenaClauseGarbCore s.core cr.toNat = false)
    (hsz_eq : sz.toNat = fullArenaClauseSizeCore s.core cr.toNat)
    (hsz_cv : sz.toNat ≤ s.core.cur_vars)
    (hcr3_bd : cr.toNat + 3 + sz.toNat ≤ s.core.arena.length)
    (hqi_nv : qi_l.toNat < nvW.toNat)
    (hbW : Step13ConeBase F_cur L mvC c s cv qi_l nvW.toNat nc_w stW)
    (hm0 : (FullMem c stW ⋆ R) m0)
    (hDrop : ∀ (nvE cntE idxE : BitVec 32) (limE : Bool) (aL : Arg Val .bool)
        (stE : FullState) (mE : Mem 64),
      aL.val = limE →
      Step13ConeSavedBase F_cur L mvC c s cv qi_l nvW stW.scratch.work_stk1
        stW.scratch.scratch_buf nvE.toNat nc_w stE →
      (FullMem c stE ⋆ R) mE →
      wp Γ Q X (k_drop nvE aL cntE idxE) mE)
    (hDone : ∀ (nvE cntE idxE : BitVec 32) (stE : FullState) (mE : Mem 64),
      Step13ConeScanBase F_cur L mvC c s cv qi_l nvW stW.scratch.work_stk1
        stW.scratch.scratch_buf cr nvE.toNat nc_w cntE.toNat idxE.toNat stE →
      idxE.toNat = sz.toNat → cntE.toNat ≤ idxE.toNat →
      (FullMem c stE ⋆ R) mE →
      wp Γ Q X (k_done nvE aLimW cntE idxE) mE) :
    wp Γ Q X (s13OccScanExpr pAr pVals pFl pTmk pTmp pWs
      aCr aSz aPol aCv aCurTmk aMvC aLimW aNvW k_drop k_done) m0 := by
  subst hpAr hpVals hpFl hpTmk hpTmp hpWs
  let ws0 := stW.scratch.work_stk1
  let scr0 := stW.scratch.scratch_buf
  refine wp_loop_inv (ts := [i32, i32, i32])
    (fun (nv_k, cnt, idx, ()) mk =>
      idx.toNat ≤ sz.toNat ∧ cnt.toNat ≤ idx.toNat ∧ ∃ st_k : FullState,
        Step13ConeScanBase F_cur L mvC c s cv qi_l nvW ws0 scr0 cr
          nv_k.toNat nc_w cnt.toNat idx.toNat st_k ∧ (FullMem c st_k ⋆ R) mk)
    (fun (_, _, idx, ()) _ => sz.toNat - idx.toNat) ?_ ?_
  · intro _ hJk
    c0_hsteps!
    rw [haNvW]
    exact hJk (nvW, 0#32, 0#32, ()) m0
      ⟨Nat.zero_le _, Nat.zero_le _, stW,
        ⟨Step13ConeSavedBase.ofBase hbW, fun _ hj => by simp at hj,
         fun _ hi => by simp at hi, fun _ hj => by simp at hj,
         fun _ _ h => by simp at h, fun _ _ h => by omega⟩,
        hm0⟩
  · rintro _ ⟨nv_k, cnt, idx, ⟨⟩⟩ mk ⟨hik_le, hcnt_le, st_k, hs_k, hmk⟩ hJk
    have hk_core := s13ConeMask_core_eq hs_k.hag
    dsimp only at hk_core
    have hae_k : st_k.core.arena = s.core.arena := by
      simpa using congrArg FullCoreState.arena hk_core
    have hve_k : st_k.core.vals = s.core.vals := by
      simpa using congrArg FullCoreState.vals hk_core
    have hcv_k : st_k.core.cur_vars = s.core.cur_vars := by
      simpa using congrArg FullCoreState.cur_vars hk_core
    c0_hsplit
    · have hk_lt : idx.toNat < sz.toNat := by
        have hlt : idx.toNat < aSz.val.toNat := ‹_›
        rwa [haSz] at hlt
      have har_k := hs_k.hlen.core_ok.arena_len_arr
      have hvals_k := hs_k.hlen.core_ok.vals_len
      have hcv_le := hs_k.hlen.core_ok.cur_vars_le
      have hsz_lt32 : cr.toNat + 3 + idx.toNat < 2 ^ 64 := by
        have := c.harena; unfold dimacsBound at this; omega
      have hidx_k : (BitVec.setWidth 64 aCr.val + 3#64 + BitVec.setWidth 64 idx).toNat =
          cr.toNat + 3 + idx.toNat := by
        rw [haCr]; simp only [BitVec.toNat_add, bv_c0_zext32_64,
          show (3#64 : BitVec 64).toNat = 3 from rfl]; omega
      have hidx_bd : (BitVec.setWidth 64 aCr.val + 3#64 + BitVec.setWidth 64 idx).toNat <
          st_k.core.arena.length := by
        rw [har_k, hidx_k]; have := hlen_s.core_ok.arena_len_arr; omega
      let lit_k : BitVec 32 :=
        st_k.core.arena[(BitVec.setWidth 64 aCr.val + 3#64 + BitVec.setWidth 64 idx).toNat]'hidx_bd
      have hlen_ar_idx : cr.toNat + 3 + idx.toNat < s.core.arena.length := by omega
      have hlit_ar : (s.core.arena[cr.toNat + 3 + idx.toNat]?.getD 0#32).toNat = lit_k.toNat := by
        have hbd_k : cr.toNat + 3 + idx.toNat < st_k.core.arena.length := har_k ▸ (by
          rw [← hlen_s.core_ok.arena_len_arr]; omega)
        have h1 : st_k.core.arena[(BitVec.setWidth 64 aCr.val + 3#64 +
            BitVec.setWidth 64 idx).toNat]'hidx_bd =
            st_k.core.arena[cr.toNat + 3 + idx.toNat]'hbd_k :=
          s13_getElem_congr hidx_k hidx_bd hbd_k
        have h2 : s.core.arena[cr.toNat + 3 + idx.toNat]? = some lit_k := by
          have h3 : st_k.core.arena[cr.toNat + 3 + idx.toNat]? = some lit_k := by
            simpa only [lit_k, ← h1] using List.getElem?_eq_getElem hbd_k
          rwa [hae_k] at h3
        rw [List.getElem?_eq_getElem hlen_ar_idx] at h2
        rw [List.getElem?_eq_getElem hlen_ar_idx, Option.getD_some]
        exact congrArg BitVec.toNat (Option.some.inj h2)
      have hl_in_cl : lit_k.toNat ∈ fullArenaClauseLitsCore s.core cr.toNat := by
        rw [mem_fullArenaClauseLitsCore_iff (by rw [← hsz_eq]; exact hcr3_bd)]
        exact ⟨idx.toNat, by rw [← hsz_eq]; exact hk_lt,
          by simp only [← hlit_ar, List.getElem?_eq_getElem hlen_ar_idx, Option.getD_some]⟩
      have hl_lt_s : lit_k.toNat < 2 * s.core.cur_vars :=
        hw.arena.lits_lt cr.toNat hcr_ref hng _ hl_in_cl
      have hval_bd : (BitVec.setWidth 64 lit_k).toNat < st_k.core.vals.length := by
        rw [hvals_k, bv_c0_zext32_64]; omega
      have hidx_c0 : (aCr.val.toNat + (3 : BitVec 64).toNat + idx.toNat) % 2 ^ 64 =
          (BitVec.setWidth 64 aCr.val + 3#64 + BitVec.setWidth 64 idx).toNat := by
        rw [hidx_k, haCr, show (3 : BitVec 64).toNat = 3 from rfl]
        have := c.harena; unfold dimacsBound at this; omega
      have har_c0_bd : (aCr.val.toNat + (3 : BitVec 64).toNat + idx.toNat) % 2 ^ 64 <
          st_k.core.arena.length := hidx_c0.symm ▸ hidx_bd
      have har_c0_eq :
          st_k.core.arena[(aCr.val.toNat + (3 : BitVec 64).toNat + idx.toNat) % 2 ^ 64]'
            har_c0_bd = lit_k :=
        s13_getElem_congr hidx_c0 har_c0_bd hidx_bd
      have hvk_c0 : (st_k.core.arena[(aCr.val.toNat + (3 : BitVec 64).toNat +
          idx.toNat) % 2 ^ 64]'har_c0_bd).toNat < st_k.core.vals.length := by
        rw [har_c0_eq, hvals_k]; omega
      have hvk_lit : lit_k.toNat < st_k.core.vals.length := by rw [hvals_k]; omega
      have hval_c0_eq :
          st_k.core.vals[(st_k.core.arena[(aCr.val.toNat + (3 : BitVec 64).toNat +
            idx.toNat) % 2 ^ 64]'har_c0_bd).toNat]'hvk_c0 =
            st_k.core.vals[lit_k.toNat]?.getD 0#8 := by
        rw [List.getElem?_eq_getElem hvk_lit, Option.getD_some]
        exact s13_getElem_congr (congrArg BitVec.toNat har_c0_eq) hvk_c0 hvk_lit
      have htm_c0_bd : (st_k.core.arena[(aCr.val.toNat + (3 : BitVec 64).toNat +
          idx.toNat) % 2 ^ 64]'har_c0_bd).toNat / 2 ^ (1 : Nat) <
          st_k.scratch.tarjan_mark.length := by
        rw [har_c0_eq, hs_k.hlen.scratch_ok.tarjan_mark_len]; omega
      have htm_c0_lit : lit_k.toNat / 2 < st_k.scratch.tarjan_mark.length := by
        rw [hs_k.hlen.scratch_ok.tarjan_mark_len]; omega
      have htm_c0_eq :
          st_k.scratch.tarjan_mark[(st_k.core.arena[(aCr.val.toNat + (3 : BitVec 64).toNat +
            idx.toNat) % 2 ^ 64]'har_c0_bd).toNat / 2 ^ (1 : Nat)]'htm_c0_bd =
            st_k.scratch.tarjan_mark[lit_k.toNat / 2]?.getD 0#32 := by
        rw [List.getElem?_eq_getElem htm_c0_lit, Option.getD_some]
        refine s13_getElem_congr ?_ htm_c0_bd htm_c0_lit
        rw [har_c0_eq]
      have hk1 : (idx + 1#32).toNat = idx.toNat + 1 :=
        m6_bv32_add1 (by have := c.hmaxv; unfold dimacsBound at this; omega)
      c0_hsplit
      · c0_hsteps!
        exact hDrop nv_k cnt idx limW aLimW st_k mk haLimW hs_k.toStep13ConeSavedBase hmk
      · have hnot_pos : (0#32 : BitVec 32).slt
            ((st_k.core.vals[lit_k.toNat]?.getD 0#8).signExtend 32) = true → False := by
          have hc_slt :
              (BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 0)).slt
                ((st_k.core.vals[(st_k.core.arena[(aCr.val.toNat + (3 : BitVec 64).toNat +
                  idx.toNat) % 2 ^ 64]'har_c0_bd).toNat]'hvk_c0).signExtend 32) = false := ‹_›
          rw [hval_c0_eq] at hc_slt
          intro hpos
          have hpos' : (BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 0)).slt
              ((st_k.core.vals[lit_k.toNat]?.getD 0#8).signExtend 32) = true := hpos
          exact absurd hpos' (Bool.eq_false_iff.mp hc_slt)
        refine wp_join_group (ts := [i32, .bool, .bool, i32])
          (fun (nv_u, lim_u, drop_u, cnt_u, ()) m_u =>
            lim_u = limW ∧ drop_u = false ∧ cnt.toNat ≤ cnt_u.toNat ∧
            cnt_u.toNat ≤ idx.toNat + 1 ∧ ∃ st_u' : FullState,
              Step13ConeScanBase F_cur L mvC c s cv qi_l nvW ws0 scr0 cr
                nv_u.toNat nc_w cnt_u.toNat (idx.toNat + 1) st_u' ∧ (FullMem c st_u' ⋆ R) m_u)
          (fun _ (nv_u, _lim_u, _drop_u, cnt_u, ()) m_u ⟨_, _, _, hc1, st_u', hs_u', hmu'⟩ => by
            c0_hsteps!
            exact hJk (nv_u, cnt_u, idx + 1#32, ()) m_u
              (by dsimp only; rw [hk1]; omega)
              ⟨by rw [hk1]; exact hk_lt, by rw [hk1]; exact hc1, st_u',
                by rw [hk1]; exact hs_u', hmu'⟩)
          (fun _ hJn => by
            c0_hsplit
            · have hlv_eq : (lit_k >>> 1#32).toNat = lit_k.toNat / 2 := m6_bv32_shr1_toNat lit_k
              have hlv_lt : (lit_k >>> 1#32).toNat < s.core.cur_vars := by omega
              have hfl_k := hs_k.hlen.core_ok.flags_len
              have htm_k := hs_k.hlen.scratch_ok.tarjan_mark_len
              have hfl_bd :
                  (BitVec.setWidth 64 (lit_k >>> 1#32)).toNat < st_k.core.flags.length := by
                rw [hfl_k, bv_c0_zext32_64]; omega
              have htm_bd : (BitVec.setWidth 64 (lit_k >>> 1#32)).toNat <
                  st_k.scratch.tarjan_mark.length := by
                rw [htm_k, bv_c0_zext32_64]; omega
              c0_hsplit
              · c0_hsteps!
                exact hDrop nv_k cnt idx limW aLimW st_k mk haLimW
                  hs_k.toStep13ConeSavedBase hmk
              · c0_hsteps_nogrp
                refine wp_join_group (ts := []) (fun () md => md = mk) ?_ ?_
                · rintro _ ⟨⟩ md hmd; subst md
                  refine wp_join_group (ts := []) (fun () mc => mc = mk) ?_ ?_
                  · rintro _ ⟨⟩ mc hmc; subst mc
                    refine wp_join_group (ts := [i32, .bool, .bool])
                      (fun (nv_u, _lim_u, _drop_u, ()) m_u =>
                        _lim_u = limW ∧ _drop_u = false ∧
                        nv_k.toNat ≤ nv_u.toNat ∧ ∃ ilv : Nat, ilv < nv_u.toNat ∧
                          (∀ v, nv_k.toNat ≤ v → v < nv_u.toNat → v = ilv) ∧
                          ∃ st_u : FullState,
                            Step13ConeSavedBase F_cur L mvC c s cv qi_l nvW ws0 scr0
                              nv_u.toNat nc_w st_u ∧
                            st_u.core.tmp = st_k.core.tmp ∧
                            (∀ j < nv_k.toNat,
                              st_u.scratch.work_stk1[j]? = st_k.scratch.work_stk1[j]?) ∧
                            (st_u.scratch.work_stk1[ilv]?.getD 0#32).toNat = lit_k.toNat / 2 ∧
                            st_u.scratch.tarjan_mark[lit_k.toNat / 2]?.getD 0#32 =
                              BitVec.ofNat 32 (ilv + 1) ∧
                            (FullMem c st_u ⋆ R) m_u)
                      (fun _ (nv_u, _lim_u, _drop_u, ()) m_u
                          ⟨hlim_u, hdrop_u, hnvku, ilv, hilv, hstep_new, st_u, hs_u, htmpu, hwku,
                            hwlv, htlv, hmu⟩
                          => by
                        subst _lim_u; subst _drop_u
                        have htm_u := hs_u.hlen.scratch_ok.tarjan_mark_len
                        have htmp_u := hs_u.hlen.core_ok.tmp_len_arr
                        have hcv_u := congrArg FullCoreState.cur_vars (s13ConeMask_core_eq hs_u.hag)
                        have htm_u_bd : (BitVec.setWidth 64 (lit_k >>> 1#32)).toNat <
                            st_u.scratch.tarjan_mark.length := by
                          rw [htm_u, bv_c0_zext32_64]; omega
                        have hcnt_bd : (BitVec.setWidth 64 cnt).toNat < st_u.core.tmp.length := by
                          have := hs_u.hcone.nv_le_cv; have := hs_u.hlen.core_ok.cur_vars_le
                          rw [htmp_u, bv_c0_zext32_64]; omega
                        have hscan := s13_scan_tmp_step hs_k hs_u htmpu hwku hnvku hstep_new hk_lt
                          hsz_cv hcnt_le hlit_ar hilv hwlv htlv hnd_cl hcr3_bd hsz_eq
                        c0_hsteps!
                        obtain ⟨hc1, hkh1, hs_u'⟩ := hscan
                        have htm_lk :
                            st_u.scratch.tarjan_mark[(BitVec.setWidth 64 (lit_k >>> 1#32)).toNat]'
                              htm_u_bd = st_u.scratch.tarjan_mark[lit_k.toNat / 2]?.getD 0#32 :=
                          (s13_tmk_at st_u lit_k (by rw [htm_u]; omega)).2.2
                        rw [hk1] at hs_u'
                        have hcnt1 : (cnt + (1 : BitVec 32)).toNat = cnt.toNat + 1 :=
                          m6_bv32_add1 (by have := c.hmaxv; unfold dimacsBound at this; omega)
                        refine hJn (nv_u, limW, false, cnt + 1, ()) _
                          ⟨rfl, rfl, by rw [hcnt1]; omega, by rw [hcnt1]; omega, _, hs_u', ?_⟩
                        have h3 : (3#64 : BitVec 64) = 3 := rfl
                        have h1 : (1#32 : BitVec 32) = 1 := rfl
                        have hshr : lit_k >>> (1 : Nat) = lit_k >>> 1#32 := by
                          apply BitVec.eq_of_toNat_eq; simp
                        have har_lit : ∀ hb, st_k.core.arena[(BitVec.setWidth 64 aCr.val + 3 +
                            BitVec.setWidth 64 idx).toNat]'hb = lit_k :=
                          fun hb => s13_getElem_congr (by simp only [h3]) hb hidx_bd
                        have htm_nat :
                            ∀ hb, st_u.scratch.tarjan_mark[(lit_k >>> (1 : Nat)).toNat]'hb =
                              st_u.scratch.tarjan_mark[lit_k.toNat / 2]?.getD 0#32 := fun hb => by
                          have h1' : (lit_k >>> (1 : Nat)).toNat =
                              (BitVec.setWidth 64 (lit_k >>> 1#32)).toNat := by
                            rw [hshr, bv_c0_zext32_64]
                          rw [← htm_lk]
                          exact s13_getElem_congr h1' hb htm_u_bd
                        simpa only [har_lit, bv_c0_zext32_64, htm_nat, h1] using hm)
                      (fun _ hJu => by
                        c0_hsplit
                        · have hmiss :
                              st_k.scratch.tarjan_mark[lit_k.toNat / 2]?.getD 0#32 = 0#32 := by
                            have hc0 :
                                st_k.scratch.tarjan_mark[(st_k.core.arena[(aCr.val.toNat +
                                  (3 : BitVec 64).toNat + idx.toNat) % 2 ^ 64]'har_c0_bd).toNat /
                                  2 ^ (1 : Nat)]'htm_c0_bd = 0#32 := ‹_›
                            simpa only [htm_c0_eq] using hc0
                          c0_hsplit
                          · c0_hsteps!
                            exact hDrop nv_k cnt idx true (Arg.imm true) st_k mk rfl
                              hs_k.toStep13ConeSavedBase hmk
                          · have hnv_lt_mv : nv_k.toNat < mvC.toNat := by
                              have hnh : ¬ aMvC.val.toNat ≤ nv_k.toNat := ‹_›
                              rw [haMvC] at hnh; omega
                            have hqi_nv_k : qi_l.toNat < nv_k.toNat :=
                              Nat.lt_of_lt_of_le hqi_nv hs_k.hsav_le
                            obtain ⟨hnv_cv, hnv1, hl_p, hag_p, hsb_p, hws_p⟩ :=
                              step13_cone_push_var_step_ok hs_k.toStep13ConeSavedBase hnv_lt_mv
                                hlv_lt hmiss hqi_nv_k
                            have hws_bd : (BitVec.setWidth 64 nv_k).toNat <
                                st_k.scratch.work_stk1.length := by
                              rw [hs_k.hlen.scratch_ok.work_stk1_len, bv_c0_zext32_64]; omega
                            c0_hsteps!
                            have hshr_nat : lit_k >>> (1 : Nat) = lit_k >>> 1#32 := by
                              apply BitVec.eq_of_toNat_eq; simp
                            have hlv_nat : (lit_k >>> (1 : Nat)).toNat = lit_k.toNat / 2 := by
                              simpa only [hshr_nat] using hlv_eq
                            let st_p : FullState :=
                              { st_k with scratch :=
                                { st_k.scratch with
                                  work_stk1 := st_k.scratch.work_stk1.set nv_k.toNat (lit_k >>> 1)
                                  tarjan_mark :=
                                    st_k.scratch.tarjan_mark.set (lit_k.toNat / 2) (nv_k + 1) } }
                            have hst_p_tmk :
                                st_p.scratch.tarjan_mark[lit_k.toNat / 2]?.getD 0#32 =
                                  BitVec.ofNat 32 (nv_k.toNat + 1) := by
                              have hltm : lit_k.toNat / 2 < st_k.scratch.tarjan_mark.length := by
                                rw [htm_k]; omega
                              rw [List.getElem?_set_self hltm, Option.getD_some,
                                show nv_k + (1 : BitVec 32) = nv_k + 1#32 from rfl,
                                m6_bv32_ofNat_add1]
                            have hws_new : (st_p.scratch.work_stk1[nv_k.toNat]?.getD 0#32).toNat =
                                lit_k.toNat / 2 := by
                              rw [List.getElem?_set_self
                                (by rw [hs_k.hlen.scratch_ok.work_stk1_len]; omega),
                                Option.getD_some, hlv_nat]
                            have hsb_p' :
                                Step13ConeSavedBase F_cur L mvC c s cv qi_l nvW ws0 scr0
                                  (nv_k + 1#32).toNat nc_w st_p := by
                              simpa only [st_p, hshr_nat, ← hlv_eq,
                                show (1 : BitVec 32) = 1#32 from rfl] using hsb_p
                            rw [haLimW]
                            refine hJu (nv_k + 1#32, limW, false, ()) _
                              ⟨rfl, rfl, by rw [hnv1]; omega, nv_k.toNat, by rw [hnv1]; omega,
                               fun v hv1 hv2 => by rw [hnv1] at hv2; omega,
                               _, hsb_p', rfl, fun j hj => List.getElem?_set_ne (by omega),
                               hws_new, hst_p_tmk, ?_⟩
                            have h3 : (3#64 : BitVec 64) = 3 := rfl
                            have hlv1 : ∀ hb,
                                (st_k.core.arena[(BitVec.setWidth 64 aCr.val + 3 +
                                  BitVec.setWidth 64 idx).toNat]'hb >>> (1 : Nat)).toNat =
                                  (st_k.core.arena[(BitVec.setWidth 64 aCr.val + 3 +
                                    BitVec.setWidth 64 idx).toNat]'hb).toNat / 2 := fun _ => by
                              simpa only [lit_k, h3] using hlv_nat
                            simpa only [st_p, lit_k, bv_c0_zext32_64, h3, hlv1] using hm
                        · have hne0 :
                              st_k.scratch.tarjan_mark[lit_k.toNat / 2]?.getD 0#32 ≠ 0#32 := by
                            have hc0 :
                                st_k.scratch.tarjan_mark[(st_k.core.arena[(aCr.val.toNat +
                                  (3 : BitVec 64).toNat + idx.toNat) % 2 ^ 64]'har_c0_bd).toNat /
                                  2 ^ (1 : Nat)]'htm_c0_bd ≠ 0#32 := ‹_›
                            simpa only [htm_c0_eq] using hc0
                          rcases hs_k.hcone.rev (lit_k.toNat / 2) (by rw [hcv_k]; omega) with
                            hz | ⟨ilv, hilv, hws_ilv, htm_ilv⟩
                          · exact absurd hz hne0
                          c0_hsteps!
                          rw [haLimW]
                          exact hJu (nv_k, limW, false, ()) mk
                            ⟨rfl, rfl, le_refl _, ilv, hilv, fun v hv1 hv2 => by omega,
                             st_k, hs_k.toStep13ConeSavedBase, rfl, fun _ _ => rfl,
                             hws_ilv, htm_ilv, hmk⟩)
                  · intro _ hJc
                    c0_hsplit
                    · c0_hsplit
                      · c0_hsteps!
                        exact hDrop nv_k cnt idx limW aLimW st_k mk haLimW
                          hs_k.toStep13ConeSavedBase hmk
                      · c0_hsteps!; exact hJc () mk rfl
                    · c0_hsteps!; exact hJc () mk rfl
                · intro _ hJb
                  c0_hsplit
                  · c0_hsplit
                    · c0_hsteps!
                      exact hDrop nv_k cnt idx limW aLimW st_k mk haLimW
                        hs_k.toStep13ConeSavedBase hmk
                    · c0_hsteps!; exact hJb () mk rfl
                  · c0_hsteps!; exact hJb () mk rfl
            · have hne0 : (st_k.core.vals[lit_k.toNat]?.getD 0#8).signExtend 32 = 0#32 → False := by
                have hc_ne :
                    ¬ (st_k.core.vals[(st_k.core.arena[(aCr.val.toNat + (3 : BitVec 64).toNat +
                        idx.toNat) % 2 ^ 64]'har_c0_bd).toNat]'hvk_c0).signExtend 32 =
                      BitVec.ofNat (OfNat.ofNat 32) (OfNat.ofNat 0) := ‹_›
                rw [hval_c0_eq] at hc_ne
                intro heq0
                exact hc_ne heq0
              have h255 : s.core.vals[lit_k.toNat]?.getD 0#8 = 255#8 := by
                rw [← hve_k]
                exact s13_neg_lt_not_one hne0 hnot_pos
                  (by rw [hve_k]; exact hw.vals_domain lit_k.toNat hl_lt_s)
              have hfal :
                  s.core.vals[(s.core.arena[cr.toNat + 3 + idx.toNat]?.getD 0#32).toNat]?.getD
                    0#8 = 255#8 := by
                simpa only [hlit_ar] using h255
              obtain ⟨_, hs_k'⟩ := s13_scan_skip_step hs_k hk_lt hfal
              rw [hk1] at hs_k'
              c0_hsteps!
              rw [haLimW]
              exact hJn (nv_k, limW, false, cnt, ()) mk
                ⟨rfl, rfl, le_refl _, by omega, st_k, hs_k', hmk⟩)
    · have hge : ¬ idx.toNat < sz.toNat := by
        have hnh : ¬ idx.toNat < aSz.val.toNat := ‹_›
        rwa [haSz] at hnh
      have hik_eq : idx.toNat = sz.toNat := Nat.le_antisymm hik_le (Nat.le_of_not_lt hge)
      c0_hsteps!
      exact hDone nv_k cnt idx st_k mk hs_k hik_eq hcnt_le hmk

/-! ## 3. Occurrence Clause Dispatch (`occClause`) -/

@[expose] def s13OccClauseExpr (pH pAr pVals pFl pTmk pTmp pWs pK : Val i64)
    (aCr aSz aPol aCv aCurTmk aMvC aLimV : Arg Val i32) (ncW : Val i32) (aLimW : Arg Val .bool)
    (aNvW : Arg Val i32)
    (k_clause_done : Val i32 → Val i32 → Val .bool → Expr Val Cont [i64]) :
    Expr Val Cont [i64] :=
  Expr.group
    (fun _Js =>
      Blocks.cons
        (fun p : Tup Val [i32, .bool, .bool, i32, i32] =>
          Expr.jnz (Arg.var p.snd.snd.fst)
            (s13RollbackLoopExpr pWs pTmk aNvW (Arg.var p.fst) fun nvr =>
              k_clause_done nvr ncW p.snd.fst)
            (s13AddClauseBlockExpr pH pTmp pK pWs pTmk
              (Arg.var p.snd.snd.snd.fst) aNvW (Arg.var p.fst) (Arg.var ncW) aLimV
              (Arg.var p.snd.fst) k_clause_done))
        Blocks.nil)
    fun Jcl =>
      s13OccScanExpr pAr pVals pFl pTmk pTmp pWs
        aCr aSz aPol aCv aCurTmk aMvC aLimW aNvW
        (fun nv lim cnt idx => Expr.jump Jcl.fst (Arg.var nv, lim, Arg.imm true,
          Arg.var cnt, Arg.var idx, ()))
        (fun nv lim cnt idx => Expr.jump Jcl.fst (Arg.var nv, lim, Arg.imm false,
          Arg.var cnt, Arg.var idx, ()))

theorem step13_cone_occ_clause_wp {Γ : Env}
    (hAddCl : Γ.Has "full_k6_add_clause" Kitten.Spec.step13K6AddClauseHwSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {L : K6Layout}
    {pH pAr pVals pFl pTmk pTmp pWs pK : Val i64}
    {mvC cr sz pol cv curTmk nvW ncW : BitVec 32}
    {aCr aSz aPol aCv aCurTmk aMvC aLimV : Arg Val i32} {limW : Bool} {aLimW : Arg Val .bool}
    {aNvW : Arg Val i32} {qi_l : BitVec 32} {s stW : FullState}
    {R : Mem 64 → Prop} {m0 : Mem 64} {Q : Post [i64]} {X : XPost}
    {k_done : Val i32 → Val i32 → Val .bool → Expr Val Cont [i64]}
    (hLscr : L.scrLen = c.scratch_cap) (hLmv : L.maxV = k6MaxV c.scratch_cap)
    (hpH : pH = c.hdr) (hpAr : pAr = c.pArena) (hpVals : pVals = c.pVals)
    (hpFl : pFl = c.pFlags) (hpTmk : pTmk = c.pTarjanMark) (hpTmp : pTmp = c.pTmp)
    (hpWs : pWs = c.pWorkStk1) (hpK : pK = L.kPtr c.pScratchBuf)
    (haCr : aCr.val = cr) (haSz : aSz.val = sz) (haPol : aPol.val = pol)
    (haCv : aCv.val = cv) (haCurTmk : aCurTmk.val = curTmk)
    (haMvC : aMvC.val = mvC) (haLimV : aLimV.val.toNat ≤ mvC.toNat) (haLimW : aLimW.val = limW)
    (haNvW : aNvW.val = nvW) (hlimW : limW = false)
    (hlen_s : FullState.LengthsOk c s) (hw : FullWitnessInv c F0 F_cur s.core)
    (hcl0 : s.core.cur_level = 0)
    (hnd_cl : ((fullArenaClauseLits s cr.toNat).map (· / 2)).Nodup)
    (hcr_ref : cr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hng : fullArenaClauseGarbCore s.core cr.toNat = false)
    (hsz_eq : sz.toNat = fullArenaClauseSizeCore s.core cr.toNat)
    (hsz_cv : sz.toNat ≤ s.core.cur_vars)
    (hcr3_bd : cr.toNat + 3 + sz.toNat ≤ s.core.arena.length)
    (hnc : ncW.toNat < L.maxOrig) (hqi_nv : qi_l.toNat < nvW.toNat)
    (hbW : Step13ConeBase F_cur L mvC c s cv qi_l nvW.toNat ncW.toNat stW)
    (hm0 : (FullMem c stW ⋆ R) m0)
    (hk : ∀ (nv' nc' : BitVec 32) (lim' : Bool) (st' : FullState) (m' : Mem 64),
      nvW.toNat ≤ nv'.toNat →
      Step13ConeBase F_cur L mvC c s cv qi_l nv'.toNat nc'.toNat st' →
      (FullMem c st' ⋆ R) m' →
      wp Γ Q X (k_done nv' nc' lim') m') :
    wp Γ Q X (s13OccClauseExpr pH pAr pVals pFl pTmk pTmp pWs pK
      aCr aSz aPol aCv aCurTmk aMvC aLimV ncW aLimW aNvW k_done) m0 := by
  subst hpH hpTmp hpWs hpTmk
  let ws0 := stW.scratch.work_stk1
  let scr0 := stW.scratch.scratch_buf
  refine wp_join_group (ts := [i32, .bool, .bool, i32, i32])
    (fun (nvE, limE, dropE, cntE, idxE, ()) mE => ∃ stE : FullState,
      Step13ConeSavedBase F_cur L mvC c s cv qi_l nvW ws0 scr0 nvE.toNat ncW.toNat stE ∧
      (dropE = false → limE = false ∧
        Step13ConeScanBase F_cur L mvC c s cv qi_l nvW ws0 scr0 cr
          nvE.toNat ncW.toNat cntE.toNat idxE.toNat stE ∧
        idxE.toNat = sz.toNat ∧ cntE.toNat ≤ idxE.toNat) ∧
      (FullMem c stE ⋆ R) mE) ?_ ?_
  · rintro _ ⟨nvE, limE, dropE, cntE, idxE, ⟨⟩⟩ mE ⟨stE, hsE, hndrop, hmE⟩
    have hsav_ge1 : 1 ≤ nvW.toNat := hbW.hcone.nv_ge1
    have hbdd_s : K6LitsBounded nvW.toNat (k6StateOfScratch L scr0) := hbW.hcone.k6_bdd
    have htrl_s : ∀ l ∈ k6TrailLits (k6StateOfScratch L scr0), l < 2 * nvW.toNat :=
      hbW.hcone.k6_trl_bdd
    c0_hsteps_nogrp
    c0_hsplit
    · refine step13_cone_rollback_loop_wp haNvW rfl hsE.hlen hsE.hag hsE.hgu_sav hsE.hcone
        hsav_ge1 hsE.hsav_le hsE.hscr hbdd_s htrl_s hsE.hws hmE ?_
      intro stR mR hlR haR hguR hcR _ hwsR hmR
      have hwkR : (stR.scratch.work_stk1[qi_l.toNat]?.getD 0#32).toNat = cv.toNat := by
        rw [hwsR qi_l.toNat hqi_nv, ← hsE.hws qi_l.toNat hqi_nv]; exact hsE.hwk
      have htmkR : stR.scratch.tarjan_mark[cv.toNat]?.getD 0#32 =
          BitVec.ofNat 32 (qi_l.toNat + 1) := by
        have hf := (hcR.fwd qi_l.toNat hqi_nv).2
        rwa [hwkR] at hf
      exact hk nvW ncW limE stR mR (le_refl _)
        ⟨hlR, haR, hguR, hcR, htmkR, hwkR⟩ hmR
    · have hd_f : dropE = false := by cases dropE <;> simp at ‹_› ⊢
      obtain ⟨hlim_f, hsbE, hik_eq, hcnt_le⟩ := hndrop hd_f
      have hcnt_le_nv : cntE.toNat ≤ nvE.toNat := m6_cone_cnt_le_nv hsbE.hlts hsbE.hnd
      have hcnt28 : cntE.toNat < 2 ^ 28 := by
        have := hsE.hcone.nv_le_mvC; have := hsE.hcone.mvC_leMax
        have := L.hmaxV; omega
      have hcnt_tmp : cntE.toNat ≤ stE.core.tmp.length := by
        have := hsE.hcone.nv_le_cv; have := hsE.hlen.core_ok.cur_vars_le
        rw [hsE.hlen.core_ok.tmp_len_arr]; omega
      have hnew_in : nvW.toNat < nvE.toNat →
          ∃ i, i < cntE.toNat ∧ (stE.core.tmp[i]?.getD 0#32).toNat / 2 + 1 = nvE.toNat := by
        intro hlt
        obtain ⟨i, hi, heq⟩ := hsbE.hsav_vars (nvE.toNat - 1) (by omega) (by omega)
        exact ⟨i, hi, by omega⟩
      have hent : (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((stE.core.tmp.take cntE.toNat).map (fun x => m6ConeLift
            stE.scratch.work_stk1 x.toNat))) := by
        refine s13_cone_clause_entails_filtered hw hcl0 hcr_ref hng ?_
        intro l hl
        rw [mem_fullArenaClauseLitsCore_iff (by rw [← hsz_eq]; exact hcr3_bd)] at hl
        obtain ⟨i, hi, rfl⟩ := hl
        have hi' : i < idxE.toNat := by rw [hik_eq, hsz_eq]; exact hi
        have hbi : cr.toNat + 3 + i < s.core.arena.length := by omega
        simpa [List.getElem?_eq_getElem hbi, Option.getD_some] using hsbE.hcov i hi'
      refine step13_cone_add_clause_block_wp hAddCl hLscr hLmv hpK (aSz := Arg.var cntE) rfl
        haNvW (aNv := Arg.var nvE) rfl rfl haLimV (aLim := Arg.var limE) rfl hsE hqi_nv
        hsav_ge1 hbdd_s htrl_s hnew_in hnc hcnt28 hcnt_tmp hsbE.hlts hent hlim_f hmE ?_
      intro nv' nc' lim' st' m' _ _ hsav_le' _ _ hb' hm'
      exact hk nv' nc' lim' st' m' hsav_le' hb' hm'
  · intro _ hJcl
    refine step13_cone_occ_scan_wp hpAr hpVals hpFl rfl rfl rfl
      haCr haSz haPol haCv haCurTmk haMvC haLimW haNvW hlen_s hw hnd_cl hcr_ref hng
      hsz_eq hsz_cv hcr3_bd hqi_nv hbW hm0 ?_ ?_
    · intro nvE cntE idxE limE aL stE mE haL hsE hmE
      c0_hsteps!
      rw [haL]
      exact hJcl (nvE, limE, true, cntE, idxE, ()) mE
        ⟨stE, hsE, fun h => absurd h (by decide), hmE⟩
    · intro nvE cntE idxE stE mE hsbE hik_eq hcnt_le hmE
      c0_hsteps!
      rw [haLimW]
      exact hJcl (nvE, limW, false, cntE, idxE, ()) mE
        ⟨stE, hsbE.toStep13ConeSavedBase, fun _ => ⟨hlimW, hsbE, hik_eq, hcnt_le⟩, hmE⟩

/-! ## 4. Occurrence Watch List Loop (`occWatch`) -/

@[expose] def s13OccWatchExpr (pH pAr pWstk pVals pFl pTmk pTmp pWs pK pWEnd : Val i64)
    (aPol aCv aCurTmk aMvC aLimV aMaxOrig aNv0 aNc0 : Arg Val i32) (aLim0 : Arg Val .bool)
    (aWOff : Arg Val i64)
    (k_exit : Val i32 → Val i32 → Val .bool → Val i64 → Expr Val Cont [i64]) :
    Expr Val Cont [i64] :=
  Expr.group
    (fun Jw =>
      Blocks.cons
        (fun p : Tup Val [i32, i32, .bool, i64] =>
          Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl)
            (Arg.var p.snd.snd.snd.fst, Arg.var pWEnd, ())) fun hlt =>
          Expr.jnz (Arg.var hlt.fst)
            (Expr.jnz (Arg.var p.snd.snd.fst)
              (k_exit p.fst p.snd.fst p.snd.snd.fst p.snd.snd.snd.fst)
              (Expr.let_ (Op.mk (.cmp .ult i32 .bool rfl)
                (Arg.var p.snd.fst, aMaxOrig, ())) fun hnc =>
                Expr.jnz (Arg.var hnc.fst)
                  (Expr.let_ (Op.mk (.mul i64)
                    (Arg.var p.snd.snd.snd.fst, Arg.imm 4, ())) fun pwo =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var pWstk, Arg.var pwo.fst, ())) fun pwa =>
                    Expr.load i32 (Arg.var pwa.fst) fun w0 =>
                    Expr.let_ (Op.mk (.add i64)
                      (Arg.var p.snd.snd.snd.fst, Arg.imm 1, ())) fun p1 =>
                    Expr.let_ (Op.mk (.and i32) (Arg.var w0, Arg.imm 2147483648, ())) fun wbin =>
                    Expr.let_ (Op.mk (.cmp .ne i32 .bool rfl)
                      (Arg.var wbin.fst, Arg.imm 0, ())) fun hbin =>
                    Expr.jnz (Arg.var hbin.fst)
                      (Expr.jump Jw.fst (Arg.var p.fst, Arg.var p.snd.fst,
                        Arg.var p.snd.snd.fst, Arg.var p1.fst, ()))
                      (Expr.let_ (Op.mk (.cmp .uge i64 .bool rfl)
                        (Arg.var p1.fst, Arg.var pWEnd, ())) fun hge =>
                        Expr.jnz (Arg.var hge.fst)
                          (k_exit p.fst p.snd.fst p.snd.snd.fst p1.fst)
                          (Expr.let_ (Op.mk (.mul i64) (Arg.var p1.fst, Arg.imm 4, ())) fun pw1o =>
                            Expr.let_ (Op.mk (.add i64) (Arg.var pWstk, Arg.var pw1o.fst, ()))
                              fun pw1a =>
                            Expr.load i32 (Arg.var pw1a.fst) fun cr =>
                            Expr.let_ (Op.mk (.add i64) (Arg.var p1.fst, Arg.imm 1, ())) fun p2 =>
                            Expr.let_ (Op.mk (.zext 32 64) (Arg.var cr, ())) fun crz =>
                            Expr.let_ (Op.mk (.add i64) (Arg.var crz.fst, Arg.imm 3, ())) fun cr3 =>
                            Expr.let_ (Op.mk (.add i64) (Arg.var pH, Arg.imm 48, ())) fun pala =>
                            Expr.load i64 (Arg.var pala.fst) fun al1 =>
                            Expr.let_ (Op.mk (.cmp .ugt i64 .bool rfl)
                              (Arg.var cr3.fst, Arg.var al1, ())) fun hgt1 =>
                            Expr.jnz (Arg.var hgt1.fst)
                              (Expr.jump Jw.fst (Arg.var p.fst, Arg.var p.snd.fst,
                                Arg.var p.snd.snd.fst, Arg.var p2.fst, ()))
                              (Expr.let_ (Op.mk (.zext 32 64) (Arg.var cr, ())) fun crz2 =>
                                Expr.let_ (Op.mk (.add i64)
                                  (Arg.var crz2.fst, Arg.imm 2, ())) fun cszi =>
                                Expr.let_ (Op.mk (.mul i64)
                                  (Arg.var cszi.fst, Arg.imm 4, ())) fun cszo =>
                                Expr.let_ (Op.mk (.add i64)
                                  (Arg.var pAr, Arg.var cszo.fst, ())) fun csza =>
                                Expr.load i32 (Arg.var csza.fst) fun sz =>
                                Expr.let_ (Op.mk (.zext 32 64) (Arg.var cr, ())) fun crz3 =>
                                Expr.let_ (Op.mk (.mul i64)
                                  (Arg.var crz3.fst, Arg.imm 4, ())) fun chdro =>
                                Expr.let_ (Op.mk (.add i64)
                                  (Arg.var pAr, Arg.var chdro.fst, ())) fun chdra =>
                                Expr.load i32 (Arg.var chdra.fst) fun hdr =>
                                Expr.let_ (Op.mk (.or i32)
                                  (Arg.imm 524288, Arg.imm 4194304, ())) fun gmsk =>
                                Expr.let_ (Op.mk (.and i32)
                                  (Arg.var hdr, Arg.var gmsk.fst, ())) fun hg =>
                                Expr.let_ (Op.mk (.cmp .ne i32 .bool rfl)
                                  (Arg.var hg.fst, Arg.imm 0, ())) fun hgn =>
                                Expr.jnz (Arg.var hgn.fst)
                                  (Expr.jump Jw.fst (Arg.var p.fst, Arg.var p.snd.fst,
                                    Arg.var p.snd.snd.fst, Arg.var p2.fst, ()))
                                  (Expr.let_ (Op.mk (.cmp .ult i32 .bool rfl)
                                    (Arg.var sz, Arg.imm 3, ())) fun hsz3 =>
                                    Expr.jnz (Arg.var hsz3.fst)
                                      (Expr.jump Jw.fst (Arg.var p.fst, Arg.var p.snd.fst,
                                        Arg.var p.snd.snd.fst, Arg.var p2.fst, ()))
                                      (Expr.let_ (Op.mk (.zext 32 64) (Arg.var cr, ())) fun crz4 =>
                                        Expr.let_ (Op.mk (.add i64)
                                          (Arg.var crz4.fst, Arg.imm 3, ())) fun cr3' =>
                                        Expr.let_ (Op.mk (.zext 32 64) (Arg.var sz, ())) fun szz =>
                                        Expr.let_ (Op.mk (.add i64)
                                          (Arg.var cr3'.fst, Arg.var szz.fst, ())) fun cend =>
                                        Expr.let_ (Op.mk (.add i64)
                                          (Arg.var pH, Arg.imm 48, ())) fun pala2 =>
                                        Expr.load i64 (Arg.var pala2.fst) fun al2 =>
                                        Expr.let_ (Op.mk (.cmp .ugt i64 .bool rfl)
                                          (Arg.var cend.fst, Arg.var al2, ())) fun hgt2 =>
                                        Expr.jnz (Arg.var hgt2.fst)
                                          (Expr.jump Jw.fst (Arg.var p.fst, Arg.var p.snd.fst,
                                            Arg.var p.snd.snd.fst, Arg.var p2.fst, ()))
                                          (s13OccClauseExpr pH pAr pVals pFl pTmk pTmp pWs pK
                                            (Arg.var cr) (Arg.var sz) aPol aCv aCurTmk aMvC aLimV
                                            p.snd.fst (Arg.var p.snd.snd.fst)
                                            (Arg.var p.fst)
                                            (fun nv' nc' lim' => Expr.jump Jw.fst
                                              (Arg.var nv', Arg.var nc', Arg.var lim',
                                                Arg.var p2.fst, ())))))))))
                  (k_exit p.fst p.snd.fst p.snd.snd.fst p.snd.snd.snd.fst)))
            (k_exit p.fst p.snd.fst p.snd.snd.fst p.snd.snd.snd.fst))
        Blocks.nil)
    fun Jw => Expr.jump Jw.fst (aNv0, aNc0, aLim0, aWOff, ())

theorem step13_cone_occ_watch_wp {Γ : Env}
    (hAddCl : Γ.Has "full_k6_add_clause" Kitten.Spec.step13K6AddClauseHwSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {L : K6Layout}
    {pH pAr pWstk pVals pFl pTmk pTmp pWs pK pWEnd : Val i64}
    {mvC maxOrig pol cv curTmk nv0 nc0 layerEnd lit : BitVec 32}
    {aPol aCv aCurTmk aMvC aLimV aMaxOrig aNv0 aNc0 : Arg Val i32} {lim0 : Bool}
    {aLim0 : Arg Val .bool} {wOff : BitVec 64} {aWOff : Arg Val i64}
    {qi_l : BitVec 32} {s st0 : FullState}
    {R : Mem 64 → Prop} {m0 : Mem 64} {Q : Post [i64]} {X : XPost}
    {k_exit : Val i32 → Val i32 → Val .bool → Val i64 → Expr Val Cont [i64]}
    (hLscr : L.scrLen = c.scratch_cap) (hLmv : L.maxV = k6MaxV c.scratch_cap)
    (hpH : pH = c.hdr) (hpAr : pAr = c.pArena) (hpWstk : pWstk = c.pWstk)
    (hpVals : pVals = c.pVals) (hpFl : pFl = c.pFlags) (hpTmk : pTmk = c.pTarjanMark)
    (hpTmp : pTmp = c.pTmp) (hpWs : pWs = c.pWorkStk1) (hpK : pK = L.kPtr c.pScratchBuf)
    (haPol : aPol.val = pol) (haCv : aCv.val = cv) (haCurTmk : aCurTmk.val = curTmk)
    (haMvC : aMvC.val = mvC) (haLimV : aLimV.val.toNat ≤ mvC.toNat)
    (haMaxOrig : aMaxOrig.val = maxOrig)
    (haNv0 : aNv0.val = nv0) (haNc0 : aNc0.val = nc0) (haLim0 : aLim0.val = lim0)
    (haWOff : aWOff.val = wOff)
    (hmaxOrig : maxOrig.toNat ≤ L.maxOrig)
    (hlen_s : FullState.LengthsOk c s) (hw : FullWitnessInv c F0 F_cur s.core)
    (hcl0 : s.core.cur_level = 0) (hnd_s : FullArenaVarsNodup s)
    (hdw : DenseWatchesInv F_cur s.core) (hlit_lt : lit.toNat < 2 * s.core.cur_vars)
    (hwOff_eq : wOff.toNat = fullWatchOffCore s.core lit.toNat)
    (hwEnd_eq : pWEnd.toNat =
      fullWatchOffCore s.core lit.toNat + fullWatchSizeCore s.core lit.toNat)
    (hwOff_le : wOff.toNat ≤ pWEnd.toNat) (hwEnd_ws : pWEnd.toNat ≤ s.core.wstk.length)
    (hqi_le : qi_l.toNat < layerEnd.toNat) (hlay_le : layerEnd.toNat ≤ nv0.toNat)
    (hb0 : Step13ConeBase F_cur L mvC c s cv qi_l nv0.toNat nc0.toNat st0)
    (hm0 : (FullMem c st0 ⋆ R) m0)
    (hExit : ∀ (nvE ncE : BitVec 32) (limE : Bool) (pwE : BitVec 64)
        (stE : FullState) (mE : Mem 64),
      layerEnd.toNat ≤ nvE.toNat →
      Step13ConeBase F_cur L mvC c s cv qi_l nvE.toNat ncE.toNat stE →
      (FullMem c stE ⋆ R) mE →
      wp Γ Q X (k_exit nvE ncE limE pwE) mE) :
    wp Γ Q X (s13OccWatchExpr pH pAr pWstk pVals pFl pTmk pTmp pWs pK pWEnd
      aPol aCv aCurTmk aMvC aLimV aMaxOrig aNv0 aNc0 aLim0 aWOff k_exit) m0 := by
  subst hpH hpAr hpWstk hpVals hpFl hpTmk hpTmp hpWs
  refine wp_loop_inv (ts := [i32, i32, .bool, i64])
    (fun (nv_w, nc_w, _lim_w, pw, ()) mw =>
      pw.toNat ≤ pWEnd.toNat ∧ layerEnd.toNat ≤ nv_w.toNat ∧
      DenseWatchSliceOk F_cur s.core lit.toNat pw.toNat (pWEnd.toNat - pw.toNat) ∧
      ∃ st_w : FullState, Step13ConeBase F_cur L mvC c s cv qi_l nv_w.toNat nc_w.toNat st_w ∧
        (FullMem c st_w ⋆ R) mw)
    (fun (_, _, _, pw, ()) _ => pWEnd.toNat - pw.toNat) ?_ ?_
  · intro _ hJw
    c0_hsteps!
    rw [haNv0, haNc0, haLim0, haWOff]
    refine hJw (nv0, nc0, lim0, wOff, ()) m0 ⟨hwOff_le, hlay_le, ?_, st0, hb0, hm0⟩
    · rw [hwOff_eq, hwEnd_eq, Nat.add_sub_cancel_left]; exact hdw.slices lit.toNat hlit_lt
  · rintro _ ⟨nv_w, nc_w, lim_w, pw, ⟨⟩⟩ mw ⟨hp_le, hnv_mono, hslice, st_w, hb_w, hmw⟩ hJw
    have hw_core := s13ConeMask_core_eq hb_w.hag
    dsimp only at hw_core
    have hwstk_eq : st_w.core.wstk = s.core.wstk := by
      simpa using congrArg FullCoreState.wstk hw_core
    have har_eq : st_w.core.arena = s.core.arena := by
      simpa using congrArg FullCoreState.arena hw_core
    have hal_eq : st_w.core.arena_len = s.core.arena_len := by
      simpa using congrArg FullCoreState.arena_len hw_core
    c0_hsplit
    · have hp_lt : pw.toNat < pWEnd.toNat := ‹_›
      c0_hsplit
      · c0_hsteps!
        dsimp only [Prod.fst, Prod.snd]
        exact hExit nv_w nc_w lim_w pw st_w mw hnv_mono hb_w hmw
      · have hlim_f : lim_w = false := by cases lim_w <;> simp at ‹_› ⊢
        c0_hsplit
        · have hnc_lt : nc_w.toNat < L.maxOrig := by
            have hlt : nc_w.toNat < aMaxOrig.val.toNat := ‹_›
            rw [haMaxOrig] at hlt; omega
          have hwcap := c.hwcap; unfold dimacsBound at hwcap
          have hp_len := hlen_s.core_ok.wstk_len_arr
          have hp_wstk : pw.toNat < st_w.core.wstk.length :=
            fid_cone_hp_wstk hwstk_eq hp_lt hwEnd_ws
          have hp1_nat : (pw + 1#64).toNat = pw.toNat + 1 :=
            fid_cone_wstk_p_toNat_eq pw (by have := hlen_s.core_ok.wlen_le; omega)
          let w0 : BitVec 32 := st_w.core.wstk[pw.toNat]'hp_wstk
          have hw0_s : s.core.wstk[pw.toNat]? = some w0 := by
            have h1 : st_w.core.wstk[pw.toNat]? = some w0 := List.getElem?_eq_getElem hp_wstk
            rwa [hwstk_eq] at h1
          c0_hsplit
          · have hbin : w0 &&& 2147483648#32 ≠ 0#32 := ‹_›
            obtain ⟨_, _, _, hslice1⟩ :=
              m6_denseSlice_step_bin hslice (Nat.sub_pos_of_lt hp_lt) hw0_s hbin
            c0_hsteps!
            exact hJw (nv_w, nc_w, lim_w, pw + 1#64, ()) mw (by dsimp only; omega)
              ⟨by omega, hnv_mono, by rw [hp1_nat, ← fid_cone_sub_sub_eq]; exact hslice1,
                st_w, hb_w, hmw⟩
          · have hocc : w0 &&& 2147483648#32 = 0#32 := ‹_›
            obtain ⟨hrem2, _, cr, hcr_s, hcr_lt, hcr_ref, hslice2⟩ :=
              m6_denseSlice_step_occ hslice (Nat.sub_pos_of_lt hp_lt) hw0_s hocc
            c0_hsplit
            · c0_hsteps!
              dsimp only [Prod.fst, Prod.snd]
              exact hExit nv_w nc_w lim_w (pw + 1#64) st_w mw hnv_mono hb_w hmw
            · have hp1_lt : (pw + 1#64).toNat < pWEnd.toNat := by omega
              have hp1_wstk : (pw + 1#64).toNat < st_w.core.wstk.length :=
                fid_cone_hp_wstk hwstk_eq hp1_lt hwEnd_ws
              have hcr_gen : ∀ h : (pw + 1#64).toNat < st_w.core.wstk.length,
                  st_w.core.wstk[(pw + 1#64).toNat]'h = cr := fun h => by
                rw [← Option.some_inj, ← List.getElem?_eq_getElem h, hwstk_eq, hp1_nat, hcr_s]
              have hp2_nat : (pw + 1#64 + 1#64).toNat = pw.toNat + 2 := by
                have := fid_cone_wstk_p_toNat_eq (pw + 1#64) (by omega)
                omega
              have hwf := hw.arena.refs_wf cr.toNat hcr_ref
              have har_s := hlen_s.core_ok.arena_len_arr
              have hal_le := hlen_s.core_ok.arena_len_le
              have hacap := c.harena; unfold dimacsBound at hacap
              have har_len_fit : st_w.core.arena_len < 2 ^ 64 := by omega
              c0_hsplit
              · c0_hsteps!
                exact hJw (nv_w, nc_w, lim_w, pw + 1#64 + 1#64, ()) mw
                  (by dsimp only; omega)
                  ⟨by omega, hnv_mono, by rw [hp2_nat, ← fid_cone_sub_sub_eq]; exact hslice2,
                    st_w, hb_w, hmw⟩
              · have har_cr_bd : (BitVec.setWidth 64 cr).toNat < st_w.core.arena.length := by
                  rw [hb_w.hlen.core_ok.arena_len_arr, bv_c0_zext32_64]; omega
                have har_cr2_bd :
                    (BitVec.setWidth 64 cr + 2#64).toNat < st_w.core.arena.length := by
                  rw [hb_w.hlen.core_ok.arena_len_arr, BitVec.toNat_add, bv_c0_zext32_64,
                    show (2#64 : BitVec 64).toNat = 2 from rfl]; omega
                simp only [show (1 : BitVec 64) = 1#64 from rfl, hcr_gen]
                let sz := st_w.core.arena[(BitVec.setWidth 64 cr + 2#64).toNat]'har_cr2_bd
                have hsz_core : sz.toNat = fullArenaClauseSizeCore s.core cr.toNat := by
                  have hk2 : (BitVec.setWidth 64 cr + 2#64).toNat = cr.toNat + 2 := by
                    rw [BitVec.toNat_add, bv_c0_zext32_64,
                      show (2#64 : BitVec 64).toNat = 2 from rfl]
                    omega
                  have hbd2 : cr.toNat + 2 < s.core.arena.length := by omega
                  unfold fullArenaClauseSizeCore
                  rw [List.getElem?_eq_getElem hbd2, Option.getD_some]
                  have hget : s.core.arena[cr.toNat + 2]? = some sz := by
                    have h1 : st_w.core.arena[(BitVec.setWidth 64 cr + 2#64).toNat]? = some sz :=
                      List.getElem?_eq_getElem har_cr2_bd
                    rwa [har_eq, hk2] at h1
                  rw [List.getElem?_eq_getElem hbd2] at hget
                  exact congrArg BitVec.toNat (Option.some.inj hget).symm
                c0_hsplit
                · c0_hsteps!
                  exact hJw (nv_w, nc_w, lim_w, pw + 1#64 + 1#64, ()) mw
                    (by dsimp only; omega)
                    ⟨by omega, hnv_mono, by rw [hp2_nat, ← fid_cone_sub_sub_eq]; exact hslice2,
                      st_w, hb_w, hmw⟩
                · have hcr_n_bd : cr.toNat < st_w.core.arena.length := by
                    simpa [bv_c0_zext32_64] using har_cr_bd
                  have hgr0 : st_w.core.arena[cr.toNat]'hcr_n_bd &&&
                      (0x00080000#32 ||| 0x00400000#32) = 0#32 := by
                    have hcongr := s13_getElem_congr (bv_c0_zext32_64 cr) har_cr_bd hcr_n_bd
                    simpa only [hcongr] using (‹_› : _ = 0#32)
                  obtain ⟨hng, hcr3_bd_s, hsz_cv, hcr3_al⟩ :=
                    s13_occ_hdr_ok hcr_n_bd hlen_s hw hnd_s har_eq hcr_ref hsz_core hgr0
                  c0_hsplit
                  · c0_hsteps!
                    exact hJw (nv_w, nc_w, lim_w, pw + 1#64 + 1#64, ()) mw
                      (by dsimp only; omega)
                      ⟨by omega, hnv_mono, by rw [hp2_nat, ← fid_cone_sub_sub_eq]; exact hslice2,
                        st_w, hb_w, hmw⟩
                  · c0_hsplit
                    · c0_hsteps!
                      exact hJw (nv_w, nc_w, lim_w, pw + 1#64 + 1#64, ()) mw
                        (by dsimp only; omega)
                        ⟨by omega, hnv_mono, by rw [hp2_nat, ← fid_cone_sub_sub_eq]; exact hslice2,
                          st_w, hb_w, hmw⟩
                    · have hqi_nv : qi_l.toNat < nv_w.toNat := Nat.lt_of_lt_of_le hqi_le hnv_mono
                      refine step13_cone_occ_clause_wp hAddCl hLscr hLmv rfl rfl rfl rfl rfl rfl
                        rfl hpK rfl rfl haPol haCv haCurTmk haMvC haLimV rfl rfl hlim_f hlen_s
                        hw hcl0 (hnd_s cr.toNat hcr_ref hng) hcr_ref hng hsz_core hsz_cv hcr3_bd_s
                        hnc_lt hqi_nv hb_w hmw ?_
                      intro nv' nc' lim' st' m' hnv'_le hb' hm'
                      c0_hsteps!
                      exact hJw (nv', nc', lim', pw + 1#64 + 1#64, ()) m'
                        (by dsimp only; omega)
                        ⟨by omega, Nat.le_trans hnv_mono hnv'_le,
                          by rw [hp2_nat, ← fid_cone_sub_sub_eq]; exact hslice2,
                          st', hb', hm'⟩
        · c0_hsteps!
          dsimp only [Prod.fst, Prod.snd]
          exact hExit nv_w nc_w lim_w pw st_w mw hnv_mono hb_w hmw
    · c0_hsteps!
      dsimp only [Prod.fst, Prod.snd]
      exact hExit nv_w nc_w lim_w pw st_w mw hnv_mono hb_w hmw

/-! ## 5. Occurrence Polarity Loop (`occPass`) -/

@[expose] def s13OccPassExpr (pH pAr pWvec pWstk pVals pFl pTmk pTmp pWs pK : Val i64)
    (aCv aCurTmk aMvC aLimV aMaxOrig aNv0 aNc0 : Arg Val i32) (aLim0 : Arg Val .bool)
    (k_done : Val i32 → Val i32 → Val .bool → Expr Val Cont [i64]) :
    Expr Val Cont [i64] :=
  Expr.group
    (fun Jpol =>
      Blocks.cons
        (fun p : Tup Val [i32, i32, .bool, i32] =>
          Expr.let_ (Op.mk (.cmp .ult i32 .bool rfl) (Arg.var p.snd.snd.snd.fst, Arg.imm 2, ()))
            fun hpol =>
          Expr.jnz (Arg.var hpol.fst)
            (Expr.jnz (Arg.var p.snd.snd.fst)
              (k_done p.fst p.snd.fst p.snd.snd.fst)
              (Expr.let_ (Op.mk (.cmp .ult i32 .bool rfl) (Arg.var p.snd.fst, aMaxOrig, ()))
                fun hnc =>
                Expr.jnz (Arg.var hnc.fst)
                  (Expr.let_ (Op.mk (.shl i32) (aCv, Arg.imm 1, ())) fun cv2 =>
                    Expr.let_ (Op.mk (.or i32) (Arg.var cv2.fst, Arg.var p.snd.snd.snd.fst, ()))
                      fun plit =>
                    Expr.let_ (Op.mk (.zext 32 64) (Arg.var plit.fst, ())) fun plitz =>
                    Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun pone =>
                    Expr.let_ (Op.mk (.shl i64) (Arg.var plitz.fst, Arg.var pone.fst, ()))
                      fun p2l =>
                    Expr.let_ (Op.mk (.mul i64) (Arg.var p2l.fst, Arg.imm 4, ())) fun pwo =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var pWvec, Arg.var pwo.fst, ())) fun pwa =>
                    Expr.load i32 (Arg.var pwa.fst) fun woff =>
                    Expr.let_ (Op.mk (.zext 32 64) (Arg.var woff, ())) fun woffz =>
                    Expr.let_ (Op.mk (.zext 32 64) (Arg.var plit.fst, ())) fun plitz2 =>
                    Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun pone2 =>
                    Expr.let_ (Op.mk (.shl i64) (Arg.var plitz2.fst, Arg.var pone2.fst, ()))
                      fun p2l2 =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var p2l2.fst, Arg.imm 1, ())) fun p2l21 =>
                    Expr.let_ (Op.mk (.mul i64) (Arg.var p2l21.fst, Arg.imm 4, ())) fun pwso =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var pWvec, Arg.var pwso.fst, ())) fun pwsa =>
                    Expr.load i32 (Arg.var pwsa.fst) fun wsz =>
                    Expr.let_ (Op.mk (.zext 32 64) (Arg.var wsz, ())) fun wszz =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var woffz.fst, Arg.var wszz.fst, ()))
                      fun wend =>
                    Expr.group
                      (fun _ => Blocks.cons
                        (fun q : Tup Val [i32, i32, .bool, i64] =>
                          Expr.let_ (Op.mk (.add i32) (Arg.var p.snd.snd.snd.fst, Arg.imm 1, ()))
                            fun p1 =>
                          Expr.jump Jpol.fst (Arg.var q.fst, Arg.var q.snd.fst,
                            Arg.var q.snd.snd.fst, Arg.var p1.fst, ()))
                        Blocks.nil)
                      fun Jwe =>
                        s13OccWatchExpr pH pAr pWstk pVals pFl pTmk pTmp pWs pK wend.fst
                          (Arg.var p.snd.snd.snd.fst) aCv aCurTmk aMvC aLimV aMaxOrig
                          (Arg.var p.fst) (Arg.var p.snd.fst) (Arg.var p.snd.snd.fst)
                          (Arg.var woffz.fst)
                          (fun nv' nc' lim' pw' =>
                            Expr.jump Jwe.fst (Arg.var nv', Arg.var nc', Arg.var lim',
                              Arg.var pw', ())))
                  (k_done p.fst p.snd.fst p.snd.snd.fst)))
            (k_done p.fst p.snd.fst p.snd.snd.fst))
        Blocks.nil)
    fun Jpol => Expr.jump Jpol.fst (aNv0, aNc0, aLim0, Arg.imm 0, ())

theorem step13_cone_occ_pass_wp {Γ : Env}
    (hAddCl : Γ.Has "full_k6_add_clause" Kitten.Spec.step13K6AddClauseHwSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {L : K6Layout}
    {pH pAr pWvec pWstk pVals pFl pTmk pTmp pWs pK : Val i64}
    {mvC maxOrig cv curTmk nv0 nc0 layerEnd : BitVec 32}
    {aCv aCurTmk aMvC aLimV aMaxOrig aNv0 aNc0 : Arg Val i32} {lim0 : Bool}
    {aLim0 : Arg Val .bool} {qi_l : BitVec 32} {s st0 : FullState}
    {R : Mem 64 → Prop} {m0 : Mem 64} {Q : Post [i64]} {X : XPost}
    {k_done : Val i32 → Val i32 → Val .bool → Expr Val Cont [i64]}
    (hLscr : L.scrLen = c.scratch_cap) (hLmv : L.maxV = k6MaxV c.scratch_cap)
    (hpH : pH = c.hdr) (hpAr : pAr = c.pArena) (hpWvec : pWvec = c.pWvec)
    (hpWstk : pWstk = c.pWstk) (hpVals : pVals = c.pVals) (hpFl : pFl = c.pFlags)
    (hpTmk : pTmk = c.pTarjanMark) (hpTmp : pTmp = c.pTmp) (hpWs : pWs = c.pWorkStk1)
    (hpK : pK = L.kPtr c.pScratchBuf)
    (haCv : aCv.val = cv) (haCurTmk : aCurTmk.val = curTmk) (haMvC : aMvC.val = mvC)
    (haLimV : aLimV.val.toNat ≤ mvC.toNat)
    (haMaxOrig : aMaxOrig.val = maxOrig) (haNv0 : aNv0.val = nv0) (haNc0 : aNc0.val = nc0)
    (haLim0 : aLim0.val = lim0) (hmaxOrig : maxOrig.toNat ≤ L.maxOrig)
    (hlen_s : FullState.LengthsOk c s) (hw : FullWitnessInv c F0 F_cur s.core)
    (hcl0 : s.core.cur_level = 0) (hnd_s : FullArenaVarsNodup s)
    (hdw : DenseWatchesInv F_cur s.core)
    (hqi_le : qi_l.toNat < layerEnd.toNat) (hlay_le : layerEnd.toNat ≤ nv0.toNat)
    (hb0 : Step13ConeBase F_cur L mvC c s cv qi_l nv0.toNat nc0.toNat st0)
    (hm0 : (FullMem c st0 ⋆ R) m0)
    (hDone : ∀ (nvE ncE : BitVec 32) (limE : Bool) (stE : FullState) (mE : Mem 64),
      layerEnd.toNat ≤ nvE.toNat →
      Step13ConeBase F_cur L mvC c s cv qi_l nvE.toNat ncE.toNat stE →
      (FullMem c stE ⋆ R) mE →
      wp Γ Q X (k_done nvE ncE limE) mE) :
    wp Γ Q X (s13OccPassExpr pH pAr pWvec pWstk pVals pFl pTmk pTmp pWs pK
      aCv aCurTmk aMvC aLimV aMaxOrig aNv0 aNc0 aLim0 k_done) m0 := by
  subst hpH hpAr hpWvec hpWstk hpVals hpFl hpTmk hpTmp hpWs
  refine wp_loop_inv (ts := [i32, i32, .bool, i32])
    (fun (nv_p, nc_p, _lim_p, pol, ()) mp =>
      pol.toNat ≤ 2 ∧ layerEnd.toNat ≤ nv_p.toNat ∧ ∃ st_p : FullState,
        Step13ConeBase F_cur L mvC c s cv qi_l nv_p.toNat nc_p.toNat st_p ∧
        (FullMem c st_p ⋆ R) mp)
    (fun (_, _, _, pol, ()) _ => 2 - pol.toNat) ?_ ?_
  · intro _ hJpol
    c0_hsteps!
    rw [haNv0, haNc0, haLim0]
    exact hJpol (nv0, nc0, lim0, 0#32, ()) m0 ⟨Nat.zero_le _, hlay_le, st0, hb0, hm0⟩
  · rintro _ ⟨nv_p, nc_p, lim_p, pol, ⟨⟩⟩ mp ⟨hpol_le, hnv_mono, st_p, hb_p, hmp⟩ hJpol
    c0_hsplit
    · have hpol_lt : pol.toNat < 2 := ‹_›
      c0_hsplit
      · c0_hsteps!
        dsimp only [Prod.fst, Prod.snd]
        exact hDone nv_p nc_p lim_p st_p mp hnv_mono hb_p hmp
      · c0_hsplit
        · have hcv_s : cv.toNat < s.core.cur_vars := by
            have h1 := hb_p.hcone.fwd qi_l.toNat (by omega)
            have h2 := congrArg FullCoreState.cur_vars (s13ConeMask_core_eq hb_p.hag)
            rw [hb_p.hwk, h2] at h1; exact h1.1
          have hcv_lt31 : cv.toNat < 2 ^ 31 := by
            have := hlen_s.core_ok.cur_vars_le; have := c.hmaxv; unfold dimacsBound at this; omega
          let lit := (aCv.val <<< 1#32) ||| pol
          have hlit_eq : lit.toNat = 2 * cv.toNat + pol.toNat := by
            have hshl1 : (cv <<< 1#32) = cv <<< (1 : Nat) := by
              apply BitVec.eq_of_toNat_eq; simp
            simpa only [lit, haCv, hshl1] using m6_bv32_shl1_or_pol cv pol hcv_lt31 hpol_lt
          have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by omega
          obtain ⟨hwo, hwsz, hend_eq, hwo_le, _hrem_eq, hend_ws, _, _⟩ :=
            step13_cone_wvec_facts hlen_s hb_p.hlen hb_p.hag hdw hlit_lt
          have hwvec_len := hb_p.hlen.core_ok.wvec_len
          have h2l_bd : (BitVec.setWidth 64 lit <<< 1).toNat < st_p.core.wvec.length := by
            rw [hwvec_len, m6_bv64_shl1]; have := hlen_s.core_ok.cur_vars_le; omega
          have h2l1_bd : (BitVec.setWidth 64 lit <<< 1 + 1#64).toNat <
              st_p.core.wvec.length := by
            rw [hwvec_len, m6_bv64_shl1_add1]; have := hlen_s.core_ok.cur_vars_le; omega
          have hpol1 : (pol + 1#32).toNat = pol.toNat + 1 :=
            m6_bv32_add1 (by omega)
          c0_hsteps_nogrp
          let wOff := BitVec.setWidth 64
            (st_p.core.wvec[(BitVec.setWidth 64 lit <<< 1).toNat]'h2l_bd)
          let wSz := BitVec.setWidth 64
            (st_p.core.wvec[(BitVec.setWidth 64 lit <<< 1 + 1#64).toNat]'h2l1_bd)
          refine wp_join_group (ts := [i32, i32, .bool, i64])
            (fun (nvE, ncE, _limE, _, ()) mE => layerEnd.toNat ≤ nvE.toNat ∧ ∃ stE : FullState,
              Step13ConeBase F_cur L mvC c s cv qi_l nvE.toNat ncE.toNat stE ∧
              (FullMem c stE ⋆ R) mE)
            (fun _ (nvE, ncE, limE, _, ()) mE ⟨hnvE, stE, hbE, hmE⟩ => by
              c0_hsteps!
              exact hJpol (nvE, ncE, limE, pol + 1#32, ()) mE (by dsimp only; omega)
                ⟨by omega, hnvE, stE, hbE, hmE⟩)
            (fun _ hJwe => by
              refine step13_cone_occ_watch_wp hAddCl hLscr hLmv rfl rfl rfl rfl rfl rfl rfl rfl
                hpK rfl haCv haCurTmk haMvC haLimV haMaxOrig rfl rfl rfl rfl hmaxOrig hlen_s hw
                hcl0 hnd_s hdw hlit_lt hwo hend_eq hwo_le hend_ws hqi_le hnv_mono hb_p hmp ?_
              intro nvE ncE limE pwE stE mE hnvE hbE hmE
              c0_hsteps!
              exact hJwe (nvE, ncE, limE, pwE, ()) mE ⟨hnvE, stE, hbE, hmE⟩)
        · c0_hsteps!
          dsimp only [Prod.fst, Prod.snd]
          exact hDone nv_p nc_p lim_p st_p mp hnv_mono hb_p hmp
    · c0_hsteps!
      dsimp only [Prod.fst, Prod.snd]
      exact hDone nv_p nc_p lim_p st_p mp hnv_mono hb_p hmp

end LeanQbe.T.Examples.Kissat.Proof.Sweep
