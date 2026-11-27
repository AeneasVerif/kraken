module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1SweepDense
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1Spec
import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1SweepDenseProof2a
import LeanQbe.T.Examples.Kissat.FullM6SweepProofVar1b
import LeanQbe.T.Examples.Kissat.FullM6SweepProofEls
import LeanQbe.T.Examples.Kissat.FullCongLemmas1

/-!
# Kissat `D-Full` Step-13 `S1` Dense Sweeping Top-Level Proof (`full_m6_sweep_var`)

Parametric `(Γ : Env)` `Func.wp` proof helpers for Step-13 `full_m6_sweep_var_body`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S1

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full LeanQbe.T.Examples.Kissat.FullM4Sweep
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open Kraken.Bedrock2.Test
open FullArenaTactics K6MemATactics K6PtrTactics M6ElsBv FullK6DynMem
open scoped FullArenaTactics M6SweepTactics

private theorem s13_denseInvW_with_tmk {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s) {tmk' : List (BitVec 32)}
    (hlen : tmk'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with tarjan_mark := tmk' } } := by
  refine ⟨⟨hinv.1.core_ok, { hinv.1.scratch_ok with tarjan_mark_len := hlen }⟩,
    hinv.2.1, hinv.2.2.1, hinv.2.2.2.1, ?_, hinv.2.2.2.2.2⟩
  exact FullExtScratchOk.of_pres hinv.2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ hr => hr)

private theorem s13_k6StateOfScratch_incons {L : K6Layout} {F_cur : List (List Nat)}
    {s : FullState} (hL : L.scrLen = s.scratch.scratch_buf.length)
    (hLmv : L.maxV = k6MaxV s.scratch.scratch_buf.length)
    (hm6c : M6SweepConeOk F_cur s (k6StateOfScratch L s.scratch.scratch_buf).nv.toNat) :
    (k6StateOfScratch L s.scratch.scratch_buf).incons ≠ 0#32 → (cnfOfClauses F_cur).Unsat := by
  intro hinc
  obtain ⟨_, hnv_le, _, _, hscr, hge, hlt, hnv⟩ := hm6c
  have hL' : L = k6LayoutOfCap s.scratch.scratch_buf.length hge hlt :=
    K6Layout.eq_of_scrLen_maxV (by rw [hL, k6LayoutOfCap_scrLen]) (by rw [hLmv]; rfl)
  subst hL'
  have hnv_to :
      (BitVec.ofNat 32
        (k6StateOfScratch (k6LayoutOfCap s.scratch.scratch_buf.length hge hlt)
          s.scratch.scratch_buf).nv.toNat).toNat =
      (k6StateOfScratch (k6LayoutOfCap s.scratch.scratch_buf.length hge hlt)
        s.scratch.scratch_buf).nv.toNat := by
    simp
  have hscr' : K6ScratchInv (ConeModelSet F_cur s.scratch.work_stk1
      (k6StateOfScratch (k6LayoutOfCap s.scratch.scratch_buf.length hge hlt)
        s.scratch.scratch_buf).nv.toNat)
      s.scratch.scratch_buf := by
    rwa [hnv, hnv_to] at hscr
  have hki := k6ScratchInv_to_inv hL hLmv hscr'
  exact m6_coneModelSet_unsat_of_empty (hki.clauses.incons_ok hinc)

private theorem s13_k6StateOfScratch_incons_eq {L : K6Layout} {scr : List (BitVec 32)} :
    scr[L.k6Base + 6]?.getD 0#32 = (k6StateOfScratch L scr).incons := by
  simp [k6StateOfScratch, K6State.ofSlab, List.getElem?_drop]

private theorem s13_k6StateOfScratch_neq_eq {L : K6Layout} {scr : List (BitVec 32)} :
    scr[L.k6Base + 24]?.getD 0#32 = (k6StateOfScratch L scr).neq := by
  simp [k6StateOfScratch, K6State.ofSlab, List.getElem?_drop]

private theorem s13_k6_hdr_ptr {c : FullCfg} {L : K6Layout} (_hL : L.scrLen = c.scratch_cap)
    (hLmv : L.maxV = k6MaxV c.scratch_cap) {idx : Nat} (_hidx : idx < 25) :
    let mv32 := BitVec.ofNat 32 (k6MaxV c.scratch_cap)
    let k_ptr := c.pScratchBuf + (1280#32 + (mv32 <<< 1#32)).setWidth 64 * 4#64
    k_ptr + BitVec.ofNat 64 idx * 4 =
      c.pScratchBuf + BitVec.ofNat 64 (4 * (L.k6Base + idx)) := by
  have hmv_lt := L.hmaxV.2
  have h1280 : 1280#32 + (BitVec.ofNat 32 (k6MaxV c.scratch_cap) <<< 1#32) =
      BitVec.ofNat 32 (1280 + 2 * L.maxV) := by
    rw [← hLmv, show (BitVec.ofNat 32 L.maxV <<< 1#32) = (BitVec.ofNat 32 L.maxV <<< (1 : Nat))
      from rfl]
    clear hLmv _hL
    bv_omega
  have hbase64 : (BitVec.ofNat 32 (1280 + 2 * L.maxV)).setWidth 64 * 4#64 =
      BitVec.ofNat 64 (4 * L.k6Base) := by
    unfold K6Layout.k6Base; clear h1280 hLmv _hL
    bv_omega
  have hidx64 : BitVec.ofNat 64 idx * 4 = BitVec.ofNat 64 (4 * idx) := by
    clear h1280 hbase64 hmv_lt hLmv _hL
    bv_omega
  dsimp only
  rw [h1280, hbase64, hidx64, BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2; omega

private theorem s13_sweep_tmk_clear_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {s : FullState} {nv32 : BitVec 32} {nv : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {after : Expr Val Cont rs}
    (hlen : s.LengthsOk c) (hnv_eq : nv32.toNat = nv) (hnv_le : nv ≤ s.core.cur_vars)
    (hws1 : ∀ i < nv, (s.scratch.work_stk1[i]?.getD 0#32).toNat < s.core.cur_vars)
    (htmk : ∀ v < s.core.cur_vars, s.scratch.tarjan_mark[v]?.getD 0#32 ≠ 0#32 →
      ∃ i < nv, (s.scratch.work_stk1[i]?.getD 0#32).toNat = v)
    (hm : (FullMem c s ⋆ R) m)
    (hAfter : ∀ (tmk' : List (BitVec 32)) (m' : Mem 64),
      tmk'.length = 2 * c.max_vars →
      M6TmkZero { s with scratch := { s.scratch with tarjan_mark := tmk' } } →
      (FullMem c { s with scratch := { s.scratch with tarjan_mark := tmk' } } ⋆ R) m' →
      wp Γ Q X after m') :
    wp Γ Q X
      (Expr.group (sig := [[i32]]) (fun Js =>
        Blocks.cons (fun p =>
          Expr.let_ { sig := [i32, i32], code := OpCode.cmp .ult i32 .bool rfl,
                      args := (Arg.var p.fst, Arg.var nv32, ()) } fun p_1 =>
          Expr.jnz (Arg.var p_1.fst)
            (Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                         args := (Arg.var p.fst, ()) } fun p_2 =>
             Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                         args := (Arg.var p_2.fst, Arg.imm 4, ()) } fun p_3 =>
             Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                         args := (Arg.var c.pWorkStk1, Arg.var p_3.fst, ()) } fun p_4 =>
             Expr.load i32 (Arg.var p_4.fst) fun ld =>
             Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                         args := (Arg.var ld, ()) } fun p_5 =>
             Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                         args := (Arg.var p_5.fst, Arg.imm 4, ()) } fun p_6 =>
             Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                         args := (Arg.var c.pTarjanMark, Arg.var p_6.fst, ()) } fun p_7 =>
             Expr.store (t := i32) (Arg.imm 0) (Arg.var p_7.fst)
               (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                            args := (Arg.var p.fst, Arg.imm 1, ()) } fun p_8 =>
                Expr.jump Js.fst (Arg.var p_8.fst, ())))
            after)
        Blocks.nil)
        (fun Js => Expr.jump Js.fst (Arg.imm 0, ()))) m := by
  have hcv_le := hlen.core_ok.cur_vars_le
  have hws1_len := hlen.scratch_ok.work_stk1_len
  have htmk_len := hlen.scratch_ok.tarjan_mark_len
  have hmv_bd := c.hmaxv; unfold dimacsBound at hmv_bd
  refine wp_loop_inv (ts := [i32])
    (fun (i, ()) mL => i.toNat ≤ nv ∧ ∃ tmkL : List (BitVec 32),
      tmkL.length = 2 * c.max_vars ∧
      (∀ v < s.core.cur_vars, tmkL[v]?.getD 0#32 ≠ 0#32 →
        ∃ j, i.toNat ≤ j ∧ j < nv ∧ (s.scratch.work_stk1[j]?.getD 0#32).toNat = v) ∧
      (FullMem c { s with scratch := { s.scratch with tarjan_mark := tmkL } } ⋆ R) mL)
    (fun (i, ()) _ => nv - i.toNat)
    (fun Js hLoop => by
      c0_hsteps_nogrp
      exact hLoop (0#32, ()) m ⟨Nat.zero_le _, s.scratch.tarjan_mark, htmk_len,
        fun v hv hne => by
          obtain ⟨j, hj1, hj2⟩ := htmk v hv hne
          exact ⟨j, Nat.zero_le _, hj1, hj2⟩, hm⟩)
    (fun Js ⟨i, ⟨⟩⟩ mL ⟨hi_le, tmkL, htmkL_len, hdirtyL, hmL⟩ hLoop => ?_)
  c0_hsplit
  · have hi_lt : i.toNat < nv := by rw [← hnv_eq]; exact hc
    have hi_ws : i.toNat < s.scratch.work_stk1.length := by omega
    let v := s.scratch.work_stk1[i.toNat]'hi_ws
    have hv_lt : v.toNat < s.core.cur_vars := by
      have := hws1 i.toNat hi_lt
      rwa [List.getElem?_eq_getElem hi_ws, Option.getD_some] at this
    have hv_tmk : v.toNat < tmkL.length := by omega
    have hi_mod : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
    have hi_ptr : c.pWorkStk1 + i.setWidth 64 * 4#64 =
        c.pWorkStk1 + BitVec.ofNat 64 (4 * i.toNat) := by
      congr 1; apply BitVec.eq_of_toNat_eq; simp; omega
    have hld_ws : loadVal mL i32 (c.pWorkStk1 + i.setWidth 64 * 4#64) = some v := by
      rw [hi_ptr]
      exact load_full_work_stk1 (s := { s with scratch := { s.scratch with tarjan_mark := tmkL } })
        hi_ws hmL
    have hv_ptr : c.pTarjanMark + v.setWidth 64 * 4#64 =
        c.pTarjanMark + BitVec.ofNat 64 (4 * v.toNat) := by
      congr 1; apply BitVec.eq_of_toNat_eq; simp; omega
    have hst_tmk := store_full_tarjan_mark
      (s := { s with scratch := { s.scratch with tarjan_mark := tmkL } })
      0#32 hv_tmk hmL
    rw [← hv_ptr] at hst_tmk
    c0_hsteps_nogrp
    exact hLoop (i + 1#32, ()) _ (by dsimp only; omega)
      ⟨by omega, tmkL.set v.toNat 0#32, by simp [htmkL_len], fun u hu hne => by
        by_cases huv : u = v.toNat
        · exfalso; apply hne; subst huv
          rw [List.getElem?_set_self hv_tmk, Option.getD_some]
        · have hu_old : tmkL[u]?.getD 0#32 ≠ 0#32 := by
            rwa [List.getElem?_set_ne (Ne.symm huv)] at hne
          obtain ⟨j, hj1, hj2, hjeq⟩ := hdirtyL u hu hu_old
          have hj_ne : j ≠ i.toNat := by
            rintro rfl; apply huv; rw [← hjeq, List.getElem?_eq_getElem hi_ws, Option.getD_some]
          exact ⟨j, by omega, hj2, hjeq⟩,
       by assumption⟩
  · have hi_ge : nv ≤ i.toNat := by
      have hnot : ¬ (i.toNat < nv32.toNat) := hc
      omega
    have hi_eq : i.toNat = nv := by omega
    c0_hsteps_nogrp
    refine hAfter tmkL mL htmkL_len (fun u hu => ?_) hmL
    exact Classical.byContradiction fun hne => by
      obtain ⟨j, hj1, hj2, _⟩ := hdirtyL u hu hne
      omega

private theorem s13_sweep_var_post_classes_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    (hEls : ∀ a m Q X, step13DenseElsSpec a m Q X →
      Γ "full_m6_dense_els" [i64, i32] [.bool] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s s4 : FullState}
    {nv32 : BitVec 32} {cr64 : BitVec 64} {nv : Nat} {R : Mem 64 → Prop} {m4 : Mem 64}
    (hinv4 : FullDenseInvW c F0 F_cur s4) (hcv4 : s4.core.cur_vars = s.core.cur_vars)
    (hfu4 : s4.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hrepr4 : FullCongReprInv F_cur (2 * s4.core.cur_vars) s4.core.repr)
    (htrh4 : s4.scratch.tarjan_reach = s.scratch.tarjan_reach)
    (hgu4 : ∀ i < 64, i ≠ 33 → s4.scratch.glue_used[i]? = s.scratch.glue_used[i]?)
    (hhwm4 : ∃ L : K6Layout, L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
      K6HwmClean L (s4.scratch.glue_used[33]?.getD 0#32)
        (k6StateOfScratch L s4.scratch.scratch_buf))
    (hcr_vals : cr64 = 1#64 ∨ cr64 = 20#64) (hcr_unsat : cr64 = 20#64 → F0.Unsat)
    (heq4 : cr64 = 1#64 → ∃ L : K6Layout, L.scrLen = c.scratch_cap ∧
      L.maxV = k6MaxV c.scratch_cap ∧
      M6EqBufOk F_cur s4 (k6StateOfScratch L s4.scratch.scratch_buf).neq.toNat)
    (hnv_eq : nv32.toNat = nv) (hnv_le : nv ≤ s4.core.cur_vars)
    (hws1_4 : ∀ i < nv, (s4.scratch.work_stk1[i]?.getD 0#32).toNat < s4.core.cur_vars)
    (htmk_4 : ∀ v < s4.core.cur_vars, s4.scratch.tarjan_mark[v]?.getD 0#32 ≠ 0#32 →
      ∃ i < nv, (s4.scratch.work_stk1[i]?.getD 0#32).toNat = v)
    (hm4 : (FullMem c s4 ⋆ R) m4)
    (hQ : ∀ r s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → M6TmkZero s' →
      FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      (∀ i < 64, i ≠ 33 → s'.scratch.glue_used[i]? = s.scratch.glue_used[i]?) →
      (∃ L : K6Layout, L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
        K6HwmClean L (s'.scratch.glue_used[33]?.getD 0#32)
          (k6StateOfScratch L s'.scratch.scratch_buf)) →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    let mv32 := BitVec.ofNat 32 (k6MaxV c.scratch_cap)
    let k_ptr := c.pScratchBuf + (1280#32 + (mv32 <<< 1#32)).setWidth 64 * 4#64
    wp Γ Q X
      (Expr.group (sig := [[i32]]) (fun Js =>
        Blocks.cons (fun p =>
          Expr.let_ { sig := [i32, i32], code := OpCode.cmp .ult i32 .bool rfl,
                      args := (Arg.var p.fst, Arg.var nv32, ()) } fun p_1 =>
          Expr.jnz (Arg.var p_1.fst)
            (Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                         args := (Arg.var p.fst, ()) } fun p_2 =>
             Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                         args := (Arg.var p_2.fst, Arg.imm 4, ()) } fun p_3 =>
             Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                         args := (Arg.var c.pWorkStk1, Arg.var p_3.fst, ()) } fun p_4 =>
             Expr.load i32 (Arg.var p_4.fst) fun ld =>
             Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                         args := (Arg.var ld, ()) } fun p_5 =>
             Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                         args := (Arg.var p_5.fst, Arg.imm 4, ()) } fun p_6 =>
             Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                         args := (Arg.var c.pTarjanMark, Arg.var p_6.fst, ()) } fun p_7 =>
             Expr.store (t := i32) (Arg.imm 0) (Arg.var p_7.fst)
               (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                            args := (Arg.var p.fst, Arg.imm 1, ()) } fun p_8 =>
                Expr.jump Js.fst (Arg.var p_8.fst, ())))
            (Expr.let_ { sig := [i64, i64], code := OpCode.cmp .eq i64 .bool rfl,
                         args := (Arg.var cr64, Arg.imm 20, ()) } fun p_9 =>
             Expr.jnz (Arg.var p_9.fst) (Expr.ret (Arg.imm 20, ()))
               (Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                            args := (Arg.var c.hdr, Arg.imm 1024, ()) } fun p_10 =>
                Expr.load i64 (Arg.var p_10.fst) fun ld_inc =>
                Expr.let_ { sig := [i64, i64], code := OpCode.cmp .ne i64 .bool rfl,
                             args := (Arg.var ld_inc, Arg.imm 0, ()) } fun p_11 =>
                Expr.jnz (Arg.var p_11.fst) (Expr.ret (Arg.imm 20, ()))
                  (Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                               args := (Arg.imm 24, ()) } fun p_12 =>
                   Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                               args := (Arg.var p_12.fst, Arg.imm 4, ()) } fun p_13 =>
                   Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                               args := (Arg.var k_ptr, Arg.var p_13.fst, ()) } fun p_14 =>
                   Expr.load i32 (Arg.var p_14.fst) fun neq =>
                   Expr.group (sig := [[]]) (fun _Js1 =>
                     Blocks.cons (fun _ =>
                       Expr.group (sig := [[i64]]) (fun _Js2 =>
                         Blocks.cons (fun pr => Expr.ret (Arg.var pr.fst, ())) Blocks.nil)
                         (fun Js2 =>
                           Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                        args := (Arg.var c.hdr, Arg.imm 1024, ()) } fun pa =>
                           Expr.load i64 (Arg.var pa.fst) fun ldi =>
                           Expr.let_ { sig := [i64, i64], code := OpCode.cmp .ne i64 .bool rfl,
                                        args := (Arg.var ldi, Arg.imm 0, ()) } fun pb =>
                           Expr.jnz (Arg.var pb.fst)
                             (Expr.jump Js2.fst (Arg.imm 20, ()))
                             (Expr.jump Js2.fst (Arg.imm 1, ()))))
                       Blocks.nil)
                     (fun Js1 =>
                       Expr.let_ { sig := [i32, i32], code := OpCode.cmp .ugt i32 .bool rfl,
                                    args := (Arg.var neq, Arg.imm 0, ()) } fun p_15 =>
                       Expr.jnz (Arg.var p_15.fst)
                         (Expr.call (as := [i64, i32]) (bs := [.bool]) "full_m6_dense_els"
                           (Arg.var c.hdr, Arg.var neq, ()) fun pok =>
                           Expr.jnz (Arg.var pok.fst)
                             (Expr.jump Js1.fst ())
                             (Expr.ret (Arg.imm 20, ())))
                         (Expr.jump Js1.fst ()))))))
        Blocks.nil)
        (fun Js => Expr.jump Js.fst (Arg.imm 0, ()))) m4 := by
  intro mv32 k_ptr
  refine s13_sweep_tmk_clear_wp hinv4.1 hnv_eq hnv_le hws1_4 htmk_4 hm4 ?_
  intro tmk4' m4' htmk4'_len htmk0_4' hm4'
  let s4' : FullState := { s4 with scratch := { s4.scratch with tarjan_mark := tmk4' } }
  have hinv4' := s13_denseInvW_with_tmk hinv4 htmk4'_len
  c0_hsplit
  · exact hQ 20#64 s4' m4' hinv4' hcv4 hfu4 htmk0_4' hrepr4 htrh4 hgu4 hhwm4
      (Or.inr rfl) (fun _ => hcr_unsat (by assumption)) hm4'
  · have hcr1 : cr64 = 1#64 := by
      have hne : cr64 ≠ 20#64 := by assumption
      rcases hcr_vals with h | h
      · exact h
      · exact absurd h hne
    c0_hsplit
    · have hunsat : F0.Unsat := by
        have hcun := hinv4'.2.1.inconsistent_sound (by assumption)
        exact hinv4'.2.1.ext_sound.2 hcun
      exact hQ 20#64 s4' m4' hinv4' hcv4 hfu4 htmk0_4' hrepr4 htrh4 hgu4 hhwm4
        (Or.inr rfl) (fun _ => hunsat) hm4'
    · obtain ⟨L4, hL4_len, hL4_mv, hhwm4_L⟩ := hhwm4
      obtain ⟨L4e, hL4e_len, hL4e_mv, heqb4⟩ := heq4 hcr1
      have hL4_eq : L4 = L4e := K6Layout.eq_of_scrLen_maxV (hL4_len.trans hL4e_len.symm)
        (hL4_mv.trans hL4e_mv.symm)
      rw [← hL4_eq] at heqb4
      have hptr_neq := s13_k6_hdr_ptr hL4_len hL4_mv (idx := 24) (by decide)
      have h24_lt : L4.k6Base + 24 < s4'.scratch.scratch_buf.length := by
        have := L4.hmaxV; have := L4.hacap
        rw [hinv4'.1.scratch_ok.scratch_buf_len, ← hL4_len]
        unfold K6Layout.scrLen K6Layout.k6Base; omega
      let neq := s4'.scratch.scratch_buf[L4.k6Base + 24]'h24_lt
      have hld_neq : loadVal m4' i32 (k_ptr + BitVec.ofNat 64 24 * 4) = some neq := by
        dsimp only [neq]; rw [hptr_neq]; exact load_full_scratch_buf h24_lt hm4'
      have hneq_eq : neq = (k6StateOfScratch L4 s4'.scratch.scratch_buf).neq := by
        have := s13_k6StateOfScratch_neq_eq (L := L4) (scr := s4'.scratch.scratch_buf)
        rwa [List.getElem?_eq_getElem h24_lt, Option.getD_some] at this
      have heqb4' : M6EqBufOk F_cur s4' neq.toNat := by
        rw [hneq_eq]; exact heqb4
      c0_hstraight
      refine head_wp_load ?_ hld_neq ?_
      · rfl
      have hc_inc : s4.core.inconsistent = 0#64 := hc
      c0_hstraight
      refine wp_join_group (ts := [])
        (fun () mE => ∃ sE : FullState,
          FullDenseInvW c F0 F_cur sE ∧ sE.core.cur_vars = s.core.cur_vars ∧
          sE.core.fuel.toNat ≤ s.core.fuel.toNat ∧ M6TmkZero sE ∧
          FullCongReprInv F_cur (2 * sE.core.cur_vars) sE.core.repr ∧
          sE.scratch.tarjan_reach = s.scratch.tarjan_reach ∧
          (∀ i < 64, i ≠ 33 → sE.scratch.glue_used[i]? = s.scratch.glue_used[i]?) ∧
          (∃ L : K6Layout, L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
            K6HwmClean L (sE.scratch.glue_used[33]?.getD 0#32)
              (k6StateOfScratch L sE.scratch.scratch_buf)) ∧
          (sE.core.inconsistent ≠ 0#64 → F0.Unsat) ∧ (FullMem c sE ⋆ R) mE)
        (fun _ ⟨⟩ mE ⟨sE, hinvE, hcvE, hfuE, htmkE, hreprE, htrhE, hguE, hhwmE, hincE, hmE⟩ => by
          c0_hstraight
          refine wp_join_group (ts := [i64])
            (fun (r, ()) mF => (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → F0.Unsat) ∧ mF = mE)
            (fun _ ⟨r, ⟨⟩⟩ mF ⟨hr_v, hr_un, hmF⟩ => by
              cases hmF; c0_hstraight
              exact hQ r sE _ hinvE hcvE hfuE htmkE hreprE htrhE hguE hhwmE hr_v hr_un
                (by assumption))
            (fun Js2 hJs2 => by
              c0_hsplit
              · exact hJs2 (20#64, ()) mE ⟨Or.inr rfl, fun _ => hincE hc, rfl⟩
              · exact hJs2 (1#64, ()) mE ⟨Or.inl rfl, (fun h => by cases h), rfl⟩))
        (fun Js1 hJs1 => by
          c0_hsplit
          · c0_hstraight; m6_call hEls
            refine ⟨c, F0, F_cur, s4', R, rfl, hinv4', heqb4', hrepr4, hm4', ?_⟩
            intro ok s5 m5 hinv5 hcv5 hfu5 hrepr5 htmk5 htrh5 hscr5 _hws2_5 hgu5 hok_f hm5
            c0_hsplit
            · c0_hstraight
              refine hJs1 () m5 ⟨s5, hinv5, hcv5.trans hcv4, hfu5 ▸ hfu4,
                (by simpa [M6TmkZero, htmk5, hcv5] using htmk0_4'), hrepr5,
                htrh5.trans htrh4,
                fun i hi1 hi2 => by rw [hgu5]; exact hgu4 i hi1 hi2,
                ⟨L4, hL4_len, hL4_mv, by rw [hgu5, hscr5]; exact hhwm4_L⟩,
                fun hne => hinv5.2.1.ext_sound.2 (hinv5.2.1.inconsistent_sound hne), hm5⟩
            · have hokf : ok = false := by
                cases ok <;> simp_all
              obtain ⟨huns5, _⟩ := hok_f hokf
              exact hQ 20#64 s5 m5 hinv5 (hcv5.trans hcv4) (hfu5 ▸ hfu4)
                (by simpa [M6TmkZero, htmk5, hcv5] using htmk0_4') hrepr5
                (htrh5.trans htrh4) (fun i hi1 hi2 => by rw [hgu5]; exact hgu4 i hi1 hi2)
                ⟨L4, hL4_len, hL4_mv, by rw [hgu5, hscr5]; exact hhwm4_L⟩
                (Or.inr rfl) (fun _ => huns5) hm5
          · c0_hstraight
            exact hJs1 () m4' ⟨s4', hinv4', hcv4, hfu4, htmk0_4', hrepr4, htrh4, hgu4,
              ⟨L4, hL4_len, hL4_mv, hhwm4_L⟩,
              fun hne => absurd hc_inc hne, hm4'⟩)

private theorem s13_sweep_var_post_units_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    (hClasses : ∀ a m Q X, step13SweepClassesSpec a m Q X →
      Γ "full_m6_sweep_classes" [i64, i32, i32, i64] [i64] a m Q X)
    (hEls : ∀ a m Q X, step13DenseElsSpec a m Q X →
      Γ "full_m6_dense_els" [i64, i32] [.bool] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s s3 : FullState}
    {tick_lim : BitVec 64} {nv32 : BitVec 32} {ur : BitVec 64} {nv : Nat}
    {R : Mem 64 → Prop} {m3 : Mem 64}
    (hinv3 : FullDenseInvW c F0 F_cur s3) (hcv3 : s3.core.cur_vars = s.core.cur_vars)
    (hfu3 : s3.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hrepr3 : FullCongReprInv F_cur (2 * s3.core.cur_vars) s3.core.repr)
    (hm6c3 : M6SweepConeOk F_cur s3 nv) (htrh3 : s3.scratch.tarjan_reach = s.scratch.tarjan_reach)
    (hgu3 : ∀ i < 64, i ≠ 33 → s3.scratch.glue_used[i]? = s.scratch.glue_used[i]?)
    (hhwm3 : ∃ L : K6Layout, L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
      K6HwmClean L (s3.scratch.glue_used[33]?.getD 0#32)
        (k6StateOfScratch L s3.scratch.scratch_buf))
    (htmk3 : ∀ v < s3.core.cur_vars, s3.scratch.tarjan_mark[v]?.getD 0#32 ≠ 0#32 →
      ∃ i < nv, (s3.scratch.work_stk1[i]?.getD 0#32).toNat = v)
    (hnv_eq : nv32.toNat = nv)
    (hur_uns : ur = 18446744073709551615#64 → F0.Unsat)
    (hur_le : ur ≠ 18446744073709551615#64 → ur.toNat ≤ 64)
    (hm3 : (FullMem c s3 ⋆ R) m3)
    (hQ : ∀ r s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → M6TmkZero s' →
      FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      (∀ i < 64, i ≠ 33 → s'.scratch.glue_used[i]? = s.scratch.glue_used[i]?) →
      (∃ L : K6Layout, L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
        K6HwmClean L (s'.scratch.glue_used[33]?.getD 0#32)
          (k6StateOfScratch L s'.scratch.scratch_buf)) →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    let mv32 := BitVec.ofNat 32 (k6MaxV c.scratch_cap)
    let k_ptr := c.pScratchBuf + (1280#32 + (mv32 <<< 1#32)).setWidth 64 * 4#64
    wp Γ Q X
      (Expr.let_ { sig := [i64, i64], code := OpCode.cmp .eq i64 .bool rfl,
                   args := (Arg.var ur, Arg.imm 18446744073709551615, ()) } fun p_34 =>
       Expr.jnz (Arg.var p_34.fst)
         (Expr.group (sig := [[i32]]) (fun Js =>
           Blocks.cons (fun p =>
             Expr.let_ { sig := [i32, i32], code := OpCode.cmp .ult i32 .bool rfl,
                         args := (Arg.var p.fst, Arg.var nv32, ()) } fun p_35 =>
             Expr.jnz (Arg.var p_35.fst)
               (Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                            args := (Arg.var p.fst, ()) } fun p_36 =>
                Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                            args := (Arg.var p_36.fst, Arg.imm 4, ()) } fun p_37 =>
                Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                            args := (Arg.var c.pWorkStk1, Arg.var p_37.fst, ()) } fun p_38 =>
                Expr.load i32 (Arg.var p_38.fst) fun ld =>
                Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                            args := (Arg.var ld, ()) } fun p_39 =>
                Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                            args := (Arg.var p_39.fst, Arg.imm 4, ()) } fun p_40 =>
                Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                            args := (Arg.var c.pTarjanMark, Arg.var p_40.fst, ()) } fun p_41 =>
                Expr.store (t := i32) (Arg.imm 0) (Arg.var p_41.fst)
                  (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                               args := (Arg.var p.fst, Arg.imm 1, ()) } fun p_42 =>
                   Expr.jump Js.fst (Arg.var p_42.fst, ())))
               (Expr.ret (Arg.imm 20, ())))
           Blocks.nil)
           (fun Js => Expr.jump Js.fst (Arg.imm 0, ())))
         (Expr.let_ { sig := [i64], code := OpCode.trunc 64 32,
                      args := (Arg.var ur, ()) } fun p_35 =>
          Expr.call (as := [i64, i32, i32, i64]) (bs := [i64])
            "full_m6_sweep_classes"
            (Arg.var c.hdr, Arg.var nv32, Arg.var p_35.fst, Arg.var tick_lim, ()) fun p_36 =>
          Expr.group (sig := [[i32]]) (fun Js =>
            Blocks.cons (fun p_37 =>
              Expr.let_ { sig := [i32, i32], code := OpCode.cmp .ult i32 .bool rfl,
                          args := (Arg.var p_37.fst, Arg.var nv32, ()) } fun p_38 =>
              Expr.jnz (Arg.var p_38.fst)
                (Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                             args := (Arg.var p_37.fst, ()) } fun p =>
                 Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                             args := (Arg.var p.fst, Arg.imm 4, ()) } fun p =>
                 Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                             args := (Arg.var c.pWorkStk1, Arg.var p.fst, ()) } fun p =>
                 Expr.load i32 (Arg.var p.fst) fun ld =>
                 Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                             args := (Arg.var ld, ()) } fun p =>
                 Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                             args := (Arg.var p.fst, Arg.imm 4, ()) } fun p =>
                 Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                             args := (Arg.var c.pTarjanMark, Arg.var p.fst, ()) } fun p =>
                 Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
                   (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                args := (Arg.var p_37.fst, Arg.imm 1, ()) } fun p =>
                    Expr.jump Js.fst (Arg.var p.fst, ())))
                (Expr.let_ { sig := [i64, i64], code := OpCode.cmp .eq i64 .bool rfl,
                             args := (Arg.var p_36.fst, Arg.imm 20, ()) } fun p_39 =>
                 Expr.jnz (Arg.var p_39.fst) (Expr.ret (Arg.imm 20, ()))
                   (Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                args := (Arg.var c.hdr, Arg.imm 1024, ()) } fun p_40 =>
                    Expr.load i64 (Arg.var p_40.fst) fun ld =>
                    Expr.let_ { sig := [i64, i64], code := OpCode.cmp .ne i64 .bool rfl,
                                args := (Arg.var ld, Arg.imm 0, ()) } fun p_41 =>
                    Expr.jnz (Arg.var p_41.fst) (Expr.ret (Arg.imm 20, ()))
                      (Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                   args := (Arg.imm 24, ()) } fun p_42 =>
                       Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                   args := (Arg.var p_42.fst, Arg.imm 4, ()) } fun p_43 =>
                       Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                   args := (Arg.var k_ptr, Arg.var p_43.fst, ()) } fun p_44 =>
                       Expr.load i32 (Arg.var p_44.fst) fun ld =>
                       Expr.group (sig := [[]]) (fun _Js =>
                         Blocks.cons (fun _ =>
                           Expr.group (sig := [[i64]]) (fun _Js =>
                             Blocks.cons (fun p => Expr.ret (Arg.var p.fst, ())) Blocks.nil)
                             (fun Js =>
                               Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                            args := (Arg.var c.hdr, Arg.imm 1024, ()) } fun p =>
                               Expr.load i64 (Arg.var p.fst) fun ld =>
                               Expr.let_ { sig := [i64, i64], code := OpCode.cmp .ne i64 .bool rfl,
                                            args := (Arg.var ld, Arg.imm 0, ()) } fun p =>
                               Expr.jnz (Arg.var p.fst)
                                 (Expr.jump Js.fst (Arg.imm 20, ()))
                                 (Expr.jump Js.fst (Arg.imm 1, ())))) Blocks.nil)
                         (fun Js =>
                           Expr.let_ { sig := [i32, i32], code := OpCode.cmp .ugt i32 .bool rfl,
                                        args := (Arg.var ld, Arg.imm 0, ()) } fun p_45 =>
                           Expr.jnz (Arg.var p_45.fst)
                             (Expr.call (as := [i64, i32]) (bs := [.bool]) "full_m6_dense_els"
                               (Arg.var c.hdr, Arg.var ld, ()) fun p =>
                              Expr.jnz (Arg.var p.fst)
                                (Expr.jump Js.fst ()) (Expr.ret (Arg.imm 20, ())))
                             (Expr.jump Js.fst ()))))))
            Blocks.nil)
            (fun Js => Expr.jump Js.fst (Arg.imm 0, ())))) m3 := by
  intro mv32 k_ptr
  have hm6c3' : M6SweepConeOk F_cur s3 nv := hm6c3
  c0_hsplit
  · refine s13_sweep_tmk_clear_wp hinv3.1 hnv_eq hm6c3'.2.2.1 hm6c3'.2.2.2.1 htmk3 hm3 ?_
    intro tmk3' m3' htmk3'_len htmk0_3' hm3'
    let s3' : FullState := { s3 with scratch := { s3.scratch with tarjan_mark := tmk3' } }
    have hinv3' := s13_denseInvW_with_tmk hinv3 htmk3'_len
    c0_hstraight
    exact hQ 20#64 s3' m3' hinv3' hcv3 hfu3 htmk0_3' hrepr3 htrh3 hgu3 hhwm3
      (Or.inr rfl) (fun _ => hur_uns hc) hm3'
  · have hur_le64 : ur.toNat ≤ 64 := hur_le hc
    have hur32_le : (ur.truncate 32).toNat ≤ 64 := by
      change (BitVec.setWidth 32 ur).toNat ≤ 64
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact hur_le64
    c0_hstraight; m6_call hClasses
    refine ⟨c, F0, F_cur, s3, R, rfl, hinv3, hnv_eq ▸ hm6c3, hur32_le, hhwm3, hm3, ?_⟩
    intro cr s4 m4 hinv4 hcv4 hfu4 hrepr4_eq hws1_4 htmk4_eq htrh4 hgu4_eq
      hhwm4 hcr_vals hcr_uns heq4 hm4
    have hcv4' : s4.core.cur_vars = s.core.cur_vars := hcv4.trans hcv3
    have hfu4' : s4.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfu4 hfu3
    have hrepr4 : FullCongReprInv F_cur (2 * s4.core.cur_vars) s4.core.repr := by
      rw [hcv4, hrepr4_eq]; exact hrepr3
    have htrh4' : s4.scratch.tarjan_reach = s.scratch.tarjan_reach := htrh4.trans htrh3
    have hgu4' : ∀ i < 64, i ≠ 33 →
        s4.scratch.glue_used[i]? = s.scratch.glue_used[i]? := fun i hi1 hi2 => by
      rw [hgu4_eq]; exact hgu3 i hi1 hi2
    have htmk4 : ∀ v < s4.core.cur_vars, s4.scratch.tarjan_mark[v]?.getD 0#32 ≠ 0#32 →
        ∃ i < nv, (s4.scratch.work_stk1[i]?.getD 0#32).toNat = v := by
      intro v hv hne
      rw [htmk4_eq] at hne
      obtain ⟨j, hj1, hj2⟩ := htmk3 v (hcv4 ▸ hv) hne
      rw [hws1_4]; exact ⟨j, hj1, hj2⟩
    exact s13_sweep_var_post_classes_wp hEls hinv4 hcv4' hfu4' hrepr4 htrh4'
      hgu4' hhwm4 hcr_vals hcr_uns heq4 hnv_eq
      (hcv4 ▸ hm6c3'.2.2.1)
      (fun i hi => by rw [hws1_4, hcv4]; exact hm6c3'.2.2.2.1 i hi)
      htmk4 hm4 hQ

private theorem s13_sweep_var_post_cone_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    (hSim : ∀ a m Q X, step13SweepSimSpec a m Q X →
      Γ "full_m6_sweep_sim" [i64, i32, i64] [i32] a m Q X)
    (hUnits : ∀ a m Q X, step13SweepUnitsSpec a m Q X →
      Γ "full_m6_sweep_units" [i64, i32, i32, i64] [i64] a m Q X)
    (hClasses : ∀ a m Q X, step13SweepClassesSpec a m Q X →
      Γ "full_m6_sweep_classes" [i64, i32, i32, i64] [i64] a m Q X)
    (hEls : ∀ a m Q X, step13DenseElsSpec a m Q X →
      Γ "full_m6_dense_els" [i64, i32] [.bool] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s s1 : FullState}
    {tick_lim : BitVec 64} {nv32 nc32 : BitVec 32} {nv : Nat}
    {R : Mem 64 → Prop} {m1 : Mem 64}
    (hinv1 : FullDenseInvW c F0 F_cur s1) (hcv1 : s1.core.cur_vars = s.core.cur_vars)
    (hfu1 : s1.core.fuel = s.core.fuel)
    (hrepr1 : FullCongReprInv F_cur (2 * s1.core.cur_vars) s1.core.repr)
    (hm6c1 : M6SweepConeOk F_cur s1 nv) (htrh1 : s1.scratch.tarjan_reach = s.scratch.tarjan_reach)
    (hgu1 : ∀ i < 64, i ≠ 33 → s1.scratch.glue_used[i]? = s.scratch.glue_used[i]?)
    (hhwm1 : ∃ L : K6Layout, L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
      K6HwmClean L (s1.scratch.glue_used[33]?.getD 0#32)
        (k6StateOfScratch L s1.scratch.scratch_buf))
    (htmk1 : ∀ v < s1.core.cur_vars, s1.scratch.tarjan_mark[v]?.getD 0#32 ≠ 0#32 →
      ∃ i < nv, (s1.scratch.work_stk1[i]?.getD 0#32).toNat = v)
    (hnv_eq : nv32.toNat = nv) (hm1 : (FullMem c s1 ⋆ R) m1)
    (hQ : ∀ r s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → M6TmkZero s' →
      FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      (∀ i < 64, i ≠ 33 → s'.scratch.glue_used[i]? = s.scratch.glue_used[i]?) →
      (∃ L : K6Layout, L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
        K6HwmClean L (s'.scratch.glue_used[33]?.getD 0#32)
          (k6StateOfScratch L s'.scratch.scratch_buf)) →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    let mv32 := BitVec.ofNat 32 (k6MaxV c.scratch_cap)
    let k_ptr := c.pScratchBuf + (1280#32 + (mv32 <<< 1#32)).setWidth 64 * 4#64
    wp Γ Q X
      (Expr.load i32 (Arg.var (k_ptr + BitVec.ofNat 64 6 * 4)) fun ld_3 =>
       Expr.let_ { sig := [i32, i32], code := OpCode.cmp .ne i32 .bool rfl,
                   args := (Arg.var ld_3, Arg.imm 0, ()) } fun p_27 =>
       Expr.jnz (Arg.var p_27.fst)
         (Expr.group (sig := [[i32]]) (fun Js =>
           Blocks.cons (fun p_28 =>
             Expr.let_ { sig := [i32, i32], code := OpCode.cmp .ult i32 .bool rfl,
                         args := (Arg.var p_28.fst, Arg.var nv32, ()) } fun p_29 =>
             Expr.jnz (Arg.var p_29.fst)
               (Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                            args := (Arg.var p_28.fst, ()) } fun p =>
                Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                            args := (Arg.var p.fst, Arg.imm 4, ()) } fun p =>
                Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                            args := (Arg.var c.pWorkStk1, Arg.var p.fst, ()) } fun p =>
                Expr.load i32 (Arg.var p.fst) fun ld =>
                Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                            args := (Arg.var ld, ()) } fun p =>
                Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                            args := (Arg.var p.fst, Arg.imm 4, ()) } fun p =>
                Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                            args := (Arg.var c.pTarjanMark, Arg.var p.fst, ()) } fun p =>
                Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
                  (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                               args := (Arg.var p_28.fst, Arg.imm 1, ()) } fun p =>
                   Expr.jump Js.fst (Arg.var p.fst, ())))
               (Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                            args := (Arg.var c.hdr, Arg.imm 1024, ()) } fun p =>
                Expr.store (t := i64) (Arg.imm 1) (Arg.var p.fst)
                  (Expr.ret (Arg.imm 20, ()))))
           Blocks.nil)
           (fun Js => Expr.jump Js.fst (Arg.imm 0, ())))
         (Expr.group (sig := [[]]) (fun _Js =>
           Blocks.cons (fun _ =>
             Expr.group (sig := [[i32]]) (fun Js =>
               Blocks.cons (fun p =>
                 Expr.let_ { sig := [i32, i32], code := OpCode.cmp .ult i32 .bool rfl,
                             args := (Arg.var p.fst, Arg.var nv32, ()) } fun p_28 =>
                 Expr.jnz (Arg.var p_28.fst)
                   (Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                args := (Arg.var p.fst, ()) } fun p_29 =>
                    Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                args := (Arg.var p_29.fst, Arg.imm 4, ()) } fun p_30 =>
                    Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                args := (Arg.var c.pWorkStk1, Arg.var p_30.fst, ()) } fun p_31 =>
                    Expr.load i32 (Arg.var p_31.fst) fun ld =>
                    Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                args := (Arg.var ld, ()) } fun p_32 =>
                    Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                args := (Arg.var p_32.fst, Arg.imm 4, ()) } fun p_33 =>
                    Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                args := (Arg.var c.pTarjanMark, Arg.var p_33.fst, ()) } fun p_34 =>
                    Expr.store (t := i32) (Arg.imm 0) (Arg.var p_34.fst)
                      (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                   args := (Arg.var p.fst, Arg.imm 1, ()) } fun p =>
                       Expr.jump Js.fst (Arg.var p.fst, ())))
                   (Expr.ret (Arg.imm 1, ())))
               Blocks.nil)
               (fun Js => Expr.jump Js.fst (Arg.imm 0, ())))
           Blocks.nil)
           (fun Js =>
             Expr.let_ { sig := [i32, i32], code := OpCode.cmp .ult i32 .bool rfl,
                         args := (Arg.var nv32, Arg.imm 2, ()) } fun p_28 =>
             Expr.jnz (Arg.var p_28.fst) (Expr.jump Js.fst ())
               (Expr.let_ { sig := [i32, i32], code := OpCode.cmp .eq i32 .bool rfl,
                            args := (Arg.var nc32, Arg.imm 0, ()) } fun p_29 =>
                Expr.jnz (Arg.var p_29.fst) (Expr.jump Js.fst ())
                  (Expr.call (as := [i64, i32, i64]) (bs := [i32]) "full_m6_sweep_sim"
                    (Arg.var c.hdr, Arg.var nv32, Arg.var tick_lim, ()) fun p_30 =>
                   Expr.let_ { sig := [i32, i32], code := OpCode.cmp .eq i32 .bool rfl,
                               args := (Arg.var p_30.fst, Arg.imm 4294967295, ()) } fun p_31 =>
                   Expr.jnz (Arg.var p_31.fst)
                     (Expr.group (sig := [[i32]]) (fun Js =>
                       Blocks.cons (fun p =>
                         Expr.let_ { sig := [i32, i32], code := OpCode.cmp .ult i32 .bool rfl,
                                     args := (Arg.var p.fst, Arg.var nv32, ()) } fun p_32 =>
                         Expr.jnz (Arg.var p_32.fst)
                           (Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                        args := (Arg.var p.fst, ()) } fun p_33 =>
                            Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                        args := (Arg.var p_33.fst, Arg.imm 4, ()) } fun p_34 =>
                            Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                        args := (Arg.var c.pWorkStk1,
                                          Arg.var p_34.fst, ()) } fun p_35 =>
                            Expr.load i32 (Arg.var p_35.fst) fun ld =>
                            Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                        args := (Arg.var ld, ()) } fun p_36 =>
                            Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                        args := (Arg.var p_36.fst, Arg.imm 4, ()) } fun p_37 =>
                            Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                        args := (Arg.var c.pTarjanMark,
                                          Arg.var p_37.fst, ()) } fun p_38 =>
                            Expr.store (t := i32) (Arg.imm 0) (Arg.var p_38.fst)
                              (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                           args := (Arg.var p.fst, Arg.imm 1, ()) } fun p =>
                               Expr.jump Js.fst (Arg.var p.fst, ())))
                           (Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                        args := (Arg.var c.hdr, Arg.imm 1024, ()) } fun p =>
                            Expr.store (t := i64) (Arg.imm 1) (Arg.var p.fst)
                              (Expr.ret (Arg.imm 20, ()))))
                       Blocks.nil)
                       (fun Js => Expr.jump Js.fst (Arg.imm 0, ())))
                     (Expr.let_ { sig := [i32, i32], code := OpCode.cmp .eq i32 .bool rfl,
                                  args := (Arg.var p_30.fst, Arg.imm 0, ()) } fun p_32 =>
                      Expr.jnz (Arg.var p_32.fst)
                        (Expr.group (sig := [[i32]]) (fun Js =>
                          Blocks.cons (fun p =>
                            Expr.let_ { sig := [i32, i32], code := OpCode.cmp .ult i32 .bool rfl,
                                        args := (Arg.var p.fst, Arg.var nv32, ()) } fun p_33 =>
                            Expr.jnz (Arg.var p_33.fst)
                              (Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                           args := (Arg.var p.fst, ()) } fun p_34 =>
                               Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                           args := (Arg.var p_34.fst, Arg.imm 4, ()) } fun p_35 =>
                               Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                           args := (Arg.var c.pWorkStk1,
                                             Arg.var p_35.fst, ()) } fun p_36 =>
                               Expr.load i32 (Arg.var p_36.fst) fun ld =>
                               Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                           args := (Arg.var ld, ()) } fun p_37 =>
                               Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                           args := (Arg.var p_37.fst, Arg.imm 4, ()) } fun p_38 =>
                               Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                           args := (Arg.var c.pTarjanMark,
                                             Arg.var p_38.fst, ()) } fun p_39 =>
                               Expr.store (t := i32) (Arg.imm 0) (Arg.var p_39.fst)
                                 (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                              args := (Arg.var p.fst, Arg.imm 1, ()) } fun p =>
                                  Expr.jump Js.fst (Arg.var p.fst, ())))
                              (Expr.ret (Arg.imm 1, ())))
                          Blocks.nil)
                          (fun Js => Expr.jump Js.fst (Arg.imm 0, ())))
                        (Expr.call (as := [i64, i32, i32, i64]) (bs := [i64])
                          "full_m6_sweep_units"
                          (Arg.var c.hdr, Arg.var nv32, Arg.var p_30.fst, Arg.var tick_lim, ())
                          fun p_33 =>
                         Expr.let_ { sig := [i64, i64], code := OpCode.cmp .eq i64 .bool rfl,
                                     args := (Arg.var p_33.fst,
                                       Arg.imm 18446744073709551615, ()) } fun p_34 =>
                         Expr.jnz (Arg.var p_34.fst)
                           (Expr.group (sig := [[i32]]) (fun Js =>
                             Blocks.cons (fun p =>
                               Expr.let_ { sig := [i32, i32], code := OpCode.cmp .ult i32 .bool rfl,
                                           args := (Arg.var p.fst, Arg.var nv32, ()) } fun p_35 =>
                               Expr.jnz (Arg.var p_35.fst)
                                 (Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                              args := (Arg.var p.fst, ()) } fun p_36 =>
                                  Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                              args := (Arg.var p_36.fst, Arg.imm 4, ()) }
                                    fun p_37 =>
                                  Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                              args := (Arg.var c.pWorkStk1,
                                                Arg.var p_37.fst, ()) } fun p_38 =>
                                  Expr.load i32 (Arg.var p_38.fst) fun ld =>
                                  Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                              args := (Arg.var ld, ()) } fun p_39 =>
                                  Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                              args := (Arg.var p_39.fst, Arg.imm 4, ()) }
                                    fun p_40 =>
                                  Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                              args := (Arg.var c.pTarjanMark,
                                                Arg.var p_40.fst, ()) } fun p_41 =>
                                  Expr.store (t := i32) (Arg.imm 0) (Arg.var p_41.fst)
                                    (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                                 args := (Arg.var p.fst, Arg.imm 1, ()) }
                                        fun p_42 =>
                                     Expr.jump Js.fst (Arg.var p_42.fst, ())))
                                 (Expr.ret (Arg.imm 20, ())))
                             Blocks.nil)
                             (fun Js => Expr.jump Js.fst (Arg.imm 0, ())))
                           (Expr.let_ { sig := [i64], code := OpCode.trunc 64 32,
                                        args := (Arg.var p_33.fst, ()) } fun p_35 =>
                            Expr.call (as := [i64, i32, i32, i64]) (bs := [i64])
                              "full_m6_sweep_classes"
                              (Arg.var c.hdr, Arg.var nv32, Arg.var p_35.fst,
                                Arg.var tick_lim, ()) fun p_36 =>
                            Expr.group (sig := [[i32]]) (fun Js =>
                              Blocks.cons (fun p_37 =>
                                Expr.let_ { sig := [i32, i32],
                                            code := OpCode.cmp .ult i32 .bool rfl,
                                            args := (Arg.var p_37.fst, Arg.var nv32, ()) }
                                  fun p_38 =>
                                Expr.jnz (Arg.var p_38.fst)
                                  (Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                               args := (Arg.var p_37.fst, ()) } fun p =>
                                   Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                               args := (Arg.var p.fst, Arg.imm 4, ()) } fun p =>
                                   Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                               args := (Arg.var c.pWorkStk1,
                                                 Arg.var p.fst, ()) } fun p =>
                                   Expr.load i32 (Arg.var p.fst) fun ld =>
                                   Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                               args := (Arg.var ld, ()) } fun p =>
                                   Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                               args := (Arg.var p.fst, Arg.imm 4, ()) } fun p =>
                                   Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                               args := (Arg.var c.pTarjanMark,
                                                 Arg.var p.fst, ()) } fun p =>
                                   Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
                                     (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                                  args := (Arg.var p_37.fst, Arg.imm 1, ()) }
                                        fun p =>
                                      Expr.jump Js.fst (Arg.var p.fst, ())))
                                  (Expr.let_ { sig := [i64, i64],
                                               code := OpCode.cmp .eq i64 .bool rfl,
                                               args := (Arg.var p_36.fst, Arg.imm 20, ()) }
                                     fun p_39 =>
                                   Expr.jnz (Arg.var p_39.fst) (Expr.ret (Arg.imm 20, ()))
                                     (Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                                  args := (Arg.var c.hdr, Arg.imm 1024, ()) }
                                        fun p_40 =>
                                      Expr.load i64 (Arg.var p_40.fst) fun ld =>
                                      Expr.let_ { sig := [i64, i64],
                                                  code := OpCode.cmp .ne i64 .bool rfl,
                                                  args := (Arg.var ld, Arg.imm 0, ()) } fun p_41 =>
                                      Expr.jnz (Arg.var p_41.fst) (Expr.ret (Arg.imm 20, ()))
                                        (Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                                                     args := (Arg.imm 24, ()) } fun p_42 =>
                                         Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                                                     args := (Arg.var p_42.fst, Arg.imm 4, ()) }
                                            fun p_43 =>
                                         Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                                                     args := (Arg.var k_ptr, Arg.var p_43.fst, ()) }
                                            fun p_44 =>
                                         Expr.load i32 (Arg.var p_44.fst) fun ld =>
                                         Expr.group (sig := [[]]) (fun _Js =>
                                           Blocks.cons (fun _ =>
                                             Expr.group (sig := [[i64]]) (fun _Js =>
                                               Blocks.cons (fun p => Expr.ret (Arg.var p.fst, ()))
                                                 Blocks.nil)
                                               (fun Js =>
                                                 Expr.let_ { sig := [i64, i64],
                                                             code := OpCode.add i64,
                                                             args := (Arg.var c.hdr,
                                                               Arg.imm 1024, ()) }
                                                    fun p =>
                                                 Expr.load i64 (Arg.var p.fst) fun ld =>
                                                 Expr.let_ { sig := [i64, i64],
                                                             code := OpCode.cmp .ne i64 .bool rfl,
                                                             args := (Arg.var ld, Arg.imm 0, ()) }
                                                    fun p =>
                                                 Expr.jnz (Arg.var p.fst)
                                                   (Expr.jump Js.fst (Arg.imm 20, ()))
                                                   (Expr.jump Js.fst (Arg.imm 1, ()))))
                                             Blocks.nil)
                                           (fun Js =>
                                             Expr.let_ { sig := [i32, i32],
                                                         code := OpCode.cmp .ugt i32 .bool rfl,
                                                         args := (Arg.var ld, Arg.imm 0, ()) }
                                                fun p_45 =>
                                             Expr.jnz (Arg.var p_45.fst)
                                               (Expr.call (as := [i64, i32]) (bs := [.bool])
                                                 "full_m6_dense_els"
                                                 (Arg.var c.hdr, Arg.var ld, ()) fun p =>
                                                Expr.jnz (Arg.var p.fst)
                                                  (Expr.jump Js.fst ())
                                                  (Expr.ret (Arg.imm 20, ())))
                                               (Expr.jump Js.fst ()))))))
                              Blocks.nil)
                              (fun Js => Expr.jump Js.fst (Arg.imm 0, ())))))))))) m1 := by
  intro mv32 k_ptr
  obtain ⟨L1, hL1_len, hL1_mv, hhwm1_L⟩ := hhwm1
  have hnv_le := hm6c1.2.2.1
  have hws1_1 := hm6c1.2.2.2.1
  have hscr1_len : s1.scratch.scratch_buf.length = c.scratch_cap :=
    hinv1.1.scratch_ok.scratch_buf_len
  have h6_lt : L1.k6Base + 6 < s1.scratch.scratch_buf.length := by
    have := L1.hmaxV; have := L1.hacap
    rw [hscr1_len, ← hL1_len]; unfold K6Layout.scrLen K6Layout.k6Base; omega
  have hptr_incons := s13_k6_hdr_ptr hL1_len hL1_mv (idx := 6) (by decide)
  let k_incons := s1.scratch.scratch_buf[L1.k6Base + 6]'h6_lt
  have hld_incons : loadVal m1 i32 (k_ptr + BitVec.ofNat 64 6 * 4) = some k_incons := by
    dsimp only [k_incons]; rw [hptr_incons]; exact load_full_scratch_buf h6_lt hm1
  have hinc_eq : k_incons = (k6StateOfScratch L1 s1.scratch.scratch_buf).incons := by
    have := s13_k6StateOfScratch_incons_eq (L := L1) (scr := s1.scratch.scratch_buf)
    rwa [List.getElem?_eq_getElem h6_lt, Option.getD_some] at this
  refine head_wp_load ?_ hld_incons ?_
  · rfl
  c0_hsplit
  · refine s13_sweep_tmk_clear_wp hinv1.1 hnv_eq hnv_le hws1_1 htmk1 hm1 ?_
    intro tmk1' m1' htmk1'_len htmk0_1' hm1'
    let s1' : FullState := { s1 with scratch := { s1.scratch with tarjan_mark := tmk1' } }
    have hinv1' := s13_denseInvW_with_tmk hinv1 htmk1'_len
    have huns1 : (cnfOfClauses F_cur).Unsat := by
      have hm6c1' : M6SweepConeOk F_cur s1 nv := hm6c1
      have hnv_k6 : (k6StateOfScratch L1 s1.scratch.scratch_buf).nv.toNat = nv := by
        obtain ⟨_, _, _, _, _, hge, hlt, hnv⟩ := hm6c1'
        have hLeq : L1 = k6LayoutOfCap s1.scratch.scratch_buf.length hge hlt :=
          K6Layout.eq_of_scrLen_maxV (by rw [hL1_len, ← hscr1_len, k6LayoutOfCap_scrLen])
            (by rw [hL1_mv, ← hscr1_len]; rfl)
        have hnv_bd : nv ≤ k6MaxV s1.scratch.scratch_buf.length := hm6c1.2.1
        have hmv_bd := (k6LayoutOfCap s1.scratch.scratch_buf.length hge hlt).hmaxV
        rw [hLeq, hnv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine s13_k6StateOfScratch_incons (hL1_len.trans hscr1_len.symm)
        (hL1_mv.trans (congrArg k6MaxV hscr1_len.symm)) (hnv_k6 ▸ hm6c1) ?_
      rw [← hinc_eq]; exact hc
    have hinv1'' := m6_denseInvW_set_inconsistent hinv1' huns1
    c0_hstraight
    exact hQ 20#64 { s1' with core := { s1'.core with inconsistent := 1#64 } } _ hinv1'' hcv1
      (hfu1 ▸ Nat.le_refl _) htmk0_1' hrepr1 htrh1 hgu1 ⟨L1, hL1_len, hL1_mv, hhwm1_L⟩
      (Or.inr rfl) (fun _ => hinv1'.2.1.ext_sound.2 huns1) (by assumption)
  · refine wp_join_group (ts := [])
      (fun () mB => ∃ sB : FullState,
        FullDenseInvW c F0 F_cur sB ∧ sB.core.cur_vars = s.core.cur_vars ∧
        sB.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        FullCongReprInv F_cur (2 * sB.core.cur_vars) sB.core.repr ∧
        sB.scratch.tarjan_reach = s.scratch.tarjan_reach ∧
        (∀ i < 64, i ≠ 33 → sB.scratch.glue_used[i]? = s.scratch.glue_used[i]?) ∧
        (∃ L : K6Layout, L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
          K6HwmClean L (sB.scratch.glue_used[33]?.getD 0#32)
            (k6StateOfScratch L sB.scratch.scratch_buf)) ∧
        (∀ v < sB.core.cur_vars, sB.scratch.tarjan_mark[v]?.getD 0#32 ≠ 0#32 →
          ∃ i < nv, (sB.scratch.work_stk1[i]?.getD 0#32).toNat = v) ∧
        nv ≤ sB.core.cur_vars ∧
        (∀ i < nv, (sB.scratch.work_stk1[i]?.getD 0#32).toNat < sB.core.cur_vars) ∧
        (FullMem c sB ⋆ R) mB)
      (fun _ ⟨⟩ mB ⟨sB, hinvB, hcvB, hfuB, hreprB, htrhB, hguB, hhwmB, htmkB, hnvB, hws1B, hmB⟩ =>
        by
          c0_hstraight
          refine s13_sweep_tmk_clear_wp hinvB.1 hnv_eq hnvB hws1B htmkB hmB ?_
          intro tmkB' mB' htmkB'_len htmk0B' hmB'
          let sB' : FullState := { sB with scratch := { sB.scratch with tarjan_mark := tmkB' } }
          have hinvB' := s13_denseInvW_with_tmk hinvB htmkB'_len
          c0_hstraight
          exact hQ 1#64 sB' mB' hinvB' hcvB hfuB htmk0B' hreprB htrhB hguB hhwmB
            (Or.inl rfl) (fun h => by cases h) hmB')
      (fun Js hJs => by
        c0_hsplit
        · c0_hstraight
          exact hJs () m1 ⟨s1, hinv1, hcv1, (hfu1 ▸ Nat.le_refl _), hrepr1, htrh1, hgu1,
            ⟨L1, hL1_len, hL1_mv, hhwm1_L⟩, htmk1, hnv_le, hws1_1, hm1⟩
        · c0_hsplit
          · c0_hstraight
            exact hJs () m1 ⟨s1, hinv1, hcv1, (hfu1 ▸ Nat.le_refl _), hrepr1, htrh1, hgu1,
              ⟨L1, hL1_len, hL1_mv, hhwm1_L⟩, htmk1, hnv_le, hws1_1, hm1⟩
          · c0_hstraight; m6_call hSim
            refine ⟨c, F0, F_cur, s1, R, rfl, hinv1, (hnv_eq ▸ hm6c1),
              ⟨L1, hL1_len, hL1_mv, hhwm1_L⟩, hm1, ?_⟩
            intro rbit _ _ _ _ m2 s2 hinv2 hfu2 hm6c2 hhwm2 huns2 hrbit_le hm2
            have hfu2' : s2.core.fuel.toNat ≤ s.core.fuel.toNat := hfu1 ▸ hfu2
            have hnv2 : nv ≤ s2.core.cur_vars := hnv_eq ▸ hm6c2.2.2.1
            have hws1_2 : ∀ i < nv,
                (s2.scratch.work_stk1[i]?.getD 0#32).toNat < s2.core.cur_vars :=
              hnv_eq ▸ hm6c2.2.2.2.1
            c0_hsplit
            · refine s13_sweep_tmk_clear_wp hinv2.1 hnv_eq hnv2 hws1_2 htmk1 hm2 ?_
              intro tmk2' m2' htmk2'_len htmk0_2' hm2'
              let s2' := { s2 with scratch := { s2.scratch with tarjan_mark := tmk2' } }
              have hinv2' := s13_denseInvW_with_tmk hinv2 htmk2'_len
              have hcf2 := huns2 hc
              c0_hstraight
              exact hQ 20#64 { s2' with core := { s2'.core with inconsistent := 1#64 } } _
                (m6_denseInvW_set_inconsistent hinv2' hcf2) hcv1 hfu2' htmk0_2' hrepr1 htrh1
                hgu1 hhwm2 (Or.inr rfl) (fun _ => hinv2'.2.1.ext_sound.2 hcf2) (by assumption)
            · c0_hsplit
              · refine s13_sweep_tmk_clear_wp hinv2.1 hnv_eq hnv2 hws1_2 htmk1 hm2 ?_
                intro tmk2' m2' htmk2'_len htmk0_2' hm2'
                let s2' := { s2 with scratch := { s2.scratch with tarjan_mark := tmk2' } }
                c0_hstraight
                exact hQ 1#64 s2' m2' (s13_denseInvW_with_tmk hinv2 htmk2'_len) hcv1 hfu2'
                  htmk0_2' hrepr1 htrh1 hgu1 hhwm2 (Or.inl rfl) (fun h => by cases h) hm2'
              · have hrbit_le64 : rbit.toNat ≤ 64 := hrbit_le (by assumption)
                c0_hstraight; m6_call hUnits
                refine ⟨c, F0, F_cur, s2, R, rfl, hinv2, hnv_eq ▸ hm6c2, hrbit_le64, hhwm2,
                  hm2, ?_⟩
                intro ur s3 m3 hinv3 hcv3 hfu3 hrepr3_eq hws1_3 htmk3_eq htrh3 hgu3_eq hm6c3
                  hhwm3 hur_uns hur_le hm3
                exact s13_sweep_var_post_units_wp hClasses hEls hinv3 (hcv3.trans hcv1)
                  (Nat.le_trans hfu3 hfu2') (by rw [hcv3, hrepr3_eq]; exact hrepr1)
                  (hnv_eq ▸ hm6c3) (htrh3.trans htrh1)
                  (fun i hi1 hi2 => by rw [hgu3_eq]; exact hgu1 i hi1 hi2) hhwm3
                  (fun v hv hne => by
                    rw [htmk3_eq] at hne; rw [hws1_3]; exact htmk1 v (hcv3 ▸ hv) hne)
                  hnv_eq hur_uns hur_le hm3 hQ)

theorem full_m6_sweep_var_s13_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hFind : ∀ a m Q X, fullCongFindSpec a m Q X →
      Γ "full_cong_find" [i64, i32] [i32] a m Q X)
    (hCone : ∀ a m Q X, step13SweepConeSpec a m Q X →
      Γ "full_m6_sweep_cone" [i64, i32] [i64] a m Q X)
    (hSim : ∀ a m Q X, step13SweepSimSpec a m Q X →
      Γ "full_m6_sweep_sim" [i64, i32, i64] [i32] a m Q X)
    (hUnits : ∀ a m Q X, step13SweepUnitsSpec a m Q X →
      Γ "full_m6_sweep_units" [i64, i32, i32, i64] [i64] a m Q X)
    (hClasses : ∀ a m Q X, step13SweepClassesSpec a m Q X →
      Γ "full_m6_sweep_classes" [i64, i32, i32, i64] [i64] a m Q X)
    (hEls : ∀ a m Q X, step13DenseElsSpec a m Q X →
      Γ "full_m6_dense_els" [i64, i32] [.bool] a m Q X) :
    ∀ args m Q X, step13SweepVarSpec args m Q X →
      Func.wp Γ full_m6_sweep_var_body args m Q X := by
  rintro ⟨h, root_v, tick_lim, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv, hcap, hrv, htmk, hrepr, ⟨L, hLlen, hLmv, hhwm⟩, hm, hQ⟩
  unfold Func.wp full_m6_sweep_var_body
  have hscr_bd : c.scratch_cap < 2 ^ 64 := by
    have := c.hscr; unfold dimacsBound at this; omega
  c0_hstraight
  refine k6_maxV_call_step hMaxV hscr_bd ?_
  have hmv_lt := L.hmaxV
  c0_hsplit
  · exfalso
    have h0 := congrArg BitVec.toNat hc
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, ← hLmv,
      Nat.mod_eq_of_lt (by omega : L.maxV < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : L.maxV < 2 ^ 32)] at h0
    simp at h0; omega
  · have hmv_eq32 : (BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32 =
        BitVec.ofNat 32 (k6MaxV c.scratch_cap) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, ← hLmv]
      rw [Nat.mod_eq_of_lt (by omega : L.maxV < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : L.maxV < 2 ^ 32)]
    have hcv_le := hinv.1.core_ok.cur_vars_le
    have hmv_bd := c.hmaxv; unfold dimacsBound at hmv_bd
    have hrl0_eq : (root_v <<< 1#32).toNat = 2 * root_v.toNat := by
      have : root_v.toNat < 2 ^ 30 := by omega
      change (root_v <<< (1 : Nat)).toNat = 2 * root_v.toNat
      clear hinv hcap htmk hrepr L hLlen hLmv hhwm hm hQ hscr_bd hmv_lt hmv_eq32 hcv_le hmv_bd
      bv_omega
    have hrl0_lt : (root_v <<< 1#32).toNat < 2 * s.core.cur_vars := by omega
    c0_hstraight
    refine s13_els_ar_call_find hFind hrepr hrl0_lt hm ?_
    intro r0 repr0 m0 hrepr0_len hrepr0 _hr0_lt _heq0 hm0
    let s0 : FullState := { s with core := { s.core with repr := repr0 } }
    have hinv0 := m6_denseInvW_set_repr hinv (hrepr0_len.trans hinv.1.core_ok.repr_len)
    c0_hsplit
    · c0_hstraight
      exact hQ 1#64 s0 m0 hinv0 rfl (Nat.le_refl _) htmk hrepr0 rfl (fun _ _ _ => rfl)
        ⟨L, hLlen, hLmv, hhwm⟩ (Or.inl rfl) (fun h => by cases h) hm0
    · m6_call hCone
      refine ⟨c, F0, F_cur, s0, R, rfl, hinv0, hcap, hrv, htmk, ⟨L, hLlen, hLmv, hhwm⟩, hm0, ?_⟩
      intro pk tmp1 ws1 tmk1 scr1 gu1 m1 s1 nv _nc hinv1 hcv1 hfu1 _hval1 _hinc1 hm6c1 _hnc_le
        _hpk_eq hgu1 hhwm1 htmk1 hm1
      have hnv_bd : nv ≤ k6MaxV c.scratch_cap := by
        rw [← hinv1.1.scratch_ok.scratch_buf_len]; exact hm6c1.2.1
      have hnv32_eq : ((pk &&& 65535#64).setWidth 32).toNat = nv := by
        dsimp only [nv]
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by rw [← hLmv] at hnv_bd; omega)]
      c0_hstraight
      try rw [hmv_eq32]
      exact s13_sweep_var_post_cone_wp hSim hUnits hClasses hEls hinv1 hcv1 hfu1
        (by simpa [s1, s0, hcv1] using hrepr0) hm6c1 rfl
        hgu1 hhwm1 htmk1 hnv32_eq hm1 hQ

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S1
