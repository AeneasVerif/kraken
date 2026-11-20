module

public import LeanQbe.T.Examples.Kissat.FullBveBvaLemmas2
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` UNSAT-Only BVE/BCE Proofs — Part 3 (`Stage 4`, BVE/BCE Shard)

Proves the remaining two owned Stage-4 parametric `(Γ : Env)` `Func.wp` theorems (UNSAT-only):
1. `full_bve_weaken_wp`: pushes reconstruction clauses/binaries to `extend_stk`, deletes binaries
   via `full_delete_binary`, and marks arena clauses `PH_GARB`, preserving `FullDenseInvW` and
   `fullArenaClauseRefs`.
2. `full_bve_try_bce_wp`: `SafetySlice`-style preservation of `lit_mark` and `FullDenseInvW` via
   `FullArenaVarsNodup` pigeonhole bounding (`sz ≤ max_vars`) and `tmpMark_clear_step`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

namespace FullBveBvaHelpers

open FullBveBvaSpecs

theorem weaken_ext_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (hdw : FullDenseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hcore : PreservesCoreSlice (fullSafetySlice c).coreProj s s')
    (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hel : s'.scratch.extend_len ≤ c.extend_cap) :
    FullDenseInvW c F0 F_cur s' ∧
    s'.core.cur_vars = s.core.cur_vars ∧
    s'.core.fuel = s.core.fuel ∧
    fullArenaClauseRefs s' = fullArenaClauseRefs s := by
  have heq : s'.core = s.core := fullCoreState_agrees_with_scratch hcore
  have hll_wf : FullLastLearnedWf s' := fun i hi => by
    have h0 := hdw.2.2.2.2.1.1 i hi
    change (s'.scratch.last_learned[i]?.getD 0xFFFFFFFF#32) = 0xFFFFFFFF#32 ∨
      (s'.scratch.last_learned[i]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefsCore s'.core
    rw [hll, heq]; exact h0
  exact ⟨fullDenseInvW_with_scratch hdw hlen' hcore ⟨hll_wf, hel⟩,
    congrArg FullCoreState.cur_vars heq, congrArg FullCoreState.fuel heq,
    by unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [heq]⟩

theorem bce_mark_step_lt {c : FullCfg}
    {mcnt i : Nat} {tmp : List (BitVec 32)} {lm : List (BitVec 8)}
    (hcov : ∀ l < 2 * c.max_vars,
      (∀ r < mcnt, (tmp[r]?.getD 0#32).toNat ≠ l) → lm[l]? = some 0#8)
    (hbd : ∀ r < mcnt, (tmp[r]?.getD 0#32).toNat < 2 * c.max_vars)
    (hr : mcnt ≤ i) (htl : tmp.length = c.max_vars) (hll : lm.length = 2 * c.max_vars)
    (hi_max : i < c.max_vars) {l : BitVec 32} (hl_mv : l.toNat < 2 * c.max_vars) :
    mcnt < tmp.length ∧ (l ^^^ 1#32).toNat < lm.length ∧ mcnt + 1 ≤ i + 1 ∧
    (∀ r < mcnt + 1, ((tmp.set mcnt (l ^^^ 1#32))[r]?.getD 0#32).toNat < 2 * c.max_vars) ∧
    (∀ l' < 2 * c.max_vars,
      (∀ r < mcnt + 1, ((tmp.set mcnt (l ^^^ 1#32))[r]?.getD 0#32).toNat ≠ l') →
      (lm.set (l ^^^ 1#32).toNat 1#8)[l']? = some 0#8) := by
  have hmt : mcnt < tmp.length := by rw [htl]; omega
  have hl1 : (l ^^^ 1#32).toNat < 2 * c.max_vars := by
    rw [FullBveBvaTactics.bv32_xor_1_toNat]; exact FullBveBvaTactics.nat_xor1_lt_two_mul hl_mv
  refine ⟨hmt, by rw [hll]; exact hl1, by omega, fun r hr1 => ?_, fun l' hl' hnone => ?_⟩
  · by_cases hrm : r = mcnt
    · subst hrm; rw [List.getElem?_set_self hmt, Option.getD_some]; exact hl1
    · rw [List.getElem?_set_ne (Ne.symm hrm)]; exact hbd r (by omega)
  · have hne : (l ^^^ 1#32).toNat ≠ l' := by
      have := hnone mcnt (Nat.lt_succ_self mcnt)
      rw [List.getElem?_set_self hmt, Option.getD_some] at this; exact this
    rw [List.getElem?_set_ne hne]
    exact hcov l' hl' fun r hr0 => by
      have := hnone r (Nat.lt_succ_of_lt hr0)
      rwa [List.getElem?_set_ne (by omega)] at this

theorem arena_lits_nodup_len_le {c : FullCfg} {s : FullState} {cr_n : Nat}
    (hcr_bd : cr_n + 3 + fullArenaClauseSize s cr_n ≤ s.core.arena.length)
    (hlts : ∀ l ∈ fullArenaClauseLits s cr_n, l < 2 * c.max_vars)
    (hnd : ((fullArenaClauseLits s cr_n).map (· / 2)).Nodup) :
    fullArenaClauseSize s cr_n ≤ c.max_vars := by
  have hlen : ((fullArenaClauseLits s cr_n).map (· / 2)).length = fullArenaClauseSize s cr_n := by
    unfold fullArenaClauseSize at hcr_bd ⊢
    unfold fullArenaClauseLits fullArenaClauseLitsCore
    simp only [List.length_map, List.length_take, List.length_drop]
    omega
  rw [← hlen]
  refine nodup_lt_length_le hnd fun v hv => ?_
  rw [List.mem_map] at hv
  obtain ⟨l, hl, rfl⟩ := hv
  have := hlts l hl; omega

theorem weaken_markGarb_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s1 : FullState} {w : BitVec 32} (hw_ref1 : w.toNat ∈ fullArenaClauseRefs s1)
    (hw_ar : w.toNat < s1.core.arena.length) (ag' : BitVec 64) :
    let s2 : FullState :=
      { s1 with core :=
        { s1.core with
          arena := s1.core.arena.set w.toNat (s1.core.arena[w.toNat]'hw_ar ||| 0x00080000#32)
          arena_garbage := ag' } }
    FullDenseInvW c F0 F_cur s1 →
    fullArenaClauseRefs s2 = fullArenaClauseRefs s1 ∧ FullDenseInvW c F0 F_cur s2 := fun hdw1 => by
  have ⟨hrefs2, hdw2⟩ := fullDenseInvW_markGarb hdw1 hw_ref1 ag'
  have hhdr : fullArenaHdr s1 w.toNat = s1.core.arena[w.toNat]'hw_ar := by
    unfold fullArenaHdr fullArenaHdrCore
    rw [List.getElem?_eq_getElem hw_ar, Option.getD_some]
  exact ⟨by simpa only [hhdr] using hrefs2, by simpa only [hhdr] using hdw2⟩

end FullBveBvaHelpers

section
open FullBveBvaTactics FullBveBvaSpecs FullBveBvaHelpers
open scoped FullArenaTactics FullBveBvaTactics

theorem full_bve_weaken_wp (Γ : Env)
    (hExtPush2 : ∀ xs m Q X, fullExtendPush2Spec xs m Q X →
      Γ "full_extend_push2" [i64, i32, i32] [.bool] xs m Q X)
    (hDelBin : ∀ xs m Q X, fullDeleteBinarySpec xs m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] xs m Q X)
    (hExtPushCl : ∀ xs m Q X, fullExtendPushClSpec xs m Q X →
      Γ "full_extend_push_cl" [i64, i32, i32] [.bool] xs m Q X) :
    ∀ args m Q X, fullBveWeakenSpec args m Q X → Func.wp Γ full_bve_weaken_body args m Q X := by
  rintro ⟨h, blk_lit, off, cnt, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hdw, hblk, hoff, hitems, hm, hQ⟩
  have hmv := c.hmaxv; have hsc := c.hscr; have harc := c.harena
  unfold dimacsBound at hmv hsc harc
  unfold Func.wp full_bve_weaken_body
  bve_steps!
  refine wp_loop_inv (ts := [i32])
    (fun (i, _) mi =>
      i.toNat ≤ cnt.toNat ∧
      ∃ si, FullDenseInvW c F0 F_cur si ∧
        si.core.cur_vars = s.core.cur_vars ∧ si.core.fuel = s.core.fuel ∧
        si.scratch.scratch_buf = s.scratch.scratch_buf ∧
        fullArenaClauseRefs si = fullArenaClauseRefs s ∧
        (FullMem c si ⋆ R) mi)
    (fun (i, _) _ => cnt.toNat - i.toNat)
    ?_ ?_
  · intro J hJ; bve_steps!
    exact hJ (0#32, PUnit.unit) m ⟨Nat.zero_le _, s, hdw, rfl, rfl, rfl, rfl, hm⟩
  · rintro J ⟨i, ⟨⟩⟩ mi ⟨hi_le, si, hdw_i, hcv_eq, hfuel_eq, hscr_eq, hrefs_eq, hm_i⟩ ih
    have hcl_i := hdw_i.1.core_ok; have hsl_i := hdw_i.1.scratch_ok
    have hscrl_i : si.scratch.scratch_buf.length = c.scratch_cap := hsl_i.scratch_buf_len
    have harl_i : si.core.arena.length = c.arena_cap := hcl_i.arena_len_arr
    have harle_i : si.core.arena_len ≤ c.arena_cap := hcl_i.arena_len_le
    bve_steps
    · have hi_lt : i.toNat < cnt.toNat := by bv_omega
      have hoff_nat : (off + i).toNat = off.toNat + i.toNat := by bv_omega
      have hscr_lt : (BitVec.setWidth 64 (off + i)).toNat < si.scratch.scratch_buf.length := by
        rw [bv_c0_zext32_64, hscrl_i, hoff_nat]; omega
      have hw_eq : si.scratch.scratch_buf[(off + i).toNat]'(by
          rw [hscrl_i, hoff_nat]; omega) = s.scratch.scratch_buf[off.toNat + i.toNat]?.getD 0#32 :=
        Option.some.inj (by
          rw [← List.getElem?_eq_getElem (by rw [hscrl_i, hoff_nat]; omega), hscr_eq, hoff_nat,
            List.getElem?_eq_getElem (by rw [hdw.1.scratch_ok.scratch_buf_len]; omega)]; rfl)
      have hitem_i := hitems i.toNat hi_lt
      unfold FullBveWeakItemOk at hitem_i
      have hbin : (si.scratch.scratch_buf[(BitVec.setWidth 64 (off + i)).toNat]'hscr_lt &&&
          0x80000000#32) ≠ 0#32 := hc
      refine wp_call_of_spec _ _ (hExtPush2 _ mi _ X ⟨c, si, R,
        ⟨rfl, hdw_i.2.2.2.2.1.2⟩, hdw_i.1, hm_i, ?_⟩)
      rintro ok s1 m1 hcore1 hlen1 ⟨hll1, hel1, hscr1⟩ hm1
      dsimp only [fullSafetySlice_mem] at hm1
      have ⟨hdw1, hcv1, hfuel1, hrefs1⟩ := weaken_ext_step hdw_i hlen1 hcore1 hll1 hel1
      bve_steps!
      · refine wp_call_of_spec _ _ (hDelBin _ m1 _ X ⟨c, s1, R, rfl, hdw1.1,
          hdw1.2.1.watches.layout, hm1, ?_⟩)
        intro wvec' wstk' wu' nb' m2 _ hlen2 _hwl2 hwat2 hm2
        let s2 : FullState :=
          { s1 with core := { s1.core with
            wvec := wvec', wstk := wstk', wusable := wu', num_binary := nb' } }
        have hdw2 := fullDenseInvW_of_delete_binary hdw1 hlen2 hwat2
        have hrefs2 : fullArenaClauseRefs s2 = fullArenaClauseRefs s1 := by
          unfold fullArenaClauseRefs fullArenaClauseRefsCore; rfl
        bve_steps!
        exact ih (i + 1#32, PUnit.unit) m2 (by bv_omega) ⟨by bv_omega, s2, hdw2,
          hcv1.trans hcv_eq, hfuel1.trans hfuel_eq, hscr1.trans hscr_eq,
          hrefs2.trans (hrefs1.trans hrefs_eq), hm2⟩
      · exact hQ false s1 m1 hdw1 (hcv1.trans hcv_eq) (hfuel1.trans hfuel_eq)
          (hscr1.trans hscr_eq) (hrefs1.trans hrefs_eq) hm1
    · have hi_lt : i.toNat < cnt.toNat := by bv_omega
      have hoff_nat : (off + i).toNat = off.toNat + i.toNat := by bv_omega
      have hscr_lt : (BitVec.setWidth 64 (off + i)).toNat < si.scratch.scratch_buf.length := by
        rw [bv_c0_zext32_64, hscrl_i, hoff_nat]; omega
      have hw_eq : si.scratch.scratch_buf[(off + i).toNat]'(by
          rw [hscrl_i, hoff_nat]; omega) = s.scratch.scratch_buf[off.toNat + i.toNat]?.getD 0#32 :=
        Option.some.inj (by
          rw [← List.getElem?_eq_getElem (by rw [hscrl_i, hoff_nat]; omega), hscr_eq, hoff_nat,
            List.getElem?_eq_getElem (by rw [hdw.1.scratch_ok.scratch_buf_len]; omega)]; rfl)
      have hitem_i := hitems i.toNat hi_lt
      unfold FullBveWeakItemOk at hitem_i
      have hnb : ¬ (s.scratch.scratch_buf[off.toNat + i.toNat]?.getD 0#32 &&&
          0x80000000#32) ≠ 0#32 := by
        intro hne
        have hhc : si.scratch.scratch_buf[(BitVec.setWidth 64 (off + i)).toNat]'hscr_lt &&&
            0x80000000#32 = 0#32 := hc
        simp only [bv_c0_zext32_64] at hhc; rw [hw_eq] at hhc; exact hne hhc
      rw [ite_eq_right hnb] at hitem_i
      have hitem_ref : (si.scratch.scratch_buf[(BitVec.setWidth 64 (off + i)).toNat]'hscr_lt
          ).toNat ∈ fullArenaClauseRefs si := by
        simp only [bv_c0_zext32_64]; rw [hw_eq, hrefs_eq]; exact hitem_i
      refine wp_call_of_spec _ _ (hExtPushCl _ mi _ X ⟨c, si, R,
        ⟨rfl, hdw_i.2.2.2.2.1.2⟩, hdw_i.1, hm_i, ?_⟩)
      rintro ok s1 m1 hcore1 hlen1 ⟨hll1, hel1, hscr1⟩ hm1
      dsimp only [fullSafetySlice_mem] at hm1
      have ⟨hdw1, hcv1, hfuel1, hrefs1⟩ := weaken_ext_step hdw_i hlen1 hcore1 hll1 hel1
      have heq_core : s1.core = si.core := fullCoreState_agrees_with_scratch hcore1
      let w := si.scratch.scratch_buf[(BitVec.setWidth 64 (off + i)).toNat]'hscr_lt
      have hw_ref1 : w.toNat ∈ fullArenaClauseRefs s1 := by
        unfold fullArenaClauseRefs; rw [heq_core]; exact hitem_ref
      have hwf1 := hdw1.2.1.arena.refs_wf w.toNat hw_ref1
      have har1 : s1.core.arena.length = c.arena_cap := hlen1.core_ok.arena_len_arr
      have harle1 : s1.core.arena_len ≤ c.arena_cap := hlen1.core_ok.arena_len_le
      have hbd1 : w.toNat + 3 + fullArenaClauseSize s1 w.toNat ≤ s1.core.arena_len := by
        unfold fullArenaClauseSize; omega
      have hw_ar : (BitVec.setWidth 64 w).toNat < s1.core.arena.length := by
        rw [bv_c0_zext32_64]; omega
      have hw2_ar : (BitVec.setWidth 64 w + 2).toNat < s1.core.arena.length := by bv_omega
      have hw_lt_ar : (si.scratch.scratch_buf[(BitVec.setWidth 64 (off + i)).toNat]'hscr_lt).toNat +
          2 < s1.core.arena.length := by change w.toNat + 2 < _; omega
      bve_steps!
      · let w_hm := si.scratch.scratch_buf[(off + i).toNat]'(by rw [hscrl_i, hoff_nat]; omega)
        have hw_hm_eq : w_hm = w := Option.some.inj (by
          dsimp only [w_hm, w]
          rw [← List.getElem?_eq_getElem (by rw [hscrl_i, hoff_nat]; omega),
            ← List.getElem?_eq_getElem hscr_lt, bv_c0_zext32_64])
        have hw_hm_ref : w_hm.toNat ∈ fullArenaClauseRefs s1 := by rw [hw_hm_eq]; exact hw_ref1
        have hw_hm_ar : w_hm.toNat < s1.core.arena.length := by
          have h1 := hw_ar; rw [bv_c0_zext32_64, ← hw_hm_eq] at h1; exact h1
        have hw2_hm_ar : (BitVec.setWidth 64 w_hm + 2).toNat <
            (s1.core.arena.set w_hm.toNat
              (s1.core.arena[w_hm.toNat]'hw_hm_ar ||| 0x00080000#32)).length := by
          rw [List.length_set, hw_hm_eq]; exact hw2_ar
        let ag_hm := s1.core.arena_garbage + 3 + BitVec.setWidth 64
          ((s1.core.arena.set w_hm.toNat
            (s1.core.arena[w_hm.toNat]'hw_hm_ar ||| 0x00080000#32))[(BitVec.setWidth 64 w_hm +
              2).toNat]'hw2_hm_ar)
        have ⟨hrefs2, hdw2⟩ := weaken_markGarb_step hw_hm_ref hw_hm_ar ag_hm hdw1
        exact ih (i + 1#32, PUnit.unit) m (by bv_omega) ⟨by bv_omega, _, hdw2,
          hcv1.trans hcv_eq, hfuel1.trans hfuel_eq, hscr1.trans hscr_eq,
          hrefs2.trans (hrefs1.trans hrefs_eq), hm⟩
      · exact hQ false s1 m1 hdw1 (hcv1.trans hcv_eq) (hfuel1.trans hfuel_eq)
          (hscr1.trans hscr_eq) (hrefs1.trans hrefs_eq) hm1
    · bve_steps!
      exact hQ true si mi hdw_i hcv_eq hfuel_eq hscr_eq hrefs_eq hm_i

private def tryBceCleanupExpr (c : FullCfg) (mcnt : Val i32) (blocked : Val Ty.bool) :
    Expr Val Cont [Ty.bool] :=
  Expr.group (sig := [[i32]])
    (fun Js =>
      Blocks.cons
        (fun p =>
          Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i32) (Arg.var p.fst, Arg.var mcnt, ())) fun p1 =>
          Expr.jnz (Arg.var p1.fst)
            (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p.fst, ())) fun p2 =>
             Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p2.fst, Arg.imm 4, ())) fun p3 =>
             Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pTmp, Arg.var p3.fst, ())) fun p4 =>
             Expr.load i32 (Arg.var p4.fst) fun ld =>
             Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld, ())) fun p5 =>
             Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pLitMark, Arg.var p5.fst, ())) fun p6 =>
             Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm 0, ())) fun p7 =>
             Expr.store (Arg.var p7.fst) (Arg.var p6.fst)
               (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var p.fst, Arg.imm 1, ())) fun p8 =>
                 Expr.jump Js.fst (Arg.var p8.fst, ())))
            (Expr.ret (Arg.var blocked, ())))
        Blocks.nil)
    fun Js => Expr.jump Js.fst (Arg.imm 0, ())

private theorem try_bce_cleanup_wp (Γ : Env) (Q : Post [Ty.bool]) (X : XPost)
    (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop)
    (hdw : FullDenseInvW c F0 F_cur s) (mcnt : Val i32) (hmcnt_le : mcnt.toNat ≤ c.max_vars)
    (lm_mk : List (BitVec 8)) (tmp_mk : List (BitVec 32))
    (hlml_mk : lm_mk.length = 2 * c.max_vars) (htmpl_mk : tmp_mk.length = c.max_vars)
    (htmp_bd : ∀ r < mcnt.toNat, (tmp_mk[r]?.getD 0#32).toNat < 2 * c.max_vars)
    (hlm_cov : ∀ l < 2 * c.max_vars,
      (∀ r < mcnt.toNat, (tmp_mk[r]?.getD 0#32).toNat ≠ l) → lm_mk[l]? = some 0#8)
    (blocked : Val Ty.bool) (m_mk : Mem 64)
    (hm_mk : (FullMem c { s with core := { s.core with lit_mark := lm_mk, tmp := tmp_mk } } ⋆ R)
      m_mk)
    (hQ : ∀ (blk : Bool) (lm' : List (BitVec 8)) (tmp' : List (BitVec 32))
        (m' : ExtHashMap (BitVec 64) UInt8),
      let s' : FullState := { s with core := { s.core with lit_mark := lm', tmp := tmp' } }
      FullDenseInvW c F0 F_cur s' → (FullMem c s' ⋆ R) m' → Q (blk, ()) m') :
    wp Γ Q X (tryBceCleanupExpr c mcnt blocked) m_mk := by
  have hmv := c.hmaxv; unfold dimacsBound at hmv
  have hcl := hdw.1.core_ok; have hlml := hcl.lit_mark_len; have hlmc := hdw.2.2.1.2
  unfold tryBceCleanupExpr
  refine wp_loop_inv (ts := [i32])
    (fun (i, _) mi =>
      i.toNat ≤ mcnt.toNat ∧
      ∃ lmi : List (BitVec 8),
        lmi.length = 2 * c.max_vars ∧
        (∀ l < 2 * c.max_vars,
          ((∃ r < i.toNat, (tmp_mk[r]?.getD 0#32).toNat = l) ∨
           (∀ r < mcnt.toNat, (tmp_mk[r]?.getD 0#32).toNat ≠ l)) →
          lmi[l]? = some 0#8) ∧
        (FullMem c { s with core := { s.core with lit_mark := lmi, tmp := tmp_mk } } ⋆ R) mi)
    (fun (i, _) _ => mcnt.toNat - i.toNat)
    ?_ ?_
  · intro Ji hJi; bve_steps!
    exact hJi (0#32, PUnit.unit) m_mk ⟨Nat.zero_le _, lm_mk, hlml_mk, fun l hl hc => by
      rcases hc with ⟨r, hr, _⟩ | hnone
      · bv_omega
      · exact hlm_cov l hl hnone, hm_mk⟩
  · rintro Ji ⟨i, ⟨⟩⟩ mi ⟨hi_le, lmi, hlml_i, hcov_i, hm_i⟩ ihi
    bve_steps
    · have hi_lt : i.toNat < mcnt.toNat := by bv_omega
      have hi_tmp : i.toNat < tmp_mk.length := by rw [htmpl_mk]; omega
      have hl_mv : (tmp_mk[i.toNat]'hi_tmp).toNat < 2 * c.max_vars := by
        have := htmp_bd i.toNat hi_lt
        rwa [List.getElem?_eq_getElem hi_tmp, Option.getD_some] at this
      have hi_lm : (BitVec.setWidth 64 (tmp_mk[(BitVec.setWidth 64 i).toNat]'(by
          rw [bv_c0_zext32_64]; exact hi_tmp))).toNat < lmi.length := by
        rw [bv_c0_zext32_64, hlml_i]; simp only [bv_c0_zext32_64]; exact hl_mv
      bve_steps!
      have hcov' := tmpMark_clear_step hi_tmp hl_mv hlml_i hcov_i
      refine ihi (i + 1#32, PUnit.unit) _ (by bv_omega)
        ⟨by bv_omega, lmi.set (tmp_mk[i.toNat]'hi_tmp).toNat 0#8, by simp [hlml_i],
          fun l hl hc => ?_, ?_⟩
      · rw [show (i + 1#32).toNat = i.toNat + 1 from by bv_omega] at hc
        simpa [bv_c0_zext32_64] using hcov' l hl hc
      · exact (by
          first
          | assumption
          | have hm_z : (FullMem c { s with core := { s.core with
                lit_mark := lmi.set (BitVec.setWidth 64 (tmp_mk[(BitVec.setWidth 64 i).toNat]'(by
                  rw [bv_c0_zext32_64]; exact hi_tmp))).toNat 0#8
                tmp := tmp_mk } } ⋆ R) _ := by assumption
            simp only [bv_c0_zext32_64] at hm_z; exact hm_z)
    · have hi_eq : i.toNat = mcnt.toNat := by bv_omega
      have heq_lm : lmi = s.core.lit_mark := by
        refine fullLitMark_eq_of_all_zero hlml hlml_i hlmc fun l hl => ?_
        apply hcov_i l hl
        by_cases hex : ∃ r < mcnt.toNat, (tmp_mk[r]?.getD 0#32).toNat = l
        · exact Or.inl (hi_eq ▸ hex)
        · exact Or.inr fun r hr heq => hex ⟨r, hr, heq⟩
      subst heq_lm
      bve_steps!
      have hinv' := fullDenseInvW_with_tmp_litMark hdw hlml htmpl_mk hcl.tmp_len_le hlmc
      exact hQ blocked s.core.lit_mark tmp_mk mi hinv' hm_i

theorem full_bve_try_bce_wp (Γ : Env) :
    ∀ args m Q X, fullBveTryBceSpec args m Q X → Func.wp Γ full_bve_try_bce_body args m Q X := by
  rintro ⟨h, blk_lit, cr, opp_off, opp_n, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hdw, _hblk, hcr_ok, hcr_nd, hopp_bd, hopp_ok, hm, hQ⟩
  have hmv := c.hmaxv; have hsc := c.hscr; have harc := c.harena
  unfold dimacsBound at hmv hsc harc
  have hlen := hdw.1; have hcl := hlen.core_ok; have hsl := hlen.scratch_ok
  have hlml := hcl.lit_mark_len; have htmpl := hcl.tmp_len_arr
  have harl := hcl.arena_len_arr; have hscrl := hsl.scratch_buf_len
  have hlmc := hdw.2.2.1.2
  let P_mark : BitVec 32 → Mem 64 → Prop := fun mcnt m_mk =>
    mcnt.toNat ≤ c.max_vars ∧
    ∃ (lm_mk : List (BitVec 8)) (tmp_mk : List (BitVec 32)),
      lm_mk.length = 2 * c.max_vars ∧ tmp_mk.length = c.max_vars ∧
      (∀ r < mcnt.toNat, (tmp_mk[r]?.getD 0#32).toNat < 2 * c.max_vars) ∧
      (∀ l < 2 * c.max_vars,
        (∀ r < mcnt.toNat, (tmp_mk[r]?.getD 0#32).toNat ≠ l) → lm_mk[l]? = some 0#8) ∧
      (FullMem c { s with core := { s.core with lit_mark := lm_mk, tmp := tmp_mk } } ⋆ R) m_mk
  unfold Func.wp full_bve_try_bce_body
  bve_to_group
  refine wp_unroll_group fun J_mk hJ_mk => ?_
  try c0_let_simp
  have hAfterMark : ∀ (mcnt : Val i32) (m_mk : Mem 64),
      P_mark mcnt m_mk → J_mk (mcnt, PUnit.unit) m_mk := by
    rintro mcnt m_mk ⟨hmcnt_le, lm_mk, tmp_mk, hlml_mk, htmpl_mk, htmp_bd, hlm_cov, hm_mk⟩
    apply hJ_mk
    bve_steps!
    refine wp_loop_inv (ts := [.bool, i32])
      (fun (_blocked, j, _) mj => j.toNat ≤ opp_n.toNat ∧ mj = m_mk)
      (fun (_, j, _) _ => opp_n.toNat - j.toNat)
      ?_ ?_
    · intro Jj hJj; bve_steps!; exact hJj (true, 0#32, PUnit.unit) m_mk ⟨Nat.zero_le _, rfl⟩
    · clear J_mk hJ_mk
      rintro Jj ⟨blocked, j, ⟨⟩⟩ mj ⟨hj_le, hmj⟩ ihj
      subst mj
      bve_steps
      · have hj_lt : j.toNat < opp_n.toNat := by bv_omega
        have hopp_nat : (opp_off + j).toNat = opp_off.toNat + j.toNat := by bv_omega
        have hscr_j : (BitVec.setWidth 64 (opp_off + j)).toNat <
            s.scratch.scratch_buf.length := by rw [bv_c0_zext32_64, hscrl, hopp_nat]; omega
        have how_item := hopp_ok j.toNat hj_lt
        have how_get : s.scratch.scratch_buf[(BitVec.setWidth 64 (opp_off + j)).toNat]'hscr_j =
            s.scratch.scratch_buf[opp_off.toNat + j.toNat]?.getD 0#32 := Option.some.inj (by
          simp only [bv_c0_zext32_64]
          rw [← List.getElem?_eq_getElem (by rw [hscrl, hopp_nat]; omega), hopp_nat,
            List.getElem?_eq_getElem (by rw [hscrl]; omega)]; rfl)
        let ow := s.scratch.scratch_buf[(BitVec.setWidth 64 (opp_off + j)).toNat]'hscr_j
        unfold FullBveBceWeakOk at how_item
        have hbin_ow : (ow &&& 0x80000000#32) ≠ 0#32 := hc
        have hbin_item : (s.scratch.scratch_buf[opp_off.toNat + j.toNat]?.getD 0#32 &&&
            0x80000000#32) ≠ 0#32 := by dsimp only [ow] at hbin_ow; rwa [← how_get]
        rw [ite_eq_left hbin_item] at how_item
        have hlm_ow : (BitVec.setWidth 64 (ow &&& 0x7FFFFFFF#32)).toNat < lm_mk.length := by
          rw [bv_c0_zext32_64, hlml_mk]; dsimp only [ow]; rw [how_get]; exact how_item
        bve_steps! <;> exact ihj (_, j + 1#32, PUnit.unit) m_mk (by bv_omega) ⟨by bv_omega, rfl⟩
      · have hj_lt : j.toNat < opp_n.toNat := by bv_omega
        have hopp_nat : (opp_off + j).toNat = opp_off.toNat + j.toNat := by bv_omega
        have hscr_j : (BitVec.setWidth 64 (opp_off + j)).toNat <
            s.scratch.scratch_buf.length := by rw [bv_c0_zext32_64, hscrl, hopp_nat]; omega
        have how_item := hopp_ok j.toNat hj_lt
        have how_get : s.scratch.scratch_buf[(BitVec.setWidth 64 (opp_off + j)).toNat]'hscr_j =
            s.scratch.scratch_buf[opp_off.toNat + j.toNat]?.getD 0#32 := Option.some.inj (by
          simp only [bv_c0_zext32_64]
          rw [← List.getElem?_eq_getElem (by rw [hscrl, hopp_nat]; omega), hopp_nat,
            List.getElem?_eq_getElem (by rw [hscrl]; omega)]; rfl)
        let ow := s.scratch.scratch_buf[(BitVec.setWidth 64 (opp_off + j)).toNat]'hscr_j
        unfold FullBveBceWeakOk at how_item
        have hnb_ow : ¬ (s.scratch.scratch_buf[opp_off.toNat + j.toNat]?.getD 0#32 &&&
            0x80000000#32) ≠ 0#32 := by
          intro hne
          have hhc : ow &&& 0x80000000#32 = 0#32 := hc
          dsimp only [ow] at hhc; rw [how_get] at hhc; exact hne hhc
        rw [ite_eq_right hnb_ow] at how_item
        obtain ⟨how_ref, how_bd, how_lits⟩ := how_item
        have how_bd' : ow.toNat + 3 + fullArenaClauseSize s ow.toNat ≤ s.core.arena_len := by
          dsimp only [ow]; rw [how_get]; exact how_bd
        have how2_lt : (BitVec.setWidth 64 ow + 2).toNat < s.core.arena.length := by
          have := hcl.arena_len_le; bv_omega
        have how2_nat : (BitVec.setWidth 64 ow + 2).toNat = ow.toNat + 2 := by bv_omega
        let osz := s.core.arena[(BitVec.setWidth 64 ow + 2).toNat]'how2_lt
        have hosz_nat : osz.toNat = fullArenaClauseSize s ow.toNat := by
          unfold fullArenaClauseSize fullArenaClauseSizeCore osz
          rw [← Option.getD_some (a := s.core.arena[(BitVec.setWidth 64 ow + 2).toNat]'how2_lt),
            ← List.getElem?_eq_getElem how2_lt, how2_nat]
        bve_steps!
        refine wp_loop_inv (ts := [i32])
          (fun (k, _) mk => k.toNat ≤ osz.toNat ∧ mk = m_mk)
          (fun (k, _) _ => osz.toNat - k.toNat)
          ?_ ?_
        · intro Jk hJk; bve_steps!; exact hJk (0#32, PUnit.unit) m_mk ⟨Nat.zero_le _, rfl⟩
        · rintro Jk ⟨k, ⟨⟩⟩ mk ⟨hk_le, hmk⟩ ihk
          subst mk
          bve_steps
          · have hk_lt : k.toNat < osz.toNat := by
              have hscr_mod : (opp_off.toNat + j.toNat) % 2 ^ 32 <
                  s.scratch.scratch_buf.length := by
                change (opp_off + j).toNat < _; rw [hopp_nat, hscrl]; omega
              have how_hc : ow =
                  s.scratch.scratch_buf[(opp_off.toNat + j.toNat) % 2 ^ 32]'hscr_mod := by
                dsimp only [ow]; simp only [bv_c0_zext32_64]; rfl
              let idx_hc :=
                ((s.scratch.scratch_buf[(opp_off.toNat + j.toNat) % 2 ^ 32]'hscr_mod).toNat +
                  BitVec.toNat (2 : BitVec 64)) % 2 ^ 64
              have hidx_eq : idx_hc = ow.toNat + 2 := by
                dsimp only [idx_hc]; rw [← how_hc]; bv_omega
              have hc' : k.toNat < (s.core.arena[idx_hc]?.getD 0#32).toNat := by
                rw [List.getElem?_eq_getElem (by
                  have := hcl.arena_len_le; rw [hidx_eq, harl]; omega), Option.getD_some]
                exact hc
              rw [hidx_eq] at hc'
              rw [hosz_nat]; exact hc'
            have hk_nat : (BitVec.setWidth 64 ow + 3 + BitVec.setWidth 64 k).toNat =
                ow.toNat + 3 + k.toNat := by bv_omega
            have har_k : (BitVec.setWidth 64 ow + 3 + BitVec.setWidth 64 k).toNat <
                s.core.arena.length := by
              have := hcl.arena_len_le; rw [hk_nat, harl]; omega
            have hlm_k : (BitVec.setWidth 64 (s.core.arena[(BitVec.setWidth 64 ow + 3 +
                BitVec.setWidth 64 k).toNat]'har_k)).toNat < lm_mk.length := by
              rw [bv_c0_zext32_64, hlml_mk]
              apply how_lits
              rw [← how_get]
              change _ ∈ fullArenaClauseLits s ow.toNat
              unfold fullArenaClauseLits
              have hbd0 : ow.toNat + 3 + fullArenaClauseSizeCore s.core ow.toNat ≤
                  s.core.arena.length := by
                have := hcl.arena_len_le; unfold fullArenaClauseSize at how_bd'; omega
              rw [mem_fullArenaClauseLitsCore_iff hbd0]
              refine ⟨k.toNat, by unfold fullArenaClauseSize at hosz_nat; omega, ?_⟩
              congr 1; exact Option.some.inj (by
                rw [← List.getElem?_eq_getElem (by
                  dsimp only [ow] at hk_nat har_k; rw [← hk_nat]; exact har_k),
                  ← List.getElem?_eq_getElem har_k]
                dsimp only [ow] at hk_nat; rw [hk_nat])
            bve_steps! <;> first
              | exact ihj (_, j + 1#32, PUnit.unit) m_mk (by bv_omega) ⟨by bv_omega, rfl⟩
              | exact ihk (k + 1#32, PUnit.unit) m_mk (by bv_omega) ⟨by bv_omega, rfl⟩
              | contradiction
          · exact ihj (_, j + 1#32, PUnit.unit) m_mk (by bv_omega) ⟨by bv_omega, rfl⟩
      all_goals
        bve_steps!
        exact try_bce_cleanup_wp Γ Q X c F0 F_cur s R hdw mcnt hmcnt_le lm_mk tmp_mk
          hlml_mk htmpl_mk htmp_bd hlm_cov _ m_mk hm_mk hQ
  clear hJ_mk
  unfold FullBveBceWeakOk at hcr_ok
  bve_steps
  · have hbin_cr : (cr &&& 0x80000000#32) ≠ 0#32 := hc
    rw [ite_eq_left hbin_cr] at hcr_ok
    have hl1_mv : ((cr &&& 0x7FFFFFFF#32) ^^^ 1#32).toNat < 2 * c.max_vars :=
      bv32_xor_1_lt hcr_ok
    have hlm_idx : (BitVec.setWidth 64 ((cr &&& 0x7FFFFFFF#32) ^^^ 1#32)).toNat <
        s.core.lit_mark.length := by rw [bv_c0_zext32_64, hlml]; exact hl1_mv
    have htmp_idx : (BitVec.setWidth 64 (0#32 : BitVec 32)).toNat < s.core.tmp.length := by
      rw [bv_c0_zext32_64, htmpl]; bv_omega
    bve_steps!
    have hcov0 : ∀ l < 2 * c.max_vars, (∀ r < 0, (s.core.tmp[r]?.getD 0#32).toNat ≠ l) →
        s.core.lit_mark[l]? = some 0#8 := fun l hl _ => by
      have h0 := hlmc l hl
      rw [List.getElem?_eq_getElem (by rw [hlml]; exact hl), Option.getD_some] at h0
      rw [List.getElem?_eq_getElem (by rw [hlml]; exact hl), h0]
    have hstep := bce_mark_step_lt (mcnt := 0) (i := 0) hcov0 (fun _ hk => by omega)
      (Nat.le_refl _) htmpl hlml (by omega) hcr_ok
    refine hAfterMark 1#32 _ ⟨by bv_omega,
      s.core.lit_mark.set ((cr &&& 0x7FFFFFFF#32) ^^^ 1#32).toNat 1#8,
      s.core.tmp.set 0 ((cr &&& 0x7FFFFFFF#32) ^^^ 1#32),
      by simp [hlml], by simp [htmpl], hstep.2.2.2.1, hstep.2.2.2.2, ?_⟩
    simp only [bv_c0_zext32_64] at *; assumption
  · have hcr_mask0 : (cr &&& 0x80000000#32) = 0#32 := hc
    have hnb_cr : ¬ (cr &&& 0x80000000#32) ≠ 0#32 := fun h => h hcr_mask0
    rw [ite_eq_right hnb_cr] at hcr_ok
    obtain ⟨hcr_ref, hcr_bd, hcr_lits⟩ := hcr_ok
    have hcr_nd' := hcr_nd hcr_mask0
    have hcr_bd_len : cr.toNat + 3 + fullArenaClauseSize s cr.toNat ≤ s.core.arena.length := by
      have := hcl.arena_len_le; omega
    have hsz_mv : fullArenaClauseSize s cr.toNat ≤ c.max_vars :=
      arena_lits_nodup_len_le hcr_bd_len hcr_lits hcr_nd'
    have hcr2_lt : (BitVec.setWidth 64 cr + 2).toNat < s.core.arena.length := by
      have := hcl.arena_len_le; rw [harl]; bv_omega
    have hcr2_nat : (BitVec.setWidth 64 cr + 2).toNat = cr.toNat + 2 := by bv_omega
    let sz := s.core.arena[(BitVec.setWidth 64 cr + 2).toNat]'hcr2_lt
    have hsz_eq : sz.toNat = fullArenaClauseSize s cr.toNat := by
      unfold fullArenaClauseSize fullArenaClauseSizeCore sz
      rw [← Option.getD_some (a := s.core.arena[(BitVec.setWidth 64 cr + 2).toNat]'hcr2_lt),
        ← List.getElem?_eq_getElem hcr2_lt, hcr2_nat]
    bve_steps!
    refine wp_loop_inv (ts := [i32, i32])
      (fun (mcnt, i, _) mi =>
        i.toNat ≤ sz.toNat ∧ mcnt.toNat ≤ i.toNat ∧
        ∃ lm_i tmp_i,
          lm_i.length = 2 * c.max_vars ∧ tmp_i.length = c.max_vars ∧
          (∀ r < mcnt.toNat, (tmp_i[r]?.getD 0#32).toNat < 2 * c.max_vars) ∧
          (∀ l < 2 * c.max_vars,
            (∀ r < mcnt.toNat, (tmp_i[r]?.getD 0#32).toNat ≠ l) → lm_i[l]? = some 0#8) ∧
          (FullMem c { s with core := { s.core with lit_mark := lm_i, tmp := tmp_i } } ⋆ R) mi)
      (fun (_, i, _) _ => sz.toNat - i.toNat)
      ?_ ?_
    · intro Ji hJi; bve_steps!
      exact hJi (0#32, 0#32, PUnit.unit) m ⟨Nat.zero_le _, Nat.le_refl _, s.core.lit_mark,
        s.core.tmp, hlml, htmpl, fun _ hk => by bv_omega, fun l hl _ => by
          have h0 := hlmc l hl
          rw [List.getElem?_eq_getElem (by rw [hlml]; exact hl), Option.getD_some] at h0
          rw [List.getElem?_eq_getElem (by rw [hlml]; exact hl), h0], hm⟩
    · rintro Ji ⟨mcnt, i, ⟨⟩⟩ mi
        ⟨hi_le, hm_le, lm_i, tmp_i, hlml_i, htmpl_i, htmp_bd, hlm_cov, hm_i⟩ ih_mk
      bve_steps
      · have hi_lt : i.toNat < sz.toNat := by
          have hidx_eq : (cr.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = cr.toNat + 2 := by
            bv_omega
          have hc' : i.toNat < (s.core.arena[(cr.toNat +
              BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]?.getD 0#32).toNat := by
            rw [List.getElem?_eq_getElem (by rw [hidx_eq]; omega), Option.getD_some]
            exact hc
          rw [hidx_eq] at hc'
          rw [hsz_eq]; exact hc'
        have har_nat : (BitVec.setWidth 64 cr + 3 + BitVec.setWidth 64 i).toNat =
            cr.toNat + 3 + i.toNat := by bv_omega
        have har_idx : (BitVec.setWidth 64 cr + 3 + BitVec.setWidth 64 i).toNat <
            s.core.arena.length := by rw [har_nat]; omega
        let l := s.core.arena[(BitVec.setWidth 64 cr + 3 + BitVec.setWidth 64 i).toNat]'har_idx
        have hl_mv : l.toNat < 2 * c.max_vars := by
          apply hcr_lits
          unfold fullArenaClauseLits
          rw [mem_fullArenaClauseLitsCore_iff hcr_bd_len]
          refine ⟨i.toNat, by unfold fullArenaClauseSize at hsz_eq; omega, ?_⟩
          simp only [l, har_nat]
        have hstep := bce_mark_step_lt (mcnt := mcnt.toNat) (i := i.toNat) hlm_cov htmp_bd
          hm_le htmpl_i hlml_i (by omega) hl_mv
        have hlm_idx : (BitVec.setWidth 64 (l ^^^ 1#32)).toNat < lm_i.length := by
          rw [bv_c0_zext32_64]; exact hstep.2.1
        have htmp_idx : (BitVec.setWidth 64 mcnt).toNat < tmp_i.length := by
          rw [bv_c0_zext32_64]; exact hstep.1
        bve_steps!
        · refine ih_mk (mcnt + 1#32, i + 1#32, PUnit.unit) _ (by bv_omega)
            ⟨by bv_omega, by rw [show (mcnt + 1#32).toNat = mcnt.toNat + 1 from by bv_omega,
                show (i + 1#32).toNat = i.toNat + 1 from by bv_omega]; exact hstep.2.2.1,
              lm_i.set (l ^^^ 1#32).toNat 1#8, tmp_i.set mcnt.toNat (l ^^^ 1#32),
              by simp [hlml_i], by simp [htmpl_i],
              by rw [show (mcnt + 1#32).toNat = mcnt.toNat + 1 from by bv_omega]
                 exact hstep.2.2.2.1,
              by rw [show (mcnt + 1#32).toNat = mcnt.toNat + 1 from by bv_omega]
                 exact hstep.2.2.2.2,
              ?_⟩
          exact (by
            first
            | assumption
            | have hm_z : (FullMem c { s with core := { s.core with
                  lit_mark := lm_i.set (BitVec.setWidth 64 (l ^^^ 1#32)).toNat 1#8
                  tmp := tmp_i.set (BitVec.setWidth 64 mcnt).toNat (l ^^^ 1#32) } } ⋆ R) _ := by
                assumption
              simp only [bv_c0_zext32_64] at hm_z; exact hm_z)
        · exact ih_mk (mcnt, i + 1#32, PUnit.unit) mi (by bv_omega)
            ⟨by bv_omega, by bv_omega, lm_i, tmp_i, hlml_i, htmpl_i, htmp_bd, hlm_cov, hm_i⟩
      · have hi_eq : i.toNat = sz.toNat := by
          have hidx_eq : (cr.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = cr.toNat + 2 := by
            bv_omega
          have hc' : ¬ i.toNat < (s.core.arena[(cr.toNat +
              BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]?.getD 0#32).toNat := by
            rw [List.getElem?_eq_getElem (by rw [hidx_eq]; omega), Option.getD_some]
            exact hc
          rw [hidx_eq] at hc'
          unfold fullArenaClauseSize fullArenaClauseSizeCore at hsz_eq
          rw [← hsz_eq] at hc'; bv_omega
        rw [hi_eq] at hm_le
        exact hAfterMark mcnt mi
          ⟨by omega, lm_i, tmp_i, hlml_i, htmpl_i, htmp_bd, hlm_cov, hm_i⟩

end

end LeanQbe.T.Examples.Kissat.Full
