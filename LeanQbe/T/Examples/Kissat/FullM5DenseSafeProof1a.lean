module

public import LeanQbe.T.Examples.Kissat.FullM5DenseSafe
public import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.Examples.Kissat.FullBvaFwdSpec
import LeanQbe.T.Examples.Kissat.FullBvaFwdLemmas4
import LeanQbe.T.Logic.C0HeadStep

/-!
# Kissat M5 Dense-Safe Proofs — Part 1a (`full_fwd_check_cl_m5`)

Proves `full_fwd_check_cl_m5_wp` against canonical `Full.fullFwdCheckClSpec` (`RC-02`):
1. Short-circuits immediately (`return true`) when `h->oom != 0ULL` on entry.
2. When strengthening a clause (`drop != 0xFFFFFFFFu`) down to `nsz == 2`, calls
   `full_add_bin(h, l0, l1)` **BEFORE** unwatching or `PH_GARB`-marking `cref`, aborting cleanly
   with `h->oom = 1ULL; return true;` on `br == 2ULL || h->oom != 0ULL` so `cref` is never
   dropped on OOM and `return false` stays strictly reserved for `F0.Unsat`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullM5DenseSafe

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullBvaFwdHelpers
open Kraken.Bedrock2.Test
open scoped FullArenaTactics FullBvaFwdTactics

/-! ## 1. Local Helpers (`j`/`p`/`l`-block search & dense-invariant preservation) -/

private theorem fullDenseInvW_with_oom {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) (oom' : BitVec 64) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with oom := oom' } } :=
  ⟨⟨{ h.1.core_ok with vals_len := h.1.core_ok.vals_len }, h.1.scratch_ok⟩,
    { h.2.1 with
      arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
      watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
    h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

private def m5FwdLdTbl (tbl : Val i64) (lit : Val i32) (k : Val i8 → Expr Val Cont [.bool]) :
    Expr Val Cont [.bool] :=
  fwdZext64 (Arg.var lit) fun p1 => fwdOp64 (.add i64) (Arg.var tbl) (Arg.var p1) fun p2 =>
  Expr.load i8 (Arg.var p2) k

private def m5FwdByteCmp0 (ext : OpCode [i8] [i32]) (op : CmpOp) (v : Val i8)
    (k : Val .bool → Expr Val Cont [.bool]) : Expr Val Cont [.bool] :=
  Expr.let_ { sig := [i32], code := OpCode.trunc 32 8, args := (Arg.imm 0, ()) } fun z =>
  Expr.let_ { sig := [i8], code := ext, args := (Arg.var v, ()) } fun a =>
  Expr.let_ { sig := [i8], code := ext, args := (Arg.var z.fst, ()) } fun b =>
  fwdCmp32 op (Arg.var a.fst) (Arg.var b.fst) k

private def m5FwdLmNe0 (tbl : Val i64) (lit : Val i32) (k : Val .bool → Expr Val Cont [.bool]) :
    Expr Val Cont [.bool] :=
  m5FwdLdTbl tbl lit fun ld => m5FwdByteCmp0 (OpCode.zext 8 32) .ne ld k

private def m5FwdCheckJLoopExpr (pAr pLm pVals : Val i64) (cr dsz : Val i32)
    (Jjx : Cont [i32, i32, i32]) : Expr Val Cont [.bool] :=
  Expr.group (fun Js_5 => Blocks.cons (fun (p : Tup Val [i32, i32]) =>
    fwdCmp32 .ult (Arg.var p.snd.fst) (Arg.var dsz) fun c =>
    Expr.jnz (Arg.var c)
      (fwdArIdx3 cr p.snd.fst fun p67 => fwdLd32 pAr p67 fun ld =>
       Expr.group (fun _ => Blocks.cons (fun (p70 : Tup Val [i32, i32]) =>
         Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                     args := (Arg.var p.snd.fst, Arg.imm 1, ()) } fun pn =>
         Expr.jump Js_5.fst (Arg.var p70.snd.fst, Arg.var pn.fst, ())) Blocks.nil)
       fun Js_6 =>
       m5FwdLdTbl pLm ld fun lm0 => m5FwdByteCmp0 (OpCode.zext 8 32) .eq lm0 fun c0 =>
       Expr.jnz (Arg.var c0)
         (m5FwdLdTbl pVals ld fun v0 => m5FwdByteCmp0 (OpCode.sext 8 32) .sge v0 fun cv =>
          Expr.jnz (Arg.var cv)
            (Expr.let_ { sig := [i32, i32], code := OpCode.xor i32,
                         args := (Arg.var ld, Arg.imm 1, ()) } fun dl1 =>
             m5FwdLdTbl pLm dl1.fst fun lm1 => m5FwdByteCmp0 (OpCode.zext 8 32) .ne lm1 fun c1 =>
             Expr.jnz (Arg.var c1)
               (fwdCmp32 .eq (Arg.var p.fst) (Arg.imm 4294967295) fun cc =>
                Expr.jnz (Arg.var cc)
                  (Expr.let_ { sig := [i32, i32], code := OpCode.xor i32,
                               args := (Arg.var ld, Arg.imm 1, ()) } fun dl1b =>
                   Expr.jump Js_6.fst (Arg.imm 0, Arg.var dl1b.fst, ()))
                  (Expr.jump Jjx (Arg.imm 2, Arg.var p.fst, Arg.var p.snd.fst, ())))
               (Expr.jump Jjx (Arg.imm 2, Arg.var p.fst, Arg.var p.snd.fst, ())))
            (Expr.jump Js_6.fst (Arg.imm 0, Arg.var p.fst, ())))
         (Expr.jump Js_6.fst (Arg.imm 0, Arg.var p.fst, ())))
      (Expr.jump Jjx (Arg.imm 0, Arg.var p.fst, Arg.var p.snd.fst, ()))) Blocks.nil)
  fun Js_5 => Expr.jump Js_5.fst (Arg.imm 4294967295, Arg.imm 0, ())

private def m5FwdCheckPExpr (pAr pLm pVals pWstk : Val i64) (sz l : Val i32) (off end64 : Val i64)
    (cref : Val i32) (sub0 : Val .bool) (drop0 : Val i32) (Js : Cont [.bool, i32, i64]) :
    Expr Val Cont [.bool] :=
  Expr.group (fun Js_4 => Blocks.cons (fun (p50 : Tup Val [i64]) =>
    fwdCmp64 .ult (Arg.var p50.fst) (Arg.var end64) fun c1 =>
    Expr.jnz (Arg.var c1)
      (fwdOp64 (.sub i64) (Arg.var p50.fst) (Arg.var off) fun df =>
       fwdCmp64 .ult (Arg.var df) (Arg.imm 128) fun c2 =>
       Expr.jnz (Arg.var c2)
         (fwdLd32 pWstk p50.fst fun w0 =>
          fwdOp64 (.add i64) (Arg.var p50.fst) (Arg.imm 1) fun p1 =>
          Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                      args := (Arg.var w0, Arg.imm 2147483648, ()) } fun f0 =>
          fwdCmp32 .ne (Arg.var f0.fst) (Arg.imm 0) fun fb =>
          Expr.jnz (Arg.var fb)
            (Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                         args := (Arg.var w0, Arg.imm 2147483647, ()) } fun ot =>
             m5FwdLmNe0 pLm ot.fst fun co =>
             Expr.jnz (Arg.var co)
               (Expr.jump Js (Arg.imm true, Arg.var drop0, Arg.var p1, ()))
               (Expr.let_ { sig := [i32, i32], code := OpCode.xor i32,
                            args := (Arg.var ot.fst, Arg.imm 1, ()) } fun x1 =>
                fwdCmp32 .ne (Arg.var x1.fst) (Arg.var l) fun cne =>
                Expr.jnz (Arg.var cne)
                  (Expr.let_ { sig := [i32, i32], code := OpCode.xor i32,
                               args := (Arg.var ot.fst, Arg.imm 1, ()) } fun x2 =>
                   m5FwdLmNe0 pLm x2.fst fun cx =>
                   Expr.jnz (Arg.var cx)
                     (Expr.let_ { sig := [i32, i32], code := OpCode.xor i32,
                                  args := (Arg.var ot.fst, Arg.imm 1, ()) } fun x3 =>
                      Expr.jump Js (Arg.var sub0, Arg.var x3.fst, Arg.var p1, ()))
                     (Expr.jump Js_4.fst (Arg.var p1, ())))
                  (Expr.jump Js_4.fst (Arg.var p1, ()))))
            (fwdCmp64 .uge (Arg.var p1) (Arg.var end64) fun ce =>
             Expr.jnz (Arg.var ce)
               (Expr.jump Js (Arg.var sub0, Arg.var drop0, Arg.var p1, ()))
               (fwdLd32 pWstk p1 fun cr =>
                fwdOp64 (.add i64) (Arg.var p1) (Arg.imm 1) fun p2 =>
                fwdCmp32 .eq (Arg.var cr) (Arg.var cref) fun ceq =>
                Expr.jnz (Arg.var ceq) (Expr.jump Js_4.fst (Arg.var p2, ()))
                  (fwdZext64 (Arg.var cr) fun cr64 => fwdLd32 pAr cr64 fun chdr =>
                   Expr.let_ { sig := [i32, i32], code := OpCode.or i32,
                               args := (Arg.imm 524288, Arg.imm 4194304, ()) } fun mk =>
                   Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                               args := (Arg.var chdr, Arg.var mk.fst, ()) } fun ma =>
                   fwdCmp32 .ne (Arg.var ma.fst) (Arg.imm 0) fun cgr =>
                   Expr.jnz (Arg.var cgr) (Expr.jump Js_4.fst (Arg.var p2, ()))
                     (fwdArOff cr 2 fun cr2 => fwdLd32 pAr cr2 fun dsz =>
                      fwdCmp32 .ugt (Arg.var dsz) (Arg.var sz) fun cgt =>
                      Expr.jnz (Arg.var cgt) (Expr.jump Js_4.fst (Arg.var p2, ()))
                        (Expr.group (fun _ => Blocks.cons
                           (fun (pj : Tup Val [i32, i32, i32]) =>
                             Expr.group (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
                               fwdCmp32 .eq (Arg.var pj.fst) (Arg.imm 0) fun m0b =>
                               Expr.jnz (Arg.var m0b)
                                 (fwdCmp32 .ne (Arg.var pj.snd.fst) (Arg.imm 4294967295) fun cnb =>
                                  Expr.jnz (Arg.var cnb)
                                    (Expr.jump Js (Arg.var sub0, Arg.var pj.snd.fst,
                                      Arg.var p2, ()))
                                    (Expr.jump Js_4.fst (Arg.var p2, ())))
                                 (Expr.jump Js_4.fst (Arg.var p2, ()))) Blocks.nil)
                             fun Js_6 => fwdCmp32 .eq (Arg.var pj.fst) (Arg.imm 0) fun m0a =>
                             Expr.jnz (Arg.var m0a)
                               (fwdCmp32 .eq (Arg.var pj.snd.fst) (Arg.imm 4294967295) fun ceb =>
                                Expr.jnz (Arg.var ceb)
                                  (Expr.jump Js (Arg.imm true, Arg.var drop0, Arg.var p2, ()))
                                  (Expr.jump Js_6.fst ()))
                               (Expr.jump Js_6.fst ())) Blocks.nil)
                         fun Js_5 => m5FwdCheckJLoopExpr pAr pLm pVals cr dsz Js_5.fst))))))
         (Expr.jump Js (Arg.var sub0, Arg.var drop0, Arg.var p50.fst, ())))
      (Expr.jump Js (Arg.var sub0, Arg.var drop0, Arg.var p50.fst, ()))) Blocks.nil)
  fun Js_4 => Expr.jump Js_4.fst (Arg.var off, ())

private theorem m5_fwd_check_j_wp {Γ : Env} {Q : Post [.bool]} {X : XPost} {c : FullCfg}
    {F0 : CNF Nat} {F_cur : List (List Nat)} {s st_m : FullState} {R : Mem 64 → Prop}
    {C : List Nat} {cr dsz : BitVec 32} {ml : Mem 64} {Jjx : Cont [i32, i32, i32]}
    (hstm : st_m = { s with core := { s.core with lit_mark := st_m.core.lit_mark } })
    (hw : FullWitnessInv c F0 F_cur s.core) (hl0 : s.core.cur_level = 0)
    (hlen : s.LengthsOk c) (hlm_m : st_m.core.lit_mark.length = 2 * c.max_vars)
    (hlm_full : ∀ x < 2 * c.max_vars, st_m.core.lit_mark[x]?.getD 0#8 ≠ 0#8 ↔ x ∈ C)
    (hC_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause C))
    (hcr_ref : cr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hng_cr : fullArenaClauseGarbCore s.core cr.toNat = false)
    (hdsz_eq : dsz.toNat = fullArenaClauseSizeCore s.core cr.toNat)
    (hnd_D : ((fullArenaClauseLitsCore s.core cr.toNat).map (· / 2)).Nodup)
    (hml : (FullMem c st_m ⋆ R) ml)
    (hJjx : ∀ miss cand j mlj,
      (miss = 0#32 → (cand = 0xFFFFFFFF#32 → (cnfOfClauses F_cur).EntailsClause
          (cnfClause (fullArenaClauseLitsCore s.core cr.toNat))) ∧
        (cand ≠ 0xFFFFFFFF#32 → FwdDropOk F_cur C cand)) →
      (FullMem c st_m ⋆ R) mlj → Jjx (miss, cand, j, ()) mlj) :
    wp Γ Q X (m5FwdCheckJLoopExpr c.pArena c.pLitMark c.pVals cr dsz Jjx) ml := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hlen.core_ok.cur_vars_le
  have hcr_wf := hw.arena.refs_wf cr.toNat hcr_ref
  let D := fullArenaClauseLitsCore s.core cr.toNat
  have hD_lt := hw.arena.lits_lt cr.toNat hcr_ref hng_cr
  have hD_ent := hw.arena.entails cr.toNat hcr_ref hng_cr
  have hcr_sz : cr.toNat + 3 + dsz.toNat ≤ s.core.arena.length := by
    have := hcr_wf.2.2.1; have := hcr_wf.2.2.2.1; have := hlen.core_ok.arena_len_le
    have := hlen.core_ok.arena_len_arr; omega
  have hD_len : D.length = dsz.toNat := by
    rw [fullArenaClauseLitsCore_length (by rw [← hdsz_eq]; exact hcr_sz), hdsz_eq]
  have har_m : st_m.core.arena = s.core.arena := by rw [hstm]
  have hvals_m : st_m.core.vals = s.core.vals := by rw [hstm]
  have har_m_len : st_m.core.arena.length = c.arena_cap := by
    rw [har_m]; exact hlen.core_ok.arena_len_arr
  have hvals_m_len : st_m.core.vals.length = 2 * c.max_vars := by
    rw [hvals_m]; exact hlen.core_ok.vals_len
  unfold m5FwdCheckJLoopExpr fwdArIdx3 fwdArOff fwdLd32 m5FwdLdTbl m5FwdByteCmp0 fwdZext64 fwdOp64
    fwdCmp32
  dsimp only
  refine wp_loop_inv
    (fun (cand, j, ()) mlj => j.toNat ≤ dsz.toNat ∧ (cand ≠ 0xFFFFFFFF#32 →
        cand.toNat ∈ C ∧ (cand.toNat ^^^ 1) ∈ D) ∧
      (∀ t < j.toNat, let dl := D[t]?.getD 0
        dl ∈ C ∨ (cnfOfClauses F_cur).EntailsClause (cnfClause [dl ^^^ 1]) ∨
          (cand ≠ 0xFFFFFFFF#32 ∧ dl = cand.toNat ^^^ 1)) ∧ (FullMem c st_m ⋆ R) mlj)
    (fun (_, j, _) _ => dsz.toNat - j.toNat)
    (fun J5 hJ5 => by
      bf_steps; exact hJ5 (0xFFFFFFFF#32, 0#32, ()) ml
        ⟨by rw [show (0#32 : BitVec 32).toNat = 0 from rfl]; omega,
         fun h => absurd rfl h, fun _ ht => by
           rw [show (0#32 : BitVec 32).toNat = 0 from rfl] at ht; omega, hml⟩)
    (fun J5 (cand, j, ()) mlj ⟨hj_le, hck, hprev, hmlj⟩ ihj => ?_)
  bf_fast
  · have hj_lt : j.toNat < dsz.toNat := by c0_bound
    have hcrj_n : (BitVec.setWidth 64 cr + 3#64 + BitVec.setWidth 64 j).toNat =
        cr.toNat + 3 + j.toNat := by c0_bound
    have hcrj_lt : (BitVec.setWidth 64 cr + 3#64 + BitVec.setWidth 64 j).toNat <
        st_m.core.arena.length := by
      rw [hcrj_n, har_m_len]; have := hlen.core_ok.arena_len_le; omega
    have hdl_eq : st_m.core.arena[(BitVec.setWidth 64 cr + 3#64 +
        BitVec.setWidth 64 j).toNat]'hcrj_lt =
        s.core.arena[cr.toNat + 3 + j.toNat]'(by omega) := Option.some.inj
      (by rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, har_m, hcrj_n])
    have hDj : D[j.toNat]? = some (s.core.arena[cr.toNat + 3 + j.toNat]'(by omega)).toNat :=
      fullArenaClauseLitsCore_getElem (by omega) (by omega)
    have hdl_mem := List.mem_of_getElem? hDj; have hdl_lt := hD_lt _ hdl_mem
    have hdl_lm : (BitVec.setWidth 64 (st_m.core.arena[(BitVec.setWidth 64 cr + 3#64 +
        BitVec.setWidth 64 j).toNat]'hcrj_lt)).toNat < st_m.core.lit_mark.length := by
      rw [hdl_eq, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hlm_m]; omega
    have hdl_vals : (BitVec.setWidth 64 (st_m.core.arena[(BitVec.setWidth 64 cr + 3#64 +
        BitVec.setWidth 64 j).toNat]'hcrj_lt)).toNat < st_m.core.vals.length := by
      rw [hdl_eq, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hvals_m_len]; omega
    have hdl1_lm : (BitVec.setWidth 64 ((st_m.core.arena[(BitVec.setWidth 64 cr + 3#64 +
        BitVec.setWidth 64 j).toNat]'hcrj_lt) ^^^ 1#32)).toNat < st_m.core.lit_mark.length := by
      rw [hdl_eq, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega),
        FullBvaFwdTactics.bv32_xor1_toNat, hlm_m]
      exact Nat.lt_of_lt_of_le (litNeg_lt_two_mul hdl_lt) (by omega)
    have hj1_n : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
    have hdl64 : (BitVec.setWidth 64 (st_m.core.arena[(BitVec.setWidth 64 cr + 3#64 +
        BitVec.setWidth 64 j).toNat]'hcrj_lt)).toNat =
        (s.core.arena[cr.toNat + 3 + j.toNat]'(by omega)).toNat := by
      rw [hdl_eq, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
    bf_step
    refine wp_join_group
      (fun (p70 : Tup Val [i32, i32]) mlj => let cand' := p70.snd.fst
        (cand' ≠ 0xFFFFFFFF#32 → cand'.toNat ∈ C ∧ (cand'.toNat ^^^ 1) ∈ D) ∧
        (∀ t < j.toNat + 1, let dl := D[t]?.getD 0
          dl ∈ C ∨ (cnfOfClauses F_cur).EntailsClause (cnfClause [dl ^^^ 1]) ∨
            (cand' ≠ 0xFFFFFFFF#32 ∧ dl = cand'.toNat ^^^ 1)) ∧ (FullMem c st_m ⋆ R) mlj)
      (fun _ (p70 : Tup Val [i32, i32]) mlj ⟨hck', hprev', hmlj⟩ => by
        bf_fast; exact ihj (p70.snd.fst, j + 1#32, ()) mlj (by dsimp only; rw [hj1_n]; omega)
          ⟨by rw [hj1_n]; omega, hck', fun t ht => by rw [hj1_n] at ht; exact hprev' t ht, hmlj⟩)
      (fun J6 hJ6 => ?_)
    have hidx_m : (cr.toNat + BitVec.toNat (3 : BitVec 64) + j.toNat) % 2 ^ 64 =
        cr.toNat + 3 + j.toNat := by c0_bound
    have hdl_m : st_m.core.arena[(cr.toNat + BitVec.toNat (3 : BitVec 64) +
        j.toNat) % 2 ^ 64]'(by rw [har_m_len]; c0_bound) =
        s.core.arena[cr.toNat + 3 + j.toNat]'(by omega) := Option.some.inj
      (by rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, har_m, hidx_m])
    have hdl_s : st_m.core.arena[(BitVec.setWidth 64 cr + (3 : BitVec 64) +
        BitVec.setWidth 64 j).toNat]'(by rw [har_m_len]; c0_bound) =
        s.core.arena[cr.toNat + 3 + j.toNat]'(by omega) := hdl_eq
    bf_fast
    · rename_i h_lm1; have hcand_old : cand = 0xFFFFFFFF#32 := by assumption
      have hnz : ¬ BitVec.setWidth 32 (st_m.core.lit_mark[(s.core.arena[cr.toNat + 3 +
          j.toNat]'(by omega)).toNat ^^^ 1]'(by
            have := litNeg_lt_two_mul hdl_lt; rw [hlm_m]; omega)) = 0#32 := by
        simpa only [hdl_m] using h_lm1
      have hdl1_memC : ((s.core.arena[cr.toNat + 3 + j.toNat]'(by omega)) ^^^ 1#32).toNat ∈ C := by
        rw [FullBvaFwdTactics.bv32_xor1_toNat]
        apply (hlm_full _ (by have := litNeg_lt_two_mul hdl_lt; omega)).mp
        rw [List.getElem?_eq_getElem (by have := litNeg_lt_two_mul hdl_lt; rw [hlm_m]; omega),
          Option.getD_some]
        intro h0; rw [h0] at hnz; exact hnz rfl
      have hdl1_neg : ((s.core.arena[cr.toNat + 3 + j.toNat]'(by omega)) ^^^ 1#32).toNat ^^^ 1 =
          (s.core.arena[cr.toNat + 3 + j.toNat]'(by omega)).toNat := by
        rw [FullBvaFwdTactics.bv32_xor1_toNat]; exact litNeg_litNeg _
      refine hJ6 (0#32, _, ()) mlj ⟨fun _ => ?_, fun t ht => ?_, hmlj⟩
      · dsimp only; rw [hdl_s, show (1 : BitVec 32) = 1#32 from rfl, hdl1_neg]
        exact ⟨hdl1_memC, hdl_mem⟩
      · try dsimp only; rw [hdl_s]
        rw [show (s.core.arena[cr.toNat + 3 + j.toNat]'(by omega) ^^^ (1 : BitVec 32)).toNat ^^^ 1 =
            (s.core.arena[cr.toNat + 3 + j.toNat]'(by omega)).toNat from by
          rw [show (1 : BitVec 32) = 1#32 from rfl, FullBvaFwdTactics.bv32_xor1_toNat]
          exact litNeg_litNeg _]
        by_cases htj : t = j.toNat
        · subst htj; rw [hDj, Option.getD_some]
          refine Or.inr (Or.inr ⟨?_, rfl⟩)
          intro hff; have hlt2 := litNeg_lt_two_mul hdl_lt
          rw [show (1 : BitVec 32) = 1#32 from rfl] at hff
          rw [← FullBvaFwdTactics.bv32_xor1_toNat, hff] at hlt2
          have : (0xFFFFFFFF#32 : BitVec 32).toNat = 4294967295 := rfl; omega
        · rcases hprev t (by omega) with h1 | h2 | ⟨hne, _⟩
          · exact Or.inl h1
          · exact Or.inr (Or.inl h2)
          · exact absurd hcand_old hne
    · exact hJjx 2#32 cand j mlj (fun h => by cases h) hmlj
    · exact hJjx 2#32 cand j mlj (fun h => by cases h) hmlj
    · have hvs_len := hlen.core_ok.vals_len
      have hve' : st_m.core.vals[(s.core.arena[cr.toNat + 3 + j.toNat]'(by omega)).toNat]'(by
          rw [hvals_m_len]; omega) =
          s.core.vals[(s.core.arena[cr.toNat + 3 + j.toNat]'(by omega)).toNat]'(by omega) :=
        Option.some.inj (by rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, hvals_m])
      have hv0_sle : (0#32 : BitVec 32).sle (BitVec.signExtend 32 (s.core.vals[
          (s.core.arena[cr.toNat + 3 + j.toNat]'(by omega)).toNat]'(by omega))) = false := by
        simpa only [hdl_m, hve'] using hc
      refine hJ6 (0#32, cand, ()) mlj ⟨hck, fun t ht => ?_, hmlj⟩
      by_cases htj : t = j.toNat
      · subst htj; dsimp only; rw [hDj, Option.getD_some]; refine Or.inr (Or.inl
          (fwd_entails_false_lit hw hl0 hdl_lt (by
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hv0_sle]; decide)))
      · exact hprev t (by omega)
    · have hlm0_z : ¬ BitVec.setWidth 32 (st_m.core.lit_mark[(s.core.arena[cr.toNat + 3 +
          j.toNat]'(by omega)).toNat]'(by rw [hlm_m]; omega)) = 0#32 := by
        simpa only [hdl_m] using hc
      refine hJ6 (0#32, cand, ()) mlj ⟨hck, fun t ht => ?_, hmlj⟩
      by_cases htj : t = j.toNat
      · subst htj; dsimp only; rw [hDj, Option.getD_some]; refine Or.inl ((hlm_full _ (by omega)).mp
          (by rw [List.getElem?_eq_getElem (by rw [hlm_m]; omega), Option.getD_some]
              intro h0; rw [h0] at hlm0_z; exact hlm0_z rfl))
      · exact hprev t (by omega)
  · have hj_eq : j.toNat = dsz.toNat := by c0_bound
    refine hJjx 0#32 cand j mlj (fun _ => ⟨fun _ => hD_ent, fun hne => ?_⟩) hmlj
    have ⟨hcC, hcD⟩ := hck hne
    refine fwd_drop_of_clause hC_ent hD_ent hnd_D hcC hcD fun t ht => ?_
    rw [hD_len, ← hj_eq] at ht; rcases hprev t ht with h1 | h2 | ⟨_, h3⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr h3)

private theorem m5_fwd_check_p_wp {Γ : Env} {Q : Post [.bool]} {X : XPost} {c : FullCfg}
    {F0 : CNF Nat} {F_cur : List (List Nat)} {s st_m : FullState} {R : Mem 64 → Prop}
    {C : List Nat} {cref sz l drop0 : BitVec 32} {off end64 : BitVec 64} {sub0 : Bool}
    {ml : Mem 64} {Js : Cont [.bool, i32, i64]}
    (hstm : st_m = { s with core := { s.core with lit_mark := st_m.core.lit_mark } })
    (hw : FullWitnessInv c F0 F_cur s.core) (hl0 : s.core.cur_level = 0)
    (hlen : s.LengthsOk c) (hlm_m : st_m.core.lit_mark.length = 2 * c.max_vars)
    (hlm_full : ∀ x < 2 * c.max_vars, st_m.core.lit_mark[x]?.getD 0#8 ≠ 0#8 ↔ x ∈ C)
    (hC_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause C))
    (hnodup : FullArenaVarsNodup s)
    (hl_mem : l.toNat ∈ C) (hoff_eq : off.toNat = fullWatchOffCore s.core l.toNat)
    (hend_n : end64.toNat = off.toNat + fullWatchSizeCore s.core l.toNat)
    (hbd_l : off.toNat + fullWatchSizeCore s.core l.toNat ≤ c.wcap)
    (hslice_l : DenseWatchSliceOk F_cur s.core l.toNat off.toNat (fullWatchSizeCore s.core l.toNat))
    (hdrop0 : FwdDropOk F_cur C drop0) (hml : (FullMem c st_m ⋆ R) ml)
    (hJs : ∀ (subx : Bool) (dropx : BitVec 32) (px : BitVec 64) mlx,
      FwdDropOk F_cur C dropx → (FullMem c st_m ⋆ R) mlx → Js (subx, dropx, px, ()) mlx) :
    wp Γ Q X
      (m5FwdCheckPExpr c.pArena c.pLitMark c.pVals c.pWstk sz l off end64 cref sub0 drop0 Js)
      ml := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx; have hcv_le := hlen.core_ok.cur_vars_le
  have hws_m : st_m.core.wstk = s.core.wstk := by rw [hstm]
  have har_m : st_m.core.arena = s.core.arena := by rw [hstm]
  have har_m_len : st_m.core.arena.length = c.arena_cap := by
    rw [har_m]; exact hlen.core_ok.arena_len_arr
  unfold m5FwdCheckPExpr m5FwdLmNe0 m5FwdByteCmp0 m5FwdLdTbl fwdArOff fwdLd32 fwdZext64 fwdOp64
    fwdCmp32 fwdCmp64
  dsimp only
  refine wp_loop_inv
    (fun (p, ()) mlp => off.toNat ≤ p.toNat ∧ p.toNat ≤ end64.toNat ∧
      DenseWatchSliceOk F_cur s.core l.toNat p.toNat (end64.toNat - p.toNat) ∧
      (FullMem c st_m ⋆ R) mlp)
    (fun (p, _) _ => end64.toNat - p.toNat)
    (fun J4 hJ4 => by
      bf_steps; exact hJ4 (off, ()) ml ⟨Nat.le_refl _, by omega,
        by rw [show end64.toNat - off.toNat = fullWatchSizeCore s.core l.toNat by omega]
           exact hslice_l, hml⟩)
    (fun J4 (p, ()) mlp ⟨hp_ge, hp_le, hremp, hmlp⟩ ihp => ?_)
  bf_steps
  · have hp_lt : p.toNat < end64.toNat := by c0_bound
    have hp_ws : p.toNat < s.core.wstk.length := by rw [hlen.core_ok.wstk_len_arr]; omega
    have hp_ws_m : p.toNat < st_m.core.wstk.length := by rw [hws_m]; exact hp_ws
    clear hc; bf_steps
    · have helem_w : st_m.core.wstk[p.toNat]'hp_ws_m =
          s.core.wstk[p.toNat]'hp_ws := Option.some.inj
        (by rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, hws_m])
      have hbin_flag : (s.core.wstk[p.toNat]'hp_ws &&& 0x80000000#32) ≠ 0#32 := by
        rw [← helem_w]; assumption
      have ⟨hot_lt, hent_ot, hrem_next⟩ := bva_slice_bin_info hremp (by omega) hp_ws hbin_flag
      have hot1_lm : (BitVec.setWidth 64 ((st_m.core.wstk[p.toNat]'(by
          rw [hws_m]; exact hp_ws) &&& 0x7FFFFFFF#32) ^^^ 1#32)).toNat <
          st_m.core.lit_mark.length := by
        rw [helem_w, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega),
          FullBvaFwdTactics.bv32_xor1_toNat, hlm_m]
        exact Nat.lt_of_lt_of_le (litNeg_lt_two_mul hot_lt) (by omega)
      have hot_lm : (BitVec.setWidth 64 (st_m.core.wstk[p.toNat]'(by
          rw [hws_m]; exact hp_ws) &&& 0x7FFFFFFF#32)).toNat < st_m.core.lit_mark.length := by
        rw [helem_w, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hlm_m]
        exact Nat.lt_of_lt_of_le hot_lt (by omega)
      have hp1_n : (p + 1#64).toNat = p.toNat + 1 := by c0_bound
      have go1 : J4 (p + 1#64, ()) mlp := ihp _ _ (by dsimp only; rw [hp1_n]; omega)
        ⟨by rw [hp1_n]; omega, by rw [hp1_n]; omega,
         by rw [hp1_n, show end64.toNat - (p.toNat + 1) = end64.toNat - p.toNat - 1 by omega]
            exact hrem_next, hmlp⟩
      have hot1_lm2 : ((st_m.core.wstk[p.toNat]'hp_ws_m &&& 0x7FFFFFFF#32) ^^^ 1#32).toNat <
          st_m.core.lit_mark.length := by
        rw [FullBvaFwdTactics.bv32_xor1_toNat, helem_w, hlm_m]
        have := litNeg_lt_two_mul hot_lt; omega
      clear hc; bf_steps
      all_goals first
        | exact hJs true drop0 (p + 1#64) mlp hdrop0 hmlp
        | exact go1
        | skip
      have hne_cne : ((st_m.core.wstk[p.toNat]'hp_ws_m &&& 0x7FFFFFFF#32) ^^^ 1#32) ≠ l := by
        assumption
      have hc_lm : ¬ BitVec.setWidth 32 (st_m.core.lit_mark[((st_m.core.wstk[p.toNat]'hp_ws_m
          &&& 0x7FFFFFFF#32) ^^^ 1#32).toNat]'hot1_lm2) = 0#32 := by assumption
      have hmem_ot1 : ((s.core.wstk[p.toNat]'hp_ws &&& 0x7FFFFFFF#32) ^^^ 1#32).toNat ∈ C := by
        rw [← helem_w]; apply (hlm_full _ (by rw [← hlm_m]; exact hot1_lm2)).mp
        rw [List.getElem?_eq_getElem hot1_lm2, Option.getD_some]
        intro h0; rw [h0] at hc_lm; exact hc_lm rfl
      have hne_ot1 : ((s.core.wstk[p.toNat]'hp_ws &&& 0x7FFFFFFF#32) ^^^ 1#32) ≠ l := by
        rw [← helem_w]; exact hne_cne
      exact hJs sub0 _ (p + 1#64) mlp
        (by rw [helem_w]; exact fwd_drop_of_bin hl_mem hC_ent hent_ot hne_ot1 hmem_ot1) hmlp
    · exact hJs sub0 drop0 (p + 1#64) mlp hdrop0 hmlp
    · have hp1_n : (p + 1#64).toNat = p.toNat + 1 := by c0_bound
      have hp1_lt : p.toNat + 1 < end64.toNat := by
        have : ¬ end64.toNat ≤ (p + 1#64).toNat := by c0_bound
        omega
      have hp1_ws : p.toNat + 1 < s.core.wstk.length := by rw [hlen.core_ok.wstk_len_arr]; omega
      have hp1_ws_m : (p + 1#64).toNat < st_m.core.wstk.length := by
        rw [hws_m, hp1_n, hlen.core_ok.wstk_len_arr]; omega
      have helem_w : st_m.core.wstk[p.toNat]'hp_ws_m = s.core.wstk[p.toNat]'hp_ws :=
        Option.some.inj (by rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, hws_m])
      have hocc_flag : (s.core.wstk[p.toNat]'hp_ws &&& 0x80000000#32) = 0#32 := by
        rw [← helem_w]; assumption
      have ⟨_, hcr_mem, hrem_next⟩ :=
        fwd_slice_occ_info hremp (by omega) hp_ws hp1_ws hocc_flag
      have hp2_n : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by c0_bound
      have hcr_eq : st_m.core.wstk[(p + 1#64).toNat]'(by rw [hws_m, hp1_n]; exact hp1_ws) =
          s.core.wstk[p.toNat + 1]'hp1_ws := Option.some.inj
        (by rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, hws_m, hp1_n])
      have hcr_ref : (st_m.core.wstk[(p + 1#64).toNat]'(by
          rw [hws_m, hp1_n]; exact hp1_ws)).toNat ∈ fullArenaClauseRefsCore s.core := by
        rw [hcr_eq]; exact hcr_mem
      have hcr_wf := hw.arena.refs_wf _ hcr_ref
      have hcr_ar : (BitVec.setWidth 64 (st_m.core.wstk[(p + 1#64).toNat]'(by
          rw [hws_m, hp1_n]; exact hp1_ws))).toNat < st_m.core.arena.length := by
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), har_m_len]
        have := hlen.core_ok.arena_len_le; omega
      have go2 : ∀ m2, (FullMem c st_m ⋆ R) m2 → J4 (p + 1#64 + 1#64, ()) m2 := fun m2 hm2 =>
        ihp _ _ (by dsimp only; rw [hp2_n]; omega) ⟨by rw [hp2_n]; omega,
          by rw [hp2_n]; omega,
          by rw [hp2_n, show end64.toNat - (p.toNat + 2) = end64.toNat - p.toNat - 2 by omega]
             exact hrem_next, hm2⟩
      clear hc; bf_steps; all_goals try exact go2 mlp hmlp
      have hcr_h0 : (st_m.core.arena[(BitVec.setWidth 64
          (st_m.core.wstk[(p + 1#64).toNat]'hp1_ws_m)).toNat]'hcr_ar &&&
          (524288#32 ||| 4194304#32)) = 0#32 := by assumption
      generalize hcr_v : st_m.core.wstk[(p + 1#64).toNat]'hp1_ws_m = cr
      have hcr_ref' : cr.toNat ∈ fullArenaClauseRefsCore s.core := by rw [← hcr_v]; exact hcr_ref
      have hcr_wf' := hw.arena.refs_wf _ hcr_ref'
      have := hcr_wf'.2.2.1; have := hcr_wf'.2.2.2.1
      have := hlen.core_ok.arena_len_le; have := hlen.core_ok.arena_len_arr
      have hng_cr : fullArenaClauseGarbCore s.core cr.toNat = false := by
        unfold fullArenaClauseGarbCore fullArenaHdrCore
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        have he : st_m.core.arena[(BitVec.setWidth 64
            (st_m.core.wstk[(p + 1#64).toNat]'hp1_ws_m)).toNat]'hcr_ar =
            s.core.arena[cr.toNat]'(by omega) :=
          Option.some.inj (by rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, har_m,
            BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hcr_v])
        rw [he] at hcr_h0; exact garb_false_of_and_garb_red_eq_zero hcr_h0
      have hcr2_n : (BitVec.setWidth 64 cr + 2#64).toNat = cr.toNat + 2 := by c0_bound
      have hcr2_lt : (BitVec.setWidth 64 cr + 2#64).toNat < st_m.core.arena.length := by
        rw [hcr2_n, har_m_len]; omega
      have hdsz_eq : (st_m.core.arena[(BitVec.setWidth 64 cr + 2#64).toNat]'hcr2_lt).toNat =
          fullArenaClauseSizeCore s.core cr.toNat := by
        unfold fullArenaClauseSizeCore
        have he : st_m.core.arena[(BitVec.setWidth 64 cr + 2#64).toNat]'hcr2_lt =
            s.core.arena[cr.toNat + 2]'(by omega) := Option.some.inj (by
          rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, har_m, hcr2_n])
        rw [he, List.getElem?_eq_getElem (by omega), Option.getD_some]
      bf_steps; all_goals try exact go2 mlp hmlp
      refine m5_fwd_check_j_wp hstm hw hl0 hlen hlm_m hlm_full hC_ent hcr_ref' hng_cr hdsz_eq
        (hnodup cr.toNat hcr_ref' hng_cr) hmlp fun miss cand _ mlj hdrop_cand hmlj => ?_
      bf_fast
      · exact hJs true drop0 (p + 1#64 + 1#64) mlj hdrop0 hmlj
      · exact hJs sub0 cand (p + 1#64 + 1#64) mlj
          ((hdrop_cand (by assumption)).2 (by assumption)) hmlj
      all_goals exact go2 mlj hmlj
  all_goals exact hJs sub0 drop0 p mlp hdrop0 hmlp

private def m5FwdLBlockExpr (pAr pLm pVals pWstk pWv : Val i64) (sz cref i3 : Val i32)
    (sub : Val .bool) (drop l : Val i32) (J3 : Cont [i32, .bool, i32]) : Expr Val Cont [.bool] :=
  fwdZext64 (Arg.var l) fun p36 =>
  Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1, ()) } fun p37 =>
  fwdOp64 (.shl i64) (Arg.var p36) (Arg.var p37.fst) fun p38 => fwdLd32 pWv p38 fun ld9 =>
  fwdZext64 (Arg.var ld9) fun p41 => fwdZext64 (Arg.var l) fun p42 =>
  Expr.let_ { sig := [i32], code := OpCode.sext 32 64, args := (Arg.imm 1, ()) } fun p43 =>
  fwdOp64 (.shl i64) (Arg.var p42) (Arg.var p43.fst) fun p44 =>
  fwdOp64 (.add i64) (Arg.var p44) (Arg.imm 1) fun p45 => fwdLd32 pWv p45 fun ld10 =>
  fwdZext64 (Arg.var ld10) fun p48 => fwdOp64 (.add i64) (Arg.var p41) (Arg.var p48) fun p49 =>
  Expr.group (fun _ => Blocks.cons (fun (p : Tup Val [.bool, i32, i64]) =>
    Expr.let_ { sig := [i32, i32], code := OpCode.add i32, args := (Arg.var i3, Arg.imm 1, ()) }
      fun p50 => Expr.jump J3 (Arg.var p50.fst, Arg.var p.fst, Arg.var p.snd.fst, ())) Blocks.nil)
  fun Js => m5FwdCheckPExpr pAr pLm pVals pWstk sz l p41 p49 cref sub drop Js.fst

private theorem m5_fwd_lblock_wp {Γ : Env} {Q : Post [.bool]} {X : XPost} {c : FullCfg}
    {F0 : CNF Nat} {F_cur : List (List Nat)} {s st_m : FullState} {R : Mem 64 → Prop}
    {C : List Nat} {cref sz i3 drop l : BitVec 32} {sub : Bool} {ml3 : Mem 64}
    {J3 : Cont [i32, .bool, i32]}
    (hstm_eq : st_m = { s with core := { s.core with lit_mark := st_m.core.lit_mark } })
    (hinv : FullDenseInv c F0 s) (hw : FullWitnessInv c F0 F_cur s.core)
    (hdw : DenseWatchesInv F_cur s.core) (hlm_m : st_m.core.lit_mark.length = 2 * c.max_vars)
    (hlm_full : ∀ x < 2 * c.max_vars, st_m.core.lit_mark[x]?.getD 0#8 ≠ 0#8 ↔ x ∈ C)
    (hC_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause C))
    (hl_mem : l.toNat ∈ C) (hl_lt : l.toNat < 2 * s.core.cur_vars)
    (hdrop_ok : FwdDropOk F_cur C drop) (hml3 : (FullMem c st_m ⋆ R) ml3)
    (hJ3 : ∀ sx dx mx, FwdDropOk F_cur C dx → (FullMem c st_m ⋆ R) mx →
      J3 (i3 + 1, sx, dx, ()) mx) :
    wp Γ Q X (m5FwdLBlockExpr c.pArena c.pLitMark c.pVals c.pWstk c.pWvec sz cref i3 sub drop l J3)
      ml3 := by
  have hlen := hinv.1.lengths.core_ok; have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hlen.cur_vars_le; have hwv_len := hlen.wvec_len; have hwlen_le := hlen.wlen_le
  have hwv_m : st_m.core.wvec = s.core.wvec := by rw [hstm_eq]
  have hwv_m_len : st_m.core.wvec.length = 4 * c.max_vars := by rw [hwv_m]; exact hwv_len
  unfold m5FwdLBlockExpr fwdLd32 fwdZext64 fwdOp64; dsimp only
  have hl_off_idx : (BitVec.setWidth 64 l <<< (1 : Nat)).toNat = 2 * l.toNat := by c0_bound
  have hl_off_lt : (BitVec.setWidth 64 l <<< (1 : Nat)).toNat <
      st_m.core.wvec.length := by rw [hl_off_idx, hwv_m_len]; omega
  have hl_sz_lt : ((BitVec.setWidth 64 l <<< (1 : Nat)) + (1 : BitVec 64)).toNat <
      st_m.core.wvec.length := by rw [hwv_m_len]; c0_bound
  have hoff_eq : (BitVec.setWidth 64 (st_m.core.wvec[(BitVec.setWidth 64 l <<<
      (1 : Nat)).toNat]'hl_off_lt)).toNat = fullWatchOffCore s.core l.toNat := by
    have he : st_m.core.wvec[(BitVec.setWidth 64 l <<< (1 : Nat)).toNat]'hl_off_lt =
        s.core.wvec[2 * l.toNat]'(by omega) := Option.some.inj (by
      rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, hwv_m, hl_off_idx])
    unfold fullWatchOffCore; rw [he, List.getElem?_eq_getElem (by omega),
      Option.getD_some, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  have hszl_eq : (BitVec.setWidth 64 (st_m.core.wvec[((BitVec.setWidth 64 l <<<
      (1 : Nat)) + (1 : BitVec 64)).toNat]'hl_sz_lt)).toNat =
      fullWatchSizeCore s.core l.toNat := by
    have he : st_m.core.wvec[((BitVec.setWidth 64 l <<< (1 : Nat)) +
        (1 : BitVec 64)).toNat]'hl_sz_lt = s.core.wvec[2 * l.toNat + 1]'(by omega) :=
      Option.some.inj (by rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem,
        hwv_m, show ((BitVec.setWidth 64 l <<< (1 : Nat)) + (1 : BitVec 64)).toNat =
          2 * l.toNat + 1 from by c0_bound])
    unfold fullWatchSizeCore; rw [he, List.getElem?_eq_getElem (by omega),
      Option.getD_some, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  have hbd_l := hdw.layout.bounds l.toNat hl_lt
  have hslice_l := hdw.slices l.toNat hl_lt; bf_fast_nogrp
  generalize hoff_v : BitVec.setWidth 64 (st_m.core.wvec[(BitVec.setWidth 64 l <<<
      (1 : Nat)).toNat]'hl_off_lt) = off at *
  generalize hszl_v : BitVec.setWidth 64 (st_m.core.wvec[((BitVec.setWidth 64 l <<<
      (1 : Nat)) + (1 : BitVec 64)).toNat]'hl_sz_lt) = szl at *
  have hend_n : (off + szl).toNat = off.toNat + szl.toNat := by bv_omega
  refine wp_join_group (fun (x : Tup Val [.bool, i32, i64]) mlp =>
      FwdDropOk F_cur C x.2.1 ∧ (FullMem c st_m ⋆ R) mlp)
    (fun _ x mlp ⟨hdropx, hmlp⟩ => by bf_fast; exact hJ3 _ _ _ hdropx hmlp)
    (fun Jpx hJpx => ?_)
  suffices hp : wp Γ Q X (m5FwdCheckPExpr c.pArena c.pLitMark c.pVals c.pWstk sz l
      off (off + szl) cref sub drop Jpx) ml3 by
    unfold m5FwdCheckPExpr m5FwdCheckJLoopExpr m5FwdLmNe0 m5FwdByteCmp0 m5FwdLdTbl fwdArOff
      fwdLd32 fwdZext64 fwdOp64 fwdCmp32 fwdCmp64 at hp; dsimp only at hp; exact hp
  exact m5_fwd_check_p_wp hstm_eq hw hinv.2.2.2.2.1 hinv.1.lengths hlm_m hlm_full
    hC_ent hinv.2.2.1 hl_mem hoff_eq (by rw [hend_n, hoff_eq, hszl_eq])
    (by rw [hoff_eq]; have := hwlen_le; omega) (by rw [hoff_eq]; exact hslice_l)
    hdrop_ok hml3
    fun sx dx px mx hdx hmx => hJpx (sx, dx, px, ()) mx ⟨hdx, hmx⟩

private theorem m5_fwd_cleanup_inv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st_c : FullState} (hinv : FullDenseInv c F0 s) (hw : FullWitnessInv c F0 F_cur s.core)
    (hdm : s.core.dense_mode ≠ 0#64)
    (hstc_eq : st_c = { s with core := { s.core with lit_mark := st_c.core.lit_mark } })
    (hlm_c : st_c.core.lit_mark.length = 2 * c.max_vars)
    (hlm_clear_c : ∀ x < 2 * c.max_vars, st_c.core.lit_mark[x]?.getD 0#8 = 0#8) :
    st_c.core = { s.core with lit_mark := st_c.core.lit_mark } ∧ st_c.LengthsOk c ∧
    FullWitnessInv c F0 F_cur st_c.core ∧ DenseWatchesInv F_cur st_c.core ∧
    fullArenaClauseRefs st_c = fullArenaClauseRefs s ∧ FullDenseInv c F0 st_c := by
  have hstc_core_eq : st_c.core = { s.core with lit_mark := st_c.core.lit_mark } := by
    rw [hstc_eq]
  have hstc_len : st_c.LengthsOk c := by rw [hstc_eq]; exact { hinv.1.lengths with
    core_ok := { hinv.1.lengths.core_ok with lit_mark_len := hlm_c } }
  have hw_c : FullWitnessInv c F0 F_cur st_c.core := by rw [hstc_core_eq]; exact { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
  have hdw_c : DenseWatchesInv F_cur st_c.core := by
    have h := hw_c.watches; unfold ModeWatchesInv at h
    rwa [ite_eq_right (by rw [hstc_core_eq]; exact hdm)] at h
  have hrefs_c : fullArenaClauseRefs st_c = fullArenaClauseRefs s := by
    unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [hstc_core_eq]
  have hstc_dense : FullDenseInv c F0 st_c := ⟨⟨hstc_len, F_cur, hw_c⟩,
    ⟨fun v hv => by rw [hstc_core_eq]; exact hinv.2.1.1 v hv, hlm_clear_c⟩,
    fun r hr hng => by
      rw [hrefs_c] at hr; rw [show fullArenaClauseLits st_c r = fullArenaClauseLits s r by
        unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore
        rw [hstc_core_eq]]
      exact hinv.2.2.1 r hr (by
        unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hng ⊢
        rwa [hstc_core_eq] at hng),
    ⟨fun i hi => by dsimp only; unfold fullArenaClauseRefs fullArenaClauseRefsCore
                    rw [hstc_eq]; exact hinv.2.2.2.1.1 i hi,
     by rw [hstc_eq]; exact hinv.2.2.2.1.2⟩,
    by rw [hstc_core_eq]; exact hinv.2.2.2.2.1, by rw [hstc_core_eq]; exact hdm⟩
  exact ⟨hstc_core_eq, hstc_len, hw_c, hdw_c, hrefs_c, hstc_dense⟩

/-! ## 2. Factored Strengthening Sub-Proof (`m5_fwd_strengthen_wp`) -/

private def m5FwdStrengthenExpr (h pAr : Val i64) (sz cref drop hdr : Val i32)
    (JsOuter : Cont [i32]) : Expr Val Cont [.bool] :=
  Expr.group (fun Jp => Blocks.cons (fun (p : Tup Val [i32, i32, i32, i32]) =>
    let ip := p.1; let nsz := p.2.1; let l0 := p.2.2.1; let l1 := p.2.2.2.1
    fwdCmp32 .ult (Arg.var ip) (Arg.var sz) fun cu =>
    Expr.jnz (Arg.var cu)
      (fwdArIdx3 cref ip fun pi => fwdLd32 pAr pi fun l =>
       Expr.group (fun _ => Blocks.cons (fun (q : Tup Val [i32, i32, i32]) =>
         Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                     args := (Arg.var ip, Arg.imm 1, ()) } fun ip1 =>
         Expr.jump Jp.1 (Arg.var ip1.1, Arg.var q.1, Arg.var q.2.1, Arg.var q.2.2.1, ()))
         Blocks.nil)
       fun Jstep =>
       fwdCmp32 .ne (Arg.var l) (Arg.var drop) fun cn => Expr.jnz (Arg.var cn)
         (Expr.group (fun _ => Blocks.cons (fun (r : Tup Val [i32, i32]) =>
            Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                        args := (Arg.var nsz, Arg.imm 1, ()) } fun n1 =>
            Expr.jump Jstep.1 (Arg.var n1.1, Arg.var r.1, Arg.var r.2.1, ())) Blocks.nil)
          fun Jsel =>
          fwdCmp32 .eq (Arg.var nsz) (Arg.imm 0) fun c0 => Expr.jnz (Arg.var c0)
            (Expr.jump Jsel.1 (Arg.var l, Arg.var l1, ()))
            (Expr.group (fun _ => Blocks.cons (fun (r1 : Tup Val [i32]) =>
               Expr.jump Jsel.1 (Arg.var l0, Arg.var r1.1, ())) Blocks.nil)
             fun Jl1 =>
             fwdCmp32 .eq (Arg.var nsz) (Arg.imm 1) fun c1 => Expr.jnz (Arg.var c1)
               (Expr.jump Jl1.1 (Arg.var l, ()))
               (Expr.jump Jl1.1 (Arg.var l1, ()))))
         (Expr.jump Jstep.1 (Arg.var nsz, Arg.var l0, Arg.var l1, ())))
      (fwdCmp32 .ule (Arg.var nsz) (Arg.imm 2) fun cle => Expr.jnz (Arg.var cle)
        (Expr.group (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
           fwdOp64 (.add i64) (Arg.var h) (Arg.imm 1128) fun pf1 =>
           Expr.load i64 (Arg.var pf1) fun fc =>
           fwdOp64 (.add i64) (Arg.var fc) (Arg.imm 1) fun fc1 =>
           fwdOp64 (.add i64) (Arg.var h) (Arg.imm 1128) fun pf2 =>
           Expr.store (Arg.var fc1) (Arg.var pf2)
             (Expr.call "full_unwatch_large" (as := [i64, i32, i32]) (bs := [])
               (Arg.var h, Arg.var drop, Arg.var cref, ()) fun _ =>
              fwdZext64 (Arg.var cref) fun p1 =>
              fwdOp64 (.mul i64) (Arg.var p1) (Arg.imm 4) fun p2 =>
              fwdOp64 (.add i64) (Arg.var pAr) (Arg.var p2) fun p3 =>
              Expr.let_ { sig := [i32, i32], code := OpCode.or i32,
                          args := (Arg.var hdr, Arg.imm 524288, ()) } fun ph =>
              Expr.store (Arg.var ph.1) (Arg.var p3)
                (fwdOp64 (.add i64) (Arg.var h) (Arg.imm 472) fun pg1 =>
                 Expr.load i64 (Arg.var pg1) fun ag =>
                 fwdOp64 (.add i64) (Arg.var ag) (Arg.imm 3) fun ag3 =>
                 fwdZext64 (Arg.var sz) fun sz64 =>
                 fwdOp64 (.add i64) (Arg.var ag3) (Arg.var sz64) fun agn =>
                 fwdOp64 (.add i64) (Arg.var h) (Arg.imm 472) fun pg2 =>
                 Expr.store (Arg.var agn) (Arg.var pg2)
                   (fwdCmp32 .eq (Arg.var nsz) (Arg.imm 0) fun cz => Expr.jnz (Arg.var cz)
                     (fwdOp64 (.add i64) (Arg.var h) (Arg.imm 1024) fun pi =>
                      Expr.store (Arg.imm (t := i64) 1#64) (Arg.var pi)
                        (Expr.ret (Arg.imm false, ())))
                     (fwdCmp32 .eq (Arg.var nsz) (Arg.imm 1) fun c1 => Expr.jnz (Arg.var c1)
                       (Expr.call "full_add_unit" (as := [i64, i32]) (bs := [.bool])
                         (Arg.var h, Arg.var l0, ()) fun ok => Expr.ret (Arg.var ok.1, ()))
                       (Expr.ret (Arg.imm true, ()))))))) Blocks.nil)
         fun Jab =>
         fwdCmp32 .eq (Arg.var nsz) (Arg.imm 2) fun c2 => Expr.jnz (Arg.var c2)
           (Expr.call "full_add_bin" (as := [i64, i32, i32]) (bs := [i64])
             (Arg.var h, Arg.var l0, Arg.var l1, ()) fun br =>
            fwdCmp64 .eq (Arg.var br.1) (Arg.imm 20) fun c20 => Expr.jnz (Arg.var c20)
              (Expr.ret (Arg.imm false, ()))
              (Expr.group (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
                 fwdOp64 (.add i64) (Arg.var h) (Arg.imm 760) fun po =>
                 Expr.store (Arg.imm (t := i64) 1#64) (Arg.var po)
                   (Expr.ret (Arg.imm true, ()))) Blocks.nil)
               fun Joom =>
               fwdCmp64 .eq (Arg.var br.1) (Arg.imm 2) fun cb2 => Expr.jnz (Arg.var cb2)
                 (Expr.jump Joom.1 ())
                 (fwdOp64 (.add i64) (Arg.var h) (Arg.imm 760) fun po2 =>
                  Expr.load i64 (Arg.var po2) fun oomv =>
                  fwdCmp64 .ne (Arg.var oomv) (Arg.imm 0) fun cnz => Expr.jnz (Arg.var cnz)
                    (Expr.jump Joom.1 ()) (Expr.jump Jab.1 ()))))
           (Expr.jump Jab.1 ()))
        (fwdOp64 (.add i64) (Arg.var h) (Arg.imm 1128) fun pf1 =>
         Expr.load i64 (Arg.var pf1) fun fc =>
         fwdOp64 (.add i64) (Arg.var fc) (Arg.imm 1) fun fc1 =>
         fwdOp64 (.add i64) (Arg.var h) (Arg.imm 1128) fun pf2 =>
         Expr.store (Arg.var fc1) (Arg.var pf2)
           (Expr.call "full_unwatch_large" (as := [i64, i32, i32]) (bs := [])
             (Arg.var h, Arg.var drop, Arg.var cref, ()) fun _ =>
            Expr.group (fun Jk => Blocks.cons (fun (pk : Tup Val [i32, i32]) =>
              fwdCmp32 .ult (Arg.var pk.1) (Arg.var sz) fun ck => Expr.jnz (Arg.var ck)
                (fwdArIdx3 cref pk.1 fun pix => fwdLd32 pAr pix fun l =>
                 Expr.group (fun _ => Blocks.cons (fun (pw : Tup Val [i32]) =>
                   Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                               args := (Arg.var pk.1, Arg.imm 1, ()) } fun k1 =>
                   Expr.jump Jk.1 (Arg.var k1.1, Arg.var pw.1, ())) Blocks.nil)
                 fun Js =>
                 fwdCmp32 .ne (Arg.var l) (Arg.var drop) fun cn => Expr.jnz (Arg.var cn)
                   (fwdArIdx3 cref pk.2.1 fun piw => fwdSt32 pAr piw (Arg.var l)
                      (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                                   args := (Arg.var pk.2.1, Arg.imm 1, ()) } fun w1 =>
                       Expr.jump Js.1 (Arg.var w1.1, ())))
                   (Expr.jump Js.1 (Arg.var pk.2.1, ())))
                (fwdArOff cref 2 fun p => fwdSt32 pAr p (Arg.var pk.2.1)
                 (fwdArOff cref 1 fun p => fwdSt32 pAr p (Arg.imm 2)
                  (Expr.group (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
                     Expr.jump JsOuter (Arg.var pk.1, ())) Blocks.nil) fun Js =>
                   Expr.let_ { sig := [i32, i32], code := OpCode.and i32,
                               args := (Arg.var hdr, Arg.imm 8388608, ()) } fun p =>
                   fwdCmp32 .eq (Arg.var p.1) (Arg.imm 0) fun cq => Expr.jnz (Arg.var cq)
                     (fwdZext64 (Arg.var cref) fun p1 =>
                      fwdOp64 (.mul i64) (Arg.var p1) (Arg.imm 4) fun p2 =>
                      fwdOp64 (.add i64) (Arg.var pAr) (Arg.var p2) fun p3 =>
                      Expr.let_ { sig := [i32, i32], code := OpCode.or i32,
                                  args := (Arg.var hdr, Arg.imm 8388608, ()) } fun p4 =>
                      Expr.store (Arg.var p4.1) (Arg.var p3)
                        (fwdArOff cref 3 fun p5 => fwdZext64 (Arg.var sz) fun p6 =>
                         fwdOp64 (.add i64) (Arg.var p5) (Arg.var p6) fun p7 =>
                         fwdOp64 (.sub i64) (Arg.var p7) (Arg.imm 1) fun p8 =>
                         fwdSt32 pAr p8 (Arg.imm 4294967295) (Expr.jump Js.1 ())))
                     (Expr.jump Js.1 ()))))) Blocks.nil)
            fun Jk => Expr.jump Jk.1 (Arg.imm 0, Arg.imm 0, ()))))) Blocks.nil)
  fun Jp => Expr.jump Jp.1 (Arg.imm 0, Arg.imm 0, Arg.imm 0, Arg.imm 0, ())

private theorem m5_fwd_strengthen_wp {Γ : Env} {Q : Post [.bool]} {X : XPost} {c : FullCfg}
    {F0 : CNF Nat} {F_cur : List (List Nat)} {s st_c : FullState} {R : Mem 64 → Prop}
    {C : List Nat} {cref sz drop hdr : BitVec 32} {mlc : Mem 64}
    (hstc_core_eq : st_c.core = { s.core with lit_mark := st_c.core.lit_mark })
    (hstc_len : st_c.LengthsOk c) (hw_c : FullWitnessInv c F0 F_cur st_c.core)
    (hdw_c : DenseWatchesInv F_cur st_c.core)
    (hrefs_c : fullArenaClauseRefs st_c = fullArenaClauseRefs s)
    (hstc_dense : FullDenseInv c F0 st_c)
    (href_c : cref.toNat ∈ fullArenaClauseRefsCore s.core)
    (hng_cref : fullArenaClauseGarbCore s.core cref.toNat = false)
    (hsz_val : sz.toNat = fullArenaClauseSizeCore s.core cref.toNat)
    (hsz_ge3 : 3 ≤ sz.toNat) (hsz_ar_len : cref.toNat + 3 + sz.toNat ≤ s.core.arena.length)
    (hhdr_v : s.core.arena[cref.toNat]'(by omega) = hdr)
    (hCu : C = fullArenaClauseLitsCore s.core cref.toNat)
    (hC_len : C.length = fullArenaClauseSizeCore s.core cref.toNat)
    (hC_lit : ∀ (t : Nat) (ht : t < sz.toNat),
      let lit := s.core.arena[cref.toNat + 3 + t]'(by omega)
      C[t]? = some lit.toNat ∧ lit.toNat ∈ C ∧ lit.toNat < 2 * s.core.cur_vars)
    (hC_lt : ∀ l ∈ C, l < 2 * s.core.cur_vars)
    (hfilt_lt_sz : (C.filter (· != drop.toNat)).length < sz.toNat)
    (hfilt_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause (C.filter (· != drop.toNat))))
    (hUnwatchLarge : ∀ args m Q X, fullUnwatchLargeSpec args m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] args m Q X)
    (hAddUnit : ∀ args m Q X, fullAddUnitSpec args m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] args m Q X)
    (hAddBin : ∀ args m Q X, fullAddBinSpec args m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] args m Q X)
    (hmlc : (FullMem c st_c ⋆ R) mlc)
    (hQ : ∀ (r : Bool) (s' : FullState) (m' : Mem 64), FullDenseInvW c F0 F_cur s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.arena_len = s.core.arena_len →
      s'.core.fuel = s.core.fuel → fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (r = false → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (JsOuter : Cont [i32])
    (hJsOuter : ∀ (iv : Val i32) ms, Q (true, ()) ms → JsOuter (iv, ()) ms) :
    wp Γ Q X (m5FwdStrengthenExpr c.hdr c.pArena sz cref drop hdr JsOuter) mlc := by
  have hmx := c.hmaxv; have har_b := c.harena; unfold dimacsBound at hmx har_b
  have hcv_le : s.core.cur_vars ≤ c.max_vars := by
    have := hstc_len.core_ok.cur_vars_le; rwa [hstc_core_eq] at this
  have har_c : st_c.core.arena = s.core.arena := by rw [hstc_core_eq]
  have har_c_len : st_c.core.arena.length = c.arena_cap := hstc_len.core_ok.arena_len_arr
  have har_len : s.core.arena.length = c.arena_cap := by rw [← har_c, har_c_len]
  have hal_le : s.core.arena_len ≤ c.arena_cap := by
    have := hstc_len.core_ok.arena_len_le; rwa [hstc_core_eq] at this
  have hcref64 : (BitVec.setWidth 64 cref).toNat = cref.toNat := by c0_bound
  let C_filt := C.filter (· != drop.toNat)
  unfold m5FwdStrengthenExpr fwdArIdx3 fwdArOff fwdLd32 fwdSt32 fwdZext64 fwdOp64 fwdCmp32 fwdCmp64
  dsimp only
  refine wp_loop_inv
    (fun (ip, nsz, l0, l1, ()) mlp =>
      mlp = mlc ∧ ip.toNat ≤ sz.toNat ∧
      nsz.toNat = ((C.take ip.toNat).filter (· != drop.toNat)).length ∧
      (0 < nsz.toNat → ((C.take ip.toNat).filter (· != drop.toNat))[0]? = some l0.toNat) ∧
      (1 < nsz.toNat → ((C.take ip.toNat).filter (· != drop.toNat))[1]? = some l1.toNat))
    (fun (ip, _, _, _, _) _ => sz.toNat - ip.toNat)
    (fun Jp hJp => by
      bf_fast
      refine hJp (0#32, 0#32, 0#32, 0#32, ()) mlc ⟨rfl,
        by rw [show (0#32 : BitVec 32).toNat = 0 from rfl]; omega, by simp,
        fun h => by rw [show (0#32 : BitVec 32).toNat = 0 from rfl] at h; omega,
        fun h => by rw [show (0#32 : BitVec 32).toNat = 0 from rfl] at h; omega⟩)
    (fun Jp (ip, nsz, l0, l1, ()) mlp ⟨hmlp, hip_le, hnsz_eq, hl0_eq, hl1_eq⟩ ihp => ?_)
  rcases hmlp.symm with rfl
  have hnsz_le_ip : nsz.toNat ≤ ip.toNat := by
    rw [hnsz_eq]; exact Nat.le_trans (List.length_filter_le _ _) (List.length_take_le _ _)
  bf_fast_nogrp
  · have hip_lt : ip.toNat < sz.toNat := by c0_bound
    have hip1 : (ip + 1#32).toNat = ip.toNat + 1 := by c0_bound
    have hnsz1 : (nsz + 1#32).toNat = nsz.toNat + 1 := by c0_bound
    have hidx_p : (BitVec.setWidth 64 cref + 3 + BitVec.setWidth 64 ip).toNat =
        cref.toNat + 3 + ip.toNat := by c0_bound
    have hidx_plt : (BitVec.setWidth 64 cref + 3 + BitVec.setWidth 64 ip).toNat <
        st_c.core.arena.length := by rw [hidx_p, har_c_len]; omega
    have hl_eq : st_c.core.arena[(BitVec.setWidth 64 cref + 3 +
        BitVec.setWidth 64 ip).toNat]'hidx_plt =
        s.core.arena[cref.toNat + 3 + ip.toNat]'(by omega) := Option.some.inj (by
      rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, har_c, hidx_p])
    have hC_ip : C[ip.toNat]'(by omega) =
        (s.core.arena[cref.toNat + 3 + ip.toNat]'(by omega)).toNat := Option.some.inj (by
      rw [← List.getElem?_eq_getElem (by omega)]; exact (hC_lit ip.toNat hip_lt).1)
    have hstep := take_succ_filter_eq (l := C) (i := ip.toNat) (x := drop.toNat) (by omega)
    refine wp_join_group (ts := [i32, i32, i32])
      (fun (nsz', l0', l1', ()) ms =>
        ms = mlc ∧
        nsz'.toNat = ((C.take (ip.toNat + 1)).filter (· != drop.toNat)).length ∧
        (0 < nsz'.toNat → ((C.take (ip.toNat + 1)).filter (· != drop.toNat))[0]? = some l0'.toNat) ∧
        (1 < nsz'.toNat → ((C.take (ip.toNat + 1)).filter (· != drop.toNat))[1]? = some l1'.toNat))
      (fun _ (nsz', l0', l1', ()) ms ⟨hms, hn', h0', h1'⟩ => by
        bf_fast
        exact ihp (ip + 1#32, nsz', l0', l1', ()) ms (by dsimp only; rw [hip1]; omega)
          ⟨hms, by rw [hip1]; omega, by rw [hip1]; exact hn',
           by rw [hip1]; exact h0', by rw [hip1]; exact h1'⟩)
      (fun Jstep hJstep => ?_)
    bf_fast_nogrp
    · have hidx_p' : (cref.toNat + BitVec.toNat (3 : BitVec 64) + ip.toNat) % 2 ^ 64 =
          cref.toNat + 3 + ip.toNat := by c0_bound
      have hl_eq' : st_c.core.arena[cref.toNat + 3 + ip.toNat]'(by omega) =
          s.core.arena[cref.toNat + 3 + ip.toNat]'(by omega) := Option.some.inj (by
        rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, har_c])
      simp only [hidx_p', hl_eq'] at hc
      have hne_nat : (C[ip.toNat]'(by omega) != drop.toNat) = true := by
        rw [hC_ip, bne_iff_ne]; intro heq; exact hc (BitVec.eq_of_toNat_eq heq)
      simp only [hne_nat, ↓reduceIte] at hstep
      refine wp_join_group (ts := [i32, i32])
        (fun (l0', l1', ()) ms =>
          ms = mlc ∧
          ((C.take (ip.toNat + 1)).filter (· != drop.toNat))[0]? = some l0'.toNat ∧
          (1 < nsz.toNat + 1 →
            ((C.take (ip.toNat + 1)).filter (· != drop.toNat))[1]? = some l1'.toNat))
        (fun _ (l0', l1', ()) ms ⟨hms, h0', h1'⟩ => by
          bf_fast
          refine hJstep (nsz + 1#32, l0', l1', ()) ms ⟨hms,
            by rw [hnsz1, hstep, List.length_append]; simp [hnsz_eq],
            fun _ => h0', fun h => h1' (by rw [hnsz1] at h; omega)⟩)
        (fun Jsel hJsel => ?_)
      bf_fast_nogrp
      · have hnsz0 : nsz.toNat = 0 := by c0_bound
        refine hJsel (_, l1, ()) mlc ⟨rfl,
          by rw [hstep, List.getElem?_append_right (by omega)]
             simp only [← hnsz_eq, hnsz0, Nat.sub_self, List.getElem?_cons_zero, hC_ip]
             rw [hl_eq],
          fun h => by omega⟩
      · refine wp_join_group (ts := [i32])
          (fun (l1', ()) ms =>
            ms = mlc ∧
            ((C.take (ip.toNat + 1)).filter (· != drop.toNat))[0]? = some l0.toNat ∧
            (1 < nsz.toNat + 1 →
              ((C.take (ip.toNat + 1)).filter (· != drop.toNat))[1]? = some l1'.toNat))
          (fun _ (l1', ()) ms ⟨hms, h0', h1'⟩ => by
            bf_fast; exact hJsel (l0, l1', ()) ms ⟨hms, h0', h1'⟩)
          (fun Jl1 hJl1 => ?_)
        bf_fast_nogrp
        · have hnsz1_v : nsz.toNat = 1 := by c0_bound
          refine hJl1 (_, ()) mlc ⟨rfl,
            by rw [hstep, List.getElem?_append_left (by omega)]; exact hl0_eq (by omega),
            fun _ => by
              rw [hstep, List.getElem?_append_right (by omega)]
              simp only [← hnsz_eq, hnsz1_v, Nat.sub_self, List.getElem?_cons_zero, hC_ip]
              rw [hl_eq]⟩
        · have hnsz2 : 2 ≤ nsz.toNat := by c0_bound
          refine hJl1 (l1, ()) mlc ⟨rfl,
            by rw [hstep, List.getElem?_append_left (by omega)]; exact hl0_eq (by omega),
            fun _ => by
              rw [hstep, List.getElem?_append_left (by omega)]; exact hl1_eq (by omega)⟩
    · have hidx_p' : (cref.toNat + BitVec.toNat (3 : BitVec 64) + ip.toNat) % 2 ^ 64 =
          cref.toNat + 3 + ip.toNat := by c0_bound
      have hl_eq' : st_c.core.arena[cref.toNat + 3 + ip.toNat]'(by omega) =
          s.core.arena[cref.toNat + 3 + ip.toNat]'(by omega) := Option.some.inj (by
        rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, har_c])
      simp only [hidx_p', hl_eq'] at hc
      have heq_nat : (C[ip.toNat]'(by omega) != drop.toNat) = false := by
        rw [hC_ip, bne_eq_false_iff_eq, hc]
      simp only [heq_nat, Bool.false_eq_true, ↓reduceIte, List.append_nil] at hstep
      exact hJstep (nsz, l0, l1, ()) mlc ⟨rfl, by rw [hstep]; exact hnsz_eq,
        by rw [hstep]; exact hl0_eq, by rw [hstep]; exact hl1_eq⟩
  · have hip_eq : ip.toNat = sz.toNat := by c0_bound
    have htake_all : C.take ip.toNat = C := List.take_of_length_le (by omega)
    rw [htake_all] at hnsz_eq hl0_eq hl1_eq
    change nsz.toNat = C_filt.length at hnsz_eq
    change 0 < nsz.toNat → C_filt[0]? = some l0.toNat at hl0_eq
    change 1 < nsz.toNat → C_filt[1]? = some l1.toNat at hl1_eq
    have hnsz_le2 : nsz.toNat ≤ 2 := by c0_bound
    refine wp_join_group (ts := [])
      (fun () mb => ∃ st_b : FullState,
        FullDenseInvW c F0 F_cur st_b ∧
        st_b.core.cur_vars = s.core.cur_vars ∧ st_b.core.arena = s.core.arena ∧
        st_b.core.arena_len = s.core.arena_len ∧ st_b.core.fuel = s.core.fuel ∧
        fullArenaClauseRefs st_b = fullArenaClauseRefs s ∧ (FullMem c st_b ⋆ R) mb)
      (fun _ () mb ⟨st_b, hinv_b, hcv_b, har_b_eq, hal_b, hfl_b, hrefs_b, hmb⟩ => ?_)
      (fun Jab hJab => ?_)
    · have hdw_b : DenseWatchesInv F_cur st_b.core := by
        have h1 := hinv_b.2.1.watches; unfold ModeWatchesInv at h1
        rwa [ite_eq_right hinv_b.2.2.2.2.2.2] at h1
      let st_b1 : FullState := { st_b with scratch := { st_b.scratch with
        fwd_str_cnt := st_b.scratch.fwd_str_cnt + 1#64 } }
      have hstb1_len : st_b1.LengthsOk c := { hinv_b.1 with scratch_ok :=
        { hinv_b.1.scratch_ok with scratch_buf_len := hinv_b.1.scratch_ok.scratch_buf_len } }
      have hstb1_dense : FullDenseInv c F0 st_b1 :=
        ⟨⟨hstb1_len, F_cur, hinv_b.2.1⟩, hinv_b.2.2.1, hinv_b.2.2.2.1,
         hinv_b.2.2.2.2.1, hinv_b.2.2.2.2.2.1, hinv_b.2.2.2.2.2.2⟩
      bf_fast_nogrp
      c0_call hUnwatchLarge
      refine ⟨c, st_b1, R, rfl, hstb1_len, hdw_b.layout, hm,
        fun wv' ws' wu' mu hlen_u _ hmode_u hmu => ?_⟩
      have hw_u : FullWitnessInv c F0 F_cur
          { st_b1.core with wvec := wv', wstk := ws', wusable := wu' } :=
        { hinv_b.2.1 with
          arena := { hinv_b.2.1.arena with len_ok := hinv_b.2.1.arena.len_ok }
          watches := hmode_u F_cur hinv_b.2.1.watches }
      have ⟨hdu, hrefs_u⟩ := fullDenseInv_of_unwatchLarge hstb1_dense hlen_u hw_u
      let st_u : FullState := { st_b1 with core :=
        { st_b1.core with wvec := wv', wstk := ws', wusable := wu' } }
      have har_u_len : st_u.core.arena.length = c.arena_cap :=
        hdu.1.lengths.core_ok.arena_len_arr
      have hcref_lt_u : (BitVec.setWidth 64 cref).toNat < st_u.core.arena.length := by
        rw [hcref64, har_u_len]; omega
      have hmk_g : FullWitnessInv c F0 F_cur { st_u.core with
          arena := st_u.core.arena.set cref.toNat (hdr ||| 0x00080000#32),
          arena_garbage := st_u.core.arena_garbage + 3#64 + BitVec.setWidth 64 sz } ∧
        FullDenseInvW c F0 F_cur { st_u with core := { st_u.core with
          arena := st_u.core.arena.set cref.toNat (hdr ||| 0x00080000#32),
          arena_garbage := st_u.core.arena_garbage + 3#64 + BitVec.setWidth 64 sz } } ∧
        fullArenaClauseRefs { st_u with core := { st_u.core with
          arena := st_u.core.arena.set cref.toNat (hdr ||| 0x00080000#32),
          arena_garbage := st_u.core.arena_garbage + 3#64 + BitVec.setWidth 64 sz } } =
          fullArenaClauseRefs st_u :=
        fwd_markGarb_comp (st_u.core.arena_garbage + 3#64 + BitVec.setWidth 64 sz)
          hdu hw_u har_b_eq hal_b rfl href_c har_u_len (by omega) hhdr_v
          (fun _ _ => by rw [har_b_eq]) hsz_val.symm
      obtain ⟨hwg, hdg, hrefs_g⟩ := hmk_g
      bf_fast
      · have hnsz0 : nsz.toNat = 0 := by c0_bound
        have ⟨hu_cur, hu_f0⟩ := fwd_unsat_of_empty_entails hw_u.ext_sound
          (List.eq_nil_of_length_eq_zero (l := C_filt) (by omega) ▸ hfilt_ent)
        exact hQ false _ m (fwdDenseW_set_inc hdg hu_cur) hcv_b hal_b hfl_b
          (hrefs_g.trans (hrefs_u.trans hrefs_b)) (fun _ => hu_f0) (by
            dsimp only [st_u]
            simp only [hcref64, show (524288 : BitVec 32) = 0x00080000#32 from rfl,
              show (3 : BitVec 64) = 3#64 from rfl] at hm ⊢
            exact hm)
      · have hnsz1 : nsz.toNat = 1 := by c0_bound
        have hC1 : C_filt = [l0.toNat] := by
          have h0 := hl0_eq (by omega)
          cases hcf : C_filt with
          | nil => rw [hcf] at hnsz_eq; simp at hnsz_eq; omega
          | cons a t =>
            have ht0 : t = [] := by
              have hlen_cf : C_filt.length = 1 := by omega
              rw [hcf] at hlen_cf; cases t <;> simp at hlen_cf ⊢
            subst ht0; rw [hcf] at h0; simp at h0; rw [h0]
        have hl0_lt : l0.toNat < 2 * s.core.cur_vars := by
          have hmem : l0.toNat ∈ C_filt := by rw [hC1]; exact List.mem_singleton.mpr rfl
          exact hC_lt _ (List.mem_filter.mp hmem).1
        have hm_g : (FullMem c { st_u with core := { st_u.core with
            arena := st_u.core.arena.set cref.toNat (hdr ||| 0x00080000#32),
            arena_garbage := st_u.core.arena_garbage + 3#64 + BitVec.setWidth 64 sz } }
            ⋆ R) m := by
          dsimp only [st_u]
          simp only [hcref64, show (524288 : BitVec 32) = 0x00080000#32 from rfl,
            show (3 : BitVec 64) = 3#64 from rfl] at hm ⊢
          exact hm
        c0_call hAddUnit
        refine ⟨c, F0, F_cur, _, R, rfl, hdg.1, hwg,
          fun _ => by rw [← hC1]; exact hfilt_ent, hm_g,
          fun ok1 _ _ _ _ _ _ _ _ cl1 _ _ _ _ _ _ _ _ _ _ _ _ _ m1
            hlen1 hw1 hcl1 _ hfalse1 hm1 => ?_⟩
        have ⟨hd1, hrefs1⟩ := fullDenseInv_of_fwd_call hdg.toDense hlen1 hw1 hcl1
          rfl rfl rfl rfl rfl rfl rfl
        exact hQ ok1 _ m1 ⟨hd1.1.lengths, hw1, hd1.2⟩ hcv_b hal_b hfl_b
          (hrefs1.trans (hrefs_g.trans (hrefs_u.trans hrefs_b)))
          (fun hok => ((hfalse1 hok).resolve_left (by
            dsimp only; rw [hcv_b]; exact Nat.not_le.mpr hl0_lt)).1) hm1
      · exact hQ true _ m hdg hcv_b hal_b hfl_b
          (hrefs_g.trans (hrefs_u.trans hrefs_b)) (by simp) (by
            dsimp only [st_u]
            simp only [hcref64, show (524288 : BitVec 32) = 0x00080000#32 from rfl,
              show (3 : BitVec 64) = 3#64 from rfl] at hm ⊢
            exact hm)
    · bf_fast_nogrp
      · have hnsz2 : nsz.toNat = 2 := by c0_bound
        have hC2 : C_filt = [l0.toNat, l1.toNat] := by
          have h0 := hl0_eq (by omega); have h1 := hl1_eq (by omega)
          cases hcf : C_filt with
          | nil => rw [hcf] at hnsz_eq; simp at hnsz_eq; omega
          | cons a t =>
            cases t with
            | nil => rw [hcf] at hnsz_eq; simp at hnsz_eq; omega
            | cons b u =>
              have hu0 : u = [] := by
                have hlen_cf : C_filt.length = 2 := by omega
                rw [hcf] at hlen_cf; cases u <;> simp at hlen_cf ⊢
              subst hu0; rw [hcf] at h0 h1; simp at h0 h1; rw [h0, h1]
        c0_call hAddBin
        refine ⟨c, F0, F_cur, st_c, R, rfl, hstc_len, hw_c,
          hstc_dense.2.2.2.2.1, fun _ _ => by rw [← hC2]; exact hfilt_ent, hmlc,
          fun rb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 hlen2 hw2 _ h20 _ hm2 => ?_⟩
        have ⟨hd2, hrefs2⟩ := fullDenseInv_of_fwd_call hstc_dense hlen2 hw2
          hstc_dense.2.2.2.2.1 rfl rfl rfl rfl rfl rfl rfl
        have hinv_2 : FullDenseInvW c F0 F_cur _ := ⟨hd2.1.lengths, hw2, hd2.2⟩
        bf_fast_nogrp
        · exact hQ false _ m2 hinv_2 (by rw [hstc_core_eq]) (by rw [hstc_core_eq])
            (by rw [hstc_core_eq]) (hrefs2.trans hrefs_c) (fun _ => (h20 hc).1) hm2
        · refine wp_join_group (ts := []) (fun () mo => mo = m2)
            (fun _ () mo hmo => by
              rcases hmo.symm with rfl; bf_fast
              exact hQ true _ m (fullDenseInvW_with_oom hinv_2 1#64)
                (by rw [hstc_core_eq]) (by rw [hstc_core_eq]) (by rw [hstc_core_eq])
                (hrefs2.trans hrefs_c) (by simp) hm)
            (fun Joom hJoom => by
              bf_fast
              · exact hJoom () m2 rfl
              · exact hJoom () m2 rfl
              · exact hJab () m2 ⟨_, hinv_2, by rw [hstc_core_eq], har_c,
                  by rw [hstc_core_eq], by rw [hstc_core_eq], hrefs2.trans hrefs_c, hm2⟩)
      · exact hJab () mlc ⟨st_c, ⟨hstc_len, hw_c, hstc_dense.2⟩,
          by rw [hstc_core_eq], har_c, by rw [hstc_core_eq],
          by rw [hstc_core_eq], hrefs_c, hmlc⟩
  · have hip_eq : ip.toNat = sz.toNat := by c0_bound
    have htake_all : C.take ip.toNat = C := List.take_of_length_le (by omega)
    rw [htake_all] at hnsz_eq hl0_eq hl1_eq
    change nsz.toNat = C_filt.length at hnsz_eq
    have hnsz3 : 3 ≤ nsz.toNat := by c0_bound
    let st_c1 : FullState := { st_c with scratch := { st_c.scratch with
      fwd_str_cnt := st_c.scratch.fwd_str_cnt + 1#64 } }
    have hstc1_len : st_c1.LengthsOk c := { hstc_len with scratch_ok :=
      { hstc_len.scratch_ok with scratch_buf_len := hstc_len.scratch_ok.scratch_buf_len } }
    have hstc1_dense : FullDenseInv c F0 st_c1 :=
      ⟨⟨hstc1_len, F_cur, hw_c⟩, hstc_dense.2.1, hstc_dense.2.2.1,
       hstc_dense.2.2.2.1, hstc_dense.2.2.2.2.1, hstc_dense.2.2.2.2.2⟩
    c0_call hUnwatchLarge
    refine ⟨c, st_c1, R, rfl, hstc1_len, hdw_c.layout, hm,
      fun wv' ws' wu' mu hlen_u _ hmode_u hmu => ?_⟩
    have hw_u : FullWitnessInv c F0 F_cur
        { st_c1.core with wvec := wv', wstk := ws', wusable := wu' } :=
      { hw_c with arena := { hw_c.arena with len_ok := hw_c.arena.len_ok }
                  watches := hmode_u F_cur hw_c.watches }
    have ⟨hdu, hrefs_u⟩ := fullDenseInv_of_unwatchLarge hstc1_dense hlen_u hw_u
    let st_u : FullState := { st_c1 with core :=
      { st_c1.core with wvec := wv', wstk := ws', wusable := wu' } }
    have har_u_len : st_u.core.arena.length = c.arena_cap :=
      hdu.1.lengths.core_ok.arena_len_arr
    have hstu_cv : st_u.core.cur_vars = s.core.cur_vars := by
      dsimp only [st_u, st_c1]; rw [hstc_core_eq]
    have hstu_al : st_u.core.arena_len = s.core.arena_len := by
      dsimp only [st_u, st_c1]; rw [hstc_core_eq]
    have hstu_fl : st_u.core.fuel = s.core.fuel := by
      dsimp only [st_u, st_c1]; rw [hstc_core_eq]
    refine wp_loop_inv (fun (ik, w, ()) mlk => ∃ st_k : FullState,
        AgreesExcept fwdArenaMask st_u st_k ∧ st_k.core.arena.length = c.arena_cap ∧
        ik.toNat ≤ sz.toNat ∧
        w.toNat = ((C.take ik.toNat).filter (· != drop.toNat)).length ∧
        (∀ t < w.toNat, st_k.core.arena[cref.toNat + 3 + t]?.map BitVec.toNat =
          ((C.take ik.toNat).filter (· != drop.toNat))[t]?) ∧
        (∀ t, ik.toNat ≤ t → t < sz.toNat →
          st_k.core.arena[cref.toNat + 3 + t]? = s.core.arena[cref.toNat + 3 + t]?) ∧
        (∀ t < sz.toNat,
          st_k.core.arena[cref.toNat + 3 + t]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) ∧
        (∀ idx, idx < cref.toNat + 3 ∨ cref.toNat + 3 + sz.toNat ≤ idx →
          st_k.core.arena[idx]? = s.core.arena[idx]?) ∧ (FullMem c st_k ⋆ R) mlk)
      (fun (ik, _, _) _ => sz.toNat - ik.toNat)
      (fun Jk hJk => by
        bf_fast; refine hJk (0#32, 0#32, ()) mu ⟨st_u, .refl _ _, har_u_len,
          by rw [show (0#32 : BitVec 32).toNat = 0 from rfl]; omega, by simp,
          fun _ ht => by simp at ht, fun _ _ _ => by rw [har_c], fun t ht => by
            rw [har_c, List.getElem?_eq_getElem (by omega), Option.getD_some]
            intro heq; have hlt := (hC_lit t ht).2.2
            have : (0xFFFFFFFF#32 : BitVec 32).toNat = 4294967295 := rfl; rw [heq] at hlt; omega,
          fun _ _ => by rw [har_c], hmu⟩)
      (fun Jk (ik, w, ()) mlk ⟨st_k, hag_k, har_k_len, hik_le, hw_eq, hpref_k,
        htail_k, hnesent_k, hout_k, hmlk⟩ ihk => ?_)
    have hstk_eq := fwd_arena_reconstruct hag_k
    have hw_le_ik : w.toNat ≤ ik.toNat := by
      rw [hw_eq]; exact Nat.le_trans (List.length_filter_le _ _) (List.length_take_le _ _)
    bf_fast_nogrp
    · have hik_lt : ik.toNat < sz.toNat := by c0_bound
      have hidx_w : (BitVec.setWidth 64 cref + 3 + BitVec.setWidth 64 w).toNat =
          cref.toNat + 3 + w.toNat := by c0_bound
      have hik1 : (ik + 1#32).toNat = ik.toNat + 1 := by c0_bound
      have hw1 : (w + 1#32).toNat = w.toNat + 1 := by c0_bound
      have hl_eq : st_k.core.arena[cref.toNat + 3 + ik.toNat]'(by omega) =
          s.core.arena[cref.toNat + 3 + ik.toNat]'(by omega) := Option.some.inj
        (by rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem]
            exact htail_k ik.toNat (Nat.le_refl _) hik_lt)
      have hC_ik : C[ik.toNat]'(by omega) =
          (s.core.arena[cref.toNat + 3 + ik.toNat]'(by omega)).toNat := Option.some.inj
        (by rw [← List.getElem?_eq_getElem (by omega)]; exact (hC_lit ik.toNat hik_lt).1)
      have hstep_filt := take_succ_filter_eq (l := C) (i := ik.toNat) (x := drop.toNat) (by omega)
      refine wp_join_group
        (fun (x : Tup Val [i32]) mls => ∃ st_s : FullState,
          AgreesExcept fwdArenaMask st_u st_s ∧ st_s.core.arena.length = c.arena_cap ∧
          x.1.toNat = ((C.take (ik.toNat + 1)).filter (· != drop.toNat)).length ∧
          (∀ t < x.1.toNat, st_s.core.arena[cref.toNat + 3 + t]?.map BitVec.toNat =
            ((C.take (ik.toNat + 1)).filter (· != drop.toNat))[t]?) ∧
          (∀ t, ik.toNat + 1 ≤ t → t < sz.toNat →
            st_s.core.arena[cref.toNat + 3 + t]? = s.core.arena[cref.toNat + 3 + t]?) ∧
          (∀ t < sz.toNat, st_s.core.arena[cref.toNat + 3 + t]?.getD
            0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) ∧
          (∀ idx, idx < cref.toNat + 3 ∨ cref.toNat + 3 + sz.toNat ≤ idx →
            st_s.core.arena[idx]? = s.core.arena[idx]?) ∧ (FullMem c st_s ⋆ R) mls)
        (fun _ x mls ⟨st_s, hags, hars, hws, hps, hts, hnes, hos, hms⟩ => by
          bf_fast
          exact ihk (ik + 1#32, x.1, ()) mls (by dsimp only; rw [hik1]; omega)
            ⟨st_s, hags, hars, by rw [hik1]; omega, by rw [hik1]; exact hws,
             fun t ht => by rw [hik1]; exact hps t ht,
             fun t ht1 ht2 => hts t (by rw [hik1] at ht1; omega) ht2, hnes, hos, hms⟩)
        (fun Js hJs => ?_)
      bf_fast
      · have hidx_k' : (cref.toNat + BitVec.toNat (3 : BitVec 64) + ik.toNat) % 2 ^ 64 =
            cref.toNat + 3 + ik.toNat := by c0_bound
        have hidx_kk : (BitVec.setWidth 64 cref + 3 + BitVec.setWidth 64 ik).toNat =
            cref.toNat + 3 + ik.toNat := by c0_bound
        simp only [hidx_k', hl_eq] at hc
        simp only [hidx_w, hidx_kk, hl_eq] at hm
        have hne_nat : (C[ik.toNat]'(by omega) != drop.toNat) = true := by
          rw [hC_ik, bne_iff_ne]; intro heq; exact hc (BitVec.eq_of_toNat_eq heq)
        simp only [hne_nat, ↓reduceIte] at hstep_filt
        have hset_lt : cref.toNat + 3 + w.toNat < st_k.core.arena.length := by
          rw [har_k_len]; omega
        refine hJs (w + 1#32, ()) m ⟨_, by exact hag_k.trans rfl, by simp [har_k_len],
          by dsimp only; rw [hw1, hstep_filt, List.length_append]; simp [hw_eq],
          fun t ht => by
            dsimp only at ht ⊢; rw [hw1] at ht; rw [hstep_filt]
            by_cases htn : t = w.toNat
            · subst htn
              rw [List.getElem?_set_self hset_lt, Option.map_some,
                List.getElem?_append_right (by omega)]
              simp [hw_eq, hC_ik]
            · rw [List.getElem?_set_ne (by omega), List.getElem?_append_left (by omega)]
              exact hpref_k t (by omega),
          fun t ht1 ht2 => by
            dsimp only; rw [List.getElem?_set_ne (by omega)]; exact htail_k t (by omega) ht2,
          fun t ht => by
            dsimp only; by_cases htn : t = w.toNat
            · subst htn; rw [List.getElem?_set_self hset_lt, Option.getD_some]
              intro heq; have hlt := (hC_lit ik.toNat hik_lt).2.2
              have : (0xFFFFFFFF#32 : BitVec 32).toNat = 4294967295 := rfl; rw [heq] at hlt; omega
            · rw [List.getElem?_set_ne (by omega)]; exact hnesent_k t ht,
          fun idx hidx => by
            dsimp only; rw [List.getElem?_set_ne (by omega)]; exact hout_k idx hidx,
          hm⟩
      · have hidx_k' : (cref.toNat + BitVec.toNat (3 : BitVec 64) + ik.toNat) % 2 ^ 64 =
            cref.toNat + 3 + ik.toNat := by c0_bound
        simp only [hidx_k', hl_eq] at hc
        have heq_nat : (C[ik.toNat]'(by omega) != drop.toNat) = false := by
          rw [hC_ik, bne_eq_false_iff_eq, hc]
        simp only [heq_nat, Bool.false_eq_true, ↓reduceIte, List.append_nil] at hstep_filt
        exact hJs (w, ()) mlk ⟨st_k, hag_k, har_k_len, by rw [hstep_filt]; exact hw_eq,
          fun t ht => by rw [hstep_filt]; exact hpref_k t ht,
          fun t ht1 ht2 => htail_k t (by omega) ht2, hnesent_k, hout_k, hmlk⟩
    · have hik_eq : ik.toNat = sz.toNat := by c0_bound
      have htake_all : C.take ik.toNat = C := List.take_of_length_le (by omega)
      rw [htake_all] at hw_eq hpref_k
      have hw_eq_nsz : w.toNat = nsz.toNat := by rw [hw_eq, hnsz_eq]
      have hw3 : 3 ≤ w.toNat := by omega
      have hw_lt_sz : w.toNat < sz.toNat := by omega
      have hw_ofNat : w = BitVec.ofNat 32 w.toNat :=
        BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt w.isLt])
      have hcref1_n : (BitVec.setWidth 64 cref + 1).toNat = cref.toNat + 1 := by c0_bound
      have hcref2_n : (BitVec.setWidth 64 cref + 2).toNat = cref.toNat + 2 := by c0_bound
      have hsent_n : (BitVec.setWidth 64 cref + 3 + BitVec.setWidth 64 sz - 1).toNat =
          cref.toNat + 3 + sz.toNat - 1 := by c0_bound
      have hszeq_u : fullArenaClauseSizeCore st_u.core cref.toNat = sz.toNat := by
        unfold fullArenaClauseSizeCore; rw [har_c]; exact hsz_val.symm
      have hhdr_u : fullArenaHdrCore st_u.core cref.toNat = hdr := by
        unfold fullArenaHdrCore; rw [har_c, List.getElem?_eq_getElem (by omega),
          Option.getD_some, hhdr_v]
      have hlen_k : cref.toNat + 3 + sz.toNat ≤ st_k.core.arena.length := by
        rw [har_k_len, ← har_len]; exact hsz_ar_len
      have hfilt_elem : ∀ (t : Nat) (ht : t < w.toNat),
          (st_k.core.arena[cref.toNat + 3 + t]'(by omega)).toNat =
            (C.filter (· != drop.toNat))[t]'(by omega) := fun t ht => Option.some.inj (by
        have h1 := hpref_k t ht
        rw [List.getElem?_eq_getElem (by omega), Option.map_some,
          List.getElem?_eq_getElem (by omega)] at h1; exact h1)
      bf_fast
      · have hsh0 : (fullArenaHdrCore st_u.core cref.toNat &&& 0x00800000#32) = 0#32 := by
          rw [hhdr_u]; exact hc
        simp only [hcref64, hcref1_n, hcref2_n, hsent_n] at hm
        exact hJsOuter _ _ (fwd_shrink_done hdu hw_u har_c hstu_cv hstu_al hstu_fl
          hstk_eq href_c hng_cref hw3 hw_lt_sz hsz_val hCu.symm hw_eq.symm hfilt_ent
          hrefs_u hrefs_c (by simp [har_k_len])
          (by rw [List.getElem?_set_ne (by omega),
                List.getElem?_set_self (by simp [har_k_len]; omega),
                ite_eq_left hsh0, hhdr_u]; try rfl)
          (by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
                List.getElem?_set_ne (by omega),
                List.getElem?_set_self (by simp [har_k_len]; omega)]
              exact congrArg some hw_ofNat)
          (fun _ => ⟨by rw [hszeq_u, List.getElem?_set_self
              (by simp [har_k_len]; omega)]; try rfl,
            fun idx hi1 hi2 => by
              rw [hszeq_u] at hi2
              rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
                List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
              have hsub := hnesent_k (idx - (cref.toNat + 3)) (by omega)
              rwa [show cref.toNat + 3 + (idx - (cref.toNat + 3)) = idx by omega] at hsub⟩)
          (fun hne => absurd hsh0 hne)
          (fun idx hidx => by
            rw [hszeq_u] at hidx
            rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
              List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), har_c]
            exact hout_k idx (by omega))
          (fun t ht => by
            rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
              List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
              List.getElem?_eq_getElem (by omega), Option.map_some,
              hfilt_elem t ht, List.getElem?_eq_getElem (by omega)]) hm hQ)
      · have hsh1 : (fullArenaHdrCore st_u.core cref.toNat &&& 0x00800000#32) ≠ 0#32 := by
          rw [hhdr_u]; exact hc
        simp only [hcref1_n, hcref2_n] at hm
        exact hJsOuter _ _ (fwd_shrink_done hdu hw_u har_c hstu_cv hstu_al hstu_fl
          hstk_eq href_c hng_cref hw3 hw_lt_sz hsz_val hCu.symm hw_eq.symm hfilt_ent
          hrefs_u hrefs_c (by simp [har_k_len])
          (by rw [ite_eq_right hsh1, List.getElem?_set_ne (by omega),
                List.getElem?_set_ne (by omega), hout_k cref.toNat (by omega),
                hhdr_u, List.getElem?_eq_getElem (by omega), hhdr_v])
          (by rw [List.getElem?_set_ne (by omega),
                List.getElem?_set_self (by simp [har_k_len]; omega)]
              exact congrArg some hw_ofNat)
          (fun h0 => absurd h0 hsh1)
          (fun _ idx hi1 hi2 => by
            rw [hszeq_u] at hi2
            rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
            have hsub := hnesent_k (idx - (cref.toNat + 3)) (by omega)
            rwa [show cref.toNat + 3 + (idx - (cref.toNat + 3)) = idx by omega] at hsub)
          (fun idx hidx => by
            rw [hszeq_u] at hidx
            rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), har_c]
            exact hout_k idx (by omega))
          (fun t ht => by
            rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
              List.getElem?_eq_getElem (by omega), Option.map_some,
              hfilt_elem t ht, List.getElem?_eq_getElem (by omega)]) hm hQ)

/-! ## 3. `full_fwd_check_cl_m5_wp` (`Full.fullFwdCheckClSpec`) -/

/-- `full_fwd_check_cl_m5` satisfies canonical `Full.fullFwdCheckClSpec` parametrically in `Γ`:
short-circuits on pre-existing `h->oom != 0ULL`, and when strengthening to a binary clause calls
`full_add_bin` before unwatching/`PH_GARB`-deleting `cref` so OOM never loses `cref`. -/
public theorem full_fwd_check_cl_m5_wp (Γ : Env)
    (hUnwatchLarge : ∀ args m Q X, fullUnwatchLargeSpec args m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] args m Q X)
    (hAddUnit : ∀ args m Q X, fullAddUnitSpec args m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] args m Q X)
    (hAddBin : ∀ args m Q X, fullAddBinSpec args m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] args m Q X) :
    ∀ args m Q X, fullFwdCheckClSpec args m Q X →
      Func.wp Γ full_fwd_check_cl_m5_body args m Q X := by
  rintro ⟨h, cref, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hinvW, href, hm, hQ⟩
  have hinv := hinvW.toDense; have hw := hinvW.2.1; have hmx := c.hmaxv; have har_b := c.harena
  have hwcap := c.hwcap; unfold dimacsBound at hmx har_b hwcap; have hlen := hinv.1.lengths.core_ok
  have hcv_le := hlen.cur_vars_le; have har_len := hlen.arena_len_arr
  have hal_le := hlen.arena_len_le
  have hlm_len := hlen.lit_mark_len; have hvals_len := hlen.vals_len; have hwv_len := hlen.wvec_len
  have hws_len := hlen.wstk_len_arr; have hwlen_le := hlen.wlen_le
  have hdm : s.core.dense_mode ≠ 0#64 := hinv.2.2.2.2.2
  have hdw : DenseWatchesInv F_cur s.core := by
    have h1 := hw.watches; unfold ModeWatchesInv at h1; rwa [ite_eq_right hdm] at h1
  have href_c : cref.toNat ∈ fullArenaClauseRefsCore s.core := href
  have hcref_wf := hw.arena.refs_wf cref.toNat href_c
  have hcref64 : (BitVec.setWidth 64 cref).toNat = cref.toNat := by c0_bound
  have hhdr_eq : s.core.arena[cref.toNat]'(by omega) = fullArenaHdrCore s.core cref.toNat := by
    unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hsz_eq : (s.core.arena[(BitVec.setWidth 64 cref + (2 : BitVec 64)).toNat]'(by
      c0_bound)).toNat = fullArenaClauseSizeCore s.core cref.toNat := by
    simp only [fullArenaClauseSizeCore, show (BitVec.setWidth 64 cref + (2 : BitVec 64)).toNat =
      cref.toNat + 2 from by c0_bound, List.getElem?_eq_getElem (show cref.toNat + 2 <
      s.core.arena.length by omega), Option.getD_some]
  unfold Func.wp full_fwd_check_cl_m5_body; dsimp only; bf_fast
  · exact hQ true s m hinvW rfl rfl rfl rfl (by simp) hm
  · exact hQ true s m hinvW rfl rfl rfl rfl (by simp) hm
  · exact hQ true s m hinvW rfl rfl rfl rfl (by simp) hm
  · have hng_cref : fullArenaClauseGarbCore s.core cref.toNat = false := by
      have hget : s.core.arena[(BitVec.setWidth 64 cref).toNat]'(by c0_bound) =
          s.core.arena[cref.toNat]'(by omega) := Option.some.inj (by
        rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, hcref64])
      unfold fullArenaClauseGarbCore; rw [← hhdr_eq, ← hget]
      exact garb_false_of_and_garb_red_eq_zero (by assumption)
    let C := fullArenaClauseLitsCore s.core cref.toNat
    have hC_len : C.length = fullArenaClauseSizeCore s.core cref.toNat :=
      fullArenaClauseLitsCore_length (by have := hcref_wf.2.2; omega)
    have hC_lt := hw.arena.lits_lt cref.toNat href_c hng_cref
    have hC_ent := hw.arena.entails cref.toNat href_c hng_cref
    have hC_nodup : (C.map (· / 2)).Nodup := hinv.2.2.1 cref.toNat href hng_cref
    have hsz_val := hsz_eq; generalize hhdr_v : s.core.arena[cref.toNat]'(by omega) = hdr
    generalize hsz_v : s.core.arena[(BitVec.setWidth 64 cref + (2 : BitVec 64)).toNat]'(by
      c0_bound) = sz at hsz_val ⊢
    have hsz_ge3 : 3 ≤ sz.toNat := by have := hcref_wf.2.1; omega
    have hsz_ar_len : cref.toNat + 3 + sz.toNat ≤ s.core.arena.length := by
      have := hcref_wf.2.2; omega
    have hC_lit : ∀ (t : Nat) (_ : t < sz.toNat),
        let lit := s.core.arena[cref.toNat + 3 + t]'(by omega)
        C[t]? = some lit.toNat ∧ lit.toNat ∈ C ∧ lit.toNat < 2 * s.core.cur_vars := fun t ht => by
      have hg := fullArenaClauseLitsCore_getElem (k := s.core) (r := cref.toNat) (j := t)
        (by omega) (by omega)
      have hmem := List.mem_of_getElem? hg; exact ⟨hg, hmem, hC_lt _ hmem⟩
    refine wp_loop_inv (fun (i, ()) mlm => ∃ st_m : FullState,
        AgreesExcept fwdLmMask s st_m ∧ st_m.core.lit_mark.length = 2 * c.max_vars ∧
        i.toNat ≤ sz.toNat ∧ (∀ x < 2 * c.max_vars,
          st_m.core.lit_mark[x]?.getD 0#8 ≠ 0#8 ↔ ∃ t < i.toNat, C[t]? = some x) ∧
        (FullMem c st_m ⋆ R) mlm) (fun (i, ()) _ => sz.toNat - i.toNat) (fun J1 hJ1 => by
          bf_steps; refine hJ1 (0#32, ()) m ⟨s, .refl _ _, hlm_len,
            by rw [show (0#32 : BitVec 32).toNat = 0 from rfl]; omega, fun x hx => ⟨fun h =>
              absurd (hinv.2.1.2 x hx) h, fun ⟨t, ht, _⟩ => by
              rw [show (0#32 : BitVec 32).toNat = 0 from rfl] at ht; omega⟩, hm⟩)
      (fun J1 (i, ()) mlm ⟨st_m, hag_m, hlm_m, hi_le, hlm_iff, hmlm⟩ ih1 => ?_)
    have hstm_eq := fwd_lm_reconstruct hag_m
    have har_m : st_m.core.arena = s.core.arena := by rw [hstm_eq]
    have har_m_len : st_m.core.arena.length = c.arena_cap := by rw [har_m]; exact har_len
    bf_steps
    · have hi_lt : i.toNat < sz.toNat := by c0_bound
      have hidx_lt : (BitVec.setWidth 64 cref + (3 : BitVec 64) + BitVec.setWidth 64 i).toNat <
          st_m.core.arena.length := by rw [har_m_len]; c0_bound
      have helem : st_m.core.arena[(BitVec.setWidth 64 cref + (3 : BitVec 64) +
          BitVec.setWidth 64 i).toNat]'hidx_lt =
          s.core.arena[cref.toNat + 3 + i.toNat]'(by omega) := Option.some.inj (by
        rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, har_m,
          show (BitVec.setWidth 64 cref + (3 : BitVec 64) + BitVec.setWidth 64 i).toNat =
            cref.toNat + 3 + i.toNat from by c0_bound])
      have hlit_i := hC_lit i.toNat hi_lt
      have hlit_lm : (BitVec.setWidth 64 (st_m.core.arena[(BitVec.setWidth 64 cref +
          (3 : BitVec 64) + BitVec.setWidth 64 i).toNat]'hidx_lt)).toNat <
          st_m.core.lit_mark.length := by
        rw [helem, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hlm_m]; omega
      have hi1_n : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
      bf_steps; refine ih1 _ _ (by
          dsimp only; rw [show (i + 1 : BitVec 32) = i + 1#32 from rfl, hi1_n]; omega)
        ⟨_, by exact hag_m.trans rfl, by simp [hlm_m],
         by rw [show (i + 1 : BitVec 32) = i + 1#32 from rfl, hi1_n]; omega, fun x hx => ?_, hm⟩
      dsimp only
      have hlit64 : (BitVec.setWidth 64 (st_m.core.arena[(BitVec.setWidth 64 cref +
          (3 : BitVec 64) + BitVec.setWidth 64 i).toNat]'hidx_lt)).toNat =
          (s.core.arena[cref.toNat + 3 + i.toNat]'(by omega)).toNat := by
        rw [helem, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
      rw [show (i + 1 : BitVec 32) = i + 1#32 from rfl, hi1_n]
      by_cases hxe : x = (s.core.arena[cref.toNat + 3 + i.toNat]'(by omega)).toNat
      · rw [hxe, ← hlit64, List.getElem?_set_self hlit_lm, Option.getD_some, hlit64]
        exact ⟨fun _ => ⟨i.toNat, by omega, hlit_i.1⟩, fun _ => by decide⟩
      · rw [List.getElem?_set_ne (by rw [hlit64]; exact Ne.symm hxe), hlm_iff x hx]
        refine ⟨fun ⟨t, ht, hct⟩ => ⟨t, by omega, hct⟩, fun ⟨t, ht, hct⟩ => ?_⟩
        by_cases hti : t = i.toNat
        · subst hti; rw [hlit_i.1] at hct; exact absurd (Option.some.inj hct).symm hxe
        · exact ⟨t, by omega, hct⟩
    · have hi_eq : i.toNat = sz.toNat := by c0_bound
      have hlm_full : ∀ x < 2 * c.max_vars, st_m.core.lit_mark[x]?.getD 0#8 ≠ 0#8 ↔ x ∈ C := by
        intro x hx; rw [hlm_iff x hx, hi_eq]
        refine ⟨fun ⟨_, _, hct⟩ => List.mem_of_getElem? hct, fun hm => ?_⟩
        obtain ⟨t, ht, hct⟩ := List.mem_iff_getElem.mp hm
        exact ⟨t, by omega, by rw [List.getElem?_eq_getElem ht, hct]⟩
      have hwv_m : st_m.core.wvec = s.core.wvec := by rw [hstm_eq]
      have hwv_m_len : st_m.core.wvec.length = 4 * c.max_vars := by rw [hwv_m]; exact hwv_len
      have hl0_info := hC_lit 0 (by omega)
      have hl0_elem : st_m.core.arena[(BitVec.setWidth 64 cref + (3 : BitVec 64)).toNat]'(by
          rw [har_m_len]; c0_bound) = s.core.arena[cref.toNat + 3]'(by omega) := Option.some.inj
        (by rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, har_m, show
          (BitVec.setWidth 64 cref + (3 : BitVec 64)).toNat = cref.toNat + 3 from by c0_bound])
      have hl0_wv : ((BitVec.setWidth 64 (st_m.core.arena[(BitVec.setWidth 64 cref +
          (3 : BitVec 64)).toNat]'(by rw [har_m_len]; c0_bound)) <<< (1 : Nat)) +
          (1 : BitVec 64)).toNat < st_m.core.wvec.length := by
        have hlt0 : (s.core.arena[cref.toNat + 3]'(by omega)).toNat < 2 * s.core.cur_vars := by
          simpa only [Nat.add_zero] using hl0_info.2.2
        rw [hl0_elem, hwv_m_len]; c0_bound
      bf_fast_nogrp
      refine wp_loop_inv (fun (i2, min_l, min_deg, ()) ml2 => 1 ≤ i2.toNat ∧
          i2.toNat ≤ sz.toNat ∧ min_l.toNat ∈ C ∧ min_l.toNat < 2 * s.core.cur_vars ∧
          (FullMem c st_m ⋆ R) ml2) (fun (i2, _, _, _) _ => sz.toNat - i2.toNat) (fun J2 hJ2 => by
        bf_fast; refine hJ2 (1#32, _, _, ()) mlm ⟨by decide,
          by rw [show (1#32 : BitVec 32).toNat = 1 from rfl]; omega,
          by rw [hl0_elem]; simpa only [Nat.add_zero] using hl0_info.2.1,
          by rw [hl0_elem]; simpa only [Nat.add_zero] using hl0_info.2.2, hmlm⟩)
        (fun J2 (i2, min_l, min_deg, ()) ml2 ⟨hi2_ge, hi2_le, hml_mem, hml_lt, hml2⟩ ih2 => ?_)
      bf_fast
      · have hi2_lt : i2.toNat < sz.toNat := by c0_bound
        have hidx2_lt : (BitVec.setWidth 64 cref + (3 : BitVec 64) + BitVec.setWidth 64 i2).toNat <
            st_m.core.arena.length := by rw [har_m_len]; c0_bound
        have helem2 : st_m.core.arena[(BitVec.setWidth 64 cref + (3 : BitVec 64) +
            BitVec.setWidth 64 i2).toNat]'hidx2_lt =
            s.core.arena[cref.toNat + 3 + i2.toNat]'(by omega) := Option.some.inj (by
          rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, har_m, show
            (BitVec.setWidth 64 cref + (3 : BitVec 64) + BitVec.setWidth 64 i2).toNat =
            cref.toNat + 3 + i2.toNat from by c0_bound])
        have hli2 := hC_lit i2.toNat hi2_lt
        have hli2_wv : ((BitVec.setWidth 64 (st_m.core.arena[(BitVec.setWidth 64 cref +
            (3 : BitVec 64) + BitVec.setWidth 64 i2).toNat]'hidx2_lt) <<< (1 : Nat)) +
            (1 : BitVec 64)).toNat < st_m.core.wvec.length := by
          rw [helem2, hwv_m_len]; have := hli2.2.2; c0_bound
        have hi2_1 : (i2 + 1#32).toNat = i2.toNat + 1 := by c0_bound
        have hi2_e : (i2 + 1 : BitVec 32) = i2 + 1#32 := rfl; bf_fast
        · exact ih2 _ _ (by dsimp only; rw [hi2_e, hi2_1]; omega) ⟨by rw [hi2_e, hi2_1]; omega,
            by rw [hi2_e, hi2_1]; omega, by rw [helem2]; exact hli2.2.1,
            by rw [helem2]; exact hli2.2.2, hml2⟩
        · exact ih2 _ _ (by dsimp only; rw [hi2_e, hi2_1]; omega)
            ⟨by rw [hi2_e, hi2_1]; omega, by rw [hi2_e, hi2_1]; omega, hml_mem, hml_lt, hml2⟩
      · refine wp_loop_inv (fun (i3, sub, drop, ()) ml3 => i3.toNat ≤ sz.toNat ∧
            FwdDropOk F_cur C drop ∧ (FullMem c st_m ⋆ R) ml3)
          (fun (i3, _, _, _) _ => sz.toNat - i3.toNat) (fun J3 hJ3 => by
            bf_fast_nogrp
            exact hJ3 (0#32, false, 0xFFFFFFFF#32, ()) ml2
              ⟨Nat.zero_le _, fun h => absurd rfl h, hml2⟩)
          (fun J3 (i3, sub, drop, ()) ml3 ⟨hi3_le, hdrop_ok, hml3⟩ ih3 => ?_)
        refine wp_join_group (fun () ml3 => FwdDropOk F_cur C drop ∧ (FullMem c st_m ⋆ R) ml3)
          (fun _ () ml3 ⟨hdrop_ok, hml3⟩ => ?_) (fun J3x hJ3x => ?_)
        · refine wp_loop_inv (fun (ic, ()) mlc => ∃ st_c : FullState,
              AgreesExcept fwdLmMask s st_c ∧ st_c.core.lit_mark.length = 2 * c.max_vars ∧
              ic.toNat ≤ sz.toNat ∧ (∀ x < 2 * c.max_vars, st_c.core.lit_mark[x]?.getD 0#8 ≠ 0#8 →
                ∃ t, ic.toNat ≤ t ∧ t < sz.toNat ∧ C[t]? = some x) ∧ (FullMem c st_c ⋆ R) mlc)
            (fun (ic, ()) _ => sz.toNat - ic.toNat) (fun Jc hJc => by
              bf_fast_nogrp; refine hJc (0#32, ()) ml3 ⟨st_m, hag_m, hlm_m,
                by rw [show (0#32 : BitVec 32).toNat = 0 from rfl]; omega, fun x hx hne => by
                  obtain ⟨t, ht, hct⟩ := (hlm_iff x hx).mp hne
                  exact ⟨t, by rw [show (0#32 : BitVec 32).toNat = 0 from rfl]; omega,
                    by omega, hct⟩, hml3⟩)
            (fun Jc (ic, ()) mlc ⟨st_c, hag_c, hlm_c, hic_le, hclr_inv, hmlc⟩ ihc => ?_)
          have hstc_eq := fwd_lm_reconstruct hag_c
          have har_c : st_c.core.arena = s.core.arena := by rw [hstc_eq]
          have har_c_len : st_c.core.arena.length = c.arena_cap := by rw [har_c]; exact har_len
          bf_step; bf_step
          · bf_fast_nogrp; have hic_lt : ic.toNat < sz.toNat := by c0_bound
            have hidx_clt : (BitVec.setWidth 64 cref + (3 : BitVec 64) +
                BitVec.setWidth 64 ic).toNat < st_c.core.arena.length := by rw [har_c_len]; c0_bound
            have helem_c : st_c.core.arena[(BitVec.setWidth 64 cref + (3 : BitVec 64) +
                BitVec.setWidth 64 ic).toNat]'hidx_clt =
                s.core.arena[cref.toNat + 3 + ic.toNat]'(by omega) := Option.some.inj (by
              rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, har_c,
                show (BitVec.setWidth 64 cref + (3 : BitVec 64) + BitVec.setWidth 64 ic).toNat =
                  cref.toNat + 3 + ic.toNat from by c0_bound])
            have hlic := hC_lit ic.toNat hic_lt
            have hlic_lm : (BitVec.setWidth 64 (st_c.core.arena[(BitVec.setWidth 64 cref +
                (3 : BitVec 64) + BitVec.setWidth 64 ic).toNat]'hidx_clt)).toNat <
                st_c.core.lit_mark.length := by
              rw [helem_c, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), hlm_c]; omega
            have hic1 : (ic + 1#32).toNat = ic.toNat + 1 := by c0_bound
            bf_fast_nogrp; refine ihc _ _ (by
                dsimp only; rw [show (ic + 1 : BitVec 32) = ic + 1#32 from rfl, hic1]; omega)
              ⟨_, by exact hag_c.trans rfl, by simp [hlm_c],
               by rw [show (ic + 1 : BitVec 32) = ic + 1#32 from rfl, hic1]; omega,
               fun x hx hne => ?_, hm⟩
            dsimp only at hne
            have hlic64 : (BitVec.setWidth 64 (st_c.core.arena[(BitVec.setWidth 64 cref +
                (3 : BitVec 64) + BitVec.setWidth 64 ic).toNat]'hidx_clt)).toNat =
                (s.core.arena[cref.toNat + 3 + ic.toNat]'(by omega)).toNat := by
              rw [helem_c, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
            have hxne : x ≠ (s.core.arena[cref.toNat + 3 + ic.toNat]'(by omega)).toNat := by
              intro heq; rw [heq, ← hlic64, List.getElem?_set_self hlic_lm, Option.getD_some] at hne
              exact hne rfl
            rw [List.getElem?_set_ne (by rw [hlic64]; exact Ne.symm hxne)] at hne
            obtain ⟨t, ht1, ht2, hct⟩ := hclr_inv x hx hne
            have htne : t ≠ ic.toNat := by
              intro heq; subst heq; rw [hlic.1] at hct; exact hxne (Option.some.inj hct).symm
            exact ⟨t, by rw [show (ic + 1 : BitVec 32) = ic + 1#32 from rfl, hic1]; omega, ht2, hct⟩
          · have hic_eq : ic.toNat = sz.toNat := by c0_bound
            have hlm_clear_c : ∀ x < 2 * c.max_vars, st_c.core.lit_mark[x]?.getD 0#8 = 0#8 :=
              fun x hx => Classical.byContradiction fun hne => by
                obtain ⟨t, ht1, ht2, _⟩ := hclr_inv x hx hne; omega
            have ⟨hstc_core_eq, hstc_len, hw_c, hdw_c, hrefs_c, hstc_dense⟩ :=
              m5_fwd_cleanup_inv hinv hw hdm hstc_eq hlm_c hlm_clear_c
            bf_fast_nogrp
            · -- `subsumed = true`: mark `PH_GARB`, `fwd_sub_cnt++`, `return true`
              bf_fast
              have hm' : (FullMem c { st_c with
                    core := { st_c.core with
                      arena := st_c.core.arena.set cref.toNat (hdr ||| 0x00080000#32),
                      arena_garbage := st_c.core.arena_garbage + 3#64 + BitVec.setWidth 64 sz },
                    scratch := { st_c.scratch with
                      fwd_sub_cnt := st_c.scratch.fwd_sub_cnt + 1#64 } }
                    ⋆ R) m := by
                simp only [hcref64, hhdr_v, show (524288 : BitVec 32) = 0x00080000#32 from rfl,
                  show (3 : BitVec 64) = 3#64 from rfl, show (1 : BitVec 64) = 1#64 from rfl] at hm
                exact hm
              have ⟨hwg, hdg, hrefs_g⟩ := fullDenseInv_of_markGarb hstc_dense hw_c
                (by rw [hstc_core_eq]; exact href_c)
                (arena' := st_c.core.arena.set cref.toNat (hdr ||| 0x00080000#32))
                (ag' := st_c.core.arena_garbage + 3#64 + BitVec.setWidth 64 sz)
                (cnt' := st_c.scratch.fwd_sub_cnt + 1#64) (by simp [har_c_len])
                (by rw [List.getElem?_set_self (by omega)]
                    unfold fullArenaHdrCore; rw [har_c, List.getElem?_eq_getElem (by omega),
                      Option.getD_some, hhdr_v])
                (fun idx hne _ => List.getElem?_set_ne (Ne.symm hne))
              exact hQ true _ m ⟨hdg.1.lengths, hwg, hdg.2⟩ (by dsimp only; rw [hstc_core_eq])
                (by dsimp only; rw [hstc_core_eq]) (by dsimp only; rw [hstc_core_eq])
                (hrefs_g.trans hrefs_c) (by simp) hm'
            · -- `subsumed = false`: `if (drop != 0xFFFFFFFFu)`
              refine wp_join_group (ts := [i32])
                (fun _ ms => Q (true, ()) ms)
                (fun _ _ ms hq => by bf_fast; exact hq)
                (fun JsOuter hJsOuter => ?_)
              bf_fast_nogrp
              · -- `drop != 0xFFFFFFFFu`: read-only pre-scan `(nsz, l0, l1)`, then `<= 2` vs `> 2`
                have hdrop_ne : drop ≠ 0xFFFFFFFF#32 := hc
                have ⟨hdrop_mem, hfilt_ent⟩ := hdrop_ok hdrop_ne
                have hfilt_lt_sz : (C.filter (· != drop.toNat)).length < sz.toNat := by
                  have := filter_length_lt_of_mem hdrop_mem; omega
                have hhdr_v' : s.core.arena[cref.toNat]'(by omega) =
                    s.core.arena[(BitVec.setWidth 64 cref).toNat]'(by rw [hcref64]; omega) :=
                  Option.some.inj (by
                    rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, hcref64])
                suffices hcomp : wp Γ Q X (m5FwdStrengthenExpr c.hdr c.pArena sz cref drop
                    (s.core.arena[(BitVec.setWidth 64 cref).toNat]'(by rw [hcref64]; omega))
                    JsOuter) mlc by
                  unfold m5FwdStrengthenExpr fwdArIdx3 fwdArOff fwdLd32 fwdSt32 fwdZext64 fwdOp64
                    fwdCmp32 fwdCmp64 at hcomp
                  first | exact hcomp | (dsimp only at hcomp ⊢; exact hcomp)
                exact m5_fwd_strengthen_wp (X := X) hstc_core_eq hstc_len hw_c hdw_c hrefs_c
                  hstc_dense href_c hng_cref hsz_val hsz_ge3 hsz_ar_len hhdr_v' rfl hC_len hC_lit
                  hC_lt hfilt_lt_sz hfilt_ent hUnwatchLarge hAddUnit hAddBin hmlc hQ JsOuter
                  (fun iv ms hq => hJsOuter (iv, ()) ms hq)
              · -- `drop == 0xFFFFFFFFu`: no-op, `return true`
                exact hJsOuter _ _ (hQ true st_c mlc ⟨hstc_len, hw_c, hstc_dense.2⟩
                  (by rw [hstc_core_eq]) (by rw [hstc_core_eq]) (by rw [hstc_core_eq])
                  hrefs_c (by simp) hmlc)
        · bf_fast_nogrp
          all_goals try exact hJ3x () ml3 ⟨hdrop_ok, hml3⟩
          have hi3_lt : i3.toNat < sz.toNat := by c0_bound
          have hi3_1 : (i3 + 1#32).toNat = i3.toNat + 1 := by c0_bound
          have hi3_e : (i3 + 1 : BitVec 32) = i3 + 1#32 := rfl
          refine wp_join_group (fun (x : Tup Val [i32]) ml3 =>
              x.1.toNat ∈ C ∧ x.1.toNat < 2 * s.core.cur_vars ∧ (FullMem c st_m ⋆ R) ml3)
            (fun _ x ml3 ⟨hl0_mem, hl0_lt, hml3⟩ => ?_) (fun Jl0 hJl0 => ?_)
          · obtain ⟨l0, ⟨⟩⟩ := x; dsimp only at hl0_mem hl0_lt
            refine wp_join_group (fun (x : Tup Val [i32]) ml3 =>
                x.1.toNat ∈ C ∧ x.1.toNat < 2 * s.core.cur_vars ∧ (FullMem c st_m ⋆ R) ml3)
              (fun _ x ml3 ⟨hl_mem, hl_lt, hml3⟩ => ?_) (fun Jl hJl => ?_)
            · obtain ⟨l, ⟨⟩⟩ := x; dsimp only at hl_mem hl_lt
              show wp Γ Q X (m5FwdLBlockExpr c.pArena c.pLitMark c.pVals c.pWstk c.pWvec sz cref i3
                sub drop l _) ml3
              exact m5_fwd_lblock_wp hstm_eq hinv hw hdw hlm_m hlm_full hC_ent hl_mem hl_lt hdrop_ok
                hml3
                fun sx dx mx hdx hmx => ih3 _ _ (by dsimp only; rw [hi3_e, hi3_1]; omega)
                  ⟨by rw [hi3_e, hi3_1]; omega, hdx, hmx⟩
            · bf_fast
              · exact hJl (_, ()) ml3 ⟨hl0_elem ▸ hl0_info.2.1, hl0_elem ▸ hl0_info.2.2, hml3⟩
              all_goals exact hJl (l0, ()) ml3 ⟨hl0_mem, hl0_lt, hml3⟩
          · have hidx3_lt : (BitVec.setWidth 64 cref + (3 : BitVec 64) +
                BitVec.setWidth 64 i3).toNat < st_m.core.arena.length := by
              rw [har_m_len]; c0_bound
            have helem3 : st_m.core.arena[(BitVec.setWidth 64 cref + (3 : BitVec 64) +
                BitVec.setWidth 64 i3).toNat]'hidx3_lt =
                s.core.arena[cref.toNat + 3 + i3.toNat]'(by omega) := Option.some.inj (by
              rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, har_m, show
                (BitVec.setWidth 64 cref + (3 : BitVec 64) + BitVec.setWidth 64 i3).toNat =
                cref.toNat + 3 + i3.toNat from by c0_bound])
            have hli3 := hC_lit i3.toNat hi3_lt; bf_fast
            · exact hJl0 (min_l, ()) ml3 ⟨hml_mem, hml_lt, hml3⟩
            · exact hJl0 (_, ()) ml3 ⟨helem3 ▸ hli3.2.1, helem3 ▸ hli3.2.2, hml3⟩

end LeanQbe.T.Examples.Kissat.FullM5DenseSafe
