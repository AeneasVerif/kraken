/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Definition.WpM7DefK6Helpers1
public import LeanQbe.T.Examples.Kissat.Src.Definition

/-!
# Kissat M7 K6 Definition Extraction WP Proof (`Proof.Definition.WpM7DefK6`)

Flat `CanonicalEnv` `Func.wp` proof for `full_bve_def_k6_m7` (`Spec.fullBveGatesM7Spec`).

`0` legacy `Full*` imports; `0` `@[expose]` on theorems/lemmas/sections; every decl `<= 450` LOC;
every line `<= 100` cols.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Definition

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Definition
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Definition.Spec
open Kraken.Bedrock2.Test

open scoped FullArenaTactics P6Tactics

local macro_rules
  | `(tactic| c0_bound) => `(tactic| first | assumption | rfl | decide |
      ((try dsimp only); (repeat rw [List.length_set]); omega))

/-! ## 1. Pure & State Helpers -/

private theorem m7_p6_entry_of_core_eq {F_cur : List (List Nat)} {s1 s2 : FullState}
    {lit : Nat} {w : BitVec 32}
    (hcv : s1.core.cur_vars = s2.core.cur_vars)
    (har : s1.core.arena = s2.core.arena)
    (hal : s1.core.arena_len = s2.core.arena_len) :
    FullBveEntryOkW F_cur s1 lit w → FullBveEntryOkW F_cur s2 lit w := by
  unfold FullBveEntryOkW fullArenaClauseRefs fullArenaClauseGarb
    fullArenaClauseRefsCore fullArenaClauseGarbCore fullArenaHdrCore
  rw [hcv, har, hal]; exact id

private theorem m7_p6_gates_inv_exit {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    (s0 : FullState) {np nn : BitVec 32} {R : Mem 64 → Prop}
    {s : FullState} {m : Mem 64}
    (hinv' : FullDenseInvW c F0 F_cur s)
    (htmk' : Spec.TmkZero s)
    (hcv : s.core.cur_vars = s0.core.cur_vars)
    (har : s.core.arena = s0.core.arena)
    (harl : s.core.arena_len = s0.core.arena_len)
    (hfl : s.core.fuel.toNat ≤ s0.core.fuel.toNat)
    (hpres : ∀ k < 1024, s.scratch.scratch_buf[k]? = s0.scratch.scratch_buf[k]?)
    (hm : (FullMem c s ⋆ R) m)
    (hnp : np.toNat ≤ 512) (hnn : nn.toNat ≤ 512)
    {Q : Post []}
    (hQ : ∀ (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → Spec.TmkZero s' →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.arena = s0.core.arena →
      s'.core.arena_len = s0.core.arena_len → s'.core.fuel.toNat ≤ s0.core.fuel.toNat →
      (∀ i < np.toNat, s'.scratch.scratch_buf[i]? = s0.scratch.scratch_buf[i]?) →
      (∀ j < nn.toNat, s'.scratch.scratch_buf[512 + j]? = s0.scratch.scratch_buf[512 + j]?) →
      (FullMem c s' ⋆ R) m' → Q () m') :
    Q () m :=
  hQ s m hinv' htmk' hcv har harl hfl
    (fun i hi => hpres i (by omega))
    (fun j hj => hpres (512 + j) (by omega))
    hm

private def m7_p6_clr_state (s0 : FullState) (tmp exp tmk scr : List (BitVec 32)) : FullState :=
  { core := { s0.core with tmp := tmp },
    scratch := { s0.scratch with wsort := exp, tarjan_mark := tmk, scratch_buf := scr } }

private theorem m7_p6_side_init_inv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hinv : FullDenseInvW c F0 F_cur s0) (htmk0 : Spec.TmkZero s0)
    (hm : (FullMem c s0 ⋆ R) m) :
    M7P6SideInv c s0 R (c.scratch_cap - 4008) 0#32 0#32 0#32 0#32 0xFFFFFFFF#32 m := by
  refine ⟨s0.scratch.wsort, s0.scratch.tarjan_mark, s0.core.tmp, s0.scratch.scratch_buf,
    hinv.1.core_ok.tmp_len_arr, hinv.1.scratch_ok.scratch_buf_len, fun _ _ => rfl, ?_, ?_,
    ?_, m7_p6_fullMem_subst hm rfl rfl⟩
  · refine ⟨hinv.1.scratch_ok.wsort_len, hinv.1.scratch_ok.tarjan_mark_len,
      by simp, by simp, fun _ hk => by simp at hk, fun u hu hne => ?_⟩
    exfalso; exact hne (htmk0 u hu)
  · exact ⟨by simp, by simp, by simp, fun _ h => by simp at h⟩
  · intro hne; exfalso; exact hne rfl

private theorem m7_p6_side_setup_wide {F_cur : List (List Nat)} {s0 : FullState}
    {v np nn side cnt off except : BitVec 32}
    (hcv : s0.core.cur_vars ≤ 2 ^ 29 - 1)
    (hv : v.toNat < s0.core.cur_vars) (hnp : np.toNat ≤ 128) (hnn : nn.toNat ≤ 128)
    (_hside : side.toNat < 2)
    (hpos : ∀ i < np.toNat, FullBveEntryOkW F_cur s0 (2 * v.toNat)
      (s0.scratch.scratch_buf[i]?.getD 0#32))
    (hneg : ∀ j < nn.toNat, FullBveEntryOkW F_cur s0 (2 * v.toNat + 1)
      (s0.scratch.scratch_buf[512 + j]?.getD 0#32))
    (hcnt : (side = 0#32 → cnt = np) ∧ (side ≠ 0#32 → cnt = nn))
    (hoff : (side = 0#32 → off = 0#32) ∧ (side ≠ 0#32 → off = 512#32))
    (hex : (side = 0#32 → except = v <<< 1) ∧ (side ≠ 0#32 → except = (v <<< 1) ||| 1#32)) :
    cnt.toNat ≤ 128 ∧ off.toNat + cnt.toNat ≤ 1024 ∧ except.toNat < 2 * s0.core.cur_vars ∧
    ∀ j < cnt.toNat, FullBveEntryOkW F_cur s0 except.toNat
      (s0.scratch.scratch_buf[off.toNat + j]?.getD 0#32) := by
  have hlt : 2 * v.toNat + 1 < 2 ^ 32 := by omega
  have hshl : (v <<< 1).toNat = 2 * v.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm,
      Nat.mod_eq_of_lt (by omega)]
  have hor : ((v <<< 1) ||| 1#32).toNat = 2 * v.toNat + 1 := by
    rw [BitVec.toNat_or, hshl, show (1#32 : BitVec 32).toNat = 1 from rfl]
    apply Nat.eq_of_testBit_eq; intro i; cases i with
    | zero => simp [Nat.testBit_zero, show (2 * v.toNat + 1) % 2 = 1 by omega]
    | succ j =>
      rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ,
        Nat.mul_add_div (by omega : 0 < 2), Nat.mul_div_right _ (by omega)]
      simp
  by_cases hs : side = 0#32
  · rw [hcnt.1 hs, hoff.1 hs, hex.1 hs, hshl]
    exact ⟨hnp, by simp; omega, by omega, fun j hj => by simp; exact hpos j hj⟩
  · rw [hcnt.2 hs, hoff.2 hs, hex.2 hs, hor]
    exact ⟨hnn, by simp; omega, by omega, fun j hj => hneg j hj⟩

private theorem m7_p6_arena_clause_bounds {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} (hinv : FullDenseInvW c F0 F_cur s0) {lit : Nat} {w : BitVec 32}
    (hok : FullBveEntryOkW F_cur s0 lit w) (hnotbin : w &&& 0x80000000#32 = 0#32) :
    let sz := s0.core.arena[w.toNat + 2]?.getD 0#32
    w.toNat + 2 < s0.core.arena.length ∧
    w.toNat + 3 + sz.toNat ≤ s0.core.arena_len ∧
    ∀ j < sz.toNat, (s0.core.arena[w.toNat + 3 + j]?.getD 0#32).toNat < 2 * s0.core.cur_vars := by
  have hok' := hok
  unfold FullBveEntryOkW at hok'
  simp only [hnotbin, ne_eq, not_true_eq_false, ↓reduceIte] at hok'
  rcases hok' with ⟨hw_ref, hw_garb⟩
  obtain ⟨hw_lo, hw_sz, hw_end, hnext_le, _⟩ := hinv.2.1.arena.refs_wf w.toNat hw_ref
  have hsz_eq : (s0.core.arena[w.toNat + 2]?.getD 0#32).toNat =
      fullArenaClauseSizeCore s0.core w.toNat := rfl
  have har_len : s0.core.arena_len ≤ s0.core.arena.length := by
    rw [hinv.1.core_ok.arena_len_arr]; exact hinv.1.core_ok.arena_len_le
  refine ⟨by omega, by omega, fun j hj => ?_⟩
  apply hinv.2.1.arena.lits_lt w.toNat hw_ref hw_garb
  have hj_ar : w.toNat + 3 + j < s0.core.arena.length := by omega
  have hmem : s0.core.arena[w.toNat + 3 + j]'hj_ar ∈
      List.take (fullArenaClauseSizeCore s0.core w.toNat)
        (List.drop (w.toNat + 3) s0.core.arena) := by
    rw [List.mem_iff_getElem]
    refine ⟨j, by rw [List.length_take, List.length_drop]; omega, ?_⟩
    rw [List.getElem_take, List.getElem_drop]
  rw [List.getElem?_eq_getElem hj_ar, Option.getD_some]
  exact List.mem_map_of_mem hmem

/-! ## 2. Inner Loop Branch Helpers (`G8` Binary & Large Cases) -/

@[reducible] private def m7_p6_bin_expr (J7 : Cont [i32, i32, i32, i32, i32, Ty.bool, i32])
    (B71 : Cont [i32, i32, i32, i32, i32, Ty.bool]) (c : FullCfg)
    (nv nc al nu teid j ld eid' : BitVec 32) (ab : Bool) (pk : BitVec 64)
    (acap_v : BitVec 32) : Expr Val Cont [] :=
  Expr.let_ (Op.mk (OpCode.and i32) (Arg.var ld, Arg.imm 0x7FFFFFFF#32, ())) fun p_10 =>
  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_10.fst, ())) fun p_11 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pVals, Arg.var p_11.fst, ())) fun p_12 =>
  Expr.load i8 (Arg.var p_12.fst) fun ld_v =>
  Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm 0, ())) fun p_13 =>
  Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var ld_v, ())) fun p_14 =>
  Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var p_13.fst, ())) fun p_15 =>
  Expr.let_ (Op.mk (OpCode.cmp .slt i32 .bool rfl) (Arg.var p_14.fst, Arg.var p_15.fst, ()))
    fun p_16 =>
  Expr.jnz (Arg.var p_16.fst)
    (Expr.jump J7 (Arg.var nv, Arg.var nc, Arg.var al, Arg.var nu,
      Arg.var eid', Arg.var ab, Arg.var j, ()))
    (Expr.group (fun _Ls : Tup Cont [[i32, i32, i32, i32, Ty.bool]] =>
      Blocks.cons (fun p : Tup Val [i32, i32, i32, i32, Ty.bool] =>
        Expr.jump B71 (Arg.var p.fst, Arg.var p.snd.fst, Arg.var p.snd.snd.fst,
          Arg.var p.snd.snd.snd.fst, Arg.var teid, Arg.var p.snd.snd.snd.snd.fst, ()))
      Blocks.nil)
      fun Ls =>
      Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm 0, ())) fun p_17 =>
      Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var ld_v, ())) fun p_18 =>
      Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var p_17.fst, ())) fun p_19 =>
      Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl) (Arg.var p_18.fst, Arg.var p_19.fst, ()))
        fun p_20 =>
      Expr.jnz (Arg.var p_20.fst)
        (Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var p_10.fst, Arg.imm 1, ())) fun lv =>
        Expr.group (fun _Lt : Tup Cont [[i32, Ty.bool]] =>
          Blocks.cons (fun pt : Tup Val [i32, Ty.bool] =>
          Expr.let_ (Op.mk (OpCode.cmp .uge i32 .bool rfl) (Arg.var nc, Arg.imm 128, ()))
            fun pc1 =>
          Expr.jnz (Arg.var pc1.fst)
            (Expr.jump J7 (Arg.var pt.fst, Arg.var nc, Arg.var al, Arg.var nu,
              Arg.var teid, Arg.imm true, Arg.var j, ()))
            (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var al, Arg.imm 1, ())) fun pal1 =>
            Expr.let_ (Op.mk (OpCode.cmp .ugt i32 .bool rfl)
              (Arg.var pal1.fst, Arg.var acap_v, ())) fun pc2 =>
            Expr.jnz (Arg.var pc2.fst)
              (Expr.jump J7 (Arg.var pt.fst, Arg.var nc, Arg.var al, Arg.var nu,
                Arg.var teid, Arg.imm true, Arg.var j, ()))
              (Expr.let_ (Op.mk (OpCode.add i32) (Arg.imm 2912, Arg.var al, ())) fun pd1 =>
              Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var pd1.fst, ())) fun pd2 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var pd2.fst, Arg.imm 4, ())) fun pd3 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pk, Arg.var pd3.fst, ())) fun pd4 =>
              Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var lv.fst, ())) fun pt1 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var pt1.fst, Arg.imm 4, ())) fun pt2 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pTarjanMark, Arg.var pt2.fst, ()))
                fun pt3 =>
              Expr.load i32 (Arg.var pt3.fst) fun tmkv =>
              Expr.let_ (Op.mk (OpCode.sub i32) (Arg.var tmkv, Arg.imm 1, ())) fun pl1 =>
              Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var pl1.fst, Arg.imm 1, ())) fun pl2 =>
              Expr.let_ (Op.mk (OpCode.and i32) (Arg.var p_10.fst, Arg.imm 1, ())) fun pl3 =>
              Expr.let_ (Op.mk (OpCode.or i32) (Arg.var pl2.fst, Arg.var pl3.fst, ())) fun ulit =>
              Expr.store (@Arg.var Val i32 ulit.fst) (Arg.var pd4.fst)
              (Expr.let_ (Op.mk (OpCode.add i32) (Arg.imm 1888, Arg.var nc, ())) fun po1 =>
              Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var po1.fst, ())) fun po2 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var po2.fst, Arg.imm 4, ())) fun po3 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pk, Arg.var po3.fst, ())) fun po4 =>
              Expr.store (@Arg.var Val i32 al) (Arg.var po4.fst)
              (Expr.let_ (Op.mk (OpCode.add i32) (Arg.imm 2144, Arg.var nc, ())) fun pm1 =>
              Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var pm1.fst, ())) fun pm2 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var pm2.fst, Arg.imm 4, ())) fun pm3 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pk, Arg.var pm3.fst, ())) fun pm4 =>
              Expr.store (@Arg.imm Val i32 1#32) (Arg.var pm4.fst)
              (Expr.let_ (Op.mk (OpCode.add i32) (Arg.imm 2400, Arg.var nc, ())) fun pe1 =>
              Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var pe1.fst, ())) fun pe2 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var pe2.fst, Arg.imm 4, ())) fun pe3 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pk, Arg.var pe3.fst, ())) fun pe4 =>
              Expr.store (@Arg.var Val i32 eid') (Arg.var pe4.fst)
              (Expr.let_ (Op.mk (OpCode.add i32) (Arg.imm 2656, Arg.var nu, ())) fun pu1 =>
              Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var pu1.fst, ())) fun pu2 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var pu2.fst, Arg.imm 4, ())) fun pu3 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pk, Arg.var pu3.fst, ())) fun pu4 =>
              Expr.store (@Arg.var Val i32 nc) (Arg.var pu4.fst)
              (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var nu, Arg.imm 1, ())) fun pnu1 =>
              Expr.let_ (Op.mk (OpCode.add i32) (Arg.var nc, Arg.imm 1, ())) fun pnc1 =>
              Expr.let_ (Op.mk (OpCode.add i32) (Arg.var al, Arg.imm 1, ())) fun paln =>
              Expr.jump Ls.fst (Arg.var pt.fst, Arg.var pnc1.fst, Arg.var paln.fst,
                Arg.var pnu1.fst, Arg.var pt.snd.fst, ()))))))))) Blocks.nil)
          fun Lt =>
          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var lv.fst, ())) fun pv1 =>
          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var pv1.fst, Arg.imm 4, ())) fun pv2 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pTarjanMark, Arg.var pv2.fst, ()))
            fun pv3 =>
          Expr.load i32 (Arg.var pv3.fst) fun tmk0 =>
          Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl) (Arg.var tmk0, Arg.imm 0, ())) fun ptz =>
          Expr.jnz (Arg.var ptz.fst)
            (Expr.let_ (Op.mk (OpCode.cmp .uge i32 .bool rfl) (Arg.var nv, Arg.imm 64, ()))
              fun pn1 =>
            Expr.jnz (Arg.var pn1.fst)
              (Expr.jump J7 (Arg.var nv, Arg.var nc, Arg.var al, Arg.var nu,
                Arg.var teid, Arg.imm true, Arg.var j, ()))
              (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var nv, ())) fun pn2 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 776, ())) fun pn3 =>
              Expr.load i64 (Arg.var pn3.fst) fun lcv =>
              Expr.let_ (Op.mk (OpCode.sext 32 64) (Arg.imm 1, ())) fun pn4 =>
              Expr.let_ (Op.mk (OpCode.shl i64) (Arg.var lcv, Arg.var pn4.fst, ())) fun pn5 =>
              Expr.let_ (Op.mk (OpCode.cmp .uge i64 .bool rfl)
                (Arg.var pn2.fst, Arg.var pn5.fst, ())) fun pn6 =>
              Expr.jnz (Arg.var pn6.fst)
                (Expr.jump J7 (Arg.var nv, Arg.var nc, Arg.var al, Arg.var nu,
                  Arg.var teid, Arg.imm true, Arg.var j, ()))
                (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var nv, ())) fun pe1 =>
                Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var pe1.fst, Arg.imm 4, ())) fun pe2 =>
                Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pWsort, Arg.var pe2.fst, ()))
                  fun pe3 =>
                Expr.store (@Arg.var Val i32 lv.fst) (Arg.var pe3.fst)
                (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var nv, Arg.imm 1, ())) fun pnv1 =>
                Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var lv.fst, ())) fun ptl1 =>
                Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var ptl1.fst, Arg.imm 4, ())) fun ptl2 =>
                Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pTarjanMark, Arg.var ptl2.fst, ()))
                  fun ptl3 =>
                Expr.store (@Arg.var Val i32 pnv1.fst) (Arg.var ptl3.fst)
                (Expr.jump Lt.fst (Arg.var pnv1.fst, Arg.var ab, ()))))))
            (Expr.jump Lt.fst (Arg.var nv, Arg.var ab, ())))
        (Expr.jump Ls.fst (Arg.var nv, Arg.var nc, Arg.var al, Arg.var nu, Arg.var ab, ())))

private theorem m7_p6_bin_branch_wp (Γ : Env) (Q : Post []) (X : XPost)
    (J7 : Cont [i32, i32, i32, i32, i32, Ty.bool, i32])
    (B71 : Cont [i32, i32, i32, i32, i32, Ty.bool])
    (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s0 : FullState)
    (R : Mem 64 → Prop) (hinv : FullDenseInvW c F0 F_cur s0)
    (h8192 : 8192 ≤ c.scratch_cap) (hcap_lt : c.scratch_cap < 2 ^ 28)
    (nv nc al nu teid j ex ld eid' : BitVec 32) (ab : Bool) (pk : BitVec 64)
    (acap_v : BitVec 32) (exp tmk tmp scr : List (BitVec 32)) (m : Mem 64)
    (htmp_len : tmp.length = c.max_vars) (hscr_len : scr.length = c.scratch_cap)
    (hpres : ∀ k < 1096, scr[k]? = s0.scratch.scratch_buf[k]?)
    (hte : M7P6TmkExpInv c s0 nv exp tmk)
    (hcls : M7P6ClsInv nc al nu (c.scratch_cap - 4008) scr)
    (hteid_bd : teid ≠ 0xFFFFFFFF#32 → (teid &&& 1023#32).toNat < 512)
    (heid'_bd : eid' ≠ 0xFFFFFFFF#32 ∧ (eid' &&& 1023#32).toNat < 512)
    (hm_st : (FullMem c (m7_p6_clr_state s0 tmp exp tmk scr) ⋆ R) m)
    (hab : ab = false) (hnv64 : nv.toNat ≤ 64) (hnc128 : nc.toNat ≤ 128)
    (hpk : pk = c.pScratchBuf + 1096#64 * 4)
    (hacap : acap_v = BitVec.ofNat 32 (c.scratch_cap - 4008))
    (hfull : FullBveEntryOkW F_cur s0 ex.toNat ld) (hbin : ld &&& 0x80000000#32 ≠ 0#32)
    (hJ7 : ∀ st m', (∃ nv' nc' al' nu' teid' j' : BitVec 32, ∃ ab' : Bool,
      st = (nv', nc', al', nu', teid', ab', j', ()) ∧
      nv'.toNat ≤ 64 ∧ nc'.toNat ≤ 128 ∧
      M7P6SideInv c s0 R (c.scratch_cap - 4008) nv' nc' al' nu' teid' m') → J7 st m')
    (hB71 : ∀ st m', (∃ nv' nc' al' nu' teid' : BitVec 32, ∃ ab' : Bool,
      st = (nv', nc', al', nu', teid', ab', ()) ∧
      nv'.toNat ≤ 64 ∧ nc'.toNat ≤ 128 ∧
      M7P6SideInv c s0 R (c.scratch_cap - 4008) nv' nc' al' nu' teid m') → B71 st m') :
    wp Γ Q X (m7_p6_bin_expr J7 B71 c nv nc al nu teid j ld eid' ab pk acap_v) m := by
  have hlid_lt : (ld &&& 0x7FFFFFFF#32).toNat < 2 * s0.core.cur_vars := by
    have hok' := hfull; unfold FullBveEntryOkW at hok'
    simp only [hbin, ne_eq, not_false_eq_true, ↓reduceIte] at hok'
    exact hok'.1
  have hvals_clr : (m7_p6_clr_state s0 tmp exp tmk scr).core.vals.length = 2 * c.max_vars :=
    hinv.1.core_ok.vals_len
  have hlid_vals : (ld &&& 0x7FFFFFFF#32).toNat <
      (m7_p6_clr_state s0 tmp exp tmk scr).core.vals.length := by
    have := hinv.1.core_ok.cur_vars_le; omega
  dsimp only [m7_p6_bin_expr]
  c0_hsteps_nogrp
  c0_hsplit
  · c0_hsteps!
    exact hJ7 _ m ⟨nv, nc, al, nu, eid', j, ab, rfl, hnv64, hnc128,
      exp, tmk, tmp, scr, htmp_len, hscr_len, hpres, hte, hcls, fun _ => heid'_bd.2, hm_st⟩
  · c0_hsteps_nogrp
    refine wp_join_state (ts := [i32, i32, i32, i32, Ty.bool]) (fun p => p)
      (fun p m' => ∃ nv' nc' al' nu' : BitVec 32, ∃ ab' : Bool,
        p = (nv', nc', al', nu', ab', ()) ∧ nv'.toNat ≤ 64 ∧ nc'.toNat ≤ 128 ∧
        M7P6SideInv c s0 R (c.scratch_cap - 4008) nv' nc' al' nu' teid m') ?_ ?_
    · intro _ ⟨nv', nc', al', nu', ab', ⟨⟩⟩ m' ⟨_, _, _, _, _, heqp, hnv'64, hnc'128, hside'⟩
      cases heqp; c0_hsteps!
      exact hB71 _ m' ⟨nv', nc', al', nu', teid, ab', rfl, hnv'64, hnc'128, hside'⟩
    · intro B82 hB82
      let lid := ld &&& 0x7FFFFFFF#32
      let lv := lid >>> (1 : BitVec 32)
      have hdiv : lv.toNat = lid.toNat / 2 := by
        rw [show lv = lid >>> (1 : Nat) from rfl, BitVec.toNat_ushiftRight,
          Nat.shiftRight_eq_div_pow]
      have hdiv64 : (BitVec.setWidth 64 ((ld &&& 0x7FFFFFFF#32) >>> (1 : BitVec 32))).toNat =
          (ld &&& 0x7FFFFFFF#32).toNat / 2 := by
        rw [BitVec.toNat_setWidth, show ((ld &&& 0x7FFFFFFF#32) >>> (1 : BitVec 32)).toNat =
          (ld &&& 0x7FFFFFFF#32).toNat / 2 from hdiv]
        exact Nat.mod_eq_of_lt (by omega)
      have hlv_cv : lv.toNat < s0.core.cur_vars := by
        rw [hdiv]; dsimp only [lid]; omega
      have hcv_mc : s0.core.cur_vars ≤ c.max_vars := hinv.1.core_ok.cur_vars_le
      have htmk_len : (m7_p6_clr_state s0 tmp exp tmk scr).scratch.tarjan_mark.length =
          2 * c.max_vars := hte.2.1
      have hexp_len : (m7_p6_clr_state s0 tmp exp tmk scr).scratch.wsort.length =
          2 * c.max_vars := hte.1
      have hlv_tmk0 : (BitVec.setWidth 64 lv).toNat <
          (m7_p6_clr_state s0 tmp exp tmk scr).scratch.tarjan_mark.length := by
        dsimp only [m7_p6_clr_state]; rw [hte.2.1, hdiv64]; omega
      c0_hsplit
      · c0_hsteps_nogrp
        refine wp_join_state (ts := [i32, Ty.bool]) (fun p => p)
          (fun p m' => ∃ nv_a : BitVec 32, ∃ ab_a : Bool, p = (nv_a, ab_a, ()) ∧
            nv_a.toNat ≤ 64 ∧ M7P6TmkJoinInv c s0 R tmp scr lv nv_a ab_a m') ?_ ?_
        · intro _ ⟨nv_a, ab_a, ⟨⟩⟩ m' ⟨_, _, heqp, hnv_a64, hab_a, exp_a, tmk_a, hte_a,
            htmk_lo, htmk_hi, hm_a⟩
          cases heqp; subst hab_a
          c0_hsplit
          · c0_hsteps!
            exact hJ7 _ m' ⟨nv_a, nc, al, nu, teid, j, true, rfl, hnv_a64, hnc128,
              exp_a, tmk_a, tmp, scr, htmp_len, hscr_len, hpres, hte_a, hcls, hteid_bd, hm_a⟩
          · c0_hsplit
            · c0_hsteps!
              exact hJ7 _ m' ⟨nv_a, nc, al, nu, teid, j, true, rfl, hnv_a64, hnc128,
                exp_a, tmk_a, tmp, scr, htmp_len, hscr_len, hpres, hte_a, hcls, hteid_bd, hm_a⟩
            · have hnc_lt : nc.toNat < 128 := by
                have hc' : ¬128 ≤ nc.toNat := by c0_bound
                omega
              have hal1_le : al.toNat + 1 ≤ c.scratch_cap - 4008 := by
                have h1 : acap_v.toNat = c.scratch_cap - 4008 := by
                  rw [hacap, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                have h2 : ¬acap_v.toNat < (al + 1#32).toNat := by c0_bound
                have hal_bd : al.toNat ≤ c.scratch_cap - 4008 := hcls.2.2.1
                have hal_eq : (al + 1#32).toNat = al.toNat + 1 := by bv_omega
                omega
              have hnu_lt : nu.toNat < 128 := by have := hcls.2.1; omega
              have hlv_tmk : (BitVec.setWidth 64 lv).toNat <
                  (m7_p6_clr_state s0 tmp exp_a tmk_a scr).scratch.tarjan_mark.length := by
                dsimp only [m7_p6_clr_state]; rw [hte_a.2.1, hdiv64]; omega
              have hbd1 : 1096 + (BitVec.setWidth 64 ((2912 : BitVec 32) + al)).toNat <
                  (m7_p6_clr_state s0 tmp exp_a tmk_a scr).scratch.scratch_buf.length := by
                dsimp only [m7_p6_clr_state]
                rw [hscr_len, m7_p6_off_add 2912 (by decide) al (by omega)]; omega
              have hbd2 : 1096 + (BitVec.setWidth 64 ((1888 : BitVec 32) + nc)).toNat <
                  (m7_p6_clr_state s0 tmp exp_a tmk_a scr).scratch.scratch_buf.length := by
                dsimp only [m7_p6_clr_state]
                rw [hscr_len, m7_p6_off_add 1888 (by decide) nc (by omega)]; omega
              have hbd3 : 1096 + (BitVec.setWidth 64 ((2144 : BitVec 32) + nc)).toNat <
                  (m7_p6_clr_state s0 tmp exp_a tmk_a scr).scratch.scratch_buf.length := by
                dsimp only [m7_p6_clr_state]
                rw [hscr_len, m7_p6_off_add 2144 (by decide) nc (by omega)]; omega
              have hbd4 : 1096 + (BitVec.setWidth 64 ((2400 : BitVec 32) + nc)).toNat <
                  (m7_p6_clr_state s0 tmp exp_a tmk_a scr).scratch.scratch_buf.length := by
                dsimp only [m7_p6_clr_state]
                rw [hscr_len, m7_p6_off_add 2400 (by decide) nc (by omega)]; omega
              have hbd5 : 1096 + (BitVec.setWidth 64 ((2656 : BitVec 32) + nu)).toNat <
                  (m7_p6_clr_state s0 tmp exp_a tmk_a scr).scratch.scratch_buf.length := by
                dsimp only [m7_p6_clr_state]
                rw [hscr_len, m7_p6_off_add 2656 (by decide) nu (by omega)]; omega
              subst hpk
              c0_hsteps!
              have hnc1 : (nc + 1#32).toNat = nc.toNat + 1 := by bv_omega
              have hal1 : (al + 1#32).toNat = al.toNat + 1 := by bv_omega
              have hnu1 : (nu + 1#32).toNat = nu.toNat + 1 := by bv_omega
              have hlvt_bd : lv.toNat < tmk_a.length := by rw [hte_a.2.1]; omega
              obtain ⟨hscr_u, hpres_u, hcls_u⟩ :=
                m7_p6_bin_unit_commit (tmkv := tmk_a[lv.toNat]'hlvt_bd) (l := lid)
                  (eid := eid') hpres hcls hscr_len (by omega) hal1 hal1_le hnc1 hnc_lt hnu1
              have hal_off : (BitVec.setWidth 64 ((2912 : BitVec 32) + al)).toNat =
                  2912 + al.toNat := m7_p6_off_add 2912 (by decide) al (by omega)
              have h1888 : (BitVec.setWidth 64 ((1888 : BitVec 32) + nc)).toNat =
                  1888 + nc.toNat := m7_p6_off_add 1888 (by decide) nc (by omega)
              have h2144 : (BitVec.setWidth 64 ((2144 : BitVec 32) + nc)).toNat =
                  2144 + nc.toNat := m7_p6_off_add 2144 (by decide) nc (by omega)
              have h2400 : (BitVec.setWidth 64 ((2400 : BitVec 32) + nc)).toNat =
                  2400 + nc.toNat := m7_p6_off_add 2400 (by decide) nc (by omega)
              have h2656 : (BitVec.setWidth 64 ((2656 : BitVec 32) + nu)).toNat =
                  2656 + nu.toNat := m7_p6_off_add 2656 (by decide) nu (by omega)
              clear hm_st
              refine hB82 _ _ ⟨nv_a, nc + 1#32, al + 1#32, nu + 1#32, false, rfl, hnv_a64,
                by omega, exp_a, tmk_a, tmp, _, htmp_len, hscr_u, hpres_u, hte_a, hcls_u,
                hteid_bd, ?_⟩
              refine Eq.mp (congrArg (fun x => (FullMem c x ⋆ R) _) ?_) ‹(FullMem c _ ⋆ R) _›
              simp only [hal_off, h1888, h2144, h2400, h2656, Nat.add_assoc,
                show lv.toNat = (ld &&& 0x7FFFFFFF#32).toNat / 2 from hdiv]; rfl
        · intro B88 hB88
          c0_hsteps_nogrp
          · exact hJ7 _ m ⟨nv, nc, al, nu, teid, j, true, rfl, hnv64, hnc128,
              exp, tmk, tmp, scr, htmp_len, hscr_len, hpres, hte, hcls, hteid_bd, hm_st⟩
          · exact hJ7 _ m ⟨nv, nc, al, nu, teid, j, true, rfl, hnv64, hnc128,
              exp, tmk, tmp, scr, htmp_len, hscr_len, hpres, hte, hcls, hteid_bd, hm_st⟩
          · have hnv_lt64 : nv.toNat < 64 := by c0_bound
            have hnv_lt2cv : nv.toNat < 2 * s0.core.cur_vars := by
              dsimp only [m7_p6_clr_state] at hc
              have := hinv.1.core_ok.cur_vars_le; have := c.hmaxv
              rw [show dimacsBound = 2 ^ 28 from rfl] at *; omega
            have hnv_wsort : (BitVec.setWidth 64 nv).toNat <
                (m7_p6_clr_state s0 tmp exp tmk scr).scratch.wsort.length := by
              dsimp only [m7_p6_clr_state]; rw [hte.1]
              have : (BitVec.setWidth 64 nv).toNat = nv.toNat := by bv_omega
              omega
            c0_hsteps!
            obtain ⟨hnv1, hnv64', hnv2cv', hexp', htmk', htmk_lo, htmk_hi⟩ :=
              m7_p6_tmk_reg hnv_lt64 hnv_lt2cv (by rw [hte.1]; omega) hte.2.1 hcv_mc hlv_cv
                hte.2.2.2.2.1 hte.2.2.2.2.2
            refine hB88 _ _ ⟨nv + 1#32, ab, rfl, hnv64', hab, exp.set nv.toNat lv,
              tmk.set lv.toNat (nv + 1#32),
              ⟨by rw [List.length_set, hte.1], by rw [List.length_set, hte.2.1],
               hnv64', hnv2cv', hexp', htmk'⟩, htmk_lo, htmk_hi, ?_⟩
            refine Eq.mp (congrArg (fun x => (FullMem c x ⋆ R) _) ?_) ‹(FullMem c _ ⋆ R) _›
            have h1 : (BitVec.setWidth 64 nv).toNat = nv.toNat := by bv_omega
            simp only [m7_p6_clr_state, h1, lv, lid,
              show lv.toNat = lid.toNat / 2 from hdiv]; rfl
          · have htmk_nz : tmk[lv.toNat]?.getD 0#32 ≠ 0#32 := by
              rw [List.getElem?_eq_getElem (by rw [hte.2.1]; omega : lv.toNat < tmk.length),
                Option.getD_some]
              c0_bound
            obtain ⟨htmk_lo, htmk_hi, _⟩ := hte.2.2.2.2.2 lv.toNat hlv_cv htmk_nz
            exact hB88 _ m ⟨nv, ab, rfl, hnv64, hab, exp, tmk, hte, htmk_lo, htmk_hi, hm_st⟩
      · c0_hsteps!
        exact hB82 _ m ⟨nv, nc, al, nu, ab, rfl, hnv64, hnc128,
          exp, tmk, tmp, scr, htmp_len, hscr_len, hpres, hte, hcls, hteid_bd, hm_st⟩

@[reducible] private def m7_p6_large_expr (J7 : Cont [i32, i32, i32, i32, i32, Ty.bool, i32])
    (B71 : Cont [i32, i32, i32, i32, i32, Ty.bool]) (c : FullCfg) (mc : BitVec 32)
    (nv nc al nu teid j ex w eid' : BitVec 32) (ab : Bool) (pk : BitVec 64)
    (acap_v : BitVec 32) : Expr Val Cont [] :=
  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var w, ())) fun p_10 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p_10.fst, Arg.imm 2, ())) fun p_11 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_11.fst, Arg.imm 4, ())) fun p_12 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pArena, Arg.var p_12.fst, ())) fun p_13 =>
  Expr.load i32 (Arg.var p_13.fst) fun sz =>
  Expr.group (fun _Bm : Tup Cont [[i32, Ty.bool, Ty.bool, i32, i32]] =>
    Blocks.cons (fun pm : Tup Val [i32, Ty.bool, Ty.bool, i32, i32] =>
      Expr.jnz (Arg.var pm.snd.fst)
        (Expr.jump J7 (Arg.var pm.fst, Arg.var nc, Arg.var al, Arg.var nu,
          Arg.var teid, Arg.var pm.snd.fst, Arg.var j, ()))
        (Expr.group (fun _B85 : Tup Cont [[i32, i32, i32, i32, Ty.bool, i32]] =>
          Blocks.cons (fun pb : Tup Val [i32, i32, i32, i32, Ty.bool, i32] =>
            Expr.jump B71 (Arg.var pm.fst, Arg.var pb.fst, Arg.var pb.snd.fst,
              Arg.var pb.snd.snd.fst, Arg.var pb.snd.snd.snd.fst,
              Arg.var pb.snd.snd.snd.snd.fst, ())) Blocks.nil)
        fun B85 =>
        Expr.jnz (Arg.var pm.snd.snd.fst)
          (Expr.jump B85.fst (Arg.var nc, Arg.var al, Arg.var nu, Arg.var teid,
            Arg.var pm.snd.fst, Arg.var pm.snd.snd.snd.snd.fst, ()))
          (Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl)
            (Arg.var pm.snd.snd.snd.fst, Arg.imm 0, ())) fun pc0 =>
          Expr.jnz (Arg.var pc0.fst)
            (Expr.jump J7 (Arg.var pm.fst, Arg.var nc, Arg.var al, Arg.var nu,
              Arg.var eid', Arg.var pm.snd.fst, Arg.var j, ()))
            (Expr.let_ (Op.mk (OpCode.cmp .uge i32 .bool rfl) (Arg.var nc, Arg.imm 128, ()))
              fun pc1 =>
            Expr.jnz (Arg.var pc1.fst)
              (Expr.jump J7 (Arg.var pm.fst, Arg.var nc, Arg.var al, Arg.var nu,
                Arg.var teid, Arg.imm true, Arg.var j, ()))
              (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var al, Arg.var pm.snd.snd.snd.fst, ()))
                fun pal =>
              Expr.let_ (Op.mk (OpCode.cmp .ugt i32 .bool rfl)
                (Arg.var pal.fst, Arg.var acap_v, ())) fun pc2 =>
              Expr.jnz (Arg.var pc2.fst)
                (Expr.jump J7 (Arg.var pm.fst, Arg.var nc, Arg.var al, Arg.var nu,
                  Arg.var teid, Arg.imm true, Arg.var j, ()))
                (Expr.group (fun Lc : Tup Cont [[i32]] => Blocks.cons (fun pmc : Tup Val [i32] =>
                  Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl)
                    (Arg.var pmc.fst, Arg.var pm.snd.snd.snd.fst, ())) fun pc =>
                  Expr.jnz (Arg.var pc.fst)
                    (Expr.let_ (Op.mk (OpCode.add i32) (Arg.imm 2912, Arg.var al, ())) fun p2 =>
                    Expr.let_ (Op.mk (OpCode.add i32) (Arg.var p2.fst, Arg.var pmc.fst, ()))
                      fun p3 =>
                    Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p3.fst, ())) fun p4 =>
                    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p4.fst, Arg.imm 4, ())) fun p5 =>
                    Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pk, Arg.var p5.fst, ())) fun p6 =>
                    Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var pmc.fst, ()))
                      fun p7 =>
                    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p7.fst, Arg.imm 4, ())) fun p8 =>
                    Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pTmp, Arg.var p8.fst, ()))
                      fun p9 =>
                    Expr.load i32 (Arg.var p9.fst) fun lit_c =>
                    Expr.store (@Arg.var Val i32 lit_c) (Arg.var p6.fst)
                    (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pmc.fst, Arg.imm 1, ())) fun p10 =>
                    Expr.jump Lc.fst (Arg.var p10.fst, ())))
                    (Expr.let_ (Op.mk (OpCode.add i32) (Arg.imm 1888, Arg.var nc, ())) fun p2 =>
                    Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p2.fst, ())) fun p3 =>
                    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p3.fst, Arg.imm 4, ())) fun p4 =>
                    Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pk, Arg.var p4.fst, ())) fun p5 =>
                    Expr.store (@Arg.var Val i32 al) (Arg.var p5.fst)
                    (Expr.let_ (Op.mk (OpCode.add i32) (Arg.imm 2144, Arg.var nc, ())) fun p6 =>
                    Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p6.fst, ())) fun p7 =>
                    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p7.fst, Arg.imm 4, ())) fun p8 =>
                    Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pk, Arg.var p8.fst, ())) fun p9 =>
                    Expr.store (@Arg.var Val i32 pm.snd.snd.snd.fst) (Arg.var p9.fst)
                    (Expr.let_ (Op.mk (OpCode.add i32) (Arg.imm 2400, Arg.var nc, ())) fun p10 =>
                    Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p10.fst, ())) fun p11 =>
                    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p11.fst, Arg.imm 4, ())) fun p12 =>
                    Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pk, Arg.var p12.fst, ())) fun p13 =>
                    Expr.store (@Arg.var Val i32 eid') (Arg.var p13.fst)
                    (Expr.group (fun _Lu : Tup Cont [[i32]] =>
                      Blocks.cons (fun pu : Tup Val [i32] =>
                      Expr.let_ (Op.mk (OpCode.add i32) (Arg.var nc, Arg.imm 1, ())) fun q1 =>
                      Expr.let_ (Op.mk (OpCode.add i32)
                        (Arg.var al, Arg.var pm.snd.snd.snd.fst, ())) fun q2 =>
                      Expr.jump B85.fst (Arg.var q1.fst, Arg.var q2.fst, Arg.var pu.fst,
                        Arg.var teid, Arg.var pm.snd.fst, Arg.var pmc.fst, ())) Blocks.nil)
                      fun Lu =>
                      Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl)
                        (Arg.var pm.snd.snd.snd.fst, Arg.imm 1, ())) fun peq1 =>
                      Expr.jnz (Arg.var peq1.fst)
                        (Expr.let_ (Op.mk (OpCode.add i32) (Arg.imm 2656, Arg.var nu, ()))
                          fun pu1 =>
                        Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var pu1.fst, ())) fun pu2 =>
                        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var pu2.fst, Arg.imm 4, ()))
                          fun pu3 =>
                        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pk, Arg.var pu3.fst, ()))
                          fun pu4 =>
                        Expr.store (@Arg.var Val i32 nc) (Arg.var pu4.fst)
                        (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var nu, Arg.imm 1, ())) fun pu5 =>
                        Expr.jump Lu.fst (Arg.var pu5.fst, ())))
                        (Expr.jump Lu.fst (Arg.var nu, ()))))))) Blocks.nil)
                  fun Lc => Expr.jump Lc.fst (Arg.imm 0, ()))))))) Blocks.nil)
    fun Bm =>
    Expr.group (fun Lm : Tup Cont [[i32, i32, i32]] =>
      Blocks.cons (fun pl : Tup Val [i32, i32, i32] =>
      Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var pl.snd.snd.fst, Arg.var sz, ()))
        fun p_1 =>
      Expr.jnz (Arg.var p_1.fst)
        (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var w, ())) fun p_2 =>
        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p_2.fst, Arg.imm 3, ())) fun p_3 =>
        Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var pl.snd.snd.fst, ())) fun p_4 =>
        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p_3.fst, Arg.var p_4.fst, ())) fun p_5 =>
        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_5.fst, Arg.imm 4, ())) fun p_6 =>
        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pArena, Arg.var p_6.fst, ())) fun p_7 =>
        Expr.load i32 (Arg.var p_7.fst) fun ld_l =>
        Expr.group (fun _Js2 : Tup Cont [[i32, Ty.bool, Ty.bool, i32]] =>
          Blocks.cons (fun p8 : Tup Val [i32, Ty.bool, Ty.bool, i32] =>
          Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pl.snd.snd.fst, Arg.imm 1, ())) fun pm1 =>
          Expr.jump Lm.fst (Arg.var p8.fst, Arg.var p8.snd.snd.snd.fst,
            Arg.var pm1.fst, ())) Blocks.nil)
          fun Js2 =>
          Expr.let_ (Op.mk (OpCode.cmp .ne i32 .bool rfl) (Arg.var ld_l, Arg.var ex, ()))
            fun p8 =>
          Expr.jnz (Arg.var p8.fst)
            (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld_l, ())) fun p9 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pVals, Arg.var p9.fst, ())) fun p10 =>
            Expr.load i8 (Arg.var p10.fst) fun ld1 =>
            Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm 0, ())) fun p11 =>
            Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var ld1, ())) fun p12 =>
            Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var p11.fst, ())) fun p13 =>
            Expr.let_ (Op.mk (OpCode.cmp .sgt i32 .bool rfl)
              (Arg.var p12.fst, Arg.var p13.fst, ())) fun p14 =>
            Expr.jnz (Arg.var p14.fst)
              (Expr.jump Bm.fst (Arg.var pl.fst, Arg.var ab, Arg.imm true,
                Arg.var pl.snd.fst, Arg.var pl.snd.snd.fst, ()))
              (Expr.group (fun _Js3 : Tup Cont [[i32, Ty.bool, i32]] =>
                Blocks.cons (fun p15 : Tup Val [i32, Ty.bool, i32] =>
                Expr.jump Js2.fst (Arg.var p15.fst, Arg.var p15.snd.fst,
                  Arg.imm false, Arg.var p15.snd.snd.fst, ())) Blocks.nil)
                fun Js3 =>
                Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm 0, ())) fun p15 =>
                Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var ld1, ())) fun p16 =>
                Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var p15.fst, ())) fun p17 =>
                Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl)
                  (Arg.var p16.fst, Arg.var p17.fst, ())) fun p18 =>
                Expr.jnz (Arg.var p18.fst)
                  (Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var ld_l, Arg.imm 1, ())) fun lv_l =>
                  Expr.group (fun _Js4 : Tup Cont [[i32, Ty.bool]] =>
                    Blocks.cons (fun p19 : Tup Val [i32, Ty.bool] =>
                    Expr.let_ (Op.mk (OpCode.cmp .uge i32 .bool rfl)
                      (Arg.var pl.snd.fst, Arg.var mc, ())) fun p20 =>
                    Expr.jnz (Arg.var p20.fst)
                      (Expr.jump Bm.fst (Arg.var p19.fst, Arg.imm true, Arg.imm false,
                        Arg.var pl.snd.fst, Arg.var pl.snd.snd.fst, ()))
                      (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var pl.snd.fst, ())) fun p21 =>
                      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p21.fst, Arg.imm 4, ())) fun p22 =>
                      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pTmp, Arg.var p22.fst, ()))
                        fun p23 =>
                      Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var lv_l.fst, ())) fun p24 =>
                      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p24.fst, Arg.imm 4, ())) fun p25 =>
                      Expr.let_ (Op.mk (OpCode.add i64)
                        (Arg.var c.pTarjanMark, Arg.var p25.fst, ())) fun p26 =>
                      Expr.load i32 (Arg.var p26.fst) fun tmkv_l =>
                      Expr.let_ (Op.mk (OpCode.sub i32) (Arg.var tmkv_l, Arg.imm 1, ())) fun p27 =>
                      Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var p27.fst, Arg.imm 1, ())) fun p28 =>
                      Expr.let_ (Op.mk (OpCode.and i32) (Arg.var ld_l, Arg.imm 1, ())) fun p29 =>
                      Expr.let_ (Op.mk (OpCode.or i32) (Arg.var p28.fst, Arg.var p29.fst, ()))
                        fun p30 =>
                      Expr.store (Arg.var p30.fst) (Arg.var p23.fst)
                      (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pl.snd.fst, Arg.imm 1, ()))
                        fun p31 =>
                      Expr.jump Js3.fst (Arg.var p19.fst, Arg.var p19.snd.fst,
                        Arg.var p31.fst, ())))) Blocks.nil)
                    fun Js4 =>
                    Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var lv_l.fst, ())) fun p19 =>
                    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p19.fst, Arg.imm 4, ())) fun p20 =>
                    Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pTarjanMark, Arg.var p20.fst, ()))
                      fun p21 =>
                    Expr.load i32 (Arg.var p21.fst) fun tmk_l =>
                    Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl) (Arg.var tmk_l, Arg.imm 0, ()))
                      fun p22 =>
                    Expr.jnz (Arg.var p22.fst)
                      (Expr.let_ (Op.mk (OpCode.cmp .uge i32 .bool rfl)
                        (Arg.var pl.fst, Arg.imm 64, ())) fun p23 =>
                      Expr.jnz (Arg.var p23.fst)
                        (Expr.jump Bm.fst (Arg.var pl.fst, Arg.imm true, Arg.imm false,
                          Arg.var pl.snd.fst, Arg.var pl.snd.snd.fst, ()))
                        (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var pl.fst, ())) fun p24 =>
                        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 776, ()))
                          fun p25 =>
                        Expr.load i64 (Arg.var p25.fst) fun cv_l =>
                        Expr.let_ (Op.mk (OpCode.sext 32 64) (Arg.imm 1, ())) fun p26 =>
                        Expr.let_ (Op.mk (OpCode.shl i64) (Arg.var cv_l, Arg.var p26.fst, ()))
                          fun p27 =>
                        Expr.let_ (Op.mk (OpCode.cmp .uge i64 .bool rfl)
                          (Arg.var p24.fst, Arg.var p27.fst, ())) fun p28 =>
                        Expr.jnz (Arg.var p28.fst)
                          (Expr.jump Bm.fst (Arg.var pl.fst, Arg.imm true, Arg.imm false,
                            Arg.var pl.snd.fst, Arg.var pl.snd.snd.fst, ()))
                          (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var pl.fst, ())) fun p29 =>
                          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p29.fst, Arg.imm 4, ()))
                            fun p30 =>
                          Expr.let_ (Op.mk (OpCode.add i64)
                            (Arg.var c.pWsort, Arg.var p30.fst, ())) fun p31 =>
                          Expr.store (@Arg.var Val i32 lv_l.fst) (Arg.var p31.fst)
                          (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pl.fst, Arg.imm 1, ()))
                            fun p32 =>
                          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var lv_l.fst, ())) fun p33 =>
                          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p33.fst, Arg.imm 4, ()))
                            fun p34 =>
                          Expr.let_ (Op.mk (OpCode.add i64)
                            (Arg.var c.pTarjanMark, Arg.var p34.fst, ())) fun p35 =>
                          Expr.store (@Arg.var Val i32 p32.fst) (Arg.var p35.fst)
                          (Expr.jump Js4.fst (Arg.var p32.fst, Arg.var ab, ()))))))
                      (Expr.jump Js4.fst (Arg.var pl.fst, Arg.var ab, ())))
                  (Expr.jump Js3.fst (Arg.var pl.fst, Arg.var ab, Arg.var pl.snd.fst, ()))))
            (Expr.jump Js2.fst (Arg.var pl.fst, Arg.var ab, Arg.imm false,
              Arg.var pl.snd.fst, ())))
      (Expr.jump Bm.fst (Arg.var pl.fst, Arg.var ab, Arg.imm false,
        Arg.var pl.snd.fst, Arg.var pl.snd.snd.fst, ()))) Blocks.nil)
      fun Lm => Expr.jump Lm.fst (Arg.var nv, Arg.imm 0, Arg.imm 0, ())

private theorem m7_p6_large_branch_wp (Γ : Env) (Q : Post []) (X : XPost)
    (J7 : Cont [i32, i32, i32, i32, i32, Ty.bool, i32])
    (B71 : Cont [i32, i32, i32, i32, i32, Ty.bool])
    (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s0 : FullState)
    (R : Mem 64 → Prop) (hinv : FullDenseInvW c F0 F_cur s0)
    (h8192 : 8192 ≤ c.scratch_cap) (hcap_lt : c.scratch_cap < 2 ^ 28)
    (mc : BitVec 32) (hmc_pos : 0 < mc.toNat) (hmc_le : mc.toNat ≤ 100)
    (hmc_mv : mc.toNat ≤ c.max_vars)
    (nv nc al nu teid j ex w eid' : BitVec 32) (ab : Bool) (pk : BitVec 64)
    (acap_v : BitVec 32) (exp tmk tmp scr : List (BitVec 32)) (m : Mem 64)
    (htmp_len : tmp.length = c.max_vars) (hscr_len : scr.length = c.scratch_cap)
    (hpres : ∀ k < 1096, scr[k]? = s0.scratch.scratch_buf[k]?)
    (hte : M7P6TmkExpInv c s0 nv exp tmk)
    (hcls : M7P6ClsInv nc al nu (c.scratch_cap - 4008) scr)
    (hteid_bd : teid ≠ 0xFFFFFFFF#32 → (teid &&& 1023#32).toNat < 512)
    (heid'_bd : eid' ≠ 0xFFFFFFFF#32 ∧ (eid' &&& 1023#32).toNat < 512)
    (hm_st : (FullMem c (m7_p6_clr_state s0 tmp exp tmk scr) ⋆ R) m)
    (hab : ab = false) (hnv64 : nv.toNat ≤ 64) (hnc128 : nc.toNat ≤ 128)
    (hpk : pk = c.pScratchBuf + 1096#64 * 4)
    (hacap : acap_v = BitVec.ofNat 32 (c.scratch_cap - 4008))
    (hfull : FullBveEntryOkW F_cur s0 ex.toNat w) (hnotbin : w &&& 0x80000000#32 = 0#32)
    (hJ7 : ∀ st m', (∃ nv' nc' al' nu' teid' j' : BitVec 32, ∃ ab' : Bool,
      st = (nv', nc', al', nu', teid', ab', j', ()) ∧
      nv'.toNat ≤ 64 ∧ nc'.toNat ≤ 128 ∧
      M7P6SideInv c s0 R (c.scratch_cap - 4008) nv' nc' al' nu' teid' m') → J7 st m')
    (hB71 : ∀ st m', (∃ nv' nc' al' nu' teid' : BitVec 32, ∃ ab' : Bool,
      st = (nv', nc', al', nu', teid', ab', ()) ∧
      nv'.toNat ≤ 64 ∧ nc'.toNat ≤ 128 ∧
      M7P6SideInv c s0 R (c.scratch_cap - 4008) nv' nc' al' nu' teid m') → B71 st m') :
    wp Γ Q X (m7_p6_large_expr J7 B71 c mc nv nc al nu teid j ex w eid' ab pk acap_v) m := by
  obtain ⟨hsz_ar, hsz_end, hlits_bd⟩ := m7_p6_arena_clause_bounds hinv hfull hnotbin
  have har_len : (m7_p6_clr_state s0 tmp exp tmk scr).core.arena.length = c.arena_cap :=
    hinv.1.core_ok.arena_len_arr
  have har_bd : (BitVec.setWidth 64 w + 2#64).toNat <
      (m7_p6_clr_state s0 tmp exp tmk scr).core.arena.length := by
    dsimp only [m7_p6_clr_state]; bv_omega
  dsimp only [m7_p6_large_expr]
  c0_hsteps_nogrp
  refine wp_join_state (ts := [i32, Ty.bool, Ty.bool, i32, i32]) (fun p => p)
    (fun p m' => ∃ nv_m csz_m m_idx : BitVec 32, ∃ ab_m sat_m : Bool,
      ∃ exp_m tmk_m tmp_m : List (BitVec 32),
      p = (nv_m, ab_m, sat_m, csz_m, m_idx, ()) ∧
      tmp_m.length = c.max_vars ∧ nv_m.toNat ≤ 64 ∧ csz_m.toNat ≤ mc.toNat ∧
      M7P6TmkExpInv c s0 nv_m exp_m tmk_m ∧
      (FullMem c (m7_p6_clr_state s0 tmp_m exp_m tmk_m scr) ⋆ R) m') ?_ ?_
  · intro _ ⟨nv_m, ab_m, sat_m, csz_m, m_idx, ⟨⟩⟩ mm
      ⟨_, _, _, _, _, exp_m, tmk_m, tmp_m, heqp, htmp_m, hnv_m64, hcsz_mc, hte_m, hm_m⟩
    cases heqp
    c0_hsplit
    · c0_hsteps!
      exact hJ7 _ mm ⟨nv_m, nc, al, nu, teid, j, ab_m, rfl, hnv_m64, hnc128,
        exp_m, tmk_m, tmp_m, scr, htmp_m, hscr_len, hpres, hte_m, hcls, hteid_bd, hm_m⟩
    · c0_hsteps_nogrp
      refine wp_join_state (ts := [i32, i32, i32, i32, Ty.bool, i32]) (fun p => p)
        (fun p m' => ∃ nc' al' nu' te' : BitVec 32, ∃ ab' : Bool, ∃ m_d : BitVec 32,
          ∃ scr' : List (BitVec 32),
          p = (nc', al', nu', te', ab', m_d, ()) ∧
          nc'.toNat ≤ 128 ∧ scr'.length = c.scratch_cap ∧
          (∀ k < 1096, scr'[k]? = s0.scratch.scratch_buf[k]?) ∧
          M7P6ClsInv nc' al' nu' (c.scratch_cap - 4008) scr' ∧
          (FullMem c (m7_p6_clr_state s0 tmp_m exp_m tmk_m scr') ⋆ R) m') ?_ ?_
      · intro _ ⟨nc', al', nu', te', ab', m_d, ⟨⟩⟩ m'
          ⟨_, _, _, _, _, _, scr', heqp, hnc'128, hscr', hpres', hcls', hm'⟩
        cases heqp; c0_hsteps!
        exact hB71 _ m' ⟨nv_m, nc', al', nu', te', ab', rfl, hnv_m64, hnc'128,
          exp_m, tmk_m, tmp_m, scr', htmp_m, hscr', hpres', hte_m, hcls', hteid_bd, hm'⟩
      · intro B85 hB85
        c0_hsplit
        · c0_hsteps!
          exact hB85 _ mm ⟨nc, al, nu, teid, ab_m, m_idx, scr, rfl, hnc128, hscr_len, hpres,
            hcls, hm_m⟩
        · c0_hsplit
          · c0_hsteps!
            exact hJ7 _ mm ⟨nv_m, nc, al, nu, eid', j, ab_m, rfl, hnv_m64, hnc128,
              exp_m, tmk_m, tmp_m, scr, htmp_m, hscr_len, hpres, hte_m, hcls,
              fun _ => heid'_bd.2, hm_m⟩
          · c0_hsplit
            · c0_hsteps!
              exact hJ7 _ mm ⟨nv_m, nc, al, nu, teid, j, true, rfl, hnv_m64, hnc128,
                exp_m, tmk_m, tmp_m, scr, htmp_m, hscr_len, hpres, hte_m, hcls, hteid_bd, hm_m⟩
            · c0_hsplit
              · c0_hsteps!
                exact hJ7 _ mm ⟨nv_m, nc, al, nu, teid, j, true, rfl, hnv_m64, hnc128,
                  exp_m, tmk_m, tmp_m, scr, htmp_m, hscr_len, hpres, hte_m, hcls, hteid_bd, hm_m⟩
              · have hcsz_pos : 0 < csz_m.toNat := by c0_bound
                have hnc_lt : nc.toNat < 128 := by
                  have hc' : ¬128 ≤ nc.toNat := by c0_bound
                  omega
                have hal_add : al.toNat + csz_m.toNat ≤ c.scratch_cap - 4008 := by
                  have hc' : ¬(acap_v.toNat < (al + csz_m).toNat) := by c0_bound
                  have hac : acap_v.toNat = c.scratch_cap - 4008 := by
                    rw [hacap, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                  have hal_bd := hcls.2.2.1
                  have hlt32 : al.toNat + csz_m.toNat < 2 ^ 32 := by omega
                  have hmod : (al + csz_m).toNat = al.toNat + csz_m.toNat := by
                    rw [BitVec.toNat_add, Nat.mod_eq_of_lt hlt32]
                  omega
                have hal_s : (al + csz_m).toNat = al.toNat + csz_m.toNat := by
                  have hal_bd := hcls.2.2.1
                  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
                refine m7_p6_copy_clause_wp Γ Q X B85 c
                  (m7_p6_clr_state s0 tmp_m exp_m tmk_m scr) R pk c.pTmp nc al nu eid' teid
                  csz_m ab_m (fun k => s0.scratch.scratch_buf[k]?) mm hpk rfl h8192 hcap_lt
                  hscr_len htmp_m hcsz_pos (by omega) (by omega) hnc_lt hcls.2.1 hal_add hpres
                  hcls.2.2.2 hm_m ?_
                intro nu_j m_done scr_j mj hscr_j hnu_j hpres_j hcls_j hm_j
                refine hB85 _ mj ⟨nc + 1#32, al + csz_m, nu_j, teid, ab_m, m_done, scr_j, rfl,
                  by bv_omega, hscr_j, hpres_j, ⟨by bv_omega, by bv_omega, by bv_omega,
                    fun cid hcid => by
                      have hc_j := hcls_j cid (by bv_omega)
                      exact ⟨by rw [hal_s]; exact hc_j.1, hc_j.2⟩⟩,
                  m7_p6_fullMem_subst hm_j rfl rfl⟩
  · intro Bm hBm
    dsimp only [Prod.fst]
    let csz_a := (m7_p6_clr_state s0 tmp exp tmk scr).core.arena[
      (BitVec.setWidth 64 w + 2#64).toNat]'(by dsimp only [m7_p6_clr_state]; bv_omega)
    have hcsz_eq : csz_a = s0.core.arena[w.toNat + 2]?.getD 0#32 := by
      simp only [csz_a, m7_p6_clr_state, List.getElem?_eq_getElem hsz_ar, Option.getD_some]
      congr 1; bv_omega
    refine m7_p6_scan_large_wp Γ Q X Bm c (m7_p6_clr_state s0 tmp exp tmk scr) R
      c.pArena c.pVals c.pTarjanMark c.pWsort c.pTmp nv ex w csz_a mc ab m rfl rfl rfl rfl rfl
      hinv.1.core_ok.arena_len_arr hinv.1.core_ok.arena_len_le hinv.1.core_ok.vals_len
      hinv.1.core_ok.cur_vars_le
      (by have := c.hmaxv; rw [show dimacsBound = 2 ^ 28 from rfl] at this; exact this)
      (hcsz_eq ▸ hsz_end) (fun j hj => hlits_bd j (hcsz_eq ▸ hj)) hte.1 hte.2.1 htmp_len
      hmc_pos hmc_le hmc_mv hnv64 hte.2.2.2.1 hab hte.2.2.2.2.1 hte.2.2.2.2.2 hm_st ?_
    intro nv_m ab_m sat_m csz_m m_idx exp_m tmk_m tmp_m mm hexp_m htmk_m htmp_m hnv_m64
      hnv_m2cv hcsz_mc hexp_cv htmk_inv hm_mm
    exact hBm _ mm ⟨nv_m, csz_m, m_idx, ab_m, sat_m, exp_m, tmk_m, tmp_m, rfl, htmp_m,
      hnv_m64, hcsz_mc, ⟨hexp_m, htmk_m, hnv_m64, hnv_m2cv, hexp_cv, htmk_inv⟩,
      m7_p6_fullMem_subst hm_mm rfl rfl⟩

@[reducible] private def m7_p6_inner_loop_expr (J7 : Cont [i32, i32, i32, i32, i32, Ty.bool, i32])
    (c : FullCfg) (mc nv nc al nu teid side : BitVec 32) (ab : Bool) (cnt off ex : BitVec 32)
    (pk : BitVec 64) (acap_v : BitVec 32) : Expr Val Cont [] :=
  Expr.group (fun G8 : Tup Cont [[i32, i32, i32, i32, Ty.bool, i32]] =>
    Blocks.cons (fun p : Tup Val [i32, i32, i32, i32, Ty.bool, i32] =>
      Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl)
        (Arg.var p.snd.snd.snd.snd.snd.fst, Arg.var cnt, ())) fun pc =>
      Expr.jnz (Arg.var pc.fst)
        (Expr.jnz (Arg.var p.snd.snd.snd.snd.fst)
          (Expr.jump J7 (Arg.var p.fst, Arg.var p.snd.fst, Arg.var p.snd.snd.fst,
            Arg.var p.snd.snd.snd.fst, Arg.var teid, Arg.var p.snd.snd.snd.snd.fst,
            Arg.var p.snd.snd.snd.snd.snd.fst, ()))
          (Expr.let_ (Op.mk (OpCode.add i32)
            (Arg.var off, Arg.var p.snd.snd.snd.snd.snd.fst, ())) fun p_2 =>
          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p_2.fst, ())) fun p_3 =>
          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_3.fst, Arg.imm 4, ())) fun p_4 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p_4.fst, ())) fun p_5 =>
          Expr.load i32 (Arg.var p_5.fst) fun ld =>
          Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var side, Arg.imm 10, ())) fun p_6 =>
          Expr.let_ (Op.mk (OpCode.or i32)
            (Arg.var p_6.fst, Arg.var p.snd.snd.snd.snd.snd.fst, ())) fun p_7 =>
          Expr.group (fun _B71 : Tup Cont [[i32, i32, i32, i32, i32, Ty.bool]] =>
            Blocks.cons (fun p_8 : Tup Val [i32, i32, i32, i32, i32, Ty.bool] =>
          Expr.let_ (Op.mk (OpCode.add i32)
            (Arg.var p.snd.snd.snd.snd.snd.fst, Arg.imm 1, ())) fun p_j =>
          Expr.jump G8.fst (Arg.var p_8.fst, Arg.var p_8.snd.fst, Arg.var p_8.snd.snd.fst,
            Arg.var p_8.snd.snd.snd.fst, Arg.var p_8.snd.snd.snd.snd.snd.fst,
            Arg.var p_j.fst, ())) Blocks.nil)
          fun B71 =>
          Expr.let_ (Op.mk (OpCode.and i32) (Arg.var ld, Arg.imm 0x80000000#32, ())) fun p_8 =>
          Expr.let_ (Op.mk (OpCode.cmp .ne i32 .bool rfl) (Arg.var p_8.fst, Arg.imm 0, ()))
            fun p_9 =>
          Expr.jnz (Arg.var p_9.fst)
            (m7_p6_bin_expr J7 B71.fst c p.fst p.snd.fst p.snd.snd.fst p.snd.snd.snd.fst teid
              p.snd.snd.snd.snd.snd.fst ld p_7.fst p.snd.snd.snd.snd.fst pk acap_v)
            (m7_p6_large_expr J7 B71.fst c mc p.fst p.snd.fst p.snd.snd.fst p.snd.snd.snd.fst teid
              p.snd.snd.snd.snd.snd.fst ex ld p_7.fst p.snd.snd.snd.snd.fst pk acap_v)))
      (Expr.jump J7 (Arg.var p.fst, Arg.var p.snd.fst, Arg.var p.snd.snd.fst,
        Arg.var p.snd.snd.snd.fst, Arg.var teid, Arg.var p.snd.snd.snd.snd.fst,
        Arg.var p.snd.snd.snd.snd.snd.fst, ()))) Blocks.nil)
    fun G8 => Expr.jump G8.fst (Arg.var nv, Arg.var nc, Arg.var al, Arg.var nu,
      Arg.var ab, Arg.imm 0, ())

private theorem m7_p6_inner_loop_wp (Γ : Env) (Q : Post []) (X : XPost)
    (J7 : Cont [i32, i32, i32, i32, i32, Ty.bool, i32])
    (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s0 : FullState)
    (R : Mem 64 → Prop) (hinv : FullDenseInvW c F0 F_cur s0)
    (h8192 : 8192 ≤ c.scratch_cap) (hcap_lt : c.scratch_cap < 2 ^ 28)
    (mc : BitVec 32) (hmc_le : mc.toNat ≤ 100) (hmc_pos : 0 < mc.toNat)
    (hmc_mv : mc.toNat ≤ c.max_vars)
    (nv nc al nu teid side : BitVec 32) (ab : Bool) (cnt off ex : BitVec 32)
    (pk : BitVec 64) (acap_v : BitVec 32)
    (hnv64 : nv.toNat ≤ 64) (hnc128 : nc.toNat ≤ 128) (hside_lt2 : side.toNat < 2)
    (_hab0 : ab = false) (hpk : pk = c.pScratchBuf + 1096#64 * 4)
    (hacap : acap_v = BitVec.ofNat 32 (c.scratch_cap - 4008))
    (hcnt_le : cnt.toNat ≤ 128) (hoff_le : off.toNat + cnt.toNat ≤ 1024)
    (_hex_lt : ex.toNat < 2 * s0.core.cur_vars)
    (hentry : ∀ j < cnt.toNat,
      FullBveEntryOkW F_cur s0 ex.toNat (s0.scratch.scratch_buf[off.toNat + j]?.getD 0#32))
    {m : Mem 64} (hsideInv : M7P6SideInv c s0 R (c.scratch_cap - 4008) nv nc al nu teid m)
    (hJ7 : ∀ st m', (∃ nv' nc' al' nu' teid' j' : BitVec 32, ∃ ab' : Bool,
      st = (nv', nc', al', nu', teid', ab', j', ()) ∧
      nv'.toNat ≤ 64 ∧ nc'.toNat ≤ 128 ∧
      M7P6SideInv c s0 R (c.scratch_cap - 4008) nv' nc' al' nu' teid' m') → J7 st m') :
    wp Γ Q X (m7_p6_inner_loop_expr J7 c mc nv nc al nu teid side ab cnt off ex pk acap_v)
      m := by
  refine wp_loop_inv
    (fun (p : Tup Val [i32, i32, i32, i32, Ty.bool, i32]) m' =>
      ∃ nv_k nc_k al_k nu_k j_k : BitVec 32, ∃ ab_k : Bool,
        p = (nv_k, nc_k, al_k, nu_k, ab_k, j_k, ()) ∧
        j_k.toNat ≤ cnt.toNat ∧ nv_k.toNat ≤ 64 ∧ nc_k.toNat ≤ 128 ∧
        M7P6SideInv c s0 R (c.scratch_cap - 4008) nv_k nc_k al_k nu_k teid m')
    (fun (p : Tup Val [i32, i32, i32, i32, Ty.bool, i32]) _ =>
      cnt.toNat - p.snd.snd.snd.snd.snd.fst.toNat) ?_ ?_
  · intro G8 hG8; c0_hsteps!
    exact hG8 (nv, nc, al, nu, ab, 0, ()) m
      ⟨nv, nc, al, nu, 0#32, ab, rfl, Nat.zero_le _, hnv64, hnc128, hsideInv⟩
  · intro G8 ⟨nv_k, nc_k, al_k, nu_k, ab_k, j_k, ⟨⟩⟩ mk
      ⟨_, _, _, _, _, _, heqp, hj_le, hnv_k64, hnc_k128, hside_k⟩ hrec8
    cases heqp
    c0_hsplit
    · have hj_lt : j_k.toNat < cnt.toNat := by c0_bound
      have hj128 : j_k.toNat < 128 := by omega
      c0_hsplit
      · c0_hsteps!
        exact hJ7 _ mk ⟨nv_k, nc_k, al_k, nu_k, teid, j_k, ab_k, rfl, hnv_k64, hnc_k128, hside_k⟩
      · have hab_k : ab_k = false := by c0_bound
        rcases hside_k with ⟨exp_k, tmk_k, tmp_k, scr_k, htmp_k, hscr_k, hpres_k, hte_k, hcls_k,
          hteid_bd, hm_k⟩
        have hscr_clr_len :
            (m7_p6_clr_state s0 tmp_k exp_k tmk_k scr_k).scratch.scratch_buf.length =
              c.scratch_cap := hscr_k
        have hoffj : (off + j_k).toNat = off.toNat + j_k.toNat := by bv_omega
        have hoffj_lt : (off + j_k).toNat < 1024 := by omega
        have hpres_ld := hpres_k (off + j_k).toNat (by omega)
        have hok_ld : FullBveEntryOkW F_cur s0 ex.toNat
            (scr_k[(off + j_k).toNat]?.getD 0#32) := by
          rw [hpres_ld, hoffj]; exact hentry j_k.toNat hj_lt
        have heid'_bd := m7_p6_eid_bounds hside_lt2 hj128
        c0_hsteps_nogrp
        refine wp_join_state (ts := [i32, i32, i32, i32, i32, Ty.bool]) (fun p => p)
          (fun p m' => ∃ nv' nc' al' nu' te' : BitVec 32, ∃ ab' : Bool,
            p = (nv', nc', al', nu', te', ab', ()) ∧ nv'.toNat ≤ 64 ∧ nc'.toNat ≤ 128 ∧
            M7P6SideInv c s0 R (c.scratch_cap - 4008) nv' nc' al' nu' teid m') ?_ ?_
        · intro _ ⟨nv', nc', al', nu', te', ab', ⟨⟩⟩ m'
            ⟨_, _, _, _, _, _, heqp', hnv'64, hnc'128, hside'⟩
          cases heqp'; c0_hsteps!
          exact hrec8 (nv', nc', al', nu', ab', j_k + 1#32, ()) m' (by bv_omega)
            ⟨nv', nc', al', nu', j_k + 1#32, ab', rfl, by bv_omega, hnv'64, hnc'128, hside'⟩
        · intro B71 hB71
          have hidx_nat : (BitVec.setWidth 64 (off + j_k)).toNat = (off + j_k).toNat := by bv_omega
          have hscr_bd : (BitVec.setWidth 64 (off + j_k)).toNat < scr_k.length := by
            rw [hidx_nat]; omega
          have h2 : scr_k[(off + j_k).toNat]?.getD 0#32 =
              scr_k[(BitVec.setWidth 64 (off + j_k)).toNat]'hscr_bd := by
            simp only [hidx_nat,
              List.getElem?_eq_getElem (by omega : (off + j_k).toNat < scr_k.length),
              Option.getD_some]
          have hok_scr : FullBveEntryOkW F_cur s0 ex.toNat
              (scr_k[(BitVec.setWidth 64 (off + j_k)).toNat]'hscr_bd) := by
            rw [← h2]; exact hok_ld
          c0_hsplit
          · refine m7_p6_bin_branch_wp Γ Q X J7 B71 c F0 F_cur s0 R hinv h8192 hcap_lt
              nv_k nc_k al_k nu_k teid j_k ex _ ((side <<< 10#32) ||| j_k) ab_k pk acap_v
              exp_k tmk_k tmp_k scr_k mk htmp_k hscr_k hpres_k hte_k hcls_k hteid_bd heid'_bd
              hm_k hab_k hnv_k64 hnc_k128 hpk hacap ?_ ?_ hJ7 hB71
            · exact hok_scr
            · c0_bound
          · refine m7_p6_large_branch_wp Γ Q X J7 B71 c F0 F_cur s0 R hinv h8192 hcap_lt
              mc hmc_pos hmc_le hmc_mv nv_k nc_k al_k nu_k teid j_k ex _
              ((side <<< 10#32) ||| j_k) ab_k pk acap_v exp_k tmk_k tmp_k scr_k mk htmp_k
              hscr_k hpres_k hte_k hcls_k hteid_bd heid'_bd hm_k hab_k hnv_k64 hnc_k128 hpk hacap
              ?_ ?_ hJ7 hB71
            · exact hok_scr
            · exact hc
    · c0_hsteps!
      exact hJ7 _ mk ⟨nv_k, nc_k, al_k, nu_k, teid, j_k, ab_k, rfl, hnv_k64, hnc_k128, hside_k⟩

/-! ## 3. Main Theorem (`full_bve_def_k6_m7_wp`) -/

public section

/-- Certifies `fullBveGatesM7Spec` for `full_bve_def_k6_m7`. -/
theorem full_bve_def_k6_m7_wp (Γ : Env)
    (h_watch : Γ.Has "full_k6_watch_m7" fullK6WatchM7Spec)
    (h_solve : Γ.Has "full_k6_solve_m7" fullK6SolveM7Spec)
    (h_core : Γ.Has "full_k6_core_m7" fullK6CoreM7Spec) :
    ∀ a m Q X, fullBveGatesM7Spec a m Q X →
      Func.wp Γ full_bve_def_k6_m7_body a m Q X := by
  rintro ⟨h, v, np, nn, ⟨⟩⟩ m0 Q X hSpec
  rcases hSpec with ⟨c, F0, F_cur, s0, R, rfl, hinv, htmk0, hcap, hv, hnp, hnn,
    hpos, hneg, hm0, hQ⟩
  unfold Func.wp full_bve_def_k6_m7_body
  c0_hsplit
  · c0_hsteps!
    exact m7_p6_gates_inv_exit s0 hinv htmk0 rfl rfl rfl (Nat.le_refl _) (fun _ _ => rfl)
      hm0 hnp hnn hQ
  · c0_hsplit
    · c0_hsteps!
      exact m7_p6_gates_inv_exit s0 hinv htmk0 rfl rfl rfl (Nat.le_refl _) (fun _ _ => rfl)
        hm0 hnp hnn hQ
    · c0_hsplit
      · c0_hsteps!
        exact m7_p6_gates_inv_exit s0 hinv htmk0 rfl rfl rfl (Nat.le_refl _) (fun _ _ => rfl)
          hm0 hnp hnn hQ
      · c0_hsplit
        · c0_hsteps!
          exact m7_p6_gates_inv_exit s0 hinv htmk0 rfl rfl rfl (Nat.le_refl _) (fun _ _ => rfl)
            hm0 hnp hnn hQ
        · c0_hsplit
          · c0_hsteps!
            exact m7_p6_gates_inv_exit s0 hinv htmk0 rfl rfl rfl (Nat.le_refl _) (fun _ _ => rfl)
              hm0 hnp hnn hQ
          · have h8192 : 8192 ≤ c.scratch_cap := by c0_bound
            have hcap_lt : c.scratch_cap < 2 ^ 28 := c.hscr
            have hnp128 : np.toNat ≤ 128 := by bv_omega
            have hnn128 : nn.toNat ≤ 128 := by bv_omega
            c0_hsteps_nogrp
            refine wp_join_state (ts := [i32]) (fun mc => (mc, ()))
              (fun mc m => mc.toNat ≤ 100 ∧ 0 < mc.toNat ∧ mc.toNat ≤ c.max_vars ∧
                (FullMem c s0 ⋆ R) m) ?_ ?_
            · intro _ mc m ⟨hmc_le, hmc_pos, hmc_mv, hm_mc⟩
              c0_hsteps_nogrp
              refine wp_loop_inv
                (fun p m => ∃ nv nc al nu teid side : BitVec 32, ∃ ab : Bool,
                  p = (nv, nc, al, nu, teid, ab, side, ()) ∧
                  side.toNat ≤ 2 ∧ nv.toNat ≤ 64 ∧ nc.toNat ≤ 128 ∧
                  M7P6SideInv c s0 R (c.scratch_cap - 4008) nv nc al nu teid m)
                (fun p _ => 2 - p.snd.snd.snd.snd.snd.snd.fst.toNat) ?_ ?_
              · intro J2 hJ2; c0_hsteps!
                exact hJ2 (0, 0, 0, 0, 4294967295, false, 0, ()) _
                  ⟨0#32, 0#32, 0#32, 0#32, 0xFFFFFFFF#32, 0#32, false, rfl,
                    Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
                    m7_p6_side_init_inv hinv htmk0 hm_mc⟩
              · intro J2 ⟨nv, nc, al, nu, teid, ab, side, ⟨⟩⟩ m
                  ⟨_, _, _, _, _, _, _, heq, hside, hnv64, hnc128, hsideInv⟩ hrec2
                cases heq
                c0_hsteps_nogrp
                refine wp_join_state (ts := []) (fun _ : Unit => ())
                  (fun _ m => M7P6SideInv c s0 R (c.scratch_cap - 4008) nv nc al nu teid m) ?_ ?_
                · intro _ ⟨⟩ m hside'
                  rcases hside' with ⟨exp, tmk, tmp, scr, htmp_len, hscr_len, hpres, hte, hcls,
                    hteid_bd, hm_st⟩
                  c0_hsteps_nogrp
                  refine wp_loop_inv
                    (fun (p : Tup Val [i32]) m => p.fst.toNat ≤ nv.toNat ∧
                      ∃ tmk_k scr_k : List (BitVec 32),
                        tmk_k.length = 2 * c.max_vars ∧ scr_k.length = c.scratch_cap ∧
                        (∀ u < s0.core.cur_vars, tmk_k[u]?.getD 0#32 ≠ 0#32 →
                          ∃ j < nv.toNat, (exp[j]?.getD 0#32).toNat = u) ∧
                        (∀ j < p.fst.toNat, tmk_k[(exp[j]?.getD 0#32).toNat]?.getD 0#32 = 0#32) ∧
                        (∀ k < 1096, scr_k[k]? = s0.scratch.scratch_buf[k]?) ∧
                        (∀ cid < nc.toNat,
                          (scr_k[1096 + 1888 + cid]?.getD 0#32).toNat +
                            (scr_k[1096 + 2144 + cid]?.getD 0#32 &&& 0xFFFF#32).toNat ≤ al.toNat ∧
                          scr_k[1096 + 2144 + cid]?.getD 0#32 &&& 0x40000000#32 = 0#32) ∧
                        (FullMem c (m7_p6_clr_state s0 tmp exp tmk_k scr_k) ⋆ R) m)
                    (fun (p : Tup Val [i32]) _ => nv.toNat - p.fst.toNat) ?_ ?_
                  · intro J4 hJ4; c0_hsteps!
                    refine hJ4 (0#32, ()) m ⟨Nat.zero_le _, tmk, scr, hte.2.1, hscr_len,
                      fun u hu hnz => (hte.2.2.2.2.2 u hu hnz).2.2,
                      fun _ hj => by simp at hj, hpres, hcls.2.2.2,
                      m7_p6_fullMem_subst hm_st rfl rfl⟩
                  · intro J4 ⟨k, ⟨⟩⟩ m ⟨hk_le, tmk_k, scr_k, htmk_k, hscr_k, htmk_nz, hclr_j,
                      hpres_k, hcls_k, hm_k⟩ hrec4
                    have hk_le' : k.toNat ≤ nv.toNat := hk_le
                    c0_hsplit
                    · have hk_lt : k.toNat < nv.toNat := by c0_bound
                      have hnv_2cv := hte.2.2.2.1
                      have hcv_mv : s0.core.cur_vars ≤ c.max_vars := hinv.1.core_ok.cur_vars_le
                      have hexp_lt : k.toNat < exp.length := by rw [hte.1]; omega
                      have hu_cv : (exp[k.toNat]'hexp_lt).toNat < s0.core.cur_vars := by
                        simpa [List.getElem?_eq_getElem hexp_lt] using hte.2.2.2.2.1 k.toNat hk_lt
                      have htmk_bd : (exp[k.toNat]'hexp_lt).toNat < tmk_k.length := by omega
                      c0_hsteps!
                      let u := (exp[k.toNat]'hexp_lt).toNat
                      have hk64_eq : (BitVec.setWidth 64 k).toNat = k.toNat := by bv_omega
                      have hweq : (BitVec.setWidth 64 (exp[(BitVec.setWidth 64 k).toNat]'(by
                          rw [hk64_eq]; exact hexp_lt))).toNat = u := by
                        have hget : exp[(BitVec.setWidth 64 k).toNat]'(by
                            rw [hk64_eq]; exact hexp_lt) = exp[k.toNat]'hexp_lt := by
                          simp only [hk64_eq]
                        dsimp only [u]; rw [hget]; bv_omega
                      refine hrec4 (k + 1, ()) _ (by bv_omega)
                        ⟨by bv_omega, tmk_k.set u 0#32, scr_k,
                          by rw [List.length_set, htmk_k], hscr_k, ?_, ?_, hpres_k, hcls_k, ?_⟩
                      · intro w hw hnz
                        by_cases hwu : w = u
                        · subst hwu; exfalso; apply hnz
                          rw [List.getElem?_set_self (by dsimp only [u]; omega)]; rfl
                        · rw [List.getElem?_set_ne (by omega)] at hnz
                          exact htmk_nz w hw hnz
                      · intro j hj
                        have hj' : j < k.toNat + 1 := by
                          have h1 : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
                          simpa [show (k + 1 : BitVec 32) = k + 1#32 from rfl, h1] using hj
                        by_cases hjk : j = k.toNat
                        · subst hjk
                          rw [List.getElem?_eq_getElem hexp_lt, Option.getD_some,
                            List.getElem?_set_self (by dsimp only [u]; omega)]; rfl
                        · have hj_lt : j < k.toNat := by omega
                          by_cases heq_u : (exp[j]?.getD 0#32).toNat = u
                          · rw [heq_u, List.getElem?_set_self (by dsimp only [u]; omega)]; rfl
                          · rw [List.getElem?_set_ne (by omega)]
                            exact hclr_j j hj_lt
                      · exact m7_p6_fullMem_subst ‹_› rfl (by simp [m7_p6_clr_state, u])
                    · have hk_eq : k.toNat = nv.toNat := by omega
                      have htmk0_f : ∀ u < s0.core.cur_vars, tmk_k[u]?.getD 0#32 = 0#32 := by
                        intro u hu
                        by_cases hz : tmk_k[u]?.getD 0#32 = 0#32
                        · exact hz
                        · obtain ⟨j, hj, hju⟩ := htmk_nz u hu hz
                          have := hclr_j j (hk_eq ▸ hj); rw [hju] at this; exact absurd this hz
                      let s_clr := m7_p6_clr_state s0 tmp exp tmk_k scr_k
                      have hinv_clr : FullDenseInvW c F0 F_cur s_clr :=
                        m7_p6_fullDenseInvW_def hinv htmp_len hte.1 htmk_k hscr_k
                      have htmk_clr : Spec.TmkZero s_clr := htmk0_f
                      c0_hsplit
                      · have hteid_ne : teid ≠ 0xFFFFFFFF#32 := by c0_bound
                        have hteid_lt : (teid &&& 1023#32).toNat < 512 := hteid_bd hteid_ne
                        c0_hsteps_nogrp
                        refine wp_join_state (ts := [i32]) (fun mb => (mb, ()))
                          (fun mb m' => (mb = 1024#32 ∨ mb = 1040#32) ∧ m' = m) ?_ ?_
                        · intro _ mb m' ⟨hmb, rfl⟩
                          obtain ⟨hidx_lo, hidx_hi, hlen_f, hinv_f, htmk_f, hpres_p, hpres_n⟩ :=
                            m7_p6_teid_exit_commit hinv htmp_len hte.1 htmk_k hscr_k htmk0_f
                              hpres_k hteid_lt hmb
                          let idx_t := teid &&& 1023#32
                          have h1056 : 1056 < scr_k.length := by omega
                          have h1057 : 1057 < scr_k.length := by omega
                          have hm_b1 : (mb + idx_t >>> 5).toNat < scr_k.length := by
                            dsimp only [idx_t]; omega
                          dsimp only [m7_p6_clr_state] at hm_k
                          c0_hsteps!
                          exact hQ _ _ hinv_f htmk_f rfl rfl rfl (Nat.le_refl _)
                            (fun i hi => by
                              rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
                                List.getElem?_set_ne (by rcases hmb with rfl | rfl <;> bv_omega)]
                              exact hpres_k i (by omega))
                            (fun j hj => by
                              rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
                                List.getElem?_set_ne (by rcases hmb with rfl | rfl <;> bv_omega)]
                              exact hpres_k (512 + j) (by omega))
                            (m7_p6_fullMem_subst ‹_› rfl rfl)
                        · intro J5 hJ5
                          c0_hsplit
                          · c0_hsteps!; exact hJ5 1024#32 m ⟨Or.inl rfl, rfl⟩
                          · c0_hsteps!; exact hJ5 1040#32 m ⟨Or.inr rfl, rfl⟩
                      · c0_hsplit
                        · c0_hsteps!
                          exact m7_p6_gates_inv_exit s0 hinv_clr htmk_clr rfl rfl rfl
                            (Nat.le_refl _) (fun k hk => hpres_k k (by omega)) hm_k hnp hnn hQ
                        · c0_hsplit
                          · c0_hsteps!
                            exact m7_p6_gates_inv_exit s0 hinv_clr htmk_clr rfl rfl rfl
                              (Nat.le_refl _) (fun k hk => hpres_k k (by omega)) hm_k hnp hnn hQ
                          · c0_hsplit
                            · c0_hsteps!
                              exact m7_p6_gates_inv_exit s0 hinv_clr htmk_clr rfl rfl rfl
                                (Nat.le_refl _) (fun k hk => hpres_k k (by omega)) hm_k hnp hnn hQ
                            · have hnv_pos : 0 < nv.toNat := by c0_bound
                              have hnc_ge2 : 2 ≤ nc.toNat := by c0_bound
                              have hal_le : al.toNat ≤ c.scratch_cap - 4008 := hcls.2.2.1
                              refine m7_p6_k6_init_solve_wp Γ Q X c s0 s_clr R
                                _ nv nc al _ nu scr_k m _
                                ?_ hcap_lt h8192 hscr_k rfl hnv_pos hnv64 hnc_ge2 hnc128 hal_le
                                ?_ hpres_k hcls_k hm_k ?_
                              · bv_omega
                              · bv_omega
                              · intro scr_pre kb_w0 scr2 m_sp hlen2 hpre_len hpre_eq hpres2
                                  hkb_eq hkb_ok hkb_len h1 h2 hm_sp
                                refine m7_p6_k6_watch_solve_wp Γ h_watch h_solve h_core c s0 s_clr R
                                  scr_pre kb_w0 scr2 nc m_sp Q X hcap_lt h8192 hnc128 rfl hlen2
                                  hpre_len hpre_eq hpres2 hkb_eq hkb_ok hkb_len h1 h2 hm_sp ?_
                                intro fl' scr' m' hfl' hlen' hpres' hm'
                                let s_f : FullState :=
                                  { core := { s_clr.core with fuel := fl' },
                                    scratch := { s_clr.scratch with scratch_buf := scr' } }
                                exact hQ s_f m'
                                  (m7_p6_fullDenseInvW_fuel
                                    (m7_p6_fullDenseInvW_def hinv_clr
                                      hinv_clr.1.core_ok.tmp_len_arr
                                      hinv_clr.1.scratch_ok.wsort_len
                                      hinv_clr.1.scratch_ok.tarjan_mark_len hlen') fl')
                                  htmk_clr rfl rfl rfl hfl'
                                  (fun i hi => hpres' i (by omega))
                                  (fun j hj => hpres' (512 + j) (by omega))
                                  hm'
                · intro J3 hJ3
                  c0_hsplit
                  · c0_hsplit
                    · c0_hsteps!
                      exact hJ3 () m hsideInv
                    · c0_hsplit
                      · have hside_lt2 : side.toNat < 2 := by c0_bound
                        have hcv_bd : s0.core.cur_vars ≤ 2 ^ 29 - 1 := by
                          have := hinv.1.core_ok.cur_vars_le; have := c.hmaxv
                          rw [show dimacsBound = 2 ^ 28 from rfl] at *; omega
                        c0_hsteps_nogrp
                        refine wp_join_state (ts := [i32]) (fun cnt => (cnt, ()))
                          (fun cnt m' => (side = 0#32 → cnt = np) ∧ (side ≠ 0#32 → cnt = nn) ∧
                            m' = m) ?_ ?_
                        · intro _ cnt m1 ⟨hc0, hc1, hm1⟩
                          subst m1
                          c0_hsteps_nogrp
                          refine wp_join_state (ts := [i32]) (fun off => (off, ()))
                            (fun off m' => (side = 0#32 → off = 0#32) ∧
                              (side ≠ 0#32 → off = 512#32) ∧ m' = m) ?_ ?_
                          · intro _ off m2 ⟨ho0, ho1, hm2⟩
                            subst m2
                            c0_hsteps_nogrp
                            refine wp_join_state (ts := [i32]) (fun ex => (ex, ()))
                              (fun ex m' => (side = 0#32 → ex = v <<< 1) ∧
                                (side ≠ 0#32 → ex = (v <<< 1) ||| 1#32) ∧ m' = m) ?_ ?_
                            · intro _ ex m3 ⟨he0, he1, hm3⟩
                              subst m3
                              obtain ⟨hcnt_le, hoff_le, hex_lt, hentry⟩ :=
                                m7_p6_side_setup_wide hcv_bd hv hnp128 hnn128 hside_lt2 hpos hneg
                                  ⟨hc0, hc1⟩ ⟨ho0, ho1⟩ ⟨he0, he1⟩
                              c0_hsteps_nogrp
                              refine wp_join_state
                                (ts := [i32, i32, i32, i32, i32, Ty.bool, i32]) (fun p => p)
                                (fun p m' => ∃ nv' nc' al' nu' teid' j' : BitVec 32,
                                  ∃ ab' : Bool,
                                  p = (nv', nc', al', nu', teid', ab', j', ()) ∧
                                  nv'.toNat ≤ 64 ∧ nc'.toNat ≤ 128 ∧
                                  M7P6SideInv c s0 R (c.scratch_cap - 4008)
                                    nv' nc' al' nu' teid' m') ?_ ?_
                              · intro _ ⟨nv', nc', al', nu', teid', ab', j', ⟨⟩⟩ m'
                                  ⟨_, _, _, _, _, _, _, heqp, hnv'64, hnc'128, hside'⟩
                                cases heqp
                                c0_hsteps!
                                exact hrec2 (nv', nc', al', nu', teid', ab', side + 1, ()) m'
                                  (by bv_omega)
                                  ⟨nv', nc', al', nu', teid', side + 1, ab', rfl, by bv_omega,
                                    hnv'64, hnc'128, hside'⟩
                              · intro J7 hJ7
                                c0_hsteps_nogrp
                                dsimp only [Prod.fst, Prod.snd]
                                refine m7_p6_inner_loop_wp Γ Q X J7 c F0 F_cur s0 R hinv h8192
                                  hcap_lt mc hmc_le hmc_pos hmc_mv nv nc al nu teid side ab cnt
                                  off ex _ _ hnv64 hnc128 hside_lt2 (by c0_bound) ?_ ?_
                                  hcnt_le hoff_le hex_lt hentry hsideInv hJ7
                                · bv_omega
                                · bv_omega
                            · intro J6 hJ6
                              c0_hsplit
                              · c0_hsteps!
                                apply hJ6
                                refine ⟨fun _ => by bv_omega, fun h => absurd hc h, rfl⟩
                              · c0_hsteps!
                                apply hJ6
                                refine ⟨fun h => absurd h (by simp_all), fun _ => by bv_omega, rfl⟩
                          · intro J5 hJ5
                            c0_hsplit
                            · c0_hsteps!; apply hJ5
                              exact ⟨fun _ => rfl, fun h => absurd hc h, rfl⟩
                            · c0_hsteps!; apply hJ5
                              exact ⟨fun h => absurd h (by simp_all), fun _ => rfl, rfl⟩
                        · intro J4 hJ4
                          c0_hsplit
                          · c0_hsteps!; apply hJ4
                            exact ⟨fun _ => rfl, fun h => absurd hc h, rfl⟩
                          · c0_hsteps!; apply hJ4
                            exact ⟨fun h => absurd h (by simp_all), fun _ => rfl, rfl⟩
                      · c0_hsteps!
                        exact hJ3 () m hsideInv
                  · c0_hsteps!
                    exact hJ3 () m hsideInv
            · intro J1 hJ1
              c0_hsplit
              · have hmv_lt100 : c.max_vars < 100 := by
                  have hc' : c.max_vars % 2 ^ 64 < 100 := by c0_bound
                  have := c.hmaxv; rw [show dimacsBound = 2 ^ 28 from rfl] at this
                  rwa [Nat.mod_eq_of_lt (by omega)] at hc'
                c0_hsteps!
                have hmv_pos : 0 < c.max_vars := by
                  have := hinv.1.core_ok.cur_vars_le; omega
                have hmv_eq :
                    (BitVec.setWidth 32 (BitVec.ofNat 64 c.max_vars)).toNat = c.max_vars := by
                  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                exact hJ1 (BitVec.setWidth 32 (BitVec.ofNat 64 c.max_vars)) m0
                  ⟨by rw [hmv_eq]; omega, by rw [hmv_eq]; exact hmv_pos,
                   by rw [hmv_eq]; exact Nat.le_refl _, hm0⟩
              · c0_hsteps!
                have hmv_ge100 : 100 ≤ c.max_vars := by
                  have hc' : ¬ (c.max_vars % 2 ^ 64 < 100) := by c0_bound
                  have := c.hmaxv; rw [show dimacsBound = 2 ^ 28 from rfl] at this
                  rw [Nat.mod_eq_of_lt (by omega)] at hc'; omega
                exact hJ1 100#32 m0 ⟨by decide, by decide, hmv_ge100, hm0⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Definition
