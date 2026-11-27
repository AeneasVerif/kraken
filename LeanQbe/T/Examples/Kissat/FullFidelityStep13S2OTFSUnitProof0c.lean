/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S2OTFSUnitProof0a
import LeanQbe.T.Examples.Kissat.FullLearnAnaLemmas1

/-!
# Kissat Fidelity Step 13 `full_eager_subsume` WP Proof (`0c`)

Plain `public section` (`0` `@[expose]` on theorems/lemmas, `0` `import all`, `<= 100` cols,
every theorem `<= 250` lines): certifies `full_eager_subsume` against `step13EagerSubsumeSpec`
(including `h->num_redundant` decrement when a subsumed redundant clause is garbage-marked).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S2

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test
open FullLearnAnaTactics FullLearnAnaHelpers
open scoped FullArenaTactics FullLearnAnaTactics

section EagerSubsumeProof

private theorem s13_i8_sext32_zero : (0#8 : BitVec 8).signExtend 32 = 0#32 := rfl
private theorem s13_u8_zext32_zero : (0#8 : BitVec 8).setWidth 32 = 0#32 := rfl
private theorem s13_i8_sext32_eq0_prop (v : BitVec 8) :
    (v.signExtend 32 = 0#32) = (v = 0#8) := propext (i8_sext32_eq0 v)
private theorem s13_bv32_lshr_1 (x : BitVec 32) : (x >>> 1#32).toNat = x.toNat / 2 :=
  bv32_lshr_1 x
private theorem s13_bv64_four_toNat : (4 : BitVec 64).toNat = 4 := rfl
attribute [local bv_c0] Bool.true_eq_false Bool.false_eq_true s13_i8_sext32_zero
  s13_u8_zext32_zero s13_i8_sext32_eq0_prop s13_bv32_lshr_1 s13_bv64_four_toNat

private theorem s13_bv32_add1_toNat {x : BitVec 32} (h : x.toNat + 1 < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

private theorem s13_bv64_add1_toNat {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

private theorem s13_bv64_sub1_toNat {x : BitVec 64} (h : 0 < x.toNat) :
    (x - 1#64).toNat = x.toNat - 1 := by
  have hx := x.isLt; bv_omega

private theorem s13_esub_arena_add2 (cr : BitVec 32) :
    (cr.setWidth 64 + 2#64).toNat = cr.toNat + 2 := by
  have := cr.isLt; bv_omega

private theorem s13_esub_arena_add3 (cr rj : BitVec 32) :
    (cr.setWidth 64 + 3#64 + rj.setWidth 64).toNat = cr.toNat + 3 + rj.toNat := by
  have := cr.isLt; have := rj.isLt; bv_omega

private def s13EsubState (s : FullState) (lm : List (BitVec 8)) (ar : List (BitVec 32))
    (ag nr : BitVec 64) (ll : List (BitVec 32)) (es : BitVec 64) : FullState :=
  { s with
    core := { s.core with lit_mark := lm, arena := ar, arena_garbage := ag, num_redundant := nr }
    scratch := { s.scratch with last_learned := ll, eager_sub_cnt := es } }

private theorem s13EsubState_tmp (s : FullState) lm ar ag nr ll es :
    (s13EsubState s lm ar ag nr ll es).core.tmp = s.core.tmp := rfl
private theorem s13EsubState_tmp_len (s : FullState) lm ar ag nr ll es :
    (s13EsubState s lm ar ag nr ll es).core.tmp_len = s.core.tmp_len := rfl
private theorem s13EsubState_cur_vars (s : FullState) lm ar ag nr ll es :
    (s13EsubState s lm ar ag nr ll es).core.cur_vars = s.core.cur_vars := rfl
private theorem s13EsubState_arena_len (s : FullState) lm ar ag nr ll es :
    (s13EsubState s lm ar ag nr ll es).core.arena_len = s.core.arena_len := rfl
private theorem s13EsubState_trail_end (s : FullState) lm ar ag nr ll es :
    (s13EsubState s lm ar ag nr ll es).core.trail_end = s.core.trail_end := rfl
private theorem s13EsubState_lm (s : FullState) lm ar ag nr ll es :
    (s13EsubState s lm ar ag nr ll es).core.lit_mark = lm := rfl
private theorem s13EsubState_arena (s : FullState) lm ar ag nr ll es :
    (s13EsubState s lm ar ag nr ll es).core.arena = ar := rfl
private theorem s13EsubState_vals (s : FullState) lm ar ag nr ll es :
    (s13EsubState s lm ar ag nr ll es).core.vals = s.core.vals := rfl
private theorem s13EsubState_lvl (s : FullState) lm ar ag nr ll es :
    (s13EsubState s lm ar ag nr ll es).core.lvl = s.core.lvl := rfl
private theorem s13EsubState_rsns (s : FullState) lm ar ag nr ll es :
    (s13EsubState s lm ar ag nr ll es).core.rsns = s.core.rsns := rfl
private theorem s13EsubState_ll (s : FullState) lm ar ag nr ll es :
    (s13EsubState s lm ar ag nr ll es).scratch.last_learned = ll := rfl
attribute [local bv_c0] s13EsubState_tmp s13EsubState_tmp_len s13EsubState_cur_vars
  s13EsubState_arena_len s13EsubState_trail_end s13EsubState_lm s13EsubState_arena
  s13EsubState_vals s13EsubState_lvl s13EsubState_rsns s13EsubState_ll

private theorem s13_list_bv8_eq_of_getD0 {xs ys : List (BitVec 8)} {n : Nat}
    (hx : xs.length = n) (hy : ys.length = n)
    (hxs : ∀ i < n, xs[i]?.getD 0#8 = 0#8) (hys : ∀ i < n, ys[i]?.getD 0#8 = 0#8) :
    xs = ys := by
  apply List.ext_getElem (hx.trans hy.symm)
  intro i hix hiy
  have hx0 := hxs i (hx ▸ hix); have hy0 := hys i (hy ▸ hiy)
  rw [List.getElem?_eq_getElem hix, Option.getD_some] at hx0
  rw [List.getElem?_eq_getElem hiy, Option.getD_some] at hy0
  exact hx0.trans hy0.symm

private theorem s13EsubState_lengths {c : FullCfg} {s : FullState}
    (hs : s.LengthsOk c) {lm : List (BitVec 8)} {ar ll : List (BitVec 32)}
    {ag nr es : BitVec 64} (hlm : lm.length = 2 * c.max_vars)
    (har : ar.length = c.arena_cap) (hll : ll.length = 16) :
    (s13EsubState s lm ar ag nr ll es).LengthsOk c :=
  ⟨{ hs.core_ok with lit_mark_len := hlm, arena_len_arr := har },
   { hs.scratch_ok with last_learned_len := hll }⟩

private theorem s13_arenaClauseRefs_congr {s1 s2 : FullState}
    (ha : s1.core.arena = s2.core.arena) (hl : s1.core.arena_len = s2.core.arena_len) :
    fullArenaClauseRefs s1 = fullArenaClauseRefs s2 := by
  unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [ha, hl]

private theorem s13_arenaVarsNodup_congr {s1 s2 : FullState}
    (ha : s1.core.arena = s2.core.arena) (hl : s1.core.arena_len = s2.core.arena_len) :
    FullArenaVarsNodup s1 ↔ FullArenaVarsNodup s2 := by
  unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseRefsCore fullArenaClauseGarb
    fullArenaClauseGarbCore fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore
    fullArenaHdrCore
  rw [ha, hl]

private theorem s13_fullWitness_with_litMark {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (lm : List (BitVec 8)) :
    FullWitnessInv c F0 F_cur { k with lit_mark := lm } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }

private theorem s13_getElem_congr_idx {α : Type} {xs : List α} {i j : Nat}
    (h : i = j) {hi : i < xs.length} {hj : j < xs.length} :
    xs[i]'hi = xs[j]'hj := by
  subst h; rfl

private theorem s13_mem_fullArenaClauseLitsCore {k : FullCoreState} {r j : Nat}
    (hj : j < fullArenaClauseSizeCore k r) (hb : r + 3 + j < k.arena.length) :
    (k.arena[r + 3 + j]?.getD 0#32).toNat ∈ fullArenaClauseLitsCore k r := by
  unfold fullArenaClauseLitsCore
  rw [List.mem_map]
  refine ⟨k.arena[r + 3 + j]'hb, ?_, ?_⟩
  · rw [List.mem_iff_getElem]
    refine ⟨j, ?_, ?_⟩
    · rw [List.length_take, List.length_drop]; omega
    · rw [List.getElem_take, List.getElem_drop]
  · rw [List.getElem?_eq_getElem hb, Option.getD_some]

private theorem s13_fullArenaClauseLitsCore_mem_iff {k : FullCoreState} {r l : Nat} :
    l ∈ fullArenaClauseLitsCore k r →
      ∃ j < fullArenaClauseSizeCore k r,
        r + 3 + j < k.arena.length ∧ (k.arena[r + 3 + j]?.getD 0#32).toNat = l := by
  intro hmem
  unfold fullArenaClauseLitsCore at hmem
  obtain ⟨el, hel, hle⟩ := List.mem_map.mp hmem
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hel
  rw [List.length_take, List.length_drop] at hj
  have hlt : j < fullArenaClauseSizeCore k r := by omega
  have hb : r + 3 + j < k.arena.length := by omega
  refine ⟨j, hlt, hb, ?_⟩
  rw [List.getElem_take, List.getElem_drop] at hle
  rw [List.getElem?_eq_getElem hb, Option.getD_some]
  exact hle

private theorem s13_ll_set_of_mem {refs : List Nat} {ll : List (BitVec 32)} {q : Nat}
    {cr : BitVec 32} (hll : FullLastLearnedIn refs ll) (hmem : cr.toNat ∈ refs) :
    FullLastLearnedIn refs (ll.set q cr) := by
  intro k hk
  by_cases hkq : k = q
  · subst hkq
    by_cases hlt : k < ll.length
    · rw [List.getElem?_set_self hlt, Option.getD_some]; exact Or.inr hmem
    · rw [List.getElem?_eq_none (by simp; omega), Option.getD_none]; exact Or.inl rfl
  · rw [List.getElem?_set_ne (Ne.symm hkq)]; exact hll k hk

private theorem s13_esub_loop2a_wp {Γ X} {Q : Post []} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s2 : FullState} {R : Mem 64 → Prop} {m2 : Mem 64}
    {cr csz : BitVec 32} {lm1 : List (BitVec 8)}
    (hs2 : s2.LengthsOk c) (hw2 : FullWitnessInv c F0 F_cur s2.core)
    (hs2_lm : s2.core.lit_mark = lm1) (hlm1_len : lm1.length = 2 * c.max_vars)
    (hcr_ref : cr.toNat ∈ fullArenaClauseRefs s2) (hcr_ng : fullArenaClauseGarb s2 cr.toNat = false)
    (hcr_sz : csz.toNat = fullArenaClauseSizeCore s2.core cr.toNat)
    (hcsz_bnd : cr.toNat + 3 + csz.toNat ≤ s2.core.arena.length)
    (hm2 : (FullMem c s2 ⋆ R) m2)
    (Ja : Cont [i64, i64, i32]) (hJa : ∀ nv rv jv m, m2 = m → Ja (nv, rv, jv, ()) m) :
    ∀ {nv0 rv0 : BitVec 64},
      wp Γ Q X
        (Expr.group (sig := [[i64, i64, i32]])
          (fun Js =>
            Blocks.cons
              (fun (p : Tup Val [i64, i64, i32]) =>
                Expr.let_
                  { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool rfl,
                    args := (Arg.var p.2.2.1, Arg.var csz, ()) }
                  fun p1 =>
                  Expr.jnz (Arg.var p1.1)
                    (Expr.group (sig := [[i64, i64]])
                      (fun _ =>
                        Blocks.cons
                          (fun (p2 : Tup Val [i64, i64]) =>
                            Expr.let_
                              { sig := [i32, i32], code := OpCode.add i32,
                                args := (Arg.var p.2.2.1, Arg.imm 1, ()) }
                              fun p3 =>
                                Expr.jump Js.1
                                  (Arg.var p2.1, Arg.var p2.2.1, Arg.var p3.1, ()))
                          Blocks.nil)
                      fun Js2 =>
                      Expr.let_
                        { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var cr, ()) }
                        fun p2 =>
                        Expr.let_
                          { sig := [i64, i64], code := OpCode.add i64,
                            args := (Arg.var p2.1, Arg.imm 3, ()) }
                          fun p3 =>
                          Expr.let_
                            { sig := [i32], code := OpCode.zext 32 64,
                              args := (Arg.var p.2.2.1, ()) }
                            fun p4 =>
                            Expr.let_
                              { sig := [i64, i64], code := OpCode.add i64,
                                args := (Arg.var p3.1, Arg.var p4.1, ()) }
                              fun p5 =>
                              Expr.let_
                                { sig := [i64, i64], code := OpCode.mul i64,
                                  args := (Arg.var p5.1, Arg.imm 4, ()) }
                                fun p6 =>
                                Expr.let_
                                  { sig := [i64, i64], code := OpCode.add i64,
                                    args := (Arg.var c.pArena, Arg.var p6.1, ()) }
                                  fun p7 =>
                                  Expr.load i32 (Arg.var p7.1) fun ld =>
                                    Expr.let_
                                      { sig := [i32], code := OpCode.zext 32 64,
                                        args := (Arg.var ld, ()) }
                                      fun p8 =>
                                      Expr.let_
                                        { sig := [i64, i64], code := OpCode.add i64,
                                          args := (Arg.var c.pLitMark, Arg.var p8.1, ()) }
                                        fun p9 =>
                                        Expr.load i8 (Arg.var p9.1) fun ld8 =>
                                          Expr.let_
                                            { sig := [i32], code := OpCode.trunc 32 8,
                                              args := (Arg.imm 0, ()) }
                                            fun p10 =>
                                            Expr.let_
                                              { sig := [i8], code := OpCode.zext 8 32,
                                                args := (Arg.var ld8, ()) }
                                              fun p11 =>
                                              Expr.let_
                                                { sig := [i8], code := OpCode.zext 8 32,
                                                  args := (Arg.var p10.1, ()) }
                                                fun p12 =>
                                                Expr.let_
                                                  { sig := [i32, i32],
                                                    code := OpCode.cmp CmpOp.ne i32 Ty.bool rfl,
                                                    args := (Arg.var p11.1, Arg.var p12.1, ()) }
                                                  fun p13 =>
                                                  Expr.jnz (Arg.var p13.1)
                                                    (Expr.let_
                                                      { sig := [i64, i64], code := OpCode.sub i64,
                                                        args := (Arg.var p.1, Arg.imm 1, ()) }
                                                      fun p14 =>
                                                      Expr.let_
                                                        { sig := [i64, i64],
                                                          code := OpCode.cmp CmpOp.eq i64 Ty.bool
                                                            rfl,
                                                          args := (Arg.var p14.1, Arg.imm 0, ()) }
                                                        fun p15 =>
                                                        Expr.jnz (Arg.var p15.1)
                                                          (Expr.jump Ja
                                                            (Arg.var p14.1, Arg.var p.2.1,
                                                             Arg.var p.2.2.1, ()))
                                                          (Expr.jump Js2.1
                                                            (Arg.var p14.1, Arg.var p.2.1, ())))
                                                    (Expr.let_
                                                      { sig := [i64, i64], code := OpCode.sub i64,
                                                        args := (Arg.var p.2.1, Arg.imm 1, ()) }
                                                      fun p14 =>
                                                      Expr.let_
                                                        { sig := [i64, i64],
                                                          code := OpCode.cmp CmpOp.ult i64 Ty.bool
                                                            rfl,
                                                          args := (Arg.var p14.1, Arg.var p.1, ()) }
                                                        fun p15 =>
                                                        Expr.jnz (Arg.var p15.1)
                                                          (Expr.jump Ja
                                                            (Arg.var p.1, Arg.var p14.1,
                                                             Arg.var p.2.2.1, ()))
                                                          (Expr.jump Js2.1
                                                            (Arg.var p.1, Arg.var p14.1, ()))))
                    (Expr.jump Ja (Arg.var p.1, Arg.var p.2.1, Arg.var p.2.2.1, ())))
              Blocks.nil)
          fun Js => Expr.jump Js.1 (Arg.var nv0, Arg.var rv0, Arg.imm 0, ()))
        m2 := by
  intro nv0 rv0
  refine wp_loop_group (ts := [i64, i64, i32])
    (fun r2a (nv, rv, jv, ()) ma =>
      jv.toNat ≤ csz.toNat ∧ r2a = csz.toNat - jv.toNat ∧ m2 = ma) ?_ ?_
  · rintro L2a r2a ⟨nv, rv, jv, ⟨⟩⟩ ma hL2a ⟨hj_le, rfl, rfl⟩
    c0_clean; c0_split
    · have hj_lt : jv.toNat < csz.toNat := by assumption
      have hidx_eq := s13_esub_arena_add3 cr jv
      have hj_ar : (cr.setWidth 64 + 3#64 + jv.setWidth 64).toNat < s2.core.arena.length := by
        rw [hidx_eq]; omega
      let lit := s2.core.arena[(cr.setWidth 64 + 3#64 + jv.setWidth 64).toNat]'hj_ar
      have hlit_mem : lit.toNat ∈ fullArenaClauseLits s2 cr.toNat := by
        have hb : cr.toNat + 3 + jv.toNat < s2.core.arena.length := by omega
        have hm := s13_mem_fullArenaClauseLitsCore (k := s2.core) (r := cr.toNat) (j := jv.toNat)
          (by rw [← hcr_sz]; exact hj_lt) hb
        have heq : (s2.core.arena[cr.toNat + 3 + jv.toNat]?.getD 0#32).toNat = lit.toNat := by
          rw [List.getElem?_eq_getElem hb, Option.getD_some]
          exact congrArg BitVec.toNat
            (show s2.core.arena[cr.toNat + 3 + jv.toNat]'hb = lit from
              s13_getElem_congr_idx hidx_eq.symm)
        rwa [heq] at hm
      have hlit_lt : (lit.setWidth 64).toNat < s2.core.lit_mark.length := by
        rw [bv32_setWidth64_toNat, hs2_lm, hlm1_len]
        have := hw2.arena.lits_lt cr.toNat hcr_ref hcr_ng lit.toNat hlit_mem
        have := hs2.1.cur_vars_le; omega
      have hj1 : (jv + 1#32).toNat = jv.toNat + 1 :=
        s13_bv32_add1_toNat (by have := csz.isLt; omega)
      c0_clean; c0_split
      · c0_clean; c0_split
        · c0_steps; exact hJa (nv - 1#64) rv jv m2 rfl
        · c0_steps; exact hL2a _ (nv - 1#64, rv, jv + 1#32, ()) m2 (by rw [hj1]; omega)
            ⟨by rw [hj1]; omega, rfl, rfl⟩
      · c0_clean; c0_split
        · c0_steps; exact hJa nv (rv - 1#64) jv m2 rfl
        · c0_steps; exact hL2a _ (nv, rv - 1#64, jv + 1#32, ()) m2 (by rw [hj1]; omega)
            ⟨by rw [hj1]; omega, rfl, rfl⟩
    · c0_steps; exact hJa nv rv jv m2 rfl
  · intro J2a hJ2a; c0_steps
    exact hJ2a csz.toNat (nv0, rv0, 0#32, ()) m2 ⟨Nat.zero_le _, rfl, rfl⟩

private theorem s13_esub_nonact_of_scan {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s2 : FullState} {cr csz : BitVec 32} (hw2 : FullWitnessInv c F0 F_cur s2.core)
    (hcr_sz : csz.toNat = fullArenaClauseSizeCore s2.core cr.toNat)
    (hact_res : ∀ k < csz.toNat,
      let rl := s2.core.arena[cr.toNat + 3 + k]?.getD 0#32
      ¬ (rl.toNat < 2 * s2.core.cur_vars ∧
        BitVec.slt 0#32 (BitVec.signExtend 32 (s2.core.vals[rl.toNat]?.getD 0#8)) = true ∧
        0 < (s2.core.lvl[rl.toNat / 2]?.getD 0#32).toNat ∧
        s2.core.rsns[rl.toNat / 2]?.getD 0xFFFFFFFF#32 = cr)) :
    ∀ idx < s2.core.trail_end,
      let rsn := s2.core.rsns[(s2.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ≠ cr.toNat := by
  intro idx hidx rsn hne hlg heq
  have hmem := hw2.reason_lit_mem idx hidx hne hlg
  rw [heq] at hmem
  obtain ⟨k, hk, _, hkeq⟩ := s13_fullArenaClauseLitsCore_mem_iff hmem
  have hlt_k : k < csz.toNat := by rw [hcr_sz]; exact hk
  have hrl_lt : (s2.core.arena[cr.toNat + 3 + k]?.getD 0#32).toNat < 2 * s2.core.cur_vars := by
    rw [hkeq]; exact hw2.trail_lits_lt idx hidx
  have hval1 : s2.core.vals[(s2.core.arena[cr.toNat + 3 + k]?.getD 0#32).toNat]?.getD 0#8 = 1#8 :=
    (hw2.vals_true_iff _ hrl_lt).mpr ⟨idx, hidx, hkeq.symm⟩
  have hslt1 : BitVec.slt 0#32 (BitVec.signExtend 32
      (s2.core.vals[(s2.core.arena[cr.toNat + 3 + k]?.getD 0#32).toNat]?.getD 0#8)) = true := by
    rw [hval1]; exact i8_eq1_slt0_sext32
  have hlvl_pos : 0 < (s2.core.lvl[(s2.core.arena[cr.toNat + 3 + k]?.getD 0#32).toNat / 2]?.getD
      0#32).toNat := by
    rw [hkeq]
    exact Classical.byContradiction fun h0 => by
      have hl0 : (s2.core.lvl[(s2.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
        omega
      exact hne (hw2.level0_rsn_none idx hidx hl0)
  have hrsn_eq : s2.core.rsns[(s2.core.arena[cr.toNat + 3 + k]?.getD 0#32).toNat / 2]?.getD
      0xFFFFFFFF#32 = cr := by
    apply BitVec.eq_of_toNat_eq; rw [hkeq]; exact heq
  exact hact_res k hlt_k ⟨hrl_lt, hslt1, hlvl_pos, hrsn_eq⟩

private theorem s13_esub_mark_garb_inv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {lm1 : List (BitVec 8)} {ar2 ll2 : List (BitVec 32)}
    {ag2 nr2 es2 ag' nr' es' : BitVec 64} {cr : BitVec 32} {i2 : Nat}
    (hs1 : s.LengthsOk c) (hlm1_len : lm1.length = 2 * c.max_vars)
    (hs2 : (s13EsubState s lm1 ar2 ag2 nr2 ll2 es2).LengthsOk c)
    (hw2 : FullWitnessInv c F0 F_cur (s13EsubState s lm1 ar2 ag2 nr2 ll2 es2).core)
    (hnd2 : FullArenaVarsNodup (s13EsubState s lm1 ar2 ag2 nr2 ll2 es2))
    (hll2 : FullLastLearnedWf (s13EsubState s lm1 ar2 ag2 nr2 ll2 es2))
    (hrefs2 : fullArenaClauseRefs (s13EsubState s lm1 ar2 ag2 nr2 ll2 es2) = fullArenaClauseRefs s)
    (hcr_ref : cr.toNat ∈ fullArenaClauseRefs (s13EsubState s lm1 ar2 ag2 nr2 ll2 es2))
    (hnonact : ∀ idx < (s13EsubState s lm1 ar2 ag2 nr2 ll2 es2).core.trail_end,
      let s2 := s13EsubState s lm1 ar2 ag2 nr2 ll2 es2
      let rsn := s2.core.rsns[(s2.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ≠ cr.toNat) :
    let s2 := s13EsubState s lm1 ar2 ag2 nr2 ll2 es2
    let ar' := ar2.set cr.toNat (fullArenaHdr s2 cr.toNat ||| 0x00080000#32)
    let ll' := ll2.set i2 0xFFFFFFFF#32
    let s' := s13EsubState s lm1 ar' ag' nr' ll' es'
    s'.LengthsOk c ∧ FullWitnessInv c F0 F_cur s'.core ∧ FullArenaVarsNodup s' ∧
      FullLastLearnedWf s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s := by
  intro s2 ar' ll' s'
  obtain ⟨hw', hrefs'⟩ := markGarb_preserves_fullWitness hw2 hs2 hcr_ref ag' hnonact
  have hnd' := FullArenaVarsNodup.of_markGarb_w hw2 hs2 hnd2 hcr_ref ag'
  have hll_in' : FullLastLearnedIn (fullArenaClauseRefs s2) ll' :=
    fullLastLearnedIn_set_sentinel hll2 i2
  have har'_eq : { s2 with core := { s2.core with
      arena := s2.core.arena.set cr.toNat (fullArenaHdr s2 cr.toNat ||| 0x00080000#32),
      arena_garbage := ag' } }.core.arena = ar' := rfl
  have href_s' : fullArenaClauseRefs s' = fullArenaClauseRefs s2 :=
    (s13_arenaClauseRefs_congr har'_eq.symm rfl).trans hrefs'
  have hll' : FullLastLearnedWf s' := by
    intro k hk
    change ll'[k]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
      (ll'[k]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefs s'
    rw [href_s']; exact hll_in' k hk
  have hnd_s' : FullArenaVarsNodup s' := (s13_arenaVarsNodup_congr har'_eq rfl).mp hnd'
  have hll_len' : ll'.length = 16 := by
    simp [ll', show ll2.length = 16 from hs2.2.last_learned_len]
  have hw_nr : FullWitnessInv c F0 F_cur s'.core :=
    { hw' with
      arena := { hw'.arena with len_ok := hw'.arena.len_ok }
      watches := hw'.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
  have har2_l : ar2.length = c.arena_cap := hs2.1.arena_len_arr
  exact ⟨s13EsubState_lengths hs1 hlm1_len (by simp [ar', har2_l]) hll_len',
    hw_nr, hnd_s', hll', href_s'.trans hrefs2⟩

private theorem s13_esub_compact_wp {Γ X} {Q : Post []} {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {lm3 : List (BitVec 8)} {ar2 ll2 : List (BitVec 32)}
    {ag2 nr2 es2 : BitVec 64} {m3 : Mem 64} {subv : Val .bool}
    (hll2_len : ll2.length = 16)
    (hll2_in : FullLastLearnedIn
      (fullArenaClauseRefs (s13EsubState s lm3 ar2 ag2 nr2 ll2 es2)) ll2)
    (hm3 : (FullMem c (s13EsubState s lm3 ar2 ag2 nr2 ll2 es2) ⋆ R) m3)
    (Jcomp : Cont [])
    (hJcomp : ∀ ll_c : List (BitVec 32), ll_c.length = 16 →
      FullLastLearnedIn (fullArenaClauseRefs (s13EsubState s lm3 ar2 ag2 nr2 ll2 es2)) ll_c →
      ∀ m_c, (FullMem c (s13EsubState s lm3 ar2 ag2 nr2 ll_c es2) ⋆ R) m_c → Jcomp () m_c) :
    wp Γ Q X
      (Expr.jnz (Arg.var subv)
        (Expr.group (sig := [[i64, i64]])
          (fun Lp =>
            Blocks.cons
              (fun p =>
                Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i64 Ty.bool rfl)
                  (Arg.var p.2.1, Arg.imm 4, ())) fun p1 =>
                Expr.jnz (Arg.var p1.1)
                  (Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p.2.1, Arg.imm 4, ())) fun p2 =>
                    Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pLastLearned, Arg.var p2.1, ()))
                      fun p3 =>
                    Expr.load i32 (Arg.var p3.1) fun cr =>
                    Expr.group (sig := [[i64]])
                      (fun _ =>
                        Blocks.cons
                          (fun qn =>
                            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p.2.1, Arg.imm 1, ()))
                              fun p4 =>
                            Expr.jump Lp.1 (Arg.var qn.1, Arg.var p4.1, ()))
                          Blocks.nil)
                      fun Jp =>
                      Expr.let_ (Op.mk (OpCode.cmp CmpOp.ne i32 Ty.bool rfl)
                        (Arg.var cr, Arg.imm 4294967295, ())) fun p5 =>
                      Expr.jnz (Arg.var p5.1)
                        (Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p.1, Arg.imm 4, ())) fun p6 =>
                          Expr.let_ (Op.mk (OpCode.add i64)
                              (Arg.var c.pLastLearned, Arg.var p6.1, ())) fun p7 =>
                          Expr.store (t := i32) (Arg.var cr) (Arg.var p7.1)
                            (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p.1, Arg.imm 1, ()))
                              fun p8 =>
                              Expr.jump Jp.1 (Arg.var p8.1, ())))
                        (Expr.jump Jp.1 (Arg.var p.1, ())))
                  (Expr.group (sig := [[i64]])
                    (fun Lq =>
                      Blocks.cons
                        (fun q =>
                          Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i64 Ty.bool rfl)
                            (Arg.var q.1, Arg.imm 4, ())) fun p1 =>
                          Expr.jnz (Arg.var p1.1)
                            (Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var q.1, Arg.imm 4, ()))
                              fun p2 =>
                              Expr.let_ (Op.mk (OpCode.add i64)
                                  (Arg.var c.pLastLearned, Arg.var p2.1, ())) fun p3 =>
                              Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var p3.1)
                                (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var q.1, Arg.imm 1, ()))
                                  fun p4 =>
                                  Expr.jump Lq.1 (Arg.var p4.1, ())))
                            (Expr.jump Jcomp ()))
                        Blocks.nil)
                    fun Lq => Expr.jump Lq.1 (Arg.var p.1, ())))
              Blocks.nil)
          fun Lp => Expr.jump Lp.1 (Arg.imm 0, Arg.imm 0, ()))
        (Expr.jump Jcomp ()))
      m3 := by
  let s3 := s13EsubState s lm3 ar2 ag2 nr2 ll2 es2
  c0_clean; c0_split
  · c0_to_group
    refine wp_loop_group (ts := [i64, i64])
      (fun rp (qv, pv, ()) mp => ∃ q p llp,
        q ≤ p ∧ p ≤ 4 ∧ rp = 4 - p ∧ qv = BitVec.ofNat 64 q ∧ pv = BitVec.ofNat 64 p ∧
        llp.length = 16 ∧ FullLastLearnedIn (fullArenaClauseRefs s3) llp ∧
        (FullMem c (s13EsubState s lm3 ar2 ag2 nr2 llp es2) ⋆ R) mp) ?_ ?_
    · rintro Lp rp ⟨qv, pv, ⟨⟩⟩ mp hLp
        ⟨q, p, llp, hqp, hp_le, rfl, rfl, rfl, hllp_len, hllp_in, hmp⟩
      have hp_lt64 : p < 2 ^ 64 := by omega
      have hq_lt64 : q < 2 ^ 64 := by omega
      c0_clean; c0_split
      · have hp_lt : p < 4 := by rw [Nat.mod_eq_of_lt hp_lt64] at hc; exact hc
        have hp_idx : (BitVec.ofNat 64 p).toNat = p := bv64_ofNat_toNat hp_lt64
        have hq_idx : (BitVec.ofNat 64 q).toNat = q := bv64_ofNat_toNat hq_lt64
        have hp_ll : (BitVec.ofNat 64 p).toNat < llp.length := by rw [hp_idx, hllp_len]; omega
        have hq_ll : (BitVec.ofNat 64 q).toNat < llp.length := by rw [hq_idx, hllp_len]; omega
        c0_steps
        refine wp_load_of (FullArenaTactics.c0_load_full_last_learned hp_ll hmp) ?_
        let crp := llp[(BitVec.ofNat 64 p).toNat]'hp_ll
        c0_to_group
        refine wp_join_group (ts := [i64])
          (fun (qn, ()) mn => ∃ q' ll',
            q' ≤ p + 1 ∧ qn = BitVec.ofNat 64 q' ∧ ll'.length = 16 ∧
            FullLastLearnedIn (fullArenaClauseRefs s3) ll' ∧
            (FullMem c (s13EsubState s lm3 ar2 ag2 nr2 ll' es2) ⋆ R) mn) ?_ ?_
        · rintro _ ⟨qn, ⟨⟩⟩ mn ⟨q', ll', hq'le, rfl, hll'_len, hll'_in, hmn⟩
          c0_steps
          have hp1 : (BitVec.ofNat 64 p + 1#64).toNat = p + 1 := by
            rw [s13_bv64_add1_toNat (by rw [hp_idx]; omega), hp_idx]
          exact hLp (4 - (p + 1)) (BitVec.ofNat 64 q', BitVec.ofNat 64 p + 1#64, ()) mn (by omega)
            ⟨q', p + 1, ll', hq'le, by omega, rfl, rfl,
              BitVec.eq_of_toNat_eq (by rw [hp1, bv64_ofNat_toNat (by omega)]),
              hll'_len, hll'_in, hmn⟩
        · intro Jp hJp; c0_clean; c0_split
          · have hcrp_ne : crp ≠ 0xFFFFFFFF#32 := by assumption
            have hcrp_mem : crp.toNat ∈ fullArenaClauseRefs s3 := by
              have hp_m := hllp_in p (by omega)
              have hget : llp[p]?.getD 0xFFFFFFFF#32 = crp := by
                rw [List.getElem?_eq_getElem (by rw [hllp_len]; omega), Option.getD_some]
                exact (s13_getElem_congr_idx hp_idx).symm
              rw [hget] at hp_m; exact hp_m.resolve_left hcrp_ne
            c0_steps
            refine wp_store_sep (FullArenaTactics.c0_store_full_last_learned crp hq_ll hmp)
              fun mq hmq => ?_
            c0_steps
            have hq1 : (BitVec.ofNat 64 q + 1#64).toNat = q + 1 := by
              rw [s13_bv64_add1_toNat (by rw [hq_idx]; omega), hq_idx]
            exact hJp (BitVec.ofNat 64 q + 1#64, ()) mq
              ⟨q + 1, llp.set (BitVec.ofNat 64 q).toNat crp, by omega,
                BitVec.eq_of_toNat_eq (by rw [hq1, bv64_ofNat_toNat (by omega)]),
                List.length_set.trans hllp_len, s13_ll_set_of_mem hllp_in hcrp_mem, hmq⟩
          · c0_steps; exact hJp (BitVec.ofNat 64 q, ()) mp
              ⟨q, llp, by omega, rfl, hllp_len, hllp_in, hmp⟩
      · clear hLp
        c0_to_group
        refine wp_loop_group (ts := [i64])
          (fun rq (qv2, ()) mq => ∃ q2 llq,
            q2 ≤ 4 ∧ rq = 4 - q2 ∧ qv2 = BitVec.ofNat 64 q2 ∧ llq.length = 16 ∧
            FullLastLearnedIn (fullArenaClauseRefs s3) llq ∧
            (FullMem c (s13EsubState s lm3 ar2 ag2 nr2 llq es2) ⋆ R) mq) ?_ ?_
        · rintro Lq rq ⟨qv2, ⟨⟩⟩ mq hLq ⟨q2, llq, hq2_le, rfl, rfl, hllq_len, hllq_in, hmq⟩
          have hq2_lt64 : q2 < 2 ^ 64 := by omega
          c0_clean; c0_split
          · have hq2_lt : q2 < 4 := by rw [Nat.mod_eq_of_lt hq2_lt64] at hc; exact hc
            have hq2_idx : (BitVec.ofNat 64 q2).toNat = q2 := bv64_ofNat_toNat hq2_lt64
            have hq2_ll : (BitVec.ofNat 64 q2).toNat < llq.length := by
              rw [hq2_idx, hllq_len]; omega
            c0_steps
            refine wp_store_sep (FullArenaTactics.c0_store_full_last_learned 0xFFFFFFFF#32
              hq2_ll hmq) fun mq' hmq' => ?_
            c0_steps
            have hq2_add : (BitVec.ofNat 64 q2 + 1#64).toNat = q2 + 1 := by
              rw [s13_bv64_add1_toNat (by rw [hq2_idx]; omega), hq2_idx]
            exact hLq (4 - (q2 + 1)) (BitVec.ofNat 64 q2 + 1#64, ()) mq' (by omega)
              ⟨q2 + 1, llq.set (BitVec.ofNat 64 q2).toNat 0xFFFFFFFF#32, by omega, rfl,
                BitVec.eq_of_toNat_eq (by rw [hq2_add, bv64_ofNat_toNat (by omega)]),
                by simp [hllq_len], fullLastLearnedIn_set_sentinel hllq_in _, hmq'⟩
          · c0_steps; exact hJcomp llq hllq_len hllq_in mq hmq
        · intro Jq hJq; c0_steps
          exact hJq (4 - q) (BitVec.ofNat 64 q, ()) mp ⟨q, llp, by omega, rfl, rfl, hllp_len,
            hllp_in, hmp⟩
    · intro Jp0 hJp0; c0_steps
      exact hJp0 4 (0#64, 0#64, ()) m3 ⟨0, 0, ll2, Nat.le_refl _, Nat.zero_le _, rfl, rfl, rfl,
        hll2_len, hll2_in, hm3⟩
  · c0_steps; exact hJcomp ll2 hll2_len hll2_in m3 hm3

private theorem s13_esub_loop2b_wp {Γ X} {Q : Post []} {c : FullCfg}
    {s s2 : FullState} {R : Mem 64 → Prop} {m2 : Mem 64}
    {lm1 : List (BitVec 8)} {ar2 ll2 : List (BitVec 32)} {ag2 nr2 es2 : BitVec 64}
    {cr csz : BitVec 32} {i2 : Nat}
    (hs2_def : s2 = s13EsubState s lm1 ar2 ag2 nr2 ll2 es2)
    (_hi2_idx : (BitVec.ofNat 64 i2).toNat = i2) (_hi2_lt : i2 < 4)
    (hi2_ll' : i2 < ll2.length) (_hcr_def : ll2[i2]'hi2_ll' = cr)
    (hs2 : s2.LengthsOk c) (hcr_sz : csz.toNat = fullArenaClauseSizeCore s2.core cr.toNat)
    (hcsz_bnd : cr.toNat + 3 + csz.toNat ≤ s.core.arena_len)
    (hal_le : s.core.arena_len ≤ c.arena_cap)
    (hm2 : (FullMem c s2 ⋆ R) m2)
    (Jb : Cont [.bool, i32])
    (hJb : ∀ act_v rj_v mb, m2 = mb →
      (act_v = false → ∀ k < csz.toNat,
        let rl := s2.core.arena[cr.toNat + 3 + k]?.getD 0#32
        ¬ (rl.toNat < 2 * s2.core.cur_vars ∧
          BitVec.slt 0#32 (BitVec.signExtend 32 (s2.core.vals[rl.toNat]?.getD 0#8)) = true ∧
          0 < (s2.core.lvl[rl.toNat / 2]?.getD 0#32).toNat ∧
          s2.core.rsns[rl.toNat / 2]?.getD 0xFFFFFFFF#32 = cr)) →
      Jb (act_v, rj_v, ()) mb) :
    wp Γ Q X
      (Expr.group (sig := [[i32]])
        (fun L2b => Blocks.cons
          (fun (p : Tup Val [i32]) =>
            Expr.let_ (Op.mk (.cmp .ult i32 .bool rfl) (Arg.var p.1, Arg.var csz, ()))
              fun pc =>
            Expr.jnz (Arg.var pc.1)
              (Expr.let_ (Op.mk (.zext 32 64) (Arg.var cr, ())) fun p0 =>
               Expr.let_ (Op.mk (.add i64) (Arg.var p0.1, Arg.imm 3, ())) fun p1 =>
               Expr.let_ (Op.mk (.zext 32 64) (Arg.var p.1, ())) fun p2 =>
               Expr.let_ (Op.mk (.add i64) (Arg.var p1.1, Arg.var p2.1, ())) fun p3 =>
               Expr.let_ (Op.mk (.mul i64) (Arg.var p3.1, Arg.imm 4, ())) fun p4 =>
               Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var p4.1, ())) fun p5 =>
               Expr.load i32 (Arg.var p5.1) fun rl =>
               Expr.group (sig := [[]])
                 (fun _ => Blocks.cons
                   (fun _ =>
                     Expr.let_ (Op.mk (.add i32) (Arg.var p.1, Arg.imm 1, ())) fun pn =>
                     Expr.jump L2b.1 (Arg.var pn.1, ()))
                   Blocks.nil)
                 fun Jnext =>
                 Expr.let_ (Op.mk (.zext 32 64) (Arg.var rl, ())) fun p6 =>
                 Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 776, ())) fun ph =>
                 Expr.load i64 (Arg.var ph.1) fun cv =>
                 Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun s1 =>
                 Expr.let_ (Op.mk (.shl i64) (Arg.var cv, Arg.var s1.1, ())) fun nl =>
                 Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var p6.1, Arg.var nl.1, ()))
                   fun plt =>
                 Expr.jnz (Arg.var plt.1)
                   (Expr.let_ (Op.mk (.zext 32 64) (Arg.var rl, ())) fun p6b =>
                    Expr.let_ (Op.mk (.add i64) (Arg.var c.pVals, Arg.var p6b.1, ())) fun pv =>
                    Expr.load i8 (Arg.var pv.1) fun v8 =>
                    Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 0, ())) fun z0 =>
                    Expr.let_ (Op.mk (.sext 8 32) (Arg.var v8, ())) fun v32 =>
                    Expr.let_ (Op.mk (.sext 8 32) (Arg.var z0.1, ())) fun z32 =>
                    Expr.let_ (Op.mk (.cmp .sgt i32 .bool rfl)
                      (Arg.var v32.1, Arg.var z32.1, ())) fun pgt =>
                    Expr.jnz (Arg.var pgt.1)
                      (Expr.let_ (Op.mk (.lshr i32) (Arg.var rl, Arg.imm 1, ())) fun r1 =>
                       Expr.let_ (Op.mk (.zext 32 64) (Arg.var r1.1, ())) fun p7 =>
                       Expr.let_ (Op.mk (.mul i64) (Arg.var p7.1, Arg.imm 4, ())) fun p8 =>
                       Expr.let_ (Op.mk (.add i64) (Arg.var c.pLevel, Arg.var p8.1, ())) fun p9 =>
                       Expr.load i32 (Arg.var p9.1) fun lv =>
                       Expr.let_ (Op.mk (.cmp .ugt i32 .bool rfl) (Arg.var lv, Arg.imm 0, ()))
                         fun plv =>
                       Expr.jnz (Arg.var plv.1)
                         (Expr.let_ (Op.mk (.lshr i32) (Arg.var rl, Arg.imm 1, ())) fun r2 =>
                          Expr.let_ (Op.mk (.zext 32 64) (Arg.var r2.1, ())) fun q7 =>
                          Expr.let_ (Op.mk (.mul i64) (Arg.var q7.1, Arg.imm 4, ())) fun q8 =>
                          Expr.let_ (Op.mk (.add i64)
                            (Arg.var c.pReason, Arg.var q8.1, ())) fun pr =>
                          Expr.load i32 (Arg.var pr.1) fun rs =>
                          Expr.let_ (Op.mk (.cmp .eq i32 .bool rfl)
                            (Arg.var rs, Arg.var cr, ())) fun prs =>
                          Expr.jnz (Arg.var prs.1)
                            (Expr.jump Jb (Arg.imm true, Arg.var p.1, ()))
                            (Expr.jump Jnext.1 ()))
                         (Expr.jump Jnext.1 ()))
                      (Expr.jump Jnext.1 ()))
                   (Expr.jump Jnext.1 ()))
              (Expr.jump Jb (Arg.imm false, Arg.var p.1, ())))
          Blocks.nil)
        fun L2b => Expr.jump L2b.1 (Arg.imm 0, ())) m2 := by
  subst hs2_def
  have har2_len : ar2.length = c.arena_cap := hs2.1.arena_len_arr
  have hcm : s.core.cur_vars ≤ c.max_vars := hs2.1.cur_vars_le
  have hvals_len : s.core.vals.length = 2 * c.max_vars := by
    simpa only [s13EsubState_vals] using hs2.1.vals_len
  have hlvl_len : s.core.lvl.length = c.max_vars := by
    simpa only [s13EsubState_lvl] using hs2.1.lvl_len
  have hrsns_len : s.core.rsns.length = c.max_vars := by
    simpa only [s13EsubState_rsns] using hs2.1.rsns_len
  have hmv32 := fullInv_max_vars_lt32 c
  have hcv63 : 2 * s.core.cur_vars < 2 ^ 64 := by omega
  have hcv64 : s.core.cur_vars < 2 ^ 64 := by omega
  c0_clean; c0_to_group
  refine wp_loop_group (ts := [i32])
    (fun r2b (rjv, ()) mb => ∃ rj : BitVec 32,
      rj.toNat ≤ csz.toNat ∧ r2b = csz.toNat - rj.toNat ∧ rjv = rj ∧ m2 = mb ∧
      ∀ k < rj.toNat,
        let rl := ar2[cr.toNat + 3 + k]?.getD 0#32
        ¬ (rl.toNat < 2 * s.core.cur_vars ∧
          BitVec.slt 0#32 (BitVec.signExtend 32 (s.core.vals[rl.toNat]?.getD 0#8)) = true ∧
          0 < (s.core.lvl[rl.toNat / 2]?.getD 0#32).toNat ∧
          s.core.rsns[rl.toNat / 2]?.getD 0xFFFFFFFF#32 = cr)) ?_ ?_
  · rintro L2b r2b ⟨rj, ⟨⟩⟩ mb hL2b ⟨rj', hrj_le, rfl, rfl, hm_eq, hinv_b⟩
    subst hm_eq
    have hcsz_lt : csz.toNat < 2 ^ 32 := csz.isLt
    c0_clean; c0_split
    · have hrj_lt : rj.toNat < csz.toNat := by assumption
      have hrj1_nat : (rj + 1#32).toNat = rj.toNat + 1 := s13_bv32_add1_toNat (by omega)
      have hadd3_eq := s13_esub_arena_add3 cr rj
      have hrj_ar : (cr.setWidth 64 + 3#64 + rj.setWidth 64).toNat < ar2.length := by
        rw [hadd3_eq, har2_len]; omega
      let rl := ar2[(cr.setWidth 64 + 3#64 + rj.setWidth 64).toNat]'hrj_ar
      have hrl_eq : ar2[cr.toNat + 3 + rj.toNat]?.getD 0#32 = rl := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        exact s13_getElem_congr_idx hadd3_eq.symm
      have hstep_b :
          ¬ (rl.toNat < 2 * s.core.cur_vars ∧
            BitVec.slt 0#32 (BitVec.signExtend 32 (s.core.vals[rl.toNat]?.getD 0#8)) = true ∧
            0 < (s.core.lvl[rl.toNat / 2]?.getD 0#32).toNat ∧
            s.core.rsns[rl.toNat / 2]?.getD 0xFFFFFFFF#32 = cr) →
          ∀ k < (rj + 1#32).toNat,
            let rlk := ar2[cr.toNat + 3 + k]?.getD 0#32
            ¬ (rlk.toNat < 2 * s.core.cur_vars ∧
              BitVec.slt 0#32 (BitVec.signExtend 32 (s.core.vals[rlk.toNat]?.getD 0#8)) = true ∧
              0 < (s.core.lvl[rlk.toNat / 2]?.getD 0#32).toNat ∧
              s.core.rsns[rlk.toNat / 2]?.getD 0xFFFFFFFF#32 = cr) := by
        intro hnot k hk; rw [hrj1_nat] at hk
        by_cases hke : k = rj.toNat
        · subst hke; dsimp only; rwa [hrl_eq]
        · exact hinv_b k (by omega)
      have hidx_mod : (cr.toNat + 3 + rj.toNat) % 2 ^ 64 =
          (cr.setWidth 64 + 3#64 + rj.setWidth 64).toNat := by
        rw [hadd3_eq, Nat.mod_eq_of_lt (by omega)]
      have hrl_hc : ar2[(cr.toNat + 3 + rj.toNat) % 2 ^ 64]'(by
          rw [hidx_mod]; exact hrj_ar) = rl :=
        s13_getElem_congr_idx hidx_mod
      c0_clean; c0_to_group
      refine wp_join_group (ts := []) (fun () mj =>
        ¬ (rl.toNat < 2 * s.core.cur_vars ∧
          BitVec.slt 0#32 (BitVec.signExtend 32 (s.core.vals[rl.toNat]?.getD 0#8)) = true ∧
          0 < (s.core.lvl[rl.toNat / 2]?.getD 0#32).toNat ∧
          s.core.rsns[rl.toNat / 2]?.getD 0xFFFFFFFF#32 = cr) ∧ m2 = mj) ?_ ?_
      · rintro _ ⟨⟩ mj ⟨hnot, rfl⟩; c0_steps
        exact hL2b _ (rj + 1#32, ()) m2 (by rw [hrj1_nat]; omega)
          ⟨rj + 1#32, by rw [hrj1_nat]; omega, rfl, rfl, rfl, hstep_b hnot⟩
      · intro J hJ; c0_clean; c0_split
        · have hrl_lt_cv : rl.toNat < 2 * s.core.cur_vars := by
            have hlt_hc : rl.toNat < 2 * (s.core.cur_vars % 2 ^ 64) % 2 ^ 64 := by
              simpa only [s13EsubState_arena, s13EsubState_cur_vars, hrl_hc] using hc
            rwa [Nat.mod_eq_of_lt hcv64, Nat.mod_eq_of_lt hcv63] at hlt_hc
          have hrl_vals : (rl.setWidth 64).toNat < s.core.vals.length := by
            rw [bv32_setWidth64_toNat, hvals_len]; omega
          c0_clean; c0_split
          · have hrl_lvl : ((rl >>> 1#32).setWidth 64).toNat < s.core.lvl.length := by
              rw [bv32_setWidth64_toNat, s13_bv32_lshr_1, hlvl_len]; omega
            have hrl_rsns : ((rl >>> 1#32).setWidth 64).toNat < s.core.rsns.length := by
              rw [bv32_setWidth64_toNat, s13_bv32_lshr_1, hrsns_len]; omega
            c0_clean; c0_split
            · c0_clean; c0_split
              · c0_steps; exact hJb true rj m2 rfl fun h => by cases h
              · have hne_rs : s.core.rsns[rl.toNat / 2]?.getD 0xFFFFFFFF#32 ≠ cr := by
                  have hlen_r : rl.toNat / 2 < s.core.rsns.length := by rw [hrsns_len]; omega
                  rw [List.getElem?_eq_getElem hlen_r, Option.getD_some]
                  simpa only [s13EsubState_rsns, s13EsubState_arena, hrl_hc] using hc
                c0_steps
                exact hJ () m2 ⟨fun ⟨_, _, _, hrs⟩ => absurd hrs hne_rs, rfl⟩
            · have hnl : ¬ 0 < (s.core.lvl[rl.toNat / 2]?.getD 0#32).toNat := by
                have hlen_l : rl.toNat / 2 < s.core.lvl.length := by rw [hlvl_len]; omega
                rw [List.getElem?_eq_getElem hlen_l, Option.getD_some]
                simpa only [s13EsubState_lvl, s13EsubState_arena, hrl_hc,
                  show BitVec.toNat (0 : BitVec 32) = 0 from rfl] using hc
              c0_steps
              exact hJ () m2 ⟨fun ⟨_, _, hpos, _⟩ => hnl hpos, rfl⟩
          · have hnslt : ¬ BitVec.slt 0#32 (BitVec.signExtend 32
                (s.core.vals[rl.toNat]?.getD 0#8)) = true := by
              have hlen_v : rl.toNat < s.core.vals.length := by rw [hvals_len]; omega
              rw [List.getElem?_eq_getElem hlen_v, Option.getD_some]
              have hc0 : BitVec.slt 0#32 (BitVec.signExtend 32
                  (s.core.vals[rl.toNat]'hlen_v)) = false := by
                simpa only [s13EsubState_vals, s13EsubState_arena, hrl_hc] using hc
              rw [hc0]; decide
            c0_steps
            exact hJ () m2 ⟨fun ⟨_, hslt, _⟩ => hnslt hslt, rfl⟩
        · have hnlt : ¬ rl.toNat < 2 * s.core.cur_vars := by
            have hc0 : ¬ rl.toNat < 2 * (s.core.cur_vars % 2 ^ 64) % 2 ^ 64 := by
              simpa only [s13EsubState_arena, s13EsubState_cur_vars, hrl_hc] using hc
            rwa [Nat.mod_eq_of_lt hcv64, Nat.mod_eq_of_lt hcv63] at hc0
          c0_steps
          exact hJ () m2 ⟨fun ⟨hlt, _⟩ => hnlt hlt, rfl⟩
    · have hrj_eq : rj.toNat = csz.toNat := by
        have hc0 : ¬ rj.toNat < csz.toNat := by assumption
        omega
      c0_steps
      exact hJb false rj m2 rfl fun _ k hk => hinv_b k (hrj_eq ▸ hk)
  · intro J2b hJ2b; c0_steps
    exact hJ2b csz.toNat (0#32, ()) m2
      ⟨0#32, Nat.zero_le _, rfl, rfl, rfl, fun k hk => by simp at hk⟩

private theorem s13_esub_loop4_wp {Γ X} {Q : Post []} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop} {m_c : Mem 64}
    {lm3 : List (BitVec 8)} {ar2 ll_c : List (BitVec 32)} {ag2 nr2 es2 : BitVec 64}
    {new_ref : BitVec 64}
    (_hs : s.LengthsOk c) (hlm3_eq : lm3 = s.core.lit_mark) (hllc_len : ll_c.length = 16)
    (hsc_len : ({ s with
      core := { s.core with arena := ar2, arena_garbage := ag2, num_redundant := nr2 }
      scratch := { s.scratch with last_learned := ll_c, eager_sub_cnt := es2 } } :
      FullState).LengthsOk c)
    (hwc : FullWitnessInv c F0 F_cur
      { s.core with arena := ar2, arena_garbage := ag2, num_redundant := nr2 })
    (hclrc : FullLitMarksClear c
      { s with core := { s.core with arena := ar2, arena_garbage := ag2, num_redundant := nr2 }
               scratch := { s.scratch with last_learned := ll_c, eager_sub_cnt := es2 } })
    (hndc : FullArenaVarsNodup
      { s with core := { s.core with arena := ar2, arena_garbage := ag2, num_redundant := nr2 }
               scratch := { s.scratch with last_learned := ll_c, eager_sub_cnt := es2 } })
    (hllc_in : FullLastLearnedIn (fullArenaClauseRefs
      (s13EsubState s lm3 ar2 ag2 nr2 ll_c es2)) ll_c)
    (hext2 : s.scratch.extend_len ≤ c.extend_cap) (hdm : s.core.dense_mode = 0#64)
    (hwork2 : s.scratch.work_stk2 = s.scratch.work_stk2)
    (href_in : new_ref.toNat < 0x80000000 → new_ref.toNat ∈ fullArenaClauseRefs s)
    (hrefs2 : fullArenaClauseRefs (s13EsubState s lm3 ar2 ag2 nr2 ll_c es2) =
      fullArenaClauseRefs s)
    (hm_c : (FullMem c (s13EsubState s lm3 ar2 ag2 nr2 ll_c es2) ⋆ R) m_c)
    (hQ : ∀ arena' ag' nr' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with arena := arena', arena_garbage := ag', num_redundant := nr' }
          scratch := sc' }
      FullSparseInvW c F0 F_cur s' → sc'.work_stk2 = s.scratch.work_stk2 →
      (FullMem c s' ⋆ R) m' → Q () m') :
    wp Γ Q X
      (Expr.group (sig := [[]])
        (fun _Js => Blocks.cons (fun _ => Expr.ret ()) Blocks.nil)
        fun Js =>
        Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var new_ref, Arg.imm 2147483648, ()))
          fun p =>
        Expr.jnz (Arg.var p.1)
          (Expr.group (sig := [[i64]])
            (fun L4 => Blocks.cons
              (fun p =>
                Expr.let_ (Op.mk (.cmp .ugt i64 .bool rfl) (Arg.var p.1, Arg.imm 0, ()))
                  fun p_1 =>
                Expr.jnz (Arg.var p_1.1)
                  (Expr.let_ (Op.mk (.mul i64) (Arg.var p.1, Arg.imm 4, ())) fun p_2 =>
                   Expr.let_ (Op.mk (.add i64)
                     (Arg.var c.pLastLearned, Arg.var p_2.1, ())) fun p_3 =>
                   Expr.let_ (Op.mk (.sub i64) (Arg.var p.1, Arg.imm 1, ())) fun p_4 =>
                   Expr.let_ (Op.mk (.mul i64) (Arg.var p_4.1, Arg.imm 4, ())) fun p_5 =>
                   Expr.let_ (Op.mk (.add i64)
                     (Arg.var c.pLastLearned, Arg.var p_5.1, ())) fun p_6 =>
                   Expr.load i32 (Arg.var p_6.1) fun ld =>
                   Expr.store (Arg.var ld) (Arg.var p_3.1)
                     (Expr.let_ (Op.mk (.sub i64) (Arg.var p.1, Arg.imm 1, ())) fun p =>
                      Expr.jump L4.1 (Arg.var p.1, ())))
                  (Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 0, ())) fun p =>
                   Expr.let_ (Op.mk (.mul i64) (Arg.var p.1, Arg.imm 4, ())) fun p =>
                   Expr.let_ (Op.mk (.add i64)
                     (Arg.var c.pLastLearned, Arg.var p.1, ())) fun p =>
                   Expr.let_ (Op.mk (.trunc 64 32) (Arg.var new_ref, ())) fun p_2 =>
                   Expr.store (t := i32) (Arg.var p_2.1) (Arg.var p.1) (Expr.jump Js.1 ())))
              Blocks.nil)
            fun L4 => Expr.jump L4.1 (Arg.imm 3, ()))
          (Expr.jump Js.1 ())) m_c := by
  let s3 := s13EsubState s lm3 ar2 ag2 nr2 ll_c es2
  let sc_fin : FullState :=
    { s with
      core := { s.core with arena := ar2, arena_garbage := ag2, num_redundant := nr2 }
      scratch := { s.scratch with last_learned := ll_c, eager_sub_cnt := es2 } }
  c0_clean; c0_split
  · have hnref_lt : new_ref.toNat < 0x80000000 := by assumption
    have hnref_ref : new_ref.toNat ∈ fullArenaClauseRefs s3 := by
      change new_ref.toNat ∈ fullArenaClauseRefs s3; rw [hrefs2]; exact href_in hnref_lt
    c0_clean; c0_to_group
    refine wp_loop_group (ts := [i64])
      (fun k (kv, ()) m4 => ∃ ll4,
        k ≤ 3 ∧ kv = BitVec.ofNat 64 k ∧ ll4.length = 16 ∧
        FullLastLearnedIn (fullArenaClauseRefs s3) ll4 ∧
        (FullMem c (s13EsubState s lm3 ar2 ag2 nr2 ll4 es2) ⋆ R) m4) ?_ ?_
    · rintro L4 k ⟨kv, ⟨⟩⟩ m4 hL4 ⟨ll4, hk_le, rfl, hll4_len, hll4_in, hm4⟩
      have hk_lt64 : k < 2 ^ 64 := by omega
      c0_clean; c0_split
      · have hk_pos : 0 < k := by
          rw [Nat.mod_eq_of_lt hk_lt64,
            show BitVec.toNat (0 : BitVec 64) = 0 from rfl] at hc
          exact hc
        have hk1_nat : (BitVec.ofNat 64 k - 1#64).toNat = k - 1 := by
          rw [s13_bv64_sub1_toNat (by rw [bv64_ofNat_toNat hk_lt64]; exact hk_pos),
            bv64_ofNat_toNat hk_lt64]
        have hk1_idx : (BitVec.ofNat 64 k - 1#64).toNat < ll4.length := by
          rw [hk1_nat, hll4_len]; omega
        have hk_idx : (BitVec.ofNat 64 k).toNat < ll4.length := by
          rw [bv64_ofNat_toNat hk_lt64, hll4_len]; omega
        c0_steps
        refine wp_load_of (FullArenaTactics.c0_load_full_last_learned hk1_idx hm4) ?_
        refine wp_store_sep (FullArenaTactics.c0_store_full_last_learned
          (ll4[(BitVec.ofNat 64 k - 1#64).toNat]'hk1_idx)
          (by rw [s13EsubState_ll]; exact hk_idx) hm4) fun m hm => ?_
        c0_steps
        have hll_next : ll4.set (BitVec.ofNat 64 k).toNat
            (ll4[(BitVec.ofNat 64 k - 1#64).toNat]'hk1_idx) =
            ll4.set k (ll4[k - 1]'(by rw [hll4_len]; omega)) := by
          rw [bv64_ofNat_toNat hk_lt64, s13_getElem_congr_idx hk1_nat]
        refine hL4 (k - 1) (BitVec.ofNat 64 k - 1#64, ()) _ (by omega)
          ⟨ll4.set k (ll4[k - 1]'(by rw [hll4_len]; omega)), by omega,
            BitVec.eq_of_toNat_eq (by rw [hk1_nat, bv64_ofNat_toNat (by omega)]),
            by simp [hll4_len], ?_, ?_⟩
        · exact fullLastLearnedIn_shift_step hll4_in hk_pos (by omega) (by omega)
        · exact (congrArg (fun ll' =>
            (FullMem c (s13EsubState s lm3 ar2 ag2 nr2 ll' es2) ⋆ R) m) hll_next).mp hm
      · have hk_zero : k = 0 := by
          rw [Nat.mod_eq_of_lt hk_lt64,
            show BitVec.toNat (0 : BitVec 64) = 0 from rfl] at hc
          omega
        subst hk_zero
        c0_steps
        refine wp_store_sep (FullLearnAnaTactics.store_full_ll0_off (new_ref.setWidth 32)
          (by rw [s13EsubState_ll, hll4_len]; decide) hm4) fun m hm => ?_
        c0_steps
        let ll_fin := ll4.set 0 (new_ref.setWidth 32)
        let s_fin : FullState :=
          { s with
            core := { s.core with arena := ar2, arena_garbage := ag2, num_redundant := nr2 }
            scratch := { s.scratch with last_learned := ll_fin, eager_sub_cnt := es2 } }
        have hll_fin_in : FullLastLearnedIn (fullArenaClauseRefs s3) ll_fin :=
          fullLastLearnedIn_set0 hll4_in (new_ref.setWidth 32)
            (by rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact hnref_ref) (by omega)
        have hs_fin : s_fin.LengthsOk c :=
          ⟨hsc_len.core_ok, { hsc_len.scratch_ok with
            last_learned_len := by simp [s_fin, ll_fin, hll4_len] }⟩
        have hm_fin : (FullMem c s_fin ⋆ R) m :=
          (congrArg (fun lm' => (FullMem c { s_fin with core :=
              { s_fin.core with lit_mark := lm' } } ⋆ R) m) hlm3_eq).mp hm
        exact hQ ar2 ag2 nr2 s_fin.scratch m
          ⟨hs_fin, hwc, hclrc, hndc, ⟨hll_fin_in, hext2⟩, hdm⟩ hwork2 hm_fin
    · intro J4 hJ4; c0_steps
      exact hJ4 3 (3#64, ()) m_c ⟨ll_c, Nat.le_refl _, rfl, hllc_len, hllc_in, hm_c⟩
  · c0_steps
    have hmc_fin : (FullMem c sc_fin ⋆ R) m_c :=
      (congrArg (fun lm' => (FullMem c { sc_fin with core :=
          { sc_fin.core with lit_mark := lm' } } ⋆ R) m_c) hlm3_eq).mp hm_c
    exact hQ ar2 ag2 nr2 sc_fin.scratch m_c
      ⟨hsc_len, hwc, hclrc, hndc, ⟨hllc_in, hext2⟩, hdm⟩ hwork2 hmc_fin

/-- `full_eager_subsume` satisfies `step13EagerSubsumeSpec` parametrically in `Γ` and `X`
(including the Step-13 `if (h->num_redundant > 0ULL) h->num_redundant -= 1ULL;` update). -/
theorem full_eager_subsume_step13_wp (Γ : Env) :
    ∀ args m Q X, step13EagerSubsumeSpec args m Q X →
      Func.wp Γ fidStep13S2EagerSubsumeFn.body args m Q X := by
  rintro ⟨h, new_ref, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hs, htmp_lt, href_in, hm, hQ⟩
  have hcl := hs.1.core_ok
  have hsl := hs.1.scratch_ok
  have hlm_clr := hs.2.2.1
  have hnd := hs.2.2.2.1
  have hext := hs.2.2.2.2.1
  have hdm := hs.2.2.2.2.2
  have hmv32 := fullInv_max_vars_lt32 c
  have hacap32 : c.arena_cap < 2 ^ 32 := Nat.lt_trans c.harena (by decide)
  have htlen_le : s.core.tmp_len ≤ c.max_vars := hcl.tmp_len_le
  have htlen32 : s.core.tmp_len < 2 ^ 32 := by omega
  have htl_lt64 : s.core.tmp_len < 2 ^ 64 := by omega
  dsimp only [Func.wp, fidStep13S2EagerSubsumeFn, full_eager_subsume_body]
  c0_clean; c0_to_group
  refine wp_loop_group (ts := [i64])
    (fun r (iv, ()) m1 => ∃ i lm1,
      i ≤ s.core.tmp_len ∧ r = s.core.tmp_len - i ∧ iv = BitVec.ofNat 64 i ∧
      lm1.length = 2 * c.max_vars ∧
      (∀ l < 2 * c.max_vars, lm1[l]?.getD 0#8 ≠ 0#8 →
        ∃ j < i, (s.core.tmp[j]?.getD 0#32).toNat = l) ∧
      (FullMem c (s13EsubState s lm1 s.core.arena s.core.arena_garbage s.core.num_redundant
        s.scratch.last_learned s.scratch.eager_sub_cnt) ⋆ R) m1) ?_ ?_
  · rintro L r ⟨iv, ⟨⟩⟩ m1 hL ⟨i, lm1, hi_le, rfl, rfl, hlm1_len, hlm1_cov, hm1⟩
    have hi_lt64 : i < 2 ^ 64 := by omega
    c0_clean; c0_split
    · let s1 := s13EsubState s lm1 s.core.arena s.core.arena_garbage s.core.num_redundant
        s.scratch.last_learned s.scratch.eager_sub_cnt
      change (FullMem c s1 ⋆ R) m1 at hm1
      have hi_lt : i < s.core.tmp_len := by
        rw [Nat.mod_eq_of_lt hi_lt64, Nat.mod_eq_of_lt htl_lt64] at hc; exact hc
      have hi_idx : (BitVec.ofNat 64 i).toNat = i := bv64_ofNat_toNat hi_lt64
      have hi_tmp : (BitVec.ofNat 64 i).toNat < s1.core.tmp.length := by
        rw [s13EsubState_tmp, hcl.tmp_len_arr, hi_idx]; omega
      have htmp_arr : s.core.tmp.length = c.max_vars := hcl.tmp_len_arr
      have heq_t : s1.core.tmp[(BitVec.ofNat 64 i).toNat]'hi_tmp =
          s.core.tmp[i]'(by rw [htmp_arr]; omega) := by
        dsimp only [s1, s13EsubState]; exact s13_getElem_congr_idx hi_idx
      have hl_idx_mod :
          ((s1.core.tmp[(BitVec.ofNat 64 i).toNat]'hi_tmp).setWidth 64).toNat <
            s1.core.lit_mark.length := by
        have hget := List.getElem?_eq_getElem (by rw [htmp_arr]; omega : i < s.core.tmp.length)
        have ht := htmp_lt i hi_lt
        rw [hget, Option.getD_some] at ht
        rw [bv32_setWidth64_toNat, s13EsubState_lm, hlm1_len, heq_t]; omega
      c0_steps
      refine wp_load_of (FullArenaTactics.c0_load_full_tmp hi_tmp hm1) ?_
      c0_steps
      have hlm_next :
          (lm1.set ((s1.core.tmp[(BitVec.ofNat 64 i).toNat]'hi_tmp).setWidth 64).toNat 1#8) =
          lm1.set (s.core.tmp[i]'(by rw [hcl.tmp_len_arr]; omega)).toNat 1#8 := by
        rw [bv32_setWidth64_toNat, heq_t]
      have hi1 : (BitVec.ofNat 64 i + 1#64).toNat = i + 1 := by
        rw [s13_bv64_add1_toNat (by rw [hi_idx]; omega), hi_idx]
      refine hL _ (BitVec.ofNat 64 i + 1#64, ()) _ (by omega)
        ⟨i + 1, lm1.set (s.core.tmp[i]'(by rw [hcl.tmp_len_arr]; omega)).toNat 1#8,
          by omega, rfl, BitVec.eq_of_toNat_eq (by rw [hi1, bv64_ofNat_toNat (by omega)]),
          by simp [hlm1_len], ?_, ?_⟩
      · intro l hl hnz
        have hget : (s.core.tmp[i]?.getD 0#32).toNat =
            (s.core.tmp[i]'(by rw [hcl.tmp_len_arr]; omega)).toNat := by
          rw [List.getElem?_eq_getElem (by rw [hcl.tmp_len_arr]; omega), Option.getD_some]
        rw [← hget] at hnz
        exact eagerSub_lm_step hlm1_cov l hl hnz
      · exact (congrArg (fun lm' => (FullMem c (s13EsubState s lm' s.core.arena
            s.core.arena_garbage s.core.num_redundant s.scratch.last_learned
            s.scratch.eager_sub_cnt) ⋆ R) m)
          hlm_next).mp hm
    · have hi_eq : i = s.core.tmp_len := by
        rw [Nat.mod_eq_of_lt hi_lt64, Nat.mod_eq_of_lt htl_lt64] at hc; omega
      subst hi_eq
      c0_clean; c0_to_group
      have hs1 : (s13EsubState s lm1 s.core.arena s.core.arena_garbage s.core.num_redundant
          s.scratch.last_learned s.scratch.eager_sub_cnt).LengthsOk c :=
        s13EsubState_lengths hs.1 hlm1_len hcl.arena_len_arr hsl.last_learned_len
      refine wp_loop_group (ts := [i64, .bool])
        (fun r2 (iv2, _subv, ()) m2 => ∃ i2 ar2 ag2 nr2 ll2 es2,
          let s2 := s13EsubState s lm1 ar2 ag2 nr2 ll2 es2
          i2 ≤ 4 ∧ r2 = 4 - i2 ∧ iv2 = BitVec.ofNat 64 i2 ∧
          s2.LengthsOk c ∧ FullWitnessInv c F0 F_cur s2.core ∧ FullArenaVarsNodup s2 ∧
          FullLastLearnedWf s2 ∧ fullArenaClauseRefs s2 = fullArenaClauseRefs s ∧
          (FullMem c s2 ⋆ R) m2) ?_ ?_
      · rintro L2 r2 ⟨iv2, subv, ⟨⟩⟩ m2 hL2 ⟨i2, ar2, ag2, nr2, ll2, es2, hi2_le, rfl, rfl,
          hs2, hw2, hnd2, hll2, hrefs2, hm2⟩
        clear hL hm1 hm
        let s2 := s13EsubState s lm1 ar2 ag2 nr2 ll2 es2
        have hi2_lt64 : i2 < 2 ^ 64 := by omega
        c0_clean; c0_split
        · have hi2_lt : i2 < 4 := by rw [Nat.mod_eq_of_lt hi2_lt64] at hc; exact hc
          have hi2_idx : (BitVec.ofNat 64 i2).toNat = i2 := bv64_ofNat_toNat hi2_lt64
          have hi2_ll : (BitVec.ofNat 64 i2).toNat < s2.scratch.last_learned.length := by
            rw [hi2_idx, hs2.2.last_learned_len]; omega
          c0_clean; c0_to_group
          refine wp_join_group (ts := [.bool])
            (fun (_sub', ()) m_next => ∃ ar' ag' nr' ll' es',
              let sn := s13EsubState s lm1 ar' ag' nr' ll' es'
              sn.LengthsOk c ∧ FullWitnessInv c F0 F_cur sn.core ∧ FullArenaVarsNodup sn ∧
              FullLastLearnedWf sn ∧ fullArenaClauseRefs sn = fullArenaClauseRefs s ∧
              (FullMem c sn ⋆ R) m_next) ?_ ?_
          · rintro _ ⟨sub', ⟨⟩⟩ m_next ⟨ar', ag', nr', ll', es', hsn, hwn, hndn, hlln,
              hrefsn, hmn⟩
            c0_steps
            have hi2_add : (BitVec.ofNat 64 i2 + 1#64).toNat = i2 + 1 := by
              rw [s13_bv64_add1_toNat (by rw [hi2_idx]; omega), hi2_idx]
            exact hL2 _ (BitVec.ofNat 64 i2 + 1#64, sub', ()) _ (by omega)
              ⟨i2 + 1, ar', ag', nr', ll', es', by omega, rfl,
                BitVec.eq_of_toNat_eq (by rw [hi2_add, bv64_ofNat_toNat (by omega)]),
                hsn, hwn, hndn, hlln, hrefsn, hmn⟩
          · intro Jnext hJnext
            let skip :=
              hJnext (subv, ()) m2 ⟨ar2, ag2, nr2, ll2, es2, hs2, hw2, hnd2, hll2, hrefs2, hm2⟩
            c0_clean; c0_split
            · have hi2_ll' : i2 < ll2.length := by
                have := hs2.2.last_learned_len
                rw [s13EsubState_ll] at this; omega
              have hcr_ne : ll2[i2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
                rw [List.getElem?_eq_getElem hi2_ll', Option.getD_some]
                have hmod : i2 % 2 ^ 64 = i2 := Nat.mod_eq_of_lt hi2_lt64
                have hc_ : ¬ ll2[i2 % 2 ^ 64]'(by rw [hmod]; exact hi2_ll') = 4294967295#32 := by
                  change ¬ (s13EsubState s lm1 ar2 ag2 nr2 ll2 es2).scratch.last_learned[
                    i2 % 2 ^ 64] = 4294967295
                  assumption
                intro h; exact hc_ (by rw [s13_getElem_congr_idx hmod]; exact h)
              have hcr_ref : (ll2[(BitVec.ofNat 64 i2).toNat]'hi2_ll).toNat ∈
                  fullArenaClauseRefs s2 := by
                have hcr_m := hll2 i2 (by omega)
                change ll2[i2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
                  (ll2[i2]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefs s2 at hcr_m
                have hcr_ne' := hcr_ne
                rw [List.getElem?_eq_getElem hi2_ll', Option.getD_some] at hcr_m hcr_ne'
                have hr := hcr_m.resolve_left hcr_ne'
                have helem : ll2[(BitVec.ofNat 64 i2).toNat]'hi2_ll = ll2[i2]'hi2_ll' :=
                  s13_getElem_congr_idx hi2_idx
                rw [helem]; exact hr
              c0_clean; c0_split
              · let cr := ll2[(BitVec.ofNat 64 i2).toNat]'hi2_ll
                have har2_len : ar2.length = c.arena_cap := hs2.1.arena_len_arr
                have hal_le : s.core.arena_len ≤ c.arena_cap := hs2.1.arena_len_le
                have hcr_wf := hw2.arena.refs_wf cr.toNat hcr_ref
                have hcr_bnd3 : cr.toNat + 3 ≤ s.core.arena_len := by
                  have h1 := hcr_wf.1; rw [s13EsubState_arena_len] at h1; exact h1
                have hcr_ar0 : (cr.setWidth 64).toNat < ar2.length := by
                  rw [bv32_setWidth64_toNat, har2_len]; omega
                have hcr_ar2 : (cr.setWidth 64 + 2#64).toNat < ar2.length := by
                  rw [s13_esub_arena_add2 cr, har2_len]; omega
                c0_clean; c0_split
                · have hcr_ar0' : cr.toNat < ar2.length := by
                    rw [← bv32_setWidth64_toNat cr]; exact hcr_ar0
                  have hcr_hdr0 : (ar2[cr.toNat]'hcr_ar0' &&& 0x00080000#32) = 0#32 := by
                    have hmod : i2 % 2 ^ 64 = i2 := Nat.mod_eq_of_lt hi2_lt64
                    have helem :
                        (ll2[i2 % 2 ^ 64]'(by rw [hmod]; exact hi2_ll')).toNat = cr.toNat :=
                      congrArg BitVec.toNat (s13_getElem_congr_idx (by rw [hmod, hi2_idx]))
                    have hc_and : ar2[(ll2[i2 % 2 ^ 64]'(by rw [hmod]; exact hi2_ll')).toNat]'(by
                        rw [helem]; exact hcr_ar0') &&& 0x00080000#32 = 0#32 := by
                      change (s13EsubState s lm1 ar2 ag2 nr2 ll2 es2).core.arena[(s13EsubState s
                        lm1 ar2 ag2 nr2 ll2 es2).scratch.last_learned[i2 % 2 ^ 64].toNat] &&&
                        524288 = 0
                      assumption
                    rw [s13_getElem_congr_idx helem.symm]; exact hc_and
                  have hcr_ng : fullArenaClauseGarb s2 cr.toNat = false := by
                    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
                    rw [s13EsubState_arena, List.getElem?_eq_getElem hcr_ar0', Option.getD_some]
                    change ((ar2[cr.toNat]'hcr_ar0' &&& 0x00080000#32) != 0#32) = false
                    rw [hcr_hdr0]; rfl
                  c0_clean; c0_split
                  · c0_clean; c0_split
                    · c0_clean; c0_split
                      · c0_clean; c0_to_group
                        have hcr_sz : (ar2[(cr.setWidth 64 + 2#64).toNat]'hcr_ar2).toNat =
                            fullArenaClauseSizeCore s2.core cr.toNat := by
                          unfold fullArenaClauseSizeCore
                          have h2 := s13_esub_arena_add2 cr
                          rw [s13EsubState_arena,
                            List.getElem?_eq_getElem (by rw [← h2]; exact hcr_ar2),
                            Option.getD_some, s13_getElem_congr_idx h2]
                        let csz := ar2[(cr.setWidth 64 + 2#64).toNat]'hcr_ar2
                        have hcsz_bnd : cr.toNat + 3 + csz.toNat ≤ s.core.arena_len := by
                          have h1 : cr.toNat + 3 + csz.toNat ≤
                              fullArenaNextOff ar2 s.core.arena_len cr.toNat := by
                            rw [hcr_sz]; exact hcr_wf.2.2.1
                          have h2 : fullArenaNextOff ar2 s.core.arena_len cr.toNat ≤
                              s.core.arena_len := hcr_wf.2.2.2.1
                          omega
                        refine wp_join_group (ts := [i64, i64, i32])
                          (fun (need_v, _, _, ()) ma => m2 = ma) ?_ ?_
                        · rintro _ ⟨need_v, _, _, ⟨⟩⟩ ma rfl
                          c0_clean; c0_split
                          · clear hL2
                            c0_clean; c0_to_group
                            refine wp_join_group (ts := [.bool, i32])
                              (fun (act_v, _, ()) mb => m2 = mb ∧
                                (act_v = false → ∀ k < csz.toNat,
                                  let rl := s2.core.arena[cr.toNat + 3 + k]?.getD 0#32
                                  ¬ (rl.toNat < 2 * s2.core.cur_vars ∧
                                    BitVec.slt 0#32 (BitVec.signExtend 32
                                      (s2.core.vals[rl.toNat]?.getD 0#8)) = true ∧
                                    0 < (s2.core.lvl[rl.toNat / 2]?.getD 0#32).toNat ∧
                                    s2.core.rsns[rl.toNat / 2]?.getD 0xFFFFFFFF#32 = cr))) ?_ ?_
                            · rintro _ ⟨act_v, _, ⟨⟩⟩ mb ⟨rfl, hact_res⟩
                              c0_clean; c0_split
                              · c0_steps; exact skip
                              · have hact_f : act_v = false := by cases act_v <;> simp_all
                                have hnonact := s13_esub_nonact_of_scan hw2 hcr_sz (hact_res hact_f)
                                have hcr_len0 : (cr.setWidth 64).toNat < s2.core.arena.length := by
                                  rw [s13EsubState_arena]; exact hcr_ar0
                                have hcr_len2 : (cr.setWidth 64 + 2#64).toNat <
                                    s2.core.arena.length := by
                                  rw [s13EsubState_arena]; exact hcr_ar2
                                c0_steps
                                refine wp_store_sep (FullArenaTactics.c0_store_full_arena
                                  (ar2[(cr.setWidth 64).toNat]'hcr_ar0 ||| 0x00080000#32)
                                  hcr_len0 hm2) fun m hm => ?_
                                c0_clean; c0_to_group
                                let ag' := (ag2 + 3#64) + csz.setWidth 64
                                let ar' :=
                                  ar2.set cr.toNat (fullArenaHdr s2 cr.toNat ||| 0x00080000#32)
                                have hcr_def : ll2[i2]'hi2_ll' = cr :=
                                  (s13_getElem_congr_idx hi2_idx).symm
                                have hhdr_rw : ar2[(cr.setWidth 64).toNat]'hcr_ar0 =
                                    ar2[cr.toNat]'hcr_ar0' :=
                                  s13_getElem_congr_idx (bv32_setWidth64_toNat cr)
                                have har2_get :
                                    ar2[cr.toNat]?.getD 0#32 = ar2[cr.toNat]'hcr_ar0' := by
                                  rw [List.getElem?_eq_getElem hcr_ar0', Option.getD_some]
                                refine wp_join_group (ts := []) (fun () mn => ∃ nr' : BitVec 64,
                                  (FullMem c (s13EsubState s lm1 ar' ag' nr' ll2 es2) ⋆ R) mn)
                                  ?_ ?_
                                · rintro _ ⟨⟩ mn ⟨nr', hmn⟩
                                  have hlen_ll_n : (BitVec.ofNat 64 i2).toNat <
                                      (s13EsubState s lm1 ar' ag' nr' ll2
                                        es2).scratch.last_learned.length := by
                                    rw [s13EsubState_ll, hi2_idx]; exact hi2_ll'
                                  c0_steps
                                  refine wp_store_sep
                                    (FullArenaTactics.c0_store_full_last_learned 0xFFFFFFFF#32
                                      hlen_ll_n hmn) fun _mn1 _hmn1 => ?_
                                  c0_steps
                                  let ll' := ll2.set i2 0xFFFFFFFF#32
                                  let es' := es2 + 1#64
                                  let s' := s13EsubState s lm1 ar' ag' nr' ll' es'
                                  obtain ⟨hs', hw', hnd_s', hll', hrefs'⟩ :=
                                    s13_esub_mark_garb_inv (ag' := ag') (nr' := nr') (es' := es')
                                      hs.1 hlm1_len hs2 hw2 hnd2 hll2 hrefs2 hcr_ref hnonact
                                  refine hJnext (true, ()) _
                                    ⟨ar', ag', nr', ll', es', hs', hw', hnd_s', hll', hrefs', ?_⟩
                                  · simpa only [s13EsubState, s2, s', ll', es', hi2_idx,
                                      show (1 : BitVec 64) = 1#64 from rfl] using hm
                                · intro Jnr hJnr; c0_split
                                  · c0_steps
                                    refine hJnr () _ ⟨nr2 - 1#64, ?_⟩
                                    simpa only [s13EsubState, s2, ar', ag', fullArenaHdr,
                                      fullArenaHdrCore, har2_get, hhdr_rw, bv32_setWidth64_toNat cr,
                                      csz] using by assumption
                                  · c0_steps
                                    refine hJnr () _ ⟨nr2, ?_⟩
                                    simpa only [s13EsubState, s2, ar', ag', fullArenaHdr,
                                      fullArenaHdrCore, har2_get, hhdr_rw, bv32_setWidth64_toNat cr,
                                      csz] using by assumption
                            · intro Jb hJb
                              exact s13_esub_loop2b_wp rfl hi2_idx hi2_lt hi2_ll'
                                (s13_getElem_congr_idx hi2_idx).symm hs2 hcr_sz hcsz_bnd hal_le
                                hm2 Jb fun act_v rj_v mb hm_eq hact =>
                                  hJb (act_v, rj_v, ()) mb ⟨hm_eq, hact⟩
                          · c0_steps; exact skip
                        · intro Ja hJa; c0_clean; c0_to_group
                          have hcsz_bnd2 : cr.toNat + 3 + csz.toNat ≤ s2.core.arena.length := by
                            dsimp only [s2]; rw [s13EsubState_arena, har2_len]; omega
                          exact s13_esub_loop2a_wp hs2 hw2 rfl hlm1_len hcr_ref hcr_ng hcr_sz
                            hcsz_bnd2 hm2 Ja
                            (fun nv rv jv ma hm_eq => hJa (nv, rv, jv, ()) ma hm_eq)
                      · c0_steps; exact skip
                    · c0_steps; exact skip
                  · c0_steps; exact skip
                · c0_steps; exact skip
              · c0_steps; exact skip
            · c0_steps; exact skip
        · clear hL2 hnd hs1 hi2_le hi2_lt64
          c0_clean; c0_to_group
          refine wp_loop_group (ts := [i64])
            (fun r3 (iv3, ()) m3 => ∃ i3 lm3,
              let s3 := s13EsubState s lm3 ar2 ag2 nr2 ll2 es2
              i3 ≤ s.core.tmp_len ∧ r3 = s.core.tmp_len - i3 ∧ iv3 = BitVec.ofNat 64 i3 ∧
              lm3.length = 2 * c.max_vars ∧
              (∀ l < 2 * c.max_vars, lm3[l]?.getD 0#8 ≠ 0#8 →
                (∃ j < s.core.tmp_len, (s.core.tmp[j]?.getD 0#32).toNat = l) ∧
                (∀ j < i3, (s.core.tmp[j]?.getD 0#32).toNat ≠ l)) ∧
              (FullMem c s3 ⋆ R) m3) ?_ ?_
          · rintro L3 r3 ⟨iv3, ⟨⟩⟩ m3 hL3 ⟨i3, lm3, hi3_le, rfl, rfl, hlm3_len, hlm3_cov, hm3⟩
            have hi3_lt64 : i3 < 2 ^ 64 := by omega
            c0_clean; c0_split
            · let s3_cur := s13EsubState s lm3 ar2 ag2 nr2 ll2 es2
              change (FullMem c s3_cur ⋆ R) m3 at hm3
              have hi3_lt : i3 < s.core.tmp_len := by
                rw [Nat.mod_eq_of_lt hi3_lt64, Nat.mod_eq_of_lt htl_lt64] at hc; exact hc
              have hi3_idx : (BitVec.ofNat 64 i3).toNat = i3 := bv64_ofNat_toNat hi3_lt64
              have hi3_tmp : (BitVec.ofNat 64 i3).toNat < s3_cur.core.tmp.length := by
                rw [s13EsubState_tmp, hcl.tmp_len_arr, hi3_idx]; omega
              have htmp_arr : s.core.tmp.length = c.max_vars := hcl.tmp_len_arr
              have heq_t : s3_cur.core.tmp[(BitVec.ofNat 64 i3).toNat]'hi3_tmp =
                  s.core.tmp[i3]'(by rw [htmp_arr]; omega) := by
                dsimp only [s3_cur, s13EsubState]; exact s13_getElem_congr_idx hi3_idx
              have hl3_idx_lm :
                  ((s3_cur.core.tmp[(BitVec.ofNat 64 i3).toNat]'hi3_tmp).setWidth 64).toNat <
                    s3_cur.core.lit_mark.length := by
                have hget := List.getElem?_eq_getElem
                  (by rw [htmp_arr]; omega : i3 < s.core.tmp.length)
                have ht := htmp_lt i3 hi3_lt
                rw [hget, Option.getD_some] at ht
                rw [bv32_setWidth64_toNat, s13EsubState_lm, hlm3_len, heq_t]; omega
              c0_steps
              refine wp_load_of (FullArenaTactics.c0_load_full_tmp hi3_tmp hm3) ?_
              c0_steps
              have hlm3_next :
                  lm3.set ((s3_cur.core.tmp[(BitVec.ofNat 64 i3).toNat]'hi3_tmp).setWidth
                    64).toNat 0#8 =
                  lm3.set (s.core.tmp[i3]'(by rw [hcl.tmp_len_arr]; omega)).toNat 0#8 := by
                rw [bv32_setWidth64_toNat, heq_t]
              have hi3_add : (BitVec.ofNat 64 i3 + 1#64).toNat = i3 + 1 := by
                rw [s13_bv64_add1_toNat (by rw [hi3_idx]; omega), hi3_idx]
              refine hL3 _ (BitVec.ofNat 64 i3 + 1#64, ()) _ (by omega)
                ⟨i3 + 1, lm3.set (s.core.tmp[i3]'(by rw [hcl.tmp_len_arr]; omega)).toNat 0#8,
                  by omega, rfl,
                  BitVec.eq_of_toNat_eq (by rw [hi3_add, bv64_ofNat_toNat (by omega)]),
                  by simp [hlm3_len], ?_, ?_⟩
              · intro l hl hnz
                have hget : (s.core.tmp[i3]?.getD 0#32).toNat =
                    (s.core.tmp[i3]'(by rw [hcl.tmp_len_arr]; omega)).toNat := by
                  rw [List.getElem?_eq_getElem (by rw [hcl.tmp_len_arr]; omega), Option.getD_some]
                have hlt' : (s.core.tmp[i3]?.getD 0#32).toNat < 2 * c.max_vars := htmp_lt i3 hi3_lt
                rw [← hget] at hnz
                exact eagerSub_lm_clear_step hlm3_len hlt' hlm3_cov l hl hnz
              · exact (congrArg (fun lm' => (FullMem c (s13EsubState s lm' ar2 ag2 nr2 ll2 es2) ⋆
                    R) m) hlm3_next).mp hm
            · have hi3_eq : i3 = s.core.tmp_len := by
                rw [Nat.mod_eq_of_lt hi3_lt64, Nat.mod_eq_of_lt htl_lt64] at hc; omega
              subst hi3_eq
              let s3 := s13EsubState s lm3 ar2 ag2 nr2 ll2 es2
              have hs3_len : s3.LengthsOk c :=
                s13EsubState_lengths hs.1 hlm3_len hs2.1.arena_len_arr hs2.2.last_learned_len
              have hw3 : FullWitnessInv c F0 F_cur s3.core := s13_fullWitness_with_litMark hw2 lm3
              have hclr3 : FullLitMarksClear c s3 := by
                refine ⟨hlm_clr.1, fun l hl => Classical.byContradiction fun hnz => ?_⟩
                obtain ⟨⟨j, hj, hje⟩, hprev⟩ := hlm3_cov l hl hnz
                exact hprev j hj hje
              have hlm3_eq : lm3 = s.core.lit_mark :=
                s13_list_bv8_eq_of_getD0 hlm3_len hcl.lit_mark_len hclr3.2 hlm_clr.2
              clear hL3 htmp_lt hlm_clr hlm3_cov hm2 hi3_le hi3_lt64 htl_lt64 htlen32 htlen_le
                hmv32 hacap32
              c0_clean; c0_to_group
              refine wp_join_group (ts := [])
                (fun () m_c => ∃ ll_c : List (BitVec 32),
                  ll_c.length = 16 ∧ FullLastLearnedIn (fullArenaClauseRefs s3) ll_c ∧
                  (FullMem c (s13EsubState s lm3 ar2 ag2 nr2 ll_c es2) ⋆ R) m_c) ?_ ?_
              · rintro _ ⟨⟩ m_c ⟨ll_c, hllc_len, hllc_in, hm_c⟩
                let sc_fin : FullState :=
                  { s with
                    core := { s.core with arena := ar2, arena_garbage := ag2,
                                          num_redundant := nr2 }
                    scratch := { s.scratch with last_learned := ll_c, eager_sub_cnt := es2 } }
                have hs3_core_eq : s3.core = sc_fin.core := by
                  dsimp only [s3, sc_fin, s13EsubState]; rw [hlm3_eq]
                have hsc_len : sc_fin.LengthsOk c :=
                  ⟨hs3_core_eq ▸ hs3_len.core_ok,
                   { hs3_len.scratch_ok with last_learned_len := hllc_len }⟩
                have hwc : FullWitnessInv c F0 F_cur sc_fin.core := hs3_core_eq ▸ hw3
                have hclrc : FullLitMarksClear c sc_fin := by
                  unfold FullLitMarksClear FullMrkZero; rw [← hs3_core_eq]; exact hclr3
                have hndc : FullArenaVarsNodup sc_fin :=
                  (s13_arenaVarsNodup_congr rfl rfl).mp hnd2
                exact s13_esub_loop4_wp hs.1 hlm3_eq hllc_len hsc_len hwc hclrc hndc hllc_in hext.2
                  hdm rfl href_in hrefs2 hm_c hQ
              · intro Jcomp hJcomp
                exact s13_esub_compact_wp (lm3 := lm3) hs2.2.last_learned_len hll2 hm3 Jcomp
                  (fun ll_c hllc_len hllc_in m_c hm_c => hJcomp () m_c
                    ⟨ll_c, hllc_len, hllc_in, hm_c⟩)
          · intro J3 hJ3; c0_steps
            exact hJ3 s.core.tmp_len (0#64, ()) m2 ⟨0, lm1, Nat.zero_le _, rfl, rfl, hlm1_len,
              fun l hl hnz => ⟨hlm1_cov l hl hnz, fun j hj => by omega⟩, hm2⟩
      · intro J2 hJ2; c0_steps
        exact hJ2 4 (0#64, false, ()) m1 ⟨0, s.core.arena, s.core.arena_garbage,
          s.core.num_redundant, s.scratch.last_learned, s.scratch.eager_sub_cnt, Nat.zero_le 4,
          rfl, rfl, hs1, s13_fullWitness_with_litMark hs.2.1 lm1, hnd, hext.1, rfl, hm1⟩
  · intro J hJ; c0_steps
    exact hJ s.core.tmp_len (0#64, ()) m ⟨0, s.core.lit_mark, Nat.zero_le _, rfl, rfl,
      hcl.lit_mark_len, fun l hl hnz => absurd (hlm_clr.2 l hl) hnz, hm⟩

end EagerSubsumeProof

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S2

end
