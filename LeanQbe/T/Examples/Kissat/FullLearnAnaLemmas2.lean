module

public import LeanQbe.T.Examples.Kissat.FullLearnAnaLemmas1

/-!
# Kissat `D-Full` Eager Subsume `Func.wp` Proof (`Stage 4`, Part 2)

Proves the `Func.wp` specification for `full_eager_subsume` in `LeanQbe.T.Examples.Kissat.Full2`,
parameterized over arbitrary `Γ : Env`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test
open FullLearnAnaSpecs FullLearnAnaTactics FullLearnAnaHelpers

open scoped FullArenaTactics FullLearnAnaTactics

section LocalTactics

attribute [local bv_c0] Bool.true_eq_false Bool.false_eq_true
@[local bv_c0] private theorem i8_sext32_zero : (0#8 : BitVec 8).signExtend 32 = 0#32 := rfl
@[local bv_c0] private theorem u8_zext32_zero : (0#8 : BitVec 8).setWidth 32 = 0#32 := rfl
@[local bv_c0] private theorem i8_sext32_eq0_prop (v : BitVec 8) :
    (v.signExtend 32 = 0#32) = (v = 0#8) := propext (i8_sext32_eq0 v)

@[local bv_c0] private theorem bv32_lshr_1' (x : BitVec 32) : (x >>> 1#32).toNat = x.toNat / 2 :=
  bv32_lshr_1 x

private theorem bv32_add1_toNat {x : BitVec 32} (h : x.toNat + 1 < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

private theorem bv64_add1_toNat {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

private theorem bv64_sub1_toNat' {x : BitVec 64} (h : 0 < x.toNat) :
    (x - 1#64).toNat = x.toNat - 1 := by
  have hx := x.isLt; bv_omega

private theorem eagerSub_arena_add2 (cr : BitVec 32) :
    (cr.setWidth 64 + 2#64).toNat = cr.toNat + 2 := by
  have := cr.isLt; bv_omega

private theorem eagerSub_arena_add3 (cr rj : BitVec 32) :
    (cr.setWidth 64 + 3#64 + rj.setWidth 64).toNat = cr.toNat + 3 + rj.toNat := by
  have := cr.isLt; have := rj.isLt; bv_omega

private def eagerSubState (s : FullState) (lm : List (BitVec 8)) (ar : List (BitVec 32))
    (ag : BitVec 64) (ll : List (BitVec 32)) (es : BitVec 64) : FullState :=
  { s with
    core := { s.core with lit_mark := lm, arena := ar, arena_garbage := ag }
    scratch := { s.scratch with last_learned := ll, eager_sub_cnt := es } }

@[local bv_c0] private theorem eagerSubState_tmp (s : FullState) lm ar ag ll es :
    (eagerSubState s lm ar ag ll es).core.tmp = s.core.tmp := rfl
@[local bv_c0] private theorem eagerSubState_tmp_len (s : FullState) lm ar ag ll es :
    (eagerSubState s lm ar ag ll es).core.tmp_len = s.core.tmp_len := rfl
@[local bv_c0] private theorem eagerSubState_cur_vars (s : FullState) lm ar ag ll es :
    (eagerSubState s lm ar ag ll es).core.cur_vars = s.core.cur_vars := rfl
@[local bv_c0] private theorem eagerSubState_arena_len (s : FullState) lm ar ag ll es :
    (eagerSubState s lm ar ag ll es).core.arena_len = s.core.arena_len := rfl
@[local bv_c0] private theorem eagerSubState_trail_end (s : FullState) lm ar ag ll es :
    (eagerSubState s lm ar ag ll es).core.trail_end = s.core.trail_end := rfl
@[local bv_c0] private theorem eagerSubState_lm (s : FullState) lm ar ag ll es :
    (eagerSubState s lm ar ag ll es).core.lit_mark = lm := rfl
@[local bv_c0] private theorem eagerSubState_arena (s : FullState) lm ar ag ll es :
    (eagerSubState s lm ar ag ll es).core.arena = ar := rfl
@[local bv_c0] private theorem eagerSubState_vals (s : FullState) lm ar ag ll es :
    (eagerSubState s lm ar ag ll es).core.vals = s.core.vals := rfl
@[local bv_c0] private theorem eagerSubState_lvl (s : FullState) lm ar ag ll es :
    (eagerSubState s lm ar ag ll es).core.lvl = s.core.lvl := rfl
@[local bv_c0] private theorem eagerSubState_rsns (s : FullState) lm ar ag ll es :
    (eagerSubState s lm ar ag ll es).core.rsns = s.core.rsns := rfl
@[local bv_c0] private theorem eagerSubState_ll (s : FullState) lm ar ag ll es :
    (eagerSubState s lm ar ag ll es).scratch.last_learned = ll := rfl

private theorem eagerSubState_set_lm (s : FullState) lm lm' ar ag ll es :
    { eagerSubState s lm ar ag ll es with
      core := { (eagerSubState s lm ar ag ll es).core with lit_mark := lm' } } =
      eagerSubState s lm' ar ag ll es := rfl

private theorem eagerSubState_set_ll (s : FullState) lm ar ag ll ll' es :
    { eagerSubState s lm ar ag ll es with
      scratch := { (eagerSubState s lm ar ag ll es).scratch with last_learned := ll' } } =
      eagerSubState s lm ar ag ll' es := rfl

private theorem list_bv8_eq_of_getD0 {xs ys : List (BitVec 8)} {n : Nat}
    (hx : xs.length = n) (hy : ys.length = n)
    (hxs : ∀ i < n, xs[i]?.getD 0#8 = 0#8) (hys : ∀ i < n, ys[i]?.getD 0#8 = 0#8) :
    xs = ys := by
  apply List.ext_getElem (hx.trans hy.symm)
  intro i hix hiy
  have hx0 := hxs i (hx ▸ hix)
  have hy0 := hys i (hy ▸ hiy)
  rw [List.getElem?_eq_getElem hix, Option.getD_some] at hx0
  rw [List.getElem?_eq_getElem hiy, Option.getD_some] at hy0
  exact hx0.trans hy0.symm

private theorem eagerSubState_lengths {c : FullCfg} {s : FullState}
    (hs : s.LengthsOk c) {lm : List (BitVec 8)} {ar ll : List (BitVec 32)}
    {ag es : BitVec 64} (hlm : lm.length = 2 * c.max_vars)
    (har : ar.length = c.arena_cap) (hll : ll.length = 16) :
    (eagerSubState s lm ar ag ll es).LengthsOk c :=
  ⟨{ hs.core_ok with lit_mark_len := hlm, arena_len_arr := har },
   { hs.scratch_ok with last_learned_len := hll }⟩

private theorem fullArenaClauseRefs_congr {s1 s2 : FullState}
    (ha : s1.core.arena = s2.core.arena) (hl : s1.core.arena_len = s2.core.arena_len) :
    fullArenaClauseRefs s1 = fullArenaClauseRefs s2 := by
  unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [ha, hl]

private theorem fullArenaVarsNodup_congr {s1 s2 : FullState}
    (ha : s1.core.arena = s2.core.arena) (hl : s1.core.arena_len = s2.core.arena_len) :
    FullArenaVarsNodup s1 ↔ FullArenaVarsNodup s2 := by
  unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseRefsCore fullArenaClauseGarb
    fullArenaClauseGarbCore fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore
    fullArenaHdrCore
  rw [ha, hl]

private theorem fullWitness_with_litMark {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (lm : List (BitVec 8)) :
    FullWitnessInv c F0 F_cur { k with lit_mark := lm } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }

private theorem getElem_congr_idx {α : Type} {xs : List α} {i j : Nat}
    (h : i = j) {hi : i < xs.length} {hj : j < xs.length} :
    xs[i]'hi = xs[j]'hj := by
  subst h; rfl

private theorem mem_fullArenaClauseLitsCore {k : FullCoreState} {r j : Nat}
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

private theorem fullArenaClauseLitsCore_mem_iff {k : FullCoreState} {r l : Nat} :
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

end LocalTactics

/-! ## 1. `full_eager_subsume` -/

private theorem eagerSub_loop2a_wp {Γ X} {Q : Post []} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s2 : FullState} {R : Mem 64 → Prop} {m2 : Mem 64}
    {cr csz : BitVec 32} {lm1 : List (BitVec 8)}
    (hs2 : s2.LengthsOk c) (hw2 : FullWitnessInv c F0 F_cur s2.core)
    (hs2_lm : s2.core.lit_mark = lm1)
    (hlm1_len : lm1.length = 2 * c.max_vars)
    (hcr_ref : cr.toNat ∈ fullArenaClauseRefs s2) (hcr_ng : fullArenaClauseGarb s2 cr.toNat = false)
    (hcr_sz : csz.toNat = fullArenaClauseSizeCore s2.core cr.toNat)
    (hcsz_bnd : cr.toNat + 3 + csz.toNat ≤ s2.core.arena.length)
    (hm2 : (FullMem c s2 ⋆ R) m2)
    (Ja : Cont [i64, i64, i32])
    (hJa : ∀ nv rv jv m, m2 = m → Ja (nv, rv, jv, ()) m) :
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
      have hidx_eq := eagerSub_arena_add3 cr jv
      have hj_ar : (cr.setWidth 64 + 3#64 + jv.setWidth 64).toNat < s2.core.arena.length := by
        rw [hidx_eq]; omega
      let lit := s2.core.arena[(cr.setWidth 64 + 3#64 + jv.setWidth 64).toNat]'hj_ar
      have hlit_mem : lit.toNat ∈ fullArenaClauseLits s2 cr.toNat := by
        have hb : cr.toNat + 3 + jv.toNat < s2.core.arena.length := by omega
        have hm := mem_fullArenaClauseLitsCore (k := s2.core) (r := cr.toNat) (j := jv.toNat)
          (by rw [← hcr_sz]; exact hj_lt) hb
        have heq : (s2.core.arena[cr.toNat + 3 + jv.toNat]?.getD 0#32).toNat = lit.toNat := by
          rw [List.getElem?_eq_getElem hb, Option.getD_some]
          exact congrArg BitVec.toNat
            (show s2.core.arena[cr.toNat + 3 + jv.toNat]'hb = lit from
              getElem_congr_idx hidx_eq.symm)
        rwa [heq] at hm
      have hlit_lt : (lit.setWidth 64).toNat < s2.core.lit_mark.length := by
        rw [bv32_setWidth64_toNat, hs2_lm, hlm1_len]
        have := hw2.arena.lits_lt cr.toNat hcr_ref hcr_ng lit.toNat hlit_mem
        have := hs2.1.cur_vars_le; omega
      have hj1 : (jv + 1#32).toNat = jv.toNat + 1 :=
        bv32_add1_toNat (by have := csz.isLt; omega)
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

theorem full_eager_subsume_wp (Γ : Env) :
    ∀ args m Q X, fullEagerSubsumeSpec args m Q X →
      Func.wp Γ full_eager_subsume_body args m Q X := by
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
  unfold Func.wp full_eager_subsume_body
  c0_clean; c0_to_group
  -- Loop 1 (`while (i < tlen) { lm[tmp[i]] = 1; i++; }`)
  refine wp_loop_group (ts := [i64])
    (fun r (iv, ()) m1 => ∃ i lm1,
      i ≤ s.core.tmp_len ∧ r = s.core.tmp_len - i ∧ iv = BitVec.ofNat 64 i ∧
      lm1.length = 2 * c.max_vars ∧
      (∀ l < 2 * c.max_vars, lm1[l]?.getD 0#8 ≠ 0#8 →
        ∃ j < i, (s.core.tmp[j]?.getD 0#32).toNat = l) ∧
      (FullMem c (eagerSubState s lm1 s.core.arena s.core.arena_garbage
        s.scratch.last_learned s.scratch.eager_sub_cnt) ⋆ R) m1) ?_ ?_
  · rintro L r ⟨iv, ⟨⟩⟩ m1 hL ⟨i, lm1, hi_le, rfl, rfl, hlm1_len, hlm1_cov, hm1⟩
    have hi_lt64 : i < 2 ^ 64 := by omega
    c0_clean; c0_split
    · -- Loop 1 body (`i < tlen`)
      let s1 := eagerSubState s lm1 s.core.arena s.core.arena_garbage
        s.scratch.last_learned s.scratch.eager_sub_cnt
      change (FullMem c s1 ⋆ R) m1 at hm1
      have hi_lt : i < s.core.tmp_len := by
        rw [Nat.mod_eq_of_lt hi_lt64, Nat.mod_eq_of_lt htl_lt64] at hc; exact hc
      have hi_idx : (BitVec.ofNat 64 i).toNat = i := bv64_ofNat_toNat hi_lt64
      have hi_tmp : (BitVec.ofNat 64 i).toNat < s1.core.tmp.length := by
        rw [eagerSubState_tmp, hcl.tmp_len_arr, hi_idx]; omega
      have htmp_arr : s.core.tmp.length = c.max_vars := hcl.tmp_len_arr
      have heq_t : s1.core.tmp[(BitVec.ofNat 64 i).toNat]'hi_tmp =
          s.core.tmp[i]'(by rw [htmp_arr]; omega) := by
        dsimp only [s1, eagerSubState]; exact getElem_congr_idx hi_idx
      have hl_idx_mod :
          ((s1.core.tmp[(BitVec.ofNat 64 i).toNat]'hi_tmp).setWidth 64).toNat <
            s1.core.lit_mark.length := by
        have hget := List.getElem?_eq_getElem (by rw [htmp_arr]; omega : i < s.core.tmp.length)
        have ht := htmp_lt i hi_lt
        rw [hget, Option.getD_some] at ht
        rw [bv32_setWidth64_toNat, eagerSubState_lm, hlm1_len, heq_t]; omega
      c0_steps
      refine wp_load_of (FullArenaTactics.c0_load_full_tmp hi_tmp hm1) ?_
      c0_steps
      have hlm_next :
          (lm1.set ((s1.core.tmp[(BitVec.ofNat 64 i).toNat]'hi_tmp).setWidth 64).toNat 1#8) =
          lm1.set (s.core.tmp[i]'(by rw [hcl.tmp_len_arr]; omega)).toNat 1#8 := by
        rw [bv32_setWidth64_toNat, heq_t]
      have hi1 : (BitVec.ofNat 64 i + 1#64).toNat = i + 1 := by
        rw [bv64_add1_toNat (by rw [hi_idx]; omega), hi_idx]
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
      · exact (congrArg (fun lm' => (FullMem c (eagerSubState s lm' s.core.arena
            s.core.arena_garbage s.scratch.last_learned s.scratch.eager_sub_cnt) ⋆ R) m)
          hlm_next).mp hm
    · -- Exit Loop 1 (`i = tlen`) -> Loop 2 (`i = 0..<8`)
      have hi_eq : i = s.core.tmp_len := by
        rw [Nat.mod_eq_of_lt hi_lt64, Nat.mod_eq_of_lt htl_lt64] at hc; omega
      subst hi_eq
      c0_clean; c0_to_group
      have hs1 : (eagerSubState s lm1 s.core.arena s.core.arena_garbage
          s.scratch.last_learned s.scratch.eager_sub_cnt).LengthsOk c :=
        eagerSubState_lengths hs.1 hlm1_len hcl.arena_len_arr hsl.last_learned_len
      -- Loop 2 (`while (i < 8ULL)`)
      refine wp_loop_group (ts := [i64])
        (fun r2 (iv2, ()) m2 => ∃ i2 ar2 ag2 ll2 es2,
          let s2 := eagerSubState s lm1 ar2 ag2 ll2 es2
          i2 ≤ 8 ∧ r2 = 8 - i2 ∧ iv2 = BitVec.ofNat 64 i2 ∧
          s2.LengthsOk c ∧ FullWitnessInv c F0 F_cur s2.core ∧ FullArenaVarsNodup s2 ∧
          FullLastLearnedWf s2 ∧ fullArenaClauseRefs s2 = fullArenaClauseRefs s ∧
          (FullMem c s2 ⋆ R) m2) ?_ ?_
      · rintro L2 r2 ⟨iv2, ⟨⟩⟩ m2 hL2 ⟨i2, ar2, ag2, ll2, es2, hi2_le, rfl, rfl,
          hs2, hw2, hnd2, hll2, hrefs2, hm2⟩
        clear hL hm1 hm
        let s2 := eagerSubState s lm1 ar2 ag2 ll2 es2
        have hi2_lt64 : i2 < 2 ^ 64 := by omega
        c0_clean; c0_split
        · -- Loop 2 body (`i2 < 8`)
          have hi2_lt : i2 < 8 := by rw [Nat.mod_eq_of_lt hi2_lt64] at hc; exact hc
          have hi2_idx : (BitVec.ofNat 64 i2).toNat = i2 := bv64_ofNat_toNat hi2_lt64
          have hi2_ll : (BitVec.ofNat 64 i2).toNat < s2.scratch.last_learned.length := by
            rw [hi2_idx, hs2.2.last_learned_len]; omega
          c0_clean; c0_to_group
          -- Join point at end of Loop 2 body (`i2 = i2 + 1`)
          refine wp_join_group (ts := [])
            (fun () m_next => ∃ ar' ag' ll' es',
              let sn := eagerSubState s lm1 ar' ag' ll' es'
              sn.LengthsOk c ∧ FullWitnessInv c F0 F_cur sn.core ∧ FullArenaVarsNodup sn ∧
              FullLastLearnedWf sn ∧ fullArenaClauseRefs sn = fullArenaClauseRefs s ∧
              (FullMem c sn ⋆ R) m_next) ?_ ?_
          · rintro _ ⟨⟩ m_next ⟨ar', ag', ll', es', hsn, hwn, hndn, hlln, hrefsn, hmn⟩
            c0_steps
            have hi2_add : (BitVec.ofNat 64 i2 + 1#64).toNat = i2 + 1 := by
              rw [bv64_add1_toNat (by rw [hi2_idx]; omega), hi2_idx]
            exact hL2 _ (BitVec.ofNat 64 i2 + 1#64, ()) _ (by omega)
              ⟨i2 + 1, ar', ag', ll', es', by omega, rfl,
                BitVec.eq_of_toNat_eq (by rw [hi2_add, bv64_ofNat_toNat (by omega)]),
                hsn, hwn, hndn, hlln, hrefsn, hmn⟩
          · intro Jnext hJnext
            let skip := hJnext () m2 ⟨ar2, ag2, ll2, es2, hs2, hw2, hnd2, hll2, hrefs2, hm2⟩
            c0_clean; c0_split
            · -- `cr != 0xFFFFFFFF`
              have hi2_ll' : i2 < ll2.length := by
                have := hs2.2.last_learned_len
                rw [eagerSubState_ll] at this; omega
              have hcr_ne : ll2[i2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
                rw [List.getElem?_eq_getElem hi2_ll', Option.getD_some]
                have hmod : i2 % 2 ^ 64 = i2 := Nat.mod_eq_of_lt hi2_lt64
                have hc_ : ¬ ll2[i2 % 2 ^ 64]'(by rw [hmod]; exact hi2_ll') =
                    4294967295#32 := by
                  change ¬ (eagerSubState s lm1 ar2 ag2 ll2 es2).scratch.last_learned[i2 % 2 ^ 64] =
                    4294967295
                  assumption
                intro h; exact hc_ (by rw [getElem_congr_idx hmod]; exact h)
              have hcr_ref : (ll2[(BitVec.ofNat 64 i2).toNat]'hi2_ll).toNat ∈
                  fullArenaClauseRefs s2 := by
                have hcr_m := hll2 i2 hi2_lt
                change ll2[i2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
                  (ll2[i2]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefs s2 at hcr_m
                have hcr_ne' := hcr_ne
                rw [List.getElem?_eq_getElem hi2_ll', Option.getD_some] at hcr_m hcr_ne'
                have hr := hcr_m.resolve_left hcr_ne'
                have helem : ll2[(BitVec.ofNat 64 i2).toNat]'hi2_ll = ll2[i2]'hi2_ll' :=
                  getElem_congr_idx hi2_idx
                rw [helem]; exact hr
              c0_clean; c0_split
              · -- `(u64)cr + 3ULL ≤ arena_len`
                let cr := ll2[(BitVec.ofNat 64 i2).toNat]'hi2_ll
                have har2_len : ar2.length = c.arena_cap := hs2.1.arena_len_arr
                have hal_le : s.core.arena_len ≤ c.arena_cap := hs2.1.arena_len_le
                have hcr_wf := hw2.arena.refs_wf cr.toNat hcr_ref
                have hcr_bnd3 : cr.toNat + 3 ≤ s.core.arena_len := by
                  have h1 := hcr_wf.1; rw [eagerSubState_arena_len] at h1; exact h1
                have hcr_ar0 : (cr.setWidth 64).toNat < ar2.length := by
                  rw [bv32_setWidth64_toNat, har2_len]; omega
                have hcr_ar2 : (cr.setWidth 64 + 2#64).toNat < ar2.length := by
                  rw [eagerSub_arena_add2 cr, har2_len]; omega
                c0_clean; c0_split
                · -- `(hdr & PH_GARB) == 0`
                  have hcr_ar0' : cr.toNat < ar2.length := by
                    rw [← bv32_setWidth64_toNat cr]; exact hcr_ar0
                  have hcr_hdr0 : (ar2[cr.toNat]'hcr_ar0' &&& 0x00080000#32) = 0#32 := by
                    have hmod : i2 % 2 ^ 64 = i2 := Nat.mod_eq_of_lt hi2_lt64
                    have helem :
                        (ll2[i2 % 2 ^ 64]'(by rw [hmod]; exact hi2_ll')).toNat = cr.toNat :=
                      congrArg BitVec.toNat (getElem_congr_idx (by rw [hmod, hi2_idx]))
                    have hc_and : ar2[(ll2[i2 % 2 ^ 64]'(by rw [hmod]; exact hi2_ll')).toNat]'(by
                        rw [helem]; exact hcr_ar0') &&& 0x00080000#32 = 0#32 := by
                      change (eagerSubState s lm1 ar2 ag2 ll2 es2).core.arena[(eagerSubState s
                        lm1 ar2 ag2 ll2 es2).scratch.last_learned[i2 % 2 ^ 64].toNat] &&&
                        524288 = 0
                      assumption
                    rw [getElem_congr_idx helem.symm]; exact hc_and
                  have hcr_ng : fullArenaClauseGarb s2 cr.toNat = false := by
                    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
                    rw [eagerSubState_arena, List.getElem?_eq_getElem hcr_ar0', Option.getD_some]
                    change ((ar2[cr.toNat]'hcr_ar0' &&& 0x00080000#32) != 0#32) = false
                    rw [hcr_hdr0]; rfl
                  c0_clean; c0_split
                  · -- `(hdr & PH_RED) != 0`
                    c0_clean; c0_split
                    · -- `(u64)csz > tlen`
                      c0_clean; c0_split
                      · -- `(u64)cr + 3ULL + (u64)csz ≤ arena_len`
                        c0_clean; c0_to_group
                        have hcr_sz : (ar2[(cr.setWidth 64 + 2#64).toNat]'hcr_ar2).toNat =
                            fullArenaClauseSizeCore s2.core cr.toNat := by
                          unfold fullArenaClauseSizeCore
                          have h2 := eagerSub_arena_add2 cr
                          rw [eagerSubState_arena,
                            List.getElem?_eq_getElem (by rw [← h2]; exact hcr_ar2),
                            Option.getD_some, getElem_congr_idx h2]
                        let csz := ar2[(cr.setWidth 64 + 2#64).toNat]'hcr_ar2
                        have hcsz_bnd : cr.toNat + 3 + csz.toNat ≤ s.core.arena_len := by
                          have h1 : cr.toNat + 3 + csz.toNat ≤
                              fullArenaNextOff ar2 s.core.arena_len cr.toNat := by
                            rw [hcr_sz]; exact hcr_wf.2.2.1
                          have h2 : fullArenaNextOff ar2 s.core.arena_len cr.toNat ≤
                              s.core.arena_len := hcr_wf.2.2.2.1
                          omega
                        -- Join after Loop 2a (`need`, `rem`, `j`)
                        refine wp_join_group (ts := [i64, i64, i32])
                          (fun (need_v, _, _, ()) ma => m2 = ma) ?_ ?_
                        · rintro _ ⟨need_v, _, _, ⟨⟩⟩ ma rfl
                          c0_clean; c0_split
                          · -- `need_v == 0#64` -> Loop 2b (`act`, `rj`)
                            clear hL2
                            c0_clean; c0_to_group
                            refine wp_join_group (ts := [.bool, i32])
                              (fun (act_v, _, ()) mb => m2 = mb ∧
                                (act_v = false → ∀ k < csz.toNat,
                                  let rl := s2.core.arena[cr.toNat + 3 + k]?.getD 0#32
                                  ¬ (rl.toNat < 2 * s2.core.cur_vars ∧
                                    BitVec.slt 0#32
                                      (BitVec.signExtend 32
                                        (s2.core.vals[rl.toNat]?.getD 0#8)) = true ∧
                                    0 < (s2.core.lvl[rl.toNat / 2]?.getD 0#32).toNat ∧
                                    s2.core.rsns[rl.toNat / 2]?.getD 0xFFFFFFFF#32 = cr))) ?_ ?_
                            · rintro _ ⟨act_v, _, ⟨⟩⟩ mb ⟨rfl, hact_res⟩
                              c0_clean; c0_split
                              · -- `act_v = true`
                                c0_steps; exact skip
                              · -- `act_v = false`: mark `cr` `PH_GARB`, clear `ll[i2]`
                                have hact_f : act_v = false := by cases act_v <;> simp_all
                                have hnonact : ∀ idx < s2.core.trail_end,
                                    let rsn := s2.core.rsns[(s2.core.trl[idx]?.getD 0#32).toNat /
                                      2]?.getD 0xFFFFFFFF#32
                                    rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 →
                                    rsn.toNat ≠ cr.toNat := by
                                  intro idx hidx rsn hne hlg heq
                                  have hmem := hw2.reason_lit_mem idx hidx hne hlg
                                  rw [heq] at hmem
                                  obtain ⟨k, hk, hk_bnd, hkeq⟩ :=
                                    fullArenaClauseLitsCore_mem_iff hmem
                                  have hlt_k : k < csz.toNat := by rw [hcr_sz]; exact hk
                                  have hrl_eq : (s2.core.arena[cr.toNat + 3 + k]?.getD 0#32).toNat =
                                      (s2.core.trl[idx]?.getD 0#32).toNat := hkeq
                                  have hrl_lt : (s2.core.arena[cr.toNat + 3 + k]?.getD 0#32).toNat <
                                      2 * s2.core.cur_vars := by
                                    rw [hrl_eq]; exact hw2.trail_lits_lt idx hidx
                                  have hval1 : s2.core.vals[(s2.core.arena[cr.toNat + 3 + k]?.getD
                                      0#32).toNat]?.getD 0#8 = 1#8 :=
                                    (hw2.vals_true_iff _ hrl_lt).mpr ⟨idx, hidx, hrl_eq.symm⟩
                                  have hslt1 : BitVec.slt 0#32
                                      (BitVec.signExtend 32 (s2.core.vals[(s2.core.arena[cr.toNat +
                                        3 + k]?.getD 0#32).toNat]?.getD 0#8)) = true := by
                                    rw [hval1]; exact i8_eq1_slt0_sext32
                                  have hlvl_pos : 0 < (s2.core.lvl[(s2.core.arena[cr.toNat + 3 +
                                      k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
                                    rw [hrl_eq]
                                    exact Classical.byContradiction fun h0 => by
                                      have hl0 : (s2.core.lvl[(s2.core.trl[idx]?.getD
                                          0#32).toNat / 2]?.getD 0#32).toNat = 0 := by omega
                                      exact hne (hw2.level0_rsn_none idx hidx hl0)
                                  have hrsn_eq : s2.core.rsns[(s2.core.arena[cr.toNat + 3 + k]?.getD
                                      0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = cr := by
                                    apply BitVec.eq_of_toNat_eq; rw [hrl_eq]; exact heq
                                  exact hact_res hact_f k hlt_k ⟨hrl_lt, hslt1, hlvl_pos, hrsn_eq⟩
                                have hcr_len0 : (cr.setWidth 64).toNat < s2.core.arena.length := by
                                  rw [eagerSubState_arena]; exact hcr_ar0
                                have hcr_len2 : (cr.setWidth 64 + 2#64).toNat <
                                    s2.core.arena.length := by
                                  rw [eagerSubState_arena]; exact hcr_ar2
                                c0_steps
                                refine wp_store_sep (FullArenaTactics.c0_store_full_arena
                                  (ar2[(cr.setWidth 64).toNat]'hcr_ar0 ||| 0x00080000#32)
                                  hcr_len0 hm2) fun m hm => ?_
                                c0_steps
                                let ag' := (ag2 + 3#64) + csz.setWidth 64
                                let ar' :=
                                  ar2.set cr.toNat (fullArenaHdr s2 cr.toNat ||| 0x00080000#32)
                                let ll' := ll2.set i2 0xFFFFFFFF#32
                                let es' := es2 + 1#64
                                let s' := eagerSubState s lm1 ar' ag' ll' es'
                                obtain ⟨hw', hrefs'⟩ :=
                                  markGarb_preserves_fullWitness hw2 hs2 hcr_ref ag' hnonact
                                have hnd' :=
                                  FullArenaVarsNodup.of_markGarb_w hw2 hs2 hnd2 hcr_ref ag'
                                have hll_in' : FullLastLearnedIn (fullArenaClauseRefs s2) ll' :=
                                  fullLastLearnedIn_set_sentinel hll2 i2
                                have har'_eq : { s2 with core := { s2.core with
                                    arena := s2.core.arena.set cr.toNat
                                      (fullArenaHdr s2 cr.toNat ||| 0x00080000#32),
                                    arena_garbage := ag' } }.core.arena = ar' := rfl
                                have href_s' : fullArenaClauseRefs s' = fullArenaClauseRefs s2 :=
                                  (fullArenaClauseRefs_congr har'_eq.symm rfl).trans hrefs'
                                have hll' : FullLastLearnedWf s' := by
                                  intro k hk
                                  change ll'[k]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
                                    (ll'[k]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefs s'
                                  rw [href_s']; exact hll_in' k hk
                                have hnd_s' : FullArenaVarsNodup s' :=
                                  (fullArenaVarsNodup_congr har'_eq rfl).mp hnd'
                                have hcr_def : ll2[i2]'hi2_ll' = cr :=
                                  (getElem_congr_idx hi2_idx).symm
                                have hhdr_rw : ar2[(cr.setWidth 64).toNat]'hcr_ar0 =
                                    ar2[cr.toNat]'hcr_ar0' :=
                                  getElem_congr_idx (bv32_setWidth64_toNat cr)
                                have har2_get :
                                    ar2[cr.toNat]?.getD 0#32 = ar2[cr.toNat]'hcr_ar0' := by
                                  rw [List.getElem?_eq_getElem hcr_ar0', Option.getD_some]
                                have hm0 : (FullMem c
                                    { s2 with
                                      core := { s2.core with
                                        arena := ar2.set cr.toNat
                                          (ar2[cr.toNat]'hcr_ar0' ||| 0x00080000#32)
                                        arena_garbage := ag2 + 3 +
                                          (ar2[(cr.setWidth 64 + 2).toNat]'hcr_ar2).setWidth 64 }
                                      scratch := { s2.scratch with
                                        last_learned := ll2.set i2 4294967295
                                        eager_sub_cnt := es2 + 1 } } ⋆ R) m := by
                                  simpa only [s2, eagerSubState, hi2_idx, hcr_def,
                                    bv32_setWidth64_toNat cr, hhdr_rw] using hm
                                have hm' : (FullMem c s' ⋆ R) m := by
                                  dsimp only [s', ar', ag', ll', es', s2, eagerSubState, csz,
                                    fullArenaHdr, fullArenaHdrCore]
                                  rw [har2_get]; exact hm0
                                have hll_len' : ll'.length = 16 := by
                                  simp [ll', show ll2.length = 16 from hs2.2.last_learned_len]
                                refine hJnext () _ ⟨ar', ag', ll', es',
                                  eagerSubState_lengths hs.1 hlm1_len (by simp [ar', har2_len])
                                    hll_len',
                                  ?_, hnd_s', hll', href_s'.trans hrefs2, hm'⟩
                                · simpa only [s', ar', ag', ll', es', s2, eagerSubState,
                                    cr, hi2_idx, Nat.mod_eq_of_lt hi2_lt64] using hw'
                            · -- Loop 2b body (`rj = 0..<csz`)
                              clear skip hJnext hcr_wf hcr_hdr0 hcr_ng hnd2 hll2 hrefs2 htmp_lt
                                href_in hQ
                              intro Jb hJb; c0_clean; c0_to_group
                              refine wp_loop_group (ts := [i32])
                                (fun r2b (rjv, ()) mb => ∃ rj : BitVec 32,
                                  rj.toNat ≤ csz.toNat ∧ r2b = csz.toNat - rj.toNat ∧ rjv = rj ∧
                                  m2 = mb ∧
                                  ∀ k < rj.toNat,
                                    let rl := s2.core.arena[cr.toNat + 3 + k]?.getD 0#32
                                    ¬ (rl.toNat < 2 * s2.core.cur_vars ∧
                                      BitVec.slt 0#32 (BitVec.signExtend 32
                                        (s2.core.vals[rl.toNat]?.getD 0#8)) = true ∧
                                      0 < (s2.core.lvl[rl.toNat / 2]?.getD 0#32).toNat ∧
                                      s2.core.rsns[rl.toNat / 2]?.getD 0xFFFFFFFF#32 = cr)) ?_ ?_
                              · rintro L2b r2b ⟨rjv, ⟨⟩⟩ mb hL2b
                                  ⟨rj, hrj_le, rfl, hrjv, rfl, hinv_b⟩
                                subst rjv
                                have hcsz_lt : csz.toNat < 2 ^ 32 := csz.isLt
                                have hrj_lt32 : rj.toNat < 2 ^ 32 := rj.isLt
                                have hcr_lt32 : cr.toNat < 2 ^ 32 := cr.isLt
                                c0_clean; c0_split
                                · -- `rj < csz`
                                  have hrj_lt : rj.toNat < csz.toNat := by assumption
                                  have hrj1_nat : (rj + 1#32).toNat = rj.toNat + 1 :=
                                    bv32_add1_toNat (by omega)
                                  have hadd3_eq := eagerSub_arena_add3 cr rj
                                  have hrj_ar : (cr.setWidth 64 + 3#64 + rj.setWidth 64).toNat <
                                      ar2.length := by rw [hadd3_eq, har2_len]; omega
                                  let rl :=
                                    ar2[(cr.setWidth 64 + 3#64 + rj.setWidth 64).toNat]'hrj_ar
                                  have hrl_eq :
                                      s2.core.arena[cr.toNat + 3 + rj.toNat]?.getD 0#32 = rl := by
                                    rw [eagerSubState_arena, List.getElem?_eq_getElem (by omega),
                                      Option.getD_some]
                                    exact getElem_congr_idx hadd3_eq.symm
                                  have hmod_b : i2 % 2 ^ 64 = i2 := Nat.mod_eq_of_lt hi2_lt64
                                  have helem_b :
                                      (ll2[i2 % 2 ^ 64]'(by rw [hmod_b]; exact hi2_ll')).toNat =
                                      cr.toNat :=
                                    congrArg BitVec.toNat
                                      (getElem_congr_idx (by rw [hmod_b, hi2_idx]))
                                  have helem_bv_b :
                                      ll2[i2 % 2 ^ 64]'(by rw [hmod_b]; exact hi2_ll') = cr :=
                                    getElem_congr_idx (by rw [hmod_b, hi2_idx])
                                  have hidx_mod_b : (cr.toNat + 3 + rj.toNat) % 2 ^ 64 =
                                      (cr.setWidth 64 + 3#64 + rj.setWidth 64).toNat := by
                                    rw [hadd3_eq, Nat.mod_eq_of_lt (by omega)]
                                  have hrl_hc_eq :
                                      (ar2[(cr.toNat + 3 + rj.toNat) % 2 ^ 64]'(by
                                        rw [hidx_mod_b]; exact hrj_ar)).toNat = rl.toNat :=
                                    congrArg BitVec.toNat (getElem_congr_idx hidx_mod_b)
                                  have hstep_b :
                                      ¬ (rl.toNat < 2 * s2.core.cur_vars ∧
                                        BitVec.slt 0#32 (BitVec.signExtend 32
                                          (s2.core.vals[rl.toNat]?.getD 0#8)) = true ∧
                                        0 < (s2.core.lvl[rl.toNat / 2]?.getD 0#32).toNat ∧
                                        s2.core.rsns[rl.toNat / 2]?.getD 0xFFFFFFFF#32 = cr) →
                                      ∀ k < (rj + 1#32).toNat,
                                        let rlk := s2.core.arena[cr.toNat + 3 + k]?.getD 0#32
                                        ¬ (rlk.toNat < 2 * s2.core.cur_vars ∧
                                          BitVec.slt 0#32 (BitVec.signExtend 32
                                            (s2.core.vals[rlk.toNat]?.getD 0#8)) = true ∧
                                          0 < (s2.core.lvl[rlk.toNat / 2]?.getD 0#32).toNat ∧
                                          s2.core.rsns[rlk.toNat / 2]?.getD 0xFFFFFFFF#32 =
                                            cr) := by
                                    intro hnot k hk
                                    rw [hrj1_nat] at hk
                                    by_cases hke : k = rj.toNat
                                    · subst hke; dsimp only; rwa [hrl_eq]
                                    · exact hinv_b k (by omega)
                                  c0_clean; c0_split
                                  · -- `rl < cur_vars << 1`
                                    have hcm : s2.core.cur_vars ≤ c.max_vars := hs2.1.cur_vars_le
                                    have hcv63 : 2 * s2.core.cur_vars < 2 ^ 64 := by omega
                                    have hcv64 : s2.core.cur_vars < 2 ^ 64 := by omega
                                    have hrl_lt_cv : rl.toNat < 2 * s2.core.cur_vars := by
                                      have hlt_hc : rl.toNat <
                                          2 * (s2.core.cur_vars % 2 ^ 64) % 2 ^ 64 := by
                                        have hc0 :
                                            (ar2[(cr.toNat + 3 + rj.toNat) % 2 ^ 64]'(by
                                              rw [hidx_mod_b]; exact hrj_ar)).toNat <
                                            2 * (s2.core.cur_vars % 2 ^ 64) % 2 ^ 64 := by
                                          simpa only [eagerSubState_arena, eagerSubState_ll,
                                            eagerSubState_cur_vars, helem_b] using by assumption
                                        rwa [hrl_hc_eq] at hc0
                                      rwa [Nat.mod_eq_of_lt hcv64,
                                        Nat.mod_eq_of_lt hcv63] at hlt_hc
                                    have hrl_vals :
                                        (rl.setWidth 64).toNat < s2.core.vals.length := by
                                      rw [bv32_setWidth64_toNat, hs2.1.vals_len]; omega
                                    c0_clean; c0_split
                                    · -- `vals[rl] > 0`
                                      have hrl_lvl : ((rl >>> 1#32).setWidth 64).toNat <
                                          s2.core.lvl.length := by
                                        rw [bv32_setWidth64_toNat, bv32_lshr_1',
                                          hs2.1.lvl_len]; omega
                                      have hrl_rsns : ((rl >>> 1#32).setWidth 64).toNat <
                                          s2.core.rsns.length := by
                                        rw [bv32_setWidth64_toNat, bv32_lshr_1',
                                          hs2.1.rsns_len]; omega
                                      c0_clean; c0_split
                                      · -- `lvl[rl >> 1] > 0`
                                        c0_clean; c0_split
                                        · -- `rsns[rl >> 1] == cr` -> `act = true; break;`
                                          c0_steps
                                          exact hJb (true, rj, ()) m2 ⟨rfl, fun h => by cases h⟩
                                        · -- `rsns != cr`
                                          have hne_rs :
                                              s2.core.rsns[rl.toNat / 2]?.getD 0xFFFFFFFF#32 ≠
                                                cr := by
                                            have hlen_r : rl.toNat / 2 < s.core.rsns.length := by
                                              rw [hs2.1.rsns_len, bv32_setWidth64_toNat,
                                                bv32_lshr_1'] at hrl_rsns
                                              rw [hcl.rsns_len]; exact hrl_rsns
                                            rw [eagerSubState_rsns,
                                              List.getElem?_eq_getElem hlen_r, Option.getD_some]
                                            have hc0 : ¬ s.core.rsns[(ar2[(cr.toNat + 3 +
                                                rj.toNat) % 2 ^ 64]'(by
                                                  rw [hidx_mod_b]; exact hrj_ar)).toNat / 2]'(by
                                                rw [hrl_hc_eq]; exact hlen_r) = cr := by
                                              simpa only [eagerSubState_rsns, eagerSubState_arena,
                                                eagerSubState_ll, helem_b, helem_bv_b] using
                                                by assumption
                                            rwa [getElem_congr_idx
                                              (congrArg (· / 2) hrl_hc_eq)] at hc0
                                          c0_steps
                                          refine hJ () m2 ?_; c0_steps
                                          exact hL2b _ (rj + 1#32, ()) m2 (by rw [hrj1_nat]; omega)
                                            ⟨rj + 1#32, by rw [hrj1_nat]; omega, rfl, rfl, rfl,
                                              hstep_b (fun ⟨_, _, _, hrs⟩ => absurd hrs hne_rs)⟩
                                      · -- `lvl[rl >> 1] == 0`
                                        have hnl : ¬ 0 <
                                            (s2.core.lvl[rl.toNat / 2]?.getD 0#32).toNat := by
                                          have hlen_l : rl.toNat / 2 < s.core.lvl.length := by
                                            rw [hs2.1.lvl_len, bv32_setWidth64_toNat,
                                              bv32_lshr_1'] at hrl_lvl
                                            rw [hcl.lvl_len]; exact hrl_lvl
                                          rw [eagerSubState_lvl,
                                            List.getElem?_eq_getElem hlen_l, Option.getD_some]
                                          have hc0 : ¬ (0#32 : BitVec 32).toNat <
                                              (s.core.lvl[(ar2[(cr.toNat + 3 +
                                                rj.toNat) % 2 ^ 64]'(by
                                                  rw [hidx_mod_b]; exact hrj_ar)).toNat / 2]'(by
                                                rw [hrl_hc_eq]; exact hlen_l)).toNat := by
                                            simpa only [eagerSubState_lvl, eagerSubState_arena,
                                              eagerSubState_ll, helem_b] using by assumption
                                          rwa [getElem_congr_idx
                                            (congrArg (· / 2) hrl_hc_eq)] at hc0
                                        c0_steps
                                        refine hJ () m2 ?_; c0_steps
                                        exact hL2b _ (rj + 1#32, ()) m2 (by rw [hrj1_nat]; omega)
                                          ⟨rj + 1#32, by rw [hrj1_nat]; omega, rfl, rfl, rfl,
                                            hstep_b (fun ⟨_, _, hpos, _⟩ => hnl hpos)⟩
                                    · -- `vals[rl] ≤ 0`
                                      have hnslt : ¬ BitVec.slt 0#32 (BitVec.signExtend 32
                                          (s2.core.vals[rl.toNat]?.getD 0#8)) = true := by
                                        have hlen_v : rl.toNat < s.core.vals.length := by
                                          rw [hs2.1.vals_len, bv32_setWidth64_toNat] at hrl_vals
                                          rw [hcl.vals_len]; exact hrl_vals
                                        rw [eagerSubState_vals,
                                          List.getElem?_eq_getElem hlen_v, Option.getD_some]
                                        have hc0 : BitVec.slt 0#32 (BitVec.signExtend 32
                                            (s.core.vals[(ar2[(cr.toNat + 3 +
                                              rj.toNat) % 2 ^ 64]'(by
                                                rw [hidx_mod_b]; exact hrj_ar)).toNat]'(by
                                              rw [hrl_hc_eq]; exact hlen_v))) = false := by
                                          simpa only [eagerSubState_vals, eagerSubState_arena,
                                            eagerSubState_ll, helem_b] using by assumption
                                        rw [getElem_congr_idx (hj := hlen_v) hrl_hc_eq] at hc0
                                        rw [hc0]; decide
                                      c0_steps
                                      refine hJ () m2 ?_; c0_steps
                                      exact hL2b _ (rj + 1#32, ()) m2 (by rw [hrj1_nat]; omega)
                                        ⟨rj + 1#32, by rw [hrj1_nat]; omega, rfl, rfl, rfl,
                                          hstep_b (fun ⟨_, hslt, _⟩ => hnslt hslt)⟩
                                  · -- `rl ≥ cur_vars << 1`
                                    have hcm : s2.core.cur_vars ≤ c.max_vars := hs2.1.cur_vars_le
                                    have hcv63 : 2 * s2.core.cur_vars < 2 ^ 64 := by omega
                                    have hcv64 : s2.core.cur_vars < 2 ^ 64 := by omega
                                    have hnlt : ¬ rl.toNat < 2 * s2.core.cur_vars := by
                                      have hc0 : ¬ (ar2[(cr.toNat + 3 + rj.toNat) % 2 ^ 64]'(by
                                          rw [hidx_mod_b]; exact hrj_ar)).toNat <
                                          2 * (s2.core.cur_vars % 2 ^ 64) % 2 ^ 64 := by
                                        simpa only [eagerSubState_arena, eagerSubState_ll,
                                          eagerSubState_cur_vars, helem_b] using by assumption
                                      rw [hrl_hc_eq, Nat.mod_eq_of_lt hcv64,
                                        Nat.mod_eq_of_lt hcv63] at hc0
                                      exact hc0
                                    c0_steps
                                    refine hJ () m2 ?_; c0_steps
                                    exact hL2b _ (rj + 1#32, ()) m2 (by rw [hrj1_nat]; omega)
                                      ⟨rj + 1#32, by rw [hrj1_nat]; omega, rfl, rfl, rfl,
                                        hstep_b (fun ⟨hlt, _⟩ => hnlt hlt)⟩
                                · -- Exit Loop 2b (`rj = csz`, `act = false`)
                                  have hrj_eq : rj.toNat = csz.toNat := by
                                    have hmod : i2 % 2 ^ 64 = i2 := Nat.mod_eq_of_lt hi2_lt64
                                    have helem :
                                        (ll2[i2 % 2 ^ 64]'(by rw [hmod]; exact hi2_ll')).toNat =
                                        cr.toNat :=
                                      congrArg BitVec.toNat
                                        (getElem_congr_idx (by rw [hmod, hi2_idx]))
                                    have hidx2 : (cr.toNat + 2) % 2 ^ 64 =
                                        (cr.setWidth 64 + 2#64).toNat := by
                                      rw [eagerSub_arena_add2 cr, Nat.mod_eq_of_lt (by omega)]
                                    have hc0 : ¬ rj.toNat < csz.toNat := by
                                      simpa only [eagerSubState_arena, eagerSubState_ll,
                                        helem, hidx2] using by assumption
                                    omega
                                  c0_steps
                                  exact hJb (false, rj, ()) m2
                                    ⟨rfl, fun _ k hk => hinv_b k (hrj_eq ▸ hk)⟩
                              · intro J2b hJ2b; c0_steps
                                exact hJ2b csz.toNat (0#32, ()) m2
                                  ⟨0#32, Nat.zero_le _, rfl, rfl, rfl, fun k hk => by simp at hk⟩
                          · -- `need_v != 0#64`
                            c0_steps; exact skip
                        · -- Loop 2a (`while (j < csz)`)
                          intro Ja hJa; c0_clean; c0_to_group
                          have hcsz_bnd2 : cr.toNat + 3 + csz.toNat ≤ s2.core.arena.length := by
                            dsimp only [s2]; rw [eagerSubState_arena, har2_len]; omega
                          exact eagerSub_loop2a_wp hs2 hw2 rfl hlm1_len hcr_ref hcr_ng hcr_sz
                            hcsz_bnd2 hm2 Ja
                            (fun nv rv jv ma hm_eq => hJa (nv, rv, jv, ()) ma hm_eq)
                      · c0_steps; exact skip
                    · c0_steps; exact skip
                  · c0_steps; exact skip
                · c0_steps; exact skip
              · -- `(u64)cr + 3ULL > arena_len`
                c0_steps; exact skip
            · -- `cr == 0xFFFFFFFF`
              c0_steps; exact skip
        · -- Exit Loop 2 (`i2 = 8`) -> Loop 3 (`i = 0..<tlen`)
          clear hL2
          c0_clean; c0_to_group
          refine wp_loop_group (ts := [i64])
            (fun r3 (iv3, ()) m3 => ∃ i3 lm3,
              let s3 := eagerSubState s lm3 ar2 ag2 ll2 es2
              i3 ≤ s.core.tmp_len ∧ r3 = s.core.tmp_len - i3 ∧ iv3 = BitVec.ofNat 64 i3 ∧
              lm3.length = 2 * c.max_vars ∧
              (∀ l < 2 * c.max_vars, lm3[l]?.getD 0#8 ≠ 0#8 →
                (∃ j < s.core.tmp_len, (s.core.tmp[j]?.getD 0#32).toNat = l) ∧
                (∀ j < i3, (s.core.tmp[j]?.getD 0#32).toNat ≠ l)) ∧
              (FullMem c s3 ⋆ R) m3) ?_ ?_
          · rintro L3 r3 ⟨iv3, ⟨⟩⟩ m3 hL3 ⟨i3, lm3, hi3_le, rfl, rfl, hlm3_len, hlm3_cov, hm3⟩
            have hi3_lt64 : i3 < 2 ^ 64 := by omega
            c0_clean; c0_split
            · -- Loop 3 body (`i3 < tlen`)
              let s3_cur := eagerSubState s lm3 ar2 ag2 ll2 es2
              change (FullMem c s3_cur ⋆ R) m3 at hm3
              have hi3_lt : i3 < s.core.tmp_len := by
                rw [Nat.mod_eq_of_lt hi3_lt64, Nat.mod_eq_of_lt htl_lt64] at hc; exact hc
              have hi3_idx : (BitVec.ofNat 64 i3).toNat = i3 := bv64_ofNat_toNat hi3_lt64
              have hi3_tmp : (BitVec.ofNat 64 i3).toNat < s3_cur.core.tmp.length := by
                rw [eagerSubState_tmp, hcl.tmp_len_arr, hi3_idx]; omega
              have htmp_arr : s.core.tmp.length = c.max_vars := hcl.tmp_len_arr
              have heq_t : s3_cur.core.tmp[(BitVec.ofNat 64 i3).toNat]'hi3_tmp =
                  s.core.tmp[i3]'(by rw [htmp_arr]; omega) := by
                dsimp only [s3_cur, eagerSubState]; exact getElem_congr_idx hi3_idx
              have hl3_idx_lm :
                  ((s3_cur.core.tmp[(BitVec.ofNat 64 i3).toNat]'hi3_tmp).setWidth 64).toNat <
                    s3_cur.core.lit_mark.length := by
                have hget :=
                  List.getElem?_eq_getElem (by rw [htmp_arr]; omega : i3 < s.core.tmp.length)
                have ht := htmp_lt i3 hi3_lt
                rw [hget, Option.getD_some] at ht
                rw [bv32_setWidth64_toNat, eagerSubState_lm, hlm3_len, heq_t]; omega
              c0_steps
              refine wp_load_of (FullArenaTactics.c0_load_full_tmp hi3_tmp hm3) ?_
              c0_steps
              have hlm3_next :
                  lm3.set ((s3_cur.core.tmp[(BitVec.ofNat 64 i3).toNat]'hi3_tmp).setWidth
                    64).toNat 0#8 =
                  lm3.set (s.core.tmp[i3]'(by rw [hcl.tmp_len_arr]; omega)).toNat 0#8 := by
                rw [bv32_setWidth64_toNat, heq_t]
              have hi3_add : (BitVec.ofNat 64 i3 + 1#64).toNat = i3 + 1 := by
                rw [bv64_add1_toNat (by rw [hi3_idx]; omega), hi3_idx]
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
              · exact (congrArg (fun lm' => (FullMem c (eagerSubState s lm' ar2 ag2 ll2 es2) ⋆ R) m)
                  hlm3_next).mp hm
            · -- Exit Loop 3 (`i3 = tlen`)
              have hi3_eq : i3 = s.core.tmp_len := by
                rw [Nat.mod_eq_of_lt hi3_lt64, Nat.mod_eq_of_lt htl_lt64] at hc; omega
              subst hi3_eq
              let s3 := eagerSubState s lm3 ar2 ag2 ll2 es2
              have hs3_len : s3.LengthsOk c :=
                eagerSubState_lengths hs.1 hlm3_len hs2.1.arena_len_arr hs2.2.last_learned_len
              have hw3 : FullWitnessInv c F0 F_cur s3.core := fullWitness_with_litMark hw2 lm3
              have hclr3 : FullLitMarksClear c s3 := by
                refine ⟨hlm_clr.1, fun l hl => Classical.byContradiction fun hnz => ?_⟩
                obtain ⟨⟨j, hj, hje⟩, hprev⟩ := hlm3_cov l hl hnz
                exact hprev j hj hje
              have hlm3_eq : lm3 = s.core.lit_mark :=
                list_bv8_eq_of_getD0 hlm3_len hcl.lit_mark_len hclr3.2 hlm_clr.2
              let s3_fin : FullState :=
                { s with
                  core := { s.core with arena := ar2, arena_garbage := ag2 }
                  scratch := { s.scratch with last_learned := ll2, eager_sub_cnt := es2 } }
              have hs3_eq : s3 = s3_fin := by dsimp only [s3, s3_fin, eagerSubState]; rw [hlm3_eq]
              have hs3'_len : s3_fin.LengthsOk c := hs3_eq ▸ hs3_len
              have hw3' : FullWitnessInv c F0 F_cur s3_fin.core := hs3_eq ▸ hw3
              have hclr3' : FullLitMarksClear c s3_fin := hs3_eq ▸ hclr3
              have hnd3' : FullArenaVarsNodup s3_fin := hs3_eq ▸ hnd2
              c0_clean; c0_split
              · -- `new_ref < 0x80000000` -> shift `last_learned`
                have hnref_lt : new_ref.toNat < 0x80000000 := by assumption
                have hnref_ref : new_ref.toNat ∈ fullArenaClauseRefs s3 := by
                  change new_ref.toNat ∈ fullArenaClauseRefs s2
                  rw [hrefs2]; exact href_in hnref_lt
                c0_clean; c0_to_group
                refine wp_loop_group (ts := [i64])
                  (fun k (kv, ()) m4 => ∃ ll4,
                    k ≤ 7 ∧ kv = BitVec.ofNat 64 k ∧ ll4.length = 16 ∧
                    FullLastLearnedIn (fullArenaClauseRefs s3) ll4 ∧
                    (FullMem c (eagerSubState s lm3 ar2 ag2 ll4 es2) ⋆ R) m4) ?_ ?_
                · rintro L4 k ⟨kv, ⟨⟩⟩ m4 hL4 ⟨ll4, hk_le, rfl, hll4_len, hll4_in, hm4⟩
                  have hk_lt64 : k < 2 ^ 64 := by omega
                  c0_clean; c0_split
                  · -- `k > 0`
                    have hk_pos : 0 < k := by
                      rw [Nat.mod_eq_of_lt hk_lt64,
                        show (BitVec.toNat (0 : BitVec 64)) = 0 from rfl] at hc
                      exact hc
                    have hk1_nat : (BitVec.ofNat 64 k - 1#64).toNat = k - 1 := by
                      rw [bv64_sub1_toNat' (by rw [bv64_ofNat_toNat hk_lt64]; exact hk_pos),
                        bv64_ofNat_toNat hk_lt64]
                    have hk1_idx : (BitVec.ofNat 64 k - 1#64).toNat < ll4.length := by
                      rw [hk1_nat, hll4_len]; omega
                    have hk_idx : (BitVec.ofNat 64 k).toNat < ll4.length := by
                      rw [bv64_ofNat_toNat hk_lt64, hll4_len]; omega
                    c0_steps
                    refine wp_load_of (FullArenaTactics.c0_load_full_last_learned hk1_idx hm4) ?_
                    refine wp_store_sep
                      (FullArenaTactics.c0_store_full_last_learned
                        (ll4[(BitVec.ofNat 64 k - 1#64).toNat]'hk1_idx) hk_idx hm4)
                      fun m hm => ?_
                    c0_steps
                    have hll_next : ll4.set (BitVec.ofNat 64 k).toNat
                        (ll4[(BitVec.ofNat 64 k - 1#64).toNat]'hk1_idx) =
                        ll4.set k (ll4[k - 1]'(by rw [hll4_len]; omega)) := by
                      rw [bv64_ofNat_toNat hk_lt64, getElem_congr_idx hk1_nat]
                    refine hL4 (k - 1) (BitVec.ofNat 64 k - 1#64, ()) _ (by omega)
                      ⟨ll4.set k (ll4[k - 1]'(by rw [hll4_len]; omega)),
                        by omega,
                        BitVec.eq_of_toNat_eq (by rw [hk1_nat, bv64_ofNat_toNat (by omega)]),
                        by simp [hll4_len], ?_, ?_⟩
                    · exact fullLastLearnedIn_shift_step hll4_in hk_pos (by omega) (by omega)
                    · exact (congrArg (fun ll' =>
                        (FullMem c (eagerSubState s lm3 ar2 ag2 ll' es2) ⋆ R) m) hll_next).mp hm
                  · -- Exit Loop 4 (`k = 0`) -> `ll[0] = (u32)new_ref`
                    have hk_zero : k = 0 := by
                      rw [Nat.mod_eq_of_lt hk_lt64,
                        show (BitVec.toNat (0 : BitVec 64)) = 0 from rfl] at hc
                      omega
                    subst hk_zero
                    c0_steps
                    refine wp_store_sep (FullLearnAnaTactics.store_full_ll0_off
                      (new_ref.setWidth 32) (by rw [eagerSubState_ll, hll4_len]; decide) hm4)
                      fun m hm => ?_
                    c0_steps
                    let ll_fin := ll4.set 0 (new_ref.setWidth 32)
                    let s_fin : FullState :=
                      { s with
                        core := { s.core with arena := ar2, arena_garbage := ag2 }
                        scratch :=
                          { s.scratch with last_learned := ll_fin, eager_sub_cnt := es2 } }
                    have hll_fin_in : FullLastLearnedIn (fullArenaClauseRefs s3) ll_fin :=
                      fullLastLearnedIn_set0 hll4_in (new_ref.setWidth 32)
                        (by
                          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                          exact hnref_ref)
                        (by omega)
                    have hs_fin : s_fin.LengthsOk c :=
                      ⟨hs3'_len.core_ok, { hs3'_len.scratch_ok with
                        last_learned_len := by simp [s_fin, ll_fin, hll4_len] }⟩
                    have hm_fin : (FullMem c s_fin ⋆ R) m :=
                      (congrArg (fun lm' => (FullMem c { s_fin with core :=
                          { s_fin.core with lit_mark := lm' } } ⋆ R) m) hlm3_eq).mp hm
                    exact hQ ar2 ag2 s_fin.scratch m
                      ⟨hs_fin, hw3', hclr3', hnd3', ⟨hll_fin_in, hext.2⟩, hdm⟩ rfl hm_fin
                · intro J4 hJ4; c0_steps
                  exact hJ4 7 (7#64, ()) m3 ⟨ll2, Nat.le_refl _, rfl,
                    hs2.2.last_learned_len, hll2, hm3⟩
              · -- `new_ref ≥ 0x80000000`
                c0_steps
                have hm3_fin : (FullMem c s3_fin ⋆ R) m3 := hs3_eq ▸ (hm3 : (FullMem c s3 ⋆ R) m3)
                exact hQ ar2 ag2 s3_fin.scratch m3
                  ⟨hs3'_len, hw3', hclr3', hnd3', ⟨hll2, hext.2⟩, hdm⟩ rfl hm3_fin
          · intro J3 hJ3; c0_steps
            exact hJ3 s.core.tmp_len (0#64, ()) m2 ⟨0, lm1, Nat.zero_le _, rfl, rfl, hlm1_len,
              fun l hl hnz => ⟨hlm1_cov l hl hnz, fun j hj => by omega⟩, hm2⟩
      · intro J2 hJ2; c0_steps
        exact hJ2 8 (0#64, ()) m1 ⟨0, s.core.arena, s.core.arena_garbage, s.scratch.last_learned,
          s.scratch.eager_sub_cnt, Nat.zero_le 8, rfl, rfl, hs1,
          fullWitness_with_litMark hs.2.1 lm1, hnd, hext.1, rfl, hm1⟩
  · intro J hJ; c0_steps
    exact hJ s.core.tmp_len (0#64, ()) m ⟨0, s.core.lit_mark, Nat.zero_le _, rfl, rfl,
      hcl.lit_mark_len, fun l hl hnz => absurd (hlm_clr.2 l hl) hnz, hm⟩

end LeanQbe.T.Examples.Kissat.Full
