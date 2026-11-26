/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep8
public import LeanQbe.T.Examples.Kissat.FullSpec2
public import LeanQbe.T.Examples.Kissat.FullAssignAddLemmas1
public import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas
public meta import Lean.Elab.Tactic
public meta import LeanQbe.T.Logic.C0Step

/-!
# Kissat Fidelity Step 8 Watch-Push Helpers (`FullFidelityStep8ProofWatch0`)

Parametric `(Γ : Env)` helper theorems (`0` `import all`, `public section`) for Step-8 watch
stack push (`wpush_reloc_step8_wp`, `wpush_caseC_step8_wp`, `wpush_caseB_step8_wp`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep8

open Std Std.Sat Std.ExtHashMap LeanQbe.T.C0Step
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

open scoped FullArenaTactics FullAssignAddTactics
open FullAssignAddTactics FullAssignAddSpecs

/-! ## 1. Watch Stack Push Helpers -/

abbrev wOff (wvec : List (BitVec 32)) (l : Nat) : Nat := (wvec[2 * l]?.getD 0#32).toNat
abbrev wSz (wvec : List (BitVec 32)) (l : Nat) : Nat := (wvec[2 * l + 1]?.getD 0#32).toNat

@[expose] def WatchPresAll (s s1 : FullState) : Prop :=
  s1.core.cur_vars = s.core.cur_vars ∧
  ∀ l < 2 * s.core.cur_vars, fullWatchSize s1 l = fullWatchSize s l ∧
    ∀ k < fullWatchSize s l,
      s1.core.wstk[fullWatchOff s1 l + k]? = s.core.wstk[fullWatchOff s l + k]?

theorem watchPresAll_refl (s : FullState) : WatchPresAll s s :=
  ⟨rfl, fun _ _ => ⟨rfl, fun _ _ => rfl⟩⟩

theorem watchPresAll_trans {s s1 s2 : FullState}
    (h1 : WatchPresAll s s1) (h2 : WatchPresAll s1 s2) : WatchPresAll s s2 := by
  refine ⟨h2.1.trans h1.1, fun l hl => ?_⟩
  have ⟨hs1, he1⟩ := h1.2 l hl
  have ⟨hs2, he2⟩ := h2.2 l (h1.1 ▸ hl)
  exact ⟨hs2.trans hs1, fun k hk => (he2 k (hs1 ▸ hk)).trans (he1 k hk)⟩

theorem wvec_set_even_u {wvec : List (BitVec 32)} {l : Nat} {v : BitVec 32}
    (hl : 2 * l < wvec.length) (j : Nat) :
    (wvec.set (2 * l) v)[2 * j + 1]? = wvec[2 * j + 1]? ∧
    (j ≠ l → (wvec.set (2 * l) v)[2 * j]? = wvec[2 * j]?) ∧
    (wvec.set (2 * l) v)[2 * l]? = some v :=
  ⟨List.getElem?_set_ne (by omega), fun hne => List.getElem?_set_ne (by omega),
   List.getElem?_set_self hl⟩

theorem wvec_set_odd_u {wvec : List (BitVec 32)} {l : Nat} {v : BitVec 32}
    (hl : 2 * l + 1 < wvec.length) (j : Nat) :
    (wvec.set (2 * l + 1) v)[2 * j]? = wvec[2 * j]? ∧
    (j ≠ l → (wvec.set (2 * l + 1) v)[2 * j + 1]? = wvec[2 * j + 1]?) ∧
    (wvec.set (2 * l + 1) v)[2 * l + 1]? = some v :=
  ⟨List.getElem?_set_ne (by omega), fun hne => List.getElem?_set_ne (by omega),
   List.getElem?_set_self hl⟩

theorem wpush_sentinel_disjoint {k1 : FullCoreState} {lit cnt : Nat}
    (hlay : WatchStackLayout k1) (hlit : lit < 2 * k1.cur_vars) (hc12 : cnt = 1 ∨ cnt = 2)
    (hs0 : k1.wstk[fullWatchOffCore k1 lit + fullWatchSizeCore k1 lit]? = some 0xFFFFFFFF#32)
    (hs1 : cnt = 2 →
      k1.wstk[fullWatchOffCore k1 lit + fullWatchSizeCore k1 lit + 1]? = some 0xFFFFFFFF#32) :
    ∀ j < 2 * k1.cur_vars, j ≠ lit → 0 < fullWatchSizeCore k1 j →
      fullWatchOffCore k1 j + fullWatchSizeCore k1 j ≤ fullWatchOffCore k1 lit ∨
      fullWatchOffCore k1 lit + (fullWatchSizeCore k1 lit + cnt) ≤ fullWatchOffCore k1 j := by
  intro j hj hne hszj
  by_cases h1 : fullWatchOffCore k1 j + fullWatchSizeCore k1 j ≤ fullWatchOffCore k1 lit
  · exact Or.inl h1
  by_cases h2 : fullWatchOffCore k1 lit + (fullWatchSizeCore k1 lit + cnt) ≤ fullWatchOffCore k1 j
  · exact Or.inr h2
  exfalso
  have hbad2 :
      fullWatchOffCore k1 j = fullWatchOffCore k1 lit + fullWatchSizeCore k1 lit + 1 →
      cnt = 2 → False := fun heq hc2 => by
    have hns := hlay.no_sentinel j hj 0 hszj
    rw [Nat.add_zero, heq] at hns; exact hns (hs1 hc2)
  by_cases hszl : 0 < fullWatchSizeCore k1 lit
  · rcases hlay.disjoint j lit hj hlit hne hszj hszl with hd | hd
    · exact h1 hd
    by_cases heq : fullWatchOffCore k1 j = fullWatchOffCore k1 lit + fullWatchSizeCore k1 lit
    · have hns := hlay.no_sentinel j hj 0 hszj
      rw [Nat.add_zero, heq] at hns; exact hns hs0
    · exact hbad2 (by omega) (by omega)
  · by_cases hle : fullWatchOffCore k1 j ≤ fullWatchOffCore k1 lit
    · have hns :=
        hlay.no_sentinel j hj (fullWatchOffCore k1 lit - fullWatchOffCore k1 j) (by omega)
      rw [show fullWatchOffCore k1 j + (fullWatchOffCore k1 lit - fullWatchOffCore k1 j) =
        fullWatchOffCore k1 lit + fullWatchSizeCore k1 lit by omega] at hns; exact hns hs0
    · exact hbad2 (by omega) (by omega)

theorem wpush_finalize {s s2 : FullState} {lit cnt dst wlen' : Nat}
    {w0 w1 : BitVec 32} {wvec' wstk' wsort' : List (BitVec 32)}
    (hlay2 : WatchStackLayout s2.core) (hpres : WatchPresAll s s2)
    (hlit : lit < 2 * s.core.cur_vars) (hc12 : cnt = 1 ∨ cnt = 2)
    (hw0 : cnt = 1 → w0 ≠ 0xFFFFFFFF#32)
    (hw1 : cnt = 2 → w0 ≠ 0xFFFFFFFF#32 ∧ w1 ≠ 0xFFFFFFFF#32)
    (hwlen_le : s2.core.wlen ≤ wlen') (hdst1 : 1 ≤ dst)
    (hdst_le : dst + (wSz s2.core.wvec lit + cnt) ≤ wlen')
    (hother_wv : ∀ j < 2 * s.core.cur_vars, j ≠ lit →
      wOff wvec' j = wOff s2.core.wvec j ∧ wSz wvec' j = wSz s2.core.wvec j)
    (hlit_off : wOff wvec' lit = dst) (hlit_sz : wSz wvec' lit = wSz s2.core.wvec lit + cnt)
    (hdisj : ∀ j < 2 * s.core.cur_vars, j ≠ lit → 0 < wSz s2.core.wvec j →
      wOff s2.core.wvec j + wSz s2.core.wvec j ≤ dst ∨
      dst + (wSz s2.core.wvec lit + cnt) ≤ wOff s2.core.wvec j)
    (hother_st : ∀ j < 2 * s.core.cur_vars, j ≠ lit → ∀ k < wSz s2.core.wvec j,
      wstk'[wOff s2.core.wvec j + k]? = s2.core.wstk[wOff s2.core.wvec j + k]?)
    (hcopy : ∀ k < wSz s2.core.wvec lit,
      wstk'[dst + k]? = s2.core.wstk[wOff s2.core.wvec lit + k]?)
    (hat0 : wstk'[dst + wSz s2.core.wvec lit]? = some w0)
    (hat1 : cnt = 2 → wstk'[dst + wSz s2.core.wvec lit + 1]? = some w1)
    (wusable' : BitVec 64) :
    let s' : FullState :=
      { s with
        core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable' }
        scratch := { s.scratch with wsort := wsort' } }
    WatchStackLayout s'.core ∧
    (∀ l < 2 * s.core.cur_vars, l ≠ lit → fullWatchSize s' l = fullWatchSize s l ∧
      ∀ k < fullWatchSize s l,
        s'.core.wstk[fullWatchOff s' l + k]? = s.core.wstk[fullWatchOff s l + k]?) ∧
    fullWatchSize s' lit = fullWatchSize s lit + cnt ∧
    (∀ k < fullWatchSize s lit,
      s'.core.wstk[fullWatchOff s' lit + k]? = s.core.wstk[fullWatchOff s lit + k]?) ∧
    s'.core.wstk[fullWatchOff s' lit + fullWatchSize s lit]? = some w0 ∧
    (cnt = 2 → s'.core.wstk[fullWatchOff s' lit + fullWatchSize s lit + 1]? = some w1) := by
  intro s'
  have hcv2 : s2.core.cur_vars = s.core.cur_vars := hpres.1
  have hlit2 : lit < 2 * s2.core.cur_vars := hcv2 ▸ hlit
  have hoff_l : fullWatchOffCore s'.core lit = dst := hlit_off
  have hsz_l : fullWatchSizeCore s'.core lit = wSz s2.core.wvec lit + cnt := hlit_sz
  have hoff_o : ∀ j < 2 * s.core.cur_vars, j ≠ lit →
      fullWatchOffCore s'.core j = fullWatchOffCore s2.core j :=
    fun j hj hne => (hother_wv j hj hne).1
  have hsz_o : ∀ j < 2 * s.core.cur_vars, j ≠ lit →
      fullWatchSizeCore s'.core j = fullWatchSizeCore s2.core j :=
    fun j hj hne => (hother_wv j hj hne).2
  have hsz_lit2 : wSz s2.core.wvec lit = fullWatchSizeCore s.core lit := (hpres.2 lit hlit).1
  have hne0 : w0 ≠ 0xFFFFFFFF#32 := by
    rcases hc12 with rfl | rfl; exact hw0 rfl; exact (hw1 rfl).1
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_,
    by change fullWatchSizeCore s'.core lit = fullWatchSizeCore s.core lit + cnt
       rw [hsz_l, hsz_lit2], ?_, ?_, ?_⟩
  · intro l hl; by_cases hll : l = lit
    · rcases hll.symm with rfl; rw [hoff_l, hsz_l]; exact hdst_le
    · rw [hoff_o l hl hll, hsz_o l hl hll]
      exact Nat.le_trans (hlay2.bounds l (hcv2 ▸ hl)) hwlen_le
  · intro l hl hpos; by_cases hll : l = lit
    · rcases hll.symm with rfl; rw [hoff_l]; exact hdst1
    · rw [hsz_o l hl hll] at hpos; rw [hoff_o l hl hll]
      exact hlay2.pos_off l (hcv2 ▸ hl) hpos
  · intro l1 l2 h1 h2 hne hp1 hp2; by_cases hl1 : l1 = lit
    · rcases hl1.symm with rfl; have hl2 : l2 ≠ lit := hne.symm
      rw [hsz_o l2 h2 hl2] at hp2
      rw [hoff_l, hsz_l, hoff_o l2 h2 hl2, hsz_o l2 h2 hl2]; exact (hdisj l2 h2 hl2 hp2).symm
    · by_cases hl2 : l2 = lit
      · rcases hl2.symm with rfl; rw [hsz_o l1 h1 hl1] at hp1
        rw [hoff_o l1 h1 hl1, hsz_o l1 h1 hl1, hoff_l, hsz_l]; exact hdisj l1 h1 hl1 hp1
      · rw [hsz_o l1 h1 hl1] at hp1; rw [hsz_o l2 h2 hl2] at hp2
        rw [hoff_o l1 h1 hl1, hsz_o l1 h1 hl1, hoff_o l2 h2 hl2, hsz_o l2 h2 hl2]
        exact hlay2.disjoint l1 l2 (hcv2 ▸ h1) (hcv2 ▸ h2) hne hp1 hp2
  · intro l hl k hk; by_cases hll : l = lit
    · rcases hll.symm with rfl; rw [hsz_l] at hk; rw [hoff_l]
      by_cases hks : k < wSz s2.core.wvec lit
      · change wstk'[dst + k]? ≠ _; rw [hcopy k hks]; exact hlay2.no_sentinel lit hlit2 k hks
      · by_cases hk0 : k = wSz s2.core.wvec lit
        · subst hk0; change wstk'[dst + wSz s2.core.wvec lit]? ≠ _; rw [hat0]
          exact fun heq => hne0 (Option.some.inj heq)
        · have hc2 : cnt = 2 := by omega
          have hk1 : k = wSz s2.core.wvec lit + 1 := by omega
          subst hk1; change wstk'[dst + (wSz s2.core.wvec lit + 1)]? ≠ _
          rw [← Nat.add_assoc, hat1 hc2]; exact fun heq => (hw1 hc2).2 (Option.some.inj heq)
    · rw [hsz_o l hl hll] at hk; rw [hoff_o l hl hll]
      change wstk'[wOff s2.core.wvec l + k]? ≠ _
      rw [hother_st l hl hll k hk]; exact hlay2.no_sentinel l (hcv2 ▸ hl) k hk
  · intro l hl hne; have ⟨hp1, hp2⟩ := hpres.2 l hl
    have hp1' : wSz s2.core.wvec l = fullWatchSize s l := hp1
    refine ⟨(hsz_o l hl hne).trans hp1, fun k hk => ?_⟩
    change wstk'[fullWatchOffCore s'.core l + k]? = _
    rw [hoff_o l hl hne]; exact (hother_st l hl hne k (hp1' ▸ hk)).trans (hp2 k hk)
  · intro k hk; change wstk'[fullWatchOffCore s'.core lit + k]? = _
    rw [hoff_l]; exact (hcopy k (hsz_lit2 ▸ hk)).trans ((hpres.2 lit hlit).2 k hk)
  · change wstk'[fullWatchOffCore s'.core lit + fullWatchSizeCore s.core lit]? = _
    rw [hoff_l, ← hsz_lit2]; exact hat0
  · intro hc2
    change wstk'[fullWatchOffCore s'.core lit + fullWatchSizeCore s.core lit + 1]? = _
    rw [hoff_l, ← hsz_lit2]; exact hat1 hc2

theorem wpush_getElem_toNat {xs : List (BitVec 32)} {i j : Nat}
    (hi : i < xs.length) (hij : i = j) : (xs[i]'hi).toNat = (xs[j]?.getD 0#32).toNat := by
  subst hij; rw [List.getElem?_eq_getElem hi, Option.getD_some]

theorem bv64_eq_nat {x : BitVec 64} (n : Nat) (hn : n < 2 ^ 64)
    (h : x = BitVec.ofNat 64 n) : x.toNat = n := by
  have := congrArg BitVec.toNat h
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] using this

theorem bv64_ne_nat {x : BitVec 64} (n : Nat) (hn : n < 2 ^ 64)
    (h : x ≠ BitVec.ofNat 64 n) : x.toNat ≠ n :=
  fun hto => h (BitVec.eq_of_toNat_eq
    (by simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] using hto))

abbrev wpOp1 {t r : Ty} (code : OpCode [t] [r]) (a : Arg Val t) : Op Val [r] :=
  { sig := [t], code := code, args := (a, ()) }

abbrev wpOp2 {t r : Ty} (code : OpCode [t, t] [r]) (a b : Arg Val t) : Op Val [r] :=
  { sig := [t, t], code := code, args := (a, b, ()) }

abbrev eHdrLd (h : Val i64) (off : BitVec 64)
    (k : Val i64 → Expr Val Cont [Ty.bool]) : Expr Val Cont [Ty.bool] :=
  Expr.let_ (wpOp2 (.add i64) (Arg.var h) (Arg.imm off)) fun p => Expr.load i64 (Arg.var p.fst) k

abbrev eHdrSt (h : Val i64) (off : BitVec 64) (v : Arg Val i64)
    (k : Expr Val Cont [Ty.bool]) : Expr Val Cont [Ty.bool] :=
  Expr.let_ (wpOp2 (.add i64) (Arg.var h) (Arg.imm off)) fun p =>
  Expr.store (t := i64) v (Arg.var p.fst) k

abbrev eIdx4 (base idx : Val i64) (k : Val i64 → Expr Val Cont [Ty.bool]) :
    Expr Val Cont [Ty.bool] :=
  Expr.let_ (wpOp2 (.mul i64) (Arg.var idx) (Arg.imm 4)) fun p1 =>
  Expr.let_ (wpOp2 (.add i64) (Arg.var base) (Arg.var p1.fst)) fun p2 => k p2.fst

abbrev eAddIdx4 (base a : Val i64) (b : Arg Val i64)
    (k : Val i64 → Expr Val Cont [Ty.bool]) : Expr Val Cont [Ty.bool] :=
  Expr.let_ (wpOp2 (.add i64) (Arg.var a) b) fun p => eIdx4 base p.fst k

abbrev eLit2Addr (pWvec : Val i64) (lit : Val i32)
    (k : Val i64 → Expr Val Cont [Ty.bool]) : Expr Val Cont [Ty.bool] :=
  Expr.let_ (wpOp1 (.zext 32 64) (Arg.var lit)) fun p1 =>
  Expr.let_ (wpOp1 (.sext 32 64) (Arg.imm 1)) fun p2 =>
  Expr.let_ (wpOp2 (.shl i64) (Arg.var p1.fst) (Arg.var p2.fst)) fun p3 => eIdx4 pWvec p3.fst k

abbrev eLit2p1Addr (pWvec : Val i64) (lit : Val i32)
    (k : Val i64 → Expr Val Cont [Ty.bool]) : Expr Val Cont [Ty.bool] :=
  Expr.let_ (wpOp1 (.zext 32 64) (Arg.var lit)) fun p1 =>
  Expr.let_ (wpOp1 (.sext 32 64) (Arg.imm 1)) fun p2 =>
  Expr.let_ (wpOp2 (.shl i64) (Arg.var p1.fst) (Arg.var p2.fst)) fun p3 =>
  eAddIdx4 pWvec p3.fst (Arg.imm 1) k

abbrev WPushPost (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (lit w0 w1 cnt : Val i32) (Q : Post [Ty.bool]) : Prop :=
  ∀ (ok : Bool) (wvec' wstk' : List (BitVec 32)) (wlen' : Nat) (wusable' : BitVec 64)
      (wsort' : List (BitVec 32)) (m' : Mem 64),
    let s' : FullState :=
      { s with
        core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable' }
        scratch := { s.scratch with wsort := wsort' } }
    s'.LengthsOk c → WatchStackLayout s'.core →
    (∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat →
      fullWatchSize s' l = fullWatchSize s l ∧
      ∀ k < fullWatchSize s l,
        s'.core.wstk[fullWatchOff s' l + k]? = s.core.wstk[fullWatchOff s l + k]?) →
    (ok = true → lit.toNat < 2 * s.core.cur_vars ∧ (cnt.toNat = 1 ∨ cnt.toNat = 2) ∧
      fullWatchSize s' lit.toNat = fullWatchSize s lit.toNat + cnt.toNat ∧
      (∀ k < fullWatchSize s lit.toNat,
        s'.core.wstk[fullWatchOff s' lit.toNat + k]? =
          s.core.wstk[fullWatchOff s lit.toNat + k]?) ∧
      s'.core.wstk[fullWatchOff s' lit.toNat + fullWatchSize s lit.toNat]? = some w0 ∧
      (cnt.toNat = 2 →
        s'.core.wstk[fullWatchOff s' lit.toNat + fullWatchSize s lit.toNat + 1]? = some w1)) →
    (ok = false →
      (lit.toNat < 2 * s.core.cur_vars → fullWatchSize s' lit.toNat = fullWatchSize s lit.toNat ∧
        ∀ k < fullWatchSize s lit.toNat,
          s'.core.wstk[fullWatchOff s' lit.toNat + k]? =
            s.core.wstk[fullWatchOff s lit.toNat + k]?) ∧
      (2 * s.core.cur_vars ≤ lit.toNat ∨ (cnt.toNat ≠ 1 ∧ cnt.toNat ≠ 2) ∨
        s' = s ∨ wusable' = 0#64)) →
    (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-! ## 2. Relocation & Cases C / B -/

abbrev wpushRelocExpr (h pWvec pWstk offD szD ncapD cVal : Val i64)
    (lit w0 w1 cnt : Val i32) : Expr Val Cont [Ty.bool] :=
  eHdrLd h 56 fun ld_5 =>
  Expr.group (sig := [[i64]]) (fun Js => Blocks.cons (fun (p_32 : Tup Val [i64]) =>
    Expr.let_ (wpOp2 (.cmp .ult i64 .bool rfl) (Arg.var p_32.fst) (Arg.var szD)) fun p_33 =>
    Expr.jnz (Arg.var p_33.fst)
      (eAddIdx4 pWstk ld_5 (Arg.var p_32.fst) fun p3 =>
       eAddIdx4 pWstk offD (Arg.var p_32.fst) fun p_36 =>
       Expr.load i32 (Arg.var p_36) fun ld_v =>
       Expr.store (t := i32) (Arg.var ld_v) (Arg.var p3)
         (eAddIdx4 pWstk offD (Arg.var p_32.fst) fun p6 =>
          Expr.store (t := i32) (Arg.imm 0xFFFFFFFF#32) (Arg.var p6)
            (Expr.let_ (wpOp2 (.add i64) (Arg.var p_32.fst) (Arg.imm 1)) fun p7 =>
             Expr.jump Js.fst (Arg.var p7.fst, ()))))
      (eAddIdx4 pWstk ld_5 (Arg.var szD) fun p_36 =>
       Expr.store (t := i32) (Arg.var w0) (Arg.var p_36)
         (Expr.group (sig := [[]]) (fun _JsW => Blocks.cons (fun (_ : Tup Val []) =>
            Expr.let_ (wpOp2 (.add i64) (Arg.var szD) (Arg.var cVal)) fun p_38 =>
            Expr.group (sig := [[i64]]) (fun JsF => Blocks.cons (fun (p_39 : Tup Val [i64]) =>
              Expr.let_ (wpOp2 (.cmp .ult i64 .bool rfl) (Arg.var p_39.fst) (Arg.var ncapD))
                fun p_40 =>
              Expr.jnz (Arg.var p_40.fst)
                (eAddIdx4 pWstk ld_5 (Arg.var p_39.fst) fun q3 =>
                 Expr.store (t := i32) (Arg.imm 0xFFFFFFFF#32) (Arg.var q3)
                   (Expr.let_ (wpOp2 (.add i64) (Arg.var p_39.fst) (Arg.imm 1)) fun q4 =>
                    Expr.jump JsF.fst (Arg.var q4.fst, ())))
                (eLit2Addr pWvec lit fun p_45 =>
                 Expr.let_ (wpOp1 (.trunc 64 32) (Arg.var ld_5)) fun p_46 =>
                 Expr.store (t := i32) (Arg.var p_46.fst) (Arg.var p_45)
                   (eLit2p1Addr pWvec lit fun p_52 =>
                    Expr.let_ (wpOp2 (.add i64) (Arg.var szD) (Arg.var cVal)) fun p_53 =>
                    Expr.let_ (wpOp1 (.trunc 64 32) (Arg.var p_53.fst)) fun p_54 =>
                    Expr.store (t := i32) (Arg.var p_54.fst) (Arg.var p_52)
                      (eHdrLd h 464 fun ld_wu =>
                       Expr.let_ (wpOp2 (.add i64) (Arg.var ld_wu) (Arg.var szD)) fun p_56 =>
                       Expr.let_ (wpOp2 (.add i64) (Arg.var szD) (Arg.var cVal)) fun p_57 =>
                       Expr.let_ (wpOp2 (.sub i64) (Arg.var ncapD) (Arg.var p_57.fst)) fun p_58 =>
                       Expr.let_ (wpOp2 (.add i64) (Arg.var p_56.fst) (Arg.var p_58.fst))
                         fun p_59 =>
                       eHdrSt h 464 (Arg.var p_59.fst)
                         (Expr.let_ (wpOp2 (.add i64) (Arg.var ld_5) (Arg.var ncapD)) fun p_61 =>
                          eHdrSt h 56 (Arg.var p_61.fst) (Expr.ret (Arg.imm true, ())))))))
              Blocks.nil) fun JsF => Expr.jump JsF.fst (Arg.var p_38.fst, ())) Blocks.nil)
            fun JsW =>
            Expr.let_ (wpOp2 (.cmp .eq i32 .bool rfl) (Arg.var cnt) (Arg.imm 2)) fun p_37 =>
            Expr.jnz (Arg.var p_37.fst)
              (Expr.let_ (wpOp2 (.add i64) (Arg.var ld_5) (Arg.var szD)) fun p_38 =>
               eAddIdx4 pWstk p_38.fst (Arg.imm 1) fun p_41 =>
               Expr.store (t := i32) (Arg.var w1) (Arg.var p_41) (Expr.jump JsW.fst ()))
              (Expr.jump JsW.fst ())))) Blocks.nil)
    fun Js => Expr.jump Js.fst (Arg.imm 0, ())

theorem wpush_reloc_step8_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost} {c : FullCfg}
    {s : FullState} {R : Mem 64 → Prop} {wvecD wstkD wsortD : List (BitVec 32)} {wlenD : Nat}
    {wusD offD szD ncapD : BitVec 64} {lit w0 w1 cnt : Val i32} {mD : Mem 64}
    (hlit_lt : lit.toNat < 2 * s.core.cur_vars) (hcnt12 : cnt.toNat = 1 ∨ cnt.toNat = 2)
    (hw0 : cnt.toNat = 1 → w0 ≠ 0xFFFFFFFF#32)
    (hw1 : cnt.toNat = 2 → w0 ≠ 0xFFFFFFFF#32 ∧ w1 ≠ 0xFFFFFFFF#32)
    (hwd1 : 1 ≤ wlenD)
    (hlenD : FullState.LengthsOk c
      { s with
        core := { s.core with wvec := wvecD, wstk := wstkD, wlen := wlenD, wusable := wusD }
        scratch := { s.scratch with wsort := wsortD } })
    (hlayD : WatchStackLayout
      { s.core with wvec := wvecD, wstk := wstkD, wlen := wlenD, wusable := wusD })
    (hpresD : WatchPresAll s
      { s with
        core := { s.core with wvec := wvecD, wstk := wstkD, wlen := wlenD, wusable := wusD }
        scratch := { s.scratch with wsort := wsortD } })
    (hoffD : offD.toNat = wOff wvecD lit.toNat) (hszD : szD.toNat = wSz wvecD lit.toNat)
    (hnc_ge : szD.toNat + cnt.toNat ≤ ncapD.toNat) (hnc_fit : ncapD.toNat ≤ c.wcap - wlenD)
    (hmD : (FullMem c
      { s with
        core := { s.core with wvec := wvecD, wstk := wstkD, wlen := wlenD, wusable := wusD }
        scratch := { s.scratch with wsort := wsortD } } ⋆ R) mD)
    (hQ : WPushPost c s R lit w0 w1 cnt Q) :
    wp Γ Q X (wpushRelocExpr c.hdr c.pWvec c.pWstk offD szD ncapD (cnt.setWidth 64) lit w0 w1 cnt)
      mD := by
  have hmx := c.hmaxv; have hwcap := c.hwcap; unfold dimacsBound at hmx hwcap
  have hcoD := hlenD.core_ok
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hcoD.cur_vars_le
  have hwvlD : wvecD.length = 4 * c.max_vars := hcoD.wvec_len
  have hwslD : wstkD.length = c.wcap := hcoD.wstk_len_arr
  have hwleD : wlenD ≤ c.wcap := hcoD.wlen_le
  have hlit2 := bv64_lit2 (lit := lit); have hlit2p1 := bv64_lit2p1 (lit := lit)
  have hoffD_le : offD.toNat + szD.toNat ≤ wlenD := by
    have hbl := hlayD.bounds lit.toNat (hpresD.1 ▸ hlit_lt)
    change wOff wvecD lit.toNat + wSz wvecD lit.toNat ≤ wlenD at hbl; omega
  have hdst_eq : (BitVec.ofNat 64 wlenD).toNat = wlenD := bv64_ofNat_toNat (by omega)
  dsimp only [wpushRelocExpr, eHdrLd, eHdrSt, eIdx4, eAddIdx4, eLit2Addr, eLit2p1Addr]
  c0_to_group
  refine wp_loop_inv (ts := [i64])
    (fun (k, ()) mK => k.toNat ≤ szD.toNat ∧ ∃ wstkK : List (BitVec 32), wstkK.length = c.wcap ∧
      (∀ j < 2 * s.core.cur_vars, j ≠ lit.toNat → ∀ r < wSz wvecD j,
        wstkK[wOff wvecD j + r]? = wstkD[wOff wvecD j + r]?) ∧
      (∀ r < k.toNat, wstkK[wlenD + r]? = wstkD[offD.toNat + r]?) ∧
      (∀ r, k.toNat ≤ r → r < szD.toNat → wstkK[offD.toNat + r]? = wstkD[offD.toNat + r]?) ∧
      (FullMem c { s with
        core := { s.core with wvec := wvecD, wstk := wstkK, wlen := wlenD, wusable := wusD }
        scratch := { s.scratch with wsort := wsortD } } ⋆ R) mK)
    (fun (k, ()) _ => szD.toNat - k.toNat) (fun JK hLoopK => ?_) ?_
  · c0_usteps; exact hLoopK _ _ ⟨by simp, wstkD, hwslD, fun _ _ _ _ _ => rfl,
      fun _ hr => by simp at hr, fun _ _ _ => rfl, hmD⟩
  · rintro JK ⟨k, ⟨⟩⟩ mK ⟨hk_le, wstkK, hwsK, hothK, hcopK, hsrcK, hmK⟩ hLoopK; clear hmD
    c0_to_group
    · have hk_lt : k.toNat < szD.toNat := by c0_bound
      have hkp1 : (k + 1).toNat = k.toNat + 1 := bv64_add1_no_ovf (by omega)
      have hdk : (BitVec.ofNat 64 wlenD + k).toNat = wlenD + k.toNat := by
        rw [BitVec.toNat_add, hdst_eq]; omega
      have hok_eq : (offD + k).toNat = offD.toNat + k.toNat := bv64_add_no_ovf (by omega)
      c0_usteps
      refine hLoopK _ _ (by dsimp only; omega)
        ⟨by omega, _, by rw [List.length_set, List.length_set, hwsK], ?_, ?_, ?_, hm⟩
      · intro j hj hne r hr
        have hbj := hlayD.bounds j (hpresD.1 ▸ hj)
        change wOff wvecD j + wSz wvecD j ≤ wlenD at hbj
        have hdj := hlayD.disjoint j lit.toNat (hpresD.1 ▸ hj) (hpresD.1 ▸ hlit_lt) hne
          (by change 0 < wSz wvecD j; omega) (by change 0 < wSz wvecD lit.toNat; omega)
        change wOff wvecD j + wSz wvecD j ≤ wOff wvecD lit.toNat ∨
          wOff wvecD lit.toNat + wSz wvecD lit.toNat ≤ wOff wvecD j at hdj
        rw [List.getElem?_set_ne (by rw [hok_eq]; rcases hdj with hd | hd <;> omega),
            List.getElem?_set_ne (by rw [hdk]; omega)]; exact hothK j hj hne r hr
      · intro r hr; by_cases hrk : r = k.toNat
        · subst hrk; rw [List.getElem?_set_ne (by rw [hok_eq]; omega), ← hdk,
            List.getElem?_set_self (by rw [hdk]; omega), ← List.getElem?_eq_getElem (by omega),
            hok_eq]; exact hsrcK k.toNat (by omega) hk_lt
        · rw [List.getElem?_set_ne (by rw [hok_eq]; omega),
            List.getElem?_set_ne (by rw [hdk]; omega)]; exact hcopK r (by omega)
      · intro r hr1 hr2
        rw [List.getElem?_set_ne (by rw [hok_eq]; omega),
            List.getElem?_set_ne (by rw [hdk]; omega)]; exact hsrcK r (by omega) hr2
    · have hk_eq : k.toNat = szD.toNat := by
        have : ¬ (k.toNat < szD.toNat) := by c0_bound
        omega
      clear hLoopK JK hsrcK
      have hdsz : (BitVec.ofNat 64 wlenD + szD).toNat = wlenD + szD.toNat := by
        rw [BitVec.toNat_add, hdst_eq]; omega
      have hdszp1 : ((BitVec.ofNat 64 wlenD + szD) + 1).toNat = wlenD + szD.toNat + 1 := by
        rw [BitVec.toNat_add, hdsz]; simp; omega
      c0_to_group
      refine wp_join_group
        (fun _ mW => ∃ wstkW : List (BitVec 32), wstkW.length = c.wcap ∧
          (∀ idx < wlenD, wstkW[idx]? = wstkK[idx]?) ∧
          (∀ r < szD.toNat, wstkW[wlenD + r]? = wstkD[offD.toNat + r]?) ∧
          wstkW[wlenD + szD.toNat]? = some w0 ∧
          (cnt.toNat = 2 → wstkW[wlenD + szD.toNat + 1]? = some w1) ∧
          (FullMem c { s with
            core := { s.core with wvec := wvecD, wstk := wstkW, wlen := wlenD, wusable := wusD }
            scratch := { s.scratch with wsort := wsortD } } ⋆ R) mW) ?_ ?_
      · rintro _ _ mW ⟨wstkW, hwsW, hpreW, hcopW, hat0W, hat1W, hmW⟩; clear hwsK hcopK
        c0_to_group
        refine wp_loop_inv (ts := [i64])
          (fun (kf, ()) mF => szD.toNat + cnt.toNat ≤ kf.toNat ∧ kf.toNat ≤ ncapD.toNat ∧
            ∃ wstkF : List (BitVec 32), wstkF.length = c.wcap ∧
              (∀ idx < wlenD + szD.toNat + cnt.toNat, wstkF[idx]? = wstkW[idx]?) ∧
              (FullMem c { s with
                core := { s.core with wvec := wvecD, wstk := wstkF, wlen := wlenD,
                                      wusable := wusD }
                scratch := { s.scratch with wsort := wsortD } } ⋆ R) mF)
          (fun (kf, ()) _ => ncapD.toNat - kf.toNat) (fun JF hLoopF => ?_) ?_
        · c0_usteps
          have hsc : (szD + cnt.setWidth 64).toNat = szD.toNat + cnt.toNat := by
            rw [BitVec.toNat_add, zext_toNat _ (by decide)]; omega
          exact hLoopF _ _ ⟨by omega, by omega, wstkW, hwsW, fun _ _ => rfl, hmW⟩
        · rintro JF ⟨kf, ⟨⟩⟩ mF ⟨hkf_ge, hkf_le, wstkF, hwsF, hpreF, hmF⟩ hLoopF; clear hmW
          c0_usteps
          · have hkf_lt : kf.toNat < ncapD.toNat := by c0_bound
            have hdkf : (BitVec.ofNat 64 wlenD + kf).toNat = wlenD + kf.toNat := by
              rw [BitVec.toNat_add, hdst_eq]; omega
            have hkfp1 : (kf + 1).toNat = kf.toNat + 1 := bv64_add1_no_ovf (by omega)
            refine hLoopF _ _ (by dsimp only; omega)
              ⟨by omega, by omega, _, by rw [List.length_set, hwsF], fun idx hidx => by
                rw [hdkf, List.getElem?_set_ne (by omega)]; exact hpreF idx hidx, hm⟩
          · have hdst32 := bv32_trunc_ofNat (n := wlenD) (by omega)
            have hsz32 := bv32_trunc_add (a := szD) (b := cnt) (by omega)
            have hwlen_new : (BitVec.ofNat 64 wlenD + ncapD).toNat = wlenD + ncapD.toNat := by
              rw [BitVec.toNat_add, hdst_eq]; omega
            have hev := wvec_set_even_u (wvec := wvecD) (l := lit.toNat)
              (v := (BitVec.ofNat 64 wlenD).setWidth 32) (by omega)
            have hod := wvec_set_odd_u (wvec := wvecD.set (2 * lit.toNat)
                ((BitVec.ofNat 64 wlenD).setWidth 32)) (l := lit.toNat)
              (v := (szD + cnt.setWidth 64).setWidth 32) (by rw [List.length_set]; omega)
            have hfin := wpush_finalize (s := s)
              (s2 := { s with
                core := { s.core with wvec := wvecD, wstk := wstkD, wlen := wlenD,
                                      wusable := wusD }
                scratch := { s.scratch with wsort := wsortD } })
              (lit := lit.toNat) (cnt := cnt.toNat) (dst := wlenD)
              (wlen' := (BitVec.ofNat 64 wlenD + ncapD).toNat)
              (wvec' := (wvecD.set (lit.setWidth 64 <<< (1 : Nat)).toNat
                  ((BitVec.ofNat 64 wlenD).setWidth 32)).set
                  ((lit.setWidth 64 <<< (1 : Nat) + 1).toNat)
                  ((szD + cnt.setWidth 64).setWidth 32))
              (wstk' := wstkF) (wsort' := wsortD) hlayD hpresD hlit_lt hcnt12 hw0 hw1
              (by dsimp only; omega) hwd1 (by dsimp only; omega)
              (fun j hj hne => by
                rw [wOff, wSz, hlit2, hlit2p1, (hod j).1, (hev j).2.1 hne, (hod j).2.1 hne,
                  (hev j).1]; exact ⟨rfl, rfl⟩)
              (by rw [wOff, hlit2, hlit2p1, (hod lit.toNat).1, (hev lit.toNat).2.2,
                Option.getD_some, hdst32])
              (by rw [wSz, hlit2, hlit2p1, (hod lit.toNat).2.2, Option.getD_some, hsz32, hszD])
              (fun j hj _ _ => Or.inl (hlayD.bounds j (hpresD.1 ▸ hj)))
              (fun j hj hne r hr => by
                have hbj := hlayD.bounds j (hpresD.1 ▸ hj)
                change wOff wvecD j + wSz wvecD j ≤ wlenD at hbj
                dsimp only at hr ⊢; rw [hpreF _ (by omega), hpreW _ (by omega)]
                exact hothK j hj hne r hr)
              (fun r hr => by
                dsimp only at hr ⊢; rw [hpreF _ (by omega), hcopW r (by omega), hoffD])
              (by dsimp only; rw [hpreF _ (by omega), ← hszD]; exact hat0W)
              (fun hc2 => by dsimp only; rw [hpreF _ (by omega), ← hszD]; exact hat1W hc2)
              (wusD + szD + (ncapD - (szD + cnt.setWidth 64)))
            exact hQ true _ wstkF _ _ wsortD _
              { core_ok := { hcoD with wvec_len := by rw [List.length_set, List.length_set, hwvlD],
                                       wstk_len_arr := hwsF, wlen_le := by dsimp only; omega }
                scratch_ok := hlenD.scratch_ok }
              hfin.1 hfin.2.1 (fun _ => ⟨hlit_lt, hcnt12, hfin.2.2.1, hfin.2.2.2.1,
                hfin.2.2.2.2.1, hfin.2.2.2.2.2⟩) (fun h => by cases h) hm
      · intro JW hJW; clear hQ hothK hlenD hcoD hlayD hpresD; c0_split
        · have hc2 := bv32_eq_nat 2 (by decide) hc; c0_usteps
          refine hJW _ _ ⟨_, by rw [List.length_set, List.length_set, hwsK],
            fun idx hidx => by
              rw [hdszp1, hdsz, List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)],
            fun r hr => by
              rw [hdszp1, hdsz, List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
              exact hcopK r (by omega),
            by rw [hdszp1, hdsz, List.getElem?_set_ne (by omega),
              List.getElem?_set_self (by omega)],
            fun _ => by rw [hdszp1, List.getElem?_set_self (by rw [List.length_set]; omega)], hm⟩
        · c0_usteps; have hne2 := bv32_ne_nat 2 (by decide) hc
          refine hJW _ _ ⟨_, by rw [List.length_set, hwsK],
            fun idx hidx => by rw [hdsz, List.getElem?_set_ne (by omega)],
            fun r hr => by rw [hdsz, List.getElem?_set_ne (by omega)]; exact hcopK r (by omega),
            by rw [hdsz, List.getElem?_set_self (by omega)], fun hc2 => absurd hc2 hne2, hm⟩

abbrev wpushCaseCExpr (h pWvec pWstk endVal sz cVal : Val i64)
    (lit w0 w1 cnt : Val i32) (JC : Cont []) : Expr Val Cont [Ty.bool] :=
  Expr.let_ (wpOp2 (.add i64) (Arg.var endVal) (Arg.var cVal)) fun p_28 =>
  eHdrLd h 56 fun ld_5 =>
  Expr.let_ (wpOp2 (.cmp .ule i64 .bool rfl) (Arg.var p_28.fst) (Arg.var ld_5)) fun p_30 =>
  Expr.jnz (Arg.var p_30.fst)
    (eIdx4 pWstk endVal fun p_32 =>
     Expr.load i32 (Arg.var p_32) fun ld_6 =>
     Expr.let_ (wpOp2 (.cmp .eq i32 .bool rfl) (Arg.var ld_6) (Arg.imm 0xFFFFFFFF#32)) fun p_33 =>
     Expr.jnz (Arg.var p_33.fst)
       (Expr.group (sig := [[]]) (fun _Js => Blocks.cons (fun (_ : Tup Val []) =>
         eIdx4 pWstk endVal fun p_36 =>
         Expr.store (t := i32) (Arg.var w0) (Arg.var p_36)
           (Expr.group (sig := [[]]) (fun _Js2 => Blocks.cons (fun (_ : Tup Val []) =>
             eLit2p1Addr pWvec lit fun p_43 =>
             Expr.let_ (wpOp2 (.add i64) (Arg.var sz) (Arg.var cVal)) fun p_44 =>
             Expr.let_ (wpOp1 (.trunc 64 32) (Arg.var p_44.fst)) fun p_45 =>
             Expr.store (t := i32) (Arg.var p_45.fst) (Arg.var p_43)
               (Expr.group (sig := [[]]) (fun _Js3 =>
                 Blocks.cons (fun (_ : Tup Val []) => Expr.ret (Arg.imm true, ())) Blocks.nil)
                 fun Js3 =>
                 eHdrLd h 464 fun ld =>
                 Expr.let_ (wpOp2 (.cmp .uge i64 .bool rfl) (Arg.var ld) (Arg.var cVal))
                   fun p_47 =>
                 Expr.jnz (Arg.var p_47.fst)
                   (eHdrLd h 464 fun ld =>
                    Expr.let_ (wpOp2 (.sub i64) (Arg.var ld) (Arg.var cVal)) fun p_49 =>
                    eHdrSt h 464 (Arg.var p_49.fst) (Expr.jump Js3.fst ()))
                   (Expr.jump Js3.fst ()))) Blocks.nil) fun Js2 =>
             Expr.let_ (wpOp2 (.cmp .eq i32 .bool rfl) (Arg.var cnt) (Arg.imm 2)) fun p_37 =>
             Expr.jnz (Arg.var p_37.fst)
               (eAddIdx4 pWstk endVal (Arg.imm 1) fun p_40 =>
                Expr.store (t := i32) (Arg.var w1) (Arg.var p_40) (Expr.jump Js2.fst ()))
               (Expr.jump Js2.fst ()))) Blocks.nil) fun Js_1 =>
         Expr.let_ (wpOp2 (.cmp .eq i32 .bool rfl) (Arg.var cnt) (Arg.imm 1)) fun p =>
         Expr.jnz (Arg.var p.fst) (Expr.jump Js_1.fst ())
           (eAddIdx4 pWstk endVal (Arg.imm 1) fun p =>
            Expr.load i32 (Arg.var p) fun ld =>
            Expr.let_ (wpOp2 (.cmp .eq i32 .bool rfl) (Arg.var ld) (Arg.imm 0xFFFFFFFF#32))
              fun p =>
            Expr.jnz (Arg.var p.fst) (Expr.jump Js_1.fst ()) (Expr.jump JC ())))
       (Expr.jump JC ()))
    (Expr.jump JC ())

theorem wpush_caseC_step8_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost} {c : FullCfg}
    {s : FullState} {R : Mem 64 → Prop} {wvec1 wstk1 wsort1 : List (BitVec 32)} {wlen1 : Nat}
    {wus1 endVal : Val i64} {sz32 lit w0 w1 cnt : Val i32} {m1 : Mem 64} {JC : Cont []}
    (hlit_lt : lit.toNat < 2 * s.core.cur_vars) (hcnt12 : cnt.toNat = 1 ∨ cnt.toNat = 2)
    (hw0 : cnt.toNat = 1 → w0 ≠ 0xFFFFFFFF#32)
    (hw1 : cnt.toNat = 2 → w0 ≠ 0xFFFFFFFF#32 ∧ w1 ≠ 0xFFFFFFFF#32)
    (hoff1_pos : 1 ≤ wOff wvec1 lit.toNat)
    (hlen1 : FullState.LengthsOk c
      { s with
        core := { s.core with wvec := wvec1, wstk := wstk1, wlen := wlen1, wusable := wus1 }
        scratch := { s.scratch with wsort := wsort1 } })
    (hlay1 : WatchStackLayout
      { s.core with wvec := wvec1, wstk := wstk1, wlen := wlen1, wusable := wus1 })
    (hpres1 : WatchPresAll s
      { s with
        core := { s.core with wvec := wvec1, wstk := wstk1, wlen := wlen1, wusable := wus1 }
        scratch := { s.scratch with wsort := wsort1 } })
    (hend_eq : endVal.toNat = wOff wvec1 lit.toNat + wSz wvec1 lit.toNat)
    (hsz1 : sz32.toNat = wSz wvec1 lit.toNat)
    (hm1 : (FullMem c
      { s with
        core := { s.core with wvec := wvec1, wstk := wstk1, wlen := wlen1, wusable := wus1 }
        scratch := { s.scratch with wsort := wsort1 } } ⋆ R) m1)
    (hJC : JC () m1) (hQ : WPushPost c s R lit w0 w1 cnt Q) :
    wp Γ Q X (wpushCaseCExpr c.hdr c.pWvec c.pWstk endVal (sz32.setWidth 64)
      (cnt.setWidth 64) lit w0 w1 cnt JC) m1 := by
  have hmx := c.hmaxv; have hwcap := c.hwcap; unfold dimacsBound at hmx hwcap
  have hco1 := hlen1.core_ok
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hco1.cur_vars_le
  have hwvl : wvec1.length = 4 * c.max_vars := hco1.wvec_len
  have hwsl1 : wstk1.length = c.wcap := hco1.wstk_len_arr
  have hwle1 : wlen1 ≤ c.wcap := hco1.wlen_le
  have hoff1_le : wOff wvec1 lit.toNat + wSz wvec1 lit.toNat ≤ wlen1 :=
    hlay1.bounds lit.toNat (hpres1.1 ▸ hlit_lt)
  have hlit2p1 := bv64_lit2p1 (lit := lit)
  dsimp only [wpushCaseCExpr, eHdrLd, eHdrSt, eIdx4, eAddIdx4, eLit2p1Addr]
  c0_split
  · have hend_c_le : wOff wvec1 lit.toNat + wSz wvec1 lit.toNat + cnt.toNat ≤ wlen1 := by omega
    clear hc; c0_to_group
    · have hs0 : wstk1[wOff wvec1 lit.toNat + wSz wvec1 lit.toNat]? =
          some 0xFFFFFFFF#32 := by
        rw [List.getElem?_eq_getElem (by omega)]; congr 1
        have hget : wstk1[wOff wvec1 lit.toNat + wSz wvec1 lit.toNat]'(by omega) =
            wstk1[endVal.toNat]'(by omega) := by congr 1; exact hend_eq.symm
        rw [hget]; exact hc
      clear hc
      refine wp_join_group (fun _ mW => (cnt.toNat = 2 →
        wstk1[wOff wvec1 lit.toNat + wSz wvec1 lit.toNat + 1]? =
          some 0xFFFFFFFF#32) ∧ m1 = mW) ?_ ?_
      · rintro _ _ mW ⟨hs1, hmW⟩; rcases hmW with rfl
        have hdisjC := wpush_sentinel_disjoint hlay1 (hpres1.1 ▸ hlit_lt) hcnt12 hs0 hs1
        c0_to_group
        refine wp_join_group (fun _ mW2 => ∃ wstkW : List (BitVec 32), wstkW.length = c.wcap ∧
          (∀ idx, idx ≠ wOff wvec1 lit.toNat + wSz wvec1 lit.toNat →
            (cnt.toNat = 2 →
              idx ≠ wOff wvec1 lit.toNat + wSz wvec1 lit.toNat + 1) →
            wstkW[idx]? = wstk1[idx]?) ∧
          wstkW[wOff wvec1 lit.toNat + wSz wvec1 lit.toNat]? = some w0 ∧
          (cnt.toNat = 2 →
            wstkW[wOff wvec1 lit.toNat + wSz wvec1 lit.toNat + 1]? = some w1) ∧
          (FullMem c { s with
            core := { s.core with wvec := wvec1, wstk := wstkW, wlen := wlen1, wusable := wus1 }
            scratch := { s.scratch with wsort := wsort1 } } ⋆ R) mW2) ?_ ?_
        · rintro _ _ mW2 ⟨wstkW, hwsW, hpreW, hat0W, hat1W, hmW2⟩
          have hsz_new : ((sz32.setWidth 64 + cnt.setWidth 64).setWidth 32).toNat =
              wSz wvec1 lit.toNat + cnt.toNat := by
            have h := bv32_trunc_add (a := sz32.setWidth 64) (b := cnt)
              (by rw [zext_toNat sz32 (by decide), hsz1]; omega)
            rwa [zext_toNat sz32 (by decide), hsz1] at h
          have hod := wvec_set_odd_u (wvec := wvec1) (l := lit.toNat)
            (v := (sz32.setWidth 64 + cnt.setWidth 64).setWidth 32) (by omega)
          have hfin := wpush_finalize (s := s)
            (s2 := { s with
              core := { s.core with wvec := wvec1, wstk := wstk1, wlen := wlen1, wusable := wus1 }
              scratch := { s.scratch with wsort := wsort1 } })
            (lit := lit.toNat) (cnt := cnt.toNat) (dst := wOff wvec1 lit.toNat)
            (wlen' := wlen1)
            (wvec' := wvec1.set ((lit.setWidth 64 <<< (1 : Nat) + 1).toNat)
              ((sz32.setWidth 64 + cnt.setWidth 64).setWidth 32))
            (wstk' := wstkW) (wsort' := wsort1)
            hlay1 hpres1 hlit_lt hcnt12 hw0 hw1 (Nat.le_refl _) hoff1_pos
            (by dsimp only; omega)
            (fun j hj hne => by
              rw [wOff, wSz, hlit2p1, (hod j).1, (hod j).2.1 hne]; exact ⟨rfl, rfl⟩)
            (by rw [wOff, hlit2p1, (hod lit.toNat).1])
            (by rw [wSz, hlit2p1, (hod lit.toNat).2.2, Option.getD_some, hsz_new])
            (fun j hj hne hszj => hdisjC j (hpres1.1 ▸ hj) hne hszj)
            (fun j hj hne k hk => by
              dsimp only at hk ⊢
              have hd := hdisjC j (hpres1.1 ▸ hj) hne (by change 0 < wSz wvec1 j; omega)
              change wOff wvec1 j + wSz wvec1 j ≤ wOff wvec1 lit.toNat ∨
                wOff wvec1 lit.toNat + (wSz wvec1 lit.toNat + cnt.toNat) ≤
                  wOff wvec1 j at hd
              exact hpreW _ (by rcases hd with hd | hd <;> omega)
                (fun _ => by rcases hd with hd | hd <;> omega))
            (fun k hk => by dsimp only at hk ⊢; exact hpreW _ (by omega) (fun _ => by omega))
            hat0W hat1W
          c0_usteps
          · exact hQ true _ wstkW wlen1 (wus1 - cnt.setWidth 64) wsort1 _
              { core_ok := { hco1 with wvec_len := by rw [List.length_set, hwvl],
                                       wstk_len_arr := hwsW, wlen_le := hwle1 }
                scratch_ok := hlen1.scratch_ok }
              (hfin _).1 (hfin _).2.1 (fun _ => ⟨hlit_lt, hcnt12, (hfin _).2.2.1,
                (hfin _).2.2.2.1, (hfin _).2.2.2.2.1, (hfin _).2.2.2.2.2⟩)
              (fun h => by cases h) hm
          · exact hQ true _ wstkW wlen1 wus1 wsort1 _
              { core_ok := { hco1 with wvec_len := by rw [List.length_set, hwvl],
                                       wstk_len_arr := hwsW, wlen_le := hwle1 }
                scratch_ok := hlen1.scratch_ok }
              (hfin _).1 (hfin _).2.1 (fun _ => ⟨hlit_lt, hcnt12, (hfin _).2.2.1,
                (hfin _).2.2.2.1, (hfin _).2.2.2.2.1, (hfin _).2.2.2.2.2⟩)
              (fun h => by cases h) hm
        · intro JW hJW; clear hQ
          have hend_p1 : (endVal + 1).toNat =
              wOff wvec1 lit.toNat + wSz wvec1 lit.toNat + 1 := by
            rw [BitVec.toNat_add, hend_eq]; simp; omega
          c0_split
          · have hc2 := bv32_eq_nat 2 (by decide) hc; c0_usteps
            refine hJW _ _ ⟨_, by rw [List.length_set, List.length_set, hwsl1],
              fun idx hne0 hne1 => by
                rw [hend_p1, hend_eq, List.getElem?_set_ne (by have := hne1 hc2; omega),
                  List.getElem?_set_ne (by omega)],
              by rw [hend_p1, hend_eq, List.getElem?_set_ne (by omega),
                List.getElem?_set_self (by omega)],
              fun _ => by rw [hend_p1, List.getElem?_set_self (by rw [List.length_set]; omega)], hm⟩
          · c0_usteps; have hne2 := bv32_ne_nat 2 (by decide) hc
            refine hJW _ _ ⟨_, by rw [List.length_set, hwsl1],
              fun idx hne0 _ => by rw [hend_eq, List.getElem?_set_ne (by omega)],
              by rw [hend_eq, List.getElem?_set_self (by omega)], fun hc2 => absurd hc2 hne2, hm⟩
      · intro Jc2 hJc2; c0_split
        · c0_usteps
          exact hJc2 _ _ ⟨fun hc2 => by have := bv32_eq_nat 1 (by decide) hc; omega, rfl⟩
        · have hc2 : cnt.toNat = 2 := by have := bv32_ne_nat 1 (by decide) hc; omega
          clear hc
          have hend_p1 : (endVal + 1).toNat =
              wOff wvec1 lit.toNat + wSz wvec1 lit.toNat + 1 := by
            rw [BitVec.toNat_add, hend_eq]; simp; omega
          c0_usteps
          · exact hJc2 _ _ ⟨fun _ => by
              rw [List.getElem?_eq_getElem (by omega)]; congr 1
              have hidx : (endVal.toNat + (1 : Val i64).toNat) % 2 ^ 64 =
                  wOff wvec1 lit.toNat + wSz wvec1 lit.toNat + 1 := by
                rw [hend_eq]; simp; omega
              have hget : wstk1[wOff wvec1 lit.toNat + wSz wvec1 lit.toNat + 1]'(by
                  omega) = wstk1[(endVal.toNat + (1 : Val i64).toNat) % 2 ^ 64]'(by
                    rw [hidx]; omega) := by congr 1; exact hidx.symm
              rw [hget]; exact hc, rfl⟩
          · exact hJC
    · exact hJC
  · c0_usteps; exact hJC

abbrev wpushCaseBExpr (h pWvec pWstk wcap endVal sz cVal : Val i64)
    (lit w0 w1 cnt : Val i32) (JB : Cont []) : Expr Val Cont [Ty.bool] :=
  eHdrLd h 56 fun ld_5 =>
  Expr.let_ (wpOp2 (.cmp .eq i64 .bool rfl) (Arg.var endVal) (Arg.var ld_5)) fun p_28 =>
  Expr.jnz (Arg.var p_28.fst)
    (eHdrLd h 56 fun ld_6 =>
     Expr.let_ (wpOp2 (.sub i64) (Arg.var wcap) (Arg.var ld_6)) fun p_30 =>
     Expr.let_ (wpOp2 (.cmp .ule i64 .bool rfl) (Arg.var cVal) (Arg.var p_30.fst)) fun p_31 =>
     Expr.jnz (Arg.var p_31.fst)
       (eIdx4 pWstk endVal fun p_33 =>
        Expr.store (t := i32) (Arg.var w0) (Arg.var p_33)
          (Expr.group (sig := [[]]) (fun _Js => Blocks.cons (fun (_ : Tup Val []) =>
            eLit2p1Addr pWvec lit fun p_40 =>
            Expr.let_ (wpOp2 (.add i64) (Arg.var sz) (Arg.var cVal)) fun p_41 =>
            Expr.let_ (wpOp1 (.trunc 64 32) (Arg.var p_41.fst)) fun p_42 =>
            Expr.store (t := i32) (Arg.var p_42.fst) (Arg.var p_40)
              (Expr.let_ (wpOp2 (.add i64) (Arg.var endVal) (Arg.var cVal)) fun p_43 =>
               eHdrSt h 56 (Arg.var p_43.fst) (Expr.ret (Arg.imm true, ())))) Blocks.nil)
            fun Js =>
            Expr.let_ (wpOp2 (.cmp .eq i32 .bool rfl) (Arg.var cnt) (Arg.imm 2)) fun p_34 =>
            Expr.jnz (Arg.var p_34.fst)
              (eAddIdx4 pWstk endVal (Arg.imm 1) fun p_37 =>
               Expr.store (t := i32) (Arg.var w1) (Arg.var p_37) (Expr.jump Js.fst ()))
              (Expr.jump Js.fst ())))
       (Expr.jump JB ()))
    (Expr.jump JB ())

theorem wpush_caseB_step8_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost} {c : FullCfg}
    {s : FullState} {R : Mem 64 → Prop} {wvec1 wstk1 wsort1 : List (BitVec 32)} {wlen1 : Nat}
    {wus1 endVal : Val i64} {sz32 lit w0 w1 cnt : Val i32} {m1 : Mem 64} {JB : Cont []}
    (hlit_lt : lit.toNat < 2 * s.core.cur_vars) (hcnt12 : cnt.toNat = 1 ∨ cnt.toNat = 2)
    (hw0 : cnt.toNat = 1 → w0 ≠ 0xFFFFFFFF#32)
    (hw1 : cnt.toNat = 2 → w0 ≠ 0xFFFFFFFF#32 ∧ w1 ≠ 0xFFFFFFFF#32)
    (hoff1_pos : 1 ≤ wOff wvec1 lit.toNat)
    (hlen1 : FullState.LengthsOk c
      { s with
        core := { s.core with wvec := wvec1, wstk := wstk1, wlen := wlen1, wusable := wus1 }
        scratch := { s.scratch with wsort := wsort1 } })
    (hlay1 : WatchStackLayout
      { s.core with wvec := wvec1, wstk := wstk1, wlen := wlen1, wusable := wus1 })
    (hpres1 : WatchPresAll s
      { s with
        core := { s.core with wvec := wvec1, wstk := wstk1, wlen := wlen1, wusable := wus1 }
        scratch := { s.scratch with wsort := wsort1 } })
    (hend_eq : endVal.toNat = wOff wvec1 lit.toNat + wSz wvec1 lit.toNat)
    (hsz1 : sz32.toNat = wSz wvec1 lit.toNat)
    (hm1 : (FullMem c
      { s with
        core := { s.core with wvec := wvec1, wstk := wstk1, wlen := wlen1, wusable := wus1 }
        scratch := { s.scratch with wsort := wsort1 } } ⋆ R) m1)
    (hJB : JB () m1) (hQ : WPushPost c s R lit w0 w1 cnt Q) :
    wp Γ Q X (wpushCaseBExpr c.hdr c.pWvec c.pWstk (BitVec.ofNat 64 c.wcap) endVal
      (sz32.setWidth 64) (cnt.setWidth 64) lit w0 w1 cnt JB) m1 := by
  have hmx := c.hmaxv; have hwcap := c.hwcap; unfold dimacsBound at hmx hwcap
  have hco1 := hlen1.core_ok
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hco1.cur_vars_le
  have hwvl : wvec1.length = 4 * c.max_vars := hco1.wvec_len
  have hwsl1 : wstk1.length = c.wcap := hco1.wstk_len_arr
  have hwle1 : wlen1 ≤ c.wcap := hco1.wlen_le
  have hlit2p1 := bv64_lit2p1 (lit := lit)
  dsimp only [wpushCaseBExpr, eHdrLd, eHdrSt, eIdx4, eAddIdx4, eLit2p1Addr]
  c0_split
  · have hend_wlen : wOff wvec1 lit.toNat + wSz wvec1 lit.toNat = wlen1 := by
      have := congrArg BitVec.toNat hc
      rw [hend_eq, bv64_ofNat_toNat (by omega)] at this; exact this
    clear hc; c0_split
    · have hfitB : cnt.toNat ≤ c.wcap - wlen1 := by omega
      clear hc; c0_to_group
      refine wp_join_group (fun _ mW => ∃ wstkW : List (BitVec 32), wstkW.length = c.wcap ∧
        (∀ idx < wlen1, wstkW[idx]? = wstk1[idx]?) ∧ wstkW[wlen1]? = some w0 ∧
        (cnt.toNat = 2 → wstkW[wlen1 + 1]? = some w1) ∧
        (FullMem c { s with
          core := { s.core with wvec := wvec1, wstk := wstkW, wlen := wlen1, wusable := wus1 }
          scratch := { s.scratch with wsort := wsort1 } } ⋆ R) mW) ?_ ?_
      · rintro _ _ mW ⟨wstkW, hwsW, hpreW, hat0W, hat1W, hmW⟩; c0_usteps
        have hsz_new : ((sz32.setWidth 64 + cnt.setWidth 64).setWidth 32).toNat =
            wSz wvec1 lit.toNat + cnt.toNat := by
          have h := bv32_trunc_add (a := sz32.setWidth 64) (b := cnt)
            (by rw [zext_toNat sz32 (by decide), hsz1]; omega)
          rwa [zext_toNat sz32 (by decide), hsz1] at h
        have hwlen_new : (endVal + cnt.setWidth 64).toNat = wlen1 + cnt.toNat := by
          rw [BitVec.toNat_add, hend_eq, hend_wlen, zext_toNat _ (by decide)]; omega
        have hod := wvec_set_odd_u (wvec := wvec1) (l := lit.toNat)
          (v := (sz32.setWidth 64 + cnt.setWidth 64).setWidth 32) (by omega)
        have hfin := wpush_finalize (s := s)
          (s2 := { s with
            core := { s.core with wvec := wvec1, wstk := wstk1, wlen := wlen1, wusable := wus1 }
            scratch := { s.scratch with wsort := wsort1 } })
          (lit := lit.toNat) (cnt := cnt.toNat) (dst := wOff wvec1 lit.toNat)
          (wlen' := (endVal + cnt.setWidth 64).toNat)
          (wvec' := wvec1.set ((lit.setWidth 64 <<< (1 : Nat) + 1).toNat)
            ((sz32.setWidth 64 + cnt.setWidth 64).setWidth 32))
          (wstk' := wstkW) (wsort' := wsort1) hlay1 hpres1 hlit_lt hcnt12 hw0 hw1
          (by dsimp only; omega) hoff1_pos (by dsimp only; omega)
          (fun j hj hne => by rw [wOff, wSz, hlit2p1, (hod j).1, (hod j).2.1 hne]; exact ⟨rfl, rfl⟩)
          (by rw [wOff, hlit2p1, (hod lit.toNat).1])
          (by rw [wSz, hlit2p1, (hod lit.toNat).2.2, Option.getD_some, hsz_new])
          (fun j hj hne hszj => by
            have hbj := hlay1.bounds j (hpres1.1 ▸ hj)
            change wOff wvec1 j + wSz wvec1 j ≤ wlen1 at hbj
            dsimp only at hszj ⊢
            by_cases hszl : 0 < wSz wvec1 lit.toNat
            · rcases hlay1.disjoint j lit.toNat (hpres1.1 ▸ hj) (hpres1.1 ▸ hlit_lt)
                  hne hszj hszl with hd | hd
              · exact Or.inl hd
              · change wOff wvec1 lit.toNat + wSz wvec1 lit.toNat ≤ wOff wvec1 j at hd
                omega
            · exact Or.inl (by omega))
          (fun j hj _ k hk => by
            have hbj := hlay1.bounds j (hpres1.1 ▸ hj)
            change wOff wvec1 j + wSz wvec1 j ≤ wlen1 at hbj
            dsimp only at hk ⊢; exact hpreW _ (by omega))
          (fun k hk => by dsimp only at hk ⊢; exact hpreW _ (by omega))
          (by dsimp only; rw [hend_wlen]; exact hat0W)
          (fun hc2 => by dsimp only; rw [hend_wlen]; exact hat1W hc2) wus1
        exact hQ true _ wstkW _ wus1 wsort1 _
          { core_ok := { hco1 with wvec_len := by rw [List.length_set, hwvl],
                                   wstk_len_arr := hwsW, wlen_le := by dsimp only; omega }
            scratch_ok := hlen1.scratch_ok }
          hfin.1 hfin.2.1 (fun _ => ⟨hlit_lt, hcnt12, hfin.2.2.1, hfin.2.2.2.1,
            hfin.2.2.2.2.1, hfin.2.2.2.2.2⟩) (fun h => by cases h) hm
      · intro JW hJW; clear hQ
        have hend_p1 : (endVal + 1).toNat = wlen1 + 1 := by
          rw [BitVec.toNat_add, hend_eq, hend_wlen]; simp; omega
        c0_split
        · have hc2 := bv32_eq_nat 2 (by decide) hc; c0_usteps
          refine hJW _ _ ⟨_, by rw [List.length_set, List.length_set, hwsl1],
            fun idx hidx => by
              rw [hend_p1, hend_eq, hend_wlen, List.getElem?_set_ne (by omega),
                List.getElem?_set_ne (by omega)],
            by rw [hend_p1, hend_eq, hend_wlen, List.getElem?_set_ne (by omega),
              List.getElem?_set_self (by omega)],
            fun _ => by rw [hend_p1, List.getElem?_set_self (by rw [List.length_set]; omega)], hm⟩
        · c0_usteps; have hne2 := bv32_ne_nat 2 (by decide) hc
          refine hJW _ _ ⟨_, by rw [List.length_set, hwsl1],
            fun idx hidx => by rw [hend_eq, hend_wlen, List.getElem?_set_ne (by omega)],
            by rw [hend_eq, hend_wlen, List.getElem?_set_self (by omega)],
            fun hc2 => absurd hc2 hne2, hm⟩
    · c0_usteps; exact hJB
  · c0_usteps; exact hJB

end LeanQbe.T.Examples.Kissat.FullFidelityStep8

end
