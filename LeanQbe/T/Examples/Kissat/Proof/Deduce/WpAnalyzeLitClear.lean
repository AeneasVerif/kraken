/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Deduce.Spec
public import LeanQbe.T.Examples.Kissat.Src.Deduce
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Deduce.WpCommon
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Leaf WP Proofs for `Src.Deduce` (`Proof.Deduce.WpAnalyzeLitClear`)

Parametric `(Γ : Env)` `Func.wp` proofs (`public section`, `0` legacy `Full*` imports,
`0` `import all`, `0` `@[expose]` on theorems/lemmas/sections) for the `3` leaf functions:
1. `full_analyze_lit_wp` (`Spec.fullAnalyzeLitSpec`)
2. `full_clear_ana_wp` (`Spec.fullClearAnaSpec`)
3. `full_otfs_subsume_wp` (`Spec.fullOtfsSubsumeSpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Deduce

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Deduce
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Deduce.Spec
open Kraken.Bedrock2.Test

open scoped FullArenaTactics DeduceTactics

local elab "d_hsteps" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 10000

local elab "d_hsteps_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

/-! ## 1. `full_analyze_lit_wp` (`Spec.fullAnalyzeLitSpec`) -/

private abbrev AnaLitQ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop)
    (lit skip_var : BitVec 32) (Q : Post [.bool]) : Prop :=
  ∀ (ok : Bool) mrk' tmp' tc' tl' mcl' ws1' ant' res' m',
    let s' : FullState :=
      { s with
        core := { s.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                              min_clr_len := mcl' }
        scratch := { s.scratch with work_stk1 := ws1', ant_sz := ant', res_sz := res' } }
    s'.LengthsOk c → FullAnaMarksCov c s' → s.core.tmp_len ≤ tl' → tl' ≤ s.core.tmp_len + 1 →
    tl' ≤ s.core.cur_vars → s.core.tmp_cnt ≤ tc' →
    ant' = s.scratch.ant_sz +
      (if lit.toNat / 2 < s.core.cur_vars ∧ 0 < (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ∧
          (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ s.core.cur_level
       then 1#64 else 0#64) →
    res' = s.scratch.res_sz +
      (if lit.toNat / 2 < s.core.cur_vars ∧ s.core.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 ∧
          mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8 then 1#64 else 0#64) →
    tc' = s.core.tmp_cnt +
      (if lit.toNat / 2 < s.core.cur_vars ∧ s.core.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 ∧
          mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8 ∧
          (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat = s.core.cur_level
       then 1 else 0) →
    (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
      mrk'[v]?.getD 0#8 = s.core.mrk[v]?.getD 0#8) →
    (∀ k < s.core.tmp_len, tmp'[k]? = s.core.tmp[k]?) →
    (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
      lit.toNat / 2 = v ∧ v < s.core.cur_vars ∧ v ≠ skip_var.toNat ∧
      0 < (s.core.lvl[v]?.getD 0#32).toNat ∧
      (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level) →
    (∀ j, s.core.tmp_len ≤ j → j < tl' →
      (tmp'[j]?.getD 0#32).toNat = lit.toNat ∧ lit.toNat / 2 < s.core.cur_vars ∧
      lit.toNat / 2 ≠ skip_var.toNat ∧ s.core.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 ∧
      0 < (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ∧
      (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat < s.core.cur_level ∧
      mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8) →
    (ok = true → lit.toNat / 2 < s.core.cur_vars ∧
      (lit.toNat / 2 ≠ skip_var.toNat →
        (0 < (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat →
          mrk'[lit.toNat / 2]?.getD 0#8 ≠ 0#8) ∧
        (s.core.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 →
          (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ s.core.cur_level ∧
          (0 < (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat →
            (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat = s.core.cur_level →
            tc' = s.core.tmp_cnt + 1) ∧
          (0 < (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat →
            (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat < s.core.cur_level →
            tl' = s.core.tmp_len + 1 ∧ tmp'[s.core.tmp_len]? = some lit)))) →
    (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

private abbrev anaLitSt (s : FullState) (mrk' : List (BitVec 8)) (tmp' ws1' : List (BitVec 32))
    (mcl' tc' tl' : Nat) (ant' res' : BitVec 64) : FullState :=
  { s with
    core := { s.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                          min_clr_len := mcl' }
    scratch := { s.scratch with work_stk1 := ws1', ant_sz := ant', res_sz := res' } }

private theorem mk_lit_ne_skip {lit skip_var : BitVec 32} (h : lit >>> 1 ≠ skip_var) :
    lit.toNat / 2 ≠ skip_var.toNat :=
  fun heq => h (BitVec.eq_of_toNat_eq (by rw [bv32_lshr_1]; exact heq))

private theorem mk_lvl_pos {lvl : List (BitVec 32)} {v : Nat} {hv : v < lvl.length}
    (hnz : lvl[v]'hv ≠ 0#32) : 0 < (lvl[v]?.getD 0#32).toNat := by
  rw [List.getElem?_eq_getElem hv, Option.getD_some]
  exact Nat.pos_of_ne_zero fun hz => hnz (BitVec.eq_of_toNat_eq hz)

private theorem mrk_getD_ne_zero {mrk : List (BitVec 8)} {v : Nat} {hv : v < mrk.length}
    (h : mrk[v]'hv ≠ 0#8) : mrk[v]?.getD 0#8 ≠ 0#8 := by
  rwa [List.getElem?_eq_getElem hv, Option.getD_some]

private theorem lvl_lt_cur_of_le_ne {lvl : List (BitVec 32)} {v cl : Nat}
    {hv : v < lvl.length} (hcl32 : cl < 2 ^ 32)
    (hle : ¬ cl % 2 ^ 32 < (lvl[v]'hv).toNat)
    (hne : lvl[v]'hv ≠ (BitVec.ofNat 64 cl).setWidth 32) :
    (lvl[v]?.getD 0#32).toNat < cl := by
  rw [Nat.mod_eq_of_lt hcl32] at hle
  rw [List.getElem?_eq_getElem hv, Option.getD_some]
  have hle' : (lvl[v]'hv).toNat ≤ cl := Nat.le_of_not_gt hle
  refine Nat.lt_of_le_of_ne hle' fun heq => hne (BitVec.eq_of_toNat_eq ?_)
  rw [BitVec.toNat_setWidth, bv64_ofNat_toNat (by omega), Nat.mod_eq_of_lt hcl32, heq]

private theorem full_analyze_lit_mark {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post [.bool]} {lit skip_var : BitVec 32} (ok : Bool)
    (tmp' : List (BitVec 32)) (tc' tl' : Nat) (hlen : s.LengthsOk c) (hcov : FullAnaMarksCov c s)
    (hvlt : lit.toNat / 2 < s.core.cur_vars) (hvne : lit.toNat / 2 ≠ skip_var.toNat)
    (hm0 : s.core.mrk[lit.toNat / 2]?.getD 0#8 = 0#8)
    (hvl_pos : 0 < (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat)
    (hvl_le : (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ s.core.cur_level)
    (htmp_len : tmp'.length = c.max_vars) (htl_ge : s.core.tmp_len ≤ tl')
    (htl_inc : tl' ≤ s.core.tmp_len + 1) (htl_cv : tl' ≤ s.core.cur_vars)
    (htc_ge : s.core.tmp_cnt ≤ tc') (htpres : ∀ k < s.core.tmp_len, tmp'[k]? = s.core.tmp[k]?)
    (hnewt : ∀ j, s.core.tmp_len ≤ j → j < tl' → (tmp'[j]?.getD 0#32).toNat = lit.toNat ∧
      (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat < s.core.cur_level)
    (htc_eq : tc' = s.core.tmp_cnt +
      if (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat = s.core.cur_level then 1 else 0)
    (hok : ok = true → ((s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat = s.core.cur_level →
        tc' = s.core.tmp_cnt + 1) ∧ ((s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat <
        s.core.cur_level → tl' = s.core.tmp_len + 1 ∧ tmp'[s.core.tmp_len]? = some lit))
    (hm : (FullMem c (anaLitSt s (s.core.mrk.set (lit.toNat / 2) 1#8) tmp'
      (s.scratch.work_stk1.set s.core.min_clr_len (lit >>> 1)) (s.core.min_clr_len + 1)
      tc' tl' (s.scratch.ant_sz + 1#64) (s.scratch.res_sz + 1#64)) ⋆ R) m)
    (hQ : AnaLitQ c s R lit skip_var Q) : Q (ok, ()) m := by
  have ⟨hmcl_lt, hcov'⟩ := anaMarksCov_step_lshr hlen hcov lit hvlt hm0
  have hcv := hlen.core_ok.cur_vars_le
  let mrk1 := s.core.mrk.set (lit.toNat / 2) 1#8
  let ws1 := s.scratch.work_stk1.set s.core.min_clr_len (lit >>> 1)
  have hlen' : (anaLitSt s mrk1 tmp' ws1 (s.core.min_clr_len + 1) tc' tl'
      (s.scratch.ant_sz + 1#64) (s.scratch.res_sz + 1#64)).LengthsOk c :=
    ⟨{ hlen.core_ok with
        mrk_len := (by dsimp [anaLitSt, mrk1]; rw [List.length_set, hlen.core_ok.mrk_len])
        tmp_len_arr := htmp_len
        tmp_len_le := (by dsimp [anaLitSt]; omega)
        min_clr_len_le := (by dsimp [anaLitSt]; omega) },
     { hlen.scratch_ok with
        work_stk1_len := (by
          dsimp [anaLitSt, ws1]; rw [List.length_set, hlen.scratch_ok.work_stk1_len]) }⟩
  have hcov_fin : FullAnaMarksCov c (anaLitSt s mrk1 tmp' ws1 (s.core.min_clr_len + 1) tc' tl'
      (s.scratch.ant_sz + 1#64) (s.scratch.res_sz + 1#64)) :=
    ⟨hcov'.1, hcov'.2.1, hcov'.2.2.1, hcov'.2.2.2⟩
  have hm1 : mrk1[lit.toNat / 2]?.getD 0#8 ≠ 0#8 := by
    rw [List.getElem?_set_self
      (by rw [hlen.core_ok.mrk_len]; have := hlen.core_ok.cur_vars_le; omega)]
    decide
  refine hQ ok mrk1 tmp' tc' tl' (s.core.min_clr_len + 1) ws1 (s.scratch.ant_sz + 1#64)
    (s.scratch.res_sz + 1#64) m hlen' hcov_fin htl_ge htl_inc htl_cv htc_ge
    (by simp [hvlt, hvl_pos, hvl_le]) (by simp [hvlt, hm0, hm1])
    (by simpa [hvlt, hm0, hm1] using htc_eq)
    (fun _ _ hnz => by rw [List.getElem?_set_ne fun heq => hnz (by rw [← heq, hm0])]) htpres
    (fun w _ hw0 hnz' => if hwe : w = lit.toNat / 2 then by subst w; exact ⟨rfl, hvlt, hvne,
        hvl_pos, hvl_le⟩ else absurd hw0 (by rwa [List.getElem?_set_ne (Ne.symm hwe)] at hnz'))
    (fun j h1 h2 => let ⟨hl, hlt⟩ := hnewt j h1 h2; ⟨hl, hvlt, hvne, hm0, hvl_pos, hlt, hm1⟩)
    (fun h => ⟨hvlt, fun _ => ⟨fun _ => hm1, fun _ =>
      ⟨hvl_le, fun _ hcl => (hok h).1 hcl, fun _ hlt => (hok h).2 hlt⟩⟩⟩) hm

private theorem full_analyze_lit_ret_false (lit skip_var : BitVec 32)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]}
    (hlen : s.LengthsOk c) (htl_cv : s.core.tmp_len ≤ s.core.cur_vars)
    (hcov : FullAnaMarksCov c s) (hm : (FullMem c s ⋆ R) m) (hQ : AnaLitQ c s R lit skip_var Q)
    (hbad : ¬ (lit.toNat / 2 < s.core.cur_vars ∧
      (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ s.core.cur_level)) : Q (false, ()) m :=
  hQ false s.core.mrk s.core.tmp s.core.tmp_cnt s.core.tmp_len s.core.min_clr_len
    s.scratch.work_stk1 s.scratch.ant_sz s.scratch.res_sz m hlen hcov (Nat.le_refl _) (by omega)
    htl_cv (Nat.le_refl _) (by rw [ite_eq_right (fun h => hbad ⟨h.1, h.2.2⟩)]; simp)
    (by rw [ite_eq_right (fun h => h.2.2 h.2.1)]; simp)
    (by rw [ite_eq_right (fun h => h.2.2.1 h.2.1)]; simp)
    (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ h0 h => absurd h0 h)
    (fun _ h1 h2 => by omega) (fun hc => by cases hc) hm

private theorem full_analyze_lit_ret_lvl0 (lit skip_var : BitVec 32)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]}
    (hlen : s.LengthsOk c) (htl_cv : s.core.tmp_len ≤ s.core.cur_vars)
    (hcov : FullAnaMarksCov c s) (hm : (FullMem c s ⋆ R) m) (hQ : AnaLitQ c s R lit skip_var Q)
    (hvlt : lit.toNat / 2 < s.core.cur_vars)
    (h0 : (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat = 0) : Q (true, ()) m :=
  hQ true s.core.mrk s.core.tmp s.core.tmp_cnt s.core.tmp_len s.core.min_clr_len
    s.scratch.work_stk1 s.scratch.ant_sz s.scratch.res_sz m hlen hcov (Nat.le_refl _) (by omega)
    htl_cv (Nat.le_refl _) (by simp [h0])
    (by rw [ite_eq_right (fun h => h.2.2 h.2.1)]; simp)
    (by rw [ite_eq_right (fun h => h.2.2.1 h.2.1)]; simp)
    (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ h0 h => absurd h0 h)
    (fun _ h1 h2 => by omega) (fun _ => ⟨hvlt, fun _ =>
      ⟨fun _ => by omega, fun _ => ⟨by omega, fun _ _ => by omega, fun _ => by omega⟩⟩⟩) hm

private theorem full_analyze_lit_ret_skip (lit skip_var : BitVec 32)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [.bool]}
    (hlen : s.LengthsOk c) (htl_cv : s.core.tmp_len ≤ s.core.cur_vars)
    (hcov : FullAnaMarksCov c s) (hQ : AnaLitQ c s R lit skip_var Q)
    (hvlt : lit.toNat / 2 < s.core.cur_vars)
    (hcase : lit.toNat / 2 = skip_var.toNat ∨ s.core.mrk[lit.toNat / 2]?.getD 0#8 ≠ 0#8)
    (hpos : 0 < (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat)
    (hle : (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ s.core.cur_level)
    (hm' : (FullMem c { s with scratch := { s.scratch with
      ant_sz := s.scratch.ant_sz + 1 } } ⋆ R) m') : Q (true, ()) m' :=
  hQ true s.core.mrk s.core.tmp s.core.tmp_cnt s.core.tmp_len s.core.min_clr_len
    s.scratch.work_stk1 (s.scratch.ant_sz + 1) s.scratch.res_sz m'
    ⟨hlen.core_ok, { hlen.scratch_ok with }⟩ hcov (Nat.le_refl _) (by omega)
    htl_cv (Nat.le_refl _) (by simp [hvlt, hpos, hle])
    (by rw [ite_eq_right (fun h => h.2.2 h.2.1)]; simp)
    (by rw [ite_eq_right (fun h => h.2.2.1 h.2.1)]; simp)
    (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ h0 h => absurd h0 h)
    (fun _ h1 h2 => by omega) (fun _ => ⟨hvlt, fun hne =>
      hcase.elim (fun h => absurd h hne) fun h => ⟨fun _ => h, fun hm0 => absurd hm0 h⟩⟩) hm'

/-- Canonical `Func.wp` proof for `full_analyze_lit` (`Spec.fullAnalyzeLitSpec`). -/
theorem full_analyze_lit_wp (Γ : Env) :
    ∀ args m Q X, Spec.fullAnalyzeLitSpec args m Q X →
      Func.wp Γ full_analyze_lit_body args m Q X := by
  rintro ⟨h, lit, skip_var, ⟨⟩⟩ m Q X
    ⟨c, s, R, rfl, hlen, hcur32, htl_cv, htc_fit, hcov, hm, hQ⟩
  have hmax32 := fullInv_max_vars_lt32 c; have hcv_le := hlen.core_ok.cur_vars_le
  have hmcl_le := hlen.core_ok.min_clr_len_le; have hml := hlen.core_ok.mrk_len
  have hll := hlen.core_ok.lvl_len; have htl := hlen.core_ok.tmp_len_arr
  have hws_l := hlen.scratch_ok.work_stk1_len
  have hcur_tr : ((BitVec.ofNat 64 s.core.cur_level).setWidth 32).toNat = s.core.cur_level := by
    rw [bv64_trunc32_ofNat hcur32, bv32_ofNat_toNat hcur32]
  have hm2_mod : s.core.cur_level % 2 ^ 64 = s.core.cur_level := Nat.mod_eq_of_lt (by omega)
  have hm3_mod : s.core.cur_vars % 2 ^ 64 = s.core.cur_vars := Nat.mod_eq_of_lt (by omega)
  have hm4_mod : s.core.tmp_len % 2 ^ 64 = s.core.tmp_len := Nat.mod_eq_of_lt (by omega)
  have hm5_mod : s.core.min_clr_len % 2 ^ 64 = s.core.min_clr_len := Nat.mod_eq_of_lt (by omega)
  have hv_lt_of (h : ¬ s.core.cur_vars % 2 ^ 64 ≤ lit.toNat / 2) :
      lit.toNat / 2 < s.core.cur_vars := by rw [hm3_mod] at h; omega
  have hm0_of (hvlt : lit.toNat / 2 < s.core.cur_vars)
      (h : s.core.mrk[lit.toNat / 2]'(by omega) = 0#8) :
      s.core.mrk[lit.toNat / 2]?.getD 0#8 = 0#8 := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact h
  have hmrk_set_eq : s.core.mrk.set ((lit >>> 1).setWidth 64).toNat 1#8 =
      s.core.mrk.set (lit.toNat / 2) 1#8 := by simp only [bv_c0_zext32_64, bv32_lshr_1]
  have hws_set_eq : s.scratch.work_stk1.set (BitVec.ofNat 64 s.core.min_clr_len).toNat (lit >>> 1) =
      s.scratch.work_stk1.set s.core.min_clr_len (lit >>> 1) := by rw [bv64_ofNat_toNat (by omega)]
  have hmcl1 : (BitVec.ofNat 64 s.core.min_clr_len + 1).toNat = s.core.min_clr_len + 1 := by
    simp only [bv_c0, BitVec.reduceToNat]; omega
  have hret_sk (hvlt : lit.toNat / 2 < s.core.cur_vars)
      (hnot : ¬ (s.core.cur_level % 2 ^ 64) % 2 ^ 32 < (s.core.lvl[lit.toNat / 2]'(by omega)).toNat)
      (hnz : s.core.lvl[lit.toNat / 2]'(by omega) ≠ 0#32)
      (hcase : lit.toNat / 2 = skip_var.toNat ∨ s.core.mrk[lit.toNat / 2]?.getD 0#8 ≠ 0#8)
      {m'} (hm' : (FullMem c { s with scratch := { s.scratch with
        ant_sz := s.scratch.ant_sz + 1 } } ⋆ R) m') : Q (true, ()) m' := by
    rw [hm2_mod, Nat.mod_eq_of_lt hcur32] at hnot
    have hle : (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat ≤ s.core.cur_level := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; omega
    exact full_analyze_lit_ret_skip lit skip_var hlen htl_cv hcov hQ hvlt hcase (mk_lvl_pos hnz)
      hle hm'
  d_hsteps
  · have hbad : s.core.cur_vars % 2 ^ 64 ≤ lit.toNat / 2 := by assumption
    rw [hm3_mod] at hbad
    exact full_analyze_lit_ret_false lit skip_var hlen htl_cv hcov hm hQ (by omega)
  · have hvlt := hv_lt_of ‹_›
    apply full_analyze_lit_ret_lvl0 lit skip_var hlen htl_cv hcov hm hQ hvlt
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some,
      show s.core.lvl[lit.toNat / 2]'(by omega) = 0#32 from ‹_›]; rfl
  · have hvlt := hv_lt_of ‹_›
    apply full_analyze_lit_ret_false lit skip_var hlen htl_cv hcov hm hQ
    rintro ⟨_, hle⟩; rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hle
    have hgt : s.core.cur_level % 2 ^ 64 % 2 ^ 32 <
        (s.core.lvl[lit.toNat / 2]'(by omega)).toNat := ‹_›
    rw [hm2_mod, Nat.mod_eq_of_lt hcur32] at hgt; omega
  · have hvlt := hv_lt_of ‹_›; have hm0 := hm0_of hvlt ‹_›
    have hvl_eq : (s.core.lvl[lit.toNat / 2]?.getD 0#32).toNat = s.core.cur_level := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some,
        show s.core.lvl[lit.toNat / 2]'(by omega) = (BitVec.ofNat 64 s.core.cur_level).setWidth 32
          from ‹_›, hcur_tr]
    have htc1 : (BitVec.ofNat 64 s.core.tmp_cnt + 1).toNat = s.core.tmp_cnt + 1 := by
      simp only [bv_c0, BitVec.reduceToNat]; omega
    try rw [show (1#64 : BitVec 64).setWidth 8 = 1#8 from rfl] at hm
    rw [hmrk_set_eq, hws_set_eq, htc1, hmcl1] at hm
    exact full_analyze_lit_mark true s.core.tmp (s.core.tmp_cnt + 1) s.core.tmp_len
      hlen hcov hvlt (mk_lit_ne_skip ‹_›) hm0 (mk_lvl_pos ‹_›) (by omega) htl (Nat.le_refl _)
      (by omega) htl_cv (by omega) (fun _ _ => rfl) (fun _ h1 h2 => by omega)
      (by simp [hvl_eq]) (fun _ => ⟨fun _ => rfl, fun h => by omega⟩) hm hQ
  · have hvlt := hv_lt_of ‹_›; have hm0 := hm0_of hvlt ‹_›
    have hle_lvl : ¬ (s.core.cur_level % 2 ^ 64) % 2 ^ 32 <
        (s.core.lvl[lit.toNat / 2]'(by omega)).toNat := ‹_›
    rw [hm2_mod] at hle_lvl
    have hvl_lt := lvl_lt_cur_of_le_ne hcur32 hle_lvl ‹_›
    try rw [show (1#64 : BitVec 64).setWidth 8 = 1#8 from rfl] at hm
    rw [hmrk_set_eq, hws_set_eq, hmcl1] at hm
    exact full_analyze_lit_mark false s.core.tmp s.core.tmp_cnt s.core.tmp_len
      hlen hcov hvlt (mk_lit_ne_skip ‹_›) hm0 (mk_lvl_pos ‹_›) (by omega) htl (Nat.le_refl _)
      (by omega) htl_cv (Nat.le_refl _) (fun _ _ => rfl) (fun _ h1 h2 => by omega)
      (by rw [ite_eq_right (fun _ => by omega), Nat.add_zero]) (fun hc => by cases hc) hm hQ
  · have hvlt := hv_lt_of ‹_›; have hm0 := hm0_of hvlt ‹_›
    have htl_b : ¬ s.core.cur_vars % 2 ^ 64 ≤ s.core.tmp_len % 2 ^ 64 := ‹_›
    rw [hm3_mod, hm4_mod] at htl_b
    have hle_lvl : ¬ (s.core.cur_level % 2 ^ 64) % 2 ^ 32 <
        (s.core.lvl[lit.toNat / 2]'(by omega)).toNat := ‹_›
    rw [hm2_mod] at hle_lvl
    have hvl_lt := lvl_lt_cur_of_le_ne hcur32 hle_lvl ‹_›
    have htl1 : (BitVec.ofNat 64 s.core.tmp_len + 1).toNat = s.core.tmp_len + 1 := by
      simp only [bv_c0, BitVec.reduceToNat]; omega
    try rw [show (1#64 : BitVec 64).setWidth 8 = 1#8 from rfl] at hm
    rw [hmrk_set_eq, hws_set_eq,
      show s.core.tmp.set (BitVec.ofNat 64 s.core.tmp_len).toNat lit =
        s.core.tmp.set s.core.tmp_len lit by rw [bv64_ofNat_toNat (by omega)], htl1, hmcl1] at hm
    exact full_analyze_lit_mark true (s.core.tmp.set s.core.tmp_len lit) s.core.tmp_cnt
      (s.core.tmp_len + 1) hlen hcov hvlt (mk_lit_ne_skip ‹_›) hm0 (mk_lvl_pos ‹_›) (by omega)
      (by simp [htl]) (by omega) (Nat.le_refl _) (by omega) (Nat.le_refl _)
      (fun _ hk => List.getElem?_set_ne (by omega)) (fun j h1 h2 => ⟨by
        have hje : j = s.core.tmp_len := by omega
        subst hje; rw [List.getElem?_set_self (by omega)]; rfl, hvl_lt⟩)
      (by rw [ite_eq_right (fun _ => by omega), Nat.add_zero])
      (fun _ => ⟨fun he => by omega, fun _ => ⟨rfl, List.getElem?_set_self (by omega)⟩⟩) hm hQ
  all_goals first
    | (have hvlt := hv_lt_of ‹_›; have hm0 := hm0_of hvlt ‹_›
       have hmcl : ¬ s.core.min_clr_len % 2 ^ 64 < s.core.cur_vars % 2 ^ 64 := ‹_›
       rw [hm5_mod, hm3_mod] at hmcl
       exact absurd (anaMarksCov_step hlen hcov hvlt hm0).1 hmcl)
    | exact hret_sk (hv_lt_of ‹_›) ‹_› ‹_› (Or.inr (mrk_getD_ne_zero (hv := by omega) ‹_›)) hm
    | (refine hret_sk (hv_lt_of ‹_›) ‹_› ‹_› (Or.inl ?_) hm
       have := congrArg BitVec.toNat (‹lit >>> 1 = skip_var›); rwa [bv32_lshr_1] at this)

/-! ## 2. `full_clear_ana_wp` (`Spec.fullClearAnaSpec`) -/

/-- Canonical `Func.wp` proof for `full_clear_ana` (`Spec.fullClearAnaSpec`). -/
theorem full_clear_ana_wp (Γ : Env) :
    ∀ args m Q X, Spec.fullClearAnaSpec args m Q X → Func.wp Γ full_clear_ana_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm0, hQ⟩
  have hmax32 := fullInv_max_vars_lt32 c; have hcv_le := hlen.core_ok.cur_vars_le
  have hm_len := hlen.core_ok.mrk_len; have hmcl_le := hlen.core_ok.min_clr_len_le
  have hws_len := hlen.scratch_ok.work_stk1_len
  let LoopInv : Nat → List (BitVec 8) → Prop := fun i mrk' =>
    i ≤ s.core.min_clr_len ∧ mrk'.length = c.max_vars ∧
    (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 = 0#8) ∧
    (∀ k < i, (s.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars →
      mrk'[(s.scratch.work_stk1[k]?.getD 0#32).toNat]?.getD 0#8 = 0#8)
  d_hsteps
  refine wp_loop_group (fun r (iv, ()) ml => ∃ i mrk',
    r = s.core.min_clr_len - i ∧ iv = BitVec.ofNat 64 i ∧ LoopInv i mrk' ∧
    (FullMem c { s with core := { s.core with mrk := mrk' } } ⋆ R) ml) ?_ ?_
  · clear hm0; rintro L r ⟨iv, ⟨⟩⟩ ml ih ⟨i, mrk', rfl, rfl, ⟨hile, hml_l, hzero, hclr⟩, hml0⟩
    have himod : i % 2 ^ 64 = i := Nat.mod_eq_of_lt (by omega)
    have hcvmod : s.core.cur_vars % 2 ^ 64 = s.core.cur_vars := Nat.mod_eq_of_lt (by omega)
    d_hsteps
    · have hilt : i < s.core.min_clr_len := by omega
      have hws_lt : i < s.scratch.work_stk1.length := by omega
      have hv_get : (s.scratch.work_stk1[i]?.getD 0#32).toNat =
          (s.scratch.work_stk1[i]'hws_lt).toNat := by
        rw [List.getElem?_eq_getElem hws_lt, Option.getD_some]
      have hidx_eq : s.scratch.work_stk1[i % 2 ^ 64]'(by rw [himod]; exact hws_lt) =
          s.scratch.work_stk1[i]'hws_lt := getElem_eq_of_idx himod
      have hv_lt : (s.scratch.work_stk1[i]'hws_lt).toNat < s.core.cur_vars := by
        have hlt_raw : (s.scratch.work_stk1[i % 2 ^ 64]'(by rw [himod]; exact hws_lt)).toNat <
            s.core.cur_vars % 2 ^ 64 := by assumption
        rw [congrArg BitVec.toNat hidx_eq, hcvmod] at hlt_raw; exact hlt_raw
      rw [show BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) from
        BitVec.eq_of_toNat_eq (by bv_omega)]
      refine ih (s.core.min_clr_len - (i + 1)) _ _ (by omega)
        ⟨i + 1, mrk'.set (s.scratch.work_stk1[i]'hws_lt).toNat 0#8, rfl, rfl,
          ⟨by omega, by simp [hml_l], fun v hv h0 => ?_, fun k hk hkv => ?_⟩, ?_⟩
      · by_cases hveq : v = (s.scratch.work_stk1[i]'hws_lt).toNat
        · rw [hveq, List.getElem?_set_self (by omega)]; rfl
        · rw [List.getElem?_set_ne (Ne.symm hveq)]; exact hzero v hv h0
      · by_cases hki : k = i
        · subst k; rw [hv_get, List.getElem?_set_self (by omega)]; rfl
        · by_cases heq : (s.scratch.work_stk1[k]?.getD 0#32).toNat =
              (s.scratch.work_stk1[i]'hws_lt).toNat
          · rw [heq, List.getElem?_set_self (by omega)]; rfl
          · rw [List.getElem?_set_ne (Ne.symm heq)]; exact hclr k (by omega) hkv
      · have hidx64 : s.scratch.work_stk1[(BitVec.ofNat 64 i).toNat]'(by
            rw [bv64_ofNat_toNat (by omega)]; exact hws_lt) = s.scratch.work_stk1[i]'hws_lt :=
          getElem_eq_of_idx (bv64_ofNat_toNat (by omega))
        have hmrk_eq : mrk'.set (BitVec.setWidth 64
            (s.scratch.work_stk1[(BitVec.ofNat 64 i).toNat]'(by
              rw [bv64_ofNat_toNat (by omega)]; exact hws_lt))).toNat 0#8 =
            mrk'.set (s.scratch.work_stk1[i]'hws_lt).toNat 0#8 := by rw [bv_c0_zext32_64, hidx64]
        rw [← hmrk_eq]; exact hm
    · have hilt : i < s.core.min_clr_len := by omega
      have hws_lt : i < s.scratch.work_stk1.length := by omega
      have hv_get : (s.scratch.work_stk1[i]?.getD 0#32).toNat =
          (s.scratch.work_stk1[i]'hws_lt).toNat := by
        rw [List.getElem?_eq_getElem hws_lt, Option.getD_some]
      have hidx_eq : s.scratch.work_stk1[i % 2 ^ 64]'(by rw [himod]; exact hws_lt) =
          s.scratch.work_stk1[i]'hws_lt := getElem_eq_of_idx himod
      have hv_ge : ¬ (s.scratch.work_stk1[i]'hws_lt).toNat < s.core.cur_vars := by
        have hge_raw : ¬ (s.scratch.work_stk1[i % 2 ^ 64]'(by rw [himod]; exact hws_lt)).toNat <
            s.core.cur_vars % 2 ^ 64 := by assumption
        rw [congrArg BitVec.toNat hidx_eq, hcvmod] at hge_raw; exact hge_raw
      rw [show BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) from
        BitVec.eq_of_toNat_eq (by bv_omega)]
      refine ih (s.core.min_clr_len - (i + 1)) _ _ (by omega)
        ⟨i + 1, mrk', rfl, rfl, ⟨by omega, hml_l, hzero, fun k hk hkv => ?_⟩, hml0⟩
      by_cases hki : k = i
      · subst k; rw [hv_get] at hkv; exact absurd hkv hv_ge
      · exact hclr k (by omega) hkv
    · have hieq : i = s.core.min_clr_len := by omega
      subst hieq; d_hsteps
      refine hQ mrk' _ hml_l hzero hclr (fun hcov v hv => ?_) (by assumption)
      by_cases hz : s.core.mrk[v]?.getD 0#8 = 0#8
      · exact hzero v hv hz
      · obtain ⟨k, hk, hkv⟩ := hcov.2.2.2 v hv hz
        have hlt := (hcov.2.2.1 k hk).1
        exact hkv ▸ hclr k hk hlt
  · intro L hL; d_hsteps
    refine hL s.core.min_clr_len _ m ⟨0, s.core.mrk, by omega, rfl,
      ⟨Nat.zero_le _, hm_len, fun _ _ h0 => h0, fun _ hk => by omega⟩, hm0⟩

/-! ## 3. `full_otfs_subsume_wp` (`Spec.fullOtfsSubsumeSpec`) -/

/-- Canonical `Func.wp` proof for `full_otfs_subsume` (`Spec.fullOtfsSubsumeSpec`). -/
theorem full_otfs_subsume_wp (Γ : Env) :
    ∀ args m Q X, Spec.fullOtfsSubsumeSpec args m Q X →
      Func.wp Γ full_otfs_subsume_body args m Q X := by
  rintro ⟨h, new_confl, old_ctype, old_cref, to_bin, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, cut, s, R, rfl, hlen, hw, hnd, hpre, hm, hQ⟩
  have hsame : Q () m := hQ s.core.arena s.core.arena_garbage s.core.num_irred
    s.core.num_redundant m hlen hw hnd rfl (fun _ _ => ⟨rfl, fun _ => rfl⟩) hm
  by_cases hct : old_ctype = 2#64
  · subst old_ctype
    by_cases hcr : old_cref = 0xFFFFFFFF#64
    · subst old_cref; c0_hsteps; exact hsame
    · obtain ⟨hold_ref, hnew_ref, hnonact⟩ := hpre rfl hcr
      have hwf := hw.arena.refs_wf old_cref.toNat hold_ref
      have har_len := hlen.core_ok.arena_len_arr; have har_le := hlen.core_ok.arena_len_le
      have hcap31 := c.harena; unfold dimacsBound at hcap31
      have hcr_bd : old_cref.toNat + 2 < s.core.arena.length := by omega
      have hcr2 : (old_cref + 2#64).toNat = old_cref.toNat + 2 := by
        rw [BitVec.toNat_add]; simp only [BitVec.reduceToNat]; omega
      have hd_eq : fullArenaHdrCore s.core old_cref.toNat =
          s.core.arena[old_cref.toNat]'(by omega) := by
        unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      obtain ⟨arena1, h_arena1⟩ : ∃ xs, xs = s.core.arena.set old_cref.toNat
          (fullArenaHdrCore s.core old_cref.toNat ||| 0x00080000#32) := ⟨_, rfl⟩
      have har1_len : arena1.length = c.arena_cap := by rw [h_arena1]; simp [har_len]
      obtain ⟨ag1, h_ag1⟩ : ∃ x, x = s.core.arena_garbage + 3#64 +
          (arena1[old_cref.toNat + 2]'(by rw [har1_len]; omega)).setWidth 64 := ⟨_, rfl⟩
      let s1 : FullState :=
        { s with core := { s.core with arena := arena1, arena_garbage := ag1 } }
      have hmg1 := markGarb_preserves_fullWitnessCut hlen.core_ok hw hold_ref ag1
        fun idx hidx hcond hne hlg => hnonact idx hidx hcond hne hlg
      rw [← h_arena1] at hmg1
      obtain ⟨hw1, hrefs1, hprops1⟩ := hmg1
      have hgarb_c : fullArenaClauseGarbCore s1.core old_cref.toNat = true := by
        unfold fullArenaClauseGarbCore fullArenaHdrCore
        dsimp only [s1]; rw [h_arena1, List.getElem?_set_self (by omega), Option.getD_some]
        simp [bv32_or_garb_garb]
      have hlen1 : s1.LengthsOk c :=
        ⟨{ hlen.core_ok with arena_len_arr := har1_len }, hlen.scratch_ok⟩
      have hnd1 : FullArenaVarsNodup s1 := fullArenaVarsNodup_markGarb hnd hrefs1 hgarb_c
        fun r hr hne => ⟨(hprops1 r hr).2.2 hne, (hprops1 r hr).2.1⟩
      have ha1_eq : s.core.arena.set old_cref.toNat
          (s.core.arena[old_cref.toNat]'(by omega) ||| 0x00080000#32) = arena1 := by
        rw [← hd_eq]; exact h_arena1.symm
      have hget_ag {xs : List (BitVec 32)} (hx : xs = arena1)
          (h1 : (old_cref + 2#64).toNat < xs.length) :
          s.core.arena_garbage + 3#64 + (xs[(old_cref + 2#64).toNat]'h1).setWidth 64 = ag1 := by
        subst hx; rw [h_ag1]; congr 1; congr 1; exact getElem_eq_of_idx hcr2
      have hdone_counts (ni1 nr1 : BitVec 64) (ml : Mem 64)
          (hml : (FullMem c { s1 with core :=
            { s1.core with num_irred := ni1, num_redundant := nr1 } } ⋆ R) ml) : Q () ml :=
        hQ arena1 ag1 ni1 nr1 ml
          ⟨{ hlen1.core_ok with arena_len_arr := har1_len }, hlen.scratch_ok⟩
          (fcut_with_counts hw1 ni1 nr1) hnd1 hrefs1
          (fun r hr => ⟨(hprops1 r hr).2.1, fun hne => (hprops1 r hr).2.2 (hne rfl)⟩) hml
      have hnc_z : (new_confl.setWidth 64).toNat = new_confl.toNat :=
        zext_toNat new_confl (by decide)
      have hcore1_eq {ml : Mem 64} {a' : List (BitVec 32)} {g' : BitVec 64}
          (ha : a' = arena1) (hg : g' = ag1)
          (hm' : (FullMem c { s with core := { s.core with arena := a', arena_garbage := g' } }
            ⋆ R) ml) : (FullMem c s1 ⋆ R) ml := by
        subst ha hg; exact hm'
      c0_hsteps_nogrp
      · exact hsame
      · refine wp_unroll_group fun Jtop hJtop => ?_
        have hm_s1 : (FullMem c s1 ⋆ R) _ := hcore1_eq ha1_eq (hget_ag ha1_eq _) ‹_›
        c0_hsteps_nogrp
        · refine wp_join_group (ts := [])
            (fun _ mnr => ∃ nr1 : BitVec 64,
              (FullMem c { s1 with core := { s1.core with num_redundant := nr1 } } ⋆ R) mnr) ?_ ?_
          · rintro _ ⟨⟩ mnr ⟨nr1, hmnr⟩
            refine wp_unroll_group fun Jred_out hJred_out => ?_
            c0_hsteps_nogrp
            · exact hdone_counts s.core.num_irred nr1 mnr hmnr
            · have hnc_ref := hnew_ref (by assumption)
              have hnc_wf := hw.arena.refs_wf new_confl.toNat hnc_ref
              have hnc_bd : new_confl.toNat < arena1.length := by rw [har1_len]; omega
              have hnc_ref1 : new_confl.toNat ∈ fullArenaClauseRefsCore s1.core := by
                rw [hrefs1]; exact hnc_ref
              have har_nc : fullArenaHdrCore s1.core new_confl.toNat =
                  arena1[new_confl.toNat]'hnc_bd := by
                unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem hnc_bd, Option.getD_some]
              c0_hsteps
              · let dg : BitVec 32 := (s.core.arena[old_cref.toNat]'(by omega)) &&& 0x0007FFFF#32
                let arena2 := s1.core.arena.set new_confl.toNat
                  ((fullArenaHdrCore s1.core new_confl.toNat &&& ~~~0x0007FFFF#32) ||| dg)
                obtain ⟨hw2, hrefs2, hprops2⟩ := arenaSetGlue_preserves_fullWitnessCut
                  hlen1.core_ok hw1 hnc_ref1 dg (bv32_and_glue_lt _) s.core.num_irred nr1
                have hlen2 : ({ s1 with core := { s1.core with
                    arena := arena2, num_redundant := nr1 } } : FullState).LengthsOk c :=
                  ⟨{ hlen1.core_ok with arena_len_arr := by simp [arena2, s1, har1_len] },
                    hlen.scratch_ok⟩
                have hnd2 : FullArenaVarsNodup { s1 with core :=
                    { s1.core with arena := arena2, num_redundant := nr1 } } := fun r hr hng2 => by
                  change r ∈ fullArenaClauseRefsCore _ at hr; rw [hrefs2] at hr
                  obtain ⟨_, hgarb2, hlits2⟩ := hprops2 r hr
                  change ((fullArenaClauseLitsCore _ r).map (· / 2)).Nodup
                  rw [hlits2]; refine hnd1 r hr ?_
                  change fullArenaClauseGarbCore s1.core r = false; rw [← hgarb2]; exact hng2
                let ar2_g := s1.core.arena.set (new_confl.setWidth 64).toNat
                  ((s1.core.arena[(new_confl.setWidth 64).toNat]'(by rw [hnc_z]; exact hnc_bd)
                    &&& ~~~0x0007FFFF#32) ||| dg)
                have har2_eq : ar2_g = arena2 := by
                  dsimp only [ar2_g, arena2, s1]
                  exact list_set_congr hnc_z
                    (by rw [getElem_eq_of_idx (hj := hnc_bd) hnc_z, har_nc])
                refine hQ arena2 ag1 s.core.num_irred nr1 _ hlen2
                  (fcut_with_counts hw2 s.core.num_irred nr1) hnd2 (hrefs2.trans hrefs1)
                  (fun r hr => by
                    have hr1 : r ∈ fullArenaClauseRefsCore s1.core := by rw [hrefs1]; exact hr
                    refine ⟨(hprops2 r hr1).2.2.trans (hprops1 r hr).2.1, fun hne => ?_⟩
                    exact (hprops2 r hr1).2.1.trans ((hprops1 r hr).2.2 (hne rfl))) ?_
                exact fullMem_of_eq (s1 := { s1 with core :=
                  { s1.core with arena := ar2_g, num_redundant := nr1 } })
                  ‹_› (by dsimp only [s1]; rw [har2_eq]) rfl
              · exact hdone_counts s.core.num_irred nr1 mnr hmnr
              · exact hdone_counts s.core.num_irred nr1 mnr hmnr
          · intro Jnr hJnr; c0_hsteps_nogrp
            · exact hJnr () _ ⟨s.core.num_redundant - 1#64, ‹_›⟩
            · exact hJnr () _ ⟨s.core.num_redundant, hm_s1⟩
        · refine wp_join_group (ts := [])
            (fun _ mni => ∃ ni1 : BitVec 64,
              (FullMem c { s1 with core := { s1.core with num_irred := ni1 } } ⋆ R) mni) ?_ ?_
          · rintro _ ⟨⟩ mni ⟨ni1, hmni⟩
            refine wp_unroll_group fun Jir_out hJir_out => ?_
            c0_hsteps_nogrp
            · exact hdone_counts ni1 s.core.num_redundant mni hmni
            · have hnc_ref := hnew_ref (by assumption)
              have hnc_wf := hw.arena.refs_wf new_confl.toNat hnc_ref
              have hnc_bd : new_confl.toNat < arena1.length := by rw [har1_len]; omega
              have hnc_ref1 : new_confl.toNat ∈ fullArenaClauseRefsCore s1.core := by
                rw [hrefs1]; exact hnc_ref
              have har_nc : fullArenaHdrCore s1.core new_confl.toNat =
                  arena1[new_confl.toNat]'hnc_bd := by
                unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem hnc_bd, Option.getD_some]
              let arena2 := s1.core.arena.set new_confl.toNat
                (fullArenaHdrCore s1.core new_confl.toNat &&& 0xFFBFFFFF#32)
              have hstep_red (ni2 nr2 : BitVec 64) (ml : Mem 64)
                  (hm2 : (FullMem c { s1 with core :=
                    { s1.core with arena := arena2, num_irred := ni2, num_redundant := nr2 } } ⋆ R)
                    ml) : Q () ml := by
                obtain ⟨hw2, hrefs2, hprops2⟩ :=
                  clearRed_preserves_fullWitnessCut hlen1.core_ok hw1 hnc_ref1 ni2 nr2
                have hlen2 : ({ s1 with core := { s1.core with
                    arena := arena2, num_irred := ni2, num_redundant := nr2 } } :
                    FullState).LengthsOk c :=
                  ⟨{ hlen1.core_ok with arena_len_arr := by simp [arena2, s1, har1_len] },
                    hlen.scratch_ok⟩
                have hnd2 : FullArenaVarsNodup { s1 with core :=
                    { s1.core with arena := arena2, num_irred := ni2, num_redundant := nr2 } } :=
                  fun r hr hng2 => by
                    change r ∈ fullArenaClauseRefsCore _ at hr; rw [hrefs2] at hr
                    obtain ⟨_, hgarb2, hlits2⟩ := hprops2 r hr
                    change ((fullArenaClauseLitsCore _ r).map (· / 2)).Nodup
                    rw [hlits2]; refine hnd1 r hr ?_
                    change fullArenaClauseGarbCore s1.core r = false; rw [← hgarb2]; exact hng2
                exact hQ arena2 ag1 ni2 nr2 ml hlen2 hw2 hnd2
                  (hrefs2.trans hrefs1) (fun r hr => by
                    have hr1 : r ∈ fullArenaClauseRefsCore s1.core := by rw [hrefs1]; exact hr
                    refine ⟨(hprops2 r hr1).2.2.trans (hprops1 r hr).2.1, fun hne => ?_⟩
                    exact (hprops2 r hr1).2.1.trans ((hprops1 r hr).2.2 (hne rfl))) hm2
              have hnot_ff : ~~~(4194304#32 : BitVec 32) = 0xFFBFFFFF#32 := by decide
              let ar2_c0 := s1.core.arena.set (new_confl.setWidth 64).toNat
                (s1.core.arena[(new_confl.setWidth 64).toNat]'(by rw [hnc_z]; exact hnc_bd) &&&
                  ~~~(4194304#32 : BitVec 32))
              have har2_eq : ar2_c0 = arena2 := by
                dsimp only [ar2_c0, arena2, s1]
                exact list_set_congr hnc_z
                  (by rw [getElem_eq_of_idx (hj := hnc_bd) hnc_z, har_nc, hnot_ff])
              c0_hsteps
              · exact hstep_red (ni1 + 1#64) (s.core.num_redundant - 1#64) _
                  (fullMem_of_eq (s1 := { s1 with core := { s1.core with
                    num_irred := ni1 + 1#64, num_redundant := s.core.num_redundant - 1#64,
                    arena := ar2_c0 } }) ‹_› (by dsimp only [s1]; rw [har2_eq]) rfl)
              · exact hstep_red (ni1 + 1#64) s.core.num_redundant _
                  (fullMem_of_eq (s1 := { s1 with core := { s1.core with
                    num_irred := ni1 + 1#64, arena := ar2_c0 } })
                    ‹_› (by dsimp only [s1]; rw [har2_eq]) rfl)
              · exact hdone_counts ni1 s.core.num_redundant mni hmni
          · intro Jni hJni; c0_hsteps_nogrp
            · exact hJni () _ ⟨s.core.num_irred - 1#64, ‹_›⟩
            · exact hJni () _ ⟨s.core.num_irred, hm_s1⟩
  · c0_hsteps
    · exact hsame
    all_goals (exfalso; exact hct ‹_›)

end LeanQbe.T.Examples.Kissat.Proof.Deduce
