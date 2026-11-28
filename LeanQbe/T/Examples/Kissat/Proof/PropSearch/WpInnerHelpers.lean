/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.BcpPropHelpers
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Canonical Inner-Loop Helpers for `PropSearch` (`WpInnerHelpers`)

Self-contained `CanonicalEnv` helpers (`0` legacy `Full*` imports, `<= 1,500` LOC,
`<= 450` LOC/decl, `<= 100` cols, `0` `@[expose]` on theorems):
1. Pure BitVec / `List` / `fastPropMem` helpers.
2. `PropLitInv` / `PropLitConfl` / `SplitWatchesInv` transition lemmas.
3. Step-13 inner-loop state lemmas (`S13ConflEq`, `s13_bin_jumpreason_step`,
   `s13_unswapped_ar_swap_nw`, `s13_clause_falsified_of_find_repl_none`, `s13_large_confl_w0`,
   `s13_setSrch_step`, `m7_tB_swap_step`, `m7_ovf_fail_step`).
4. Sub-expression AST builders (`m7LpReplScanExpr`, `m7LpMaxLvlExpr`, `fidLpArSwapExpr`) and WPs.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.PropSearch

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
open LeanQbe.T.Examples.Kissat.Proof.PropSearch.BcpPropTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.PropSearch.BcpPropTactics

attribute [local irreducible] fastPropMem

local macro "s13_hsteps" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps))

local macro "s13_hsteps_nogrp" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsteps_nogrp))

local macro "s13_hsplit" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsplit))

/-! ## 1. Arithmetic, List & `fastPropMem` Helpers -/

theorem m7_list_set_eq_self {α : Type} {xs : List α} {i : Nat} {v : α}
    (hget : xs[i]? = some v) : xs.set i v = xs := by
  by_cases hi : i < xs.length
  · have hv : xs[i]'hi = v := Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hget)
    rw [← hv]; exact List.set_getElem_self hi
  · rw [List.getElem?_eq_none (Nat.le_of_not_lt hi)] at hget
    cases hget

theorem m7_bv64_sub_toNat {a b : BitVec 64} (hba : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := bv64_sub_toNat hba

theorem m7_bv64_add_toNat {a b : BitVec 64} (hab : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := bv64_add_toNat hab

theorem m7_bv64_add1_toNat {a : BitVec 64} (ha : a.toNat + 1 < 2 ^ 64) :
    (a + 1#64).toNat = a.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt ha]

theorem m7_bv64_add2_toNat {a : BitVec 64} (ha : a.toNat + 2 < 2 ^ 64) :
    (a + 2#64).toNat = a.toNat + 2 := bv64_add2_toNat ha

theorem m7_bv64_shl1_u32_nat (x : BitVec 32) :
    (x.setWidth 64 <<< (1 : Nat)).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, bv_c0_zext32_64]; simp [Nat.shiftLeft_eq]
  rw [Nat.mul_comm, Nat.mod_eq_of_lt (by have := x.isLt; omega)]

theorem m7_bv64_shl1_add1_nat (x : BitVec 32) :
    ((x.setWidth 64 <<< (1 : Nat)) + 1#64).toNat = 2 * x.toNat + 1 := by
  have hx := x.isLt
  rw [m7_bv64_add1_toNat (by rw [m7_bv64_shl1_u32_nat]; omega), m7_bv64_shl1_u32_nat]

theorem m7_bv32_rshift1_toNat (x : BitVec 32) :
    ((x >>> 1#32).setWidth 64).toNat = x.toNat / 2 := by
  rw [bv_c0_zext32_64, show (x >>> 1#32) = (x >>> 1) from rfl, bv32_lshr_1]

theorem m7_bv32_ofNat_toNat_lt {n : Nat} (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 n).toNat = n := bv32_ofNat_toNat hn

theorem m7_bv64_ofNat_toNat_lt {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem m7_bv32_mask7f_eq {x : BitVec 32} (hx : x.toNat < 2 ^ 31) :
    x &&& 0x7FFFFFFF#32 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 from by decide]
  exact (Nat.and_two_pow_sub_one_eq_mod x.toNat 31).trans (Nat.mod_eq_of_lt hx)

theorem fc_getElem_eq_of_idx {α : Type} {a b : List α} {i j : Nat}
    (hab : a = b) (hij : i = j) (hi : i < a.length) (hj : j < b.length) :
    a[i]'hi = b[j]'hj := by
  subst hab hij; rfl

theorem fc_getElem_vals (s0 sem : FullState) {i : Nat}
    (h1 : i < (fastPropMem s0 sem).core.vals.length) (h2 : i < sem.core.vals.length) :
    (fastPropMem s0 sem).core.vals[i]'h1 = sem.core.vals[i]'h2 :=
  fc_getElem_eq_of_idx (fastPropMem_vals s0 sem) rfl h1 h2

theorem fc_getElem_wstk (s0 sem : FullState) {i : Nat}
    (h1 : i < (fastPropMem s0 sem).core.wstk.length) (h2 : i < sem.core.wstk.length) :
    (fastPropMem s0 sem).core.wstk[i]'h1 = sem.core.wstk[i]'h2 :=
  fc_getElem_eq_of_idx (fastPropMem_wstk s0 sem) rfl h1 h2

theorem fc_getElem_arena (s0 sem : FullState) {i : Nat}
    (h1 : i < (fastPropMem s0 sem).core.arena.length) (h2 : i < sem.core.arena.length) :
    (fastPropMem s0 sem).core.arena[i]'h1 = sem.core.arena[i]'h2 :=
  fc_getElem_eq_of_idx (fastPropMem_arena s0 sem) rfl h1 h2

theorem fc_getElem_lvl (s0 sem : FullState) {i : Nat}
    (h1 : i < (fastPropMem s0 sem).core.lvl.length) (h2 : i < sem.core.lvl.length) :
    (fastPropMem s0 sem).core.lvl[i]'h1 = sem.core.lvl[i]'h2 :=
  fc_getElem_eq_of_idx (fastPropMem_lvl s0 sem) rfl h1 h2

theorem litNeg_ne_self (l : Nat) : l ^^^ 1 ≠ l := by
  intro h
  have hb := congrArg (·.testBit 0) h
  simp only [Nat.testBit_xor, show (1 : Nat).testBit 0 = true from rfl] at hb
  cases h0 : l.testBit 0 <;> simp_all

theorem mem_fullArenaClauseLitsCore_of_idx {k : FullCoreState} {cref k_off : Nat} {v : BitVec 32}
    (hsz : k_off < fullArenaClauseSizeCore k cref)
    (hget : k.arena[cref + 3 + k_off]? = some v) :
    v.toNat ∈ fullArenaClauseLitsCore k cref := by
  have hlen : cref + 3 + k_off < k.arena.length :=
    Nat.lt_of_not_ge fun hge => by rw [List.getElem?_eq_none hge] at hget; cases hget
  unfold fullArenaClauseLitsCore; rw [List.mem_map]
  refine ⟨v, List.mem_iff_getElem.mpr ⟨k_off, ?_, ?_⟩, rfl⟩
  · rw [List.length_take, List.length_drop]; exact Nat.lt_min.mpr ⟨hsz, by omega⟩
  · rw [List.getElem_take, List.getElem_drop]
    exact Option.some.inj ((List.getElem?_eq_getElem hlen).symm.trans hget)

theorem mem_fullArenaClauseLitsCore_of_fit {k : FullCoreState} {cref l : Nat}
    (hfit : cref + 3 + fullArenaClauseSizeCore k cref ≤ k.arena.length)
    (hl : l ∈ fullArenaClauseLitsCore k cref) :
    ∃ k_off < fullArenaClauseSizeCore k cref,
      (k.arena[cref + 3 + k_off]?.getD 0#32).toNat = l := by
  unfold fullArenaClauseLitsCore at hl
  rw [List.mem_map] at hl
  obtain ⟨bv, hbv, rfl⟩ := hl
  obtain ⟨k_off, hk_lt, rfl⟩ := List.mem_iff_getElem.mp hbv
  rw [List.length_take, List.length_drop] at hk_lt
  have hk_sz : k_off < fullArenaClauseSizeCore k cref :=
    Nat.lt_of_lt_of_le hk_lt (Nat.min_le_left _ _)
  have hidx : cref + 3 + k_off < k.arena.length := by omega
  refine ⟨k_off, hk_sz, ?_⟩
  rw [List.getElem_take, List.getElem_drop, List.getElem?_eq_getElem hidx, Option.getD_some]

theorem fc_let_mul {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {a b : Arg Val i64} {va vb : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs}
    (ha : a.val = va) (hb : b.val = vb) (hk : wp Γ Q X (k (va * vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.mul i64) (a, b, ())) k) m := by
  cases ha; cases hb; exact hk

theorem fc_let_add {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {a b : Arg Val i64} {va vb : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs}
    (ha : a.val = va) (hb : b.val = vb) (hk : wp Γ Q X (k (va + vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.add i64) (a, b, ())) k) m := by
  cases ha; cases hb; exact hk

theorem m7_fastPropMem_with_vals (s0 sem : FullState) (vs' : List (BitVec 8)) :
    { fastPropMem s0 sem with core := { (fastPropMem s0 sem).core with vals := vs' } } =
      fastPropMem s0 { sem with core := { sem.core with vals := vs' } } :=
  fastPropMem_with_vals s0 sem vs'

theorem m7_fastPropMem_with_lvl (s0 sem : FullState) (lv' : List (BitVec 32)) :
    { fastPropMem s0 sem with core := { (fastPropMem s0 sem).core with lvl := lv' } } =
      fastPropMem s0 { sem with core := { sem.core with lvl := lv' } } :=
  fastPropMem_with_lvl s0 sem lv'

theorem m7_fastPropMem_with_rsns (s0 sem : FullState) (rs' : List (BitVec 32)) :
    { fastPropMem s0 sem with core := { (fastPropMem s0 sem).core with rsns := rs' } } =
      fastPropMem s0 { sem with core := { sem.core with rsns := rs' } } :=
  fastPropMem_with_rsns s0 sem rs'

theorem m7_fastPropMem_with_flags (s0 sem : FullState) (fl' : List (BitVec 32)) :
    { fastPropMem s0 sem with core := { (fastPropMem s0 sem).core with flags := fl' } } =
      fastPropMem s0 { sem with core := { sem.core with flags := fl' } } :=
  fastPropMem_with_flags s0 sem fl'

theorem m7_fastPropMem_with_phases (s0 sem : FullState) (ph' : List (BitVec 8)) :
    { fastPropMem s0 sem with
      scratch := { (fastPropMem s0 sem).scratch with phases := ph' } } =
      fastPropMem s0 { sem with scratch := { sem.scratch with phases := ph' } } :=
  fastPropMem_with_phases s0 sem ph'

theorem m7_fastPropMem_with_arena (s0 sem : FullState) (a' : List (BitVec 32)) :
    { fastPropMem s0 sem with core := { (fastPropMem s0 sem).core with arena := a' } } =
      fastPropMem s0 { sem with core := { sem.core with arena := a' } } :=
  fastPropMem_with_arena s0 sem a'

theorem m7_fastPropMem_with_confl_bin (s0 sem : FullState) (l0 l1 : BitVec 32) :
    { fastPropMem s0 sem with core := { (fastPropMem s0 sem).core with
        confl_type := 1#64, confl_lit0 := l0.setWidth 64, confl_lit1 := l1.setWidth 64 } } =
      fastPropMem s0 { sem with core := { sem.core with
        confl_type := 1#64, confl_lit0 := l0.setWidth 64, confl_lit1 := l1.setWidth 64 } } := by
  unfold fastPropMem; rfl

theorem m7_fastPropMem_with_confl_large (s0 sem : FullState) (cref : BitVec 32) :
    { fastPropMem s0 sem with core := { (fastPropMem s0 sem).core with
        confl_type := 2#64, confl_ref := cref.setWidth 64 } } =
      fastPropMem s0 { sem with core := { sem.core with
        confl_type := 2#64, confl_ref := cref.setWidth 64 } } := by
  unfold fastPropMem; rfl

theorem fid_fastPropMem_with_bin_confl (s0 sem : FullState) (l0 l1 : BitVec 32) :
    { fastPropMem s0 sem with core := { (fastPropMem s0 sem).core with
        confl_type := 1#64, confl_lit0 := l0.setWidth 64, confl_lit1 := l1.setWidth 64 } } =
      fastPropMem s0 { sem with core := { sem.core with
        confl_type := 1#64, confl_lit0 := l0.setWidth 64, confl_lit1 := l1.setWidth 64 } } :=
  m7_fastPropMem_with_confl_bin s0 sem l0 l1

theorem m7_trail_end_lt_of_unassigned {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    {l : Nat} (hl : l < 2 * k.cur_vars) (hun : k.vals[l]?.getD 0#8 = 0#8) :
    k.trail_end < k.cur_vars :=
  hw.trail_end_lt_of_unassigned hl hun

theorem m7_arenaPermEq_congr {k1 k2 k1' k2' : FullCoreState}
    (h1 : k1'.arena = k1.arena) (h1l : k1'.arena_len = k1.arena_len)
    (h2 : k2'.arena = k2.arena) (h2l : k2'.arena_len = k2.arena_len)
    (hp : FullArenaPermEq k1 k2) : FullArenaPermEq k1' k2' := by
  have hsz1 : ∀ r, fullArenaClauseSizeCore k1' r = fullArenaClauseSizeCore k1 r := fun r => by
    unfold fullArenaClauseSizeCore; rw [h1]
  have hsz2 : ∀ r, fullArenaClauseSizeCore k2' r = fullArenaClauseSizeCore k2 r := fun r => by
    unfold fullArenaClauseSizeCore; rw [h2]
  have hgb1 : ∀ r, fullArenaClauseGarbCore k1' r = fullArenaClauseGarbCore k1 r := fun r => by
    unfold fullArenaClauseGarbCore fullArenaHdrCore; rw [h1]
  have hgb2 : ∀ r, fullArenaClauseGarbCore k2' r = fullArenaClauseGarbCore k2 r := fun r => by
    unfold fullArenaClauseGarbCore fullArenaHdrCore; rw [h2]
  have hrf1 : fullArenaClauseRefsCore k1' = fullArenaClauseRefsCore k1 := by
    unfold fullArenaClauseRefsCore; rw [h1, h1l]
  have hrf2 : fullArenaClauseRefsCore k2' = fullArenaClauseRefsCore k2 := by
    unfold fullArenaClauseRefsCore; rw [h2, h2l]
  have hlt1 : ∀ r, fullArenaClauseLitsCore k1' r = fullArenaClauseLitsCore k1 r := fun r => by
    unfold fullArenaClauseLitsCore; rw [h1, hsz1 r]
  have hlt2 : ∀ r, fullArenaClauseLitsCore k2' r = fullArenaClauseLitsCore k2 r := fun r => by
    unfold fullArenaClauseLitsCore; rw [h2, hsz2 r]
  refine ⟨by rw [h2l, h1l]; exact hp.1, by rw [hrf2, hrf1]; exact hp.2.1, fun r hr => ?_⟩
  rw [hrf1] at hr
  obtain ⟨hs, hg, hpm⟩ := hp.2.2 r hr
  exact ⟨by rw [hsz2, hsz1]; exact hs, by rw [hgb2, hgb1]; exact hg,
    by rw [hlt2, hlt1]; exact hpm⟩

theorem m7_fullConflOkW_of_perm {F_cur : List (List Nat)} {k k' : FullCoreState}
    (hp : FullArenaPermEq k k') (hcv : k'.cur_vars = k.cur_vars) (hvals : k'.vals = k.vals)
    (hct : k'.confl_type = k.confl_type) (hcr : k'.confl_ref = k.confl_ref)
    (hc0 : k'.confl_lit0 = k.confl_lit0) (hc1 : k'.confl_lit1 = k.confl_lit1)
    (hc : FullConflOkW F_cur k) : FullConflOkW F_cur k' := by
  rcases hc with ⟨ht1, h0, h1, hent, hv0, hv1⟩ | ⟨ht2, href, hng, hlits⟩
  · exact Or.inl ⟨hct.trans ht1, hcv ▸ hc0 ▸ h0, hcv ▸ hc1 ▸ h1,
      hc0 ▸ hc1 ▸ hent, hvals ▸ hc0 ▸ hv0, hvals ▸ hc1 ▸ hv1⟩
  · have href' : k'.confl_ref.toNat ∈ fullArenaClauseRefsCore k' := by
      rw [hcr, hp.2.1]; exact href
    refine Or.inr ⟨hct.trans ht2, href', ?_, fun l hl => ?_⟩
    · rw [hcr, (hp.2.2 k.confl_ref.toNat href).2.1]; exact hng
    · rw [hcr] at hl
      have hm := (hp.2.2 k.confl_ref.toNat href).2.2.mem_iff.mp hl
      rw [hvals]; exact hlits l hm

theorem fid_pi_delayed_eq {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_orig sem : FullState} {not_lit off_v q_v p_v end_v : Nat}
    (h : PropLitInv c F0 F_cur s_orig sem not_lit off_v q_v p_v end_v) :
    sem.scratch.delayed = s_orig.scratch.delayed := by
  have hs := h.sc_eq; rw [hs]

theorem s13_pi_rebase_del {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {del' : List (BitVec 32)} {not_lit off_v q_v p_v end_v : Nat}
    (h : PropLitInv c F0 F_cur { s0 with scratch := { s0.scratch with delayed := del' } }
      st not_lit off_v q_v p_v end_v)
    (hdel : st.scratch.delayed = del') :
    PropLitInv c F0 F_cur
      { s0 with scratch := { s0.scratch with delayed := st.scratch.delayed } }
      st not_lit off_v q_v p_v end_v := by
  rw [hdel]; exact h

/-! ## 2. `PropLitInv` & `PropLitConfl` Transitions -/

theorem PropLitConfl.congr {F_cur : List (List Nat)} {ign : BitVec 64} {k k' : FullCoreState}
    (hc : PropLitConfl F_cur ign k) (hp : FullArenaPermEq k k')
    (hcv : k'.cur_vars = k.cur_vars) (hvals : k'.vals = k.vals)
    (hct : k'.confl_type = k.confl_type) (hcr : k'.confl_ref = k.confl_ref)
    (hc0 : k'.confl_lit0 = k.confl_lit0) (hc1 : k'.confl_lit1 = k.confl_lit1) :
    PropLitConfl F_cur ign k' :=
  ⟨m7_fullConflOkW_of_perm hp hcv hvals hct hcr hc0 hc1 hc.1,
    fun h2 => by rw [hcr]; exact hc.2 (hct ▸ h2)⟩

theorem propLit_vals_neg {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (_hnw : FullWitnessInv c F0 F_cur k)
    {l : BitVec 32} (_hl : l.toNat < 2 * k.cur_vars) (hf : k.vals[l.toNat]?.getD 0#8 = 0xFF#8) :
    ((k.vals[l.toNat]?.getD 0#8).signExtend 32).slt 0#32 = true := by
  rw [hf]; decide

theorem propLit_vals_un {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hnw : FullWitnessInv c F0 F_cur k)
    {l : Nat} (hl : l < 2 * k.cur_vars)
    (hs1 : ((k.vals[l]?.getD 0#8).signExtend 32).slt 0#32 = false)
    (hs2 : (0#32).slt ((k.vals[l]?.getD 0#8).signExtend 32) = false) :
    k.vals[l]?.getD 0#8 = 0#8 :=
  i8_vals_eq0_of_not_pos_neg (hnw.vals_domain l hl) hs2 hs1

theorem propLit_inv_drop {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {not_lit off q p step end_v : Nat}
    (hpi : PropLitInv c F0 F_cur s st not_lit off q p end_v)
    (hp : p ≤ p + step) (hp' : p + step ≤ end_v)
    (hrem : WatchSliceOk F_cur st.core not_lit (p + step) (end_v - (p + step))) :
    PropLitInv c F0 F_cur s st not_lit off q (p + step) end_v :=
  { hpi with sw := SplitWatchesInv.advance_rem hpi.sw hp hp' hrem }

theorem propLit_inv_keep_large {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {not_lit off q p end_v : Nat} {w0 cref : BitVec 32}
    (hpi : PropLitInv c F0 F_cur s st not_lit off q (p + 2) end_v)
    (hnot_lt : not_lit < 2 * st.core.cur_vars) (hqp : q ≤ p)
    (_hq_lt : q < st.core.wstk.length) (hq1_lt : q + 1 < st.core.wstk.length)
    (hflag : (w0 &&& 0x80000000#32) = 0#32)
    (hcr_lt : cref.toNat < 0x80000000) (hcref : cref.toNat ∈ fullArenaClauseRefsCore st.core) :
    PropLitInv c F0 F_cur s
      { st with core := { st.core with wstk := (st.core.wstk.set q w0).set (q + 1) cref } }
      not_lit off (q + 2) (p + 2) end_v := by
  have hst' : ({ st with core := { st.core with
      wstk := (st.core.wstk.set q w0).set (q + 1) cref } }).LengthsOk c :=
    ⟨{ hpi.len.core_ok with wstk_len_arr := by simp [hpi.len.core_ok.wstk_len_arr] },
     hpi.len.scratch_ok⟩
  have hnw' : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c
      { st.core with wstk := (st.core.wstk.set q w0).set (q + 1) cref }) :=
    fullWitnessInv_nw_congr hpi.len.core_ok.cur_vars_le hpi.nw
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  exact
    { len := hst', nw := hnw'
      sw := SplitWatchesInv.write_large hpi.sw hnot_lt (by omega) hq1_lt hflag hcr_lt hcref
      ag := hpi.ag.update (fun k => { k with wstk := (st.core.wstk.set q w0).set (q + 1) cref })
      tr := hpi.tr, rsns_pres := hpi.rsns_pres, perm := hpi.perm,
      sc_eq := hpi.sc_eq, not_f := hpi.not_f }

theorem propLit_bin_confl {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {not_lit off q p end_v : Nat} {not_lit_v other_v : BitVec 32}
    (hpi : PropLitInv c F0 F_cur s st not_lit off q p end_v)
    (hnot_eq : not_lit_v.toNat = not_lit) (hnot_lt : not_lit < 2 * st.core.cur_vars)
    (hother_lt : other_v.toNat < 2 * st.core.cur_vars)
    (hother_f : st.core.vals[other_v.toNat]?.getD 0#8 = 0xFF#8)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [not_lit, other_v.toNat])) :
    let st' : FullState := { st with core := { st.core with
      confl_type := 1#64, confl_lit0 := not_lit_v.setWidth 64,
      confl_lit1 := other_v.setWidth 64 } }
    PropLitInv c F0 F_cur s st' not_lit off q p end_v ∧
    FullConflOkW F_cur st'.core ∧
    (st'.core.confl_type = 2#64 → st'.core.confl_ref ≠ 0#64) := by
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv := hpi.len.core_ok.cur_vars_le
  have hc0 : (not_lit_v.setWidth 64).toNat = not_lit := by
    rw [bv_c0_zext32_64, hnot_eq]
  have hc1 : (other_v.setWidth 64).toNat = other_v.toNat := bv_c0_zext32_64 other_v
  let kc' : FullCoreState :=
    { st.core with
      confl_type := 1#64, confl_lit0 := not_lit_v.setWidth 64,
      confl_lit1 := other_v.setWidth 64 }
  have hnw' : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c kc') :=
    fullWitnessInv_nw_congr hcv hpi.nw rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  refine ⟨{ len := ⟨{ hpi.len.core_ok with cur_vars_le := hpi.len.core_ok.cur_vars_le },
              hpi.len.scratch_ok⟩,
            nw := hnw',
            sw := SplitWatchesInv.with_nonwatch hpi.sw rfl rfl rfl rfl (fun _ hr => hr),
            ag := hpi.ag.update (fun k =>
              { k with
                confl_type := 1#64, confl_lit0 := not_lit_v.setWidth 64,
                confl_lit1 := other_v.setWidth 64 }),
            tr := hpi.tr, rsns_pres := hpi.rsns_pres, perm := hpi.perm,
            sc_eq := hpi.sc_eq, not_f := hpi.not_f },
    ?_, fun h => by cases h⟩
  exact Or.inl ⟨rfl, hc0 ▸ hnot_lt, hc1 ▸ hother_lt, hc0 ▸ hc1 ▸ hent,
    hc0 ▸ hpi.not_f, hc1 ▸ hother_f⟩

theorem propLit_large_confl {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {not_lit off q p end_v : Nat} {cref : BitVec 32}
    (hpi : PropLitInv c F0 F_cur s st not_lit off q p end_v)
    (hcr_ref : cref.toNat ∈ fullArenaClauseRefsCore st.core)
    (hng : fullArenaClauseGarbCore st.core cref.toNat = false)
    (hfals : ∀ l ∈ fullArenaClauseLitsCore st.core cref.toNat,
      st.core.vals[l]?.getD 0#8 = 0xFF#8) :
    let st' : FullState := { st with core := { st.core with
      confl_type := 2#64, confl_ref := cref.setWidth 64 } }
    PropLitInv c F0 F_cur s st' not_lit off q p end_v ∧ FullConflOkW F_cur st'.core := by
  have hcr64 : (cref.setWidth 64).toNat = cref.toNat := bv_c0_zext32_64 cref
  have hnw' : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c
      { st.core with confl_type := 2#64, confl_ref := cref.setWidth 64 }) :=
    fullWitnessInv_nw_congr hpi.len.core_ok.cur_vars_le hpi.nw
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  refine ⟨{ len := ⟨{ hpi.len.core_ok with cur_vars_le := hpi.len.core_ok.cur_vars_le },
              hpi.len.scratch_ok⟩,
            nw := hnw',
            sw := SplitWatchesInv.with_nonwatch hpi.sw rfl rfl rfl rfl (fun _ hr => hr),
            ag := hpi.ag.update (fun k =>
              { k with confl_type := 2#64, confl_ref := cref.setWidth 64 }),
            tr := hpi.tr, rsns_pres := hpi.rsns_pres, perm := hpi.perm,
            sc_eq := hpi.sc_eq, not_f := hpi.not_f },
    Or.inr ⟨rfl, hcr64 ▸ hcr_ref, hcr64 ▸ hng, fun l hl => hfals l (hcr64 ▸ hl)⟩⟩

theorem propLit_hunit {_F_cur : List (List Nat)} {k : FullCoreState}
    {cref : Nat} {other not_lit : Nat}
    (hrw0 : k.arena[cref + 3]? = some (BitVec.ofNat 32 other) ∨
      k.arena[cref + 3]? = some (BitVec.ofNat 32 not_lit))
    (hrw1 : k.arena[cref + 4]? = some (BitVec.ofNat 32 not_lit) ∨
      k.arena[cref + 4]? = some (BitVec.ofNat 32 other))
    (_hsize : 3 ≤ fullArenaClauseSizeCore k cref)
    (hfit : cref + 3 + fullArenaClauseSizeCore k cref ≤ k.arena.length)
    (hnot_f : k.vals[not_lit]?.getD 0#8 = 0xFF#8)
    (htail_f : ∀ i, 2 ≤ i → i < fullArenaClauseSizeCore k cref →
      (k.vals[(k.arena[cref + 3 + i]?.getD 0#32).toNat]?.getD 0#8) = 0xFF#8)
    (hother_lt : other < 2 ^ 32) (hnot_lt : not_lit < 2 ^ 32) :
    ∀ l ∈ fullArenaClauseLitsCore k cref, l = other ∨ k.vals[l]?.getD 0#8 = 0xFF#8 := by
  intro l hl
  obtain ⟨k_off, hk_mem, rfl⟩ := mem_fullArenaClauseLitsCore_of_fit hfit hl
  rcases Nat.lt_trichotomy k_off 1 with hk0 | hk1 | hk2
  · have hkz : k_off = 0 := by omega
    subst hkz
    simp only [Nat.add_zero]
    rcases hrw0 with h0 | h0
    · rw [h0, Option.getD_some, bv32_ofNat_toNat hother_lt]; exact Or.inl rfl
    · rw [h0, Option.getD_some, bv32_ofNat_toNat hnot_lt]; exact Or.inr hnot_f
  · subst hk1
    rcases hrw1 with h1 | h1
    · rw [h1, Option.getD_some, bv32_ofNat_toNat hnot_lt]; exact Or.inr hnot_f
    · rw [h1, Option.getD_some, bv32_ofNat_toNat hother_lt]; exact Or.inl rfl
  · exact Or.inr (htail_f k_off hk2 hk_mem)

theorem propLit_measure_lt {p step end_v : Nat} (hstep : 0 < step) (hp : p + step ≤ end_v) :
    end_v - (p + step) < end_v - p := by omega

theorem SplitWatchesInv.after_push {c : FullCfg} {F_cur : List (List Nat)}
    {k k' : FullCoreState} {not_lit off q p end_v lit w0 cref : Nat}
    (h : SplitWatchesInv F_cur k not_lit off q p end_v)
    (_hcv : k.cur_vars ≤ c.max_vars) (hnot_lt : not_lit < 2 * k.cur_vars)
    (_hlit_lt : lit < 2 * k.cur_vars) (hne : lit ≠ not_lit)
    (hk' : k'.cur_vars = k.cur_vars)
    (hrefs : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k)
    (hlay' : WatchStackLayout k')
    (hpres_o : ∀ l < 2 * k.cur_vars, l ≠ lit →
      fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ idx < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k' l + idx]? = k.wstk[fullWatchOffCore k l + idx]?)
    (hpush : fullWatchSizeCore k' lit = fullWatchSizeCore k lit + 2 ∧
      (∀ idx < fullWatchSizeCore k lit,
        k'.wstk[fullWatchOffCore k' lit + idx]? = k.wstk[fullWatchOffCore k lit + idx]?) ∧
      k'.wstk[fullWatchOffCore k' lit + fullWatchSizeCore k lit]? = some (BitVec.ofNat 32 w0) ∧
      k'.wstk[fullWatchOffCore k' lit + fullWatchSizeCore k lit + 1]? =
        some (BitVec.ofNat 32 cref))
    (hw0_flag : (BitVec.ofNat 32 w0 &&& 0x80000000#32) = 0#32)
    (hcr_lt : cref < 0x80000000) (hcref : cref ∈ fullArenaClauseRefsCore k') :
    let off' := fullWatchOffCore k' not_lit
    SplitWatchesInv F_cur k' not_lit off'
      (off' + (q - off)) (off' + (p - off)) (off' + (end_v - off)) := by
  have hF : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ hx => hx
  have hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k' :=
    fun _ hr => hrefs ▸ hr
  have ⟨hsz_not, hpre_not⟩ := hpres_o not_lit hnot_lt hne.symm
  rw [h.off_eq, h.sz_eq] at hpre_not
  have hq_ge := h.q_ge; have hq_le := h.q_le_p; have hp_le := h.p_le_end
  intro off'
  refine
    { layout := hlay', off_eq := rfl
      sz_eq := by rw [hsz_not, h.sz_eq]; omega
      sz_pos := by have := h.sz_pos; omega
      q_ge := by omega, q_le_p := by omega, p_le_end := by omega
      other_slices := fun l hl hnl => by
        have hl0 : l < 2 * k.cur_vars := hk' ▸ hl
        by_cases hll : l = lit
        · subst l; rw [hpush.1]
          exact watchSlice_append_large (k := k) (k' := k') (by omega) hsub hpush.2.1
            (h.other_slices lit hl0 hnl) hpush.2.2.1 hpush.2.2.2 hw0_flag
            (by rw [bv32_ofNat_toNat (by omega)]; exact hcr_lt)
            (by rw [bv32_ofNat_toNat (by omega)]; exact hcref)
        · obtain ⟨hsz_l, hpre_l⟩ := hpres_o l hl0 hll
          rw [hsz_l]
          exact watchSlice_relocate (k := k) (k' := k') hF (by omega) hsub hpre_l
            (h.other_slices l hl0 hnl)
      kept_slice := by
        rw [show off' + (q - off) - off' = q - off by omega]
        exact watchSlice_relocate (k := k) (k' := k') hF (by omega) hsub
          (fun j hj => hpre_not j (by omega)) h.kept_slice
      rem_slice := by
        rw [show off' + (end_v - off) - (off' + (p - off)) = end_v - p by omega]
        refine watchSlice_relocate (k := k) (k' := k') hF (by omega) hsub (fun j hj => ?_)
          h.rem_slice
        have hj' := hpre_not ((p - off) + j) (by omega)
        rwa [show off' + (p - off + j) = off' + (p - off) + j by omega,
          show off + (p - off + j) = p + j by omega] at hj' }

theorem propLit_b1_after_push {c : FullCfg} {F_cur : List (List Nat)}
    {st3 st4 : FullState} {lit other cref repl : BitVec 32}
    {off_v p_v q_v end_v : BitVec 64} {pok : Bool} {idx0 : Nat}
    (hnot_lt : (lit ^^^ 1#32).toNat < 2 * st3.core.cur_vars)
    (hcv4 : st4.core.cur_vars = st3.core.cur_vars)
    (hnot_lt4 : (lit ^^^ 1#32).toNat < 2 * st4.core.cur_vars)
    (hlen4 : st4.LengthsOk c) (hlay4 : WatchStackLayout st4.core)
    (hsw3 : SplitWatchesInv F_cur st3.core (lit ^^^ 1#32).toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat)
    (href4 : fullArenaClauseRefsCore st4.core = fullArenaClauseRefsCore st3.core)
    (hrepl_lt : repl.toNat < 2 * st3.core.cur_vars)
    (hrepl_ne : repl.toNat ≠ (lit ^^^ 1#32).toNat)
    (hcr_lt : cref.toNat < 0x80000000)
    (hcr_ref3 : cref.toNat ∈ fullArenaClauseRefsCore st3.core)
    (hp2_nat : (p_v + 1#64 + 1#64).toNat = p_v.toNat + 2) (hq_le : q_v.toNat ≤ p_v.toNat)
    (hoth_pres : ∀ l < 2 * st3.core.cur_vars, l ≠ repl.toNat →
      fullWatchSizeCore st4.core l = fullWatchSizeCore st3.core l ∧
      ∀ idx < fullWatchSizeCore st3.core l,
        st4.core.wstk[fullWatchOffCore st4.core l + idx]? =
          st3.core.wstk[fullWatchOffCore st3.core l + idx]?)
    (hpok_t : pok = true →
      fullWatchSizeCore st4.core repl.toNat = fullWatchSizeCore st3.core repl.toNat + 2 ∧
      (∀ idx < fullWatchSizeCore st3.core repl.toNat,
        st4.core.wstk[fullWatchOffCore st4.core repl.toNat + idx]? =
          st3.core.wstk[fullWatchOffCore st3.core repl.toNat + idx]?) ∧
      st4.core.wstk[fullWatchOffCore st4.core repl.toNat +
        fullWatchSizeCore st3.core repl.toNat]? = some (other &&& 0x7FFFFFFF#32) ∧
      st4.core.wstk[fullWatchOffCore st4.core repl.toNat +
        fullWatchSizeCore st3.core repl.toNat + 1]? = some cref)
    (hpok_f : pok = false →
      fullWatchSizeCore st4.core repl.toNat = fullWatchSizeCore st3.core repl.toNat ∧
      ∀ idx < fullWatchSizeCore st3.core repl.toNat,
        st4.core.wstk[fullWatchOffCore st4.core repl.toNat + idx]? =
          st3.core.wstk[fullWatchOffCore st3.core repl.toNat + idx]?)
    (hidx0 : idx0 = 2 * (lit ^^^ 1#32).toNat) :
    let off4_v := BitVec.setWidth 64 (st4.core.wvec[idx0]?.getD 0#32)
    let q4_v := off4_v + (q_v - off_v)
    let p4_v := off4_v + (p_v + 1#64 + 1#64 - off_v)
    let end4_v := off4_v + (end_v - off_v)
    off4_v.toNat = fullWatchOffCore st4.core (lit ^^^ 1#32).toNat ∧
    q4_v.toNat = off4_v.toNat + (q_v.toNat - off_v.toNat) ∧
    p4_v.toNat = off4_v.toNat + (p_v.toNat + 2 - off_v.toNat) ∧
    end4_v.toNat = off4_v.toNat + (end_v.toNat - off_v.toNat) ∧
    q4_v.toNat + 2 ≤ p4_v.toNat ∧ p4_v.toNat ≤ end4_v.toNat ∧
    (off4_v.toNat + (end_v.toNat - off_v.toNat) ≤ c.wcap ∧ c.wcap < 2 ^ 64) ∧
    SplitWatchesInv F_cur st4.core (lit ^^^ 1#32).toNat off4_v.toNat q4_v.toNat p4_v.toNat
      end4_v.toNat := by
  subst hidx0
  have hwc := c.hwcap; unfold dimacsBound at hwc
  have hbd4 := hlay4.bounds (lit ^^^ 1#32).toNat hnot_lt4
  have hwc64 : c.wcap < 2 ^ 64 := Nat.lt_trans hwc (by decide)
  have hsw4 : let off4 := fullWatchOffCore st4.core (lit ^^^ 1#32).toNat
      SplitWatchesInv F_cur st4.core (lit ^^^ 1#32).toNat off4
        (off4 + (q_v.toNat - off_v.toNat)) (off4 + (p_v.toNat + 2 - off_v.toNat))
        (off4 + (end_v.toNat - off_v.toNat)) := by
    cases pok
    · have hF : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
        rw [CNF.entails_def]; exact fun _ hx => hx
      have ⟨hsz_n, hpre_n⟩ := hoth_pres _ hnot_lt hrepl_ne.symm
      rw [hsw3.off_eq, hsw3.sz_eq] at hpre_n
      have hq_ge := hsw3.q_ge; have hq_le' := hsw3.q_le_p; have hp_le := hsw3.p_le_end
      have hsub : ∀ r ∈ fullArenaClauseRefsCore st3.core, r ∈ fullArenaClauseRefsCore st4.core :=
        fun _ hr => href4 ▸ hr
      intro off4
      refine
        { layout := hlay4, off_eq := rfl
          sz_eq := by rw [hsz_n, hsw3.sz_eq]; omega
          sz_pos := by have := hsw3.sz_pos; omega
          q_ge := by omega, q_le_p := by omega, p_le_end := by omega
          other_slices := fun l hl hnl => by
            have hl0 : l < 2 * st3.core.cur_vars := hcv4 ▸ hl
            have hstep := if hll : l = repl.toNat then hll ▸ hpok_f rfl else hoth_pres l hl0 hll
            rw [hstep.1]
            exact watchSlice_relocate (k := st3.core) (k' := st4.core) hF (by omega) hsub
              hstep.2 (hsw3.other_slices l hl0 hnl)
          kept_slice := by
            rw [show off4 + (q_v.toNat - off_v.toNat) - off4 = q_v.toNat - off_v.toNat by omega]
            exact watchSlice_relocate (k := st3.core) (k' := st4.core) hF (by omega) hsub
              (fun j hj => hpre_n j (by omega)) hsw3.kept_slice
          rem_slice := by
            rw [show off4 + (end_v.toNat - off_v.toNat) -
                (off4 + (p_v.toNat + 2 - off_v.toNat)) = end_v.toNat - (p_v.toNat + 2) by omega]
            refine watchSlice_relocate (k := st3.core) (k' := st4.core) hF (by omega) hsub
              (fun j hj => ?_) hsw3.rem_slice
            have hj' := hpre_n ((p_v.toNat + 2 - off_v.toNat) + j) (by omega)
            rwa [show off4 + (p_v.toNat + 2 - off_v.toNat + j) =
                off4 + (p_v.toNat + 2 - off_v.toNat) + j by omega,
              show off_v.toNat + (p_v.toNat + 2 - off_v.toNat + j) =
                (p_v.toNat + 2) + j by omega] at hj' }
    · obtain ⟨hsz, hpre, hw0, hw1⟩ := hpok_t rfl
      refine SplitWatchesInv.after_push hsw3 (c := c) (w0 := (other &&& 0x7FFFFFFF#32).toNat)
        (by rw [← hcv4]; exact hlen4.core_ok.cur_vars_le)
        hnot_lt hrepl_lt hrepl_ne hcv4 href4 hlay4 hoth_pres ⟨hsz, hpre, ?_, ?_⟩ ?_ hcr_lt
        (href4 ▸ hcr_ref3)
      · simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hw0
      · simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hw1
      · simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
          bv32_mask7f_flag0 other
  have hsz_eq4 := hsw4.sz_eq
  have hq_ge3 := hsw3.q_ge; have hp_le3 := hsw3.p_le_end
  have hend4_le : fullWatchOffCore st4.core (lit ^^^ 1#32).toNat +
      (end_v.toNat - off_v.toNat) ≤ c.wcap := by
    have := hlen4.core_ok.wlen_le; omega
  have hoff4_n : (BitVec.setWidth 64 (st4.core.wvec[2 * (lit ^^^ 1#32).toNat]?.getD 0#32)).toNat =
      fullWatchOffCore st4.core (lit ^^^ 1#32).toNat := by
    rw [bv_c0_zext32_64]; rfl
  have hq4_n : (BitVec.setWidth 64 (st4.core.wvec[2 * (lit ^^^ 1#32).toNat]?.getD 0#32) +
      (q_v - off_v)).toNat =
      fullWatchOffCore st4.core (lit ^^^ 1#32).toNat + (q_v.toNat - off_v.toNat) := by
    rw [m7_bv64_add_toNat, hoff4_n, m7_bv64_sub_toNat hq_ge3]
    rw [hoff4_n, m7_bv64_sub_toNat hq_ge3]; omega
  have hp4_n : (BitVec.setWidth 64 (st4.core.wvec[2 * (lit ^^^ 1#32).toNat]?.getD 0#32) +
      (p_v + 1#64 + 1#64 - off_v)).toNat =
      fullWatchOffCore st4.core (lit ^^^ 1#32).toNat + (p_v.toNat + 2 - off_v.toNat) := by
    rw [m7_bv64_add_toNat, hoff4_n, m7_bv64_sub_toNat (by omega), hp2_nat]
    rw [hoff4_n, m7_bv64_sub_toNat (by omega), hp2_nat]; omega
  have hend4_n : (BitVec.setWidth 64 (st4.core.wvec[2 * (lit ^^^ 1#32).toNat]?.getD 0#32) +
      (end_v - off_v)).toNat =
      fullWatchOffCore st4.core (lit ^^^ 1#32).toNat + (end_v.toNat - off_v.toNat) := by
    rw [m7_bv64_add_toNat, hoff4_n, m7_bv64_sub_toNat (by omega)]
    rw [hoff4_n, m7_bv64_sub_toNat (by omega)]; omega
  refine ⟨hoff4_n, by rw [hoff4_n]; exact hq4_n, by rw [hoff4_n]; exact hp4_n,
    by rw [hoff4_n]; exact hend4_n, by omega, by omega, ⟨hend4_le, hwc64⟩, ?_⟩
  rw [hoff4_n, hq4_n, hp4_n, hend4_n]; exact hsw4

theorem propLit_loop2_step {off q p pc end_v wc : Nat} {wstk : List (BitVec 32)}
    {wstk0 : List (BitVec 32)}
    (hq_ge : off ≤ q) (hq_le : q ≤ p) (hp_pc : p ≤ pc) (hpc_lt : pc < end_v)
    (hpc_w : pc < wstk.length) (hqc_w : q + (pc - p) < wstk.length)
    (hpre : ∀ k, off ≤ k → k < q → wstk[k]? = wstk0[k]?)
    (hsuf : ∀ k < pc - p, wstk[q + k]? = wstk0[p + k]?)
    (hrem : ∀ k, pc ≤ k → k < end_v → wstk[k]? = wstk0[k]?)
    (hout : ∀ k, (k < off ∨ end_v ≤ k) → wstk[k]? = wstk0[k]?) :
    let qc := q + (pc - p)
    let wstk' := wstk.set qc (wstk[pc]'hpc_w)
    (∀ k, off ≤ k → k < q → wstk'[k]? = wstk0[k]?) ∧
    (∀ k < (pc + 1) - p, wstk'[q + k]? = wstk0[p + k]?) ∧
    (∀ k, pc + 1 ≤ k → k < end_v → wstk'[k]? = wstk0[k]?) ∧
    (∀ k, (k < off ∨ end_v ≤ k) → wstk'[k]? = wstk0[k]?) := by
  have _ := wc
  intro qc wstk'
  have hqc_le_pc : qc ≤ pc := by omega
  refine ⟨fun k hk1 hk2 => ?_, fun k hk => ?_, fun k hk1 hk2 => ?_, fun k hk => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hpre k hk1 hk2
  · by_cases hkc : k = pc - p
    · subst hkc
      rw [show q + (pc - p) = qc from rfl, List.getElem?_set_self hqc_w,
        show p + (pc - p) = pc by omega]
      exact (List.getElem?_eq_getElem hpc_w).symm.trans (hrem pc (Nat.le_refl _) hpc_lt)
    · rw [List.getElem?_set_ne (by omega)]; exact hsuf k (by omega)
  · rw [List.getElem?_set_ne (by omega)]; exact hrem k (by omega) hk2
  · rw [List.getElem?_set_ne (by omega)]; exact hout k hk

theorem propLit_loop3_step {qc k end_v : Nat} {wstk wstk0 : List (BitVec 32)}
    (hq_k : qc ≤ k) (hk_lt : k < end_v)
    (hkeep : ∀ i, (i < qc ∨ end_v ≤ i) → wstk[i]? = wstk0[i]?) :
    ∀ i, (i < qc ∨ end_v ≤ i) → (wstk.set k 0xFFFFFFFF#32)[i]? = wstk0[i]? := fun i hi => by
  rw [List.getElem?_set_ne (by omega)]; exact hkeep i hi

/-! ## 3. Step-13 Inner-Loop State Helpers -/

abbrev S13ConflEq (k1 k2 : FullCoreState) : Prop :=
  k2.confl_type = k1.confl_type ∧ k2.confl_ref = k1.confl_ref ∧
  k2.confl_lit0 = k1.confl_lit0 ∧ k2.confl_lit1 = k1.confl_lit1

theorem s13ConflEq_trans {k1 k2 k3 : FullCoreState}
    (h23 : S13ConflEq k2 k3) (h12 : S13ConflEq k1 k2) : S13ConflEq k1 k3 :=
  ⟨h23.1.trans h12.1, h23.2.1.trans h12.2.1, h23.2.2.1.trans h12.2.2.1,
   h23.2.2.2.trans h12.2.2.2⟩

abbrev s13OvfSig (isBeyond : Bool) : List Ty :=
  if isBeyond then [i64, i64, i64, i64, i64, i64, i64, Ty.bool, i32, i32, i32, i64]
  else [i64, i64, i64, i64, i64, i64, i64, i64, Ty.bool, i32, i32, i32, i64]

abbrev s13OvfJump {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (isBeyond : Bool) (J_ovf : L (s13OvfSig isBeyond))
    (te un uf tk p q di brk : Arg V i64) (ovf : Arg V Ty.bool)
    (rw oth cr : Arg V i32) (ri : Arg V i64) : Expr V L rs :=
  match isBeyond, J_ovf with
  | true, Jo => Expr.jump Jo (te, un, uf, tk, p, q, di, ovf, rw, oth, cr, ri, ())
  | false, Jo => Expr.jump Jo (te, un, uf, tk, p, q, di, brk, ovf, rw, oth, cr, ri, ())

theorem s13_bin_jumpreason_nw_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hlen : k.LengthsOk c)
    (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k))
    {not_lit other alvl : BitVec 32} {flags' : List (BitVec 32)} {unas' unfl' : BitVec 64}
    (hnot_lt : not_lit.toNat < 2 * k.cur_vars) (hother_lt : other.toNat < 2 * k.cur_vars)
    (hun : k.vals[other.toNat]?.getD 0#8 = 0#8)
    (hnot_false : k.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8)
    (halvl_le : alvl.toNat ≤ k.cur_level)
    (hnl_le : (k.lvl[not_lit.toNat / 2]?.getD 0#32).toNat ≤ alvl.toNat)
    (hnl0_iff : alvl = 0#32 ↔ k.lvl[not_lit.toNat / 2]?.getD 0#32 = 0#32)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [not_lit.toNat, other.toNat])) :
    let bin_rsn := (not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    let v := other.toNat / 2
    let rsn' := if alvl = 0#32 then 0xFFFFFFFF#32 else bin_rsn
    let k' : FullCoreState :=
      { k with
        vals := (k.vals.set other.toNat 1#8).set (other.toNat ^^^ 1) 0xFF#8
        flags := flags', lvl := k.lvl.set v alvl, rsns := k.rsns.set v rsn'
        trl := k.trl.set k.trail_end other
        trail_pos := k.trail_pos.set v (BitVec.ofNat 32 k.trail_end)
        trail_end := k.trail_end + 1, unassigned := unas', unflushed := unfl' }
    FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k') ∧
    k'.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8 ∧ FullTrailExt k k' ∧
    FullTrailRsnsPres k k' := by
  have hstep := full_bin_assign_nw_step hlen hnw halvl_le hother_lt hun hnot_lt hnot_false hent
    hnl_le hnl0_iff flags' unas' unfl'
  have hnf : ({ k with
      vals := (k.vals.set other.toNat 1#8).set (other.toNat ^^^ 1) 0xFF#8
      flags := flags', lvl := k.lvl.set (other.toNat / 2) alvl
      rsns := k.rsns.set (other.toNat / 2)
        (if alvl = 0#32 then 0xFFFFFFFF#32 else (not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32)
      trl := k.trl.set k.trail_end other
      trail_pos := k.trail_pos.set (other.toNat / 2) (BitVec.ofNat 32 k.trail_end)
      trail_end := k.trail_end + 1, unassigned := unas', unflushed := unfl' } :
      FullCoreState).vals[not_lit.toNat]?.getD 0#8 = 0xFF#8 := by
    have hnot_ne1 : not_lit.toNat ≠ other.toNat := fun heq => by
      rw [heq, hun] at hnot_false; cases hnot_false
    have hnot_ne2 : not_lit.toNat ≠ other.toNat ^^^ 1 := fun heq => by
      have hinv := (hnw.vals_false_iff not_lit.toNat hnot_lt).mp hnot_false
      obtain ⟨j, hj, hjeq⟩ := hinv
      dsimp only [withEmptyWatchesCore] at hjeq
      have hx : (k.trl[j]?.getD 0#32).toNat = other.toNat := by
        rw [hjeq, heq, Nat.xor_assoc]; simp
      have htr : k.vals[(k.trl[j]?.getD 0#32).toNat]?.getD 0#8 = 1#8 :=
        (hnw.vals_true_iff _ (hnw.trail_lits_lt j hj)).mpr ⟨j, hj, rfl⟩
      rw [hx, hun] at htr; cases htr
    simpa only [List.getElem?_set_ne hnot_ne2.symm, List.getElem?_set_ne hnot_ne1.symm] using
      hnot_false
  exact ⟨hstep.1, hnf, hstep.2.1, hstep.2.2⟩

theorem s13_bin_jumpreason_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_pi sem : FullState} {not_lit blk alvl nl_lvl0 : BitVec 32}
    {off_v p_v q_v end_v : BitVec 64} {flags' : List (BitVec 32)}
    {ph' : List (BitVec 8)} {unas' unfl' : BitVec 64}
    (hpi : PropLitInv c F0 F_cur s_pi sem not_lit.toNat off_v.toNat
      (q_v + 1#64).toNat (p_v.toNat + 1) end_v.toNat)
    (hfl : flags'.length = c.max_vars) (hph : ph'.length = c.max_vars)
    (hnot_lt : not_lit.toNat < 2 * sem.core.cur_vars)
    (hblk_lt : blk.toNat < 2 * sem.core.cur_vars)
    (hun : sem.core.vals[blk.toNat]?.getD 0#8 = 0#8)
    (halvl_le : alvl.toNat ≤ sem.core.cur_level)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [not_lit.toNat, blk.toNat]))
    (hnl : sem.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0)
    (hnl_le : (sem.core.lvl[not_lit.toNat / 2]?.getD 0#32).toNat ≤ alvl.toNat)
    (hnl0_iff : alvl = 0#32 ↔ sem.core.lvl[not_lit.toNat / 2]?.getD 0#32 = 0#32) :
    let rsn0 := (not_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    let rsn' := if alvl = 0#32 then 0xFFFFFFFF#32 else rsn0
    let sem2 : FullState :=
      { core :=
          { sem.core with
            vals := (sem.core.vals.set blk.toNat 1#8).set (blk.toNat ^^^ 1) 0xFF#8
            flags := flags', lvl := sem.core.lvl.set (blk.toNat / 2) alvl
            rsns := sem.core.rsns.set (blk.toNat / 2) rsn'
            trl := sem.core.trl.set sem.core.trail_end blk
            trail_pos := sem.core.trail_pos.set (blk.toNat / 2)
              (BitVec.ofNat 32 sem.core.trail_end)
            trail_end := sem.core.trail_end + 1, unassigned := unas', unflushed := unfl' }
        scratch := { sem.scratch with phases := ph' } }
    PropLitInv c F0 F_cur s_pi sem2 not_lit.toNat off_v.toNat (q_v + 1#64).toNat
      (p_v.toNat + 1) end_v.toNat ∧
    sem2.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl0 :=
  m7_bin_assign_step hpi hfl hph hnot_lt hblk_lt hun halvl_le hent hnl hnl_le hnl0_iff

theorem s13_unswapped_ar_swap_nw {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hl : k.LengthsOk c)
    (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k))
    {cref ri : Nat} {not_lit other repl : BitVec 32}
    (href : cref ∈ fullArenaClauseRefsCore k) (hsz3 : 3 ≤ fullArenaClauseSizeCore k cref)
    (hfit : cref + 3 + fullArenaClauseSizeCore k cref ≤ k.arena_len)
    (hri2 : 2 ≤ ri) (hri_lt : ri < fullArenaClauseSizeCore k cref)
    {l0' l1' : BitVec 32} (hwt : l0' = not_lit ∨ l1' = not_lit)
    (hoth : other = l0' ^^^ l1' ^^^ not_lit)
    (har3 : k.arena[cref + 3]? = some l0') (har4 : k.arena[cref + 4]? = some l1')
    (har_ri : k.arena[cref + 3 + ri]? = some repl) :
    let k' : FullCoreState := { k with
      arena := ((k.arena.set (cref + 3) other).set (cref + 4) repl).set (cref + 3 + ri) not_lit }
    FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k') ∧ FullArenaPermEq k k' ∧
    k'.arena[cref + 3]? = some other ∧ k'.arena[cref + 4]? = some repl ∧
    k'.arena[cref + 3 + ri]? = some not_lit := by
  have har_len := hl.arena_len_arr; have halen := hl.arena_len_le
  have hl0_lt : cref + 3 < k.arena.length := by omega
  have hl1_lt : cref + 4 < k.arena.length := by omega
  have hri_len : cref + 3 + ri < k.arena.length := by omega
  have har3_g : k.arena[cref + 3 + 0]'hl0_lt = l0' :=
    Option.some.inj ((List.getElem?_eq_getElem hl0_lt).symm.trans har3)
  have har4_g : k.arena[cref + 3 + 1]'hl1_lt = l1' :=
    Option.some.inj ((List.getElem?_eq_getElem hl1_lt).symm.trans har4)
  have har_ri_g : k.arena[cref + 3 + ri]'hri_len = repl :=
    Option.some.inj ((List.getElem?_eq_getElem hri_len).symm.trans har_ri)
  rcases hwt with rfl | rfl
  · have hoth_eq : other = l1' := by rw [hoth, BitVec.xor_assoc, BitVec.xor_comm l1' l0',
        ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    obtain ⟨hnw1, hp1⟩ := full_swapLits_preserves_nw hl hnw href (k1 := 0) (k2 := 1)
      (by omega) (by omega)
    let k1 : FullCoreState := { k with arena := (k.arena.set (cref + 3) l1').set (cref + 4) l0' }
    have hk1_eq : k1 = { k with arena := (k.arena.set (cref + 3 + 0)
        k.arena[cref + 3 + 1]).set (cref + 3 + 1) k.arena[cref + 3 + 0] } := by
      dsimp only [k1]; simp only [Nat.add_zero, har3_g, har4_g]
    rw [← hk1_eq] at hnw1 hp1
    have hl1 : k1.LengthsOk c := { hl with arena_len_arr := by simp [k1, har_len] }
    have href1 : cref ∈ fullArenaClauseRefsCore k1 := hp1.2.1 ▸ href
    have hsz1 : fullArenaClauseSizeCore k1 cref = fullArenaClauseSizeCore k cref :=
      (hp1.2.2 cref href).1
    have har1_4_len : cref + 3 + 1 < k1.arena.length := by simp [k1, har_len]; omega
    have har1_ri_len : cref + 3 + ri < k1.arena.length := by simp [k1, har_len]; omega
    have har1_4 : k1.arena[cref + 3 + 1]'har1_4_len = l0' := by
      simp [k1]
    have har1_ri : k1.arena[cref + 3 + ri]'har1_ri_len = repl := by
      simp [k1, List.getElem_set_ne (by omega : cref + 4 ≠ cref + 3 + ri),
        List.getElem_set_ne (by omega : cref + 3 ≠ cref + 3 + ri), har_ri_g]
    obtain ⟨hnw2, hp2⟩ := full_swapLits_preserves_nw hl1 hnw1 href1 (k1 := 1) (k2 := ri)
      (by omega) (by omega)
    let k' : FullCoreState := { k with
      arena := ((k.arena.set (cref + 3) other).set (cref + 4) repl).set (cref + 3 + ri) l0' }
    let arr'_1 := (k1.arena.set (cref + 3 + 1) (k1.arena[cref + 3 + ri]'har1_ri_len)).set
      (cref + 3 + ri) (k1.arena[cref + 3 + 1]'har1_4_len)
    have hk'_eq : k' = { k1 with arena := arr'_1 } := by
      dsimp only [k', k1, arr'_1]; rw [har1_4, har1_ri, hoth_eq]
      congr 1; apply List.ext_getElem (by simp)
      intro i hi1 hi2; simp only [List.getElem_set]
      by_cases hri : cref + 3 + ri = i
      · simp [hri]
      · simp only [hri, ↓reduceIte]; by_cases h4 : cref + 4 = i <;> simp [h4]
    rw [← hk'_eq] at hnw2 hp2
    have h3 : k'.arena[cref + 3]? = some other := by
      dsimp only [k']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by omega)]
    have h4 : k'.arena[cref + 4]? = some repl := by
      dsimp only [k']; rw [List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by simp; omega)]
    have hri' : k'.arena[cref + 3 + ri]? = some l0' := by
      dsimp only [k']; rw [List.getElem?_set_self (by simp; omega)]
    exact ⟨hnw2, fullArenaPermEq_trans hp1 hp2, h3, h4, hri'⟩
  · have hoth_eq : other = l0' := by
      rw [hoth, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    obtain ⟨hnw2, hp2⟩ := full_swapLits_preserves_nw hl hnw href (k1 := 1) (k2 := ri)
      (by omega) (by omega)
    let k' : FullCoreState := { k with
      arena := ((k.arena.set (cref + 3) other).set (cref + 4) repl).set (cref + 3 + ri) l1' }
    let arr'_2 := (k.arena.set (cref + 3 + 1) (k.arena[cref + 3 + ri]'hri_len)).set
      (cref + 3 + ri) (k.arena[cref + 3 + 1]'hl1_lt)
    have hk'_eq : k' = { k with arena := arr'_2 } := by
      dsimp only [k', arr'_2]; rw [har4_g, har_ri_g, hoth_eq]
      congr 1; apply List.ext_getElem (by simp)
      intro i hi1 hi2; simp only [List.getElem_set]
      by_cases hri : cref + 3 + ri = i
      · simp [hri]
      · simp only [hri, ↓reduceIte]; by_cases h4 : cref + 4 = i
        · simp [h4]
        · simp only [h4, ↓reduceIte]; by_cases h3 : cref + 3 = i
          · subst h3; simp only [↓reduceIte]
            exact (Option.some.inj ((List.getElem?_eq_getElem hl0_lt).symm.trans har3)).symm
          · simp [h3]
    rw [← hk'_eq] at hnw2 hp2
    have h3 : k'.arena[cref + 3]? = some other := by
      dsimp only [k']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by omega)]
    have h4 : k'.arena[cref + 4]? = some repl := by
      dsimp only [k']; rw [List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by simp; omega)]
    have hri' : k'.arena[cref + 3 + ri]? = some l1' := by
      dsimp only [k']; rw [List.getElem?_set_self (by simp; omega)]
    exact ⟨hnw2, hp2, h3, h4, hri'⟩

theorem s13_clause_falsified_of_find_repl_none {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} {cref : Nat}
    {not_lit other : BitVec 32} (hl : k.LengthsOk c)
    (hnw : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c k))
    (_href : cref ∈ fullArenaClauseRefsCore k) (_hsz3 : 3 ≤ fullArenaClauseSizeCore k cref)
    (hfit : cref + 3 + fullArenaClauseSizeCore k cref ≤ k.arena_len)
    {l0' l1' : BitVec 32} (hwt : l0' = not_lit ∨ l1' = not_lit)
    (hoth : other = l0' ^^^ l1' ^^^ not_lit)
    (har3 : k.arena[cref + 3]? = some l0') (har4 : k.arena[cref + 4]? = some l1')
    (hnot_f : k.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8)
    (hoth_f : k.vals[other.toNat]?.getD 0#8 = 0xFF#8)
    (hnone : ∀ r, 2 ≤ r → r < fullArenaClauseSizeCore k cref →
      (k.arena[cref + 3 + r]?.getD 0#32).toNat < 2 * k.cur_vars ∧
      ((k.vals[(k.arena[cref + 3 + r]?.getD 0#32).toNat]?.getD 0#8).signExtend 32).slt 0#32 =
        true) :
    ∀ l ∈ fullArenaClauseLitsCore k cref, k.vals[l]?.getD 0#8 = 0xFF#8 := by
  intro l hl_mem
  have hfit' : cref + 3 + fullArenaClauseSizeCore k cref ≤ k.arena.length := by
    rw [hl.arena_len_arr]; exact Nat.le_trans hfit hl.arena_len_le
  obtain ⟨k_off, hk_mem, rfl⟩ := mem_fullArenaClauseLitsCore_of_fit hfit' hl_mem
  rcases Nat.lt_trichotomy k_off 1 with hk0 | hk1 | hk2
  · have hkz : k_off = 0 := by omega
    subst hkz; simp only [Nat.add_zero]
    rcases hwt with rfl | rfl
    · rw [har3, Option.getD_some]; exact hnot_f
    · have hoth_eq : other = l0' := by
        rw [hoth, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
      rw [har3, Option.getD_some, ← hoth_eq]; exact hoth_f
  · subst hk1
    rcases hwt with rfl | rfl
    · have hoth_eq : other = l1' := by
        rw [hoth, BitVec.xor_assoc, BitVec.xor_comm l1' l0', ← BitVec.xor_assoc,
          BitVec.xor_self, BitVec.zero_xor]
      rw [har4, Option.getD_some, ← hoth_eq]; exact hoth_f
    · rw [har4, Option.getD_some]; exact hnot_f
  · have ⟨hlt, hslt⟩ := hnone k_off hk2 hk_mem
    have hdom : k.vals[(k.arena[cref + 3 + k_off]?.getD 0#32).toNat]?.getD 0#8 = 0#8 ∨
        k.vals[(k.arena[cref + 3 + k_off]?.getD 0#32).toNat]?.getD 0#8 = 1#8 ∨
        k.vals[(k.arena[cref + 3 + k_off]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8 :=
      hnw.vals_domain (k.arena[cref + 3 + k_off]?.getD 0#32).toNat hlt
    rcases hdom with h0 | h1 | hff
    · rw [h0] at hslt; cases hslt
    · rw [h1] at hslt; cases hslt
    · exact hff

theorem s13_large_confl_w0 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {not_lit off q p end_v : Nat} {w0 cref : BitVec 32}
    (hpi : PropLitInv c F0 F_cur s st not_lit off q (p + 2) end_v)
    (hnot_lt : not_lit < 2 * st.core.cur_vars) (hqp : q ≤ p)
    (hq_lt : q < st.core.wstk.length) (hq1_lt : q + 1 < st.core.wstk.length)
    (hflag : (w0 &&& 0x80000000#32) = 0#32)
    (hcr_lt : cref.toNat < 0x80000000) (hcref : cref.toNat ∈ fullArenaClauseRefsCore st.core)
    (hng : fullArenaClauseGarbCore st.core cref.toNat = false)
    (hfals : ∀ l ∈ fullArenaClauseLitsCore st.core cref.toNat,
      st.core.vals[l]?.getD 0#8 = 0xFF#8) :
    let st' : FullState := { st with core := { st.core with
      wstk := (st.core.wstk.set q w0).set (q + 1) cref
      confl_type := 2#64, confl_ref := cref.setWidth 64 } }
    PropLitInv c F0 F_cur s st' not_lit off (q + 2) (p + 2) end_v ∧
    FullConflOkW F_cur st'.core := by
  have hpi1 := propLit_inv_keep_large hpi hnot_lt hqp hq_lt hq1_lt hflag hcr_lt hcref
  exact propLit_large_confl hpi1 hcref hng hfals

theorem s13_setSrch_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_pi sem1 : FullState} {not_lit cref repl : BitVec 32}
    {ri_n : Nat} {ri32 : BitVec 32} {off_v p_v q_v end_v : BitVec 64}
    (hpi1 : PropLitInv c F0 F_cur s_pi sem1 not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat)
    (hcr_ref : cref.toNat ∈ fullArenaClauseRefsCore sem1.core)
    {l0' l1' : BitVec 32}
    (har3 : sem1.core.arena[cref.toNat + 3]? = some l0')
    (har4 : sem1.core.arena[cref.toNat + 4]? = some l1')
    (har_ri : sem1.core.arena[cref.toNat + 3 + ri_n]? = some repl) :
    let sem2 : FullState := { sem1 with core := { sem1.core with
      arena := sem1.core.arena.set (cref.toNat + 1) ri32 } }
    PropLitInv c F0 F_cur s_pi sem2 not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat ∧
    sem2.LengthsOk c ∧ cref.toNat ∈ fullArenaClauseRefsCore sem2.core ∧
    fullArenaClauseSizeCore sem2.core cref.toNat = fullArenaClauseSizeCore sem1.core cref.toNat ∧
    sem2.core.arena[cref.toNat + 3]? = some l0' ∧
    sem2.core.arena[cref.toNat + 4]? = some l1' ∧
    sem2.core.arena[cref.toNat + 3 + ri_n]? = some repl := by
  have := m7_setSrch_step hpi1 hcr_ref har3 har4 har_ri (ri32 := ri32)
  exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1,
    this.2.2.2.2.2.1, this.2.2.2.2.2.2⟩

theorem m7_tB_swap_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st_t : FullState} {not_lit l0 l1 other cref : BitVec 32}
    {off_v p_v q_v end_v : BitVec 64}
    (hpi : PropLitInv c F0 F_cur s st_t not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat)
    (hcr_ref : cref.toNat ∈ fullArenaClauseRefsCore st_t.core)
    (hng : fullArenaClauseGarbCore st_t.core cref.toNat = false)
    (_hsz3 : 3 ≤ fullArenaClauseSizeCore st_t.core cref.toNat)
    (hfit : cref.toNat + 3 + fullArenaClauseSizeCore st_t.core cref.toNat ≤ st_t.core.arena_len)
    (har3 : st_t.core.arena[cref.toNat + 3]? = some l0)
    (har4 : st_t.core.arena[cref.toNat + 4]? = some l1)
    (hwt : l0 = not_lit) (hoth : other = l0 ^^^ l1 ^^^ not_lit) :
    let st2 : FullState := { st_t with core := { st_t.core with
      arena := (st_t.core.arena.set (cref.toNat + 3) other).set (cref.toNat + 4) not_lit } }
    other = l1 ∧
    PropLitInv c F0 F_cur s st2 not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat ∧
    cref.toNat ∈ fullArenaClauseRefsCore st2.core ∧
    fullArenaClauseSizeCore st2.core cref.toNat = fullArenaClauseSizeCore st_t.core cref.toNat ∧
    st2.core.arena[cref.toNat + 3]? = some other ∧
    st2.core.arena[cref.toNat + 4]? = some not_lit := by
  cases hwt
  have hoth_eq : other = l1 := by
    rw [hoth, BitVec.xor_assoc, BitVec.xor_comm l1 not_lit, ← BitVec.xor_assoc,
      BitVec.xor_self, BitVec.zero_xor]
  subst hoth_eq
  obtain ⟨hpi2, hcr2, _, hcsz2, har3_2, har4_2⟩ :=
    m7_swapCl_step hpi hcr_ref hng hfit har3 har4
  exact ⟨rfl, hpi2, hcr2, hcsz2, har3_2, har4_2⟩

theorem m7_ovf_fail_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s_pi st2 : FullState} {not_lit other repl cref : BitVec 32}
    {off_v p_v q_v end_v : BitVec 64}
    (hpi2 : PropLitInv c F0 F_cur s_pi st2 not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat)
    (hlen2 : st2.LengthsOk c) (hcv2 : st2.core.cur_vars = st2.core.cur_vars)
    (hnot_lt : not_lit.toNat < 2 * st2.core.cur_vars)
    (hlay2 : WatchStackLayout st2.core)
    (hperm : FullArenaPermEq st2.core st2.core)
    (hnw2 : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st2.core))
    (hag2 : AgreesExcept propLitCoreMask s_pi.core st2.core)
    (htr2 : FullTrailExt s_pi.core st2.core)
    (hsc2 : st2.scratch = { s_pi.scratch with
      search_ticks := st2.scratch.search_ticks, wsort := st2.scratch.wsort,
      phases := st2.scratch.phases })
    (hnot_f : st2.core.vals[not_lit.toNat]?.getD 0#8 = 0xFF#8)
    (hrepl_lt : repl.toNat < 2 * st2.core.cur_vars) (hrepl_ne : repl.toNat ≠ not_lit.toNat)
    (hcr_lt : cref.toNat < 0x80000000) (hcr_ref : cref.toNat ∈ fullArenaClauseRefsCore st2.core)
    (hp2_nat : (p_v + 1#64 + 1#64).toNat = p_v.toNat + 2) (hq_le : q_v.toNat ≤ p_v.toNat)
    (hoth_mask : other &&& 0x7FFFFFFF#32 = other)
    (hother_pres : ∀ l < 2 * st2.core.cur_vars, l ≠ repl.toNat →
      fullWatchSizeCore st2.core l = fullWatchSizeCore st2.core l ∧
      ∀ k < fullWatchSizeCore st2.core l,
        st2.core.wstk[fullWatchOffCore st2.core l + k]? =
          st2.core.wstk[fullWatchOffCore st2.core l + k]?)
    (hrepl_fail : fullWatchSizeCore st2.core repl.toNat = fullWatchSizeCore st2.core repl.toNat ∧
      ∀ k < fullWatchSizeCore st2.core repl.toNat,
        st2.core.wstk[fullWatchOffCore st2.core repl.toNat + k]? =
          st2.core.wstk[fullWatchOffCore st2.core repl.toNat + k]?) :
    let wv_n0 := (st2.core.wvec[2 * not_lit.toNat]?.getD 0#32).setWidth 64
    (wv_n0 + (q_v - off_v)).toNat < st2.core.wstk.length ∧
    (wv_n0 + (q_v - off_v) + 1#64).toNat < st2.core.wstk.length ∧
    (wv_n0 + (q_v - off_v) + 1#64).toNat = (wv_n0 + (q_v - off_v)).toNat + 1 ∧
    ((st2.core.wstk.set (wv_n0 + (q_v - off_v)).toNat other).set
      ((wv_n0 + (q_v - off_v)).toNat + 1) cref).length = c.wcap ∧
    True ∧ True ∧ True ∧
    PropLitInv c F0 F_cur s_pi
      { st2 with core := { st2.core with
          wstk := (st2.core.wstk.set (wv_n0 + (q_v - off_v)).toNat other).set
            ((wv_n0 + (q_v - off_v)).toNat + 1) cref } }
      not_lit.toNat wv_n0.toNat (wv_n0 + (q_v - off_v) + 2#64).toNat
      (wv_n0 + (p_v + 1#64 + 1#64 - off_v)).toNat (wv_n0 + (end_v - off_v)).toNat := by
  have _ : True := by
    have _ := hcv2; have _ := hperm; have _ := hnw2; have _ := hag2; have _ := htr2
    have _ := hsc2; have _ := hnot_f; have _ := hother_pres; have _ := hrepl_fail
    trivial
  have hwc := c.hwcap; unfold dimacsBound at hwc
  have hidx0 : 2 * not_lit.toNat = 2 * (not_lit ^^^ 0#32).toNat := by simp
  have hsw_f := propLit_b1_after_push (c := c) (F_cur := F_cur) (st3 := st2) (st4 := st2)
    (lit := not_lit ^^^ 1#32) (other := other) (cref := cref) (repl := repl)
    (off_v := off_v) (p_v := p_v) (q_v := q_v) (end_v := end_v) (pok := false)
    (idx0 := 2 * not_lit.toNat) (by rw [BitVec.xor_assoc]; simp [hnot_lt]) rfl
    (by rw [BitVec.xor_assoc]; simp [hnot_lt]) hlen2 hlay2
    (by simpa [BitVec.xor_assoc] using hpi2.sw) rfl hrepl_lt
    (by simpa [BitVec.xor_assoc] using hrepl_ne) hcr_lt hcr_ref hp2_nat hq_le
    (fun l hl _ => ⟨rfl, fun _ _ => rfl⟩) (fun h => by cases h) (fun _ => ⟨rfl, fun _ _ => rfl⟩)
    (by rw [BitVec.xor_assoc]; simp)
  simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] at hsw_f
  rcases hsw_f with ⟨hoff_n, hq_n, hp_n, hend_n, hq2_le, hp_le_end, ⟨hend_le, hwc64⟩, hsw4⟩
  have hwlen := hlen2.core_ok.wstk_len_arr
  have hq_lt_len : ((st2.core.wvec[2 * not_lit.toNat]?.getD 0#32).setWidth 64 +
      (q_v - off_v)).toNat < st2.core.wstk.length := by
    rw [hwlen]; omega
  have hq1_nat : ((st2.core.wvec[2 * not_lit.toNat]?.getD 0#32).setWidth 64 +
      (q_v - off_v) + 1#64).toNat =
      ((st2.core.wvec[2 * not_lit.toNat]?.getD 0#32).setWidth 64 + (q_v - off_v)).toNat + 1 :=
    m7_bv64_add1_toNat (by omega)
  have hq2_nat : ((st2.core.wvec[2 * not_lit.toNat]?.getD 0#32).setWidth 64 +
      (q_v - off_v) + 2#64).toNat =
      ((st2.core.wvec[2 * not_lit.toNat]?.getD 0#32).setWidth 64 + (q_v - off_v)).toNat + 2 :=
    m7_bv64_add2_toNat (by omega)
  have hq1_lt_len : ((st2.core.wvec[2 * not_lit.toNat]?.getD 0#32).setWidth 64 +
      (q_v - off_v) + 1#64).toNat < st2.core.wstk.length := by
    rw [hq1_nat, hwlen]; omega
  have hflag : (other &&& 0x80000000#32) = 0#32 := by
    rw [← hoth_mask]; exact bv32_mask7f_flag0 other
  have hsw_w := SplitWatchesInv.write_large hsw4 hnot_lt (by omega)
    (by rw [← hq1_nat]; exact hq1_lt_len) hflag hcr_lt hcr_ref
  rw [← hq2_nat] at hsw_w
  let wv_n0 := (st2.core.wvec[2 * not_lit.toNat]?.getD 0#32).setWidth 64
  let st_f : FullState := { st2 with core := { st2.core with
    wstk := (st2.core.wstk.set (wv_n0 + (q_v - off_v)).toNat other).set
      ((wv_n0 + (q_v - off_v)).toNat + 1) cref } }
  have hlen_f : st_f.LengthsOk c :=
    ⟨{ hlen2.core_ok with wstk_len_arr := by simp [st_f, hwlen] }, hlen2.scratch_ok⟩
  have hnw_f : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c st_f.core) :=
    fullWitnessInv_nw_congr hpi2.len.core_ok.cur_vars_le hpi2.nw
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  refine ⟨hq_lt_len, hq1_lt_len, hq1_nat, by simp [hwlen], trivial, trivial, trivial, ?_⟩
  exact
    { len := hlen_f, nw := hnw_f, sw := hsw_w
      ag := hpi2.ag.update (fun k => { k with wstk := st_f.core.wstk })
      tr := hpi2.tr, rsns_pres := hpi2.rsns_pres, perm := hpi2.perm
      sc_eq := hpi2.sc_eq, not_f := hpi2.not_f }

/-! ## 4. Shared Sub-Expression AST Builders & WP Proofs -/

@[expose] def m7LpReplScanExpr {Val : Ty → Type} {Cont : List Ty → Type} {rs : List Ty}
    (vals arena : Val i64) (cbase _csz start end_r : Val i64)
    (J_found : Cont [i64, i32]) (J_none : Cont []) : Expr Val Cont rs :=
  .group (sig := [[i64]])
    (fun J_r => .cons (fun r =>
      .let_ (Op.mk (.cmp .ult i64) (.var r.1, (.var end_r, ()))) fun cr =>
      .jnz (.var cr.1)
        (.let_ (Op.mk (.add i64) (.var cbase, (.var r.1, ()))) fun ar_i =>
         .let_ (Op.mk (.mul i64) (.var ar_i.1, (.imm 4, ()))) fun o_i =>
         .let_ (Op.mk (.add i64) (.var arena, (.var o_i.1, ()))) fun ap_i =>
         .load i32 (.var ap_i.1) fun repl =>
         .let_ (Op.mk (.zext 32 64) (.var repl, ())) fun repl64 =>
         .let_ (Op.mk (.add i64) (.var vals, (.var repl64.1, ()))) fun vp_r =>
         .load i8 (.var vp_r.1) fun vr =>
         .let_ (Op.mk (.sext 8 32) (.var vr, ())) fun s_vr =>
         .let_ (Op.mk (.cmp .slt i32) (.var s_vr.1, (.imm 0, ()))) fun clt =>
         .jnz (.var clt.1)
           (.let_ (Op.mk (.add i64) (.var r.1, (.imm 1, ()))) fun r1 =>
            .jump J_r.1 (.var r1.1, ()))
           (.jump J_found (.var r.1, (.var repl, ()))))
        (.jump J_none ())) .nil)
    (fun J_r => .jump J_r.1 (.var start, ()))

theorem m7_lp_repl_scan_arg_wp {Γ : Env} {rs : List Ty} {c : FullCfg}
    {s_disk sem1 : FullState} {cref : BitVec 32} {cbase csz start end_r : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post rs} {X : XPost}
    {J_found : Cont [i64, i32]} {J_none : Cont []}
    (har : c.arena_cap < 2 * dimacsBound) (_hmaxv : c.max_vars < 2 * dimacsBound)
    (hlen1 : sem1.LengthsOk c) (hcv_le : sem1.core.cur_vars ≤ c.max_vars)
    (_hcr_ref : cref.toNat ∈ fullArenaClauseRefsCore sem1.core)
    (hfit : cref.toNat + 3 + fullArenaClauseSizeCore sem1.core cref.toNat ≤ sem1.core.arena_len)
    (hlits_lt : ∀ r, 2 ≤ r → r < fullArenaClauseSizeCore sem1.core cref.toNat →
      (sem1.core.arena[cref.toNat + 3 + r]?.getD 0#32).toNat < 2 * sem1.core.cur_vars)
    (hcbase : cbase.toNat = cref.toNat + 3)
    (hcsz : csz.toNat = fullArenaClauseSizeCore sem1.core cref.toNat)
    (hstart : 2 ≤ start.toNat) (hend_eq : end_r.toNat ≤ csz.toNat)
    (hstart_le : start.toNat ≤ end_r.toNat)
    (hm : (FullMem c (fastPropMem s_disk sem1) ⋆ R) m)
    (hJ_found : ∀ (r : BitVec 64) (repl : BitVec 32),
      start.toNat ≤ r.toNat → r.toNat < end_r.toNat →
      sem1.core.arena[cref.toNat + 3 + r.toNat]? = some repl →
      repl.toNat < 2 * sem1.core.cur_vars →
      ((sem1.core.vals[repl.toNat]?.getD 0#8).signExtend 32).slt 0#32 = false →
      (∀ r0, start.toNat ≤ r0 → r0 < r.toNat →
        (sem1.core.arena[cref.toNat + 3 + r0]?.getD 0#32).toNat < 2 * sem1.core.cur_vars ∧
        ((sem1.core.vals[(sem1.core.arena[cref.toNat + 3 + r0]?.getD 0#32).toNat]?.getD
          0#8).signExtend 32).slt 0#32 = true) →
      wp Γ Q X (.jump J_found (.var r, (.var repl, ()))) m)
    (hJ_none :
      (∀ r0, start.toNat ≤ r0 → r0 < end_r.toNat →
        (sem1.core.arena[cref.toNat + 3 + r0]?.getD 0#32).toNat < 2 * sem1.core.cur_vars ∧
        ((sem1.core.vals[(sem1.core.arena[cref.toNat + 3 + r0]?.getD 0#32).toNat]?.getD
          0#8).signExtend 32).slt 0#32 = true) →
      wp Γ Q X (.jump J_none ()) m) :
    wp Γ Q X (m7LpReplScanExpr c.pVals c.pArena cbase csz start end_r J_found J_none) m := by
  unfold dimacsBound at har
  have haren := hlen1.core_ok.arena_len_arr; have halen := hlen1.core_ok.arena_len_le
  have hvals := hlen1.core_ok.vals_len
  unfold m7LpReplScanExpr
  refine wp_loop_group (fun rem (r, ()) mr => mr = m ∧ start.toNat ≤ r.toNat ∧
      r.toNat ≤ end_r.toNat ∧ rem = end_r.toNat - r.toNat ∧
      (∀ r0, start.toNat ≤ r0 → r0 < r.toNat →
        (sem1.core.arena[cref.toNat + 3 + r0]?.getD 0#32).toNat < 2 * sem1.core.cur_vars ∧
        ((sem1.core.vals[(sem1.core.arena[cref.toNat + 3 + r0]?.getD 0#32).toNat]?.getD
          0#8).signExtend 32).slt 0#32 = true)) ?_ ?_
  · rintro J_r rem ⟨r, ⟨⟩⟩ mr ih ⟨hmr, hsr, hre, rfl, hall⟩
    subst mr
    s13_hsplit
    · have hr_lt : r.toNat < end_r.toNat := hc
      have hr2 : 2 ≤ r.toNat := by omega
      have hr_sz : r.toNat < fullArenaClauseSizeCore sem1.core cref.toNat := by omega
      have hcr_idx : (cbase + r).toNat = cref.toNat + 3 + r.toNat := by
        rw [m7_bv64_add_toNat (by rw [hcbase]; omega), hcbase]
      have hcb_mod : (cbase.toNat + r.toNat) % 2 ^ 64 = cref.toNat + 3 + r.toNat := by
        rw [Nat.mod_eq_of_lt (by rw [hcbase]; omega), hcbase]
      have hcr_len : cref.toNat + 3 + r.toNat < sem1.core.arena.length := by omega
      have hcr_mem : (cbase + r).toNat < (fastPropMem s_disk sem1).core.arena.length := by
        rw [fastPropMem_arena, hcr_idx]; exact hcr_len
      let repl := (fastPropMem s_disk sem1).core.arena[(cbase + r).toNat]'hcr_mem
      have hrepl_get : sem1.core.arena[cref.toNat + 3 + r.toNat]? = some repl := by
        dsimp only [repl]
        rw [fc_getElem_arena s_disk sem1 hcr_mem (by rw [hcr_idx]; exact hcr_len)]
        have h1 : sem1.core.arena[(cbase + r).toNat]'(by rw [hcr_idx]; exact hcr_len) =
            sem1.core.arena[cref.toNat + 3 + r.toNat]'hcr_len :=
          fc_getElem_eq_of_idx rfl hcr_idx _ hcr_len
        rw [h1, List.getElem?_eq_getElem hcr_len]
      have hrepl_lt : repl.toNat < 2 * sem1.core.cur_vars := by
        have h := hlits_lt r.toNat hr2 hr_sz; rwa [hrepl_get, Option.getD_some] at h
      have hrepl_idx : sem1.core.arena[(cbase.toNat + r.toNat) % 2 ^ 64]'(by
          rw [hcb_mod]; exact hcr_len) = repl := by
        have h1 := fc_getElem_eq_of_idx (a := sem1.core.arena) (b := sem1.core.arena) rfl hcb_mod
          (by rw [hcb_mod]; exact hcr_len) hcr_len
        exact h1.trans (Option.some.inj ((List.getElem?_eq_getElem hcr_len).symm.trans hrepl_get))
      have hrepl_vals_bd : (BitVec.setWidth 64
          (fastPropMem s_disk sem1).core.arena[(cbase + r).toNat]).toNat <
          (fastPropMem s_disk sem1).core.vals.length := by
        rw [bv_c0_zext32_64, fastPropMem_vals, hvals]
        have h1 : (fastPropMem s_disk sem1).core.arena[(cbase + r).toNat]'hcr_mem = repl := rfl
        rw [h1]; omega
      have hrepl_idx_nat := congrArg BitVec.toNat hrepl_idx
      have hv_eq : sem1.core.vals[repl.toNat]'(by rw [hvals]; omega) =
          sem1.core.vals[sem1.core.arena[(cbase.toNat + r.toNat) % 2 ^ 64].toNat]'(by
            rw [hvals, hrepl_idx_nat]; omega) :=
        fc_getElem_eq_of_idx rfl hrepl_idx_nat.symm _ _
      s13_hsplit
      · have hr1_n : (r + 1#64).toNat = r.toNat + 1 := m7_bv64_add1_toNat (by omega)
        have hvr_slt : ((sem1.core.vals[repl.toNat]?.getD 0#8).signExtend 32).slt 0#32 =
            true := by
          rw [List.getElem?_eq_getElem (by rw [hvals]; omega), Option.getD_some, hv_eq]
          exact hc
        refine ih (end_r.toNat - (r + 1#64).toNat) (r + 1#64, ()) m (by omega)
          ⟨rfl, by omega, by omega, rfl, fun r0 hr0_lo hr0_hi => ?_⟩
        by_cases heq : r0 = r.toNat
        · subst heq; rw [hrepl_get, Option.getD_some]; exact ⟨hrepl_lt, hvr_slt⟩
        · exact hall r0 hr0_lo (by omega)
      · have hvr_f : ((sem1.core.vals[repl.toNat]?.getD 0#8).signExtend 32).slt 0#32 =
            false := by
          rw [List.getElem?_eq_getElem (by rw [hvals]; omega), Option.getD_some, hv_eq]
          exact hc
        exact hJ_found r repl hsr hr_lt hrepl_get hrepl_lt hvr_f hall
    · have hreq : r.toNat = end_r.toNat := by omega
      exact hJ_none (fun r0 hr0_lo hr0_hi => hall r0 hr0_lo (by omega))
  · intro J_r hJ_r
    exact hJ_r _ (start, ()) m ⟨rfl, le_refl _, hstart_le, rfl, fun r0 h1 h2 => by omega⟩

@[expose] def m7LpMaxLvlExpr {Val : Ty → Type} {Cont : List Ty → Type} {rs : List Ty}
    (arena lvl : Val i64) (not_lit nl_lvl : Val i32) (cbase csz : Val i64)
    (J_done : Cont [i32]) : Expr Val Cont rs :=
  .group (sig := [[i64, i32]])
    (fun J_k => .cons (fun kv =>
      .let_ (Op.mk (.cmp .ult i64) (.var kv.1, (.var csz, ()))) fun ck =>
      .jnz (.var ck.1)
        (.let_ (Op.mk (.add i64) (.var cbase, (.var kv.1, ()))) fun ar_k =>
         .let_ (Op.mk (.mul i64) (.var ar_k.1, (.imm 4, ()))) fun o_k =>
         .let_ (Op.mk (.add i64) (.var arena, (.var o_k.1, ()))) fun ap_k =>
         .load i32 (.var ap_k.1) fun lk =>
         .let_ (Op.mk (.cmp .ne i32) (.var lk, (.var not_lit, ()))) fun hne =>
         .jnz (.var hne.1)
           (.let_ (Op.mk (.lshr i32) (.var lk, (.imm 1, ()))) fun vk =>
            .let_ (Op.mk (.zext 32 64) (.var vk.1, ())) fun vk64 =>
            .let_ (Op.mk (.mul i64) (.var vk64.1, (.imm 4, ()))) fun lvo =>
            .let_ (Op.mk (.add i64) (.var lvl, (.var lvo.1, ()))) fun lvp =>
            .load i32 (.var lvp.1) fun kl =>
            .let_ (Op.mk (.cmp .ugt i32) (.var kl, (.var kv.2.1, ()))) fun hgt =>
            .let_ (Op.mk (.add i64) (.var kv.1, (.imm 1, ()))) fun k1 =>
            .jnz (.var hgt.1)
              (.jump J_k.1 (.var k1.1, (.var kl, ())))
              (.jump J_k.1 (.var k1.1, (.var kv.2.1, ()))))
           (.let_ (Op.mk (.add i64) (.var kv.1, (.imm 1, ()))) fun k1 =>
            .jump J_k.1 (.var k1.1, (.var kv.2.1, ()))))
        (.jump J_done (.var kv.2.1, ()))) .nil)
    (fun J_k => .jump J_k.1 (.imm 1, (.var nl_lvl, ())))

theorem m7_lp_max_lvl_wp {Γ : Env} {rs : List Ty} {c : FullCfg}
    {s_disk sem1 : FullState} {not_lit other cref nl_lvl : BitVec 32}
    {cbase csz : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post rs} {X : XPost}
    {J_done : Cont [i32]}
    (har : c.arena_cap < 2 * dimacsBound) (_hmaxv : c.max_vars < 2 * dimacsBound)
    (hlen1 : sem1.LengthsOk c) (hcv_le : sem1.core.cur_vars ≤ c.max_vars)
    (_hcr_ref : cref.toNat ∈ fullArenaClauseRefsCore sem1.core)
    (hfit : cref.toNat + 3 + fullArenaClauseSizeCore sem1.core cref.toNat ≤ sem1.core.arena_len)
    (har3 : sem1.core.arena[cref.toNat + 3]? = some other)
    (har4 : sem1.core.arena[cref.toNat + 4]? = some not_lit)
    (_hnot_lt : not_lit.toNat < 2 * sem1.core.cur_vars)
    (hnl : sem1.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl)
    (_hother_lt : other.toNat < 2 * sem1.core.cur_vars)
    (hoth_un : sem1.core.vals[other.toNat]?.getD 0#8 = 0#8)
    (hnot_ne_oth : not_lit.toNat ≠ other.toNat)
    (htail_f : ∀ r, 2 ≤ r → r < fullArenaClauseSizeCore sem1.core cref.toNat →
      ((sem1.core.vals[(sem1.core.arena[cref.toNat + 3 + r]?.getD 0#32).toNat]?.getD
        0#8).signExtend 32).slt 0#32 = true)
    (hlits_lt : ∀ k_off, k_off < fullArenaClauseSizeCore sem1.core cref.toNat →
      (sem1.core.arena[cref.toNat + 3 + k_off]?.getD 0#32).toNat < 2 * sem1.core.cur_vars)
    (hcbase : cbase.toNat = cref.toNat + 3)
    (hcsz : csz.toNat = fullArenaClauseSizeCore sem1.core cref.toNat)
    (hsz3 : 3 ≤ fullArenaClauseSizeCore sem1.core cref.toNat)
    (hm : (FullMem c (fastPropMem s_disk sem1) ⋆ R) m)
    (hJ_done : ∀ alvl : BitVec 32,
      (∀ l ∈ fullArenaClauseLitsCore sem1.core cref.toNat, l ≠ other.toNat →
        (sem1.core.lvl[l / 2]?.getD 0#32).toNat ≤ alvl.toNat) →
      (alvl = 0#32 ∨ ∃ l ∈ fullArenaClauseLitsCore sem1.core cref.toNat,
        l ≠ other.toNat ∧ alvl = sem1.core.lvl[l / 2]?.getD 0#32) →
      wp Γ Q X (.jump J_done (.var alvl, ())) m) :
    wp Γ Q X (m7LpMaxLvlExpr c.pArena c.pLevel not_lit nl_lvl cbase csz J_done) m := by
  unfold dimacsBound at har
  have haren := hlen1.core_ok.arena_len_arr; have halen := hlen1.core_ok.arena_len_le
  have hlvl_len := hlen1.core_ok.lvl_len
  have hnot_mem : not_lit.toNat ∈ fullArenaClauseLitsCore sem1.core cref.toNat :=
    mem_fullArenaClauseLitsCore_of_idx (k_off := 1) (by omega) har4
  unfold m7LpMaxLvlExpr
  refine wp_loop_group (fun rem (k_v, al_v, ()) mk => mk = m ∧
      1 ≤ k_v.toNat ∧ k_v.toNat ≤ csz.toNat ∧ rem = csz.toNat - k_v.toNat ∧
      nl_lvl.toNat ≤ al_v.toNat ∧
      (∀ k_off, 1 ≤ k_off → k_off < k_v.toNat →
        ((sem1.core.lvl[(sem1.core.arena[cref.toNat + 3 + k_off]?.getD 0#32).toNat / 2]?.getD
          0#32).toNat ≤ al_v.toNat)) ∧
      (al_v = 0#32 ∨ ∃ l ∈ fullArenaClauseLitsCore sem1.core cref.toNat,
        l ≠ other.toNat ∧ al_v = sem1.core.lvl[l / 2]?.getD 0#32)) ?_ ?_
  · rintro J_k rem ⟨k_v, al_v, ⟨⟩⟩ mk ih ⟨hmr, hk1, hk_csz, rfl, hnl_le, hge, hatt⟩
    rw [← hmr] at hm
    s13_hsplit
    · have hk_lt : k_v.toNat < csz.toNat := hc
      have hk_sz : k_v.toNat < fullArenaClauseSizeCore sem1.core cref.toNat := hcsz ▸ hk_lt
      have hcr_idx : (cbase + k_v).toNat = cref.toNat + 3 + k_v.toNat := by
        rw [m7_bv64_add_toNat (by rw [hcbase]; omega), hcbase]
      have hcb_mod : (cbase.toNat + k_v.toNat) % 2 ^ 64 = cref.toNat + 3 + k_v.toNat := by
        rw [Nat.mod_eq_of_lt (by rw [hcbase]; omega), hcbase]
      have hcr_len : cref.toNat + 3 + k_v.toNat < sem1.core.arena.length := by omega
      have hcr_mem : (cbase + k_v).toNat < (fastPropMem s_disk sem1).core.arena.length := by
        rw [fastPropMem_arena, hcr_idx]; exact hcr_len
      let lk := (fastPropMem s_disk sem1).core.arena[(cbase + k_v).toNat]'hcr_mem
      have hlk_get : sem1.core.arena[cref.toNat + 3 + k_v.toNat]? = some lk := by
        dsimp only [lk]
        rw [fc_getElem_arena s_disk sem1 hcr_mem (by rw [hcr_idx]; exact hcr_len)]
        have h1 : sem1.core.arena[(cbase + k_v).toNat]'(by rw [hcr_idx]; exact hcr_len) =
            sem1.core.arena[cref.toNat + 3 + k_v.toNat]'hcr_len :=
          fc_getElem_eq_of_idx rfl hcr_idx _ hcr_len
        rw [h1, List.getElem?_eq_getElem hcr_len]
      have hlk_idx : sem1.core.arena[(cbase.toNat + k_v.toNat) % 2 ^ 64]'(by
          rw [hcb_mod]; exact hcr_len) = lk := by
        have h1 := fc_getElem_eq_of_idx (a := sem1.core.arena) (b := sem1.core.arena) rfl hcb_mod
          (by rw [hcb_mod]; exact hcr_len) hcr_len
        exact h1.trans (Option.some.inj ((List.getElem?_eq_getElem hcr_len).symm.trans hlk_get))
      have hlk_lt : lk.toNat < 2 * sem1.core.cur_vars := by
        have h := hlits_lt k_v.toNat hk_sz; rwa [hlk_get, Option.getD_some] at h
      have hlk_mem : lk.toNat ∈ fullArenaClauseLitsCore sem1.core cref.toNat :=
        mem_fullArenaClauseLitsCore_of_idx hk_sz hlk_get
      have hk1_n : (k_v + 1#64).toNat = k_v.toNat + 1 := m7_bv64_add1_toNat (by omega)
      have hkl_lvl_bd : (BitVec.setWidth 64
          ((fastPropMem s_disk sem1).core.arena[(cbase + k_v).toNat] >>> 1)).toNat <
          (fastPropMem s_disk sem1).core.lvl.length := by
        have h1 : (fastPropMem s_disk sem1).core.arena[(cbase + k_v).toNat]'hcr_mem = lk := rfl
        rw [h1, bv_c0_zext32_64, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
          Nat.pow_one, fastPropMem_lvl, hlvl_len]
        omega
      s13_hsplit
      · have hlk_ne : lk ≠ not_lit := by rw [hlk_idx] at hc; exact hc
        have hlk_ne_oth : lk.toNat ≠ other.toNat := fun heq => by
          rcases Nat.eq_or_lt_of_le hk1 with h1 | h2
          · rw [← h1, har4, Option.some.injEq] at hlk_get
            exact hlk_ne hlk_get.symm
          · have hf := htail_f k_v.toNat (by omega) hk_sz
            rw [hlk_get, Option.getD_some, heq, hoth_un] at hf
            cases hf
        have hvk_n : ((lk >>> 1#32).setWidth 64).toNat = lk.toNat / 2 := m7_bv32_rshift1_toNat lk
        have hvk_len : lk.toNat / 2 < sem1.core.lvl.length := by rw [hlvl_len]; omega
        have hvk_mem : ((lk >>> 1#32).setWidth 64).toNat <
            (fastPropMem s_disk sem1).core.lvl.length := by
          rw [fastPropMem_lvl, hvk_n]; exact hvk_len
        let kl := (fastPropMem s_disk sem1).core.lvl[((lk >>> 1#32).setWidth 64).toNat]'hvk_mem
        have hkl_idx : sem1.core.lvl[lk.toNat / 2]'hvk_len = kl := by
          dsimp only [kl]
          rw [fc_getElem_lvl s_disk sem1 hvk_mem hvk_len]
          exact fc_getElem_eq_of_idx rfl hvk_n _ hvk_len
        have hlk_idx_nat := congrArg BitVec.toNat hlk_idx
        have hkl_idx_mod :
            sem1.core.lvl[sem1.core.arena[(cbase.toNat + k_v.toNat) % 2 ^ 64].toNat / 2]'(by
              rw [hlvl_len, hlk_idx_nat]; omega) = kl := by
          have h1 := fc_getElem_eq_of_idx (a := sem1.core.lvl) (b := sem1.core.lvl) rfl
            (congrArg (· / 2) hlk_idx_nat) (by rw [hlvl_len, hlk_idx_nat]; omega) hvk_len
          exact h1.trans hkl_idx
        have hkl_get : sem1.core.lvl[lk.toNat / 2]? = some kl := by
          rw [List.getElem?_eq_getElem hvk_len, hkl_idx]
        s13_hsplit
        · have hgt : al_v.toNat < kl.toNat := by rw [hkl_idx_mod] at hc; exact hc
          refine ih _ (k_v + 1#64, kl, ()) mk (by omega)
            ⟨hmr, by omega, by omega, rfl, Nat.le_trans hnl_le (Nat.le_of_lt hgt),
              fun ko hlo hhi => ?_,
              Or.inr ⟨lk.toNat, hlk_mem, hlk_ne_oth, by rw [hkl_get, Option.getD_some]⟩⟩
          by_cases heq : ko = k_v.toNat
          · subst heq; rw [hlk_get, Option.getD_some, hkl_get, Option.getD_some]
            exact le_refl _
          · exact Nat.le_trans (hge ko hlo (by omega)) (Nat.le_of_lt hgt)
        · have hle : kl.toNat ≤ al_v.toNat := by rw [hkl_idx_mod] at hc; omega
          refine ih _ (k_v + 1#64, al_v, ()) mk (by omega)
            ⟨hmr, by omega, by omega, rfl, hnl_le, fun ko hlo hhi => ?_, hatt⟩
          by_cases heq : ko = k_v.toNat
          · subst heq; rwa [hlk_get, Option.getD_some, hkl_get, Option.getD_some]
          · exact hge ko hlo (by omega)
      · have hlk_eq : lk = not_lit := by rw [hlk_idx] at hc; exact hc
        s13_hsteps
        refine ih _ (k_v + 1#64, al_v, ()) mk (by omega)
          ⟨hmr, by omega, by omega, rfl, hnl_le, fun ko hlo hhi => ?_, hatt⟩
        by_cases heq : ko = k_v.toNat
        · subst heq; rw [hlk_get, Option.getD_some, hlk_eq, hnl]; exact hnl_le
        · exact hge ko hlo (by omega)
    · have hk_eq : k_v.toNat = csz.toNat := by omega
      s13_hsteps
      rw [hmr]
      refine hJ_done al_v (fun l hl hne => ?_) hatt
      obtain ⟨k_off, hk_mem, rfl⟩ := mem_fullArenaClauseLitsCore_of_fit (by omega) hl
      rcases Nat.eq_zero_or_pos k_off with rfl | hk_pos
      · simp only [Nat.add_zero] at hne
        rw [har3, Option.getD_some] at hne
        exact absurd rfl hne
      · exact hge k_off hk_pos (by omega)
  · intro J_k hJ_k
    exact hJ_k _ (1#64, nl_lvl, ()) m ⟨rfl, by decide,
      show (1#64).toNat ≤ csz.toNat by rw [bv64_ofNat_toNat_lt (by decide), hcsz]; omega,
      rfl, le_refl _,
      fun k_off h1 h2 => absurd h2 (by rw [bv64_ofNat_toNat_lt (by decide)]; omega),
      Or.inr ⟨not_lit.toNat, hnot_mem, hnot_ne_oth, hnl.symm⟩⟩

@[expose] def fidLpArSwapExpr {Val : Ty → Type} {Cont : List Ty → Type} {rs : List Ty}
    (arena : Val i64) (l0 not_lit other : Val i32) (cbase : Val i64)
    (J_sw : Cont []) : Expr Val Cont rs :=
  .let_ (Op.mk (.cmp .eq i32) (.var l0, (.var not_lit, ()))) fun eq0 =>
  .jnz (.var eq0.1)
    (.let_ (Op.mk (.mul i64) (.var cbase, (.imm 4, ()))) fun ao0 =>
     .let_ (Op.mk (.add i64) (.var arena, (.var ao0.1, ()))) fun ap0 =>
     .store (.var other) (.var ap0.1)
       (.let_ (Op.mk (.add i64) (.var cbase, (.imm 1, ()))) fun ci1 =>
        .let_ (Op.mk (.mul i64) (.var ci1.1, (.imm 4, ()))) fun ao1 =>
        .let_ (Op.mk (.add i64) (.var arena, (.var ao1.1, ()))) fun ap1 =>
        .store (.var not_lit) (.var ap1.1) (.jump J_sw ())))
    (.jump J_sw ())

theorem fid_lp_ar_swap_wp {Γ : Env} {rs : List Ty} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s_disk s_pi sem1 : FullState}
    {l0 l1 not_lit other cref : BitVec 32} {cbase off_v p_v q_v end_v : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post rs} {X : XPost} {J_sw : Cont []}
    (_har : c.arena_cap < 2 * dimacsBound)
    (hpi : PropLitInv c F0 F_cur s_pi sem1 not_lit.toNat off_v.toNat q_v.toNat
      (p_v.toNat + 2) end_v.toNat)
    (hcr_ref : cref.toNat ∈ fullArenaClauseRefsCore sem1.core)
    (hng : fullArenaClauseGarbCore sem1.core cref.toNat = false)
    (hsz3 : 3 ≤ fullArenaClauseSizeCore sem1.core cref.toNat)
    (hfit : cref.toNat + 3 + fullArenaClauseSizeCore sem1.core cref.toNat ≤ sem1.core.arena_len)
    (har3 : sem1.core.arena[cref.toNat + 3]? = some l0)
    (har4 : sem1.core.arena[cref.toNat + 4]? = some l1)
    (hwt : l0 = not_lit ∨ l1 = not_lit) (hoth : other = l0 ^^^ l1 ^^^ not_lit)
    (hcbase : cbase.toNat = cref.toNat + 3)
    (hm : (FullMem c (fastPropMem s_disk sem1) ⋆ R) m)
    (hJ_sw : ∀ (sem2 : FullState) (m2 : Mem 64),
      PropLitInv c F0 F_cur s_pi sem2 not_lit.toNat off_v.toNat q_v.toNat
        (p_v.toNat + 2) end_v.toNat →
      cref.toNat ∈ fullArenaClauseRefsCore sem2.core →
      fullArenaClauseGarbCore sem2.core cref.toNat = false →
      fullArenaClauseSizeCore sem2.core cref.toNat =
        fullArenaClauseSizeCore sem1.core cref.toNat →
      sem2.core.arena[cref.toNat + 3]? = some other →
      sem2.core.arena[cref.toNat + 4]? = some not_lit →
      sem2.core.vals = sem1.core.vals → sem2.core.lvl = sem1.core.lvl →
      sem2.core.trail_end = sem1.core.trail_end → sem2.core.unassigned = sem1.core.unassigned →
      sem2.core.unflushed = sem1.core.unflushed → sem2.core.oom = sem1.core.oom →
      S13ConflEq sem1.core sem2.core →
      (FullMem c (fastPropMem s_disk sem2) ⋆ R) m2 →
      wp Γ Q X (.jump J_sw ()) m2) :
    wp Γ Q X (fidLpArSwapExpr c.pArena l0 not_lit other cbase J_sw) m := by
  have haren := hpi.len.core_ok.arena_len_arr; have halen := hpi.len.core_ok.arena_len_le
  have hfit_cap : cref.toNat + 3 + fullArenaClauseSizeCore sem1.core cref.toNat ≤ c.arena_cap :=
    Nat.le_trans hfit halen
  unfold fidLpArSwapExpr
  s13_hsplit
  · have hwt0 : l0 = not_lit := hc
    obtain ⟨rfl, hpi2, hcr2, hcsz2, har3_2, har4_2⟩ :=
      m7_tB_swap_step hpi hcr_ref hng hsz3 hfit har3 har4 hwt0 hoth
    have h0_lt : cbase.toNat < (fastPropMem s_disk sem1).core.arena.length := by
      rw [fastPropMem_arena, haren, hcbase]; omega
    have hcb1 : (cbase + 1#64).toNat = cref.toNat + 4 := by
      rw [m7_bv64_add1_toNat (by rw [hcbase]; omega), hcbase]
    have h1_lt : (cbase + 1#64).toNat <
        { fastPropMem s_disk sem1 with core := { (fastPropMem s_disk sem1).core with
            arena := (fastPropMem s_disk sem1).core.arena.set cbase.toNat other }
        }.core.arena.length := by
      simp only [List.length_set, fastPropMem_arena]; rw [haren, hcb1]; omega
    s13_hsteps_nogrp
    have hng2 : fullArenaClauseGarbCore ({ sem1 with core := { sem1.core with
        arena := (sem1.core.arena.set (cref.toNat + 3) other).set (cref.toNat + 4) not_lit
        } }).core cref.toNat = false := by
      unfold fullArenaClauseGarbCore fullArenaHdrCore at hng ⊢
      simpa [List.getElem?_set_ne (by omega : cref.toNat + 4 ≠ cref.toNat),
        List.getElem?_set_ne (by omega : cref.toNat + 3 ≠ cref.toNat)] using hng
    rw [m7_fastPropMem_with_arena, m7_fastPropMem_with_arena] at hm
    simp only [fastPropMem_arena, hcbase,
      show (cbase + 1).toNat = cref.toNat + 4 from hcb1] at hm
    exact hJ_sw _ m hpi2 hcr2 hng2 hcsz2 har3_2 har4_2
      rfl rfl rfl rfl rfl rfl ⟨rfl, rfl, rfl, rfl⟩ hm
  · have hwt1 : l1 = not_lit := hwt.resolve_left hc
    subst hwt1
    have hoth_eq : other = l0 := by
      rw [hoth, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    subst hoth_eq
    exact hJ_sw sem1 m hpi hcr_ref hng rfl har3 har4 rfl rfl rfl rfl rfl rfl
      ⟨rfl, rfl, rfl, rfl⟩ hm
