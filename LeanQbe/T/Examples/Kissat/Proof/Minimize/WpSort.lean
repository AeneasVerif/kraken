/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Minimize.WpSortMerge
public import LeanQbe.T.Examples.Kissat.Src.Minimize
import LeanQbe.T.Examples.Kissat.Proof.Minimize.MinTactics
import LeanQbe.T.Examples.Kissat.Proof.Lib.ContractLemmas
import LeanQbe.T.Logic.C0Grind
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.Rules

/-!
# Canonical WP Soundness Proof for `full_sort_tmp`

Proves `full_sort_tmp_wp` for `Src.Minimize.full_sort_tmp_body` against `Spec.fullSortTmpSpec`:
- early return for `tlen ≤ 2` / `tlen > max_vars`;
- `tlen ≤ 32`: in-place level-only insertion sort (`wsort` untouched);
- `tlen > 32`: copy to `wsort` + `[min_l, max_l]` scan; `span == 1` return; `lvl`-only counting
  sort in `wsort[max_vars + b]` buckets; bottom-up merge-sort fallback (`s7_sort_merge_wp`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Minimize

open LeanQbe.T
open LeanQbe.T.C0Grind
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Minimize.FullMinTactics
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.Kissat.Src.Minimize

/-! ## 1. Framing Helpers & Pure List Lemmas -/

private theorem s7_get_tmp {st s : FullState} {t : List (BitVec 32)}
    (hc : st.core = { s.core with tmp := t }) {i : Nat} (hi : i < t.length) :
    st.core.tmp[i]'(by rw [hc]; exact hi) = t[i]'hi := by
  have h : st.core.tmp = t := by rw [hc]
  cases h; rfl

private theorem s7_get_wsort {st s : FullState} {ws : List (BitVec 32)}
    (hs : st.scratch = { s.scratch with wsort := ws }) {i : Nat} (hi : i < ws.length) :
    st.scratch.wsort[i]'(by rw [hs]; exact hi) = ws[i]'hi := by
  have h : st.scratch.wsort = ws := by rw [hs]
  cases h; rfl

private theorem s7_get_lvl_of {st s : FullState} {t : List (BitVec 32)}
    (hc : st.core = { s.core with tmp := t }) {i j : Nat} (hi : i < st.core.lvl.length)
    (hij : i = j) (hj : j < s.core.lvl.length) :
    st.core.lvl[i]'hi = s.core.lvl[j]'hj := by
  subst hij; simp only [hc]

private theorem s7_lshr1 (v : BitVec 32) :
    (v.setWidth 64 >>> ((BitVec.signExtend 64 1#32).toNat % 64)).toNat =
      v.toNat / 2 := by c0_bound

private theorem s7_lshr1_one (v : BitVec 32) :
    (v.setWidth 64 >>> (1 : Nat)).toNat = v.toNat / 2 := by c0_bound

private theorem s7_st_upd_tmp {st s : FullState} {t : List (BitVec 32)}
    (hc : st.core = { s.core with tmp := t }) {i : Nat} {v : BitVec 32} :
    ({ st with core := { st.core with tmp := st.core.tmp.set i v } }).core =
      { s.core with tmp := t.set i v } := by rw [hc]

private theorem s7_st_upd_wsort {st s : FullState} {ws : List (BitVec 32)}
    (hs : st.scratch = { s.scratch with wsort := ws }) {i : Nat} {v : BitVec 32} :
    ({ st with scratch := { st.scratch with wsort := st.scratch.wsort.set i v } }).scratch =
      { s.scratch with wsort := ws.set i v } := by rw [hs]

private theorem s7_state_eq {s1 s2 : FullState}
    (hc : s1.core = s2.core) (hs : s1.scratch = s2.scratch) : s1 = s2 := by
  cases s1; cases s2; simp at hc hs; subst hc; subst hs; rfl

private theorem s7Slice_congr_lt {α : Type _} {xs ys : List α} {lo hi : Nat}
    (hlo : lo ≤ hi) (hx : hi ≤ xs.length) (hy : hi ≤ ys.length)
    (heq : ∀ q < hi, xs[q]? = ys[q]?) :
    m7Slice xs lo hi = m7Slice ys lo hi := by
  apply List.ext_getElem
  · simp [m7Slice_length]; omega
  · intro k hk1 hk2
    rw [m7Slice_getElem, m7Slice_getElem]
    rw [m7Slice_length] at hk1
    have hlt : lo + k < hi := by omega
    have hq := heq (lo + k) hlt
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hq
    exact Option.some.inj hq

private theorem s7_drop_set_offset {α : Type _} (ws : List α) {mv b : Nat} (v : α)
    (hlen : ws.length = 2 * mv) (hb : b < mv) :
    (ws.set (mv + b) v).drop mv = (ws.drop mv).set b v := by
  apply List.ext_getElem
  · simp [hlen]
  · intro k hk1 hk2
    simp only [List.getElem_drop]
    by_cases hkb : k = b
    · subst hkb; simp
    · rw [List.getElem_set_ne (by omega), List.getElem_set_ne (by omega)]
      simp only [List.getElem_drop]

/-! ## 2. Phase Sub-AST Abbreviations (`rfl`-identical to `full_sort_tmp_body`) -/

private abbrev s7SortInsExpr {Val : Ty → Type} {Cont : List Ty → Type}
    (n64 pTmp pLvl : Val i64) : Expr Val Cont [] :=
  .group (sig := [[i64]]) (fun J1 =>
    .cons (fun xi =>
      .let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var xi.1, Arg.var n64, ())) fun c1 =>
      .jnz (Arg.var c1.1)
        (.let_ (Op.mk (.mul i64) (Arg.var xi.1, Arg.imm 4, ())) fun a1 =>
        .let_ (Op.mk (.add i64) (Arg.var pTmp, Arg.var a1.1, ())) fun a2 =>
        .load i32 (Arg.var a2.1) fun vx =>
        .let_ (Op.mk (.zext 32 64) (Arg.var vx, ())) fun a3 =>
        .let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun a4 =>
        .let_ (Op.mk (.lshr i64) (Arg.var a3.1, Arg.var a4.1, ())) fun a5 =>
        .let_ (Op.mk (.mul i64) (Arg.var a5.1, Arg.imm 4, ())) fun a6 =>
        .let_ (Op.mk (.add i64) (Arg.var pLvl, Arg.var a6.1, ())) fun a7 =>
        .load i32 (Arg.var a7.1) fun vlx =>
        .group (sig := [[i64]]) (fun J2 =>
          .cons (fun xj =>
            .group (sig := [[]]) (fun _ =>
              .cons (fun _ =>
                .let_ (Op.mk (.mul i64) (Arg.var xj.1, Arg.imm 4, ())) fun b1 =>
                .let_ (Op.mk (.add i64) (Arg.var pTmp, Arg.var b1.1, ())) fun b2 =>
                .store (t := i32) (Arg.var vx) (Arg.var b2.1) (
                  .let_ (Op.mk (.add i64) (Arg.var xi.1, Arg.imm 1, ())) fun b3 =>
                  .jump J1.1 (Arg.var b3.1, ())))
              .nil)
              (fun J3 =>
                .let_ (Op.mk (.cmp .ugt i64 .bool rfl) (Arg.var xj.1, Arg.imm 1, ())) fun c2 =>
                .jnz (Arg.var c2.1)
                  (.let_ (Op.mk (.sub i64) (Arg.var xj.1, Arg.imm 1, ())) fun d1 =>
                  .let_ (Op.mk (.mul i64) (Arg.var d1.1, Arg.imm 4, ())) fun d2 =>
                  .let_ (Op.mk (.add i64) (Arg.var pTmp, Arg.var d2.1, ())) fun d3 =>
                  .load i32 (Arg.var d3.1) fun vp =>
                  .let_ (Op.mk (.zext 32 64) (Arg.var vp, ())) fun d4 =>
                  .let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun d5 =>
                  .let_ (Op.mk (.lshr i64) (Arg.var d4.1, Arg.var d5.1, ())) fun d6 =>
                  .let_ (Op.mk (.mul i64) (Arg.var d6.1, Arg.imm 4, ())) fun d7 =>
                  .let_ (Op.mk (.add i64) (Arg.var pLvl, Arg.var d7.1, ())) fun d8 =>
                  .load i32 (Arg.var d8.1) fun vlp =>
                  .let_ (Op.mk (.cmp .ugt i32 .bool rfl) (Arg.var vlp, Arg.var vlx, ())) fun c3 =>
                  .jnz (Arg.var c3.1)
                    (.let_ (Op.mk (.mul i64) (Arg.var xj.1, Arg.imm 4, ())) fun e1 =>
                    .let_ (Op.mk (.add i64) (Arg.var pTmp, Arg.var e1.1, ())) fun e2 =>
                    .let_ (Op.mk (.sub i64) (Arg.var xj.1, Arg.imm 1, ())) fun e3 =>
                    .let_ (Op.mk (.mul i64) (Arg.var e3.1, Arg.imm 4, ())) fun e4 =>
                    .let_ (Op.mk (.add i64) (Arg.var pTmp, Arg.var e4.1, ())) fun e5 =>
                    .load i32 (Arg.var e5.1) fun vq =>
                    .store (t := i32) (Arg.var vq) (Arg.var e2.1) (
                      .let_ (Op.mk (.sub i64) (Arg.var xj.1, Arg.imm 1, ())) fun e6 =>
                      .jump J2.1 (Arg.var e6.1, ())))
                    (.jump J3.1 ()))
                  (.jump J3.1 ())))
          .nil)
          (fun J4 => .jump J4.1 (Arg.var xi.1, ())))
        (.ret ()))
    .nil)
    (fun J5 => .jump J5.1 (Arg.imm 2, ()))

private abbrev s7SortZeroExpr {Val : Ty → Type} {Cont : List Ty → Type}
    (mv64 span pWsort : Val i64) (kNext : Expr Val Cont []) : Expr Val Cont [] :=
  .group (sig := [[i64]]) (fun J48 =>
    .cons (fun x50 =>
      .let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var x50.1, Arg.var span, ())) fun x51 =>
      .jnz (Arg.var x51.1)
        (.let_ (Op.mk (.add i64) (Arg.var mv64, Arg.var x50.1, ())) fun xidx =>
        .let_ (Op.mk (.mul i64) (Arg.var xidx.1, Arg.imm 4, ())) fun x52 =>
        .let_ (Op.mk (.add i64) (Arg.var pWsort, Arg.var x52.1, ())) fun x53 =>
        .store (t := i32) (Arg.imm 0) (Arg.var x53.1) (
          .let_ (Op.mk (.add i64) (Arg.var x50.1, Arg.imm 1, ())) fun x54 =>
          .jump J48.1 (Arg.var x54.1, ())))
        (kNext))
    .nil)
    (fun J49 => .jump J49.1 (Arg.imm 0, ()))

private abbrev s7SortHistExpr {Val : Ty → Type} {Cont : List Ty → Type}
    (mv64 n64 pLvl pWsort : Val i64) (minL : Val i32)
    (kNext : Expr Val Cont []) : Expr Val Cont [] :=
  .group (sig := [[i64]]) (fun J55 =>
    .cons (fun x57 =>
      .let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var x57.1, Arg.var n64, ())) fun x58 =>
      .jnz (Arg.var x58.1)
        (.let_ (Op.mk (.mul i64) (Arg.var x57.1, Arg.imm 4, ())) fun x59 =>
        .let_ (Op.mk (.add i64) (Arg.var pWsort, Arg.var x59.1, ())) fun x60 =>
        .load i32 (Arg.var x60.1) fun v61 =>
        .let_ (Op.mk (.zext 32 64) (Arg.var v61, ())) fun x62 =>
        .let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun x63 =>
        .let_ (Op.mk (.lshr i64) (Arg.var x62.1, Arg.var x63.1, ())) fun x64 =>
        .let_ (Op.mk (.mul i64) (Arg.var x64.1, Arg.imm 4, ())) fun x65 =>
        .let_ (Op.mk (.add i64) (Arg.var pLvl, Arg.var x65.1, ())) fun x66 =>
        .load i32 (Arg.var x66.1) fun v67 =>
        .let_ (Op.mk (.zext 32 64) (Arg.var v67, ())) fun x68 =>
        .let_ (Op.mk (.zext 32 64) (Arg.var minL, ())) fun x69 =>
        .let_ (Op.mk (.sub i64) (Arg.var x68.1, Arg.var x69.1, ())) fun x70 =>
        .let_ (Op.mk (.add i64) (Arg.var mv64, Arg.var x70.1, ())) fun xidx1 =>
        .let_ (Op.mk (.mul i64) (Arg.var xidx1.1, Arg.imm 4, ())) fun x71 =>
        .let_ (Op.mk (.add i64) (Arg.var pWsort, Arg.var x71.1, ())) fun x72 =>
        .let_ (Op.mk (.add i64) (Arg.var mv64, Arg.var x70.1, ())) fun xidx2 =>
        .let_ (Op.mk (.mul i64) (Arg.var xidx2.1, Arg.imm 4, ())) fun x73 =>
        .let_ (Op.mk (.add i64) (Arg.var pWsort, Arg.var x73.1, ())) fun x74 =>
        .load i32 (Arg.var x74.1) fun v75 =>
        .let_ (Op.mk (.add i32) (Arg.var v75, Arg.imm 1, ())) fun x76 =>
        .store (t := i32) (Arg.var x76.1) (Arg.var x72.1) (
          .let_ (Op.mk (.add i64) (Arg.var x57.1, Arg.imm 1, ())) fun x77 =>
          .jump J55.1 (Arg.var x77.1, ())))
        (kNext))
    .nil)
    (fun J56 => .jump J56.1 (Arg.imm 1, ()))

private abbrev s7SortPrefExpr {Val : Ty → Type} {Cont : List Ty → Type}
    (mv64 span pWsort : Val i64) (kNext : Expr Val Cont []) : Expr Val Cont [] :=
  .group (sig := [[i64, i64]]) (fun J78 =>
    .cons (fun x80 =>
      .let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var x80.1, Arg.var span, ())) fun x81 =>
      .jnz (Arg.var x81.1)
        (.let_ (Op.mk (.add i64) (Arg.var mv64, Arg.var x80.1, ())) fun xidx1 =>
        .let_ (Op.mk (.mul i64) (Arg.var xidx1.1, Arg.imm 4, ())) fun x82 =>
        .let_ (Op.mk (.add i64) (Arg.var pWsort, Arg.var x82.1, ())) fun x83 =>
        .load i32 (Arg.var x83.1) fun v84 =>
        .let_ (Op.mk (.add i64) (Arg.var mv64, Arg.var x80.1, ())) fun xidx2 =>
        .let_ (Op.mk (.mul i64) (Arg.var xidx2.1, Arg.imm 4, ())) fun x85 =>
        .let_ (Op.mk (.add i64) (Arg.var pWsort, Arg.var x85.1, ())) fun x86 =>
        .let_ (Op.mk (.trunc 64 32) (Arg.var x80.2.1, ())) fun x87 =>
        .store (t := i32) (Arg.var x87.1) (Arg.var x86.1) (
          .let_ (Op.mk (.zext 32 64) (Arg.var v84, ())) fun x88 =>
          .let_ (Op.mk (.add i64) (Arg.var x80.2.1, Arg.var x88.1, ())) fun x89 =>
          .let_ (Op.mk (.add i64) (Arg.var x80.1, Arg.imm 1, ())) fun x90 =>
          .jump J78.1 (Arg.var x90.1, Arg.var x89.1, ())))
        (kNext))
    .nil)
    (fun J79 => .jump J79.1 (Arg.imm 0, Arg.imm 1, ()))

private abbrev s7SortScatExpr {Val : Ty → Type} {Cont : List Ty → Type}
    (mv64 n64 pTmp pLvl pWsort : Val i64) (minL : Val i32)
    (kNext : Expr Val Cont []) : Expr Val Cont [] :=
  .group (sig := [[i64]]) (fun J91 =>
    .cons (fun x93 =>
      .let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var x93.1, Arg.var n64, ())) fun x94 =>
      .jnz (Arg.var x94.1)
        (.let_ (Op.mk (.mul i64) (Arg.var x93.1, Arg.imm 4, ())) fun x95 =>
        .let_ (Op.mk (.add i64) (Arg.var pWsort, Arg.var x95.1, ())) fun x96 =>
        .load i32 (Arg.var x96.1) fun v97 =>
        .let_ (Op.mk (.zext 32 64) (Arg.var v97, ())) fun x98 =>
        .let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun x99 =>
        .let_ (Op.mk (.lshr i64) (Arg.var x98.1, Arg.var x99.1, ())) fun x100 =>
        .let_ (Op.mk (.mul i64) (Arg.var x100.1, Arg.imm 4, ())) fun x101 =>
        .let_ (Op.mk (.add i64) (Arg.var pLvl, Arg.var x101.1, ())) fun x102 =>
        .load i32 (Arg.var x102.1) fun v103 =>
        .let_ (Op.mk (.zext 32 64) (Arg.var v103, ())) fun x104 =>
        .let_ (Op.mk (.zext 32 64) (Arg.var minL, ())) fun x105 =>
        .let_ (Op.mk (.sub i64) (Arg.var x104.1, Arg.var x105.1, ())) fun x106 =>
        .let_ (Op.mk (.add i64) (Arg.var mv64, Arg.var x106.1, ())) fun xidx1 =>
        .let_ (Op.mk (.mul i64) (Arg.var xidx1.1, Arg.imm 4, ())) fun x107 =>
        .let_ (Op.mk (.add i64) (Arg.var pWsort, Arg.var x107.1, ())) fun x108 =>
        .load i32 (Arg.var x108.1) fun v109 =>
        .let_ (Op.mk (.zext 32 64) (Arg.var v109, ())) fun x110 =>
        .let_ (Op.mk (.add i64) (Arg.var mv64, Arg.var x106.1, ())) fun xidx2 =>
        .let_ (Op.mk (.mul i64) (Arg.var xidx2.1, Arg.imm 4, ())) fun x111 =>
        .let_ (Op.mk (.add i64) (Arg.var pWsort, Arg.var x111.1, ())) fun x112 =>
        .let_ (Op.mk (.add i64) (Arg.var x110.1, Arg.imm 1, ())) fun x113 =>
        .let_ (Op.mk (.trunc 64 32) (Arg.var x113.1, ())) fun x114 =>
        .store (t := i32) (Arg.var x114.1) (Arg.var x112.1) (
          .let_ (Op.mk (.mul i64) (Arg.var x110.1, Arg.imm 4, ())) fun x115 =>
          .let_ (Op.mk (.add i64) (Arg.var pTmp, Arg.var x115.1, ())) fun x116 =>
          .store (t := i32) (Arg.var v97) (Arg.var x116.1) (
            .let_ (Op.mk (.add i64) (Arg.var x93.1, Arg.imm 1, ())) fun x117 =>
            .jump J91.1 (Arg.var x117.1, ()))))
        (kNext))
    .nil)
    (fun J92 => .jump J92.1 (Arg.imm 1, ()))

/-! ## 3. Finishing Helper -/

/-- Finishing lemma deriving every `Spec.sortTmpSpec` postcondition from a slice
permutation, `tmp[0]` preservation and level-sortedness. -/
private theorem s7_finish_spec {c : FullCfg} {s st' : FullState}
    {tmp' ws' : List (BitVec 32)} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post []}
    (hlenOk : FullState.LengthsOk c s) (htl : s.core.tmp_len ≤ c.max_vars)
    (hc' : st'.core = { s.core with tmp := tmp' })
    (hs' : st'.scratch = { s.scratch with wsort := ws' })
    (hlen_t : tmp'.length = c.max_vars)
    (hlen_w : ws'.length = 2 * c.max_vars)
    (hle32_w : s.core.tmp_len ≤ 32 → ws' = s.scratch.wsort)
    (hperm : (m7Slice tmp' 1 s.core.tmp_len).Perm (m7Slice s.core.tmp 1 s.core.tmp_len))
    (h0 : 0 < s.core.tmp_len → tmp'[0]? = s.core.tmp[0]?)
    (hsort : ∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
      (s.core.lvl[(tmp'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
      (s.core.lvl[(tmp'[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hm' : (FullMem c st' ⋆ R) m')
    (hQ : ∀ (res : Tup Val []) (s' : FullState) m', s'.LengthsOk c →
      Spec.SortTmpPost s s' → (FullMem c s' ⋆ R) m' → Q res m') :
    Q () m' := by
  have hst_ok := m7SortTmp_stateOk c s tmp' ws' hlenOk hlen_t hlen_w
  have htake : (tmp'.take s.core.tmp_len).Perm (s.core.tmp.take s.core.tmp_len) := by
    by_cases hn0 : 0 < s.core.tmp_len
    · exact m7Slice_perm_to_take (h0 hn0) hperm hn0 (by rw [hlen_t]; exact htl)
        (by rw [hlenOk.core_ok.tmp_len_arr]; exact htl)
    · have : s.core.tmp_len = 0 := by omega
      simp [this]
  have hbij := m7Slice_perm_bij hperm (by rw [hlen_t]; exact htl)
    (by rw [hlenOk.core_ok.tmp_len_arr]; exact htl)
  have hst_eq : st' = FullState.mk { s.core with tmp := tmp' }
      { s.scratch with wsort := ws' } :=
    s7_state_eq hc' hs'
  exact hQ () st' m' (hst_eq ▸ hst_ok.1)
    ⟨by subst hst_eq; rfl, by rw [hs']; exact hle32_w, by rw [hc']; exact htake,
     by rw [hc']; exact h0, by rw [hc']; exact hbij.1, by rw [hc']; exact hbij.2,
     by rw [hc']; exact hsort⟩
    hm'

/-! ## 4. `tlen ≤ 32` Level-Only Insertion Sort -/

private theorem s7_sort_ins_wp {Γ : Env} {c : FullCfg} {s st0 : FullState}
    {sc0 : FullScratch} {R : Mem 64 → Prop} {m0 : Mem 64} {Q : Post []} {X : XPost}
    (htmp_len : s.core.tmp.length = c.max_vars)
    (hlvl_len : s.core.lvl.length = c.max_vars)
    (htl : s.core.tmp_len ≤ c.max_vars)
    (h2lt : 2 ≤ s.core.tmp_len)
    (hbd0 : ∀ p, 1 ≤ p → p < s.core.tmp_len →
      (s.core.tmp[p]?.getD 0#32).toNat < 2 * c.max_vars)
    (hc0 : st0.core = { s.core with tmp := s.core.tmp })
    (hs0 : st0.scratch = sc0)
    (hm0 : (FullMem c st0 ⋆ R) m0)
    (hPost : ∀ st' tmp' m',
      st'.core = { s.core with tmp := tmp' } → st'.scratch = sc0 →
      tmp'.length = c.max_vars →
      (m7Slice tmp' 1 s.core.tmp_len).Perm (m7Slice s.core.tmp 1 s.core.tmp_len) →
      tmp'[0]? = s.core.tmp[0]? →
      (∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
        (s.core.lvl[(tmp'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        (s.core.lvl[(tmp'[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      (FullMem c st' ⋆ R) m' → Q () m') :
    wp Γ Q X (s7SortInsExpr (BitVec.ofNat 64 s.core.tmp_len) c.pTmp c.pLevel) m0 := by
  let N := s.core.tmp_len
  let K : BitVec 32 → Nat := fun a => (s.core.lvl[a.toNat / 2]?.getD 0#32).toNat
  have hmv : c.max_vars < 2 ^ 32 := by have := c.hmaxv; unfold Ref.dimacsBound at this; omega
  let InvOut : Nat → Tup Val [i64] → Mem 64 → Prop := fun meas xs m =>
    ∃ i st tmp_i, xs.1 = BitVec.ofNat 64 i ∧ 2 ≤ i ∧ i ≤ N ∧ meas = N - i ∧
      st.core = { s.core with tmp := tmp_i } ∧ st.scratch = sc0 ∧
      tmp_i.length = c.max_vars ∧ (m7Slice tmp_i 1 N).Perm (m7Slice s.core.tmp 1 N) ∧
      tmp_i[0]? = s.core.tmp[0]? ∧
      (∀ a b, 1 ≤ a → a ≤ b → b < i → K (tmp_i[a]?.getD 0#32) ≤ K (tmp_i[b]?.getD 0#32)) ∧
      (FullMem c st ⋆ R) m
  refine wp_loop_group InvOut ?_ ?_
  · intro J1 meas xs m hm_ex ⟨i, st, tmp_i, hxs, hi2, hiN, hmeas, hst_c, hst_s, hlen_i,
      hperm_i, h0_i, hsort_i, hm⟩
    rcases xs with ⟨i_bv, ⟨⟩⟩; dsimp only at hxs; subst hxs
    rw [Blocks.get_here]; c0_hsplit
    · have hi_lt : i < N := by c0_grind
      have hi_i : (BitVec.ofNat 64 i).toNat = i := by c0_bound
      have hi_tmp : i < tmp_i.length := by rw [hlen_i]; omega
      have hi_st : (BitVec.ofNat 64 i).toNat < st.core.tmp.length := by
        rw [m7_core_tmp_eq hst_c, hlen_i, hi_i]; omega
      have hgi : st.core.tmp[(BitVec.ofNat 64 i).toNat]'hi_st = tmp_i[i]'hi_tmp := by
        simpa only [hi_i] using s7_get_tmp hst_c (i := i) hi_tmp
      have hbd_i : (tmp_i[i]'hi_tmp).toNat < 2 * c.max_vars := by
        have h := m7Slice_perm_bd hperm_i (by rw [hlen_i]; exact htl)
          (by rw [htmp_len]; exact htl) hbd0 i (by omega) hi_lt
        rwa [List.getElem?_eq_getElem hi_tmp, Option.getD_some] at h
      have hi_lvl : ((st.core.tmp[(BitVec.ofNat 64 i).toNat]'hi_st).setWidth 64 >>>
          ((BitVec.signExtend 64 1#32).toNat % 64)).toNat < st.core.lvl.length := by
        rw [hgi, s7_lshr1, m7_core_lvl_eq hst_c, hlvl_len]; omega
      let v7 := tmp_i[i]'hi_tmp
      have hv7_bd : v7.toNat < 2 * c.max_vars := hbd_i
      have hv7_lvl : v7.toNat / 2 < s.core.lvl.length := by rw [hlvl_len]; omega
      let v13 := s.core.lvl[v7.toNat / 2]'hv7_lvl
      have hK7 : K v7 = v13.toNat := by
        show (s.core.lvl[v7.toNat / 2]?.getD 0#32).toNat = v13.toNat
        rw [List.getElem?_eq_getElem hv7_lvl, Option.getD_some]
      c0_hsteps_nogrp
      let InvIn : Nat → Tup Val [i64] → Mem 64 → Prop := fun m_in ys m_cur =>
        ∃ j st_j tmp_j,
          ys.1 = BitVec.ofNat 64 j ∧ 1 ≤ j ∧ j ≤ i ∧ m_in = j ∧
          st_j.core = { s.core with tmp := tmp_j } ∧ st_j.scratch = sc0 ∧
          tmp_j.length = c.max_vars ∧
          (m7Slice (tmp_j.set j v7) 1 N).Perm (m7Slice s.core.tmp 1 N) ∧
          tmp_j[0]? = s.core.tmp[0]? ∧
          (∀ a b, 1 ≤ a → a ≤ b → b ≤ i → a ≠ j → b ≠ j →
            K (tmp_j[a]?.getD 0#32) ≤ K (tmp_j[b]?.getD 0#32)) ∧
          (∀ k, j < k → k ≤ i → K v7 ≤ K (tmp_j[k]?.getD 0#32)) ∧
          (FullMem c st_j ⋆ R) m_cur
      refine wp_loop_group InvIn ?_ ?_
      · intro J2 m_in ys m_cur hIH_in ⟨j, st_j, tmp_j, hys1, hj1, hji, hmin,
          hstj_c, hstj_s, hlen_j, hperm_j, h0_j, hinv_j, hgt_j, hm_j⟩
        rcases ys with ⟨j_bv, ⟨⟩⟩; dsimp only at hys1; subst hys1
        rw [Blocks.get_here]
        let Pex : Tup Val [] → Mem 64 → Prop := fun _ m' =>
          m' = m_cur ∧ (1 < j → K (tmp_j[j - 1]?.getD 0#32) ≤ K v7)
        refine wp_join_group Pex ?_ ?_
        · intro J3 _ m' ⟨hm_eq, hstop⟩
          subst hm_eq; rw [Blocks.get_here]
          have hj_i : (BitVec.ofNat 64 j).toNat = j := by c0_bound
          have hj_st : (BitVec.ofNat 64 j).toNat < st_j.core.tmp.length := by
            rw [m7_core_tmp_eq hstj_c, hlen_j, hj_i]; omega
          c0_hsteps!
          have hi1_bv : BitVec.ofNat 64 i + (1 : BitVec 64) = BitVec.ofNat 64 (i + 1) := by
            c0_bound
          rw [hi1_bv]
          have hsort_e := m7_ins_place_sorted (ltp := fun a b => K a ≤ K b)
            (fun _ => Nat.le_refl _) (fun _ _ _ => Nat.le_trans) (xs := tmp_j)
            (lo := 1) (i := i) (j := j) (x := v7) hj1 hji (by rw [hlen_j]; omega)
            hinv_j hstop hgt_j
          let core1 := st_j.core
          let tmp1 := core1.tmp.set (BitVec.ofNat 64 j).toNat
            (st.core.tmp[(BitVec.ofNat 64 i).toNat]'hi_st)
          refine hm_ex (N - (i + 1)) _ _ (by omega) ⟨i + 1,
            { core := { core1 with tmp := tmp1 }, scratch := st_j.scratch },
            tmp_j.set j v7, rfl, by omega, by omega, rfl, ?_, hstj_s, by simp [hlen_j],
            hperm_j, by rw [← h0_j]; exact List.getElem?_set_ne (by omega),
            fun a b ha hab hb => hsort_e a b ha hab (by omega), by assumption⟩
          · dsimp only [core1, tmp1]; rw [hgi, hj_i]; exact s7_st_upd_tmp hstj_c
        · intro J3 hExit3
          c0_hsplit
          · have hj_gt1 : 1 < j := by c0_grind
            have hj1_sub : BitVec.ofNat 64 j - (1 : BitVec 64) = BitVec.ofNat 64 (j - 1) := by
              c0_bound
            have hj1_i : (BitVec.ofNat 64 j - (1 : BitVec 64)).toNat = j - 1 := by
              rw [hj1_sub]; c0_bound
            have hj1_lt : j - 1 < tmp_j.length := by rw [hlen_j]; omega
            have hj1_st : (BitVec.ofNat 64 j - (1 : BitVec 64)).toNat < st_j.core.tmp.length := by
              rw [m7_core_tmp_eq hstj_c, hj1_i]; exact hj1_lt
            have hgj1 : st_j.core.tmp[(BitVec.ofNat 64 j - (1 : BitVec 64)).toNat]'hj1_st =
                tmp_j[j - 1]'hj1_lt := by
              simpa only [hj1_i] using s7_get_tmp hstj_c (i := j - 1) hj1_lt
            let v26 := tmp_j[j - 1]'hj1_lt
            have hv26_bd : v26.toNat < 2 * c.max_vars := by
              have h := m7Slice_perm_bd hperm_j (by simp [hlen_j]; exact htl)
                (by rw [htmp_len]; exact htl) hbd0 (j - 1) (by omega) (by omega)
              rwa [List.getElem?_set_ne (by omega), List.getElem?_eq_getElem hj1_lt,
                Option.getD_some] at h
            have hv26_lvl : v26.toNat / 2 < s.core.lvl.length := by
              have : v26.toNat < 2 * c.max_vars := hv26_bd
              rw [hlvl_len]; omega
            have hj1_lvl : ((st_j.core.tmp[(BitVec.ofNat 64 j - (1 : BitVec 64)).toNat]'hj1_st
                ).setWidth 64 >>> ((BitVec.signExtend 64 1#32).toNat % 64)).toNat <
                st_j.core.lvl.length := by
              have hbd26 : (tmp_j[j - 1]'hj1_lt).toNat < 2 * c.max_vars := hv26_bd
              rw [hgj1, s7_lshr1, m7_core_lvl_eq hstj_c, hlvl_len]; omega
            let v32 := s.core.lvl[v26.toNat / 2]'hv26_lvl
            have hv26_get : tmp_j[j - 1]?.getD 0#32 = v26 := by
              rw [List.getElem?_eq_getElem hj1_lt, Option.getD_some]
            have hK26 : K (tmp_j[j - 1]?.getD 0#32) = v32.toNat := by
              rw [hv26_get]
              show (s.core.lvl[v26.toNat / 2]?.getD 0#32).toNat = v32.toNat
              rw [List.getElem?_eq_getElem hv26_lvl, Option.getD_some]
            have hgj1_hc : st_j.core.tmp[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) + j) % 2 ^ 64]'(by
                have h : (2 ^ 64 - BitVec.toNat (1 : BitVec 64) + j) % 2 ^ 64 = j - 1 := by
                  rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega
                rw [h, m7_core_tmp_eq hstj_c]; exact hj1_lt) = v26 := by
              have h : (2 ^ 64 - BitVec.toNat (1 : BitVec 64) + j) % 2 ^ 64 = j - 1 := by
                rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega
              simpa only [h] using s7_get_tmp hstj_c (i := j - 1) hj1_lt
            have hgi_hc : st.core.tmp[i % 2 ^ 64]'(by
                have h : i % 2 ^ 64 = i := by c0_bound
                rw [h, m7_core_tmp_eq hst_c]; exact hi_tmp) = v7 := by
              have h : i % 2 ^ 64 = i := by c0_bound
              simpa only [h] using s7_get_tmp hst_c (i := i) hi_tmp
            c0_hsplit
            · have hlt_lv : v13.toNat < v32.toNat := by
                have hc' := hc
                rw [s7_get_lvl_of hstj_c _ (by rw [hgj1_hc, s7_lshr1_one]) hv26_lvl,
                  s7_get_lvl_of hst_c _ (by first | rw [hgi_hc, s7_lshr1_one] |
                    (rw [← hi_i] at *; rw [hgi, s7_lshr1_one])) hv7_lvl] at hc'
                c0_grind
              have hj_i : (BitVec.ofNat 64 j).toNat = j := by c0_bound
              have hj_st : (BitVec.ofNat 64 j).toNat < st_j.core.tmp.length := by
                rw [m7_core_tmp_eq hstj_c, hlen_j, hj_i]; omega
              c0_hsteps!
              rw [hj1_sub]
              let tmp_j' := tmp_j.set j v26
              have htmpj'_set : tmp_j' = tmp_j.set j (tmp_j[j - 1]?.getD 0#32) := by
                simp [tmp_j', hv26_get]
              have hshift := m7_ins_shift_inv (ltp := fun a b => K a ≤ K b) (xs := tmp_j)
                (lo := 1) (i := i) (j := j) (x := v7) hj_gt1 hji (by rw [hlen_j]; omega)
                hinv_j hgt_j (by rw [hK7, hK26]; omega)
              have hperm_j' :
                  (m7Slice (tmp_j'.set (j - 1) v7) 1 N).Perm (m7Slice s.core.tmp 1 N) :=
                (m7_shift_slice_perm (xs := tmp_j) (lo := 1) (hi := N) (j := j) (j' := j - 1)
                  v7 (by omega) (by omega) (by omega) (by rw [hlen_j]; exact htl)).trans hperm_j
              let core1 := st_j.core
              let tmp1 := core1.tmp.set (BitVec.ofNat 64 j).toNat
                (st_j.core.tmp[(BitVec.ofNat 64 j - (1 : BitVec 64)).toNat]'hj1_st)
              refine hIH_in (j - 1) _ _ (by omega) ⟨j - 1,
                { core := { core1 with tmp := tmp1 }, scratch := st_j.scratch },
                tmp_j', rfl, by omega, by omega, rfl, ?_, hstj_s, by simp [tmp_j', hlen_j],
                hperm_j', by dsimp [tmp_j']; rw [← h0_j]; exact List.getElem?_set_ne (by omega),
                by simpa [htmpj'_set] using hshift.1,
                by simpa [htmpj'_set] using hshift.2, by assumption⟩
              · dsimp only [core1, tmp1]; rw [hgj1, hj_i]; exact s7_st_upd_tmp hstj_c
            · have hge_lv : v32.toNat ≤ v13.toNat := by
                have hc' := hc
                rw [s7_get_lvl_of hstj_c _ (by rw [hgj1_hc, s7_lshr1_one]) hv26_lvl,
                  s7_get_lvl_of hst_c _ (by first | rw [hgi_hc, s7_lshr1_one] |
                    (rw [← hi_i] at *; rw [hgi, s7_lshr1_one])) hv7_lvl] at hc'
                c0_grind
              c0_hsteps!; exact hExit3 () m_cur ⟨rfl, fun _ => by rw [hK26, hK7]; exact hge_lv⟩
          · have hj_le1 : j ≤ 1 := by c0_grind
            c0_hsteps!; exact hExit3 () m_cur ⟨rfl, fun h => absurd h (by omega)⟩
      · intro J4 hExit4; c0_hsteps!
        refine hExit4 i _ m ⟨i, st, tmp_i, rfl, by omega, Nat.le_refl i, rfl, hst_c, hst_s,
          hlen_i, ?_, h0_i, ?_, fun k hk1 hk2 => by omega, hm⟩
        · have hset : tmp_i.set i v7 = tmp_i := by
            apply List.ext_getElem
            · simp
            · intro p hp1 hp2
              by_cases hpi : p = i
              · subst hpi; simp [v7]
              · simp [List.getElem_set_ne (Ne.symm hpi)]
          simpa [hset] using hperm_i
        · intro a b ha hab hbi _ _; exact hsort_i a b ha hab (by omega)
    · have hi_ge : N ≤ i := by c0_grind
      have hi_eq : i = N := by omega
      subst hi_eq; c0_hsteps!
      exact hPost st tmp_i m hst_c hst_s hlen_i hperm_i h0_i hsort_i hm
  · intro J5 hExit5; c0_hsteps!
    refine hExit5 (N - 2) _ m0
      ⟨2, st0, s.core.tmp, rfl, Nat.le_refl 2, h2lt, rfl, hc0, hs0, htmp_len, List.Perm.refl _,
        rfl, ?_, hm0⟩
    intro a b ha hab hb
    have ha1 : a = 1 := by omega
    have hb1 : b = 1 := by omega
    subst ha1; subst hb1; exact Nat.le_refl _

/-! ## 5. Counting-Sort Phase WP Proofs -/

private theorem s7_sort_zero_wp {Γ : Env} {c : FullCfg} {s st0 : FullState}
    {tmp0 ws0 : List (BitVec 32)} {R : Mem 64 → Prop} {m0 : Mem 64} {Q : Post []}
    {X : XPost} {span : Nat} {kNext : Expr Val Cont []}
    (hspan_le : span ≤ c.max_vars)
    (hc0 : st0.core = { s.core with tmp := tmp0 })
    (hs0 : st0.scratch = { s.scratch with wsort := ws0 })
    (hws_len : ws0.length = 2 * c.max_vars)
    (hm0 : (FullMem c st0 ⋆ R) m0)
    (hNext : ∀ st' ws' m',
      st'.core = { s.core with tmp := tmp0 } →
      st'.scratch = { s.scratch with wsort := ws' } →
      ws'.length = 2 * c.max_vars →
      (∀ q < c.max_vars, ws'[q]? = ws0[q]?) →
      (∀ b < span, (ws'[c.max_vars + b]?.getD 0#32).toNat = 0) →
      (FullMem c st' ⋆ R) m' → wp Γ Q X kNext m') :
    wp Γ Q X (s7SortZeroExpr (BitVec.ofNat 64 c.max_vars) (BitVec.ofNat 64 span) c.pWsort kNext)
      m0 := by
  have hmv : c.max_vars < 2 ^ 32 := by have := c.hmaxv; unfold Ref.dimacsBound at this; omega
  let Inv : Nat → Tup Val [i64] → Mem 64 → Prop := fun meas xs m =>
    ∃ k st ws_k, xs.1 = BitVec.ofNat 64 k ∧ k ≤ span ∧ meas = span - k ∧
      st.core = { s.core with tmp := tmp0 } ∧
      st.scratch = { s.scratch with wsort := ws_k } ∧
      ws_k.length = 2 * c.max_vars ∧
      (∀ q < c.max_vars, ws_k[q]? = ws0[q]?) ∧
      (∀ b < k, (ws_k[c.max_vars + b]?.getD 0#32).toNat = 0) ∧
      (FullMem c st ⋆ R) m
  refine wp_loop_group Inv ?_ ?_
  · intro J48 meas xs m hIH ⟨k, st, ws_k, hxs, hk_le, hmeas, hst_c, hst_s, hlen_ws, hpre, hz, hm⟩
    rcases xs with ⟨k_bv, ⟨⟩⟩; dsimp only at hxs; subst hxs
    rw [Blocks.get_here]; c0_hsplit
    · have hk_lt : k < span := by c0_grind
      have hidx : BitVec.ofNat 64 c.max_vars + BitVec.ofNat 64 k =
          BitVec.ofNat 64 (c.max_vars + k) := by c0_bound
      have hidx_n : (BitVec.ofNat 64 c.max_vars + BitVec.ofNat 64 k).toNat = c.max_vars + k := by
        rw [hidx]; c0_bound
      have hidx_st : (BitVec.ofNat 64 c.max_vars + BitVec.ofNat 64 k).toNat <
          st.scratch.wsort.length := by
        rw [hidx_n, m7_scr_ws_eq hst_s, hlen_ws]; omega
      c0_hsteps!
      have hk1_bv : BitVec.ofNat 64 k + (1 : BitVec 64) = BitVec.ofNat 64 (k + 1) := by c0_bound
      rw [hk1_bv]
      let ws' := ws_k.set (c.max_vars + k) 0#32
      let scr1 := st.scratch
      let ws1 := scr1.wsort.set (BitVec.ofNat 64 c.max_vars + BitVec.ofNat 64 k).toNat
        (BitVec.truncate 32 0#64)
      refine hIH (span - (k + 1)) _ _ (by omega) ⟨k + 1,
        { core := st.core, scratch := { scr1 with wsort := ws1 } }, ws', rfl, by omega, rfl,
        hst_c, ?_, by simp [ws', hlen_ws], fun q hq => by
          dsimp [ws']; rw [List.getElem?_set_ne (by omega)]; exact hpre q hq,
        fun b hb => ?_, hm⟩
      · dsimp only [scr1, ws1]
        rw [hidx_n, show BitVec.truncate 32 0#64 = 0#32 from rfl]
        exact s7_st_upd_wsort hst_s
      · by_cases hbk : b = k
        · subst hbk; dsimp [ws']
          rw [List.getElem?_eq_getElem (by simp [hlen_ws]; omega),
            List.getElem_set_self, Option.getD_some]; rfl
        · dsimp [ws']; rw [List.getElem?_set_ne (by omega)]; exact hz b (by omega)
    · have hk_ge : span ≤ k := by c0_grind
      have hk_eq : k = span := by omega
      subst hk_eq; c0_hsteps!
      exact hNext st ws_k m hst_c hst_s hlen_ws hpre hz hm
  · intro J49 hExit49; c0_hsteps!
    exact hExit49 span _ m0 ⟨0, st0, ws0, rfl, Nat.zero_le span, rfl, hc0, hs0, hws_len,
      fun _ _ => rfl, fun _ hb => by omega, hm0⟩

private theorem s7_sort_hist_wp {Γ : Env} {c : FullCfg} {s st0 : FullState}
    {ws0 : List (BitVec 32)} {R : Mem 64 → Prop} {m0 : Mem 64} {Q : Post []} {X : XPost}
    {minL_bv : BitVec 32} {span : Nat} {kNext : Expr Val Cont []}
    (hlvl_len : s.core.lvl.length = c.max_vars)
    (hle_mv : s.core.tmp_len ≤ c.max_vars) (h1N : 1 ≤ s.core.tmp_len)
    (hlen_ws0 : ws0.length = 2 * c.max_vars)
    (hspan_le : span ≤ c.max_vars)
    (hminmax : ∀ p, 1 ≤ p → p < s.core.tmp_len →
      minL_bv.toNat ≤ (s.core.lvl[(ws0[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
      (s.core.lvl[(ws0[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < minL_bv.toNat + span)
    (hbd_ws : ∀ p, 1 ≤ p → p < s.core.tmp_len → (ws0[p]?.getD 0#32).toNat < 2 * c.max_vars)
    (hzero : ∀ b < span, (ws0[c.max_vars + b]?.getD 0#32).toNat = 0)
    (hc0 : st0.core = { s.core with tmp := s.core.tmp })
    (hs0 : st0.scratch = { s.scratch with wsort := ws0 })
    (hm0 : (FullMem c st0 ⋆ R) m0)
    (hNext : ∀ st' ws' m',
      st'.core = { s.core with tmp := s.core.tmp } →
      st'.scratch = { s.scratch with wsort := ws' } →
      ws'.length = 2 * c.max_vars →
      (∀ q < c.max_vars, ws'[q]? = ws0[q]?) →
      (∀ b < span, (ws'[c.max_vars + b]?.getD 0#32).toNat =
        m7BktCnt s.core.lvl minL_bv.toNat (m7Slice ws0 1 s.core.tmp_len) b) →
      (FullMem c st' ⋆ R) m' → wp Γ Q X kNext m') :
    wp Γ Q X (s7SortHistExpr (BitVec.ofNat 64 c.max_vars) (BitVec.ofNat 64 s.core.tmp_len)
      c.pLevel c.pWsort minL_bv kNext) m0 := by
  let N := s.core.tmp_len
  let minL := minL_bv.toNat
  have hmv : c.max_vars < 2 ^ 32 := by have := c.hmaxv; unfold Ref.dimacsBound at this; omega
  let Inv : Nat → Tup Val [i64] → Mem 64 → Prop := fun meas xs m =>
    ∃ k st ws_k, xs.1 = BitVec.ofNat 64 k ∧ 1 ≤ k ∧ k ≤ N ∧ meas = N - k ∧
      st.core = { s.core with tmp := s.core.tmp } ∧
      st.scratch = { s.scratch with wsort := ws_k } ∧
      ws_k.length = 2 * c.max_vars ∧
      (∀ q < c.max_vars, ws_k[q]? = ws0[q]?) ∧
      (∀ b < span, (ws_k[c.max_vars + b]?.getD 0#32).toNat =
        m7BktCnt s.core.lvl minL (m7Slice ws0 1 k) b) ∧
      (FullMem c st ⋆ R) m
  refine wp_loop_group Inv ?_ ?_
  · intro J55 meas xs m hIH ⟨k, st, ws_k, hxs, hk1, hk_le, hmeas, hst_c, hst_s,
      hlen_wk, hpre, hcnt, hm⟩
    rcases xs with ⟨k_bv, ⟨⟩⟩; dsimp only at hxs; subst hxs
    rw [Blocks.get_here]; c0_hsplit
    · have hk_lt : k < N := by c0_grind
      have hk_i : (BitVec.ofNat 64 k).toNat = k := by c0_bound
      have hk_ws : k < ws_k.length := by rw [hlen_wk]; omega
      have hk_ws0 : k < ws0.length := by rw [hlen_ws0]; omega
      have hk_st : (BitVec.ofNat 64 k).toNat < st.scratch.wsort.length := by
        rw [m7_scr_ws_eq hst_s, hk_i]; exact hk_ws
      have hgk : st.scratch.wsort[(BitVec.ofNat 64 k).toNat]'hk_st = ws_k[k]'hk_ws := by
        simpa only [hk_i] using s7_get_wsort hst_s (i := k) hk_ws
      have hpre_k : ws_k[k]'hk_ws = ws0[k]'hk_ws0 := by
        have hq := hpre k (by omega)
        rw [List.getElem?_eq_getElem hk_ws, List.getElem?_eq_getElem hk_ws0] at hq
        exact Option.some.inj hq
      have hbd_k : (ws_k[k]'hk_ws).toNat < 2 * c.max_vars := by
        have h := hbd_ws k hk1 hk_lt
        rwa [List.getElem?_eq_getElem hk_ws0, Option.getD_some, ← hpre_k] at h
      have hk_lvl : ((st.scratch.wsort[(BitVec.ofNat 64 k).toNat]'hk_st).setWidth 64 >>>
          ((BitVec.signExtend 64 1#32).toNat % 64)).toNat < st.core.lvl.length := by
        rw [hgk, s7_lshr1, m7_core_lvl_eq hst_c, hlvl_len]; omega
      let v61 := ws_k[k]'hk_ws
      have hv61_bd : v61.toNat < 2 * c.max_vars := hbd_k
      have hv61_lvl : v61.toNat / 2 < s.core.lvl.length := by rw [hlvl_len]; omega
      let v67 := s.core.lvl[v61.toNat / 2]'hv61_lvl
      let wst_k := ws_k.drop c.max_vars
      have hwst_len : wst_k.length = c.max_vars := by simp [wst_k, hlen_wk]; omega
      have hsl_eq : m7Slice ws_k 1 N = m7Slice ws0 1 N :=
        s7Slice_congr_lt (by omega) (by rw [hlen_wk]; omega) (by rw [hlen_ws0]; omega)
          (fun q hq => hpre q (by omega))
      have hsl_k : m7Slice ws_k 1 k = m7Slice ws0 1 k :=
        s7Slice_congr_lt hk1 (by rw [hlen_wk]; omega) (by rw [hlen_ws0]; omega)
          (fun q hq => hpre q (by omega))
      have hminmax_k : ∀ p, 1 ≤ p → p < s.core.tmp_len →
          minL ≤ (s.core.lvl[(ws_k[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
          (s.core.lvl[(ws_k[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < minL + span := by
        intro p hp1 hp2; rw [show ws_k[p]? = ws0[p]? from hpre p (by omega)]
        exact hminmax p hp1 hp2
      have hcnt_wst : ∀ b < span, (wst_k[b]?.getD 0#32).toNat =
          m7BktCnt s.core.lvl minL (m7Slice ws_k 1 k) b := by
        intro b hb; dsimp [wst_k]; rw [List.getElem?_drop, hsl_k]; exact hcnt b hb
      have hstep := m7_hist_step_cnt hlvl_len hlen_wk hwst_len hk1 hk_lt hle_mv
        hminmax_k hcnt_wst hspan_le
      have hx_min : minL ≤ v67.toNat := by
        have h := (hminmax_k k hk1 hk_lt).1
        rwa [List.getElem?_eq_getElem hk_ws, Option.getD_some,
          List.getElem?_eq_getElem hv61_lvl, Option.getD_some] at h
      have hglvl : st.core.lvl[((st.scratch.wsort[(BitVec.ofNat 64 k).toNat]'hk_st).setWidth 64 >>>
          ((BitVec.signExtend 64 1#32).toNat % 64)).toNat]'hk_lvl = v67 :=
        s7_get_lvl_of hst_c _ (by rw [hgk, s7_lshr1]) hv61_lvl
      let bi := m7Bkt s.core.lvl minL v61
      have hbi_eq : v67.toNat - minL = bi := by
        dsimp [bi]; rw [m7Bkt_eq, List.getElem?_eq_getElem hv61_lvl, Option.getD_some]
      have hbi_lt : bi < span := hstep.1
      have hidx_n : (BitVec.ofNat 64 c.max_vars +
          ((st.core.lvl[((st.scratch.wsort[(BitVec.ofNat 64 k).toNat]'hk_st).setWidth 64 >>>
            ((BitVec.signExtend 64 1#32).toNat % 64)).toNat]'hk_lvl).setWidth 64 -
          minL_bv.setWidth 64)).toNat = c.max_vars + bi := by
        rw [hglvl]; dsimp [minL] at hx_min hbi_eq; c0_bound
      have hbi_w : c.max_vars + bi < ws_k.length := by rw [hlen_wk]; omega
      have hidx_st : (BitVec.ofNat 64 c.max_vars +
          ((st.core.lvl[((st.scratch.wsort[(BitVec.ofNat 64 k).toNat]'hk_st).setWidth 64 >>>
            ((BitVec.signExtend 64 1#32).toNat % 64)).toNat]'hk_lvl).setWidth 64 -
          minL_bv.setWidth 64)).toNat < st.scratch.wsort.length := by
        rw [hidx_n, m7_scr_ws_eq hst_s]; exact hbi_w
      have hgold : st.scratch.wsort[(BitVec.ofNat 64 c.max_vars +
          ((st.core.lvl[((st.scratch.wsort[(BitVec.ofNat 64 k).toNat]'hk_st).setWidth 64 >>>
            ((BitVec.signExtend 64 1#32).toNat % 64)).toNat]'hk_lvl).setWidth 64 -
          minL_bv.setWidth 64)).toNat]'hidx_st = ws_k[c.max_vars + bi]'hbi_w := by
        simpa only [hidx_n] using s7_get_wsort hst_s (i := c.max_vars + bi) hbi_w
      c0_hsteps!
      let old := ws_k[c.max_vars + bi]'hbi_w
      have hold_eq : old = wst_k[bi]'(by rw [hwst_len]; omega) := by
        dsimp [old, wst_k]; simp [List.getElem_drop]
      have hold_le : old.toNat + 1 ≤ k := hold_eq ▸ hstep.2.1
      have hold32 : old.toNat + 1 < 2 ^ 32 := by omega
      have hk1_bv : BitVec.ofNat 64 k + (1 : BitVec 64) = BitVec.ofNat 64 (k + 1) := by c0_bound
      rw [hk1_bv]
      let ws_k1 := ws_k.set (c.max_vars + bi) (BitVec.ofNat 32 (old.toNat + 1))
      have hpre1 : ∀ q < c.max_vars, ws_k1[q]? = ws0[q]? := fun q hq => by
        dsimp [ws_k1]; rw [List.getElem?_set_ne (by omega)]; exact hpre q hq
      have hsl_k1 : m7Slice ws_k 1 (k + 1) = m7Slice ws0 1 (k + 1) :=
        s7Slice_congr_lt (by omega) (by rw [hlen_wk]; omega) (by rw [hlen_ws0]; omega)
          (fun q hq => hpre q (by omega))
      let scr1 := st.scratch
      let idx_c := (BitVec.ofNat 64 c.max_vars +
          ((st.core.lvl[((st.scratch.wsort[(BitVec.ofNat 64 k).toNat]'hk_st).setWidth 64 >>>
            ((BitVec.signExtend 64 1#32).toNat % 64)).toNat]'hk_lvl).setWidth 64 -
          minL_bv.setWidth 64)).toNat
      let ws1 := scr1.wsort.set idx_c (st.scratch.wsort[idx_c]'hidx_st + 1#32)
      refine hIH (N - (k + 1)) _ _ (by omega) ⟨k + 1,
        { core := st.core, scratch := { scr1 with wsort := ws1 } },
        ws_k1, rfl, by omega, by omega, rfl, hst_c, ?_, by simp [ws_k1, hlen_wk], hpre1,
        fun b hb => ?_, hm⟩
      · dsimp only [scr1, ws1, idx_c]
        have hadd : old + 1#32 = BitVec.ofNat 32 (old.toNat + 1) := by c0_bound
        rw [hgold, hidx_n, hadd]
        exact s7_st_upd_wsort hst_s
      · have hd_drop : ws_k1.drop c.max_vars = wst_k.set bi (BitVec.ofNat 32 (old.toNat + 1)) :=
          s7_drop_set_offset ws_k _ hlen_wk (by omega)
        have hst_b := hstep.2.2.2 b hb
        rw [← hold_eq, ← hd_drop, List.getElem?_drop] at hst_b
        rwa [← hsl_k1]
    · have hk_ge : N ≤ k := by c0_grind
      have hk_eq : k = N := by omega
      subst hk_eq; c0_hsteps!
      exact hNext st ws_k m hst_c hst_s hlen_wk hpre hcnt hm
  · intro J56 hExit56; c0_hsteps!
    refine hExit56 (N - 1) _ m0 ⟨1, st0, ws0, rfl, Nat.le_refl 1, h1N, rfl, hc0, hs0, hlen_ws0,
      fun _ _ => rfl, fun b hb => ?_, hm0⟩
    rw [m7Slice_nil _ (Nat.le_refl 1), m7BktCnt_nil]; exact hzero b hb

private theorem s7_sort_pref_wp {Γ : Env} {c : FullCfg} {s st0 : FullState}
    {ws0 : List (BitVec 32)} {R : Mem 64 → Prop} {m0 : Mem 64} {Q : Post []} {X : XPost}
    {tot : Nat → Nat} {span : Nat} {kNext : Expr Val Cont []}
    (hlen_ws0 : ws0.length = 2 * c.max_vars)
    (hspan_le : span ≤ c.max_vars)
    (hspos_N : m7PrefixStart tot span ≤ c.max_vars)
    (hsuf0 : ∀ b < span, (ws0[c.max_vars + b]?.getD 0#32).toNat = tot b)
    (hc0 : st0.core = { s.core with tmp := s.core.tmp })
    (hs0 : st0.scratch = { s.scratch with wsort := ws0 })
    (hm0 : (FullMem c st0 ⋆ R) m0)
    (hNext : ∀ st' ws' m',
      st'.core = { s.core with tmp := s.core.tmp } →
      st'.scratch = { s.scratch with wsort := ws' } →
      ws'.length = 2 * c.max_vars →
      (∀ q < c.max_vars, ws'[q]? = ws0[q]?) →
      (∀ b < span, (ws'[c.max_vars + b]?.getD 0#32).toNat = m7PrefixStart tot b) →
      (FullMem c st' ⋆ R) m' → wp Γ Q X kNext m') :
    wp Γ Q X (s7SortPrefExpr (BitVec.ofNat 64 c.max_vars) (BitVec.ofNat 64 span) c.pWsort kNext)
      m0 := by
  have hmv : c.max_vars < 2 ^ 32 := by have := c.hmaxv; unfold Ref.dimacsBound at this; omega
  let Inv : Nat → Tup Val [i64, i64] → Mem 64 → Prop := fun meas xs m =>
    ∃ j st ws_j, xs.1 = BitVec.ofNat 64 j ∧ j ≤ span ∧ meas = span - j ∧
      xs.2.1.toNat = m7PrefixStart tot j ∧
      st.core = { s.core with tmp := s.core.tmp } ∧
      st.scratch = { s.scratch with wsort := ws_j } ∧
      ws_j.length = 2 * c.max_vars ∧
      (∀ q < c.max_vars, ws_j[q]? = ws0[q]?) ∧
      (∀ b, j ≤ b → b < span → (ws_j[c.max_vars + b]?.getD 0#32).toNat = tot b) ∧
      (∀ b < j, (ws_j[c.max_vars + b]?.getD 0#32).toNat = m7PrefixStart tot b) ∧
      (FullMem c st ⋆ R) m
  refine wp_loop_group Inv ?_ ?_
  · intro J78 meas xs m hIH ⟨j, st, ws_j, hxs1, hj_le, hmeas, hsum, hst_c, hst_s,
      hlen_ws, hpre_arr, hsuf, hpre, hm⟩
    rcases xs with ⟨j_bv, sum_bv, ⟨⟩⟩; dsimp only at hxs1 hsum; subst hxs1
    rw [Blocks.get_here]; c0_hsplit
    · have hj_lt : j < span := by c0_grind
      have hs_bd : m7PrefixStart tot (j + 1) < 2 ^ 32 := by
        have := m7PrefixStart_mono (tot := tot) (by omega : j + 1 ≤ span); omega
      let wst_j := ws_j.drop c.max_vars
      have hwst_len : wst_j.length = c.max_vars := by simp [wst_j, hlen_ws]; omega
      have hj_ws : c.max_vars + j < ws_j.length := by rw [hlen_ws]; omega
      have hidx_n : (BitVec.ofNat 64 c.max_vars + BitVec.ofNat 64 j).toNat = c.max_vars + j := by
        c0_bound
      have hj_st : (BitVec.ofNat 64 c.max_vars + BitVec.ofNat 64 j).toNat <
          st.scratch.wsort.length := by
        rw [hidx_n, m7_scr_ws_eq hst_s]; exact hj_ws
      have hgwj : st.scratch.wsort[(BitVec.ofNat 64 c.max_vars + BitVec.ofNat 64 j).toNat]'hj_st =
          ws_j[c.max_vars + j]'hj_ws := by
        simpa only [hidx_n] using s7_get_wsort hst_s (i := c.max_vars + j) hj_ws
      let wj := ws_j[c.max_vars + j]'hj_ws
      have hwj_drop : wj = wst_j[j]'(by rw [hwst_len]; omega) := by
        dsimp [wj, wst_j]; simp [List.getElem_drop]
      have hrs32 : sum_bv.toNat < 2 ^ 32 := by
        have : m7PrefixStart tot j ≤ m7PrefixStart tot (j + 1) := by
          rw [m7PrefixStart_succ]; exact Nat.le_add_right _ _
        omega
      c0_hsteps!
      have hsuf_w : ∀ b, j ≤ b → b < span → (wst_j[b]?.getD 0#32).toNat = tot b := by
        intro b hb1 hb2; dsimp [wst_j]; rw [List.getElem?_drop]; exact hsuf b hb1 hb2
      have hpre_w : ∀ b < j, (wst_j[b]?.getD 0#32).toNat = m7PrefixStart tot b := by
        intro b hb; dsimp [wst_j]; rw [List.getElem?_drop]; exact hpre b hb
      have hstep := m7_pref_step_inv hwst_len hj_lt hspan_le hsum hsuf_w hpre_w hs_bd
      have hj1_bv : BitVec.ofNat 64 j + (1 : BitVec 64) = BitVec.ofNat 64 (j + 1) := by c0_bound
      rw [hj1_bv, hgwj]
      let ws_j1 := ws_j.set (c.max_vars + j) (BitVec.ofNat 32 sum_bv.toNat)
      have hd_drop : ws_j1.drop c.max_vars = wst_j.set j (BitVec.ofNat 32 sum_bv.toNat) :=
        s7_drop_set_offset ws_j _ hlen_ws (by omega)
      let scr1 := st.scratch
      let ws1 := scr1.wsort.set
        (BitVec.ofNat 64 c.max_vars + BitVec.ofNat 64 j).toNat (BitVec.truncate 32 sum_bv)
      have hsum' : (sum_bv + wj.setWidth 64).toNat = m7PrefixStart tot (j + 1) := by
        rw [hwj_drop]; exact hstep.1
      refine hIH (span - (j + 1)) _ _ (by omega) ⟨j + 1,
        { core := st.core, scratch := { scr1 with wsort := ws1 } }, ws_j1, rfl, by omega, rfl,
        hsum',
        hst_c, ?_, by simp [ws_j1, hlen_ws],
        fun q hq => by dsimp [ws_j1]; rw [List.getElem?_set_ne (by omega)]; exact hpre_arr q hq,
        fun b hb1 hb2 => by
          have h := hstep.2.1 b hb1 hb2; rwa [← hd_drop, List.getElem?_drop] at h,
        fun b hb => by
          have h := hstep.2.2 b hb; rwa [← hd_drop, List.getElem?_drop] at h,
        hm⟩
      · dsimp only [scr1, ws1]
        have htr : BitVec.truncate 32 sum_bv = BitVec.ofNat 32 sum_bv.toNat := by c0_bound
        rw [hidx_n, htr]; exact s7_st_upd_wsort hst_s
    · have hj_ge : span ≤ j := by c0_grind
      have hj_eq : j = span := by omega
      subst hj_eq; c0_hsteps!
      exact hNext st ws_j m hst_c hst_s hlen_ws hpre_arr hpre hm
  · intro J79 hExit79; c0_hsteps!
    refine hExit79 span _ m0 ⟨0, st0, ws0, rfl, Nat.zero_le span, rfl, ?_, hc0, hs0, hlen_ws0,
      fun _ _ => rfl, fun b _ hb => hsuf0 b hb, fun _ hb => by omega, hm0⟩
    rw [m7PrefixStart_zero]; rfl

private theorem s7_sort_scat_wp {Γ : Env} {c : FullCfg} {s st0 : FullState}
    {ws0 : List (BitVec 32)} {R : Mem 64 → Prop} {m0 : Mem 64} {Q : Post []} {X : XPost}
    {minL_bv : BitVec 32} {span : Nat} {kNext : Expr Val Cont []}
    (htmp_len : s.core.tmp.length = c.max_vars)
    (hlvl_len : s.core.lvl.length = c.max_vars)
    (htl : s.core.tmp_len ≤ c.max_vars) (h1N : 1 ≤ s.core.tmp_len)
    (hlen_ws0 : ws0.length = 2 * c.max_vars)
    (hspan_le : span ≤ c.max_vars)
    (hsl_ws : m7Slice ws0 1 s.core.tmp_len = m7Slice s.core.tmp 1 s.core.tmp_len)
    (hminmax : ∀ p, 1 ≤ p → p < s.core.tmp_len →
      minL_bv.toNat ≤ (s.core.lvl[(ws0[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
      (s.core.lvl[(ws0[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < minL_bv.toNat + span)
    (hbd_ws : ∀ p, 1 ≤ p → p < s.core.tmp_len → (ws0[p]?.getD 0#32).toNat < 2 * c.max_vars)
    (hspos_N : m7PrefixStart (m7BktCnt s.core.lvl minL_bv.toNat (m7Slice ws0 1 s.core.tmp_len))
      span = s.core.tmp_len)
    (hspos_le : ∀ b ≤ span, m7PrefixStart
      (m7BktCnt s.core.lvl minL_bv.toNat (m7Slice ws0 1 s.core.tmp_len)) b ≤ s.core.tmp_len)
    (hspos0 : ∀ b < span, (ws0[c.max_vars + b]?.getD 0#32).toNat = m7PrefixStart
      (m7BktCnt s.core.lvl minL_bv.toNat (m7Slice ws0 1 s.core.tmp_len)) b)
    (hc0 : st0.core = { s.core with tmp := s.core.tmp })
    (hs0 : st0.scratch = { s.scratch with wsort := ws0 })
    (hm0 : (FullMem c st0 ⋆ R) m0)
    (hNext : ∀ st' tmp' ws' m',
      st'.core = { s.core with tmp := tmp' } →
      st'.scratch = { s.scratch with wsort := ws' } →
      tmp'.length = c.max_vars → ws'.length = 2 * c.max_vars →
      (m7Slice tmp' 1 s.core.tmp_len).Perm (m7Slice s.core.tmp 1 s.core.tmp_len) →
      tmp'[0]? = s.core.tmp[0]? →
      (∀ q, s.core.tmp_len ≤ q → tmp'[q]? = s.core.tmp[q]?) →
      (∀ i j, 1 ≤ i → i ≤ j → j < s.core.tmp_len →
        (s.core.lvl[(tmp'[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        (s.core.lvl[(tmp'[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      (FullMem c st' ⋆ R) m' → wp Γ Q X kNext m') :
    wp Γ Q X (s7SortScatExpr (BitVec.ofNat 64 c.max_vars) (BitVec.ofNat 64 s.core.tmp_len)
      c.pTmp c.pLevel c.pWsort minL_bv kNext) m0 := by
  let N := s.core.tmp_len
  let minL := minL_bv.toNat
  let tot := m7BktCnt s.core.lvl minL (m7Slice ws0 1 N)
  let spos := m7PrefixStart tot
  have hmv : c.max_vars < 2 ^ 32 := by have := c.hmaxv; unfold Ref.dimacsBound at this; omega
  let Inv : Nat → Tup Val [i64] → Mem 64 → Prop := fun meas xs m =>
    ∃ k_s st tmp_s ws_s, xs.1 = BitVec.ofNat 64 k_s ∧ 1 ≤ k_s ∧ k_s ≤ N ∧ meas = N - k_s ∧
      st.core = { s.core with tmp := tmp_s } ∧
      st.scratch = { s.scratch with wsort := ws_s } ∧
      tmp_s.length = c.max_vars ∧ ws_s.length = 2 * c.max_vars ∧
      (∀ q < c.max_vars, ws_s[q]? = ws0[q]?) ∧
      tmp_s[0]? = s.core.tmp[0]? ∧ (∀ q, N ≤ q → tmp_s[q]? = s.core.tmp[q]?) ∧
      (∀ b < span, (ws_s[c.max_vars + b]?.getD 0#32).toNat =
        spos b + m7BktCnt s.core.lvl minL (m7Slice ws0 1 k_s) b) ∧
      (∀ b < span, ∀ p, spos b ≤ p → p < (ws_s[c.max_vars + b]?.getD 0#32).toNat →
        m7Bkt s.core.lvl minL (tmp_s[p]?.getD 0#32) = b ∧
        minL ≤ (s.core.lvl[(tmp_s[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
      (m7FlatBkts tmp_s spos (fun b => (ws_s[c.max_vars + b]?.getD 0#32).toNat) span).Perm
        (m7Slice ws0 1 k_s) ∧
      (FullMem c st ⋆ R) m
  refine wp_loop_group Inv ?_ ?_
  · intro J91 meas xs m hIH ⟨k_s, st, tmp_s, ws_s, hxs, hk1, hk_le, hmeas, hst_c, hst_s,
      hlen_ts, hlen_ws, hpre, h0_s, hout_s, hepos_s, hbkt_s, hperm_s, hm⟩
    rcases xs with ⟨ks_bv, ⟨⟩⟩; dsimp only at hxs; subst hxs
    rw [Blocks.get_here]; c0_hsplit
    · have hk_lt : k_s < N := by c0_grind
      have hks_i : (BitVec.ofNat 64 k_s).toNat = k_s := by c0_bound
      have hks_ws : k_s < ws_s.length := by rw [hlen_ws]; omega
      have hks_ws0 : k_s < ws0.length := by rw [hlen_ws0]; omega
      have hks_st : (BitVec.ofNat 64 k_s).toNat < st.scratch.wsort.length := by
        rw [m7_scr_ws_eq hst_s, hks_i]; exact hks_ws
      have hgks : st.scratch.wsort[(BitVec.ofNat 64 k_s).toNat]'hks_st = ws_s[k_s]'hks_ws := by
        simpa only [hks_i] using s7_get_wsort hst_s (i := k_s) hks_ws
      have hpre_k : ws_s[k_s]'hks_ws = ws0[k_s]'hks_ws0 := by
        have hq := hpre k_s (by omega)
        rw [List.getElem?_eq_getElem hks_ws, List.getElem?_eq_getElem hks_ws0] at hq
        exact Option.some.inj hq
      have hbd_k : (ws_s[k_s]'hks_ws).toNat < 2 * c.max_vars := by
        have h := hbd_ws k_s hk1 hk_lt
        rwa [List.getElem?_eq_getElem hks_ws0, Option.getD_some, ← hpre_k] at h
      have hks_lvl : ((st.scratch.wsort[(BitVec.ofNat 64 k_s).toNat]'hks_st).setWidth 64 >>>
          ((BitVec.signExtend 64 1#32).toNat % 64)).toNat < st.core.lvl.length := by
        rw [hgks, s7_lshr1, m7_core_lvl_eq hst_c, hlvl_len]; omega
      let v97 := ws_s[k_s]'hks_ws
      have hv97_bd : v97.toNat < 2 * c.max_vars := hbd_k
      have hv97_lvl : v97.toNat / 2 < s.core.lvl.length := by rw [hlvl_len]; omega
      let v103 := s.core.lvl[v97.toNat / 2]'hv97_lvl
      let wst_s := ws_s.drop c.max_vars
      have hwst_len : wst_s.length = c.max_vars := by simp [wst_s, hlen_ws]; omega
      have hsl_eq : m7Slice ws_s 1 N = m7Slice ws0 1 N :=
        s7Slice_congr_lt (by omega) (by rw [hlen_ws]; omega) (by rw [hlen_ws0]; omega)
          (fun q hq => hpre q (by omega))
      have hsl_ks : m7Slice ws_s 1 k_s = m7Slice ws0 1 k_s :=
        s7Slice_congr_lt hk1 (by rw [hlen_ws]; omega) (by rw [hlen_ws0]; omega)
          (fun q hq => hpre q (by omega))
      have hminmax_s : ∀ p, 1 ≤ p → p < N →
          minL ≤ (s.core.lvl[(ws_s[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
          (s.core.lvl[(ws_s[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < minL + span := by
        intro p hp1 hp2; rw [show ws_s[p]? = ws0[p]? from hpre p (by omega)]
        exact hminmax p hp1 hp2
      have hstep := m7_scat_step_inv hlen_ws hlen_ts hwst_len htl hk1 hk_lt hspan_le
        hminmax_s (by rw [hsl_eq]; exact hspos_N) (by intro b hb; rw [hsl_eq]; exact hspos_le b hb)
        h0_s hout_s
        (fun b hb => by dsimp [wst_s]; rw [List.getElem?_drop, hsl_eq, hsl_ks]; exact hepos_s b hb)
        (fun b hb p hp1 hp2 => by
          dsimp [wst_s] at hp2; rw [List.getElem?_drop] at hp2
          rw [hsl_eq] at hp1; exact hbkt_s b hb p hp1 hp2)
        (by
          have hcon : m7FlatBkts tmp_s
              (m7PrefixStart (m7BktCnt s.core.lvl minL (m7Slice ws_s 1 N)))
              (fun b => (wst_s[b]?.getD 0#32).toNat) span =
              m7FlatBkts tmp_s spos (fun b => (ws_s[c.max_vars + b]?.getD 0#32).toNat) span := by
            have h1 : m7PrefixStart (m7BktCnt s.core.lvl minL (m7Slice ws_s 1 N)) = spos := by
              rw [hsl_eq]
            rw [h1]; simp only [wst_s, List.getElem?_drop]
          rw [hcon, hsl_ks]; exact hperm_s)
      have hx_min : minL ≤ v103.toNat := by
        have h := (hminmax_s k_s hk1 hk_lt).1
        rwa [List.getElem?_eq_getElem hks_ws, Option.getD_some,
          List.getElem?_eq_getElem hv97_lvl, Option.getD_some] at h
      have hglvl :
          st.core.lvl[((st.scratch.wsort[(BitVec.ofNat 64 k_s).toNat]'hks_st).setWidth 64 >>>
          ((BitVec.signExtend 64 1#32).toNat % 64)).toNat]'hks_lvl = v103 :=
        s7_get_lvl_of hst_c _ (by rw [hgks, s7_lshr1]) hv97_lvl
      let bi := m7Bkt s.core.lvl minL v97
      have hbi_eq : v103.toNat - minL = bi := by
        dsimp [bi]; rw [m7Bkt_eq, List.getElem?_eq_getElem hv97_lvl, Option.getD_some]
      have hbi_lt : bi < span := hstep.1
      have hidx_n : (BitVec.ofNat 64 c.max_vars +
          ((st.core.lvl[((st.scratch.wsort[(BitVec.ofNat 64 k_s).toNat]'hks_st).setWidth 64 >>>
            ((BitVec.signExtend 64 1#32).toNat % 64)).toNat]'hks_lvl).setWidth 64 -
          minL_bv.setWidth 64)).toNat = c.max_vars + bi := by
        rw [hglvl]; dsimp [minL] at hx_min hbi_eq; c0_bound
      have hbi_w : c.max_vars + bi < ws_s.length := by rw [hlen_ws]; omega
      have hidx_st : (BitVec.ofNat 64 c.max_vars +
          ((st.core.lvl[((st.scratch.wsort[(BitVec.ofNat 64 k_s).toNat]'hks_st).setWidth 64 >>>
            ((BitVec.signExtend 64 1#32).toNat % 64)).toNat]'hks_lvl).setWidth 64 -
          minL_bv.setWidth 64)).toNat < st.scratch.wsort.length := by
        rw [hidx_n, m7_scr_ws_eq hst_s]; exact hbi_w
      have hgdst : st.scratch.wsort[(BitVec.ofNat 64 c.max_vars +
          ((st.core.lvl[((st.scratch.wsort[(BitVec.ofNat 64 k_s).toNat]'hks_st).setWidth 64 >>>
            ((BitVec.signExtend 64 1#32).toNat % 64)).toNat]'hks_lvl).setWidth 64 -
          minL_bv.setWidth 64)).toNat]'hidx_st = ws_s[c.max_vars + bi]'hbi_w := by
        simpa only [hidx_n] using s7_get_wsort hst_s (i := c.max_vars + bi) hbi_w
      let dst_bv := ws_s[c.max_vars + bi]'hbi_w
      let dst := dst_bv.toNat
      have hdst_eq : dst_bv = wst_s[bi]'(by rw [hwst_len]; omega) := by
        dsimp [dst_bv, wst_s]; simp [List.getElem_drop]
      have hdst_ge1 : 1 ≤ dst := by dsimp [dst]; rw [hdst_eq]; exact hstep.2.1
      have hdst1_32 : dst + 1 < 2 ^ 32 := by dsimp [dst]; rw [hdst_eq]; exact hstep.2.2.2.1
      have hdst_lt : dst < N := by dsimp [dst]; rw [hdst_eq]; exact hstep.2.2.1
      have hdst_ts : dst < tmp_s.length := by rw [hlen_ts]; omega
      have hdst_st : ((st.scratch.wsort[(BitVec.ofNat 64 c.max_vars +
          ((st.core.lvl[((st.scratch.wsort[(BitVec.ofNat 64 k_s).toNat]'hks_st).setWidth 64 >>>
            ((BitVec.signExtend 64 1#32).toNat % 64)).toNat]'hks_lvl).setWidth 64 -
          minL_bv.setWidth 64)).toNat]'hidx_st).setWidth 64).toNat < st.core.tmp.length := by
        rw [hgdst, m7_core_tmp_eq hst_c, hlen_ts]
        change (dst_bv.setWidth 64).toNat < c.max_vars; c0_bound
      c0_hsteps!
      have hk1_bv : BitVec.ofNat 64 k_s + (1 : BitVec 64) = BitVec.ofNat 64 (k_s + 1) := by c0_bound
      rw [hk1_bv]
      let ws_s1 := ws_s.set (c.max_vars + bi) (BitVec.ofNat 32 (dst + 1))
      have hpre1 : ∀ q < c.max_vars, ws_s1[q]? = ws0[q]? := fun q hq => by
        dsimp [ws_s1]; rw [List.getElem?_set_ne (by omega)]; exact hpre q hq
      have hd_drop : ws_s1.drop c.max_vars = wst_s.set bi (BitVec.ofNat 32 (dst + 1)) :=
        s7_drop_set_offset ws_s _ hlen_ws (by omega)
      have hdst_raw : dst_bv =
          wst_s[m7Bkt s.core.lvl minL ws_s[k_s]]'(by rw [hwst_len]; have := hstep.1; omega) := by
        simpa only [bi, v97] using hdst_eq
      have hd_drop_raw : ws_s1.drop c.max_vars =
          wst_s.set (m7Bkt s.core.lvl minL ws_s[k_s])
            (BitVec.ofNat 32 (wst_s[m7Bkt s.core.lvl minL ws_s[k_s]].toNat + 1)) := by
        simpa only [bi, v97, dst, hdst_raw] using hd_drop
      have hsl_k1 : m7Slice ws_s 1 (k_s + 1) = m7Slice ws0 1 (k_s + 1) :=
        s7Slice_congr_lt (by omega) (by rw [hlen_ws]; omega) (by rw [hlen_ws0]; omega)
          (fun q hq => hpre q (by omega))
      let core1 := st.core
      let scr1 := st.scratch
      let idx_c := (BitVec.ofNat 64 c.max_vars +
          ((st.core.lvl[((st.scratch.wsort[(BitVec.ofNat 64 k_s).toNat]'hks_st).setWidth 64 >>>
            ((BitVec.signExtend 64 1#32).toNat % 64)).toNat]'hks_lvl).setWidth 64 -
          minL_bv.setWidth 64)).toNat
      let tmp1 := core1.tmp.set
        ((st.scratch.wsort[idx_c]'hidx_st).setWidth 64).toNat
        (st.scratch.wsort[(BitVec.ofNat 64 k_s).toNat]'hks_st)
      let ws1 := scr1.wsort.set idx_c
        (BitVec.truncate 32 ((st.scratch.wsort[idx_c]'hidx_st).setWidth 64 + 1#64))
      refine hIH (N - (k_s + 1)) _ _ (by omega) ⟨k_s + 1,
        { core := { core1 with tmp := tmp1 }, scratch := { scr1 with wsort := ws1 } },
        tmp_s.set dst v97, ws_s1, rfl, by omega, by omega, rfl, ?_, ?_, by simp [hlen_ts],
        by simp [ws_s1, hlen_ws], hpre1,
        by rw [List.getElem?_set_ne (by omega)]; exact h0_s,
        fun q hq => by rw [List.getElem?_set_ne (by omega)]; exact hout_s q hq,
        fun b hb => by
          have h := hstep.2.2.2.2.2.2.2.2.1 b hb
          simpa only [spos, minL, N, ← hd_drop_raw, List.getElem?_drop, hsl_eq, hsl_k1] using h,
        fun b hb p hp1 hp2 => by
          have h := hstep.2.2.2.2.2.2.2.2.2.1 b hb p
            (by simpa only [spos, tot, minL, N, hsl_eq] using hp1)
            (by simpa only [← hd_drop_raw, List.getElem?_drop] using hp2)
          simpa only [dst, v97, ← hdst_raw] using h,
        by
          have h := hstep.2.2.2.2.2.2.2.2.2.2
          rw [← hd_drop_raw, ← hdst_raw] at h
          have hcon : m7FlatBkts (tmp_s.set dst v97) spos
              (fun b => (ws_s1[c.max_vars + b]?.getD 0#32).toNat) span =
              m7FlatBkts (tmp_s.set dst v97)
                (m7PrefixStart (m7BktCnt s.core.lvl minL (m7Slice ws_s 1 N)))
                (fun b => ((ws_s1.drop c.max_vars)[b]?.getD 0#32).toNat) span := by
            have h1 : m7PrefixStart (m7BktCnt s.core.lvl minL (m7Slice ws_s 1 N)) = spos := by
              rw [hsl_eq]
            rw [h1]; simp [List.getElem?_drop]
          rw [hcon]; simpa only [dst, v97, N, hsl_k1] using h,
        hm⟩
      · dsimp only [core1, tmp1]
        have htr : ((st.scratch.wsort[idx_c]'hidx_st).setWidth 64).toNat = dst := by
          rw [hgdst]; dsimp [dst]; c0_bound
        rw [hgks, htr]; exact s7_st_upd_tmp hst_c
      · dsimp only [scr1, ws1]
        have htr : BitVec.truncate 32 ((st.scratch.wsort[idx_c]'hidx_st).setWidth 64 + 1#64) =
            BitVec.ofNat 32 (dst + 1) := by
          rw [hgdst]; change BitVec.truncate 32 (dst_bv.setWidth 64 + 1#64) = _; c0_bound
        rw [htr, show idx_c = c.max_vars + bi from hidx_n]; exact s7_st_upd_wsort hst_s
    · have hk_ge : N ≤ k_s := by c0_grind
      have hk_eq : k_s = N := by omega
      subst hk_eq; c0_hsteps!
      have hsl_eq : m7Slice ws_s 1 N = m7Slice ws0 1 N :=
        s7Slice_congr_lt (by omega) (by rw [hlen_ws]; omega) (by rw [hlen_ws0]; omega)
          (fun q hq => hpre q (by omega))
      have hfin := m7_scat_finish_inv hlen_ts htl (hsl_eq.trans hsl_ws)
        (by rw [hsl_eq]; exact hspos_N)
        (fun b hb => by rw [List.getElem?_drop, hsl_eq]; exact hepos_s b hb)
        (fun b hb p hp1 hp2 => by
          rw [List.getElem?_drop] at hp2; rw [hsl_eq] at hp1; exact hbkt_s b hb p hp1 hp2)
        (by
          have hcon : m7FlatBkts tmp_s
              (m7PrefixStart (m7BktCnt s.core.lvl minL (m7Slice ws_s 1 N)))
              (fun b => ((ws_s.drop c.max_vars)[b]?.getD 0#32).toNat) span =
              m7FlatBkts tmp_s spos (fun b => (ws_s[c.max_vars + b]?.getD 0#32).toNat) span := by
            have h1 : m7PrefixStart (m7BktCnt s.core.lvl minL (m7Slice ws_s 1 N)) = spos := by
              rw [hsl_eq]
            rw [h1]; simp [List.getElem?_drop]
          rw [hcon, hsl_eq]; exact hperm_s)
      exact hNext st tmp_s ws_s m hst_c hst_s hlen_ts hlen_ws hfin.1 h0_s hout_s hfin.2 hm
  · intro J92 hExit92; c0_hsteps!
    refine hExit92 (N - 1) _ m0 ⟨1, st0, s.core.tmp, ws0, rfl, Nat.le_refl 1, h1N, rfl, hc0, hs0,
      htmp_len, hlen_ws0, fun _ _ => rfl, rfl, fun _ _ => rfl, ?_, ?_, ?_, hm0⟩
    · intro b hb; rw [m7Slice_nil _ (Nat.le_refl 1), m7BktCnt_nil, Nat.add_zero]; exact hspos0 b hb
    · intro b hb p hp1 hp2
      change spos b ≤ p at hp1; rw [hspos0 b hb] at hp2
      dsimp only [spos, tot, minL, N] at hp1; omega
    · rw [m7FlatBkts_nil _ _ _ _ (fun b hb => by
          rw [hspos0 b hb]; dsimp only [spos, tot, minL]; exact Nat.le_refl _),
        m7Slice_nil _ (Nat.le_refl 1)]

/-! ## 6. Post-Copy Tail & Main `full_sort_tmp_wp` -/

private abbrev s7SortTailExpr {Val : Ty → Type} {Cont : List Ty → Type}
    (n64 mv64 pTmp pLvl pWsort : Val i64) (minL maxL : Val i32) : Expr Val Cont [] :=
  .let_ (Op.mk (.zext 32 64) (Arg.var maxL, ())) fun t1 =>
  .let_ (Op.mk (.zext 32 64) (Arg.var minL, ())) fun t2 =>
  .let_ (Op.mk (.sub i64) (Arg.var t1.1, Arg.var t2.1, ())) fun t3 =>
  .let_ (Op.mk (.add i64) (Arg.var t3.1, Arg.imm 1, ())) fun sp =>
  .let_ (Op.mk (.sub i64) (Arg.var n64, Arg.imm 1, ())) fun nn =>
  .let_ (Op.mk (.cmp .eq i64 .bool rfl) (Arg.var sp.1, Arg.imm 1, ())) fun c1 =>
  .jnz (Arg.var c1.1) (.ret ())
    (.group (sig := [[]]) (fun _ =>
      .cons (fun _ => s7SortMergeExpr n64 nn.1 pTmp pLvl pWsort) .nil)
      (fun J =>
        .let_ (Op.mk (.cmp .ule i64 .bool rfl) (Arg.var sp.1, Arg.var mv64, ())) fun c2 =>
        .jnz (Arg.var c2.1)
          (.let_ (Op.mk (.sext 32 64) (Arg.imm 2, ())) fun t4 =>
          .let_ (Op.mk (.shl i64) (Arg.var nn.1, Arg.var t4.1, ())) fun t5 =>
          .let_ (Op.mk (.cmp .ule i64 .bool rfl) (Arg.var sp.1, Arg.var t5.1, ())) fun c3 =>
          .jnz (Arg.var c3.1)
            (s7SortZeroExpr mv64 sp.1 pWsort
              (s7SortHistExpr mv64 n64 pLvl pWsort minL
                (s7SortPrefExpr mv64 sp.1 pWsort
                  (s7SortScatExpr mv64 n64 pTmp pLvl pWsort minL (.ret ())))))
            (.jump J.1 ()))
          (.jump J.1 ())))

private theorem s7_ws_eq_tmp {s : FullState} {ws_k : List (BitVec 32)} {mv : Nat}
    (htmp_len : s.core.tmp.length = mv) (hlen_wk : ws_k.length = 2 * mv)
    (htl : s.core.tmp_len ≤ mv)
    (hsl_wk : m7Slice ws_k 1 s.core.tmp_len = m7Slice s.core.tmp 1 s.core.tmp_len)
    {p : Nat} (hp1 : 1 ≤ p) (hp2 : p < s.core.tmp_len) : ws_k[p]? = s.core.tmp[p]? := by
  have hw : p < ws_k.length := by rw [hlen_wk]; omega
  have ht : p < s.core.tmp.length := by rw [htmp_len]; omega
  rw [List.getElem?_eq_getElem (l := ws_k) (i := p) hw,
    List.getElem?_eq_getElem (l := s.core.tmp) (i := p) ht]
  congr 1
  have hs := congrArg (fun l => l[p - 1]?) hsl_wk
  rw [List.getElem?_eq_getElem (by rw [m7Slice_length, hlen_wk]; omega),
    List.getElem?_eq_getElem (by rw [m7Slice_length, htmp_len]; omega),
    m7Slice_getElem, m7Slice_getElem] at hs
  simp only [Option.some.injEq] at hs
  simpa [show 1 + (p - 1) = p by omega] using hs

private theorem s7_sort_tail_wp {Γ : Env} {c : FullCfg} {s st_c : FullState}
    {ws_k : List (BitVec 32)} {R : Mem 64 → Prop} {m_c : Mem 64} {Q : Post []} {X : XPost}
    {minL maxL : BitVec 32}
    (hlenOk : FullState.LengthsOk c s) (htl : s.core.tmp_len ≤ c.max_vars)
    (hbd : ∀ k, 1 ≤ k → k < s.core.tmp_len →
      (s.core.tmp[k]?.getD 0#32).toNat < 2 * c.max_vars)
    (hQ : ∀ (res : Tup Val []) (s' : FullState) m', s'.LengthsOk c →
      Spec.SortTmpPost s s' → (FullMem c s' ⋆ R) m' → Q res m')
    (hNgt32 : 32 < s.core.tmp_len) (hmn_mx : minL.toNat ≤ maxL.toNat)
    (hst_c : st_c.core = { s.core with tmp := s.core.tmp })
    (hst_s : st_c.scratch = { s.scratch with wsort := ws_k })
    (hlen_wk : ws_k.length = 2 * c.max_vars)
    (hsl_wk : m7Slice ws_k 1 s.core.tmp_len = m7Slice s.core.tmp 1 s.core.tmp_len)
    (hminmax_k : ∀ p, 1 ≤ p → p < s.core.tmp_len →
      minL.toNat ≤ (s.core.lvl[(ws_k[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
      (s.core.lvl[(ws_k[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ maxL.toNat)
    (hm_c : (FullMem c st_c ⋆ R) m_c) :
    wp Γ Q X (s7SortTailExpr (BitVec.ofNat 64 s.core.tmp_len) (BitVec.ofNat 64 c.max_vars)
      c.pTmp c.pLevel c.pWsort minL maxL) m_c := by
  have htmp_len : s.core.tmp.length = c.max_vars := hlenOk.core_ok.tmp_len_arr
  have hlvl_len : s.core.lvl.length = c.max_vars := hlenOk.core_ok.lvl_len
  have hmv : c.max_vars < 2 ^ 32 := by have := c.hmaxv; unfold Ref.dimacsBound at this; omega
  let span := maxL.toNat - minL.toNat + 1
  have hspan_bv :
      (BitVec.setWidth 64 maxL - BitVec.setWidth 64 minL) + (1 : BitVec 64) =
      BitVec.ofNat 64 span := by
    have := maxL.isLt; dsimp [span]; c0_bound
  have hN1_bv : BitVec.ofNat 64 s.core.tmp_len - (1 : BitVec 64) =
      BitVec.ofNat 64 (s.core.tmp_len - 1) := by c0_bound
  have hws_tmp : ∀ p, 1 ≤ p → p < s.core.tmp_len → ws_k[p]? = s.core.tmp[p]? :=
    fun p hp1 hp2 => s7_ws_eq_tmp htmp_len hlen_wk htl hsl_wk hp1 hp2
  dsimp only [s7SortTailExpr]
  c0_hsplit
  · have hsp1 : span = 1 := by
      rw [hspan_bv] at hc; have := maxL.isLt; dsimp [span] at *; c0_grind
    c0_hsteps!
    refine s7_finish_spec hlenOk htl hst_c hst_s htmp_len hlen_wk (fun h => by omega)
      (List.Perm.refl _) (fun _ => rfl) (fun i j hi hij hj => ?_) hm_c hQ
    have hmi := hminmax_k i hi (by omega)
    have hmj := hminmax_k j (by omega) hj
    rw [hws_tmp i hi (by omega)] at hmi
    rw [hws_tmp j (by omega) hj] at hmj
    dsimp [span] at hsp1; omega
  · refine wp_join_group (fun _ m' => m' = m_c) ?_ ?_
    · intro J _ m' hm'
      rw [hm', Blocks.get_here, hN1_bv]
      exact s7_sort_merge_wp htmp_len hlvl_len htl (by omega) hbd hlen_wk hst_c hst_s hm_c
        fun st' tmp' ws' m' hc' hs' hlen_t' hlen_w' hperm' h0' hsort' hm' =>
          s7_finish_spec hlenOk htl hc' hs' hlen_t' hlen_w' (fun h => by omega) hperm'
            (fun _ => h0') hsort' hm' hQ
    · intro J hExit
      c0_hsplit
      · have hspan_le_mv : span ≤ c.max_vars := by
          have : maxL.toNat < 2 ^ 32 := maxL.isLt
          have : minL.toNat < 2 ^ 32 := minL.isLt
          have hmod : (2 ^ 64 - minL.toNat + maxL.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 =
              span := by
            change (2 ^ 64 - minL.toNat + maxL.toNat + 1) % 2 ^ 64 = _
            dsimp [span]
            have h1 : 2 ^ 64 - minL.toNat + maxL.toNat + 1 =
                2 ^ 64 + (maxL.toNat - minL.toNat + 1) := by omega
            rw [h1, Nat.add_mod_left]
            exact Nat.mod_eq_of_lt (by omega)
          rw [hmod] at hc
          dsimp [span] at *; omega
        c0_hsplit
        · rw [hspan_bv]
          change wp Γ Q X (s7SortZeroExpr (BitVec.ofNat 64 c.max_vars)
            (BitVec.ofNat 64 span) c.pWsort
            (s7SortHistExpr (BitVec.ofNat 64 c.max_vars)
              (BitVec.ofNat 64 s.core.tmp_len) c.pLevel c.pWsort minL
              (s7SortPrefExpr (BitVec.ofNat 64 c.max_vars) (BitVec.ofNat 64 span)
                c.pWsort
                (s7SortScatExpr (BitVec.ofNat 64 c.max_vars)
                  (BitVec.ofNat 64 s.core.tmp_len) c.pTmp c.pLevel c.pWsort minL
                  (.ret ()))))) m_c
          have hminmax_ws : ∀ p, 1 ≤ p → p < s.core.tmp_len →
              minL.toNat ≤ (s.core.lvl[(ws_k[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
              (s.core.lvl[(ws_k[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
                minL.toNat + span := fun p hp1 hp2 => by
            have h := hminmax_k p hp1 hp2; exact ⟨h.1, by dsimp [span]; omega⟩
          have hbd_ws : ∀ p, 1 ≤ p → p < s.core.tmp_len →
              (ws_k[p]?.getD 0#32).toNat < 2 * c.max_vars := fun p hp1 hp2 => by
            rw [hws_tmp p hp1 hp2]; exact hbd p hp1 hp2
          let tot := m7BktCnt s.core.lvl minL.toNat (m7Slice ws_k 1 s.core.tmp_len)
          have hspos_N : m7PrefixStart tot span = s.core.tmp_len := by
            rw [m7PrefixStart_eq_sum]
            have hsum := m7BktCnt_sum_range s.core.lvl minL.toNat
              (m7Slice ws_k 1 s.core.tmp_len) span (fun y hy => by
                rw [List.mem_iff_getElem] at hy
                obtain ⟨idx, hidx, rfl⟩ := hy
                rw [m7Slice_length, hlen_wk] at hidx
                rw [m7Slice_getElem, m7Bkt_eq]
                have hmm := hminmax_ws (1 + idx) (by omega) (by omega)
                rw [List.getElem?_eq_getElem (l := ws_k) (i := 1 + idx)
                  (by rw [hlen_wk]; omega), Option.getD_some] at hmm
                omega)
            rw [m7Slice_length, hlen_wk] at hsum; dsimp only [tot]; rw [hsum]; omega
          have hspos_le : ∀ b ≤ span, m7PrefixStart tot b ≤ s.core.tmp_len :=
            fun b hb => hspos_N ▸ m7PrefixStart_mono hb
          refine s7_sort_zero_wp hspan_le_mv hst_c hst_s hlen_wk hm_c ?_
          intro st1 ws1 m1 hst1_c hst1_s hlen_ws1 hpre1 hz1 hm1
          have hsl1 : m7Slice ws1 1 s.core.tmp_len = m7Slice s.core.tmp 1 s.core.tmp_len :=
            (s7Slice_congr_lt (by omega) (by rw [hlen_ws1]; omega)
              (by rw [hlen_wk]; omega) (fun q hq => hpre1 q (by omega))).trans hsl_wk
          have hminmax1 : ∀ p, 1 ≤ p → p < s.core.tmp_len →
              minL.toNat ≤ (s.core.lvl[(ws1[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
              (s.core.lvl[(ws1[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
                minL.toNat + span := fun p hp1 hp2 => by
            rw [show ws1[p]? = ws_k[p]? from hpre1 p (by omega)]; exact hminmax_ws p hp1 hp2
          have hbd1' : ∀ p, 1 ≤ p → p < s.core.tmp_len →
              (ws1[p]?.getD 0#32).toNat < 2 * c.max_vars := fun p hp1 hp2 => by
            rw [show ws1[p]? = ws_k[p]? from hpre1 p (by omega)]; exact hbd_ws p hp1 hp2
          refine s7_sort_hist_wp hlvl_len htl (by omega) hlen_ws1 hspan_le_mv
            hminmax1 hbd1' hz1 hst1_c hst1_s hm1 ?_
          intro st2 ws2 m2 hst2_c hst2_s hlen_ws2 hpre2 hcnt2 hm2
          have hpre20 : ∀ q < c.max_vars, ws2[q]? = ws_k[q]? :=
            fun q hq => (hpre2 q hq).trans (hpre1 q hq)
          have hsl1_k : m7Slice ws1 1 s.core.tmp_len = m7Slice ws_k 1 s.core.tmp_len :=
            s7Slice_congr_lt (by omega) (by rw [hlen_ws1]; omega)
              (by rw [hlen_wk]; omega) (fun q hq => hpre1 q (by omega))
          refine s7_sort_pref_wp hlen_ws2 hspan_le_mv (by rw [hspos_N]; exact htl)
            (fun b hb => by rw [hcnt2 b hb, hsl1_k]) hst2_c hst2_s hm2 ?_
          intro st3 ws3 m3 hst3_c hst3_s hlen_ws3 hpre3 hpref3 hm3
          have hpre3k : ∀ q < c.max_vars, ws3[q]? = ws_k[q]? :=
            fun q hq => (hpre3 q hq).trans (hpre20 q hq)
          have hsl3 : m7Slice ws3 1 s.core.tmp_len = m7Slice ws_k 1 s.core.tmp_len :=
            s7Slice_congr_lt (by omega) (by rw [hlen_ws3]; omega)
              (by rw [hlen_wk]; omega) (fun q hq => hpre3k q (by omega))
          have hminmax3 : ∀ p, 1 ≤ p → p < s.core.tmp_len →
              minL.toNat ≤ (s.core.lvl[(ws3[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
              (s.core.lvl[(ws3[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
                minL.toNat + span := fun p hp1 hp2 => by
            rw [show ws3[p]? = ws_k[p]? from hpre3k p (by omega)]; exact hminmax_ws p hp1 hp2
          have hbd3 : ∀ p, 1 ≤ p → p < s.core.tmp_len →
              (ws3[p]?.getD 0#32).toNat < 2 * c.max_vars := fun p hp1 hp2 => by
            rw [show ws3[p]? = ws_k[p]? from hpre3k p (by omega)]; exact hbd_ws p hp1 hp2
          refine s7_sort_scat_wp htmp_len hlvl_len htl (by omega) hlen_ws3 hspan_le_mv
            (hsl3.trans hsl_wk) hminmax3 hbd3 (by rw [hsl3]; exact hspos_N)
            (fun b hb => by rw [hsl3]; exact hspos_le b hb)
            (fun b hb => by rw [hsl3]; exact hpref3 b hb) hst3_c hst3_s hm3 ?_
          intro st4 tmp4 ws4 m4 hst4_c hst4_s hlen_t4 hlen_ws4 hperm4 h0_4 _ hlvl4 hm4
          exact s7_finish_spec hlenOk htl hst4_c hst4_s hlen_t4 hlen_ws4
            (fun h => by omega) hperm4 (fun _ => h0_4) hlvl4 hm4 hQ
        · c0_hsteps!; exact hExit () m_c rfl
      · c0_hsteps!; exact hExit () m_c rfl

/-- `Func.wp` soundness of `full_sort_tmp` (`≤ 32` insertion sort, `> 32` counting sort in
`wsort`, bottom-up merge-sort fallback) against `Spec.sortTmpSpec`. -/
theorem full_sort_tmp_wp (Γ : Env) :
    ∀ (args : Tup Val [i64]) (m : Mem 64) (Q : Post []) (X : XPost),
      Spec.sortTmpSpec args m Q X →
      Func.wp Γ full_sort_tmp_body args m Q X := by
  intro args m Q X hspec
  rcases args with ⟨p_hd, ⟨⟩⟩
  obtain ⟨c, s, _, R, rfl, hlenOk, ⟨htl, hbd⟩, hm, hQ⟩ := FullContract.elim hspec
  dsimp only [Func.wp, full_sort_tmp_body]
  have htmp_len : s.core.tmp.length = c.max_vars := hlenOk.core_ok.tmp_len_arr
  have hlvl_len : s.core.lvl.length = c.max_vars := hlenOk.core_ok.lvl_len
  have hws_len : s.scratch.wsort.length = 2 * c.max_vars := hlenOk.scratch_ok.wsort_len
  have hmv : c.max_vars < 2 ^ 32 := by have := c.hmaxv; unfold Ref.dimacsBound at this; omega
  c0_hsplit
  · have hNle2 : s.core.tmp_len ≤ 2 := by c0_grind
    c0_hsteps!
    obtain ⟨st0, hc0, hs0, hm0⟩ := m7_wrap_state hm
    exact s7_finish_spec hlenOk htl hc0 hs0 htmp_len hws_len (fun _ => rfl) (List.Perm.refl _)
      (fun _ => rfl) (fun i j hi hij hj => by
        have : i = 1 := by omega
        have : j = 1 := by omega
        subst_vars; exact Nat.le_refl _) hm0 hQ
  · have hNgt2 : 2 < s.core.tmp_len := by c0_grind
    c0_hsplit
    · have : c.max_vars < s.core.tmp_len := by c0_grind
      omega
    · c0_hsplit
      · obtain ⟨st0, hc0, hs0, hm0⟩ := m7_wrap_state hm
        change wp Γ Q X (s7SortInsExpr (BitVec.ofNat 64 s.core.tmp_len) c.pTmp c.pLevel) m
        exact s7_sort_ins_wp htmp_len hlvl_len htl (by omega) hbd hc0 hs0 hm0
          fun st' tmp' m' hc' hs' hlen' hperm' h0' hsort' hm' =>
            s7_finish_spec hlenOk htl hc' hs' hlen' hws_len (fun _ => rfl) hperm'
              (fun _ => h0') hsort' hm' hQ
      · have hNgt32 : 32 < s.core.tmp_len := by c0_grind
        have h1t : 1 < s.core.tmp.length := by rw [htmp_len]; omega
        have h1w : 1 < s.scratch.wsort.length := by rw [hws_len]; omega
        have hbd1 : (s.core.tmp[1]'h1t).toNat < 2 * c.max_vars := by
          have h := hbd 1 (Nat.le_refl 1) (by omega)
          rwa [List.getElem?_eq_getElem h1t, Option.getD_some] at h
        let v284 := s.core.tmp[1]'h1t
        have hv284_bd : v284.toNat < 2 * c.max_vars := hbd1
        have hv284_lvl : v284.toNat / 2 < s.core.lvl.length := by rw [hlvl_len]; omega
        let v293 := s.core.lvl[v284.toNat / 2]'hv284_lvl
        have hs1_idx : (BitVec.signExtend 64 1#32).toNat < s.core.tmp.length := by
          change 1 < _; exact h1t
        have hs1_widx : (BitVec.signExtend 64 1#32).toNat < s.scratch.wsort.length := by
          change 1 < _; exact h1w
        have h1t_lvl : ((s.core.tmp[1]'h1t).setWidth 64 >>>
            ((BitVec.signExtend 64 1#32).toNat % 64)).toNat < s.core.lvl.length := by
          rw [s7_lshr1]; exact hv284_lvl
        c0_hsteps_nogrp
        let InvCopy : Nat → Tup Val [i32, i32, i64] → Mem 64 → Prop := fun meas xs m_c =>
          ∃ k st ws_k, xs.1.toNat ≤ xs.2.1.toNat ∧
            xs.2.2.1 = BitVec.ofNat 64 k ∧ 2 ≤ k ∧ k ≤ s.core.tmp_len ∧
            meas = s.core.tmp_len - k ∧
            st.core = { s.core with tmp := s.core.tmp } ∧
            st.scratch = { s.scratch with wsort := ws_k } ∧
            ws_k.length = 2 * c.max_vars ∧
            m7Slice ws_k 1 k = m7Slice s.core.tmp 1 k ∧
            (∀ p, 1 ≤ p → p < k →
              xs.1.toNat ≤ (s.core.lvl[(ws_k[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
              (s.core.lvl[(ws_k[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ xs.2.1.toNat) ∧
            (FullMem c st ⋆ R) m_c
        refine wp_loop_group InvCopy ?_ ?_
        · intro J294 meas xs m_c hIH ⟨k, st_c, ws_k, hmn_mx, hxs3, hk2, hkN, hmeas, hst_c,
            hst_s, hlen_wk, hsl_wk, hminmax_k, hm_c⟩
          rcases xs with ⟨mn_bv, mx_bv, k_bv, ⟨⟩⟩; dsimp only at hxs3; subst hxs3
          rw [Blocks.get_here]; c0_hsplit
          · have hk_lt : k < s.core.tmp_len := by c0_grind
            have hk_i : (BitVec.ofNat 64 k).toNat = k := by c0_bound
            have hkt : k < s.core.tmp.length := by rw [htmp_len]; omega
            have hkt_st : (BitVec.ofNat 64 k).toNat < st_c.core.tmp.length := by
              rw [m7_core_tmp_eq hst_c, hk_i]; exact hkt
            have hgk : st_c.core.tmp[(BitVec.ofNat 64 k).toNat]'hkt_st = s.core.tmp[k]'hkt := by
              simpa only [hk_i] using s7_get_tmp hst_c (i := k) hkt
            have hbdk : (s.core.tmp[k]'hkt).toNat < 2 * c.max_vars := by
              have h := hbd k (by omega) hk_lt
              rwa [List.getElem?_eq_getElem hkt, Option.getD_some] at h
            have hkw_st : (BitVec.ofNat 64 k).toNat < st_c.scratch.wsort.length := by
              rw [m7_scr_ws_eq hst_s, hlen_wk, hk_i]; omega
            let v300 := s.core.tmp[k]'hkt
            have hv300_bd : v300.toNat < 2 * c.max_vars := hbdk
            have hv300_lvl : v300.toNat / 2 < s.core.lvl.length := by rw [hlvl_len]; omega
            let v308 := s.core.lvl[v300.toNat / 2]'hv300_lvl
            have hklvl_st : ((st_c.core.tmp[(BitVec.ofNat 64 k).toNat]'hkt_st).setWidth 64 >>>
                ((BitVec.signExtend 64 1#32).toNat % 64)).toNat < st_c.core.lvl.length := by
              rw [hgk, s7_lshr1, m7_core_lvl_eq hst_c]; exact hv300_lvl
            have hgk_hc : st_c.core.tmp[k % 2 ^ 64]'(by
                have h : k % 2 ^ 64 = k := by c0_bound
                rw [h, m7_core_tmp_eq hst_c]; exact hkt) = v300 := by
              have h : k % 2 ^ 64 = k := by c0_bound
              simpa only [h] using s7_get_tmp hst_c (i := k) hkt
            have hglvl_hc : st_c.core.lvl[(BitVec.setWidth 64 (st_c.core.tmp[k % 2 ^ 64]'(by
                have h : k % 2 ^ 64 = k := by c0_bound
                rw [h, m7_core_tmp_eq hst_c]; exact hkt)) >>> (1 : Nat)).toNat]'(by
                rw [hgk_hc, s7_lshr1_one, m7_core_lvl_eq hst_c]; exact hv300_lvl) = v308 :=
              s7_get_lvl_of hst_c _ (by rw [hgk_hc, s7_lshr1_one]) hv300_lvl
            have hglvl : st_c.core.lvl[(BitVec.setWidth 64
                (st_c.core.tmp[(BitVec.ofNat 64 k).toNat]'hkt_st) >>> (1 : Nat)).toNat]'(by
                rw [hgk, s7_lshr1_one, m7_core_lvl_eq hst_c]; exact hv300_lvl) = v308 :=
              s7_get_lvl_of hst_c _ (by rw [hgk, s7_lshr1_one]) hv300_lvl
            c0_hsteps_nogrp
            let scr1 := st_c.scratch
            let ws1 := scr1.wsort.set (BitVec.ofNat 64 k).toNat
              (st_c.core.tmp[(BitVec.ofNat 64 k).toNat]'hkt_st)
            let st_c' : FullState := { core := st_c.core, scratch := { scr1 with wsort := ws1 } }
            have hst_c' : st_c'.core = { s.core with tmp := s.core.tmp } := hst_c
            have hst_s' : st_c'.scratch = { s.scratch with wsort := ws_k.set k v300 } := by
              dsimp only [st_c', scr1, ws1]; rw [hgk, hk_i]; exact s7_st_upd_wsort hst_s
            let Pj309 : Tup Val [i32] → Mem 64 → Prop := fun mn m309 =>
              (FullMem c st_c' ⋆ R) m309 ∧ mn.1.toNat ≤ v308.toNat ∧
              (∀ p, 1 ≤ p → p < k →
                mn.1.toNat ≤ (s.core.lvl[(ws_k[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
              mn.1.toNat ≤ mx_bv.toNat
            refine wp_join_group Pj309 ?_ ?_
            · intro J309 mn m309 ⟨hm309, hmn_lx, hmn_pre, hmn_mx'⟩
              rw [Blocks.get_here]
              let Pj311 : Tup Val [i32] → Mem 64 → Prop := fun mx m311 =>
                (FullMem c st_c' ⋆ R) m311 ∧ v308.toNat ≤ mx.1.toNat ∧
                (∀ p, 1 ≤ p → p < k →
                  (s.core.lvl[(ws_k[p]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ mx.1.toNat) ∧
                mn.1.toNat ≤ mx.1.toNat
              refine wp_join_group Pj311 ?_ ?_
              · intro J311 mx m311 ⟨hm311, hlx_mx, hmx_pre, hmn_mx''⟩
                rw [Blocks.get_here]; c0_hsteps!
                have hstep := m7_copy_step_inv htmp_len hlvl_len hlen_wk hk2 hk_lt htl
                  hsl_wk (by rw [List.getElem?_eq_getElem hkt, Option.getD_some]; exact hbdk)
                  rfl hmn_lx hlx_mx hmn_pre hmx_pre
                have hk1_bv : BitVec.ofNat 64 k + (1 : BitVec 64) = BitVec.ofNat 64 (k + 1) := by
                  c0_bound
                rw [hk1_bv]
                exact hIH (s.core.tmp_len - (k + 1)) _ _ (by omega)
                  ⟨k + 1, st_c', ws_k.set k v300, hmn_mx'', rfl, by omega, by omega, rfl,
                    hst_c', hst_s', hstep.1, hstep.2.1, hstep.2.2, hm311⟩
              · intro J311 hExit311; c0_hsplit
                · have hlt_mx : mx_bv.toNat < v308.toNat := by
                    rw [show st_c.core.lvl[(BitVec.setWidth 64 st_c.core.tmp[k % 2 ^ 64] >>>
                      (1 : Nat)).toNat]'_ = v308 from hglvl_hc] at hc
                    c0_grind
                  c0_hsteps!
                  first | rw [hglvl] | rw [hglvl_hc]
                  exact hExit311 (v308, ()) _ ⟨hm309, Nat.le_refl _, fun p hp1 hp2 =>
                    Nat.le_trans (hminmax_k p hp1 hp2).2 (Nat.le_of_lt hlt_mx),
                    Nat.le_trans hmn_mx' (Nat.le_of_lt hlt_mx)⟩
                · have hle_mx' : v308.toNat ≤ mx_bv.toNat := by
                    first | rw [hglvl] at hc | rw [hglvl_hc] at hc
                    c0_grind
                  c0_hsteps!
                  exact hExit311 (mx_bv, ()) _ ⟨hm309, hle_mx', fun p hp1 hp2 =>
                    (hminmax_k p hp1 hp2).2, hmn_mx'⟩
            · intro J309 hExit309; c0_hsplit
              · have hlt_mn' : v308.toNat < mn_bv.toNat := by
                  first | rw [hglvl] at hc | rw [hglvl_hc] at hc
                  c0_grind
                c0_hsteps!
                first | rw [hglvl] | rw [hglvl_hc]
                exact hExit309 (v308, ()) _ ⟨by assumption, Nat.le_refl _, fun p hp1 hp2 =>
                  Nat.le_trans (Nat.le_of_lt hlt_mn') (hminmax_k p hp1 hp2).1,
                  Nat.le_trans (Nat.le_of_lt hlt_mn') hmn_mx⟩
              · have hge_mn' : mn_bv.toNat ≤ v308.toNat := by
                  first | rw [hglvl] at hc | rw [hglvl_hc] at hc
                  c0_grind
                c0_hsteps!
                exact hExit309 (mn_bv, ()) _ ⟨by assumption, hge_mn', fun p hp1 hp2 =>
                  (hminmax_k p hp1 hp2).1, hmn_mx⟩
          · have hk_ge : s.core.tmp_len ≤ k := by c0_grind
            have hk_eq : k = s.core.tmp_len := by omega
            subst hk_eq
            exact s7_sort_tail_wp hlenOk htl hbd hQ hNgt32 hmn_mx hst_c hst_s hlen_wk hsl_wk
              hminmax_k hm_c
        · intro J295 hExit295
          have hinv0 := m7_copy_init_inv htmp_len hlvl_len hws_len (by omega) htl
            (hbd 1 (Nat.le_refl 1) (by omega))
          c0_hsteps!
          simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide : 1 < 2 ^ 64)] at hm ⊢
          rw [show ({ core := s.core, scratch := { s.scratch with
              wsort := s.scratch.wsort.set 1 s.core.tmp[1] } } : FullState
              ).core.lvl[(BitVec.setWidth 64 s.core.tmp[1] >>> (1 : Nat)).toNat]'(by
                rw [s7_lshr1_one]; exact hv284_lvl) = v293 from by simp only [s7_lshr1_one]; rfl]
          exact hExit295 (s.core.tmp_len - 2) _ _
            ⟨2, { core := s.core,
                  scratch := { s.scratch with wsort := s.scratch.wsort.set 1 v284 } },
              s.scratch.wsort.set 1 v284, Nat.le_refl _, rfl, Nat.le_refl 2, by omega, rfl,
              rfl, rfl, hinv0.1, hinv0.2.1, hinv0.2.2, hm⟩

end LeanQbe.T.Examples.Kissat.Proof.Minimize
