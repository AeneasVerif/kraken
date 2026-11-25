/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep7
public import LeanQbe.T.Examples.Kissat.FullM7AnalyzeSortProof3
import LeanQbe.T.Examples.Kissat.FullMinLemmas1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.Rules
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Step-7 `full_sort_tmp` Proof Shard 0a0: Shared Helpers & Phase Sub-ASTs

BitVec / Nat-indexed load-store helpers (adapted from `FullM7AnalyzeSortProof4`) and
`rfl`-identical phase sub-expressions of `FullFidelityStep7.full_sort_tmp_body`: `≤ 32`
level-only insertion sort, counting-sort zero / histogram / prefix / scatter loops, and the
bottom-up merge-sort fallback.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof0a

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open LeanQbe.T.Examples.Kissat.FullM7AnalyzeSort
open scoped LeanQbe.T.Examples.Kissat.Full.FullMinTactics
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.Kissat.FullFidelityStep7


/-! ## 1. BitVec, Opaque Nat-Indexed Load/Store & Finishing Helpers -/

theorem s7_ult64_true {a b : BitVec 64} (h : BitVec.ult a b = true) :
    a.toNat < b.toNat := by
  simpa [BitVec.ult] using h

theorem s7_ult64_false {a b : BitVec 64} (h : BitVec.ult a b = false) :
    b.toNat ≤ a.toNat := by
  have h1 : ¬ (a.toNat < b.toNat) := by simpa [BitVec.ult] using h
  omega

theorem s7_ule64_true {a b : BitVec 64} (h : BitVec.ule a b = true) :
    a.toNat ≤ b.toNat := by
  simpa [BitVec.ule] using h

theorem s7_ule64_false {a b : BitVec 64} (h : BitVec.ule a b = false) :
    b.toNat < a.toNat := by
  have h1 : ¬ (a.toNat ≤ b.toNat) := by simpa [BitVec.ule] using h
  omega

theorem s7_ult32_true {a b : BitVec 32} (h : BitVec.ult a b = true) :
    a.toNat < b.toNat := by
  simpa [BitVec.ult] using h

theorem s7_ult32_false {a b : BitVec 32} (h : BitVec.ult a b = false) :
    b.toNat ≤ a.toNat := by
  have h1 : ¬ (a.toNat < b.toNat) := by simpa [BitVec.ult] using h
  omega

theorem s7_ule32_true {a b : BitVec 32} (h : BitVec.ule a b = true) :
    a.toNat ≤ b.toNat := by
  simpa [BitVec.ule] using h

theorem s7_ule32_false {a b : BitVec 32} (h : BitVec.ule a b = false) :
    b.toNat < a.toNat := by
  have h1 : ¬ (a.toNat ≤ b.toNat) := by simpa [BitVec.ule] using h
  omega

theorem s7_var_idx64 (v : BitVec 32) :
    BitVec.setWidth 64 v >>> ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64) =
      BitVec.ofNat 64 (v.toNat / 2) := by
  apply BitVec.eq_of_toNat_eq
  have hv64 : v.toNat / 2 < 2 ^ 64 := by have := v.isLt; omega
  rw [m7_ushr1_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv64]

theorem s7_sub_bv64_ofNat {a b : Nat} (hba : b ≤ a) (ha : a < 2 ^ 64)
    (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [m7_bv64_sub (by rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]; exact hba),
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (by omega)]

theorem s7_add_bv64_ofNat {a b : Nat} (hab : a + b < 2 ^ 64) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  rw [m7_bv64_add (by rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; exact hab),
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hab]

theorem s7_add1_bv64 {a : Nat} (ha : a + 1 < 2 ^ 64) :
    BitVec.ofNat 64 a + (1 : BitVec 64) = BitVec.ofNat 64 (a + 1) := by
  simpa using s7_add_bv64_ofNat ha

theorem s7_sub1_bv64 {a : Nat} (h1 : 1 ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - (1 : BitVec 64) = BitVec.ofNat 64 (a - 1) := by
  simpa using s7_sub_bv64_ofNat h1 ha (by decide)

theorem s7_sub_zext64_of_le {v minL : BitVec 32} (hle : minL.toNat ≤ v.toNat) :
    BitVec.setWidth 64 v - BitVec.setWidth 64 minL =
      BitVec.ofNat 64 (v.toNat - minL.toNat) := by
  have hv64 : v.toNat < 2 ^ 64 := Nat.lt_trans v.isLt (by decide)
  have hm64 : minL.toNat < 2 ^ 64 := Nat.lt_trans minL.isLt (by decide)
  have h1 : BitVec.setWidth 64 v = BitVec.ofNat 64 v.toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv64]
  have h2 : BitVec.setWidth 64 minL = BitVec.ofNat 64 minL.toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm64]
  rw [h1, h2]
  exact s7_sub_bv64_ofNat hle hv64 hm64

theorem s7_trunc_add1_32 {v : BitVec 32} (hv : v.toNat + 1 < 2 ^ 32) :
    BitVec.setWidth 32 (BitVec.setWidth 64 v + (1 : BitVec 64)) =
      BitVec.ofNat 32 (v.toNat + 1) := by
  apply BitVec.eq_of_toNat_eq
  have hv64 : (BitVec.setWidth 64 v + (1 : BitVec 64)).toNat = v.toNat + 1 := by
    have hvlt : (BitVec.setWidth 64 v).toNat + (1 : BitVec 64).toNat < 2 ^ 64 := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans v.isLt (by decide))]
      change v.toNat + 1 < 2 ^ 64; omega
    rw [m7_bv64_add hvlt, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_trans v.isLt (by decide))]
    rfl
  rw [m7_bv32_trunc64 (by rw [hv64]; exact hv), hv64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]

theorem s7_trunc_zext64 {r : BitVec 64} (hr : r.toNat < 2 ^ 32) :
    BitVec.setWidth 32 r = BitVec.ofNat 32 r.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [m7_bv32_trunc64 hr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]

theorem s7_add_bv32_ofNat {v : BitVec 32} (hv : v.toNat + 1 < 2 ^ 32) :
    v + (1 : BitVec 32) = BitVec.ofNat 32 (v.toNat + 1) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : v + (1 : BitVec 32) = v + 1#32 := rfl
  rw [h1, m7_bv32_add1_lt hv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]

theorem s7_load_tmp_nat {c : FullCfg} {st s : FullState} {tmp_cur : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {i : Nat}
    (hc : st.core = { s.core with tmp := tmp_cur })
    (hi : i < tmp_cur.length) (hi64 : i < 2 ^ 64) (hm : (FullMem c st ⋆ R) m) :
    loadVal m i32 (c.pTmp + BitVec.ofNat 64 i * 4) = some (tmp_cur[i]'hi) := by
  have hi' : (BitVec.ofNat 64 i).toNat < tmp_cur.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64]; exact hi
  have hld := m7_load_tmp_of hc hi' hm
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64] using hld

theorem s7_load_lvl_nat {c : FullCfg} {st s : FullState} {tmp_cur : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {i : Nat}
    (hc : st.core = { s.core with tmp := tmp_cur })
    (hi : i < s.core.lvl.length) (hi64 : i < 2 ^ 64) (hm : (FullMem c st ⋆ R) m) :
    loadVal m i32 (c.pLevel + BitVec.ofNat 64 i * 4) = some (s.core.lvl[i]'hi) := by
  have hi' : (BitVec.ofNat 64 i).toNat < s.core.lvl.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64]; exact hi
  have hld := m7_load_lvl_of hc hi' hm
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64] using hld

theorem s7_load_tpos_nat {c : FullCfg} {st s : FullState} {tmp_cur : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} {i : Nat}
    (hc : st.core = { s.core with tmp := tmp_cur })
    (hi : i < s.core.trail_pos.length) (hi64 : i < 2 ^ 64) (hm : (FullMem c st ⋆ R) m) :
    loadVal m i32 (c.pTrailPos + BitVec.ofNat 64 i * 4) = some (s.core.trail_pos[i]'hi) := by
  have hi' : (BitVec.ofNat 64 i).toNat < s.core.trail_pos.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64]; exact hi
  have hld := m7_load_tpos_of hc hi' hm
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64] using hld

theorem s7_load_wsort_nat {c : FullCfg} {st s : FullState}
    {ws_cur : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {i : Nat}
    (hs : st.scratch = { s.scratch with wsort := ws_cur })
    (hi : i < ws_cur.length) (hi64 : i < 2 ^ 64) (hm : (FullMem c st ⋆ R) m) :
    loadVal m i32 (c.pWsort + BitVec.ofNat 64 i * 4) = some (ws_cur[i]'hi) := by
  have hi' : (BitVec.ofNat 64 i).toNat < ws_cur.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64]; exact hi
  have hld := m7_load_wsort_of hs hi' hm
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64] using hld

theorem s7_store_tmp_nat {c : FullCfg} {st s : FullState} {tmp_cur : List (BitVec 32)}
    {sc0 : FullScratch} {R : Mem 64 → Prop} {m : Mem 64} {i : Nat} (v : BitVec 32)
    (hc : st.core = { s.core with tmp := tmp_cur }) (hs : st.scratch = sc0)
    (hi : i < tmp_cur.length) (hi64 : i < 2 ^ 64) (hm : (FullMem c st ⋆ R) m) :
    ∃ st' : FullState,
      st'.core = { s.core with tmp := tmp_cur.set i v } ∧
      st'.scratch = sc0 ∧
      storeOk m i32 (c.pTmp + BitVec.ofNat 64 i * 4) ∧
      (FullMem c st' ⋆ R) (storeMem m i32 (c.pTmp + BitVec.ofNat 64 i * 4) v) := by
  have hi' : (BitVec.ofNat 64 i).toNat < tmp_cur.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64]; exact hi
  obtain ⟨st', hc', hs', hok, hm'⟩ := m7_store_tmp_upd v hc hs hi' hm
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64] at hc'
  exact ⟨st', hc', hs', hok, hm'⟩

theorem s7_store_wsort_nat {c : FullCfg} {st s : FullState}
    {tmp_cur ws_cur : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    {i : Nat} (v : BitVec 32)
    (hc : st.core = { s.core with tmp := tmp_cur })
    (hs : st.scratch = { s.scratch with wsort := ws_cur })
    (hi : i < ws_cur.length) (hi64 : i < 2 ^ 64) (hm : (FullMem c st ⋆ R) m) :
    ∃ st' : FullState,
      st'.core = { s.core with tmp := tmp_cur } ∧
      st'.scratch = { s.scratch with wsort := ws_cur.set i v } ∧
      storeOk m i32 (c.pWsort + BitVec.ofNat 64 i * 4) ∧
      (FullMem c st' ⋆ R) (storeMem m i32 (c.pWsort + BitVec.ofNat 64 i * 4) v) := by
  have hi' : (BitVec.ofNat 64 i).toNat < ws_cur.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64]; exact hi
  obtain ⟨st', hc', hs', hok, hm'⟩ := m7_store_wsort_upd v hc hs hi' hm
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64] at hs'
  exact ⟨st', hc', hs', hok, hm'⟩

theorem s7_state_eq {s1 s2 : FullState}
    (hc : s1.core = s2.core) (hs : s1.scratch = s2.scratch) : s1 = s2 := by
  cases s1; cases s2; simp at hc hs; subst hc; subst hs; rfl

theorem s7Slice_congr_lt {α : Type _} {xs ys : List α} {lo hi : Nat}
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

theorem s7_drop_set_offset {α : Type _} (ws : List α) {mv b : Nat} (v : α)
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


/-! ## 2. Phase Sub-AST Definitions (`rfl`-identical to `full_sort_tmp_body`) -/

/-- `tlen ≤ 32` level-only insertion sort phase of `full_sort_tmp` (Step 7). -/
abbrev s7SortInsExpr {Val : Ty → Type} {Cont : List Ty → Type}
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

/-- Bottom-up merge-sort fallback phase of `full_sort_tmp` (Step 7), with `n64 = tlen`,
`nm1 = tlen - 1` and `wsort` (`pWsort`) as merge scratch. -/
abbrev s7SortMergeExpr {Val : Ty → Type} {Cont : List Ty → Type}
    (n64 nm1 pTmp pLvl pWsort : Val i64) : Expr Val Cont [] :=
  .group (sig := [[i64]]) (fun JW =>
    .cons (fun xw =>
      .let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var xw.1, Arg.var nm1, ())) fun c1 =>
      .jnz (Arg.var c1.1)
        (.group (sig := [[i64]]) (fun JL =>
          .cons (fun xlo =>
            .let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var xlo.1, Arg.var n64, ())) fun c2 =>
            .jnz (Arg.var c2.1)
              (.group (sig := [[i64]]) (fun _ =>
                .cons (fun xmid =>
                  .group (sig := [[i64]]) (fun _ =>
                    .cons (fun xhi =>
                      .group (sig := [[i64, i64, i64]]) (fun JM =>
                        .cons (fun xm =>
                          .group (sig := [[]]) (fun _ =>
                            .cons (fun _ =>
                              .group (sig := [[i64, i64]]) (fun JT0 =>
                                .cons (fun t0 =>
                                  .let_ (Op.mk (.cmp .ult i64 .bool rfl)
                                    (Arg.var t0.1, Arg.var xmid.1, ())) fun c3 =>
                                  .jnz (Arg.var c3.1)
                                    (.let_ (Op.mk (.mul i64)
                                      (Arg.var t0.2.1, Arg.imm 4, ())) fun f1 =>
                                    .let_ (Op.mk (.add i64)
                                      (Arg.var pWsort, Arg.var f1.1, ())) fun f2 =>
                                    .let_ (Op.mk (.mul i64) (Arg.var t0.1, Arg.imm 4, ())) fun f3 =>
                                    .let_ (Op.mk (.add i64)
                                      (Arg.var pTmp, Arg.var f3.1, ())) fun f4 =>
                                    .load i32 (Arg.var f4.1) fun v0 =>
                                    .store (t := i32) (Arg.var v0) (Arg.var f2.1) (
                                      .let_ (Op.mk (.add i64)
                                        (Arg.var t0.1, Arg.imm 1, ())) fun f5 =>
                                      .let_ (Op.mk (.add i64)
                                        (Arg.var t0.2.1, Arg.imm 1, ())) fun f6 =>
                                      .jump JT0.1 (Arg.var f5.1, Arg.var f6.1, ())))
                                    (.group (sig := [[i64, i64]]) (fun JT1 =>
                                      .cons (fun t1 =>
                                        .let_ (Op.mk (.cmp .ult i64 .bool rfl)
                                          (Arg.var t1.1, Arg.var xhi.1, ())) fun c4 =>
                                        .jnz (Arg.var c4.1)
                                          (.let_ (Op.mk (.mul i64)
                                            (Arg.var t1.2.1, Arg.imm 4, ())) fun g1 =>
                                          .let_ (Op.mk (.add i64)
                                            (Arg.var pWsort, Arg.var g1.1, ())) fun g2 =>
                                          .let_ (Op.mk (.mul i64)
                                            (Arg.var t1.1, Arg.imm 4, ())) fun g3 =>
                                          .let_ (Op.mk (.add i64)
                                            (Arg.var pTmp, Arg.var g3.1, ())) fun g4 =>
                                          .load i32 (Arg.var g4.1) fun v1 =>
                                          .store (t := i32) (Arg.var v1) (Arg.var g2.1) (
                                            .let_ (Op.mk (.add i64)
                                              (Arg.var t1.1, Arg.imm 1, ())) fun g5 =>
                                            .let_ (Op.mk (.add i64)
                                              (Arg.var t1.2.1, Arg.imm 1, ())) fun g6 =>
                                            .jump JT1.1 (Arg.var g5.1, Arg.var g6.1, ())))
                                          (.group (sig := [[i64]]) (fun JC =>
                                            .cons (fun xc =>
                                              .let_ (Op.mk (.cmp .ult i64 .bool rfl)
                                                (Arg.var xc.1, Arg.var xhi.1, ())) fun c5 =>
                                              .jnz (Arg.var c5.1)
                                                (.let_ (Op.mk (.mul i64)
                                                  (Arg.var xc.1, Arg.imm 4, ())) fun h1 =>
                                                .let_ (Op.mk (.add i64)
                                                  (Arg.var pTmp, Arg.var h1.1, ())) fun h2 =>
                                                .let_ (Op.mk (.mul i64)
                                                  (Arg.var xc.1, Arg.imm 4, ())) fun h3 =>
                                                .let_ (Op.mk (.add i64)
                                                  (Arg.var pWsort, Arg.var h3.1, ())) fun h4 =>
                                                .load i32 (Arg.var h4.1) fun v2 =>
                                                .store (t := i32) (Arg.var v2) (Arg.var h2.1) (
                                                  .let_ (Op.mk (.add i64)
                                                    (Arg.var xc.1, Arg.imm 1, ())) fun h5 =>
                                                  .jump JC.1 (Arg.var h5.1, ())))
                                                (.jump JL.1 (Arg.var xhi.1, ())))
                                            .nil)
                                            (fun J => .jump J.1 (Arg.var xlo.1, ()))))
                                      .nil)
                                      (fun J => .jump J.1 (Arg.var xm.2.1, Arg.var t0.2.1, ()))))
                                .nil)
                                (fun J => .jump J.1 (Arg.var xm.1, Arg.var xm.2.2.1, ())))
                            .nil)
                            (fun JA =>
                              .let_ (Op.mk (.cmp .ult i64 .bool rfl)
                                (Arg.var xm.1, Arg.var xmid.1, ())) fun c6 =>
                              .jnz (Arg.var c6.1)
                                (.let_ (Op.mk (.cmp .ult i64 .bool rfl)
                                  (Arg.var xm.2.1, Arg.var xhi.1, ())) fun c7 =>
                                .jnz (Arg.var c7.1)
                                  (.group (sig := [[i64, i64]]) (fun _ =>
                                    .cons (fun xu =>
                                      .let_ (Op.mk (.add i64)
                                        (Arg.var xm.2.2.1, Arg.imm 1, ())) fun k1 =>
                                      .jump JM.1 (Arg.var xu.1, Arg.var xu.2.1, Arg.var k1.1, ()))
                                    .nil)
                                    (fun JU =>
                                      .let_ (Op.mk (.mul i64)
                                        (Arg.var xm.1, Arg.imm 4, ())) fun l1 =>
                                      .let_ (Op.mk (.add i64)
                                        (Arg.var pTmp, Arg.var l1.1, ())) fun l2 =>
                                      .load i32 (Arg.var l2.1) fun va =>
                                      .let_ (Op.mk (.zext 32 64) (Arg.var va, ())) fun l3 =>
                                      .let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun l4 =>
                                      .let_ (Op.mk (.lshr i64)
                                        (Arg.var l3.1, Arg.var l4.1, ())) fun l5 =>
                                      .let_ (Op.mk (.mul i64)
                                        (Arg.var l5.1, Arg.imm 4, ())) fun l6 =>
                                      .let_ (Op.mk (.add i64)
                                        (Arg.var pLvl, Arg.var l6.1, ())) fun l7 =>
                                      .load i32 (Arg.var l7.1) fun vla =>
                                      .let_ (Op.mk (.mul i64)
                                        (Arg.var xm.2.1, Arg.imm 4, ())) fun m1 =>
                                      .let_ (Op.mk (.add i64)
                                        (Arg.var pTmp, Arg.var m1.1, ())) fun m2 =>
                                      .load i32 (Arg.var m2.1) fun vb =>
                                      .let_ (Op.mk (.zext 32 64) (Arg.var vb, ())) fun m3 =>
                                      .let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun m4 =>
                                      .let_ (Op.mk (.lshr i64)
                                        (Arg.var m3.1, Arg.var m4.1, ())) fun m5 =>
                                      .let_ (Op.mk (.mul i64)
                                        (Arg.var m5.1, Arg.imm 4, ())) fun m6 =>
                                      .let_ (Op.mk (.add i64)
                                        (Arg.var pLvl, Arg.var m6.1, ())) fun m7 =>
                                      .load i32 (Arg.var m7.1) fun vlb =>
                                      .let_ (Op.mk (.cmp .ule i32 .bool rfl)
                                        (Arg.var vla, Arg.var vlb, ())) fun c8 =>
                                      .jnz (Arg.var c8.1)
                                        (.let_ (Op.mk (.mul i64)
                                          (Arg.var xm.2.2.1, Arg.imm 4, ())) fun n1 =>
                                        .let_ (Op.mk (.add i64)
                                          (Arg.var pWsort, Arg.var n1.1, ())) fun n2 =>
                                        .let_ (Op.mk (.mul i64)
                                          (Arg.var xm.1, Arg.imm 4, ())) fun n3 =>
                                        .let_ (Op.mk (.add i64)
                                          (Arg.var pTmp, Arg.var n3.1, ())) fun n4 =>
                                        .load i32 (Arg.var n4.1) fun vc =>
                                        .store (t := i32) (Arg.var vc) (Arg.var n2.1) (
                                          .let_ (Op.mk (.add i64)
                                            (Arg.var xm.1, Arg.imm 1, ())) fun n5 =>
                                          .jump JU.1 (Arg.var n5.1, Arg.var xm.2.1, ())))
                                        (.let_ (Op.mk (.mul i64)
                                          (Arg.var xm.2.2.1, Arg.imm 4, ())) fun o1 =>
                                        .let_ (Op.mk (.add i64)
                                          (Arg.var pWsort, Arg.var o1.1, ())) fun o2 =>
                                        .let_ (Op.mk (.mul i64)
                                          (Arg.var xm.2.1, Arg.imm 4, ())) fun o3 =>
                                        .let_ (Op.mk (.add i64)
                                          (Arg.var pTmp, Arg.var o3.1, ())) fun o4 =>
                                        .load i32 (Arg.var o4.1) fun vd =>
                                        .store (t := i32) (Arg.var vd) (Arg.var o2.1) (
                                          .let_ (Op.mk (.add i64)
                                            (Arg.var xm.2.1, Arg.imm 1, ())) fun o5 =>
                                          .jump JU.1 (Arg.var xm.1, Arg.var o5.1, ())))))
                                  (.jump JA.1 ()))
                                (.jump JA.1 ())))
                        .nil)
                        (fun J => .jump J.1 (Arg.var xlo.1, Arg.var xmid.1, Arg.var xlo.1, ())))
                    .nil)
                    (fun J =>
                      .let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun q1 =>
                      .let_ (Op.mk (.shl i64) (Arg.var xw.1, Arg.var q1.1, ())) fun q2 =>
                      .let_ (Op.mk (.add i64) (Arg.var xlo.1, Arg.var q2.1, ())) fun q3 =>
                      .let_ (Op.mk (.cmp .ult i64 .bool rfl)
                        (Arg.var q3.1, Arg.var n64, ())) fun c9 =>
                      .jnz (Arg.var c9.1)
                        (.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun q4 =>
                        .let_ (Op.mk (.shl i64) (Arg.var xw.1, Arg.var q4.1, ())) fun q5 =>
                        .let_ (Op.mk (.add i64) (Arg.var xlo.1, Arg.var q5.1, ())) fun q6 =>
                        .jump J.1 (Arg.var q6.1, ()))
                        (.jump J.1 (Arg.var n64, ()))))
                .nil)
                (fun J =>
                  .let_ (Op.mk (.add i64) (Arg.var xlo.1, Arg.var xw.1, ())) fun r1 =>
                  .let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var r1.1, Arg.var n64, ())) fun c10 =>
                  .jnz (Arg.var c10.1)
                    (.let_ (Op.mk (.add i64) (Arg.var xlo.1, Arg.var xw.1, ())) fun r2 =>
                    .jump J.1 (Arg.var r2.1, ()))
                    (.jump J.1 (Arg.var n64, ()))))
              (.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun s1 =>
              .let_ (Op.mk (.shl i64) (Arg.var xw.1, Arg.var s1.1, ())) fun s2 =>
              .jump JW.1 (Arg.var s2.1, ())))
          .nil)
          (fun J => .jump J.1 (Arg.imm 1, ())))
        (.ret ()))
    .nil)
    (fun J => .jump J.1 (Arg.imm 1, ()))

abbrev s7SortZeroExpr {Val : Ty → Type} {Cont : List Ty → Type}
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

abbrev s7SortHistExpr {Val : Ty → Type} {Cont : List Ty → Type}
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

abbrev s7SortPrefExpr {Val : Ty → Type} {Cont : List Ty → Type}
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

abbrev s7SortScatExpr {Val : Ty → Type} {Cont : List Ty → Type}
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


end LeanQbe.T.Examples.Kissat.FullFidelityStep7Proof0a

end
