module

public import LeanQbe.T.LeanLCNF.LcnfC0RtProofCommon
import LeanQbe.T.LeanLCNF.LcnfC0RtProofM0a
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.ControlComb
import all Kraken.Separation

/-!
# Soundness Proofs for `LcnfC0Rt`, Part M0b (Recursive Cold Dec / Mark Persistent / ModuleOk)

Proves `lcnf_mark_persistent_wp`, `lcnf_dec_ref_cold_wp`, `rtC0Env_dec_ref_cold_wp`,
`rtC0Env_mark_persistent_wp`, and `rtR0Mod_ok`.
-/

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF

open LeanQbe.T
open Std.ExtHashMap
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit
open LeanQbe.T.LeanLCNF.RtProof

public section

/-! ## Private BitVec, Header, Worklist & Dispatch Helpers -/

private theorem hdr_rc {o : LcnfObj} (hwf : o.Wf) :
    o.header &&& 4294967295#64 = BitVec.ofNat 64 o.rc.toNat :=
  LcnfObj.header_rc o hwf.2.2.2.1 hwf.2.2.2.2.1 hwf.2.2.2.2.2.1

private theorem hdr_clear_rc {o : LcnfObj} (hwf : o.Wf) :
    o.header &&& 18446744069414584320#64 = (o.withRc 0#32).header :=
  LcnfObj.header_clear_rc o hwf.2.2.2.1 hwf.2.2.2.2.1 hwf.2.2.2.2.2.1

private theorem hdr_tag {o : LcnfObj} (hwf : o.Wf) : o.header >>> 56 = BitVec.ofNat 64 o.tag :=
  LcnfObj.header_tag o hwf.2.2.2.1 hwf.2.2.2.2.1 hwf.2.2.2.2.2.1

private theorem hdr_tag_toNat {o : LcnfObj} (hwf : o.Wf) : (o.header >>> 56).toNat = o.tag := by
  rw [hdr_tag hwf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hwf.2.2.2.2.2.1; omega)]

private theorem hdr_other {o : LcnfObj} (hwf : o.Wf) :
    o.header >>> 48 &&& 255#64 = BitVec.ofNat 64 o.other :=
  LcnfObj.header_other o hwf.2.2.2.1 hwf.2.2.2.2.1 hwf.2.2.2.2.2.1

private theorem sext_56 : BitVec.signExtend 64 56#32 = 56#64 := rfl
private theorem sext_48 : BitVec.signExtend 64 48#32 = 48#64 := rfl
private theorem sext_16 : BitVec.signExtend 64 16#32 = 16#64 := rfl

private theorem hm_heap_left {A B C : Mem 64 → Prop} {m : Mem 64} (h : (A ⋆ B ⋆ C) m) :
    (B ⋆ (A ⋆ C)) m := by
  rw [sep_comm A B, sep_assoc] at h; exact h

private theorem hm_heap_unleft {A B C : Mem 64 → Prop} {m : Mem 64} (h : (B ⋆ (A ⋆ C)) m) :
    (A ⋆ B ⋆ C) m := by
  rw [← sep_assoc, sep_comm B A] at h; exact h

private theorem bv64_ugt_zero_iff (n : Nat) (hn : n < 2 ^ 64) :
    BitVec.ult 0#64 (BitVec.ofNat 64 n) = true ↔ 0 < n := by
  simp [BitVec.ult, Nat.mod_eq_of_lt hn]

private theorem bv64_ult_iff (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = true ↔ a < b := by
  simp [BitVec.ult, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

private theorem bv64_sub1_mul8 {n : Nat} (hn : 0 < n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n - 1#64) * 8#64 = BitVec.ofNat 64 (8 * (n - 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have h1 : (2 ^ 64 - 1 + n % 2 ^ 64) % 2 ^ 64 = n - 1 := by rw [Nat.mod_eq_of_lt hlt]; omega
  rw [h1, show (8#64 : BitVec 64).toNat = 8 by rfl]; simp only [BitVec.toNat_ofNat, Nat.mul_comm]

private theorem bv64_ofNat_add1 (n : Nat) :
    BitVec.ofNat 64 n + 1#64 = BitVec.ofNat 64 (n + 1) := by
  apply BitVec.eq_of_toNat_eq; simp [Nat.add_mod]

private theorem bv64_ofNat_sub1 {n : Nat} (hn : 0 < n) (hlt : n < 2 ^ 64) :
    BitVec.ofNat 64 n - 1#64 = BitVec.ofNat 64 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hlt, show (1 : Nat) % 2 ^ 64 = 1 by decide,
    show 2 ^ 64 - 1 + n = 2 ^ 64 + (n - 1) by omega, Nat.add_mod_left,
    Nat.mod_eq_of_lt (by omega)]

private theorem nodup_take_last {α : Type _} {xs : List α} (hne : xs ≠ []) :
    xs.take (xs.length - 1) ++ [xs[xs.length - 1]'(Nat.sub_lt (List.length_pos_iff.mpr hne)
    (by decide))] = xs := by
  have hpos : 0 < xs.length := List.length_pos_iff.mpr hne
  have := List.take_append_drop (xs.length - 1) xs
  have hdrop : xs.drop (xs.length - 1) =
      [xs[xs.length - 1]'(Nat.sub_lt hpos (by decide))] := by
    rw [List.drop_eq_getElem_cons (Nat.sub_lt hpos (by decide)),
      List.drop_of_length_le (by omega)]
  rwa [hdrop] at this

private theorem mem_not_in_take_last {α : Type _} {xs : List α} (hne : xs ≠ [])
    (hnodup : xs.Nodup) :
    xs[xs.length - 1]'(Nat.sub_lt (List.length_pos_iff.mpr hne) (by decide)) ∉
    xs.take (xs.length - 1) := by
  have hsplit := nodup_take_last hne; rw [← hsplit, List.nodup_append] at hnodup
  exact fun hm => hnodup.2.2 _ hm _ (by simp) rfl

private theorem workBuf_take_set {α : Type _} (wb : List α) {k : Nat} (hk : k < wb.length)
    (v : α) (xs : List α) (hpre : wb.take k = xs) : (wb.set k v).take (k + 1) = xs ++ [v] := by
  rw [list_take_set_append wb hk v, hpre]

private theorem rc32_toNat_eq_zero_iff (rc : BitVec 32) : rc.toNat = 0 ↔ rc = 0#32 :=
  ⟨fun h => BitVec.eq_of_toNat_eq (by simpa using h), fun h => h ▸ rfl⟩

private theorem rc32_toNat_eq_one_iff (rc : BitVec 32) : rc.toNat = 1 ↔ rc = 1#32 :=
  ⟨fun h => BitVec.eq_of_toNat_eq (by simpa using h), fun h => h ▸ rfl⟩

private theorem rc32_bv64_iff (rc : BitVec 32) (k : Nat) (hk : k < 2 ^ 32) :
    BitVec.ofNat 64 rc.toNat = BitVec.ofNat 64 k ↔ rc = BitVec.ofNat 32 k := by
  constructor
  · intro h; apply BitVec.eq_of_toNat_eq; have h1 := congrArg BitVec.toNat h
    have hlt : rc.toNat < 2 ^ 64 := Nat.lt_trans rc.isLt (by decide)
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt,
      Nat.mod_eq_of_lt (by omega : k < 2 ^ 64)] at h1
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]; exact h1
  · intro h; subst h; simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

private theorem bv64_ofNat_eq_zero_iff {rc : BitVec 32} :
    BitVec.ofNat 64 rc.toNat = 0#64 ↔ rc = 0#32 := rc32_bv64_iff rc 0 (by decide)

private theorem bv64_ofNat_eq_one_iff {rc : BitVec 32} :
    BitVec.ofNat 64 rc.toNat = 1#64 ↔ rc = 1#32 := rc32_bv64_iff rc 1 (by decide)

private theorem workCap_ne_zero_of_lt {st : RtC0State} {i n : Nat}
    (hi : i < n) (hCap : n ≤ st.workCap) (hc : st.hdr.s_work_cap.toNat = 0) : False :=
  Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.zero_lt_of_lt hi) hCap) hc

private theorem work_overflow_absurd {len cap : Nat} {sCap sCap' : BitVec 64}
    (hlt : len < cap) (h64 : len < 2 ^ 64) (hCap : cap = sCap.toNat)
    (hEq : sCap' = sCap) (hc : BitVec.ofNat 64 len = sCap') : False := by
  have htoNat := congrArg BitVec.toNat hc
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64, hEq, ← hCap] at htoNat; omega

private theorem nodup_append_singleton {α : Type _} {xs : List α} {x : α}
    (hnd : xs.Nodup) (hx : x ∉ xs) : (xs ++ [x]).Nodup :=
  List.nodup_append.mpr ⟨hnd, by simp, fun _ _ _ hb heq => by
      simp at hb; subst heq hb; exact hx ‹_›⟩

private theorem workBuf_init_take1 (wb : List (BitVec 64)) (h0 : 0 < wb.length)
    (a : BitVec 64) : (wb.set 0 a).take 1 = [a] := by
  simpa using workBuf_take_set wb h0 a [] (by simp)

private theorem workBuf_pop_eq (wb : List (BitVec 64)) (wl : List (BitVec 64)) {i : Nat}
    (htake : wb.take wl.length = wl) (hle : wl.length ≤ wb.length) (hi : i < wl.length) :
    wb[i]'(Nat.lt_of_lt_of_le hi hle) = wl[i] := by
  have hlt : i < (wb.take wl.length).length := by rw [List.length_take]; omega
  rw [← List.getElem_take (h := hlt)]; simp [htake]

private theorem mem_append_singleton_ite {α : Type _} [DecidableEq α] {c : α} {xs : List α}
    (hc : c ∉ xs) (a : α) :
    (if a ∈ xs ++ [c] then 1 else 0) = (if a ∈ xs then 1 else 0) + if a = c then 1 else 0 := by
  by_cases hac : a = c
  · subst hac; simp [hc]
  · by_cases ha : a ∈ xs <;> simp [ha, hac]

private theorem count_drop_succ {α : Type _} [DecidableEq α]
    (a : α) (xs : List α) {i : Nat} (hi : i < xs.length) : List.count a (xs.drop i) =
    (if a = xs[i] then 1 else 0) + List.count a (xs.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons hi, List.count_cons, Nat.add_comm]
  by_cases ha : a = xs[i]
  · simp [ha]
  · simp [ha, Ne.symm ha]

private theorem count_take_succ {α : Type _} [DecidableEq α]
    (a : α) (xs : List α) {i : Nat} (hi : i < xs.length) : List.count a (xs.take (i + 1)) =
    List.count a (xs.take i) + (if a = xs[i] then 1 else 0) := by
  rw [List.take_succ_eq_append_getElem hi, List.count_append, List.count_singleton]
  by_cases ha : a = xs[i]
  · simp [ha]
  · simp [ha, Ne.symm ha]

/-- Shared 4-way tag-to-`(childCount, childByteOffset)` C0 dispatch block used in both
`lcnf_mark_persistent_body` and `lcnf_dec_ref_cold_body`. -/
private theorem tag_dispatch_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {objs : List LcnfObj} {F : Mem 64 → Prop}
    {idx : Nat} (hidx : idx < objs.length) (hwf : objs[idx].Wf)
    (hm : (lcnfHeap objs ⋆ F) m) (J : Cont [i64, i64])
    (hJ : J (BitVec.ofNat 64 objs[idx].childFields.length, objFieldsOff objs[idx], ()) m) :
    wp Γ Q X (Expr.let_ (Op.mk (.cmp .eq i64)
    (Arg.var (objs[idx].header >>> BitVec.signExtend 64 56#32), Arg.imm 245, ())) fun p =>
    Expr.jnz (Arg.var p.fst) (Expr.let_ (Op.mk (.add i64) (Arg.var objs[idx].addr, Arg.imm 16, ()))
    fun p => Expr.load i64 (Arg.var p.fst) fun ld =>
    Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 16, ())) fun p =>
    Expr.let_ (Op.mk (.lshr i64) (Arg.var ld, Arg.var p.fst, ())) fun p =>
    Expr.let_ (Op.mk (.and i64) (Arg.var p.fst, Arg.imm 65535, ())) fun p =>
    Expr.jump J (Arg.var p.fst, Arg.imm 24, ())) (Expr.group (sig := [[i64, i64]])
      (fun _Js_1 => Blocks.cons
        (fun p => Expr.jump J (Arg.var p.fst, Arg.var p.snd.fst, ())) Blocks.nil)
      fun Js => Expr.let_ (Op.mk (.cmp .eq i64)
        (Arg.var (objs[idx].header >>> BitVec.signExtend 64 56#32), Arg.imm 246, ())) fun p =>
      Expr.jnz (Arg.var p.fst) (Expr.let_ (Op.mk (.add i64) (Arg.var objs[idx].addr, Arg.imm 8, ()))
        fun p => Expr.load i64 (Arg.var p.fst) fun ld =>
          Expr.jump Js.fst (Arg.var ld, Arg.imm 24, ()))
        (Expr.group (sig := [[i64, i64]]) (fun _Js_1 =>
          Blocks.cons (fun p => Expr.jump Js.fst (Arg.var p.fst, Arg.var p.snd.fst, ())) Blocks.nil)
          fun Js => Expr.let_ (Op.mk (.cmp .ule i64)
            (Arg.var (objs[idx].header >>> BitVec.signExtend 64 56#32), Arg.imm 244, ())) fun p =>
          Expr.jnz (Arg.var p.fst) (Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 48, ())) fun p =>
            Expr.let_ (Op.mk (.lshr i64) (Arg.var objs[idx].header, Arg.var p.fst, ())) fun p =>
            Expr.let_ (Op.mk (.and i64) (Arg.var p.fst, Arg.imm 255, ())) fun p =>
            Expr.jump Js.fst (Arg.var p.fst, Arg.imm 8, ()))
            (Expr.jump Js.fst (Arg.imm 0, Arg.imm 8, ()))))) m := by
  have htagN : (objs[idx].header >>> 56).toNat = objs[idx].tag := hdr_tag_toNat hwf
  have htagLt : objs[idx].tag < 256 := hwf.2.2.2.2.2.1; c0_hstep
  by_cases hClo : objs[idx].tag = closureTag
  · refine wp_jnz_true (bv64_tag_eq _ (by decide) (htagN.trans hClo)) ?_
    c0_hsteps_nogrp
    refine wp_load_of (v := objs[idx].cloMeta) (lcnfHeap_load_cloMeta hidx hClo hm) ?_
    c0_hsteps!
    have hwfClo := hwf.2.2.2.2.2.2.2.2.2; simp only [hClo, ↓reduceIte] at hwfClo
    have hnf : (objs[idx].cloMeta >>> 16#64 &&& 65535#64) =
        BitVec.ofNat 64 objs[idx].childFields.length := by
      rw [show objs[idx].childFields = objs[idx].fields by simp [LcnfObj.childFields, hClo],
        LcnfObj.cloMeta]
      exact cloMetaWord_nfix _ _ hwfClo.1 hwfClo.2.1
    rw [show objFieldsOff objs[idx] = 24#64 by simp [objFieldsOff, hClo]] at hJ
    erw [hnf]; exact hJ
  · refine wp_jnz_false (bv64_tag_ne _ (by decide) (fun h => hClo (htagN.symm.trans h))) ?_
    refine wp_join_state (fun p : BitVec 64 × BitVec 64 => (p.1, p.2, ()))
      (fun p m' => p.1 = BitVec.ofNat 64 objs[idx].childFields.length ∧
        p.2 = objFieldsOff objs[idx] ∧ m' = m)
      (fun _ _ m' ⟨h1, h2, hm'⟩ => by c0_hsteps!; rw [h1, h2, hm']; exact hJ) (fun K hK => ?_)
    c0_hstep
    by_cases hArr : objs[idx].tag = arrayTag
    · refine wp_jnz_true (bv64_tag_eq _ (by decide) (htagN.trans hArr)) ?_
      c0_hsteps_nogrp
      refine wp_load_of (v := BitVec.ofNat 64 objs[idx].fields.length)
        (lcnfHeap_load_arrSize hidx hArr hm) ?_
      c0_hsteps!
      exact hK (BitVec.ofNat 64 objs[idx].fields.length, 24#64) m
        ⟨by simp [LcnfObj.childFields, hArr], by simp [objFieldsOff, hArr], rfl⟩
    · refine wp_jnz_false (bv64_tag_ne _ (by decide) (fun h => hArr (htagN.symm.trans h))) ?_
      refine wp_join_state (fun p : BitVec 64 × BitVec 64 => (p.1, p.2, ()))
        (fun p m' => p.1 = BitVec.ofNat 64 objs[idx].childFields.length ∧
          p.2 = objFieldsOff objs[idx] ∧ m' = m)
        (fun _ _ m' hp => by c0_hsteps!; exact hK _ m' hp) (fun K2 hK2 => ?_)
      c0_hstep
      have hTagVal : objs[idx].header >>> BitVec.signExtend 64 56#32 =
          BitVec.ofNat 64 objs[idx].tag := by rw [sext_56]; exact hdr_tag hwf
      by_cases hCtor : objs[idx].tag ≤ 244
      · refine wp_jnz_true (by rw [hTagVal]; simp [BitVec.ule]; omega) ?_; c0_hsteps!
        have hwfC := hwf.2.2.2.2.2.2.2.2.2
        have hs1 : objs[idx].tag ≠ sarrayTag := by simp [sarrayTag]; omega
        have hs2 : objs[idx].tag ≠ stringTag := by simp [stringTag]; omega
        have hs3 : objs[idx].tag ≠ mpzTag := by simp [mpzTag]; omega
        simp only [hClo, hArr, hs1, hs2, hs3, ↓reduceIte] at hwfC
        have hoth : objs[idx].header >>> BitVec.signExtend 64 48#32 &&& 255#64 =
            BitVec.ofNat 64 objs[idx].childFields.length := by
          rw [sext_48]; erw [hdr_other hwf]
          rw [show objs[idx].childFields = objs[idx].fields by simp [LcnfObj.childFields, hCtor],
            hwfC.2.1]
        exact hK2 (_, 8#64) m ⟨hoth, by simp [objFieldsOff, hClo, hArr], rfl⟩
      · refine wp_jnz_false (by rw [hTagVal]; simp [BitVec.ule]; omega) ?_; c0_hsteps!
        exact hK2 (0#64, 8#64) m ⟨by simp [LcnfObj.childFields, hCtor, hClo, hArr],
          by simp [objFieldsOff, hClo, hArr], rfl⟩

/-! ## `lcnf_mark_persistent` Verification -/

private structure MarkState where
  st : RtC0State
  curObjs : List LcnfObj
  wl : List (BitVec 64)

private def MarkInv (rt root : BitVec 64) (objs : List LcnfObj) (st0 : RtC0State)
    (R : Mem 64 → Prop) (ms : MarkState) (m : Mem 64) : Prop :=
  ms.curObjs.length = objs.length ∧ ms.st.PreservesMeta st0 ∧
  ms.st.rem = st0.rem ∧ (rtC0Inv rt ms.st ⋆ lcnfHeap ms.curObjs ⋆ R) m ∧
  lcnfHeapClosed ms.curObjs ∧ ms.wl.length ≤ ms.st.workCap ∧
  ms.wl.Nodup ∧ ms.st.workBuf.take ms.wl.length = ms.wl ∧
  (∀ k (hk : k < objs.length) (hk' : k < ms.curObjs.length), SameNonRc objs[k] ms.curObjs[k] ∧
    ms.curObjs[k].Wf ∧ (objs[k].addr = root → ms.curObjs[k].rc = 0#32) ∧
    (ms.curObjs[k].rc = objs[k].rc ∨ ms.curObjs[k].rc = 0#32) ∧
    (objs[k].rc ≠ 0#32 → ms.curObjs[k].rc = 0#32 → NonPersistReach objs root objs[k].addr)) ∧
  (∀ a ∈ ms.wl, ∃ k : Nat, ∃ (_ : k < objs.length) (_ : k < ms.curObjs.length),
    objs[k].addr = a ∧ objs[k].rc ≠ 0#32 ∧ ms.curObjs[k].rc = 0#32) ∧
  (∀ k (hk : k < objs.length) (hk' : k < ms.curObjs.length),
    objs[k].rc ≠ 0#32 → ms.curObjs[k].rc = 0#32 → ms.curObjs[k].addr ∉ ms.wl →
      ∀ f ∈ ms.curObjs[k].childFields, f &&& 1#64 = 0#64 →
        ∃ q ∈ ms.curObjs, q.addr = f ∧ q.rc = 0#32)

private def markMeasure (objs : List LcnfObj) (ms : MarkState) : Nat :=
  (objs.length + 1) * unmarkedCount ms.curObjs + ms.wl.length

private structure MarkInnerState where
  st : RtC0State
  curObjs : List LcnfObj
  wl : List (BitVec 64)
  i : Nat

private def MarkInnerInv (rt root : BitVec 64) (objs : List LcnfObj) (st0 : RtC0State)
    (R : Mem 64 → Prop) (idxX u0 w0 : Nat) (mis : MarkInnerState) (m : Mem 64) : Prop :=
  mis.curObjs.length = objs.length ∧ mis.st.PreservesMeta st0 ∧
  mis.st.rem = st0.rem ∧ (rtC0Inv rt mis.st ⋆ lcnfHeap mis.curObjs ⋆ R) m ∧
  lcnfHeapClosed mis.curObjs ∧ mis.wl.length ≤ mis.st.workCap ∧
  mis.wl.Nodup ∧ mis.st.workBuf.take mis.wl.length = mis.wl ∧
  (∃ hx : idxX < objs.length, ∃ hx' : idxX < mis.curObjs.length,
    ∃ hilen : mis.i ≤ mis.curObjs[idxX].childFields.length,
      objs[idxX].rc ≠ 0#32 ∧ mis.curObjs[idxX].rc = 0#32 ∧ mis.curObjs[idxX].addr ∉ mis.wl ∧
      ∀ (j : Nat) (hj : j < mis.i),
        mis.curObjs[idxX].childFields[j]'(Nat.lt_of_lt_of_le hj hilen) &&& 1#64 = 0#64 →
          ∃ q ∈ mis.curObjs,
            q.addr = mis.curObjs[idxX].childFields[j]'(Nat.lt_of_lt_of_le hj hilen) ∧
            q.rc = 0#32) ∧
  (unmarkedCount mis.curObjs < u0 ∨ (unmarkedCount mis.curObjs = u0 ∧ mis.wl.length + 1 ≤ w0)) ∧
  (∀ k (hk : k < objs.length) (hk' : k < mis.curObjs.length), SameNonRc objs[k] mis.curObjs[k] ∧
    mis.curObjs[k].Wf ∧ (objs[k].addr = root → mis.curObjs[k].rc = 0#32) ∧
    (mis.curObjs[k].rc = objs[k].rc ∨ mis.curObjs[k].rc = 0#32) ∧
    (objs[k].rc ≠ 0#32 → mis.curObjs[k].rc = 0#32 → NonPersistReach objs root objs[k].addr)) ∧
  (∀ a ∈ mis.wl, ∃ k : Nat, ∃ (_ : k < objs.length) (_ : k < mis.curObjs.length),
    objs[k].addr = a ∧ objs[k].rc ≠ 0#32 ∧ mis.curObjs[k].rc = 0#32) ∧
  (∀ k (hk : k < objs.length) (hk' : k < mis.curObjs.length),
    k ≠ idxX → objs[k].rc ≠ 0#32 → mis.curObjs[k].rc = 0#32 →
    mis.curObjs[k].addr ∉ mis.wl →
      ∀ f ∈ mis.curObjs[k].childFields, f &&& 1#64 = 0#64 →
        ∃ q ∈ mis.curObjs, q.addr = f ∧ q.rc = 0#32)

private theorem mark_skip_inv {rt root : BitVec 64} {objs : List LcnfObj} {st0 : RtC0State}
    {R : Mem 64 → Prop} {idxX u0 w0 : Nat} {mis : MarkInnerState} {m : Mem 64}
    (hInv : MarkInnerInv rt root objs st0 R idxX u0 w0 mis m) (hx : idxX < mis.curObjs.length)
    (hiLt : mis.i < (mis.curObjs[idxX]'hx).childFields.length)
    (hElem : ((mis.curObjs[idxX]'hx).childFields[mis.i]'hiLt &&& 1#64 = 0#64) →
    ∃ q ∈ mis.curObjs, q.addr = (mis.curObjs[idxX]'hx).childFields[mis.i]'hiLt ∧ q.rc = 0#32) :
    MarkInnerInv rt root objs st0 R idxX u0 w0 ⟨mis.st, mis.curObjs, mis.wl, mis.i + 1⟩ m := by
  rcases hInv with ⟨hlenI, hPreI, hRemI, hmI, hClosedI, hWlICap, hWlINodup, hWlITake,
    ⟨hxIO, hxIC, _, hxIOrigNz, hxICur0, hxINotIn, hPrefixX⟩,
    hMeasI, hPerI, hWlIMem, hClosedOthersI⟩
  refine ⟨hlenI, hPreI, hRemI, hmI, hClosedI, hWlICap, hWlINodup, hWlITake,
    ⟨hxIO, hxIC, hiLt, hxIOrigNz, hxICur0, hxINotIn, fun j hj hjev => ?_⟩,
    hMeasI, hPerI, hWlIMem, hClosedOthersI⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjOld | rfl
  · exact hPrefixX j hjOld hjev
  · exact hElem hjev

private theorem mark_rel_self {root : BitVec 64} {objs : List LcnfObj}
    (hwf : ∀ o ∈ objs,
        o.Wf) (hclosed : lcnfHeapClosed objs) (hnodup : (objs.map LcnfObj.addr).Nodup)
    (hzero : ∃ obj ∈ objs, obj.addr = root ∧ obj.rc = 0#32) : MarkPersistRel root objs objs := by
  rcases hzero with ⟨obj0, hmem0, had0, hrc0⟩; refine ⟨rfl, hwf, hclosed, hclosed, fun p hp => ?_⟩
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hp
  simp only [List.length_zip, Nat.min_self] at hk; rw [List.getElem_zip]
  refine ⟨hwf _ (List.getElem_mem hk), rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    fun ha => by rw [nodup_addr_eq_of_mem hnodup (List.getElem_mem hk) hmem0
      (ha.trans had0.symm), hrc0], Or.inl rfl, fun hnz => ⟨fun h => False.elim (hnz h), fun hr => by
      obtain ⟨o', hm', ha', hnz'⟩ := nonPersistReach_root_nz hr
      exact absurd (by rw [nodup_addr_eq_of_mem hnodup hm' hmem0 (ha'.trans had0.symm),
          hrc0]) hnz'⟩⟩

private theorem mark_rel_of_inv {rt root : BitVec 64} {objs : List LcnfObj} {st0 : RtC0State}
    {R : Mem 64 → Prop} {ms : MarkState} {m : Mem 64} (hwfO : ∀ o ∈ objs, o.Wf)
    (hclosedO : lcnfHeapClosed objs) (hnodupO : (objs.map LcnfObj.addr).Nodup)
    (hinv : MarkInv rt root objs st0 R ms m) (hwl : ms.wl = []) :
    MarkPersistRel root objs ms.curObjs := by
  rcases hinv with ⟨hlen, _, _, _, hclosedC, _, _, _, hPer, _, hClosed⟩
  have hcomplete : ∀ {a}, NonPersistReach objs root a → ∃ k : Nat,
      ∃ (_ : k < ms.curObjs.length), ms.curObjs[k].addr = a ∧ ms.curObjs[k].rc = 0#32 :=
    nonPersistReach_mark_complete hlen hnodupO (fun k hk hk' h => (hPer k hk hk').2.2.1 h)
      (fun k hk hk' => (hPer k hk hk').1)
      (fun k hk hk' hnz hc0 f hf hev => hClosed k hk hk' hnz hc0 (by simp [hwl]) f hf hev)
  refine ⟨hlen, hwfO, hclosedO, hclosedC, fun p hp => ?_⟩
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hp
  simp only [List.length_zip, hlen, Nat.min_self] at hk
  have hk' : k < ms.curObjs.length := hlen ▸ hk; rw [List.getElem_zip]
  rcases hPer k hk hk' with ⟨⟨ha, hcs, hot, htg, hfn, har, hcp, has, hsl, hfd, hsd, hlb⟩,
    hwfC, hrt, hrcOr, hreach⟩
  refine ⟨hwfC, ha, hcs, hot, htg, hfn, har, hcp, has, hsl, hfd, hsd, hlb, hrt, hrcOr,
    fun hnz => ⟨hreach hnz, fun hnp => ?_⟩⟩
  obtain ⟨j, hj, hja, hjc⟩ := hcomplete hnp; have hjO : j < objs.length := hlen ▸ hj
  obtain rfl := nodup_addr_idx_eq hnodupO hjO hk ((hPer j hjO hj).1.1.symm.trans hja); exact hjc

/-- Verified soundness proof for `lcnf_mark_persistent`. -/
theorem lcnf_mark_persistent_wp (Γ : Env) : ∀ (xs : Tup Val lcnf_mark_persistent.as) (m : Mem 64)
    (Q : Post lcnf_mark_persistent.rs) (X : XPost),
    lcnfMarkPersistentSpec xs m Q X → Func.wp Γ lcnf_mark_persistent.body xs m Q X := by
  rintro ⟨rt, o, ⟨⟩⟩ m Q X hspec
  dsimp only [lcnf_mark_persistent, lcnf_mark_persistent_body, Func.wp]
  dsimp only [lcnfMarkPersistentSpec] at hspec
  by_cases hOdd : o &&& 1#64 ≠ 0#64
  · obtain ⟨_, _, _, hQ⟩ := show ∃ st R, (rtC0Inv rt st ⋆ R) m ∧ Q () m by simpa [hOdd] using hspec
    c0_hsteps_nogrp; exact hQ
  · have hEven : o &&& 1#64 = 0#64 := Classical.not_not.mp hOdd
    obtain ⟨st, objs, R, hCap, hm, ⟨obj0, ho0, had0⟩, hWfO, hClosedO, hCont⟩ := show
        ∃ st objs R, objs.length ≤ st.workCap ∧ (rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R) m ∧
          (∃ obj ∈ objs, obj.addr = o) ∧ (∀ obj ∈ objs, obj.Wf) ∧ lcnfHeapClosed objs ∧
          ∀ st' objs' m', st'.PreservesMeta st → st'.rem = st.rem →
            MarkPersistRel o objs objs' → (rtC0Inv rt st' ⋆ lcnfHeap objs' ⋆ R) m' → Q () m' by
      simpa [hOdd] using hspec
    have hNodupO := lcnfHeap_nodup_addrs (hm_heap_left hm)
    obtain ⟨idx0, hidx0, rfl⟩ := List.mem_iff_getElem.mp ho0; subst had0; c0_hsteps_nogrp
    · refine wp_load_of (v := objs[idx0].header) (lcnfHeap_load_header hidx0 (hm_heap_left hm)) ?_
      c0_hsteps_nogrp
      · have hRc0 : objs[idx0].rc = 0#32 := by
          erw [hdr_rc (hWfO _ (List.getElem_mem hidx0))] at hc; exact bv64_ofNat_eq_zero_iff.mp hc
        exact hCont st objs m ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl
          (mark_rel_self hWfO hClosedO hNodupO ⟨objs[idx0], List.getElem_mem hidx0, rfl, hRc0⟩) hm
      · have hRcNz : objs[idx0].rc ≠ 0#32 := fun hz => by
          erw [hdr_rc (hWfO _ (List.getElem_mem hidx0)), hz] at hc; simp at hc
        refine head_wp_store (hdr_clear_rc (hWfO _ (List.getElem_mem hidx0))) rfl
          (lcnfHeap_store_rc hidx0 0#32 (hm_heap_left hm)) (fun m1 hm1 => ?_)
        let objs1 := objs.set idx0 (objs[idx0].withRc 0#32)
        have hm1' : (rtC0Inv rt st ⋆ lcnfHeap objs1 ⋆ R) m1 := hm_heap_unleft hm1; c0_hsteps_nogrp
        · exfalso; exact workCap_ne_zero_of_lt hidx0 hCap (by
            have := congrArg BitVec.toNat hc
            simpa [RtC0State.withPersistInc, RtC0State.withPersist] using this)
        · let st1 := RtC0State.withPersistInc st
          have hWork0 : 0 < st1.workBuf.length := by rw [st1.workLen]; change 0 < st.workCap; omega
          have hmWork1 : (rtC0Inv rt st1 ⋆ (lcnfHeap objs1 ⋆ R)) m := by
            rw [sep_emp] at hm; exact hm
          refine head_wp_store rfl (by simp [st1, RtC0State.withPersistInc, RtC0State.withPersist])
            (rtC0Inv_store_work hWork0 objs[idx0].addr hmWork1) (fun m2 hm2 => ?_)
          let wb2 := st1.workBuf.set 0 objs[idx0].addr
          let st2 := RtC0State.withWorkBuf st1 wb2 (by simpa [wb2] using st1.workLen)
          have hm2' : (rtC0Inv rt st2 ⋆ lcnfHeap objs1 ⋆ R) m2 := by simpa [sep_assoc] using hm2
          refine wp_while_state1 (fun ms : MarkState => BitVec.ofNat 64 ms.wl.length)
            (markMeasure objs) (MarkInv rt objs[idx0].addr objs st R)
            (fun J hJ => ?_) (fun J ms mL hInv hIH => ?_)
          · c0_hsteps!; refine hJ ⟨st2, objs1, [objs[idx0].addr]⟩ m2 ?_
            have hPre1 : st1.PreservesMeta st := by
              simp [st1, RtC0State.withPersistInc, RtC0State.withPersist, RtC0State.PreservesMeta]
            have hPre2 : st2.PreservesMeta st := preservesMeta_trans hPre1
              (by simp [st2, RtC0State.withWorkBuf, RtC0State.PreservesMeta])
            have hTake : st2.workBuf.take 1 = [objs[idx0].addr] :=
              workBuf_init_take1 st1.workBuf hWork0 objs[idx0].addr
            refine ⟨by simp [objs1], hPre2, rfl, hm2',
              lcnfHeapClosed_set_withRc hClosedO hidx0 0#32,
              by dsimp only [st2, st1, RtC0State.withWorkBuf, RtC0State.withPersistInc,
                RtC0State.withPersist]; change 1 ≤ st.workCap; omega, by simp, hTake, ?_, ?_, ?_⟩
            · intro k hk hk'; dsimp only at hk' ⊢; by_cases hkEq : k = idx0
              · subst hkEq; simp only [objs1, List.getElem_set_self]
                exact ⟨SameNonRc.withRc_r (SameNonRc.refl _) 0#32,
                  objWf_withRc_zero (hWfO _ (List.getElem_mem hk)),
                  fun _ => by simp [LcnfObj.withRc], Or.inr (by simp [LcnfObj.withRc]),
                  fun hnz _ => NonPersistReach.refl ⟨objs[k], List.getElem_mem hk, rfl, hnz⟩⟩
              · simp only [objs1, List.getElem_set_ne (Ne.symm hkEq) hk']
                exact ⟨SameNonRc.refl _, hWfO _ (List.getElem_mem hk),
                  fun heq => False.elim (hkEq (nodup_addr_idx_eq hNodupO hk hidx0 heq)),
                  Or.inl trivial, fun hnz h0 => False.elim (hnz h0)⟩
            · intro a ha; simp only [List.mem_singleton] at ha; subst ha
              exact ⟨idx0, hidx0, by simpa [objs1] using hidx0, rfl, hRcNz,
                by simp [objs1, LcnfObj.withRc]⟩
            · intro k hk hk' hnz hc0 hnotin; dsimp only at hk' hc0 hnotin; by_cases hkEq : k = idx0
              · subst hkEq; exact absurd (by simp [objs1, LcnfObj.withRc]) hnotin
              · simp only [objs1, List.getElem_set_ne (Ne.symm hkEq) hk'] at hc0
                exact False.elim (hnz hc0)
          · rcases hInv with ⟨hlenC, hPreL, hRemL, hmL, hClosedC, hWlCap, hWlNodup, hWlTake,
              hPer, hWlMem, hClosedOthers⟩
            have hWlLt64 : ms.wl.length < 2 ^ 64 :=
              Nat.lt_of_le_of_lt hWlCap ms.st.hdr.s_work_cap.isLt
            c0_hstep; by_cases hWlPos : 0 < ms.wl.length
            · refine wp_jnz_true (by erw [bv64_ugt_zero_iff ms.wl.length hWlLt64]; exact hWlPos) ?_
              have hWlNe : ms.wl ≠ [] := List.ne_nil_of_length_pos hWlPos
              let sp' := ms.wl.length - 1; let xAddr := ms.wl[sp']; let wl' := ms.wl.take sp'
              have hWlSplit : wl' ++ [xAddr] = ms.wl := nodup_take_last hWlNe
              have hXNotIn : xAddr ∉ wl' := mem_not_in_take_last hWlNe hWlNodup
              have hNodupWl' : wl'.Nodup := (List.nodup_append.mp (hWlSplit ▸ hWlNodup)).1
              have hTake' : ms.st.workBuf.take sp' = wl' := by
                calc ms.st.workBuf.take sp' = (ms.st.workBuf.take ms.wl.length).take sp' := by
                        rw [List.take_take, Nat.min_eq_left (by omega)]
                  _ = wl' := by rw [hWlTake]
              have hXInWl : xAddr ∈ ms.wl := List.getElem_mem _
              obtain ⟨idxX, hxO, hxC, hxAddrO, hxOrigNz, hxCur0⟩ := hWlMem xAddr hXInWl
              have hxSame := (hPer idxX hxO hxC).1; have hxWf := (hPer idxX hxO hxC).2.1
              have hxAddrC : ms.curObjs[idxX].addr = xAddr := hxSame.1.trans hxAddrO
              have hSpWork : sp' < ms.st.workBuf.length := by
                rw [ms.st.workLen]; change sp' < ms.st.workCap; omega
              have hWorkAtSp := workBuf_pop_eq ms.st.workBuf ms.wl hWlTake
                (by rw [ms.st.workLen]; exact hWlCap) (by omega : sp' < ms.wl.length)
              c0_hsteps_nogrp; erw [bv64_sub1_mul8 hWlPos hWlLt64]
              rw [show (RtC0State.withPersist st (st.hdr.s_st_persistent + 1)).hdr.s_work =
                ms.st.hdr.s_work by simp [RtC0State.withPersist, hPreL.2.2.2.2.1]]
              have hloadWork : loadVal mL i64 (ms.st.hdr.s_work + BitVec.ofNat 64 (8 * sp')) =
                  some xAddr := by
                simpa only [hWorkAtSp] using rtC0Inv_load_work hSpWork
                  (by simpa [sep_assoc] using hmL)
              refine wp_load_of (v := xAddr) hloadWork ?_
              refine wp_load_of (v := ms.curObjs[idxX].header)
                (hxAddrC ▸ lcnfHeap_load_header hxC (hm_heap_left hmL)) ?_
              c0_hsteps_nogrp
              have hOfSub1 : BitVec.ofNat 64 ms.wl.length - 1#64 = BitVec.ofNat 64 sp' :=
                bv64_ofNat_sub1 hWlPos hWlLt64
              let u0 := unmarkedCount ms.curObjs; let w0 := ms.wl.length
              refine wp_join_state (fun _ : Unit =>
                  (BitVec.ofNat 64 ms.curObjs[idxX].childFields.length,
                    objFieldsOff ms.curObjs[idxX], ()))
                (fun _ m' => m' = mL) (fun _ _ m' hmEq => ?_) (fun K hK => ?_)
              · subst hmEq
                refine wp_while_state (fun mis : MarkInnerState =>
                    (BitVec.ofNat 64 mis.wl.length, BitVec.ofNat 64 mis.i, ()))
                  (fun mis : MarkInnerState => objs[idxX].childFields.length - mis.i)
                  (MarkInnerInv rt objs[idx0].addr objs st R idxX u0 w0)
                  (fun L hL => ?_) (fun L mis mI hInvI hIL => ?_)
                · c0_hsteps!; erw [hOfSub1]
                  have hWl'Len : wl'.length = sp' := by dsimp [wl']; rw [List.length_take]; omega
                  rw [← hWl'Len]; refine hL ⟨ms.st, ms.curObjs, wl', 0⟩ m' ?_
                  refine ⟨hlenC, hPreL, hRemL, hmL, hClosedC, by dsimp only; rw [hWl'Len]; omega,
                    hNodupWl', by dsimp only; rw [hWl'Len]; exact hTake',
                    ⟨hxO, hxC, by dsimp only; omega, hxOrigNz, hxCur0, hxAddrC.symm ▸ hXNotIn,
                      fun j hj => by dsimp only at hj; omega⟩,
                    Or.inr ⟨rfl, by dsimp only; rw [hWl'Len]; omega⟩, hPer, ?_, ?_⟩
                  · intro a ha; exact hWlMem a (hWlSplit ▸ List.mem_append_left [xAddr] ha)
                  · intro k hk hk' hne hnz hc0 hnotin
                    refine hClosedOthers k hk hk' hnz hc0 ?_
                    intro hinWl; rw [← hWlSplit, List.mem_append, List.mem_singleton] at hinWl
                    rcases hinWl with hin | heqX
                    · exact hnotin hin
                    · have hkEq : objs[k].addr = objs[idxX].addr := by
                        calc objs[k].addr = ms.curObjs[k].addr := (hPer k hk hk').1.1.symm
                          _ = xAddr := heqX
                          _ = objs[idxX].addr := hxAddrO.symm
                      exact hne (nodup_addr_idx_eq hNodupO hk hxO hkEq)
                · have hAllI := hInvI
                  rcases hInvI with ⟨hlenI, hPreI, hRemI, hmI, hClosedI, hWlICap, hWlINodup,
                    hWlITake, ⟨hxIO, hxIC, hiLen, hxIOrigNz, hxICur0, hxINotIn, hPrefixX⟩,
                    hMeasI, hPerI, hWlIMem, hClosedOthersI⟩
                  have hiLt64 : mis.i < 2 ^ 64 := Nat.lt_of_le_of_lt hiLen
                    (objWf_childFields_lt (hPerI idxX hxIO hxIC).2.1)
                  have hcfLenLt64 : mis.curObjs[idxX].childFields.length < 2 ^ 64 :=
                    objWf_childFields_lt (hPerI idxX hxIO hxIC).2.1
                  have hxICf : mis.curObjs[idxX].childFields = objs[idxX].childFields :=
                    SameNonRc.childFields_eq (hPerI idxX hxIO hxIC).1
                  have hMsCf : ms.curObjs[idxX].childFields = mis.curObjs[idxX].childFields :=
                    (SameNonRc.childFields_eq hxSame).trans hxICf.symm
                  have hWlILt64 : mis.wl.length < 2 ^ 64 :=
                    Nat.lt_of_le_of_lt hWlICap mis.st.hdr.s_work_cap.isLt
                  rw [hMsCf]; c0_hstep
                  have hUltIff := bv64_ult_iff mis.i mis.curObjs[idxX].childFields.length
                    hiLt64 hcfLenLt64
                  by_cases hiLt : mis.i < mis.curObjs[idxX].childFields.length
                  · refine wp_jnz_true (hUltIff.mpr hiLt) ?_
                    let c := mis.curObjs[idxX].childFields[mis.i]; c0_hsteps_nogrp
                    erw [bv64_8_mul mis.i]
                    have hloadC : loadVal mI i64 (mis.curObjs[idxX].addr +
                        objFieldsOff mis.curObjs[idxX] + BitVec.ofNat 64 (8 * mis.i)) = some c :=
                      lcnfHeap_load_child hxIC (hPerI idxX hxIO hxIC).2.1 (hm_heap_left hmI) hiLt
                    have hxIOff : objFieldsOff mis.curObjs[idxX] =
                        objFieldsOff ms.curObjs[idxX] := by
                      simp [objFieldsOff, (hPerI idxX hxIO hxIC).1.2.2.2.1, hxSame.2.2.2.1]
                    have hxIA : mis.curObjs[idxX].addr = xAddr :=
                      (hPerI idxX hxIO hxIC).1.1.trans hxAddrO
                    rw [hxIOff, hxIA] at hloadC
                    refine wp_load_of (v := c) hloadC ?_
                    refine wp_join_state1 (fun misNext : MarkInnerState =>
                        BitVec.ofNat 64 misNext.wl.length)
                      (fun misNext mNext => misNext.i = mis.i + 1 ∧
                        MarkInnerInv rt objs[idx0].addr objs st R idxX u0 w0 misNext mNext)
                      (fun Jjoin misNext mNext hJn => ?_) (fun Jjoin hJoin => ?_)
                    · rcases hJn with ⟨hiNext, hInvNext⟩; c0_hsteps!
                      erw [bv64_ofNat_add1 mis.i]; rw [← hiNext]
                      exact hIL misNext mNext (by rw [hiNext, ← hxICf]; omega) hInvNext
                    · c0_hsteps_nogrp
                      · have hcEven : c &&& 1#64 = 0#64 := hc
                        obtain ⟨qC, hqCMem, hqCAddr⟩ := hClosedI _ (List.getElem_mem hxIC) _
                          (List.getElem_mem hiLt) hcEven
                        obtain ⟨idxC, hidxC, rfl⟩ := List.mem_iff_getElem.mp hqCMem
                        have hidxCO : idxC < objs.length := hlenI ▸ hidxC
                        have hwfC := (hPerI idxC hidxCO hidxC).2.1
                        refine wp_load_of (v := mis.curObjs[idxC].header)
                          (hqCAddr ▸ lcnfHeap_load_header hidxC (hm_heap_left hmI)) ?_
                        refine wp_join_state1 (fun misNext : MarkInnerState =>
                            BitVec.ofNat 64 misNext.wl.length)
                          (fun misNext mNext => misNext.i = mis.i + 1 ∧
                            MarkInnerInv rt objs[idx0].addr objs st R idxX u0 w0 misNext mNext)
                          (fun Jjoin2 misNext mNext hJ2 => ?_) (fun Jjoin2 hJoin2 => ?_)
                        · c0_hsteps!; exact hJoin misNext mNext hJ2
                        · c0_hsteps_nogrp
                          · have hCRc0 : mis.curObjs[idxC].rc ≠ 0#32 := fun hz =>
                              hc (by erw [hdr_rc hwfC, hz]; rfl)
                            have hCOrigNz : objs[idxC].rc ≠ 0#32 := by
                              rcases (hPerI idxC hidxCO hidxC).2.2.2.1 with h | h
                              · exact fun hz => hCRc0 (h.trans hz)
                              · exact False.elim (hCRc0 h)
                            have hNodupI : (mis.curObjs.map LcnfObj.addr).Nodup :=
                              lcnfHeap_nodup_addrs (hm_heap_left hmI)
                            have hcNeXIdx : idxC ≠ idxX := fun heq => by
                              subst heq; exact hCRc0 hxICur0
                            have hcNeX : mis.curObjs[idxC].addr ≠ mis.curObjs[idxX].addr :=
                              lcnfHeap_addr_ne (hm_heap_left hmI) hidxC hxIC hcNeXIdx
                            have hcNotIn : mis.curObjs[idxC].addr ∉ mis.wl := fun hin => by
                              obtain ⟨j, hjO, hjC, hjHad, _, hj0⟩ := hWlIMem _ hin
                              have haddrEq : mis.curObjs[j].addr = mis.curObjs[idxC].addr :=
                                (hPerI j hjO hjC).1.1.trans hjHad
                              obtain rfl := nodup_addr_idx_eq hNodupI hjC hidxC haddrEq
                              exact hCRc0 hj0
                            have hWorkLtCap : mis.wl.length < mis.st.workCap := by
                              refine work_push_lt_cap hWlINodup hxINotIn (hqCAddr ▸ hcNotIn)
                                (hqCAddr ▸ hcNeX) ⟨mis.curObjs[idxX], List.getElem_mem hxIC, rfl⟩
                                ⟨mis.curObjs[idxC], List.getElem_mem hidxC, hqCAddr⟩ (fun a ha => by
                                  obtain ⟨k, hkO, hkC, had, _⟩ := hWlIMem a ha
                                  exact ⟨mis.curObjs[k], List.getElem_mem hkC,
                                    (hPerI k hkO hkC).1.1.trans had⟩)
                                (by rw [hlenI]; simpa [RtC0State.workCap,
                                  hPreI.2.2.2.2.2.1] using hCap)
                            refine head_wp_store (hdr_clear_rc hwfC) rfl
                              (hqCAddr ▸ lcnfHeap_store_rc hidxC 0#32 (hm_heap_left hmI))
                              (fun mI1 hmI1 => ?_)
                            let curObjs' := mis.curObjs.set idxC (mis.curObjs[idxC].withRc 0#32)
                            have hmI1' : (rtC0Inv rt mis.st ⋆ lcnfHeap curObjs' ⋆ R) mI1 :=
                              hm_heap_unleft hmI1
                            c0_hsteps_nogrp
                            · exfalso; exact work_overflow_absurd hWorkLtCap hWlILt64 rfl
                                hPreI.2.2.2.2.2.1 (by simpa [RtC0State.withPersist] using hc)
                            · let stI1 := RtC0State.withPersistInc mis.st
                              have hIdxWork : mis.wl.length < stI1.workBuf.length := by
                                rw [stI1.workLen]; exact hWorkLtCap
                              have hmWork1 : (rtC0Inv rt stI1 ⋆ (lcnfHeap curObjs' ⋆ R)) m := by
                                rw [sep_emp] at hm; exact hm
                              rw [hPreL.2.2.2.2.1.symm.trans hPreI.2.2.2.2.1]
                              refine head_wp_store rfl (by erw [bv64_mul8_comm mis.wl.length]; rfl)
                                (rtC0Inv_store_work hIdxWork c hmWork1) (fun mI2 hmI2 => ?_)
                              let wbI2 := stI1.workBuf.set mis.wl.length c
                              let stI2 := RtC0State.withWorkBuf stI1 wbI2
                                (by simpa [wbI2] using stI1.workLen)
                              have hmI2' : (rtC0Inv rt stI2 ⋆ lcnfHeap curObjs' ⋆ R) mI2 := by
                                simpa [sep_assoc] using hmI2
                              c0_hsteps!; erw [bv64_ofNat_add1 mis.wl.length]
                              rw [← show (mis.wl ++ [c]).length = mis.wl.length + 1 by simp]
                              refine hJoin2 ⟨stI2, curObjs', mis.wl ++ [c], mis.i + 1⟩ mI2 ⟨rfl, ?_⟩
                              have h1 : stI1.PreservesMeta mis.st := by
                                simp [stI1, RtC0State.withPersistInc, RtC0State.withPersist,
                                  RtC0State.PreservesMeta]
                              have hPreI2 : stI2.PreservesMeta st := preservesMeta_trans hPreI
                                (preservesMeta_trans h1
                                  (by simp [stI2, RtC0State.withWorkBuf, RtC0State.PreservesMeta]))
                              have hUnmarked : unmarkedCount curObjs' < u0 := by
                                have := unmarkedCount_set_zero mis.curObjs hidxC hCRc0
                                dsimp only [curObjs']; rcases hMeasI with h | ⟨h, _⟩ <;> omega
                              have hTakeI2 :
                                  stI2.workBuf.take (mis.wl ++ [c]).length = mis.wl ++ [c] := by
                                rw [List.length_append, List.length_singleton]
                                exact workBuf_take_set stI1.workBuf hIdxWork c mis.wl hWlITake
                              have hNodupWl' : (mis.wl ++ [c]).Nodup := nodup_append_singleton
                                hWlINodup (fun h => hcNotIn (hqCAddr ▸ h))
                              have hReachX := (hPerI idxX hxIO hxIC).2.2.2.2 hxIOrigNz hxICur0
                              have hcOAddr : objs[idxC].addr = c :=
                                (hPerI idxC hidxCO hidxC).1.1.symm.trans hqCAddr
                              have hReachC : NonPersistReach objs objs[idx0].addr objs[idxC].addr :=
                                NonPersistReach.step hReachX ⟨objs[idxX], List.getElem_mem hxO, rfl,
                                  by rw [hcOAddr, ← hxICf]; exact List.getElem_mem hiLt⟩
                                  (hcOAddr ▸ hcEven) ⟨objs[idxC], List.getElem_mem hidxCO, rfl,
                                    hCOrigNz⟩
                              have hsetNe : ∀ {k}, k ≠ idxC → (hk : k < curObjs'.length) →
                                  curObjs'[k]'hk = mis.curObjs[k]'(by simpa [curObjs'] using hk) :=
                                fun hne hk => List.getElem_set_ne (Ne.symm hne) hk
                              have hxIC' : idxX < curObjs'.length := by simp [curObjs', hxIC]
                              have hidxC' : idxC < curObjs'.length := by simp [curObjs', hidxC]
                              have hsetC : curObjs'[idxC]'hidxC' = mis.curObjs[idxC].withRc 0#32 :=
                                by simp [curObjs']
                              have hcfX :
                                  curObjs'[idxX].childFields = mis.curObjs[idxX].childFields := by
                                rw [hsetNe hcNeXIdx.symm hxIC']
                              refine ⟨by simp [curObjs', hlenI], hPreI2, hRemI, hmI2',
                                lcnfHeapClosed_set_withRc hClosedI hidxC 0#32,
                                by dsimp only [stI2, stI1, RtC0State.withWorkBuf,
                                    RtC0State.withPersistInc, RtC0State.withPersist]
                                   rw [List.length_append, List.length_singleton]
                                   change mis.wl.length + 1 ≤ mis.st.workCap; omega,
                                hNodupWl', hTakeI2, ?_, Or.inl hUnmarked, ?_, ?_, ?_⟩
                              · refine ⟨hxIO, hxIC', hcfX ▸ hiLt, hxIOrigNz,
                                  by rw [hsetNe hcNeXIdx.symm hxIC', hxICur0], fun hin => by
                                    rcases List.mem_append.mp hin with h1 | h2
                                    · exact hxINotIn (hsetNe hcNeXIdx.symm hxIC' ▸ h1)
                                    · exact hcNeX (hqCAddr.trans
                                        (List.mem_singleton.mp h2).symm |>.trans
                                        (by rw [hsetNe hcNeXIdx.symm hxIC'])),
                                  fun j hj hjev => ?_⟩
                                dsimp only at hj
                                have hjI : j < mis.curObjs[idxX].childFields.length := by omega
                                have hjEq : curObjs'[idxX].childFields[j]'(hcfX ▸ hjI) =
                                    mis.curObjs[idxX].childFields[j] := by simp [hcfX]
                                rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjOld | rfl
                                · obtain ⟨q, hqM, hqA, hq0⟩ := hPrefixX j hjOld (hjEq ▸ hjev)
                                  by_cases hqc : q = mis.curObjs[idxC]
                                  · subst hqc; exact ⟨curObjs'[idxC], List.getElem_mem hidxC',
                                      by rw [hsetC, hjEq, ← hqA]; rfl, by rw [hsetC]; rfl⟩
                                  · obtain ⟨jq, hjq, rfl⟩ := List.mem_iff_getElem.mp hqM
                                    have hjq' : jq < curObjs'.length := by simp [curObjs', hjq]
                                    have hse := hsetNe (fun h => hqc (by subst h; rfl)) hjq'
                                    exact ⟨curObjs'[jq], List.getElem_mem hjq',
                                      by rw [hse, hjEq]; exact hqA, by rw [hse]; exact hq0⟩
                                · exact ⟨curObjs'[idxC], List.getElem_mem hidxC',
                                    by simp only [hsetC, LcnfObj.withRc, hcfX]; exact hqCAddr,
                                    by rw [hsetC]; rfl⟩
                              · intro k hk hk'
                                rcases hPerI k hk (by simpa [curObjs'] using hk') with
                                  ⟨hs, hwfK, hrtK, hrcK, hnrK⟩
                                by_cases hkEq : k = idxC
                                · subst hkEq; rw [hsetC]
                                  exact ⟨SameNonRc.withRc_r hs 0#32, objWf_withRc_zero hwfK,
                                    fun _ => rfl, Or.inr rfl, fun _ _ => hReachC⟩
                                · rw [hsetNe hkEq hk']; exact ⟨hs, hwfK, hrtK, hrcK, hnrK⟩
                              · intro a ha; rcases List.mem_append.mp ha with haOld | haNew
                                · obtain ⟨k, hkO, hkC, had, hnz, h0⟩ := hWlIMem a haOld
                                  have hkC' : k < curObjs'.length := by simpa [curObjs'] using hkC
                                  have hse := hsetNe (fun heq => by subst heq; exact hCRc0 h0) hkC'
                                  exact ⟨k, hkO, hkC', had, hnz, by rw [hse]; exact h0⟩
                                · rw [List.mem_singleton.mp haNew]
                                  exact ⟨idxC, hidxCO, hidxC', hcOAddr, hCOrigNz,
                                    by rw [hsetC]; rfl⟩
                              · intro k hk hk' hneX hnz hc0 hnotin f hf hev
                                have hkI : k < mis.curObjs.length := by simpa [curObjs'] using hk'
                                have hse := hsetNe (fun heq => by
                                  subst heq; apply hnotin; rw [hsetC]
                                  exact hqCAddr ▸ List.mem_append_right _
                                    (List.mem_singleton.mpr rfl)) hk'
                                rw [hse] at hc0 hf hnotin
                                obtain ⟨q, hqM, hqA, hq0⟩ := hClosedOthersI k hk hkI hneX hnz hc0
                                  (fun h => hnotin (List.mem_append_left [c] h)) f hf hev
                                obtain ⟨jq, hjq, rfl⟩ := List.mem_iff_getElem.mp hqM
                                by_cases jqEq : jq = idxC
                                · subst jqEq; exact False.elim (hCRc0 hq0)
                                · have hjq' : jq < curObjs'.length := by simp [curObjs', hjq]
                                  have hqEq := hsetNe jqEq hjq'
                                  exact ⟨curObjs'[jq], List.getElem_mem hjq',
                                    by rw [hqEq]; exact hqA, by rw [hqEq]; exact hq0⟩
                          · have hCRc0 : mis.curObjs[idxC].rc = 0#32 := by
                              erw [hdr_rc hwfC] at hc; exact bv64_ofNat_eq_zero_iff.mp hc
                            exact hJoin2 ⟨mis.st, mis.curObjs, mis.wl, mis.i + 1⟩ mI
                              ⟨rfl, mark_skip_inv hAllI hxIC hiLt (fun _ =>
                                ⟨mis.curObjs[idxC], List.getElem_mem hidxC, hqCAddr, hCRc0⟩)⟩
                      · exact hJoin ⟨mis.st, mis.curObjs, mis.wl, mis.i + 1⟩ mI
                          ⟨rfl, mark_skip_inv hAllI hxIC hiLt (fun h => False.elim (hc h))⟩
                  · have hiEq : mis.i = mis.curObjs[idxX].childFields.length := by omega
                    refine wp_jnz_false (by
                      cases h : (BitVec.ofNat 64 mis.i).ult
                          (BitVec.ofNat 64 mis.curObjs[idxX].childFields.length)
                      · rfl
                      · exact absurd (hUltIff.mp h) hiLt) ?_
                    c0_hsteps!
                    have hInvNext : MarkInv rt objs[idx0].addr objs st R
                        ⟨mis.st, mis.curObjs, mis.wl⟩ mI :=
                      ⟨hlenI, hPreI, hRemI, hmI, hClosedI, hWlICap, hWlINodup, hWlITake,
                        hPerI, hWlIMem, fun k hk hk' hnz hc0 hnotin f hf hev => by
                          by_cases hkX : k = idxX
                          · subst hkX; obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hf
                            exact hPrefixX j (hiEq ▸ hj) hev
                          · exact hClosedOthersI k hk hk' hkX hnz hc0 hnotin f hf hev⟩
                    refine hIH ⟨mis.st, mis.curObjs, mis.wl⟩ mI ?_ hInvNext
                    have hle : mis.wl.length ≤ objs.length :=
                      nodup_addr_length_le hWlINodup fun a ha => by
                        obtain ⟨k, hkO, _, had, _, _⟩ := hWlIMem a ha
                        exact ⟨objs[k], List.getElem_mem hkO, had⟩
                    dsimp only [markMeasure, u0, w0] at hMeasI ⊢
                    rcases hMeasI with huLt | ⟨huEq, hwLe⟩
                    · have hm1 := Nat.mul_le_mul_left (objs.length + 1) (Nat.succ_le_of_lt huLt)
                      rw [Nat.mul_succ] at hm1; omega
                    · rw [huEq]; omega
              · rw [← hxAddrC]; exact tag_dispatch_wp hxC hxWf (hm_heap_left hmL) _ (hK () mL rfl)
            · have hWl0 : ms.wl = [] := List.eq_nil_of_length_eq_zero (by omega)
              refine wp_jnz_false (by rw [hWl0, List.length_nil]; decide) ?_; c0_hsteps!
              exact hCont ms.st ms.curObjs mL hPreL hRemL
                (mark_rel_of_inv hWfO hClosedO hNodupO ⟨hlenC, hPreL, hRemL, hmL, hClosedC,
                  hWlCap, hWlNodup, hWlTake, hPer, hWlMem, hClosedOthers⟩ hWl0) hmL

/-- `rtC0Env` specialization of `lcnf_mark_persistent_wp`. -/
theorem rtC0Env_mark_persistent_wp : ∀ xs m Q X,
    lcnfMarkPersistentSpec xs m Q X → Func.wp rtC0Env lcnf_mark_persistent.body xs m Q X :=
  lcnf_mark_persistent_wp rtC0Env

/-! ## `lcnf_dec_ref_cold` Verification -/

private structure DecState where
  st : RtC0State
  curObjs : List LcnfObj
  wl : List (BitVec 64)

private def DecInv (rt root : BitVec 64) (objs : List LcnfObj) (st0 : RtC0State)
    (R : Mem 64 → Prop) (ds : DecState) (m : Mem 64) : Prop :=
  ds.curObjs.length ≤ objs.length ∧ ds.st.PreservesMeta st0 ∧ ds.st.rem = st0.rem ∧
  (rtC0Inv rt ds.st ⋆ lcnfHeap ds.curObjs ⋆ R) m ∧ lcnfHeapClosed ds.curObjs ∧
  (ds.curObjs.map LcnfObj.addr).Nodup ∧ ds.wl.length ≤ ds.st.workCap ∧ ds.wl.Nodup ∧
  ds.st.workBuf.take ds.wl.length = ds.wl ∧ (∀ o' ∈ ds.curObjs, o'.Wf) ∧
  (∀ p ∈ ds.curObjs, p.rc = 0#32 → ∀ f ∈ p.childFields, f &&& 1#64 = 0#64 →
    ∃ q ∈ ds.curObjs, q.addr = f ∧ q.rc = 0#32) ∧
  (∀ a ∈ ds.wl, ∃ o' ∈ ds.curObjs, o'.addr = a ∧ o'.rc = 1#32) ∧
  (∀ y ∈ ds.curObjs, 0 < y.rc.toInt →
    nonPersistRefs ds.curObjs y.addr + (if y.addr ∈ ds.wl then 1 else 0) ≤ y.rc.toNat) ∧
  (∀ o' ∈ ds.curObjs, ∃ ox ∈ objs, ox.addr = o'.addr ∧ SameNonRc ox o' ∧
    ((ox.rc = 0#32 ∧ o'.rc = 0#32) ∨
      (0 < ox.rc.toInt ∧ 0 < o'.rc.toInt ∧ o'.rc.toInt ≤ ox.rc.toInt))) ∧
  (∀ ox ∈ objs, ox.rc = 0#32 → ∃ o' ∈ ds.curObjs, o'.addr = ox.addr ∧ o'.rc = 0#32) ∧
  (∀ ox ∈ objs, 0 < ox.rc.toInt → ∀ o' ∈ ds.curObjs, o'.addr = ox.addr →
    o'.rc.toNat + (if ox.addr = root then 1 else 0) +
      nonPersistRefs (freedObjs objs ds.curObjs) ox.addr =
      ox.rc.toNat + (if ox.addr ∈ ds.wl then 1 else 0)) ∧
  (∀ f ∈ freedObjs objs ds.curObjs,
    f.rc.toNat = (if f.addr = root then 1 else 0) +
      nonPersistRefs (freedObjs objs ds.curObjs) f.addr ∧ NonPersistReach objs root f.addr) ∧
  (∀ a ∈ ds.wl, NonPersistReach objs root a)

private structure DecInnerState where
  st : RtC0State
  curObjs : List LcnfObj
  wl : List (BitVec 64)
  i : Nat

private def DecInnerInv (rt root : BitVec 64) (objs : List LcnfObj) (st0 : RtC0State)
    (R : Mem 64 → Prop) (idxX : Nat) (xAddr : BitVec 64) (len0 : Nat)
    (dis : DecInnerState) (m : Mem 64) : Prop :=
  dis.curObjs.length = len0 ∧ len0 ≤ objs.length ∧ dis.st.PreservesMeta st0 ∧
  dis.st.rem = st0.rem ∧ (rtC0Inv rt dis.st ⋆ lcnfHeap dis.curObjs ⋆ R) m ∧
  lcnfHeapClosed dis.curObjs ∧ (dis.curObjs.map LcnfObj.addr).Nodup ∧
  dis.wl.length ≤ dis.st.workCap ∧ dis.wl.Nodup ∧ dis.st.workBuf.take dis.wl.length = dis.wl ∧
  (∃ hx : idxX < dis.curObjs.length, ∃ hilen : dis.i ≤ dis.curObjs[idxX].childFields.length,
    dis.curObjs[idxX].addr = xAddr ∧ dis.curObjs[idxX].rc = 1#32 ∧ xAddr ∉ dis.wl ∧
    nonPersistRefs (dis.curObjs.eraseIdx idxX) xAddr = 0 ∧
    xAddr ∉ dis.curObjs[idxX].childFields ∧ NonPersistReach objs root xAddr) ∧
  (∀ o' ∈ dis.curObjs, o'.Wf) ∧
  (∀ p ∈ dis.curObjs, p.rc = 0#32 → ∀ f ∈ p.childFields, f &&& 1#64 = 0#64 →
    ∃ q ∈ dis.curObjs, q.addr = f ∧ q.rc = 0#32) ∧
  (∀ a ∈ dis.wl, ∃ o' ∈ dis.curObjs, o'.addr = a ∧ o'.rc = 1#32) ∧
  (∀ hx : idxX < dis.curObjs.length, ∀ y ∈ dis.curObjs, 0 < y.rc.toInt →
    nonPersistRefs (dis.curObjs.eraseIdx idxX) y.addr +
      List.count y.addr (dis.curObjs[idxX].childFields.drop dis.i) +
      (if y.addr ∈ dis.wl then 1 else 0) ≤ y.rc.toNat) ∧
  (∀ o' ∈ dis.curObjs, ∃ ox ∈ objs, ox.addr = o'.addr ∧ SameNonRc ox o' ∧
    ((ox.rc = 0#32 ∧ o'.rc = 0#32) ∨
      (0 < ox.rc.toInt ∧ 0 < o'.rc.toInt ∧ o'.rc.toInt ≤ ox.rc.toInt))) ∧
  (∀ ox ∈ objs, ox.rc = 0#32 → ∃ o' ∈ dis.curObjs, o'.addr = ox.addr ∧ o'.rc = 0#32) ∧
  (∀ hx : idxX < dis.curObjs.length, ∀ ox ∈ objs, 0 < ox.rc.toInt →
    ∀ o' ∈ dis.curObjs, o'.addr = ox.addr → o'.addr ≠ xAddr →
    o'.rc.toNat + (if ox.addr = root then 1 else 0) +
      nonPersistRefs (freedObjs objs dis.curObjs) ox.addr +
      List.count ox.addr (dis.curObjs[idxX].childFields.take dis.i) =
      ox.rc.toNat + (if ox.addr ∈ dis.wl then 1 else 0)) ∧
  (∀ ox ∈ objs, ox.addr = xAddr → ox.rc.toNat =
    (if xAddr = root then 1 else 0) + nonPersistRefs (freedObjs objs dis.curObjs) xAddr) ∧
  (∀ f ∈ freedObjs objs dis.curObjs,
    f.rc.toNat = (if f.addr = root then 1 else 0) +
      nonPersistRefs (freedObjs objs dis.curObjs) f.addr ∧ NonPersistReach objs root f.addr) ∧
  (∀ a ∈ dis.wl, NonPersistReach objs root a)

private theorem dec_rel_of_inv {rt root : BitVec 64} {objs : List LcnfObj} {st0 : RtC0State}
    {R : Mem 64 → Prop} {ds : DecState} {m : Mem 64}
    (hRoot : ∃ obj ∈ objs, obj.addr = root ∧ obj.rc = 1#32)
    (hNodupO : (objs.map LcnfObj.addr).Nodup)
    (hWfO : ∀ o ∈ objs, o.Wf) (hClosedO : lcnfHeapClosed objs)
    (hinv : DecInv rt root objs st0 R ds m) (hwl : ds.wl = []) :
    DecColdRel root objs ds.curObjs := by
  rcases hinv with ⟨_, _, _, _, hClosedC, _, _, _, _, hWfC, hPersC, _, hRcC, hRelO', hZero, hExactC,
    hFreeInv, _⟩
  refine ⟨hRoot, hWfO, hClosedO, hClosedC, fun o' ho' => ?_, hPersC,
    fun y hy hyPos => by simpa [hwl] using hRcC y hy hyPos, hZero,
    fun ox hoxM hoxPos => ⟨fun o' ho' ho'a => by
      simpa [Nat.add_assoc, hwl] using hExactC ox hoxM hoxPos o' ho' ho'a, hFreeInv ox⟩⟩
  obtain ⟨ox, hoxM, hoxa, ⟨ha, hcs, hot, htg, hfn, har, hcp, has, hsl, hfd, hsd, hlb⟩, hrc⟩ :=
    hRelO' o' ho'
  have hNeRoot : o'.addr ≠ root := fun hEq => by
    rcases hRoot with ⟨oroot, horM, horA, horRc⟩
    obtain rfl := nodup_addr_eq_of_mem hNodupO hoxM horM (hoxa.trans hEq |>.trans horA.symm)
    have hEx := hExactC ox hoxM (by simp [horRc]) o' ho' (hEq.trans horA.symm)
    rw [horA, hwl] at hEx; simp only [↓reduceIte, List.not_mem_nil, horRc] at hEx
    rcases hrc with ⟨h0, _⟩ | ⟨_, hp, _⟩
    · exact absurd (horRc.symm.trans h0) (by decide)
    · have hnz : o'.rc ≠ 0#32 := fun hz => by simp [hz] at hp
      have hrcPos : 0 < o'.rc.toNat :=
        Nat.pos_of_ne_zero fun h => hnz ((rc32_toNat_eq_zero_iff _).mp h)
      have h1 : (1#32 : BitVec 32).toNat = 1 := rfl; omega
  exact ⟨hWfC o' ho', hNeRoot, ox, hoxM, hoxa, hcs, hot, htg, hfn, har, hcp, has, hsl, hfd,
    hsd, hlb, hrc⟩

private theorem dec_erase_nonPersistRefs_set {curObjs : List LcnfObj}
    {idxX idxC : Nat} (hx : idxX < curObjs.length) (hc : idxC < curObjs.length)
    (hne : idxC ≠ idxX) {rc' : BitVec 32} (h1 : curObjs[idxC].rc ≠ 0#32) (h2 : rc' ≠ 0#32)
    (y : BitVec 64) : let curObjs' := curObjs.set idxC (curObjs[idxC].withRc rc')
    nonPersistRefs (curObjs'.eraseIdx idxX) y = nonPersistRefs (curObjs.eraseIdx idxX) y := by
  intro curObjs'; have hx' : idxX < curObjs'.length := by simp [curObjs', hx]
  have hf1 := nonPersistRefs_focus curObjs' hx' y; have hf2 := nonPersistRefs_focus curObjs hx y
  have hsame := nonPersistRefs_set_same_nz curObjs hc h1 h2 y
  have hxEq : curObjs'[idxX] = curObjs[idxX] := List.getElem_set_ne hne hx'
  rw [hf1, hf2, hxEq] at hsame; omega

private theorem dec_free_inv {rt root : BitVec 64} {objs : List LcnfObj} {st0 st' : RtC0State}
    {R : Mem 64 → Prop} {idxX : Nat} {xAddr : BitVec 64} {len0 : Nat}
    {dis : DecInnerState} {m m' : Mem 64} (hNodupO : (objs.map LcnfObj.addr).Nodup)
    (hWfO : ∀ o ∈ objs, o.Wf) (hInv : DecInnerInv rt root objs st0 R idxX xAddr len0 dis m)
    (hx : idxX < dis.curObjs.length) (hiEnd : dis.i = dis.curObjs[idxX].childFields.length)
    (hMeta' : st'.PreservesMeta dis.st) (hRem' : st'.rem = dis.st.rem)
    (hWb' : st'.workBuf = dis.st.workBuf)
    (hm' : (rtC0Inv rt st' ⋆ lcnfHeap (dis.curObjs.eraseIdx idxX) ⋆ R) m') :
    DecInv rt root objs st0 R ⟨st', dis.curObjs.eraseIdx idxX, dis.wl⟩ m' := by
  rcases hInv with ⟨hlenI, hlenLe, hPreI, hRemI, hmI, hClosedI, hNodupI, hWlCap, hWlNodup,
    hWlTake, ⟨_, hilen, hxA, hxRc1, hxNotWl, hNpX0, hXNotInCf, hReachX⟩, hWfI, hPersI, hWlMem,
    hRcI, hRelI, hZeroI, hExactI, hExactX, hFreeI, hWlReach⟩
  let nextObjs := dis.curObjs.eraseIdx idxX
  have hPre' := preservesMeta_trans hPreI hMeta'; have hRem'' := hRem'.trans hRemI
  have hWlCap' : dis.wl.length ≤ st'.workCap := by
    simpa [RtC0State.workCap, hMeta'.2.2.2.2.2.1] using hWlCap
  have hWbTake' : st'.workBuf.take dis.wl.length = dis.wl := hWb'.symm ▸ hWlTake
  have hLenNext : nextObjs.length ≤ objs.length := by
    have : nextObjs.length = dis.curObjs.length - 1 := List.length_eraseIdx_of_lt hx; omega
  have hXNotInNext : xAddr ∉ nextObjs.map LcnfObj.addr := by
    rw [map_addr_eraseIdx_mem hNodupI hx xAddr]; simp [hxA]
  have hNodupNext : (nextObjs.map LcnfObj.addr).Nodup := lcnfHeap_nodup_addrs (hm_heap_left hm')
  have hMemSub : ∀ q ∈ nextObjs, q ∈ dis.curObjs ∧ q.addr ≠ xAddr := fun q hq =>
    ⟨List.mem_of_mem_eraseIdx hq, fun heq => hXNotInNext (heq ▸ List.mem_map_of_mem hq)⟩
  have hBackMem : ∀ q ∈ dis.curObjs, q.addr ≠ xAddr → q ∈ nextObjs := fun q hq hne => by
    obtain ⟨q', hq'M, hq'A⟩ := List.mem_map.mp
      ((map_addr_eraseIdx_mem hNodupI hx q.addr).mpr ⟨List.mem_map_of_mem hq, hxA ▸ hne⟩)
    exact nodup_addr_eq_of_mem hNodupI (hMemSub q' hq'M).1 hq hq'A ▸ hq'M
  have hXNe0 : ∀ {q}, q ∈ dis.curObjs → q.rc = 0#32 → q.addr ≠ xAddr := fun hq h0 heq => by
    have := nodup_addr_eq_of_mem hNodupI hq (List.getElem_mem hx) (heq.trans hxA.symm)
    rw [this, hxRc1] at h0; exact absurd h0 (by decide)
  have hClosedNext : lcnfHeapClosed nextObjs := fun p hp f hf hev => by
    obtain ⟨hpI, _⟩ := hMemSub p hp; obtain ⟨q, hqI, hqA⟩ := hClosedI p hpI f hf hev
    refine ⟨q, hBackMem q hqI (fun hqx => ?_), hqA⟩
    by_cases hp0 : p.rc = 0#32
    · obtain ⟨q', hq'I, hq'A, hq'0⟩ := hPersI p hpI hp0 f hf hev
      exact hXNe0 hq'I hq'0 (hq'A.trans (hqA.symm.trans hqx))
    · exact nonPersistRefs_eq_zero_imp nextObjs xAddr hNpX0 p hp hp0 ((hqA.symm.trans hqx) ▸ hf)
  have hPersNext : ∀ p ∈ nextObjs, p.rc = 0#32 → ∀ f ∈ p.childFields,
      f &&& 1#64 = 0#64 → ∃ q ∈ nextObjs, q.addr = f ∧ q.rc = 0#32 := fun p hp hp0 f hf hev => by
    obtain ⟨q, hqI, hqA, hq0⟩ := hPersI p (hMemSub p hp).1 hp0 f hf hev
    exact ⟨q, hBackMem q hqI (hXNe0 hqI hq0), hqA, hq0⟩
  have hOxX : ∃ ox ∈ objs, ox.addr = xAddr ∧ ox.rc ≠ 0#32 ∧
      ox.childFields = dis.curObjs[idxX].childFields := by
    obtain ⟨ox, hoxM, hoxa, hsame, hrc⟩ := hRelI _ (List.getElem_mem hx)
    refine ⟨ox, hoxM, hoxa.trans hxA, ?_, (SameNonRc.childFields_eq hsame).symm⟩
    rcases hrc with ⟨_, hz⟩ | ⟨hpos, _⟩
    · exact absurd (hz.symm.trans hxRc1) (by decide)
    · exact fun hz => by simp [hz] at hpos
  have hDropErase :=
    nonPersistRefs_freedObjs_eraseIdx hNodupO hNodupI hx (by simpa [hxA] using hOxX)
  refine ⟨hLenNext, hPre', hRem'', hm', hClosedNext, hNodupNext, hWlCap', hWlNodup, hWbTake',
    fun o' ho' => hWfI o' (hMemSub o' ho').1, hPersNext, ?_, ?_,
    fun o' ho' => hRelI o' (hMemSub o' ho').1, ?_, ?_, ?_, hWlReach⟩
  · intro a ha; obtain ⟨o', ho'M, ho'A, ho'1⟩ := hWlMem a ha
    exact ⟨o', hBackMem o' ho'M (fun heq => hxNotWl ((ho'A.symm.trans heq) ▸ ha)), ho'A, ho'1⟩
  · intro y hy hyPos; have hyI := hRcI hx y (hMemSub y hy).1 hyPos
    rwa [List.drop_of_length_le (by omega), List.count_nil, Nat.add_zero] at hyI
  · intro ox hoxM hox0; obtain ⟨o', ho'M, ho'A, ho'0⟩ := hZeroI ox hoxM hox0
    exact ⟨o', hBackMem o' ho'M (hXNe0 ho'M ho'0), ho'A, ho'0⟩
  · intro ox hoxM hoxPos o' ho' ho'A; obtain ⟨ho'I, ho'Ne⟩ := hMemSub o' ho'
    have hEx := hExactI hx ox hoxM hoxPos o' ho'I ho'A ho'Ne; dsimp only at hEx ⊢
    rw [hiEnd, List.take_length] at hEx; rw [hDropErase ox.addr]; omega
  · intro f hf; simp only [freedObjs, List.mem_filter, Bool.not_eq_true'] at hf
    have hfW := hf.1; rw [hDropErase f.addr]
    by_cases hfEq : f.addr = xAddr
    · rw [List.count_eq_zero.mpr (hfEq ▸ hXNotInCf), Nat.add_zero, hfEq]
      exact ⟨hExactX f hfW hfEq, hfEq ▸ hReachX⟩
    · have hfOld : f ∈ freedObjs objs dis.curObjs := by
        simp only [freedObjs, List.mem_filter, Bool.not_eq_true'] at hf ⊢; refine ⟨hfW, ?_⟩
        cases hC : (dis.curObjs.map LcnfObj.addr).contains f.addr
        · rfl
        · have hfNext : (nextObjs.map LcnfObj.addr).contains f.addr = true :=
            List.contains_iff_mem.mpr ((map_addr_eraseIdx_mem hNodupI hx f.addr).mpr
              ⟨List.contains_iff_mem.mp hC, hxA ▸ hfEq⟩)
          exact absurd (hfNext ▸ hf.2) (by decide)
      have hfNotCf : f.addr ∉ dis.curObjs[idxX].childFields := fun hin => by
        obtain ⟨q, hqI, hqA⟩ :=
          hClosedI _ (List.getElem_mem hx) f.addr hin (objWf_addr_even (hWfO f hfW))
        simp only [freedObjs, List.mem_filter, Bool.not_eq_true'] at hfOld
        have hmem : (dis.curObjs.map LcnfObj.addr).contains f.addr = true :=
          List.contains_iff_mem.mpr (hqA ▸ List.mem_map_of_mem hqI)
        exact absurd (hmem ▸ hfOld.2) (by decide)
      rw [List.count_eq_zero.mpr hfNotCf, Nat.add_zero]; exact hFreeI f hfOld

private theorem dec_push_inv {rt root : BitVec 64} {objs : List LcnfObj} {st0 : RtC0State}
    {R : Mem 64 → Prop} {idxX idxC : Nat} {xAddr c : BitVec 64} {len0 : Nat}
    {dis : DecInnerState} {m : Mem 64} (hCap : objs.length ≤ st0.workCap)
    (hInv : DecInnerInv rt root objs st0 R idxX xAddr len0 dis m)
    (hx : idxX < dis.curObjs.length) (hiLt : dis.i < dis.curObjs[idxX].childFields.length)
    (hcMem : idxC < dis.curObjs.length) (hcAddr : dis.curObjs[idxC].addr = c)
    (hcCf : dis.curObjs[idxX].childFields[dis.i] = c) (hcEven : c &&& 1#64 = 0#64)
    (hcRc1 : dis.curObjs[idxC].rc = 1#32) : c ∉ dis.wl ∧ dis.wl.length < dis.st.workCap ∧
    (∀ (wb : List (BitVec 64)) (hlen : wb.length = dis.st.hdr.s_work_cap.toNat) (m' : Mem 64),
      wb = dis.st.workBuf.set dis.wl.length c →
      (rtC0Inv rt (RtC0State.withWorkBuf dis.st wb hlen) ⋆ lcnfHeap dis.curObjs ⋆ R) m' →
      DecInnerInv rt root objs st0 R idxX xAddr len0
        ⟨RtC0State.withWorkBuf dis.st wb hlen, dis.curObjs, dis.wl ++ [c], dis.i + 1⟩ m') := by
  rcases hInv with ⟨hlenI, hlenLe, hPreI, hRemI, hmI, hClosedI, hNodupI, hWlCap, hWlNodup,
    hWlTake, ⟨_, _, hxA, hxRc1, hxNotWl, hNpX0, hXNotInCf, hReachX⟩, hWfI, hPersI, hWlMem,
    hRcI, hRelI, hZeroI, hExactI, hExactX, hFreeI, hWlReach⟩
  have hcNeX : c ≠ xAddr := fun heq => hXNotInCf (heq ▸ hcCf ▸ List.getElem_mem hiLt)
  have hcNotIn : c ∉ dis.wl := fun hin => by
    have hInDrop : c ∈ dis.curObjs[idxX].childFields.drop dis.i := by
      have h0 : 0 < (dis.curObjs[idxX].childFields.drop dis.i).length := by simp; omega
      have : (dis.curObjs[idxX].childFields.drop dis.i)[0] = c := by simpa using hcCf
      exact this ▸ List.getElem_mem h0
    have hCntPos : 1 ≤ List.count c (dis.curObjs[idxX].childFields.drop dis.i) :=
      Nat.succ_le_of_lt (List.count_pos_iff.mpr hInDrop)
    have hRc := hRcI hx dis.curObjs[idxC] (List.getElem_mem hcMem) (by simp [hcRc1])
    simp only [hcAddr, hin, ↓reduceIte, hcRc1] at hRc
    have h1 : (1#32 : BitVec 32).toNat = 1 := rfl; omega
  have hCapLt : dis.wl.length < dis.st.workCap :=
    work_push_lt_cap hWlNodup (hxA ▸ hxNotWl) hcNotIn hcNeX
      ⟨dis.curObjs[idxX], List.getElem_mem hx, hxA⟩
      ⟨dis.curObjs[idxC], List.getElem_mem hcMem, hcAddr⟩
      (fun a ha => by obtain ⟨o', ho'M, ho'A, _⟩ := hWlMem a ha; exact ⟨o', ho'M, ho'A⟩)
      (by simpa [RtC0State.workCap, hPreI.2.2.2.2.2.1] using Nat.le_trans (hlenI ▸ hlenLe) hCap)
  refine ⟨hcNotIn, hCapLt, fun wb hlen m' hwb hm' => ?_⟩
  let st' := RtC0State.withWorkBuf dis.st wb hlen
  have hIdxWork : dis.wl.length < dis.st.workBuf.length := by rw [dis.st.workLen]; exact hCapLt
  have hPre' : st'.PreservesMeta st0 := preservesMeta_trans hPreI
    (by simp [st', RtC0State.withWorkBuf, RtC0State.PreservesMeta])
  have hTake' : st'.workBuf.take (dis.wl ++ [c]).length = dis.wl ++ [c] := by
    rw [List.length_append, List.length_singleton]
    change wb.take (dis.wl.length + 1) = dis.wl ++ [c]
    rw [hwb]; exact workBuf_take_set dis.st.workBuf hIdxWork c dis.wl hWlTake
  have hNodupWl' : (dis.wl ++ [c]).Nodup := nodup_append_singleton hWlNodup hcNotIn
  have hReachC : NonPersistReach objs root c := by
    obtain ⟨oxX, hoxXM, hoxXA, hsameX, _⟩ := hRelI _ (List.getElem_mem hx)
    obtain ⟨oxC, hoxCM, hoxCA, _, hrcC⟩ := hRelI _ (List.getElem_mem hcMem)
    have hoxCNz : oxC.rc ≠ 0#32 := by
      rcases hrcC with ⟨_, hz⟩ | ⟨hpos, _⟩
      · exact absurd (hz.symm.trans hcRc1) (by decide)
      · exact fun hz => by simp [hz] at hpos
    exact NonPersistReach.step hReachX ⟨oxX, hoxXM, hoxXA.trans hxA, by
        rw [← SameNonRc.childFields_eq hsameX]; exact hcCf ▸ List.getElem_mem hiLt⟩
      hcEven ⟨oxC, hoxCM, hoxCA.trans hcAddr, hoxCNz⟩
  refine ⟨hlenI, hlenLe, hPre', hRemI, hm', hClosedI, hNodupI,
    by simpa [st', RtC0State.withWorkBuf, RtC0State.workCap] using Nat.succ_le_of_lt hCapLt,
    hNodupWl', hTake',
    ⟨hx, by dsimp only; omega, hxA, hxRc1, fun hin => by
      simp at hin; rcases hin with h | h; exact hxNotWl h; exact hcNeX h.symm,
      hNpX0, hXNotInCf, hReachX⟩, hWfI, hPersI, ?_, ?_, hRelI, hZeroI, ?_, hExactX, hFreeI, ?_⟩
  · intro a ha; simp only [List.mem_append, List.mem_singleton] at ha; rcases ha with h | rfl
    · exact hWlMem a h
    · exact ⟨dis.curObjs[idxC], List.getElem_mem hcMem, hcAddr, hcRc1⟩
  · intro hx' y hy hyPos; have hyI := hRcI hx y hy hyPos
    have hCnt := count_drop_succ y.addr dis.curObjs[idxX].childFields hiLt
    rw [hcCf] at hCnt; rw [mem_append_singleton_ite hcNotIn y.addr]; dsimp only; omega
  · intro hx' ox hoxM hoxPos o' ho' ho'A ho'Ne
    have hEx := hExactI hx ox hoxM hoxPos o' ho' ho'A ho'Ne
    have hCnt := count_take_succ ox.addr dis.curObjs[idxX].childFields hiLt
    rw [hcCf] at hCnt; rw [mem_append_singleton_ite hcNotIn ox.addr]; dsimp only; omega
  · intro a ha; simp only [List.mem_append, List.mem_singleton] at ha; rcases ha with h | rfl
    · exact hWlReach a h
    · exact hReachC

private theorem dec_skip_inv {rt root : BitVec 64} {objs : List LcnfObj} {st0 : RtC0State}
    {R : Mem 64 → Prop} {idxX : Nat} {xAddr c : BitVec 64} {len0 : Nat}
    {dis : DecInnerState} {m : Mem 64}
    (hInv : DecInnerInv rt root objs st0 R idxX xAddr len0 dis m)
    (hx : idxX < dis.curObjs.length) (hiLt : dis.i < dis.curObjs[idxX].childFields.length)
    (hcCf : dis.curObjs[idxX].childFields[dis.i] = c)
    (hYNeC : ∀ y ∈ dis.curObjs, 0 < y.rc.toInt → y.addr ≠ c)
    (hOxNeC : ∀ ox ∈ objs, 0 < ox.rc.toInt → ox.addr ≠ c) :
    DecInnerInv rt root objs st0 R idxX xAddr len0 ⟨dis.st, dis.curObjs, dis.wl, dis.i + 1⟩ m := by
  rcases hInv with ⟨hlenI, hlenLe, hPreI, hRemI, hmI, hClosedI, hNodupI, hWlCap, hWlNodup,
    hWlTake, ⟨_, _, hxA, hxRc1, hxNotWl, hNpX0, hXNotInCf, hReachX⟩, hWfI, hPersI, hWlMem,
    hRcI, hRelI, hZeroI, hExactI, hExactX, hFreeI, hWlReach⟩
  refine ⟨hlenI, hlenLe, hPreI, hRemI, hmI, hClosedI, hNodupI, hWlCap, hWlNodup, hWlTake,
    ⟨hx, by dsimp only; omega, hxA, hxRc1, hxNotWl, hNpX0, hXNotInCf, hReachX⟩,
    hWfI, hPersI, hWlMem, ?_, hRelI, hZeroI, ?_, hExactX, hFreeI, hWlReach⟩
  · intro _ y hy hyPos; have := hRcI hx y hy hyPos
    have hCnt := count_drop_succ y.addr dis.curObjs[idxX].childFields hiLt
    rw [hcCf] at hCnt; simp only [hYNeC y hy hyPos, ↓reduceIte] at hCnt; dsimp only; omega
  · intro _ ox hoxM hoxPos o' ho' ho'A ho'Ne; have := hExactI hx ox hoxM hoxPos o' ho' ho'A ho'Ne
    have hCnt := count_take_succ ox.addr dis.curObjs[idxX].childFields hiLt
    rw [hcCf] at hCnt; simp only [hOxNeC ox hoxM hoxPos, ↓reduceIte] at hCnt; dsimp only; omega

private theorem dec_sub1_inv {rt root : BitVec 64} {objs : List LcnfObj} {st0 : RtC0State}
    {R : Mem 64 → Prop} {idxX idxC : Nat} {xAddr c : BitVec 64} {len0 : Nat}
    {dis : DecInnerState} {m m' : Mem 64}
    (hInv : DecInnerInv rt root objs st0 R idxX xAddr len0 dis m)
    (hx : idxX < dis.curObjs.length) (hiLt : dis.i < dis.curObjs[idxX].childFields.length)
    (hcMem : idxC < dis.curObjs.length) (hcAddr : dis.curObjs[idxC].addr = c)
    (hcCf : dis.curObjs[idxX].childFields[dis.i] = c) (hcGt1 : 1 < dis.curObjs[idxC].rc.toNat)
    (hm' : (rtC0Inv rt dis.st ⋆ lcnfHeap (dis.curObjs.set idxC
      (dis.curObjs[idxC].withRc (dis.curObjs[idxC].rc - 1#32))) ⋆ R) m') :
    DecInnerInv rt root objs st0 R idxX xAddr len0
      ⟨dis.st, dis.curObjs.set idxC (dis.curObjs[idxC].withRc (dis.curObjs[idxC].rc - 1#32)),
      dis.wl, dis.i + 1⟩ m' := by
  rcases hInv with ⟨hlenI, hlenLe, hPreI, hRemI, hmI, hClosedI, hNodupI, hWlCap, hWlNodup,
    hWlTake, ⟨_, hilen, hxA, hxRc1, hxNotWl, hNpX0, hXNotInCf, hReachX⟩, hWfI, hPersI,
    hWlMem, hRcI, hRelI, hZeroI, hExactI, hExactX, hFreeI, hWlReach⟩
  let rc' := dis.curObjs[idxC].rc - 1#32
  let curObjs' := dis.curObjs.set idxC (dis.curObjs[idxC].withRc rc')
  have hwfC := hWfI _ (List.getElem_mem hcMem)
  have hCNeX : idxC ≠ idxX := fun h => by
    subst h; rw [hxRc1] at hcGt1; exact absurd hcGt1 (by decide)
  have hCNz : dis.curObjs[idxC].rc ≠ 0#32 := fun hz => by
    rw [hz] at hcGt1; exact absurd hcGt1 (by decide)
  have hRc'ToNat : rc'.toNat = dis.curObjs[idxC].rc.toNat - 1 := objRc_sub1_toNat hcGt1
  have hCToInt : dis.curObjs[idxC].rc.toInt = dis.curObjs[idxC].rc.toNat := by
    have hlt := objWf_rc_lt hwfC; simp [BitVec.toInt_eq_toNat_cond]; omega
  have hRc'Pos : 0 < rc'.toInt := by
    have hSub := objWf_rc_sub1_toInt hwfC hcGt1
    change 0 < (dis.curObjs[idxC].rc - 1#32).toInt; rw [hSub, hCToInt]; omega
  have hRc'Nz : rc' ≠ 0#32 := fun hz => by simp [hz] at hRc'Pos
  have hCNotInWl : c ∉ dis.wl := fun hin => by
    obtain ⟨o', ho'M, ho'A, ho'1⟩ := hWlMem c hin
    have := nodup_addr_eq_of_mem hNodupI ho'M (List.getElem_mem hcMem) (ho'A.trans hcAddr.symm)
    rw [← this, ho'1] at hcGt1; exact absurd hcGt1 (by decide)
  have hNodup' : (curObjs'.map LcnfObj.addr).Nodup := lcnfHeap_nodup_addrs (hm_heap_left hm')
  have hsetNe : ∀ {k}, k ≠ idxC → (hk : k < curObjs'.length) →
      curObjs'[k]'hk = dis.curObjs[k]'(by simpa [curObjs'] using hk) :=
    fun hne hk => List.getElem_set_ne (Ne.symm hne) hk
  have hsetC : curObjs'[idxC]'(by simp [curObjs', hcMem]) = dis.curObjs[idxC].withRc rc' := by
    simp [curObjs']
  have hPers' : ∀ p ∈ curObjs', p.rc = 0#32 → ∀ f ∈ p.childFields, f &&& 1#64 = 0#64 →
      ∃ q ∈ curObjs', q.addr = f ∧ q.rc = 0#32 := fun p hp hp0 f hf hev => by
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hp
    have hjNeC : j ≠ idxC := fun heq => by
      subst heq; simp [curObjs', LcnfObj.withRc] at hp0; exact hRc'Nz hp0
    rw [hsetNe hjNeC hj] at hp0 hf
    obtain ⟨q, hqI, hqA, hq0⟩ :=
      hPersI _ (List.getElem_mem (by simpa [curObjs'] using hj)) hp0 f hf hev
    obtain ⟨jq, hjq, rfl⟩ := List.mem_iff_getElem.mp hqI
    have hjq' : jq < curObjs'.length := by simp [curObjs', hjq]
    have hse := hsetNe (fun heq => by subst heq; exact hCNz hq0) hjq'
    exact ⟨curObjs'[jq], List.getElem_mem hjq', by rw [hse]; exact hqA, by rw [hse]; exact hq0⟩
  have hNpEraseEq := fun y => dec_erase_nonPersistRefs_set hx hcMem hCNeX hCNz hRc'Nz y
  have hFreeEq : freedObjs objs curObjs' = freedObjs objs dis.curObjs :=
    freedObjs_set_rc objs dis.curObjs hcMem rc'
  have hx' : idxX < curObjs'.length := by simp [curObjs', hx]
  refine ⟨by simp [hlenI], hlenLe, hPreI, hRemI, hm', lcnfHeapClosed_set_withRc hClosedI hcMem rc',
    hNodup', hWlCap, hWlNodup, hWlTake,
    ⟨hx', by dsimp only; rw [List.getElem_set_ne hCNeX]; omega,
      by dsimp only; rw [List.getElem_set_ne hCNeX]; exact hxA,
      by dsimp only; rw [List.getElem_set_ne hCNeX]; exact hxRc1, hxNotWl,
      by rw [hNpEraseEq]; exact hNpX0,
      by dsimp only; rw [List.getElem_set_ne hCNeX]; exact hXNotInCf,
      hReachX⟩, ?_, hPers', ?_, ?_, ?_, ?_, ?_,
    fun ox hoxM hoxA => by rw [hFreeEq]; exact hExactX ox hoxM hoxA,
    fun f hf => by rw [hFreeEq] at hf ⊢; exact hFreeI f hf, hWlReach⟩
  · intro o' ho'; obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ho'
    by_cases hjC : j = idxC
    · subst hjC; rw [hsetC]; exact lcnfObjWf_withRc hwfC (Int.le_of_lt hRc'Pos)
    · rw [hsetNe hjC hj]; exact hWfI _ (List.getElem_mem (by simpa [curObjs'] using hj))
  · intro a ha; obtain ⟨o', ho'M, ho'A, ho'1⟩ := hWlMem a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ho'M
    have hj' : j < curObjs'.length := by simpa [curObjs'] using hj
    have hse := hsetNe (fun heq => by
      subst heq; exact hCNotInWl ((ho'A.symm.trans hcAddr) ▸ ha)) hj'
    exact ⟨curObjs'[j], List.getElem_mem hj', by rw [hse]; exact ho'A, by rw [hse]; exact ho'1⟩
  · intro hx'' y hy hyPos; dsimp only at hyPos ⊢
    rw [hNpEraseEq y.addr, List.getElem_set_ne hCNeX]
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hy
    have hjI : j < dis.curObjs.length := by simpa [curObjs'] using hj
    have hCnt := count_drop_succ curObjs'[j].addr dis.curObjs[idxX].childFields hiLt
    by_cases hjC : j = idxC
    · subst hjC; have hy0 := hRcI hx dis.curObjs[j] (List.getElem_mem hjI) (by omega)
      have haEq : curObjs'[j].addr = c := by rw [hsetC]; exact hcAddr
      rw [haEq, hcCf] at hCnt; simp only [↓reduceIte] at hCnt
      simp only [List.getElem_set_self, LcnfObj.withRc] at hyPos ⊢; rw [hcAddr] at hy0 ⊢
      simp only [hCNotInWl, ↓reduceIte] at hy0 ⊢
      change nonPersistRefs (dis.curObjs.eraseIdx idxX) c +
        List.count c (dis.curObjs[idxX].childFields.drop (dis.i + 1)) + 0 ≤ rc'.toNat; omega
    · have hse := hsetNe hjC hj; rw [hse] at hyPos hCnt ⊢
      have hy0 := hRcI hx dis.curObjs[j] (List.getElem_mem hjI) hyPos
      have hneA : dis.curObjs[j].addr ≠ c :=
        fun h => hjC (nodup_addr_idx_eq hNodupI hjI hcMem (h.trans hcAddr.symm))
      rw [hcCf] at hCnt; simp only [hneA, ↓reduceIte] at hCnt; omega
  · intro o' ho'; obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ho'
    have hjI : j < dis.curObjs.length := by simpa [curObjs'] using hj
    obtain ⟨ox, hoxM, hoxa, hsame, hrc⟩ := hRelI _ (List.getElem_mem hjI)
    by_cases hjC : j = idxC
    · subst hjC; rw [hsetC]; refine ⟨ox, hoxM, hoxa, SameNonRc.withRc_r hsame rc', Or.inr ?_⟩
      rcases hrc with ⟨_, hz⟩ | ⟨hoxP, _, hle⟩
      · exact False.elim (hCNz hz)
      · have hSub := objWf_rc_sub1_toInt hwfC hcGt1
        exact ⟨hoxP, hRc'Pos, Int.le_trans
          (by change (dis.curObjs[j].rc - 1#32).toInt ≤ dis.curObjs[j].rc.toInt
              rw [hSub]; exact Int.sub_le_self _ (by decide)) hle⟩
    · rw [hsetNe hjC hj]; exact ⟨ox, hoxM, hoxa, hsame, hrc⟩
  · intro ox hoxM hox0; obtain ⟨o', ho'M, ho'A, ho'0⟩ := hZeroI ox hoxM hox0
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ho'M
    have hj' : j < curObjs'.length := by simpa [curObjs'] using hj
    have hse := hsetNe (fun heq => by subst heq; exact hCNz ho'0) hj'
    exact ⟨curObjs'[j], List.getElem_mem hj', by rw [hse]; exact ho'A, by rw [hse]; exact ho'0⟩
  · intro hx'' ox hoxM hoxPos o' ho' ho'A ho'Ne; dsimp only at ho' ho'A ho'Ne ⊢
    rw [hFreeEq, List.getElem_set_ne hCNeX]; obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ho'
    have hjI : j < dis.curObjs.length := by simpa [curObjs'] using hj
    have hCnt := count_take_succ ox.addr dis.curObjs[idxX].childFields hiLt; rw [hcCf] at hCnt
    by_cases hjC : j = idxC
    · subst hjC; rw [List.getElem_set_self] at ho'A ho'Ne ⊢
      have ho'A' : dis.curObjs[j].addr = ox.addr := ho'A
      have ho'Ne' : dis.curObjs[j].addr ≠ xAddr := ho'Ne
      have hEx := hExactI hx ox hoxM hoxPos dis.curObjs[j] (List.getElem_mem hjI) ho'A' ho'Ne'
      have hoxC : ox.addr = c := ho'A'.symm.trans hcAddr; rw [hoxC] at hCnt hEx ⊢
      simp only [LcnfObj.withRc]
      change rc'.toNat + (if c = root then 1 else 0) +
        nonPersistRefs (freedObjs objs dis.curObjs) c +
        List.count c (dis.curObjs[idxX].childFields.take (dis.i + 1)) =
        ox.rc.toNat + (if c ∈ dis.wl then 1 else 0)
      simp only [↓reduceIte] at hCnt; omega
    · have hse := hsetNe hjC hj; rw [hse] at ho'A ho'Ne ⊢
      have hEx := hExactI hx ox hoxM hoxPos dis.curObjs[j] (List.getElem_mem hjI) ho'A ho'Ne
      have hneC : ox.addr ≠ c :=
        fun h => hjC (nodup_addr_idx_eq hNodupI hjI hcMem (ho'A.trans (h.trans hcAddr.symm)))
      simp only [hneC, ↓reduceIte] at hCnt; omega

/-- Verified soundness proof for `lcnf_dec_ref_cold`. -/
theorem lcnf_dec_ref_cold_wp (Γ : Env) (hFree : ∀ xs m Q X, lcnfFreeObjSpec xs m Q X →
    Γ "lcnf_free_obj" [i64, i64] [] xs m Q X) : ∀ (xs : Tup Val lcnf_dec_ref_cold.as) (m : Mem 64)
    (Q : Post lcnf_dec_ref_cold.rs) (X : XPost),
    lcnfDecRefColdSpec xs m Q X → Func.wp Γ lcnf_dec_ref_cold.body xs m Q X := by
  rintro ⟨rt, o, ⟨⟩⟩ m Q X hspec; dsimp only [lcnf_dec_ref_cold, lcnf_dec_ref_cold_body, Func.wp]
  dsimp only [lcnfDecRefColdSpec] at hspec
  rcases hspec with ⟨hEven, st, objs, R, hCap, hm, ⟨obj0, ho0, had0, hrc0⟩, hWfO, hClosedO,
    hRcSound, hCont⟩
  have hNodupO := lcnfHeap_nodup_addrs (hm_heap_left hm)
  obtain ⟨idx0, hidx0, rfl⟩ := List.mem_iff_getElem.mp ho0; subst had0; c0_hsteps_nogrp
  · exfalso; exact workCap_ne_zero_of_lt hidx0 hCap (by
      have := congrArg BitVec.toNat hc
      simpa [RtC0State.withColdDecsInc, RtC0State.withColdDecs] using this)
  · let st1 := RtC0State.withColdDecsInc st
    have hWork0 : 0 < st1.workBuf.length := by rw [st1.workLen]; change 0 < st.workCap; omega
    have hmWork1 : (rtC0Inv rt st1 ⋆ (lcnfHeap objs ⋆ R)) m := by rw [sep_emp] at hm; exact hm
    refine head_wp_store rfl (by simp [st1, RtC0State.withColdDecsInc, RtC0State.withColdDecs])
      (rtC0Inv_store_work hWork0 objs[idx0].addr hmWork1) (fun m2 hm2 => ?_)
    let wb2 := st1.workBuf.set 0 objs[idx0].addr
    let st2 := RtC0State.withWorkBuf st1 wb2 (by simpa [wb2] using st1.workLen)
    have hm2' : (rtC0Inv rt st2 ⋆ lcnfHeap objs ⋆ R) m2 := by simpa [sep_assoc] using hm2
    refine wp_while_state1 (fun ds : DecState => BitVec.ofNat 64 ds.wl.length)
      (fun ds : DecState => ds.curObjs.length) (DecInv rt objs[idx0].addr objs st R)
      (fun J hJ => ?_) (fun J ds mL hInv hIH => ?_)
    · c0_hsteps!; refine hJ ⟨st2, objs, [objs[idx0].addr]⟩ m2 ?_
      have hPre1 : st1.PreservesMeta st := by
        simp [st1, RtC0State.withColdDecsInc, RtC0State.withColdDecs, RtC0State.PreservesMeta]
      have hPre2 : st2.PreservesMeta st := preservesMeta_trans hPre1
        (by simp [st2, RtC0State.withWorkBuf, RtC0State.PreservesMeta])
      have hTake : st2.workBuf.take 1 = [objs[idx0].addr] :=
        workBuf_init_take1 st1.workBuf hWork0 objs[idx0].addr
      refine ⟨Nat.le_refl _, hPre2, rfl, hm2', hClosedO, hNodupO,
        by dsimp only [st2, st1, RtC0State.withWorkBuf, RtC0State.withColdDecsInc,
          RtC0State.withColdDecs]; change 1 ≤ st.workCap; omega,
        by simp, hTake, hWfO, hRcSound.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro a ha; simp only [List.mem_singleton] at ha; subst ha
        exact ⟨objs[idx0], List.getElem_mem hidx0, rfl, hrc0⟩
      · intro y hy hyPos; simpa only [List.mem_singleton] using hRcSound.2 y hy hyPos
      · intro o' ho'; refine ⟨o', ho', rfl, SameNonRc.refl o', ?_⟩
        by_cases hz : o'.rc = 0#32
        · exact Or.inl ⟨hz, hz⟩
        · exact Or.inr ⟨objWf_rc_pos (hWfO o' ho') hz, objWf_rc_pos (hWfO o' ho') hz, Int.le_refl _⟩
      · intro ox hoxM hox0; exact ⟨ox, hoxM, rfl, hox0⟩
      · intro ox hoxM _ o' ho' ho'A; dsimp only at ho'
        obtain rfl := nodup_addr_eq_of_mem hNodupO ho' hoxM ho'A
        rw [freedObjs_self]; simp [nonPersistRefs]
      · intro f hf; rw [freedObjs_self] at hf; simp at hf
      · intro a ha; simp only [List.mem_singleton] at ha; subst ha
        exact NonPersistReach.refl ⟨objs[idx0], List.getElem_mem hidx0, rfl, by simp [hrc0]⟩
    · rcases hInv with ⟨hlenLe, hPreL, hRemL, hmL, hClosedL, hNodupL, hWlCap, hWlNodup, hWlTake,
        hWfL, hPersL, hWlMem, hRcL, hRelL, hZeroL, hExactL, hFreeL, hWlReach⟩
      have hWlLt64 : ds.wl.length < 2 ^ 64 := Nat.lt_of_le_of_lt hWlCap ds.st.hdr.s_work_cap.isLt
      c0_hstep
      by_cases hWlPos : 0 < ds.wl.length
      · refine wp_jnz_true (by erw [bv64_ugt_zero_iff ds.wl.length hWlLt64]; exact hWlPos) ?_
        have hWlNe : ds.wl ≠ [] := List.ne_nil_of_length_pos hWlPos; let sp' := ds.wl.length - 1
        let xAddr := ds.wl[sp']; let wl' := ds.wl.take sp'
        have hWlSplit : wl' ++ [xAddr] = ds.wl := nodup_take_last hWlNe
        have hXNotIn : xAddr ∉ wl' := mem_not_in_take_last hWlNe hWlNodup
        have hNodupWl' : wl'.Nodup := (List.nodup_append.mp (hWlSplit ▸ hWlNodup)).1
        have hTake' : ds.st.workBuf.take sp' = wl' := by
          calc ds.st.workBuf.take sp' = (ds.st.workBuf.take ds.wl.length).take sp' := by
                  rw [List.take_take, Nat.min_eq_left (by omega)]
            _ = wl' := by rw [hWlTake]
        have hXInWl : xAddr ∈ ds.wl := List.getElem_mem _
        obtain ⟨oxX, hxLM, hxLA, hxLRc1⟩ := hWlMem xAddr hXInWl
        obtain ⟨idxX, hxC, rfl⟩ := List.mem_iff_getElem.mp hxLM
        have hxWf := hWfL _ (List.getElem_mem hxC)
        have hxNz : ds.curObjs[idxX].rc ≠ 0#32 := by simp [hxLRc1]
        have hNpTot0 : nonPersistRefs ds.curObjs ds.curObjs[idxX].addr = 0 := by
          have := hRcL _ (List.getElem_mem hxC) (by simp [hxLRc1])
          simp only [hxLA ▸ hXInWl, ↓reduceIte, hxLRc1] at this
          have h1 : (1#32 : BitVec 32).toNat = 1 := rfl; omega
        have hNpErase0 : nonPersistRefs (ds.curObjs.eraseIdx idxX) ds.curObjs[idxX].addr = 0 := by
          have := nonPersistRefs_focus ds.curObjs hxC ds.curObjs[idxX].addr
          simp only [hxNz, ↓reduceIte] at this; omega
        have hXNotInCf := nonPersistRefs_eq_zero_imp ds.curObjs ds.curObjs[idxX].addr hNpTot0
          ds.curObjs[idxX] (List.getElem_mem hxC) hxNz
        have hSpWork : sp' < ds.st.workBuf.length := by
          rw [ds.st.workLen]; change sp' < ds.st.workCap; omega
        have hWorkAtSp : ds.st.workBuf[sp'] = ds.curObjs[idxX].addr :=
          (workBuf_pop_eq ds.st.workBuf ds.wl hWlTake (by rw [ds.st.workLen]; exact hWlCap)
            (by omega)).trans hxLA.symm
        c0_hsteps_nogrp; erw [bv64_sub1_mul8 hWlPos hWlLt64]
        rw [show (RtC0State.withColdDecs st (st.hdr.s_st_cold_decs + 1)).hdr.s_work =
            ds.st.hdr.s_work by simp [RtC0State.withColdDecs, hPreL.2.2.2.2.1]]
        have hloadWork : loadVal mL i64 (ds.st.hdr.s_work + BitVec.ofNat 64 (8 * sp')) =
            some ds.curObjs[idxX].addr := by
          simpa only [hWorkAtSp] using rtC0Inv_load_work hSpWork (by simpa [sep_assoc] using hmL)
        refine wp_load_of (v := ds.curObjs[idxX].addr) hloadWork ?_
        refine wp_load_of (v := ds.curObjs[idxX].header)
          (lcnfHeap_load_header hxC (hm_heap_left hmL)) ?_
        c0_hsteps_nogrp
        have hOfSub1 : BitVec.ofNat 64 ds.wl.length - 1#64 = BitVec.ofNat 64 sp' :=
          bv64_ofNat_sub1 hWlPos hWlLt64
        let len0 := ds.curObjs.length
        refine wp_join_state (fun _ : Unit =>
            (BitVec.ofNat 64 ds.curObjs[idxX].childFields.length,
              objFieldsOff ds.curObjs[idxX], ()))
          (fun _ m' => m' = mL) (fun _ _ m' hmEq => ?_) (fun K hK => ?_)
        · subst hmEq
          refine wp_while_state
            (fun dis : DecInnerState => (BitVec.ofNat 64 dis.wl.length, BitVec.ofNat 64 dis.i, ()))
            (fun dis : DecInnerState => ds.curObjs[idxX].childFields.length - dis.i)
            (DecInnerInv rt objs[idx0].addr objs st R idxX ds.curObjs[idxX].addr len0)
            (fun L hL => ?_) (fun L dis mI hInvI hIL => ?_)
          · c0_hsteps!; erw [hOfSub1]
            have hWl'Len : wl'.length = sp' := by dsimp [wl']; rw [List.length_take]; omega
            rw [← hWl'Len]; refine hL ⟨ds.st, ds.curObjs, wl', 0⟩ m' ?_
            refine ⟨rfl, hlenLe, hPreL, hRemL, hmL, hClosedL, hNodupL,
              by dsimp only; rw [hWl'Len]; omega, hNodupWl',
              by dsimp only; rw [hWl'Len]; exact hTake',
              ⟨hxC, by dsimp only; omega, rfl, hxLRc1, hxLA ▸ hXNotIn, hNpErase0, hXNotInCf,
                hWlReach _ (hxLA ▸ hXInWl)⟩, hWfL, hPersL, ?_, ?_, hRelL, hZeroL,
              ?_, ?_, hFreeL, ?_⟩
            · intro a ha; exact hWlMem a (hWlSplit ▸ List.mem_append_left [xAddr] ha)
            · intro hx' y hy hyPos; have hy0 := hRcL y hy hyPos
              have hFoc := nonPersistRefs_focus ds.curObjs hxC y.addr
              simp only [hxNz, ↓reduceIte] at hFoc; dsimp only at hyPos ⊢; rw [List.drop_zero]
              by_cases hyX : y.addr = ds.curObjs[idxX].addr
              · have hyW : y.addr ∈ ds.wl := (hyX.trans hxLA) ▸ hXInWl
                have hyW' : y.addr ∉ wl' := (hyX.trans hxLA) ▸ hXNotIn
                simp only [hyW, hyW', ↓reduceIte] at hy0 ⊢; omega
              · have hneX : y.addr ≠ xAddr := fun h => hyX (h.trans hxLA.symm)
                have hIte := hWlSplit ▸ mem_append_singleton_ite hXNotIn y.addr
                simp only [hneX, ↓reduceIte, Nat.add_zero] at hIte; rw [hIte] at hy0; omega
            · intro hx' ox hoxM hoxPos o' ho' ho'A ho'Ne
              have hEx := hExactL ox hoxM hoxPos o' ho' ho'A
              have hneX : ox.addr ≠ xAddr := fun heq => ho'Ne (ho'A.trans (heq.trans hxLA.symm))
              have hIte := hWlSplit ▸ mem_append_singleton_ite hXNotIn ox.addr
              simp only [hneX, ↓reduceIte, Nat.add_zero] at hIte
              simpa [List.take_zero, List.count_nil, Nat.add_zero, hIte] using hEx
            · intro ox hoxM hoxA
              have hoxPos : 0 < ox.rc.toInt := by
                obtain ⟨o0, ho0M, ho0A, hsame, hrc⟩ := hRelL ds.curObjs[idxX] (List.getElem_mem hxC)
                have := nodup_addr_eq_of_mem hNodupO hoxM ho0M (hoxA.trans ho0A.symm)
                rcases hrc with ⟨_, hz⟩ | ⟨hpos, _⟩
                · exact absurd (hz.symm.trans hxLRc1) (by decide)
                · exact this ▸ hpos
              have hEx := hExactL ox hoxM hoxPos ds.curObjs[idxX] (List.getElem_mem hxC) hoxA.symm
              rw [hoxA, hxLRc1] at hEx; simp only [hxLA ▸ hXInWl, ↓reduceIte] at hEx
              have h1 : (1#32 : BitVec 32).toNat = 1 := rfl; rw [h1] at hEx; dsimp only; omega
            · intro a ha; exact hWlReach a (hWlSplit ▸ List.mem_append_left [xAddr] ha)
          · have hAll := hInvI
            rcases hInvI with ⟨hlenI, hlenLeI, hPreI, hRemI, hmI, hClosedI, hNodupI,
              hWlICap, hWlINodup, hWlITake, ⟨hxI, hiLen, hxIA, hxIRc1, hxINotWl, hNpXI, hXNotCfI,
                hReachXI⟩, hWfI, hPersI, hWlIMem, hRcI, hRelI, hZeroI, hExactI, hExactXI, hFreeI,
              hWlReachI⟩
            have hwfXI := hWfI _ (List.getElem_mem hxI)
            have hiLt64 : dis.i < 2 ^ 64 := Nat.lt_of_le_of_lt hiLen (objWf_childFields_lt hwfXI)
            have hcfLenLt64 : dis.curObjs[idxX].childFields.length < 2 ^ 64 :=
              objWf_childFields_lt hwfXI
            have hxICf : dis.curObjs[idxX].childFields = ds.curObjs[idxX].childFields := by
              obtain ⟨oxX, _, hoxaX, hsameX, _⟩ := hRelI _ (List.getElem_mem hxI)
              obtain ⟨ox0, _, hoxa0, hsame0, _⟩ := hRelL _ (List.getElem_mem hxC)
              have := nodup_addr_eq_of_mem hNodupO ‹_› ‹_› (hoxaX.trans hxIA |>.trans hoxa0.symm)
              rw [SameNonRc.childFields_eq hsameX, this, SameNonRc.childFields_eq hsame0]
            have hWlILt64 : dis.wl.length < 2 ^ 64 :=
              Nat.lt_of_le_of_lt hWlICap dis.st.hdr.s_work_cap.isLt
            rw [← hxICf]; c0_hstep
            have hUltIff := bv64_ult_iff dis.i dis.curObjs[idxX].childFields.length
              hiLt64 hcfLenLt64
            by_cases hiLt : dis.i < dis.curObjs[idxX].childFields.length
            · refine wp_jnz_true (hUltIff.mpr hiLt) ?_
              let c := dis.curObjs[idxX].childFields[dis.i]; c0_hsteps_nogrp; erw [bv64_8_mul dis.i]
              have hloadC : loadVal mI i64 (dis.curObjs[idxX].addr +
                  objFieldsOff dis.curObjs[idxX] + BitVec.ofNat 64 (8 * dis.i)) = some c :=
                lcnfHeap_load_child hxI hwfXI (hm_heap_left hmI) hiLt
              have hxIOff : objFieldsOff dis.curObjs[idxX] = objFieldsOff ds.curObjs[idxX] := by
                obtain ⟨oxX, _, hoxaX, hsameX, _⟩ := hRelI _ (List.getElem_mem hxI)
                obtain ⟨ox0, _, hoxa0, hsame0, _⟩ := hRelL _ (List.getElem_mem hxC)
                have := nodup_addr_eq_of_mem hNodupO ‹_› ‹_› (hoxaX.trans hxIA |>.trans hoxa0.symm)
                simp [objFieldsOff, hsameX.2.2.2.1, this, hsame0.2.2.2.1]
              rw [hxIOff, hxIA] at hloadC
              refine wp_load_of (v := c) hloadC ?_
              refine wp_join_state1
                (fun disNext : DecInnerState => BitVec.ofNat 64 disNext.wl.length)
                (fun disNext mNext => disNext.i = dis.i + 1 ∧
                  DecInnerInv rt objs[idx0].addr objs st R idxX ds.curObjs[idxX].addr len0
                    disNext mNext)
                (fun Jjoin disNext mNext hJn => ?_) (fun Jjoin hJoin => ?_)
              · rcases hJn with ⟨hiNext, hInvNext⟩; c0_hsteps!
                erw [bv64_ofNat_add1 dis.i]; rw [← hiNext]
                exact hIL disNext mNext (by rw [hiNext, ← hxICf]; omega) hInvNext
              · c0_hsteps_nogrp
                · have hcEven : c &&& 1#64 = 0#64 := hc
                  obtain ⟨qC, hqCMem, hqCAddr⟩ := hClosedI _ (List.getElem_mem hxI) _
                    (List.getElem_mem hiLt) hcEven
                  obtain ⟨idxC, hidxC, rfl⟩ := List.mem_iff_getElem.mp hqCMem
                  have hwfC := hWfI _ (List.getElem_mem hidxC)
                  refine wp_load_of (v := dis.curObjs[idxC].header)
                    (hqCAddr ▸ lcnfHeap_load_header hidxC (hm_heap_left hmI)) ?_
                  c0_hsteps_nogrp
                  refine wp_join_state1 (fun disNext : DecInnerState =>
                      BitVec.ofNat 64 disNext.wl.length)
                    (fun disNext mNext => disNext.i = dis.i + 1 ∧
                      DecInnerInv rt objs[idx0].addr objs st R idxX ds.curObjs[idxX].addr len0
                        disNext mNext)
                    (fun Jjoin2 disNext mNext hJ2 => ?_) (fun Jjoin2 hJoin2 => ?_)
                  · c0_hsteps!; exact hJoin disNext mNext hJ2
                  · c0_hsteps_nogrp
                    · have hCRc1 : dis.curObjs[idxC].rc = 1#32 := bv64_ofNat_eq_one_iff.mp (by
                        first
                        | (erw [← hdr_rc hwfC]; assumption)
                        | (have h := ‹BitVec.ofNat 64
                              (dis.curObjs[idxC].header &&& 4294967295#64).toNat = 1#64›
                           erw [hdr_rc hwfC] at h; exact h))
                      obtain ⟨_, hWorkLtCap, _⟩ := dec_push_inv hCap hAll hxI hiLt hidxC hqCAddr
                        rfl hcEven hCRc1
                      exfalso; exact work_overflow_absurd hWorkLtCap hWlILt64 rfl
                        hPreI.2.2.2.2.2.1 (by simpa [RtC0State.withColdDecs] using hc)
                    · have hCRc1 : dis.curObjs[idxC].rc = 1#32 := bv64_ofNat_eq_one_iff.mp (by
                        first
                        | (erw [← hdr_rc hwfC]; assumption)
                        | (have h := ‹BitVec.ofNat 64
                              (dis.curObjs[idxC].header &&& 4294967295#64).toNat = 1#64›
                           erw [hdr_rc hwfC] at h; exact h))
                      obtain ⟨_, hWorkLtCap, hPush⟩ := dec_push_inv hCap hAll hxI hiLt hidxC hqCAddr
                        rfl hcEven hCRc1
                      have hIdxWork : dis.wl.length < dis.st.workBuf.length := by
                        rw [dis.st.workLen]; exact hWorkLtCap
                      rw [hPreL.2.2.2.2.1.symm.trans hPreI.2.2.2.2.1]
                      refine head_wp_store rfl (by erw [bv64_mul8_comm dis.wl.length]; rfl)
                        (rtC0Inv_store_work hIdxWork c (by simpa [sep_assoc] using hmI))
                        (fun mI2 hmI2 => ?_)
                      let wbI2 := dis.st.workBuf.set dis.wl.length c
                      let hlenI2 : wbI2.length = dis.st.hdr.s_work_cap.toNat := by
                        simpa [wbI2] using dis.st.workLen
                      c0_hsteps!; erw [bv64_ofNat_add1 dis.wl.length]
                      rw [← show (dis.wl ++ [c]).length = dis.wl.length + 1 by simp]
                      exact hJoin2 ⟨_, dis.curObjs, dis.wl ++ [c], dis.i + 1⟩ mI2
                        ⟨rfl, hPush wbI2 hlenI2 mI2 rfl (by simpa [sep_assoc] using hmI2)⟩
                    · have hCRc1 : dis.curObjs[idxC].rc ≠ 1#32 := fun h =>
                        hc (by erw [hdr_rc hwfC, h]; rfl)
                      erw [hdr_rc hwfC]
                      refine wp_join_state0 (α := DecInnerState)
                        (fun disNext mNext => disNext.i = dis.i + 1 ∧ disNext.wl = dis.wl ∧
                          DecInnerInv rt objs[idx0].addr objs st R idxX ds.curObjs[idxX].addr len0
                            disNext mNext)
                        (fun Jjoin3 disNext mNext hJ3 => ?_) (fun Jjoin3 hJoin3 => ?_)
                      · rcases hJ3 with ⟨hiN, hwlN, hInvN⟩; c0_hsteps!
                        rw [← hwlN]; exact hJoin2 disNext mNext ⟨hiN, hInvN⟩
                      · c0_hstep
                        have hlt64 : dis.curObjs[idxC].rc.toNat < 2 ^ 64 :=
                          Nat.lt_trans dis.curObjs[idxC].rc.isLt (by decide)
                        by_cases hCGt1 : 1 < dis.curObjs[idxC].rc.toNat
                        · refine wp_jnz_true
                            (by simp [BitVec.ult, Nat.mod_eq_of_lt hlt64, hCGt1]) ?_
                          c0_hstep; have hlt := objWf_rc_lt hwfC
                          refine wp_jnz_true (by simp [BitVec.ult, Nat.mod_eq_of_lt hlt64, hlt]) ?_
                          c0_hstep
                          refine head_wp_store (lcnfObjHeader_sub1_wf dis.curObjs[idxC] hwfC hCGt1)
                            rfl (hqCAddr ▸ lcnfHeap_store_rc hidxC (dis.curObjs[idxC].rc - 1#32)
                              (hm_heap_left hmI)) (fun mI1 hmI1 => ?_)
                          let curObjs' := dis.curObjs.set idxC
                            (dis.curObjs[idxC].withRc (dis.curObjs[idxC].rc - 1#32))
                          have hmI1' : (rtC0Inv rt dis.st ⋆ lcnfHeap curObjs' ⋆
                              R) mI1 := hm_heap_unleft hmI1
                          c0_hsteps!
                          exact hJoin3 ⟨dis.st, curObjs', dis.wl, dis.i + 1⟩ mI1
                            ⟨rfl, rfl, dec_sub1_inv hAll hxI hiLt hidxC hqCAddr rfl hCGt1 hmI1'⟩
                        · refine wp_jnz_false
                            (by simp [BitVec.ult, Nat.mod_eq_of_lt hlt64, hCGt1]) ?_
                          have hCRc0 : dis.curObjs[idxC].rc = 0#32 := (rc32_toNat_eq_zero_iff _).mp
                            (by have : dis.curObjs[idxC].rc.toNat ≠ 1 :=
                              fun h => hCRc1 ((rc32_toNat_eq_one_iff _).mp h); omega)
                          c0_hsteps!
                          refine hJoin3 ⟨dis.st, dis.curObjs, dis.wl, dis.i + 1⟩ mI ⟨rfl, rfl, ?_⟩
                          refine dec_skip_inv hAll hxI hiLt rfl (fun y hy hyPos heq => ?_)
                            (fun ox hox hoxPos heq => ?_)
                          · rw [nodup_addr_eq_of_mem hNodupI hy (List.getElem_mem hidxC)
                              (heq.trans hqCAddr.symm), hCRc0] at hyPos
                            exact absurd hyPos (by decide)
                          · obtain ⟨ox0, hox0M, hox0A, _, hrc0⟩ := hRelI _ (List.getElem_mem hidxC)
                            obtain rfl := nodup_addr_eq_of_mem hNodupO hox hox0M
                              (heq.trans (hqCAddr.symm.trans hox0A.symm))
                            rcases hrc0 with ⟨hz, _⟩ | ⟨_, hp, _⟩
                            · rw [hz] at hoxPos; exact absurd hoxPos (by decide)
                            · rw [hCRc0] at hp; exact absurd hp (by decide)
                · have hcEven : ¬c &&& 1#64 = 0#64 := hc
                  refine hJoin ⟨dis.st, dis.curObjs, dis.wl, dis.i + 1⟩ mI ⟨rfl, ?_⟩
                  exact dec_skip_inv hAll hxI hiLt rfl
                    (fun y hy _ heq => hcEven
                      ((show y.addr = c from heq) ▸ objWf_addr_even (hWfI y hy)))
                    (fun ox hox _ heq => hcEven
                      ((show ox.addr = c from heq) ▸ objWf_addr_even (hWfO ox hox)))
            · have hiEq : dis.i = dis.curObjs[idxX].childFields.length := by omega
              refine wp_jnz_false (by
                cases h : (BitVec.ofNat 64 dis.i).ult
                    (BitVec.ofNat 64 dis.curObjs[idxX].childFields.length)
                · rfl
                · exact absurd (hUltIff.mp h) hiLt) ?_
              have hmFocus : (rtC0Inv rt dis.st ⋆ freeObjLayout dis.curObjs[idxX].addr
                  dis.curObjs[idxX].totalBytes dis.curObjs[idxX].header ⋆
                  (lcnfHeap (dis.curObjs.eraseIdx idxX) ⋆ R)) mI := by
                have hf1 := hm_heap_left hmI
                rw [lcnfHeap_focus dis.curObjs hxI, ← lcnfHeap_eraseIdx] at hf1
                have hf2 : ((freeObjLayout dis.curObjs[idxX].addr dis.curObjs[idxX].totalBytes
                      dis.curObjs[idxX].header ⋆ lcnfHeap (dis.curObjs.eraseIdx idxX)) ⋆
                    (rtC0Inv rt dis.st ⋆ R)) mI :=
                  sep_mono (fun _ h => sep_mono (fun _ h0 =>
                    lcnfObjMem_to_freeObjLayout hwfXI h0) h) hf1
                exact sep_cast hf2 (by ac_rfl)
              rw [← hxIA]; simp only [wp]
              refine ⟨(fun _ m' => J (BitVec.ofNat 64 dis.wl.length, ()) m'), X,
                hFree (rt, dis.curObjs[idxX].addr, ()) mI _ X ?_,
                (fun _ _ hp => hp), (fun _ _ _ _ hx => hx)⟩
              simp only [lcnfFreeObjSpec, show (dis.curObjs[idxX].addr &&& 1#64 ≠ 0#64) = False by
                simp [objWf_addr_even hwfXI], ↓reduceIte]
              refine ⟨dis.st, dis.curObjs[idxX].header, dis.curObjs[idxX].totalBytes,
                lcnfHeap (dis.curObjs.eraseIdx idxX) ⋆ R, hwfXI.1, hwfXI.2.1,
                hwfXI.2.2.2.2.2.2.1, hwfXI.2.2.2.2.2.2.2.1, hwfXI.2.2.2.2.2.2.2.2.1, hmFocus,
                fun st' m' hM' hR' hW' hm' => hIH ⟨st', dis.curObjs.eraseIdx idxX, dis.wl⟩ m'
                  (by rw [List.length_eraseIdx_of_lt hxI, hlenI]
                      change len0 - 1 < ds.curObjs.length; omega)
                  (dec_free_inv hNodupO hWfO hAll hxI hiEq hM' hR' hW'
                    (by simpa only [sep_assoc] using hm'))⟩
        · exact tag_dispatch_wp hxC hxWf (hm_heap_left hmL) _ (hK () mL rfl)
      · have hWl0 : ds.wl = [] := List.eq_nil_of_length_eq_zero (by omega)
        refine wp_jnz_false (by rw [hWl0, List.length_nil]; decide) ?_; c0_hsteps!
        exact hCont ds.st ds.curObjs mL hPreL hRemL
          (dec_rel_of_inv ⟨objs[idx0], List.getElem_mem hidx0, rfl, hrc0⟩ hNodupO hWfO hClosedO
            ⟨hlenLe, hPreL, hRemL, hmL, hClosedL, hNodupL, hWlCap, hWlNodup, hWlTake, hWfL, hPersL,
              hWlMem, hRcL, hRelL, hZeroL, hExactL, hFreeL, hWlReach⟩ hWl0)
          hmL

/-- `rtC0Env` specialization of `lcnf_dec_ref_cold_wp`. -/
theorem rtC0Env_dec_ref_cold_wp : ∀ xs m Q X,
    lcnfDecRefColdSpec xs m Q X → Func.wp rtC0Env lcnf_dec_ref_cold.body xs m Q X :=
  lcnf_dec_ref_cold_wp rtC0Env rtC0Env_free_obj

/-! ## `ModuleOk` for Complete Phase R0 Runtime Module (`rtR0Mod`) -/

/-- Whole-module soundness proof for the Phase R0 runtime module `rtR0Mod` under `rtC0Env`. -/
theorem rtR0Mod_ok : ModuleOk rtC0Env rtR0Mod := by
  refine Module.moduleOk_of_checkAcyclic rtR0Mod_checkAcyclic rtR0Mod_wf ?_
  intro fn hfn xs m Q X hspec; dsimp only [rtC0Env, rtC0SpecEntries] at hspec
  simp only [rtR0Mod, rtR0_fns, List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl | rfl | rfl | rfl <;> (
    try simp (disch := decide) only [Env.ofTable_cons_ne] at hspec
    rw [Env.ofTable_cons_self] at hspec; dsimp only [SpecEntry.ofFn] at hspec)
  · exact lcnf_alloc_wp rtC0Env xs m Q X hspec
  · exact lcnf_free_obj_wp rtC0Env xs m Q X hspec
  · exact rtC0Env_dec_ref_cold_wp xs m Q X hspec
  · exact rtC0Env_mark_persistent_wp xs m Q X hspec
  · exact lcnf_clo_under_wp rtC0Env rtC0Env_alloc rtC0Env_free_obj xs m Q X hspec

end

end LeanQbe.T.LeanLCNF
