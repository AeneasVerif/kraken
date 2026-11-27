/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Bitblast.Proof.Tseitin1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.Bytes

/-!
# DIMACS Writer Correctness Proof (`Bitblast.Proof.Tseitin`)

Proves `bv_dimacs_write_wp`: the canonical `Γ`-parametric `Func.wp` specification
(`bvDimacsWriteSpec`) for `bv_dimacs_write_body`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Proof

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofKit
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Bitblast.Src LeanQbe.T.Examples.Bitblast.Src.Tseitin
open LeanQbe.T.Examples.Bitblast.Ref LeanQbe.T.Examples.Bitblast.Ref.Tseitin

@[local c0_load] private theorem c0_load_hdr_wb {h s R m} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i64 h = some s.work_base := load_hdr_work_base hm
@[local c0_load] private theorem c0_load_hdr_we {h s R m} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i64 (h + 8#64) = some s.work_end := load_hdr_work_end hm
@[local c0_load] private theorem c0_load_hdr_aig {h s R m} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i64 (h + 24#64) = some s.aig_ptr := load_hdr_aig_ptr hm
@[local c0_load] private theorem c0_load_hdr_marks {h s R m} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i64 (h + 64#64) = some s.marks_ptr := load_hdr_marks_ptr hm
@[local c0_load] private theorem c0_load_hdr_atoms {h s R m} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 96#64) = some s.num_atoms := load_hdr_num_atoms hm
@[local c0_load] private theorem c0_load_hdr_aiglen {h s R m} (hm : (bvHdrMem h s ⋆ R) m) :
    loadVal m i32 (h + 100#64) = some s.aig_len := load_hdr_aig_len hm
@[local c0_store] private theorem c0_store_hdr_ds {h s R m} (v : BitVec 64)
    (hm : (bvHdrMem h s ⋆ R) m) : storeOk m i64 (h + 72#64) ∧
      (bvHdrMem h { s with dimacs_start := v } ⋆ R) (storeMem m i64 (h + 72#64) v) :=
  store_hdr_dimacs_start v hm
@[local c0_store] private theorem c0_store_hdr_oom {h s R m} (v : BitVec 32)
    (hm : (bvHdrMem h s ⋆ R) m) : storeOk m i32 (h + 120#64) ∧
      (bvHdrMem h { s with oom := v } ⋆ R) (storeMem m i32 (h + 120#64) v) := store_hdr_oom v hm
@[local c0_store] private theorem c0_store_hdr_dl {h s R m} (v : BitVec 32)
    (hm : (bvHdrMem h s ⋆ R) m) : storeOk m i32 (h + 124#64) ∧
      (bvHdrMem h { s with dimacs_len := v } ⋆ R) (storeMem m i32 (h + 124#64) v) :=
  store_hdr_dimacs_len v hm

@[local c0_load] private theorem c0_load_bytes_u32 {base : BitVec 64} {i : BitVec 32}
    {bs R m} (hi : i.toNat < bs.length) (hlen : bs.length ≤ 2 ^ 64) (hm : (bytes base bs ⋆ R) m) :
    loadVal m i8 (base + i.setWidth 64) = some (BitVec.ofNat 8 (bs[i.toNat]'hi).toNat) := by
  rw [show base + i.setWidth 64 = base + BitVec.ofNat 64 i.toNat from
    congrArg _ (BitVec.eq_of_toNat_eq (by simp))]
  exact load_bytes_at hi hlen hm

@[local c0_load] private theorem c0_load_array64_u32_mul8 {a : BitVec 64} {i : BitVec 32}
    {xs : List (BitVec 64)} {R m} (h : (array64 a xs ⋆ R) m) (hi : i.toNat < xs.length) :
    loadVal m i64 (a + i.setWidth 64 * 8#64) = some (xs[i.toNat]'hi) := by
  have heq : i.setWidth 64 * 8#64 = BitVec.ofNat 64 (8 * i.toNat) := BitVec.eq_of_toNat_eq <| by
    have := i.isLt
    simp [BitVec.toNat_mul, Nat.mod_eq_of_lt (by omega : 8 * i.toNat < 2 ^ 64), Nat.mul_comm]
  rw [heq]; exact loadVal_array64 hi h

/-! ## 1. Pass-1 and Pass-2 WP Proofs -/

private theorem wp_maxUpdate (Γ : Env) (Q : Post [Ty.bool]) (X : XPost)
    (a b : Val i32) (k : Val i32 → Expr Val Cont [Ty.bool]) (m : Mem 64)
    (hk : wp Γ Q X (k (if b.toNat < a.toNat then a else b)) m) :
    wp Γ Q X (maxUpdate a b k) m := by
  unfold maxUpdate; c0_hsteps_nogrp
  refine wp_join_state1 (fun x : Val i32 => x)
    (fun x m' => m' = m ∧ x = if b.toNat < a.toNat then a else b)
    (fun _ _ _ ⟨hm', hx⟩ => hm' ▸ hx ▸ hk) fun _ hJ => ?_
  c0_hsteps_nogrp
  · exact hJ a m ⟨rfl, by simp [show b.toNat < a.toNat by c0_bv_omega [hc]]⟩
  · exact hJ b m ⟨rfl, by simp [show ¬ b.toNat < a.toNat by c0_bv_omega [hc]]⟩

private theorem bv32_if_lt_toNat (a b : BitVec 32) :
    (if a.toNat < b.toNat then b else a).toNat = max a.toNat b.toNat := by split <;> omega

private theorem idx32_toNat {g : Aig} {k : Nat} (hbd : g.A + 1 + g.nodes.size < bvDimacsBound)
    (hk : k < g.nodes.size) : (BitVec.ofNat 32 (g.A + 1 + k)).toNat = g.A + 1 + k := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold bvDimacsBound at hbd; omega)]

private theorem idx32_add1 {g : Aig} {k : Nat} (hbd : g.A + 1 + g.nodes.size < bvDimacsBound)
    (hk : k < g.nodes.size) :
    BitVec.ofNat 32 (g.A + 1 + k) + 1#32 = BitVec.ofNat 32 (g.A + 1 + (k + 1)) := by
  apply BitVec.eq_of_toNat_eq; unfold bvDimacsBound at hbd
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega : 1 < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega

private theorem mark_getD_true_of_bv {marks : List UInt8} {idx : BitVec 32} {n : Nat}
    {z : BitVec 32} (hz0 : z.toNat = 0) (hidx : idx.toNat = n) (hn : n < marks.length)
    (hne : (BitVec.ofNat 8 (marks[idx.toNat]'(by rw [hidx]; exact hn)).toNat).setWidth 32 ≠ z) :
    (marksToBool marks).getD n false = true := by
  have hnz : marks[n]'hn ≠ 0 := fun hz => hne <| BitVec.eq_of_toNat_eq <| by
    have h0 : (marks[idx.toNat]'(by rw [hidx]; exact hn)).toNat = 0 := by
      simp only [hidx]; rw [hz]; rfl
    rw [h0, hz0]; rfl
  rw [marksToBool_getD marks hn]; exact bne_iff_ne.mpr hnz

private theorem mark_getD_false_of_bv {marks : List UInt8} {idx : BitVec 32} {n : Nat}
    {z : BitVec 32} (hz0 : z.toNat = 0) (hidx : idx.toNat = n) (hn : n < marks.length)
    (heq : (BitVec.ofNat 8 (marks[idx.toNat]'(by rw [hidx]; exact hn)).toNat).setWidth 32 = z) :
    (marksToBool marks).getD n false = false := by
  have h0 : (marks[idx.toNat]'(by rw [hidx]; exact hn)).toNat = 0 := by
    have ht := congrArg BitVec.toNat heq
    have hlt := (marks[idx.toNat]'(by rw [hidx]; exact hn)).toNat_lt
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, hz0, Nat.mod_eq_of_lt hlt,
      Nat.mod_eq_of_lt (by omega : _ < 2 ^ 32)] at ht; exact ht
  simp only [hidx] at h0
  have hm0 : marks[n]'hn = 0 := UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (by simpa using h0))
  rw [marksToBool_getD marks hn, hm0]; rfl

private theorem bv64_cl2_toNat {dl l : Nat} (hdl : dl ≤ 10) (hl : l ≤ 12) :
    (BitVec.ofNat 64 dl + 2#64 + BitVec.ofNat 64 l + 2#64).toNat = dl + 2 + l + 2 := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : 2 < 2 ^ 64), Nat.mod_eq_of_lt (by omega : dl < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : dl + 2 < 2 ^ 64), Nat.mod_eq_of_lt (by omega : l < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : dl + 2 + l < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : dl + 2 + l + 2 < 2 ^ 64)]

private theorem bv64_cl3_toNat {dl l1 l2 : Nat} (hdl : dl ≤ 10) (hl1 : l1 ≤ 12) (hl2 : l2 ≤ 12) :
    (BitVec.ofNat 64 dl + 1#64 + BitVec.ofNat 64 l1 + BitVec.ofNat 64 l2 + 2#64).toNat =
      dl + 1 + l1 + l2 + 2 := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : 1 < 2 ^ 64), Nat.mod_eq_of_lt (by omega : 2 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : dl < 2 ^ 64), Nat.mod_eq_of_lt (by omega : dl + 1 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : l1 < 2 ^ 64), Nat.mod_eq_of_lt (by omega : dl + 1 + l1 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : l2 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : dl + 1 + l1 + l2 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : dl + 1 + l1 + l2 + 2 < 2 ^ 64)]

private theorem bv64_gate_bytes_toNat {bb : BitVec 64} {dl b1 b2 b3 b4 : Nat}
    (hfit : bb.toNat + (dl + 11 + b1 + b2 + b3 + b4 + 2 * dl) < 2 ^ 64)
    (hdl : dl ≤ 10) (hb1 : b1 ≤ 12) (hb2 : b2 ≤ 12) (hb3 : b3 ≤ 12) (hb4 : b4 ≤ 12) :
    (bb + (BitVec.ofNat 64 dl + 2#64 + BitVec.ofNat 64 b1 + 2#64) +
      (BitVec.ofNat 64 dl + 2#64 + BitVec.ofNat 64 b2 + 2#64) +
      (BitVec.ofNat 64 dl + 1#64 + BitVec.ofNat 64 b3 + BitVec.ofNat 64 b4 + 2#64)).toNat =
    bb.toNat + (dl + 11 + b1 + b2 + b3 + b4 + 2 * dl) := by
  have hc1 := bv64_cl2_toNat hdl hb1; have hc2 := bv64_cl2_toNat hdl hb2
  have hc3 := bv64_cl3_toNat hdl hb3 hb4
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, hc1, hc2, hc3,
    Nat.mod_eq_of_lt (by omega : _ < 2 ^ 64), Nat.mod_eq_of_lt (by omega : _ < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : _ < 2 ^ 64)]
  omega

private theorem bv64_shl2_toNat {d : Nat} (hd : d ≤ 10) :
    (BitVec.ofNat 64 d <<< (2 : Nat)).toNat = 4 * d := by
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : d < 2 ^ 64),
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega

private theorem bv64_shl1_toNat {d : Nat} (hd : d ≤ 10) :
    (BitVec.ofNat 64 d <<< (1 : Nat)).toNat = 2 * d := by
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : d < 2 ^ 64),
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega

private theorem bv64_ite_bytes_toNat {bb : BitVec 64} {d0 dc dt df : Nat}
    (hfit : bb.toNat + (4 * d0 + 4 * dc + 2 * dt + 2 * df + 26) < 2 ^ 64)
    (hd0 : d0 ≤ 10) (hdc : dc ≤ 10) (hdt : dt ≤ 10) (hdf : df ≤ 10) :
    (bb + (BitVec.ofNat 64 d0 <<< (2 : Nat)) + (BitVec.ofNat 64 dc <<< (2 : Nat)) +
      (BitVec.ofNat 64 dt <<< (1 : Nat)) + (BitVec.ofNat 64 df <<< (1 : Nat)) + 26#64).toNat =
      bb.toNat + (4 * d0 + 4 * dc + 2 * dt + 2 * df + 26) := by
  have h0 := bv64_shl2_toNat hd0; have hc := bv64_shl2_toNat hdc
  have ht := bv64_shl1_toNat hdt; have hf := bv64_shl1_toNat hdf
  simp only [BitVec.toNat_add, h0, hc, ht, hf, show (26#64 : BitVec 64).toNat = 26 from rfl]
  rw [Nat.mod_eq_of_lt (by omega : _ < 2 ^ 64), Nat.mod_eq_of_lt (by omega : _ < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : _ < 2 ^ 64), Nat.mod_eq_of_lt (by omega : _ < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : _ < 2 ^ 64)]
  omega

private theorem wp_pass1GateStep (Γ : Env) (hDecLen : HypDecLen Γ) (hLitBytes : HypLitBytes Γ)
    (Q : Post [Ty.bool]) (X : XPost) (c : CoiCtx) (R : Mem 64 → Prop) (m : Mem 64)
    (root : BitVec 32) (k : Nat) (hk : k < c.g.nodes.size)
    (mv nc : Val i32) (bb : Val i64) (idx : Val i32)
    (onDone : Val i32 → Val i32 → Val i64 → Val i32 → Expr Val Cont [Ty.bool])
    (hidx : idx.toNat = c.g.A + 1 + k)
    (hmv_eq : mv.toNat = pass1Mv c.g (marksToBool c.marks) root k)
    (hnc_eq : nc.toNat = pass1Nc c.g (marksToBool c.marks) k)
    (hbb_eq : bb.toNat = pass1BodyBytes c.g (marksToBool c.marks) root k)
    (hmv_bd : mv.toNat < bvDimacsBound)
    (hm_true : (marksToBool c.marks).getD (c.g.A + 1 + k) false = true)
    (hm : (bvCoiMem c.workBase c.aigPtr c.marksPtr c.avail c.hdr c.aigUsed c.marks ⋆ R) m)
    (hOom : HypOom c R Q)
    (hNext : ∀ (mv' nc' : Val i32) (bb' : Val i64),
      mv'.toNat = pass1Mv c.g (marksToBool c.marks) root (k + 1) →
      nc'.toNat = pass1Nc c.g (marksToBool c.marks) (k + 1) →
      bb'.toNat = pass1BodyBytes c.g (marksToBool c.marks) root (k + 1) →
      mv'.toNat < bvDimacsBound → nc'.toNat < bvDimacsBound → wp Γ Q X (onDone mv' nc' bb' idx) m) :
    wp Γ Q X (pass1GateStep c.workBase c.aigPtr c.hdr.num_atoms mv nc bb idx idx
      (packAigGate (c.g.nodes[k]'hk).1 (c.g.nodes[k]'hk).2) onDone) m := by
  have hbd := c.bd; have hlen := c.aig_len; have hwf := c.wf
  have hm_aig : (array64 c.aigPtr c.aigUsed ⋆ (bvHdrMem c.workBase c.hdr ⋆
      region (c.workBase + 128#64) (c.aigPtr.toNat - (c.workBase.toNat + 128)) ⋆
      bytes c.marksPtr c.marks ⋆ region (c.marksPtr + BitVec.ofNat 64 c.marks.length)
        (c.workBase.toNat + c.avail - (c.marksPtr.toNat + c.marks.length)) ⋆ R)) m := by
    unfold bvCoiMem at hm; exact sep_ac hm
  unfold pass1GateStep; c0_hsteps_nogrp; simp only [packAigGate_lo, packAigGate_hi]
  have hgv_lt : c.g.A + 1 + k + 1 < bvDimacsBound := by unfold bvDimacsBound at hbd ⊢; omega
  have hgv : (idx + 1#32).toNat = c.g.A + 1 + k + 1 := by
    rw [BitVec.toNat_add, hidx, show (1#32 : BitVec 32).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by unfold bvDimacsBound at hgv_lt; omega)]
  refine wp_detectIteExpr Γ Q X c.aigPtr c.hdr.num_atoms c.g c.aigUsed _ m k hk c.num_atoms hwf
    c.aig_w (by rw [c.aig_l, hlen]) hm_aig _ (fun ic it if_ hd => ?_) (fun hd => ?_)
  · dsimp only; c0_hstraight
    refine wp_maxUpdate Γ Q X _ _ _ m ?_
    let mv1 := if mv.toNat < (idx + 1#32).toNat then idx + 1#32 else mv
    refine wp_join_state (ts := [i32, i32, i64]) (α := Val i32 × Val i32 × Val i64)
      (fun st' => (st'.1, st'.2.1, st'.2.2, ()))
      (fun st' ml => ml = m ∧ st'.1.toNat = pass1Mv c.g (marksToBool c.marks) root (k + 1) ∧
        st'.2.1.toNat = pass1Nc c.g (marksToBool c.marks) (k + 1) ∧
        st'.2.2.toNat = pass1BodyBytes c.g (marksToBool c.marks) root (k + 1) ∧
        st'.1.toNat < bvDimacsBound ∧ st'.2.1.toNat < bvDimacsBound)
      (fun _ ⟨mv', nc', bb'⟩ ml ⟨hml, hmv', hnc', hbb', hmvb', hncb'⟩ =>
        hml ▸ hNext mv' nc' bb' hmv' hnc' hbb' hmvb' hncb')
      fun _ hJB => ?_
    c0_hstraight; c0_hsplit
    · clear hc
      have ⟨hc_lt, ht_lt, hf_lt⟩ := detectIte_bounds hwf hd
      have hcv_eq : (ic.toBitVec >>> (1 : Nat) + 1#32).toNat = (ic >>> 1).toNat + 1 :=
        bv32_lsr1_add1_toNat _
      have htv_eq : (it.toBitVec >>> (1 : Nat) + 1#32).toNat = (it >>> 1).toNat + 1 :=
        bv32_lsr1_add1_toNat _
      have hfv_eq : (if_.toBitVec >>> (1 : Nat) + 1#32).toNat = (if_ >>> 1).toNat + 1 :=
        bv32_lsr1_add1_toNat _
      have hcv_lt : (ic >>> 1).toNat + 1 < bvDimacsBound := by unfold bvDimacsBound at hbd ⊢; omega
      have htv_lt : (it >>> 1).toNat + 1 < bvDimacsBound := by unfold bvDimacsBound at hbd ⊢; omega
      have hfv_lt : (if_ >>> 1).toNat + 1 < bvDimacsBound := by unfold bvDimacsBound at hbd ⊢; omega
      c0_hstraight
      refine wp_maxUpdate Γ Q X _ _ _ m (wp_maxUpdate Γ Q X _ _ _ m
        (wp_maxUpdate Γ Q X _ _ _ m ?_))
      let mv2 := if mv1.toNat < (ic.toBitVec >>> (1 : Nat) + 1#32).toNat then
        ic.toBitVec >>> (1 : Nat) + 1#32 else mv1
      let mv3 := if mv2.toNat < (it.toBitVec >>> (1 : Nat) + 1#32).toNat then
        it.toBitVec >>> (1 : Nat) + 1#32 else mv2
      let mv4 := if mv3.toNat < (if_.toBitVec >>> (1 : Nat) + 1#32).toNat then
        if_.toBitVec >>> (1 : Nat) + 1#32 else mv3
      have hmv4_nat : mv4.toNat = max (max (max (max mv.toNat (c.g.A + 1 + k + 1))
          ((ic >>> 1).toNat + 1)) ((it >>> 1).toNat + 1)) ((if_ >>> 1).toNat + 1) := by
        dsimp only [mv4, mv3, mv2, mv1]
        rw [bv32_if_lt_toNat, bv32_if_lt_toNat, bv32_if_lt_toNat, bv32_if_lt_toNat,
          hgv, hcv_eq, htv_eq, hfv_eq]
      have hmv4_bd : mv4.toNat < bvDimacsBound := by rw [hmv4_nat]; omega
      have ⟨hmv_s, hnc_s, _, hbb_s⟩ :=
        pass1_succ_true_ite c.g (marksToBool c.marks) root hk hm_true hd
      have hmv4_eq : mv4.toNat = pass1Mv c.g (marksToBool c.marks) root (k + 1) := by
        rw [hmv_s, ← hmv_eq, hmv4_nat]
      refine wp_join0 (fun ml => ml = m)
        (fun _ _ hml => hml ▸ wp_coiOomRet Γ Q X c R m hm hOom) fun _ hJ => ?_
      c0_hsteps_nogrp
      · exact hJ m rfl
      · exact hJ m rfl
      · have hnc_lt4 : nc.toNat < 268435456 - 4 := by
          simp only [Nat.reducePow, Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd] at hc; omega
        have hnc1_toNat : (nc + 4#32).toNat = nc.toNat + 4 := by
          rw [BitVec.toNat_add, show (4#32 : BitVec 32).toNat = 4 from rfl,
            Nat.mod_eq_of_lt (by omega : nc.toNat + 4 < 2 ^ 32)]
        have hnc1_eq : (nc + 4#32).toNat = pass1Nc c.g (marksToBool c.marks) (k + 1) := by
          rw [hnc1_toNat, hnc_eq, ← hnc_s]
        have hnc1_bd : (nc + 4#32).toNat < bvDimacsBound := by unfold bvDimacsBound; omega
        refine wp_decLen_call Γ hDecLen _ m _ ?_; c0_hsteps_nogrp
        refine wp_decLen_call Γ hDecLen _ m _ ?_; c0_hsteps_nogrp
        refine wp_decLen_call Γ hDecLen _ m _ ?_; c0_hsteps_nogrp
        refine wp_decLen_call Γ hDecLen _ m _ ?_; c0_hsteps_nogrp
        have hb := pass1BodyBytes_lt_pow64 (g := c.g) (marks := marksToBool c.marks) (root := root)
          c.bd_nat (k := k + 1)
        have hsum := bv64_ite_bytes_toNat (bb := bb)
          (by unfold bvDimacsBound at hnc1_bd
              rw [hbb_s, ← hbb_eq, ← hgv, ← hcv_eq, ← htv_eq, ← hfv_eq] at hb; omega)
          (natToBytes_length_le_10 (idx + 1#32).isLt)
          (natToBytes_length_le_10 (ic.toBitVec >>> (1 : Nat) + 1#32).isLt)
          (natToBytes_length_le_10 (it.toBitVec >>> (1 : Nat) + 1#32).isLt)
          (natToBytes_length_le_10 (if_.toBitVec >>> (1 : Nat) + 1#32).isLt)
        exact hJB (mv4, nc + 4#32, _) m ⟨rfl, hmv4_eq, hnc1_eq,
          by dsimp only; rw [hsum, hbb_s, ← hbb_eq, hgv, hcv_eq, htv_eq, hfv_eq],
          hmv4_bd, hnc1_bd⟩
    · exact absurd hc (by decide)
  · dsimp only; c0_hstraight
    refine wp_maxUpdate Γ Q X _ _ _ m ?_
    let mv1 := if mv.toNat < (idx + 1#32).toNat then idx + 1#32 else mv
    refine wp_join_state (ts := [i32, i32, i64]) (α := Val i32 × Val i32 × Val i64)
      (fun st' => (st'.1, st'.2.1, st'.2.2, ()))
      (fun st' ml => ml = m ∧ st'.1.toNat = pass1Mv c.g (marksToBool c.marks) root (k + 1) ∧
        st'.2.1.toNat = pass1Nc c.g (marksToBool c.marks) (k + 1) ∧
        st'.2.2.toNat = pass1BodyBytes c.g (marksToBool c.marks) root (k + 1) ∧
        st'.1.toNat < bvDimacsBound ∧ st'.2.1.toNat < bvDimacsBound)
      (fun _ ⟨mv', nc', bb'⟩ ml ⟨hml, hmv', hnc', hbb', hmvb', hncb'⟩ =>
        hml ▸ hNext mv' nc' bb' hmv' hnc' hbb' hmvb' hncb')
      fun _ hJB => ?_
    c0_hstraight; c0_hsplit
    · exact absurd trivial hc
    · clear hc
      have hlv_eq : ((c.g.nodes[k]'hk).1.toBitVec >>> (1 : Nat) + 1#32).toNat =
          ((c.g.nodes[k]'hk).1 >>> 1).toNat + 1 := bv32_lsr1_add1_toNat _
      have hrv_eq : ((c.g.nodes[k]'hk).2.toBitVec >>> (1 : Nat) + 1#32).toNat =
          ((c.g.nodes[k]'hk).2 >>> 1).toNat + 1 := bv32_lsr1_add1_toNat _
      have hlv_lt : ((c.g.nodes[k]'hk).1 >>> 1).toNat + 1 < bvDimacsBound := by
        have := (hwf k hk).1; unfold bvDimacsBound at hbd ⊢; omega
      have hrv_lt : ((c.g.nodes[k]'hk).2 >>> 1).toNat + 1 < bvDimacsBound := by
        have := (hwf k hk).2; unfold bvDimacsBound at hbd ⊢; omega
      c0_hstraight
      refine wp_maxUpdate Γ Q X _ _ _ m (wp_maxUpdate Γ Q X _ _ _ m ?_)
      let mv2 := if mv1.toNat < ((c.g.nodes[k]'hk).1.toBitVec >>> 1 + 1#32).toNat then
        (c.g.nodes[k]'hk).1.toBitVec >>> 1 + 1#32 else mv1
      let mv3 := if mv2.toNat < ((c.g.nodes[k]'hk).2.toBitVec >>> 1 + 1#32).toNat then
        (c.g.nodes[k]'hk).2.toBitVec >>> 1 + 1#32 else mv2
      have hmv3_nat : mv3.toNat = max (max (max mv.toNat (c.g.A + 1 + k + 1))
          (((c.g.nodes[k]'hk).1 >>> 1).toNat + 1)) (((c.g.nodes[k]'hk).2 >>> 1).toNat + 1) := by
        dsimp only [mv3, mv2, mv1]
        rw [bv32_if_lt_toNat, bv32_if_lt_toNat, bv32_if_lt_toNat, hgv, hlv_eq, hrv_eq]
      have hmv3_bd : mv3.toNat < bvDimacsBound := by rw [hmv3_nat]; omega
      have ⟨hmv_s, hnc_s, _, hbb_s⟩ :=
        pass1_succ_true_and c.g (marksToBool c.marks) root hk hm_true hd
      have hmv3_eq : mv3.toNat = pass1Mv c.g (marksToBool c.marks) root (k + 1) := by
        rw [hmv_s, ← hmv_eq, hmv3_nat]
      refine wp_join0 (fun ml => ml = m)
        (fun _ _ hml => hml ▸ wp_coiOomRet Γ Q X c R m hm hOom) fun _ hJ => ?_
      c0_hsteps_nogrp
      · exact hJ m rfl
      · exact hJ m rfl
      · have hnc_lt3 : nc.toNat < 268435456 - 3 := by
          simp only [Nat.reducePow, Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd] at hc; omega
        have hnc1_toNat : (nc + 3#32).toNat = nc.toNat + 3 := by
          rw [BitVec.toNat_add, show (3#32 : BitVec 32).toNat = 3 from rfl,
            Nat.mod_eq_of_lt (by omega : nc.toNat + 3 < 2 ^ 32)]
        have hnc1_eq : (nc + 3#32).toNat = pass1Nc c.g (marksToBool c.marks) (k + 1) := by
          rw [hnc1_toNat, hnc_eq, ← hnc_s]
        have hnc1_bd : (nc + 3#32).toNat < bvDimacsBound := by unfold bvDimacsBound; omega
        refine wp_decLen_call Γ hDecLen _ m _ ?_; c0_hsteps_nogrp
        refine wp_litBytes_call Γ hLitBytes _ m _ ?_; c0_hsteps_nogrp
        refine wp_litBytes_call Γ hLitBytes _ m _ ?_; c0_hsteps_nogrp
        refine wp_litBytes_call Γ hLitBytes _ m _ ?_; c0_hsteps_nogrp
        refine wp_litBytes_call Γ hLitBytes _ m _ ?_; c0_hsteps_nogrp
        have hb := pass1BodyBytes_lt_pow64 (g := c.g) (marks := marksToBool c.marks) (root := root)
          c.bd_nat (k := k + 1)
        have hsum := bv64_gate_bytes_toNat (bb := bb)
          (by simp only [UInt32.ofBitVec_toBitVec]; unfold bvDimacsBound at hnc1_bd
              rw [hbb_s, ← hbb_eq, ← hgv] at hb; omega)
          (natToBytes_length_le_10 (idx + 1#32).isLt)
          (encodeDimacsLit_length_le_bv (c.g.nodes[k]'hk).1.toBitVec)
          (encodeDimacsLit_length_le_bv (c.g.nodes[k]'hk).2.toBitVec)
          (encodeDimacsLit_length_le_bv ((c.g.nodes[k]'hk).1.toBitVec ^^^ 1#32))
          (encodeDimacsLit_length_le_bv ((c.g.nodes[k]'hk).2.toBitVec ^^^ 1#32))
        simp only [UInt32.ofBitVec_toBitVec] at hsum
        exact hJB (mv3, nc + 3#32, _) m ⟨rfl, hmv3_eq, hnc1_eq,
          by rw [hsum, hbb_s, ← hbb_eq, hgv], hmv3_bd, hnc1_bd⟩

private theorem wp_pass1Expr (Γ : Env) (hDecLen : HypDecLen Γ) (hLitBytes : HypLitBytes Γ)
    (Q : Post [Ty.bool]) (X : XPost) (c : CoiCtx) (R : Mem 64 → Prop) (m : Mem 64)
    (root : BitVec 32) (mv0 : Val i32) (bb0 : Val i64) (g0 : Val i32)
    (kExit : Val i32 → Val i32 → Val i64 → Expr Val Cont [Ty.bool])
    (hmv0_eq : mv0.toNat = pass1Mv c.g (marksToBool c.marks) root 0)
    (hbb0_eq : bb0.toNat = pass1BodyBytes c.g (marksToBool c.marks) root 0)
    (hmv0_bd : mv0.toNat < bvDimacsBound) (hg0_eq : g0 = BitVec.ofNat 32 (c.g.A + 1))
    (hm : (bvCoiMem c.workBase c.aigPtr c.marksPtr c.avail c.hdr c.aigUsed c.marks ⋆ R) m)
    (hOom : HypOom c R Q)
    (hkExit : ∀ (mv nc : Val i32) (bb : Val i64),
      mv.toNat = pass1Mv c.g (marksToBool c.marks) root c.g.nodes.size →
      nc.toNat = pass1Nc c.g (marksToBool c.marks) c.g.nodes.size →
      bb.toNat = pass1BodyBytes c.g (marksToBool c.marks) root c.g.nodes.size →
      mv.toNat < bvDimacsBound → nc.toNat < bvDimacsBound → wp Γ Q X (kExit mv nc bb) m) :
    wp Γ Q X (pass1Expr c.workBase c.hdr.num_atoms c.hdr.aig_len c.marksPtr c.aigPtr mv0 bb0 g0
      kExit) m := by
  have hcoi : (coiCoreMem c c.hdr (c.workBase.toNat + c.avail) ⋆ R) m := by
    unfold bvCoiMem at hm; dsimp only [coiCoreMem]; exact sep_ac hm
  dsimp only [coiCoreMem] at hcoi
  have hbd := c.bd; have hlen := c.aig_len; have hm_l := c.marks_l; have haig_l := c.aig_l
  unfold pass1Expr; have h1bd : 1 < bvDimacsBound := by decide
  refine wp_while_state (ts := [i32, i32, i64, i32]) (α := Nat × Val i32 × Val i32 × Val i64)
    (fun st => (st.2.1, st.2.2.1, st.2.2.2, BitVec.ofNat 32 (c.g.A + 1 + st.1), ()))
    (fun st => c.g.nodes.size - st.1)
    (fun st ml => ml = m ∧ st.1 ≤ c.g.nodes.size ∧
      st.2.1.toNat = pass1Mv c.g (marksToBool c.marks) root st.1 ∧
      st.2.2.1.toNat = pass1Nc c.g (marksToBool c.marks) st.1 ∧
      st.2.2.2.toNat = pass1BodyBytes c.g (marksToBool c.marks) root st.1 ∧
      st.2.1.toNat < bvDimacsBound ∧ st.2.2.1.toNat < bvDimacsBound) ?_ ?_
  · intro J hJ; c0_hsteps
    simpa [hg0_eq] using hJ (0, mv0, 1#32, bb0) m ⟨rfl, Nat.zero_le _, hmv0_eq,
      by simp [(pass1_zero c.g (marksToBool c.marks) root).2.1], hbb0_eq, hmv0_bd, h1bd⟩
  · intro J ⟨k, mv, nc, bb⟩ ml ⟨hml, hk_le, hmv_eq, hnc_eq, hbb_eq, hmv_bd, hnc_bd⟩ ih
    subst ml; c0_hsteps_nogrp
    · have hk_lt : k < c.g.nodes.size := by c0_bv_omega [hc, hlen, hbd]
      have hidx_eq := idx32_toNat c.bd_nat hk_lt
      refine wp_join_state (α := Val i32 × Val i32 × Val i64)
        (fun st' => (st'.1, st'.2.1, st'.2.2, ()))
        (fun st' ml' => ml' = m ∧ st'.1.toNat = pass1Mv c.g (marksToBool c.marks) root (k + 1) ∧
          st'.2.1.toNat = pass1Nc c.g (marksToBool c.marks) (k + 1) ∧
          st'.2.2.toNat = pass1BodyBytes c.g (marksToBool c.marks) root (k + 1) ∧
          st'.1.toNat < bvDimacsBound ∧ st'.2.1.toNat < bvDimacsBound) ?_ ?_
      · intro _ ⟨mv', nc', bb'⟩ ml' ⟨hml', hmv', hnc', hbb', hmvb', hncb'⟩
        subst ml'; c0_hsteps; rw [idx32_add1 c.bd_nat hk_lt]
        exact ih (k + 1, mv', nc', bb') m (by omega) ⟨rfl, by omega, hmv', hnc', hbb', hmvb', hncb'⟩
      · intro J1 hJ1; have hg_lt : c.g.A + 1 + k < c.marks.length := by omega
        c0_hsteps_nogrp
        · have hm_t := mark_getD_true_of_bv rfl hidx_eq hg_lt hc
          have haig_lt : (BitVec.ofNat 32 (c.g.A + 1 + k)).toNat < c.aigUsed.length := by
            rw [hidx_eq]; omega
          c0_hsteps_nogrp; simp only [hidx_eq]; rw [c.aig_w.gate_eq k hk_lt]
          refine wp_pass1GateStep Γ hDecLen hLitBytes Q X c R m root k hk_lt mv nc bb
            (BitVec.ofNat 32 (c.g.A + 1 + k)) _ hidx_eq hmv_eq hnc_eq hbb_eq hmv_bd hm_t hm hOom
            fun mv' nc' bb' hmv' hnc' hbb' hmvb' hncb' => ?_
          c0_hsteps; exact hJ1 (mv', nc', bb') m ⟨rfl, hmv', hnc', hbb', hmvb', hncb'⟩
        · have hm_f := mark_getD_false_of_bv rfl hidx_eq hg_lt hc
          have ⟨hmv_s, hnc_s, _, hbb_s⟩ :=
            pass1_succ_false c.g (marksToBool c.marks) root hk_lt hm_f
          rw [← hmv_s] at hmv_eq; rw [← hnc_s] at hnc_eq; rw [← hbb_s] at hbb_eq
          exact hJ1 (mv, nc, bb) m ⟨rfl, hmv_eq, hnc_eq, hbb_eq, hmv_bd, hnc_bd⟩
    · have hk_end : k = c.g.nodes.size := by c0_bv_omega [hc, hlen, hbd]
      subst hk_end; exact hkExit mv nc bb hmv_eq hnc_eq hbb_eq hmv_bd hnc_bd

private theorem wp_writeLit_pref (Γ : Env) (hWriteLit : HypWriteLit Γ)
    {Q : Post [Ty.bool]} {X : XPost} {curP base : BitVec 64} {pref : List UInt8}
    {l : BitVec 32} {lit : Std.Sat.Literal Nat} {rem : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Tup Val [i64] → Expr Val Cont [Ty.bool]}
    (hcur : curP = base + BitVec.ofNat 64 pref.length)
    (hlit : litToDimacs (UInt32.ofBitVec l) = lit)
    (hm : (region curP ((encodeDimacsLit lit).length + rem) ⋆ (bytes base pref ⋆ R)) m)
    (hfit : base.toNat + (pref.length + (encodeDimacsLit lit).length + rem) < 2 ^ 64)
    (hk : ∀ m', bufAt base (pref ++ encodeDimacsLit lit) rem R m' →
      wp Γ Q X (k (base + BitVec.ofNat 64 (pref ++ encodeDimacsLit lit).length, ())) m') :
    wp Γ Q X (Expr.call (as := [i64, i32]) (bs := [i64]) "bv_write_lit"
      (Arg.var curP, Arg.var l, ()) k) m := by
  subst hcur
  have hcur_nat := bv64_add_ofNat_toNat (a := base) (n := pref.length) (by omega)
  have hs := region_split_prefix (by omega) hm
  c0_call hWriteLit
  refine ⟨_, by rw [hlit, hcur_nat]; omega, by rw [hlit]; exact hs, fun m' hm' => ?_⟩
  rw [hlit] at hm' ⊢; rw [ptr_add_ofNat, ← List.length_append]
  exact hk m' (buf_append_step (by omega) (sep_ac hm'))

private theorem wp_writeEnd_pref (Γ : Env) (hWriteEnd : HypWriteEnd Γ)
    {Q : Post [Ty.bool]} {X : XPost} {base : BitVec 64} {pref : List UInt8}
    {rem : Nat} {R : Mem 64 → Prop} {m : Mem 64} {k : Tup Val [i64] → Expr Val Cont [Ty.bool]}
    (hm : bufAt base pref (2 + rem) R m) (hfit : base.toNat + (pref.length + 2 + rem) < 2 ^ 64)
    (hk : ∀ m', bufAt base (pref ++ [asciiZero, asciiNewline]) rem R m' →
      wp Γ Q X (k (base + BitVec.ofNat 64 (pref ++ [asciiZero, asciiNewline]).length, ())) m') :
    wp Γ Q X (Expr.call (as := [i64]) (bs := [i64]) "bv_write_clause_end"
      (Arg.var (base + BitVec.ofNat 64 pref.length), ()) k) m := by
  have hcur_nat := bv64_add_ofNat_toNat (a := base) (n := pref.length) (by omega)
  have hs := region_split_prefix (by omega) hm
  c0_call hWriteEnd
  refine ⟨_, by rw [hcur_nat]; omega, hs, fun m' hm' => ?_⟩
  rw [ptr_add_ofNat, ← show (pref ++ [asciiZero, asciiNewline]).length = pref.length + 2 by simp]
  exact hk m' (buf_append_step (by simp; omega) (sep_ac hm'))

private theorem wp_writeClause2_pref (Γ : Env)
    (hWriteLit : HypWriteLit Γ) (hWriteEnd : HypWriteEnd Γ)
    {Q : Post [Ty.bool]} {X : XPost} {curP base : BitVec 64} {pref : List UInt8}
    {v1 v2 : BitVec 32} {l1 l2 : Std.Sat.Literal Nat} {rem : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {k : Tup Val [i64] → Expr Val Cont [Ty.bool]}
    (hcur : curP = base + BitVec.ofNat 64 pref.length)
    (hl1 : litToDimacs (UInt32.ofBitVec v1) = l1) (hl2 : litToDimacs (UInt32.ofBitVec v2) = l2)
    (hm : (region curP ((encodeDimacsLit l1 ++ encodeDimacsLit l2 ++
        [asciiZero, asciiNewline]).length + rem) ⋆ (bytes base pref ⋆ R)) m)
    (hfit : base.toNat + (pref.length + (encodeDimacsLit l1 ++ encodeDimacsLit l2 ++
        [asciiZero, asciiNewline]).length + rem) < 2 ^ 64)
    (hk : ∀ m', bufAt base (pref ++ encodeDimacsLit l1 ++ encodeDimacsLit l2 ++
          [asciiZero, asciiNewline]) rem R m' →
      wp Γ Q X (k (base + BitVec.ofNat 64 (pref ++ encodeDimacsLit l1 ++ encodeDimacsLit l2 ++
        [asciiZero, asciiNewline]).length, ())) m') :
    wp Γ Q X (Expr.call (as := [i64, i32]) (bs := [i64]) "bv_write_lit"
        (Arg.var curP, Arg.var v1, ())
      fun p1 => Expr.call (as := [i64, i32]) (bs := [i64]) "bv_write_lit"
        (Arg.var p1.1, Arg.var v2, ()) fun p2 => Expr.call (as := [i64]) (bs := [i64])
        "bv_write_clause_end" (Arg.var p2.1, ()) k) m := by
  simp only [List.length_append,
    show [asciiZero, asciiNewline].length = 2 from rfl] at hm hfit
  refine wp_writeLit_pref Γ hWriteLit hcur hl1 (by simpa only [Nat.add_assoc] using hm)
    (by omega) fun m1 hm1 => ?_; c0_hsteps_nogrp
  refine wp_writeLit_pref Γ hWriteLit rfl hl2
    (by dsimp only [bufAt] at hm1; simpa only [Nat.add_assoc] using hm1)
    (by simp only [List.length_append] at hfit ⊢; omega) fun m2 hm2 => ?_; c0_hsteps_nogrp
  refine wp_writeEnd_pref Γ hWriteEnd hm2
    (by simp only [List.length_append] at hfit ⊢; omega) fun m3 hm3 => ?_
  simpa only [List.append_assoc] using hk m3 hm3

private theorem wp_writeClause3Xor_pref (Γ : Env)
    (hWriteLit : HypWriteLit Γ) (hWriteEnd : HypWriteEnd Γ)
    {Q : Post [Ty.bool]} {X : XPost} {base : BitVec 64} {pref : List UInt8}
    {v1 lhs rhs : BitVec 32} {l1 l2 l3 : Std.Sat.Literal Nat} {rem : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {k : Tup Val [i64] → Expr Val Cont [Ty.bool]}
    (hl1 : litToDimacs (UInt32.ofBitVec v1) = l1)
    (hl2 : litToDimacs (UInt32.ofBitVec (lhs ^^^ 1#32)) = l2)
    (hl3 : litToDimacs (UInt32.ofBitVec (rhs ^^^ 1#32)) = l3)
    (hm : bufAt base pref ((encodeDimacsLit l1 ++ encodeDimacsLit l2 ++ encodeDimacsLit l3 ++
        [asciiZero, asciiNewline]).length + rem) R m)
    (hfit : base.toNat + (pref.length + (encodeDimacsLit l1 ++ encodeDimacsLit l2 ++
        encodeDimacsLit l3 ++ [asciiZero, asciiNewline]).length + rem) < 2 ^ 64)
    (hk : ∀ m', bufAt base (pref ++ encodeDimacsLit l1 ++ encodeDimacsLit l2 ++
          encodeDimacsLit l3 ++ [asciiZero, asciiNewline]) rem R m' →
      wp Γ Q X (k (base + BitVec.ofNat 64 (pref ++ encodeDimacsLit l1 ++ encodeDimacsLit l2 ++
        encodeDimacsLit l3 ++ [asciiZero, asciiNewline]).length, ())) m') :
    wp Γ Q X (Expr.call (as := [i64, i32]) (bs := [i64]) "bv_write_lit"
        (Arg.var (base + BitVec.ofNat 64 pref.length), Arg.var v1, ()) fun p7 =>
      Expr.let_ ⟨OpCode.xor i32, (Arg.var lhs, Arg.imm 1#32, ())⟩ fun nl =>
      Expr.call (as := [i64, i32]) (bs := [i64]) "bv_write_lit" (Arg.var p7.1, Arg.var nl.1, ())
        fun p8 => Expr.let_ ⟨OpCode.xor i32, (Arg.var rhs, Arg.imm 1#32, ())⟩ fun nr =>
      Expr.call (as := [i64, i32]) (bs := [i64]) "bv_write_lit" (Arg.var p8.1, Arg.var nr.1, ())
        fun p9 => Expr.call (as := [i64]) (bs := [i64]) "bv_write_clause_end" (Arg.var p9.1, ()) k)
      m := by
  simp only [List.length_append, show [asciiZero, asciiNewline].length = 2 from rfl] at hm hfit
  refine wp_writeLit_pref Γ hWriteLit rfl hl1
    (by dsimp only [bufAt] at hm; simpa only [Nat.add_assoc] using hm)
    (by omega) fun m1 hm1 => ?_; c0_hsteps_nogrp
  refine wp_writeLit_pref Γ hWriteLit rfl hl2
    (by dsimp only [bufAt] at hm1; simpa only [Nat.add_assoc] using hm1)
    (by simp only [List.length_append] at hfit ⊢; omega) fun m2 hm2 => ?_; c0_hsteps_nogrp
  refine wp_writeLit_pref Γ hWriteLit rfl hl3
    (by dsimp only [bufAt] at hm2; simpa only [Nat.add_assoc] using hm2)
    (by simp only [List.length_append] at hfit ⊢; omega) fun m3 hm3 => ?_; c0_hsteps_nogrp
  refine wp_writeEnd_pref Γ hWriteEnd hm3
    (by simp only [List.length_append] at hfit ⊢; omega) fun m4 hm4 => ?_
  simpa only [List.append_assoc] using hk m4 hm4

private theorem wp_writeClause3_pref (Γ : Env)
    (hWriteLit : HypWriteLit Γ) (hWriteEnd : HypWriteEnd Γ)
    {Q : Post [Ty.bool]} {X : XPost} {curP base : BitVec 64} {pref : List UInt8}
    {v1 v2 v3 : BitVec 32} {l1 l2 l3 : Std.Sat.Literal Nat} {rem : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {k : Tup Val [i64] → Expr Val Cont [Ty.bool]}
    (hcur : curP = base + BitVec.ofNat 64 pref.length)
    (hl1 : litToDimacs (UInt32.ofBitVec v1) = l1)
    (hl2 : litToDimacs (UInt32.ofBitVec v2) = l2)
    (hl3 : litToDimacs (UInt32.ofBitVec v3) = l3)
    (hm : (region curP ((encodeDimacsLit l1 ++ encodeDimacsLit l2 ++ encodeDimacsLit l3 ++
        [asciiZero, asciiNewline]).length + rem) ⋆ (bytes base pref ⋆ R)) m)
    (hfit : base.toNat + (pref.length + (encodeDimacsLit l1 ++ encodeDimacsLit l2 ++
        encodeDimacsLit l3 ++ [asciiZero, asciiNewline]).length + rem) < 2 ^ 64)
    (hk : ∀ m', bufAt base (pref ++ encodeDimacsLit l1 ++ encodeDimacsLit l2 ++
          encodeDimacsLit l3 ++ [asciiZero, asciiNewline]) rem R m' →
      wp Γ Q X (k (base + BitVec.ofNat 64 (pref ++ encodeDimacsLit l1 ++ encodeDimacsLit l2 ++
        encodeDimacsLit l3 ++ [asciiZero, asciiNewline]).length, ())) m') :
    wp Γ Q X (Expr.call (as := [i64, i32]) (bs := [i64]) "bv_write_lit"
        (Arg.var curP, Arg.var v1, ()) fun p1 =>
      Expr.call (as := [i64, i32]) (bs := [i64]) "bv_write_lit"
        (Arg.var p1.1, Arg.var v2, ()) fun p2 =>
      Expr.call (as := [i64, i32]) (bs := [i64]) "bv_write_lit"
        (Arg.var p2.1, Arg.var v3, ()) fun p3 =>
      Expr.call (as := [i64]) (bs := [i64]) "bv_write_clause_end" (Arg.var p3.1, ()) k) m := by
  simp only [List.length_append, show [asciiZero, asciiNewline].length = 2 from rfl] at hm hfit
  refine wp_writeLit_pref Γ hWriteLit hcur hl1 (by simpa only [Nat.add_assoc] using hm)
    (by omega) fun m1 hm1 => ?_; c0_hsteps_nogrp
  refine wp_writeLit_pref Γ hWriteLit rfl hl2
    (by dsimp only [bufAt] at hm1; simpa only [Nat.add_assoc] using hm1)
    (by simp only [List.length_append] at hfit ⊢; omega) fun m2 hm2 => ?_; c0_hsteps_nogrp
  refine wp_writeLit_pref Γ hWriteLit rfl hl3
    (by dsimp only [bufAt] at hm2; simpa only [Nat.add_assoc] using hm2)
    (by simp only [List.length_append] at hfit ⊢; omega) fun m3 hm3 => ?_; c0_hsteps_nogrp
  refine wp_writeEnd_pref Γ hWriteEnd hm3
    (by simp only [List.length_append] at hfit ⊢; omega) fun m4 hm4 => ?_
  simpa only [List.append_assoc] using hk m4 hm4

private theorem wp_pass2GateStep (Γ : Env) (hWriteLit : HypWriteLit Γ) (hWriteEnd : HypWriteEnd Γ)
    (Q : Post [Ty.bool]) (X : XPost) (aigPtr : Val i64) (A : Val i32) (g : Aig)
    (aigUsed : List (BitVec 64)) (k : Nat) (hk : k < g.nodes.size)
    (idx : Val i32) (curP : Val i64) (R : Mem 64 → Prop) (m : Mem 64)
    (onDone : Val i64 → Expr Val Cont [Ty.bool])
    (hA : A.toNat = g.A) (hwf : g.Wf) (haig_w : AigWordsMatch g aigUsed)
    (haig_l : aigUsed.length = g.A + 1 + g.nodes.size)
    (hidx : idx.toNat = g.A + 1 + k) (hk_bd : g.A + 1 + k < bvDimacsBound)
    (hfit : curP.toNat + ((gateClauses g k hk).flatMap encodeDimacsClause).length < 2 ^ 64)
    (hm : (region curP ((gateClauses g k hk).flatMap encodeDimacsClause).length ⋆
      (array64 aigPtr aigUsed ⋆ R)) m)
    (hNext : ∀ (m' : Mem 64), (bytes curP ((gateClauses g k hk).flatMap encodeDimacsClause) ⋆
        (array64 aigPtr aigUsed ⋆ R)) m' →
      wp Γ Q X (onDone (curP + BitVec.ofNat 64 ((gateClauses g k hk).flatMap
        encodeDimacsClause).length)) m') :
    wp Γ Q X (pass2GateStep aigPtr A idx curP
      (packAigGate (g.nodes[k]'hk).1 (g.nodes[k]'hk).2) onDone) m := by
  unfold pass2GateStep; c0_hsteps_nogrp; simp only [packAigGate_lo, packAigGate_hi]
  have hn_lt : g.A + 1 + k < 2 ^ 31 := by unfold bvDimacsBound at hk_bd; omega
  have hidx_bv : idx = BitVec.ofNat 32 (g.A + 1 + k) := BitVec.eq_of_toNat_eq (by simp [hidx])
  have hlit_neg : litToDimacs (UInt32.ofBitVec ((idx <<< (1 : Nat)) ||| 1#32)) =
      (g.A + 1 + k + 1, false) := by
    rw [show idx <<< (1 : Nat) = idx <<< (1 : BitVec 32) from rfl, hidx_bv]
    exact litToDimacs_neg_out hn_lt
  have hlit_pos : litToDimacs (UInt32.ofBitVec (idx <<< (1 : Nat))) = (g.A + 1 + k + 1, true) := by
    rw [show idx <<< (1 : Nat) = idx <<< (1 : BitVec 32) from rfl, hidx_bv]
    exact litToDimacs_pos_out hn_lt
  have hnil : bytes curP [] = emp := (eq_nil_At curP).symm
  refine wp_detectIteExpr Γ Q X aigPtr A g aigUsed
    (region curP ((gateClauses g k hk).flatMap encodeDimacsClause).length ⋆ R) m k hk hA hwf
    haig_w haig_l (sep_ac hm) _ (fun ic it if_ hd => ?_) (fun hd => ?_)
  · dsimp only; c0_hstraight
    refine wp_join_state1 (fun np : Val i64 => np)
      (fun np m' => np = curP + BitVec.ofNat 64 ((gateClauses g k hk).flatMap
          encodeDimacsClause).length ∧
        (bytes curP ((gateClauses g k hk).flatMap encodeDimacsClause) ⋆
          (array64 aigPtr aigUsed ⋆ R)) m')
      (fun _ np m' ⟨hnp, hm'⟩ => hnp ▸ hNext m' hm') fun _ hJB => ?_
    c0_hstraight; c0_hsplit
    · clear hc; c0_hstraight
      have hgate : gateClauses g k hk = iteClauses (g.A + 1 + k) ic it if_ := by
        unfold gateClauses; rw [hd]
      have hfull := iteClauses_flatMap_eq (g.A + 1 + k) ic it if_
      rw [hgate, hfull] at hm hfit
      have hic : litToDimacs (UInt32.ofBitVec ic.toBitVec) = litToDimacs ic := rfl
      have hit : litToDimacs (UInt32.ofBitVec it.toBitVec) = litToDimacs it := rfl
      have hif : litToDimacs (UInt32.ofBitVec if_.toBitVec) = litToDimacs if_ := rfl
      refine wp_writeClause3_pref Γ hWriteLit hWriteEnd (BitVec.add_zero curP).symm rfl rfl
        hlit_pos (by rw [hnil, emp_sep]; simpa only [List.length_append] using hm)
        (by simp only [List.length_append, List.length_nil] at hfit ⊢; omega) fun m1 hm1 => ?_
      refine wp_writeClause3_pref Γ hWriteLit hWriteEnd rfl rfl hit hlit_neg
        (by dsimp only [bufAt] at hm1; simpa only [List.length_append] using hm1)
        (by simp only [List.length_append, List.length_nil] at hfit ⊢; omega) fun m2 hm2 => ?_
      refine wp_writeClause3_pref Γ hWriteLit hWriteEnd rfl hic rfl hlit_pos
        (by dsimp only [bufAt] at hm2; simpa only [List.length_append] using hm2)
        (by simp only [List.length_append, List.length_nil] at hfit ⊢; omega) fun m3 hm3 => ?_
      refine wp_writeClause3_pref Γ hWriteLit hWriteEnd rfl hic hif hlit_neg (rem := 0)
        (bufAt_rem (by simp only [List.length_append,
          show [asciiZero, asciiNewline].length = 2 from rfl]) hm3)
        (by simp only [List.length_append, List.length_nil, Nat.add_zero] at hfit ⊢; omega)
        fun m4 hm4 => ?_
      rw [bufAt, region_zero, emp_sep] at hm4; c0_hsteps_nogrp
      exact hJB _ m4 ⟨by rw [hgate, hfull]; simp only [List.nil_append, List.append_assoc],
        by rw [hgate, hfull]; simpa only [List.nil_append, List.append_assoc] using hm4⟩
    · exact absurd hc (by decide)
  · dsimp only; c0_hstraight
    refine wp_join_state1 (fun np : Val i64 => np)
      (fun np m' => np = curP + BitVec.ofNat 64 ((gateClauses g k hk).flatMap
          encodeDimacsClause).length ∧
        (bytes curP ((gateClauses g k hk).flatMap encodeDimacsClause) ⋆
          (array64 aigPtr aigUsed ⋆ R)) m')
      (fun _ np m' ⟨hnp, hm'⟩ => hnp ▸ hNext m' hm') fun _ hJB => ?_
    c0_hstraight; c0_hsplit
    · exact absurd trivial hc
    · clear hc
      have hgate : gateClauses g k hk =
          andClauses (g.A + 1 + k) (g.nodes[k]'hk).1 (g.nodes[k]'hk).2 := by
        unfold gateClauses; rw [hd]
      have hfull := andClauses_flatMap_eq (g.A + 1 + k) (g.nodes[k]'hk).1 (g.nodes[k]'hk).2
      rw [hgate, hfull] at hm hfit
      refine wp_writeClause2_pref Γ hWriteLit hWriteEnd (BitVec.add_zero curP).symm hlit_neg
        (l2 := litToDimacs (g.nodes[k]'hk).1) (by simp only [UInt32.ofBitVec_toBitVec])
        (by rw [hnil, emp_sep]; simpa only [List.length_append] using hm)
        (by simp only [List.length_append, List.length_nil] at hfit ⊢; omega) fun m1 hm1 => ?_
      refine wp_writeClause2_pref Γ hWriteLit hWriteEnd rfl hlit_neg
        (l2 := litToDimacs (g.nodes[k]'hk).2) (by simp only [UInt32.ofBitVec_toBitVec])
        (by dsimp only [bufAt] at hm1; simpa only [List.length_append] using hm1)
        (by simp only [List.length_append, List.length_nil] at hfit ⊢; omega) fun m2 hm2 => ?_
      refine wp_writeClause3Xor_pref Γ hWriteLit hWriteEnd (l1 := (g.A + 1 + k + 1, true))
        hlit_pos rfl rfl (rem := 0)
        (bufAt_rem (by simp only [List.length_append,
          show [asciiZero, asciiNewline].length = 2 from rfl]) hm2)
        (by simp only [List.length_append, List.length_nil, Nat.add_zero] at hfit ⊢; omega)
        fun m3 hm3 => ?_
      rw [bufAt, region_zero, emp_sep] at hm3; c0_hsteps_nogrp
      exact hJB _ m3 ⟨by rw [hgate, hfull]; simp only [List.nil_append, List.append_assoc],
        by rw [hgate, hfull]; simpa only [List.nil_append, List.append_assoc] using hm3⟩

private theorem wp_pass2Expr (Γ : Env) (hWriteLit : HypWriteLit Γ) (hWriteEnd : HypWriteEnd Γ)
    (Q : Post [Ty.bool]) (X : XPost) (c : CoiCtx) (bufStart : BitVec 64)
    (R : Mem 64 → Prop) (m : Mem 64) (root : BitVec 32) (initG : Val i32)
    (kDone : Val i64 → Expr Val Cont [Ty.bool]) (hg0_eq : initG = BitVec.ofNat 32 (c.g.A + 1))
    (hbuf_fit : bufStart.toNat + (p1Bytes c c.g.nodes.size).length < 2 ^ 64)
    (hm : (region bufStart (p1Bytes c c.g.nodes.size).length ⋆
      (array64 c.aigPtr c.aigUsed ⋆ bytes c.marksPtr c.marks ⋆ R)) m)
    (hkDone : ∀ (m' : Mem 64), (bytes bufStart (p1Bytes c c.g.nodes.size) ⋆
        (array64 c.aigPtr c.aigUsed ⋆ bytes c.marksPtr c.marks ⋆ R)) m' →
      wp Γ Q X (kDone (bufStart + BitVec.ofNat 64 (p1Bytes c c.g.nodes.size).length)) m') :
    wp Γ Q X (pass2Expr c.hdr.num_atoms c.hdr.aig_len c.marksPtr c.aigPtr initG bufStart
      kDone) m := by
  have hbd := c.bd; have hlen := c.aig_len; have haig_l := c.aig_l; have hm_l := c.marks_l
  unfold pass2Expr
  refine wp_while_state (ts := [i32, i64]) (α := Nat × Val i64)
    (fun st => (BitVec.ofNat 32 (c.g.A + 1 + st.1), st.2, ())) (fun st => c.g.nodes.size - st.1)
    (fun st ml => st.1 ≤ c.g.nodes.size ∧
      st.2 = bufStart + BitVec.ofNat 64 (p1Bytes c st.1).length ∧
      bufAt bufStart (p1Bytes c st.1) ((p1Bytes c c.g.nodes.size).length - (p1Bytes c st.1).length)
        (array64 c.aigPtr c.aigUsed ⋆ bytes c.marksPtr c.marks ⋆ R) ml) ?_ ?_
  · intro J hJ; c0_hsteps
    have h0 := (pass1_zero c.g (marksToBool c.marks) root).2.2.1
    have hnil : bytes bufStart [] = emp := (eq_nil_At bufStart).symm
    have hinit : bufAt bufStart (p1Bytes c 0)
        ((p1Bytes c c.g.nodes.size).length - (p1Bytes c 0).length)
        (array64 c.aigPtr c.aigUsed ⋆ bytes c.marksPtr c.marks ⋆ R) m := by
      dsimp only [bufAt, p1Bytes]
      rw [h0, List.length_nil, BitVec.add_zero, Nat.sub_zero, hnil, emp_sep]; exact hm
    simpa [hg0_eq] using hJ (0, bufStart) m ⟨Nat.zero_le _, by simp [p1Bytes, h0], hinit⟩
  · intro J ⟨k, curP⟩ ml ⟨hk_le, hcur_eq, hml⟩ ih
    dsimp only at hk_le hcur_eq; dsimp only [bufAt] at hml; c0_hsteps_nogrp
    · have hk_lt : k < c.g.nodes.size := by c0_bv_omega [hc, hlen, hbd]
      have hidx_eq := idx32_toNat c.bd_nat hk_lt
      refine wp_join_state1 (fun np : Val i64 => np)
        (fun np ml' => np = bufStart + BitVec.ofNat 64 (p1Bytes c (k + 1)).length ∧
          bufAt bufStart (p1Bytes c (k + 1))
            ((p1Bytes c c.g.nodes.size).length - (p1Bytes c (k + 1)).length)
            (array64 c.aigPtr c.aigUsed ⋆ bytes c.marksPtr c.marks ⋆ R) ml') ?_ ?_
      · intro _ np ml' ⟨hnp, hml'⟩; c0_hsteps; rw [idx32_add1 c.bd_nat hk_lt]
        exact ih (k + 1, np) ml' (by omega) ⟨by omega, hnp, hml'⟩
      · intro J1 hJ1; have hg_lt : c.g.A + 1 + k < c.marks.length := by omega
        c0_hsteps_nogrp
        · have hm_t := mark_getD_true_of_bv rfl hidx_eq hg_lt hc
          have haig_lt : (BitVec.ofNat 32 (c.g.A + 1 + k)).toNat < c.aigUsed.length := by
            rw [hidx_eq]; omega
          c0_hsteps_nogrp; simp only [hidx_eq]; rw [c.aig_w.gate_eq k hk_lt]
          have hbs_s : pass1Bytes c.g (marksToBool c.marks) (k + 1) =
              pass1Bytes c.g (marksToBool c.marks) k ++
                (gateClauses c.g k hk_lt).flatMap encodeDimacsClause := by
            cases hd : detectIte c.g k hk_lt with
            | none =>
              have ⟨_, _, h, _⟩ := pass1_succ_true_and c.g (marksToBool c.marks) root hk_lt hm_t hd
              unfold gateClauses; rw [hd]; exact h
            | some ctf =>
              rcases ctf with ⟨ic, it, if_⟩
              have ⟨_, _, h, _⟩ := pass1_succ_true_ite c.g (marksToBool c.marks) root hk_lt hm_t hd
              unfold gateClauses; rw [hd]; exact h
          have hk_le_tot := pass1Bytes_len_mono (marksToBool c.marks) (root := root)
            hk_le (Nat.le_refl _)
          have hle_next := pass1Bytes_len_mono (marksToBool c.marks) (root := root)
            (by omega : k + 1 ≤ c.g.nodes.size) (Nat.le_refl _)
          dsimp only [p1Bytes] at hcur_eq hml hbuf_fit ⊢
          have hlen_g : (pass1Bytes c.g (marksToBool c.marks) (k + 1)).length =
              (pass1Bytes c.g (marksToBool c.marks) k).length +
                ((gateClauses c.g k hk_lt).flatMap encodeDimacsClause).length := by
            rw [hbs_s, List.length_append]
          have hlen_step : (pass1Bytes c.g (marksToBool c.marks) c.g.nodes.size).length -
              (pass1Bytes c.g (marksToBool c.marks) k).length =
              ((gateClauses c.g k hk_lt).flatMap encodeDimacsClause).length +
              ((pass1Bytes c.g (marksToBool c.marks) c.g.nodes.size).length -
                (pass1Bytes c.g (marksToBool c.marks) (k + 1)).length) := by omega
          have hcur_nat : curP.toNat =
              bufStart.toNat + (pass1Bytes c.g (marksToBool c.marks) k).length := by
            rw [hcur_eq, bv64_add_ofNat_toNat (by omega)]
          rw [← hcur_eq, hlen_step] at hml
          have hsp := region_split_prefix (by omega) hml
          refine wp_pass2GateStep Γ hWriteLit hWriteEnd Q X c.aigPtr c.hdr.num_atoms c.g c.aigUsed
            k hk_lt (BitVec.ofNat 32 (c.g.A + 1 + k)) curP
            (region (curP + BitVec.ofNat 64 ((gateClauses c.g k hk_lt).flatMap
                encodeDimacsClause).length)
              ((pass1Bytes c.g (marksToBool c.marks) c.g.nodes.size).length -
                (pass1Bytes c.g (marksToBool c.marks) (k + 1)).length) ⋆
              bytes bufStart (pass1Bytes c.g (marksToBool c.marks) k) ⋆
              bytes c.marksPtr c.marks ⋆ R)
            ml _ c.num_atoms c.wf c.aig_w
            (by rw [haig_l, hlen]) hidx_eq (by have := c.bd_nat; omega)
            (by omega) (sep_ac hsp) fun m' hm' => ?_
          have hptr_eq : curP + BitVec.ofNat 64 ((gateClauses c.g k hk_lt).flatMap
                encodeDimacsClause).length =
              bufStart + BitVec.ofNat 64 (pass1Bytes c.g (marksToBool c.marks) (k + 1)).length := by
            rw [hcur_eq, ptr_add_ofNat, hlen_g]
          have hm'' : bufAt bufStart (p1Bytes c (k + 1))
              ((p1Bytes c c.g.nodes.size).length - (p1Bytes c (k + 1)).length)
              (array64 c.aigPtr c.aigUsed ⋆ bytes c.marksPtr c.marks ⋆ R) m' := by
            have hb := buf_append_step (base := bufStart)
              (pref := pass1Bytes c.g (marksToBool c.marks) k)
              (bs := (gateClauses c.g k hk_lt).flatMap encodeDimacsClause)
              (rem := (pass1Bytes c.g (marksToBool c.marks) c.g.nodes.size).length -
                (pass1Bytes c.g (marksToBool c.marks) (k + 1)).length)
              (R := array64 c.aigPtr c.aigUsed ⋆ bytes c.marksPtr c.marks ⋆ R)
              (by omega) (by rw [← hcur_eq]; exact sep_ac hm')
            rw [← hbs_s] at hb; exact hb
          c0_hsteps; rw [hptr_eq]; exact hJ1 _ m' ⟨rfl, hm''⟩
        · have hm_f := mark_getD_false_of_bv rfl hidx_eq hg_lt hc
          have ⟨_, _, hbs_s, _⟩ := pass1_succ_false c.g (marksToBool c.marks) root hk_lt hm_f
          dsimp only [p1Bytes] at hcur_eq hml
          rw [← hbs_s] at hcur_eq hml; exact hJ1 curP ml ⟨hcur_eq, hml⟩
    · have hk_end : k = c.g.nodes.size := by c0_bv_omega [hc, hlen, hbd]
      subst hk_end; rw [Nat.sub_self, region_zero, emp_sep] at hml
      dsimp only; rw [hcur_eq]; exact hkDone ml (sep_ac hml)

private theorem wp_postPass1 (Γ : Env) (hDecLen : HypDecLen Γ) (hWriteLit : HypWriteLit Γ)
    (hWriteHdr : HypWriteHdr Γ) (hWriteEnd : HypWriteEnd Γ)
    (Q : Post [Ty.bool]) (X : XPost) (c : CoiCtx) (R : Mem 64 → Prop) (m : Mem 64)
    (root : BitVec 32) (mv nc : Val i32) (bb : Val i64) (hroot : root ≠ 0#32)
    (hmv_eq : mv.toNat = pass1Mv c.g (marksToBool c.marks) root c.g.nodes.size)
    (hnc_eq : nc.toNat = pass1Nc c.g (marksToBool c.marks) c.g.nodes.size)
    (hbb_eq : bb.toNat = pass1BodyBytes c.g (marksToBool c.marks) root c.g.nodes.size)
    (hmv_bd : mv.toNat < bvDimacsBound) (hnc_bd : nc.toNat < bvDimacsBound)
    (hm : (bvCoiMem c.workBase c.aigPtr c.marksPtr c.avail c.hdr c.aigUsed c.marks ⋆ R) m)
    (hQ : DimacsPost c root R Q) :
    wp Γ Q X (postPass1Expr c.workBase root c.hdr.aig_len c.hdr.num_atoms c.marksPtr c.aigPtr
      mv nc bb) m := by
  have hcoi : (coiCoreMem c c.hdr (c.workBase.toNat + c.avail) ⋆ R) m := by
    unfold bvCoiMem at hm; dsimp only [coiCoreMem]; exact sep_ac hm
  dsimp only [coiCoreMem] at hcoi
  have hbd := c.bd; have hfit := c.fit; have hwe_nat := c.we_nat; have hfl_nat := c.fl_nat
  have hmptr_nat := c.mptr_nat; have hm_ub := c.marks_ub
  unfold postPass1Expr
  refine wp_decLen_call Γ hDecLen _ m _ ?_; c0_hsteps_nogrp
  refine wp_decLen_call Γ hDecLen _ m _ ?_; c0_hsteps_nogrp
  have hmv_le := natToBytes_length_le_10 mv.isLt; have hnc_le := natToBytes_length_le_10 nc.isLt
  have hbb_le : bb.toNat ≤ 14 + 40 * bvDimacsBound := by
    rw [hbb_eq]; have := pass1BodyBytes_lt_pow64 (g := c.g) (marks := marksToBool c.marks)
      (root := root) c.bd_nat (k := c.g.nodes.size)
    unfold bvDimacsBound at hnc_bd ⊢; omega
  have ⟨hmv_s, hnc_s, hlen_enc, henc_eq⟩ := pass1_end_eq c.g (marksToBool c.marks) root hroot
  let tot := 8#64 + BitVec.ofNat 64 (natToBytes mv.toNat).length +
    BitVec.ofNat 64 (natToBytes nc.toNat).length + bb
  have hb_bd : 8 + (natToBytes mv.toNat).length + (natToBytes nc.toNat).length + bb.toNat <
      2 ^ 64 := by unfold bvDimacsBound at hbb_le; omega
  have hsum_tot := (bv64_tot_toNat hb_bd).symm
  have htot_nat : tot.toNat = (encodeDimacs (tseitinCnf c root)).length := by
    rw [← hsum_tot, hmv_eq, hnc_eq, hbb_eq, hlen_enc]
  refine wp_join0 (fun ml => ml = m) (fun _ _ hml => hml ▸ wp_coiOomRet Γ Q X c R m hm
    (fun hdr' m' => (hQ false hdr' m').2 rfl)) fun _ hJ => ?_
  c0_hsteps_nogrp
  · exact hJ m rfl
  · exact hJ m rfl
  · rename_i hc1 hc2; clear hc2
    rw [hsum_tot, Nat.mod_eq_of_lt (by omega : tot.toNat < 2 ^ 64),
      Nat.mod_eq_of_lt (by decide : 4294967295 < 2 ^ 64)] at hc1
    rw [hsum_tot, Nat.mod_eq_of_lt (by omega : tot.toNat < 2 ^ 64)] at hc
    have htot_u32 : tot.toNat ≤ 4294967295 := by omega
    have h_ma : (c.hdr.marks_ptr.toNat + c.hdr.aig_len.toNat) % 2 ^ 64 =
        c.marksPtr.toNat + c.marks.length := by
      rw [c.marks_hdr, ← c.marks_l, Nat.mod_eq_of_lt (by omega)]
    rw [h_ma, hwe_nat] at hc
    have htot_rem :
        tot.toNat ≤ c.workBase.toNat + c.avail - (c.marksPtr.toNat + c.marks.length) := by omega
    clear hc hc1
    let dstart := c.hdr.work_end - tot
    have hst_nat : dstart.toNat = c.workBase.toNat + c.avail - tot.toNat := by
      rw [bv64_sub_toNat (by rw [hwe_nat]; omega), hwe_nat]
    have hm_ge : c.marksPtr.toNat + c.marks.length ≤ dstart.toNat := by omega
    have hm_tail := bvCoiTail_to_prefixRegion hfit hm_ge (dbsLen := tot.toNat)
      (by rw [hst_nat]; omega) hm
    let hdrBs := dimacsHeaderPrefix ++ natToBytes mv.toNat ++ [asciiSpace] ++
      natToBytes nc.toNat ++ [asciiNewline]
    let p1Bs := p1Bytes c c.g.nodes.size
    let rLitBs := encodeDimacsLit (litToDimacs (UInt32.ofBitVec root))
    have henc_split : encodeDimacs (tseitinCnf c root) =
        hdrBs ++ p1Bs ++ rLitBs ++ [asciiZero, asciiNewline] := by
      rw [henc_eq, ← hmv_s, ← hmv_eq, ← hnc_s, ← hnc_eq, encodeDimacsClause_ofLiterals]
      simp [hdrBs, p1Bs, rLitBs, List.append_assoc]
    have htot_sum : tot.toNat = hdrBs.length + (p1Bs.length + (rLitBs.length + 2)) := by
      rw [htot_nat, henc_split]; simp [List.length_append]
    rw [htot_sum] at hm_tail
    c0_call hWriteHdr
    refine ⟨region (dstart + BitVec.ofNat 64 hdrBs.length) (p1Bs.length + (rLitBs.length + 2)) ⋆
        coiCoreMem c c.hdr dstart.toNat ⋆ R,
      by dsimp only [hdrBs] at *; rw [hst_nat]; omega,
      by dsimp only [dstart, tot, hdrBs, coiCoreMem] at *
         exact sep_ac (region_split_prefix (by omega) hm_tail),
      fun m1 hm1 => ?_⟩
    clear hm; c0_hsteps_nogrp
    have hm1' : bufAt dstart hdrBs (p1Bs.length + (rLitBs.length + 2))
        (coiCoreMem c c.hdr dstart.toNat ⋆ R) m1 := by
      dsimp only [dstart, tot, hdrBs, bufAt, coiCoreMem] at hm1 ⊢
      simp only [List.append_assoc] at hm1 ⊢; exact sep_ac hm1
    have hs_p1 := region_split_prefix (by omega) hm1'
    have hbuf_fit : (dstart + BitVec.ofNat 64 hdrBs.length).toNat + p1Bs.length < 2 ^ 64 := by
      rw [bv64_add_ofNat_toNat (by rw [hst_nat]; omega), hst_nat]; omega
    refine wp_pass2Expr Γ hWriteLit hWriteEnd Q X c (dstart + BitVec.ofNat 64 hdrBs.length)
      (bytes dstart hdrBs ⋆ region (dstart + BitVec.ofNat 64 hdrBs.length +
        BitVec.ofNat 64 p1Bs.length) (rLitBs.length + 2) ⋆ coiRestMem c c.hdr dstart.toNat ⋆ R)
      m1 root (c.hdr.num_atoms + 1#32) _ c.g0_bv hbuf_fit
      (by dsimp only [coiCoreMem, coiRestMem] at hs_p1 ⊢; exact sep_ac hs_p1) fun m2 hm2 => ?_
    have hm2' : bufAt dstart (hdrBs ++ p1Bs) (rLitBs.length + 2)
        (coiCoreMem c c.hdr dstart.toNat ⋆ R) m2 :=
      buf_append_step (by rw [hst_nat, htot_sum]; omega)
        (by dsimp only [coiCoreMem, coiRestMem] at hm2 ⊢; exact sep_ac hm2)
    have hr_l : (encodeDimacsLit (litToDimacs (UInt32.ofBitVec root))).length = rLitBs.length := rfl
    refine wp_writeLit_pref Γ hWriteLit (base := dstart) (pref := hdrBs ++ p1Bs) (rem := 2)
      (R := coiCoreMem c c.hdr dstart.toNat ⋆ R)
      (by rw [ptr_add_ofNat, ← List.length_append (as := hdrBs) (bs := p1Bs)]) rfl
      (by dsimp only [p1Bs, rLitBs, bufAt, coiCoreMem] at hm2' ⊢
          rw [ptr_add_ofNat,
            ← List.length_append (as := hdrBs) (bs := p1Bytes c c.g.nodes.size)]
          exact sep_ac hm2')
      (by rw [hst_nat, htot_sum, List.length_append (as := hdrBs) (bs := p1Bs), hr_l]; omega)
      fun m3 hm3 => ?_
    refine wp_writeEnd_pref Γ hWriteEnd (rem := 0) hm3
      (by rw [hst_nat, htot_sum, List.length_append (as := hdrBs ++ p1Bs) (bs := rLitBs),
        List.length_append (as := hdrBs) (bs := p1Bs), hr_l]; omega) fun m4 hm4 => ?_
    rw [bufAt, region_zero, emp_sep, ← henc_split] at hm4
    dsimp only [coiCoreMem] at hm4; c0_hsteps!
    let hdr' : BVHdrState := { c.hdr with dimacs_start := dstart, dimacs_len := tot.setWidth 32 }
    have hm4_hd : (coiCoreMem c hdr' dstart.toNat ⋆
        bytes dstart (encodeDimacs (tseitinCnf c root)) ⋆ R) m := by
      dsimp only [hdr', dstart, tot, coiCoreMem] at hm ⊢; exact sep_ac hm
    have hm4_fin := bvCoiMem_to_dimacsSep hfit c.aig_ge c.marks_eq (by omega) hm_ge
      (dbs := encodeDimacs (tseitinCnf c root)) (by rw [hst_nat, htot_nat]; omega)
      (by dsimp only [coiCoreMem] at hm4_hd; exact hm4_hd)
    have haig_ge := c.aig_ge; have haig_end := c.aig_end
    refine (hQ true hdr' m).1 rfl ⟨validDimacs_tseitin_of_counts (marksToBool c.marks)
      (by rw [← hmv_s, ← hmv_eq]; unfold dimacsBound; unfold bvDimacsBound at hmv_bd; omega)
      (by rw [← hnc_s, ← hnc_eq]; unfold dimacsBound; unfold bvDimacsBound at hnc_bd; omega),
      by dsimp only [hdr']; rw [hst_nat, htot_nat]; omega,
      by dsimp only [hdr']; rw [BitVec.toNat_setWidth,
        Nat.mod_eq_of_lt (by omega : tot.toNat < 2 ^ 32), htot_nat],
      by dsimp only [hdr']; rw [hst_nat]; omega, hm4_fin⟩

public section

/-- Canonical `Γ`-parametric `Func.wp` proof for `bv_dimacs_write_body`. -/
theorem bv_dimacs_write_wp (Γ : Env)
    (hDecLen : ∀ xs m Q X, bvDecLenSpec xs m Q X → Γ "bv_dec_len" [i32] [i64] xs m Q X)
    (hLitBytes : ∀ xs m Q X, bvLitBytesSpec xs m Q X → Γ "bv_lit_bytes" [i32] [i64] xs m Q X)
    (hWriteLit : ∀ xs m Q X, bvWriteLitSpec xs m Q X → Γ "bv_write_lit" [i64, i32] [i64] xs m Q X)
    (hWriteHdr : ∀ xs m Q X, bvWriteDimacsHdrSpec xs m Q X →
      Γ "bv_write_dimacs_hdr" [i64, i32, i32] [i64] xs m Q X)
    (hWriteEnd : ∀ xs m Q X, bvWriteClauseEndSpec xs m Q X →
      Γ "bv_write_clause_end" [i64] [i64] xs m Q X) :
    ∀ xs m Q X, bvDimacsWriteSpec xs m Q X → Func.wp Γ bv_dimacs_write_body xs m Q X := by
  rintro ⟨h, root, ⟨⟩⟩ m Q X ⟨workBase, aigPtr, marksPtr, avail, hdr, g, aigUsed, marks, R,
    heq_h, hfit, hwb, hwe, haig_hdr, hmptr_hdr, haig_ge, hmptr_eq, haig_end, hwf, hA, hlen, hbd,
    haig_w, haig_l, hm_l, hroot_lt, hmptr_ne, hm, hQ⟩
  rw [heq_h] at *
  let c : CoiCtx := ⟨workBase, aigPtr, marksPtr, avail, hdr, g, aigUsed, marks, hfit, hwb, hwe,
    haig_hdr, hmptr_hdr, haig_ge, hmptr_eq, haig_end, hwf, hA, hlen, hbd, haig_w, haig_l, hm_l,
    hmptr_ne⟩
  change wp Γ Q X (bv_dimacs_write_body Val Cont (workBase, root, ())) m
  rw [bv_dimacs_write_eq_topBody]; unfold topBody; c0_hsteps_nogrp
  · have hr0 : root = 0#32 := hc; subst hr0
    exact wp_root0Body Γ hWriteHdr hWriteEnd Q X c R m hm
      (by dsimp only [c, DimacsPost, tseitinCnf]; exact hQ)
  · have hroot_ne : root ≠ 0#32 := hc
    have hcoi := hm; unfold bvCoiMem at hcoi
    c0_hsteps_nogrp
    refine wp_join0 (fun ml => ml = m) (fun _ _ hml => hml ▸ wp_coiOomRet Γ Q X c R m hm
      (fun hdr' m' => (hQ false hdr' m').2 rfl)) fun _ hJ => ?_
    c0_hsteps_nogrp
    · exact hJ m rfl
    · exact wp_coiOomRet Γ Q X c R m hm (fun hdr' m' => (hQ false hdr' m').2 rfl)
    · have hmv0 : ((root >>> (1 : Nat)) + 1#32).toNat = (root >>> 1).toNat + 1 :=
        bv32_lsr1_add1_toNat root
      have hmv0_lt : ((root >>> (1 : Nat)) + 1#32).toNat < bvDimacsBound := by
        have : (root >>> 1).toNat < hdr.aig_len.toNat := hroot_lt
        rw [hmv0]; unfold bvDimacsBound at hbd ⊢; omega
      rw [haig_hdr, hmptr_hdr]
      refine wp_litBytes_call Γ hLitBytes _ m _ ?_; c0_hsteps_nogrp
      have hbb0_eq : (BitVec.ofNat 64
          (encodeDimacsLit (litToDimacs (UInt32.ofBitVec root))).length + 2#64).toNat =
          pass1BodyBytes g (marksToBool marks) root 0 := by
        have hle := encodeDimacsLit_length_le_bv root
        rw [bv64_add_ofNat_toNat (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : (encodeDimacsLit _).length < 2 ^ 64),
          (pass1_zero g (marksToBool marks) root).2.2.2]
      exact wp_pass1Expr Γ hDecLen hLitBytes Q X c R m root _ _ _ _
        (by dsimp only; rw [hmv0, (pass1_zero g (marksToBool marks) root).1]) hbb0_eq hmv0_lt
        c.g0_bv hm (fun hdr' m' => (hQ false hdr' m').2 rfl)
        fun mv nc bb hmv_eq hnc_eq hbb_eq hmv_bd hnc_bd =>
        wp_postPass1 Γ hDecLen hWriteLit hWriteHdr hWriteEnd Q X c R m root mv nc bb
          hroot_ne hmv_eq hnc_eq hbb_eq hmv_bd hnc_bd hm
          (by dsimp only [c, DimacsPost, tseitinCnf]; exact hQ)

end

end LeanQbe.T.Examples.Bitblast.Proof
