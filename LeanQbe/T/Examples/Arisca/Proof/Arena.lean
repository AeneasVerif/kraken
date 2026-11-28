/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Src.Header
public import LeanQbe.T.Logic.Mem
public import LeanQbe.T.Logic.Bytes
public import LeanQbe.T.Logic.Rules
public import LeanQbe.T.Logic.SepTree
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.SlabChain
import LeanQbe.T.Logic.Cells
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0StepAttr
meta import LeanQbe.T.Logic.C0StepAttr
import Kraken.Separation

/-!
# ARiSCA `ArCtx` Layout, `arCtxMem` Accessors, & Header Primitive WPs (`Arisca.Proof.Arena`)

Defines:
- `ArCtxState` (`776 B`: `77 × u64` + `40 × u32`) and `SepTree`-backed `arCtxMem`
- Global `@[c0_load]` / `@[c0_store]` accessors for all scalar and embedded-array fields
- `SlabChain`-backed `region cx 776 ↔ ∃ s, arCtxMem cx s` conversions
- `u32LE` / `wordAt` and WP contracts + proofs for `ar_rd32`, `ar_next_word`, and `ar_aalloc`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Arisca.Proof

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Arisca.Src
open LeanQbe.T.Examples.Arisca.Src.Header
open Kraken.Bedrock2.Test

@[expose] public section

/-! ## 1. `ArCtxState` & `SepTree`-Backed `arCtxMem` (`776 B`) -/

/-- Logical mirror of the `776`-byte C0 `ArCtx` struct (`56` `u64` scalars, `8` `u64` arrays,
`22` `u32` scalars, `5` `u32` arrays). -/
structure ArCtxState where
  w : BitVec 64
  wlen : BitVec 64
  top : BitVec 64
  mlo : BitVec 64
  mhi : BitVec 64
  rhs0 : BitVec 64
  rhs1 : BitVec 64
  olit : BitVec 64
  art : BitVec 64
  nw : BitVec 64
  pos : BitVec 64
  bind : BitVec 64
  in_net : BitVec 64
  out_ref : BitVec 64
  rule_off : BitVec 64
  rule_n : BitVec 64
  partner : BitVec 64
  flipped : BitVec 64
  stk_n : BitVec 64
  stk_p : BitVec 64
  memo_n : BitVec 64
  memo_v : BitVec 64
  dense : BitVec 64
  gsy : BitVec 64
  gcl : BitVec 64
  gch : BitVec 64
  g_lmask : List (BitVec 64)
  g_tin : List (BitVec 64)
  g_tto : List (BitVec 64)
  rs_m : BitVec 64
  rs_l : BitVec 64
  rs_h : BitVec 64
  rs_pool : BitVec 64
  rs_ptop : BitVec 64
  rs_pcap : BitVec 64
  tm : List (BitVec 64)
  ts : List (BitVec 64)
  tl : List (BitVec 64)
  th : List (BitVec 64)
  pool : List (BitVec 64)
  ptop : BitVec 64
  pcap : BitVec 64
  qm : BitVec 64
  qs : BitVec 64
  ql : BitVec 64
  qh : BitVec 64
  ix : BitVec 64
  ix2 : BitVec 64
  bx : BitVec 64
  vq_off : BitVec 64
  vq : BitVec 64
  vq_skip : BitVec 64
  rm : BitVec 64
  rm2 : BitVec 64
  rl : BitVec 64
  rh : BitVec 64
  rl2 : BitVec 64
  rh2 : BitVec 64
  rpool : BitVec 64
  rpcap : BitVec 64
  cur_rm : BitVec 64
  cur_rl : BitVec 64
  cur_rh : BitVec 64
  cur_rp : BitVec 64
  n_out : BitVec 32
  M : BitVec 32
  I : BitVec 32
  A : BitVec 32
  O : BitVec 32
  spec : BitVec 32
  n_in : BitVec 32
  n_nets : BitVec 32
  n_gates : BitVec 32
  n_cones : BitVec 32
  n_main : BitVec 32
  rs_n : BitVec 32
  rs_cap : BitVec 32
  tc : BitVec 32
  tn : BitVec 32
  tcap : BitVec 32
  pc : BitVec 32
  qn : BitVec 32
  qcap : BitVec 32
  rcap : BitVec 32
  cur_nr : BitVec 32
  g_outs : List (BitVec 32)
  g_innet : List (BitVec 32)
  g_inneg : List (BitVec 32)
  g_lnode : List (BitVec 32)
  g_vs : List (BitVec 32)
  pad_end : BitVec 32

/-- Modulus bitwidth (`n_out / 2` in `SPEC_MITER` `spec = 2`, else `n_out`). -/
def ArCtxState.modW (s : ArCtxState) : Nat :=
  if s.spec = 2#32 then s.n_out.toNat / 2 else s.n_out.toNat

/-- `26` leading `u64` words of `ArCtxState` (`+0 .. +200`). -/
def ArCtxState.blk0 (s : ArCtxState) : List (BitVec 64) :=
  [ s.w, s.wlen, s.top, s.mlo, s.mhi, s.rhs0, s.rhs1, s.olit, s.art, s.nw, s.pos
  , s.bind, s.in_net, s.out_ref, s.rule_off, s.rule_n, s.partner, s.flipped
  , s.stk_n, s.stk_p, s.memo_n, s.memo_v, s.dense, s.gsy, s.gcl, s.gch ]

/-- `6` rule-store `u64` words of `ArCtxState` (`+296 .. +336`). -/
def ArCtxState.blk1 (s : ArCtxState) : List (BitVec 64) :=
  [ s.rs_m, s.rs_l, s.rs_h, s.rs_pool, s.rs_ptop, s.rs_pcap ]

/-- `24` trailing `u64` words of `ArCtxState` (`+424 .. +608`). -/
def ArCtxState.blk2 (s : ArCtxState) : List (BitVec 64) :=
  [ s.ptop, s.pcap, s.qm, s.qs, s.ql, s.qh, s.ix, s.ix2, s.bx, s.vq_off, s.vq, s.vq_skip
  , s.rm, s.rm2, s.rl, s.rh, s.rl2, s.rh2, s.rpool, s.rpcap
  , s.cur_rm, s.cur_rl, s.cur_rh, s.cur_rp ]

/-- `21` scalar `u32` words of `ArCtxState` (`+616 .. +696`). -/
def ArCtxState.u32Blk (s : ArCtxState) : List (BitVec 32) :=
  [ s.n_out, s.M, s.I, s.A, s.O, s.spec, s.n_in, s.n_nets, s.n_gates, s.n_cones, s.n_main
  , s.rs_n, s.rs_cap, s.tc, s.tn, s.tcap, s.pc, s.qn, s.qcap, s.rcap, s.cur_nr ]

/-- Length invariant for the `13` fixed embedded arrays of `ArCtxState`. -/
structure ArCtxLengthsOk (s : ArCtxState) : Prop where
  g_lmask : s.g_lmask.length = 6
  g_tin : s.g_tin.length = 3
  g_tto : s.g_tto.length = 2
  tm : s.tm.length = 2
  ts : s.ts.length = 2
  tl : s.tl.length = 2
  th : s.th.length = 2
  pool : s.pool.length = 2
  g_outs : s.g_outs.length = 2
  g_innet : s.g_innet.length = 3
  g_inneg : s.g_inneg.length = 3
  g_lnode : s.g_lnode.length = 6
  g_vs : s.g_vs.length = 4

/-- Balanced `18`-leaf `SepTree` for `ArCtx` at `cx`. -/
def arCtxTree (cx : BitVec 64) (s : ArCtxState) : SepTree :=
  .node
    (.node
      (.node
        (.node (.leaf (array64 cx s.blk0)) (.leaf (array64 (cx + 208) s.g_lmask)))
        (.node (.leaf (array64 (cx + 256) s.g_tin)) (.leaf (array64 (cx + 280) s.g_tto))))
      (.node
        (.node (.leaf (array64 (cx + 296) s.blk1)) (.leaf (array64 (cx + 344) s.tm)))
        (.node (.leaf (array64 (cx + 360) s.ts))
          (.node (.leaf (array64 (cx + 376) s.tl)) (.leaf (array64 (cx + 392) s.th))))))
    (.node
      (.node
        (.node (.leaf (array64 (cx + 408) s.pool)) (.leaf (array64 (cx + 424) s.blk2)))
        (.node (.leaf (array (t := i32) (cx + 616) s.u32Blk))
          (.leaf (array (t := i32) (cx + 700) s.g_outs))))
      (.node
        (.node (.leaf (array (t := i32) (cx + 708) s.g_innet))
          (.leaf (array (t := i32) (cx + 720) s.g_inneg)))
        (.node (.leaf (array (t := i32) (cx + 732) s.g_lnode))
          (.node (.leaf (array (t := i32) (cx + 756) s.g_vs))
            (.leaf (cell (t := i32) (cx + 772) s.pad_end))))))

/-- Exact `776`-byte separation predicate for `ArCtx` at `cx`, carrying `ArCtxLengthsOk s`. -/
def arCtxMem (cx : BitVec 64) (s : ArCtxState) : Mem 64 → Prop :=
  fun m => ArCtxLengthsOk s ∧ (arCtxTree cx s).eval m

end

/-! ## 2. `ArCtx` Length Preservation & `SlabChain` Region Equivalence -/

public section

private def pBlk0 : List Bool := [false, false, false, false]
private def pGLmask : List Bool := [false, false, false, true]
private def pGTin : List Bool := [false, false, true, false]
private def pGTto : List Bool := [false, false, true, true]
private def pBlk1 : List Bool := [false, true, false, false]
private def pTm : List Bool := [false, true, false, true]
private def pTs : List Bool := [false, true, true, false]
private def pTl : List Bool := [false, true, true, true, false]
private def pTh : List Bool := [false, true, true, true, true]
private def pPool : List Bool := [true, false, false, false]
private def pBlk2 : List Bool := [true, false, false, true]
private def pU32Blk : List Bool := [true, false, true, false]
private def pGOuts : List Bool := [true, false, true, true]
private def pGInnet : List Bool := [true, true, false, false]
private def pGInneg : List Bool := [true, true, false, true]
private def pGLnode : List Bool := [true, true, true, false]
private def pGVs : List Bool := [true, true, true, true, false]
private def pPadEnd : List Bool := [true, true, true, true, true]

private theorem lengths_same {s s' : ArCtxState} (h : ArCtxLengthsOk s)
    (h1 : s'.g_lmask.length = s.g_lmask.length := by rfl)
    (h2 : s'.g_tin.length = s.g_tin.length := by rfl)
    (h3 : s'.g_tto.length = s.g_tto.length := by rfl)
    (h4 : s'.tm.length = s.tm.length := by rfl)
    (h5 : s'.ts.length = s.ts.length := by rfl)
    (h6 : s'.tl.length = s.tl.length := by rfl)
    (h7 : s'.th.length = s.th.length := by rfl)
    (h8 : s'.pool.length = s.pool.length := by rfl)
    (h9 : s'.g_outs.length = s.g_outs.length := by rfl)
    (h10 : s'.g_innet.length = s.g_innet.length := by rfl)
    (h11 : s'.g_inneg.length = s.g_inneg.length := by rfl)
    (h12 : s'.g_lnode.length = s.g_lnode.length := by rfl)
    (h13 : s'.g_vs.length = s.g_vs.length := by rfl) : ArCtxLengthsOk s' :=
  ⟨h1.trans h.g_lmask, h2.trans h.g_tin, h3.trans h.g_tto, h4.trans h.tm, h5.trans h.ts,
   h6.trans h.tl, h7.trans h.th, h8.trans h.pool, h9.trans h.g_outs, h10.trans h.g_innet,
   h11.trans h.g_inneg, h12.trans h.g_lnode, h13.trans h.g_vs⟩

private def arCtxSegs (s : ArCtxState) (hl : ArCtxLengthsOk s) : List SlabSeg :=
  [ SlabSeg.ofArray64 s.blk0 26 rfl
  , SlabSeg.ofArray64 s.g_lmask 6 hl.g_lmask
  , SlabSeg.ofArray64 s.g_tin 3 hl.g_tin
  , SlabSeg.ofArray64 s.g_tto 2 hl.g_tto
  , SlabSeg.ofArray64 s.blk1 6 rfl
  , SlabSeg.ofArray64 s.tm 2 hl.tm
  , SlabSeg.ofArray64 s.ts 2 hl.ts
  , SlabSeg.ofArray64 s.tl 2 hl.tl
  , SlabSeg.ofArray64 s.th 2 hl.th
  , SlabSeg.ofArray64 s.pool 2 hl.pool
  , SlabSeg.ofArray64 s.blk2 24 rfl
  , SlabSeg.ofArrayExact i32 s.u32Blk 84 rfl
  , SlabSeg.ofArrayExact i32 s.g_outs 8 (by simp [Ty.bytes, Ty.size, hl.g_outs])
  , SlabSeg.ofArrayExact i32 s.g_innet 12 (by simp [Ty.bytes, Ty.size, hl.g_innet])
  , SlabSeg.ofArrayExact i32 s.g_inneg 12 (by simp [Ty.bytes, Ty.size, hl.g_inneg])
  , SlabSeg.ofArrayExact i32 s.g_lnode 24 (by simp [Ty.bytes, Ty.size, hl.g_lnode])
  , SlabSeg.ofArrayExact i32 s.g_vs 16 (by simp [Ty.bytes, Ty.size, hl.g_vs])
  , SlabSeg.ofCell i32 s.pad_end ]

private theorem arCtxSegs_totalBytes (s : ArCtxState) (hl : ArCtxLengthsOk s) :
    SlabChain.totalBytes (arCtxSegs s hl) = 776 := by
  simp [arCtxSegs, SlabChain.totalBytes, SlabSeg.ofArray64, SlabSeg.ofArrayExact, SlabSeg.ofCell,
    Ty.bytes, Ty.size]

private theorem arCtxTree_eval_eq_slab (cx : BitVec 64) (s : ArCtxState) (hl : ArCtxLengthsOk s) :
    (arCtxTree cx s).eval = SlabChain.eval cx (arCtxSegs s hl) := by
  simp only [arCtxTree, SepTree.eval, SlabChain.eval, arCtxSegs,
    SlabSeg.ofArray64, SlabSeg.ofArrayExact, SlabSeg.ofCell, Ty.bytes, Ty.size,
    ptr_add_ofNat, Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat, sep_emp]
  ac_rfl

theorem arCtxMem_to_region {cx : BitVec 64} {s : ArCtxState} {m : Mem 64}
    (hm : arCtxMem cx s m) : region cx 776 m := by
  rcases hm with ⟨hl, ht⟩
  rw [arCtxTree_eval_eq_slab cx s hl] at ht
  exact SlabChain.to_region_eq (arCtxSegs_totalBytes s hl) (by decide) ht

private theorem region_to_array64 {a : BitVec 64} (k : Nat) (hk : 8 * k ≤ 2 ^ 64) {m : Mem 64}
    (hm : region a (8 * k) m) :
    ∃ xs : List (BitVec 64), xs.length = k ∧ array64 a xs m := by
  obtain ⟨xs, hlen, hmem⟩ := region_to_word8Array k hk hm
  have hconv : ∀ (a : BitVec 64) (xs : List (BitVec 64)), word8Array a xs = array64 a xs := by
    intro a xs
    induction xs generalizing a with
    | nil => rfl
    | cons x xs ih =>
      rw [word8Array_cons, array64_cons, ih]
      congr 1; unfold word8 cell64
      rw [← Int.toBytes_emod, ← Int.toBytes_emod (x := x.toInt)]
      congr 1; simp only [Int.take]
      rw [BitVec.toInt_eq_msb_cond]
      have h0 : 0 ≤ (x.toNat : Int) := Int.natCast_nonneg _
      have hlt : (x.toNat : Int) < ((2 ^ 64 : Nat) : Int) := by exact_mod_cast x.isLt
      cases x.msb
      · simp
      · simp only [↓reduceIte]
        rw [show (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) from rfl, Int.sub_emod_right,
          Int.emod_eq_of_lt h0 hlt]
  rw [hconv] at hmem
  exact ⟨xs, hlen, hmem⟩

private theorem region_to_array32 {a : BitVec 64} (k : Nat) (hk : 4 * k ≤ 2 ^ 64) {m : Mem 64}
    (hm : region a (4 * k) m) :
    ∃ xs : List (BitVec 32), xs.length = k ∧ array (t := i32) a xs m := by
  obtain ⟨xs, hlen, hmem⟩ := region_to_int4Array k hk hm
  have hconv : ∀ (a : BitVec 64) (xs : List (BitVec 64)),
      int4Array a xs = array (t := i32) a (xs.map (BitVec.setWidth 32)) := by
    intro a xs
    induction xs generalizing a with
    | nil => rfl
    | cons x xs ih =>
      rw [int4Array_cons, List.map_cons, array_cons, ih]
      congr 1; unfold int4 cell toBits Ty.bytes Ty.size
      have hsw : ((x.setWidth 32).setWidth 32).toInt = (x.setWidth 32).toInt := by
        rw [show (x.setWidth 32).setWidth 32 = x.setWidth 32 from
          BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_setWidth])]
      have htb : Int.toBytes 4 (x.toNat : Int) = Int.toBytes 4 (x.setWidth 32).toInt := by
        rw [← Int.toBytes_emod, ← Int.toBytes_emod (x := (x.setWidth 32).toInt)]
        congr 1; simp only [Int.take]
        have h0 : 0 ≤ ((x.setWidth 32).toNat : Int) := Int.natCast_nonneg _
        have hlt : ((x.setWidth 32).toNat : Int) < ((2 ^ 32 : Nat) : Int) := by
          exact_mod_cast (x.setWidth 32).isLt
        have htoNat :
            (x.toNat : Int) % ((2 ^ 32 : Nat) : Int) = ((x.setWidth 32).toNat : Int) := by
          rw [BitVec.toNat_setWidth]; exact_mod_cast rfl
        rw [show (2 : Int) ^ (8 * 4) = ((2 ^ 32 : Nat) : Int) from rfl, htoNat,
          BitVec.toInt_eq_msb_cond]
        cases (x.setWidth 32).msb
        · simp
        · simp only [↓reduceIte]; rw [Int.sub_emod_right, Int.emod_eq_of_lt h0 hlt]
      exact (hsw ▸ htb) ▸ rfl
  rw [hconv] at hmem
  exact ⟨xs.map (BitVec.setWidth 32), by simp [hlen], hmem⟩

private theorem list_eq_26 {α : Type _} (l : List α) (h : l.length = 26) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23
      a24 a25, l = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15,
        a16, a17, a18, a19, a20, a21, a22, a23, a24, a25] := by
  rcases l with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ |
      ⟨a8, _ | ⟨a9, _ | ⟨a10, _ | ⟨a11, _ | ⟨a12, _ | ⟨a13, _ | ⟨a14, _ | ⟨a15, _ | ⟨a16, _ |
      ⟨a17, _ | ⟨a18, _ | ⟨a19, _ | ⟨a20, _ | ⟨a21, _ | ⟨a22, _ | ⟨a23, _ | ⟨a24, _ | ⟨a25,
      _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp at h
  exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17,
    a18, a19, a20, a21, a22, a23, a24, a25, rfl⟩

private theorem list_eq_24 {α : Type _} (l : List α) (h : l.length = 24) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23,
      l = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15,
        a16, a17, a18, a19, a20, a21, a22, a23] := by
  rcases l with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ |
      ⟨a8, _ | ⟨a9, _ | ⟨a10, _ | ⟨a11, _ | ⟨a12, _ | ⟨a13, _ | ⟨a14, _ | ⟨a15, _ | ⟨a16, _ |
      ⟨a17, _ | ⟨a18, _ | ⟨a19, _ | ⟨a20, _ | ⟨a21, _ | ⟨a22, _ |
        ⟨a23, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp at h
  exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17,
    a18, a19, a20, a21, a22, a23, rfl⟩

private theorem list_eq_21 {α : Type _} (l : List α) (h : l.length = 21) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20,
      l = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15,
        a16, a17, a18, a19, a20] := by
  rcases l with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ |
      ⟨a8, _ | ⟨a9, _ | ⟨a10, _ | ⟨a11, _ | ⟨a12, _ | ⟨a13, _ | ⟨a14, _ | ⟨a15, _ | ⟨a16, _ |
      ⟨a17, _ | ⟨a18, _ | ⟨a19, _ | ⟨a20, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp at h
  exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17,
    a18, a19, a20, rfl⟩

private theorem list_eq_6 {α : Type _} (l : List α) (h : l.length = 6) :
    ∃ a0 a1 a2 a3 a4 a5, l = [a0, a1, a2, a3, a4, a5] := by
  rcases l with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | _⟩⟩⟩⟩⟩⟩ <;> simp at h
  exact ⟨a0, a1, a2, a3, a4, a5, rfl⟩

theorem region_to_arCtxMem {cx : BitVec 64} {m : Mem 64} (hm : region cx 776 m) :
    ∃ s : ArCtxState, arCtxMem cx s m := by
  have h1 : (region cx 616 ⋆ region (cx + 616) 160) m :=
    (congrFun (region_merge_eq (a := cx) (n1 := 616) (n2 := 160) (n := 776) rfl (by decide)) m).mpr
      hm
  obtain ⟨u64s, hu64l, u32s, hu32l, h32⟩ :
      ∃ u64s : List (BitVec 64), u64s.length = 77 ∧
        ∃ u32s : List (BitVec 32), u32s.length = 40 ∧
          (array64 cx u64s ⋆ array (t := i32) (cx + 616) u32s) m := by
    have hsp := sep_mono2
      (fun _ h1 => region_to_array64 77 (by decide) h1)
      (fun _ h2 => region_to_array32 40 (by decide) h2) m h1
    obtain ⟨u64s, ha⟩ := sep_ex_l.mp hsp
    obtain ⟨u32s, hb⟩ := sep_ex_r.mp ha
    rw [sep_pure_l, sep_pure_r] at hb
    exact ⟨u64s, hb.1, u32s, hb.2.1, hb.2.2⟩
  have split64 : array64 cx u64s =
      (array64 cx (u64s.take 26) ⋆
       array64 (cx + 208) ((u64s.drop 26).take 6) ⋆
       array64 (cx + 256) ((u64s.drop 32).take 3) ⋆
       array64 (cx + 280) ((u64s.drop 35).take 2) ⋆
       array64 (cx + 296) ((u64s.drop 37).take 6) ⋆
       array64 (cx + 344) ((u64s.drop 43).take 2) ⋆
       array64 (cx + 360) ((u64s.drop 45).take 2) ⋆
       array64 (cx + 376) ((u64s.drop 47).take 2) ⋆
       array64 (cx + 392) ((u64s.drop 49).take 2) ⋆
       array64 (cx + 408) ((u64s.drop 51).take 2) ⋆
       array64 (cx + 424) (u64s.drop 53)) := by
    have hlen : u64s = u64s.take 26 ++ (u64s.drop 26).take 6 ++ (u64s.drop 32).take 3 ++
        (u64s.drop 35).take 2 ++ (u64s.drop 37).take 6 ++ (u64s.drop 43).take 2 ++
        (u64s.drop 45).take 2 ++ (u64s.drop 47).take 2 ++ (u64s.drop 49).take 2 ++
        (u64s.drop 51).take 2 ++ u64s.drop 53 := by
      simp only [List.append_assoc]
      have h51 : (u64s.drop 51).take 2 ++ u64s.drop 53 = u64s.drop 51 := by
        rw [show 53 = 51 + 2 from rfl, ← List.drop_drop, List.take_append_drop]
      have h49 : (u64s.drop 49).take 2 ++ u64s.drop 51 = u64s.drop 49 := by
        rw [show 51 = 49 + 2 from rfl, ← List.drop_drop, List.take_append_drop]
      have h47 : (u64s.drop 47).take 2 ++ u64s.drop 49 = u64s.drop 47 := by
        rw [show 49 = 47 + 2 from rfl, ← List.drop_drop, List.take_append_drop]
      have h45 : (u64s.drop 45).take 2 ++ u64s.drop 47 = u64s.drop 45 := by
        rw [show 47 = 45 + 2 from rfl, ← List.drop_drop, List.take_append_drop]
      have h43 : (u64s.drop 43).take 2 ++ u64s.drop 45 = u64s.drop 43 := by
        rw [show 45 = 43 + 2 from rfl, ← List.drop_drop, List.take_append_drop]
      have h37 : (u64s.drop 37).take 6 ++ u64s.drop 43 = u64s.drop 37 := by
        rw [show 43 = 37 + 6 from rfl, ← List.drop_drop, List.take_append_drop]
      have h35 : (u64s.drop 35).take 2 ++ u64s.drop 37 = u64s.drop 35 := by
        rw [show 37 = 35 + 2 from rfl, ← List.drop_drop, List.take_append_drop]
      have h32 : (u64s.drop 32).take 3 ++ u64s.drop 35 = u64s.drop 32 := by
        rw [show 35 = 32 + 3 from rfl, ← List.drop_drop, List.take_append_drop]
      have h26 : (u64s.drop 26).take 6 ++ u64s.drop 32 = u64s.drop 26 := by
        rw [show 32 = 26 + 6 from rfl, ← List.drop_drop, List.take_append_drop]
      rw [h51, h49, h47, h45, h43, h37, h35, h32, h26, List.take_append_drop]
    have hl0 : (u64s.take 26).length = 26 := by simp [hu64l]
    have hl1 : ((u64s.drop 26).take 6).length = 6 := by simp [hu64l]
    have hl2 : ((u64s.drop 32).take 3).length = 3 := by simp [hu64l]
    have hl3 : ((u64s.drop 35).take 2).length = 2 := by simp [hu64l]
    have hl4 : ((u64s.drop 37).take 6).length = 6 := by simp [hu64l]
    have hl5 : ((u64s.drop 43).take 2).length = 2 := by simp [hu64l]
    have hl6 : ((u64s.drop 45).take 2).length = 2 := by simp [hu64l]
    have hl7 : ((u64s.drop 47).take 2).length = 2 := by simp [hu64l]
    have hl8 : ((u64s.drop 49).take 2).length = 2 := by simp [hu64l]
    have hl9 : ((u64s.drop 51).take 2).length = 2 := by simp [hu64l]
    conv => lhs; rw [hlen]
    repeat rw [array64_append]
    simp only [List.length_append, hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8, hl9,
      Nat.reduceAdd, Nat.reduceMul, BitVec.ofNat_eq_ofNat]
  have split32 : array (t := i32) (cx + 616) u32s =
      (array (t := i32) (cx + 616) (u32s.take 21) ⋆
       array (t := i32) (cx + 700) ((u32s.drop 21).take 2) ⋆
       array (t := i32) (cx + 708) ((u32s.drop 23).take 3) ⋆
       array (t := i32) (cx + 720) ((u32s.drop 26).take 3) ⋆
       array (t := i32) (cx + 732) ((u32s.drop 29).take 6) ⋆
       array (t := i32) (cx + 756) ((u32s.drop 35).take 4) ⋆
       cell (t := i32) (cx + 772) (u32s[39]'(by omega))) := by
    have hlen : u32s = u32s.take 21 ++ (u32s.drop 21).take 2 ++ (u32s.drop 23).take 3 ++
        (u32s.drop 26).take 3 ++ (u32s.drop 29).take 6 ++ (u32s.drop 35).take 4 ++
        [u32s[39]'(by omega)] := by
      have hd : u32s.drop 39 = [u32s[39]'(by omega)] := by
        rw [List.drop_eq_getElem_cons (by omega)]
        congr 1; simp [List.drop_eq_nil_iff, hu32l]
      rw [← hd]
      simp only [List.append_assoc]
      have h35 : (u32s.drop 35).take 4 ++ u32s.drop 39 = u32s.drop 35 := by
        rw [show 39 = 35 + 4 from rfl, ← List.drop_drop, List.take_append_drop]
      have h29 : (u32s.drop 29).take 6 ++ u32s.drop 35 = u32s.drop 29 := by
        rw [show 35 = 29 + 6 from rfl, ← List.drop_drop, List.take_append_drop]
      have h26 : (u32s.drop 26).take 3 ++ u32s.drop 29 = u32s.drop 26 := by
        rw [show 29 = 26 + 3 from rfl, ← List.drop_drop, List.take_append_drop]
      have h23 : (u32s.drop 23).take 3 ++ u32s.drop 26 = u32s.drop 23 := by
        rw [show 26 = 23 + 3 from rfl, ← List.drop_drop, List.take_append_drop]
      have h21 : (u32s.drop 21).take 2 ++ u32s.drop 23 = u32s.drop 21 := by
        rw [show 23 = 21 + 2 from rfl, ← List.drop_drop, List.take_append_drop]
      rw [h35, h29, h26, h23, h21, List.take_append_drop]
    have hl0 : (u32s.take 21).length = 21 := by simp [hu32l]
    have hl1 : ((u32s.drop 21).take 2).length = 2 := by simp [hu32l]
    have hl2 : ((u32s.drop 23).take 3).length = 3 := by simp [hu32l]
    have hl3 : ((u32s.drop 26).take 3).length = 3 := by simp [hu32l]
    have hl4 : ((u32s.drop 29).take 6).length = 6 := by simp [hu32l]
    have hl5 : ((u32s.drop 35).take 4).length = 4 := by simp [hu32l]
    conv => lhs; rw [hlen]
    repeat rw [array_append]
    rw [array_cons, array_nil, sep_emp]
    simp only [List.length_append, hl0, hl1, hl2, hl3, hl4, hl5,
      Ty.bytes, Ty.size, ptr_add_ofNat, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat]
  rw [split64, split32] at h32
  obtain ⟨w, wlen, top, mlo, mhi, rhs0, rhs1, olit, art, nw, pos, bind, in_net, out_ref,
    rule_off, rule_n, partner, flipped, stk_n, stk_p, memo_n, memo_v, dense, gsy, gcl, gch, h0⟩ :=
    list_eq_26 (u64s.take 26) (by simp [hu64l])
  obtain ⟨rs_m, rs_l, rs_h, rs_pool, rs_ptop, rs_pcap, h1⟩ :=
    list_eq_6 ((u64s.drop 37).take 6) (by simp [hu64l])
  obtain ⟨ptop, pcap, qm, qs, ql, qh, ix, ix2, bx, vq_off, vq, vq_skip, rm, rm2, rl, rh,
    rl2, rh2, rpool, rpcap, cur_rm, cur_rl, cur_rh, cur_rp, h2⟩ :=
    list_eq_24 (u64s.drop 53) (by simp [hu64l])
  obtain ⟨n_out, M, I, A, O, spec, n_in, n_nets, n_gates, n_cones, n_main, rs_n, rs_cap, tc,
    tn, tcap, pc, qn, qcap, rcap, cur_nr, h3⟩ :=
    list_eq_21 (u32s.take 21) (by simp [hu32l])
  let s : ArCtxState :=
    { w, wlen, top, mlo, mhi, rhs0, rhs1, olit, art, nw, pos, bind, in_net, out_ref,
      rule_off, rule_n, partner, flipped, stk_n, stk_p, memo_n, memo_v, dense, gsy, gcl, gch,
      g_lmask := (u64s.drop 26).take 6, g_tin := (u64s.drop 32).take 3,
      g_tto := (u64s.drop 35).take 2,
      rs_m, rs_l, rs_h, rs_pool, rs_ptop, rs_pcap,
      tm := (u64s.drop 43).take 2, ts := (u64s.drop 45).take 2, tl := (u64s.drop 47).take 2,
      th := (u64s.drop 49).take 2, pool := (u64s.drop 51).take 2,
      ptop, pcap, qm, qs, ql, qh, ix, ix2, bx, vq_off, vq, vq_skip,
      rm, rm2, rl, rh, rl2, rh2, rpool, rpcap, cur_rm, cur_rl, cur_rh, cur_rp,
      n_out, M, I, A, O, spec, n_in, n_nets, n_gates, n_cones, n_main, rs_n, rs_cap, tc,
      tn, tcap, pc, qn, qcap, rcap, cur_nr,
      g_outs := (u32s.drop 21).take 2, g_innet := (u32s.drop 23).take 3,
      g_inneg := (u32s.drop 26).take 3, g_lnode := (u32s.drop 29).take 6,
      g_vs := (u32s.drop 35).take 4, pad_end := u32s[39]'(by omega) }
  have hl : ArCtxLengthsOk s :=
    { g_lmask := by simp [s, hu64l], g_tin := by simp [s, hu64l], g_tto := by simp [s, hu64l],
      tm := by simp [s, hu64l], ts := by simp [s, hu64l], tl := by simp [s, hu64l],
      th := by simp [s, hu64l], pool := by simp [s, hu64l],
      g_outs := by simp [s, hu32l], g_innet := by simp [s, hu32l], g_inneg := by simp [s, hu32l],
      g_lnode := by simp [s, hu32l], g_vs := by simp [s, hu32l] }
  refine ⟨s, hl, ?_⟩
  have hev : (arCtxTree cx s).eval =
      ((array64 cx (u64s.take 26) ⋆
        array64 (cx + 208) ((u64s.drop 26).take 6) ⋆
        array64 (cx + 256) ((u64s.drop 32).take 3) ⋆
        array64 (cx + 280) ((u64s.drop 35).take 2) ⋆
        array64 (cx + 296) ((u64s.drop 37).take 6) ⋆
        array64 (cx + 344) ((u64s.drop 43).take 2) ⋆
        array64 (cx + 360) ((u64s.drop 45).take 2) ⋆
        array64 (cx + 376) ((u64s.drop 47).take 2) ⋆
        array64 (cx + 392) ((u64s.drop 49).take 2) ⋆
        array64 (cx + 408) ((u64s.drop 51).take 2) ⋆
        array64 (cx + 424) (u64s.drop 53)) ⋆
       (array (t := i32) (cx + 616) (u32s.take 21) ⋆
        array (t := i32) (cx + 700) ((u32s.drop 21).take 2) ⋆
        array (t := i32) (cx + 708) ((u32s.drop 23).take 3) ⋆
        array (t := i32) (cx + 720) ((u32s.drop 26).take 3) ⋆
        array (t := i32) (cx + 732) ((u32s.drop 29).take 6) ⋆
        array (t := i32) (cx + 756) ((u32s.drop 35).take 4) ⋆
        cell (t := i32) (cx + 772) (u32s[39]'(by omega)))) := by
    simp only [arCtxTree, SepTree.eval, s, ArCtxState.blk0, ArCtxState.blk1, ArCtxState.blk2,
      ArCtxState.u32Blk, ← h0, ← h1, ← h2, ← h3]
    ac_rfl
  exact hev ▸ h32

/-! ## 4. Global `@[c0_load]` / `@[c0_store]` Accessors for `ArCtx` -/

section ArCtxAccessors
variable {cx : BitVec 64} {s : ArCtxState} {R : Mem 64 → Prop} {m : Mem 64}

private theorem arCtx_split (hm : (arCtxMem cx s ⋆ R) m) :
    ArCtxLengthsOk s ∧ ((arCtxTree cx s).eval ⋆ R) m :=
  sep_pure_l.mp hm

private theorem arCtx_mk (hl : ArCtxLengthsOk s) (hm : ((arCtxTree cx s).eval ⋆ R) m) :
    (arCtxMem cx s ⋆ R) m :=
  sep_pure_l.mpr ⟨hl, hm⟩

private theorem add_ofNat_assoc (a : BitVec 64) (c k : Nat) :
    (a + BitVec.ofNat 64 c) + BitVec.ofNat 64 k = a + BitVec.ofNat 64 (c + k) := by
  rw [ptr_add_ofNat]

private theorem load_blk0 (i : Nat) (hi : i < 26) (off : BitVec 64)
    (hoff : off = BitVec.ofNat 64 (8 * i)) (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + off) = some (s.blk0[i]'(by simpa [ArCtxState.blk0] using hi)) := by
  rw [hoff]
  exact sepTree_hdr_get (p := pBlk0) rfl i (by simpa [ArCtxState.blk0] using hi) (arCtx_split hm).2

private theorem store_blk0 (i : Nat) (hi : i < 26) (off : BitVec 64)
    (hoff : off = BitVec.ofNat 64 (8 * i)) (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m)
    (s' : ArCtxState) (hb : s'.blk0 = s.blk0.set i v)
    (hrest : (arCtxTree cx s).set pBlk0 (array64 cx s'.blk0) = arCtxTree cx s')
    (hl' : ArCtxLengthsOk s') :
    storeOk m i64 (cx + off) ∧ (arCtxMem cx s' ⋆ R) (storeMem m i64 (cx + off) v) := by
  have ⟨_, ht⟩ := arCtx_split hm
  rw [hoff]
  obtain ⟨hok, hm'⟩ := sepTree_hdr_put (p := pBlk0) rfl i (by simpa [ArCtxState.blk0] using hi)
    v hb (congrArg SepTree.eval hrest) ht
  exact ⟨hok, arCtx_mk hl' hm'⟩

private theorem load_blk1 (i : Nat) (hi : i < 6) (off : BitVec 64)
    (hoff : off = BitVec.ofNat 64 (296 + 8 * i)) (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + off) = some (s.blk1[i]'(by simpa [ArCtxState.blk1] using hi)) := by
  have h := sepTree_hdr_get (p := pBlk1) (t := arCtxTree cx s) rfl i
    (by simpa [ArCtxState.blk1] using hi) (arCtx_split hm).2
  rwa [show (cx + 296 : BitVec 64) = cx + BitVec.ofNat 64 296 from rfl,
    add_ofNat_assoc, ← hoff] at h

private theorem store_blk1 (i : Nat) (hi : i < 6) (off : BitVec 64)
    (hoff : off = BitVec.ofNat 64 (296 + 8 * i)) (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m)
    (s' : ArCtxState) (hb : s'.blk1 = s.blk1.set i v)
    (hrest : (arCtxTree cx s).set pBlk1 (array64 (cx + 296) s'.blk1) = arCtxTree cx s')
    (hl' : ArCtxLengthsOk s') :
    storeOk m i64 (cx + off) ∧ (arCtxMem cx s' ⋆ R) (storeMem m i64 (cx + off) v) := by
  have ⟨_, ht⟩ := arCtx_split hm
  obtain ⟨hok, hm'⟩ := sepTree_hdr_put (p := pBlk1) (t := arCtxTree cx s) rfl i
    (by simpa [ArCtxState.blk1] using hi) v hb (congrArg SepTree.eval hrest) ht
  rw [show (cx + 296 : BitVec 64) = cx + BitVec.ofNat 64 296 from rfl,
    add_ofNat_assoc, ← hoff] at hok hm'
  exact ⟨hok, arCtx_mk hl' hm'⟩

private theorem load_blk2 (i : Nat) (hi : i < 24) (off : BitVec 64)
    (hoff : off = BitVec.ofNat 64 (424 + 8 * i)) (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + off) = some (s.blk2[i]'(by simpa [ArCtxState.blk2] using hi)) := by
  have h := sepTree_hdr_get (p := pBlk2) (t := arCtxTree cx s) rfl i
    (by simpa [ArCtxState.blk2] using hi) (arCtx_split hm).2
  rwa [show (cx + 424 : BitVec 64) = cx + BitVec.ofNat 64 424 from rfl,
    add_ofNat_assoc, ← hoff] at h

private theorem store_blk2 (i : Nat) (hi : i < 24) (off : BitVec 64)
    (hoff : off = BitVec.ofNat 64 (424 + 8 * i)) (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m)
    (s' : ArCtxState) (hb : s'.blk2 = s.blk2.set i v)
    (hrest : (arCtxTree cx s).set pBlk2 (array64 (cx + 424) s'.blk2) = arCtxTree cx s')
    (hl' : ArCtxLengthsOk s') :
    storeOk m i64 (cx + off) ∧ (arCtxMem cx s' ⋆ R) (storeMem m i64 (cx + off) v) := by
  have ⟨_, ht⟩ := arCtx_split hm
  obtain ⟨hok, hm'⟩ := sepTree_hdr_put (p := pBlk2) (t := arCtxTree cx s) rfl i
    (by simpa [ArCtxState.blk2] using hi) v hb (congrArg SepTree.eval hrest) ht
  rw [show (cx + 424 : BitVec 64) = cx + BitVec.ofNat 64 424 from rfl,
    add_ofNat_assoc, ← hoff] at hok hm'
  exact ⟨hok, arCtx_mk hl' hm'⟩

private theorem load_u32 (i : Nat) (hi : i < 21) (off : BitVec 64)
    (hoff : off = BitVec.ofNat 64 (616 + 4 * i)) (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i32 (cx + off) = some (s.u32Blk[i]'(by simpa [ArCtxState.u32Blk] using hi)) := by
  have h := sepTree_arr_get (p := pU32Blk) (t := arCtxTree cx s) rfl (by decide)
    (by simpa [ArCtxState.u32Blk] using hi) (arCtx_split hm).2
  simp only [Ty.bytes, Ty.size] at h
  rwa [show (cx + 616 : BitVec 64) = cx + BitVec.ofNat 64 616 from rfl,
    add_ofNat_assoc, ← hoff] at h

private theorem store_u32 (i : Nat) (hi : i < 21) (off : BitVec 64)
    (hoff : off = BitVec.ofNat 64 (616 + 4 * i)) (v : BitVec 32) (hm : (arCtxMem cx s ⋆ R) m)
    (s' : ArCtxState) (hb : s'.u32Blk = s.u32Blk.set i v)
    (hrest : (arCtxTree cx s).set pU32Blk (array (t := i32) (cx + 616) s'.u32Blk) =
      arCtxTree cx s')
    (hl' : ArCtxLengthsOk s') :
    storeOk m i32 (cx + off) ∧ (arCtxMem cx s' ⋆ R) (storeMem m i32 (cx + off) v) := by
  have ⟨_, ht⟩ := arCtx_split hm
  have heq : ((arCtxTree cx s).set pU32Blk
      (array (t := i32) (cx + 616) (s.u32Blk.set i v))).eval = (arCtxTree cx s').eval := by
    rw [← hb, hrest]
  obtain ⟨hok, hm'⟩ := sepTree_arr_put (p := pU32Blk) (t := arCtxTree cx s) rfl (by decide)
    v (by simpa [ArCtxState.u32Blk] using hi) heq ht
  simp only [Ty.bytes, Ty.size] at hok hm'
  rw [show (cx + 616 : BitVec 64) = cx + BitVec.ofNat 64 616 from rfl,
    add_ofNat_assoc, ← hoff] at hok hm'
  exact ⟨hok, arCtx_mk hl' hm'⟩

/-! ### `blk0` scalar accessors (`+0 .. +200`) -/

@[c0_load] theorem load_w (hm : (arCtxMem cx s ⋆ R) m) : loadVal m i64 cx = some s.w :=
  (BitVec.add_zero cx) ▸ load_blk0 0 (by decide) 0 rfl hm
@[c0_load] theorem load_w_off0 (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 0) = some s.w := load_blk0 0 (by decide) 0 rfl hm
@[c0_load] theorem load_wlen (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 8) = some s.wlen := load_blk0 1 (by decide) 8 rfl hm
@[c0_load] theorem load_top (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 16) = some s.top := load_blk0 2 (by decide) 16 rfl hm
@[c0_load] theorem load_mlo (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 24) = some s.mlo := load_blk0 3 (by decide) 24 rfl hm
@[c0_load] theorem load_mhi (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 32) = some s.mhi := load_blk0 4 (by decide) 32 rfl hm
@[c0_load] theorem load_rhs0 (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 40) = some s.rhs0 := load_blk0 5 (by decide) 40 rfl hm
@[c0_load] theorem load_rhs1 (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 48) = some s.rhs1 := load_blk0 6 (by decide) 48 rfl hm
@[c0_load] theorem load_olit (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 56) = some s.olit := load_blk0 7 (by decide) 56 rfl hm
@[c0_load] theorem load_art (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 64) = some s.art := load_blk0 8 (by decide) 64 rfl hm
@[c0_load] theorem load_nw (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 72) = some s.nw := load_blk0 9 (by decide) 72 rfl hm
@[c0_load] theorem load_pos (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 80) = some s.pos := load_blk0 10 (by decide) 80 rfl hm
@[c0_load] theorem load_bind (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 88) = some s.bind := load_blk0 11 (by decide) 88 rfl hm
@[c0_load] theorem load_in_net (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 96) = some s.in_net := load_blk0 12 (by decide) 96 rfl hm
@[c0_load] theorem load_out_ref (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 104) = some s.out_ref := load_blk0 13 (by decide) 104 rfl hm
@[c0_load] theorem load_rule_off (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 112) = some s.rule_off := load_blk0 14 (by decide) 112 rfl hm
@[c0_load] theorem load_rule_n (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 120) = some s.rule_n := load_blk0 15 (by decide) 120 rfl hm
@[c0_load] theorem load_partner (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 128) = some s.partner := load_blk0 16 (by decide) 128 rfl hm
@[c0_load] theorem load_flipped (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 136) = some s.flipped := load_blk0 17 (by decide) 136 rfl hm
@[c0_load] theorem load_stk_n (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 144) = some s.stk_n := load_blk0 18 (by decide) 144 rfl hm
@[c0_load] theorem load_stk_p (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 152) = some s.stk_p := load_blk0 19 (by decide) 152 rfl hm
@[c0_load] theorem load_memo_n (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 160) = some s.memo_n := load_blk0 20 (by decide) 160 rfl hm
@[c0_load] theorem load_memo_v (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 168) = some s.memo_v := load_blk0 21 (by decide) 168 rfl hm
@[c0_load] theorem load_dense (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 176) = some s.dense := load_blk0 22 (by decide) 176 rfl hm
@[c0_load] theorem load_gsy (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 184) = some s.gsy := load_blk0 23 (by decide) 184 rfl hm
@[c0_load] theorem load_gcl (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 192) = some s.gcl := load_blk0 24 (by decide) 192 rfl hm
@[c0_load] theorem load_gch (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 200) = some s.gch := load_blk0 25 (by decide) 200 rfl hm

@[c0_store] theorem store_w (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 cx ∧ (arCtxMem cx { s with w := v } ⋆ R) (storeMem m i64 cx v) := by
  simpa [BitVec.add_zero] using
    store_blk0 0 (by decide) 0 rfl v hm { s with w := v } rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_w_off0 (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 0) ∧ (arCtxMem cx { s with w := v } ⋆ R) (storeMem m i64 (cx + 0) v) :=
  store_blk0 0 (by decide) 0 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_wlen (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 8) ∧ (arCtxMem cx { s with wlen := v } ⋆ R) (storeMem m i64 (cx + 8) v) :=
  store_blk0 1 (by decide) 8 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_top (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 16) ∧ (arCtxMem cx { s with top := v } ⋆ R) (storeMem m i64 (cx + 16) v) :=
  store_blk0 2 (by decide) 16 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_mlo (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 24) ∧ (arCtxMem cx { s with mlo := v } ⋆ R) (storeMem m i64 (cx + 24) v) :=
  store_blk0 3 (by decide) 24 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_mhi (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 32) ∧ (arCtxMem cx { s with mhi := v } ⋆ R) (storeMem m i64 (cx + 32) v) :=
  store_blk0 4 (by decide) 32 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_rhs0 (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 40) ∧
      (arCtxMem cx { s with rhs0 := v } ⋆ R) (storeMem m i64 (cx + 40) v) :=
  store_blk0 5 (by decide) 40 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_rhs1 (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 48) ∧
      (arCtxMem cx { s with rhs1 := v } ⋆ R) (storeMem m i64 (cx + 48) v) :=
  store_blk0 6 (by decide) 48 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_olit (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 56) ∧
      (arCtxMem cx { s with olit := v } ⋆ R) (storeMem m i64 (cx + 56) v) :=
  store_blk0 7 (by decide) 56 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_art (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 64) ∧ (arCtxMem cx { s with art := v } ⋆ R) (storeMem m i64 (cx + 64) v) :=
  store_blk0 8 (by decide) 64 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_nw (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 72) ∧ (arCtxMem cx { s with nw := v } ⋆ R) (storeMem m i64 (cx + 72) v) :=
  store_blk0 9 (by decide) 72 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_pos (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 80) ∧ (arCtxMem cx { s with pos := v } ⋆ R) (storeMem m i64 (cx + 80) v) :=
  store_blk0 10 (by decide) 80 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_bind (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 88) ∧
      (arCtxMem cx { s with bind := v } ⋆ R) (storeMem m i64 (cx + 88) v) :=
  store_blk0 11 (by decide) 88 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_in_net (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 96) ∧
      (arCtxMem cx { s with in_net := v } ⋆ R) (storeMem m i64 (cx + 96) v) :=
  store_blk0 12 (by decide) 96 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_out_ref (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 104) ∧
      (arCtxMem cx { s with out_ref := v } ⋆ R) (storeMem m i64 (cx + 104) v) :=
  store_blk0 13 (by decide) 104 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_rule_off (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 112) ∧
      (arCtxMem cx { s with rule_off := v } ⋆ R) (storeMem m i64 (cx + 112) v) :=
  store_blk0 14 (by decide) 112 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_rule_n (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 120) ∧
      (arCtxMem cx { s with rule_n := v } ⋆ R) (storeMem m i64 (cx + 120) v) :=
  store_blk0 15 (by decide) 120 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_partner (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 128) ∧
      (arCtxMem cx { s with partner := v } ⋆ R) (storeMem m i64 (cx + 128) v) :=
  store_blk0 16 (by decide) 128 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_flipped (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 136) ∧
      (arCtxMem cx { s with flipped := v } ⋆ R) (storeMem m i64 (cx + 136) v) :=
  store_blk0 17 (by decide) 136 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_stk_n (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 144) ∧
      (arCtxMem cx { s with stk_n := v } ⋆ R) (storeMem m i64 (cx + 144) v) :=
  store_blk0 18 (by decide) 144 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_stk_p (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 152) ∧
      (arCtxMem cx { s with stk_p := v } ⋆ R) (storeMem m i64 (cx + 152) v) :=
  store_blk0 19 (by decide) 152 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_memo_n (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 160) ∧
      (arCtxMem cx { s with memo_n := v } ⋆ R) (storeMem m i64 (cx + 160) v) :=
  store_blk0 20 (by decide) 160 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_memo_v (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 168) ∧
      (arCtxMem cx { s with memo_v := v } ⋆ R) (storeMem m i64 (cx + 168) v) :=
  store_blk0 21 (by decide) 168 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_dense (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 176) ∧
      (arCtxMem cx { s with dense := v } ⋆ R) (storeMem m i64 (cx + 176) v) :=
  store_blk0 22 (by decide) 176 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_gsy (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 184) ∧
      (arCtxMem cx { s with gsy := v } ⋆ R) (storeMem m i64 (cx + 184) v) :=
  store_blk0 23 (by decide) 184 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_gcl (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 192) ∧
      (arCtxMem cx { s with gcl := v } ⋆ R) (storeMem m i64 (cx + 192) v) :=
  store_blk0 24 (by decide) 192 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_gch (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 200) ∧
      (arCtxMem cx { s with gch := v } ⋆ R) (storeMem m i64 (cx + 200) v) :=
  store_blk0 25 (by decide) 200 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)

/-! ### `blk1` & `blk2` scalar accessors (`+296 .. +336`, `+424 .. +608`) -/

@[c0_load] theorem load_rs_m (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 296) = some s.rs_m := load_blk1 0 (by decide) 296 rfl hm
@[c0_load] theorem load_rs_l (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 304) = some s.rs_l := load_blk1 1 (by decide) 304 rfl hm
@[c0_load] theorem load_rs_h (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 312) = some s.rs_h := load_blk1 2 (by decide) 312 rfl hm
@[c0_load] theorem load_rs_pool (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 320) = some s.rs_pool := load_blk1 3 (by decide) 320 rfl hm
@[c0_load] theorem load_rs_ptop (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 328) = some s.rs_ptop := load_blk1 4 (by decide) 328 rfl hm
@[c0_load] theorem load_rs_pcap (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 336) = some s.rs_pcap := load_blk1 5 (by decide) 336 rfl hm

@[c0_store] theorem store_rs_m (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 296) ∧
      (arCtxMem cx { s with rs_m := v } ⋆ R) (storeMem m i64 (cx + 296) v) :=
  store_blk1 0 (by decide) 296 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_rs_l (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 304) ∧
      (arCtxMem cx { s with rs_l := v } ⋆ R) (storeMem m i64 (cx + 304) v) :=
  store_blk1 1 (by decide) 304 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_rs_h (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 312) ∧
      (arCtxMem cx { s with rs_h := v } ⋆ R) (storeMem m i64 (cx + 312) v) :=
  store_blk1 2 (by decide) 312 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_rs_pool (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 320) ∧
      (arCtxMem cx { s with rs_pool := v } ⋆ R) (storeMem m i64 (cx + 320) v) :=
  store_blk1 3 (by decide) 320 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_rs_ptop (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 328) ∧
      (arCtxMem cx { s with rs_ptop := v } ⋆ R) (storeMem m i64 (cx + 328) v) :=
  store_blk1 4 (by decide) 328 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_rs_pcap (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 336) ∧
      (arCtxMem cx { s with rs_pcap := v } ⋆ R) (storeMem m i64 (cx + 336) v) :=
  store_blk1 5 (by decide) 336 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)

@[c0_load] theorem load_ptop (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 424) = some s.ptop := load_blk2 0 (by decide) 424 rfl hm
@[c0_load] theorem load_pcap (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 432) = some s.pcap := load_blk2 1 (by decide) 432 rfl hm
@[c0_load] theorem load_qm (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 440) = some s.qm := load_blk2 2 (by decide) 440 rfl hm
@[c0_load] theorem load_qs (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 448) = some s.qs := load_blk2 3 (by decide) 448 rfl hm
@[c0_load] theorem load_ql (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 456) = some s.ql := load_blk2 4 (by decide) 456 rfl hm
@[c0_load] theorem load_qh (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 464) = some s.qh := load_blk2 5 (by decide) 464 rfl hm
@[c0_load] theorem load_ix (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 472) = some s.ix := load_blk2 6 (by decide) 472 rfl hm
@[c0_load] theorem load_ix2 (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 480) = some s.ix2 := load_blk2 7 (by decide) 480 rfl hm
@[c0_load] theorem load_bx (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 488) = some s.bx := load_blk2 8 (by decide) 488 rfl hm
@[c0_load] theorem load_vq_off (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 496) = some s.vq_off := load_blk2 9 (by decide) 496 rfl hm
@[c0_load] theorem load_vq (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 504) = some s.vq := load_blk2 10 (by decide) 504 rfl hm
@[c0_load] theorem load_vq_skip (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 512) = some s.vq_skip := load_blk2 11 (by decide) 512 rfl hm
@[c0_load] theorem load_rm (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 520) = some s.rm := load_blk2 12 (by decide) 520 rfl hm
@[c0_load] theorem load_rm2 (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 528) = some s.rm2 := load_blk2 13 (by decide) 528 rfl hm
@[c0_load] theorem load_rl (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 536) = some s.rl := load_blk2 14 (by decide) 536 rfl hm
@[c0_load] theorem load_rh (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 544) = some s.rh := load_blk2 15 (by decide) 544 rfl hm
@[c0_load] theorem load_rl2 (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 552) = some s.rl2 := load_blk2 16 (by decide) 552 rfl hm
@[c0_load] theorem load_rh2 (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 560) = some s.rh2 := load_blk2 17 (by decide) 560 rfl hm
@[c0_load] theorem load_rpool (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 568) = some s.rpool := load_blk2 18 (by decide) 568 rfl hm
@[c0_load] theorem load_rpcap (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 576) = some s.rpcap := load_blk2 19 (by decide) 576 rfl hm
@[c0_load] theorem load_cur_rm (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 584) = some s.cur_rm := load_blk2 20 (by decide) 584 rfl hm
@[c0_load] theorem load_cur_rl (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 592) = some s.cur_rl := load_blk2 21 (by decide) 592 rfl hm
@[c0_load] theorem load_cur_rh (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 600) = some s.cur_rh := load_blk2 22 (by decide) 600 rfl hm
@[c0_load] theorem load_cur_rp (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 608) = some s.cur_rp := load_blk2 23 (by decide) 608 rfl hm

@[c0_store] theorem store_ptop (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 424) ∧
      (arCtxMem cx { s with ptop := v } ⋆ R) (storeMem m i64 (cx + 424) v) :=
  store_blk2 0 (by decide) 424 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_pcap (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 432) ∧
      (arCtxMem cx { s with pcap := v } ⋆ R) (storeMem m i64 (cx + 432) v) :=
  store_blk2 1 (by decide) 432 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_qm (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 440) ∧ (arCtxMem cx { s with qm := v } ⋆ R) (storeMem m i64 (cx + 440) v) :=
  store_blk2 2 (by decide) 440 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_qs (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 448) ∧ (arCtxMem cx { s with qs := v } ⋆ R) (storeMem m i64 (cx + 448) v) :=
  store_blk2 3 (by decide) 448 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_ql (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 456) ∧ (arCtxMem cx { s with ql := v } ⋆ R) (storeMem m i64 (cx + 456) v) :=
  store_blk2 4 (by decide) 456 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_qh (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 464) ∧ (arCtxMem cx { s with qh := v } ⋆ R) (storeMem m i64 (cx + 464) v) :=
  store_blk2 5 (by decide) 464 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_ix (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 472) ∧ (arCtxMem cx { s with ix := v } ⋆ R) (storeMem m i64 (cx + 472) v) :=
  store_blk2 6 (by decide) 472 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_ix2 (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 480) ∧
      (arCtxMem cx { s with ix2 := v } ⋆ R) (storeMem m i64 (cx + 480) v) :=
  store_blk2 7 (by decide) 480 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_bx (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 488) ∧ (arCtxMem cx { s with bx := v } ⋆ R) (storeMem m i64 (cx + 488) v) :=
  store_blk2 8 (by decide) 488 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_vq_off (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 496) ∧
      (arCtxMem cx { s with vq_off := v } ⋆ R) (storeMem m i64 (cx + 496) v) :=
  store_blk2 9 (by decide) 496 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_vq (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 504) ∧ (arCtxMem cx { s with vq := v } ⋆ R) (storeMem m i64 (cx + 504) v) :=
  store_blk2 10 (by decide) 504 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_vq_skip (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 512) ∧
      (arCtxMem cx { s with vq_skip := v } ⋆ R) (storeMem m i64 (cx + 512) v) :=
  store_blk2 11 (by decide) 512 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_rm (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 520) ∧ (arCtxMem cx { s with rm := v } ⋆ R) (storeMem m i64 (cx + 520) v) :=
  store_blk2 12 (by decide) 520 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_rm2 (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 528) ∧
      (arCtxMem cx { s with rm2 := v } ⋆ R) (storeMem m i64 (cx + 528) v) :=
  store_blk2 13 (by decide) 528 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_rl (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 536) ∧ (arCtxMem cx { s with rl := v } ⋆ R) (storeMem m i64 (cx + 536) v) :=
  store_blk2 14 (by decide) 536 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_rh (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 544) ∧ (arCtxMem cx { s with rh := v } ⋆ R) (storeMem m i64 (cx + 544) v) :=
  store_blk2 15 (by decide) 544 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_rl2 (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 552) ∧
      (arCtxMem cx { s with rl2 := v } ⋆ R) (storeMem m i64 (cx + 552) v) :=
  store_blk2 16 (by decide) 552 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_rh2 (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 560) ∧
      (arCtxMem cx { s with rh2 := v } ⋆ R) (storeMem m i64 (cx + 560) v) :=
  store_blk2 17 (by decide) 560 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_rpool (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 568) ∧
      (arCtxMem cx { s with rpool := v } ⋆ R) (storeMem m i64 (cx + 568) v) :=
  store_blk2 18 (by decide) 568 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_rpcap (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 576) ∧
      (arCtxMem cx { s with rpcap := v } ⋆ R) (storeMem m i64 (cx + 576) v) :=
  store_blk2 19 (by decide) 576 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_cur_rm (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 584) ∧
      (arCtxMem cx { s with cur_rm := v } ⋆ R) (storeMem m i64 (cx + 584) v) :=
  store_blk2 20 (by decide) 584 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_cur_rl (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 592) ∧
      (arCtxMem cx { s with cur_rl := v } ⋆ R) (storeMem m i64 (cx + 592) v) :=
  store_blk2 21 (by decide) 592 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_cur_rh (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 600) ∧
      (arCtxMem cx { s with cur_rh := v } ⋆ R) (storeMem m i64 (cx + 600) v) :=
  store_blk2 22 (by decide) 600 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_cur_rp (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 608) ∧
      (arCtxMem cx { s with cur_rp := v } ⋆ R) (storeMem m i64 (cx + 608) v) :=
  store_blk2 23 (by decide) 608 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)

/-! ### `u32` scalar accessors (`+616 .. +696`, `+772`) -/

@[c0_load] theorem load_n_out (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i32 (cx + 616) = some s.n_out := load_u32 0 (by decide) 616 rfl hm
@[c0_load] theorem load_M (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i32 (cx + 620) = some s.M := load_u32 1 (by decide) 620 rfl hm
@[c0_load] theorem load_I (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i32 (cx + 624) = some s.I := load_u32 2 (by decide) 624 rfl hm
@[c0_load] theorem load_A (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i32 (cx + 628) = some s.A := load_u32 3 (by decide) 628 rfl hm
@[c0_load] theorem load_O (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i32 (cx + 632) = some s.O := load_u32 4 (by decide) 632 rfl hm
@[c0_load] theorem load_spec (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i32 (cx + 636) = some s.spec := load_u32 5 (by decide) 636 rfl hm
@[c0_load] theorem load_n_in (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i32 (cx + 640) = some s.n_in := load_u32 6 (by decide) 640 rfl hm
@[c0_load] theorem load_n_nets (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i32 (cx + 644) = some s.n_nets := load_u32 7 (by decide) 644 rfl hm
@[c0_load] theorem load_n_gates (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i32 (cx + 648) = some s.n_gates := load_u32 8 (by decide) 648 rfl hm
@[c0_load] theorem load_n_cones (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i32 (cx + 652) = some s.n_cones := load_u32 9 (by decide) 652 rfl hm
@[c0_load] theorem load_n_main (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i32 (cx + 656) = some s.n_main := load_u32 10 (by decide) 656 rfl hm
@[c0_load] theorem load_rs_n (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i32 (cx + 660) = some s.rs_n := load_u32 11 (by decide) 660 rfl hm
@[c0_load] theorem load_rs_cap (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i32 (cx + 664) = some s.rs_cap := load_u32 12 (by decide) 664 rfl hm
@[c0_load] theorem load_tc (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i32 (cx + 668) = some s.tc := load_u32 13 (by decide) 668 rfl hm
@[c0_load] theorem load_tn (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i32 (cx + 672) = some s.tn := load_u32 14 (by decide) 672 rfl hm
@[c0_load] theorem load_tcap (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i32 (cx + 676) = some s.tcap := load_u32 15 (by decide) 676 rfl hm
@[c0_load] theorem load_pc (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i32 (cx + 680) = some s.pc := load_u32 16 (by decide) 680 rfl hm
@[c0_load] theorem load_qn (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i32 (cx + 684) = some s.qn := load_u32 17 (by decide) 684 rfl hm
@[c0_load] theorem load_qcap (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i32 (cx + 688) = some s.qcap := load_u32 18 (by decide) 688 rfl hm
@[c0_load] theorem load_rcap (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i32 (cx + 692) = some s.rcap := load_u32 19 (by decide) 692 rfl hm
@[c0_load] theorem load_cur_nr (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i32 (cx + 696) = some s.cur_nr := load_u32 20 (by decide) 696 rfl hm
@[c0_load] theorem load_pad_end (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i32 (cx + 772) = some s.pad_end :=
  sepTree_cell_get (p := pPadEnd) rfl (by decide) (arCtx_split hm).2

@[c0_store] theorem store_n_out (v : BitVec 32) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i32 (cx + 616) ∧
      (arCtxMem cx { s with n_out := v } ⋆ R) (storeMem m i32 (cx + 616) v) :=
  store_u32 0 (by decide) 616 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_M (v : BitVec 32) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i32 (cx + 620) ∧ (arCtxMem cx { s with M := v } ⋆ R) (storeMem m i32 (cx + 620) v) :=
  store_u32 1 (by decide) 620 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_I (v : BitVec 32) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i32 (cx + 624) ∧ (arCtxMem cx { s with I := v } ⋆ R) (storeMem m i32 (cx + 624) v) :=
  store_u32 2 (by decide) 624 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_A (v : BitVec 32) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i32 (cx + 628) ∧ (arCtxMem cx { s with A := v } ⋆ R) (storeMem m i32 (cx + 628) v) :=
  store_u32 3 (by decide) 628 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_O (v : BitVec 32) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i32 (cx + 632) ∧ (arCtxMem cx { s with O := v } ⋆ R) (storeMem m i32 (cx + 632) v) :=
  store_u32 4 (by decide) 632 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_spec (v : BitVec 32) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i32 (cx + 636) ∧
      (arCtxMem cx { s with spec := v } ⋆ R) (storeMem m i32 (cx + 636) v) :=
  store_u32 5 (by decide) 636 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_n_in (v : BitVec 32) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i32 (cx + 640) ∧
      (arCtxMem cx { s with n_in := v } ⋆ R) (storeMem m i32 (cx + 640) v) :=
  store_u32 6 (by decide) 640 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_n_nets (v : BitVec 32) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i32 (cx + 644) ∧
      (arCtxMem cx { s with n_nets := v } ⋆ R) (storeMem m i32 (cx + 644) v) :=
  store_u32 7 (by decide) 644 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_n_gates (v : BitVec 32) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i32 (cx + 648) ∧
      (arCtxMem cx { s with n_gates := v } ⋆ R) (storeMem m i32 (cx + 648) v) :=
  store_u32 8 (by decide) 648 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_n_cones (v : BitVec 32) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i32 (cx + 652) ∧
      (arCtxMem cx { s with n_cones := v } ⋆ R) (storeMem m i32 (cx + 652) v) :=
  store_u32 9 (by decide) 652 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_n_main (v : BitVec 32) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i32 (cx + 656) ∧
      (arCtxMem cx { s with n_main := v } ⋆ R) (storeMem m i32 (cx + 656) v) :=
  store_u32 10 (by decide) 656 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_rs_n (v : BitVec 32) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i32 (cx + 660) ∧
      (arCtxMem cx { s with rs_n := v } ⋆ R) (storeMem m i32 (cx + 660) v) :=
  store_u32 11 (by decide) 660 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_rs_cap (v : BitVec 32) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i32 (cx + 664) ∧
      (arCtxMem cx { s with rs_cap := v } ⋆ R) (storeMem m i32 (cx + 664) v) :=
  store_u32 12 (by decide) 664 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_tc (v : BitVec 32) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i32 (cx + 668) ∧ (arCtxMem cx { s with tc := v } ⋆ R) (storeMem m i32 (cx + 668) v) :=
  store_u32 13 (by decide) 668 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_tn (v : BitVec 32) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i32 (cx + 672) ∧ (arCtxMem cx { s with tn := v } ⋆ R) (storeMem m i32 (cx + 672) v) :=
  store_u32 14 (by decide) 672 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_tcap (v : BitVec 32) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i32 (cx + 676) ∧
      (arCtxMem cx { s with tcap := v } ⋆ R) (storeMem m i32 (cx + 676) v) :=
  store_u32 15 (by decide) 676 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_pc (v : BitVec 32) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i32 (cx + 680) ∧ (arCtxMem cx { s with pc := v } ⋆ R) (storeMem m i32 (cx + 680) v) :=
  store_u32 16 (by decide) 680 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_qn (v : BitVec 32) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i32 (cx + 684) ∧ (arCtxMem cx { s with qn := v } ⋆ R) (storeMem m i32 (cx + 684) v) :=
  store_u32 17 (by decide) 684 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_qcap (v : BitVec 32) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i32 (cx + 688) ∧
      (arCtxMem cx { s with qcap := v } ⋆ R) (storeMem m i32 (cx + 688) v) :=
  store_u32 18 (by decide) 688 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_rcap (v : BitVec 32) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i32 (cx + 692) ∧
      (arCtxMem cx { s with rcap := v } ⋆ R) (storeMem m i32 (cx + 692) v) :=
  store_u32 19 (by decide) 692 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_cur_nr (v : BitVec 32) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i32 (cx + 696) ∧
      (arCtxMem cx { s with cur_nr := v } ⋆ R) (storeMem m i32 (cx + 696) v) :=
  store_u32 20 (by decide) 696 rfl v hm _ rfl rfl (lengths_same (arCtx_split hm).1)
@[c0_store] theorem store_pad_end (v : BitVec 32) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i32 (cx + 772) ∧
      (arCtxMem cx { s with pad_end := v } ⋆ R) (storeMem m i32 (cx + 772) v) := by
  have ⟨hl, ht⟩ := arCtx_split hm
  obtain ⟨hok, hm'⟩ := sepTree_cell_put (p := pPadEnd) v rfl (by decide) rfl ht
  exact ⟨hok, arCtx_mk (lengths_same hl) hm'⟩

/-! ### Embedded `u64` & `u32` array helpers & `@[c0_load]` / `@[c0_store]` accessors -/

private theorem load_arr64_u32 (p : List Bool) (off : BitVec 64) (xs : List (BitVec 64))
    (n : Nat) (hget : (arCtxTree cx s).get p = array64 (cx + off) xs) (hxs : xs.length = n)
    {i : BitVec 32} (hi : i.toNat < n) (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + off + i.setWidth 64 * 8) = some (xs[i.toNat]'(by omega)) := by
  have hf := SepTree.focus p (arCtx_split hm).2
  rw [hget] at hf
  exact c0_load_array64_u32 (a := cx + off) (i := i) hf (by omega)

private theorem load_arr64_off (p : List Bool) (off k : BitVec 64) (xs : List (BitVec 64))
    (n : Nat) (hget : (arCtxTree cx s).get p = array64 (cx + off) xs) (hxs : xs.length = n)
    (hk : k.toNat % 8 = 0) (hi : k.toNat / 8 < n) (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + off + k) = some (xs[k.toNat / 8]'(by omega)) := by
  have hk_eq : k = BitVec.ofNat 64 (8 * (k.toNat / 8)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := k.isLt; omega)]; omega
  have hf := SepTree.focus p (arCtx_split hm).2
  rw [hget] at hf
  conv => lhs; rw [hk_eq]
  exact loadVal_array64 (i := k.toNat / 8) (by omega) hf

private theorem store_arr64_u32 (p : List Bool) (off : BitVec 64) (xs : List (BitVec 64))
    (n : Nat) (hget : (arCtxTree cx s).get p = array64 (cx + off) xs) (hxs : xs.length = n)
    {i : BitVec 32} (v : BitVec 64) (hi : i.toNat < n) (hm : (arCtxMem cx s ⋆ R) m)
    (s' : ArCtxState)
    (heq : (arCtxTree cx s).set p (array64 (cx + off) (xs.set i.toNat v)) = arCtxTree cx s')
    (hl' : ArCtxLengthsOk s') :
    storeOk m i64 (cx + off + i.setWidth 64 * 8) ∧
      (arCtxMem cx s' ⋆ R) (storeMem m i64 (cx + off + i.setWidth 64 * 8) v) := by
  have hf := SepTree.focus p (arCtx_split hm).2
  rw [hget] at hf
  obtain ⟨hok, hm'⟩ := c0_store_array64_u32 (a := cx + off) (i := i) v hf (by omega)
  exact ⟨hok, arCtx_mk hl' (SepTree.unfocus_eq p (congrArg SepTree.eval heq) hm')⟩

private theorem store_arr64_off (p : List Bool) (off k : BitVec 64) (xs : List (BitVec 64))
    (n : Nat) (hget : (arCtxTree cx s).get p = array64 (cx + off) xs) (hxs : xs.length = n)
    (hk : k.toNat % 8 = 0) (v : BitVec 64) (hi : k.toNat / 8 < n) (hm : (arCtxMem cx s ⋆ R) m)
    (s' : ArCtxState)
    (heq : (arCtxTree cx s).set p (array64 (cx + off) (xs.set (k.toNat / 8) v)) = arCtxTree cx s')
    (hl' : ArCtxLengthsOk s') :
    storeOk m i64 (cx + off + k) ∧
      (arCtxMem cx s' ⋆ R) (storeMem m i64 (cx + off + k) v) := by
  have hk_eq : k = BitVec.ofNat 64 (8 * (k.toNat / 8)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := k.isLt; omega)]; omega
  have hf := SepTree.focus p (arCtx_split hm).2
  rw [hget] at hf
  have hst := store_array64 (i := k.toNat / 8) v (by omega) hf
  rw [← hk_eq] at hst
  exact ⟨hst.1, arCtx_mk hl' (SepTree.unfocus_eq p (congrArg SepTree.eval heq) hst.2)⟩

private theorem load_arr32_u32 (p : List Bool) (off : BitVec 64) (xs : List (BitVec 32))
    (n : Nat) (hget : (arCtxTree cx s).get p = array (t := i32) (cx + off) xs)
    (hxs : xs.length = n) {i : BitVec 32} (hi : i.toNat < n) (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i32 (cx + off + i.setWidth 64 * 4) = some (xs[i.toNat]'(by omega)) := by
  have hf := SepTree.focus p (arCtx_split hm).2
  rw [hget] at hf
  exact c0_load_array32_u32 (a := cx + off) (i := i) hf (by omega)

private theorem load_arr32_off (p : List Bool) (off k : BitVec 64) (xs : List (BitVec 32))
    (n : Nat) (hget : (arCtxTree cx s).get p = array (t := i32) (cx + off) xs)
    (hxs : xs.length = n) (hk : k.toNat % 4 = 0) (hi : k.toNat / 4 < n)
    (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i32 (cx + off + k) = some (xs[k.toNat / 4]'(by omega)) := by
  have hk_eq : k = BitVec.ofNat 64 (4 * (k.toNat / 4)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := k.isLt; omega)]; omega
  have hf := SepTree.focus p (arCtx_split hm).2
  rw [hget] at hf
  conv => lhs; rw [hk_eq]
  exact loadVal_array (t := i32) (i := k.toNat / 4) (by decide) (by omega) hf

private theorem store_arr32_u32 (p : List Bool) (off : BitVec 64) (xs : List (BitVec 32))
    (n : Nat) (hget : (arCtxTree cx s).get p = array (t := i32) (cx + off) xs)
    (hxs : xs.length = n) {i : BitVec 32} (v : BitVec 32) (hi : i.toNat < n)
    (hm : (arCtxMem cx s ⋆ R) m) (s' : ArCtxState)
    (heq : (arCtxTree cx s).set p (array (t := i32) (cx + off) (xs.set i.toNat v)) =
      arCtxTree cx s')
    (hl' : ArCtxLengthsOk s') :
    storeOk m i32 (cx + off + i.setWidth 64 * 4) ∧
      (arCtxMem cx s' ⋆ R) (storeMem m i32 (cx + off + i.setWidth 64 * 4) v) := by
  have hf := SepTree.focus p (arCtx_split hm).2
  rw [hget] at hf
  obtain ⟨hok, hm'⟩ := c0_store_array32_u32 (a := cx + off) (i := i) v hf (by omega)
  exact ⟨hok, arCtx_mk hl' (SepTree.unfocus_eq p (congrArg SepTree.eval heq) hm')⟩

private theorem store_arr32_off (p : List Bool) (off k : BitVec 64) (xs : List (BitVec 32))
    (n : Nat) (hget : (arCtxTree cx s).get p = array (t := i32) (cx + off) xs)
    (hxs : xs.length = n) (hk : k.toNat % 4 = 0) (v : BitVec 32) (hi : k.toNat / 4 < n)
    (hm : (arCtxMem cx s ⋆ R) m) (s' : ArCtxState)
    (heq : (arCtxTree cx s).set p (array (t := i32) (cx + off) (xs.set (k.toNat / 4) v)) =
      arCtxTree cx s')
    (hl' : ArCtxLengthsOk s') :
    storeOk m i32 (cx + off + k) ∧
      (arCtxMem cx s' ⋆ R) (storeMem m i32 (cx + off + k) v) := by
  have hk_eq : k = BitVec.ofNat 64 (4 * (k.toNat / 4)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := k.isLt; omega)]; omega
  have hf := SepTree.focus p (arCtx_split hm).2
  rw [hget] at hf
  have hst := store_array (t := i32) (i := k.toNat / 4) v (by decide) (by omega) hf
  have hty : i32.bytes = 4 := by decide
  rw [hty, ← hk_eq] at hst
  exact ⟨hst.1, arCtx_mk hl' (SepTree.unfocus_eq p (congrArg SepTree.eval heq) hst.2)⟩

-- `g_lmask[6]` (+208)
@[c0_load] theorem load_g_lmask_u32 {i : BitVec 32} (hi : i.toNat < 6)
    (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 208 + i.setWidth 64 * 8) =
      some (s.g_lmask[i.toNat]'(by have := (arCtx_split hm).1.g_lmask; omega)) :=
  load_arr64_u32 pGLmask 208 s.g_lmask 6 rfl (arCtx_split hm).1.g_lmask hi hm

@[c0_store] theorem store_g_lmask_u32 {i : BitVec 32} (v : BitVec 64) (hi : i.toNat < 6)
    (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 208 + i.setWidth 64 * 8) ∧
      (arCtxMem cx { s with g_lmask := s.g_lmask.set i.toNat v } ⋆ R)
        (storeMem m i64 (cx + 208 + i.setWidth 64 * 8) v) :=
  store_arr64_u32 pGLmask 208 s.g_lmask 6 rfl (arCtx_split hm).1.g_lmask v hi hm _ rfl
    (lengths_same (arCtx_split hm).1 (h1 := by simp [(arCtx_split hm).1.g_lmask]))

-- `g_tin[3]` (+256)
@[c0_load] theorem load_g_tin_u32 {i : BitVec 32} (hi : i.toNat < 3)
    (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 256 + i.setWidth 64 * 8) =
      some (s.g_tin[i.toNat]'(by have := (arCtx_split hm).1.g_tin; omega)) :=
  load_arr64_u32 pGTin 256 s.g_tin 3 rfl (arCtx_split hm).1.g_tin hi hm

@[c0_store] theorem store_g_tin_u32 {i : BitVec 32} (v : BitVec 64) (hi : i.toNat < 3)
    (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 256 + i.setWidth 64 * 8) ∧
      (arCtxMem cx { s with g_tin := s.g_tin.set i.toNat v } ⋆ R)
        (storeMem m i64 (cx + 256 + i.setWidth 64 * 8) v) :=
  store_arr64_u32 pGTin 256 s.g_tin 3 rfl (arCtx_split hm).1.g_tin v hi hm _ rfl
    (lengths_same (arCtx_split hm).1 (h2 := by simp [(arCtx_split hm).1.g_tin]))

-- `g_tto[2]` (+280)
@[c0_load] theorem load_g_tto_u32 {i : BitVec 32} (hi : i.toNat < 2)
    (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 280 + i.setWidth 64 * 8) =
      some (s.g_tto[i.toNat]'(by have := (arCtx_split hm).1.g_tto; omega)) :=
  load_arr64_u32 pGTto 280 s.g_tto 2 rfl (arCtx_split hm).1.g_tto hi hm

@[c0_load] theorem load_g_tto_off {k : BitVec 64} (hk : k.toNat % 8 = 0) (hi : k.toNat / 8 < 2)
    (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 280 + k) =
      some (s.g_tto[k.toNat / 8]'(by have := (arCtx_split hm).1.g_tto; omega)) :=
  load_arr64_off pGTto 280 k s.g_tto 2 rfl (arCtx_split hm).1.g_tto hk hi hm

@[c0_store] theorem store_g_tto_u32 {i : BitVec 32} (v : BitVec 64) (hi : i.toNat < 2)
    (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 280 + i.setWidth 64 * 8) ∧
      (arCtxMem cx { s with g_tto := s.g_tto.set i.toNat v } ⋆ R)
        (storeMem m i64 (cx + 280 + i.setWidth 64 * 8) v) :=
  store_arr64_u32 pGTto 280 s.g_tto 2 rfl (arCtx_split hm).1.g_tto v hi hm _ rfl
    (lengths_same (arCtx_split hm).1 (h3 := by simp [(arCtx_split hm).1.g_tto]))

-- `tm[2]` (+344), `ts[2]` (+360), `tl[2]` (+376), `th[2]` (+392), `pool[2]` (+408)
@[c0_load] theorem load_tm_u32 {i : BitVec 32} (hi : i.toNat < 2)
    (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 344 + i.setWidth 64 * 8) =
      some (s.tm[i.toNat]'(by have := (arCtx_split hm).1.tm; omega)) :=
  load_arr64_u32 pTm 344 s.tm 2 rfl (arCtx_split hm).1.tm hi hm

@[c0_store] theorem store_tm_off {k : BitVec 64} (hk : k.toNat % 8 = 0) (hi : k.toNat / 8 < 2)
    (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 344 + k) ∧
      (arCtxMem cx { s with tm := s.tm.set (k.toNat / 8) v } ⋆ R)
        (storeMem m i64 (cx + 344 + k) v) :=
  store_arr64_off pTm 344 k s.tm 2 rfl (arCtx_split hm).1.tm hk v hi hm _ rfl
    (lengths_same (arCtx_split hm).1 (h4 := by simp [(arCtx_split hm).1.tm]))

@[c0_load] theorem load_ts_u32 {i : BitVec 32} (hi : i.toNat < 2)
    (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 360 + i.setWidth 64 * 8) =
      some (s.ts[i.toNat]'(by have := (arCtx_split hm).1.ts; omega)) :=
  load_arr64_u32 pTs 360 s.ts 2 rfl (arCtx_split hm).1.ts hi hm

@[c0_store] theorem store_ts_off {k : BitVec 64} (hk : k.toNat % 8 = 0) (hi : k.toNat / 8 < 2)
    (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 360 + k) ∧
      (arCtxMem cx { s with ts := s.ts.set (k.toNat / 8) v } ⋆ R)
        (storeMem m i64 (cx + 360 + k) v) :=
  store_arr64_off pTs 360 k s.ts 2 rfl (arCtx_split hm).1.ts hk v hi hm _ rfl
    (lengths_same (arCtx_split hm).1 (h5 := by simp [(arCtx_split hm).1.ts]))

@[c0_load] theorem load_tl_u32 {i : BitVec 32} (hi : i.toNat < 2)
    (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 376 + i.setWidth 64 * 8) =
      some (s.tl[i.toNat]'(by have := (arCtx_split hm).1.tl; omega)) :=
  load_arr64_u32 pTl 376 s.tl 2 rfl (arCtx_split hm).1.tl hi hm

@[c0_store] theorem store_tl_off {k : BitVec 64} (hk : k.toNat % 8 = 0) (hi : k.toNat / 8 < 2)
    (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 376 + k) ∧
      (arCtxMem cx { s with tl := s.tl.set (k.toNat / 8) v } ⋆ R)
        (storeMem m i64 (cx + 376 + k) v) :=
  store_arr64_off pTl 376 k s.tl 2 rfl (arCtx_split hm).1.tl hk v hi hm _ rfl
    (lengths_same (arCtx_split hm).1 (h6 := by simp [(arCtx_split hm).1.tl]))

@[c0_load] theorem load_th_u32 {i : BitVec 32} (hi : i.toNat < 2)
    (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 392 + i.setWidth 64 * 8) =
      some (s.th[i.toNat]'(by have := (arCtx_split hm).1.th; omega)) :=
  load_arr64_u32 pTh 392 s.th 2 rfl (arCtx_split hm).1.th hi hm

@[c0_store] theorem store_th_off {k : BitVec 64} (hk : k.toNat % 8 = 0) (hi : k.toNat / 8 < 2)
    (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 392 + k) ∧
      (arCtxMem cx { s with th := s.th.set (k.toNat / 8) v } ⋆ R)
        (storeMem m i64 (cx + 392 + k) v) :=
  store_arr64_off pTh 392 k s.th 2 rfl (arCtx_split hm).1.th hk v hi hm _ rfl
    (lengths_same (arCtx_split hm).1 (h7 := by simp [(arCtx_split hm).1.th]))

@[c0_load] theorem load_pool_u32 {i : BitVec 32} (hi : i.toNat < 2)
    (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 408 + i.setWidth 64 * 8) =
      some (s.pool[i.toNat]'(by have := (arCtx_split hm).1.pool; omega)) :=
  load_arr64_u32 pPool 408 s.pool 2 rfl (arCtx_split hm).1.pool hi hm

@[c0_store] theorem store_pool_off {k : BitVec 64} (hk : k.toNat % 8 = 0) (hi : k.toNat / 8 < 2)
    (v : BitVec 64) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 408 + k) ∧
      (arCtxMem cx { s with pool := s.pool.set (k.toNat / 8) v } ⋆ R)
        (storeMem m i64 (cx + 408 + k) v) :=
  store_arr64_off pPool 408 k s.pool 2 rfl (arCtx_split hm).1.pool hk v hi hm _ rfl
    (lengths_same (arCtx_split hm).1 (h8 := by simp [(arCtx_split hm).1.pool]))

-- `g_outs[2]` (+700), `g_innet[3]` (+708), `g_inneg[3]` (+720), `g_lnode[6]` (+732),
-- `g_vs[4]` (+756)
@[c0_load] theorem load_g_outs_u32 {i : BitVec 32} (hi : i.toNat < 2)
    (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i32 (cx + 700 + i.setWidth 64 * 4) =
      some (s.g_outs[i.toNat]'(by have := (arCtx_split hm).1.g_outs; omega)) :=
  load_arr32_u32 pGOuts 700 s.g_outs 2 rfl (arCtx_split hm).1.g_outs hi hm

@[c0_load] theorem load_g_outs_off {k : BitVec 64} (hk : k.toNat % 4 = 0) (hi : k.toNat / 4 < 2)
    (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i32 (cx + 700 + k) =
      some (s.g_outs[k.toNat / 4]'(by have := (arCtx_split hm).1.g_outs; omega)) :=
  load_arr32_off pGOuts 700 k s.g_outs 2 rfl (arCtx_split hm).1.g_outs hk hi hm

@[c0_store] theorem store_g_outs_u32 {i : BitVec 32} (v : BitVec 32) (hi : i.toNat < 2)
    (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i32 (cx + 700 + i.setWidth 64 * 4) ∧
      (arCtxMem cx { s with g_outs := s.g_outs.set i.toNat v } ⋆ R)
        (storeMem m i32 (cx + 700 + i.setWidth 64 * 4) v) :=
  store_arr32_u32 pGOuts 700 s.g_outs 2 rfl (arCtx_split hm).1.g_outs v hi hm _ rfl
    (lengths_same (arCtx_split hm).1 (h9 := by simp [(arCtx_split hm).1.g_outs]))

@[c0_load] theorem load_g_innet_u32 {i : BitVec 32} (hi : i.toNat < 3)
    (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i32 (cx + 708 + i.setWidth 64 * 4) =
      some (s.g_innet[i.toNat]'(by have := (arCtx_split hm).1.g_innet; omega)) :=
  load_arr32_u32 pGInnet 708 s.g_innet 3 rfl (arCtx_split hm).1.g_innet hi hm

@[c0_store] theorem store_g_innet_u32 {i : BitVec 32} (v : BitVec 32) (hi : i.toNat < 3)
    (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i32 (cx + 708 + i.setWidth 64 * 4) ∧
      (arCtxMem cx { s with g_innet := s.g_innet.set i.toNat v } ⋆ R)
        (storeMem m i32 (cx + 708 + i.setWidth 64 * 4) v) :=
  store_arr32_u32 pGInnet 708 s.g_innet 3 rfl (arCtx_split hm).1.g_innet v hi hm _ rfl
    (lengths_same (arCtx_split hm).1 (h10 := by simp [(arCtx_split hm).1.g_innet]))

@[c0_load] theorem load_g_inneg_u32 {i : BitVec 32} (hi : i.toNat < 3)
    (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i32 (cx + 720 + i.setWidth 64 * 4) =
      some (s.g_inneg[i.toNat]'(by have := (arCtx_split hm).1.g_inneg; omega)) :=
  load_arr32_u32 pGInneg 720 s.g_inneg 3 rfl (arCtx_split hm).1.g_inneg hi hm

@[c0_load] theorem load_g_inneg_off {k : BitVec 64} (hk : k.toNat % 4 = 0) (hi : k.toNat / 4 < 3)
    (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i32 (cx + 720 + k) =
      some (s.g_inneg[k.toNat / 4]'(by have := (arCtx_split hm).1.g_inneg; omega)) :=
  load_arr32_off pGInneg 720 k s.g_inneg 3 rfl (arCtx_split hm).1.g_inneg hk hi hm

@[c0_store] theorem store_g_inneg_u32 {i : BitVec 32} (v : BitVec 32) (hi : i.toNat < 3)
    (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i32 (cx + 720 + i.setWidth 64 * 4) ∧
      (arCtxMem cx { s with g_inneg := s.g_inneg.set i.toNat v } ⋆ R)
        (storeMem m i32 (cx + 720 + i.setWidth 64 * 4) v) :=
  store_arr32_u32 pGInneg 720 s.g_inneg 3 rfl (arCtx_split hm).1.g_inneg v hi hm _ rfl
    (lengths_same (arCtx_split hm).1 (h11 := by simp [(arCtx_split hm).1.g_inneg]))

@[c0_load] theorem load_g_lnode_u32 {i : BitVec 32} (hi : i.toNat < 6)
    (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i32 (cx + 732 + i.setWidth 64 * 4) =
      some (s.g_lnode[i.toNat]'(by have := (arCtx_split hm).1.g_lnode; omega)) :=
  load_arr32_u32 pGLnode 732 s.g_lnode 6 rfl (arCtx_split hm).1.g_lnode hi hm

@[c0_store] theorem store_g_lnode_u32 {i : BitVec 32} (v : BitVec 32) (hi : i.toNat < 6)
    (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i32 (cx + 732 + i.setWidth 64 * 4) ∧
      (arCtxMem cx { s with g_lnode := s.g_lnode.set i.toNat v } ⋆ R)
        (storeMem m i32 (cx + 732 + i.setWidth 64 * 4) v) :=
  store_arr32_u32 pGLnode 732 s.g_lnode 6 rfl (arCtx_split hm).1.g_lnode v hi hm _ rfl
    (lengths_same (arCtx_split hm).1 (h12 := by simp [(arCtx_split hm).1.g_lnode]))

@[c0_load] theorem load_g_vs_u32 {i : BitVec 32} (hi : i.toNat < 4)
    (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i32 (cx + 756 + i.setWidth 64 * 4) =
      some (s.g_vs[i.toNat]'(by have := (arCtx_split hm).1.g_vs; omega)) :=
  load_arr32_u32 pGVs 756 s.g_vs 4 rfl (arCtx_split hm).1.g_vs hi hm

@[c0_store] theorem store_g_vs_u32 {i : BitVec 32} (v : BitVec 32) (hi : i.toNat < 4)
    (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i32 (cx + 756 + i.setWidth 64 * 4) ∧
      (arCtxMem cx { s with g_vs := s.g_vs.set i.toNat v } ⋆ R)
        (storeMem m i32 (cx + 756 + i.setWidth 64 * 4) v) :=
  store_arr32_u32 pGVs 756 s.g_vs 4 rfl (arCtx_split hm).1.g_vs v hi hm _ rfl
    (lengths_same (arCtx_split hm).1 (h13 := by simp [(arCtx_split hm).1.g_vs]))

@[c0_store] theorem store_g_vs_off {k : BitVec 64} (hk : k.toNat % 4 = 0) (hi : k.toNat / 4 < 4)
    (v : BitVec 32) (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i32 (cx + 756 + k) ∧
      (arCtxMem cx { s with g_vs := s.g_vs.set (k.toNat / 4) v } ⋆ R)
        (storeMem m i32 (cx + 756 + k) v) :=
  store_arr32_off pGVs 756 k s.g_vs 4 rfl (arCtx_split hm).1.g_vs hk v hi hm _ rfl
    (lengths_same (arCtx_split hm).1 (h13 := by simp [(arCtx_split hm).1.g_vs]))

end ArCtxAccessors

end

end LeanQbe.T.Examples.Arisca.Proof
