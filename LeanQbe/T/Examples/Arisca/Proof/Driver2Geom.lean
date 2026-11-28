/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Src.Driver
public import LeanQbe.T.Examples.Arisca.Proof.Sem
public import LeanQbe.T.Examples.Arisca.Proof.Arith
public import LeanQbe.T.Examples.Arisca.Proof.Arena
public import LeanQbe.T.Examples.Arisca.Proof.ParseBase
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
meta import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0StepAttr
meta import LeanQbe.T.Logic.C0StepAttr
import Kraken.Separation

/-!
# ARiSCA Dynamic Arena Geometry & Allocator Lemmas (`Arisca.Proof.Driver2Geom`)

`XPost`-polymorphic (`noExit = true`, `<= std3`) WP specification (`arSetupDynamicSpec`),
exact `DynGeom` invariant, collapse lemmas, and step helpers for `ar_setup_dynamic`.
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
open LeanQbe.T.Examples.Arisca.Src.Driver

@[expose] public section

/-- Byte offset after all `31` dynamic allocations starting from `align8 top0`. -/
def dynEndTop (top0 cap : Nat) : Nat :=
  let t0 := align8 top0
  let pw := 12 * cap
  let a4 := align8 (4 * cap)
  let a8 := 8 * cap
  let ap := 4 * pw
  let avo := align8 (4 * cap + 4)
  let avs := align8 cap
  t0 + 9 * a4 + 15 * a8 + 5 * ap + avo + avs

/-- Exact contiguous pointer geometry for the `31` dynamic slabs allocated by `ar_setup_dynamic`. -/
structure DynGeom (s : ArCtxState) (top0 cap : Nat) : Prop where
  top_eq : s.top.toNat = dynEndTop top0 cap
  rs_m_eq : s.rs_m = s.w + BitVec.ofNat 64 (align8 top0)
  rs_l_eq : s.rs_l = s.rs_m + BitVec.ofNat 64 (align8 (4 * cap))
  rs_h_eq : s.rs_h = s.rs_l + BitVec.ofNat 64 (8 * cap)
  rs_pool_eq : s.rs_pool = s.rs_h + BitVec.ofNat 64 (8 * cap)
  tm0_eq : s.tm.getD 0 0#64 = s.rs_pool + BitVec.ofNat 64 (4 * (12 * cap))
  ts0_eq : s.ts.getD 0 0#64 = s.tm.getD 0 0#64 + BitVec.ofNat 64 (align8 (4 * cap))
  tl0_eq : s.tl.getD 0 0#64 = s.ts.getD 0 0#64 + BitVec.ofNat 64 (8 * cap)
  th0_eq : s.th.getD 0 0#64 = s.tl.getD 0 0#64 + BitVec.ofNat 64 (8 * cap)
  tm1_eq : s.tm.getD 1 0#64 = s.th.getD 0 0#64 + BitVec.ofNat 64 (8 * cap)
  ts1_eq : s.ts.getD 1 0#64 = s.tm.getD 1 0#64 + BitVec.ofNat 64 (align8 (4 * cap))
  tl1_eq : s.tl.getD 1 0#64 = s.ts.getD 1 0#64 + BitVec.ofNat 64 (8 * cap)
  th1_eq : s.th.getD 1 0#64 = s.tl.getD 1 0#64 + BitVec.ofNat 64 (8 * cap)
  pool0_eq : s.pool.getD 0 0#64 = s.th.getD 1 0#64 + BitVec.ofNat 64 (8 * cap)
  pool1_eq : s.pool.getD 1 0#64 = s.pool.getD 0 0#64 + BitVec.ofNat 64 (4 * (12 * cap))
  qm_eq : s.qm = s.pool.getD 1 0#64 + BitVec.ofNat 64 (4 * (12 * cap))
  qs_eq : s.qs = s.qm + BitVec.ofNat 64 (align8 (4 * cap))
  ql_eq : s.ql = s.qs + BitVec.ofNat 64 (8 * cap)
  qh_eq : s.qh = s.ql + BitVec.ofNat 64 (8 * cap)
  ix_pair_eq :
    (s.ix = s.qh + BitVec.ofNat 64 (8 * cap) ∧
      s.ix2 = s.ix + BitVec.ofNat 64 (align8 (4 * cap))) ∨
    (s.ix2 = s.qh + BitVec.ofNat 64 (8 * cap) ∧
      s.ix = s.ix2 + BitVec.ofNat 64 (align8 (4 * cap)))
  bx_eq : s.bx = s.qh + BitVec.ofNat 64 (8 * cap + 2 * align8 (4 * cap))
  vq_off_eq : s.vq_off = s.bx + BitVec.ofNat 64 (align8 (4 * cap))
  vq_eq : s.vq = s.vq_off + BitVec.ofNat 64 (align8 (4 * (cap + 1)))
  vq_skip_eq : s.vq_skip = s.vq + BitVec.ofNat 64 (4 * (12 * cap))
  rm_eq : s.rm = s.vq_skip + BitVec.ofNat 64 (align8 cap)
  rl_eq : s.rl = s.rm + BitVec.ofNat 64 (align8 (4 * cap))
  rh_eq : s.rh = s.rl + BitVec.ofNat 64 (8 * cap)
  rm2_eq : s.rm2 = s.rh + BitVec.ofNat 64 (8 * cap)
  rl2_eq : s.rl2 = s.rm2 + BitVec.ofNat 64 (align8 (4 * cap))
  rh2_eq : s.rh2 = s.rl2 + BitVec.ofNat 64 (8 * cap)
  rpool_eq : s.rpool = s.rh2 + BitVec.ofNat 64 (8 * cap)

/-- WP specification for `ar_setup_dynamic(cx)`. -/
def arSetupDynamicSpec : Spec [i64] [.bool] :=
  fun ⟨cx, ⟨⟩⟩ m Q _ =>
    ∃ (s : ArCtxState) (baseTop : Nat) (R : Mem 64 → Prop),
      0 < s.w.toNat ∧
      s.w.toNat + s.wlen.toNat < 2 ^ 64 ∧
      baseTop ≤ s.top.toNat ∧
      s.top.toNat ≤ s.wlen.toNat ∧
      s.rs_n = 0#32 ∧ s.rs_ptop = 0#64 ∧
      s.ptop = 0#64 ∧ s.tn = 0#32 ∧ s.qn = 0#32 ∧
      s.pc = 0#32 ∧ s.tc = 0#32 ∧ s.cur_nr = 0#32 ∧
      (arCtxMem cx s ⋆
        region (s.w + BitVec.ofNat 64 baseTop) (s.top.toNat - baseTop) ⋆
        region (s.w + s.top) (s.wlen.toNat - s.top.toNat) ⋆ R) m ∧
      (∀ (ok : Bool) (m' : Mem 64),
        ((ok = false ∧ ∃ s' : ArCtxState,
            s'.w = s.w ∧ s'.wlen = s.wlen ∧
            (arCtxMem cx s' ⋆
              region (s.w + BitVec.ofNat 64 baseTop) (s.wlen.toNat - baseTop) ⋆ R) m') ∨
         (ok = true ∧ ∃ (s' : ArCtxState)
            (rsM : List (BitVec 32)) (rsL rsH : List (BitVec 64)) (rsPool : List (BitVec 32))
            (tm0 tm1 : List (BitVec 32)) (ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64))
            (pool0 pool1 qm : List (BitVec 32)) (qs ql qh : List (BitVec 64))
            (ix ix2 bx vqOff vq : List (BitVec 32)) (vqSkip : List (BitVec 8))
            (rm : List (BitVec 32)) (rl rh : List (BitVec 64))
            (rm2 : List (BitVec 32)) (rl2 rh2 : List (BitVec 64))
            (rpool : List (BitVec 32)),
            let cap := s'.qcap.toNat
            let pw := s'.pcap.toNat
            16 ≤ cap ∧ cap ≤ 300000000 ∧ pw = 12 * cap ∧
            s'.rs_cap = s'.qcap ∧ s'.tcap = s'.qcap ∧ s'.rcap = s'.qcap ∧
            s'.rs_pcap = s'.pcap ∧ s'.rpcap = s'.pcap ∧
            s'.top.toNat ≤ s'.wlen.toNat ∧
            DynGeom s' s.top.toNat cap ∧
            s' = { s with
              top := s'.top, rs_cap := s'.rs_cap, rs_pcap := s'.rs_pcap,
              tcap := s'.tcap, pcap := s'.pcap, qcap := s'.qcap,
              rcap := s'.rcap, rpcap := s'.rpcap,
              rs_m := s'.rs_m, rs_l := s'.rs_l, rs_h := s'.rs_h, rs_pool := s'.rs_pool,
              tm := s'.tm, ts := s'.ts, tl := s'.tl, th := s'.th, pool := s'.pool,
              qm := s'.qm, qs := s'.qs, ql := s'.ql, qh := s'.qh,
              ix := s'.ix, ix2 := s'.ix2, bx := s'.bx,
              vq_off := s'.vq_off, vq := s'.vq, vq_skip := s'.vq_skip,
              rm := s'.rm, rl := s'.rl, rh := s'.rh,
              rm2 := s'.rm2, rl2 := s'.rl2, rh2 := s'.rh2, rpool := s'.rpool } ∧
            rsM.length = cap ∧ rsL.length = cap ∧ rsH.length = cap ∧ rsPool.length = pw ∧
            tm0.length = cap ∧ tm1.length = cap ∧
            ts0.length = cap ∧ tl0.length = cap ∧ th0.length = cap ∧
            ts1.length = cap ∧ tl1.length = cap ∧ th1.length = cap ∧
            pool0.length = pw ∧ pool1.length = pw ∧
            qm.length = cap ∧ qs.length = cap ∧ ql.length = cap ∧ qh.length = cap ∧
            ix.length = cap ∧ ix2.length = cap ∧ bx.length = cap ∧
            vqOff.length = cap + 1 ∧ vq.length = pw ∧ vqSkip.length = cap ∧
            rm.length = cap ∧ rl.length = cap ∧ rh.length = cap ∧
            rm2.length = cap ∧ rl2.length = cap ∧ rh2.length = cap ∧ rpool.length = pw ∧
            (arCtxMem cx s' ⋆
              region (s.w + BitVec.ofNat 64 baseTop) (align8 s.top.toNat - baseTop) ⋆
              rsMem s' rsM rsL rsH rsPool ⋆
              tMem s' tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
              qMem s' qm qs ql qh ix ix2 bx vqOff vq vqSkip ⋆
              rMem s' rm rl rh rm2 rl2 rh2 rpool ⋆
              region (s'.w + s'.top) (s'.wlen.toNat - s'.top.toNat) ⋆ R) m')) →
        Q (ok, ⟨⟩) m')

end

public section

private theorem align8_add_of_mod {a b : Nat} (ha : a % 8 = 0) : align8 (a + b) = a + align8 b := by
  unfold align8; omega

private theorem pop_dyn_u32 {w : BitVec 64} {off rem : Nat} (n : Nat)
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region (w + BitVec.ofNat 64 off) rem ⋆ R) m)
    (h8 : off % 8 = 0) (hle : align8 (4 * n) ≤ rem) (hle64 : rem ≤ 2 ^ 64) :
    ∃ xs : List (BitVec 32), xs.length = n ∧
      (arrayPad i32 (w + BitVec.ofNat 64 off) xs ⋆
        (region (w + BitVec.ofNat 64 (off + align8 (4 * n))) (rem - align8 (4 * n)) ⋆ R)) m := by
  have hm0 := hm
  rw [show rem = align8 (4 * n) + (rem - align8 (4 * n)) by omega,
    region_split (by omega), sep_assoc, addr_add_ofNat] at hm0
  have ha : align8 off = off := by unfold align8; omega
  obtain ⟨xs, hlen, hm1⟩ := region_pop_alloc_u32 n
    (by rw [ha, Nat.sub_self, Nat.zero_add]; exact align8_ge (4 * n)) (by omega) hm0
  rw [ha, Nat.sub_self, region_zero, emp_sep, ← hlen, ← addr_add_ofNat,
    show align8 (4 * xs.length) - (0 + 4 * xs.length) =
      align8 (4 * xs.length) - 4 * xs.length by omega] at hm1
  exact ⟨xs, hlen, by simpa [hlen] using region_merge_pad_u32 hm1⟩

private theorem pop_dyn_u64 {w : BitVec 64} {off rem : Nat} (n : Nat)
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region (w + BitVec.ofNat 64 off) rem ⋆ R) m)
    (h8 : off % 8 = 0) (hle : 8 * n ≤ rem) (hle64 : rem ≤ 2 ^ 64) :
    ∃ xs : List (BitVec 64), xs.length = n ∧
      (array64 (w + BitVec.ofNat 64 off) xs ⋆
        (region (w + BitVec.ofNat 64 (off + 8 * n)) (rem - 8 * n) ⋆ R)) m := by
  have hm0 := hm
  rw [show rem = 8 * n + (rem - 8 * n) by omega,
    region_split (by omega), sep_assoc, addr_add_ofNat] at hm0
  have ha : align8 off = off := by unfold align8; omega
  obtain ⟨xs, hlen, hm1⟩ := region_pop_alloc_u64 n (by rw [ha]; omega) (by omega) hm0
  rw [ha, Nat.sub_self, region_zero, emp_sep, show 8 * n - (0 + 8 * n) = 0 by omega,
    region_zero] at hm1
  exact ⟨xs, hlen, by simpa [sep_emp] using hm1⟩

private theorem pop_dyn_u8 {w : BitVec 64} {off rem : Nat} (n : Nat)
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region (w + BitVec.ofNat 64 off) rem ⋆ R) m)
    (h8 : off % 8 = 0) (hle : align8 n ≤ rem) (hle64 : rem ≤ 2 ^ 64) :
    ∃ xs : List (BitVec 8), xs.length = n ∧
      (arrayPad i8 (w + BitVec.ofNat 64 off) xs ⋆
        (region (w + BitVec.ofNat 64 (off + align8 n)) (rem - align8 n) ⋆ R)) m := by
  have hm0 := hm
  rw [show rem = align8 n + (rem - align8 n) by omega,
    region_split (by omega), sep_assoc, addr_add_ofNat] at hm0
  have ha : align8 off = off := by unfold align8; omega
  obtain ⟨xs, hlen, hm1⟩ := region_pop_alloc_u8 n
    (by rw [ha, Nat.sub_self, Nat.zero_add]; exact align8_ge n) (by omega) hm0
  rw [ha, Nat.sub_self, region_zero, emp_sep, ← hlen, ← addr_add_ofNat,
    show align8 xs.length - (0 + xs.length) = align8 xs.length - xs.length by omega] at hm1
  exact ⟨xs, hlen, by simpa [hlen] using region_merge_pad_u8 hm1⟩

private theorem dyn_pop_rs {s0 s : ArCtxState} {cap t0 rem : Nat}
    {R : Mem 64 → Prop} {m : Mem 64}
    (ht0_8 : t0 % 8 = 0) (hfit : t0 + rem ≤ 2 ^ 64)
    (hle : align8 (4 * cap) + 16 * cap + 4 * (12 * cap) ≤ rem)
    (hrsm : s.rs_m = s0.w + BitVec.ofNat 64 t0)
    (hrsl : s.rs_l = s0.w + BitVec.ofNat 64 (t0 + align8 (4 * cap)))
    (hrsh : s.rs_h = s0.w + BitVec.ofNat 64 (t0 + align8 (4 * cap) + 8 * cap))
    (hrsp : s.rs_pool = s0.w + BitVec.ofNat 64 (t0 + align8 (4 * cap) + 2 * (8 * cap)))
    (hm : (region (s0.w + BitVec.ofNat 64 t0) rem ⋆ R) m) :
    ∃ (rsM : List (BitVec 32)) (rsL rsH : List (BitVec 64)) (rsPool : List (BitVec 32)),
      rsM.length = cap ∧ rsL.length = cap ∧ rsH.length = cap ∧ rsPool.length = 12 * cap ∧
      (region (s0.w + BitVec.ofNat 64 (t0 + align8 (4 * cap) + 2 * (8 * cap) + 4 * (12 * cap)))
        (rem - (align8 (4 * cap) + 2 * (8 * cap) + 4 * (12 * cap))) ⋆
        rsMem s rsM rsL rsH rsPool ⋆ R) m := by
  let a4 := align8 (4 * cap); let a8 := 8 * cap; let ap := 4 * (12 * cap)
  have h8_a4 : a4 % 8 = 0 := align8_mod _
  have hap_al : align8 (4 * (12 * cap)) = ap := by dsimp only [ap]; unfold align8; omega
  obtain ⟨rsM, hrsM, hm⟩ := pop_dyn_u32 cap hm ht0_8 (by omega) (by omega)
  obtain ⟨rsL, hrsL, hm⟩ := pop_dyn_u64 cap (sep_swap2r hm) (by omega) (by omega) (by omega)
  rw [Nat.sub_sub] at hm
  obtain ⟨rsH, hrsH, hm⟩ := pop_dyn_u64 cap (sep_swap2r hm) (by omega) (by omega) (by omega)
  rw [Nat.sub_sub] at hm
  obtain ⟨rsPool, hrsPool, hm⟩ :=
    pop_dyn_u32 (12 * cap) (sep_swap2r hm) (by omega) (by rw [hap_al]; omega) (by omega)
  rw [hap_al, Nat.sub_sub] at hm
  have hm' := sep_swap2r hm
  rw [show t0 + a4 + a8 + a8 + ap = t0 + a4 + 2 * a8 + ap by omega,
    show rem - (a4 + a8 + a8 + ap) = rem - (a4 + 2 * a8 + ap) by omega] at hm'
  refine ⟨rsM, rsL, rsH, rsPool, hrsM, hrsL, hrsH, hrsPool, ?_⟩
  simp only [rsMem]; rw [hrsm, hrsl, hrsh, hrsp]
  rw [show t0 + a4 + a8 + a8 = t0 + a4 + 2 * a8 by omega] at hm'
  dsimp only [a4, a8, ap] at hm'
  exact sep_cast hm' (by ac_rfl)

private theorem dyn_pop_t {s0 s : ArCtxState} {cap t1 rem : Nat}
    {R : Mem 64 → Prop} {m : Mem 64}
    (ht1_8 : t1 % 8 = 0) (hfit : t1 + rem ≤ 2 ^ 64)
    (hle : 2 * align8 (4 * cap) + 48 * cap + 2 * (4 * (12 * cap)) ≤ rem)
    (htm0 : s.tm.getD 0 0#64 = s0.w + BitVec.ofNat 64 t1)
    (hts0 : s.ts.getD 0 0#64 = s0.w + BitVec.ofNat 64 (t1 + align8 (4 * cap)))
    (htl0 : s.tl.getD 0 0#64 = s0.w + BitVec.ofNat 64 (t1 + align8 (4 * cap) + 8 * cap))
    (hth0 : s.th.getD 0 0#64 = s0.w + BitVec.ofNat 64 (t1 + align8 (4 * cap) + 2 * (8 * cap)))
    (htm1 : s.tm.getD 1 0#64 = s0.w + BitVec.ofNat 64 (t1 + align8 (4 * cap) + 3 * (8 * cap)))
    (hts1 : s.ts.getD 1 0#64 = s0.w + BitVec.ofNat 64 (t1 + 2 * align8 (4 * cap) + 3 * (8 * cap)))
    (htl1 : s.tl.getD 1 0#64 = s0.w + BitVec.ofNat 64 (t1 + 2 * align8 (4 * cap) + 4 * (8 * cap)))
    (hth1 : s.th.getD 1 0#64 = s0.w + BitVec.ofNat 64 (t1 + 2 * align8 (4 * cap) + 5 * (8 * cap)))
    (hp0 : s.pool.getD 0 0#64 = s0.w + BitVec.ofNat 64 (t1 + 2 * align8 (4 * cap) + 6 * (8 * cap)))
    (hp1 : s.pool.getD 1 0#64 =
      s0.w + BitVec.ofNat 64 (t1 + 2 * align8 (4 * cap) + 6 * (8 * cap) + 4 * (12 * cap)))
    (hm : (region (s0.w + BitVec.ofNat 64 t1) rem ⋆ R) m) :
    ∃ (tm0 tm1 : List (BitVec 32)) (ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64))
      (pool0 pool1 : List (BitVec 32)),
      tm0.length = cap ∧ tm1.length = cap ∧
      ts0.length = cap ∧ tl0.length = cap ∧ th0.length = cap ∧
      ts1.length = cap ∧ tl1.length = cap ∧ th1.length = cap ∧
      pool0.length = 12 * cap ∧ pool1.length = 12 * cap ∧
      (region (s0.w + BitVec.ofNat 64
          (t1 + 2 * align8 (4 * cap) + 6 * (8 * cap) + 2 * (4 * (12 * cap))))
        (rem - (2 * align8 (4 * cap) + 6 * (8 * cap) + 2 * (4 * (12 * cap)))) ⋆
        tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆ R) m := by
  let a4 := align8 (4 * cap); let a8 := 8 * cap; let ap := 4 * (12 * cap)
  have h8_a4 : a4 % 8 = 0 := align8_mod _
  have hap_al : align8 (4 * (12 * cap)) = ap := by dsimp only [ap]; unfold align8; omega
  obtain ⟨tm0, htm0_l, hm⟩ := pop_dyn_u32 cap hm ht1_8 (by omega) (by omega)
  obtain ⟨ts0, hts0_l, hm⟩ := pop_dyn_u64 cap (sep_swap2r hm) (by omega) (by omega) (by omega)
  rw [Nat.sub_sub] at hm
  obtain ⟨tl0, htl0_l, hm⟩ := pop_dyn_u64 cap (sep_swap2r hm) (by omega) (by omega) (by omega)
  rw [Nat.sub_sub] at hm
  obtain ⟨th0, hth0_l, hm⟩ := pop_dyn_u64 cap (sep_swap2r hm) (by omega) (by omega) (by omega)
  rw [Nat.sub_sub] at hm
  obtain ⟨tm1, htm1_l, hm⟩ := pop_dyn_u32 cap (sep_swap2r hm) (by omega) (by omega) (by omega)
  rw [Nat.sub_sub] at hm
  obtain ⟨ts1, hts1_l, hm⟩ := pop_dyn_u64 cap (sep_swap2r hm) (by omega) (by omega) (by omega)
  rw [Nat.sub_sub] at hm
  obtain ⟨tl1, htl1_l, hm⟩ := pop_dyn_u64 cap (sep_swap2r hm) (by omega) (by omega) (by omega)
  rw [Nat.sub_sub] at hm
  obtain ⟨th1, hth1_l, hm⟩ := pop_dyn_u64 cap (sep_swap2r hm) (by omega) (by omega) (by omega)
  rw [Nat.sub_sub] at hm
  obtain ⟨pool0, hp0_l, hm⟩ :=
    pop_dyn_u32 (12 * cap) (sep_swap2r hm) (by omega) (by rw [hap_al]; omega) (by omega)
  rw [hap_al, Nat.sub_sub] at hm
  obtain ⟨pool1, hp1_l, hm⟩ :=
    pop_dyn_u32 (12 * cap) (sep_swap2r hm) (by omega) (by rw [hap_al]; omega) (by omega)
  rw [hap_al, Nat.sub_sub] at hm
  have hm' := sep_swap2r hm
  rw [show t1 + a4 + a8 + a8 + a8 + a4 + a8 + a8 + a8 + ap + ap =
      t1 + 2 * a4 + 6 * a8 + 2 * ap by omega,
    show rem - (a4 + a8 + a8 + a8 + a4 + a8 + a8 + a8 + ap + ap) =
      rem - (2 * a4 + 6 * a8 + 2 * ap) by omega] at hm'
  refine ⟨tm0, tm1, ts0, tl0, th0, ts1, tl1, th1, pool0, pool1,
    htm0_l, htm1_l, hts0_l, htl0_l, hth0_l, hts1_l, htl1_l, hth1_l, hp0_l, hp1_l, ?_⟩
  simp only [tMem]; rw [htm0, hts0, htl0, hth0, htm1, hts1, htl1, hth1, hp0, hp1]
  rw [show t1 + a4 + a8 + a8 = t1 + a4 + 2 * a8 by omega,
    show t1 + a4 + 2 * a8 + a8 = t1 + a4 + 3 * a8 by omega,
    show t1 + a4 + 3 * a8 + a4 = t1 + 2 * a4 + 3 * a8 by omega,
    show t1 + 2 * a4 + 3 * a8 + a8 = t1 + 2 * a4 + 4 * a8 by omega,
    show t1 + 2 * a4 + 4 * a8 + a8 = t1 + 2 * a4 + 5 * a8 by omega,
    show t1 + 2 * a4 + 5 * a8 + a8 = t1 + 2 * a4 + 6 * a8 by omega] at hm'
  dsimp only [a4, a8, ap] at hm'
  exact sep_cast hm' (by ac_rfl)

private theorem dyn_pop_q {s0 s : ArCtxState} {cap t2 rem : Nat}
    {R : Mem 64 → Prop} {m : Mem 64}
    (ht2_8 : t2 % 8 = 0) (hfit : t2 + rem ≤ 2 ^ 64)
    (hle : 4 * align8 (4 * cap) + 24 * cap + align8 (4 * cap + 4) +
      4 * (12 * cap) + align8 cap ≤ rem)
    (hqm : s.qm = s0.w + BitVec.ofNat 64 t2)
    (hqs : s.qs = s0.w + BitVec.ofNat 64 (t2 + align8 (4 * cap)))
    (hql : s.ql = s0.w + BitVec.ofNat 64 (t2 + align8 (4 * cap) + 8 * cap))
    (hqh : s.qh = s0.w + BitVec.ofNat 64 (t2 + align8 (4 * cap) + 2 * (8 * cap)))
    (hix : s.ix = s0.w + BitVec.ofNat 64 (t2 + align8 (4 * cap) + 3 * (8 * cap)))
    (hix2 : s.ix2 = s0.w + BitVec.ofNat 64 (t2 + 2 * align8 (4 * cap) + 3 * (8 * cap)))
    (hbx : s.bx = s0.w + BitVec.ofNat 64 (t2 + 3 * align8 (4 * cap) + 3 * (8 * cap)))
    (hvqo : s.vq_off = s0.w + BitVec.ofNat 64 (t2 + 4 * align8 (4 * cap) + 3 * (8 * cap)))
    (hvq : s.vq =
      s0.w + BitVec.ofNat 64 (t2 + 4 * align8 (4 * cap) + 3 * (8 * cap) + align8 (4 * cap + 4)))
    (hvqs : s.vq_skip = s0.w + BitVec.ofNat 64
      (t2 + 4 * align8 (4 * cap) + 3 * (8 * cap) + align8 (4 * cap + 4) + 4 * (12 * cap)))
    (hm : (region (s0.w + BitVec.ofNat 64 t2) rem ⋆ R) m) :
    ∃ (qm : List (BitVec 32)) (qs ql qh : List (BitVec 64))
      (ix ix2 bx vqOff vq : List (BitVec 32)) (vqSkip : List (BitVec 8)),
      qm.length = cap ∧ qs.length = cap ∧ ql.length = cap ∧ qh.length = cap ∧
      ix.length = cap ∧ ix2.length = cap ∧ bx.length = cap ∧
      vqOff.length = cap + 1 ∧ vq.length = 12 * cap ∧ vqSkip.length = cap ∧
      (region (s0.w + BitVec.ofNat 64
          (t2 + 4 * align8 (4 * cap) + 3 * (8 * cap) + align8 (4 * cap + 4) +
            4 * (12 * cap) + align8 cap))
        (rem - (4 * align8 (4 * cap) + 3 * (8 * cap) + align8 (4 * cap + 4) +
          4 * (12 * cap) + align8 cap)) ⋆
        qMem s qm qs ql qh ix ix2 bx vqOff vq vqSkip ⋆ R) m := by
  let a4 := align8 (4 * cap); let a8 := 8 * cap; let ap := 4 * (12 * cap)
  let avo := align8 (4 * cap + 4); let avs := align8 cap
  have h8_a4 : a4 % 8 = 0 := align8_mod _
  have h8_avo : avo % 8 = 0 := align8_mod _
  have h8_avs : avs % 8 = 0 := align8_mod _
  have hap_al : align8 (4 * (12 * cap)) = ap := by dsimp only [ap]; unfold align8; omega
  have h4vo : align8 (4 * (cap + 1)) = avo := by simp only [avo, Nat.mul_add]
  obtain ⟨qm, hqm_l, hm⟩ := pop_dyn_u32 cap hm ht2_8 (by omega) (by omega)
  obtain ⟨qs, hqs_l, hm⟩ := pop_dyn_u64 cap (sep_swap2r hm) (by omega) (by omega) (by omega)
  rw [Nat.sub_sub] at hm
  obtain ⟨ql, hql_l, hm⟩ := pop_dyn_u64 cap (sep_swap2r hm) (by omega) (by omega) (by omega)
  rw [Nat.sub_sub] at hm
  obtain ⟨qh, hqh_l, hm⟩ := pop_dyn_u64 cap (sep_swap2r hm) (by omega) (by omega) (by omega)
  rw [Nat.sub_sub] at hm
  obtain ⟨ix, hix_l, hm⟩ := pop_dyn_u32 cap (sep_swap2r hm) (by omega) (by omega) (by omega)
  rw [Nat.sub_sub] at hm
  obtain ⟨ix2, hix2_l, hm⟩ := pop_dyn_u32 cap (sep_swap2r hm) (by omega) (by omega) (by omega)
  rw [Nat.sub_sub] at hm
  obtain ⟨bx, hbx_l, hm⟩ := pop_dyn_u32 cap (sep_swap2r hm) (by omega) (by omega) (by omega)
  rw [Nat.sub_sub] at hm
  obtain ⟨vqOff, hvqo_l, hm⟩ :=
    pop_dyn_u32 (cap + 1) (sep_swap2r hm) (by omega) (by rw [h4vo]; omega) (by omega)
  rw [h4vo, Nat.sub_sub] at hm
  obtain ⟨vq, hvq_l, hm⟩ :=
    pop_dyn_u32 (12 * cap) (sep_swap2r hm) (by omega) (by rw [hap_al]; omega) (by omega)
  rw [hap_al, Nat.sub_sub] at hm
  obtain ⟨vqSkip, hvqs_l, hm⟩ := pop_dyn_u8 cap (sep_swap2r hm) (by omega) (by omega) (by omega)
  rw [Nat.sub_sub] at hm
  have hm' := sep_swap2r hm
  rw [show t2 + a4 + a8 + a8 + a8 + a4 + a4 + a4 + avo + ap + avs =
      t2 + 4 * a4 + 3 * a8 + avo + ap + avs by omega,
    show rem - (a4 + a8 + a8 + a8 + a4 + a4 + a4 + avo + ap + avs) =
      rem - (4 * a4 + 3 * a8 + avo + ap + avs) by omega] at hm'
  refine ⟨qm, qs, ql, qh, ix, ix2, bx, vqOff, vq, vqSkip,
    hqm_l, hqs_l, hql_l, hqh_l, hix_l, hix2_l, hbx_l, hvqo_l, hvq_l, hvqs_l, ?_⟩
  simp only [qMem]; rw [hqm, hqs, hql, hqh, hix, hix2, hbx, hvqo, hvq, hvqs]
  rw [show t2 + a4 + a8 + a8 = t2 + a4 + 2 * a8 by omega,
    show t2 + a4 + 2 * a8 + a8 = t2 + a4 + 3 * a8 by omega,
    show t2 + a4 + 3 * a8 + a4 = t2 + 2 * a4 + 3 * a8 by omega,
    show t2 + 2 * a4 + 3 * a8 + a4 = t2 + 3 * a4 + 3 * a8 by omega,
    show t2 + 3 * a4 + 3 * a8 + a4 = t2 + 4 * a4 + 3 * a8 by omega] at hm'
  dsimp only [a4, a8, ap, avo, avs] at hm'
  exact sep_cast hm' (by ac_rfl)

private theorem dyn_pop_r {s0 s : ArCtxState} {cap t3 rem : Nat}
    {R : Mem 64 → Prop} {m : Mem 64}
    (ht3_8 : t3 % 8 = 0) (hfit : t3 + rem ≤ 2 ^ 64)
    (hle : rem = 2 * align8 (4 * cap) + 4 * (8 * cap) + 4 * (12 * cap))
    (hrm : s.rm = s0.w + BitVec.ofNat 64 t3)
    (hrl : s.rl = s0.w + BitVec.ofNat 64 (t3 + align8 (4 * cap)))
    (hrh : s.rh = s0.w + BitVec.ofNat 64 (t3 + align8 (4 * cap) + 8 * cap))
    (hrm2 : s.rm2 = s0.w + BitVec.ofNat 64 (t3 + align8 (4 * cap) + 2 * (8 * cap)))
    (hrl2 : s.rl2 = s0.w + BitVec.ofNat 64 (t3 + 2 * align8 (4 * cap) + 2 * (8 * cap)))
    (hrh2 : s.rh2 = s0.w + BitVec.ofNat 64 (t3 + 2 * align8 (4 * cap) + 3 * (8 * cap)))
    (hrp : s.rpool = s0.w + BitVec.ofNat 64 (t3 + 2 * align8 (4 * cap) + 4 * (8 * cap)))
    (hm : (region (s0.w + BitVec.ofNat 64 t3) rem ⋆ R) m) :
    ∃ (rm : List (BitVec 32)) (rl rh : List (BitVec 64))
      (rm2 : List (BitVec 32)) (rl2 rh2 : List (BitVec 64)) (rpool : List (BitVec 32)),
      rm.length = cap ∧ rl.length = cap ∧ rh.length = cap ∧
      rm2.length = cap ∧ rl2.length = cap ∧ rh2.length = cap ∧ rpool.length = 12 * cap ∧
      (rMem s rm rl rh rm2 rl2 rh2 rpool ⋆ R) m := by
  let a4 := align8 (4 * cap); let a8 := 8 * cap; let ap := 4 * (12 * cap)
  have h8_a4 : a4 % 8 = 0 := align8_mod _
  have hap_al : align8 (4 * (12 * cap)) = ap := by dsimp only [ap]; unfold align8; omega
  obtain ⟨rm, hrm_l, hm⟩ := pop_dyn_u32 cap hm ht3_8 (by omega) (by omega)
  obtain ⟨rl, hrl_l, hm⟩ := pop_dyn_u64 cap (sep_swap2r hm) (by omega) (by omega) (by omega)
  rw [Nat.sub_sub] at hm
  obtain ⟨rh, hrh_l, hm⟩ := pop_dyn_u64 cap (sep_swap2r hm) (by omega) (by omega) (by omega)
  rw [Nat.sub_sub] at hm
  obtain ⟨rm2, hrm2_l, hm⟩ := pop_dyn_u32 cap (sep_swap2r hm) (by omega) (by omega) (by omega)
  rw [Nat.sub_sub] at hm
  obtain ⟨rl2, hrl2_l, hm⟩ := pop_dyn_u64 cap (sep_swap2r hm) (by omega) (by omega) (by omega)
  rw [Nat.sub_sub] at hm
  obtain ⟨rh2, hrh2_l, hm⟩ := pop_dyn_u64 cap (sep_swap2r hm) (by omega) (by omega) (by omega)
  rw [Nat.sub_sub] at hm
  obtain ⟨rpool, hrp_l, hm⟩ :=
    pop_dyn_u32 (12 * cap) (sep_swap2r hm) (by omega) (by rw [hap_al]; omega) (by omega)
  rw [hap_al, Nat.sub_sub] at hm
  have hm' := sep_swap2r hm
  rw [show rem - (a4 + a8 + a8 + a4 + a8 + a8 + ap) = 0 by omega, region_zero, emp_sep] at hm'
  refine ⟨rm, rl, rh, rm2, rl2, rh2, rpool, hrm_l, hrl_l, hrh_l, hrm2_l, hrl2_l, hrh2_l, hrp_l, ?_⟩
  simp only [rMem]; rw [hrm, hrl, hrh, hrm2, hrl2, hrh2, hrp]
  rw [show t3 + a4 + a8 + a8 = t3 + a4 + 2 * a8 by omega,
    show t3 + a4 + 2 * a8 + a4 = t3 + 2 * a4 + 2 * a8 by omega,
    show t3 + 2 * a4 + 2 * a8 + a8 = t3 + 2 * a4 + 3 * a8 by omega,
    show t3 + 2 * a4 + 3 * a8 + a8 = t3 + 2 * a4 + 4 * a8 by omega] at hm'
  dsimp only [a4, a8, ap] at hm'
  exact sep_cast hm' (by ac_rfl)

private theorem dyn_pop_repack {s0 s : ArCtxState} {baseTop : Nat}
    {rsM rsPool tm0 tm1 pool0 pool1 qm ix ix2 bx vqOff vq rm rm2 rpool : List (BitVec 32)}
    {rsL rsH ts0 tl0 th0 ts1 tl1 th1 qs ql qh rl rh rl2 rh2 : List (BitVec 64)}
    {vqSkip : List (BitVec 8)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (rMem s rm rl rh rm2 rl2 rh2 rpool ⋆ (qMem s qm qs ql qh ix ix2 bx vqOff vq vqSkip ⋆
      (tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆ (rsMem s rsM rsL rsH rsPool ⋆
      (region (s0.w + BitVec.ofNat 64 baseTop) (align8 s0.top.toNat - baseTop) ⋆ R))))) m) :
    (region (s0.w + BitVec.ofNat 64 baseTop) (align8 s0.top.toNat - baseTop) ⋆
      rsMem s rsM rsL rsH rsPool ⋆ tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
      qMem s qm qs ql qh ix ix2 bx vqOff vq vqSkip ⋆
      rMem s rm rl rh rm2 rl2 rh2 rpool ⋆ R) m :=
  sep_cast hm (by ac_rfl)

private theorem dyn_pop_rs_t {s0 s : ArCtxState} {baseTop cap t0 t1 t2 : Nat}
    {R : Mem 64 → Prop} {m : Mem 64}
    (ht0 : t0 = align8 s0.top.toNat) (ht0_le : t0 ≤ s.top.toNat)
    (ht1 : t1 = align8 s0.top.toNat + align8 (4 * cap) + 2 * (8 * cap) + 4 * (12 * cap))
    (ht2 : t2 = t1 + 2 * align8 (4 * cap) + 6 * (8 * cap) + 2 * (4 * (12 * cap)))
    (h8_t0 : t0 % 8 = 0) (_hfit : s.top.toNat ≤ 2 ^ 64)
    (hle : 3 * align8 (4 * cap) + 8 * (8 * cap) + 3 * (4 * (12 * cap)) ≤ s.top.toNat - t0)
    (hrs_ptrs :
      let t0 := align8 s0.top.toNat; let a4 := align8 (4 * cap); let a8 := 8 * cap
      s.rs_m = s0.w + BitVec.ofNat 64 t0 ∧ s.rs_l = s0.w + BitVec.ofNat 64 (t0 + a4) ∧
      s.rs_h = s0.w + BitVec.ofNat 64 (t0 + a4 + a8) ∧
      s.rs_pool = s0.w + BitVec.ofNat 64 (t0 + a4 + 2 * a8))
    (ht_ptrs :
      let t1 := align8 s0.top.toNat + align8 (4 * cap) + 2 * (8 * cap) + 4 * (12 * cap)
      let a4 := align8 (4 * cap); let a8 := 8 * cap; let ap := 4 * (12 * cap)
      s.tm.getD 0 0#64 = s0.w + BitVec.ofNat 64 t1 ∧
      s.ts.getD 0 0#64 = s0.w + BitVec.ofNat 64 (t1 + a4) ∧
      s.tl.getD 0 0#64 = s0.w + BitVec.ofNat 64 (t1 + a4 + a8) ∧
      s.th.getD 0 0#64 = s0.w + BitVec.ofNat 64 (t1 + a4 + 2 * a8) ∧
      s.tm.getD 1 0#64 = s0.w + BitVec.ofNat 64 (t1 + a4 + 3 * a8) ∧
      s.ts.getD 1 0#64 = s0.w + BitVec.ofNat 64 (t1 + 2 * a4 + 3 * a8) ∧
      s.tl.getD 1 0#64 = s0.w + BitVec.ofNat 64 (t1 + 2 * a4 + 4 * a8) ∧
      s.th.getD 1 0#64 = s0.w + BitVec.ofNat 64 (t1 + 2 * a4 + 5 * a8) ∧
      s.pool.getD 0 0#64 = s0.w + BitVec.ofNat 64 (t1 + 2 * a4 + 6 * a8) ∧
      s.pool.getD 1 0#64 = s0.w + BitVec.ofNat 64 (t1 + 2 * a4 + 6 * a8 + ap))
    (hm : (region (s0.w + BitVec.ofNat 64 t0) (s.top.toNat - t0) ⋆
      (region (s0.w + BitVec.ofNat 64 baseTop) (t0 - baseTop) ⋆ R)) m) :
    ∃ (rsM : List (BitVec 32)) (rsL rsH : List (BitVec 64)) (rsPool tm0 tm1 : List (BitVec 32))
      (ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64)) (pool0 pool1 : List (BitVec 32)),
      rsM.length = cap ∧ rsL.length = cap ∧ rsH.length = cap ∧ rsPool.length = 12 * cap ∧
      tm0.length = cap ∧ tm1.length = cap ∧ ts0.length = cap ∧ tl0.length = cap ∧
      th0.length = cap ∧ ts1.length = cap ∧ tl1.length = cap ∧ th1.length = cap ∧
      pool0.length = 12 * cap ∧ pool1.length = 12 * cap ∧
      (region (s0.w + BitVec.ofNat 64 t2) (s.top.toNat - t2) ⋆
        (tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
        (rsMem s rsM rsL rsH rsPool ⋆
        (region (s0.w + BitVec.ofNat 64 baseTop) (t0 - baseTop) ⋆ R)))) m := by
  rcases hrs_ptrs with ⟨hrsm, hrsl, hrsh, hrsp⟩
  rcases ht_ptrs with ⟨htm0, hts0, htl0, hth0, htm1, hts1, htl1, hth1, hp0, hp1⟩
  have ht1_eq : t1 = t0 + align8 (4 * cap) + 2 * (8 * cap) + 4 * (12 * cap) := by omega
  have ht1_8 : t1 % 8 = 0 := by rw [ht1_eq]; have := align8_mod (4 * cap); omega
  let r0 := region (s0.w + BitVec.ofNat 64 baseTop) (t0 - baseTop) ⋆ R
  obtain ⟨rsM, rsL, rsH, rsPool, hrsM, hrsL, hrsH, hrsPool, hm1⟩ :=
    dyn_pop_rs (s0 := s0) (s := s) (cap := cap) (t0 := t0) (rem := s.top.toNat - t0) (R := r0)
      h8_t0 (by omega) (by omega)
      (ht0 ▸ hrsm) (ht0 ▸ hrsl) (ht0 ▸ hrsh) (ht0 ▸ hrsp) hm
  rw [sep_assoc, ← ht1_eq,
    show s.top.toNat - t0 - (align8 (4 * cap) + 2 * (8 * cap) + 4 * (12 * cap)) =
      s.top.toNat - t1 by rw [ht1_eq]; omega] at hm1
  let r1 := rsMem s rsM rsL rsH rsPool ⋆ r0
  obtain ⟨tm0, tm1, ts0, tl0, th0, ts1, tl1, th1, pool0, pool1,
    htm0_l, htm1_l, hts0_l, htl0_l, hth0_l, hts1_l, htl1_l, hth1_l, hp0_l, hp1_l, hm2⟩ :=
    dyn_pop_t (s0 := s0) (s := s) (cap := cap) (t1 := t1) (rem := s.top.toNat - t1) (R := r1)
      ht1_8 (by rw [ht1_eq]; omega) (by rw [ht1_eq] at *; omega)
      (ht1 ▸ htm0) (ht1 ▸ hts0) (ht1 ▸ htl0) (ht1 ▸ hth0) (ht1 ▸ htm1)
      (ht1 ▸ hts1) (ht1 ▸ htl1) (ht1 ▸ hth1) (ht1 ▸ hp0) (ht1 ▸ hp1) hm1
  rw [sep_assoc, ← ht2,
    show s.top.toNat - t1 - (2 * align8 (4 * cap) + 6 * (8 * cap) + 2 * (4 * (12 * cap))) =
      s.top.toNat - t2 by rw [ht2]; omega] at hm2
  exact ⟨rsM, rsL, rsH, rsPool, tm0, tm1, ts0, tl0, th0, ts1, tl1, th1, pool0, pool1,
    hrsM, hrsL, hrsH, hrsPool, htm0_l, htm1_l, hts0_l, htl0_l, hth0_l, hts1_l, htl1_l, hth1_l,
    hp0_l, hp1_l, hm2⟩

private theorem dyn_pop_q_r {s0 s : ArCtxState} {cap t2 t3 : Nat}
    {R : Mem 64 → Prop} {m : Mem 64}
    (ht2_le : t2 ≤ s.top.toNat)
    (ht2 : t2 = align8 s0.top.toNat + 3 * align8 (4 * cap) + 8 * (8 * cap) + 3 * (4 * (12 * cap)))
    (ht3 : t3 = align8 s0.top.toNat + 7 * align8 (4 * cap) + 11 * (8 * cap) +
      4 * (4 * (12 * cap)) + align8 (4 * cap + 4) + align8 cap)
    (ht2_8 : t2 % 8 = 0) (_hfit : s.top.toNat ≤ 2 ^ 64)
    (hle : s.top.toNat - t2 = 6 * align8 (4 * cap) + 7 * (8 * cap) + align8 (4 * cap + 4) +
      8 * (12 * cap) + align8 cap)
    (hq_ptrs :
      let t2 := align8 s0.top.toNat + 3 * align8 (4 * cap) + 8 * (8 * cap) + 3 * (4 * (12 * cap))
      let a4 := align8 (4 * cap); let a8 := 8 * cap; let ap := 4 * (12 * cap)
      let avo := align8 (4 * cap + 4)
      s.qm = s0.w + BitVec.ofNat 64 t2 ∧ s.qs = s0.w + BitVec.ofNat 64 (t2 + a4) ∧
      s.ql = s0.w + BitVec.ofNat 64 (t2 + a4 + a8) ∧
      s.qh = s0.w + BitVec.ofNat 64 (t2 + a4 + 2 * a8) ∧
      s.ix = s0.w + BitVec.ofNat 64 (t2 + a4 + 3 * a8) ∧
      s.ix2 = s0.w + BitVec.ofNat 64 (t2 + 2 * a4 + 3 * a8) ∧
      s.bx = s0.w + BitVec.ofNat 64 (t2 + 3 * a4 + 3 * a8) ∧
      s.vq_off = s0.w + BitVec.ofNat 64 (t2 + 4 * a4 + 3 * a8) ∧
      s.vq = s0.w + BitVec.ofNat 64 (t2 + 4 * a4 + 3 * a8 + avo) ∧
      s.vq_skip = s0.w + BitVec.ofNat 64 (t2 + 4 * a4 + 3 * a8 + avo + ap))
    (hr_ptrs :
      let t3 := align8 s0.top.toNat + 7 * align8 (4 * cap) + 11 * (8 * cap) +
        4 * (4 * (12 * cap)) + align8 (4 * cap + 4) + align8 cap
      let a4 := align8 (4 * cap); let a8 := 8 * cap
      s.rm = s0.w + BitVec.ofNat 64 t3 ∧ s.rl = s0.w + BitVec.ofNat 64 (t3 + a4) ∧
      s.rh = s0.w + BitVec.ofNat 64 (t3 + a4 + a8) ∧
      s.rm2 = s0.w + BitVec.ofNat 64 (t3 + a4 + 2 * a8) ∧
      s.rl2 = s0.w + BitVec.ofNat 64 (t3 + 2 * a4 + 2 * a8) ∧
      s.rh2 = s0.w + BitVec.ofNat 64 (t3 + 2 * a4 + 3 * a8) ∧
      s.rpool = s0.w + BitVec.ofNat 64 (t3 + 2 * a4 + 4 * a8))
    (hm : (region (s0.w + BitVec.ofNat 64 t2) (s.top.toNat - t2) ⋆ R) m) :
    ∃ (qm : List (BitVec 32)) (qs ql qh : List (BitVec 64))
      (ix ix2 bx vqOff vq : List (BitVec 32)) (vqSkip : List (BitVec 8))
      (rm : List (BitVec 32)) (rl rh : List (BitVec 64))
      (rm2 : List (BitVec 32)) (rl2 rh2 : List (BitVec 64)) (rpool : List (BitVec 32)),
      qm.length = cap ∧ qs.length = cap ∧ ql.length = cap ∧ qh.length = cap ∧
      ix.length = cap ∧ ix2.length = cap ∧ bx.length = cap ∧
      vqOff.length = cap + 1 ∧ vq.length = 12 * cap ∧ vqSkip.length = cap ∧
      rm.length = cap ∧ rl.length = cap ∧ rh.length = cap ∧
      rm2.length = cap ∧ rl2.length = cap ∧ rh2.length = cap ∧ rpool.length = 12 * cap ∧
      (rMem s rm rl rh rm2 rl2 rh2 rpool ⋆
        (qMem s qm qs ql qh ix ix2 bx vqOff vq vqSkip ⋆ R)) m := by
  rcases hq_ptrs with ⟨hqm, hqs, hql, hqh, hix, hix2, hbx, hvqo, hvq, hvqs⟩
  rcases hr_ptrs with ⟨hrm, hrl, hrh, hrm2, hrl2, hrh2, hrp⟩
  have ht3_eq : t3 = t2 + 4 * align8 (4 * cap) + 3 * (8 * cap) + align8 (4 * cap + 4) +
      4 * (12 * cap) + align8 cap := by rw [ht3, ht2]; omega
  have ht3_8 : t3 % 8 = 0 := by
    rw [ht3_eq]; have := align8_mod (4 * cap); have := align8_mod (4 * cap + 4)
    have := align8_mod cap; omega
  obtain ⟨qm, qs, ql, qh, ix, ix2, bx, vqOff, vq, vqSkip,
    hqm_l, hqs_l, hql_l, hqh_l, hix_l, hix2_l, hbx_l, hvqo_l, hvq_l, hvqs_l, hm3⟩ :=
    dyn_pop_q (s0 := s0) (s := s) (cap := cap) (t2 := t2) (rem := s.top.toNat - t2) (R := R)
      ht2_8 (by omega) (by omega)
      (ht2 ▸ hqm) (ht2 ▸ hqs) (ht2 ▸ hql) (ht2 ▸ hqh) (ht2 ▸ hix)
      (ht2 ▸ hix2) (ht2 ▸ hbx) (ht2 ▸ hvqo) (ht2 ▸ hvq) (ht2 ▸ hvqs) hm
  rw [sep_assoc, ← ht3_eq, show s.top.toNat - t2 - (4 * align8 (4 * cap) + 3 * (8 * cap) +
    align8 (4 * cap + 4) + 4 * (12 * cap) + align8 cap) = s.top.toNat - t3 by
    rw [ht3_eq]; omega] at hm3
  obtain ⟨rm, rl, rh, rm2, rl2, rh2, rpool,
    hrm_l, hrl_l, hrh_l, hrm2_l, hrl2_l, hrh2_l, hrp_l, hm4⟩ :=
    dyn_pop_r (s0 := s0) (s := s) (cap := cap) (t3 := t3) (rem := s.top.toNat - t3)
      (R := qMem s qm qs ql qh ix ix2 bx vqOff vq vqSkip ⋆ R)
      ht3_8 (by rw [ht3_eq]; omega) (by rw [ht3_eq]; omega)
      (ht3 ▸ hrm) (ht3 ▸ hrl) (ht3 ▸ hrh) (ht3 ▸ hrm2)
      (ht3 ▸ hrl2) (ht3 ▸ hrh2) (ht3 ▸ hrp) hm3
  exact ⟨qm, qs, ql, qh, ix, ix2, bx, vqOff, vq, vqSkip, rm, rl, rh, rm2, rl2, rh2, rpool,
    hqm_l, hqs_l, hql_l, hqh_l, hix_l, hix2_l, hbx_l, hvqo_l, hvq_l, hvqs_l,
    hrm_l, hrl_l, hrh_l, hrm2_l, hrl2_l, hrh2_l, hrp_l, hm4⟩

private theorem dyn_rs_t_hle (a4 a8 ap avo avs : Nat) :
    3 * a4 + 8 * a8 + 3 * ap ≤ 9 * a4 + 15 * a8 + 5 * ap + avo + avs := by omega

private theorem dyn_t2_le (t0 a4 a8 ap avo avs : Nat) :
    t0 + 3 * a4 + 8 * a8 + 3 * ap ≤ t0 + (9 * a4 + 15 * a8 + 5 * ap + avo + avs) := by omega

private theorem dyn_t2_rem (t0 cap a4 a8 avo avs : Nat) :
    t0 + (9 * a4 + 15 * a8 + 5 * (4 * (12 * cap)) + avo + avs) -
      (t0 + 3 * a4 + 8 * a8 + 3 * (4 * (12 * cap))) =
      6 * a4 + 7 * a8 + avo + 8 * (12 * cap) + avs := by omega

private theorem dyn_t2_def (t0 a4 a8 ap : Nat) :
    t0 + 3 * a4 + 8 * a8 + 3 * ap =
      t0 + a4 + 2 * a8 + ap + 2 * a4 + 6 * a8 + 2 * ap := by omega

private theorem dyn_pop_alloc {s0 s : ArCtxState} {baseTop cap : Nat}
    {R : Mem 64 → Prop} {m : Mem 64}
    (_htop0 : baseTop ≤ align8 s0.top.toNat) (htop_le : align8 s0.top.toNat ≤ s.top.toNat)
    (hfit : s.top.toNat ≤ 2 ^ 64)
    (_hcap_eq : s.qcap.toNat = cap) (_hpw_eq : s.pcap.toNat = 12 * cap)
    (hs_fin : s.top.toNat = dynEndTop s0.top.toNat cap)
    (hrs_ptrs :
      let t0 := align8 s0.top.toNat; let a4 := align8 (4 * cap); let a8 := 8 * cap
      s.rs_m = s0.w + BitVec.ofNat 64 t0 ∧ s.rs_l = s0.w + BitVec.ofNat 64 (t0 + a4) ∧
      s.rs_h = s0.w + BitVec.ofNat 64 (t0 + a4 + a8) ∧
      s.rs_pool = s0.w + BitVec.ofNat 64 (t0 + a4 + 2 * a8))
    (ht_ptrs :
      let t1 := align8 s0.top.toNat + align8 (4 * cap) + 2 * (8 * cap) + 4 * (12 * cap)
      let a4 := align8 (4 * cap); let a8 := 8 * cap; let ap := 4 * (12 * cap)
      s.tm.getD 0 0#64 = s0.w + BitVec.ofNat 64 t1 ∧
      s.ts.getD 0 0#64 = s0.w + BitVec.ofNat 64 (t1 + a4) ∧
      s.tl.getD 0 0#64 = s0.w + BitVec.ofNat 64 (t1 + a4 + a8) ∧
      s.th.getD 0 0#64 = s0.w + BitVec.ofNat 64 (t1 + a4 + 2 * a8) ∧
      s.tm.getD 1 0#64 = s0.w + BitVec.ofNat 64 (t1 + a4 + 3 * a8) ∧
      s.ts.getD 1 0#64 = s0.w + BitVec.ofNat 64 (t1 + 2 * a4 + 3 * a8) ∧
      s.tl.getD 1 0#64 = s0.w + BitVec.ofNat 64 (t1 + 2 * a4 + 4 * a8) ∧
      s.th.getD 1 0#64 = s0.w + BitVec.ofNat 64 (t1 + 2 * a4 + 5 * a8) ∧
      s.pool.getD 0 0#64 = s0.w + BitVec.ofNat 64 (t1 + 2 * a4 + 6 * a8) ∧
      s.pool.getD 1 0#64 = s0.w + BitVec.ofNat 64 (t1 + 2 * a4 + 6 * a8 + ap))
    (hq_ptrs :
      let t2 := align8 s0.top.toNat + 3 * align8 (4 * cap) + 8 * (8 * cap) + 3 * (4 * (12 * cap))
      let a4 := align8 (4 * cap); let a8 := 8 * cap; let ap := 4 * (12 * cap)
      let avo := align8 (4 * cap + 4)
      s.qm = s0.w + BitVec.ofNat 64 t2 ∧ s.qs = s0.w + BitVec.ofNat 64 (t2 + a4) ∧
      s.ql = s0.w + BitVec.ofNat 64 (t2 + a4 + a8) ∧
      s.qh = s0.w + BitVec.ofNat 64 (t2 + a4 + 2 * a8) ∧
      s.ix = s0.w + BitVec.ofNat 64 (t2 + a4 + 3 * a8) ∧
      s.ix2 = s0.w + BitVec.ofNat 64 (t2 + 2 * a4 + 3 * a8) ∧
      s.bx = s0.w + BitVec.ofNat 64 (t2 + 3 * a4 + 3 * a8) ∧
      s.vq_off = s0.w + BitVec.ofNat 64 (t2 + 4 * a4 + 3 * a8) ∧
      s.vq = s0.w + BitVec.ofNat 64 (t2 + 4 * a4 + 3 * a8 + avo) ∧
      s.vq_skip = s0.w + BitVec.ofNat 64 (t2 + 4 * a4 + 3 * a8 + avo + ap))
    (hr_ptrs :
      let t3 := align8 s0.top.toNat + 7 * align8 (4 * cap) + 11 * (8 * cap) +
        4 * (4 * (12 * cap)) + align8 (4 * cap + 4) + align8 cap
      let a4 := align8 (4 * cap); let a8 := 8 * cap
      s.rm = s0.w + BitVec.ofNat 64 t3 ∧ s.rl = s0.w + BitVec.ofNat 64 (t3 + a4) ∧
      s.rh = s0.w + BitVec.ofNat 64 (t3 + a4 + a8) ∧
      s.rm2 = s0.w + BitVec.ofNat 64 (t3 + a4 + 2 * a8) ∧
      s.rl2 = s0.w + BitVec.ofNat 64 (t3 + 2 * a4 + 2 * a8) ∧
      s.rh2 = s0.w + BitVec.ofNat 64 (t3 + 2 * a4 + 3 * a8) ∧
      s.rpool = s0.w + BitVec.ofNat 64 (t3 + 2 * a4 + 4 * a8))
    (hm : (region (s0.w + BitVec.ofNat 64 baseTop) (s.top.toNat - baseTop) ⋆ R) m) :
    ∃ (rsM : List (BitVec 32)) (rsL rsH : List (BitVec 64)) (rsPool tm0 tm1 : List (BitVec 32))
      (ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64)) (pool0 pool1 qm : List (BitVec 32))
      (qs ql qh : List (BitVec 64)) (ix ix2 bx vqOff vq : List (BitVec 32))
      (vqSkip : List (BitVec 8)) (rm : List (BitVec 32)) (rl rh : List (BitVec 64))
      (rm2 : List (BitVec 32)) (rl2 rh2 : List (BitVec 64)) (rpool : List (BitVec 32)),
      rsM.length = cap ∧ rsL.length = cap ∧ rsH.length = cap ∧ rsPool.length = 12 * cap ∧
      tm0.length = cap ∧ tm1.length = cap ∧ ts0.length = cap ∧ tl0.length = cap ∧
      th0.length = cap ∧ ts1.length = cap ∧ tl1.length = cap ∧ th1.length = cap ∧
      pool0.length = 12 * cap ∧ pool1.length = 12 * cap ∧ qm.length = cap ∧ qs.length = cap ∧
      ql.length = cap ∧ qh.length = cap ∧ ix.length = cap ∧ ix2.length = cap ∧
      bx.length = cap ∧ vqOff.length = cap + 1 ∧ vq.length = 12 * cap ∧ vqSkip.length = cap ∧
      rm.length = cap ∧ rl.length = cap ∧ rh.length = cap ∧ rm2.length = cap ∧
      rl2.length = cap ∧ rh2.length = cap ∧ rpool.length = 12 * cap ∧
      (region (s0.w + BitVec.ofNat 64 baseTop) (align8 s0.top.toNat - baseTop) ⋆
        rsMem s rsM rsL rsH rsPool ⋆ tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
        qMem s qm qs ql qh ix ix2 bx vqOff vq vqSkip ⋆
        rMem s rm rl rh rm2 rl2 rh2 rpool ⋆ R) m := by
  let a4 := align8 (4 * cap); let a8 := 8 * cap; let ap := 4 * (12 * cap)
  let avo := align8 (4 * cap + 4); let avs := align8 cap
  let t1 := align8 s0.top.toNat + a4 + 2 * a8 + ap
  let t2 := align8 s0.top.toNat + 3 * a4 + 8 * a8 + 3 * ap
  let t3 := align8 s0.top.toNat + 7 * a4 + 11 * a8 + 4 * ap + avo + avs
  have h8_t0 : align8 s0.top.toNat % 8 = 0 := align8_mod _
  have h8_t2 : t2 % 8 = 0 := by
    have := align8_mod (4 * cap); dsimp only [t2, a4, a8, ap]; omega
  have hrem_tot : s.top.toNat - align8 s0.top.toNat = 9 * a4 + 15 * a8 + 5 * ap + avo + avs := by
    rw [hs_fin]; dsimp only [dynEndTop]; omega
  have htop_eq : s.top.toNat = align8 s0.top.toNat + (9 * a4 + 15 * a8 + 5 * ap + avo + avs) := by
    rw [← hrem_tot]; exact (Nat.add_sub_of_le htop_le).symm
  have hlt_t2 : t2 ≤ s.top.toNat := by
    rw [htop_eq]; exact dyn_t2_le (align8 s0.top.toNat) a4 a8 ap avo avs
  have hrem_t2 : s.top.toNat - t2 =
      6 * a4 + 7 * a8 + avo + 8 * (12 * cap) + avs := by
    rw [htop_eq]; exact dyn_t2_rem (align8 s0.top.toNat) cap a4 a8 avo avs
  have hm_split : (region (s0.w + BitVec.ofNat 64 (align8 s0.top.toNat))
      (s.top.toNat - align8 s0.top.toNat) ⋆
      (region (s0.w + BitVec.ofNat 64 baseTop) (align8 s0.top.toNat - baseTop) ⋆ R)) m := by
    have hm0 := hm
    rw [show s.top.toNat - baseTop =
        (align8 s0.top.toNat - baseTop) + (s.top.toNat - align8 s0.top.toNat) by omega,
      region_split (by omega), sep_assoc, addr_add_ofNat,
      show baseTop + (align8 s0.top.toNat - baseTop) = align8 s0.top.toNat by omega] at hm0
    exact sep_cast hm0 (by ac_rfl)
  obtain ⟨rsM, rsL, rsH, rsPool, tm0, tm1, ts0, tl0, th0, ts1, tl1, th1, pool0, pool1,
    hrsM, hrsL, hrsH, hrsPool, htm0_l, htm1_l, hts0_l, htl0_l, hth0_l, hts1_l, htl1_l, hth1_l,
    hp0_l, hp1_l, hm2⟩ :=
    dyn_pop_rs_t (s0 := s0) (s := s) (baseTop := baseTop) (cap := cap)
      (t0 := align8 s0.top.toNat) (t1 := t1) (t2 := t2) (R := R) rfl htop_le rfl
      (dyn_t2_def (align8 s0.top.toNat) a4 a8 ap) h8_t0 hfit
      (hrem_tot ▸ dyn_rs_t_hle a4 a8 ap avo avs) hrs_ptrs ht_ptrs hm_split
  obtain ⟨qm, qs, ql, qh, ix, ix2, bx, vqOff, vq, vqSkip, rm, rl, rh, rm2, rl2, rh2, rpool,
    hqm_l, hqs_l, hql_l, hqh_l, hix_l, hix2_l, hbx_l, hvqo_l, hvq_l, hvqs_l,
    hrm_l, hrl_l, hrh_l, hrm2_l, hrl2_l, hrh2_l, hrp_l, hm4⟩ :=
    dyn_pop_q_r (s0 := s0) (s := s) (cap := cap) (t2 := t2) (t3 := t3)
      (R := tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
        (rsMem s rsM rsL rsH rsPool ⋆
          (region (s0.w + BitVec.ofNat 64 baseTop) (align8 s0.top.toNat - baseTop) ⋆ R)))
      hlt_t2 rfl rfl h8_t2 hfit hrem_t2 hq_ptrs hr_ptrs hm2
  exact ⟨rsM, rsL, rsH, rsPool, tm0, tm1, ts0, tl0, th0, ts1, tl1, th1, pool0, pool1,
    qm, qs, ql, qh, ix, ix2, bx, vqOff, vq, vqSkip, rm, rl, rh, rm2, rl2, rh2, rpool,
    hrsM, hrsL, hrsH, hrsPool, htm0_l, htm1_l, hts0_l, htl0_l, hth0_l, hts1_l, htl1_l, hth1_l,
    hp0_l, hp1_l, hqm_l, hqs_l, hql_l, hqh_l, hix_l, hix2_l, hbx_l, hvqo_l, hvq_l, hvqs_l,
    hrm_l, hrl_l, hrh_l, hrm2_l, hrl2_l, hrh2_l, hrp_l,
    dyn_pop_repack (s0 := s0) (s := s) (baseTop := baseTop) hm4⟩

public theorem align8_sub_le (n : Nat) : align8 n ≤ n + 7 := by unfold align8; omega

public theorem dyn_slack_le {wlen : Nat} (top0 cap : Nat) (htop : align8 top0 ≤ top0 + 7)
    (hrem : 401 * cap + 4096 ≤ wlen - top0) :
    dynEndTop top0 cap ≤ wlen := by
  have ha4 := align8_sub_le (4 * cap)
  have havo := align8_sub_le (4 * cap + 4)
  have havs := align8_sub_le cap
  dsimp only [dynEndTop]
  omega

public theorem dyn_alloc_step (Γ : T.Env)
    (hAlloc : ∀ xs m Q X, arAallocSpec xs m Q X → Γ "ar_aalloc" [i64, i64] [i64] xs m Q X)
    {cx nbytes : BitVec 64} {s : ArCtxState} {w : BitVec 64} {baseTop wlen : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Tup Val [i64] → Mem 64 → Prop} {X : XPost}
    (hm : (arCtxMem cx s ⋆ (region (w + BitVec.ofNat 64 baseTop) (s.top.toNat - baseTop) ⋆
      (region (w + s.top) (wlen - s.top.toNat) ⋆ R))) m)
    (hwpos : 0 < w.toNat) (hfit : w.toNat + wlen < 2 ^ 64)
    (hw_eq : s.w = w) (hwl_eq : s.wlen.toNat = wlen)
    (hbase : baseTop ≤ s.top.toNat) (htop : s.top.toNat ≤ wlen)
    (hk : ∀ (ret newTop : BitVec 64) (m' : Mem 64),
      baseTop ≤ newTop.toNat → newTop.toNat ≤ wlen →
      ((ret = 0#64 ∧ newTop = s.top) ∨
       (ret ≠ 0#64 ∧ ret = w + BitVec.ofNat 64 (align8 s.top.toNat) ∧
        newTop.toNat = align8 s.top.toNat + nbytes.toNat)) →
      (arCtxMem cx { s with top := newTop } ⋆
        (region (w + BitVec.ofNat 64 baseTop) (newTop.toNat - baseTop) ⋆
        (region (w + newTop) (wlen - newTop.toNat) ⋆ R))) m' →
      Q (ret, ()) m') :
    Γ "ar_aalloc" [i64, i64] [i64] (cx, nbytes, ()) m Q X := by
  cases hw_eq
  rw [← hwl_eq] at hm htop hfit
  exact ar_aalloc_seq_step Γ hAlloc hwpos hfit hbase htop hm fun ret newTop m' hb ht hdisj hm' =>
    hk ret newTop m' hb (by rw [hwl_eq] at ht; exact ht) hdisj (by simpa only [hwl_eq] using hm')

public theorem dyn_fail_wrap {cx : BitVec 64} {s0 s' : ArCtxState} {baseTop : Nat}
    {R : Mem 64 → Prop} {m' : Mem 64}
    (hfit : s0.w.toNat + s0.wlen.toNat < 2 ^ 64)
    (hbase : baseTop ≤ s'.top.toNat) (htop : s'.top.toNat ≤ s0.wlen.toNat)
    (hm : (arCtxMem cx s' ⋆ region (s0.w + BitVec.ofNat 64 baseTop) (s'.top.toNat - baseTop) ⋆
      region (s0.w + s'.top) (s0.wlen.toNat - s'.top.toNat) ⋆ R) m') :
    (arCtxMem cx s' ⋆
      region (s0.w + BitVec.ofNat 64 baseTop) (s0.wlen.toNat - baseTop) ⋆ R) m' := by
  have hrm : (region (s0.w + BitVec.ofNat 64 baseTop) (s'.top.toNat - baseTop) ⋆
      region (s0.w + s'.top) (s0.wlen.toNat - s'.top.toNat)) =
      region (s0.w + BitVec.ofNat 64 baseTop) (s0.wlen.toNat - baseTop) := by
    rw [← addr_add_toNat s0.w s'.top]
    exact region_merge_offset s0.w hbase htop hfit
  have hm1 : (arCtxMem cx s' ⋆
      (region (s0.w + BitVec.ofNat 64 baseTop) (s'.top.toNat - baseTop) ⋆
       region (s0.w + s'.top) (s0.wlen.toNat - s'.top.toNat)) ⋆ R) m' :=
    sep_cast hm (by ac_rfl)
  rw [hrm] at hm1; exact hm1

public theorem dyn_store_tm0 (v : BitVec 64) {cx : BitVec 64} {s : ArCtxState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 344) ∧
      (arCtxMem cx { s with tm := s.tm.set 0 v } ⋆ R) (storeMem m i64 (cx + 344) v) := by
  simpa using store_tm_off (k := 0#64) rfl (by decide) v hm

public theorem dyn_store_ts0 (v : BitVec 64) {cx : BitVec 64} {s : ArCtxState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 360) ∧
      (arCtxMem cx { s with ts := s.ts.set 0 v } ⋆ R) (storeMem m i64 (cx + 360) v) := by
  simpa using store_ts_off (k := 0#64) rfl (by decide) v hm

public theorem dyn_store_tl0 (v : BitVec 64) {cx : BitVec 64} {s : ArCtxState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 376) ∧
      (arCtxMem cx { s with tl := s.tl.set 0 v } ⋆ R) (storeMem m i64 (cx + 376) v) := by
  simpa using store_tl_off (k := 0#64) rfl (by decide) v hm

public theorem dyn_store_th0 (v : BitVec 64) {cx : BitVec 64} {s : ArCtxState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 392) ∧
      (arCtxMem cx { s with th := s.th.set 0 v } ⋆ R) (storeMem m i64 (cx + 392) v) := by
  simpa using store_th_off (k := 0#64) rfl (by decide) v hm

public theorem dyn_store_pool0 (v : BitVec 64) {cx : BitVec 64} {s : ArCtxState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 408) ∧
      (arCtxMem cx { s with pool := s.pool.set 0 v } ⋆ R) (storeMem m i64 (cx + 408) v) := by
  simpa using store_pool_off (k := 0#64) rfl (by decide) v hm

public theorem dyn_store_tm1 (v : BitVec 64) {cx : BitVec 64} {s : ArCtxState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 352) ∧
      (arCtxMem cx { s with tm := s.tm.set 1 v } ⋆ R) (storeMem m i64 (cx + 352) v) := by
  have h := store_tm_off (k := 8#64) rfl (by decide) v hm
  rw [show (cx + 344 : BitVec 64) + 8#64 = cx + 352 by rw [BitVec.add_assoc]; rfl] at h
  exact h

public theorem dyn_store_ts1 (v : BitVec 64) {cx : BitVec 64} {s : ArCtxState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 368) ∧
      (arCtxMem cx { s with ts := s.ts.set 1 v } ⋆ R) (storeMem m i64 (cx + 368) v) := by
  have h := store_ts_off (k := 8#64) rfl (by decide) v hm
  rw [show (cx + 360 : BitVec 64) + 8#64 = cx + 368 by rw [BitVec.add_assoc]; rfl] at h
  exact h

public theorem dyn_store_tl1 (v : BitVec 64) {cx : BitVec 64} {s : ArCtxState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 384) ∧
      (arCtxMem cx { s with tl := s.tl.set 1 v } ⋆ R) (storeMem m i64 (cx + 384) v) := by
  have h := store_tl_off (k := 8#64) rfl (by decide) v hm
  rw [show (cx + 376 : BitVec 64) + 8#64 = cx + 384 by rw [BitVec.add_assoc]; rfl] at h
  exact h

public theorem dyn_store_th1 (v : BitVec 64) {cx : BitVec 64} {s : ArCtxState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 400) ∧
      (arCtxMem cx { s with th := s.th.set 1 v } ⋆ R) (storeMem m i64 (cx + 400) v) := by
  have h := store_th_off (k := 8#64) rfl (by decide) v hm
  rw [show (cx + 392 : BitVec 64) + 8#64 = cx + 400 by rw [BitVec.add_assoc]; rfl] at h
  exact h

public theorem dyn_store_pool1 (v : BitVec 64) {cx : BitVec 64} {s : ArCtxState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (arCtxMem cx s ⋆ R) m) :
    storeOk m i64 (cx + 416) ∧
      (arCtxMem cx { s with pool := s.pool.set 1 v } ⋆ R) (storeMem m i64 (cx + 416) v) := by
  have h := store_pool_off (k := 8#64) rfl (by decide) v hm
  rw [show (cx + 408 : BitVec 64) + 8#64 = cx + 416 by rw [BitVec.add_assoc]; rfl] at h
  exact h

private theorem dyn_off64_sw {k : BitVec 64} (hk : k.toNat % 8 = 0) (hi : k.toNat / 8 < 2) :
    (BitVec.ofNat 32 (k.toNat / 8)).setWidth 64 * 8 = k ∧
    (BitVec.ofNat 32 (k.toNat / 8)).toNat = k.toNat / 8 := by
  have hk2 : k = 0#64 ∨ k = 8#64 := by
    by_cases h0 : k.toNat = 0
    · exact Or.inl (BitVec.eq_of_toNat_eq h0)
    · have hk8 : k.toNat = (8#64 : BitVec 64).toNat := by
        simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
      exact Or.inr (BitVec.eq_of_toNat_eq hk8)
  rcases hk2 with rfl | rfl <;> exact ⟨by decide, by decide⟩

@[c0_load] public theorem dyn_load_tm_off {cx k : BitVec 64} {s : ArCtxState} {R : Mem 64 → Prop}
    {m : Mem 64} (hk : k.toNat % 8 = 0) (hi : k.toNat / 8 < 2) (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 344 + k) =
      some (s.tm[k.toNat / 8]'(by have := (sep_pure_l.mp hm).1.tm; omega)) := by
  have ⟨he, hi0⟩ := dyn_off64_sw hk hi
  simpa only [he, hi0] using load_tm_u32 (i := BitVec.ofNat 32 (k.toNat / 8)) (by omega) hm

@[c0_load] public theorem dyn_load_ts_off {cx k : BitVec 64} {s : ArCtxState} {R : Mem 64 → Prop}
    {m : Mem 64} (hk : k.toNat % 8 = 0) (hi : k.toNat / 8 < 2) (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 360 + k) =
      some (s.ts[k.toNat / 8]'(by have := (sep_pure_l.mp hm).1.ts; omega)) := by
  have ⟨he, hi0⟩ := dyn_off64_sw hk hi
  simpa only [he, hi0] using load_ts_u32 (i := BitVec.ofNat 32 (k.toNat / 8)) (by omega) hm

@[c0_load] public theorem dyn_load_tl_off {cx k : BitVec 64} {s : ArCtxState} {R : Mem 64 → Prop}
    {m : Mem 64} (hk : k.toNat % 8 = 0) (hi : k.toNat / 8 < 2) (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 376 + k) =
      some (s.tl[k.toNat / 8]'(by have := (sep_pure_l.mp hm).1.tl; omega)) := by
  have ⟨he, hi0⟩ := dyn_off64_sw hk hi
  simpa only [he, hi0] using load_tl_u32 (i := BitVec.ofNat 32 (k.toNat / 8)) (by omega) hm

@[c0_load] public theorem dyn_load_th_off {cx k : BitVec 64} {s : ArCtxState} {R : Mem 64 → Prop}
    {m : Mem 64} (hk : k.toNat % 8 = 0) (hi : k.toNat / 8 < 2) (hm : (arCtxMem cx s ⋆ R) m) :
    loadVal m i64 (cx + 392 + k) =
      some (s.th[k.toNat / 8]'(by have := (sep_pure_l.mp hm).1.th; omega)) := by
  have ⟨he, hi0⟩ := dyn_off64_sw hk hi
  simpa only [he, hi0] using load_th_u32 (i := BitVec.ofNat 32 (k.toNat / 8)) (by omega) hm

@[c0_load] public theorem dyn_load_pool_off {cx k : BitVec 64} {s : ArCtxState}
    {R : Mem 64 → Prop} {m : Mem 64} (hk : k.toNat % 8 = 0) (hi : k.toNat / 8 < 2)
    (hm : (arCtxMem cx s ⋆ R) m) : loadVal m i64 (cx + 408 + k) =
      some (s.pool[k.toNat / 8]'(by have := (sep_pure_l.mp hm).1.pool; omega)) := by
  have ⟨he, hi0⟩ := dyn_off64_sw hk hi
  simpa only [he, hi0] using load_pool_u32 (i := BitVec.ofNat 32 (k.toNat / 8)) (by omega) hm

public theorem dyn_step_init {s : ArCtxState} {w ret newTop nbytes : BitVec 64}
    {prevAlign delta nextAlign : Nat}
    (hdisj : (ret = 0#64 ∧ newTop = s.top) ∨
      (ret ≠ 0#64 ∧ ret = w + BitVec.ofNat 64 (align8 s.top.toNat) ∧
        newTop.toNat = align8 s.top.toNat + nbytes.toNat))
    (hs : align8 s.top.toNat = prevAlign) (hnbytes : nbytes.toNat = delta)
    (hsum : prevAlign + align8 delta = nextAlign) :
    let ok1 := true && (ret != 0#64)
    (ok1 = true → ret ≠ 0#64 ∧ ret = w + BitVec.ofNat 64 prevAlign ∧
      newTop.toNat = prevAlign + delta ∧ align8 newTop.toNat = nextAlign) ∧
    (ok1 = false → true = false ∨ ret = 0#64) := by
  intro ok1; constructor
  · intro h1
    have hne : ret ≠ 0#64 := by cases hret : (ret != 0#64) <;> simp_all [ok1]
    have hprev : prevAlign % 8 = 0 := by rw [← hs]; exact align8_mod _
    rcases hdisj with ⟨rfl, _⟩ | ⟨_, hr, hn⟩
    · exact absurd rfl hne
    · rw [hs] at hr hn
      refine ⟨hne, hr, by rw [hn, hnbytes], ?_⟩
      rw [hn, hnbytes, align8_add_of_mod hprev, hsum]
  · intro h0; cases hret : (ret != 0#64) <;> simp_all [ok1]

public theorem dyn_step_chain {s : ArCtxState} {w r0 w0 nt0 ret newTop nbytes : BitVec 64}
    {a0 d0 prevAlign delta nextAlign : Nat} {ok0 : Bool} {Pfalse : Prop}
    (hdisj : (ret = 0#64 ∧ newTop = s.top) ∨
      (ret ≠ 0#64 ∧ ret = w + BitVec.ofNat 64 (align8 s.top.toNat) ∧
        newTop.toNat = align8 s.top.toNat + nbytes.toNat))
    (hok0 : (ok0 = true → r0 ≠ 0#64 ∧ r0 = w0 + BitVec.ofNat 64 a0 ∧
        nt0.toNat = d0 ∧ align8 s.top.toNat = prevAlign) ∧ (ok0 = false → Pfalse))
    (hnbytes : nbytes.toNat = delta) (hsum : prevAlign + align8 delta = nextAlign) :
    let ok1 := ok0 && (ret != 0#64)
    (ok1 = true → ret ≠ 0#64 ∧ ret = w + BitVec.ofNat 64 prevAlign ∧
      newTop.toNat = prevAlign + delta ∧ align8 newTop.toNat = nextAlign) ∧
    (ok1 = false → ok0 = false ∨ ret = 0#64) := by
  intro ok1; constructor
  · intro h1
    have h0 : ok0 = true := by cases ok0 <;> simp_all [ok1]
    have hne : ret ≠ 0#64 := by cases hret : (ret != 0#64) <;> simp_all [ok1]
    have hs := (hok0.1 h0).2.2.2
    have hprev : prevAlign % 8 = 0 := by rw [← hs]; exact align8_mod _
    rcases hdisj with ⟨rfl, _⟩ | ⟨_, hr, hn⟩
    · exact absurd rfl hne
    · rw [hs] at hr hn
      refine ⟨hne, hr, by rw [hn, hnbytes], ?_⟩
      rw [hn, hnbytes, align8_add_of_mod hprev, hsum]
  · intro h0; cases ok0 <;> simp_all [ok1]

private theorem dyn_ptr_ne_zero {w : BitVec 64} {off wlen : Nat}
    (hwpos : 0 < w.toNat) (hfit : w.toNat + wlen < 2 ^ 64) (hof : off ≤ wlen) :
    w + BitVec.ofNat 64 off ≠ 0#64 := by
  intro heq
  have h1 := congrArg BitVec.toNat heq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : off < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : w.toNat + off < 2 ^ 64)] at h1
  simp only [BitVec.toNat_zero] at h1; omega

public theorem dyn_ctx_bind {cx : BitVec 64} {s s' : ArCtxState} {R : Mem 64 → Prop}
    {m : Mem 64} (hs : s' = s) (hm : (arCtxMem cx s ⋆ R) m) :
    (arCtxMem cx s' ⋆ R) m := hs ▸ hm

private theorem getD_set2_0 {l : List (BitVec 64)} {a b : BitVec 64} (h : l.length = 2) :
    ((l.set 0 a).set 1 b).getD 0 0#64 = a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by decide),
    List.getElem?_set_self (by omega)]
  rfl

private theorem getD_set2_1 {l : List (BitVec 64)} {a b : BitVec 64} (h : l.length = 2) :
    ((l.set 0 a).set 1 b).getD 1 0#64 = b := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self (by simp [h])]; rfl

private theorem dyn_segs_sum (a4 a8 ap avo avs : Nat) :
    a4 + (a8 + (a8 + (ap + (a4 + (a8 + (a8 + (a8 + (a4 + (a8 + (a8 + (a8 + (ap + (ap +
      (a4 + (a8 + (a8 + (a8 + (a4 + (a4 + (a4 + (avo + (ap + (avs + (a4 + (a8 + (a8 +
      (a4 + (a8 + (a8 + ap))))))))))))))))))))))))))))) =
      9 * a4 + 15 * a8 + 5 * ap + avo + avs := by omega

private theorem dyn_collapse_ord {s : ArCtxState} {top0 cap : Nat}
    {rsM rsPool tm0 tm1 pool0 pool1 qm ixA ixB bx vqOff vq rm rm2 rpool : List (BitVec 32)}
    {rsL rsH ts0 tl0 th0 ts1 tl1 th1 qs ql qh rl rh rl2 rh2 : List (BitVec 64)}
    {vqSkip : List (BitVec 8)} {pA pB : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (htop : s.top.toNat = dynEndTop top0 cap) (_hle : align8 top0 ≤ s.top.toNat)
    (hfit : s.top.toNat ≤ 2 ^ 64)
    (hrsm : s.rs_m = s.w + BitVec.ofNat 64 (align8 top0))
    (hrsl : s.rs_l = s.rs_m + BitVec.ofNat 64 (align8 (4 * cap)))
    (hrsh : s.rs_h = s.rs_l + BitVec.ofNat 64 (8 * cap))
    (hrsp : s.rs_pool = s.rs_h + BitVec.ofNat 64 (8 * cap))
    (htm0 : s.tm.getD 0 0#64 = s.rs_pool + BitVec.ofNat 64 (4 * (12 * cap)))
    (hts0 : s.ts.getD 0 0#64 = s.tm.getD 0 0#64 + BitVec.ofNat 64 (align8 (4 * cap)))
    (htl0 : s.tl.getD 0 0#64 = s.ts.getD 0 0#64 + BitVec.ofNat 64 (8 * cap))
    (hth0 : s.th.getD 0 0#64 = s.tl.getD 0 0#64 + BitVec.ofNat 64 (8 * cap))
    (htm1 : s.tm.getD 1 0#64 = s.th.getD 0 0#64 + BitVec.ofNat 64 (8 * cap))
    (hts1 : s.ts.getD 1 0#64 = s.tm.getD 1 0#64 + BitVec.ofNat 64 (align8 (4 * cap)))
    (htl1 : s.tl.getD 1 0#64 = s.ts.getD 1 0#64 + BitVec.ofNat 64 (8 * cap))
    (hth1 : s.th.getD 1 0#64 = s.tl.getD 1 0#64 + BitVec.ofNat 64 (8 * cap))
    (hp0 : s.pool.getD 0 0#64 = s.th.getD 1 0#64 + BitVec.ofNat 64 (8 * cap))
    (hp1 : s.pool.getD 1 0#64 = s.pool.getD 0 0#64 + BitVec.ofNat 64 (4 * (12 * cap)))
    (hqm : s.qm = s.pool.getD 1 0#64 + BitVec.ofNat 64 (4 * (12 * cap)))
    (hqs : s.qs = s.qm + BitVec.ofNat 64 (align8 (4 * cap)))
    (hql : s.ql = s.qs + BitVec.ofNat 64 (8 * cap))
    (hqh : s.qh = s.ql + BitVec.ofNat 64 (8 * cap))
    (hpA : pA = s.qh + BitVec.ofNat 64 (8 * cap))
    (hpB : pB = pA + BitVec.ofNat 64 (align8 (4 * cap)))
    (hbx : s.bx = pB + BitVec.ofNat 64 (align8 (4 * cap)))
    (hvqo : s.vq_off = s.bx + BitVec.ofNat 64 (align8 (4 * cap)))
    (hvq : s.vq = s.vq_off + BitVec.ofNat 64 (align8 (4 * (cap + 1))))
    (hvqs : s.vq_skip = s.vq + BitVec.ofNat 64 (4 * (12 * cap)))
    (hrm : s.rm = s.vq_skip + BitVec.ofNat 64 (align8 cap))
    (hrl : s.rl = s.rm + BitVec.ofNat 64 (align8 (4 * cap)))
    (hrh : s.rh = s.rl + BitVec.ofNat 64 (8 * cap))
    (hrm2 : s.rm2 = s.rh + BitVec.ofNat 64 (8 * cap))
    (hrl2 : s.rl2 = s.rm2 + BitVec.ofNat 64 (align8 (4 * cap)))
    (hrh2 : s.rh2 = s.rl2 + BitVec.ofNat 64 (8 * cap))
    (hrp : s.rpool = s.rh2 + BitVec.ofNat 64 (8 * cap))
    (l1 : rsM.length = cap) (l2 : rsL.length = cap) (l3 : rsH.length = cap)
    (l4 : rsPool.length = 12 * cap) (l5 : tm0.length = cap) (l6 : tm1.length = cap)
    (l7 : ts0.length = cap) (l8 : tl0.length = cap) (l9 : th0.length = cap)
    (l10 : ts1.length = cap) (l11 : tl1.length = cap) (l12 : th1.length = cap)
    (l13 : pool0.length = 12 * cap) (l14 : pool1.length = 12 * cap)
    (l15 : qm.length = cap) (l16 : qs.length = cap) (l17 : ql.length = cap) (l18 : qh.length = cap)
    (l19 : ixA.length = cap) (l20 : ixB.length = cap) (l21 : bx.length = cap)
    (l22 : vqOff.length = cap + 1) (l23 : vq.length = 12 * cap) (l24 : vqSkip.length = cap)
    (l25 : rm.length = cap) (l26 : rl.length = cap) (l27 : rh.length = cap)
    (l28 : rm2.length = cap) (l29 : rl2.length = cap) (l30 : rh2.length = cap)
    (l31 : rpool.length = 12 * cap)
    (hm : (arrayPad i32 s.rs_m rsM ⋆ array64 s.rs_l rsL ⋆ array64 s.rs_h rsH ⋆
      arrayPad i32 s.rs_pool rsPool ⋆
      tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
      arrayPad i32 s.qm qm ⋆ array64 s.qs qs ⋆ array64 s.ql ql ⋆ array64 s.qh qh ⋆
      arrayPad i32 pA ixA ⋆ arrayPad i32 pB ixB ⋆ arrayPad i32 s.bx bx ⋆
      arrayPad i32 s.vq_off vqOff ⋆ arrayPad i32 s.vq vq ⋆ arrayPad i8 s.vq_skip vqSkip ⋆
      rMem s rm rl rh rm2 rl2 rh2 rpool ⋆ R) m) :
    (region (s.w + BitVec.ofNat 64 (align8 top0)) (s.top.toNat - align8 top0) ⋆ R) m := by
  have h4c : ∀ {xs : List (BitVec 32)}, xs.length = cap → Ty.bytes i32 * xs.length = 4 * cap :=
    fun h => by simp [Ty.bytes, Ty.size, h]
  have h4p : ∀ {xs : List (BitVec 32)}, xs.length = 12 * cap →
      Ty.bytes i32 * xs.length = 4 * (12 * cap) :=
    fun h => by simp [Ty.bytes, Ty.size, h]
  have h4vo : Ty.bytes i32 * vqOff.length = 4 * (cap + 1) := by simp [Ty.bytes, Ty.size, l22]
  have h1vs : Ty.bytes i8 * vqSkip.length = cap := by simp [Ty.bytes, Ty.size, l24]
  let segs : List SlabSeg :=
    [SlabSeg.ofArrayAlign8 i32 rsM (4 * cap) (h4c l1),
     SlabSeg.ofArray64 rsL cap l2,
     SlabSeg.ofArray64 rsH cap l3,
     SlabSeg.ofArrayAlign8 i32 rsPool (4 * (12 * cap)) (h4p l4),
     SlabSeg.ofArrayAlign8 i32 tm0 (4 * cap) (h4c l5),
     SlabSeg.ofArray64 ts0 cap l7, SlabSeg.ofArray64 tl0 cap l8, SlabSeg.ofArray64 th0 cap l9,
     SlabSeg.ofArrayAlign8 i32 tm1 (4 * cap) (h4c l6),
     SlabSeg.ofArray64 ts1 cap l10, SlabSeg.ofArray64 tl1 cap l11, SlabSeg.ofArray64 th1 cap l12,
     SlabSeg.ofArrayAlign8 i32 pool0 (4 * (12 * cap)) (h4p l13),
     SlabSeg.ofArrayAlign8 i32 pool1 (4 * (12 * cap)) (h4p l14),
     SlabSeg.ofArrayAlign8 i32 qm (4 * cap) (h4c l15),
     SlabSeg.ofArray64 qs cap l16, SlabSeg.ofArray64 ql cap l17, SlabSeg.ofArray64 qh cap l18,
     SlabSeg.ofArrayAlign8 i32 ixA (4 * cap) (h4c l19),
     SlabSeg.ofArrayAlign8 i32 ixB (4 * cap) (h4c l20),
     SlabSeg.ofArrayAlign8 i32 bx (4 * cap) (h4c l21),
     SlabSeg.ofArrayAlign8 i32 vqOff (4 * (cap + 1)) h4vo,
     SlabSeg.ofArrayAlign8 i32 vq (4 * (12 * cap)) (h4p l23),
     SlabSeg.ofArrayAlign8 i8 vqSkip cap h1vs,
     SlabSeg.ofArrayAlign8 i32 rm (4 * cap) (h4c l25),
     SlabSeg.ofArray64 rl cap l26, SlabSeg.ofArray64 rh cap l27,
     SlabSeg.ofArrayAlign8 i32 rm2 (4 * cap) (h4c l28),
     SlabSeg.ofArray64 rl2 cap l29, SlabSeg.ofArray64 rh2 cap l30,
     SlabSeg.ofArrayAlign8 i32 rpool (4 * (12 * cap)) (h4p l31)]
  have hap : align8 (4 * (12 * cap)) = 4 * (12 * cap) := by
    rw [show 4 * (12 * cap) = 8 * (6 * cap) from by
      rw [← Nat.mul_assoc, show (4 * 12 : Nat) = 8 * 6 from rfl, Nat.mul_assoc]]
    exact align8_mul8 (6 * cap)
  have hvo : align8 (4 * (cap + 1)) = align8 (4 * cap + 4) := by rw [Nat.mul_add]
  have htot : SlabChain.totalBytes segs = s.top.toNat - align8 top0 := by
    have hde : dynEndTop top0 cap = align8 top0 +
        (9 * align8 (4 * cap) + 15 * (8 * cap) + 5 * (4 * (12 * cap)) +
         align8 (4 * cap + 4) + align8 cap) := by
      simp only [dynEndTop, Nat.add_assoc]
    rw [htop, hde, Nat.add_sub_cancel_left]
    simp only [segs, SlabChain.totalBytes, SlabSeg.ofArrayAlign8, SlabSeg.ofArray,
      SlabSeg.ofArray64, hap, hvo, Nat.add_zero]
    exact dyn_segs_sum _ _ _ _ _
  refine SlabChain.to_region_frame htot (Nat.le_trans (Nat.sub_le _ _) hfit) ?_
  have hm' := hm
  have hb32 : i32.bytes = 4 := rfl
  have hb8 : i8.bytes = 1 := rfl
  simp only [tMem, rMem, arrayPad, SlabSeg.ofArrayAlign8, SlabSeg.ofArray, hb32, hb8,
    l1, l4, l5, l6, l13, l14, l15, l19, l20, l21, l22, l23, l24, l25, l28, l31,
    Nat.one_mul, hap, Nat.sub_self, region_zero, sep_emp, sep_assoc] at hm'
  simp only [segs, SlabChain.eval, SlabSeg.ofArrayAlign8, SlabSeg.ofArray, SlabSeg.ofArray64,
    hap, Nat.sub_self, region_zero, sep_emp, sep_assoc]
  rw [← hrsm, ← hrsl, ← hrsh, ← hrsp, ← htm0, ← hts0, ← htl0, ← hth0, ← htm1, ← hts1,
    ← htl1, ← hth1, ← hp0, ← hp1, ← hqm, ← hqs, ← hql, ← hqh, ← hpA, ← hpB, ← hbx,
    ← hvqo, ← hvq, ← hvqs, ← hrm, ← hrl, ← hrh, ← hrm2, ← hrl2, ← hrh2, ← hrp]
  exact hm'

/-- Preserve `DynGeom` across `ar_check_main` field updates (including `ix`/`ix2` swaps). -/
public theorem DynGeom.preserve {s s' : ArCtxState} {top0 cap : Nat} (hg : DynGeom s top0 cap)
    (htop : s'.top = s.top) (hw : s'.w = s.w)
    (hrsm : s'.rs_m = s.rs_m) (hrsl : s'.rs_l = s.rs_l) (hrsh : s'.rs_h = s.rs_h)
    (hrsp : s'.rs_pool = s.rs_pool) (htm : s'.tm = s.tm) (hts : s'.ts = s.ts)
    (htl : s'.tl = s.tl) (hth : s'.th = s.th) (hpool : s'.pool = s.pool)
    (hqm : s'.qm = s.qm) (hqs : s'.qs = s.qs) (hql : s'.ql = s.ql) (hqh : s'.qh = s.qh)
    (hix : (s'.ix = s.ix ∧ s'.ix2 = s.ix2) ∨ (s'.ix = s.ix2 ∧ s'.ix2 = s.ix))
    (hbx : s'.bx = s.bx) (hvqo : s'.vq_off = s.vq_off) (hvq : s'.vq = s.vq)
    (hvqs : s'.vq_skip = s.vq_skip) (hrm : s'.rm = s.rm) (hrl : s'.rl = s.rl) (hrh : s'.rh = s.rh)
    (hrm2 : s'.rm2 = s.rm2) (hrl2 : s'.rl2 = s.rl2) (hrh2 : s'.rh2 = s.rh2)
    (hrp : s'.rpool = s.rpool) : DynGeom s' top0 cap :=
  { top_eq := htop ▸ hg.top_eq, rs_m_eq := hrsm ▸ hw ▸ hg.rs_m_eq,
    rs_l_eq := hrsl ▸ hrsm ▸ hg.rs_l_eq, rs_h_eq := hrsh ▸ hrsl ▸ hg.rs_h_eq,
    rs_pool_eq := hrsp ▸ hrsh ▸ hg.rs_pool_eq, tm0_eq := htm ▸ hrsp ▸ hg.tm0_eq,
    ts0_eq := hts ▸ htm ▸ hg.ts0_eq, tl0_eq := htl ▸ hts ▸ hg.tl0_eq,
    th0_eq := hth ▸ htl ▸ hg.th0_eq, tm1_eq := htm ▸ hth ▸ hg.tm1_eq,
    ts1_eq := hts ▸ htm ▸ hg.ts1_eq, tl1_eq := htl ▸ hts ▸ hg.tl1_eq,
    th1_eq := hth ▸ htl ▸ hg.th1_eq, pool0_eq := hpool ▸ hth ▸ hg.pool0_eq,
    pool1_eq := hpool ▸ hg.pool1_eq, qm_eq := hqm ▸ hpool ▸ hg.qm_eq,
    qs_eq := hqs ▸ hqm ▸ hg.qs_eq, ql_eq := hql ▸ hqs ▸ hg.ql_eq,
    qh_eq := hqh ▸ hql ▸ hg.qh_eq,
    ix_pair_eq := by
      rcases hix with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simpa only [h1, h2, hqh] using hg.ix_pair_eq
      · rw [h1, h2, hqh]; exact hg.ix_pair_eq.symm
    bx_eq := hbx ▸ hqh ▸ hg.bx_eq, vq_off_eq := hvqo ▸ hbx ▸ hg.vq_off_eq,
    vq_eq := hvq ▸ hvqo ▸ hg.vq_eq, vq_skip_eq := hvqs ▸ hvq ▸ hg.vq_skip_eq,
    rm_eq := hrm ▸ hvqs ▸ hg.rm_eq, rl_eq := hrl ▸ hrm ▸ hg.rl_eq,
    rh_eq := hrh ▸ hrl ▸ hg.rh_eq, rm2_eq := hrm2 ▸ hrh ▸ hg.rm2_eq,
    rl2_eq := hrl2 ▸ hrm2 ▸ hg.rl2_eq, rh2_eq := hrh2 ▸ hrl2 ▸ hg.rh2_eq,
    rpool_eq := hrp ▸ hrh2 ▸ hg.rpool_eq }

/-- Collapse `region baseTop..align8 top0 ⋆ rsMem ⋆ tMem ⋆ qMem ⋆ rMem ⋆ region top..wlen`
back to `region (s.w + baseTop) (s.wlen.toNat - baseTop)`. -/
public theorem dyn_collapse_avail {s : ArCtxState} {baseTop top0 cap : Nat}
    {rsM rsPool tm0 tm1 pool0 pool1 qm ix ix2 bx vqOff vq rm rm2 rpool : List (BitVec 32)}
    {rsL rsH ts0 tl0 th0 ts1 tl1 th1 qs ql qh rl rh rl2 rh2 : List (BitVec 64)}
    {vqSkip : List (BitVec 8)} {R : Mem 64 → Prop} {m : Mem 64}
    (hg : DynGeom s top0 cap) (hb : baseTop ≤ align8 top0) (hle : s.top.toNat ≤ s.wlen.toNat)
    (hfit : s.w.toNat + s.wlen.toNat < 2 ^ 64)
    (l1 : rsM.length = cap) (l2 : rsL.length = cap) (l3 : rsH.length = cap)
    (l4 : rsPool.length = 12 * cap) (l5 : tm0.length = cap) (l6 : tm1.length = cap)
    (l7 : ts0.length = cap) (l8 : tl0.length = cap) (l9 : th0.length = cap)
    (l10 : ts1.length = cap) (l11 : tl1.length = cap) (l12 : th1.length = cap)
    (l13 : pool0.length = 12 * cap) (l14 : pool1.length = 12 * cap)
    (l15 : qm.length = cap) (l16 : qs.length = cap) (l17 : ql.length = cap) (l18 : qh.length = cap)
    (l19 : ix.length = cap) (l20 : ix2.length = cap) (l21 : bx.length = cap)
    (l22 : vqOff.length = cap + 1) (l23 : vq.length = 12 * cap) (l24 : vqSkip.length = cap)
    (l25 : rm.length = cap) (l26 : rl.length = cap) (l27 : rh.length = cap)
    (l28 : rm2.length = cap) (l29 : rl2.length = cap) (l30 : rh2.length = cap)
    (l31 : rpool.length = 12 * cap)
    (hm : (region (s.w + BitVec.ofNat 64 baseTop) (align8 top0 - baseTop) ⋆
      rsMem s rsM rsL rsH rsPool ⋆ tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
      qMem s qm qs ql qh ix ix2 bx vqOff vq vqSkip ⋆
      rMem s rm rl rh rm2 rl2 rh2 rpool ⋆
      region (s.w + s.top) (s.wlen.toNat - s.top.toNat) ⋆ R) m) :
    (region (s.w + BitVec.ofNat 64 baseTop) (s.wlen.toNat - baseTop) ⋆ R) m := by
  have hal : align8 top0 ≤ s.top.toNat := by
    rw [hg.top_eq]; simp only [dynEndTop, Nat.add_assoc]; exact Nat.le_add_right _ _
  have htop64_le : s.top.toNat ≤ 2 ^ 64 := by
    have : s.top.toNat ≤ s.w.toNat + s.wlen.toNat := Nat.le_trans hle (Nat.le_add_left _ _)
    exact Nat.le_of_lt (Nat.lt_of_le_of_lt this hfit)
  have htop64 : s.w.toNat + s.top.toNat < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.add_le_add_left hle _) hfit
  have hhm : (rsMem s rsM rsL rsH rsPool ⋆ tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
      qMem s qm qs ql qh ix ix2 bx vqOff vq vqSkip ⋆ rMem s rm rl rh rm2 rl2 rh2 rpool ⋆
      (region (s.w + BitVec.ofNat 64 baseTop) (align8 top0 - baseTop) ⋆
       region (s.w + s.top) (s.wlen.toNat - s.top.toNat) ⋆ R)) m :=
    sep_cast hm (by ac_rfl)
  have hcol : (region (s.w + BitVec.ofNat 64 (align8 top0)) (s.top.toNat - align8 top0) ⋆
      (region (s.w + BitVec.ofNat 64 baseTop) (align8 top0 - baseTop) ⋆
       region (s.w + s.top) (s.wlen.toNat - s.top.toNat) ⋆ R)) m := by
    rcases hg.ix_pair_eq with ⟨h1, h2⟩ | ⟨h2, h1⟩
    · have hm0 : (arrayPad i32 s.rs_m rsM ⋆ array64 s.rs_l rsL ⋆ array64 s.rs_h rsH ⋆
          arrayPad i32 s.rs_pool rsPool ⋆
          tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
          arrayPad i32 s.qm qm ⋆ array64 s.qs qs ⋆ array64 s.ql ql ⋆ array64 s.qh qh ⋆
          arrayPad i32 s.ix ix ⋆ arrayPad i32 s.ix2 ix2 ⋆ arrayPad i32 s.bx bx ⋆
          arrayPad i32 s.vq_off vqOff ⋆ arrayPad i32 s.vq vq ⋆ arrayPad i8 s.vq_skip vqSkip ⋆
          rMem s rm rl rh rm2 rl2 rh2 rpool ⋆
          (region (s.w + BitVec.ofNat 64 baseTop) (align8 top0 - baseTop) ⋆
           region (s.w + s.top) (s.wlen.toNat - s.top.toNat) ⋆ R)) m := by
        simpa only [rsMem, qMem, sep_assoc] using hhm
      have hbx' : s.bx = s.ix2 + BitVec.ofNat 64 (align8 (4 * cap)) := by
        rw [hg.bx_eq, h2, h1, addr_add_ofNat, addr_add_ofNat, Nat.two_mul]
      exact dyn_collapse_ord hg.top_eq hal htop64_le hg.rs_m_eq hg.rs_l_eq hg.rs_h_eq
        hg.rs_pool_eq hg.tm0_eq hg.ts0_eq hg.tl0_eq hg.th0_eq hg.tm1_eq hg.ts1_eq hg.tl1_eq
        hg.th1_eq hg.pool0_eq hg.pool1_eq hg.qm_eq hg.qs_eq hg.ql_eq hg.qh_eq h1 h2 hbx'
        hg.vq_off_eq hg.vq_eq hg.vq_skip_eq hg.rm_eq hg.rl_eq hg.rh_eq hg.rm2_eq hg.rl2_eq
        hg.rh2_eq hg.rpool_eq l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18
        l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 hm0
    · have hm0 : (arrayPad i32 s.rs_m rsM ⋆ array64 s.rs_l rsL ⋆ array64 s.rs_h rsH ⋆
          arrayPad i32 s.rs_pool rsPool ⋆
          tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
          arrayPad i32 s.qm qm ⋆ array64 s.qs qs ⋆ array64 s.ql ql ⋆ array64 s.qh qh ⋆
          arrayPad i32 s.ix2 ix2 ⋆ arrayPad i32 s.ix ix ⋆ arrayPad i32 s.bx bx ⋆
          arrayPad i32 s.vq_off vqOff ⋆ arrayPad i32 s.vq vq ⋆ arrayPad i8 s.vq_skip vqSkip ⋆
          rMem s rm rl rh rm2 rl2 rh2 rpool ⋆
          (region (s.w + BitVec.ofNat 64 baseTop) (align8 top0 - baseTop) ⋆
           region (s.w + s.top) (s.wlen.toNat - s.top.toNat) ⋆ R)) m := by
        simp only [rsMem, qMem, sep_assoc] at hhm
        exact sep_cast hhm (by ac_rfl)
      have hbx' : s.bx = s.ix + BitVec.ofNat 64 (align8 (4 * cap)) := by
        rw [hg.bx_eq, h1, h2, addr_add_ofNat, addr_add_ofNat, Nat.two_mul]
      exact dyn_collapse_ord hg.top_eq hal htop64_le hg.rs_m_eq hg.rs_l_eq hg.rs_h_eq
        hg.rs_pool_eq hg.tm0_eq hg.ts0_eq hg.tl0_eq hg.th0_eq hg.tm1_eq hg.ts1_eq hg.tl1_eq
        hg.th1_eq hg.pool0_eq hg.pool1_eq hg.qm_eq hg.qs_eq hg.ql_eq hg.qh_eq h2 h1 hbx'
        hg.vq_off_eq hg.vq_eq hg.vq_skip_eq hg.rm_eq hg.rl_eq hg.rh_eq hg.rm2_eq hg.rl2_eq
        hg.rh2_eq hg.rpool_eq l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18
        l20 l19 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 hm0
  have hcol1 : ((region (s.w + BitVec.ofNat 64 baseTop) (align8 top0 - baseTop) ⋆
      region (s.w + BitVec.ofNat 64 (align8 top0)) (s.top.toNat - align8 top0)) ⋆
      region (s.w + s.top) (s.wlen.toNat - s.top.toNat) ⋆ R) m :=
    sep_cast hcol (by ac_rfl)
  rw [region_merge_offset s.w hb hal htop64] at hcol1
  have hcol2 : ((region (s.w + BitVec.ofNat 64 baseTop) (s.top.toNat - baseTop) ⋆
      region (s.w + s.top) (s.wlen.toNat - s.top.toNat)) ⋆ R) m :=
    sep_cast hcol1 (by ac_rfl)
  rw [← addr_add_toNat s.w s.top,
    region_merge_offset s.w (Nat.le_trans hb hal) hle hfit] at hcol2
  exact hcol2

public theorem dyn_finish_alloc {cx : BitVec 64} {s0 : ArCtxState} {baseTop : Nat}
    {cap p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
      p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 tp31 : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hlens : ArCtxLengthsOk s0) (_hfit : s0.w.toNat + s0.wlen.toNat < 2 ^ 64)
    (hcap16 : 16 ≤ cap.toNat) (hcapMax : cap.toNat ≤ 300000000)
    (hpw_nat : (cap * 12).toNat = 12 * cap.toNat)
    (hcap32_nat : (cap.setWidth 32).toNat = cap.toNat)
    (hp_rs :
      let t0 := align8 s0.top.toNat; let a4 := align8 (4 * cap.toNat); let a8 := 8 * cap.toNat
      p1 = s0.w + BitVec.ofNat 64 t0 ∧ p2 = s0.w + BitVec.ofNat 64 (t0 + a4) ∧
      p3 = s0.w + BitVec.ofNat 64 (t0 + a4 + a8) ∧
      p4 = s0.w + BitVec.ofNat 64 (t0 + a4 + 2 * a8))
    (hp_t :
      let t0 := align8 s0.top.toNat; let a4 := align8 (4 * cap.toNat)
      let a8 := 8 * cap.toNat; let ap := 4 * (12 * cap.toNat)
      p5 = s0.w + BitVec.ofNat 64 (t0 + a4 + 2 * a8 + ap) ∧
      p6 = s0.w + BitVec.ofNat 64 (t0 + 2 * a4 + 2 * a8 + ap) ∧
      p7 = s0.w + BitVec.ofNat 64 (t0 + 2 * a4 + 3 * a8 + ap) ∧
      p8 = s0.w + BitVec.ofNat 64 (t0 + 2 * a4 + 4 * a8 + ap) ∧
      p9 = s0.w + BitVec.ofNat 64 (t0 + 2 * a4 + 5 * a8 + ap) ∧
      p10 = s0.w + BitVec.ofNat 64 (t0 + 3 * a4 + 5 * a8 + ap) ∧
      p11 = s0.w + BitVec.ofNat 64 (t0 + 3 * a4 + 6 * a8 + ap) ∧
      p12 = s0.w + BitVec.ofNat 64 (t0 + 3 * a4 + 7 * a8 + ap) ∧
      p13 = s0.w + BitVec.ofNat 64 (t0 + 3 * a4 + 8 * a8 + ap) ∧
      p14 = s0.w + BitVec.ofNat 64 (t0 + 3 * a4 + 8 * a8 + 2 * ap))
    (hp_q :
      let t0 := align8 s0.top.toNat; let a4 := align8 (4 * cap.toNat)
      let a8 := 8 * cap.toNat; let ap := 4 * (12 * cap.toNat)
      let avo := align8 (4 * cap.toNat + 4)
      p15 = s0.w + BitVec.ofNat 64 (t0 + 3 * a4 + 8 * a8 + 3 * ap) ∧
      p16 = s0.w + BitVec.ofNat 64 (t0 + 4 * a4 + 8 * a8 + 3 * ap) ∧
      p17 = s0.w + BitVec.ofNat 64 (t0 + 4 * a4 + 9 * a8 + 3 * ap) ∧
      p18 = s0.w + BitVec.ofNat 64 (t0 + 4 * a4 + 10 * a8 + 3 * ap) ∧
      p19 = s0.w + BitVec.ofNat 64 (t0 + 4 * a4 + 11 * a8 + 3 * ap) ∧
      p20 = s0.w + BitVec.ofNat 64 (t0 + 5 * a4 + 11 * a8 + 3 * ap) ∧
      p21 = s0.w + BitVec.ofNat 64 (t0 + 6 * a4 + 11 * a8 + 3 * ap) ∧
      p22 = s0.w + BitVec.ofNat 64 (t0 + 7 * a4 + 11 * a8 + 3 * ap) ∧
      p23 = s0.w + BitVec.ofNat 64 (t0 + 7 * a4 + 11 * a8 + 3 * ap + avo) ∧
      p24 = s0.w + BitVec.ofNat 64 (t0 + 7 * a4 + 11 * a8 + 4 * ap + avo))
    (hp_r :
      let t0 := align8 s0.top.toNat; let a4 := align8 (4 * cap.toNat)
      let a8 := 8 * cap.toNat; let ap := 4 * (12 * cap.toNat)
      let av := align8 (4 * cap.toNat + 4) + align8 cap.toNat
      p25 = s0.w + BitVec.ofNat 64 (t0 + 7 * a4 + 11 * a8 + 4 * ap + av) ∧
      p26 = s0.w + BitVec.ofNat 64 (t0 + 8 * a4 + 11 * a8 + 4 * ap + av) ∧
      p27 = s0.w + BitVec.ofNat 64 (t0 + 8 * a4 + 12 * a8 + 4 * ap + av) ∧
      p28 = s0.w + BitVec.ofNat 64 (t0 + 8 * a4 + 13 * a8 + 4 * ap + av) ∧
      p29 = s0.w + BitVec.ofNat 64 (t0 + 9 * a4 + 13 * a8 + 4 * ap + av) ∧
      p30 = s0.w + BitVec.ofNat 64 (t0 + 9 * a4 + 14 * a8 + 4 * ap + av) ∧
      p31 = s0.w + BitVec.ofNat 64 (t0 + 9 * a4 + 15 * a8 + 4 * ap + av))
    (ht31_fin : tp31.toNat = dynEndTop s0.top.toNat cap.toNat)
    (ht0_le : baseTop ≤ align8 s0.top.toNat) (ht31 : tp31.toNat ≤ s0.wlen.toNat)
    (hm : (arCtxMem cx { s0 with
        top := tp31, rs_cap := cap.setWidth 32, rs_pcap := cap * 12,
        rs_m := p1, rs_l := p2, rs_h := p3, rs_pool := p4, tcap := cap.setWidth 32,
        tm := (s0.tm.set 0 p5).set 1 p9, ts := (s0.ts.set 0 p6).set 1 p10,
        tl := (s0.tl.set 0 p7).set 1 p11, th := (s0.th.set 0 p8).set 1 p12,
        pcap := cap * 12, pool := (s0.pool.set 0 p13).set 1 p14, qcap := cap.setWidth 32,
        qm := p15, qs := p16, ql := p17, qh := p18, ix := p19, ix2 := p20, bx := p21,
        vq_off := p22, vq := p23, vq_skip := p24, rcap := cap.setWidth 32, rpcap := cap * 12,
        rm := p25, rl := p26, rh := p27, rm2 := p28, rl2 := p29, rh2 := p30, rpool := p31 } ⋆
      region (s0.w + BitVec.ofNat 64 baseTop) (tp31.toNat - baseTop) ⋆
      region (s0.w + tp31) (s0.wlen.toNat - tp31.toNat) ⋆ R) m) :
    ∃ (s' : ArCtxState) (rsM : List (BitVec 32)) (rsL rsH : List (BitVec 64))
      (rsPool tm0 tm1 : List (BitVec 32)) (ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64))
      (pool0 pool1 qm : List (BitVec 32)) (qs ql qh : List (BitVec 64))
      (ix ix2 bx vqOff vq : List (BitVec 32)) (vqSkip : List (BitVec 8))
      (rm : List (BitVec 32)) (rl rh : List (BitVec 64))
      (rm2 : List (BitVec 32)) (rl2 rh2 : List (BitVec 64)) (rpool : List (BitVec 32)),
      let capn := s'.qcap.toNat; let pw := s'.pcap.toNat
      16 ≤ capn ∧ capn ≤ 300000000 ∧ pw = 12 * capn ∧
      s'.rs_cap = s'.qcap ∧ s'.tcap = s'.qcap ∧ s'.rcap = s'.qcap ∧
      s'.rs_pcap = s'.pcap ∧ s'.rpcap = s'.pcap ∧ s'.top.toNat ≤ s'.wlen.toNat ∧
      DynGeom s' s0.top.toNat capn ∧
      s' = { s0 with
        top := s'.top, rs_cap := s'.rs_cap, rs_pcap := s'.rs_pcap, tcap := s'.tcap,
        pcap := s'.pcap, qcap := s'.qcap, rcap := s'.rcap, rpcap := s'.rpcap, rs_m := s'.rs_m,
        rs_l := s'.rs_l, rs_h := s'.rs_h, rs_pool := s'.rs_pool, tm := s'.tm, ts := s'.ts,
        tl := s'.tl, th := s'.th, pool := s'.pool, qm := s'.qm, qs := s'.qs, ql := s'.ql,
        qh := s'.qh, ix := s'.ix, ix2 := s'.ix2, bx := s'.bx, vq_off := s'.vq_off,
        vq := s'.vq, vq_skip := s'.vq_skip, rm := s'.rm, rl := s'.rl, rh := s'.rh,
        rm2 := s'.rm2, rl2 := s'.rl2, rh2 := s'.rh2, rpool := s'.rpool } ∧
      rsM.length = capn ∧ rsL.length = capn ∧ rsH.length = capn ∧ rsPool.length = pw ∧
      tm0.length = capn ∧ tm1.length = capn ∧ ts0.length = capn ∧ tl0.length = capn ∧
      th0.length = capn ∧ ts1.length = capn ∧ tl1.length = capn ∧ th1.length = capn ∧
      pool0.length = pw ∧ pool1.length = pw ∧ qm.length = capn ∧ qs.length = capn ∧
      ql.length = capn ∧ qh.length = capn ∧ ix.length = capn ∧ ix2.length = capn ∧
      bx.length = capn ∧ vqOff.length = capn + 1 ∧ vq.length = pw ∧ vqSkip.length = capn ∧
      rm.length = capn ∧ rl.length = capn ∧ rh.length = capn ∧ rm2.length = capn ∧
      rl2.length = capn ∧ rh2.length = capn ∧ rpool.length = pw ∧
      (arCtxMem cx s' ⋆
        region (s0.w + BitVec.ofNat 64 baseTop) (align8 s0.top.toNat - baseTop) ⋆
        rsMem s' rsM rsL rsH rsPool ⋆ tMem s' tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
        qMem s' qm qs ql qh ix ix2 bx vqOff vq vqSkip ⋆ rMem s' rm rl rh rm2 rl2 rh2 rpool ⋆
        region (s'.w + s'.top) (s'.wlen.toNat - s'.top.toNat) ⋆ R) m := by
  let s32 : ArCtxState := { s0 with
    top := tp31, rs_cap := cap.setWidth 32, rs_pcap := cap * 12,
    rs_m := p1, rs_l := p2, rs_h := p3, rs_pool := p4, tcap := cap.setWidth 32,
    tm := (s0.tm.set 0 p5).set 1 p9, ts := (s0.ts.set 0 p6).set 1 p10,
    tl := (s0.tl.set 0 p7).set 1 p11, th := (s0.th.set 0 p8).set 1 p12,
    pcap := cap * 12, pool := (s0.pool.set 0 p13).set 1 p14, qcap := cap.setWidth 32,
    qm := p15, qs := p16, ql := p17, qh := p18, ix := p19, ix2 := p20, bx := p21,
    vq_off := p22, vq := p23, vq_skip := p24, rcap := cap.setWidth 32, rpcap := cap * 12,
    rm := p25, rl := p26, rh := p27, rm2 := p28, rl2 := p29, rh2 := p30, rpool := p31 }
  have htm0_v := getD_set2_0 (a := p5) (b := p9) hlens.tm
  have htm1_v := getD_set2_1 (a := p5) (b := p9) hlens.tm
  have hts0_v := getD_set2_0 (a := p6) (b := p10) hlens.ts
  have hts1_v := getD_set2_1 (a := p6) (b := p10) hlens.ts
  have htl0_v := getD_set2_0 (a := p7) (b := p11) hlens.tl
  have htl1_v := getD_set2_1 (a := p7) (b := p11) hlens.tl
  have hth0_v := getD_set2_0 (a := p8) (b := p12) hlens.th
  have hth1_v := getD_set2_1 (a := p8) (b := p12) hlens.th
  have hp0_v := getD_set2_0 (a := p13) (b := p14) hlens.pool
  have hp1_v := getD_set2_1 (a := p13) (b := p14) hlens.pool
  have hpw64 : ∀ {x : BitVec 64} {a b : Nat},
      x = s0.w + BitVec.ofNat 64 a → a = b → x = s0.w + BitVec.ofNat 64 b := fun h hab => hab ▸ h
  rcases hp_rs with ⟨hp1, hp2, hp3, hp4⟩
  rcases hp_t with ⟨hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14⟩
  rcases hp_q with ⟨hp15, hp16, hp17, hp18, hp19, hp20, hp21, hp22, hp23, hp24⟩
  rcases hp_r with ⟨hp25, hp26, hp27, hp28, hp29, hp30, hp31⟩
  obtain ⟨rsM, rsL, rsH, rsPool, tm0, tm1, ts0, tl0, th0, ts1, tl1, th1,
    pool0, pool1, qm, qs, ql, qh, ix, ix2, bx, vqOff, vq, vqSkip,
    rm, rl, rh, rm2, rl2, rh2, rpool, hrsM, hrsL, hrsH, hrsPool,
    htm0_l, htm1_l, hts0_l, htl0_l, hth0_l, hts1_l, htl1_l, hth1_l,
    hp0_l, hp1_l, hqm_l, hqs_l, hql_l, hqh_l, hix_l, hix2_l, hbx_l,
    hvqo_l, hvq_l, hvqs_l, hrm_l, hrl_l, hrh_l, hrm2_l, hrl2_l, hrh2_l, hrp_l, hm_pop⟩ :=
    dyn_pop_alloc (s0 := s0) (s := s32)
      (R := region (s0.w + tp31) (s0.wlen.toNat - tp31.toNat) ⋆ arCtxMem cx s32 ⋆ R) ht0_le
      (by change align8 s0.top.toNat ≤ tp31.toNat; rw [ht31_fin]; dsimp only [dynEndTop]; omega)
      (by change tp31.toNat ≤ 2 ^ 64; omega) hcap32_nat hpw_nat ht31_fin
      ⟨hp1, hp2, hp3, hp4⟩
      ⟨hpw64 (htm0_v.trans hp5) (by omega), hpw64 (hts0_v.trans hp6) (by omega),
       hpw64 (htl0_v.trans hp7) (by omega), hpw64 (hth0_v.trans hp8) (by omega),
       hpw64 (htm1_v.trans hp9) (by omega), hpw64 (hts1_v.trans hp10) (by omega),
       hpw64 (htl1_v.trans hp11) (by omega), hpw64 (hth1_v.trans hp12) (by omega),
       hpw64 (hp0_v.trans hp13) (by omega), hpw64 (hp1_v.trans hp14) (by omega)⟩
      ⟨hpw64 hp15 (by omega), hpw64 hp16 (by omega), hpw64 hp17 (by omega),
       hpw64 hp18 (by omega), hpw64 hp19 (by omega), hpw64 hp20 (by omega),
       hpw64 hp21 (by omega), hpw64 hp22 (by omega), hpw64 hp23 (by omega),
       hpw64 hp24 (by omega)⟩
      ⟨hpw64 hp25 (by omega), hpw64 hp26 (by omega), hpw64 hp27 (by omega),
       hpw64 hp28 (by omega), hpw64 hp29 (by omega), hpw64 hp30 (by omega),
       hpw64 hp31 (by omega)⟩
      (sep_cast hm (by ac_rfl))
  have hcap_v : s32.qcap.toNat = cap.toNat := hcap32_nat
  have hpw_v : s32.pcap.toNat = 12 * cap.toNat := hpw_nat
  have hp_off : ∀ {a b : BitVec 64} {n1 n2 d : Nat},
      a = s0.w + BitVec.ofNat 64 n1 → b = s0.w + BitVec.ofNat 64 n2 → n2 = n1 + d →
      b = a + BitVec.ofNat 64 d := by
    intro a b n1 n2 d ha hb hn; rw [hb, ha, addr_add_ofNat, hn]
  have hgeom : DynGeom s32 s0.top.toNat s32.qcap.toNat := by
    rw [hcap_v]
    refine
      { top_eq := ht31_fin, rs_m_eq := hp1,
        rs_l_eq := hp_off hp1 hp2 (by omega), rs_h_eq := hp_off hp2 hp3 (by omega),
        rs_pool_eq := hp_off hp3 hp4 (by omega),
        tm0_eq := htm0_v.trans (hp_off hp4 hp5 (by omega)),
        ts0_eq := hts0_v.trans (hp_off (htm0_v.trans hp5) hp6 (by omega)),
        tl0_eq := htl0_v.trans (hp_off (hts0_v.trans hp6) hp7 (by omega)),
        th0_eq := hth0_v.trans (hp_off (htl0_v.trans hp7) hp8 (by omega)),
        tm1_eq := htm1_v.trans (hp_off (hth0_v.trans hp8) hp9 (by omega)),
        ts1_eq := hts1_v.trans (hp_off (htm1_v.trans hp9) hp10 (by omega)),
        tl1_eq := htl1_v.trans (hp_off (hts1_v.trans hp10) hp11 (by omega)),
        th1_eq := hth1_v.trans (hp_off (htl1_v.trans hp11) hp12 (by omega)),
        pool0_eq := hp0_v.trans (hp_off (hth1_v.trans hp12) hp13 (by omega)),
        pool1_eq := hp1_v.trans (hp_off (hp0_v.trans hp13) hp14 (by omega)),
        qm_eq := hp_off (hp1_v.trans hp14) hp15 (by omega),
        qs_eq := hp_off hp15 hp16 (by omega), ql_eq := hp_off hp16 hp17 (by omega),
        qh_eq := hp_off hp17 hp18 (by omega),
        ix_pair_eq := Or.inl ⟨hp_off hp18 hp19 (by omega), hp_off hp19 hp20 (by omega)⟩,
        bx_eq := hp_off hp18 hp21 (by omega),
        vq_off_eq := hp_off hp21 hp22 (by omega),
        vq_eq := hp_off hp22 hp23 (by rw [Nat.mul_add]),
        vq_skip_eq := hp_off hp23 hp24 (by omega),
        rm_eq := hp_off hp24 hp25 (by omega), rl_eq := hp_off hp25 hp26 (by omega),
        rh_eq := hp_off hp26 hp27 (by omega), rm2_eq := hp_off hp27 hp28 (by omega),
        rl2_eq := hp_off hp28 hp29 (by omega), rh2_eq := hp_off hp29 hp30 (by omega),
        rpool_eq := hp_off hp30 hp31 (by omega) }
  exact ⟨s32, rsM, rsL, rsH, rsPool, tm0, tm1, ts0, tl0, th0, ts1, tl1, th1, pool0, pool1, qm,
    qs, ql, qh, ix, ix2, bx, vqOff, vq, vqSkip, rm, rl, rh, rm2, rl2, rh2, rpool,
    hcap_v.symm ▸ hcap16, hcap_v.symm ▸ hcapMax,
    by change s32.pcap.toNat = 12 * s32.qcap.toNat; rw [hpw_v, hcap_v],
    rfl, rfl, rfl, rfl, rfl, ht31, hgeom, rfl, hcap_v ▸ hrsM, hcap_v ▸ hrsL, hcap_v ▸ hrsH,
    hpw_v ▸ hrsPool, hcap_v ▸ htm0_l, hcap_v ▸ htm1_l, hcap_v ▸ hts0_l, hcap_v ▸ htl0_l,
    hcap_v ▸ hth0_l, hcap_v ▸ hts1_l, hcap_v ▸ htl1_l, hcap_v ▸ hth1_l, hpw_v ▸ hp0_l,
    hpw_v ▸ hp1_l, hcap_v ▸ hqm_l, hcap_v ▸ hqs_l, hcap_v ▸ hql_l, hcap_v ▸ hqh_l,
    hcap_v ▸ hix_l, hcap_v ▸ hix2_l, hcap_v ▸ hbx_l, hcap_v ▸ hvqo_l, hpw_v ▸ hvq_l,
    hcap_v ▸ hvqs_l, hcap_v ▸ hrm_l, hcap_v ▸ hrl_l, hcap_v ▸ hrh_l, hcap_v ▸ hrm2_l,
    hcap_v ▸ hrl2_l, hcap_v ▸ hrh2_l, hpw_v ▸ hrp_l, sep_cast hm_pop (by ac_rfl)⟩

end
