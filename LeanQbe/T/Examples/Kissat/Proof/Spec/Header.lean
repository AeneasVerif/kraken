/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Header
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.ControlComb
public import Kraken.Mem
public import Kraken.Separation

/-!
# Kissat M6 `FullM6Hdr` Extension Layout, Invariants, Framing & Contracts (`Proof.Spec.Header`)

1. `m6ExtAddr`, `m6ExtMem`, `M6HdrExtOk`, `M6HdrExtInitOk`, `FullM6HdrCfgOk`, `FullM6HdrMem`,
   `FullM6HdrInv`, `FullM6HdrInvW`, `FullM6HdrCoreInv`, and non-interference predicates.
2. Automatic separation-logic framing bridges (`fullM6HdrMem_iff`, `fullM6HdrMem_to_region`).
3. Scoped `M6HdrTactics` (`O(1)` `FullMem ⋆ (array64 ⋆ R)` accessors, zero `ecancel`).
4. `FullM6Hdr` function specifications (`m6HdrInitSpec`, `m6ExtEnsureInitSpec`, `fullM6MemInitSpec`,
   `m6HdrW2aSpec`, `m6HdrDrMutSpec`, `m6HdrDrAllowSpec`, etc.).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Spec

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src
open scoped FullArenaTactics
open Kraken.Bedrock2.Test

/-! ## 1. `FullM6HdrMem`, `FullM6HdrInv`, Non-Interference & Region Collapse -/

/-- Base address of the `2,304`-byte `M6HdrExt` prefix immediately preceding `FullHdr`. -/
@[expose] def m6ExtAddr (hdr : BitVec 64) : BitVec 64 :=
  hdr - 2304

/-- Spatial ownership of the `288`-word (`2,304`-byte) `M6HdrExt` prefix. -/
@[expose] def m6ExtMem (extAddr : BitVec 64) (ext : List (BitVec 64)) : Mem 64 → Prop :=
  array64 extAddr ext

/-- Well-formedness of the `M6HdrExt` `u64` word array (`length = 288`). -/
@[expose] def M6HdrExtOk (ext : List (BitVec 64)) : Prop :=
  ext.length = fullM6ExtWords

/-- Initialized `M6HdrExt` invariant: length `288` and word `0` holds `fullM6HdrMagic`. -/
@[expose] def M6HdrExtInitOk (ext : List (BitVec 64)) : Prop :=
  ext.length = fullM6ExtWords ∧ ext[0]? = some fullM6HdrMagic

/-- No-underflow geometry condition ensuring `c.hdr - 2304#64` does not wrap below `0`. -/
@[expose] def FullM6HdrCfgOk (c : FullCfg) : Prop :=
  fullM6ExtBytes ≤ c.hdr.toNat

/-- Combined spatial predicate extending frozen `FullMem c s` by disjoint `M6HdrExt` prefix. -/
@[expose] def FullM6HdrMem (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) : Mem 64 → Prop :=
  m6ExtMem (m6ExtAddr c.hdr) ext ⋆ FullMem c s

/-- Sparse-mode UNSAT-only invariant extended with `FullM6Hdr` geometry & `M6HdrExt` length. -/
@[expose]
def FullM6HdrInv (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) : Prop :=
  FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ FullSparseInv c F0 s

/-- Explicit-witness sparse-mode invariant extended with `FullM6Hdr` geometry & `M6HdrExt`. -/
def FullM6HdrInvW (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (ext : List (BitVec 64)) (s : FullState) : Prop :=
  FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ FullSparseInvW c F0 F_cur s

/-- Core CDCL invariant extended with `FullM6Hdr` geometry & `M6HdrExt` length. -/
def FullM6HdrCoreInv (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64))
    (s : FullState) : Prop :=
  FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ FullCoreInv c F0 s

/-- `BcpS15` / `VivBackbone` non-interference: base `h->delayed` and `h->delayed_len` untouched. -/
def M6HdrBaseDelayedPres (s s' : FullState) : Prop :=
  s'.scratch.delayed = s.scratch.delayed ∧ s'.scratch.delayed_len = s.scratch.delayed_len

/-- Decision-rate non-interference inside `M6HdrExt`: words `1..7` (`dr_*`) untouched. -/
def M6ExtW2bPres (ext ext' : List (BitVec 64)) : Prop :=
  ∀ k, 1 ≤ k → k < 8 → ext'[k]? = ext[k]?

/-- Tier/watermark non-interference inside `M6HdrExt`: word `0` and words `8..287` untouched. -/
def M6ExtW2aPres (ext ext' : List (BitVec 64)) : Prop :=
  ext'[0]? = ext[0]? ∧ ∀ k, 8 ≤ k → k < fullM6ExtWords → ext'[k]? = ext[k]?

/-- Combined probe-scratch and base `delayed*` preservation for `FullM6Hdr` helpers. -/
def M6HdrScratchPres (s s' : FullState) : Prop :=
  FullProbeScratchPres s s' ∧ M6HdrBaseDelayedPres s s'

/-! ### Public Structural Bridges (Opaque-Safe Downstream) -/

theorem m6ExtAddr_eq (hdr : BitVec 64) : m6ExtAddr hdr = hdr - 2304 := by rfl

theorem m6ExtAddr_eq_bv (hdr : BitVec 64) : m6ExtAddr hdr = hdr - 2304#64 := by
  unfold m6ExtAddr; rfl

theorem m6ExtAddr_add_bytes (hdr : BitVec 64) :
    m6ExtAddr hdr + BitVec.ofNat 64 fullM6ExtBytes = hdr := by
  unfold m6ExtAddr fullM6ExtBytes; bv_omega

theorem m6ExtAddr_of_add (base : BitVec 64) :
    m6ExtAddr (base + BitVec.ofNat 64 fullM6ExtBytes) = base := by
  unfold m6ExtAddr fullM6ExtBytes; bv_omega

theorem m6ExtAddr_of_add_imm (base : BitVec 64) :
    m6ExtAddr (base + 2304) = base := by
  unfold m6ExtAddr; bv_omega

theorem m6ExtAddr_toNat {hdr : BitVec 64} (h : fullM6ExtBytes ≤ hdr.toNat) :
    (m6ExtAddr hdr).toNat = hdr.toNat - fullM6ExtBytes := by
  unfold m6ExtAddr fullM6ExtBytes at *; bv_omega

theorem M6HdrExtInitOk.toOk {ext : List (BitVec 64)} (h : M6HdrExtInitOk ext) :
    M6HdrExtOk ext := h.1

theorem M6HdrExtInitOk.magic {ext : List (BitVec 64)} (h : M6HdrExtInitOk ext) :
    ext[0]? = some fullM6HdrMagic := h.2

theorem M6HdrExtInitOk.set_pos {ext : List (BitVec 64)} {idx : Nat} (v : BitVec 64)
    (h : M6HdrExtInitOk ext) (hpos : 0 < idx) : M6HdrExtInitOk (ext.set idx v) :=
  ⟨by rw [List.length_set]; exact h.1, by rw [List.getElem?_set_ne (by omega)]; exact h.2⟩

theorem M6HdrExtOk.len {ext : List (BitVec 64)} (h : M6HdrExtOk ext) :
    ext.length = 288 := h

theorem M6HdrExtOk.of_len {ext : List (BitVec 64)} (h : ext.length = 288) :
    M6HdrExtOk ext := h

theorem M6HdrCfgOk_of_le {c : FullCfg} (h : 2304 ≤ c.hdr.toNat) : FullM6HdrCfgOk c := h

theorem M6HdrCfgOk_le {c : FullCfg} (h : FullM6HdrCfgOk c) : 2304 ≤ c.hdr.toNat := h

theorem M6HdrBaseDelayedPres.refl (s : FullState) : M6HdrBaseDelayedPres s s := ⟨rfl, rfl⟩

theorem M6HdrBaseDelayedPres.trans {s1 s2 s3 : FullState}
    (h12 : M6HdrBaseDelayedPres s1 s2) (h23 : M6HdrBaseDelayedPres s2 s3) :
    M6HdrBaseDelayedPres s1 s3 :=
  ⟨h23.1.trans h12.1, h23.2.trans h12.2⟩

theorem M6ExtW2bPres.refl (ext : List (BitVec 64)) : M6ExtW2bPres ext ext := fun _ _ _ => rfl

theorem M6ExtW2bPres.trans {e1 e2 e3 : List (BitVec 64)}
    (h12 : M6ExtW2bPres e1 e2) (h23 : M6ExtW2bPres e2 e3) : M6ExtW2bPres e1 e3 :=
  fun k h1 h8 => (h23 k h1 h8).trans (h12 k h1 h8)

theorem M6ExtW2bPres.set_ge8 {ext : List (BitVec 64)} {idx : Nat} (v : BitVec 64)
    (hge : 8 ≤ idx) : M6ExtW2bPres ext (ext.set idx v) :=
  fun _ _ h8 => List.getElem?_set_ne (by omega)

theorem M6ExtW2aPres.refl (ext : List (BitVec 64)) : M6ExtW2aPres ext ext :=
  ⟨rfl, fun _ _ _ => rfl⟩

theorem M6ExtW2aPres.trans {e1 e2 e3 : List (BitVec 64)}
    (h12 : M6ExtW2aPres e1 e2) (h23 : M6ExtW2aPres e2 e3) : M6ExtW2aPres e1 e3 :=
  ⟨h23.1.trans h12.1, fun k h8 h288 => (h23.2 k h8 h288).trans (h12.2 k h8 h288)⟩

theorem M6ExtW2aPres.set_w2b {ext : List (BitVec 64)} {idx : Nat} (v : BitVec 64)
    (h1 : 1 ≤ idx) (h8 : idx < 8) : M6ExtW2aPres ext (ext.set idx v) :=
  ⟨List.getElem?_set_ne (by omega), fun _ hk _ => List.getElem?_set_ne (by omega)⟩

theorem M6HdrScratchPres.refl (s : FullState) : M6HdrScratchPres s s :=
  ⟨⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl⟩⟩

theorem M6HdrScratchPres.trans {s1 s2 s3 : FullState}
    (h12 : M6HdrScratchPres s1 s2) (h23 : M6HdrScratchPres s2 s3) :
    M6HdrScratchPres s1 s3 :=
  ⟨⟨⟨h23.1.1.1.trans h12.1.1.1, h23.1.1.2.trans h12.1.1.2⟩,
    h23.1.2.1.trans h12.1.2.1, h23.1.2.2.1.trans h12.1.2.2.1,
    h23.1.2.2.2.1.trans h12.1.2.2.2.1, h23.1.2.2.2.2.1.trans h12.1.2.2.2.2.1,
    h23.1.2.2.2.2.2.1.trans h12.1.2.2.2.2.2.1,
    h23.1.2.2.2.2.2.2.1.trans h12.1.2.2.2.2.2.2.1,
    h23.1.2.2.2.2.2.2.2.trans h12.1.2.2.2.2.2.2.2⟩,
   h12.2.trans h23.2⟩

theorem M6HdrScratchPres.of_tier {s : FullState} (t1 t2 : BitVec 64) :
    M6HdrScratchPres s { s with scratch := { s.scratch with tier1 := t1, tier2 := t2 } } :=
  ⟨⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl⟩⟩

theorem M6HdrScratchPres.of_ticks {s : FullState} (st : BitVec 64) :
    M6HdrScratchPres s { s with scratch := { s.scratch with search_ticks := st } } :=
  ⟨⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl⟩⟩

theorem M6HdrScratchPres.extPres {s s' : FullState} (h : M6HdrScratchPres s s') :
    FullExtScratchPres s s' := h.1.1

theorem M6HdrScratchPres.ws1 {s s' : FullState} (h : M6HdrScratchPres s s') :
    s'.scratch.work_stk1 = s.scratch.work_stk1 := h.1.2.1

theorem M6HdrScratchPres.ws2 {s s' : FullState} (h : M6HdrScratchPres s s') :
    s'.scratch.work_stk2 = s.scratch.work_stk2 := h.1.2.2.1

theorem M6HdrScratchPres.ant_sz {s s' : FullState} (h : M6HdrScratchPres s s') :
    s'.scratch.ant_sz = s.scratch.ant_sz := h.1.2.2.2.2.2.1

theorem M6HdrScratchPres.res_sz {s s' : FullState} (h : M6HdrScratchPres s s') :
    s'.scratch.res_sz = s.scratch.res_sz := h.1.2.2.2.2.2.2.1

theorem M6HdrScratchPres.delayed {s s' : FullState} (h : M6HdrScratchPres s s') :
    M6HdrBaseDelayedPres s s' := h.2

theorem M6HdrScratchPres.probePres {s s' : FullState} (h : M6HdrScratchPres s s') :
    FullProbeScratchPres s s' := h.1

theorem FullM6HdrInv.mk_inv {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} (hc : FullM6HdrCfgOk c) (he : M6HdrExtOk ext) (hs : FullSparseInv c F0 s) :
    FullM6HdrInv c F0 ext s := ⟨hc, he, hs⟩

theorem FullM6HdrInv.cfgOk {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} (h : FullM6HdrInv c F0 ext s) : FullM6HdrCfgOk c := h.1

theorem FullM6HdrInv.extOk {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} (h : FullM6HdrInv c F0 ext s) : M6HdrExtOk ext := h.2.1

theorem FullM6HdrInv.sparse {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} (h : FullM6HdrInv c F0 ext s) : FullSparseInv c F0 s := h.2.2

theorem FullM6HdrInvW.mk_inv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext : List (BitVec 64)} {s : FullState}
    (hc : FullM6HdrCfgOk c) (he : M6HdrExtOk ext) (hs : FullSparseInvW c F0 F_cur s) :
    FullM6HdrInvW c F0 F_cur ext s := ⟨hc, he, hs⟩

theorem FullM6HdrInvW.cfgOk {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext : List (BitVec 64)} {s : FullState} (h : FullM6HdrInvW c F0 F_cur ext s) :
    FullM6HdrCfgOk c := h.1

theorem FullM6HdrInvW.extOk {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext : List (BitVec 64)} {s : FullState} (h : FullM6HdrInvW c F0 F_cur ext s) :
    M6HdrExtOk ext := h.2.1

theorem FullM6HdrInvW.sparseW {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext : List (BitVec 64)} {s : FullState} (h : FullM6HdrInvW c F0 F_cur ext s) :
    FullSparseInvW c F0 F_cur s := h.2.2

theorem FullM6HdrInvW.toInv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext : List (BitVec 64)} {s : FullState} (h : FullM6HdrInvW c F0 F_cur ext s) :
    FullM6HdrInv c F0 ext s := ⟨h.1, h.2.1, h.2.2.toSparse⟩

theorem FullM6HdrCoreInv.mk_inv {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} (hc : FullM6HdrCfgOk c) (he : M6HdrExtOk ext) (hs : FullCoreInv c F0 s) :
    FullM6HdrCoreInv c F0 ext s := ⟨hc, he, hs⟩

theorem FullM6HdrCoreInv.cfgOk {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} (h : FullM6HdrCoreInv c F0 ext s) : FullM6HdrCfgOk c := h.1

theorem FullM6HdrCoreInv.extOk {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} (h : FullM6HdrCoreInv c F0 ext s) : M6HdrExtOk ext := h.2.1

theorem FullM6HdrCoreInv.coreInv {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} (h : FullM6HdrCoreInv c F0 ext s) : FullCoreInv c F0 s := h.2.2

theorem fullM6HdrMem_mk {c : FullCfg} {ext : List (BitVec 64)} {s : FullState} {m : Mem 64}
    (h : (array64 (c.hdr - 2304) ext ⋆ FullMem c s) m) : FullM6HdrMem c ext s m := h

theorem fullM6HdrMem_iff (c : FullCfg) (ext : List (BitVec 64)) (s : FullState)
    (R : Mem 64 → Prop) (m : Mem 64) :
    (FullM6HdrMem c ext s ⋆ R) m ↔ (FullMem c s ⋆ (array64 (c.hdr - 2304) ext ⋆ R)) m := by
  unfold FullM6HdrMem m6ExtMem m6ExtAddr
  constructor
  · intro h; rw [sep_assoc] at h; exact sep_swap_l h
  · intro h; rw [sep_assoc]; exact sep_swap_l h

theorem fullM6HdrMem_iff_ext (c : FullCfg) (ext : List (BitVec 64)) (s : FullState)
    (R : Mem 64 → Prop) (m : Mem 64) :
    (FullM6HdrMem c ext s ⋆ R) m ↔ (array64 (c.hdr - 2304) ext ⋆ (FullMem c s ⋆ R)) m := by
  unfold FullM6HdrMem m6ExtMem m6ExtAddr
  constructor
  · intro h; rwa [sep_assoc] at h
  · intro h; rwa [sep_assoc]

theorem fullM6HdrMem_focus_full {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullM6HdrMem c ext s ⋆ R) m) :
    (FullMem c s ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m := by
  unfold FullM6HdrMem at hm; rw [sep_assoc] at hm; exact sep_swap_l hm

theorem fullM6HdrMem_unfocus_full {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m) :
    (FullM6HdrMem c ext s ⋆ R) m := by
  unfold FullM6HdrMem; rw [sep_assoc]; exact sep_swap_l hm

/-- Collapses `FullM6HdrMem c ext s` (`2,304 B` prefix + `c.avail B` base) back into a single
contiguous workspace `region (c.hdr - 2304) (2304 + c.avail)`. -/
theorem fullM6HdrMem_to_region {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {m : Mem 64} (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hm : FullM6HdrMem c ext s m) :
    region (m6ExtAddr c.hdr) (fullM6ExtBytes + c.avail) m := by
  unfold FullM6HdrMem m6ExtMem at hm
  have hfit : fullM6ExtBytes + c.avail ≤ 2 ^ 64 := by
    have := c.havail_fit; unfold FullM6HdrCfgOk at hcfg; omega
  have hreg : (region (m6ExtAddr c.hdr) fullM6ExtBytes ⋆ region c.hdr c.avail) m := by
    refine sep_mono2 (fun _ hf => ?_) (fun _ hf => FullArenaInv.to_region ⟨hlen, hf⟩) m hm
    have h1 := array_to_region (t := i64) (xs := ext)
      (by simp [Ty.bytes, Ty.size, i64, hext.len]) ((array64_eq_array _ ext) ▸ hf)
    simpa [Ty.bytes, Ty.size, i64, hext.len, fullM6ExtBytes] using h1
  have hreg' : (region (m6ExtAddr c.hdr) fullM6ExtBytes ⋆
      region (m6ExtAddr c.hdr + BitVec.ofNat 64 fullM6ExtBytes) c.avail) m := by
    rwa [m6ExtAddr_add_bytes c.hdr]
  have hmg := region_merge_eq (a := m6ExtAddr c.hdr) (n1 := fullM6ExtBytes) (n2 := c.avail)
    rfl hfit
  rw [hmg] at hreg'
  exact hreg'

/-! ## 2. Automatic Separation-Logic Framing Bridges Over `FullMem` -/

/-- Generic framing theorem: any `Full1..3` / `M4` / `M5` / `BcpS15` / `CompactFlush` / `FullM6*`
contract parameterized by `(FullMem c s ⋆ R) m` lifts automatically to `FullM6HdrMem c ext s ⋆ R`
preserving `ext` verbatim with zero edits to the underlying proof. -/
theorem fullM6Hdr_frame_full {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {P : (FullState → Mem 64 → Prop) → Prop}
    (hfn : ∀ F : Mem 64 → Prop, (FullMem c s ⋆ F) m → P (fun s' m' => (FullMem c s' ⋆ F) m'))
    (hm : (FullM6HdrMem c ext s ⋆ R) m) :
    P (fun s' m' => (FullM6HdrMem c ext s' ⋆ R) m') := by
  have h1 := hfn (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R) (fullM6HdrMem_focus_full hm)
  have heq : (fun s' m' => (FullMem c s' ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m') =
      (fun s' m' => (FullM6HdrMem c ext s' ⋆ R) m') := by
    funext s' m'; exact propext ⟨fullM6HdrMem_unfocus_full, fullM6HdrMem_focus_full⟩
  rwa [heq] at h1

/-- Automatic framing of canonical `fullAnalyzeSpec` over `M6HdrExt`. -/
theorem fullM6Hdr_frame_analyze {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hsp : FullSparseInvW c F0 F_cur s) (hcf : FullConflictOkW F_cur s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (s'.scratch.work_stk2 = s.scratch.work_stk2 ∧ (r = 20#64 → FullOtfsInvW c F0 F_cur s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode)) →
      (r = 20#64 → F0.Unsat) →
      (r = 0#64 → FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → FullSparseInvW c F0 F_cur s' ∧ s'.core.cur_level < s.core.cur_level) →
      (FullM6HdrMem c ext s' ⋆ R) m' → Q (r, ()) m') :
    fullAnalyzeSpec (c.hdr, ()) m Q X :=
  ⟨c, F0, F_cur, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hsp, hcf,
    fullM6HdrMem_focus_full hm,
    fun r s' m' h1 h2 h3 h4 h5 h6 h7 h8 hm' =>
      hQ r s' m' h1 h2 h3 h4 h5 h6 h7 h8 (fullM6HdrMem_unfocus_full hm')⟩

/-- Automatic framing of canonical `fullPropLitSpec` (`BcpS15` / `Full1`) over `M6HdrExt`. -/
theorem fullM6Hdr_frame_prop_lit {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext : List (BitVec 64)} {s : FullState} {lit : BitVec 32} {ign : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hdense : s.core.dense_mode = 0#64) (hoom : s.core.oom = 0#64)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ (ok : Bool) vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' arena' wstk'
      wlen' wu' ctype' cref' c0' c1' oom' ticks' wsort' phases' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', trail_end := te',
                                unassigned := unass', unflushed := unfl', wvec := wvec',
                                arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                                confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                                confl_lit1 := c1', oom := oom' }
          scratch := { s.scratch with search_ticks := ticks', wsort := wsort', phases := phases' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
      (ok = false → oom' ≠ 0#64 ∨
        (FullConflictOkW F_cur s' ∧ (ctype' = 2#64 → cref' ≠ ign))) →
      (ok = true → oom' = 0#64 ∧ ctype' = s.core.confl_type) →
      (FullM6HdrMem c ext s' ⋆ R) m' → Q (ok, ()) m') :
    fullPropLitSpec (c.hdr, lit, ign, ()) m Q X :=
  ⟨c, F0, F_cur, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hlen, hw, hdense, hoom,
    fullM6HdrMem_focus_full hm,
    fun ok vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' arena' wstk' wlen' wu'
        ctype' cref' c0' c1' oom' ticks' wsort' phases' m' h1 h2 h3 h4 h5 h6 hm' =>
      hQ ok vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' arena' wstk' wlen' wu'
        ctype' cref' c0' c1' oom' ticks' wsort' phases' m' h1 h2 h3 h4 h5 h6
        (fullM6HdrMem_unfocus_full hm')⟩

/-- Automatic framing of canonical `fullSafetyVoidSpec` over `M6HdrExt`. -/
theorem fullM6Hdr_frame_safety_void {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hlen : s.LengthsOk c) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ s' m', s'.core = s.core → s'.LengthsOk c → FullProbeScratchPres s s' →
      (FullM6HdrMem c ext s' ⋆ R) m' → Q () m') :
    fullSafetyVoidSpec (c.hdr, ()) m Q X :=
  ⟨c, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hlen, fullM6HdrMem_focus_full hm,
    fun () s' m' hco hln hpr hm' =>
      hQ s' m' hco hln hpr (fullM6HdrMem_unfocus_full hm')⟩

/-! ## 3. Scoped `M6HdrTactics` (`O(1)` `FullMem ⋆ (array64 ⋆ R)` Accessors, Zero `ecancel`) -/

namespace M6HdrTactics

private theorem shl3_eq {a i : BitVec 64} (hi : i.toNat < 2 ^ 61) :
    a + (i <<< (((3 : BitVec 32).signExtend 64).toNat % 64)) =
      a + BitVec.ofNat 64 (8 * i.toNat) := by
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [show ((3 : BitVec 32).signExtend 64).toNat % 64 = 3 from rfl,
    BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

@[scoped c0_load] theorem load_m6Ext_mul8 {c : FullCfg} {s : FullState} {a i : BitVec 64}
    {ext : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ (array64 a ext ⋆ R)) m) (hi : i.toNat < ext.length) :
    loadVal m i64 (a + i * 8) = some (ext[i.toNat]'hi) := by
  rw [m8]; exact loadVal_array64 hi (sep_swap_l hm)

@[scoped c0_store] theorem store_m6Ext_mul8 {c : FullCfg} {s : FullState} {a i : BitVec 64}
    {ext : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64)
    (hm : (FullMem c s ⋆ (array64 a ext ⋆ R)) m) (hi : i.toNat < ext.length) :
    storeOk m i64 (a + i * 8) ∧
      (FullMem c s ⋆ (array64 a (ext.set i.toNat v) ⋆ R)) (storeMem m i64 (a + i * 8) v) := by
  rw [m8]
  obtain ⟨hok, hst⟩ := store_array64 v hi (sep_swap_l hm)
  exact ⟨hok, sep_swap_l hst⟩

@[scoped c0_load] theorem load_m6Ext_zero {c : FullCfg} {s : FullState} {a : BitVec 64}
    {ext : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ (array64 a ext ⋆ R)) m) (hi : 0 < ext.length) :
    loadVal m i64 a = some (ext[0]'hi) := by
  simpa using loadVal_array64 (i := 0) hi (sep_swap_l hm)

@[scoped c0_store] theorem store_m6Ext_zero {c : FullCfg} {s : FullState} {a : BitVec 64}
    {ext : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64)
    (hm : (FullMem c s ⋆ (array64 a ext ⋆ R)) m) (hi : 0 < ext.length) :
    storeOk m i64 a ∧
      (FullMem c s ⋆ (array64 a (ext.set 0 v) ⋆ R)) (storeMem m i64 a v) := by
  obtain ⟨hok, hst⟩ := store_array64 (i := 0) v hi (sep_swap_l hm)
  exact ⟨by simpa using hok, by simpa using sep_swap_l hst⟩

@[scoped c0_load] theorem load_m6Ext_add0 {c : FullCfg} {s : FullState} {a : BitVec 64}
    {ext : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ (array64 a ext ⋆ R)) m) (hi : 0 < ext.length) :
    loadVal m i64 (a + 0) = some (ext[0]'hi) := by
  simpa using load_m6Ext_zero hm hi

@[scoped c0_store] theorem store_m6Ext_add0 {c : FullCfg} {s : FullState} {a : BitVec 64}
    {ext : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64)
    (hm : (FullMem c s ⋆ (array64 a ext ⋆ R)) m) (hi : 0 < ext.length) :
    storeOk m i64 (a + 0) ∧
      (FullMem c s ⋆ (array64 a (ext.set 0 v) ⋆ R)) (storeMem m i64 (a + 0) v) := by
  simpa using store_m6Ext_zero v hm hi

@[scoped c0_load] theorem load_m6Ext_shl3 {c : FullCfg} {s : FullState} {a i : BitVec 64}
    {ext : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ (array64 a ext ⋆ R)) m) (hi : i.toNat < ext.length)
    (hb : i.toNat < 2 ^ 61) :
    loadVal m i64 (a + (i <<< (((3 : BitVec 32).signExtend 64).toNat % 64))) =
      some (ext[i.toNat]'hi) := by
  rw [shl3_eq hb]; exact loadVal_array64 hi (sep_swap_l hm)

@[scoped c0_store] theorem store_m6Ext_shl3 {c : FullCfg} {s : FullState} {a i : BitVec 64}
    {ext : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64)
    (hm : (FullMem c s ⋆ (array64 a ext ⋆ R)) m) (hi : i.toNat < ext.length)
    (hb : i.toNat < 2 ^ 61) :
    storeOk m i64 (a + (i <<< (((3 : BitVec 32).signExtend 64).toNat % 64))) ∧
      (FullMem c s ⋆ (array64 a (ext.set i.toNat v) ⋆ R))
        (storeMem m i64 (a + (i <<< (((3 : BitVec 32).signExtend 64).toNat % 64))) v) := by
  rw [shl3_eq hb]
  obtain ⟨hok, hst⟩ := store_array64 v hi (sep_swap_l hm)
  exact ⟨hok, sep_swap_l hst⟩

@[scoped c0_load] theorem load_m6Ext_const {c : FullCfg} {s : FullState} {a k : BitVec 64}
    {ext : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ (array64 a ext ⋆ R)) m) (hmod : k.toNat % 8 = 0)
    (hi : k.toNat / 8 < ext.length) :
    loadVal m i64 (a + k) = some (ext[k.toNat / 8]'hi) := by
  have hk : a + k = a + BitVec.ofNat 64 (8 * (k.toNat / 8)) := by
    congr 1; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  rw [hk]; exact loadVal_array64 hi (sep_swap_l hm)

@[scoped c0_store] theorem store_m6Ext_const {c : FullCfg} {s : FullState} {a k : BitVec 64}
    {ext : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 64)
    (hm : (FullMem c s ⋆ (array64 a ext ⋆ R)) m) (hmod : k.toNat % 8 = 0)
    (hi : k.toNat / 8 < ext.length) :
    storeOk m i64 (a + k) ∧
      (FullMem c s ⋆ (array64 a (ext.set (k.toNat / 8) v) ⋆ R)) (storeMem m i64 (a + k) v) := by
  have hk : a + k = a + BitVec.ofNat 64 (8 * (k.toNat / 8)) := by
    congr 1; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  rw [hk]
  obtain ⟨hok, hst⟩ := store_array64 v hi (sep_swap_l hm)
  exact ⟨hok, sep_swap_l hst⟩

scoped macro "m6h_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

end M6HdrTactics

open scoped M6HdrTactics

/-! ## 4. All `27` `FullM6Hdr` Function Specifications & Bridges -/

def m6HdrSizeofSpec : Spec [] [i64] := fun () m Q _ =>
  Q (BitVec.ofNat 64 fullM6HdrTotalBytes, ()) m

def m6ExtSizeofSpec : Spec [] [i64] := fun () m Q _ =>
  Q (BitVec.ofNat 64 fullM6ExtBytes, ()) m

@[expose] def m6HdrInitSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ ext' m', M6HdrExtInitOk ext' → (FullM6HdrMem c ext' s ⋆ R) m' → Q () m'

def m6HdrResetSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ ext' m', M6HdrExtInitOk ext' →
      let s' : FullState := { s with scratch := { s.scratch with tier1 := 2#64, tier2 := 6#64 } }
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m'

@[expose] def m6ExtEnsureInitSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ ext' m', M6HdrExtInitOk ext' → (M6HdrExtInitOk ext → ext' = ext) →
      (FullM6HdrMem c ext' s ⋆ R) m' → Q () m'

def m6HdrExtReadySpec : Spec [i64] [.bool] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ ext' m', M6HdrExtInitOk ext' → (M6HdrExtInitOk ext → ext' = ext) →
      (FullM6HdrMem c ext' s ⋆ R) m' → Q (true, ()) m'

@[expose] def fullM6MemInitSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cend, work_base, avail, fuel, ()) m Q _ =>
    ∃ (cnfBytes : List UInt8) (R : Mem 64 → Prop),
      cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      work_base.toNat + avail.toNat < 2 ^ 64 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_base avail.toNat ⋆ R) m ∧
      (∀ m', (bytes cnf_ptr cnfBytes ⋆ region work_base avail.toNat ⋆ R) m' →
        (avail.toNat < fullM6HdrTotalBytes ∨
          ∀ mv nc rest, parseHeader cnfBytes = some (mv, nc, rest) →
            avail.toNat - fullM6ExtBytes < fullFixedBytes mv + nc * 40 + 136) →
        Q (0#64, ()) m') ∧
      (∀ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (j : Nat) (rest : List UInt8)
          (m' : Mem 64),
        c.hdr = work_base + BitVec.ofNat 64 fullM6ExtBytes →
        c.avail = avail.toNat - fullM6ExtBytes →
        FullM6HdrCfgOk c → M6HdrExtInitOk ext →
        parseHeader cnfBytes = some (c.mv, c.nc, rest) →
        j ≤ cnfBytes.length → cnfBytes.drop j = rest →
        FullM6HdrInv c (shiftDownCnf CNF.empty) ext s →
        s.core.cur_vars = c.mv → s.core.d_cur = cnf_ptr + BitVec.ofNat 64 j →
        s.core.arena_len = 0 → s.core.wlen = 1 → s.core.trail_end = 0 →
        s.core.propagated = 0 → s.core.cur_level = 0 → s.core.fuel = fuel →
        s.core.oom = 0#64 → s.core.inconsistent = 0#64 →
        (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c ext s ⋆ R) m' →
        Q (c.hdr, ()) m')

/-- Shared contract for all `FullM6Hdr` tier/delay/watermark helpers on `FullM6HdrMem`:
preserves `s.core` verbatim, `FullProbeScratchPres`, `M6HdrBaseDelayedPres` (`h->delayed*`
untouched), and `M6ExtW2bPres` (once initialized, `M6HdrExtInitOk` & words `1..7` hold). -/
def m6HdrW2aSpec (extraArgs rs : List Ty) : Spec (i64 :: extraArgs) rs :=
  fun args m Q _ =>
    ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      args.1 = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ (r : Tup Val rs) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
        s'.core = s.core → s'.LengthsOk c → M6HdrScratchPres s s' →
        M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q r m'

/-- Contract for `FullM6Hdr` `decision_rate` mutators (`m6_hdr_dr_init`, `m6_hdr_dr_update`):
zero writes to `FullMem` (`s` unchanged), zero collision with `h->delayed*`, and once initialized
preserves `m6_magic` + all tier/watermark words `8..287` (`M6ExtW2aPres`). -/
def m6HdrDrMutSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ ext' m', M6HdrExtInitOk ext' → (M6HdrExtInitOk ext → M6ExtW2aPres ext ext') →
      (FullM6HdrMem c ext' s ⋆ R) m' → Q () m'

/-- Contract for `FullM6Hdr` `m6_hdr_dr_allow`: zero writes to `FullMem`, pure read when
already initialized (`ext' = ext`). -/
def m6HdrDrAllowSpec : Spec [i64] [.bool] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ (r : Bool) ext' m', M6HdrExtInitOk ext' → (M6HdrExtInitOk ext → ext' = ext) →
      (FullM6HdrMem c ext' s ⋆ R) m' → Q (r, ()) m'

/-- Lifted canonical `fullDecideSpec` over `FullM6HdrMem` (`m6_hdr_decide`). -/
def m6HdrDecideSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCoreInv c F0 ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' cl' unass' unfl' sc' ext' m',
      let s' : FullState :=
        { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', frame_trail := ftrl',
                                frame_dec := fdec', trail_end := te', cur_level := cl',
                                unassigned := unass', unflushed := unfl' }
          scratch := sc' }
      FullM6HdrCoreInv c F0 ext' s' → FullExtScratchPres s s' → (r = 0#64 ∨ r = 1#64) →
      (r = 0#64 → cl' = s.core.cur_level ∧ te' = s.core.trail_end) →
      (r = 1#64 → cl' = s.core.cur_level + 1 ∧ te' = s.core.trail_end + 1 ∧
        M6HdrExtInitOk ext' ∧ (M6HdrExtInitOk ext → M6ExtW2aPres ext ext')) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Lifted canonical `fullAnalyzeRsnSpec` over `FullM6HdrMem` (`m6_hdr_analyze_rsn`). -/
def m6HdrAnalyzeRsnSpec : Spec [i64, i32, i32] [.bool] := fun (h, rsn, skip_var, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut : Nat)
    (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
    FullWitnessCutInv c F0 F_cur cut s.core ∧ FullAnaMarksCov c s ∧
    s.core.tmp_len ≤ s.core.cur_vars ∧ s.core.tmp_cnt + s.core.cur_vars + 1 < 2 ^ 64 ∧
    (rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ∈ fullArenaClauseRefs s) ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ (ok : Bool) mrk' tmp' tc' tl' mcl' arena' sc' ext' m',
      let s' : FullState :=
        { s with
          core := { s.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                                min_clr_len := mcl', arena := arena' }
          scratch := sc' }
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6ExtW2bPres ext ext') →
      s'.LengthsOk c → FullWitnessCutInv c F0 F_cur cut s'.core → FullAnaMarksCov c s' →
      FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
      s.core.tmp_len ≤ tl' → tl' ≤ s.core.cur_vars → s.core.tmp_cnt ≤ tc' →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
        fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
        fullArenaClauseLits s' r = fullArenaClauseLits s r) →
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
        mrk'[v]?.getD 0#8 = s.core.mrk[v]?.getD 0#8) →
      (∀ k < s.core.tmp_len, tmp'[k]? = s.core.tmp[k]?) →
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
        ∃ l ∈ fullRsnLits s rsn, l / 2 = v ∧ v < s.core.cur_vars ∧ v ≠ skip_var.toNat ∧
          0 < (s.core.lvl[v]?.getD 0#32).toNat ∧
          (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level) →
      (∀ j, s.core.tmp_len ≤ j → j < tl' →
        let l := (tmp'[j]?.getD 0#32).toNat
        l ∈ fullRsnLits s rsn ∧ l < 2 * s.core.cur_vars ∧ l / 2 ≠ skip_var.toNat ∧
        s.core.mrk[l / 2]?.getD 0#8 = 0#8 ∧
        0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
        (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level ∧
        mrk'[l / 2]?.getD 0#8 ≠ 0#8) →
      (∀ j1 j2, s.core.tmp_len ≤ j1 → j1 < j2 → j2 < tl' →
        (tmp'[j1]?.getD 0#32).toNat / 2 ≠ (tmp'[j2]?.getD 0#32).toNat / 2) →
      (tc' - s.core.tmp_cnt = ((List.range s.core.cur_vars).filter fun w =>
        decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8) &&
        decide ((s.core.lvl[w]?.getD 0#32).toNat = s.core.cur_level)).length) →
      (sc'.res_sz = s.scratch.res_sz + BitVec.ofNat 64 ((List.range s.core.cur_vars).filter fun w =>
        decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8)).length) →
      (ok = true → rsn ≠ 0xFFFFFFFF#32 ∧
        sc'.ant_sz = s.scratch.ant_sz + BitVec.ofNat 64 ((fullRsnLits s rsn).countP fun l =>
          decide (l / 2 < s.core.cur_vars ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
            (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level)) ∧
        ∀ l ∈ fullRsnLits s rsn, l / 2 < s.core.cur_vars ∧
          (l / 2 ≠ skip_var.toNat →
            (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
            (s.core.mrk[l / 2]?.getD 0#8 = 0#8 →
              (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level ∧
              (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat →
                (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level →
                ∃ j, s.core.tmp_len ≤ j ∧ j < tl' ∧
                  (tmp'[j]?.getD 0#32).toNat / 2 = l / 2)))) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (ok, ()) m'

/-- Lifted canonical `fullAnalyzeSpec` over `FullM6HdrMem` (`m6_hdr_analyze`), composing
`m6_hdr_update_tier_limits` + `m6_hdr_dr_update` + `full_analyze`. -/
def m6HdrAnalyzeSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (ext : List (BitVec 64))
    (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrInvW c F0 F_cur ext s ∧ FullConflictOkW F_cur s ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      M6HdrExtOk ext' → s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (s'.scratch.work_stk2 = s.scratch.work_stk2 ∧ (r = 20#64 → FullOtfsInvW c F0 F_cur s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode)) →
      (r = 20#64 → F0.Unsat) →
      (r = 0#64 → FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → FullM6HdrInvW c F0 F_cur ext' s' ∧ s'.core.cur_level < s.core.cur_level) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

/-! ### Public Spec Constructors, Destructors & `monoX` Bridges -/

theorem m6HdrSizeofSpec_monoX {xs : Tup Val []} {m : Mem 64} {Q : Post [i64]} {X X' : XPost}
    (h : m6HdrSizeofSpec xs m Q X) : m6HdrSizeofSpec xs m Q X' := by
  rcases xs with ⟨⟩; exact h

theorem m6ExtSizeofSpec_monoX {xs : Tup Val []} {m : Mem 64} {Q : Post [i64]} {X X' : XPost}
    (h : m6ExtSizeofSpec xs m Q X) : m6ExtSizeofSpec xs m Q X' := by
  rcases xs with ⟨⟩; exact h

theorem m6HdrInitSpec_of {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ ext' m', M6HdrExtInitOk ext' → (FullM6HdrMem c ext' s ⋆ R) m' → Q () m') :
    m6HdrInitSpec (c.hdr, ()) m Q X :=
  ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩

theorem m6HdrInitSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post []} {X X' : XPost}
    (h : m6HdrInitSpec xs m Q X) : m6HdrInitSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem m6HdrResetSpec_of {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ ext' m', M6HdrExtInitOk ext' →
      let s' : FullState := { s with scratch := { s.scratch with tier1 := 2#64, tier2 := 6#64 } }
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q () m') :
    m6HdrResetSpec (c.hdr, ()) m Q X :=
  ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩

theorem m6HdrResetSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post []} {X X' : XPost}
    (h : m6HdrResetSpec xs m Q X) : m6HdrResetSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem m6ExtEnsureInitSpec_of {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ ext' m', M6HdrExtInitOk ext' → (M6HdrExtInitOk ext → ext' = ext) →
      (FullM6HdrMem c ext' s ⋆ R) m' → Q () m') :
    m6ExtEnsureInitSpec (c.hdr, ()) m Q X :=
  ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩

theorem m6ExtEnsureInitSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post []} {X X' : XPost}
    (h : m6ExtEnsureInitSpec xs m Q X) : m6ExtEnsureInitSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem m6HdrExtReadySpec_of {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ ext' m', M6HdrExtInitOk ext' → (M6HdrExtInitOk ext → ext' = ext) →
      (FullM6HdrMem c ext' s ⋆ R) m' → Q (true, ()) m') :
    m6HdrExtReadySpec (c.hdr, ()) m Q X :=
  ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩

theorem m6HdrExtReadySpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [.bool]}
    {X X' : XPost} (h : m6HdrExtReadySpec xs m Q X) : m6HdrExtReadySpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem fullM6MemInitSpec_of {cnf_ptr cend work_base avail fuel : BitVec 64}
    {cnfBytes : List UInt8} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hcend : cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length)
    (hfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_base.toNat + avail.toNat < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_base avail.toNat ⋆ R) m)
    (hFail : ∀ m', (bytes cnf_ptr cnfBytes ⋆ region work_base avail.toNat ⋆ R) m' →
      (avail.toNat < fullM6HdrTotalBytes ∨
        ∀ mv nc rest, parseHeader cnfBytes = some (mv, nc, rest) →
          avail.toNat - fullM6ExtBytes < fullFixedBytes mv + nc * 40 + 136) →
      Q (0#64, ()) m')
    (hOk : ∀ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (j : Nat) (rest : List UInt8)
        (m' : Mem 64),
      c.hdr = work_base + BitVec.ofNat 64 fullM6ExtBytes →
      c.avail = avail.toNat - fullM6ExtBytes →
      FullM6HdrCfgOk c → M6HdrExtInitOk ext →
      parseHeader cnfBytes = some (c.mv, c.nc, rest) →
      j ≤ cnfBytes.length → cnfBytes.drop j = rest →
      FullM6HdrInv c (shiftDownCnf CNF.empty) ext s →
      s.core.cur_vars = c.mv → s.core.d_cur = cnf_ptr + BitVec.ofNat 64 j →
      s.core.arena_len = 0 → s.core.wlen = 1 → s.core.trail_end = 0 →
      s.core.propagated = 0 → s.core.cur_level = 0 → s.core.fuel = fuel →
      s.core.oom = 0#64 → s.core.inconsistent = 0#64 →
      (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c ext s ⋆ R) m' →
      Q (c.hdr, ()) m') :
    fullM6MemInitSpec (cnf_ptr, cend, work_base, avail, fuel, ()) m Q X :=
  ⟨cnfBytes, R, hcend, hfit, hwfit, hm, hFail, hOk⟩

theorem fullM6MemInitSpec_monoX {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X X' : XPost}
    (h : fullM6MemInitSpec xs m Q X) : fullM6MemInitSpec xs m Q X' := by
  rcases xs with ⟨_, _, _, _, _, ⟨⟩⟩; exact h

theorem m6HdrW2aSpec_of {extraArgs rs : List Ty} {args : Tup Val (i64 :: extraArgs)}
    {c : FullCfg} {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post rs} {X : XPost}
    (hh : args.1 = c.hdr) (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext)
    (hlen : s.LengthsOk c) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ (r : Tup Val rs) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      s'.core = s.core → s'.LengthsOk c → M6HdrScratchPres s s' →
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q r m') :
    m6HdrW2aSpec extraArgs rs args m Q X :=
  ⟨c, ext, s, R, hh, hcfg, hext, hlen, hm, hQ⟩

theorem m6HdrW2aSpec_elim {extraArgs rs : List Ty} {args : Tup Val (i64 :: extraArgs)}
    {m : Mem 64} {Q : Post rs} {X : XPost} (h : m6HdrW2aSpec extraArgs rs args m Q X) :
    ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      args.1 = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ (r : Tup Val rs) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
        s'.core = s.core → s'.LengthsOk c → M6HdrScratchPres s s' →
        M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q r m' := h

theorem m6HdrW2aSpec_monoX {extraArgs rs : List Ty} {xs : Tup Val (i64 :: extraArgs)}
    {m : Mem 64} {Q : Post rs} {X X' : XPost}
    (h : m6HdrW2aSpec extraArgs rs xs m Q X) : m6HdrW2aSpec extraArgs rs xs m Q X' := h

theorem m6HdrDrMutSpec_of {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ ext' m', M6HdrExtInitOk ext' → (M6HdrExtInitOk ext → M6ExtW2aPres ext ext') →
      (FullM6HdrMem c ext' s ⋆ R) m' → Q () m') :
    m6HdrDrMutSpec (c.hdr, ()) m Q X :=
  ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩

theorem m6HdrDrMutSpec_elim {h : BitVec 64} {m : Mem 64} {Q : Post []} {X : XPost}
    (hs : m6HdrDrMutSpec (h, ()) m Q X) :
    ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ ext' m', M6HdrExtInitOk ext' → (M6HdrExtInitOk ext → M6ExtW2aPres ext ext') →
        (FullM6HdrMem c ext' s ⋆ R) m' → Q () m' := hs

theorem m6HdrDrMutSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post []} {X X' : XPost}
    (h : m6HdrDrMutSpec xs m Q X) : m6HdrDrMutSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem m6HdrDrAllowSpec_of {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ (r : Bool) ext' m', M6HdrExtInitOk ext' → (M6HdrExtInitOk ext → ext' = ext) →
      (FullM6HdrMem c ext' s ⋆ R) m' → Q (r, ()) m') :
    m6HdrDrAllowSpec (c.hdr, ()) m Q X :=
  ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩

theorem m6HdrDrAllowSpec_elim {h : BitVec 64} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    (hs : m6HdrDrAllowSpec (h, ()) m Q X) :
    ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ (r : Bool) ext' m', M6HdrExtInitOk ext' → (M6HdrExtInitOk ext → ext' = ext) →
        (FullM6HdrMem c ext' s ⋆ R) m' → Q (r, ()) m' := hs

theorem m6HdrDrAllowSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [.bool]}
    {X X' : XPost} (h : m6HdrDrAllowSpec xs m Q X) : m6HdrDrAllowSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem m6HdrDecideSpec_of {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hinv : FullM6HdrCoreInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ r vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' cl' unass' unfl' sc' ext' m',
      let s' : FullState :=
        { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', frame_trail := ftrl',
                                frame_dec := fdec', trail_end := te', cur_level := cl',
                                unassigned := unass', unflushed := unfl' }
          scratch := sc' }
      FullM6HdrCoreInv c F0 ext' s' → FullExtScratchPres s s' → (r = 0#64 ∨ r = 1#64) →
      (r = 0#64 → cl' = s.core.cur_level ∧ te' = s.core.trail_end) →
      (r = 1#64 → cl' = s.core.cur_level + 1 ∧ te' = s.core.trail_end + 1 ∧
        M6HdrExtInitOk ext' ∧ (M6HdrExtInitOk ext → M6ExtW2aPres ext ext')) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    m6HdrDecideSpec (c.hdr, ()) m Q X :=
  ⟨c, F0, ext, s, R, rfl, hinv, hm, hQ⟩

theorem m6HdrDecideSpec_elim {h : BitVec 64} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hs : m6HdrDecideSpec (h, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCoreInv c F0 ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ r vals' flags' lvl' rsns' trl' tp' ftrl' fdec' te' cl' unass' unfl' sc' ext' m',
        let s' : FullState :=
          { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                  trl := trl', trail_pos := tp', frame_trail := ftrl',
                                  frame_dec := fdec', trail_end := te', cur_level := cl',
                                  unassigned := unass', unflushed := unfl' }
            scratch := sc' }
        FullM6HdrCoreInv c F0 ext' s' → FullExtScratchPres s s' → (r = 0#64 ∨ r = 1#64) →
        (r = 0#64 → cl' = s.core.cur_level ∧ te' = s.core.trail_end) →
        (r = 1#64 → cl' = s.core.cur_level + 1 ∧ te' = s.core.trail_end + 1 ∧
          M6HdrExtInitOk ext' ∧ (M6HdrExtInitOk ext → M6ExtW2aPres ext ext')) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m' := hs

theorem m6HdrDecideSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]} {X X' : XPost}
    (h : m6HdrDecideSpec xs m Q X) : m6HdrDecideSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem m6HdrAnalyzeRsnSpec_elim {h : BitVec 64} {rsn skip_var : BitVec 32} {m : Mem 64}
    {Q : Post [.bool]} {X : XPost} (hs : m6HdrAnalyzeRsnSpec (h, rsn, skip_var, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut : Nat)
      (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
      FullWitnessCutInv c F0 F_cur cut s.core ∧ FullAnaMarksCov c s ∧
      s.core.tmp_len ≤ s.core.cur_vars ∧ s.core.tmp_cnt + s.core.cur_vars + 1 < 2 ^ 64 ∧
      (rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ∈ fullArenaClauseRefs s) ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ (ok : Bool) mrk' tmp' tc' tl' mcl' arena' sc' ext' m',
        let s' : FullState :=
          { s with
            core := { s.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                                  min_clr_len := mcl', arena := arena' }
            scratch := sc' }
        M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6ExtW2bPres ext ext') →
        s'.LengthsOk c → FullWitnessCutInv c F0 F_cur cut s'.core → FullAnaMarksCov c s' →
        FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
        s.core.tmp_len ≤ tl' → tl' ≤ s.core.cur_vars → s.core.tmp_cnt ≤ tc' →
        fullArenaClauseRefs s' = fullArenaClauseRefs s →
        (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
          fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
          fullArenaClauseLits s' r = fullArenaClauseLits s r) →
        (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
          mrk'[v]?.getD 0#8 = s.core.mrk[v]?.getD 0#8) →
        (∀ k < s.core.tmp_len, tmp'[k]? = s.core.tmp[k]?) →
        (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
          ∃ l ∈ fullRsnLits s rsn, l / 2 = v ∧ v < s.core.cur_vars ∧ v ≠ skip_var.toNat ∧
            0 < (s.core.lvl[v]?.getD 0#32).toNat ∧
            (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level) →
        (∀ j, s.core.tmp_len ≤ j → j < tl' →
          let l := (tmp'[j]?.getD 0#32).toNat
          l ∈ fullRsnLits s rsn ∧ l < 2 * s.core.cur_vars ∧ l / 2 ≠ skip_var.toNat ∧
          s.core.mrk[l / 2]?.getD 0#8 = 0#8 ∧
          0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
          (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level ∧
          mrk'[l / 2]?.getD 0#8 ≠ 0#8) →
        (∀ j1 j2, s.core.tmp_len ≤ j1 → j1 < j2 → j2 < tl' →
          (tmp'[j1]?.getD 0#32).toNat / 2 ≠ (tmp'[j2]?.getD 0#32).toNat / 2) →
        (tc' - s.core.tmp_cnt = ((List.range s.core.cur_vars).filter fun w =>
          decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8) &&
          decide ((s.core.lvl[w]?.getD 0#32).toNat = s.core.cur_level)).length) →
        (sc'.res_sz = s.scratch.res_sz + BitVec.ofNat 64 ((List.range s.core.cur_vars).filter
          fun w => decide (s.core.mrk[w]?.getD 0#8 = 0#8) &&
            decide (mrk'[w]?.getD 0#8 ≠ 0#8)).length) →
        (ok = true → rsn ≠ 0xFFFFFFFF#32 ∧
          sc'.ant_sz = s.scratch.ant_sz + BitVec.ofNat 64 ((fullRsnLits s rsn).countP fun l =>
            decide (l / 2 < s.core.cur_vars ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
              (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level)) ∧
          ∀ l ∈ fullRsnLits s rsn, l / 2 < s.core.cur_vars ∧
            (l / 2 ≠ skip_var.toNat →
              (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
              (s.core.mrk[l / 2]?.getD 0#8 = 0#8 →
                (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level ∧
                (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat →
                  (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level →
                  ∃ j, s.core.tmp_len ≤ j ∧ j < tl' ∧
                    (tmp'[j]?.getD 0#32).toNat / 2 = l / 2)))) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (ok, ()) m' := hs

theorem m6HdrAnalyzeRsnSpec_monoX {xs : Tup Val [i64, i32, i32]} {m : Mem 64}
    {Q : Post [.bool]} {X X' : XPost}
    (h : m6HdrAnalyzeRsnSpec xs m Q X) : m6HdrAnalyzeRsnSpec xs m Q X' := by
  rcases xs with ⟨_, _, _, ⟨⟩⟩; exact h

theorem m6HdrAnalyzeSpec_of {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hinv : FullM6HdrInvW c F0 F_cur ext s) (hcf : FullConflictOkW F_cur s)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ r ext' s' m',
      M6HdrExtOk ext' → s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (s'.scratch.work_stk2 = s.scratch.work_stk2 ∧ (r = 20#64 → FullOtfsInvW c F0 F_cur s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode)) →
      (r = 20#64 → F0.Unsat) →
      (r = 0#64 → FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → FullM6HdrInvW c F0 F_cur ext' s' ∧ s'.core.cur_level < s.core.cur_level) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    m6HdrAnalyzeSpec (c.hdr, ()) m Q X :=
  ⟨c, F0, F_cur, ext, s, R, rfl, hinv, hcf, hm, hQ⟩

theorem m6HdrAnalyzeSpec_elim {h : BitVec 64} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hs : m6HdrAnalyzeSpec (h, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (ext : List (BitVec 64))
      (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrInvW c F0 F_cur ext s ∧ FullConflictOkW F_cur s ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ r ext' s' m',
        M6HdrExtOk ext' → s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (s'.scratch.work_stk2 = s.scratch.work_stk2 ∧ (r = 20#64 → FullOtfsInvW c F0 F_cur s' ∧
          s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode)) →
        (r = 20#64 → F0.Unsat) →
        (r = 0#64 → FullOtfsInvW c F0 F_cur s') →
        (r = 1#64 → FullM6HdrInvW c F0 F_cur ext' s' ∧ s'.core.cur_level < s.core.cur_level) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m' := hs

theorem m6HdrAnalyzeSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]} {X X' : XPost}
    (h : m6HdrAnalyzeSpec xs m Q X) : m6HdrAnalyzeSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h


end LeanQbe.T.Examples.Kissat.Proof.Spec
