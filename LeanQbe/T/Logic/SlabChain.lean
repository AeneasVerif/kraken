module

public import LeanQbe.T.Logic.Bytes
public import LeanQbe.T.Logic.SepTree
import all Kraken.Separation

/-!
# `SlabChain`: Contiguous Arena Slab Collapse (`regions_to_avail`)

Generic inductive collapse of any contiguous slab of headers, typed arrays (exact or `align8`-
padded), concrete byte slices, cells, and trailing slack into a single `region base totalBytes`:

* `align8` rounds any byte count up to the next multiple of `8` with standard arithmetic lemmas.
* `SlabSeg` describes one contiguous segment of width `stride` collapsing to `region a stride`
  whenever `stride ≤ 2 ^ 64` (checked once at the top level by `SlabChain.to_region`, eliminating
  per-segment overflow boilerplate).
* Smart constructors: `SlabSeg.ofArray64`, `SlabSeg.ofArray`, `SlabSeg.ofArrayExact`,
  `SlabSeg.ofArrayAlign8`, `SlabSeg.ofRegion`, `SlabSeg.ofBytes`, `SlabSeg.ofCell`,
  `SlabSeg.ofCell64`.
* `SlabChain.to_region` / `SlabChain.to_region_eq` / `SlabChain.to_region_frame` collapse linear
  chains in `O(K)`.
* `SlabChain.balancedTree` / `SlabChain.balancedTree_to_region` bridge directly from a balanced
  `SepTree` layout to `region base totalBytes` in `O(K)` with **zero `ecancel`**.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

open Std Std.ExtHashMap

/-! ## 1. 8-Byte Alignment Helper (`align8`) -/

/-- Round `n` up to the next multiple of `8`. -/
def align8 (n : Nat) : Nat := ((n + 7) / 8) * 8

theorem align8_ge (n : Nat) : n ≤ align8 n := by
  unfold align8; omega

theorem align8_le (n : Nat) : align8 n ≤ n + 7 := by
  unfold align8; omega

theorem align8_mod (n : Nat) : align8 n % 8 = 0 := by
  unfold align8; omega

theorem align8_zero : align8 0 = 0 := rfl

theorem align8_mul8 (k : Nat) : align8 (8 * k) = 8 * k := by
  unfold align8; omega

theorem align8_mono {a b : Nat} (h : a ≤ b) : align8 a ≤ align8 b := by
  unfold align8; omega

/-! ## 2. `SlabSeg` Descriptors & Smart Constructors -/

/-- One contiguous slab segment of `stride` bytes collapsing to `region a stride`. -/
structure SlabSeg where
  stride : Nat
  pred : BitVec 64 → Mem 64 → Prop
  toReg : ∀ a m, stride ≤ 2 ^ 64 → pred a m → region a stride m

/-- Segment from an `array64` header block of `k` 64-bit words (`8 * k` bytes). -/
def SlabSeg.ofArray64 (xs : List (BitVec 64)) (k : Nat) (hk : xs.length = k) : SlabSeg where
  stride := 8 * k
  pred a := array64 a xs
  toReg a _ hfit h := by
    rw [array64_eq_array] at h
    have hbytes := array_eq_bytesOf (t := i64) a xs
      (by simp only [Ty.bytes, Ty.size, i64, hk]; omega) h
    have hreg := bytes_to_region (a := a) (bs := bytesOf (t := i64) xs) hbytes.symm
    simpa only [bytesOf_length, Ty.bytes, Ty.size, i64, hk] using hreg

/-- Segment from a typed `array (t := ty)` plus explicit trailing padding to `stride` bytes. -/
def SlabSeg.ofArray (ty : Ty) (xs : List (Val ty)) (active stride : Nat)
    (hact : ty.bytes * xs.length = active) (hle : active ≤ stride) : SlabSeg where
  stride := stride
  pred a := array (t := ty) a xs ⋆ region (a + BitVec.ofNat 64 active) (stride - active)
  toReg a _ hfit hm := by
    obtain ⟨m1, m2, hu, hd, h1, h2⟩ := hm
    have hr1 : region a active m1 := by
      have hbytes := array_eq_bytesOf (t := ty) a xs (by omega) h1
      have hreg := bytes_to_region (a := a) (bs := bytesOf (t := ty) xs) hbytes.symm
      simpa only [bytesOf_length, hact] using hreg
    have hmerge := region_merge_eq (a := a) (n1 := active) (n2 := stride - active)
      (n := stride) (by omega) hfit
    rw [← hmerge]
    exact ⟨m1, m2, hu, hd, hr1, h2⟩

/-- Segment from a typed `array (t := ty)` with exact width `active` (zero padding leaf). -/
def SlabSeg.ofArrayExact (ty : Ty) (xs : List (Val ty)) (active : Nat)
    (hact : ty.bytes * xs.length = active) : SlabSeg where
  stride := active
  pred a := array (t := ty) a xs
  toReg a _ hfit h := by
    have hbytes := array_eq_bytesOf (t := ty) a xs (by omega) h
    have hreg := bytes_to_region (a := a) (bs := bytesOf (t := ty) xs) hbytes.symm
    simpa only [bytesOf_length, hact] using hreg

/-- Segment from a typed `array (t := ty)` padded up to `align8 active` bytes. -/
def SlabSeg.ofArrayAlign8 (ty : Ty) (xs : List (Val ty)) (active : Nat)
    (hact : ty.bytes * xs.length = active) : SlabSeg :=
  SlabSeg.ofArray ty xs active (align8 active) hact (align8_ge active)

/-- Segment from a raw `region a n` (e.g., trailing slack or scratch space). -/
def SlabSeg.ofRegion (n : Nat) : SlabSeg where
  stride := n
  pred a := region a n
  toReg _ _ _ h := h

/-- Segment from a concrete byte slice `bytes a bs` of length `n`. -/
def SlabSeg.ofBytes (bs : List UInt8) (n : Nat) (hn : bs.length = n) : SlabSeg where
  stride := n
  pred a := bytes a bs
  toReg _ _ _ h := hn ▸ bytes_to_region h

/-- Segment from a single typed `cell (t := ty) a v`. -/
def SlabSeg.ofCell (ty : Ty) (v : Val ty) : SlabSeg where
  stride := ty.bytes
  pred a := cell (t := ty) a v
  toReg _ _ _ h := by
    refine ⟨Int.toBytes ty.bytes ((toBits ty v).setWidth (8 * ty.bytes)).toInt,
      Int.toBytes_length _ _, h.symm⟩

/-- Segment from a single 64-bit word `cell64 a v`. -/
def SlabSeg.ofCell64 (v : BitVec 64) : SlabSeg where
  stride := 8
  pred a := cell64 a v
  toReg _ _ _ h := ⟨Int.toBytes 8 v.toInt, Int.toBytes_length _ _, h.symm⟩

/-! ## 3. `SlabChain`: Contiguous Chain Evaluation & Collapse -/

/-- Contiguous `⋆`-layout of a list of `SlabSeg` starting at `base`. -/
def SlabChain.eval (base : BitVec 64) : List SlabSeg → Mem 64 → Prop
  | [] => emp
  | seg :: rest => seg.pred base ⋆ SlabChain.eval (base + BitVec.ofNat 64 seg.stride) rest

/-- Total byte width of a `SlabChain`. -/
def SlabChain.totalBytes : List SlabSeg → Nat
  | [] => 0
  | seg :: rest => seg.stride + SlabChain.totalBytes rest

/-- Running end address of a `SlabChain` (chained `+` matching pointer definitions). -/
def SlabChain.endAddr (base : BitVec 64) : List SlabSeg → BitVec 64
  | [] => base
  | seg :: rest => SlabChain.endAddr (base + BitVec.ofNat 64 seg.stride) rest

theorem SlabChain.totalBytes_append (l r : List SlabSeg) :
    SlabChain.totalBytes (l ++ r) = SlabChain.totalBytes l + SlabChain.totalBytes r := by
  induction l with
  | nil => simp [SlabChain.totalBytes]
  | cons seg rest ih => simp [SlabChain.totalBytes, ih, Nat.add_assoc]

theorem SlabChain.endAddr_eq : ∀ (segs : List SlabSeg) (base : BitVec 64),
    SlabChain.endAddr base segs = base + BitVec.ofNat 64 (SlabChain.totalBytes segs)
  | [], base => by simp [SlabChain.endAddr, SlabChain.totalBytes]
  | seg :: rest, base => by
    simp only [SlabChain.endAddr, SlabChain.totalBytes]
    rw [SlabChain.endAddr_eq rest (base + BitVec.ofNat 64 seg.stride), ptr_add_ofNat]

theorem SlabChain.endAddr_append (base : BitVec 64) (l r : List SlabSeg) :
    SlabChain.endAddr base (l ++ r) = SlabChain.endAddr (SlabChain.endAddr base l) r := by
  induction l generalizing base with
  | nil => rfl
  | cons seg rest ih => exact ih (base + BitVec.ofNat 64 seg.stride)

theorem SlabChain.eval_append (base : BitVec 64) (l r : List SlabSeg) :
    SlabChain.eval base (l ++ r) =
      (SlabChain.eval base l ⋆ SlabChain.eval (SlabChain.endAddr base l) r) := by
  induction l generalizing base with
  | nil =>
    funext m; apply propext
    simp [SlabChain.eval, SlabChain.endAddr, emp_sep]
  | cons seg rest ih =>
    simp only [List.cons_append, SlabChain.eval, SlabChain.endAddr]
    rw [ih (base + BitVec.ofNat 64 seg.stride), sep_assoc]

/-- Universal `regions_to_avail` theorem: collapses any contiguous chain of headers, typed arrays,
alignment pads, and trailing slack into `region base (SlabChain.totalBytes segs)`. -/
theorem SlabChain.to_region : ∀ (segs : List SlabSeg) (base : BitVec 64) {m : Mem 64},
    SlabChain.totalBytes segs ≤ 2 ^ 64 →
    SlabChain.eval base segs m → region base (SlabChain.totalBytes segs) m
  | [], base, _, _, hm => by
    rw [SlabChain.totalBytes, region_zero]; exact hm
  | seg :: rest, base, m, hfit, hm => by
    simp only [SlabChain.totalBytes] at hfit ⊢
    simp only [SlabChain.eval] at hm
    obtain ⟨m1, m2, hu, hd, h1, h2⟩ := hm
    have hr1 : region base seg.stride m1 := seg.toReg base m1 (by omega) h1
    have hr2 : region (base + BitVec.ofNat 64 seg.stride) (SlabChain.totalBytes rest) m2 :=
      SlabChain.to_region rest (base + BitVec.ofNat 64 seg.stride) (by omega) h2
    have hmerge := region_merge_eq (a := base) (n1 := seg.stride)
      (n2 := SlabChain.totalBytes rest) (n := seg.stride + SlabChain.totalBytes rest) rfl hfit
    rw [← hmerge]
    exact ⟨m1, m2, hu, hd, hr1, hr2⟩

/-- Collapse a `SlabChain` to `region base total` given `SlabChain.totalBytes segs = total`. -/
theorem SlabChain.to_region_eq {segs : List SlabSeg} {base : BitVec 64} {total : Nat}
    {m : Mem 64} (htot : SlabChain.totalBytes segs = total) (hfit : total ≤ 2 ^ 64)
    (hm : SlabChain.eval base segs m) : region base total m :=
  htot ▸ SlabChain.to_region segs base (htot ▸ hfit) hm

/-- Framed `SlabChain.to_region_eq`: collapses the slab inside
`(SlabChain.eval base segs ⋆ R) m`. -/
theorem SlabChain.to_region_frame {segs : List SlabSeg} {base : BitVec 64} {total : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} (htot : SlabChain.totalBytes segs = total)
    (hfit : total ≤ 2 ^ 64) (hm : (SlabChain.eval base segs ⋆ R) m) :
    (region base total ⋆ R) m :=
  sep_mono (fun _ h => SlabChain.to_region_eq htot hfit h) hm

/-! ## 4. Zero-`ecancel` Balanced `SepTree` ↔ `SlabChain` Bridge -/

/-- Pair each segment with its chained start address
(`base`, `base + s₀`, `(base + s₀) + s₁`, …). -/
def SlabChain.addrList (base : BitVec 64) : List SlabSeg → List (BitVec 64 × SlabSeg)
  | [] => []
  | seg :: rest => (base, seg) :: SlabChain.addrList (base + BitVec.ofNat 64 seg.stride) rest

theorem SlabChain.addrList_length (base : BitVec 64) (segs : List SlabSeg) :
    (SlabChain.addrList base segs).length = segs.length := by
  induction segs generalizing base with
  | nil => rfl
  | cons seg rest ih => simp [SlabChain.addrList, ih]

theorem SlabChain.addrList_append (base : BitVec 64) (l r : List SlabSeg) :
    SlabChain.addrList base (l ++ r) =
      SlabChain.addrList base l ++ SlabChain.addrList (SlabChain.endAddr base l) r := by
  induction l generalizing base with
  | nil => rfl
  | cons seg rest ih =>
    simp only [List.cons_append, SlabChain.addrList, SlabChain.endAddr]
    rw [ih]

theorem SlabChain.addrList_take (base : BitVec 64) (segs : List SlabSeg) (k : Nat) :
    (SlabChain.addrList base segs).take k = SlabChain.addrList base (segs.take k) := by
  induction segs generalizing base k with
  | nil => simp [SlabChain.addrList]
  | cons seg rest ih =>
    cases k with
    | zero => simp [SlabChain.addrList]
    | succ k => simp [SlabChain.addrList, ih]

theorem SlabChain.addrList_drop (base : BitVec 64) (segs : List SlabSeg) (k : Nat) :
    (SlabChain.addrList base segs).drop k =
      SlabChain.addrList (SlabChain.endAddr base (segs.take k)) (segs.drop k) := by
  induction segs generalizing base k with
  | nil => simp [SlabChain.addrList, SlabChain.endAddr]
  | cons seg rest ih =>
    cases k with
    | zero => simp [SlabChain.addrList, SlabChain.endAddr]
    | succ k => simp [SlabChain.addrList, SlabChain.endAddr, ih]

/-- Structurally recursive balanced `SepTree` from address-paired segments (`rfl`-reducible). -/
def SlabChain.balancedTreeAux : Nat → List (BitVec 64 × SlabSeg) → SepTree
  | 0, _ => .leaf emp
  | _, [] => .leaf emp
  | _, [(a, seg)] => .leaf (seg.pred a)
  | fuel + 1, xs =>
    let mid := xs.length / 2
    .node (SlabChain.balancedTreeAux fuel (xs.take mid))
          (SlabChain.balancedTreeAux fuel (xs.drop mid))

/-- Balanced `SepTree` over `SlabChain.addrList base segs`, matching `c0_slab_layout!` tree shape
definitionally (`rfl`). -/
def SlabChain.balancedTree (xs : List (BitVec 64 × SlabSeg)) : SepTree :=
  SlabChain.balancedTreeAux xs.length xs

private theorem sep_emp_r_slab (P : Mem 64 → Prop) : (P ⋆ emp) = P := by
  funext m; apply propext; simp [sep_emp]

/-- A balanced `SepTree` built from `SlabChain.addrList base segs` evaluates identically to
`SlabChain.eval base segs` without any AC-matching at call sites. -/
theorem SlabChain.balancedTreeAux_eval :
    ∀ (fuel : Nat) (base : BitVec 64) (segs : List SlabSeg),
      segs.length ≤ fuel →
      (SlabChain.balancedTreeAux fuel (SlabChain.addrList base segs)).eval =
        SlabChain.eval base segs
  | 0, base, segs, hle => by
    cases segs with
    | nil => rfl
    | cons _ _ => simp at hle
  | fuel + 1, base, segs, hle => by
    match segs with
    | [] => rfl
    | [seg] =>
      simp only [SlabChain.addrList, SlabChain.balancedTreeAux, SepTree.eval, SlabChain.eval]
      exact (sep_emp_r_slab (seg.pred base)).symm
    | s1 :: s2 :: rest =>
      let segs' := s1 :: s2 :: rest
      let mid := (SlabChain.addrList base segs').length / 2
      have hlen : (SlabChain.addrList base segs').length = segs'.length :=
        SlabChain.addrList_length base segs'
      have hmid_l : (segs'.take mid).length ≤ fuel := by
        simp only [List.length_take, mid, hlen, segs', List.length_cons] at hle ⊢; omega
      have hmid_r : (segs'.drop mid).length ≤ fuel := by
        simp only [List.length_drop, mid, hlen, segs', List.length_cons] at hle ⊢; omega
      have hsplit : segs' = segs'.take mid ++ segs'.drop mid :=
        (List.take_append_drop mid segs').symm
      change ((SlabChain.balancedTreeAux fuel ((SlabChain.addrList base segs').take mid)).eval ⋆
        (SlabChain.balancedTreeAux fuel ((SlabChain.addrList base segs').drop mid)).eval) =
        SlabChain.eval base segs'
      rw [SlabChain.addrList_take, SlabChain.addrList_drop,
        SlabChain.balancedTreeAux_eval fuel base (segs'.take mid) hmid_l,
        SlabChain.balancedTreeAux_eval fuel (SlabChain.endAddr base (segs'.take mid))
          (segs'.drop mid) hmid_r,
        ← SlabChain.eval_append, ← hsplit]

theorem SlabChain.balancedTree_eval (base : BitVec 64) (segs : List SlabSeg) :
    (SlabChain.balancedTree (SlabChain.addrList base segs)).eval = SlabChain.eval base segs := by
  unfold SlabChain.balancedTree
  rw [SlabChain.addrList_length]
  exact SlabChain.balancedTreeAux_eval segs.length base segs (Nat.le_refl _)

/-- Zero-`ecancel` `O(K)` collapse of any balanced `SepTree`-backed slab to
`region base (SlabChain.totalBytes segs)`. -/
theorem SlabChain.balancedTree_to_region (base : BitVec 64) (segs : List SlabSeg) {m : Mem 64}
    (hfit : SlabChain.totalBytes segs ≤ 2 ^ 64)
    (hm : (SlabChain.balancedTree (SlabChain.addrList base segs)).eval m) :
    region base (SlabChain.totalBytes segs) m := by
  rw [SlabChain.balancedTree_eval] at hm
  exact SlabChain.to_region segs base hfit hm

/-- Zero-`ecancel` `O(K)` collapse of any balanced `SepTree`-backed slab to `region base total`. -/
theorem SlabChain.balancedTree_to_region_eq {base : BitVec 64} {segs : List SlabSeg} {total : Nat}
    {m : Mem 64} (htot : SlabChain.totalBytes segs = total) (hfit : total ≤ 2 ^ 64)
    (hm : (SlabChain.balancedTree (SlabChain.addrList base segs)).eval m) :
    region base total m :=
  htot ▸ SlabChain.balancedTree_to_region base segs (htot ▸ hfit) hm

end LeanQbe.T
