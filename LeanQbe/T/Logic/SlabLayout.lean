module

public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.SlabChain

/-!
# Typed Slab Segments (`SlabSegKind`), Flat Tree Bridges, and `SepTree` Array/Byte Accessors

Provides `SlabSegKind` / `SlabVals` bidirectional `region ↔ Slab` conversion, flat
`Option Nat` offset bridges (`SlabChain.flatAddrs`, `SlabChain.Contiguous`), balanced
predicate trees (`SepTree.balancedPred`), and `SepTree` array/byte load-store lemmas.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-- Flat address tag (`none` = base `p`, `some off` = `p + BitVec.ofNat 64 off`). -/
@[expose] def SlabChain.flatAddr (base : BitVec 64) : Option Nat → BitVec 64
  | none => base
  | some off => base + BitVec.ofNat 64 off

/-- Address-tagged segment list using explicit `Option Nat` offsets from `base`. -/
@[expose] def SlabChain.flatAddrs (base : BitVec 64) :
    List (Option Nat × SlabSeg) → List (BitVec 64 × SlabSeg)
  | [] => []
  | (off?, seg) :: rest => (flatAddr base off?, seg) :: flatAddrs base rest

/-- Evaluation of an arbitrary address-tagged segment list as a separating conjunction. -/
@[expose] def SlabChain.evalAddrs : List (BitVec 64 × SlabSeg) → Mem 64 → Prop
  | [] => Std.ExtHashMap.emp
  | (a, seg) :: rest => seg.pred a ⋆ evalAddrs rest

/-- Contiguity invariant matching `SlabChain.eval` strides against flat `Option Nat` offsets. -/
@[expose] def SlabChain.Contiguous (cur : Nat) : List (Option Nat × SlabSeg) → Prop
  | [] => True
  | (none, seg) :: rest => cur = 0 ∧ Contiguous (cur + seg.stride) rest
  | (some off, seg) :: rest => off = cur ∧ Contiguous (cur + seg.stride) rest

/-- Typed segment descriptor supporting bidirectional `region ↔ Slab` conversion. -/
inductive SlabSegKind where
  | cell (b : Nat)
  | array (b len : Nat)
  | arrayPad (b len stride : Nat) (hle : b * len ≤ stride)
  | bytes (len : Nat)
  | pad (len : Nat)

/-- Byte stride of a typed segment kind. -/
@[expose] def SlabSegKind.stride : SlabSegKind → Nat
  | .cell b => b
  | .array b len => b * len
  | .arrayPad _ _ stride _ => stride
  | .bytes len => len
  | .pad len => len

/-- Total byte footprint of a list of segment kinds. -/
@[expose] def SlabSegKind.totalBytes : List SlabSegKind → Nat
  | [] => 0
  | k :: ks => k.stride + totalBytes ks

/-- Pure Lean value type carried by a segment kind. -/
@[expose] def SlabSegKind.Val : SlabSegKind → Type
  | .cell b => BitVec (8 * b)
  | .array b len => { xs : List (BitVec (8 * b)) // xs.length = len }
  | .arrayPad b len _ _ => { xs : List (BitVec (8 * b)) // xs.length = len }
  | .bytes len => { bs : List UInt8 // bs.length = len }
  | .pad _ => Unit

/-- Separating-logic memory predicate denoted by a typed segment kind at `a`. -/
@[expose] def SlabSegKind.pred : (k : SlabSegKind) → BitVec 64 → k.Val → Mem 64 → Prop
  | .cell b, a, v => LeanQbe.T.cell (t := .bits (8 * b)) a v
  | .array b _, a, xs => LeanQbe.T.array (t := .bits (8 * b)) a xs.1
  | .arrayPad b len stride _, a, xs =>
      LeanQbe.T.array (t := .bits (8 * b)) a xs.1 ⋆
        LeanQbe.T.region (a + BitVec.ofNat 64 (b * len)) (stride - b * len)
  | .bytes _, a, bs => LeanQbe.T.bytes a bs.1
  | .pad len, a, _ => LeanQbe.T.region a len

/-- Contiguity predicate for `SlabSegKind` layout descriptors. -/
@[expose] def SlabSegKind.Contiguous (cur : Nat) : List (Option Nat × SlabSegKind) → Prop
  | [] => True
  | (none, k) :: rest => cur = 0 ∧ Contiguous (cur + k.stride) rest
  | (some off, k) :: rest => off = cur ∧ Contiguous (cur + k.stride) rest

/-- Heterogeneous tuple of segment values indexed by `List SlabSegKind`. -/
inductive SlabVals : List SlabSegKind → Type where
  | nil : SlabVals []
  | cons : {k : SlabSegKind} → {ks : List SlabSegKind} → k.Val → SlabVals ks → SlabVals (k :: ks)

/-- Separating-conjunction predicate evaluated directly from `SlabSegKind` descriptors and `SlabVals`. -/
@[expose] def SlabSegKind.evalFlat (base : BitVec 64) :
    (xs : List (Option Nat × SlabSegKind)) → SlabVals (xs.map Prod.snd) → Mem 64 → Prop
  | [], .nil => Std.ExtHashMap.emp
  | (off?, k) :: rest, .cons v vs =>
      k.pred (SlabChain.flatAddr base off?) v ⋆ evalFlat base rest vs

/-- Lower `SlabSegKind` + `SlabVals` into a `SlabChain` `SepTree` via balanced tree splitting. -/
@[expose] def SlabSegKind.toAddrList (base : BitVec 64) :
    (xs : List (Option Nat × SlabSegKind)) → SlabVals (xs.map Prod.snd) →
      List (BitVec 64 × SlabSeg)
  | [], .nil => []
  | (off?, k) :: rest, .cons v vs =>
      (SlabChain.flatAddr base off?,
        { stride := k.stride
          pred := fun a => k.pred a v
          toReg := fun a m hfit hm => by
            cases k with
            | cell b =>
              dsimp only [SlabSegKind.stride, SlabSegKind.pred] at hm ⊢
              have hreg := bytes_to_region (a := a)
                (bs := Int.toBytes (Ty.bits (8 * b)).bytes
                  (BitVec.setWidth (8 * (Ty.bits (8 * b)).bytes) (toBits (.bits (8 * b)) v)).toInt)
                hm
              rw [Int.toBytes_length,
                show (Ty.bits (8 * b)).bytes = b by simp [Ty.bytes, Ty.size]; omega] at hreg
              exact hreg
            | array b len =>
              dsimp only [SlabSegKind.stride, SlabSegKind.pred] at hfit hm ⊢
              have hbt : (Ty.bits (8 * b)).bytes = b := by simp [Ty.bytes, Ty.size]; omega
              have hlen : (@bytesOf (.bits (8 * b)) v.1).length = b * len := by
                rw [bytesOf_length, v.2, hbt]
              exact ⟨@bytesOf (.bits (8 * b)) v.1, hlen,
                @array_eq_bytesOf (.bits (8 * b)) a v.1 (by rw [hbt, v.2]; exact hfit) m hm⟩
            | arrayPad b len stride hle =>
              dsimp only [SlabSegKind.stride, SlabSegKind.pred] at hfit hm ⊢
              have hbt : (Ty.bits (8 * b)).bytes = b := by simp [Ty.bytes, Ty.size]; omega
              have hreg := sep_mono2 (fun m1 hm1 => show region a (b * len) m1 from by
                have hlen : (@bytesOf (.bits (8 * b)) v.1).length = b * len := by
                  rw [bytesOf_length, v.2, hbt]
                exact ⟨@bytesOf (.bits (8 * b)) v.1, hlen,
                  @array_eq_bytesOf (.bits (8 * b)) a v.1 (by rw [hbt, v.2]; omega) m1 hm1⟩)
                (fun _ h => h) m hm
              rwa [show stride = b * len + (stride - b * len) by omega, region_split (by omega)]
            | bytes len =>
              dsimp only [SlabSegKind.stride, SlabSegKind.pred] at hm ⊢
              rw [← v.2]; exact bytes_to_region hm
            | pad len => exact hm }) :: toAddrList base rest vs

/-- Flatten a `SepTree` into its left-to-right list of leaf memory predicates. -/
@[expose] def SepTree.leaves : SepTree → List (Mem 64 → Prop)
  | .leaf P => [P]
  | .node l r => l.leaves ++ r.leaves

/-- Predicate-only balanced `SepTree` matching `SlabChain.balancedTree` split order structurally. -/
@[expose] def SepTree.balancedPredAux : Nat → List (Mem 64 → Prop) → SepTree
  | 0, _ => .leaf Std.ExtHashMap.emp
  | _, [] => .leaf Std.ExtHashMap.emp
  | _, [P] => .leaf P
  | fuel + 1, ps =>
    let mid := ps.length / 2
    .node (balancedPredAux fuel (ps.take mid)) (balancedPredAux fuel (ps.drop mid))

/-- Balanced `SepTree` built directly from a list of leaf memory predicates. -/
@[expose] def SepTree.balancedPred (ps : List (Mem 64 → Prop)) : SepTree :=
  SepTree.balancedPredAux ps.length ps

/-- Right-associated separating conjunction of a list of memory predicates. -/
@[expose] def SlabChain.evalPreds : List (Mem 64 → Prop) → Mem 64 → Prop
  | [] => Std.ExtHashMap.emp
  | P :: rest => P ⋆ evalPreds rest

/-- Direct list of leaf memory predicates for `SlabSegKind` + `SlabVals`. -/
@[expose] def SlabSegKind.toPredList (base : BitVec 64) :
    (xs : List (Option Nat × SlabSegKind)) → SlabVals (xs.map Prod.snd) →
      List (Mem 64 → Prop)
  | [], .nil => []
  | (off?, k) :: rest, .cons v vs =>
      k.pred (SlabChain.flatAddr base off?) v :: toPredList base rest vs

/-- Structural total byte count of a segment list (without `List.brecOn`, friendly to `dsimp`). -/
@[expose] def SlabChain.totalBytesFlat : List SlabSeg → Nat
  | [] => 0
  | s :: rest => s.stride + totalBytesFlat rest

end LeanQbe.T

end

public section

namespace LeanQbe.T

open Std Std.ExtHashMap

private theorem int_toBytes_mod (n : Nat) (x y : Int)
    (h : x % ((2 : Int) ^ (8 * n)) = y % ((2 : Int) ^ (8 * n))) :
    Int.toBytes n x = Int.toBytes n y := by
  induction n generalizing x y with
  | zero => simp [Int.toBytes]
  | succ n ih =>
    simp only [Int.toBytes, Int.take]
    have hpow : (2 : Int) ^ (8 * (n + 1)) = ((2 : Int) ^ 8) * (2 : Int) ^ (8 * n) := by
      have : 8 * (n + 1) = 8 + 8 * n := by omega
      rw [this, Int.pow_add]
    have hpow2 : (2 : Int) ^ (8 * (n + 1)) = (2 : Int) ^ (8 * n) * ((2 : Int) ^ 8) := by
      rw [hpow, Int.mul_comm]
    have hmod8 : x % ((2 : Int) ^ 8) = y % ((2 : Int) ^ 8) := by
      have aux : ∀ z : Int, z % ((2 : Int) ^ 8) =
          (z % ((2 : Int) ^ (8 * (n + 1)))) % ((2 : Int) ^ 8) := by
        intro z; rw [hpow2]
        exact (Int.emod_emod_of_dvd z ⟨(2 : Int) ^ (8 * n), Int.mul_comm _ _⟩).symm
      rw [aux x, aux y, h]
    have hdiv : (x / (256 : Int)) % ((2 : Int) ^ (8 * n)) =
        (y / (256 : Int)) % ((2 : Int) ^ (8 * n)) := by
      have hm : x % (256 * (2 : Int) ^ (8 * n)) =
          y % (256 * (2 : Int) ^ (8 * n)) := by
        have h256 : ((2 : Int) ^ 8) = 256 := rfl
        rw [hpow, h256] at h
        exact h
      have hdiv256 : (x - y) % (256 * (2 : Int) ^ (8 * n)) = 0 := by
        rw [Int.sub_emod, hm, Int.sub_self, Int.zero_emod]
      obtain ⟨q, hq⟩ := Int.dvd_of_emod_eq_zero hdiv256
      have ex := Int.emod_add_mul_ediv x 256
      have ey := Int.emod_add_mul_ediv y 256
      have hd : x % (256 : Int) = y % (256 : Int) := by
        simpa [show ((2 : Int) ^ 8) = 256 by rfl] using hmod8
      let m2 := (2 : Int) ^ (8 * n) * q
      have hsub : (256 : Int) * (x / 256 - y / 256) = 256 * m2 := by
        have hq' : x - y = 256 * m2 := by simpa [m2, Int.mul_assoc] using hq
        omega
      have hsub2 : x / 256 - y / 256 = m2 := Int.eq_of_mul_eq_mul_left (by omega) hsub
      have hadd : x / 256 = y / 256 + m2 := by omega
      have hadd' : x / 256 = y / 256 + (2 : Int) ^ (8 * n) * q := hadd
      rw [hadd', Int.add_mul_emod_self_left]
    rw [hmod8, ih _ _ hdiv]

/-- Convert a raw `b`-byte `region` into an arbitrary `(8 * b)`-bit `cell`. -/
theorem region_to_cell_bits {b : Nat}
    {a : BitVec 64} {m : Mem 64} (hm : region a b m) :
    ∃ v : BitVec (8 * b), cell (t := .bits (8 * b)) a v m := by
  obtain ⟨bs, hlen, rfl⟩ := hm
  refine ⟨BitVec.ofNat (8 * b) (Int.ofBytes bs).toNat, ?_⟩
  simp only [cell, toBits]
  have hbytes : (Ty.bits (8 * b)).bytes = b := by simp [Ty.bytes, Ty.size]; omega
  rw [hbytes]
  have hge : 0 ≤ Int.ofBytes bs := Int.ofBytes_ge_zero bs
  have hmod : (BitVec.setWidth (8 * b) (BitVec.ofNat (8 * b) (Int.ofBytes bs).toNat)).toInt %
        ((2 : Int) ^ (8 * b)) = Int.ofBytes bs % ((2 : Int) ^ (8 * b)) := by
    rw [BitVec.toInt_setWidth, BitVec.toNat_ofNat]
    have hcoe : ((2 : Int) ^ (8 * b)) = ((2 ^ (8 * b) : Nat) : Int) := by simp [Int.natCast_pow]
    rw [hcoe, Int.bmod_emod, Int.natCast_emod, Int.toNat_of_nonneg hge, Int.emod_emod]
  rw [int_toBytes_mod b _ _ hmod, ← hlen, Int.toBytes_ofBytes_all]

/-- Convert an arbitrary `(8 * b)`-bit `cell` into a `b`-byte `region`. -/
theorem cell_to_region {b : Nat}
    {a : BitVec 64} {v : BitVec (8 * b)} {m : Mem 64}
    (hm : cell (t := .bits (8 * b)) a v m) : region a b m := by
  have hreg := bytes_to_region (a := a)
    (bs := Int.toBytes (Ty.bits (8 * b)).bytes
      (BitVec.setWidth (8 * (Ty.bits (8 * b)).bytes) (toBits (.bits (8 * b)) v)).toInt)
    hm
  rw [Int.toBytes_length,
    show (Ty.bits (8 * b)).bytes = b by simp [Ty.bytes, Ty.size]; omega] at hreg
  exact hreg

/-- Convert a `b * k`-byte `region` into an `array` of `k` `(8 * b)`-bit values. -/
theorem region_to_array_bits {b : Nat} (a : BitVec 64) (k : Nat)
    (hk : b * k ≤ 2 ^ 64) {m : Mem 64} (hm : region a (b * k) m) :
    ∃ xs : List (BitVec (8 * b)), xs.length = k ∧ array (t := .bits (8 * b)) a xs m := by
  induction k generalizing a m with
  | zero =>
    obtain ⟨bs, hlen, rfl⟩ := hm
    have hnil : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst hnil
    exact ⟨[], rfl, by simp only [array]; exact (congrFun (eq_nil_At a) ([].At a)).mpr rfl⟩
  | succ k ih =>
    have hmul : b * (k + 1) = b + b * k := by rw [Nat.mul_succ, Nat.add_comm]
    rw [hmul, region_split (by omega)] at hm
    have hsep := sep_mono2
      (fun _ hm1 => region_to_cell_bits hm1)
      (fun _ hm2 => show ∃ p : { xs : List (BitVec (8 * b)) // xs.length = k },
          array (t := .bits (8 * b)) (a + BitVec.ofNat 64 b) p.1 _ by
        obtain ⟨xs, hlen, hxs⟩ := ih (a + BitVec.ofNat 64 b) (by omega) hm2
        exact ⟨⟨xs, hlen⟩, hxs⟩)
      m hm
    rw [sep_ex_l] at hsep; obtain ⟨v, hsep⟩ := hsep
    rw [sep_ex_r] at hsep; obtain ⟨⟨xs, hlen⟩, hsep⟩ := hsep
    have hbytes : (Ty.bits (8 * b)).bytes = b := by simp [Ty.bytes, Ty.size]; omega
    refine ⟨v :: xs, by simp [hlen], ?_⟩
    rwa [array_cons, hbytes]

private theorem evalAddrs_append (xs ys : List (BitVec 64 × SlabSeg)) :
    SlabChain.evalAddrs (xs ++ ys) = SlabChain.evalAddrs xs ⋆ SlabChain.evalAddrs ys := by
  induction xs with
  | nil => simp [SlabChain.evalAddrs, emp_sep]
  | cons x xs ih =>
    rcases x with ⟨a, seg⟩
    simp only [List.cons_append, SlabChain.evalAddrs, ih, sep_assoc]

private theorem balancedTreeAux_evalAddrs (fuel : Nat) (xs : List (BitVec 64 × SlabSeg))
    (hlen : xs.length ≤ fuel) :
    (SlabChain.balancedTreeAux fuel xs).eval = SlabChain.evalAddrs xs := by
  induction fuel generalizing xs with
  | zero =>
    have hnil : xs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
    subst hnil; rfl
  | succ fuel ih =>
    match xs with
    | [] => rfl
    | [(a, seg)] =>
      simp only [SlabChain.balancedTreeAux, SepTree.eval, SlabChain.evalAddrs, sep_emp]
    | x1 :: x2 :: rest =>
      have hlen2 : (x1 :: x2 :: rest).length ≥ 2 := by simp
      have hmid : (x1 :: x2 :: rest).length / 2 < (x1 :: x2 :: rest).length :=
        Nat.div_lt_self (by omega) (by decide)
      have hdrop : (x1 :: x2 :: rest).length - (x1 :: x2 :: rest).length / 2 <
          (x1 :: x2 :: rest).length := by omega
      have h1 : (List.take ((x1 :: x2 :: rest).length / 2) (x1 :: x2 :: rest)).length ≤ fuel := by
        rw [List.length_take]; omega
      have h2 : (List.drop ((x1 :: x2 :: rest).length / 2) (x1 :: x2 :: rest)).length ≤ fuel := by
        rw [List.length_drop]; omega
      simp only [SlabChain.balancedTreeAux, SepTree.eval]
      rw [ih _ h1, ih _ h2, ← evalAddrs_append, List.take_append_drop]

/-- Evaluating `SlabChain.balancedTree` on arbitrary `(addr, seg)` pairs equals `evalAddrs`. -/
theorem SlabChain.balancedTree_evalAddrs (xs : List (BitVec 64 × SlabSeg)) :
    (SlabChain.balancedTree xs).eval = SlabChain.evalAddrs xs :=
  balancedTreeAux_evalAddrs xs.length xs (Nat.le_refl _)

private theorem evalAddrs_flatAddrs_aux (base : BitVec 64) (cur : Nat)
    (xs : List (Option Nat × SlabSeg)) (hcont : SlabChain.Contiguous cur xs) :
    SlabChain.evalAddrs (SlabChain.flatAddrs base xs) =
      SlabChain.eval (base + BitVec.ofNat 64 cur) (xs.map Prod.snd) := by
  induction xs generalizing cur with
  | nil => simp [SlabChain.flatAddrs, SlabChain.evalAddrs, SlabChain.eval]
  | cons x rest ih =>
    rcases x with ⟨off?, seg⟩
    cases off? with
    | none =>
      rcases hcont with ⟨hoff, hrest⟩
      subst hoff
      simp only [SlabChain.flatAddrs, SlabChain.flatAddr, SlabChain.evalAddrs, List.map_cons,
        SlabChain.eval]
      have hz : base + BitVec.ofNat 64 0 = base := BitVec.add_zero base
      rw [hz, ih seg.stride (by simpa [Nat.zero_add] using hrest)]
    | some off =>
      rcases hcont with ⟨hoff, hrest⟩
      simp only [SlabChain.flatAddrs, SlabChain.flatAddr, SlabChain.evalAddrs, List.map_cons,
        SlabChain.eval]
      rw [hoff, ih (cur + seg.stride) hrest, BitVec.ofNat_add, ← BitVec.add_assoc]

/-- Evaluating flat `balancedTree` reduces to `SlabChain.eval base`. -/
theorem SlabChain.flatTree_eval (base : BitVec 64) (xs : List (Option Nat × SlabSeg))
    (hcont : SlabChain.Contiguous 0 xs) :
    (SlabChain.balancedTree (SlabChain.flatAddrs base xs)).eval =
      SlabChain.eval base (xs.map Prod.snd) := by
  rw [SlabChain.balancedTree_evalAddrs, evalAddrs_flatAddrs_aux base 0 xs hcont, BitVec.add_zero]

/-- Frame-polymorphic conversion from flat balanced `SepTree` to `region`. -/
theorem SlabChain.flatTree_to_region_frame_eq {base : BitVec 64}
    {xs : List (Option Nat × SlabSeg)} {total : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcont : SlabChain.Contiguous 0 xs)
    (htot : SlabChain.totalBytes (xs.map Prod.snd) = total)
    (hfit : total ≤ 2 ^ 64)
    (hm : ((SlabChain.balancedTree (SlabChain.flatAddrs base xs)).eval ⋆ R) m) :
    (region base total ⋆ R) m := by
  rw [SlabChain.flatTree_eval base xs hcont] at hm
  exact SlabChain.to_region_frame htot hfit hm

/-- Non-framed conversion from flat balanced `SepTree` to `region`. -/
theorem SlabChain.flatTree_to_region_eq {base : BitVec 64}
    {xs : List (Option Nat × SlabSeg)} {total : Nat} {m : Mem 64}
    (hcont : SlabChain.Contiguous 0 xs)
    (htot : SlabChain.totalBytes (xs.map Prod.snd) = total)
    (hfit : total ≤ 2 ^ 64)
    (hm : (SlabChain.balancedTree (SlabChain.flatAddrs base xs)).eval m) :
    region base total m := by
  rw [SlabChain.flatTree_eval base xs hcont] at hm
  exact SlabChain.to_region_eq htot hfit hm

/-- `SlabChain.to_region_frame` for `balancedTree (addrList base segs)`. -/
theorem SlabChain.balancedTree_to_region_frame_eq {base : BitVec 64}
    {segs : List SlabSeg} {total : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (htot : SlabChain.totalBytes segs = total)
    (hfit : total ≤ 2 ^ 64)
    (hm : ((SlabChain.balancedTree (SlabChain.addrList base segs)).eval ⋆ R) m) :
    (region base total ⋆ R) m := by
  rw [SlabChain.balancedTree_eval] at hm
  exact SlabChain.to_region_frame htot hfit hm

private theorem evalPreds_append (xs ys : List (Mem 64 → Prop)) :
    SlabChain.evalPreds (xs ++ ys) = SlabChain.evalPreds xs ⋆ SlabChain.evalPreds ys := by
  induction xs with
  | nil => simp [SlabChain.evalPreds, emp_sep]
  | cons P xs ih => simp only [List.cons_append, SlabChain.evalPreds, ih, sep_assoc]

private theorem balancedPredAux_eval (fuel : Nat) (ps : List (Mem 64 → Prop))
    (hlen : ps.length ≤ fuel) :
    (SepTree.balancedPredAux fuel ps).eval = SlabChain.evalPreds ps := by
  induction fuel generalizing ps with
  | zero =>
    have hnil : ps = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
    subst hnil; rfl
  | succ fuel ih =>
    match ps with
    | [] => rfl
    | [P] => simp only [SepTree.balancedPredAux, SepTree.eval, SlabChain.evalPreds, sep_emp]
    | p1 :: p2 :: rest =>
      have hlen2 : (p1 :: p2 :: rest).length ≥ 2 := by simp
      have hmid : (p1 :: p2 :: rest).length / 2 < (p1 :: p2 :: rest).length :=
        Nat.div_lt_self (by omega) (by decide)
      have h1 : (List.take ((p1 :: p2 :: rest).length / 2) (p1 :: p2 :: rest)).length ≤ fuel := by
        rw [List.length_take]; omega
      have h2 : (List.drop ((p1 :: p2 :: rest).length / 2) (p1 :: p2 :: rest)).length ≤ fuel := by
        rw [List.length_drop]; omega
      simp only [SepTree.balancedPredAux, SepTree.eval]
      rw [ih _ h1, ih _ h2, ← evalPreds_append, List.take_append_drop]

/-- Evaluating any `SepTree` equals `SlabChain.evalPreds t.leaves`. -/
theorem SepTree.eval_eq_evalPreds (t : SepTree) :
    t.eval = SlabChain.evalPreds t.leaves := by
  induction t with
  | leaf P => simp [SepTree.eval, SepTree.leaves, SlabChain.evalPreds, sep_emp]
  | node l r ihl ihr => simp [SepTree.eval, SepTree.leaves, evalPreds_append, ihl, ihr]

/-- Evaluating `SepTree.balancedPred ps` equals `SlabChain.evalPreds ps`. -/
theorem SepTree.balancedPred_eval (ps : List (Mem 64 → Prop)) :
    (SepTree.balancedPred ps).eval = SlabChain.evalPreds ps :=
  balancedPredAux_eval ps.length ps (Nat.le_refl _)

private theorem evalPreds_flatAddrs (base : BitVec 64) (xs : List (Option Nat × SlabSeg)) :
    SlabChain.evalPreds ((SlabChain.flatAddrs base xs).map fun p => p.2.pred p.1) =
      SlabChain.evalAddrs (SlabChain.flatAddrs base xs) := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    rcases x with ⟨off?, seg⟩
    simp only [SlabChain.flatAddrs, List.map_cons, SlabChain.evalPreds, SlabChain.evalAddrs, ih]

/-- `SlabChain.totalBytesFlat` equals `SlabChain.totalBytes`. -/
theorem SlabChain.totalBytesFlat_eq (segs : List SlabSeg) :
    SlabChain.totalBytesFlat segs = SlabChain.totalBytes segs := by
  induction segs with
  | nil => simp [SlabChain.totalBytesFlat, SlabChain.totalBytes]
  | cons s rest ih => simp [SlabChain.totalBytesFlat, SlabChain.totalBytes, ih]

/-- Non-framed conversion from `SlabChain.evalPreds` on flat address-tagged segments to `region`. -/
theorem SepTree.evalPreds_to_region_eq {base : BitVec 64}
    {xs : List (Option Nat × SlabSeg)} {total : Nat} {m : Mem 64}
    (hcont : SlabChain.Contiguous 0 xs)
    (htot : SlabChain.totalBytesFlat (xs.map Prod.snd) = total)
    (hfit : total ≤ 2 ^ 64)
    (hm : SlabChain.evalPreds ((SlabChain.flatAddrs base xs).map fun p => p.2.pred p.1) m) :
    region base total m := by
  rw [evalPreds_flatAddrs, evalAddrs_flatAddrs_aux base 0 xs hcont, BitVec.add_zero] at hm
  exact SlabChain.to_region_eq ((SlabChain.totalBytesFlat_eq _).symm.trans htot) hfit hm

/-- Frame-polymorphic conversion from `SlabChain.evalPreds` on flat segments to `region`. -/
theorem SepTree.evalPreds_to_region_frame_eq {base : BitVec 64}
    {xs : List (Option Nat × SlabSeg)} {total : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcont : SlabChain.Contiguous 0 xs)
    (htot : SlabChain.totalBytesFlat (xs.map Prod.snd) = total)
    (hfit : total ≤ 2 ^ 64)
    (hm : (SlabChain.evalPreds ((SlabChain.flatAddrs base xs).map fun p => p.2.pred p.1) ⋆ R) m) :
    (region base total ⋆ R) m := by
  rw [evalPreds_flatAddrs, evalAddrs_flatAddrs_aux base 0 xs hcont, BitVec.add_zero] at hm
  exact SlabChain.to_region_frame ((SlabChain.totalBytesFlat_eq _).symm.trans htot) hfit hm

/-- Non-framed conversion from structural `SepTree.balancedPred` to `region`. -/
theorem SepTree.balancedPred_to_region_eq {base : BitVec 64}
    {xs : List (Option Nat × SlabSeg)} {total : Nat} {m : Mem 64}
    (hcont : SlabChain.Contiguous 0 xs)
    (htot : SlabChain.totalBytesFlat (xs.map Prod.snd) = total)
    (hfit : total ≤ 2 ^ 64)
    (hm : (SepTree.balancedPred ((SlabChain.flatAddrs base xs).map fun p => p.2.pred p.1)).eval m) :
    region base total m := by
  rw [SepTree.balancedPred_eval, evalPreds_flatAddrs, evalAddrs_flatAddrs_aux base 0 xs hcont,
    BitVec.add_zero] at hm
  exact SlabChain.to_region_eq ((SlabChain.totalBytesFlat_eq _).symm.trans htot) hfit hm

/-- Frame-polymorphic conversion from structural `SepTree.balancedPred` to `region`. -/
theorem SepTree.balancedPred_to_region_frame_eq {base : BitVec 64}
    {xs : List (Option Nat × SlabSeg)} {total : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcont : SlabChain.Contiguous 0 xs)
    (htot : SlabChain.totalBytesFlat (xs.map Prod.snd) = total)
    (hfit : total ≤ 2 ^ 64)
    (hm : ((SepTree.balancedPred
      ((SlabChain.flatAddrs base xs).map fun p => p.2.pred p.1)).eval ⋆ R) m) :
    (region base total ⋆ R) m := by
  rw [SepTree.balancedPred_eval, evalPreds_flatAddrs, evalAddrs_flatAddrs_aux base 0 xs hcont,
    BitVec.add_zero] at hm
  exact SlabChain.to_region_frame ((SlabChain.totalBytesFlat_eq _).symm.trans htot) hfit hm

private theorem slabSegKind_region_to_val (k : SlabSegKind) (a : BitVec 64)
    (hfit : k.stride ≤ 2 ^ 64) {m : Mem 64} (hm : region a k.stride m) :
    ∃ v : k.Val, k.pred a v m := by
  cases k with
  | cell b =>
    dsimp only [SlabSegKind.stride] at hfit hm
    exact region_to_cell_bits hm
  | array b len =>
    dsimp only [SlabSegKind.stride] at hfit hm
    obtain ⟨xs, hlen, hxs⟩ := region_to_array_bits a len hfit hm
    exact ⟨⟨xs, hlen⟩, hxs⟩
  | arrayPad b len stride hle =>
    dsimp only [SlabSegKind.stride] at hfit hm
    rw [show stride = b * len + (stride - b * len) by omega, region_split (by omega)] at hm
    have hsep := sep_mono2
      (fun _ hm1 => show ∃ p : { xs : List (BitVec (8 * b)) // xs.length = len },
          array (t := .bits (8 * b)) a p.1 _ by
        obtain ⟨xs, hlen, hxs⟩ := region_to_array_bits a len (by omega) hm1
        exact ⟨⟨xs, hlen⟩, hxs⟩)
      (fun _ h => h) m hm
    rw [sep_ex_l] at hsep
    exact hsep
  | bytes len =>
    obtain ⟨bs, hlen, hmem⟩ := hm
    exact ⟨⟨bs, hlen⟩, hmem.symm⟩
  | pad len => exact ⟨(), hm⟩

private theorem slabSegKind_of_region_aux (base : BitVec 64) (cur : Nat)
    (xs : List (Option Nat × SlabSegKind))
    (hcont : SlabSegKind.Contiguous cur xs)
    (hfit : SlabSegKind.totalBytes (xs.map Prod.snd) ≤ 2 ^ 64)
    {m : Mem 64}
    (hm : region (base + BitVec.ofNat 64 cur) (SlabSegKind.totalBytes (xs.map Prod.snd)) m) :
    ∃ vs : SlabVals (xs.map Prod.snd), SlabSegKind.evalFlat base xs vs m := by
  induction xs generalizing cur m with
  | nil =>
    simp only [List.map_nil, SlabSegKind.totalBytes] at hm
    obtain ⟨bs, hlen, rfl⟩ := hm
    have hnil : bs = [] := List.eq_nil_of_length_eq_zero hlen
    subst hnil
    exact ⟨.nil, (congrFun (eq_nil_At (base + BitVec.ofNat 64 cur)) ([].At _)).mpr rfl⟩
  | cons x rest ih =>
    rcases x with ⟨off?, k⟩
    simp only [List.map_cons, SlabSegKind.totalBytes] at hfit hm
    rw [region_split hfit] at hm
    rw [BitVec.add_assoc, ← BitVec.ofNat_add] at hm
    cases off? with
    | none =>
      rcases hcont with ⟨hoff, hrest⟩
      subst hoff
      have hz : base + BitVec.ofNat 64 0 = base := BitVec.add_zero base
      rw [hz, show 0 + k.stride = k.stride from Nat.zero_add _] at hm
      have hsep := sep_mono2
        (fun _ hm1 => slabSegKind_region_to_val k base (by omega) hm1)
        (fun _ hm2 => ih k.stride (by simpa [Nat.zero_add] using hrest) (by omega) hm2)
        m hm
      rw [sep_ex_l] at hsep; obtain ⟨v, hsep⟩ := hsep
      rw [sep_ex_r] at hsep; obtain ⟨vs, hsep⟩ := hsep
      exact ⟨.cons v vs, hsep⟩
    | some off =>
      rcases hcont with ⟨hoff, hrest⟩
      have hsep := sep_mono2
        (fun _ hm1 => slabSegKind_region_to_val k (base + BitVec.ofNat 64 cur) (by omega) hm1)
        (fun _ hm2 => ih (cur + k.stride) hrest (by omega) hm2)
        m hm
      rw [sep_ex_l] at hsep; obtain ⟨v, hsep⟩ := hsep
      rw [sep_ex_r] at hsep; obtain ⟨vs, hsep⟩ := hsep
      refine ⟨.cons v vs, ?_⟩
      simpa [SlabSegKind.evalFlat, SlabChain.flatAddr, hoff] using hsep

/-- Decode a flat contiguous `region` into heterogeneous `SlabVals` and `SlabSegKind.evalFlat`. -/
theorem SlabSegKind.of_region_flat {base : BitVec 64} {xs : List (Option Nat × SlabSegKind)}
    {total : Nat} {m : Mem 64}
    (hcont : SlabSegKind.Contiguous 0 xs)
    (htot : SlabSegKind.totalBytes (xs.map Prod.snd) = total)
    (hfit : total ≤ 2 ^ 64)
    (hm : region base total m) :
    ∃ vs : SlabVals (xs.map Prod.snd), SlabSegKind.evalFlat base xs vs m := by
  subst htot
  have hm' : region (base + BitVec.ofNat 64 0) (SlabSegKind.totalBytes (xs.map Prod.snd)) m := by
    rwa [BitVec.add_zero]
  exact slabSegKind_of_region_aux base 0 xs hcont hfit hm'

/-- Frame-polymorphic decode from `(region base total ⋆ R) m` into `SlabVals` and `SlabSegKind.evalFlat`. -/
theorem SlabSegKind.of_region_flat_frame {base : BitVec 64} {xs : List (Option Nat × SlabSegKind)}
    {total : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    (hcont : SlabSegKind.Contiguous 0 xs)
    (htot : SlabSegKind.totalBytes (xs.map Prod.snd) = total)
    (hfit : total ≤ 2 ^ 64)
    (hm : (region base total ⋆ R) m) :
    ∃ vs : SlabVals (xs.map Prod.snd), (SlabSegKind.evalFlat base xs vs ⋆ R) m := by
  have hsep := sep_mono2
    (fun _ hm1 => SlabSegKind.of_region_flat hcont htot hfit hm1) (fun _ h => h) m hm
  rwa [sep_ex_l] at hsep

private theorem evalPreds_toPredList (base : BitVec 64)
    (xs : List (Option Nat × SlabSegKind)) (vs : SlabVals (xs.map Prod.snd)) :
    SlabChain.evalPreds (SlabSegKind.toPredList base xs vs) = SlabSegKind.evalFlat base xs vs := by
  induction xs with
  | nil => cases vs; rfl
  | cons x rest ih =>
    rcases x with ⟨off?, k⟩
    cases vs with
    | cons v vs' =>
      simp only [SlabSegKind.toPredList, SlabChain.evalPreds, SlabSegKind.evalFlat, ih vs']

/-- Converting `SlabSegKind.evalFlat` to `SlabChain.evalPreds (SlabSegKind.toPredList ...)`. -/
theorem SlabSegKind.evalFlat_eq_evalPreds (base : BitVec 64)
    (xs : List (Option Nat × SlabSegKind)) (vs : SlabVals (xs.map Prod.snd)) :
    SlabSegKind.evalFlat base xs vs = SlabChain.evalPreds (SlabSegKind.toPredList base xs vs) := by
  rw [← evalPreds_toPredList]

/-- Evaluating structural `SepTree.balancedPred (SlabSegKind.toPredList ...)` equals `evalFlat`. -/
theorem SlabSegKind.balancedTree_eval (base : BitVec 64)
    (xs : List (Option Nat × SlabSegKind)) (vs : SlabVals (xs.map Prod.snd)) :
    (SepTree.balancedPred (SlabSegKind.toPredList base xs vs)).eval =
      SlabSegKind.evalFlat base xs vs := by
  rw [SepTree.balancedPred_eval, evalPreds_toPredList]

/-- `BitVec.toNat` of `BitVec.setWidth 64` on a `BitVec 32` index. -/
theorem sepTree_toNat_setWidth64 (i : BitVec 32) : (i.setWidth 64).toNat = i.toNat := by
  simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := i.isLt; omega : i.toNat < 2 ^ 64)]

/-- `SepTree` array load using an arbitrary `BitVec 64` element index and stride equality. -/
theorem sepTree_arr_get_bv_at {ty : Ty} {t : SepTree} {p : List Bool} {arrBase : BitVec 64}
    {xs : List (Val ty)} {R : Mem 64 → Prop} {m : Mem 64}
    (hget : t.get p = array arrBase xs) (hb : ty.bytes ≤ 2 ^ 64)
    {w : BitVec 64} (hw : w = BitVec.ofNat 64 ty.bytes)
    {i : BitVec 64} (hi : i.toNat < xs.length) (hm : (t.eval ⋆ R) m) :
    loadVal m ty (arrBase + i * w) = some xs[i.toNat] := by
  subst hw
  have h := sepTree_arr_get hget hb hi hm
  simpa [BitVec.ofNat_mul, BitVec.ofNat_toNat, BitVec.mul_comm] using h

/-- `SepTree` array store using an arbitrary `BitVec 64` element index and stride equality. -/
theorem sepTree_arr_put_bv_at {ty : Ty} {t : SepTree} {p : List Bool} {arrBase : BitVec 64}
    {xs : List (Val ty)} {M' R : Mem 64 → Prop} {m : Mem 64}
    (hget : t.get p = array arrBase xs) (hb : ty.bytes ≤ 2 ^ 64)
    {w : BitVec 64} (hw : w = BitVec.ofNat 64 ty.bytes)
    (v : Val ty) {i : BitVec 64} (hi : i.toNat < xs.length)
    (heq : (t.set p (array arrBase (xs.set i.toNat v))).eval = M')
    (hm : (t.eval ⋆ R) m) :
    storeOk m ty (arrBase + i * w) ∧ (M' ⋆ R) (storeMem m ty (arrBase + i * w) v) := by
  subst hw
  have h := sepTree_arr_put hget hb v hi heq hm
  simpa [BitVec.ofNat_mul, BitVec.ofNat_toNat, BitVec.mul_comm] using h

/-- `SepTree` padded-array load using an arbitrary `BitVec 64` element index. -/
theorem sepTree_arr_pad_get_bv_at {ty : Ty} {t : SepTree} {p : List Bool} {arrBase : BitVec 64}
    {xs : List (Val ty)} {pad R : Mem 64 → Prop} {m : Mem 64}
    (hget : t.get p = array arrBase xs ⋆ pad) (hb : ty.bytes ≤ 2 ^ 64)
    {w : BitVec 64} (hw : w = BitVec.ofNat 64 ty.bytes)
    {i : BitVec 64} (hi : i.toNat < xs.length) (hm : (t.eval ⋆ R) m) :
    loadVal m ty (arrBase + i * w) = some xs[i.toNat] := by
  subst hw
  have h := sepTree_arr_pad_get hget hb hi hm
  simpa [BitVec.ofNat_mul, BitVec.ofNat_toNat, BitVec.mul_comm] using h

/-- `SepTree` padded-array store using an arbitrary `BitVec 64` element index. -/
theorem sepTree_arr_pad_put_bv_at {ty : Ty} {t : SepTree} {p : List Bool} {arrBase : BitVec 64}
    {xs : List (Val ty)} {pad M' R : Mem 64 → Prop} {m : Mem 64}
    (hget : t.get p = array arrBase xs ⋆ pad) (hb : ty.bytes ≤ 2 ^ 64)
    {w : BitVec 64} (hw : w = BitVec.ofNat 64 ty.bytes)
    (v : Val ty) {i : BitVec 64} (hi : i.toNat < xs.length)
    (heq : (t.set p (array arrBase (xs.set i.toNat v) ⋆ pad)).eval = M')
    (hm : (t.eval ⋆ R) m) :
    storeOk m ty (arrBase + i * w) ∧ (M' ⋆ R) (storeMem m ty (arrBase + i * w) v) := by
  subst hw
  have h := sepTree_arr_pad_put hget hb v hi heq hm
  simpa [BitVec.ofNat_mul, BitVec.ofNat_toNat, BitVec.mul_comm] using h

/-- `SepTree` byte-array (`i8`) load via `array arrBase (xs : List (BitVec 8))` and `Nat` index. -/
theorem sepTree_arr_get_byte_nat {t : SepTree} {p : List Bool} {arrBase : BitVec 64}
    {xs : List (BitVec 8)} {R : Mem 64 → Prop} {m : Mem 64}
    (hget : t.get p = array (t := i8) arrBase xs) {i : Nat} (hi : i < xs.length)
    (hm : (t.eval ⋆ R) m) :
    loadVal m i8 (arrBase + BitVec.ofNat 64 i) = some xs[i] := by
  have h := sepTree_arr_get hget (by decide) hi hm
  simpa [i8, Ty.bytes, Ty.size, Nat.one_mul] using h

/-- `SepTree` byte-array (`i8`) store via `array arrBase (xs : List (BitVec 8))` and `Nat` index. -/
theorem sepTree_arr_put_byte_nat {t : SepTree} {p : List Bool} {arrBase : BitVec 64}
    {xs : List (BitVec 8)} {M' R : Mem 64 → Prop} {m : Mem 64}
    (hget : t.get p = array (t := i8) arrBase xs) (v : BitVec 8) {i : Nat} (hi : i < xs.length)
    (heq : (t.set p (array (t := i8) arrBase (xs.set i v))).eval = M')
    (hm : (t.eval ⋆ R) m) :
    storeOk m i8 (arrBase + BitVec.ofNat 64 i) ∧
      (M' ⋆ R) (storeMem m i8 (arrBase + BitVec.ofNat 64 i) v) := by
  have h := sepTree_arr_put hget (by decide) v hi heq hm
  simpa [i8, Ty.bytes, Ty.size, Nat.one_mul] using h

/-- `SepTree` padded byte-array (`i8`) load via `Nat` index. -/
theorem sepTree_arr_pad_get_byte_nat {t : SepTree} {p : List Bool} {arrBase : BitVec 64}
    {xs : List (BitVec 8)} {pad R : Mem 64 → Prop} {m : Mem 64}
    (hget : t.get p = array (t := i8) arrBase xs ⋆ pad) {i : Nat} (hi : i < xs.length)
    (hm : (t.eval ⋆ R) m) :
    loadVal m i8 (arrBase + BitVec.ofNat 64 i) = some xs[i] := by
  have h := sepTree_arr_pad_get hget (by decide) hi hm
  simpa [i8, Ty.bytes, Ty.size, Nat.one_mul] using h

/-- `SepTree` padded byte-array (`i8`) store via `Nat` index. -/
theorem sepTree_arr_pad_put_byte_nat {t : SepTree} {p : List Bool} {arrBase : BitVec 64}
    {xs : List (BitVec 8)} {pad M' R : Mem 64 → Prop} {m : Mem 64}
    (hget : t.get p = array (t := i8) arrBase xs ⋆ pad) (v : BitVec 8) {i : Nat}
    (hi : i < xs.length)
    (heq : (t.set p (array (t := i8) arrBase (xs.set i v) ⋆ pad)).eval = M')
    (hm : (t.eval ⋆ R) m) :
    storeOk m i8 (arrBase + BitVec.ofNat 64 i) ∧
      (M' ⋆ R) (storeMem m i8 (arrBase + BitVec.ofNat 64 i) v) := by
  have h := sepTree_arr_pad_put hget (by decide) v hi heq hm
  simpa [i8, Ty.bytes, Ty.size, Nat.one_mul] using h

/-- `SepTree` `bytes` segment load (`Nat` index) via `SepTree.focus`. -/
theorem sepTree_bytes_get {t : SepTree} {p : List Bool} {arrBase : BitVec 64}
    {bs : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (hget : t.get p = bytes arrBase bs) {i : Nat} (hi : i < bs.length)
    (hb : bs.length ≤ 2 ^ 64) (hm : (t.eval ⋆ R) m) :
    loadVal m i8 (arrBase + BitVec.ofNat 64 i) = some (BitVec.ofNat 8 bs[i].toNat) := by
  have hf := SepTree.focus p hm
  rw [hget] at hf
  exact load_bytes_at hi hb hf

/-- `SepTree` `bytes` segment load (`BitVec 64` index) via `SepTree.focus`. -/
theorem sepTree_bytes_get_bv {t : SepTree} {p : List Bool} {arrBase : BitVec 64}
    {bs : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (hget : t.get p = bytes arrBase bs) {i : BitVec 64} (hi : i.toNat < bs.length)
    (hb : bs.length ≤ 2 ^ 64) (hm : (t.eval ⋆ R) m) :
    loadVal m i8 (arrBase + i) = some (BitVec.ofNat 8 bs[i.toNat].toNat) := by
  have h := sepTree_bytes_get hget hi hb hm
  simpa [BitVec.ofNat_toNat] using h

end LeanQbe.T

end
