module

public import LeanQbe.T.Logic.MemLemmas
public import LeanQbe.T.Logic.BitVec
import all Kraken.Separation

/-!
# `SepTree`: Universal `O(log K)` Separation-Logic Focusing (Zero `ecancel`)

Balanced binary tree of `Mem 64` separation-logic footprints replacing flat `N`-atom `⋆`-chains
and hand-maintained `Full*Rest` / `focus_*` / `unfocus_*` boilerplate:

* `SepTree.eval` interprets a `SepTree` as a nested `⋆` predicate.
* `SepTree.get` / `SepTree.rest` / `SepTree.set` extract or replace any leaf along its binary
  path `List Bool` (`false` = left, `true` = right) by kernel reduction (`rfl`).
* `SepTree.focus` / `SepTree.unfocus` / `SepTree.unfocus_eq` extract or update any leaf in
  `O(log K)` steps without invoking `ecancel` or AC-matching at call sites.
* Generic accessors (`sepTree_cell_*`, `sepTree_hdr_*`, `sepTree_arr_*`, `sepTree_arr_pad_*`)
  provide `O(log K)` typed loads/stores over `SepTree`-backed arena layouts, including constant-
  offset sub-buffer slices and alignment-padded array leaves.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

open Std Std.ExtHashMap

/-! ## 1. Core `SepTree` Structure and `O(log K)` Focus/Unfocus Laws -/

/-- Balanced binary tree of `Mem 64` separation-logic footprints. -/
inductive SepTree where
  | leaf (P : Mem 64 → Prop)
  | node (l r : SepTree)

/-- Evaluate a `SepTree` as a nested `⋆` predicate. -/
def SepTree.eval : SepTree → Mem 64 → Prop
  | .leaf P => P
  | .node l r => l.eval ⋆ r.eval

/-- Extract the leaf (or subtree) at binary path `p` (`false` = left, `true` = right). -/
def SepTree.get : SepTree → List Bool → Mem 64 → Prop
  | .leaf P, _ => P
  | .node l _, false :: ps => l.get ps
  | .node _ r, true :: ps => r.get ps
  | t, [] => t.eval

/-- Extract the frame complement (`Rest`) of the leaf at binary path `p`. -/
def SepTree.rest : SepTree → List Bool → Mem 64 → Prop
  | .leaf _, _ => emp
  | .node l r, false :: ps => l.rest ps ⋆ r.eval
  | .node l r, true :: ps => l.eval ⋆ r.rest ps
  | _, [] => emp

/-- Replace the leaf (or subtree) at binary path `p` with `P'`. -/
def SepTree.set : SepTree → List Bool → (Mem 64 → Prop) → SepTree
  | .leaf _, _, P' => .leaf P'
  | .node l r, false :: ps, P' => .node (l.set ps P') r
  | .node l r, true :: ps, P' => .node l (r.set ps P')
  | _, [], P' => .leaf P'

/-- Number of leaves in a `SepTree`. -/
def SepTree.size : SepTree → Nat
  | .leaf _ => 1
  | .node l r => l.size + r.size

/-- Height of a `SepTree` (`0` for a single leaf). -/
def SepTree.depth : SepTree → Nat
  | .leaf _ => 0
  | .node l r => 1 + max l.depth r.depth

/-- Structurally recursive balanced `SepTree` builder from a list of leaf predicates. -/
def SepTree.ofListAux : Nat → List (Mem 64 → Prop) → SepTree
  | 0, _ => .leaf emp
  | _, [] => .leaf emp
  | _, [P] => .leaf P
  | fuel + 1, ps =>
    let mid := ps.length / 2
    .node (SepTree.ofListAux fuel (ps.take mid)) (SepTree.ofListAux fuel (ps.drop mid))

/-- Build a balanced `SepTree` of depth `⌈log₂ K⌉` from `K` leaf predicates. -/
def SepTree.ofList (ps : List (Mem 64 → Prop)) : SepTree :=
  SepTree.ofListAux ps.length ps

private theorem sep_emp_r (P : Mem 64 → Prop) : (P ⋆ emp) = P := by
  funext m; apply propext; simp [sep_emp]

/-- Universal `O(log K)` focus equality: any leaf in a `K`-leaf `SepTree` splits out along its
binary path without AC-matching at call sites. -/
theorem SepTree.eval_eq_focus : ∀ (t : SepTree) (p : List Bool),
    t.eval = (t.get p ⋆ t.rest p)
  | .leaf P, _ => (sep_emp_r P).symm
  | .node l r, [] => (sep_emp_r (l.eval ⋆ r.eval)).symm
  | .node l r, false :: ps => by
    simp only [SepTree.eval, SepTree.get, SepTree.rest]
    rw [SepTree.eval_eq_focus l ps, sep_assoc]
  | .node l r, true :: ps => by
    simp only [SepTree.eval, SepTree.get, SepTree.rest]
    rw [SepTree.eval_eq_focus r ps]
    ac_rfl

/-- Replacing leaf `p` leaves its complement `rest p` unchanged. -/
theorem SepTree.rest_set : ∀ (t : SepTree) (p : List Bool) (P' : Mem 64 → Prop),
    (t.set p P').rest p = t.rest p
  | .leaf _, _, _ => rfl
  | .node _ _, [], _ => rfl
  | .node l r, false :: ps, P' => by
    simp only [SepTree.set, SepTree.rest, SepTree.rest_set l ps P']
  | .node l r, true :: ps, P' => by
    simp only [SepTree.set, SepTree.rest, SepTree.rest_set r ps P']

/-- Reading back leaf `p` after replacing it yields `P'`. -/
theorem SepTree.get_set : ∀ (t : SepTree) (p : List Bool) (P' : Mem 64 → Prop),
    (t.set p P').get p = P'
  | .leaf _, _, _ => rfl
  | .node _ _, [], _ => rfl
  | .node l _, false :: ps, P' => SepTree.get_set l ps P'
  | .node _ r, true :: ps, P' => SepTree.get_set r ps P'

/-- Replacing leaf `p` with its existing value preserves `eval`. -/
theorem SepTree.set_get_eval (t : SepTree) (p : List Bool) :
    (t.set p (t.get p)).eval = t.eval := by
  rw [SepTree.eval_eq_focus (t.set p (t.get p)) p, SepTree.get_set, SepTree.rest_set,
    ← SepTree.eval_eq_focus t p]

/-- Focus leaf `p` out of `(t.eval ⋆ R) m` in `O(log K)`. -/
theorem SepTree.focus {t : SepTree} {R : Mem 64 → Prop} {m : Mem 64} (p : List Bool)
    (hm : (t.eval ⋆ R) m) : (t.get p ⋆ (t.rest p ⋆ R)) m := by
  rw [SepTree.eval_eq_focus t p, sep_assoc] at hm; exact hm

/-- Unfocus a modified leaf `P'` back into `((t.set p P').eval ⋆ R) m` in `O(log K)`. -/
theorem SepTree.unfocus {t : SepTree} {P' R : Mem 64 → Prop} {m : Mem 64} (p : List Bool)
    (hm : (P' ⋆ (t.rest p ⋆ R)) m) : ((t.set p P').eval ⋆ R) m := by
  rw [SepTree.eval_eq_focus (t.set p P') p, SepTree.get_set, SepTree.rest_set, sep_assoc]
  exact hm

/-- Bridge `(t.set p P').eval = M'` when `M'` is the updated state's `*Mem`. -/
theorem SepTree.unfocus_eq {t : SepTree} {P' M' R : Mem 64 → Prop} {m : Mem 64} (p : List Bool)
    (heq : (t.set p P').eval = M') (hm : (P' ⋆ (t.rest p ⋆ R)) m) : (M' ⋆ R) m :=
  heq ▸ SepTree.unfocus p hm

/-- Unfocus an unmodified leaf `t.get p` back into `(t.eval ⋆ R) m`. -/
theorem SepTree.unfocus_same {t : SepTree} {R : Mem 64 → Prop} {m : Mem 64} (p : List Bool)
    (hm : (t.get p ⋆ (t.rest p ⋆ R)) m) : (t.eval ⋆ R) m := by
  rw [SepTree.eval_eq_focus t p, sep_assoc]; exact hm

/-- Bidirectional focusing equivalence for leaf `p`. -/
theorem SepTree.focus_iff {t : SepTree} {R : Mem 64 → Prop} {m : Mem 64} (p : List Bool) :
    (t.eval ⋆ R) m ↔ (t.get p ⋆ (t.rest p ⋆ R)) m :=
  ⟨SepTree.focus p, SepTree.unfocus_same p⟩

/-- Lift a pointwise leaf implication `t.get p → P'` into
`(t.eval ⋆ R) → ((t.set p P').eval ⋆ R)`. -/
theorem SepTree.focus_mono {t : SepTree} {P' R : Mem 64 → Prop} {m : Mem 64} (p : List Bool)
    (h : ∀ f, t.get p f → P' f) (hm : (t.eval ⋆ R) m) : ((t.set p P').eval ⋆ R) m :=
  SepTree.unfocus p (sep_mono h (SepTree.focus p hm))

/-! ## 2. Address Helpers & Generic `O(log K)` `SepTree` Accessors -/

theorem bv64_ofNat_toNat (v : BitVec 64) : BitVec.ofNat 64 v.toNat = v :=
  BitVec.eq_of_toNat_eq (by simp)

private theorem sepTree_mul_ofNat (i : BitVec 64) (b : Nat) :
    i * BitVec.ofNat 64 b = BitVec.ofNat 64 (b * i.toNat) :=
  BitVec.eq_of_toNat_eq (by
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mul_mod_mod, Nat.mul_comm])

private theorem sepTree_u32_mul_ofNat (i : BitVec 32) (b : Nat) :
    i.setWidth 64 * BitVec.ofNat 64 b = BitVec.ofNat 64 (b * i.toNat) := by
  rw [sepTree_mul_ofNat, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_trans i.isLt (by decide : 2 ^ 32 < 2 ^ 64))]

theorem sepTree_u32_setWidth_eq (i : BitVec 32) :
    i.setWidth 64 = BitVec.ofNat 64 i.toNat :=
  BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat])

/-- Load a scalar `cell` at leaf `p` of `t`. -/
theorem sepTree_cell_get {ty : Ty} {t : SepTree} {p : List Bool} {a : BitVec 64} {v : Val ty}
    {R : Mem 64 → Prop} {m : Mem 64} (hget : t.get p = cell (t := ty) a v)
    (hb : ty.bytes ≤ 2 ^ 64) (hm : (t.eval ⋆ R) m) : loadVal m ty a = some v := by
  have hf := SepTree.focus p hm
  rw [hget] at hf
  exact loadVal_cell hb hf

/-- Store into a scalar `cell` at leaf `p` of `t`. -/
theorem sepTree_cell_put {ty : Ty} {t : SepTree} {p : List Bool} {a : BitVec 64} {v0 : Val ty}
    (v : Val ty) {M' R : Mem 64 → Prop} {m : Mem 64} (hget : t.get p = cell (t := ty) a v0)
    (hb : ty.bytes ≤ 2 ^ 64) (heq : (t.set p (cell (t := ty) a v)).eval = M')
    (hm : (t.eval ⋆ R) m) :
    storeOk m ty a ∧ (M' ⋆ R) (storeMem m ty a v) := by
  have hf := SepTree.focus p hm
  rw [hget] at hf
  obtain ⟨hok, hst⟩ := store_cell v hb hf
  exact ⟨hok, SepTree.unfocus_eq p heq hst⟩

/-- Load word `i` from an `array64` header block at leaf `p`. -/
theorem sepTree_hdr_get {t : SepTree} {p : List Bool} {base : BitVec 64}
    {words : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    (hget : t.get p = array64 base words) (i : Nat) (hi : i < words.length)
    (hm : (t.eval ⋆ R) m) :
    loadVal m i64 (base + BitVec.ofNat 64 (8 * i)) = some (words[i]'hi) := by
  have hf := SepTree.focus p hm
  rw [hget] at hf
  exact loadVal_array64 hi hf

/-- Load word `0` (`base` with zero offset) from an `array64` header block at leaf `p`. -/
theorem sepTree_hdr_get_zero {t : SepTree} {p : List Bool} {base : BitVec 64}
    {words : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    (hget : t.get p = array64 base words) (hi : 0 < words.length) (hm : (t.eval ⋆ R) m) :
    loadVal m i64 base = some (words[0]'hi) := by
  have h := sepTree_hdr_get hget 0 hi hm
  rwa [show BitVec.ofNat 64 (8 * 0) = 0#64 from rfl, BitVec.add_zero] at h

/-- Store word `i` into an `array64` header block at leaf `p`. -/
theorem sepTree_hdr_put {t : SepTree} {p : List Bool} {base : BitVec 64}
    {words words' : List (BitVec 64)} {M' R : Mem 64 → Prop} {m : Mem 64}
    (hget : t.get p = array64 base words) (i : Nat) (hi : i < words.length) (v : BitVec 64)
    (hset : words' = words.set i v) (heq : (t.set p (array64 base words')).eval = M')
    (hm : (t.eval ⋆ R) m) :
    storeOk m i64 (base + BitVec.ofNat 64 (8 * i)) ∧
      (M' ⋆ R) (storeMem m i64 (base + BitVec.ofNat 64 (8 * i)) v) := by
  have hf := SepTree.focus p hm
  rw [hget] at hf
  obtain ⟨hok, hst⟩ := store_array64 v hi hf
  rw [← hset] at hst
  exact ⟨hok, SepTree.unfocus_eq p heq hst⟩

/-- Store word `0` (`base` with zero offset) into an `array64` header block at leaf `p`. -/
theorem sepTree_hdr_put_zero {t : SepTree} {p : List Bool} {base : BitVec 64}
    {words words' : List (BitVec 64)} {M' R : Mem 64 → Prop} {m : Mem 64}
    (hget : t.get p = array64 base words) (hi : 0 < words.length) (v : BitVec 64)
    (hset : words' = words.set 0 v) (heq : (t.set p (array64 base words')).eval = M')
    (hm : (t.eval ⋆ R) m) :
    storeOk m i64 base ∧ (M' ⋆ R) (storeMem m i64 base v) := by
  have h := sepTree_hdr_put hget 0 hi v hset heq hm
  rwa [show BitVec.ofNat 64 (8 * 0) = 0#64 from rfl, BitVec.add_zero] at h

/-- Load element `i` (`Nat`) from a typed `array` leaf at path `p`. -/
theorem sepTree_arr_get {ty : Ty} {t : SepTree} {p : List Bool} {base : BitVec 64}
    {xs : List (Val ty)} {R : Mem 64 → Prop} {m : Mem 64}
    (hget : t.get p = array (t := ty) base xs) (hb : ty.bytes ≤ 2 ^ 64)
    {i : Nat} (hi : i < xs.length) (hm : (t.eval ⋆ R) m) :
    loadVal m ty (base + BitVec.ofNat 64 (ty.bytes * i)) = some (xs[i]'hi) := by
  have hf := SepTree.focus p hm
  rw [hget] at hf
  exact loadVal_array hb hi hf

/-- Store element `i` (`Nat`) into a typed `array` leaf at path `p`. -/
theorem sepTree_arr_put {ty : Ty} {t : SepTree} {p : List Bool} {base : BitVec 64}
    {xs : List (Val ty)} {M' R : Mem 64 → Prop} {m : Mem 64}
    (hget : t.get p = array (t := ty) base xs) (hb : ty.bytes ≤ 2 ^ 64)
    (v : Val ty) {i : Nat} (hi : i < xs.length)
    (heq : (t.set p (array (t := ty) base (xs.set i v))).eval = M')
    (hm : (t.eval ⋆ R) m) :
    storeOk m ty (base + BitVec.ofNat 64 (ty.bytes * i)) ∧
      (M' ⋆ R) (storeMem m ty (base + BitVec.ofNat 64 (ty.bytes * i)) v) := by
  have hf := SepTree.focus p hm
  rw [hget] at hf
  obtain ⟨hok, hst⟩ := store_array v hb hi hf
  exact ⟨hok, SepTree.unfocus_eq p heq hst⟩

/-- Load element `i` (`BitVec 64`) from a byte (`i8`) `array` leaf at `base + i`. -/
theorem sepTree_arr_get_byte {t : SepTree} {p : List Bool} {base : BitVec 64}
    {xs : List (BitVec 8)} {R : Mem 64 → Prop} {m : Mem 64}
    (hget : t.get p = array (t := i8) base xs) {i : BitVec 64} (hi : i.toNat < xs.length)
    (hm : (t.eval ⋆ R) m) :
    loadVal m i8 (base + i) = some (xs[i.toNat]'hi) := by
  have h := sepTree_arr_get hget (by decide) hi hm
  simpa only [show i8.bytes = 1 from rfl, Nat.one_mul, bv64_ofNat_toNat] using h

/-- Store element `i` (`BitVec 64`) into a byte (`i8`) `array` leaf at `base + i`. -/
theorem sepTree_arr_put_byte {t : SepTree} {p : List Bool} {base : BitVec 64}
    {xs : List (BitVec 8)} {M' R : Mem 64 → Prop} {m : Mem 64}
    (hget : t.get p = array (t := i8) base xs) (v : BitVec 8) {i : BitVec 64}
    (hi : i.toNat < xs.length)
    (heq : (t.set p (array (t := i8) base (xs.set i.toNat v))).eval = M')
    (hm : (t.eval ⋆ R) m) :
    storeOk m i8 (base + i) ∧ (M' ⋆ R) (storeMem m i8 (base + i) v) := by
  have h := sepTree_arr_put hget (by decide) v hi heq hm
  simpa only [show i8.bytes = 1 from rfl, Nat.one_mul, bv64_ofNat_toNat] using h

/-- Load element `i` (`BitVec 32`) from a byte (`i8`) `array` leaf at `base + i.setWidth 64`. -/
theorem sepTree_arr_get_byte_u32 {t : SepTree} {p : List Bool} {base : BitVec 64}
    {xs : List (BitVec 8)} {R : Mem 64 → Prop} {m : Mem 64}
    (hget : t.get p = array (t := i8) base xs) {i : BitVec 32} (hi : i.toNat < xs.length)
    (hm : (t.eval ⋆ R) m) :
    loadVal m i8 (base + i.setWidth 64) = some (xs[i.toNat]'hi) := by
  rw [sepTree_u32_setWidth_eq]
  simpa only [show i8.bytes = 1 from rfl, Nat.one_mul] using sepTree_arr_get hget (by decide) hi hm

/-- Store element `i` (`BitVec 32`) into a byte (`i8`) `array` leaf at `base + i.setWidth 64`. -/
theorem sepTree_arr_put_byte_u32 {t : SepTree} {p : List Bool} {base : BitVec 64}
    {xs : List (BitVec 8)} {M' R : Mem 64 → Prop} {m : Mem 64}
    (hget : t.get p = array (t := i8) base xs) (v : BitVec 8) {i : BitVec 32}
    (hi : i.toNat < xs.length)
    (heq : (t.set p (array (t := i8) base (xs.set i.toNat v))).eval = M')
    (hm : (t.eval ⋆ R) m) :
    storeOk m i8 (base + i.setWidth 64) ∧ (M' ⋆ R) (storeMem m i8 (base + i.setWidth 64) v) := by
  rw [sepTree_u32_setWidth_eq]
  simpa only [show i8.bytes = 1 from rfl, Nat.one_mul] using
    sepTree_arr_put hget (by decide) v hi heq hm

/-- Constant-offset sub-buffer load (`base + off + i * ty.bytes`). -/
theorem sepTree_arr_get_off {ty : Ty} {t : SepTree} {p : List Bool} {base : BitVec 64}
    {xs : List (Val ty)} {R : Mem 64 → Prop} {m : Mem 64}
    (hget : t.get p = array (t := ty) base xs) (hb : ty.bytes ≤ 2 ^ 64)
    (k : Nat) {off : BitVec 64} (hoff : off = BitVec.ofNat 64 (ty.bytes * k))
    {i : BitVec 64} (hi : k + i.toNat < xs.length) (hm : (t.eval ⋆ R) m) :
    loadVal m ty (base + off + i * BitVec.ofNat 64 ty.bytes) = some (xs[k + i.toNat]'hi) := by
  rw [hoff, sepTree_mul_ofNat, ptr_add_ofNat, ← Nat.mul_add]
  exact sepTree_arr_get hget hb hi hm

/-- Constant-offset sub-buffer load with `u32` index (`base + off + i.setWidth 64 * ty.bytes`). -/
theorem sepTree_arr_get_off_u32 {ty : Ty} {t : SepTree} {p : List Bool} {base : BitVec 64}
    {xs : List (Val ty)} {R : Mem 64 → Prop} {m : Mem 64}
    (hget : t.get p = array (t := ty) base xs) (hb : ty.bytes ≤ 2 ^ 64)
    (k : Nat) {off : BitVec 64} (hoff : off = BitVec.ofNat 64 (ty.bytes * k))
    {i : BitVec 32} (hi : k + i.toNat < xs.length) (hm : (t.eval ⋆ R) m) :
    loadVal m ty (base + off + i.setWidth 64 * BitVec.ofNat 64 ty.bytes) =
      some (xs[k + i.toNat]'hi) := by
  rw [hoff, sepTree_u32_mul_ofNat, ptr_add_ofNat, ← Nat.mul_add]
  exact sepTree_arr_get hget hb hi hm

/-- Constant-offset sub-buffer store (`base + off + i * ty.bytes`). -/
theorem sepTree_arr_put_off {ty : Ty} {t : SepTree} {p : List Bool} {base : BitVec 64}
    {xs : List (Val ty)} {M' R : Mem 64 → Prop} {m : Mem 64}
    (hget : t.get p = array (t := ty) base xs) (hb : ty.bytes ≤ 2 ^ 64)
    (k : Nat) {off : BitVec 64} (hoff : off = BitVec.ofNat 64 (ty.bytes * k))
    (v : Val ty) {i : BitVec 64} (hi : k + i.toNat < xs.length)
    (heq : (t.set p (array (t := ty) base (xs.set (k + i.toNat) v))).eval = M')
    (hm : (t.eval ⋆ R) m) :
    storeOk m ty (base + off + i * BitVec.ofNat 64 ty.bytes) ∧
      (M' ⋆ R) (storeMem m ty (base + off + i * BitVec.ofNat 64 ty.bytes) v) := by
  rw [hoff, sepTree_mul_ofNat, ptr_add_ofNat, ← Nat.mul_add]
  exact sepTree_arr_put hget hb v hi heq hm

/-- Constant-offset sub-buffer store with `u32` index. -/
theorem sepTree_arr_put_off_u32 {ty : Ty} {t : SepTree} {p : List Bool} {base : BitVec 64}
    {xs : List (Val ty)} {M' R : Mem 64 → Prop} {m : Mem 64}
    (hget : t.get p = array (t := ty) base xs) (hb : ty.bytes ≤ 2 ^ 64)
    (k : Nat) {off : BitVec 64} (hoff : off = BitVec.ofNat 64 (ty.bytes * k))
    (v : Val ty) {i : BitVec 32} (hi : k + i.toNat < xs.length)
    (heq : (t.set p (array (t := ty) base (xs.set (k + i.toNat) v))).eval = M')
    (hm : (t.eval ⋆ R) m) :
    storeOk m ty (base + off + i.setWidth 64 * BitVec.ofNat 64 ty.bytes) ∧
      (M' ⋆ R) (storeMem m ty (base + off + i.setWidth 64 * BitVec.ofNat 64 ty.bytes) v) := by
  rw [hoff, sepTree_u32_mul_ofNat, ptr_add_ofNat, ← Nat.mul_add]
  exact sepTree_arr_put hget hb v hi heq hm

/-! ## 3. Alignment-Padded Leaf Accessors (`array ⋆ pad` Leaves, Zero `ecancel`) -/

/-- Focus the `array` portion of a padded leaf `(array base xs ⋆ pad)` in `O(log K)`. -/
theorem sepTree_arr_pad_focus {ty : Ty} {t : SepTree} {p : List Bool} {base : BitVec 64}
    {xs : List (Val ty)} {pad R : Mem 64 → Prop} {m : Mem 64}
    (hget : t.get p = (array (t := ty) base xs ⋆ pad)) (hm : (t.eval ⋆ R) m) :
    (array (t := ty) base xs ⋆ (pad ⋆ (t.rest p ⋆ R))) m := by
  have hf := SepTree.focus p hm
  rw [hget, sep_assoc] at hf
  exact hf

/-- Unfocus an updated `array` back into a padded leaf `(array base xs' ⋆ pad)` in `O(log K)`. -/
theorem sepTree_arr_pad_unfocus_eq {ty : Ty} {t : SepTree} {p : List Bool} {base : BitVec 64}
    {xs' : List (Val ty)} {pad M' R : Mem 64 → Prop} {m : Mem 64}
    (heq : (t.set p (array (t := ty) base xs' ⋆ pad)).eval = M')
    (hm : (array (t := ty) base xs' ⋆ (pad ⋆ (t.rest p ⋆ R))) m) :
    (M' ⋆ R) m := by
  rw [← sep_assoc] at hm
  exact SepTree.unfocus_eq p heq hm

/-- Focus the `array` portion of a padded leaf, grouping `(pad ⋆ t.rest p)` as one `Rest` atom. -/
theorem sepTree_arr_pad_focus_rest {ty : Ty} {t : SepTree} {p : List Bool} {base : BitVec 64}
    {xs : List (Val ty)} {pad R : Mem 64 → Prop} {m : Mem 64}
    (hget : t.get p = (array (t := ty) base xs ⋆ pad)) (hm : (t.eval ⋆ R) m) :
    (array (t := ty) base xs ⋆ ((pad ⋆ t.rest p) ⋆ R)) m := by
  have hf := sepTree_arr_pad_focus hget hm
  rwa [← sep_assoc pad] at hf

/-- Unfocus an updated `array` from a grouped `Rest := pad ⋆ t.rest p` in `O(log K)`. -/
theorem sepTree_arr_pad_unfocus_rest_eq {ty : Ty} {t : SepTree} {p : List Bool} {base : BitVec 64}
    {xs' : List (Val ty)} {pad M' R : Mem 64 → Prop} {m : Mem 64}
    (heq : (t.set p (array (t := ty) base xs' ⋆ pad)).eval = M')
    (hm : (array (t := ty) base xs' ⋆ ((pad ⋆ t.rest p) ⋆ R)) m) :
    (M' ⋆ R) m := by
  rw [sep_assoc pad] at hm
  exact sepTree_arr_pad_unfocus_eq heq hm

/-- Load element `i` (`Nat`) from an alignment-padded `array ⋆ pad` leaf. -/
theorem sepTree_arr_pad_get {ty : Ty} {t : SepTree} {p : List Bool} {base : BitVec 64}
    {xs : List (Val ty)} {pad R : Mem 64 → Prop} {m : Mem 64}
    (hget : t.get p = (array (t := ty) base xs ⋆ pad)) (hb : ty.bytes ≤ 2 ^ 64)
    {i : Nat} (hi : i < xs.length) (hm : (t.eval ⋆ R) m) :
    loadVal m ty (base + BitVec.ofNat 64 (ty.bytes * i)) = some (xs[i]'hi) :=
  loadVal_array hb hi (sepTree_arr_pad_focus hget hm)

/-- Store element `i` (`Nat`) into an alignment-padded `array ⋆ pad` leaf. -/
theorem sepTree_arr_pad_put {ty : Ty} {t : SepTree} {p : List Bool} {base : BitVec 64}
    {xs : List (Val ty)} {pad M' R : Mem 64 → Prop} {m : Mem 64}
    (hget : t.get p = (array (t := ty) base xs ⋆ pad)) (hb : ty.bytes ≤ 2 ^ 64)
    (v : Val ty) {i : Nat} (hi : i < xs.length)
    (heq : (t.set p (array (t := ty) base (xs.set i v) ⋆ pad)).eval = M')
    (hm : (t.eval ⋆ R) m) :
    storeOk m ty (base + BitVec.ofNat 64 (ty.bytes * i)) ∧
      (M' ⋆ R) (storeMem m ty (base + BitVec.ofNat 64 (ty.bytes * i)) v) := by
  obtain ⟨hok, hst⟩ := store_array v hb hi (sepTree_arr_pad_focus hget hm)
  exact ⟨hok, sepTree_arr_pad_unfocus_eq heq hst⟩

/-- Load element `i` (`BitVec 64`) from a padded `i8` leaf at `base + i`. -/
theorem sepTree_arr_pad_get_byte {t : SepTree} {p : List Bool} {base : BitVec 64}
    {xs : List (BitVec 8)} {pad R : Mem 64 → Prop} {m : Mem 64}
    (hget : t.get p = (array (t := i8) base xs ⋆ pad)) {i : BitVec 64}
    (hi : i.toNat < xs.length) (hm : (t.eval ⋆ R) m) :
    loadVal m i8 (base + i) = some (xs[i.toNat]'hi) := by
  have h := sepTree_arr_pad_get hget (by decide) hi hm
  simpa only [show i8.bytes = 1 from rfl, Nat.one_mul, bv64_ofNat_toNat] using h

/-- Store element `i` (`BitVec 64`) into a padded `i8` leaf at `base + i`. -/
theorem sepTree_arr_pad_put_byte {t : SepTree} {p : List Bool} {base : BitVec 64}
    {xs : List (BitVec 8)} {pad M' R : Mem 64 → Prop} {m : Mem 64}
    (hget : t.get p = (array (t := i8) base xs ⋆ pad)) (v : BitVec 8) {i : BitVec 64}
    (hi : i.toNat < xs.length)
    (heq : (t.set p (array (t := i8) base (xs.set i.toNat v) ⋆ pad)).eval = M')
    (hm : (t.eval ⋆ R) m) :
    storeOk m i8 (base + i) ∧ (M' ⋆ R) (storeMem m i8 (base + i) v) := by
  have h := sepTree_arr_pad_put hget (by decide) v hi heq hm
  simpa only [show i8.bytes = 1 from rfl, Nat.one_mul, bv64_ofNat_toNat] using h

/-- Load element `i` (`BitVec 32`) from a padded `i8` leaf at `base + i.setWidth 64`. -/
theorem sepTree_arr_pad_get_byte_u32 {t : SepTree} {p : List Bool} {base : BitVec 64}
    {xs : List (BitVec 8)} {pad R : Mem 64 → Prop} {m : Mem 64}
    (hget : t.get p = (array (t := i8) base xs ⋆ pad)) {i : BitVec 32}
    (hi : i.toNat < xs.length) (hm : (t.eval ⋆ R) m) :
    loadVal m i8 (base + i.setWidth 64) = some (xs[i.toNat]'hi) := by
  rw [sepTree_u32_setWidth_eq]
  simpa only [show i8.bytes = 1 from rfl, Nat.one_mul] using
    sepTree_arr_pad_get hget (by decide) hi hm

/-- Store element `i` (`BitVec 32`) into a padded `i8` leaf at `base + i.setWidth 64`. -/
theorem sepTree_arr_pad_put_byte_u32 {t : SepTree} {p : List Bool} {base : BitVec 64}
    {xs : List (BitVec 8)} {pad M' R : Mem 64 → Prop} {m : Mem 64}
    (hget : t.get p = (array (t := i8) base xs ⋆ pad)) (v : BitVec 8) {i : BitVec 32}
    (hi : i.toNat < xs.length)
    (heq : (t.set p (array (t := i8) base (xs.set i.toNat v) ⋆ pad)).eval = M')
    (hm : (t.eval ⋆ R) m) :
    storeOk m i8 (base + i.setWidth 64) ∧ (M' ⋆ R) (storeMem m i8 (base + i.setWidth 64) v) := by
  rw [sepTree_u32_setWidth_eq]
  simpa only [show i8.bytes = 1 from rfl, Nat.one_mul] using
    sepTree_arr_pad_put hget (by decide) v hi heq hm

/-- Constant-offset sub-buffer load on an alignment-padded `array ⋆ pad` leaf. -/
theorem sepTree_arr_pad_get_off {ty : Ty} {t : SepTree} {p : List Bool} {base : BitVec 64}
    {xs : List (Val ty)} {pad R : Mem 64 → Prop} {m : Mem 64}
    (hget : t.get p = (array (t := ty) base xs ⋆ pad)) (hb : ty.bytes ≤ 2 ^ 64)
    (k : Nat) {off : BitVec 64} (hoff : off = BitVec.ofNat 64 (ty.bytes * k))
    {i : BitVec 64} (hi : k + i.toNat < xs.length) (hm : (t.eval ⋆ R) m) :
    loadVal m ty (base + off + i * BitVec.ofNat 64 ty.bytes) = some (xs[k + i.toNat]'hi) := by
  rw [hoff, sepTree_mul_ofNat, ptr_add_ofNat, ← Nat.mul_add]
  exact sepTree_arr_pad_get hget hb hi hm

/-- Constant-offset sub-buffer store on an alignment-padded `array ⋆ pad` leaf. -/
theorem sepTree_arr_pad_put_off {ty : Ty} {t : SepTree} {p : List Bool} {base : BitVec 64}
    {xs : List (Val ty)} {pad M' R : Mem 64 → Prop} {m : Mem 64}
    (hget : t.get p = (array (t := ty) base xs ⋆ pad)) (hb : ty.bytes ≤ 2 ^ 64)
    (k : Nat) {off : BitVec 64} (hoff : off = BitVec.ofNat 64 (ty.bytes * k))
    (v : Val ty) {i : BitVec 64} (hi : k + i.toNat < xs.length)
    (heq : (t.set p (array (t := ty) base (xs.set (k + i.toNat) v) ⋆ pad)).eval = M')
    (hm : (t.eval ⋆ R) m) :
    storeOk m ty (base + off + i * BitVec.ofNat 64 ty.bytes) ∧
      (M' ⋆ R) (storeMem m ty (base + off + i * BitVec.ofNat 64 ty.bytes) v) := by
  rw [hoff, sepTree_mul_ofNat, ptr_add_ofNat, ← Nat.mul_add]
  exact sepTree_arr_pad_put hget hb v hi heq hm

end LeanQbe.T
