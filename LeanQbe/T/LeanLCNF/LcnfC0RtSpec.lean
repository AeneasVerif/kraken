module

public import LeanQbe.T.LeanLCNF.LcnfC0Rt
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.SlabChain
import all Kraken.Separation

/-!
# Separation-Logic Contracts and Heap Invariants for `LcnfC0Rt` (Milestone R0)

Defines the formal specification layer for `LeanQbe.T.LeanLCNF.LcnfC0Rt`:

1. **Concrete Slab Runtime State (`RtC0State`, `rtC0Inv`)**:
   - Bytes `0..255`: `extraArgs` (`32 × u64`)
   - Bytes `256..33023`: `globals` (`4096 × u64`)
   - Bytes `33024..33535`: `freeList` (`64 × u64`)
   - Bytes `33536..33671`: `LcnfC0Rt.At rt hdr`
   - `workBuf` (`work_cap × u64` @ `hdr.s_work`)
   - `smallPoolsAt` (`smallFreeList` chains for classes `2..63`, `16..504B`)
   - `largeFreeList` / `largeSeg` (`≥ 512B` singly-linked free blocks)
   - Remaining bump arena `region hdr.s_cur rem` (`[s_cur, s_end)`)
   - Optional 48-bit address-space predicate `RtC0State.Bounded48` for future segregated metadata
2. **Heap Objects (`LcnfObj`, `LcnfObj.Wf`, `lcnfObjMem`, `lcnfHeap`, `RcSound`)**:
   Covers constructors (`tag ≤ 244`), closures (`245`), `Array` (`246`), `SArray`/`ByteArray`
   (`248`), `String` (`249`), and `MPZ` (`250`), plus Perceus reference-count soundness (`RcSound`).
3. **Contracts (`Spec`) & Specification Environment (`rtC0SpecEntries`, `rtC0Env`)**:
   `lcnfAllocSpec`, `lcnfFreeObjSpec`, `lcnfDecRefColdSpec`, `lcnfMarkPersistentSpec`,
   `lcnfCloUnderSpec`, `Spec.Mono` lemmas, `rtC0Env` lookup lemmas, and `rtC0Inv_init_satisfiable`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.LeanLCNF

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil

/-! ## 1. Runtime Constants, Object Tags, and Region/Cell Helpers -/

/-- Minimum object cell size (`16` bytes) and exclusive upper bound (`2^28` bytes). -/
def rtMinObjBytes : Nat := 16
def rtMaxObjBytes : Nat := 268435456
def rtNumClasses : Nat := 64

/-- Dynamic LCNF heap object tags beyond `closureTag = 245` (`lcnf_rt.h`). -/
def arrayTag : Nat := 246
def sarrayTag : Nat := 248
def stringTag : Nat := 249
def mpzTag : Nat := 250

private theorem ptr_add_nat (a : BitVec 64) (m n : Nat) :
    a + BitVec.ofNat 64 m + BitVec.ofNat 64 n = a + BitVec.ofNat 64 (m + n) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

private theorem bv64_toBytes_toInt (v : BitVec 64) :
    Int.toBytes 8 v.toInt = Int.toBytes 8 (v.toNat : Int) := by
  rw [← Int.toBytes_emod, ← Int.toBytes_emod (x := (v.toNat : Int))]
  congr 1
  simp only [Int.take, BitVec.toInt_eq_msb_cond]
  cases v.msb
  · simp
  · simp only [↓reduceIte]
    have hsub : ((v.toNat : Int) - (2 ^ (8 * 8) : Nat)) % (2 ^ (8 * 8) : Int) =
        (v.toNat : Int) % (2 ^ (8 * 8) : Int) := by
      rw [show ((2 ^ (8 * 8) : Nat) : Int) = (2 ^ (8 * 8) : Int) by decide, Int.sub_emod_right]
    simpa [show ((2 ^ 64 : Nat) : Int) = ((2 ^ (8 * 8) : Nat) : Int) by decide] using hsub

/-- Coalesce one `cell64` into an 8-byte `region`. -/
theorem cell64_to_region {a v : BitVec 64} {m : Mem 64} (h : cell64 a v m) :
    region a 8 m := by
  rw [cell64] at h
  exact ⟨Int.toBytes 8 v.toInt, Int.toBytes_length 8 v.toInt, h.symm⟩

/-- Split an 8-byte `region` into a `cell64` with an existentially quantified word. -/
theorem region_to_cell64 {a : BitVec 64} {m : Mem 64} (h : region a 8 m) :
    ∃ v : BitVec 64, cell64 a v m := by
  obtain ⟨xs, hlen, hw⟩ := region_to_word8Array 1 (by decide) h
  rcases xs with _ | ⟨v, _ | _⟩ <;> simp at hlen
  rw [word8Array_eq a [v] (by simp)] at hw
  simp only [bytesN, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hw
  refine ⟨v, ?_⟩
  rw [cell64, bv64_toBytes_toInt]
  exact hw

/-- Coalesce an `array64 a xs` into a `region a (8 * xs.length)`. -/
theorem array64_to_region {a : BitVec 64} {xs : List (BitVec 64)} {m : Mem 64}
    (hfit : 8 * xs.length ≤ 2 ^ 64) (h : array64 a xs m) : region a (8 * xs.length) m := by
  rw [array64_eq_array] at h
  have hb := array_eq_bytesOf (t := i64) a xs (by simp [Ty.bytes, Ty.size, i64]; omega) h
  have hr := bytes_to_region hb.symm
  simpa [bytesOf_length, Ty.bytes, Ty.size, i64] using hr

/-- Split `region a (8 * k)` into `array64 a xs` of length `k`. -/
theorem region_to_array64 {a : BitVec 64} :
    ∀ (k : Nat) (_hk : 8 * k ≤ 2 ^ 64) {m : Mem 64},
      region a (8 * k) m → ∃ xs : List (BitVec 64), xs.length = k ∧ array64 a xs m
  | 0, _, m, h => by
    simp only [Nat.mul_zero, region_zero] at h
    exact ⟨[], rfl, h⟩
  | k + 1, hk, m, h => by
    have heq : 8 * (k + 1) = 8 + 8 * k := by omega
    rw [heq, region_split (by omega)] at h
    rcases h with ⟨m1, m2, hu, hd, hr1, hr2⟩
    obtain ⟨v, hc1⟩ := region_to_cell64 hr1
    obtain ⟨xs, hlen, hxs⟩ := region_to_array64 (a := a + 8) k (by omega) hr2
    refine ⟨v :: xs, by simp [hlen], ?_⟩
    exact ⟨m1, m2, hu, hd, hc1, hxs⟩

/-! ## 2. Small Size-Class Freelists and `large_free` Segments -/

/-- Head address of a small freelist (`0#64` if empty). -/
def listHeadPtr : List (BitVec 64) → BitVec 64
  | [] => 0#64
  | p :: _ => p

/-- A single free node of `bytes` (`16 ≤ bytes < 512`) in `free_list[cls]`. -/
def smallFreeNode (bytes : Nat) (p nxt : BitVec 64) : Mem 64 → Prop :=
  (region p 8 ⋆ cell64 (p + 8#64) nxt) ⋆ region (p + 16#64) (bytes - 16)

theorem smallFreeNode_to_region {bytes : Nat} {p nxt : BitVec 64} {m : Mem 64}
    (hlo : 16 ≤ bytes) (hhi : bytes ≤ 2 ^ 64) (h : smallFreeNode bytes p nxt m) :
    region p bytes m := by
  have h1 : ((region p 8 ⋆ region (p + 8#64) 8) ⋆ region (p + 16#64) (bytes - 16)) m := by
    unfold smallFreeNode at h
    exact sep_mono (fun _ hx => sep_mono_r (fun _ hc => cell64_to_region hc) hx) h
  have h2 : (region p 16 ⋆ region (p + 16#64) (bytes - 16)) m := by
    have hm := region_merge_eq (a := p) (n1 := 8) (n2 := 8) (n := 16) rfl (by decide)
    rw [show p + BitVec.ofNat 64 8 = p + 8#64 from rfl] at hm
    exact sep_mono (fun _ hx => hm ▸ hx) h1
  have hm := region_merge_eq (a := p) (n1 := 16) (n2 := bytes - 16) (n := bytes) (by omega) hhi
  rw [show p + BitVec.ofNat 64 16 = p + 16#64 from rfl] at hm
  exact hm ▸ h2

theorem region_to_smallFreeNode {bytes : Nat} {p : BitVec 64} {m : Mem 64}
    (hlo : 16 ≤ bytes) (hhi : bytes ≤ 2 ^ 64) (h : region p bytes m) :
    ∃ curNxt : BitVec 64, smallFreeNode bytes p curNxt m := by
  have heq0 : bytes = 16 + (bytes - 16) := by omega
  rw [heq0, region_split (by omega)] at h
  rcases h with ⟨m12, m3, hu12, hd12, hr12, hr3⟩
  have hr12' : region p (8 + 8) m12 := hr12
  rw [region_split (by decide)] at hr12'
  rcases hr12' with ⟨m1, m2, hu1, hd1, hr1, hr2⟩
  obtain ⟨v, hc2⟩ := region_to_cell64 hr2
  exact ⟨v, m12, m3, hu12, hd12, ⟨m1, m2, hu1, hd1, hr1, hc2⟩, hr3⟩

/-- Singly-linked freelist for size class `bytes = 8 * cls` (`2 ≤ cls < 64`). -/
def smallFreeList (bytes : Nat) : BitVec 64 → List (BitVec 64) → Mem 64 → Prop
  | hd, [], m => hd = 0#64 ∧ emp m
  | hd, p :: rest, m =>
    hd = p ∧ p ≠ 0#64 ∧ p.toNat % 8 = 0 ∧
    (smallFreeNode bytes p (listHeadPtr rest) ⋆
      smallFreeList bytes (listHeadPtr rest) rest) m

/-- Memory ownership of a single entry `n < 64` in `free_list`. -/
def smallPoolSlot (n : Nat) (hd : BitVec 64) (nodes : List (BitVec 64)) : Mem 64 → Prop :=
  if 2 ≤ n then smallFreeList (8 * n) hd nodes
  else fun m => hd = 0#64 ∧ nodes = [] ∧ emp m

/-- Ownership of classes `[0..n)` of the 64 small size-class freelists. -/
def smallPoolsAt (freeList : List (BitVec 64)) (pools : Nat → List (BitVec 64)) :
    Nat → Mem 64 → Prop
  | 0 => emp
  | n + 1 =>
    smallPoolsAt freeList pools n ⋆ smallPoolSlot n (freeList.getD n 0#64) (pools n)

/-- Ownership of classes `[0..n) \ {excl}` of the small freelists (used when focusing `excl`). -/
def smallPoolsExcl (excl : Nat) (freeList : List (BitVec 64))
    (pools : Nat → List (BitVec 64)) : Nat → Mem 64 → Prop
  | 0 => emp
  | n + 1 =>
    smallPoolsExcl excl freeList pools n ⋆
      if n = excl then emp else smallPoolSlot n (freeList.getD n 0#64) (pools n)

theorem smallPoolsExcl_eq_self (excl : Nat) (freeList : List (BitVec 64))
    (pools : Nat → List (BitVec 64)) : ∀ m, m ≤ excl →
    smallPoolsExcl excl freeList pools m = smallPoolsAt freeList pools m
  | 0, _ => rfl
  | m + 1, hm => by
    have hne : m ≠ excl := by omega
    simp only [smallPoolsExcl, smallPoolsAt, hne, ↓reduceIte]
    rw [smallPoolsExcl_eq_self excl freeList pools m (by omega)]

theorem smallPoolsAt_split {cls : Nat} : ∀ (n : Nat) (freeList : List (BitVec 64))
    (pools : Nat → List (BitVec 64)),
    cls < n →
    smallPoolsAt freeList pools n =
      (smallPoolSlot cls (freeList.getD cls 0#64) (pools cls) ⋆
       smallPoolsExcl cls freeList pools n)
  | 0, _, _, h => by omega
  | n + 1, freeList, pools, h => by
    by_cases hne : n = cls
    · subst hne
      simp only [smallPoolsAt, smallPoolsExcl, ↓reduceIte, sep_emp]
      rw [← smallPoolsExcl_eq_self n freeList pools n (Nat.le_refl n), sep_comm]
    · have hlt : cls < n := by omega
      have ih := smallPoolsAt_split n freeList pools hlt
      simp only [smallPoolsAt, smallPoolsExcl, hne, ↓reduceIte]
      rw [ih, sep_assoc]

theorem smallPoolsExcl_update {cls : Nat} (fl fl' : List (BitVec 64))
    (p p' : Nat → List (BitVec 64))
    (hfl : ∀ i, i ≠ cls → fl'.getD i 0#64 = fl.getD i 0#64)
    (hp : ∀ i, i ≠ cls → p' i = p i) :
    ∀ n, smallPoolsExcl cls fl' p' n = smallPoolsExcl cls fl p n
  | 0 => rfl
  | n + 1 => by
    simp only [smallPoolsExcl]
    rw [smallPoolsExcl_update fl fl' p p' hfl hp n]
    by_cases hne : n = cls
    · simp [hne]
    · simp only [hne, ↓reduceIte]
      have h1 := hfl n hne
      have h2 := hp n hne
      simp only [List.getD_eq_getElem?_getD] at h1 ⊢
      rw [h1, h2]

/-- Next pointer following a `large_free` segment ending at `endPtr`. -/
def largeSegNext (endPtr : BitVec 64) : List (BitVec 64 × Nat) → BitVec 64
  | [] => endPtr
  | (p, _) :: _ => p

/-- A single free large node (`bytes ≥ 512`): `[0..8)` cleared, `[8..16)` next, `[16..24)` size. -/
def largeFreeNode (bytes : Nat) (p nxt : BitVec 64) : Mem 64 → Prop :=
  ((region p 8 ⋆ cell64 (p + 8#64) nxt) ⋆ cell64 (p + 16#64) (BitVec.ofNat 64 bytes)) ⋆
  region (p + 24#64) (bytes - 24)

theorem largeFreeNode_to_region {bytes : Nat} {p nxt : BitVec 64} {m : Mem 64}
    (hlo : 24 ≤ bytes) (hhi : bytes ≤ 2 ^ 64) (h : largeFreeNode bytes p nxt m) :
    region p bytes m := by
  have h1 : (((region p 8 ⋆ region (p + 8#64) 8) ⋆ region (p + 16#64) 8) ⋆
      region (p + 24#64) (bytes - 24)) m := by
    unfold largeFreeNode at h
    exact sep_mono (fun _ hx => sep_mono2
      (fun _ hy => sep_mono_r (fun _ hc => cell64_to_region hc) hy)
      (fun _ hc => cell64_to_region hc) _ hx) h
  have h12 : ((region p 16 ⋆ region (p + 16#64) 8) ⋆ region (p + 24#64) (bytes - 24)) m := by
    have hm := region_merge_eq (a := p) (n1 := 8) (n2 := 8) (n := 16) rfl (by decide)
    rw [show p + BitVec.ofNat 64 8 = p + 8#64 from rfl] at hm
    exact sep_mono (fun _ hx => sep_mono (fun _ hy => hm ▸ hy) hx) h1
  have h123 : (region p 24 ⋆ region (p + 24#64) (bytes - 24)) m := by
    have hm := region_merge_eq (a := p) (n1 := 16) (n2 := 8) (n := 24) rfl (by decide)
    rw [show p + BitVec.ofNat 64 16 = p + 16#64 from rfl] at hm
    exact sep_mono (fun _ hx => hm ▸ hx) h12
  have hm := region_merge_eq (a := p) (n1 := 24) (n2 := bytes - 24) (n := bytes) (by omega) hhi
  rw [show p + BitVec.ofNat 64 24 = p + 24#64 from rfl] at hm
  exact hm ▸ h123

/-- Linked segment of `large_free` blocks starting at `hd` and terminating at `endPtr`. -/
def largeSeg (hd endPtr : BitVec 64) : List (BitVec 64 × Nat) → Mem 64 → Prop
  | [], m => hd = endPtr ∧ emp m
  | (p, b) :: rest, m =>
    hd = p ∧ p ≠ 0#64 ∧ p.toNat % 8 = 0 ∧ 512 ≤ b ∧ b < rtMaxObjBytes ∧ b % 8 = 0 ∧
    (largeFreeNode b p (largeSegNext endPtr rest) ⋆
      largeSeg (largeSegNext endPtr rest) endPtr rest) m

/-- Full `large_free` list rooted at `hd` and ending at `0#64`. -/
abbrev largeFreeList (hd : BitVec 64) (nodes : List (BitVec 64 × Nat)) : Mem 64 → Prop :=
  largeSeg hd 0#64 nodes

theorem largeSeg_hd_eq_next {mid endPtr : BitVec 64} {ys : List (BitVec 64 × Nat)} {m : Mem 64}
    (hy : largeSeg mid endPtr ys m) : mid = largeSegNext endPtr ys := by
  cases ys with
  | nil => exact hy.1
  | cons hd rest => exact hy.1

theorem largeSeg_append {hd mid endPtr : BitVec 64} :
    ∀ (xs ys : List (BitVec 64 × Nat)) {m : Mem 64},
      (largeSeg hd mid xs ⋆ largeSeg mid endPtr ys) m →
      largeSeg hd endPtr (xs ++ ys) m
  | [], ys, m, hm => by
    have hm' : ((fun m => hd = mid ∧ emp m) ⋆ largeSeg mid endPtr ys) m := hm
    obtain ⟨heq, hm2⟩ := sep_pure_l.mp hm'
    rw [emp_sep] at hm2
    rwa [heq]
  | (p, b) :: xs, ys, m, hm => by
    have hmid : mid = largeSegNext endPtr ys := by
      rcases hm with ⟨_, _, _, _, _, hy⟩
      exact largeSeg_hd_eq_next hy
    have hnext : largeSegNext mid xs = largeSegNext endPtr (xs ++ ys) := by
      cases xs with
      | nil => exact hmid
      | cons z zs => rfl
    have hcons :
        ((fun m =>
            (hd = p ∧ p ≠ 0#64 ∧ p.toNat % 8 = 0 ∧ 512 ≤ b ∧ b < rtMaxObjBytes ∧ b % 8 = 0) ∧
            (largeFreeNode b p (largeSegNext endPtr (xs ++ ys)) ⋆
              largeSeg (largeSegNext mid xs) mid xs) m) ⋆
          largeSeg mid endPtr ys) m := by
      refine sep_mono (fun _ hx => ?_) hm
      rcases hx with ⟨h1, h2, h3, h4, h5, h6, hrest⟩
      refine ⟨⟨h1, h2, h3, h4, h5, h6⟩, ?_⟩
      simpa only [hnext] using hrest
    obtain ⟨hmeta, hbody⟩ := sep_pure_l.mp hcons
    rw [sep_assoc] at hbody
    have hbody' :
        (largeFreeNode b p (largeSegNext endPtr (xs ++ ys)) ⋆
          (largeSeg (largeSegNext endPtr (xs ++ ys)) mid xs ⋆ largeSeg mid endPtr ys)) m := by
      simpa only [hnext] using hbody
    have hstep := sep_mono_r (fun _ h => largeSeg_append xs ys h) hbody'
    exact ⟨hmeta.1, hmeta.2.1, hmeta.2.2.1, hmeta.2.2.2.1, hmeta.2.2.2.2.1, hmeta.2.2.2.2.2, hstep⟩

theorem largeSeg_split_snoc {hd endPtr cur : BitVec 64} {b : Nat}
    (hcur : cur ≠ 0#64) (halign : cur.toNat % 8 = 0)
    (hlo : 512 ≤ b) (hhi : b < rtMaxObjBytes) (hmod : b % 8 = 0)
    (xs : List (BitVec 64 × Nat)) {m : Mem 64}
    (hm : (largeSeg hd cur xs ⋆ largeFreeNode b cur endPtr) m) :
    largeSeg hd endPtr (xs ++ [(cur, b)]) m := by
  refine largeSeg_append (mid := cur) xs [(cur, b)] ?_
  refine sep_mono_r (fun m2 h2 => ?_) hm
  refine ⟨rfl, hcur, halign, hlo, hhi, hmod, ?_⟩
  change (largeFreeNode b cur endPtr ⋆ (fun m => endPtr = endPtr ∧ emp m)) m2
  rw [sep_comm]
  exact sep_pure_l.mpr ⟨rfl, by rw [emp_sep]; exact h2⟩

/-! ## 3. Concrete `LcnfC0Rt` State and Slab Invariant -/

/-- Well-typed state of an initialized `LcnfC0Rt` slab. -/
structure RtC0State where
  extraArgs : List (BitVec 64)
  globals : List (BitVec 64)
  freeList : List (BitVec 64)
  hdr : LcnfC0Rt
  workBuf : List (BitVec 64)
  smallPools : Nat → List (BitVec 64)
  largeNodes : List (BitVec 64 × Nat)
  extraLen : extraArgs.length = rtExtraSlots
  globalsLen : globals.length = rtGlobalSlots
  freeListLen : freeList.length = rtNumClasses
  workLen : workBuf.length = hdr.s_work_cap.toNat
  curLeEnd : hdr.s_cur.toNat ≤ hdr.s_end.toNat
  arenaAlign : hdr.s_cur.toNat % 8 = 0
  curNz : hdr.s_cur ≠ 0#64

/-- Remaining bump-arena bytes `[cur, end)`. -/
def RtC0State.rem (st : RtC0State) : Nat :=
  st.hdr.s_end.toNat - st.hdr.s_cur.toNat

/-- Pre-allocated DFS worklist capacity (in `u64` object pointers). -/
def RtC0State.workCap (st : RtC0State) : Nat :=
  st.hdr.s_work_cap.toNat

/-- Optional 48-bit virtual-address-space bound for future upstream `lean.h` convergence. -/
def RtC0State.Bounded48 (st : RtC0State) : Prop :=
  st.hdr.s_end.toNat < 2 ^ 48

/-- Whether `st` currently holds a reusable free cell of exact size `bytes`. -/
def RtC0State.hasFree (st : RtC0State) (bytes : Nat) : Prop :=
  (bytes < 512 ∧ st.smallPools (bytes / 8) ≠ []) ∨
  (512 ≤ bytes ∧ ∃ x ∈ st.largeNodes, x.2 = bytes)

/-- Full separation-logic predicate for the `LcnfC0Rt` block, worklist, freelists, and bump arena. -/
def rtC0Inv (rt : BitVec 64) (st : RtC0State) : Mem 64 → Prop :=
  array64 rt st.extraArgs ⋆
  array64 (rt + BitVec.ofNat 64 rtGlobalsOff) st.globals ⋆
  array64 (rt + 33024#64) st.freeList ⋆
  LcnfC0Rt.At rt st.hdr ⋆
  array64 st.hdr.s_work st.workBuf ⋆
  smallPoolsAt st.freeList st.smallPools rtNumClasses ⋆
  largeFreeList st.hdr.s_large_free st.largeNodes ⋆
  region st.hdr.s_cur st.rem

/-- Static/caller-owned metadata preserved across R0 runtime calls. -/
def RtC0State.PreservesMeta (st st' : RtC0State) : Prop :=
  st'.extraArgs = st.extraArgs ∧
  st'.globals = st.globals ∧
  st'.hdr.s_ba_empty = st.hdr.s_ba_empty ∧
  st'.hdr.s_end = st.hdr.s_end ∧
  st'.hdr.s_work = st.hdr.s_work ∧
  st'.hdr.s_work_cap = st.hdr.s_work_cap ∧
  st'.hdr.s_chunks = st.hdr.s_chunks ∧
  st'.hdr.s_nchunks = st.hdr.s_nchunks ∧
  st'.hdr.s_chunks_cap = st.hdr.s_chunks_cap

/-- Concrete initial `RtC0State` packed into one contiguous slab `[rt, rt + 33672 + 8*workCap + rem)`. -/
def initRtC0State (rt : BitVec 64) (workCap rem : Nat)
    (hrt0 : rt.toNat + 33672 + 8 * workCap + rem < 2 ^ 64)
    (halign : rt.toNat % 8 = 0) : RtC0State where
  extraArgs := List.replicate rtExtraSlots 0#64
  globals := List.replicate rtGlobalSlots 0#64
  freeList := List.replicate rtNumClasses 0#64
  hdr :=
    { s_large_free := 0#64
      s_ba_empty := 0#64
      s_cur := rt + BitVec.ofNat 64 (33672 + 8 * workCap)
      s_end := rt + BitVec.ofNat 64 (33672 + 8 * workCap + rem)
      s_work := rt + 33672#64
      s_work_cap := BitVec.ofNat 64 workCap
      s_chunks := 0#64
      s_nchunks := 0#64
      s_chunks_cap := 0#64
      s_st_allocs := 0#64
      s_st_frees := 0#64
      s_st_live := 0#64
      s_st_peak_live := 0#64
      s_st_persistent := 0#64
      s_st_reused := 0#64
      s_st_cold_decs := 0#64
      s_st_bytes := 0#64 }
  workBuf := List.replicate workCap 0#64
  smallPools := fun _ => []
  largeNodes := []
  extraLen := List.length_replicate
  globalsLen := List.length_replicate
  freeListLen := List.length_replicate
  workLen := by
    have hwc : workCap < 2 ^ 64 := by omega
    rw [List.length_replicate, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwc]
  curLeEnd := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have hm1 : (33672 + 8 * workCap) % 2 ^ 64 = 33672 + 8 * workCap := Nat.mod_eq_of_lt (by omega)
    have hm2 : (33672 + 8 * workCap + rem) % 2 ^ 64 = 33672 + 8 * workCap + rem :=
      Nat.mod_eq_of_lt (by omega)
    rw [hm1, hm2, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  arenaAlign := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have hm1 : (33672 + 8 * workCap) % 2 ^ 64 = 33672 + 8 * workCap := Nat.mod_eq_of_lt (by omega)
    have hm2 : (rt.toNat + (33672 + 8 * workCap)) % 2 ^ 64 = rt.toNat + (33672 + 8 * workCap) :=
      Nat.mod_eq_of_lt (by omega)
    rw [hm1, hm2]
    omega
  curNz := by
    intro h
    have hto := congrArg BitVec.toNat h
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hto
    have hm1 : (33672 + 8 * workCap) % 2 ^ 64 = 33672 + 8 * workCap := Nat.mod_eq_of_lt (by omega)
    have hm2 : (rt.toNat + (33672 + 8 * workCap)) % 2 ^ 64 = rt.toNat + (33672 + 8 * workCap) :=
      Nat.mod_eq_of_lt (by omega)
    rw [hm1, hm2] at hto
    omega

private theorem initSmallPools_emp (n : Nat) :
    smallPoolsAt (List.replicate rtNumClasses 0#64) (fun _ => []) n = emp := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have heq : (List.replicate rtNumClasses 0#64).getD n 0#64 = 0#64 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split <;> rfl
    have hslot : smallPoolSlot n 0#64 [] = emp := by
      funext m
      unfold smallPoolSlot
      split <;> simp [smallFreeList]
    simp only [smallPoolsAt, ih, heq, hslot, sep_emp]

theorem rtC0Inv_init_satisfiable (rt : BitVec 64) (workCap rem : Nat)
    (hrt0 : rt.toNat + 33672 + 8 * workCap + rem < 2 ^ 64)
    (halign : rt.toNat % 8 = 0) {m : Mem 64}
    (hm : (array64 rt (initRtC0State rt workCap rem hrt0 halign).extraArgs ⋆
      array64 (rt + BitVec.ofNat 64 rtGlobalsOff)
        (initRtC0State rt workCap rem hrt0 halign).globals ⋆
      array64 (rt + 33024#64) (initRtC0State rt workCap rem hrt0 halign).freeList ⋆
      LcnfC0Rt.At rt (initRtC0State rt workCap rem hrt0 halign).hdr ⋆
      array64 (initRtC0State rt workCap rem hrt0 halign).hdr.s_work
        (initRtC0State rt workCap rem hrt0 halign).workBuf ⋆
      region (initRtC0State rt workCap rem hrt0 halign).hdr.s_cur rem) m) :
    rtC0Inv rt (initRtC0State rt workCap rem hrt0 halign) m := by
  let st := initRtC0State rt workCap rem hrt0 halign
  have hrem : st.rem = rem := by
    simp only [RtC0State.rem, st, initRtC0State, BitVec.toNat_add, BitVec.toNat_ofNat]
    have hm1 : (33672 + 8 * workCap) % 2 ^ 64 = 33672 + 8 * workCap := Nat.mod_eq_of_lt (by omega)
    have hm2 : (33672 + 8 * workCap + rem) % 2 ^ 64 = 33672 + 8 * workCap + rem :=
      Nat.mod_eq_of_lt (by omega)
    rw [hm1, hm2, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have hsm : smallPoolsAt st.freeList st.smallPools rtNumClasses = emp :=
    initSmallPools_emp rtNumClasses
  have hlg : largeFreeList st.hdr.s_large_free st.largeNodes = emp := by
    funext m'
    simp only [largeFreeList, largeSeg, st, initRtC0State, true_and]
  unfold rtC0Inv
  rw [hrem, hsm, hlg, sep_assoc, sep_emp, sep_comm emp, sep_emp]
  exact hm

private theorem cell_i64_to_region {a : BitVec 64} {v : Val i64} {m : Mem 64}
    (h : cell (t := i64) a v m) : region a 8 m :=
  cell64_to_region (by rwa [cell64_eq_cell])

private theorem peel_cell_reg {b a : BitVec 64} {k : Nat} {v : Val i64}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hk : k + 8 ≤ 2 ^ 64) (ha : b + BitVec.ofNat 64 k = a)
    (h : (region b k ⋆ (cell (t := i64) a v ⋆ R)) m) :
    (region b (k + 8) ⋆ R) m := by
  subst ha
  rw [← sep_assoc] at h
  refine sep_mono (fun _ hx => ?_) h
  exact (region_merge_eq rfl hk) ▸ sep_mono_r (fun _ hc => cell_i64_to_region hc) hx

private theorem last_cell_reg {b a : BitVec 64} {k : Nat} {v : Val i64} {m : Mem 64}
    (hk : k + 8 ≤ 2 ^ 64) (ha : b + BitVec.ofNat 64 k = a)
    (h : (region b k ⋆ cell (t := i64) a v) m) :
    region b (k + 8) m := by
  subst ha
  exact (region_merge_eq rfl hk) ▸ sep_mono_r (fun _ hc => cell_i64_to_region hc) h

private theorem lcnfC0Rt_at_to_region (rt : BitVec 64) (x : LcnfC0Rt) {m : Mem 64}
    (hm : LcnfC0Rt.At rt x m) : region (rt + 33536#64) 136 m := by
  unfold LcnfC0Rt.At at hm
  repeat rw [sep_assoc] at hm
  have h := sep_mono (fun _ hx => cell_i64_to_region hx) hm
  have h := peel_cell_reg (by decide) (by rw [BitVec.add_assoc]; congr 1) h
  have h := peel_cell_reg (by decide) (by rw [BitVec.add_assoc]; congr 1) h
  have h := peel_cell_reg (by decide) (by rw [BitVec.add_assoc]; congr 1) h
  have h := peel_cell_reg (by decide) (by rw [BitVec.add_assoc]; congr 1) h
  have h := peel_cell_reg (by decide) (by rw [BitVec.add_assoc]; congr 1) h
  have h := peel_cell_reg (by decide) (by rw [BitVec.add_assoc]; congr 1) h
  have h := peel_cell_reg (by decide) (by rw [BitVec.add_assoc]; congr 1) h
  have h := peel_cell_reg (by decide) (by rw [BitVec.add_assoc]; congr 1) h
  have h := peel_cell_reg (by decide) (by rw [BitVec.add_assoc]; congr 1) h
  have h := peel_cell_reg (by decide) (by rw [BitVec.add_assoc]; congr 1) h
  have h := peel_cell_reg (by decide) (by rw [BitVec.add_assoc]; congr 1) h
  have h := peel_cell_reg (by decide) (by rw [BitVec.add_assoc]; congr 1) h
  have h := peel_cell_reg (by decide) (by rw [BitVec.add_assoc]; congr 1) h
  have h := peel_cell_reg (by decide) (by rw [BitVec.add_assoc]; congr 1) h
  have h := peel_cell_reg (by decide) (by rw [BitVec.add_assoc]; congr 1) h
  exact last_cell_reg (by decide) (by rw [BitVec.add_assoc]; congr 1) h

/-- Contiguous collapse via `SlabChain.to_region_eq` showing the entire initialized R0 slab
fits inside one contiguous `region rt (33672 + 8 * workCap + rem)`. -/
theorem rtC0Slab_to_region (rt : BitVec 64) (workCap rem : Nat)
    (hrt0 : rt.toNat + 33672 + 8 * workCap + rem < 2 ^ 64)
    (halign : rt.toNat % 8 = 0) {m : Mem 64}
    (hm : (array64 rt (initRtC0State rt workCap rem hrt0 halign).extraArgs ⋆
      array64 (rt + BitVec.ofNat 64 rtGlobalsOff)
        (initRtC0State rt workCap rem hrt0 halign).globals ⋆
      array64 (rt + 33024#64) (initRtC0State rt workCap rem hrt0 halign).freeList ⋆
      LcnfC0Rt.At rt (initRtC0State rt workCap rem hrt0 halign).hdr ⋆
      array64 (initRtC0State rt workCap rem hrt0 halign).hdr.s_work
        (initRtC0State rt workCap rem hrt0 halign).workBuf ⋆
      region (initRtC0State rt workCap rem hrt0 halign).hdr.s_cur rem) m) :
    region rt (33672 + 8 * workCap + rem) m := by
  let st := initRtC0State rt workCap rem hrt0 halign
  let hdrSeg : SlabSeg :=
    { stride := 136
      pred := fun a => LcnfC0Rt.At (a - 33536#64) st.hdr
      toReg := fun a m' _ ha => by
        have hr := lcnfC0Rt_at_to_region (a - 33536#64) st.hdr ha
        have hadd : (a - 33536#64) + 33536#64 = a := by bv_omega
        rwa [hadd] at hr }
  let segs : List SlabSeg :=
    [ SlabSeg.ofArray64 st.extraArgs rtExtraSlots st.extraLen,
      SlabSeg.ofArray64 st.globals rtGlobalSlots st.globalsLen,
      SlabSeg.ofArray64 st.freeList rtNumClasses st.freeListLen,
      hdrSeg,
      SlabSeg.ofArray64 st.workBuf workCap List.length_replicate,
      SlabSeg.ofRegion rem ]
  have htot : SlabChain.totalBytes segs = 33672 + 8 * workCap + rem := by
    simp [segs, SlabChain.totalBytes, SlabSeg.ofArray64, SlabSeg.ofRegion, hdrSeg,
      rtExtraSlots, rtGlobalSlots, rtNumClasses]
    omega
  refine SlabChain.to_region_eq htot (by omega) ?_
  simp only [SlabChain.eval, segs, SlabSeg.ofArray64, SlabSeg.ofRegion, hdrSeg, sep_emp]
  have h1 : rt + BitVec.ofNat 64 (8 * rtExtraSlots) = rt + BitVec.ofNat 64 rtGlobalsOff := rfl
  have h2 : rt + BitVec.ofNat 64 rtGlobalsOff + BitVec.ofNat 64 (8 * rtGlobalSlots) =
      rt + 33024#64 := by rw [ptr_add_nat]; rfl
  have h3 : rt + 33024#64 + BitVec.ofNat 64 (8 * rtNumClasses) = rt + 33536#64 := by
    rw [ptr_add_nat]; rfl
  have h4 : rt + 33536#64 - 33536#64 = rt := by bv_omega
  have h5 : rt + 33536#64 + BitVec.ofNat 64 136 = st.hdr.s_work := by
    simp only [st, initRtC0State, ptr_add_nat]
  have h6 : st.hdr.s_work + BitVec.ofNat 64 (8 * workCap) = st.hdr.s_cur := by
    simp only [st, initRtC0State, ptr_add_nat]
  rw [h1, h2, h3, h4, h5, h6]
  repeat rw [sep_assoc]
  repeat rw [sep_assoc] at hm
  exact hm

/-! ## 4. Heap Objects (`LcnfObj`), Footprints, and `RcSound` -/

/-- Descriptor of any R0-supported `lean_object`:
ctor (`≤ 244`), closure (`245`), `Array` (`246`), `SArray` (`248`), `String` (`249`), `MPZ` (`250`). -/
structure LcnfObj where
  addr : BitVec 64
  rc : BitVec 32
  csSz : Nat
  other : Nat
  tag : Nat
  funId : BitVec 64 := 0#64
  arity : Nat := 0
  cap : Nat := 0
  arrSize : Nat := 0
  strLen : Nat := 0
  fields : List (BitVec 64) := []
  scalarData : List UInt8 := []
  limbs : List (BitVec 64) := []
  deriving Repr, BEq

/-- 64-bit object header word (`m_rc : i32 @0`, `m_cs_sz : u16 @4`, `m_other : u8 @6`, `m_tag : u8 @7`). -/
def LcnfObj.header (o : LcnfObj) : BitVec 64 :=
  BitVec.ofNat 64 o.rc.toNat |||
  (BitVec.ofNat 64 o.csSz <<< 32) |||
  (BitVec.ofNat 64 o.other <<< 48) |||
  (BitVec.ofNat 64 o.tag <<< 56)

/-- Packed closure metadata word (`arity : u16 @16`, `num_fixed : u16 @18`, `pad : u32 @20`). -/
def cloMetaWord (arity numFixed : Nat) : BitVec 64 :=
  BitVec.ofNat 64 arity ||| (BitVec.ofNat 64 numFixed <<< 16)

/-- Packed closure metadata word of `o`. -/
def LcnfObj.cloMeta (o : LcnfObj) : BitVec 64 :=
  cloMetaWord o.arity o.fields.length

/-- Packed MPZ capacity/size word (`m_cap : u32 @8`, `m_size : u32 @12`). -/
def LcnfObj.mpzMeta (o : LcnfObj) : BitVec 64 :=
  BitVec.ofNat 64 o.cap ||| (BitVec.ofNat 64 o.arrSize <<< 32)

/-- Exact total cell size (in bytes) computed by `lcnf_rt.c` / `lcnf_free_obj`. -/
def LcnfObj.totalBytes (o : LcnfObj) : Nat :=
  if o.tag = arrayTag then 24 + 8 * o.cap
  else if o.tag = sarrayTag then align8 (24 + (o.other % 128) * o.cap)
  else if o.tag = stringTag then align8 (32 + o.cap)
  else if o.tag = mpzTag then 16 + 8 * o.cap
  else o.csSz

/-- Structural validity of a heap `LcnfObj` across all 6 R0 object representations. -/
def LcnfObj.Wf (o : LcnfObj) : Prop :=
  o.addr ≠ 0#64 ∧ o.addr.toNat % 8 = 0 ∧ 0 ≤ o.rc.toInt ∧
  o.csSz < 65536 ∧ o.other < 256 ∧ o.tag < 256 ∧
  rtMinObjBytes ≤ o.totalBytes ∧ o.totalBytes < rtMaxObjBytes ∧ o.totalBytes % 8 = 0 ∧
  if o.tag = closureTag then
    o.arity < 65536 ∧ o.fields.length < 65536 ∧ 24 + 8 * o.fields.length ≤ o.csSz ∧ o.csSz % 8 = 0
  else if o.tag = arrayTag then
    o.fields.length ≤ o.cap ∧ o.cap ≤ 33554428
  else if o.tag = sarrayTag then
    o.cap ≤ 268435455 ∧ o.arrSize < 2 ^ 64 ∧
    o.scalarData.length ≤ (o.other % 128) * o.cap
  else if o.tag = stringTag then
    o.cap ≤ 268435415 ∧ o.arrSize < 2 ^ 64 ∧ o.strLen < 2 ^ 64 ∧
    o.scalarData.length ≤ o.cap
  else if o.tag = mpzTag then
    o.limbs.length = o.cap ∧ o.cap ≤ 33554429 ∧ o.arrSize < 2 ^ 32
  else
    o.tag ≤ 244 ∧ o.fields.length = o.other ∧
    8 + 8 * o.fields.length + o.scalarData.length ≤ o.csSz ∧ o.csSz % 8 = 0

/-- Child `lean_object` fields traversed by `lcnf_dec_ref_cold` and `lcnf_mark_persistent`. -/
def LcnfObj.childFields (o : LcnfObj) : List (BitVec 64) :=
  if o.tag ≤ 244 ∨ o.tag = closureTag ∨ o.tag = arrayTag then o.fields else []

/-- Separation-logic footprint of a single heap `LcnfObj`. -/
def lcnfObjMem (o : LcnfObj) : Mem 64 → Prop :=
  if o.tag = closureTag then
    cell64 o.addr o.header ⋆
    cell64 (o.addr + 8#64) o.funId ⋆
    cell64 (o.addr + 16#64) o.cloMeta ⋆
    array64 (o.addr + 24#64) o.fields ⋆
    region (o.addr + BitVec.ofNat 64 (24 + 8 * o.fields.length))
      (o.csSz - (24 + 8 * o.fields.length))
  else if o.tag = arrayTag then
    cell64 o.addr o.header ⋆
    cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.fields.length) ⋆
    cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
    array64 (o.addr + 24#64) o.fields ⋆
    region (o.addr + BitVec.ofNat 64 (24 + 8 * o.fields.length))
      (8 * (o.cap - o.fields.length))
  else if o.tag = sarrayTag then
    cell64 o.addr o.header ⋆
    cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.arrSize) ⋆
    cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
    bytes (o.addr + 24#64) o.scalarData ⋆
    region (o.addr + BitVec.ofNat 64 (24 + o.scalarData.length))
      (o.totalBytes - (24 + o.scalarData.length))
  else if o.tag = stringTag then
    cell64 o.addr o.header ⋆
    cell64 (o.addr + 8#64) (BitVec.ofNat 64 o.arrSize) ⋆
    cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap) ⋆
    cell64 (o.addr + 24#64) (BitVec.ofNat 64 o.strLen) ⋆
    bytes (o.addr + 32#64) o.scalarData ⋆
    region (o.addr + BitVec.ofNat 64 (32 + o.scalarData.length))
      (o.totalBytes - (32 + o.scalarData.length))
  else if o.tag = mpzTag then
    cell64 o.addr o.header ⋆
    cell64 (o.addr + 8#64) o.mpzMeta ⋆
    array64 (o.addr + 16#64) o.limbs
  else
    let soff := 8 + 8 * o.fields.length
    cell64 o.addr o.header ⋆
    array64 (o.addr + 8#64) o.fields ⋆
    bytes (o.addr + BitVec.ofNat 64 soff) o.scalarData ⋆
    region (o.addr + BitVec.ofNat 64 (soff + o.scalarData.length))
      (o.csSz - (soff + o.scalarData.length))

/-- Separating conjunction of a list of heap objects. -/
def lcnfHeap : List LcnfObj → Mem 64 → Prop
  | [] => emp
  | o :: os => lcnfObjMem o ⋆ lcnfHeap os

theorem lcnfHeap_append (xs ys : List LcnfObj) :
    lcnfHeap (xs ++ ys) = (lcnfHeap xs ⋆ lcnfHeap ys) := by
  induction xs with
  | nil => simp [lcnfHeap, emp_sep]
  | cons x xs ih => simp [lcnfHeap, ih, sep_assoc]

theorem lcnfHeap_focus : ∀ (objs : List LcnfObj) {i : Nat} (_hi : i < objs.length),
    lcnfHeap objs =
      (lcnfObjMem objs[i] ⋆ (lcnfHeap (objs.take i) ⋆ lcnfHeap (objs.drop (i + 1))))
  | [], _, hi => by simp at hi
  | x :: _, 0, _ => by simp [lcnfHeap, emp_sep]
  | x :: xs, i + 1, hi => by
    have hi' : i < xs.length := by simp at hi; omega
    have ih := lcnfHeap_focus xs hi'
    simp only [List.getElem_cons_succ, lcnfHeap, List.take_succ_cons, List.drop_succ_cons]
    rw [ih, ← sep_assoc (lcnfObjMem x), sep_comm (lcnfObjMem x) (lcnfObjMem xs[i]),
      sep_assoc (lcnfObjMem xs[i]), ← sep_assoc (lcnfObjMem x)]

theorem lcnfHeap_set : ∀ (objs : List LcnfObj) {i : Nat} (_hi : i < objs.length) (obj' : LcnfObj),
    lcnfHeap (objs.set i obj') =
      (lcnfObjMem obj' ⋆ (lcnfHeap (objs.take i) ⋆ lcnfHeap (objs.drop (i + 1))))
  | [], _, hi, _ => by simp at hi
  | _ :: xs, 0, _, obj' => by simp [lcnfHeap, emp_sep]
  | x :: xs, i + 1, hi, obj' => by
    have ih := lcnfHeap_set xs (by simp at hi; omega) obj'
    simp only [List.set_cons_succ, lcnfHeap, ih, List.take_succ_cons, List.drop_succ_cons]
    rw [← sep_assoc (lcnfObjMem x), sep_comm (lcnfObjMem x) (lcnfObjMem obj'),
      sep_assoc (lcnfObjMem obj'), ← sep_assoc (lcnfObjMem x)]

theorem lcnfHeap_eraseIdx (objs : List LcnfObj) {i : Nat} :
    lcnfHeap (objs.eraseIdx i) = (lcnfHeap (objs.take i) ⋆ lcnfHeap (objs.drop (i + 1))) := by
  rw [List.eraseIdx_eq_take_drop_succ, lcnfHeap_append]

/-- Every non-scalar child pointer in `objs` resolves to an object in `objs`. -/
def lcnfHeapClosed (objs : List LcnfObj) : Prop :=
  ∀ o ∈ objs, ∀ f ∈ o.childFields, (f &&& 1#64) = 0#64 → ∃ o' ∈ objs, o'.addr = f

/-- Total references to `addr` held by non-persistent (`m_rc ≠ 0`) objects in `objs`. -/
def nonPersistRefs (objs : List LcnfObj) (addr : BitVec 64) : Nat :=
  objs.foldl (fun acc p => if p.rc = 0#32 then acc else acc + p.childFields.count addr) 0

/-- Perceus RC soundness for dropping `root`:
1. Persistent objects (`m_rc = 0`) point only to persistent objects (`m_rc = 0`).
2. Every RC-managed object (`0 < m_rc`) has `nonPersistRefs objs o.addr + (root?) ≤ o.rc.toNat`. -/
def RcSound (root : BitVec 64) (objs : List LcnfObj) : Prop :=
  (∀ p ∈ objs, p.rc = 0#32 → ∀ f ∈ p.childFields, (f &&& 1#64) = 0#64 →
    ∃ q ∈ objs, q.addr = f ∧ q.rc = 0#32) ∧
  (∀ y ∈ objs, 0 < y.rc.toInt →
    nonPersistRefs objs y.addr + (if y.addr = root then 1 else 0) ≤ y.rc.toNat)

/-- Update `m_rc` of an object while keeping all payload fields fixed. -/
def LcnfObj.withRc (o : LcnfObj) (rc' : BitVec 32) : LcnfObj :=
  { o with rc := rc' }

/-- Raw shallow cell footprint expected by `lcnf_free_obj(rt, o)`. -/
def freeObjLayout (o : BitVec 64) (bytes : Nat) (hdr : BitVec 64) : Mem 64 → Prop :=
  let tag := (hdr >>> 56).toNat
  if tag = arrayTag then
    fun m => ∃ w16 : BitVec 64,
      w16.toNat ≤ 33554428 ∧ bytes = 24 + 8 * w16.toNat ∧
      (((cell64 o hdr ⋆ region (o + 8#64) 8) ⋆ cell64 (o + 16#64) w16) ⋆
        region (o + 24#64) (bytes - 24)) m
  else if tag = sarrayTag then
    fun m => ∃ w16 : BitVec 64,
      w16.toNat ≤ 268435455 ∧
      bytes = align8 (24 + ((hdr >>> 48).toNat % 128) * w16.toNat) ∧
      (((cell64 o hdr ⋆ region (o + 8#64) 8) ⋆ cell64 (o + 16#64) w16) ⋆
        region (o + 24#64) (bytes - 24)) m
  else if tag = stringTag then
    fun m => ∃ w16 : BitVec 64,
      w16.toNat ≤ 268435415 ∧ bytes = align8 (32 + w16.toNat) ∧
      (((cell64 o hdr ⋆ region (o + 8#64) 8) ⋆ cell64 (o + 16#64) w16) ⋆
        region (o + 24#64) (bytes - 24)) m
  else if tag = mpzTag then
    fun m => ∃ w8 : BitVec 64,
      (w8 &&& 0xffffffff#64).toNat ≤ 33554429 ∧
      bytes = 16 + 8 * (w8 &&& 0xffffffff#64).toNat ∧
      ((cell64 o hdr ⋆ cell64 (o + 8#64) w8) ⋆ region (o + 16#64) (bytes - 16)) m
  else
    fun m => ((hdr >>> 32) &&& 0xffff#64).toNat = bytes ∧
      (cell64 o hdr ⋆ region (o + 8#64) (bytes - 8)) m

/-- Relational post-state for `lcnf_dec_ref_cold(rt, o)`. -/
def DecColdRel (root : BitVec 64) (objs objs' : List LcnfObj) : Prop :=
  (∃ obj ∈ objs, obj.addr = root ∧ obj.rc = 1#32) ∧
  (∀ o ∈ objs, o.Wf) ∧ lcnfHeapClosed objs ∧ lcnfHeapClosed objs' ∧
  (∀ o' ∈ objs', o'.Wf ∧ o'.addr ≠ root ∧
    ∃ o ∈ objs, o.addr = o'.addr ∧ o'.csSz = o.csSz ∧ o'.other = o.other ∧
      o'.tag = o.tag ∧ o'.funId = o.funId ∧ o'.arity = o.arity ∧
      o'.cap = o.cap ∧ o'.arrSize = o.arrSize ∧ o'.strLen = o.strLen ∧
      o'.fields = o.fields ∧ o'.scalarData = o.scalarData ∧ o'.limbs = o.limbs ∧
      ((o.rc = 0#32 ∧ o'.rc = 0#32) ∨
       (0 < o.rc.toInt ∧ 0 < o'.rc.toInt ∧ o'.rc.toInt ≤ o.rc.toInt)))

/-- Relational post-state for `lcnf_mark_persistent(rt, o)`. -/
def MarkPersistRel (root : BitVec 64) (objs objs' : List LcnfObj) : Prop :=
  objs'.length = objs.length ∧
  (∀ o ∈ objs, o.Wf) ∧ lcnfHeapClosed objs ∧ lcnfHeapClosed objs' ∧
  (∀ p ∈ objs.zip objs',
    p.2.Wf ∧ p.2.addr = p.1.addr ∧ p.2.csSz = p.1.csSz ∧ p.2.other = p.1.other ∧
    p.2.tag = p.1.tag ∧ p.2.funId = p.1.funId ∧ p.2.arity = p.1.arity ∧
    p.2.cap = p.1.cap ∧ p.2.arrSize = p.1.arrSize ∧ p.2.strLen = p.1.strLen ∧
    p.2.fields = p.1.fields ∧ p.2.scalarData = p.1.scalarData ∧ p.2.limbs = p.1.limbs ∧
    (p.1.addr = root → p.2.rc = 0#32) ∧
    (p.2.rc = p.1.rc ∨ p.2.rc = 0#32))

/-- Post-relation for `objs'` in `lcnf_clo_under` when `fc.rc ≠ 1#32`. -/
def CloUnderIncRel (fcFields : List (BitVec 64)) (objs objs' : List LcnfObj) : Prop :=
  objs'.length = objs.length ∧ lcnfHeapClosed objs' ∧
  ∀ p ∈ objs.zip objs',
    p.2.Wf ∧ p.2.addr = p.1.addr ∧ p.2.csSz = p.1.csSz ∧ p.2.other = p.1.other ∧
    p.2.tag = p.1.tag ∧ p.2.funId = p.1.funId ∧ p.2.arity = p.1.arity ∧
    p.2.cap = p.1.cap ∧ p.2.arrSize = p.1.arrSize ∧ p.2.strLen = p.1.strLen ∧
    p.2.fields = p.1.fields ∧ p.2.scalarData = p.1.scalarData ∧ p.2.limbs = p.1.limbs ∧
    ((p.1.rc = 0#32 ∧ p.2.rc = 0#32) ∨
     (0 < p.1.rc.toInt ∧ p.2.rc.toInt = p.1.rc.toInt + (fcFields.count p.1.addr : Int)))

/-! ## 5. Header Bitpacking & `LcnfObj` Region Lemmas -/

private theorem testBit_pow_sub_one (k i : Nat) :
    (2 ^ k - 1).testBit i = decide (i < k) :=
  Nat.testBit_two_pow_sub_one k i

private theorem testBit_hi32_mask (i : Nat) :
    (0xffffffff00000000 : Nat).testBit i = decide (32 ≤ i ∧ i < 64) := by
  have heq : (0xffffffff00000000 : Nat) = (2 ^ 32 - 1) <<< 32 := by decide
  rw [heq, Nat.testBit_shiftLeft, testBit_pow_sub_one]
  by_cases h1 : 32 ≤ i <;> by_cases h2 : i < 64 <;> simp [h1, h2] <;> omega

private theorem testBit_lt_of_lt {x k i : Nat} (hx : x < 2 ^ k) (hi : k ≤ i) :
    x.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide : 0 < 2) hi))

private theorem header_getLsbD (o : LcnfObj) (hcs : o.csSz < 65536) (hoth : o.other < 256)
    (_htag : o.tag < 256) (i : Nat) :
    o.header.getLsbD i =
      if i < 32 then o.rc.toNat.testBit i
      else if i < 48 then o.csSz.testBit (i - 32)
      else if i < 56 then o.other.testBit (i - 48)
      else if i < 64 then o.tag.testBit (i - 56)
      else false := by
  by_cases hi : i < 64
  · simp only [LcnfObj.header, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and]
    by_cases h32 : i < 32
    · simp [h32, show i < 48 by omega, show i < 56 by omega]
    · have hrcf : o.rc.toNat.testBit i = false :=
        testBit_lt_of_lt (k := 32) o.rc.isLt (by omega)
      by_cases h48 : i < 48
      · simp [h32, h48, show i < 56 by omega, show i - 32 < 64 by omega, hrcf]
      · have hcsf : o.csSz.testBit (i - 32) = false :=
          testBit_lt_of_lt (k := 16) (show o.csSz < 2 ^ 16 from hcs) (by omega)
        by_cases h56 : i < 56
        · simp [h32, h48, h56, show i - 32 < 64 by omega, show i - 48 < 64 by omega, hrcf, hcsf]
        · have hothf : o.other.testBit (i - 48) = false :=
            testBit_lt_of_lt (k := 8) (show o.other < 2 ^ 8 from hoth) (by omega)
          simp [h32, h48, h56, show i - 32 < 64 by omega, show i - 48 < 64 by omega,
            show i - 56 < 64 by omega, hrcf, hcsf, hothf]
  · have hge : ¬(i < 32) ∧ ¬(i < 48) ∧ ¬(i < 56) ∧ ¬(i < 64) := by omega
    have hfalse : o.header.getLsbD i = false := by
      rw [BitVec.getLsbD]
      exact testBit_lt_of_lt (k := 64) o.header.isLt (by omega)
    simp [hfalse, hge]

theorem LcnfObj.header_tag (o : LcnfObj) (hcs : o.csSz < 65536) (hoth : o.other < 256)
    (htag : o.tag < 256) : (o.header >>> 56) = BitVec.ofNat 64 o.tag := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat, header_getLsbD o hcs hoth htag]
  by_cases hi : i < 64
  · by_cases hlt : 56 + i < 64
    · simp [hi, hlt, show ¬(56 + i < 32) by omega, show ¬(56 + i < 48) by omega,
        show ¬(56 + i < 56) by omega]
    · have htf : o.tag.testBit i = false :=
        testBit_lt_of_lt (k := 8) (show o.tag < 2 ^ 8 from htag) (by omega)
      simp [hi, hlt, show ¬(56 + i < 32) by omega, show ¬(56 + i < 48) by omega,
        show ¬(56 + i < 56) by omega, htf]
  · have htf : o.tag.testBit i = false :=
      testBit_lt_of_lt (k := 8) (show o.tag < 2 ^ 8 from htag) (by omega)
    simp [hi, show ¬(56 + i < 64) by omega, show ¬(56 + i < 56) by omega,
      show ¬(56 + i < 48) by omega, show ¬(56 + i < 32) by omega, htf]

theorem LcnfObj.header_esz (o : LcnfObj) (hcs : o.csSz < 65536) (hoth : o.other < 256)
    (htag : o.tag < 256) : ((o.header >>> 48) &&& 127#64) = BitVec.ofNat 64 (o.other % 128) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat,
    header_getLsbD o hcs hoth htag]
  have h127 : (127 : Nat) = 2 ^ 7 - 1 := rfl
  rw [h127, testBit_pow_sub_one]
  by_cases hi7 : i < 7
  · have hmod : (o.other % 128).testBit i = o.other.testBit i := by
      rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.testBit_mod_two_pow]
      simp [hi7]
    simp [show i < 64 by omega, hi7, show ¬(48 + i < 32) by omega,
      show ¬(48 + i < 48) by omega, show 48 + i < 56 by omega, hmod]
  · have hmf : (o.other % 128).testBit i = false :=
      testBit_lt_of_lt (k := 7) (Nat.mod_lt _ (by decide)) (by omega)
    by_cases hi64 : i < 64 <;> simp [hi7, hi64, hmf]

theorem LcnfObj.header_csSz (o : LcnfObj) (hcs : o.csSz < 65536) (hoth : o.other < 256)
    (htag : o.tag < 256) : ((o.header >>> 32) &&& 0xffff#64) = BitVec.ofNat 64 o.csSz := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat,
    header_getLsbD o hcs hoth htag]
  have hff : (0xffff : Nat) = 2 ^ 16 - 1 := rfl
  rw [hff, testBit_pow_sub_one]
  by_cases hi16 : i < 16
  · simp [show i < 64 by omega, hi16, show ¬(32 + i < 32) by omega, show 32 + i < 48 by omega]
  · have hcf : o.csSz.testBit i = false :=
      testBit_lt_of_lt (k := 16) (show o.csSz < 2 ^ 16 from hcs) (by omega)
    by_cases hi64 : i < 64 <;> simp [hi16, hi64, hcf]

theorem LcnfObj.header_rc (o : LcnfObj) (hcs : o.csSz < 65536) (hoth : o.other < 256)
    (htag : o.tag < 256) : (o.header &&& 0xffffffff#64) = BitVec.ofNat 64 o.rc.toNat := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, header_getLsbD o hcs hoth htag]
  have hff : (0xffffffff : Nat) = 2 ^ 32 - 1 := rfl
  rw [hff, testBit_pow_sub_one]
  by_cases hi32 : i < 32
  · simp [show i < 64 by omega, hi32]
  · have hrf : o.rc.toNat.testBit i = false :=
      testBit_lt_of_lt (k := 32) o.rc.isLt (by omega)
    by_cases hi64 : i < 64 <;> simp [hi32, hi64, hrf]

theorem LcnfObj.header_clear_rc (o : LcnfObj) (hcs : o.csSz < 65536) (hoth : o.other < 256)
    (htag : o.tag < 256) :
    (o.header &&& 0xffffffff00000000#64) = (o.withRc 0#32).header := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, header_getLsbD o hcs hoth htag,
    header_getLsbD (o.withRc 0#32) hcs hoth htag, testBit_hi32_mask]
  by_cases hi64 : i < 64
  · by_cases hi32 : i < 32
    · simp [hi64, hi32, LcnfObj.withRc]
    · by_cases h48 : i < 48 <;> by_cases h56 : i < 56 <;>
        simp [hi64, hi32, h48, h56, show 32 ≤ i by omega, LcnfObj.withRc]
  · simp [hi64]

private theorem LcnfObj.mpzMeta_cap (o : LcnfObj) (hcap : o.cap < 2 ^ 32) :
    (o.mpzMeta &&& 0xffffffff#64) = BitVec.ofNat 64 o.cap := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [LcnfObj.mpzMeta, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat]
  have hff : (0xffffffff : Nat) = 2 ^ 32 - 1 := rfl
  rw [hff, testBit_pow_sub_one]
  by_cases hi32 : i < 32
  · simp [show i < 64 by omega, hi32]
  · have hcf : o.cap.testBit i = false :=
      testBit_lt_of_lt (k := 32) hcap (by omega)
    by_cases hi64 : i < 64 <;> simp [hi32, hi64, hcf]

private theorem merge_reg_l {a : BitVec 64} {n1 n2 n : Nat} {Q : Mem 64 → Prop} {m : Mem 64}
    (hsum : n1 + n2 = n) (hfit : n ≤ 2 ^ 64)
    (h : (region a n1 ⋆ (region (a + BitVec.ofNat 64 n1) n2 ⋆ Q)) m) :
    (region a n ⋆ Q) m := by
  rw [← sep_assoc] at h
  exact sep_mono (fun _ y => (region_merge_eq hsum hfit) ▸ y) h

private theorem merge_reg_2 {a : BitVec 64} {n1 n2 n : Nat} {m : Mem 64}
    (hsum : n1 + n2 = n) (hfit : n ≤ 2 ^ 64)
    (h : (region a n1 ⋆ region (a + BitVec.ofNat 64 n1) n2) m) :
    region a n m :=
  (region_merge_eq hsum hfit) ▸ h

private theorem bytes_to_reg_mem {a : BitVec 64} {bs : List UInt8} {m : Mem 64}
    (h : bytes a bs m) : region a bs.length m :=
  bytes_to_region h

/-- Any well-formed `LcnfObj` footprint weakens to `freeObjLayout o.addr o.totalBytes o.header`. -/
theorem lcnfObjMem_to_freeObjLayout {o : LcnfObj} (hwf : o.Wf) {m : Mem 64}
    (hm : lcnfObjMem o m) : freeObjLayout o.addr o.totalBytes o.header m := by
  rcases hwf with ⟨_, _, _, hcs, hoth, htag, hmin, hmax, _, hspec⟩
  have hhtag := o.header_tag hcs hoth htag
  have hhesz := o.header_esz hcs hoth htag
  have hhcs := o.header_csSz hcs hoth htag
  have htagN : (o.header >>> 56).toNat = o.tag := by
    rw [hhtag, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcsN : ((o.header >>> 32) &&& 0xffff#64).toNat = o.csSz := by
    rw [hhcs, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have heszN : (o.header >>> 48).toNat % 128 = o.other % 128 := by
    have h1 := congrArg BitVec.toNat hhesz
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h1
    change ((o.header >>> 48).toNat &&& (2 ^ 7 - 1)) = o.other % 128 % 2 ^ 64 at h1
    rw [Nat.and_two_pow_sub_one_eq_mod] at h1
    have hmodlt : o.other % 128 < 2 ^ 64 := Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
    simpa [Nat.mod_eq_of_lt hmodlt] using h1
  have hlt64 : o.totalBytes ≤ 2 ^ 64 := by unfold rtMaxObjBytes at hmax; omega
  by_cases hc : o.tag = closureTag
  · simp only [lcnfObjMem, hc, ↓reduceIte] at hm
    simp only [hc, ↓reduceIte] at hspec
    rcases hspec with ⟨_, _, hle, _⟩
    have htb : o.totalBytes = o.csSz := by
      simp [LcnfObj.totalBytes, hc, closureTag, arrayTag, sarrayTag, stringTag, mpzTag]
    have h8f : 8 * o.fields.length ≤ 2 ^ 64 := by omega
    simp only [freeObjLayout, htagN, hc, show closureTag ≠ arrayTag by decide,
      show closureTag ≠ sarrayTag by decide, show closureTag ≠ stringTag by decide,
      show closureTag ≠ mpzTag by decide, ↓reduceIte]
    refine ⟨by rw [hcsN, htb], ?_⟩
    repeat rw [sep_assoc] at hm
    have hm1 : (cell64 o.addr o.header ⋆ (region (o.addr + 8#64) 8 ⋆
        (region (o.addr + 16#64) 8 ⋆ (region (o.addr + 24#64) (8 * o.fields.length) ⋆
        region (o.addr + BitVec.ofNat 64 (24 + 8 * o.fields.length))
          (o.csSz - (24 + 8 * o.fields.length)))))) m :=
      sep_mono_r (fun _ x => sep_mono2 (fun _ h => cell64_to_region h)
        (fun _ x => sep_mono2 (fun _ h => cell64_to_region h)
          (fun _ x => sep_mono (fun _ h => array64_to_region h8f h) x) _ x) _ x) hm
    have hm2 : (cell64 o.addr o.header ⋆ (region (o.addr + 8#64) 8 ⋆
        (region (o.addr + 16#64) (8 + 8 * o.fields.length) ⋆
        region (o.addr + BitVec.ofNat 64 (24 + 8 * o.fields.length))
          (o.csSz - (24 + 8 * o.fields.length))))) m := by
      refine sep_mono_r (fun _ x => sep_mono_r (fun _ y => ?_) x) hm1
      rw [show o.addr + 24#64 = (o.addr + 16#64) + BitVec.ofNat 64 8 by rw [ptr_add_nat]] at y
      exact merge_reg_l rfl (by omega) y
    have hm3 : (cell64 o.addr o.header ⋆
        (region (o.addr + 8#64) (16 + 8 * o.fields.length) ⋆
        region (o.addr + BitVec.ofNat 64 (24 + 8 * o.fields.length))
          (o.csSz - (24 + 8 * o.fields.length)))) m := by
      refine sep_mono_r (fun _ x => ?_) hm2
      rw [show o.addr + 16#64 = (o.addr + 8#64) + BitVec.ofNat 64 8 by rw [ptr_add_nat]] at x
      exact merge_reg_l (by omega) (by omega) x
    have hm4 : (cell64 o.addr o.header ⋆ region (o.addr + 8#64) (o.csSz - 8)) m := by
      refine sep_mono_r (fun _ x => ?_) hm3
      rw [show o.addr + BitVec.ofNat 64 (24 + 8 * o.fields.length) =
        (o.addr + 8#64) + BitVec.ofNat 64 (16 + 8 * o.fields.length) by
        rw [ptr_add_nat, show 8 + (16 + 8 * o.fields.length) = 24 + 8 * o.fields.length by omega]] at x
      exact merge_reg_2 (by omega) (by omega) x
    simpa [htb] using hm4
  · by_cases ha : o.tag = arrayTag
    · simp only [lcnfObjMem, ha, show arrayTag ≠ closureTag by decide, ↓reduceIte] at hm
      simp only [ha, show arrayTag ≠ closureTag by decide, ↓reduceIte] at hspec
      rcases hspec with ⟨hfle, hcaple⟩
      have htb : o.totalBytes = 24 + 8 * o.cap := by simp [LcnfObj.totalBytes, ha, arrayTag]
      have h8f : 8 * o.fields.length ≤ 2 ^ 64 := by omega
      simp only [freeObjLayout, htagN, ha, ↓reduceIte]
      refine ⟨BitVec.ofNat 64 o.cap,
        by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hcaple,
        by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact htb, ?_⟩
      rw [sep_assoc] at hm
      have hm1 : (((cell64 o.addr o.header ⋆ region (o.addr + 8#64) 8) ⋆
          cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap)) ⋆
          (region (o.addr + 24#64) (8 * o.fields.length) ⋆
          region (o.addr + BitVec.ofNat 64 (24 + 8 * o.fields.length))
            (8 * (o.cap - o.fields.length)))) m :=
        sep_mono2 (fun _ x => sep_mono (fun _ y => sep_mono_r (fun _ h => cell64_to_region h) y) x)
          (fun _ x => sep_mono (fun _ h => array64_to_region h8f h) x) _ hm
      have hmrg := region_merge_eq (a := o.addr + 24#64) (n1 := 8 * o.fields.length)
        (n2 := 8 * (o.cap - o.fields.length)) (n := o.totalBytes - 24) (by omega) (by omega)
      rw [ptr_add_nat] at hmrg
      exact sep_mono_r (fun _ x => hmrg ▸ x) hm1
    · by_cases hsa : o.tag = sarrayTag
      · simp only [lcnfObjMem, hsa, show sarrayTag ≠ closureTag by decide,
          show sarrayTag ≠ arrayTag by decide, ↓reduceIte] at hm
        simp only [hsa, show sarrayTag ≠ closureTag by decide,
          show sarrayTag ≠ arrayTag by decide, ↓reduceIte] at hspec
        rcases hspec with ⟨hcaple, _, hdatle⟩
        have htb : o.totalBytes = align8 (24 + (o.other % 128) * o.cap) := by
          simp [LcnfObj.totalBytes, hsa, arrayTag, sarrayTag]
        have h24 : 24 + o.scalarData.length ≤ o.totalBytes := by
          rw [htb]; exact Nat.le_trans (by omega) (align8_ge _)
        simp only [freeObjLayout, htagN, hsa, show sarrayTag ≠ arrayTag by decide, ↓reduceIte]
        refine ⟨BitVec.ofNat 64 o.cap,
          by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hcaple,
          by rw [heszN, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show o.cap < 2 ^ 64 by omega)]; exact htb,
          ?_⟩
        rw [sep_assoc] at hm
        have hm1 : (((cell64 o.addr o.header ⋆ region (o.addr + 8#64) 8) ⋆
            cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap)) ⋆
            (region (o.addr + 24#64) o.scalarData.length ⋆
            region (o.addr + BitVec.ofNat 64 (24 + o.scalarData.length))
              (o.totalBytes - (24 + o.scalarData.length)))) m :=
          sep_mono2 (fun _ x => sep_mono (fun _ y => sep_mono_r (fun _ h => cell64_to_region h) y) x)
            (fun _ x => sep_mono (fun _ h => bytes_to_reg_mem h) x) _ hm
        have hmrg := region_merge_eq (a := o.addr + 24#64) (n1 := o.scalarData.length)
          (n2 := o.totalBytes - (24 + o.scalarData.length)) (n := o.totalBytes - 24)
          (by omega) (by omega)
        rw [ptr_add_nat] at hmrg
        exact sep_mono_r (fun _ x => hmrg ▸ x) hm1
      · by_cases hstr : o.tag = stringTag
        · simp only [lcnfObjMem, hstr, show stringTag ≠ closureTag by decide,
            show stringTag ≠ arrayTag by decide, show stringTag ≠ sarrayTag by decide,
            ↓reduceIte] at hm
          simp only [hstr, show stringTag ≠ closureTag by decide,
            show stringTag ≠ arrayTag by decide, show stringTag ≠ sarrayTag by decide,
            ↓reduceIte] at hspec
          rcases hspec with ⟨hcaple, _, _, hdatle⟩
          have htb : o.totalBytes = align8 (32 + o.cap) := by
            simp [LcnfObj.totalBytes, hstr, arrayTag, sarrayTag, stringTag]
          have h32 : 32 + o.scalarData.length ≤ o.totalBytes := by
            rw [htb]; exact Nat.le_trans (by omega) (align8_ge _)
          simp only [freeObjLayout, htagN, hstr, show stringTag ≠ arrayTag by decide,
            show stringTag ≠ sarrayTag by decide, ↓reduceIte]
          refine ⟨BitVec.ofNat 64 o.cap,
            by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hcaple,
            by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact htb, ?_⟩
          rw [sep_assoc, sep_assoc] at hm
          have hm1 : (((cell64 o.addr o.header ⋆ region (o.addr + 8#64) 8) ⋆
              cell64 (o.addr + 16#64) (BitVec.ofNat 64 o.cap)) ⋆
              (region (o.addr + 24#64) 8 ⋆ (region (o.addr + 32#64) o.scalarData.length ⋆
              region (o.addr + BitVec.ofNat 64 (32 + o.scalarData.length))
                (o.totalBytes - (32 + o.scalarData.length))))) m :=
            sep_mono2 (fun _ x => sep_mono (fun _ y => sep_mono_r (fun _ h => cell64_to_region h) y) x)
              (fun _ x => sep_mono2 (fun _ h => cell64_to_region h)
                (fun _ y => sep_mono (fun _ h => bytes_to_reg_mem h) y) _ x) _ hm
          refine sep_mono_r (fun m' x => ?_) hm1
          have hm2 : (region (o.addr + 24#64) (8 + o.scalarData.length) ⋆
              region (o.addr + BitVec.ofNat 64 (32 + o.scalarData.length))
                (o.totalBytes - (32 + o.scalarData.length))) m' := by
            rw [show o.addr + 32#64 = (o.addr + 24#64) + BitVec.ofNat 64 8 by rw [ptr_add_nat]] at x
            exact merge_reg_l (by omega) (by omega) x
          rw [show o.addr + BitVec.ofNat 64 (32 + o.scalarData.length) =
            (o.addr + 24#64) + BitVec.ofNat 64 (8 + o.scalarData.length) by
            rw [ptr_add_nat, show 24 + (8 + o.scalarData.length) = 32 + o.scalarData.length by omega]] at hm2
          exact merge_reg_2 (by omega) (by omega) hm2
        · by_cases hmpz : o.tag = mpzTag
          · simp only [lcnfObjMem, hmpz, show mpzTag ≠ closureTag by decide,
              show mpzTag ≠ arrayTag by decide, show mpzTag ≠ sarrayTag by decide,
              show mpzTag ≠ stringTag by decide, ↓reduceIte] at hm
            simp only [hmpz, show mpzTag ≠ closureTag by decide,
              show mpzTag ≠ arrayTag by decide, show mpzTag ≠ sarrayTag by decide,
              show mpzTag ≠ stringTag by decide, ↓reduceIte] at hspec
            rcases hspec with ⟨hlim, hcaple, _⟩
            have htb : o.totalBytes = 16 + 8 * o.cap := by
              simp [LcnfObj.totalBytes, hmpz, arrayTag, sarrayTag, stringTag, mpzTag]
            have hcap32 : o.cap < 2 ^ 32 := by omega
            have h8l : 8 * o.limbs.length ≤ 2 ^ 64 := by omega
            simp only [freeObjLayout, htagN, hmpz, show mpzTag ≠ arrayTag by decide,
              show mpzTag ≠ sarrayTag by decide, show mpzTag ≠ stringTag by decide, ↓reduceIte]
            refine ⟨o.mpzMeta,
              by rw [o.mpzMeta_cap hcap32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hcaple,
              by rw [o.mpzMeta_cap hcap32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact htb, ?_⟩
            exact sep_mono_r (fun _ h => by simpa [htb, hlim] using array64_to_region h8l h) hm
          · simp only [lcnfObjMem, hc, ha, hsa, hstr, hmpz, ↓reduceIte] at hm
            simp only [hc, ha, hsa, hstr, hmpz, ↓reduceIte] at hspec
            rcases hspec with ⟨_, _, hle, _⟩
            have htb : o.totalBytes = o.csSz := by
              simp [LcnfObj.totalBytes, ha, hsa, hstr, hmpz]
            have h8f : 8 * o.fields.length ≤ 2 ^ 64 := by omega
            simp only [freeObjLayout, htagN, ha, hsa, hstr, hmpz, ↓reduceIte]
            refine ⟨by rw [hcsN, htb], ?_⟩
            repeat rw [sep_assoc] at hm
            have hm1 : (cell64 o.addr o.header ⋆
                (region (o.addr + 8#64) (8 * o.fields.length) ⋆
                (region (o.addr + BitVec.ofNat 64 (8 + 8 * o.fields.length)) o.scalarData.length ⋆
                region (o.addr + BitVec.ofNat 64 (8 + 8 * o.fields.length + o.scalarData.length))
                  (o.csSz - (8 + 8 * o.fields.length + o.scalarData.length))))) m :=
              sep_mono_r (fun _ x => sep_mono2 (fun _ h => array64_to_region h8f h)
                (fun _ y => sep_mono (fun _ h => bytes_to_reg_mem h) y) _ x) hm
            refine sep_mono_r (fun m' x => ?_) hm1
            have hm2 : (region (o.addr + 8#64) (8 * o.fields.length + o.scalarData.length) ⋆
                region (o.addr + BitVec.ofNat 64 (8 + 8 * o.fields.length + o.scalarData.length))
                  (o.csSz - (8 + 8 * o.fields.length + o.scalarData.length))) m' := by
              rw [show o.addr + BitVec.ofNat 64 (8 + 8 * o.fields.length) =
                (o.addr + 8#64) + BitVec.ofNat 64 (8 * o.fields.length) by rw [ptr_add_nat]] at x
              exact merge_reg_l (by omega) (by omega) x
            rw [show o.addr + BitVec.ofNat 64 (8 + 8 * o.fields.length + o.scalarData.length) =
              (o.addr + 8#64) + BitVec.ofNat 64 (8 * o.fields.length + o.scalarData.length) by
              rw [ptr_add_nat, show 8 + (8 * o.fields.length + o.scalarData.length) =
                8 + 8 * o.fields.length + o.scalarData.length by omega]] at hm2
            simpa [htb] using merge_reg_2 (by omega) (by omega) hm2

/-! ## 6. R0 Function `Spec` Contracts (`rtC0SpecEntries`, `rtC0Env`) -/

/-- `lcnf_alloc(rt, sz) -> p`: 8-byte aligned allocator via freelist, `large_free`, or bump. -/
def lcnfAllocSpec : Spec [i64, i64] [i64] := fun (rt, sz, ()) m Q _ =>
  let bytes := align8 sz.toNat
  ∃ (st : RtC0State) (R : Mem 64 → Prop),
    sz.toNat ≤ 268435448 ∧ rtMinObjBytes ≤ bytes ∧ bytes < rtMaxObjBytes ∧
    (st.hasFree bytes ∨ bytes ≤ st.rem) ∧
    (rtC0Inv rt st ⋆ R) m ∧
    ∀ p st' m',
      p ≠ 0#64 → p.toNat % 8 = 0 →
      st'.PreservesMeta st → st'.rem ≤ st.rem →
      (rtC0Inv rt st' ⋆ region p bytes ⋆ R) m' → Q (p, ()) m'

/-- `lcnf_free_obj(rt, o) -> ()`: shallowly frees cell `o` (no-op on tagged scalars). -/
def lcnfFreeObjSpec : Spec [i64, i64] [] := fun (rt, o, ()) m Q _ =>
  if (o &&& 1#64) ≠ 0#64 then
    ∃ (st : RtC0State) (R : Mem 64 → Prop), (rtC0Inv rt st ⋆ R) m ∧ Q () m
  else
    ∃ (st : RtC0State) (hdr : BitVec 64) (bytes : Nat) (R : Mem 64 → Prop),
      o ≠ 0#64 ∧ o.toNat % 8 = 0 ∧
      rtMinObjBytes ≤ bytes ∧ bytes < rtMaxObjBytes ∧ bytes % 8 = 0 ∧
      (rtC0Inv rt st ⋆ freeObjLayout o bytes hdr ⋆ R) m ∧
      ∀ st' m', st'.PreservesMeta st → st'.rem = st.rem →
        (rtC0Inv rt st' ⋆ R) m' → Q () m'

/-- `lcnf_dec_ref_cold(rt, o) -> ()`: iteratively frees exclusive `o` and cascades across
RC-sound closed heap `objs`. -/
def lcnfDecRefColdSpec : Spec [i64, i64] [] := fun (rt, o, ()) m Q _ =>
  (o &&& 1#64) = 0#64 ∧
  ∃ (st : RtC0State) (objs : List LcnfObj) (R : Mem 64 → Prop),
    objs.length ≤ st.workCap ∧
    (rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R) m ∧
    (∃ obj ∈ objs, obj.addr = o ∧ obj.rc = 1#32) ∧
    (∀ obj ∈ objs, obj.Wf) ∧ lcnfHeapClosed objs ∧ RcSound o objs ∧
    ∀ st' objs' m',
      st'.PreservesMeta st → st'.rem = st.rem →
      DecColdRel o objs objs' →
      (rtC0Inv rt st' ⋆ lcnfHeap objs' ⋆ R) m' → Q () m'

/-- `lcnf_mark_persistent(rt, o) -> ()`: marks `o` and all reachable heap objects persistent. -/
def lcnfMarkPersistentSpec : Spec [i64, i64] [] := fun (rt, o, ()) m Q _ =>
  if (o &&& 1#64) ≠ 0#64 then
    ∃ (st : RtC0State) (R : Mem 64 → Prop), (rtC0Inv rt st ⋆ R) m ∧ Q () m
  else
    ∃ (st : RtC0State) (objs : List LcnfObj) (R : Mem 64 → Prop),
      objs.length ≤ st.workCap ∧
      (rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R) m ∧
      (∃ obj ∈ objs, obj.addr = o) ∧
      (∀ obj ∈ objs, obj.Wf) ∧ lcnfHeapClosed objs ∧
      ∀ st' objs' m',
        st'.PreservesMeta st → st'.rem = st.rem →
        MarkPersistRel o objs objs' →
        (rtC0Inv rt st' ⋆ lcnfHeap objs' ⋆ R) m' → Q () m'

/-- `lcnf_clo_under(rt, f, k) -> c`: allocates extended closure and copies/updates captures. -/
def lcnfCloUnderSpec : Spec [i64, i64, i64] [i64] := fun (rt, f, k, ()) m Q _ =>
  ∃ (st : RtC0State) (fc : LcnfObj) (objs : List LcnfObj) (R : Mem 64 → Prop),
    let nfix := fc.fields.length
    let sz := 24 + 8 * (nfix + k.toNat)
    fc.addr = f ∧ fc.tag = closureTag ∧ fc.Wf ∧
    (∀ obj ∈ objs, obj.Wf) ∧ lcnfHeapClosed objs ∧
    (∀ p ∈ fc.fields, (p &&& 1#64) = 0#64 → ∃ obj ∈ objs, obj.addr = p) ∧
    (∀ obj ∈ objs, 0 < obj.rc.toInt →
      obj.rc.toInt + (fc.fields.count obj.addr : Int) < 2147483648) ∧
    0 < k.toNat ∧ k.toNat ≤ 8188 ∧ nfix + k.toNat ≤ 8188 ∧
    rtMinObjBytes ≤ sz ∧ sz < 65536 ∧ (st.hasFree sz ∨ sz ≤ st.rem) ∧
    (rtC0Inv rt st ⋆ lcnfObjMem fc ⋆ lcnfHeap objs ⋆ R) m ∧
    ∀ c st' objs' m',
      let cHdr :=
        (1#64 : BitVec 64) ||| (BitVec.ofNat 64 sz <<< 32) |||
        (BitVec.ofNat 64 closureTag <<< 56)
      let cMeta := cloMetaWord fc.arity (nfix + k.toNat)
      c ≠ 0#64 → c.toNat % 8 = 0 →
      st'.PreservesMeta st → st'.rem ≤ st.rem →
      (if fc.rc = 1#32 then objs' = objs else CloUnderIncRel fc.fields objs objs') →
      (rtC0Inv rt st' ⋆ cell64 c cHdr ⋆ cell64 (c + 8#64) fc.funId ⋆
        cell64 (c + 16#64) cMeta ⋆ array64 (c + 24#64) fc.fields ⋆
        region (c + BitVec.ofNat 64 (24 + 8 * nfix)) (8 * k.toNat) ⋆
        (if fc.rc = 1#32 then emp else
          let rc' := fc.rc - if fc.rc = 0#32 then 0#32 else 1#32
          lcnfObjMem (fc.withRc rc')) ⋆
        lcnfHeap objs' ⋆ R) m' →
      Q (c, ()) m'

/-- Monotonicity proofs for `Spec.Mono` and `Env.ofTable`. -/
theorem lcnfAllocSpec_mono : lcnfAllocSpec.Mono := by
  rintro ⟨rt, sz, ⟨⟩⟩ m Q Q' X X' hQ _ ⟨st, R, h1, h2, h3, h4, hm, hk⟩
  exact ⟨st, R, h1, h2, h3, h4, hm, fun p st' m' hp1 hp2 hpr hrem hm' =>
    hQ _ m' (hk p st' m' hp1 hp2 hpr hrem hm')⟩

theorem lcnfFreeObjSpec_mono : lcnfFreeObjSpec.Mono := by
  rintro ⟨rt, o, ⟨⟩⟩ m Q Q' X X' hQ _ h
  dsimp only [lcnfFreeObjSpec] at h ⊢
  split at h
  · split
    · rcases h with ⟨st, R, hm, hq⟩
      exact ⟨st, R, hm, hQ _ m hq⟩
    · contradiction
  · split
    · contradiction
    · rcases h with ⟨st, hdr, bytes, R, h0, h1, h2, h3, h4, hm, hk⟩
      exact ⟨st, hdr, bytes, R, h0, h1, h2, h3, h4, hm, fun st' m' hpr hrem hm' =>
        hQ _ m' (hk st' m' hpr hrem hm')⟩

theorem lcnfDecRefColdSpec_mono : lcnfDecRefColdSpec.Mono := by
  rintro ⟨rt, o, ⟨⟩⟩ m Q Q' X X' hQ _ ⟨h0, st, objs, R, hcap, hm, hroot, hwf, hcl, hrc, hk⟩
  exact ⟨h0, st, objs, R, hcap, hm, hroot, hwf, hcl, hrc, fun st' objs' m' hpr hrem hrel hm' =>
    hQ _ m' (hk st' objs' m' hpr hrem hrel hm')⟩

theorem lcnfMarkPersistentSpec_mono : lcnfMarkPersistentSpec.Mono := by
  rintro ⟨rt, o, ⟨⟩⟩ m Q Q' X X' hQ _ h
  dsimp only [lcnfMarkPersistentSpec] at h ⊢
  split at h
  · split
    · rcases h with ⟨st, R, hm, hq⟩
      exact ⟨st, R, hm, hQ _ m hq⟩
    · contradiction
  · split
    · contradiction
    · rcases h with ⟨st, objs, R, hcap, hm, hroot, hwf, hcl, hk⟩
      exact ⟨st, objs, R, hcap, hm, hroot, hwf, hcl,
        fun st' objs' m' hpr hrem hrel hm' => hQ _ m' (hk st' objs' m' hpr hrem hrel hm')⟩

theorem lcnfCloUnderSpec_mono : lcnfCloUnderSpec.Mono := by
  rintro ⟨rt, f, k, ⟨⟩⟩ m Q Q' X X' hQ _
    ⟨st, fc, objs, R, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hm, hk⟩
  exact ⟨st, fc, objs, R, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hm,
    fun c st' objs' m' hc1 hc2 hpr hrem hrel hm' =>
      hQ _ m' (hk c st' objs' m' hc1 hc2 hpr hrem hrel hm')⟩

/-- Specification table and closed `Env` for `rtR0Mod`. -/
def rtC0SpecEntries : List SpecEntry :=
  [ SpecEntry.ofFn lcnf_alloc lcnfAllocSpec true,
    SpecEntry.ofFn lcnf_free_obj lcnfFreeObjSpec true,
    SpecEntry.ofFn lcnf_dec_ref_cold lcnfDecRefColdSpec true,
    SpecEntry.ofFn lcnf_mark_persistent lcnfMarkPersistentSpec true,
    SpecEntry.ofFn lcnf_clo_under lcnfCloUnderSpec true ]

theorem rtC0SpecEntries_nodup : (rtC0SpecEntries.map SpecEntry.name).Nodup := by decide

def rtC0Env : Env := Env.ofTable rtC0SpecEntries

theorem rtC0Env_alloc (xs : Tup Val [i64, i64]) (m : Mem 64) (Q : Post [i64]) (X : XPost)
    (h : lcnfAllocSpec xs m Q X) : rtC0Env "lcnf_alloc" [i64, i64] [i64] xs m Q X :=
  Env.ofTable_of_mem (tbl := rtC0SpecEntries) (e := SpecEntry.ofFn lcnf_alloc lcnfAllocSpec true)
    (by simp [rtC0SpecEntries]) rtC0SpecEntries_nodup h

theorem rtC0Env_free_obj (xs : Tup Val [i64, i64]) (m : Mem 64) (Q : Post []) (X : XPost)
    (h : lcnfFreeObjSpec xs m Q X) : rtC0Env "lcnf_free_obj" [i64, i64] [] xs m Q X :=
  Env.ofTable_of_mem (tbl := rtC0SpecEntries) (e := SpecEntry.ofFn lcnf_free_obj lcnfFreeObjSpec true)
    (by simp [rtC0SpecEntries]) rtC0SpecEntries_nodup h

theorem rtC0Env_dec_ref_cold (xs : Tup Val [i64, i64]) (m : Mem 64) (Q : Post []) (X : XPost)
    (h : lcnfDecRefColdSpec xs m Q X) :
    rtC0Env "lcnf_dec_ref_cold" [i64, i64] [] xs m Q X :=
  Env.ofTable_of_mem (tbl := rtC0SpecEntries)
    (e := SpecEntry.ofFn lcnf_dec_ref_cold lcnfDecRefColdSpec true)
    (by simp [rtC0SpecEntries]) rtC0SpecEntries_nodup h

theorem rtC0Env_mark_persistent (xs : Tup Val [i64, i64]) (m : Mem 64) (Q : Post []) (X : XPost)
    (h : lcnfMarkPersistentSpec xs m Q X) :
    rtC0Env "lcnf_mark_persistent" [i64, i64] [] xs m Q X :=
  Env.ofTable_of_mem (tbl := rtC0SpecEntries)
    (e := SpecEntry.ofFn lcnf_mark_persistent lcnfMarkPersistentSpec true)
    (by simp [rtC0SpecEntries]) rtC0SpecEntries_nodup h

theorem rtC0Env_clo_under (xs : Tup Val [i64, i64, i64]) (m : Mem 64) (Q : Post [i64]) (X : XPost)
    (h : lcnfCloUnderSpec xs m Q X) :
    rtC0Env "lcnf_clo_under" [i64, i64, i64] [i64] xs m Q X :=
  Env.ofTable_of_mem (tbl := rtC0SpecEntries)
    (e := SpecEntry.ofFn lcnf_clo_under lcnfCloUnderSpec true)
    (by simp [rtC0SpecEntries]) rtC0SpecEntries_nodup h

end LeanQbe.T.LeanLCNF
