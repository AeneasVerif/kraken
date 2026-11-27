module

public import LeanQbe.T.LeanLCNF.LcnfC0BigNum
public import LeanQbe.T.LeanLCNF.LcnfC0BigNumMath
public import LeanQbe.T.LeanLCNF.LcnfC0RtSpec
public import LeanQbe.T.LeanLCNF.Lower
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.SlabChain
import all Kraken.Separation

/-!
# Canonical `MPZ`/`Nat`/`Int` Specifications & Contracts for `LcnfC0BigNum` (Milestone R1)

Formal specification layer for `LeanQbe.T.LeanLCNF.LcnfC0BigNum`:

1. **Shared R0 runtime state**: R1 contracts are stated directly over `LcnfC0RtSpec`'s
   `RtC0State`, `rtC0Inv`, `LcnfObj`, `lcnfHeap`, `RcSound`, `DecColdRel`, `lcnfAllocSpec`, and
   `lcnfDecRefColdSpec` (the R1 header `LcnfC0BaseRt` is layout-identical but never unfolded).
2. **Canonical `Nat` & `Int` (`MPZ`) representations**:
   - `mpzNatCanon obj n`: trimmed `limbs`, `other = 0`, `limbsVal obj.limbs = n`, `2 ^ 63 ≤ n`.
   - `mpzIntCanon obj z`: trimmed `limbs`, `other ∈ {0, 1}`, `other = 1 ↔ z < 0`,
     `limbsVal obj.limbs = z.natAbs`, `z < -(2 ^ 62) ∨ 2 ^ 62 ≤ z` (non-overlapping with `2*z + 1`).
   - `natRep w n objs` and `intRep w z objs`, plus `limbLenNat`.
3. **Contracts for all 34 C0 functions + 2 R0 externs (`rtR1SpecEntries`, `rtR1Env`)**:
   Full `Spec` contracts and lookup theorems enabling modular `Func.wp` verification and
   `ModuleOk rtR1Env rtR1Mod`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.LeanLCNF

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil

/-! ## 1. Shared R0 Runtime State (`LcnfC0RtSpec`) -/

theorem RtC0State.bounded48_of_preserves {st st' : RtC0State}
    (hb : st.Bounded48) (hp : st'.PreservesMeta st) : st'.Bounded48 := by
  rcases hp with ⟨_, _, _, hs, _⟩
  show st'.hdr.s_end.toNat < 2 ^ 48
  rw [← hs]
  exact hb

/-! ## 2. Canonical `MPZ` / `Nat` / `Int` Representation & Bitpacking Lemmas -/

/-- Maximum MPZ limb count supported by `LcnfC0Rt` (`268435448` total object bytes). -/
def mpzMaxLimbs : Nat := 0x01fffffd

/-- Unique canonical limb count of `n : Nat` (`0` for `0`, `n.log2 / 64 + 1` for `n > 0`). -/
def limbLenNat (n : Nat) : Nat :=
  if n = 0 then 0 else n.log2 / 64 + 1

theorem limbLenNat_zero : limbLenNat 0 = 0 := rfl

theorem limbLenNat_pos_iff {n : Nat} : 0 < limbLenNat n ↔ 0 < n := by
  unfold limbLenNat
  split <;> omega

theorem limbLenNat_eq_one_of_pos_lt {n : Nat} (hp : 0 < n) (hlt : n < 2 ^ 64) :
    limbLenNat n = 1 := by
  unfold limbLenNat
  have hnz : n ≠ 0 := by omega
  have hlog : n.log2 < 64 := (Nat.log2_lt hnz).mpr hlt
  simp [hnz, Nat.div_eq_of_lt hlog]

theorem limbLenNat_lt_pow {n : Nat} : n < 2 ^ (64 * limbLenNat n) := by
  by_cases h0 : n = 0
  · subst h0; simp [limbLenNat]
  · unfold limbLenNat
    simp only [h0, ↓reduceIte]
    have hlog := Nat.lt_log2_self (n := n)
    have hle : n.log2 + 1 ≤ 64 * (n.log2 / 64 + 1) := by omega
    exact Nat.lt_of_lt_of_le (Nat.log2_lt h0 |>.mp (Nat.lt_succ_self _))
      (Nat.pow_le_pow_right (by decide) hle)

theorem pow_le_of_limbLenNat {n : Nat} (hn : 0 < n) :
    2 ^ (64 * (limbLenNat n - 1)) ≤ n := by
  unfold limbLenNat
  have hnz : n ≠ 0 := by omega
  simp only [hnz, ↓reduceIte, Nat.add_sub_cancel]
  have h1 : 64 * (n.log2 / 64) ≤ n.log2 := by omega
  exact Nat.le_trans (Nat.pow_le_pow_right (by decide) h1) ((Nat.le_log2 hnz).mp (Nat.le_refl _))

theorem limbLenNat_mono {a b : Nat} (h : a ≤ b) : limbLenNat a ≤ limbLenNat b := by
  by_cases ha : a = 0
  · subst ha; simp [limbLenNat]
  · have hb : b ≠ 0 := by omega
    unfold limbLenNat
    simp only [ha, hb, ↓reduceIte]
    have hl : a.log2 ≤ b.log2 :=
      (Nat.le_log2 hb).mpr (Nat.le_trans ((Nat.le_log2 ha).mp (Nat.le_refl _)) h)
    omega

theorem limbLenNat_eq_length_of_trimmed {xs : List (BitVec 64)}
    (hne : xs ≠ []) (hlast : xs.getLast! ≠ 0#64) :
    limbLenNat (limbsVal xs) = xs.length := by
  have hsplit : xs = xs.dropLast ++ [xs.getLast!] := by
    rw [list_getLast!_eq_getLast xs hne]
    exact (List.dropLast_concat_getLast hne).symm
  have hval : limbsVal xs = limbsVal xs.dropLast +
    2 ^ (64 * xs.dropLast.length) * xs.getLast!.toNat := by
    conv => lhs; rw [hsplit, limbsVal_snoc]
  have hlen : xs.dropLast.length = xs.length - 1 := List.length_dropLast
  have hhi_pos : 0 < xs.getLast!.toNat := bv64_toNat_pos_of_ne hlast
  have hpow_pos : 0 < 2 ^ (64 * (xs.length - 1)) := Nat.pow_pos (by decide)
  have hlb : 2 ^ (64 * (xs.length - 1)) ≤ limbsVal xs := by
    rw [hval, hlen]
    have : 2 ^ (64 * (xs.length - 1)) * 1 ≤ 2 ^ (64 * (xs.length - 1)) * xs.getLast!.toNat :=
      Nat.mul_le_mul_left _ hhi_pos
    omega
  have hub : limbsVal xs < 2 ^ (64 * xs.length) := limbsVal_lt_pow xs
  have hpos : limbsVal xs ≠ 0 := by omega
  have hl1 : 64 * (xs.length - 1) ≤ (limbsVal xs).log2 := (Nat.le_log2 hpos).mpr hlb
  have hl2 : (limbsVal xs).log2 < 64 * xs.length := (Nat.log2_lt hpos).mpr hub
  have hlen_pos : 1 ≤ xs.length := by
    cases xs with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  unfold limbLenNat
  simp only [hpos, ↓reduceIte]
  omega

theorem limbLenNat_trimLenLoop {xs : List (BitVec 64)} {n : Nat} (hn : n ≤ xs.length) :
    limbLenNat (limbsVal (xs.take n)) = trimLenLoop xs n := by
  rw [← limbsVal_trimLenLoop xs n hn]
  cases h : trimLenLoop xs n with
  | zero => simp [limbLenNat]
  | succ m =>
    have hlt : m + 1 ≤ xs.length := by rw [← h]; exact Nat.le_trans (trimLenLoop_le xs n) hn
    have hnz := trimLenLoop_nonzero xs n (by omega)
    rw [h, Nat.add_sub_cancel] at hnz
    have hne : xs.take (m + 1) ≠ [] := by
      intro heq
      have := congrArg List.length heq
      simp [List.length_take_of_le hlt] at this
    have hlast : (xs.take (m + 1)).getLast! ≠ 0#64 := by
      have hm : m < (xs.take (m + 1)).length := by simp [List.length_take_of_le hlt]
      rw [list_getLast!_eq_getLast _ hne, List.getLast_eq_getElem hne]
      simp only [List.length_take_of_le hlt, Nat.add_sub_cancel, List.getElem_take]
      simpa [getElem!_pos xs m (by omega)] using hnz
    rw [limbLenNat_eq_length_of_trimmed hne hlast, List.length_take_of_le hlt]

/-- Boxed canonical MPZ `Nat` invariant (`other = 0`, trimmed limbs, `val ≥ 2^63`). -/
def mpzNatCanon (obj : LcnfObj) (n : Nat) : Prop :=
  obj.Wf ∧
  obj.tag = mpzTag ∧
  obj.other = 0 ∧
  obj.arrSize = obj.limbs.length ∧
  1 ≤ obj.limbs.length ∧
  obj.limbs.length ≤ mpzMaxLimbs ∧
  obj.limbs.getLast! ≠ 0#64 ∧
  limbsVal obj.limbs = n ∧
  2 ^ 63 ≤ n

/-- Representation predicate for Lean runtime `Nat` values (`(2*n + 1)` scalar or boxed MPZ). -/
def natRep (w : BitVec 64) (n : Nat) (objs : List LcnfObj) : Prop :=
  if n < 2 ^ 63 then w = BitVec.ofNat 64 (2 * n + 1)
  else (w &&& 1#64) = 0#64 ∧ ∃ obj ∈ objs, obj.addr = w ∧ mpzNatCanon obj n

/-- Boxed canonical MPZ `Int` invariant (`other ∈ {0, 1}`, trimmed limbs, `|z| ∉ [-2^62, 2^62)`). -/
def mpzIntCanon (obj : LcnfObj) (z : Int) : Prop :=
  obj.Wf ∧
  obj.tag = mpzTag ∧
  (obj.other = 0 ∨ obj.other = 1) ∧
  obj.arrSize = obj.limbs.length ∧
  1 ≤ obj.limbs.length ∧
  obj.limbs.length ≤ mpzMaxLimbs ∧
  obj.limbs.getLast! ≠ 0#64 ∧
  limbsVal obj.limbs = z.natAbs ∧
  (obj.other = 1 ↔ z < 0) ∧
  (z < -(2 ^ 62 : Int) ∨ (2 ^ 62 : Int) ≤ z)

/-- Representation predicate for Lean runtime `Int` values (`[-2^62, 2^62)` scalar or boxed MPZ). -/
def intRep (w : BitVec 64) (z : Int) (objs : List LcnfObj) : Prop :=
  if -(2 ^ 62 : Int) ≤ z ∧ z < (2 ^ 62 : Int) then w = BitVec.ofInt 64 (2 * z + 1)
  else (w &&& 1#64) = 0#64 ∧ ∃ obj ∈ objs, obj.addr = w ∧ mpzIntCanon obj z

theorem limbLenNat_le_max_of_natRep {w : BitVec 64} {n : Nat} {objs : List LcnfObj}
    (h : natRep w n objs) : limbLenNat n ≤ mpzMaxLimbs := by
  by_cases hs : n < 2 ^ 63
  · by_cases h0 : n = 0
    · subst h0; simp [limbLenNat, mpzMaxLimbs]
    · have h1 := limbLenNat_eq_one_of_pos_lt (Nat.pos_of_ne_zero h0) (by omega)
      rw [h1]; decide
  · simp only [natRep, hs, ↓reduceIte] at h
    rcases h with ⟨_, obj, _, _, hc⟩
    rcases hc with ⟨_, _, _, _, h1, hmax, hlast, hval, _⟩
    have hne : obj.limbs ≠ [] := by intro he; simp [he] at h1
    rw [← hval, limbLenNat_eq_length_of_trimmed hne hlast]
    exact hmax

theorem limbLenNat_le_max_of_intRep {w : BitVec 64} {z : Int} {objs : List LcnfObj}
    (h : intRep w z objs) : limbLenNat z.natAbs ≤ mpzMaxLimbs := by
  by_cases hs : -(2 ^ 62 : Int) ≤ z ∧ z < (2 ^ 62 : Int)
  · by_cases h0 : z.natAbs = 0
    · simp [limbLenNat, h0, mpzMaxLimbs]
    · have hlt : z.natAbs < 2 ^ 64 := by omega
      rw [limbLenNat_eq_one_of_pos_lt (Nat.pos_of_ne_zero h0) hlt]
      decide
  · simp only [intRep, hs, ↓reduceIte] at h
    rcases h with ⟨_, obj, _, _, hc⟩
    rcases hc with ⟨_, _, _, _, h1, hmax, hlast, hval, _, _⟩
    have hne : obj.limbs ≠ [] := by intro he; simp [he] at h1
    rw [← hval, limbLenNat_eq_length_of_trimmed hne hlast]
    exact hmax

theorem mpzNatCanon_to_int {obj : LcnfObj} {n : Nat} (h : mpzNatCanon obj n) :
    mpzIntCanon obj (n : Int) := by
  rcases h with ⟨hwf, htag, hoth, harr, h1, hmax, hlast, hval, h63⟩
  refine ⟨hwf, htag, Or.inl hoth, harr, h1, hmax, hlast, ?_, ?_, ?_⟩
  · simpa using hval
  · constructor <;> intro hz <;> omega
  · right; omega

theorem natRep_preserving {w : BitVec 64} {n : Nat} {objs objs' : List LcnfObj}
    (h : natRep w n objs) (hsub : ∀ o ∈ objs, o.addr = w → o ∈ objs') :
    natRep w n objs' := by
  dsimp only [natRep] at h ⊢
  split at h <;> rename_i hs
  · simp only [hs]; exact h
  · simp only [hs]; rcases h with ⟨hw, obj, hmem, had, hc⟩
    exact ⟨hw, obj, hsub obj hmem had, had, hc⟩

theorem intRep_preserving {w : BitVec 64} {z : Int} {objs objs' : List LcnfObj}
    (h : intRep w z objs) (hsub : ∀ o ∈ objs, o.addr = w → o ∈ objs') :
    intRep w z objs' := by
  dsimp only [intRep] at h ⊢
  split at h <;> rename_i hs
  · simp only [hs]; exact h
  · simp only [hs]; rcases h with ⟨hw, obj, hmem, had, hc⟩
    exact ⟨hw, obj, hsub obj hmem had, had, hc⟩

/-- Outcome of `bn_dec_nat(rt,
  a)` across scalar, persistent, shared, and exclusive (`rc = 1`) cases. -/
def DecNatRel (a : BitVec 64) (st st' : RtC0State) (objs objs' : List LcnfObj) : Prop :=
  ((a &&& 1#64) ≠ 0#64 ∧ st' = st ∧ objs' = objs) ∨
  ((a &&& 1#64) = 0#64 ∧ ∃ obj ∈ objs, obj.addr = a ∧ obj.rc = 0#32 ∧ st' = st ∧ objs' = objs) ∨
  ((a &&& 1#64) = 0#64 ∧ ∃ (i : Nat) (hi : i < objs.length),
    objs[i].addr = a ∧ 1 < objs[i].rc.toInt ∧ st' = st ∧
    objs' = objs.set i (objs[i].withRc (objs[i].rc - 1#32))) ∨
  ((a &&& 1#64) = 0#64 ∧ st'.PreservesMeta st ∧ st'.rem = st.rem ∧ DecColdRel a objs objs')

theorem DecNatRel.preservesMeta {a : BitVec 64} {st st' : RtC0State} {objs objs' : List LcnfObj}
    (h : DecNatRel a st st' objs objs') : st'.PreservesMeta st := by
  rcases h with ⟨_, rfl, _⟩ | ⟨_, _, _, _, _, rfl, _⟩ | ⟨_, _, _, _, _, rfl, _⟩ | ⟨_, hp, _, _⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact hp

theorem DecNatRel.rem_eq {a : BitVec 64} {st st' : RtC0State} {objs objs' : List LcnfObj}
    (h : DecNatRel a st st' objs objs') : st'.rem = st.rem := by
  rcases h with ⟨_, rfl, _⟩ | ⟨_, _, _, _, _, rfl, _⟩ | ⟨_, _, _, _, _, rfl, _⟩ | ⟨_, _, hr, _⟩
  · rfl
  · rfl
  · rfl
  · exact hr

/-- Well-formedness of the extended `LcnfC0BigNumRt` slab and non-overflowing scratch region. -/
def BigNumRtWf (rt : BitVec 64) (st : RtC0State) (scr : BitVec 64)
    (scrLimbs : List (BitVec 64)) : Prop :=
  st.Bounded48 ∧
  rt.toNat + LcnfC0BigNumRt.sizeof < 2 ^ 64 ∧
  scr ≠ 0#64 ∧
  scr.toNat % 8 = 0 ∧
  scrLimbs.length < 2 ^ 64 ∧
  scr.toNat + 8 * scrLimbs.length < 2 ^ 64

/-- Separation-logic invariant for `LcnfC0BigNumRt`: R0 slab + trailing `scratch` / `scratch_cap` +
scratch limb array. -/
def bigNumRtInv (rt : BitVec 64) (st : RtC0State) (scr : BitVec 64)
    (scrLimbs : List (BitVec 64)) : Mem 64 → Prop :=
  rtC0Inv rt st ⋆
  cell64 (rt + 33672#64) scr ⋆
  cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
  array64 scr scrLimbs

/-- Comparison encoding returned by `bn_cmp_fixed` / `bn_cmp`: `-1#64`, `0#64`, or `1#64`. -/
def cmpResult64 (x y : Nat) : BitVec 64 :=
  if x < y then (-1#64) else if x > y then 1#64 else 0#64

/-! ## 3. Helper Contracts (`Spec`) for All 34 R1 C0 Functions -/

def rtScratchSpec : Spec [i64] [i64] := fun (rt, ()) m Q _ =>
  ∃ (scr : BitVec 64) (R : Mem 64 → Prop),
    (cell64 (rt + 33672#64) scr ⋆ R) m ∧ Q (scr, ()) m

def rtScratchCapSpec : Spec [i64] [i64] := fun (rt, ()) m Q _ =>
  ∃ (cap : BitVec 64) (R : Mem 64 → Prop),
    (cell64 (rt + 33680#64) cap ⋆ R) m ∧ Q (cap, ()) m

def lcnfNatAllocSpec : Spec [i64, i64] [i64] := fun (rt, nlimbs, ()) m Q _ =>
  let n' := max 1 nlimbs.toNat
  let bytes := 16 + 8 * n'
  ∃ (st : RtC0State) (R : Mem 64 → Prop),
    nlimbs.toNat ≤ mpzMaxLimbs ∧ st.Bounded48 ∧
    (st.hasFree bytes ∨ bytes ≤ st.rem) ∧
    (rtC0Inv rt st ⋆ R) m ∧
    ∀ p st' m',
      let obj : LcnfObj :=
        { addr := p
          rc := 1#32
          csSz := if bytes < 65536 then bytes else 0
          other := 0
          tag := mpzTag
          cap := n'
          arrSize := n'
          limbs := List.replicate n' 0#64 }
      obj.Wf → (p &&& 1#64) = 0#64 →
      st'.PreservesMeta st → st'.rem ≤ st.rem → st'.Bounded48 →
      (rtC0Inv rt st' ⋆ lcnfObjMem obj ⋆ R) m' → Q (p, ()) m'

def bnDecNatSpec : Spec [i64, i64] [] := fun (rt, a, ()) m Q _ =>
  if (a &&& 1#64) ≠ 0#64 then
    Q () m
  else
    ∃ (st : RtC0State) (objs : List LcnfObj) (R : Mem 64 → Prop),
      objs.length ≤ st.workCap ∧
      (rtC0Inv rt st ⋆ lcnfHeap objs ⋆ R) m ∧
      (∃ obj ∈ objs, obj.addr = a) ∧
      (∀ obj ∈ objs, obj.Wf) ∧ lcnfHeapClosed objs ∧
      (∀ obj ∈ objs, obj.addr = a → obj.rc = 1#32 → RcSound a objs) ∧
      ∀ st' objs' m',
        DecNatRel a st st' objs objs' →
        (rtC0Inv rt st' ⋆ lcnfHeap objs' ⋆ R) m' → Q () m'

def bnRequireScratchSpec : Spec [i64, i64] [i64] := fun (rt, need, ()) m Q _ =>
  ∃ (scr cap : BitVec 64) (R : Mem 64 → Prop),
    scr ≠ 0#64 ∧ need.toNat ≤ cap.toNat ∧
    (cell64 (rt + 33672#64) scr ⋆ cell64 (rt + 33680#64) cap ⋆ R) m ∧
    Q (scr, ()) m

def bnTrimSpec : Spec [i64, i64] [i64] := fun (buf, n, ()) m Q _ =>
  ∃ (xs : List (BitVec 64)) (R : Mem 64 → Prop),
    n.toNat ≤ xs.length ∧ (array64 buf xs ⋆ R) m ∧
    Q (BitVec.ofNat 64 (trimLenLoop xs n.toNat), ()) m

def bnCopySpec : Spec [i64, i64, i64] [] := fun (dst, src, n, ()) m Q _ =>
  ∃ (dstXs srcXs : List (BitVec 64)) (R : Mem 64 → Prop),
    n.toNat ≤ dstXs.length ∧ n.toNat ≤ srcXs.length ∧
    (array64 dst dstXs ⋆ array64 src srcXs ⋆ R) m ∧
    ∀ m',
      (array64 dst (srcXs.take n.toNat ++ dstXs.drop n.toNat) ⋆ array64 src srcXs ⋆ R) m' →
      Q () m'

def bnZeroSpec : Spec [i64, i64] [] := fun (dst, n, ()) m Q _ =>
  ∃ (xs : List (BitVec 64)) (R : Mem 64 → Prop),
    n.toNat ≤ xs.length ∧ (array64 dst xs ⋆ R) m ∧
    ∀ m', (array64 dst (List.replicate n.toNat 0#64 ++ xs.drop n.toNat) ⋆ R) m' → Q () m'

def bnNatFromLimbsSpec : Spec [i64, i64, i64] [i64] := fun (rt, buf, n, ()) m Q _ =>
  ∃ (st : RtC0State) (bufXs : List (BitVec 64)) (objs : List LcnfObj) (R : Mem 64 → Prop),
    let val := limbsVal (bufXs.take n.toNat)
    let tn := trimLenLoop bufXs n.toNat
    n.toNat ≤ bufXs.length ∧ n.toNat ≤ mpzMaxLimbs ∧ st.Bounded48 ∧
    (2 ^ 63 ≤ val → st.hasFree (16 + 8 * tn) ∨ 16 + 8 * tn ≤ st.rem) ∧
    (rtC0Inv rt st ⋆ array64 buf bufXs ⋆ lcnfHeap objs ⋆ R) m ∧
    ∀ p st' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → st'.Bounded48 →
      natRep p val objs' →
      (val < 2 ^ 63 → objs' = objs) →
      (2 ^ 63 ≤ val → ∃ newObj : LcnfObj, newObj.addr = p ∧ mpzNatCanon newObj val ∧
        objs' = newObj :: objs) →
      (rtC0Inv rt st' ⋆ array64 buf bufXs ⋆ lcnfHeap objs' ⋆ R) m' →
      Q (p, ()) m'

def bnIntFromLimbsSpec : Spec [i64, i64, i64, i64] [i64] := fun (rt, neg, buf, n, ()) m Q _ =>
  ∃ (st : RtC0State) (bufXs : List (BitVec 64)) (objs : List LcnfObj) (R : Mem 64 → Prop),
    let mag := limbsVal (bufXs.take n.toNat)
    let tn := trimLenLoop bufXs n.toNat
    let val : Int := if tn = 0 then 0 else if neg = 0#64 then (mag : Int) else -(mag : Int)
    n.toNat ≤ bufXs.length ∧ n.toNat ≤ mpzMaxLimbs ∧ st.Bounded48 ∧
    ((val < -(2 ^ 62 : Int) ∨ (2 ^ 62 : Int) ≤ val) →
      st.hasFree (16 + 8 * tn) ∨ 16 + 8 * tn ≤ st.rem) ∧
    (rtC0Inv rt st ⋆ array64 buf bufXs ⋆ lcnfHeap objs ⋆ R) m ∧
    ∀ p st' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → st'.Bounded48 →
      intRep p val objs' →
      ((-(2 ^ 62 : Int) ≤ val ∧ val < (2 ^ 62 : Int)) → objs' = objs) →
      ((val < -(2 ^ 62 : Int) ∨ (2 ^ 62 : Int) ≤ val) →
        ∃ newObj : LcnfObj, newObj.addr = p ∧ mpzIntCanon newObj val ∧
          objs' = newObj :: objs) →
      (rtC0Inv rt st' ⋆ array64 buf bufXs ⋆ lcnfHeap objs' ⋆ R) m' →
      Q (p, ()) m'

def bnNatLenSpec : Spec [i64] [i64] := fun (a, ()) m Q _ =>
  ∃ (val : Nat) (objs : List LcnfObj) (R : Mem 64 → Prop),
    natRep a val objs ∧ (lcnfHeap objs ⋆ R) m ∧
    Q (BitVec.ofNat 64 (limbLenNat val), ()) m

def bnIntLenSpec : Spec [i64] [i64] := fun (a, ()) m Q _ =>
  ∃ (val : Int) (objs : List LcnfObj) (R : Mem 64 → Prop),
    intRep a val objs ∧ (lcnfHeap objs ⋆ R) m ∧
    Q (BitVec.ofNat 64 (limbLenNat val.natAbs), ()) m

def bnLoadNatSpec : Spec [i64, i64] [i64] := fun (a, dst, ()) m Q _ =>
  ∃ (val : Nat) (objs : List LcnfObj) (dstXs : List (BitVec 64)) (R : Mem 64 → Prop),
    let len := limbLenNat val
    natRep a val objs ∧ len ≤ dstXs.length ∧
    (lcnfHeap objs ⋆ array64 dst dstXs ⋆ R) m ∧
    ∀ dstXs' m',
      dstXs'.length = dstXs.length →
      limbsVal (dstXs'.take len) = val →
      dstXs'.drop len = dstXs.drop len →
      (lcnfHeap objs ⋆ array64 dst dstXs' ⋆ R) m' →
      Q (BitVec.ofNat 64 len, ()) m'

def bnLoadIntSpec : Spec [i64, i64] [i64] := fun (a, dst, ()) m Q _ =>
  ∃ (val : Int) (objs : List LcnfObj) (dstXs : List (BitVec 64)) (R : Mem 64 → Prop),
    let len := limbLenNat val.natAbs
    let negBit : BitVec 64 := if val < 0 then 1#64 else 0#64
    let info := (BitVec.ofNat 64 len <<< 1) ||| negBit
    intRep a val objs ∧ len ≤ dstXs.length ∧
    (lcnfHeap objs ⋆ array64 dst dstXs ⋆ R) m ∧
    ∀ dstXs' m',
      dstXs'.length = dstXs.length →
      limbsVal (dstXs'.take len) = val.natAbs →
      dstXs'.drop len = dstXs.drop len →
      (lcnfHeap objs ⋆ array64 dst dstXs' ⋆ R) m' →
      Q (info, ()) m'

def bnCmpFixedSpec : Spec [i64, i64, i64] [i64] := fun (a, b, n, ()) m Q _ =>
  ∃ (aXs bXs : List (BitVec 64)) (R : Mem 64 → Prop),
    n.toNat ≤ aXs.length ∧ n.toNat ≤ bXs.length ∧
    (array64 a aXs ⋆ array64 b bXs ⋆ R) m ∧
    Q (cmpResult64 (limbsVal (aXs.take n.toNat)) (limbsVal (bXs.take n.toNat)), ()) m

def bnCmpSpec : Spec [i64, i64, i64, i64] [i64] := fun (a, na, b, nb, ()) m Q _ =>
  ∃ (aXs bXs : List (BitVec 64)) (R : Mem 64 → Prop),
    na.toNat ≤ aXs.length ∧ nb.toNat ≤ bXs.length ∧
    (array64 a aXs ⋆ array64 b bXs ⋆ R) m ∧
    Q (cmpResult64 (limbsVal (aXs.take na.toNat)) (limbsVal (bXs.take nb.toNat)), ()) m

def bnAddSpec : Spec [i64, i64, i64, i64, i64] [i64] := fun (a, na, b, nb, out, ()) m Q _ =>
  ∃ (aXs bXs outXs : List (BitVec 64)) (R : Mem 64 → Prop),
    let sum := limbsVal (aXs.take na.toNat) + limbsVal (bXs.take nb.toNat)
    let tn := limbLenNat sum
    na.toNat ≤ aXs.length ∧ nb.toNat ≤ bXs.length ∧
    max na.toNat nb.toNat + 1 ≤ outXs.length ∧ max na.toNat nb.toNat + 1 < 2 ^ 64 ∧
    (array64 a aXs ⋆ array64 b bXs ⋆ array64 out outXs ⋆ R) m ∧
    ∀ outXs' m',
      outXs'.length = outXs.length → tn ≤ outXs.length →
      limbsVal (outXs'.take tn) = sum →
      (array64 a aXs ⋆ array64 b bXs ⋆ array64 out outXs' ⋆ R) m' →
      Q (BitVec.ofNat 64 tn, ()) m'

def bnAddOneSpec : Spec [i64, i64, i64] [i64] := fun (a, na, out, ()) m Q _ =>
  ∃ (aXs outXs : List (BitVec 64)) (R : Mem 64 → Prop),
    let sum := limbsVal (aXs.take na.toNat) + 1
    let tn := limbLenNat sum
    na.toNat ≤ aXs.length ∧ na.toNat + 1 ≤ outXs.length ∧ na.toNat + 1 < 2 ^ 64 ∧
    (array64 a aXs ⋆ array64 out outXs ⋆ R) m ∧
    ∀ outXs' m',
      outXs'.length = outXs.length → tn ≤ outXs.length →
      limbsVal (outXs'.take tn) = sum →
      (array64 a aXs ⋆ array64 out outXs' ⋆ R) m' →
      Q (BitVec.ofNat 64 tn, ()) m'

def bnSubSpec : Spec [i64, i64, i64, i64, i64] [i64] := fun (a, na, b, nb, out, ()) m Q _ =>
  ∃ (aXs bXs outXs : List (BitVec 64)) (R : Mem 64 → Prop),
    let aVal := limbsVal (aXs.take na.toNat)
    let bVal := limbsVal (bXs.take nb.toNat)
    let diff := aVal - bVal
    let tn := limbLenNat diff
    na.toNat ≤ aXs.length ∧ nb.toNat ≤ bXs.length ∧ na.toNat ≤ outXs.length ∧
    bVal ≤ aVal ∧
    (array64 a aXs ⋆ array64 b bXs ⋆ array64 out outXs ⋆ R) m ∧
    ∀ outXs' m',
      outXs'.length = outXs.length → tn ≤ outXs.length →
      limbsVal (outXs'.take tn) = diff →
      (array64 a aXs ⋆ array64 b bXs ⋆ array64 out outXs' ⋆ R) m' →
      Q (BitVec.ofNat 64 tn, ()) m'

def bnSubOneSpec : Spec [i64, i64, i64] [i64] := fun (a, na, out, ()) m Q _ =>
  ∃ (aXs outXs : List (BitVec 64)) (R : Mem 64 → Prop),
    let aVal := limbsVal (aXs.take na.toNat)
    let diff := aVal - 1
    let tn := limbLenNat diff
    na.toNat ≤ aXs.length ∧ na.toNat ≤ outXs.length ∧ (na.toNat = 0 ∨ 1 ≤ aVal) ∧
    (array64 a aXs ⋆ array64 out outXs ⋆ R) m ∧
    ∀ outXs' m',
      outXs'.length = outXs.length → tn ≤ outXs.length →
      limbsVal (outXs'.take tn) = diff →
      (array64 a aXs ⋆ array64 out outXs' ⋆ R) m' →
      Q (BitVec.ofNat 64 tn, ()) m'

def bnMulSpec : Spec [i64, i64, i64, i64, i64] [i64] := fun (a, na, b, nb, out, ()) m Q _ =>
  ∃ (aXs bXs outXs : List (BitVec 64)) (R : Mem 64 → Prop),
    let prod := limbsVal (aXs.take na.toNat) * limbsVal (bXs.take nb.toNat)
    let tn := limbLenNat prod
    na.toNat ≤ aXs.length ∧ nb.toNat ≤ bXs.length ∧
    na.toNat + nb.toNat ≤ outXs.length ∧ na.toNat + nb.toNat < 2 ^ 64 ∧
    (array64 a aXs ⋆ array64 b bXs ⋆ array64 out outXs ⋆ R) m ∧
    ∀ outXs' m',
      outXs'.length = outXs.length → tn ≤ outXs.length →
      limbsVal (outXs'.take tn) = prod →
      (array64 a aXs ⋆ array64 b bXs ⋆ array64 out outXs' ⋆ R) m' →
      Q (BitVec.ofNat 64 tn, ()) m'

def bnBitwiseSpec : Spec [i64, i64, i64, i64, i64, i64] [i64] :=
    fun (op, a, na, b, nb, out, ()) m Q _ =>
  ∃ (aXs bXs outXs : List (BitVec 64)) (R : Mem 64 → Prop),
    let aVal := limbsVal (aXs.take na.toNat)
    let bVal := limbsVal (bXs.take nb.toNat)
    let res :=
      if op = 0#64 then Nat.land aVal bVal
      else if op = 1#64 then Nat.lor aVal bVal
      else Nat.xor aVal bVal
    let tn := limbLenNat res
    let needOut := if op = 0#64 then min na.toNat nb.toNat else max na.toNat nb.toNat
    (op = 0#64 ∨ op = 1#64 ∨ op = 2#64) ∧
    na.toNat ≤ aXs.length ∧ nb.toNat ≤ bXs.length ∧ needOut ≤ outXs.length ∧
    (array64 a aXs ⋆ array64 b bXs ⋆ array64 out outXs ⋆ R) m ∧
    ∀ outXs' m',
      outXs'.length = outXs.length → tn ≤ outXs.length →
      limbsVal (outXs'.take tn) = res →
      (array64 a aXs ⋆ array64 b bXs ⋆ array64 out outXs' ⋆ R) m' →
      Q (BitVec.ofNat 64 tn, ()) m'

def bnShlSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
    fun (a, na, ws, bs, out, ()) m Q _ =>
  ∃ (aXs outXs : List (BitVec 64)) (R : Mem 64 → Prop),
    let res := limbsVal (aXs.take na.toNat) <<< (64 * ws.toNat + bs.toNat)
    let tn := limbLenNat res
    na.toNat ≤ aXs.length ∧ bs.toNat < 64 ∧
    (na.toNat = 0 ∨ ws.toNat + na.toNat + 1 ≤ outXs.length) ∧
    ws.toNat + na.toNat + 1 < 2 ^ 64 ∧
    (array64 a aXs ⋆ array64 out outXs ⋆ R) m ∧
    ∀ outXs' m',
      outXs'.length = outXs.length → tn ≤ outXs.length →
      limbsVal (outXs'.take tn) = res →
      (array64 a aXs ⋆ array64 out outXs' ⋆ R) m' →
      Q (BitVec.ofNat 64 tn, ()) m'

def bnShrSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
    fun (a, na, ws, bs, out, ()) m Q _ =>
  ∃ (aXs outXs : List (BitVec 64)) (R : Mem 64 → Prop),
    let res := limbsVal (aXs.take na.toNat) >>> (64 * ws.toNat + bs.toNat)
    let tn := limbLenNat res
    na.toNat ≤ aXs.length ∧ bs.toNat < 64 ∧
    (na.toNat ≤ ws.toNat ∨ na.toNat - ws.toNat ≤ outXs.length) ∧
    (array64 a aXs ⋆ array64 out outXs ⋆ R) m ∧
    ∀ outXs' m',
      outXs'.length = outXs.length → tn ≤ outXs.length →
      limbsVal (outXs'.take tn) = res →
      (array64 a aXs ⋆ array64 out outXs' ⋆ R) m' →
      Q (BitVec.ofNat 64 tn, ()) m'

def bnDivModSpec : Spec [i64, i64, i64, i64, i64, i64] [] :=
    fun (a, na, b, nb, q, r, ()) m Q _ =>
  ∃ (aXs bXs qXs rXs : List (BitVec 64)) (R : Mem 64 → Prop),
    let aVal := limbsVal (aXs.take na.toNat)
    let bVal := limbsVal (bXs.take nb.toNat)
    0 < na.toNat ∧ 0 < nb.toNat ∧
    na.toNat ≤ aXs.length ∧ nb.toNat ≤ bXs.length ∧
    na.toNat ≤ qXs.length ∧ nb.toNat ≤ rXs.length ∧
    bXs[nb.toNat - 1]! ≠ 0#64 ∧
    (array64 a aXs ⋆ array64 b bXs ⋆ array64 q qXs ⋆ array64 r rXs ⋆ R) m ∧
    ∀ qXs' rXs' m',
      qXs'.length = qXs.length → rXs'.length = rXs.length →
      limbsVal (qXs'.take na.toNat) = aVal / bVal →
      limbsVal (rXs'.take nb.toNat) = aVal % bVal →
      (array64 a aXs ⋆ array64 b bXs ⋆ array64 q qXs' ⋆ array64 r rXs' ⋆ R) m' →
      Q () m'

/-! ## 4. Top-Level `Nat` & `Int` Preconditions, Postconditions, and `Spec`s -/

/-- Allocation capacity predicate covering both small-freelist/large-freelist and bump arena. -/
def canAllocBytes (st : RtC0State) (bytes : Nat) : Prop :=
  st.hasFree bytes ∨ bytes ≤ st.rem

def natPowOk (aVal bVal scrCap : Nat) (st : RtC0State) : Prop :=
  bVal = 0 ∨ aVal = 0 ∨ aVal = 1 ∨
  (bVal < 2 ^ 63 ∧
   let tn := limbLenNat (aVal ^ bVal)
   tn ≤ mpzMaxLimbs ∧ 4 * (tn + 1) ≤ scrCap ∧
   (2 ^ 63 ≤ aVal ^ bVal → canAllocBytes st (16 + 8 * tn)))

def natGcdOk (aVal bVal scrCap : Nat) (st : RtC0State) : Prop :=
  let na := limbLenNat aVal
  let nb := limbLenNat bVal
  let maxn := max na nb
  let g := Nat.gcd aVal bVal
  let tg := limbLenNat g
  (aVal = 0 ∧ bVal = 0) ∨
  (aVal = 0 ∧ bVal ≠ 0 ∧ nb ≤ scrCap ∧ (2 ^ 63 ≤ bVal → canAllocBytes st (16 + 8 * nb))) ∨
  (aVal ≠ 0 ∧ bVal = 0 ∧ na ≤ scrCap ∧ (2 ^ 63 ≤ aVal → canAllocBytes st (16 + 8 * na))) ∨
  (aVal ≠ 0 ∧ bVal ≠ 0 ∧ 4 * maxn ≤ scrCap ∧ (2 ^ 63 ≤ g → canAllocBytes st (16 + 8 * tg)))

def natArithRes (op aVal bVal : Nat) : Nat :=
  if op = 1 then aVal + bVal
  else if op = 2 then aVal - bVal
  else if op = 3 then aVal * bVal
  else if op = 4 then aVal / bVal
  else if op = 5 then aVal % bVal
  else aVal - 1

def natArithOk (op aVal bVal scrCap : Nat) (st : RtC0State) : Prop :=
  let na := limbLenNat aVal
  let nb := limbLenNat bVal
  if op = 17 then
    aVal < 2 ^ 63 ∨
    (2 * na ≤ scrCap ∧ (2 ^ 63 ≤ aVal - 1 → canAllocBytes st (16 + 8 * limbLenNat (aVal - 1))))
  else if op ∈ [1, 2, 3, 4, 5] then
    let res := natArithRes op aVal bVal
    2 * (na + nb) + 2 ≤ scrCap ∧
    limbLenNat res ≤ mpzMaxLimbs ∧
    (2 ^ 63 ≤ res → canAllocBytes st (16 + 8 * limbLenNat res))
  else if op ∈ [6, 7, 8] then
    2 * (na + nb) + 2 ≤ scrCap
  else False

def natBitsOk (op : Nat) (aVal : Nat) (bRaw : BitVec 64) (objs : List LcnfObj)
    (scrCap : Nat) (st : RtC0State) : Prop :=
  let na := limbLenNat aVal
  if op = 13 then True
  else if op = 14 then
    2 ^ 63 ≤ aVal → canAllocBytes st 24
  else if op = 19 then True
  else ∃ bVal : Nat, natRep bRaw bVal objs ∧
    if op = 9 then
      let res := aVal >>> bVal
      (aVal < 2 ^ 63 ∨ 2 ^ 63 ≤ bVal ∨ na ≤ bVal / 64) ∨
      (2 * na - bVal / 64 ≤ scrCap ∧ (2 ^ 63 ≤ res → canAllocBytes st (16 + 8 * limbLenNat res)))
    else if op = 15 then
      aVal = 0 ∨
      (bVal < 2 ^ 63 ∧
       na + bVal / 64 + 1 ≤ mpzMaxLimbs ∧
       2 * na + bVal / 64 + 1 ≤ scrCap ∧
       (2 ^ 63 ≤ aVal <<< bVal → canAllocBytes st (16 + 8 * limbLenNat (aVal <<< bVal))))
    else if op ∈ [10, 11, 12] then
      let nb := limbLenNat bVal
      let res := if op = 10 then Nat.land aVal bVal else if op = 11 then Nat.lor aVal bVal
        else Nat.xor aVal bVal
      na + nb + max na nb + 1 ≤ scrCap ∧
      (2 ^ 63 ≤ res → canAllocBytes st (16 + 8 * limbLenNat res))
    else False

def bnNatPowSpec : Spec [i64, i64, i64] [i64] := fun (rt, a, b, ()) m Q _ =>
  ∃ (st : RtC0State) (scr : BitVec 64) (scrLimbs : List (BitVec 64))
    (objs : List LcnfObj) (aVal bVal : Nat) (R : Mem 64 → Prop),
    BigNumRtWf rt st scr scrLimbs ∧
    natRep a aVal objs ∧ natRep b bVal objs ∧
    natPowOk aVal bVal scrLimbs.length st ∧
    (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m ∧
    ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
      natRep res (aVal ^ bVal) objs' →
      (∀ o ∈ objs, o.addr = a ∨ o.addr = b → o ∈ objs') →
      (∀ o ∈ objs, o.addr ≠ res → o ∈ objs') →
      (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' →
      Q (res, ()) m'

def bnNatGcdSpec : Spec [i64, i64, i64] [i64] := fun (rt, a, b, ()) m Q _ =>
  ∃ (st : RtC0State) (scr : BitVec 64) (scrLimbs : List (BitVec 64))
    (objs : List LcnfObj) (aVal bVal : Nat) (R : Mem 64 → Prop),
    BigNumRtWf rt st scr scrLimbs ∧
    natRep a aVal objs ∧ natRep b bVal objs ∧
    natGcdOk aVal bVal scrLimbs.length st ∧
    (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m ∧
    ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
      natRep res (Nat.gcd aVal bVal) objs' →
      (∀ o ∈ objs, o ∈ objs') →
      (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' →
      Q (res, ()) m'

def natArithPost (op aVal bVal : Nat) (res : BitVec 64) (objs objs' : List LcnfObj) : Prop :=
  if op = 6 then res = (if aVal = bVal then 1#64 else 0#64) ∧ objs' = objs
  else if op = 7 then res = (if aVal < bVal then 1#64 else 0#64) ∧ objs' = objs
  else if op = 8 then res = (if aVal ≤ bVal then 1#64 else 0#64) ∧ objs' = objs
  else natRep res (natArithRes op aVal bVal) objs' ∧ (∀ o ∈ objs, o ∈ objs')

def lcnfNatArithSpec : Spec [i64, i64, i64, i64] [i64] := fun (rt, op, a, b, ()) m Q _ =>
  ∃ (st : RtC0State) (scr : BitVec 64) (scrLimbs : List (BitVec 64))
    (objs : List LcnfObj) (aVal bVal : Nat) (R : Mem 64 → Prop),
    BigNumRtWf rt st scr scrLimbs ∧
    natRep a aVal objs ∧
    (op.toNat = 17 ∨ natRep b bVal objs) ∧
    natArithOk op.toNat aVal bVal scrLimbs.length st ∧
    (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m ∧
    ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
      natArithPost op.toNat aVal bVal res objs objs' →
      (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' →
      Q (res, ()) m'

def natBitsPost (op : Nat) (aVal : Nat) (bRaw : BitVec 64) (res : BitVec 64)
    (objs objs' : List LcnfObj) : Prop :=
  if op = 13 then
    objs' = objs ∧
    res =
      (if bRaw.toNat = 0 then 0#64
       else if 64 ≤ bRaw.toNat then BitVec.ofNat 64 aVal
       else BitVec.ofNat 64 (aVal % 2 ^ bRaw.toNat))
  else if op = 14 then
    natRep res aVal objs' ∧ (∀ o ∈ objs, o ∈ objs')
  else if op = 19 then
    natRep res aVal.log2 objs' ∧ objs' = objs
  else ∃ bVal : Nat, natRep bRaw bVal objs ∧ (∀ o ∈ objs, o ∈ objs') ∧
    if op = 9 then natRep res (aVal >>> bVal) objs'
    else if op = 15 then natRep res (aVal <<< bVal) objs'
    else if op = 10 then natRep res (Nat.land aVal bVal) objs'
    else if op = 11 then natRep res (Nat.lor aVal bVal) objs'
    else if op = 12 then natRep res (Nat.xor aVal bVal) objs'
    else False

def lcnfNatBitsSpec : Spec [i64, i64, i64, i64] [i64] := fun (rt, op, a, b, ()) m Q _ =>
  ∃ (st : RtC0State) (scr : BitVec 64) (scrLimbs : List (BitVec 64))
    (objs : List LcnfObj) (aVal : Nat) (R : Mem 64 → Prop),
    BigNumRtWf rt st scr scrLimbs ∧
    (if op.toNat = 14 then aVal = a.toNat else natRep a aVal objs) ∧
    natBitsOk op.toNat aVal b objs scrLimbs.length st ∧
    (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m ∧
    ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
      natBitsPost op.toNat aVal b res objs objs' →
      (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' →
      Q (res, ()) m'

def lcnfNatSlowSpec : Spec [i64, i64, i64, i64] [i64] := fun (rt, op, a, b, ()) m Q _ =>
  ∃ (st : RtC0State) (scr : BitVec 64) (scrLimbs : List (BitVec 64))
    (objs : List LcnfObj) (R : Mem 64 → Prop),
    BigNumRtWf rt st scr scrLimbs ∧
    (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m ∧
    (if op.toNat ∈ [1, 2, 3, 4, 5, 6, 7, 8, 17] then
      ∃ aVal bVal, natRep a aVal objs ∧ (op.toNat = 17 ∨ natRep b bVal objs) ∧
        natArithOk op.toNat aVal bVal scrLimbs.length st ∧
        ∀ res st' scrLimbs' objs' m',
          st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
          natArithPost op.toNat aVal bVal res objs objs' →
          (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m'
    else if op.toNat ∈ [9, 10, 11, 12, 13, 14, 15, 19] then
      ∃ aVal, (if op.toNat = 14 then aVal = a.toNat else natRep a aVal objs) ∧
        natBitsOk op.toNat aVal b objs scrLimbs.length st ∧
        ∀ res st' scrLimbs' objs' m',
          st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
          natBitsPost op.toNat aVal b res objs objs' →
          (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m'
    else if op.toNat = 16 then
      ∃ aVal bVal, natRep a aVal objs ∧ natRep b bVal objs ∧
        natPowOk aVal bVal scrLimbs.length st ∧
        ∀ res st' scrLimbs' objs' m',
          st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
          natRep res (aVal ^ bVal) objs' →
          (∀ o ∈ objs, o.addr ≠ res → o ∈ objs') →
          (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m'
    else if op.toNat = 18 then
      ∃ aVal bVal, natRep a aVal objs ∧ natRep b bVal objs ∧
        natGcdOk aVal bVal scrLimbs.length st ∧
        ∀ res st' scrLimbs' objs' m',
          st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
          natRep res (Nat.gcd aVal bVal) objs' →
          (∀ o ∈ objs, o ∈ objs') →
          (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m'
    else False)

def lcnfIntConvSpec : Spec [i64, i64, i64] [i64] := fun (rt, op, a, ()) m Q _ =>
  ∃ (st : RtC0State) (scr : BitVec 64) (scrLimbs : List (BitVec 64))
    (objs : List LcnfObj) (R : Mem 64 → Prop),
    BigNumRtWf rt st scr scrLimbs ∧
    (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m ∧
    (if op.toNat = 1 then
      ∃ aVal : Nat, natRep a aVal objs ∧
        ((2 ^ 62 ≤ aVal ∧ aVal < 2 ^ 63) → canAllocBytes st 24) ∧
        ∀ res st' scrLimbs' objs' m',
          st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
          intRep res (aVal : Int) objs' →
          (∀ o ∈ objs, o ∈ objs') →
          (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m'
    else if op.toNat = 13 then
      let z : Int := a.toInt
      ((z < -(2 ^ 62 : Int) ∨ (2 ^ 62 : Int) ≤ z) → canAllocBytes st 24) ∧
      ∀ res st' scrLimbs' objs' m',
        st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
        intRep res z objs' →
        (∀ o ∈ objs, o ∈ objs') →
        (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m'
    else if op.toNat = 16 then
      ∃ z : Int, intRep a z objs ∧
        ∀ m', (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m' →
          Q (if (0 : Int) ≤ z then 1#64 else 0#64, ()) m'
    else if op.toNat = 2 then
      ∃ aVal : Nat, natRep a aVal objs ∧
        let z := Int.negSucc aVal
        let tn := limbLenNat (aVal + 1)
        tn ≤ mpzMaxLimbs ∧
        (2 ^ 63 ≤ aVal →
          limbLenNat aVal + 1 ≤ scrLimbs.length ∧
          objs.length ≤ st.workCap ∧ (∀ o ∈ objs, o.Wf) ∧ lcnfHeapClosed objs ∧
          (∀ o ∈ objs, o.addr = a → o.rc = 1#32 → RcSound a objs) ∧
          16 + 8 * tn ≤ st.rem) ∧
        ((aVal < 2 ^ 63 ∧ z < -(2 ^ 62 : Int)) → canAllocBytes st 24) ∧
        ∀ res st' scrLimbs' objs' m',
          st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
          intRep res z objs' →
          (∀ o ∈ objs, o.addr ≠ a → ∃ o' ∈ objs', o'.addr = o.addr ∧ o'.tag = o.tag ∧
            o'.other = o.other ∧ o'.arrSize = o.arrSize ∧ o'.cap = o.cap ∧
            o'.limbs = o.limbs ∧ (o.Wf → o'.Wf)) →
          (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m'
    else if op.toNat = 3 then
      ∃ z : Int, intRep a z objs ∧
        (z ≠ 0 → limbLenNat z.natAbs ≤ scrLimbs.length ∧
          ((-z < -(2 ^ 62 : Int) ∨ (2 ^ 62 : Int) ≤ -z) →
            canAllocBytes st (16 + 8 * limbLenNat z.natAbs))) ∧
        ∀ res st' scrLimbs' objs' m',
          st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
          intRep res (-z) objs' →
          (∀ o ∈ objs, o ∈ objs') →
          (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m'
    else if op.toNat = 9 then
      ∃ z : Int, intRep a z objs ∧
        (z ≠ 0 → limbLenNat z.natAbs ≤ scrLimbs.length ∧
          (2 ^ 63 ≤ z.natAbs → canAllocBytes st (16 + 8 * limbLenNat z.natAbs))) ∧
        ∀ res st' scrLimbs' objs' m',
          st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
          natRep res z.natAbs objs' →
          (∀ o ∈ objs, o ∈ objs') →
          (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m'
    else False)

def lcnfIntAddSubCmpSpec : Spec [i64, i64, i64, i64] [i64] :=
    fun (rt, op, a, b, ()) m Q _ =>
  ∃ (st : RtC0State) (scr : BitVec 64) (scrLimbs : List (BitVec 64))
    (objs : List LcnfObj) (aVal bVal : Int) (R : Mem 64 → Prop),
    let na := limbLenNat aVal.natAbs
    let nb := limbLenNat bVal.natAbs
    BigNumRtWf rt st scr scrLimbs ∧
    intRep a aVal objs ∧ intRep b bVal objs ∧
    na + nb + max na nb + 1 ≤ scrLimbs.length ∧
    op.toNat ∈ [4, 5, 10, 11, 12] ∧
    (op.toNat ∈ [4, 5] →
      let z := if op.toNat = 4 then aVal + bVal else aVal - bVal
      let tn := limbLenNat z.natAbs
      tn ≤ mpzMaxLimbs ∧
      ((z < -(2 ^ 62 : Int) ∨ (2 ^ 62 : Int) ≤ z) → canAllocBytes st (16 + 8 * tn))) ∧
    (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m ∧
    ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
      (if op.toNat = 4 then intRep res (aVal + bVal) objs' ∧ (∀ o ∈ objs, o ∈ objs')
       else if op.toNat = 5 then intRep res (aVal - bVal) objs' ∧ (∀ o ∈ objs, o ∈ objs')
       else if op.toNat = 10 then res = (if aVal = bVal then 1#64 else 0#64) ∧ objs' = objs
       else if op.toNat = 11 then res = (if aVal < bVal then 1#64 else 0#64) ∧ objs' = objs
       else res = (if aVal ≤ bVal then 1#64 else 0#64) ∧ objs' = objs) →
      (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' →
      Q (res, ()) m'

def intMulDivRes (op : Nat) (aVal bVal : Int) : Int :=
  if op = 6 then aVal * bVal
  else if op = 7 then aVal.ediv bVal
  else if op = 8 then aVal.emod bVal
  else if op = 14 then aVal.tdiv bVal
  else aVal.tmod bVal

def lcnfIntMulDivSpec : Spec [i64, i64, i64, i64] [i64] :=
    fun (rt, op, a, b, ()) m Q _ =>
  ∃ (st : RtC0State) (scr : BitVec 64) (scrLimbs : List (BitVec 64))
    (objs : List LcnfObj) (aVal bVal : Int) (R : Mem 64 → Prop),
    let na := limbLenNat aVal.natAbs
    let nb := limbLenNat bVal.natAbs
    let z := intMulDivRes op.toNat aVal bVal
    let tn := limbLenNat z.natAbs
    BigNumRtWf rt st scr scrLimbs ∧
    intRep a aVal objs ∧ intRep b bVal objs ∧
    op.toNat ∈ [6, 7, 8, 14, 15] ∧
    2 * (na + nb) + max na nb + 2 ≤ scrLimbs.length ∧
    tn ≤ mpzMaxLimbs ∧
    ((z < -(2 ^ 62 : Int) ∨ (2 ^ 62 : Int) ≤ z) → canAllocBytes st (16 + 8 * tn)) ∧
    (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m ∧
    ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
      intRep res z objs' → (∀ o ∈ objs, o ∈ objs') →
      (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' →
      Q (res, ()) m'

def lcnfIntOpSpec : Spec [i64, i64, i64, i64] [i64] := fun (rt, op, a, b, ()) m Q _ =>
  ∃ (st : RtC0State) (scr : BitVec 64) (scrLimbs : List (BitVec 64))
    (objs : List LcnfObj) (R : Mem 64 → Prop),
    BigNumRtWf rt st scr scrLimbs ∧
    (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m ∧
    (if op.toNat ∈ [1, 2, 3, 9, 13, 16] then
      lcnfIntConvSpec (rt, op, a, ()) m Q (fun _ _ _ _ => False)
    else if op.toNat ∈ [4, 5, 10, 11, 12] then
      lcnfIntAddSubCmpSpec (rt, op, a, b, ()) m Q (fun _ _ _ _ => False)
    else if op.toNat ∈ [6, 7, 8, 14, 15] then
      lcnfIntMulDivSpec (rt, op, a, b, ()) m Q (fun _ _ _ _ => False)
    else False)

/-! ## 5. Specification Table `rtR1SpecEntries` & Environment `rtR1Env` -/

/-- Exact specification table aligned row-by-row with `rtR1_fns` (`noExit := false` so all
callers may supply arbitrary `X : XPost`), followed by the two R0 extern contracts. -/
def rtR1SpecEntries : List SpecEntry :=
  [ SpecEntry.ofFn rt_scratch rtScratchSpec false
  , SpecEntry.ofFn rt_scratch_cap rtScratchCapSpec false
  , SpecEntry.ofFn lcnf_nat_alloc lcnfNatAllocSpec false
  , SpecEntry.ofFn bn_dec_nat bnDecNatSpec false
  , SpecEntry.ofFn bn_require_scratch bnRequireScratchSpec false
  , SpecEntry.ofFn bn_trim bnTrimSpec false
  , SpecEntry.ofFn bn_copy bnCopySpec false
  , SpecEntry.ofFn bn_zero bnZeroSpec false
  , SpecEntry.ofFn bn_nat_from_limbs bnNatFromLimbsSpec false
  , SpecEntry.ofFn bn_int_from_limbs bnIntFromLimbsSpec false
  , SpecEntry.ofFn bn_nat_len bnNatLenSpec false
  , SpecEntry.ofFn bn_int_len bnIntLenSpec false
  , SpecEntry.ofFn bn_load_nat bnLoadNatSpec false
  , SpecEntry.ofFn bn_load_int bnLoadIntSpec false
  , SpecEntry.ofFn bn_cmp_fixed bnCmpFixedSpec false
  , SpecEntry.ofFn bn_cmp bnCmpSpec false
  , SpecEntry.ofFn bn_add bnAddSpec false
  , SpecEntry.ofFn bn_add_one bnAddOneSpec false
  , SpecEntry.ofFn bn_sub bnSubSpec false
  , SpecEntry.ofFn bn_sub_one bnSubOneSpec false
  , SpecEntry.ofFn bn_mul bnMulSpec false
  , SpecEntry.ofFn bn_bitwise bnBitwiseSpec false
  , SpecEntry.ofFn bn_shl bnShlSpec false
  , SpecEntry.ofFn bn_shr bnShrSpec false
  , SpecEntry.ofFn bn_divmod bnDivModSpec false
  , SpecEntry.ofFn bn_nat_pow bnNatPowSpec false
  , SpecEntry.ofFn bn_nat_gcd bnNatGcdSpec false
  , SpecEntry.ofFn lcnf_nat_arith lcnfNatArithSpec false
  , SpecEntry.ofFn lcnf_nat_bits lcnfNatBitsSpec false
  , SpecEntry.ofFn lcnf_nat_slow lcnfNatSlowSpec false
  , SpecEntry.ofFn lcnf_int_conv lcnfIntConvSpec false
  , SpecEntry.ofFn lcnf_int_addsub_cmp lcnfIntAddSubCmpSpec false
  , SpecEntry.ofFn lcnf_int_muldiv lcnfIntMulDivSpec false
  , SpecEntry.ofFn lcnf_int_op lcnfIntOpSpec false
  , ⟨"lcnf_alloc", [i64, i64], [i64], lcnfAllocSpec, false⟩
  , ⟨"lcnf_dec_ref_cold", [i64, i64], [], lcnfDecRefColdSpec, false⟩ ]

def rtR1Env : Env :=
  Env.ofTable rtR1SpecEntries

theorem rtR1SpecEntries_names_nodup : (rtR1SpecEntries.map SpecEntry.name).Nodup := by
  refine listNodup_nodup ?_
  decide

private theorem env_lookup_at (i : Nat) (hi : i < rtR1SpecEntries.length)
    (hno : rtR1SpecEntries[i].noExit = false)
    {xs : Tup Val rtR1SpecEntries[i].as} {m : Mem 64}
    {Q : Post rtR1SpecEntries[i].rs} {X : XPost}
    (h : rtR1SpecEntries[i].spec xs m Q X) :
    rtR1Env rtR1SpecEntries[i].name rtR1SpecEntries[i].as rtR1SpecEntries[i].rs xs m Q X := by
  refine Env.ofTable_of_mem (List.getElem_mem hi) rtR1SpecEntries_names_nodup ?_
  simpa [SpecEntry.eff, hno] using h

theorem rtR1Env_rt_scratch {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : rtScratchSpec xs m Q X) : rtR1Env "rt_scratch" [i64] [i64] xs m Q X :=
  env_lookup_at 0 (by decide) rfl h

theorem rtR1Env_rt_scratch_cap {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : rtScratchCapSpec xs m Q X) : rtR1Env "rt_scratch_cap" [i64] [i64] xs m Q X :=
  env_lookup_at 1 (by decide) rfl h

theorem rtR1Env_lcnf_nat_alloc {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : lcnfNatAllocSpec xs m Q X) : rtR1Env "lcnf_nat_alloc" [i64, i64] [i64] xs m Q X :=
  env_lookup_at 2 (by decide) rfl h

theorem rtR1Env_bn_dec_nat {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post []} {X : XPost}
    (h : bnDecNatSpec xs m Q X) : rtR1Env "bn_dec_nat" [i64, i64] [] xs m Q X :=
  env_lookup_at 3 (by decide) rfl h

theorem rtR1Env_bn_require_scratch {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : bnRequireScratchSpec xs m Q X) :
    rtR1Env "bn_require_scratch" [i64, i64] [i64] xs m Q X :=
  env_lookup_at 4 (by decide) rfl h

theorem rtR1Env_bn_trim {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : bnTrimSpec xs m Q X) : rtR1Env "bn_trim" [i64, i64] [i64] xs m Q X :=
  env_lookup_at 5 (by decide) rfl h

theorem rtR1Env_bn_copy {xs : Tup Val [i64, i64, i64]} {m : Mem 64} {Q : Post []} {X : XPost}
    (h : bnCopySpec xs m Q X) : rtR1Env "bn_copy" [i64, i64, i64] [] xs m Q X :=
  env_lookup_at 6 (by decide) rfl h

theorem rtR1Env_bn_zero {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post []} {X : XPost}
    (h : bnZeroSpec xs m Q X) : rtR1Env "bn_zero" [i64, i64] [] xs m Q X :=
  env_lookup_at 7 (by decide) rfl h

theorem rtR1Env_bn_nat_from_limbs {xs : Tup Val [i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : bnNatFromLimbsSpec xs m Q X) :
    rtR1Env "bn_nat_from_limbs" [i64, i64, i64] [i64] xs m Q X :=
  env_lookup_at 8 (by decide) rfl h

theorem rtR1Env_bn_int_from_limbs {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : bnIntFromLimbsSpec xs m Q X) :
    rtR1Env "bn_int_from_limbs" [i64, i64, i64, i64] [i64] xs m Q X :=
  env_lookup_at 9 (by decide) rfl h

theorem rtR1Env_bn_nat_len {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : bnNatLenSpec xs m Q X) : rtR1Env "bn_nat_len" [i64] [i64] xs m Q X :=
  env_lookup_at 10 (by decide) rfl h

theorem rtR1Env_bn_int_len {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : bnIntLenSpec xs m Q X) : rtR1Env "bn_int_len" [i64] [i64] xs m Q X :=
  env_lookup_at 11 (by decide) rfl h

theorem rtR1Env_bn_load_nat {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : bnLoadNatSpec xs m Q X) : rtR1Env "bn_load_nat" [i64, i64] [i64] xs m Q X :=
  env_lookup_at 12 (by decide) rfl h

theorem rtR1Env_bn_load_int {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : bnLoadIntSpec xs m Q X) : rtR1Env "bn_load_int" [i64, i64] [i64] xs m Q X :=
  env_lookup_at 13 (by decide) rfl h

theorem rtR1Env_bn_cmp_fixed {xs : Tup Val [i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : bnCmpFixedSpec xs m Q X) :
    rtR1Env "bn_cmp_fixed" [i64, i64, i64] [i64] xs m Q X :=
  env_lookup_at 14 (by decide) rfl h

theorem rtR1Env_bn_cmp {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : bnCmpSpec xs m Q X) :
    rtR1Env "bn_cmp" [i64, i64, i64, i64] [i64] xs m Q X :=
  env_lookup_at 15 (by decide) rfl h

theorem rtR1Env_bn_add {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : bnAddSpec xs m Q X) :
    rtR1Env "bn_add" [i64, i64, i64, i64, i64] [i64] xs m Q X :=
  env_lookup_at 16 (by decide) rfl h

theorem rtR1Env_bn_add_one {xs : Tup Val [i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : bnAddOneSpec xs m Q X) :
    rtR1Env "bn_add_one" [i64, i64, i64] [i64] xs m Q X :=
  env_lookup_at 17 (by decide) rfl h

theorem rtR1Env_bn_sub {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : bnSubSpec xs m Q X) :
    rtR1Env "bn_sub" [i64, i64, i64, i64, i64] [i64] xs m Q X :=
  env_lookup_at 18 (by decide) rfl h

theorem rtR1Env_bn_sub_one {xs : Tup Val [i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : bnSubOneSpec xs m Q X) :
    rtR1Env "bn_sub_one" [i64, i64, i64] [i64] xs m Q X :=
  env_lookup_at 19 (by decide) rfl h

theorem rtR1Env_bn_mul {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : bnMulSpec xs m Q X) :
    rtR1Env "bn_mul" [i64, i64, i64, i64, i64] [i64] xs m Q X :=
  env_lookup_at 20 (by decide) rfl h

theorem rtR1Env_bn_bitwise {xs : Tup Val [i64, i64, i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : bnBitwiseSpec xs m Q X) :
    rtR1Env "bn_bitwise" [i64, i64, i64, i64, i64, i64] [i64] xs m Q X :=
  env_lookup_at 21 (by decide) rfl h

theorem rtR1Env_bn_shl {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : bnShlSpec xs m Q X) :
    rtR1Env "bn_shl" [i64, i64, i64, i64, i64] [i64] xs m Q X :=
  env_lookup_at 22 (by decide) rfl h

theorem rtR1Env_bn_shr {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : bnShrSpec xs m Q X) :
    rtR1Env "bn_shr" [i64, i64, i64, i64, i64] [i64] xs m Q X :=
  env_lookup_at 23 (by decide) rfl h

theorem rtR1Env_bn_divmod {xs : Tup Val [i64, i64, i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post []} {X : XPost} (h : bnDivModSpec xs m Q X) :
    rtR1Env "bn_divmod" [i64, i64, i64, i64, i64, i64] [] xs m Q X :=
  env_lookup_at 24 (by decide) rfl h

theorem rtR1Env_bn_nat_pow {xs : Tup Val [i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : bnNatPowSpec xs m Q X) :
    rtR1Env "bn_nat_pow" [i64, i64, i64] [i64] xs m Q X :=
  env_lookup_at 25 (by decide) rfl h

theorem rtR1Env_bn_nat_gcd {xs : Tup Val [i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : bnNatGcdSpec xs m Q X) :
    rtR1Env "bn_nat_gcd" [i64, i64, i64] [i64] xs m Q X :=
  env_lookup_at 26 (by decide) rfl h

theorem rtR1Env_lcnf_nat_arith {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : lcnfNatArithSpec xs m Q X) :
    rtR1Env "lcnf_nat_arith" [i64, i64, i64, i64] [i64] xs m Q X :=
  env_lookup_at 27 (by decide) rfl h

theorem rtR1Env_lcnf_nat_bits {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : lcnfNatBitsSpec xs m Q X) :
    rtR1Env "lcnf_nat_bits" [i64, i64, i64, i64] [i64] xs m Q X :=
  env_lookup_at 28 (by decide) rfl h

theorem rtR1Env_lcnf_nat_slow {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : lcnfNatSlowSpec xs m Q X) :
    rtR1Env "lcnf_nat_slow" [i64, i64, i64, i64] [i64] xs m Q X :=
  env_lookup_at 29 (by decide) rfl h

theorem rtR1Env_lcnf_int_conv {xs : Tup Val [i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : lcnfIntConvSpec xs m Q X) :
    rtR1Env "lcnf_int_conv" [i64, i64, i64] [i64] xs m Q X :=
  env_lookup_at 30 (by decide) rfl h

theorem rtR1Env_lcnf_int_addsub_cmp {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : lcnfIntAddSubCmpSpec xs m Q X) :
    rtR1Env "lcnf_int_addsub_cmp" [i64, i64, i64, i64] [i64] xs m Q X :=
  env_lookup_at 31 (by decide) rfl h

theorem rtR1Env_lcnf_int_muldiv {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : lcnfIntMulDivSpec xs m Q X) :
    rtR1Env "lcnf_int_muldiv" [i64, i64, i64, i64] [i64] xs m Q X :=
  env_lookup_at 32 (by decide) rfl h

theorem rtR1Env_lcnf_int_op {xs : Tup Val [i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]}
    {X : XPost} (h : lcnfIntOpSpec xs m Q X) :
    rtR1Env "lcnf_int_op" [i64, i64, i64, i64] [i64] xs m Q X :=
  env_lookup_at 33 (by decide) rfl h

theorem rtR1Env_lcnf_alloc {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (h : lcnfAllocSpec xs m Q X) : rtR1Env "lcnf_alloc" [i64, i64] [i64] xs m Q X :=
  env_lookup_at 34 (by decide) rfl h

theorem rtR1Env_lcnf_dec_ref_cold {xs : Tup Val [i64, i64]} {m : Mem 64} {Q : Post []} {X : XPost}
    (h : lcnfDecRefColdSpec xs m Q X) :
    rtR1Env "lcnf_dec_ref_cold" [i64, i64] [] xs m Q X :=
  env_lookup_at 35 (by decide) rfl h

end LeanQbe.T.LeanLCNF
