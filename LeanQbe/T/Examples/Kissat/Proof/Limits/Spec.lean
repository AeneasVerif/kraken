/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Logic.CanonicalEnv
public import LeanQbe.T.Examples.Kissat.Src.Limits
public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3

/-!
# Canonical `Spec` Table for `Kissat/Src/Limits.lean` (`15` fns)

Canonical contracts (`Spec` + `Spec.XFree` + `specs_sigs` + `specs_nodup`) for the `15` functions
in `Kissat/Src/Limits.lean`, reusing `Proof.Spec` contracts where already defined
(`fullIsqrtSpec`, `fullIlog10Spec`, `fullTickRelSpec`, `fullEmaUpdateSpec`, `fullSortU32Spec`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Limits.Spec

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Proof.Spec

@[expose] public section

/-! ## M7 State / Scratch Constants & Helpers -/

def m7SearchMagic : BitVec 64 := 0x4D37534541524348#64
def m7EmaInitExp : BitVec 64 := 0x3FF0000000000000#64
def m7LcgMul : BitVec 64 := 6364136223846793005#64
def m7LcgInc : BitVec 64 := 1442695040888963407#64

def m7GuMagicIdx : Nat := 36
def m7GuEmaMaskIdx : Nat := 38
def m7GuEma0FbIdx : Nat := 40
def m7GuEma0FeIdx : Nat := 42
def m7GuEma0SbIdx : Nat := 44
def m7GuEma0SeIdx : Nat := 46
def m7GuEma1FbIdx : Nat := 48
def m7GuEma1FeIdx : Nat := 50
def m7GuEma1SbIdx : Nat := 52
def m7GuEma1SeIdx : Nat := 54
def m7GuRandecRemIdx : Nat := 56
def m7GuRandecLimIdx : Nat := 58
def m7GuRandecSeqIdx : Nat := 60
def m7GuRandecConflIdx : Nat := 62

def u64Of32Pair (lo hi : BitVec 32) : BitVec 64 :=
  lo.setWidth 64 ||| (hi.setWidth 64 <<< 32)

def m7Get64Val (gu : List (BitVec 32)) (idx : Nat) : BitVec 64 :=
  u64Of32Pair (gu[idx]?.getD 0#32) (gu[idx + 1]?.getD 0#32)

def m7Set64List (gu : List (BitVec 32)) (idx : Nat) (val : BitVec 64) : List (BitVec 32) :=
  (gu.set idx (val.setWidth 32)).set (idx + 1) ((val >>> 32).setWidth 32)

def m7LcgNextVal (rng : BitVec 64) : BitVec 64 :=
  rng * m7LcgMul + m7LcgInc

def M7GuPrefixPres (s s' : FullState) : Prop :=
  ∀ j < 36, s'.scratch.glue_used[j]? = s.scratch.glue_used[j]?

def M7StateInitOk (gu : List (BitVec 32)) : Prop :=
  gu.length = 64 ∧ m7Get64Val gu m7GuMagicIdx = m7SearchMagic

/-! ## Canonical Per-Function `Spec`s (`10` local + `5` re-exported from `Proof.Spec`) -/

def schedScaleDeltaSpec : Spec [i64, i64] [i64] :=
  fun (h, _base, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧ ∀ delta : BitVec 64, Q (delta, ()) m

def m7FillU64Spec : Spec [i64, i64, i64] [] :=
  fun (dst, n, val, ()) m Q _ =>
    ∃ (xs : List (BitVec 64)) (R : Mem 64 → Prop),
      n.toNat ≤ xs.length ∧ n.toNat + 4 < 2 ^ 64 ∧ (array64 dst xs ⋆ R) m ∧
      ∀ m', (array64 dst (List.replicate n.toNat val ++ xs.drop n.toNat) ⋆ R) m' → Q () m'

def schedMaxU64Spec : Spec [i64, i64] [i64] :=
  fun (a, b, ()) m Q _ => Q (if b < a then a else b, ()) m

def schedElimDticksSpec : Spec [i64, .bool] [i64] :=
  fun (h, _initial, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧ ∀ dticks : BitVec 64, Q (dticks, ()) m

def m7LcgNextSpec : Spec [i64] [i64] :=
  fun (h, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      ∀ m',
        let rng' := m7LcgNextVal s.scratch.rng_state
        let s' : FullState := { s with scratch := { s.scratch with rng_state := rng' } }
        (FullMem c s' ⋆ R) m' → Q (rng' >>> 32, ()) m'

def m7Get64Spec : Spec [i64, i64] [i64] :=
  fun (h, idx, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      Q (if idx.toNat < 63 then m7Get64Val s.scratch.glue_used idx.toNat else 0#64, ()) m

def m7Set64Spec : Spec [i64, i64, i64] [] :=
  fun (h, idx, val, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      ∀ m',
        let gu' := if idx.toNat < 63 then m7Set64List s.scratch.glue_used idx.toNat val
                   else s.scratch.glue_used
        let s' : FullState := { s with scratch := { s.scratch with glue_used := gu' } }
        (FullMem c s' ⋆ R) m' → Q () m'

def step13M7StateInitSpec : Spec [i64] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ _ s s' =>
      FullExtScratchPres s s' ∧ M7GuPrefixPres s s' ∧ M7StateInitOk s'.scratch.glue_used)

def step13EmaSwapSpec : Spec [i64, i64, i64] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _, _, ()) _ => h = c.hdr)
    (fun _ _ _ s s' =>
      FullExtScratchPres s s' ∧ M7GuPrefixPres s s' ∧ M7StateInitOk s'.scratch.glue_used)

/-- Canonical spec table for `Src.Limits.fns` (`15` functions, 1:1 order). -/
def specs : List SpecEntry :=
  [ ⟨"full_isqrt",          [i64],           [i64], fullIsqrtSpec,       true⟩
  , ⟨"full_ilog10",         [i64],           [i64], fullIlog10Spec,      true⟩
  , ⟨"full_tick_rel",       [i64],           [],    fullTickRelSpec,     true⟩
  , ⟨"full_scale_delta_m5", [i64, i64],      [i64], schedScaleDeltaSpec, true⟩
  , ⟨"full_ema_update",     [i64, i64],      [],    fullEmaUpdateSpec,   true⟩
  , ⟨"full_scale_delta",    [i64, i64],      [i64], schedScaleDeltaSpec, true⟩
  , ⟨"full_fill_u64_m7",    [i64, i64, i64], [],    m7FillU64Spec,       true⟩
  , ⟨"full_sort_u32",       [i64, i32],      [],    fullSortU32Spec,     true⟩
  , ⟨"full_max_u64",        [i64, i64],      [i64], schedMaxU64Spec,     true⟩
  , ⟨"full_elim_dticks",    [i64, .bool],    [i64], schedElimDticksSpec, true⟩
  , ⟨"full_lcg_next_m7",    [i64],           [i64], m7LcgNextSpec,       true⟩
  , ⟨"full_m7_get64",       [i64, i64],      [i64], m7Get64Spec,         true⟩
  , ⟨"full_m7_set64",       [i64, i64, i64], [],    m7Set64Spec,         true⟩
  , ⟨"full_m7_state_init",  [i64],           [],    step13M7StateInitSpec, true⟩
  , ⟨"full_ema_swap_m7",    [i64, i64, i64], [],    step13EmaSwapSpec,   true⟩ ]

end -- @[expose] public section

public section

/-! ## `XFree` Proofs & Table Invariants -/

theorem fullIsqrtSpec_xfree : fullIsqrtSpec.XFree := by xfree
theorem fullIlog10Spec_xfree : fullIlog10Spec.XFree := by xfree
theorem fullTickRelSpec_xfree : fullTickRelSpec.XFree := by xfree
theorem schedScaleDeltaSpec_xfree : schedScaleDeltaSpec.XFree := by xfree
theorem fullEmaUpdateSpec_xfree : fullEmaUpdateSpec.XFree := by xfree
theorem m7FillU64Spec_xfree : m7FillU64Spec.XFree := by xfree
theorem fullSortU32Spec_xfree : fullSortU32Spec.XFree := by xfree
theorem schedMaxU64Spec_xfree : schedMaxU64Spec.XFree := by xfree
theorem schedElimDticksSpec_xfree : schedElimDticksSpec.XFree := by xfree
theorem m7LcgNextSpec_xfree : m7LcgNextSpec.XFree := by xfree
theorem m7Get64Spec_xfree : m7Get64Spec.XFree := by xfree
theorem m7Set64Spec_xfree : m7Set64Spec.XFree := by xfree
theorem step13M7StateInitSpec_xfree : step13M7StateInitSpec.XFree := by xfree
theorem step13EmaSwapSpec_xfree : step13EmaSwapSpec.XFree := by xfree

theorem specs_xfree : ∀ e ∈ specs, e.spec.XFree := by
  intro e he
  simp only [specs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact fullIsqrtSpec_xfree
  · exact fullIlog10Spec_xfree
  · exact fullTickRelSpec_xfree
  · exact schedScaleDeltaSpec_xfree
  · exact fullEmaUpdateSpec_xfree
  · exact schedScaleDeltaSpec_xfree
  · exact m7FillU64Spec_xfree
  · exact fullSortU32Spec_xfree
  · exact schedMaxU64Spec_xfree
  · exact schedElimDticksSpec_xfree
  · exact m7LcgNextSpec_xfree
  · exact m7Get64Spec_xfree
  · exact m7Set64Spec_xfree
  · exact step13M7StateInitSpec_xfree
  · exact step13EmaSwapSpec_xfree

theorem specs_sigs : specs.map SpecEntry.sig = Src.Limits.fns.map Fn.sig := rfl

theorem specs_nodup : (specs.map SpecEntry.name).Nodup := by decide

/-! ## Pure `glue_used` / `u64Of32Pair` Helper Lemmas -/

theorem u64Of32Pair_split (v : BitVec 64) :
    u64Of32Pair (v.setWidth 32) ((v >>> 32).setWidth 32) = v := by
  apply BitVec.eq_of_getElem_eq
  intro k hk
  by_cases h32 : k < 32
  · simp [u64Of32Pair, hk, h32]
  · simp [u64Of32Pair, hk, h32, show k - 32 < 32 by omega, show 32 + (k - 32) = k by omega]

theorem m7Set64List_length (gu : List (BitVec 32)) (idx : Nat) (val : BitVec 64) :
    (m7Set64List gu idx val).length = gu.length := by
  simp [m7Set64List]

theorem m7Set64List_get_lt {gu : List (BitVec 32)} {idx k : Nat} (val : BitVec 64) (hk : k < idx) :
    (m7Set64List gu idx val)[k]? = gu[k]? := by
  unfold m7Set64List
  rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]

theorem m7Get64Val_set64_self {gu : List (BitVec 32)} {idx : Nat} (val : BitVec 64)
    (hi : idx + 1 < gu.length) :
    m7Get64Val (m7Set64List gu idx val) idx = val := by
  unfold m7Get64Val m7Set64List
  rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega),
    List.getElem?_set_self (by simp; omega)]
  exact u64Of32Pair_split val

theorem m7Get64Val_set64_ne {gu : List (BitVec 32)} {i j : Nat} (val : BitVec 64)
    (hdisj : i + 1 < j ∨ j + 1 < i) :
    m7Get64Val (m7Set64List gu i val) j = m7Get64Val gu j := by
  unfold m7Get64Val m7Set64List
  have h1 : i ≠ j := by omega
  have h2 : i + 1 ≠ j := by omega
  have h3 : i ≠ j + 1 := by omega
  have h4 : i + 1 ≠ j + 1 := by omega
  rw [List.getElem?_set_ne h2, List.getElem?_set_ne h1,
    List.getElem?_set_ne h4, List.getElem?_set_ne h3]

theorem M7GuPrefixPres.refl (s : FullState) : M7GuPrefixPres s s := fun _ _ => rfl

theorem M7GuPrefixPres.trans {s1 s2 s3 : FullState}
    (h1 : M7GuPrefixPres s1 s2) (h2 : M7GuPrefixPres s2 s3) : M7GuPrefixPres s1 s3 :=
  fun k hk => (h2 k hk).trans (h1 k hk)

theorem M7StateInitOk.of_set64 {gu : List (BitVec 32)} (h : M7StateInitOk gu)
    {idx : Nat} (hidx : 38 ≤ idx) (val : BitVec 64) :
    M7StateInitOk (m7Set64List gu idx val) := by
  refine ⟨by rw [m7Set64List_length]; exact h.1, ?_⟩
  change m7Get64Val (m7Set64List gu idx val) m7GuMagicIdx = m7SearchMagic
  rw [m7Get64Val_set64_ne val (by dsimp only [m7GuMagicIdx]; omega)]
  exact h.2

end -- public section

end LeanQbe.T.Examples.Kissat.Proof.Limits.Spec
