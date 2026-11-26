module

public import LeanQbe.T.Bootstrap0.Sound0Part8
import LeanQbe.T.TargetLemmas
import LeanQbe.T.AbiLemmas
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Amd64.FrameLemmas
import LeanQbe.T.Amd64.IselLemmas1
import LeanQbe.T.Amd64.IselLemmas2
import LeanQbe.T.Amd64.IselLemmas3
import LeanQbe.T.Amd64.IselLemmas4

/-!
# Bootstrap Stage B (`Sound0Part9a`): `Rega0` Environment, ABI, & Prefix Monotonicity

Establishes pure environment/ABI equivalences (`EnvTypesOk0`, `HoldsCanon640`,
`tupAbiHolds0`), frame/slot invariants (`FnFrameInv0`, `SlotsAgree0`, `GlEntriesSem0`,
`NodeContracts0`), and `regaStep0_st_mono` for `Sound0Part9`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Bootstrap0

open LeanQbe.T
open LeanQbe.T.Amd64
open Std Std.ExtHashMap

/-! ## 1. Pure Environment, Canonical 64-Bit Value, & ABI Register Equivalences -/

theorem u32_ofNat_toNat_lt9 {n : Nat} (h : n < 2 ^ 32) :
    (UInt32.ofNat n).toNat = n := by
  rw [u32_toNat_ofNat7, Nat.mod_eq_of_lt h]

private theorem u32_ofNat_succ9 {n : Nat} (h : n + 1 < 2 ^ 32) :
    UInt32.ofNat (n + 1) = UInt32.ofNat n + 1 := by
  apply u32_ext7
  rw [UInt32.toNat_add, UInt32.toNat_one, u32_ofNat_toNat_lt9 h,
    u32_ofNat_toNat_lt9 (by omega), Nat.mod_eq_of_lt h]

theorem u32_add_ofNat_succ9 (a : UInt32) (k : Nat) :
    a + UInt32.ofNat (k + 1) = (a + 1) + UInt32.ofNat k := by
  apply u32_ext7
  rw [UInt32.toNat_add, UInt32.toNat_add, UInt32.toNat_add, UInt32.toNat_one,
    u32_toNat_ofNat7, u32_toNat_ofNat7, Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_mod_mod,
    Nat.add_assoc, Nat.add_comm k 1]

private theorem listGetD_eq_getElem9 {α : Type} :
    ∀ (xs : List α) (d : α) (i : Nat) (hi : i < xs.length), xs.getD i d = xs[i]'hi
  | [], _, _, hi => absurd hi (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => rfl
  | _ :: xs, d, k + 1, hi => listGetD_eq_getElem9 xs d k (Nat.lt_of_succ_lt_succ hi)

private theorem listGet?_eq_some_iff9 {α : Type} :
    ∀ (xs : List α) (i : Nat) (x : α),
      listGet? xs i = some x ↔ ∃ hi : i < xs.length, xs[i]'hi = x
  | [], _, _ =>
    Iff.intro (fun h => by cases h) (fun ⟨hi, _⟩ => absurd hi (Nat.not_lt_zero _))
  | a :: xs, 0, x => by
    dsimp only [listGet?]
    simp only [Option.some.injEq, List.length_cons, Nat.zero_lt_succ,
      List.getElem_cons_zero, exists_const]
  | a :: xs, k + 1, x => by
    dsimp only [listGet?]
    simp only [listGet?_eq_some_iff9 xs k x, List.length_cons, Nat.succ_lt_succ_iff,
      List.getElem_cons_succ]

private theorem castTy_ty0_refl (t : Ty0) (v : Val (ty0ToTy t)) :
    castTy (ty0ToTy t) (ty0ToTy t) v = some v := by
  cases t <;> dsimp only [ty0ToTy, castTy] <;> first | rfl | exact dif_pos rfl

/-- Type agreement between static `vT : List Ty0` and runtime heterogeneous `vs`. -/
@[expose] def EnvTypesOk0 : List Ty0 → List ((t : Ty) × Val t) → Prop
  | [], [] => True
  | t :: ts, ⟨ty, _⟩ :: vs => ty = ty0ToTy t ∧ EnvTypesOk0 ts vs
  | _, _ => False

theorem envTypesOk0_length {ts : List Ty0} {vs : List ((t : Ty) × Val t)}
    (h : EnvTypesOk0 ts vs) : ts.length = vs.length := by
  induction ts generalizing vs with
  | nil => cases vs <;> first | rfl | exact False.elim h
  | cons _ _ ih => cases vs with
    | nil => exact False.elim h
    | cons _ _ => exact congrArg Nat.succ (ih h.2)

theorem envTypesOk0_getElem {ts : List Ty0} {vs : List ((t : Ty) × Val t)}
    (h : EnvTypesOk0 ts vs) {i : Nat} (hi1 : i < ts.length) (hi2 : i < vs.length) :
    (vs[i]'hi2).1 = ty0ToTy (ts[i]'hi1) := by
  induction ts generalizing vs i with
  | nil => exact absurd hi1 (Nat.not_lt_zero _)
  | cons _ _ ih =>
    cases vs with
    | nil => exact False.elim h
    | cons _ _ =>
      cases i with
      | zero => exact h.1
      | succ k => exact ih h.2 (Nat.lt_of_succ_lt_succ hi1) (Nat.lt_of_succ_lt_succ hi2)

theorem envTypesOk0_cons {t : Ty0} {v : Val (ty0ToTy t)}
    {ts : List Ty0} {vs : List ((t : Ty) × Val t)} (h : EnvTypesOk0 ts vs) :
    EnvTypesOk0 (t :: ts) (⟨ty0ToTy t, v⟩ :: vs) := ⟨rfl, h⟩

theorem envTypesOk0_pushTup :
    ∀ {ts : List Ty0} (xs : Tup Val (ty0ListToTy ts))
      {vT : List Ty0} {vs : List ((t : Ty) × Val t)},
      EnvTypesOk0 vT vs → EnvTypesOk0 (pushTys0 ts vT) (pushTup xs vs)
  | [], (), _, _, h => h
  | t :: _, (x, xs), _, _, h =>
    envTypesOk0_pushTup xs (envTypesOk0_cons (t := t) (v := x) h)

theorem pushFreshVids0_drop (m : Nat) (nv : UInt32) (venv : List UInt32) :
    (pushFreshVids0 m nv venv).drop m = venv := by
  induction m generalizing nv venv with
  | zero => rfl
  | succ k ih =>
    rw [pushFreshVids0_succ_head, List.drop_succ_cons]
    exact ih nv venv

theorem pushTys0_length9 (ts acc : List Ty0) :
    (pushTys0 ts acc).length = acc.length + ts.length := by
  rw [pushTys0_eq_pushTypes, pushTypes_length]

theorem pushTys0_drop (ts acc : List Ty0) :
    (pushTys0 ts acc).drop ts.length = acc := by
  induction ts generalizing acc with
  | nil => rfl
  | cons t rest ih =>
    dsimp only [pushTys0, List.length_cons]
    have h := ih (t :: acc)
    have hr : ∀ {α : Type} (xs : List α) (n : Nat) (y : α) (ys : List α),
        xs.drop n = y :: ys → xs.drop (n + 1) = ys := by
      intro α xs n y ys hd
      rw [← List.drop_drop, hd, List.drop_one, List.tail_cons]
    exact hr _ rest.length t acc h

private theorem pushTup_length_aux :
    ∀ {tys : List Ty} (xs : Tup Val tys) (vs : List ((t : Ty) × Val t)),
      (pushTup xs vs).length = vs.length + tys.length
  | [], xs, vs => by cases xs; rfl
  | t :: tys, xs, vs => by
    rcases xs with ⟨x, rest⟩
    dsimp only [pushTup, List.length_cons]
    rw [pushTup_length_aux rest (⟨t, x⟩ :: vs)]
    simp only [List.length_cons]
    omega

private theorem pushTup_length9 {ts : List Ty0} (xs : Tup Val (ty0ListToTy ts))
    (vs : List ((t : Ty) × Val t)) :
    (pushTup xs vs).length = vs.length + ts.length := by
  have h : (ty0ListToTy ts).length = ts.length := List.length_map ..
  exact (pushTup_length_aux xs vs).trans (congrArg (vs.length + ·) h)

theorem pushTup_drop_aux :
    ∀ {tys : List Ty} (xs : Tup Val tys) (vs : List ((t : Ty) × Val t)),
      (pushTup xs vs).drop tys.length = vs
  | [], xs, vs => by cases xs; rfl
  | t :: tys, xs, vs => by
    rcases xs with ⟨x, rest⟩
    dsimp only [pushTup, List.length_cons]
    have h := pushTup_drop_aux rest (⟨t, x⟩ :: vs)
    rw [← List.drop_drop, h, List.drop_one, List.tail_cons]

theorem pushTup_drop {ts : List Ty0} (xs : Tup Val (ty0ListToTy ts))
    (vs : List ((t : Ty) × Val t)) :
    (pushTup xs vs).drop ts.length = vs := by
  have h : (ty0ListToTy ts).length = ts.length := List.length_map ..
  exact h ▸ pushTup_drop_aux xs vs

theorem list_drop_drop9 {α : Type} (xs : List α) (a b : Nat) :
    (xs.drop a).drop b = xs.drop (a + b) := by
  rw [List.drop_drop, Nat.add_comm]

private theorem list_getElem_drop9 {α : Type} (xs : List α) {p i : Nat}
    (hp : p + i < xs.length) :
    (xs.drop p)[i]'(by rw [List.length_drop]; omega) = xs[p + i]'hp :=
  List.getElem_drop

private theorem lookupV_ty0_some {vs : List ((t : Ty) × Val t)} {k : Nat}
    (hk : k < vs.length) {t0 : Ty0} (hty : (vs[k]'hk).1 = ty0ToTy t0) {v : Val (ty0ToTy t0)}
    (hl : lookupV vs (ty0ToTy t0) k = some v) :
    vs[k]'hk = ⟨ty0ToTy t0, v⟩ := by
  induction vs generalizing k with
  | nil => exact absurd hk (Nat.not_lt_zero _)
  | cons p rest ih =>
    rcases p with ⟨pt, pv⟩
    cases k with
    | zero =>
      dsimp only [List.getElem_cons_zero] at hty ⊢
      subst hty
      dsimp only [lookupV, listGet?] at hl
      rw [castTy_ty0_refl] at hl
      injection hl with hv
      subst hv; rfl
    | succ k' =>
      exact ih (Nat.lt_of_succ_lt_succ hk) hty hl

/-- Canonical 64-bit word equality between `v0 : (t : Ty) × Val t` typed by `t0 : Ty0` and `w`. -/
@[expose] def HoldsCanon640 : Ty0 → ((t : Ty) × Val t) → BitVec 64 → Prop
  | .bool, ⟨.bool, b⟩, w => w = toCanon64 .bool b
  | .b8, ⟨.bits 8, v⟩, w => w = toCanon64 .b8 v
  | .b16, ⟨.bits 16, v⟩, w => w = toCanon64 .b16 v
  | .b32, ⟨.bits 32, v⟩, w => w = toCanon64 .b32 v
  | .b64, ⟨.bits 64, v⟩, w => w = toCanon64 .b64 v
  | _, _, _ => False

theorem holdsCanon640_iff {t0 : Ty0} {v0 : (t : Ty) × Val t} {w : BitVec 64}
    (hty : v0.1 = ty0ToTy t0) :
    HoldsCanon640 t0 v0 w ↔
      ∃ v : Val (ty0ToTy t0), v0 = ⟨ty0ToTy t0, v⟩ ∧ w = toCanon64 t0 v := by
  rcases v0 with ⟨ty, val⟩
  dsimp only at hty
  subst hty
  cases t0 with
  | bool | b8 | b16 | b32 | b64 =>
    constructor
    · intro h; exact ⟨val, rfl, h⟩
    · rintro ⟨v, heq, hw⟩
      have h' : val = v := eq_of_heq (Sigma.mk.inj heq).2
      subst h'; exact hw

theorem holdsCanon640_mk {t0 : Ty0} (v : Val (ty0ToTy t0)) :
    HoldsCanon640 t0 ⟨ty0ToTy t0, v⟩ (toCanon64 t0 v) := by
  cases t0 <;> rfl

/-- Project `Tup Val (ty0ListToTy ts)` to canonical 64-bit words. -/
@[expose] def tupToCanon64s :
    (ts : List Ty0) → Tup Val (ty0ListToTy ts) → List (BitVec 64)
  | [], () => []
  | t :: ts, (v, vs) => toCanon64 t v :: tupToCanon64s ts vs

theorem tupToCanon64s_length (ts : List Ty0) (xs : Tup Val (ty0ListToTy ts)) :
    (tupToCanon64s ts xs).length = ts.length := by
  induction ts with
  | nil => rfl
  | cons _ _ ih => rcases xs with ⟨_, _⟩; exact congrArg Nat.succ (ih _)

theorem tupToCanon64s_cons_getElem {t : Ty0} {ts : List Ty0}
    (v : Val (ty0ToTy t)) (vs : Tup Val (ty0ListToTy ts)) (k : Nat)
    (h1 : k + 1 < (tupToCanon64s (t :: ts) (v, vs)).length)
    (h2 : k < (tupToCanon64s ts vs).length) :
    (tupToCanon64s (t :: ts) (v, vs))[k + 1]'h1 = (tupToCanon64s ts vs)[k]'h2 := rfl

theorem canon64_setWidth_tyWidth0 (t : Ty0) (v : Val (ty0ToTy t)) :
    ((toCanon64 t v).setWidth (tyWidth0 t).bits).setWidth 64 = toCanon64 t v := by
  cases t with
  | bool => cases v <;> decide
  | b8 | b16 | b32 =>
    dsimp only [tyWidth0, Width.bits, toCanon64, ty0ToTy] at v ⊢
    have hlt := v.isLt
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    omega
  | b64 =>
    dsimp only [tyWidth0, Width.bits, toCanon64, ty0ToTy] at v ⊢
    rw [BitVec.setWidth_eq, BitVec.setWidth_eq]

theorem tupToCanon64s_canon_ok (ts : List Ty0) (xs : Tup Val (ty0ListToTy ts))
    (j : Nat) (hj1 : j < ts.length) (hj2 : j < (tupToCanon64s ts xs).length) :
    (((tupToCanon64s ts xs)[j]'hj2).setWidth (tyWidth0 (ts[j]'hj1)).bits).setWidth 64 =
      (tupToCanon64s ts xs)[j]'hj2 := by
  induction ts generalizing j with
  | nil => exact absurd hj1 (Nat.not_lt_zero _)
  | cons t ts ih =>
    rcases xs with ⟨x, xs⟩
    cases j with
    | zero => exact canon64_setWidth_tyWidth0 t x
    | succ k => exact ih xs k (Nat.lt_of_succ_lt_succ hj1) (Nat.lt_of_succ_lt_succ hj2)

/-- Flat register specification for SysV argument (`useRet = false`) or return (`true`) tuples. -/
@[expose] def tupAbiHolds0 (s : MachineData) (useRet : Bool) (i : Nat) :
    (ts : List Ty0) → Tup Val (ty0ListToTy ts) → Prop
  | [], () => True
  | t :: ts, (v, vs) =>
    s.regs.get64 (abiRegAt0 useRet (UInt32.ofNat i)) = toCanon64 t v ∧
    tupAbiHolds0 s useRet (i + 1) ts vs

theorem tupAbiHolds0_of_regs :
    ∀ (useRet : Bool) (i : Nat) (ts : List Ty0) (xs : Tup Val (ty0ListToTy ts)) (s : MachineData),
      (∀ (j : Nat) (hj : j < ts.length),
        s.regs.get64 (abiRegAt0 useRet (UInt32.ofNat (i + j))) =
          (tupToCanon64s ts xs)[j]'(by rw [tupToCanon64s_length]; exact hj)) →
      tupAbiHolds0 s useRet i ts xs
  | _, _, [], _, _, _ => trivial
  | useRet, i, t :: ts, xs, s, h => by
    dsimp only [ty0ListToTy, List.map_cons] at xs ⊢
    rcases xs with ⟨v, vs⟩
    dsimp only [tupAbiHolds0]
    refine ⟨?_, tupAbiHolds0_of_regs useRet (i + 1) ts vs s fun j hj => ?_⟩
    · have h0 := h 0 (Nat.zero_lt_succ ts.length)
      dsimp only [tupToCanon64s, List.getElem_cons_zero] at h0
      rw [Nat.add_zero] at h0
      exact h0
    · have hj' := h (j + 1) (Nat.succ_lt_succ hj)
      dsimp only [tupToCanon64s, List.getElem_cons_succ] at hj'
      rwa [show i + (j + 1) = i + 1 + j by omega] at hj'

theorem tupAbiHolds0_to_regs :
    ∀ (useRet : Bool) (i : Nat) (ts : List Ty0) (xs : Tup Val (ty0ListToTy ts)) (s : MachineData),
      tupAbiHolds0 s useRet i ts xs →
      ∀ (j : Nat) (hj : j < ts.length),
        s.regs.get64 (abiRegAt0 useRet (UInt32.ofNat (i + j))) =
          (tupToCanon64s ts xs)[j]'(by rw [tupToCanon64s_length]; exact hj)
  | _, _, [], _, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | useRet, i, t :: ts, xs, s, h, 0, _ => by
    dsimp only [ty0ListToTy, List.map_cons, tupToCanon64s, List.getElem_cons_zero] at xs h ⊢
    rcases xs with ⟨v, vs⟩
    rw [Nat.add_zero]
    exact h.1
  | useRet, i, t :: ts, xs, s, h, j + 1, hj => by
    dsimp only [ty0ListToTy, List.map_cons, tupToCanon64s, List.getElem_cons_succ] at xs h ⊢
    rcases xs with ⟨v, vs⟩
    have hr := tupAbiHolds0_to_regs useRet (i + 1) ts vs s h.2 j (Nat.lt_of_succ_lt_succ hj)
    rwa [show i + (j + 1) = i + 1 + j by omega]

private theorem abiRegAt0_false_drop_head (k : Nat) (hk : k < 6) :
    ∃ gs', x64Frame.argRegs.drop k = abiRegAt0 false (UInt32.ofNat k) :: gs' := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

private theorem abiRegAt0_true_drop_head (k : Nat) (hk : k < 7) :
    ∃ gs', x64Frame.retRegs.drop k = abiRegAt0 true (UInt32.ofNat k) :: gs' := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

private theorem abiRegAt0_drop_tail {α : Type} :
    ∀ (k : Nat) (xs : List α) {r : α} {rs : List α},
      xs.drop k = r :: rs → xs.drop (k + 1) = rs
  | 0, [], _, _, h => by simp at h
  | 0, _ :: _, _, _, h => by simpa using (List.cons.inj h).2
  | k + 1, [], _, _, h => by simp at h
  | k + 1, _ :: xs, _, _, h => by
    simpa [List.drop_succ_cons] using
      abiRegAt0_drop_tail k xs (by simpa [List.drop_succ_cons] using h)

theorem assignSig_ty0_iff :
    ∀ (useRet : Bool) (i : Nat) (ts : List Ty0) (xs : Tup Val (ty0ListToTy ts)) (s : MachineData)
      (_hlen : i + ts.length ≤ (if useRet then 7 else 6)),
      (∃ locs,
        x64ScalarIsa.assignSig (ty0ListToTy ts)
          ((if useRet then x64Frame.retRegs else x64Frame.argRegs).drop i) [] = some locs ∧
        TRel (x64ScalarMach.AbiHolds s) locs xs) ↔
      tupAbiHolds0 s useRet i ts xs
  | _, _, [], xs, _, _ => by
    cases xs; exact ⟨fun _ => trivial, fun _ => ⟨(), rfl, .nil⟩⟩
  | useRet, i, t :: ts, (v, vs), s, hlen => by
    have hi : i < (if useRet then 7 else 6) := by simp only [List.length_cons] at hlen; omega
    have hdrop :
        ∃ gs', (if useRet then x64Frame.retRegs else x64Frame.argRegs).drop i =
          abiRegAt0 useRet (UInt32.ofNat i) :: gs' := by
      cases useRet
      · exact abiRegAt0_false_drop_head i hi
      · exact abiRegAt0_true_drop_head i hi
    obtain ⟨gs', hgs⟩ := hdrop
    have hgs1 : (if useRet then x64Frame.retRegs else x64Frame.argRegs).drop (i + 1) = gs' :=
      abiRegAt0_drop_tail i _ hgs
    have ih := assignSig_ty0_iff useRet (i + 1) ts vs s
      (by simp only [List.length_cons] at hlen; omega)
    have hbw8 : x64ScalarIsa.frame.bitWidths.contains 8 = true := by decide
    have hbw16 : x64ScalarIsa.frame.bitWidths.contains 16 = true := by decide
    have hbw32 : x64ScalarIsa.frame.bitWidths.contains 32 = true := by decide
    have hbw64 : x64ScalarIsa.frame.bitWidths.contains 64 = true := by decide
    have hass : ∀ r (locs' : Tup (AbiReg Reg64 Empty) (ty0ListToTy ts)),
        x64ScalarIsa.assignSig (ty0ListToTy ts) gs' [] = some locs' →
        x64ScalarIsa.assignSig (ty0ListToTy (t :: ts)) (r :: gs') [] =
          some (AbiReg.gpr r, locs') := fun r locs' hl => by
      cases t
      · change Option.map (AbiReg.gpr r, ·) (x64ScalarIsa.assignSig (ty0ListToTy ts) gs' []) = _
        rw [hl]; rfl
      · change (if x64ScalarIsa.frame.bitWidths.contains 8 = true then
            Option.map (AbiReg.gpr r, ·) (x64ScalarIsa.assignSig (ty0ListToTy ts) gs' [])
          else none) = _
        simp only [hbw8, ↓reduceIte, hl]; rfl
      · change (if x64ScalarIsa.frame.bitWidths.contains 16 = true then
            Option.map (AbiReg.gpr r, ·) (x64ScalarIsa.assignSig (ty0ListToTy ts) gs' [])
          else none) = _
        simp only [hbw16, ↓reduceIte, hl]; rfl
      · change (if x64ScalarIsa.frame.bitWidths.contains 32 = true then
            Option.map (AbiReg.gpr r, ·) (x64ScalarIsa.assignSig (ty0ListToTy ts) gs' [])
          else none) = _
        simp only [hbw32, ↓reduceIte, hl]; rfl
      · change (if x64ScalarIsa.frame.bitWidths.contains 64 = true then
            Option.map (AbiReg.gpr r, ·) (x64ScalarIsa.assignSig (ty0ListToTy ts) gs' [])
          else none) = _
        simp only [hbw64, ↓reduceIte, hl]; rfl
    have hnone : ∀ r,
        x64ScalarIsa.assignSig (ty0ListToTy ts) gs' [] = none →
        x64ScalarIsa.assignSig (ty0ListToTy (t :: ts)) (r :: gs') [] = none :=
          fun r hl => by
      cases t
      · change Option.map (AbiReg.gpr r, ·) (x64ScalarIsa.assignSig (ty0ListToTy ts) gs' []) = none
        rw [hl]; rfl
      · change (if x64ScalarIsa.frame.bitWidths.contains 8 = true then
            Option.map (AbiReg.gpr r, ·) (x64ScalarIsa.assignSig (ty0ListToTy ts) gs' [])
          else none) = none
        simp only [hbw8, ↓reduceIte, hl]; rfl
      · change (if x64ScalarIsa.frame.bitWidths.contains 16 = true then
            Option.map (AbiReg.gpr r, ·) (x64ScalarIsa.assignSig (ty0ListToTy ts) gs' [])
          else none) = none
        simp only [hbw16, ↓reduceIte, hl]; rfl
      · change (if x64ScalarIsa.frame.bitWidths.contains 32 = true then
            Option.map (AbiReg.gpr r, ·) (x64ScalarIsa.assignSig (ty0ListToTy ts) gs' [])
          else none) = none
        simp only [hbw32, ↓reduceIte, hl]; rfl
      · change (if x64ScalarIsa.frame.bitWidths.contains 64 = true then
            Option.map (AbiReg.gpr r, ·) (x64ScalarIsa.assignSig (ty0ListToTy ts) gs' [])
          else none) = none
        simp only [hbw64, ↓reduceIte, hl]; rfl
    constructor
    · rintro ⟨locs, hlocs, hrel⟩
      rw [hgs] at hlocs
      cases hts' : x64ScalarIsa.assignSig (ty0ListToTy ts) gs' [] with
      | none => rw [hnone _ hts'] at hlocs; cases hlocs
      | some locs' =>
        rw [hass _ locs' hts'] at hlocs
        injection hlocs with heq; subst heq
        cases hrel with
        | cons h1 h2 =>
          refine ⟨(abiGprHolds_ty0_iff _ t v).mp h1, ih.mp ?_⟩
          exact ⟨locs', hgs1 ▸ hts', h2⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨locs', hlocs', hrel'⟩ := ih.mpr h2
      rw [hgs1] at hlocs'
      refine ⟨(.gpr (abiRegAt0 useRet (UInt32.ofNat i)), locs'), ?_,
        .cons (abiGprHolds_of_canon64 h1) hrel'⟩
      rw [hgs]
      exact hass (abiRegAt0 useRet (UInt32.ofNat i)) locs' hlocs'

theorem argsIn_ty0_iff {as : List Ty0} (has : as.length ≤ 6)
    (args : Tup Val (ty0ListToTy as)) (s : MachineData) :
    x64ScalarTarget.ArgsIn args s ↔ tupAbiHolds0 s false 0 as args := by
  change (∃ locs,
    x64ScalarIsa.assignSig (ty0ListToTy as)
      ((if false then x64Frame.retRegs else x64Frame.argRegs).drop 0) [] = some locs ∧
    TRel (x64ScalarMach.AbiHolds s) locs args) ↔ tupAbiHolds0 s false 0 as args
  exact assignSig_ty0_iff false 0 as args s (by simpa using has)

theorem retsIn_ty0_iff {bs : List Ty0} (hbs : bs.length ≤ 7)
    (rets : Tup Val (ty0ListToTy bs)) (s : MachineData) :
    x64ScalarTarget.RetsIn rets s ↔ tupAbiHolds0 s true 0 bs rets := by
  change (∃ locs,
    x64ScalarIsa.assignSig (ty0ListToTy bs)
      ((if true then x64Frame.retRegs else x64Frame.argRegs).drop 0) [] = some locs ∧
    TRel (x64ScalarMach.AbiHolds s) locs rets) ↔ tupAbiHolds0 s true 0 bs rets
  exact assignSig_ty0_iff true 0 bs rets s (by simpa using hbs)

theorem tupAbiHolds0_frame {s s' : MachineData} {useRet : Bool} {clob : List Reg64}
    (hkeeps : ∀ r, r ∉ clob → s'.regs.get64 r = s.regs.get64 r) :
    ∀ {i : Nat} {ts : List Ty0} {xs : Tup Val (ty0ListToTy ts)},
      (∀ j < ts.length, abiRegAt0 useRet (UInt32.ofNat (i + j)) ∉ clob) →
      tupAbiHolds0 s useRet i ts xs → tupAbiHolds0 s' useRet i ts xs
  | _, [], (), _, _ => trivial
  | i, _ :: ts, (_, xs), hdisj, ⟨h1, h2⟩ => by
    refine ⟨(hkeeps _ (by simpa [Nat.add_zero] using hdisj 0 (Nat.zero_lt_succ _))).trans h1, ?_⟩
    exact tupAbiHolds0_frame hkeeps
      (fun j hj => by
        simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hdisj (j + 1) (Nat.succ_lt_succ hj))
      h2

theorem abiRegAt0_not_in_rsp_scratch (useRet : Bool) (i : UInt32) :
    abiRegAt0 useRet i ∉ ([.rsp, .r10, .r11] : List Reg64) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  dsimp only [abiRegAt0]
  cases useRet <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> repeat' split
  all_goals rintro (c | c | c) <;> cases c

theorem calleeSaved_not_in_rsp_scratch :
    ∀ r ∈ x64Frame.calleeSaved, r ∉ ([.rsp, .r10, .r11] : List Reg64) := by
  intro r hr hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hm
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hm with c | c | c <;> cases c

theorem checkOp0_checkArgs0 {vT : List Ty0} {op : OpCode0} {args : List Arg0}
    (hc : checkOp0 vT op args = true) : checkArgs0 vT (op0ArgTys op) args = true := by
  cases op with
  | un u t =>
    dsimp only [checkOp0, checkOpArith0] at hc
    cases u <;> cases t
    all_goals first
      | contradiction
      | (rcases args with _ | ⟨a, _ | _⟩ <;> first
          | contradiction
          | (dsimp only [op0ArgTys, checkArgs0]; dsimp only at hc; rw [hc]; rfl))
  | bin b t =>
    dsimp only [checkOp0, checkOpArith0, checkBinOp0] at hc
    rcases args with _ | ⟨a, _ | ⟨bArg, _ | _⟩⟩ <;> try contradiction
    simp only [Bool.and_eq_true] at hc
    dsimp only [op0ArgTys, checkArgs0]; rw [hc.1.2, hc.2]; rfl
  | select t =>
    dsimp only [checkOp0, checkOpArith0] at hc
    rcases args with _ | ⟨c, _ | ⟨a, _ | ⟨bArg, _ | _⟩⟩⟩ <;> try contradiction
    simp only [Bool.and_eq_true] at hc
    dsimp only [op0ArgTys, checkArgs0]; rw [hc.1.1, hc.1.2, hc.2]; rfl
  | cmp _ t =>
    dsimp only [checkOp0] at hc
    rcases args with _ | ⟨a, _ | ⟨bArg, _ | _⟩⟩ <;> try contradiction
    simp only [Bool.and_eq_true] at hc
    dsimp only [op0ArgTys, checkArgs0]; rw [hc.1.2, hc.2]; rfl
  | conv c m n =>
    dsimp only [checkOp0, checkConv0] at hc
    cases c <;> rcases args with _ | ⟨a, _ | _⟩ <;> try contradiction
    all_goals simp only [Bool.and_eq_true] at hc
    all_goals (dsimp only [op0ArgTys, checkArgs0]; rw [hc.2]; rfl)
  | div _ w =>
    dsimp only [checkOp0] at hc
    rcases args with _ | ⟨a, _ | ⟨bArg, _ | _⟩⟩ <;> try contradiction
    simp only [Bool.and_eq_true] at hc
    dsimp only [op0ArgTys, checkArgs0]; rw [hc.1, hc.2]; rfl
  | umulw64 => dsimp only [checkOp0] at hc; cases hc

theorem op0ArgTys_length_le (op : OpCode0) : (op0ArgTys op).length ≤ 3 := by
  cases op with
  | conv c _ _ => cases c <;> simp [op0ArgTys]
  | _ => simp [op0ArgTys]

theorem opArgsIn0_of_regs (op : OpCode0) (argv : Tup Val (ty0ListToTy (op0ArgTys op)))
    (s : MachineData)
    (h : ∀ (j : Nat) (hj : j < (op0ArgTys op).length),
      s.regs.get64 (abiRegAt0 false (UInt32.ofNat j)) =
        (tupToCanon64s (op0ArgTys op) argv)[j]'(by rw [tupToCanon64s_length]; exact hj)) :
    OpArgsIn0 s op argv := by
  cases op with
  | un _ t =>
    rcases argv with ⟨a, ⟨⟩⟩
    exact h 0 (by simp [op0ArgTys])
  | bin _ t | cmp _ t | div _ t =>
    rcases argv with ⟨a, b, ⟨⟩⟩
    exact ⟨h 0 (by simp [op0ArgTys]), h 1 (by simp [op0ArgTys])⟩
  | select t =>
    rcases argv with ⟨c, a, b, ⟨⟩⟩
    exact ⟨h 0 (by simp [op0ArgTys]), h 1 (by simp [op0ArgTys]), h 2 (by simp [op0ArgTys])⟩
  | conv c _ _ =>
    cases c <;> rcases argv with ⟨a, ⟨⟩⟩ <;> exact h 0 (by simp [op0ArgTys])
  | umulw64 =>
    rcases argv with ⟨a, b, ⟨⟩⟩
    exact ⟨h 0 (by simp [op0ArgTys]), h 1 (by simp [op0ArgTys])⟩

/-! ## 2. Frame, Slot-Agreement, Loop-Chain, & Worklist Splitting Invariants -/

/-- Function-level stack frame invariant maintained at every block/instruction boundary. -/
@[expose] def FnFrameInv0 (ns : UInt32) (s0 : MachineData) (ra0 : Int64) (n : Nat)
    (Rf : Mem 64 → Prop) (mCur : Mem 64) (s : MachineData) (σ : List (BitVec 64)) : Prop :=
  σ.length = ns.toNat ∧
  s.regs.get64 .rsp = s0.regs.get64 .rsp - BitVec.ofNat 64 (x64FrameSize ns.toNat) ∧
  (∀ r ∈ x64Frame.calleeSaved, s.regs.get64 r = s0.regs.get64 r) ∧
  (s.dmem =⋆
    Eq mCur ⋆ array64 (s.regs.get64 .rsp) σ ⋆
    x64ScalarFramePreds.Saved (s0.regs.get64 .rsp) ra0 ns.toNat ⋆
    region (s0.regs.get64 .rsp - BitVec.ofNat 64 n) (n - x64FrameSize ns.toNat) ⋆ Rf)

/-- Slot agreement for every live variable in task `(p, t)`. -/
@[expose] def SlotsAgree0 (esc : Array Nat) (preSt : PreSt0) (st : RegaSt0) (p : PreItem0)
    (t : RegaTask0) (vT : List Ty0) (vs : List ((ty : Ty) × Val ty))
    (σ : List (BitVec 64)) : Prop :=
  t.venv.length = vs.length ∧ EnvTypesOk0 vT vs ∧
  ∀ (idx : Nat) (_hi : idx < t.venv.length),
    let vid := t.venv[idx]
    LiveInTask0 esc preSt st p t vid.toNat →
    ∃ (hsl : (arrGetU0 st.vslot vid).toNat < σ.length) (hvs : idx < vs.length)
      (ht : idx < vT.length),
      HoldsCanon640 vT[idx] vs[idx] σ[(arrGetU0 st.vslot vid).toNat]

/-- Escaped outer-environment variables agree with `σ` under `vslot`. -/
@[expose] def EscOuterAgree0 (esc : Array Nat) (vslot : Array Nat) (info : LblInfo0)
    (outerVs : List ((ty : Ty) × Val ty)) (σ : List (BitVec 64)) : Prop :=
  info.outerVenv.length = outerVs.length ∧ EnvTypesOk0 info.outerVT outerVs ∧
  ∀ (idx : Nat) (_hi : idx < info.outerVenv.length),
    let vid := info.outerVenv[idx]
    esc.getD vid.toNat 0 = 1 →
    ∃ (hsl : (arrGetU0 vslot vid).toNat < σ.length) (hvs : idx < outerVs.length)
      (ht : idx < info.outerVT.length),
      HoldsCanon640 info.outerVT[idx] outerVs[idx] σ[(arrGetU0 vslot vid).toNat]

/-- Block parameter values `xs` sit in `tgts` slots of `σ`. -/
@[expose] def TupInSlots0 (σ : List (BitVec 64)) :
    List UInt32 → (ts : List Ty0) → Tup Val (ty0ListToTy ts) → Prop
  | [], [], () => True
  | s :: ss, t :: ts, (v, vs) =>
    (∃ hs : s.toNat < σ.length, σ[s.toNat] = toCanon64 t v) ∧ TupInSlots0 σ ss ts vs
  | _, _, _ => False

/-- Semantic contract for one enclosing `.group` label `info ∈ mCur.gl`. -/
@[expose] def GlEntrySem0 (h : Host) (symName : Sym0 → Sym) (post : MachineState → Prop)
    (ns : UInt32) (s0 : MachineData) (ra0 : Int64) (n : Nat) (Rf : Mem 64 → Prop)
    (esc : Array Nat) (st : RegaSt0) (cur : RegaTask0) (mCur : TaskMeta0)
    (vs : List ((ty : Ty) × Val ty)) (fnIdx : UInt32)
    (info : LblInfo0) (lentry : (ts : List Ty) × Cont ts) : Prop :=
  info.nxt.toNat ≤ cur.nextSlot.toNat ∧
  x64ScalarTarget.Defined h (label0ToSym symName (.loc fnIdx info.lbl)) ∧
  ∃ (outerVs : List ((ty : Ty) × Val ty)) (pLen : Nat),
    pLen + info.outerVenv.length = cur.venv.length ∧
    cur.venv.drop pLen = info.outerVenv ∧
    mCur.vT.drop pLen = info.outerVT ∧
    vs.drop pLen = outerVs ∧
    ∃ (J : Cont (ty0ListToTy info.pts)),
      lentry = ⟨ty0ListToTy info.pts, J⟩ ∧
      ∀ (xs : Tup Val (ty0ListToTy info.pts)) (m' : Mem 64),
        J xs m' →
        ∀ s' σ', FnFrameInv0 ns s0 ra0 n Rf m' s' σ' →
          EscOuterAgree0 esc st.vslot info outerVs σ' →
          TupInSlots0 σ' info.tgts info.pts xs →
          Eventually (x64ScalarMach.step h) post
            ⟨s', x64ScalarMach.labelAddr h (label0ToSym symName (.loc fnIdx info.lbl))⟩

/-- List pairing of `GlEntrySem0` across `mCur.gl` and `ls`. -/
@[expose] def GlEntriesSem0 (h : Host) (symName : Sym0 → Sym) (post : MachineState → Prop)
    (ns : UInt32) (s0 : MachineData) (ra0 : Int64) (n : Nat) (Rf : Mem 64 → Prop)
    (esc : Array Nat) (st : RegaSt0) (cur : RegaTask0) (mCur : TaskMeta0)
    (vs : List ((ty : Ty) × Val ty)) (fnIdx : UInt32) :
    List LblInfo0 → List ((ts : List Ty) × Cont ts) → Prop
  | [], [] => True
  | info :: glRest, lentry :: lsRest =>
    GlEntrySem0 h symName post ns s0 ra0 n Rf esc st cur mCur vs fnIdx info lentry ∧
    GlEntriesSem0 h symName post ns s0 ra0 n Rf esc st cur mCur vs fnIdx glRest lsRest
  | _, _ => False

mutual
/-- Per-AST-subtree stack & callee contract hypotheses matching `Γ` and `x64ScalarTarget`. -/
@[expose] def NodeContracts0 (h : Host) (symName : Sym0 → Sym) (Γ : Env) (ctx : LegalCtx0)
    (ns : UInt32) (n nX : Nat) : TFlat0 → Prop
  | .let1 _ _ k | .let2Umulw64 _ _ k | .load _ _ k | .store _ _ _ k =>
    NodeContracts0 h symName Γ ctx ns n nX k
  | .call fnSym as bs _ k =>
    (∃ bound, x64FrameSize ns.toNat + 8 + bound ≤ n ∧
      x64ScalarTarget.Defined h (symName fnSym) ∧
      x64ScalarTarget.FnSpec h (symName fnSym)
        (Γ (symName fnSym) (ty0ListToTy as) (ty0ListToTy bs)) bound nX) ∧
    NodeContracts0 h symName Γ ctx ns n nX k
  | .tailCall fnSym as _ =>
    ∃ bound, bound ≤ n ∧
      x64ScalarTarget.Defined h (symName fnSym) ∧
      x64ScalarTarget.FnSpec h (symName fnSym)
        (Γ (symName fnSym) (ty0ListToTy as) (ty0ListToTy ctx.curRs)) bound nX
  | .exit fnSym _ _ =>
    nX ≤ n ∧ x64ScalarTarget.Defined h (symName fnSym)
  | .jnz _ t e =>
    NodeContracts0 h symName Γ ctx ns n nX t ∧ NodeContracts0 h symName Γ ctx ns n nX e
  | .group bodies k =>
    BlocksContracts0 h symName Γ ctx ns n nX bodies ∧
    NodeContracts0 h symName Γ ctx ns n nX k
  | .jump _ _ | .ret _ | .hlt => True

/-- Block-list sibling of `NodeContracts0`. -/
@[expose] def BlocksContracts0 (h : Host) (symName : Sym0 → Sym) (Γ : Env) (ctx : LegalCtx0)
    (ns : UInt32) (n nX : Nat) : List (List Ty0 × TFlat0) → Prop
  | [] => True
  | (_, b) :: rest =>
    NodeContracts0 h symName Γ ctx ns n nX b ∧
    BlocksContracts0 h symName Γ ctx ns n nX rest
end

theorem blocksContracts0_mem {h : Host} {symName : Sym0 → Sym} {Γ : Env}
    {ctx : LegalCtx0} {ns : UInt32} {n nX : Nat} :
    ∀ {bs : List (List Ty0 × TFlat0)},
      BlocksContracts0 h symName Γ ctx ns n nX bs →
      ∀ p ∈ bs, NodeContracts0 h symName Γ ctx ns n nX p.2
  | [], _, _, hp => nomatch hp
  | _ :: _, hc, _, .head _ => by dsimp only [BlocksContracts0] at hc; exact hc.1
  | _ :: _, hc, p, .tail _ hp =>
    blocksContracts0_mem (by dsimp only [BlocksContracts0] at hc; exact hc.2) p hp

theorem nodeContracts0_lin {h : Host} {symName : Sym0 → Sym} {Γ : Env} {ctx : LegalCtx0}
    {ns : UInt32} {n nX : Nat} {node : TFlat0} (hc : NodeContracts0 h symName Γ ctx ns n nX node)
    (hlin : isTerm0 node = false) (hnj : ∀ c t e, node ≠ .jnz c t e)
    (hng : ∀ bs k, node ≠ .group bs k) :
    NodeContracts0 h symName Γ ctx ns n nX (linK0 node) := by
  cases node with
  | let1 _ _ _ | let2Umulw64 _ _ _ | load _ _ _ | store _ _ _ _ =>
    dsimp only [NodeContracts0] at hc; dsimp only [linK0]; exact hc
  | call _ _ _ _ _ => dsimp only [NodeContracts0] at hc; dsimp only [linK0]; exact hc.2
  | jnz _ _ _ => exact absurd rfl (hnj _ _ _)
  | group _ _ => exact absurd rfl (hng _ _)
  | tailCall _ _ _ | jump _ _ | ret _ | exit _ _ _ | hlt => simp [isTerm0] at hlin

theorem argSlotVal64_of_evalArg0Ty {esc : Array Nat} {preSt : PreSt0} {st : RegaSt0}
    {p : PreItem0} {t : RegaTask0} {vT : List Ty0} {vs : List ((ty : Ty) × Val ty)}
    {σ : List (BitVec 64)} {t0 : Ty0} {a : Arg0} {v : Val (ty0ToTy t0)}
    (hc : checkArg0 vT t0 a = true)
    (hag : SlotsAgree0 esc preSt st p t vT vs σ)
    (hev : evalArg0Ty vs (ty0ToTy t0) a = some v)
    (hlive : ∀ idx, a = .var idx →
      LiveInTask0 esc preSt st p t (listGetU32 t.venv idx).toNat) :
    ArgSlotVal64 t.venv st.vslot σ a (toCanon64 t0 v) := by
  cases a with
  | var idx =>
    obtain ⟨hv_len, henv, hslot⟩ := hag
    have hspec := checkArg0_spec hc
    dsimp only at hspec
    obtain ⟨hidx, hvt_eq⟩ := (listGet?_eq_some_iff9 vT idx.toNat t0).mp hspec
    have hidx_v : idx.toNat < t.venv.length := by
      have := envTypesOk0_length henv; omega
    have hidx_vs : idx.toNat < vs.length := hv_len ▸ hidx_v
    have hty_vs := envTypesOk0_getElem henv hidx hidx_vs
    dsimp only [evalArg0Ty] at hev
    have hvs_eq := lookupV_ty0_some hidx_vs (hty_vs.trans (by rw [hvt_eq])) hev
    have hvid_eq : listGetU32 t.venv idx = t.venv[idx.toNat]'hidx_v := by
      rw [listGetU32_eq_listGetD, listGetD_eq_getElem9 t.venv 0 idx.toNat hidx_v]
    have hlv := hlive idx rfl
    rw [hvid_eq] at hlv
    obtain ⟨hsl, hvs', ht', hcanon⟩ := hslot idx.toNat hidx_v hlv
    dsimp only [ArgSlotVal64]
    rw [hvid_eq]
    refine ⟨hsl, ?_⟩
    rw [hvt_eq, hvs_eq] at hcanon
    obtain ⟨v', hmk, hw⟩ := (holdsCanon640_iff (t0 := t0) rfl).mp hcanon
    rw [eq_of_heq (Sigma.mk.inj hmk).2]
    exact hw
  | immBool b =>
    have hspec := checkArg0_spec hc; dsimp only at hspec; subst hspec
    dsimp only [evalArg0Ty] at hev
    injection hev with hb; subst hb; rfl
  | immBits w val =>
    have hspec := checkArg0_spec hc; dsimp only at hspec; subst hspec
    cases w <;> (
      dsimp only [ty0ToTy, widthTy0] at hev v
      dsimp only [evalArg0Ty] at hev
      injection hev with hv
      rw [← hv]
      simp [ArgSlotVal64, toCanon64, widthTy0, Width.bits, BitVec.setWidth_eq]
      try (apply BitVec.eq_of_toNat_eq; simp [Nat.mod_eq_of_lt val.isLt]))

theorem argsSlotVal64_of_evalArgs0Ty {esc : Array Nat} {preSt : PreSt0} {st : RegaSt0}
    {p : PreItem0} {t : RegaTask0} {vT : List Ty0} {vs : List ((ty : Ty) × Val ty)}
    {σ : List (BitVec 64)} :
    ∀ {ts : List Ty0} {args : List Arg0} {argv : Tup Val (ty0ListToTy ts)},
      checkArgs0 vT ts args = true →
      SlotsAgree0 esc preSt st p t vT vs σ →
      evalArgs0Ty vs (ty0ListToTy ts) args = some argv →
      (∀ a ∈ args, ∀ idx, a = .var idx →
        LiveInTask0 esc preSt st p t (listGetU32 t.venv idx).toNat) →
      ArgsSlotVal64 t.venv st.vslot σ args (tupToCanon64s ts argv)
  | [], [], (), _, _, _, _ => trivial
  | [], _ :: _, _, hc, _, _, _ => by dsimp only [checkArgs0] at hc; cases hc
  | _ :: _, [], _, hc, _, _, _ => by dsimp only [checkArgs0] at hc; cases hc
  | t0 :: ts, a :: args, argv, hc, hag, hev, hlive => by
    dsimp only [checkArgs0] at hc
    cases hca : checkArg0 vT t0 a with
    | false => simp [hca] at hc
    | true =>
      rw [hca] at hc
      rcases argv with ⟨v', restv'⟩
      change evalArgs0Ty vs (ty0ToTy t0 :: ty0ListToTy ts) (a :: args) = some (v', restv') at hev
      dsimp only [evalArgs0Ty] at hev
      cases hea : evalArg0Ty vs (ty0ToTy t0) a with
      | none => rw [hea] at hev; cases hev
      | some v =>
        cases her : evalArgs0Ty vs (ty0ListToTy ts) args with
        | none => rw [hea, her] at hev; cases hev
        | some restv =>
          rw [hea, her] at hev
          injection hev with heq
          injection heq with hv_eq hr_eq
          subst hv_eq; subst hr_eq
          exact ⟨argSlotVal64_of_evalArg0Ty hca hag hea (hlive a List.mem_cons_self),
            argsSlotVal64_of_evalArgs0Ty hc hag her fun b hb =>
              hlive b (List.mem_cons_of_mem _ hb)⟩

private theorem spineUses0_ge_nodeArgsUses0 (vid : UInt32) (venv : List UInt32) (nv : UInt32)
    (n : TFlat0) : nodeArgsUses0 vid venv n ≤ spineUses0 vid venv nv n := by
  cases n <;> dsimp only [spineUses0, nodeArgsUses0] <;> omega

theorem liveInTask0_of_nodeArg {ctx : LegalCtx0} {fnIdx : UInt32} {fnMaxJump : Nat}
    {preRes : PreSt0} {nextSc : UInt32} {preSt : PreSt0} {curPre : PreItem0}
    {restPre : List PreItem0} {seenJnz : Bool} {st : RegaSt0} {ctrl : CtrlSt0}
    {cur : RegaTask0} {rest : List RegaTask0} {mCur : TaskMeta0} {restMeta : List TaskMeta0}
    (h : RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc preSt (curPre :: restPre) seenJnz st ctrl
      (cur :: rest) (mCur :: restMeta))
    {idx : UInt32} (hidx : idx.toNat < cur.venv.length)
    (huse : 0 < nodeArgsUses0 (listGetU32 cur.venv idx) cur.venv cur.node) :
    LiveInTask0 preRes.escaped preSt st curPre cur (listGetU32 cur.venv idx).toNat := by
  have hcur_ok := h.items_ok 0 (by simp) (by simp) (by simp)
  dsimp only [List.getElem_cons_zero] at hcur_ok
  obtain ⟨hpn, hpv, _, hvlt, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hcur_ok
  let vid := listGetU32 cur.venv idx
  have hvid_mem : vid ∈ cur.venv := by
    dsimp only [vid]; rw [listGetU32_eq_listGetD, listGetD_eq_getElem9 _ _ _ hidx]
    exact List.getElem_mem _
  have hvid_lt : vid.toNat < st.nextVid.toNat := hvlt vid hvid_mem
  have hvid_res : vid.toNat < preRes.nextVid.toNat :=
    Nat.lt_of_lt_of_le hvid_lt (by have := h.preRes_uses_lt_bd; omega)
  have hvid_eq : UInt32.ofNat vid.toNat = vid := UInt32.ofNat_toNat
  rcases h.preRes_es_bit vid.toNat hvid_res with he0 | he1
  · right
    have hsub := preRunAux0_sub_active h.pre_inv h.pre_run
    have hsc : curPre.scope.toNat = preSt.defScope.getD vid.toNat 0 := by
      by_cases he : curPre.scope.toNat = preSt.defScope.getD vid.toNat 0
      · exact he
      · exfalso
        have h0 := hsub.2 vid.toNat (h.st_nv ▸ hvid_lt) he0 curPre List.mem_cons_self
        simp only [he, ↓reduceIte] at h0
        rw [hpn, hpv, ← h.st_nv, hvid_eq] at h0
        have h1 := spineUses0_le_astUses0 cur.node vid cur.venv st.nextVid
        have h2 := spineUses0_ge_nodeArgsUses0 vid cur.venv st.nextVid cur.node
        exact absurd (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le huse h2) h1)
          (Nat.not_lt_of_le (Nat.le_of_eq h0))
    have hact : ActiveDefScope0 preSt (curPre :: restPre) vid.toNat :=
      ⟨h.st_nv ▸ hvid_lt, curPre, List.mem_cons_self, hsc⟩
    have hru := h.st_rem_active vid.toNat hvid_lt he0 hact
    rw [hvid_eq, ← h.st_nv] at hru
    have hss :
        sameScopeSpineSum0 vid (preSt.defScope.getD vid.toNat 0) st.nextVid (curPre :: restPre) =
          (if preSt.defScope.getD vid.toNat 0 = curPre.scope.toNat then
            spineUses0 vid curPre.venv st.nextVid curPre.node
          else 0) +
          sameScopeSpineSum0 vid (preSt.defScope.getD vid.toNat 0) st.nextVid restPre := rfl
    simp only [hsc.symm, ↓reduceIte] at hss
    rw [hpn, hpv] at hss
    have hge := spineUses0_ge_nodeArgsUses0 vid cur.venv st.nextVid cur.node
    refine ⟨he0, hsc, ?_⟩
    rw [hru, ← hsc, hss]
    exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le huse hge) (Nat.le_add_right _ _)
  · left; exact ⟨he1, hvid_eq.symm ▸ hvid_mem⟩

theorem nodeArgsUses0_pos_of_mem {venv : List UInt32} {args : List Arg0} {idx : UInt32}
    (ha : .var idx ∈ args) : 0 < argsUses0 (listGetU32 venv idx) venv args := by
  induction args with
  | nil => nomatch ha
  | cons a rest ih =>
    rcases List.mem_cons.mp ha with rfl | hb
    · dsimp only [argsUses0, argUses0]; simp only [↓reduceIte]; omega
    · dsimp only [argsUses0]; have := ih hb; omega

theorem nodeArgsUses0_pos_lin_term {venv : List UInt32} {node : TFlat0} {idx : UInt32} :
    (match node with
     | .let1 _ args _ | .call _ _ _ args _ | .tailCall _ _ args
     | .jump _ args | .ret args | .exit _ _ args => .var idx ∈ args
     | .let2Umulw64 a b _ | .store _ a b _ => a = .var idx ∨ b = .var idx
     | .load _ a _ | .jnz a _ _ => a = .var idx
     | _ => False) →
    0 < nodeArgsUses0 (listGetU32 venv idx) venv node := by
  intro hm
  cases node with
  | let1 _ args _ | call _ _ _ args _ | tailCall _ _ args
  | jump _ args | ret args | exit _ _ args =>
    exact nodeArgsUses0_pos_of_mem hm
  | let2Umulw64 a b _ | store _ a b _ =>
    rcases hm with rfl | rfl <;>
    · dsimp only [nodeArgsUses0, argUses0]; simp only [↓reduceIte]; omega
  | load _ a _ | jnz a _ _ =>
    subst hm; simp [nodeArgsUses0, argUses0]
  | hlt | group _ _ => exact False.elim hm

theorem slotsAgree0_after_rel_drop_none (esc : Array Nat) (preSt : PreSt0)
    {st st' : RegaSt0} {p : PreItem0} {t t' : RegaTask0} {vT : List Ty0}
    {vs : List ((ty : Ty) × Val ty)} {σ : List (BitVec 64)}
    (hag : SlotsAgree0 esc preSt st p t vT vs σ)
    (htv : t'.venv = t.venv)
    (hvsl : ∀ v < st.nextVid.toNat,
      arrGetU0 st'.vslot (UInt32.ofNat v) = arrGetU0 st.vslot (UInt32.ofNat v))
    (hvlt : ∀ v ∈ t.venv, v.toNat < st.nextVid.toNat)
    (hlive : ∀ v < st.nextVid.toNat,
      LiveInTask0 esc preSt st' p t' v → LiveInTask0 esc preSt st p t v) :
    SlotsAgree0 esc preSt st' p t' vT vs σ := by
  obtain ⟨hv_len, henv, hslot⟩ := hag
  refine ⟨by rw [htv]; exact hv_len, henv, fun idx hi hlv => ?_⟩
  have hi_old : idx < t.venv.length := htv ▸ hi
  have hvid_eq : t'.venv[idx]'hi = t.venv[idx]'hi_old := by
    rcases t with ⟨_, _, _, _, _, _⟩
    rcases t' with ⟨_, _, _, _, _, _⟩
    dsimp only at htv ⊢; subst htv; rfl
  have hvid_lt : (t.venv[idx]'hi_old).toNat < st.nextVid.toNat := hvlt _ (List.getElem_mem _)
  rw [hvid_eq] at hlv ⊢
  have hlv_old := hlive _ hvid_lt hlv
  obtain ⟨hsl, hvs, ht, hcanon⟩ := hslot idx hi_old hlv_old
  have hv_e := hvsl _ hvid_lt
  rw [UInt32.ofNat_toNat] at hv_e
  rw [hv_e]
  exact ⟨hsl, hvs, ht, hcanon⟩

theorem regaPrependLbl0_clean (cur : RegaTask0) (st : RegaSt0) (ctrl : CtrlSt0) :
    let p0 := regaPrependLbl0 cur { st with revDirs := [] } ctrl
    regaPrependLbl0 cur st ctrl = { p0 with revDirs := p0.revDirs ++ st.revDirs } := by
  dsimp only [regaPrependLbl0]; split <;> simp

private theorem regaPrepGroup0_clean_acc :
    ∀ (bs : List (List Ty0 × TFlat0)) (venv : List UInt32) (gp : GroupPrepOut0)
      (d : List Dir0),
      regaPrepGroup0 bs venv { gp with st := { gp.st with revDirs := gp.st.revDirs ++ d } } =
      let r := regaPrepGroup0 bs venv gp
      { r with st := { r.st with revDirs := r.st.revDirs ++ d } } := by
  intro bs
  induction bs with
  | nil => intro _ _ _; rfl
  | cons p bs ih =>
    intro venv gp d; rcases p with ⟨pts, b⟩
    have hbb : ∀ ts v (s0 : RegaSt0) f n d',
        bindBlockParams0 ts v { s0 with revDirs := s0.revDirs ++ d' } f n =
          let bb := bindBlockParams0 ts v s0 f n
          { bb with st := { bb.st with revDirs := bb.st.revDirs ++ d' } } := by
      intro ts
      induction ts with
      | nil => intro _ _ _ _ _; rfl
      | cons _ _ ihb =>
        intro v s0 f n d'
        dsimp only [bindBlockParams0, bindOneBlockSlot0]
        let s1 : RegaSt0 :=
          { s0 with
            nextVid := s0.nextVid + 1
            maxSlots := (allocSlot0 f n s0.maxSlots).maxSlots
            vslot := s0.vslot.push (allocSlot0 f n s0.maxSlots).slot.toNat }
        exact ihb (s0.nextVid :: v) s1
          (allocSlot0 f n s0.maxSlots).free (allocSlot0 f n s0.maxSlots).nxt d'
    dsimp only [regaPrepGroup0, prepOneBlock0, prepOneBind0, prepFinishBlock0, prepUpdCtrl0]
    rw [hbb]
    let bb := bindBlockParams0 pts venv gp.st gp.free gp.nxt
    let slots := slotsOfVids0 (tyLenU0 pts 0) bb.venv bb.st.vslot []
    let ctrl1 : CtrlSt0 :=
      CtrlSt0.mk gp.ctrl.fnIdx (gp.ctrl.nextLbl + 1) (gp.ctrl.lblSlots.push slots)
    let gm1 : GroupMeta0 := GroupMeta0.mk gp.ctrl.nextLbl b bb.venv
    let gp1 : GroupPrepOut0 :=
      GroupPrepOut0.mk (gp.ctrl.nextLbl :: gp.lenv) bb.st ctrl1 bb.free bb.nxt
        (gm1 :: gp.metas)
    exact ih venv gp1 d

private theorem regaEnqueueGroup0_append (lenv' free : List UInt32) (nxt : UInt32) :
    ∀ (metas : List GroupMeta0) (w₁ w₂ : List RegaTask0),
      regaEnqueueGroup0 metas lenv' free nxt (w₁ ++ w₂) =
        regaEnqueueGroup0 metas lenv' free nxt w₁ ++ w₂
  | [], _, _ => rfl
  | _ :: rest, w₁, w₂ => by
    dsimp only [regaEnqueueGroup0]
    rw [← List.cons_append]
    exact regaEnqueueGroup0_append lenv' free nxt rest _ w₂

theorem stepLinear0_clean_append (esc : Array Nat) (task : RegaTask0) (p0 : RegaSt0)
    (d : List Dir0) (ctrl : CtrlSt0) (w₁ w₂ : List RegaTask0) :
    let ls0 := stepLinear0 esc task p0 ctrl w₁
    let ls := stepLinear0 esc task { p0 with revDirs := p0.revDirs ++ d } ctrl (w₁ ++ w₂)
    ls.work = ls0.work ++ w₂ ∧ ls.ctrl = ls0.ctrl ∧
    ls.st = { ls0.st with revDirs := ls0.st.revDirs ++ d } := by
  dsimp only [stepLinear0, stepLinBindPush0, linBindPush0]
  obtain ⟨hl1, _⟩ := emitLinNode0_acc task { p0 with revDirs := p0.revDirs ++ d }
  obtain ⟨hl0, _⟩ := emitLinNode0_acc task p0
  have hl : emitLinNode0 task { p0 with revDirs := p0.revDirs ++ d } =
      emitLinNode0 task p0 ++ d := by
    rw [hl1, hl0]
    change emitLinNode0 task { p0 with revDirs := [] } ++ (p0.revDirs ++ d) =
      (emitLinNode0 task { p0 with revDirs := [] } ++ p0.revDirs) ++ d
    simp only [List.append_assoc]
  let rr := relNodeArgs0 esc p0.vslot task.venv task.node (RelRes0.mk p0.remUses task.freeSlots)
  have hbr := bindRetsN0_revDirs esc (linCnt0 task.node).toNat (linCnt0 task.node) 0
    ⟨task.venv, { p0 with remUses := rr.remUses, revDirs := emitLinNode0 task p0 },
      rr.free, task.nextSlot⟩ rfl
  have hbr_s := bindRetsN0_revDirs esc (linCnt0 task.node).toNat (linCnt0 task.node) 0
    ⟨task.venv, { p0 with remUses := rr.remUses, revDirs := emitLinNode0 task p0 ++ d },
      rr.free, task.nextSlot⟩ rfl
  dsimp only [relAndUpdateSt0] at *
  rw [hl]
  let bz := { p0 with remUses := rr.remUses, revDirs := [] }
  let stA : RegaSt0 := { p0 with remUses := rr.remUses, revDirs := emitLinNode0 task p0 ++ d }
  let stB : RegaSt0 := { p0 with remUses := rr.remUses, revDirs := emitLinNode0 task p0 }
  have hbz_eq : { stA with revDirs := [] } = bz := rfl
  have hbz_eq0 : { stB with revDirs := [] } = bz := rfl
  refine ⟨?_, rfl, ?_⟩
  · rw [← List.cons_append, hbr_s.1, hbr_s.2.1, hbr_s.2.2.1, hbz_eq, ← hbz_eq0,
      ← hbr.1, ← hbr.2.1, ← hbr.2.2.1]
  · rw [hbr_s.2.2.2.1, hbr.2.2.2.1, hbz_eq]
    dsimp only
    simp only [List.append_assoc]

theorem regaStep0_clean_append (esc : Array Nat) (cur : RegaTask0) (st : RegaSt0)
    (ctrl : CtrlSt0) (w₁ w₂ : List RegaTask0) :
    let st0 := regaPrependLbl0 cur st ctrl
    let ls := regaStep0 esc cur st0 ctrl (w₁ ++ w₂)
    let st0Clean := regaPrependLbl0 cur { st with revDirs := [] } ctrl
    let lsClean := regaStep0 esc cur st0Clean ctrl w₁
    ls.work = lsClean.work ++ w₂ ∧ ls.ctrl = lsClean.ctrl ∧
    ls.st = { lsClean.st with revDirs := lsClean.st.revDirs ++ st.revDirs } := by
  intro st0 ls st0Clean lsClean
  have hpre : st0 = { st0Clean with revDirs := st0Clean.revDirs ++ st.revDirs } :=
    regaPrependLbl0_clean cur st ctrl
  rcases cur with ⟨lbl, nd, venv, lenv, free, nextSlot⟩
  dsimp only [ls, lsClean, regaStep0] at *
  rw [hpre]
  cases nd with
  | jnz c t e =>
    dsimp only [stepJnzPush0, jnzBuildSt0, jnzWrapRes0]
    obtain ⟨hj1, _⟩ := jnzPrep0_revDirs esc c ⟨lbl, .jnz c t e, venv, lenv, free, nextSlot⟩
      { st0Clean with revDirs := st0Clean.revDirs ++ st.revDirs } ctrl
    obtain ⟨hj0, _⟩ := jnzPrep0_revDirs esc c ⟨lbl, .jnz c t e, venv, lenv, free, nextSlot⟩
      st0Clean ctrl
    have hj : (jnzPrep0 esc c ⟨lbl, .jnz c t e, venv, lenv, free, nextSlot⟩
          { st0Clean with revDirs := st0Clean.revDirs ++ st.revDirs } ctrl).2 =
        (jnzPrep0 esc c ⟨lbl, .jnz c t e, venv, lenv, free, nextSlot⟩
          st0Clean ctrl).2 ++ st.revDirs := by
      rw [hj1, hj0]
      change (jnzPrep0 esc c ⟨lbl, .jnz c t e, venv, lenv, free, nextSlot⟩
          { st0Clean with revDirs := [] } ctrl).2 ++ (st0Clean.revDirs ++ st.revDirs) = _
      simp only [List.append_assoc]
    rw [hj]
    exact ⟨rfl, rfl, rfl⟩
  | group bodies k =>
    dsimp only [stepGroupFinish0, stepGroupPrep0, groupEnqCont0]
    have hp := regaPrepGroup0_clean_acc bodies venv
      ⟨lenv, st0Clean, ctrl, free, nextSlot, []⟩ st.revDirs
    dsimp only at hp
    rw [hp, regaEnqueueGroup0_append]
    exact ⟨rfl, rfl, rfl⟩
  | let1 op args k =>
    exact stepLinear0_clean_append esc ⟨lbl, .let1 op args k, venv, lenv, free, nextSlot⟩
      st0Clean st.revDirs ctrl w₁ w₂
  | let2Umulw64 a b k =>
    exact stepLinear0_clean_append esc ⟨lbl, .let2Umulw64 a b k, venv, lenv, free, nextSlot⟩
      st0Clean st.revDirs ctrl w₁ w₂
  | load t addr k =>
    exact stepLinear0_clean_append esc ⟨lbl, .load t addr k, venv, lenv, free, nextSlot⟩
      st0Clean st.revDirs ctrl w₁ w₂
  | store t val addr k =>
    exact stepLinear0_clean_append esc ⟨lbl, .store t val addr k, venv, lenv, free, nextSlot⟩
      st0Clean st.revDirs ctrl w₁ w₂
  | call fn as bs args k =>
    exact stepLinear0_clean_append esc ⟨lbl, .call fn as bs args k, venv, lenv, free, nextSlot⟩
      st0Clean st.revDirs ctrl w₁ w₂
  | tailCall fnSym as args =>
    dsimp only [regaStepCtrl0, stepTail0]
    obtain ⟨hla1, _⟩ := loadRegArgs0_acc ⟨false, true, venv, st0Clean.vslot⟩ as args 0
      (st0Clean.revDirs ++ st.revDirs)
    obtain ⟨hla0, _⟩ := loadRegArgs0_acc ⟨false, true, venv, st0Clean.vslot⟩ as args 0
      st0Clean.revDirs
    have hla : loadRegArgs0 ⟨false, true, venv, st0Clean.vslot⟩ as args 0
          (st0Clean.revDirs ++ st.revDirs) =
        loadRegArgs0 ⟨false, true, venv, st0Clean.vslot⟩ as args 0 st0Clean.revDirs ++
          st.revDirs := by rw [hla1, hla0, List.append_assoc]
    rw [hla]; exact ⟨rfl, rfl, rfl⟩
  | exit fnSym as args =>
    dsimp only [regaStepCtrl0, stepTail0]
    obtain ⟨hla1, _⟩ := loadRegArgs0_acc ⟨false, true, venv, st0Clean.vslot⟩ as args 0
      (st0Clean.revDirs ++ st.revDirs)
    obtain ⟨hla0, _⟩ := loadRegArgs0_acc ⟨false, true, venv, st0Clean.vslot⟩ as args 0
      st0Clean.revDirs
    have hla : loadRegArgs0 ⟨false, true, venv, st0Clean.vslot⟩ as args 0
          (st0Clean.revDirs ++ st.revDirs) =
        loadRegArgs0 ⟨false, true, venv, st0Clean.vslot⟩ as args 0 st0Clean.revDirs ++
          st.revDirs := by rw [hla1, hla0, List.append_assoc]
    rw [hla]; exact ⟨rfl, rfl, rfl⟩
  | jump j args =>
    dsimp only [regaStepCtrl0]
    obtain ⟨hj1, _⟩ := emitJump0_revDirs j args ⟨lbl, .jump j args, venv, lenv, free, nextSlot⟩
      { st0Clean with revDirs := st0Clean.revDirs ++ st.revDirs } ctrl
    obtain ⟨hj0, _⟩ := emitJump0_revDirs j args ⟨lbl, .jump j args, venv, lenv, free, nextSlot⟩
      st0Clean ctrl
    have hj : emitJump0 j args ⟨lbl, .jump j args, venv, lenv, free, nextSlot⟩
          { st0Clean with revDirs := st0Clean.revDirs ++ st.revDirs } ctrl =
        { emitJump0 j args ⟨lbl, .jump j args, venv, lenv, free, nextSlot⟩ st0Clean ctrl with
          revDirs := (emitJump0 j args ⟨lbl, .jump j args, venv, lenv, free, nextSlot⟩
            st0Clean ctrl).revDirs ++ st.revDirs } := by
      rw [hj1, hj0]
      cases emitJump0 j args ⟨lbl, .jump j args, venv, lenv, free, nextSlot⟩
        { st0Clean with revDirs := [] } ctrl
      simp only [List.append_assoc]
    rw [hj]; exact ⟨rfl, rfl, rfl⟩
  | ret vs =>
    dsimp only [regaStepCtrl0, stepRet0]
    obtain ⟨hla1, _⟩ := loadRegArgs0_acc ⟨true, false, venv, st0Clean.vslot⟩ [] vs 0
      (st0Clean.revDirs ++ st.revDirs)
    obtain ⟨hla0, _⟩ := loadRegArgs0_acc ⟨true, false, venv, st0Clean.vslot⟩ [] vs 0
      st0Clean.revDirs
    have hla : loadRegArgs0 ⟨true, false, venv, st0Clean.vslot⟩ [] vs 0
          (st0Clean.revDirs ++ st.revDirs) =
        loadRegArgs0 ⟨true, false, venv, st0Clean.vslot⟩ [] vs 0 st0Clean.revDirs ++
          st.revDirs := by rw [hla1, hla0, List.append_assoc]
    rw [hla]; exact ⟨rfl, rfl, rfl⟩
  | hlt => dsimp only [regaStepCtrl0]; exact ⟨rfl, rfl, rfl⟩

theorem regaStep0_st_mono (esc : Array Nat) (cur : RegaTask0) (st : RegaSt0)
    (ctrl : CtrlSt0) (rest : List RegaTask0)
    (hvsz : st.vslot.size = st.nextVid.toNat)
    (hnv_bd : st.nextVid.toNat + binderCount0 cur.node < 2 ^ 31) :
    let ls := regaStep0 esc cur (regaPrependLbl0 cur st ctrl) ctrl rest
    st.nextVid.toNat ≤ ls.st.nextVid.toNat ∧ st.maxSlots.toNat ≤ ls.st.maxSlots.toNat ∧
    (∀ v < st.nextVid.toNat,
      arrGetU0 ls.st.vslot (UInt32.ofNat v) = arrGetU0 st.vslot (UInt32.ofNat v)) := by
  have hbr_mono : ∀ (m : Nat) (rem idx : UInt32) (bl : BindListOut0),
      rem.toNat = m → bl.st.vslot.size = bl.st.nextVid.toNat →
      bl.st.nextVid.toNat + m < 2 ^ 31 →
      let bl' := bindRetsN0 esc rem idx bl
      bl.st.nextVid.toNat ≤ bl'.st.nextVid.toNat ∧
      bl.st.maxSlots.toNat ≤ bl'.st.maxSlots.toNat ∧
      (∀ v < bl.st.nextVid.toNat,
        arrGetU0 bl'.st.vslot (UInt32.ofNat v) = arrGetU0 bl.st.vslot (UInt32.ofNat v)) := by
    intro m; induction m with
    | zero =>
      intro rem idx bl hrem _ _
      have hr0 : rem = 0 := u32_ext7 hrem
      subst hr0; rw [bindRetsN0.eq_def]; simp
    | succ k ih =>
      intro rem idx bl hrem hsz hbd
      have hpos : 0 < rem.toNat := by omega
      have hne : rem ≠ 0 := fun h => by simp [h] at hpos
      have hsub : (rem - 1).toNat = k := by rw [u32_sub1_toNat7 hpos, hrem]; omega
      let bo := bindOneSlot0 esc (abiRegAt0 true idx) bl.st bl.free bl.nxt
      let bl1 : BindListOut0 := ⟨bo.vid :: bl.venv, bo.st, bo.free, bo.nxt⟩
      have hhd : bindRetsN0 esc rem idx bl = bindRetsN0 esc (rem - 1) (idx + 1) bl1 := by
        have hd := bindRetsN0.eq_def esc rem idx bl
        simp only [hne, ↓reduceDIte] at hd; exact hd
      have h1_nv : bo.st.nextVid.toNat = bl.st.nextVid.toNat + 1 := by
        dsimp only [bo, bindOneSlot0]; split <;> exact u32_add1_toNat7 (by omega)
      have h1_ms : bl.st.maxSlots.toNat ≤ bo.st.maxSlots.toNat := by
        dsimp only [bo, bindOneSlot0]; split
        · cases bl.free <;> simp [allocSlot0, u32Max0_toNat, Nat.le_max_left]
        · exact Nat.le_refl _
      have h1_sz : bo.st.vslot.size = bo.st.nextVid.toNat := by
        rw [h1_nv]; dsimp only [bo, bindOneSlot0]; split <;> simp [Array.size_push, hsz]
      have h1_pres : ∀ v < bl.st.nextVid.toNat,
          arrGetU0 bo.st.vslot (UInt32.ofNat v) = arrGetU0 bl.st.vslot (UInt32.ofNat v) := by
        intro v hv
        have hv32 : (UInt32.ofNat v).toNat = v := by
          rw [u32_toNat_ofNat7, Nat.mod_eq_of_lt (by omega)]
        dsimp only [arrGetU0, bo, bindOneSlot0]; split
        · simp only [hv32, arrPush_getD7, hsz, hv, ↓reduceIte]
        · simp only [hv32, arrPush_getD7, hsz, hv, ↓reduceIte]
      have h2 := ih (rem - 1) (idx + 1) bl1 hsub h1_sz (by dsimp only [bl1]; omega)
      have hbo_nv : bl.st.nextVid.toNat ≤ bl1.st.nextVid.toNat := by dsimp only [bl1]; omega
      dsimp only
      rw [hhd]
      exact ⟨Nat.le_trans hbo_nv h2.1, Nat.le_trans h1_ms h2.2.1, fun v hv => by
        have hv2 := h2.2.2 v (by dsimp only [bl1]; omega)
        dsimp only [bl1] at hv2
        exact hv2.trans (h1_pres v hv)⟩
  rcases cur with ⟨lbl, nd, venv, lenv, free, nextSlot⟩
  let st0 := regaPrependLbl0 ⟨lbl, nd, venv, lenv, free, nextSlot⟩ st ctrl
  have hs0 : st0.nextVid = st.nextVid ∧ st0.maxSlots = st.maxSlots ∧ st0.vslot = st.vslot := by
    dsimp only [st0, regaPrependLbl0]; split <;> exact ⟨rfl, rfl, rfl⟩
  dsimp only [regaStep0]
  cases nd with
  | tailCall _ _ _ | exit _ _ _ | ret _ | hlt =>
    dsimp only [regaStepCtrl0, stepTail0, stepRet0]
    change st.nextVid.toNat ≤ st0.nextVid.toNat ∧ st.maxSlots.toNat ≤ st0.maxSlots.toNat ∧
      ∀ v < st.nextVid.toNat,
        arrGetU0 st0.vslot (UInt32.ofNat v) = arrGetU0 st.vslot (UInt32.ofNat v)
    rw [hs0.1, hs0.2.1, hs0.2.2]; exact ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ => rfl⟩
  | jump j args =>
    dsimp only [regaStepCtrl0, emitJump0]
    cases args with
    | nil =>
      change st.nextVid.toNat ≤ st0.nextVid.toNat ∧ st.maxSlots.toNat ≤ st0.maxSlots.toNat ∧ _
      rw [hs0.1, hs0.2.1, hs0.2.2]; exact ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ => rfl⟩
    | cons a r =>
      cases r with
      | nil =>
        dsimp only [emitJumpOne0]
        change st.nextVid.toNat ≤ st0.nextVid.toNat ∧ st.maxSlots.toNat ≤ st0.maxSlots.toNat ∧ _
        rw [hs0.1, hs0.2.1, hs0.2.2]; exact ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ => rfl⟩
      | cons b tl =>
        dsimp only [emitJumpMulti0]
        change st.nextVid.toNat ≤ st0.nextVid.toNat ∧
          st.maxSlots.toNat ≤ (u32Max0 st0.maxSlots _).toNat ∧
          ∀ v < st.nextVid.toNat,
            arrGetU0 st0.vslot (UInt32.ofNat v) = arrGetU0 st.vslot (UInt32.ofNat v)
        rw [hs0.1, hs0.2.1, hs0.2.2, u32Max0_toNat]
        exact ⟨Nat.le_refl _, Nat.le_max_left _ _, fun _ _ => rfl⟩
  | jnz _ _ _ =>
    dsimp only [stepJnzPush0, jnzBuildSt0, jnzWrapRes0]
    change st.nextVid.toNat ≤ st0.nextVid.toNat ∧ st.maxSlots.toNat ≤ st0.maxSlots.toNat ∧ _
    rw [hs0.1, hs0.2.1, hs0.2.2]; exact ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ => rfl⟩
  | group bodies k =>
    dsimp only [stepGroupFinish0, stepGroupPrep0]
    have hbd_bs : blocksBinderCount0 bodies ≤ binderCount0 (.group bodies k) := by
      dsimp only [binderCount0]; exact Nat.le_add_right _ _
    have hgp : ∀ (bs : List (List Ty0 × TFlat0)) venv' (gp : GroupPrepOut0),
        gp.st.vslot.size = gp.st.nextVid.toNat →
        gp.st.nextVid.toNat + blocksBinderCount0 bs < 2 ^ 31 →
        gp.st.nextVid.toNat ≤ (regaPrepGroup0 bs venv' gp).st.nextVid.toNat ∧
        gp.st.maxSlots.toNat ≤ (regaPrepGroup0 bs venv' gp).st.maxSlots.toNat ∧
        (∀ v < gp.st.nextVid.toNat,
          arrGetU0 (regaPrepGroup0 bs venv' gp).st.vslot (UInt32.ofNat v) =
            arrGetU0 gp.st.vslot (UInt32.ofNat v)) := by
      intro bs; induction bs with
      | nil => intro _ _ _ _; exact ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ => rfl⟩
      | cons p restB ihb =>
        intro venv' gp hgsz hgbd
        rcases p with ⟨pts, b⟩
        have hbb : ∀ ts v (s0 : RegaSt0) f n,
            s0.vslot.size = s0.nextVid.toNat → s0.nextVid.toNat + ts.length < 2 ^ 31 →
            let bb := bindBlockParams0 ts v s0 f n
            bb.st.nextVid.toNat = s0.nextVid.toNat + ts.length ∧
            bb.st.vslot.size = s0.nextVid.toNat + ts.length ∧
            s0.maxSlots.toNat ≤ bb.st.maxSlots.toNat ∧
            (∀ w < s0.nextVid.toNat,
              arrGetU0 bb.st.vslot (UInt32.ofNat w) = arrGetU0 s0.vslot (UInt32.ofNat w)) := by
          intro ts; induction ts with
          | nil => intro _ _ _ _ hs0z _; exact ⟨rfl, hs0z, Nat.le_refl _, fun _ _ => rfl⟩
          | cons _ rts iht =>
            intro v s0 f n hs0z hbd'
            simp only [List.length_cons] at hbd'
            dsimp only [bindBlockParams0, bindOneBlockSlot0]
            let sp := allocSlot0 f n s0.maxSlots
            let s1 : RegaSt0 :=
              { s0 with
                nextVid := s0.nextVid + 1
                maxSlots := sp.maxSlots
                vslot := s0.vslot.push sp.slot.toNat }
            have hs1_nv : s1.nextVid.toNat = s0.nextVid.toNat + 1 := u32_add1_toNat7 (by omega)
            have hs1_sz : s1.vslot.size = s1.nextVid.toNat := by
              rw [hs1_nv]; simp [s1, Array.size_push, hs0z]
            have hs1_ms : s0.maxSlots.toNat ≤ s1.maxSlots.toNat := by
              cases f <;> simp [s1, sp, allocSlot0, u32Max0_toNat, Nat.le_max_left]
            have ih1 := iht (s0.nextVid :: v) s1 sp.free sp.nxt hs1_sz (by rw [hs1_nv]; omega)
            dsimp only [s1, sp] at ih1
            change (bindBlockParams0 rts (s0.nextVid :: v)
                { s0 with
                  nextVid := s0.nextVid + 1
                  maxSlots := (allocSlot0 f n s0.maxSlots).maxSlots
                  vslot := s0.vslot.push (allocSlot0 f n s0.maxSlots).slot.toNat }
                (allocSlot0 f n s0.maxSlots).free
                (allocSlot0 f n s0.maxSlots).nxt).st.nextVid.toNat =
              s0.nextVid.toNat + (rts.length + 1) ∧ _
            rw [hs1_nv] at ih1
            simp only [List.length_cons]
            refine ⟨by omega, by omega, Nat.le_trans hs1_ms ih1.2.2.1, fun w hw => ?_⟩
            rw [ih1.2.2.2 w (by omega)]
            have hw32 : (UInt32.ofNat w).toNat = w := by
              rw [u32_toNat_ofNat7, Nat.mod_eq_of_lt (by omega)]
            dsimp only [arrGetU0]; simp only [hw32, arrPush_getD7, hs0z, hw, ↓reduceIte]
        have hbb1 := hbb pts venv' gp.st gp.free gp.nxt hgsz (by
          dsimp only [blocksBinderCount0] at hgbd; omega)
        dsimp only [regaPrepGroup0, prepOneBlock0, prepOneBind0, prepFinishBlock0, prepUpdCtrl0]
        let bb := bindBlockParams0 pts venv' gp.st gp.free gp.nxt
        let slots := slotsOfVids0 (tyLenU0 pts 0) bb.venv bb.st.vslot []
        let ctrl1 : CtrlSt0 :=
          CtrlSt0.mk gp.ctrl.fnIdx (gp.ctrl.nextLbl + 1) (gp.ctrl.lblSlots.push slots)
        let gm1 : GroupMeta0 := GroupMeta0.mk gp.ctrl.nextLbl b bb.venv
        let gp1 : GroupPrepOut0 :=
          GroupPrepOut0.mk (gp.ctrl.nextLbl :: gp.lenv) bb.st ctrl1 bb.free bb.nxt
            (gm1 :: gp.metas)
        have hg1 := ihb venv' gp1 (by dsimp only [gp1, bb]; rw [hbb1.2.1, hbb1.1]) (by
          dsimp only [gp1, bb]; rw [hbb1.1]
          dsimp only [blocksBinderCount0] at hgbd; omega)
        dsimp only [gp1, bb] at hg1 hbb1
        change gp.st.nextVid.toNat ≤ (regaPrepGroup0 restB venv' gp1).st.nextVid.toNat ∧
          gp.st.maxSlots.toNat ≤ (regaPrepGroup0 restB venv' gp1).st.maxSlots.toNat ∧
          ∀ v < gp.st.nextVid.toNat,
            arrGetU0 (regaPrepGroup0 restB venv' gp1).st.vslot (UInt32.ofNat v) =
              arrGetU0 gp.st.vslot (UInt32.ofNat v)
        dsimp only [gp1, bb]
        exact ⟨by omega, Nat.le_trans hbb1.2.2.1 hg1.2.1,
          fun v hv => (hg1.2.2 v (by omega)).trans (hbb1.2.2.2 v hv)⟩
    dsimp only [binderCount0] at hnv_bd
    have hgp' := hgp bodies venv ⟨lenv, st0, ctrl, free, nextSlot, []⟩
      (by rw [hs0.1, hs0.2.2]; exact hvsz) (by rw [hs0.1]; omega)
    change st.nextVid.toNat ≤
        (regaPrepGroup0 bodies venv ⟨lenv, st0, ctrl, free, nextSlot, []⟩).st.nextVid.toNat ∧
      st.maxSlots.toNat ≤
        (regaPrepGroup0 bodies venv ⟨lenv, st0, ctrl, free, nextSlot, []⟩).st.maxSlots.toNat ∧
      ∀ v < st.nextVid.toNat,
        arrGetU0 (regaPrepGroup0 bodies venv
          ⟨lenv, st0, ctrl, free, nextSlot, []⟩).st.vslot (UInt32.ofNat v) =
          arrGetU0 st.vslot (UInt32.ofNat v)
    rw [← hs0.1, ← hs0.2.1, ← hs0.2.2]
    exact hgp'
  | let1 op args k =>
    dsimp only [stepLinear0, stepLinBindPush0, linBindPush0, linCnt0]
    dsimp only [binderCount0] at hnv_bd
    let task := RegaTask0.mk lbl (.let1 op args k) venv lenv free nextSlot
    let bl0 := relAndUpdateSt0 esc task st0 (emitLinNode0 task st0)
    have hres := hbr_mono 1 1 0 bl0 rfl
      (by dsimp only [bl0, relAndUpdateSt0]; rw [hs0.1, hs0.2.2]; exact hvsz)
      (by dsimp only [bl0, relAndUpdateSt0]; rw [hs0.1]; omega)
    refine ⟨Nat.le_trans (by
          dsimp only [bl0, relAndUpdateSt0]
          exact Nat.le_of_eq (congrArg UInt32.toNat hs0.1.symm)) hres.1,
      Nat.le_trans (by
          dsimp only [bl0, relAndUpdateSt0]
          exact Nat.le_of_eq (congrArg UInt32.toNat hs0.2.1.symm)) hres.2.1,
      fun v hv => (hres.2.2 v (by
          dsimp only [bl0, relAndUpdateSt0]
          exact (congrArg UInt32.toNat hs0.1).symm ▸ hv)).trans
        (by
          dsimp only [bl0, relAndUpdateSt0]
          exact congrArg (fun a => arrGetU0 a (UInt32.ofNat v)) hs0.2.2)⟩
  | let2Umulw64 a b k =>
    dsimp only [stepLinear0, stepLinBindPush0, linBindPush0, linCnt0]
    dsimp only [binderCount0] at hnv_bd
    let task := RegaTask0.mk lbl (.let2Umulw64 a b k) venv lenv free nextSlot
    let bl0 := relAndUpdateSt0 esc task st0 (emitLinNode0 task st0)
    have hres := hbr_mono 2 2 0 bl0 rfl
      (by dsimp only [bl0, relAndUpdateSt0]; rw [hs0.1, hs0.2.2]; exact hvsz)
      (by dsimp only [bl0, relAndUpdateSt0]; rw [hs0.1]; omega)
    refine ⟨Nat.le_trans (by
          dsimp only [bl0, relAndUpdateSt0]
          exact Nat.le_of_eq (congrArg UInt32.toNat hs0.1.symm)) hres.1,
      Nat.le_trans (by
          dsimp only [bl0, relAndUpdateSt0]
          exact Nat.le_of_eq (congrArg UInt32.toNat hs0.2.1.symm)) hres.2.1,
      fun v hv => (hres.2.2 v (by
          dsimp only [bl0, relAndUpdateSt0]
          exact (congrArg UInt32.toNat hs0.1).symm ▸ hv)).trans
        (by
          dsimp only [bl0, relAndUpdateSt0]
          exact congrArg (fun a => arrGetU0 a (UInt32.ofNat v)) hs0.2.2)⟩
  | load t addr k =>
    dsimp only [stepLinear0, stepLinBindPush0, linBindPush0, linCnt0]
    dsimp only [binderCount0] at hnv_bd
    let task := RegaTask0.mk lbl (.load t addr k) venv lenv free nextSlot
    let bl0 := relAndUpdateSt0 esc task st0 (emitLinNode0 task st0)
    have hres := hbr_mono 1 1 0 bl0 rfl
      (by dsimp only [bl0, relAndUpdateSt0]; rw [hs0.1, hs0.2.2]; exact hvsz)
      (by dsimp only [bl0, relAndUpdateSt0]; rw [hs0.1]; omega)
    refine ⟨Nat.le_trans (by
          dsimp only [bl0, relAndUpdateSt0]
          exact Nat.le_of_eq (congrArg UInt32.toNat hs0.1.symm)) hres.1,
      Nat.le_trans (by
          dsimp only [bl0, relAndUpdateSt0]
          exact Nat.le_of_eq (congrArg UInt32.toNat hs0.2.1.symm)) hres.2.1,
      fun v hv => (hres.2.2 v (by
          dsimp only [bl0, relAndUpdateSt0]
          exact (congrArg UInt32.toNat hs0.1).symm ▸ hv)).trans
        (by
          dsimp only [bl0, relAndUpdateSt0]
          exact congrArg (fun a => arrGetU0 a (UInt32.ofNat v)) hs0.2.2)⟩
  | store t val addr k =>
    dsimp only [stepLinear0, stepLinBindPush0, linBindPush0, linCnt0]
    dsimp only [binderCount0] at hnv_bd
    let task := RegaTask0.mk lbl (.store t val addr k) venv lenv free nextSlot
    let bl0 := relAndUpdateSt0 esc task st0 (emitLinNode0 task st0)
    have hres := hbr_mono 0 0 0 bl0 rfl
      (by dsimp only [bl0, relAndUpdateSt0]; rw [hs0.1, hs0.2.2]; exact hvsz)
      (by dsimp only [bl0, relAndUpdateSt0]; rw [hs0.1]; omega)
    refine ⟨Nat.le_trans (by
          dsimp only [bl0, relAndUpdateSt0]
          exact Nat.le_of_eq (congrArg UInt32.toNat hs0.1.symm)) hres.1,
      Nat.le_trans (by
          dsimp only [bl0, relAndUpdateSt0]
          exact Nat.le_of_eq (congrArg UInt32.toNat hs0.2.1.symm)) hres.2.1,
      fun v hv => (hres.2.2 v (by
          dsimp only [bl0, relAndUpdateSt0]
          exact (congrArg UInt32.toNat hs0.1).symm ▸ hv)).trans
        (by
          dsimp only [bl0, relAndUpdateSt0]
          exact congrArg (fun a => arrGetU0 a (UInt32.ofNat v)) hs0.2.2)⟩
  | call fn as bs args k =>
    dsimp only [stepLinear0, stepLinBindPush0, linBindPush0, linCnt0]
    dsimp only [binderCount0] at hnv_bd
    have hlt32 : bs.length < 2 ^ 32 := by omega
    let task := RegaTask0.mk lbl (.call fn as bs args k) venv lenv free nextSlot
    let bl0 := relAndUpdateSt0 esc task st0 (emitLinNode0 task st0)
    have hres := hbr_mono (tyLenU0 bs 0).toNat (tyLenU0 bs 0) 0 bl0 rfl
      (by dsimp only [bl0, relAndUpdateSt0]; rw [hs0.1, hs0.2.2]; exact hvsz)
      (by
        dsimp only [bl0, relAndUpdateSt0]
        rw [hs0.1, tyLenU0_eq_of_lt hlt32]; omega)
    refine ⟨Nat.le_trans (by
          dsimp only [bl0, relAndUpdateSt0]
          exact Nat.le_of_eq (congrArg UInt32.toNat hs0.1.symm)) hres.1,
      Nat.le_trans (by
          dsimp only [bl0, relAndUpdateSt0]
          exact Nat.le_of_eq (congrArg UInt32.toNat hs0.2.1.symm)) hres.2.1,
      fun v hv => (hres.2.2 v (by
          dsimp only [bl0, relAndUpdateSt0]
          exact (congrArg UInt32.toNat hs0.1).symm ▸ hv)).trans
        (by
          dsimp only [bl0, relAndUpdateSt0]
          exact congrArg (fun a => arrGetU0 a (UInt32.ofNat v)) hs0.2.2)⟩

end LeanQbe.T.Bootstrap0
