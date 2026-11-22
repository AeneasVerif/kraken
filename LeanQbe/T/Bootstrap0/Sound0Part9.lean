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
# Bootstrap Stage B (`Sound0Part9`): Machine-Level `Rega0` Worklist Soundness & `compileFn0_fnSpec`

Proves end-to-end semantic soundness (`x64ScalarTarget.FnSpec`) for every compiled function
`compileFn0 fnIdx fn` satisfying `WfNode0` and `fn.okGuardsFull = true`:
1. Pure environment, canonical 64-bit word, `ArgsSlotVal64`, `ArgsIn`/`RetsIn`, and
   `pushFreshVids0` drop/prefix helpers (`EnvTypesOk0`, `HoldsCanon640`, `tupAbiHolds0`).
2. Frame/stack-slot invariants (`FnFrameInv0`, `SlotsAgree0`, `TupInSlots0`, `GlEntrySem0`,
   `NodeContracts0`), worklist slicing (`regaRunAux0_step_prefix`), and binder run specs.
3. Modular instruction/terminator runners (`emitJump0_run_ok`, `stepRet0_run_ok`,
   `stepTail0_run_ok`, `call_run_ok`, `let1_run_ok`, `umulw_run_ok`, `load_run_ok`,
   `store_run_ok`, `jnz_run_ok`, `group_run_ok`).
4. Inductive soundness `regaTask0_run_ok` and per-function headline `compileFn0_fnSpec`.
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

private theorem u32_add_ofNat_succ9 (a : UInt32) (k : Nat) :
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

private theorem pushTup_drop_aux :
    ∀ {tys : List Ty} (xs : Tup Val tys) (vs : List ((t : Ty) × Val t)),
      (pushTup xs vs).drop tys.length = vs
  | [], xs, vs => by cases xs; rfl
  | t :: tys, xs, vs => by
    rcases xs with ⟨x, rest⟩
    dsimp only [pushTup, List.length_cons]
    have h := pushTup_drop_aux rest (⟨t, x⟩ :: vs)
    rw [← List.drop_drop, h, List.drop_one, List.tail_cons]

private theorem pushTup_drop {ts : List Ty0} (xs : Tup Val (ty0ListToTy ts))
    (vs : List ((t : Ty) × Val t)) :
    (pushTup xs vs).drop ts.length = vs := by
  have h : (ty0ListToTy ts).length = ts.length := List.length_map ..
  exact h ▸ pushTup_drop_aux xs vs

private theorem list_drop_drop9 {α : Type} (xs : List α) (a b : Nat) :
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

private theorem tupToCanon64s_cons_getElem {t : Ty0} {ts : List Ty0}
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

theorem regaStep0_prefix_split {ctx : LegalCtx0} {fnIdx : UInt32} {fnMaxJump : Nat}
    {preRes : PreSt0} {nextSc : UInt32} {preSt : PreSt0} {curPre : PreItem0}
    {restPre₁ restPre₂ : List PreItem0} {seenJnz : Bool} {st : RegaSt0} {ctrl : CtrlSt0}
    {cur : RegaTask0} {rest₁ w₂ : List RegaTask0} {mCur : TaskMeta0} {restM₁ m₂ : List TaskMeta0}
    (h : RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc preSt (curPre :: (restPre₁ ++ restPre₂))
      seenJnz st ctrl (cur :: (rest₁ ++ w₂)) (mCur :: (restM₁ ++ m₂)))
    (hlpw : restPre₁.length = rest₁.length) (hlmw : restM₁.length = rest₁.length) :
    let st0 := regaPrependLbl0 cur st ctrl
    let ls := regaStep0 preRes.escaped cur st0 ctrl (rest₁ ++ w₂)
    let st0Clean := regaPrependLbl0 cur { st with revDirs := [] } ctrl
    let lsClean := regaStep0 preRes.escaped cur st0Clean ctrl rest₁
    let preSt1 := preNoteNode0 curPre.scope curPre.venv curPre.node preSt
    let out := preStepPush0 curPre preSt1 nextSc (restPre₁ ++ restPre₂)
    ∃ (seenJnz' : Bool) (pw₁' : List PreItem0) (m₁' : List TaskMeta0),
      pw₁'.length = lsClean.work.length ∧ m₁'.length = lsClean.work.length ∧
      out.work = pw₁' ++ restPre₂ ∧
      RegaStepInv0 ctx fnIdx fnMaxJump preRes out.nextScope out.st out.work seenJnz'
        ls.st ls.ctrl ls.work (m₁' ++ m₂) := by
  intro st0 ls st0Clean lsClean preSt1 out
  obtain ⟨seenJnz', headMeta, hinv'⟩ := regaStep0_lockstep_head
    (by simpa only [List.cons_append] using h)
  have hcur_ok := h.items_ok 0 (by simp) (by simp) (by simp)
  dsimp only [List.getElem_cons_zero] at hcur_ok
  obtain ⟨hpn, _, _, _, _, _, _, _, _, hsbg, _⟩ := hcur_ok
  have hcl := regaStep0_clean_append preRes.escaped cur st ctrl rest₁ w₂
  dsimp only at hcl
  have hl_m2 : m₂.length = w₂.length := by
    have hmw := h.len_mw
    simp only [List.length_cons, List.length_append] at hmw
    omega
  have hl_hm : (headMeta ++ restM₁).length = lsClean.work.length := by
    have h1 := hinv'.len_mw
    have h2 := congrArg List.length hcl.1
    dsimp only [lsClean, st0Clean] at h2 ⊢
    simp only [List.length_append] at h1 h2 ⊢
    omega
  have hpw_split : ∃ pw₁', pw₁'.length = lsClean.work.length ∧ out.work = pw₁' ++ restPre₂ := by
    have hpre_split : ∀ bodies k, curPre.node = .group bodies k →
        bodies = [] ∨ ∃ pts b, bodies = [(pts, b)] := fun bodies k he => by
      rw [← hpn, he] at hsbg
      dsimp only [TFlat0.singleBlockGroups] at hsbg
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hsbg
      cases bodies with
      | nil => exact Or.inl rfl
      | cons p bs => cases bs with
        | nil => exact Or.inr ⟨p.1, p.2, rfl⟩
        | cons _ _ => simp at hsbg
    rcases hnd : cur.node with
      op | a | t | t | fnSym | fnSym | c | j | vs | fnSym | _ | bodies
    · exact ⟨PreItem0.mk (linK0 curPre.node)
          (preBindLoop0 (linCnt0 curPre.node) curPre.scope curPre.venv preSt1).1 curPre.scope ::
          restPre₁,
        by simp [lsClean, regaStep0, stepLinear0, stepLinBindPush0, linBindPush0, hnd, hlpw],
        by dsimp only [out, preStepPush0]
           simp [isTerm0, preStepLin0, preLinFinish0, hpn, hnd, List.cons_append]⟩
    · exact ⟨PreItem0.mk (linK0 curPre.node)
          (preBindLoop0 (linCnt0 curPre.node) curPre.scope curPre.venv preSt1).1 curPre.scope ::
          restPre₁,
        by simp [lsClean, regaStep0, stepLinear0, stepLinBindPush0, linBindPush0, hnd, hlpw],
        by dsimp only [out, preStepPush0]
           simp [isTerm0, preStepLin0, preLinFinish0, hpn, hnd, List.cons_append]⟩
    · exact ⟨PreItem0.mk (linK0 curPre.node)
          (preBindLoop0 (linCnt0 curPre.node) curPre.scope curPre.venv preSt1).1 curPre.scope ::
          restPre₁,
        by simp [lsClean, regaStep0, stepLinear0, stepLinBindPush0, linBindPush0, hnd, hlpw],
        by dsimp only [out, preStepPush0]
           simp [isTerm0, preStepLin0, preLinFinish0, hpn, hnd, List.cons_append]⟩
    · exact ⟨PreItem0.mk (linK0 curPre.node)
          (preBindLoop0 (linCnt0 curPre.node) curPre.scope curPre.venv preSt1).1 curPre.scope ::
          restPre₁,
        by simp [lsClean, regaStep0, stepLinear0, stepLinBindPush0, linBindPush0, hnd, hlpw],
        by dsimp only [out, preStepPush0]
           simp [isTerm0, preStepLin0, preLinFinish0, hpn, hnd, List.cons_append]⟩
    · exact ⟨PreItem0.mk (linK0 curPre.node)
          (preBindLoop0 (linCnt0 curPre.node) curPre.scope curPre.venv preSt1).1 curPre.scope ::
          restPre₁,
        by simp [lsClean, regaStep0, stepLinear0, stepLinBindPush0, linBindPush0, hnd, hlpw],
        by dsimp only [out, preStepPush0]
           simp [isTerm0, preStepLin0, preLinFinish0, hpn, hnd, List.cons_append]⟩
    · exact ⟨restPre₁, by simp [lsClean, regaStep0, regaStepCtrl0, hnd, hlpw],
        by dsimp only [out, preStepPush0]; simp [isTerm0, hpn, hnd]⟩
    · rename_i t e
      exact ⟨PreItem0.mk e curPre.venv (nextSc + 1) :: PreItem0.mk t curPre.venv nextSc ::
          restPre₁,
        by simp [lsClean, regaStep0, stepJnzPush0, hnd, hlpw],
        by dsimp only [out, preStepPush0]
           simp [isTerm0, preStepJnz0, hpn, hnd, List.cons_append]⟩
    · exact ⟨restPre₁, by simp [lsClean, regaStep0, regaStepCtrl0, hnd, hlpw],
        by dsimp only [out, preStepPush0]; simp [isTerm0, hpn, hnd]⟩
    · exact ⟨restPre₁, by simp [lsClean, regaStep0, regaStepCtrl0, hnd, hlpw],
        by dsimp only [out, preStepPush0]; simp [isTerm0, hpn, hnd]⟩
    · exact ⟨restPre₁, by simp [lsClean, regaStep0, regaStepCtrl0, hnd, hlpw],
        by dsimp only [out, preStepPush0]; simp [isTerm0, hpn, hnd]⟩
    · exact ⟨restPre₁, by simp [lsClean, regaStep0, regaStepCtrl0, hnd, hlpw],
        by dsimp only [out, preStepPush0]; simp [isTerm0, hpn, hnd]⟩
    · rename_i k
      rcases hpre_split bodies k (hpn.trans hnd) with rfl | ⟨pts, b, rfl⟩
      · exact ⟨PreItem0.mk k curPre.venv nextSc :: restPre₁, by
            dsimp only [lsClean, regaStep0]; rw [hnd]
            dsimp only [stepGroupFinish0, stepGroupPrep0, regaPrepGroup0,
              groupEnqCont0, regaEnqueueGroup0]
            simp only [List.length_cons, hlpw],
          by dsimp only [out, preStepPush0]; rw [hpn, hnd]
             simp only [isTerm0, Bool.false_eq_true, ↓reduceIte]
             dsimp only [preStepGroup0, prePushGroup0, preEnqueueGroup0]
             rw [List.cons_append]⟩
      · exact ⟨PreItem0.mk k curPre.venv (nextSc + 1) ::
            PreItem0.mk b (preBindLoop0 (tyLenU0 pts 0) nextSc curPre.venv preSt1).1
              nextSc :: restPre₁,
          by dsimp only [lsClean, regaStep0]; rw [hnd]
             dsimp only [stepGroupFinish0, stepGroupPrep0, regaPrepGroup0,
               prepOneBlock0, prepOneBind0, prepFinishBlock0, prepUpdCtrl0,
               groupEnqCont0, regaEnqueueGroup0]
             simp only [List.length_cons, hlpw],
          by dsimp only [out, preStepPush0]; rw [hpn, hnd]
             simp only [isTerm0, Bool.false_eq_true, ↓reduceIte]
             dsimp only [preStepGroup0, prePushGroup0, prePushOne0, preEnqueueGroup0]
             rw [List.cons_append, List.cons_append]⟩
  obtain ⟨pw₁', hlpw', hout_eq⟩ := hpw_split
  exact ⟨seenJnz', pw₁', headMeta ++ restM₁, hlpw', hl_hm, hout_eq, by
    simpa only [List.append_assoc] using hinv'⟩

/-- Worklist monotonicity & prefix splitting for `regaRunAux0` along `RegaStepInv0`. -/
theorem regaRunAux0_step_prefix :
    ∀ (N : Nat) (fuel : UInt32) (ctx : LegalCtx0) (fnIdx : UInt32) (fnMaxJump : Nat)
      (preRes : PreSt0) (nextSc : UInt32) (preSt : PreSt0) (preWork₁ preWork₂ : List PreItem0)
      (seenJnz : Bool) (st : RegaSt0) (ctrl : CtrlSt0) (w₁ w₂ : List RegaTask0)
      (m₁ m₂ : List TaskMeta0),
      workNodeCount0 (w₁.map RegaTask0.node) = N → N ≤ fuel.toNat →
      preWork₁.length = w₁.length → m₁.length = w₁.length →
      RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc preSt (preWork₁ ++ preWork₂) seenJnz st ctrl
        (w₁ ++ w₂) (m₁ ++ m₂) →
      let r1 := regaRunAux0 (UInt32.ofNat N) preRes.escaped { st with revDirs := [] } ctrl w₁
      let rFull := regaRunAux0 fuel preRes.escaped st ctrl (w₁ ++ w₂)
      rFull = regaRunAux0 (UInt32.ofNat (fuel.toNat - N)) preRes.escaped
        { r1.1 with revDirs := r1.1.revDirs ++ st.revDirs } r1.2 w₂ ∧
      st.nextVid.toNat ≤ r1.1.nextVid.toNat ∧
      r1.1.maxSlots.toNat ≤ (regaRunAux0 fuel preRes.escaped st ctrl (w₁ ++ w₂)).1.maxSlots.toNat ∧
      st.maxSlots.toNat ≤ r1.1.maxSlots.toNat ∧
      (∀ v < st.nextVid.toNat,
        arrGetU0 r1.1.vslot (UInt32.ofNat v) = arrGetU0 st.vslot (UInt32.ofNat v)) ∧
      ∃ seenJnz' nextSc' preSt',
        RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc' preSt' preWork₂ seenJnz'
          { r1.1 with revDirs := r1.1.revDirs ++ st.revDirs } r1.2 w₂ m₂ := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro fuel ctx fnIdx fnMaxJump preRes nextSc preSt pw₁ pw₂ seenJnz st ctrl w₁ w₂ m₁ m₂
      hN hle hlen_pw hlen_mw hinv
    cases w₁ with
    | nil =>
      subst hN
      have hpw_nil : pw₁ = [] := List.eq_nil_of_length_eq_zero hlen_pw
      have hm_nil : m₁ = [] := List.eq_nil_of_length_eq_zero hlen_mw
      subst hpw_nil; subst hm_nil
      rw [List.nil_append] at hinv
      rw [show workNodeCount0 (List.map RegaTask0.node []) = 0 from rfl,
        Nat.sub_zero, List.nil_append, UInt32.ofNat_toNat]
      rw [show regaRunAux0 (UInt32.ofNat 0) preRes.escaped { st with revDirs := [] } ctrl [] =
          ({ st with revDirs := [] }, ctrl) from regaRunAux0_nil _ _ _ _]
      simp only [List.nil_append]
      have hst_id : ({ st with revDirs := st.revDirs } : RegaSt0) = st := by cases st; rfl
      rw [hst_id]
      refine ⟨trivial, Nat.le_refl _, ?_, Nat.le_refl _, fun _ _ => trivial,
        seenJnz, nextSc, preSt, hinv⟩
      have aux_ms : ∀ (M : Nat) (fl : UInt32) (esc : Array Nat) (s0 : RegaSt0) (c0 : CtrlSt0)
          (wk : List RegaTask0),
          fl.toNat = M → s0.maxSlots.toNat ≤ (regaRunAux0 fl esc s0 c0 wk).1.maxSlots.toNat := by
        intro M
        induction M using Nat.strongRecOn with
        | ind M ihM =>
          intro fl esc s0 c0 wk hfl
          by_cases hfl0 : fl = 0
          · rw [hfl0, regaRunAux0_zero]; exact Nat.le_refl _
          · cases wk with
            | nil => rw [regaRunAux0_nil]; exact Nat.le_refl _
            | cons hd tl =>
              rw [regaRunAux0_succ hfl0]
              have hltM : (fl - 1).toNat < M := hfl ▸ u32Sub1Lt0 fl hfl0
              have ih1 := ihM (fl - 1).toNat hltM (fl - 1) esc
                (regaStep0 esc hd (regaPrependLbl0 hd s0 c0) c0 tl).st
                (regaStep0 esc hd (regaPrependLbl0 hd s0 c0) c0 tl).ctrl
                (regaStep0 esc hd (regaPrependLbl0 hd s0 c0) c0 tl).work rfl
              have hstep_ms : s0.maxSlots.toNat ≤
                  (regaStep0 esc hd (regaPrependLbl0 hd s0 c0) c0 tl).st.maxSlots.toNat := by
                have hs0_bd : (regaPrependLbl0 hd s0 c0).maxSlots = s0.maxSlots := by
                  dsimp only [regaPrependLbl0]; split <;> rfl
                rcases hd with ⟨lbl, nd, venv, lenv, fr, nxt⟩
                cases nd with
                | tailCall _ _ _ | exit _ _ _ | ret _ | hlt =>
                  dsimp only [regaStep0, regaStepCtrl0, stepTail0, stepRet0]; rw [hs0_bd]
                  exact Nat.le_refl _
                | jump j args =>
                  dsimp only [regaStep0, regaStepCtrl0, emitJump0]
                  cases args with
                  | nil => rw [hs0_bd]; exact Nat.le_refl _
                  | cons _ r => cases r with
                    | nil => dsimp only [emitJumpOne0]; rw [hs0_bd]; exact Nat.le_refl _
                    | cons _ _ =>
                      dsimp only [emitJumpMulti0]; rw [u32Max0_toNat, hs0_bd]
                      exact Nat.le_max_left _ _
                | jnz _ _ _ =>
                  dsimp only [regaStep0, stepJnzPush0, jnzBuildSt0, jnzWrapRes0]
                  rw [hs0_bd]; exact Nat.le_refl _
                | group bs k' =>
                  dsimp only [regaStep0, stepGroupFinish0, groupEnqCont0, stepGroupPrep0]
                  have hgp_ms : ∀ bs' venv' gp',
                      gp'.st.maxSlots.toNat ≤ (regaPrepGroup0 bs' venv' gp').st.maxSlots.toNat := by
                    intro bs'; induction bs' with
                    | nil => intro _ _; exact Nat.le_refl _
                    | cons p restB ihg =>
                      intro venv' gp'; rcases p with ⟨pts, b⟩
                      dsimp only [regaPrepGroup0, prepOneBlock0, prepOneBind0, prepFinishBlock0,
                        prepUpdCtrl0]
                      let bb := bindBlockParams0 pts venv' gp'.st gp'.free gp'.nxt
                      let gp1 : GroupPrepOut0 :=
                        ⟨gp'.ctrl.nextLbl :: gp'.lenv, bb.st,
                         ⟨gp'.ctrl.fnIdx, gp'.ctrl.nextLbl + 1,
                          gp'.ctrl.lblSlots.push
                            (slotsOfVids0 (tyLenU0 pts 0) bb.venv bb.st.vslot [])⟩,
                         bb.free, bb.nxt, ⟨gp'.ctrl.nextLbl, b, bb.venv⟩ :: gp'.metas⟩
                      exact Nat.le_trans
                        (bindBlockParams0_maxSlots_le pts venv' gp'.st gp'.free gp'.nxt)
                        (ihg venv' gp1)
                  have hms := hgp_ms bs venv ⟨lenv, regaPrependLbl0
                    { lblId := lbl, node := .group bs k', venv := venv, lenv := lenv,
                      freeSlots := fr, nextSlot := nxt } s0 c0, c0, fr, nxt, []⟩
                  dsimp only at hms
                  rwa [hs0_bd] at hms
                | let1 _ _ _ | let2Umulw64 _ _ _ | load _ _ _ | store _ _ _ _ | call _ _ _ _ _ =>
                  have lin_ms : ∀ (t0 : RegaTask0) (s1 : RegaSt0),
                      s1.maxSlots.toNat ≤ (stepLinear0 esc t0 s1 c0 tl).st.maxSlots.toNat :=
                    fun t0 s1 => bindRetsN0_maxSlots_le esc (linCnt0 t0.node).toNat
                      (linCnt0 t0.node) 0 (relAndUpdateSt0 esc t0 s1 (emitLinNode0 t0 s1)) rfl
                  dsimp only [regaStep0]
                  exact hs0_bd ▸ lin_ms _ _
              exact Nat.le_trans hstep_ms ih1
      exact aux_ms fuel.toNat fuel preRes.escaped { st with revDirs := st.revDirs } ctrl w₂ rfl
    | cons cur rest₁ =>
      cases pw₁ with
      | nil => simp at hlen_pw
      | cons curPre restPre₁ =>
        cases m₁ with
        | nil => simp at hlen_mw
        | cons mCur restM₁ =>
          have hpos : 0 < N := by
            rw [← hN, List.map_cons]; dsimp only [workNodeCount0]
            have := nodeCount0_pos cur.node; omega
          have hN_lt32 : N < 2 ^ 32 := by
            have htot := hinv.ctrl_nl.2
            rw [List.cons_append] at htot
            have hN_le : N ≤ workNodeCount0 ((cur :: (rest₁ ++ w₂)).map RegaTask0.node) := by
              rw [← hN, List.map_cons, List.map_cons, List.map_append]
              dsimp only [workNodeCount0]
              rw [workNodeCount0_append]
              omega
            omega
          have hf_ne : fuel ≠ 0 := fun h => by
            have := congrArg UInt32.toNat h; rw [UInt32.toNat_zero] at this; omega
          have hN_ne : UInt32.ofNat N ≠ 0 := fun h => by
            have := congrArg UInt32.toNat h
            rw [u32_ofNat_toNat_lt9 hN_lt32, UInt32.toNat_zero] at this
            omega
          have hN1 : (UInt32.ofNat N - 1).toNat = N - 1 := by
            rw [u32_sub1_toNat7 (by rw [u32_ofNat_toNat_lt9 hN_lt32]; exact hpos),
              u32_ofNat_toNat_lt9 hN_lt32]
          have hfl1 : (fuel - 1).toNat = fuel.toNat - 1 := u32_sub1_toNat7 (by omega)
          let st0 := regaPrependLbl0 cur st ctrl
          let ls := regaStep0 preRes.escaped cur st0 ctrl (rest₁ ++ w₂)
          let st0Clean := regaPrependLbl0 cur { st with revDirs := [] } ctrl
          let lsClean := regaStep0 preRes.escaped cur st0Clean ctrl rest₁
          have hcl := regaStep0_clean_append preRes.escaped cur st ctrl rest₁ w₂
          dsimp only at hcl
          have hsplit_clean :
              regaRunAux0 (UInt32.ofNat N) preRes.escaped { st with revDirs := [] } ctrl
                (cur :: rest₁) =
              regaRunAux0 (UInt32.ofNat N - 1) preRes.escaped lsClean.st lsClean.ctrl
                lsClean.work :=
            regaRunAux0_succ hN_ne preRes.escaped { st with revDirs := [] } ctrl cur rest₁
          have hsplit_full1 :
              regaRunAux0 fuel preRes.escaped st ctrl (cur :: (rest₁ ++ w₂)) =
              regaRunAux0 (fuel - 1) preRes.escaped ls.st ls.ctrl ls.work :=
            regaRunAux0_succ hf_ne preRes.escaped st ctrl cur (rest₁ ++ w₂)
          have hcnt_clean : workNodeCount0 (lsClean.work.map RegaTask0.node) + 1 = N := by
            rw [← hN]
            simpa only [lsClean, List.map_cons] using
              regaWorkNodeCount0_children preRes.escaped cur st0Clean ctrl rest₁
          have hlt_clean : workNodeCount0 (lsClean.work.map RegaTask0.node) < N := by omega
          have hcnt_sub : UInt32.ofNat N - 1 =
              UInt32.ofNat (workNodeCount0 (lsClean.work.map RegaTask0.node)) := by
            apply u32_ext7; rw [hN1, u32_ofNat_toNat_lt9 (by omega)]; omega
          have hcur_ok := hinv.items_ok 0 (by simp) (by simp) (by simp)
          simp only [List.cons_append, List.getElem_cons_zero] at hcur_ok
          have hnv_bd : st.nextVid.toNat + binderCount0 cur.node < 2 ^ 31 := by
            have hb := hinv.pre_inv.nextVid_bound
            rw [List.cons_append, List.map_cons] at hb
            dsimp only [workBinderCount0] at hb
            rw [hcur_ok.1] at hb
            rw [← hinv.st_nv] at hb; omega
          have hmono1 := regaStep0_st_mono preRes.escaped cur { st with revDirs := [] } ctrl rest₁
            hinv.st_vslot_sz hnv_bd
          dsimp only at hmono1
          obtain ⟨seenJnz1, pw₁', m₁', hlen_pw', hlen_mw', hout_eq, hinv1⟩ :=
            regaStep0_prefix_split hinv (by simp at hlen_pw; exact hlen_pw)
              (by simp at hlen_mw; exact hlen_mw)
          rw [hcl.1, hcl.2.1, hout_eq] at hinv1
          have hih := ih (workNodeCount0 (lsClean.work.map RegaTask0.node)) hlt_clean (fuel - 1)
            ctx fnIdx fnMaxJump preRes _ _ pw₁' pw₂ seenJnz1 ls.st lsClean.ctrl lsClean.work w₂
            m₁' m₂ rfl (by rw [hfl1]; omega) hlen_pw' hlen_mw' hinv1
          dsimp only at hih
          have hz_clean : { ls.st with revDirs := [] } = { lsClean.st with revDirs := [] } := by
            rw [hcl.2.2]
          let r1' := regaRunAux0 (UInt32.ofNat (workNodeCount0 (lsClean.work.map RegaTask0.node)))
            preRes.escaped { lsClean.st with revDirs := [] } lsClean.ctrl lsClean.work
          have hrev_ls :
              regaRunAux0 (UInt32.ofNat (workNodeCount0 (lsClean.work.map RegaTask0.node)))
                preRes.escaped lsClean.st lsClean.ctrl lsClean.work =
              ({ r1'.1 with revDirs := r1'.1.revDirs ++ lsClean.st.revDirs }, r1'.2) :=
            regaRunAux0_revDirs_append
              (UInt32.ofNat (workNodeCount0 (lsClean.work.map RegaTask0.node)))
              preRes.escaped lsClean.st lsClean.ctrl lsClean.work
          have hr1_eq : regaRunAux0 (UInt32.ofNat N) preRes.escaped { st with revDirs := [] }
              ctrl (cur :: rest₁) =
              ({ r1'.1 with revDirs := r1'.1.revDirs ++ lsClean.st.revDirs }, r1'.2) := by
            rw [hsplit_clean, hcnt_sub, hrev_ls]
          have hfull_eq : regaRunAux0 fuel preRes.escaped st ctrl ((cur :: rest₁) ++ w₂) =
              regaRunAux0 (fuel - 1) preRes.escaped ls.st lsClean.ctrl (lsClean.work ++ w₂) := by
            rw [List.cons_append, hsplit_full1, hcl.1, hcl.2.1]
          have hcomb_rev :
              ({ r1'.1 with revDirs := r1'.1.revDirs ++ ls.st.revDirs }, r1'.2) =
              ({ (regaRunAux0 (UInt32.ofNat N) preRes.escaped { st with revDirs := [] } ctrl
                  (cur :: rest₁)).1 with
                revDirs :=
                  (regaRunAux0 (UInt32.ofNat N) preRes.escaped { st with revDirs := [] } ctrl
                    (cur :: rest₁)).1.revDirs ++ st.revDirs },
               (regaRunAux0 (UInt32.ofNat N) preRes.escaped { st with revDirs := [] } ctrl
                  (cur :: rest₁)).2) := by
            rw [hr1_eq, hcl.2.2]
            dsimp only [lsClean, st0Clean]
            simp only [List.append_assoc]
          have hcomb_st := congrArg Prod.fst hcomb_rev
          have hcomb_ctrl := congrArg Prod.snd hcomb_rev
          dsimp only at hcomb_st hcomb_ctrl
          have hih' :
              regaRunAux0 (fuel - 1) preRes.escaped ls.st lsClean.ctrl (lsClean.work ++ w₂) =
                regaRunAux0 (UInt32.ofNat ((fuel - 1).toNat -
                  workNodeCount0 (lsClean.work.map RegaTask0.node))) preRes.escaped
                  { r1'.1 with revDirs := r1'.1.revDirs ++ ls.st.revDirs } r1'.2 w₂ ∧
              ls.st.nextVid.toNat ≤ r1'.1.nextVid.toNat ∧
              r1'.1.maxSlots.toNat ≤
                (regaRunAux0 (fuel - 1) preRes.escaped ls.st lsClean.ctrl
                  (lsClean.work ++ w₂)).1.maxSlots.toNat ∧
              ls.st.maxSlots.toNat ≤ r1'.1.maxSlots.toNat ∧
              (∀ v < ls.st.nextVid.toNat,
                arrGetU0 r1'.1.vslot (UInt32.ofNat v) = arrGetU0 ls.st.vslot (UInt32.ofNat v)) ∧
              ∃ seenJnz' nextSc' preSt',
                RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc' preSt' pw₂ seenJnz'
                  { r1'.1 with revDirs := r1'.1.revDirs ++ ls.st.revDirs } r1'.2 w₂ m₂ := by
            rwa [hz_clean] at hih
          have hsub_fuel : (fuel - 1).toNat - workNodeCount0 (lsClean.work.map RegaTask0.node) =
              fuel.toNat - N := by
            rw [hfl1]; omega
          have hls_eq : ls.st.nextVid = lsClean.st.nextVid ∧
              ls.st.maxSlots = lsClean.st.maxSlots ∧ ls.st.vslot = lsClean.st.vslot := by
            rw [hcl.2.2]; exact ⟨rfl, rfl, rfl⟩
          refine ⟨?_, ?_, ?_, ?_, fun v hv => ?_, ?_⟩
          · rw [List.cons_append, hsplit_full1, hcl.1, hcl.2.1, hih'.1, ← hsub_fuel,
              hcomb_st, hcomb_ctrl]
          · rw [hr1_eq]; exact Nat.le_trans hmono1.1 (hls_eq.1 ▸ hih'.2.1)
          · rw [hr1_eq, hfull_eq]; exact hih'.2.2.1
          · rw [hr1_eq]; exact Nat.le_trans hmono1.2.1 (hls_eq.2.1 ▸ hih'.2.2.2.1)
          · rw [hr1_eq]
            have hv2 : v < ls.st.nextVid.toNat := hls_eq.1 ▸ Nat.lt_of_lt_of_le hv hmono1.1
            exact (hih'.2.2.2.2.1 v hv2).trans (hls_eq.2.2 ▸ hmono1.2.2 v hv)
          · rw [← hcomb_st, ← hcomb_ctrl]; exact hih'.2.2.2.2.2

/-! ### Program-Slice Helpers, `FnFrameInv0` Lemmas, & Binder Execution Specs -/

theorem compileFnFinish0_rev_eq (fn : TFlatFn0) (r : RegaSt0) :
    let fSz := x64FrameSizeU0 r.maxSlots
    revDirAux0 (emitSpAdj0 true fSz [.label (.sym fn.name)])
      (patchEpilogues0 fSz (revDirAux0 r.revDirs []) []) =
    .label (.sym fn.name) ::
      ((emitSpAdj0 true fSz []).reverse ++
        patchEpilogues0 fSz (revDirAux0 r.revDirs []) []) := by
  intro fSz
  rw [(emitSpAdj0_acc true fSz (Or.inl rfl) [.label (.sym fn.name)]).1,
    revDirAux0_eq, List.reverse_append, List.reverse_singleton,
    List.singleton_append, List.cons_append]

theorem infix_getElem?_zero {α : Type} {xs ys : List α} {k : Nat} {x : α}
    (hinf : xs.IsInfixAt ys k) (hx : xs[0]? = some x) : ys[k]? = some x := by
  cases xs with
  | nil => simp at hx
  | cons a _ =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
    subst hx
    exact (List.IsInfixAt.cons hinf).1

theorem list_drop_getElem9 {α : Type} (xs ys : List α) (k j : Nat)
    (hj : j < ys.length) (hkj : k + j < xs.length) (he : xs.drop k = ys) :
    ys[j]'hj = xs[k + j]'hkj := by
  subst he; exact List.getElem_drop

theorem list_getElem_eq9 {α : Type} (xs : List α) {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) (he : i = j) :
    xs[i]'hi = xs[j]'hj := by
  subst he; rfl

theorem infix_labelAddr_eq {h : Host} {prog : List Directive} {k : Nat} {l : Sym}
    (hu : x64ScalarTarget.LabelsUnique h)
    (hinf : prog.IsInfixAt (x64ScalarMach.prog h) k)
    (hl : prog[0]? = some (x64Frame.label l)) :
    x64ScalarMach.labelAddr h l = x64ScalarMach.addrOf h k := by
  have hk := infix_getElem?_zero hinf hl
  exact x64ScalarTarget.frameSpec.labelAddr_eq hk fun j hj heq =>
    absurd (hu j k l heq hk) (Nat.ne_of_lt hj)

theorem defined_labelAddr_eq {h : Host} {l : Sym}
    (hu : x64ScalarTarget.LabelsUnique h) (hd : x64ScalarTarget.Defined h l) :
    ∃ j, (x64ScalarMach.prog h)[j]? = some (x64Frame.label l) ∧
      x64ScalarMach.labelAddr h l = x64ScalarMach.addrOf h j := by
  obtain ⟨j, hj⟩ := hd
  exact ⟨j, hj, x64ScalarTarget.frameSpec.labelAddr_eq hj fun i hi heq =>
    absurd (hu i j l heq hj) (Nat.ne_of_lt hi)⟩

theorem listNoSpZero0_prependLbl (cur : RegaTask0) (st : RegaSt0) (ctrl : CtrlSt0) :
    ListNoSpZero0 (regaPrependLbl0 cur { st with revDirs := [] } ctrl).revDirs := by
  dsimp only [regaPrependLbl0]; split
  · exact listNoSpZero0_nil
  · exact listNoSpZero0_cons (by intro h; cases h) listNoSpZero0_nil

theorem regaPrependLbl0_dirs_eq (cur : RegaTask0) (st : RegaSt0) (ctrl : CtrlSt0) :
    let st0 := regaPrependLbl0 cur { st with revDirs := [] } ctrl
    st0.revDirs = if cur.lblId = 0 then [] else [.label (.loc ctrl.fnIdx cur.lblId)] := by
  dsimp only [regaPrependLbl0]; split <;> rfl

theorem sub_add_ofNat_le (a : BitVec 64) {n k : Nat} (hle : k ≤ n) :
    a - BitVec.ofNat 64 n + BitVec.ofNat 64 k = a - BitVec.ofNat 64 (n - k) := by
  have h1 : BitVec.ofNat 64 n = BitVec.ofNat 64 (n - k) + BitVec.ofNat 64 k := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.add_mod_mod, Nat.mod_add_mod, Nat.sub_add_cancel hle]
  rw [h1]
  grind

theorem fnFrameInv0_mem_slots {ns : UInt32} {s0 : MachineData} {ra0 : Int64} {n : Nat}
    {Rf : Mem 64 → Prop} {mCur : Mem 64} {s : MachineData} {σ : List (BitVec 64)}
    (h : FnFrameInv0 ns s0 ra0 n Rf mCur s σ) :
    s.dmem =⋆ array64 (s.regs.get64 .rsp) σ ⋆
      (Eq mCur ⋆ x64ScalarFramePreds.Saved (s0.regs.get64 .rsp) ra0 ns.toNat ⋆
        region (s0.regs.get64 .rsp - BitVec.ofNat 64 n) (n - x64FrameSize ns.toNat) ⋆ Rf) :=
  sep_cast h.2.2.2 (by ac_rfl)

theorem fnFrameInv0_of_eq {ns : UInt32} {s0 : MachineData} {ra0 : Int64} {n : Nat}
    {Rf : Mem 64 → Prop} {mCur : Mem 64} {s s' : MachineData} {σ : List (BitVec 64)}
    {clob : List Reg64} {fClob : FlagMask}
    (h : FnFrameInv0 ns s0 ra0 n Rf mCur s σ)
    (hfr : x64ScalarMach.Frame x64CondReads s s' clob [] fClob)
    (hrsp : .rsp ∉ clob) (hcs : ∀ r ∈ x64Frame.calleeSaved, r ∉ clob)
    (hmem : s'.dmem = s.dmem) :
    FnFrameInv0 ns s0 ra0 n Rf mCur s' σ := by
  obtain ⟨hlen, hr, hcal, hm⟩ := h
  have hrsp' : s'.regs.get64 .rsp = s.regs.get64 .rsp := hfr.1 .rsp hrsp
  refine ⟨hlen, hrsp'.trans hr,
    fun r hrm => (hfr.1 r (hcs r hrm)).trans (hcal r hrm), ?_⟩
  rw [hmem, hrsp']
  exact hm

theorem escOuterAgree0_of_slotsAgree0 {esc : Array Nat} {preSt : PreSt0} {st : RegaSt0}
    {p : PreItem0} {cur : RegaTask0} {vT : List Ty0} {vs : List ((ty : Ty) × Val ty)}
    {σ : List (BitVec 64)} {info : LblInfo0} {outerVs : List ((ty : Ty) × Val ty)}
    {pLen : Nat}
    (hag : SlotsAgree0 esc preSt st p cur vT vs σ)
    (hplen : pLen + info.outerVenv.length = cur.venv.length)
    (hv : cur.venv.drop pLen = info.outerVenv)
    (hvt : vT.drop pLen = info.outerVT)
    (hvs : vs.drop pLen = outerVs) :
    EscOuterAgree0 esc st.vslot info outerVs σ := by
  obtain ⟨hv_len, henv, hslot⟩ := hag
  have hov_len : info.outerVenv.length = outerVs.length := by
    rw [← hv, ← hvs, List.length_drop, List.length_drop, hv_len]
  have henv_drop : EnvTypesOk0 info.outerVT outerVs := by
    rw [← hvt, ← hvs]
    have hplen_le : pLen ≤ vT.length := by have := envTypesOk0_length henv; omega
    clear hvt hvs hv hplen hslot hv_len hov_len
    induction pLen generalizing vT vs with
    | zero => exact henv
    | succ k ih =>
      cases vT with
      | nil => simp at hplen_le
      | cons _ ts => cases vs with
        | nil => exact False.elim henv
        | cons _ ws => exact ih henv.2 (by simp at hplen_le; omega)
  refine ⟨hov_len, henv_drop, fun idx hi hesc => ?_⟩
  have hpi : pLen + idx < cur.venv.length := by omega
  have hvid_eq : info.outerVenv[idx]'hi = cur.venv[pLen + idx]'hpi :=
    list_drop_getElem9 cur.venv info.outerVenv pLen idx hi hpi hv
  have hlv : LiveInTask0 esc preSt st p cur (cur.venv[pLen + idx]'hpi).toNat :=
    Or.inl ⟨hvid_eq ▸ hesc, by rw [UInt32.ofNat_toNat]; exact List.getElem_mem _⟩
  obtain ⟨hsl, hvs', ht', hcanon⟩ := hslot (pLen + idx) hpi hlv
  have hvs_lt : idx < outerVs.length := hov_len ▸ hi
  have ht_lt : idx < info.outerVT.length := by have := envTypesOk0_length henv_drop; omega
  have hvs_eq : outerVs[idx]'hvs_lt = vs[pLen + idx]'hvs' :=
    list_drop_getElem9 vs outerVs pLen idx hvs_lt hvs' hvs
  have hvt_eq : info.outerVT[idx]'ht_lt = vT[pLen + idx]'ht' :=
    list_drop_getElem9 vT info.outerVT pLen idx ht_lt ht' hvt
  have hsl' : (arrGetU0 st.vslot (info.outerVenv[idx]'hi)).toNat < σ.length := hvid_eq ▸ hsl
  refine ⟨hsl', hvs_lt, ht_lt, ?_⟩
  rw [list_getElem_eq9 σ hsl' hsl (congrArg UInt32.toNat (congrArg (arrGetU0 st.vslot) hvid_eq)),
    hvs_eq, hvt_eq]
  exact hcanon

theorem escOuterAgree0_vslot_congr {esc : Array Nat} {vsl1 vsl2 : Array Nat}
    {info : LblInfo0} {outerVs : List ((ty : Ty) × Val ty)} {σ : List (BitVec 64)} {bound : Nat}
    (hbd : ∀ w ∈ info.outerVenv, w.toNat < bound)
    (heq : ∀ v < bound, arrGetU0 vsl1 (UInt32.ofNat v) = arrGetU0 vsl2 (UInt32.ofNat v))
    (h : EscOuterAgree0 esc vsl1 info outerVs σ) :
    EscOuterAgree0 esc vsl2 info outerVs σ := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun idx hi hesc => ?_⟩
  have hw := heq _ (hbd _ (List.getElem_mem hi))
  rw [UInt32.ofNat_toNat] at hw
  obtain ⟨hsl, hvs, ht, hcanon⟩ := h3 idx hi hesc
  have hsl' : (arrGetU0 vsl2 (info.outerVenv[idx]'hi)).toNat < σ.length := hw ▸ hsl
  refine ⟨hsl', hvs, ht, ?_⟩
  rw [list_getElem_eq9 σ hsl' hsl (congrArg UInt32.toNat hw.symm)]
  exact hcanon

theorem escOuterAgree0_mem_congr {esc : Array Nat} {vslot : Array Nat}
    {info : LblInfo0} {outerVs : List ((ty : Ty) × Val ty)} {σ σ' : List (BitVec 64)}
    (hlen : σ'.length = σ.length)
    (hmem : ∀ idx (hi : idx < info.outerVenv.length), esc.getD info.outerVenv[idx].toNat 0 = 1 →
      ∀ hsl : (arrGetU0 vslot (info.outerVenv[idx]'hi)).toNat < σ.length,
        σ'[(arrGetU0 vslot (info.outerVenv[idx]'hi)).toNat]'(hlen ▸ hsl) =
          σ[(arrGetU0 vslot (info.outerVenv[idx]'hi)).toNat]'hsl)
    (h : EscOuterAgree0 esc vslot info outerVs σ) :
    EscOuterAgree0 esc vslot info outerVs σ' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun idx hi hesc => ?_⟩
  obtain ⟨hsl, hvs, ht, hcanon⟩ := h3 idx hi hesc
  refine ⟨hlen ▸ hsl, hvs, ht, ?_⟩
  rw [hmem idx hi hesc hsl]; exact hcanon

theorem glEntrySem0_eq_vslot_nextSlot {h : Host} {symName : Sym0 → Sym}
    {post : MachineState → Prop} {ns : UInt32} {s0 : MachineData} {ra0 : Int64} {n : Nat}
    {Rf : Mem 64 → Prop} {esc : Array Nat} {st st' : RegaSt0} {cur cur' : RegaTask0}
    {mCur mCur' : TaskMeta0} {vs : List ((ty : Ty) × Val ty)} {fnIdx : UInt32} :
    ∀ {gl : List LblInfo0} {ls : List ((ts : List Ty) × Cont ts)},
      GlEntriesSem0 h symName post ns s0 ra0 n Rf esc st cur mCur vs fnIdx gl ls →
      cur.nextSlot.toNat ≤ cur'.nextSlot.toNat →
      cur'.venv = cur.venv → mCur'.vT = mCur.vT →
      (∀ info ∈ gl, ∃ N,
        (∀ w ∈ info.outerVenv, w.toNat < N) ∧
        ∀ v < N, arrGetU0 st'.vslot (UInt32.ofNat v) = arrGetU0 st.vslot (UInt32.ofNat v)) →
      GlEntriesSem0 h symName post ns s0 ra0 n Rf esc st' cur' mCur' vs fnIdx gl ls
  | [], [], _, _, _, _, _ => trivial
  | [], _ :: _, hgl, _, _, _, _ => False.elim hgl
  | _ :: _, [], hgl, _, _, _, _ => False.elim hgl
  | info :: glRest, lentry :: lsRest, hgl, hnxt, hvenv, hvT, houter => by
    refine ⟨?_, glEntrySem0_eq_vslot_nextSlot hgl.2 hnxt hvenv hvT
      fun inf hinf => houter inf (List.mem_cons_of_mem _ hinf)⟩
    obtain ⟨hn_le, hdef, outerVs, pLen, hplen, hv, hvt, hvs, J, rfl, hj⟩ := hgl.1
    obtain ⟨N, hN_bd, hN_eq⟩ := houter info List.mem_cons_self
    refine ⟨Nat.le_trans hn_le hnxt, hdef, outerVs, pLen, hvenv ▸ hplen, hvenv ▸ hv,
      hvT ▸ hvt, hvs, J, rfl, fun xs m' hJ s' σ' hfr hesc htup => ?_⟩
    exact hj xs m' hJ s' σ' hfr (escOuterAgree0_vslot_congr hN_bd hN_eq hesc) htup

theorem glEntrySem0_pushTys0 {h : Host} {symName : Sym0 → Sym}
    {post : MachineState → Prop} {ns : UInt32} {s0 : MachineData} {ra0 : Int64} {n : Nat}
    {Rf : Mem 64 → Prop} {esc : Array Nat} {st st' : RegaSt0} {cur cur' : RegaTask0}
    {mCur mCur' : TaskMeta0} {vs : List ((ty : Ty) × Val ty)} {fnIdx : UInt32}
    {bs : List Ty0} {rvs : Tup Val (ty0ListToTy bs)} {nv : UInt32} :
    ∀ {gl : List LblInfo0} {ls : List ((ts : List Ty) × Cont ts)},
      GlEntriesSem0 h symName post ns s0 ra0 n Rf esc st cur mCur vs fnIdx gl ls →
      cur.nextSlot.toNat ≤ cur'.nextSlot.toNat →
      cur'.venv = pushFreshVids0 bs.length nv cur.venv →
      mCur'.vT = pushTys0 bs mCur.vT →
      (∀ info ∈ gl, ∃ N,
        (∀ w ∈ info.outerVenv, w.toNat < N) ∧
        ∀ v < N, arrGetU0 st'.vslot (UInt32.ofNat v) = arrGetU0 st.vslot (UInt32.ofNat v)) →
      GlEntriesSem0 h symName post ns s0 ra0 n Rf esc st' cur' mCur'
        (pushTup rvs vs) fnIdx gl ls
  | [], [], _, _, _, _, _ => trivial
  | [], _ :: _, hgl, _, _, _, _ => False.elim hgl
  | _ :: _, [], hgl, _, _, _, _ => False.elim hgl
  | info :: glRest, lentry :: lsRest, hgl, hnxt, hvenv, hvT, houter => by
    refine ⟨?_, glEntrySem0_pushTys0 hgl.2 hnxt hvenv hvT
      fun inf hinf => houter inf (List.mem_cons_of_mem _ hinf)⟩
    obtain ⟨hn_le, hdef, outerVs, pLen, hplen, hv, hvt, hvs, J, rfl, hj⟩ := hgl.1
    obtain ⟨N, hN_bd, hN_eq⟩ := houter info List.mem_cons_self
    refine ⟨Nat.le_trans hn_le hnxt, hdef, outerVs, bs.length + pLen, ?_, ?_, ?_, ?_, J, rfl,
      fun xs m' hJ s' σ' hfr hesc htup => ?_⟩
    · rw [hvenv, pushFreshVids0_length]; omega
    · rw [hvenv, ← list_drop_drop9, pushFreshVids0_drop, hv]
    · rw [hvT, ← list_drop_drop9, pushTys0_drop, hvt]
    · rw [← list_drop_drop9, pushTup_drop, hvs]
    · exact hj xs m' hJ s' σ' hfr (escOuterAgree0_vslot_congr hN_bd hN_eq hesc) htup

/-- Slot agreement for freshly bound variables (`nv .. nv + ts.length - 1`). -/
@[expose] def PushAgree0 (esc : Array Nat) (remUses vslot : Array Nat) (nv : UInt32) :
    (ts : List Ty0) → Tup Val (ty0ListToTy ts) → List (BitVec 64) → Prop
  | [], (), _ => True
  | t :: rest, (x, xs), σ =>
    ((0 < remUses.getD nv.toNat 0 ∨ 0 < esc.getD nv.toNat 0) →
      ∃ hsl : (arrGetU0 vslot nv).toNat < σ.length,
        σ[(arrGetU0 vslot nv).toNat]'hsl = toCanon64 t x) ∧
    PushAgree0 esc remUses vslot (nv + 1) rest xs σ

theorem pushAgree0_mono_esc_rem {esc remUses : Array Nat} {vslot1 vslot2 : Array Nat}
    {σ : List (BitVec 64)} :
    ∀ (ts : List Ty0) (xs : Tup Val (ty0ListToTy ts)) (nv : UInt32),
      nv.toNat + ts.length < 2 ^ 31 →
      (∀ k < ts.length, arrGetU0 vslot1 (nv + UInt32.ofNat k) =
        arrGetU0 vslot2 (nv + UInt32.ofNat k)) →
      PushAgree0 esc remUses vslot1 nv ts xs σ → PushAgree0 esc remUses vslot2 nv ts xs σ
  | [], (), _, _, _, _ => trivial
  | _ :: rest, (_, xs), nv, hnv, heq, ⟨h1, h2⟩ => by
    simp only [List.length_cons] at hnv
    have heq0 := heq 0 (Nat.zero_lt_succ _)
    rw [show nv + UInt32.ofNat 0 = nv from u32_ofNat_add_eq7 nv 0 (by omega) ▸
      congrArg UInt32.ofNat (Nat.add_zero nv.toNat) ▸ UInt32.ofNat_toNat] at heq0
    refine ⟨fun hneed => by rw [← heq0]; exact h1 hneed,
      pushAgree0_mono_esc_rem rest xs (nv + 1)
        (by rw [u32_add1_toNat7 (by omega)]; omega) (fun k hk => by
          have := heq (k + 1) (Nat.succ_lt_succ hk)
          rwa [u32_add_ofNat_succ9] at this) h2⟩

theorem pushFresh_slotsAgree0_aux (esc : Array Nat) (preSt' : PreSt0) (st' : RegaSt0)
    (p' : PreItem0) (t' : RegaTask0) (σ : List (BitVec 64)) :
    ∀ (ts : List Ty0) (xs : Tup Val (ty0ListToTy ts)) (nv : UInt32)
      (venv : List UInt32) (vT : List Ty0) (vs : List ((ty : Ty) × Val ty)),
      nv.toNat + ts.length < 2 ^ 31 →
      venv.length = vs.length → EnvTypesOk0 vT vs →
      (∀ v ∈ venv, v.toNat < nv.toNat) →
      (∀ (idx : Nat) (_hi : idx < venv.length),
        let vid := venv[idx]
        LiveInTask0 esc preSt' st' p' t' vid.toNat →
        ∃ (hsl : (arrGetU0 st'.vslot vid).toNat < σ.length) (hvs : idx < vs.length)
          (ht : idx < vT.length),
          HoldsCanon640 vT[idx] vs[idx] σ[(arrGetU0 st'.vslot vid).toNat]) →
      PushAgree0 esc st'.remUses st'.vslot nv ts xs σ →
      (pushFreshVids0 ts.length nv venv).length = (pushTup xs vs).length ∧
      EnvTypesOk0 (pushTys0 ts vT) (pushTup xs vs) ∧
      ∀ (idx : Nat) (hi : idx < (pushFreshVids0 ts.length nv venv).length),
        let vid := (pushFreshVids0 ts.length nv venv)[idx]
        LiveInTask0 esc preSt' st' p' t' vid.toNat →
        ∃ (hsl : (arrGetU0 st'.vslot vid).toNat < σ.length)
          (hvs : idx < (pushTup xs vs).length)
          (ht : idx < (pushTys0 ts vT).length),
          HoldsCanon640 (pushTys0 ts vT)[idx] (pushTup xs vs)[idx]
            σ[(arrGetU0 st'.vslot vid).toNat] := by
  intro ts
  induction ts with
  | nil =>
    intro xs nv venv vT vs _ hlen henv _ hold _
    cases xs
    exact ⟨hlen, henv, hold⟩
  | cons t rest ih =>
    intro xs nv venv vT vs hnv hlen henv hbd hold hpa
    simp only [List.length_cons] at hnv
    rcases xs with ⟨x, restX⟩
    have hnv1 : (nv + 1).toNat = nv.toNat + 1 := u32_add1_toNat7 (by omega)
    dsimp only [PushAgree0] at hpa
    have hbd1 : ∀ v ∈ nv :: venv, v.toNat < (nv + 1).toNat := by
      intro v hv; rcases List.mem_cons.mp hv with rfl | hv'
      · rw [hnv1]; omega
      · have := hbd v hv'; rw [hnv1]; omega
    have hold1 : ∀ (idx : Nat) (_hi : idx < (nv :: venv).length),
        let vid := (nv :: venv)[idx]
        LiveInTask0 esc preSt' st' p' t' vid.toNat →
        ∃ (hsl : (arrGetU0 st'.vslot vid).toNat < σ.length)
          (hvs : idx < (⟨ty0ToTy t, x⟩ :: vs).length)
          (ht : idx < (t :: vT).length),
          HoldsCanon640 (t :: vT)[idx] (⟨ty0ToTy t, x⟩ :: vs)[idx]
            σ[(arrGetU0 st'.vslot vid).toNat] := by
      intro idx hi
      cases idx with
      | zero =>
        dsimp only [List.getElem_cons_zero]
        intro hlv
        have hneed : 0 < st'.remUses.getD nv.toNat 0 ∨ 0 < esc.getD nv.toNat 0 := by
          rcases hlv with ⟨hes, _⟩ | ⟨_, _, hpos⟩
          · right; omega
          · left; exact hpos
        obtain ⟨hsl, heq⟩ := hpa.1 hneed
        refine ⟨hsl, Nat.zero_lt_succ _, Nat.zero_lt_succ _, ?_⟩
        rw [heq]; exact holdsCanon640_mk x
      | succ idx' =>
        dsimp only [List.getElem_cons_succ]
        intro hlv
        obtain ⟨hsl, hvs, ht, hcanon⟩ := hold idx' (Nat.lt_of_succ_lt_succ hi) hlv
        exact ⟨hsl, Nat.succ_lt_succ hvs, Nat.succ_lt_succ ht, hcanon⟩
    exact ih restX (nv + 1) (nv :: venv) (t :: vT) (⟨ty0ToTy t, x⟩ :: vs)
      (by rw [hnv1]; omega) (by simp [hlen]) (envTypesOk0_cons henv) hbd1 hold1 hpa.2

private theorem arrGetU0_eq9 (arr : Array Nat) (i : UInt32) :
    (arrGetU0 arr i).toNat = arr.getD i.toNat 0 % 2 ^ 32 := by
  dsimp only [arrGetU0]; exact u32_toNat_ofNat7 _

theorem allocSlot0_spec9 (free : List UInt32) (nxt maxSl : UInt32) (maxBd : Nat)
    (hinv : SlotPoolInv0 free nxt maxSl maxBd) (hlt : nxt.toNat + 1 ≤ maxBd) :
    let sp := allocSlot0 free nxt maxSl
    SlotPoolInv0 sp.free sp.nxt sp.maxSlots maxBd ∧
    sp.slot.toNat < sp.nxt.toNat ∧
    nxt.toNat ≤ sp.nxt.toNat ∧ sp.nxt.toNat ≤ nxt.toNat + 1 ∧
    (sp.slot ∈ free ∨ sp.slot = nxt) ∧
    (∀ x, x ∈ sp.free ↔ x ∈ free ∧ x ≠ sp.slot) := by
  cases free with
  | nil =>
    dsimp only [allocSlot0]
    obtain ⟨_, _, h1, h2, hmax_bd⟩ := hinv
    have hadd1 : (nxt + 1).toNat = nxt.toNat + 1 := u32_add1_toNat7 (by omega)
    have hlt_s : nxt.toNat < (nxt + 1).toNat := by omega
    refine ⟨⟨List.nodup_nil, fun _ hm => by simp at hm, ?_, ?_, hmax_bd⟩,
      hlt_s, by omega, by omega, Or.inr rfl, fun x => by simp⟩
    · rw [u32Max0_toNat, hadd1]; exact Nat.le_max_right _ _
    · rw [u32Max0_toNat, hadd1]; exact Nat.max_le.mpr ⟨h2, hlt⟩
  | cons s rest =>
    dsimp only [allocSlot0]
    obtain ⟨hnd0, hflt0, h1, h2, hmax_bd⟩ := hinv
    obtain ⟨hnin, hnd⟩ := List.nodup_cons.mp hnd0
    have hs_lt : s.toNat < nxt.toNat := hflt0 s List.mem_cons_self
    have hadd1 : (s + 1).toNat = s.toNat + 1 := u32_add1_toNat7 (by omega)
    refine ⟨⟨hnd, fun x hx => hflt0 x (List.mem_cons_of_mem _ hx), ?_, ?_, hmax_bd⟩,
      hs_lt, Nat.le_refl _, Nat.le_add_right _ _, Or.inl List.mem_cons_self, fun x => ?_⟩
    · rw [u32Max0_toNat]; exact Nat.le_trans h1 (Nat.le_max_left _ _)
    · rw [u32Max0_toNat, hadd1]; exact Nat.max_le.mpr ⟨h2, by omega⟩
    · constructor
      · intro hx; exact ⟨List.mem_cons_of_mem _ hx, fun h => hnin (h ▸ hx)⟩
      · rintro ⟨hx, hne⟩; rcases List.mem_cons.mp hx with rfl | hx'
        · exact absurd rfl hne
        · exact hx'

theorem bindRetsN0_run_spec {symName : Sym0 → Sym} {h : Host} {esc : Array Nat}
    {G : Mem 64 → Prop} {post : MachineState → Prop} :
    ∀ (ts : List Ty0) (k : Nat) (rem idx : UInt32) (bl : BindListOut0)
      (xs : Tup Val (ty0ListToTy ts)) (σ : List (BitVec 64)) (s : MachineData) (maxBd : Nat),
      let bl0 : BindListOut0 := { bl with st := { bl.st with revDirs := [] } }
      let bl' := bindRetsN0 esc rem idx bl0
      rem.toNat = ts.length → idx.toNat + ts.length ≤ 7 →
      tupAbiHolds0 s true idx.toNat ts xs →
      bl.st.vslot.size = bl.st.nextVid.toNat →
      bl.st.nextVid.toNat + ts.length < 2 ^ 31 →
      SlotPoolInv0 bl.free bl.nxt bl.st.maxSlots maxBd →
      bl.nxt.toNat + ts.length ≤ maxBd →
      bl'.st.maxSlots.toNat ≤ σ.length →
      (∀ j < ts.length, esc.getD (bl.st.nextVid.toNat + j) 0 < 2 ^ 32 ∧
        bl.st.remUses.getD (bl.st.nextVid.toNat + j) 0 < 2 ^ 32) →
      (s.dmem =⋆ array64 (s.regs.get64 .rsp) σ ⋆ G) →
      x64ScalarMach.FallsTo x64CondReads h k
        (toAmd64Program symName (emitFwd0 bl'.st.revDirs)) [.r10] [] maskNone s
        (fun s' => ∃ (σ' : List (BitVec 64)) (hσ' : σ'.length = σ.length),
          (∀ q : UInt32, q.toNat < bl.nxt.toNat → q ∉ bl.free →
            ∀ hq : q.toNat < σ.length, σ'[q.toNat]'(hσ' ▸ hq) = σ[q.toNat]'hq) ∧
          PushAgree0 esc bl'.st.remUses bl'.st.vslot bl.st.nextVid ts xs σ' ∧
          (s'.dmem =⋆ array64 (s'.regs.get64 .rsp) σ' ⋆ G)) post := by
  intro ts
  induction ts with
  | nil =>
    intro k rem idx bl xs σ s maxBd bl0 bl' hrem _ _ _ _ _ _ _ _ hmem
    cases xs
    have hr0 : rem = 0 := u32_ext7 hrem
    have hrev : bl'.st.revDirs = [] := by
      dsimp only [bl', bl0]; subst hr0; rw [bindRetsN0.eq_def]; simp
    rw [hrev]
    dsimp only [emitFwd0, List.reverse_nil, toAmd64Program, List.flatMap_nil]
    refine Machine.FallsTo.nil ⟨σ, rfl, fun _ _ _ _ => rfl, trivial, hmem⟩
  | cons t rest ih =>
    intro k rem idx bl xs σ s maxBd bl0 bl' hrem hidx htup hvsz hnv hpool hnxt hms hbd hmem
    change Val (ty0ToTy t) × Tup Val (ty0ListToTy rest) at xs
    simp only [List.length_cons] at hnv hnxt
    rcases xs with ⟨x, restX⟩
    dsimp only [tupAbiHolds0] at htup
    have hrem_pos : 0 < rem.toNat := by rw [hrem]; simp
    have hrne : rem ≠ 0 := fun h => by simp [h] at hrem_pos
    have hsub : (rem - 1).toNat = rest.length := by
      rw [u32_sub1_toNat7 hrem_pos, hrem]; simp
    have hidx1 : (idx + 1).toNat = idx.toNat + 1 :=
      u32_add1_toNat7 (by simp only [List.length_cons] at hidx; omega)
    let bo := bindOneSlot0 esc (abiRegAt0 true idx) bl0.st bl0.free bl0.nxt
    let bl1 : BindListOut0 := ⟨bo.vid :: bl0.venv, bo.st, bo.free, bo.nxt⟩
    let bl1Clean : BindListOut0 := { bl1 with st := { bl1.st with revDirs := [] } }
    let bl'1 := bindRetsN0 esc (rem - 1) (idx + 1) bl1Clean
    have hbo_spec := bindRetsN0_spec esc (t :: rest).length rem idx bl0 maxBd
      hrem hvsz (by simp only [List.length_cons]; exact hnv)
      hpool (by simp only [List.length_cons]; exact hnxt) hbd
    have hbr_tail := bindRetsN0_revDirs esc rest.length (rem - 1) (idx + 1) bl1 hsub
    dsimp only at hbr_tail
    have hbl'_eq : bl' = bindRetsN0 esc (rem - 1) (idx + 1) bl1 := by
      dsimp only [bl']; rw [bindRetsN0.eq_def]; simp only [hrne, ↓reduceDIte]
      rfl
    have hrev_split : bl'.st.revDirs = bl'1.st.revDirs ++ bo.st.revDirs := by
      rw [hbl'_eq, hbr_tail.2.2.2.1]
    have hbl'_st_eq : bl'.st = { bl'1.st with revDirs := bl'1.st.revDirs ++ bo.st.revDirs } := by
      rw [hbl'_eq, hbr_tail.2.2.2.1]
    have hbo_ms_le : bo.st.maxSlots.toNat ≤ bl'.st.maxSlots.toNat := by
      rw [hbl'_eq]
      exact bindRetsN0_maxSlots_le esc rest.length (rem - 1) (idx + 1) bl1 hsub
    have h1_nv : bo.st.nextVid.toNat = bl.st.nextVid.toNat + 1 := by
      dsimp only [bl0, bo, bindOneSlot0]; split <;> exact u32_add1_toNat7 (by omega)
    have h1_nv_eq : bo.st.nextVid = bl.st.nextVid + 1 := by
      dsimp only [bl0, bo, bindOneSlot0]; split <;> rfl
    have h1_sz : bo.st.vslot.size = bo.st.nextVid.toNat := by
      rw [h1_nv]; dsimp only [bl0, bo, bindOneSlot0]
      split <;> simp only [Array.size_push, hvsz]
    have h1_rem : bo.st.remUses = bl.st.remUses := by
      dsimp only [bl0, bo, bindOneSlot0]; split <;> rfl
    have h1_pool : SlotPoolInv0 bo.free bo.nxt bo.st.maxSlots maxBd := by
      dsimp only [bo, bindOneSlot0]; split
      · exact (allocSlot0_spec9 bl0.free bl0.nxt bl0.st.maxSlots maxBd hpool
          (by dsimp only [bl0]; omega)).1
      · exact hpool
    have h1_nxt_le : bl.nxt.toNat ≤ bo.nxt.toNat ∧ bo.nxt.toNat ≤ bl.nxt.toNat + 1 := by
      dsimp only [bo, bindOneSlot0]; split
      · have hs := allocSlot0_spec9 bl0.free bl0.nxt bl0.st.maxSlots maxBd hpool
          (by dsimp only [bl0]; omega)
        exact ⟨hs.2.2.1, hs.2.2.2.1⟩
      · exact ⟨Nat.le_refl _, Nat.le_succ _⟩
    have h1_fr : ∀ x, x ∈ bo.free → x ∈ bl.free := by
      intro q hq; dsimp only [bo, bindOneSlot0] at hq; split at hq
      · exact ((allocSlot0_spec9 bl0.free bl0.nxt bl0.st.maxSlots maxBd hpool
          (by dsimp only [bl0]; omega)).2.2.2.2.2 q).mp hq |>.1
      · exact hq
    have hneed_iff :
        ((decide (0 < arrGetU0 bl0.st.remUses bl0.st.nextVid) ||
          decide (0 < arrGetU0 esc bl0.st.nextVid)) = true) ↔
        (0 < bl.st.remUses.getD bl.st.nextVid.toNat 0 ∨
          0 < esc.getD bl.st.nextVid.toNat 0) := by
      have hre := arrGetU0_eq9 bl0.st.remUses bl0.st.nextVid
      have hee := arrGetU0_eq9 esc bl0.st.nextVid
      dsimp only [bl0] at hre hee ⊢
      rw [Nat.mod_eq_of_lt (by simpa only [Nat.add_zero] using (hbd 0 (by simp)).2)] at hre
      rw [Nat.mod_eq_of_lt (by simpa only [Nat.add_zero] using (hbd 0 (by simp)).1)] at hee
      simp only [Bool.or_eq_true, decide_eq_true_eq, UInt32.lt_iff_toNat_lt, UInt32.toNat_zero,
        hre, hee]
    have h1_slot_spec := bindRetsN0_spec esc rest.length (rem - 1) (idx + 1) bl1Clean maxBd
      hsub h1_sz (by dsimp only [bl1Clean, bl1]; rw [h1_nv]; omega) h1_pool
      (by dsimp only [bl1Clean, bl1]; omega)
      (fun j hj => by
        dsimp only [bl1Clean, bl1]; rw [h1_nv, h1_rem, Nat.add_assoc, Nat.add_comm 1 j]
        exact hbd (j + 1) (by simp only [List.length_cons]; omega))
    dsimp only [bl1Clean, bl1] at h1_slot_spec
    have hbo_exec :
        x64ScalarMach.FallsTo x64CondReads h k
          (toAmd64Program symName (emitFwd0 bo.st.revDirs)) [.r10] [] maskNone s
          (fun s1 => ∃ (σ1 : List (BitVec 64)) (hσ1 : σ1.length = σ.length),
            (∀ q : UInt32, q.toNat < bl.nxt.toNat → q ∉ bl.free →
              ∀ hq : q.toNat < σ.length, σ1[q.toNat]'(hσ1 ▸ hq) = σ[q.toNat]'hq) ∧
            ((0 < bl.st.remUses.getD bl.st.nextVid.toNat 0 ∨
              0 < esc.getD bl.st.nextVid.toNat 0) →
              ∃ hsl : (arrGetU0 bl'.st.vslot bl.st.nextVid).toNat < σ1.length,
                σ1[(arrGetU0 bl'.st.vslot bl.st.nextVid).toNat]'hsl = toCanon64 t x ∧
                (arrGetU0 bl'.st.vslot bl.st.nextVid).toNat < bo.nxt.toNat ∧
                arrGetU0 bl'.st.vslot bl.st.nextVid ∉ bo.free) ∧
            tupAbiHolds0 s1 true (idx + 1).toNat rest restX ∧
            (s1.dmem =⋆ array64 (s1.regs.get64 .rsp) σ1 ⋆ G)) post := by
      dsimp only [bo, bindOneSlot0]
      by_cases hn : (decide (0 < arrGetU0 bl0.st.remUses bl0.st.nextVid) ||
          decide (0 < arrGetU0 esc bl0.st.nextVid)) = true
      · simp only [hn, ↓reduceIte]
        let sp := allocSlot0 bl0.free bl0.nxt bl0.st.maxSlots
        have hsp := allocSlot0_spec9 bl0.free bl0.nxt bl0.st.maxSlots maxBd hpool
          (by dsimp only [bl0]; omega)
        have hsp_lt_σ : sp.slot.toNat < σ.length := by
          have h2 : bo.st.maxSlots.toNat ≤ σ.length := Nat.le_trans hbo_ms_le hms
          have hbo_nxt_le : bo.nxt.toNat ≤ bo.st.maxSlots.toNat := h1_pool.2.2.1
          have hbo_n : bo.nxt = sp.nxt := by dsimp only [bo, bindOneSlot0]; simp [hn, sp]
          have hsp_lt : sp.slot.toNat < bo.nxt.toNat := by rw [hbo_n]; exact hsp.2.1
          omega
        have hst_spec := emitSlotMem0_st_spec (symName := symName) (h := h) (k := k)
          (post := post) (abiRegAt0 true idx) (abiRegAt0_ne_r10 true idx) sp.slot hsp_lt_σ hmem
        refine Machine.FallsTo.conseq hst_spec fun s1 hd1 hfr1 => ?_
        have hfr1_rsp : s1.regs.get64 .rsp = s.regs.get64 .rsp := hfr1.1 .rsp (by simp)
        have hreg_val : s.regs.get64 (abiRegAt0 true idx) = toCanon64 t x := by
          simpa [UInt32.ofNat_toNat] using htup.1
        let σ1 := σ.set sp.slot.toNat (toCanon64 t x)
        have hσ1_len : σ1.length = σ.length := List.length_set
        have hbo_vslot : arrGetU0 bo.st.vslot bl.st.nextVid = sp.slot := by
          apply u32_ext7
          dsimp only [bo, bindOneSlot0]
          simp only [hn, ↓reduceIte]
          dsimp only [arrGetU0, bl0]
          rw [u32_toNat_ofNat7, arrPush_getD7, hvsz]
          simp only [Nat.lt_irrefl, ↓reduceIte]
          exact Nat.mod_eq_of_lt (UInt32.toNat_lt sp.slot)
        have hslot_eq : arrGetU0 bl'.st.vslot bl.st.nextVid = sp.slot := by
          have hv_pres := h1_slot_spec.2.2.2.2.2.2.2.2.1 bl.st.nextVid.toNat (by omega)
          simp only [UInt32.ofNat_toNat] at hv_pres
          have hve : bl'.st.vslot = bl'1.st.vslot := by rw [hbl'_st_eq]
          rw [hve, hv_pres, hbo_vslot]
        have hup_tup : tupAbiHolds0 s1 true (idx + 1).toNat rest restX := by
          rw [hidx1]
          refine tupAbiHolds0_frame (fun r hr => hfr1.1 r hr) (fun j hj => ?_) htup.2
          simp only [List.mem_singleton]
          exact abiRegAt0_ne_r10 true _
        refine ⟨σ1, hσ1_len, fun q hq1 hq2 hqσ => ?_, fun _ => ?_, hup_tup, ?_⟩
        · have hne : q.toNat ≠ sp.slot.toNat := fun heq => by
            have hqe : q = sp.slot := u32_ext7 heq
            rcases hsp.2.2.2.2.1 with hm | hnxt_eq
            · exact hq2 (hqe ▸ hm)
            · dsimp only [bl0] at hnxt_eq; rw [hqe, hnxt_eq] at hq1; omega
          dsimp only [σ1]; rw [List.getElem_set_ne (Ne.symm hne)]
        · refine ⟨by rw [hslot_eq, hσ1_len]; exact hsp_lt_σ, ?_, ?_, ?_⟩
          · simp only [σ1, hslot_eq, List.getElem_set_self]
          · rw [hslot_eq]; exact hsp.2.1
          · rw [hslot_eq]; exact fun hm => ((hsp.2.2.2.2.2 sp.slot).mp hm).2 rfl
        · rw [hfr1_rsp]; dsimp only [σ1]; rw [← hreg_val]; exact hd1
      · simp only [hn, Bool.false_eq_true, ↓reduceIte]
        have hnot : ¬ (0 < bl.st.remUses.getD bl.st.nextVid.toNat 0 ∨
            0 < esc.getD bl.st.nextVid.toNat 0) := fun h => hn (hneed_iff.mpr h)
        dsimp only [emitFwd0, List.reverse_nil, toAmd64Program, List.flatMap_nil]
        refine Machine.FallsTo.nil ⟨σ, rfl, fun _ _ _ _ => rfl,
          fun h => absurd h hnot, hidx1 ▸ htup.2, hmem⟩
    have hcomp_rev :
        emitFwd0 bl'.st.revDirs = emitFwd0 bo.st.revDirs ++ emitFwd0 bl'1.st.revDirs := by
      rw [hrev_split, emitFwd0_append]
    rw [hcomp_rev, toAmd64Program_append]
    refine Machine.FallsTo.weaken (Machine.FallsTo.comp hbo_exec fun s1 hq _ => by
      rcases hq with ⟨σ1, hσ1_len, hq1, hhead1, htup1, hmem1⟩
      have hih1 := ih (k + (toAmd64Program symName (emitFwd0 bo.st.revDirs)).length)
        (rem - 1) (idx + 1) bl1 restX σ1 s1 maxBd hsub
        (by rw [hidx1]; simp only [List.length_cons] at hidx; omega) htup1 h1_sz
        (by dsimp only [bl1]; rw [h1_nv]; omega) h1_pool (by dsimp only [bl1]; omega)
        (by change bl'1.st.maxSlots.toNat ≤ σ1.length
            have hms1 : bl'1.st.maxSlots.toNat = bl'.st.maxSlots.toNat := by rw [hbl'_st_eq]
            omega)
        (fun j hj => by
          dsimp only [bl1]; rw [h1_nv, h1_rem, Nat.add_assoc, Nat.add_comm 1 j]
          exact hbd (j + 1) (by simp only [List.length_cons]; omega))
        hmem1
      dsimp only [bl1] at hih1
      refine Machine.FallsTo.conseq hih1 fun s2 ⟨σ2, hσ2_len, hq2, htail2, hmem2⟩ _ => ?_
      refine ⟨σ2, hσ2_len.trans hσ1_len, fun q hql hqf hqσ => ?_, ?_, hmem2⟩
      · have hqσ1 : q.toNat < σ1.length := hσ1_len ▸ hqσ
        have hq_nxt1 : q.toNat < bo.nxt.toNat := Nat.lt_of_lt_of_le hql h1_nxt_le.1
        have hq_nf1 : q ∉ bo.free := fun hm => hqf (h1_fr q hm)
        exact (hq2 q hq_nxt1 hq_nf1 hqσ1).trans (hq1 q hql hqf hqσ)
      · dsimp only [PushAgree0]
        refine ⟨fun hneed => ?_, ?_⟩
        · have hneed0 : 0 < bl.st.remUses.getD bl.st.nextVid.toNat 0 ∨
              0 < esc.getD bl.st.nextVid.toNat 0 := by
            rw [hbo_spec.2.2.2.1] at hneed; exact hneed
          obtain ⟨hsl1, heq1, hsl_lt_bonxt, hnf_bo⟩ := hhead1 hneed0
          have hq_step := hq2 (arrGetU0 bl'.st.vslot bl.st.nextVid) hsl_lt_bonxt hnf_bo hsl1
          refine ⟨hσ2_len ▸ hsl1, ?_⟩
          exact hq_step.trans heq1
        · have hrem_eq' : bl'.st.remUses = bl'1.st.remUses := by rw [hbl'_st_eq]
          have hvsl_eq' : bl'.st.vslot = bl'1.st.vslot := by rw [hbl'_st_eq]
          rw [hrem_eq', hvsl_eq', ← h1_nv_eq]
          exact htail2)
      (fun r hr => by
        simp only [List.mem_append, List.mem_singleton] at hr ⊢
        rcases hr with rfl | rfl <;> rfl)
      (fun _ hv => nomatch hv) (by decide)

private theorem bindEntryArgs0_run_spec_aux {symName : Sym0 → Sym} {h : Host} {G : Mem 64 → Prop}
    {post : MachineState → Prop} :
    ∀ (ts : List Ty0) (k : Nat) (i : UInt32) (venv : List UInt32) (st : RegaSt0)
      (xs : Tup Val (ty0ListToTy ts)) (σ : List (BitVec 64)) (s : MachineData),
      let bl0 := bindEntryArgs0 ts i venv { st with revDirs := [] }
      i.toNat + ts.length ≤ 6 → (hi_σ : i.toNat + ts.length ≤ σ.length) →
      tupAbiHolds0 s false i.toNat ts xs →
      (s.dmem =⋆ array64 (s.regs.get64 .rsp) σ ⋆ G) →
      x64ScalarMach.FallsTo x64CondReads h k
        (toAmd64Program symName (emitFwd0 bl0.st.revDirs)) x64ScratchAndAbi [] maskNone s
        (fun s' => ∃ (σ' : List (BitVec 64)) (hσ' : σ'.length = σ.length),
          (∀ q : Nat, ∀ hq : q < i.toNat,
            σ'[q]'(hσ' ▸ by omega) = σ[q]'(by omega)) ∧
          (∀ (j : Nat) (hj : j < ts.length),
            σ'[i.toNat + j]'(hσ' ▸ by omega) =
              (tupToCanon64s ts xs)[j]'(by rw [tupToCanon64s_length]; exact hj)) ∧
          (s'.dmem =⋆ array64 (s'.regs.get64 .rsp) σ' ⋆ G)) post := by
  intro ts
  induction ts with
  | nil =>
    intro k i venv st xs σ s bl0 _ hi_σ _ hmem
    cases xs
    dsimp only [bl0, bindEntryArgs0, emitFwd0, List.reverse_nil, toAmd64Program, List.flatMap_nil]
    refine Machine.FallsTo.nil ⟨σ, rfl, fun _ _ => rfl, fun _ hj => absurd hj (Nat.not_lt_zero _),
      hmem⟩
  | cons t rest ih =>
    intro k i venv st xs σ s bl0 hi_cap hi_σ htup hmem
    change Val (ty0ToTy t) × Tup Val (ty0ListToTy rest) at xs
    rcases xs with ⟨x, restX⟩
    dsimp only [tupAbiHolds0] at htup
    have hi_lt6 : i.toNat < 6 := by simp only [List.length_cons] at hi_cap; omega
    have hi_ltσ : i.toNat < σ.length := by simp only [List.length_cons] at hi_σ; omega
    have hi1 : (i + 1).toNat = i.toNat + 1 := u32_add1_toNat7 (by omega)
    let st10 := bindOneEntryArg0 i t { st with revDirs := [] }
    have hacc := bindEntryArgs0_acc rest (i + 1) (st.nextVid :: venv) st10
    dsimp only at hacc
    have hst10_rev :
        st10.revDirs =
          emitSlotMem0 false (abiRegAt0 false i) i [] ++
            emitCanon0 (tyWidth0 t) (abiRegAt0 false i) [] := by
      dsimp only [st10, bindOneEntryArg0]
      exact (emitSlotMem0_acc false (abiRegAt0 false i) i _).1
    have hbl_eq :
        bl0.st.revDirs =
          (bindEntryArgs0 rest (i + 1) (st.nextVid :: venv)
            { st10 with revDirs := [] }).st.revDirs ++ st10.revDirs := by
      dsimp only [bl0, bindEntryArgs0]; rw [hacc.2.2.2.2.1]
    have hprog_eq :
        toAmd64Program symName (emitFwd0 bl0.st.revDirs) =
          (toAmd64Program symName (emitFwd0 (emitCanon0 (tyWidth0 t) (abiRegAt0 false i) [])) ++
            toAmd64Program symName (emitFwd0 (emitSlotMem0 false (abiRegAt0 false i) i []))) ++
          toAmd64Program symName (emitFwd0
            (bindEntryArgs0 rest (i + 1) (st.nextVid :: venv)
              { st10 with revDirs := [] }).st.revDirs) := by
      rw [hbl_eq, hst10_rev, emitFwd0_append, emitFwd0_append, toAmd64Program_append,
        toAmd64Program_append, List.append_assoc]
    have hreg0 : s.regs.get64 (abiRegAt0 false i) = toCanon64 t x := by
      simpa [UInt32.ofNat_toNat] using htup.1
    have hcan_spec :
        x64ScalarMach.FallsTo x64CondReads h k
          (toAmd64Program symName (emitFwd0 (emitCanon0 (tyWidth0 t) (abiRegAt0 false i) [])))
          [abiRegAt0 false i] [] maskNone s
          (fun s1 => s1.regs.get64 (abiRegAt0 false i) = toCanon64 t x ∧ s1.dmem = s.dmem) post :=
      emitCanon0_ty_spec (symName := symName) (h := h) (k := k) t (abiRegAt0 false i)
        (by rw [hreg0]; exact toCanon64_toGprHolds t x)
    have hone :
        x64ScalarMach.FallsTo x64CondReads h k
          (toAmd64Program symName (emitFwd0 (emitCanon0 (tyWidth0 t) (abiRegAt0 false i) [])) ++
            toAmd64Program symName (emitFwd0 (emitSlotMem0 false (abiRegAt0 false i) i [])))
          [abiRegAt0 false i, .r10] [] maskNone s
          (fun s2 =>
            tupAbiHolds0 s2 false (i + 1).toNat rest restX ∧
            (s2.dmem =⋆ array64 (s2.regs.get64 .rsp) (σ.set i.toNat (toCanon64 t x)) ⋆ G))
          post := by
      have hc12 :
          x64ScalarMach.FallsTo x64CondReads h k
            (toAmd64Program symName (emitFwd0 (emitCanon0 (tyWidth0 t) (abiRegAt0 false i) [])) ++
              toAmd64Program symName (emitFwd0 (emitSlotMem0 false (abiRegAt0 false i) i [])))
            ([abiRegAt0 false i] ++ [.r10]) ([] ++ []) (maskNone ||| maskNone) s
            (fun s2 =>
              tupAbiHolds0 s2 false (i + 1).toNat rest restX ∧
              (s2.dmem =⋆ array64 (s2.regs.get64 .rsp) (σ.set i.toNat (toCanon64 t x)) ⋆ G))
            post :=
        Machine.FallsTo.comp hcan_spec fun s1 ⟨hr1, hm1⟩ hfr1 => by
          have hrsp1 : s1.regs.get64 .rsp = s.regs.get64 .rsp :=
            hfr1.1 .rsp fun hm => abiRegAt0_ne_rsp false i (List.mem_singleton.mp hm).symm
          have hmem1 : s1.dmem =⋆ array64 (s1.regs.get64 .rsp) σ ⋆ G := by
            rw [hm1, hrsp1]; exact hmem
          have htup1 : tupAbiHolds0 s1 false (i + 1).toNat rest restX := by
            rw [hi1]
            refine tupAbiHolds0_frame (fun r hr => hfr1.1 r hr) (fun j hj hm => ?_) htup.2
            have hj_eq := List.mem_singleton.mp hm
            have hj_lt : i.toNat + 1 + j < 6 := by simp only [List.length_cons] at hi_cap; omega
            have hne := abiRegAt0_inj_lt false hi_lt6 hj_lt
              (by simpa [UInt32.ofNat_toNat] using hj_eq.symm)
            omega
          have hst1 := emitSlotMem0_st_spec (symName := symName) (h := h)
            (k := k + (toAmd64Program symName (emitFwd0
              (emitCanon0 (tyWidth0 t) (abiRegAt0 false i) []))).length)
            (post := post) (abiRegAt0 false i) (abiRegAt0_ne_r10 false i) i hi_ltσ hmem1
          refine Machine.FallsTo.conseq hst1 fun s2 hm2 hfr2 => ?_
          have hrsp2 : s2.regs.get64 .rsp = s1.regs.get64 .rsp := hfr2.1 .rsp (by simp)
          refine ⟨tupAbiHolds0_frame (fun r hr => hfr2.1 r hr)
              (fun j _ hm => abiRegAt0_ne_r10 false _ (List.mem_singleton.mp hm)) htup1, ?_⟩
          rw [← hrsp2, hr1] at hm2
          exact hm2
      exact Machine.FallsTo.weaken hc12
        (fun r hr => by simp at hr ⊢; exact hr) (fun _ hv => nomatch hv) (by decide)
    rw [hprog_eq]
    have hcomp := Machine.FallsTo.comp hone fun s2 ⟨htup2, hmem2⟩ _ =>
      ih (k + (toAmd64Program symName (emitFwd0 (emitCanon0 (tyWidth0 t) (abiRegAt0 false i) [])) ++
        toAmd64Program symName (emitFwd0 (emitSlotMem0 false (abiRegAt0 false i) i []))).length)
        (i + 1) (st.nextVid :: venv) st10 restX (σ.set i.toNat (toCanon64 t x)) s2
        (by simp only [List.length_cons] at hi_cap; rw [hi1]; omega)
        (by simp only [List.length_cons, List.length_set] at hi_σ ⊢; rw [hi1]; omega)
        htup2 hmem2
    have hwk :
        x64ScalarMach.FallsTo x64CondReads h k
          ((toAmd64Program symName (emitFwd0 (emitCanon0 (tyWidth0 t) (abiRegAt0 false i) [])) ++
              toAmd64Program symName (emitFwd0 (emitSlotMem0 false (abiRegAt0 false i) i []))) ++
            toAmd64Program symName (emitFwd0
              (bindEntryArgs0 rest (i + 1) (st.nextVid :: venv)
                { st10 with revDirs := [] }).st.revDirs))
          x64ScratchAndAbi [] maskNone s
          (fun s' =>
            ∃ (σ' : List (BitVec 64)) (hσ' : σ'.length = (σ.set i.toNat (toCanon64 t x)).length),
            (∀ q : Nat, ∀ hq : q < (i + 1).toNat,
              σ'[q]'(hσ' ▸ by simp only [List.length_set]; rw [hi1] at hq; omega) =
                (σ.set i.toNat (toCanon64 t x))[q]'(by
                  simp only [List.length_set]; rw [hi1] at hq; omega)) ∧
            (∀ (j : Nat) (hj : j < rest.length),
              σ'[(i + 1).toNat + j]'(hσ' ▸ by
                simp only [List.length_set]; simp only [List.length_cons] at hi_σ
                rw [hi1]; omega) =
                (tupToCanon64s rest restX)[j]'(by rw [tupToCanon64s_length]; exact hj)) ∧
            (s'.dmem =⋆ array64 (s'.regs.get64 .rsp) σ' ⋆ G)) post :=
      Machine.FallsTo.weaken hcomp (fun r hr => by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with (rfl | rfl) | hr2
        · exact abiRegAt0_mem_scratchAndAbi false i
        · simp [x64ScratchAndAbi]
        · exact hr2) (fun _ hv => nomatch hv) (by decide)
    refine Machine.FallsTo.conseq hwk fun s' ⟨σ', hσ'_len, hq_lt, hj_rest, hmem'⟩ _ => ?_
    refine ⟨σ', hσ'_len.trans List.length_set, fun q hq => ?_, fun j hj => ?_, hmem'⟩
    · have hne : q ≠ i.toNat := by omega
      exact (hq_lt q (by rw [hi1]; omega)).trans (by rw [List.getElem_set_ne (Ne.symm hne)])
    · cases j with
      | zero =>
        dsimp only [tupToCanon64s, List.getElem_cons_zero]
        simp only [Nat.add_zero]
        exact (hq_lt i.toNat (by rw [hi1]; omega)).trans (List.getElem_set_self ..)
      | succ k' =>
        have h' := hj_rest k' (Nat.lt_of_succ_lt_succ hj)
        have h2 : k' < (tupToCanon64s rest restX).length := by
          rw [tupToCanon64s_length]; exact Nat.lt_of_succ_lt_succ hj
        refine Eq.trans ?_ (tupToCanon64s_cons_getElem x restX k' _ h2).symm
        simpa only [hi1, Nat.add_assoc, Nat.add_comm 1 k'] using h'

theorem bindEntryArgs0_run_spec {symName : Sym0 → Sym} {h : Host} {G : Mem 64 → Prop}
    {post : MachineState → Prop} (ts : List Ty0) (k : Nat) (st : RegaSt0)
    (xs : Tup Val (ty0ListToTy ts)) (σ : List (BitVec 64)) (s : MachineData) (maxBd : Nat)
    (hcap : ts.length ≤ 6) (hvsz : st.vslot.size = st.nextVid.toNat) (hnv0 : st.nextVid = 0)
    (hmaxBd : ts.length ≤ maxBd) (hlt31 : maxBd < 2 ^ 31) (hms0 : st.maxSlots = 0)
    (hσ_len : ts.length ≤ σ.length)
    (hargs : x64ScalarTarget.ArgsIn xs s)
    (hmem : s.dmem =⋆ array64 (s.regs.get64 .rsp) σ ⋆ G) :
    let bl0 := bindEntryArgs0 ts 0 [] { st with revDirs := [] }
    x64ScalarMach.FallsTo x64CondReads h k
      (toAmd64Program symName (emitFwd0 bl0.st.revDirs)) x64ScratchAndAbi [] maskNone s
      (fun s' => ∃ (σ' : List (BitVec 64)) (hσ' : σ'.length = σ.length),
        (∀ (j : Nat) (hj : j < ts.length),
          σ'[(arrGetU0 bl0.st.vslot (UInt32.ofNat j)).toNat]'(hσ' ▸ by
            have hsp := bindEntryArgs0_spec ts 0 [] { st with revDirs := [] } maxBd
              hvsz hnv0 (by simpa using hmaxBd) hlt31 (by rw [hms0])
            have hj0 := hsp.2.2.2.2.2.2.2.2 j hj
            simp only [UInt32.toNat_zero, Nat.zero_add] at hj0
            rw [hj0, u32_toNat_ofNat7, Nat.mod_eq_of_lt (by omega)]
            omega) =
          (tupToCanon64s ts xs)[j]'(by rw [tupToCanon64s_length]; exact hj)) ∧
        (s'.dmem =⋆ array64 (s'.regs.get64 .rsp) σ' ⋆ G)) post := by
  have htup := (argsIn_ty0_iff hcap xs s).mp hargs
  have hrun := bindEntryArgs0_run_spec_aux (symName := symName) (h := h) (G := G) (post := post)
    ts k 0 [] st xs σ s (by simpa using hcap) (by simpa using hσ_len) htup hmem
  have hsp := bindEntryArgs0_spec ts 0 [] { st with revDirs := [] } maxBd
    hvsz hnv0 (by simpa using hmaxBd) hlt31 (by rw [hms0])
  refine Machine.FallsTo.conseq hrun fun s' ⟨σ', hσ'_len, _, hj_val, hmem'⟩ _ => ?_
  refine ⟨σ', hσ'_len, fun j hj => ?_, hmem'⟩
  have hslot_j := hsp.2.2.2.2.2.2.2.2 j hj
  simp only [UInt32.toNat_zero, Nat.zero_add] at hslot_j
  have heq_toNat : (arrGetU0 (bindEntryArgs0 ts 0 [] { st with revDirs := [] }).st.vslot
      (UInt32.ofNat j)).toNat = j := by
    rw [hslot_j, u32_toNat_ofNat7, Nat.mod_eq_of_lt (by omega)]
  have hj' := hj_val j hj
  simp only [UInt32.toNat_zero, Nat.zero_add] at hj'
  simpa only [heq_toNat] using hj'

end LeanQbe.T.Bootstrap0
