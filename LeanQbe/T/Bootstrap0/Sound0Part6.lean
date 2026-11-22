module

public import LeanQbe.T.Bootstrap0.Sound0Part5

/-!
# Bootstrap Stage B (`Sound0Part6`): `astUses0` & Lockstep `PrePass0` ↔ `Rega0`

Establishes:
1. Total subtree occurrence counts (`astUses0`), congruence (`astUses0_congr`), and exact
   zero/spine-equivalence for non-escaped variables (`preRunAux0_no_esc_uses`,
   `compileFnPre0_no_esc_uses`).
2. `SlotPoolInv0` & step specifications for `allocSlot0`, `releaseArg0`, `releaseArgs0`,
   `relNodeArgs0`, `bindOneSlot0`, `bindRetsN0`, `bindEntryArgs0`, `slotsOfVids0`, and
   `bindBlockParams0`.
3. Full lockstep `PrePass0` ↔ `Rega0` worklist invariant (`LblInfo0`, `LiveInTask0`, `TaskSlotOk0`,
   `RegaStepInv0`, `regaRunAux0_lockstep`, `compileFn0_maxSlots_lt`) showing `compileFn0`
   never overflows `UInt32` slot/vid/label bounds and preserves distinctness of live, free, and
   `.group` block target slots under `fn.okGuardsFull = true`
   (x64-only `Compiler0` verification targeting `LeanQbe.T.Amd64.ScalarTarg` via `Sound0Part1`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Bootstrap0

open LeanQbe.T

private theorem u32_ext6 {a b : UInt32} (h : a.toNat = b.toNat) : a = b :=
  UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)

private theorem u32_toNat_ofNat6 (n : Nat) : (UInt32.ofNat n).toNat = n % 2 ^ 32 := by
  rw [← UInt32.toNat_toBitVec]; exact BitVec.toNat_ofNat n 32

private theorem u32_sub1_toNat6 {x : UInt32} (hx : 0 < x.toNat) :
    (x - 1).toNat = x.toNat - 1 := by
  refine UInt32.toNat_sub_of_le x 1 ?_
  exact UInt32.le_iff_toNat_le.mpr (by rw [UInt32.toNat_one]; exact hx)

private theorem u32_add1_toNat6 {x : UInt32} (hx : x.toNat + 1 < 2 ^ 32) :
    (x + 1).toNat = x.toNat + 1 := by
  rw [UInt32.toNat_add, UInt32.toNat_one, Nat.mod_eq_of_lt hx]

private theorem u32_add_assoc6 (a b c : UInt32) : (a + b) + c = a + (b + c) := by
  apply u32_ext6
  rw [UInt32.toNat_add, UInt32.toNat_add, UInt32.toNat_add, UInt32.toNat_add,
    Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]

private theorem u32_add_zero6 (a : UInt32) : a + UInt32.ofNat 0 = a := by
  apply u32_ext6
  rw [UInt32.toNat_add, u32_toNat_ofNat6]
  simp [Nat.mod_eq_of_lt (UInt32.toNat_lt a)]

private theorem u32_eq_add_of_toNat6 {a b : UInt32} {m : Nat} (h : b.toNat = a.toNat + m)
    (hlt : a.toNat + m < 2 ^ 32) : b = a + UInt32.ofNat m := by
  apply u32_ext6
  rw [h, UInt32.toNat_add, u32_toNat_ofNat6,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hlt), Nat.mod_eq_of_lt hlt]

private theorem u32_add_ofNat_lt6 {a : UInt32} {m : Nat} (hlt : a.toNat + m < 2 ^ 32) :
    (a + UInt32.ofNat m).toNat = a.toNat + m := by
  rw [UInt32.toNat_add, u32_toNat_ofNat6,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hlt), Nat.mod_eq_of_lt hlt]

private theorem arrGetU0_of_lt6 (arr : Array Nat) (i : UInt32)
    (hlt : arr.getD i.toNat 0 < 2 ^ 32) :
    (arrGetU0 arr i).toNat = arr.getD i.toNat 0 := by
  dsimp only [arrGetU0]; rw [u32_toNat_ofNat6, Nat.mod_eq_of_lt hlt]

private theorem arrSetU0_size6 (arr : Array Nat) (i v : UInt32) :
    (arrSetU0 arr i v).size = arr.size := by
  dsimp only [arrSetU0, Array.set!]; exact Array.size_setIfInBounds

private theorem arrSetU0_getD6 (arr : Array Nat) (i v : UInt32) (hi : i.toNat < arr.size)
    (j : Nat) :
    (arrSetU0 arr i v).getD j 0 = if j = i.toNat then v.toNat else arr.getD j 0 := by
  dsimp only [arrSetU0, Array.set!, Array.getD]
  by_cases hj : j < arr.size
  · have hlt : j < (arr.setIfInBounds i.toNat v.toNat).size := by
      rw [Array.size_setIfInBounds]; exact hj
    simp only [hj, hlt, ↓reduceDIte]
    change (arr.setIfInBounds i.toNat v.toNat)[j] = if j = i.toNat then v.toNat else arr[j]
    rw [Array.getElem_setIfInBounds]
    · split <;> rename_i heq
      · subst heq; simp
      · simp [Ne.symm heq]
    · exact hj
  · have hge : ¬ j < (arr.setIfInBounds i.toNat v.toNat).size := by
      rw [Array.size_setIfInBounds]; exact hj
    simp only [hj, hge, ↓reduceDIte]
    have hne : j ≠ i.toNat := fun h => hj (h ▸ hi)
    simp [hne]

private theorem arrPush_getD6 {α : Type} (arr : Array α) (x d : α) (j : Nat) :
    (arr.push x).getD j d =
      if j < arr.size then arr.getD j d else if j = arr.size then x else d := by
  dsimp only [Array.getD]
  by_cases hj : j < arr.size
  · have hlt : j < (arr.push x).size := by rw [Array.size_push]; omega
    simp only [hj, hlt, ↓reduceDIte]; exact Array.getElem_push_lt hj
  · by_cases heq : j = arr.size
    · subst heq
      have hlt : arr.size < (arr.push x).size := by rw [Array.size_push]; omega
      simp only [Nat.lt_irrefl, hlt, ↓reduceDIte]; exact Array.getElem_push_eq
    · have hge : ¬ j < (arr.push x).size := by rw [Array.size_push]; omega
      simp only [hj, heq, hge, ↓reduceDIte, ite_false]

private theorem listGetD_mem6 {α : Type} :
    ∀ {xs : List α} {i : Nat} {d : α}, i < xs.length → xs.getD i d ∈ xs
  | [], _, _, hi => absurd hi (Nat.not_lt_zero _)
  | _ :: _, 0, _, _ => List.mem_cons_self
  | _ :: xs, _ + 1, _, hi =>
    List.mem_cons_of_mem _ (listGetD_mem6 (xs := xs) (Nat.lt_of_succ_lt_succ hi))

theorem u32Max0_toNat (a b : UInt32) :
    (u32Max0 a b).toNat = max a.toNat b.toNat := by
  dsimp only [u32Max0]; split <;> rename_i h
  · have hlt : a.toNat < b.toNat := by simpa [UInt32.lt_iff_toNat_lt] using decide_eq_true_eq.mp h
    omega
  · have hge : b.toNat ≤ a.toNat := by
      have hn : ¬ (a < b) := fun hl => h (decide_eq_true hl)
      rw [UInt32.lt_iff_toNat_lt] at hn; omega
    omega

/-! ## 1. Full Subtree Occurrence Counts (`astUses0`) & Non-Escaped Zero Lemma -/

mutual
/-- Total operand occurrences of `vid` across the entire `TFlat0` subtree (including branches). -/
@[expose] def astUses0 (vid : UInt32) (venv : List UInt32) (nextVid : UInt32) : TFlat0 → Nat
  | .let1 _ args k =>
    argsUses0 vid venv args + astUses0 vid (pushFreshVids0 1 nextVid venv) (nextVid + 1) k
  | .let2Umulw64 a b k =>
    argUses0 vid venv a + argUses0 vid venv b +
      astUses0 vid (pushFreshVids0 2 nextVid venv) (nextVid + 2) k
  | .load _ addr k =>
    argUses0 vid venv addr + astUses0 vid (pushFreshVids0 1 nextVid venv) (nextVid + 1) k
  | .store _ val addr k =>
    argUses0 vid venv val + argUses0 vid venv addr + astUses0 vid venv nextVid k
  | .call _ _ bs args k =>
    argsUses0 vid venv args +
      astUses0 vid (pushFreshVids0 bs.length nextVid venv)
        (nextVid + UInt32.ofNat bs.length) k
  | .jnz c t e =>
    argUses0 vid venv c + astUses0 vid venv nextVid t + astUses0 vid venv nextVid e
  | .group bodies k =>
    blocksAstUses0 vid venv nextVid bodies + astUses0 vid venv nextVid k
  | node => nodeArgsUses0 vid venv node

/-- Total operand occurrences of `vid` across `.group` block bodies. -/
@[expose] def blocksAstUses0 (vid : UInt32) (venv : List UInt32) (nextVid : UInt32) :
    List (List Ty0 × TFlat0) → Nat
  | [] => 0
  | (pts, b) :: rest =>
    astUses0 vid (pushFreshVids0 pts.length nextVid venv)
      (nextVid + UInt32.ofNat pts.length) b +
      blocksAstUses0 vid venv (nextVid + UInt32.ofNat pts.length) rest
end

private theorem nodeArgsUses0_congr6 {vid : UInt32} {v₁ v₂ : List UInt32}
    (h : AgreeBelow0 vid v₁ v₂) (n : TFlat0) :
    nodeArgsUses0 vid v₁ n = nodeArgsUses0 vid v₂ n := by
  have ha : ∀ a, argUses0 vid v₁ a = argUses0 vid v₂ a := fun a => by
    cases a with | var idx => simp only [argUses0, h idx] | _ => rfl
  have has : ∀ args, argsUses0 vid v₁ args = argsUses0 vid v₂ args := fun args => by
    induction args with | nil => rfl | cons a r ih => dsimp only [argsUses0]; rw [ha a, ih]
  cases n with
  | let1 _ args _ | call _ _ _ args _ | tailCall _ _ args
  | jump _ args | ret args | exit _ _ args => exact has args
  | let2Umulw64 a b _ | store _ a b _ => dsimp only [nodeArgsUses0]; rw [ha a, ha b]
  | load _ a _ | jnz a _ _ => exact ha a
  | hlt | group _ _ => rfl

mutual
theorem astUses0_congr :
    ∀ (n : TFlat0) (vid nv₁ nv₂ : UInt32) (v₁ v₂ : List UInt32),
      vid.toNat < nv₁.toNat → vid.toNat < nv₂.toNat →
      nv₁.toNat + binderCount0 n < 2 ^ 32 → nv₂.toNat + binderCount0 n < 2 ^ 32 →
      AgreeBelow0 vid v₁ v₂ →
      astUses0 vid v₁ nv₁ n = astUses0 vid v₂ nv₂ n
  | .let1 op args k, vid, nv₁, nv₂, v₁, v₂, h1, h2, hb1, hb2, hag => by
    dsimp only [binderCount0, astUses0] at hb1 hb2 ⊢
    have hu := nodeArgsUses0_congr6 hag (.let1 op args k); dsimp only [nodeArgsUses0] at hu
    have hag' := agreeBelow0_pushFreshVids0 1 vid nv₁ nv₂ v₁ v₂ h1 h2 (by omega) (by omega) hag
    have h1' : (nv₁ + 1).toNat = nv₁.toNat + 1 := u32_add1_toNat6 (by omega)
    have h2' : (nv₂ + 1).toNat = nv₂.toNat + 1 := u32_add1_toNat6 (by omega)
    rw [hu, astUses0_congr k vid (nv₁ + 1) (nv₂ + 1) _ _
      (by omega) (by omega) (by omega) (by omega) hag']
  | .let2Umulw64 a b k, vid, nv₁, nv₂, v₁, v₂, h1, h2, hb1, hb2, hag => by
    dsimp only [binderCount0, astUses0] at hb1 hb2 ⊢
    have hu := nodeArgsUses0_congr6 hag (.let2Umulw64 a b k); dsimp only [nodeArgsUses0] at hu
    have hag' := agreeBelow0_pushFreshVids0 2 vid nv₁ nv₂ v₁ v₂ h1 h2 (by omega) (by omega) hag
    have h21 : (nv₁ + 2).toNat = nv₁.toNat + 2 := u32_add_ofNat_lt6 (m := 2) (by omega)
    have h22 : (nv₂ + 2).toNat = nv₂.toNat + 2 := u32_add_ofNat_lt6 (m := 2) (by omega)
    rw [hu, astUses0_congr k vid (nv₁ + 2) (nv₂ + 2) _ _
      (by omega) (by omega) (by omega) (by omega) hag']
  | .load t addr k, vid, nv₁, nv₂, v₁, v₂, h1, h2, hb1, hb2, hag => by
    dsimp only [binderCount0, astUses0] at hb1 hb2 ⊢
    have hu := nodeArgsUses0_congr6 hag (.load t addr k); dsimp only [nodeArgsUses0] at hu
    have hag' := agreeBelow0_pushFreshVids0 1 vid nv₁ nv₂ v₁ v₂ h1 h2 (by omega) (by omega) hag
    have h1' : (nv₁ + 1).toNat = nv₁.toNat + 1 := u32_add1_toNat6 (by omega)
    have h2' : (nv₂ + 1).toNat = nv₂.toNat + 1 := u32_add1_toNat6 (by omega)
    rw [hu, astUses0_congr k vid (nv₁ + 1) (nv₂ + 1) _ _
      (by omega) (by omega) (by omega) (by omega) hag']
  | .store t val addr k, vid, nv₁, nv₂, v₁, v₂, h1, h2, hb1, hb2, hag => by
    dsimp only [binderCount0, astUses0] at hb1 hb2 ⊢
    have hu := nodeArgsUses0_congr6 hag (.store t val addr k); dsimp only [nodeArgsUses0] at hu
    rw [hu, astUses0_congr k vid nv₁ nv₂ v₁ v₂ h1 h2 hb1 hb2 hag]
  | .call fnSym as bs args k, vid, nv₁, nv₂, v₁, v₂, h1, h2, hb1, hb2, hag => by
    dsimp only [binderCount0, astUses0] at hb1 hb2 ⊢
    have hu := nodeArgsUses0_congr6 hag (.call fnSym as bs args k); dsimp only [nodeArgsUses0] at hu
    have hag' := agreeBelow0_pushFreshVids0 bs.length vid nv₁ nv₂ v₁ v₂ h1 h2
      (by omega) (by omega) hag
    have hb1' : (nv₁ + UInt32.ofNat bs.length).toNat = nv₁.toNat + bs.length :=
      u32_add_ofNat_lt6 (by omega)
    have hb2' : (nv₂ + UInt32.ofNat bs.length).toNat = nv₂.toNat + bs.length :=
      u32_add_ofNat_lt6 (by omega)
    rw [hu, astUses0_congr k vid (nv₁ + UInt32.ofNat bs.length) (nv₂ + UInt32.ofNat bs.length)
      (pushFreshVids0 bs.length nv₁ v₁) (pushFreshVids0 bs.length nv₂ v₂)
      (by omega) (by omega) (by omega) (by omega) hag']
  | .jnz c t e, vid, nv₁, nv₂, v₁, v₂, h1, h2, hb1, hb2, hag => by
    dsimp only [binderCount0, astUses0] at hb1 hb2 ⊢
    have hu := nodeArgsUses0_congr6 hag (.jnz c t e); dsimp only [nodeArgsUses0] at hu
    rw [hu, astUses0_congr t vid nv₁ nv₂ v₁ v₂ h1 h2 (by omega) (by omega) hag,
      astUses0_congr e vid nv₁ nv₂ v₁ v₂ h1 h2 (by omega) (by omega) hag]
  | .group bodies k, vid, nv₁, nv₂, v₁, v₂, h1, h2, hb1, hb2, hag => by
    dsimp only [binderCount0, astUses0] at hb1 hb2 ⊢
    rw [blocksAstUses0_congr bodies vid nv₁ nv₂ v₁ v₂ h1 h2 (by omega) (by omega) hag,
      astUses0_congr k vid nv₁ nv₂ v₁ v₂ h1 h2 (by omega) (by omega) hag]
  | .tailCall _ _ _, _, _, _, _, _, _, _, _, _, hag => by
    dsimp only [astUses0]; exact nodeArgsUses0_congr6 hag _
  | .jump _ _, _, _, _, _, _, _, _, _, _, hag => by
    dsimp only [astUses0]; exact nodeArgsUses0_congr6 hag _
  | .ret _, _, _, _, _, _, _, _, _, _, hag => by
    dsimp only [astUses0]; exact nodeArgsUses0_congr6 hag _
  | .exit _ _ _, _, _, _, _, _, _, _, _, _, hag => by
    dsimp only [astUses0]; exact nodeArgsUses0_congr6 hag _
  | .hlt, _, _, _, _, _, _, _, _, _, hag => by
    dsimp only [astUses0]; exact nodeArgsUses0_congr6 hag _

theorem blocksAstUses0_congr :
    ∀ (bs : List (List Ty0 × TFlat0)) (vid nv₁ nv₂ : UInt32) (v₁ v₂ : List UInt32),
      vid.toNat < nv₁.toNat → vid.toNat < nv₂.toNat →
      nv₁.toNat + blocksBinderCount0 bs < 2 ^ 32 →
      nv₂.toNat + blocksBinderCount0 bs < 2 ^ 32 →
      AgreeBelow0 vid v₁ v₂ →
      blocksAstUses0 vid v₁ nv₁ bs = blocksAstUses0 vid v₂ nv₂ bs
  | [], _, _, _, _, _, _, _, _, _, _ => by dsimp only [blocksAstUses0]
  | (pts, b) :: rest, vid, nv₁, nv₂, v₁, v₂, h1, h2, hb1, hb2, hag => by
    dsimp only [blocksBinderCount0, blocksAstUses0] at hb1 hb2 ⊢
    have hag' := agreeBelow0_pushFreshVids0 pts.length vid nv₁ nv₂ v₁ v₂ h1 h2
      (by omega) (by omega) hag
    have h1' : (nv₁ + UInt32.ofNat pts.length).toNat = nv₁.toNat + pts.length :=
      u32_add_ofNat_lt6 (by omega)
    have h2' : (nv₂ + UInt32.ofNat pts.length).toNat = nv₂.toNat + pts.length :=
      u32_add_ofNat_lt6 (by omega)
    rw [astUses0_congr b vid (nv₁ + UInt32.ofNat pts.length) (nv₂ + UInt32.ofNat pts.length)
        (pushFreshVids0 pts.length nv₁ v₁) (pushFreshVids0 pts.length nv₂ v₂)
        (by omega) (by omega) (by omega) (by omega) hag',
      blocksAstUses0_congr rest vid (nv₁ + UInt32.ofNat pts.length)
        (nv₂ + UInt32.ofNat pts.length) v₁ v₂ (by omega) (by omega) (by omega) (by omega) hag]
end

theorem astUses0_lin (vid : UInt32) (venv : List UInt32) (nv : UInt32)
    {n : TFlat0} (hlin : isTerm0 n = false)
    (hnj : ∀ c t e, n ≠ .jnz c t e) (hng : ∀ bs k, n ≠ .group bs k)
    (hfit : n.sigLensFitU32 = true) :
    astUses0 vid venv nv n =
      nodeArgsUses0 vid venv n +
        astUses0 vid (pushFreshVids0 (linCnt0 n).toNat nv venv)
          (nv + UInt32.ofNat (linCnt0 n).toNat) (linK0 n) := by
  cases n with
  | let1 _ _ _ | let2Umulw64 _ _ _ | load _ _ _ => rfl
  | store _ _ _ _ =>
    dsimp only [astUses0, linCnt0, linK0, nodeArgsUses0, pushFreshVids0]
    rw [UInt32.toNat_zero, u32_add_zero6]; rfl
  | call _ _ bs _ _ =>
    dsimp only [TFlat0.sigLensFitU32, listLenFitsU32] at hfit
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hfit
    dsimp only [astUses0, linCnt0, linK0, nodeArgsUses0]
    rw [tyLenU0_eq_of_lt hfit.1.2]
  | jnz _ _ _ => exact absurd rfl (hnj _ _ _)
  | group _ _ => exact absurd rfl (hng _ _)
  | tailCall _ _ _ | jump _ _ | ret _ | exit _ _ _ | hlt => simp [isTerm0] at hlin

theorem spineUses0_le_astUses0 :
    ∀ (n : TFlat0) (vid : UInt32) (venv : List UInt32) (nv : UInt32),
      spineUses0 vid venv nv n ≤ astUses0 vid venv nv n
  | .let1 _ args k, vid, venv, nv => by
    have := spineUses0_le_astUses0 k vid (pushFreshVids0 1 nv venv) (nv + 1)
    dsimp only [spineUses0, astUses0]; omega
  | .let2Umulw64 a b k, vid, venv, nv => by
    have := spineUses0_le_astUses0 k vid (pushFreshVids0 2 nv venv) (nv + 2)
    dsimp only [spineUses0, astUses0]; omega
  | .load _ addr k, vid, venv, nv => by
    have := spineUses0_le_astUses0 k vid (pushFreshVids0 1 nv venv) (nv + 1)
    dsimp only [spineUses0, astUses0]; omega
  | .store _ val addr k, vid, venv, nv => by
    have := spineUses0_le_astUses0 k vid venv nv
    dsimp only [spineUses0, astUses0]; omega
  | .call _ _ bs args k, vid, venv, nv => by
    have := spineUses0_le_astUses0 k vid (pushFreshVids0 bs.length nv venv)
      (nv + UInt32.ofNat bs.length)
    dsimp only [spineUses0, astUses0]; omega
  | .jnz c t e, vid, venv, nv => by
    dsimp only [spineUses0, astUses0, nodeArgsUses0]; omega
  | .group bodies k, vid, venv, nv => by
    dsimp only [spineUses0, astUses0, nodeArgsUses0]; exact Nat.zero_le _
  | .tailCall _ _ _, _, _, _ | .jump _ _, _, _, _ | .ret _, _, _, _
  | .exit _ _ _, _, _, _ | .hlt, _, _, _ => by
    dsimp only [spineUses0, astUses0]; exact Nat.le_refl _

private theorem binderCount0_le_work_of_mem {p : PreItem0} :
    ∀ {xs : List PreItem0}, p ∈ xs → binderCount0 p.node ≤ workBinderCount0 (xs.map PreItem0.node)
  | _ :: _, .head _ => by rw [List.map_cons]; dsimp only [workBinderCount0]; omega
  | _ :: _, .tail _ h => by
    have := binderCount0_le_work_of_mem h
    rw [List.map_cons]; dsimp only [workBinderCount0]; omega

theorem argUses0_eq_one_of_eq {vid : UInt32} {venv : List UInt32} {idx : UInt32}
    (h : listGetU32 venv idx = vid) : argUses0 vid venv (.var idx) = 1 := by
  simp [argUses0, h]

theorem nodeArgsUses0_zero_of_astZero {vid : UInt32} {venv : List UInt32} {nv : UInt32}
    {n : TFlat0} (h : astUses0 vid venv nv n = 0) :
    nodeArgsUses0 vid venv n = 0 := by
  have h1 := spineUses0_le_astUses0 n vid venv nv
  have h2 : nodeArgsUses0 vid venv n ≤ spineUses0 vid venv nv n := by
    cases n <;> (dsimp only [spineUses0, nodeArgsUses0]; omega)
  omega

theorem preRunAux0_no_esc_uses (ctx : LegalCtx0) :
    ∀ (N : Nat) (fuel nextSc : UInt32) (st : PreSt0) (work : List PreItem0),
      workNodeCount0 (work.map PreItem0.node) = N →
      N ≤ fuel.toNat →
      PreWorkInv0 ctx nextSc st work →
      let r := preRunAux0 fuel nextSc st work
      ∀ v < st.nextVid.toNat, r.2.escaped.getD v 0 = 0 →
        ∀ p ∈ work,
          if p.scope.toNat = st.defScope.getD v 0 then
            astUses0 (UInt32.ofNat v) p.venv st.nextVid p.node =
              spineUses0 (UInt32.ofNat v) p.venv st.nextVid p.node
          else
            astUses0 (UInt32.ofNat v) p.venv st.nextVid p.node = 0 := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro fuel nextSc st work hN hle hinv
    dsimp only
    cases work with
    | nil => intro _ _ _ _ hp; simp at hp
    | cons cur rest =>
      have hpos : 0 < N := by
        rw [← hN, List.map_cons]; dsimp only [workNodeCount0]
        have := nodeCount0_pos cur.node; omega
      have hfne : fuel ≠ 0 := fun h => by
        have := congrArg UInt32.toNat h; simp at this; omega
      have hN1 : (fuel - 1).toNat = fuel.toNat - 1 := u32_sub1_toNat6 (by omega)
      have hcur_ok := hinv.items_ok cur List.mem_cons_self
      obtain ⟨vT, lT, hvlen, hvlt, hwf, hfit, hsbg, hnb⟩ := hcur_ok
      have hnd_vars : nodeArgsInVenv0 cur.venv.length cur.node := by
        rw [hvlen]; exact wfNode0_nodeArgsInVenv0 hwf
      have hmax_u : ∀ v < st.nextVid.toNat, st.uses.getD v 0 + argCount0 cur.node < 2 ^ 32 := by
        intro v hv
        have hb := hinv.uses_bound v hv
        rw [List.map_cons] at hb; dsimp only [workArgCount0] at hb; omega
      have hds_lt : ∀ v < st.nextVid.toNat, st.defScope.getD v 0 < 2 ^ 32 := fun v hv =>
        Nat.lt_trans (hinv.defScope_lt v hv) (UInt32.toNat_lt nextSc)
      have hst1 := preNoteNode0_spec cur.scope cur.venv cur.node st hinv.defScope_sz
        hinv.uses_sz hinv.escaped_sz hvlt hnd_vars hmax_u hds_lt hinv.escaped_bit
      dsimp only at hst1
      let st1 := preNoteNode0 cur.scope cur.venv cur.node st
      let out := preStepPush0 cur st1 nextSc rest
      have hcnt : workNodeCount0 (out.work.map PreItem0.node) + 1 = N := by
        rw [← hN]
        simpa only [out, List.map_cons] using preWorkNodeCount0_children cur st1 nextSc rest
      have hlt_N : workNodeCount0 (out.work.map PreItem0.node) < N := by omega
      have hdef_out : preRunAux0 fuel nextSc st (cur :: rest) =
          preRunAux0 (fuel - 1) out.nextScope out.st out.work :=
        preRunAux0_succ hfne nextSc st cur rest
      have hrest_scopes : ∀ p ∈ rest, p.scope ≠ cur.scope := by
        have hnd := hinv.scopes_nodup
        simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
        intro p hp he; exact hnd.1 p hp he
      have hrest_nodup : (rest.map PreItem0.scope).Nodup := by
        have hnd := hinv.scopes_nodup
        simp only [List.map_cons, List.nodup_cons] at hnd; exact hnd.2
      have hrest_lt : ∀ p ∈ rest, p.scope.toNat < nextSc.toNat := fun p hp =>
        hinv.scopes_lt p (List.mem_cons_of_mem _ hp)
      have hsc_cur_lt : cur.scope.toNat < nextSc.toNat := hinv.scopes_lt cur List.mem_cons_self
      have step_post : PreWorkInv0 ctx out.nextScope out.st out.work →
          (∀ v < st.nextVid.toNat, out.st.defScope.getD v 0 = st.defScope.getD v 0) →
          st.nextVid.toNat ≤ out.st.nextVid.toNat →
          (∀ v < st.nextVid.toNat, st1.escaped.getD v 0 = 1 → out.st.escaped.getD v 0 = 1) →
          ∀ v < st.nextVid.toNat,
            (preRunAux0 fuel nextSc st (cur :: rest)).2.escaped.getD v 0 = 0 →
            (cur.scope.toNat ≠ st.defScope.getD v 0 →
              nodeArgsUses0 (UInt32.ofNat v) cur.venv cur.node = 0) ∧
            ∀ q ∈ out.work,
              if q.scope.toNat = st.defScope.getD v 0 then
                astUses0 (UInt32.ofNat v) q.venv out.st.nextVid q.node =
                  spineUses0 (UInt32.ofNat v) q.venv out.st.nextVid q.node
              else
                astUses0 (UInt32.ofNat v) q.venv out.st.nextVid q.node = 0 := by
        intro hinv' hds_eq hnv_le hesc_mono v hv hre
        rw [hdef_out] at hre
        have hinv_r := preRunAux0_inv ctx (workNodeCount0 (out.work.map PreItem0.node))
          (fuel - 1) out.nextScope out.st out.work rfl (by omega) hinv'
        dsimp only at hinv_r
        have he_out_ne1 : out.st.escaped.getD v 0 ≠ 1 := fun he1 => by
          have := hinv_r.2.2.2.2.2.2.2.2.1 v (Nat.lt_of_lt_of_le hv hnv_le) he1
          rw [hre] at this; cases this
        have he_st1_ne1 : st1.escaped.getD v 0 ≠ 1 := fun he1 =>
          he_out_ne1 (hesc_mono v hv he1)
        have hih := ih (workNodeCount0 (out.work.map PreItem0.node)) hlt_N (fuel - 1)
          out.nextScope out.st out.work rfl (by omega) hinv'
        dsimp only at hih
        have hih_v := hih v (Nat.lt_of_lt_of_le hv hnv_le) hre
        refine ⟨fun hne => ?_, fun q hq => ?_⟩
        · have hv1 := hst1.2.2.2.2.2 v hv
          have hne' : ¬ (st.defScope.getD v 0 = cur.scope.toNat) := Ne.symm hne
          simp only [hne', ↓reduceIte] at hv1
          by_cases hpos_u : 0 < nodeArgsUses0 (UInt32.ofNat v) cur.venv cur.node
          · simp only [hpos_u, ↓reduceIte] at hv1
            exact absurd hv1.2 he_st1_ne1
          · omega
        · have hq' := hih_v q hq
          rwa [hds_eq v hv] at hq'
      have congr_nv : ∀ (p : PreItem0) (nv' : UInt32) (v : Nat),
          p ∈ cur :: rest → v < st.nextVid.toNat → st.nextVid.toNat ≤ nv'.toNat →
          nv'.toNat + binderCount0 p.node < 2 ^ 32 →
          astUses0 (UInt32.ofNat v) p.venv nv' p.node =
            astUses0 (UInt32.ofNat v) p.venv st.nextVid p.node ∧
          spineUses0 (UInt32.ofNat v) p.venv nv' p.node =
            spineUses0 (UInt32.ofNat v) p.venv st.nextVid p.node := by
        intro p nv' v hp hv hle_nv hbd_nv
        have hlt32 : (UInt32.ofNat v).toNat < st.nextVid.toNat := by
          rw [u32_toNat_ofNat6, Nat.mod_eq_of_lt (Nat.lt_trans hv (UInt32.toNat_lt _))]
          exact hv
        have hb_st : st.nextVid.toNat + binderCount0 p.node < 2 ^ 32 := by omega
        exact ⟨astUses0_congr p.node (UInt32.ofNat v) nv' st.nextVid p.venv p.venv
            (by omega) hlt32 hbd_nv hb_st (agreeBelow0_refl _ _),
          spineUses0_congr p.node (UInt32.ofNat v) nv' st.nextVid p.venv p.venv
            (by omega) hlt32 hbd_nv hb_st (agreeBelow0_refl _ _)⟩
      have term_case : isTerm0 cur.node = true →
          ∀ v < st.nextVid.toNat, (preRunAux0 fuel nextSc st (cur :: rest)).2.escaped.getD v 0 = 0 →
            ∀ p ∈ cur :: rest,
              if p.scope.toNat = st.defScope.getD v 0 then
                astUses0 (UInt32.ofNat v) p.venv st.nextVid p.node =
                  spineUses0 (UInt32.ofNat v) p.venv st.nextVid p.node
              else astUses0 (UInt32.ofNat v) p.venv st.nextVid p.node = 0 := by
        intro ht
        have hout : out = PreOut0.mk st1 nextSc rest := by
          dsimp only [out, preStepPush0]; simp [ht]
        have huses_b : ∀ v < st1.nextVid.toNat,
            st1.uses.getD v 0 + workArgCount0 (rest.map PreItem0.node) < 2 ^ 31 := by
          intro v hv; rw [hst1.1] at hv
          have hv1 := hst1.2.2.2.2.2 v hv
          have hau := nodeArgsUses0_le_argCount0 (UInt32.ofNat v) cur.venv cur.node
          have hb := hinv.uses_bound v hv
          rw [List.map_cons] at hb; dsimp only [workArgCount0] at hb
          split at hv1 <;> { rw [hv1.1]; omega }
        have hbc0 : binderCount0 cur.node = 0 := by
          cases hnd : cur.node <;> rw [hnd] at ht <;> simp only [isTerm0] at ht <;>
            first | (dsimp only [binderCount0]; done) | exact absurd ht Bool.false_ne_true
        have hinv' : PreWorkInv0 ctx out.nextScope out.st out.work := by
          rw [hout]; dsimp only
          refine ⟨hst1.1 ▸ hst1.2.1.symm ▸ hinv.defScope_sz,
            hst1.1 ▸ hst1.2.2.1, hst1.1 ▸ hst1.2.2.2.1,
            fun v hv => hst1.2.1 ▸ hinv.defScope_lt v (hst1.1 ▸ hv),
            fun v hv => hst1.2.2.2.2.1 v (hst1.1 ▸ hv),
            hrest_nodup, hrest_lt,
            fun p hp => hst1.1 ▸ hinv.items_ok p (List.mem_cons_of_mem _ hp),
            by rw [hst1.1]; have := hinv.nextVid_bound
               rw [List.map_cons] at this; dsimp only [workBinderCount0] at this
               rw [hbc0] at this; omega,
            by have hb := hinv.nextSc_bound; have := nodeCount0_pos cur.node
               rw [List.map_cons] at hb; dsimp only [workNodeCount0] at hb; omega,
            by have := hinv.argCount_bound
               rw [List.map_cons] at this; dsimp only [workArgCount0] at this; omega,
            huses_b⟩
        intro v hv hre p hp
        obtain ⟨hn_z, hrest_u⟩ := step_post hinv' (fun _ _ => by rw [hout, hst1.2.1])
          (by rw [hout, hst1.1]; exact Nat.le_refl _) (fun _ _ h => by rw [hout]; exact h) v hv hre
        rcases List.mem_cons.mp hp with rfl | hp'
        · have hsp_eq : astUses0 (UInt32.ofNat v) p.venv st.nextVid p.node =
              nodeArgsUses0 (UInt32.ofNat v) p.venv p.node ∧
              spineUses0 (UInt32.ofNat v) p.venv st.nextVid p.node =
              nodeArgsUses0 (UInt32.ofNat v) p.venv p.node := by
            cases hnd : p.node <;> rw [hnd] at ht <;> simp only [isTerm0] at ht
            all_goals first
              | (dsimp only [astUses0, spineUses0, nodeArgsUses0]; exact ⟨rfl, rfl⟩)
              | cases ht
          split <;> rename_i hsc
          · rw [hsp_eq.1, hsp_eq.2]
          · rw [hsp_eq.1]; exact hn_z hsc
        · have hr := hrest_u p (by rw [hout]; exact hp')
          rw [hout, hst1.1] at hr
          exact hr
      cases hnd_eq : cur.node with
      | tailCall _ _ _ | jump _ _ | ret _ | exit _ _ _ | hlt =>
        exact term_case (by simp [isTerm0, hnd_eq])
      | jnz c t e =>
        have hout : out = PreOut0.mk st1 (nextSc + 2)
            (PreItem0.mk e cur.venv (nextSc + 1) ::
              PreItem0.mk t cur.venv nextSc :: rest) := by
          dsimp only [out, preStepPush0]; simp [isTerm0, preStepJnz0, hnd_eq]
        have hsc_ub_big : nextSc.toNat + 2 * (1 + nodeCount0 t + nodeCount0 e +
            workNodeCount0 (rest.map PreItem0.node)) < 2 ^ 31 := by
          have := hinv.nextSc_bound
          rw [List.map_cons, hnd_eq] at this
          dsimp only [workNodeCount0, nodeCount0] at this; exact this
        have hsc1 : (nextSc + 1).toNat = nextSc.toNat + 1 := u32_add1_toNat6 (by omega)
        have hsc2 : (nextSc + 2).toNat = nextSc.toNat + 2 := u32_add_ofNat_lt6 (m := 2) (by omega)
        rw [hnd_eq] at hwf hfit hsbg hnb
        cases hwf with | jnz _ hwft hwfe =>
        dsimp only [TFlat0.sigLensFitU32] at hfit; rw [Bool.and_eq_true] at hfit
        dsimp only [TFlat0.singleBlockGroups] at hsbg; rw [Bool.and_eq_true] at hsbg
        dsimp only [TFlat0.noNegBool] at hnb; rw [Bool.and_eq_true] at hnb
        have hnd_scopes : ([nextSc + 1, nextSc] ++ rest.map PreItem0.scope).Nodup := by
          refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, hrest_nodup⟩⟩
          · intro hm; rcases List.mem_cons.mp hm with h | h
            · have := congrArg UInt32.toNat h; omega
            · obtain ⟨p, hp, hpe⟩ := List.mem_map.mp h
              have := hrest_lt p hp; have := congrArg UInt32.toNat hpe; omega
          · intro hm; obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hm
            have := hrest_lt p hp; have := congrArg UInt32.toNat hpe; omega
        have huses_b : ∀ v < st1.nextVid.toNat,
            st1.uses.getD v 0 +
              (argCount0 e + (argCount0 t + workArgCount0 (rest.map PreItem0.node))) < 2 ^ 31 := by
          intro v hv; rw [hst1.1] at hv
          have hv1 := hst1.2.2.2.2.2 v hv
          have hau : argUses0 (UInt32.ofNat v) cur.venv c ≤ 1 := by
            cases c <;> simp [argUses0] <;> try split <;> omega
          have hb := hinv.uses_bound v hv
          rw [List.map_cons, hnd_eq] at hb; dsimp only [workArgCount0, argCount0] at hb
          split at hv1
          · rw [hv1.1]; dsimp only [nodeArgsUses0]; rw [hnd_eq]; dsimp only [nodeArgsUses0]; omega
          · rw [hv1.1]; omega
        have hinv' : PreWorkInv0 ctx out.nextScope out.st out.work := by
          rw [hout]; dsimp only
          refine ⟨hst1.1 ▸ hst1.2.1.symm ▸ hinv.defScope_sz,
            hst1.1 ▸ hst1.2.2.1, hst1.1 ▸ hst1.2.2.2.1,
            fun v hv => by have := hinv.defScope_lt v (hst1.1 ▸ hv); rw [hst1.2.1]; omega,
            fun v hv => hst1.2.2.2.2.1 v (hst1.1 ▸ hv),
            by simpa only [List.map_cons, List.cons_append, List.nil_append] using hnd_scopes,
            fun p hp => by
              rcases List.mem_cons.mp hp with rfl | hp1
              · dsimp only; omega
              · rcases List.mem_cons.mp hp1 with rfl | hp2
                · dsimp only; omega
                · have := hrest_lt p hp2; omega,
            fun p hp => by
              rw [hst1.1]; rcases List.mem_cons.mp hp with rfl | hp1
              · exact ⟨vT, lT, hvlen, hvlt, hwfe, hfit.2, hsbg.2, hnb.2⟩
              · rcases List.mem_cons.mp hp1 with rfl | hp2
                · exact ⟨vT, lT, hvlen, hvlt, hwft, hfit.1, hsbg.1, hnb.1⟩
                · exact hinv.items_ok p (List.mem_cons_of_mem _ hp2),
            by rw [hst1.1]; have := hinv.nextVid_bound
               rw [List.map_cons, hnd_eq] at this; simp only [List.map_cons]
               dsimp only [workBinderCount0, binderCount0] at this ⊢; omega,
            by have := hsc_ub_big; simp only [List.map_cons]
               dsimp only [workNodeCount0]; omega,
            by have := hinv.argCount_bound
               rw [List.map_cons, hnd_eq] at this; simp only [List.map_cons]
               dsimp only [workArgCount0, argCount0] at this ⊢; omega,
            by rw [List.map_cons]; dsimp only [workArgCount0]; exact huses_b⟩
        intro v hv hre p hp
        obtain ⟨hn_z, hrest_u⟩ := step_post hinv' (fun _ _ => by rw [hout, hst1.2.1])
          (by rw [hout, hst1.1]; exact Nat.le_refl _) (fun _ _ h => by rw [hout]; exact h) v hv hre
        rcases List.mem_cons.mp hp with rfl | hp'
        · have hdl := hinv.defScope_lt v hv
          have ht_u := hrest_u ⟨t, p.venv, nextSc⟩ (by rw [hout]; simp)
          have he_u := hrest_u ⟨e, p.venv, nextSc + 1⟩ (by rw [hout]; simp)
          have hnt : (nextSc : UInt32).toNat ≠ st.defScope.getD v 0 := by omega
          have hne : (nextSc + 1).toNat ≠ st.defScope.getD v 0 := by omega
          simp only [hnt, hne, ↓reduceIte, hout] at ht_u he_u
          rw [hst1.1] at ht_u he_u
          rw [hnd_eq]
          dsimp only [astUses0, spineUses0, nodeArgsUses0]
          rw [ht_u, he_u, Nat.add_zero]
          split <;> rename_i hsc
          · exact rfl
          · have hnu := hn_z hsc; rw [hnd_eq] at hnu; exact hnu
        · have hr := hrest_u p (by rw [hout]; simp [hp'])
          rw [hout, hst1.1] at hr; exact hr
      | group bodies k =>
        rw [hnd_eq] at hwf hfit hsbg hnb
        obtain ⟨hwfk, hfitk, hsbgk, hnbk, hcases⟩ := wfNode0_group_single_inv hwf hfit hsbg hnb
        have hst1_eq : st1 = st := by dsimp only [st1]; rw [hnd_eq]; rfl
        rcases hcases with rfl | ⟨pts, b, rfl, hpts_lt, hwfb, hfitb, hsbgb, hnbb⟩
        · have hout : out = PreOut0.mk st1 (nextSc + 1)
              (PreItem0.mk k cur.venv nextSc :: rest) := by
            dsimp only [out, preStepPush0, isTerm0, preStepGroup0, prePushGroup0,
              preEnqueueGroup0]
            rw [hnd_eq]; rfl
          have hsc_ub_big : nextSc.toNat + 2 * (1 + 0 + nodeCount0 k +
              workNodeCount0 (rest.map PreItem0.node)) < 2 ^ 31 := by
            have := hinv.nextSc_bound
            rw [List.map_cons, hnd_eq] at this
            dsimp only [workNodeCount0, nodeCount0, blocksNodeCount0] at this; exact this
          have hsc1 : (nextSc + 1).toNat = nextSc.toNat + 1 := u32_add1_toNat6 (by omega)
          have hnd_sc : (nextSc :: rest.map PreItem0.scope).Nodup := by
            refine List.nodup_cons.mpr ⟨fun hm => ?_, hrest_nodup⟩
            obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hm
            have := hrest_lt p hp; have := congrArg UInt32.toNat hpe; omega
          have huses_b : ∀ v < st1.nextVid.toNat,
              st1.uses.getD v 0 +
                (argCount0 k + workArgCount0 (rest.map PreItem0.node)) < 2 ^ 31 := by
            intro v hv; rw [hst1_eq] at hv ⊢
            have hb := hinv.uses_bound v hv
            rw [List.map_cons, hnd_eq] at hb
            dsimp only [workArgCount0, argCount0, blocksArgCount0] at hb
            omega
          have hinv' : PreWorkInv0 ctx out.nextScope out.st out.work := by
            rw [hout, hst1_eq]; dsimp only
            refine ⟨hinv.defScope_sz, hinv.uses_sz, hinv.escaped_sz,
              fun v hv => by have := hinv.defScope_lt v hv; omega,
              hinv.escaped_bit, by simpa only [List.map_cons] using hnd_sc,
              fun p hp => by rcases List.mem_cons.mp hp with rfl | hp1; · dsimp only; omega
                             · have := hrest_lt p hp1; omega,
              fun p hp => by
                rcases List.mem_cons.mp hp with rfl | hp1
                · exact ⟨vT, legalAddSigs0 [] lT, hvlen, hvlt, hwfk, hfitk, hsbgk, hnbk⟩
                · exact hinv.items_ok p (List.mem_cons_of_mem _ hp1),
              by have := hinv.nextVid_bound
                 rw [List.map_cons, hnd_eq] at this; simp only [List.map_cons]
                 dsimp only [workBinderCount0, binderCount0, blocksBinderCount0] at this ⊢
                 omega,
              by have := hsc_ub_big; simp only [List.map_cons]
                 dsimp only [workNodeCount0]; omega,
              by have := hinv.argCount_bound
                 rw [List.map_cons, hnd_eq] at this; simp only [List.map_cons]
                 dsimp only [workArgCount0, argCount0, blocksArgCount0] at this ⊢; omega,
              by rw [hst1_eq] at huses_b; rw [List.map_cons]
                 dsimp only [workArgCount0]; exact huses_b⟩
          intro v hv hre p hp
          obtain ⟨_, hrest_u⟩ := step_post hinv' (fun _ _ => by rw [hout, hst1_eq])
            (by rw [hout, hst1_eq]; exact Nat.le_refl _)
            (fun _ _ h => by rw [hout]; exact h) v hv hre
          rcases List.mem_cons.mp hp with rfl | hp'
          · have hdl := hinv.defScope_lt v hv
            have hk_u := hrest_u ⟨k, p.venv, nextSc⟩ (by rw [hout]; simp)
            have hnk : (nextSc : UInt32).toNat ≠ st.defScope.getD v 0 := by omega
            simp only [hnk, ↓reduceIte, hout, hst1_eq] at hk_u
            rw [hnd_eq]
            dsimp only [astUses0, blocksAstUses0, spineUses0, nodeArgsUses0]
            rw [hk_u, Nat.zero_add]
            split <;> exact rfl
          · have hr := hrest_u p (by rw [hout]; simp [hp'])
            rw [hout, hst1_eq] at hr; exact hr
        · have hout : out =
              PreOut0.mk (preBindLoop0 (tyLenU0 pts 0) nextSc cur.venv st1).2 (nextSc + 2)
                (PreItem0.mk k cur.venv (nextSc + 1) ::
                  PreItem0.mk b (preBindLoop0 (tyLenU0 pts 0) nextSc cur.venv st1).1
                    nextSc :: rest) := by
            dsimp only [out, preStepPush0]; rw [hnd_eq]
            simp only [isTerm0, Bool.false_eq_true, ↓reduceIte]
            dsimp only [preStepGroup0, preEnqueueGroup0, prePushGroup0, prePushOne0]
            rw [UInt32.add_assoc, show (1 : UInt32) + 1 = 2 by decide]
          have hsc_ub_big : nextSc.toNat + 2 * (1 + (nodeCount0 b + 0) + nodeCount0 k +
              workNodeCount0 (rest.map PreItem0.node)) < 2 ^ 31 := by
            have := hinv.nextSc_bound
            rw [List.map_cons, hnd_eq] at this
            dsimp only [workNodeCount0, nodeCount0, blocksNodeCount0] at this; exact this
          have hsc1 : (nextSc + 1).toNat = nextSc.toNat + 1 := u32_add1_toNat6 (by omega)
          have hsc2 : (nextSc + 2).toNat = nextSc.toNat + 2 := u32_add_ofNat_lt6 (m := 2) (by omega)
          have hlen_pts : (tyLenU0 pts 0).toNat = pts.length := tyLenU0_eq_of_lt hpts_lt
          have hnv_b : st.nextVid.toNat + pts.length < 2 ^ 32 := by
            have := hinv.nextVid_bound
            rw [List.map_cons, hnd_eq] at this
            dsimp only [workBinderCount0, binderCount0, blocksBinderCount0] at this; omega
          have hbind := preBindLoop0_spec pts.length (tyLenU0 pts 0) nextSc cur.venv st
            hlen_pts hnv_b hinv.defScope_sz hinv.uses_sz hinv.escaped_sz
          dsimp only at hbind
          have hnd_sc : ([nextSc + 1, nextSc] ++ rest.map PreItem0.scope).Nodup := by
            refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, hrest_nodup⟩⟩
            · intro hm; rcases List.mem_cons.mp hm with h | h
              · have := congrArg UInt32.toNat h; omega
              · obtain ⟨p, hp, hpe⟩ := List.mem_map.mp h
                have := hrest_lt p hp; have := congrArg UInt32.toNat hpe; omega
            · intro hm; obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hm
              have := hrest_lt p hp; have := congrArg UInt32.toNat hpe; omega
          have hvlen_b : (pushFreshVids0 pts.length st.nextVid cur.venv).length =
              (pushTys0 pts vT).length := by
            rw [pushFreshVids0_length, hvlen, pushTys0_eq_pushTypes, pushTypes_length]
          have hvlt_b : ∀ v ∈ pushFreshVids0 pts.length st.nextVid cur.venv,
              v.toNat < st.nextVid.toNat + pts.length := by
            intro v hm
            rcases (mem_pushFreshVids0 pts.length st.nextVid cur.venv v).mp hm
              with h0 | ⟨j, hj, rfl⟩
            · exact Nat.lt_of_lt_of_le (hvlt v h0) (Nat.le_add_right _ _)
            · rw [u32_add_ofNat_lt6 (by omega)]; omega
          have huses_b : ∀ v <
              (preBindLoop0 (tyLenU0 pts 0) nextSc cur.venv st).2.nextVid.toNat,
              (preBindLoop0 (tyLenU0 pts 0) nextSc cur.venv st).2.uses.getD v 0 +
                (argCount0 k +
                  (argCount0 b + workArgCount0 (rest.map PreItem0.node))) < 2 ^ 31 := by
            intro v hv
            rw [hbind.2.1] at hv; rw [hbind.2.2.2.2.2.2.1 v]
            by_cases hv0 : v < st.nextVid.toNat
            · simp only [hv0, ↓reduceIte]
              have hb := hinv.uses_bound v hv0
              rw [List.map_cons, hnd_eq] at hb
              dsimp only [workArgCount0, argCount0, blocksArgCount0] at hb
              omega
            · simp only [hv0, ↓reduceIte, Nat.zero_add]
              have hb := hinv.argCount_bound
              rw [List.map_cons, hnd_eq] at hb
              dsimp only [workArgCount0, argCount0, blocksArgCount0] at hb
              omega
          have hinv' : PreWorkInv0 ctx out.nextScope out.st out.work := by
            rw [hout, hst1_eq]; dsimp only
            refine ⟨hbind.2.2.1.trans hbind.2.1.symm, hbind.2.2.2.1.trans hbind.2.1.symm,
              hbind.2.2.2.2.1.trans hbind.2.1.symm,
              fun v hv => by
                rw [hbind.2.1] at hv; rw [hbind.2.2.2.2.2.1 v]; split
                · rename_i hv0; have := hinv.defScope_lt v hv0; omega
                · omega,
              fun v hv => by
                rw [hbind.2.1] at hv; rw [hbind.2.2.2.2.2.2.2 v]; split
                · rename_i hv0; exact hinv.escaped_bit v hv0
                · exact Or.inl rfl,
              by simpa only [List.map_cons, List.cons_append, List.nil_append] using hnd_sc,
              fun p hp => by
                rcases List.mem_cons.mp hp with rfl | hp1
                · dsimp only; omega
                · rcases List.mem_cons.mp hp1 with rfl | hp2
                  · dsimp only; omega
                  · have := hrest_lt p hp2; omega,
              fun p hp => by
                rw [hbind.2.1]; rcases List.mem_cons.mp hp with rfl | hp1
                · exact ⟨vT, legalAddSigs0 [(pts, b)] lT, hvlen,
                    fun v hm => Nat.lt_of_lt_of_le (hvlt v hm) (Nat.le_add_right _ _),
                    hwfk, hfitk, hsbgk, hnbk⟩
                · rcases List.mem_cons.mp hp1 with rfl | hp2
                  · rw [hbind.1]
                    exact ⟨pushTys0 pts vT, legalAddSigs0 [(pts, b)] lT, hvlen_b, hvlt_b,
                      hwfb, hfitb, hsbgb, hnbb⟩
                  · obtain ⟨vT', lT', hvl', hvlt', hwf', hfit', hsbg', hnb'⟩ :=
                      hinv.items_ok p (List.mem_cons_of_mem _ hp2)
                    exact ⟨vT', lT', hvl',
                      fun v hm => Nat.lt_of_lt_of_le (hvlt' v hm) (Nat.le_add_right _ _),
                      hwf', hfit', hsbg', hnb'⟩,
              by rw [hbind.2.1]; have := hinv.nextVid_bound
                 rw [List.map_cons, hnd_eq] at this; simp only [List.map_cons]
                 dsimp only [workBinderCount0, binderCount0, blocksBinderCount0] at this ⊢; omega,
              by have := hsc_ub_big; simp only [List.map_cons]
                 dsimp only [workNodeCount0]; omega,
              by have := hinv.argCount_bound
                 rw [List.map_cons, hnd_eq] at this; simp only [List.map_cons]
                 dsimp only [workArgCount0, argCount0, blocksArgCount0] at this ⊢; omega,
              by rw [List.map_cons]; dsimp only [workArgCount0]; exact huses_b⟩
          intro v hv hre p hp
          obtain ⟨_, hrest_u⟩ := step_post hinv'
            (fun v hv => by rw [hout, hst1_eq, hbind.2.2.2.2.2.1 v]; simp [hv])
            (by rw [hout, hst1_eq, hbind.2.1]; exact Nat.le_add_right _ _)
            (fun v hv h => by
              rw [hout, hst1_eq, hbind.2.2.2.2.2.2.2 v]; simp only [hv, ↓reduceIte]
              rw [hst1_eq] at h; exact h) v hv hre
          have hnv_eq : out.st.nextVid = st.nextVid + UInt32.ofNat pts.length := by
            rw [hout, hst1_eq]
            exact u32_eq_add_of_toNat6 hbind.2.1 hnv_b
          rcases List.mem_cons.mp hp with rfl | hp'
          · have hdl := hinv.defScope_lt v hv
            have hk_u := hrest_u ⟨k, p.venv, nextSc + 1⟩ (by rw [hout]; simp)
            have hb_u := hrest_u
              ⟨b, (preBindLoop0 (tyLenU0 pts 0) nextSc p.venv st1).1, nextSc⟩
              (by rw [hout]; simp)
            have hnk : (nextSc + 1).toNat ≠ st.defScope.getD v 0 := by omega
            have hnb' : (nextSc : UInt32).toNat ≠ st.defScope.getD v 0 := by omega
            simp only [hnk, hnb', ↓reduceIte] at hk_u hb_u
            rw [hst1_eq, hbind.1, hnv_eq] at hb_u
            have hck : astUses0 (UInt32.ofNat v) p.venv st.nextVid k = 0 := by
              have hb_k : st.nextVid.toNat + binderCount0 k < 2 ^ 32 := by
                have := hinv.nextVid_bound
                rw [List.map_cons, hnd_eq] at this
                dsimp only [workBinderCount0, binderCount0] at this; omega
              have hb_ko : out.st.nextVid.toNat + binderCount0 k < 2 ^ 32 := by
                rw [hout, hst1_eq, hbind.2.1]
                have := hinv.nextVid_bound
                rw [List.map_cons, hnd_eq] at this
                dsimp only [workBinderCount0, binderCount0, blocksBinderCount0] at this; omega
              have hlt32 : (UInt32.ofNat v).toNat < st.nextVid.toNat := by
                rw [u32_toNat_ofNat6, Nat.mod_eq_of_lt (Nat.lt_trans hv (UInt32.toNat_lt _))]
                exact hv
              rw [← astUses0_congr k (UInt32.ofNat v) out.st.nextVid st.nextVid p.venv p.venv
                (by rw [hout, hst1_eq, hbind.2.1]; omega) hlt32 hb_ko hb_k (agreeBelow0_refl _ _)]
              exact hk_u
            rw [hnd_eq]
            dsimp only [astUses0, blocksAstUses0, spineUses0, nodeArgsUses0]
            rw [hb_u, hck, Nat.add_zero]
            split <;> exact rfl
          · have hr := hrest_u p (by rw [hout]; simp [hp'])
            have hbc_p := binderCount0_le_work_of_mem hp'
            have hcn := congr_nv p out.st.nextVid v (List.mem_cons_of_mem _ hp') hv
              (by rw [hout, hst1_eq, hbind.2.1]; exact Nat.le_add_right _ _)
              (by rw [hout, hst1_eq, hbind.2.1]
                  have := hinv.nextVid_bound
                  rw [List.map_cons, hnd_eq] at this
                  dsimp only [workBinderCount0, binderCount0, blocksBinderCount0] at this; omega)
            split at hr <;> rename_i hsc
            · simp only [hsc, ↓reduceIte]; exact hcn.1.symm.trans (hr.trans hcn.2)
            · simp only [hsc, ↓reduceIte]; exact hcn.1.symm.trans hr
      | let1 op args k | let2Umulw64 a b k | load t addr k | store t val addr k
      | call fnSym as bs args k =>
        have hlin : isTerm0 cur.node = false := by simp [isTerm0, hnd_eq]
        have hnj : ∀ c t e, cur.node ≠ .jnz c t e := fun c t e h => by rw [hnd_eq] at h; cases h
        have hng : ∀ bs' k', cur.node ≠ .group bs' k' := fun bs' k' h => by
          rw [hnd_eq] at h; cases h
        obtain ⟨hcnt_lt, hvlen_l, hwfl, hfitl, hsbgl, hnbl, hbc_l, hac_l, hnc_l, _⟩ :=
          wfNode0_lin_inv hwf hfit hsbg hnb hlin hnj hng
        have hout : out =
            PreOut0.mk (preBindLoop0 (linCnt0 cur.node) cur.scope cur.venv st1).2 nextSc
              (PreItem0.mk (linK0 cur.node)
                (preBindLoop0 (linCnt0 cur.node) cur.scope cur.venv st1).1 cur.scope ::
                rest) := by
          dsimp only [out, preStepPush0]; simp only [hlin, Bool.false_eq_true, ↓reduceIte]; rfl
        have hnv_b : st1.nextVid.toNat + (linCnt0 cur.node).toNat < 2 ^ 32 := by
          rw [hst1.1]; have := hinv.nextVid_bound
          rw [List.map_cons] at this; dsimp only [workBinderCount0] at this; omega
        have hbind := preBindLoop0_spec (linCnt0 cur.node).toNat (linCnt0 cur.node) cur.scope
          cur.venv st1 rfl hnv_b (hst1.1 ▸ hst1.2.1.symm ▸ hinv.defScope_sz)
          (hst1.1 ▸ hst1.2.2.1) (hst1.1 ▸ hst1.2.2.2.1)
        dsimp only at hbind
        have hnd_sc : (cur.scope :: rest.map PreItem0.scope).Nodup :=
          List.nodup_cons.mpr ⟨fun hm => by
            obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hm; exact hrest_scopes p hp hpe, hrest_nodup⟩
        have hvlt_l : ∀ v ∈ pushFreshVids0 (linCnt0 cur.node).toNat st1.nextVid cur.venv,
            v.toNat < st1.nextVid.toNat + (linCnt0 cur.node).toNat := by
          intro v hm
          rcases (mem_pushFreshVids0 (linCnt0 cur.node).toNat st1.nextVid cur.venv v).mp hm
            with h0 | ⟨j, hj, rfl⟩
          · rw [hst1.1]; exact Nat.lt_of_lt_of_le (hvlt v h0) (Nat.le_add_right _ _)
          · rw [u32_add_ofNat_lt6 (by omega)]; omega
        have huses_b : ∀ v <
            (preBindLoop0 (linCnt0 cur.node) cur.scope cur.venv st1).2.nextVid.toNat,
            (preBindLoop0 (linCnt0 cur.node) cur.scope cur.venv st1).2.uses.getD v 0 +
              (argCount0 (linK0 cur.node) + workArgCount0 (rest.map PreItem0.node)) < 2 ^ 31 := by
          intro v hv; rw [hbind.2.1, hst1.1] at hv; rw [hbind.2.2.2.2.2.2.1 v]
          by_cases hv0 : v < st.nextVid.toNat
          · rw [hst1.1]; simp only [hv0, ↓reduceIte]
            have hv1 := hst1.2.2.2.2.2 v hv0
            have hb := hinv.uses_bound v hv0
            rw [List.map_cons] at hb; dsimp only [workArgCount0] at hb
            have hnu := nodeArgsUses0_add_linK0_le (UInt32.ofNat v) cur.venv hlin hnj hng
            split at hv1 <;> { rw [hv1.1]; omega }
          · rw [hst1.1]; simp only [hv0, ↓reduceIte, Nat.zero_add]
            have hb := hinv.argCount_bound
            rw [List.map_cons] at hb; dsimp only [workArgCount0] at hb; omega
        have hinv' : PreWorkInv0 ctx out.nextScope out.st out.work := by
          rw [hout]
          refine ⟨hbind.2.2.1.trans hbind.2.1.symm, hbind.2.2.2.1.trans hbind.2.1.symm,
            hbind.2.2.2.2.1.trans hbind.2.1.symm,
            fun v hv => by
              rw [hbind.2.1] at hv; rw [hbind.2.2.2.2.2.1 v]; split
              · rename_i hv0; rw [hst1.2.1]; exact hinv.defScope_lt v (hst1.1 ▸ hv0)
              · exact hsc_cur_lt,
            fun v hv => by
              rw [hbind.2.1] at hv; rw [hbind.2.2.2.2.2.2.2 v]; split
              · rename_i hv0; exact hst1.2.2.2.2.1 v (hst1.1 ▸ hv0)
              · exact Or.inl rfl,
            by simpa only [List.map_cons] using hnd_sc,
            fun p hp => by
              rcases List.mem_cons.mp hp with rfl | hp1
              · exact hsc_cur_lt
              · exact hrest_lt p hp1,
            fun p hp => by
              rw [hbind.2.1]; rcases List.mem_cons.mp hp with rfl | hp1
              · rw [hbind.1]
                exact ⟨legalNextVenv0 cur.node vT, lT,
                  (pushFreshVids0_length _ _ _).trans (hvlen ▸ hvlen_l.symm), hvlt_l,
                  hwfl, hfitl, hsbgl, hnbl⟩
              · obtain ⟨vT', lT', hvl', hvlt', hwf', hfit', hsbg', hnb'⟩ :=
                  hinv.items_ok p (List.mem_cons_of_mem _ hp1)
                exact ⟨vT', lT', hvl',
                  fun v hm => by
                    rw [hst1.1]; exact Nat.lt_of_lt_of_le (hvlt' v hm) (Nat.le_add_right _ _),
                  hwf', hfit', hsbg', hnb'⟩,
            by rw [hbind.2.1, hst1.1]; have := hinv.nextVid_bound
               rw [List.map_cons] at this ⊢; dsimp only [workBinderCount0] at this ⊢; omega,
            by have := hinv.nextSc_bound; rw [List.map_cons] at this ⊢
               dsimp only [workNodeCount0] at this ⊢; omega,
            by have := hinv.argCount_bound; rw [List.map_cons] at this ⊢
               dsimp only [workArgCount0] at this ⊢; omega,
            by rw [List.map_cons]; dsimp only [workArgCount0]; exact huses_b⟩
        intro v hv hre p hp
        obtain ⟨hn_z, hrest_u⟩ := step_post hinv'
          (fun v hv => by
            have hv1 : v < st1.nextVid.toNat := by rw [hst1.1]; exact hv
            rw [hout, hbind.2.2.2.2.2.1 v]; simp only [hv1, ↓reduceIte]; rw [hst1.2.1])
          (by rw [hout, hbind.2.1, hst1.1]; exact Nat.le_add_right _ _)
          (fun v hv h => by
            have hv1 : v < st1.nextVid.toNat := by rw [hst1.1]; exact hv
            rw [hout, hbind.2.2.2.2.2.2.2 v]; simp only [hv1, ↓reduceIte]; exact h) v hv hre
        have hnv_eq : out.st.nextVid = st.nextVid + UInt32.ofNat (linCnt0 cur.node).toNat := by
          rw [hout]
          exact u32_eq_add_of_toNat6 (by rw [hbind.2.1, hst1.1]) (by rw [← hst1.1]; exact hnv_b)
        have hvenv_eq : (preBindLoop0 (linCnt0 cur.node) cur.scope cur.venv st1).1 =
            pushFreshVids0 (linCnt0 cur.node).toNat st.nextVid cur.venv := by
          rw [hbind.1, hst1.1]
        rcases List.mem_cons.mp hp with rfl | hp'
        · have hk_u := hrest_u ⟨linK0 p.node,
              (preBindLoop0 (linCnt0 p.node) p.scope p.venv st1).1, p.scope⟩
              (by rw [hout]; exact List.mem_cons_self)
          have hnv_k : (preBindLoop0 (linCnt0 p.node) p.scope p.venv st1).2.nextVid =
              st.nextVid + UInt32.ofNat (linCnt0 p.node).toNat := by
            simpa only [hout] using hnv_eq
          rw [hout] at hk_u
          dsimp only at hk_u
          rw [hbind.1, hst1.1, hnv_k] at hk_u
          rw [astUses0_lin (UInt32.ofNat v) p.venv st.nextVid hlin hnj hng hfit,
            spineUses0_lin (UInt32.ofNat v) p.venv st.nextVid hlin hnj hng hfit]
          split at hk_u <;> rename_i hsc
          · simp only [hsc, ↓reduceIte, hk_u]
          · simp only [hsc, ↓reduceIte, hn_z hsc, hk_u, Nat.add_zero]
        · have hr := hrest_u p (by rw [hout]; exact List.mem_cons_of_mem _ hp')
          have hbc_p := binderCount0_le_work_of_mem hp'
          have hcn := congr_nv p out.st.nextVid v (List.mem_cons_of_mem _ hp') hv
            (by rw [hout, hbind.2.1, hst1.1]; exact Nat.le_add_right _ _)
            (by rw [hout, hbind.2.1, hst1.1]
                have := hinv.nextVid_bound
                rw [List.map_cons] at this; dsimp only [workBinderCount0] at this; omega)
          split at hr <;> rename_i hsc
          · simp only [hsc, ↓reduceIte]; exact hcn.1.symm.trans (hr.trans hcn.2)
          · simp only [hsc, ↓reduceIte]; exact hcn.1.symm.trans hr

/-! ## 2. Slot Pool, Release, & Binding Specs -/

/-- Well-formedness of `(free, nxt)` slot pool relative to bound `maxBd`. -/
@[expose] def SlotPoolInv0 (free : List UInt32) (nxt maxSl : UInt32) (maxBd : Nat) : Prop :=
  free.Nodup ∧ (∀ s ∈ free, s.toNat < nxt.toNat) ∧
  nxt.toNat ≤ maxSl.toNat ∧ maxSl.toNat ≤ maxBd ∧ maxBd < 2 ^ 31

private theorem allocSlot0_spec (free : List UInt32) (nxt maxSl : UInt32) (maxBd : Nat)
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
    have hadd1 : (nxt + 1).toNat = nxt.toNat + 1 := u32_add1_toNat6 (by omega)
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
    have hadd1 : (s + 1).toNat = s.toNat + 1 := u32_add1_toNat6 (by omega)
    refine ⟨⟨hnd, fun x hx => hflt0 x (List.mem_cons_of_mem _ hx), ?_, ?_, hmax_bd⟩,
      hs_lt, Nat.le_refl _, Nat.le_add_right _ _, Or.inl List.mem_cons_self, fun x => ?_⟩
    · rw [u32Max0_toNat]; exact Nat.le_trans h1 (Nat.le_max_left _ _)
    · rw [u32Max0_toNat, hadd1]; exact Nat.max_le.mpr ⟨h2, by omega⟩
    · constructor
      · intro hx; exact ⟨List.mem_cons_of_mem _ hx, fun h => hnin (h ▸ hx)⟩
      · rintro ⟨hx, hne⟩; rcases List.mem_cons.mp hx with rfl | hx'
        · exact absurd rfl hne
        · exact hx'

private theorem argUses0_var_self6 (venv : List UInt32) (idx : UInt32) :
    argUses0 (UInt32.ofNat (listGetU32 venv idx).toNat) venv (.var idx) = 1 := by
  simp [argUses0, UInt32.ofNat_toNat]

private theorem argsUses0_var_pos6 {venv : List UInt32} {args : List Arg0} {idx : UInt32}
    (hm : Arg0.var idx ∈ args) :
    0 < argsUses0 (UInt32.ofNat (listGetU32 venv idx).toNat) venv args := by
  induction args with
  | nil => simp at hm
  | cons a rest ih =>
    dsimp only [argsUses0]
    rcases List.mem_cons.mp hm with rfl | hrest
    · rw [argUses0_var_self6]; exact Nat.add_pos_left Nat.one_pos _
    · exact Nat.add_pos_right _ (ih hrest)

theorem releaseArg0_spec (esc vslot : Array Nat) (venv : List UInt32) (res : RelRes0)
    (a : Arg0) (nextVid : Nat) (nxt : UInt32) (hnv32 : nextVid ≤ 2 ^ 32)
    (D : Nat → Prop) (hsz : res.remUses.size = nextVid)
    (hvlt : ∀ v ∈ venv, v.toNat < nextVid)
    (ha : ∀ idx, a = .var idx → idx.toNat < venv.length)
    (hD : ∀ idx, a = .var idx →
      esc.getD (listGetU32 venv idx).toNat 0 = 0 → D (listGetU32 venv idx).toNat)
    (hesc : ∀ v < nextVid, esc.getD v 0 = 0 ∨ esc.getD v 0 = 1)
    (hrem_bd : ∀ v < nextVid, res.remUses.getD v 0 < 2 ^ 31)
    (hrem_ge : ∀ v < nextVid, esc.getD v 0 = 0 →
      argUses0 (UInt32.ofNat v) venv a ≤ res.remUses.getD v 0)
    (hvsl_ok : ∀ v < nextVid, D v → esc.getD v 0 = 0 → 0 < res.remUses.getD v 0 →
      (arrGetU0 vslot (UInt32.ofNat v)).toNat < nxt.toNat ∧
      arrGetU0 vslot (UInt32.ofNat v) ∉ res.free ∧
      ∀ w < nextVid, w ≠ v → D w → esc.getD w 0 = 0 → 0 < res.remUses.getD w 0 →
        arrGetU0 vslot (UInt32.ofNat w) ≠ arrGetU0 vslot (UInt32.ofNat v))
    (hfree_nd : res.free.Nodup) (hfree_lt : ∀ s ∈ res.free, s.toNat < nxt.toNat) :
    let res' := releaseArg0 esc vslot venv res a
    res'.remUses.size = nextVid ∧
    res'.free.Nodup ∧ (∀ s ∈ res'.free, s.toNat < nxt.toNat) ∧
    (∀ v < nextVid, res'.remUses.getD v 0 =
      if esc.getD v 0 = 0 then res.remUses.getD v 0 - argUses0 (UInt32.ofNat v) venv a
      else res.remUses.getD v 0) ∧
    (∀ s, s ∈ res'.free ↔ s ∈ res.free ∨
      ∃ v < nextVid, D v ∧ esc.getD v 0 = 0 ∧ 0 < res.remUses.getD v 0 ∧
        res'.remUses.getD v 0 = 0 ∧ s = arrGetU0 vslot (UInt32.ofNat v)) ∧
    (∀ v < nextVid, D v → esc.getD v 0 = 0 → 0 < res'.remUses.getD v 0 →
      (arrGetU0 vslot (UInt32.ofNat v)).toNat < nxt.toNat ∧
      arrGetU0 vslot (UInt32.ofNat v) ∉ res'.free ∧
      ∀ w < nextVid, w ≠ v → D w → esc.getD w 0 = 0 → 0 < res'.remUses.getD w 0 →
        arrGetU0 vslot (UInt32.ofNat w) ≠ arrGetU0 vslot (UInt32.ofNat v)) := by
  cases a with
  | immBool _ | immBits _ _ =>
    refine ⟨hsz, hfree_nd, hfree_lt, fun v _ => by simp [releaseArg0, argUses0],
      fun s => ⟨Or.inl, fun h => h.elim id fun ⟨_, _, _, _, h1, h2, _⟩ => by
        dsimp only [releaseArg0] at h2; omega⟩,
      fun v hv hDv he hr => hvsl_ok v hv hDv he hr⟩
  | var idx =>
    dsimp only [releaseArg0]
    let vid := listGetU32 venv idx
    have hvid_def : listGetU32 venv idx = vid := rfl
    have hidx : idx.toNat < venv.length := ha idx rfl
    have hvid_mem : vid ∈ venv := by
      rw [← hvid_def, listGetU32_eq_listGetD]; exact listGetD_mem6 hidx
    have hvid_lt : vid.toNat < nextVid := hvlt vid hvid_mem
    have hvid_eq32 : vid = UInt32.ofNat vid.toNat := UInt32.ofNat_toNat.symm
    have hesc_lt : esc.getD vid.toNat 0 < 2 ^ 32 := by
      rcases hesc vid.toNat hvid_lt with h0 | h1 <;> omega
    have hesc_v := arrGetU0_of_lt6 esc vid hesc_lt
    by_cases hz : arrGetU0 esc (listGetU32 venv idx) = 0
    · have hesc0 : esc.getD vid.toNat 0 = 0 := by rw [← hesc_v, ← hvid_def, hz]; rfl
      have hD_vid : D vid.toNat := hD idx rfl (hvid_def ▸ hesc0)
      have hge1 : 1 ≤ res.remUses.getD vid.toNat 0 := by
        have hg := hrem_ge vid.toNat hvid_lt hesc0
        have hu : argUses0 (UInt32.ofNat vid.toNat) venv (.var idx) = 1 := by
          simp [argUses0, ← hvid_eq32, hvid_def]
        omega
      have hrem_lt : res.remUses.getD vid.toNat 0 < 2 ^ 32 := by
        have := hrem_bd vid.toNat hvid_lt; omega
      have hrem_v := arrGetU0_of_lt6 res.remUses vid hrem_lt
      have hv_ok := hvsl_ok vid.toNat hvid_lt hD_vid hesc0 (by omega)
      have harg_eq : ∀ v < nextVid, argUses0 (UInt32.ofNat v) venv (.var idx) =
          if v = vid.toNat then 1 else 0 := fun v hv => by
        by_cases hvv : v = vid.toNat
        · subst hvv; simp [argUses0, ← hvid_eq32, hvid_def]
        · have hne : vid ≠ UInt32.ofNat v := fun h => hvv (by
            have := congrArg UInt32.toNat h
            rw [u32_toNat_ofNat6, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hv hnv32)] at this
            exact this.symm)
          simp [argUses0, show listGetU32 venv idx ≠ UInt32.ofNat v from hvid_def ▸ hne, hvv]
      simp only [hz, ↓reduceIte]
      by_cases hle1 : arrGetU0 res.remUses (listGetU32 venv idx) ≤ 1
      · have hle1' : (arrGetU0 res.remUses vid).toNat ≤ 1 := by
          simpa [UInt32.toNat_one, ← hvid_def] using UInt32.le_iff_toNat_le.mp hle1
        have hrem1 : res.remUses.getD vid.toNat 0 = 1 := by omega
        have hdec : decide (arrGetU0 res.remUses (listGetU32 venv idx) ≤ 1) = true :=
          decide_eq_true hle1
        simp only [hdec, ↓reduceIte]
        have hrem_spec : ∀ v < nextVid,
            (arrSetU0 res.remUses (listGetU32 venv idx) 0).getD v 0 =
            if esc.getD v 0 = 0 then
              res.remUses.getD v 0 - argUses0 (UInt32.ofNat v) venv (.var idx)
            else res.remUses.getD v 0 := fun v hv => by
          rw [arrSetU0_getD6 res.remUses (listGetU32 venv idx) 0 (hsz ▸ hvid_lt) v, harg_eq v hv]
          split <;> rename_i hvv
          · rw [hvid_def] at hvv; subst hvv; simp [hesc0, hrem1]
          · split <;> simp
        refine ⟨by rw [arrSetU0_size6, hsz],
          List.nodup_cons.mpr ⟨by rw [hvid_def, hvid_eq32]; exact hv_ok.2.1, hfree_nd⟩,
          fun s hs => by
            rcases List.mem_cons.mp hs with rfl | hs'
            · rw [hvid_def, hvid_eq32]; exact hv_ok.1
            · exact hfree_lt s hs',
          hrem_spec, fun s => ?_, fun v hv hDv he hr => ?_⟩
        · rw [List.mem_cons]; constructor
          · rintro (rfl | hm)
            · right; exact ⟨vid.toNat, hvid_lt, hD_vid, hesc0, by omega,
                by rw [hrem_spec vid.toNat hvid_lt, harg_eq vid.toNat hvid_lt]
                   simp [hesc0, hrem1],
                by rw [hvid_def, UInt32.ofNat_toNat]⟩
            · left; exact hm
          · rintro (hm | ⟨v, hv, _, hev, hposv, hzv, rfl⟩)
            · right; exact hm
            · left; rw [hrem_spec v hv, hev, harg_eq v hv] at hzv
              simp only [↓reduceIte] at hzv
              by_cases hvv : v = vid.toNat
              · subst hvv; rw [hvid_def, UInt32.ofNat_toNat]
              · simp only [hvv, ↓reduceIte, Nat.sub_zero] at hzv; omega
        · rw [hrem_spec v hv, he] at hr; simp only [↓reduceIte] at hr
          have hne_v : v ≠ vid.toNat := by
            rintro rfl; rw [harg_eq vid.toNat hvid_lt, hrem1] at hr; simp at hr
          have hok_v := hvsl_ok v hv hDv he (by omega)
          refine ⟨hok_v.1, fun hm => ?_, fun w hw hnw hDw hew hrw => ?_⟩
          · rcases List.mem_cons.mp hm with heq | hm'
            · rw [hvid_def, hvid_eq32] at heq
              exact hv_ok.2.2 v hv hne_v hDv he (by omega) heq
            · exact hok_v.2.1 hm'
          · rw [hrem_spec w hw, hew] at hrw; simp only [↓reduceIte] at hrw
            exact hok_v.2.2 w hw hnw hDw hew (by omega)
      · have hgt1 : 1 < res.remUses.getD vid.toNat 0 := by
          have hn : ¬ (arrGetU0 res.remUses vid).toNat ≤ 1 := fun h =>
            hle1 (UInt32.le_iff_toNat_le.mpr (by simpa [UInt32.toNat_one, ← hvid_def] using h))
          omega
        have hsub : (arrGetU0 res.remUses (listGetU32 venv idx) - 1).toNat =
            res.remUses.getD vid.toNat 0 - 1 := by
          have h0 : 0 < (arrGetU0 res.remUses vid).toNat := by omega
          rw [hvid_def, u32_sub1_toNat6 h0, hrem_v]
        have hdec : decide (arrGetU0 res.remUses (listGetU32 venv idx) ≤ 1) = false :=
          decide_eq_false hle1
        simp only [hdec, Bool.false_eq_true, ↓reduceIte]
        have hrem_spec : ∀ v < nextVid,
            (arrSetU0 res.remUses (listGetU32 venv idx)
              (arrGetU0 res.remUses (listGetU32 venv idx) - 1)).getD v 0 =
            if esc.getD v 0 = 0 then
              res.remUses.getD v 0 - argUses0 (UInt32.ofNat v) venv (.var idx)
            else res.remUses.getD v 0 := fun v hv => by
          rw [arrSetU0_getD6 res.remUses (listGetU32 venv idx) _ (hsz ▸ hvid_lt) v, harg_eq v hv]
          split <;> rename_i hvv
          · rw [hvid_def] at hvv; subst hvv; simp [hesc0, hsub]
          · split <;> simp
        refine ⟨by rw [arrSetU0_size6, hsz], hfree_nd, hfree_lt, hrem_spec, fun s => ?_,
          fun v hv hDv he hr => ?_⟩
        · constructor
          · intro hm; exact Or.inl hm
          · rintro (hm | ⟨v, hv, _, hev, hposv, hzv, rfl⟩)
            · exact hm
            · rw [hrem_spec v hv, hev, harg_eq v hv] at hzv
              simp only [↓reduceIte] at hzv
              split at hzv <;> rename_i hvv
              · subst hvv; omega
              · omega
        · rw [hrem_spec v hv, he] at hr; simp only [↓reduceIte] at hr
          have hau_v : argUses0 (UInt32.ofNat v) venv (.var idx) ≤ 1 := by
            rw [harg_eq v hv]; split <;> omega
          have hok_v := hvsl_ok v hv hDv he (by omega)
          refine ⟨hok_v.1, hok_v.2.1, fun w hw hnw hDw hew hrw => ?_⟩
          rw [hrem_spec w hw, hew] at hrw; simp only [↓reduceIte] at hrw
          have hau_w : argUses0 (UInt32.ofNat w) venv (.var idx) ≤ 1 := by
            rw [harg_eq w hw]; split <;> omega
          exact hok_v.2.2 w hw hnw hDw hew (by omega)
    · have hesc1 : esc.getD vid.toNat 0 = 1 := by
        rcases hesc vid.toNat hvid_lt with h0 | h1
        · exfalso; apply hz; apply u32_ext6; rw [hvid_def, hesc_v, h0]; rfl
        · exact h1
      have harg_zero : ∀ v < nextVid, esc.getD v 0 = 0 →
          argUses0 (UInt32.ofNat v) venv (.var idx) = 0 := fun v hv he => by
        have hne : vid ≠ UInt32.ofNat v := fun h => by
          have hv_eq : vid.toNat = v := by
            have := congrArg UInt32.toNat h
            rw [u32_toNat_ofNat6, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hv hnv32)] at this
            exact this
          rw [hv_eq, he] at hesc1; cases hesc1
        simp [argUses0, show listGetU32 venv idx ≠ UInt32.ofNat v from hvid_def ▸ hne]
      simp only [hz, ↓reduceIte]
      refine ⟨hsz, hfree_nd, hfree_lt, fun v hv => by
        split <;> rename_i he
        · rw [harg_zero v hv he, Nat.sub_zero]
        · rfl,
        fun s => ⟨Or.inl, fun h => h.elim id fun ⟨v, hv, _, he, _, hz, _⟩ => by omega⟩,
        fun v hv hDv he hr => hvsl_ok v hv hDv he hr⟩

private theorem releaseArgs0_spec (esc vslot : Array Nat) (venv : List UInt32) :
    ∀ (args : List Arg0) (res : RelRes0) (nextVid : Nat) (nxt : UInt32) (D : Nat → Prop),
      nextVid ≤ 2 ^ 32 →
      res.remUses.size = nextVid →
      (∀ v ∈ venv, v.toNat < nextVid) →
      (∀ a ∈ args, ∀ idx, a = .var idx → idx.toNat < venv.length) →
      (∀ a ∈ args, ∀ idx, a = .var idx →
        esc.getD (listGetU32 venv idx).toNat 0 = 0 → D (listGetU32 venv idx).toNat) →
      (∀ v < nextVid, esc.getD v 0 = 0 ∨ esc.getD v 0 = 1) →
      (∀ v < nextVid, res.remUses.getD v 0 < 2 ^ 31) →
      (∀ v < nextVid, esc.getD v 0 = 0 →
        argsUses0 (UInt32.ofNat v) venv args ≤ res.remUses.getD v 0) →
      (∀ v < nextVid, D v → esc.getD v 0 = 0 → 0 < res.remUses.getD v 0 →
        (arrGetU0 vslot (UInt32.ofNat v)).toNat < nxt.toNat ∧
        arrGetU0 vslot (UInt32.ofNat v) ∉ res.free ∧
        ∀ w < nextVid, w ≠ v → D w → esc.getD w 0 = 0 → 0 < res.remUses.getD w 0 →
          arrGetU0 vslot (UInt32.ofNat w) ≠ arrGetU0 vslot (UInt32.ofNat v)) →
      res.free.Nodup → (∀ s ∈ res.free, s.toNat < nxt.toNat) →
      let res' := releaseArgs0 esc vslot venv res args
      res'.remUses.size = nextVid ∧
      res'.free.Nodup ∧ (∀ s ∈ res'.free, s.toNat < nxt.toNat) ∧
      (∀ v < nextVid, res'.remUses.getD v 0 =
        if esc.getD v 0 = 0 then res.remUses.getD v 0 - argsUses0 (UInt32.ofNat v) venv args
        else res.remUses.getD v 0) ∧
      (∀ s, s ∈ res'.free ↔ s ∈ res.free ∨
        ∃ v < nextVid, D v ∧ esc.getD v 0 = 0 ∧ 0 < res.remUses.getD v 0 ∧
          res'.remUses.getD v 0 = 0 ∧ s = arrGetU0 vslot (UInt32.ofNat v)) ∧
      (∀ v < nextVid, D v → esc.getD v 0 = 0 → 0 < res'.remUses.getD v 0 →
        (arrGetU0 vslot (UInt32.ofNat v)).toNat < nxt.toNat ∧
        arrGetU0 vslot (UInt32.ofNat v) ∉ res'.free ∧
        ∀ w < nextVid, w ≠ v → D w → esc.getD w 0 = 0 → 0 < res'.remUses.getD w 0 →
          arrGetU0 vslot (UInt32.ofNat w) ≠ arrGetU0 vslot (UInt32.ofNat v))
  | [], res, _, _, _, _, hsz, _, _, _, _, _, _, hvok, hnd, hflt =>
    ⟨hsz, hnd, hflt, fun v _ => by
        dsimp only [releaseArgs0, argsUses0]; split
        · exact (Nat.sub_zero _).symm
        · rfl,
      fun s => ⟨Or.inl, fun h => h.elim id fun ⟨_, _, _, _, h1, h2, _⟩ => by
        dsimp only [releaseArgs0] at h2; omega⟩, hvok⟩
  | a :: rest, res, nextVid, nxt, D, hnv32, hsz, hvlt, ha, hD, hesc, hbd, hge, hvok,
      hnd, hflt => by
    dsimp only [releaseArgs0]
    have h1 := releaseArg0_spec esc vslot venv res a nextVid nxt hnv32 D hsz hvlt
      (ha a List.mem_cons_self) (hD a List.mem_cons_self) hesc hbd
      (fun v hv he => by have := hge v hv he; dsimp only [argsUses0] at this; omega)
      hvok hnd hflt
    dsimp only at h1
    let r1 := releaseArg0 esc vslot venv res a
    have hbd1 : ∀ v < nextVid, r1.remUses.getD v 0 < 2 ^ 31 := fun v hv => by
      have hs := h1.2.2.2.1 v hv; split at hs <;> { have hb := hbd v hv; rw [hs]; omega }
    have hge1 : ∀ v < nextVid, esc.getD v 0 = 0 →
        argsUses0 (UInt32.ofNat v) venv rest ≤ r1.remUses.getD v 0 := fun v hv he => by
      have hs := h1.2.2.2.1 v hv; simp only [he, ↓reduceIte] at hs
      have hg := hge v hv he; dsimp only [argsUses0] at hg; rw [hs]; omega
    have h2 := releaseArgs0_spec esc vslot venv rest r1 nextVid nxt D hnv32 h1.1 hvlt
      (fun b hb => ha b (List.mem_cons_of_mem _ hb))
      (fun b hb => hD b (List.mem_cons_of_mem _ hb))
      hesc hbd1 hge1 h1.2.2.2.2.2 h1.2.1 h1.2.2.1
    dsimp only at h2
    refine ⟨h2.1, h2.2.1, h2.2.2.1, fun v hv => ?_, fun s => ?_, h2.2.2.2.2.2⟩
    · rw [h2.2.2.2.1 v hv, h1.2.2.2.1 v hv]
      dsimp only [argsUses0]; split
      · rw [Nat.sub_sub]
      · rfl
    · rw [h2.2.2.2.2.1 s, h1.2.2.2.2.1 s]
      constructor
      · rintro ((hs | ⟨v, hv, hDv, he, hpos, hzr, rfl⟩) | ⟨v, hv, hDv, he, hpos, hzf, rfl⟩)
        · exact Or.inl hs
        · refine Or.inr ⟨v, hv, hDv, he, hpos, ?_, rfl⟩
          rw [h2.2.2.2.1 v hv, he, hzr]; simp
        · have hr1 := h1.2.2.2.1 v hv; simp only [he, ↓reduceIte] at hr1
          rw [hr1] at hpos
          exact Or.inr ⟨v, hv, hDv, he, by omega, hzf, rfl⟩
      · rintro (hs | ⟨v, hv, hDv, he, hpos, hzf, rfl⟩)
        · exact Or.inl (Or.inl hs)
        · by_cases hzr : r1.remUses.getD v 0 = 0
          · exact Or.inl (Or.inr ⟨v, hv, hDv, he, hpos, hzr, rfl⟩)
          · exact Or.inr ⟨v, hv, hDv, he, Nat.pos_of_ne_zero hzr, hzf, rfl⟩

theorem relNodeArgs0_spec (esc vslot : Array Nat) (venv : List UInt32) (node : TFlat0)
    (res : RelRes0) (nextVid : Nat) (nxt : UInt32) (hnv32 : nextVid ≤ 2 ^ 32)
    (D : Nat → Prop)
    (hlin : isTerm0 node = false) (hnj : ∀ c t e, node ≠ .jnz c t e)
    (hng : ∀ bs k, node ≠ .group bs k)
    (hsz : res.remUses.size = nextVid)
    (hvlt : ∀ v ∈ venv, v.toNat < nextVid) (hargs : nodeArgsInVenv0 venv.length node)
    (hD : ∀ v < nextVid, esc.getD v 0 = 0 →
      0 < nodeArgsUses0 (UInt32.ofNat v) venv node → D v)
    (hesc : ∀ v < nextVid, esc.getD v 0 = 0 ∨ esc.getD v 0 = 1)
    (hbd : ∀ v < nextVid, res.remUses.getD v 0 < 2 ^ 31)
    (hge : ∀ v < nextVid, esc.getD v 0 = 0 →
      nodeArgsUses0 (UInt32.ofNat v) venv node ≤ res.remUses.getD v 0)
    (hvok : ∀ v < nextVid, D v → esc.getD v 0 = 0 → 0 < res.remUses.getD v 0 →
      (arrGetU0 vslot (UInt32.ofNat v)).toNat < nxt.toNat ∧
      arrGetU0 vslot (UInt32.ofNat v) ∉ res.free ∧
      ∀ w < nextVid, w ≠ v → D w → esc.getD w 0 = 0 → 0 < res.remUses.getD w 0 →
        arrGetU0 vslot (UInt32.ofNat w) ≠ arrGetU0 vslot (UInt32.ofNat v))
    (hnd : res.free.Nodup) (hflt : ∀ s ∈ res.free, s.toNat < nxt.toNat) :
    let res' := relNodeArgs0 esc vslot venv node res
    res'.remUses.size = nextVid ∧
    res'.free.Nodup ∧ (∀ s ∈ res'.free, s.toNat < nxt.toNat) ∧
    (∀ v < nextVid, res'.remUses.getD v 0 =
      if esc.getD v 0 = 0 then res.remUses.getD v 0 - nodeArgsUses0 (UInt32.ofNat v) venv node
      else res.remUses.getD v 0) ∧
    (∀ s, s ∈ res'.free ↔ s ∈ res.free ∨
      ∃ v < nextVid, D v ∧ esc.getD v 0 = 0 ∧ 0 < res.remUses.getD v 0 ∧
        res'.remUses.getD v 0 = 0 ∧ s = arrGetU0 vslot (UInt32.ofNat v)) ∧
    (∀ v < nextVid, D v → esc.getD v 0 = 0 → 0 < res'.remUses.getD v 0 →
      (arrGetU0 vslot (UInt32.ofNat v)).toNat < nxt.toNat ∧
      arrGetU0 vslot (UInt32.ofNat v) ∉ res'.free ∧
      ∀ w < nextVid, w ≠ v → D w → esc.getD w 0 = 0 → 0 < res'.remUses.getD w 0 →
        arrGetU0 vslot (UInt32.ofNat w) ≠ arrGetU0 vslot (UInt32.ofNat v)) := by
  have hvid_lt_of_idx : ∀ {idx : UInt32}, idx.toNat < venv.length →
      (listGetU32 venv idx).toNat < nextVid := fun {idx} hi =>
    hvlt _ (by rw [listGetU32_eq_listGetD]; exact listGetD_mem6 hi)
  have twoArgs : ∀ (a b : Arg0),
      (∀ idx, a = .var idx → idx.toNat < venv.length) →
      (∀ idx, b = .var idx → idx.toNat < venv.length) →
      (∀ idx, a = .var idx →
        esc.getD (listGetU32 venv idx).toNat 0 = 0 → D (listGetU32 venv idx).toNat) →
      (∀ idx, b = .var idx →
        esc.getD (listGetU32 venv idx).toNat 0 = 0 → D (listGetU32 venv idx).toNat) →
      (∀ v < nextVid, esc.getD v 0 = 0 →
        argUses0 (UInt32.ofNat v) venv a + argUses0 (UInt32.ofNat v) venv b ≤
          res.remUses.getD v 0) →
      let res' := releaseArg0 esc vslot venv (releaseArg0 esc vslot venv res a) b
      res'.remUses.size = nextVid ∧
      res'.free.Nodup ∧ (∀ s ∈ res'.free, s.toNat < nxt.toNat) ∧
      (∀ v < nextVid, res'.remUses.getD v 0 =
        if esc.getD v 0 = 0 then
          res.remUses.getD v 0 -
            (argUses0 (UInt32.ofNat v) venv a + argUses0 (UInt32.ofNat v) venv b)
        else res.remUses.getD v 0) ∧
      (∀ s, s ∈ res'.free ↔ s ∈ res.free ∨
        ∃ v < nextVid, D v ∧ esc.getD v 0 = 0 ∧ 0 < res.remUses.getD v 0 ∧
          res'.remUses.getD v 0 = 0 ∧ s = arrGetU0 vslot (UInt32.ofNat v)) ∧
      (∀ v < nextVid, D v → esc.getD v 0 = 0 → 0 < res'.remUses.getD v 0 →
        (arrGetU0 vslot (UInt32.ofNat v)).toNat < nxt.toNat ∧
        arrGetU0 vslot (UInt32.ofNat v) ∉ res'.free ∧
        ∀ w < nextVid, w ≠ v → D w → esc.getD w 0 = 0 → 0 < res'.remUses.getD w 0 →
          arrGetU0 vslot (UInt32.ofNat w) ≠ arrGetU0 vslot (UInt32.ofNat v)) := by
    intro a b ha hb hDa hDb hge2
    have h := releaseArgs0_spec esc vslot venv [a, b] res nextVid nxt D hnv32 hsz hvlt
      (fun x hx => by rcases List.mem_cons.mp hx with rfl | hx1
                      · exact ha
                      · simp only [List.mem_singleton] at hx1; subst hx1; exact hb)
      (fun x hx => by rcases List.mem_cons.mp hx with rfl | hx1
                      · exact hDa
                      · simp only [List.mem_singleton] at hx1; subst hx1; exact hDb)
      hesc hbd (fun v hv he => by have := hge2 v hv he; dsimp only [argsUses0]; omega)
      hvok hnd hflt
    dsimp only [releaseArgs0, argsUses0] at h
    simpa only [Nat.add_zero] using h
  cases node with
  | let1 op args k =>
    refine releaseArgs0_spec esc vslot venv args res nextVid nxt D hnv32 hsz hvlt
      hargs ?_ hesc hbd hge hvok hnd hflt
    intro a ha idx heq hesc0; subst heq
    exact hD _ (hvid_lt_of_idx (hargs _ ha _ rfl)) hesc0 (argsUses0_var_pos6 ha)
  | call fnSym as bs args k =>
    refine releaseArgs0_spec esc vslot venv args res nextVid nxt D hnv32 hsz hvlt
      hargs ?_ hesc hbd hge hvok hnd hflt
    intro a ha idx heq hesc0; subst heq
    exact hD _ (hvid_lt_of_idx (hargs _ ha _ rfl)) hesc0 (argsUses0_var_pos6 ha)
  | let2Umulw64 a b k =>
    refine twoArgs a b hargs.1 hargs.2 ?_ ?_ hge
    · intro idx heq hesc0; subst heq
      refine hD _ (hvid_lt_of_idx (hargs.1 idx rfl)) hesc0 ?_
      dsimp only [nodeArgsUses0]; rw [argUses0_var_self6]; exact Nat.add_pos_left Nat.one_pos _
    · intro idx heq hesc0; subst heq
      refine hD _ (hvid_lt_of_idx (hargs.2 idx rfl)) hesc0 ?_
      dsimp only [nodeArgsUses0]; rw [argUses0_var_self6]; exact Nat.add_pos_right _ Nat.one_pos
  | store t a b k =>
    refine twoArgs a b hargs.1 hargs.2 ?_ ?_ hge
    · intro idx heq hesc0; subst heq
      refine hD _ (hvid_lt_of_idx (hargs.1 idx rfl)) hesc0 ?_
      dsimp only [nodeArgsUses0]; rw [argUses0_var_self6]; exact Nat.add_pos_left Nat.one_pos _
    · intro idx heq hesc0; subst heq
      refine hD _ (hvid_lt_of_idx (hargs.2 idx rfl)) hesc0 ?_
      dsimp only [nodeArgsUses0]; rw [argUses0_var_self6]; exact Nat.add_pos_right _ Nat.one_pos
  | load t addr k =>
    refine releaseArg0_spec esc vslot venv res addr nextVid nxt hnv32 D hsz hvlt hargs ?_
      hesc hbd hge hvok hnd hflt
    intro idx heq hesc0; subst heq
    refine hD _ (hvid_lt_of_idx (hargs idx rfl)) hesc0 ?_
    dsimp only [nodeArgsUses0]; rw [argUses0_var_self6]; exact Nat.one_pos
  | jnz _ _ _ => exact absurd rfl (hnj _ _ _)
  | group _ _ => exact absurd rfl (hng _ _)
  | tailCall _ _ _ | jump _ _ | ret _ | exit _ _ _ | hlt => simp [isTerm0] at hlin

private theorem bindOneSlot0_spec (esc : Array Nat) (reg : Reg64) (st : RegaSt0)
    (free : List UInt32) (nxt : UInt32) (maxBd : Nat)
    (hvsz : st.vslot.size = st.nextVid.toNat) (hnv_lt : st.nextVid.toNat + 1 < 2 ^ 32)
    (hpool : SlotPoolInv0 free nxt st.maxSlots maxBd) (hnxt_lt : nxt.toNat + 1 ≤ maxBd)
    (hesc_lt : esc.getD st.nextVid.toNat 0 < 2 ^ 32)
    (hrem_lt : st.remUses.getD st.nextVid.toNat 0 < 2 ^ 32) :
    let bo := bindOneSlot0 esc reg st free nxt
    bo.vid = st.nextVid ∧
    bo.st.nextVid.toNat = st.nextVid.toNat + 1 ∧
    bo.st.vslot.size = st.nextVid.toNat + 1 ∧
    bo.st.remUses = st.remUses ∧
    SlotPoolInv0 bo.free bo.nxt bo.st.maxSlots maxBd ∧
    nxt.toNat ≤ bo.nxt.toNat ∧ bo.nxt.toNat ≤ nxt.toNat + 1 ∧
    (0 < st.remUses.getD st.nextVid.toNat 0 ∨ 0 < esc.getD st.nextVid.toNat 0 →
      (arrGetU0 bo.st.vslot st.nextVid).toNat < bo.nxt.toNat ∧
      arrGetU0 bo.st.vslot st.nextVid ∉ bo.free ∧
      (arrGetU0 bo.st.vslot st.nextVid ∈ free ∨ arrGetU0 bo.st.vslot st.nextVid = nxt)) ∧
    (∀ x, x ∈ bo.free → x ∈ free) ∧
    (∀ v < st.nextVid.toNat, arrGetU0 bo.st.vslot (UInt32.ofNat v) =
      arrGetU0 st.vslot (UInt32.ofNat v)) := by
  have hnv1 : (st.nextVid + 1).toNat = st.nextVid.toNat + 1 := u32_add1_toNat6 hnv_lt
  have hrem_u := arrGetU0_of_lt6 st.remUses st.nextVid hrem_lt
  have hesc_u := arrGetU0_of_lt6 esc st.nextVid hesc_lt
  have hneed_iff : ((decide (0 < arrGetU0 st.remUses st.nextVid) ||
      decide (0 < arrGetU0 esc st.nextVid)) = true) ↔
      (0 < st.remUses.getD st.nextVid.toNat 0 ∨ 0 < esc.getD st.nextVid.toNat 0) := by
    simp only [Bool.or_eq_true, decide_eq_true_eq, UInt32.lt_iff_toNat_lt, UInt32.toNat_zero,
      hrem_u, hesc_u]
  dsimp only [bindOneSlot0]
  by_cases hn : (decide (0 < arrGetU0 st.remUses st.nextVid) ||
      decide (0 < arrGetU0 esc st.nextVid)) = true
  · simp only [hn, ↓reduceIte]
    have hsp := allocSlot0_spec free nxt st.maxSlots maxBd hpool hnxt_lt
    dsimp only at hsp
    let sp := allocSlot0 free nxt st.maxSlots
    have hslot_eq : arrGetU0 (st.vslot.push sp.slot.toNat) st.nextVid = sp.slot := by
      apply u32_ext6
      dsimp only [arrGetU0]
      rw [u32_toNat_ofNat6, arrPush_getD6, hvsz]
      simp [Nat.mod_eq_of_lt (UInt32.toNat_lt sp.slot)]
    refine ⟨by first | exact rfl | exact trivial, hnv1, by rw [Array.size_push, hvsz],
      by first | exact rfl | exact trivial, hsp.1, hsp.2.2.1, hsp.2.2.2.1,
      fun _ => by rw [hslot_eq]; refine ⟨hsp.2.1, fun hm => ((hsp.2.2.2.2.2 sp.slot).mp hm).2 rfl,
        hsp.2.2.2.2.1⟩,
      fun x hx => ((hsp.2.2.2.2.2 x).mp hx).1, fun v hv => ?_⟩
    have hv_eq : (UInt32.ofNat v).toNat = v := by
      rw [u32_toNat_ofNat6, Nat.mod_eq_of_lt (by omega)]
    dsimp only [arrGetU0]
    rw [arrPush_getD6, hvsz, hv_eq]
    simp [hv]
  · have hneed : ¬ (0 < st.remUses.getD st.nextVid.toNat 0 ∨ 0 < esc.getD st.nextVid.toNat 0) :=
      fun h => hn (hneed_iff.mpr h)
    simp only [hn, Bool.false_eq_true, ↓reduceIte]
    refine ⟨by first | exact rfl | exact trivial, hnv1, by rw [Array.size_push, hvsz],
      by first | exact rfl | exact trivial, hpool, Nat.le_refl _,
      Nat.le_add_right _ _, fun h => absurd h hneed, fun _ hx => hx, fun v hv => ?_⟩
    have hv_eq : (UInt32.ofNat v).toNat = v := by
      rw [u32_toNat_ofNat6, Nat.mod_eq_of_lt (by omega)]
    dsimp only [arrGetU0]
    rw [arrPush_getD6, hvsz, hv_eq]
    simp [hv]

private theorem bindRetsN0_zero6 (esc : Array Nat) (idx : UInt32) (bl : BindListOut0) :
    bindRetsN0 esc 0 idx bl = bl := by
  rw [bindRetsN0.eq_def]; simp

private theorem bindRetsN0_succ6 (esc : Array Nat) {rem idx : UInt32} (hr : rem ≠ 0)
    (bl : BindListOut0) :
    bindRetsN0 esc rem idx bl =
      let bo := bindOneSlot0 esc (abiRegAt0 true idx) bl.st bl.free bl.nxt
      bindRetsN0 esc (rem - 1) (idx + 1) ⟨bo.vid :: bl.venv, bo.st, bo.free, bo.nxt⟩ := by
  have h := bindRetsN0.eq_def esc rem idx bl; simp only [hr, ↓reduceDIte] at h; exact h

theorem bindRetsN0_spec (esc : Array Nat) :
    ∀ (m : Nat) (rem idx : UInt32) (bl : BindListOut0) (maxBd : Nat),
      rem.toNat = m → bl.st.vslot.size = bl.st.nextVid.toNat →
      bl.st.nextVid.toNat + m < 2 ^ 31 →
      SlotPoolInv0 bl.free bl.nxt bl.st.maxSlots maxBd →
      bl.nxt.toNat + m ≤ maxBd →
      (∀ k < m, esc.getD (bl.st.nextVid.toNat + k) 0 < 2 ^ 32 ∧
        bl.st.remUses.getD (bl.st.nextVid.toNat + k) 0 < 2 ^ 32) →
      let bl' := bindRetsN0 esc rem idx bl
      bl'.venv = pushFreshVids0 m bl.st.nextVid bl.venv ∧
      bl'.st.nextVid.toNat = bl.st.nextVid.toNat + m ∧
      bl'.st.vslot.size = bl.st.nextVid.toNat + m ∧
      bl'.st.remUses = bl.st.remUses ∧
      SlotPoolInv0 bl'.free bl'.nxt bl'.st.maxSlots maxBd ∧
      bl.nxt.toNat ≤ bl'.nxt.toNat ∧ bl'.nxt.toNat ≤ bl.nxt.toNat + m ∧
      (∀ x, x ∈ bl'.free → x ∈ bl.free) ∧
      (∀ v < bl.st.nextVid.toNat, arrGetU0 bl'.st.vslot (UInt32.ofNat v) =
        arrGetU0 bl.st.vslot (UInt32.ofNat v)) ∧
      (∀ k < m,
        (0 < bl.st.remUses.getD (bl.st.nextVid.toNat + k) 0 ∨
          0 < esc.getD (bl.st.nextVid.toNat + k) 0) →
        (arrGetU0 bl'.st.vslot (UInt32.ofNat (bl.st.nextVid.toNat + k))).toNat < bl'.nxt.toNat ∧
        arrGetU0 bl'.st.vslot (UInt32.ofNat (bl.st.nextVid.toNat + k)) ∉ bl'.free ∧
        (arrGetU0 bl'.st.vslot (UInt32.ofNat (bl.st.nextVid.toNat + k)) ∈ bl.free ∨
          bl.nxt.toNat ≤ (arrGetU0 bl'.st.vslot (UInt32.ofNat (bl.st.nextVid.toNat + k))).toNat) ∧
        ∀ j < k,
          (0 < bl.st.remUses.getD (bl.st.nextVid.toNat + j) 0 ∨
            0 < esc.getD (bl.st.nextVid.toNat + j) 0) →
          arrGetU0 bl'.st.vslot (UInt32.ofNat (bl.st.nextVid.toNat + j)) ≠
            arrGetU0 bl'.st.vslot (UInt32.ofNat (bl.st.nextVid.toNat + k))) := by
  intro m
  induction m with
  | zero =>
    intro rem idx bl maxBd hrem hvsz hnv hpool hnxt hlt
    have hr0 : rem = 0 := u32_ext6 hrem
    subst hr0; dsimp only; rw [bindRetsN0_zero6]
    exact ⟨rfl, rfl, hvsz, rfl, hpool, Nat.le_refl _, Nat.le_refl _, fun _ h => h,
      fun _ _ => rfl, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ m ih =>
    intro rem idx bl maxBd hrem hvsz hnv hpool hnxt hlt
    have hne : rem ≠ 0 := fun h => by subst h; simp at hrem
    have hsub : (rem - 1).toNat = m := by rw [u32_sub1_toNat6 (by omega), hrem]; omega
    dsimp only; rw [bindRetsN0_succ6 esc hne]; dsimp only
    let bo := bindOneSlot0 esc (abiRegAt0 true idx) bl.st bl.free bl.nxt
    have h1 := bindOneSlot0_spec esc (abiRegAt0 true idx) bl.st bl.free bl.nxt maxBd hvsz
      (by omega) hpool (by omega) (hlt 0 (Nat.zero_lt_succ m)).1 (hlt 0 (Nat.zero_lt_succ m)).2
    dsimp only at h1
    obtain ⟨h1_vid, h1_nv, h1_vsz, h1_rem, h1_pool, h1_nlo, h1_nhi, h1_sl, h1_fr, h1_pres⟩ := h1
    let bl1 : BindListOut0 := ⟨bo.vid :: bl.venv, bo.st, bo.free, bo.nxt⟩
    have h2 := ih (rem - 1) (idx + 1) bl1 maxBd hsub
      (by dsimp only [bl1, bo]; rw [h1_nv, h1_vsz])
      (by dsimp only [bl1, bo]; rw [h1_nv]; omega) h1_pool
      (by dsimp only [bl1, bo]; omega)
      (fun k hk => by
        dsimp only [bl1, bo]
        rw [h1_nv, h1_rem, Nat.add_assoc, Nat.add_comm 1 k]
        exact hlt (k + 1) (by omega))
    dsimp only [bl1, bo] at h2
    obtain ⟨h2_venv, h2_nv, h2_vsz, h2_rem, h2_pool, h2_nlo, h2_nhi, h2_fr, h2_pres, h2_sl⟩ := h2
    have hnv_1lt : bl.st.nextVid.toNat + 1 < 2 ^ 32 :=
      Nat.lt_trans (Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_add_left 1 m) _) hnv)
        (by decide)
    have hbo_nv : bo.st.nextVid = bl.st.nextVid + 1 :=
      u32_eq_add_of_toNat6 (by dsimp only [bo]; exact h1_nv) hnv_1lt
    have hvenv_eq : pushFreshVids0 m bo.st.nextVid (bo.vid :: bl.venv) =
        pushFreshVids0 (m + 1) bl.st.nextVid bl.venv := by
      dsimp only [bo] at hbo_nv ⊢; rw [h1_vid, hbo_nv]; dsimp only [pushFreshVids0]
    dsimp only [bo] at hvenv_eq
    refine ⟨by rw [h2_venv, ← hvenv_eq], by rw [h2_nv, h1_nv]; omega,
      by rw [h2_vsz, h1_nv]; omega, h2_rem.trans h1_rem,
      h2_pool, Nat.le_trans h1_nlo h2_nlo, by omega,
      fun x hx => h1_fr x (h2_fr x hx),
      fun v hv => (h2_pres v (by rw [h1_nv]; omega)).trans (h1_pres v hv),
      fun k hk hneed => ?_⟩
    cases k with
    | zero =>
      simp only [Nat.add_zero, UInt32.ofNat_toNat] at hneed ⊢
      have h0 := h1_sl hneed
      have hpres := h2_pres bl.st.nextVid.toNat (by rw [h1_nv]; omega)
      simp only [UInt32.ofNat_toNat] at hpres
      rw [hpres]
      refine ⟨Nat.lt_of_lt_of_le h0.1 h2_nlo,
        fun hm => h0.2.1 (h2_fr _ hm), ?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
      rcases h0.2.2 with hm | heq
      · exact Or.inl hm
      · right; rw [heq]; exact Nat.le_refl _
    | succ k' =>
      have hk2 := h2_sl k' (Nat.lt_of_succ_lt_succ hk) (by
        rw [h1_nv, h1_rem, Nat.add_assoc, Nat.add_comm 1 k']
        exact hneed)
      rw [h1_nv, Nat.add_assoc, Nat.add_comm 1 k'] at hk2
      refine ⟨hk2.1, hk2.2.1, ?_, fun j hj hneed_j => ?_⟩
      · rcases hk2.2.2.1 with hm | hge
        · exact Or.inl (h1_fr _ hm)
        · right; omega
      · cases j with
        | zero =>
          simp only [Nat.add_zero, UInt32.ofNat_toNat] at hneed_j ⊢
          have h0 := h1_sl hneed_j
          have hpres := h2_pres bl.st.nextVid.toNat (by rw [h1_nv]; omega)
          simp only [UInt32.ofNat_toNat] at hpres
          rw [hpres]
          intro hcol
          rcases h0.2.2 with hm0 | heq0 <;> rcases hk2.2.2.1 with hmk | hgek
          · exact h0.2.1 (hcol ▸ hmk)
          · have hlt0 := hpool.2.1 _ hm0
            rw [← hcol] at hgek; omega
          · rw [← hcol, heq0] at hmk
            exact Nat.lt_irrefl _ (hpool.2.1 _ (h1_fr _ hmk))
          · rw [heq0] at h0; rw [← hcol, heq0] at hgek; omega
        | succ j' =>
          have hj2 := hk2.2.2.2 j' (Nat.lt_of_succ_lt_succ hj) (by
            rw [h1_rem, Nat.add_assoc, Nat.add_comm 1 j']; exact hneed_j)
          rw [Nat.add_assoc, Nat.add_comm 1 j'] at hj2
          exact hj2

private theorem bindOneBlockSlot0_spec (st : RegaSt0) (free : List UInt32) (nxt : UInt32)
    (maxBd : Nat) (hvsz : st.vslot.size = st.nextVid.toNat) (hnv_lt : st.nextVid.toNat + 1 < 2 ^ 32)
    (hpool : SlotPoolInv0 free nxt st.maxSlots maxBd) (hnxt_lt : nxt.toNat + 1 ≤ maxBd) :
    let bo := bindOneBlockSlot0 st free nxt
    bo.vid = st.nextVid ∧ bo.st.nextVid.toNat = st.nextVid.toNat + 1 ∧
    bo.st.vslot.size = st.nextVid.toNat + 1 ∧ bo.st.remUses = st.remUses ∧
    bo.st.revDirs = st.revDirs ∧
    SlotPoolInv0 bo.free bo.nxt bo.st.maxSlots maxBd ∧
    nxt.toNat ≤ bo.nxt.toNat ∧ bo.nxt.toNat ≤ nxt.toNat + 1 ∧
    (arrGetU0 bo.st.vslot st.nextVid).toNat < bo.nxt.toNat ∧
    arrGetU0 bo.st.vslot st.nextVid ∉ bo.free ∧
    (arrGetU0 bo.st.vslot st.nextVid ∈ free ∨ arrGetU0 bo.st.vslot st.nextVid = nxt) ∧
    (∀ x, x ∈ bo.free → x ∈ free) ∧
    (∀ v < st.nextVid.toNat, arrGetU0 bo.st.vslot (UInt32.ofNat v) =
      arrGetU0 st.vslot (UInt32.ofNat v)) := by
  have hnv1 : (st.nextVid + 1).toNat = st.nextVid.toNat + 1 := u32_add1_toNat6 hnv_lt
  dsimp only [bindOneBlockSlot0]
  have hsp := allocSlot0_spec free nxt st.maxSlots maxBd hpool hnxt_lt
  dsimp only at hsp
  let sp := allocSlot0 free nxt st.maxSlots
  have hslot_eq : arrGetU0 (st.vslot.push sp.slot.toNat) st.nextVid = sp.slot := by
    apply u32_ext6; dsimp only [arrGetU0]
    rw [u32_toNat_ofNat6, arrPush_getD6, hvsz]
    simp [Nat.mod_eq_of_lt (UInt32.toNat_lt sp.slot)]
  refine ⟨rfl, hnv1, by rw [Array.size_push, hvsz], rfl, rfl,
    hsp.1, hsp.2.2.1, hsp.2.2.2.1, ?_, ?_, ?_, fun x hx => ((hsp.2.2.2.2.2 x).mp hx).1, ?_⟩
  · rw [hslot_eq]; exact hsp.2.1
  · rw [hslot_eq]; exact fun hm => ((hsp.2.2.2.2.2 sp.slot).mp hm).2 rfl
  · rw [hslot_eq]; exact hsp.2.2.2.2.1
  · intro v hv
    have hv_eq : (UInt32.ofNat v).toNat = v := by
      rw [u32_toNat_ofNat6, Nat.mod_eq_of_lt (by omega)]
    dsimp only [arrGetU0]; rw [arrPush_getD6, hvsz, hv_eq]; simp [hv]

theorem pushFreshVids0_succ_head (m : Nat) (nv : UInt32) (venv : List UInt32) :
    pushFreshVids0 (m + 1) nv venv = (nv + UInt32.ofNat m) :: pushFreshVids0 m nv venv := by
  induction m generalizing nv venv with
  | zero => dsimp only [pushFreshVids0]; rw [u32_add_zero6]
  | succ m' ih =>
    change pushFreshVids0 (m' + 1) (nv + 1) (nv :: venv) =
      (nv + UInt32.ofNat (m' + 1)) :: pushFreshVids0 (m' + 1) nv venv
    rw [ih (nv + 1) (nv :: venv)]
    congr 1
    apply u32_ext6
    rw [UInt32.toNat_add, UInt32.toNat_add, UInt32.toNat_add, UInt32.toNat_one,
      u32_toNat_ofNat6, u32_toNat_ofNat6,
      Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_mod_mod, Nat.add_assoc, Nat.add_comm 1 m']

private theorem slotsOfVids0_zero6 (venv : List UInt32) (vslot : Array Nat) (acc : List UInt32) :
    slotsOfVids0 0 venv vslot acc = acc := by
  rw [slotsOfVids0.eq_def]; simp

private theorem slotsOfVids0_succ6 {n : UInt32} (hn : n ≠ 0) (vid : UInt32) (rest : List UInt32)
    (vslot : Array Nat) (acc : List UInt32) :
    slotsOfVids0 n (vid :: rest) vslot acc =
      slotsOfVids0 (n - 1) rest vslot (arrGetU0 vslot vid :: acc) := by
  have h := slotsOfVids0.eq_def n (vid :: rest) vslot acc
  simp only [hn, ↓reduceDIte] at h
  exact h

theorem slotsOfVids0_pushFreshVids0 :
    ∀ (m : Nat) (n nv : UInt32) (venv : List UInt32) (vslot : Array Nat) (acc : List UInt32),
      n.toNat = m → nv.toNat + m < 2 ^ 32 →
      slotsOfVids0 n (pushFreshVids0 m nv venv) vslot acc =
        (List.range m).map (fun k => arrGetU0 vslot (nv + UInt32.ofNat k)) ++ acc
  | 0, n, nv, venv, vslot, acc, hn, _ => by
    have hn0 : n = 0 := u32_ext6 hn; subst hn0; simp [slotsOfVids0_zero6]
  | m + 1, n, nv, venv, vslot, acc, hn, hlt => by
    have hne : n ≠ 0 := fun h => by subst h; simp at hn
    have hsub : (n - 1).toNat = m := by rw [u32_sub1_toNat6 (by omega), hn]; omega
    rw [pushFreshVids0_succ_head, slotsOfVids0_succ6 hne]
    rw [slotsOfVids0_pushFreshVids0 m (n - 1) nv venv vslot _ hsub (by omega)]
    rw [List.range_succ, List.map_append, List.map_singleton, List.append_assoc,
      List.singleton_append]

theorem bindBlockParams0_spec :
    ∀ (pts : List Ty0) (venv : List UInt32) (st : RegaSt0) (free : List UInt32) (nxt : UInt32)
      (maxBd : Nat),
      st.vslot.size = st.nextVid.toNat → st.nextVid.toNat + pts.length < 2 ^ 31 →
      SlotPoolInv0 free nxt st.maxSlots maxBd → nxt.toNat + pts.length ≤ maxBd →
      let bb := bindBlockParams0 pts venv st free nxt
      bb.venv = pushFreshVids0 pts.length st.nextVid venv ∧
      bb.st.nextVid.toNat = st.nextVid.toNat + pts.length ∧
      bb.st.vslot.size = st.nextVid.toNat + pts.length ∧
      bb.st.remUses = st.remUses ∧ bb.st.revDirs = st.revDirs ∧
      SlotPoolInv0 bb.free bb.nxt bb.st.maxSlots maxBd ∧
      nxt.toNat ≤ bb.nxt.toNat ∧ bb.nxt.toNat ≤ nxt.toNat + pts.length ∧
      (∀ x, x ∈ bb.free → x ∈ free) ∧
      (∀ v < st.nextVid.toNat, arrGetU0 bb.st.vslot (UInt32.ofNat v) =
        arrGetU0 st.vslot (UInt32.ofNat v)) ∧
      (∀ k < pts.length,
        (arrGetU0 bb.st.vslot (st.nextVid + UInt32.ofNat k)).toNat < bb.nxt.toNat ∧
        arrGetU0 bb.st.vslot (st.nextVid + UInt32.ofNat k) ∉ bb.free ∧
        (arrGetU0 bb.st.vslot (st.nextVid + UInt32.ofNat k) ∈ free ∨
          nxt.toNat ≤ (arrGetU0 bb.st.vslot (st.nextVid + UInt32.ofNat k)).toNat) ∧
        ∀ j < k, arrGetU0 bb.st.vslot (st.nextVid + UInt32.ofNat j) ≠
          arrGetU0 bb.st.vslot (st.nextVid + UInt32.ofNat k))
  | [], venv, st, free, nxt, _, hvsz, _, hpool, _ =>
    ⟨rfl, rfl, hvsz, rfl, rfl, hpool, Nat.le_refl _, Nat.le_refl _, fun _ h => h,
      fun _ _ => rfl, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | _ :: rest, venv, st, free, nxt, maxBd, hvsz, hnv, hpool, hnxt => by
    simp only [List.length_cons] at hnv hnxt ⊢
    dsimp only [bindBlockParams0]
    let bo := bindOneBlockSlot0 st free nxt
    have h1 := bindOneBlockSlot0_spec st free nxt maxBd hvsz (by omega) hpool (by omega)
    dsimp only at h1
    obtain ⟨h1_vid, h1_nv, h1_vsz, h1_rem, h1_rev, h1_pool, h1_nlo, h1_nhi,
      h1_slt, h1_snf, h1_sorg, h1_fr, h1_pres⟩ := h1
    have h2 := bindBlockParams0_spec rest (bo.vid :: venv) bo.st bo.free bo.nxt maxBd
      (by dsimp only [bo]; rw [h1_nv, h1_vsz])
      (by dsimp only [bo]; rw [h1_nv]; omega) h1_pool (by dsimp only [bo]; omega)
    dsimp only [bo] at h2
    obtain ⟨h2_venv, h2_nv, h2_vsz, h2_rem, h2_rev, h2_pool, h2_nlo, h2_nhi,
      h2_fr, h2_pres, h2_sl⟩ := h2
    have hnv_1lt : st.nextVid.toNat + 1 < 2 ^ 32 :=
      Nat.lt_trans (Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_add_left 1 rest.length) _) hnv)
        (by decide)
    have hnv1 : (bindOneBlockSlot0 st free nxt).st.nextVid = st.nextVid + 1 :=
      u32_eq_add_of_toNat6 h1_nv hnv_1lt
    have hnv1_nat : (st.nextVid + 1).toNat = st.nextVid.toNat + 1 := u32_add1_toNat6 hnv_1lt
    have hvenv_eq : pushFreshVids0 rest.length (bindOneBlockSlot0 st free nxt).st.nextVid
        ((bindOneBlockSlot0 st free nxt).vid :: venv) =
        pushFreshVids0 (rest.length + 1) st.nextVid venv := by
      rw [h1_vid, hnv1]; dsimp only [pushFreshVids0]
    refine ⟨by rw [h2_venv, ← hvenv_eq],
      by rw [h2_nv, h1_nv]; omega,
      by rw [h2_vsz, h1_nv]; omega,
      h2_rem.trans h1_rem,
      h2_rev.trans h1_rev,
      h2_pool, Nat.le_trans h1_nlo h2_nlo, by omega,
      fun x hx => h1_fr x (h2_fr x hx),
      fun v hv => (h2_pres v (by rw [h1_nv]; omega)).trans (h1_pres v hv),
      fun k hk => ?_⟩
    cases k with
    | zero =>
      rw [u32_add_zero6]
      have hpres := h2_pres st.nextVid.toNat (by rw [h1_nv]; omega)
      simp only [UInt32.ofNat_toNat] at hpres
      rw [hpres]
      refine ⟨Nat.lt_of_lt_of_le h1_slt h2_nlo,
        fun hm => h1_snf (h2_fr _ hm), ?_,
        fun j hj => absurd hj (Nat.not_lt_zero _)⟩
      rcases h1_sorg with hm | heq
      · exact Or.inl hm
      · right; rw [heq]; exact Nat.le_refl _
    | succ k' =>
      have hk2 := h2_sl k' (Nat.lt_of_succ_lt_succ hk)
      have heq_idx : (bindOneBlockSlot0 st free nxt).st.nextVid + UInt32.ofNat k' =
          st.nextVid + UInt32.ofNat (k' + 1) := by
        rw [hnv1]; apply u32_ext6
        rw [u32_add_ofNat_lt6 (by omega), u32_add_ofNat_lt6 (by omega), hnv1_nat]; omega
      rw [heq_idx] at hk2
      refine ⟨hk2.1, hk2.2.1, ?_, fun j hj => ?_⟩
      · rcases hk2.2.2.1 with hm | hge
        · exact Or.inl (h1_fr _ hm)
        · right; omega
      · cases j with
        | zero =>
          rw [u32_add_zero6]
          have hpres := h2_pres st.nextVid.toNat (by rw [h1_nv]; omega)
          simp only [UInt32.ofNat_toNat] at hpres; rw [hpres]
          intro hcol
          rcases h1_sorg with hm0 | heq0 <;> rcases hk2.2.2.1 with hmk | hgek
          · exact h1_snf (hcol ▸ hmk)
          · have hlt0 := hpool.2.1 _ hm0
            rw [← hcol] at hgek; omega
          · rw [← hcol, heq0] at hmk
            exact Nat.lt_irrefl _ (hpool.2.1 _ (h1_fr _ hmk))
          · rw [heq0] at h1_slt; rw [← hcol, heq0] at hgek; omega
        | succ j' =>
          have hj2 := hk2.2.2.2 j' (Nat.lt_of_succ_lt_succ hj)
          have heq_j : (bindOneBlockSlot0 st free nxt).st.nextVid + UInt32.ofNat j' =
              st.nextVid + UInt32.ofNat (j' + 1) := by
            rw [hnv1]; apply u32_ext6
            rw [u32_add_ofNat_lt6 (by omega), u32_add_ofNat_lt6 (by omega), hnv1_nat]; omega
          rwa [heq_j] at hj2

theorem bindBlockParams0_spec_clean :
    ∀ (pts : List Ty0) (venv : List UInt32) (st : RegaSt0) (free : List UInt32) (nxt : UInt32)
      (maxBd : Nat),
      st.vslot.size = st.nextVid.toNat → st.nextVid.toNat + pts.length < 2 ^ 31 →
      SlotPoolInv0 free nxt st.maxSlots maxBd → nxt.toNat + pts.length ≤ maxBd →
      let bb := bindBlockParams0 pts venv st free nxt
      bb.venv = pushFreshVids0 pts.length st.nextVid venv ∧
      bb.st.nextVid.toNat = st.nextVid.toNat + pts.length ∧
      bb.st.vslot.size = st.nextVid.toNat + pts.length ∧
      bb.st.remUses = st.remUses ∧ bb.st.revDirs = st.revDirs ∧
      SlotPoolInv0 bb.free bb.nxt bb.st.maxSlots maxBd ∧
      nxt.toNat ≤ bb.nxt.toNat ∧ bb.nxt.toNat ≤ nxt.toNat + pts.length ∧
      (∀ x, x ∈ bb.free → x ∈ free) ∧
      (∀ v < st.nextVid.toNat, arrGetU0 bb.st.vslot (UInt32.ofNat v) =
        arrGetU0 st.vslot (UInt32.ofNat v)) ∧
      (∀ k < pts.length,
        (arrGetU0 bb.st.vslot (st.nextVid + UInt32.ofNat k)).toNat < bb.nxt.toNat ∧
        arrGetU0 bb.st.vslot (st.nextVid + UInt32.ofNat k) ∉ bb.free ∧
        (arrGetU0 bb.st.vslot (st.nextVid + UInt32.ofNat k) ∈ free ∨
          nxt.toNat ≤ (arrGetU0 bb.st.vslot (st.nextVid + UInt32.ofNat k)).toNat) ∧
        ∀ j < k, arrGetU0 bb.st.vslot (st.nextVid + UInt32.ofNat j) ≠
          arrGetU0 bb.st.vslot (st.nextVid + UInt32.ofNat k)) :=
  fun pts venv st free nxt maxBd hv hnv hp hnx =>
    bindBlockParams0_spec pts venv st free nxt maxBd hv hnv hp hnx

theorem bindEntryArgs0_spec :
    ∀ (ts : List Ty0) (i : UInt32) (venv : List UInt32) (st : RegaSt0) (maxBd : Nat),
      st.vslot.size = st.nextVid.toNat → st.nextVid = i →
      i.toNat + ts.length ≤ maxBd → maxBd < 2 ^ 31 →
      st.maxSlots.toNat = i.toNat →
      let bl := bindEntryArgs0 ts i venv st
      bl.venv = pushFreshVids0 ts.length st.nextVid venv ∧
      bl.free = [] ∧
      bl.nxt.toNat = i.toNat + ts.length ∧
      bl.st.nextVid.toNat = i.toNat + ts.length ∧
      bl.st.vslot.size = i.toNat + ts.length ∧
      bl.st.remUses = st.remUses ∧
      SlotPoolInv0 bl.free bl.nxt bl.st.maxSlots maxBd ∧
      (∀ v < i.toNat, arrGetU0 bl.st.vslot (UInt32.ofNat v) =
        arrGetU0 st.vslot (UInt32.ofNat v)) ∧
      (∀ k < ts.length,
        arrGetU0 bl.st.vslot (UInt32.ofNat (i.toNat + k)) = UInt32.ofNat (i.toNat + k)) := by
  intro ts
  induction ts with
  | nil =>
    intro i venv st maxBd hvsz hnv hbd hmax hms
    dsimp only [bindEntryArgs0, pushFreshVids0]; rw [List.length_nil, Nat.add_zero]
    refine ⟨rfl, rfl, rfl, by rw [hnv], by rw [hvsz, hnv], rfl,
      ⟨List.nodup_nil, fun _ h => by simp at h, by omega, by omega, hmax⟩,
      fun _ _ => rfl, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | cons t rest ih =>
    intro i venv st maxBd hvsz hnv hbd hmax hms
    simp only [List.length_cons] at hbd ⊢
    have hi1 : (i + 1).toNat = i.toNat + 1 := u32_add1_toNat6 (by omega)
    let st1 := bindOneEntryArg0 i t st
    have hms1 : st1.maxSlots.toNat = (i + 1).toNat := by
      dsimp only [st1, bindOneEntryArg0]; rw [u32Max0_toNat, hi1, hms]
      exact Nat.max_eq_right (Nat.le_succ _)
    have hih := ih (i + 1) (st.nextVid :: venv) st1 maxBd
      (by dsimp only [st1, bindOneEntryArg0]; rw [Array.size_push, hvsz, hnv, hi1])
      (by dsimp only [st1, bindOneEntryArg0]; rw [hnv])
      (by rw [hi1]; omega) hmax hms1
    dsimp only [bindEntryArgs0, pushFreshVids0] at hih ⊢
    have hnv1 : st1.nextVid = st.nextVid + 1 := rfl
    have heq_v : pushFreshVids0 rest.length st1.nextVid (st.nextVid :: venv) =
        pushFreshVids0 rest.length (st.nextVid + 1) (st.nextVid :: venv) := rfl
    refine ⟨hih.1.trans heq_v, hih.2.1, by rw [hih.2.2.1, hi1]; omega,
      by rw [hih.2.2.2.1, hi1]; omega, by rw [hih.2.2.2.2.1, hi1]; omega,
      hih.2.2.2.2.2.1, hih.2.2.2.2.2.2.1, fun v hv => ?_, fun k hk => ?_⟩
    · have hp := hih.2.2.2.2.2.2.2.1 v (by rw [hi1]; omega)
      rw [hp]
      dsimp only [st1, bindOneEntryArg0, arrGetU0]
      rw [arrPush_getD6, hvsz, hnv, u32_toNat_ofNat6, Nat.mod_eq_of_lt (by omega)]
      simp [hv]
    · cases k with
      | zero =>
        simp only [Nat.add_zero]
        have hp := hih.2.2.2.2.2.2.2.1 i.toNat (by rw [hi1]; omega)
        rw [hp]
        dsimp only [st1, bindOneEntryArg0, arrGetU0]
        rw [arrPush_getD6, hvsz, hnv, u32_toNat_ofNat6, Nat.mod_eq_of_lt (by omega)]
        simp
      | succ k' =>
        have hk2 := hih.2.2.2.2.2.2.2.2 k' (Nat.lt_of_succ_lt_succ hk)
        rw [hi1, Nat.add_assoc, show 1 + k' = k' + 1 from Nat.add_comm 1 k'] at hk2
        exact hk2

private theorem allocSlot0_maxSlots_le (free : List UInt32) (nxt maxSl : UInt32) :
    maxSl.toNat ≤ (allocSlot0 free nxt maxSl).maxSlots.toNat := by
  cases free <;> simp [allocSlot0, u32Max0_toNat, Nat.le_max_left]

private theorem bindOneSlot0_maxSlots_le (esc : Array Nat) (reg : Reg64) (st : RegaSt0)
    (free : List UInt32) (nxt : UInt32) :
    st.maxSlots.toNat ≤ (bindOneSlot0 esc reg st free nxt).st.maxSlots.toNat := by
  dsimp only [bindOneSlot0]; split
  · exact allocSlot0_maxSlots_le free nxt st.maxSlots
  · exact Nat.le_refl _

theorem bindRetsN0_maxSlots_le (esc : Array Nat) :
    ∀ (m : Nat) (rem idx : UInt32) (bl : BindListOut0),
      rem.toNat = m → bl.st.maxSlots.toNat ≤ (bindRetsN0 esc rem idx bl).st.maxSlots.toNat
  | 0, rem, idx, bl, hrem => by
    have hr0 : rem = 0 := u32_ext6 hrem
    subst hr0; rw [bindRetsN0_zero6]; exact Nat.le_refl _
  | m + 1, rem, idx, bl, hrem => by
    have hne : rem ≠ 0 := fun h => by subst h; simp at hrem
    have hsub : (rem - 1).toNat = m := by rw [u32_sub1_toNat6 (by omega), hrem]; omega
    let bo := bindOneSlot0 esc (abiRegAt0 true idx) bl.st bl.free bl.nxt
    rw [bindRetsN0_succ6 esc hne]
    exact Nat.le_trans (bindOneSlot0_maxSlots_le esc (abiRegAt0 true idx) bl.st bl.free bl.nxt)
      (bindRetsN0_maxSlots_le esc m (rem - 1) (idx + 1)
        ⟨bo.vid :: bl.venv, bo.st, bo.free, bo.nxt⟩ hsub)

private theorem bindOneBlockSlot0_maxSlots_le (st : RegaSt0) (free : List UInt32)
    (nxt : UInt32) :
    st.maxSlots.toNat ≤ (bindOneBlockSlot0 st free nxt).st.maxSlots.toNat :=
  allocSlot0_maxSlots_le free nxt st.maxSlots

theorem bindBlockParams0_maxSlots_le :
    ∀ (pts : List Ty0) (venv : List UInt32) (st : RegaSt0) (free : List UInt32) (nxt : UInt32),
      st.maxSlots.toNat ≤ (bindBlockParams0 pts venv st free nxt).st.maxSlots.toNat
  | [], _, st, _, _ => Nat.le_refl _
  | _ :: rest, venv, st, free, nxt => by
    dsimp only [bindBlockParams0]
    let bo := bindOneBlockSlot0 st free nxt
    exact Nat.le_trans (bindOneBlockSlot0_maxSlots_le st free nxt)
      (bindBlockParams0_maxSlots_le rest (bo.vid :: venv) bo.st bo.free bo.nxt)

end LeanQbe.T.Bootstrap0
