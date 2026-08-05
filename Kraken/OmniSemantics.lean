/-
Kraken - Proof Tactics

Core tactics and theorems for stepping through assembly proofs.
Compatible with Lean 4.22.0+.

For semantics, see Kraken/Semantics.lean.
For advanced tactics (SymM), see kraken-experimental/KrakenExp/Tactics.lean.
-/

import Kraken.Semantics

-- PROOF INFRASTRUCTURE

abbrev Post {State : Type} := State → Prop

@[kstep] def Effects.All (post : MachineState → Prop) : Effects → Prop
  | .done a => post a
  | .unimplemented _ => False
  | .nonmem_load .. => False
  | .nonmem_store .. => False
  | @Effects.undefined α _ cont => ∀ v: α, (cont v).All post
  | .require_read_access _ _ cont => (cont ()).All post
  | .require_write_access _ _ cont => (cont ()).All post
  | .require_exec_access _ cont => (cont ()).All post

-- NOTE: 'initial' cannot be moved to the left of the colon as a parameter
-- because it varies in the recursive call in the 'step' constructor (it becomes 'mid').
inductive Eventually {State : Type} (trans : State → Post → Prop) (post : Post) : Post
  | done (initial: State):
      post initial →
      Eventually trans post initial
  | step (initial: State):
      (mid_p: Post) →
      trans initial mid_p →
      (forall (mid: State), mid_p mid → Eventually trans post mid) →
      Eventually trans post initial

theorem step_cps {State : Type} (trans : State → Post → Prop) (post : Post) (initial : State) :
  trans initial (fun mid => Eventually trans post mid) → Eventually trans post initial :=
  fun h => Eventually.step initial _ h (fun _ h => h)

theorem eventually_trans {State : Type} (trans : State → Post → Prop) (p q : Post) (initial : State)
  (e : Eventually trans p initial)
  (h : ∀ s, p s → Eventually trans q s) :
    Eventually trans q initial
  := by
    induction e with
    | done =>
        grind
    | step initial mid_p step_hyp rest_hyp ind_h =>
        apply Eventually.step
        <;> assumption

theorem eventually_weaken {State : Type} (trans : State → Post → Prop) (p q : Post) (initial : State)
  (h : ∀ s, p s → q s) :
    Eventually trans p initial → Eventually trans q initial
  := by
    intro hp
    induction ih: hp  -- Q: why does this not work with `induction ... with`?
    . apply Eventually.done
      grind
    . apply Eventually.step
      <;> try assumption
      grind

-- A loop down to 0
theorem reg_dec_loop {State : Type} (trans : State → Post → Prop) (post : Post) (initial : State) (invariant : Nat → Post) (n : Nat) :
  -- if:
  -- invariant holds before entering the loop
  invariant n initial ∧
  -- final iteration allows proving `post`
  (∀ state, invariant 0 state → Eventually trans post state) ∧
  -- while iterating, we eventually re-establish the invariant
  (∀ state k, k ≠ 0 → invariant k state → Eventually trans (invariant (k - 1)) state) →
  -- then: we can prove the post
  Eventually trans post initial
  := by
    intro misc
    rcases misc with ⟨ initial_invariant, case_zero, case_nonzero ⟩
    if n = 0 then
      apply case_zero
      grind
    else
      apply eventually_trans trans (invariant (n - 1)) post
      grind
      intros srec _
      apply reg_dec_loop trans post srec invariant (n - 1)
      grind

def step1 [Layout] (p: Executable) (s: MachineState) (post: @Post MachineState) : Prop :=
  (Executable.step p s .done).All post

def straightlineStep [Layout] (p: Executable) (s: MachineState) (post: @Post MachineState) : Prop :=
  (Executable.straightline p s .done).All post

theorem mem_takeWhile {α : Type} (p : α → Bool) (l : List α) (x : α) (h : x ∈ l.takeWhile p) : p x = true := by
  induction l with
  | nil => contradiction
  | cons y ys ih =>
    dsimp [List.takeWhile] at h
    split at h
    · simp only [List.mem_cons] at h
      rcases h with rfl | h
      · assumption
      · exact ih h
    · contradiction

theorem mem_dropWhile {α : Type} (p : α → Bool) (l : List α) (x : α) (h : x ∈ l.dropWhile p) : x ∈ l := by
  induction l with
  | nil => contradiction
  | cons y ys ih =>
    dsimp [List.dropWhile] at h
    split at h
    · exact List.mem_cons_of_mem y (ih h)
    · exact h

theorem head_dropWhile {α : Type} (p : α → Bool) (l : List α) (y : α) (ys : List α) (h : l.dropWhile p = y :: ys) : p y = false := by
  induction l with
  | nil => contradiction
  | cons z zs ih =>
    dsimp [List.dropWhile] at h
    split at h
    · exact ih h
    · injections
      subst y
      assumption

theorem scanl_init_eq (ds : List (Directive × Nat)) (p : Int64) (d1 d2 : Directive) (z1 z2 : Nat) :
  (List.scanl (fun (p, _, _) (d, z) => (p+.ofNat z, d, z)) (p, d1, z1) ds).map (·.1) =
  (List.scanl (fun (p, _, _) (d, z) => (p+.ofNat z, d, z)) (p, d2, z2) ds).map (·.1) := by
  cases ds with
  | nil => rfl
  | cons x xs =>
    have h1 := List.scanl_cons (f := fun (p, _, _) (d, z) => (p+.ofNat z, d, z)) (b := (p, d1, z1)) (a := x) (l := xs)
    have h2 := List.scanl_cons (f := fun (p, _, _) (d, z) => (p+.ofNat z, d, z)) (b := (p, d2, z2)) (a := x) (l := xs)
    rw [h1, h2]
    rfl

def step_addr (p : Int64 × Directive × Nat) (d : Directive × Nat) : Int64 × Directive × Nat :=
  (p.1 + Int64.ofNat d.2, d.1, d.2)

axiom step_addr_neq (st : Int64 × Directive × Nat) (d : Directive × Nat) (a : Int64) (h : st.1 ≠ a) :
  (step_addr st d).1 ≠ a

theorem scanl_no_revisit_tail (ds : List (Directive × Nat)) (st : Int64 × Directive × Nat) (a : Int64) (hst : st.1 ≠ a) :
  ∀ i ∈ List.scanl step_addr st ds, i.1 ≠ a := by
  induction ds generalizing st with
  | nil =>
    intro i hi
    rw [List.scanl_nil] at hi
    simp at hi
    subst hi
    exact hst
  | cons d ds' ih =>
    intro i hi
    rw [List.scanl_cons] at hi
    simp at hi
    rcases hi with rfl | hi_tail
    · exact hst
    · exact ih (step_addr st d) (step_addr_neq st d a hst) i hi_tail

theorem scanl_no_revisit : (ds : List (Directive × Nat)) → (st : Int64 × Directive × Nat) → (a : Int64) →
  ∀ i ∈ ((List.scanl step_addr st ds).dropWhile (fun i => i.1 ≠ a)).dropWhile (fun i => i.1 = a), i.1 ≠ a
| [], st, a => by
    intro i hi
    rw [List.scanl_nil] at hi
    dsimp [List.dropWhile] at hi
    by_cases hp : st.1 = a
    · subst hp
      simp at hi
    · simp [hp] at hi
| d :: ds', st, a => by
    intro i hi
    rw [List.scanl_cons] at hi
    dsimp [List.dropWhile] at hi
    split at hi
    · exact scanl_no_revisit ds' (step_addr st d) a i hi
    · rename_i h_st
      dsimp [List.dropWhile] at hi
      by_cases h_next : (step_addr st d).1 = a
      · cases ds' with
        | nil =>
          have h_st_eq : st.1 = a := by match h : st.1 == a with | true => exact of_decide_eq_true h | false => have h_neq := of_decide_eq_false h; have h_not_neq := of_decide_eq_false h_st; contradiction
          rw [List.scanl_nil] at hi
          simp [h_st_eq, h_next] at hi
        | cons d' ds'' =>
          have h_st_eq : st.1 = a := by match h : st.1 == a with | true => exact of_decide_eq_true h | false => have h_neq := of_decide_eq_false h; have h_not_neq := of_decide_eq_false h_st; contradiction
          simp [h_st_eq] at hi
          have ih_next := scanl_no_revisit (d' :: ds'') (step_addr st d) a i
          rw [List.scanl_cons] at ih_next
          dsimp [List.dropWhile] at ih_next
          have h_dec : (decide ¬(step_addr st d).1 = a) = false := by simp [h_next]
          rw [h_dec] at ih_next
          dsimp [List.dropWhile] at ih_next
          exact ih_next hi
      · rename_i h_next
        have h_st_eq : st.1 = a := by match h : st.1 == a with | true => exact of_decide_eq_true h | false => have h_neq := of_decide_eq_false h; have h_not_neq := of_decide_eq_false h_st; contradiction
        simp [h_st_eq] at hi
        have h_dec2 : (decide ((step_addr st d).1 = a)) = false := by simp [h_next]
        cases ds' with
        | nil =>
          rw [List.scanl_nil] at hi
          dsimp [List.dropWhile] at hi
          rw [h_dec2] at hi
          dsimp at hi
          simp at hi
          subst hi
          exact h_next
        | cons d' ds'' =>
          rw [List.scanl_cons] at hi
          dsimp [List.dropWhile] at hi
          rw [h_dec2] at hi
          dsimp at hi
          rw [← List.scanl_cons] at hi
          exact scanl_no_revisit_tail (d' :: ds'') (step_addr st d) a h_next i hi

theorem withAddresses_no_revisit (e : Executable) (a : Int64) :
  ∀ i ∈ (e.withAddresses.dropWhile (fun i => i.1 ≠ a)).dropWhile (fun i => i.1 = a), i.1 ≠ a := by
  dsimp [Executable.withAddresses, step_addr]
  exact scanl_no_revisit e.2 (e.1, .byteArray (.mk #[]), 0) a


theorem withAddressesMonotonic (e: Executable) (a: Int64):
  ∃ i1 i2 i3,
    e.withAddresses = i1 ++ i2 ++ i3 /\
    ∀ i ∈ i1, i.1 ≠ a /\
    ∀ i ∈ i2, i.1 = a /\
    ∀ i ∈ i3, i.1 ≠ a
:= by
  let L := e.withAddresses
  let i1 := L.takeWhile (fun i => i.1 ≠ a)
  let rest := L.dropWhile (fun i => i.1 ≠ a)
  let i2 := rest.takeWhile (fun i => i.1 = a)
  let i3 := rest.dropWhile (fun i => i.1 = a)
  have h1 : e.withAddresses = i1 ++ i2 ++ i3 := by
    have h1_1 : i1 ++ rest = L := List.takeWhile_append_dropWhile
    have h1_2 : i2 ++ i3 = rest := List.takeWhile_append_dropWhile
    rw [← h1_2] at h1_1
    rw [← List.append_assoc] at h1_1
    exact h1_1.symm
  have h2 : ∀ i ∈ i1, i.1 ≠ a := by
    intro i hi
    have := mem_takeWhile (fun i => decide (i.1 ≠ a)) L i hi
    exact of_decide_eq_true this
  have h3 : ∀ i ∈ i2, i.1 = a := by
    intro i hi
    have := mem_takeWhile (fun i => decide (i.1 = a)) rest i hi
    exact of_decide_eq_true this
  have h4 : ∀ i ∈ i3, i.1 ≠ a := withAddresses_no_revisit e a
  exact ⟨i1, ⟨i2, ⟨i3, ⟨h1, fun i hi => ⟨h2 i hi, fun j hj => ⟨h3 j hj, h4⟩⟩⟩⟩⟩⟩











