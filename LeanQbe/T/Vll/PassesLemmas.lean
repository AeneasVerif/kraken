module

public import LeanQbe.T.Vll.PassesLemmas0
import LeanQbe.T.TargetLemmas

/-!
# Small-Step `VllHost` Simulation & End-to-End `FnSpec` Transfer (`Vll.PassesLemmas`)

100% architecture-free (`0` imports of `Arm64`, `Amd64`, `Kraken.X64`, `Kraken.AArch64`,
`Vll.Arm64*`, `Vll.AsmArm64*`, or `Vll.FactorArm64*`) small-step host simulation and `FnSpec`
preservation proofs atop `LeanQbe.T.Vll.PassesLemmas0` (`std3` axioms only):

1. **Chunk-based twin-host simulation (`Chunk`, `ChunksValid`, `TwinHosts`, `chunks_bwd_sim`,
   `chunks_twinHost_sim`, `chunks_fnSpec_transfer`):** proves both unconditional backward
   simulation (`h₂ → h₁`) and twin-host forward simulation (`h₁, h₁' → h₂`) for every shrinking
   rewrite pass (`elimFilter`, `elimWindow`, `invertJccJmp`, `elimFallthrough`), transferring
   `Target.FnSpec` across arbitrary calls, returns, exits, and `.native` directives with zero
   restrictions on caller return addresses.
2. **1:1 trampoline threading simulation (`threadJmp_bwd_sim`, `threadJmp_fwd_sim`,
   `threadJmp_fnSpec_transfer`):** length- and address-preserving simulation for `threadJmp`.
3. **End-to-end `vllLowerFn` soundness (`vllLowerFn_passPipeWf_correct`,
   `vllLowerFn_passPipeCore_correct`, `vllLowerFn_passPipe_correct`):** connects `vllLowerFn`
   directly to `passPipeWf` (bare `A.Wf`), `passPipeCore` (`A.PassWf`), and full `passPipe`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Vll

open LeanQbe.T

/-! ## 1. Elementary Rewrite Chunks & Index Maps -/

/-- Elementary rewrite chunk pairing an unoptimized slice with its optimized slice. -/
private inductive Chunk (A : Arch) : Type where
  | same (i : Instr A)
  | dropNoop (i : Instr A)
  | pairDet (i₁ i₂ i' : Instr A)
  | dropFallJmp (l : Sym)
  | dropFallJcc (c : A.Cond) (l : Sym)
  | invertJcc (c : A.Cond) (l₁ l₂ : Sym)

/-- Unoptimized slice of a chunk. -/
private def Chunk.lhs {A : Arch} : Chunk A → List (Instr A)
  | .same i => [i]
  | .dropNoop i => [i]
  | .pairDet i₁ i₂ _ => [i₁, i₂]
  | .dropFallJmp l => [.jmp l, .label l]
  | .dropFallJcc c l => [.jcc c l, .label l]
  | .invertJcc c l₁ l₂ => [.jcc c l₁, .jmp l₂, .label l₁]

/-- Optimized slice of a chunk. -/
private def Chunk.rhs {A : Arch} : Chunk A → List (Instr A)
  | .same i => [i]
  | .dropNoop _ => []
  | .pairDet _ _ i' => [i']
  | .dropFallJmp l => [.label l]
  | .dropFallJcc _ l => [.label l]
  | .invertJcc c l₁ l₂ => [.jcc (A.negCond c) l₂, .label l₁]

/-- True iff the chunk keeps index `0` of `c.lhs` at index `0` of `c.rhs`. -/
private def Chunk.keepsHead {A : Arch} : Chunk A → Bool
  | .same _ | .pairDet _ _ _ | .invertJcc _ _ _ => true
  | .dropNoop _ | .dropFallJmp _ | .dropFallJcc _ _ => false

/-- True iff the last instruction of `c.lhs` is a hardware call (`.call` / `.icall`). -/
private def Chunk.endCall {A : Arch} : Chunk A → Bool
  | .same i => i.isCall
  | _ => false

/-- Semantic validity of an elementary chunk under architecture `A`. -/
private def Chunk.Valid (A : Arch) : Chunk A → Prop
  | .same _ => True
  | .dropNoop i =>
    (∀ l, i ≠ .label l) ∧ i.isCall = false ∧
    ∀ symAddr np s o, instrRel A symAddr np i s o ↔ o = .fall s
  | .pairDet i₁ i₂ i' =>
    ((∀ l, i₁ ≠ .label l) ∧ (∀ l, i₂ ≠ .label l) ∧ (∀ l, i' ≠ .label l)) ∧
    (i₁.isCall = false ∧ i₂.isCall = false ∧ i'.isCall = false) ∧
    ∀ symAddr, DetFallPair A symAddr i₁ i₂ i'
  | .dropFallJmp _ => True
  | .dropFallJcc _ _ => True
  | .invertJcc _ _ _ => True

/-- Flattened unoptimized instruction list of a chunk sequence. -/
private def chunksLhs {A : Arch} (cs : List (Chunk A)) : List (Instr A) :=
  cs.flatMap Chunk.lhs

/-- Flattened optimized instruction list of a chunk sequence. -/
private def chunksRhs {A : Arch} (cs : List (Chunk A)) : List (Instr A) :=
  cs.flatMap Chunk.rhs

/-- Call-anchor-preserving validity of a chunk sequence. -/
private def ChunksValid (A : Arch) : Bool → List (Chunk A) → Prop
  | _, [] => True
  | prevCall, c :: rest =>
    c.Valid A ∧ (prevCall = true → c.keepsHead = true) ∧ ChunksValid A c.endCall rest

/-- Kept-index map from `chunksLhs cs` to `chunksRhs cs` (`none` for dropped indices; maps
`k ≥ (chunksLhs cs).length` to `(chunksRhs cs).length + (k - (chunksLhs cs).length)`). -/
private def chunksMap {A : Arch} : List (Chunk A) → Nat → Option Nat
  | [], k => some k
  | .same _ :: _, 0 => some 0
  | .same _ :: rest, k + 1 => (chunksMap rest k).map (· + 1)
  | .dropNoop _ :: _, 0 => none
  | .dropNoop _ :: rest, k + 1 => chunksMap rest k
  | .pairDet _ _ _ :: _, 0 => some 0
  | .pairDet _ _ _ :: _, 1 => none
  | .pairDet _ _ _ :: rest, k + 2 => (chunksMap rest k).map (· + 1)
  | .dropFallJmp _ :: _, 0 => none
  | .dropFallJmp _ :: _, 1 => some 0
  | .dropFallJmp _ :: rest, k + 2 => (chunksMap rest k).map (· + 1)
  | .dropFallJcc _ _ :: _, 0 => none
  | .dropFallJcc _ _ :: _, 1 => some 0
  | .dropFallJcc _ _ :: rest, k + 2 => (chunksMap rest k).map (· + 1)
  | .invertJcc _ _ _ :: _, 0 => some 0
  | .invertJcc _ _ _ :: _, 1 => none
  | .invertJcc _ _ _ :: _, 2 => some 1
  | .invertJcc _ _ _ :: rest, k + 3 => (chunksMap rest k).map (· + 2)

/-- Target index in `chunksRhs cs` associated with index `k` of `chunksLhs cs`. -/
private def chunksTarget {A : Arch} : List (Chunk A) → Nat → Nat
  | [], k => k
  | .same _ :: _, 0 => 0
  | .same _ :: rest, k + 1 => chunksTarget rest k + 1
  | .dropNoop _ :: _, 0 => 0
  | .dropNoop _ :: rest, k + 1 => chunksTarget rest k
  | .pairDet _ _ _ :: _, 0 => 0
  | .pairDet _ _ _ :: _, 1 => 1
  | .pairDet _ _ _ :: rest, k + 2 => chunksTarget rest k + 1
  | .dropFallJmp _ :: _, 0 => 0
  | .dropFallJmp _ :: _, 1 => 0
  | .dropFallJmp _ :: rest, k + 2 => chunksTarget rest k + 1
  | .dropFallJcc _ _ :: _, 0 => 0
  | .dropFallJcc _ _ :: _, 1 => 0
  | .dropFallJcc _ _ :: rest, k + 2 => chunksTarget rest k + 1
  | .invertJcc _ _ _ :: _, 0 => 0
  | .invertJcc _ _ _ :: _, 1 => 1
  | .invertJcc _ _ _ :: _, 2 => 1
  | .invertJcc _ _ _ :: rest, k + 3 => chunksTarget rest k + 2

/-- True iff `k` is not the dropped 2nd instruction of a `pairDet` or `invertJcc` chunk. -/
private def chunkBoundary {A : Arch} : List (Chunk A) → Nat → Bool
  | [], _ => true
  | .same _ :: _, 0 => true
  | .same _ :: rest, k + 1 => chunkBoundary rest k
  | .dropNoop _ :: _, 0 => true
  | .dropNoop _ :: rest, k + 1 => chunkBoundary rest k
  | .pairDet _ _ _ :: _, 0 => true
  | .pairDet _ _ _ :: _, 1 => false
  | .pairDet _ _ _ :: rest, k + 2 => chunkBoundary rest k
  | .dropFallJmp _ :: _, 0 => true
  | .dropFallJmp _ :: _, 1 => true
  | .dropFallJmp _ :: rest, k + 2 => chunkBoundary rest k
  | .dropFallJcc _ _ :: _, 0 => true
  | .dropFallJcc _ _ :: _, 1 => true
  | .dropFallJcc _ _ :: rest, k + 2 => chunkBoundary rest k
  | .invertJcc _ _ _ :: _, 0 => true
  | .invertJcc _ _ _ :: _, 1 => false
  | .invertJcc _ _ _ :: _, 2 => true
  | .invertJcc _ _ _ :: rest, k + 3 => chunkBoundary rest k

/-! ### Structural Index-Map Lemmas -/

private theorem chunksLhs_cons {A : Arch} (c : Chunk A) (rest : List (Chunk A)) :
    chunksLhs (c :: rest) = c.lhs ++ chunksLhs rest := rfl

private theorem chunksRhs_cons {A : Arch} (c : Chunk A) (rest : List (Chunk A)) :
    chunksRhs (c :: rest) = c.rhs ++ chunksRhs rest := rfl

private theorem chunksLhs_append {A : Arch} (cs₁ cs₂ : List (Chunk A)) :
    chunksLhs (cs₁ ++ cs₂) = chunksLhs cs₁ ++ chunksLhs cs₂ := by
  simp [chunksLhs, List.flatMap_append]

private theorem chunksRhs_append {A : Arch} (cs₁ cs₂ : List (Chunk A)) :
    chunksRhs (cs₁ ++ cs₂) = chunksRhs cs₁ ++ chunksRhs cs₂ := by
  simp [chunksRhs, List.flatMap_append]

private theorem chunksLhs_cons_len {A : Arch} (c : Chunk A) (rest : List (Chunk A)) :
    (chunksLhs (c :: rest)).length = c.lhs.length + (chunksLhs rest).length := by
  simp [chunksLhs]

private theorem chunksRhs_cons_len {A : Arch} (c : Chunk A) (rest : List (Chunk A)) :
    (chunksRhs (c :: rest)).length = c.rhs.length + (chunksRhs rest).length := by
  simp [chunksRhs]

private theorem chunksMap_ge {A : Arch} :
    ∀ (cs : List (Chunk A)) (k : Nat), (chunksLhs cs).length ≤ k →
      chunksMap cs k = some ((chunksRhs cs).length + (k - (chunksLhs cs).length))
  | [], k, _ => by simp [chunksLhs, chunksRhs, chunksMap]
  | c :: rest, k, hk => by
    rw [chunksLhs_cons_len] at hk ⊢; rw [chunksRhs_cons_len]
    cases c with
    | same _ =>
      match k with
      | 0 => simp [Chunk.lhs] at hk
      | k + 1 =>
        simp only [Chunk.lhs, Chunk.rhs, List.length_singleton] at hk ⊢
        rw [chunksMap, chunksMap_ge rest k (by omega)]
        simp only [Option.map_some, Option.some.injEq]; omega
    | dropNoop _ =>
      match k with
      | 0 => simp [Chunk.lhs] at hk
      | k + 1 =>
        simp only [Chunk.lhs, Chunk.rhs, List.length_singleton, List.length_nil] at hk ⊢
        rw [chunksMap, chunksMap_ge rest k (by omega)]
        simp only [Option.some.injEq]; omega
    | pairDet _ _ _ | dropFallJmp _ | dropFallJcc _ _ =>
      match k with
      | 0 => simp [Chunk.lhs] at hk
      | 1 => simp [Chunk.lhs] at hk; omega
      | k + 2 =>
        simp only [Chunk.lhs, Chunk.rhs, List.length_cons, List.length_nil] at hk ⊢
        rw [chunksMap, chunksMap_ge rest k (by omega)]
        simp only [Option.map_some, Option.some.injEq]; omega
    | invertJcc _ _ _ =>
      match k with
      | 0 => simp [Chunk.lhs] at hk
      | 1 | 2 => simp [Chunk.lhs] at hk; omega
      | k + 3 =>
        simp only [Chunk.lhs, Chunk.rhs, List.length_cons, List.length_nil] at hk ⊢
        rw [chunksMap, chunksMap_ge rest k (by omega)]
        simp only [Option.map_some, Option.some.injEq]; omega

private theorem chunksMap_lt {A : Arch} :
    ∀ {cs : List (Chunk A)} {k j : Nat}, k < (chunksLhs cs).length →
      chunksMap cs k = some j → j < (chunksRhs cs).length
  | [], _, _, hk, _ => by simp [chunksLhs] at hk
  | c :: rest, k, j, hk, hm => by
    rw [chunksLhs_cons_len] at hk; rw [chunksRhs_cons_len]
    cases c with
    | same _ =>
      match k with
      | 0 => simp only [chunksMap, Option.some.injEq] at hm; subst hm; simp [Chunk.rhs]; omega
      | k + 1 =>
        simp only [chunksMap, Option.map_eq_some_iff] at hm; obtain ⟨j', hj', rfl⟩ := hm
        simp only [Chunk.lhs, Chunk.rhs, List.length_singleton] at hk ⊢
        have := chunksMap_lt (cs := rest) (by omega) hj'; omega
    | dropNoop _ =>
      match k with
      | 0 => simp [chunksMap] at hm
      | k + 1 =>
        simp only [Chunk.lhs, Chunk.rhs, List.length_singleton, List.length_nil,
          Nat.zero_add] at hk ⊢
        exact chunksMap_lt (cs := rest) (by omega) hm
    | pairDet _ _ _ =>
      match k with
      | 0 => simp only [chunksMap, Option.some.injEq] at hm; subst hm; simp [Chunk.rhs]; omega
      | 1 => simp [chunksMap] at hm
      | k + 2 =>
        simp only [chunksMap, Option.map_eq_some_iff] at hm; obtain ⟨j', hj', rfl⟩ := hm
        simp only [Chunk.lhs, Chunk.rhs, List.length_cons, List.length_nil] at hk ⊢
        have := chunksMap_lt (cs := rest) (by omega) hj'; omega
    | dropFallJmp _ | dropFallJcc _ _ =>
      match k with
      | 0 => simp [chunksMap] at hm
      | 1 => simp only [chunksMap, Option.some.injEq] at hm; subst hm; simp [Chunk.rhs]; omega
      | k + 2 =>
        simp only [chunksMap, Option.map_eq_some_iff] at hm; obtain ⟨j', hj', rfl⟩ := hm
        simp only [Chunk.lhs, Chunk.rhs, List.length_cons, List.length_nil] at hk ⊢
        have := chunksMap_lt (cs := rest) (by omega) hj'; omega
    | invertJcc _ _ _ =>
      match k with
      | 0 => simp only [chunksMap, Option.some.injEq] at hm; subst hm; simp [Chunk.rhs]; omega
      | 1 => simp [chunksMap] at hm
      | 2 => simp only [chunksMap, Option.some.injEq] at hm; subst hm; simp [Chunk.rhs]; omega
      | k + 3 =>
        simp only [chunksMap, Option.map_eq_some_iff] at hm; obtain ⟨j', hj', rfl⟩ := hm
        simp only [Chunk.lhs, Chunk.rhs, List.length_cons, List.length_nil] at hk ⊢
        have := chunksMap_lt (cs := rest) (by omega) hj'; omega

private theorem chunksMap_mono {A : Arch} :
    ∀ {cs : List (Chunk A)} {k₁ k₂ j₁ j₂ : Nat}, k₁ < k₂ →
      chunksMap cs k₁ = some j₁ → chunksMap cs k₂ = some j₂ → j₁ < j₂
  | [], _, _, _, _, hlt, h1, h2 => by simp only [chunksMap, Option.some.injEq] at h1 h2; omega
  | c :: rest, k₁, k₂, j₁, j₂, hlt, h1, h2 => by
    cases c with
    | same _ =>
      match k₁, k₂ with
      | 0, 0 => omega
      | 0, k₂ + 1 =>
        simp only [chunksMap, Option.some.injEq, Option.map_eq_some_iff] at h1 h2
        obtain ⟨_, _, rfl⟩ := h2; omega
      | k₁ + 1, 0 => omega
      | k₁ + 1, k₂ + 1 =>
        simp only [chunksMap, Option.map_eq_some_iff] at h1 h2
        obtain ⟨a, ha, rfl⟩ := h1; obtain ⟨b, hb, rfl⟩ := h2
        have := chunksMap_mono (cs := rest) (by omega) ha hb; omega
    | dropNoop _ =>
      match k₁, k₂ with
      | 0, _ => simp [chunksMap] at h1
      | k₁ + 1, 0 => omega
      | k₁ + 1, k₂ + 1 => exact chunksMap_mono (cs := rest) (by omega) h1 h2
    | pairDet _ _ _ =>
      match k₁, k₂ with
      | 0, 0 => omega
      | 0, 1 => simp [chunksMap] at h2
      | 0, k₂ + 2 =>
        simp only [chunksMap, Option.some.injEq, Option.map_eq_some_iff] at h1 h2
        obtain ⟨_, _, rfl⟩ := h2; omega
      | 1, _ => simp [chunksMap] at h1
      | k₁ + 2, 0 | k₁ + 2, 1 => omega
      | k₁ + 2, k₂ + 2 =>
        simp only [chunksMap, Option.map_eq_some_iff] at h1 h2
        obtain ⟨a, ha, rfl⟩ := h1; obtain ⟨b, hb, rfl⟩ := h2
        have := chunksMap_mono (cs := rest) (by omega) ha hb; omega
    | dropFallJmp _ | dropFallJcc _ _ =>
      match k₁, k₂ with
      | 0, _ => simp [chunksMap] at h1
      | 1, 0 | 1, 1 => omega
      | 1, k₂ + 2 =>
        simp only [chunksMap, Option.some.injEq, Option.map_eq_some_iff] at h1 h2
        obtain ⟨_, _, rfl⟩ := h2; omega
      | k₁ + 2, 0 | k₁ + 2, 1 => omega
      | k₁ + 2, k₂ + 2 =>
        simp only [chunksMap, Option.map_eq_some_iff] at h1 h2
        obtain ⟨a, ha, rfl⟩ := h1; obtain ⟨b, hb, rfl⟩ := h2
        have := chunksMap_mono (cs := rest) (by omega) ha hb; omega
    | invertJcc _ _ _ =>
      match k₁, k₂ with
      | 0, 0 => omega
      | 0, 1 => simp [chunksMap] at h2
      | 0, 2 => simp only [chunksMap, Option.some.injEq] at h1 h2; omega
      | 0, k₂ + 3 =>
        simp only [chunksMap, Option.some.injEq, Option.map_eq_some_iff] at h1 h2
        obtain ⟨_, _, rfl⟩ := h2; omega
      | 1, _ => simp [chunksMap] at h1
      | 2, 0 | 2, 1 | 2, 2 => omega
      | 2, k₂ + 3 =>
        simp only [chunksMap, Option.some.injEq, Option.map_eq_some_iff] at h1 h2
        obtain ⟨_, _, rfl⟩ := h2; omega
      | k₁ + 3, 0 | k₁ + 3, 1 | k₁ + 3, 2 => omega
      | k₁ + 3, k₂ + 3 =>
        simp only [chunksMap, Option.map_eq_some_iff] at h1 h2
        obtain ⟨a, ha, rfl⟩ := h1; obtain ⟨b, hb, rfl⟩ := h2
        have := chunksMap_mono (cs := rest) (by omega) ha hb; omega

private theorem chunksMap_inj {A : Arch} {cs : List (Chunk A)} {k₁ k₂ j : Nat}
    (h1 : chunksMap cs k₁ = some j) (h2 : chunksMap cs k₂ = some j) : k₁ = k₂ := by
  by_cases hlt : k₁ < k₂
  · exact absurd (chunksMap_mono hlt h1 h2) (Nat.lt_irrefl j)
  · by_cases hgt : k₂ < k₁
    · exact absurd (chunksMap_mono hgt h2 h1) (Nat.lt_irrefl j)
    · omega

private theorem chunksTarget_of_map {A : Arch} :
    ∀ {cs : List (Chunk A)} {k j : Nat}, chunksMap cs k = some j → chunksTarget cs k = j
  | [], _, _, h => by simp only [chunksMap, Option.some.injEq] at h; exact h
  | c :: rest, k, j, h => by
    cases c with
    | same _ =>
      match k with
      | 0 => simp only [chunksMap, Option.some.injEq] at h; simpa [chunksTarget] using h
      | k + 1 =>
        simp only [chunksMap, Option.map_eq_some_iff] at h; obtain ⟨a, ha, rfl⟩ := h
        simp [chunksTarget, chunksTarget_of_map (cs := rest) ha]
    | dropNoop _ =>
      match k with
      | 0 => simp [chunksMap] at h
      | k + 1 => exact chunksTarget_of_map (cs := rest) h
    | pairDet _ _ _ =>
      match k with
      | 0 => simp only [chunksMap, Option.some.injEq] at h; simpa [chunksTarget] using h
      | 1 => simp [chunksMap] at h
      | k + 2 =>
        simp only [chunksMap, Option.map_eq_some_iff] at h; obtain ⟨a, ha, rfl⟩ := h
        simp [chunksTarget, chunksTarget_of_map (cs := rest) ha]
    | dropFallJmp _ | dropFallJcc _ _ =>
      match k with
      | 0 => simp [chunksMap] at h
      | 1 => simp only [chunksMap, Option.some.injEq] at h; simpa [chunksTarget] using h
      | k + 2 =>
        simp only [chunksMap, Option.map_eq_some_iff] at h; obtain ⟨a, ha, rfl⟩ := h
        simp [chunksTarget, chunksTarget_of_map (cs := rest) ha]
    | invertJcc _ _ _ =>
      match k with
      | 0 => simp only [chunksMap, Option.some.injEq] at h; simpa [chunksTarget] using h
      | 1 => simp [chunksMap] at h
      | 2 => simp only [chunksMap, Option.some.injEq] at h; simpa [chunksTarget] using h
      | k + 3 =>
        simp only [chunksMap, Option.map_eq_some_iff] at h; obtain ⟨a, ha, rfl⟩ := h
        simp [chunksTarget, chunksTarget_of_map (cs := rest) ha]

private theorem chunksMap_label_lhs {A : Arch} :
    ∀ {cs : List (Chunk A)} {pc : Bool}, ChunksValid A pc cs →
      ∀ {k : Nat} {l : Sym}, (chunksLhs cs)[k]? = some (.label l) →
        ∃ j, chunksMap cs k = some j ∧ (chunksRhs cs)[j]? = some (.label l)
  | [], _, _, _, _, hk => by simp [chunksLhs] at hk
  | c :: rest, _, ⟨hv, _, hrest⟩, k, l, hk => by
    cases c with
    | same _ =>
      match k with
      | 0 => exact ⟨0, rfl, hk⟩
      | k + 1 =>
        obtain ⟨j, hm, hr⟩ := chunksMap_label_lhs hrest hk
        exact ⟨j + 1, by simp [chunksMap, hm], hr⟩
    | dropNoop _ =>
      match k with
      | 0 =>
        simp only [chunksLhs, List.flatMap_cons, Chunk.lhs, List.singleton_append,
          List.getElem?_cons_zero, Option.some.injEq] at hk
        exact absurd hk (hv.1 l)
      | k + 1 => exact chunksMap_label_lhs hrest hk
    | pairDet _ _ _ =>
      match k with
      | 0 =>
        simp only [chunksLhs, List.flatMap_cons, Chunk.lhs, List.cons_append,
          List.getElem?_cons_zero, Option.some.injEq] at hk
        exact absurd hk (hv.1.1 l)
      | 1 =>
        simp only [chunksLhs, List.flatMap_cons, Chunk.lhs, List.cons_append,
          List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hk
        exact absurd hk (hv.1.2.1 l)
      | k + 2 =>
        obtain ⟨j, hm, hr⟩ := chunksMap_label_lhs hrest hk
        exact ⟨j + 1, by simp [chunksMap, hm], hr⟩
    | dropFallJmp _ | dropFallJcc _ _ =>
      match k with
      | 0 => simp [chunksLhs, Chunk.lhs] at hk
      | 1 =>
        simp only [chunksLhs, List.flatMap_cons, Chunk.lhs, List.cons_append,
          List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          Instr.label.injEq] at hk
        subst hk; exact ⟨0, rfl, rfl⟩
      | k + 2 =>
        obtain ⟨j, hm, hr⟩ := chunksMap_label_lhs hrest hk
        exact ⟨j + 1, by simp [chunksMap, hm], hr⟩
    | invertJcc _ _ _ =>
      match k with
      | 0 | 1 => simp [chunksLhs, Chunk.lhs] at hk
      | 2 =>
        simp only [chunksLhs, List.flatMap_cons, Chunk.lhs, List.cons_append,
          List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          Instr.label.injEq] at hk
        subst hk; exact ⟨1, rfl, rfl⟩
      | k + 3 =>
        obtain ⟨j, hm, hr⟩ := chunksMap_label_lhs hrest hk
        exact ⟨j + 2, by simp [chunksMap, hm], hr⟩

private theorem chunksMap_label_rhs {A : Arch} :
    ∀ {cs : List (Chunk A)} {pc : Bool}, ChunksValid A pc cs →
      ∀ {j : Nat} {l : Sym}, (chunksRhs cs)[j]? = some (.label l) →
        ∃ k, chunksMap cs k = some j ∧ (chunksLhs cs)[k]? = some (.label l)
  | [], _, _, _, _, hj => by simp [chunksRhs] at hj
  | c :: rest, _, ⟨hv, _, hrest⟩, j, l, hj => by
    cases c with
    | same _ =>
      match j with
      | 0 => exact ⟨0, rfl, hj⟩
      | j + 1 =>
        obtain ⟨k, hm, hl⟩ := chunksMap_label_rhs hrest hj
        exact ⟨k + 1, by simp [chunksMap, hm], hl⟩
    | dropNoop _ =>
      obtain ⟨k, hm, hl⟩ := chunksMap_label_rhs hrest hj
      exact ⟨k + 1, hm, hl⟩
    | pairDet _ _ _ =>
      match j with
      | 0 =>
        simp only [chunksRhs, List.flatMap_cons, Chunk.rhs, List.singleton_append,
          List.getElem?_cons_zero, Option.some.injEq] at hj
        exact absurd hj (hv.1.2.2 l)
      | j + 1 =>
        obtain ⟨k, hm, hl⟩ := chunksMap_label_rhs hrest hj
        exact ⟨k + 2, by simp [chunksMap, hm], hl⟩
    | dropFallJmp _ | dropFallJcc _ _ =>
      match j with
      | 0 =>
        simp only [chunksRhs, List.flatMap_cons, Chunk.rhs, List.singleton_append,
          List.getElem?_cons_zero, Option.some.injEq, Instr.label.injEq] at hj
        subst hj; exact ⟨1, rfl, rfl⟩
      | j + 1 =>
        obtain ⟨k, hm, hl⟩ := chunksMap_label_rhs hrest hj
        exact ⟨k + 2, by simp [chunksMap, hm], hl⟩
    | invertJcc _ _ _ =>
      match j with
      | 0 => simp [chunksRhs, Chunk.rhs] at hj
      | 1 =>
        simp only [chunksRhs, List.flatMap_cons, Chunk.rhs, List.cons_append,
          List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          Instr.label.injEq] at hj
        subst hj; exact ⟨2, rfl, rfl⟩
      | j + 2 =>
        obtain ⟨k, hm, hl⟩ := chunksMap_label_rhs hrest hj
        exact ⟨k + 3, by simp [chunksMap, hm], hl⟩

private theorem chunksMap_head_kept {A : Arch} {cs : List (Chunk A)}
    (hv : ChunksValid A true cs) : chunksMap cs 0 = some 0 := by
  cases cs with
  | nil => rfl
  | cons c _ =>
    have hk := hv.2.1 rfl
    cases c <;> simp [Chunk.keepsHead] at hk <;> rfl

private theorem chunksMap_surj {A : Arch} :
    ∀ {cs : List (Chunk A)} {j : Nat}, j < (chunksRhs cs).length →
      ∃ k < (chunksLhs cs).length, chunksMap cs k = some j
  | [], _, hj => by simp [chunksRhs] at hj
  | c :: rest, j, hj => by
    rw [chunksRhs_cons_len] at hj; rw [chunksLhs_cons_len]
    cases c with
    | same _ =>
      match j with
      | 0 => exact ⟨0, by simp [Chunk.lhs]; omega, rfl⟩
      | j + 1 =>
        simp [Chunk.rhs] at hj
        obtain ⟨k, hk, hm⟩ := chunksMap_surj (cs := rest) (j := j) (by omega)
        exact ⟨k + 1, by simp [Chunk.lhs]; omega, by simp [chunksMap, hm]⟩
    | dropNoop _ =>
      simp [Chunk.rhs] at hj
      obtain ⟨k, hk, hm⟩ := chunksMap_surj (cs := rest) (j := j) hj
      exact ⟨k + 1, by simp [Chunk.lhs]; omega, hm⟩
    | pairDet _ _ _ =>
      match j with
      | 0 => exact ⟨0, by simp [Chunk.lhs]; omega, rfl⟩
      | j + 1 =>
        simp [Chunk.rhs] at hj
        obtain ⟨k, hk, hm⟩ := chunksMap_surj (cs := rest) (j := j) (by omega)
        exact ⟨k + 2, by simp [Chunk.lhs]; omega, by simp [chunksMap, hm]⟩
    | dropFallJmp _ | dropFallJcc _ _ =>
      match j with
      | 0 => exact ⟨1, by simp [Chunk.lhs]; omega, rfl⟩
      | j + 1 =>
        simp [Chunk.rhs] at hj
        obtain ⟨k, hk, hm⟩ := chunksMap_surj (cs := rest) (j := j) (by omega)
        exact ⟨k + 2, by simp [Chunk.lhs]; omega, by simp [chunksMap, hm]⟩
    | invertJcc _ _ _ =>
      match j with
      | 0 => exact ⟨0, by simp [Chunk.lhs]; omega, rfl⟩
      | 1 => exact ⟨2, by simp [Chunk.lhs]; omega, rfl⟩
      | j + 2 =>
        simp [Chunk.rhs] at hj
        obtain ⟨k, hk, hm⟩ := chunksMap_surj (cs := rest) (j := j) (by omega)
        exact ⟨k + 3, by simp [Chunk.lhs]; omega, by simp [chunksMap, hm]⟩

private theorem chunksMap_append_left {A : Arch} :
    ∀ {cs₁ cs₂ : List (Chunk A)} {k : Nat},
      k < (chunksLhs cs₁).length → chunksMap (cs₁ ++ cs₂) k = chunksMap cs₁ k
  | [], _, _, hk => by simp [chunksLhs] at hk
  | c :: rest, cs₂, k, hk => by
    rw [chunksLhs_cons_len] at hk
    cases c with
    | same _ =>
      match k with
      | 0 => rfl
      | k + 1 =>
        simp [Chunk.lhs] at hk
        simp only [List.cons_append, chunksMap,
          chunksMap_append_left (cs₁ := rest) (cs₂ := cs₂) (k := k) (by omega)]
    | dropNoop _ =>
      match k with
      | 0 => rfl
      | k + 1 =>
        simp [Chunk.lhs] at hk
        exact chunksMap_append_left (cs₁ := rest) (cs₂ := cs₂) (k := k) (by omega)
    | pairDet _ _ _ | dropFallJmp _ | dropFallJcc _ _ =>
      match k with
      | 0 | 1 => rfl
      | k + 2 =>
        simp [Chunk.lhs] at hk
        simp only [List.cons_append, chunksMap,
          chunksMap_append_left (cs₁ := rest) (cs₂ := cs₂) (k := k) (by omega)]
    | invertJcc _ _ _ =>
      match k with
      | 0 | 1 | 2 => rfl
      | k + 3 =>
        simp [Chunk.lhs] at hk
        simp only [List.cons_append, chunksMap,
          chunksMap_append_left (cs₁ := rest) (cs₂ := cs₂) (k := k) (by omega)]

private theorem chunksMap_map_same_append {A : Arch} :
    ∀ (pre : List (Instr A)) (cs : List (Chunk A)) (k : Nat),
      chunksMap (pre.map Chunk.same ++ cs) (pre.length + k) =
        (chunksMap cs k).map (pre.length + ·)
  | [], cs, k => by simp
  | _ :: pre, cs, k => by
    simp only [List.map_cons, List.cons_append, List.length_cons, Nat.succ_add, chunksMap,
      chunksMap_map_same_append pre cs k]
    cases chunksMap cs k <;> simp

private inductive KeptClass (A : Arch) (cs : List (Chunk A)) (k j : Nat) : Prop where
  | same (i : Instr A) :
      (chunksLhs cs)[k]? = some i → (chunksRhs cs)[j]? = some i →
      chunksTarget cs (k + 1) = j + 1 → chunkBoundary cs (k + 1) = true →
      (i.isCall = true → chunksMap cs (k + 1) = some (j + 1)) →
      KeptClass A cs k j
  | pairDet (i₁ i₂ i' : Instr A) :
      (chunksLhs cs)[k]? = some i₁ → (chunksLhs cs)[k + 1]? = some i₂ →
      (chunksRhs cs)[j]? = some i' →
      chunksMap cs (k + 1) = none →
      chunksTarget cs (k + 1) = j + 1 → chunksTarget cs (k + 2) = j + 1 →
      chunkBoundary cs (k + 2) = true →
      (∀ symAddr, DetFallPair A symAddr i₁ i₂ i') →
      KeptClass A cs k j
  | invertJcc (c : A.Cond) (l₁ l₂ : Sym) :
      (chunksLhs cs)[k]? = some (.jcc c l₁) →
      (chunksLhs cs)[k + 1]? = some (.jmp l₂) →
      (chunksLhs cs)[k + 2]? = some (.label l₁) →
      (chunksRhs cs)[j]? = some (.jcc (A.negCond c) l₂) →
      (chunksRhs cs)[j + 1]? = some (.label l₁) →
      chunksMap cs (k + 1) = none → chunksMap cs (k + 2) = some (j + 1) →
      KeptClass A cs k j

private inductive DropClass (A : Arch) (cs : List (Chunk A)) (k : Nat) : Prop where
  | noop (i : Instr A) :
      (chunksLhs cs)[k]? = some i →
      (∀ symAddr np s o, instrRel A symAddr np i s o ↔ o = .fall s) →
      chunksTarget cs (k + 1) = chunksTarget cs k → chunkBoundary cs (k + 1) = true →
      DropClass A cs k
  | fallJmp (l : Sym) :
      (chunksLhs cs)[k]? = some (.jmp l) → (chunksLhs cs)[k + 1]? = some (.label l) →
      chunksMap cs (k + 1) = some (chunksTarget cs k) → DropClass A cs k
  | fallJcc (c : A.Cond) (l : Sym) :
      (chunksLhs cs)[k]? = some (.jcc c l) → (chunksLhs cs)[k + 1]? = some (.label l) →
      chunksMap cs (k + 1) = some (chunksTarget cs k) → DropClass A cs k
  | pairSecond (i₁ i₂ i' : Instr A) :
      chunkBoundary cs k = false →
      (chunksLhs cs)[k]? = some i₂ → (∀ l₂, i₂ ≠ .jmp l₂) →
      chunksTarget cs (k + 1) = chunksTarget cs k → chunkBoundary cs (k + 1) = true →
      DropClass A cs k
  | invertSecond (l₂ : Sym) :
      chunkBoundary cs k = false →
      (chunksLhs cs)[k]? = some (.jmp l₂) → DropClass A cs k

private theorem keptClass_shift {A : Arch} {c : Chunk A} {rest : List (Chunk A)} {k j : Nat}
    (h : KeptClass A rest k j) :
    KeptClass A (c :: rest) (c.lhs.length + k) (c.rhs.length + j) := by
  have hgetL : ∀ n, (chunksLhs (c :: rest))[c.lhs.length + n]? = (chunksLhs rest)[n]? := fun n => by
    simp [chunksLhs, List.getElem?_append_right]
  have hgetR : ∀ n, (chunksRhs (c :: rest))[c.rhs.length + n]? = (chunksRhs rest)[n]? := fun n => by
    simp [chunksRhs, List.getElem?_append_right]
  have hmap : ∀ n m, chunksMap rest n = some m →
      chunksMap (c :: rest) (c.lhs.length + n) = some (c.rhs.length + m) := by
    intro n m hm; cases c <;> simp [Chunk.lhs, Chunk.rhs, chunksMap, hm, Nat.add_comm]
  have hmapN : ∀ n, chunksMap rest n = none →
      chunksMap (c :: rest) (c.lhs.length + n) = none := by
    intro n hm; cases c <;> simp [Chunk.lhs, chunksMap, hm, Nat.add_comm]
  have htgt : ∀ n, chunksTarget (c :: rest) (c.lhs.length + n) =
      c.rhs.length + chunksTarget rest n := by
    intro n; cases c <;> simp [Chunk.lhs, Chunk.rhs, chunksTarget, Nat.add_comm]
  have hbnd : ∀ n, chunkBoundary (c :: rest) (c.lhs.length + n) = chunkBoundary rest n := by
    intro n; cases c <;> simp [Chunk.lhs, chunkBoundary, Nat.add_comm]
  cases h with
  | same i hl hr ht hb hcall =>
    refine .same i (by simpa using hgetL k ▸ hl) (by simpa using hgetR j ▸ hr) ?_ ?_ ?_
    · rw [Nat.add_assoc, htgt, ht]; omega
    · rw [Nat.add_assoc, hbnd]; exact hb
    · intro hc; rw [Nat.add_assoc, hmap _ _ (hcall hc)]; congr 1
  | pairDet i₁ i₂ i' hl1 hl2 hr hn ht1 ht2 hb hd =>
    refine .pairDet i₁ i₂ i' (by simpa using hgetL k ▸ hl1)
      (by rw [Nat.add_assoc, hgetL]; exact hl2) (by simpa using hgetR j ▸ hr)
      (by rw [Nat.add_assoc, hmapN _ hn]) (by rw [Nat.add_assoc, htgt, ht1]; omega)
      (by rw [Nat.add_assoc, htgt, ht2]; omega) (by rw [Nat.add_assoc, hbnd]; exact hb) hd
  | invertJcc cond l₁ l₂ hl0 hl1 hl2 hr0 hr1 hn hm =>
    refine .invertJcc cond l₁ l₂ (by simpa using hgetL k ▸ hl0)
      (by rw [Nat.add_assoc, hgetL]; exact hl1) (by rw [Nat.add_assoc, hgetL]; exact hl2)
      (by simpa using hgetR j ▸ hr0) (by rw [Nat.add_assoc, hgetR]; exact hr1)
      (by rw [Nat.add_assoc, hmapN _ hn])
      (by rw [Nat.add_assoc, hmap _ _ hm]; congr 1)

private theorem dropClass_shift {A : Arch} {c : Chunk A} {rest : List (Chunk A)} {k : Nat}
    (h : DropClass A rest k) :
    DropClass A (c :: rest) (c.lhs.length + k) := by
  have hgetL : ∀ n, (chunksLhs (c :: rest))[c.lhs.length + n]? = (chunksLhs rest)[n]? := fun n => by
    simp [chunksLhs, List.getElem?_append_right]
  have hmap : ∀ n m, chunksMap rest n = some m →
      chunksMap (c :: rest) (c.lhs.length + n) = some (c.rhs.length + m) := by
    intro n m hm; cases c <;> simp [Chunk.lhs, Chunk.rhs, chunksMap, hm, Nat.add_comm]
  have htgt : ∀ n, chunksTarget (c :: rest) (c.lhs.length + n) =
      c.rhs.length + chunksTarget rest n := by
    intro n; cases c <;> simp [Chunk.lhs, Chunk.rhs, chunksTarget, Nat.add_comm]
  have hbnd : ∀ n, chunkBoundary (c :: rest) (c.lhs.length + n) = chunkBoundary rest n := by
    intro n; cases c <;> simp [Chunk.lhs, chunkBoundary, Nat.add_comm]
  cases h with
  | noop i hl hrel ht hb =>
    refine .noop i (by simpa using hgetL k ▸ hl) hrel ?_ ?_
    · rw [Nat.add_assoc, htgt, htgt, ht]
    · rw [Nat.add_assoc, hbnd]; exact hb
  | fallJmp l hl0 hl1 hm =>
    refine .fallJmp l (by simpa using hgetL k ▸ hl0) (by rw [Nat.add_assoc, hgetL]; exact hl1) ?_
    rw [Nat.add_assoc, htgt, hmap _ _ hm]
  | fallJcc cond l hl0 hl1 hm =>
    refine .fallJcc cond l (by simpa using hgetL k ▸ hl0)
      (by rw [Nat.add_assoc, hgetL]; exact hl1) ?_
    rw [Nat.add_assoc, htgt, hmap _ _ hm]
  | pairSecond i₁ i₂ i' hnb hl hnj ht hb =>
    refine .pairSecond i₁ i₂ i' (by rw [hbnd]; exact hnb) (by simpa using hgetL k ▸ hl) hnj
      (by rw [Nat.add_assoc, htgt, htgt, ht]) (by rw [Nat.add_assoc, hbnd]; exact hb)
  | invertSecond l₂ hnb hl =>
    exact .invertSecond l₂ (by rw [hbnd]; exact hnb) (by simpa using hgetL k ▸ hl)

private theorem chunks_classify_kept {A : Arch} :
    ∀ {cs : List (Chunk A)} {pc : Bool}, ChunksValid A pc cs →
      ∀ {k j : Nat}, k < (chunksLhs cs).length → chunksMap cs k = some j → KeptClass A cs k j
  | [], _, _, _, _, hk, _ => by simp [chunksLhs] at hk
  | c :: rest, _, ⟨hv, _, hrest⟩, k, j, hk, hm => by
    rw [chunksLhs_cons_len] at hk
    have hbnd0 : chunkBoundary rest 0 = true := by
      cases rest with | nil => rfl | cons c' _ => cases c' <;> rfl
    have htgt0 : chunksTarget rest 0 = 0 := by
      cases rest with | nil => rfl | cons c' _ => cases c' <;> rfl
    cases c with
    | same i =>
      match k with
      | 0 =>
        simp only [chunksMap, Option.some.injEq] at hm; subst hm
        refine .same i rfl rfl (by simp [chunksTarget, htgt0])
          (by simp [chunkBoundary, hbnd0]) fun hcall => ?_
        have hhead : chunksMap rest 0 = some 0 :=
          chunksMap_head_kept (by simpa [Chunk.endCall, hcall] using hrest)
        simp [chunksMap, hhead]
      | k + 1 =>
        simp only [chunksMap, Option.map_eq_some_iff] at hm; obtain ⟨j', hj', rfl⟩ := hm
        simp only [Chunk.lhs, List.length_singleton] at hk
        simpa [Chunk.lhs, Chunk.rhs, Nat.add_comm] using
          keptClass_shift (c := .same i) (chunks_classify_kept hrest (by omega) hj')
    | dropNoop i =>
      match k with
      | 0 => simp [chunksMap] at hm
      | k + 1 =>
        simp only [Chunk.lhs, List.length_singleton] at hk
        simpa [Chunk.lhs, Chunk.rhs, Nat.add_comm] using
          keptClass_shift (c := .dropNoop i) (chunks_classify_kept hrest (by omega) hm)
    | pairDet i₁ i₂ i' =>
      match k with
      | 0 =>
        simp only [chunksMap, Option.some.injEq] at hm; subst hm
        exact .pairDet i₁ i₂ i' rfl rfl rfl rfl rfl (by simp [chunksTarget, htgt0])
          (by simp [chunkBoundary, hbnd0]) hv.2.2
      | 1 => simp [chunksMap] at hm
      | k + 2 =>
        simp only [chunksMap, Option.map_eq_some_iff] at hm; obtain ⟨j', hj', rfl⟩ := hm
        simp only [Chunk.lhs, List.length_cons, List.length_nil] at hk
        simpa [Chunk.lhs, Chunk.rhs, Nat.add_comm] using
          keptClass_shift (c := .pairDet i₁ i₂ i') (chunks_classify_kept hrest (by omega) hj')
    | dropFallJmp l =>
      match k with
      | 0 => simp [chunksMap] at hm
      | 1 =>
        simp only [chunksMap, Option.some.injEq] at hm; subst hm
        exact .same (.label l) rfl rfl (by simp [chunksTarget, htgt0])
          (by simp [chunkBoundary, hbnd0]) (fun h => by cases h)
      | k + 2 =>
        simp only [chunksMap, Option.map_eq_some_iff] at hm; obtain ⟨j', hj', rfl⟩ := hm
        simp only [Chunk.lhs, List.length_cons, List.length_nil] at hk
        simpa [Chunk.lhs, Chunk.rhs, Nat.add_comm] using
          keptClass_shift (c := .dropFallJmp l) (chunks_classify_kept hrest (by omega) hj')
    | dropFallJcc cond l =>
      match k with
      | 0 => simp [chunksMap] at hm
      | 1 =>
        simp only [chunksMap, Option.some.injEq] at hm; subst hm
        exact .same (.label l) rfl rfl (by simp [chunksTarget, htgt0])
          (by simp [chunkBoundary, hbnd0]) (fun h => by cases h)
      | k + 2 =>
        simp only [chunksMap, Option.map_eq_some_iff] at hm; obtain ⟨j', hj', rfl⟩ := hm
        simp only [Chunk.lhs, List.length_cons, List.length_nil] at hk
        simpa [Chunk.lhs, Chunk.rhs, Nat.add_comm] using
          keptClass_shift (c := .dropFallJcc cond l) (chunks_classify_kept hrest (by omega) hj')
    | invertJcc cond l₁ l₂ =>
      match k with
      | 0 =>
        simp only [chunksMap, Option.some.injEq] at hm; subst hm
        exact .invertJcc cond l₁ l₂ rfl rfl rfl rfl rfl rfl rfl
      | 1 => simp [chunksMap] at hm
      | 2 =>
        simp only [chunksMap, Option.some.injEq] at hm; subst hm
        exact .same (.label l₁) rfl rfl (by simp [chunksTarget, htgt0])
          (by simp [chunkBoundary, hbnd0]) (fun h => by cases h)
      | k + 3 =>
        simp only [chunksMap, Option.map_eq_some_iff] at hm; obtain ⟨j', hj', rfl⟩ := hm
        simp only [Chunk.lhs, List.length_cons, List.length_nil] at hk
        simpa [Chunk.lhs, Chunk.rhs, Nat.add_comm] using
          keptClass_shift (c := .invertJcc cond l₁ l₂) (chunks_classify_kept hrest (by omega) hj')

private theorem detFallPair_second_ne_jmp {A : Arch} {i₁ i₂ i' : Instr A}
    (hd : ∀ symAddr, DetFallPair A symAddr i₁ i₂ i') (l₂ : Sym) : i₂ ≠ .jmp l₂ := by
  intro heq; subst heq
  let s0 : MachSt A :=
    { gpr := fun _ => 0#64, vreg := fun _ => 0#512, flags := A.clearFlagsVal, mem := ∅ }
  obtain ⟨s₁, s₂, _, h2, _⟩ := (hd (fun _ => 0#64)).spec s0
  have := (h2 0#64 (.jump 0#64 s₁)).mp rfl
  cases this

private theorem chunks_classify_drop {A : Arch} :
    ∀ {cs : List (Chunk A)} {pc : Bool}, ChunksValid A pc cs →
      ∀ {k : Nat}, k < (chunksLhs cs).length → chunksMap cs k = none → DropClass A cs k
  | [], _, _, _, hk, _ => by simp [chunksLhs] at hk
  | c :: rest, _, ⟨hv, _, hrest⟩, k, hk, hm => by
    rw [chunksLhs_cons_len] at hk
    have hbnd0 : chunkBoundary rest 0 = true := by
      cases rest with | nil => rfl | cons c' _ => cases c' <;> rfl
    have htgt0 : chunksTarget rest 0 = 0 := by
      cases rest with | nil => rfl | cons c' _ => cases c' <;> rfl
    cases c with
    | same i =>
      match k with
      | 0 => simp [chunksMap] at hm
      | k + 1 =>
        simp only [chunksMap, Option.map_eq_none_iff] at hm
        simp only [Chunk.lhs, List.length_singleton] at hk
        simpa [Chunk.lhs, Nat.add_comm] using
          dropClass_shift (c := .same i) (chunks_classify_drop hrest (by omega) hm)
    | dropNoop i =>
      match k with
      | 0 => exact .noop i rfl hv.2.2 (by simp [chunksTarget, htgt0]) hbnd0
      | k + 1 =>
        simp only [Chunk.lhs, List.length_singleton] at hk
        simpa [Chunk.lhs, Nat.add_comm] using
          dropClass_shift (c := .dropNoop i) (chunks_classify_drop hrest (by omega) hm)
    | pairDet i₁ i₂ i' =>
      match k with
      | 0 => simp [chunksMap] at hm
      | 1 =>
        exact .pairSecond i₁ i₂ i' rfl rfl (detFallPair_second_ne_jmp hv.2.2)
          (by simp [chunksTarget, htgt0]) hbnd0
      | k + 2 =>
        simp only [chunksMap, Option.map_eq_none_iff] at hm
        simp only [Chunk.lhs, List.length_cons, List.length_nil] at hk
        simpa [Chunk.lhs, Nat.add_comm] using
          dropClass_shift (c := .pairDet i₁ i₂ i') (chunks_classify_drop hrest (by omega) hm)
    | dropFallJmp l =>
      match k with
      | 0 => exact .fallJmp l rfl rfl rfl
      | 1 => simp [chunksMap] at hm
      | k + 2 =>
        simp only [chunksMap, Option.map_eq_none_iff] at hm
        simp only [Chunk.lhs, List.length_cons, List.length_nil] at hk
        simpa [Chunk.lhs, Nat.add_comm] using
          dropClass_shift (c := .dropFallJmp l) (chunks_classify_drop hrest (by omega) hm)
    | dropFallJcc cond l =>
      match k with
      | 0 => exact .fallJcc cond l rfl rfl rfl
      | 1 => simp [chunksMap] at hm
      | k + 2 =>
        simp only [chunksMap, Option.map_eq_none_iff] at hm
        simp only [Chunk.lhs, List.length_cons, List.length_nil] at hk
        simpa [Chunk.lhs, Nat.add_comm] using
          dropClass_shift (c := .dropFallJcc cond l) (chunks_classify_drop hrest (by omega) hm)
    | invertJcc cond l₁ l₂ =>
      match k with
      | 0 | 2 => simp [chunksMap] at hm
      | 1 => exact .invertSecond l₂ rfl rfl
      | k + 3 =>
        simp only [chunksMap, Option.map_eq_none_iff] at hm
        simp only [Chunk.lhs, List.length_cons, List.length_nil] at hk
        simpa [Chunk.lhs, Nat.add_comm] using
          dropClass_shift (c := .invertJcc cond l₁ l₂) (chunks_classify_drop hrest (by omega) hm)

/-! ## 2. Finite Pigeonhole & Twin-Host Construction -/

private theorem nodup_length_le_of_subset {α : Type} [DecidableEq α] :
    ∀ {xs ys : List α}, xs.Nodup → (∀ x ∈ xs, x ∈ ys) → xs.length ≤ ys.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, ys, hnd, hsub => by
    rw [List.nodup_cons] at hnd
    have hx : x ∈ ys := hsub x List.mem_cons_self
    have hsub' : ∀ y ∈ xs, y ∈ ys.erase x := by
      intro y hy
      have hne : y ≠ x := fun e => hnd.1 (e ▸ hy)
      exact (List.mem_erase_of_ne hne).mpr (hsub y (List.mem_cons_of_mem _ hy))
    have ih := nodup_length_le_of_subset hnd.2 hsub'
    have hlen : (ys.erase x).length + 1 = ys.length := by
      rw [List.length_erase_of_mem hx]
      have hpos : 0 < ys.length := List.length_pos_of_mem hx
      omega
    simp only [List.length_cons]; omega

private theorem nodup_map_on {α β : Type} {f : α → β} :
    ∀ {xs : List α}, (∀ a ∈ xs, ∀ b ∈ xs, f a = f b → a = b) → xs.Nodup → (xs.map f).Nodup
  | [], _, _ => List.nodup_nil
  | x :: xs, hinj, hnd => by
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, nodup_map_on (fun a ha b hb =>
      hinj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)) hnd.2⟩
    obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hmem
    have hxy := hinj y (List.mem_cons_of_mem _ hy) x List.mem_cons_self hfy
    exact hnd.1 (hxy ▸ hy)

private theorem nodup_getElem_inj {α : Type} :
    ∀ {xs : List α}, xs.Nodup → ∀ {i j : Nat} (hi : i < xs.length) (hj : j < xs.length),
      xs[i] = xs[j] → i = j
  | [], _, _, _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | x :: xs, hnd, i, j, hi, hj, heq => by
    rw [List.nodup_cons] at hnd
    match i, j with
    | 0, 0 => rfl
    | 0, j + 1 =>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
      exact absurd (heq ▸ List.getElem_mem (Nat.lt_of_succ_lt_succ hj)) hnd.1
    | i + 1, 0 =>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
      exact absurd (heq.symm ▸ List.getElem_mem (Nat.lt_of_succ_lt_succ hi)) hnd.1
    | i + 1, j + 1 =>
      simp only [List.getElem_cons_succ] at heq
      exact congrArg Nat.succ (nodup_getElem_inj hnd.2 _ _ heq)

private theorem exists_fresh_bv64 (used : List (BitVec 64)) (h : used.length < 2 ^ 64) :
    ∃ x : BitVec 64, x ∉ used := by
  let L : List (BitVec 64) := (List.range (used.length + 1)).map (BitVec.ofNat 64)
  have hnd : L.Nodup := by
    refine nodup_map_on ?_ List.nodup_range
    intro a ha b hb heq
    rw [List.mem_range] at ha hb
    have hnat := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_ofNat] at hnat
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hnat
    exact hnat
  exact Classical.byContradiction fun hall => by
    have hsub : ∀ x ∈ L, x ∈ used := fun x hx =>
      Classical.byContradiction fun hnx => hall ⟨x, hnx⟩
    have hle := nodup_length_le_of_subset hnd hsub
    simp [L] at hle; omega

private theorem exists_fresh_list_bv64 :
    ∀ (n : Nat) (used : List (BitVec 64)), used.length + n ≤ 2 ^ 64 →
      ∃ fs : List (BitVec 64), fs.length = n ∧ fs.Nodup ∧ ∀ x ∈ fs, x ∉ used
  | 0, _, _ => ⟨[], rfl, List.nodup_nil, fun _ h => nomatch h⟩
  | n + 1, used, hlen => by
    obtain ⟨x, hx⟩ := exists_fresh_bv64 used (by omega)
    obtain ⟨fs, hfl, hfnd, hfu⟩ := exists_fresh_list_bv64 n (x :: used) (by simp; omega)
    refine ⟨x :: fs, by simp [hfl], List.nodup_cons.mpr ⟨fun hxm =>
      hfu x hxm List.mem_cons_self, hfnd⟩, fun y hy => ?_⟩
    rcases List.mem_cons.mp hy with rfl | hym
    · exact hx
    · exact fun hu => hfu y hym (List.mem_cons_of_mem _ hu)

private structure TwinHosts (A : Arch) (cs : List (Chunk A)) (h₂ : VllHost A)
    (avoid : List (BitVec 64)) where
  h₁ : VllHost A
  h₁' : VllHost A
  prog₁ : h₁.prog = chunksLhs cs
  prog₁' : h₁'.prog = chunksLhs cs
  lab₁ : h₁.labelAddr = h₂.labelAddr
  lab₁' : h₁'.labelAddr = h₂.labelAddr
  kept₁ : ∀ k j, chunksMap cs k = some j → h₁.addrOf k = h₂.addrOf j
  kept₁' : ∀ k j, chunksMap cs k = some j → h₁'.addrOf k = h₂.addrOf j
  drop_disj_h₂ : ∀ k < (chunksLhs cs).length, chunksMap cs k = none →
    ∀ j ≤ h₂.prog.length, h₁.addrOf k ≠ h₂.addrOf j ∧ h₁'.addrOf k ≠ h₂.addrOf j
  drop_disj_twin : ∀ k₁ < (chunksLhs cs).length, chunksMap cs k₁ = none →
    ∀ k₂ < (chunksLhs cs).length, chunksMap cs k₂ = none → h₁.addrOf k₁ ≠ h₁'.addrOf k₂
  drop_avoid : ∀ k < (chunksLhs cs).length, chunksMap cs k = none →
    ∀ a ∈ avoid, h₁.addrOf k ≠ a ∧ h₁'.addrOf k ≠ a

private theorem mkTwinHosts {A : Arch} {cs : List (Chunk A)} {pc : Bool}
    (hv : ChunksValid A pc cs) {h₂ : VllHost A} (hp₂ : h₂.prog = chunksRhs cs)
    (avoid : List (BitVec 64))
    (hsize : h₂.prog.length + 1 + avoid.length + 2 * (chunksLhs cs).length ≤ 2 ^ 64) :
    Nonempty (TwinHosts A cs h₂ avoid) := by
  let used : List (BitVec 64) :=
    (List.range (h₂.prog.length + 1)).map h₂.addrOf ++ avoid
  have hulen : used.length + 2 * (chunksLhs cs).length ≤ 2 ^ 64 := by
    simp only [used, List.length_append, List.length_map, List.length_range]; omega
  obtain ⟨fs, hflen, hfnd, hfdisj⟩ :=
    exists_fresh_list_bv64 (2 * (chunksLhs cs).length) used hulen
  let n := (chunksLhs cs).length
  have hfs_get : ∀ i (hi : i < 2 * n), fs[i]? = some (fs[i]'(by omega)) := fun i hi =>
    List.getElem?_eq_getElem (by omega)
  have hfs_notin_h₂ : ∀ i (hi : i < 2 * n) j, j ≤ h₂.prog.length →
      fs[i]'(by omega) ≠ h₂.addrOf j := by
    intro i hi j hj heq
    have hmem : fs[i]'(by omega) ∈ used := by
      rw [heq]; apply List.mem_append_left
      exact List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩
    exact hfdisj _ (List.getElem_mem _) hmem
  have hfs_notin_avoid : ∀ i (hi : i < 2 * n) a, a ∈ avoid →
      fs[i]'(by omega) ≠ a := by
    intro i hi a ha heq
    have hmem : fs[i]'(by omega) ∈ used := by rw [heq]; exact List.mem_append_right _ ha
    exact hfdisj _ (List.getElem_mem _) hmem
  have hfs_inj : ∀ i j (hi : i < 2 * n) (hj : j < 2 * n),
      fs[i]'(by omega) = fs[j]'(by omega) → i = j := fun i j hi hj heq =>
    nodup_getElem_inj hfnd (by omega) (by omega) heq
  let mkH (off : Nat) (hoff : off = 0 ∨ off = n) : VllHost A := {
    prog := chunksLhs cs
    addrOf := fun k =>
      match chunksMap cs k with | some j => h₂.addrOf j | none => fs[off + k]?.getD 0#64
    labelAddr := h₂.labelAddr
    addrOf_inj := by
      intro i j hi hj heq
      have hio : off + i < 2 * n := by rcases hoff with rfl | rfl <;> omega
      have hjo : off + j < 2 * n := by rcases hoff with rfl | rfl <;> omega
      cases hmi : chunksMap cs i with
      | some ji =>
        have hjilt : ji < h₂.prog.length := hp₂ ▸ chunksMap_lt hi hmi
        cases hmj : chunksMap cs j with
        | some jj =>
          have hjjlt : jj < h₂.prog.length := hp₂ ▸ chunksMap_lt hj hmj
          simp only [hmi, hmj] at heq
          exact chunksMap_inj hmi ((h₂.addrOf_inj hjilt hjjlt heq) ▸ hmj)
        | none =>
          simp only [hmi, hmj, hfs_get _ hjo, Option.getD_some] at heq
          exact absurd heq.symm (hfs_notin_h₂ _ hjo ji (by omega))
      | none =>
        cases hmj : chunksMap cs j with
        | some jj =>
          have hjjlt : jj < h₂.prog.length := hp₂ ▸ chunksMap_lt hj hmj
          simp only [hmi, hmj, hfs_get _ hio, Option.getD_some] at heq
          exact absurd heq (hfs_notin_h₂ _ hio jj (by omega))
        | none =>
          simp only [hmi, hmj, hfs_get _ hio, hfs_get _ hjo, Option.getD_some] at heq
          have := hfs_inj _ _ hio hjo heq; omega
    labelAddr_wf := by
      intro k l hk hfirst
      obtain ⟨j, hmj, hrj⟩ := chunksMap_label_lhs hv hk
      have hfirstR : ∀ j' < j, h₂.prog[j']? ≠ some (.label l) := by
        intro j' hj' heq
        rw [hp₂] at heq
        obtain ⟨k', hmk', hlk'⟩ := chunksMap_label_rhs hv heq
        have hlt : k' < k :=
          Classical.byContradiction fun hge => by
            rcases Nat.eq_or_lt_of_le (Nat.le_of_not_lt hge) with rfl | hgt
            · rw [hmj] at hmk'; cases hmk'; omega
            · have := chunksMap_mono hgt hmj hmk'; omega
        exact hfirst k' hlt hlk'
      have hwf2 := h₂.labelAddr_wf (hp₂.symm ▸ hrj) hfirstR
      simp only [hmj, hwf2]
  }
  refine ⟨{
    h₁ := mkH 0 (Or.inl rfl)
    h₁' := mkH n (Or.inr rfl)
    prog₁ := rfl
    prog₁' := rfl
    lab₁ := rfl
    lab₁' := rfl
    kept₁ := fun k j hm => by simp [mkH, hm]
    kept₁' := fun k j hm => by simp [mkH, hm]
    drop_disj_h₂ := fun k hk hm j hj => by
      have h1 : 0 + k < 2 * n := by omega
      have h2 : n + k < 2 * n := by omega
      simp only [mkH, hm, hfs_get _ h1, hfs_get _ h2, Option.getD_some]
      exact ⟨hfs_notin_h₂ _ h1 j hj, hfs_notin_h₂ _ h2 j hj⟩
    drop_disj_twin := fun k₁ hk₁ hm₁ k₂ hk₂ hm₂ heq => by
      have h1 : 0 + k₁ < 2 * n := by omega
      have h2 : n + k₂ < 2 * n := by omega
      simp only [mkH, hm₁, hm₂, hfs_get _ h1, hfs_get _ h2, Option.getD_some] at heq
      have := hfs_inj _ _ h1 h2 heq; omega
    drop_avoid := fun k hk hm a ha => by
      have h1 : 0 + k < 2 * n := by omega
      have h2 : n + k < 2 * n := by omega
      simp only [mkH, hm, hfs_get _ h1, hfs_get _ h2, Option.getD_some]
      exact ⟨hfs_notin_avoid _ h1 a ha, hfs_notin_avoid _ h2 a ha⟩
  }⟩

/-! ## 3. Backward (`h₂ → h₁`) & Twin-Host Forward (`h₁, h₁' → h₂`) Simulation -/

private theorem twin_label_addr {A : Arch} {cs : List (Chunk A)} {pc : Bool}
    (hv : ChunksValid A pc cs) {h₂ : VllHost A} (hp₂ : h₂.prog = chunksRhs cs)
    (hu₂ : ∀ (i j : Nat) (l : Sym),
      h₂.prog[i]? = some (Instr.label l) → h₂.prog[j]? = some (Instr.label l) → i = j)
    {avoid : List (BitVec 64)} (T : TwinHosts A cs h₂ avoid) {k : Nat} {l : Sym}
    (hk : (chunksLhs cs)[k]? = some (.label l)) :
    T.h₁.labelAddr l = T.h₁.addrOf k := by
  obtain ⟨j, hmj, hrj⟩ := chunksMap_label_lhs hv hk
  have hfirstR : ∀ j' < j, h₂.prog[j']? ≠ some (.label l) := fun j' hj' heq => by
    have := hu₂ j' j l heq (hp₂.symm ▸ hrj); omega
  rw [T.lab₁, h₂.labelAddr_wf (hp₂.symm ▸ hrj) hfirstR, T.kept₁ k j hmj]

private theorem bwd_skip_dropped {A : Arch} {cs : List (Chunk A)} {pc : Bool}
    (hv : ChunksValid A pc cs) {h₂ : VllHost A} (hp₂ : h₂.prog = chunksRhs cs)
    (hu₂ : ∀ (i j : Nat) (l : Sym),
      h₂.prog[i]? = some (Instr.label l) → h₂.prog[j]? = some (Instr.label l) → i = j)
    {avoid : List (BitVec 64)} (T : TwinHosts A cs h₂ avoid)
    {post : Config A → Prop} {s : MachSt A} :
    ∀ (fuel k : Nat), (chunksLhs cs).length - k ≤ fuel → chunkBoundary cs k = true →
      Eventually (vllStep T.h₁) post ⟨s, h₂.addrOf (chunksTarget cs k)⟩ →
      Eventually (vllStep T.h₁) post ⟨s, T.h₁.addrOf k⟩
  | 0, k, hfuel, _, hev => by
    have hm := chunksMap_ge cs k (by omega)
    rw [chunksTarget_of_map hm] at hev; rw [T.kept₁ k _ hm]; exact hev
  | fuel + 1, k, hfuel, hbnd, hev => by
    by_cases hlt : k < (chunksLhs cs).length
    · cases hm : chunksMap cs k with
      | some j => rw [chunksTarget_of_map hm] at hev; rw [T.kept₁ k j hm]; exact hev
      | none =>
        cases chunks_classify_drop hv hlt hm with
        | noop i hl hrel ht hb =>
          refine step_cps (vllStep T.h₁) post ⟨s, T.h₁.addrOf k⟩
            ⟨k, i, T.prog₁.symm ▸ hl, rfl, ⟨.fall s, (hrel _ _ _ _).mpr rfl⟩,
              (fun s' hr => ?_), (fun _ _ hr => by cases (hrel _ _ _ _).mp hr),
              (fun _ _ hr => by cases (hrel _ _ _ _).mp hr)⟩
          cases (hrel _ _ _ _).mp hr
          exact bwd_skip_dropped hv hp₂ hu₂ T fuel (k + 1) (by omega) hb (ht.symm ▸ hev)
        | fallJmp l hl0 hl1 hm1 =>
          have hlab := twin_label_addr hv hp₂ hu₂ T hl1
          refine step_cps (vllStep T.h₁) post ⟨s, T.h₁.addrOf k⟩
            ⟨k, .jmp l, T.prog₁.symm ▸ hl0, rfl, ⟨.jump (T.h₁.labelAddr l) s, rfl⟩,
              (fun _ hr => by cases hr), (fun pc' s' hr => ?_), (fun _ _ hr => by cases hr)⟩
          cases hr; rw [hlab, T.kept₁ (k + 1) _ hm1]; exact hev
        | fallJcc cond l hl0 hl1 hm1 =>
          have hlab := twin_label_addr hv hp₂ hu₂ T hl1
          have htarget : T.h₁.addrOf (k + 1) = h₂.addrOf (chunksTarget cs k) :=
            T.kept₁ (k + 1) _ hm1
          cases heval : A.evalCond s.flags cond with
          | true =>
            refine step_cps (vllStep T.h₁) post ⟨s, T.h₁.addrOf k⟩
              ⟨k, .jcc cond l, T.prog₁.symm ▸ hl0, rfl,
                ⟨.jump (T.h₁.labelAddr l) s, by simp [instrRel, heval]⟩,
                (fun _ hr => by simp [instrRel, heval] at hr), (fun pc' s' hr => ?_),
                (fun _ _ hr => by simp [instrRel, heval] at hr)⟩
            simp only [instrRel, heval, ↓reduceIte, InstrOut.jump.injEq] at hr
            rcases hr with ⟨rfl, rfl⟩; rw [hlab, htarget]; exact hev
          | false =>
            refine step_cps (vllStep T.h₁) post ⟨s, T.h₁.addrOf k⟩
              ⟨k, .jcc cond l, T.prog₁.symm ▸ hl0, rfl,
                ⟨.fall s, by simp [instrRel, heval]⟩, (fun s' hr => ?_),
                (fun _ _ hr => by simp [instrRel, heval] at hr),
                (fun _ _ hr => by simp [instrRel, heval] at hr)⟩
            simp only [instrRel, heval, Bool.false_eq_true, ↓reduceIte, InstrOut.fall.injEq] at hr
            subst hr; rw [htarget]; exact hev
        | pairSecond _ _ _ hnb => rw [hbnd] at hnb; cases hnb
        | invertSecond _ hnb => rw [hbnd] at hnb; cases hnb
    · have hm := chunksMap_ge cs k (Nat.le_of_not_lt hlt)
      rw [chunksTarget_of_map hm] at hev; rw [T.kept₁ k _ hm]; exact hev

private theorem chunks_bwd_sim {A : Arch} (hwf : A.Wf) {cs : List (Chunk A)} {pc : Bool}
    (hv : ChunksValid A pc cs) {h₂ : VllHost A} (hp₂ : h₂.prog = chunksRhs cs)
    (hu₂ : ∀ (i j : Nat) (l : Sym),
      h₂.prog[i]? = some (Instr.label l) → h₂.prog[j]? = some (Instr.label l) → i = j)
    {avoid : List (BitVec 64)} (T : TwinHosts A cs h₂ avoid)
    {post : Config A → Prop} {st : Config A}
    (hev : Eventually (vllStep h₂) post st) :
    Eventually (vllStep T.h₁) post st := by
  induction hev with
  | done st hp => exact .done st hp
  | step st mid_p hstep _ ih =>
    obtain ⟨j, instr₂, hj, hpc, hex, hfall, hjump, hhalt⟩ := hstep
    have hjlt : j < (chunksRhs cs).length := hp₂ ▸ getElem?_some_lt hj
    obtain ⟨k, hklt, hmk⟩ := chunksMap_surj hjlt
    have hkpc : T.h₁.addrOf k = st.pc := (T.kept₁ k j hmk).trans hpc
    cases chunks_classify_kept hv hklt hmk with
    | same i hl hr ht hb hcall =>
      have hinstr : instr₂ = i := Option.some.inj ((hp₂.symm ▸ hr).symm.trans hj).symm
      subst instr₂
      have hrelEq : ∀ o, instrRel A T.h₁.labelAddr (T.h₁.addrOf (k + 1)) i st.data o ↔
          instrRel A h₂.labelAddr (h₂.addrOf (j + 1)) i st.data o := by
        intro o; rw [T.lab₁]
        cases i with
        | call _ | icall _ => rw [T.kept₁ (k + 1) (j + 1) (hcall rfl)]
        | label _ | pad _ | mov _ _ _ | movi _ _ | alu _ _ _ _ _ _ | cmp _ _ _
        | test _ _ _ | clearFlags | setcc _ _ | load _ _ _ _ | store _ _ _
        | slotSt _ _ | slotLd _ _ | prologue _ | epilogue _ | canonAbi _ _
        | jmp _ | jcc _ _ | jnzGpr _ _ | ret | exitJmp _ | tailJmpR _
        | symAddr _ _ | ijmp _ | native _ => exact Iff.rfl
      obtain ⟨o₀, ho₀⟩ := hex
      refine step_cps (vllStep T.h₁) post st
        ⟨k, i, T.prog₁.symm ▸ hl, hkpc, ⟨o₀, (hrelEq o₀).mpr ho₀⟩, (fun s' hr1 => ?_),
          (fun pc' s' hr1 => ih ⟨s', pc'⟩ (hjump pc' s' ((hrelEq _).mp hr1))),
          (fun c s' hr1 => hhalt c s' ((hrelEq _).mp hr1))⟩
      have hnext := ih ⟨s', h₂.addrOf (j + 1)⟩ (hfall s' ((hrelEq _).mp hr1))
      exact bwd_skip_dropped hv hp₂ hu₂ T ((chunksLhs cs).length - (k + 1)) (k + 1)
        (Nat.le_refl _) hb (ht.symm ▸ hnext)
    | pairDet i₁ i₂ i' hl1 hl2 hr _ _ ht2 hb hd =>
      have hinstr : instr₂ = i' := Option.some.inj ((hp₂.symm ▸ hr).symm.trans hj).symm
      subst instr₂
      obtain ⟨s₁, s₂, h1, h2, h3⟩ := (hd h₂.labelAddr).spec st.data
      have hnext := ih ⟨s₂, h₂.addrOf (j + 1)⟩ (hfall s₂ ((h3 _ _).mpr rfl))
      refine step_cps (vllStep T.h₁) post st
        ⟨k, i₁, T.prog₁.symm ▸ hl1, hkpc, ⟨.fall s₁, T.lab₁.symm ▸ (h1 _ _).mpr rfl⟩,
          (fun s₁' hr1 => ?_), (fun _ _ hr1 => by cases (h1 _ _).mp (T.lab₁ ▸ hr1)),
          (fun _ _ hr1 => by cases (h1 _ _).mp (T.lab₁ ▸ hr1))⟩
      cases (h1 _ _).mp (T.lab₁ ▸ hr1)
      refine step_cps (vllStep T.h₁) post ⟨s₁, T.h₁.addrOf (k + 1)⟩
        ⟨k + 1, i₂, T.prog₁.symm ▸ hl2, rfl, ⟨.fall s₂, T.lab₁.symm ▸ (h2 _ _).mpr rfl⟩,
          (fun s₂' hr2 => ?_), (fun _ _ hr2 => by cases (h2 _ _).mp (T.lab₁ ▸ hr2)),
          (fun _ _ hr2 => by cases (h2 _ _).mp (T.lab₁ ▸ hr2))⟩
      cases (h2 _ _).mp (T.lab₁ ▸ hr2)
      exact bwd_skip_dropped hv hp₂ hu₂ T ((chunksLhs cs).length - (k + 2)) (k + 2)
        (Nat.le_refl _) hb (ht2.symm ▸ hnext)
    | invertJcc cond l₁ l₂ hl0 hl1 hl2 hr0 _ _ hm2 =>
      have hinstr : instr₂ = .jcc (A.negCond cond) l₂ :=
        Option.some.inj ((hp₂.symm ▸ hr0).symm.trans hj).symm
      subst instr₂
      have hlab1 := twin_label_addr hv hp₂ hu₂ T hl2
      cases hev_c : A.evalCond st.data.flags cond with
      | true =>
        have hneg : A.evalCond st.data.flags (A.negCond cond) = false := by
          rw [hwf.negCond_eval, hev_c]; rfl
        have hnext := ih ⟨st.data, h₂.addrOf (j + 1)⟩ (hfall st.data (by simp [instrRel, hneg]))
        refine step_cps (vllStep T.h₁) post st
          ⟨k, .jcc cond l₁, T.prog₁.symm ▸ hl0, hkpc,
            ⟨.jump (T.h₁.labelAddr l₁) st.data, by simp [instrRel, hev_c]⟩,
            (fun _ hr => by simp [instrRel, hev_c] at hr), (fun pc' s' hr => ?_),
            (fun _ _ hr => by simp [instrRel, hev_c] at hr)⟩
        simp only [instrRel, hev_c, ↓reduceIte, InstrOut.jump.injEq] at hr
        rcases hr with ⟨rfl, rfl⟩; rw [hlab1, T.kept₁ (k + 2) (j + 1) hm2]; exact hnext
      | false =>
        have hneg : A.evalCond st.data.flags (A.negCond cond) = true := by
          rw [hwf.negCond_eval, hev_c]; rfl
        have hnext := ih ⟨st.data, h₂.labelAddr l₂⟩
          (hjump (h₂.labelAddr l₂) st.data (by simp [instrRel, hneg]))
        refine step_cps (vllStep T.h₁) post st
          ⟨k, .jcc cond l₁, T.prog₁.symm ▸ hl0, hkpc,
            ⟨.fall st.data, by simp [instrRel, hev_c]⟩, (fun s' hr => ?_),
            (fun _ _ hr => by simp [instrRel, hev_c] at hr),
            (fun _ _ hr => by simp [instrRel, hev_c] at hr)⟩
        simp only [instrRel, hev_c, Bool.false_eq_true, ↓reduceIte, InstrOut.fall.injEq] at hr
        subst hr
        refine step_cps (vllStep T.h₁) post ⟨st.data, T.h₁.addrOf (k + 1)⟩
          ⟨k + 1, .jmp l₂, T.prog₁.symm ▸ hl1, rfl, ⟨.jump (T.h₁.labelAddr l₂) st.data, rfl⟩,
            (fun _ hr => by cases hr), (fun pc' s' hr => ?_), (fun _ _ hr => by cases hr)⟩
        cases hr; rw [T.lab₁]; exact hnext

private def TwinHosts.swap {A : Arch} {cs : List (Chunk A)} {h₂ : VllHost A}
    {avoid : List (BitVec 64)} (T : TwinHosts A cs h₂ avoid) : TwinHosts A cs h₂ avoid where
  h₁ := T.h₁'
  h₁' := T.h₁
  prog₁ := T.prog₁'
  prog₁' := T.prog₁
  lab₁ := T.lab₁'
  lab₁' := T.lab₁
  kept₁ := T.kept₁'
  kept₁' := T.kept₁
  drop_disj_h₂ := fun k hk hm j hj => (T.drop_disj_h₂ k hk hm j hj).symm
  drop_disj_twin := fun k₁ hk₁ hm₁ k₂ hk₂ hm₂ => (T.drop_disj_twin k₂ hk₂ hm₂ k₁ hk₁ hm₁).symm
  drop_avoid := fun k hk hm a ha => (T.drop_avoid k hk hm a ha).symm

private def DroppedTarget {A : Arch} (cs : List (Chunk A)) (h₂ : VllHost A)
    (k : Nat) (s : MachSt A) (st₂ : Config A) : Prop :=
  (chunkBoundary cs k = true ∧ st₂ = ⟨s, h₂.addrOf (chunksTarget cs k)⟩) ∨
  (∃ i₂ s₂, (chunksLhs cs)[k]? = some i₂ ∧
    (∀ np, instrRel A h₂.labelAddr np i₂ s (.fall s₂)) ∧
    st₂ = ⟨s₂, h₂.addrOf (chunksTarget cs k)⟩) ∨
  (∃ l₂, (chunksLhs cs)[k]? = some (.jmp l₂) ∧ st₂ = ⟨s, h₂.labelAddr l₂⟩)

private theorem vllStep_inv_at {A : Arch} {h : VllHost A} {k : Nat} {instr : Instr A}
    {s : MachSt A} {post : Config A → Prop}
    (hk : h.prog[k]? = some instr) (hnot : ¬post ⟨s, h.addrOf k⟩)
    (hev : Eventually (vllStep h) post ⟨s, h.addrOf k⟩) :
    (∃ o, instrRel A h.labelAddr (h.addrOf (k + 1)) instr s o) ∧
    (∀ s', instrRel A h.labelAddr (h.addrOf (k + 1)) instr s (.fall s') →
      Eventually (vllStep h) post ⟨s', h.addrOf (k + 1)⟩) ∧
    (∀ pc' s', instrRel A h.labelAddr (h.addrOf (k + 1)) instr s (.jump pc' s') →
      Eventually (vllStep h) post ⟨s', pc'⟩) ∧
    (∀ c s', instrRel A h.labelAddr (h.addrOf (k + 1)) instr s (.halt c s') → False) := by
  cases hev with
  | done _ hp => exact absurd hp hnot
  | step _ _ hstep hcont =>
    obtain ⟨k', i', hk', hpc, hex, hfall, hjump, hhalt⟩ := hstep
    have hklt : k < h.prog.length := getElem?_some_lt hk
    have hk'lt : k' < h.prog.length := getElem?_some_lt hk'
    have heqk : k' = k := h.addrOf_inj hk'lt hklt hpc
    subst heqk
    have heqi : i' = instr := Option.some.inj (hk'.symm.trans hk)
    subst heqi
    exact ⟨hex, fun s' hr => hcont _ (hfall s' hr), fun pc' s' hr => hcont _ (hjump pc' s' hr),
      hhalt⟩

private theorem chunks_twinHost_sim {A : Arch} (hwf : A.Wf) {cs : List (Chunk A)} {pc : Bool}
    (hv : ChunksValid A pc cs) {h₂ : VllHost A} (hp₂ : h₂.prog = chunksRhs cs)
    (hu₂ : ∀ (i j : Nat) (l : Sym),
      h₂.prog[i]? = some (Instr.label l) → h₂.prog[j]? = some (Instr.label l) → i = j)
    {avoid : List (BitVec 64)} (T : TwinHosts A cs h₂ avoid)
    {post : Config A → Prop}
    (hnoDrop : ∀ k < (chunksLhs cs).length, chunksMap cs k = none →
      ∀ s, ¬post ⟨s, T.h₁.addrOf k⟩ ∧ ¬post ⟨s, T.h₁'.addrOf k⟩)
    {st₁ : Config A} (e₁ : Eventually (vllStep T.h₁) post st₁) :
    ((∀ k < (chunksLhs cs).length, chunksMap cs k = none → st₁.pc ≠ T.h₁.addrOf k) →
      Eventually (vllStep T.h₁') post st₁ →
      Eventually (vllStep h₂) post st₁) ∧
    (∀ k < (chunksLhs cs).length, chunksMap cs k = none → st₁.pc = T.h₁.addrOf k →
      ∀ st₂, DroppedTarget cs h₂ k st₁.data st₂ →
      Eventually (vllStep T.h₁') post ⟨st₁.data, T.h₁'.addrOf k⟩ →
      Eventually (vllStep h₂) post st₂) := by
  have hkept_le_not_drop : ∀ k j, k ≤ (chunksLhs cs).length → chunksMap cs k = some j →
      ∀ d < (chunksLhs cs).length, chunksMap cs d = none → T.h₁.addrOf k ≠ T.h₁.addrOf d := by
    intro k j hkle hmk d hdlt hmd heq
    rcases Nat.lt_or_eq_of_le hkle with hklt | rfl
    · have := T.h₁.addrOf_inj (T.prog₁.symm ▸ hklt) (T.prog₁.symm ▸ hdlt) heq
      subst this; rw [hmk] at hmd; cases hmd
    · have hm := chunksMap_ge cs (chunksLhs cs).length (Nat.le_refl _)
      have hj' : (chunksRhs cs).length + ((chunksLhs cs).length - (chunksLhs cs).length) =
          h₂.prog.length := by rw [hp₂]; omega
      rw [T.kept₁ _ _ hm, hj'] at heq
      exact (T.drop_disj_h₂ d hdlt hmd h₂.prog.length (Nat.le_refl _)).1 heq.symm
  have hjump_resolve : ∀ {pc' : BitVec 64} {s' : MachSt A},
      ((∀ d < (chunksLhs cs).length, chunksMap cs d = none → pc' ≠ T.h₁.addrOf d) →
        Eventually (vllStep T.h₁') post ⟨s', pc'⟩ → Eventually (vllStep h₂) post ⟨s', pc'⟩) →
      Eventually (vllStep T.h₁') post ⟨s', pc'⟩ →
      Eventually (vllStep h₂) post ⟨s', pc'⟩ := by
    intro pc' s' hcase1 he1'
    by_cases hdrop : ∃ d < (chunksLhs cs).length, chunksMap cs d = none ∧ pc' = T.h₁.addrOf d
    · obtain ⟨d, hdlt, hmd, rfl⟩ := hdrop
      cases he1' with
      | done _ hp => exact .done _ hp
      | step _ _ hst' _ =>
        obtain ⟨k', _, hk', hpc', _, _, _, _⟩ := hst'
        have hk'lt : k' < (chunksLhs cs).length :=
          T.prog₁' ▸ getElem?_some_lt hk'
        cases hmk' : chunksMap cs k' with
        | some j' =>
          have hj'lt : j' < h₂.prog.length := hp₂ ▸ chunksMap_lt hk'lt hmk'
          rw [T.kept₁' k' j' hmk'] at hpc'
          exact absurd hpc'.symm ((T.drop_disj_h₂ d hdlt hmd j' (by omega)).1)
        | none =>
          exact absurd hpc'.symm (T.drop_disj_twin d hdlt hmd k' hk'lt hmk')
    · exact hcase1 (fun d hdlt hmd heq => hdrop ⟨d, hdlt, hmd, heq⟩) he1'
  induction e₁ with
  | done st hp =>
    refine ⟨fun _ _ => .done st hp, fun k hk hmk hpc _ _ _ => ?_⟩
    exact absurd (by cases st; simp only at hpc; subst hpc; exact hp) (hnoDrop k hk hmk st.data).1
  | step st mid_p hstep _ ih =>
    obtain ⟨k, instr, hk, hpc, hex, hfall, hjump, hhalt⟩ := hstep
    have hklt : k < (chunksLhs cs).length := T.prog₁ ▸ getElem?_some_lt hk
    have hkL : (chunksLhs cs)[k]? = some instr := T.prog₁ ▸ hk
    constructor
    · intro hnotDrop he1'
      cases hmk : chunksMap cs k with
      | none => exact absurd hpc.symm (hnotDrop k hklt hmk)
      | some j =>
        cases he1' with
        | done _ hp => exact .done st hp
        | step _ mid_p' hstep' hcont' =>
          obtain ⟨k', i', hk', hpc', _, hfall', hjump', _⟩ := hstep'
          have hk'lt : k' < (chunksLhs cs).length :=
            T.prog₁' ▸ getElem?_some_lt hk'
          have heqkk' : k' = k := by
            have hst_kept : T.h₁'.addrOf k = st.pc :=
              (T.kept₁' k j hmk).trans ((T.kept₁ k j hmk).symm.trans hpc)
            exact T.h₁'.addrOf_inj (T.prog₁'.symm ▸ hk'lt) (T.prog₁'.symm ▸ hklt)
              (hpc'.trans hst_kept.symm)
          subst k'
          have heqi' : i' = instr := Option.some.inj (hk'.symm.trans (T.prog₁'.symm ▸ hkL))
          subst i'
          have h2pc : h₂.addrOf j = st.pc := (T.kept₁ k j hmk).symm.trans hpc
          cases chunks_classify_kept hv hklt hmk with
          | same i hl hr ht hb hcall =>
            have heqi : instr = i := Option.some.inj (hkL.symm.trans hl)
            subst instr
            have hrelEq : ∀ o, instrRel A h₂.labelAddr (h₂.addrOf (j + 1)) i st.data o ↔
                instrRel A T.h₁.labelAddr (T.h₁.addrOf (k + 1)) i st.data o := by
              intro o; rw [T.lab₁]
              cases i with
              | call _ | icall _ => rw [T.kept₁ (k + 1) (j + 1) (hcall rfl)]
              | label _ | pad _ | mov _ _ _ | movi _ _ | alu _ _ _ _ _ _ | cmp _ _ _
              | test _ _ _ | clearFlags | setcc _ _ | load _ _ _ _ | store _ _ _
              | slotSt _ _ | slotLd _ _ | prologue _ | epilogue _ | canonAbi _ _
              | jmp _ | jcc _ _ | jnzGpr _ _ | ret | exitJmp _ | tailJmpR _
              | symAddr _ _ | ijmp _ | native _ => exact Iff.rfl
            have hrelEq' : ∀ o, instrRel A T.h₁'.labelAddr (T.h₁'.addrOf (k + 1)) i st.data o ↔
                instrRel A T.h₁.labelAddr (T.h₁.addrOf (k + 1)) i st.data o := by
              intro o; rw [T.lab₁, T.lab₁']
              cases i with
              | call _ | icall _ =>
                rw [T.kept₁ (k + 1) (j + 1) (hcall rfl), T.kept₁' (k + 1) (j + 1) (hcall rfl)]
              | label _ | pad _ | mov _ _ _ | movi _ _ | alu _ _ _ _ _ _ | cmp _ _ _
              | test _ _ _ | clearFlags | setcc _ _ | load _ _ _ _ | store _ _ _
              | slotSt _ _ | slotLd _ _ | prologue _ | epilogue _ | canonAbi _ _
              | jmp _ | jcc _ _ | jnzGpr _ _ | ret | exitJmp _ | tailJmpR _
              | symAddr _ _ | ijmp _ | native _ => exact Iff.rfl
            obtain ⟨o₀, ho₀⟩ := hex
            refine step_cps (vllStep h₂) post st
              ⟨j, i, hp₂.symm ▸ hr, h2pc, ⟨o₀, (hrelEq o₀).mpr ho₀⟩, (fun s' hr2 => ?_),
                (fun pc' s' hr2 => ?_), (fun c s' hr2 => hhalt c s' ((hrelEq _).mp hr2))⟩
            · have hr1 := (hrelEq _).mp hr2
              have hih := ih ⟨s', T.h₁.addrOf (k + 1)⟩ (hfall s' hr1)
              have he1'_next := hcont' _ (hfall' s' ((hrelEq' _).mpr hr1))
              cases hmk1 : chunksMap cs (k + 1) with
              | some j1 =>
                have hj1 : j1 = j + 1 := (chunksTarget_of_map hmk1).symm.trans ht
                subst hj1
                have heqA := T.kept₁ (k + 1) (j + 1) hmk1
                have heqA' := T.kept₁' (k + 1) (j + 1) hmk1
                rw [heqA] at hih; rw [heqA'] at he1'_next
                exact hih.1 (fun d hdlt hmd => heqA ▸
                  hkept_le_not_drop (k + 1) (j + 1) (by omega) hmk1 d hdlt hmd) he1'_next
              | none =>
                have hk1lt : k + 1 < (chunksLhs cs).length :=
                  Classical.byContradiction fun hge => by
                    have := chunksMap_ge cs (k + 1) (Nat.le_of_not_lt hge)
                    rw [hmk1] at this; cases this
                exact hih.2 (k + 1) hk1lt hmk1 rfl ⟨s', h₂.addrOf (j + 1)⟩
                  (Or.inl ⟨hb, by rw [ht]⟩) he1'_next
            · have hr1 := (hrelEq _).mp hr2
              exact hjump_resolve (ih ⟨s', pc'⟩ (hjump pc' s' hr1)).1
                (hcont' _ (hjump' pc' s' ((hrelEq' _).mpr hr1)))
          | pairDet i₁ i₂ i' hl1 hl2 hr hm1 ht1 _ _ hd =>
            have heqi : instr = i₁ := Option.some.inj (hkL.symm.trans hl1)
            subst instr
            obtain ⟨s₁, s₂, h1, h2, h3⟩ := (hd h₂.labelAddr).spec st.data
            have hk1lt : k + 1 < (chunksLhs cs).length := getElem?_some_lt hl2
            refine step_cps (vllStep h₂) post st
              ⟨j, i', hp₂.symm ▸ hr, h2pc, ⟨.fall s₂, (h3 _ _).mpr rfl⟩, (fun s₂' hr2 => ?_),
                (fun _ _ hr2 => by cases (h3 _ _).mp hr2),
                (fun _ _ hr2 => by cases (h3 _ _).mp hr2)⟩
            cases (h3 _ _).mp hr2
            have hih := ih ⟨s₁, T.h₁.addrOf (k + 1)⟩ (hfall s₁ (T.lab₁.symm ▸ (h1 _ _).mpr rfl))
            have he1'_next := hcont' _ (hfall' s₁ (T.lab₁'.symm ▸ (h1 _ _).mpr rfl))
            exact hih.2 (k + 1) hk1lt hm1 rfl ⟨s₂, h₂.addrOf (j + 1)⟩
              (Or.inr (Or.inl ⟨i₂, s₂, hl2, fun np => (h2 np _).mpr rfl, by rw [ht1]⟩)) he1'_next
          | invertJcc cond l₁ l₂ hl0 hl1 hl2 hr0 _ hm1 hm2 =>
            have heqi : instr = .jcc cond l₁ := Option.some.inj (hkL.symm.trans hl0)
            subst instr
            have hk1lt : k + 1 < (chunksLhs cs).length := getElem?_some_lt hl1
            have hk2lt : k + 2 < (chunksLhs cs).length := getElem?_some_lt hl2
            have hlab1 := twin_label_addr hv hp₂ hu₂ T hl2
            cases hev_c : A.evalCond st.data.flags cond with
            | true =>
              have hneg : A.evalCond st.data.flags (A.negCond cond) = false := by
                rw [hwf.negCond_eval, hev_c]; rfl
              refine step_cps (vllStep h₂) post st
                ⟨j, .jcc (A.negCond cond) l₂, hp₂.symm ▸ hr0, h2pc,
                  ⟨.fall st.data, by simp [instrRel, hneg]⟩, (fun s' hr2 => ?_),
                  (fun _ _ hr2 => by simp [instrRel, hneg] at hr2),
                  (fun _ _ hr2 => by simp [instrRel, hneg] at hr2)⟩
              simp only [instrRel, hneg, Bool.false_eq_true, ↓reduceIte, InstrOut.fall.injEq] at hr2
              subst hr2
              have hih := ih ⟨st.data, T.h₁.labelAddr l₁⟩
                (hjump (T.h₁.labelAddr l₁) st.data (by simp [instrRel, hev_c]))
              have he1'_next := hcont' _
                (hjump' (T.h₁'.labelAddr l₁) st.data (by simp [instrRel, hev_c]))
              have heqA : T.h₁.labelAddr l₁ = h₂.addrOf (j + 1) :=
                hlab1.trans (T.kept₁ (k + 2) (j + 1) hm2)
              rw [T.lab₁', ← T.lab₁, heqA] at he1'_next
              rw [heqA] at hih
              exact hih.1 (fun d hdlt hmd => (hlab1.symm.trans heqA) ▸
                hkept_le_not_drop (k + 2) (j + 1) (by omega) hm2 d hdlt hmd) he1'_next
            | false =>
              have hneg : A.evalCond st.data.flags (A.negCond cond) = true := by
                rw [hwf.negCond_eval, hev_c]; rfl
              refine step_cps (vllStep h₂) post st
                ⟨j, .jcc (A.negCond cond) l₂, hp₂.symm ▸ hr0, h2pc,
                  ⟨.jump (h₂.labelAddr l₂) st.data, by simp [instrRel, hneg]⟩,
                  (fun _ hr2 => by simp [instrRel, hneg] at hr2), (fun pc' s' hr2 => ?_),
                  (fun _ _ hr2 => by simp [instrRel, hneg] at hr2)⟩
              simp only [instrRel, hneg, ↓reduceIte, InstrOut.jump.injEq] at hr2
              rcases hr2 with ⟨rfl, rfl⟩
              have hih := ih ⟨st.data, T.h₁.addrOf (k + 1)⟩
                (hfall st.data (by simp [instrRel, hev_c]))
              have he1'_next := hcont' _ (hfall' st.data (by simp [instrRel, hev_c]))
              exact hih.2 (k + 1) hk1lt hm1 rfl ⟨st.data, h₂.labelAddr l₂⟩
                (Or.inr (Or.inr ⟨l₂, hl1, rfl⟩)) he1'_next
    · intro d hdlt hmd hdpc st₂ hdt he1'
      have heqkd : k = d := T.h₁.addrOf_inj (T.prog₁.symm ▸ hklt) (T.prog₁.symm ▸ hdlt)
        (hpc.trans hdpc)
      subst d
      have hinv' := vllStep_inv_at (T.prog₁'.symm ▸ hkL) (hnoDrop k hklt hmd st.data).2 he1'
      cases chunks_classify_drop hv hklt hmd with
      | noop i hl hrel ht hb =>
        have heqi : instr = i := Option.some.inj (hkL.symm.trans hl)
        subst instr
        have hst₂ : st₂ = ⟨st.data, h₂.addrOf (chunksTarget cs k)⟩ := by
          rcases hdt with ⟨_, rfl⟩ | ⟨i₂, s₂, hl2, hr2, rfl⟩ | ⟨l₂, hl2, rfl⟩
          · rfl
          · have heq := Option.some.inj (hl2.symm.trans hl); subst i₂
            cases (hrel _ _ _ _).mp (hr2 0#64); rfl
          · have heq := Option.some.inj (hl2.symm.trans hl); subst i
            have := (hrel h₂.labelAddr 0#64 st.data (.jump (h₂.labelAddr l₂) st.data)).mp rfl
            cases this
        subst hst₂
        have hih := ih ⟨st.data, T.h₁.addrOf (k + 1)⟩ (hfall st.data ((hrel _ _ _ _).mpr rfl))
        have he1'_next := hinv'.2.1 st.data ((hrel _ _ _ _).mpr rfl)
        cases hmk1 : chunksMap cs (k + 1) with
        | some j1 =>
          have hj1 : j1 = chunksTarget cs k := (chunksTarget_of_map hmk1).symm.trans ht
          subst j1
          have heqA := T.kept₁ (k + 1) (chunksTarget cs k) hmk1
          have heqA' := T.kept₁' (k + 1) (chunksTarget cs k) hmk1
          rw [heqA] at hih; rw [heqA'] at he1'_next
          exact hih.1 (fun d' hd' hmd' => heqA ▸
            hkept_le_not_drop (k + 1) (chunksTarget cs k) (by omega) hmk1 d' hd' hmd') he1'_next
        | none =>
          have hk1lt : k + 1 < (chunksLhs cs).length :=
            Classical.byContradiction fun hge => by
              have := chunksMap_ge cs (k + 1) (Nat.le_of_not_lt hge)
              rw [hmk1] at this; cases this
          exact hih.2 (k + 1) hk1lt hmk1 rfl ⟨st.data, h₂.addrOf (chunksTarget cs k)⟩
            (Or.inl ⟨hb, by rw [ht]⟩) he1'_next
      | fallJmp l hl0 hl1 hm1 =>
        have heqi : instr = .jmp l := Option.some.inj (hkL.symm.trans hl0)
        subst instr
        have hlab := twin_label_addr hv hp₂ hu₂ T hl1
        have heqA : T.h₁.labelAddr l = h₂.addrOf (chunksTarget cs k) :=
          hlab.trans (T.kept₁ (k + 1) _ hm1)
        have hst₂ : st₂ = ⟨st.data, h₂.addrOf (chunksTarget cs k)⟩ := by
          rcases hdt with ⟨_, rfl⟩ | ⟨i₂, _, hl2, hr2, _⟩ | ⟨l₂, hl2, rfl⟩
          · rfl
          · have heq := Option.some.inj (hl2.symm.trans hl0); subst i₂; cases hr2 0#64
          · have heq := Option.some.inj (hl2.symm.trans hl0); cases heq; rw [← T.lab₁, heqA]
        subst hst₂
        have hih := ih ⟨st.data, T.h₁.labelAddr l⟩ (hjump (T.h₁.labelAddr l) st.data rfl)
        have he1'_next := hinv'.2.2.1 (T.h₁'.labelAddr l) st.data rfl
        rw [T.lab₁', ← T.lab₁, heqA] at he1'_next
        rw [heqA] at hih
        exact hih.1 (fun d' hd' hmd' => (hlab.symm.trans heqA) ▸
          hkept_le_not_drop (k + 1) _ (by omega) hm1 d' hd' hmd') he1'_next
      | fallJcc cond l hl0 hl1 hm1 =>
        have heqi : instr = .jcc cond l := Option.some.inj (hkL.symm.trans hl0)
        subst instr
        have hlab := twin_label_addr hv hp₂ hu₂ T hl1
        have heqA : T.h₁.addrOf (k + 1) = h₂.addrOf (chunksTarget cs k) := T.kept₁ (k + 1) _ hm1
        have heqA' : T.h₁'.addrOf (k + 1) = h₂.addrOf (chunksTarget cs k) := T.kept₁' (k + 1) _ hm1
        have hst₂ : st₂ = ⟨st.data, h₂.addrOf (chunksTarget cs k)⟩ := by
          rcases hdt with ⟨_, rfl⟩ | ⟨i₂, s₂, hl2, hr2, rfl⟩ | ⟨l₂, hl2, _⟩
          · rfl
          · have heq := Option.some.inj (hl2.symm.trans hl0); subst i₂
            have h2 := hr2 0#64
            cases hev_c : A.evalCond st.data.flags cond <;> simp [instrRel, hev_c] at h2
            subst h2; rfl
          · have heq := Option.some.inj (hl2.symm.trans hl0); cases heq
        subst hst₂
        cases hev_c : A.evalCond st.data.flags cond with
        | true =>
          have hih := ih ⟨st.data, T.h₁.labelAddr l⟩
            (hjump (T.h₁.labelAddr l) st.data (by simp [instrRel, hev_c]))
          have he1'_next := hinv'.2.2.1 (T.h₁'.labelAddr l) st.data (by simp [instrRel, hev_c])
          rw [T.lab₁', ← T.lab₁, hlab, heqA] at he1'_next
          rw [hlab, heqA] at hih
          exact hih.1 (fun d' hd' hmd' => heqA ▸
            hkept_le_not_drop (k + 1) _ (by omega) hm1 d' hd' hmd') he1'_next
        | false =>
          have hih := ih ⟨st.data, T.h₁.addrOf (k + 1)⟩
            (hfall st.data (by simp [instrRel, hev_c]))
          have he1'_next := hinv'.2.1 st.data (by simp [instrRel, hev_c])
          rw [heqA'] at he1'_next; rw [heqA] at hih
          exact hih.1 (fun d' hd' hmd' => heqA ▸
            hkept_le_not_drop (k + 1) _ (by omega) hm1 d' hd' hmd') he1'_next
      | pairSecond i₁ i₂ i' hnb hl hnj ht hb =>
        have heqi : instr = i₂ := Option.some.inj (hkL.symm.trans hl)
        subst instr
        rcases hdt with ⟨hb', _⟩ | ⟨i₂', s₂, hl2, hr2, rfl⟩ | ⟨l₂, hl2, _⟩
        · rw [hnb] at hb'; cases hb'
        · have heq2 : i₂' = i₂ := Option.some.inj (hl2.symm.trans hl)
          subst i₂'
          have hih := ih ⟨s₂, T.h₁.addrOf (k + 1)⟩
            (hfall s₂ (T.lab₁.symm ▸ hr2 (T.h₁.addrOf (k + 1))))
          have he1'_next := hinv'.2.1 s₂ (T.lab₁'.symm ▸ hr2 (T.h₁'.addrOf (k + 1)))
          cases hmk1 : chunksMap cs (k + 1) with
          | some j1 =>
            have hj1 : j1 = chunksTarget cs k := (chunksTarget_of_map hmk1).symm.trans ht
            subst j1
            have heqA := T.kept₁ (k + 1) (chunksTarget cs k) hmk1
            have heqA' := T.kept₁' (k + 1) (chunksTarget cs k) hmk1
            rw [heqA] at hih; rw [heqA'] at he1'_next
            exact hih.1 (fun d' hd' hmd' => heqA ▸
              hkept_le_not_drop (k + 1) (chunksTarget cs k) (by omega) hmk1 d' hd' hmd') he1'_next
          | none =>
            have hk1lt : k + 1 < (chunksLhs cs).length :=
              Classical.byContradiction fun hge => by
                have := chunksMap_ge cs (k + 1) (Nat.le_of_not_lt hge)
                rw [hmk1] at this; cases this
            exact hih.2 (k + 1) hk1lt hmk1 rfl ⟨s₂, h₂.addrOf (chunksTarget cs k)⟩
              (Or.inl ⟨hb, by rw [ht]⟩) he1'_next
        · exact absurd (Option.some.inj (hl.symm.trans hl2)) (hnj l₂)
      | invertSecond l₂ hnb hl =>
        have heqi : instr = .jmp l₂ := Option.some.inj (hkL.symm.trans hl)
        subst instr
        rcases hdt with ⟨hb', _⟩ | ⟨i₂, _, hl2, hr2, _⟩ | ⟨l₂', hl2, rfl⟩
        · rw [hnb] at hb'; cases hb'
        · have heq := Option.some.inj (hl2.symm.trans hl); subst i₂; cases hr2 0#64
        · have heq : l₂' = l₂ := Instr.jmp.inj (Option.some.inj (hl2.symm.trans hl))
          subst l₂'
          have hih := ih ⟨st.data, T.h₁.labelAddr l₂⟩ (hjump (T.h₁.labelAddr l₂) st.data rfl)
          have he1'_next := hinv'.2.2.1 (T.h₁'.labelAddr l₂) st.data rfl
          rw [T.lab₁] at hih; rw [T.lab₁'] at he1'_next
          exact hjump_resolve hih.1 he1'_next

/-! ## 4. Generic Chunk `FnSpec` Transfer & Pass Chunk Witnesses -/

private theorem chunks_labelsUnique_lhs {A : Arch} {cs : List (Chunk A)} {pc : Bool}
    (hv : ChunksValid A pc cs) {h₂ : VllHost A} (hp₂ : h₂.prog = chunksRhs cs)
    (hu₂ : ∀ (i j : Nat) (l : Sym),
      h₂.prog[i]? = some (Instr.label l) → h₂.prog[j]? = some (Instr.label l) → i = j) :
    ∀ (i j : Nat) (l : Sym),
      (chunksLhs cs)[i]? = some (Instr.label l) →
      (chunksLhs cs)[j]? = some (Instr.label l) → i = j := by
  intro i j l hi hj
  obtain ⟨ji, hmi, hri⟩ := chunksMap_label_lhs hv hi
  obtain ⟨jj, hmj, hrj⟩ := chunksMap_label_lhs hv hj
  have heqj := hu₂ ji jj l (hp₂.symm ▸ hri) (hp₂.symm ▸ hrj)
  subst heqj
  exact chunksMap_inj hmi hmj

private theorem chunks_defined_iff {A : Arch} (hwf : A.Wf) (P : VllPolicy A)
    {cs : List (Chunk A)} {pc : Bool} (hv : ChunksValid A pc cs)
    {h₁ h₂ : VllHost A} (hp₁ : h₁.prog = chunksLhs cs) (hp₂ : h₂.prog = chunksRhs cs) (l : Sym) :
    (vllTarget A hwf P).Defined h₁ l ↔ (vllTarget A hwf P).Defined h₂ l := by
  simp only [Target.Defined, vllTarget, vllIsa, vllIsaOfHooks, vllFrameIsaOfHooks,
    vllFrameIsa, vllMach]
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨j, _, hr⟩ := chunksMap_label_lhs hv (hp₁ ▸ hk)
    exact ⟨j, hp₂.symm ▸ hr⟩
  · rintro ⟨j, hj⟩
    obtain ⟨k, _, hl⟩ := chunksMap_label_rhs hv (hp₂ ▸ hj)
    exact ⟨k, hp₁.symm ▸ hl⟩

private abbrev vllFnPost {A : Arch} (hwf : A.Wf) (P : VllPolicy A) (host : VllHost A)
    {bs : List Ty} (s : MachSt A) (ra : BitVec 64) (n nX : Nat) (Q : Post bs) (X : XPost)
    (R : Mem 64 → Prop) : Config A → Prop :=
  fun st =>
    (st.pc = ra ∧ ∃ rets m', Q rets m' ∧ (vllTarget A hwf P).RetsIn rets st.data ∧
      (vllTarget A hwf P).Restored s st.data ∧
      (st.data.mem =⋆ Eq m' ⋆ (vllTarget A hwf P).Exit (s.gpr A.abi.sp) n ⋆ R)) ∨
    (∃ sym' cs' xs m', X sym' cs' xs m' ∧ (vllTarget A hwf P).Defined host sym' ∧
      st.pc = host.labelAddr sym' ∧ (vllTarget A hwf P).ArgsIn xs st.data ∧
      A.abi.spEntry (st.data.gpr A.abi.sp) ∧
      ∃ ra' n' F, nX ≤ n' ∧ n' + A.abi.raBytes ≤ 2 ^ 64 ∧
        (vllFramePreds A).raReg st.data ra' ∧
        (st.data.mem =⋆ Eq m' ⋆ (vllTarget A hwf P).Entry (st.data.gpr A.abi.sp) ra' n' ⋆
          F ⋆ R))

private theorem fnSpec_bwd_of_twin {A : Arch} (hwf : A.Wf) (P : VllPolicy A)
    {cs : List (Chunk A)} {pc : Bool} (hv : ChunksValid A pc cs)
    {h₂ : VllHost A} (hp₂ : h₂.prog = chunksRhs cs)
    (hu₂ : (vllTarget A hwf P).LabelsUnique h₂)
    {avoid : List (BitVec 64)} (T : TwinHosts A cs h₂ avoid)
    {sym : Sym} {as bs : List Ty} {spec : Spec as bs} {n nX : Nat}
    (hfn : (vllTarget A hwf P).FnSpec h₂ sym spec n nX) :
    (vllTarget A hwf P).FnSpec T.h₁ sym spec n nX := by
  intro args m Q X hspec s ra R hargs hra hsp hm
  have hev2 := hfn args m Q X hspec s ra R hargs hra hsp hm
  have hev1 := chunks_bwd_sim hwf hv hp₂ hu₂ T hev2
  change Eventually (vllStep T.h₁) _ ⟨s, T.h₁.labelAddr sym⟩
  rw [T.lab₁]
  refine eventually_weaken (vllStep T.h₁) _ _ _ ?_ hev1
  intro st hst
  rcases hst with hret | ⟨sym', cs', xs, m', hX, hdef, hpc, hax, hsx, hrest⟩
  · exact Or.inl hret
  · refine Or.inr ⟨sym', cs', xs, m', hX,
      (chunks_defined_iff hwf P hv T.prog₁ hp₂ sym').mpr hdef,
      (by show st.pc = T.h₁.labelAddr sym'; rw [T.lab₁]; exact hpc), hax, hsx, hrest⟩

private theorem chunks_post_weaken {A : Arch} (hwf : A.Wf) (P : VllPolicy A)
    {cs : List (Chunk A)} {pc : Bool} (hv : ChunksValid A pc cs)
    {h₁ h₂ : VllHost A} (hp₁ : h₁.prog = chunksLhs cs) (hp₂ : h₂.prog = chunksRhs cs)
    (hlab : h₁.labelAddr = h₂.labelAddr)
    {bs : List Ty} {s : MachSt A} {ra : BitVec 64} {n nX : Nat}
    {Q : Post bs} {X : XPost} {R : Mem 64 → Prop} {st : Config A}
    (h : vllFnPost hwf P h₁ s ra n nX Q X R st) :
    vllFnPost hwf P h₂ s ra n nX Q X R st := by
  rcases h with h1 | ⟨sym', cs', xs, m', hX, hdef, hpc, hrest⟩
  · exact Or.inl h1
  · exact Or.inr ⟨sym', cs', xs, m', hX,
      (chunks_defined_iff hwf P hv hp₁ hp₂ sym').mp hdef, hlab ▸ hpc, hrest⟩

private theorem chunks_noDrop_fnPost {A : Arch} (hwf : A.Wf) (P : VllPolicy A)
    {cs : List (Chunk A)} {h₂ : VllHost A}
    (hu₂ : (vllTarget A hwf P).LabelsUnique h₂)
    {sym : Sym} {bs : List Ty} {s : MachSt A} {ra : BitVec 64} {n nX : Nat}
    {Q : Post bs} {X : XPost} {R : Mem 64 → Prop}
    (TW : TwinHosts A cs h₂ [ra, h₂.labelAddr sym]) :
    ∀ k < (chunksLhs cs).length, chunksMap cs k = none → ∀ s',
      ¬vllFnPost hwf P h₂ s ra n nX Q X R ⟨s', TW.h₁.addrOf k⟩ ∧
      ¬vllFnPost hwf P h₂ s ra n nX Q X R ⟨s', TW.h₁'.addrOf k⟩ := by
  intro k hk hmk s'
  have hdisj := TW.drop_avoid k hk hmk ra List.mem_cons_self
  constructor
  · rintro (⟨hpc, _⟩ | ⟨sym', _, _, _, _, ⟨j, hj⟩, hpc, _⟩)
    · exact hdisj.1 hpc
    · have hjlt : j < h₂.prog.length := getElem?_some_lt hj
      have hfirst : ∀ j' < j, h₂.prog[j']? ≠ some (.label sym') := fun j' hj' heq => by
        have := hu₂ j' j sym' heq hj; omega
      rw [h₂.labelAddr_wf hj hfirst] at hpc
      exact (TW.drop_disj_h₂ k hk hmk j (by omega)).1 hpc
  · rintro (⟨hpc, _⟩ | ⟨sym', _, _, _, _, ⟨j, hj⟩, hpc, _⟩)
    · exact hdisj.2 hpc
    · have hjlt : j < h₂.prog.length := getElem?_some_lt hj
      have hfirst : ∀ j' < j, h₂.prog[j']? ≠ some (.label sym') := fun j' hj' heq => by
        have := hu₂ j' j sym' heq hj; omega
      rw [h₂.labelAddr_wf hj hfirst] at hpc
      exact (TW.drop_disj_h₂ k hk hmk j (by omega)).2 hpc

private theorem chunks_fnSpec_transfer {A : Arch} (hwf : A.Wf) (P : VllPolicy A)
    {cs : List (Chunk A)} {pc : Bool} (hv : ChunksValid A pc cs)
    {h₂ : VllHost A} (hp₂ : h₂.prog = chunksRhs cs)
    (hu₂ : (vllTarget A hwf P).LabelsUnique h₂)
    (hsize : h₂.prog.length + 3 + 2 * (chunksLhs cs).length ≤ 2 ^ 64)
    {sym : Sym} {as bs : List Ty} {spec : Spec as bs} {n nX : Nat}
    {callees : List (Sym × List Ty × List Ty)} {exits : List Sym}
    {Γ : Env} {bound : Sym → Nat}
    (hcal₂ : ∀ g as' bs', (g, as', bs') ∈ callees →
      (vllTarget A hwf P).FnSpec h₂ g (Γ g as' bs') (bound g) nX)
    (hex₂ : ∀ g, g ∈ exits → (vllTarget A hwf P).Defined h₂ g)
    (hspec₁ : ∀ (h₁ : VllHost A), h₁.prog = chunksLhs cs →
      (vllTarget A hwf P).LabelsUnique h₁ →
      (∀ g as' bs', (g, as', bs') ∈ callees →
        (vllTarget A hwf P).FnSpec h₁ g (Γ g as' bs') (bound g) nX) →
      (∀ g, g ∈ exits → (vllTarget A hwf P).Defined h₁ g) →
      (vllTarget A hwf P).FnSpec h₁ sym spec n nX) :
    (vllTarget A hwf P).FnSpec h₂ sym spec n nX := by
  intro args m Q X hspec s ra R hargs hra hsp hm
  obtain ⟨TW⟩ := mkTwinHosts hv hp₂ [ra, h₂.labelAddr sym] (by simp; omega)
  have hu₁ : (vllTarget A hwf P).LabelsUnique TW.h₁ := fun i j l hi hj =>
    chunks_labelsUnique_lhs hv hp₂ hu₂ i j l (TW.prog₁ ▸ hi) (TW.prog₁ ▸ hj)
  have hu₁' : (vllTarget A hwf P).LabelsUnique TW.h₁' := fun i j l hi hj =>
    chunks_labelsUnique_lhs hv hp₂ hu₂ i j l (TW.prog₁' ▸ hi) (TW.prog₁' ▸ hj)
  have hcal₁ := fun g as' bs' hg => fnSpec_bwd_of_twin hwf P hv hp₂ hu₂ TW (hcal₂ g as' bs' hg)
  have hcal₁' := fun g as' bs' hg =>
    fnSpec_bwd_of_twin hwf P hv hp₂ hu₂ TW.swap (hcal₂ g as' bs' hg)
  have hex₁ := fun g hg => (chunks_defined_iff hwf P hv TW.prog₁ hp₂ g).mpr (hex₂ g hg)
  have hex₁' := fun g hg => (chunks_defined_iff hwf P hv TW.prog₁' hp₂ g).mpr (hex₂ g hg)
  have he₁ := hspec₁ TW.h₁ TW.prog₁ hu₁ hcal₁ hex₁ args m Q X hspec s ra R hargs hra hsp hm
  have he₁' := hspec₁ TW.h₁' TW.prog₁' hu₁' hcal₁' hex₁' args m Q X hspec s ra R hargs hra hsp hm
  have he₁w : Eventually (vllStep TW.h₁) (vllFnPost hwf P h₂ s ra n nX Q X R)
      ⟨s, TW.h₁.labelAddr sym⟩ :=
    eventually_weaken (vllStep TW.h₁) _ _ _
      (fun _ => chunks_post_weaken hwf P hv TW.prog₁ hp₂ TW.lab₁) he₁
  have he₁'w : Eventually (vllStep TW.h₁') (vllFnPost hwf P h₂ s ra n nX Q X R)
      ⟨s, TW.h₁'.labelAddr sym⟩ :=
    eventually_weaken (vllStep TW.h₁') _ _ _
      (fun _ => chunks_post_weaken hwf P hv TW.prog₁' hp₂ TW.lab₁') he₁'
  rw [TW.lab₁] at he₁w; rw [TW.lab₁'] at he₁'w
  have hnotEntry : ∀ k < (chunksLhs cs).length, chunksMap cs k = none →
      h₂.labelAddr sym ≠ TW.h₁.addrOf k := fun k hk hmk heq =>
    (TW.drop_avoid k hk hmk (h₂.labelAddr sym)
      (List.mem_cons_of_mem _ List.mem_cons_self)).1 heq.symm
  exact (chunks_twinHost_sim hwf hv hp₂ hu₂ TW
    (chunks_noDrop_fnPost hwf P hu₂ TW) he₁w).1 hnotEntry he₁'w

/-! ### Chunk Witnesses for `elimFilter`, `elimWindow`, `invertJccJmp`, `elimFallthrough` -/

private theorem chunksValid_append {A : Arch} :
    ∀ {cs₁ cs₂ : List (Chunk A)} {pc : Bool},
      ChunksValid A pc cs₁ →
      ChunksValid A (match cs₁.getLast? with | some c => c.endCall | none => pc) cs₂ →
      ChunksValid A pc (cs₁ ++ cs₂)
  | [], _, _, _, h2 => h2
  | [c], _, _, ⟨hv, hk, _⟩, h2 => ⟨hv, hk, by simpa using h2⟩
  | c :: c' :: rest, cs₂, _, ⟨hv, hk, hrest⟩, h2 => by
    refine ⟨hv, hk, chunksValid_append hrest ?_⟩
    simpa [List.getLast?] using h2

private theorem chunksValid_map_same {A : Arch} :
    ∀ (is : List (Instr A)) (pc : Bool), ChunksValid A pc (is.map Chunk.same)
  | [], _ => trivial
  | i :: rest, _ => ⟨trivial, fun _ => rfl, chunksValid_map_same rest i.isCall⟩

private theorem chunksLhs_map_same {A : Arch} :
    ∀ (is : List (Instr A)), chunksLhs (is.map Chunk.same) = is
  | [] => rfl
  | i :: rest => by rw [List.map_cons, chunksLhs_cons, chunksLhs_map_same rest]; rfl

private theorem chunksRhs_map_same {A : Arch} :
    ∀ (is : List (Instr A)), chunksRhs (is.map Chunk.same) = is
  | [] => rfl
  | i :: rest => by rw [List.map_cons, chunksRhs_cons, chunksRhs_map_same rest]; rfl

private theorem chunks_wrap_infix {A : Arch} {pre code code' suf : List (Instr A)}
    {cs : List (Chunk A)} (hv : ChunksValid A true cs)
    (hl : chunksLhs cs = code) (hr : chunksRhs cs = code') :
    ∃ csAll : List (Chunk A), ChunksValid A false csAll ∧
      chunksLhs csAll = pre ++ code ++ suf ∧ chunksRhs csAll = pre ++ code' ++ suf ∧
      ∀ k < code.length,
        chunksMap csAll (pre.length + k) = (chunksMap cs k).map (pre.length + ·) := by
  have hv_any : ∀ pc, ChunksValid A pc cs := by
    intro pc
    cases pc
    · revert hv; cases cs with
      | nil => intro _; trivial
      | cons c rest => intro hv; exact ⟨hv.1, (fun h => by cases h), hv.2.2⟩
    · exact hv
  have h1 : ChunksValid A false (pre.map Chunk.same ++ cs) :=
    chunksValid_append (chunksValid_map_same pre false) (hv_any _)
  have h2 : ChunksValid A false ((pre.map Chunk.same ++ cs) ++ suf.map Chunk.same) :=
    chunksValid_append h1 (chunksValid_map_same suf _)
  refine ⟨(pre.map Chunk.same ++ cs) ++ suf.map Chunk.same, h2, ?_, ?_, ?_⟩
  · rw [chunksLhs_append, chunksLhs_append, chunksLhs_map_same, chunksLhs_map_same, hl]
  · rw [chunksRhs_append, chunksRhs_append, chunksRhs_map_same, chunksRhs_map_same, hr]
  · intro k hk
    have hlt : pre.length + k < (chunksLhs (pre.map Chunk.same ++ cs)).length := by
      rw [chunksLhs_append, chunksLhs_map_same, hl, List.length_append]; omega
    rw [chunksMap_append_left hlt, chunksMap_map_same_append]

private theorem chunks_infix_run_transfer {A : Arch} (hwf : A.Wf) (P : VllPolicy A)
    {pre code code' suf : List (Instr A)} {cs : List (Chunk A)}
    (hv : ChunksValid A true cs) (hl : chunksLhs cs = code) (hr : chunksRhs cs = code')
    {h₂ : VllHost A} (hp₂ : h₂.prog = pre ++ code' ++ suf)
    (hu₂ : (vllTarget A hwf P).LabelsUnique h₂)
    (hsize : (pre ++ code' ++ suf).length + 3 + 2 * (pre ++ code ++ suf).length ≤ 2 ^ 64)
    {sym : Sym} {bs : List Ty} {s : MachSt A} {ra : BitVec 64} {n nX : Nat}
    {Q : Post bs} {X : XPost} {R : Mem 64 → Prop}
    {callees : List (Sym × List Ty × List Ty)} {exits : List Sym}
    {Γ : Env} {bound : Sym → Nat}
    (hra₂ : ∀ k < code'.length, h₂.addrOf (pre.length + k) ≠ ra)
    (hcal₂ : ∀ g as' bs', (g, as', bs') ∈ callees →
      (vllTarget A hwf P).FnSpec h₂ g (Γ g as' bs') (bound g) nX)
    (hex₂ : ∀ g, g ∈ exits → (vllTarget A hwf P).Defined h₂ g)
    (hrun₁ : ∀ (h₁ : VllHost A), h₁.prog = pre ++ code ++ suf →
      (vllTarget A hwf P).LabelsUnique h₁ →
      (∀ k < code.length, h₁.addrOf (pre.length + k) ≠ ra) →
      (∀ g as' bs', (g, as', bs') ∈ callees →
        (vllTarget A hwf P).FnSpec h₁ g (Γ g as' bs') (bound g) nX) →
      (∀ g, g ∈ exits → (vllTarget A hwf P).Defined h₁ g) →
      Eventually (vllStep h₁) (vllFnPost hwf P h₁ s ra n nX Q X R) ⟨s, h₁.labelAddr sym⟩) :
    Eventually (vllStep h₂) (vllFnPost hwf P h₂ s ra n nX Q X R) ⟨s, h₂.labelAddr sym⟩ := by
  obtain ⟨csAll, hvA, hlA, hrA, hmapA⟩ := chunks_wrap_infix (pre := pre) (suf := suf) hv hl hr
  have hp₂' : h₂.prog = chunksRhs csAll := hp₂.trans hrA.symm
  obtain ⟨TW⟩ := mkTwinHosts hvA hp₂' [ra, h₂.labelAddr sym] (by
    rw [hp₂, hlA]; simp only [List.length_cons, List.length_nil]; omega)
  have hu₁ : (vllTarget A hwf P).LabelsUnique TW.h₁ := fun i j l hi hj =>
    chunks_labelsUnique_lhs hvA hp₂' hu₂ i j l (TW.prog₁ ▸ hi) (TW.prog₁ ▸ hj)
  have hu₁' : (vllTarget A hwf P).LabelsUnique TW.h₁' := fun i j l hi hj =>
    chunks_labelsUnique_lhs hvA hp₂' hu₂ i j l (TW.prog₁' ▸ hi) (TW.prog₁' ▸ hj)
  have hcal₁ := fun g as' bs' hg => fnSpec_bwd_of_twin hwf P hvA hp₂' hu₂ TW (hcal₂ g as' bs' hg)
  have hcal₁' := fun g as' bs' hg =>
    fnSpec_bwd_of_twin hwf P hvA hp₂' hu₂ TW.swap (hcal₂ g as' bs' hg)
  have hex₁ := fun g hg => (chunks_defined_iff hwf P hvA TW.prog₁ hp₂' g).mpr (hex₂ g hg)
  have hex₁' := fun g hg => (chunks_defined_iff hwf P hvA TW.prog₁' hp₂' g).mpr (hex₂ g hg)
  have hra_both : (∀ k < code.length, TW.h₁.addrOf (pre.length + k) ≠ ra) ∧
      (∀ k < code.length, TW.h₁'.addrOf (pre.length + k) ≠ ra) := by
    have aux : ∀ k < code.length,
        TW.h₁.addrOf (pre.length + k) ≠ ra ∧ TW.h₁'.addrOf (pre.length + k) ≠ ra := by
      intro k hk
      have hmk := hmapA k hk
      cases hm : chunksMap cs k with
      | none =>
        rw [hm] at hmk
        exact TW.drop_avoid (pre.length + k) (by rw [hlA]; simp; omega) hmk ra List.mem_cons_self
      | some j =>
        rw [hm] at hmk
        have hjlt : j < code'.length := hr ▸ chunksMap_lt (hl.symm ▸ hk) hm
        rw [TW.kept₁ _ _ hmk, TW.kept₁' _ _ hmk]
        exact ⟨hra₂ j hjlt, hra₂ j hjlt⟩
    exact ⟨fun k hk => (aux k hk).1, fun k hk => (aux k hk).2⟩
  have he₁ := hrun₁ TW.h₁ (TW.prog₁.trans hlA) hu₁ hra_both.1 hcal₁ hex₁
  have he₁' := hrun₁ TW.h₁' (TW.prog₁'.trans hlA) hu₁' hra_both.2 hcal₁' hex₁'
  have he₁w := eventually_weaken (vllStep TW.h₁) _ _ _
    (fun _ => chunks_post_weaken hwf P hvA TW.prog₁ hp₂' TW.lab₁) he₁
  have he₁'w := eventually_weaken (vllStep TW.h₁') _ _ _
    (fun _ => chunks_post_weaken hwf P hvA TW.prog₁' hp₂' TW.lab₁') he₁'
  rw [TW.lab₁] at he₁w; rw [TW.lab₁'] at he₁'w
  have hnotEntry : ∀ k < (chunksLhs csAll).length, chunksMap csAll k = none →
      h₂.labelAddr sym ≠ TW.h₁.addrOf k := fun k hk hmk heq =>
    (TW.drop_avoid k hk hmk (h₂.labelAddr sym)
      (List.mem_cons_of_mem _ List.mem_cons_self)).1 heq.symm
  exact (chunks_twinHost_sim hwf hvA hp₂' hu₂ TW
    (chunks_noDrop_fnPost hwf P hu₂ TW) he₁w).1 hnotEntry he₁'w

private theorem elimFilterAux_chunks {A : Arch} {p : Instr A → Bool}
    (hp : ∀ i, p i = true → (∀ l, i ≠ .label l) ∧ i.isCall = false ∧
      ∀ symAddr np s o, instrRel A symAddr np i s o ↔ o = .fall s)
    (ac : Bool) (is : List (Instr A)) :
    ∃ cs : List (Chunk A), ChunksValid A ac cs ∧
      chunksLhs cs = is ∧ chunksRhs cs = elimFilterAux p ac is := by
  fun_induction elimFilterAux p ac is with
  | case1 _ => exact ⟨[], trivial, rfl, rfl⟩
  | case2 ac i rest hcond ih =>
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
    obtain ⟨cs, hv, hl, hr⟩ := ih
    refine ⟨.dropNoop i :: cs, ⟨hp i hcond.2, (fun h => by rw [hcond.1] at h; cases h), hv⟩,
      by rw [chunksLhs_cons, Chunk.lhs, hl]; rfl, by rw [chunksRhs_cons, Chunk.rhs, hr]; rfl⟩
  | case3 ac i rest _ ih =>
    obtain ⟨cs, hv, hl, hr⟩ := ih
    refine ⟨.same i :: cs, ⟨trivial, fun _ => rfl, hv⟩,
      by rw [chunksLhs_cons, Chunk.lhs, hl]; rfl, by rw [chunksRhs_cons, Chunk.rhs, hr]; rfl⟩

private theorem elimFilter_chunks_of_label_head {A : Arch} {p : Instr A → Bool}
    (hp : ∀ i, p i = true → (∀ l, i ≠ .label l) ∧ i.isCall = false ∧
      ∀ symAddr np s o, instrRel A symAddr np i s o ↔ o = .fall s)
    {l : Sym} (rest : List (Instr A)) :
    ∃ cs : List (Chunk A), ChunksValid A true cs ∧
      chunksLhs cs = .label l :: rest ∧ chunksRhs cs = elimFilter p (.label l :: rest) := by
  have hpl : p (.label l) = false := by
    cases h : p (.label l) with
    | false => rfl
    | true => exact absurd rfl ((hp (.label l) h).1 l)
  obtain ⟨cs, hv, hl, hr⟩ := elimFilterAux_chunks hp false rest
  refine ⟨.same (.label l) :: cs, ⟨trivial, fun _ => rfl, hv⟩,
    by rw [chunksLhs_cons, Chunk.lhs, hl]; rfl,
    by rw [chunksRhs_cons, Chunk.rhs, hr]; simp [elimFilter, elimFilterAux, hpl, Instr.isCall]⟩

private theorem elimWindow_chunks {A : Arch} {rule : Instr A → Instr A → Option (Instr A)}
    (hr : ∀ i₁ i₂ i', rule i₁ i₂ = some i' →
      ((∀ l, i₁ ≠ .label l) ∧ (∀ l, i₂ ≠ .label l) ∧ (∀ l, i' ≠ .label l)) ∧
      (i₁.isCall = false ∧ i₂.isCall = false ∧ i'.isCall = false) ∧
      ∀ symAddr, DetFallPair A symAddr i₁ i₂ i')
    (is : List (Instr A)) :
    ∀ pc, ∃ cs : List (Chunk A), ChunksValid A pc cs ∧
      chunksLhs cs = is ∧ chunksRhs cs = elimWindow rule is := by
  fun_induction elimWindow rule is with
  | case1 => intro _; exact ⟨[], trivial, rfl, rfl⟩
  | case2 i => intro _; exact ⟨[.same i], ⟨trivial, fun _ => rfl, trivial⟩, rfl, rfl⟩
  | case3 i₁ i₂ rest i' hrule ih =>
    intro _
    obtain ⟨cs, hv, hl, hrh⟩ := ih false
    refine ⟨.pairDet i₁ i₂ i' :: cs, ⟨hr i₁ i₂ i' hrule, fun _ => rfl, hv⟩,
      by rw [chunksLhs_cons, Chunk.lhs, hl]; rfl, by rw [chunksRhs_cons, Chunk.rhs, hrh]; rfl⟩
  | case4 i₁ i₂ rest _ ih =>
    intro _
    obtain ⟨cs, hv, hl, hrh⟩ := ih i₁.isCall
    refine ⟨.same i₁ :: cs, ⟨trivial, fun _ => rfl, hv⟩,
      by rw [chunksLhs_cons, Chunk.lhs, hl]; rfl, by rw [chunksRhs_cons, Chunk.rhs, hrh]; rfl⟩

private theorem invertJccJmp_chunks_wf (A : Arch) (is : List (Instr A)) :
    ∀ pc, ∃ cs : List (Chunk A), ChunksValid A pc cs ∧
      chunksLhs cs = is ∧ chunksRhs cs = invertJccJmp A is := by
  suffices ∀ n (is : List (Instr A)) (pc : Bool), is.length ≤ n →
      ∃ cs : List (Chunk A), ChunksValid A pc cs ∧
        chunksLhs cs = is ∧ chunksRhs cs = invertJccJmp A is from
    fun pc => this is.length is pc (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro is _ hlen
    cases is with | nil => exact ⟨[], trivial, rfl, rfl⟩ | cons _ _ => simp at hlen
  | succ n ih =>
    intro is pc hlen
    cases is with
    | nil => exact ⟨[], trivial, rfl, rfl⟩
    | cons i rest =>
      cases h1 : i with
      | jcc c l₁ =>
        cases rest with
        | nil => exact ⟨[.same (.jcc c l₁)], ⟨trivial, fun _ => rfl, trivial⟩, rfl, rfl⟩
        | cons x rest1 =>
          cases h2 : x with
          | jmp l₂ =>
            cases rest1 with
            | nil =>
              exact ⟨[.same (.jcc c l₁), .same (.jmp l₂)],
                ⟨trivial, fun _ => rfl, trivial, fun _ => rfl, trivial⟩, rfl, rfl⟩
            | cons y rest2 =>
              cases h3 : y with
              | label l₃ =>
                dsimp only [invertJccJmp]
                by_cases heq : (l₁ == l₃) = true
                · simp only [heq, ↓reduceIte]
                  have hll : l₁ = l₃ := beq_iff_eq.mp heq; subst hll
                  obtain ⟨cs, hv, hl, hr⟩ := ih rest2 false (by simp at hlen; omega)
                  refine ⟨.invertJcc c l₁ l₂ :: cs, ⟨trivial, fun _ => rfl, hv⟩,
                    by rw [chunksLhs_cons, Chunk.lhs, hl]; rfl,
                    by rw [chunksRhs_cons, Chunk.rhs, hr]; rfl⟩
                · simp only [heq]
                  obtain ⟨cs, hv, hl, hr⟩ :=
                    ih (.jmp l₂ :: .label l₃ :: rest2) false (by simp at hlen; omega)
                  refine ⟨.same (.jcc c l₁) :: cs, ⟨trivial, fun _ => rfl, hv⟩,
                    by rw [chunksLhs_cons, Chunk.lhs, hl]; rfl,
                    by rw [chunksRhs_cons, Chunk.rhs, hr]; rfl⟩
              | _ =>
                obtain ⟨cs, hv, hl, hr⟩ := ih (.jmp l₂ :: y :: rest2) false (by simp at hlen; omega)
                refine ⟨.same (.jcc c l₁) :: cs, ⟨trivial, fun _ => rfl, hv⟩,
                  by rw [chunksLhs_cons, Chunk.lhs, hl, h3]; rfl,
                  by rw [chunksRhs_cons, Chunk.rhs, hr, h3]; rfl⟩
          | _ =>
            obtain ⟨cs, hv, hl, hr⟩ := ih (x :: rest1) false (by simp at hlen; omega)
            refine ⟨.same (.jcc c l₁) :: cs, ⟨trivial, fun _ => rfl, hv⟩,
              by rw [chunksLhs_cons, Chunk.lhs, hl, h2]; rfl,
              by rw [chunksRhs_cons, Chunk.rhs, hr, h2]; rfl⟩
      | _ =>
        obtain ⟨cs, hv, hl, hr⟩ := ih rest i.isCall (by simp at hlen; omega)
        refine ⟨.same i :: cs, ⟨trivial, fun _ => rfl, hv⟩,
          by rw [chunksLhs_cons, Chunk.lhs, hl, h1]; rfl,
          by rw [chunksRhs_cons, Chunk.rhs, hr, h1]; rfl⟩

private theorem elimFallthroughAux_chunks (A : Arch) (inc ac : Bool) (is : List (Instr A)) :
    ∃ cs : List (Chunk A), ChunksValid A ac cs ∧
      chunksLhs cs = is ∧ chunksRhs cs = elimFallthroughAux A inc ac is := by
  suffices ∀ n (ac : Bool) (is : List (Instr A)), is.length ≤ n →
      ∃ cs : List (Chunk A), ChunksValid A ac cs ∧
        chunksLhs cs = is ∧ chunksRhs cs = elimFallthroughAux A inc ac is from
    this is.length ac is (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro ac is hlen
    cases is with | nil => exact ⟨[], trivial, rfl, rfl⟩ | cons _ _ => simp at hlen
  | succ n ih =>
    intro ac is hlen
    cases is with
    | nil => exact ⟨[], trivial, rfl, rfl⟩
    | cons i rest =>
      cases h1 : i with
      | jmp l₁ =>
        cases rest with
        | nil => exact ⟨[.same (.jmp l₁)], ⟨trivial, fun _ => rfl, trivial⟩, rfl, rfl⟩
        | cons nxt rest' =>
          cases h2 : nxt with
          | label l₂ =>
            dsimp only [elimFallthroughAux]
            by_cases hcond : (!ac && l₁ == l₂) = true
            · simp only [hcond, ↓reduceIte]
              simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hcond
              rcases hcond with ⟨rfl, rfl⟩
              obtain ⟨cs, hv, hl, hr⟩ := ih false rest' (by simp at hlen; omega)
              refine ⟨.dropFallJmp l₁ :: cs, ⟨trivial, (fun h => by cases h), hv⟩,
                by rw [chunksLhs_cons, Chunk.lhs, hl]; rfl,
                by rw [chunksRhs_cons, Chunk.rhs, hr]; rfl⟩
            · simp only [hcond]
              obtain ⟨cs, hv, hl, hr⟩ := ih false (.label l₂ :: rest') (by simp at hlen; omega)
              refine ⟨.same (.jmp l₁) :: cs, ⟨trivial, fun _ => rfl, hv⟩,
                by rw [chunksLhs_cons, Chunk.lhs, hl]; rfl,
                by rw [chunksRhs_cons, Chunk.rhs, hr]; rfl⟩
          | _ =>
            obtain ⟨cs, hv, hl, hr⟩ := ih false (nxt :: rest') (by simp at hlen; omega)
            refine ⟨.same (.jmp l₁) :: cs, ⟨trivial, fun _ => rfl, hv⟩,
              by rw [chunksLhs_cons, Chunk.lhs, hl, h2]; rfl,
              by rw [chunksRhs_cons, Chunk.rhs, hr, h2]; rfl⟩
      | jcc c l₁ =>
        cases rest with
        | nil => exact ⟨[.same (.jcc c l₁)], ⟨trivial, fun _ => rfl, trivial⟩, rfl, rfl⟩
        | cons nxt rest' =>
          cases h2 : nxt with
          | label l₂ =>
            dsimp only [elimFallthroughAux]
            by_cases hcond : (inc && !ac && l₁ == l₂) = true
            · simp only [hcond, ↓reduceIte]
              simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hcond
              rcases hcond with ⟨⟨_, rfl⟩, rfl⟩
              obtain ⟨cs, hv, hl, hr⟩ := ih false rest' (by simp at hlen; omega)
              refine ⟨.dropFallJcc c l₁ :: cs, ⟨trivial, (fun h => by cases h), hv⟩,
                by rw [chunksLhs_cons, Chunk.lhs, hl]; rfl,
                by rw [chunksRhs_cons, Chunk.rhs, hr]; rfl⟩
            · simp only [hcond]
              obtain ⟨cs, hv, hl, hr⟩ := ih false (.label l₂ :: rest') (by simp at hlen; omega)
              refine ⟨.same (.jcc c l₁) :: cs, ⟨trivial, fun _ => rfl, hv⟩,
                by rw [chunksLhs_cons, Chunk.lhs, hl]; rfl,
                by rw [chunksRhs_cons, Chunk.rhs, hr]; rfl⟩
          | _ =>
            obtain ⟨cs, hv, hl, hr⟩ := ih false (nxt :: rest') (by simp at hlen; omega)
            refine ⟨.same (.jcc c l₁) :: cs, ⟨trivial, fun _ => rfl, hv⟩,
              by rw [chunksLhs_cons, Chunk.lhs, hl, h2]; rfl,
              by rw [chunksRhs_cons, Chunk.rhs, hr, h2]; rfl⟩
      | _ =>
        obtain ⟨cs, hv, hl, hr⟩ := ih i.isCall rest (by simp at hlen; omega)
        refine ⟨.same i :: cs, ⟨trivial, fun _ => rfl, hv⟩,
          by rw [chunksLhs_cons, Chunk.lhs, hl, h1]; rfl,
          by rw [chunksRhs_cons, Chunk.rhs, hr, h1]; rfl⟩

private theorem elimFallthrough_chunks_of_label_head (A : Arch) (inc : Bool)
    {l : Sym} (rest : List (Instr A)) :
    ∃ cs : List (Chunk A), ChunksValid A true cs ∧
      chunksLhs cs = .label l :: rest ∧
      chunksRhs cs = elimFallthroughAux A inc false (.label l :: rest) := by
  obtain ⟨cs, hv, hl, hr⟩ := elimFallthroughAux_chunks A inc false rest
  refine ⟨.same (.label l) :: cs, ⟨trivial, fun _ => rfl, hv⟩,
    by rw [chunksLhs_cons, Chunk.lhs, hl]; rfl,
    by rw [chunksRhs_cons, Chunk.rhs, hr]; rfl⟩

/-! ## 5. Top-Level `FnSpec` & `vllLowerFn` Soundness Theorems -/

private theorem pass_head_label {A : Arch} {l : Sym} (rest : List (Instr A)) :
    (∃ r1, elimNoop A (.label l :: rest) = .label l :: r1) ∧
    (∃ r1, elimSelfMov A (.label l :: rest) = .label l :: r1) ∧
    (∃ r1, elimRedundantWindow A (.label l :: rest) = .label l :: r1) ∧
    (∃ r1, elimRedundantWindowCore A (.label l :: rest) = .label l :: r1) ∧
    (∃ r1, threadJmp A (.label l :: rest) = .label l :: r1) ∧
    (∃ r1, invertJccJmp A (.label l :: rest) = .label l :: r1) ∧
    (∃ r1, elimFallthrough A (.label l :: rest) = .label l :: r1) := by
  refine ⟨⟨_, by dsimp [elimNoop, elimFilter, elimFilterAux, Instr.isNoop, Instr.isSelfMov64,
      Instr.isZeroFrameNoop, Instr.isCanonAbi64Noop]⟩,
    ⟨_, by dsimp [elimSelfMov, elimFilter, elimFilterAux, Instr.isSelfMov64]⟩, ?_, ?_,
    ⟨_, by dsimp [threadJmp, threadInstr]; rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩⟩
  · cases rest with
    | nil => exact ⟨[], rfl⟩
    | cons x xs => exact ⟨_, by dsimp [elimRedundantWindow, elimWindow, peepholePair?,
        peepholePairCore?, Instr.pureGprWriteDst?]⟩
  · cases rest with
    | nil => exact ⟨[], rfl⟩
    | cons x xs => exact ⟨_, by dsimp [elimRedundantWindowCore, elimWindow,
        peepholePairCore?, Instr.pureGprWriteDst?]⟩

private theorem vllLowerFn_head_label {A : Arch} {P : VllPolicy A} {hints : (vllIsa A P).Hints}
    {E : Rega.Ext} {f : Fn} {code : List (Instr A)}
    (hl : vllLowerFn A P hints E f = .ok code) :
    ∃ rest, code = .label f.name :: rest := by
  simp only [vllLowerFn, Rega.lowerFn] at hl
  repeat (split at hl <;> try cases hl)
  exact ⟨_, rfl⟩

private theorem chunk_step_fnSpec {A : Arch} (hwf : A.Wf) (P : VllPolicy A)
    {pre code code' suf : List (Instr A)} {cs : List (Chunk A)}
    (hv : ChunksValid A true cs) (hl : chunksLhs cs = code) (hr : chunksRhs cs = code')
    {sym : Sym} {as bs : List Ty} {spec : Spec as bs} {n nX : Nat}
    {callees : List (Sym × List Ty × List Ty)} {exits : List Sym}
    {Γ : Env} {bound : Sym → Nat}
    (hprev : ∀ (h₁ : VllHost A), h₁.prog = pre ++ code ++ suf →
      (vllTarget A hwf P).LabelsUnique h₁ →
      (∀ g as' bs', (g, as', bs') ∈ callees →
        (vllTarget A hwf P).FnSpec h₁ g (Γ g as' bs') (bound g) nX) →
      (∀ g, g ∈ exits → (vllTarget A hwf P).Defined h₁ g) →
      (vllTarget A hwf P).FnSpec h₁ sym spec n nX)
    (hsize : (pre ++ code' ++ suf).length + 3 + 2 * (pre ++ code ++ suf).length ≤ 2 ^ 64) :
    ∀ (h₂ : VllHost A), h₂.prog = pre ++ code' ++ suf →
      (vllTarget A hwf P).LabelsUnique h₂ →
      (∀ g as' bs', (g, as', bs') ∈ callees →
        (vllTarget A hwf P).FnSpec h₂ g (Γ g as' bs') (bound g) nX) →
      (∀ g, g ∈ exits → (vllTarget A hwf P).Defined h₂ g) →
      (vllTarget A hwf P).FnSpec h₂ sym spec n nX := by
  intro h₂ hp₂ hu₂ hcal₂ hex₂
  obtain ⟨csAll, hvA, hlA, hrA, _⟩ := chunks_wrap_infix (pre := pre) (suf := suf) hv hl hr
  refine chunks_fnSpec_transfer hwf P hvA (hp₂.trans hrA.symm) hu₂ ?_ hcal₂ hex₂
    (fun h₁ hp₁ => hprev h₁ (hp₁.trans hlA))
  rw [hp₂, hlA]; exact hsize

private theorem vllLowerFn_base_spec {A : Arch} (hwf : A.Wf) (P : VllPolicy A)
    {hints : (vllIsa A P).Hints} {E : Rega.Ext} {f : Fn}
    {Γ : Env} {n nX : Nat} {bound : Sym → Nat}
    {pre code suf : List (Instr A)}
    (hf : f.Wf) (hl : vllLowerFn A P hints E f = .ok code)
    (hfr : Rega.effFrame (vllIsa A P) hints E ≤ n) (hn : n + A.abi.raBytes ≤ 2 ^ 64)
    (hcalB : ∀ g as bs, (g, as, bs) ∈ E.callees →
      Rega.effFrame (vllIsa A P) hints E + A.abi.raBytes + bound g ≤ n)
    (hexB : ∀ g, g ∈ E.exits → nX ≤ n) :
    ∀ (h0 : VllHost A), h0.prog = pre ++ code ++ suf →
      (vllTarget A hwf P).LabelsUnique h0 →
      (∀ g as bs, (g, as, bs) ∈ E.callees →
        (vllTarget A hwf P).FnSpec h0 g (Γ g as bs) (bound g) nX) →
      (∀ g, g ∈ E.exits → (vllTarget A hwf P).Defined h0 g) →
      (vllTarget A hwf P).FnSpec h0 f.name (Func.spec Γ f.body) n nX := by
  intro h0 hp0 hu0 hcal0 hex0
  have hinf : code.IsInfixAt h0.prog pre.length := by
    rw [hp0]; exact ⟨suf, by simp⟩
  exact vllLowerFn_correct A hwf P h0 hints E f Γ n nX bound hf hl hinf hu0 hfr hn
    (fun g as bs hg => ⟨hcal0 g as bs hg, hcalB g as bs hg⟩)
    (fun g hg => ⟨hex0 g hg, hexB g hg⟩)

/-- End-to-end `Target.FnSpec` soundness for `passPipeWf` (`elimFallthrough ∘ invertJccJmp ∘
elimRedundantWindowCore ∘ elimSelfMov`) under **bare `A.Wf`**, with zero extra flag assumptions
and zero restrictions on caller return addresses. -/
theorem vllLowerFn_passPipeWf_correct (A : Arch) (hwf : A.Wf) (P : VllPolicy A)
    (host : VllHost A) (hints : (vllIsa A P).Hints) (E : Rega.Ext) (f : Fn)
    (Γ : Env) (n nX : Nat) (bound : Sym → Nat)
    {pre code suf : List (Instr A)}
    (hf : f.Wf) (hl : vllLowerFn A P hints E f = .ok code)
    (hprog : host.prog = pre ++ passPipeWf A code ++ suf)
    (hu : (vllTarget A hwf P).LabelsUnique host)
    (hsize : 3 * (pre.length + code.length + suf.length) + 3 ≤ 2 ^ 64)
    (hfr : Rega.effFrame (vllIsa A P) hints E ≤ n)
    (hn : n + A.abi.raBytes ≤ 2 ^ 64)
    (hcal : ∀ g as bs, (g, as, bs) ∈ E.callees →
      (vllTarget A hwf P).FnSpec host g (Γ g as bs) (bound g) nX ∧
      Rega.effFrame (vllIsa A P) hints E + A.abi.raBytes + bound g ≤ n)
    (hex : ∀ g, g ∈ E.exits → (vllTarget A hwf P).Defined host g ∧ nX ≤ n) :
    (vllTarget A hwf P).FnSpec host f.name (Func.spec Γ f.body) n nX := by
  obtain ⟨rest0, hcode0⟩ := vllLowerFn_head_label hl
  let c1 := elimSelfMov A code
  let c2 := elimRedundantWindowCore A c1
  let c3 := invertJccJmp A c2
  obtain ⟨r1, hr1⟩ : ∃ r, c1 = .label f.name :: r := by
    dsimp only [c1]; rw [hcode0]; exact (pass_head_label rest0).2.1
  obtain ⟨r2, hr2⟩ : ∃ r, c2 = .label f.name :: r := by
    dsimp only [c2]; rw [hr1]; exact (pass_head_label r1).2.2.2.1
  obtain ⟨r3, hr3⟩ : ∃ r, c3 = .label f.name :: r := by
    dsimp only [c3]; rw [hr2]; exact (pass_head_label r2).2.2.2.2.2.1
  have hlen1 : c1.length ≤ code.length := elimFilterAux_length_le _ false code
  have hlen2 : c2.length ≤ c1.length := elimWindow_length_le _ c1
  have hlen3 : c3.length ≤ c2.length := invertJccJmp_length_le A c2
  have hlen4 : (passPipeWf A code).length ≤ c3.length :=
    elimFallthroughAux_length_le A true false c3
  have h0 := vllLowerFn_base_spec hwf P (Γ := Γ) (pre := pre) (suf := suf) hf hl hfr hn
    (fun g as bs hg => (hcal g as bs hg).2) (fun g hg => (hex g hg).2)
  obtain ⟨cs1, hv1, hl1, hr1'⟩ := elimFilter_chunks_of_label_head
    (fun i hi => ⟨isSelfMov64_not_label hi,
      by cases i <;> simp [Instr.isSelfMov64, Instr.isCall] at hi ⊢,
      isSelfMov64_rel hwf hi⟩) rest0
  have hcr1 : chunksRhs cs1 = c1 := by dsimp only [c1]; rw [hcode0]; exact hr1'
  have h1 := chunk_step_fnSpec hwf P hv1 (hcode0.symm ▸ hl1) hcr1 h0 (by simp; omega)
  obtain ⟨cs2, hv2, hl2, hr2'⟩ := elimWindow_chunks
    (fun i₁ i₂ i' h => ⟨(peepholePairCore?_no_label_call h).1,
      (peepholePairCore?_no_label_call h).2, fun sa => peepholePairCore?_detFall hwf sa h⟩)
    c1 true
  have hcr2 : chunksRhs cs2 = c2 := hr2'
  have h2 := chunk_step_fnSpec hwf P hv2 hl2 hcr2 h1 (by simp; omega)
  obtain ⟨cs3, hv3, hl3, hr3'⟩ := invertJccJmp_chunks_wf A c2 true
  have hcr3 : chunksRhs cs3 = c3 := hr3'
  have h3 := chunk_step_fnSpec hwf P hv3 hl3 hcr3 h2 (by simp; omega)
  obtain ⟨cs4, hv4, hl4, hr4'⟩ := elimFallthrough_chunks_of_label_head A true r3
  have hcr4 : chunksRhs cs4 = passPipeWf A code := by
    show chunksRhs cs4 = elimFallthrough A c3
    dsimp only [elimFallthrough]; rw [hr3]; exact hr4'
  exact chunk_step_fnSpec hwf P hv4 (hr3.symm ▸ hl4) hcr4 h3 (by simp; omega)
    host hprog hu (fun g as bs hg => (hcal g as bs hg).1) (fun g hg => (hex g hg).1)

/-- End-to-end `Target.FnSpec` soundness for `passPipeCore` (`elimFallthrough ∘ invertJccJmp ∘
elimRedundantWindow ∘ elimNoop`) under `A.PassWf`, with zero restrictions on caller return
addresses. -/
theorem vllLowerFn_passPipeCore_correct (A : Arch) (hwf : A.PassWf) (P : VllPolicy A)
    (host : VllHost A) (hints : (vllIsa A P).Hints) (E : Rega.Ext) (f : Fn)
    (Γ : Env) (n nX : Nat) (bound : Sym → Nat)
    {pre code suf : List (Instr A)}
    (hf : f.Wf) (hl : vllLowerFn A P hints E f = .ok code)
    (hprog : host.prog = pre ++ passPipeCore A code ++ suf)
    (hu : (vllTarget A hwf.toWf P).LabelsUnique host)
    (hsize : 3 * (pre.length + code.length + suf.length) + 3 ≤ 2 ^ 64)
    (hfr : Rega.effFrame (vllIsa A P) hints E ≤ n)
    (hn : n + A.abi.raBytes ≤ 2 ^ 64)
    (hcal : ∀ g as bs, (g, as, bs) ∈ E.callees →
      (vllTarget A hwf.toWf P).FnSpec host g (Γ g as bs) (bound g) nX ∧
      Rega.effFrame (vllIsa A P) hints E + A.abi.raBytes + bound g ≤ n)
    (hex : ∀ g, g ∈ E.exits → (vllTarget A hwf.toWf P).Defined host g ∧ nX ≤ n) :
    (vllTarget A hwf.toWf P).FnSpec host f.name (Func.spec Γ f.body) n nX := by
  obtain ⟨rest0, hcode0⟩ := vllLowerFn_head_label hl
  let c1 := elimNoop A code
  let c2 := elimRedundantWindow A c1
  let c3 := invertJccJmp A c2
  obtain ⟨r1, hr1⟩ : ∃ r, c1 = .label f.name :: r := by
    dsimp only [c1]; rw [hcode0]; exact (pass_head_label rest0).1
  obtain ⟨r2, hr2⟩ : ∃ r, c2 = .label f.name :: r := by
    dsimp only [c2]; rw [hr1]; exact (pass_head_label r1).2.2.1
  obtain ⟨r3, hr3⟩ : ∃ r, c3 = .label f.name :: r := by
    dsimp only [c3]; rw [hr2]; exact (pass_head_label r2).2.2.2.2.2.1
  have hlen1 : c1.length ≤ code.length := elimFilterAux_length_le _ false code
  have hlen2 : c2.length ≤ c1.length := elimWindow_length_le _ c1
  have hlen3 : c3.length ≤ c2.length := invertJccJmp_length_le A c2
  have hlen4 : (passPipeCore A code).length ≤ c3.length :=
    elimFallthroughAux_length_le A true false c3
  have h0 := vllLowerFn_base_spec hwf.toWf P (Γ := Γ) (pre := pre) (suf := suf) hf hl hfr hn
    (fun g as bs hg => (hcal g as bs hg).2) (fun g hg => (hex g hg).2)
  obtain ⟨cs1, hv1, hl1, hr1'⟩ := elimFilter_chunks_of_label_head
    (fun i hi => ⟨isNoop_not_label hi, isNoop_not_call hi, isNoop_rel hwf hi⟩) rest0
  have hcr1 : chunksRhs cs1 = c1 := by dsimp only [c1]; rw [hcode0]; exact hr1'
  have h1 := chunk_step_fnSpec hwf.toWf P hv1 (hcode0.symm ▸ hl1) hcr1 h0 (by simp; omega)
  obtain ⟨cs2, hv2, hl2, hr2'⟩ := elimWindow_chunks
    (fun i₁ i₂ i' h => ⟨(peepholePair?_no_label_call h).1,
      (peepholePair?_no_label_call h).2, fun sa => peepholePair?_detFall hwf sa h⟩)
    c1 true
  have hcr2 : chunksRhs cs2 = c2 := hr2'
  have h2 := chunk_step_fnSpec hwf.toWf P hv2 hl2 hcr2 h1 (by simp; omega)
  obtain ⟨cs3, hv3, hl3, hr3'⟩ := invertJccJmp_chunks_wf A c2 true
  have hcr3 : chunksRhs cs3 = c3 := hr3'
  have h3 := chunk_step_fnSpec hwf.toWf P hv3 hl3 hcr3 h2 (by simp; omega)
  obtain ⟨cs4, hv4, hl4, hr4'⟩ := elimFallthrough_chunks_of_label_head A true r3
  have hcr4 : chunksRhs cs4 = passPipeCore A code := by
    show chunksRhs cs4 = elimFallthrough A c3
    dsimp only [elimFallthrough]; rw [hr3]; exact hr4'
  exact chunk_step_fnSpec hwf.toWf P hv4 (hr3.symm ▸ hl4) hcr4 h3 (by simp; omega)
    host hprog hu (fun g as bs hg => (hcal g as bs hg).1) (fun g hg => (hex g hg).1)

/-- End-to-end semantic soundness for the full five-pass `passPipe` (`elimFallthrough ∘
invertJccJmp ∘ threadJmp ∘ elimRedundantWindow ∘ elimNoop`) connected to `vllLowerFn_correct`,
for every caller return address `ra` outside the optimized function body and every exit
postcondition `X` not targeting bypassed internal trampoline labels. -/
theorem vllLowerFn_passPipe_correct (A : Arch) (hwf : A.PassWf) (P : VllPolicy A)
    (host : VllHost A) (hints : (vllIsa A P).Hints) (E : Rega.Ext) (f : Fn)
    (Γ : Env) (n nX : Nat) (bound : Sym → Nat)
    {pre code suf : List (Instr A)}
    (hf : f.Wf) (hl : vllLowerFn A P hints E f = .ok code)
    (hprog : host.prog = pre ++ passPipe A code ++ suf)
    (hu : (vllTarget A hwf.toWf P).LabelsUnique host)
    (hsize : 3 * (pre.length + code.length + suf.length) + 3 ≤ 2 ^ 64)
    (hfr : Rega.effFrame (vllIsa A P) hints E ≤ n)
    (hn : n + A.abi.raBytes ≤ 2 ^ 64)
    (hcal : ∀ g as bs, (g, as, bs) ∈ E.callees →
      (vllTarget A hwf.toWf P).FnSpec host g (Γ g as bs) (bound g) nX ∧
      Rega.effFrame (vllIsa A P) hints E + A.abi.raBytes + bound g ≤ n)
    (hex : ∀ g, g ∈ E.exits → (vllTarget A hwf.toWf P).Defined host g ∧ nX ≤ n)
    (args : Tup Val f.as) (m : Mem 64) (Q : Post f.rs) (X : XPost)
    (hspec : Func.spec Γ f.body args m Q X)
    (s : MachSt A) (ra : BitVec 64) (R : Mem 64 → Prop)
    (hargs : (vllTarget A hwf.toWf P).ArgsIn args s)
    (hra : (vllFramePreds A).raReg s ra)
    (hsp : A.abi.spEntry (s.gpr A.abi.sp))
    (hm : s.mem =⋆ Eq m ⋆ (vllTarget A hwf.toWf P).Entry (s.gpr A.abi.sp) ra n ⋆ R)
    (hra_ext : ∀ k < (passPipe A code).length, host.addrOf (pre.length + k) ≠ ra)
    (hx_ext : ∀ l ∈ threadedLabels A (elimRedundantWindow A (elimNoop A code)),
      ∀ cs' xs m', ¬X l cs' xs m') :
    Eventually (vllStep host)
      (fun st =>
        (st.pc = ra ∧ ∃ rets m', Q rets m' ∧ (vllTarget A hwf.toWf P).RetsIn rets st.data ∧
          (vllTarget A hwf.toWf P).Restored s st.data ∧
          (st.data.mem =⋆ Eq m' ⋆ (vllTarget A hwf.toWf P).Exit (s.gpr A.abi.sp) n ⋆ R)) ∨
        (∃ sym' cs' xs m', X sym' cs' xs m' ∧ (vllTarget A hwf.toWf P).Defined host sym' ∧
          st.pc = host.labelAddr sym' ∧ (vllTarget A hwf.toWf P).ArgsIn xs st.data ∧
          A.abi.spEntry (st.data.gpr A.abi.sp) ∧
          ∃ ra' n' F, nX ≤ n' ∧ n' + A.abi.raBytes ≤ 2 ^ 64 ∧
            (vllFramePreds A).raReg st.data ra' ∧
            (st.data.mem =⋆ Eq m' ⋆ (vllTarget A hwf.toWf P).Entry (st.data.gpr A.abi.sp) ra' n' ⋆
              F ⋆ R)))
      ⟨s, host.labelAddr f.name⟩ := by
  obtain ⟨rest0, hcode0⟩ := vllLowerFn_head_label hl
  let c1 := elimNoop A code
  let c2 := elimRedundantWindow A c1
  let c2t := threadJmp A c2
  let c3 := invertJccJmp A c2t
  obtain ⟨r1, hr1⟩ : ∃ r, c1 = .label f.name :: r := by
    dsimp only [c1]; rw [hcode0]; exact (pass_head_label rest0).1
  obtain ⟨r2, hr2⟩ : ∃ r, c2 = .label f.name :: r := by
    dsimp only [c2]; rw [hr1]; exact (pass_head_label r1).2.2.1
  obtain ⟨r2t, hr2t⟩ : ∃ r, c2t = .label f.name :: r := by
    dsimp only [c2t]; rw [hr2]; exact (pass_head_label r2).2.2.2.2.1
  obtain ⟨r3, hr3⟩ : ∃ r, c3 = .label f.name :: r := by
    dsimp only [c3]; rw [hr2t]; exact (pass_head_label r2t).2.2.2.2.2.1
  have hlen1 : c1.length ≤ code.length := elimFilterAux_length_le _ false code
  have hlen2 : c2.length ≤ c1.length := elimWindow_length_le _ c1
  have hlen2t : c2t.length = c2.length := threadJmp_length A c2
  have hlen3 : c3.length ≤ c2t.length := invertJccJmp_length_le A c2t
  have hlen4 : (passPipe A code).length ≤ c3.length :=
    elimFallthroughAux_length_le A true false c3
  have h0 := vllLowerFn_base_spec hwf.toWf P (Γ := Γ) (pre := pre) (suf := suf) hf hl hfr hn
    (fun g as bs hg => (hcal g as bs hg).2) (fun g hg => (hex g hg).2)
  obtain ⟨cs1, hv1, hl1, hr1'⟩ := elimFilter_chunks_of_label_head
    (fun i hi => ⟨isNoop_not_label hi, isNoop_not_call hi, isNoop_rel hwf hi⟩) rest0
  have hcr1 : chunksRhs cs1 = c1 := by dsimp only [c1]; rw [hcode0]; exact hr1'
  have h1 := chunk_step_fnSpec hwf.toWf P hv1 (hcode0.symm ▸ hl1) hcr1 h0 (by simp; omega)
  obtain ⟨cs2, hv2, hl2, hr2'⟩ := elimWindow_chunks
    (fun i₁ i₂ i' h => ⟨(peepholePair?_no_label_call h).1,
      (peepholePair?_no_label_call h).2, fun sa => peepholePair?_detFall hwf sa h⟩)
    c1 true
  have hcr2 : chunksRhs cs2 = c2 := hr2'
  have hstep2 := chunk_step_fnSpec hwf.toWf P hv2 hl2 hcr2 h1 (by simp; omega)
  have hrun2t : ∀ (h2t : VllHost A), h2t.prog = pre ++ c2t ++ suf →
      (vllTarget A hwf.toWf P).LabelsUnique h2t →
      (∀ k < c2t.length, h2t.addrOf (pre.length + k) ≠ ra) →
      (∀ g as bs, (g, as, bs) ∈ E.callees →
        (vllTarget A hwf.toWf P).FnSpec h2t g (Γ g as bs) (bound g) nX) →
      (∀ g, g ∈ E.exits → (vllTarget A hwf.toWf P).Defined h2t g) →
      Eventually (vllStep h2t)
        (vllFnPost hwf.toWf P h2t s ra n nX Q X R) ⟨s, h2t.labelAddr f.name⟩ := by
    intro h2t hp2t hu2t hra2t hcal2t hex2t
    let h2 := mkUnthreadedHost h2t hp2t
    have hp2 : h2.prog = pre ++ c2 ++ suf := mkUnthreadedHost_prog h2t hp2t
    have hlab2 : h2.labelAddr = h2t.labelAddr := mkUnthreadedHost_labelAddr h2t hp2t
    have hdef_iff : ∀ g, (vllTarget A hwf.toWf P).Defined h2 g ↔
        (vllTarget A hwf.toWf P).Defined h2t g := by
      intro g
      have h1 : (vllTarget A hwf.toWf P).Defined h2 g ↔ g ∈ definedLabels h2.prog :=
        (mem_definedLabels_iff (is := h2.prog) (l := g)).symm
      have h2' : (vllTarget A hwf.toWf P).Defined h2t g ↔ g ∈ definedLabels h2t.prog :=
        (mem_definedLabels_iff (is := h2t.prog) (l := g)).symm
      rw [h1, h2', hp2, hp2t, definedLabels_append, definedLabels_append, definedLabels_append,
        definedLabels_append, threadJmp_definedLabels]
    have hu2 : (vllTarget A hwf.toWf P).LabelsUnique h2 := by
      rw [show (vllTarget A hwf.toWf P).LabelsUnique h2 ↔ (definedLabels h2.prog).Nodup from
        (definedLabels_nodup_iff h2.prog).symm]
      have hnodup : (definedLabels h2t.prog).Nodup := (definedLabels_nodup_iff h2t.prog).mpr hu2t
      rw [hp2t, definedLabels_append, definedLabels_append, threadJmp_definedLabels] at hnodup
      rw [hp2, definedLabels_append, definedLabels_append]; exact hnodup
    have hcal2 : ∀ g as bs, (g, as, bs) ∈ E.callees →
        (vllTarget A hwf.toWf P).FnSpec h2 g (Γ g as bs) (bound g) nX := by
      intro g as bs hg a1 m1 Q1 X1 hs1 s1 ra1 R1 ha1 hr1 hsp1 hm1
      have hev := threadJmp_bwd_sim hp2t hu2t
        (hcal2t g as bs hg a1 m1 Q1 X1 hs1 s1 ra1 R1 ha1 hr1 hsp1 hm1)
      change Eventually (vllStep h2) _ ⟨s1, h2.labelAddr g⟩
      rw [hlab2]
      refine eventually_weaken (vllStep h2) _ _ _ ?_ hev
      intro st hst
      rcases hst with h1 | ⟨sym', cs', xs, m', hX, hd, hpc, hrest⟩
      · exact Or.inl h1
      · exact Or.inr ⟨sym', cs', xs, m', hX, (hdef_iff sym').mpr hd,
          (by show st.pc = h2.labelAddr sym'; rw [hlab2]; exact hpc), hrest⟩
    have hex2 : ∀ g, g ∈ E.exits → (vllTarget A hwf.toWf P).Defined h2 g :=
      fun g hg => (hdef_iff g).mpr (hex2t g hg)
    have he2 := hstep2 h2 hp2 hu2 hcal2 hex2 args m Q X hspec s ra R hargs hra hsp hm
    have he2w : Eventually (vllStep h2)
        (vllFnPost hwf.toWf P h2t s ra n nX Q X R) ⟨s, h2t.labelAddr f.name⟩ := by
      rw [← hlab2]
      refine eventually_weaken (vllStep h2) _ _ _ ?_ he2
      intro st hst
      rcases hst with h1 | ⟨sym', cs', xs, m', hX, hd, hpc, hrest⟩
      · exact Or.inl h1
      · exact Or.inr ⟨sym', cs', xs, m', hX, (hdef_iff sym').mp hd, hlab2 ▸ hpc, hrest⟩
    have hnoTramp : ∀ (k : Nat) (l : Sym) (act : JmpAction), c2[k]? = some (.label l) →
        lookupJmpTable (buildJmpTable A c2) l = some act → ∀ s',
        ¬vllFnPost hwf.toWf P h2t s ra n nX Q X R ⟨s', h2t.addrOf (pre.length + k)⟩ ∧
        ((∀ l', c2[k + 1]? ≠ some (.label l')) →
          ¬vllFnPost hwf.toWf P h2t s ra n nX Q X R ⟨s', h2t.addrOf (pre.length + k + 1)⟩) := by
      intro k l act hk hlu s'
      have hkl : k < c2.length := getElem?_some_lt hk
      obtain ⟨m0, hm0, hspec0⟩ := buildJmpTable_spec hlu
      have hm0l : m0 < c2.length := getElem?_some_lt hm0
      have hlu_mem : l ∈ threadedLabels A c2 := by
        simp only [threadedLabels, lookupJmpTable, Option.map_eq_some_iff] at hlu ⊢
        obtain ⟨⟨l', a'⟩, hfind, _⟩ := hlu
        have hmem := List.mem_of_find?_eq_some hfind
        have heq : l' = l := beq_iff_eq.mp (by simpa using List.find?_some hfind)
        exact List.mem_map.mpr ⟨(l', a'), hmem, heq⟩
      have h2_at_k : h2t.prog[pre.length + k]? = some (.label l) := by
        rw [hp2t, List.getElem?_append_left (by simp [hlen2t]; omega),
          List.getElem?_append_right (Nat.le_add_right pre.length k)]
        simp [c2t, threadJmp, List.getElem?_map, hk, threadInstr]
      have hm_eq : m0 = k := by
        have h2_at_m0 : h2t.prog[pre.length + m0]? = some (.label l) := by
          rw [hp2t, List.getElem?_append_left (by simp [hlen2t]; omega),
            List.getElem?_append_right (Nat.le_add_right pre.length m0)]
          simp [c2t, threadJmp, List.getElem?_map, hm0, threadInstr]
        have := hu2t _ _ l h2_at_m0 h2_at_k; omega
      subst m0
      have hk1lt : k + 1 < c2.length := by
        cases act with
        | toLabel _ => rcases hspec0.2 with h1 | h1 <;> exact getElem?_some_lt h1
        | toRet => exact getElem?_some_lt hspec0
      constructor
      · rintro (⟨hpc, _⟩ | ⟨sym', cs', xs, m', hX, ⟨j, hj⟩, hpc, _⟩)
        · exact hra2t k (by omega) hpc
        · have hjlt : j < h2t.prog.length := getElem?_some_lt hj
          have hfirst : ∀ j' < j, h2t.prog[j']? ≠ some (.label sym') := fun j' hj' heq => by
            have := hu2t j' j sym' heq hj; omega
          rw [h2t.labelAddr_wf hj hfirst] at hpc
          have heqj : pre.length + k = j := h2t.addrOf_inj (getElem?_some_lt h2_at_k) hjlt hpc
          subst heqj
          have heqs : l = sym' := Instr.label.inj (Option.some.inj (h2_at_k.symm.trans hj))
          subst heqs
          exact hx_ext l hlu_mem cs' xs m' hX
      · intro hnotL
        rintro (⟨hpc, _⟩ | ⟨sym', cs', xs, m', hX, ⟨j, hj⟩, hpc, _⟩)
        · exact hra2t (k + 1) (by omega) (by simpa [Nat.add_assoc] using hpc)
        · have hjlt : j < h2t.prog.length := getElem?_some_lt hj
          have hfirst : ∀ j' < j, h2t.prog[j']? ≠ some (.label sym') := fun j' hj' heq => by
            have := hu2t j' j sym' heq hj; omega
          rw [h2t.labelAddr_wf hj hfirst] at hpc
          have hk1prog : pre.length + k + 1 < h2t.prog.length := by
            rw [hp2t]; simp [hlen2t]; omega
          have heqj : pre.length + k + 1 = j := h2t.addrOf_inj hk1prog hjlt hpc
          subst heqj
          have h2_at_k1 : h2t.prog[pre.length + k + 1]? =
              (c2[k + 1]?).map (threadInstr A (buildJmpTable A c2)) := by
            rw [hp2t, List.getElem?_append_left (by simp [hlen2t]; omega),
              Nat.add_assoc, List.getElem?_append_right (Nat.le_add_right pre.length (k + 1))]
            simp [c2t, threadJmp]
          have hj' : h2t.prog[pre.length + k + 1]? = some (.label sym') := hj
          rw [hj'] at h2_at_k1
          cases hc1 : c2[k + 1]? with
          | none => simp [hc1] at h2_at_k1
          | some ins =>
            simp only [hc1, Option.map_some, Option.some.injEq] at h2_at_k1
            have := (threadInstr_label_iff (buildJmpTable A c2) ins sym').mp h2_at_k1.symm
            subst this; exact hnotL sym' hc1
    exact threadJmp_fwd_sim hp2t hu2t hnoTramp he2w
  have hrun3 : ∀ (h3 : VllHost A), h3.prog = pre ++ c3 ++ suf →
      (vllTarget A hwf.toWf P).LabelsUnique h3 →
      (∀ k < c3.length, h3.addrOf (pre.length + k) ≠ ra) →
      (∀ g as bs, (g, as, bs) ∈ E.callees →
        (vllTarget A hwf.toWf P).FnSpec h3 g (Γ g as bs) (bound g) nX) →
      (∀ g, g ∈ E.exits → (vllTarget A hwf.toWf P).Defined h3 g) →
      Eventually (vllStep h3)
        (vllFnPost hwf.toWf P h3 s ra n nX Q X R) ⟨s, h3.labelAddr f.name⟩ := by
    intro h3 hp3 hu3 hra3 hcal3 hex3
    obtain ⟨cs3, hv3, hl3, hr3'⟩ := invertJccJmp_chunks_wf A c2t true
    have hcr3 : chunksRhs cs3 = c3 := hr3'
    exact chunks_infix_run_transfer hwf.toWf P hv3 hl3 hcr3 hp3 hu3 (by simp; omega)
      hra3 hcal3 hex3 hrun2t
  obtain ⟨cs4, hv4, hl4, hr4'⟩ := elimFallthrough_chunks_of_label_head A true r3
  have hcr4 : chunksRhs cs4 = passPipe A code := by
    show chunksRhs cs4 = elimFallthrough A c3
    dsimp only [elimFallthrough]; rw [hr3]; exact hr4'
  exact chunks_infix_run_transfer hwf.toWf P hv4 (hr3.symm ▸ hl4) hcr4 hprog hu (by simp; omega)
    hra_ext (fun g as bs hg => (hcal g as bs hg).1) (fun g hg => (hex g hg).1) hrun3

end LeanQbe.T.Vll
