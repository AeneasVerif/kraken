module

public import LeanQbe.T.Frontend.C0
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Frontend.C0

/-!
# End-to-end test of the C0 proof-scaling toolkit (`c0_layout_lemmas!`, `c0_steps`, `Env.ofTable`)

A small "solver state" module: an 8-field `Solver` struct, a `u64` trail array, an array scan
(`sv_find`, calling `sv_get` in its loop condition) and a backtrack-style loop (`sv_backtrack`)
that pops the trail, clears popped slots, and counts steps. The three functions are linked through
one `Env.ofTable` specification table, proved `ModuleOk` with `Env.ofTable_moduleOk`, and shown to
ignore exit continuations with `Env.ofTable_noExit`.

* `c0_layout_lemmas!` generates `structure Solver`, `Solver.At`, and the `@[c0_load]` /
  `@[c0_store]` field lemmas; `c0_steps` finds them through the `Solver.At` footprint.
* The six fields the code never touches (`cap`, `level`, `flags`, `aux0`, `aux1`, and `found` in
  `sv_backtrack`) are never mentioned: stores produce record updates `{ s with f := v }`, and the
  `sv_backtrack` contract and invariant frame them with `AgreesExcept btMask s s'`.

## Proof-to-C0 LOC ratio

Counted as non-blank lines of this file:
* C0 code of the three functions (`u64 sv_get` .. the closing `}` of `sv_backtrack`): 22.
* The three `*_wp` theorems, statements and proofs (`sv_get_wp` .. `sv_backtrack_wp`): 39,
  i.e. **1.8 : 1** (target `≤ 4 : 1`).
* Also counting the three `Spec` definitions and `btMask` (16 lines): 55, i.e. **2.5 : 1**.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.C0StepTest

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.C0Step

c0_layout_lemmas! "typedef struct {
  u64 len; u64 cap; u64 level; u64 found; u64 steps; u64 flags; u64 aux0; u64 aux1;
} Solver;"

c0_decl! sv "
typedef struct {
  u64 len; u64 cap; u64 level; u64 found; u64 steps; u64 flags; u64 aux0; u64 aux1;
} Solver;
u64 sv_get(u64 arr, u64 i) { return ((u64 *)arr)[i]; }
u64 sv_find(u64 sp, u64 arr, u64 key) {
  Solver *s = (Solver *)sp;
  u64 i = 0ULL;
  while (i < s->len) {
    if (sv_get(arr, i) == key) {
      s->found = i;
      return 1ULL;
    }
    i = i + 1ULL;
  }
  s->found = s->len;
  return 0ULL;
}
void sv_backtrack(u64 sp, u64 arr, u64 target) {
  Solver *s = (Solver *)sp;
  while (target < s->len) {
    s->len = s->len - 1ULL;
    ((u64 *)arr)[s->len] = 0ULL;
    s->steps = s->steps + 1ULL;
  }
}
"

/-! ## Generated layout -/

example : Solver.sizeof = 64 := rfl
example (s : Solver) (v : BitVec 64) : ({ s with found := v } : Solver).cap = s.cap := rfl

/-- `AgreesExcept` frames every field outside the mask by `rfl`. -/
example (s s' : Solver) (h : AgreesExcept (fun t => { t with len := 0, steps := 0 }) s s') :
    s'.cap = s.cap ∧ s'.aux1 = s.aux1 :=
  ⟨h.get Solver.cap, h.get Solver.aux1⟩

/-! ## Contracts -/

def svGetSpec : Spec [i64, i64] [i64] := fun (arr, i, ()) m Q _ =>
  ∃ (xs : List (BitVec 64)) (R : Mem 64 → Prop) (hi : i.toNat < xs.length),
    (array (t := i64) arr xs ⋆ R) m ∧ Q (xs[i.toNat], ()) m

def svFindSpec : Spec [i64, i64, i64] [i64] := fun (sp, arr, key, ()) m Q _ =>
  ∃ (s : Solver) (xs : List (BitVec 64)) (R : Mem 64 → Prop), s.len.toNat ≤ xs.length ∧
    (Solver.At sp s ⋆ array (t := i64) arr xs ⋆ R) m ∧
    ∀ r k m', (Solver.At sp { s with found := k } ⋆ array (t := i64) arr xs ⋆ R) m' →
      (r = 1 → k.toNat < s.len.toNat ∧ xs[k.toNat]? = some key) →
      (r = 0 → ∀ j < s.len.toNat, xs[j]? ≠ some key) → Q (r, ()) m'

/-- The fields `sv_backtrack` may change. -/
abbrev btMask (t : Solver) : Solver := { t with len := 0, steps := 0 }

def svBacktrackSpec : Spec [i64, i64, i64] [] := fun (sp, arr, tgt, ()) m Q _ =>
  ∃ (s : Solver) (xs : List (BitVec 64)) (R : Mem 64 → Prop), s.len.toNat ≤ xs.length ∧
    (Solver.At sp s ⋆ array (t := i64) arr xs ⋆ R) m ∧
    ∀ s' ys m', AgreesExcept btMask s s' → s'.len.toNat = min s.len.toNat tgt.toNat →
      ys.length = xs.length → (∀ j < s'.len.toNat, ys[j]? = xs[j]?) →
      (Solver.At sp s' ⋆ array (t := i64) arr ys ⋆ R) m' → Q () m'

/-! ## `Func.wp` proofs -/

theorem sv_get_wp (Γ : Env) : ∀ a m Q X, svGetSpec a m Q X → Func.wp Γ sv_get_body a m Q X := by
  rintro ⟨arr, i, ⟨⟩⟩ m Q X ⟨xs, R, hi, hm, hQ⟩; c0_steps; exact hQ

theorem sv_find_wp (Γ : Env)
    (hGet : ∀ a m Q X, svGetSpec a m Q X → Γ "sv_get" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, svFindSpec a m Q X → Func.wp Γ sv_find_body a m Q X := by
  rintro ⟨sp, arr, key, ⟨⟩⟩ m Q X ⟨s, xs, R, hlen, hm, hQ⟩
  c0_steps
  refine wp_loop_inv (fun v m => v.1.toNat ≤ s.len.toNat ∧ (∀ j < v.1.toNat, xs[j]? ≠ some key) ∧
      (Solver.At sp s ⋆ array (t := i64) arr xs ⋆ R) m) (fun v _ => s.len.toNat - v.1.toNat)
    (fun J hJ => ?_) (fun J v m ⟨hle, hne, hm⟩ hJ => ?_)
  · c0_steps; exact hJ _ _ ⟨by simp, by simp, hm⟩
  · c0_steps
    · c0_call hGet
      refine ⟨xs, _, by omega, by c0_frame, ?_⟩
      c0_steps
      · exact hQ _ _ _ (by c0_frame) (fun _ => ⟨by omega, List.getElem?_eq_some_iff.2 ⟨_, hc⟩⟩)
          (by simp)
      · refine hJ _ _ (by c0_bound) ⟨by c0_bound, fun j hj => ?_, hm⟩
        rcases Nat.lt_or_ge j v.1.toNat with h | h
        · exact hne j h
        obtain rfl : j = v.1.toNat := by simp only at hj; bv_omega
        simpa [List.getElem?_eq_getElem (show v.1.toNat < xs.length by omega)] using hc
    · exact hQ _ _ _ (by c0_frame) (by simp) fun _ j hj => hne j (by omega)

theorem sv_backtrack_wp (Γ : Env) :
    ∀ a m Q X, svBacktrackSpec a m Q X → Func.wp Γ sv_backtrack_body a m Q X := by
  rintro ⟨sp, arr, tgt, ⟨⟩⟩ m Q X ⟨s, xs, R, hlen, hm, hQ⟩
  c0_steps
  refine wp_loop_group (fun n _ m => ∃ s' ys, n = s'.len.toNat ∧ AgreesExcept btMask s s' ∧
      s'.len.toNat ≤ s.len.toNat ∧ (s'.len.toNat < s.len.toNat → tgt.toNat ≤ s'.len.toNat) ∧
      ys.length = xs.length ∧ (∀ j < s'.len.toNat, ys[j]? = xs[j]?) ∧
      (Solver.At sp s' ⋆ array (t := i64) arr ys ⋆ R) m)
    (fun J n _ m hJ ⟨s', ys, hn, hag, hle, hlt, hyl, hys, hm⟩ => ?_) (fun J hJ => ?_)
  · c0_steps
    · refine hJ _ () m ?_ ⟨_, _, rfl, ?_, ?_, ?_, ?_, fun j hj => ?_, by c0_frame⟩
      all_goals first | exact hag.update _ | c0_bound | simpa using hyl | skip
      rw [List.getElem?_set_ne (by c0_bound)]; exact hys j (by c0_bound)
    · exact hQ s' ys m hag (by c0_bound) hyl hys (by c0_frame)
  · c0_steps
    exact hJ _ () m ⟨s, xs, rfl, .refl _ _, Nat.le_refl _, by omega, rfl, fun _ _ => rfl, hm⟩

/-! ## Linking: one specification table for the whole module -/

def svTable : List SpecEntry :=
  [⟨"sv_get", [i64, i64], [i64], svGetSpec, true⟩,
    ⟨"sv_find", [i64, i64, i64], [i64], svFindSpec, true⟩,
    ⟨"sv_backtrack", [i64, i64, i64], [], svBacktrackSpec, true⟩]

abbrev svEnv : Env := Env.ofTable svTable

theorem svEnv_get : ∀ a m Q X, svGetSpec a m Q X → svEnv "sv_get" [i64, i64] [i64] a m Q X :=
  fun _ _ _ _ h => Env.ofTable_of_mem (e := ⟨"sv_get", [i64, i64], [i64], svGetSpec, true⟩)
    (by simp [svTable]) (by decide) h

theorem sv_module_checkAcyclic : sv_module.checkAcyclic = true := by t_kernel_rfl

theorem sv_get_wf : Func.Wf sv_get_body := by t_wf_reify
theorem sv_find_wf : Func.Wf sv_find_body := by t_wf_reify
theorem sv_backtrack_wf : Func.Wf sv_backtrack_body := by t_wf_reify

/-- Headline: the whole module meets its specification table. -/
theorem svEnv_moduleOk : ModuleOk svEnv sv_module :=
  Env.ofTable_moduleOk sv_module_checkAcyclic ⟨sv_get_wf, sv_find_wf, sv_backtrack_wf, trivial⟩
    ⟨.of (sv_get_wp _), .of (sv_find_wp _ svEnv_get), .of (sv_backtrack_wp _), trivial⟩

/-- Every row is `noExit`, as `Compiled.fnSpec_noExit_id` requires. -/
theorem svEnv_noExit : ∀ f as bs xs m Q X X', svEnv f as bs xs m Q X → svEnv f as bs xs m Q X' :=
  Env.ofTable_noExit (by simp [svTable])

#print axioms sv_find_wp
#print axioms sv_backtrack_wp
#print axioms svEnv_moduleOk
#print axioms svEnv_noExit

end LeanQbeTest.T.C0StepTest
