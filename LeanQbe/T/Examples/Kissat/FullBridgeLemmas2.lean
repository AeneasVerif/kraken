module

public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullBinLuckyLemmas
public import LeanQbe.T.Examples.Kissat.FullAssignAddLemmas
public import LeanQbe.T.Examples.Kissat.FullIngestLemmas

/-!
# Kissat `D-Full` Canonical `FullSpec` Bridge Lemmas (Parts 5–8)

Parametric `(Γ : Env)` table-entry bridge lemmas `full_<fn>_bridge_wp` adapting the landed
shards 5–8 to canonical `FullSpec2`/`FullSpec3` contracts (`9` bridgeable functions):
- Part 5 (`FullDenseWatchLemmas`, `0` fns): all `3` deferred as `[bridge-gap]` (`#1134`).
- Part 6 (`FullBinLuckyLemmas`, `2` fns): `full_has_bin`, `full_set_inactive` (`4` `[bridge-gap]`).
- Part 7 (`FullAssignAddLemmas`, `4` fns): `full_assign_lvl`, `full_assign`,
  `full_watch_push`, `full_add_clause`.
- Part 8 (`FullIngestLemmas`, `3` fns): `full_arena_next`, `full_alloc_cl`,
  `full_wstack_defrag` (`1` `[bridge-gap]`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat

/-! ## Part 5: `FullDenseWatchLemmas` (`0` bridgeable; all `3` in `#1134`) -/

/-! ## Part 6: `FullBinLuckyLemmas` (`2` fns) -/

section Part6

theorem full_has_bin_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullHasBinSpec a m Q X → Func.wp Γ full_has_bin_body a m Q X := by
  rintro ⟨h, a, b, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hm, hQ⟩
  refine full_has_bin_wp Γ _ m Q X ⟨c, F0, s, R, rfl, ⟨hlen, F_cur, hw⟩, hm, fun r hr => ?_⟩
  exact hQ r fun hrt => let ⟨ha, hb, hab, hneg, hent⟩ := hr hrt; ⟨ha, hb, hab, hneg, hent F_cur hw⟩

theorem full_set_inactive_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullSetInactiveSpec a m Q X → Func.wp Γ full_set_inactive_body a m Q X := by
  intro a m Q X hspec
  exact full_set_inactive_wp Γ a m Q X hspec

end Part6

/-! ## Part 7: `FullAssignAddLemmas` (`4` fns) -/

section Part7

theorem full_assign_lvl_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullAssignLvlSpec a m Q X → Func.wp Γ full_assign_lvl_body a m Q X :=
  full_assign_lvl_wp Γ

theorem full_assign_bridge_wp (Γ : Env)
    (hAssignLvl : ∀ a m Q X, fullAssignLvlSpec a m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] a m Q X) :
    ∀ a m Q X, fullAssignSpec a m Q X → Func.wp Γ full_assign_body a m Q X :=
  full_assign_wp Γ hAssignLvl

theorem full_watch_push_bridge_wp (Γ : Env)
    (hDefrag : ∀ a m Q X, fullWstackDefragSpec a m Q X → Γ "full_wstack_defrag" [i64] [] a m Q X) :
    ∀ a m Q X, fullWatchPushSpec a m Q X → Func.wp Γ full_watch_push_body a m Q X :=
  full_watch_push_wp Γ hDefrag

theorem full_add_clause_bridge_wp (Γ : Env)
    (hAlloc : ∀ a m Q X, fullAllocClSpec a m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] a m Q X)
    (hPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullAddClauseSpec a m Q X → Func.wp Γ full_add_clause_body a m Q X := by
  rintro ⟨h, len, glue, red, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hle, hlits, hm, hQ⟩
  refine full_add_clause_wp Γ hAlloc hPush _ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm, hle, hlits, hm, ?_⟩
  split
  · next h1 => simp only [h1, ↓reduceIte] at hQ; exact hQ
  · next h1 =>
    simp only [h1, ↓reduceIte] at hQ
    split
    · next h2 => simp only [h2, ↓reduceIte] at hQ; exact hQ
    · next h2 =>
      simp only [h2, ↓reduceIte] at hQ
      exact fun r arena' alen' wvec' wstk' wlen' wusable' fred' ni' nr' wsort' m'
        hr hlen' hw' hrefs hnd halloc hm' =>
        hQ r arena' alen' wvec' wstk' wlen' wusable' fred' ni' nr' wsort' m'
          hr hlen' hw' hrefs (fun h => hnd h) halloc hm'

end Part7

/-! ## Part 8: `FullIngestLemmas` (`3` fns) -/

section Part8

theorem full_arena_next_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullArenaNextSpec a m Q X → Func.wp Γ full_arena_next_body a m Q X :=
  full_arena_next_wp Γ

theorem full_alloc_cl_bridge_wp (Γ : Env) :
    ∀ a m Q X, fullAllocClSpec a m Q X → Func.wp Γ full_alloc_cl_body a m Q X :=
  full_alloc_cl_wp Γ

theorem full_wstack_defrag_bridge_wp (Γ : Env)
    (hSift : ∀ a m Q X, fullWsortSiftSpec a m Q X →
      Γ "full_wsort_sift" [i64, i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, fullWstackDefragSpec a m Q X → Func.wp Γ full_wstack_defrag_body a m Q X := by
  refine full_wstack_defrag_wp Γ ?_
  rintro ⟨wvp, wsp, start, n, ⟨⟩⟩ m Q X
    ⟨nlits, wvec, ws, R, hwv, _hst62, hn62, hstn, hnws, hlt, hhp, hm, hQ⟩
  exact hSift (wvp, wsp, start, n, ()) m Q X
    ⟨nlits, wvec, ws, R, hwv, hstn, hn62, hnws, hlt, hhp, hm, hQ⟩

end Part8

end LeanQbe.T.Examples.Kissat.Full
