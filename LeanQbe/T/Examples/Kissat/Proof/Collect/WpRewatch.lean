/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Collect
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
public import LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
import LeanQbe.T.Examples.Kissat.Proof.Collect.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Collect.HelpersWatch
import LeanQbe.T.Examples.Kissat.Proof.Collect.HelpersArena
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# Arena Rewatching WP Proofs (`Proof.Collect.WpRewatch`)

Canonical `Func.wp` proofs for `full_rewatch_range_m6`, `full_rewatch_arena_m6`, and
`full_rewatch_arena` from `Src.Collect`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Collect

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Collect
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullKissatMath
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open LeanQbe.T.Examples.Kissat.Proof.Collect.Spec
open Kraken.Bedrock2.Test
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Collect.M6Tactics1

public section

private theorem collect_fwd1_rw {t : Ty} {Q : Post [t]} :
    (fun (r : Tup Val [t]) m' => Q (r.fst, ()) m') = Q := funext fun ⟨_, ⟨⟩⟩ => rfl

private theorem full_mem_cast_rw {c : FullCfg} {s1 s2 : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (FullMem c s1 ⋆ R) m) (heq : s1 = s2) : (FullMem c s2 ⋆ R) m :=
  heq ▸ hm

private theorem modeWatchesInv_to_sparse {F_cur : List (List Nat)} {k : FullCoreState}
    (h : ModeWatchesInv F_cur k) (hdm : k.dense_mode = 0#64) : WatchesInv F_cur k := by
  unfold ModeWatchesInv at h; rwa [rw_ite_pos hdm] at h

private theorem bv32_large_props (l : BitVec 32) :
    ((l &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32 ∧ (l &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32 := by
  refine ⟨?_, ?_⟩
  · rw [BitVec.and_assoc, show (0x7FFFFFFF#32 &&& 0x80000000#32) = 0#32 from rfl,
      BitVec.and_zero]
  · intro h; have h31 := congrArg (fun x : BitVec 32 => x[31]) h; revert h31; simp

private theorem list_swap_eq_idx {α : Type} {xs : List α} {i j i' j' : Nat}
    (hi : i = i') (hj : j = j') (hi_lt : i < xs.length) (hj_lt : j < xs.length)
    (hi'_lt : i' < xs.length) (hj'_lt : j' < xs.length) :
    (xs.set i (xs[j]'hj_lt)).set j (xs[i]'hi_lt) =
    (xs.set i' (xs[j']'hj'_lt)).set j' (xs[i']'hi'_lt) := by
  subst hi hj; rfl

private theorem rw_lit_lt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {p sz : Nat} (hsz_fit : p + 3 + sz ≤ k.arena.length)
    (hw : FullWitnessInv c F0 F_cur k) (href : p ∈ fullArenaClauseRefsCore k)
    (hng : fullArenaClauseGarbCore k p = false) (hsz : fullArenaClauseSizeCore k p = sz)
    {j : Nat} (hj : j < sz) : (k.arena[p + 3 + j]?.getD 0#32).toNat < 2 * k.cur_vars := by
  have hbd : p + 3 + fullArenaClauseSizeCore k p ≤ k.arena.length := by rw [hsz]; omega
  have hmem := (mem_fullArenaClauseLitsCore_iff hbd).mpr ⟨j, by rw [hsz]; exact hj, rfl⟩
  have hlt := hw.arena.lits_lt p href hng _ hmem
  rwa [List.getElem?_eq_getElem (by omega : p + 3 + j < k.arena.length), Option.getD_some]

private theorem rw_body_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sL : FullState} {p sz : Nat} {ar0 ar1 : List (BitVec 32)}
    (hlenL : sL.LengthsOk c) (hp_ref0 : p ∈ fullArenaClauseRefs s) (har0 : ar0.length = c.arena_cap)
    (hw0 : FullWitnessInv c F0 F_cur { sL.core with arena := ar0 })
    (hrefs0 : fullArenaClauseRefs { sL with core := { sL.core with arena := ar0 } } =
      fullArenaClauseRefs s)
    (hno0 : ∀ r ∈ fullArenaClauseRefs s,
      (fullArenaHdr { sL with core := { sL.core with arena := ar0 } } r &&& 0x00800000#32) = 0#32 ∧
      fullArenaClauseGarb { sL with core := { sL.core with arena := ar0 } } r = false)
    (hsz0 : fullArenaClauseSize { sL with core := { sL.core with arena := ar0 } } p = sz)
    (hnd0 : FullArenaVarsNodup s →
      FullArenaVarsNodup { sL with core := { sL.core with arena := ar0 } })
    (har1 : ar1.length = c.arena_cap)
    (hout : OutsideSliceAgrees (p + 1) (p + 3 + sz) ar0 ar1) (h2eq : ar1[p + 2]? = ar0[p + 2]?)
    (hperm : List.Perm (fullArenaClauseLitsCore { sL.core with arena := ar1 } p)
      (fullArenaClauseLitsCore { sL.core with arena := ar0 } p)) :
    let s1 : FullState := { sL with core := { sL.core with arena := ar1 } }
    ar1.length = c.arena_cap ∧ s1.LengthsOk c ∧ FullWitnessInv c F0 F_cur s1.core ∧
    fullArenaClauseRefs s1 = fullArenaClauseRefs s ∧ p ∈ fullArenaClauseRefsCore s1.core ∧
    (∀ r ∈ fullArenaClauseRefs s,
      (fullArenaHdr s1 r &&& 0x00800000#32) = 0#32 ∧ fullArenaClauseGarb s1 r = false) ∧
    fullArenaClauseSize s1 p = sz ∧ (FullArenaVarsNodup s → FullArenaVarsNodup s1) := by
  intro s1
  let s0 : FullState := { sL with core := { sL.core with arena := ar0 } }
  have hlen0 : s0.core.LengthsOk c := { hlenL.core_ok with arena_len_arr := har0 }
  have href0 : p ∈ fullArenaClauseRefsCore s0.core := by
    change p ∈ fullArenaClauseRefs s0; rw [hrefs0]; exact hp_ref0
  have hsz1 : fullArenaClauseSizeCore s1.core p = fullArenaClauseSizeCore s0.core p := by
    unfold fullArenaClauseSizeCore s1 s0; exact congrArg (fun o => (o.getD 0#32).toNat) h2eq
  obtain ⟨hrefs1, hmeta1, hlits_oth1, hw1⟩ := modifyClauseBody_preserves_witness hlen0 hw0 href0
    (ar' := ar1) har1 (by rw [show fullArenaClauseSizeCore s0.core p = sz from hsz0]; exact hout)
    h2eq (fun l => hperm.mem_iff)
  refine ⟨har1, ⟨{ hlenL.core_ok with arena_len_arr := har1 }, hlenL.scratch_ok⟩, hw1,
    hrefs1.trans hrefs0, by rw [hrefs1]; exact href0,
    fun r hr => ?_, hsz1.trans hsz0, fun hnd => ?_⟩
  · have hr0 : r ∈ fullArenaClauseRefsCore s0.core := by
      change r ∈ fullArenaClauseRefs s0; rw [hrefs0]; exact hr
    have hm := hmeta1 r hr0; have ho := hno0 r hr
    exact ⟨by change (fullArenaHdrCore s1.core r &&& 0x00800000#32) = 0#32; rw [hm.1]; exact ho.1,
      by change fullArenaClauseGarbCore s1.core r = false; rw [hm.2.2]; exact ho.2⟩
  · intro r hr hng
    have hr0 : r ∈ fullArenaClauseRefsCore s0.core := by
      change r ∈ fullArenaClauseRefsCore s1.core at hr; rw [hrefs1] at hr; exact hr
    by_cases hrp : r = p
    · subst r; exact (hperm.map (· / 2)).nodup_iff.mpr (hnd0 hnd p href0 (hno0 p hp_ref0).2)
    · change ((fullArenaClauseLitsCore s1.core r).map (· / 2)).Nodup; rw [hlits_oth1 r hr0 hrp]
      exact hnd0 hnd r hr0 (by change fullArenaClauseGarbCore s0.core r = false
                               rw [← (hmeta1 r hr0).2.2]; exact hng)

private theorem rw_swap_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sL : FullState} {p sz a b : Nat} {ar0 : List (BitVec 32)}
    (hlenL : sL.LengthsOk c) (hp_ref0 : p ∈ fullArenaClauseRefs s)
    (hsz_fit : p + 3 + sz ≤ s.core.arena_len) (hal_le : s.core.arena_len ≤ c.arena_cap)
    (har0 : ar0.length = c.arena_cap)
    (hw0 : FullWitnessInv c F0 F_cur { sL.core with arena := ar0 })
    (hrefs0 : fullArenaClauseRefs { sL with core := { sL.core with arena := ar0 } } =
      fullArenaClauseRefs s)
    (hno0 : ∀ r ∈ fullArenaClauseRefs s,
      (fullArenaHdr { sL with core := { sL.core with arena := ar0 } } r &&& 0x00800000#32) = 0#32 ∧
      fullArenaClauseGarb { sL with core := { sL.core with arena := ar0 } } r = false)
    (hsz0 : fullArenaClauseSize { sL with core := { sL.core with arena := ar0 } } p = sz)
    (hnd0 : FullArenaVarsNodup s →
      FullArenaVarsNodup { sL with core := { sL.core with arena := ar0 } })
    (ha : a < sz) (hb : b < sz) :
    let pa := p + 3 + a; let pb := p + 3 + b
    let ar1 := (ar0.set pa (ar0[pb]'(by omega))).set pb (ar0[pa]'(by omega))
    let s1 : FullState := { sL with core := { sL.core with arena := ar1 } }
    ar1.length = c.arena_cap ∧ FullWitnessInv c F0 F_cur s1.core ∧
    fullArenaClauseRefs s1 = fullArenaClauseRefs s ∧
    (∀ r ∈ fullArenaClauseRefs s,
      (fullArenaHdr s1 r &&& 0x00800000#32) = 0#32 ∧ fullArenaClauseGarb s1 r = false) ∧
    fullArenaClauseSize s1 p = sz ∧ (FullArenaVarsNodup s → FullArenaVarsNodup s1) := by
  intro pa pb ar1 s1
  have h2eq : ar1[p + 2]? = ar0[p + 2]? := by
    dsimp only [ar1, pa, pb]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  have hsz1 : fullArenaClauseSizeCore s1.core p = sz := by
    unfold fullArenaClauseSizeCore s1; rw [h2eq]; exact hsz0
  have hperm : List.Perm (fullArenaClauseLitsCore s1.core p)
      (fullArenaClauseLitsCore { sL.core with arena := ar0 } p) := by
    unfold fullArenaClauseLitsCore; rw [hsz1, show fullArenaClauseSizeCore _ p = sz from hsz0]
    exact swapClauseLits_perm ha hb (by omega)
  obtain ⟨h1, _, h3, h4, _, h6, h7, h8⟩ := rw_body_step hlenL hp_ref0 har0 hw0 hrefs0 hno0 hsz0
    hnd0 (ar1 := ar1) (by simp [ar1, har0])
    (fun idx hidx => by
      dsimp only [ar1, pa, pb]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
    h2eq hperm
  exact ⟨h1, h3, h4, h6, h7, h8⟩

private theorem rw_set_saved_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sL : FullState} {p : BitVec 64} {sz : Nat} {arA : List (BitVec 32)}
    (hlenL : sL.LengthsOk c) (hp_ref0 : p.toNat ∈ fullArenaClauseRefs s)
    (hsz_fit : p.toNat + 3 + sz ≤ s.core.arena_len) (hal_le : s.core.arena_len ≤ c.arena_cap)
    (harA : arA.length = c.arena_cap)
    (hwA : FullWitnessInv c F0 F_cur { sL.core with arena := arA })
    (hrefsA : fullArenaClauseRefs { sL with core := { sL.core with arena := arA } } =
      fullArenaClauseRefs s)
    (hnoA : ∀ r ∈ fullArenaClauseRefs s,
      (fullArenaHdr { sL with core := { sL.core with arena := arA } } r &&& 0x00800000#32) = 0#32 ∧
      fullArenaClauseGarb { sL with core := { sL.core with arena := arA } } r = false)
    (hszA : fullArenaClauseSize { sL with core := { sL.core with arena := arA } } p.toNat = sz)
    (hndA : FullArenaVarsNodup s →
      FullArenaVarsNodup { sL with core := { sL.core with arena := arA } })
    (hp1_eq : (p + 1#64).toNat = p.toNat + 1) :
    let arB := arA.set (p + 1#64).toNat 2#32
    let sB : FullState := { sL with core := { sL.core with arena := arB } }
    arB.length = c.arena_cap ∧ sB.LengthsOk c ∧ FullWitnessInv c F0 F_cur sB.core ∧
    fullArenaClauseRefs sB = fullArenaClauseRefs s ∧ p.toNat ∈ fullArenaClauseRefsCore sB.core ∧
    (∀ r ∈ fullArenaClauseRefs s,
      (fullArenaHdr sB r &&& 0x00800000#32) = 0#32 ∧ fullArenaClauseGarb sB r = false) ∧
    (FullArenaVarsNodup s → FullArenaVarsNodup sB) := by
  intro arB sB
  have h2eq : arB[p.toNat + 2]? = arA[p.toNat + 2]? := List.getElem?_set_ne (by omega)
  have hszA' : fullArenaClauseSizeCore { sL.core with arena := arA } p.toNat = sz := hszA
  have hszB : fullArenaClauseSizeCore sB.core p.toNat = sz := by
    unfold fullArenaClauseSizeCore sB; rw [h2eq]; exact hszA'
  have hlitsB : fullArenaClauseLitsCore sB.core p.toNat =
      fullArenaClauseLitsCore { sL.core with arena := arA } p.toNat :=
    fullArenaClauseLitsCore_eq_of_hold
      (by rw [hszA']; change p.toNat + 3 + sz ≤ arA.length; omega)
      (by rw [hszA']; change p.toNat + 3 + sz ≤ arB.length; simp [arB, harA]; omega)
      (hszB.trans hszA'.symm) (fun j _ => List.getElem?_set_ne (by omega))
  obtain ⟨h1, h2, h3, h4, h5, h6, _, h8⟩ := rw_body_step hlenL hp_ref0 harA hwA hrefsA hnoA
    hszA hndA (ar1 := arB) (by simp [arB, harA])
    (fun idx hidx => List.getElem?_set_ne (by omega)) h2eq (hlitsB ▸ List.Perm.refl _)
  exact ⟨h1, h2, h3, h4, h5, h6, h8⟩

private theorem rw_push_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {lit w0 w1 : BitVec 32} {ok : Bool} {wvec' wstk' : List (BitVec 32)}
    {wlen' : Nat} {wu' : BitVec 64}
    (hw : FullWitnessInv c F0 F_cur k) (hdm : k.dense_mode = 0#64)
    (hlay' : WatchStackLayout { k with wvec := wvec', wstk := wstk', wlen := wlen',
                                       wusable := wu' })
    (hw0 : (w0 &&& 0x80000000#32) = 0#32) (hw1_lt : w1.toNat < 0x80000000)
    (href : w1.toNat ∈ fullArenaClauseRefsCore k)
    (hoth : ∀ l < 2 * k.cur_vars, l ≠ lit.toNat →
      fullWatchSizeCore { k with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' } l =
        fullWatchSizeCore k l ∧
      ∀ i < fullWatchSizeCore k l,
        wstk'[fullWatchOffCore { k with wvec := wvec', wstk := wstk', wlen := wlen',
                                        wusable := wu' } l + i]? =
          k.wstk[fullWatchOffCore k l + i]?)
    (hokt : ok = true →
      lit.toNat < 2 * k.cur_vars ∧ (2 = 1 ∨ 2 = 2) ∧
      fullWatchSizeCore { k with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
          lit.toNat = fullWatchSizeCore k lit.toNat + 2 ∧
      (∀ i < fullWatchSizeCore k lit.toNat,
        wstk'[fullWatchOffCore { k with wvec := wvec', wstk := wstk', wlen := wlen',
                                        wusable := wu' } lit.toNat + i]? =
          k.wstk[fullWatchOffCore k lit.toNat + i]?) ∧
      wstk'[fullWatchOffCore { k with wvec := wvec', wstk := wstk', wlen := wlen',
                                      wusable := wu' } lit.toNat + fullWatchSizeCore k lit.toNat]? =
        some w0 ∧
      (2 = 2 →
        wstk'[fullWatchOffCore { k with wvec := wvec', wstk := wstk', wlen := wlen',
                                        wusable := wu' } lit.toNat +
          fullWatchSizeCore k lit.toNat + 1]? = some w1))
    (hokf : ok = false → lit.toNat < 2 * k.cur_vars →
      fullWatchSizeCore { k with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
          lit.toNat = fullWatchSizeCore k lit.toNat ∧
      ∀ i < fullWatchSizeCore k lit.toNat,
        wstk'[fullWatchOffCore { k with wvec := wvec', wstk := wstk', wlen := wlen',
                                        wusable := wu' } lit.toNat + i]? =
          k.wstk[fullWatchOffCore k lit.toNat + i]?) :
    FullWitnessInv c F0 F_cur
      { k with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := fullWatchPush_preserves_modeWatchesInv (cnt := 2#32) hw.watches hlay' rfl rfl
      (fun _ hr => hr) (fun hc => by exfalso; revert hc; decide)
      (fun _ => ⟨hw0, fun h => absurd hdm h, hw1_lt, href⟩) hoth
      (fun h => by simpa using hokt h) hokf }

private def RewatchRangeLoopInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (arg : Tup Val [i64]) (mL : Mem 64) : Prop :=
  let (p, ()) := arg
  p.toNat ≤ s.core.arena_len ∧ (p.toNat < s.core.arena_len → p.toNat ∈ fullArenaClauseRefs s) ∧
  ∃ arL wvecL wstkL wlenL wuL wsL,
    let sL : FullState :=
      { core := { s.core with arena := arL, wvec := wvecL, wstk := wstkL, wlen := wlenL,
                              wusable := wuL }
        scratch := { s.scratch with wsort := wsL } }
    sL.LengthsOk c ∧ FullWitnessInv c F0 F_cur sL.core ∧
    fullArenaClauseRefs sL = fullArenaClauseRefs s ∧
    (∀ r ∈ fullArenaClauseRefs s,
      (fullArenaHdr sL r &&& 0x00800000#32) = 0#32 ∧ fullArenaClauseGarb sL r = false) ∧
    (FullArenaVarsNodup s → FullArenaVarsNodup sL) ∧ (FullMem c sL ⋆ R) mL

private def RewatchRangeSwapInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s sL : FullState) (R : Mem 64 → Prop) (p : BitVec 64) (sz32 : BitVec 32)
    (_ : Tup Val []) (mA : Mem 64) : Prop :=
  ∃ arA : List (BitVec 32), arA.length = c.arena_cap ∧
    let sA : FullState := { sL with core := { sL.core with arena := arA } }
    FullWitnessInv c F0 F_cur sA.core ∧ fullArenaClauseRefs sA = fullArenaClauseRefs s ∧
    (∀ r ∈ fullArenaClauseRefs s,
      (fullArenaHdr sA r &&& 0x00800000#32) = 0#32 ∧ fullArenaClauseGarb sA r = false) ∧
    fullArenaClauseSize sA p.toNat = sz32.toNat ∧
    (FullArenaVarsNodup s → FullArenaVarsNodup sA) ∧ (FullMem c sA ⋆ R) mA

theorem full_rewatch_range_m6_wp (Γ : Env)
    (hrank : ∀ a m Q X, fullLitRankSpec a m Q X →
      Γ "full_lit_rank_m6" [i64, i64, i32] [i64] a m Q X)
    (hpush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push_m6" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullRewatchRangeSpec a m Q X →
      Func.wp Γ full_rewatch_range_m6_body a m Q X := by
  rintro ⟨h, start, dst, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hst_le, hst_mem, hdst_eq, hw, hdm0, hno_sg, hm, hQ⟩
  change fullRewatchArenaPost c F0 F_cur s R Q at hQ
  have hcap_lt : c.arena_cap < 2 * dimacsBound := c.harena
  have hmax_lt : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hcap_lt hmax_lt
  have hal_le := hlen.core_ok.arena_len_le
  have hcv_le := hlen.core_ok.cur_vars_le
  have hv_len := hlen.core_ok.vals_len
  have hl_len := hlen.core_ok.lvl_len
  m6_steps
  refine wp_loop_inv (RewatchRangeLoopInv c F0 F_cur s R)
    (fun (p, ()) _ => s.core.arena_len - p.toNat) (fun JL hLoopL => ?_) ?_
  · m6_steps
    exact hLoopL (start, ()) m ⟨hst_le, hst_mem, s.core.arena, s.core.wvec, s.core.wstk,
      s.core.wlen, s.core.wusable, s.scratch.wsort, hlen, hw, rfl, hno_sg, id, hm⟩
  · rintro JL ⟨p, ⟨⟩⟩ mL
      ⟨hp_le, hp_mem, arL, wvecL, wstkL, wlenL, wuL, wsL, hlenL, hwL, hrefsL, hnoL, hndL, hmL⟩
      hLoopL
    let sL : FullState :=
      { core := { s.core with arena := arL, wvec := wvecL, wstk := wstkL, wlen := wlenL,
                              wusable := wuL }
        scratch := { s.scratch with wsort := wsL } }
    have harL_len : arL.length = c.arena_cap := hlenL.core_ok.arena_len_arr
    m6_split
    · have hp_lt : p.toNat < s.core.arena_len := by
        have : p.toNat < dst.toNat := by c0_bound
        omega
      have hp_ref0 : p.toNat ∈ fullArenaClauseRefs s := hp_mem hp_lt
      have hp_ref : p.toNat ∈ fullArenaClauseRefsCore sL.core := by
        change p.toNat ∈ fullArenaClauseRefs sL; rw [hrefsL]; exact hp_ref0
      have hpwf := hwL.arena.refs_wf p.toNat hp_ref
      have hp_no := hnoL p.toNat hp_ref0
      have hsz_ge3 : 3 ≤ fullArenaClauseSizeCore sL.core p.toNat := hpwf.2.1
      have hsz_fit : p.toNat + 3 + fullArenaClauseSizeCore sL.core p.toNat ≤ s.core.arena_len := by
        have h1 : p.toNat + 3 + fullArenaClauseSizeCore sL.core p.toNat ≤
            fullArenaNextOff arL s.core.arena_len p.toNat := hpwf.2.2.1
        have h2 : fullArenaNextOff arL s.core.arena_len p.toNat ≤ s.core.arena_len := hpwf.2.2.2.1
        omega
      have hp2_eq : (p + 2#64).toNat = p.toNat + 2 := bv64_add2_lt (by omega)
      have hp2_lt : (p + 2#64).toNat < arL.length := by omega
      let sz32 := arL[(p + 2#64).toNat]'hp2_lt
      have hsz_eq : sz32.toNat = fullArenaClauseSizeCore sL.core p.toNat := by
        have h1 : sz32 = arL[p.toNat + 2]'(by omega) := by dsimp only [sz32]; simp only [hp2_eq]
        unfold fullArenaClauseSizeCore sL
        simp [h1, List.getElem?_eq_getElem (by omega : p.toNat + 2 < arL.length)]
      have hsz_fit2 : p.toNat + 3 + sz32.toNat ≤ s.core.arena_len := by rw [hsz_eq]; exact hsz_fit
      have hsz_ge32 : 3 ≤ sz32.toNat := by omega
      have hnext_eq : fullArenaNextOff arL s.core.arena_len p.toNat = p.toNat + 3 + sz32.toNat := by
        have h1 : (arL[p.toNat]?.getD 0#32 &&& 0x00800000#32) = 0#32 := hp_no.1
        have h2 : (arL[p.toNat + 2]?.getD 0#32).toNat = sz32.toNat := by rw [hsz_eq]; rfl
        simp [fullArenaNextOff, show ¬ (p.toNat + 3 > s.core.arena_len) by omega, h2,
          show ¬ (p.toNat + 3 + sz32.toNat > s.core.arena_len) by omega, h1]
      have hnext_mem : p.toNat + 3 + sz32.toNat = s.core.arena_len ∨
          p.toNat + 3 + sz32.toNat ∈ fullArenaClauseRefs s := by
        have h := fullArenaClauseRefs_next_or_end hwL.arena hp_ref
        change _ = s.core.arena_len ∨ _ ∈ fullArenaClauseRefs sL at h
        rwa [show fullArenaNextOff sL.core.arena sL.core.arena_len p.toNat =
          p.toNat + 3 + sz32.toNat from hnext_eq, hrefsL] at h
      clear hnext_eq
      m6_to_group
      refine wp_join_group (RewatchRangeSwapInv c F0 F_cur s sL R p sz32) ?_ ?_
      · rintro _ ⟨⟩ mA ⟨arA, harA, hwA, hrefsA, hnoA, hszA, hndA, hmA⟩
        clear hrank hwL hrefsL hnoL hndL hp_ref hp_no hpwf hsz_fit hsz_eq harL_len hmL
        have hp1_eq : (p + 1#64).toNat = p.toNat + 1 := bv64_add1_lt (by omega)
        have hp1_lt : (p + 1#64).toNat < arA.length := by omega
        let arB := arA.set (p + 1#64).toNat 2#32
        let sB : FullState := { sL with core := { sL.core with arena := arB } }
        obtain ⟨harB, hlenB, hwB, hrefsB_s, hrefB, hnoB, hndB⟩ :=
          rw_set_saved_step hlenL hp_ref0 hsz_fit2 hal_le harA hwA hrefsA hnoA hszA hndA hp1_eq
        have harB_len : arB.length = c.arena_cap := harB
        have hp3_eq : (p + 3#64).toNat = p.toNat + 3 := bv64_add3_lt (by omega)
        have hp4_eq : (p + 4#64).toNat = p.toNat + 4 := bv64_add4_lt (by omega)
        have hp3_lt : (p + 3#64).toNat < arB.length := by omega
        have hp4_lt : (p + 4#64).toNat < arB.length := by omega
        let l0 := arB[(p + 3#64).toNat]'hp3_lt
        let l1 := arB[(p + 4#64).toNat]'hp4_lt
        have hp32_eq : (p.setWidth 32).toNat = p.toNat := by
          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
        have hp32_lt : (p.setWidth 32).toNat < 0x80000000 := by omega
        have hp32_ne : p.setWidth 32 ≠ 0xFFFFFFFF#32 := fun h => by
          have := congrArg BitVec.toNat h; simp at this; omega
        have hlw0 := bv32_large_props l1
        have hlw1 := bv32_large_props l0
        have hwB_sp : WatchesInv F_cur sB.core := modeWatchesInv_to_sparse hwB.watches hdm0
        m6_steps; c0_call hpush
        refine ⟨c, sB, R, rfl, hlenB, hwB_sp.layout, fun h => by exfalso; revert h; decide,
          fun _ => ⟨hlw0.2, hp32_ne⟩, hm,
          fun ok1 wvec1 wstk1 wlen1 wu1 ws1 m1 hlen1 hlay1 hoth1 hok1t hok1f hm1 => ?_⟩
        have hw1 := rw_push_step hwB hdm0 hlay1 hlw0.1 hp32_lt (by rw [hp32_eq]; exact hrefB)
          hoth1 hok1t (fun h hlt => (hok1f h).1 hlt)
        clear hoth1 hok1t hok1f hwB_sp hlw0 hlenB hm
        m6_split
        · m6_steps; c0_call hpush
          refine ⟨c, { core := { sB.core with wvec := wvec1, wstk := wstk1, wlen := wlen1,
                                              wusable := wu1 }
                       scratch := { s.scratch with wsort := ws1 } }, R, rfl, hlen1, hlay1,
            fun h => by exfalso; revert h; decide, fun _ => ⟨hlw1.2, hp32_ne⟩, hm1,
            fun ok2 wvec2 wstk2 wlen2 wu2 ws2 m2 hlen2 hlay2 hoth2 hok2t hok2f hm2 => ?_⟩
          have hw2 := rw_push_step hw1 hdm0 hlay2 hlw1.1 hp32_lt
            (by rw [hp32_eq]; exact hrefB) hoth2 hok2t (fun h hlt => (hok2f h).1 hlt)
          clear hoth2 hok2t hok2f hlw1 hlen1 hlay1 hm1 hpush
          m6_split
          · have hp_next_eq : (p + 3#64 + sz32.setWidth 64).toNat = p.toNat + 3 + sz32.toNat :=
              bv64_add3_zext_lt (by omega)
            m6_steps
            refine hLoopL (p + 3#64 + sz32.setWidth 64, ()) m2
              (by dsimp only; rw [hp_next_eq]; omega)
              ⟨by rw [hp_next_eq]; omega, fun hlt => ?_, arB, wvec2, wstk2, wlen2, wu2, ws2,
               hlen2, hw2, hrefsB_s, hnoB, hndB, hm2⟩
            rw [hp_next_eq] at hlt ⊢
            rcases hnext_mem with he | hmem
            · omega
            · exact hmem
          · m6_steps
            exact hQ false arB wvec2 wstk2 wlen2 wu2 1#64 ws2 m
              ⟨{ hlen2.core_ok with }, hlen2.scratch_ok⟩ (fullWitnessInv_with_oom hw2)
              hndB hrefsB_s (fun _ => rfl) (fun h => Bool.noConfusion h)
              (full_mem_cast_rw hm rfl)
        · m6_steps
          exact hQ false arB wvec1 wstk1 wlen1 wu1 1#64 ws1 m
            ⟨{ hlen1.core_ok with }, hlen1.scratch_ok⟩ (fullWitnessInv_with_oom hw1)
            hndB hrefsB_s (fun _ => rfl) (fun h => Bool.noConfusion h)
            (full_mem_cast_rw hm rfl)
      · intro JA hJA
        clear hLoopL JL hQ hpush hnext_mem hw hlen hno_sg hdst_eq hdm0 hp_le hp_mem hsz_ge3
          hsz_fit hp2_eq hst_le hst_mem
        m6_split
        · m6_steps; exact hJA () mL ⟨arL, harL_len, hwL, hrefsL, hnoL, hsz_eq.symm, hndL, hmL⟩
        · m6_split
          · have hp3_eq : (p + 3#64).toNat = p.toNat + 3 := bv64_add3_lt (by omega)
            have hp3_lt : (p + 3#64).toNat < arL.length := by omega
            have hl0_lt : (arL[(p + 3#64).toNat]'hp3_lt).toNat < 2 * s.core.cur_vars := by
              have h1 : arL[(p + 3#64).toNat]'hp3_lt = arL[p.toNat + 3]'(by omega) := by
                simp only [hp3_eq]
              have := rw_lit_lt (k := sL.core) (by change _ ≤ arL.length; omega)
                hwL hp_ref hp_no.2 hsz_eq.symm (j := 0) (by omega)
              rw [Nat.add_zero, List.getElem?_eq_getElem (by omega : p.toNat + 3 < arL.length),
                Option.getD_some] at this; rwa [h1]
            m6_steps; c0_call hrank
            have hl0_v : (arL[(p + 3#64).toNat]'hp3_lt).toNat < s.core.vals.length := by
              rw [hv_len]; omega
            have hl0_lv : (arL[(p + 3#64).toNat]'hp3_lt).toNat / 2 < s.core.lvl.length := by
              rw [hl_len]; omega
            refine ⟨s.core.vals, s.core.lvl, FullValsLvlRest c sL ⋆ R,
              by simpa using hl0_v, by simpa using hl0_lv, focus_full_vals_lvl hmL, fun r0 => ?_⟩
            m6_steps
            refine wp_loop_inv
              (fun (i0, _r0, i, ()) m1 =>
                mL = m1 ∧ i0.toNat < sz32.toNat ∧ 1 ≤ i.toNat ∧ i.toNat ≤ sz32.toNat)
              (fun (_, _, i, ()) _ => sz32.toNat - i.toNat)
              (fun J1 hLoop1 => by
                m6_steps; exact hLoop1 (0#32, r0, 1#32, ()) mL
                  ⟨rfl, by simp; omega, by decide, by simp; omega⟩)
              (fun J1 (i0, r0c, i, ()) _ ⟨rfl, hi0_lt, hi1, hi_le⟩ hLoop1 => ?_)
            m6_split
            · have hi_lt : i.toNat < sz32.toNat := by c0_bound
              have hi_next : (i + 1#32).toNat = i.toNat + 1 := bv32_add1_lt (by omega)
              have hpi_eq : (p + 3#64 + i.setWidth 64).toNat = p.toNat + 3 + i.toNat :=
                bv64_add3_zext_lt (by omega)
              have hpi_lt : (p + 3#64 + i.setWidth 64).toNat < arL.length := by omega
              have hli_lt : (arL[(p + 3#64 + i.setWidth 64).toNat]'hpi_lt).toNat <
                  2 * s.core.cur_vars := by
                have h1 : arL[(p + 3#64 + i.setWidth 64).toNat]'hpi_lt =
                    arL[p.toNat + 3 + i.toNat]'(by omega) := by simp only [hpi_eq]
                have := rw_lit_lt (k := sL.core) (by change _ ≤ arL.length; omega)
                  hwL hp_ref hp_no.2 hsz_eq.symm hi_lt
                rw [List.getElem?_eq_getElem (by omega : p.toNat + 3 + i.toNat < arL.length),
                  Option.getD_some] at this; rwa [h1]
              m6_steps; c0_call hrank
              have hli_v : (arL[(p + 3#64 + i.setWidth 64).toNat]'hpi_lt).toNat <
                  s.core.vals.length := by rw [hv_len]; omega
              have hli_lv : (arL[(p + 3#64 + i.setWidth 64).toNat]'hpi_lt).toNat / 2 <
                  s.core.lvl.length := by rw [hl_len]; omega
              refine ⟨s.core.vals, s.core.lvl, FullValsLvlRest c sL ⋆ R,
                by simpa using hli_v, by simpa using hli_lv, focus_full_vals_lvl hmL, fun rk => ?_⟩
              m6_steps
              · exact hLoop1 (i, rk, i + 1#32, ()) mL (by dsimp only; rw [hi_next]; omega)
                  ⟨rfl, hi_lt, by rw [hi_next]; omega, by rw [hi_next]; omega⟩
              · exact hLoop1 (i0, r0c, i + 1#32, ()) mL (by dsimp only; rw [hi_next]; omega)
                  ⟨rfl, hi0_lt, by rw [hi_next]; omega, by rw [hi_next]; omega⟩
            · clear hLoop1 J1
              m6_to_group
              refine wp_join_group (RewatchRangeSwapInv c F0 F_cur s sL R p sz32) ?_ ?_
              · rintro _ ⟨⟩ m1 ⟨ar1, har1, hw1, hrefs1, hno1, hsz1, hnd1, hm1⟩
                clear hwL hrefsL hnoL hndL hp_ref hp_no hpwf harL_len hp3_eq hp3_lt hl0_lt hl0_v
                  hl0_lv r0 hmL
                let s1 : FullState := { sL with core := { sL.core with arena := ar1 } }
                have hp_ref1 : p.toNat ∈ fullArenaClauseRefsCore s1.core := by
                  change p.toNat ∈ fullArenaClauseRefs s1; rw [hrefs1]; exact hp_ref0
                have hp4_eq : (p + 4#64).toNat = p.toNat + 4 := bv64_add4_lt (by omega)
                have hp4_lt : (p + 4#64).toNat < ar1.length := by omega
                have hl1_lt : (ar1[(p + 4#64).toNat]'hp4_lt).toNat <
                    2 * s.core.cur_vars := by
                  have h1 : ar1[(p + 4#64).toNat]'hp4_lt = ar1[p.toNat + 4]'(by omega) := by
                    simp only [hp4_eq]
                  have := rw_lit_lt (k := s1.core) (by change _ ≤ ar1.length; omega)
                    hw1 hp_ref1 (hno1 _ hp_ref0).2 hsz1 (j := 1) (by omega)
                  rw [show p.toNat + 3 + 1 = p.toNat + 4 by omega,
                    List.getElem?_eq_getElem (by omega : p.toNat + 4 < ar1.length),
                    Option.getD_some] at this; rwa [h1]
                m6_steps; c0_call hrank
                have hl1_v : (ar1[(p + 4#64).toNat]'hp4_lt).toNat < s.core.vals.length := by
                  rw [hv_len]; omega
                have hl1_lv : (ar1[(p + 4#64).toNat]'hp4_lt).toNat / 2 < s.core.lvl.length := by
                  rw [hl_len]; omega
                refine ⟨s.core.vals, s.core.lvl, FullValsLvlRest c s1 ⋆ R,
                  by simpa using hl1_v, by simpa using hl1_lv,
                  focus_full_vals_lvl hm1, fun r1 => ?_⟩
                m6_steps
                refine wp_loop_inv
                  (fun (i, i1, _r1, ()) m2 =>
                    m1 = m2 ∧ i1.toNat < sz32.toNat ∧ 2 ≤ i.toNat ∧ i.toNat ≤ sz32.toNat)
                  (fun (i, _, _, ()) _ => sz32.toNat - i.toNat)
                  (fun J2 hLoop2 => by
                    m6_steps; exact hLoop2 (2#32, 1#32, r1, ()) m1
                      ⟨rfl, by simp; omega, by decide, by simp; omega⟩)
                  (fun J2 (i, i1, r1c, ()) _ ⟨rfl, hi1_lt, hi2, hi_le2⟩ hLoop2 => ?_)
                m6_split
                · have hi_lt : i.toNat < sz32.toNat := by c0_bound
                  have hi_next : (i + 1#32).toNat = i.toNat + 1 := bv32_add1_lt (by omega)
                  have hpi_eq : (p + 3#64 + i.setWidth 64).toNat = p.toNat + 3 + i.toNat :=
                    bv64_add3_zext_lt (by omega)
                  have hpi_lt : (p + 3#64 + i.setWidth 64).toNat < ar1.length := by omega
                  have hli_lt : (ar1[(p + 3#64 + i.setWidth 64).toNat]'hpi_lt).toNat <
                      2 * s.core.cur_vars := by
                    have h1 : ar1[(p + 3#64 + i.setWidth 64).toNat]'hpi_lt =
                        ar1[p.toNat + 3 + i.toNat]'(by omega) := by simp only [hpi_eq]
                    have := rw_lit_lt (k := s1.core) (by change _ ≤ ar1.length; omega)
                      hw1 hp_ref1 (hno1 _ hp_ref0).2 hsz1 hi_lt
                    rw [List.getElem?_eq_getElem (by omega : p.toNat + 3 + i.toNat < ar1.length),
                      Option.getD_some] at this; rwa [h1]
                  m6_steps; c0_call hrank
                  have hli_v : (ar1[(p + 3#64 + i.setWidth 64).toNat]'hpi_lt).toNat <
                      s.core.vals.length := by rw [hv_len]; omega
                  have hli_lv : (ar1[(p + 3#64 + i.setWidth 64).toNat]'hpi_lt).toNat / 2 <
                      s.core.lvl.length := by rw [hl_len]; omega
                  refine ⟨s.core.vals, s.core.lvl, FullValsLvlRest c s1 ⋆ R,
                    by simpa using hli_v, by simpa using hli_lv,
                    focus_full_vals_lvl hm1, fun rk => ?_⟩
                  m6_steps
                  · exact hLoop2 (i + 1#32, i, rk, ()) m1 (by dsimp only; rw [hi_next]; omega)
                      ⟨rfl, hi_lt, by rw [hi_next]; omega, by rw [hi_next]; omega⟩
                  · exact hLoop2 (i + 1#32, i1, r1c, ()) m1 (by dsimp only; rw [hi_next]; omega)
                      ⟨rfl, hi1_lt, by rw [hi_next]; omega, by rw [hi_next]; omega⟩
                · clear hLoop2 J2 hrank
                  m6_split
                  · have hpi1_eq : (p + 3#64 + i1.setWidth 64).toNat = p.toNat + 3 + i1.toNat :=
                      bv64_add3_zext_lt (by omega)
                    have hpi1_lt : (p + 3#64 + i1.setWidth 64).toNat < ar1.length := by omega
                    m6_steps
                    obtain ⟨har2, hw2, hrefs2, hno2, hsz2, hnd2⟩ :=
                      rw_swap_step hlenL hp_ref0 hsz_fit2 hal_le har1 hw1 hrefs1 hno1 hsz1 hnd1
                        (a := 1) (b := i1.toNat) (by omega) hi1_lt
                    let ar2 :=
                      (ar1.set (p.toNat + 3 + 1) (ar1[p.toNat + 3 + i1.toNat]'(by omega))).set
                        (p.toNat + 3 + i1.toNat) (ar1[p.toNat + 3 + 1]'(by omega))
                    have hp31_eq : (p + 4#64).toNat = p.toNat + 3 + 1 := bv64_add4_lt (by omega)
                    exact hJA () m ⟨ar2, har2, hw2, hrefs2, hno2, hsz2, hnd2,
                      full_mem_cast_rw hm (by
                        congr 2; exact list_swap_eq_idx hp31_eq hpi1_eq _ _ _ _)⟩
                  · m6_steps
                    exact hJA () m1 ⟨ar1, har1, hw1, hrefs1, hno1, hsz1, hnd1, hm1⟩
              · intro J1s hJ1s
                clear hrank r0 hl0_lt hp_no hpwf
                m6_split
                · have hpi0_eq : (p + 3#64 + i0.setWidth 64).toNat = p.toNat + 3 + i0.toNat :=
                    bv64_add3_zext_lt (by omega)
                  have hpi0_lt : (p + 3#64 + i0.setWidth 64).toNat < arL.length := by omega
                  m6_steps
                  obtain ⟨har1, hw1, hrefs1, hno1, hsz1, hnd1⟩ :=
                    rw_swap_step hlenL hp_ref0 hsz_fit2 hal_le harL_len hwL hrefsL hnoL
                      hsz_eq.symm hndL (a := 0) (b := i0.toNat) (by omega) hi0_lt
                  let ar1 :=
                    (arL.set (p.toNat + 3) (arL[p.toNat + 3 + i0.toNat]'(by omega))).set
                      (p.toNat + 3 + i0.toNat) (arL[p.toNat + 3]'(by omega))
                  exact hJ1s () m ⟨ar1, har1, hw1, hrefs1, hno1, hsz1, hnd1,
                    full_mem_cast_rw hm (by
                      congr 2; exact list_swap_eq_idx hp3_eq hpi0_eq _ _ _ _)⟩
                · m6_steps
                  exact hJ1s () mL ⟨arL, harL_len, hwL, hrefsL, hnoL, hsz_eq.symm, hndL, hmL⟩
          · m6_steps; exact hJA () mL ⟨arL, harL_len, hwL, hrefsL, hnoL, hsz_eq.symm, hndL, hmL⟩
    · m6_steps
      exact hQ true arL wvecL wstkL wlenL wuL s.core.oom wsL mL hlenL hwL hndL hrefsL
        (fun h => Bool.noConfusion h) (fun _ => rfl) hmL

theorem full_rewatch_arena_m6_wp (Γ : Env)
    (hRange : ∀ a m Q X, fullRewatchRangeSpec a m Q X →
      Γ "full_rewatch_range_m6" [i64, i64, i64] [.bool] a m Q X) :
    ∀ a m Q X, fullRewatchArenaSpec a m Q X →
      Func.wp Γ full_rewatch_arena_m6_body a m Q X := by
  rintro ⟨h, dst, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm0, hdst_eq, hno_sg, hm, hQ⟩
  m6_steps; c0_call hRange
  exact ⟨c, F0, F_cur, s, R, rfl, hlen, Nat.zero_le _,
    fun hpos => fullArenaClauseRefs_zero_mem hw.arena hpos, hdst_eq, hw, hdm0,
    fun r hr => ⟨(hno_sg r hr).2, (hno_sg r hr).1⟩, hm, hQ⟩

theorem full_rewatch_arena_wp (Γ : Env)
    (hSub : ∀ a m Q X, fullRewatchArenaSpec a m Q X →
      Γ "full_rewatch_arena_m6" [i64, i64] [.bool] a m Q X) :
    ∀ a m Q X, fullRewatchArenaSpec a m Q X →
      Func.wp Γ full_rewatch_arena_body a m Q X := by
  intro ⟨_, _, ⟨⟩⟩ _ _ _ hs; unfold Func.wp full_rewatch_arena_body
  c0_hsteps; c0_call hSub; rwa [collect_fwd1_rw]

end

end LeanQbe.T.Examples.Kissat.Proof.Collect
