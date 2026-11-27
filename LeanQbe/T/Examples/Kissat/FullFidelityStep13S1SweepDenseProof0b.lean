/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1SweepDense
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1Spec
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas
import LeanQbe.T.Examples.Kissat.FullReduceLemmas1
import LeanQbe.T.Examples.Kissat.FullReduceLemmas3
import LeanQbe.T.Examples.Kissat.FullSpec1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 Shard S1-A Proofs — Part 0b (`full_watch_large_clauses_fid`)

Parametric `(Γ : Env)` proof (`public section`, `0` `@[expose]`, `0` `import all`,
`<= 100` cols, `< 1,400` LOC, every theorem `<= 420` lines):
1. `full_watch_large_clauses_fid_s13_wp` (`step13WatchLargeClausesSpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S1

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open FullReduceHelpers
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

local macro "s13a0b_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

private theorem m6_getElem_congr {α : Type} {xs : List α} {i j : Nat} (h : i = j)
    (hi : i < xs.length) (hj : j < xs.length) : xs[i]'hi = xs[j]'hj := by
  subst h; rfl

private theorem s13_rewatch_body_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sL : FullState} {p sz : Nat} {ar0 ar1 : List (BitVec 32)}
    (hlenL : sL.LengthsOk c) (hp_ref0 : p ∈ fullArenaClauseRefs s) (har0 : ar0.length = c.arena_cap)
    (hw0 : FullWitnessInv c F0 F_cur { sL.core with arena := ar0 })
    (hrefs0 : fullArenaClauseRefs { sL with core := { sL.core with arena := ar0 } } =
      fullArenaClauseRefs s)
    (hgarb0 : fullArenaClauseGarb { sL with core := { sL.core with arena := ar0 } } p = false)
    (hsz0 : fullArenaClauseSize { sL with core := { sL.core with arena := ar0 } } p = sz)
    (hnd0 : FullArenaVarsNodup { sL with core := { sL.core with arena := ar0 } })
    (har1 : ar1.length = c.arena_cap)
    (hout : OutsideSliceAgrees (p + 1) (p + 3 + sz) ar0 ar1) (h2eq : ar1[p + 2]? = ar0[p + 2]?)
    (hperm : List.Perm (fullArenaClauseLitsCore { sL.core with arena := ar1 } p)
      (fullArenaClauseLitsCore { sL.core with arena := ar0 } p)) :
    let s1 : FullState := { sL with core := { sL.core with arena := ar1 } }
    ar1.length = c.arena_cap ∧ s1.LengthsOk c ∧ FullWitnessInv c F0 F_cur s1.core ∧
    fullArenaClauseRefs s1 = fullArenaClauseRefs s ∧ p ∈ fullArenaClauseRefsCore s1.core ∧
    fullArenaClauseGarb s1 p = false ∧
    fullArenaClauseSize s1 p = sz ∧ FullArenaVarsNodup s1 := by
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
    hrefs1.trans hrefs0, by rw [hrefs1]; exact href0, ?_, hsz1.trans hsz0, ?_⟩
  · change fullArenaClauseGarbCore s1.core p = false
    rw [(hmeta1 p href0).2.2]; exact hgarb0
  · intro r hr hng
    have hr0 : r ∈ fullArenaClauseRefsCore s0.core := by
      change r ∈ fullArenaClauseRefsCore s1.core at hr; rw [hrefs1] at hr; exact hr
    by_cases hrp : r = p
    · subst r; exact (hperm.map (· / 2)).nodup_iff.mpr (hnd0 p href0 hgarb0)
    · change ((fullArenaClauseLitsCore s1.core r).map (· / 2)).Nodup; rw [hlits_oth1 r hr0 hrp]
      exact hnd0 r hr0 (by change fullArenaClauseGarbCore s0.core r = false
                           rw [← (hmeta1 r hr0).2.2]; exact hng)

private theorem s13_rewatch_swap_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sL : FullState} {p sz a b : Nat} {ar0 : List (BitVec 32)}
    (hlenL : sL.LengthsOk c) (hp_ref0 : p ∈ fullArenaClauseRefs s)
    (hsz_fit : p + 3 + sz ≤ sL.core.arena_len) (hal_le : sL.core.arena_len ≤ c.arena_cap)
    (har0 : ar0.length = c.arena_cap)
    (hw0 : FullWitnessInv c F0 F_cur { sL.core with arena := ar0 })
    (hrefs0 : fullArenaClauseRefs { sL with core := { sL.core with arena := ar0 } } =
      fullArenaClauseRefs s)
    (hgarb0 : fullArenaClauseGarb { sL with core := { sL.core with arena := ar0 } } p = false)
    (hsz0 : fullArenaClauseSize { sL with core := { sL.core with arena := ar0 } } p = sz)
    (hnd0 : FullArenaVarsNodup { sL with core := { sL.core with arena := ar0 } })
    (ha : a < sz) (hb : b < sz) :
    let pa := p + 3 + a; let pb := p + 3 + b
    let ar1 := (ar0.set pa (ar0[pb]'(by omega))).set pb (ar0[pa]'(by omega))
    let s1 : FullState := { sL with core := { sL.core with arena := ar1 } }
    ar1.length = c.arena_cap ∧ FullWitnessInv c F0 F_cur s1.core ∧
    fullArenaClauseRefs s1 = fullArenaClauseRefs s ∧
    fullArenaClauseGarb s1 p = false ∧
    fullArenaClauseSize s1 p = sz ∧ FullArenaVarsNodup s1 := by
  intro pa pb ar1 s1
  have h2eq : ar1[p + 2]? = ar0[p + 2]? := by
    dsimp only [ar1, pa, pb]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  have hsz1 : fullArenaClauseSizeCore s1.core p = sz := by
    unfold fullArenaClauseSizeCore s1; rw [h2eq]; exact hsz0
  have hperm : List.Perm (fullArenaClauseLitsCore s1.core p)
      (fullArenaClauseLitsCore { sL.core with arena := ar0 } p) := by
    unfold fullArenaClauseLitsCore; rw [hsz1, show fullArenaClauseSizeCore _ p = sz from hsz0]
    exact swapClauseLits_perm ha hb (by omega)
  obtain ⟨h1, _, h3, h4, _, h6, h7, h8⟩ := s13_rewatch_body_step hlenL hp_ref0 har0 hw0 hrefs0
    hgarb0 hsz0 hnd0 (ar1 := ar1) (by simp [ar1, har0])
    (fun idx hidx => by
      dsimp only [ar1, pa, pb]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)])
    h2eq hperm
  exact ⟨h1, h3, h4, h6, h7, h8⟩

private theorem s13_rewatch_lit_lt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} {p sz : Nat} (hsz_fit : p + 3 + sz ≤ k.arena.length)
    (hw : FullWitnessInv c F0 F_cur k) (href : p ∈ fullArenaClauseRefsCore k)
    (hng : fullArenaClauseGarbCore k p = false) (hsz : fullArenaClauseSizeCore k p = sz)
    {j : Nat} (hj : j < sz) : (k.arena[p + 3 + j]?.getD 0#32).toNat < 2 * k.cur_vars := by
  have hbd : p + 3 + fullArenaClauseSizeCore k p ≤ k.arena.length := by rw [hsz]; omega
  have hmem := (mem_fullArenaClauseLitsCore_iff hbd).mpr ⟨j, by rw [hsz]; exact hj, rfl⟩
  have hlt := hw.arena.lits_lt p href hng _ hmem
  rwa [List.getElem?_eq_getElem (by omega : p + 3 + j < k.arena.length), Option.getD_some]

private theorem s13_rewatch_set_saved_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sL : FullState} {p : BitVec 64} {sz : Nat} {arA : List (BitVec 32)}
    (hlenL : sL.LengthsOk c) (hp_ref0 : p.toNat ∈ fullArenaClauseRefs s)
    (hsz_fit : p.toNat + 3 + sz ≤ sL.core.arena_len) (hal_le : sL.core.arena_len ≤ c.arena_cap)
    (harA : arA.length = c.arena_cap)
    (hwA : FullWitnessInv c F0 F_cur { sL.core with arena := arA })
    (hrefsA : fullArenaClauseRefs { sL with core := { sL.core with arena := arA } } =
      fullArenaClauseRefs s)
    (hgarbA : fullArenaClauseGarb { sL with core := { sL.core with arena := arA } } p.toNat =
      false)
    (hszA : fullArenaClauseSize { sL with core := { sL.core with arena := arA } } p.toNat = sz)
    (hndA : FullArenaVarsNodup { sL with core := { sL.core with arena := arA } })
    (hp1_eq : (p + 1#64).toNat = p.toNat + 1) :
    let arB := arA.set (p + 1#64).toNat 2#32
    let sB : FullState := { sL with core := { sL.core with arena := arB } }
    arB.length = c.arena_cap ∧ sB.LengthsOk c ∧ FullWitnessInv c F0 F_cur sB.core ∧
    fullArenaClauseRefs sB = fullArenaClauseRefs s ∧ p.toNat ∈ fullArenaClauseRefsCore sB.core ∧
    FullArenaVarsNodup sB := by
  intro arB sB
  have h2eq : arB[p.toNat + 2]? = arA[p.toNat + 2]? := List.getElem?_set_ne (by omega)
  have hszA' : fullArenaClauseSizeCore { sL.core with arena := arA } p.toNat = sz := hszA
  have hszB : fullArenaClauseSizeCore sB.core p.toNat = sz := by
    unfold fullArenaClauseSizeCore sB; rw [h2eq]; exact hszA'
  have hlitsB : fullArenaClauseLitsCore sB.core p.toNat =
      fullArenaClauseLitsCore { sL.core with arena := arA } p.toNat :=
    fullArenaClauseLitsCore_eq_of_hold
      (by rw [hszA']; change p.toNat + 3 + sz ≤ arA.length; omega)
      (by rw [hszA']; change p.toNat + 3 + sz ≤ arB.length
          have harB' : arB.length = c.arena_cap := by simp [arB, harA]
          omega)
      (hszB.trans hszA'.symm) (fun j _ => List.getElem?_set_ne (by omega))
  obtain ⟨h1, h2, h3, h4, h5, _, _, h8⟩ := s13_rewatch_body_step hlenL hp_ref0 harA hwA hrefsA
    hgarbA hszA hndA (ar1 := arB) (by simp [arB, harA])
    (fun idx hidx => List.getElem?_set_ne (by omega)) h2eq (hlitsB ▸ List.Perm.refl _)
  exact ⟨h1, h2, h3, h4, h5, h8⟩

private theorem s13_rewatch_push_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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
    (hokf : ok = false →
      lit.toNat < 2 * k.cur_vars →
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

private theorem s13_swap_list_eq {α : Type} {xs : List α} {i j i' j' : Nat}
    (hi : i = i') (hj : j = j') (hi_lt : i < xs.length) (hj_lt : j < xs.length)
    (hi'_lt : i' < xs.length) (hj'_lt : j' < xs.length) :
    (xs.set i (xs[j]'hj_lt)).set j (xs[i]'hi_lt) =
    (xs.set i' (xs[j']'hj'_lt)).set j' (xs[i']'hi'_lt) := by
  subst hi hj; rfl

private def s13WatchRankSwapExpr (c : FullCfg) (p : Val i64) (sz32 : Val i32) (JA : Cont []) :
    Expr Val Cont [] :=
  Expr.let_ (Op.mk (.add i64) (Arg.var p, Arg.imm 3, ())) (fun (p3, ()) =>
  Expr.let_ (Op.mk (.mul i64) (Arg.var p3, Arg.imm 4, ())) (fun (o3, ()) =>
  Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var o3, ())) (fun (a3, ()) =>
  Expr.load i32 (Arg.var a3) (fun l0 =>
  Expr.call (as := [i64, i64, i32]) (bs := [i64]) "full_lit_rank_m6"
    (Arg.var c.pVals, Arg.var c.pLevel, Arg.var l0, ())
    (fun (r0, ()) =>
    Expr.group (sig := [[i32, i64, i32]]) (fun J1 =>
      Blocks.cons (fun (st : Val i32 × Val i64 × Val i32 × Unit) =>
        let i0 := st.1; let r0c := st.2.1; let i := st.2.2.1;
        Expr.let_ (Op.mk (.cmp .ult i32 .bool rfl) (Arg.var i, Arg.var sz32, ()))
          (fun (b1, ()) =>
        Expr.jnz (Arg.var b1)
          (Expr.let_ (Op.mk (.add i64) (Arg.var p, Arg.imm 3, ())) (fun (p3_, ()) =>
            Expr.let_ (Op.mk (.zext 32 64) (Arg.var i, ())) (fun (i64v, ()) =>
            Expr.let_ (Op.mk (.add i64) (Arg.var p3_, Arg.var i64v, ())) (fun (pi, ()) =>
            Expr.let_ (Op.mk (.mul i64) (Arg.var pi, Arg.imm 4, ())) (fun (oi, ()) =>
            Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var oi, ())) (fun (ai, ()) =>
            Expr.load i32 (Arg.var ai) (fun li =>
            Expr.call (as := [i64, i64, i32]) (bs := [i64]) "full_lit_rank_m6"
              (Arg.var c.pVals, Arg.var c.pLevel, Arg.var li, ()) (fun (rk, ()) =>
              Expr.group (sig := [[i32, i64]]) (fun _Js =>
                Blocks.cons (fun (stJ : Val i32 × Val i64 × Unit) =>
                  Expr.let_ (Op.mk (.add i32) (Arg.var i, Arg.imm 1, ())) (fun (i1, ()) =>
                  Expr.jump J1.fst (Arg.var stJ.1, Arg.var stJ.2.1, Arg.var i1, ())))
                  Blocks.nil) (fun Js =>
                Expr.let_ (Op.mk (.cmp .ugt i64 .bool rfl) (Arg.var rk, Arg.var r0c, ()))
                  (fun (bg, ()) =>
                Expr.jnz (Arg.var bg)
                  (Expr.jump Js.fst (Arg.var i, Arg.var rk, ()))
                  (Expr.jump Js.fst (Arg.var i0, Arg.var r0c, ()))))))))))))
          (Expr.group (sig := [[]]) (fun _J1s =>
            Blocks.cons (fun _ =>
              Expr.let_ (Op.mk (.add i64) (Arg.var p, Arg.imm 4, ())) (fun (p4, ()) =>
              Expr.let_ (Op.mk (.mul i64) (Arg.var p4, Arg.imm 4, ())) (fun (o4, ()) =>
              Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var o4, ())) (fun (a4, ()) =>
              Expr.load i32 (Arg.var a4) (fun l1 =>
              Expr.call (as := [i64, i64, i32]) (bs := [i64]) "full_lit_rank_m6"
                (Arg.var c.pVals, Arg.var c.pLevel, Arg.var l1, ()) (fun (r1, ()) =>
                Expr.group (sig := [[i32, i32, i64]]) (fun J2 =>
                  Blocks.cons (fun (st2 : Val i32 × Val i32 × Val i64 × Unit) =>
                    let i := st2.1; let i1 := st2.2.1; let r1c := st2.2.2.1;
                    Expr.let_ (Op.mk (.cmp .ult i32 .bool rfl)
                      (Arg.var i, Arg.var sz32, ())) (fun (b2, ()) =>
                    Expr.jnz (Arg.var b2)
                      (Expr.let_ (Op.mk (.add i64) (Arg.var p, Arg.imm 3, ()))
                          (fun (p3_, ()) =>
                        Expr.let_ (Op.mk (.zext 32 64) (Arg.var i, ())) (fun (i64v, ()) =>
                        Expr.let_ (Op.mk (.add i64) (Arg.var p3_, Arg.var i64v, ()))
                          (fun (pi, ()) =>
                        Expr.let_ (Op.mk (.mul i64) (Arg.var pi, Arg.imm 4, ()))
                          (fun (oi, ()) =>
                        Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var oi, ()))
                          (fun (ai, ()) =>
                        Expr.load i32 (Arg.var ai) (fun li =>
                        Expr.call (as := [i64, i64, i32]) (bs := [i64]) "full_lit_rank_m6"
                          (Arg.var c.pVals, Arg.var c.pLevel, Arg.var li, ()) (fun (rk, ()) =>
                          Expr.group (sig := [[i32, i64]]) (fun _Js =>
                            Blocks.cons (fun (stJ : Val i32 × Val i64 × Unit) =>
                              Expr.let_ (Op.mk (.add i32) (Arg.var i, Arg.imm 1, ()))
                                (fun (inx, ()) =>
                              Expr.jump J2.fst
                                (Arg.var inx, Arg.var stJ.1, Arg.var stJ.2.1, ())))
                              Blocks.nil) (fun Js =>
                            Expr.let_ (Op.mk (.cmp .ugt i64 .bool rfl)
                              (Arg.var rk, Arg.var r1c, ())) (fun (bg, ()) =>
                            Expr.jnz (Arg.var bg)
                              (Expr.jump Js.fst (Arg.var i, Arg.var rk, ()))
                              (Expr.jump Js.fst (Arg.var i1, Arg.var r1c, ()))))))))))))
                      (Expr.group (sig := [[]]) (fun _J2s =>
                        Blocks.cons (fun _ => Expr.jump JA ()) Blocks.nil) (fun J2s =>
                        Expr.let_ (Op.mk (.cmp .ne i32 .bool rfl)
                          (Arg.var i1, Arg.imm 1, ())) (fun (bne1, ()) =>
                        Expr.jnz (Arg.var bne1)
                          (Expr.let_ (Op.mk (.add i64) (Arg.var p, Arg.imm 4, ()))
                            (fun (p4a, ()) =>
                          Expr.let_ (Op.mk (.mul i64) (Arg.var p4a, Arg.imm 4, ()))
                            (fun (o4a, ()) =>
                          Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var o4a, ()))
                            (fun (a4a, ()) =>
                          Expr.load i32 (Arg.var a4a) (fun t1 =>
                          Expr.let_ (Op.mk (.add i64) (Arg.var p, Arg.imm 4, ()))
                            (fun (p4b, ()) =>
                          Expr.let_ (Op.mk (.mul i64) (Arg.var p4b, Arg.imm 4, ()))
                            (fun (o4b, ()) =>
                          Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var o4b, ()))
                            (fun (a4b, ()) =>
                          Expr.let_ (Op.mk (.add i64) (Arg.var p, Arg.imm 3, ()))
                            (fun (p3a, ()) =>
                          Expr.let_ (Op.mk (.zext 32 64) (Arg.var i1, ())) (fun (i1_64, ()) =>
                          Expr.let_ (Op.mk (.add i64) (Arg.var p3a, Arg.var i1_64, ()))
                            (fun (pi1, ()) =>
                          Expr.let_ (Op.mk (.mul i64) (Arg.var pi1, Arg.imm 4, ()))
                            (fun (oi1, ()) =>
                          Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var oi1, ()))
                            (fun (ai1, ()) =>
                          Expr.load i32 (Arg.var ai1) (fun v1 =>
                          Expr.store (Arg.var v1) (Arg.var a4b)
                            (Expr.let_ (Op.mk (.add i64) (Arg.var p, Arg.imm 3, ()))
                              (fun (p3b, ()) =>
                            Expr.let_ (Op.mk (.zext 32 64) (Arg.var i1, ()))
                              (fun (i1_64b, ()) =>
                            Expr.let_ (Op.mk (.add i64) (Arg.var p3b, Arg.var i1_64b, ()))
                              (fun (pi1b, ()) =>
                            Expr.let_ (Op.mk (.mul i64) (Arg.var pi1b, Arg.imm 4, ()))
                              (fun (oi1b, ()) =>
                            Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var oi1b, ()))
                              (fun (ai1b, ()) =>
                            Expr.store (Arg.var t1) (Arg.var ai1b)
                              (Expr.jump J2s.fst ())))))))))))))))))))))
                          (Expr.jump J2s.fst ()))))))
                  Blocks.nil)
                  (fun J2 => Expr.jump J2.fst (Arg.imm 2, Arg.imm 1, Arg.var r1, ()))))))))
            Blocks.nil) (fun J1s =>
            Expr.let_ (Op.mk (.cmp .ne i32 .bool rfl) (Arg.var i0, Arg.imm 0, ()))
              (fun (bne0, ()) =>
            Expr.jnz (Arg.var bne0)
              (Expr.let_ (Op.mk (.add i64) (Arg.var p, Arg.imm 3, ())) (fun (p3a, ()) =>
              Expr.let_ (Op.mk (.mul i64) (Arg.var p3a, Arg.imm 4, ())) (fun (o3a, ()) =>
              Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var o3a, ())) (fun (a3a, ()) =>
              Expr.load i32 (Arg.var a3a) (fun t0 =>
              Expr.let_ (Op.mk (.add i64) (Arg.var p, Arg.imm 3, ())) (fun (p3b, ()) =>
              Expr.let_ (Op.mk (.mul i64) (Arg.var p3b, Arg.imm 4, ())) (fun (o3b, ()) =>
              Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var o3b, ())) (fun (a3b, ()) =>
              Expr.let_ (Op.mk (.add i64) (Arg.var p, Arg.imm 3, ())) (fun (p3c, ()) =>
              Expr.let_ (Op.mk (.zext 32 64) (Arg.var i0, ())) (fun (i0_64, ()) =>
              Expr.let_ (Op.mk (.add i64) (Arg.var p3c, Arg.var i0_64, ())) (fun (pi0, ()) =>
              Expr.let_ (Op.mk (.mul i64) (Arg.var pi0, Arg.imm 4, ())) (fun (oi0, ()) =>
              Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var oi0, ()))
                (fun (ai0, ()) =>
              Expr.load i32 (Arg.var ai0) (fun v0 =>
              Expr.store (Arg.var v0) (Arg.var a3b)
                (Expr.let_ (Op.mk (.add i64) (Arg.var p, Arg.imm 3, ())) (fun (p3d, ()) =>
                Expr.let_ (Op.mk (.zext 32 64) (Arg.var i0, ())) (fun (i0_64b, ()) =>
                Expr.let_ (Op.mk (.add i64) (Arg.var p3d, Arg.var i0_64b, ()))
                  (fun (pi0b, ()) =>
                Expr.let_ (Op.mk (.mul i64) (Arg.var pi0b, Arg.imm 4, ())) (fun (oi0b, ()) =>
                Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var oi0b, ()))
                  (fun (ai0b, ()) =>
                Expr.store (Arg.var t0) (Arg.var ai0b) (Expr.jump J1s.fst ())))))))))))))))))))))
              (Expr.jump J1s.fst ()))))))
      Blocks.nil)
      (fun J1 => Expr.jump J1.fst (Arg.imm 0, Arg.var r0, Arg.imm 1, ())))))))

private theorem s13_watch_rank_swap_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s sL : FullState} {R : Mem 64 → Prop} {Q : Post []} {X : XPost}
    {p : BitVec 64} {sz32 : BitVec 32} {mL : Mem 64} {JA : Cont []}
    (hRank : ∀ a m Q X, fullLitRankSpec a m Q X →
      Γ "full_lit_rank_m6" [i64, i64, i32] [i64] a m Q X)
    (_hmaxv : c.max_vars < 2 * 2 ^ 28) (har_cap : c.arena_cap < 2 * 2 ^ 28)
    (hlenL : sL.LengthsOk c) (hp_ref0 : p.toNat ∈ fullArenaClauseRefs s)
    (hp_ref : p.toNat ∈ fullArenaClauseRefsCore sL.core)
    (hsz_ge3 : 3 ≤ sz32.toNat) (hsz_fit : p.toNat + 3 + sz32.toNat ≤ sL.core.arena_len)
    (hal_le : sL.core.arena_len ≤ c.arena_cap) (harL_len : sL.core.arena.length = c.arena_cap)
    (hwL : FullWitnessInv c F0 F_cur sL.core)
    (hrefsL : fullArenaClauseRefs sL = fullArenaClauseRefs s)
    (hgarbL : fullArenaClauseGarb sL p.toNat = false)
    (hsz_eq : sz32.toNat = fullArenaClauseSizeCore sL.core p.toNat)
    (hndL : FullArenaVarsNodup sL) (hmL : (FullMem c sL ⋆ R) mL)
    (hJA : ∀ (arA : List (BitVec 32)) (mA : Mem 64),
      arA.length = c.arena_cap →
      let sA : FullState := { sL with core := { sL.core with arena := arA } }
      FullWitnessInv c F0 F_cur sA.core → fullArenaClauseRefs sA = fullArenaClauseRefs s →
      fullArenaClauseGarb sA p.toNat = false → fullArenaClauseSize sA p.toNat = sz32.toNat →
      FullArenaVarsNodup sA → (FullMem c sA ⋆ R) mA → JA () mA) :
    wp Γ Q X (s13WatchRankSwapExpr c p sz32 JA) mL := by
  unfold s13WatchRankSwapExpr
  dsimp only
  have hcv_le := hlenL.core_ok.cur_vars_le
  have hv_len := hlenL.core_ok.vals_len; have hl_len := hlenL.core_ok.lvl_len
  have hp3_eq : (p + 3#64).toNat = p.toNat + 3 := by bv_omega
  have hp3_lt : (p + 3#64).toNat < sL.core.arena.length := by omega
  have hl0_lt : (sL.core.arena[(p + 3#64).toNat]'hp3_lt).toNat < 2 * sL.core.cur_vars := by
    have h1 : sL.core.arena[(p + 3#64).toNat]'hp3_lt = sL.core.arena[p.toNat + 3]'(by omega) := by
      simp only [hp3_eq]
    have := s13_rewatch_lit_lt (k := sL.core) (by omega) hwL hp_ref hgarbL hsz_eq.symm
      (j := 0) (by omega)
    rw [Nat.add_zero, List.getElem?_eq_getElem (by omega), Option.getD_some] at this; rwa [h1]
  have hv_bd : (sL.core.arena[(p + 3#64).toNat]'hp3_lt).toNat < sL.core.vals.length := by
    have := lt_of_lt_of_le hl0_lt (Nat.mul_le_mul_left 2 hcv_le); rw [hv_len]; exact this
  have hl_bd : (sL.core.arena[(p + 3#64).toNat]'hp3_lt).toNat / 2 < sL.core.lvl.length := by
    have := lt_of_lt_of_le hl0_lt (Nat.mul_le_mul_left 2 hcv_le); rw [hl_len]; omega
  have hp3_mod : (p.toNat + 3 % 2 ^ 64) % 2 ^ 64 = p.toNat + 3 := by bv_omega
  c0_hsteps_nogrp; s13a0b_call hRank
  refine ⟨sL.core.vals, sL.core.lvl, FullValsLvlRest c sL ⋆ R,
    by dsimp only [Arg.val]; rw [m6_getElem_congr (by bv_omega) _ hp3_lt]; exact hv_bd,
    by dsimp only [Arg.val]; rw [m6_getElem_congr (by bv_omega) _ hp3_lt]; exact hl_bd,
    focus_full_vals_lvl hmL, fun r0 => ?_⟩
  c0_hsteps_nogrp
  refine wp_loop_inv (ts := [i32, i64, i32])
    (fun (st : Tup Val [i32, i64, i32]) m1 =>
      mL = m1 ∧ st.1.toNat < sz32.toNat ∧ 1 ≤ st.2.2.1.toNat ∧ st.2.2.1.toNat ≤ sz32.toNat)
    (fun (st : Tup Val [i32, i64, i32]) _ => sz32.toNat - st.2.2.1.toNat)
    (fun J1 hLoop1 => by
      c0_hsteps_nogrp; exact hLoop1 (0#32, r0, 1#32, ()) mL
        ⟨rfl, by dsimp only; simp; omega, by dsimp only; decide, by dsimp only; simp; omega⟩)
    (fun J1 ⟨i0, r0c, i, ⟨⟩⟩ _ ⟨rfl, hi0_lt, hi1, hi_le⟩ hLoop1 => ?_)
  c0_hsplit
  · have hi_lt : i.toNat < sz32.toNat := hc
    have hi_next : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
    have hpi_eq : (p + 3#64 + i.setWidth 64).toNat = p.toNat + 3 + i.toNat := by bv_omega
    have hpi_lt : (p + 3#64 + i.setWidth 64).toNat < sL.core.arena.length := by
      rw [hpi_eq, harL_len]; omega
    have hli_lt : (sL.core.arena[(p + 3#64 + i.setWidth 64).toNat]'hpi_lt).toNat <
        2 * sL.core.cur_vars := by
      have h1 : sL.core.arena[(p + 3#64 + i.setWidth 64).toNat]'hpi_lt =
          sL.core.arena[p.toNat + 3 + i.toNat]'(by omega) := by simp only [hpi_eq]
      have := s13_rewatch_lit_lt (k := sL.core) (by omega) hwL hp_ref hgarbL hsz_eq.symm hi_lt
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at this; rwa [h1]
    have hv_bd1 : (sL.core.arena[(p + 3#64 + i.setWidth 64).toNat]'hpi_lt).toNat <
        sL.core.vals.length := by
      have := lt_of_lt_of_le hli_lt (Nat.mul_le_mul_left 2 hcv_le); rw [hv_len]; exact this
    have hl_bd1 : (sL.core.arena[(p + 3#64 + i.setWidth 64).toNat]'hpi_lt).toNat / 2 <
        sL.core.lvl.length := by
      have := lt_of_lt_of_le hli_lt (Nat.mul_le_mul_left 2 hcv_le); rw [hl_len]; omega
    have hpi_mod : (p.toNat + 3 % 2 ^ 64) % 2 ^ 64 + i.toNat % 2 ^ 64 =
        p.toNat + 3 + i.toNat := by bv_omega
    c0_hsteps_nogrp; s13a0b_call hRank
    refine ⟨sL.core.vals, sL.core.lvl, FullValsLvlRest c sL ⋆ R,
      by dsimp only [Arg.val]; rw [m6_getElem_congr (by bv_omega) _ hpi_lt]; exact hv_bd1,
      by dsimp only [Arg.val]; rw [m6_getElem_congr (by bv_omega) _ hpi_lt]; exact hl_bd1,
      focus_full_vals_lvl hmL, fun rk => ?_⟩
    c0_hsteps_nogrp
    refine wp_join_group (ts := [i32, i64])
      (fun (i0', _) m1 => m1 = mL ∧ i0'.toNat < sz32.toNat)
      (fun _ ⟨i0', r0', ⟨⟩⟩ m1 ⟨hm_eq, hi0'_lt⟩ => by
        subst m1; c0_hsteps_nogrp
        exact hLoop1 (i0', r0', i + 1#32, ()) mL (by dsimp only; rw [hi_next]; omega)
          ⟨rfl, hi0'_lt, by dsimp only; rw [hi_next]; omega, by dsimp only; rw [hi_next]; omega⟩)
      (fun Js hJs => by
        c0_hsteps_nogrp; c0_hsplit
        · c0_hsteps_nogrp; exact hJs (i, rk, ()) mL ⟨rfl, hi_lt⟩
        · c0_hsteps_nogrp; exact hJs (i0, r0c, ()) mL ⟨rfl, hi0_lt⟩)
  · clear hLoop1 J1
    c0_hsteps_nogrp
    refine wp_join_group (ts := []) (fun () m1 => ∃ ar1 : List (BitVec 32),
        ar1.length = c.arena_cap ∧
        let s1 : FullState := { sL with core := { sL.core with arena := ar1 } }
        FullWitnessInv c F0 F_cur s1.core ∧ fullArenaClauseRefs s1 = fullArenaClauseRefs s ∧
        fullArenaClauseGarb s1 p.toNat = false ∧ fullArenaClauseSize s1 p.toNat = sz32.toNat ∧
        FullArenaVarsNodup s1 ∧ (FullMem c s1 ⋆ R) m1) ?_ ?_
    · rintro _ ⟨⟩ m1 ⟨ar1, har1, hw1, hrefs1, hgarb1, hsz1, hnd1, hm1⟩
      clear hwL hrefsL hgarbL hndL hp_ref harL_len hl0_lt hv_bd hl_bd hp3_mod hp3_eq hp3_lt r0 hmL
      let s1 : FullState := { sL with core := { sL.core with arena := ar1 } }
      have hp_ref1 : p.toNat ∈ fullArenaClauseRefsCore s1.core := by
        change p.toNat ∈ fullArenaClauseRefs s1; rw [hrefs1]; exact hp_ref0
      have hp4_eq : (p + 4#64).toNat = p.toNat + 4 := by bv_omega
      have hp4_lt : (p + 4#64).toNat < ar1.length := by rw [hp4_eq, har1]; omega
      have hl1_lt : (ar1[(p + 4#64).toNat]'hp4_lt).toNat < 2 * sL.core.cur_vars := by
        have h1 : ar1[(p + 4#64).toNat]'hp4_lt = ar1[p.toNat + 4]'(by omega) := by
          simp only [hp4_eq]
        have := s13_rewatch_lit_lt (k := s1.core) (by change _ ≤ ar1.length; omega)
          hw1 hp_ref1 hgarb1 hsz1 (j := 1) (by omega)
        rw [show p.toNat + 3 + 1 = p.toNat + 4 by omega,
          List.getElem?_eq_getElem (by omega : p.toNat + 4 < ar1.length),
          Option.getD_some] at this; rwa [h1]
      have hv_bd2 : (ar1[(p + 4#64).toNat]'hp4_lt).toNat < sL.core.vals.length := by
        have := lt_of_lt_of_le hl1_lt (Nat.mul_le_mul_left 2 hcv_le); rw [hv_len]; exact this
      have hl_bd2 : (ar1[(p + 4#64).toNat]'hp4_lt).toNat / 2 < sL.core.lvl.length := by
        have := lt_of_lt_of_le hl1_lt (Nat.mul_le_mul_left 2 hcv_le); rw [hl_len]; omega
      have hp4_mod : (p.toNat + 4 % 2 ^ 64) % 2 ^ 64 = p.toNat + 4 := by bv_omega
      c0_hsteps_nogrp; s13a0b_call hRank
      refine ⟨sL.core.vals, sL.core.lvl, FullValsLvlRest c s1 ⋆ R,
        by dsimp only [Arg.val]; rw [m6_getElem_congr (by bv_omega) _ hp4_lt]; exact hv_bd2,
        by dsimp only [Arg.val]; rw [m6_getElem_congr (by bv_omega) _ hp4_lt]; exact hl_bd2,
        focus_full_vals_lvl hm1, fun r1 => ?_⟩
      c0_hsteps_nogrp
      refine wp_loop_inv (ts := [i32, i32, i64])
        (fun (st : Tup Val [i32, i32, i64]) m2 =>
          m1 = m2 ∧ st.2.1.toNat < sz32.toNat ∧ 2 ≤ st.1.toNat ∧ st.1.toNat ≤ sz32.toNat)
        (fun (st : Tup Val [i32, i32, i64]) _ => sz32.toNat - st.1.toNat)
        (fun J2 hLoop2 => by
          c0_hsteps_nogrp; exact hLoop2 (2#32, 1#32, r1, ()) m1
            ⟨rfl, by dsimp only; simp; omega, by dsimp only; decide,
             by dsimp only; simp; omega⟩)
        (fun J2 ⟨i, i1, r1c, ⟨⟩⟩ _ ⟨rfl, hi1_lt, hi2, hi_le2⟩ hLoop2 => ?_)
      c0_hsplit
      · have hi_lt : i.toNat < sz32.toNat := hc
        have hi_next : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
        have hpi_eq : (p + 3#64 + i.setWidth 64).toNat = p.toNat + 3 + i.toNat := by bv_omega
        have hpi_lt : (p + 3#64 + i.setWidth 64).toNat < ar1.length := by
          rw [hpi_eq, har1]; omega
        have hli_lt : (ar1[(p + 3#64 + i.setWidth 64).toNat]'hpi_lt).toNat <
            2 * sL.core.cur_vars := by
          have h1 : ar1[(p + 3#64 + i.setWidth 64).toNat]'hpi_lt =
              ar1[p.toNat + 3 + i.toNat]'(by omega) := by simp only [hpi_eq]
          have := s13_rewatch_lit_lt (k := s1.core)
            (by change _ ≤ ar1.length; rw [har1]; omega) hw1 hp_ref1 hgarb1 hsz1 hi_lt
          rw [List.getElem?_eq_getElem (by rw [har1]; omega), Option.getD_some] at this
          rwa [h1]
        have hv_bd3 : (ar1[(p + 3#64 + i.setWidth 64).toNat]'hpi_lt).toNat <
            sL.core.vals.length := by
          have := lt_of_lt_of_le hli_lt (Nat.mul_le_mul_left 2 hcv_le); rw [hv_len]; exact this
        have hl_bd3 : (ar1[(p + 3#64 + i.setWidth 64).toNat]'hpi_lt).toNat / 2 <
            sL.core.lvl.length := by
          have := lt_of_lt_of_le hli_lt (Nat.mul_le_mul_left 2 hcv_le); rw [hl_len]; omega
        have hpi_mod : (p.toNat + 3 % 2 ^ 64) % 2 ^ 64 + i.toNat % 2 ^ 64 =
            p.toNat + 3 + i.toNat := by bv_omega
        c0_hsteps_nogrp; s13a0b_call hRank
        refine ⟨sL.core.vals, sL.core.lvl, FullValsLvlRest c s1 ⋆ R,
          by dsimp only [Arg.val]; rw [m6_getElem_congr (by bv_omega) _ hpi_lt]; exact hv_bd3,
          by dsimp only [Arg.val]; rw [m6_getElem_congr (by bv_omega) _ hpi_lt]; exact hl_bd3,
          focus_full_vals_lvl hm1, fun rk => ?_⟩
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i32, i64])
          (fun (i1', _) m2 => m1 = m2 ∧ i1'.toNat < sz32.toNat)
          (fun _ ⟨i1', r1', ⟨⟩⟩ m2 ⟨hm_eq, hi1'_lt⟩ => by
            have hi1'_lt' : i1'.toNat < sz32.toNat := hi1'_lt
            have hi2' : 2 ≤ i.toNat := hi2
            subst m2; c0_hsteps_nogrp
            exact hLoop2 (i + 1#32, i1', r1', ()) m1 (by simp only [hi_next]; omega)
              ⟨rfl, hi1'_lt', by simp only [hi_next]; omega, by simp only [hi_next]; omega⟩)
          (fun Js hJs => by
            c0_hsteps_nogrp; c0_hsplit
            · c0_hsteps_nogrp; exact hJs (i, rk, ()) m1 ⟨rfl, hi_lt⟩
            · c0_hsteps_nogrp; exact hJs (i1, r1c, ()) m1 ⟨rfl, hi1_lt⟩)
      · clear hLoop2 J2 hRank
        c0_hsteps_nogrp
        refine wp_join_group (ts := [])
          (fun () mA => ∃ arA : List (BitVec 32), arA.length = c.arena_cap ∧
            let sA : FullState := { sL with core := { sL.core with arena := arA } }
            FullWitnessInv c F0 F_cur sA.core ∧ fullArenaClauseRefs sA = fullArenaClauseRefs s ∧
            fullArenaClauseGarb sA p.toNat = false ∧ fullArenaClauseSize sA p.toNat = sz32.toNat ∧
            FullArenaVarsNodup sA ∧ (FullMem c sA ⋆ R) mA)
          (fun _ ⟨⟩ mA ⟨arA, harA, hwA, hrefsA, hgarbA, hszA, hndA, hmA⟩ => by
            c0_hsteps_nogrp; exact hJA arA mA harA hwA hrefsA hgarbA hszA hndA hmA)
          (fun J2s hJ2s => by
            c0_hsteps_nogrp; c0_hsplit
            · have hi1_lt' : i1.toNat < sz32.toNat := hi1_lt
              have hpi1_eq : (p + 3#64 + i1.setWidth 64).toNat = p.toNat + 3 + i1.toNat := by
                bv_omega
              have hpi1_lt : (p + 3#64 + i1.setWidth 64).toNat < ar1.length := by
                rw [hpi1_eq, har1]; omega
              have hp4_c0 : (p + 4#64).toNat = p.toNat + 4 := by bv_omega
              have hpi1_c0 : (p + 3#64 + BitVec.setWidth 64 i1).toNat =
                  p.toNat + 3 + i1.toNat := by bv_omega
              c0_hsteps_nogrp
              obtain ⟨har2, hw2, hrefs2, hgarb2, hsz2, hnd2⟩ := s13_rewatch_swap_step hlenL
                hp_ref0 hsz_fit hal_le har1 hw1 hrefs1 hgarb1 hsz1 hnd1 (a := 1) (b := i1.toNat)
                (by omega) hi1_lt
              let ar2 :=
                (ar1.set (p.toNat + 3 + 1) (ar1[p.toNat + 3 + i1.toNat]'(by omega))).set
                  (p.toNat + 3 + i1.toNat) (ar1[p.toNat + 3 + 1]'(by omega))
              have hm_eq := s13_swap_list_eq (xs := ar1)
                (hp4_c0.trans (by omega : p.toNat + 4 = p.toNat + 3 + 1)) hpi1_c0
                (by rw [hp4_c0, har1]; omega) (by rw [hpi1_c0, har1]; omega)
                (by rw [har1]; omega)
                (by rw [har1]; omega)
              refine hJ2s () _ ⟨ar2, har2, hw2, hrefs2, hgarb2, hsz2, hnd2, ?_⟩
              dsimp only [ar2, s1] at *; rw [← hm_eq]; exact (by assumption)
            · c0_hsteps_nogrp
              exact hJ2s () m1 ⟨ar1, har1, hw1, hrefs1, hgarb1, hsz1, hnd1, hm1⟩)
    · intro J1s hJ1s
      clear hRank r0
      c0_hsplit
      · have hpi0_eq : (p + 3#64 + i0.setWidth 64).toNat = p.toNat + 3 + i0.toNat := by bv_omega
        have hi0_lt' : i0.toNat < sz32.toNat := hi0_lt
        have hpi0_lt : (p + 3#64 + i0.setWidth 64).toNat < sL.core.arena.length := by
          have := hsz_fit; have := hal_le; rw [hpi0_eq, harL_len]; omega
        have hp3_c0 : (p + 3#64).toNat = p.toNat + 3 := by bv_omega
        have hpi0_c0 : (p + 3#64 + BitVec.setWidth 64 i0).toNat =
            p.toNat + 3 + i0.toNat := by bv_omega
        c0_hsteps_nogrp
        obtain ⟨har1, hw1, hrefs1, hgarb1, hsz1, hnd1⟩ := s13_rewatch_swap_step hlenL hp_ref0
          hsz_fit hal_le harL_len hwL hrefsL hgarbL hsz_eq.symm hndL (a := 0) (b := i0.toNat)
          (by omega) hi0_lt
        let ar1 :=
          (sL.core.arena.set (p.toNat + 3 + 0)
            (sL.core.arena[p.toNat + 3 + i0.toNat]'(by omega))).set
            (p.toNat + 3 + i0.toNat) (sL.core.arena[p.toNat + 3 + 0]'(by omega))
        have hm_eq := s13_swap_list_eq (xs := sL.core.arena)
          (hp3_c0.trans (Nat.add_zero _).symm) hpi0_c0
          (by rw [hp3_c0, harL_len]; omega) (by rw [hpi0_c0, harL_len]; omega)
          (by rw [harL_len]; omega)
          (by rw [harL_len]; omega)
        refine hJ1s () _ ⟨ar1, har1, hw1, hrefs1, hgarb1, hsz1, hnd1, ?_⟩
        dsimp only [ar1] at *; rw [← hm_eq]; exact (by assumption)
      · c0_hsteps_nogrp
        exact hJ1s () mL ⟨sL.core.arena, harL_len, hwL, hrefsL, hgarbL, hsz_eq.symm, hndL, hmL⟩

private theorem s13_watch_ret_wp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {Q : Post []}
    (hlm : FullLitMarksClear c s) (hext : FullExtScratchOk c s)
    (hQ : ∀ (s' : FullState) (m' : Mem 64),
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
      s'.core.dense_mode = s.core.dense_mode → s'.core.arena_len = s.core.arena_len →
      s'.core.vals = s.core.vals → s'.core.lvl = s.core.lvl →
      s'.core.flags = s.core.flags → s'.core.fuel = s.core.fuel →
      s'.core.inconsistent = s.core.inconsistent → s'.core.d_cur = s.core.d_cur →
      s'.core.d_val = s.core.d_val → s'.scratch.extend_len = s.scratch.extend_len →
      s'.scratch.walk_vals = s.scratch.walk_vals →
      s'.scratch.walk_best = s.scratch.walk_best →
      s'.scratch.last_learned = s.scratch.last_learned → (FullMem c s' ⋆ R) m' → Q () m')
    (ar' wvec' wstk' ws' : List (BitVec 32)) (wlen' : Nat) (wu' oom' : BitVec 64)
    (m' : Mem 64) :
    let s' : FullState :=
      { s with
        core := { s.core with arena := ar', wvec := wvec', wstk := wstk',
                              wlen := wlen', wusable := wu', oom := oom' }
        scratch := { s.scratch with wsort := ws' } }
    s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → FullArenaVarsNodup s' →
    fullArenaClauseRefs s' = fullArenaClauseRefs s → (FullMem c s' ⋆ R) m' → Q () m' := by
  intro s' hlen' hw' hnd' hrefs' hm'
  have hll_wf : FullLastLearnedWf s' := fun i hi => by
    change s.scratch.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
      (s.scratch.last_learned[i]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefs s'
    rw [hrefs']; exact hext.1 i hi
  exact hQ s' m' hlen' hw' hlm hnd' ⟨hll_wf, hext.2⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl hm'

private def s13WatchClausePostExpr (c : FullCfg) (p : Val i64) (JN : Cont []) :
    Expr Val Cont [] :=
  Expr.let_ (Op.mk (.add i64) (Arg.var p, Arg.imm 1, ())) (fun (p1, ()) =>
  Expr.let_ (Op.mk (.mul i64) (Arg.var p1, Arg.imm 4, ())) (fun (o1, ()) =>
  Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var o1, ())) (fun (a1, ()) =>
  Expr.store (t := i32) (Arg.imm 2) (Arg.var a1)
    (Expr.let_ (Op.mk (.add i64) (Arg.var p, Arg.imm 3, ())) (fun (p3, ()) =>
    Expr.let_ (Op.mk (.mul i64) (Arg.var p3, Arg.imm 4, ())) (fun (o3, ()) =>
    Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var o3, ())) (fun (a3, ()) =>
    Expr.load i32 (Arg.var a3) (fun l0 =>
    Expr.let_ (Op.mk (.add i64) (Arg.var p, Arg.imm 4, ())) (fun (p4, ()) =>
    Expr.let_ (Op.mk (.mul i64) (Arg.var p4, Arg.imm 4, ())) (fun (o4, ()) =>
    Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var o4, ())) (fun (a4, ()) =>
    Expr.load i32 (Arg.var a4) (fun l1 =>
    Expr.group (sig := [[]]) (fun _Joom =>
      Blocks.cons (fun _ =>
        Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 760, ())) (fun (po, ()) =>
        Expr.store (t := i64) (Arg.imm 1) (Arg.var po) (Expr.ret ()))) Blocks.nil)
      (fun Joom =>
        Expr.let_ (Op.mk (.and i32) (Arg.var l1, Arg.imm 2147483647, ())) (fun (m1, ()) =>
        Expr.let_ (Op.mk (.trunc 64 32) (Arg.var p, ())) (fun (p32a, ()) =>
        Expr.call (as := [i64, i32, i32, i32, i32]) (bs := [.bool]) "full_watch_push_m6"
          (Arg.var c.hdr, Arg.var l0, Arg.var m1, Arg.var p32a, Arg.imm 2, ())
          (fun (ok1, ()) =>
          Expr.jnz (Arg.var ok1)
            (Expr.let_ (Op.mk (.and i32) (Arg.var l0, Arg.imm 2147483647, ())) (fun (m0, ()) =>
            Expr.let_ (Op.mk (.trunc 64 32) (Arg.var p, ())) (fun (p32b, ()) =>
            Expr.call (as := [i64, i32, i32, i32, i32]) (bs := [.bool]) "full_watch_push_m6"
              (Arg.var c.hdr, Arg.var l1, Arg.var m0, Arg.var p32b, Arg.imm 2, ())
              (fun (ok2, ()) =>
              Expr.jnz (Arg.var ok2) (Expr.jump JN ()) (Expr.jump Joom.fst ())))))
            (Expr.jump Joom.fst ())))))))))))))))))

private abbrev s13WatchSt (s : FullState) (ar wvec wstk ws : List (BitVec 32))
    (wlen : Nat) (wu oom : BitVec 64) : FullState :=
  { s with
    core := { s.core with arena := ar, wvec := wvec, wstk := wstk,
                          wlen := wlen, wusable := wu, oom := oom }
    scratch := { s.scratch with wsort := ws } }

private theorem s13_watch_lengths_with_arena {c : FullCfg} {s : FullState}
    {arL arA wvecL wstkL wsL : List (BitVec 32)} {wlenL : Nat} {wuL oomL : BitVec 64}
    (hlen : (s13WatchSt s arL wvecL wstkL wsL wlenL wuL oomL).LengthsOk c)
    (har : arA.length = c.arena_cap) :
    (s13WatchSt s arA wvecL wstkL wsL wlenL wuL oomL).LengthsOk c :=
  ⟨⟨hlen.core_ok.vals_len, hlen.core_ok.lit_mark_len, hlen.core_ok.mrk_len,
    hlen.core_ok.flags_len, hlen.core_ok.lvl_len, hlen.core_ok.rsns_len, hlen.core_ok.trl_len,
    hlen.core_ok.trail_pos_len, hlen.core_ok.tmp_len_arr, hlen.core_ok.min_clr_len_arr,
    hlen.core_ok.frame_trail_len, hlen.core_ok.frame_dec_len, hlen.core_ok.wvec_len,
    hlen.core_ok.repr_len, hlen.core_ok.min_stk_len, har, hlen.core_ok.wstk_len_arr,
    hlen.core_ok.cur_vars_ge, hlen.core_ok.cur_vars_le, hlen.core_ok.arena_len_le,
    hlen.core_ok.wlen_le, hlen.core_ok.trail_end_le, hlen.core_ok.propagated_le,
    hlen.core_ok.tmp_len_le, hlen.core_ok.min_clr_len_le⟩, hlen.scratch_ok⟩

private theorem s13_watch_clause_post_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop} {Q : Post []} {X : XPost}
    {p : BitVec 64} {sz32 : BitVec 32} {arA wvecL wstkL wsL : List (BitVec 32)}
    {wlenL : Nat} {wuL oomL : BitVec 64} {mA : Mem 64} {JN : Cont []}
    (hPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push_m6" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hlenA : (s13WatchSt s arA wvecL wstkL wsL wlenL wuL oomL).LengthsOk c)
    (hlm : FullLitMarksClear c s) (hext : FullExtScratchOk c s)
    (hQ : ∀ (s' : FullState) (m' : Mem 64),
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
      s'.core.dense_mode = s.core.dense_mode → s'.core.arena_len = s.core.arena_len →
      s'.core.vals = s.core.vals → s'.core.lvl = s.core.lvl →
      s'.core.flags = s.core.flags → s'.core.fuel = s.core.fuel →
      s'.core.inconsistent = s.core.inconsistent → s'.core.d_cur = s.core.d_cur →
      s'.core.d_val = s.core.d_val → s'.scratch.extend_len = s.scratch.extend_len →
      s'.scratch.walk_vals = s.scratch.walk_vals →
      s'.scratch.walk_best = s.scratch.walk_best →
      s'.scratch.last_learned = s.scratch.last_learned → (FullMem c s' ⋆ R) m' → Q () m')
    (hp_ref0 : p.toNat ∈ fullArenaClauseRefs s) (hsz_ge3 : 3 ≤ sz32.toNat)
    (hsz_fit : p.toNat + 3 + sz32.toNat ≤ s.core.arena_len)
    (hal_le : s.core.arena_len ≤ c.arena_cap) (harA : arA.length = c.arena_cap)
    (hdm0 : s.core.dense_mode = 0#64)
    (hwA : FullWitnessInv c F0 F_cur (s13WatchSt s arA wvecL wstkL wsL wlenL wuL oomL).core)
    (hrefsA : fullArenaClauseRefs (s13WatchSt s arA wvecL wstkL wsL wlenL wuL oomL) =
      fullArenaClauseRefs s)
    (hgarbA : fullArenaClauseGarb (s13WatchSt s arA wvecL wstkL wsL wlenL wuL oomL) p.toNat =
      false)
    (hszA : fullArenaClauseSize (s13WatchSt s arA wvecL wstkL wsL wlenL wuL oomL) p.toNat =
      sz32.toNat)
    (hndA : FullArenaVarsNodup (s13WatchSt s arA wvecL wstkL wsL wlenL wuL oomL))
    (hmA : (FullMem c (s13WatchSt s arA wvecL wstkL wsL wlenL wuL oomL) ⋆ R) mA)
    (hJN : ∀ (mN : Mem 64), (∃ arN wvecN wstkN wlenN wuN oomN wsN,
      let sN : FullState := s13WatchSt s arN wvecN wstkN wsN wlenN wuN oomN
      sN.LengthsOk c ∧ FullWitnessInv c F0 F_cur sN.core ∧
      fullArenaClauseRefs sN = fullArenaClauseRefs s ∧
      FullArenaVarsNodup sN ∧ (FullMem c sN ⋆ R) mN) → JN () mN) :
    wp Γ Q X (s13WatchClausePostExpr c p JN) mA := by
  unfold s13WatchClausePostExpr
  have harena_dim := c.harena; unfold dimacsBound at harena_dim
  have hp1_eq : (p + 1#64).toNat = p.toNat + 1 := by bv_omega
  have hp1_lt : (p + 1#64).toNat < arA.length := by rw [hp1_eq, harA]; omega
  let arB := arA.set (p + 1#64).toNat 2#32
  let sB : FullState := s13WatchSt s arB wvecL wstkL wsL wlenL wuL oomL
  obtain ⟨harB, hlenB, hwB, hrefsB_s, hrefB, hndB⟩ :=
    s13_rewatch_set_saved_step hlenA hp_ref0 hsz_fit hal_le harA hwA hrefsA hgarbA hszA hndA hp1_eq
  have harB' : arB.length = c.arena_cap := by dsimp only [arB]; rw [List.length_set, harA]
  have hp3_eq : (p + 3#64).toNat = p.toNat + 3 := by bv_omega
  have hp4_eq : (p + 4#64).toNat = p.toNat + 4 := by bv_omega
  have hp3_lt : (p + 3#64).toNat < arB.length := by rw [hp3_eq, harB']; omega
  have hp4_lt : (p + 4#64).toNat < arB.length := by rw [hp4_eq, harB']; omega
  let l0 := arB[(p + 3#64).toNat]'hp3_lt
  let l1 := arB[(p + 4#64).toNat]'hp4_lt
  have hp32_eq : (p.setWidth 32).toNat = p.toNat := by bv_omega
  have hp32_lt : (p.setWidth 32).toNat < 0x80000000 := by
    have := hal_le; have := c.harena; unfold dimacsBound at this; omega
  have hp32_ne : p.setWidth 32 ≠ 0xFFFFFFFF#32 := fun h' => by
    have := congrArg BitVec.toNat h'; simp at this; omega
  have hlw0 := bv32_large_word_props l1
  have hlw1 := bv32_large_word_props l0
  have hwB_sp : WatchesInv F_cur sB.core := modeWatchesInv_to_sparse hwB.watches hdm0
  c0_hsteps_nogrp
  refine wp_join_group (ts := [])
    (fun () mO => ∃ (wvecO wstkO wsO : List (BitVec 32)) (wlenO : Nat) (wuO : BitVec 64),
      let sO : FullState := s13WatchSt s arB wvecO wstkO wsO wlenO wuO oomL
      sO.LengthsOk c ∧ FullWitnessInv c F0 F_cur sO.core ∧
      fullArenaClauseRefs sO = fullArenaClauseRefs s ∧
      FullArenaVarsNodup sO ∧ (FullMem c sO ⋆ R) mO)
    (fun _ ⟨⟩ mO ⟨wvecO, wstkO, wsO, wlenO, wuO, hlenO, hwO, hrefsO, hndO, _⟩ => by
      let sO1 : FullState := s13WatchSt s arB wvecO wstkO wsO wlenO wuO 1#64
      have hlenO1 : sO1.LengthsOk c :=
        ⟨{ hlenO.core_ok with vals_len := hlenO.core_ok.vals_len }, hlenO.scratch_ok⟩
      c0_hsteps_nogrp
      exact s13_watch_ret_wp hlm hext hQ arB wvecO wstkO wsO wlenO wuO 1#64 _ hlenO1
        (fullWitnessInv_with_oom hwO 1#64) hndO hrefsO (by assumption))
    (fun Joom hJoom => by
      c0_hsteps_nogrp; s13a0b_call hPush
      refine ⟨c, sB, R, rfl, hlenB, hwB_sp.layout, fun h => by exfalso; revert h; decide,
        fun _ => ⟨hlw0.2, hp32_ne⟩, (by assumption), ?_⟩
      intro ok1 wvec1 wstk1 wlen1 wu1 ws1 m1 _ hlen1 hlay1 hoth1 hok1t hok1f hm1
      dsimp only [Arg.val] at hok1t hok1f
      have hw1 := s13_rewatch_push_step hwB hdm0 hlay1 hlw0.1 hp32_lt
        (by rw [hp32_eq]; exact hrefB) hoth1 hok1t
        (fun hl => by
          dsimp only [Arg.val] at hl ⊢
          simpa only [fullWatchSize, fullWatchOff] using (hok1f hl).1)
      c0_hsplit
      · let sB1 : FullState := s13WatchSt s arB wvec1 wstk1 ws1 wlen1 wu1 oomL
        c0_hsteps_nogrp; s13a0b_call hPush
        refine ⟨c, sB1, R, rfl, hlen1, hlay1, fun h => by exfalso; revert h; decide,
          fun _ => ⟨hlw1.2, hp32_ne⟩, hm1, ?_⟩
        intro ok2 wvec2 wstk2 wlen2 wu2 ws2 m2 _ hlen2 hlay2 hoth2 hok2t hok2f hm2
        dsimp only [Arg.val] at hok2t hok2f
        have hw2 := s13_rewatch_push_step hw1 hdm0 hlay2 hlw1.1 hp32_lt
          (by rw [hp32_eq]; exact hrefB) hoth2 hok2t
          (fun hl => by
            dsimp only [Arg.val] at hl ⊢
            simpa only [fullWatchSize, fullWatchOff] using (hok2f hl).1)
        c0_hsplit
        · c0_hsteps!
          exact hJN m2
            ⟨arB, wvec2, wstk2, wlen2, wu2, oomL, ws2, hlen2, hw2, hrefsB_s, hndB, hm2⟩
        · c0_hsteps!
          exact hJoom () m2
            ⟨wvec2, wstk2, ws2, wlen2, wu2, hlen2, hw2, hrefsB_s, hndB, hm2⟩
      · c0_hsteps!
        exact hJoom () m1
          ⟨wvec1, wstk1, ws1, wlen1, wu1, hlen1, hw1, hrefsB_s, hndB, hm1⟩)

private def s13WatchClauseIterExpr (c : FullCfg) (p : Val i64) (hdr sz32 : Val i32)
    (at_root : Val .bool) (JN : Cont []) : Expr Val Cont [] :=
  Expr.let_ (Op.mk (.and i32) (Arg.var hdr, Arg.imm 524288, ())) (fun (garb, ()) =>
  Expr.let_ (Op.mk (.cmp .eq i32 .bool rfl) (Arg.var garb, Arg.imm 0, ())) (fun (bg, ()) =>
  Expr.jnz (Arg.var bg)
    (Expr.let_ (Op.mk (.cmp .uge i32 .bool rfl) (Arg.var sz32, Arg.imm 3, ())) (fun (bsz, ()) =>
    Expr.jnz (Arg.var bsz)
      (Expr.let_ (Op.mk (.add i64) (Arg.var p, Arg.imm 3, ())) (fun (p3, ()) =>
      Expr.let_ (Op.mk (.zext 32 64) (Arg.var sz32, ())) (fun (sz64, ()) =>
      Expr.let_ (Op.mk (.add i64) (Arg.var p3, Arg.var sz64, ())) (fun (pend, ()) =>
      Expr.let_ (Op.mk (.add i64) (Arg.var c.hdr, Arg.imm 48, ())) (fun (pal, ()) =>
      Expr.load i64 (Arg.var pal) (fun al =>
      Expr.let_ (Op.mk (.cmp .ule i64 .bool rfl) (Arg.var pend, Arg.var al, ()))
        (fun (bfit, ()) =>
      Expr.jnz (Arg.var bfit)
        (Expr.group (sig := [[]]) (fun _JA =>
          Blocks.cons (fun _ => s13WatchClausePostExpr c p JN) Blocks.nil)
          (fun JA =>
            Expr.jnz (Arg.var at_root) (Expr.jump JA.fst ())
              (s13WatchRankSwapExpr c p sz32 JA.fst)))
        (Expr.jump JN ()))))))))
      (Expr.jump JN ())))
    (Expr.jump JN ())))

private theorem s13_watch_clause_iter_wp {Γ : Env} {Q : Post []} {X : XPost}
    (hRank : ∀ a m Q X, Full.fullLitRankSpec a m Q X →
      Γ "full_lit_rank_m6" [i64, i64, i32] [i64] a m Q X)
    (hPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push_m6" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {arL : List (BitVec 32)} {wvecL wstkL wsL : List (BitVec 32)}
    {wlenL : Nat} {wuL oomL p : BitVec 64} {at_root : Bool} {R : Mem 64 → Prop} {mL : Mem 64}
    {JN : Cont []}
    (hmaxv : c.max_vars < 2 * 2 ^ 28) (har_cap : c.arena_cap < 2 * 2 ^ 28)
    (hsL_def : ∀ sL : FullState, sL = s13WatchSt s arL wvecL wstkL wsL wlenL wuL oomL →
      sL.LengthsOk c ∧ FullWitnessInv c F0 F_cur sL.core ∧
      fullArenaClauseRefs sL = fullArenaClauseRefs s ∧ FullArenaVarsNodup sL)
    (hp_ref0 : p.toNat ∈ fullArenaClauseRefs s)
    (hp_lt_ar : p.toNat < arL.length) (hp2_eq : (p + 2#64).toNat = p.toNat + 2)
    (hp2_lt : (p + 2#64).toNat < arL.length)
    (hal_le : s.core.arena_len ≤ c.arena_cap) (harL_len : arL.length = c.arena_cap)
    (hdm0 : s.core.dense_mode = 0#64) (hlm : FullLitMarksClear c s) (hext : FullExtScratchOk c s)
    (hmL : (FullMem c (s13WatchSt s arL wvecL wstkL wsL wlenL wuL oomL) ⋆ R) mL)
    (hJN : ∀ (arN : List (BitVec 32)) wvecN wstkN (wlenN : Nat) wuN oomN wsN (mN : Mem 64),
      let sN : FullState := s13WatchSt s arN wvecN wstkN wsN wlenN wuN oomN
      sN.LengthsOk c → FullWitnessInv c F0 F_cur sN.core →
      fullArenaClauseRefs sN = fullArenaClauseRefs s → FullArenaVarsNodup sN →
      (FullMem c sN ⋆ R) mN → JN () mN)
    (hQ : ∀ (s' : FullState) (m' : Mem 64),
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
      s'.core.dense_mode = s.core.dense_mode → s'.core.arena_len = s.core.arena_len →
      s'.core.vals = s.core.vals → s'.core.lvl = s.core.lvl → s'.core.flags = s.core.flags →
      s'.core.fuel = s.core.fuel → s'.core.inconsistent = s.core.inconsistent →
      s'.core.d_cur = s.core.d_cur → s'.core.d_val = s.core.d_val →
      s'.scratch.extend_len = s.scratch.extend_len →
      s'.scratch.walk_vals = s.scratch.walk_vals →
      s'.scratch.walk_best = s.scratch.walk_best →
      s'.scratch.last_learned = s.scratch.last_learned → (FullMem c s' ⋆ R) m' → Q () m') :
    let hdr := arL[p.toNat]'hp_lt_ar
    let sz32 := arL[(p + 2#64).toNat]'hp2_lt
    wp Γ Q X (s13WatchClauseIterExpr c p hdr sz32 at_root JN) mL := by
  let sL : FullState := s13WatchSt s arL wvecL wstkL wsL wlenL wuL oomL
  obtain ⟨hlenL, hwL, hrefsL, hndL⟩ := hsL_def sL rfl
  have hp_ref : p.toNat ∈ fullArenaClauseRefsCore sL.core := by
    change p.toNat ∈ fullArenaClauseRefs sL; rw [hrefsL]; exact hp_ref0
  dsimp only [s13WatchClauseIterExpr]
  c0_hsplit
  · have hgarb_hc := hc
    c0_hsplit
    · have hsz_hc := hc
      c0_hsplit
      · have hfit_hc := hc
        let hdr := arL[p.toNat]'hp_lt_ar
        let sz32 := arL[(p + 2#64).toNat]'hp2_lt
        have hgarbL : fullArenaClauseGarb sL p.toNat = false := by
          unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
          rw [List.getElem?_eq_getElem hp_lt_ar, Option.getD_some]
          have hhdr0 : (arL[p.toNat]'hp_lt_ar &&& 0x00080000#32) = 0#32 := hgarb_hc
          rw [hhdr0]; rfl
        have hsz_eq : sz32.toNat = fullArenaClauseSizeCore sL.core p.toNat := by
          unfold fullArenaClauseSizeCore sL; dsimp only [sz32]
          rw [List.getElem?_eq_getElem (by omega : p.toNat + 2 < arL.length), Option.getD_some]
          simp only [hp2_eq]
        have hp2_c0 : (p.toNat + 2 % 2 ^ 64) % 2 ^ 64 = p.toNat + 2 := by bv_omega
        have hsz_c0 : sL.core.arena[(p.toNat + 2 % 2 ^ 64) % 2 ^ 64]'(by
            rw [hp2_c0]; dsimp only [sL]; omega) = sz32 :=
          m6_getElem_congr (hp2_c0.trans hp2_eq.symm) _ hp2_lt
        have hsz_ge3 : 3 ≤ sz32.toNat := by
          change 3 ≤ (sL.core.arena[(p.toNat + 2 % 2 ^ 64) % 2 ^ 64]'_).toNat at hsz_hc
          rw [hsz_c0] at hsz_hc; exact hsz_hc
        have hsz_fit : p.toNat + 3 + sz32.toNat ≤ s.core.arena_len := by
          have hp2_n : (p.toNat + 2) % 2 ^ 64 = p.toNat + 2 := by bv_omega
          have hsz_n : arL[(p.toNat + 2) % 2 ^ 64]'(by rw [hp2_n]; omega) = sz32 :=
            m6_getElem_congr (hp2_n.trans hp2_eq.symm) _ hp2_lt
          change (p.toNat + BitVec.toNat 3 +
              (sL.core.arena[(p.toNat + 2) % 2 ^ 64]'_).toNat) % 2 ^ 64 ≤
            s.core.arena_len % 2 ^ 64 at hfit_hc
          dsimp only [sL] at hfit_hc
          rw [hsz_n] at hfit_hc
          have := hal_le; have := har_cap; bv_omega
        c0_hsteps_nogrp
        refine wp_join_group (ts := [])
          (fun () mA => ∃ arA : List (BitVec 32), arA.length = c.arena_cap ∧
            let sA : FullState := s13WatchSt s arA wvecL wstkL wsL wlenL wuL oomL
            FullWitnessInv c F0 F_cur sA.core ∧ fullArenaClauseRefs sA = fullArenaClauseRefs s ∧
            fullArenaClauseGarb sA p.toNat = false ∧ fullArenaClauseSize sA p.toNat = sz32.toNat ∧
            FullArenaVarsNodup sA ∧ (FullMem c sA ⋆ R) mA) ?_ ?_
        · rintro _ ⟨⟩ mA ⟨arA, harA, hwA, hrefsA, hgarbA, hszA, hndA, hmA⟩
          exact s13_watch_clause_post_wp hPush (s13_watch_lengths_with_arena hlenL harA)
            hlm hext hQ hp_ref0 hsz_ge3 hsz_fit hal_le harA hdm0 hwA hrefsA hgarbA hszA hndA hmA
            (fun mN ⟨arN, wvecN, wstkN, wlenN, wuN, oomN, wsN, hlenN, hwN, hrefsN, hndN, hmN⟩ =>
              hJN arN wvecN wstkN wlenN wuN oomN wsN mN hlenN hwN hrefsN hndN hmN)
        · intro JA hJA
          c0_hsplit
          · c0_hsteps!
            exact hJA () mL ⟨arL, harL_len, hwL, hrefsL, hgarbL, hsz_eq.symm, hndL, hmL⟩
          · have hp2_c0 : (p.toNat + 2 % 2 ^ 64) % 2 ^ 64 = p.toNat + 2 := by bv_omega
            have hsz_c0 : sL.core.arena[(p.toNat + 2 % 2 ^ 64) % 2 ^ 64]'(by
                rw [hp2_c0]; dsimp only [sL]; omega) = sz32 :=
              m6_getElem_congr (hp2_c0.trans hp2_eq.symm) _ hp2_lt
            refine s13_watch_rank_swap_wp hRank hmaxv har_cap hlenL hp_ref0 hp_ref
              (sL := sL) (sz32 := sz32) hsz_ge3 hsz_fit hal_le harL_len hwL hrefsL hgarbL hsz_eq
              hndL hmL (fun arA mA harA hwA hrefsA hgarbA hszA hndA hmA =>
                hJA () mA ⟨arA, harA, hwA, hrefsA, hgarbA, hszA, hndA, hmA⟩)
      · c0_hsteps!; exact hJN arL wvecL wstkL wlenL wuL oomL wsL mL hlenL hwL hrefsL hndL hmL
    · c0_hsteps!; exact hJN arL wvecL wstkL wlenL wuL oomL wsL mL hlenL hwL hrefsL hndL hmL
  · c0_hsteps!; exact hJN arL wvecL wstkL wlenL wuL oomL wsL mL hlenL hwL hrefsL hndL hmL

private theorem s13_watch_next_join_wp {Γ : Env} {Q : Post []} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {arL arN wvecN wstkN wsN : List (BitVec 32)} {wlenN : Nat} {wuN oomN p : BitVec 64}
    {R : Mem 64 → Prop} {mN : Mem 64} {JB JL : Cont [i64]}
    (har_cap : c.arena_cap < 2 * 2 ^ 28) (hal_le : s.core.arena_len ≤ c.arena_cap)
    (hp_lt : p.toNat < s.core.arena_len) (hp_trunc : (p.setWidth 32).toNat = p.toNat)
    (hnb : fullArenaNextOff arL s.core.arena_len p.toNat ≤ s.core.arena_len)
    (hnp_eq : ((BitVec.ofNat 32 (fullArenaNextOff arL s.core.arena_len
        (p.setWidth 32).toNat)).setWidth 64).toNat = fullArenaNextOff arL s.core.arena_len p.toNat)
    (hnext_mem0 : fullArenaNextOff arL s.core.arena_len p.toNat = s.core.arena_len ∨
      fullArenaNextOff arL s.core.arena_len p.toNat ∈ fullArenaClauseRefs s)
    (hlenN : (s13WatchSt s arN wvecN wstkN wsN wlenN wuN oomN).LengthsOk c)
    (hwN : FullWitnessInv c F0 F_cur (s13WatchSt s arN wvecN wstkN wsN wlenN wuN oomN).core)
    (hrefsN : fullArenaClauseRefs (s13WatchSt s arN wvecN wstkN wsN wlenN wuN oomN) =
      fullArenaClauseRefs s)
    (hndN : FullArenaVarsNodup (s13WatchSt s arN wvecN wstkN wsN wlenN wuN oomN))
    (hmN : (FullMem c (s13WatchSt s arN wvecN wstkN wsN wlenN wuN oomN) ⋆ R) mN)
    (hJB : ∀ (bst : BitVec 64 × FullState) m', (∃ arB wvecB wstkB wlenB wuB oomB wsB,
      let sB : FullState := s13WatchSt s arB wvecB wstkB wsB wlenB wuB oomB
      bst.2 = sB ∧ sB.LengthsOk c ∧ FullWitnessInv c F0 F_cur sB.core ∧
      FullArenaVarsNodup sB ∧ fullArenaClauseRefs sB = fullArenaClauseRefs s ∧
      (FullMem c sB ⋆ R) m') → JB (bst.1, ()) m')
    (hLoopL : ∀ (st' : BitVec 64 × FullState) m',
      s.core.arena_len - st'.1.toNat < s.core.arena_len - p.toNat →
      (st'.1.toNat ≤ s.core.arena_len ∧
        (st'.1.toNat < s.core.arena_len → st'.1.toNat ∈ fullArenaClauseRefs s) ∧
        ∃ arL' wvecL' wstkL' wlenL' wuL' oomL' wsL',
          let sL' : FullState := s13WatchSt s arL' wvecL' wstkL' wsL' wlenL' wuL' oomL'
          st'.2 = sL' ∧ sL'.LengthsOk c ∧ FullWitnessInv c F0 F_cur sL'.core ∧
          fullArenaClauseRefs sL' = fullArenaClauseRefs s ∧
          FullArenaVarsNodup sL' ∧ (FullMem c sL' ⋆ R) m') →
      JL (st'.1, ()) m') :
    let np := BitVec.setWidth 64 (BitVec.ofNat 32 (fullArenaNextOff arL s.core.arena_len
      (BitVec.setWidth 32 p).toNat))
    wp Γ Q X (Expr.let_ (Op.mk (.cmp .ule i64 .bool rfl) (Arg.var np, Arg.var p, ()))
      (fun (ble, ()) => Expr.jnz (Arg.var ble) (Expr.jump JB (Arg.var p, ()))
        (Expr.jump JL (Arg.var np, ())))) mN := by
  dsimp only
  let sN : FullState := s13WatchSt s arN wvecN wstkN wsN wlenN wuN oomN
  c0_hsteps_nogrp; c0_hsplit
  · c0_hsteps_nogrp
    exact hJB (p, sN) mN ⟨arN, wvecN, wstkN, wlenN, wuN, oomN, wsN, rfl, hlenN, hwN, hndN,
      hrefsN, hmN⟩
  · have hnp_lt_32 : fullArenaNextOff arL s.core.arena_len p.toNat < 2 ^ 32 := by omega
    have hnp32_mod : fullArenaNextOff arL s.core.arena_len
        (BitVec.setWidth 32 p).toNat % 2 ^ 32 = fullArenaNextOff arL s.core.arena_len p.toNat := by
      rw [hp_trunc, Nat.mod_eq_of_lt hnp_lt_32]
    have hle_gt : p.toNat < fullArenaNextOff arL s.core.arena_len p.toNat := by
      have hle := hc
      change ¬ fullArenaNextOff arL s.core.arena_len
        (BitVec.setWidth 32 p).toNat % 2 ^ 32 ≤ p.toNat at hle
      rw [hnp32_mod] at hle; omega
    c0_hsteps_nogrp
    refine hLoopL (_, sN) mN ?_ ?_
    · change s.core.arena_len - (BitVec.setWidth 64 (BitVec.ofNat 32
          (fullArenaNextOff arL s.core.arena_len
            (BitVec.setWidth 32 p).toNat))).toNat < s.core.arena_len - p.toNat
      rw [hnp_eq]; omega
    · refine ⟨by
          dsimp only [Arg.val]
          change (BitVec.setWidth 64 (BitVec.ofNat 32
              (fullArenaNextOff arL s.core.arena_len
                (BitVec.setWidth 32 p).toNat))).toNat ≤ s.core.arena_len
          rw [hnp_eq]; omega,
        fun hlt => by
          have hnp32_eq : (BitVec.ofNat 32 (fullArenaNextOff arL s.core.arena_len
              (BitVec.setWidth 32 p).toNat)).toNat =
              fullArenaNextOff arL s.core.arena_len p.toNat := by
            have h1 := hnp_eq
            rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by
              have := BitVec.isLt (BitVec.ofNat 32 (fullArenaNextOff arL s.core.arena_len
                (BitVec.setWidth 32 p).toNat))
              omega)] at h1
            exact h1
          change (BitVec.ofNat 32 (fullArenaNextOff arL s.core.arena_len
              (BitVec.setWidth 32 p).toNat)).toNat < s.core.arena_len at hlt
          change (BitVec.ofNat 32 (fullArenaNextOff arL s.core.arena_len
              (BitVec.setWidth 32 p).toNat)).toNat ∈ fullArenaClauseRefs s
          rw [hnp32_eq] at hlt ⊢
          rcases hnext_mem0 with hend | hmem
          · rw [hend] at hlt; exact absurd hlt (Nat.lt_irrefl _)
          · exact hmem,
       arN, wvecN, wstkN, wlenN, wuN, oomN, wsN, rfl, hlenN, hwN, hrefsN, hndN, hmN⟩

private def s13WatchLoopStepExpr (c : FullCfg) (p : Val i64) (at_root : Val .bool)
    (JB JL : Cont [i64]) : Expr Val Cont [] :=
  Expr.let_ (Op.mk (.mul i64) (Arg.var p, Arg.imm 4, ())) (fun (o0, ()) =>
  Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var o0, ())) (fun (ap0, ()) =>
  Expr.load i32 (Arg.var ap0) (fun hdr =>
  Expr.let_ (Op.mk (.add i64) (Arg.var p, Arg.imm 2, ())) (fun (p2, ()) =>
  Expr.let_ (Op.mk (.mul i64) (Arg.var p2, Arg.imm 4, ())) (fun (o2, ()) =>
  Expr.let_ (Op.mk (.add i64) (Arg.var c.pArena, Arg.var o2, ())) (fun (ap2, ()) =>
  Expr.load i32 (Arg.var ap2) (fun sz32 =>
  Expr.let_ (Op.mk (.trunc 64 32) (Arg.var p, ())) (fun (p32, ()) =>
  Expr.call (as := [i64, i32]) (bs := [i32]) "full_arena_next" (Arg.var c.hdr, Arg.var p32, ())
    (fun (np32, ()) =>
    Expr.let_ (Op.mk (.zext 32 64) (Arg.var np32, ())) (fun (np, ()) =>
    Expr.group (sig := [[]]) (fun _JN =>
      Blocks.cons (fun _ =>
        Expr.let_ (Op.mk (.cmp .ule i64 .bool rfl) (Arg.var np, Arg.var p, ())) (fun (ble, ()) =>
        Expr.jnz (Arg.var ble) (Expr.jump JB (Arg.var p, ()))
          (Expr.jump JL (Arg.var np, ())))) Blocks.nil)
      (fun JN => s13WatchClauseIterExpr c p hdr sz32 at_root JN.fst)))))))))))

private theorem s13_watch_loop_step_wp {Γ : Env} {Q : Post []} {X : XPost}
    (hNext : ∀ a m Q X, Full.fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hRank : ∀ a m Q X, Full.fullLitRankSpec a m Q X →
      Γ "full_lit_rank_m6" [i64, i64, i32] [i64] a m Q X)
    (hPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push_m6" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {arL wvecL wstkL wsL : List (BitVec 32)} {wlenL : Nat} {wuL oomL p : BitVec 64}
    {at_root : Bool} {R : Mem 64 → Prop} {mL : Mem 64} {JB JL : Cont [i64]}
    (hmaxv : c.max_vars < 2 * 2 ^ 28) (har_cap : c.arena_cap < 2 * 2 ^ 28)
    (hal_le : s.core.arena_len ≤ c.arena_cap) (hdm0 : s.core.dense_mode = 0#64)
    (hlm : FullLitMarksClear c s) (hext : FullExtScratchOk c s)
    (hp_lt : p.toNat < s.core.arena_len) (hp_mem : p.toNat < s.core.arena_len →
      p.toNat ∈ fullArenaClauseRefs s)
    (hlenL : (s13WatchSt s arL wvecL wstkL wsL wlenL wuL oomL).LengthsOk c)
    (hwL : FullWitnessInv c F0 F_cur (s13WatchSt s arL wvecL wstkL wsL wlenL wuL oomL).core)
    (hrefsL : fullArenaClauseRefs (s13WatchSt s arL wvecL wstkL wsL wlenL wuL oomL) =
      fullArenaClauseRefs s)
    (hndL : FullArenaVarsNodup (s13WatchSt s arL wvecL wstkL wsL wlenL wuL oomL))
    (hmL : (FullMem c (s13WatchSt s arL wvecL wstkL wsL wlenL wuL oomL) ⋆ R) mL)
    (hJB : ∀ (bst : BitVec 64 × FullState) m', (∃ arB wvecB wstkB wlenB wuB oomB wsB,
      let sB : FullState := s13WatchSt s arB wvecB wstkB wsB wlenB wuB oomB
      bst.2 = sB ∧ sB.LengthsOk c ∧ FullWitnessInv c F0 F_cur sB.core ∧
      FullArenaVarsNodup sB ∧ fullArenaClauseRefs sB = fullArenaClauseRefs s ∧
      (FullMem c sB ⋆ R) m') → JB (bst.1, ()) m')
    (hLoopL : ∀ (st' : BitVec 64 × FullState) m',
      s.core.arena_len - st'.1.toNat < s.core.arena_len - p.toNat →
      (st'.1.toNat ≤ s.core.arena_len ∧
        (st'.1.toNat < s.core.arena_len → st'.1.toNat ∈ fullArenaClauseRefs s) ∧
        ∃ arL' wvecL' wstkL' wlenL' wuL' oomL' wsL',
          let sL' : FullState := s13WatchSt s arL' wvecL' wstkL' wsL' wlenL' wuL' oomL'
          st'.2 = sL' ∧ sL'.LengthsOk c ∧ FullWitnessInv c F0 F_cur sL'.core ∧
          fullArenaClauseRefs sL' = fullArenaClauseRefs s ∧
          FullArenaVarsNodup sL' ∧ (FullMem c sL' ⋆ R) m') →
      JL (st'.1, ()) m')
    (hQ : ∀ (s' : FullState) (m' : Mem 64),
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.cur_level = s.core.cur_level →
      s'.core.dense_mode = s.core.dense_mode → s'.core.arena_len = s.core.arena_len →
      s'.core.vals = s.core.vals → s'.core.lvl = s.core.lvl → s'.core.flags = s.core.flags →
      s'.core.fuel = s.core.fuel → s'.core.inconsistent = s.core.inconsistent →
      s'.core.d_cur = s.core.d_cur → s'.core.d_val = s.core.d_val →
      s'.scratch.extend_len = s.scratch.extend_len →
      s'.scratch.walk_vals = s.scratch.walk_vals →
      s'.scratch.walk_best = s.scratch.walk_best →
      s'.scratch.last_learned = s.scratch.last_learned → (FullMem c s' ⋆ R) m' → Q () m') :
    wp Γ Q X (s13WatchLoopStepExpr c p at_root JB JL) mL := by
  let sL : FullState := s13WatchSt s arL wvecL wstkL wsL wlenL wuL oomL
  have harL_len : arL.length = c.arena_cap := hlenL.core_ok.arena_len_arr
  have hp_ref0 : p.toNat ∈ fullArenaClauseRefs s := hp_mem hp_lt
  have hp_ref : p.toNat ∈ fullArenaClauseRefsCore sL.core := by
    change p.toNat ∈ fullArenaClauseRefs sL; rw [hrefsL]; exact hp_ref0
  have hpwf := hwL.arena.refs_wf p.toNat hp_ref
  have hnb := fullArenaNextOff_bounds (ar := arL) (alen := s.core.arena_len) (cref := p.toNat)
    hpwf.1
  have hp_trunc : (p.setWidth 32).toNat = p.toNat := by bv_omega
  have hnp_eq : ((BitVec.ofNat 32 (fullArenaNextOff arL s.core.arena_len
      (p.setWidth 32).toNat)).setWidth 64).toNat =
      fullArenaNextOff arL s.core.arena_len p.toNat := by
    rw [hp_trunc, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : fullArenaNextOff arL s.core.arena_len p.toNat < 2 ^ 32)]
    exact Nat.mod_eq_of_lt (by omega)
  have hnext_mem := fullArenaClauseRefs_next_mem hwL.arena hp_ref
  have hnext_mem0 : fullArenaNextOff arL s.core.arena_len p.toNat = s.core.arena_len ∨
      fullArenaNextOff arL s.core.arena_len p.toNat ∈ fullArenaClauseRefs s := by
    change fullArenaNextOff sL.core.arena sL.core.arena_len p.toNat = s.core.arena_len ∨
      fullArenaNextOff sL.core.arena sL.core.arena_len p.toNat ∈
        fullArenaClauseRefs sL at hnext_mem
    rwa [hrefsL] at hnext_mem
  have hp_lt_ar : p.toNat < arL.length := by omega
  have hp2_eq : (p + 2#64).toNat = p.toNat + 2 := by bv_omega
  have hp2_lt : (p + 2#64).toNat < arL.length := by
    have h1 : p.toNat + 3 ≤ s.core.arena_len := hpwf.1; rw [hp2_eq]; omega
  unfold s13WatchLoopStepExpr
  c0_hsteps_nogrp; s13a0b_call hNext
  refine ⟨c, sL, R, rfl, hlenL, hmL, ?_⟩
  c0_hsteps_nogrp
  refine wp_join_group (ts := [])
    (fun () mN => ∃ arN wvecN wstkN wlenN wuN oomN wsN,
      let sN : FullState := s13WatchSt s arN wvecN wstkN wsN wlenN wuN oomN
      sN.LengthsOk c ∧ FullWitnessInv c F0 F_cur sN.core ∧
      fullArenaClauseRefs sN = fullArenaClauseRefs s ∧
      FullArenaVarsNodup sN ∧ (FullMem c sN ⋆ R) mN) ?_ ?_
  · rintro _ ⟨⟩ mN ⟨arN, wvecN, wstkN, wlenN, wuN, oomN, wsN, hlenN, hwN, hrefsN, hndN, hmN⟩
    dsimp only [Prod.fst]
    have hnb2 : fullArenaNextOff sL.core.arena sL.core.arena_len p.toNat ≤
        sL.core.arena_len := by dsimp only [sL]; exact hnb.2
    have hnp_eq' : ((BitVec.ofNat 32 (fullArenaNextOff sL.core.arena sL.core.arena_len
        (p.setWidth 32).toNat)).setWidth 64).toNat =
        fullArenaNextOff sL.core.arena sL.core.arena_len p.toNat := by
      dsimp only [sL]; exact hnp_eq
    have hnext_mem0' : fullArenaNextOff sL.core.arena sL.core.arena_len p.toNat =
          sL.core.arena_len ∨
        fullArenaNextOff sL.core.arena sL.core.arena_len p.toNat ∈ fullArenaClauseRefs s := by
      dsimp only [sL]; exact hnext_mem0
    exact s13_watch_next_join_wp (s := s) (arL := sL.core.arena) har_cap hal_le hp_lt hp_trunc
      hnb2 hnp_eq' hnext_mem0' hlenN hwN hrefsN hndN hmN hJB hLoopL
  · intro JN hJN
    dsimp only [Prod.fst]
    exact s13_watch_clause_iter_wp hRank hPush hmaxv har_cap
      (fun _ hs => hs.symm ▸ ⟨hlenL, hwL, hrefsL, hndL⟩) hp_ref0 hp_lt_ar hp2_eq hp2_lt
      hal_le harL_len hdm0 hlm hext hmL
      (fun arN wvecN wstkN wlenN wuN oomN wsN mN hlenN hwN hrefsN hndN hmN =>
        hJN () mN ⟨arN, wvecN, wstkN, wlenN, wuN, oomN, wsN, hlenN, hwN, hrefsN, hndN, hmN⟩)
      hQ

private def s13WatchBrkInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (st : BitVec 64 × FullState) (mf : Mem 64) : Prop :=
  ∃ arB wvecB wstkB wlenB wuB oomB wsB,
    let sB : FullState := s13WatchSt s arB wvecB wstkB wsB wlenB wuB oomB
    st.2 = sB ∧ sB.LengthsOk c ∧ FullWitnessInv c F0 F_cur sB.core ∧
    FullArenaVarsNodup sB ∧ fullArenaClauseRefs sB = fullArenaClauseRefs s ∧
    (FullMem c sB ⋆ R) mf

private def s13WatchLpInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (st : BitVec 64 × FullState) (mL : Mem 64) : Prop :=
  st.1.toNat ≤ s.core.arena_len ∧
  (st.1.toNat < s.core.arena_len → st.1.toNat ∈ fullArenaClauseRefs s) ∧
  ∃ arL wvecL wstkL wlenL wuL oomL wsL,
    let sL : FullState := s13WatchSt s arL wvecL wstkL wsL wlenL wuL oomL
    st.2 = sL ∧ sL.LengthsOk c ∧ FullWitnessInv c F0 F_cur sL.core ∧
    fullArenaClauseRefs sL = fullArenaClauseRefs s ∧
    FullArenaVarsNodup sL ∧ (FullMem c sL ⋆ R) mL

private def s13WatchLoopStepProj (hdr pArena pVals pLvl : Val i64) (at_root : Val .bool)
    (p : Val i64) (JB JL : Cont [i64]) : Expr Val Cont [] :=
  match full_watch_large_clauses_fid_body Val Cont (hdr, ()) with
  | .let_ (ts := [.bits 64]) _ k1 => match k1 ((0#64 : Val i64), ()) with
    | .load (.bits 64) _ k2 => match k2 pArena with
      | .let_ (ts := [.bits 64]) _ k3 => match k3 ((0#64 : Val i64), ()) with
        | .load (.bits 64) _ k4 => match k4 pVals with
          | .let_ (ts := [.bits 64]) _ k5 => match k5 ((0#64 : Val i64), ()) with
            | .load (.bits 64) _ k6 => match k6 pLvl with
              | .let_ (ts := [.bits 64]) _ k7 => match k7 ((0#64 : Val i64), ()) with
                | .load (.bits 64) _ k8 => match k8 (0#64 : Val i64) with
                  | .let_ (ts := [.bool]) _ k9 => match k9 (at_root, ()) with
                    | .group (sig := [[.bits 64]]) _ kB =>
                      match kB (JB, ()) with
                      | .group (sig := [[.bits 64]]) bsL _ =>
                        match bsL (JL, ()) with
                        | .cons b _ =>
                          match b (p, ()) with
                          | .let_ (ts := [.bits 64]) _ ka => match ka ((0#64 : Val i64), ()) with
                            | .load (.bits 64) _ kb => match kb (0#64 : Val i64) with
                              | .let_ (ts := [.bool]) _ kc => match kc (true, ()) with
                                | .jnz _ t _ => t
                                | _ => .hlt
                              | _ => .hlt
                            | _ => .hlt
                          | _ => .hlt
                        | _ => .hlt
                      | _ => .hlt
                    | _ => .hlt
                  | _ => .hlt
                | _ => .hlt
              | _ => .hlt
            | _ => .hlt
          | _ => .hlt
        | _ => .hlt
      | _ => .hlt
    | _ => .hlt
  | _ => .hlt

private theorem s13_watch_loop_step_eq (c : FullCfg) (p : Val i64) (at_root : Val .bool)
    (JB JL : Cont [i64]) :
    s13WatchLoopStepProj c.hdr c.pArena c.pVals c.pLevel at_root p JB JL =
      s13WatchLoopStepExpr c p at_root JB JL :=
  rfl

/-- Step-13 `full_watch_large_clauses_fid` ranks large arena clauses and attaches 2WL watches. -/
theorem full_watch_large_clauses_fid_s13_wp (Γ : Env)
    (hNext : ∀ a m Q X, Full.fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hRank : ∀ a m Q X, Full.fullLitRankSpec a m Q X →
      Γ "full_lit_rank_m6" [i64, i64, i32] [i64] a m Q X)
    (hPush : ∀ a m Q X, Full.fullWatchPushSpec a m Q X →
      Γ "full_watch_push_m6" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, step13WatchLargeClausesSpec a m Q X →
      Func.wp Γ full_watch_large_clauses_fid_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hlm, hnd, hext, hdm0, hm, hQ⟩
  have har_cap := c.harena; have hmaxv := c.hmaxv; unfold dimacsBound at har_cap hmaxv
  have hal_le := hlen.core_ok.arena_len_le
  unfold Func.wp full_watch_large_clauses_fid_body
  c0_hsteps_nogrp
  refine wp_while_break_state (brkTs := [i64]) (lpTs := [i64])
    (β := BitVec 64 × FullState) (fun st => (st.1, ()))
    (s13WatchBrkInv c F0 F_cur s R)
    (α := BitVec 64 × FullState) (fun st => (st.1, ())) (fun st => s.core.arena_len - st.1.toNat)
    (s13WatchLpInv c F0 F_cur s R) ?_ ?_ ?_
  · rintro B ⟨_pB, _sB⟩ mf ⟨arB, wvecB, wstkB, wlenB, wuB, oomB, wsB, _, hlenB, hwB, hndB,
      hrefsB, hmf⟩
    c0_hsteps_nogrp
    exact s13_watch_ret_wp hlm hext hQ arB wvecB wstkB wsB wlenB wuB oomB mf
      hlenB hwB hndB hrefsB hmf
  · rintro B JL ⟨p, _stL⟩ mL hJB hLoopL ⟨_hp_le, hp_mem, arL, wvecL, wstkL, wlenL, wuL, oomL, wsL,
      _, hlenL, hwL, hrefsL, hndL, hmL⟩
    c0_hsplit
    · have hp_lt : p.toNat < s.core.arena_len := by
        have hlt := hc; rw [Nat.mod_eq_of_lt (by omega)] at hlt; exact hlt
      change wp Γ Q X (s13WatchLoopStepProj c.hdr c.pArena c.pVals c.pLevel
        (BitVec.ofNat 64 s.core.cur_level == 0) p B JL) mL
      rw [s13_watch_loop_step_eq]
      exact s13_watch_loop_step_wp hNext hRank hPush hmaxv har_cap hal_le hdm0 hlm hext
        hp_lt hp_mem hlenL hwL hrefsL hndL hmL hJB hLoopL hQ
    · c0_hsteps_nogrp
      exact hJB (p, s13WatchSt s arL wvecL wstkL wsL wlenL wuL oomL) mL
        ⟨arL, wvecL, wstkL, wlenL, wuL, oomL, wsL, rfl, hlenL, hwL, hndL, hrefsL, hmL⟩
  · intro B JL hB hLoopL
    c0_hsteps_nogrp
    exact hLoopL (0#64, s) m
      ⟨Nat.zero_le _, fun hpos => FullReduceHelpers.fullArenaClauseRefs_zero_mem hw.arena hpos,
       s.core.arena, s.core.wvec, s.core.wstk, s.core.wlen, s.core.wusable, s.core.oom,
       s.scratch.wsort, rfl, hlen, hw, rfl, hnd, hm⟩

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S1
