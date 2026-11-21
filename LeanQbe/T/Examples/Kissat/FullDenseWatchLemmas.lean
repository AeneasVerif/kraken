module

public import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas2

/-!
# Kissat `D-Full` `full_enter_dense` & `full_rebuild_watches` `Func.wp` Proofs (`Stage 4`)

Proves parametric `(Γ : Env)` `Func.wp` contracts for `full_enter_dense` (`Full3.lean:1090-1111`)
and `full_rebuild_watches` (`Full3.lean:1113-1123`), and re-exports `full_reduce_wp` from
`FullDenseWatchLemmas2`:
1. `full_enter_dense_wp`: transitions to `FullDenseInv c F0 s'` on `true` (backtracking to
   level 0, sweeping binaries, pushing `(sz & 0x7FFFFFFF, cref)` occurrence entries onto `wstk`)
   and rolls back cleanly via `full_arena_sweep` to `FullSparseInv c F0 s'` on `false` (OOM).
2. `full_rebuild_watches_wp`: resets `dense_mode = 0#64` and runs the `full_arena_sweep` /
   `full_propagate` fixed-point loop, proving `FullSparseInv c F0 s' ∧ s'.core.cur_level = 0`
   on all return codes `r ∈ {0#64, 1#64, 20#64}`, `r = 20#64 → F0.Unsat`, and
   `s'.core.fuel.toNat ≤ s.core.fuel.toNat`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test
open FullDenseWatchSpecs
open FullDenseWatchHelpers
open scoped FullArenaTactics

open Lean Elab Tactic in
/-- Step goals like `c0_steps`, stopping at `Expr.group` instead of inlining join points. -/
local elab "c0_to_group" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let mut out : Array MVarId := #[]
    for g in ← getUnsolvedGoals do
      if ← g.isAssigned then continue
      let mut g := g
      let mut ty ← Lean.instantiateMVars (← g.getType)
      if ty.isMData then
        g ← g.replaceTargetDefEq ty.consumeMData
        ty := ty.consumeMData
      setGoals [g]
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.group then
        out := out.push g
      else if ← LeanQbe.T.C0Step.stepOnce then
        go (fuel - 1); out := out ++ (← getUnsolvedGoals)
      else out := out.push g
    setGoals out.toList
  go 500

open Lean Elab Tactic in
/-- Strip `mdata` wrappers (e.g. after `have`) and run `c0_steps`. -/
local elab "c0_go" : tactic => do
  let mut gs : Array MVarId := #[]
  for g in ← getUnsolvedGoals do
    if ← g.isAssigned then continue
    let ty ← Lean.instantiateMVars (← g.getType)
    if ty.isMData then gs := gs.push (← g.replaceTargetDefEq ty.consumeMData)
    else gs := gs.push g
  setGoals gs.toList
  LeanQbe.T.C0Step.steps 10000

open Lean Elab Tactic in
/-- Step straight-line ops on the main goal until the next `Expr.jnz`, then split it once. -/
local elab "c0_split" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let mut g ← getMainGoal
    let mut ty ← Lean.instantiateMVars (← g.getType)
    if ty.isMData then
      g ← g.replaceTargetDefEq ty.consumeMData
      ty := ty.consumeMData
      setGoals [g]
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).headBeta).isAppOf ``LeanQbe.T.Expr.jnz then
      let _ ← LeanQbe.T.C0Step.stepOnce; return
    if ← LeanQbe.T.C0Step.stepOnce then go (fuel - 1)
  go 100

/-! ## 1. `full_enter_dense` (`Full3.lean:1090-1111`) -/

private def EnterDenseOk (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s s' : FullState) : Prop :=
  s'.LengthsOk c ∧
  FullWitnessInv c F0 F_cur s'.core ∧
  FullLitMarksClear c s' ∧
  FullArenaVarsNodup s' ∧
  FullExtScratchOk c s' ∧
  s'.core.cur_level = 0 ∧
  s'.core.fuel = s.core.fuel ∧
  s'.core.cur_vars = s.core.cur_vars ∧
  s'.core.inconsistent = s.core.inconsistent ∧
  s'.core.d_cur = s.core.d_cur ∧
  s'.core.d_val = s.core.d_val ∧
  s'.scratch.extend_len = s.scratch.extend_len

private theorem enterDenseOk_watch_push {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sK : FullState} {lit w0 w1 : BitVec 32} {ok : Bool}
    {wvec' wstk' wsort' : List (BitVec 32)} {wlen' : Nat} {wu' : BitVec 64}
    (hokK : EnterDenseOk c F0 F_cur s sK) (hdK : DenseWatchesInv F_cur sK.core)
    (hdmK : sK.core.dense_mode = 0#64)
    (hflag : (w0 &&& 0x80000000#32) = 0#32) (hsz : 3 ≤ w0.toNat)
    (hlt : w1.toNat < 0x80000000) (href : w1.toNat ∈ fullArenaClauseRefsCore sK.core) :
    let sK' : FullState :=
      { sK with
        core := { sK.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
        scratch := { sK.scratch with wsort := wsort' } }
    sK'.LengthsOk c → WatchStackLayout sK'.core →
    (∀ l < 2 * sK.core.cur_vars, l ≠ lit.toNat →
      fullWatchSize sK' l = fullWatchSize sK l ∧
      ∀ i < fullWatchSize sK l,
        sK'.core.wstk[fullWatchOff sK' l + i]? = sK.core.wstk[fullWatchOff sK l + i]?) →
    (ok = true →
      lit.toNat < 2 * sK.core.cur_vars ∧
      fullWatchSize sK' lit.toNat = fullWatchSize sK lit.toNat + 2 ∧
      (∀ i < fullWatchSize sK lit.toNat,
        sK'.core.wstk[fullWatchOff sK' lit.toNat + i]? =
          sK.core.wstk[fullWatchOff sK lit.toNat + i]?) ∧
      sK'.core.wstk[fullWatchOff sK' lit.toNat + fullWatchSize sK lit.toNat]? = some w0 ∧
      sK'.core.wstk[fullWatchOff sK' lit.toNat + fullWatchSize sK lit.toNat + 1]? = some w1) →
    (ok = false → lit.toNat < 2 * sK.core.cur_vars →
      fullWatchSize sK' lit.toNat = fullWatchSize sK lit.toNat ∧
      ∀ i < fullWatchSize sK lit.toNat,
        sK'.core.wstk[fullWatchOff sK' lit.toNat + i]? =
          sK.core.wstk[fullWatchOff sK lit.toNat + i]?) →
    EnterDenseOk c F0 F_cur s sK' ∧ DenseWatchesInv F_cur sK'.core := by
  intro sK' hlen' hlay' hoth hokT hokF
  have hd' : DenseWatchesInv F_cur sK'.core :=
    fullWatchPush_preserves_denseWatchesInv hdK hlay' rfl (fun _ r => r)
      hflag hsz hlt href hoth hokT hokF
  have hw' : FullWitnessInv c F0 F_cur sK'.core :=
    { hokK.2.1 with
      arena := { hokK.2.1.arena with len_ok := hokK.2.1.arena.len_ok }
      watches := by
        rw [ModeWatchesInv, ite_eq_left hdmK]; exact denseWatchesInv_toWatchesInv hd' }
  exact ⟨⟨hlen', hw', hokK.2.2.1, hokK.2.2.2.1, hokK.2.2.2.2.1, hokK.2.2.2.2.2.1,
    hokK.2.2.2.2.2.2.1, hokK.2.2.2.2.2.2.2.1, hokK.2.2.2.2.2.2.2.2.1, hokK.2.2.2.2.2.2.2.2.2.1,
    hokK.2.2.2.2.2.2.2.2.2.2.1, hokK.2.2.2.2.2.2.2.2.2.2.2⟩, hd'⟩

private theorem enterDenseOk_oom_sweep {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sOom : FullState} (hokO : EnterDenseOk c F0 F_cur s sOom)
    {valsS : List (BitVec 8)}
    {flagsS lvlS rsnsS trlS tpS wvecS wstkS arenaS : List (BitVec 32)}
    {teS alenS wlenS : Nat} {unassS unflS wuS fredS niS nrS nbS oomS : BitVec 64}
    {scS : FullScratch} :
    let sS : FullState :=
      { sOom with
        core := { sOom.core with
          vals := valsS, flags := flagsS, lvl := lvlS, rsns := rsnsS, trl := trlS,
          trail_pos := tpS, trail_end := teS, unassigned := unassS, unflushed := unflS,
          wvec := wvecS, wstk := wstkS, arena := arenaS, arena_len := alenS, wlen := wlenS,
          wusable := wuS, arena_garbage := 0#64, first_reducible := fredS, num_irred := niS,
          num_redundant := nrS, num_binary := nbS, oom := oomS }
        scratch := scS }
    sS.LengthsOk c → FullWitnessInv c F0 F_cur sS.core → FullArenaVarsNodup sS →
    FullLastLearnedWf sS → scS.extend_len = sOom.scratch.extend_len →
    EnterDenseOk c F0 F_cur s sS := by
  intro sS hlenS hwS hndS hllS hextS
  exact ⟨hlenS, hwS, hokO.2.2.1, hndS, ⟨hllS, hextS ▸ hokO.2.2.2.2.1.2⟩,
    hokO.2.2.2.2.2.1, hokO.2.2.2.2.2.2.1, hokO.2.2.2.2.2.2.2.1, hokO.2.2.2.2.2.2.2.2.1,
    hokO.2.2.2.2.2.2.2.2.2.1, hokO.2.2.2.2.2.2.2.2.2.2.1,
    hextS.trans hokO.2.2.2.2.2.2.2.2.2.2.2⟩

theorem full_enter_dense_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hSweepBins : ∀ a m Q X, fullSweepBinsSpec a m Q X →
      Γ "full_sweep_bins" [i64] [] a m Q X)
    (hWatchPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hArenaNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X) :
    ∀ a m Q X, fullEnterDenseSpec a m Q X → Func.wp Γ full_enter_dense_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hlm, hnd, hext, hm, hQ⟩
  have har_cap : c.arena_cap < 2 * 2 ^ 28 := c.harena
  have hmaxv : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hret_t : ∀ (st : FullState) (ml : Mem 64),
      EnterDenseOk c F0 F_cur s st → st.core.dense_mode ≠ 0#64 →
      (FullMem c st ⋆ R) ml → Q (true, ()) ml := fun st ml hok hdm hml =>
    hQ true st ml hok.1 hok.2.1 hok.2.2.1 hok.2.2.2.1 hok.2.2.2.2.1 hok.2.2.2.2.2.1
      hok.2.2.2.2.2.2.1 hok.2.2.2.2.2.2.2.1 hok.2.2.2.2.2.2.2.2.1 hok.2.2.2.2.2.2.2.2.2.1
      hok.2.2.2.2.2.2.2.2.2.2.1 hok.2.2.2.2.2.2.2.2.2.2.2
      (fun _ => ⟨⟨hok.1, ⟨F_cur, hok.2.1⟩⟩, hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2.1,
        hok.2.2.2.2.2.1, hdm⟩)
      (by simp) hml
  have hret_f : ∀ (st : FullState) (ml : Mem 64),
      EnterDenseOk c F0 F_cur s st → st.core.dense_mode = 0#64 →
      (FullMem c st ⋆ R) ml → Q (false, ()) ml := fun st ml hok hdm hml =>
    hQ false st ml hok.1 hok.2.1 hok.2.2.1 hok.2.2.2.1 hok.2.2.2.2.1 hok.2.2.2.2.2.1
      hok.2.2.2.2.2.2.1 hok.2.2.2.2.2.2.2.1 hok.2.2.2.2.2.2.2.2.1 hok.2.2.2.2.2.2.2.2.2.1
      hok.2.2.2.2.2.2.2.2.2.2.1 hok.2.2.2.2.2.2.2.2.2.2.2
      (by simp)
      (fun _ => ⟨⟨hok.1, ⟨F_cur, hok.2.1⟩⟩, hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2.1, hdm⟩)
      hml
  c0_to_group
  -- Join point after `if (h->cur_level != 0ULL) { full_backtrack(h, 0ULL); }`.
  refine wp_join_group
    (fun _ m1 => ∃ s1 : FullState, EnterDenseOk c F0 F_cur s s1 ∧ (FullMem c s1 ⋆ R) m1) ?_ ?_
  · rintro _ _ m1 ⟨s1, hok1, hm1⟩
    clear hm hlen hw hlm hnd hext
    c0_to_group
    · -- Already in dense mode (`dense_mode ≠ 0`): return `true`.
      exact hret_t s1 m1 hok1 hc hm1
    · -- `dense_mode == 0`: sweep bins, push occurrence lists, then set `dense_mode := 1#64`.
      have hdm1 : s1.core.dense_mode = 0#64 := hc
      c0_call hSweepBins
      refine ⟨c, F0, F_cur, s1, R, rfl, hok1.1, hok1.2.1, hm1,
        fun wvec2 wstk2 wlen2 nb2 wsort2 m2 hlen2 hw2 hd2 hm2 => ?_⟩
      let s2 : FullState :=
        { s1 with
          core := { s1.core with
            wvec := wvec2, wstk := wstk2, wlen := wlen2, wusable := 0#64, num_binary := nb2 }
          scratch := { s1.scratch with wsort := wsort2 } }
      have hok2 : EnterDenseOk c F0 F_cur s s2 :=
        ⟨hlen2, hw2, hok1.2.2.1, hok1.2.2.2.1, hok1.2.2.2.2.1, hok1.2.2.2.2.2.1,
          hok1.2.2.2.2.2.2.1, hok1.2.2.2.2.2.2.2.1, hok1.2.2.2.2.2.2.2.2.1,
          hok1.2.2.2.2.2.2.2.2.2.1, hok1.2.2.2.2.2.2.2.2.2.2.1, hok1.2.2.2.2.2.2.2.2.2.2.2⟩
      c0_to_group
      -- Outer loop: `while (p < h->arena_len)`.
      refine wp_loop_inv
        (fun (p, ()) mP =>
          p.toNat ≤ s2.core.arena_len ∧
          (p.toNat = s2.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs s2) ∧
          ∃ sP : FullState,
            EnterDenseOk c F0 F_cur s sP ∧ DenseWatchesInv F_cur sP.core ∧
            sP.core.arena = s2.core.arena ∧ sP.core.arena_len = s2.core.arena_len ∧
            sP.core.dense_mode = 0#64 ∧ (FullMem c sP ⋆ R) mP)
        (fun (p, ()) _ => s2.core.arena_len - p.toNat)
        (fun JP hLoopP => by
          c0_go
          refine hLoopP (0#64, ()) m2 ⟨Nat.zero_le _, ?_, s2, hok2, hd2, rfl, rfl, hdm1, hm2⟩
          by_cases hz : s2.core.arena_len = 0
          · exact Or.inl hz.symm
          · exact Or.inr (fullArenaClauseRefs_zero_mem hw2.arena (Nat.pos_of_ne_zero hz)))
        (fun JP (p, ()) mP ⟨hp_le, hp_mem, sP, hokP, hdP, harP, halenP, hdmP, hmP⟩ hLoopP => ?_)
      · have halP := hokP.1.core_ok.arena_len_le
        have haarP := hokP.1.core_ok.arena_len_arr
        have hrefsP : fullArenaClauseRefs sP = fullArenaClauseRefs s2 := by
          unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [harP, halenP]
        c0_split
        · -- Outer loop body: `p < sP.core.arena_len`.
          have hp_lt : p.toNat < sP.core.arena_len := by c0_bound
          have hp_in : p.toNat ∈ fullArenaClauseRefs sP := by
            rw [hrefsP]; exact hp_mem.resolve_left (by omega)
          have hp_wf := hokP.2.1.arena.refs_wf p.toNat hp_in
          have hp_lt32 : p.toNat < 2 ^ 32 := by omega
          have hp_trunc : (p.setWidth 32).toNat = p.toNat := by
            rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt hp_lt32
          have hnb := fullArenaNextOff_bounds (ar := sP.core.arena) (alen := sP.core.arena_len)
            (cref := p.toNat) hp_wf.1
          have hnxt_mem := fullArenaClauseRefs_next_mem hokP.2.1.arena hp_in
          -- Join point before `p = (u64)full_arena_next(h, (u32)p);`.
          c0_to_group
          refine wp_join_group
            (fun _ mN =>
              ∃ sN : FullState,
                EnterDenseOk c F0 F_cur s sN ∧ DenseWatchesInv F_cur sN.core ∧
                sN.core.arena = s2.core.arena ∧ sN.core.arena_len = s2.core.arena_len ∧
                sN.core.dense_mode = 0#64 ∧ (FullMem c sN ⋆ R) mN)
            (fun _ _ mN ⟨sN, hokN, hdN, harN, halenN, hdmN, hmN⟩ => by
              c0_to_group
              c0_call hArenaNext
              refine ⟨c, sN, R, rfl, hokN.1, hmN, ?_⟩
              have hn_eq : ((BitVec.ofNat 32 (fullArenaNextOff sN.core.arena sN.core.arena_len
                  (p.setWidth 32).toNat)).setWidth 64).toNat =
                  fullArenaNextOff sP.core.arena sP.core.arena_len p.toNat := by
                rw [harN, halenN, ← harP, ← halenP, hp_trunc, BitVec.toNat_setWidth,
                  bv32_ofNat_toNat (by omega)]
                exact Nat.mod_eq_of_lt (by omega)
              c0_go
              exact hLoopP (_, ()) mN (by dsimp only; rw [hn_eq]; omega)
                ⟨by rw [hn_eq]; omega,
                  by rw [hn_eq]
                     rcases hnxt_mem with hend | hmem
                     · exact Or.inl (hend.trans halenP)
                     · exact Or.inr (hrefsP ▸ hmem),
                  sN, hokN, hdN, harN, halenN, hdmN, hmN⟩)
            (fun JN hJN => ?_)
          c0_to_group
          · -- Live irred clause with `sz ≥ 3`: push `(sz & 0x7FFFFFFF, p)` for each `k < sz`.
            have hsz_eq : (sP.core.arena[(p + 2#64).toNat]'(by c0_bound)).toNat =
                fullArenaClauseSizeCore sP.core p.toNat := by
              have hp2 : (p + 2#64).toNat = p.toNat + 2 := by c0_bound
              unfold fullArenaClauseSizeCore
              rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
              simp only [hp2]
            have hsz_ge3 : 3 ≤ (sP.core.arena[(p + 2#64).toNat]'(by c0_bound)).toNat := by
              rw [hsz_eq]; exact hp_wf.2.1
            have hsz_lt31 : (sP.core.arena[(p + 2#64).toNat]'(by c0_bound)).toNat < 2 ^ 31 := by
              rw [hsz_eq]; have := hp_wf.2.2.1; have := hp_wf.2.2.2.1; omega
            have hmask := bv32_mask_7fffffff_props hsz_ge3 hsz_lt31
            have hp_lt31 : (p.setWidth 32).toNat < 0x80000000 := by rw [hp_trunc]; omega
            have hp_neff : p.setWidth 32 ≠ 0xFFFFFFFF#32 := fun heq => by
              rw [heq] at hp_lt31; revert hp_lt31; decide
            refine wp_loop_inv
              (fun (k, ()) mK =>
                k.toNat ≤ (sP.core.arena[(p + 2#64).toNat]'(by c0_bound)).toNat ∧
                ∃ sK : FullState,
                  EnterDenseOk c F0 F_cur s sK ∧ DenseWatchesInv F_cur sK.core ∧
                  sK.core.arena = s2.core.arena ∧ sK.core.arena_len = s2.core.arena_len ∧
                  sK.core.dense_mode = 0#64 ∧ (FullMem c sK ⋆ R) mK)
              (fun (k, ()) _ => (sP.core.arena[(p + 2#64).toNat]'(by c0_bound)).toNat - k.toNat)
              (fun JK hLoopK => by
                c0_go
                exact hLoopK (0#32, ()) mP ⟨Nat.zero_le _, sP, hokP, hdP, harP, halenP, hdmP, hmP⟩)
              (fun JK (k, ()) mK ⟨hk_le, sK, hokK, hdK, harK, halenK, hdmK, hmK⟩ hLoopK => ?_)
            · have haarK := hokK.1.core_ok.arena_len_arr
              c0_split
              · -- Inner loop body (`k < sz`).
                have hk_lt : k.toNat < (sP.core.arena[(p + 2#64).toNat]'(by c0_bound)).toNat := by
                  c0_bound
                have hidx_eq : (p + 3#64 + k.setWidth 64).toNat = p.toNat + 3 + k.toNat := by
                  have h1 : (p + 3#64).toNat = p.toNat + 3 := by c0_bound
                  have h2 : (k.setWidth 64).toNat = k.toNat := zext_toNat k (by decide)
                  have := hp_wf.2.2.1; have := hp_wf.2.2.2.1
                  rw [BitVec.toNat_add, h1, h2]; exact Nat.mod_eq_of_lt (by omega)
                have hidx_lt : (p + 3#64 + k.setWidth 64).toNat < sK.core.arena.length := by
                  rw [hidx_eq]; rw [hsz_eq] at hk_lt
                  have := hp_wf.2.2.1; have := hp_wf.2.2.2.1
                  have := hokK.1.core_ok.arena_len_le; omega
                c0_to_group
                c0_call hWatchPush
                refine ⟨c, sK, R, rfl, hokK.1, hdK.layout, by simp,
                  fun _ => ⟨hmask.2.1, hp_neff⟩, hmK,
                  fun ok wvecK' wstkK' wlenK' wuK' wsortK' mK' hlenK' hlayK' hothK' hokT
                    hokF hmK' => ?_⟩
                let sK' : FullState :=
                  { sK with
                    core := { sK.core with wvec := wvecK', wstk := wstkK', wlen := wlenK',
                                           wusable := wuK' }
                    scratch := { sK.scratch with wsort := wsortK' } }
                have hp_inK : (p.setWidth 32).toNat ∈ fullArenaClauseRefsCore sK.core := by
                  rw [hp_trunc]; unfold fullArenaClauseRefsCore; rw [harK, halenK, ← harP, ← halenP]
                  exact hp_in
                obtain ⟨hokK', hdK'⟩ :=
                  enterDenseOk_watch_push hokK hdK hdmK hmask.1 hmask.2.2 hp_lt31 hp_inK
                    hlenK' hlayK' hothK'
                    (fun ht => by
                      obtain ⟨hl, _, hsz', hpre', hw0', hw1'⟩ := hokT ht
                      exact ⟨hl, hsz', hpre', hw0', hw1' rfl⟩) hokF
                c0_to_group
                · -- `ok = true`: advance `k := k + 1u`.
                  have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
                  exact hLoopK (k + 1#32, ()) mK' (by dsimp only; omega)
                    ⟨by omega, sK', hokK', hdK', harK, halenK, hdmK, hmK'⟩
                · -- `ok = false` (OOM): `h->oom = 0ULL; full_arena_sweep(h); return false;`.
                  let sOom : FullState := { sK' with core := { sK'.core with oom := 0#64 } }
                  have hlenOom : sOom.LengthsOk c :=
                    ⟨{ hlenK'.core_ok with vals_len := hlenK'.core_ok.vals_len },
                      hlenK'.scratch_ok⟩
                  have hokOom : EnterDenseOk c F0 F_cur s sOom :=
                    ⟨hlenOom, fullWitnessInv_with_oom hokK'.2.1 0#64, hokK'.2.2.1, hokK'.2.2.2.1,
                      hokK'.2.2.2.2.1, hokK'.2.2.2.2.2.1, hokK'.2.2.2.2.2.2.1,
                      hokK'.2.2.2.2.2.2.2.1, hokK'.2.2.2.2.2.2.2.2.1, hokK'.2.2.2.2.2.2.2.2.2.1,
                      hokK'.2.2.2.2.2.2.2.2.2.2.1, hokK'.2.2.2.2.2.2.2.2.2.2.2⟩
                  c0_call hSweep
                  refine ⟨c, F0, F_cur, sOom, R, rfl, hlenOom, hokOom.2.1, hokOom.2.2.2.1, hdmK,
                    fun hpos => by
                      change 0 < sK.core.cur_level at hpos
                      have := hokK.2.2.2.2.2.1; omega,
                    hm,
                    fun _ valsS flagsS lvlS rsnsS trlS tpS teS unassS unflS wvecS wstkS arenaS
                      alenS wlenS wuS fredS niS nrS nbS oomS scS mS hlenS hwS hndS hllS hextS
                      _ _ _ _ _ _ hmS => ?_⟩
                  c0_go
                  exact hret_f _ mS (enterDenseOk_oom_sweep hokOom hlenS hwS hndS hllS hextS)
                    hdmK hmS
              · -- Inner loop exit (`k == sz`).
                c0_go
                exact hJN () mK ⟨sK, hokK, hdK, harK, halenK, hdmK, hmK⟩
          all_goals exact hJN () mP ⟨sP, hokP, hdP, harP, halenP, hdmP, hmP⟩
        · -- Outer loop exit (`p ≥ arena_len`): `h->dense_mode = 1ULL; return true;`.
          c0_go
          let sFin : FullState := { sP with core := { sP.core with dense_mode := 1#64 } }
          have hlenFin : sFin.LengthsOk c :=
            ⟨{ hokP.1.core_ok with vals_len := hokP.1.core_ok.vals_len }, hokP.1.scratch_ok⟩
          exact hret_t sFin _
            ⟨hlenFin, fullWitnessInv_with_dense_mode_nz hokP.2.1 hdP (by decide), hokP.2.2.1,
              hokP.2.2.2.1,
              hokP.2.2.2.2.1, hokP.2.2.2.2.2.1, hokP.2.2.2.2.2.2.1, hokP.2.2.2.2.2.2.2.1,
              hokP.2.2.2.2.2.2.2.2.1, hokP.2.2.2.2.2.2.2.2.2.1, hokP.2.2.2.2.2.2.2.2.2.2.1,
              hokP.2.2.2.2.2.2.2.2.2.2.2⟩
            (show (1#64 : BitVec 64) ≠ 0#64 by decide) hm
  · -- Entry to `if (h->cur_level != 0ULL)`.
    intro J1 hJ1
    c0_to_group
    · c0_call hBacktrack
      refine ⟨c, F0, F_cur, s, R, rfl, hlen, hw, Nat.zero_le _, hm,
        fun vals' lvl' rsns' trl' tp' te' prop' unass' sc' m' hlen' hw' hll' hext' _ hm' => ?_⟩
      let s1 : FullState :=
        { s with
          core := { s.core with
            vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
            trail_end := te', propagated := prop', cur_level := 0, unassigned := unass' }
          scratch := sc' }
      have hll1 : FullLastLearnedWf s1 := fun i hi => by
        change sc'.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
          (sc'.last_learned[i]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefs s
        rw [hll']; exact hext.1 i hi
      c0_go
      exact hJ1 () m' ⟨s1, ⟨hlen', hw', hlm, hnd, ⟨hll1, hext' ▸ hext.2⟩, rfl, rfl, rfl, rfl,
        rfl, rfl, hext'⟩, hm'⟩
    · have hcl0 : s.core.cur_level = 0 := by
        have := hlen.core_ok.trail_end_le; have := hlen.core_ok.cur_vars_le; have := hw.cur_level_le
        c0_bound
      exact hJ1 () m ⟨s, ⟨hlen, hw, hlm, hnd, hext, hcl0, rfl, rfl, rfl, rfl, rfl, rfl⟩, hm⟩

/-! ## 2. `full_rebuild_watches` (`Full3.lean:1113-1123`) -/

private def RebuildOk (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s s' : FullState) : Prop :=
  FullSparseInv c F0 s' ∧
  FullWitnessInv c F0 F_cur s'.core ∧
  s'.core.cur_level = 0 ∧
  s'.core.fuel.toNat ≤ s.core.fuel.toNat ∧
  s'.core.cur_vars = s.core.cur_vars ∧
  s'.core.inconsistent = s.core.inconsistent ∧
  s'.core.d_cur = s.core.d_cur ∧
  s'.core.d_val = s.core.d_val ∧
  s'.scratch.extend_len = s.scratch.extend_len

private theorem rebuildOk_arena_sweep {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} (hst : RebuildOk c F0 F_cur s st)
    {vals' : List (BitVec 8)}
    {flags' lvl' rsns' trl' tp' wvec' wstk' arena' : List (BitVec 32)}
    {te' alen' wlen' : Nat} {unass' unfl' wu' fred' ni' nr' nb' oom' : BitVec 64}
    {sc' : FullScratch} :
    let sA : FullState :=
      { st with
        core := { st.core with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
          trail_pos := tp', trail_end := te', unassigned := unass', unflushed := unfl',
          wvec := wvec', wstk := wstk', arena := arena', arena_len := alen', wlen := wlen',
          wusable := wu', arena_garbage := 0#64, first_reducible := fred', num_irred := ni',
          num_redundant := nr', num_binary := nb', oom := oom' }
        scratch := sc' }
    sA.LengthsOk c → FullWitnessInv c F0 F_cur sA.core → FullArenaVarsNodup sA →
    FullLastLearnedWf sA → sc'.extend_len = st.scratch.extend_len →
    RebuildOk c F0 F_cur s sA := by
  intro sA hlenA hwA hndA hllA hextA
  exact ⟨⟨⟨hlenA, ⟨F_cur, hwA⟩⟩, hst.1.2.1, hndA, ⟨hllA, hextA ▸ hst.1.2.2.2.1.2⟩,
    hst.1.2.2.2.2⟩, hwA, hst.2.2.1, hst.2.2.2.1, hst.2.2.2.2.1,
    hst.2.2.2.2.2.1, hst.2.2.2.2.2.2.1, hst.2.2.2.2.2.2.2.1,
    hextA.trans hst.2.2.2.2.2.2.2.2⟩

private theorem rebuildOk_propagate {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sA : FullState} (hA : RebuildOk c F0 F_cur s sA)
    {valsB : List (BitVec 8)}
    {flagsB lvlB rsnsB trlB tpB wvecB arenaB wstkB : List (BitVec 32)}
    {teB propB wlenB : Nat} {unassB unflB wuB fuelB ctypeB crefB c0B c1B oomB : BitVec 64}
    {scB : FullScratch} :
    let sB : FullState :=
      { sA with
        core := { sA.core with
          vals := valsB, flags := flagsB, lvl := lvlB, rsns := rsnsB, trl := trlB,
          trail_pos := tpB, trail_end := teB, propagated := propB, unassigned := unassB,
          unflushed := unflB, wvec := wvecB, arena := arenaB, wstk := wstkB, wlen := wlenB,
          wusable := wuB, fuel := fuelB, confl_type := ctypeB, confl_ref := crefB,
          confl_lit0 := c0B, confl_lit1 := c1B, oom := oomB }
        scratch := scB }
    sB.LengthsOk c → FullWitnessInv c F0 F_cur sB.core → FullArenaVarsNodup sB →
    (∀ ref ∈ fullArenaClauseRefs sA, ref ∈ fullArenaClauseRefs sB) →
    scB.last_learned = sA.scratch.last_learned →
    scB.extend_len = sA.scratch.extend_len →
    fuelB.toNat ≤ sA.core.fuel.toNat →
    RebuildOk c F0 F_cur s sB := by
  intro sB hlenB hwB hndB hrefsB hllB hextB hfuelB
  have hllB' : FullLastLearnedWf sB := fun i hi => by
    change scB.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∨
      (scB.last_learned[i]?.getD 0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefs sB
    rw [hllB]; exact (hA.1.2.2.2.1.1 i hi).imp id (hrefsB _)
  exact ⟨⟨⟨hlenB, ⟨F_cur, hwB⟩⟩, hA.1.2.1, hndB, ⟨hllB', hextB ▸ hA.1.2.2.2.1.2⟩,
    hA.1.2.2.2.2⟩, hwB, hA.2.2.1, Nat.le_trans hfuelB hA.2.2.2.1, hA.2.2.2.2.1,
    hA.2.2.2.2.2.1, hA.2.2.2.2.2.2.1, hA.2.2.2.2.2.2.2.1,
    hextB.trans hA.2.2.2.2.2.2.2.2⟩

theorem full_rebuild_watches_wp (Γ : Env)
    (hSweep : ∀ a m Q X, fullArenaSweepSpec a m Q X →
      Γ "full_arena_sweep" [i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullRebuildWatchesSpec a m Q X → Func.wp Γ full_rebuild_watches_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hlm, hnd, hext, hcl0, hm, hQ⟩
  have hret : ∀ (r : BitVec 64) (st : FullState) (ml : Mem 64),
      RebuildOk c F0 F_cur s st → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) → (FullMem c st ⋆ R) ml → Q (r, ()) ml := by
    intro r st ml hok hr hu hml
    exact hQ r st ml hok.1 hok.2.1 hok.2.2.1 hr hu hok.2.2.2.1 hok.2.2.2.2.1
      hok.2.2.2.2.2.1 hok.2.2.2.2.2.2.1 hok.2.2.2.2.2.2.2.1 hok.2.2.2.2.2.2.2.2 hml
  c0_to_group
  let s0 : FullState := { s with core := { s.core with dense_mode := 0#64 } }
  have hlen0 : s0.LengthsOk c :=
    ⟨{ hlen.core_ok with vals_len := hlen.core_ok.vals_len }, hlen.scratch_ok⟩
  have hw0 : FullWitnessInv c F0 F_cur s0.core := fullWitnessInv_with_dense_mode_zero hw
  have hok0 : RebuildOk c F0 F_cur s s0 :=
    ⟨⟨⟨hlen0, ⟨F_cur, hw0⟩⟩, hlm, hnd, hext, rfl⟩, hw0, hcl0, Nat.le_refl _, rfl, rfl, rfl, rfl,
      rfl⟩
  -- Join point `Jbrk` after `while (true)` -> `return 1ULL`.
  refine wp_join_group
    (fun _ m1 => ∃ st : FullState, RebuildOk c F0 F_cur s st ∧ (FullMem c st ⋆ R) m1)
    (fun _ _ m1 ⟨st, hok, hm1⟩ => by
      c0_go; exact hret 1#64 st m1 hok (Or.inr (Or.inl rfl)) (by simp) hm1)
    (fun Jbrk hJbrk => by
      c0_to_group
      refine wp_loop_group
        (fun rem () ml => ∃ st : FullState, rem = c.max_vars - st.core.trail_end ∧
          RebuildOk c F0 F_cur s st ∧ (FullMem c st ⋆ R) ml) ?_ ?_
      · rintro L rem ⟨⟩ ml ih ⟨st, rfl, hok_st, hm_st⟩
        dsimp only [Blocks.get]
        refine wp_jnz_of (fun _ => ?_) (fun hc => by cases hc)
        c0_call hSweep
        refine ⟨c, F0, F_cur, st, R, rfl, hok_st.1.1.lengths, hok_st.2.1, hok_st.1.2.2.1,
          hok_st.1.2.2.2.2, fun hpos => by have := hok_st.2.2.1; omega, hm_st,
          fun sr vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' arena' alen'
            wlen' wu' fred' ni' nr' nb' oom' sc' mA hlenA hwA hndA hllA hextA _ hsr_dom _ _ hsr1
            hsr2 hmA => ?_⟩
        let sA : FullState :=
          { st with
            core := { st.core with
              vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
              trail_pos := tp', trail_end := te', unassigned := unass', unflushed := unfl',
              wvec := wvec', wstk := wstk', arena := arena', arena_len := alen', wlen := wlen',
              wusable := wu', arena_garbage := 0#64, first_reducible := fred', num_irred := ni',
              num_redundant := nr', num_binary := nb', oom := oom' }
            scratch := sc' }
        have hokA : RebuildOk c F0 F_cur s sA :=
          rebuildOk_arena_sweep hok_st hlenA hwA hndA hllA hextA
        c0_go
        · exact hret 20#64 sA mA hokA (Or.inr (Or.inr rfl)) (fun _ => (hsr2 hc).2) hmA
        · exact hret 0#64 sA mA hokA (Or.inl rfl) (by simp) hmA
        · c0_call hProp
          refine ⟨c, F0, F_cur, sA, R, rfl, hlenA, hwA, hndA, hok_st.1.2.2.2.2, hmA,
            fun pr valsB flagsB lvlB rsnsB trlB tpB teB propB unassB unflB wvecB arenaB wstkB
              wlenB wuB fuelB ctypeB crefB c0B c1B oomB scB mB hlenB hwB hndB hrefsB hllB hextB
              _ hteB hfuelB _ _ hconflB hmB => ?_⟩
          let sB : FullState :=
            { sA with
              core := { sA.core with
                vals := valsB, flags := flagsB, lvl := lvlB, rsns := rsnsB, trl := trlB,
                trail_pos := tpB, trail_end := teB, propagated := propB, unassigned := unassB,
                unflushed := unflB, wvec := wvecB, arena := arenaB, wstk := wstkB, wlen := wlenB,
                wusable := wuB, fuel := fuelB, confl_type := ctypeB, confl_ref := crefB,
                confl_lit0 := c0B, confl_lit1 := c1B, oom := oomB }
              scratch := scB }
          have hokB : RebuildOk c F0 F_cur s sB :=
            rebuildOk_propagate hokA hlenB hwB hndB hrefsB hllB hextB hfuelB
          c0_go
          · exact hret 20#64 sB mB hokB (Or.inr (Or.inr rfl))
              (fun _ => fullConflictInv_level0_unsat hwB hok_st.2.2.1 (hconflB hc)) hmB
          · exact hJbrk () mB ⟨sB, hokB, hmB⟩
          · have hsr_eq1 : sr = 1#64 := by
              rcases hsr_dom with rfl | rfl | rfl | rfl <;> first | rfl | contradiction
            obtain ⟨_, hte_lt⟩ := hsr1 hsr_eq1
            have hte_bd : sB.core.trail_end ≤ c.max_vars :=
              Nat.le_trans hlenB.core_ok.trail_end_le hlenB.core_ok.cur_vars_le
            have hteA : sA.core.trail_end = te' := rfl
            have hteB_eq : sB.core.trail_end = teB := rfl
            exact ih (c.max_vars - sB.core.trail_end) () mB (by omega) ⟨sB, rfl, hokB, hmB⟩
      · intro L hL; c0_go
        exact hL (c.max_vars - s0.core.trail_end) () _ ⟨s0, rfl, hok0, hm⟩)

end LeanQbe.T.Examples.Kissat.Full
