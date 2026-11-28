/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Clause
public import LeanQbe.T.Examples.Kissat.Proof.Clause.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Clause.Helpers
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts4
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation
meta import LeanQbe.T.Logic.C0Step
meta import LeanQbe.T.Logic.C0HeadStep

/-!
# WP Proof for `Src.Clause.full_add_clause` (`Proof.Clause.Wp1`)

Canonical parametric `(Γ : Env)` `Func.wp` proof for `full_add_clause` against
`Clause.Spec.fullAddClauseSpec`:
1. `len = 2`: binary watch insertion (`full_watch_push`), rollback (`full_watch_pop_c0`),
   and `flags` + `num_binary` update.
2. `len < 2`: immediate no-op (`0xFFFFFFFF`).
3. `3 ≤ len`: arena allocation (`full_alloc_cl`), literal-copy loop (`wp_loop_inv`),
   binary-free large watch insertion + rollback (`h->arena_len = cref`), and reducible/irred
   counters.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Clause

open Std.Sat
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Clause
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullBvaFwdTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open Kraken.Bedrock2.Test

/-! ## 1. Pure Post-Condition & Tmp Helpers for `full_add_clause` -/

private theorem tmp2_props {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    (hlen : s.LengthsOk c) (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hlen2 : 2 ≤ c.max_vars)
    (hTmp : (∀ l ∈ (s.core.tmp.take 2).map BitVec.toNat, l < 2 * s.core.cur_vars) ∧
      ((s.core.tmp.take 2).map fun x => x.toNat / 2).Nodup ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause ((s.core.tmp.take 2).map BitVec.toNat))) :
    have h0 : 0 < s.core.tmp.length := by rw [hlen.core_ok.tmp_len_arr]; omega
    have h1 : 1 < s.core.tmp.length := by rw [hlen.core_ok.tmp_len_arr]; omega
    let l0 := s.core.tmp[0]'h0
    let l1 := s.core.tmp[1]'h1
    l0.toNat < 2 * s.core.cur_vars ∧ l1.toNat < 2 * s.core.cur_vars ∧
    l0 ≠ l1 ∧ (l0 >>> 1#32).toNat < c.max_vars ∧ (l1 >>> 1#32).toNat < c.max_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l0.toNat, l1.toNat]) := by
  have h0 : 0 < s.core.tmp.length := by rw [hlen.core_ok.tmp_len_arr]; omega
  have h1 : 1 < s.core.tmp.length := by rw [hlen.core_ok.tmp_len_arr]; omega
  have htake : s.core.tmp.take 2 = [s.core.tmp[0]'h0, s.core.tmp[1]'h1] := by
    apply List.ext_getElem
    · simp [List.length_take]; omega
    · intro i hi1 hi2
      rcases (by simp at hi2; omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp
  rcases hTmp with ⟨hlits, hnd, hent⟩
  rw [htake, List.map_cons, List.map_cons, List.map_nil] at hlits hnd hent
  have hl0 := hlits _ List.mem_cons_self
  have hl1 := hlits _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hne_div : (s.core.tmp[0]'h0).toNat / 2 ≠ (s.core.tmp[1]'h1).toNat / 2 := by
    rw [List.nodup_cons, List.mem_singleton] at hnd; exact hnd.1
  have hne : s.core.tmp[0]'h0 ≠ s.core.tmp[1]'h1 := fun heq =>
    hne_div (congrArg (fun x => x.toNat / 2) heq)
  exact ⟨hl0, hl1, hne, Nat.lt_of_lt_of_le (bv32_shr1_lt_vars hl0) hcv_le,
    Nat.lt_of_lt_of_le (bv32_shr1_lt_vars hl1) hcv_le, hent⟩

private theorem tmp_large_props {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {len : Nat} (hlen : s.LengthsOk c) (hge3 : 3 ≤ len) (hlen_mv : len ≤ c.max_vars)
    (hTmp : (∀ l ∈ (s.core.tmp.take len).map BitVec.toNat, l < 2 * s.core.cur_vars) ∧
      ((s.core.tmp.take len).map fun x => x.toNat / 2).Nodup ∧
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause ((s.core.tmp.take len).map BitVec.toNat))) :
    have h0 : 0 < s.core.tmp.length := by rw [hlen.core_ok.tmp_len_arr]; omega
    have h1 : 1 < s.core.tmp.length := by rw [hlen.core_ok.tmp_len_arr]; omega
    let l0 := s.core.tmp[0]'h0
    let l1 := s.core.tmp[1]'h1
    l0.toNat < 2 * s.core.cur_vars ∧ l1.toNat < 2 * s.core.cur_vars ∧ l0 ≠ l1 := by
  have h0 : 0 < s.core.tmp.length := by rw [hlen.core_ok.tmp_len_arr]; omega
  have h1 : 1 < s.core.tmp.length := by rw [hlen.core_ok.tmp_len_arr]; omega
  rcases hTmp with ⟨hlits, hnd, _⟩
  have hlen_t0 : 0 < (s.core.tmp.take len).length := by
    simp [List.length_take, hlen.core_ok.tmp_len_arr]; omega
  have hlen_t1 : 1 < (s.core.tmp.take len).length := by
    simp [List.length_take, hlen.core_ok.tmp_len_arr]; omega
  have h0_mem : s.core.tmp[0]'h0 ∈ s.core.tmp.take len := by
    have hm0 : (s.core.tmp.take len)[0]'hlen_t0 ∈ s.core.tmp.take len := List.getElem_mem _
    simpa [List.getElem_take] using hm0
  have h1_mem : s.core.tmp[1]'h1 ∈ s.core.tmp.take len := by
    have hm1 : (s.core.tmp.take len)[1]'hlen_t1 ∈ s.core.tmp.take len := List.getElem_mem _
    simpa [List.getElem_take] using hm1
  have hl0 := hlits _ (List.mem_map_of_mem h0_mem)
  have hl1 := hlits _ (List.mem_map_of_mem h1_mem)
  have hnd2 : ((s.core.tmp.take len).Pairwise fun a b => a.toNat / 2 ≠ b.toNat / 2) := by
    rwa [← List.pairwise_map]
  have hlt_take0 : 0 < (s.core.tmp.take len).length := by
    rw [List.length_take, hlen.core_ok.tmp_len_arr]; omega
  have hlt_take1 : 1 < (s.core.tmp.take len).length := by
    rw [List.length_take, hlen.core_ok.tmp_len_arr]; omega
  have hpw := (List.pairwise_iff_getElem.mp hnd2) 0 1 hlt_take0 hlt_take1 (by omega)
  simp only [List.getElem_take] at hpw
  have hne : s.core.tmp[0]'h0 ≠ s.core.tmp[1]'h1 := fun heq =>
    hpw (congrArg (fun x => x.toNat / 2) heq)
  exact ⟨hl0, hl1, hne⟩

/-! ## 2. Binary Clause Post-Push Continuation (`len = 2`) -/

private theorem add_clause_bin_ok_post {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop} {Q : Post [i64]}
    {m' : Mem 64} {wvec2 wstk2 : List (BitVec 32)} {wlen2 : Nat} {wu2 : BitVec 64}
    {wsort2 flags' : List (BitVec 32)} {nb' : BitVec 64}
    (hlen2 : ({ s with
      core := { s.core with wvec := wvec2, wstk := wstk2, wlen := wlen2, wusable := wu2 }
      scratch := { s.scratch with wsort := wsort2 } } : FullState).LengthsOk c)
    (hw2 : FullWitnessInv c F0 F_cur
      { s.core with wvec := wvec2, wstk := wstk2, wlen := wlen2, wusable := wu2 })
    (hf_len : flags'.length = c.max_vars)
    (hm' : (FullMem c { s with
      core := { s.core with flags := flags', wvec := wvec2, wstk := wstk2, wlen := wlen2,
                            wusable := wu2, num_binary := nb' }
      scratch := { s.scratch with wsort := wsort2 } } ⋆ R) m')
    (hQ : ∀ r flags'' wvec'' wstk'' wlen'' wu'' nb'' wsort'' m'',
      let s' : FullState :=
        { s with
          core := { s.core with
            flags := flags'', wvec := wvec'', wstk := wstk'',
            wlen := wlen'', wusable := wu'', num_binary := nb'' }
          scratch := { s.scratch with wsort := wsort'' } }
      (r = 0xFFFFFFFF#64 ∨ r = 0xFFFFFFFE#64) →
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      (FullMem c s' ⋆ R) m'' → Q (r, ()) m'') :
    Q (0xFFFFFFFE#64, ()) m' := by
  let s' : FullState :=
    { s with
      core := { s.core with flags := flags', wvec := wvec2, wstk := wstk2, wlen := wlen2,
                            wusable := wu2, num_binary := nb' }
      scratch := { s.scratch with wsort := wsort2 } }
  have hlen' : s'.LengthsOk c :=
    ⟨{ hlen2.core_ok with flags_len := hf_len }, hlen2.scratch_ok⟩
  have hwat' : ModeWatchesInv F_cur s'.core :=
    hw2.watches.with_wstk rfl rfl rfl rfl rfl (fun _ h => h)
  have hw' := fullWitnessInv_with_watches_meta hw2 hwat'
  exact hQ 0xFFFFFFFE#64 flags' wvec2 wstk2 wlen2 wu2 nb' wsort2 m' (.inr rfl) hlen' hw' hm'

/-! ## 3. Large Clause Loop & Post-Push Helpers (`3 ≤ len`) -/

private theorem add_clause_large_rollback_post {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop} {Q : Post [i64]}
    {m' : Mem 64} {len : Nat} {arena' wvec' wstk' : List (BitVec 32)} {wlen' : Nat}
    {wu' : BitVec 64} {wsort' : List (BitVec 32)}
    (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hlen_rb : ({ s with
      core := { s.core with arena := arena', wvec := wvec', wstk := wstk', wlen := wlen',
                            wusable := wu' }
      scratch := { s.scratch with wsort := wsort' } } : FullState).LengthsOk c)
    (hlay_rb : WatchStackLayout
      { s.core with arena := arena', wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' })
    (hhold : ∀ i < s.core.arena_len, arena'[i]? = s.core.arena[i]?)
    (hrel : ∀ l < 2 * s.core.cur_vars,
      fullWatchSizeCore { s.core with arena := arena', wvec := wvec', wstk := wstk',
                                      wlen := wlen', wusable := wu' } l =
        fullWatchSizeCore s.core l ∧
      ∀ idx < fullWatchSizeCore s.core l,
        wstk'[fullWatchOffCore { s.core with arena := arena', wvec := wvec', wstk := wstk',
                                             wlen := wlen', wusable := wu' } l + idx]? =
          s.core.wstk[fullWatchOffCore s.core l + idx]?)
    (hm' : (FullMem c { s with
      core := { s.core with arena := arena', wvec := wvec', wstk := wstk', wlen := wlen',
                            wusable := wu' }
      scratch := { s.scratch with wsort := wsort' } } ⋆ R) m')
    (hQ : ∀ r arena'' alen'' wvec'' wstk'' wlen'' wu'' fred'' ni'' nr'' wsort'' m'',
      let s' : FullState :=
        { s with
          core := { s.core with
            arena := arena'', arena_len := alen'', wvec := wvec'',
            wstk := wstk'', wlen := wlen'', wusable := wu'',
            first_reducible := fred'', num_irred := ni'', num_redundant := nr'' }
          scratch := { s.scratch with wsort := wsort'' } }
      (r = 0xFFFFFFFF#64 ∨ r = BitVec.ofNat 64 s.core.arena_len) →
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      (∀ ref ∈ fullArenaClauseRefs s, ref ∈ fullArenaClauseRefs s') →
      (FullArenaVarsNodup s → FullArenaVarsNodup s') →
      (r = BitVec.ofNat 64 s.core.arena_len → alen'' = s.core.arena_len + 3 + len ∧
        s.core.arena_len ∈ fullArenaClauseRefs s' ∧
        fullArenaClauseGarb s' s.core.arena_len = false ∧
        fullArenaClauseLits s' s.core.arena_len =
          (s.core.tmp.take len).map BitVec.toNat) →
      (FullMem c s' ⋆ R) m'' → Q (r, ()) m'') :
    Q (0xFFFFFFFF#64, ()) m' := by
  let c_rb : FullCoreState :=
    { s.core with arena := arena', wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
  let s_rb : FullState := { s with core := c_rb, scratch := { s.scratch with wsort := wsort' } }
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaNextOff arena' s.core.arena_len r =
        fullArenaNextOff s.core.arena s.core.arena_len r :=
    hw.arena.arenaNextOff_extend (arena' := arena') (alen' := s.core.arena_len)
      (Nat.le_refl _) hhold
  have hrefs : fullArenaClauseRefsCore c_rb = fullArenaClauseRefsCore s.core :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hwat_rb : ModeWatchesInv F_cur c_rb :=
    modeWatchesInv_of_slice_relocate hw.watches hlay_rb rfl rfl (fun r hr => hrefs ▸ hr) hrel
  have hw_rb : FullWitnessInv c F0 F_cur c_rb :=
    rollback_preserves_fullWitness hw
      (by have := hlen.core_ok.arena_len_le; rw [hlen.core_ok.arena_len_arr]; exact this)
      (by have := hlen_rb.core_ok.arena_len_le; rw [hlen_rb.core_ok.arena_len_arr]; exact this)
      hhold hwat_rb
  have hcreq : (0xFFFFFFFF#64 : BitVec 64) ≠ BitVec.ofNat 64 s.core.arena_len := by
    have ha := hlen.core_ok.arena_len_le
    have hcap := c.harena; unfold dimacsBound at hcap
    intro h; have hb := congrArg BitVec.toNat h
    have hx : (0xFFFFFFFF#64 : BitVec 64).toNat = 0xFFFFFFFF := rfl
    rw [hx, bv64_ofNat_toNat (by omega)] at hb; omega
  have hnodup : FullArenaVarsNodup s → FullArenaVarsNodup s_rb := fun hnd r hr hng => by
    unfold fullArenaClauseRefs at hr; rw [hrefs] at hr
    have hwf := hw.arena.refs_wf r hr
    have hwf_sub := hwf.2.2.1; have hwf_le := hwf.2.2.2.1
    have hbd : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena_len := by omega
    have hsz_eq : fullArenaClauseSizeCore c_rb r = fullArenaClauseSizeCore s.core r := by
      unfold fullArenaClauseSizeCore c_rb; simp [hhold (r + 2) (by omega)]
    have hlits : fullArenaClauseLits s_rb r = fullArenaClauseLits s r :=
      fullArenaClauseLitsCore_eq_of_hold
        (by have := hlen.core_ok.arena_len_le; rw [hlen.core_ok.arena_len_arr]; omega)
        (by have := hlen_rb.core_ok.arena_len_le
            rw [hlen_rb.core_ok.arena_len_arr]; exact Nat.le_trans hbd this)
        hsz_eq (fun j hj => hhold (r + 3 + j) (by omega))
    have hgb : fullArenaClauseGarb s_rb r = fullArenaClauseGarb s r := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore s_rb c_rb
      simp [hhold r (by omega)]
    rw [hlits]; exact hnd r hr (hgb ▸ hng)
  exact hQ 0xFFFFFFFF#64 arena' s.core.arena_len wvec' wstk' wlen' wu' s.core.first_reducible
    s.core.num_irred s.core.num_redundant wsort' m' (.inl rfl) hlen_rb hw_rb
    (fun r hr => by unfold fullArenaClauseRefs; rw [hrefs]; exact hr)
    hnodup (fun h => absurd h hcreq) hm'

private theorem add_clause_large_ok_post {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} {R : Mem 64 → Prop} {Q : Post [i64]}
    {m' : Mem 64} {len : Nat} {arena' wvec' wstk' : List (BitVec 32)} {wlen' : Nat}
    {wu' fred' ni' nr' : BitVec 64} {wsort' : List (BitVec 32)}
    (hlen2 : ({ s with
      core := { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len,
                            wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
      scratch := { s.scratch with wsort := wsort' } } : FullState).LengthsOk c)
    (hw_wr : FullWitnessInv c F0 F_cur (addArenaState s arena' len).core)
    (hwat2 : ModeWatchesInv F_cur
      { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len,
                    wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' })
    (hrefs_wr : fullArenaClauseRefs (addArenaState s arena' len) =
      fullArenaClauseRefs s ++ [s.core.arena_len])
    (hsub_wr : ∀ r ∈ fullArenaClauseRefs s, r ∈ fullArenaClauseRefs (addArenaState s arena' len))
    (hnodup_wr : FullArenaVarsNodup s → FullArenaVarsNodup (addArenaState s arena' len))
    (hgarb_wr : fullArenaClauseGarb (addArenaState s arena' len) s.core.arena_len = false)
    (hlits_wr : fullArenaClauseLits (addArenaState s arena' len) s.core.arena_len =
      (s.core.tmp.take len).map BitVec.toNat)
    (hm' : (FullMem c { s with
      core := { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len,
                            wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu',
                            first_reducible := fred', num_irred := ni', num_redundant := nr' }
      scratch := { s.scratch with wsort := wsort' } } ⋆ R) m')
    (hQ : ∀ r arena'' alen'' wvec'' wstk'' wlen'' wu'' fred'' ni'' nr'' wsort'' m'',
      let s' : FullState :=
        { s with
          core := { s.core with
            arena := arena'', arena_len := alen'', wvec := wvec'',
            wstk := wstk'', wlen := wlen'', wusable := wu'',
            first_reducible := fred'', num_irred := ni'', num_redundant := nr'' }
          scratch := { s.scratch with wsort := wsort'' } }
      (r = 0xFFFFFFFF#64 ∨ r = BitVec.ofNat 64 s.core.arena_len) →
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      (∀ ref ∈ fullArenaClauseRefs s, ref ∈ fullArenaClauseRefs s') →
      (FullArenaVarsNodup s → FullArenaVarsNodup s') →
      (r = BitVec.ofNat 64 s.core.arena_len → alen'' = s.core.arena_len + 3 + len ∧
        s.core.arena_len ∈ fullArenaClauseRefs s' ∧
        fullArenaClauseGarb s' s.core.arena_len = false ∧
        fullArenaClauseLits s' s.core.arena_len =
          (s.core.tmp.take len).map BitVec.toNat) →
      (FullMem c s' ⋆ R) m'' → Q (r, ()) m'') :
    Q (BitVec.ofNat 64 s.core.arena_len, ()) m' := by
  let c' : FullCoreState :=
    { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len,
                  wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu',
                  first_reducible := fred', num_irred := ni', num_redundant := nr' }
  let s' : FullState := { s with core := c', scratch := { s.scratch with wsort := wsort' } }
  have hlen' : s'.LengthsOk c :=
    ⟨{ hlen2.core_ok with vals_len := hlen2.core_ok.vals_len }, hlen2.scratch_ok⟩
  have hwat' : ModeWatchesInv F_cur c' :=
    hwat2.with_wstk rfl rfl rfl rfl rfl (fun _ h => h)
  have hw' : FullWitnessInv c F0 F_cur c' :=
    fullWitnessInv_with_watches_meta hw_wr hwat'
  have hrefs' : fullArenaClauseRefs s' = fullArenaClauseRefs (addArenaState s arena' len) := rfl
  have hmem_new : s.core.arena_len ∈ fullArenaClauseRefs s' := by
    rw [hrefs', hrefs_wr]; simp
  exact hQ (BitVec.ofNat 64 s.core.arena_len) arena' (s.core.arena_len + 3 + len)
    wvec' wstk' wlen' wu' fred' ni' nr' wsort' m' (.inr rfl) hlen' hw' hsub_wr hnodup_wr
    (fun _ => ⟨rfl, hmem_new, hgarb_wr, hlits_wr⟩) hm'

/-! ## 4. `full_add_clause_wp` -/

/-- Canonical `Func.wp` proof for `full_add_clause` against `Clause.Spec.fullAddClauseSpec`. -/
theorem full_add_clause_wp (Γ : Env)
    (hAllocCl : Γ.Has "full_alloc_cl" Proof.Spec.fullAllocClSpec)
    (hWatchPush : Γ.Has "full_watch_push" Proof.Spec.fullWatchPushSpec)
    (hWatchPop : Γ.Has "full_watch_pop_c0" Proof.Watch.Spec.fullWatchPopC0Spec) :
    ∀ a m Q X, Spec.fullAddClauseSpec a m Q X → Func.wp Γ full_add_clause_body a m Q X := by
  rintro ⟨h, len, glue, red, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm0, hlen_mv, hTmp, hm, hQ⟩
  unfold Func.wp full_add_clause_body
  have hcl := hlen.core_ok
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hcl.cur_vars_le
  have hmax_lt : 2 * c.max_vars < 0x7FFFFFFF := by
    have hmx := c.hmaxv; unfold dimacsBound at hmx; omega
  c0_hsteps
  · -- `len == 2u`
    have hlen_nat : len.toNat = 2 := by c0_bound
    have hmv2 : 2 ≤ c.max_vars := by omega
    have hTmp2 := hTmp (by rw [hlen_nat]; omega)
    rw [hlen_nat] at hTmp2
    rcases tmp2_props hlen hcv_le hmv2 hTmp2 with
      ⟨hl0_lt, hl1_lt, hne01, hv0_mv, hv1_mv, hent01⟩
    have htmp0_len : 0 < s.core.tmp.length := by rw [hcl.tmp_len_arr]; omega
    have htmp1_len : 1 < s.core.tmp.length := by rw [hcl.tmp_len_arr]; omega
    let l0 := s.core.tmp[0]'htmp0_len
    let l1 := s.core.tmp[1]'htmp1_len
    have hw0_0 : ((l1 &&& 0x7FFFFFFF#32) ||| 0x80000000#32) ≠ 0xFFFFFFFF#32 :=
      bv32_tag_bin_ne_sent (lit_lt_0x7FFFFFFF hcv_le hl1_lt)
    have hw0_1 : ((l0 &&& 0x7FFFFFFF#32) ||| 0x80000000#32) ≠ 0xFFFFFFFF#32 :=
      bv32_tag_bin_ne_sent (lit_lt_0x7FFFFFFF hcv_le hl0_lt)
    simp only [hlen_nat, show ¬ (2 < 2) from by omega, ↓reduceIte] at hQ
    c0_hsteps
    c0_call hWatchPush
    refine ⟨c, s, R, rfl, hlen, hw.watches.layout, (fun _ => hw0_0),
      (fun h => by cases h), hm, ?_⟩
    intro ok1 wvec1 wstk1 wlen1 wu1 wsort1 m1
    dsimp only
    rintro hlen1 hlay1 hoth1 hok1t hok1f hm1
    let s1 : FullState :=
      { s with
        core := { s.core with wvec := wvec1, wstk := wstk1, wlen := wlen1, wusable := wu1 }
        scratch := { s.scratch with wsort := wsort1 } }
    have hwat1 : ModeWatchesInv F_cur s1.core := by
      refine fullWatchPush_preserves_modeWatchesInv hw.watches hlay1 rfl rfl
        (fun _ h => h) (fun _ => ?_) (fun h => by cases h) hoth1 hok1t
        (fun h hlt => (hok1f h).1 hlt)
      refine ⟨bv32_tag_bin_msb_ne l1, hw0_0, ?_, ?_⟩
      · change (((l1 &&& 0x7FFFFFFF#32) ||| 0x80000000#32) &&& 0x7FFFFFFF#32).toNat < _
        rw [bv32_tag_bin_unmask, bv32_and_mask_eq
          (by have : l1.toNat < 0x7FFFFFFF := lit_lt_0x7FFFFFFF hcv_le hl1_lt; omega)]
        exact hl1_lt
      · change (cnfOfClauses F_cur).EntailsClause
          (cnfClause [l0.toNat, (((l1 &&& 0x7FFFFFFF#32) ||| 0x80000000#32) &&&
            0x7FFFFFFF#32).toNat])
        rw [bv32_tag_bin_unmask, bv32_and_mask_eq
          (by have : l1.toNat < 0x7FFFFFFF := lit_lt_0x7FFFFFFF hcv_le hl1_lt; omega)]
        exact hent01
    have hw1 := fullWitnessInv_with_watches_meta hw hwat1
    c0_hsteps
    · -- `ok1 = true` -> push 2 on `l1`
      have hok1_parts := hok1t (by
        rename_i hc; cases h : ok1 <;> (try rw [h] at hc) <;>
          first | rfl | contradiction | cases hc | exact absurd hc (by decide))
      c0_call hWatchPush
      refine ⟨c, s1, R, rfl, hlen1, hlay1, (fun _ => hw0_1), (fun h => by cases h), hm1, ?_⟩
      intro ok2 wvec2 wstk2 wlen2 wu2 wsort2 m2
      dsimp only
      rintro hlen2 hlay2 hoth2 hok2t hok2f hm2
      let s2 : FullState :=
        { s1 with
          core := { s1.core with wvec := wvec2, wstk := wstk2, wlen := wlen2, wusable := wu2 }
          scratch := { s1.scratch with wsort := wsort2 } }
      have hwat2 : ModeWatchesInv F_cur s2.core := by
        refine fullWatchPush_preserves_modeWatchesInv hwat1 hlay2 rfl rfl
          (fun _ h => h) (fun _ => ?_) (fun h => by cases h) hoth2 hok2t
          (fun h hlt => (hok2f h).1 hlt)
        refine ⟨bv32_tag_bin_msb_ne l0, hw0_1, ?_, ?_⟩
        · change (((l0 &&& 0x7FFFFFFF#32) ||| 0x80000000#32) &&& 0x7FFFFFFF#32).toNat < _
          rw [bv32_tag_bin_unmask, bv32_and_mask_eq
            (by have : l0.toNat < 0x7FFFFFFF := lit_lt_0x7FFFFFFF hcv_le hl0_lt; omega)]
          exact hl0_lt
        · change (cnfOfClauses F_cur).EntailsClause
            (cnfClause [l1.toNat, (((l0 &&& 0x7FFFFFFF#32) ||| 0x80000000#32) &&&
              0x7FFFFFFF#32).toNat])
          rw [bv32_tag_bin_unmask, bv32_and_mask_eq
            (by have : l0.toNat < 0x7FFFFFFF := lit_lt_0x7FFFFFFF hcv_le hl0_lt; omega)]
          exact entails_swap2 hent01
      c0_hsteps_nogrp
      · -- `ok2 = true` -> update `flags`, `num_binary`, return `0xFFFFFFFE`
        have hfl_s2 : s2.core.flags.length = c.max_vars := hlen2.core_ok.flags_len
        have hv0_s2 :
            (BitVec.setWidth 64 (s2.core.tmp[(BitVec.ofNat 64 0).toNat] >>> 1)).toNat <
              s2.core.flags.length := by
          change (BitVec.setWidth 64 (l0 >>> 1#32)).toNat < s2.core.flags.length
          rw [hfl_s2, BitVec.toNat_setWidth,
            Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide))]
          exact hv0_mv
        have hv1_s2 :
            (BitVec.setWidth 64 (s2.core.tmp[(BitVec.ofNat 64 1).toNat] >>> 1)).toNat <
              s2.core.flags.length := by
          change (BitVec.setWidth 64 (l1 >>> 1#32)).toNat < s2.core.flags.length
          rw [hfl_s2, BitVec.toNat_setWidth,
            Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide))]
          exact hv1_mv
        c0_hsteps_nogrp_nobound
        refine LeanQbe.T.wp_join_group (fun (_ : Tup Val [i32]) m' => m' = m2) ?_ ?_
        · rintro J ⟨bit_0, ⟨⟩⟩ m' rfl
          rw [Blocks.get_here]
          c0_hsteps_nogrp_nobound
          obtain ⟨v_1, hv_1⟩ : ∃ v_1 : BitVec 32,
              loadVal m i32
                (c.pFlags +
                  BitVec.setWidth 64 (s2.core.tmp[(BitVec.ofNat 64 1).toNat] >>> 1) * 4) =
                some v_1 := by
            refine ⟨_, FullArenaTactics.c0_load_full_flags ?_ hm⟩
            rw [List.length_set]; exact hv1_s2
          apply LeanQbe.T.wp_load_of hv_1
          c0_hsteps_nogrp_nobound
          refine LeanQbe.T.wp_join_group (fun (_ : Tup Val [i32]) m'' => m'' = m) ?_ ?_
          · rintro Js ⟨bit_1, ⟨⟩⟩ m'' rfl
            rw [Blocks.get_here]
            c0_hsteps_nogrp_nobound
            apply LeanQbe.T.wp_store_sep
            · refine FullArenaTactics.c0_store_full_flags _ ?_ hm
              rw [List.length_set]; exact hv1_s2
            · intro m_f hm_f
              clear hv_1 hm
              c0_hsteps_nobound
              have hw2 := fullWitnessInv_with_watches_meta hw1 hwat2
              have hfl2 : s2.core.flags.length = c.max_vars := hlen2.core_ok.flags_len
              refine add_clause_bin_ok_post hlen2 hw2 ?_ (by assumption) hQ
              try simp only [List.length_set]
              exact hfl2
          · intro Js hJs
            c0_hfast_nogrp_nobound
            all_goals exact hJs _ _ rfl
        · intro J hJ
          c0_hfast_nogrp_nobound
          all_goals exact hJ _ _ rfl
      · -- `ok2 = false` -> `full_watch_pop_c0(h, l0, 1); return 0xFFFFFFFF`
        c0_hsteps
        have hok2_parts := hok2f (by
          rename_i hc; cases h : ok2 <;> (try rw [h] at hc) <;>
            first | rfl | contradiction | cases hc | exact absurd hc (by decide))
        have hsz2_l0 : fullWatchSize s2 l0.toNat = fullWatchSize s1 l0.toNat ∧
            ∀ idx < fullWatchSize s1 l0.toNat,
              s2.core.wstk[fullWatchOff s2 l0.toNat + idx]? =
                s1.core.wstk[fullWatchOff s1 l0.toNat + idx]? :=
          hoth2 l0.toNat hl0_lt (fun h => hne01 (BitVec.eq_of_toNat_eq h))
        c0_call hWatchPop
        refine ⟨c, s2, R, rfl, hlen2, hlay2,
          (by change l0.toNat < 2 * s2.core.cur_vars; exact hl0_lt),
          by decide, ?_, hm2, ?_⟩
        · have hpush1 : fullWatchSize s1 l0.toNat = fullWatchSize s l0.toNat + 1 :=
            hok1_parts.2.2.1
          change fullWatchSize s2 l0.toNat ≥ 1; omega
        · intro wvec3 wstk3 wu3 m3
          dsimp only
          rintro hlen3 hlay3 hoth3 hoff3 hsz3 hpf3 hm3
          let s3 : FullState :=
            { s2 with core := { s2.core with wvec := wvec3, wstk := wstk3, wusable := wu3 } }
          have hwat3 : ModeWatchesInv F_cur s3.core :=
            fullWatchPopC0_after_push_fail_modeWatchesInv (k1 := s1.core) (cnt := 1)
              hw.watches hwat2 hlay3
              rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hl0_lt
              hok1_parts.2.2.1 hok1_parts.2.2.2.1 hsz2_l0 hsz3 hpf3 hoth3
          have hw3 := fullWitnessInv_with_watches_meta hw hwat3
          c0_hsteps
          exact hQ 0xFFFFFFFF#64 s.core.flags wvec3 wstk3 wlen2 wu3 s.core.num_binary wsort2 m3
            (.inl rfl) hlen3 hw3 hm3
    · -- `ok1 = false` -> `return 0xFFFFFFFF`
      exact hQ 0xFFFFFFFF#64 s.core.flags wvec1 wstk1 wlen1 wu1 s.core.num_binary wsort1 m1
        (.inl rfl) hlen1 hw1 hm1
  · -- `len < 3u` (and `len ≠ 2u`, so `len < 2`)
    have hlt2 : len.toNat < 2 := by
      have hne2 : len.toNat ≠ 2 := by c0_bound
      have hlt3 : len.toNat < 3 := by c0_bound
      omega
    simp only [hlt2, ↓reduceIte] at hQ
    exact hQ
  · -- `3 ≤ len`
    have hge3 : 3 ≤ len.toNat := by c0_bound
    simp only [show ¬ (len.toNat < 2) from by omega, show len.toNat ≠ 2 from by omega, ↓reduceIte]
      at hQ
    c0_call hAllocCl
    refine ⟨c, s, R, rfl, hlen, hm, ?_⟩
    by_cases hcap : c.arena_cap - s.core.arena_len < 3 + len.toNat
    · rw [ite_eq_left hcap]
      c0_hsteps
      exact hQ 0xFFFFFFFF#64 s.core.arena s.core.arena_len s.core.wvec s.core.wstk s.core.wlen
        s.core.wusable s.core.first_reducible s.core.num_irred s.core.num_redundant s.scratch.wsort
        m (.inl rfl) hlen hw (fun _ h => h) (fun h => h)
        (fun h => by
          have ha := hcl.arena_len_le; have hmx := c.harena; unfold dimacsBound at hmx
          have hb := congrArg BitVec.toNat h
          have hx : (0xFFFFFFFF#64 : BitVec 64).toNat = 0xFFFFFFFF := rfl
          rw [hx, bv64_ofNat_toNat (by omega)] at hb; omega)
        hm
    · rw [ite_eq_right hcap]
      dsimp only
      rintro arena1 m1 hlen1 hhold1 hns1 hng1 hred1 hsz1 hm1
      have hcr_le : s.core.arena_len < c.arena_cap := by omega
      have hcap_lt : c.arena_cap < 2 * dimacsBound := c.harena
      unfold dimacsBound at hcap_lt
      have hne_sent : BitVec.ofNat 64 s.core.arena_len ≠ 0xFFFFFFFF#64 := by
        intro h; have hb := congrArg BitVec.toNat h
        have hx : (0xFFFFFFFF#64 : BitVec 64).toNat = 0xFFFFFFFF := rfl
        rw [hx, bv64_ofNat_toNat (by omega)] at hb; omega
      let s1 : FullState := addArenaState s arena1 len.toNat
      c0_hsteps_nogrp
      have htmp_arr : s.core.tmp.length = c.max_vars := hcl.tmp_len_arr
      have har1_arr : arena1.length = c.arena_cap := hlen1.core_ok.arena_len_arr
      have hal1_le : s.core.arena_len + 3 + len.toNat ≤ c.arena_cap := by omega
      have htmp_all := hTmp (by omega)
      rcases tmp_large_props hlen hge3 hlen_mv htmp_all with ⟨hl0_lt, hl1_lt, hne01⟩
      have htmp0_len : 0 < s.core.tmp.length := by rw [htmp_arr]; omega
      have htmp1_len : 1 < s.core.tmp.length := by rw [htmp_arr]; omega
      let l0 := s.core.tmp[0]'htmp0_len
      let l1 := s.core.tmp[1]'htmp1_len
      have hcr_32 : (BitVec.ofNat 64 s.core.arena_len).setWidth 32 =
          BitVec.ofNat 32 s.core.arena_len := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_setWidth, bv64_ofNat_toNat (by omega),
          bv32_ofNat_toNat (by omega), Nat.mod_eq_of_lt (by omega)]
      have hw1_lt : ((BitVec.ofNat 64 s.core.arena_len).setWidth 32).toNat < 0x80000000 := by
        rw [hcr_32, bv32_ofNat_toNat (by omega)]; omega
      have hw1_ns : (BitVec.ofNat 64 s.core.arena_len).setWidth 32 ≠ 0xFFFFFFFF#32 := by
        intro h; have hb := congrArg BitVec.toNat h
        have hx : (0xFFFFFFFF#32 : BitVec 32).toNat = 0xFFFFFFFF := rfl
        rw [hx, hcr_32, bv32_ofNat_toNat (by omega)] at hb; omega
      have hw0_1_ns : (l1 &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32 :=
        bv32_and_litMask_ne_sent (lit_lt_0x7FFFFFFF hcv_le hl1_lt)
      have hw0_0_ns : (l0 &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32 :=
        bv32_and_litMask_ne_sent (lit_lt_0x7FFFFFFF hcv_le hl0_lt)
      refine wp_loop_inv (ts := [i32])
        (fun (i, ()) mL => ∃ arL : List (BitVec 32),
          i.toNat ≤ len.toNat ∧ arL.length = c.arena_cap ∧
          (∀ j < s.core.arena_len, arL[j]? = s.core.arena[j]?) ∧
          (arL[s.core.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32 ∧
          (arL[s.core.arena_len]?.getD 0#32 &&& 0x00080000#32) = 0#32 ∧
          (arL[s.core.arena_len + 2]?.getD 0#32).toNat = len.toNat ∧
          (∀ j < i.toNat, arL[s.core.arena_len + 3 + j]? = s.core.tmp[j]?) ∧
          (FullMem c (addArenaState s arL len.toNat) ⋆ R) mL)
        (fun (i, ()) _ => len.toNat - i.toNat)
        ?_ ?_
      · intro JL hLoop
        c0_hsteps
        exact hLoop (0#32, ()) m1 ⟨arena1, Nat.zero_le _, har1_arr, hhold1, hns1, hng1,
          hsz1, fun j hj => by simp at hj, hm1⟩
      · rintro JL ⟨i, ⟨⟩⟩ mL ⟨arL, hi_le, harL_len, hholdL, hnsL, hngL, hszL, hlitsL, hmL⟩ hLoop
        rw [Blocks.get_here]; dsimp only
        c0_hsplit_nobound
        · have hi_lt : i.toNat < len.toNat := by c0_bound
          have hi_mv : i.toNat < s.core.tmp.length := by rw [htmp_arr]; omega
          have hi_sw : (i.setWidth 64).toNat <
              (addArenaState s arL len.toNat).core.tmp.length := by
            dsimp [addArenaState]
            rw [BitVec.toNat_setWidth,
              Nat.mod_eq_of_lt (Nat.lt_trans i.isLt (by decide))]
            exact hi_mv
          have hdst_lt : s.core.arena_len + 3 + i.toNat < arL.length := by rw [harL_len]; omega
          have hi_64 : (BitVec.ofNat 64 s.core.arena_len + 3#64 + i.setWidth 64).toNat =
              s.core.arena_len + 3 + i.toNat := by
            have hsw : i.setWidth 64 = BitVec.ofNat 64 i.toNat := by
              apply BitVec.eq_of_toNat_eq
              rw [BitVec.toNat_setWidth, bv64_ofNat_toNat (Nat.lt_trans hi_lt (by omega)),
                Nat.mod_eq_of_lt (Nat.lt_trans i.isLt (by decide))]
            rw [hsw]; exact bv64_add3_add_toNat (by omega)
          have hdst_64 : (BitVec.ofNat 64 s.core.arena_len + 3#64 + i.setWidth 64).toNat <
              (addArenaState s arL len.toNat).core.arena.length := by
            rw [hi_64]; exact hdst_lt
          have hi1 : (i + 1#32).toNat = i.toNat + 1 := by
            rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
              Nat.mod_eq_of_lt (by omega)]
          c0_hsteps_nobound
          let arL' := arL.set (s.core.arena_len + 3 + i.toNat) (s.core.tmp[i.toNat]'hi_mv)
          refine hLoop (i + 1#32, ()) _ (by dsimp only; rw [hi1]; omega)
            ⟨arL', by rw [hi1]; omega,
              by dsimp only [arL']; rw [List.length_set, harL_len], ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro j hj
            dsimp [arL']; rw [List.getElem?_set_ne (by omega)]; exact hholdL j hj
          · dsimp [arL']; rw [List.getElem?_set_ne (by omega)]; exact hnsL
          · dsimp [arL']; rw [List.getElem?_set_ne (by omega)]; exact hngL
          · dsimp [arL']; rw [List.getElem?_set_ne (by omega)]; exact hszL
          · intro j hj
            rw [hi1] at hj
            dsimp [arL']
            by_cases hje : j = i.toNat
            · subst hje; rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem hi_mv]
            · rw [List.getElem?_set_ne (by omega)]; exact hlitsL j (by omega)
          · dsimp only [arL']
            rw [← hi_64]
            exact hm
        · have hi_eq : i.toNat = len.toNat := by
            have hge : len.toNat ≤ i.toNat := by c0_bound
            omega
          c0_hsteps_nobound
          let s_wr : FullState := addArenaState s arL len.toNat
          have hlen_wr : s_wr.LengthsOk c :=
            ⟨{ hlen1.core_ok with arena_len_arr := harL_len }, hlen1.scratch_ok⟩
          obtain ⟨hw_wr, hrefs_wr, hsub_wr, hnodup_wr, hgarb_wr, hlits_wr⟩ :=
            addArenaClause_preserves_fullWitness hlen hw hge3 hlen_mv harL_len hal1_le htmp_all.1
              htmp_all.2.1 htmp_all.2.2 hholdL hnsL hngL hszL (fun j hj => hlitsL j (by omega))
          have hw1_mem : ((BitVec.ofNat 64 s.core.arena_len).setWidth 32).toNat ∈
              fullArenaClauseRefsCore s_wr.core := by
            rw [hcr_32, bv32_ofNat_toNat (by omega)]
            change s.core.arena_len ∈ fullArenaClauseRefs s_wr
            rw [hrefs_wr]; simp
          c0_hsteps
          c0_call hWatchPush
          refine ⟨c, s_wr, R, rfl, hlen_wr, hw_wr.watches.layout, (fun h => by cases h),
            (fun _ => ⟨hw0_1_ns, hw1_ns⟩), hmL, ?_⟩
          intro ok1 wvec1 wstk1 wlen1 wu1 wsort1 m_p1
          dsimp only
          rintro hlen_p1 hlay_p1 hoth_p1 hok1t hok1f hm_p1
          let s_p1 : FullState :=
            { s_wr with
              core := { s_wr.core with wvec := wvec1, wstk := wstk1, wlen := wlen1,
                                       wusable := wu1 }
              scratch := { s_wr.scratch with wsort := wsort1 } }
          c0_hsteps
          · -- `ok1 = true` -> push 2 on `l1`
            have hok1_parts := hok1t (by
              rename_i hc; cases h : ok1 <;> (try rw [h] at hc) <;>
                first | rfl | contradiction | cases hc | exact absurd hc (by decide))
            have hwat_p1 : ModeWatchesInv F_cur s_p1.core := by
              refine fullWatchPush_preserves_modeWatchesInv hw_wr.watches hlay_p1 rfl rfl
                (fun _ h => h) (fun h => by cases h) (fun _ => ?_) hoth_p1 hok1t
                (fun h hlt => (hok1f h).1 hlt)
              refine ⟨by change ((l1 &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32
                         exact bv32_large_msb_zero l1,
                fun hdm => absurd hdm0 hdm, hw1_lt, hw1_mem⟩
            c0_call hWatchPush
            refine ⟨c, s_p1, R, rfl, hlen_p1, hlay_p1, (fun h => by cases h),
              (fun _ => ⟨hw0_0_ns, hw1_ns⟩), hm_p1, ?_⟩
            intro ok2 wvec2 wstk2 wlen2 wu2 wsort2 m_p2
            dsimp only
            rintro hlen_p2 hlay_p2 hoth_p2 hok2t hok2f hm_p2
            let s_p2 : FullState :=
              { s_p1 with
                core := { s_p1.core with wvec := wvec2, wstk := wstk2, wlen := wlen2,
                                         wusable := wu2 }
                scratch := { s_p1.scratch with wsort := wsort2 } }
            have hwat_p2 : ModeWatchesInv F_cur s_p2.core := by
              refine fullWatchPush_preserves_modeWatchesInv hwat_p1 hlay_p2 rfl rfl
                (fun _ h => h) (fun h => by cases h) (fun _ => ?_) hoth_p2 hok2t
                (fun h hlt => (hok2f h).1 hlt)
              refine ⟨by change ((l0 &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32
                         exact bv32_large_msb_zero l0,
                fun hdm => absurd hdm0 hdm, hw1_lt, hw1_mem⟩
            c0_hsteps_nogrp
            · -- `ok2 = true` -> `if (red)` counters + return `cref`
              c0_hfast_nobound
              all_goals
                exact add_clause_large_ok_post hlen_p2 hw_wr hwat_p2 hrefs_wr hsub_wr hnodup_wr
                  hgarb_wr hlits_wr (by assumption) hQ
            · -- `ok2 = false` -> `full_watch_pop_c0(h, l0, 2)` + rollback
              c0_hsteps
              have hok2_parts := hok2f (by
                rename_i hc; cases h : ok2 <;> (try rw [h] at hc) <;>
                  first | rfl | contradiction | cases hc | exact absurd hc (by decide))
              have hsz2_l0 : fullWatchSize s_p2 l0.toNat = fullWatchSize s_p1 l0.toNat ∧
                  ∀ idx < fullWatchSize s_p1 l0.toNat,
                    s_p2.core.wstk[fullWatchOff s_p2 l0.toNat + idx]? =
                      s_p1.core.wstk[fullWatchOff s_p1 l0.toNat + idx]? :=
                hoth_p2 l0.toNat hl0_lt (fun h => hne01 (BitVec.eq_of_toNat_eq h))
              c0_call hWatchPop
              refine ⟨c, s_p2, R, rfl, hlen_p2, hlay_p2,
                (by change l0.toNat < 2 * s_p2.core.cur_vars; exact hl0_lt), by decide,
                ?_, hm_p2, ?_⟩
              · have hpush1 : fullWatchSize s_p1 l0.toNat = fullWatchSize s_wr l0.toNat + 2 :=
                  hok1_parts.2.2.1
                change fullWatchSize s_p2 l0.toNat ≥ 2; omega
              · intro wvec3 wstk3 wu3 m3
                dsimp only; rintro hlen3 hlay3 hoth3 hoff3 hsz3 hpf3 hm3
                c0_hsteps
                let c_rb : FullCoreState :=
                  { s.core with arena := arL, wvec := wvec3, wstk := wstk3, wlen := wlen2,
                                wusable := wu3 }
                let s_rb : FullState :=
                  { s with core := c_rb, scratch := { s.scratch with wsort := wsort2 } }
                have hlen_rb : s_rb.LengthsOk c :=
                  ⟨{ hlen3.core_ok with arena_len_le := hcl.arena_len_le }, hlen3.scratch_ok⟩
                have hlay_rb : WatchStackLayout c_rb := hlay3.with_wstk rfl rfl rfl rfl
                have hrel_rb : ∀ l < 2 * s.core.cur_vars,
                    fullWatchSizeCore c_rb l = fullWatchSizeCore s.core l ∧
                    ∀ idx < fullWatchSizeCore s.core l,
                      wstk3[fullWatchOffCore c_rb l + idx]? =
                        s.core.wstk[fullWatchOffCore s.core l + idx]? := by
                  intro l hl; by_cases hle : l = l0.toNat
                  · subst hle
                    have h1sz : fullWatchSize s_p1 l0.toNat = fullWatchSize s_wr l0.toNat + 2 :=
                      hok1_parts.2.2.1
                    have h1pf : ∀ idx < fullWatchSize s_wr l0.toNat,
                        wstk1[fullWatchOff s_p1 l0.toNat + idx]? =
                          s_wr.core.wstk[fullWatchOff s_wr l0.toNat + idx]? := hok1_parts.2.2.2.1
                    have hsz3_l0 :
                        fullWatchSizeCore c_rb l0.toNat = fullWatchSize s_p2 l0.toNat - 2 := hsz3
                    have hpf3_l0 : ∀ idx < fullWatchSize s_p2 l0.toNat - 2,
                        wstk3[fullWatchOffCore c_rb l0.toNat + idx]? =
                          s_p2.core.wstk[fullWatchOff s_p2 l0.toNat + idx]? := hpf3
                    have hsz2_l0' := hsz2_l0
                    dsimp [fullWatchSize, fullWatchSizeCore, fullWatchOffCore, fullWatchOff, s_rb,
                      c_rb, s_p2, s_p1, s_wr] at h1sz h1pf hsz3_l0 hpf3_l0 hsz2_l0' ⊢
                    refine ⟨by omega, fun idx hidx => ?_⟩
                    rw [hpf3_l0 idx (by omega), hsz2_l0'.2 idx (by omega), h1pf idx hidx]
                  · obtain ⟨h3a, h3b, h3pf⟩ := hoth3 l hl hle
                    have h2 : fullWatchSize s_p2 l = fullWatchSize s_p1 l ∧
                        ∀ idx < fullWatchSize s_p1 l,
                          s_p2.core.wstk[fullWatchOff s_p2 l + idx]? =
                            s_p1.core.wstk[fullWatchOff s_p1 l + idx]? := by
                      by_cases hl1 : l = l1.toNat
                      · subst hl1; exact hok2_parts.1 hl
                      · exact hoth_p2 l hl hl1
                    obtain ⟨h2sz, h2pf⟩ := h2
                    obtain ⟨h1sz, h1pf⟩ := hoth_p1 l hl hle
                    dsimp [c_rb, fullWatchOffCore, fullWatchOff, fullWatchSize,
                      fullWatchSizeCore, s_p2, s_p1, s_wr] at h3a h3b h3pf h2sz h2pf h1sz h1pf ⊢
                    refine ⟨by omega, fun idx hidx => ?_⟩
                    first
                    | rw [h3a, h3pf idx (by omega), h2pf idx (by omega), h1pf idx hidx]
                    | rw [h3pf idx (by omega), h2pf idx (by omega), h1pf idx hidx]
                exact add_clause_large_rollback_post (len := len.toNat)
                  hlen hw hlen_rb hlay_rb hholdL hrel_rb (by assumption) hQ
          · -- `ok1 = false` -> `h->arena_len = cref; return 0xFFFFFFFF`
            c0_hsteps
            have hok1_parts := hok1f (by
              rename_i hc; cases h : ok1 <;> (try rw [h] at hc) <;>
                first | rfl | contradiction | cases hc | exact absurd hc (by decide))
            let c_rb : FullCoreState :=
              { s.core with arena := arL, wvec := wvec1, wstk := wstk1, wlen := wlen1,
                            wusable := wu1 }
            let s_rb : FullState :=
              { s with core := c_rb, scratch := { s.scratch with wsort := wsort1 } }
            have hlen_rb : s_rb.LengthsOk c :=
              ⟨{ hlen_p1.core_ok with arena_len_le := hcl.arena_len_le }, hlen_p1.scratch_ok⟩
            have hlay_rb : WatchStackLayout c_rb := hlay_p1.with_wstk rfl rfl rfl rfl
            have hrel_rb : ∀ l < 2 * s.core.cur_vars,
                fullWatchSizeCore c_rb l = fullWatchSizeCore s.core l ∧
                ∀ idx < fullWatchSizeCore s.core l,
                  wstk1[fullWatchOffCore c_rb l + idx]? =
                    s.core.wstk[fullWatchOffCore s.core l + idx]? := by
              intro l hl; by_cases hle : l = l0.toNat
              · subst hle; exact hok1_parts.1 hl
              · exact hoth_p1 l hl hle
            exact add_clause_large_rollback_post (len := len.toNat)
              hlen hw hlen_rb hlay_rb hholdL hrel_rb (by assumption) hQ

end LeanQbe.T.Examples.Kissat.Proof.Clause
