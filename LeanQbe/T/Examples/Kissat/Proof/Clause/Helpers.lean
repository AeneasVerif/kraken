/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
public import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts4
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics

/-!
# Shared Pure, Witness & Watch Helpers for `Proof.Clause` (`Proof.Clause.Helpers`)

Pure `BitVec` / literal helpers plus canonical `FullWitnessInv` and `ModeWatchesInv`
preservation lemmas shared by `Wp0` (`full_add_bin_m6`, `full_add_bin`, `full_add_unit`)
and `Wp1` (`full_add_clause`):
1. `BitVec` tagging (`PW_LIT_MASK`, `PW_BIN_FLAG`), bounds, and arena index arithmetic.
2. `modeWatchesInv_of_slice_relocate` & `fullWatchPopC0_after_push_fail_modeWatchesInv`.
3. `rollback_preserves_fullWitness` (restoring `arena_len` preserves `FullWitnessInv`).
4. `addArenaClause_preserves_fullWitness` (large clause append on `FullWitnessInv`).
5. `assignLevel0_preserves_fullWitness` (level-0 unit assignment on `FullWitnessInv`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Clause

open Std.Sat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullBvaFwdTactics

/-! ## 1. Pure BitVec & Literal Bounds -/

theorem lit_lt_0x7FFFFFFF {c : FullCfg} {cv l : Nat}
    (hcv : cv ≤ c.max_vars) (hl : l < 2 * cv) : l < 0x7FFFFFFF := by
  have hm := c.hmaxv
  unfold dimacsBound at hm
  omega

theorem bv32_tag_bin_msb_ne (w0 : BitVec 32) :
    (((w0 &&& 0x7FFFFFFF#32) ||| 0x80000000#32) &&& 0x80000000#32) ≠ 0#32 := by
  intro h
  have hb := congrArg (fun x => BitVec.getLsbD x 31) h
  simp at hb

private theorem nat_xor1_xor1 (l : Nat) : (l ^^^ 1) ^^^ 1 = l := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_xor]
  cases l.testBit i <;> cases (1 : Nat).testBit i <;> rfl

theorem bv32_tag_bin_unmask (w0 : BitVec 32) :
    (((w0 &&& 0x7FFFFFFF#32) ||| 0x80000000#32) &&& 0x7FFFFFFF#32) = (w0 &&& 0x7FFFFFFF#32) := by
  have hdist : ∀ a b c : BitVec 32, (a ||| b) &&& c = (a &&& c) ||| (b &&& c) := by
    intro a b c; apply BitVec.eq_of_getLsbD_eq; intro i _
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> rfl
  rw [hdist, BitVec.and_assoc,
    show (0x7FFFFFFF#32 &&& 0x7FFFFFFF#32 : BitVec 32) = 0x7FFFFFFF#32 from rfl,
    show (0x80000000#32 &&& 0x7FFFFFFF#32 : BitVec 32) = 0#32 from rfl, BitVec.or_zero]

theorem bv32_tag_bin_ne_sent {w0 : BitVec 32} (h : w0.toNat < 0x7FFFFFFF) :
    ((w0 &&& 0x7FFFFFFF#32) ||| 0x80000000#32) ≠ 0xFFFFFFFF#32 := by
  intro heq
  have hmask := congrArg (· &&& 0x7FFFFFFF#32) heq
  rw [bv32_tag_bin_unmask, bv32_and_mask_eq (by omega)] at hmask
  have hrhs : (0xFFFFFFFF#32 &&& 0x7FFFFFFF#32 : BitVec 32) = 0x7FFFFFFF#32 := rfl
  rw [hrhs] at hmask
  have hb := congrArg BitVec.toNat hmask
  have h7f : (0x7FFFFFFF#32 : BitVec 32).toNat = 0x7FFFFFFF := rfl
  omega

theorem bv32_large_msb_zero (w0 : BitVec 32) :
    ((w0 &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32 := by
  rw [BitVec.and_assoc, show (0x7FFFFFFF#32 &&& 0x80000000#32 : BitVec 32) = 0#32 from rfl,
    BitVec.and_zero]

theorem bv32_and_litMask_ne_sent {w0 : BitVec 32} (h : w0.toNat < 0x7FFFFFFF) :
    (w0 &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32 := by
  intro heq
  have h1 : (w0 &&& 0x7FFFFFFF#32) = w0 := bv32_and_mask_eq (by omega)
  rw [h1] at heq
  have hb := congrArg BitVec.toNat heq
  have hs : (0xFFFFFFFF#32 : BitVec 32).toNat = 0xFFFFFFFF := rfl
  omega

theorem bv32_shr1_lt_vars {lit : BitVec 32} {nv : Nat} (hlt : lit.toNat < 2 * nv) :
    (lit >>> 1#32).toNat < nv := by
  rw [bv32_shr1_toNat]
  omega

theorem bv64_setWidth32_eq {x : BitVec 64} (hx : x.toNat < 2 ^ 32) :
    (x.setWidth 32).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx]

theorem bv64_add3_add_toNat {a b : Nat} (h : a + 3 + b < 2 ^ 64) :
    (BitVec.ofNat 64 a + 3#64 + BitVec.ofNat 64 b).toNat = a + 3 + b := by
  have ha : (BitVec.ofNat 64 a + 3#64).toNat = a + 3 := by
    rw [BitVec.toNat_add, bv64_ofNat_toNat (by omega), show (3#64 : BitVec 64).toNat = 3 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_add, ha, bv64_ofNat_toNat (by omega), Nat.mod_eq_of_lt (by omega)]

/-! ## 2. ModeWatchesInv & Witness Updaters -/

theorem fullWitnessInv_with_watches_meta {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    {flags' wvec' wstk' : List (BitVec 32)} {wlen' : Nat}
    {wusable' fred' ni' nr' nb' oom' : BitVec 64}
    (hwat : ModeWatchesInv F_cur
      { k with flags := flags', wvec := wvec', wstk := wstk', wlen := wlen',
               wusable := wusable', first_reducible := fred', num_irred := ni',
               num_redundant := nr', num_binary := nb', oom := oom' }) :
    FullWitnessInv c F0 F_cur
      { k with flags := flags', wvec := wvec', wstk := wstk', wlen := wlen',
               wusable := wusable', first_reducible := fred', num_irred := ni',
               num_redundant := nr', num_binary := nb', oom := oom' } :=
  { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }, watches := hwat }

theorem modeWatchesInv_of_slice_relocate {F_cur : List (List Nat)} {k0 k' : FullCoreState}
    (hw0 : ModeWatchesInv F_cur k0) (hlay : WatchStackLayout k')
    (hv : k'.cur_vars = k0.cur_vars) (hdm : k'.dense_mode = k0.dense_mode)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k0, r ∈ fullArenaClauseRefsCore k')
    (hrel : ∀ l < 2 * k0.cur_vars,
      fullWatchSizeCore k' l = fullWatchSizeCore k0 l ∧
      ∀ idx < fullWatchSizeCore k0 l,
        k'.wstk[fullWatchOffCore k' l + idx]? = k0.wstk[fullWatchOffCore k0 l + idx]?) :
    ModeWatchesInv F_cur k' := by
  have hF : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ h => h
  by_cases hzero : k'.dense_mode = 0#64
  · have hzero0 : k0.dense_mode = 0#64 := hdm ▸ hzero
    unfold ModeWatchesInv at hw0 ⊢
    simp only [hzero, hzero0, ↓reduceIte] at hw0 ⊢
    refine ⟨hlay, fun l hl => ?_⟩
    have hl0 : l < 2 * k0.cur_vars := hv ▸ hl
    rcases hrel l hl0 with ⟨hsz, hslice⟩
    rw [hsz]
    exact fullWatchSlice_relocate hF (by omega) hsub hslice (hw0.slices l hl0)
  · have hzero0 : k0.dense_mode ≠ 0#64 := fun h => hzero (hdm.trans h)
    unfold ModeWatchesInv at hw0 ⊢
    simp only [hzero, hzero0, ↓reduceIte] at hw0 ⊢
    refine ⟨hlay, fun l hl => ?_⟩
    have hl0 : l < 2 * k0.cur_vars := hv ▸ hl
    rcases hrel l hl0 with ⟨hsz, hslice⟩
    rw [hsz]
    exact DenseWatchSliceOk.relocate hF (by omega) hsub hslice (hw0.slices l hl0)

theorem fullWatchPopC0_after_push_fail_modeWatchesInv {F_cur : List (List Nat)}
    {k0 k1 k2 k3 : FullCoreState} {lit0 cnt : Nat}
    (hw0 : ModeWatchesInv F_cur k0) (hw2 : ModeWatchesInv F_cur k2)
    (hlay3 : WatchStackLayout k3)
    (hv1 : k1.cur_vars = k0.cur_vars) (hv2 : k2.cur_vars = k1.cur_vars)
    (hv3 : k3.cur_vars = k2.cur_vars)
    (hdm1 : k1.dense_mode = k0.dense_mode) (hdm2 : k2.dense_mode = k1.dense_mode)
    (hdm3 : k3.dense_mode = k2.dense_mode)
    (har1 : k1.arena = k0.arena) (hal1 : k1.arena_len = k0.arena_len)
    (har2 : k2.arena = k1.arena) (hal2 : k2.arena_len = k1.arena_len)
    (har3 : k3.arena = k2.arena) (hal3 : k3.arena_len = k2.arena_len)
    (hlit0 : lit0 < 2 * k0.cur_vars)
    (h1_sz : fullWatchSizeCore k1 lit0 = fullWatchSizeCore k0 lit0 + cnt)
    (h1_pfx : ∀ idx < fullWatchSizeCore k0 lit0,
      k1.wstk[fullWatchOffCore k1 lit0 + idx]? = k0.wstk[fullWatchOffCore k0 lit0 + idx]?)
    (h2_lit0 : fullWatchSizeCore k2 lit0 = fullWatchSizeCore k1 lit0 ∧
      ∀ idx < fullWatchSizeCore k1 lit0,
        k2.wstk[fullWatchOffCore k2 lit0 + idx]? = k1.wstk[fullWatchOffCore k1 lit0 + idx]?)
    (h3_lit0_sz : fullWatchSizeCore k3 lit0 = fullWatchSizeCore k2 lit0 - cnt)
    (h3_lit0_pfx : ∀ idx < fullWatchSizeCore k2 lit0 - cnt,
      k3.wstk[fullWatchOffCore k3 lit0 + idx]? = k2.wstk[fullWatchOffCore k2 lit0 + idx]?)
    (h3_other : ∀ l < 2 * k2.cur_vars, l ≠ lit0 →
      fullWatchOffCore k3 l = fullWatchOffCore k2 l ∧
      fullWatchSizeCore k3 l = fullWatchSizeCore k2 l ∧
      ∀ idx < fullWatchSizeCore k2 l,
        k3.wstk[fullWatchOffCore k3 l + idx]? = k2.wstk[fullWatchOffCore k2 l + idx]?) :
    ModeWatchesInv F_cur k3 := by
  have hF : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ h => h
  have href03 : ∀ r ∈ fullArenaClauseRefsCore k0, r ∈ fullArenaClauseRefsCore k3 :=
    fun r hr => by unfold fullArenaClauseRefsCore at hr ⊢; rwa [har3, hal3, har2, hal2, har1, hal1]
  have href23 : ∀ r ∈ fullArenaClauseRefsCore k2, r ∈ fullArenaClauseRefsCore k3 :=
    fun r hr => by unfold fullArenaClauseRefsCore at hr ⊢; rwa [har3, hal3]
  have hsz3_lit0 : fullWatchSizeCore k3 lit0 = fullWatchSizeCore k0 lit0 := by omega
  have hpf3_lit0 : ∀ idx < fullWatchSizeCore k0 lit0,
      k3.wstk[fullWatchOffCore k3 lit0 + idx]? = k0.wstk[fullWatchOffCore k0 lit0 + idx]? :=
    fun idx hidx => by rw [h3_lit0_pfx idx (by omega), h2_lit0.2 idx (by omega), h1_pfx idx hidx]
  by_cases hdm : k3.dense_mode = 0#64
  · have hdm0 : k0.dense_mode = 0#64 := by rwa [← hdm1, ← hdm2, ← hdm3]
    have hdm2' : k2.dense_mode = 0#64 := by rwa [← hdm3]
    unfold ModeWatchesInv at hw0 hw2 ⊢
    simp only [hdm, hdm0, hdm2', ↓reduceIte] at hw0 hw2 ⊢
    refine ⟨hlay3, fun l hl => ?_⟩
    by_cases hle : l = lit0
    · subst hle; rw [hsz3_lit0]
      exact fullWatchSlice_relocate hF (by omega) href03 hpf3_lit0 (hw0.slices l hlit0)
    · have hl2 : l < 2 * k2.cur_vars := by omega
      rcases h3_other l hl2 hle with ⟨_, hsz, hpf⟩
      rw [hsz]
      exact fullWatchSlice_relocate hF (by omega) href23 hpf (hw2.slices l hl2)
  · have hdm0 : k0.dense_mode ≠ 0#64 := fun h => hdm (by rw [hdm3, hdm2, hdm1, h])
    have hdm2' : k2.dense_mode ≠ 0#64 := fun h => hdm (hdm3.trans h)
    unfold ModeWatchesInv at hw0 hw2 ⊢
    simp only [hdm, hdm0, hdm2', ↓reduceIte] at hw0 hw2 ⊢
    refine ⟨hlay3, fun l hl => ?_⟩
    by_cases hle : l = lit0
    · subst hle; rw [hsz3_lit0]
      exact DenseWatchSliceOk.relocate hF (by omega) href03 hpf3_lit0 (hw0.slices l hlit0)
    · have hl2 : l < 2 * k2.cur_vars := by omega
      rcases h3_other l hl2 hle with ⟨_, hsz, hpf⟩
      rw [hsz]
      exact DenseWatchSliceOk.relocate hF (by omega) href23 hpf (hw2.slices l hl2)

/-! ## 3. Arena Rollback & Clause Append Preservation -/

theorem rollback_preserves_fullWitness {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    {arena' wvec' wstk' : List (BitVec 32)} {wlen' : Nat} {wusable' : BitVec 64}
    (hk_len : k.arena_len ≤ k.arena.length) (hk'_len : k.arena_len ≤ arena'.length)
    (hhold : ∀ i < k.arena_len, arena'[i]? = k.arena[i]?)
    (hwat : ModeWatchesInv F_cur
      { k with arena := arena', wvec := wvec', wstk := wstk',
               wlen := wlen', wusable := wusable' }) :
    FullWitnessInv c F0 F_cur
      { k with arena := arena', wvec := wvec', wstk := wstk',
               wlen := wlen', wusable := wusable' } := by
  let k' : FullCoreState :=
    { k with arena := arena', wvec := wvec', wstk := wstk',
             wlen := wlen', wusable := wusable' }
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaNextOff k'.arena k.arena_len r = fullArenaNextOff k.arena k.arena_len r :=
    hw.arena.arenaNextOff_extend (arena' := arena') (alen' := k.arena_len) (Nat.le_refl _) hhold
  have hrefs : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hold_sz : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r := fun r hr => by
    have := (hw.arena.refs_wf r hr).1
    unfold fullArenaClauseSizeCore k'; simp [hhold (r + 2) (by omega)]
  have hold_garb : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r := fun r hr => by
    have := (hw.arena.refs_wf r hr).1
    unfold fullArenaClauseGarbCore fullArenaHdrCore k'; simp [hhold r (by omega)]
  have hold_lits : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r := fun r hr => by
    have hwf := hw.arena.refs_wf r hr
    have hwf_sub := hwf.2.2.1
    have hwf_le := hwf.2.2.2.1
    have hbd : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena_len := by omega
    exact fullArenaClauseLitsCore_eq_of_hold (by omega) (by dsimp [k']; omega) (hold_sz r hr)
      fun j hj => by dsimp [k']; exact hhold (r + 3 + j) (by omega)
  have har' : FullArenaClausesInv c F_cur k' :=
    { len_ok := hw.arena.len_ok
      refs_wf := fun r hr => by
        rw [hrefs] at hr
        have hwf := hw.arena.refs_wf r hr
        rw [hold_sz r hr]
        simpa [k', hnxt r hr] using hwf
      shrk_term := fun r hr hsh => by
        rw [hrefs] at hr
        have hwf := hw.arena.refs_wf r hr
        have hhd : fullArenaHdrCore k' r = fullArenaHdrCore k r := by
          unfold fullArenaHdrCore k'; simp [hhold r (by omega)]
        rw [hhd] at hsh
        obtain ⟨t, ht1, ht2, hts⟩ := hw.arena.shrk_term r hr hsh
        refine ⟨t, by simpa [hold_sz r hr] using ht1, ht2, ?_⟩
        dsimp only [k']; rw [hhold t ht2]; exact hts
      lits_lt := fun r hr hng => by
        rw [hrefs] at hr
        rw [hold_lits r hr]; exact hw.arena.lits_lt r hr (hold_garb r hr ▸ hng)
      entails := fun r hr hng => by
        rw [hrefs] at hr
        rw [hold_lits r hr]; exact hw.arena.entails r hr (hold_garb r hr ▸ hng) }
  exact
    { hw with
      arena := har'
      watches := hwat
      reason_inv := fun idx hidx hne => by
        have hr := hw.reason_inv idx hidx hne
        dsimp only [k'] at hr ⊢
        by_cases hf : ((k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32) &&& 0x80000000#32) ≠ 0#32
        · simpa [hf] using hr
        · simp only [hf, ↓reduceIte] at hr ⊢
          rcases hr with ⟨href, hgarb, hmem⟩
          refine ⟨hrefs ▸ href, hold_garb _ href ▸ hgarb, fun q hq =>
            hmem q (hold_lits _ href ▸ hq)⟩
      reason_lit_mem := fun idx hidx hne hf => by
        have href : (k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefsCore k := by
          have hr := hw.reason_inv idx hidx hne
          simp [hf] at hr; exact hr.1
        dsimp only [k']
        rw [hold_lits _ href]
        exact hw.reason_lit_mem idx hidx hne hf }

abbrev addArenaState (s : FullState) (arena' : List (BitVec 32)) (len : Nat) : FullState :=
  let c' : FullCoreState :=
    { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len }
  { s with core := c' }

theorem addArenaClause_preserves_fullWitness {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState}
    (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    {len : Nat} (hge3 : 3 ≤ len) (hlen_mv : len ≤ c.max_vars)
    {arena' : List (BitVec 32)}
    (har_len : arena'.length = c.arena_cap)
    (hal_le : s.core.arena_len + 3 + len ≤ c.arena_cap)
    (hlits_lt : ∀ l ∈ (s.core.tmp.take len).map BitVec.toNat, l < 2 * s.core.cur_vars)
    (hnodup : ((s.core.tmp.take len).map fun x => x.toNat / 2).Nodup)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s.core.tmp.take len).map BitVec.toNat)))
    (hhold : ∀ i < s.core.arena_len, arena'[i]? = s.core.arena[i]?)
    (hnoshrk : (arena'[s.core.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hnogarb : (arena'[s.core.arena_len]?.getD 0#32 &&& 0x00080000#32) = 0#32)
    (hsz : (arena'[s.core.arena_len + 2]?.getD 0#32).toNat = len)
    (hlits_eq : ∀ i < len, arena'[s.core.arena_len + 3 + i]? = s.core.tmp[i]?) :
    let s' := addArenaState s arena' len
    FullWitnessInv c F0 F_cur s'.core ∧
    fullArenaClauseRefs s' = fullArenaClauseRefs s ++ [s.core.arena_len] ∧
    (∀ ref ∈ fullArenaClauseRefs s, ref ∈ fullArenaClauseRefs s') ∧
    (FullArenaVarsNodup s → FullArenaVarsNodup s') ∧
    fullArenaClauseGarb s' s.core.arena_len = false ∧
    fullArenaClauseLits s' s.core.arena_len = (s.core.tmp.take len).map BitVec.toNat := by
  intro s'
  have hcl := hlen.core_ok
  have hal_le_s : s.core.arena_len ≤ s.core.arena.length := by
    rw [hcl.arena_len_arr]; exact hcl.arena_len_le
  have hal_le' : s.core.arena_len + 3 + len ≤ arena'.length := by
    rw [har_len]; exact hal_le
  have htmp_len : len ≤ s.core.tmp.length := by rw [hcl.tmp_len_arr]; exact hlen_mv
  have hlits_new :
      fullArenaClauseLitsCore s'.core s.core.arena_len =
        (s.core.tmp.take len).map BitVec.toNat := by
    unfold fullArenaClauseLitsCore fullArenaClauseSizeCore
    dsimp only [s', addArenaState]
    rw [hsz]
    congr 1
    apply List.ext_getElem
    · simp [htmp_len, List.length_take, List.length_drop]; omega
    · intro i hi1 hi2
      have hi : i < len := by simp [List.length_take] at hi2; omega
      have h1 : s.core.arena_len + 3 + i < arena'.length := by omega
      have h2 : i < s.core.tmp.length := by omega
      simp [List.getElem_take, List.getElem_drop]
      have heq := hlits_eq i hi
      rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] at heq
      exact Option.some.inj heq
  have hrefs :
      fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core ++ [s.core.arena_len] :=
    fullArenaClauseRefsCore_append hw.arena hge3 (k' := s'.core) rfl hhold hnoshrk hsz
  have href_sub : ∀ r ∈ fullArenaClauseRefs s, r ∈ fullArenaClauseRefs s' := fun r hr => by
    unfold fullArenaClauseRefs; rw [hrefs]; exact List.mem_append_left _ hr
  have hnxt_old : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaNextOff arena' (s.core.arena_len + 3 + len) r =
        fullArenaNextOff s.core.arena s.core.arena_len r :=
    fun r hr => hw.arena.arenaNextOff_extend (by omega) hhold r hr
  have hnxt_new :
      fullArenaNextOff arena' (s.core.arena_len + 3 + len) s.core.arena_len =
        s.core.arena_len + 3 + len := by
    unfold fullArenaNextOff; simp [hsz, hnoshrk]
  have hold_garb : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := fun r hr => by
    have := (hw.arena.refs_wf r hr).1
    unfold fullArenaClauseGarbCore fullArenaHdrCore s'; simp [hhold r (by omega)]
  have hold_sz : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := fun r hr => by
    have := (hw.arena.refs_wf r hr).1
    unfold fullArenaClauseSizeCore s'; simp [hhold (r + 2) (by omega)]
  have hold_lits : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := fun r hr => by
    have hwf := hw.arena.refs_wf r hr
    have hwf_sub := hwf.2.2.1
    have hwf_le := hwf.2.2.2.1
    have hbd : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena_len := by omega
    exact fullArenaClauseLitsCore_eq_of_hold (by omega)
      (by dsimp only [s', addArenaState]; omega) (hold_sz r hr)
      fun j hj => by dsimp [s']; exact hhold (r + 3 + j) (by omega)
  have hnew_garb : fullArenaClauseGarb s' s.core.arena_len = false := by
    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore s'
    simp [hnogarb]
  have hnew_sz' : fullArenaClauseSizeCore s'.core s.core.arena_len = len := hsz
  have har' : FullArenaClausesInv c F_cur s'.core :=
    { len_ok := .inr (by dsimp only [s', addArenaState]; omega)
      refs_wf := fun r hr => by
        rw [hrefs, List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | rfl
        · have hwf := hw.arena.refs_wf r hr
          rw [hold_sz r hr]; dsimp only [s']; rw [hnxt_old r hr]
          refine ⟨by omega, hwf.2.1, hwf.2.2.1, by omega, ?_⟩
          rcases hwf.2.2.2.2 with h1 | h1 <;> exact .inr (by omega)
        · rw [hnew_sz']; dsimp only [s']; rw [hnxt_new]
          exact ⟨by omega, hge3, Nat.le_refl _, Nat.le_refl _, .inl rfl⟩
      shrk_term := fun r hr hsh => by
        rw [hrefs, List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | rfl
        · have hwf := hw.arena.refs_wf r hr
          have hhd : fullArenaHdrCore s'.core r = fullArenaHdrCore s.core r := by
            unfold fullArenaHdrCore s'; simp [hhold r (by omega)]
          rw [hhd] at hsh
          obtain ⟨t, ht1, ht2, hts⟩ := hw.arena.shrk_term r hr hsh
          refine ⟨t, by rw [hold_sz r hr]; exact ht1,
            by dsimp only [s', addArenaState]; omega, ?_⟩
          dsimp only [s']; rw [hhold t ht2]; exact hts
        · exact absurd hnoshrk (by simpa [fullArenaHdrCore, s'] using hsh)
      lits_lt := fun r hr hng => by
        rw [hrefs, List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | rfl
        · rw [hold_lits r hr]; exact hw.arena.lits_lt r hr (hold_garb r hr ▸ hng)
        · rw [hlits_new]; exact hlits_lt
      entails := fun r hr hng => by
        rw [hrefs, List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | rfl
        · rw [hold_lits r hr]; exact hw.arena.entails r hr (hold_garb r hr ▸ hng)
        · rw [hlits_new]; exact hent }
  have hwat' : ModeWatchesInv F_cur s'.core :=
    modeWatchesInv_of_slice_relocate hw.watches
      (hw.watches.layout.with_wstk rfl rfl rfl rfl) rfl rfl
      (fun r hr => href_sub r hr)
      (fun l _ => ⟨rfl, fun _ _ => rfl⟩)
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := har'
      watches := hwat'
      reason_inv := fun idx hidx hne => by
        have hr := hw.reason_inv idx hidx hne
        dsimp only [s'] at hr ⊢
        by_cases hf : ((s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32) &&& 0x80000000#32) ≠ 0#32
        · simpa [hf] using hr
        · simp only [hf, ↓reduceIte] at hr ⊢
          rcases hr with ⟨href, hgarb, hmem⟩
          refine ⟨href_sub _ href, hold_garb _ href ▸ hgarb, fun q hq =>
            hmem q (hold_lits _ href ▸ hq)⟩
      reason_lit_mem := fun idx hidx hne hf => by
        dsimp only [s', addArenaState] at hf
        have href : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32).toNat ∈ fullArenaClauseRefsCore s.core := by
          have hr := hw.reason_inv idx hidx hne
          simp [hf] at hr
          exact hr.1
        dsimp only [s']
        rw [hold_lits _ href]
        exact hw.reason_lit_mem idx hidx hne hf }
  have hnodup' : FullArenaVarsNodup s → FullArenaVarsNodup s' := by
    intro hnd r hr hng
    unfold fullArenaClauseRefs at hr; rw [hrefs, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · unfold fullArenaClauseLits
      unfold fullArenaClauseGarb at hng
      have hgarb_eq : fullArenaClauseGarbCore s.core r = false := by
        rw [← hold_garb r hr]; exact hng
      rw [hold_lits r hr]
      exact hnd r hr hgarb_eq
    · unfold fullArenaClauseLits; rw [hlits_new, List.map_map]
      exact hnodup
  exact ⟨hw', hrefs, href_sub, hnodup', hnew_garb, hlits_new⟩

/-! ## 4. Level-0 Assignment Witness Preservation -/

theorem assignLevel0_preserves_fullWitness {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hlen : s.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur s.core) (hcl0 : s.core.cur_level = 0)
    {lit : BitVec 32} (hlt : lit.toNat < 2 * s.core.cur_vars)
    (hun : s.core.vals[lit.toNat]?.getD 0#8 = 0#8)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]))
    (flags' : List (BitVec 32)) (unass' unfl' : BitVec 64) :
    FullWitnessInv c F0 F_cur
      { (s.core) with
        vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
        flags := flags'
        lvl := s.core.lvl.set (lit.toNat / 2) 0#32
        rsns := s.core.rsns.set (lit.toNat / 2) 0xFFFFFFFF#32
        trl := s.core.trl.set s.core.trail_end lit
        trail_pos := s.core.trail_pos.set (lit.toNat / 2) (BitVec.ofNat 32 s.core.trail_end)
        trail_end := s.core.trail_end + 1
        unassigned := unass'
        unflushed := unfl' } := by
  let k' : FullCoreState :=
    { (s.core) with
      vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
      flags := flags'
      lvl := s.core.lvl.set (lit.toNat / 2) 0#32
      rsns := s.core.rsns.set (lit.toNat / 2) 0xFFFFFFFF#32
      trl := s.core.trl.set s.core.trail_end lit
      trail_pos := s.core.trail_pos.set (lit.toNat / 2) (BitVec.ofNat 32 s.core.trail_end)
      trail_end := s.core.trail_end + 1
      unassigned := unass'
      unflushed := unfl' }
  have hcl := hlen.core_ok
  have hte_lt : s.core.trail_end < s.core.cur_vars := hw.trail_end_lt_of_unassigned hlt hun
  have hte_mv : s.core.trail_end < c.max_vars := Nat.lt_of_lt_of_le hte_lt hcl.cur_vars_le
  have hte_trl : s.core.trail_end < s.core.trl.length := by rw [hcl.trl_len]; exact hte_mv
  have hte_32 : s.core.trail_end < 2 ^ 32 := Nat.lt_trans hte_mv (fullInv_max_vars_lt32 c)
  have hv_lt : lit.toNat / 2 < s.core.cur_vars := by omega
  have hv_mv : lit.toNat / 2 < c.max_vars := Nat.lt_of_lt_of_le hv_lt hcl.cur_vars_le
  have hxor_eq := nat_xor1_eq lit.toNat
  have hlit_len : lit.toNat < s.core.vals.length := by rw [hcl.vals_len]; omega
  have hneg_lt : (lit.toNat ^^^ 1) < 2 * s.core.cur_vars := nat_xor1_lt hlt
  have hneg_len : (lit.toNat ^^^ 1) < s.core.vals.length := by
    rw [hcl.vals_len]; have := hcl.cur_vars_le; omega
  have hne_neg : (lit.toNat ^^^ 1) ≠ lit.toNat := by
    by_cases hmod : lit.toNat % 2 = 0 <;> simp [hxor_eq, hmod] <;> omega
  have hlvl_len : lit.toNat / 2 < s.core.lvl.length := by rw [hcl.lvl_len]; exact hv_mv
  have hrsns_len : lit.toNat / 2 < s.core.rsns.length := by rw [hcl.rsns_len]; exact hv_mv
  have htp_len : lit.toNat / 2 < s.core.trail_pos.length := by
    rw [hcl.trail_pos_len]; exact hv_mv
  have htrl_ne_v : ∀ j < s.core.trail_end,
      (s.core.trl[j]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := by
    intro j hj heq
    have hcases : (s.core.trl[j]?.getD 0#32).toNat = lit.toNat ∨
        (s.core.trl[j]?.getD 0#32).toNat = lit.toNat ^^^ 1 := by
      by_cases hmod : lit.toNat % 2 = 0 <;> simp only [hxor_eq, hmod, ↓reduceIte] <;> omega
    rcases hcases with h1 | h1
    · have htr := (hw.vals_true_iff lit.toNat hlt).mpr ⟨j, hj, h1⟩
      rw [hun] at htr; cases htr
    · have hfl := (hw.vals_false_iff lit.toNat hlt).mpr ⟨j, hj, h1⟩
      rw [hun] at hfl; cases hfl
  have htrl_lt' : ∀ i < k'.trail_end, (k'.trl[i]?.getD 0#32).toNat < 2 * k'.cur_vars := by
    intro i hi
    by_cases he : i = s.core.trail_end
    · subst he; dsimp only [k']; rw [List.getElem?_set_self hte_trl, Option.getD_some]; exact hlt
    · have hi' : i < s.core.trail_end := by dsimp [k'] at hi; omega
      dsimp only [k']; rw [List.getElem?_set_ne (Ne.symm he)]; exact hw.trail_lits_lt i hi'
  have hnodup' : ∀ i j, i < k'.trail_end → j < k'.trail_end →
      (k'.trl[i]?.getD 0#32).toNat / 2 = (k'.trl[j]?.getD 0#32).toNat / 2 → i = j := by
    intro i j hi hj heq
    by_cases hie : i = s.core.trail_end <;> by_cases hje : j = s.core.trail_end
    · exact hie.trans hje.symm
    · subst hie
      have hj' : j < s.core.trail_end := by dsimp [k'] at hj; omega
      dsimp only [k'] at heq
      rw [List.getElem?_set_self hte_trl, List.getElem?_set_ne (Ne.symm hje),
        Option.getD_some] at heq
      exact absurd heq.symm (htrl_ne_v j hj')
    · subst hje
      have hi' : i < s.core.trail_end := by dsimp [k'] at hi; omega
      dsimp only [k'] at heq
      rw [List.getElem?_set_self hte_trl, List.getElem?_set_ne (Ne.symm hie),
        Option.getD_some] at heq
      exact absurd heq (htrl_ne_v i hi')
    · have hi' : i < s.core.trail_end := by dsimp [k'] at hi; omega
      have hj' : j < s.core.trail_end := by dsimp [k'] at hj; omega
      dsimp only [k'] at heq
      rw [List.getElem?_set_ne (Ne.symm hie), List.getElem?_set_ne (Ne.symm hje)] at heq
      exact hw.trail_vars_nodup i j hi' hj' heq
  have hvals_dom' : ∀ l < 2 * k'.cur_vars,
      k'.vals[l]?.getD 0#8 = 0#8 ∨ k'.vals[l]?.getD 0#8 = 1#8 ∨ k'.vals[l]?.getD 0#8 = 0xFF#8 := by
    intro l hl
    have hl0 : l < 2 * s.core.cur_vars := hl
    by_cases hln : l = lit.toNat ^^^ 1
    · subst hln; dsimp only [k']
      rw [List.getElem?_set_self (by simp; exact hneg_len), Option.getD_some]
      exact .inr (.inr rfl)
    · by_cases hll : l = lit.toNat
      · subst hll; dsimp only [k']
        rw [List.getElem?_set_ne hne_neg, List.getElem?_set_self hlit_len, Option.getD_some]
        exact .inr (.inl rfl)
      · dsimp only [k']
        rw [List.getElem?_set_ne (Ne.symm hln), List.getElem?_set_ne (Ne.symm hll)]
        exact hw.vals_domain l hl0
  have hvals_true' : ∀ l < 2 * k'.cur_vars,
      k'.vals[l]?.getD 0#8 = 1#8 ↔ ∃ i < k'.trail_end, (k'.trl[i]?.getD 0#32).toNat = l := by
    intro l hl
    have hl0 : l < 2 * s.core.cur_vars := hl
    by_cases hln : l = lit.toNat ^^^ 1
    · subst hln
      have hff : k'.vals[lit.toNat ^^^ 1]?.getD 0#8 = 0xFF#8 := by
        dsimp only [k']; rw [List.getElem?_set_self (by simp; exact hneg_len), Option.getD_some]
      constructor
      · intro hv; rw [hff] at hv; cases hv
      · rintro ⟨i, hi, heq⟩
        by_cases hie : i = s.core.trail_end
        · subst hie; dsimp only [k'] at heq
          rw [List.getElem?_set_self hte_trl, Option.getD_some] at heq
          exact absurd heq.symm hne_neg
        · have hi' : i < s.core.trail_end := by dsimp [k'] at hi; omega
          dsimp only [k'] at heq; rw [List.getElem?_set_ne (Ne.symm hie)] at heq
          have hfl := (hw.vals_false_iff lit.toNat hlt).mpr ⟨i, hi', heq⟩
          rw [hun] at hfl; cases hfl
    · by_cases hll : l = lit.toNat
      · subst hll
        have h1 : k'.vals[lit.toNat]?.getD 0#8 = 1#8 := by
          dsimp only [k']
          rw [List.getElem?_set_ne hne_neg, List.getElem?_set_self hlit_len, Option.getD_some]
        constructor
        · intro _; refine ⟨s.core.trail_end, by dsimp [k']; omega, ?_⟩
          dsimp only [k']; rw [List.getElem?_set_self hte_trl, Option.getD_some]
        · intro _; exact h1
      · have hveq : k'.vals[l]?.getD 0#8 = s.core.vals[l]?.getD 0#8 := by
          dsimp only [k']
          rw [List.getElem?_set_ne (Ne.symm hln), List.getElem?_set_ne (Ne.symm hll)]
        rw [hveq, hw.vals_true_iff l hl0]
        constructor
        · rintro ⟨i, hi, heq⟩
          refine ⟨i, by dsimp [k']; omega, ?_⟩
          dsimp only [k']; rw [List.getElem?_set_ne (by omega)]; exact heq
        · rintro ⟨i, hi, heq⟩
          by_cases hie : i = s.core.trail_end
          · subst hie; dsimp only [k'] at heq
            rw [List.getElem?_set_self hte_trl, Option.getD_some] at heq
            exact absurd heq.symm hll
          · have hi' : i < s.core.trail_end := by dsimp [k'] at hi; omega
            dsimp only [k'] at heq; rw [List.getElem?_set_ne (Ne.symm hie)] at heq
            exact ⟨i, hi', heq⟩
  have hvals_false' : ∀ l < 2 * k'.cur_vars,
      k'.vals[l]?.getD 0#8 = 0xFF#8 ↔
        ∃ i < k'.trail_end, (k'.trl[i]?.getD 0#32).toNat = l ^^^ 1 := by
    intro l hl
    have hl0 : l < 2 * s.core.cur_vars := hl
    by_cases hln : l = lit.toNat ^^^ 1
    · subst hln
      have hff : k'.vals[lit.toNat ^^^ 1]?.getD 0#8 = 0xFF#8 := by
        dsimp only [k']; rw [List.getElem?_set_self (by simp; exact hneg_len), Option.getD_some]
      have hxx : (lit.toNat ^^^ 1) ^^^ 1 = lit.toNat := nat_xor1_xor1 lit.toNat
      constructor
      · intro _; refine ⟨s.core.trail_end, by dsimp [k']; omega, ?_⟩
        dsimp only [k']; rw [List.getElem?_set_self hte_trl, Option.getD_some, hxx]
      · intro _; exact hff
    · by_cases hll : l = lit.toNat
      · subst hll
        have h1 : k'.vals[lit.toNat]?.getD 0#8 = 1#8 := by
          dsimp only [k']
          rw [List.getElem?_set_ne hne_neg, List.getElem?_set_self hlit_len, Option.getD_some]
        constructor
        · intro hv; rw [h1] at hv; cases hv
        · rintro ⟨i, hi, heq⟩
          by_cases hie : i = s.core.trail_end
          · subst hie; dsimp only [k'] at heq
            rw [List.getElem?_set_self hte_trl, Option.getD_some] at heq
            exact absurd heq.symm hne_neg
          · have hi' : i < s.core.trail_end := by dsimp [k'] at hi; omega
            dsimp only [k'] at heq; rw [List.getElem?_set_ne (Ne.symm hie)] at heq
            have hfl := (hw.vals_false_iff lit.toNat hlt).mpr ⟨i, hi', heq⟩
            rw [hun] at hfl; cases hfl
      · have hveq : k'.vals[l]?.getD 0#8 = s.core.vals[l]?.getD 0#8 := by
          dsimp only [k']
          rw [List.getElem?_set_ne (Ne.symm hln), List.getElem?_set_ne (Ne.symm hll)]
        have hne_neg2 : l ^^^ 1 ≠ lit.toNat := fun heq =>
          hln (by rw [← heq, nat_xor1_xor1])
        rw [hveq, hw.vals_false_iff l hl0]
        constructor
        · rintro ⟨i, hi, heq⟩
          refine ⟨i, by dsimp [k']; omega, ?_⟩
          dsimp only [k']; rw [List.getElem?_set_ne (by omega)]; exact heq
        · rintro ⟨i, hi, heq⟩
          by_cases hie : i = s.core.trail_end
          · subst hie; dsimp only [k'] at heq
            rw [List.getElem?_set_self hte_trl, Option.getD_some] at heq
            exact absurd heq.symm hne_neg2
          · have hi' : i < s.core.trail_end := by dsimp [k'] at hi; omega
            dsimp only [k'] at heq; rw [List.getElem?_set_ne (Ne.symm hie)] at heq
            exact ⟨i, hi', heq⟩
  have hlvl_le' : ∀ i < k'.trail_end,
      (k'.lvl[(k'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ k'.cur_level := by
    intro i hi
    by_cases hie : i = s.core.trail_end
    · subst hie; dsimp only [k']
      rw [List.getElem?_set_self hte_trl, Option.getD_some,
        List.getElem?_set_self hlvl_len, Option.getD_some]
      simp [hcl0]
    · have hi' : i < s.core.trail_end := by dsimp [k'] at hi; omega
      have hne := htrl_ne_v i hi'
      have hwi := hw.lvl_le i hi'
      dsimp only [k'] at *
      rw [List.getElem?_set_ne (Ne.symm hie), List.getElem?_set_ne (Ne.symm hne)]
      exact hwi
  have hrsn_none' : ∀ idx < k'.trail_end,
      (k'.lvl[(k'.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 →
      k'.rsns[(k'.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 := by
    intro idx hidx _
    by_cases hie : idx = s.core.trail_end
    · subst hie; dsimp only [k']
      rw [List.getElem?_set_self hte_trl, Option.getD_some,
        List.getElem?_set_self hrsns_len, Option.getD_some]
    · have hi' : idx < s.core.trail_end := by dsimp [k'] at hidx; omega
      have hne := htrl_ne_v idx hi'
      have hwi := hw.lvl_le idx hi'
      dsimp only [k']
      rw [List.getElem?_set_ne (Ne.symm hie), List.getElem?_set_ne (Ne.symm hne)]
      exact hw.level0_rsn_none idx hi' (by omega)
  exact
    { ext_sound := hw.ext_sound
      inconsistent_sound := hw.inconsistent_sound
      arena := ⟨hw.arena.len_ok, hw.arena.refs_wf, hw.arena.shrk_term,
        hw.arena.lits_lt, hw.arena.entails⟩
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
      cur_level_le := by dsimp [k']; omega
      trail_lits_lt := htrl_lt'
      trail_vars_nodup := hnodup'
      vals_domain := hvals_dom'
      vals_true_iff := hvals_true'
      vals_false_iff := hvals_false'
      lvl_le := hlvl_le'
      dec_earliest := fun i j hi hj _ hpos => by
        have hlj := hlvl_le' j hj
        have hkcl : k'.cur_level = 0 := hcl0
        rw [hkcl] at hlj
        exact absurd hpos.1 (Nat.not_lt.mpr hlj)
      levels_inhabited := fun L h1 h2 => by
        have hkcl : k'.cur_level = 0 := hcl0
        rw [hkcl] at h2; omega
      level0_sound := fun i hi _ => by
        by_cases hie : i = s.core.trail_end
        · subst hie; dsimp only [k']
          rw [List.getElem?_set_self hte_trl, Option.getD_some]; exact hent
        · have hi' : i < s.core.trail_end := by dsimp [k'] at hi; omega
          have hwi := hw.lvl_le i hi'
          dsimp only [k']; rw [List.getElem?_set_ne (Ne.symm hie)]
          exact hw.level0_sound i hi' (by omega)
      trail_pos_inv := fun i hi => by
        by_cases hie : i = s.core.trail_end
        · subst hie; dsimp only [k']
          rw [List.getElem?_set_self hte_trl, Option.getD_some,
            List.getElem?_set_self htp_len, Option.getD_some, bv32_ofNat_toNat hte_32]
        · have hi' : i < s.core.trail_end := by dsimp [k'] at hi; omega
          have hne := htrl_ne_v i hi'
          dsimp only [k']
          rw [List.getElem?_set_ne (Ne.symm hie), List.getElem?_set_ne (Ne.symm hne)]
          exact hw.trail_pos_inv i hi'
      level0_rsn_none := hrsn_none'
      frame_trail_lt := fun L hL => by
        have hL' : L ≤ s.core.cur_level := by dsimp only [k'] at hL; exact hL
        have hft := hw.frame_trail_lt L hL'
        dsimp only [k']; omega
      frame_trail_mono := fun L1 L2 h12 h2 => by
        have h2' : L2 ≤ s.core.cur_level := by dsimp only [k'] at h2; exact h2
        dsimp only [k']; exact hw.frame_trail_mono L1 L2 h12 h2'
      frame_trail_before_lt := fun L h1 h2 => by
        dsimp only [k'] at h2; rw [hcl0] at h2; omega
      frame_dec_lt := fun L h1 h2 => by
        dsimp only [k'] at h2; rw [hcl0] at h2; omega
      reason_inv := fun idx hidx hne => by
        have hle := hlvl_le' idx hidx
        have hkcl : k'.cur_level = 0 := hcl0
        rw [hkcl] at hle
        exact absurd (hrsn_none' idx hidx (by omega)) hne
      reason_lit_mem := fun idx hidx hne _ => by
        have hle := hlvl_le' idx hidx
        have hkcl : k'.cur_level = 0 := hcl0
        rw [hkcl] at hle
        exact absurd (hrsn_none' idx hidx (by omega)) hne }

end LeanQbe.T.Examples.Kissat.Proof.Clause
