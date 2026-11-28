/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Sweep.LemmasCommon

/-!
# Equivalent-Literal Substitution Helpers & Arena Rewrite WP Proof (`Proof.Sweep.WpEls0`)

Provides shared `FullDenseInvW` arena/watch/repr transition lemmas, `M6ElsFrame`, typed callee
wrappers (`m6_call_cong_find`, `m6_call_add_unit`, `m6_call_add_bin`), and the flat-`CanonicalEnv`
`Func.wp` proof for `full_m6_els_ar` (`fullM6ElsArSpec`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Sweep

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Sweep
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Kitten
open LeanQbe.T.Examples.Kissat.Proof.Sweep.Spec
open FullArenaTactics
open scoped FullArenaTactics M6SweepTactics M6ElsBv

/-! ## 1. Scoped BitVector & Pure List / Entailment Helpers -/

namespace M6ElsBvExt

@[scoped bv_c0] theorem m6_els_bv32_xor1_toNat (x : BitVec 32) :
    (x ^^^ 1#32).toNat = x.toNat ^^^ 1 := by simp
@[scoped bv_c0] theorem m6_els_bv32_xor1_ofnat (x : BitVec 32) :
    (x ^^^ (1 : BitVec 32)).toNat = x.toNat ^^^ 1 := by simp
@[scoped bv_c0] theorem m6_els_bv64_shl1_ofnat (x : BitVec 64) :
    (x <<< (1 : BitVec 64)).toNat = (2 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]
@[scoped bv_c0] theorem m6_els_bv64_shl1_nat (x : BitVec 64) :
    (x <<< (1 : Nat)).toNat = (2 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]
@[scoped bv_c0] theorem m6_els_bv32_shl1_bv (x : BitVec 32) :
    (x <<< 1#32).toNat = (2 * x.toNat) % 2 ^ 32 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]
@[scoped bv_c0] theorem m6_els_bv32_shl1_ofnat (x : BitVec 32) :
    (x <<< (1 : BitVec 32)).toNat = (2 * x.toNat) % 2 ^ 32 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]
@[scoped bv_c0] theorem m6_els_bv32_shl1_nat (x : BitVec 32) :
    (x <<< (1 : Nat)).toNat = (2 * x.toNat) % 2 ^ 32 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]
@[scoped bv_c0] theorem m6_els_bv32_shr1_nat (x : BitVec 32) :
    (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
@[scoped bv_c0] theorem m6_els_bv8_sgt0 (v : BitVec 8) :
    (0#32).slt (v.signExtend 32) = (0#8).slt v := by revert v; decide

end M6ElsBvExt

open M6ElsBvExt
open scoped M6ElsBvExt

private theorem list_take_set_succ {α : Type _} (xs : List α) {n : Nat} (hn : n < xs.length)
    (x : α) : (xs.set n x).take (n + 1) = xs.take n ++ [x] := by
  apply List.ext_getElem
  · simp [List.length_take, List.length_set]; omega
  · intro i hi1 _
    simp only [List.length_take, List.length_set] at hi1
    rw [List.getElem_take]
    by_cases hin : i < n
    · rw [List.getElem_set_ne (by omega),
        List.getElem_append_left (by rw [List.length_take]; omega), List.getElem_take]
    · have hie : i = n := by omega
      subst hie
      rw [List.getElem_set_self (by rw [List.length_set]; exact hn),
        List.getElem_append_right (by rw [List.length_take]; omega)]
      simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hn)]

private theorem nodup_of_map_div2 {xs : List (BitVec 32)}
    (h : (xs.map fun x => x.toNat / 2).Nodup) : (xs.map BitVec.toNat).Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h ⊢
    exact ⟨fun ⟨y, hy, hyx⟩ => h.1 ⟨y, hy, by omega⟩, ih h.2⟩

private theorem m6_nodup_getElem_ne {α : Type _} :
    ∀ {xs : List α}, xs.Nodup → ∀ {i j : Nat} (hi : i < xs.length) (hj : j < xs.length),
      i ≠ j → xs[i]'hi ≠ xs[j]'hj
  | [], _, _, _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | _ :: xs, hnd, 0, j + 1, _, hj, _ => fun heq => by
    simp only [List.nodup_cons, List.getElem_cons_zero, List.getElem_cons_succ] at hnd heq
    exact hnd.1 (heq ▸ List.getElem_mem _)
  | _ :: xs, hnd, i + 1, 0, hi, _, _ => fun heq => by
    simp only [List.nodup_cons, List.getElem_cons_zero, List.getElem_cons_succ] at hnd heq
    exact hnd.1 (heq.symm ▸ List.getElem_mem _)
  | _ :: xs, hnd, i + 1, j + 1, hi, hj, hne => by
    simp only [List.nodup_cons] at hnd
    exact m6_nodup_getElem_ne hnd.2 (by simp at hi; exact hi) (by simp at hj; exact hj) (by omega)
  | _ :: _, _, 0, 0, _, _, hne => absurd rfl hne

theorem m6_list_set2_eq {α : Type _} (xs : List α) {i1 j1 i2 j2 : Nat}
    {v1 v2 w1 w2 : α} (hi : i1 = j1) (hj : i2 = j2) (hv1 : v1 = w1) (hv2 : v2 = w2) :
    (xs.set i1 v1).set i2 v2 = (xs.set j1 w1).set j2 w2 := by
  subst hi hj hv1 hv2; rfl

theorem m6_bv8_zext32_eq0_iff (v : BitVec 8) : BitVec.setWidth 32 v = 0#32 ↔ v = 0#8 := by
  revert v; decide

theorem m6_bv8_sext32_eq0_iff (v : BitVec 8) : BitVec.signExtend 32 v = 0#32 ↔ v = 0#8 := by
  revert v; decide

private theorem m6_bv32_mask7f_props {sz : BitVec 32} (h3 : 3 ≤ sz.toNat)
    (hlt : sz.toNat < 2 ^ 31) :
    let w := sz &&& 0x7FFFFFFF#32
    w ≠ 0xFFFFFFFF#32 ∧ (w &&& 0x80000000#32) = 0#32 ∧ 3 ≤ w.toNat := by
  have hbit : ((sz &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32 := by
    rw [BitVec.and_assoc, show (0x7FFFFFFF#32 &&& 0x80000000#32) = 0#32 by decide, BitVec.and_zero]
  have hne : (sz &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32 := fun heq => by
    rw [heq] at hbit; revert hbit; decide
  have hto : (sz &&& 0x7FFFFFFF#32).toNat = sz.toNat := by
    rw [BitVec.toNat_and, show (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hlt]
  exact ⟨hne, hbit, by omega⟩

private theorem m6_entails_clause_subst {f : CNF Nat} {cs cs' : List Nat}
    (hmap : ∀ l ∈ cs, ∃ l' ∈ cs', LitEquiv f l l')
    (hc : f.EntailsClause (cnfClause cs)) : f.EntailsClause (cnfClause cs') := by
  rw [CNF.entails_clause_def] at hc ⊢
  intro α hα
  have h1 := (clauseEvalVal_iff α _).mpr (hc α hα)
  rw [← clauseEvalVal_iff]; rw [clauseEvalVal, List.any_eq_true] at h1 ⊢
  obtain ⟨l, hl, hsat⟩ := h1; obtain ⟨l', hl', heq⟩ := hmap l hl
  exact ⟨l', hl', by rw [← litEquiv_eval hα heq]; exact hsat⟩

private theorem m6_lits_eq_of_hold {ar1 ar2 : List (BitVec 32)} {cr sz : Nat}
    (hb1 : cr + 3 + sz ≤ ar1.length) (hb2 : cr + 3 + sz ≤ ar2.length)
    (h : ∀ j < sz, ar2[cr + 3 + j]? = ar1[cr + 3 + j]?) :
    ((ar2.drop (cr + 3)).take sz).map BitVec.toNat =
      ((ar1.drop (cr + 3)).take sz).map BitVec.toNat := by
  apply List.ext_getElem
  · simp [List.length_take, List.length_drop]; omega
  · intro j hj1 _; simp only [List.length_map, List.length_take, List.length_drop] at hj1
    have hj : j < sz := by omega
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
    have hq := h j hj
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hq
    exact congrArg BitVec.toNat (Option.some.inj hq)

private theorem m6_nlits_mod64 {cv : Nat} (h : 2 * cv < 2 ^ 64) :
    (cv * 2 ^ OfNat.ofNat 1) % 2 ^ 64 = 2 * cv := by
  change (cv * 2 ^ 1) % 2 ^ 64 = 2 * cv
  rw [Nat.pow_one, Nat.mod_eq_of_lt (by omega)]; omega

/-! ## 2. `FullDenseInvW` Transition & Framing Helpers -/

theorem m6_arenaVarsNodup_eq {s s' : FullState}
    (ha : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    (h : FullArenaVarsNodup s) : FullArenaVarsNodup s' := by
  intro r hr hng
  have hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s := by
    unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [ha, hal]
  have hgarb : fullArenaClauseGarb s' r = fullArenaClauseGarb s r := by
    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore; rw [ha]
  have hlits : fullArenaClauseLits s' r = fullArenaClauseLits s r := by
    unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [ha]
  rw [hrefs] at hr; rw [hgarb] at hng; rw [hlits]; exact h r hr hng

theorem m6_denseInvW_set_oom {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with oom := 1#64 } } :=
  ⟨⟨{ hinv.1.core_ok with vals_len := hinv.1.core_ok.vals_len }, hinv.1.scratch_ok⟩,
   { hinv.2.1 with
     arena := { hinv.2.1.arena with len_ok := hinv.2.1.arena.len_ok }
     watches := hinv.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
   hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩

private theorem m6_denseInvW_set_repr_lm_tmp {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {repr' : List (BitVec 32)} {lm' : List (BitVec 8)} {tmp' : List (BitVec 32)}
    (hrp : repr'.length = 2 * c.max_vars) (hlm : lm'.length = 2 * c.max_vars)
    (htmp : tmp'.length = c.max_vars)
    (hclear : ∀ l < 2 * c.max_vars, lm'[l]?.getD 0#8 = 0#8) :
    FullDenseInvW c F0 F_cur
      { s with core := { s.core with repr := repr', lit_mark := lm', tmp := tmp' } } :=
  ⟨⟨{ hinv.1.core_ok with repr_len := hrp, lit_mark_len := hlm, tmp_len_arr := htmp },
     hinv.1.scratch_ok⟩,
   { hinv.2.1 with
     arena := { hinv.2.1.arena with len_ok := hinv.2.1.arena.len_ok }
     watches := hinv.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
   ⟨hinv.2.2.1.1, hclear⟩, m6_arenaVarsNodup_eq rfl rfl hinv.2.2.2.1,
   hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩

private theorem m6_denseInvW_markGarb {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) (ag' : BitVec 64) :
    let s' : FullState :=
      { s with core :=
        { s.core with
          arena := s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
          arena_garbage := ag' } }
    FullDenseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s := by
  intro s'
  have hcl := hinv.1.core_ok; have hw := hinv.2.1; have hcl0 := hinv.2.2.2.2.2.1
  have hmg := hw.arena.markGarb hcl href ag'
  have hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s := hmg.1
  have hlen' : s'.LengthsOk c :=
    ⟨{ hcl with arena_len_arr := by simp [s', hcl.arena_len_arr] }, hinv.1.scratch_ok⟩
  have hnd' : FullArenaVarsNodup s' :=
    FullArenaVarsNodup.of_markGarb ⟨hinv.1, F_cur, hw⟩ hinv.2.2.2.1 href ag'
  have hno_rsn : ∀ idx < s.core.trail_end,
      s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 :=
    fun idx hidx => hw.level0_rsn_none idx hidx (by have := hw.lvl_le idx hidx; omega)
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := hmg.2
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl
        fun r hr => by change r ∈ fullArenaClauseRefs s'; rw [hrefs]; exact hr
      reason_inv := fun idx hidx hne => absurd (hno_rsn idx hidx) hne
      reason_lit_mem := fun idx hidx hne _ => absurd (hno_rsn idx hidx) hne }
  exact ⟨⟨hlen', hw', hinv.2.2.1, hnd',
    FullExtScratchOk.of_pres hinv.2.2.2.2.1 ⟨rfl, rfl⟩ (fun r hr => hrefs ▸ hr),
    hcl0, hinv.2.2.2.2.2.2⟩, hrefs⟩

private def mkWatchCore (core : FullCoreState) (wvec' wstk' : List (BitVec 32))
    (wlen' : Nat) (wu' : BitVec 64) : FullCoreState :=
  { core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }

private theorem m6_denseInvW_watchPush {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {rl w0 w1 : BitVec 32} {ok : Bool}
    {wvec' wstk' : List (BitVec 32)} {wlen' : Nat} {wu' : BitVec 64} {wsort' : List (BitVec 32)}
    (hsok' : ({ s with
      core := mkWatchCore s.core wvec' wstk' wlen' wu'
      scratch := { s.scratch with wsort := wsort' } } : FullState).LengthsOk c)
    (hlay' : WatchStackLayout (mkWatchCore s.core wvec' wstk' wlen' wu'))
    (hflag : (w0 &&& 0x80000000#32) = 0#32) (hsz : 3 ≤ w0.toNat)
    (hlt : w1.toNat < 0x80000000) (href : w1.toNat ∈ fullArenaClauseRefs s)
    (hother : ∀ l < 2 * s.core.cur_vars, l ≠ rl.toNat →
      fullWatchSizeCore (mkWatchCore s.core wvec' wstk' wlen' wu') l = fullWatchSize s l ∧
      ∀ k < fullWatchSize s l,
        wstk'[fullWatchOffCore (mkWatchCore s.core wvec' wstk' wlen' wu') l + k]? =
          s.core.wstk[fullWatchOff s l + k]?)
    (hok_t : ok = true →
      rl.toNat < 2 * s.core.cur_vars ∧
      fullWatchSizeCore (mkWatchCore s.core wvec' wstk' wlen' wu') rl.toNat =
        fullWatchSize s rl.toNat + 2 ∧
      (∀ k < fullWatchSize s rl.toNat,
        wstk'[fullWatchOffCore (mkWatchCore s.core wvec' wstk' wlen' wu') rl.toNat + k]? =
          s.core.wstk[fullWatchOff s rl.toNat + k]?) ∧
      wstk'[fullWatchOffCore (mkWatchCore s.core wvec' wstk' wlen' wu') rl.toNat +
        fullWatchSize s rl.toNat]? = some w0 ∧
      wstk'[fullWatchOffCore (mkWatchCore s.core wvec' wstk' wlen' wu') rl.toNat +
        fullWatchSize s rl.toNat + 1]? = some w1)
    (hok_f : ok = false → rl.toNat < 2 * s.core.cur_vars →
      fullWatchSizeCore (mkWatchCore s.core wvec' wstk' wlen' wu') rl.toNat =
        fullWatchSize s rl.toNat ∧
      ∀ k < fullWatchSize s rl.toNat,
        wstk'[fullWatchOffCore (mkWatchCore s.core wvec' wstk' wlen' wu') rl.toNat + k]? =
          s.core.wstk[fullWatchOff s rl.toNat + k]?) :
    FullDenseInvW c F0 F_cur
      { s with
        core := mkWatchCore s.core wvec' wstk' wlen' wu'
        scratch := { s.scratch with wsort := wsort' } } := by
  have hw := hinv.2.1; have hwm := hw.watches; unfold ModeWatchesInv at hwm
  rw [ite_eq_right (fun h0 => hinv.2.2.2.2.2.2 h0)] at hwm
  have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ h => h
  let k' : FullCoreState := mkWatchCore s.core wvec' wstk' wlen' wu'
  have hwat' : ModeWatchesInv F_cur k' := by
    unfold ModeWatchesInv
    rw [show k'.dense_mode = s.core.dense_mode from rfl,
      ite_eq_right (fun h0 => absurd h0 hinv.2.2.2.2.2.2)]
    refine ⟨hlay', fun l hl => ?_⟩
    by_cases hle : l = rl.toNat
    · subst hle
      cases ok with
      | false =>
        obtain ⟨hs, hslice⟩ := hok_f rfl hl
        change DenseWatchSliceOk F_cur k' rl.toNat (fullWatchOffCore k' rl.toNat)
          (fullWatchSizeCore k' rl.toNat)
        rw [hs]
        exact DenseWatchSliceOk.relocate (k := s.core) (k' := k') hrefl (le_refl _)
          (fun _ r => r) hslice (hwm.slices rl.toNat hl)
      | true =>
        obtain ⟨_, hs, hpre, hw0, hw1⟩ := hok_t rfl
        change DenseWatchSliceOk F_cur k' rl.toNat (fullWatchOffCore k' rl.toNat)
          (fullWatchSizeCore k' rl.toNat)
        rw [hs]
        exact DenseWatchSliceOk.append_occ (k := s.core) (k' := k') (le_refl _)
          (fun _ r => r) hpre (hwm.slices rl.toNat hl) hw0 hw1 hflag hsz hlt href
    · obtain ⟨hs, hslice⟩ := hother l hl hle
      change DenseWatchSliceOk F_cur k' l (fullWatchOffCore k' l) (fullWatchSizeCore k' l)
      rw [hs]
      exact DenseWatchSliceOk.relocate (k := s.core) (k' := k') hrefl (le_refl _)
        (fun _ r => r) hslice (hwm.slices l hl)
  exact ⟨hsok', { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }, watches := hwat' },
    hinv.2.2.1, m6_arenaVarsNodup_eq rfl rfl hinv.2.2.2.1,
    hinv.2.2.2.2.1, hinv.2.2.2.2.2.1, hinv.2.2.2.2.2.2⟩

private theorem m6_denseInvW_replaceSameLen {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) (_hng : fullArenaClauseGarb s cref = false)
    {arena' : List (BitVec 32)} (har_len : arena'.length = c.arena_cap)
    (hout : ∀ i, i < cref + 3 ∨ cref + 3 + fullArenaClauseSize s cref ≤ i →
      arena'[i]? = s.core.arena[i]?)
    (hlits_lt' : ∀ l ∈ fullArenaClauseLits { s with core := { s.core with arena := arena' } } cref,
      l < 2 * s.core.cur_vars)
    (hnd_cr' : ((fullArenaClauseLits { s with core := { s.core with arena := arena' } } cref).map
      (· / 2)).Nodup)
    (hent' : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullArenaClauseLits { s with core := { s.core with arena := arena' } } cref))) :
    let s' := { s with core := { s.core with arena := arena' } }
    FullDenseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s := by
  intro s'
  have hcl := hinv.1.core_ok; have hw := hinv.2.1; have hcl0 := hinv.2.2.2.2.2.1
  let old_sz := fullArenaClauseSizeCore s.core cref
  have hwf := hw.arena.refs_wf cref href
  have hbd_wf := hwf.2.2.1; have hal_le := hcl.arena_len_le; have haa := hcl.arena_len_arr
  have hout_c : ∀ i, i < cref + 3 ∨ cref + 3 + old_sz ≤ i → arena'[i]? = s.core.arena[i]? := hout
  have hout_ref : ∀ r ∈ fullArenaClauseRefsCore s.core, r ≠ cref →
      (r + 3 + fullArenaClauseSizeCore s.core r ≤ cref ∧
        fullArenaNextOff s.core.arena s.core.arena_len r ≤ cref) ∨
      cref + 3 + old_sz ≤ r := fun r hr hne =>
    (Nat.lt_or_gt_of_ne hne).elim
      (fun hlt => Or.inl ⟨hw.arena.disjoint hr href hlt, fullArenaScanRefs_disjoint hr href hlt⟩)
      (fun hgt => Or.inr (hw.arena.disjoint href hr hgt))
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaNextOff arena' s.core.arena_len r =
        fullArenaNextOff s.core.arena s.core.arena_len r := fun r hr => by
    by_cases hrc : r = cref
    · subst r
      exact fullArenaNextOff_congr_block (hout_c cref (Or.inl (by omega)))
        (hout_c (cref + 2) (Or.inl (by omega))) fun k hk _ => hout_c k (Or.inr hk)
    · rcases hout_ref r hr hrc with ⟨hlt, _⟩ | hgt
      · have hr3 := (hw.arena.refs_wf r hr).2.1
        exact fullArenaNextOff_congr_block (hout_c r (Or.inl (by omega)))
          (hout_c (r + 2) (Or.inl (by omega))) fun i _ _ => hout_c i (Or.inl (by omega))
      · exact fullArenaNextOff_congr_block (hout_c r (Or.inr hgt))
          (hout_c (r + 2) (Or.inr (by omega))) fun i _ _ => hout_c i (Or.inr (by omega))
  have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hother : ∀ r ∈ fullArenaClauseRefsCore s.core, r ≠ cref →
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r ∧
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r ∧
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := fun r hr hne => by
    have hrwf := hw.arena.refs_wf r hr
    have hbd_r : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
      have := hrwf.2.2.1; omega
    have hbd_r' : r + 3 + fullArenaClauseSizeCore s.core r ≤ arena'.length := by
      rw [har_len]; have := hrwf.2.2.1; omega
    have hside : ∀ i, r ≤ i → i < r + 3 + fullArenaClauseSizeCore s.core r →
        arena'[i]? = s.core.arena[i]? := fun i hi1 hi2 => by
      rcases hout_ref r hr hne with ⟨hlt, _⟩ | hgt
      · exact hout_c i (Or.inl (by omega))
      · exact hout_c i (Or.inr (by omega))
    have hszr : fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := by
      unfold fullArenaClauseSizeCore; dsimp only [s']; rw [hside (r + 2) (by omega) (by omega)]
    have hgar : fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := by
      unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [s']
      rw [hside r (le_refl _) (by omega)]
    refine ⟨hszr, hgar, ?_⟩
    unfold fullArenaClauseLitsCore; rw [hszr]
    exact m6_lits_eq_of_hold hbd_r hbd_r' fun j hj => hside (r + 3 + j) (by omega) (by omega)
  have hsz_cref : fullArenaClauseSizeCore s'.core cref = old_sz := by
    dsimp only [old_sz]; unfold fullArenaClauseSizeCore; dsimp only [s']
    rw [hout_c (cref + 2) (Or.inl (by omega))]
  have harena' : FullArenaClausesInv c F_cur s'.core := by
    refine ⟨hw.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; rw [hnxt r hr]
      by_cases hrc : r = cref
      · subst r; rw [hsz_cref]; exact hwf
      · rw [(hother r hr hrc).1]; exact hw.arena.refs_wf r hr
    · intro r hr hsh; rw [hrefs] at hr
      have hsh_of : ∀ (heq : arena'[r]? = s.core.arena[r]?),
          (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := fun heq => by
        unfold fullArenaHdrCore at hsh ⊢
        change (arena'[r]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 at hsh; rwa [heq] at hsh
      by_cases hrc : r = cref
      · subst r; have hsh0 := hsh_of (hout_c cref (Or.inl (by omega)))
        obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term cref hr hsh0
        change cref + 3 + old_sz ≤ t at ht1; rw [hsz_cref]
        exact ⟨t, ht1, ht2, by
          change arena'[t]? = some 0xFFFFFFFF#32; rw [hout_c t (Or.inr ht1)]; exact hsent⟩
      · rcases hout_ref r hr hrc with ⟨hlt, hlt_nxt⟩ | hgt
        · have hsh0 := hsh_of (hout_c r (Or.inl (by omega)))
          obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
          obtain ⟨t0, ht0_lo, ht0_hi, _, ht0_sent⟩ :=
            fullArenaNextOff_hits_sentinel (hw.arena.refs_wf r hr).1 hsh0 ht1 ht2 hsent
          rw [(hother r hr hrc).1]
          exact ⟨t0, ht0_lo, Nat.lt_of_le_of_lt ht0_hi ht2, by
            change arena'[t0]? = some 0xFFFFFFFF#32
            rw [hout_c t0 (Or.inl (by omega))]; exact ht0_sent⟩
        · have hsh0 := hsh_of (hout_c r (Or.inr hgt))
          obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
          rw [(hother r hr hrc).1]
          exact ⟨t, ht1, ht2, by
            change arena'[t]? = some 0xFFFFFFFF#32
            rw [hout_c t (Or.inr (by omega))]; exact hsent⟩
    · intro r hr hng'; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r; exact hlits_lt'
      · rw [(hother r hr hrc).2.1] at hng'; rw [(hother r hr hrc).2.2]
        exact hw.arena.lits_lt r hr hng'
    · intro r hr hng'; rw [hrefs] at hr
      by_cases hrc : r = cref
      · subst r; exact hent'
      · rw [(hother r hr hrc).2.1] at hng'; rw [(hother r hr hrc).2.2]
        exact hw.arena.entails r hr hng'
  have hlen' : s'.LengthsOk c := ⟨{ hcl with arena_len_arr := har_len }, hinv.1.scratch_ok⟩
  have hnd' : FullArenaVarsNodup s' := by
    intro r hr hng'; change r ∈ fullArenaClauseRefsCore s'.core at hr; rw [hrefs] at hr
    by_cases hrc : r = cref
    · subst r; exact hnd_cr'
    · have hg0 : fullArenaClauseGarb s r = false := by
        change fullArenaClauseGarbCore s'.core r = false at hng'
        rwa [(hother r hr hrc).2.1] at hng'
      change ((fullArenaClauseLitsCore s'.core r).map (· / 2)).Nodup
      rw [(hother r hr hrc).2.2]; exact hinv.2.2.2.1 r hr hg0
  have hno_rsn : ∀ idx < s.core.trail_end,
      s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 :=
    fun idx hidx => hw.level0_rsn_none idx hidx (by have := hw.lvl_le idx hidx; omega)
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := harena'
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl fun r hr => by
        change r ∈ fullArenaClauseRefsCore s'.core; rw [hrefs]; exact hr
      reason_inv := fun idx hidx hne => absurd (hno_rsn idx hidx) hne
      reason_lit_mem := fun idx hidx hne _ => absurd (hno_rsn idx hidx) hne }
  exact ⟨⟨hlen', hw', hinv.2.2.1, hnd',
    FullExtScratchOk.of_pres hinv.2.2.2.2.1 ⟨rfl, rfl⟩ fun r hr => by
      change r ∈ fullArenaClauseRefsCore s'.core; rw [hrefs]; exact hr,
    hcl0, hinv.2.2.2.2.2.2⟩, hrefs⟩

private theorem m6_denseInvW_inPlaceShrink {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hinv : FullDenseInvW c F0 F_cur s)
    {cref nsz : Nat} (href : cref ∈ fullArenaClauseRefs s)
    (hng : fullArenaClauseGarb s cref = false) (h3 : 3 ≤ nsz)
    (hlt : nsz < fullArenaClauseSize s cref) {arena' : List (BitVec 32)}
    (har_len : arena'.length = c.arena_cap)
    (hhdr' : arena'[cref]? = some
      (if (fullArenaHdr s cref &&& 0x00800000#32) = 0#32 then
        fullArenaHdr s cref ||| 0x00800000#32
      else fullArenaHdr s cref))
    (hsz' : arena'[cref + 2]? = some (BitVec.ofNat 32 nsz))
    (hpad_old : ∀ j, nsz ≤ j → j < fullArenaClauseSize s cref - 1 →
      arena'[cref + 3 + j]? = s.core.arena[cref + 3 + j]?)
    (hlast_sent : (fullArenaHdr s cref &&& 0x00800000#32) = 0#32 →
      arena'[cref + 3 + fullArenaClauseSize s cref - 1]? = some 0xFFFFFFFF#32)
    (hlast_keep : (fullArenaHdr s cref &&& 0x00800000#32) ≠ 0#32 →
      arena'[cref + 3 + fullArenaClauseSize s cref - 1]? =
        s.core.arena[cref + 3 + fullArenaClauseSize s cref - 1]?)
    (hout : ∀ i, i < cref ∨ cref + 3 + fullArenaClauseSize s cref ≤ i →
      arena'[i]? = s.core.arena[i]?)
    (hlits_lt' : ∀ l ∈ fullArenaClauseLits { s with core := { s.core with arena := arena' } } cref,
      l < 2 * s.core.cur_vars)
    (hnd_cr' : ((fullArenaClauseLits { s with core := { s.core with arena := arena' } } cref).map
      (· / 2)).Nodup)
    (hent' : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullArenaClauseLits { s with core := { s.core with arena := arena' } } cref))) :
    let s' := { s with core := { s.core with arena := arena' } }
    FullDenseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s := by
  intro s'
  have hcl := hinv.1.core_ok; have hw := hinv.2.1; have hcl0 := hinv.2.2.2.2.2.1
  obtain ⟨hrefs, hother, _, _, harena'⟩ := inPlaceShrink_preserves_arena hw.arena hcl href hng h3
    hlt har_len hhdr' hsz' hpad_old hlast_sent hlast_keep hout hlits_lt' hent'
  have hlen' : s'.LengthsOk c := ⟨{ hcl with arena_len_arr := har_len }, hinv.1.scratch_ok⟩
  have hnd' : FullArenaVarsNodup s' := by
    intro r hr hng'; change r ∈ fullArenaClauseRefsCore s'.core at hr; rw [hrefs] at hr
    by_cases hrc : r = cref
    · subst r; exact hnd_cr'
    · have hg0 : fullArenaClauseGarb s r = false := by
        change fullArenaClauseGarbCore s'.core r = false at hng'
        rwa [(hother r hr hrc).2.1] at hng'
      change ((fullArenaClauseLitsCore s'.core r).map (· / 2)).Nodup
      rw [(hother r hr hrc).2.2]; exact hinv.2.2.2.1 r hr hg0
  have hno_rsn : ∀ idx < s.core.trail_end,
      s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 :=
    fun idx hidx => hw.level0_rsn_none idx hidx (by have := hw.lvl_le idx hidx; omega)
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := harena'
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl fun r hr => by
        change r ∈ fullArenaClauseRefsCore s'.core; rw [hrefs]; exact hr
      reason_inv := fun idx hidx hne => absurd (hno_rsn idx hidx) hne
      reason_lit_mem := fun idx hidx hne _ => absurd (hno_rsn idx hidx) hne }
  exact ⟨⟨hlen', hw', hinv.2.2.1, hnd',
    FullExtScratchOk.of_pres hinv.2.2.2.2.1 ⟨rfl, rfl⟩ fun r hr => by
      change r ∈ fullArenaClauseRefsCore s'.core; rw [hrefs]; exact hr,
    hcl0, hinv.2.2.2.2.2.2⟩, hrefs⟩

/-! ## 3. Shared ELS Frame & Typed Callee Wrappers -/

structure M6ElsFrame (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s sL : FullState) : Prop where
  dinv : FullDenseInvW c F0 F_cur sL
  cv : sL.core.cur_vars = s.core.cur_vars
  fuel : sL.core.fuel = s.core.fuel
  repr : FullCongReprInv F_cur (2 * s.core.cur_vars) sL.core.repr
  tmk : sL.scratch.tarjan_mark = s.scratch.tarjan_mark
  trh : sL.scratch.tarjan_reach = s.scratch.tarjan_reach
  scr : sL.scratch.scratch_buf = s.scratch.scratch_buf
  ws1 : sL.scratch.work_stk1 = s.scratch.work_stk1
  ws2 : sL.scratch.work_stk2 = s.scratch.work_stk2
  gu : sL.scratch.glue_used = s.scratch.glue_used

theorem M6ElsFrame.set_oom {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sL : FullState} (h : M6ElsFrame c F0 F_cur s sL) :
    M6ElsFrame c F0 F_cur s { sL with core := { sL.core with oom := 1#64 } } :=
  ⟨m6_denseInvW_set_oom h.dinv, h.cv, h.fuel, h.repr, h.tmk, h.trh, h.scr, h.ws1, h.ws2, h.gu⟩

theorem m6_call_cong_find {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hFind : Γ.Has "full_cong_find" fullCongFindSpec)
    {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {l : BitVec 32} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Tup Val [i32] → Expr Val Cont rs}
    (hrepr : FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr)
    (hl : l.toNat < 2 * s.core.cur_vars) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ (r : BitVec 32) (repr' : List (BitVec 32)) (m' : Mem 64),
      repr'.length = s.core.repr.length →
      FullCongReprInv F_cur (2 * s.core.cur_vars) repr' →
      r.toNat ≤ l.toNat → r.toNat < 2 * s.core.cur_vars →
      LitEquiv (cnfOfClauses F_cur) l.toNat r.toNat →
      (FullMem c { s with core := { s.core with repr := repr' } } ⋆ R) m' →
      wp Γ Q X (k (r, ())) m') :
    wp Γ Q X
      (Expr.call (as := [i64, i32]) (bs := [i32]) "full_cong_find"
        (Arg.var c.pRepr, Arg.var l, ()) k) m := by
  refine wp_call_of_spec _ k ?_
  refine hFind (c.pRepr, l, ()) m (fun r m' => wp Γ Q X (k r) m') X
    ⟨F_cur, 2 * s.core.cur_vars, s.core.repr, ArrayField.repr.rest c s ⋆ R,
      hrepr, hl, ArrayField.repr.focus hm, fun r repr' m' hlen hinv hle hlt heqv hm' =>
        hk r repr' m' hlen hinv hle hlt heqv (ArrayField.repr.unfocus hm')⟩

theorem m6_call_add_unit {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hAddUnit : Γ.Has "full_add_unit" fullAddUnitSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s sB : FullState}
    {u : BitVec 32} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Tup Val [.bool] → Expr Val Cont rs}
    (hfr : M6ElsFrame c F0 F_cur s sB) (hu_lt : u.toNat < 2 * sB.core.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [u.toNat]))
    (hm : (FullMem c sB ⋆ R) m)
    (hk : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      M6ElsFrame c F0 F_cur s s' → s'.core.tmp = sB.core.tmp →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k (ok, ())) m') :
    wp Γ Q X
      (Expr.call (as := [i64, i32]) (bs := [.bool]) "full_add_unit"
        (Arg.var c.hdr, Arg.var u, ()) k) m := by
  refine wp_call_of_spec _ k ?_
  refine hAddUnit (c.hdr, u, ()) m (fun r m' => wp Γ Q X (k r) m') X
    ⟨c, F0, F_cur, sB, R, rfl, hfr.dinv.1, hfr.dinv.2.1, fun _ => hent, hm, ?_⟩
  intro ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
    phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss' m' s' hlen' hw' hcl' hfail _ hm'
  have hinv' : FullDenseInvW c F0 F_cur s' :=
    ⟨hlen', hw', hfr.dinv.2.2.1, m6_arenaVarsNodup_eq rfl rfl hfr.dinv.2.2.2.1,
     ⟨fun i hi => hfr.dinv.2.2.2.2.1.1 i hi, hfr.dinv.2.2.2.2.1.2⟩, hcl', hfr.dinv.2.2.2.2.2.2⟩
  exact hk ok s' m'
    ⟨hinv', hfr.cv, hfr.fuel, hfr.repr, hfr.tmk, hfr.trh, hfr.scr, hfr.ws1, hfr.ws2, hfr.gu⟩
    rfl (hfail hu_lt) hm'

theorem m6_call_add_bin {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hAddBin : Γ.Has "full_add_bin" fullAddBinSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s sB : FullState}
    {a b : BitVec 32} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Tup Val [i64] → Expr Val Cont rs}
    (hfr : M6ElsFrame c F0 F_cur s sB)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat]))
    (hm : (FullMem c sB ⋆ R) m)
    (hk : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      M6ElsFrame c F0 F_cur s s' →
      (r = 20#64 → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X
      (Expr.call (as := [i64, i32, i32]) (bs := [i64]) "full_add_bin"
        (Arg.var c.hdr, Arg.var a, Arg.var b, ()) k) m := by
  refine wp_call_of_spec _ k ?_
  refine hAddBin (c.hdr, a, b, ()) m (fun r m' => wp Γ Q X (k r) m') X
    ⟨c, F0, F_cur, sB, R, rfl, hfr.dinv.1, hfr.dinv.2.1, hfr.dinv.2.2.2.2.2.1,
      fun _ _ => hent, hm, ?_⟩
  intro r vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu'
    nb' oom' inc' phases' wsort' m' s' hlen' hw' _ hr20 _ hm'
  have hinv' : FullDenseInvW c F0 F_cur s' :=
    ⟨hlen', hw', hfr.dinv.2.2.1, m6_arenaVarsNodup_eq rfl rfl hfr.dinv.2.2.2.1,
     ⟨fun i hi => hfr.dinv.2.2.2.2.1.1 i hi, hfr.dinv.2.2.2.2.1.2⟩,
     hfr.dinv.2.2.2.2.2.1, hfr.dinv.2.2.2.2.2.2⟩
  exact hk r s' m'
    ⟨hinv', hfr.cv, hfr.fuel, hfr.repr, hfr.tmk, hfr.trh, hfr.scr, hfr.ws1, hfr.ws2, hfr.gu⟩
    hr20 hm'

/-! ## 4. `M6ElsLitMapOk` & `full_m6_els_ar` Helpers -/

private structure M6ElsLitMapOk (c : FullCfg) (s : FullState) (lm : List (BitVec 8))
    (tmp : List (BitVec 32)) (nsz : Nat) : Prop where
  lm_len : lm.length = 2 * c.max_vars
  tmp_len : tmp.length = c.max_vars
  cv_le : s.core.cur_vars ≤ c.max_vars
  nsz_le : nsz ≤ s.core.cur_vars
  tmp_lt : ∀ j < nsz, (tmp[j]?.getD 0#32).toNat < 2 * s.core.cur_vars
  nodup : ((tmp.take nsz).map fun x => x.toNat / 2).Nodup
  map : ∀ l < 2 * c.max_vars,
    lm[l]?.getD 0#8 = if decide (∃ j < nsz, (tmp[j]?.getD 0#32).toNat = l) then 1#8 else 0#8

private theorem m6_elsLitMapOk_init {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvW c F0 F_cur s) :
    M6ElsLitMapOk c s s.core.lit_mark s.core.tmp 0 :=
  ⟨hinv.1.core_ok.lit_mark_len, hinv.1.core_ok.tmp_len_arr, hinv.1.core_ok.cur_vars_le,
   Nat.zero_le _, (fun _ hj => by cases hj), by simp,
   fun l hl => by
     rw [decide_eq_false (by intro ⟨j, hj, _⟩; exact Nat.not_lt_zero j hj)]
     simpa using hinv.2.2.1.2 l hl⟩

private theorem m6_elsLitMapOk_push {c : FullCfg} {s : FullState}
    {lm : List (BitVec 8)} {tmp : List (BitVec 32)} {nsz : Nat}
    (h : M6ElsLitMapOk c s lm tmp nsz) {rx : BitVec 32}
    (hrx_lt : rx.toNat < 2 * s.core.cur_vars)
    (h0 : lm[rx.toNat]?.getD 0#8 = 0#8) (h1 : lm[(rx ^^^ 1#32).toNat]?.getD 0#8 = 0#8) :
    nsz < c.max_vars ∧
    M6ElsLitMapOk c s (lm.set rx.toNat 1#8) (tmp.set nsz rx) (nsz + 1) := by
  rcases h with ⟨hlm, htmp, hcv, hnsz, hlt, hnd, hmap⟩
  have hrx1 : (rx ^^^ 1#32).toNat = rx.toNat ^^^ 1 := by simp
  have hnot_var : rx.toNat / 2 ∉ (tmp.take nsz).map (fun x => x.toNat / 2) := by
    intro hmem
    rw [List.mem_map] at hmem; obtain ⟨x, hx, hxv⟩ := hmem
    rw [List.mem_iff_getElem] at hx; obtain ⟨j, hj, rfl⟩ := hx
    have hj' : j < nsz := by simp only [List.length_take] at hj; omega
    rw [List.getElem_take] at hxv
    have hx_eq : (tmp[j]?.getD 0#32).toNat = (tmp[j]'(by omega)).toNat := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    have hcases : (tmp[j]?.getD 0#32).toNat = rx.toNat ∨
        (tmp[j]?.getD 0#32).toNat = rx.toNat ^^^ 1 := by
      rw [show rx.toNat ^^^ 1 = litNeg rx.toNat from rfl, litNeg_eq]; split <;> omega
    rcases hcases with he | he
    · have hl := hmap rx.toNat (by omega)
      rw [decide_eq_true ⟨j, hj', he⟩] at hl; simp only [ite_true] at hl; rw [h0] at hl; cases hl
    · have hl := hmap (rx.toNat ^^^ 1) (by omega)
      rw [decide_eq_true ⟨j, hj', he⟩] at hl; simp only [ite_true] at hl
      rw [← hrx1, h1] at hl; cases hl
  have hlen_take : ((tmp.take nsz).map fun x => x.toNat / 2).length = nsz := by
    simp [List.length_take]; omega
  have hpig : nsz + 1 ≤ s.core.cur_vars := by
    have hnd' := List.nodup_cons.mpr ⟨hnot_var, hnd⟩
    have hl : (rx.toNat / 2 :: (tmp.take nsz).map fun x => x.toNat / 2).length ≤ s.core.cur_vars :=
      k6_nodup_subset_length hnd' fun v hv => by
        rcases List.mem_cons.mp hv with rfl | hm
        · omega
        · rw [List.mem_map] at hm; obtain ⟨x, hx, rfl⟩ := hm
          rw [List.mem_iff_getElem] at hx; obtain ⟨j, hj, rfl⟩ := hx
          have hj' : j < nsz := by simp only [List.length_take] at hj; omega
          rw [List.getElem_take]; have := hlt j hj'
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at this; omega
    simp only [List.length_cons, hlen_take] at hl; exact hl
  refine ⟨by omega, by simp [hlm], by simp [htmp], hcv, hpig, ?_, ?_, ?_⟩
  · intro j hj
    by_cases hjn : j = nsz
    · subst hjn; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hrx_lt
    · rw [List.getElem?_set_ne (Ne.symm hjn)]; exact hlt j (by omega)
  · rw [list_take_set_succ tmp (by omega) rx, List.map_append, List.map_singleton,
      List.nodup_append]
    refine ⟨hnd, by simp, fun a ha b hb => ?_⟩
    simp only [List.mem_singleton] at hb; subst hb; rintro rfl; exact hnot_var ha
  · intro l hl
    by_cases hlx : l = rx.toNat
    · subst hlx
      rw [List.getElem?_set_self (by omega), Option.getD_some,
        decide_eq_true ⟨nsz, by omega, by rw [List.getElem?_set_self (by omega), Option.getD_some]⟩]
      rfl
    · rw [List.getElem?_set_ne (Ne.symm hlx), hmap l hl]
      have hmem_iff : (∃ j < nsz + 1, ((tmp.set nsz rx)[j]?.getD 0#32).toNat = l) ↔
          (∃ j < nsz, (tmp[j]?.getD 0#32).toNat = l) := by
        constructor
        · rintro ⟨j, hj, hje⟩
          by_cases hjn : j = nsz
          · subst hjn; rw [List.getElem?_set_self (by omega), Option.getD_some] at hje
            exact absurd hje.symm hlx
          · rw [List.getElem?_set_ne (Ne.symm hjn)] at hje; exact ⟨j, by omega, hje⟩
        · rintro ⟨j, hj, hje⟩
          exact ⟨j, by omega, by rw [List.getElem?_set_ne (by omega)]; exact hje⟩
      by_cases hex : ∃ j < nsz, (tmp[j]?.getD 0#32).toNat = l
      · rw [decide_eq_true hex, decide_eq_true (hmem_iff.mpr hex)]
      · rw [decide_eq_false hex, decide_eq_false (fun h' => hex (hmem_iff.mp h'))]

private theorem m6_els_ar_loop3_step_ok {c : FullCfg} {s : FullState}
    {lm2 lm3 : List (BitVec 8)} {tmp2 : List (BitVec 32)}
    {nsz2 k3 : BitVec 32} (hmap2 : M6ElsLitMapOk c s lm2 tmp2 nsz2.toNat)
    (hk3 : k3.toNat < nsz2.toNat) (hlm3 : lm3.length = 2 * c.max_vars)
    (hmap3 : ∀ l < 2 * c.max_vars, lm3[l]?.getD 0#8 =
      if decide (∃ j < nsz2.toNat, k3.toNat ≤ j ∧ (tmp2[j]?.getD 0#32).toNat = l) then
        1#8 else 0#8) :
    let tk := (tmp2[k3.toNat]'(by
      have := hmap2.nsz_le; have := hmap2.cv_le; have := hmap2.tmp_len; omega)).toNat
    ∀ l < 2 * c.max_vars, (lm3.set tk 0#8)[l]?.getD 0#8 =
      if decide (∃ j < nsz2.toNat, k3.toNat + 1 ≤ j ∧ (tmp2[j]?.getD 0#32).toNat = l) then
        1#8 else 0#8 := by
  intro tk l hl
  have hnsz_le := hmap2.nsz_le; have hcv_le := hmap2.cv_le; have htl := hmap2.tmp_len
  have htk_lt : tk < 2 * s.core.cur_vars := by
    dsimp only [tk]; have := hmap2.tmp_lt k3.toNat hk3
    rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
  have hnd_t := nodup_of_map_div2 hmap2.nodup
  have hinj : ∀ j, k3.toNat + 1 ≤ j → j < nsz2.toNat → (tmp2[j]?.getD 0#32).toNat ≠ tk := by
    intro j hj1 hj2 heq
    have hlen_tk : (tmp2.take nsz2.toNat).length = nsz2.toNat := List.length_take_of_le (by omega)
    have hne_get := m6_nodup_getElem_ne hnd_t
      (by rw [List.length_map, hlen_tk]; exact hk3)
      (by rw [List.length_map, hlen_tk]; exact hj2) (by omega)
    simp only [List.getElem_map, List.getElem_take] at hne_get
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at heq
    exact hne_get heq.symm
  by_cases hlt_tk : l = tk
  · rw [hlt_tk, List.getElem?_set_self (by rw [hlm3]; omega), Option.getD_some,
      decide_eq_false (by rintro ⟨j, hj2, hj1, hjeq⟩; exact hinj j hj1 hj2 hjeq)]; rfl
  · rw [List.getElem?_set_ne (Ne.symm hlt_tk), hmap3 l hl]
    have hex_iff : (∃ j < nsz2.toNat, k3.toNat + 1 ≤ j ∧ (tmp2[j]?.getD 0#32).toNat = l) ↔
        (∃ j < nsz2.toNat, k3.toNat ≤ j ∧ (tmp2[j]?.getD 0#32).toNat = l) := by
      constructor
      · rintro ⟨j, h2, h1, h3⟩; exact ⟨j, h2, by omega, h3⟩
      · rintro ⟨j, h2, h1, h3⟩
        by_cases hjk : j = k3.toNat
        · subst hjk; exfalso; apply hlt_tk
          rw [← h3, List.getElem?_eq_getElem (by omega), Option.getD_some]
        · exact ⟨j, h2, by omega, h3⟩
    by_cases hex : ∃ j < nsz2.toNat, k3.toNat ≤ j ∧ (tmp2[j]?.getD 0#32).toNat = l
    · rw [decide_eq_true hex, decide_eq_true (hex_iff.mpr hex)]
    · rw [decide_eq_false hex, decide_eq_false (fun h => hex (hex_iff.mp h))]

private theorem m6_els_ar_hent_tmp {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {lm2 : List (BitVec 8)} {tmp2 : List (BitVec 32)} {cr sz32 nsz2 : BitVec 32}
    (hsz_c : fullArenaClauseSizeCore s.core cr.toNat = sz32.toNat)
    (hsz_ar_bd : cr.toNat + 3 + sz32.toNat ≤ s.core.arena.length)
    (hent_cr : (cnfOfClauses F_cur).EntailsClause (cnfClause (fullArenaClauseLits s cr.toNat)))
    (hmap2 : M6ElsLitMapOk c s lm2 tmp2 nsz2.toNat)
    (hcov : ∀ i < sz32.toNat,
      let x := (s.core.arena[cr.toNat + 3 + i]?.getD 0#32).toNat
      ∃ j < nsz2.toNat, LitEquiv (cnfOfClauses F_cur) x (tmp2[j]?.getD 0#32).toNat) :
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((tmp2.take nsz2.toNat).map BitVec.toNat)) := by
  refine m6_entails_clause_subst (cs := fullArenaClauseLits s cr.toNat) ?_ hent_cr
  intro lit hl; unfold fullArenaClauseLits at hl
  rw [mem_fullArenaClauseLitsCore_iff (by rw [hsz_c]; exact hsz_ar_bd)] at hl
  obtain ⟨i, hi, hig⟩ := hl; have hi' : i < sz32.toNat := by rwa [hsz_c] at hi
  obtain ⟨j, hj, heqv⟩ := hcov i hi'
  have htmp2_l := hmap2.tmp_len; have hnsz2_l := hmap2.nsz_le; have hcv_l := hmap2.cv_le
  refine ⟨(tmp2[j]?.getD 0#32).toNat, ?_, ?_⟩
  · rw [List.mem_map]
    refine ⟨tmp2[j]'(by omega), List.mem_iff_getElem.mpr
      ⟨j, by simp only [List.length_take]; omega, by rw [List.getElem_take]⟩,
      by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]⟩
  · rw [← hig]; rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at heqv

private theorem m6_els_ar_push_watched {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hWatch : Γ.Has "full_watch_push" fullWatchPushSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s s5 : FullState}
    {rl cr sz : BitVec 32} {R : Mem 64 → Prop} {m5 : Mem 64}
    {aH : Arg Val i64} {aRl aSz aCr aK : Arg Val i32}
    {cont : Tup Val [.bool] → Expr Val Cont rs}
    (haH : aH.val = c.hdr) (haRl : aRl.val = rl)
    (haSz : aSz.val = sz &&& 0x7FFFFFFF#32) (haCr : aCr.val = cr) (haK : aK.val = 2#32)
    (hfr5 : M6ElsFrame c F0 F_cur s s5) (hsz3 : 3 ≤ sz.toNat) (hsz_lt : sz.toNat < 2 ^ 31)
    (hcr_lt : cr.toNat < 0x80000000) (hcr_ne : cr ≠ 0xFFFFFFFF#32)
    (hcr5 : cr.toNat ∈ fullArenaClauseRefs s5) (hm5 : (FullMem c s5 ⋆ R) m5)
    (hk : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      M6ElsFrame c F0 F_cur s s' → (FullMem c s' ⋆ R) m' → wp Γ Q X (cont (ok, ())) m') :
    wp Γ Q X (Expr.call (as := [i64, i32, i32, i32, i32]) (bs := [.bool])
      "full_watch_push" (aH, aRl, aSz, aCr, aK, ()) cont) m5 := by
  obtain ⟨hw0_ne, hw0_f, hw0_3⟩ := m6_bv32_mask7f_props hsz3 hsz_lt
  have hinv5 := hfr5.dinv; have hwm5 := hinv5.2.1.watches; unfold ModeWatchesInv at hwm5
  rw [ite_eq_right (fun h0 => hinv5.2.2.2.2.2.2 h0)] at hwm5
  refine wp_call_of_spec _ cont ?_
  dsimp only [vals]; rw [haH, haRl, haSz, haCr, haK]
  refine hWatch _ m5 (fun r m' => wp Γ Q X (cont r) m') X
    ⟨c, s5, R, rfl, hinv5.1, hwm5.layout, (fun h => by cases h),
      (fun _ => ⟨hw0_ne, hcr_ne⟩), hm5, ?_⟩
  intro ok wvec' wstk' wlen' wu' wsort' m' s' hlen' hlay' hother hok_t hok_f hm'
  have hinv' := m6_denseInvW_watchPush hinv5 hlen' hlay' hw0_f hw0_3 hcr_lt hcr5 hother
    (fun ht => by
      obtain ⟨h1, _, h2, h3, h4, h5⟩ := hok_t ht
      exact ⟨h1, by simpa [mkWatchCore, fullWatchSize, fullWatchOff] using h2,
        h3, by simpa [mkWatchCore, fullWatchSize, fullWatchOff] using h4,
        by simpa [mkWatchCore, fullWatchSize, fullWatchOff] using h5⟩)
    (fun hf hl => (hok_f hf).1 hl)
  exact hk ok s' m' ⟨hinv', hfr5.cv, hfr5.fuel, hfr5.repr, hfr5.tmk, hfr5.trh, hfr5.scr,
    hfr5.ws1, hfr5.ws2, hfr5.gu⟩ hm'

private theorem m6_els_ar_lits_props {c : FullCfg} {s sC : FullState}
    {lm2 : List (BitVec 8)} {tmp2 ar5 : List (BitVec 32)} {cr nsz2 : BitVec 32}
    (hsC_cv : sC.core.cur_vars = s.core.cur_vars)
    (hmap2 : M6ElsLitMapOk c s lm2 tmp2 nsz2.toNat)
    (hbd : cr.toNat + 3 + nsz2.toNat ≤ ar5.length)
    (hsz5 : ar5[cr.toNat + 2]? = some nsz2)
    (hl5 : ∀ j < nsz2.toNat, ar5[cr.toNat + 3 + j]? = tmp2[j]?) :
    let s5 : FullState := { sC with core := { sC.core with arena := ar5 } }
    fullArenaClauseLits s5 cr.toNat = ((tmp2.take nsz2.toNat).map BitVec.toNat) ∧
    (∀ l ∈ fullArenaClauseLits s5 cr.toNat, l < 2 * sC.core.cur_vars) ∧
    ((fullArenaClauseLits s5 cr.toNat).map (· / 2)).Nodup := by
  intro s5
  have htl := hmap2.tmp_len; have hnl := hmap2.nsz_le; have hcl := hmap2.cv_le
  have heq : fullArenaClauseLits s5 cr.toNat = ((tmp2.take nsz2.toNat).map BitVec.toNat) := by
    unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore; dsimp only [s5]
    rw [hsz5, Option.getD_some,
      show nsz2.toNat = (tmp2.take nsz2.toNat).length by rw [List.length_take_of_le (by omega)]]
    apply List.ext_getElem
    · simp only [List.length_map, List.length_take, List.length_drop]; omega
    · intro j hj1 _; simp only [List.length_map, List.length_take] at hj1
      have hj : j < nsz2.toNat := by omega
      simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
      have hq := hl5 j hj
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hq
      exact congrArg BitVec.toNat (Option.some.inj hq)
  refine ⟨heq, fun l hl => ?_, by rw [heq, List.map_map]; exact hmap2.nodup⟩
  rw [heq, List.mem_iff_getElem] at hl; obtain ⟨j, hj, rfl⟩ := hl
  have hj' : j < nsz2.toNat := by simp only [List.length_map, List.length_take] at hj; omega
  simp only [List.getElem_map, List.getElem_take]
  have := hsC_cv ▸ hmap2.tmp_lt j hj'
  rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this

private theorem m6_els_ar_shrink_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sC : FullState} {lm2 : List (BitVec 8)} {tmp2 ar4 : List (BitVec 32)}
    {cr sz32 nsz2 : BitVec 32} (hinvC : FullDenseInvW c F0 F_cur sC)
    (hcr_ref : cr.toNat ∈ fullArenaClauseRefs sC) (hng_cr : fullArenaClauseGarb s cr.toNat = false)
    (hcr_bd : cr.toNat < s.core.arena.length) (har4 : ar4.length = c.arena_cap)
    (hcr_bd2 : cr.toNat + 2 < ar4.length)
    (hsC_ar : sC.core.arena = s.core.arena) (hsC_cv : sC.core.cur_vars = s.core.cur_vars)
    (hsz_def : sz32.toNat = fullArenaClauseSize s cr.toNat)
    (h3n : 3 ≤ nsz2.toNat) (hlt_sz : nsz2.toNat < sz32.toNat)
    (hout4 : ∀ i, i < cr.toNat + 3 ∨ cr.toNat + 3 + nsz2.toNat ≤ i →
      ar4[i]? = sC.core.arena[i]?)
    (htmp_cp : ∀ j < nsz2.toNat, ar4[cr.toNat + 3 + j]? = tmp2[j]?)
    (hmap2 : M6ElsLitMapOk c s lm2 tmp2 nsz2.toNat)
    (hhent4 : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((tmp2.take nsz2.toNat).map BitVec.toNat))) :
    let arBase := (ar4.set (cr.toNat + 2) nsz2).set (cr.toNat + 1) 2#32
    let ar0 := (arBase.set cr.toNat (fullArenaHdr sC cr.toNat ||| 0x00800000#32)).set
      (cr.toNat + 3 + sz32.toNat - 1) 0xFFFFFFFF#32
    ((s.core.arena[cr.toNat]'hcr_bd &&& 0x00800000#32) = 0#32 →
      FullDenseInvW c F0 F_cur { sC with core := { sC.core with arena := ar0 } } ∧
      fullArenaClauseRefs { sC with core := { sC.core with arena := ar0 } } =
        fullArenaClauseRefs sC) ∧
    ((s.core.arena[cr.toNat]'hcr_bd &&& 0x00800000#32) ≠ 0#32 →
      FullDenseInvW c F0 F_cur { sC with core := { sC.core with arena := arBase } } ∧
      fullArenaClauseRefs { sC with core := { sC.core with arena := arBase } } =
        fullArenaClauseRefs sC) := by
  intro arBase ar0
  have hng_sC : fullArenaClauseGarb sC cr.toNat = false := by
    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hng_cr ⊢
    rw [hsC_ar]; exact hng_cr
  have hsz_eq_sC : fullArenaClauseSize sC cr.toNat = sz32.toNat := by
    unfold fullArenaClauseSize fullArenaClauseSizeCore at hsz_def ⊢; rw [hsC_ar, ← hsz_def]
  have hlt_sz_ar : nsz2.toNat < fullArenaClauseSize sC cr.toNat := by omega
  have hwf_cr := hinvC.2.1.arena.refs_wf cr.toNat hcr_ref; have hal := hinvC.1.core_ok.arena_len_le
  have hsz_bd : cr.toNat + 3 + sz32.toNat ≤ c.arena_cap := by
    have h1 := hwf_cr.2.2.1; change cr.toNat + 3 + fullArenaClauseSize sC cr.toNat ≤ _ at h1
    rw [hsz_eq_sC] at h1; omega
  have hszB : arBase[cr.toNat + 2]? = some nsz2 := by
    dsimp only [arBase]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_self hcr_bd2]
  have hlB : ∀ j < nsz2.toNat, arBase[cr.toNat + 3 + j]? = tmp2[j]? := fun j hj => by
    dsimp only [arBase]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact htmp_cp j hj
  have hlenB : arBase.length = c.arena_cap := by simp [arBase, har4]
  have hhdr_eq : fullArenaHdr sC cr.toNat = s.core.arena[cr.toNat]'hcr_bd := by
    unfold fullArenaHdr fullArenaHdrCore; rw [hsC_ar]
    change s.core.arena[cr.toNat]?.getD 0#32 = _; rw [List.getElem?_eq_getElem hcr_bd]; rfl
  constructor
  · intro hsh0
    have hsh0' : (fullArenaHdr sC cr.toNat &&& 0x00800000#32) = 0#32 := hhdr_eq.symm ▸ hsh0
    have hsz0 : ar0[cr.toNat + 2]? = some nsz2 := by
      dsimp only [ar0]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), hszB]
    have hl0 : ∀ j < nsz2.toNat, ar0[cr.toNat + 3 + j]? = tmp2[j]? := fun j hj => by
      dsimp only [ar0]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact hlB j hj
    have hlen0 : ar0.length = c.arena_cap := by simp [ar0, hlenB]
    obtain ⟨heq0, hlt0, hnd0⟩ := m6_els_ar_lits_props hsC_cv hmap2 (by omega) hsz0 hl0
    exact m6_denseInvW_inPlaceShrink hinvC hcr_ref hng_sC h3n hlt_sz_ar hlen0
      (by dsimp only [ar0]; rw [ite_eq_left hsh0', List.getElem?_set_ne (by omega),
          List.getElem?_set_self (by rw [hlenB]; omega)])
      (by rw [hsz0, show BitVec.ofNat 32 nsz2.toNat = nsz2 from by simp])
      (fun j hj1 hj2 => by
        dsimp only [ar0, arBase]; rw [hsz_eq_sC] at hj2
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
        exact hout4 (cr.toNat + 3 + j) (Or.inr (by omega)))
      (fun _ => by
        dsimp only [ar0]; change ar0[cr.toNat + 3 + fullArenaClauseSize sC cr.toNat - 1]? = _
        rw [hsz_eq_sC]; exact List.getElem?_set_self (by simp [hlenB]; omega))
      (fun h => absurd hsh0' h)
      (fun i hi => by
        change i < cr.toNat ∨ cr.toNat + 3 + fullArenaClauseSize sC cr.toNat ≤ i at hi
        rw [hsz_eq_sC] at hi; dsimp only [ar0, arBase]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
        exact hi.elim (fun h => hout4 i (Or.inl (by omega))) (fun h => hout4 i (Or.inr (by omega))))
      hlt0 hnd0 (heq0.symm ▸ hhent4)
  · intro hsh1
    have hsh1' : (fullArenaHdr sC cr.toNat &&& 0x00800000#32) ≠ 0#32 := hhdr_eq.symm ▸ hsh1
    obtain ⟨heqB, hltB, hndB⟩ := m6_els_ar_lits_props hsC_cv hmap2 (by omega) hszB hlB
    exact m6_denseInvW_inPlaceShrink hinvC hcr_ref hng_sC h3n hlt_sz_ar hlenB
      (by dsimp only [arBase]
          rw [ite_eq_right hsh1', List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            hout4 cr.toNat (Or.inl (by omega)), hhdr_eq, hsC_ar, List.getElem?_eq_getElem hcr_bd])
      (by rw [hszB, show BitVec.ofNat 32 nsz2.toNat = nsz2 from by simp])
      (fun j hj1 hj2 => by
        dsimp only [arBase]; rw [hsz_eq_sC] at hj2
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
        exact hout4 (cr.toNat + 3 + j) (Or.inr (by omega)))
      (fun h => absurd h hsh1')
      (fun _ => by
        dsimp only [arBase]; change arBase[cr.toNat + 3 + fullArenaClauseSize sC cr.toNat - 1]? = _
        rw [hsz_eq_sC, List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
        exact hout4 (cr.toNat + 3 + sz32.toNat - 1) (Or.inr (by omega)))
      (fun i hi => by
        change i < cr.toNat ∨ cr.toNat + 3 + fullArenaClauseSize sC cr.toNat ≤ i at hi
        rw [hsz_eq_sC] at hi; dsimp only [arBase]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
        exact hi.elim (fun h => hout4 i (Or.inl (by omega))) (fun h => hout4 i (Or.inr (by omega))))
      hltB hndB (heqB.symm ▸ hhent4)

private theorem m6_els_ar_same_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sC : FullState} {lm2 : List (BitVec 8)} {tmp2 ar4 : List (BitVec 32)}
    {cr sz32 nsz2 : BitVec 32} (hinvC : FullDenseInvW c F0 F_cur sC)
    (hcr_ref : cr.toNat ∈ fullArenaClauseRefs sC) (hng_cr : fullArenaClauseGarb s cr.toNat = false)
    (har4 : ar4.length = c.arena_cap) (hcr_bd2 : cr.toNat + 2 < ar4.length)
    (hsC_ar : sC.core.arena = s.core.arena) (hsC_cv : sC.core.cur_vars = s.core.cur_vars)
    (hsz_def : sz32.toNat = fullArenaClauseSize s cr.toNat) (hnsz_eq : nsz2.toNat = sz32.toNat)
    (hout4 : ∀ i, i < cr.toNat + 3 ∨ cr.toNat + 3 + nsz2.toNat ≤ i →
      ar4[i]? = sC.core.arena[i]?)
    (htmp_cp : ∀ j < nsz2.toNat, ar4[cr.toNat + 3 + j]? = tmp2[j]?)
    (hmap2 : M6ElsLitMapOk c s lm2 tmp2 nsz2.toNat)
    (hhent4 : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((tmp2.take nsz2.toNat).map BitVec.toNat))) :
    let s4 : FullState := { sC with core := { sC.core with arena := ar4 } }
    FullDenseInvW c F0 F_cur s4 ∧ fullArenaClauseRefs s4 = fullArenaClauseRefs sC := by
  have hsz_cr4 : fullArenaClauseSize sC cr.toNat = sz32.toNat := by
    unfold fullArenaClauseSize fullArenaClauseSizeCore at hsz_def ⊢; rw [hsC_ar, ← hsz_def]
  have hng_sC : fullArenaClauseGarb sC cr.toNat = false := by
    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hng_cr ⊢
    rw [hsC_ar]; exact hng_cr
  have hwf_cr := hinvC.2.1.arena.refs_wf cr.toNat hcr_ref
  have hal := hinvC.1.core_ok.arena_len_le
  have hsz_bd : cr.toNat + 3 + sz32.toNat ≤ c.arena_cap := by
    have h1 := hwf_cr.2.2.1; change cr.toNat + 3 + fullArenaClauseSize sC cr.toNat ≤ _ at h1
    rw [hsz_cr4] at h1; omega
  have hsz4 : ar4[cr.toNat + 2]? = some nsz2 := by
    rw [hout4 (cr.toNat + 2) (Or.inl (by omega))]
    have harC_l : cr.toNat + 2 < sC.core.arena.length := by
      rw [hinvC.1.core_ok.arena_len_arr, ← har4]; exact hcr_bd2
    unfold fullArenaClauseSize fullArenaClauseSizeCore at hsz_cr4
    rw [List.getElem?_eq_getElem harC_l, Option.getD_some] at hsz_cr4
    rw [List.getElem?_eq_getElem harC_l]; congr 1
    exact BitVec.eq_of_toNat_eq (hsz_cr4.trans hnsz_eq.symm)
  obtain ⟨heq4, hlt4, hnd4⟩ := m6_els_ar_lits_props hsC_cv hmap2 (by omega) hsz4 htmp_cp
  exact m6_denseInvW_replaceSameLen hinvC hcr_ref hng_sC har4
    (fun i hi => by rw [hsz_cr4, ← hnsz_eq] at hi; exact hout4 i hi) hlt4 hnd4 (heq4.symm ▸ hhent4)

private theorem m6_els_ar_ret {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sR : FullState} {R : Mem 64 → Prop} {mR : Mem 64} {Q : Post [.bool]} {ok : Bool}
    (hfr : M6ElsFrame c F0 F_cur s sR)
    (hf : ok = false → F0.Unsat ∧ sR.core.inconsistent ≠ 0#64) (hmR : (FullMem c sR ⋆ R) mR)
    (hQ : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → FullCongReprInv F_cur (2 * s.core.cur_vars) s'.core.repr →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.work_stk1 = s.scratch.work_stk1 → s'.scratch.work_stk2 = s.scratch.work_stk2 →
      s'.scratch.glue_used = s.scratch.glue_used →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) → (FullMem c s' ⋆ R) m' →
      Q (ok, ()) m') : Q (ok, ()) mR :=
  hQ ok sR mR hfr.dinv hfr.cv hfr.fuel hfr.repr hfr.tmk hfr.trh hfr.scr hfr.ws1 hfr.ws2
    hfr.gu hf hmR

private abbrev M6ElsL2Cov (F_cur : List (List Nat)) (ar tmp : List (BitVec 32))
    (cr : BitVec 32) (k nsz : Nat) : Prop :=
  ∀ i < k, let x := (ar[cr.toNat + 3 + i]?.getD 0#32).toNat
    ∃ j < nsz, LitEquiv (cnfOfClauses F_cur) x (tmp[j]?.getD 0#32).toNat

private abbrev M6ElsL2Step (c : FullCfg) (F_cur : List (List Nat)) (s : FullState)
    (reprN : List (BitVec 32)) (cr kL : BitVec 32) (R : Mem 64 → Prop)
    (nsz' : BitVec 32) (ml' : Mem 64) : Prop :=
  nsz'.toNat ≤ kL.toNat + 1 ∧ ∃ lm' tmp', M6ElsLitMapOk c s lm' tmp' nsz'.toNat ∧
    M6ElsL2Cov F_cur s.core.arena tmp' cr (kL.toNat + 1) nsz'.toNat ∧
    (FullMem c { s with core := { s.core with repr := reprN, lit_mark := lm', tmp := tmp' } } ⋆ R)
      ml'

private theorem m6_els_ar_cov_push {F_cur : List (List Nat)} {ar tmpL : List (BitVec 32)}
    {cr kL nszL rx : BitVec 32} (har : cr.toNat + 3 + kL.toNat < ar.length)
    (htmp : nszL.toNat < tmpL.length)
    (heqv : LitEquiv (cnfOfClauses F_cur) (ar[cr.toNat + 3 + kL.toNat]'har).toNat rx.toNat)
    (hcov : M6ElsL2Cov F_cur ar tmpL cr kL.toNat nszL.toNat) :
    M6ElsL2Cov F_cur ar (tmpL.set nszL.toNat rx) cr (kL.toNat + 1) (nszL.toNat + 1) := by
  intro i hi
  by_cases hik : i = kL.toNat
  · subst hik; refine ⟨nszL.toNat, by omega, ?_⟩
    rw [List.getElem?_set_self htmp, Option.getD_some, List.getElem?_eq_getElem har,
      Option.getD_some]; exact heqv
  · obtain ⟨j, hj, hje⟩ := hcov i (by omega)
    exact ⟨j, by omega, by rw [List.getElem?_set_ne (by omega)]; exact hje⟩

private theorem m6_els_ar_cov_dup {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {lmL : List (BitVec 8)} {tmpL : List (BitVec 32)} {cr kL nszL rx : BitVec 32}
    (hmap : M6ElsLitMapOk c s lmL tmpL nszL.toNat)
    (har : cr.toNat + 3 + kL.toNat < s.core.arena.length)
    (hrx_lt : rx.toNat < 2 * s.core.cur_vars) (h0_nz : lmL[rx.toNat]?.getD 0#8 ≠ 0#8)
    (heqv : LitEquiv (cnfOfClauses F_cur)
      (s.core.arena[cr.toNat + 3 + kL.toNat]'har).toNat rx.toNat)
    (hcov : M6ElsL2Cov F_cur s.core.arena tmpL cr kL.toNat nszL.toNat) :
    M6ElsL2Cov F_cur s.core.arena tmpL cr (kL.toNat + 1) nszL.toNat := by
  intro i hi
  by_cases hik : i = kL.toNat
  · subst hik; have hml := hmap.map rx.toNat (by have := hmap.cv_le; omega)
    by_cases hex : ∃ j < nszL.toNat, (tmpL[j]?.getD 0#32).toNat = rx.toNat
    · obtain ⟨j, hj, hje⟩ := hex
      exact ⟨j, hj, by rw [hje, List.getElem?_eq_getElem har, Option.getD_some]; exact heqv⟩
    · exfalso; rw [decide_eq_false hex] at hml; exact h0_nz hml
  · exact hcov i (by omega)

private theorem m6_take1_map : ∀ (xs : List (BitVec 32)) (h : 0 < xs.length),
    (xs.take 1).map BitVec.toNat = [(xs[0]'h).toNat]
  | _ :: _, _ => rfl

private theorem m6_take2_map : ∀ (xs : List (BitVec 32)) (h : 1 < xs.length),
    (xs.take 2).map BitVec.toNat = [(xs[0]'(by omega)).toNat, (xs[1]'h).toNat]
  | _ :: _ :: _, _ => rfl

private theorem m6_lm_eq0_of_zext {lm : List (BitVec 8)} {idx : Nat} (hbd : idx < lm.length)
    (h : BitVec.setWidth 32 (lm[idx]'hbd) = 0#32) : lm[idx]?.getD 0#8 = 0#8 := by
  rw [List.getElem?_eq_getElem hbd, Option.getD_some, ← m6_bv8_zext32_eq0_iff]; exact h

private theorem m6_lm_ne0_of_zext {lm : List (BitVec 8)} {idx : Nat} (hbd : idx < lm.length)
    (h : BitVec.setWidth 32 (lm[idx]'hbd) ≠ 0#32) : lm[idx]?.getD 0#8 ≠ 0#8 := by
  rw [List.getElem?_eq_getElem hbd, Option.getD_some]; intro he
  exact h ((m6_bv8_zext32_eq0_iff _).mpr he)

private theorem m6_els_ar_hdr_eq {s s' : FullState} {cr : BitVec 32}
    (har : s'.core.arena = s.core.arena) (hbd : cr.toNat < s.core.arena.length) :
    s.core.arena[cr.toNat]'hbd = fullArenaHdr s' cr.toNat := by
  unfold fullArenaHdr fullArenaHdrCore; rw [har, List.getElem?_eq_getElem hbd, Option.getD_some]

/-! ## 5. `full_m6_els_ar_wp` -/

theorem full_m6_els_ar_wp (Γ : Env)
    (hFind : Γ.Has "full_cong_find" fullCongFindSpec)
    (hWatch : Γ.Has "full_watch_push" fullWatchPushSpec)
    (hAddUnit : Γ.Has "full_add_unit" fullAddUnitSpec)
    (hAddBin : Γ.Has "full_add_bin" fullAddBinSpec) :
    ∀ args m Q X, fullM6ElsArSpec args m Q X → Func.wp Γ full_m6_els_ar_body args m Q X := by
  rintro ⟨h, cr, rl, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv, hcr_ref, hrl_lt, hrepr_inv, hm, hQ⟩
  have hcl := hinv.1.core_ok; have hw := hinv.2.1; have hmx := c.hmaxv
  have har := c.harena; have hwc := c.hwcap; unfold dimacsBound at hmx har hwc
  have hcv_le := hcl.cur_vars_le; have hal_le := hcl.arena_len_le
  have har_len := hcl.arena_len_arr; have hrp_len := hcl.repr_len
  have hwf_cr := hw.arena.refs_wf cr.toNat hcr_ref
  have hcr_bd : cr.toNat < s.core.arena.length := by have := hwf_cr.2.2.1; omega
  have hcr2_bd : cr.toNat + 2 < s.core.arena.length := by have := hwf_cr.2.2.1; omega
  have hcr1_eq : (cr.setWidth 64 + 1#64).toNat = cr.toNat + 1 := by bv_omega
  have hcr2_eq : (cr.setWidth 64 + 2#64).toNat = cr.toNat + 2 := by bv_omega
  have hcr2_mod : (cr.toNat + 2) % 2 ^ 64 = cr.toNat + 2 := Nat.mod_eq_of_lt (by omega)
  let sz32 := s.core.arena[cr.toNat + 2]'hcr2_bd
  have hsz_c : fullArenaClauseSizeCore s.core cr.toNat = sz32.toNat := by
    unfold fullArenaClauseSizeCore; rw [List.getElem?_eq_getElem hcr2_bd, Option.getD_some]
  have hsz3 : 3 ≤ sz32.toNat := by simpa [hsz_c] using hwf_cr.2.1
  have hsz_core_bd : cr.toNat + 3 + sz32.toNat ≤ s.core.arena_len := by have := hwf_cr.2.2.1; omega
  have hsz32_mod : s.core.arena[(cr.toNat + 2) % 2 ^ 64]'(by rw [hcr2_mod]; exact hcr2_bd) = sz32 :=
    m6_list_getElem_congr hcr2_mod (by rw [hcr2_mod]; exact hcr2_bd) hcr2_bd
  have hsz_toNat := congrArg BitVec.toNat hsz32_mod
  unfold Func.wp full_m6_els_ar_body
  c0_hsplit; · exfalso; bv_omega
  c0_hsplit; · c0_hsteps!; exact m6_els_ar_ret (ok := true) ⟨hinv, rfl, rfl, hrepr_inv, rfl, rfl,
                 rfl, rfl, rfl, rfl⟩ (fun h => Bool.noConfusion h) hm hQ
  c0_hsplit; · exfalso; have h2 : (s.core.arena[(cr.toNat + 2) % 2 ^ 64]'(by
                 rw [hcr2_mod]; exact hcr2_bd)).toNat < 3 := hc; rw [hsz_toNat] at h2; omega
  c0_hsplit; · exfalso; have hlt : s.core.arena_len % 2 ^ 64 < (cr.toNat + 3 + (s.core.arena[
                 (cr.toNat + 2) % 2 ^ 64]'(by rw [hcr2_mod]; exact hcr2_bd)).toNat) % 2 ^ 64 := hc
               rw [hsz_toNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hlt
               omega
  have hng_cr : fullArenaClauseGarb s cr.toNat = false := by
    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
    rw [List.getElem?_eq_getElem hcr_bd, Option.getD_some]
    simpa [BitVec.toNat_and, show (0x00080000#32).toNat = 0x80000 from rfl] using
      (by assumption : (s.core.arena[cr.toNat]'hcr_bd &&& 0x00080000#32) = 0#32)
  have hsz_ar_bd : cr.toNat + 3 + sz32.toNat ≤ s.core.arena.length := by omega
  have hsz_lt_dim : sz32.toNat < 2 ^ 31 := by omega
  have hcr_lt_dim : cr.toNat < 0x80000000 := by omega
  have hcr_ne : cr ≠ 0xFFFFFFFF#32 := by intro h'; rw [h'] at hcr_lt_dim; revert hcr_lt_dim; decide
  have hlits_lt_k : ∀ i (hi : i < sz32.toNat),
      (s.core.arena[cr.toNat + 3 + i]'(by omega)).toNat < 2 * s.core.cur_vars := fun i hi =>
    hw.arena.lits_lt cr.toNat hcr_ref hng_cr _ (by
      rw [mem_fullArenaClauseLitsCore_iff (by rw [hsz_c]; omega)]
      exact ⟨i, by rw [hsz_c]; exact hi, rfl⟩)
  have hmaxv_pos : 0 < c.max_vars := by have := hlits_lt_k 0 (by omega); omega
  have hent_cr := hw.arena.entails cr.toNat hcr_ref hng_cr
  have hnlits_m := m6_nlits_mod64 (by omega : 2 * s.core.cur_vars < 2 ^ 64); c0_hsteps_nogrp
  refine wp_join_state (ts := [.bool, i32]) (proj := fun p : Bool × BitVec 32 => (p.1, p.2, ()))
    (fun (_chg, _k) m1 => ∃ repr1 : List (BitVec 32), repr1.length = 2 * c.max_vars ∧
      FullCongReprInv F_cur (2 * s.core.cur_vars) repr1 ∧
      (FullMem c { s with core := { s.core with repr := repr1 } } ⋆ R) m1) ?_ ?_
  · rintro _ ⟨chg1, _k1⟩ m1 ⟨repr1, hrp1_len, hrepr1, hm1⟩
    let s1 : FullState := { s with core := { s.core with repr := repr1 } }
    have hinv1 := m6_fullDenseInvW_set_repr hinv hrp1_len
    have hfr1 : M6ElsFrame c F0 F_cur s s1 := ⟨hinv1, rfl, rfl, hrepr1, rfl, rfl, rfl, rfl, rfl,
      rfl⟩
    c0_hsplit
    · c0_hsteps_nogrp
      refine wp_join_state (ts := [.bool, i32]) (proj := fun p : Bool × BitVec 32 => (p.1, p.2, ()))
        (fun _ mH => mH = m1) ?_ ?_
      · rintro _ ⟨has_rl, _hk⟩ mH hmH; subst mH; c0_hsteps_nogrp
        refine wp_join_state (ts := [i32, .bool, i32])
          (proj := fun p : BitVec 32 × Bool × BitVec 32 => (p.1, p.2.1, p.2.2, ()))
          (fun (_k2, taut2, nsz2) m2 => ∃ (repr2 : List (BitVec 32))
              (lm2 : List (BitVec 8)) (tmp2 : List (BitVec 32)),
            repr2.length = 2 * c.max_vars ∧ FullCongReprInv F_cur (2 * s.core.cur_vars) repr2 ∧
            nsz2.toNat ≤ sz32.toNat ∧ M6ElsLitMapOk c s lm2 tmp2 nsz2.toNat ∧
            (taut2 = false → M6ElsL2Cov F_cur s.core.arena tmp2 cr sz32.toNat nsz2.toNat) ∧
            (FullMem c { s with core :=
              { s.core with repr := repr2, lit_mark := lm2, tmp := tmp2 } } ⋆ R) m2) ?_ ?_
        · rintro _ ⟨_k2, taut2, nsz2⟩ m2 ⟨repr2, lm2, tmp2, hrp2_len, hrepr2, hnsz_sz, hmap2,
              hcov2, hm2⟩; c0_hsteps_nogrp
          refine wp_while_state (ts := [i32]) (proj := fun k : BitVec 32 => (k, ()))
            (μ := fun k => nsz2.toNat - k.toNat)
            (Inv := fun k ml => k.toNat ≤ nsz2.toNat ∧ ∃ lmL : List (BitVec 8),
              lmL.length = 2 * c.max_vars ∧
              (∀ l < 2 * c.max_vars, lmL[l]?.getD 0#8 =
                if decide (∃ j < nsz2.toNat, k.toNat ≤ j ∧
                  (tmp2[j]?.getD 0#32).toNat = l) then 1#8 else 0#8) ∧
              (FullMem c { s with core :=
                { s.core with repr := repr2, lit_mark := lmL, tmp := tmp2 } } ⋆ R) ml) ?_ ?_
          · intro J3 hJ3; c0_hsteps!
            exact hJ3 0#32 m2 ⟨Nat.zero_le _, lm2, hmap2.lm_len, fun l hl => by
              rw [hmap2.map l hl]
              simp only [show (0#32 : BitVec 32).toNat = 0 from rfl, Nat.zero_le, true_and], hm2⟩
          · rintro J3 k3 ml ⟨hk3, lm3, hlm3, hmap3, hml⟩ ih3; c0_hsplit
            · have hk_lt : k3.toNat < nsz2.toNat := hc
              have hk1 : (k3 + 1#32).toNat = k3.toNat + 1 := by bv_omega
              have hnsz_le := hmap2.nsz_le; have htl := hmap2.tmp_len
              have htk_lt : (tmp2[k3.toNat]'(by omega)).toNat < 2 * s.core.cur_vars := by
                have := hmap2.tmp_lt k3.toNat hk_lt
                rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
              have htk_bd64 : (k3.setWidth 64).toNat < tmp2.length := by rw [bv_c0_zext32_64]; omega
              have hidx_tk : ((tmp2[(k3.setWidth 64).toNat]'htk_bd64).setWidth 64).toNat =
                  (tmp2[k3.toNat]'(by omega)).toNat := by
                rw [bv_c0_zext32_64, m6_list_getElem_congr (bv_c0_zext32_64 k3) htk_bd64 (by omega)]
              have htk_lm64 : ((tmp2[(k3.setWidth 64).toNat]'htk_bd64).setWidth 64).toNat <
                  lm3.length := by rw [hidx_tk, hlm3]; omega
              dsimp only [Prod.fst]; c0_hsteps_nogrp
              exact ih3 (k3 + 1#32) _ (by rw [hk1]; omega) ⟨by omega,
                lm3.set (tmp2[k3.toNat]'(by omega)).toNat 0#8, by simp [hlm3],
                by rw [hk1]; exact m6_els_ar_loop3_step_ok hmap2 hk_lt hlm3 hmap3,
                by rw [← hidx_tk]; assumption⟩
            · have hk_eq : k3.toNat = nsz2.toNat := Nat.le_antisymm hk3 (Nat.le_of_not_lt hc)
              let sC : FullState :=
                { s with core := { s.core with repr := repr2, lit_mark := lm3, tmp := tmp2 } }
              have hinvC := m6_denseInvW_set_repr_lm_tmp hinv hrp2_len hlm3 hmap2.tmp_len
                fun l hl => by rw [hmap3 l hl, hk_eq,
                  decide_eq_false (by rintro ⟨j, h1, h2, _⟩; omega)]; rfl
              have hfrC : M6ElsFrame c F0 F_cur s sC :=
                ⟨hinvC, rfl, rfl, hrepr2, rfl, rfl, rfl, rfl, rfl, rfl⟩
              have hent_tmp := fun htf => m6_els_ar_hent_tmp hsz_c hsz_ar_bd hent_cr hmap2
                (hcov2 htf)
              have hhd_sC := m6_els_ar_hdr_eq (s' := sC) rfl hcr_bd; c0_hsteps_nogrp
              refine wp_join_group (ts := []) (fun () m_garb =>
                  (taut2 = true ∨ nsz2.toNat ≤ 2) ∧ (FullMem c sC ⋆ R) m_garb) ?_ ?_
              · rintro _ ⟨⟩ m_garb ⟨_, hm_g0⟩
                let ag' := sC.core.arena_garbage + 3#64 + sz32.setWidth 64
                obtain ⟨hinvG, _⟩ := m6_denseInvW_markGarb hinvC hcr_ref ag'
                let sG : FullState := { sC with core := { sC.core with
                  arena := sC.core.arena.set cr.toNat (fullArenaHdr sC cr.toNat ||| 0x00080000#32),
                  arena_garbage := ag' } }
                have hfrG : M6ElsFrame c F0 F_cur s sG :=
                  ⟨hinvG, rfl, rfl, hrepr2, rfl, rfl, rfl, rfl, rfl, rfl⟩
                have hag_eq : sC.core.arena_garbage + 3#64 + (s.core.arena[(cr.toNat + 2) % 2 ^ 64]'
                    (by rw [hcr2_mod]; exact hcr2_bd)).setWidth 64 = ag' := by
                  dsimp only [ag']; rw [hsz32_mod]
                c0_hsteps_nogrp
                refine wp_join_group (ts := []) (fun () mU => (FullMem c sG ⋆ R) mU) ?_ ?_
                · rintro _ ⟨⟩ mU hmU
                  refine wp_join_group (ts := []) (fun () mB => ∃ sB : FullState,
                      M6ElsFrame c F0 F_cur s sB ∧ sB.core.tmp = tmp2 ∧ (FullMem c sB ⋆ R) mB) ?_ ?_
                  · rintro _ ⟨⟩ mB ⟨sB, hfrB, htmpB, hmB⟩
                    refine wp_join_group (ts := []) (fun () mRet => ∃ sR : FullState,
                        M6ElsFrame c F0 F_cur s sR ∧ (FullMem c sR ⋆ R) mRet)
                      (fun _ () mRet ⟨sR, hfrR, hmR⟩ => by
                        c0_hsteps!; exact m6_els_ar_ret (ok := true) hfrR (by simp) hmR hQ) ?_
                    intro JW hJW; c0_hsplit; · c0_hsteps!; exact hJW () mB ⟨sB, hfrB, hmB⟩
                    have htf : taut2 = false := by cases taut2 <;> first | rfl | contradiction
                    c0_hsplit; rotate_left; · c0_hsteps!; exact hJW () mB ⟨sB, hfrB, hmB⟩
                    have hn2 : nsz2.toNat = 2 := by bv_omega
                    have htl := hmap2.tmp_len; have hnl := hmap2.nsz_le
                    have hent2 := hent_tmp htf; rw [hn2, m6_take2_map tmp2 (by omega)] at hent2
                    have htmp_lenB := hfrB.dinv.1.core_ok.tmp_len_arr
                    have htmp0B : 0 < sB.core.tmp.length := by omega
                    have htmp1B : 1 < sB.core.tmp.length := by omega
                    c0_hsteps_nogrp
                    refine m6_call_add_bin hAddBin hfrB (by
                        simpa only [htmpB, BitVec.toNat_ofNat, Nat.zero_mod,
                          Nat.mod_eq_of_lt (by decide : 1 < 2 ^ 64)] using hent2)
                      hmB fun rB sBn mBn hfrBn hr20 hmBn => ?_
                    c0_hsplit; · c0_hsteps!; exact m6_els_ar_ret (ok := false) hfrBn
                                   (fun _ => hr20 (by bv_omega)) hmBn hQ
                    try refine wp_unroll_group fun _ _ => ?_
                    c0_hsplit; · c0_hsteps!; exact hJW () _ ⟨_, hfrBn.set_oom, by assumption⟩
                    · c0_hsteps!; exact hJW () mBn ⟨sBn, hfrBn, hmBn⟩
                  · intro J5 hJ5; c0_hsplit; · c0_hsteps!; exact hJ5 () mU ⟨sG, hfrG, rfl, hmU⟩
                    have htf : taut2 = false := by cases taut2 <;> first | rfl | contradiction
                    c0_hsplit; rotate_left; · c0_hsteps!; exact hJ5 () mU ⟨sG, hfrG, rfl, hmU⟩
                    have hn1 : nsz2.toNat = 1 := by bv_omega
                    have htl := hmap2.tmp_len; have hnl := hmap2.nsz_le
                    have hent1 := hent_tmp htf; rw [hn1, m6_take1_map tmp2 (by omega)] at hent1
                    have htmp0_lt : (tmp2[0]'(by omega)).toNat < 2 * sG.core.cur_vars := by
                      have := hmap2.tmp_lt 0 (by omega)
                      rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
                    have htmp_posG : 0 < sG.core.tmp.length := by
                      rw [hinvG.1.core_ok.tmp_len_arr]; omega
                    c0_hsteps_nogrp
                    refine m6_call_add_unit hAddUnit hfrG htmp0_lt hent1 hmU
                      fun okU sU mUn hfrU htmpU hfail hmUn => ?_
                    c0_hsplit; · c0_hsteps!; exact hJ5 () mUn ⟨sU, hfrU, htmpU, hmUn⟩
                    · have hokf : okU = false := by cases okU <;> first | rfl | contradiction
                      c0_hsteps!; exact m6_els_ar_ret (ok := false) hfrU (fun _ => hfail hokf)
                        hmUn hQ
                · intro J4 hJ4
                  c0_hsplit; · c0_hsteps!; refine hJ4 () _ ?_; dsimp only [sG]
                               rw [← hhd_sC, ← hag_eq]; assumption
                  have htf : taut2 = false := by cases taut2 <;> first | rfl | contradiction
                  c0_hsplit
                  · have hnz : nsz2.toNat = 0 := by bv_omega
                    have hent0 := hent_tmp htf; rw [hnz, List.take_zero, List.map_nil] at hent0
                    have huns := m6_unsat_of_nil_entails hent0; c0_hsteps!
                    refine m6_els_ar_ret (ok := false)
                      ⟨m6_fullDenseInvW_set_inconsistent hinvG huns, rfl, rfl, hrepr2, rfl, rfl,
                        rfl, rfl, rfl, rfl⟩ (fun _ => ⟨hinvG.2.1.ext_sound.2 huns, by simp⟩) ?_ hQ
                    dsimp only [sG]; rw [← hhd_sC, ← hag_eq]; assumption
                  · c0_hsteps!; refine hJ4 () _ ?_; dsimp only [sG]; rw [← hhd_sC, ← hag_eq]
                    assumption
              · intro J3 hJ3
                c0_hsplit; · c0_hsteps!; exact hJ3 () _ ⟨Or.inl ‹_›, hml⟩
                c0_hsplit; · c0_hsteps!; exact hJ3 () _ ⟨Or.inr ‹_›, hml⟩
                have htf : taut2 = false := by cases taut2 <;> first | rfl | contradiction
                have h3n : 3 ≤ nsz2.toNat := by bv_omega
                have hnsz_le := hmap2.nsz_le; c0_hsteps_nogrp
                refine wp_while_state (ts := [i32]) (proj := fun k : BitVec 32 => (k, ()))
                  (μ := fun k => nsz2.toNat - k.toNat)
                  (Inv := fun k ml => k.toNat ≤ nsz2.toNat ∧ ∃ ar4 : List (BitVec 32),
                    ar4.length = c.arena_cap ∧
                    (∀ i, i < cr.toNat + 3 ∨ cr.toNat + 3 + k.toNat ≤ i →
                      ar4[i]? = sC.core.arena[i]?) ∧
                    (∀ j < k.toNat, ar4[cr.toNat + 3 + j]? = tmp2[j]?) ∧
                    (FullMem c { sC with core := { sC.core with arena := ar4 } } ⋆ R) ml) ?_ ?_
                · intro J4 hJ4; c0_hsteps!
                  exact hJ4 0#32 _ ⟨Nat.zero_le _, sC.core.arena, hcl.arena_len_arr,
                    fun _ _ => rfl, (fun _ hj => by cases hj), hml⟩
                · rintro J4 k4 ml ⟨hk4, ar4, har4, hout4, hcp4, hml⟩ ih4; c0_hsplit
                  · have hk4_lt : k4.toNat < nsz2.toNat := hc
                    have hk1 : (k4 + 1#32).toNat = k4.toNat + 1 := by bv_omega
                    have htk_bd : k4.toNat < tmp2.length := by have := hmap2.tmp_len; omega
                    have htk_bd64 : (k4.setWidth 64).toNat < tmp2.length := by
                      rw [bv_c0_zext32_64]; exact htk_bd
                    have hidx_4_c0 : (cr.setWidth 64 + (3 : BitVec 64) + k4.setWidth 64).toNat =
                        cr.toNat + 3 + k4.toNat := by bv_omega
                    have har_bd : cr.toNat + 3 + k4.toNat < ar4.length := by rw [har4]; omega
                    dsimp only [Prod.fst]; c0_hsteps_nogrp
                    have htmp_eq := m6_list_getElem_congr (xs := tmp2) (bv_c0_zext32_64 k4)
                      htk_bd64 htk_bd
                    refine ih4 (k4 + 1#32) _ (by rw [hk1]; omega) ⟨by omega,
                      ar4.set (cr.toNat + 3 + k4.toNat) (tmp2[k4.toNat]'htk_bd), by simp [har4],
                      fun i hi => by rw [List.getElem?_set_ne (by omega)]
                                     exact hout4 i (hi.imp id fun h => by rw [hk1] at h; omega),
                      fun j hj => by
                        by_cases hjk : j = k4.toNat
                        · subst hjk; rw [List.getElem?_set_self har_bd, List.getElem?_eq_getElem
                            htk_bd]
                        · rw [List.getElem?_set_ne (by omega)]; exact hcp4 j (by omega),
                      by first | (rw [← hidx_4_c0]; assumption)
                               | (rw [← hidx_4_c0, ← htmp_eq]; assumption)⟩
                  · have hk_eq : k4.toNat = nsz2.toNat := Nat.le_antisymm hk4 (Nat.le_of_not_lt hc)
                    rw [hk_eq] at hout4 hcp4; have hhent4 := hent_tmp htf; c0_hsteps_nogrp
                    refine wp_join_group (ts := []) (fun () m5 => ∃ ar5 : List (BitVec 32),
                        let s5 := { sC with core := { sC.core with arena := ar5 } }
                        FullDenseInvW c F0 F_cur s5 ∧
                        fullArenaClauseRefs s5 = fullArenaClauseRefs sC ∧ (FullMem c s5 ⋆ R) m5)
                      ?_ ?_
                    · rintro _ ⟨⟩ m5 ⟨ar5, hinv5, hrefs5, hm5⟩
                      have hfr5 : M6ElsFrame c F0 F_cur s
                          { sC with core := { sC.core with arena := ar5 } } :=
                        ⟨hinv5, rfl, rfl, hrepr2, rfl, rfl, rfl, rfl, rfl, rfl⟩
                      c0_hsteps_nogrp
                      refine wp_join_group (ts := []) (fun () mRet => ∃ sR : FullState,
                          M6ElsFrame c F0 F_cur s sR ∧ (FullMem c sR ⋆ R) mRet)
                        (fun _ () mRet ⟨sR, hfrR, hmR⟩ => by
                          c0_hsteps!; exact m6_els_ar_ret (ok := true) hfrR (by simp) hmR hQ) ?_
                      intro JW hJW; c0_hsplit; · c0_hsteps!; exact hJW () m5 ⟨_, hfr5, hm5⟩
                      c0_hsteps_nogrp
                      refine m6_els_ar_push_watched hWatch rfl rfl rfl rfl rfl hfr5 h3n (by omega)
                        hcr_lt_dim hcr_ne (hrefs5 ▸ hcr_ref) hm5 fun ok s' m' hfr' hm' => ?_
                      c0_hsplit; · c0_hsteps!; exact hJW () m' ⟨s', hfr', hm'⟩
                      · c0_hsteps!; exact hJW () _ ⟨_, hfr'.set_oom, by assumption⟩
                    · intro J5 hJ5
                      have hcr_bd2 : cr.toNat + 2 < ar4.length := by rw [har4]; omega
                      c0_hsplit
                      · have hlt_sz : nsz2.toNat < sz32.toNat := hsz_toNat ▸ hc
                        obtain ⟨hsh0_ok, hsh1_ok⟩ := m6_els_ar_shrink_ok hinvC hcr_ref hng_cr
                          hcr_bd har4 hcr_bd2 rfl rfl hsz_c.symm h3n hlt_sz hout4 hcp4 hmap2 hhent4
                        c0_hsteps_nogrp; rw [hcr2_eq, hcr1_eq] at *
                        refine wp_join_group (ts := []) (fun () m6 => ∃ ar5 : List (BitVec 32),
                            let s5 := { sC with core := { sC.core with arena := ar5 } }
                            FullDenseInvW c F0 F_cur s5 ∧
                            fullArenaClauseRefs s5 = fullArenaClauseRefs sC ∧ (FullMem c s5 ⋆ R) m6)
                          (fun _ () m6 h6 => by c0_hsteps!; exact hJ5 () m6 h6) ?_
                        intro J6 hJ6
                        have hcr2_bv : (cr.setWidth 64 + 2#64).toNat = cr.toNat + 2 := by bv_omega
                        have hcr1_bv : (cr.setWidth 64 + 1#64).toNat = cr.toNat + 1 := by bv_omega
                        c0_hsplit
                        · obtain ⟨hinv5, hrefs5⟩ := hsh0_ok hc
                          have hcr3_bv : (cr.setWidth 64 + 3#64 + sz32.setWidth 64 - 1#64).toNat =
                              cr.toNat + 3 + sz32.toNat - 1 := by bv_omega
                          have hcr3_mod : (cr.setWidth 64 + 3#64 + (s.core.arena[(cr.toNat + 2) %
                              2 ^ 64]'(by rw [hcr2_mod]; exact hcr2_bd)).setWidth 64 - 1#64).toNat
                              = cr.toNat + 3 + sz32.toNat - 1 := by rw [hsz32_mod]; exact hcr3_bv
                          c0_hsteps!; refine hJ6 () _ ⟨_, hinv5, hrefs5, ?_⟩
                          dsimp only; rw [← hhd_sC, ← hcr2_bv, ← hcr1_bv]
                          first | (rw [← hcr3_bv]; assumption) | (rw [← hcr3_mod]; assumption)
                                | (rw [← hcr3_bv, ← bv_c0_zext32_64 cr]; assumption)
                                | (rw [← hcr3_mod, ← bv_c0_zext32_64 cr]; assumption)
                        · obtain ⟨hinv5, hrefs5⟩ := hsh1_ok hc
                          c0_hsteps!; refine hJ6 () _ ⟨_, hinv5, hrefs5, ?_⟩
                          dsimp only; rw [← hcr2_bv, ← hcr1_bv]; assumption
                      · have hnsz_eq : nsz2.toNat = sz32.toNat :=
                          Nat.le_antisymm hnsz_sz (Nat.le_of_not_lt (hsz_toNat ▸ hc))
                        obtain ⟨hinv4, hrefs4⟩ := m6_els_ar_same_ok hinvC hcr_ref hng_cr har4
                          hcr_bd2 rfl rfl hsz_c.symm hnsz_eq hout4 hcp4 hmap2 hhent4
                        c0_hsteps!; exact hJ5 () ml ⟨ar4, hinv4, hrefs4, by assumption⟩
        · intro J2 hJ2; c0_hsteps_nogrp
          refine wp_while_state (ts := [i32, i32]) (proj := fun p : BitVec 32 × BitVec 32 =>
              (p.1, p.2, ())) (μ := fun p => sz32.toNat - p.1.toNat)
            (Inv := fun p ml => p.1.toNat ≤ sz32.toNat ∧ p.2.toNat ≤ p.1.toNat ∧
              ∃ (repr2 : List (BitVec 32)) (lm2 : List (BitVec 8)) (tmp2 : List (BitVec 32)),
                repr2.length = 2 * c.max_vars ∧ FullCongReprInv F_cur (2 * s.core.cur_vars) repr2 ∧
                M6ElsLitMapOk c s lm2 tmp2 p.2.toNat ∧
                M6ElsL2Cov F_cur s.core.arena tmp2 cr p.1.toNat p.2.toNat ∧
                (FullMem c { s with core :=
                  { s.core with repr := repr2, lit_mark := lm2, tmp := tmp2 } } ⋆ R) ml) ?_ ?_
          · intro L2 hL2; c0_hsteps!; exact hL2 (0#32, 0#32) m1 ⟨Nat.zero_le _, Nat.zero_le _,
              repr1, s.core.lit_mark, s.core.tmp, hrp1_len, hrepr1, m6_elsLitMapOk_init hinv,
              (fun _ hi => by cases hi), hm1⟩
          · rintro L2 ⟨kL, nszL⟩ ml ⟨hk_le, hnk, reprL, lmL, tmpL, hrpL_len, hreprL, hmapL, hcovL,
              hml⟩ ih2; dsimp only at *; c0_hsplit
            · have hk_lt : kL.toNat < sz32.toNat := hsz_toNat ▸ hc
              have hk1 : (kL + 1#32).toNat = kL.toNat + 1 := by bv_omega
              have hnszL := hmapL.nsz_le; have hlmL := hmapL.lm_len; have htmpL := hmapL.tmp_len
              have hidx_k_mod : (cr.toNat + 3 + kL.toNat) % 2 ^ 64 = cr.toNat + 3 + kL.toNat :=
                Nat.mod_eq_of_lt (by omega)
              have hx_bd : cr.toNat + 3 + kL.toNat < s.core.arena.length := by omega
              have hx_lt := hlits_lt_k kL.toNat hk_lt; dsimp only [Prod.fst]; c0_hsteps_nogrp
              refine wp_join_state (ts := [i32]) (proj := fun rx : BitVec 32 => (rx, ()))
                (fun rx ml1 => rx.toNat < 2 * s.core.cur_vars ∧ LitEquiv (cnfOfClauses F_cur)
                    (s.core.arena[cr.toNat + 3 + kL.toNat]'hx_bd).toNat rx.toNat ∧
                  ∃ reprN : List (BitVec 32), reprN.length = 2 * c.max_vars ∧
                    FullCongReprInv F_cur (2 * s.core.cur_vars) reprN ∧ (FullMem c { s with
                      core := { s.core with repr := reprN, lit_mark := lmL, tmp := tmpL } } ⋆ R)
                    ml1) ?_ ?_
              · rintro _ rx ml1 ⟨hrx_lt, hrx_eqv, reprN, hrpN_len, hreprN, hml1⟩
                have hrx_xor : (rx ^^^ 1#32).toNat < 2 * s.core.cur_vars := by
                  rw [m6_els_bv32_xor1_toNat]; exact m6_nat_xor1_lt hrx_lt
                c0_hsteps_nogrp
                refine wp_join_state (ts := [.bool, i32]) (proj := fun p : Bool × BitVec 32 =>
                    (p.1, p.2, ()))
                  (fun (_, nsz') ml' => M6ElsL2Step c F_cur s reprN cr kL R nsz' ml')
                  (fun _ ⟨_, nsz'⟩ ml' ⟨hnk', lm', tmp', hmap', hcov', hm'⟩ => by
                    c0_hsteps!; exact @ih2 (kL + 1#32, nsz') ml' (by dsimp only; rw [hk1]; omega)
                      ⟨by dsimp only; rw [hk1]; omega, by dsimp only; rw [hk1]; exact hnk',
                       reprN, lm', tmp', hrpN_len, hreprN, hmap',
                       (by simpa only [hk1] using hcov'), hm'⟩) ?_
                intro J4 hJ4; c0_hsplit; rotate_left
                · exfalso; simp only [bv_c0,
                    Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64), hnlits_m] at hc; omega
                c0_hsplit
                · c0_hsteps!; exact hJ2 (kL, true, nszL) ml1 ⟨reprN, lmL, tmpL, hrpN_len, hreprN,
                    by dsimp only; omega, hmapL, (fun h => Bool.noConfusion h), hml1⟩
                · have h1_zero : lmL[(rx ^^^ 1#32).toNat]?.getD 0#8 = 0#8 :=
                    m6_lm_eq0_of_zext (by rw [hlmL]; omega) (by
                      simpa only [m6_els_bv32_xor1_toNat] using (hc : BitVec.setWidth 32
                        (lmL[rx.toNat ^^^ 1]'(by rw [← m6_els_bv32_xor1_toNat, hlmL]; omega)) =
                        0#32))
                  refine wp_join_state (ts := [i32]) (proj := fun n : BitVec 32 => (n, ()))
                    (M6ElsL2Step c F_cur s reprN cr kL R)
                    (fun _ nsz' ml' hst => by c0_hsteps!; exact hJ4 (false, nsz') ml' hst) ?_
                  intro J5 hJ5; c0_hsplit
                  · obtain ⟨hnsz_mx, hmap'⟩ := m6_elsLitMapOk_push hmapL hrx_lt
                      (m6_lm_eq0_of_zext (by rw [hlmL]; omega) hc) h1_zero
                    have hnsz_lt_tl : (BitVec.setWidth 64 nszL).toNat < tmpL.length := by
                      rw [htmpL, bv_c0_zext32_64]; omega
                    c0_hsplit; rotate_left; · exfalso; rw [bv_c0_zext32_64] at *; omega
                    have hnsz1 : (nszL + 1#32).toNat = nszL.toNat + 1 := by bv_omega
                    c0_hsteps!; exact hJ5 (nszL + 1#32) _ ⟨by rw [hnsz1]; omega, _, _,
                      by rw [hnsz1]; exact hmap',
                      by rw [hnsz1]; exact m6_els_ar_cov_push hx_bd (by omega) hrx_eqv hcovL,
                      by assumption⟩
                  · c0_hsteps!; exact hJ5 nszL ml1 ⟨by omega, lmL, tmpL, hmapL,
                      m6_els_ar_cov_dup hmapL hx_bd hrx_lt
                        (m6_lm_ne0_of_zext (by rw [hlmL]; omega) hc) hrx_eqv hcovL, hml1⟩
              · intro J3 hJ3
                have hidx_k_c0 : (cr.setWidth 64 + (3 : BitVec 64) + kL.setWidth 64).toNat =
                    cr.toNat + 3 + kL.toNat := by bv_omega
                rw [hidx_k_mod] at *; c0_hsplit
                · c0_hsteps_nogrp
                  refine m6_call_cong_find hFind hreprL (by
                      rw [m6_list_getElem_congr hidx_k_c0 _ hx_bd]; exact hx_lt) hml
                    fun rx reprN mlN hrpN_l hreprN _ hrx_lt hrx_eqv hmlN => ?_
                  c0_hsteps!; exact hJ3 rx mlN ⟨hrx_lt, (m6_list_getElem_congr hidx_k_c0 _ hx_bd) ▸
                    hrx_eqv, reprN, hrpN_l.trans hrpL_len, hreprN, hmlN⟩
                · exfalso
                  have hidx_l' : (cr.toNat + (3 : BitVec 64).toNat + kL.toNat) % 2 ^ 64 =
                      cr.toNat + 3 + kL.toNat := by
                    change (cr.toNat + 3 + kL.toNat) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
                  simp only [bv_c0, hidx_l',
                    Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64), hnlits_m] at hc; omega
            · have hk_eq : kL.toNat = sz32.toNat :=
                Nat.le_antisymm hk_le (Nat.le_of_not_lt (hsz_toNat ▸ hc))
              c0_hsteps!; exact hJ2 (kL, false, nszL) ml ⟨reprL, lmL, tmpL, hrpL_len, hreprL,
                by dsimp only; omega, hmapL, fun _ i hi => hcovL i (hk_eq ▸ hi), hml⟩
      · intro JH hJH; c0_hsteps_nogrp
        refine wp_while_state (ts := [i32]) (proj := fun hk : BitVec 32 => (hk, ()))
          (μ := fun hk => sz32.toNat - hk.toNat) (Inv := fun hk ml => hk.toNat ≤ sz32.toNat ∧
            ml = m1) (fun LH hLH => by c0_hsteps!; exact hLH 0#32 m1 ⟨Nat.zero_le _, rfl⟩) ?_
        rintro LH hkL ml ⟨hhk_le, hml_eq⟩ ihH; c0_hsplit
        · have hhk_lt : hkL.toNat < sz32.toNat := hsz_toNat ▸ hc
          have hhk1 : (hkL + 1#32).toNat = hkL.toNat + 1 := by bv_omega
          have hidx_h_ar : (cr.setWidth 64 + (3 : BitVec 64) + hkL.setWidth 64).toNat <
              s1.core.arena.length := by
            rw [show (cr.setWidth 64 + (3 : BitVec 64) + hkL.setWidth 64).toNat =
              cr.toNat + 3 + hkL.toNat by bv_omega]; dsimp only [s1]; omega
          have hm_ml : (FullMem c s1 ⋆ R) ml := hml_eq ▸ hm1
          c0_hsplit; · c0_hsteps!; exact hJH (true, hkL) ml hml_eq
          · c0_hsteps!; exact ihH (hkL + 1#32) ml (by rw [hhk1]; omega) ⟨by omega, hml_eq⟩
        · c0_hsteps!; exact hJH (false, hkL) ml hml_eq
    · c0_hsteps_nogrp
      refine wp_join_group (ts := []) (fun () mRet => ∃ sR : FullState,
          M6ElsFrame c F0 F_cur s sR ∧ (FullMem c sR ⋆ R) mRet)
        (fun _ () mRet ⟨sR, hfrR, hmR⟩ => by
          c0_hsteps!; exact m6_els_ar_ret (ok := true) hfrR (by simp) hmR hQ) ?_
      intro JW hJW
      refine m6_els_ar_push_watched hWatch rfl rfl (by
          dsimp only [Arg.val]
          first | exact congrArg (· &&& 0x7FFFFFFF#32) hsz32_mod
                | (rw [m6_list_getElem_congr hcr2_eq _ hcr2_bd]; rfl) | rfl)
        rfl rfl hfr1 hsz3 hsz_lt_dim hcr_lt_dim hcr_ne hcr_ref hm1 fun ok s' m' hfr' hm' => ?_
      c0_hsplit; · c0_hsteps!; exact hJW () m' ⟨s', hfr', hm'⟩
      · c0_hsteps!; exact hJW () _ ⟨_, hfr'.set_oom, by assumption⟩
  · intro J1 hJ1; c0_hsteps_nogrp
    refine wp_while_state (ts := [i32]) (proj := fun k : BitVec 32 => (k, ()))
      (μ := fun k => sz32.toNat - k.toNat)
      (Inv := fun k ml => k.toNat ≤ sz32.toNat ∧ ∃ reprL : List (BitVec 32),
        reprL.length = 2 * c.max_vars ∧ FullCongReprInv F_cur (2 * s.core.cur_vars) reprL ∧
        (FullMem c { s with core := { s.core with repr := reprL } } ⋆ R) ml)
      (fun L1 hL1 => by
        c0_hsteps!; exact hL1 0#32 m ⟨Nat.zero_le _, s.core.repr, hrp_len, hrepr_inv, hm⟩) ?_
    rintro L1 kL ml ⟨hk_le, reprL, hrpL_len, hreprL, hml⟩ ih1; c0_hsplit
    · have hk_lt : kL.toNat < sz32.toNat := hsz_toNat ▸ hc
      have hk1 : (kL + 1#32).toNat = kL.toNat + 1 := by bv_omega
      have hidx_k_c0 : (cr.setWidth 64 + (3 : BitVec 64) + kL.setWidth 64).toNat =
          cr.toNat + 3 + kL.toNat := by bv_omega
      have hidx_k_ar : (cr.setWidth 64 + (3 : BitVec 64) + kL.setWidth 64).toNat <
          s.core.arena.length := by rw [hidx_k_c0]; omega
      have hl_lt := hlits_lt_k kL.toNat hk_lt; c0_hsteps_nogrp; dsimp only [Prod.fst]
      c0_hsteps_nogrp
      refine wp_join_group (ts := []) (fun () ml' => ∃ reprN : List (BitVec 32),
          reprN.length = 2 * c.max_vars ∧ FullCongReprInv F_cur (2 * s.core.cur_vars) reprN ∧
          (FullMem c { s with core := { s.core with repr := reprN } } ⋆ R) ml')
        (fun _ () ml' ⟨reprN, hrpN_l, hreprN, hml'⟩ => by
          c0_hsteps!; exact ih1 (kL + 1#32) ml' (by omega) ⟨by omega, reprN, hrpN_l, hreprN, hml'⟩)
        ?_
      intro J2 hJ2; c0_hsplit
      · c0_hsteps_nogrp
        refine m6_call_cong_find hFind hreprL (by
            rw [m6_list_getElem_congr hidx_k_c0 _ (by omega)]; exact hl_lt) hml
          fun _ reprN mlN hrpN_l hreprN _ _ _ hmlN => ?_
        c0_hsplit; · c0_hsteps!; exact hJ1 (true, kL) mlN ⟨reprN, hrpN_l.trans hrpL_len, hreprN,
                       hmlN⟩
        · c0_hsteps!; exact hJ2 () mlN ⟨reprN, hrpN_l.trans hrpL_len, hreprN, hmlN⟩
      · exfalso
        have hidx_l' : (cr.toNat + (3 : BitVec 64).toNat + kL.toNat) % 2 ^ 64 =
            cr.toNat + 3 + kL.toNat := by
          change (cr.toNat + 3 + kL.toNat) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
        simp only [bv_c0, hidx_l',
          Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64), hnlits_m] at hc; omega
    · c0_hsteps!; exact hJ1 (false, kL) ml ⟨reprL, hrpL_len, hreprL, hml⟩

end LeanQbe.T.Examples.Kissat.Proof.Sweep

end
