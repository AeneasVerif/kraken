module

public import LeanQbe.T.Examples.Kissat.Src.PropSearch
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Examples.Kissat.Proof.PropSearch.BcpWatchHelpers
import LeanQbe.T.Examples.Kissat.Proof.PropSearch.BcpFlushHelpers
import LeanQbe.T.Examples.Kissat.Proof.PropSearch.BcpPropHelpers
import LeanQbe.T.Examples.Kissat.Proof.PropSearch.WpInnerHelpers
import LeanQbe.T.Examples.Kissat.Proof.PropSearch.WpPost
import LeanQbe.T.Examples.Kissat.Proof.PropSearch.WpOvfLoop
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics

namespace LeanQbe.T.Examples.Kissat.Proof.PropSearch

open LeanQbe.T
open LeanQbe.T.C0HeadStep
open Std.Sat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.PropSearch
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
open scoped FullArenaTactics BcpPropTactics

local macro "s13_hsteps_nogrp" : tactic =>
  `(tactic| ((try dsimp only [opI64, opCmp64, opCmp32, opI32]); c0_hsteps_nogrp))

private structure S13OutSt where
  prop_v : BitVec 64
  tend_v : BitVec 64
  fuel_v : BitVec 64
  unass_v : BitVec 64
  unfl_v : BitVec 64
  ticks_v : BitVec 64

private def s13OutProj (st : S13OutSt) : Tup Val [i64, i64, i64, i64, i64, i64] :=
  (st.prop_v, st.tend_v, st.fuel_v, st.unass_v, st.unfl_v, st.ticks_v, ())

private theorem nat_xor1_eq (n : Nat) :
    n ^^^ 1 = if n % 2 = 0 then n + 1 else n - 1 := by
  have hmod : n % 2 = 0 ∨ n % 2 = 1 := Nat.mod_two_eq_zero_or_one n
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor]
  rcases hmod with h0 | h1m
  · simp only [h0, ↓reduceIte]
    cases i with
    | zero =>
      have h1 : (n + 1) % 2 = 1 := by omega
      simp [Nat.testBit_zero, h0, h1]
    | succ j =>
      have hd : (n + 1) / 2 = n / 2 := by omega
      simp [Nat.testBit_succ, hd]
  · simp only [h1m, show ¬(1 = 0) by decide, ↓reduceIte]
    cases i with
    | zero =>
      have h1 : (n - 1) % 2 = 0 := by omega
      simp [Nat.testBit_zero, h1m, h1]
    | succ j =>
      have hd : (n - 1) / 2 = n / 2 := by omega
      simp [Nat.testBit_succ, hd]

private theorem bv32_xor1_props {lit : BitVec 32} {cv : Nat}
    (hlt : lit.toNat < 2 * cv) :
    (lit ^^^ 1#32).toNat < 2 * cv ∧
      (lit ^^^ 1#32).toNat / 2 = lit.toNat / 2 ∧
      (lit ^^^ 1#32).toNat ^^^ 1 = lit.toNat := by
  have hx : (lit ^^^ 1#32).toNat = lit.toNat ^^^ 1 := by
    rw [BitVec.toNat_xor]; rfl
  have h1 := nat_xor1_eq lit.toNat
  have h2 := nat_xor1_eq (lit.toNat ^^^ 1)
  rw [hx]
  by_cases hm : lit.toNat % 2 = 0
  · simp only [hm, ↓reduceIte] at h1
    have hm2 : (lit.toNat ^^^ 1) % 2 ≠ 0 := by omega
    simp only [hm2, ↓reduceIte] at h2
    omega
  · simp only [hm, ↓reduceIte] at h1
    have hm2 : (lit.toNat ^^^ 1) % 2 = 0 := by omega
    simp only [hm2, ↓reduceIte] at h2
    omega

private theorem bv64_toNat_pos_of_ne_zero {x : BitVec 64} (h : x ≠ 0#64) : 0 < x.toNat := by
  cases Nat.eq_zero_or_pos x.toNat with
  | inl h0 => exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) h
  | inr hp => exact hp

private theorem list_getElem_eq {α : Type} {l : List α} {i j : Nat}
    {hi : i < l.length} {hj : j < l.length} (h : i = j) : l[i]'hi = l[j]'hj := by
  subst h; rfl

private theorem s13HQ_of_propIgnore {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext : List (BitVec 64)} {s : FullState} {ignore_ref : BitVec 64}
    {R : Mem 64 → Prop} {Q : Post [i64]}
    (hQ : ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (vals' : List (BitVec 8))
      (flags' lvl' rsns' trl' tp' : List (BitVec 32)) (te' prop' : Nat)
      (unass' unfl' : BitVec 64) (wvec' arena' wstk' : List (BitVec 32)) (wlen' : Nat)
      (wu' fuel' ctype' cref' c0' c1' oom' : BitVec 64) (sc' : FullScratch) (m' : Mem 64),
      let s' : FullState := {
        core := { s.core with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns',
          trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
          unassigned := unass', unflushed := unfl',
          wvec := wvec', arena := arena', wstk := wstk',
          wlen := wlen', wusable := wu', fuel := fuel',
          confl_type := ctype', confl_ref := cref',
          confl_lit0 := c0', confl_lit1 := c1', oom := oom' },
        scratch := sc' }
      M6HdrExtOk ext' →
      (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      s'.LengthsOk c →
      FullWitnessInv c F0 F_cur s'.core →
      FullTrailExt s.core s'.core →
      FullTrailRsnsPres s.core s'.core →
      FullArenaPermEq s.core s'.core →
      FullProbeScratchPres { s with scratch := { s.scratch with
        search_ticks := sc'.search_ticks, phases := sc'.phases,
        wsort := sc'.wsort, delayed := sc'.delayed } } s' →
      sc'.red_refs = s.scratch.red_refs →
      sc'.delayed_len = s.scratch.delayed_len →
      (s.core.probing = 0#64 → sc' = { s.scratch with
        search_ticks := sc'.search_ticks, phases := sc'.phases,
        wsort := sc'.wsort, delayed := sc'.delayed }) →
      (c.delayed_cap = 0 → sc'.delayed = s.scratch.delayed) →
      fuel'.toNat ≤ s.core.fuel.toNat →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → prop' = te' ∧ ctype' = s.core.confl_type ∧
        (s.core.oom = 0#64 → oom' = 0#64) ∧
        (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧
        FullConflictOkW F_cur s' ∧ (ctype' = 2#64 → cref' ≠ ignore_ref)) →
      (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ ext' = ext ∧ s' = s) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    S13HQ false c F0 F_cur ext s ignore_ref R Q := by
  intro r ext' vals' flags' lvl' rsns' trl' tp' te' prop' unas' unfl' wvec' arena' wstk'
    wlen' wu' fuel' ctype' cref' c0' c1' oom' sc' m' _s' hext' hw2b' hlen' hwinv' htr' hrsns'
    hperm' hprob' hred' hdlen' hsc' hd0' hfl_le hr_cases _hbcf hr0 hr1 hr2 hnoop hm'
  exact hQ r ext' vals' flags' lvl' rsns' trl' tp' te' prop' unas' unfl' wvec' arena' wstk'
    wlen' wu' fuel' ctype' cref' c0' c1' oom' sc' m' hext' hw2b' hlen' hwinv' htr' hrsns'
    hperm' hprob' hred' hdlen' hsc' hd0' hfl_le hr_cases
    (fun hr => let ⟨h1, h2, h3, h4⟩ := hr0 hr; ⟨h1, h2 rfl, h3, h4⟩)
    (hr1 rfl) hr2 hnoop hm'

private theorem s13HQ_of_propBeyond {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {Q : Post [i64]}
    (hQ : ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (vals' : List (BitVec 8))
      (flags' lvl' rsns' trl' tp' : List (BitVec 32)) (te' prop' : Nat)
      (unass' unfl' : BitVec 64) (wvec' arena' wstk' : List (BitVec 32)) (wlen' : Nat)
      (wu' fuel' oom' : BitVec 64) (sc' : FullScratch) (m' : Mem 64),
      let s' : FullState := {
        core := { s.core with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns',
          trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
          unassigned := unass', unflushed := unfl',
          wvec := wvec', arena := arena', wstk := wstk',
          wlen := wlen', wusable := wu', fuel := fuel', oom := oom' },
        scratch := sc' }
      M6HdrExtOk ext' →
      (M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext') →
      s'.LengthsOk c →
      FullWitnessInv c F0 F_cur s'.core →
      FullTrailExt s.core s'.core →
      FullTrailRsnsPres s.core s'.core →
      FullArenaPermEq s.core s'.core →
      FullProbeScratchPres { s with scratch := { s.scratch with
        search_ticks := sc'.search_ticks, phases := sc'.phases,
        wsort := sc'.wsort, delayed := sc'.delayed } } s' →
      sc'.red_refs = s.scratch.red_refs →
      sc'.delayed_len = s.scratch.delayed_len →
      (s.core.probing = 0#64 → sc' = { s.scratch with
        search_ticks := sc'.search_ticks, phases := sc'.phases,
        wsort := sc'.wsort, delayed := sc'.delayed }) →
      (c.delayed_cap = 0 → sc'.delayed = s.scratch.delayed) →
      fuel'.toNat ≤ s.core.fuel.toNat →
      (r = 0#64 ∨ r = 2#64) →
      (r = 0#64 → prop' = te' ∧ (s.core.oom = 0#64 → oom' = 0#64) ∧
        (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
      (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ ext' = ext ∧ s' = s) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    S13HQ true c F0 F_cur ext s 0xFFFFFFFF#64 R Q := by
  intro r ext' vals' flags' lvl' rsns' trl' tp' te' prop' unas' unfl' wvec' arena' wstk'
    wlen' wu' fuel' ctype' cref' c0' c1' oom' sc' m' _s' hext' hw2b' hlen' hwinv' htr' hrsns'
    hperm' hprob' hred' hdlen' hsc' hd0' hfl_le hr_cases hbcf hr0 _hr1 hr2 hnoop hm'
  rcases hbcf rfl with ⟨rfl, rfl, rfl, rfl⟩
  exact hQ r ext' vals' flags' lvl' rsns' trl' tp' te' prop' unas' unfl' wvec' arena' wstk'
    wlen' wu' fuel' oom' sc' m' hext' hw2b' hlen' hwinv' htr' hrsns' hperm' hprob' hred'
    hdlen' hsc' hd0' hfl_le hr_cases
    (fun hr => let ⟨h1, _, h3, h4⟩ := hr0 hr; ⟨h1, h3, h4⟩)
    hr2 hnoop hm'

private theorem s13_ret_early_0 {isBeyond : Bool} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {ext : List (BitVec 64)} {s : FullState}
    {ign : BitVec 64} {R : Mem 64 → Prop} {Q : Post [i64]} {m : Mem 64}
    (hQ : S13HQ isBeyond c F0 F_cur ext s ign R Q)
    (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c) (hwinv : FullWitnessInv c F0 F_cur s.core)
    (hpr_eq : s.core.propagated = s.core.trail_end) (hm : (FullM6HdrMem c ext s ⋆ R) m) :
    Q (0#64, ()) m := by
  refine s13_exit_hQ hQ hext (fun h => ⟨h, M6ExtW2bPres.refl _⟩) rfl
    (s13_probePres_of_S13Scr (s := s) (st := s) rfl) rfl rfl (fun _ => rfl)
    hlen hwinv (fullTrailExt_refl _) (fullTrailRsnsPres_refl _) (fullArenaPermEq_refl _)
    (fun _ => rfl) (Nat.le_refl _) ?_ (fun _ => ⟨rfl, rfl, rfl, rfl⟩)
    (fun _ => ⟨hpr_eq, fun _ => rfl, id, fun h => absurd hpr_eq (Nat.ne_of_lt h)⟩)
    (fun _ h => absurd h (by decide)) (fun h => absurd h (by decide))
    (fun _ => ⟨rfl, rfl, rfl⟩) hm
  cases isBeyond <;> simp

private theorem s13_ret_early_oom {isBeyond : Bool} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {ext : List (BitVec 64)} {s : FullState}
    {ign : BitVec 64} {R : Mem 64 → Prop} {Q : Post [i64]} {m : Mem 64}
    (hQ : S13HQ isBeyond c F0 F_cur ext s ign R Q)
    (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c) (hwinv : FullWitnessInv c F0 F_cur s.core)
    (hpr_lt : s.core.propagated < s.core.trail_end) (hoom : s.core.oom ≠ 0#64)
    (hm : (FullM6HdrMem c ext s ⋆ R) m) :
    Q (2#64, ()) m := by
  refine s13_exit_hQ hQ hext (fun h => ⟨h, M6ExtW2bPres.refl _⟩) rfl
    (s13_probePres_of_S13Scr (s := s) (st := s) rfl) rfl rfl (fun _ => rfl)
    hlen hwinv (fullTrailExt_refl _) (fullTrailRsnsPres_refl _) (fullArenaPermEq_refl _)
    (fun _ => rfl) (Nat.le_refl _) ?_ (fun _ => ⟨rfl, rfl, rfl, rfl⟩)
    (fun h => absurd h (by decide)) (fun _ h => absurd h (by decide))
    (fun _ => Or.inl hoom) (fun h => absurd h (Nat.ne_of_lt hpr_lt)) hm
  cases isBeyond <;> simp

private theorem s13_outer_init {isBeyond : Bool} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c) (hwinv : FullWitnessInv c F0 F_cur s.core)
    (hdense : s.core.dense_mode = 0#64) (hoom0 : s.core.oom = 0#64)
    (hm : (FullM6HdrMem c ext s ⋆ R) m) :
    S13OuterInv isBeyond c F0 F_cur ext s R s.core.fuel.toNat
      (BitVec.ofNat 64 s.core.propagated) (BitVec.ofNat 64 s.core.trail_end)
      s.core.fuel s.core.unassigned s.core.unflushed 0#64 m := by
  have hmax := c.hmaxv
  have hcv := hlen.core_ok.cur_vars_le
  have hte := hlen.core_ok.trail_end_le
  have hpr := hlen.core_ok.propagated_le
  have hpr64 : (BitVec.ofNat 64 s.core.propagated).toNat = s.core.propagated :=
    bv64_ofNat_toNat_lt (by unfold dimacsBound at hmax; omega)
  have hte64 : (BitVec.ofNat 64 s.core.trail_end).toNat = s.core.trail_end :=
    bv64_ofNat_toNat_lt (by unfold dimacsBound at hmax; omega)
  refine s13OuterInv_mk ⟨ext, s, s.core.trail_end, rfl, hext,
    fun h => ⟨h, M6ExtW2bPres.refl _⟩, hlen, hwinv,
    fullTrailExt_refl _, fullTrailRsnsPres_refl _, fullArenaPermEq_refl _, rfl,
    hpr64.symm, hte64.symm, rfl, rfl, rfl, hoom0, fun _ => rfl,
    fun _ => ⟨rfl, rfl, rfl, rfl⟩, hdense, rfl, rfl, rfl, rfl, Nat.le_refl _,
    fun h => absurd h (by omega), by omega, by omega, Nat.le_refl _, hpr,
    rfl, fun _ => rfl, ?_⟩
  have hself : fastPropMem
      { s with core := { s.core with trail_end := s.core.trail_end } }
      { s with core := { s.core with propagated := s.core.propagated, fuel := s.core.fuel } } =
      s := fastPropMem_self s
  simpa only [hself] using hm

private theorem s13_fastProp_flush_eq {s sem : FullState} {te_mem : Nat}
    {prop_v tend_v fuel_v unass_v unfl_v : BitVec 64}
    (hag : AgreesExcept fidCoreMask s.core sem.core) (hsc : S13Scr s sem) :
    let fp := fastPropMem
      { s with core := { s.core with trail_end := te_mem } }
      { sem with core := { sem.core with propagated := s.core.propagated, fuel := s.core.fuel } }
    { fp with core := { fp.core with
        fuel := fuel_v, propagated := prop_v.toNat, trail_end := tend_v.toNat,
        unassigned := unass_v, unflushed := unfl_v } } =
    { sem with core := { sem.core with
        unassigned := unass_v, unflushed := unfl_v,
        trail_end := tend_v.toNat, propagated := prop_v.toNat, fuel := fuel_v } } := by
  intro fp
  have hc := fid_core_eq_of_agrees s.core sem.core hag
  have hdl : sem.scratch.delayed_len = s.scratch.delayed_len := by rw [hsc]
  cases s with
  | mk sc0 scr0 =>
    cases sem with
    | mk sc1 scr1 =>
      dsimp only [fp, fastPropMem]
      congr 1
      · dsimp only at hc
        rw [hc]
      · dsimp only [S13Scr] at hsc hdl
        rw [hdl, ← hsc]

private theorem s13_outer_sz0_next {isBeyond : Bool} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {ext0 ext1 : List (BitVec 64)} {s sem : FullState}
    {te_mem : Nat} {prop_v tend_v fuel_v unass_v unfl_v ticks_v : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hext1 : M6HdrExtOk ext1)
    (hw2b1 : M6HdrExtInitOk ext0 → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext0 ext1)
    (hlen : sem.LengthsOk c) (hwinv : FullWitnessInv c F0 F_cur sem.core)
    (htr : FullTrailExt s.core sem.core) (hrsns : FullTrailRsnsPres s.core sem.core)
    (hperm : FullArenaPermEq s.core sem.core) (hag : AgreesExcept fidCoreMask s.core sem.core)
    (hprop : sem.core.propagated = prop_v.toNat) (hte : sem.core.trail_end = tend_v.toNat)
    (hfl : sem.core.fuel = fuel_v) (hun : sem.core.unassigned = unass_v)
    (huf : sem.core.unflushed = unfl_v) (hoom : sem.core.oom = 0#64)
    (hct : isBeyond = false → sem.core.confl_type = s.core.confl_type)
    (hcf : isBeyond = true → S13ConflEq s.core sem.core)
    (hdense : sem.core.dense_mode = 0#64) (hcv : sem.core.cur_vars = s.core.cur_vars)
    (hcl : sem.core.cur_level = s.core.cur_level) (hprob : sem.core.probing = s.core.probing)
    (halen : sem.core.arena_len = s.core.arena_len)
    (hfl_le : sem.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hpr_ge : s.core.propagated ≤ prop_v.toNat)
    (hpt_lt : prop_v.toNat < tend_v.toNat) (hfl_nz : fuel_v ≠ 0#64)
    (hte_le : te_mem ≤ sem.core.trail_end) (hpr_te : s.core.propagated ≤ te_mem)
    (hsc : S13Scr s sem) (hd0 : c.delayed_cap = 0 → sem.scratch.delayed = s.scratch.delayed)
    (hm : (FullM6HdrMem c ext1 (fastPropMem
      { s with core := { s.core with trail_end := te_mem } }
      { sem with core := { sem.core with
          propagated := s.core.propagated, fuel := s.core.fuel } }) ⋆ R) m) :
    (fuel_v - 1#64).toNat < fuel_v.toNat ∧
      S13OuterInv isBeyond c F0 F_cur ext0 s R (fuel_v - 1#64).toNat
        (prop_v + 1#64) tend_v (fuel_v - 1#64) unass_v unfl_v (ticks_v + 1#64) m := by
  have hmax := c.hmaxv
  have hcv_le := hlen.core_ok.cur_vars_le
  have hte_le_cv := hlen.core_ok.trail_end_le
  have hp1 : (prop_v + 1#64).toNat = prop_v.toNat + 1 :=
    bv64_add_toNat (by simp only [BitVec.toNat_ofNat]; unfold dimacsBound at hmax; omega)
  have hf1 : (fuel_v - 1#64).toNat = fuel_v.toNat - 1 := bv64_sub1_toNat hfl_nz
  have hfnz_nat : 0 < fuel_v.toNat := bv64_toNat_pos_of_ne_zero hfl_nz
  refine ⟨by omega, ?_⟩
  let sem' : FullState :=
    { sem with core := { sem.core with
        propagated := prop_v.toNat + 1, fuel := fuel_v - 1#64 } }
  have hlen' : sem'.LengthsOk c :=
    ⟨{ hlen.core_ok with propagated_le := by dsimp [sem']; omega }, hlen.scratch_ok⟩
  have hwinv' : FullWitnessInv c F0 F_cur sem'.core :=
    fullWitnessInv_with_fuel_prop hwinv (fuel_v - 1#64) (prop_v.toNat + 1)
  have hag' : AgreesExcept fidCoreMask s.core sem'.core := hag
  refine s13OuterInv_mk ⟨ext1, sem', te_mem, rfl, hext1, hw2b1, hlen', hwinv',
    htr, hrsns, hperm, hag', hp1.symm, hte, rfl, hun, huf, hoom, hct, hcf,
    hdense, hcv, hcl, hprob, halen,
    by dsimp only [sem']; rw [hf1]; rw [hfl] at hfl_le; omega,
    fun _ => by dsimp only [sem']; rw [hf1]; rw [hfl] at hfl_le; omega,
    by omega, by omega, hte_le, hpr_te, hsc, hd0, hm⟩

private theorem s13_outer_sz_nz_pi0 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s sem s_base : FullState} {prop_v off0 sz0 end0 : BitVec 64} {lit not_lit nl_lvl : BitVec 32}
    (hs_base : s_base = { sem with core := { sem.core with
      propagated := s.core.propagated, fuel := s.core.fuel } })
    (hlen : sem.LengthsOk c) (hwinv : FullWitnessInv c F0 F_cur sem.core)
    (hdense : sem.core.dense_mode = 0#64)
    (hpr_ge : s.core.propagated ≤ prop_v.toNat) (hp_lt : prop_v.toNat < sem.core.trail_end)
    (hlit : lit = sem.core.trl[prop_v.toNat]?.getD 0#32)
    (hnot : not_lit = lit ^^^ 1#32)
    (hoff : off0 = BitVec.setWidth 64 (sem.core.wvec[2 * not_lit.toNat]?.getD 0#32))
    (hsz : sz0 = BitVec.setWidth 64 (sem.core.wvec[2 * not_lit.toNat + 1]?.getD 0#32))
    (hsz_nz : sz0 ≠ 0#64) (hend : end0 = off0 + sz0)
    (hnl_lvl : nl_lvl = sem.core.lvl[not_lit.toNat / 2]?.getD 0#32) :
    not_lit.toNat < 2 * sem.core.cur_vars ∧
      PropLitInv c F0 F_cur s_base s_base not_lit.toNat
        off0.toNat off0.toNat off0.toNat end0.toNat ∧
      (∀ k, FullTrailExt s_base.core k → k.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl) := by
  have hlit_lt : lit.toNat < 2 * sem.core.cur_vars := by
    rw [hlit]; exact hwinv.trail_lits_lt prop_v.toNat hp_lt
  have ⟨hnot_lt, hnot_div, hnot_xor⟩ := bv32_xor1_props hlit_lt
  rw [← hnot] at hnot_lt hnot_div hnot_xor
  have hlen_b : s_base.LengthsOk c := by
    subst hs_base
    exact ⟨{ hlen.core_ok with propagated_le := by dsimp; omega }, hlen.scratch_ok⟩
  have hwinv_b : FullWitnessInv c F0 F_cur s_base.core := by
    subst hs_base
    exact fullWitnessInv_with_fuel_prop hwinv s.core.fuel s.core.propagated
  have hnw_b : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c s_base.core) :=
    fullWitnessInv_to_nw hlen_b.core_ok.cur_vars_le hwinv_b
  have hwat_b : WatchesInv F_cur s_base.core := by
    have hm := hwinv_b.watches
    have hd : s_base.core.dense_mode = 0#64 := by subst hs_base; exact hdense
    simpa [ModeWatchesInv, hd] using hm
  have hoff_lt32 : (sem.core.wvec[2 * not_lit.toNat]?.getD 0#32).toNat < 2 ^ 32 :=
    BitVec.isLt _
  have hsz_lt32 : (sem.core.wvec[2 * not_lit.toNat + 1]?.getD 0#32).toNat < 2 ^ 32 :=
    BitVec.isLt _
  have hoff_nat : off0.toNat = fullWatchOffCore s_base.core not_lit.toNat := by
    subst hs_base
    rw [hoff, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
    rfl
  have hsz_nat : sz0.toNat = fullWatchSizeCore s_base.core not_lit.toNat := by
    subst hs_base
    rw [hsz, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
    rfl
  have hsz_pos : 0 < fullWatchSizeCore s_base.core not_lit.toNat := by
    rw [← hsz_nat]; exact bv64_toNat_pos_of_ne_zero hsz_nz
  have hend_nat : end0.toNat = off0.toNat + sz0.toNat := by
    rw [hend]
    have h1 : off0.toNat < 2 ^ 32 := by
      rw [hoff, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact hoff_lt32
    have h2 : sz0.toNat < 2 ^ 32 := by
      rw [hsz, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact hsz_lt32
    exact bv64_add_toNat (by omega)
  have hsw_b : SplitWatchesInv F_cur s_base.core not_lit.toNat
      off0.toNat off0.toNat off0.toNat end0.toNat := by
    have h0 := SplitWatchesInv.of_init hwat_b (by subst hs_base; exact hnot_lt) hsz_pos
    simpa only [← hoff_nat, ← hsz_nat, ← hend_nat] using h0
  have hnot_f : s_base.core.vals[not_lit.toNat]?.getD 0#8 = 255#8 := by
    have hlt_b : not_lit.toNat < 2 * s_base.core.cur_vars := by subst hs_base; exact hnot_lt
    exact (hwinv_b.vals_false_iff not_lit.toNat hlt_b).mpr
      ⟨prop_v.toNat, by subst hs_base; exact hp_lt, by subst hs_base; rw [← hlit, hnot_xor]⟩
  have hpi : PropLitInv c F0 F_cur s_base s_base not_lit.toNat
      off0.toNat off0.toNat off0.toNat end0.toNat :=
    ⟨hlen_b, hnw_b, hsw_b, rfl, fullTrailExt_refl _, fullTrailRsnsPres_refl _,
      fullArenaPermEq_refl _, rfl, hnot_f⟩
  have hnl_sb : ∀ k, FullTrailExt s_base.core k →
      k.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl :=
    s13_nl_lvl_of_trail_ext
      ⟨prop_v.toNat, by subst hs_base; exact hp_lt,
        by subst hs_base; rw [← hlit, hnot_div]⟩
      (by subst hs_base; exact hnl_lvl.symm)
  exact ⟨hnot_lt, hpi, hnl_sb⟩

private theorem s13_outer_body_exit {Γ : Env} {isBeyond : Bool} {c : FullCfg}
    {F0 : CNF Nat} {F_cur : List (List Nat)} {ext0 ext1 : List (BitVec 64)}
    {s sem : FullState} {te_mem : Nat}
    {ign_v prop_v tend_v fuel_v unass_v unfl_v ticks_v r : BitVec 64}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {m : Mem 64}
    (hAddTicks : Γ.Has "m6_hdr_add_ticks" Tiers.Spec.m6HdrAddTicksSpec)
    (hQ : S13HQ isBeyond c F0 F_cur ext0 s ign_v R Q)
    (hcfg : FullM6HdrCfgOk c) (hext1 : M6HdrExtOk ext1)
    (hw2b1 : M6HdrExtInitOk ext0 → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext0 ext1)
    (hlen : sem.LengthsOk c) (hwinv : FullWitnessInv c F0 F_cur sem.core)
    (htr : FullTrailExt s.core sem.core) (hrsns : FullTrailRsnsPres s.core sem.core)
    (hperm : FullArenaPermEq s.core sem.core) (hag : AgreesExcept fidCoreMask s.core sem.core)
    (hsc : S13Scr s sem) (hd0 : c.delayed_cap = 0 → sem.scratch.delayed = s.scratch.delayed)
    (hprop : sem.core.propagated = prop_v.toNat) (hte : sem.core.trail_end = tend_v.toNat)
    (hfl : sem.core.fuel = fuel_v) (hun : sem.core.unassigned = unass_v)
    (huf : sem.core.unflushed = unfl_v) (hfl_le : sem.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hpr_lt : s.core.propagated < s.core.trail_end)
    (hr_cases : if isBeyond = true then r = 0#64 ∨ r = 2#64
      else r = 0#64 ∨ r = 1#64 ∨ r = 2#64)
    (hbcf : isBeyond = true → S13ConflEq s.core sem.core)
    (hr0 : r = 0#64 → prop_v.toNat = tend_v.toNat ∧
      (isBeyond = false → sem.core.confl_type = s.core.confl_type) ∧
      (s.core.oom = 0#64 → sem.core.oom = 0#64) ∧
      (s.core.propagated < s.core.trail_end → sem.core.fuel.toNat < s.core.fuel.toNat))
    (hr1 : isBeyond = false → r ≠ 1#64)
    (hr2 : r = 2#64 → sem.core.oom ≠ 0#64 ∨ sem.core.fuel = 0#64)
    (hm : (FullMem c { (fastPropMem
        { s with core := { s.core with trail_end := te_mem } }
        { sem with core := { sem.core with
            propagated := s.core.propagated, fuel := s.core.fuel } }) with
      core := { (fastPropMem
          { s with core := { s.core with trail_end := te_mem } }
          { sem with core := { sem.core with
              propagated := s.core.propagated, fuel := s.core.fuel } }).core with
        fuel := fuel_v, propagated := prop_v.toNat, trail_end := tend_v.toNat,
        unassigned := unass_v, unflushed := unfl_v } } ⋆
      (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) m) :
    wp Γ Q X (s13PostTicksExpr c.hdr ticks_v r) m := by
  rw [s13_fastProp_flush_eq hag hsc] at hm
  exact s13_outer_flush_ret hAddTicks hQ hcfg hext1 hw2b1 hlen hwinv htr hrsns hperm hag
    hsc hd0 hprop hte hfl hun huf hfl_le hpr_lt hr_cases hbcf hr0 hr1 hr2
    (fullM6HdrMem_unfocus hm)

private theorem s13_outer_loop_jump {Γ : Env} {Q : Post [i64]} {X : XPost}
    {isBeyond : Bool} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext0 ext1 : List (BitVec 64)} {s sem : FullState}
    {prop_v fuel_v fuel1 te_b un_b uf_b tk_b : BitVec 64} {R : Mem 64 → Prop}
    {J_out : Cont [i64, i64, i64, i64, i64, i64]}
    (hext1 : M6HdrExtOk ext1)
    (hw2b1 : M6HdrExtInitOk ext0 → M6HdrExtInitOk ext1 ∧ M6ExtW2bPres ext0 ext1)
    (hfl_cur : sem.core.fuel = fuel_v)
    (hih : ∀ st' m', st'.fuel_v.toNat < fuel_v.toNat →
      S13OuterInv isBeyond c F0 F_cur ext0 s R st'.fuel_v.toNat
        st'.prop_v st'.tend_v st'.fuel_v st'.unass_v st'.unfl_v st'.ticks_v m' →
      J_out (s13OutProj st') m')
    (sem_next : FullState) (te_mc : Nat) (mc0 : Mem 64)
    (hlen_n : sem_next.LengthsOk c) (hwinv_n : FullWitnessInv c F0 F_cur sem_next.core)
    (htr_n : FullTrailExt s.core sem_next.core)
    (hrsns_n : FullTrailRsnsPres s.core sem_next.core)
    (hperm_n : FullArenaPermEq s.core sem_next.core)
    (hag_n : AgreesExcept fidCoreMask s.core sem_next.core)
    (hpr_n : sem_next.core.propagated = (prop_v + 1#64).toNat)
    (hfl_n : sem_next.core.fuel = fuel1) (hte_n : sem_next.core.trail_end = te_b.toNat)
    (hun_n : sem_next.core.unassigned = un_b) (huf_n : sem_next.core.unflushed = uf_b)
    (hoom_n : sem_next.core.oom = 0#64)
    (hct_n : isBeyond = false → sem_next.core.confl_type = s.core.confl_type)
    (hcf_n : isBeyond = true → S13ConflEq s.core sem_next.core)
    (hdense_n : sem_next.core.dense_mode = 0#64)
    (hcv_n : sem_next.core.cur_vars = s.core.cur_vars)
    (hcl_n : sem_next.core.cur_level = s.core.cur_level)
    (hprob_n : sem_next.core.probing = s.core.probing)
    (halen_n : sem_next.core.arena_len = s.core.arena_len)
    (hfl_lt_sem : sem_next.core.fuel.toNat < sem.core.fuel.toNat)
    (hfl_lt_s : sem_next.core.fuel.toNat < s.core.fuel.toNat)
    (hfl_le_s : sem_next.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hpr_ge_s : s.core.propagated ≤ sem_next.core.propagated)
    (hte_mc_le : te_mc ≤ sem_next.core.trail_end) (hpr_te_mc : s.core.propagated ≤ te_mc)
    (hsc_n : S13Scr s sem_next)
    (hd0_n : c.delayed_cap = 0 → sem_next.scratch.delayed = s.scratch.delayed)
    (hmc0 : (FullM6HdrMem c ext1 (fastPropMem
      { s with core := { s.core with trail_end := te_mc } }
      { sem_next with core := { sem_next.core with
          propagated := s.core.propagated, fuel := s.core.fuel } }) ⋆ R) mc0) :
    wp Γ Q X (Expr.jump J_out
      (Arg.var (prop_v + 1#64), Arg.var te_b, Arg.var fuel1,
        Arg.var un_b, Arg.var uf_b, Arg.var tk_b, ())) mc0 := by
  have hpt_n : (prop_v + 1#64).toNat ≤ te_b.toNat := by
    have := hlen_n.core_ok.propagated_le; omega
  have hlt : fuel1.toNat < fuel_v.toNat := by rw [← hfl_n, ← hfl_cur]; exact hfl_lt_sem
  let st_next : S13OutSt := ⟨prop_v + 1#64, te_b, fuel1, un_b, uf_b, tk_b⟩
  exact (wp_jump _ _).mpr (hih st_next mc0 hlt (s13OuterInv_mk ⟨ext1, sem_next, te_mc,
    by rw [hfl_n], hext1, hw2b1, hlen_n, hwinv_n, htr_n, hrsns_n, hperm_n, hag_n,
    hpr_n, hte_n, hfl_n, hun_n, huf_n, hoom_n, hct_n, hcf_n, hdense_n, hcv_n, hcl_n,
    hprob_n, halen_n, hfl_le_s, fun _ => hfl_lt_s,
    by rw [← hpr_n]; exact hpr_ge_s, hpt_n, hte_mc_le,
    hpr_te_mc, hsc_n, hd0_n, hmc0⟩))

private theorem s13_outer_arith_facts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hlen : s.LengthsOk c) (hwinv : FullWitnessInv c F0 F_cur s.core) :
    ((BitVec.ofNat 64 c.delayed_cap * 3#64).toNat = 3 * c.delayed_cap) ∧
      ((BitVec.ofNat 64 s.core.cur_vars <<< 1#64).toNat = 2 * s.core.cur_vars) ∧
      s.core.cur_level < 2 ^ 32 ∧
      BitVec.setWidth 32 (BitVec.ofNat 64 s.core.cur_level) =
        BitVec.ofNat 32 s.core.cur_level := by
  have hdel := c.hdel
  have hmax := c.hmaxv
  have hcv := hlen.core_ok.cur_vars_le
  have hcl_le := hwinv.cur_level_le
  have hte_le := hlen.core_ok.trail_end_le
  have hcl_lt32 : s.core.cur_level < 2 ^ 32 := by unfold dimacsBound at hmax; omega
  refine ⟨?_, ?_, hcl_lt32, ?_⟩
  · have h1 : (BitVec.ofNat 64 c.delayed_cap).toNat = c.delayed_cap :=
      bv64_ofNat_toNat_lt (by unfold dimacsBound at hdel; omega)
    rw [BitVec.toNat_mul, h1]; simp; unfold dimacsBound at hdel; omega
  · have h1 : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars :=
      bv64_ofNat_toNat_lt (by unfold dimacsBound at hmax; omega)
    have hsh : BitVec.ofNat 64 s.core.cur_vars <<< 1#64 =
        BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat) := rfl
    rw [hsh, BitVec.toNat_shiftLeft, h1]; simp; unfold dimacsBound at hmax; omega
  · apply BitVec.eq_of_toNat_eq
    simp

public theorem full_propagate_ignore_hot_wp (Γ : Env)
    (hOvf : Γ.Has "full_prop_lit_ovf_hot" Spec.fullPropLitOvfHotSpec)
    (hFlush : Γ.Has "full_prop_flush_del_fid" Spec.fidPropFlushDelSpec)
    (hWm4 : Γ.Has "m6_wm4_get" Float64.Spec.m6Wm4GetSpec)
    (hAddTicks : Γ.Has "m6_hdr_add_ticks" Tiers.Spec.m6HdrAddTicksSpec) :
    ∀ a m Q X, Spec.propIgnoreM6Spec a m Q X →
      Func.wp Γ full_propagate_ignore_hot_body a m Q X := by
  rintro ⟨h, ign_v, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, ext0, s, R, rfl, hcfg, hext0, hlen,
    hwinv, hdense, hm, hQ_raw⟩
  have hQ := s13HQ_of_propIgnore hQ_raw
  have hmax := c.hmaxv
  have hcv_le := hlen.core_ok.cur_vars_le
  have hte_le := hlen.core_ok.trail_end_le
  have hpr_le := hlen.core_ok.propagated_le
  have hm_f := fullM6HdrMem_focus hm
  dsimp only [Func.wp, full_propagate_ignore_hot_body]
  s13_hsteps_nogrp
  · exact s13_ret_early_0 hQ hext0 hlen hwinv (by unfold dimacsBound at hmax; omega) hm
  · exact s13_ret_early_oom hQ hext0 hlen hwinv (by unfold dimacsBound at hmax; omega) hc hm
  · have hpr_lt : s.core.propagated < s.core.trail_end := by unfold dimacsBound at hmax; omega
    have hoom0 : s.core.oom = 0#64 := hc
    refine wp_call_of_spec _ _ (hWm4 _ _ _ _ ⟨c, ext0, s, R, rfl, hcfg, hext0, hlen, hm, ?_⟩)
    intro wm hm_w
    have hm_wf := fullM6HdrMem_focus hm_w
    s13_hsteps_nogrp
    have ⟨hdlim, htwo_cv, hcl32, hcur_lvl⟩ := s13_outer_arith_facts hlen hwinv
    let μOut : S13OutSt → Nat := fun st => st.fuel_v.toNat
    let InvOut : S13OutSt → Mem 64 → Prop := fun st m' =>
      S13OuterInv false c F0 F_cur ext0 s R st.fuel_v.toNat
        st.prop_v st.tend_v st.fuel_v st.unass_v st.unfl_v st.ticks_v m'
    refine wp_while_state s13OutProj μOut InvOut ?_ ?_
    · intro J hJ
      let st0 : S13OutSt := ⟨BitVec.ofNat 64 s.core.propagated,
        BitVec.ofNat 64 s.core.trail_end, s.core.fuel,
        s.core.unassigned, s.core.unflushed, 0#64⟩
      exact (wp_jump _ _).mpr (hJ st0 m (s13_outer_init hext0 hlen hwinv hdense hoom0 hm_w))
    · intro J st m' hInv hih
      rcases s13OuterInv_elim hInv with
        ⟨ext1, sem, te_mem, _hrem, hext1, hw2b1, hlen_o, hwinv_o, htr_o, hrsns_o,
          hperm_o, hag_o, hprop_o, hte_o, hfl_o, hun_o, huf_o, hoom_o, hct_o, _hcf_o,
          hdense_o, hcv_o, hcl_o, hprob_o, halen_o, hfl_le, hfl_dec, hpr_ge, hpt_le,
          hte_mem_le, hpr_te_mem, hsc_o, hd0_o, hm_o⟩
      dsimp only [Blocks.get, s13OutProj]
      have hm_of := fullM6HdrMem_focus hm_o
      s13_hsteps_nogrp
      · have hfl0 : st.fuel_v = 0#64 := hc
        dsimp only at hm
        exact s13_outer_body_exit (fuel_v := 0#64) hAddTicks hQ hcfg hext1 hw2b1 hlen_o
          hwinv_o htr_o hrsns_o hperm_o hag_o hsc_o hd0_o hprop_o hte_o (hfl_o.trans hfl0)
          hun_o huf_o hfl_le hpr_lt (Or.inr (Or.inr rfl)) (fun h => Bool.noConfusion h)
          (fun h => absurd h (by decide)) (fun _ h => absurd h (by decide))
          (fun _ => Or.inr (by rw [hfl_o, hfl0])) hm
      · have hpt_lt : st.prop_v.toNat < st.tend_v.toNat := by omega
        have hfl_nz : st.fuel_v ≠ 0#64 := hc
        let s_disk : FullState := { s with core := { s.core with trail_end := te_mem } }
        let s_base : FullState := { sem with core := { sem.core with
          propagated := s.core.propagated, fuel := s.core.fuel } }
        have hpr_lt_mv : st.prop_v.toNat < c.max_vars := by
          have := hlen_o.core_ok.trail_end_le
          have := hlen_o.core_ok.cur_vars_le; omega
        have hpr_lt_trl : st.prop_v.toNat < (fastPropMem s_disk s_base).core.trl.length := by
          change st.prop_v.toNat < sem.core.trl.length
          rw [hlen_o.core_ok.trl_len]; exact hpr_lt_mv
        s13_hsteps_nogrp
        let lit : BitVec 32 := (fastPropMem s_disk s_base).core.trl[st.prop_v.toNat]'hpr_lt_trl
        have hlit_eq : lit = sem.core.trl[st.prop_v.toNat]?.getD 0#32 := by
          change (fastPropMem s_disk s_base).core.trl[st.prop_v.toNat]'hpr_lt_trl =
            (fastPropMem s_disk s_base).core.trl[st.prop_v.toNat]?.getD 0#32
          rw [List.getElem?_eq_getElem hpr_lt_trl]; rfl
        have hlit_lt : lit.toNat < 2 * sem.core.cur_vars := by
          rw [hlit_eq]; exact hwinv_o.trail_lits_lt st.prop_v.toNat (by omega)
        let not_lit : BitVec 32 := lit ^^^ 1#32
        have ⟨hnot_lt, hnot_div, _⟩ := bv32_xor1_props hlit_lt
        have hnot_lt_n : not_lit.toNat < 2 * sem.core.cur_vars := hnot_lt
        have hnl64_idx : (BitVec.setWidth 64 not_lit <<< 1#64).toNat = 2 * not_lit.toNat := by
          have := hlen_o.core_ok.cur_vars_le
          exact bv64_shl1_u32 (by unfold dimacsBound at hmax; omega)
        have hnl_lt_wvec : (BitVec.setWidth 64 not_lit <<< 1#64).toNat <
            (fastPropMem s_disk s_base).core.wvec.length := by
          change (BitVec.setWidth 64 not_lit <<< 1#64).toNat < sem.core.wvec.length
          rw [hnl64_idx, hlen_o.core_ok.wvec_len]; have := hlen_o.core_ok.cur_vars_le; omega
        have hnl1_idx : ((BitVec.setWidth 64 not_lit <<< 1#64) + 1#64).toNat =
            2 * not_lit.toNat + 1 := by
          rw [bv64_add_toNat (by
            simp only [BitVec.toNat_ofNat]
            have := hlen_o.core_ok.cur_vars_le; unfold dimacsBound at hmax; omega), hnl64_idx]
          rfl
        have hnl1_lt_wvec : ((BitVec.setWidth 64 not_lit <<< 1#64) + 1#64).toNat <
            (fastPropMem s_disk s_base).core.wvec.length := by
          change ((BitVec.setWidth 64 not_lit <<< 1#64) + 1#64).toNat < sem.core.wvec.length
          rw [hnl1_idx, hlen_o.core_ok.wvec_len]; have := hlen_o.core_ok.cur_vars_le; omega
        s13_hsteps_nogrp
        · have ⟨hlt_fl, hInv'⟩ :=
            s13_outer_sz0_next (ticks_v := st.ticks_v) hext1 hw2b1 hlen_o hwinv_o htr_o
            hrsns_o hperm_o hag_o hprop_o hte_o hfl_o hun_o huf_o hoom_o hct_o
            (fun h => Bool.noConfusion h) hdense_o hcv_o hcl_o hprob_o halen_o hfl_le
            hpr_ge hpt_lt hfl_nz hte_mem_le hpr_te_mem hsc_o hd0_o hm_o
          exact hih ⟨st.prop_v + 1#64, st.tend_v, st.fuel_v - 1#64,
            st.unass_v, st.unfl_v, st.ticks_v + 1#64⟩ m' hlt_fl hInv'
        · let off32 : BitVec 32 :=
            (fastPropMem s_disk s_base).core.wvec[
              (BitVec.setWidth 64 not_lit <<< 1#64).toNat]'hnl_lt_wvec
          let sz32 : BitVec 32 :=
            (fastPropMem s_disk s_base).core.wvec[
              ((BitVec.setWidth 64 not_lit <<< 1#64) + 1#64).toNat]'hnl1_lt_wvec
          have hsz_nz : BitVec.setWidth 64 sz32 ≠ 0#64 := by
            intro h0; apply hc
            have hnx : not_lit.toNat =
                (sem.core.trl[st.prop_v.toNat]'hpr_lt_trl).toNat ^^^ 1 := by
              change (lit ^^^ 1#32).toNat = _
              rw [BitVec.toNat_xor]; rfl
            have hidx_eq : (2 * ((sem.core.trl[st.prop_v.toNat]'hpr_lt_trl).toNat ^^^ 1) +
                BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 =
                ((BitVec.setWidth 64 not_lit <<< 1#64) + 1#64).toNat := by
              rw [hnl1_idx, ← hnx]
              have := hlen_o.core_ok.cur_vars_le; unfold dimacsBound at hmax
              change (2 * not_lit.toNat + 1) % 2 ^ 64 = 2 * not_lit.toNat + 1; omega
            let idx1 := ((BitVec.setWidth 64 not_lit <<< 1#64) + 1#64).toNat
            have h0' : BitVec.setWidth 64 (sem.core.wvec[idx1]'hnl1_lt_wvec) = 0 := h0
            rw [← h0']; congr 1; exact list_getElem_eq hidx_eq
          have hvar_lt : (BitVec.setWidth 64 (not_lit >>> 1#32)).toNat < c.max_vars := by
            rw [m7_bv32_rshift1_toNat not_lit]
            have := hlen_o.core_ok.cur_vars_le; omega
          have hvar_lt_lvl : (BitVec.setWidth 64 (not_lit >>> 1#32)).toNat <
              (fastPropMem s_disk s_base).core.lvl.length := by
            change (BitVec.setWidth 64 (not_lit >>> 1#32)).toNat < sem.core.lvl.length
            rw [hlen_o.core_ok.lvl_len]; exact hvar_lt
          s13_hsteps_nogrp
          have hvar_eq := m7_bv32_rshift1_toNat not_lit
          have hoff_eq : BitVec.setWidth 64 off32 =
              BitVec.setWidth 64 (sem.core.wvec[2 * not_lit.toNat]?.getD 0#32) := by
            congr 1
            change (fastPropMem s_disk s_base).core.wvec[
              (BitVec.setWidth 64 not_lit <<< 1#64).toNat]'hnl_lt_wvec =
              (fastPropMem s_disk s_base).core.wvec[2 * not_lit.toNat]?.getD 0#32
            rw [← hnl64_idx, List.getElem?_eq_getElem hnl_lt_wvec]; rfl
          have hsz_eq : BitVec.setWidth 64 sz32 =
              BitVec.setWidth 64 (sem.core.wvec[2 * not_lit.toNat + 1]?.getD 0#32) := by
            congr 1
            change (fastPropMem s_disk s_base).core.wvec[
              ((BitVec.setWidth 64 not_lit <<< 1#64) + 1#64).toNat]'hnl1_lt_wvec =
              (fastPropMem s_disk s_base).core.wvec[2 * not_lit.toNat + 1]?.getD 0#32
            rw [← hnl1_idx, List.getElem?_eq_getElem hnl1_lt_wvec]; rfl
          let nl_lvl : BitVec 32 := (fastPropMem s_disk s_base).core.lvl[
            (BitVec.setWidth 64 (not_lit >>> 1#32)).toNat]'hvar_lt_lvl
          have hnl_eq : nl_lvl = sem.core.lvl[not_lit.toNat / 2]?.getD 0#32 := by
            change (fastPropMem s_disk s_base).core.lvl[
              (BitVec.setWidth 64 (not_lit >>> 1#32)).toNat]'hvar_lt_lvl =
              (fastPropMem s_disk s_base).core.lvl[not_lit.toNat / 2]?.getD 0#32
            rw [← hvar_eq, List.getElem?_eq_getElem hvar_lt_lvl]; rfl
          have ⟨hnot_lt', hpi_0, hnl_sb⟩ := s13_outer_sz_nz_pi0 (s_base := s_base)
            rfl hlen_o hwinv_o hdense_o hpr_ge (by omega) hlit_eq rfl
            (off0 := BitVec.setWidth 64 off32) hoff_eq
            (sz0 := BitVec.setWidth 64 sz32) hsz_eq hsz_nz rfl
            (nl_lvl := nl_lvl) hnl_eq
          have hfl_dec1 : (sem.core.fuel - 1#64).toNat < sem.core.fuel.toNat := by
            have hf1 := bv64_sub1_toNat hfl_nz
            have hpos := bv64_toNat_pos_of_ne_zero hfl_nz
            rw [hfl_o]; omega
          have hp1_prop : (st.prop_v + 1#64).toNat = st.prop_v.toNat + 1 :=
            bv64_add_toNat (by
              simp only [BitVec.toNat_ofNat]
              have := hlen_o.core_ok.trail_end_le
              have := hlen_o.core_ok.cur_vars_le; unfold dimacsBound at hmax; omega)
          refine s13_ovf_loop_wp (isBeyond := false)
            (rec_ph := decide (s.core.probing = 0#64)) (bigbig := decide (wm &&& 2#64 ≠ 0#64))
            (tk0 := st.ticks_v + 1#64 + ((BitVec.setWidth 64 sz32 + 31#64) >>> 5#64))
            (s_base := s_base) (s_disk := s_disk)
            hOvf hFlush hAddTicks hQ
            (fun sem_next te_mc mc0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
              h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 =>
              s13_outer_loop_jump hext1 hw2b1 hfl_o hih sem_next te_mc mc0
                h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
                h19 h20 h21 h22 h23 h24 h25 h26 h27 h28)
            hcfg hext1 hw2b1 c.hwcap c.hmaxv hlen hpr_lt rfl (by rw [hfl_o]; rfl)
            ⟨te_mem, rfl, hte_mem_le, hpr_te_mem⟩
            hlen_o htr_o hrsns_o hperm_o hag_o hcv_o hcl_o hprob_o halen_o hsc_o hd0_o
            hfl_dec1 hfl_le hp1_prop (by omega) hpr_ge (Or.inr rfl)
            (by rw [hcv_o]; exact htwo_cv) (by omega) (by rw [hcl_o]; exact hcur_lvl)
            rfl hnl64_idx hnot_lt' hnl_sb hdlim hdense_o hpi_0
            hte_o.symm hun_o.symm huf_o.symm hoom_o hct_o
            (fun h => Bool.noConfusion h) hm_of
      · have hpt_eq : st.prop_v.toNat = st.tend_v.toNat := by omega
        have hpr_lt_prop : s.core.propagated < st.prop_v.toNat := by
          have hte_ext : s.core.trail_end ≤ sem.core.trail_end := htr_o.1
          omega
        dsimp only at hm
        exact s13_outer_body_exit hAddTicks hQ hcfg hext1 hw2b1 hlen_o hwinv_o
          htr_o hrsns_o hperm_o hag_o hsc_o hd0_o hprop_o hte_o hfl_o hun_o huf_o
          hfl_le hpr_lt (Or.inl rfl) (fun h => Bool.noConfusion h)
          (fun _ => ⟨hpt_eq, hct_o, fun _ => hoom_o, fun _ => hfl_dec hpr_lt_prop⟩)
          (fun _ h => absurd h (by decide)) (fun h => absurd h (by decide)) hm

public theorem full_propagate_ignore_wp (Γ : Env)
    (hOvf : Γ.Has "full_prop_lit_ovf_hot" Spec.fullPropLitOvfHotSpec)
    (hFlush : Γ.Has "full_prop_flush_del_fid" Spec.fidPropFlushDelSpec)
    (hWm4 : Γ.Has "m6_wm4_get" Float64.Spec.m6Wm4GetSpec)
    (hAddTicks : Γ.Has "m6_hdr_add_ticks" Tiers.Spec.m6HdrAddTicksSpec) :
    ∀ a m Q X, Spec.propIgnoreM6Spec a m Q X →
      Func.wp Γ full_propagate_ignore_body a m Q X :=
  full_propagate_ignore_hot_wp Γ hOvf hFlush hWm4 hAddTicks

public theorem full_propagate_wp (Γ : Env)
    (hIgnHot : Γ.Has "full_propagate_ignore_hot" Spec.propIgnoreM6Spec) :
    ∀ a m Q X, Spec.propagateM6Spec a m Q X →
      Func.wp Γ full_propagate_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, ext, s, R, rfl, hcfg, hext, hlen, hwinv,
    hdense, hm, hQ⟩
  unfold Func.wp full_propagate_body
  refine wp_call_of_spec _ _ (hIgnHot _ _ _ _ ⟨c, F0, F_cur, ext, s, R, rfl, hcfg, hext, hlen,
    hwinv, hdense, hm, ?_⟩)
  intro r ext' vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl'
    wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' sc' m' _s'
    hext' hw2b' hlen' hwinv' htr' hrsns' hperm' hprob' hred' hdlen' hsc' hd0'
    hfl_le' hr_cases hr0 hr1 hr2 hnoop hm'
  exact (wp_ret _).mpr (hQ r ext' vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl'
    wvec' arena' wstk' wlen' wu' fuel' ctype' cref' c0' c1' oom' sc' m'
    hext' hw2b' hlen' hwinv' htr' hrsns' hperm' hprob' hred' hdlen' hsc' hd0'
    hfl_le' hr_cases
    (fun hr => let ⟨h1, _, h3, h4⟩ := hr0 hr; ⟨h1, h3, h4⟩)
    (fun hr => let ⟨h1, h2, h3, _⟩ := hr1 hr; ⟨h1, h2, h3⟩)
    hr2 hnoop hm')

public theorem full_propagate_beyond_m7_wp (Γ : Env)
    (hOvf : Γ.Has "full_prop_lit_ovf_hot" Spec.fullPropLitOvfHotSpec)
    (hFlush : Γ.Has "full_prop_flush_del_fid" Spec.fidPropFlushDelSpec)
    (hWm4 : Γ.Has "m6_wm4_get" Float64.Spec.m6Wm4GetSpec)
    (hAddTicks : Γ.Has "m6_hdr_add_ticks" Tiers.Spec.m6HdrAddTicksSpec) :
    ∀ a m Q X, Spec.propagateBeyondM6Spec a m Q X →
      Func.wp Γ full_propagate_beyond_m7_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, ext0, s, R, rfl, hcfg, hext0, hlen,
    hwinv, hdense, hm, hQ_raw⟩
  have hQ := s13HQ_of_propBeyond hQ_raw
  have hmax := c.hmaxv
  have hcv_le := hlen.core_ok.cur_vars_le
  have hte_le := hlen.core_ok.trail_end_le
  have hpr_le := hlen.core_ok.propagated_le
  have hm_f := fullM6HdrMem_focus hm
  dsimp only [Func.wp, full_propagate_beyond_m7_body]
  s13_hsteps_nogrp
  · exact s13_ret_early_0 hQ hext0 hlen hwinv (by unfold dimacsBound at hmax; omega) hm
  · exact s13_ret_early_oom hQ hext0 hlen hwinv (by unfold dimacsBound at hmax; omega) hc hm
  · have hpr_lt : s.core.propagated < s.core.trail_end := by unfold dimacsBound at hmax; omega
    have hoom0 : s.core.oom = 0#64 := hc
    refine wp_call_of_spec _ _ (hWm4 _ _ _ _ ⟨c, ext0, s, R, rfl, hcfg, hext0, hlen, hm, ?_⟩)
    intro wm hm_w
    have hm_wf := fullM6HdrMem_focus hm_w
    s13_hsteps_nogrp
    have ⟨hdlim, htwo_cv, hcl32, hcur_lvl⟩ := s13_outer_arith_facts hlen hwinv
    let μOut : S13OutSt → Nat := fun st => st.fuel_v.toNat
    let InvOut : S13OutSt → Mem 64 → Prop := fun st m' =>
      S13OuterInv true c F0 F_cur ext0 s R st.fuel_v.toNat
        st.prop_v st.tend_v st.fuel_v st.unass_v st.unfl_v st.ticks_v m'
    refine wp_while_state s13OutProj μOut InvOut ?_ ?_
    · intro J hJ
      let st0 : S13OutSt := ⟨BitVec.ofNat 64 s.core.propagated,
        BitVec.ofNat 64 s.core.trail_end, s.core.fuel,
        s.core.unassigned, s.core.unflushed, 0#64⟩
      exact (wp_jump _ _).mpr (hJ st0 m (s13_outer_init hext0 hlen hwinv hdense hoom0 hm_w))
    · intro J st m' hInv hih
      rcases s13OuterInv_elim hInv with
        ⟨ext1, sem, te_mem, _hrem, hext1, hw2b1, hlen_o, hwinv_o, htr_o, hrsns_o,
          hperm_o, hag_o, hprop_o, hte_o, hfl_o, hun_o, huf_o, hoom_o, _hct_o, hcf_o,
          hdense_o, hcv_o, hcl_o, hprob_o, halen_o, hfl_le, hfl_dec, hpr_ge, hpt_le,
          hte_mem_le, hpr_te_mem, hsc_o, hd0_o, hm_o⟩
      dsimp only [Blocks.get, s13OutProj]
      have hm_of := fullM6HdrMem_focus hm_o
      s13_hsteps_nogrp
      · have hfl0 : st.fuel_v = 0#64 := hc
        dsimp only at hm
        exact s13_outer_body_exit (fuel_v := 0#64) hAddTicks hQ hcfg hext1 hw2b1 hlen_o
          hwinv_o htr_o hrsns_o hperm_o hag_o hsc_o hd0_o hprop_o hte_o (hfl_o.trans hfl0)
          hun_o huf_o hfl_le hpr_lt (Or.inr rfl) hcf_o
          (fun h => absurd h (by decide)) (fun h => Bool.noConfusion h)
          (fun _ => Or.inr (by rw [hfl_o, hfl0])) hm
      · have hpt_lt : st.prop_v.toNat < st.tend_v.toNat := by omega
        have hfl_nz : st.fuel_v ≠ 0#64 := hc
        let s_disk : FullState := { s with core := { s.core with trail_end := te_mem } }
        let s_base : FullState := { sem with core := { sem.core with
          propagated := s.core.propagated, fuel := s.core.fuel } }
        have hpr_lt_mv : st.prop_v.toNat < c.max_vars := by
          have := hlen_o.core_ok.trail_end_le
          have := hlen_o.core_ok.cur_vars_le; omega
        have hpr_lt_trl : st.prop_v.toNat < (fastPropMem s_disk s_base).core.trl.length := by
          change st.prop_v.toNat < sem.core.trl.length
          rw [hlen_o.core_ok.trl_len]; exact hpr_lt_mv
        s13_hsteps_nogrp
        let lit : BitVec 32 := (fastPropMem s_disk s_base).core.trl[st.prop_v.toNat]'hpr_lt_trl
        have hlit_eq : lit = sem.core.trl[st.prop_v.toNat]?.getD 0#32 := by
          change (fastPropMem s_disk s_base).core.trl[st.prop_v.toNat]'hpr_lt_trl =
            (fastPropMem s_disk s_base).core.trl[st.prop_v.toNat]?.getD 0#32
          rw [List.getElem?_eq_getElem hpr_lt_trl]; rfl
        have hlit_lt : lit.toNat < 2 * sem.core.cur_vars := by
          rw [hlit_eq]; exact hwinv_o.trail_lits_lt st.prop_v.toNat (by omega)
        let not_lit : BitVec 32 := lit ^^^ 1#32
        have ⟨hnot_lt, hnot_div, _⟩ := bv32_xor1_props hlit_lt
        have hnot_lt_n : not_lit.toNat < 2 * sem.core.cur_vars := hnot_lt
        have hnl64_idx : (BitVec.setWidth 64 not_lit <<< 1#64).toNat = 2 * not_lit.toNat := by
          have := hlen_o.core_ok.cur_vars_le
          exact bv64_shl1_u32 (by unfold dimacsBound at hmax; omega)
        have hnl_lt_wvec : (BitVec.setWidth 64 not_lit <<< 1#64).toNat <
            (fastPropMem s_disk s_base).core.wvec.length := by
          change (BitVec.setWidth 64 not_lit <<< 1#64).toNat < sem.core.wvec.length
          rw [hnl64_idx, hlen_o.core_ok.wvec_len]; have := hlen_o.core_ok.cur_vars_le; omega
        have hnl1_idx : ((BitVec.setWidth 64 not_lit <<< 1#64) + 1#64).toNat =
            2 * not_lit.toNat + 1 := by
          rw [bv64_add_toNat (by
            simp only [BitVec.toNat_ofNat]
            have := hlen_o.core_ok.cur_vars_le; unfold dimacsBound at hmax; omega), hnl64_idx]
          rfl
        have hnl1_lt_wvec : ((BitVec.setWidth 64 not_lit <<< 1#64) + 1#64).toNat <
            (fastPropMem s_disk s_base).core.wvec.length := by
          change ((BitVec.setWidth 64 not_lit <<< 1#64) + 1#64).toNat < sem.core.wvec.length
          rw [hnl1_idx, hlen_o.core_ok.wvec_len]; have := hlen_o.core_ok.cur_vars_le; omega
        s13_hsteps_nogrp
        · have ⟨hlt_fl, hInv'⟩ :=
            s13_outer_sz0_next (ticks_v := st.ticks_v) hext1 hw2b1 hlen_o hwinv_o htr_o
            hrsns_o hperm_o hag_o hprop_o hte_o hfl_o hun_o huf_o hoom_o
            (fun h => Bool.noConfusion h) hcf_o hdense_o hcv_o hcl_o hprob_o halen_o
            hfl_le hpr_ge hpt_lt hfl_nz hte_mem_le hpr_te_mem hsc_o hd0_o hm_o
          exact hih ⟨st.prop_v + 1#64, st.tend_v, st.fuel_v - 1#64,
            st.unass_v, st.unfl_v, st.ticks_v + 1#64⟩ m' hlt_fl hInv'
        · let off32 : BitVec 32 :=
            (fastPropMem s_disk s_base).core.wvec[
              (BitVec.setWidth 64 not_lit <<< 1#64).toNat]'hnl_lt_wvec
          let sz32 : BitVec 32 :=
            (fastPropMem s_disk s_base).core.wvec[
              ((BitVec.setWidth 64 not_lit <<< 1#64) + 1#64).toNat]'hnl1_lt_wvec
          have hsz_nz : BitVec.setWidth 64 sz32 ≠ 0#64 := by
            intro h0; apply hc
            have hnx : not_lit.toNat =
                (sem.core.trl[st.prop_v.toNat]'hpr_lt_trl).toNat ^^^ 1 := by
              change (lit ^^^ 1#32).toNat = _
              rw [BitVec.toNat_xor]; rfl
            have hidx_eq : (2 * ((sem.core.trl[st.prop_v.toNat]'hpr_lt_trl).toNat ^^^ 1) +
                BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 =
                ((BitVec.setWidth 64 not_lit <<< 1#64) + 1#64).toNat := by
              rw [hnl1_idx, ← hnx]
              have := hlen_o.core_ok.cur_vars_le; unfold dimacsBound at hmax
              change (2 * not_lit.toNat + 1) % 2 ^ 64 = 2 * not_lit.toNat + 1; omega
            let idx1 := ((BitVec.setWidth 64 not_lit <<< 1#64) + 1#64).toNat
            have h0' : BitVec.setWidth 64 (sem.core.wvec[idx1]'hnl1_lt_wvec) = 0 := h0
            rw [← h0']; congr 1; exact list_getElem_eq hidx_eq
          have hvar_lt : (BitVec.setWidth 64 (not_lit >>> 1#32)).toNat < c.max_vars := by
            rw [m7_bv32_rshift1_toNat not_lit]
            have := hlen_o.core_ok.cur_vars_le; omega
          have hvar_lt_lvl : (BitVec.setWidth 64 (not_lit >>> 1#32)).toNat <
              (fastPropMem s_disk s_base).core.lvl.length := by
            change (BitVec.setWidth 64 (not_lit >>> 1#32)).toNat < sem.core.lvl.length
            rw [hlen_o.core_ok.lvl_len]; exact hvar_lt
          s13_hsteps_nogrp
          have hvar_eq := m7_bv32_rshift1_toNat not_lit
          have hoff_eq : BitVec.setWidth 64 off32 =
              BitVec.setWidth 64 (sem.core.wvec[2 * not_lit.toNat]?.getD 0#32) := by
            congr 1
            change (fastPropMem s_disk s_base).core.wvec[
              (BitVec.setWidth 64 not_lit <<< 1#64).toNat]'hnl_lt_wvec =
              (fastPropMem s_disk s_base).core.wvec[2 * not_lit.toNat]?.getD 0#32
            rw [← hnl64_idx, List.getElem?_eq_getElem hnl_lt_wvec]; rfl
          have hsz_eq : BitVec.setWidth 64 sz32 =
              BitVec.setWidth 64 (sem.core.wvec[2 * not_lit.toNat + 1]?.getD 0#32) := by
            congr 1
            change (fastPropMem s_disk s_base).core.wvec[
              ((BitVec.setWidth 64 not_lit <<< 1#64) + 1#64).toNat]'hnl1_lt_wvec =
              (fastPropMem s_disk s_base).core.wvec[2 * not_lit.toNat + 1]?.getD 0#32
            rw [← hnl1_idx, List.getElem?_eq_getElem hnl1_lt_wvec]; rfl
          let nl_lvl : BitVec 32 := (fastPropMem s_disk s_base).core.lvl[
            (BitVec.setWidth 64 (not_lit >>> 1#32)).toNat]'hvar_lt_lvl
          have hnl_eq : nl_lvl = sem.core.lvl[not_lit.toNat / 2]?.getD 0#32 := by
            change (fastPropMem s_disk s_base).core.lvl[
              (BitVec.setWidth 64 (not_lit >>> 1#32)).toNat]'hvar_lt_lvl =
              (fastPropMem s_disk s_base).core.lvl[not_lit.toNat / 2]?.getD 0#32
            rw [← hvar_eq, List.getElem?_eq_getElem hvar_lt_lvl]; rfl
          have ⟨hnot_lt', hpi_0, hnl_sb⟩ := s13_outer_sz_nz_pi0 (s_base := s_base)
            rfl hlen_o hwinv_o hdense_o hpr_ge (by omega) hlit_eq rfl
            (off0 := BitVec.setWidth 64 off32) hoff_eq
            (sz0 := BitVec.setWidth 64 sz32) hsz_eq hsz_nz rfl
            (nl_lvl := nl_lvl) hnl_eq
          have hfl_dec1 : (sem.core.fuel - 1#64).toNat < sem.core.fuel.toNat := by
            have hf1 := bv64_sub1_toNat hfl_nz
            have hpos := bv64_toNat_pos_of_ne_zero hfl_nz
            rw [hfl_o]; omega
          have hp1_prop : (st.prop_v + 1#64).toNat = st.prop_v.toNat + 1 :=
            bv64_add_toNat (by
              simp only [BitVec.toNat_ofNat]
              have := hlen_o.core_ok.trail_end_le
              have := hlen_o.core_ok.cur_vars_le; unfold dimacsBound at hmax; omega)
          refine s13_ovf_loop_wp (isBeyond := true)
            (rec_ph := decide (s.core.probing = 0#64)) (bigbig := decide (wm &&& 2#64 ≠ 0#64))
            (tk0 := st.ticks_v + 1#64 + ((BitVec.setWidth 64 sz32 + 31#64) >>> 5#64))
            (ignore_ref := Arg.imm 0xFFFFFFFF#64) (ign_v := 0xFFFFFFFF#64)
            (s_base := s_base) (s_disk := s_disk)
            hOvf hFlush hAddTicks hQ
            (fun sem_next te_mc mc0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
              h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 =>
              s13_outer_loop_jump hext1 hw2b1 hfl_o hih sem_next te_mc mc0
                h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
                h19 h20 h21 h22 h23 h24 h25 h26 h27 h28)
            hcfg hext1 hw2b1 c.hwcap c.hmaxv hlen hpr_lt rfl (by rw [hfl_o]; rfl)
            ⟨te_mem, rfl, hte_mem_le, hpr_te_mem⟩
            hlen_o htr_o hrsns_o hperm_o hag_o hcv_o hcl_o hprob_o halen_o hsc_o hd0_o
            hfl_dec1 hfl_le hp1_prop (by omega) hpr_ge (Or.inl rfl)
            (by rw [hcv_o]; exact htwo_cv) (by omega) (by rw [hcl_o]; exact hcur_lvl)
            rfl hnl64_idx hnot_lt' hnl_sb hdlim hdense_o hpi_0
            hte_o.symm hun_o.symm huf_o.symm hoom_o
            (fun h => Bool.noConfusion h) hcf_o hm_of
      · have hpt_eq : st.prop_v.toNat = st.tend_v.toNat := by omega
        have hpr_lt_prop : s.core.propagated < st.prop_v.toNat := by
          have hte_ext : s.core.trail_end ≤ sem.core.trail_end := htr_o.1
          omega
        dsimp only at hm
        exact s13_outer_body_exit hAddTicks hQ hcfg hext1 hw2b1 hlen_o hwinv_o
          htr_o hrsns_o hperm_o hag_o hsc_o hd0_o hprop_o hte_o hfl_o hun_o huf_o
          hfl_le hpr_lt (Or.inl rfl) hcf_o
          (fun _ => ⟨hpt_eq, fun h => Bool.noConfusion h,
            fun _ => hoom_o, fun _ => hfl_dec hpr_lt_prop⟩)
          (fun h => Bool.noConfusion h) (fun h => absurd h (by decide)) hm

private theorem fullArenaVarsNodup_of_perm {s s' : FullState}
    (hn : FullArenaVarsNodup s) (hp : FullArenaPermEq s.core s'.core) :
    FullArenaVarsNodup s' := by
  intro r hr hgarb
  have hr0 : r ∈ fullArenaClauseRefsCore s.core := by
    change r ∈ fullArenaClauseRefsCore s'.core at hr
    rwa [hp.2.1] at hr
  have ⟨_, hgarb_eq, hlits_perm⟩ := hp.2.2 r hr0
  have hgarb0 : fullArenaClauseGarb s r = false := by
    change fullArenaClauseGarbCore s'.core r = false at hgarb
    rwa [hgarb_eq] at hgarb
  exact (hlits_perm.map (fun x => x / 2)).nodup_iff.mpr (hn r hr0 hgarb0)

private theorem fullWitnessInv_with_inconsistent {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState}
    (hwinv : FullWitnessInv c F0 F_cur s.core) (hcl : s.core.cur_level = 0)
    (hconfl : FullConflictOkW F_cur s) :
    F0.Unsat ∧ FullWitnessInv c F0 F_cur { s.core with inconsistent := 1#64 } := by
  have hw_self : FullWitnessInv c (cnfOfClauses F_cur) F_cur s.core :=
    { hwinv with ext_sound := ⟨hwinv.ext_sound.1, id⟩ }
  have hunsat_cur : (cnfOfClauses F_cur).Unsat :=
    level0_unsat_of_conflict_okW hw_self hcl hconfl
  exact ⟨hwinv.ext_sound.2 hunsat_cur,
    FullBvaFwdHelpers.fullWitnessInv_set_inconsistent hwinv hunsat_cur⟩

private theorem fullM6HdrInv_flush_clear {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s : FullState} (hinv : FullM6HdrInv c F0 ext s) :
    FullM6HdrInv c F0 ext { s with core := { s.core with
      unflushed := 0#64, confl_ref := 0xFFFFFFFF#64, confl_type := 0#64 } } := by
  rcases hinv with ⟨hcfg, hext, ⟨hlen, F_cur, hwinv⟩, hlm, hnodup, hext_sc, hdense⟩
  have hwat : WatchesInv F_cur s.core := by simpa [ModeWatchesInv, hdense] using hwinv.watches
  have hnw' : FullWitnessInv c F0 F_cur (withEmptyWatchesCore c
      { s.core with unflushed := 0#64, confl_ref := 0xFFFFFFFF#64, confl_type := 0#64 }) :=
    fullWitnessInv_nw_congr hlen.core_ok.cur_vars_le
      (fullWitnessInv_to_nw hlen.core_ok.cur_vars_le hwinv)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hwat' : WatchesInv F_cur
      { s.core with unflushed := 0#64, confl_ref := 0xFFFFFFFF#64, confl_type := 0#64 } :=
    fid_watches_congr hwat rfl rfl rfl rfl (fun _ hr => hr)
  refine ⟨hcfg, hext, ⟨⟨{ hlen.core_ok with }, hlen.scratch_ok⟩, F_cur,
    fullWitnessInv_of_nw hnw' hdense hwat'⟩, hlm, hnodup, hext_sc, hdense⟩

public theorem full_flush_trail_wp (Γ : Env)
    (hBt : Γ.Has "full_backtrack" fullBacktrackSpec)
    (hProp : Γ.Has "full_propagate" Spec.propagateM6Spec) :
    ∀ a m Q X, Spec.flushTrailM6Spec a m Q X →
      Func.wp Γ full_flush_trail_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, ext, s, R, rfl, hinv, hm, hQ⟩
  rcases hinv with ⟨hcfg, hext, ⟨hlen, F_cur, hwinv⟩, hlm, hnodup, hext_sc, hdense⟩
  have hinv_s : FullM6HdrInv c F0 ext s :=
    ⟨hcfg, hext, ⟨hlen, F_cur, hwinv⟩, hlm, hnodup, hext_sc, hdense⟩
  have hm_f := fullM6HdrMem_focus hm
  dsimp only [Func.wp, full_flush_trail_body]
  s13_hsteps_nogrp
  · exact hQ 20#64 ext s m hext (fun h => ⟨h, M6ExtW2bPres.refl _⟩) hinv_s
      (fullArenaPermEq_refl _) (fullProbeScratchPres_refl _) rfl rfl (fun _ => rfl)
      (Or.inr (Or.inr rfl)) rfl rfl (Nat.le_refl _) id
      (fun _ => fullM6HdrInv_inconsistent_unsat hinv_s hc)
      (fun h => absurd h (by decide)) (fun _ => Or.inr hc) hm
  · have hinc0 : s.core.inconsistent = 0#64 := hc
    let Inv1 : Unit → Mem 64 → Prop := fun _ m1 =>
      ∃ s1, FullM6HdrInv c F0 ext s1 ∧ FullArenaPermEq s.core s1.core ∧
        FullProbeScratchPres s s1 ∧ s1.scratch.red_refs = s.scratch.red_refs ∧
        s1.scratch.delayed_len = s.scratch.delayed_len ∧
        (c.delayed_cap = 0 → s1.scratch.delayed = s.scratch.delayed) ∧
        s1.core.cur_vars = s.core.cur_vars ∧ s1.core.probing = s.core.probing ∧
        s1.core.fuel = s.core.fuel ∧ s1.core.inconsistent = 0#64 ∧
        s1.core.cur_level = 0 ∧ (s.core.cur_level = 0 → s1 = s) ∧
        (FullM6HdrMem c ext s1 ⋆ R) m1
    refine wp_join_state (fun _ : Unit => ()) Inv1 ?_ ?_
    · intro J1 _ m1 ⟨s1, hinv1, hperm1, hprob1, hred1, hdlen1, hd0_1, hcv1, hprb1,
        hfl1, hinc1, hcl1, hs1_eq, hm1⟩
      rcases hinv1 with ⟨_, _, ⟨hlen1, F_cur1, hwinv1⟩, hlm1, hnodup1, hext_sc1, hdense1⟩
      have hinv1_full : FullM6HdrInv c F0 ext s1 :=
        ⟨hcfg, hext, ⟨hlen1, F_cur1, hwinv1⟩, hlm1, hnodup1, hext_sc1, hdense1⟩
      have hm1_f := fullM6HdrMem_focus hm1
      s13_hsteps_nogrp
      · exact hQ 0#64 ext s1 m1 hext (fun h => ⟨h, M6ExtW2bPres.refl _⟩) hinv1_full
          hperm1 hprob1 hred1 hdlen1 hd0_1 (Or.inl rfl) hcv1 hprb1
          (by rw [hfl1]; exact Nat.le_refl _)
          (fun _ => hcl1) (fun h => absurd h (by decide))
          (fun h => absurd h (by decide)) (fun _ => Or.inl hcl1) hm1
      · have hoom1 : s1.core.oom = 0#64 := hc
        let Inv2 : Unit → Mem 64 → Prop := fun _ m2 =>
          ∃ ext2 s2, M6HdrExtOk ext2 ∧
            (M6HdrExtInitOk ext → M6HdrExtInitOk ext2 ∧ M6ExtW2bPres ext ext2) ∧
            FullM6HdrInv c F0 ext2 s2 ∧ FullArenaPermEq s.core s2.core ∧
            FullProbeScratchPres s s2 ∧ s2.scratch.red_refs = s.scratch.red_refs ∧
            s2.scratch.delayed_len = s.scratch.delayed_len ∧
            (c.delayed_cap = 0 → s2.scratch.delayed = s.scratch.delayed) ∧
            s2.core.cur_vars = s.core.cur_vars ∧ s2.core.probing = s.core.probing ∧
            s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧ s2.core.cur_level = 0 ∧
            s2.core.propagated = s2.core.trail_end ∧ s2.core.oom = 0#64 ∧
            s2.core.inconsistent = 0#64 ∧
            (s.core.cur_level = 0 → s.core.propagated < s.core.trail_end →
              s2.core.fuel.toNat < s.core.fuel.toNat) ∧
            (FullM6HdrMem c ext2 s2 ⋆ R) m2
        refine wp_join_state (fun _ : Unit => ()) Inv2 ?_ ?_
        · intro J2 _ m2 ⟨ext2, s2, hext2, hw2b2, hinv2, hperm2, hprob2, hred2, hdlen2,
            hd0_2, hcv2, hprb2, hfl_le2, hcl2, hpt2, hoom2, hinc2, hfl_dec2, hm2⟩
          have hm2_f := fullM6HdrMem_focus hm2
          s13_hsteps_nogrp
          dsimp only at hm
          let s3 : FullState := { s2 with core := { s2.core with
            unflushed := 0#64, confl_ref := 0xFFFFFFFF#64, confl_type := 0#64 } }
          exact hQ 1#64 ext2 s3 _ hext2 hw2b2 (fullM6HdrInv_flush_clear hinv2)
            hperm2 hprob2 hred2 hdlen2 hd0_2 (Or.inr (Or.inl rfl)) hcv2 hprb2 hfl_le2
            (fun _ => hcl2) (fun h => absurd h (by decide))
            (fun _ => ⟨hcl2, hpt2, hoom2, rfl, hinc2, hfl_dec2⟩)
            (fun h => absurd rfl h) (fullM6HdrMem_unfocus hm)
        · intro J2 hJ2
          have hmax := c.hmaxv
          have hcv1_le := hlen1.core_ok.cur_vars_le
          have hte1_le := hlen1.core_ok.trail_end_le
          have hpr1_le := hlen1.core_ok.propagated_le
          s13_hsteps_nogrp
          · have hlt1 : s1.core.propagated < s1.core.trail_end := by
              unfold dimacsBound at hmax; omega
            refine wp_call_of_spec _ _ (hProp _ _ _ _ ⟨c, F0, F_cur1, ext, s1, R, rfl, hcfg, hext,
              hlen1, hwinv1, hdense1, hm1, ?_⟩)
            intro r_p ext2 vals2 flags2 lvl2 rsns2 trl2 tp2 te2 prop2 unass2 unfl2
              wvec2 arena2 wstk2 wlen2 wu2 fuel2 ctype2 cref2 c0_2 c1_2 oom2 sc2 m2 _s2
              hext2 hw2b2 hlen2 hwinv2 _htr2 _hrsns2 hperm2 hprob2_raw hred2 hdlen2
              _hsc2 hd0_2 hfl_le2 hr_cases hr0 hr1 _hr2 _hnoop2 hm2
            let s2 : FullState := {
              core := { s1.core with
                vals := vals2, flags := flags2, lvl := lvl2, rsns := rsns2,
                trl := trl2, trail_pos := tp2, trail_end := te2, propagated := prop2,
                unassigned := unass2, unflushed := unfl2,
                wvec := wvec2, arena := arena2, wstk := wstk2,
                wlen := wlen2, wusable := wu2, fuel := fuel2,
                confl_type := ctype2, confl_ref := cref2,
                confl_lit0 := c0_2, confl_lit1 := c1_2, oom := oom2 },
              scratch := sc2 }
            have hprob12 : FullProbeScratchPres s1 s2 := hprob2_raw
            have hprob02 : FullProbeScratchPres s s2 := fullProbeScratchPres_trans hprob1 hprob12
            have hperm02 : FullArenaPermEq s.core s2.core := fullArenaPermEq_trans hperm1 hperm2
            have hinv2 : FullM6HdrInv c F0 ext2 s2 :=
              ⟨hcfg, hext2, ⟨hlen2, F_cur1, hwinv2⟩, hlm1,
                fullArenaVarsNodup_of_perm hnodup1 hperm2,
                FullExtScratchOk.of_pres hext_sc1 hprob12.1 (fun _ hr => by
                  change _ ∈ fullArenaClauseRefsCore s2.core; rw [hperm2.2.1]; exact hr),
                hdense1⟩
            have hm2_f := fullM6HdrMem_focus hm2
            s13_hsteps_nogrp
            · have ⟨_, _, hconfl2⟩ := hr1 hc
              have ⟨hunsat, hwinv2_inc⟩ := fullWitnessInv_with_inconsistent hwinv2 hcl1 hconfl2
              let s2_inc : FullState := { s2 with core := { s2.core with inconsistent := 1#64 } }
              have hinv2_inc : FullM6HdrInv c F0 ext2 s2_inc :=
                ⟨hcfg, hext2, ⟨⟨{ hlen2.core_ok with }, hlen2.scratch_ok⟩, F_cur1, hwinv2_inc⟩,
                  hlm1, fullArenaVarsNodup_of_perm hnodup1 hperm2,
                  FullExtScratchOk.of_pres hext_sc1 hprob12.1 (fun _ hr => by
                    change _ ∈ fullArenaClauseRefsCore s2.core; rw [hperm2.2.1]; exact hr),
                  hdense1⟩
              dsimp only at hm
              exact hQ 20#64 ext2 s2_inc _ hext2 hw2b2 hinv2_inc hperm02 hprob02
                (hred2.trans hred1) (hdlen2.trans hdlen1)
                (fun h0 => (hd0_2 h0).trans (hd0_1 h0)) (Or.inr (Or.inr rfl))
                hcv1 hprb1 (by rw [← hfl1]; exact hfl_le2) (fun _ => hcl1)
                (fun _ => hunsat) (fun h => absurd h (by decide))
                (fun _ => Or.inl hcl1) (fullM6HdrMem_unfocus hm)
            · exact hQ 0#64 ext2 s2 m2 hext2 hw2b2 hinv2 hperm02 hprob02
                (hred2.trans hred1) (hdlen2.trans hdlen1)
                (fun h0 => (hd0_2 h0).trans (hd0_1 h0)) (Or.inl rfl)
                hcv1 hprb1 (by rw [← hfl1]; exact hfl_le2) (fun _ => hcl1)
                (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
                (fun _ => Or.inl hcl1) hm2
            · exact hQ 0#64 ext2 s2 m2 hext2 hw2b2 hinv2 hperm02 hprob02
                (hred2.trans hred1) (hdlen2.trans hdlen1)
                (fun h0 => (hd0_2 h0).trans (hd0_1 h0)) (Or.inl rfl)
                hcv1 hprb1 (by rw [← hfl1]; exact hfl_le2) (fun _ => hcl1)
                (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
                (fun _ => Or.inl hcl1) hm2
            · have hr_eq0 : r_p = 0#64 := by assumption
              have ⟨hpt2, hoom2_imp, hfl_dec2⟩ := hr0 hr_eq0
              exact hJ2 () m2 ⟨ext2, s2, hext2, hw2b2, hinv2, hperm02,
                hprob02, hred2.trans hred1, hdlen2.trans hdlen1,
                fun h0 => (hd0_2 h0).trans (hd0_1 h0), hcv1, hprb1,
                by rw [← hfl1]; exact hfl_le2, hcl1, hpt2, hoom2_imp hoom1, hinc1,
                fun _ _ => by rw [← hfl1]; exact hfl_dec2 hlt1, hm2⟩
          · have hpt1 : s1.core.propagated = s1.core.trail_end := by
              unfold dimacsBound at hmax; omega
            exact hJ2 () m1 ⟨ext, s1, hext, fun h => ⟨h, M6ExtW2bPres.refl _⟩,
              hinv1_full, hperm1, hprob1, hred1, hdlen1, hd0_1, hcv1, hprb1,
              by rw [hfl1]; exact Nat.le_refl _, hcl1, hpt1, hoom1, hinc1,
              fun hcl0 hlt0 => by rw [hs1_eq hcl0] at hpt1; omega, hm1⟩
    · intro J1 hJ1
      have hmax := c.hmaxv
      have hcl_le := hwinv.cur_level_le
      have hte_le := hlen.core_ok.trail_end_le
      have hcv_le := hlen.core_ok.cur_vars_le
      have hcl64 : (BitVec.ofNat 64 s.core.cur_level).toNat = s.core.cur_level :=
        bv64_ofNat_toNat_lt (by unfold dimacsBound at hmax; omega)
      s13_hsteps_nogrp
      · have hcl_nz : s.core.cur_level ≠ 0 := fun h0 => hc (by simp [h0])
        have hmv_pos : 0 < c.max_vars := by
          obtain ⟨i, hi, _⟩ := hwinv.levels_inhabited 1 (by omega) (by omega)
          omega
        refine wp_call_of_spec _ _ (hBt _ _ _ _ ⟨c, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl,
          hlen, by unfold dimacsBound at hmax; omega, fun _ => by simp; exact hmv_pos,
          hwinv.trail_lits_lt, hm_f, ?_⟩)
        intro vals1 lvl1 rsns1 trl1 tp1 te1 prop1 cl1 unass1 sc1 m1 _s1 hlen1 _hte1 _hprop1
          hcl1 hprob1 hsc1 _htrl1 _hvals1 hwinv_bt _hotfs1 hm1_f
        let s1 : FullState := {
          core := { s.core with
            vals := vals1, lvl := lvl1, rsns := rsns1, trl := trl1, trail_pos := tp1,
            trail_end := te1, propagated := prop1, cur_level := cl1, unassigned := unass1 },
          scratch := sc1 }
        rcases hsc1 with ⟨_, _, _, _, _, _, _, _, _, hsc1_eq⟩
        have hwinv1 : FullWitnessInv c F0 F_cur s1.core :=
          hwinv_bt F0 F_cur hwinv (by simp)
        have hinv1 : FullM6HdrInv c F0 ext s1 :=
          ⟨hcfg, hext, ⟨hlen1, F_cur, hwinv1⟩, hlm, hnodup,
            FullExtScratchOk.of_pres hext_sc hprob1.1 (fun _ hr => hr), hdense⟩
        exact (wp_jump _ _).mpr (hJ1 () m1 ⟨s1, hinv1, fullArenaPermEq_refl _, hprob1,
          by dsimp only [s1]; rw [hsc1_eq], by dsimp only [s1]; rw [hsc1_eq],
          fun _ => by dsimp only [s1]; rw [hsc1_eq],
          rfl, rfl, rfl, hinc0, by simpa using hcl1, fun h0 => absurd h0 hcl_nz,
          fullM6HdrMem_unfocus hm1_f⟩)
      · have hcl0 : s.core.cur_level = 0 := by
          have := congrArg BitVec.toNat hc
          simpa [hcl64] using this
        exact hJ1 () m ⟨s, hinv_s, fullArenaPermEq_refl _,
          fullProbeScratchPres_refl _, rfl, rfl, fun _ => rfl, rfl, rfl, rfl,
          hinc0, hcl0, fun _ => rfl, hm⟩

end LeanQbe.T.Examples.Kissat.Proof.PropSearch
