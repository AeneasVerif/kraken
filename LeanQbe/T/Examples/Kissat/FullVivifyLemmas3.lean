module

public import LeanQbe.T.Examples.Kissat.FullVivifyLemmas1

/-!
# Kissat `D-Full` Tiered Clause Vivification Proofs — Part 3 (Helpers)

Arena, shrink, watch-layout, and pure BFS helpers shared by Parts 2 and Hub.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat Kraken.Bedrock2.Test
open FullVivifySpecs FullVivifyTactics
open scoped FullArenaTactics FullVivifyTactics

namespace FullVivifyHelpers

private abbrev HypUnwatch (Γ : Env) : Prop :=
  ∀ a m Q X, fullVivUnwatchLargeSpec a m Q X → Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X
abbrev HypAddUnit (Γ : Env) : Prop :=
  ∀ a m Q X, fullVivAddUnitSpec a m Q X → Γ "full_add_unit" [i64, i32] [.bool] a m Q X
abbrev HypAddBin (Γ : Env) : Prop :=
  ∀ a m Q X, fullVivAddBinSpec a m Q X → Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X
abbrev HypWatchPush (Γ : Env) : Prop :=
  ∀ a m Q X, fullVivWatchPushSpec a m Q X →
    Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X

@[expose] def ShrkPad (ar_p ar0 : List (BitVec 32)) (cref old_sz nsz : Nat) : Prop :=
  if (ar0[cref]?.getD 0#32 &&& 0x00800000#32) = 0#32 then
    (∀ k, cref + 3 + nsz ≤ k → k < cref + 3 + old_sz - 1 → ar_p[k]? = ar0[k]?) ∧
    ar_p[cref + 3 + old_sz - 1]? = some 0xFFFFFFFF#32
  else ∀ k, cref + 3 + nsz ≤ k → k < cref + 3 + old_sz → ar_p[k]? = ar0[k]?

@[expose] def VivMetaEq (s s' : FullState) : Prop :=
  s'.core.arena_len = s.core.arena_len ∧ s'.core.cur_vars = s.core.cur_vars ∧
  s'.core.cur_level = 0 ∧ s'.core.probing = s.core.probing ∧ s'.core.fuel = s.core.fuel

@[expose] def VivArenaEq (s s' : FullState) : Prop :=
  fullArenaClauseRefs s' = fullArenaClauseRefs s ∧ ∀ q ∈ fullArenaClauseRefs s,
    fullArenaNextOff s'.core.arena s.core.arena_len q =
      fullArenaNextOff s.core.arena s.core.arena_len q

@[expose] def VivQ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop) (Q : Post [i64]) (cref : Nat) (allow0 : Bool) : Prop :=
  ∀ (r : BitVec 64) s' m',
    FullSparseInvW c F0 F_cur s' → s'.core.cur_level = 0 → s'.core.cur_vars = s.core.cur_vars →
    s'.core.arena_len = s.core.arena_len → s'.core.probing = s.core.probing →
    s'.core.fuel = s.core.fuel → fullArenaClauseRefs s' = fullArenaClauseRefs s →
    (if allow0 then r = 0#64 ∨ r = 1#64 ∨ r = 20#64 else r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
    (r = 20#64 → F0.Unsat) →
    (allow0 = true → r = 0#64 →
      cref ∈ fullArenaClauseRefs s' ∧ fullArenaClauseGarb s' cref = false) →
    (FullMem c s' ⋆ R) m' → Q (r, ()) m'

private theorem nodup_of_strict_subseq {orig sub : List Nat} (hnd : (orig.map (· / 2)).Nodup)
    (idxs : List Nat) (hlen : idxs.length = sub.length) (hp : idxs.Pairwise (· < ·))
    (hbd : ∀ q ∈ idxs, q < orig.length)
    (heq : ∀ (t : Nat) (ht : t < sub.length), sub[t] = orig[idxs[t]?.getD 0]'(by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hbd _ (by simp))) :
    (sub.map (· / 2)).Nodup := by
  unfold List.Nodup at hnd ⊢; rw [List.pairwise_iff_getElem] at hnd ⊢
  intro i j hi hj hij heqv; simp only [List.length_map, List.getElem_map] at hi hj heqv
  rw [heq i hi, heq j hj] at heqv
  have hid : ∀ t (ht : t < idxs.length), idxs[t]?.getD 0 = idxs[t]'ht := fun t ht => by
    rw [List.getElem?_eq_getElem ht, Option.getD_some]
  exact hnd (idxs[i]'(by omega)) (idxs[j]'(by omega)) (by simp [hbd]) (by simp [hbd])
    (List.pairwise_iff_getElem.mp hp i j (by omega) (by omega) hij)
    (by simpa [List.getElem_map, hid i (by omega), hid j (by omega)] using heqv)

private theorem fullArenaClauseLitsCore_length {k : FullCoreState} {r : Nat}
    (hbd : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena.length) :
    (fullArenaClauseLitsCore k r).length = fullArenaClauseSizeCore k r := by
  unfold fullArenaClauseLitsCore; simp [List.length_map, List.length_take, List.length_drop]; omega

private theorem fullArenaClauseLitsCore_getElem {k : FullCoreState} {r t : Nat}
    (hbd : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena.length)
    (ht : t < fullArenaClauseSizeCore k r) :
    (fullArenaClauseLitsCore k r)[t]'(by rw [fullArenaClauseLitsCore_length hbd]; exact ht) =
      (k.arena[r + 3 + t]'(by omega)).toNat := by
  unfold fullArenaClauseLitsCore; simp [List.getElem_map, List.getElem_take, List.getElem_drop]

private theorem fullArenaClauseLitsCore_eq_map_take {k : FullCoreState} {r nsz : Nat}
    {out : List (BitVec 32)} (hsz : fullArenaClauseSizeCore k r = nsz)
    (hbd : r + 3 + nsz ≤ k.arena.length) (hout_len : nsz ≤ out.length)
    (hget : ∀ j < nsz, k.arena[r + 3 + j]? = out[j]?) :
    fullArenaClauseLitsCore k r = (out.take nsz).map BitVec.toNat := by
  have hbd' : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena.length := hsz ▸ hbd
  refine List.ext_getElem
    (by rw [fullArenaClauseLitsCore_length hbd', hsz, List.length_map, List.length_take]; omega)
    fun t ht1 _ => ?_
  rw [fullArenaClauseLitsCore_length hbd', hsz] at ht1
  rw [fullArenaClauseLitsCore_getElem hbd' (by omega), List.getElem_map, List.getElem_take]
  have hg := hget t ht1; rw [List.getElem?_eq_getElem (by omega),
    List.getElem?_eq_getElem (by omega)] at hg; exact congrArg BitVec.toNat (Option.some.inj hg)

private theorem fullSparseInv_of_inPlaceShrink {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    (hl0 : s.core.cur_level = 0) {cref nsz : Nat}
    (href : cref ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cref = false)
    (hnsz3 : 3 ≤ nsz) (hnsz_lt : nsz < fullArenaClauseSize s cref)
    {arena' : List (BitVec 32)} {ni' nr' : BitVec 64} (hal' : arena'.length = c.arena_cap)
    (hout : ∀ k, (k < cref ∨ cref + 3 + fullArenaClauseSize s cref ≤ k) →
      arena'[k]? = s.core.arena[k]?)
    (hnhdr_garb : (arena'[cref]?.getD 0#32 &&& 0x00080000#32) = 0#32)
    (hnhdr_shrk : (arena'[cref]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32)
    (hnsz_eq : (arena'[cref + 2]?.getD 0#32).toNat = nsz)
    (hpad_old : ShrkPad arena' s.core.arena cref (fullArenaClauseSize s cref) nsz)
    (hlits_lt : ∀ j < nsz, (arena'[cref + 3 + j]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hnd_cref : ((fullArenaClauseLitsCore { s.core with arena := arena' } cref).map (· / 2)).Nodup)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullArenaClauseLitsCore { s.core with arena := arena' } cref))) :
    let s' : FullState :=
      { s with core := { s.core with arena := arena', num_irred := ni', num_redundant := nr' } }
    FullSparseInvW c F0 F_cur s' ∧ fullArenaClauseGarb s' cref = false ∧ VivArenaEq s s' := by
  intro s'
  have hw := hsp.2.1
  obtain ⟨hlen', hw', hrefs', hgb', _, hnxt'⟩ := inPlaceShrink_preserves_fullWitness hsp.1
    hw hl0 href hng hnsz3 hnsz_lt hal' hsp.1.scratch_ok hout hnhdr_garb hnhdr_shrk hnsz_eq
    (by simpa [ShrkPad, fullArenaHdr, fullArenaHdrCore] using hpad_old) hlits_lt hent
  have hcl := hsp.1.core_ok
  have hnd' : FullArenaVarsNodup s' := fun r hr hngr => by
    rw [hrefs'] at hr
    dsimp only [fullArenaClauseRefs, fullArenaClauseGarb, fullArenaClauseLits] at hr hngr ⊢
    by_cases hrc : r = cref
    · subst r; exact hnd_cref
    · have hr_wf := hw.arena.refs_wf r hr; have hdisj := (Nat.lt_or_gt_of_ne hrc).elim
        (fun h => Or.inl (hw.arena.disjoint hr href h))
        (fun h => Or.inr (hw.arena.disjoint href hr h))
      have hbd1 : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
        have := hcl.arena_len_arr; have := hcl.arena_len_le; omega
      have hsz_c : fullArenaClauseSize s cref = fullArenaClauseSizeCore s.core cref := rfl
      have hout' : ∀ p, r ≤ p → p < r + 3 + fullArenaClauseSizeCore s.core r →
          arena'[p]? = s.core.arena[p]? := fun p _ _ =>
        hdisj.elim (fun _ => hout p (Or.inl (by omega))) (fun _ => hout p (Or.inr (by omega)))
      have hszr : fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := by
        unfold fullArenaClauseSizeCore; dsimp only [s']; rw [hout' (r + 2) (by omega) (by omega)]
      have hgbr : fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := by
        unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [s']
        rw [hout' r (by omega) (by omega)]
      have hlitsr := fullArenaClauseLitsCore_eq_of_hold hbd1
        (by rw [hal', ← hcl.arena_len_arr]; exact hbd1)
        hszr fun j hj => hout' (r + 3 + j) (by omega) (by omega)
      rw [hgbr] at hngr; rw [hlitsr]; exact hsp.2.2.2.1 r hr hngr
  exact ⟨⟨hlen', hw', hsp.2.2.1, hnd', ⟨fun i hi => by
    dsimp only [s']; rw [hrefs']; exact hsp.2.2.2.2.1.1 i hi, hsp.2.2.2.2.1.2⟩,
    hsp.2.2.2.2.2⟩, hgb', hrefs', hnxt'⟩

private theorem fv_len_core_inc {c : FullCfg} {k : FullCoreState} (hc : k.LengthsOk c)
    (inc' : BitVec 64) : ({ k with inconsistent := inc' } : FullCoreState).LengthsOk c :=
  ⟨hc.1, hc.2, hc.3, hc.4, hc.5, hc.6, hc.7, hc.8, hc.9, hc.10, hc.11, hc.12, hc.13, hc.14,
   hc.15, hc.16, hc.17, hc.18, hc.19, hc.20, hc.21, hc.22, hc.23, hc.24, hc.25⟩
private theorem fv_len_arena_ag {c : FullCfg} {s : FullState} (h : s.LengthsOk c)
    {ar' : List (BitVec 32)} {ag' : BitVec 64} (har : ar'.length = c.arena_cap) :
    ({ s with core := { s.core with arena := ar', arena_garbage := ag' } } :
      FullState).LengthsOk c :=
  let hc := h.core_ok
  ⟨⟨hc.1, hc.2, hc.3, hc.4, hc.5, hc.6, hc.7, hc.8, hc.9, hc.10, hc.11, hc.12, hc.13, hc.14,
    hc.15, har, hc.17, hc.18, hc.19, hc.20, hc.21, hc.22, hc.23, hc.24, hc.25⟩, h.scratch_ok⟩
private theorem fv_len_arena {c : FullCfg} {s : FullState} (h : s.LengthsOk c)
    {ar' : List (BitVec 32)} (har : ar'.length = c.arena_cap) :
    ({ s with core := { s.core with arena := ar' } } : FullState).LengthsOk c :=
  fv_len_arena_ag h (ag' := s.core.arena_garbage) har
private theorem fv_len_vivcnt {c : FullCfg} {sc : FullScratch} (hs : sc.LengthsOk c)
    (v : BitVec 64) : ({ sc with viv_cnt := v } : FullScratch).LengthsOk c :=
  ⟨hs.1, hs.2, hs.3, hs.4, hs.5, hs.6, hs.7, hs.8, hs.9, hs.10, hs.11, hs.12, hs.13, hs.14,
   hs.15, hs.16, hs.17, hs.18, hs.19, hs.20, hs.21, hs.22, hs.23, hs.24⟩

theorem bv32_ge3_of_ne (x : BitVec 32) (h0 : x ≠ 0#32) (h1 : x ≠ 1#32) (h2 : x ≠ 2#32) :
    3 ≤ x.toNat := by
  have ha : x.toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq h)
  have hb : x.toNat ≠ 1 := fun h => h1 (BitVec.eq_of_toNat_eq h)
  have hc : x.toNat ≠ 2 := fun h => h2 (BitVec.eq_of_toNat_eq h); omega

theorem take_entails_1 {F : CNF Nat} {xs : List (BitVec 32)} {n : Nat} (h : n = 1)
    (hl : 1 ≤ xs.length) (he : F.EntailsClause (cnfClause ((xs.take n).map BitVec.toNat))) :
    F.EntailsClause (cnfClause [(xs[0]'(by omega)).toNat]) := by
  subst h; cases xs with | nil => simp at hl | cons _ _ => exact he
theorem take_entails_2 {F : CNF Nat} {xs : List (BitVec 32)} {n : Nat} (h : n = 2)
    (hl : 2 ≤ xs.length) (he : F.EntailsClause (cnfClause ((xs.take n).map BitVec.toNat))) :
    F.EntailsClause (cnfClause [(xs[0]'(by omega)).toNat, (xs[1]'(by omega)).toNat]) := by
  subst h; cases xs with | nil => simp at hl | cons _ tl =>
    cases tl with | nil => simp at hl | cons _ _ => exact he
theorem range_entails_1 {F : CNF Nat} {ar : List (BitVec 32)} {off n : Nat} (h : n = 1)
    (hb : off < ar.length) (he : F.EntailsClause
      (cnfClause ((List.range n).map fun t => (ar[off + t]?.getD 0#32).toNat))) :
    F.EntailsClause (cnfClause [(ar[off]'hb).toNat]) := by
  subst h; simpa [List.getElem?_eq_getElem hb] using he
theorem range_entails_2 {F : CNF Nat} {ar : List (BitVec 32)} {off n : Nat} (h : n = 2)
    (hb : off + 1 < ar.length) (he : F.EntailsClause
      (cnfClause ((List.range n).map fun t => (ar[off + t]?.getD 0#32).toNat))) :
    F.EntailsClause (cnfClause [(ar[off]'(by omega)).toNat, (ar[off + 1]'hb).toNat]) := by
  subst h; simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil, List.cons_append, Nat.add_zero] at he
  rwa [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem hb, Option.getD_some,
    Option.getD_some] at he

theorem ws2_lt_cv {s s3 sg : FullState} {j n : Nat} (hj : j < n)
    (hlt : ∀ k < n, (s.scratch.work_stk2[k]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hws : s3.scratch.work_stk2 = s.scratch.work_stk2) (hcv3 : s3.core.cur_vars = s.core.cur_vars)
    (hcvg : sg.core.cur_vars = s3.core.cur_vars) (hbd : j < s3.scratch.work_stk2.length) :
    (s3.scratch.work_stk2[j]'hbd).toNat < 2 * sg.core.cur_vars := by
  have h := hlt j hj
  rwa [← hws, List.getElem?_eq_getElem hbd, Option.getD_some, ← hcv3, ← hcvg] at h

private theorem watchLayout_of_sparse {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hsp : FullSparseInv c F0 s) : WatchStackLayout s.core := by
  obtain ⟨_, hw⟩ := hsp.1.witness; have := hw.watches
  unfold ModeWatchesInv at this; rw [hsp.2.2.2.2] at this
  exact (by simpa using this : WatchesInv _ s.core).layout

theorem fullMem_eq_of_arena_eq {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {a1 a2 : List (BitVec 32)} (heq : a1 = a2)
    (hm : (FullMem c { s with core := { s.core with arena := a1 } } ⋆ R) m) :
    (FullMem c { s with core := { s.core with arena := a2 } } ⋆ R) m := by subst heq; exact hm
theorem fullMem_eq_of_arena_ag_eq {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} {a1 a2 : List (BitVec 32)} {ag : BitVec 64} (heq : a1 = a2)
    (hm : (FullMem c { s with core := { s.core with arena := a1, arena_garbage := ag } } ⋆ R) m) :
    (FullMem c { s with core := { s.core with arena := a2, arena_garbage := ag } } ⋆ R) m := by
  subst heq; exact hm

private theorem fv_witness_with_inc {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hu : (cnfOfClauses F_cur).Unsat) :
    FullWitnessInv c F0 F_cur { k with inconsistent := 1#64 } :=
  { hw with
    inconsistent_sound := fun _ => hu
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }

theorem commit_vivcnt_pack {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} (hsp : FullSparseInvW c F0 F_cur s)
    (hm : (FullMem c { s with scratch :=
      { s.scratch with viv_cnt := s.scratch.viv_cnt + 1#64 } } ⋆ R) m) :
    ∃ s1 : FullState, s1.core = s.core ∧ s1.scratch.work_stk2 = s.scratch.work_stk2 ∧
      FullSparseInvW c F0 F_cur s1 ∧ (FullMem c s1 ⋆ R) m :=
  ⟨{ s with scratch := { s.scratch with viv_cnt := s.scratch.viv_cnt + 1#64 } }, rfl, rfl,
    ⟨⟨hsp.1.core_ok, fv_len_vivcnt hsp.1.scratch_ok _⟩, hsp.2.1, hsp.2.2.1, hsp.2.2.2.1,
      hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩, hm⟩

theorem commit_zero_pack {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {m : Mem 64} {cref : Nat}
    (hsp : FullSparseInvW c F0 F_cur s) (hl0 : s.core.cur_level = 0)
    (hu : (cnfOfClauses F_cur).Unsat) (hQ : VivQ c F0 F_cur s R Q cref false)
    (hm : (FullMem c { { s with scratch := { s.scratch with viv_cnt := s.scratch.viv_cnt + 1#64 } }
      with core := { s.core with inconsistent := 1#64 } } ⋆ R) m) : Q (20#64, ()) m :=
  let s' : FullState := { { s with scratch := { s.scratch with viv_cnt := s.scratch.viv_cnt +
    1#64 } } with core := { s.core with inconsistent := 1#64 } }
  have hsp' : FullSparseInvW c F0 F_cur s' :=
    ⟨⟨fv_len_core_inc hsp.1.core_ok 1#64, fv_len_vivcnt hsp.1.scratch_ok _⟩,
      fv_witness_with_inc hsp.2.1 hu, hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩
  hQ 20#64 s' m hsp' hl0 rfl rfl rfl rfl rfl (Or.inr (Or.inr rfl))
    (fun _ => hsp.2.1.ext_sound.2 hu) (fun h => by cases h) hm

theorem simplify_zero_pack {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s2 : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {m : Mem 64} {cref : Nat}
    {ar3 : List (BitVec 32)} (hsp2 : FullSparseInvW c F0 F_cur s2)
    (har_eq : ar3 = s2.core.arena) (hu : (cnfOfClauses F_cur).Unsat) (hm2 : VivMetaEq s s2)
    (href2 : fullArenaClauseRefs s2 = fullArenaClauseRefs s)
    (hQ : VivQ c F0 F_cur s R Q cref true)
    (hm : (FullMem c { s2 with core :=
      { s2.core with arena := ar3, inconsistent := 1#64 } } ⋆ R) m) : Q (20#64, ()) m :=
  let s' : FullState := { s2 with core := { s2.core with inconsistent := 1#64 } }
  have hsp' : FullSparseInvW c F0 F_cur s' :=
    ⟨⟨fv_len_core_inc hsp2.1.core_ok 1#64, hsp2.1.scratch_ok⟩,
      fv_witness_with_inc hsp2.2.1 hu, hsp2.2.2.1, hsp2.2.2.2.1, hsp2.2.2.2.2.1, hsp2.2.2.2.2.2⟩
  hQ 20#64 s' m hsp' hm2.2.2.1 hm2.2.1 hm2.1 hm2.2.2.2.1 hm2.2.2.2.2 href2 (Or.inr (Or.inr rfl))
    (fun _ => hsp2.2.1.ext_sound.2 hu) (fun _ h => by cases h) (by simpa only [har_eq] using hm)

theorem ar_get_eq_getD {ar : List (BitVec 32)} {p q : Nat} (heq : p = q)
    (hlt : p < ar.length) : ar[p]'hlt = ar[q]?.getD 0#32 := by
  have hg : ar[p]? = ar[q]? := by rw [heq]
  rw [List.getElem?_eq_getElem hlt] at hg; rw [← hg, Option.getD_some]

theorem cref_hdr_facts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInv c F0 s) (hw : FullWitnessInv c F0 F_cur s.core)
    {cref : BitVec 32} (href : cref.toNat ∈ fullArenaClauseRefs s)
    (hng : fullArenaClauseGarb s cref.toNat = false) :
    cref.toNat < s.core.arena.length ∧ (cref.toNat + 2) % 18446744073709551616 = cref.toNat + 2 ∧
    (cref.setWidth 64).toNat = cref.toNat ∧ (cref.setWidth 64 + 1#64).toNat = cref.toNat + 1 ∧
    (cref.setWidth 64 + 2#64).toNat = cref.toNat + 2 ∧
    (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3 ∧
    (cref.setWidth 64 + 4#64).toNat = cref.toNat + 4 ∧
    (s.core.arena[cref.toNat]?.getD 0#32 &&& 0x00080000#32) = 0#32 := by
  have hcl := hsp.1.lengths.core_ok; have hwf := hw.arena.refs_wf cref.toNat href
  have hcap := c.harena; unfold dimacsBound at hcap
  have hng' := hng; unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hng'
  refine ⟨by have := hcl.arena_len_arr; have := hcl.arena_len_le; omega,
    Nat.mod_eq_of_lt (by have := hcl.arena_len_le; omega),
    by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega, by simpa using hng'⟩

theorem simplify_compact_facts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s2 : FullState} (hsp2 : FullSparseInvW c F0 F_cur s2)
    (hl0 : s2.core.cur_level = 0) {cref nsz : Nat} (href : cref ∈ fullArenaClauseRefs s2)
    (hng : fullArenaClauseGarb s2 cref = false) (hnsz_lt : nsz < fullArenaClauseSize s2 cref)
    {ar3 : List (BitVec 32)} {idxs : List Nat} (har3_len : ar3.length = c.arena_cap)
    (hid_len : idxs.length = nsz)
    (hout3 : ∀ p, (p < cref + 3 ∨ cref + 3 + nsz ≤ p) → ar3[p]? = s2.core.arena[p]?)
    (hid_lt : ∀ q ∈ idxs, q < fullArenaClauseSize s2 cref)
    (hsub3 : ∀ t < nsz, ar3[cref + 3 + t]? = s2.core.arena[cref + 3 + idxs[t]?.getD 0]?)
    (hcov3 : ∀ j < fullArenaClauseSize s2 cref,
      s2.core.vals[(s2.core.arena[cref + 3 + j]?.getD 0#32).toNat]?.getD 0#8 = 0#8 →
      ∃ t < nsz, ar3[cref + 3 + t]? = s2.core.arena[cref + 3 + j]?)
    (hno1 : ∀ j < fullArenaClauseSize s2 cref,
      s2.core.vals[(s2.core.arena[cref + 3 + j]?.getD 0#32).toNat]?.getD 0#8 ≠ 1#8) :
    (∀ t < nsz, (ar3[cref + 3 + t]?.getD 0#32).toNat < 2 * s2.core.cur_vars) ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((List.range nsz).map fun t => (ar3[cref + 3 + t]?.getD 0#32).toNat)) ∧
    (0 < nsz → let s_upd : FullState := { s2 with core := { s2.core with arena := ar3 } }
      s_upd.LengthsOk c ∧ FullWitnessInv c F0 F_cur s_upd.core ∧
      fullArenaClauseRefs s_upd = fullArenaClauseRefs s2 ∧ ∀ r ∈ fullArenaClauseRefs s2,
        fullArenaNextOff ar3 s2.core.arena_len r =
          fullArenaNextOff s2.core.arena s2.core.arena_len r) ∧
    (∀ (st : FullState), st.core.arena = ar3 → st.core.arena_len = s2.core.arena_len →
      ∀ r ∈ fullArenaClauseRefs s2, r ≠ cref → fullArenaClauseGarb st r = false →
        ((fullArenaClauseLits st r).map (· / 2)).Nodup) := by
  have hw2 := hsp2.2.1; have hcl := hsp2.1.core_ok; have hcref_wf := hw2.arena.refs_wf cref href
  have har_len := hcl.arena_len_arr; have halen_le := hcl.arena_len_le
  have hsz_def : fullArenaClauseSize s2 cref = fullArenaClauseSizeCore s2.core cref := rfl
  have hbd0 : cref + 3 + fullArenaClauseSizeCore s2.core cref ≤ s2.core.arena.length := by omega
  have hlit_lt : ∀ j < fullArenaClauseSize s2 cref,
      (s2.core.arena[cref + 3 + j]?.getD 0#32).toNat < 2 * s2.core.cur_vars := fun j hj => by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact hw2.arena.lits_lt cref href hng _
      ((mem_fullArenaClauseLitsCore_iff hbd0).mpr ⟨j, by omega, rfl⟩)
  have hnew_lt : ∀ t < nsz, (ar3[cref + 3 + t]?.getD 0#32).toNat < 2 * s2.core.cur_vars := by
    intro t ht; rw [hsub3 t ht, show idxs[t]?.getD 0 = idxs[t]'(by omega) by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]]
    exact hlit_lt _ (hid_lt _ (by simp))
  have hent_new : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((List.range nsz).map fun t => (ar3[cref + 3 + t]?.getD 0#32).toNat)) := by
    refine entails_filter_level0 hw2 hl0 (hw2.arena.entails cref href hng) fun l hl => ?_
    obtain ⟨j, hj, hget⟩ := (mem_fullArenaClauseLitsCore_iff hbd0).mp hl
    have hgetD : (s2.core.arena[cref + 3 + j]?.getD 0#32).toNat = l := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hget
    have hl_lt : l < 2 * s2.core.cur_vars := hgetD ▸ hlit_lt j hj
    rcases hw2.vals_domain l hl_lt with h0 | h1 | hff
    · left; obtain ⟨t, ht, hteq⟩ := hcov3 j hj (by rwa [hgetD])
      exact List.mem_map.mpr ⟨t, List.mem_range.mpr ht, by rw [hteq]; exact hgetD⟩
    · exact absurd (hgetD.symm ▸ h1) (hno1 j hj)
    · exact Or.inr ⟨hl_lt, hff⟩
  refine ⟨hnew_lt, hent_new, fun _ => ?_, fun st hst_ar _ r hr hne hngr => ?_⟩
  · refine fullArena_updateLits_preserves_fullWitness hsp2.1 hw2 hl0 href har3_len
      (fun k hk => hout3 k (by omega)) (fun j hj => by
        by_cases hjn : j < nsz; · exact hnew_lt j hjn
        · rw [hout3 (cref + 3 + j) (Or.inr (by omega))]; exact hlit_lt j hj) ?_
    refine entails_of_mem_or_false hent_new fun l hl => Or.inl ?_
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hl; rw [List.mem_range] at ht
    have hsz_u : fullArenaClauseSizeCore { s2.core with arena := ar3 } cref =
        fullArenaClauseSize s2 cref := by
      unfold fullArenaClauseSizeCore fullArenaClauseSize
      rw [hout3 (cref + 2) (Or.inl (by omega))]; rfl
    have hbd_u : cref + 3 + fullArenaClauseSizeCore { s2.core with arena := ar3 } cref ≤
        ar3.length := by rw [hsz_u]; omega
    refine (mem_fullArenaClauseLitsCore_iff hbd_u).mpr ⟨t, by rw [hsz_u]; omega, ?_⟩
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  · have hr_wf := hw2.arena.refs_wf r hr; have hdisj := (Nat.lt_or_gt_of_ne hne).elim
      (fun h => Or.inl (hw2.arena.disjoint hr href h))
      (fun h => Or.inr (hw2.arena.disjoint href hr h))
    have hhold : ∀ p, r ≤ p → p < r + 3 + fullArenaClauseSizeCore s2.core r →
        st.core.arena[p]? = s2.core.arena[p]? := fun p _ _ => by
      rw [hst_ar]
      exact hdisj.elim (fun _ => hout3 p (Or.inl (by omega)))
        (fun _ => hout3 p (Or.inr (by omega)))
    have hszr : fullArenaClauseSizeCore st.core r = fullArenaClauseSizeCore s2.core r := by
      unfold fullArenaClauseSizeCore; rw [hhold (r + 2) (by omega) (by omega)]
    have hgbr : fullArenaClauseGarbCore st.core r = fullArenaClauseGarbCore s2.core r := by
      unfold fullArenaClauseGarbCore fullArenaHdrCore; rw [hhold r (by omega) (by omega)]
    have hlitsr := fullArenaClauseLitsCore_eq_of_hold (by omega) (by rw [hst_ar]; omega) hszr
      fun j hj => hhold (r + 3 + j) (by omega) (by omega)
    dsimp only [fullArenaClauseGarb, fullArenaClauseLits] at hngr ⊢
    rw [hgbr] at hngr; rw [hlitsr]; exact hsp2.2.2.2.1 r hr hngr

theorem simplify_shrk_sparseInv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s2 : FullState} (hsp2 : FullSparseInvW c F0 F_cur s2)
    (hl0 : s2.core.cur_level = 0) {cref nsz : Nat} (href : cref ∈ fullArenaClauseRefs s2)
    (hng : fullArenaClauseGarb s2 cref = false) (hnsz3 : 3 ≤ nsz)
    (hnsz_lt : nsz < fullArenaClauseSize s2 cref) {ar3 ar_f : List (BitVec 32)} {idxs : List Nat}
    (harf_len : ar_f.length = c.arena_cap) (hid_len : idxs.length = nsz)
    (hid_pw : idxs.Pairwise (· < ·)) (hid_lt : ∀ q ∈ idxs, q < fullArenaClauseSize s2 cref)
    (hsub3 : ∀ t < nsz, ar3[cref + 3 + t]? = s2.core.arena[cref + 3 + idxs[t]?.getD 0]?)
    (hnew_lt : ∀ t < nsz, (ar3[cref + 3 + t]?.getD 0#32).toNat < 2 * s2.core.cur_vars)
    (hent_new : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((List.range nsz).map fun t => (ar3[cref + 3 + t]?.getD 0#32).toNat)))
    (hout_f : ∀ k, (k < cref ∨ cref + 3 + fullArenaClauseSize s2 cref ≤ k) →
      ar_f[k]? = s2.core.arena[k]?)
    (hng_f : (ar_f[cref]?.getD 0#32 &&& 0x00080000#32) = 0#32)
    (hsh_f : (ar_f[cref]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32)
    (hsz_f : (ar_f[cref + 2]?.getD 0#32).toNat = nsz)
    (hpay_f : ∀ t < nsz, ar_f[cref + 3 + t]? = ar3[cref + 3 + t]?)
    (hpad_f : ShrkPad ar_f s2.core.arena cref (fullArenaClauseSize s2 cref) nsz) :
    let s_f : FullState := { s2 with core := { s2.core with arena := ar_f } }
    FullSparseInvW c F0 F_cur s_f ∧ fullArenaClauseGarb s_f cref = false ∧ VivArenaEq s2 s_f := by
  have hw2 := hsp2.2.1; have hcl := hsp2.1.core_ok; have hcref_wf := hw2.arena.refs_wf cref href
  have har_len := hcl.arena_len_arr; have halen_le := hcl.arena_len_le
  have hsz_def : fullArenaClauseSize s2 cref = fullArenaClauseSizeCore s2.core cref := rfl
  have hsz_core_f : fullArenaClauseSizeCore { s2.core with arena := ar_f } cref = nsz := hsz_f
  have hbd_f : cref + 3 + fullArenaClauseSizeCore { s2.core with arena := ar_f } cref ≤
      ar_f.length := by rw [hsz_core_f]; omega
  have hbd0 : cref + 3 + fullArenaClauseSizeCore s2.core cref ≤ s2.core.arena.length := by omega
  have hnd_f : ((fullArenaClauseLitsCore { s2.core with arena := ar_f } cref).map
      (· / 2)).Nodup := by
    refine nodup_of_strict_subseq (hsp2.2.2.2.1 cref href hng) idxs
      (by rw [fullArenaClauseLitsCore_length hbd_f, hsz_core_f]; exact hid_len) hid_pw
      (fun q hq => by rw [fullArenaClauseLitsCore_length hbd0]; exact hid_lt q hq) fun t ht => ?_
    rw [fullArenaClauseLitsCore_length hbd_f, hsz_core_f] at ht
    have hq_lt : idxs[t]?.getD 0 < fullArenaClauseSizeCore s2.core cref := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hid_lt _ (by simp)
    rw [fullArenaClauseLitsCore_getElem hbd_f (by omega),
      fullArenaClauseLitsCore_getElem hbd0 hq_lt]
    have heq_t := (hpay_f t ht).trans (hsub3 t ht)
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at heq_t
    exact congrArg BitVec.toNat (Option.some.inj heq_t)
  have hent_f : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullArenaClauseLitsCore { s2.core with arena := ar_f } cref)) := by
    have heq_l : fullArenaClauseLitsCore { s2.core with arena := ar_f } cref =
        (List.range nsz).map fun t => (ar3[cref + 3 + t]?.getD 0#32).toNat := by
      refine List.ext_getElem (by rw [fullArenaClauseLitsCore_length hbd_f, hsz_core_f,
          List.length_map, List.length_range]) fun t ht1 _ => ?_
      rw [fullArenaClauseLitsCore_length hbd_f, hsz_core_f] at ht1
      rw [fullArenaClauseLitsCore_getElem hbd_f (by omega), List.getElem_map, List.getElem_range,
        ← hpay_f t ht1, List.getElem?_eq_getElem (by omega), Option.getD_some]
    rwa [heq_l]
  exact fullSparseInv_of_inPlaceShrink hsp2 hl0 href hng hnsz3 hnsz_lt harf_len hout_f hng_f
    hsh_f hsz_f hpad_f (fun j hj => by rw [hpay_f j hj]; exact hnew_lt j hj) hnd_f hent_f

theorem commit_shrk_sparseInv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s3 : FullState} (hsp3 : FullSparseInvW c F0 F_cur s3)
    (hl0 : s3.core.cur_level = 0) {cref olen : Nat} (href : cref ∈ fullArenaClauseRefs s3)
    (hng : fullArenaClauseGarb s3 cref = false) (holen3 : 3 ≤ olen)
    (holen_lt : olen < fullArenaClauseSize s3 cref) (holen_le : olen ≤ s3.scratch.work_stk2.length)
    (hout_lt : ∀ j < olen, (s3.scratch.work_stk2[j]?.getD 0#32).toNat < 2 * s3.core.cur_vars)
    (hout_nd : (((s3.scratch.work_stk2.take olen).map BitVec.toNat).map (· / 2)).Nodup)
    (hout_ent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s3.scratch.work_stk2.take olen).map BitVec.toNat)))
    {nhdr2 : BitVec 32} {ar_p : List (BitVec 32)} {ni1 nr1 : BitVec 64}
    (harp_len : ar_p.length = c.arena_cap)
    (hng2 : (nhdr2 &&& 0x00080000#32) = 0#32) (hsh2 : (nhdr2 &&& 0x00800000#32) ≠ 0#32)
    (hout_p : ∀ k, (k < cref ∨ cref + 3 + fullArenaClauseSize s3 cref ≤ k) →
      ar_p[k]? = s3.core.arena[k]?)
    (hsz_p : (ar_p[cref + 2]?.getD 0#32).toNat = olen)
    (hpay_p : ∀ j < olen, ar_p[cref + 3 + j]? = s3.scratch.work_stk2[j]?)
    (hpad_p : ShrkPad ar_p s3.core.arena cref (fullArenaClauseSize s3 cref) olen) :
    let ar_f := ar_p.set cref nhdr2
    let s_f : FullState :=
      { s3 with core := { s3.core with arena := ar_f, num_irred := ni1, num_redundant := nr1 } }
    FullSparseInvW c F0 F_cur s_f ∧ VivArenaEq s3 s_f := by
  intro ar_f s_f
  have hw3 := hsp3.2.1; have hcl := hsp3.1.core_ok; have hcref_wf := hw3.arena.refs_wf cref href
  have halen_le := hcl.arena_len_le
  have hsz_def : fullArenaClauseSize s3 cref = fullArenaClauseSizeCore s3.core cref := rfl
  have harf_len : ar_f.length = c.arena_cap := by simp [ar_f, harp_len]
  have hsz_f : (ar_f[cref + 2]?.getD 0#32).toNat = olen := by
    dsimp only [ar_f]; rw [List.getElem?_set_ne (by omega)]; exact hsz_p
  have hpay_f : ∀ j < olen, ar_f[cref + 3 + j]? = s3.scratch.work_stk2[j]? := fun j hj => by
    dsimp only [ar_f]; rw [List.getElem?_set_ne (by omega)]; exact hpay_p j hj
  have hlits_eq := fullArenaClauseLitsCore_eq_map_take (k := { s3.core with arena := ar_f }) hsz_f
    (by change cref + 3 + olen ≤ ar_f.length; omega) holen_le hpay_f
  have hpad_f : ShrkPad ar_f s3.core.arena cref (fullArenaClauseSize s3 cref) olen := by
    unfold ShrkPad at hpad_p ⊢; split
    · rename_i h0; rw [ite_eq_left h0] at hpad_p
      exact ⟨fun k hk1 hk2 => by
        dsimp only [ar_f]; rw [List.getElem?_set_ne (by omega)]; exact hpad_p.1 k hk1 hk2,
        by dsimp only [ar_f]; rw [List.getElem?_set_ne (by omega)]; exact hpad_p.2⟩
    · rename_i hne; rw [ite_eq_right hne] at hpad_p
      exact fun k hk1 hk2 => by
        dsimp only [ar_f]; rw [List.getElem?_set_ne (by omega)]; exact hpad_p k hk1 hk2
  obtain ⟨hsp_f, _, ha_f⟩ := fullSparseInv_of_inPlaceShrink hsp3 hl0 href hng holen3 holen_lt
    harf_len
    (fun k hk => by dsimp only [ar_f]; rw [List.getElem?_set_ne (by omega)]; exact hout_p k hk)
    (by dsimp only [ar_f]; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hng2)
    (by dsimp only [ar_f]; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hsh2)
    hsz_f hpad_f (fun j hj => by rw [hpay_f j hj]; exact hout_lt j hj)
    (by rw [hlits_eq]; exact hout_nd) (by rw [hlits_eq]; exact hout_ent)
  exact ⟨hsp_f, ha_f⟩

theorem fullArena_markGarb_pack {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {cref : Nat} {hdr : BitVec 32} {ag : BitVec 64}
    (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core) (hmc : FullLitMarksClear c s)
    (hext : FullExtScratchOk c s) (hdm : s.core.dense_mode = 0#64) (hl0 : s.core.cur_level = 0)
    (href : cref ∈ fullArenaClauseRefs s) (hhdr : fullArenaHdr s cref = hdr)
    (hnd_other : ∀ r ∈ fullArenaClauseRefs s, r ≠ cref → fullArenaClauseGarb s r = false →
      ((fullArenaClauseLits s r).map (· / 2)).Nodup)
    (hm : (FullMem c { s with core := { s.core with
      arena := s.core.arena.set cref (hdr ||| 0x00080000#32), arena_garbage := ag } } ⋆ R) m) :
    ∃ s_g : FullState,
      s_g.core.arena = s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32) ∧
      VivMetaEq s s_g ∧ s_g.scratch = s.scratch ∧ FullSparseInvW c F0 F_cur s_g ∧
      VivArenaEq s s_g ∧ (FullMem c s_g ⋆ R) m := by
  obtain ⟨hlen_g, hw_g, hrefs_g, hnd_g, hnxt_g⟩ :=
    fv_witness_markGarb_level0 hlen hw hl0 href ag hnd_other
  let s_g : FullState := { s with core := { s.core with
    arena := s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32), arena_garbage := ag } }
  exact ⟨s_g, rfl, ⟨rfl, rfl, hl0, rfl, rfl⟩, rfl, ⟨hlen_g, hw_g, hmc, hnd_g,
    ⟨fun i hi => by dsimp only [FullLastLearnedWf, s_g]; rw [hrefs_g]; exact hext.1 i hi, hext.2⟩,
    hdm⟩, ⟨hrefs_g, hnxt_g⟩, fullMem_eq_of_arena_ag_eq
      (congrArg (fun x => s.core.arena.set cref (x ||| 0x00080000#32)) hhdr.symm) hm⟩

theorem ar_set_sz_props {ar0 ar_orig : List (BitVec 32)} {cref old_sz nsz : Nat}
    {nsz_bv : BitVec 32} {p2 p1 : Nat} (hlen : ar0.length = ar_orig.length) (hnsz3 : 3 ≤ nsz)
    (hlt : nsz < old_sz) (hbd : cref + 3 + old_sz ≤ ar0.length) (hnsz_eq : nsz_bv.toNat = nsz)
    (hp2 : p2 = cref + 2) (hp1 : p1 = cref + 1)
    (hout : ∀ p, (p < cref + 3 ∨ cref + 3 + nsz ≤ p) → ar0[p]? = ar_orig[p]?) :
    let ar_sz := (ar0.set p2 nsz_bv).set p1 2#32
    ar_sz.length = ar_orig.length ∧ (∀ k, (k < cref ∨ cref + 3 + old_sz ≤ k) →
      ar_sz[k]? = ar_orig[k]?) ∧ (ar_sz[cref + 2]?.getD 0#32).toNat = nsz ∧
    (∀ t < nsz, ar_sz[cref + 3 + t]? = ar0[cref + 3 + t]?) ∧
    (∀ k, cref + 3 + nsz ≤ k → k < cref + 3 + old_sz → ar_sz[k]? = ar_orig[k]?) ∧
    ar_sz[cref]? = ar_orig[cref]? := by
  intro ar_sz; subst hp2 hp1
  refine ⟨by simp [ar_sz, hlen], fun k hk => ?_, ?_, fun t ht => ?_, fun k hk1 _ => ?_, ?_⟩ <;>
    dsimp only [ar_sz]
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hout k (by omega)
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some,
      hnsz_eq]
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hout k (Or.inr hk1)
  rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  exact hout cref (Or.inl (by omega))

theorem unwatch2_state_pack {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s_in : FullState} {R : Mem 64 → Prop} {m : Mem 64} {cref : Nat} {old_sz hdr : BitVec 32}
    (hsp : FullSparseInv c F0 s_in) (hw : FullWitnessInv c F0 F_cur s_in.core)
    (hm : (FullMem c s_in ⋆ R) m) (hng : fullArenaClauseGarb s cref = false)
    (hsz_eq : fullArenaClauseSize s cref = old_sz.toNat) (hhdr_eq : hdr = fullArenaHdr s cref)
    (hs_ar : s_in.core.arena = s.core.arena) (hs_v : s_in.core.vals = s.core.vals)
    (hs_cv : s_in.core.cur_vars = s.core.cur_vars) (hs_al : s_in.core.arena_len = s.core.arena_len)
    (hs_l0 : s_in.core.cur_level = 0) (hs_pr : s_in.core.probing = s.core.probing)
    (hs_fu : s_in.core.fuel = s.core.fuel) (hws2 : s_in.scratch.work_stk2 = s.scratch.work_stk2) :
    ∃ s2 : FullState, s2.core.arena = s.core.arena ∧ s2.core.vals = s.core.vals ∧
      s2.scratch.work_stk2 = s.scratch.work_stk2 ∧ VivMetaEq s s2 ∧
      fullArenaClauseRefs s2 = fullArenaClauseRefs s ∧ fullArenaClauseGarb s2 cref = false ∧
      fullArenaClauseSize s2 cref = old_sz.toNat ∧ fullArenaHdr s2 cref = hdr ∧
      FullSparseInvW c F0 F_cur s2 ∧ (FullMem c s2 ⋆ R) m :=
  ⟨s_in, hs_ar, hs_v, hws2, ⟨hs_al, hs_cv, hs_l0, hs_pr, hs_fu⟩,
    by unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [hs_ar, hs_al],
    by unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore; rw [hs_ar]; exact hng,
    by unfold fullArenaClauseSize fullArenaClauseSizeCore; rw [hs_ar]; exact hsz_eq,
    by unfold fullArenaHdr fullArenaHdrCore; rw [hs_ar]; exact hhdr_eq.symm,
    ⟨hsp.1.lengths, hw, hsp.2.1, hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2⟩, hm⟩

private theorem arena_same_refs_nxt {s s_g s4 : FullState}
    (har4 : s4.core.arena = s_g.core.arena) (halen4 : s4.core.arena_len = s_g.core.arena_len)
    (ha_g : VivArenaEq s s_g) : VivArenaEq s s4 :=
  ⟨(show fullArenaClauseRefs s4 = fullArenaClauseRefs s_g by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har4, halen4]).trans ha_g.1,
   fun q hq => by rw [har4]; exact ha_g.2 q hq⟩

theorem addUnit_call_wp (Γ : Env) (hAddUnit : HypAddUnit Γ)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s s_g : FullState}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {lit : Val i32} {m_g : Mem 64} {J : Cont [i64]} (hsp_g : FullSparseInvW c F0 F_cur s_g)
    (hm_g : VivMetaEq s s_g) (ha_g : VivArenaEq s s_g)
    (hlit_lt : lit.toNat < 2 * s_g.core.cur_vars)
    (hlit_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]))
    (hmem_g : (FullMem c s_g ⋆ R) m_g)
    (hJ1 : ∀ s' m', FullSparseInvW c F0 F_cur s' → VivMetaEq s s' → VivArenaEq s s' →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (Expr.jump J (Arg.imm 1, ())) m')
    (hJ20 : ∀ s' m', FullSparseInvW c F0 F_cur s' → VivMetaEq s s' → VivArenaEq s s' →
      F0.Unsat → (FullMem c s' ⋆ R) m' → wp Γ Q X (Expr.jump J (Arg.imm 20, ())) m') :
    wp Γ Q X (Expr.call "full_add_unit" (as := [i64, i32]) (bs := [.bool])
      (Arg.var c.hdr, Arg.var lit, ()) fun p => Expr.jnz (Arg.var p.fst)
        (Expr.jump J (Arg.imm 1, ())) (Expr.jump J (Arg.imm 20, ()))) m_g := by
  c0_call hAddUnit
  refine ⟨c, F0, F_cur, s_g, R, rfl, hsp_g, hlit_lt, hlit_ent, hmem_g,
    fun ok s4 m4 hsp4 hl4 har4 halen4 hcv4 hpr4 _ hfu4 hok_f hm4 => ?_⟩
  have hmv4 : VivMetaEq s s4 := ⟨halen4.trans hm_g.1, hcv4.trans hm_g.2.1, hl4,
    hpr4.trans hm_g.2.2.2.1, hfu4.trans hm_g.2.2.2.2⟩
  have ha4 := arena_same_refs_nxt har4 halen4 ha_g
  fv_steps
  · exact hJ1 s4 m4 hsp4 hmv4 ha4 hm4
  · exact hJ20 s4 m4 hsp4 hmv4 ha4 (hok_f hc) hm4

theorem addBin_ok_post {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s_g s4 : FullState} (hlen4 : s4.LengthsOk c) (hw4 : FullWitnessInv c F0 F_cur s4.core)
    (hmc4 : FullLitMarksClear c s4) (hext4 : FullExtScratchOk c s4)
    (hdm4 : s4.core.dense_mode = 0#64) (hl4 : s4.core.cur_level = 0)
    (har4 : s4.core.arena = s_g.core.arena) (halen4 : s4.core.arena_len = s_g.core.arena_len)
    (hnd_g : FullArenaVarsNodup s_g) (ha_g : VivArenaEq s s_g) :
    FullSparseInvW c F0 F_cur s4 ∧ s4.core.cur_level = 0 ∧ VivArenaEq s s4 := by
  have hnd4 : FullArenaVarsNodup s4 := fun r hr hngr => by
    unfold fullArenaClauseRefs fullArenaClauseRefsCore at hr
    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hngr
    unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore
    rw [har4, halen4] at hr; rw [har4] at hngr ⊢; exact hnd_g r hr hngr
  exact ⟨⟨hlen4, hw4, hmc4, hnd4, hext4, hdm4⟩, hl4, arena_same_refs_nxt har4 halen4 ha_g⟩

theorem markGarb_bin_pack {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s2 s4 : FullState} {R : Mem 64 → Prop} {m : Mem 64} {cref : Nat} {hdr : BitVec 32}
    {ag : BitVec 64} (hlen4 : s4.LengthsOk c) (hw4 : FullWitnessInv c F0 F_cur s4.core)
    (hmc4 : FullLitMarksClear c s4) (hext4 : FullExtScratchOk c s4)
    (hdm4 : s4.core.dense_mode = 0#64) (hl4 : s4.core.cur_level = 0)
    (href : cref ∈ fullArenaClauseRefs s) (hs2_ref : fullArenaClauseRefs s2 = fullArenaClauseRefs s)
    (hs2_al : s2.core.arena_len = s.core.arena_len) (har4 : s4.core.arena = s2.core.arena)
    (halen4 : s4.core.arena_len = s2.core.arena_len) (hhdr4 : fullArenaHdr s4 cref = hdr)
    (hnd_other : ∀ r ∈ fullArenaClauseRefs s4, r ≠ cref → fullArenaClauseGarb s4 r = false →
      ((fullArenaClauseLits s4 r).map (· / 2)).Nodup)
    (hnxt_u : ∀ q ∈ fullArenaClauseRefs s2, fullArenaNextOff s2.core.arena s2.core.arena_len q =
      fullArenaNextOff s.core.arena s2.core.arena_len q)
    (hm : (FullMem c { s4 with core := { s4.core with
      arena := s4.core.arena.set cref (hdr ||| 0x00080000#32), arena_garbage := ag } } ⋆ R) m) :
    ∃ s5 : FullState, s5.core.arena_len = s.core.arena_len ∧
      s5.core.cur_vars = s4.core.cur_vars ∧ s5.core.probing = s4.core.probing ∧
      s5.core.fuel = s4.core.fuel ∧ FullSparseInvW c F0 F_cur s5 ∧ s5.core.cur_level = 0 ∧
      VivArenaEq s s5 ∧ (FullMem c s5 ⋆ R) m := by
  have href4 : fullArenaClauseRefs s4 = fullArenaClauseRefs s2 := by
    unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har4, halen4]
  obtain ⟨s5, _, hm5', _, hsp5, ha5, hm5⟩ := fullArena_markGarb_pack hlen4 hw4 hmc4 hext4 hdm4
    hl4 (href4 ▸ hs2_ref ▸ href) hhdr4 hnd_other hm
  exact ⟨s5, hm5'.1.trans (halen4.trans hs2_al), hm5'.2.1, hm5'.2.2.2.1, hm5'.2.2.2.2, hsp5,
    hm5'.2.2.1, ⟨ha5.1.trans (href4.trans hs2_ref), fun q hq => by
      have h1 := ha5.2 q (href4 ▸ hs2_ref ▸ hq); have h2 := hnxt_u q (hs2_ref ▸ hq)
      rw [halen4, hs2_al] at h1; rw [hs2_al] at h2; rw [har4] at h1; exact h1.trans h2⟩, hm5⟩

private theorem watch2_pre_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {blk cref : BitVec 32} (hsp : FullSparseInvW c F0 F_cur s) (hcref : cref ≠ 0xFFFFFFFF#32) :
    s.LengthsOk c ∧ WatchStackLayout s.core ∧
    ((2#32 : BitVec 32).toNat = 1 → (blk &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32) ∧
    ((2#32 : BitVec 32).toNat = 2 →
      (blk &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32 ∧ cref ≠ 0xFFFFFFFF#32) :=
  ⟨hsp.1, watchLayout_of_sparse (fv_sparseW_to_sparse hsp), fun h => absurd h (by decide),
    fun _ => ⟨(bv32_mask_lo31_props _).2, hcref⟩⟩

theorem ar_set_shrk_facts {ar_sz ar_orig : List (BitVec 32)}
    {cref old_sz nsz cap term : Nat} {nhdr : BitVec 32} (har_len : ar_sz.length = cap)
    (hsz_le : cref + 3 + old_sz ≤ cap) (hterm : term = cref + 3 + old_sz - 1)
    (hnz_lt : nsz < old_sz) (hnsz3 : 3 ≤ nsz) (hng : (nhdr &&& 0x00080000#32) = 0#32)
    (hsh0 : (nhdr &&& 0x00800000#32) = 0#32)
    (hsh_orig : (ar_orig[cref]?.getD 0#32 &&& 0x00800000#32) = (nhdr &&& 0x00800000#32))
    (hout : ∀ k, (k < cref ∨ cref + 3 + old_sz ≤ k) → ar_sz[k]? = ar_orig[k]?)
    (hsz : (ar_sz[cref + 2]?.getD 0#32).toNat = nsz)
    (hpad : ∀ k, cref + 3 + nsz ≤ k → k < cref + 3 + old_sz → ar_sz[k]? = ar_orig[k]?) :
    let ar1 := ar_sz.set cref (nhdr ||| 0x00800000#32); let ar2 := ar1.set term 0xFFFFFFFF#32
    ar2.length = cap ∧ (∀ k, (k < cref ∨ cref + 3 + old_sz ≤ k) → ar2[k]? = ar_orig[k]?) ∧
    (ar2[cref]?.getD 0#32 &&& 0x00080000#32) = 0#32 ∧
    (ar2[cref]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 ∧ (ar2[cref + 2]?.getD 0#32).toNat = nsz ∧
    ShrkPad ar2 ar_orig cref old_sz nsz := by
  intro ar1 ar2; subst hterm
  refine ⟨by simp [ar2, ar1, har_len], fun k hk => by
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hout k hk,
    by rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp [har_len]; omega),
        Option.getD_some, bv32_or_shrk_garb, hng],
    by rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp [har_len]; omega),
        Option.getD_some]; exact bv32_or_shrk_ne0 nhdr,
    by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hsz, ?_⟩
  unfold ShrkPad; rw [ite_eq_left (by rw [hsh_orig, hsh0])]
  exact ⟨fun k hk1 hk2 => by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                             exact hpad k hk1 (by omega),
    List.getElem?_set_self (by simp [ar1, har_len]; omega)⟩

abbrev fvOp {as bs : List Ty} (c : OpCode as bs) (args : Tup (Arg Val) as)
    (k : Tup Val bs → Expr Val Cont [i64]) : Expr Val Cont [i64] :=
  Expr.let_ (⟨c, args⟩ : Op Val bs) k

abbrev arBasePtr (pA : Val i64) (cref : Val i32) (k : Val i64 → Expr Val Cont [i64]) :=
  fvOp (OpCode.zext 32 64) (Arg.var cref, ()) fun p =>
  fvOp (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
  fvOp (OpCode.add i64) (Arg.var pA, Arg.var p.fst, ()) fun p => k p.fst

abbrev arOffPtr (pA : Val i64) (cref : Val i32) (off : BitVec 64)
    (k : Val i64 → Expr Val Cont [i64]) :=
  fvOp (OpCode.zext 32 64) (Arg.var cref, ()) fun p =>
  fvOp (OpCode.add i64) (Arg.var p.fst, Arg.imm off, ()) fun p =>
  fvOp (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
  fvOp (OpCode.add i64) (Arg.var pA, Arg.var p.fst, ()) fun p => k p.fst

abbrev arLitPtr (pA : Val i64) (cref idx : Val i32) (k : Val i64 → Expr Val Cont [i64]) :=
  fvOp (OpCode.zext 32 64) (Arg.var cref, ()) fun p =>
  fvOp (OpCode.add i64) (Arg.var p.fst, Arg.imm 3, ()) fun p =>
  fvOp (OpCode.zext 32 64) (Arg.var idx, ()) fun p1 =>
  fvOp (OpCode.add i64) (Arg.var p.fst, Arg.var p1.fst, ()) fun p =>
  fvOp (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
  fvOp (OpCode.add i64) (Arg.var pA, Arg.var p.fst, ()) fun p => k p.fst

abbrev addArenaGarbageExpr (h : Val i64) (old_sz : Val i32) (k : Expr Val Cont [i64]) :=
  fvOp (OpCode.add i64) (Arg.var h, Arg.imm 472, ()) fun p => Expr.load i64 (Arg.var p.fst) fun a =>
  fvOp (OpCode.add i64) (Arg.var a, Arg.imm 3, ()) fun p =>
  fvOp (OpCode.zext 32 64) (Arg.var old_sz, ()) fun p1 =>
  fvOp (OpCode.add i64) (Arg.var p.fst, Arg.var p1.fst, ()) fun p1 =>
  fvOp (OpCode.add i64) (Arg.var h, Arg.imm 472, ()) fun p =>
  Expr.store (Arg.var p1.fst) (Arg.var p.fst) k

abbrev storeTermExpr (pA : Val i64) (cref old_sz : Val i32) (k : Expr Val Cont [i64]) :=
  fvOp (OpCode.zext 32 64) (Arg.var cref, ()) fun p =>
  fvOp (OpCode.add i64) (Arg.var p.fst, Arg.imm 3, ()) fun p =>
  fvOp (OpCode.zext 32 64) (Arg.var old_sz, ()) fun p1 =>
  fvOp (OpCode.add i64) (Arg.var p.fst, Arg.var p1.fst, ()) fun p =>
  fvOp (OpCode.sub i64) (Arg.var p.fst, Arg.imm 1, ()) fun p =>
  fvOp (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
  fvOp (OpCode.add i64) (Arg.var pA, Arg.var p.fst, ()) fun p =>
  Expr.store (Arg.imm (t := i32) 4294967295) (Arg.var p.fst) k

abbrev watch2Expr (h : Val i64) (cref la lb : Val i32) (k_ok k_oom : Expr Val Cont [i64]) :=
  Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
    fvOp (OpCode.add i64) (Arg.var h, Arg.imm 760, ()) fun p =>
    Expr.store (Arg.imm (t := i64) 1) (Arg.var p.fst) k_oom) Blocks.nil) fun Js =>
  fvOp (OpCode.and i32) (Arg.var lb, Arg.imm 2147483647, ()) fun p =>
  Expr.call "full_watch_push" (as := [i64, i32, i32, i32, i32]) (bs := [.bool])
    (Arg.var h, Arg.var la, Arg.var p.fst, Arg.var cref, Arg.imm 2, ()) fun p =>
  Expr.jnz (Arg.var p.fst) (fvOp (OpCode.and i32) (Arg.var la, Arg.imm 2147483647, ()) fun p =>
    Expr.call "full_watch_push" (as := [i64, i32, i32, i32, i32]) (bs := [.bool])
      (Arg.var h, Arg.var lb, Arg.var p.fst, Arg.var cref, Arg.imm 2, ()) fun p =>
    Expr.jnz (Arg.var p.fst) k_ok (Expr.jump Js.fst ())) (Expr.jump Js.fst ())

theorem watch2_calls_wp (Γ : Env) (hWatchPush : HypWatchPush Γ)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s s_f : FullState} {R : Mem 64 → Prop}
    {cref la lb : Val i32} {k_ok k_oom : Expr Val Cont [i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (hsp : FullSparseInvW c F0 F_cur s_f)
    (hcref : cref.toNat < 0x80000000) (href : cref.toNat ∈ fullArenaClauseRefs s)
    (hsref : fullArenaClauseRefs s_f = fullArenaClauseRefs s) (hm_f : VivMetaEq s s_f)
    (hm : (FullMem c s_f ⋆ R) m)
    (hok : ∀ s' m', FullSparseInvW c F0 F_cur s' → s'.core.arena = s_f.core.arena →
      VivMetaEq s s' → fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (FullMem c s' ⋆ R) m' → wp Γ Q X k_ok m')
    (hoom : ∀ s' m', FullSparseInvW c F0 F_cur s' → s'.core.arena = s_f.core.arena →
      VivMetaEq s s' → fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (FullMem c s' ⋆ R) m' → wp Γ Q X k_oom m') :
    wp Γ Q X (watch2Expr c.hdr cref la lb k_ok k_oom) m := by
  have hne : cref ≠ 0xFFFFFFFF#32 := bv32_ne_sentinel_of_lt hcref
  dsimp only [watch2Expr, fvOp]
  refine wp_join_group
    (fun _ m' => ∃ s' : FullState, FullSparseInvW c F0 F_cur s' ∧
      s'.core.arena = s_f.core.arena ∧ VivMetaEq s s' ∧
      fullArenaClauseRefs s' = fullArenaClauseRefs s ∧ (FullMem c s' ⋆ R) m')
    (fun _ _ _ ⟨s', hsp', har', hmv', href', hm'⟩ => by
      fv_steps; exact hoom _ _ (fv_with_oomW hsp' 1#64) har' hmv' href' hm)
    (fun Js hJs => ?_)
  fv_steps; c0_call hWatchPush
  obtain ⟨hl1, lay1, hp1_1, hp1_2⟩ := watch2_pre_ok (blk := lb) hsp hne
  refine ⟨c, s_f, R, rfl, hl1, lay1, hp1_1, hp1_2, hm,
    fun ok1 wvec3 wstk3 wlen3 wu3 wsort3 m4 hlen4 hlay4 hoth4 hok1_t hok1_f hm4 => ?_⟩
  have hsp4 := fullWatchPush_large_preserves_sparseInvW hsp (bv32_mask_lo31_props lb).1 hcref
    (by rw [hsref]; exact href) hlen4 hlay4 hoth4
    (fun h => let t := hok1_t h; ⟨t.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2 rfl⟩) hok1_f
  fv_steps
  · c0_call hWatchPush
    obtain ⟨hl2, lay2, hp2_1, hp2_2⟩ := watch2_pre_ok (blk := la) hsp4 hne
    refine ⟨c, _, R, rfl, hl2, lay2, hp2_1, hp2_2, hm4,
      fun ok2 wvec4 wstk4 wlen4 wu4 wsort4 m5 hlen5 hlay5 hoth5 hok2_t hok2_f hm5 => ?_⟩
    have hsp5 := fullWatchPush_large_preserves_sparseInvW hsp4 (bv32_mask_lo31_props la).1 hcref
      (by change cref.toNat ∈ fullArenaClauseRefs s_f; rw [hsref]; exact href) hlen5 hlay5 hoth5
      (fun h => let t := hok2_t h; ⟨t.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2 rfl⟩)
      hok2_f
    fv_steps
    · exact hok _ m5 hsp5 rfl hm_f hsref hm5
    · exact hJs () m5 ⟨_, hsp5, rfl, hm_f, hsref, hm5⟩
  · exact hJs () m4 ⟨_, hsp4, rfl, hm_f, hsref, hm4⟩


theorem bv8_zext32_eq0_iff : ∀ x : BitVec 8, x.setWidth 32 = 0#32 ↔ x = 0#8 := by decide
theorem bv32_lshr1_toNat (x : BitVec 32) : (x >>> 1#32).toNat = x.toNat / 2 := by
  change (x >>> 1).toNat = x.toNat / 2
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
private theorem bv32_xor1_toNat (x : BitVec 32) : (x ^^^ 1#32).toNat = x.toNat ^^^ 1 := by
  simp [BitVec.toNat_xor]
private theorem litNeg_div2 (l : Nat) : litNeg l / 2 = l / 2 := litVar_litNeg l
private theorem bv32_xor1_lt {x : BitVec 32} {n : Nat} (hx : x.toNat < 2 * n) :
    (x ^^^ 1#32).toNat < 2 * n := by
  rw [bv32_xor1_toNat, show x.toNat ^^^ 1 = litNeg x.toNat from rfl, litNeg_eq]
  split <;> omega
private theorem bv32_xor1_div2 (x : BitVec 32) : (x ^^^ 1#32).toNat / 2 = x.toNat / 2 := by
  rw [bv32_xor1_toNat]; exact fullInv_var_xor1 x.toNat
theorem bv64_trunc32_toNat {x : BitVec 64} (hx : x.toNat < 2 ^ 32) :
    (x.truncate 32).toNat = x.toNat := by bv_omega

private theorem nodup_map_inj_on {α β : Type} {f : α → β} :
    ∀ l : List α, l.Nodup → (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → (l.map f).Nodup
  | [], _, _ => .nil
  | a :: l, hnd, hinj => by
    have ⟨han, hndl⟩ := List.nodup_cons.mp hnd
    refine List.nodup_cons.mpr ⟨fun hm => ?_,
      nodup_map_inj_on l hndl fun x hx y hy => hinj x (by simp [hx]) y (by simp [hy])⟩
    obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hm
    exact han ((hinj b (by simp [hb]) a (by simp) hfb) ▸ hb)

theorem nodup_lt_length_le :
    ∀ (l : List Nat) (n : Nat), l.Nodup → (∀ x ∈ l, x < n) → l.length ≤ n
  | [], _, _, _ => Nat.zero_le _
  | a :: l, 0, _, h => absurd (h a (by simp)) (by omega)
  | a :: l, n + 1, hnd, h => by
    have ha := h a (by simp)
    have ⟨han, hndl⟩ := List.nodup_cons.mp hnd
    by_cases htop : a = n
    · have hl := nodup_lt_length_le l n hndl fun x hx => by
        have := h x (by simp [hx]); have : x ≠ a := fun e => han (e ▸ hx); omega
      simp [hl]
    · let l' := l.map fun x => if x = n then a else x
      have hnd' : l'.Nodup := by
        refine nodup_map_inj_on l hndl fun x hx y hy heq => ?_
        by_cases hxn : x = n <;> by_cases hyn : y = n <;> simp only [hxn, hyn, ↓reduceIte] at heq
        · rw [hxn, hyn]
        · exact absurd (heq ▸ hy) han
        · exact absurd (heq.symm ▸ hx) han
        · exact heq
      have hlt' : ∀ y ∈ l', y < n := by
        intro y hy; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
        by_cases hxn : x = n
        · simp only [hxn, ↓reduceIte]; omega
        · simp only [hxn, ↓reduceIte]; have := h x (by simp [hx]); omega
      have hl' := nodup_lt_length_le l' n hnd' hlt'
      simp only [l', List.length_map] at hl'
      simp only [List.length_cons]; omega

private theorem queue_missing_lt {n m x : Nat} {xs : List (BitVec 32)}
    (hm : m ≤ xs.length) (hlt : ∀ i < m, (xs[i]?.getD 0#32).toNat < n)
    (hnd : ((xs.take m).map BitVec.toNat).Nodup) (hx : x < n)
    (hmiss : ∀ i < m, (xs[i]?.getD 0#32).toNat ≠ x) : m < n := by
  refine inj_lt_of_missing (fun i => (xs[i]?.getD 0#32).toNat) (fun i j hi hj heq => ?_) hlt
    hx hmiss
  have hlen : ((xs.take m).map BitVec.toNat).length = m := by
    rw [List.length_map, List.length_take]; omega
  have hpw := List.pairwise_iff_getElem.mp hnd
  rw [← hlen] at hi hj
  by_cases hne : i = j
  · exact hne
  · rcases Nat.lt_or_gt_of_ne hne with hlt_ij | hgt_ij
    · exact absurd (by
        simp only [List.getElem_map, List.getElem_take]
        rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at heq
        exact heq) (hpw i j hi hj hlt_ij)
    · exact absurd (by
        simp only [List.getElem_map, List.getElem_take]
        rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at heq
        exact heq.symm) (hpw j i hj hi hgt_ij)

theorem fv_with_mrk_rsz {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInv c F0 s) (hw : FullWitnessInv c F0 F_cur s.core)
    {mrk' : List (BitVec 8)} {ws1' ws2' : List (BitVec 32)} {rsz' : BitVec 64}
    (hmrk : mrk'.length = c.max_vars) (hmrk_clr : ∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8)
    (hws1 : ws1'.length = 2 * c.max_vars) (hws2 : ws2'.length = 2 * c.max_vars) :
    let s' : FullState :=
      { s with
        core := { s.core with mrk := mrk' }
        scratch := { s.scratch with work_stk1 := ws1', work_stk2 := ws2', res_sz := rsz' } }
    FullSparseInv c F0 s' ∧ FullWitnessInv c F0 F_cur s'.core := by
  intro s'
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
  have hlen' : s'.LengthsOk c :=
    ⟨{ hsp.1.lengths.core_ok with mrk_len := hmrk },
     { hsp.1.lengths.scratch_ok with work_stk1_len := hws1, work_stk2_len := hws2 }⟩
  exact ⟨⟨⟨hlen', F_cur, hw'⟩, ⟨hmrk_clr, hsp.2.1.2⟩, hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2⟩, hw'⟩

@[expose] def VivQueueOk (c : FullCfg) (s : FullState) (mrk : List (BitVec 8))
    (ws1 : List (BitVec 32)) (qlen : Nat) : Prop :=
  mrk.length = c.max_vars ∧ ws1.length = 2 * c.max_vars ∧ qlen ≤ s.core.cur_vars ∧
  (∀ i < qlen, (ws1[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
  ((ws1.take qlen).map BitVec.toNat).Nodup ∧
  (∀ i < qlen,
    0 < (s.core.lvl[(ws1[i]?.getD 0#32).toNat]?.getD 0#32).toNat ∧
    ∃ idx < s.core.trail_end,
      (s.core.trl[idx]?.getD 0#32).toNat / 2 = (ws1[i]?.getD 0#32).toNat) ∧
  (∀ v < s.core.cur_vars, mrk[v]?.getD 0#8 = 1#8 ↔ v ∈ (ws1.take qlen).map BitVec.toNat) ∧
  (∀ v < s.core.cur_vars, mrk[v]?.getD 0#8 = 0#8 ∨ mrk[v]?.getD 0#8 = 1#8) ∧
  (∀ v, s.core.cur_vars ≤ v → v < c.max_vars → mrk[v]?.getD 0#8 = 0#8)

theorem mem_map_take_iff {xs : List (BitVec 32)} {n x : Nat} (hn : n ≤ xs.length) :
    x ∈ (xs.take n).map BitVec.toNat ↔ ∃ i < n, (xs[i]?.getD 0#32).toNat = x := by
  rw [List.mem_map]; constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    have hlt : i < n := by rw [List.length_take] at hi; omega
    exact ⟨i, hlt, by rw [List.getElem_take, List.getElem?_eq_getElem (by omega), Option.getD_some]⟩
  · rintro ⟨i, hi, heq⟩
    refine ⟨xs[i]'(by omega), ?_, ?_⟩
    · rw [List.mem_iff_getElem]
      exact ⟨i, by rw [List.length_take]; omega, by simp [List.getElem_take]⟩
    · rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at heq

theorem push_queue_lt {c : FullCfg} {s : FullState} {mrk : List (BitVec 8)}
    {ws1 : List (BitVec 32)} {qlen : Nat} (hq : VivQueueOk c s mrk ws1 qlen)
    (hcv : s.core.cur_vars ≤ c.max_vars) {v : Nat} (hv : v < s.core.cur_vars)
    (hm0 : mrk[v]?.getD 0#8 = 0#8) : qlen < s.core.cur_vars := by
  have hql := hq.2.2.1; have hsl := hq.2.1
  have hlen : qlen ≤ ws1.length := by omega
  refine queue_missing_lt hlen hq.2.2.2.1 hq.2.2.2.2.1 hv fun i hi heq => ?_
  have h1 := (hq.2.2.2.2.2.2.1 v hv).mpr ((mem_map_take_iff hlen).mpr ⟨i, hi, heq⟩)
  rw [hm0] at h1; cases h1

theorem push_queue_step {c : FullCfg} {s : FullState} {mrk : List (BitVec 8)}
    {ws1 : List (BitVec 32)} {qlen : Nat} (hq : VivQueueOk c s mrk ws1 qlen)
    (hcv : s.core.cur_vars ≤ c.max_vars) {v : BitVec 32} (hv : v.toNat < s.core.cur_vars)
    (hlvl : 0 < (s.core.lvl[v.toNat]?.getD 0#32).toNat) (hm0 : mrk[v.toNat]?.getD 0#8 = 0#8)
    (htrl : ∃ idx < s.core.trail_end, (s.core.trl[idx]?.getD 0#32).toNat / 2 = v.toNat) :
    let mrk' := mrk.set v.toNat 1#8
    let ws1' := ws1.set qlen v
    qlen < s.core.cur_vars ∧ VivQueueOk c s mrk' ws1' (qlen + 1) ∧
    (∀ j < qlen, ws1'[j]? = ws1[j]?) ∧
    ∀ x, x ∈ (ws1.take qlen).map BitVec.toNat →
      x ∈ (ws1'.take (qlen + 1)).map BitVec.toNat := by
  have hq_lt : qlen < s.core.cur_vars := push_queue_lt hq hcv hv hm0
  have hmrk_len : mrk.length = c.max_vars := hq.1
  have hws1_len : ws1.length = 2 * c.max_vars := hq.2.1
  have hv_mrk : v.toNat < mrk.length := by omega
  have hq_ws1 : qlen < ws1.length := by omega
  have hnot : v.toNat ∉ (ws1.take qlen).map BitVec.toNat := fun hmem => by
    have h1 := (hq.2.2.2.2.2.2.1 v.toNat hv).mpr hmem; rw [hm0] at h1; cases h1
  have htake : (ws1.set qlen v).take (qlen + 1) = ws1.take qlen ++ [v] := by
    refine List.ext_getElem (by simp [List.length_take]; try omega) fun i hi _ => ?_
    simp only [List.length_take, List.length_set] at hi
    rw [List.getElem_take]
    by_cases hlt : i < qlen
    · rw [List.getElem_set_ne (by omega),
        List.getElem_append_left (by simp [List.length_take]; omega), List.getElem_take]
    · have hieq : i = qlen := by omega
      simp only [hieq]
      rw [List.getElem_set_self, List.getElem_append_right (by simp [List.length_take]; omega)]
      simp [List.length_take, Nat.min_eq_left (by omega : qlen ≤ ws1.length)]
  have hmap : ((ws1.set qlen v).take (qlen + 1)).map BitVec.toNat =
      (ws1.take qlen).map BitVec.toNat ++ [v.toNat] := by rw [htake, List.map_append]; rfl
  refine ⟨hq_lt, ⟨by simp [hmrk_len], by simp [hws1_len], by omega, fun i hi => ?_, ?_,
      fun i hi => ?_, fun u hu => ?_, fun u hu => ?_, fun u hu1 hu2 => ?_⟩,
      fun j hj => List.getElem?_set_ne (by omega),
      fun x hx => by rw [hmap]; exact List.mem_append.mpr (Or.inl hx)⟩
  · rcases (by omega : i < qlen ∨ i = qlen) with hi' | rfl
    · rw [List.getElem?_set_ne (by omega)]; exact hq.2.2.2.1 i hi'
    · rw [List.getElem?_set_self hq_ws1, Option.getD_some]; exact hv
  · rw [hmap, List.nodup_append]
    exact ⟨hq.2.2.2.2.1, List.nodup_cons.mpr ⟨by simp, .nil⟩, fun a ha b hb => by
      simp only [List.mem_singleton] at hb; subst hb; exact fun heq => hnot (heq ▸ ha)⟩
  · rcases (by omega : i < qlen ∨ i = qlen) with hi' | rfl
    · rw [List.getElem?_set_ne (by omega)]; exact hq.2.2.2.2.2.1 i hi'
    · rw [List.getElem?_set_self hq_ws1, Option.getD_some]; exact ⟨hlvl, htrl⟩
  · rw [hmap]; simp only [List.mem_append, List.mem_singleton]
    by_cases huv : u = v.toNat
    · subst huv; rw [List.getElem?_set_self hv_mrk, Option.getD_some]; simp
    · rw [List.getElem?_set_ne (Ne.symm huv), hq.2.2.2.2.2.2.1 u hu]; simp [huv]
  · by_cases huv : u = v.toNat
    · subst huv; right; rw [List.getElem?_set_self hv_mrk, Option.getD_some]
    · rw [List.getElem?_set_ne (Ne.symm huv)]; exact hq.2.2.2.2.2.2.2.1 u hu
  · rw [List.getElem?_set_ne (by omega)]; exact hq.2.2.2.2.2.2.2.2 u hu1 hu2

@[expose] def VivClosedOk (s : FullState) (implied : BitVec 32)
    (ws1 ws2 : List (BitVec 32)) (qi qlen olen : Nat) (taut : Bool) : Prop :=
  ∀ k < qi, ∀ idx < s.core.trail_end,
    (s.core.trl[idx]?.getD 0#32).toNat / 2 = (ws1[k]?.getD 0#32).toNat →
      if s.core.rsns[(ws1[k]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 then
        taut = false →
          (s.core.trl[idx]?.getD 0#32).toNat ≠ implied.toNat ∧
          ((s.core.trl[idx]?.getD 0#32).toNat ^^^ 1) ∈ (ws2.take olen).map BitVec.toNat
      else if
          (s.core.rsns[(ws1[k]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
          then
        let ov := (s.core.rsns[(ws1[k]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 &&&
          0x7FFFFFFF#32).toNat / 2
        (s.core.lvl[ov]?.getD 0#32).toNat = 0 ∨ ov ∈ (ws1.take qlen).map BitVec.toNat
      else
        ∀ q ∈ fullArenaClauseLitsCore s.core
            (s.core.rsns[(ws1[k]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32).toNat,
          q ≠ (s.core.trl[idx]?.getD 0#32).toNat →
          (s.core.lvl[q / 2]?.getD 0#32).toNat = 0 ∨
            q / 2 ∈ (ws1.take qlen).map BitVec.toNat

@[expose] def VivOutOk (s : FullState) (implied : BitVec 32)
    (ws1 ws2 : List (BitVec 32)) (qi olen : Nat) (taut : Bool) : Prop :=
  taut = false →
    olen ≤ s.core.cur_vars ∧
    (∀ i < olen, (ws2[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
    (((ws2.take olen).map BitVec.toNat).map (· / 2)).Nodup ∧
    (∀ i < olen,
      let v := (ws2[i]?.getD 0#32).toNat / 2
      (implied ≠ 0xFFFFFFFF#32 ∧ i = 0 ∧ v = implied.toNat / 2) ∨
      v ∈ (ws1.take qi).map BitVec.toNat) ∧
    (implied ≠ 0xFFFFFFFF#32 → 0 < olen ∧ ws2[0]? = some implied) ∧
    (∀ j < qi,
      implied = 0xFFFFFFFF#32 ∨ (ws1[j]?.getD 0#32).toNat ≠ implied.toNat / 2 ∨
      s.core.rsns[(ws1[j]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)

@[expose] def VivSeedOk (s : FullState) (cref implied : BitVec 32)
    (ws1 ws2 : List (BitVec 32)) (qlen olen : Nat) (taut : Bool) : Prop :=
  taut = false →
    if implied ≠ 0xFFFFFFFF#32 then
      implied.toNat ∈ (ws2.take olen).map BitVec.toNat
    else if s.core.confl_type = 1#64 then
      let a := s.core.confl_lit0.toNat
      let b := s.core.confl_lit1.toNat
      ((s.core.lvl[a / 2]?.getD 0#32).toNat = 0 ∨ a / 2 ∈ (ws1.take qlen).map BitVec.toNat) ∧
      ((s.core.lvl[b / 2]?.getD 0#32).toNat = 0 ∨ b / 2 ∈ (ws1.take qlen).map BitVec.toNat)
    else
      let src := if s.core.confl_type = 2#64 then s.core.confl_ref.toNat else cref.toNat
      ∀ l ∈ fullArenaClauseLits s src,
        (s.core.lvl[l / 2]?.getD 0#32).toNat = 0 ∨ l / 2 ∈ (ws1.take qlen).map BitVec.toNat

theorem vivClosed_mono_q {s : FullState} {implied : BitVec 32}
    {ws1 ws1' ws2 : List (BitVec 32)} {qi qlen qlen' olen : Nat} {taut : Bool}
    (hc : VivClosedOk s implied ws1 ws2 qi qlen olen taut)
    (hqi : qi ≤ qlen) (hql : qlen ≤ qlen') (hl1 : qlen ≤ ws1.length) (hql' : qlen' ≤ ws1'.length)
    (heq : ∀ j < qlen, ws1'[j]? = ws1[j]?) :
    VivClosedOk s implied ws1' ws2 qi qlen' olen taut := by
  intro k hk idx hidx htrl
  have hkeq : ws1'[k]? = ws1[k]? := heq k (by omega)
  have hmem : ∀ x, x ∈ (ws1.take qlen).map BitVec.toNat →
      x ∈ (ws1'.take qlen').map BitVec.toNat := fun x hx => by
    obtain ⟨j, hj, rfl⟩ := (mem_map_take_iff hl1).mp hx
    exact (mem_map_take_iff hql').mpr ⟨j, by omega, by rw [heq j hj]⟩
  have hc' := hc k hk idx hidx (by rwa [← hkeq])
  rw [hkeq]
  by_cases h1 :
      s.core.rsns[(ws1[k]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32
  · rw [ite_eq_left h1] at hc' ⊢; exact hc'
  · rw [ite_eq_right h1] at hc' ⊢
    by_cases h2 :
        (s.core.rsns[(ws1[k]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
    · rw [ite_eq_left h2] at hc' ⊢; exact hc'.elim Or.inl (fun hm => Or.inr (hmem _ hm))
    · rw [ite_eq_right h2] at hc' ⊢
      intro q hq hqp; exact (hc' q hq hqp).elim Or.inl (fun hm => Or.inr (hmem _ hm))

theorem vivOut_mono_qi_len {s : FullState} {implied : BitVec 32}
    {ws1 ws2 : List (BitVec 32)} {qi qlen olen : Nat} {taut : Bool}
    (ho : VivOutOk s implied ws1 ws2 qi olen taut)
    (hqi1 : qi + 1 ≤ qlen) (hq_len : qlen ≤ ws1.length)
    (hne : implied = 0xFFFFFFFF#32 ∨ (ws1[qi]?.getD 0#32).toNat ≠ implied.toNat / 2 ∨
      s.core.rsns[(ws1[qi]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) :
    VivOutOk s implied ws1 ws2 (qi + 1) olen taut := by
  intro hf; obtain ⟨hle, hlt, hnd, hmem, himp, hnot⟩ := ho hf
  refine ⟨hle, hlt, hnd, fun i hi => ?_, himp, fun j hj => ?_⟩
  · refine (hmem i hi).elim Or.inl fun hm => Or.inr ?_
    obtain ⟨k, hk, heq⟩ := (mem_map_take_iff (by omega)).mp hm
    exact (mem_map_take_iff (by omega)).mpr ⟨k, by omega, heq⟩
  · rcases (by omega : j < qi ∨ j = qi) with hj' | rfl
    · exact hnot j hj'
    · exact hne

theorem vivOut_mono_qlen {s : FullState} {implied : BitVec 32}
    {ws1 ws1' ws2 : List (BitVec 32)} {qi qlen olen : Nat} {taut : Bool}
    (ho : VivOutOk s implied ws1 ws2 qi olen taut) (hqi : qi ≤ qlen)
    (hl1 : qlen ≤ ws1.length) (hl2 : qlen ≤ ws1'.length)
    (heq : ∀ j < qlen, ws1'[j]? = ws1[j]?) :
    VivOutOk s implied ws1' ws2 qi olen taut := by
  intro hf; obtain ⟨hle, hlt, hnd, hmem, himp, hnot⟩ := ho hf
  have htake : ws1'.take qi = ws1.take qi := List.ext_getElem
    (by simp [List.length_take]; omega) fun i hi _ => by
      simp only [List.length_take] at hi
      rw [List.getElem_take, List.getElem_take]
      have h := heq i (by omega)
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at h
      exact Option.some.inj h
  exact ⟨hle, hlt, hnd, fun i hi => by rw [htake]; exact hmem i hi, himp,
    fun j hj => by rw [heq j (by omega)]; exact hnot j hj⟩

theorem vivOut_push_lt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {mrk : List (BitVec 8)} {ws1 ws2 : List (BitVec 32)}
    {implied : BitVec 32} {qi qlen olen : Nat}
    (hw : FullWitnessInv c F0 F_cur s.core) (hq : VivQueueOk c s mrk ws1 qlen)
    (hcv : s.core.cur_vars ≤ c.max_vars)
    (hqi : qi < qlen) (ho : VivOutOk s implied ws1 ws2 qi olen false)
    (himp : implied ≠ 0xFFFFFFFF#32 →
      implied.toNat < 2 * s.core.cur_vars ∧ s.core.vals[implied.toNat]?.getD 0#8 = 1#8)
    {idx : Nat} (hidx : idx < s.core.trail_end)
    (htrl : (s.core.trl[idx]?.getD 0#32).toNat / 2 = (ws1[qi]?.getD 0#32).toNat)
    (hne_imp : implied ≠ 0xFFFFFFFF#32 → (s.core.trl[idx]?.getD 0#32) ≠ implied)
    (hws2 : olen ≤ ws2.length) :
    let v := (ws1[qi]?.getD 0#32).toNat
    olen < s.core.cur_vars ∧ v < s.core.cur_vars ∧
    (implied ≠ 0xFFFFFFFF#32 → v ≠ implied.toNat / 2) ∧
    v ∉ ((ws2.take olen).map BitVec.toNat).map (· / 2) := by
  intro v
  have hql := hq.2.2.1; have hws1_l := hq.2.1
  obtain ⟨hle, hlt, hnd, hmem, himp_out, _⟩ := ho rfl
  have hv_lt : v < s.core.cur_vars := hq.2.2.2.1 qi hqi
  have hv_ne_imp : implied ≠ 0xFFFFFFFF#32 → v ≠ implied.toNat / 2 := by
    intro hne heq
    obtain ⟨hil, hiv⟩ := himp hne
    obtain ⟨idx0, hidx0, heq0⟩ := (hw.vals_true_iff implied.toNat hil).mp hiv
    have hidx_eq : idx = idx0 := hw.trail_vars_nodup idx idx0 hidx hidx0 (by
      rw [htrl, show (ws1[qi]?.getD 0#32).toNat = v from rfl, heq, ← heq0])
    rw [← hidx_eq] at heq0; exact hne_imp hne (BitVec.eq_of_toNat_eq heq0)
  have hv_not_qi : v ∉ (ws1.take qi).map BitVec.toNat := by
    intro hm
    obtain ⟨j, hj, hj_eq⟩ := (mem_map_take_iff (by omega)).mp hm
    have hql' : ((ws1.take qlen).map BitVec.toNat).length = qlen := by
      rw [List.length_map, List.length_take]; omega
    have hj_lt : j < ((ws1.take qlen).map BitVec.toNat).length := by omega
    have hq_lt : qi < ((ws1.take qlen).map BitVec.toNat).length := by omega
    have hpair := List.pairwise_iff_getElem.mp hq.2.2.2.2.1 j qi hj_lt hq_lt hj
    simp only [List.getElem_map, List.getElem_take] at hpair
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hj_eq
    have hqi_eq : v = ws1[qi].toNat := by
      dsimp only [v]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact hpair (hj_eq.trans hqi_eq)
  have hv_not : v ∉ ((ws2.take olen).map BitVec.toNat).map (· / 2) := by
    intro hm; obtain ⟨w, hm', hw_eq⟩ := List.mem_map.mp hm
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm'
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    have hi' : i < olen := by rw [List.length_take] at hi; omega
    have hmi := hmem i hi'
    rw [List.getElem_take] at hw_eq
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hmi
    rcases hmi with ⟨hne, _, heq⟩ | hm_qi
    · exact hv_ne_imp hne (by rw [← hw_eq, heq])
    · rw [hw_eq] at hm_qi; exact hv_not_qi hm_qi
  have hnd' : (v :: ((ws2.take olen).map BitVec.toNat).map (· / 2)).Nodup :=
    List.nodup_cons.mpr ⟨hv_not, hnd⟩
  have hlt' : ∀ x ∈ (v :: ((ws2.take olen).map BitVec.toNat).map (· / 2)),
      x < s.core.cur_vars := fun x hx => by
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hv_lt
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
      have hi' : i < olen := by rw [List.length_take] at hi; omega
      have hb_lt := hlt i hi'
      rw [List.getElem_take]
      have hbi : (ws2[i]'(by omega)).toNat = (ws2[i]?.getD 0#32).toNat := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      omega
  have hlen_le := nodup_lt_length_le _ _ hnd' hlt'
  simp only [List.length_cons, List.length_map, List.length_take] at hlen_le
  exact ⟨by omega, hv_lt, hv_ne_imp, hv_not⟩

theorem vivOut_push_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {mrk : List (BitVec 8)} {ws1 ws2 : List (BitVec 32)}
    {implied : BitVec 32} {qi qlen olen : Nat}
    (hw : FullWitnessInv c F0 F_cur s.core) (hq : VivQueueOk c s mrk ws1 qlen)
    (hqi : qi < qlen) (ho : VivOutOk s implied ws1 ws2 qi olen false)
    (hc : VivClosedOk s implied ws1 ws2 qi qlen olen false)
    (himp : implied ≠ 0xFFFFFFFF#32 →
      implied.toNat < 2 * s.core.cur_vars ∧ s.core.vals[implied.toNat]?.getD 0#8 = 1#8)
    {idx : Nat} (hidx : idx < s.core.trail_end)
    (htrl : (s.core.trl[idx]?.getD 0#32).toNat / 2 = (ws1[qi]?.getD 0#32).toNat)
    (hrsn : s.core.rsns[(ws1[qi]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32)
    (hne_imp : implied ≠ 0xFFFFFFFF#32 → (s.core.trl[idx]?.getD 0#32) ≠ implied)
    (hws2 : ws2.length = 2 * c.max_vars) (hcv : s.core.cur_vars ≤ c.max_vars) :
    let tl := s.core.trl[idx]?.getD 0#32
    let ws2' := ws2.set olen (tl ^^^ 1#32)
    olen < s.core.cur_vars ∧ olen < ws2.length ∧
    VivOutOk s implied ws1 ws2' (qi + 1) (olen + 1) false ∧
    VivClosedOk s implied ws1 ws2' (qi + 1) qlen (olen + 1) false ∧
    (∀ j < olen, ws2'[j]? = ws2[j]?) := by
  intro tl ws2'
  have hql := hq.2.2.1; have hws1_l := hq.2.1
  obtain ⟨hle, hlt, hnd, hmem, himp_out, hnot_qi⟩ := ho rfl
  obtain ⟨hol_lt, hv_lt, hv_ne_imp, hv_not⟩ :=
    vivOut_push_lt hw hq hcv hqi ho himp hidx htrl hne_imp (by omega)
  have hol_ws2 : olen < ws2.length := by omega
  have htake2 : ws2'.take (olen + 1) = ws2.take olen ++ [tl ^^^ 1#32] := by
    refine List.ext_getElem (by simp [ws2', List.length_take]; try omega) fun i hi _ => ?_
    simp only [List.length_take, List.length_set, ws2'] at hi
    rw [List.getElem_take]
    by_cases hlt_i : i < olen
    · rw [List.getElem_set_ne (by omega),
        List.getElem_append_left (by simp [List.length_take]; omega), List.getElem_take]
    · have hieq : i = olen := by omega
      simp only [hieq]
      rw [List.getElem_set_self, List.getElem_append_right (by simp [List.length_take]; omega)]
      simp [List.length_take, Nat.min_eq_left (by omega : olen ≤ ws2.length)]
  have htl_lt : tl.toNat < 2 * s.core.cur_vars := hw.trail_lits_lt idx hidx
  have hxor_lt : (tl ^^^ 1#32).toNat < 2 * s.core.cur_vars := bv32_xor1_lt htl_lt
  have hdiv_eq : (tl ^^^ 1#32).toNat / 2 = (ws1[qi]?.getD 0#32).toNat := by
    rw [bv32_xor1_div2, ← htrl]
  have hq_ws1 : qi < ws1.length := by omega
  have htake1 : ws1.take (qi + 1) = ws1.take qi ++ [ws1[qi]'hq_ws1] := by
    refine List.ext_getElem (by simp [List.length_take, hws1_l]; try omega) fun i hi _ => ?_
    simp only [List.length_take, hws1_l] at hi
    rw [List.getElem_take]
    by_cases hlt_i : i < qi
    · rw [List.getElem_append_left (by simp [List.length_take]; omega), List.getElem_take]
    · have hieq : i = qi := by omega
      simp only [hieq]; rw [List.getElem_append_right (by simp [List.length_take]; omega)]
      simp [List.length_take, Nat.min_eq_left (by omega : qi ≤ ws1.length)]
  refine ⟨hol_lt, hol_ws2, fun _ => ⟨by omega, fun i hi => ?_, ?_, fun i hi => ?_,
      fun hne => ?_, fun j hj => ?_⟩, fun k hk idx' hidx' htrl' => ?_,
      fun j hj => List.getElem?_set_ne (by omega)⟩
  · rcases (by omega : i < olen ∨ i = olen) with hi' | rfl
    · rw [List.getElem?_set_ne (by omega)]; exact hlt i hi'
    · rw [List.getElem?_set_self hol_ws2, Option.getD_some]; exact hxor_lt
  · rw [htake2, List.map_append, List.map_append, List.nodup_append]
    refine ⟨hnd, List.nodup_cons.mpr ⟨by simp, .nil⟩, fun a ha b hb => ?_⟩
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb; subst hb
    rw [hdiv_eq]; exact fun heq => hv_not (heq ▸ ha)
  · rcases (by omega : i < olen ∨ i = olen) with hi' | rfl
    · rw [List.getElem?_set_ne (by omega)]
      refine (hmem i hi').elim Or.inl fun hm => Or.inr ?_
      rw [htake1, List.map_append]; exact List.mem_append.mpr (Or.inl hm)
    · right; rw [List.getElem?_set_self hol_ws2, Option.getD_some, hdiv_eq, htake1,
        List.map_append]
      exact List.mem_append.mpr (Or.inr (by simp [List.getElem?_eq_getElem hq_ws1]))
  · obtain ⟨h0, hw0⟩ := himp_out hne
    exact ⟨by omega, by dsimp only [ws2']; rw [List.getElem?_set_ne (by omega)]; exact hw0⟩
  · rcases (by omega : j < qi ∨ j = qi) with hj' | rfl
    · exact hnot_qi j hj'
    · by_cases hne : implied = 0xFFFFFFFF#32
      · exact Or.inl hne
      · exact Or.inr (Or.inl (hv_ne_imp hne))
  · have hmem2 : ∀ l, l ∈ (ws2.take olen).map BitVec.toNat →
        l ∈ (ws2'.take (olen + 1)).map BitVec.toNat := fun l hl => by
      rw [htake2, List.map_append]; exact List.mem_append.mpr (Or.inl hl)
    rcases (by omega : k < qi ∨ k = qi) with hk' | rfl
    · have hc' := hc k hk' idx' hidx' htrl'
      by_cases hrsn_k :
          s.core.rsns[(ws1[k]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32
      · simp only [hrsn_k, ↓reduceIte] at hc' ⊢
        exact fun hf => ⟨(hc' hf).1, hmem2 _ (hc' hf).2⟩
      · simp only [hrsn_k, ↓reduceIte] at hc' ⊢
        exact hc'
    · rw [ite_eq_left hrsn]; intro _
      have hidx_eq : idx' = idx := hw.trail_vars_nodup idx' idx hidx' hidx (by rw [htrl', htrl])
      subst hidx_eq
      refine ⟨fun heq => hne_imp ?_ (BitVec.eq_of_toNat_eq heq), ?_⟩
      · intro himp0; simp [himp0] at heq
        have := hw.trail_lits_lt idx' hidx'
        have := c.hmaxv; unfold dimacsBound at this; omega
      · rw [htake2, List.map_append, ← bv32_xor1_toNat tl]
        simp only [List.mem_append, List.map_cons, List.map_nil, List.mem_singleton, or_true]

theorem vivClosed_step_bin {s : FullState} {implied : BitVec 32}
    {ws1 ws2 : List (BitVec 32)} {qi qlen olen : Nat} {taut : Bool}
    (hc : VivClosedOk s implied ws1 ws2 qi qlen olen taut)
    (htrl_nodup : ∀ i j, i < s.core.trail_end → j < s.core.trail_end →
      (s.core.trl[i]?.getD 0#32).toNat / 2 = (s.core.trl[j]?.getD 0#32).toNat / 2 → i = j)
    {idx0 : Nat} (hidx0 : idx0 < s.core.trail_end)
    (htrl0 : (s.core.trl[idx0]?.getD 0#32).toNat / 2 = (ws1[qi]?.getD 0#32).toNat)
    (hrsn_ne : s.core.rsns[(ws1[qi]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hbin : (s.core.rsns[(ws1[qi]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32)
    (hcov : (s.core.lvl[(s.core.rsns[(ws1[qi]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 &&&
        0x7FFFFFFF#32).toNat / 2]?.getD 0#32).toNat = 0 ∨
      (s.core.rsns[(ws1[qi]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 &&& 0x7FFFFFFF#32).toNat / 2 ∈
        (ws1.take qlen).map BitVec.toNat) :
    VivClosedOk s implied ws1 ws2 (qi + 1) qlen olen taut := by
  intro k hk idx hidx htrl
  rcases (by omega : k < qi ∨ k = qi) with hk' | hk_eq
  · exact hc k hk' idx hidx htrl
  · rw [hk_eq] at htrl ⊢
    have := htrl_nodup idx idx0 hidx hidx0 (htrl.trans htrl0.symm)
    subst this; rw [ite_eq_right hrsn_ne, ite_eq_left hbin]; exact hcov

theorem vivClosed_step_large {s : FullState} {implied : BitVec 32}
    {ws1 ws2 : List (BitVec 32)} {qi qlen olen : Nat} {taut : Bool}
    (hc : VivClosedOk s implied ws1 ws2 qi qlen olen taut)
    (htrl_nodup : ∀ i j, i < s.core.trail_end → j < s.core.trail_end →
      (s.core.trl[i]?.getD 0#32).toNat / 2 = (s.core.trl[j]?.getD 0#32).toNat / 2 → i = j)
    {idx0 : Nat} (hidx0 : idx0 < s.core.trail_end)
    (htrl0 : (s.core.trl[idx0]?.getD 0#32).toNat / 2 = (ws1[qi]?.getD 0#32).toNat)
    (hrsn_ne : s.core.rsns[(ws1[qi]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hlg : (s.core.rsns[(ws1[qi]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) = 0#32)
    (hcov : ∀ q ∈ fullArenaClauseLitsCore s.core
        (s.core.rsns[(ws1[qi]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32).toNat,
      q / 2 ≠ (ws1[qi]?.getD 0#32).toNat →
      (s.core.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ q / 2 ∈ (ws1.take qlen).map BitVec.toNat)
    (hreason : ∀ q ∈ fullArenaClauseLitsCore s.core
        (s.core.rsns[(ws1[qi]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32).toNat,
      q = (s.core.trl[idx0]?.getD 0#32).toNat ∨
      ∃ m < idx0, (s.core.trl[m]?.getD 0#32).toNat = q ^^^ 1) :
    VivClosedOk s implied ws1 ws2 (qi + 1) qlen olen taut := by
  intro k hk idx hidx htrl
  rcases (by omega : k < qi ∨ k = qi) with hk' | hk_eq
  · exact hc k hk' idx hidx htrl
  · rw [hk_eq] at htrl ⊢
    have := htrl_nodup idx idx0 hidx hidx0 (htrl.trans htrl0.symm)
    subst this; rw [ite_eq_right hrsn_ne, ite_eq_right (by simp [hlg])]
    intro q hq hqp
    have hq_ne_v : q / 2 ≠ (ws1[qi]?.getD 0#32).toNat := by
      rcases hreason q hq with hsame | ⟨m, hm_lt, hmeq⟩
      · exact absurd hsame hqp
      · intro heqv; have hmi : m = idx := htrl_nodup m idx (by omega) hidx (by
          rw [hmeq, fullInv_var_xor1 q, heqv, ← htrl0])
        omega
    exact hcov q hq hq_ne_v

theorem vivClosed_taut_true {s : FullState} {implied : BitVec 32}
    {ws1 ws2 : List (BitVec 32)} {qi qlen olen : Nat}
    (hc : VivClosedOk s implied ws1 ws2 qi qlen olen false)
    (_htrl_nodup : ∀ i j, i < s.core.trail_end → j < s.core.trail_end →
      (s.core.trl[i]?.getD 0#32).toNat / 2 = (s.core.trl[j]?.getD 0#32).toNat / 2 → i = j)
    {idx0 : Nat} (_hidx0 : idx0 < s.core.trail_end)
    (_htrl0 : (s.core.trl[idx0]?.getD 0#32).toNat / 2 = (ws1[qi]?.getD 0#32).toNat)
    (hrsn : s.core.rsns[(ws1[qi]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) :
    VivClosedOk s implied ws1 ws2 (qi + 1) qlen olen true := by
  intro k hk idx hidx htrl
  rcases (by omega : k < qi ∨ k = qi) with hk' | hk_eq
  · have hc' := hc k hk' idx hidx htrl
    by_cases hrsn_k :
        s.core.rsns[(ws1[k]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32
    · rw [ite_eq_left hrsn_k] at hc' ⊢; intro h; cases h
    · rw [ite_eq_right hrsn_k] at hc' ⊢; exact hc'
  · rw [hk_eq]
    rw [ite_eq_left hrsn]; intro h; cases h

theorem vivClosed_of_taut_true {s : FullState} {implied : BitVec 32}
    {ws1 ws2 ws2' : List (BitVec 32)} {qi qlen olen olen' : Nat}
    (hc : VivClosedOk s implied ws1 ws2 qi qlen olen true)
    (hrsn : s.core.rsns[(ws1[qi]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) :
    VivClosedOk s implied ws1 ws2' (qi + 1) qlen olen' true := by
  intro k hk idx hidx htrl
  rcases (by omega : k < qi ∨ k = qi) with hk' | hk_eq
  · have hc' := hc k hk' idx hidx htrl
    by_cases hrsn_k :
        s.core.rsns[(ws1[k]?.getD 0#32).toNat]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32
    · rw [ite_eq_left hrsn_k] at hc' ⊢; intro h; cases h
    · rw [ite_eq_right hrsn_k] at hc' ⊢; exact hc'
  · rw [hk_eq, ite_eq_left hrsn]; intro h; cases h


theorem viv_clear_mrk_init {c : FullCfg} {s : FullState} {mrk : List (BitVec 8)}
    {ws1 : List (BitVec 32)} {qlen : Nat}
    (hq : VivQueueOk c s mrk ws1 qlen) (hcv : s.core.cur_vars ≤ c.max_vars) :
    ∀ v < c.max_vars, mrk[v]?.getD 0#8 = 0#8 ∨
      ∃ k, 0 ≤ k ∧ k < qlen ∧ (ws1[k]?.getD 0#32).toNat = v := by
  intro v hv
  by_cases hv_cv : v < s.core.cur_vars
  · rcases hq.2.2.2.2.2.2.2.1 v hv_cv with h0 | h1
    · exact Or.inl h0
    · obtain ⟨k, hk, heq⟩ :=
        (mem_map_take_iff (by have := hq.2.1; have := hq.2.2.1; omega)).mp
          ((hq.2.2.2.2.2.2.1 v hv_cv).mp h1)
      exact Or.inr ⟨k, Nat.zero_le _, hk, heq⟩
  · exact Or.inl (hq.2.2.2.2.2.2.2.2 v (by omega) hv)

theorem viv_clear_mrk_step {c : FullCfg} {s : FullState} {mrk : List (BitVec 8)}
    {ws1 : List (BitVec 32)} {qi qlen : Nat}
    (hmrk_len : mrk.length = c.max_vars)
    (hws1_lt : ∀ i < qlen, (ws1[i]?.getD 0#32).toNat < s.core.cur_vars)
    (hcv : s.core.cur_vars ≤ c.max_vars) (hqi : qi < qlen)
    (hinv : ∀ v < c.max_vars,
      mrk[v]?.getD 0#8 = 0#8 ∨ ∃ k, qi ≤ k ∧ k < qlen ∧ (ws1[k]?.getD 0#32).toNat = v) :
    let v := (ws1[qi]?.getD 0#32).toNat
    v < mrk.length ∧
    ∀ u < c.max_vars, (mrk.set v 0#8)[u]?.getD 0#8 = 0#8 ∨
      ∃ k, qi + 1 ≤ k ∧ k < qlen ∧ (ws1[k]?.getD 0#32).toNat = u := by
  intro v; have hv_lt : v < c.max_vars := by have := hws1_lt qi hqi; omega
  refine ⟨by omega, fun u hu => ?_⟩
  by_cases huv : u = v
  · subst huv; left; rw [List.getElem?_set_self (by omega), Option.getD_some]
  · rw [List.getElem?_set_ne (Ne.symm huv)]
    refine (hinv u hu).elim Or.inl fun ⟨k, hk1, hk2, hkeq⟩ => Or.inr ?_
    exact ⟨k, by have : k ≠ qi := fun e => huv (e ▸ hkeq).symm; omega, hk2, hkeq⟩

theorem fullArenaClauseSize_le_maxVars {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState}
    (hsp : FullSparseInv c F0 s) (hw : FullWitnessInv c F0 F_cur s.core)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cref = false) :
    fullArenaClauseSize s cref ≤ c.max_vars := by
  have hcl := hsp.1.lengths.core_ok
  have hwf := hw.arena.refs_wf cref href
  have hbd : cref + 3 + fullArenaClauseSizeCore s.core cref ≤ s.core.arena.length := by
    have := hcl.arena_len_arr; have := hcl.arena_len_le; omega
  have hlen : (fullArenaClauseLits s cref).length = fullArenaClauseSize s cref := by
    unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSize
    simp [List.length_map, List.length_take, List.length_drop]; omega
  have hnd := hsp.2.2.1 cref href hng
  have hlt : ∀ x ∈ (fullArenaClauseLits s cref).map (· / 2), x < c.max_vars := by
    intro x hx; obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
    have := hw.arena.lits_lt cref href hng l hl; have := hcl.cur_vars_le; omega
  have hl := nodup_lt_length_le _ _ hnd hlt
  rwa [List.length_map, hlen] at hl

theorem vivSeed_mono_q {s : FullState} {cref implied : BitVec 32}
    {ws1 ws1' ws2 : List (BitVec 32)} {qlen qlen' olen : Nat} {taut : Bool}
    (hsd : VivSeedOk s cref implied ws1 ws2 qlen olen taut)
    (hql : qlen ≤ qlen') (hql' : qlen' ≤ ws1'.length) (hl1 : qlen ≤ ws1.length)
    (heq : ∀ j < qlen, ws1'[j]? = ws1[j]?) :
    VivSeedOk s cref implied ws1' ws2 qlen' olen taut := by
  intro hf; have hsd' := hsd hf
  have hmem : ∀ x, x ∈ (ws1.take qlen).map BitVec.toNat →
      x ∈ (ws1'.take qlen').map BitVec.toNat := fun x hx => by
    obtain ⟨j, hj, rfl⟩ := (mem_map_take_iff hl1).mp hx
    exact (mem_map_take_iff hql').mpr ⟨j, by omega, by rw [heq j hj]⟩
  by_cases himp : implied = 0xFFFFFFFF#32 <;>
    simp only [himp, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte] at hsd' ⊢
  · by_cases hct : s.core.confl_type = 1#64 <;> simp only [hct, ↓reduceIte] at hsd' ⊢
    · exact ⟨hsd'.1.elim Or.inl (fun hm => Or.inr (hmem _ hm)),
        hsd'.2.elim Or.inl (fun hm => Or.inr (hmem _ hm))⟩
    · exact fun l hl => (hsd' l hl).elim Or.inl (fun hm => Or.inr (hmem _ hm))
  · exact hsd'


end FullVivifyHelpers

end LeanQbe.T.Examples.Kissat.Full
