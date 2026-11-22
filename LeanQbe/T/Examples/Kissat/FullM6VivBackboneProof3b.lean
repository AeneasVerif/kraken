module

public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof3a
import LeanQbe.T.Examples.Kissat.FullVivTopLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# Kissat Wave-2 PR-W2C (`RC-20`) — Vivification Scheduler & Top-Level (`Proof3b`)

Certifies UNSAT-sound `Func.wp` (`XPost := False`, `0` SAT model proofs) for the `7` top-level
`RC-20` vivification scheduling and driver functions in `FullM6VivBackbone.lean`, culminating in
the canonical drop-in contract `FullFastBveBudgets.fullVivifyFastSpec`:
1. `full_viv_tier_match_m6_wp` (tier predicate)
2. `full_viv_collect_m6_wp` (2-pass unvivified-first candidate collection into `red_refs`)
3. `full_viv_count_m6_wp` (true `counts[lit]` accumulation into `tarjan_reach`)
4. `full_viv_keys_m6_wp` (top-2 count-weighted prefix keys `(k0, k1)`)
5. `full_viv_sort_sched_m6_wp` (Shell sort by unvivified-first + `counts[k0]`/`counts[k1]`)
6. `full_viv_clear_tier_m6_wp` (wrap-around `PH_VIV` clearing)
7. `full_vivify_m6_wp` (exact canonical `FullFastBveBudgets.fullVivifyFastSpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6VivBackbone

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test
open FullVivTopTactics FullVivTop
open scoped FullArenaTactics FullVivTopTactics

/-! ## 1. Cross-File Specifications (`6` Scheduler Helpers; `full_vivify_m6` Uses Canonical Spec) -/

section Specs

/-- `full_viv_tier_match_m6(h, hdr, tier_mode)`: read-only tier filter predicate. -/
@[expose] def fullVivTierMatchM6Spec : Spec [i64, i32, i64] [.bool] :=
  fun (h, _hdr, _tier_mode, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ (FullMem c s ⋆ R) m ∧ ∀ r, Q (r, ()) m

/-- `full_viv_collect_m6(h, tier_mode)`: 2-pass candidate collection (unvivified first, then
vivified) into `red_refs[3*k]`, mutating only `red_refs`. -/
@[expose] def fullVivCollectM6Spec : Spec [i64, i64] [i64] := fun (h, _tier_mode, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ bn rr' m',
      3 * bn.toNat ≤ c.red_cap → rr'.length = c.red_cap →
      (∀ k < bn.toNat, (rr'[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) →
      (FullMem c { s with scratch := { s.scratch with red_refs := rr' } } ⋆ R) m' → Q (bn, ()) m'

/-- `full_viv_count_m6(h, bn)`: zeroes `tarjan_reach[0 ..< 2*cur_vars)` and accumulates literal
occurrence counts across scheduled candidates `red_refs[3*bi]`, mutating only `tarjan_reach`. -/
@[expose] def fullVivCountM6Spec : Spec [i64, i64] [] := fun (h, bn, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ 3 * bn.toNat ≤ c.red_cap ∧
    (∀ k < bn.toNat, (s.scratch.red_refs[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ tr' m',
      tr'.length = 2 * c.max_vars →
      (FullMem c { s with scratch := { s.scratch with tarjan_reach := tr' } } ⋆ R) m' → Q () m'

/-- `full_viv_keys_m6(h, bn)`: computes top-2 count-weighted keys `(k0, k1)` into
`red_refs[3*bi+1..2]` reading `tarjan_reach`, preserving valid clause refs in `red_refs[3*k]`. -/
@[expose] def fullVivKeysM6Spec : Spec [i64, i64] [] := fun (h, bn, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ 3 * bn.toNat ≤ c.red_cap ∧
    (∀ k < bn.toNat, (s.scratch.red_refs[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ rr' m',
      rr'.length = c.red_cap →
      (∀ k < bn.toNat, (rr'[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) →
      (FullMem c { s with scratch := { s.scratch with red_refs := rr' } } ⋆ R) m' → Q () m'

/-- `full_viv_sort_sched_m6(h, bn)`: Shell sort on `red_refs[0 ..< 3*bn)` by unvivified-first and
`tarjan_reach` count-weighted `(k0, k1)` keys, preserving valid clause refs in `red_refs[3*k]`. -/
@[expose] def fullVivSortSchedM6Spec : Spec [i64, i64] [] := fun (h, bn, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ 3 * bn.toNat ≤ c.red_cap ∧
    (∀ k < bn.toNat, (s.scratch.red_refs[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ rr' m',
      rr'.length = c.red_cap →
      (∀ k < bn.toNat, (rr'[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) →
      (FullMem c { s with scratch := { s.scratch with red_refs := rr' } } ⋆ R) m' → Q () m'

/-- `full_viv_clear_tier_m6(h, tier_mode)`: wrap-around scan clearing `PH_VIV` on matching tier
clauses at level `0`, preserving `FullSparseInv`, `cur_level = 0`, and `fuel`. -/
@[expose] def fullVivClearTierM6Spec : Spec [i64, i64] [] := fun (h, _tier_mode, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ s.core.cur_level = 0 ∧ (FullMem c s ⋆ R) m ∧
    ∀ s' m',
      FullSparseInv c F0 s' → s'.core.cur_level = 0 → s'.core.fuel = s.core.fuel →
      (FullMem c s' ⋆ R) m' → Q () m'

end Specs

/-! ## 2. Private Helpers -/

section Helpers

private theorem m6b_sparse_with_tr {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {tr' : List (BitVec 32)} (htr : tr'.length = 2 * c.max_vars) :
    FullSparseInv c F0 { s with scratch := { s.scratch with tarjan_reach := tr' } } :=
  ⟨⟨⟨h.1.lengths.core_ok, { h.1.lengths.scratch_ok with tarjan_reach_len := htr }⟩, h.1.witness⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private theorem m6b_sparse_with_rr {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {rr' : List (BitVec 32)} (hrr : rr'.length = c.red_cap) :
    FullSparseInv c F0 { s with scratch := { s.scratch with red_refs := rr' } } :=
  ⟨⟨⟨h.1.lengths.core_ok, { h.1.lengths.scratch_ok with red_refs_len := hrr }⟩, h.1.witness⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private theorem m6b_sparseInvW_of_prop_canon {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' : Nat} {unass' unfl' : BitVec 64} {wvec' arena' wstk' : List (BitVec 32)}
    {wlen' : Nat} {wu' fuel' ctype' cref' c0' c1' oom' ticks' : BitVec 64}
    {wsort' : List (BitVec 32)} {phases' : List (BitVec 8)}
    (hlen' : ({ s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                            unassigned := unass', unflushed := unfl', wvec := wvec',
                            arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                            fuel := fuel', confl_type := ctype', confl_ref := cref',
                            confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
      scratch := { s.scratch with search_ticks := ticks', wsort := wsort', phases := phases' } } :
      FullState).LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                    trail_pos := tp', trail_end := te', propagated := prop',
                    unassigned := unass', unflushed := unfl', wvec := wvec', arena := arena',
                    wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                    confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                    confl_lit1 := c1', oom := oom' })
    (hperm : FullArenaPermEq s.core
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                    trail_pos := tp', trail_end := te', propagated := prop',
                    unassigned := unass', unflushed := unfl', wvec := wvec', arena := arena',
                    wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                    confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                    confl_lit1 := c1', oom := oom' }) :
    FullSparseInvW c F0 F_cur
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                              unassigned := unass', unflushed := unfl', wvec := wvec',
                              arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                              fuel := fuel', confl_type := ctype', confl_ref := cref',
                              confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
        scratch := { s.scratch with
          search_ticks := ticks', wsort := wsort', phases := phases' } } := by
  let s' : FullState :=
    { s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                            unassigned := unass', unflushed := unfl', wvec := wvec',
                            arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                            fuel := fuel', confl_type := ctype', confl_ref := cref',
                            confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
      scratch := { s.scratch with search_ticks := ticks', wsort := wsort', phases := phases' } }
  have hnd' : FullArenaVarsNodup s' := fun ref href hng => by
    have href0 : ref ∈ fullArenaClauseRefsCore s.core := hperm.2.1 ▸ href
    obtain ⟨_, hgb, hp⟩ := hperm.2.2 ref href0
    exact (hp.map (· / 2)).nodup_iff.mpr (hsp.2.2.2.1 ref href0 (hgb.symm.trans hng))
  have hrefs : ∀ ref ∈ fullArenaClauseRefs s, ref ∈ fullArenaClauseRefs s' := fun ref hr => by
    change ref ∈ fullArenaClauseRefsCore s'.core; rw [hperm.2.1]; exact hr
  exact FullVivTop.fullSparseInvW_of_prop_state hsp hlen' hw' hnd'
    ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hrefs

private theorem m6b_sched_set3_ok {rr : List (BitVec 32)} {cap bn j : Nat}
    {cr k0 k1 : BitVec 32} {refs : List Nat}
    (hlen : rr.length = cap) (h3 : 3 * bn ≤ cap) (hj : j < bn)
    (hok : ∀ k < bn, (rr[3 * k]?.getD 0#32).toNat ∈ refs) (hcr : cr.toNat ∈ refs) :
    let rr' := ((rr.set (3 * j) cr).set (3 * j + 1) k0).set (3 * j + 2) k1
    rr'.length = cap ∧ ∀ k < bn, (rr'[3 * k]?.getD 0#32).toNat ∈ refs := by
  refine ⟨by simp [hlen], fun k hk => ?_⟩
  have hne2 : 3 * j + 2 ≠ 3 * k := by omega
  have hne1 : 3 * j + 1 ≠ 3 * k := by omega
  rw [List.getElem?_set_ne hne2, List.getElem?_set_ne hne1]
  by_cases hkj : k = j
  · subst hkj
    rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hcr
  · rw [List.getElem?_set_ne (by omega)]; exact hok k hk

private theorem m6b_mul3_toNat {x : BitVec 64} (hx : 3 * x.toNat + 2 < 2 ^ 64) :
    (x * 3).toNat = 3 * x.toNat := by
  rw [BitVec.toNat_mul, show (3 : BitVec 64).toNat = 3 from rfl, Nat.mod_eq_of_lt (by omega)]
  omega

private theorem m6b_mul3_add1_toNat {x : BitVec 64} (hx : 3 * x.toNat + 2 < 2 ^ 64) :
    (x * 3 + 1).toNat = 3 * x.toNat + 1 := by
  rw [BitVec.toNat_add, m6b_mul3_toNat hx, show (1 : BitVec 64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega)]

private theorem m6b_mul3_add2_toNat {x : BitVec 64} (hx : 3 * x.toNat + 2 < 2 ^ 64) :
    (x * 3 + 2).toNat = 3 * x.toNat + 2 := by
  rw [BitVec.toNat_add, m6b_mul3_toNat hx, show (2 : BitVec 64).toNat = 2 from rfl,
    Nat.mod_eq_of_lt (by omega)]

private theorem m6b_add1_toNat {x : BitVec 64} (hx : x.toNat + 1 < 2 ^ 64) :
    (x + 1).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt hx]

private theorem m6b_sub_toNat {a b : BitVec 64} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)]

private theorem m6b_getElem_eq {α : Type} {l : List α} {i j : Nat}
    (hi : i < l.length) (hj : j < l.length) (h : i = j) : l[i] = l[j] := by
  subst h; rfl

private theorem m6b_bv32_clr_viv_garb (x : BitVec 32) :
    ((x &&& ~~~0x00100000#32) &&& 0x00080000#32) = (x &&& 0x00080000#32) := by
  rw [BitVec.and_assoc, show (~~~0x00100000#32 &&& 0x00080000#32) = 0x00080000#32 from rfl]

private theorem m6b_bv32_clr_viv_shrk (x : BitVec 32) :
    ((x &&& ~~~0x00100000#32) &&& 0x00800000#32) = (x &&& 0x00800000#32) := by
  rw [BitVec.and_assoc, show (~~~0x00100000#32 &&& 0x00800000#32) = 0x00800000#32 from rfl]

end Helpers

/-! ## 3. Vivification Scheduler & Top-Level `Func.wp` Proofs (`7` Functions) -/

section VivSchedProofs

theorem full_viv_tier_match_m6_wp (Γ : Env) :
    ∀ a m Q X, fullVivTierMatchM6Spec a m Q X →
      Func.wp Γ full_viv_tier_match_m6_body a m Q X := by
  rintro ⟨h, hdr, tier_mode, ⟨⟩⟩ m0 Q X ⟨c, s, R, rfl, hm0, hQ⟩
  unfold Func.wp full_viv_tier_match_m6_body
  fvt_steps <;> exact hQ _

theorem full_viv_collect_m6_wp (Γ : Env)
    (hNext : ∀ a m Q X, Full.fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hTierMatch : ∀ a m Q X, fullVivTierMatchM6Spec a m Q X →
      Γ "full_viv_tier_match_m6" [i64, i32, i64] [.bool] a m Q X) :
    ∀ a m Q X, fullVivCollectM6Spec a m Q X →
      Func.wp Γ full_viv_collect_m6_body a m Q X := by
  rintro ⟨h, tier_mode, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hsp0, hm0, hQ⟩
  have har_cap := c.harena; have hmx := c.hmaxv; have hrc := c.hred
  unfold dimacsBound at har_cap hmx hrc
  obtain ⟨F_cur0, hsw0⟩ := hsp0.exists_witness
  have hal0 : s.core.arena_len ≤ c.arena_cap := hsp0.1.lengths.core_ok.arena_len_le
  have har0_len : s.core.arena.length = c.arena_cap := hsp0.1.lengths.core_ok.arena_len_arr
  have hrr0_len : s.scratch.red_refs.length = c.red_cap := hsp0.1.lengths.scratch_ok.red_refs_len
  let bmax : BitVec 64 := BitVec.ofNat 64 c.red_cap / 3#64
  have hbmax_nat : bmax.toNat = c.red_cap / 3 := by
    dsimp only [bmax]
    rw [BitVec.toNat_udiv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      show (3#64 : BitVec 64).toNat = 3 from rfl]
  have h3bmax : 3 * bmax.toNat ≤ c.red_cap := by omega
  have h0_mem : 0 = s.core.arena_len ∨ 0 ∈ fullArenaClauseRefs s := by
    rcases Nat.eq_zero_or_pos s.core.arena_len with h0 | hpos
    · exact Or.inl h0.symm
    · exact Or.inr (fullArenaClauseRefs_zero_mem hsw0.2.1.arena hpos)
  unfold Func.wp full_viv_collect_m6_body
  fvt_steps
  -- Outer 2-pass loop `while (pass < 2ULL && bn < bmax)`
  refine wp_loop_inv (ts := [i64, i64])
    (fun (bn, pass, ()) mo => ∃ rro : List (BitVec 32),
      pass.toNat ≤ 2 ∧ bn.toNat ≤ bmax.toNat ∧ rro.length = c.red_cap ∧
      (∀ k < bn.toNat, (rro[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
      (FullMem c { s with scratch := { s.scratch with red_refs := rro } } ⋆ R) mo)
    (fun (_, pass, ()) _ => 2 - pass.toNat)
    (fun Jo hJo => by
      fvt_steps
      exact hJo (0#64, 0#64, ()) m0 ⟨s.scratch.red_refs, Nat.zero_le _, Nat.zero_le _,
        hrr0_len, fun _ hk => by simp at hk, hm0⟩)
    (fun Jo ⟨bn0, pass, ⟨⟩⟩ mo ⟨rro, hpass_le, hbn0_le, hrro_len, hoko, hmo⟩ iho => ?_)
  fvt_steps
  · have hpass_lt : pass.toNat < 2 := by c0_bound
    have hpass1 : (pass + 1#64).toNat = pass.toNat + 1 := by bv_omega
    -- Inner arena scan `while (p < h->arena_len)`
    refine wp_loop_inv (ts := [i64, i64])
      (fun (bn, p, ()) mp => ∃ rrp : List (BitVec 32),
        p.toNat ≤ s.core.arena_len ∧
        (p.toNat = s.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs s) ∧
        bn.toNat ≤ bmax.toNat ∧ rrp.length = c.red_cap ∧
        (∀ k < bn.toNat, (rrp[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
        (FullMem c { s with scratch := { s.scratch with red_refs := rrp } } ⋆ R) mp)
      (fun (_, p, ()) _ => s.core.arena_len - p.toNat)
      (fun J1 hJ1 => by
        fvt_steps
        exact hJ1 (bn0, 0#64, ()) mo ⟨rro, Nat.zero_le _, h0_mem, hbn0_le, hrro_len, hoko, hmo⟩)
      (fun J1 ⟨bn, p, ⟨⟩⟩ mp ⟨rrp, hp_le, hp_mem, hbn_le, hrrp_len, hokp, hmp⟩ ih1 => ?_)
    fvt_steps
    · have hp_lt : p.toNat < s.core.arena_len := by c0_bound
      have hp_ref : p.toNat ∈ fullArenaClauseRefs s := hp_mem.resolve_left (by omega)
      have hwfp := hsw0.2.1.arena.refs_wf p.toNat hp_ref
      have hp_lt_ar : p.toNat < s.core.arena.length := by omega
      have hp32 : (p.setWidth 32).toNat = p.toNat := by bv_omega
      fvt_steps
      c0_call hNext
      refine ⟨c, { s with scratch := { s.scratch with red_refs := rrp } },
        R, rfl, ⟨hsp0.1.lengths.core_ok,
          { hsp0.1.lengths.scratch_ok with red_refs_len := hrrp_len }⟩,
        hmp, ?_⟩
      let np_nat := fullArenaNextOff s.core.arena s.core.arena_len (p.setWidth 32).toNat
      have hnb : p.toNat < np_nat ∧ np_nat ≤ s.core.arena_len := by
        dsimp only [np_nat]; rw [hp32]; exact fullArenaNextOff_bounds hwfp.1
      have hnp_mem : np_nat = s.core.arena_len ∨ np_nat ∈ fullArenaClauseRefs s := by
        dsimp only [np_nat]; rw [hp32]
        exact fullArenaClauseRefs_next_mem_or_end hsw0.2.1.arena hp_ref
      have hnp_bv : ((BitVec.ofNat 32 np_nat).setWidth 64).toNat = np_nat := by
        rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega)]
      dsimp only; fvt_to_group
      refine wp_join_group (ts := [i64])
        (fun (bn', ()) mn => ∃ rrn : List (BitVec 32),
          bn'.toNat ≤ bmax.toNat ∧ rrn.length = c.red_cap ∧
          (∀ k < bn'.toNat, (rrn[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
          (FullMem c { s with scratch := { s.scratch with red_refs := rrn } } ⋆ R) mn) ?_ ?_
      · rintro _ ⟨bn', ⟨⟩⟩ mn ⟨rrn, hbn'_le, hrrn_len, hokn, hmn⟩
        fvt_steps
        exact ih1 (bn', (BitVec.ofNat 32 np_nat).setWidth 64, ()) mn
          (by dsimp only; rw [hnp_bv]; omega)
          ⟨rrn, by rw [hnp_bv]; exact hnb.2, by rw [hnp_bv]; exact hnp_mem,
            hbn'_le, hrrn_len, hokn, hmn⟩
      · intro Jn hJn
        fvt_to_group
        · -- `(hdr & PH_GARB) == 0u`: join `want = (pass == 0) ? ... : ...`
          refine wp_join_group (ts := [i32]) (fun _ mw => mw = mp) ?_
            (fun Jw hJw => by fvt_steps <;> exact hJw _ mp rfl)
          rintro _ ⟨_want, ⟨⟩⟩ mw hmw; rw [hmw]
          fvt_steps
          · c0_call hTierMatch
            refine ⟨c, { s with scratch := { s.scratch with red_refs := rrp } },
              R, rfl, hmp, fun _take => ?_⟩
            fvt_steps
            · have hbn_lt : bn.toNat < bmax.toNat := by dsimp only [bmax]; c0_bound
              have hbn3_nat : (bn * 3).toNat = 3 * bn.toNat := by bv_omega
              have hbn3_lt : (bn * 3).toNat < rrp.length := by omega
              have hbn1 : (bn + 1).toNat = bn.toNat + 1 := by bv_omega
              let rrp1 := rrp.set (3 * bn.toNat) (p.setWidth 32)
              have hrrp1_len : rrp1.length = c.red_cap := by simp [rrp1, hrrp_len]
              have hokp1 : ∀ k < (bn + 1).toNat,
                  (rrp1[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s := by
                intro k hk; rw [hbn1] at hk
                rcases (by omega : k < bn.toNat ∨ k = bn.toNat) with hk' | rfl
                · dsimp only [rrp1]; rw [List.getElem?_set_ne (by omega)]; exact hokp k hk'
                · dsimp only [rrp1]
                  rw [List.getElem?_set_self (by omega), Option.getD_some, hp32]
                  exact hp_ref
              fvt_steps
              exact hJn (bn + 1, ()) _ ⟨rrp1, by omega, hrrp1_len, hokp1,
                by simpa only [rrp1, hbn3_nat] using hm⟩
            · exact hJn (bn, ()) mp ⟨rrp, hbn_le, hrrp_len, hokp, hmp⟩
            · exact hJn (bn, ()) mp ⟨rrp, hbn_le, hrrp_len, hokp, hmp⟩
          · exact hJn (bn, ()) mp ⟨rrp, hbn_le, hrrp_len, hokp, hmp⟩
        · exact hJn (bn, ()) mp ⟨rrp, hbn_le, hrrp_len, hokp, hmp⟩
    · -- Inner loop exit: advance `pass + 1`
      fvt_steps
      exact iho (bn, pass + 1#64, ()) mp (by dsimp only; omega)
        ⟨rrp, by omega, hbn_le, hrrp_len, hokp, hmp⟩
  · exact hQ bn0 rro mo (by omega) hrro_len hoko hmo
  · exact hQ bn0 rro mo (by omega) hrro_len hoko hmo

theorem full_viv_count_m6_wp (Γ : Env) :
    ∀ a m Q X, fullVivCountM6Spec a m Q X →
      Func.wp Γ full_viv_count_m6_body a m Q X := by
  rintro ⟨h, bn, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hsp0, h3bn, hok0, hm0, hQ⟩
  have har_cap := c.harena; have hmx := c.hmaxv; have hrc := c.hred
  unfold dimacsBound at har_cap hmx hrc
  obtain ⟨F_cur0, hsw0⟩ := hsp0.exists_witness
  have hcv0_le : s.core.cur_vars ≤ c.max_vars := hsp0.1.lengths.core_ok.cur_vars_le
  have hal0 : s.core.arena_len ≤ c.arena_cap := hsp0.1.lengths.core_ok.arena_len_le
  have har0_len : s.core.arena.length = c.arena_cap := hsp0.1.lengths.core_ok.arena_len_arr
  have htr0_len : s.scratch.tarjan_reach.length = 2 * c.max_vars :=
    hsp0.1.lengths.scratch_ok.tarjan_reach_len
  have hrr0_len : s.scratch.red_refs.length = c.red_cap := hsp0.1.lengths.scratch_ok.red_refs_len
  let nlits : BitVec 64 := BitVec.ofNat 64 s.core.cur_vars <<< (BitVec.toNat (1 : BitVec 64) % 64)
  have hnlits_nat : nlits.toNat = 2 * s.core.cur_vars := by
    dsimp only [nlits]
    rw [show BitVec.toNat (1 : BitVec 64) % 64 = 1 from rfl, BitVec.toNat_shiftLeft,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (by omega)]
    omega
  have hnlits_le : nlits.toNat ≤ 2 * c.max_vars := by omega
  unfold Func.wp full_viv_count_m6_body
  fvt_steps
  -- Loop 1: zero `tarjan_reach[0 ..< nlits)`
  refine wp_loop_inv (ts := [i64])
    (fun (l, ()) ml => ∃ trl : List (BitVec 32),
      l.toNat ≤ nlits.toNat ∧ trl.length = 2 * c.max_vars ∧
      (FullMem c { s with scratch := { s.scratch with tarjan_reach := trl } } ⋆ R) ml)
    (fun (l, ()) _ => nlits.toNat - l.toNat)
    (fun Jl hJl => by
      fvt_steps; exact hJl (0#64, ()) m0 ⟨s.scratch.tarjan_reach, Nat.zero_le _, htr0_len, hm0⟩)
    (fun Jl ⟨l, ⟨⟩⟩ ml ⟨trl, hl_le, htrl_len, hml⟩ ihl => ?_)
  fvt_steps
  · have hl_lt : l.toNat < nlits.toNat := by c0_bound
    have hl_tr : l.toNat < trl.length := by omega
    have hl1 : (l + 1#64).toNat = l.toNat + 1 := by bv_omega
    fvt_steps
    exact ihl (l + 1#64, ()) _ (by dsimp only; omega)
      ⟨trl.set l.toNat 0#32, by omega, by simp [htrl_len], by assumption⟩
  · -- Loop 2: count occurrences across `bi < bn`
    refine wp_loop_inv (ts := [i64])
      (fun (bi, ()) mbi => ∃ trb : List (BitVec 32),
        bi.toNat ≤ bn.toNat ∧ trb.length = 2 * c.max_vars ∧
        (FullMem c { s with scratch := { s.scratch with tarjan_reach := trb } } ⋆ R) mbi)
      (fun (bi, ()) _ => bn.toNat - bi.toNat)
      (fun Jb hJb => by fvt_steps; exact hJb (0#64, ()) ml ⟨trl, Nat.zero_le _, htrl_len, hml⟩)
      (fun Jb ⟨bi, ⟨⟩⟩ mbi ⟨trb, hbi_le, htrb_len, hmbi⟩ ihb => ?_)
    fvt_steps
    · have hbi_lt : bi.toNat < bn.toNat := by c0_bound
      have hbi3_nat : (bi * 3#64).toNat = 3 * bi.toNat := m6b_mul3_toNat (by omega)
      have hbi3_lt : (bi * 3#64).toNat < s.scratch.red_refs.length := by omega
      let cr := s.scratch.red_refs[(bi * 3#64).toNat]'hbi3_lt
      have hcr_ref : cr.toNat ∈ fullArenaClauseRefs s := by
        have h := hok0 bi.toNat hbi_lt
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h
        have heq : cr = s.scratch.red_refs[3 * bi.toNat]'(by omega) := Option.some.inj (by
          rw [← List.getElem?_eq_getElem hbi3_lt, hbi3_nat, List.getElem?_eq_getElem (by omega)])
        rwa [heq]
      have hwfcr := hsw0.2.1.arena.refs_wf cr.toNat hcr_ref
      have hcr2_nat : (cr.setWidth 64 + 2#64).toNat = cr.toNat + 2 := by bv_omega
      have hcr2_lt : (cr.setWidth 64 + 2#64).toNat < s.core.arena.length := by omega
      let szc := s.core.arena[(cr.setWidth 64 + 2#64).toNat]'hcr2_lt
      have hszc_nat : szc.toNat = fullArenaClauseSizeCore s.core cr.toNat := by
        unfold fullArenaClauseSizeCore
        have hg : s.core.arena[cr.toNat + 2]? = some szc := by
          rw [← hcr2_nat, List.getElem?_eq_getElem hcr2_lt]
        rw [hg, Option.getD_some]
      have hbdc : cr.toNat + 3 + szc.toNat ≤ s.core.arena.length := by
        have := hwfcr.2.2.1; have := hwfcr.2.2.2.1; omega
      have hbi1 : (bi + 1#64).toNat = bi.toNat + 1 := m6b_add1_toNat (by omega)
      fvt_steps
      -- Inner clause-literal loop `while (k < szc)`
      refine wp_loop_inv (ts := [i32])
        (fun (k, ()) mk => ∃ trk : List (BitVec 32),
          k.toNat ≤ szc.toNat ∧ trk.length = 2 * c.max_vars ∧
          (FullMem c { s with scratch := { s.scratch with tarjan_reach := trk } } ⋆ R) mk)
        (fun (k, ()) _ => szc.toNat - k.toNat)
        (fun Jk hJk => by fvt_steps; exact hJk (0#32, ()) mbi ⟨trb, Nat.zero_le _, htrb_len, hmbi⟩)
        (fun Jk ⟨k, ⟨⟩⟩ mk ⟨trk, hk_le, htrk_len, hmk⟩ ihk => ?_)
      fvt_steps
      · have hk_lt : k.toNat < szc.toNat := by c0_bound
        have hk_idx : (cr.setWidth 64 + 3#64 + k.setWidth 64).toNat =
            cr.toNat + 3 + k.toNat := by bv_omega
        have hk_ar : (cr.setWidth 64 + 3#64 + k.setWidth 64).toNat <
            s.core.arena.length := by omega
        have hk1 : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
        fvt_to_group
        refine wp_join_group (ts := [])
          (fun () mn => ∃ trn : List (BitVec 32),
            trn.length = 2 * c.max_vars ∧
            (FullMem c { s with scratch := { s.scratch with tarjan_reach := trn } } ⋆ R) mn)
          (fun _ _ mn ⟨trn, htrn_len, hmn⟩ => by
            fvt_steps
            exact ihk (k + 1#32, ()) mn (by dsimp only; omega) ⟨trn, by omega, htrn_len, hmn⟩)
          fun Jn hJn => ?_
        c0_hsplit
        · let lit := s.core.arena[(cr.setWidth 64 + 3#64 + k.setWidth 64).toNat]'hk_ar
          have hlit_tr : (lit.setWidth 64).toNat < trk.length := by
            have hc0 : (lit.setWidth 64).toNat < nlits.toNat := by dsimp only [lit, cr]; c0_bound
            omega
          dsimp only [lit] at hlit_tr
          fvt_steps
          · refine hJn () _ ⟨_, ?_, by assumption⟩; simp [htrk_len]
          · exact hJn () mk ⟨trk, htrk_len, hmk⟩
        · fvt_steps; exact hJn () mk ⟨trk, htrk_len, hmk⟩
      · exact ihb (bi + 1#64, ()) mk (by dsimp only; omega) ⟨trk, by omega, htrk_len, hmk⟩
    · exact hQ trb mbi htrb_len hmbi

theorem full_viv_keys_m6_wp (Γ : Env) :
    ∀ a m Q X, fullVivKeysM6Spec a m Q X →
      Func.wp Γ full_viv_keys_m6_body a m Q X := by
  rintro ⟨h, bn, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hsp0, h3bn, hok0, hm0, hQ⟩
  have har_cap := c.harena; have hmx := c.hmaxv; have hrc := c.hred
  unfold dimacsBound at har_cap hmx hrc
  obtain ⟨F_cur0, hsw0⟩ := hsp0.exists_witness
  have hcv0_le : s.core.cur_vars ≤ c.max_vars := hsp0.1.lengths.core_ok.cur_vars_le
  have hal0 : s.core.arena_len ≤ c.arena_cap := hsp0.1.lengths.core_ok.arena_len_le
  have har0_len : s.core.arena.length = c.arena_cap := hsp0.1.lengths.core_ok.arena_len_arr
  have htr0_len : s.scratch.tarjan_reach.length = 2 * c.max_vars :=
    hsp0.1.lengths.scratch_ok.tarjan_reach_len
  have hrr0_len : s.scratch.red_refs.length = c.red_cap := hsp0.1.lengths.scratch_ok.red_refs_len
  let nlits : BitVec 64 := BitVec.ofNat 64 s.core.cur_vars <<< (BitVec.toNat (1 : BitVec 64) % 64)
  have hnlits_nat : nlits.toNat = 2 * s.core.cur_vars := by
    dsimp only [nlits]
    rw [show BitVec.toNat (1 : BitVec 64) % 64 = 1 from rfl, BitVec.toNat_shiftLeft,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (by omega)]
    omega
  have hnlits_le : nlits.toNat ≤ 2 * c.max_vars := by omega
  unfold Func.wp full_viv_keys_m6_body
  fvt_steps
  refine wp_loop_inv (ts := [i64])
    (fun (bi, ()) mbi => ∃ rri : List (BitVec 32),
      bi.toNat ≤ bn.toNat ∧ rri.length = c.red_cap ∧
      (∀ k < bn.toNat, (rri[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
      (FullMem c { s with scratch := { s.scratch with red_refs := rri } } ⋆ R) mbi)
    (fun (bi, ()) _ => bn.toNat - bi.toNat) ?_ ?_
  · intro J2 hJ2; fvt_steps
    exact hJ2 (0#64, ()) m0 ⟨s.scratch.red_refs, Nat.zero_le _, hrr0_len, hok0, hm0⟩
  · intro J2 ⟨bi, ⟨⟩⟩ mbi ⟨rri, hbi_le, hrri_len, hoki, hmbi⟩ ih2
    fvt_steps
    · have hbi_lt : bi.toNat < bn.toNat := by c0_bound
      have hbi3_nat : (bi * 3).toNat = 3 * bi.toNat := by bv_omega
      have hbi31_nat : (bi * 3 + 1).toNat = 3 * bi.toNat + 1 := by bv_omega
      have hbi32_nat : (bi * 3 + 2).toNat = 3 * bi.toNat + 2 := by bv_omega
      have hbi3_lt : (bi * 3).toNat < rri.length := by omega
      let cr := rri[(bi * 3).toNat]'hbi3_lt
      have hcr_ref : cr.toNat ∈ fullArenaClauseRefs s := by
        have h := hoki bi.toNat hbi_lt
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h
        have heq : cr = rri[3 * bi.toNat]'(by omega) := Option.some.inj (by
          rw [← List.getElem?_eq_getElem hbi3_lt, hbi3_nat,
            List.getElem?_eq_getElem (by omega)])
        rwa [heq]
      have hwfcr := hsw0.2.1.arena.refs_wf cr.toNat hcr_ref
      have hcr2_nat : (cr.setWidth 64 + 2).toNat = cr.toNat + 2 := by bv_omega
      have hcr2_lt : (cr.setWidth 64 + 2).toNat < s.core.arena.length := by omega
      let szc := s.core.arena[(cr.setWidth 64 + 2).toNat]'hcr2_lt
      have hszc_nat : szc.toNat = fullArenaClauseSizeCore s.core cr.toNat := by
        unfold fullArenaClauseSizeCore
        have hg : s.core.arena[cr.toNat + 2]? = some szc := by
          rw [← hcr2_nat, List.getElem?_eq_getElem hcr2_lt]
        rw [hg, Option.getD_some]
      have hbdc : cr.toNat + 3 + szc.toNat ≤ s.core.arena.length := by
        have := hwfcr.2.2.1; have := hwfcr.2.2.2.1; omega
      fvt_steps
      refine wp_loop_inv (ts := [i32, i32, i32, i32, i32])
        (fun (k0, d0, k1, d1, j, ()) mj => j.toNat ≤ szc.toNat ∧ mj = mbi)
        (fun (_, _, _, _, j, ()) _ => szc.toNat - j.toNat) ?_ ?_
      · intro Jk hJk; fvt_steps
        exact hJk (0xFFFFFFFF#32, 0#32, 0xFFFFFFFF#32, 0#32, 0#32, ()) mbi
          ⟨Nat.zero_le _, rfl⟩
      · intro Jk ⟨k0, d0, k1, d1, j, ⟨⟩⟩ mj ⟨hj_le, hmj⟩ ihk
        rw [hmj]; fvt_steps
        · have hj_lt : j.toNat < szc.toNat := by c0_bound
          have hj_idx : (cr.setWidth 64 + 3 + j.setWidth 64).toNat =
              cr.toNat + 3 + j.toNat := by bv_omega
          have hj_ar : (cr.setWidth 64 + 3 + j.setWidth 64).toNat <
              s.core.arena.length := by omega
          have hj1 : (j + 1).toNat = j.toNat + 1 := by bv_omega
          fvt_to_group
          refine wp_join_group (ts := [i32]) (fun _ mdl => mdl = mbi) ?_ ?_
          · rintro _ ⟨dl, ⟨⟩⟩ mdl hmdl; rw [hmdl]; fvt_to_group
            refine wp_join_group (ts := [i32, i32, i32, i32]) (fun _ mu => mu = mbi) ?_ ?_
            · rintro _ ⟨k0', d0', k1', d1', ⟨⟩⟩ mu hmu
              rw [hmu]; fvt_steps
              exact ihk (k0', d0', k1', d1', j + 1, ()) mbi
                (by dsimp only; omega) ⟨by omega, rfl⟩
            · intro Ju hJu
              fvt_steps <;> exact hJu _ mbi rfl
          · intro Jdl hJdl
            fvt_steps
            · let l := s.core.arena[(cr.setWidth 64 + 3 + j.setWidth 64).toNat]'hj_ar
              have hl_tr : (l.setWidth 64).toNat < s.scratch.tarjan_reach.length := by
                have hc0 : (l.setWidth 64).toNat < nlits.toNat := by dsimp only [l, cr]; c0_bound
                omega
              fvt_steps; exact hJdl _ mbi rfl
            · exact hJdl _ mbi rfl
        · have hbi31_lt : (bi * 3 + 1).toNat < rri.length := by omega
          have hbi32_lt : (bi * 3 + 2).toNat <
              (rri.set (bi * 3 + 1).toNat k0).length := by simp [hrri_len]; omega
          have hbi1 : (bi + 1).toNat = bi.toNat + 1 := by bv_omega
          fvt_steps
          let rri' := (rri.set (3 * bi.toNat + 1) k0).set (3 * bi.toNat + 2) k1
          have hoki' : ∀ k < bn.toNat,
              (rri'[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s := by
            intro k hk
            dsimp only [rri']
            rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
            exact hoki k hk
          exact ih2 (bi + 1, ()) _ (by dsimp only; omega)
            ⟨rri', by omega, by simp [rri', hrri_len], hoki',
              by simpa only [rri', hbi31_nat, hbi32_nat] using hm⟩
    · exact hQ rri mbi hrri_len hoki hmbi

theorem full_viv_sort_sched_m6_wp (Γ : Env) :
    ∀ a m Q X, fullVivSortSchedM6Spec a m Q X →
      Func.wp Γ full_viv_sort_sched_m6_body a m Q X := by
  rintro ⟨h, bn, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hsp0, h3bn, hok0, hm0, hQ⟩
  have hrc := c.hred; have hmx := c.hmaxv; have har_cap := c.harena
  unfold dimacsBound at hrc hmx har_cap
  obtain ⟨F_cur0, hsw0⟩ := hsp0.exists_witness
  have hlen := hsp0.1.lengths
  have hrr0_len : s.scratch.red_refs.length = c.red_cap := hlen.scratch_ok.red_refs_len
  have htr0_len : s.scratch.tarjan_reach.length = 2 * c.max_vars := hlen.scratch_ok.tarjan_reach_len
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hlen.core_ok.cur_vars_le
  have hal0 : s.core.arena_len ≤ c.arena_cap := hlen.core_ok.arena_len_le
  have har0_len : s.core.arena.length = c.arena_cap := hlen.core_ok.arena_len_arr
  have href_ar : ∀ ref ∈ fullArenaClauseRefs s, ref < s.core.arena.length := fun r hr => by
    have := (hsw0.2.1.arena.refs_wf r hr).1; omega
  clear hsw0 hsp0 hlen
  let nlits : BitVec 64 := BitVec.ofNat 64 s.core.cur_vars <<< (BitVec.toNat (1 : BitVec 64) % 64)
  have hnlits_nat : nlits.toNat = 2 * s.core.cur_vars := by
    dsimp only [nlits]
    rw [show BitVec.toNat (1 : BitVec 64) % 64 = 1 from rfl, BitVec.toNat_shiftLeft,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (by omega)]
    omega
  have hnlits_le : nlits.toNat ≤ 2 * c.max_vars := by omega
  unfold Func.wp full_viv_sort_sched_m6_body
  c0_hsteps_nogrp
  -- Outer loop on `gap`: `while (gap > 0ULL)`
  refine wp_loop_inv (ts := [i64])
    (fun (gap, ()) mg => ∃ rr : List (BitVec 32),
      gap.toNat ≤ bn.toNat ∧ rr.length = c.red_cap ∧
      (∀ k < bn.toNat, (rr[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
      (FullMem c { s with scratch := { s.scratch with red_refs := rr } } ⋆ R) mg)
    (fun (gap, ()) _ => gap.toNat)
    (fun Jg hJg => by
      c0_hsteps
      have hshr : (bn >>> (BitVec.toNat (1#64 : BitVec 64) % 64)).toNat = bn.toNat / 2 := by
        rw [show BitVec.toNat (1#64 : BitVec 64) % 64 = 1 from rfl, BitVec.toNat_ushiftRight,
          Nat.shiftRight_eq_div_pow]
      exact hJg (bn >>> (BitVec.toNat (1#64 : BitVec 64) % 64), ()) m0
        ⟨s.scratch.red_refs, by rw [hshr]; omega, hrr0_len, hok0, hm0⟩)
    (fun Jg ⟨gap, ⟨⟩⟩ mg ⟨rrg, hgap_le, hrrg_len, hokg, hmg⟩ ihg => ?_)
  c0_hsteps_nogrp
  · have hgap_pos : 0 < gap.toNat := by c0_bound
    -- Middle loop on `si`: `while (si < bn)`
    refine wp_loop_inv (ts := [i64])
      (fun (si, ()) msi => ∃ rrs : List (BitVec 32),
        gap.toNat ≤ si.toNat ∧ si.toNat ≤ bn.toNat ∧ rrs.length = c.red_cap ∧
        (∀ k < bn.toNat, (rrs[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
        (FullMem c { s with scratch := { s.scratch with red_refs := rrs } } ⋆ R) msi)
      (fun (si, ()) _ => bn.toNat - si.toNat)
      (fun Ji hJi => by
        c0_hsteps
        exact hJi (gap, ()) mg ⟨rrg, Nat.le_refl _, hgap_le, hrrg_len, hokg, hmg⟩)
      (fun Ji ⟨si, ⟨⟩⟩ msi ⟨rrs, hgsi, hsi_le, hrrs_len, hoks, hmsi⟩ ihi => ?_)
    c0_hsteps_nogrp
    · have hsi_lt : si.toNat < bn.toNat := by c0_bound
      have hsb_nat : (si * 3).toNat = 3 * si.toNat := m6b_mul3_toNat (by omega)
      have hsb1_nat : (si * 3 + 1).toNat = 3 * si.toNat + 1 := m6b_mul3_add1_toNat (by omega)
      have hsb2_nat : (si * 3 + 2).toNat = 3 * si.toNat + 2 := m6b_mul3_add2_toNat (by omega)
      have hsb_lt : (si * 3).toNat < rrs.length := by omega
      have hsb1_lt : (si * 3 + 1).toNat < rrs.length := by omega
      have hsb2_lt : (si * 3 + 2).toNat < rrs.length := by omega
      let cr := rrs[(si * 3).toNat]'hsb_lt
      let k0 := rrs[(si * 3 + 1).toNat]'hsb1_lt
      let k1 := rrs[(si * 3 + 2).toNat]'hsb2_lt
      have hcr_ref : cr.toNat ∈ fullArenaClauseRefs s := by
        have h := hoks si.toNat hsi_lt
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h
        have heq : cr = rrs[3 * si.toNat]'(by omega) := Option.some.inj (by
          rw [← List.getElem?_eq_getElem hsb_lt, hsb_nat, List.getElem?_eq_getElem (by omega)])
        rwa [heq]
      have hcr_ar : (cr.setWidth 64).toNat < s.core.arena.length := by
        rw [bv32_setWidth64_toNat]; exact href_ar cr.toNat hcr_ref
      dsimp only [cr] at hcr_ar
      c0_hsteps_nogrp
      -- Join `dk0 = ((u64)k0 < nlits) ? cnt[k0] : 0u`
      refine wp_join_group (ts := [i32]) (fun _ md0 => md0 = msi) ?_
        (fun Jd0 hJd0 => by
          c0_hsteps
          · have hk0_tr : (k0.setWidth 64).toNat < s.scratch.tarjan_reach.length := by
              have hc0 : (k0.setWidth 64).toNat < nlits.toNat := by dsimp only [k0]; c0_bound
              omega
            dsimp only [k0] at hk0_tr
            c0_hsteps; exact hJd0 _ msi rfl
          · exact hJd0 _ msi rfl)
      rintro _ ⟨dk0, ⟨⟩⟩ md0 hmd0; rw [hmd0]; c0_hsteps_nogrp
      -- Join `dk1 = ((u64)k1 < nlits) ? cnt[k1] : 0u`
      refine wp_join_group (ts := [i32]) (fun _ md1 => md1 = msi) ?_
        (fun Jd1 hJd1 => by
          c0_hsteps
          · have hk1_tr : (k1.setWidth 64).toNat < s.scratch.tarjan_reach.length := by
              have hc0 : (k1.setWidth 64).toNat < nlits.toNat := by dsimp only [k1]; c0_bound
              omega
            dsimp only [k1] at hk1_tr
            c0_hsteps; exact hJd1 _ msi rfl
          · exact hJd1 _ msi rfl)
      rintro _ ⟨dk1, ⟨⟩⟩ md1 hmd1; rw [hmd1]; c0_hsteps_nogrp
      -- Inner gap-shift loop on `sj`: `while (sj >= gap)` with `break`
      refine wp_loop_break_group (brkTs := [i64]) (lpTs := [i64])
        (fun (sj_b, ()) mb => ∃ rrb : List (BitVec 32),
          sj_b.toNat < bn.toNat ∧ rrb.length = c.red_cap ∧
          (∀ k < bn.toNat, (rrb[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
          (FullMem c { s with scratch := { s.scratch with red_refs := rrb } } ⋆ R) mb)
        (fun rem (sj, ()) mj => ∃ rrj : List (BitVec 32),
          sj.toNat < bn.toNat ∧ rem = sj.toNat ∧ rrj.length = c.red_cap ∧
          (∀ k < bn.toNat, (rrj[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
          (FullMem c { s with scratch := { s.scratch with red_refs := rrj } } ⋆ R) mj)
        ?_ ?_ ?_
      · rintro _ ⟨sj_b, ⟨⟩⟩ mb ⟨rrb, hsjb_lt, hrrb_len, hokb, hmb⟩
        have hfb_nat : (sj_b * 3).toNat = 3 * sj_b.toNat := m6b_mul3_toNat (by omega)
        have hfb1_nat : (sj_b * 3 + 1).toNat = 3 * sj_b.toNat + 1 :=
          m6b_mul3_add1_toNat (by omega)
        have hfb2_nat : (sj_b * 3 + 2).toNat = 3 * sj_b.toNat + 2 :=
          m6b_mul3_add2_toNat (by omega)
        have hfb_lt : (sj_b * 3).toNat < rrb.length := by omega
        have hfb1_lt : (sj_b * 3 + 1).toNat <
            (rrb.set (sj_b * 3).toNat cr).length := by rw [List.length_set]; omega
        have hfb2_lt : (sj_b * 3 + 2).toNat <
            ((rrb.set (sj_b * 3).toNat cr).set (sj_b * 3 + 1).toNat k0).length := by
          rw [List.length_set, List.length_set]; omega
        have hsi1 : (si + 1).toNat = si.toNat + 1 := m6b_add1_toNat (by omega)
        c0_hsteps
        let rrf := ((rrb.set (3 * sj_b.toNat) cr).set (3 * sj_b.toNat + 1) k0).set
          (3 * sj_b.toNat + 2) k1
        obtain ⟨hrrf_len, hokf⟩ := m6b_sched_set3_ok hrrb_len h3bn hsjb_lt hokb hcr_ref
        exact ihi (si + 1, ()) _ (by dsimp only; omega)
          ⟨rrf, by omega, by omega, hrrf_len, hokf,
            by dsimp only [rrf]; rw [hfb_nat, hfb1_nat, hfb2_nat] at hm; exact hm⟩
      · intro B L rem ⟨sj, ⟨⟩⟩ mj hB hL ⟨rrj, hsj_lt, hrem, hrrj_len, hokj, hmj⟩
        subst hrem
        have hbrk : B (sj, ()) mj := hB (sj, ()) mj ⟨rrj, hsj_lt, hrrj_len, hokj, hmj⟩
        c0_hsteps_nogrp
        · have hsj_ge : gap.toNat ≤ sj.toNat := by c0_bound
          have hpj_nat : (sj - gap).toNat = sj.toNat - gap.toNat := m6b_sub_toNat hsj_ge
          have hpj_lt : (sj - gap).toNat < bn.toNat := by omega
          have hpb_nat : ((sj - gap) * 3).toNat = 3 * (sj - gap).toNat :=
            m6b_mul3_toNat (by omega)
          have hpb1_nat : ((sj - gap) * 3 + 1).toNat = 3 * (sj - gap).toNat + 1 :=
            m6b_mul3_add1_toNat (by omega)
          have hpb2_nat : ((sj - gap) * 3 + 2).toNat = 3 * (sj - gap).toNat + 2 :=
            m6b_mul3_add2_toNat (by omega)
          have hpb_lt : ((sj - gap) * 3).toNat < rrj.length := by omega
          have hpb1_lt : ((sj - gap) * 3 + 1).toNat < rrj.length := by omega
          have hpb2_lt : ((sj - gap) * 3 + 2).toNat < rrj.length := by omega
          let pcr := rrj[((sj - gap) * 3).toNat]'hpb_lt
          let pk0 := rrj[((sj - gap) * 3 + 1).toNat]'hpb1_lt
          let pk1 := rrj[((sj - gap) * 3 + 2).toNat]'hpb2_lt
          have hpcr_ref : pcr.toNat ∈ fullArenaClauseRefs s := by
            have h := hokj (sj - gap).toNat hpj_lt
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h
            have heq : pcr = rrj[3 * (sj - gap).toNat]'(by omega) := Option.some.inj (by
              rw [← List.getElem?_eq_getElem hpb_lt, hpb_nat, List.getElem?_eq_getElem (by omega)])
            rwa [heq]
          have hpcr_ar : (pcr.setWidth 64).toNat < s.core.arena.length := by
            rw [bv32_setWidth64_toNat]; exact href_ar pcr.toNat hpcr_ref
          dsimp only [pcr] at hpcr_ar
          c0_hsteps_nogrp
          -- Join `dpk0`
          refine wp_join_group (ts := [i32]) (fun _ mp0 => mp0 = mj) ?_
            (fun Jp0 hJp0 => by
              c0_hsteps
              · have hpk0_tr : (pk0.setWidth 64).toNat < s.scratch.tarjan_reach.length := by
                  have hc0 : (pk0.setWidth 64).toNat < nlits.toNat := by dsimp only [pk0]; c0_bound
                  omega
                dsimp only [pk0] at hpk0_tr
                c0_hsteps; exact hJp0 _ mj rfl
              · exact hJp0 _ mj rfl)
          rintro _ ⟨dpk0, ⟨⟩⟩ mp0 hmp0; rw [hmp0]; c0_hsteps_nogrp
          -- Join `dpk1`
          refine wp_join_group (ts := [i32]) (fun _ mp1 => mp1 = mj) ?_
            (fun Jp1 hJp1 => by
              c0_hsteps
              · have hpk1_tr : (pk1.setWidth 64).toNat < s.scratch.tarjan_reach.length := by
                  have hc0 : (pk1.setWidth 64).toNat < nlits.toNat := by dsimp only [pk1]; c0_bound
                  omega
                dsimp only [pk1] at hpk1_tr
                c0_hsteps; exact hJp1 _ mj rfl
              · exact hJp1 _ mj rfl)
          rintro _ ⟨dpk1, ⟨⟩⟩ mp1 hmp1; rw [hmp1]
          -- Join after `if (!pv0 && v0)` and `if (pv0 == v0)` -> single shift copy!
          c0_hsteps_nogrp
          refine wp_join_group (ts := []) (fun () ms => ms = mj)
            (fun _ _ ms hms => by
              rw [hms]
              refine wp_join_group (ts := []) (fun () ms2 => ms2 = mj)
                (fun _ _ ms2 hms2 => by
                  rw [hms2]
                  have hjb_nat : (sj * 3).toNat = 3 * sj.toNat := m6b_mul3_toNat (by omega)
                  have hjb1_nat : (sj * 3 + 1).toNat = 3 * sj.toNat + 1 :=
                    m6b_mul3_add1_toNat (by omega)
                  have hjb2_nat : (sj * 3 + 2).toNat = 3 * sj.toNat + 2 :=
                    m6b_mul3_add2_toNat (by omega)
                  have hjb_lt : (sj * 3).toNat < rrj.length := by omega
                  have hjb1_lt : (sj * 3 + 1).toNat <
                      (rrj.set (sj * 3).toNat pcr).length := by rw [List.length_set]; omega
                  have hjb2_lt : (sj * 3 + 2).toNat <
                      ((rrj.set (sj * 3).toNat pcr).set (sj * 3 + 1).toNat pk0).length := by
                    rw [List.length_set, List.length_set]; omega
                  c0_hsteps
                  let rrj' := ((rrj.set (3 * sj.toNat) pcr).set (3 * sj.toNat + 1) pk0).set
                    (3 * sj.toNat + 2) pk1
                  obtain ⟨hrrj'_len, hokj'⟩ :=
                    m6b_sched_set3_ok hrrj_len h3bn hsj_lt hokj hpcr_ref
                  exact hL (sj - gap).toNat (sj - gap, ()) _ (by omega)
                    ⟨rrj', hpj_lt, rfl, hrrj'_len, hokj',
                      by dsimp only [rrj']; rw [hjb_nat, hjb1_nat, hjb2_nat] at hm; exact hm⟩)
                fun Jv hJv => by
                  repeat' (first
                    | exact hbrk
                    | exact hJv () mj rfl
                    | (refine head_wp_jnz rfl (fun _ => ?_) (fun _ => ?_))
                    | (refine wp_unroll_group fun _ _ => ?_)
                    | c0_hstep))
            fun Jp hJp => by
              repeat' (first
                | exact hbrk
                | exact hJp () mj rfl
                | (refine head_wp_jnz rfl (fun _ => ?_) (fun _ => ?_))
                | (refine wp_unroll_group fun _ _ => ?_)
                | c0_hstep)
        · exact hbrk
      · intro B L _ hL
        c0_hsteps
        exact hL si.toNat (si, ()) msi ⟨rrs, hsi_lt, rfl, hrrs_len, hoks, hmsi⟩
    · have hshr : (gap >>> (BitVec.toNat (1#64 : BitVec 64) % 64)).toNat = gap.toNat / 2 := by
        rw [show BitVec.toNat (1#64 : BitVec 64) % 64 = 1 from rfl, BitVec.toNat_ushiftRight,
          Nat.shiftRight_eq_div_pow]
      exact ihg (gap >>> (BitVec.toNat (1#64 : BitVec 64) % 64), ()) msi
        (by dsimp only; rw [hshr]; omega)
        ⟨rrs, by rw [hshr]; omega, hrrs_len, hoks, hmsi⟩
  · exact hQ rrg mg hrrg_len hokg hmg

theorem full_viv_clear_tier_m6_wp (Γ : Env)
    (hNext : ∀ a m Q X, Full.fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hTierMatch : ∀ a m Q X, fullVivTierMatchM6Spec a m Q X →
      Γ "full_viv_tier_match_m6" [i64, i32, i64] [.bool] a m Q X) :
    ∀ a m Q X, fullVivClearTierM6Spec a m Q X →
      Func.wp Γ full_viv_clear_tier_m6_body a m Q X := by
  rintro ⟨h, tier_mode, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hsp0, hcl0, hm0, hQ⟩
  have har_cap := c.harena; unfold dimacsBound at har_cap
  unfold Func.wp full_viv_clear_tier_m6_body
  fvt_steps
  refine wp_loop_inv (ts := [i64])
    (fun (q, ()) mq => ∃ sq : FullState,
      sq.core.arena_len ≤ c.arena_cap ∧ q.toNat ≤ sq.core.arena_len ∧
      (q.toNat = sq.core.arena_len ∨ q.toNat ∈ fullArenaClauseRefs sq) ∧
      FullSparseInv c F0 sq ∧ sq.core.cur_level = 0 ∧ sq.core.fuel = s.core.fuel ∧
      (FullMem c sq ⋆ R) mq)
    (fun (q, ()) _ => c.arena_cap - q.toNat) ?_ ?_
  · intro Jq hJq; fvt_steps
    obtain ⟨F_cur0, hsw0⟩ := hsp0.exists_witness
    have h0_mem : 0 = s.core.arena_len ∨ 0 ∈ fullArenaClauseRefs s := by
      rcases Nat.eq_zero_or_pos s.core.arena_len with h0 | hpos
      · exact Or.inl h0.symm
      · exact Or.inr (fullArenaClauseRefs_zero_mem hsw0.2.1.arena hpos)
    exact hJq (0#64, ()) m0 ⟨s, hsp0.1.lengths.core_ok.arena_len_le, Nat.zero_le _, h0_mem,
      hsp0, hcl0, rfl, hm0⟩
  · intro Jq ⟨q, ⟨⟩⟩ mq ⟨sq, halq, hq_le, hq_mem, hspq, hclq, hflq, hmq⟩ ihq
    fvt_steps
    · have hq_lt : q.toNat < sq.core.arena_len := by c0_bound
      have hq_ref : q.toNat ∈ fullArenaClauseRefs sq := hq_mem.resolve_left (by omega)
      obtain ⟨F_curq, hswq⟩ := hspq.exists_witness
      have hq_lt_ar : q.toNat < sq.core.arena.length := by
        have := hspq.1.lengths.core_ok.arena_len_arr; omega
      have hq32 : (q.setWidth 32).toNat = q.toNat := by bv_omega
      let hdrq := sq.core.arena[q.toNat]'hq_lt_ar
      have hhdrq : fullArenaHdr sq q.toNat = hdrq := by
        unfold fullArenaHdr fullArenaHdrCore
        rw [List.getElem?_eq_getElem hq_lt_ar, Option.getD_some]
      fvt_to_group
      refine wp_join_group (ts := [])
        (fun () mq2 => ∃ sq2 : FullState,
          sq2.core.arena_len = sq.core.arena_len ∧ sq2.core.arena_len ≤ c.arena_cap ∧
          FullSparseInv c F0 sq2 ∧ sq2.core.cur_level = 0 ∧ sq2.core.fuel = s.core.fuel ∧
          q.toNat ∈ fullArenaClauseRefs sq2 ∧ (FullMem c sq2 ⋆ R) mq2) ?_ ?_
      · rintro _ ⟨⟩ mq2 ⟨sq2, _, halq2, hspq2, hclq2, hflq2, hq_ref2, hmq2⟩
        fvt_steps
        c0_call hNext
        refine ⟨c, sq2, R, rfl, hspq2.1.lengths, hmq2, ?_⟩
        obtain ⟨F_curq2, hswq2⟩ := hspq2.exists_witness
        have hwfq2 := hswq2.2.1.arena.refs_wf q.toNat hq_ref2
        let nq_nat := fullArenaNextOff sq2.core.arena sq2.core.arena_len q.toNat
        have hnb : q.toNat < nq_nat ∧ nq_nat ≤ sq2.core.arena_len := by
          dsimp only [nq_nat]; simpa using fullArenaNextOff_bounds hwfq2.1
        have hnq_mem : nq_nat = sq2.core.arena_len ∨ nq_nat ∈ fullArenaClauseRefs sq2 :=
          fullArenaClauseRefs_next_mem_or_end hswq2.2.1.arena hq_ref2
        have hnq_bv : ((BitVec.ofNat 32 nq_nat).setWidth 64).toNat = nq_nat := by
          rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
            Nat.mod_eq_of_lt (by omega)]
        simp only [hq32]
        exact ihq ((BitVec.ofNat 32 nq_nat).setWidth 64, ()) _ (by dsimp only; rw [hnq_bv]; omega)
          ⟨sq2, halq2, by rw [hnq_bv]; exact hnb.2, by rw [hnq_bv]; exact hnq_mem,
            hspq2, hclq2, hflq2, hmq2⟩
      · intro Jn2 hJn2
        fvt_steps
        · c0_call hTierMatch
          refine ⟨c, sq, R, rfl, hmq, fun _take => ?_⟩
          fvt_steps
          · let hdrq' := hdrq &&& ~~~0x00100000#32
            obtain ⟨hsw_cl, hrefs_cl, _⟩ :=
              fullSparseInvW_set_hdr_non_gs hswq hq_ref hdrq'
                sq.core.num_irred sq.core.num_redundant
                (by rw [hhdrq]; exact m6b_bv32_clr_viv_garb hdrq)
                (by rw [hhdrq]; exact m6b_bv32_clr_viv_shrk hdrq)
            let s_cl : FullState :=
              { sq with core := { sq.core with arena := sq.core.arena.set q.toNat hdrq' } }
            exact hJn2 () _ ⟨s_cl, rfl, halq, hsw_cl.toSparse, hclq, hflq,
              by rw [hrefs_cl]; exact hq_ref, by assumption⟩
          · exact hJn2 () mq ⟨sq, rfl, halq, hspq, hclq, hflq, hq_ref, hmq⟩
        · exact hJn2 () mq ⟨sq, rfl, halq, hspq, hclq, hflq, hq_ref, hmq⟩
    · exact hQ sq mq hspq hclq hflq hmq

theorem full_vivify_m6_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hCollect : ∀ a m Q X, fullVivCollectM6Spec a m Q X →
      Γ "full_viv_collect_m6" [i64, i64] [i64] a m Q X)
    (hCount : ∀ a m Q X, fullVivCountM6Spec a m Q X →
      Γ "full_viv_count_m6" [i64, i64] [] a m Q X)
    (hKeys : ∀ a m Q X, fullVivKeysM6Spec a m Q X →
      Γ "full_viv_keys_m6" [i64, i64] [] a m Q X)
    (hSortSched : ∀ a m Q X, fullVivSortSchedM6Spec a m Q X →
      Γ "full_viv_sort_sched_m6" [i64, i64] [] a m Q X)
    (hVivClause : ∀ a m Q X, fullVivClauseM6Spec a m Q X →
      Γ "full_viv_clause_m6" [i64, i32] [i64] a m Q X)
    (hProp : ∀ a m Q X, Full.fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hClearTier : ∀ a m Q X, fullVivClearTierM6Spec a m Q X →
      Γ "full_viv_clear_tier_m6" [i64, i64] [] a m Q X) :
    ∀ a m Q X, FullFastBveBudgets.fullVivifyFastSpec a m Q X →
      Func.wp Γ full_vivify_m6_body a m Q X := by
  rintro ⟨h, tier_mode, budget0, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hsp0, hm0, hQ⟩
  have har_cap := c.harena; have hmx := c.hmaxv; have hrc := c.hred
  unfold dimacsBound at har_cap hmx hrc
  unfold Func.wp full_vivify_m6_body; fvt_to_group
  · fvt_steps
    exact hQ 1#64 s m0 hsp0 id id (fun hnz => absurd (by c0_bound) hnz)
      (Nat.le_refl _) (Or.inl rfl) (fun h => by cases h) hm0
  -- Entry backtrack to level 0
  refine wp_join_group (ts := [])
    (fun () m1 => ∃ s1 : FullState, FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m1) ?_ ?_
  · rintro _ ⟨⟩ m1 ⟨s1, hsp1, hcl1, hfl1, hm1⟩
    fvt_to_group
    refine wp_join_group (ts := [i64]) (fun _ md => md = m1) ?_
      (fun Jd hJd => by fvt_steps <;> exact hJd _ m1 rfl)
    rintro _ ⟨delta, ⟨⟩⟩ md hmd; rw [hmd]
    fvt_to_group
    refine wp_join_group (ts := [i64]) (fun _ me => me = m1) ?_
      (fun Je hJe => by fvt_steps <;> exact hJe _ m1 rfl)
    rintro _ ⟨eff_ref, ⟨⟩⟩ me hme; rw [hme]
    fvt_to_group
    refine wp_join_group (ts := [i64]) (fun _ mtc => mtc = m1) ?_
      (fun Jtc hJtc => by fvt_steps <;> exact hJtc _ m1 rfl)
    rintro _ ⟨tick_cap, ⟨⟩⟩ mtc hmtc; rw [hmtc]
    fvt_steps
    let s2 : FullState := { s1 with core := { s1.core with probing := 1#64 } }
    have hsp2 : FullSparseInv c F0 s2 := FullVivTop.FullSparseInv.with_probing hsp1 1#64
    have hm2 : (FullMem c s2 ⋆ R) m := hm
    have hfl2 : s2.core.fuel.toNat ≤ s.core.fuel.toNat := hfl1
    clear_value s2
    clear hsp1 hcl1 hfl1 hm
    -- Pass 1: collect candidate clause refs into `red_refs`
    c0_call hCollect
    refine ⟨c, F0, s2, R, rfl, hsp2, hm2, fun bn rr3 m3 h3bn hrr3 hok3 hm3 => ?_⟩
    let s3 : FullState := { s2 with scratch := { s2.scratch with red_refs := rr3 } }
    have hsp3 : FullSparseInv c F0 s3 := m6b_sparse_with_rr hsp2 hrr3
    -- Pass 2: accumulate true literal counts into `tarjan_reach`
    c0_call hCount
    refine ⟨c, F0, s3, R, rfl, hsp3, h3bn, hok3, hm3, fun tr3 m3c htr3 hm3c => ?_⟩
    let s3c : FullState := { s3 with scratch := { s3.scratch with tarjan_reach := tr3 } }
    have hsp3c : FullSparseInv c F0 s3c := m6b_sparse_with_tr hsp3 htr3
    -- Pass 3: compute top-2 `(k0, k1)` keys in `red_refs`
    c0_call hKeys
    refine ⟨c, F0, s3c, R, rfl, hsp3c, h3bn, hok3, hm3c, fun rr4 m4 hrr4 hok4 hm4 => ?_⟩
    let s4 : FullState := { s3c with scratch := { s3c.scratch with red_refs := rr4 } }
    have hsp4 : FullSparseInv c F0 s4 := m6b_sparse_with_rr hsp3c hrr4
    -- Pass 4: shellsort schedule in `red_refs`
    c0_call hSortSched
    refine ⟨c, F0, s4, R, rfl, hsp4, h3bn, hok4, hm4,
      fun rr5 m5 hrr5_len hok5 hm5 => ?_⟩
    let s5 : FullState := { s4 with scratch := { s4.scratch with red_refs := rr5 } }
    have hsp5 : FullSparseInv c F0 s5 := m6b_sparse_with_rr hsp4 hrr5_len
    have hfl5 : s5.core.fuel.toNat ≤ s.core.fuel.toNat := hfl2
    have hrefs5 : fullArenaClauseRefs s5 = fullArenaClauseRefs s2 := rfl
    have hrr5 : s5.scratch.red_refs = rr5 := rfl
    have hok5' : ∀ k < bn.toNat, (rr5[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s2 := hok5
    have hm5' : (FullMem c s5 ⋆ R) m5 := hm5
    clear_value s5 s4 s3c s3
    clear s4 s3c s3 hsp4 hsp3c hsp3 tr3 rr3 rr4 htr3 hrr3 hrr4 hok3 hok4 hok5
      hm3 hm3c hm4 hm5 hsp2 hm2 hfl2 hCollect hCount hKeys hSortSched
    fvt_to_group
    -- Pass 5: Vivify sorted candidates `while (bi < bn && ...)`
    refine wp_loop_break_group (brkTs := [i64, i64, i64]) (lpTs := [i64, i64])
      (fun (_budget_b, res_b, bi_b, ()) mb => ∃ sb : FullState,
        FullSparseInv c F0 sb ∧ sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (res_b = 1#64 ∨ res_b = 20#64) ∧ (res_b = 20#64 → F0.Unsat) ∧
        (FullMem c sb ⋆ R) mb)
      (fun rem (budget, bi, ()) mvi => ∃ svi : FullState,
        bi.toNat ≤ bn.toNat ∧ rem = bn.toNat - bi.toNat ∧
        FullSparseInv c F0 svi ∧ svi.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        fullArenaClauseRefs svi = fullArenaClauseRefs s2 ∧
        svi.scratch.red_refs = rr5 ∧ (FullMem c svi ⋆ R) mvi)
      ?_ ?_ ?_
    · rintro _ ⟨_, res_b, bi_b, ⟨⟩⟩ mb ⟨sb, hspb, hflb, hresb, h20b, hmb⟩
      refine wp_join_group (ts := [])
        (fun () m_bt => ∃ sbt : FullState,
          FullSparseInv c F0 sbt ∧ sbt.core.cur_level = 0 ∧
          sbt.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sbt ⋆ R) m_bt) ?_ ?_
      · rintro _ ⟨⟩ m_bt ⟨sbt, hspbt, hclbt, hflbt, hm_bt⟩
        refine wp_join_group (ts := [])
          (fun () m_w => ∃ sw : FullState,
            FullSparseInv c F0 sw ∧ sw.core.cur_level = 0 ∧
            sw.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sw ⋆ R) m_w) ?_ ?_
        · rintro _ ⟨⟩ m_w ⟨sw, hspw, hclw, hflw, hm_w⟩
          fvt_steps
          let sf : FullState := { sw with core := { sw.core with probing := 0#64 } }
          have hspf : FullSparseInv c F0 sf := FullVivTop.FullSparseInv.with_probing hspw 0#64
          exact hQ res_b sf _ hspf (fun _ => hclw) (fun _ => rfl)
            (fun _ => ⟨hclw, rfl⟩) hflw hresb h20b hm
        · intro Jw hJw
          fvt_steps
          · c0_call hClearTier
            refine ⟨c, F0, sbt, R, rfl, hspbt, hclbt, hm_bt,
              fun sw m_w hspw hclw hflw hm_w =>
                hJw () m_w ⟨sw, hspw, hclw, by rw [hflw]; exact hflbt, hm_w⟩⟩
          · exact hJw () m_bt ⟨sbt, hspbt, hclbt, hflbt, hm_bt⟩
          · exact hJw () m_bt ⟨sbt, hspbt, hclbt, hflbt, hm_bt⟩
          · exact hJw () m_bt ⟨sbt, hspbt, hclbt, hflbt, hm_bt⟩
      · intro Jbt hJbt
        obtain ⟨F_curb, hswb⟩ := hspb.exists_witness
        have hclb_lt : sb.core.cur_level < 2 ^ 64 := by
          have := hswb.2.1.cur_level_le; have := hspb.1.lengths.core_ok.trail_end_le
          have := hspb.1.lengths.core_ok.cur_vars_le; omega
        fvt_steps
        · c0_call hBacktrack
          refine ⟨c, sb, R, rfl, hspb.1.lengths, hclb_lt,
            (by have h0n : BitVec.toNat (0 : BitVec 64) = 0 := rfl; rw [h0n]; intro;
                have := hswb.2.1.cur_level_le; have := hspb.1.lengths.core_ok.trail_end_le
                have := hspb.1.lengths.core_ok.cur_vars_le; omega),
            hswb.2.1.trail_lits_lt, hmb,
            fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt
              hlen_bt _ _ hcl_bt hpres_bt _ _ _ hw_bt _ hm_bt => ?_⟩
          have hsp_bt : FullSparseInv c F0 _ :=
            FullVivTop.FullSparseInv.of_backtrack hspb (Nat.zero_le _) hlen_bt hpres_bt
              (by simpa using hw_bt F0)
          exact hJbt () m_bt ⟨_, hsp_bt, by rw [hcl_bt]; simp, hflb, hm_bt⟩
        · have hclb0 : sb.core.cur_level = 0 := by
            have h0 : (BitVec.ofNat 64 sb.core.cur_level).toNat = 0 := by rw [hc]; rfl
            rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hclb_lt] at h0
          exact hJbt () mb ⟨sb, hspb, hclb0, hflb, hmb⟩
    · intro B L rem ⟨budget, bi, ⟨⟩⟩ mvi hB hL
        ⟨svi, hbi_le, hrem, hspv, hflv, hrefsv, hrrv, hmvi⟩
      subst hrem
      fvt_steps
      · have hbi_lt : bi.toNat < bn.toNat := by c0_bound
        have hbi3_nat : (bi * 3).toNat = 3 * bi.toNat := by bv_omega
        have hbi3_lt : (bi * 3).toNat < svi.scratch.red_refs.length := by
          rw [hrrv, hrr5_len]; omega
        let cr := svi.scratch.red_refs[(bi * 3).toNat]'hbi3_lt
        have hcr_ref : cr.toNat ∈ fullArenaClauseRefs svi := by
          rw [hrefsv]
          have h := hok5' bi.toNat hbi_lt
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h
          have heq : cr = rr5[3 * bi.toNat]'(by omega) := Option.some.inj (by
            rw [← List.getElem?_eq_getElem hbi3_lt, hrrv, hbi3_nat,
              List.getElem?_eq_getElem (by omega)])
          rwa [heq]
        obtain ⟨F_curv, hswv⟩ := hspv.exists_witness
        have hbi1 : (bi + 1#64).toNat = bi.toNat + 1 := by bv_omega
        fvt_steps
        c0_call hVivClause
        refine ⟨c, F0, F_curv, svi, R, rfl, hswv, hcr_ref, hmvi,
          fun vc s_vc m_vc hsw_vc hfl_vc _ hrefs_vc hrr_vc hvc h20_vc hm_vc => ?_⟩
        have hrefs_vc2 : fullArenaClauseRefs s_vc = fullArenaClauseRefs s2 :=
          hrefs_vc.trans hrefsv
        have hrr_vc5 : s_vc.scratch.red_refs = rr5 := hrr_vc.trans hrrv
        have hfl_vc' : s_vc.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfl_vc hflv
        fvt_steps
        · exact hB (budget - 1#64, 20#64, bi, ()) m_vc
            ⟨s_vc, hsw_vc.toSparse, hfl_vc', Or.inr rfl, fun _ => h20_vc (by c0_bound), hm_vc⟩
        · exact hB (budget - 1#64, 1#64, bi, ()) m_vc
            ⟨s_vc, hsw_vc.toSparse, hfl_vc', Or.inl rfl, (fun h => by cases h), hm_vc⟩
        · have hcl_vc_lt : s_vc.core.cur_level < 2 ^ 64 := by
            have := hsw_vc.2.1.cur_level_le; have := hsw_vc.1.core_ok.trail_end_le
            have := hsw_vc.1.core_ok.cur_vars_le; omega
          have hcl_vc0 : s_vc.core.cur_level = 0 := by
            have h0 : (BitVec.ofNat 64 s_vc.core.cur_level).toNat = 0 := by
              have hc0 : BitVec.ofNat 64 s_vc.core.cur_level = 0#64 := by c0_bound
              rw [hc0]; rfl
            rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_vc_lt] at h0
          c0_call hProp
          refine ⟨c, F0, F_curv, s_vc, R, rfl, hsw_vc.1, hsw_vc.2.1, hsw_vc.2.2.2.2.2, hm_vc,
            fun pr vals_p flags_p lvl_p rsns_p trl_p tp_p te_p prop_p unass_p unfl_p
              wvec_p arena_p wstk_p wlen_p wu_p fuel_p ctype_p cref_p c0_p c1_p oom_p
              ticks_p wsort_p phases_p m_p hlen_p hw_p _ hperm_p hfl_p _ _ hpr1 _ _
              hm_p => ?_⟩
          let s_p : FullState :=
            { s_vc with
              core := { s_vc.core with
                vals := vals_p, flags := flags_p, lvl := lvl_p, rsns := rsns_p,
                trl := trl_p, trail_pos := tp_p, trail_end := te_p, propagated := prop_p,
                unassigned := unass_p, unflushed := unfl_p, wvec := wvec_p,
                arena := arena_p, wstk := wstk_p, wlen := wlen_p, wusable := wu_p,
                fuel := fuel_p, confl_type := ctype_p, confl_ref := cref_p,
                confl_lit0 := c0_p, confl_lit1 := c1_p, oom := oom_p }
              scratch := { s_vc.scratch with
                search_ticks := ticks_p, wsort := wsort_p, phases := phases_p } }
          have hsw_p : FullSparseInvW c F0 F_curv s_p :=
            m6b_sparseInvW_of_prop_canon hsw_vc hlen_p hw_p hperm_p
          have hrefs_p : fullArenaClauseRefs s_p = fullArenaClauseRefs s_vc := hperm_p.2.1
          have hfl_p' : s_p.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfl_p hfl_vc'
          fvt_steps
          · have hpr_eq1 : pr = 1#64 := by c0_bound
            have hunsat : F0.Unsat :=
              FullVivTopSpecs.level0_unsat_of_conflict_okW hw_p hcl_vc0 (hpr1 hpr_eq1).2.2
            exact hB (budget - 1#64, 20#64, bi, ()) m_p
              ⟨s_p, hsw_p.toSparse, hfl_p', Or.inr rfl, fun _ => hunsat, hm_p⟩
          · exact hL (bn.toNat - (bi + 1#64).toNat) (budget - 1#64, bi + 1#64, ()) m_p
              (by rw [hbi1]; omega)
              ⟨s_p, by rw [hbi1]; omega, rfl, hsw_p.toSparse, hfl_p',
                hrefs_p.trans hrefs_vc2, hrr_vc5, hm_p⟩
        · exact hL (bn.toNat - (bi + 1#64).toNat) (budget - 1#64, bi + 1#64, ()) m_vc
            (by rw [hbi1]; omega)
            ⟨s_vc, by rw [hbi1]; omega, rfl, hsw_vc.toSparse, hfl_vc', hrefs_vc2, hrr_vc5, hm_vc⟩
      · exact hB (budget, 1#64, bi, ()) mvi
          ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
      · exact hB (budget, 1#64, bi, ()) mvi
          ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
      · exact hB (budget, 1#64, bi, ()) mvi
          ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
      · exact hB (budget, 1#64, bi, ()) mvi
          ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
      · exact hB (budget, 1#64, bi, ()) mvi
          ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
    · intro B L _ hL; fvt_steps
      exact hL bn.toNat (budget0, 0#64, ()) m5
        ⟨s5, Nat.zero_le _, by simp, hsp5, hfl5, hrefs5, hrr5, hm5'⟩
  · intro Jc hJc
    obtain ⟨F_cur0, hsw0⟩ := hsp0.exists_witness
    have hcl0_lt : s.core.cur_level < 2 ^ 64 := by
      have := hsw0.2.1.cur_level_le; have := hsp0.1.lengths.core_ok.trail_end_le
      have := hsp0.1.lengths.core_ok.cur_vars_le; omega
    fvt_steps
    · c0_call hBacktrack
      refine ⟨c, s, R, rfl, hsp0.1.lengths, hcl0_lt,
        (by have h0n : BitVec.toNat (0 : BitVec 64) = 0 := rfl; rw [h0n]; intro;
            have := hsw0.2.1.cur_level_le; have := hsp0.1.lengths.core_ok.trail_end_le
            have := hsp0.1.lengths.core_ok.cur_vars_le; omega),
        hsw0.2.1.trail_lits_lt, hm0,
        fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m1
          hlen1 _ _ hcl1 hpres1 _ _ _ hw_bt _ hm1 => ?_⟩
      have hsp1 : FullSparseInv c F0 _ :=
        FullVivTop.FullSparseInv.of_backtrack hsp0 (Nat.zero_le _) hlen1 hpres1
          (by simpa using hw_bt F0)
      exact hJc () m1 ⟨_, hsp1, by rw [hcl1]; simp, Nat.le_refl _, hm1⟩
    · have hcl0 : s.core.cur_level = 0 := by
        have h0 : (BitVec.ofNat 64 s.core.cur_level).toNat = 0 := by rw [hc]; rfl
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl0_lt] at h0
      exact hJc () m0 ⟨s, hsp0, hcl0, Nat.le_refl _, hm0⟩

end VivSchedProofs

end LeanQbe.T.Examples.Kissat.FullM6VivBackbone
