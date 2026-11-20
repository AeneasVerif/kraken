module

public import LeanQbe.T.Examples.Kissat.PlainSpec1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Plain` Auxiliary Preservation, GC/Analysis & Minimization Lemmas (`Stage 3`)

Builds on `PlainSpec1` to provide:
1. `arenaClauseRefs_append`, `addGarbageClause_preserves_core`,
   `plainWstackDefrag_preserves_watchesInv`, and `plainWatchPush_preserves_watchesInv`.
2. `ReasonsMarked` (for `plain_mark_reasons` / `plain_sweep` / `plain_reduce`) and `rsnLits`
   (for `plain_analyze_rsn` / `plain_analyze`).
3. Iterative minimization mark preservation & soundness lemmas (`plainMinMarkInv_init`,
   `plainMinMarkState`, `plainMinMarkInv_set_bit8`, `plainMinMarkInv_clear_bit8`,
   `plainMinMarkInv_poison`, `plainMinMarkInv_mark_keep`, `plainMinMarkInv_mark_rem`,
   `plainMinMarkInv_drop`, `plainMinMark_entails`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Plain

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Garbage-clause append and watch-stack preservation lemmas -/

theorem arenaClauseRefs_append {c : PlainCfg} {F0 : CNF Nat} {s s' : PlainState} {len : Nat}
    (ha : ArenaClausesInv c F0 s) (hge3 : 3 ≤ len)
    (halen : s'.arena_len = s.arena_len + 3 + len)
    (hhold : ∀ k < s.arena_len, s'.arena[k]? = s.arena[k]?)
    (hnoshrk : (s'.arena[s.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hsz : (s'.arena[s.arena_len + 2]?.getD 0#32).toNat = len) :
    arenaClauseRefs s' = arenaClauseRefs s ++ [s.arena_len] := by
  unfold arenaClauseRefs; rw [halen]
  exact arenaScanRefs_eq_of_prefix hge3 hnoshrk hsz
    (fun r hr => (ha.refs_wf r hr).2.2.2.2) ha.chain_end
    (ha.arenaNextOff_extend (by omega) hhold)

/-- Appending a garbage-marked clause (`len ≥ 3`, `PH_GARB` set, `PH_SHRK` clear) preserves
`PlainCoreInv` (used when `plain_watch_push` fails after `plain_alloc_cl`). -/
theorem addGarbageClause_preserves_core {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    {len : Nat} {arena' wvec' wstk' wsort' : List (BitVec 32)}
    {wlen' : Nat} {wusable' : BitVec 64}
    (hinv : PlainCoreInv c F0 s) (hge3 : 3 ≤ len)
    (hhold_arena : ∀ k < s.arena_len, arena'[k]? = s.arena[k]?)
    (hnew_noshrk : (arena'[s.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hnew_garb : (arena'[s.arena_len]?.getD 0#32 &&& 0x00080000#32) ≠ 0#32)
    (hnew_sz : (arena'[s.arena_len + 2]?.getD 0#32).toNat = len) :
    let s' : PlainState :=
      { s with
        arena := arena', arena_len := s.arena_len + 3 + len,
        wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable',
        heur := { s.heur with wsort := wsort' } }
    s'.LengthsOk c → WatchesInv c F0 s' → PlainCoreInv c F0 s' := by
  intro s' hlen' hwat
  have hnxt_hold := hinv.arena.arenaNextOff_extend (alen' := s.arena_len + 3 + len)
    (by omega) hhold_arena
  have hrefs : arenaClauseRefs s' = arenaClauseRefs s ++ [s.arena_len] :=
    arenaClauseRefs_append hinv.arena hge3 rfl hhold_arena hnew_noshrk hnew_sz
  have hold_garb : ∀ r ∈ arenaClauseRefs s, arenaClauseGarb s' r = arenaClauseGarb s r := by
    intro r hr
    have hr3 := (hinv.arena.refs_wf r hr).1
    unfold arenaClauseGarb arenaHdr s'; simp [hhold_arena r (by omega)]
  have hold_sz : ∀ r ∈ arenaClauseRefs s, arenaClauseSize s' r = arenaClauseSize s r := by
    intro r hr
    have hr3 := (hinv.arena.refs_wf r hr).1
    unfold arenaClauseSize s'; simp [hhold_arena (r + 2) (by omega)]
  have hold_lits : ∀ r ∈ arenaClauseRefs s, arenaClauseLits s' r = arenaClauseLits s r := by
    intro r hr
    have hwf := hinv.arena.refs_wf r hr
    have h1l := hinv.lengths.arena_len_arr; have h1e := hinv.lengths.arena_len_le
    have h2l : s'.arena.length = c.arena_cap := hlen'.arena_len_arr
    have h2e : s'.arena_len ≤ c.arena_cap := hlen'.arena_len_le
    have hbd_ar : r + 3 + arenaClauseSize s r ≤ s.arena_len := by omega
    have hbd1 : r + 3 + arenaClauseSize s r ≤ s.arena.length := by omega
    have hbd2 : r + 3 + arenaClauseSize s r ≤ s'.arena.length := by dsimp [s'] at h2l h2e ⊢; omega
    dsimp only [s'] at hbd2
    unfold arenaClauseLits; rw [hold_sz r hr]
    apply List.ext_getElem
    · simp only [List.length_map, List.length_take, List.length_drop]
      rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
    · intro k hk1 _
      simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
      have hks : k < arenaClauseSize s r := by
        simp only [List.length_map, List.length_take, List.length_drop] at hk1; omega
      have heq := hhold_arena (r + 3 + k) (by omega)
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at heq
      exact congrArg BitVec.toNat (Option.some.inj heq)
  have hnew_garb_s' : arenaClauseGarb s' s.arena_len = true := by
    unfold arenaClauseGarb arenaHdr s'; simp [hnew_garb]
  have harena' : ArenaClausesInv c F0 s' := by
    refine ⟨Or.inr (by dsimp [s']; omega), ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · have hwf := hinv.arena.refs_wf r hr
        have hnx : arenaNextOff s'.arena s'.arena_len r = arenaNextOff s.arena s.arena_len r :=
          hnxt_hold r hr
        rw [hnx, hold_sz r hr]
        refine ⟨by dsimp [s']; omega, hwf.2.1, hwf.2.2.1, by dsimp [s']; omega, ?_⟩
        rcases hwf.2.2.2.2 with he | h3 <;> right <;> dsimp [s'] <;> omega
      · have hnxt_new : arenaNextOff s'.arena s'.arena_len s.arena_len = s.arena_len + 3 + len := by
          unfold arenaNextOff s'; simp [hnew_sz, hnew_noshrk]
        rw [hnxt_new, show arenaClauseSize s' s.arena_len = len from hnew_sz]
        refine ⟨by dsimp [s']; omega, hge3, by omega, by dsimp [s']; omega, Or.inl (by dsimp [s'])⟩
    · intro r hr; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · have hr3 := (hinv.arena.refs_wf r hr).1
        unfold arenaHdr s'; rw [hhold_arena r (by omega)]; exact hinv.arena.no_shrk r hr
      · exact hnew_noshrk
    · intro r hr hng; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · rw [hold_garb r hr] at hng; rw [hold_lits r hr]; exact hinv.arena.lits_lt r hr hng
      · rw [hnew_garb_s'] at hng; cases hng
    · intro r hr hng; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · rw [hold_garb r hr] at hng; rw [hold_lits r hr]; exact hinv.arena.entails r hr hng
      · rw [hnew_garb_s'] at hng; cases hng
  refine ⟨hlen', harena', hwat, hinv.cur_level_le, hinv.trail_lits_lt, hinv.trail_vars_nodup,
    hinv.vals_domain, hinv.vals_true_iff, hinv.vals_false_iff, hinv.lvl_le, hinv.trail_mono,
    hinv.levels_inhabited, hinv.level0_sound, hinv.trail_pos_inv, hinv.level0_rsn_none, ?_⟩
  intro idx hidx; dsimp only [s']; intro hne
  have hrs := hinv.reason_inv idx hidx hne
  split at hrs <;> split
  · exact hrs
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · have hrefs' := hrefs; have hgarb' := hold_garb _ hrs.1; have hlits' := hold_lits _ hrs.1
    dsimp only [s'] at hrefs' hgarb' hlits'
    exact ⟨hrefs' ▸ List.mem_append_left _ hrs.1, hgarb'.trans hrs.2.1,
      fun q hq => hrs.2.2 q (hlits' ▸ hq)⟩

theorem WatchSliceOk.relocate {c : PlainCfg} {F0 F1 : CNF Nat} {s s' : PlainState}
    {lit p p' rem : Nat}
    (hF : F1.Entails F0)
    (hsub : ∀ r ∈ arenaClauseRefs s, r ∈ arenaClauseRefs s')
    (hwstk : ∀ k < rem, s'.wstk[p' + k]? = s.wstk[p + k]?)
    (h : WatchSliceOk c F0 s lit p rem) : WatchSliceOk c F1 s' lit p' rem := by
  induction h generalizing p' with
  | empty => exact .empty
  | @bin p rem w0 hp hflag hlt hent hrest ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hflag hlt
      (CNF.entails_clause_trans hF hent)
      (ih (p' := p' + 1) fun k hk => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (k + 1) (by omega))
  | @large p rem w0 cref hp hp1 hflag hlt href hrest ih =>
    refine .large (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1)
      hflag hlt (hsub _ href)
      (ih (p' := p' + 2) fun k hk => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (k + 2) (by omega))

theorem WatchSliceOk.append_bin {c : PlainCfg} {F0 : CNF Nat} {s s' : PlainState}
    {lit p p' rem : Nat} {w0 : BitVec 32}
    (hsub : ∀ r ∈ arenaClauseRefs s, r ∈ arenaClauseRefs s')
    (hwstk : ∀ k < rem, s'.wstk[p' + k]? = s.wstk[p + k]?)
    (h : WatchSliceOk c F0 s lit p rem)
    (hw0 : s'.wstk[p' + rem]? = some w0)
    (hflag : (w0 &&& 0x80000000#32) ≠ 0#32)
    (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * c.mv)
    (hent : F0.EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat])) :
    WatchSliceOk c F0 s' lit p' (rem + 1) := by
  induction h generalizing p' with
  | empty => exact .bin (by simpa using hw0) hflag hlt hent .empty
  | @bin p rem w hp hf hl he _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hl he ?_
    exact ih (p' := p' + 1)
      (fun k hk => by simpa [show p' + 1 + k = p' + (k + 1) by omega,
        show p + 1 + k = p + (k + 1) by omega] using hwstk (k + 1) (by omega))
      (by simpa [show p' + 1 + rem = p' + (rem + 1) by omega] using hw0)
  | @large p rem w cref hp hp1 hf hl href _ ih =>
    refine .large (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hf hl (hsub _ href) ?_
    exact ih (p' := p' + 2)
      (fun k hk => by simpa [show p' + 2 + k = p' + (k + 2) by omega,
        show p + 2 + k = p + (k + 2) by omega] using hwstk (k + 2) (by omega))
      (by simpa [show p' + 2 + rem = p' + (rem + 2) by omega] using hw0)

theorem WatchSliceOk.append_large {c : PlainCfg} {F0 : CNF Nat} {s s' : PlainState}
    {lit p p' rem : Nat} {w0 cref : BitVec 32}
    (hsub : ∀ r ∈ arenaClauseRefs s, r ∈ arenaClauseRefs s')
    (hwstk : ∀ k < rem, s'.wstk[p' + k]? = s.wstk[p + k]?)
    (h : WatchSliceOk c F0 s lit p rem)
    (hw0 : s'.wstk[p' + rem]? = some w0)
    (hw1 : s'.wstk[p' + rem + 1]? = some cref)
    (hflag : (w0 &&& 0x80000000#32) = 0#32)
    (hlt : cref.toNat < 0x80000000)
    (href : cref.toNat ∈ arenaClauseRefs s') :
    WatchSliceOk c F0 s' lit p' (rem + 2) := by
  induction h generalizing p' with
  | empty => exact .large (by simpa using hw0) (by simpa using hw1) hflag hlt href .empty
  | @bin p rem w hp hf hl he _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hl he ?_
    exact ih (p' := p' + 1)
      (fun k hk => by simpa [show p' + 1 + k = p' + (k + 1) by omega,
        show p + 1 + k = p + (k + 1) by omega] using hwstk (k + 1) (by omega))
      (by simpa [show p' + 1 + rem = p' + (rem + 1) by omega] using hw0)
      (by simpa [show p' + 1 + rem + 1 = p' + (rem + 1) + 1 by omega] using hw1)
  | @large p rem w cr hp hp1 hf hl hr _ ih =>
    refine .large (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hf hl (hsub _ hr) ?_
    exact ih (p' := p' + 2)
      (fun k hk => by simpa [show p' + 2 + k = p' + (k + 2) by omega,
        show p + 2 + k = p + (k + 2) by omega] using hwstk (k + 2) (by omega))
      (by simpa [show p' + 2 + rem = p' + (rem + 2) by omega] using hw0)
      (by simpa [show p' + 2 + rem + 1 = p' + (rem + 2) + 1 by omega] using hw1)

/-- Verbatim slice-preserving defragmentation (`plainWstackDefragSpec`) preserves `WatchesInv`. -/
theorem plainWstackDefrag_preserves_watchesInv {c : PlainCfg} {F0 : CNF Nat}
    {s s' : PlainState}
    (hw : WatchesInv c F0 s) (hlay : WatchStackLayout c s')
    (hsub : ∀ r ∈ arenaClauseRefs s, r ∈ arenaClauseRefs s')
    (hpres : ∀ l < 2 * c.mv, watchSize s' l = watchSize s l ∧
      ∀ k < watchSize s l, s'.wstk[watchOff s' l + k]? = s.wstk[watchOff s l + k]?) :
    WatchesInv c F0 s' := by
  refine ⟨hlay, fun l hl => ?_⟩
  obtain ⟨hsz, hslice⟩ := hpres l hl
  rw [hsz]
  exact (hw.slices l hl).relocate (by rw [CNF.entails_def]; exact fun _ h => h) hsub hslice

/-- Exact-append watch push (`plainWatchPushSpec`) preserves `WatchesInv`. -/
theorem plainWatchPush_preserves_watchesInv {c : PlainCfg} {F0 : CNF Nat}
    {s s' : PlainState} {lit w0 w1 cnt : BitVec 32} {ok : Bool}
    (hw : WatchesInv c F0 s) (hlay : WatchStackLayout c s')
    (hsub : ∀ r ∈ arenaClauseRefs s, r ∈ arenaClauseRefs s')
    (hbin : cnt.toNat = 1 →
      (w0 &&& 0x80000000#32) ≠ 0#32 ∧ (w0 &&& 0x7FFFFFFF#32).toNat < 2 * c.mv ∧
      F0.EntailsClause (cnfClause [lit.toNat, (w0 &&& 0x7FFFFFFF#32).toNat]))
    (hlarge : cnt.toNat = 2 →
      (w0 &&& 0x80000000#32) = 0#32 ∧ w1.toNat < 0x80000000 ∧
      w1.toNat ∈ arenaClauseRefs s')
    (hother : ∀ l < 2 * c.mv, l ≠ lit.toNat →
      watchSize s' l = watchSize s l ∧
      ∀ k < watchSize s l, s'.wstk[watchOff s' l + k]? = s.wstk[watchOff s l + k]?)
    (hok_true : ok = true →
      lit.toNat < 2 * c.mv ∧ (cnt.toNat = 1 ∨ cnt.toNat = 2) ∧
      watchSize s' lit.toNat = watchSize s lit.toNat + cnt.toNat ∧
      (∀ k < watchSize s lit.toNat,
        s'.wstk[watchOff s' lit.toNat + k]? = s.wstk[watchOff s lit.toNat + k]?) ∧
      s'.wstk[watchOff s' lit.toNat + watchSize s lit.toNat]? = some w0 ∧
      (cnt.toNat = 2 →
        s'.wstk[watchOff s' lit.toNat + watchSize s lit.toNat + 1]? = some w1))
    (hok_false : ok = false → lit.toNat < 2 * c.mv →
      watchSize s' lit.toNat = watchSize s lit.toNat ∧
      ∀ k < watchSize s lit.toNat,
        s'.wstk[watchOff s' lit.toNat + k]? = s.wstk[watchOff s lit.toNat + k]?) :
    WatchesInv c F0 s' := by
  refine ⟨hlay, fun l hl => ?_⟩
  by_cases hle : l = lit.toNat
  · subst hle
    cases ok with
    | false =>
      obtain ⟨hsz, hslice⟩ := hok_false rfl hl
      rw [hsz]
      exact (hw.slices _ hl).relocate (by rw [CNF.entails_def]; exact fun _ h => h) hsub hslice
    | true =>
      obtain ⟨_, hcnt, hsz, hpre, hw0, hw1⟩ := hok_true rfl
      rw [hsz]
      rcases hcnt with hc1 | hc2
      · rw [hc1]; obtain ⟨hf, hlt, hent⟩ := hbin hc1
        exact (hw.slices _ hl).append_bin hsub hpre hw0 hf hlt hent
      · rw [hc2]; obtain ⟨hf, hlt, href⟩ := hlarge hc2
        exact (hw.slices _ hl).append_large hsub hpre hw0 (hw1 hc2) hf hlt href
  · obtain ⟨hsz, hslice⟩ := hother l hl hle
    rw [hsz]
    exact (hw.slices l hl).relocate (by rw [CNF.entails_def]; exact fun _ h => h) hsub hslice

/-! ## 2. GC reason-marking predicate and conflict-analysis reason literals -/

/-- Every large arena reason referenced by a positive-level trail literal has `PH_RSN`
(`0x00200000#32`) set in its header word. -/
def ReasonsMarked (s : PlainState) : Prop :=
  ∀ idx < s.trail_end,
    let v := (s.trl[idx]?.getD 0#32).toNat / 2
    let rsn := s.rsns[v]?.getD 0xFFFFFFFF#32
    0 < (s.lvl[v]?.getD 0#32).toNat →
    (rsn &&& 0x80000000#32) = 0#32 →
    (arenaHdr s rsn.toNat &&& 0x00200000#32) ≠ 0#32

/-- Literals scanned by `plain_analyze_rsn` for a binary or arena clause reason `rsn`. -/
def rsnLits (s : PlainState) (rsn : BitVec 32) : List Nat :=
  if rsn = 0xFFFFFFFF#32 then []
  else if (rsn &&& 0x80000000#32) ≠ 0#32 then [(rsn &&& 0x7FFFFFFF#32).toNat]
  else arenaClauseLits s rsn.toNat

/-! ## 3. Iterative minimization mark preservation & soundness lemmas -/

private theorem bv8_eq_zero_of_masks :
    ∀ x : BitVec 8, (x &&& 0xF1#8) = 0#8 → (x &&& 8#8) = 0#8 → (x &&& 6#8) = 0#8 → x = 0#8 := by
  decide

private theorem bv8_or_tag_dom :
    ∀ x : BitVec 8, (x &&& 0xF1#8) = 0#8 →
      ((x ||| 2#8) &&& 0xF1#8) = 0#8 ∧ ((x ||| 4#8) &&& 0xF1#8) = 0#8 ∧
      ((x ||| 8#8) &&& 0xF1#8) = 0#8 ∧ ((x &&& 0xF7#8) &&& 0xF1#8) = 0#8 := by
  decide

private theorem bv8_bit_pres :
    ∀ x : BitVec 8,
      ((x ||| 4#8) &&& 2#8) = (x &&& 2#8) ∧
      ((x ||| 2#8) &&& 2#8) = 2#8 ∧
      ((x ||| 8#8) &&& 6#8) = (x &&& 6#8) ∧
      ((x ||| 8#8) &&& 2#8) = (x &&& 2#8) ∧
      ((x &&& 0xF7#8) &&& 6#8) = (x &&& 6#8) ∧
      ((x &&& 0xF7#8) &&& 2#8) = (x &&& 2#8) := by
  decide

theorem plainMinMarkInv_init {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hcore : PlainCoreInv c F0 s) (hmc : MarksClear c s) (keep : List Nat) :
    PlainMinMarkInv c F0 s keep :=
  ⟨fun v hv => by rw [hmc v hv]; decide,
   fun _ v hv hnz => by rw [hmc v hv] at hnz; exact absurd rfl hnz,
   fun idx hi h => by
     have hv : (s.trl[idx]?.getD 0#32).toNat / 2 < c.mv := by
       have := hcore.trail_lits_lt idx hi; omega
     rw [hmc _ hv] at h; exact absurd rfl h⟩

theorem plainMinMarkInv_mrk_ne_zero_iff {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    {keep : List Nat} (hmin : PlainMinMarkInv c F0 s keep)
    (hno8 : ∀ v < c.mv, (s.mrk[v]?.getD 0#8 &&& 8#8) = 0#8) {v : Nat} (hv : v < c.mv) :
    s.mrk[v]?.getD 0#8 ≠ 0#8 ↔ (s.mrk[v]?.getD 0#8 &&& 6#8) ≠ 0#8 := by
  constructor
  · intro hnz h6; exact hnz (bv8_eq_zero_of_masks _ (hmin.mrk_dom v hv) (hno8 v hv) h6)
  · intro h6 hz; rw [hz] at h6; exact absurd rfl h6

private theorem plain_trail_xor_var_lt {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hcore : PlainCoreInv c F0 s) {k q : Nat} (hk : k < s.trail_end)
    (hkeq : (s.trl[k]?.getD 0#32).toNat = q ^^^ 1) : q / 2 < c.mv := by
  have hlt := hcore.trail_lits_lt k hk
  have hql : (q ^^^ 1) / 2 = q / 2 := litVar_litNeg q
  rw [hkeq, ← hql] at *; omega

/-- State update performed by `plain_min_mark(h, v, tag)`: ORs `tag` into `mrk[v]` and pushes `v`
to `min_clr` (or sets `min_clr_full := 1#64`) iff the previous byte `cur` was `0#8`. -/
def plainMinMarkState (c : PlainCfg) (s : PlainState) (v : Nat) (tag : BitVec 8) :
    PlainState :=
  let cur := s.mrk[v]?.getD 0#8
  let mclr' := if cur = 0#8 ∧ s.min_clr_len < c.mv then
                 s.min_clr.set s.min_clr_len (BitVec.ofNat 32 v)
               else s.min_clr
  let mcl' := if cur = 0#8 ∧ s.min_clr_len < c.mv then s.min_clr_len + 1 else s.min_clr_len
  let mcf' := if cur = 0#8 ∧ ¬ s.min_clr_len < c.mv then 1#64 else s.min_clr_full
  { s with mrk := s.mrk.set v (cur ||| tag),
           min_clr := mclr', min_clr_len := mcl', min_clr_full := mcf' }

private theorem plain_clr_cov_mark_step {c : PlainCfg} {s : PlainState}
    (hdom : ∀ w < c.mv, (s.mrk[w]?.getD 0#8 &&& 0xF1#8) = 0#8)
    (hcov : s.min_clr_full = 0#64 → ∀ w < c.mv, (s.mrk[w]?.getD 0#8 &&& 6#8) ≠ 0#8 →
      ∃ k < s.min_clr_len, (s.min_clr[k]?.getD 0#32).toNat = w)
    {v : Nat} (hv : v < c.mv) (hmcll : s.min_clr.length = c.mv)
    (hno8 : (s.mrk[v]?.getD 0#8 &&& 8#8) = 0#8) (tag : BitVec 8) :
    let s' := plainMinMarkState c s v tag
    s'.min_clr_full = 0#64 → ∀ w < c.mv, (s'.mrk[w]?.getD 0#8 &&& 6#8) ≠ 0#8 →
      ∃ k < s'.min_clr_len, (s'.min_clr[k]?.getD 0#32).toNat = w := by
  dsimp only [plainMinMarkState]
  intro hmcf w hw hnz
  by_cases hcur0 : s.mrk[v]?.getD 0#8 = 0#8
  · by_cases hlt : s.min_clr_len < c.mv
    · simp only [hcur0, hlt, and_self, not_true_eq_false, and_false, ↓reduceIte] at hmcf hnz ⊢
      by_cases hweq : w = v
      · subst w
        refine ⟨s.min_clr_len, by omega, ?_⟩
        rw [List.getElem?_set_self (by omega), Option.getD_some,
          bv32_ofNat_toNat (by have := c.hmv; unfold dimacsBound at this; omega)]
      · have hnz' : (s.mrk[w]?.getD 0#8 &&& 6#8) ≠ 0#8 := by
          simpa [List.getElem?_set_ne (Ne.symm hweq)] using hnz
        obtain ⟨k, hk, hkeq⟩ := hcov hmcf w hw hnz'
        exact ⟨k, by omega, by rw [List.getElem?_set_ne (by omega)]; exact hkeq⟩
    · simp only [hcur0, hlt, not_false_eq_true, and_self, ↓reduceIte] at hmcf
      cases hmcf
  · simp only [hcur0, false_and, ↓reduceIte] at hmcf hnz ⊢
    by_cases hweq : w = v
    · subst w
      have h6 : (s.mrk[v]?.getD 0#8 &&& 6#8) ≠ 0#8 := fun h =>
        hcur0 (bv8_eq_zero_of_masks _ (hdom v hv) hno8 h)
      exact hcov hmcf v hv h6
    · have hnz' : (s.mrk[w]?.getD 0#8 &&& 6#8) ≠ 0#8 := by
        simpa [List.getElem?_set_ne (Ne.symm hweq)] using hnz
      exact hcov hmcf w hw hnz'

private theorem plainMinMarkInv_lift_sound {c : PlainCfg} {F0 : CNF Nat}
    {s s' : PlainState} {keep : List Nat} (hcore : PlainCoreInv c F0 s)
    (hs_eq : s'.trail_end = s.trail_end ∧ s'.trl = s.trl ∧ s'.lvl = s.lvl ∧
      s'.rsns = s.rsns ∧ s'.arena = s.arena ∧ s'.arena_len = s.arena_len)
    (hmono : ∀ w < c.mv,
      (s.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (s'.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8)
    (hprev : ∀ idx < s.trail_end,
      let p := (s.trl[idx]?.getD 0#32).toNat
      (s.mrk[p / 2]?.getD 0#8 &&& 2#8) ≠ 0#8 →
      (p ^^^ 1) ∈ keep ∨
        let rsn := s.rsns[p / 2]?.getD 0xFFFFFFFF#32
        rsn ≠ 0xFFFFFFFF#32 ∧
        if (rsn &&& 0x80000000#32) ≠ 0#32 then
          let ot := (rsn &&& 0x7FFFFFFF#32).toNat
          ot < 2 * c.mv ∧ F0.EntailsClause (cnfClause [p, ot]) ∧
          ∃ k < idx, (s.trl[k]?.getD 0#32).toNat = ot ^^^ 1 ∧
            ((s.lvl[ot / 2]?.getD 0#32).toNat = 0 ∨ (s.mrk[ot / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)
        else
          rsn.toNat ∈ arenaClauseRefs s ∧ arenaClauseGarb s rsn.toNat = false ∧
          ∀ q ∈ arenaClauseLits s rsn.toNat,
            q = p ∨ ∃ k < idx, (s.trl[k]?.getD 0#32).toNat = q ^^^ 1 ∧
              ((s.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ (s.mrk[q / 2]?.getD 0#8 &&& 2#8) ≠ 0#8))
    {idx : Nat} (hi : idx < s.trail_end)
    (h2' : (s.mrk[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) :
    let p := (s'.trl[idx]?.getD 0#32).toNat
    (p ^^^ 1) ∈ keep ∨
      let rsn := s'.rsns[p / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 ∧
      if (rsn &&& 0x80000000#32) ≠ 0#32 then
        let ot := (rsn &&& 0x7FFFFFFF#32).toNat
        ot < 2 * c.mv ∧ F0.EntailsClause (cnfClause [p, ot]) ∧
        ∃ k < idx, (s'.trl[k]?.getD 0#32).toNat = ot ^^^ 1 ∧
          ((s'.lvl[ot / 2]?.getD 0#32).toNat = 0 ∨ (s'.mrk[ot / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)
      else
        rsn.toNat ∈ arenaClauseRefs s' ∧ arenaClauseGarb s' rsn.toNat = false ∧
        ∀ q ∈ arenaClauseLits s' rsn.toNat,
          q = p ∨ ∃ k < idx, (s'.trl[k]?.getD 0#32).toNat = q ^^^ 1 ∧
            ((s'.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ (s'.mrk[q / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) := by
  rcases hs_eq with ⟨_, htrl, hlvl, hrsn, har, hal⟩
  rw [htrl, hrsn, hlvl]
  have hr : arenaClauseRefs s' = arenaClauseRefs s := by simp [arenaClauseRefs, har, hal]
  have hcl : ∀ r, arenaClauseGarb s' r = arenaClauseGarb s r ∧
      arenaClauseLits s' r = arenaClauseLits s r := fun r => by
    simp [arenaClauseGarb, arenaHdr, arenaClauseLits, arenaClauseSize, har]
  rcases hprev idx hi h2' with hin | ⟨hne, hif⟩
  · exact Or.inl hin
  · refine Or.inr ⟨hne, ?_⟩
    split at hif <;> split
    · obtain ⟨hot, hent, k, hk, hkeq, hdep⟩ := hif
      exact ⟨hot, hent, k, hk, hkeq, hdep.elim Or.inl fun hk2 => Or.inr (hmono _ (by omega) hk2)⟩
    · rename_i h1 h2; exact absurd h1 h2
    · rename_i h1 h2; exact absurd h2 h1
    · obtain ⟨href, hng, hall⟩ := hif
      refine ⟨by rw [hr]; exact href, by rw [(hcl _).1]; exact hng, fun q hq => ?_⟩
      rw [(hcl _).2] at hq
      rcases hall q hq with rfl | ⟨k, hk, hkeq, hdep⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨k, hk, hkeq, hdep.elim Or.inl fun hk2 =>
          Or.inr (hmono _ (plain_trail_xor_var_lt hcore (Nat.lt_trans hk hi) hkeq) hk2)⟩

/-- Setting temporary block-shrink bit `8#8` on `v` preserves `PlainMinMarkInv`. -/
theorem plainMinMarkInv_set_bit8 {c : PlainCfg} {F0 : CNF Nat} {s : PlainState} {keep : List Nat}
    (hcore : PlainCoreInv c F0 s) (hmin : PlainMinMarkInv c F0 s keep)
    {v : Nat} (hv : v < c.mv) :
    PlainMinMarkInv c F0 { s with mrk := s.mrk.set v (s.mrk[v]?.getD 0#8 ||| 8#8) } keep := by
  let s' : PlainState := { s with mrk := s.mrk.set v (s.mrk[v]?.getD 0#8 ||| 8#8) }
  change PlainMinMarkInv c F0 s' keep
  have hlen := hcore.lengths
  have hbit2 : ∀ w < c.mv,
      (s'.mrk[w]?.getD 0#8 &&& 2#8) = (s.mrk[w]?.getD 0#8 &&& 2#8) := fun w _ => by
    by_cases hweq : w = v
    · subst w
      simp [s', List.getElem?_set_self (by rw [hlen.mrk_len]; omega), (bv8_bit_pres _).2.2.2.1]
    · simp [s', List.getElem?_set_ne (Ne.symm hweq)]
  refine ⟨fun w hw => ?_, fun hmcf w hw hnz => ?_, fun idx hi h2 => ?_⟩
  · by_cases hweq : w = v
    · subst w
      simp [s', List.getElem?_set_self (by rw [hlen.mrk_len]; omega),
        (bv8_or_tag_dom _ (hmin.mrk_dom v hv)).2.2.1]
    · simp [s', List.getElem?_set_ne (Ne.symm hweq), hmin.mrk_dom w hw]
  · refine hmin.clr_cov hmcf w hw ?_
    by_cases hweq : w = v
    · subst w
      simpa [s', List.getElem?_set_self (by rw [hlen.mrk_len]; omega),
        (bv8_bit_pres _).2.2.1] using hnz
    · simpa [s', List.getElem?_set_ne (Ne.symm hweq)] using hnz
  · have hvw : (s.trl[idx]?.getD 0#32).toNat / 2 < c.mv := by
      have := hcore.trail_lits_lt idx hi; omega
    exact plainMinMarkInv_lift_sound (s' := s') hcore ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      (fun w hw h => by rwa [hbit2 w hw]) hmin.rem_sound hi (by rwa [← hbit2 _ hvw])

/-- Clearing temporary block-shrink bit `8#8` (`&&& 0xF7#8`) on `v` preserves `PlainMinMarkInv`. -/
theorem plainMinMarkInv_clear_bit8 {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    {keep : List Nat} (hcore : PlainCoreInv c F0 s) (hmin : PlainMinMarkInv c F0 s keep)
    {v : Nat} (hv : v < c.mv) :
    PlainMinMarkInv c F0 { s with mrk := s.mrk.set v (s.mrk[v]?.getD 0#8 &&& 0xF7#8) } keep := by
  let s' : PlainState := { s with mrk := s.mrk.set v (s.mrk[v]?.getD 0#8 &&& 0xF7#8) }
  change PlainMinMarkInv c F0 s' keep
  have hlen := hcore.lengths
  have hbit2 : ∀ w < c.mv,
      (s'.mrk[w]?.getD 0#8 &&& 2#8) = (s.mrk[w]?.getD 0#8 &&& 2#8) := fun w _ => by
    by_cases hweq : w = v
    · subst w
      simp [s', List.getElem?_set_self (by rw [hlen.mrk_len]; omega), (bv8_bit_pres _).2.2.2.2.2]
    · simp [s', List.getElem?_set_ne (Ne.symm hweq)]
  refine ⟨fun w hw => ?_, fun hmcf w hw hnz => ?_, fun idx hi h2 => ?_⟩
  · by_cases hweq : w = v
    · subst w
      simp [s', List.getElem?_set_self (by rw [hlen.mrk_len]; omega),
        (bv8_or_tag_dom _ (hmin.mrk_dom v hv)).2.2.2]
    · simp [s', List.getElem?_set_ne (Ne.symm hweq), hmin.mrk_dom w hw]
  · refine hmin.clr_cov hmcf w hw ?_
    by_cases hweq : w = v
    · subst w
      simpa [s', List.getElem?_set_self (by rw [hlen.mrk_len]; omega),
        (bv8_bit_pres _).2.2.2.2.1] using hnz
    · simpa [s', List.getElem?_set_ne (Ne.symm hweq)] using hnz
  · have hvw : (s.trl[idx]?.getD 0#32).toNat / 2 < c.mv := by
      have := hcore.trail_lits_lt idx hi; omega
    exact plainMinMarkInv_lift_sound (s' := s') hcore ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      (fun w hw h => by rwa [hbit2 w hw]) hmin.rem_sound hi (by rwa [← hbit2 _ hvw])

theorem plainMinMarkInv_poison {c : PlainCfg} {F0 : CNF Nat} {s : PlainState} {keep : List Nat}
    (hcore : PlainCoreInv c F0 s) (hmin : PlainMinMarkInv c F0 s keep)
    {v : Nat} (hv : v < c.mv) (hno8 : (s.mrk[v]?.getD 0#8 &&& 8#8) = 0#8) :
    PlainMinMarkInv c F0 (plainMinMarkState c s v 4#8) keep := by
  let s' := plainMinMarkState c s v 4#8; change PlainMinMarkInv c F0 s' keep
  have hlen := hcore.lengths
  have hbit2 : ∀ w < c.mv,
      (s'.mrk[w]?.getD 0#8 &&& 2#8) = (s.mrk[w]?.getD 0#8 &&& 2#8) := fun w _ => by
    by_cases hweq : w = v
    · subst w
      simp [s', plainMinMarkState, List.getElem?_set_self (by rw [hlen.mrk_len]; omega),
        (bv8_bit_pres _).1]
    · simp [s', plainMinMarkState, List.getElem?_set_ne (Ne.symm hweq)]
  refine ⟨fun w hw => ?_,
    plain_clr_cov_mark_step hmin.mrk_dom hmin.clr_cov hv hlen.min_clr_len_arr hno8 4#8,
    fun idx hi h2 => ?_⟩
  · by_cases hweq : w = v
    · subst w
      simp [s', plainMinMarkState, List.getElem?_set_self (by rw [hlen.mrk_len]; omega),
        (bv8_or_tag_dom _ (hmin.mrk_dom v hv)).2.1]
    · simp [s', plainMinMarkState, List.getElem?_set_ne (Ne.symm hweq), hmin.mrk_dom w hw]
  · have hvw : (s.trl[idx]?.getD 0#32).toNat / 2 < c.mv := by
      have := hcore.trail_lits_lt idx hi; omega
    exact plainMinMarkInv_lift_sound (s' := s') hcore ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      (fun w hw h => by rwa [hbit2 w hw]) hmin.rem_sound hi (by rwa [← hbit2 _ hvw])

theorem plainMinMarkInv_mark_keep {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    {keep : List Nat} (hcore : PlainCoreInv c F0 s) (hmin : PlainMinMarkInv c F0 s keep)
    {l : Nat} (hl : l < 2 * c.mv) (hkeep : l ∈ keep) (hfals : s.vals[l]?.getD 0#8 = 0xFF#8)
    (hno8 : (s.mrk[l / 2]?.getD 0#8 &&& 8#8) = 0#8) :
    PlainMinMarkInv c F0 (plainMinMarkState c s (l / 2) 2#8) keep := by
  let v := l / 2; let s' := plainMinMarkState c s v 2#8; change PlainMinMarkInv c F0 s' keep
  have hlen := hcore.lengths; have hv : v < c.mv := by omega
  have hmono : ∀ w < c.mv,
      (s.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (s'.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 := by
    intro w _ hw2
    by_cases hweq : w = v
    · subst w
      simp [s', plainMinMarkState, List.getElem?_set_self (by rw [hlen.mrk_len]; omega),
        (bv8_bit_pres _).2.1]
    · simpa [s', plainMinMarkState, List.getElem?_set_ne (Ne.symm hweq)] using hw2
  refine ⟨fun w hw => ?_,
    plain_clr_cov_mark_step hmin.mrk_dom hmin.clr_cov hv hlen.min_clr_len_arr hno8 2#8,
    fun idx hi h2 => ?_⟩
  · by_cases hweq : w = v
    · subst w
      simp [s', plainMinMarkState, List.getElem?_set_self (by rw [hlen.mrk_len]; omega),
        (bv8_or_tag_dom _ (hmin.mrk_dom v hv)).1]
    · simp [s', plainMinMarkState, List.getElem?_set_ne (Ne.symm hweq), hmin.mrk_dom w hw]
  · have hi' : idx < s.trail_end := hi
    by_cases hveq : (s.trl[idx]?.getD 0#32).toNat / 2 = v
    · obtain ⟨k, hk, hkeq⟩ := (hcore.vals_false_iff l hl).mp hfals
      have hk_idx : k = idx := hcore.trail_vars_nodup k idx hk hi' (by
        rw [hkeq, show (l ^^^ 1) / 2 = v from litVar_litNeg l, hveq])
      subst hk_idx
      have hp : (l ^^^ 1) ^^^ 1 = l := litNeg_litNeg l
      exact Or.inl (by dsimp only [s', plainMinMarkState]; rwa [hkeq, hp])
    · have h2' : (s.mrk[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 2#8) ≠ 0#8 := by
        simpa [s', plainMinMarkState, List.getElem?_set_ne (Ne.symm hveq)] using h2
      exact plainMinMarkInv_lift_sound (s' := s') hcore ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
        hmono hmin.rem_sound hi' h2'

theorem plainMinMarkInv_mark_rem {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    {keep : List Nat} (hcore : PlainCoreInv c F0 s) (hmin : PlainMinMarkInv c F0 s keep)
    {idx0 : Nat} (hi0 : idx0 < s.trail_end)
    (hno8 : (s.mrk[(s.trl[idx0]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 8#8) = 0#8)
    (hrsn : let p0 := (s.trl[idx0]?.getD 0#32).toNat
      let rsn := s.rsns[p0 / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 ∧
      if (rsn &&& 0x80000000#32) ≠ 0#32 then
        let ot := (rsn &&& 0x7FFFFFFF#32).toNat
        ot < 2 * c.mv ∧ F0.EntailsClause (cnfClause [p0, ot]) ∧
        ∃ k < idx0, (s.trl[k]?.getD 0#32).toNat = ot ^^^ 1 ∧
          ((s.lvl[ot / 2]?.getD 0#32).toNat = 0 ∨ (s.mrk[ot / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)
      else
        rsn.toNat ∈ arenaClauseRefs s ∧ arenaClauseGarb s rsn.toNat = false ∧
        ∀ q ∈ arenaClauseLits s rsn.toNat,
          q = p0 ∨ ∃ k < idx0, (s.trl[k]?.getD 0#32).toNat = q ^^^ 1 ∧
            ((s.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ (s.mrk[q / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)) :
    PlainMinMarkInv c F0
      (plainMinMarkState c s ((s.trl[idx0]?.getD 0#32).toNat / 2) 2#8) keep := by
  let v := (s.trl[idx0]?.getD 0#32).toNat / 2
  let s' := plainMinMarkState c s v 2#8; change PlainMinMarkInv c F0 s' keep
  have hlen := hcore.lengths
  have hv : v < c.mv := by have := hcore.trail_lits_lt idx0 hi0; omega
  have hmono : ∀ w < c.mv,
      (s.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 → (s'.mrk[w]?.getD 0#8 &&& 2#8) ≠ 0#8 := by
    intro w _ hw2
    by_cases hweq : w = v
    · subst w
      simp [s', plainMinMarkState, List.getElem?_set_self (by rw [hlen.mrk_len]; omega),
        (bv8_bit_pres _).2.1]
    · simpa [s', plainMinMarkState, List.getElem?_set_ne (Ne.symm hweq)] using hw2
  refine ⟨fun w hw => ?_,
    plain_clr_cov_mark_step hmin.mrk_dom hmin.clr_cov hv hlen.min_clr_len_arr hno8 2#8,
    fun idx hi h2 => ?_⟩
  · by_cases hweq : w = v
    · subst w
      simp [s', plainMinMarkState, List.getElem?_set_self (by rw [hlen.mrk_len]; omega),
        (bv8_or_tag_dom _ (hmin.mrk_dom v hv)).1]
    · simp [s', plainMinMarkState, List.getElem?_set_ne (Ne.symm hweq), hmin.mrk_dom w hw]
  · have hi' : idx < s.trail_end := hi
    by_cases hveq : (s.trl[idx]?.getD 0#32).toNat / 2 = v
    · have hidx : idx = idx0 := hcore.trail_vars_nodup idx idx0 hi' hi0 hveq; subst hidx
      obtain ⟨hne, hif⟩ := hrsn; refine Or.inr ⟨hne, ?_⟩
      split at hif <;> split
      · obtain ⟨hot, hent, k, hk, hkeq, hdep⟩ := hif
        have hot_v : (s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
            0x7FFFFFFF#32).toNat / 2 < c.mv := by omega
        exact ⟨hot, hent, k, hk, hkeq, hdep.elim Or.inl fun hk2 => Or.inr (hmono _ hot_v hk2)⟩
      · rename_i h1 h2; exact absurd h1 h2
      · rename_i h1 h2; exact absurd h2 h1
      · obtain ⟨href, hng, hall⟩ := hif; refine ⟨href, hng, fun q hq => ?_⟩
        rcases hall q hq with rfl | ⟨k, hk, hkeq, hdep⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨k, hk, hkeq, hdep.elim Or.inl fun hk2 =>
            Or.inr (hmono _ (plain_trail_xor_var_lt hcore (Nat.lt_trans hk hi0) hkeq) hk2)⟩
    · have h2' : (s.mrk[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#8 &&& 2#8) ≠ 0#8 := by
        simpa [s', plainMinMarkState, List.getElem?_set_ne (Ne.symm hveq)] using h2
      exact plainMinMarkInv_lift_sound (s' := s') hcore ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
        hmono hmin.rem_sound hi' h2'

theorem plainMinMarkInv_drop {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    {keep keep' : List Nat} (hcore : PlainCoreInv c F0 s) (hmin : PlainMinMarkInv c F0 s keep)
    {root_lit : Nat} (hsub : ∀ l ∈ keep, l = root_lit ∨ l ∈ keep')
    {idx0 : Nat} (hi0 : idx0 < s.trail_end)
    (hroot : (s.trl[idx0]?.getD 0#32).toNat = root_lit ^^^ 1)
    (hrsn : let p0 := root_lit ^^^ 1
      let rsn := s.rsns[p0 / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 ∧
      if (rsn &&& 0x80000000#32) ≠ 0#32 then
        let ot := (rsn &&& 0x7FFFFFFF#32).toNat
        ot < 2 * c.mv ∧ F0.EntailsClause (cnfClause [p0, ot]) ∧
        ∃ k < idx0, (s.trl[k]?.getD 0#32).toNat = ot ^^^ 1 ∧
          ((s.lvl[ot / 2]?.getD 0#32).toNat = 0 ∨ (s.mrk[ot / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)
      else
        rsn.toNat ∈ arenaClauseRefs s ∧ arenaClauseGarb s rsn.toNat = false ∧
        ∀ q ∈ arenaClauseLits s rsn.toNat,
          q = p0 ∨ ∃ k < idx0, (s.trl[k]?.getD 0#32).toNat = q ^^^ 1 ∧
            ((s.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ (s.mrk[q / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)) :
    PlainMinMarkInv c F0 s keep' := by
  refine ⟨hmin.mrk_dom, hmin.clr_cov, fun idx hi h2 => ?_⟩
  rcases hmin.rem_sound idx hi h2 with hin | hok
  · rcases hsub _ hin with heq | hin'
    · have hv_eq : (s.trl[idx]?.getD 0#32).toNat / 2 = (s.trl[idx0]?.getD 0#32).toNat / 2 := by
        rw [hroot]
        have h1 : ((s.trl[idx]?.getD 0#32).toNat ^^^ 1) / 2 =
            (s.trl[idx]?.getD 0#32).toNat / 2 := litVar_litNeg _
        have h2' : (root_lit ^^^ 1) / 2 = root_lit / 2 := litVar_litNeg root_lit
        rw [← h1, heq, h2']
      have hidx : idx = idx0 := hcore.trail_vars_nodup idx idx0 hi hi0 hv_eq
      subst hidx; rw [hroot]; exact Or.inr hrsn
    · exact Or.inl hin'
  · exact Or.inr hok

private theorem plain_trail_lit_false_strong {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    {keep : List Nat} (hcore : PlainCoreInv c F0 s) (hmin : PlainMinMarkInv c F0 s keep)
    (α : Nat → Bool) (hα : F0.Sat α)
    (hkeep_false : ∀ l ∈ keep, α (litVar l) ≠ !(litSign l)) :
    ∀ i < s.trail_end, let p := (s.trl[i]?.getD 0#32).toNat
      (s.lvl[p / 2]?.getD 0#32).toNat = 0 ∨ (s.mrk[p / 2]?.getD 0#8 &&& 2#8) ≠ 0#8 →
      α (litVar p) = !(litSign p) := by
  intro i hi p hcond
  rcases hcond with hl0 | hrem
  · exact (sat_cnfClause_singleton α p).mp
      (CNF.entails_clause_def.mp (hcore.level0_sound i hi hl0) α hα)
  · rcases hmin.rem_sound i hi hrem with hin | ⟨_, hif⟩
    · have hf := hkeep_false _ hin
      have hv : litVar (p ^^^ 1) = litVar p := litVar_litNeg p
      have hs : litSign (p ^^^ 1) = !(litSign p) := litSign_litNeg p
      rw [hv, hs] at hf; cases h1 : α (litVar p) <;> cases h2 : litSign p <;> simp_all
    · have hcontra : ∀ (q k : Nat), k < i → (s.trl[k]?.getD 0#32).toNat = q ^^^ 1 →
          ((s.lvl[q / 2]?.getD 0#32).toNat = 0 ∨ (s.mrk[q / 2]?.getD 0#8 &&& 2#8) ≠ 0#8) →
          α (litVar q) = !(litSign q) → False := fun q k hk hkeq hkcond hqsat => by
        have hkq : (s.trl[k]?.getD 0#32).toNat / 2 = q / 2 := by rw [hkeq]; exact litVar_litNeg q
        have hkf := plain_trail_lit_false_strong hcore hmin α hα hkeep_false k
          (Nat.lt_trans hk hi) (by rw [hkq]; exact hkcond)
        have hv : litVar (q ^^^ 1) = litVar q := litVar_litNeg q
        have hs : litSign (q ^^^ 1) = !(litSign q) := litSign_litNeg q
        rw [hkeq, hv, hs] at hkf; cases h1 : α (litVar q) <;> cases h2 : litSign q <;> simp_all
      split at hif
      · obtain ⟨_, hent, k, hk, hkeq, hkcond⟩ := hif
        obtain ⟨q, hq, hqsat⟩ := (clause_sat_cnfClause_iff α _).mp
          (CNF.entails_clause_def.mp hent α hα)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | hq
        · exact hqsat
        · exact False.elim (hcontra _ k hk hkeq hkcond (hq ▸ hqsat))
      · obtain ⟨href, hng, hall⟩ := hif
        obtain ⟨q, hq, hqsat⟩ := (clause_sat_cnfClause_iff α _).mp
          (CNF.entails_clause_def.mp (hcore.arena.entails _ href hng) α hα)
        rcases hall q hq with rfl | ⟨k, hk, hkeq, hkcond⟩
        · exact hqsat
        · exact False.elim (hcontra q k hk hkeq hkcond hqsat)
termination_by i => i

/-- Soundness of clause minimization via `PlainMinMarkInv`: if every literal of `orig` is
falsified and either kept in `keep` or has `REMOVABLE` bit `2#8` set, then `F0` entails `keep`. -/
theorem plainMinMark_entails {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    {orig keep : List Nat} (hcore : PlainCoreInv c F0 s) (hmin : PlainMinMarkInv c F0 s keep)
    (horig : F0.EntailsClause (cnfClause orig))
    (hspec : ∀ l ∈ orig, l < 2 * c.mv ∧ s.vals[l]?.getD 0#8 = 0xFF#8 ∧
      (l ∈ keep ∨ (s.mrk[l / 2]?.getD 0#8 &&& 2#8) ≠ 0#8)) :
    F0.EntailsClause (cnfClause keep) := by
  rw [CNF.entails_clause_def] at horig ⊢; intro α hα
  by_cases hsat : (keep.any fun l => α (litVar l) == !(litSign l)) = true
  · obtain ⟨l, hl, hlt⟩ := List.any_eq_true.mp hsat
    exact (clause_sat_cnfClause_iff α keep).mpr ⟨l, hl, beq_iff_eq.mp hlt⟩
  · exfalso
    have hkf : ∀ l ∈ keep, α (litVar l) ≠ !(litSign l) := fun l hl heq =>
      hsat (List.any_eq_true.mpr ⟨l, hl, beq_iff_eq.mpr heq⟩)
    obtain ⟨l, hl, hlsat⟩ := (clause_sat_cnfClause_iff α orig).mp (horig α hα)
    obtain ⟨hlt, hfals, hkm⟩ := hspec l hl
    rcases hkm with hin | hmrk
    · exact hkf l hin hlsat
    · obtain ⟨i, hi, hieq⟩ := (hcore.vals_false_iff l hlt).mp hfals
      have hvar : (s.trl[i]?.getD 0#32).toNat / 2 = l / 2 := by rw [hieq]; exact litVar_litNeg l
      have htf := plain_trail_lit_false_strong hcore hmin α hα hkf i hi
        (Or.inr (by rw [hvar]; exact hmrk))
      have hv : litVar (l ^^^ 1) = litVar l := litVar_litNeg l
      have hs : litSign (l ^^^ 1) = !(litSign l) := litSign_litNeg l
      rw [hieq, hv, hs, hlsat] at htf; cases hls : litSign l <;> simp_all

end LeanQbe.T.Examples.Kissat.Plain
