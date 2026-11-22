module

public import LeanQbe.T.Examples.Kissat.PlainReduceLemmas2

/-!
# Kissat `D-Plain` Compaction GC Helpers (`PlainReduceLemmas3`) (`Wave 2b`)

Provides shared Phase 1/2/3 invariants, `BitVec` arithmetic lemmas, and pure state-transition
helpers used by `plain_sweep_wp` in `PlainReduceLemmas4`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Plain

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.C0Step
open Kraken.Bedrock2.Test

section
open scoped PlainReduceTactics

namespace PlainReduceHelpers

@[expose] def SwFiltInv (c : PlainCfg) (F0 : CNF Nat) (s0 s_2 : PlainState)
    (src dst old_sz new_sz i : Nat) (ar : List (BitVec 32)) : Prop :=
  new_sz ≤ i ∧ i ≤ old_sz ∧ ar.length = c.arena_cap ∧
  (∀ k < dst, ar[k]? = s_2.arena[k]?) ∧
  (∀ k, src + 3 + i ≤ k → k < s0.arena_len → ar[k]? = s_2.arena[k]?) ∧
  (∀ k < new_sz, (ar[dst + 3 + k]?.getD 0#32).toNat < 2 * c.mv) ∧
  F0.EntailsClause (cnfClause ((((ar.drop (dst + 3)).take new_sz).map BitVec.toNat) ++
    (((s0.arena.drop (src + 3 + i)).take (old_sz - i)).map BitVec.toNat)))

@[expose] def SwEmitOk (c : PlainCfg) (F0 : CNF Nat) (s0 s_2 : PlainState)
    (src dst new_sz : Nat) (ar : List (BitVec 32)) : Prop :=
  3 ≤ new_sz ∧ new_sz ≤ arenaClauseSize s0 src ∧ ar.length = c.arena_cap ∧
  (∀ k < dst, ar[k]? = s_2.arena[k]?) ∧
  (∀ k, src + 3 + arenaClauseSize s0 src ≤ k → k < s0.arena_len → ar[k]? = s_2.arena[k]?) ∧
  (∀ k < new_sz, (ar[dst + 3 + k]?.getD 0#32).toNat < 2 * c.mv) ∧
  F0.EntailsClause (cnfClause (((ar.drop (dst + 3)).take new_sz).map BitVec.toNat)) ∧
  (0 < s0.cur_level → ((ar.drop (dst + 3)).take new_sz).map BitVec.toNat = arenaClauseLits s0 src)

@[expose] def SwP3Inv (c : PlainCfg) (F0 : CNF Nat) (s0 : PlainState) (dst : Nat)
    (new_unit : Bool) (s : PlainState) : Prop :=
  PlainCoreInv c F0 s ∧ SameSwPre s0 s ∧ s.arena_garbage = 0#64 ∧
  s.heur.rel_trigger = s0.heur.rel_trigger ∧ s.arena_len = dst ∧ s.oom = 0#64 ∧
  (new_unit = true → s0.cur_level = 0 ∧ s0.trail_end < s.trail_end) ∧
  (0 < s0.cur_level → s.vals = s0.vals ∧ s.lvl = s0.lvl ∧ s.trl = s0.trl ∧
    s.trail_pos = s0.trail_pos ∧ s.trail_end = s0.trail_end) ∧
  (∀ r ∈ arenaClauseRefs s, arenaClauseGarb s r = false)

theorem bv64_add_toNat {x : BitVec 64} {k : Nat} (h : x.toNat + k < 2 ^ 64)
    (hk : k < 2 ^ 64 := by decide) : (x + BitVec.ofNat 64 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt h]

theorem bv32_add_toNat {x : BitVec 32} {k : Nat} (h : x.toNat + k < 2 ^ 32)
    (hk : k < 2 ^ 32 := by decide) : (x + BitVec.ofNat 32 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt h]

theorem bv64_truncate32 {x : BitVec 64} (h : x.toNat < 2 ^ 32) :
    x.truncate 32 = BitVec.ofNat 32 x.toNat := by
  apply BitVec.eq_of_toNat_eq; change (x.setWidth 32).toNat = _
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem sw_filt_cons {ar : List (BitVec 32)} {src old_sz i : Nat}
    (hi : i < old_sz) (hbd : src + 3 + old_sz ≤ ar.length) :
    ((ar.drop (src + 3 + i)).take (old_sz - i)).map BitVec.toNat =
      (ar[src + 3 + i]'(by omega)).toNat ::
        (((ar.drop (src + 3 + (i + 1))).take (old_sz - (i + 1))).map BitVec.toNat) := by
  rw [drop_head_eq (by omega), show old_sz - i = (old_sz - (i + 1)) + 1 by omega,
    List.take_succ_cons, List.map_cons]
  simp only [Nat.add_assoc]

theorem sw_copy_lits {s0 : PlainState} {ar : List (BitVec 32)} {src dst old_sz : Nat}
    (hsz : arenaClauseSize s0 src = old_sz) (h1 : dst + 3 + old_sz ≤ ar.length)
    (h2 : src + 3 + old_sz ≤ s0.arena.length)
    (heq : ∀ k < old_sz, ar[dst + 3 + k]? = s0.arena[src + 3 + k]?) :
    ((ar.drop (dst + 3)).take old_sz).map BitVec.toNat = arenaClauseLits s0 src := by
  unfold arenaClauseLits; rw [hsz]; apply congrArg (List.map BitVec.toNat)
  apply List.ext_getElem
  · simp [Nat.min_eq_left (show old_sz ≤ ar.length - (dst + 3) by omega),
      Nat.min_eq_left (show old_sz ≤ s0.arena.length - (src + 3) by omega)]
  · intro k hk1 _
    simp only [List.length_take, List.length_drop, Nat.lt_min] at hk1
    simp only [List.getElem_take, List.getElem_drop]
    have hke := heq k hk1.1
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hke
    exact Option.some.inj hke

theorem trailValsInv_rsn_set {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (htv : TrailValsInv c F0 s) {v : Nat} {val : BitVec 32} (_hv_lt : v < s.rsns.length)
    (hpos : 0 < (s.lvl[v]?.getD 0#32).toNat) :
    TrailValsInv c F0 { s with rsns := s.rsns.set v val } :=
  ⟨htv.cur_level_le, htv.trail_lits_lt, htv.trail_vars_nodup, htv.vals_domain, htv.vals_true_iff,
    htv.vals_false_iff, htv.lvl_le, htv.trail_mono, htv.levels_inhabited, htv.level0_sound,
    htv.trail_pos_inv, fun idx hidx hl0 => by
      dsimp only at hl0 ⊢
      have hne : (s.trl[idx]?.getD 0#32).toNat / 2 ≠ v := fun h => by rw [h] at hl0; omega
      rw [List.getElem?_set_ne (Ne.symm hne)]
      exact htv.level0_rsn_none idx hidx hl0⟩

theorem lengthsOk_with_arena {c : PlainCfg} {s : PlainState} {ar : List (BitVec 32)}
    (hlen : s.LengthsOk c) (har : ar.length = c.arena_cap) :
    ({ s with arena := ar } : PlainState).LengthsOk c :=
  { hlen with arena_len_arr := har }

theorem trailValsInv_congr {c : PlainCfg} {F0 : CNF Nat} {s s' : PlainState}
    (h : TrailValsInv c F0 s) (hcl : s'.cur_level = s.cur_level) (hv : s'.vals = s.vals)
    (hl : s'.lvl = s.lvl) (hr : s'.rsns = s.rsns) (ht : s'.trl = s.trl)
    (htp : s'.trail_pos = s.trail_pos) (hte : s'.trail_end = s.trail_end) :
    TrailValsInv c F0 s' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simpa only [hcl, hv, hl, hr, ht, htp, hte] using
      (by first
        | exact h.cur_level_le | exact h.trail_lits_lt | exact h.trail_vars_nodup
        | exact h.vals_domain | exact h.vals_true_iff | exact h.vals_false_iff
        | exact h.lvl_le | exact h.trail_mono | exact h.levels_inhabited
        | exact h.level0_sound | exact h.trail_pos_inv | exact h.level0_rsn_none)

theorem rsnReloc_init_congr {s0 s' : PlainState} (hr : s'.rsns = s0.rsns) :
    RsnRelocInv s0 s' 0 0 :=
  ⟨congrArg List.length hr, fun _ _ => Or.inr (by rw [hr]), fun _ _ _ _ _ => by simp [hr]⟩

theorem sw_store_wvec {c : PlainCfg} {s : PlainState} {R : Mem 64 → Prop} {m : Mem 64}
    {i : BitVec 64} (v : BitVec 32) (hm : (PlainMem c s ⋆ R) m) (hi : i.toNat < s.wvec.length) :
    storeOk m i32 (c.pWvec + i * 4) ∧
      (PlainMem c { s with wvec := s.wvec.set i.toNat v } ⋆ R)
        (storeMem m i32 (c.pWvec + i * 4) v) :=
  c0_store_arena_wvec v hi hm

theorem vals_eq_one_of_sext_pos {v : BitVec 8}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (hs : (0#32 : BitVec 32).slt (v.signExtend 32) = true) : v = 1#8 := by
  rcases hdom with rfl | rfl | rfl <;> simp_all

theorem vals_eq_neg_of_sext_lt {v : BitVec 8}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (hs : (v.signExtend 32).slt 0#32 = true) : v = 0xFF#8 := by
  rcases hdom with rfl | rfl | rfl <;> simp_all

theorem vals_eq_zero_of_sext_eq {v : BitVec 8}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8)
    (hs : v.signExtend 32 = 0#32) : v = 0#8 := by
  rcases hdom with rfl | rfl | rfl <;> simp_all

theorem vals_eq_neg_of_ne_pos {v : BitVec 8}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) (hne : v.signExtend 32 ≠ 0#32)
    (hns : ¬ (0#32 : BitVec 32).slt (v.signExtend 32) = true) : v = 0xFF#8 := by
  rcases hdom with rfl | rfl | rfl
  · exact absurd rfl hne
  · exact absurd rfl hns
  · rfl

theorem sw_swap_swp3 {c : PlainCfg} {F0 : CNF Nat} {s0 s : PlainState}
    {dst new_unit : _} {p k1 k2 : Nat} (hsw : SwP3Inv c F0 s0 dst new_unit s)
    (href : p ∈ arenaClauseRefs s) (hk1 : k1 < arenaClauseSize s p)
    (hk2 : k2 < arenaClauseSize s p) :
    let hbd : p + 3 + arenaClauseSize s p ≤ s.arena.length := by
      have := (hsw.1.arena.refs_wf p href).2.2.1
      have := (hsw.1.arena.refs_wf p href).2.2.2.1
      have := hsw.1.lengths.arena_len_le; have := hsw.1.lengths.arena_len_arr; omega
    let ar' := (s.arena.set (p + 3 + k1) (s.arena[p + 3 + k2]'(by omega))).set
      (p + 3 + k2) (s.arena[p + 3 + k1]'(by omega))
    p ∈ arenaClauseRefs { s with arena := ar' } ∧
    SwP3Inv c F0 s0 dst new_unit { s with arena := ar' } ∧
    arenaClauseSize { s with arena := ar' } p = arenaClauseSize s p := by
  intro hbd ar'
  obtain ⟨hcore, hrefs, hng⟩ := swapCl_lits_core hsw.1 href hk1 hk2
  have hsz_eq : arenaClauseSize { s with arena := ar' } p = arenaClauseSize s p := by
    unfold arenaClauseSize ar'; dsimp only
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  exact ⟨hrefs.symm ▸ href, ⟨hcore, hsw.2.1, hsw.2.2.1, hsw.2.2.2.1, hsw.2.2.2.2.1,
    hsw.2.2.2.2.2.1, hsw.2.2.2.2.2.2.1, hsw.2.2.2.2.2.2.2.1,
    fun r hr => (hng r (hrefs ▸ hr)).trans (hsw.2.2.2.2.2.2.2.2 r (hrefs ▸ hr))⟩, hsz_eq⟩

theorem sweep_ret {c : PlainCfg} {F0 : CNF Nat} {s0 s1 : PlainState}
    {R : Mem 64 → Prop} {Q : Post [i64]} {r : BitVec 64} {m1 : Mem 64}
    (hQ : ∀ r vals' lvl' rsns' trl' tp' te' unfl' wvec' wstk' arena' alen' wlen' wu' fred'
      ni' nr' nb' oom' heur' m',
      let s' : PlainState :=
        { s0 with
          vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
          trail_end := te', unflushed := unfl', wvec := wvec', wstk := wstk',
          arena := arena', arena_len := alen', wlen := wlen', wusable := wu',
          arena_garbage := 0#64, first_reducible := fred', num_irred := ni',
          num_redundant := nr', num_binary := nb', oom := oom', heur := heur' }
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 3#64) →
      heur'.rel_trigger = s0.heur.rel_trigger →
      (∀ i < te', (trl'[i]?.getD 0#32).toNat < 2 * c.mv) →
      (r = 0#64 ∨ r = 1#64 → PlainCoreInv c F0 s' ∧ oom' = 0#64) →
      (0 < s0.cur_level → r = 0#64 → vals' = s0.vals ∧ lvl' = s0.lvl ∧ trl' = s0.trl ∧
        tp' = s0.trail_pos ∧ te' = s0.trail_end) →
      (r = 1#64 → s0.cur_level = 0 ∧ s0.trail_end < te') →
      (r = 2#64 → s0.cur_level = 0 ∧ F0.Unsat) →
      (PlainMem c s' ⋆ R) m' → Q (r, ()) m')
    (hsame : SameSwPre s0 s1) (hag : s1.arena_garbage = 0#64) (hlen : s1.LengthsOk c)
    (hr : r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 3#64)
    (hrt : s1.heur.rel_trigger = s0.heur.rel_trigger)
    (htrl : ∀ i < s1.trail_end, (s1.trl[i]?.getD 0#32).toNat < 2 * c.mv)
    (h01 : r = 0#64 ∨ r = 1#64 → PlainCoreInv c F0 s1 ∧ s1.oom = 0#64)
    (hk0 : 0 < s0.cur_level → r = 0#64 →
      s1.vals = s0.vals ∧ s1.lvl = s0.lvl ∧ s1.trl = s0.trl ∧
      s1.trail_pos = s0.trail_pos ∧ s1.trail_end = s0.trail_end)
    (h1 : r = 1#64 → s0.cur_level = 0 ∧ s0.trail_end < s1.trail_end)
    (h2 : r = 2#64 → s0.cur_level = 0 ∧ F0.Unsat)
    (hm : (PlainMem c s1 ⋆ R) m1) : Q (r, ()) m1 := by
  have heq := hsame.eq hag
  exact hQ r _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1
    (heq ▸ hlen) hr hrt htrl (fun h => heq ▸ h01 h) hk0 h1 h2 (heq ▸ hm)

theorem SameSwPre.cur_level {s0 s : PlainState} (h : SameSwPre s0 s) :
    s.cur_level = s0.cur_level := h.2.2.2.1

theorem sw1_skip_zero {c : PlainCfg} {F0 : CNF Nat} {s0 s1 : PlainState} {l : BitVec 64}
    (hs1 : SwP1Inv c F0 s0 l.toNat s1) (hl_lt : l.toNat < 2 * c.mv)
    (hl1_eq : (l + 1).toNat = l.toNat + 1) (hsz0 : watchSize s1 l.toNat = 0) :
    SwP1Inv c F0 s0 (l + 1).toNat s1 := by
  rw [hl1_eq]
  exact ⟨by omega, hs1.2.1, hs1.2.2.1, hs1.2.2.2.1, hs1.2.2.2.2.1, hs1.2.2.2.2.2.1,
    hs1.2.2.2.2.2.2.1, hs1.2.2.2.2.2.2.2.1, hs1.2.2.2.2.2.2.2.2.1,
    hs1.2.2.2.2.2.2.2.2.2.1, hs1.2.2.2.2.2.2.2.2.2.2.1, hs1.2.2.2.2.2.2.2.2.2.2.2.1,
    hs1.2.2.2.2.2.2.2.2.2.2.2.2.1, hs1.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hs1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    binWatchesOnly_skip_zero hs1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 hsz0⟩

theorem sw1_bin_step {c : PlainCfg} {F0 : CNF Nat} {s1 : PlainState} {R : Mem 64 → Prop}
    {l p q : BitVec 64} {wstk' : List (BitVec 32)} {nb'' : BitVec 64} {mb : Mem 64}
    (hq_lo : watchOff s1 l.toNat ≤ q.toNat) (hqp : q.toNat ≤ p.toNat)
    (hp_lt : p.toNat < watchOff s1 l.toNat + watchSize s1 l.toNat)
    (hws_len : s1.wstk.length = c.wcap) (hlen_w : wstk'.length = c.wcap)
    (hout : ∀ m, m < watchOff s1 l.toNat ∨ watchOff s1 l.toNat + watchSize s1 l.toNat ≤ m →
      wstk'[m]? = s1.wstk[m]?)
    (hsuf : ∀ m, p.toNat ≤ m → m < watchOff s1 l.toNat + watchSize s1 l.toNat →
      wstk'[m]? = s1.wstk[m]?)
    (hbin_q : ∀ k < q.toNat - watchOff s1 l.toNat,
      ∃ w, wstk'[watchOff s1 l.toNat + k]? = some w ∧ BinWatchOk c F0 l.toNat w)
    (hp1 : (p + 1).toNat = p.toNat + 1) (hq1 : (q + 1).toNat = q.toNat + 1)
    (hp_w : p.toNat < wstk'.length) (hq_w : q.toNat < wstk'.length)
    (hbin : BinWatchOk c F0 l.toNat wstk'[p.toNat] ∧
      p.toNat + 1 ≤ watchOff s1 l.toNat + watchSize s1 l.toNat ∧
      WatchSliceOk c F0 s1 l.toNat (p.toNat + 1)
        (watchOff s1 l.toNat + watchSize s1 l.toNat - (p.toNat + 1)))
    (hmb : (PlainMem c { s1 with
      wstk := wstk'.set q.toNat wstk'[p.toNat], num_binary := nb'' } ⋆ R) mb) :
    ∃ (wstk'' : List (BitVec 32)) (nb'' : BitVec 64),
      watchOff s1 l.toNat ≤ (q + 1).toNat ∧ (q + 1).toNat ≤ (p + 1).toNat ∧
      (p + 1).toNat ≤ watchOff s1 l.toNat + watchSize s1 l.toNat ∧
      p.toNat < (p + 1).toNat ∧ wstk''.length = c.wcap ∧
      (∀ m, m < watchOff s1 l.toNat ∨ watchOff s1 l.toNat + watchSize s1 l.toNat ≤ m →
        wstk''[m]? = s1.wstk[m]?) ∧
      (∀ m, (p + 1).toNat ≤ m → m < watchOff s1 l.toNat + watchSize s1 l.toNat →
        wstk''[m]? = s1.wstk[m]?) ∧
      WatchSliceOk c F0 s1 l.toNat (p + 1).toNat
        (watchOff s1 l.toNat + watchSize s1 l.toNat - (p + 1).toNat) ∧
      (∀ k < (q + 1).toNat - watchOff s1 l.toNat,
        ∃ w, wstk''[watchOff s1 l.toNat + k]? = some w ∧ BinWatchOk c F0 l.toNat w) ∧
      (PlainMem c { s1 with wstk := wstk'', num_binary := nb'' } ⋆ R) mb := by
  have hpush := sweep_prune_push (ws0 := s1.wstk) (ws := wstk') (off := watchOff s1 l.toNat)
    (end_ := watchOff s1 l.toNat + watchSize s1 l.toNat) (p := p.toNat) (q := q.toNat)
    (w0 := wstk'[p.toNat]) hq_lo hqp hp_lt (hlen_w.trans hws_len.symm) hq_w hout hsuf
  refine ⟨wstk'.set q.toNat wstk'[p.toNat], nb'', by omega, by omega, by omega, by omega,
    hpush.1.trans hws_len, hpush.2.1, fun m hm1 hm2 => hpush.2.2.1 m (by omega) hm2,
    by simpa only [hp1] using hbin.2.2, fun k hk => ?_, hmb⟩
  rw [hq1] at hk
  by_cases hkq : k = q.toNat - watchOff s1 l.toNat
  · subst hkq
    exact ⟨wstk'[p.toNat], by rw [show watchOff s1 l.toNat +
      (q.toNat - watchOff s1 l.toNat) = q.toNat by omega, List.getElem?_set_self hq_w], hbin.1⟩
  · obtain ⟨w, hw, hok⟩ := hbin_q k (by omega)
    exact ⟨w, (by rw [List.getElem?_set_ne (by omega)]; exact hw), hok⟩

theorem sw1_finish_z {c : PlainCfg} {F0 : CNF Nat} {s0 s1 : PlainState} {R : Mem 64 → Prop}
    {l : BitVec 64} {wstk' : List (BitVec 32)} {nb' : BitVec 64} {mw : Mem 64}
    (hs1 : SwP1Inv c F0 s0 l.toNat s1) (hag1 : s1.arena_garbage = s0.arena_garbage)
    (hl_lt : l.toNat < 2 * c.mv) (hl1_eq : (l + 1).toNat = l.toNat + 1)
    (h2l1 : ((l <<< (1 : Nat)) + 1#64).toNat = 2 * l.toNat + 1)
    (hw1_len : ((l <<< (1 : Nat)) + 1#64).toNat < s1.wvec.length) (hlen_w : wstk'.length = c.wcap)
    (hout : ∀ q, q < watchOff s1 l.toNat ∨
      watchOff s1 l.toNat + watchSize s1 l.toNat ≤ q → wstk'[q]? = s1.wstk[q]?)
    (hms1 : (PlainMem c { s1 with
      wstk := wstk', wvec := s1.wvec.set (2 * l.toNat + 1) 0#32, num_binary := nb',
      wusable := s1.wusable +
        (s1.wvec[((l <<< (1 : Nat)) + 1#64).toNat]'hw1_len).setWidth 64 } ⋆ R) mw) :
    ∃ s2 : PlainState, SwP1Inv c F0 s0 (l + 1).toNat s2 ∧ s2.arena_garbage = s0.arena_garbage ∧
      (PlainMem c s2 ⋆ R) mw := by
  obtain ⟨_, hlen1, hsame1, hv1, hlvl1, hrsn1, htrl1, htp1, hte1, hunf1, har1, hal1, hwl1, hoom1,
    hrt1, hb1⟩ := hs1
  have hfin := sweep_finish_slice (c := c) (F0 := F0) (s := s1) (l := l.toNat) (new_sz := 0)
    (wstk' := wstk')
    (wusable' := s1.wusable + (s1.wvec[((l <<< (1 : Nat)) + 1#64).toNat]'hw1_len).setWidth 64)
    (num_binary' := nb') hlen1 hb1 hl_lt hlen_w (Nat.zero_le _) hout
    fun _ h => absurd h (Nat.not_lt_zero _)
  have := h2l1
  exact ⟨_, ⟨by omega, hfin.1, hsame1, hv1, hlvl1, hrsn1, htrl1, htp1, hte1, hunf1, har1, hal1,
    hwl1, hoom1, hrt1, hl1_eq ▸ hfin.2⟩, hag1, hms1⟩

theorem sw1_finish_q {c : PlainCfg} {F0 : CNF Nat} {s0 s1 : PlainState} {R : Mem 64 → Prop}
    {l q nb' : BitVec 64} {wstk' : List (BitVec 32)} {mw : Mem 64}
    (hs1 : SwP1Inv c F0 s0 l.toNat s1) (hag1 : s1.arena_garbage = s0.arena_garbage)
    (hl_lt : l.toNat < 2 * c.mv) (hl1_eq : (l + 1).toNat = l.toNat + 1)
    (h2l : (l <<< (1 : Nat)).toNat = 2 * l.toNat)
    (h2l1 : ((l <<< (1 : Nat)) + 1#64).toNat = 2 * l.toNat + 1)
    (hw0_len : (l <<< (1 : Nat)).toNat < s1.wvec.length)
    (hw1_len : ((l <<< (1 : Nat)) + 1#64).toNat < s1.wvec.length)
    (hq_lo : watchOff s1 l.toNat ≤ q.toNat)
    (hp_hi : q.toNat ≤ watchOff s1 l.toNat + watchSize s1 l.toNat)
    (hlen_w : wstk'.length = c.wcap)
    (hout : ∀ m, m < watchOff s1 l.toNat ∨
      watchOff s1 l.toNat + watchSize s1 l.toNat ≤ m → wstk'[m]? = s1.wstk[m]?)
    (hbin : ∀ k < q.toNat - watchOff s1 l.toNat,
      ∃ w, wstk'[watchOff s1 l.toNat + k]? = some w ∧ BinWatchOk c F0 l.toNat w)
    (hms1 : (PlainMem c { s1 with
      wstk := wstk',
      wvec := s1.wvec.set (2 * l.toNat + 1)
        ((q - (s1.wvec[(l <<< (1 : Nat)).toNat]'hw0_len).setWidth 64).truncate 32),
      num_binary := nb',
      wusable := s1.wusable +
        (((s1.wvec[(l <<< (1 : Nat)).toNat]'hw0_len).setWidth 64 +
          (s1.wvec[((l <<< (1 : Nat)) + 1#64).toNat]'hw1_len).setWidth 64) - q) } ⋆ R) mw) :
    ∃ s2 : PlainState, SwP1Inv c F0 s0 (l + 1).toNat s2 ∧ s2.arena_garbage = s0.arena_garbage ∧
      (PlainMem c s2 ⋆ R) mw := by
  obtain ⟨_, hlen1, hsame1, hv1, hlvl1, hrsn1, htrl1, htp1, hte1, hunf1, har1, hal1, hwl1, hoom1,
    hrt1, hb1⟩ := hs1
  have hcw := c.hwcap; unfold dimacsBound at hcw
  have hoff64 : ((s1.wvec[(l <<< (1 : Nat)).toNat]'hw0_len).setWidth 64).toNat =
      watchOff s1 l.toNat := by
    rw [bv_c0_zext32_64]; unfold watchOff
    rw [← h2l, List.getElem?_eq_getElem hw0_len, Option.getD_some]
  have hlay := hb1.1.layout; have hbdd := hlay.bounds l.toNat hl_lt
  have hlen_wc : watchOff s1 l.toNat + watchSize s1 l.toNat ≤ c.wcap := by
    have := hlen1.wlen_le; omega
  have hnews_eq : (q - (s1.wvec[(l <<< (1 : Nat)).toNat]'hw0_len).setWidth 64).truncate 32 =
      BitVec.ofNat 32 (q.toNat - watchOff s1 l.toNat) := by
    have hsub : (q - (s1.wvec[(l <<< (1 : Nat)).toNat]'hw0_len).setWidth 64).toNat =
        q.toNat - watchOff s1 l.toNat := by bv_omega
    rw [bv64_truncate32 (by omega), hsub]
  have hfin := sweep_finish_slice (c := c) (F0 := F0) (s := s1) (l := l.toNat)
    (new_sz := q.toNat - watchOff s1 l.toNat) (wstk' := wstk')
    (wusable' := s1.wusable +
      (((s1.wvec[(l <<< (1 : Nat)).toNat]'hw0_len).setWidth 64 +
        (s1.wvec[((l <<< (1 : Nat)) + 1#64).toNat]'hw1_len).setWidth 64) - q))
    (num_binary' := nb') hlen1 hb1 hl_lt hlen_w (by omega) hout hbin
  have hms1' : (PlainMem c { s1 with
      wstk := wstk', wvec := s1.wvec.set (2 * l.toNat + 1)
        (BitVec.ofNat 32 (q.toNat - watchOff s1 l.toNat)),
      num_binary := nb',
      wusable := s1.wusable +
        (((s1.wvec[(l <<< (1 : Nat)).toNat]'hw0_len).setWidth 64 +
          (s1.wvec[((l <<< (1 : Nat)) + 1#64).toNat]'hw1_len).setWidth 64) - q) } ⋆ R) mw := by
    simpa only [h2l1, hnews_eq] using hms1
  exact ⟨_, ⟨by omega, hfin.1, hsame1, hv1, hlvl1, hrsn1, htrl1, htp1, hte1, hunf1, har1, hal1,
    hwl1, hoom1, hrt1, hl1_eq ▸ hfin.2⟩, hag1, hms1'⟩

theorem sw2_rsn_hit {c : PlainCfg} {F0 : CNF Nat} {s0 s_2 : PlainState} {R : Mem 64 → Prop}
    {src dst : BitVec 64} {new_sz ir : BitVec 32} {ar1 : List (BitVec 32)} {mr : Mem 64}
    (hinv0 : PlainCoreInv c F0 s0) (hlen_2 : s_2.LengthsOk c)
    (htv_2 : TrailValsInv c F0 s_2) (hrr_2 : RsnRelocInv s0 s_2 src.toNat dst.toNat)
    (hscl_2 : s_2.cur_level = s0.cur_level)
    (hkeep_2 : 0 < s0.cur_level → s_2.vals = s0.vals ∧ s_2.lvl = s0.lvl ∧ s_2.trl = s0.trl ∧
      s_2.trail_pos = s0.trail_pos ∧ s_2.trail_end = s0.trail_end)
    (hsrc_ref : src.toNat ∈ arenaClauseRefs s0) (hdst_le : dst.toNat ≤ src.toNat)
    (hge3 : 3 ≤ new_sz.toNat) (har_e : ar1.length = c.arena_cap)
    (har1_le : dst.toNat + 3 + new_sz.toNat ≤ c.arena_cap)
    (hnohit : 0 < s0.cur_level →
      arenaClauseLits { s_2 with arena := ar1, arena_len := dst.toNat + 3 + new_sz.toNat }
        dst.toNat = arenaClauseLits s0 src.toNat)
    (hdst_in : dst.toNat ∈
      arenaClauseRefs { s_2 with arena := ar1, arena_len := dst.toNat + 3 + new_sz.toNat })
    (hdst_ng :
      arenaClauseGarb { s_2 with arena := ar1, arena_len := dst.toNat + 3 + new_sz.toNat }
        dst.toNat = false)
    (hrel : ∀ r ∈ arenaClauseRefs { s_2 with arena_len := dst.toNat },
      r ∈ arenaClauseRefs { s_2 with arena := ar1, arena_len := dst.toNat + 3 + new_sz.toNat } ∧
      arenaClauseGarb { s_2 with arena := ar1, arena_len := dst.toNat + 3 + new_sz.toNat } r =
        arenaClauseGarb { s_2 with arena_len := dst.toNat } r ∧
      arenaClauseLits { s_2 with arena := ar1, arena_len := dst.toNat + 3 + new_sz.toNat } r =
        arenaClauseLits { s_2 with arena_len := dst.toNat } r)
    (hsz_eq : (ar1[dst.toNat + 2]?.getD 0#32).toNat = new_sz.toNat)
    (htr_r : TrailValsInv c F0 { s_2 with arena := ar1 }) (hrs_len2 : s_2.rsns.length = c.mv)
    (hdi_lt : (dst + 3#64 + ir.setWidth 64).toNat < ar1.length)
    (hdi_eq : (dst + 3#64 + ir.setWidth 64).toNat = dst.toNat + 3 + ir.toNat)
    (hir_lt : ir.toNat < new_sz.toNat)
    (hlit_ar : ar1[(dst + 3#64 + ir.setWidth 64).toNat]'hdi_lt =
      ar1[dst.toNat + 3 + ir.toNat]'(by omega))
    (hlit_ir : (ar1[dst.toNat + 3 + ir.toNat]'(by omega)).toNat < 2 * c.mv)
    (hdom_v : s_2.vals[(ar1[dst.toNat + 3 + ir.toNat]'(by omega)).toNat]'(by
        rw [hlen_2.vals_len]; exact hlit_ir) = 0#8 ∨
      s_2.vals[(ar1[dst.toNat + 3 + ir.toNat]'(by omega)).toNat]'(by
        rw [hlen_2.vals_len]; exact hlit_ir) = 1#8 ∨
      s_2.vals[(ar1[dst.toNat + 3 + ir.toNat]'(by omega)).toNat]'(by
        rw [hlen_2.vals_len]; exact hlit_ir) = 0xFF#8)
    (hval_pos : (0#32 : BitVec 32).slt
      ((s_2.vals[(ar1[(dst + 3#64 + ir.setWidth 64).toNat]'hdi_lt).toNat]'(by
        rw [hlen_2.vals_len, hlit_ar]; exact hlit_ir)).signExtend 32) = true)
    (hrsn_eq : BitVec.setWidth 64 (s_2.rsns[(((ar1[(dst + 3#64 + ir.setWidth 64).toNat]'
        hdi_lt) >>> (1 : Nat)).setWidth 64).toNat]'(by
      rw [hrs_len2, hlit_ar, bv_c0_zext32_64, PlainReduceTactics.bv_c0_shr1n_32]; omega)) = src)
    (hmr : (PlainMem c { s_2 with
      arena := ar1,
      rsns := s_2.rsns.set (((ar1[(dst + 3#64 + ir.setWidth 64).toNat]'hdi_lt) >>>
        (1 : Nat)).setWidth 64).toNat (dst.truncate 32) } ⋆ R) mr) :
    ∃ rsns' : List (BitVec 32),
      RsnRelocInv s0 { s_2 with arena := ar1, rsns := rsns' }
        (arenaNextOff s0.arena s0.arena_len src.toNat) (dst.toNat + 3 + new_sz.toNat) ∧
      TrailValsInv c F0 { s_2 with arena := ar1, rsns := rsns' } ∧ rsns'.length = c.mv ∧
      (PlainMem c { s_2 with arena := ar1, rsns := rsns' } ⋆ R) mr := by
  have har := c.harena; unfold dimacsBound at har; have hlen_a := hinv0.lengths.arena_len_le
  have hsrc_lt : src.toNat < s0.arena_len := by have := (hinv0.arena.refs_wf _ hsrc_ref).1; omega
  have hs_val1 : s_2.vals[ar1[dst.toNat + 3 + ir.toNat].toNat]?.getD 0#8 = 1#8 := by
    rw [List.getElem?_eq_getElem (by rw [hlen_2.vals_len]; exact hlit_ir), Option.getD_some]
    exact vals_eq_one_of_sext_pos hdom_v (by simpa only [hlit_ar] using hval_pos)
  obtain ⟨idx0, hidx0, htrl0⟩ := (htv_2.vals_true_iff _ hlit_ir).mp hs_val1
  have hidx_v : (((ar1[(dst + 3#64 + ir.setWidth 64).toNat]'hdi_lt) >>>
      (1 : Nat)).setWidth 64).toNat = ar1[dst.toNat + 3 + ir.toNat].toNat / 2 := by
    rw [hlit_ar, bv_c0_zext32_64, PlainReduceTactics.bv_c0_shr1n_32]
  have h_rs_get : s_2.rsns[(((ar1[(dst + 3#64 + ir.setWidth 64).toNat]'hdi_lt) >>>
        (1 : Nat)).setWidth 64).toNat]'(by
        rw [hrs_len2, hlit_ar, bv_c0_zext32_64, PlainReduceTactics.bv_c0_shr1n_32]; omega) =
      s_2.rsns[ar1[dst.toNat + 3 + ir.toNat].toNat / 2]'(by rw [hrs_len2]; omega) :=
    Option.some.inj (by
      rw [← List.getElem?_eq_getElem, hidx_v,
        List.getElem?_eq_getElem (by rw [hrs_len2]; omega)])
  have hrsn_src : s_2.rsns[ar1[dst.toNat + 3 + ir.toNat].toNat / 2]?.getD 0xFFFFFFFF#32 =
      BitVec.ofNat 32 src.toNat := by
    apply BitVec.eq_of_toNat_eq
    have heq64 := congrArg BitVec.toNat hrsn_eq
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide)),
      h_rs_get] at heq64
    rw [List.getElem?_eq_getElem (by rw [hrs_len2]; omega), Option.getD_some,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show src.toNat < 2 ^ 32 by omega), heq64]
  have hpos_v : 0 < (s_2.lvl[ar1[dst.toNat + 3 + ir.toNat].toNat / 2]?.getD 0#32).toNat := by
    apply Classical.byContradiction; intro hz
    have h0 := htv_2.level0_rsn_none idx0 hidx0 (by rw [htrl0]; omega)
    rw [htrl0, hrsn_src] at h0
    have hct := congrArg BitVec.toNat h0
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show src.toNat < 2 ^ 32 by omega)] at hct
    omega
  have hcur : 0 < s0.cur_level := by
    have := htv_2.lvl_le idx0 hidx0; rw [htrl0, hscl_2] at this; omega
  have hdr_lt : dst.truncate 32 = BitVec.ofNat 32 dst.toNat := bv64_truncate32 (by omega)
  have hvals_slt : (0#8).slt (s0.vals[ar1[dst.toNat + 3 + ir.toNat].toNat]?.getD 0#8) = true := by
    rw [← (hkeep_2 hcur).1, hs_val1]; decide
  have hlit_ar1 : ar1[dst.toNat + 3 + ir.toNat]? = some ar1[dst.toNat + 3 + ir.toNat] :=
    List.getElem?_eq_getElem (by omega)
  have hrr_hit := rsnReloc_step_hit hinv0 hrr_2 hcur hsrc_ref hdst_le hir_lt hsz_eq har_e har1_le
    hlit_ar1 (hnohit hcur) hdst_in hdst_ng hrel (by omega) hvals_slt hrsn_src
  have htv_hit := trailValsInv_rsn_set htr_r (v := ar1[dst.toNat + 3 + ir.toNat].toNat / 2)
    (val := BitVec.ofNat 32 dst.toNat) (by rw [hrs_len2]; omega) hpos_v
  exact ⟨_, hrr_hit, htv_hit, by rw [List.length_set, hrs_len2],
    by simpa only [hidx_v, hdr_lt] using hmr⟩

theorem sw2_rsn_neg1 {s0 s_2 : PlainState} {c : PlainCfg} {src dst : BitVec 64} {ir : BitVec 32}
    {ar1 : List (BitVec 32)} (hhar : ar1.length = c.arena_cap)
    (hdi_lt : (dst + 3#64 + ir.setWidth 64).toNat < ar1.length)
    (hdi_eq : (dst + 3#64 + ir.setWidth 64).toNat = dst.toNat + 3 + ir.toNat)
    (hlit_ar : ar1[(dst + 3#64 + ir.setWidth 64).toNat]'hdi_lt =
      ar1[dst.toNat + 3 + ir.toNat]'(by omega))
    (hsrc_bd : src.toNat < c.arena_cap) (har_bd : c.arena_cap < 2 * 2 ^ 28)
    (hrs_l : s_2.rsns.length = c.mv)
    (hlit_ir : (ar1[dst.toNat + 3 + ir.toNat]'(by omega)).toNat < 2 * c.mv)
    (hne : BitVec.setWidth 64 (s_2.rsns[(((ar1[(dst + 3#64 + ir.setWidth 64).toNat]'
        hdi_lt) >>> (1 : Nat)).setWidth 64).toNat]'(by
      rw [hrs_l, hlit_ar, bv_c0_zext32_64, PlainReduceTactics.bv_c0_shr1n_32]; omega)) ≠ src) :
    let lit := ar1[dst.toNat + 3 + ir.toNat]?.getD 0#32
    ¬ (lit.toNat / 2 < c.mv ∧ (0#8).slt (s0.vals[lit.toNat]?.getD 0#8) = true ∧
      s_2.rsns[lit.toNat / 2]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 src.toNat) := by
  dsimp only; intro h; obtain ⟨_, _, hrs⟩ := h
  have h_ar_d : ar1[dst.toNat + 3 + ir.toNat]?.getD 0#32 = ar1[dst.toNat + 3 + ir.toNat] := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  simp only [h_ar_d] at hrs
  rw [List.getElem?_eq_getElem (by rw [hrs_l]; omega), Option.getD_some] at hrs
  have hidx_v : (((ar1[(dst + 3#64 + ir.setWidth 64).toNat]'hdi_lt) >>>
      (1 : Nat)).setWidth 64).toNat = ar1[dst.toNat + 3 + ir.toNat].toNat / 2 := by
    rw [hlit_ar, bv_c0_zext32_64, PlainReduceTactics.bv_c0_shr1n_32]
  have h_rs_get : s_2.rsns[(((ar1[(dst + 3#64 + ir.setWidth 64).toNat]'hdi_lt) >>>
        (1 : Nat)).setWidth 64).toNat]'(by
        rw [hrs_l, hlit_ar, bv_c0_zext32_64, PlainReduceTactics.bv_c0_shr1n_32]; omega) =
      s_2.rsns[ar1[dst.toNat + 3 + ir.toNat].toNat / 2]'(by rw [hrs_l]; omega) :=
    Option.some.inj (by
      rw [← List.getElem?_eq_getElem, hidx_v,
        List.getElem?_eq_getElem (by rw [hrs_l]; omega)])
  rw [h_rs_get] at hne
  apply hne; apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide)), hrs,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem sw2_rsn_neg_le {s0 s_2 : PlainState} {c : PlainCfg} {src dst : BitVec 64} {ir : BitVec 32}
    {ar1 : List (BitVec 32)} (har1 : ar1.length = c.arena_cap)
    (hkeep : 0 < s0.cur_level → s_2.vals = s0.vals ∧ s_2.lvl = s0.lvl ∧ s_2.trl = s0.trl ∧
      s_2.trail_pos = s0.trail_pos ∧ s_2.trail_end = s0.trail_end)
    (hvals_l : s_2.vals.length = 2 * c.mv)
    (hdi_lt : (dst + 3#64 + ir.setWidth 64).toNat < ar1.length)
    (hdi_eq : (dst + 3#64 + ir.setWidth 64).toNat = dst.toNat + 3 + ir.toNat)
    (hlit_ar : ar1[(dst + 3#64 + ir.setWidth 64).toNat]'hdi_lt =
      ar1[dst.toNat + 3 + ir.toNat]'(by omega))
    (hlit_ir : (ar1[dst.toNat + 3 + ir.toNat]'(by omega)).toNat < 2 * c.mv)
    (hdom : s_2.vals[(ar1[dst.toNat + 3 + ir.toNat]'(by omega)).toNat]'(by omega) = 0#8 ∨
      s_2.vals[(ar1[dst.toNat + 3 + ir.toNat]'(by omega)).toNat]'(by omega) = 1#8 ∨
      s_2.vals[(ar1[dst.toNat + 3 + ir.toNat]'(by omega)).toNat]'(by omega) = 0xFF#8)
    (hs : ¬ (0#32 : BitVec 32).slt
      ((s_2.vals[(ar1[(dst + 3#64 + ir.setWidth 64).toNat]'hdi_lt).toNat]'(by
        rw [hvals_l, hlit_ar]; exact hlit_ir)).signExtend 32) = true) :
    0 < s0.cur_level → let lit := ar1[dst.toNat + 3 + ir.toNat]?.getD 0#32
    ¬ (lit.toNat / 2 < c.mv ∧ (0#8).slt (s0.vals[lit.toNat]?.getD 0#8) = true ∧
      s_2.rsns[lit.toNat / 2]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 src.toNat) := by
  intro hcur; dsimp only; intro h; obtain ⟨_, hv0, _⟩ := h
  have h_ar_d : ar1[dst.toNat + 3 + ir.toNat]?.getD 0#32 = ar1[dst.toNat + 3 + ir.toNat] := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  simp only [h_ar_d, ← (hkeep hcur).1] at hv0
  rw [List.getElem?_eq_getElem (by rw [hvals_l]; omega), Option.getD_some] at hv0
  have hs' := hs; simp only [hlit_ar] at hs'
  rcases hdom with h | h | h <;> rw [h] at hv0 hs' <;>
    first | exact absurd hv0 (by decide) | exact hs' (by decide)

theorem sw2_rsn_neg_z {s0 s_2 : PlainState} {c : PlainCfg} {src dst : BitVec 64} {ir : BitVec 32}
    {ar1 : List (BitVec 32)} (har1 : ar1.length = c.arena_cap)
    (hkeep : 0 < s0.cur_level → s_2.vals = s0.vals ∧ s_2.lvl = s0.lvl ∧ s_2.trl = s0.trl ∧
      s_2.trail_pos = s0.trail_pos ∧ s_2.trail_end = s0.trail_end)
    (hvals_l : s_2.vals.length = 2 * c.mv)
    (hdi_lt : (dst + 3#64 + ir.setWidth 64).toNat < ar1.length)
    (hdi_eq : (dst + 3#64 + ir.setWidth 64).toNat = dst.toNat + 3 + ir.toNat)
    (hlit_ar : ar1[(dst + 3#64 + ir.setWidth 64).toNat]'hdi_lt =
      ar1[dst.toNat + 3 + ir.toNat]'(by omega))
    (hlit_ir : (ar1[dst.toNat + 3 + ir.toNat]'(by omega)).toNat < 2 * c.mv)
    (hdom : s_2.vals[(ar1[dst.toNat + 3 + ir.toNat]'(by omega)).toNat]'(by omega) = 0#8 ∨
      s_2.vals[(ar1[dst.toNat + 3 + ir.toNat]'(by omega)).toNat]'(by omega) = 1#8 ∨
      s_2.vals[(ar1[dst.toNat + 3 + ir.toNat]'(by omega)).toNat]'(by omega) = 0xFF#8)
    (hs : ¬ ((s_2.vals[(ar1[(dst + 3#64 + ir.setWidth 64).toNat]'hdi_lt).toNat]'(by
        rw [hvals_l, hlit_ar]; exact hlit_ir)).signExtend 32) ≠ 0#32) :
    0 < s0.cur_level → let lit := ar1[dst.toNat + 3 + ir.toNat]?.getD 0#32
    ¬ (lit.toNat / 2 < c.mv ∧ (0#8).slt (s0.vals[lit.toNat]?.getD 0#8) = true ∧
      s_2.rsns[lit.toNat / 2]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 src.toNat) := by
  intro hcur; dsimp only; intro h; obtain ⟨_, hv0, _⟩ := h
  have h_ar_d : ar1[dst.toNat + 3 + ir.toNat]?.getD 0#32 = ar1[dst.toNat + 3 + ir.toNat] := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  simp only [h_ar_d, ← (hkeep hcur).1] at hv0
  rw [List.getElem?_eq_getElem (by rw [hvals_l]; omega), Option.getD_some] at hv0
  have hs' := hs; simp only [hlit_ar] at hs'
  rcases hdom with h | h | h <;> rw [h] at hv0 hs' <;>
    first | exact absurd hv0 (by decide) | exact hs' (by decide)

theorem sw2_rsn_neg_mv {s0 s_2 : PlainState} {c : PlainCfg} {src dst : BitVec 64} {ir : BitVec 32}
    {ar1 : List (BitVec 32)}
    (hdi_lt : (dst + 3#64 + ir.setWidth 64).toNat < ar1.length)
    (hdi_eq : (dst + 3#64 + ir.setWidth 64).toNat = dst.toNat + 3 + ir.toNat)
    (hlit_ar : ar1[(dst + 3#64 + ir.setWidth 64).toNat]'hdi_lt =
      ar1[dst.toNat + 3 + ir.toNat]'(by rw [← hdi_eq]; exact hdi_lt))
    (hnc : ¬ (BitVec.setWidth 64 ((ar1[(dst + 3#64 + ir.setWidth 64).toNat]'hdi_lt) >>>
      (1 : Nat))).toNat < c.mv) :
    let lit := ar1[dst.toNat + 3 + ir.toNat]?.getD 0#32
    ¬ (lit.toNat / 2 < c.mv ∧ (0#8).slt (s0.vals[lit.toNat]?.getD 0#8) = true ∧
      s_2.rsns[lit.toNat / 2]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 src.toNat) := by
  dsimp only; intro h; obtain ⟨hmv_l, _⟩ := h
  have h_ar_d : ar1[dst.toNat + 3 + ir.toNat]?.getD 0#32 =
      ar1[dst.toNat + 3 + ir.toNat]'(by rw [← hdi_eq]; exact hdi_lt) := by
    rw [List.getElem?_eq_getElem (by rw [← hdi_eq]; exact hdi_lt), Option.getD_some]
  simp only [h_ar_d] at hmv_l
  rw [hlit_ar, bv_c0_zext32_64, PlainReduceTactics.bv_c0_shr1n_32] at hnc
  exact hnc hmv_l

theorem sw2_rsn_nohit_done {c : PlainCfg} {F0 : CNF Nat} {s0 s_2 : PlainState}
    {src dst : BitVec 64} {new_sz : BitVec 32} {ar1 : List (BitVec 32)}
    (hinv0 : PlainCoreInv c F0 s0) (hrm0 : 0 < s0.cur_level → ReasonsMarked s0)
    (hrr_2 : RsnRelocInv s0 s_2 src.toNat dst.toNat) (hsrc_ref : src.toNat ∈ arenaClauseRefs s0)
    (hsz_ar1 : (ar1[dst.toNat + 2]?.getD 0#32).toNat = new_sz.toNat)
    (har_e : ar1.length = c.arena_cap)
    (har1_le : dst.toNat + 3 + new_sz.toNat ≤ c.arena_cap)
    (hnohit : 0 < s0.cur_level →
      arenaClauseLits { s_2 with arena := ar1, arena_len := dst.toNat + 3 + new_sz.toNat }
        dst.toNat = arenaClauseLits s0 src.toNat)
    (hrel : ∀ r ∈ arenaClauseRefs { s_2 with arena_len := dst.toNat },
      r ∈ arenaClauseRefs { s_2 with arena := ar1, arena_len := dst.toNat + 3 + new_sz.toNat } ∧
      arenaClauseGarb { s_2 with arena := ar1, arena_len := dst.toNat + 3 + new_sz.toNat } r =
        arenaClauseGarb { s_2 with arena_len := dst.toNat } r ∧
      arenaClauseLits { s_2 with arena := ar1, arena_len := dst.toNat + 3 + new_sz.toNat } r =
        arenaClauseLits { s_2 with arena_len := dst.toNat } r)
    (htr_r : TrailValsInv c F0 { s_2 with arena := ar1 }) (hrs_len2 : s_2.rsns.length = c.mv)
    (hcond : 0 < s0.cur_level → (s0.arena[src.toNat]?.getD 0#32 &&& 0x00200000#32) = 0#32 ∨
      ∀ k < new_sz.toNat, let lit := ar1[dst.toNat + 3 + k]?.getD 0#32;
        ¬ (lit.toNat / 2 < c.mv ∧ (0#8).slt (s0.vals[lit.toNat]?.getD 0#8) = true ∧
          s_2.rsns[lit.toNat / 2]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 src.toNat)) :
    RsnRelocInv s0 { s_2 with arena := ar1, rsns := s_2.rsns }
      (arenaNextOff s0.arena s0.arena_len src.toNat) (dst.toNat + 3 + new_sz.toNat) ∧
    TrailValsInv c F0 { s_2 with arena := ar1, rsns := s_2.rsns } ∧ s_2.rsns.length = c.mv := by
  by_cases hcl0 : s0.cur_level = 0
  · exact ⟨rsnReloc_l0 hcl0 hrr_2.1, htr_r, hrs_len2⟩
  · have hcur := Nat.pos_of_ne_zero hcl0
    exact ⟨rsnReloc_step_nohit hinv0 hrm0 hrr_2 hsrc_ref hsz_ar1 har_e har1_le (hnohit hcur) hrel
      (Or.inr (hcond hcur)), htr_r, hrs_len2⟩

theorem sw2_sz1_prep {c : PlainCfg} {F0 : CNF Nat}
    {dst : BitVec 64} {new_sz : BitVec 32} {ar_o : List (BitVec 32)}
    (hsz1 : new_sz.toNat = 1) (hu_eq : (dst + 3#64).toNat = dst.toNat + 3)
    (hud_lt : (dst + 3#64).toNat < ar_o.length)
    (hlits_o : ∀ k < new_sz.toNat, (ar_o[dst.toNat + 3 + k]?.getD 0#32).toNat < 2 * c.mv)
    (hent_fin : F0.EntailsClause
      (cnfClause (((ar_o.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat))) :
    (ar_o[(dst + 3#64).toNat]'hud_lt).toNat < 2 * c.mv ∧
      F0.EntailsClause (cnfClause [(ar_o[(dst + 3#64).toNat]'hud_lt).toNat]) := by
  have he_u : ar_o[(dst + 3#64).toNat]'hud_lt = ar_o[dst.toNat + 3]'(by omega) :=
    Option.some.inj (by
      rw [← List.getElem?_eq_getElem hud_lt, hu_eq, List.getElem?_eq_getElem (by omega)])
  have hulit : (ar_o[(dst + 3#64).toNat]'hud_lt).toNat < 2 * c.mv := by
    have h0 := hlits_o 0 (by omega)
    rw [Nat.add_zero, List.getElem?_eq_getElem (by omega), Option.getD_some] at h0
    rwa [he_u]
  have hl0 : F0.EntailsClause (cnfClause [(ar_o[(dst + 3#64).toNat]'hud_lt).toNat]) := by
    rw [hsz1, drop_head_eq (by rw [hu_eq] at hud_lt; exact hud_lt),
      List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil] at hent_fin
    rwa [he_u]
  exact ⟨hulit, hl0⟩

theorem sw2_sz2_prep {c : PlainCfg} {F0 : CNF Nat} {dst : BitVec 64} {new_sz : BitVec 32}
    {ar_o : List (BitVec 32)}
    (hsz2 : new_sz.toNat = 2)
    (h3_eq : (dst + 3#64).toNat = dst.toNat + 3) (h4_eq : (dst + 4#64).toNat = dst.toNat + 4)
    (hd3_lt : (dst + 3#64).toNat < ar_o.length) (hd4_lt : (dst + 4#64).toNat < ar_o.length)
    (hlits_o : ∀ k < new_sz.toNat, (ar_o[dst.toNat + 3 + k]?.getD 0#32).toNat < 2 * c.mv)
    (hent_fin : F0.EntailsClause
      (cnfClause (((ar_o.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat))) :
    let l0 := ar_o[(dst + 3#64).toNat]'hd3_lt
    let l1 := ar_o[(dst + 4#64).toNat]'hd4_lt
    let b0 := (l1 &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    let b1 := (l0 &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    l0.toNat < 2 * c.mv ∧ l1.toNat < 2 * c.mv ∧
    BinWatchOk c F0 l0.toNat b0 ∧ BinWatchOk c F0 l1.toNat b1 ∧
    b0 ≠ 0xFFFFFFFF#32 ∧ b1 ≠ 0xFFFFFFFF#32 := by
  have he3 : ar_o[(dst + 3#64).toNat]'hd3_lt = ar_o[dst.toNat + 3]'(by omega) :=
    Option.some.inj (by
      rw [← List.getElem?_eq_getElem hd3_lt, h3_eq, List.getElem?_eq_getElem (by omega)])
  have he4 : ar_o[(dst + 4#64).toNat]'hd4_lt = ar_o[dst.toNat + 3 + 1]'(by omega) :=
    Option.some.inj (by
      rw [← List.getElem?_eq_getElem hd4_lt,
        show (dst + 4#64).toNat = dst.toNat + 3 + 1 by rw [h4_eq],
        List.getElem?_eq_getElem (by omega)])
  have hl0 : (ar_o[(dst + 3#64).toNat]'hd3_lt).toNat < 2 * c.mv := by
    have h0 := hlits_o 0 (by omega)
    rw [Nat.add_zero, List.getElem?_eq_getElem (by omega), Option.getD_some] at h0; rwa [he3]
  have hl1 : (ar_o[(dst + 4#64).toNat]'hd4_lt).toNat < 2 * c.mv := by
    have h1 := hlits_o 1 (by omega)
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h1; rwa [he4]
  have hent_2 : F0.EntailsClause
      (cnfClause [(ar_o[(dst + 3#64).toNat]'hd3_lt).toNat,
        (ar_o[(dst + 4#64).toNat]'hd4_lt).toNat]) := by
    have : ((ar_o.drop (dst.toNat + 3)).take 2).map BitVec.toNat =
        [(ar_o[(dst + 3#64).toNat]'hd3_lt).toNat, (ar_o[(dst + 4#64).toNat]'hd4_lt).toNat] := by
      rw [drop_head_eq (by rw [h3_eq] at hd3_lt; exact hd3_lt), List.take_succ_cons,
        drop_head_eq (by rw [h4_eq] at hd4_lt; omega), List.take_succ_cons, List.take_zero,
        List.map_cons, List.map_cons, List.map_nil, he3, he4]
    rwa [hsz2, this] at hent_fin
  obtain ⟨hb0, hb1, hne0, hne1⟩ := binWatchOk_pair hl0 hl1 hent_2
  exact ⟨hl0, hl1, hb0, hb1, hne0, hne1⟩

theorem sw2_filt_push {c : PlainCfg} {F0 : CNF Nat} {s0 s_2 : PlainState} {R : Mem 64 → Prop}
    {src dst : BitVec 64} {nsz i : BitVec 32} {ar_i : List (BitVec 32)} {mw : Mem 64}
    (hnsz_le : nsz.toNat ≤ i.toNat) (hi_lt : i.toNat < arenaClauseSize s0 src.toNat)
    (hwf0_bd : src.toNat + 3 + arenaClauseSize s0 src.toNat ≤ s0.arena_len)
    (hlen_a : s0.arena_len ≤ c.arena_cap) (hdst_le : dst.toNat ≤ src.toNat)
    (har_i : ar_i.length = c.arena_cap)
    (hsi3_lt : (src + 3#64 + i.setWidth 64).toNat < ar_i.length)
    (hpre_i : ∀ k < dst.toNat, ar_i[k]? = s_2.arena[k]?)
    (hsuf_i : ∀ k, src.toNat + 3 + i.toNat ≤ k → k < s0.arena_len → ar_i[k]? = s_2.arena[k]?)
    (hlits_i : ∀ k < nsz.toNat, (ar_i[dst.toNat + 3 + k]?.getD 0#32).toNat < 2 * c.mv)
    (hent_i : F0.EntailsClause (cnfClause ((((ar_i.drop (dst.toNat + 3)).take nsz.toNat).map
        BitVec.toNat) ++ ((ar_i[src.toNat + 3 + i.toNat]'(by omega)).toNat ::
      (((s0.arena.drop (src.toNat + 3 + (i.toNat + 1))).take
        (arenaClauseSize s0 src.toNat - (i.toNat + 1))).map BitVec.toNat)))))
    (hlit_lt : (ar_i[(src + 3#64 + i.setWidth 64).toNat]'hsi3_lt).toNat < 2 * c.mv)
    (hlit_ar : ar_i[(src + 3#64 + i.setWidth 64).toNat]'hsi3_lt =
      ar_i[src.toNat + 3 + i.toNat]'(by omega))
    (hdi_eq : (dst + 3#64 + nsz.setWidth 64).toNat = dst.toNat + 3 + nsz.toNat)
    (hnsz1 : (nsz + 1#32).toNat = nsz.toNat + 1)
    (hmw : (PlainMem c
      { s_2 with
        arena := ar_i.set (dst + 3#64 + nsz.setWidth 64).toNat
          (ar_i[(src + 3#64 + i.setWidth 64).toNat]'hsi3_lt) } ⋆ R) mw) :
    ∃ ar_s : List (BitVec 32),
      SwFiltInv c F0 s0 s_2 src.toNat dst.toNat (arenaClauseSize s0 src.toNat)
        (nsz + 1#32).toNat (i.toNat + 1) ar_s ∧ (PlainMem c { s_2 with arena := ar_s } ⋆ R) mw := by
  have har_w := arenaClauseLits_take_set_append (ar := ar_i) (dst := dst.toNat) (n := nsz.toNat)
    (lit := ar_i[(src + 3#64 + i.setWidth 64).toNat]'hsi3_lt) (by rw [har_i]; omega)
  have hlen_w : (ar_i.set (dst.toNat + 3 + nsz.toNat)
      (ar_i[(src + 3#64 + i.setWidth 64).toNat]'hsi3_lt)).length = c.arena_cap := by
    rw [List.length_set, har_i]
  have hent_w := entails_append_drop_cons hent_i
  rw [← hlit_ar, ← har_w] at hent_w
  exact ⟨ar_i.set (dst.toNat + 3 + nsz.toNat) _, ⟨by omega, by omega, hlen_w,
    fun k hk => by rw [List.getElem?_set_ne (by omega)]; exact hpre_i k hk,
    fun k hk1 hk2 => by rw [List.getElem?_set_ne (by omega)]; exact hsuf_i k (by omega) hk2,
    fun k hk => by
      rw [hnsz1] at hk
      by_cases hkn : k = nsz.toNat
      · subst hkn; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hlit_lt
      · rw [List.getElem?_set_ne (by omega)]; exact hlits_i k (by omega),
    by simpa only [hnsz1] using hent_w⟩, by simpa only [hdi_eq] using hmw⟩

theorem sw2_filt_fals {c : PlainCfg} {F0 : CNF Nat} {s0 s_2 : PlainState}
    {src dst : BitVec 64} {nsz i : BitVec 32} {ar_i : List (BitVec 32)}
    (hsame_2 : SameSwPre s0 s_2) (htv_2 : TrailValsInv c F0 s_2) (hcl0 : s0.cur_level = 0)
    (hva_len : s_2.vals.length = 2 * c.mv)
    (hnsz_le : nsz.toNat ≤ i.toNat) (hi_lt : i.toNat < arenaClauseSize s0 src.toNat)
    (har_i : ar_i.length = c.arena_cap)
    (hsi3_lt : (src + 3#64 + i.setWidth 64).toNat < ar_i.length)
    (hsi3_eq : (src + 3#64 + i.setWidth 64).toNat = src.toNat + 3 + i.toNat)
    (hpre_i : ∀ k < dst.toNat, ar_i[k]? = s_2.arena[k]?)
    (hsuf_i : ∀ k, src.toNat + 3 + i.toNat ≤ k → k < s0.arena_len → ar_i[k]? = s_2.arena[k]?)
    (hlits_i : ∀ k < nsz.toNat, (ar_i[dst.toNat + 3 + k]?.getD 0#32).toNat < 2 * c.mv)
    (hlit_lt : (ar_i[(src + 3#64 + i.setWidth 64).toNat]'hsi3_lt).toNat < 2 * c.mv)
    (hent_i : F0.EntailsClause (cnfClause ((((ar_i.drop (dst.toNat + 3)).take nsz.toNat).map
        BitVec.toNat) ++ ((ar_i[(src + 3#64 + i.setWidth 64).toNat]'hsi3_lt).toNat ::
      (((s0.arena.drop (src.toNat + 3 + (i.toNat + 1))).take
        (arenaClauseSize s0 src.toNat - (i.toNat + 1))).map BitVec.toNat)))))
    (hne : (s_2.vals[(ar_i[(src + 3#64 + i.setWidth 64).toNat]'hsi3_lt).toNat]'(by
      rw [hva_len]; exact hlit_lt)).signExtend 32 ≠ 0#32)
    (hns : ¬ (0#32 : BitVec 32).slt
      ((s_2.vals[(ar_i[(src + 3#64 + i.setWidth 64).toNat]'hsi3_lt).toNat]'(by
        rw [hva_len]; exact hlit_lt)).signExtend 32) = true) :
    SwFiltInv c F0 s0 s_2 src.toNat dst.toNat (arenaClauseSize s0 src.toNat)
      nsz.toNat (i.toNat + 1) ar_i := by
  have hvals_k : (ar_i[(src + 3#64 + i.setWidth 64).toNat]'hsi3_lt).toNat < s_2.vals.length := by
    rw [hva_len]; exact hlit_lt
  have hdom_k : s_2.vals[(ar_i[(src + 3#64 + i.setWidth 64).toNat]'hsi3_lt).toNat] = 0#8 ∨
      s_2.vals[(ar_i[(src + 3#64 + i.setWidth 64).toNat]'hsi3_lt).toNat] = 1#8 ∨
      s_2.vals[(ar_i[(src + 3#64 + i.setWidth 64).toNat]'hsi3_lt).toNat] = 0xFF#8 := by
    have h0 := htv_2.vals_domain _ hlit_lt
    rwa [List.getElem?_eq_getElem hvals_k, Option.getD_some] at h0
  have hfals_k : s_2.vals[(ar_i[(src + 3#64 + i.setWidth 64).toNat]'hsi3_lt).toNat]?.getD 0#8 =
      0xFF#8 := by
    rw [List.getElem?_eq_getElem hvals_k, Option.getD_some]
    exact vals_eq_neg_of_ne_pos hdom_k hne hns
  have hfals_ent := level0_entails_neg_of_fals htv_2 (hsame_2.cur_level.trans hcl0)
    hlit_lt hfals_k
  exact ⟨by omega, by omega, har_i, hpre_i, fun k hk1 hk2 => hsuf_i k (by omega) hk2, hlits_i,
    entails_drop_falsified_cons hent_i hfals_ent⟩

theorem sw2_copy_step {c : PlainCfg} {s0 s_2 : PlainState} {R : Mem 64 → Prop}
    {src dst : BitVec 64} {ic : BitVec 32} {ar_c : List (BitVec 32)} {mc' : Mem 64}
    (hic_lt : ic.toNat < arenaClauseSize s0 src.toNat) (hic1 : (ic + 1#32).toNat = ic.toNat + 1)
    (hdst_le : dst.toNat ≤ src.toNat)
    (har_c : ar_c.length = c.arena_cap)
    (hsi_lt : (src + 3#64 + ic.setWidth 64).toNat < ar_c.length)
    (hsi_eq : (src + 3#64 + ic.setWidth 64).toNat = src.toNat + 3 + ic.toNat)
    (hdi_eq : (dst + 3#64 + ic.setWidth 64).toNat = dst.toNat + 3 + ic.toNat)
    (hpre_c : ∀ k < dst.toNat, ar_c[k]? = s_2.arena[k]?)
    (hsuf_c : ∀ k, src.toNat + 3 + ic.toNat ≤ k → k < s0.arena_len → ar_c[k]? = s_2.arena[k]?)
    (hcp_c : ∀ k < ic.toNat, ar_c[dst.toNat + 3 + k]? = s0.arena[src.toNat + 3 + k]?)
    (har_sc : ar_c[src.toNat + 3 + ic.toNat]? = s0.arena[src.toNat + 3 + ic.toNat]?)
    (hmc : (PlainMem c
      { s_2 with
        arena := ar_c.set (dst + 3#64 + ic.setWidth 64).toNat
          (ar_c[(src + 3#64 + ic.setWidth 64).toNat]'hsi_lt) } ⋆ R) mc') :
    ∃ ar_c' : List (BitVec 32), (ic + 1#32).toNat ≤ arenaClauseSize s0 src.toNat ∧
      ar_c'.length = c.arena_cap ∧ (∀ k < dst.toNat, ar_c'[k]? = s_2.arena[k]?) ∧
      (∀ k, src.toNat + 3 + (ic + 1#32).toNat ≤ k → k < s0.arena_len →
        ar_c'[k]? = s_2.arena[k]?) ∧
      (∀ k < (ic + 1#32).toNat, ar_c'[dst.toNat + 3 + k]? = s0.arena[src.toNat + 3 + k]?) ∧
      (PlainMem c { s_2 with arena := ar_c' } ⋆ R) mc' := by
  refine ⟨ar_c.set (dst.toNat + 3 + ic.toNat)
      (ar_c[(src + 3#64 + ic.setWidth 64).toNat]'hsi_lt),
    by omega, by rw [List.length_set, har_c],
    fun k hk => by rw [List.getElem?_set_ne (by omega)]; exact hpre_c k hk,
    fun k hk1 hk2 => by
      rw [hic1] at hk1; rw [List.getElem?_set_ne (by omega)]; exact hsuf_c k (by omega) hk2,
    fun k hk => ?_, by simpa only [hdi_eq] using hmc⟩
  rw [hic1] at hk
  by_cases hkc : k = ic.toNat
  · subst hkc
    rw [List.getElem?_set_self (by rw [har_c]; omega), ← har_sc, ← hsi_eq,
      List.getElem?_eq_getElem hsi_lt]
  · rw [List.getElem?_set_ne (by omega)]; exact hcp_c k (by omega)

theorem sw2_copy_emit {c : PlainCfg} {F0 : CNF Nat} {s0 s_2 : PlainState}
    {src dst : BitVec 64} {ic new_sz : BitVec 32} {ar_c : List (BitVec 32)}
    (hinv0 : PlainCoreInv c F0 s0) (hsrc_ref : src.toNat ∈ arenaClauseRefs s0)
    (hng_s0 : arenaClauseGarb s0 src.toNat = false)
    (hwf0_sz : 3 ≤ arenaClauseSize s0 src.toNat)
    (hwf0_bd : src.toNat + 3 + arenaClauseSize s0 src.toNat ≤ s0.arena_len)
    (hdst_le : dst.toNat ≤ src.toNat) (hic_eq : ic.toNat = arenaClauseSize s0 src.toNat)
    (hsz_nat : new_sz.toNat = arenaClauseSize s0 src.toNat) (har_c : ar_c.length = c.arena_cap)
    (hpre_c : ∀ k < dst.toNat, ar_c[k]? = s_2.arena[k]?)
    (hsuf_c : ∀ k, src.toNat + 3 + ic.toNat ≤ k → k < s0.arena_len → ar_c[k]? = s_2.arena[k]?)
    (hcp_c : ∀ k < ic.toNat, ar_c[dst.toNat + 3 + k]? = s0.arena[src.toNat + 3 + k]?) :
    SwEmitOk c F0 s0 s_2 src.toNat dst.toNat new_sz.toNat ar_c := by
  have hlen_a := hinv0.lengths.arena_len_le
  have hlits_cp := sw_copy_lits (s0 := s0) (ar := ar_c) (src := src.toNat) (dst := dst.toNat)
    (old_sz := arenaClauseSize s0 src.toNat) rfl (by rw [har_c]; omega)
    (by rw [hinv0.lengths.arena_len_arr]; omega) (by rwa [hic_eq] at hcp_c)
  refine ⟨by omega, by omega, har_c, hpre_c, by rwa [hic_eq] at hsuf_c, fun k hk => ?_,
    by rw [hsz_nat, hlits_cp]; exact hinv0.arena.entails src.toNat hsrc_ref hng_s0,
    fun _ => by rw [hsz_nat, hlits_cp]⟩
  rw [hsz_nat] at hk; rw [hcp_c k (hic_eq ▸ hk)]
  refine hinv0.arena.lits_lt src.toNat hsrc_ref hng_s0 _ ?_
  rw [mem_arenaClauseLits_iff (by rw [hinv0.lengths.arena_len_arr]; omega)]
  exact ⟨k, hk, (by
    rw [List.getElem?_eq_getElem (by rw [hinv0.lengths.arena_len_arr]; omega), Option.getD_some])⟩

theorem sw2_sz2_done {c : PlainCfg} {F0 : CNF Nat} {s0 s_2 : PlainState}
    {src dst : BitVec 64} {new_unit : Bool} {ar_o : List (BitVec 32)}
    {l0 l1 b0 b1 : BitVec 32} {wv1 ws1 wso1 wv2 ws2 wso2 : List (BitVec 32)}
    {wl1 wl2 : Nat} {wu1 wu2 : BitVec 64}
    (hinv0 : PlainCoreInv c F0 s0) (hp_2 : ArenaPrefixOk c F0 s0 s_2 src.toNat dst.toNat)
    (hsrc_lt : src.toNat < s0.arena_len) (hcl0 : s0.cur_level = 0)
    (hsame_2 : SameSwPre s0 s_2) (hrt_2 : s_2.heur.rel_trigger = s0.heur.rel_trigger)
    (hal_2 : s_2.arena_len = s0.arena_len) (hag_2 : s_2.arena_garbage = s0.arena_garbage)
    (hoom_2 : s_2.oom = s0.oom) (htv_o : TrailValsInv c F0 { s_2 with arena := ar_o })
    (hb_o : BinWatchesOnly c F0 s_2 (2 * c.mv))
    (hte_le_2 : s0.trail_end ≤ s_2.trail_end)
    (hnew_2 : new_unit = true → s0.cur_level = 0 ∧ s0.trail_end < s_2.trail_end)
    (har_o : ar_o.length = c.arena_cap)
    (hpre_o : ∀ k < dst.toNat, ar_o[k]? = s_2.arena[k]?)
    (hsuf_o : ∀ k, src.toNat + 3 + arenaClauseSize s0 src.toNat ≤ k →
      k < s0.arena_len → ar_o[k]? = s_2.arena[k]?)
    (hb0 : BinWatchOk c F0 l0.toNat b0) (hb1 : BinWatchOk c F0 l1.toNat b1)
    (hlay_w1 : WatchStackLayout c (pushWatchState { s_2 with arena := ar_o } wv1 ws1 wso1 wl1 wu1))
    (hoth1 : ∀ l < 2 * c.mv, l ≠ l0.toNat →
      watchSize (pushWatchState { s_2 with arena := ar_o } wv1 ws1 wso1 wl1 wu1) l =
        watchSize { s_2 with arena := ar_o } l ∧
      ∀ k < watchSize { s_2 with arena := ar_o } l,
        ws1[watchOff (pushWatchState { s_2 with arena := ar_o } wv1 ws1 wso1 wl1 wu1) l + k]? =
          ({ s_2 with arena := ar_o } : PlainState).wstk[
            watchOff { s_2 with arena := ar_o } l + k]?)
    (hsz1 : watchSize (pushWatchState { s_2 with arena := ar_o } wv1 ws1 wso1 wl1 wu1) l0.toNat =
      watchSize { s_2 with arena := ar_o } l0.toNat + 1)
    (hpre1 : ∀ k < watchSize { s_2 with arena := ar_o } l0.toNat,
      ws1[watchOff (pushWatchState { s_2 with arena := ar_o } wv1 ws1 wso1 wl1 wu1) l0.toNat + k]? =
        ({ s_2 with arena := ar_o } : PlainState).wstk[
          watchOff { s_2 with arena := ar_o } l0.toNat + k]?)
    (hw1a : ws1[watchOff (pushWatchState { s_2 with arena := ar_o } wv1 ws1 wso1 wl1 wu1) l0.toNat +
      watchSize { s_2 with arena := ar_o } l0.toNat]? = some b0)
    (hlen_w2 : (pushWatchState (pushWatchState { s_2 with arena := ar_o } wv1 ws1 wso1 wl1 wu1)
      wv2 ws2 wso2 wl2 wu2).LengthsOk c)
    (hlay_w2 : WatchStackLayout c (pushWatchState
      (pushWatchState { s_2 with arena := ar_o } wv1 ws1 wso1 wl1 wu1) wv2 ws2 wso2 wl2 wu2))
    (hoth2 : ∀ l < 2 * c.mv, l ≠ l1.toNat →
      watchSize (pushWatchState (pushWatchState { s_2 with arena := ar_o } wv1 ws1 wso1 wl1 wu1)
        wv2 ws2 wso2 wl2 wu2) l =
        watchSize (pushWatchState { s_2 with arena := ar_o } wv1 ws1 wso1 wl1 wu1) l ∧
      ∀ k < watchSize (pushWatchState { s_2 with arena := ar_o } wv1 ws1 wso1 wl1 wu1) l,
        ws2[watchOff (pushWatchState (pushWatchState { s_2 with arena := ar_o }
            wv1 ws1 wso1 wl1 wu1) wv2 ws2 wso2 wl2 wu2) l + k]? =
          ws1[watchOff (pushWatchState { s_2 with arena := ar_o } wv1 ws1 wso1 wl1 wu1) l + k]?)
    (hsz2w : watchSize (pushWatchState
        (pushWatchState { s_2 with arena := ar_o } wv1 ws1 wso1 wl1 wu1) wv2 ws2 wso2 wl2 wu2)
        l1.toNat =
      watchSize (pushWatchState { s_2 with arena := ar_o } wv1 ws1 wso1 wl1 wu1) l1.toNat + 1)
    (hpre2 : ∀ k < watchSize (pushWatchState { s_2 with arena := ar_o }
        wv1 ws1 wso1 wl1 wu1) l1.toNat,
      ws2[watchOff (pushWatchState (pushWatchState { s_2 with arena := ar_o }
            wv1 ws1 wso1 wl1 wu1) wv2 ws2 wso2 wl2 wu2) l1.toNat + k]? =
        ws1[watchOff (pushWatchState { s_2 with arena := ar_o }
          wv1 ws1 wso1 wl1 wu1) l1.toNat + k]?)
    (hw2a : ws2[watchOff (pushWatchState (pushWatchState { s_2 with arena := ar_o }
        wv1 ws1 wso1 wl1 wu1) wv2 ws2 wso2 wl2 wu2) l1.toNat +
      watchSize (pushWatchState { s_2 with arena := ar_o } wv1 ws1 wso1 wl1 wu1) l1.toNat]? =
      some b1) :
    let sw1 := pushWatchState { s_2 with arena := ar_o } wv1 ws1 wso1 wl1 wu1
    let sw2 := pushWatchState sw1 wv2 ws2 wso2 wl2 wu2
    SwP2Inv c F0 s0 (arenaNextOff s0.arena s0.arena_len src.toNat) dst.toNat new_unit
      { sw2 with num_binary := sw2.num_binary + 1#64 } := by
  intro sw1 sw2
  have hb_ar := binWatchesOnly_with_arena hb_o ar_o s_2.arena_len
  have hb_w1 := binWatchesOnly_push hb_ar hlay_w1 (fun _ hr => hr) hb0 hoth1 hsz1 hpre1 hw1a
  have hb_w2 := binWatchesOnly_push hb_w1 hlay_w2 (fun _ hr => hr) hb1 hoth2 hsz2w hpre2 hw2a
  have hp_w2 := arenaPrefix_congr_arena
    (arenaPrefix_skip_mut hinv0 hp_2 hsrc_lt har_o hpre_o hsuf_o) rfl
  have hrr_w2 := rsnReloc_l0 (s := { sw2 with num_binary := sw2.num_binary + 1#64 })
    (src := arenaNextOff s0.arena s0.arena_len src.toNat) (dst := dst.toNat) hcl0
    (hlen_w2.rsns_len.trans hinv0.lengths.rsns_len.symm)
  exact ⟨{ hlen_w2 with }, hsame_2, hrt_2, hal_2, hag_2, hoom_2,
    trailValsInv_congr htv_o rfl rfl rfl rfl rfl rfl rfl,
    binWatchesOnly_repack hb_w2 rfl rfl rfl, arenaPrefix_congr_arena hp_w2 rfl, hrr_w2,
    hsame_2.cur_level, hte_le_2, hnew_2, fun h => absurd h (by omega)⟩

theorem sw3_push_done {c : PlainCfg} {F0 : CNF Nat} {s0 s_r : PlainState} {R : Mem 64 → Prop}
    {dst p : BitVec 64} {l0 l1 : BitVec 32} {new_unit : Bool}
    {wv1 ws1 wso1 wv2 ws2 wso2 : List (BitVec 32)} {wl1 wl2 : Nat} {wu1 wu2 : BitVec 64}
    {m_w2 : Mem 64}
    (hsw_r : SwP3Inv c F0 s0 dst.toNat new_unit s_r) (href_r : p.toNat ∈ arenaClauseRefs s_r)
    (hp3_eq : (p + 3#64).toNat = p.toNat + 3) (hp4_eq : (p + 4#64).toNat = p.toNat + 4)
    (hp2_eq : (p + 2#64).toNat = p.toNat + 2)
    (hpt_eq : p.truncate 32 = BitVec.ofNat 32 p.toNat)
    (hm_w2 : (PlainMem c (pushWatchState
      (pushWatchState { s_r with arena := s_r.arena.set (p.toNat + 1) 2#32 }
        wv1 ws1 wso1 wl1 wu1)
      wv2 ws2 wso2 wl2 wu2) ⋆ R) m_w2)
    (hl0 : (s_r.arena.set (p.toNat + 1) 2#32)[p.toNat + 3]? = some l0)
    (hl1 : (s_r.arena.set (p.toNat + 1) 2#32)[p.toNat + 4]? = some l1)
    (hlen_w1 : (pushWatchState { s_r with arena := s_r.arena.set (p.toNat + 1) 2#32 }
      wv1 ws1 wso1 wl1 wu1).LengthsOk c)
    (hlay_w1 : WatchStackLayout c (pushWatchState
      { s_r with arena := s_r.arena.set (p.toNat + 1) 2#32 } wv1 ws1 wso1 wl1 wu1))
    (hoth1 : ∀ l < 2 * c.mv, l ≠ l0.toNat →
      watchSize (pushWatchState { s_r with arena := s_r.arena.set (p.toNat + 1) 2#32 }
        wv1 ws1 wso1 wl1 wu1) l =
        watchSize { s_r with arena := s_r.arena.set (p.toNat + 1) 2#32 } l ∧
      ∀ k < watchSize { s_r with arena := s_r.arena.set (p.toNat + 1) 2#32 } l,
        ws1[watchOff (pushWatchState { s_r with arena := s_r.arena.set (p.toNat + 1) 2#32 }
          wv1 ws1 wso1 wl1 wu1) l + k]? =
          s_r.wstk[watchOff { s_r with arena := s_r.arena.set (p.toNat + 1) 2#32 } l + k]?)
    (hsz1 : watchSize (pushWatchState { s_r with arena := s_r.arena.set (p.toNat + 1) 2#32 }
        wv1 ws1 wso1 wl1 wu1) l0.toNat =
      watchSize { s_r with arena := s_r.arena.set (p.toNat + 1) 2#32 } l0.toNat + 2)
    (hpre1 : ∀ k < watchSize { s_r with arena := s_r.arena.set (p.toNat + 1) 2#32 } l0.toNat,
      ws1[watchOff (pushWatchState { s_r with arena := s_r.arena.set (p.toNat + 1) 2#32 }
          wv1 ws1 wso1 wl1 wu1) l0.toNat + k]? =
        s_r.wstk[watchOff { s_r with arena := s_r.arena.set (p.toNat + 1) 2#32 } l0.toNat + k]?)
    (hw1a : ws1[watchOff (pushWatchState { s_r with arena := s_r.arena.set (p.toNat + 1) 2#32 }
          wv1 ws1 wso1 wl1 wu1) l0.toNat +
        watchSize { s_r with arena := s_r.arena.set (p.toNat + 1) 2#32 } l0.toNat]? = some l1)
    (hw1b : ws1[watchOff (pushWatchState { s_r with arena := s_r.arena.set (p.toNat + 1) 2#32 }
          wv1 ws1 wso1 wl1 wu1) l0.toNat +
        watchSize { s_r with arena := s_r.arena.set (p.toNat + 1) 2#32 } l0.toNat + 1]? =
      some (p.truncate 32))
    (hlen_w2 : (pushWatchState (pushWatchState
      { s_r with arena := s_r.arena.set (p.toNat + 1) 2#32 } wv1 ws1 wso1 wl1 wu1)
      wv2 ws2 wso2 wl2 wu2).LengthsOk c)
    (hlay_w2 : WatchStackLayout c (pushWatchState (pushWatchState
      { s_r with arena := s_r.arena.set (p.toNat + 1) 2#32 } wv1 ws1 wso1 wl1 wu1)
      wv2 ws2 wso2 wl2 wu2))
    (hoth2 : ∀ l < 2 * c.mv, l ≠ l1.toNat →
      watchSize (pushWatchState (pushWatchState
        { s_r with arena := s_r.arena.set (p.toNat + 1) 2#32 } wv1 ws1 wso1 wl1 wu1)
        wv2 ws2 wso2 wl2 wu2) l =
        watchSize (pushWatchState { s_r with arena := s_r.arena.set (p.toNat + 1) 2#32 }
          wv1 ws1 wso1 wl1 wu1) l ∧
      ∀ k < watchSize (pushWatchState { s_r with arena := s_r.arena.set (p.toNat + 1) 2#32 }
          wv1 ws1 wso1 wl1 wu1) l,
        ws2[watchOff (pushWatchState (pushWatchState
          { s_r with arena := s_r.arena.set (p.toNat + 1) 2#32 } wv1 ws1 wso1 wl1 wu1)
          wv2 ws2 wso2 wl2 wu2) l + k]? =
          ws1[watchOff (pushWatchState { s_r with arena := s_r.arena.set (p.toNat + 1) 2#32 }
            wv1 ws1 wso1 wl1 wu1) l + k]?)
    (hsz2 : watchSize (pushWatchState (pushWatchState
        { s_r with arena := s_r.arena.set (p.toNat + 1) 2#32 } wv1 ws1 wso1 wl1 wu1)
        wv2 ws2 wso2 wl2 wu2) l1.toNat =
      watchSize (pushWatchState { s_r with arena := s_r.arena.set (p.toNat + 1) 2#32 }
          wv1 ws1 wso1 wl1 wu1) l1.toNat + 2)
    (hpre2 : ∀ k < watchSize (pushWatchState
        { s_r with arena := s_r.arena.set (p.toNat + 1) 2#32 } wv1 ws1 wso1 wl1 wu1) l1.toNat,
      ws2[watchOff (pushWatchState (pushWatchState
          { s_r with arena := s_r.arena.set (p.toNat + 1) 2#32 } wv1 ws1 wso1 wl1 wu1)
          wv2 ws2 wso2 wl2 wu2) l1.toNat + k]? =
        ws1[watchOff (pushWatchState { s_r with arena := s_r.arena.set (p.toNat + 1) 2#32 }
          wv1 ws1 wso1 wl1 wu1) l1.toNat + k]?)
    (hw2a : ws2[watchOff (pushWatchState (pushWatchState
        { s_r with arena := s_r.arena.set (p.toNat + 1) 2#32 } wv1 ws1 wso1 wl1 wu1)
        wv2 ws2 wso2 wl2 wu2) l1.toNat +
      watchSize (pushWatchState { s_r with arena := s_r.arena.set (p.toNat + 1) 2#32 }
          wv1 ws1 wso1 wl1 wu1) l1.toNat]? = some l0)
    (hw2b : ws2[watchOff (pushWatchState (pushWatchState
        { s_r with arena := s_r.arena.set (p.toNat + 1) 2#32 } wv1 ws1 wso1 wl1 wu1)
        wv2 ws2 wso2 wl2 wu2) l1.toNat +
      watchSize (pushWatchState { s_r with arena := s_r.arena.set (p.toNat + 1) 2#32 }
          wv1 ws1 wso1 wl1 wu1) l1.toNat + 1]? = some (p.truncate 32))
    (hp2_lt : (p + 2#64).toNat < s_r.arena.length) :
    ∃ s_w2 : PlainState,
      p.toNat < (p + 3#64 + (s_r.arena[(p + 2#64).toNat]'hp2_lt).setWidth 64).toNat ∧
      (p + 3#64 + (s_r.arena[(p + 2#64).toNat]'hp2_lt).setWidth 64).toNat ≤ dst.toNat ∧
      ((p + 3#64 + (s_r.arena[(p + 2#64).toNat]'hp2_lt).setWidth 64).toNat = dst.toNat ∨
        (p + 3#64 + (s_r.arena[(p + 2#64).toNat]'hp2_lt).setWidth 64).toNat ∈
          arenaClauseRefs s_w2) ∧
      SwP3Inv c F0 s0 dst.toNat new_unit s_w2 ∧ (PlainMem c s_w2 ⋆ R) m_w2 := by
  have har := c.harena; unfold dimacsBound at har
  have hlen_r := hsw_r.1.lengths; have hwf_r := hsw_r.1.arena.refs_wf p.toNat href_r
  have hng_rr := hsw_r.2.2.2.2.2.2.2.2 p.toNat href_r
  have ⟨hcore_s2, hrefs_s2, hng_s2⟩ := setSrch2_core hsw_r.1 href_r
  let s_r2 : PlainState := { s_r with arena := s_r.arena.set (p.toNat + 1) 2#32 }
  have href_r2 : p.toNat ∈ arenaClauseRefs s_r2 := hrefs_s2.symm ▸ href_r
  have hng_r2 : arenaClauseGarb s_r2 p.toNat = false := (hng_s2 p.toNat href_r).trans hng_rr
  have hpp := phase3_push_prep hcore_s2 href_r2 hng_r2
  have hwf_r2 := hcore_s2.arena.refs_wf p.toNat href_r2
  have hp3_bd : p.toNat + 3 < s_r2.arena.length := by
    dsimp [s_r2]; rw [List.length_set, hlen_r.arena_len_arr]
    have := hwf_r2.2.1; have := hwf_r2.2.2.1; have := hwf_r2.2.2.2.1
    have := hlen_r.arena_len_le; omega
  have hp4_bd : p.toNat + 4 < s_r2.arena.length := by
    dsimp [s_r2]; rw [List.length_set, hlen_r.arena_len_arr]
    have := hwf_r2.2.1; have := hwf_r2.2.2.1; have := hwf_r2.2.2.2.1
    have := hlen_r.arena_len_le; omega
  have he3 : l0 = s_r2.arena[p.toNat + 3]'hp3_bd := by
    have := hl0; dsimp [s_r2]; rw [List.getElem?_eq_getElem hp3_bd] at this
    exact (Option.some.inj this).symm
  have he4 : l1 = s_r2.arena[p.toNat + 4]'hp4_bd := by
    have := hl1; dsimp [s_r2]; rw [List.getElem?_eq_getElem hp4_bd] at this
    exact (Option.some.inj this).symm
  rw [he3] at hoth1 hsz1 hpre1 hw1a hw1b hw2a
  rw [he4] at hw1a hoth2 hsz2 hpre2 hw2a hw2b
  have hcw1 := pushClWatches_step_core (cref := p.truncate 32) hcore_s2 hlay_w1 hlen_w1
    hpp.2.2.2.2.2.2.1
    (by rw [hpt_eq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := hlen_r.arena_len_le; omega)]; exact hpp.2.2.2.2.2.2.2.2)
    (by rw [hpt_eq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := hlen_r.arena_len_le; omega)]; exact href_r2)
    hoth1 hpp.1 hsz1 hpre1 hw1a hw1b
  let s_w1 := pushWatchState s_r2 wv1 ws1 wso1 wl1 wu1
  have hcw2 := pushClWatches_step_core (cref := p.truncate 32) hcw1 hlay_w2 hlen_w2
    hpp.2.2.2.2.2.2.2.1
    (by rw [hpt_eq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := hlen_r.arena_len_le; omega)]; exact hpp.2.2.2.2.2.2.2.2)
    (by rw [hpt_eq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := hlen_r.arena_len_le; omega)]; exact href_r2)
    hoth2 hpp.2.1 hsz2 hpre2 hw2a hw2b
  let s_w2 := pushWatchState s_w1 wv2 ws2 wso2 wl2 wu2
  have hsw2 : SwP3Inv c F0 s0 dst.toNat new_unit s_w2 :=
    ⟨hcw2, hsw_r.2.1, hsw_r.2.2.1, hsw_r.2.2.2.1, hsw_r.2.2.2.2.1, hsw_r.2.2.2.2.2.1,
      hsw_r.2.2.2.2.2.2.1, hsw_r.2.2.2.2.2.2.2.1,
      fun r hr => (hng_s2 r (hrefs_s2 ▸ hr)).trans (hsw_r.2.2.2.2.2.2.2.2 r (hrefs_s2 ▸ hr))⟩
  have hpnxt : (p + 3#64 + (s_r.arena[(p + 2#64).toNat]'hp2_lt).setWidth 64).toNat =
      p.toNat + 3 + arenaClauseSize s_r p.toNat := by
    have hsz_z : ((s_r.arena[(p + 2#64).toNat]'hp2_lt).setWidth 64).toNat =
        arenaClauseSize s_r p.toNat := by
      rw [bv_c0_zext32_64]; unfold arenaClauseSize
      rw [← hp2_eq, List.getElem?_eq_getElem hp2_lt, Option.getD_some]
    have h3 : (p + 3#64).toNat = p.toNat + 3 :=
      bv64_add_toNat (by have := hwf_r.2.2.1; have := hwf_r.2.2.2.1; have := hlen_r.arena_len_le
                         omega)
    rw [BitVec.toNat_add, h3, hsz_z, Nat.mod_eq_of_lt (by
      have := hwf_r.2.2.1; have := hwf_r.2.2.2.1; have := hlen_r.arena_len_le; omega)]
  have hnxt_eq : arenaNextOff s_r.arena s_r.arena_len p.toNat =
      p.toNat + 3 + arenaClauseSize s_r p.toNat := hsw_r.1.arena.arenaNextOff_eq href_r
  have hstep_r := arenaScan_step (fun r hr => (hsw_r.1.arena.refs_wf r hr).2.2.2.2) href_r
  rw [hnxt_eq, hsw_r.2.2.2.2.1] at hstep_r
  refine ⟨s_w2, by rw [hpnxt]; have := hwf_r.2.1; omega,
    by rw [hpnxt]; have := hwf_r.2.2.2.1; rw [hnxt_eq, hsw_r.2.2.2.2.1] at this; exact this,
    ?_, hsw2, hm_w2⟩
  rw [hpnxt]
  exact hstep_r.imp id fun h => by
    dsimp only [s_w2, s_w1, pushWatchState]
    change _ ∈ arenaClauseRefs s_r2
    rw [hrefs_s2]; unfold arenaClauseRefs; rw [hsw_r.2.2.2.2.1]; exact h

theorem sw3_swap_step {c : PlainCfg} {F0 : CNF Nat} {s0 s : PlainState} {R : Mem 64 → Prop}
    {dst new_unit : _} {p : BitVec 64} {k1 : Nat} {k2 : BitVec 32} {ms : Mem 64}
    (hsw : SwP3Inv c F0 s0 dst new_unit s) (href : p.toNat ∈ arenaClauseRefs s)
    (hk1 : k1 < arenaClauseSize s p.toNat) (hk2 : k2.toNat < arenaClauseSize s p.toNat)
    (h3k1_lt : (p + BitVec.ofNat 64 (3 + k1)).toNat < s.arena.length)
    (hk2_lt : (p + 3#64 + k2.setWidth 64).toNat < s.arena.length)
    (hp1_eq : (p + BitVec.ofNat 64 (3 + k1)).toNat = p.toNat + 3 + k1)
    (hp2_eq : (p + 3#64 + k2.setWidth 64).toNat = p.toNat + 3 + k2.toNat)
    (hm : (PlainMem c
      { s with
        arena :=
          (s.arena.set (p + BitVec.ofNat 64 (3 + k1)).toNat
            (s.arena[(p + 3#64 + k2.setWidth 64).toNat]'hk2_lt)).set
            (p + 3#64 + k2.setWidth 64).toNat
            (s.arena[(p + BitVec.ofNat 64 (3 + k1)).toNat]'h3k1_lt) } ⋆ R) ms) :
    ∃ s' : PlainState, p.toNat ∈ arenaClauseRefs s' ∧ SwP3Inv c F0 s0 dst new_unit s' ∧
      arenaClauseSize s' p.toNat = arenaClauseSize s p.toNat ∧ (PlainMem c s' ⋆ R) ms := by
  have hs := sw_swap_swp3 hsw href hk1 hk2
  exact ⟨_, hs.1, hs.2.1, hs.2.2, by simpa only [hp1_eq, hp2_eq] using hm⟩

theorem sw1_defrag_to_p2 {c : PlainCfg} {F0 : CNF Nat} {s0 s1 : PlainState} {R : Mem 64 → Prop}
    {wvec' wstk' wsort' : List (BitVec 32)} {wlen' : Nat} {m2 : Mem 64}
    (hs1 : SwP1Inv c F0 s0 (2 * c.mv) s1) (hag1 : s1.arena_garbage = s0.arena_garbage)
    (hlen2 : ({ s1 with
      wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64,
      heur := { s1.heur with wsort := wsort' } } : PlainState).LengthsOk c)
    (hlay2 : WatchStackLayout c { s1 with
      wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64,
      heur := { s1.heur with wsort := wsort' } })
    (hpres2 : ∀ l < 2 * c.mv,
      watchSize { s1 with
        wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64,
        heur := { s1.heur with wsort := wsort' } } l = watchSize s1 l ∧
      ∀ k < watchSize s1 l,
        wstk'[watchOff { s1 with
          wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64,
          heur := { s1.heur with wsort := wsort' } } l + k]? = s1.wstk[watchOff s1 l + k]?)
    (hm2 : (PlainMem c { s1 with
      wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64,
      heur := { s1.heur with wsort := wsort' } } ⋆ R) m2) :
    ∃ s_p1 : PlainState,
      s_p1.LengthsOk c ∧ SameSwPre s0 s_p1 ∧ s_p1.heur.rel_trigger = s0.heur.rel_trigger ∧
      s_p1.vals = s0.vals ∧ s_p1.lvl = s0.lvl ∧ s_p1.rsns = s0.rsns ∧
      s_p1.trl = s0.trl ∧ s_p1.trail_pos = s0.trail_pos ∧ s_p1.trail_end = s0.trail_end ∧
      s_p1.unflushed = s0.unflushed ∧ s_p1.arena = s0.arena ∧
      s_p1.arena_len = s0.arena_len ∧ s_p1.arena_garbage = s0.arena_garbage ∧
      s_p1.oom = s0.oom ∧ BinWatchesOnly c F0 s_p1 (2 * c.mv) ∧
      (PlainMem c s_p1 ⋆ R) m2 := by
  obtain ⟨_, _, hsame1, hv1, hlvl1, hrsn1, htrl1, htp1, hte1, hunf1, har1, hal1, _, hoom1,
    hrt1, hb1⟩ := hs1
  exact ⟨_, hlen2, hsame1, hrt1, hv1, hlvl1, hrsn1, htrl1, htp1, hte1, hunf1, har1, hal1,
    hag1, hoom1, binWatchesOnly_defrag hb1 hlay2 rfl rfl hpres2, hm2⟩

theorem sw2_exit_to_p3 {c : PlainCfg} {F0 : CNF Nat} {s0 s_e : PlainState} {dst : BitVec 64}
    {fred irred redd : BitVec 64} {unsat new_unit : Bool}
    (hinv0 : PlainCoreInv c F0 s0) (he : SwP2ExitInv c F0 s0 dst.toNat unsat new_unit s_e) :
    let s_fin : PlainState :=
      { s_e with
        arena_len := dst.toNat, arena_garbage := 0#64, first_reducible := fred,
        num_irred := irred, num_redundant := redd }
    s_fin.LengthsOk c ∧ SameSwPre s0 s_fin ∧
    (unsat = false → s_fin.oom = 0#64 → SwP3Inv c F0 s0 dst.toNat new_unit s_fin) := by
  obtain ⟨hlen_e, hsame_e, hrt_e, hdst_le, _, _, hok_e⟩ := he
  intro s_fin
  have hlen_f : s_fin.LengthsOk c :=
    { hlen_e with arena_len_le := Nat.le_trans hdst_le hinv0.lengths.arena_len_le }
  refine ⟨hlen_f, hsame_e, fun huf hoom => ?_⟩
  obtain ⟨htv', hb', hp', hrr', hscl', hnew', hkeep'⟩ := hok_e huf hoom
  have htv_f : TrailValsInv c F0 s_fin := trailValsInv_congr htv' rfl rfl rfl rfl rfl rfl rfl
  have hcore' := phase2_to_core hinv0 hlen_f htv_f (binWatchesOnly_repack hb' rfl rfl rfl)
    (arenaPrefix_congr_arena hp' rfl) (rsnReloc_congr_state hrr' rfl rfl) rfl hscl'
    (fun hpos => ⟨(hkeep' hpos).2.2.1, (hkeep' hpos).2.2.2.2⟩)
  have hng' : ∀ r ∈ arenaClauseRefs s_fin, arenaClauseGarb s_fin r = false := fun r hr => by
    simpa only [arenaClauseRefs, arenaClauseGarb, arenaHdr, arenaClauseSize, arenaNextOff,
      s_fin] using hp'.no_garb r hr
  exact ⟨hcore', hsame_e, rfl, hrt_e, rfl, hoom, hnew', hkeep', hng'⟩

theorem sw2_sat_skip {c : PlainCfg} {F0 : CNF Nat} {s0 s_2 : PlainState}
    {src dst : BitVec 64} {new_unit : Bool} {ar_o : List (BitVec 32)}
    (hinv0 : PlainCoreInv c F0 s0) (hlen_2 : s_2.LengthsOk c) (hsame_2 : SameSwPre s0 s_2)
    (hrt_2 : s_2.heur.rel_trigger = s0.heur.rel_trigger)
    (hal_2 : s_2.arena_len = s0.arena_len) (hag_2 : s_2.arena_garbage = s0.arena_garbage)
    (hoom_2 : s_2.oom = s0.oom) (htv_2 : TrailValsInv c F0 s_2)
    (hb_2 : BinWatchesOnly c F0 s_2 (2 * c.mv))
    (hp_2 : ArenaPrefixOk c F0 s0 s_2 src.toNat dst.toNat)
    (hrr_2 : RsnRelocInv s0 s_2 src.toNat dst.toNat) (hscl_2 : s_2.cur_level = s0.cur_level)
    (hte_le_2 : s0.trail_end ≤ s_2.trail_end)
    (hnew_2 : new_unit = true → s0.cur_level = 0 ∧ s0.trail_end < s_2.trail_end)
    (hcl0 : s0.cur_level = 0) (hsrc_lt : src.toNat < s0.arena_len)
    (har_y : ar_o.length = c.arena_cap)
    (hpre_y : ∀ k < dst.toNat, ar_o[k]? = s_2.arena[k]?)
    (hsuf_y : ∀ k, src.toNat + 3 + arenaClauseSize s0 src.toNat ≤ k → k < s0.arena_len →
      ar_o[k]? = s_2.arena[k]?) :
    SwP2Inv c F0 s0 (arenaNextOff s0.arena s0.arena_len src.toNat) dst.toNat new_unit
      { s_2 with arena := ar_o } :=
  ⟨lengthsOk_with_arena hlen_2 har_y, hsame_2, hrt_2, hal_2, hag_2, hoom_2,
    trailValsInv_congr htv_2 rfl rfl rfl rfl rfl rfl rfl,
    binWatchesOnly_repack hb_2 rfl rfl rfl,
    arenaPrefix_skip_mut hinv0 hp_2 hsrc_lt har_y hpre_y hsuf_y,
    rsnReloc_l0 (s := { s_2 with arena := ar_o }) hcl0 hrr_2.1,
    hscl_2, hte_le_2, hnew_2, fun h => absurd h (by omega)⟩

theorem sw2_unit_keep {c : PlainCfg} {F0 : CNF Nat} {s0 s_2 s_nu : PlainState}
    {src dst : BitVec 64} {nu' : Bool} {ar_o : List (BitVec 32)}
    (hinv0 : PlainCoreInv c F0 s0) (hp_2 : ArenaPrefixOk c F0 s0 s_2 src.toNat dst.toNat)
    (hsrc_lt : src.toNat < s0.arena_len) (hcl0 : s0.cur_level = 0)
    (hal_2 : s_2.arena_len = s0.arena_len) (hag_2 : s_2.arena_garbage = s0.arena_garbage)
    (hoom_2 : s_2.oom = s0.oom)
    (har_o : ar_o.length = c.arena_cap) (hpre_o : ∀ k < dst.toNat, ar_o[k]? = s_2.arena[k]?)
    (hsuf_o : ∀ k, src.toNat + 3 + arenaClauseSize s0 src.toNat ≤ k → k < s0.arena_len →
      ar_o[k]? = s_2.arena[k]?)
    (hlen_nu : s_nu.LengthsOk c) (hsame_nu : SameSwPre s0 s_nu)
    (hrt_nu : s_nu.heur.rel_trigger = s0.heur.rel_trigger) (har_nu : s_nu.arena = ar_o)
    (hal_nu : s_nu.arena_len = s_2.arena_len) (hag_nu : s_nu.arena_garbage = s_2.arena_garbage)
    (hoom_nu : s_nu.oom = s_2.oom) (htv_nu : TrailValsInv c F0 s_nu)
    (hb_nu : BinWatchesOnly c F0 s_nu (2 * c.mv)) (hte_nu : s0.trail_end ≤ s_nu.trail_end)
    (hnew_nu : nu' = true → s0.trail_end < s_nu.trail_end) :
    SwP2Inv c F0 s0 (arenaNextOff s0.arena s0.arena_len src.toNat) dst.toNat nu' s_nu :=
  ⟨hlen_nu, hsame_nu, hrt_nu, hal_nu.trans hal_2, hag_nu.trans hag_2, hoom_nu.trans hoom_2,
    htv_nu, hb_nu,
    arenaPrefix_congr_arena (arenaPrefix_skip_mut hinv0 hp_2 hsrc_lt har_o hpre_o hsuf_o)
      har_nu,
    rsnReloc_l0 (s := s_nu) hcl0 (hlen_nu.rsns_len.trans hinv0.lengths.rsns_len.symm),
    hsame_nu.cur_level, hte_nu, fun h => ⟨hcl0, hnew_nu h⟩, fun h => absurd h (by omega)⟩

theorem sw2_sz1_ctx {c : PlainCfg} {F0 : CNF Nat} {s_2 : PlainState}
    {dst : BitVec 64} {new_sz : BitVec 32} {ar_o : List (BitVec 32)}
    (hsz1 : new_sz.toNat = 1) (hu_eq : (dst + 3#64).toNat = dst.toNat + 3)
    (hud_lt : (dst + 3#64).toNat < ar_o.length)
    (hlits_o : ∀ k < new_sz.toNat, (ar_o[dst.toNat + 3 + k]?.getD 0#32).toNat < 2 * c.mv)
    (hent_fin : F0.EntailsClause
      (cnfClause (((ar_o.drop (dst.toNat + 3)).take new_sz.toNat).map BitVec.toNat)))
    (hlen_o : ({ s_2 with arena := ar_o } : PlainState).LengthsOk c)
    (htv_o : TrailValsInv c F0 { s_2 with arena := ar_o }) :
    (ar_o[(dst + 3#64).toNat]'hud_lt).toNat < 2 * c.mv ∧
    F0.EntailsClause (cnfClause [(ar_o[(dst + 3#64).toNat]'hud_lt).toNat]) ∧
    ∃ hvals_u : (ar_o[(dst + 3#64).toNat]'hud_lt).toNat < s_2.vals.length,
      s_2.vals[(ar_o[(dst + 3#64).toNat]'hud_lt).toNat]'hvals_u = 0#8 ∨
      s_2.vals[(ar_o[(dst + 3#64).toNat]'hud_lt).toNat]'hvals_u = 1#8 ∨
      s_2.vals[(ar_o[(dst + 3#64).toNat]'hud_lt).toNat]'hvals_u = 0xFF#8 := by
  obtain ⟨hulit, hl0⟩ := sw2_sz1_prep hsz1 hu_eq hud_lt hlits_o hent_fin
  have hvals_u : (ar_o[(dst + 3#64).toNat]'hud_lt).toNat < s_2.vals.length := by
    have := hlen_o.vals_len; dsimp only at this; omega
  have h0 := htv_o.vals_domain _ hulit
  dsimp only at h0
  rw [List.getElem?_eq_getElem hvals_u, Option.getD_some] at h0
  exact ⟨hulit, hl0, hvals_u, h0⟩

theorem sw2_filt_prep {c : PlainCfg} {F0 : CNF Nat} {s0 s_2 : PlainState}
    {src dst : BitVec 64} {nsz i : BitVec 32} {ar_i : List (BitVec 32)}
    (hinv0 : PlainCoreInv c F0 s0) (hp_2 : ArenaPrefixOk c F0 s0 s_2 src.toNat dst.toNat)
    (hsrc_ref : src.toNat ∈ arenaClauseRefs s0)
    (hng_s0 : arenaClauseGarb s0 src.toNat = false)
    (hsuf_bd : src.toNat + 3 + arenaClauseSize s0 src.toNat ≤ s0.arena_len)
    (har_i : ar_i.length = c.arena_cap)
    (hsuf_i : ∀ k, src.toNat + 3 + i.toNat ≤ k → k < s0.arena_len → ar_i[k]? = s_2.arena[k]?)
    (hi_lt : i.toNat < arenaClauseSize s0 src.toNat)
    (hent_i : F0.EntailsClause (cnfClause ((((ar_i.drop (dst.toNat + 3)).take nsz.toNat).map
        BitVec.toNat) ++
      (((s0.arena.drop (src.toNat + 3 + i.toNat)).take
        (arenaClauseSize s0 src.toNat - i.toNat)).map BitVec.toNat)))) :
    (i + 1#32).toNat = i.toNat + 1 ∧
    ∃ (hsi3_eq : (src + 3#64 + i.setWidth 64).toNat = src.toNat + 3 + i.toNat)
      (hsi3_lt : (src + 3#64 + i.setWidth 64).toNat < ar_i.length)
      (_hlit_ar : ar_i[(src + 3#64 + i.setWidth 64).toNat]'hsi3_lt =
        ar_i[src.toNat + 3 + i.toNat]'(by rw [← hsi3_eq]; exact hsi3_lt)),
      (ar_i[(src + 3#64 + i.setWidth 64).toNat]'hsi3_lt).toNat < 2 * c.mv ∧
      F0.EntailsClause (cnfClause ((((ar_i.drop (dst.toNat + 3)).take nsz.toNat).map
          BitVec.toNat) ++
        ((ar_i[src.toNat + 3 + i.toNat]'(by rw [← hsi3_eq]; exact hsi3_lt)).toNat ::
        (((s0.arena.drop (src.toNat + 3 + (i.toNat + 1))).take
          (arenaClauseSize s0 src.toNat - (i.toNat + 1))).map BitVec.toNat)))) := by
  have har := c.harena; unfold dimacsBound at har
  have hlen_a := hinv0.lengths.arena_len_le
  have har0 := hinv0.lengths.arena_len_arr
  have hi1_eq : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
  have hsi3_eq : (src + 3#64 + i.setWidth 64).toNat = src.toNat + 3 + i.toNat := by bv_omega
  have hsi3_lt : (src + 3#64 + i.setWidth 64).toNat < ar_i.length := by
    rw [har_i, hsi3_eq]; omega
  have hlit_s0 : ar_i[(src + 3#64 + i.setWidth 64).toNat]'hsi3_lt =
      s0.arena[src.toNat + 3 + i.toNat]'(by omega) := by
    have h1 := hsuf_i (src.toNat + 3 + i.toNat) (Nat.le_refl _) (by omega)
    have h2 := hp_2.suffix_eq (src.toNat + 3 + i.toNat) (by omega) (by omega)
    have h3 := h1.trans h2
    rw [List.getElem?_eq_getElem (by rw [← hsi3_eq]; exact hsi3_lt),
      List.getElem?_eq_getElem (by omega)] at h3
    exact Option.some.inj (by simpa only [← hsi3_eq] using h3)
  have hlit_lt : (ar_i[(src + 3#64 + i.setWidth 64).toNat]'hsi3_lt).toNat < 2 * c.mv := by
    refine hinv0.arena.lits_lt src.toNat hsrc_ref hng_s0 _ ?_
    rw [mem_arenaClauseLits_iff (by omega)]
    exact ⟨i.toNat, hi_lt, congrArg BitVec.toNat hlit_s0.symm⟩
  have hcons := sw_filt_cons (ar := s0.arena) (src := src.toNat) hi_lt (by omega)
  have hlit_ar : ar_i[(src + 3#64 + i.setWidth 64).toNat]'hsi3_lt =
      ar_i[src.toNat + 3 + i.toNat]'(by rw [← hsi3_eq]; exact hsi3_lt) :=
    Option.some.inj (by
      rw [← List.getElem?_eq_getElem hsi3_lt,
        ← List.getElem?_eq_getElem (by rw [← hsi3_eq]; exact hsi3_lt)]
      simp only [hsi3_eq])
  rw [← hlit_s0] at hcons
  exact ⟨hi1_eq, hsi3_eq, hsi3_lt, hlit_ar, hlit_lt, by simpa only [hcons, hlit_ar] using hent_i⟩

theorem sw2_hdr_prep {c : PlainCfg} {F0 : CNF Nat} {s0 s_2 : PlainState} {src : BitVec 64}
    (hinv0 : PlainCoreInv c F0 s0) (hlen_2 : s_2.LengthsOk c)
    (hsuf_c : src.toNat ∈ arenaClauseRefs s0 ∧
      src.toNat + 3 + arenaClauseSize s0 src.toNat ≤ s0.arena_len ∧
      s_2.arena[src.toNat]? = s0.arena[src.toNat]? ∧
      s_2.arena[src.toNat + 2]? = s0.arena[src.toNat + 2]? ∧
      arenaNextOff s_2.arena s0.arena_len src.toNat =
        arenaNextOff s0.arena s0.arena_len src.toNat) :
    ∃ (hsrc2_len : (src + 2#64).toNat < s_2.arena.length),
      src.toNat < s_2.arena.length ∧
      (src + 2#64).toNat = src.toNat + 2 ∧
      (src.truncate 32).toNat = src.toNat ∧
      (BitVec.ofNat 32 (arenaNextOff s0.arena s0.arena_len src.toNat)
        |>.setWidth 64).toNat = arenaNextOff s0.arena s0.arena_len src.toNat ∧
      s_2.arena.length = c.arena_cap ∧
      src.toNat < arenaNextOff s0.arena s0.arena_len src.toNat ∧
      arenaNextOff s0.arena s0.arena_len src.toNat ≤ s0.arena_len ∧
      s_2.arena[src.toNat]? = s0.arena[src.toNat]? ∧
      s_2.arena[(src + 2#64).toNat]? = s0.arena[src.toNat + 2]? ∧
      (s_2.arena[(src + 2#64).toNat]'hsrc2_len).toNat = arenaClauseSize s0 src.toNat := by
  have har := c.harena; unfold dimacsBound at har
  have hlen_a := hinv0.lengths.arena_len_le
  have hwf0 := hinv0.arena.refs_wf src.toNat hsuf_c.1
  have h2_ar : s_2.arena.length = c.arena_cap := hlen_2.arena_len_arr
  have hsrc_len : src.toNat < s_2.arena.length := by omega
  have hsrc2_eq : (src + 2#64).toNat = src.toNat + 2 := bv64_add_toNat (by omega)
  have hsrc2_len : (src + 2#64).toNat < s_2.arena.length := by rw [hsrc2_eq]; omega
  have hsrc_t : (src.truncate 32).toNat = src.toNat := by
    rw [bv64_truncate32 (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hnb0 := arenaNextOff_bounds (ar := s0.arena) (alen := s0.arena_len) (cref := src.toNat)
    hwf0.1
  have hnsrc_eq : (BitVec.ofNat 32 (arenaNextOff s0.arena s0.arena_len src.toNat)
      |>.setWidth 64).toNat = arenaNextOff s0.arena s0.arena_len src.toNat := by
    rw [bv_c0_zext32_64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsz_eq : s_2.arena[(src + 2#64).toNat]? = s0.arena[src.toNat + 2]? := by
    rw [hsrc2_eq]; exact hsuf_c.2.2.2.1
  have hsz_nat : (s_2.arena[(src + 2#64).toNat]'hsrc2_len).toNat =
      arenaClauseSize s0 src.toNat := by
    unfold arenaClauseSize; rw [← hsz_eq, List.getElem?_eq_getElem hsrc2_len, Option.getD_some]
  exact ⟨hsrc2_len, hsrc_len, hsrc2_eq, hsrc_t, hnsrc_eq, h2_ar, hnb0.1, hnb0.2,
    hsuf_c.2.2.1, hsz_eq, hsz_nat⟩

theorem sw2_copy_prep {c : PlainCfg} {F0 : CNF Nat} {s0 s_2 : PlainState}
    {src dst : BitVec 64} {ic : BitVec 32} {ar_c : List (BitVec 32)}
    (hinv0 : PlainCoreInv c F0 s0) (hp_2 : ArenaPrefixOk c F0 s0 s_2 src.toNat dst.toNat)
    (hsuf_bd : src.toNat + 3 + arenaClauseSize s0 src.toNat ≤ s0.arena_len)
    (hdst_le : dst.toNat ≤ src.toNat) (hic_lt : ic.toNat < arenaClauseSize s0 src.toNat)
    (har_c : ar_c.length = c.arena_cap)
    (hsuf_c : ∀ k, src.toNat + 3 + ic.toNat ≤ k → k < s0.arena_len → ar_c[k]? = s_2.arena[k]?) :
    (ic + 1#32).toNat = ic.toNat + 1 ∧
    (src + 3#64 + ic.setWidth 64).toNat = src.toNat + 3 + ic.toNat ∧
    (dst + 3#64 + ic.setWidth 64).toNat = dst.toNat + 3 + ic.toNat ∧
    (src + 3#64 + ic.setWidth 64).toNat < ar_c.length ∧
    (dst + 3#64 + ic.setWidth 64).toNat < ar_c.length ∧
    ar_c[src.toNat + 3 + ic.toNat]? = s0.arena[src.toNat + 3 + ic.toNat]? := by
  have har := c.harena; unfold dimacsBound at har
  have hlen_a := hinv0.lengths.arena_len_le
  have hic1 : (ic + 1#32).toNat = ic.toNat + 1 := by bv_omega
  have hsi_eq : (src + 3#64 + ic.setWidth 64).toNat = src.toNat + 3 + ic.toNat := by bv_omega
  have hdi_eq : (dst + 3#64 + ic.setWidth 64).toNat = dst.toNat + 3 + ic.toNat := by bv_omega
  have hsi_lt : (src + 3#64 + ic.setWidth 64).toNat < ar_c.length := by rw [har_c, hsi_eq]; omega
  have hdi_lt : (dst + 3#64 + ic.setWidth 64).toNat < ar_c.length := by rw [har_c, hdi_eq]; omega
  have har_sc : ar_c[src.toNat + 3 + ic.toNat]? = s0.arena[src.toNat + 3 + ic.toNat]? :=
    (hsuf_c _ (Nat.le_refl _) (by omega)).trans (hp_2.suffix_eq _ (by omega) (by omega))
  exact ⟨hic1, hsi_eq, hdi_eq, hsi_lt, hdi_lt, har_sc⟩

theorem sw2_rsn_prep {c : PlainCfg} {F0 : CNF Nat} {s_2 : PlainState} {dst : BitVec 64}
    {ir : BitVec 32} {ar1 : List (BitVec 32)} (htv_2 : TrailValsInv c F0 s_2)
    (hva_l : s_2.vals.length = 2 * c.mv) (hdi_lt : (dst + 3#64 + ir.setWidth 64).toNat < ar1.length)
    (_hdi_eq : (dst + 3#64 + ir.setWidth 64).toNat = dst.toNat + 3 + ir.toNat)
    (har1_len : dst.toNat + 3 + ir.toNat < ar1.length)
    (hlit_ar : ar1[(dst + 3#64 + ir.setWidth 64).toNat]'hdi_lt =
      ar1[dst.toNat + 3 + ir.toNat]'har1_len)
    (hlit_ir : (ar1[dst.toNat + 3 + ir.toNat]'har1_len).toNat < 2 * c.mv) :
    ((ar1[(dst + 3#64 + ir.setWidth 64).toNat]'hdi_lt) >>> (1 : Nat)).toNat < c.mv ∧
    (((ar1[(dst + 3#64 + ir.setWidth 64).toNat]'hdi_lt) >>> (1 : Nat)).setWidth 64).toNat <
      c.mv ∧
    (s_2.vals[(ar1[dst.toNat + 3 + ir.toNat]'har1_len).toNat]'(by omega) = 0#8 ∨
      s_2.vals[(ar1[dst.toNat + 3 + ir.toNat]'har1_len).toNat]'(by omega) = 1#8 ∨
      s_2.vals[(ar1[dst.toNat + 3 + ir.toNat]'har1_len).toNat]'(by omega) = 0xFF#8) := by
  have h1 : ((ar1[(dst + 3#64 + ir.setWidth 64).toNat]'hdi_lt) >>> (1 : Nat)).toNat < c.mv := by
    rw [PlainReduceTactics.bv_c0_shr1n_32, hlit_ar]; omega
  have h2 : (((ar1[(dst + 3#64 + ir.setWidth 64).toNat]'hdi_lt) >>>
      (1 : Nat)).setWidth 64).toNat < c.mv := by rw [bv_c0_zext32_64]; exact h1
  have h0 := htv_2.vals_domain _ hlit_ir
  rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h0
  exact ⟨h1, h2, h0⟩

end PlainReduceHelpers

end

end LeanQbe.T.Examples.Kissat.Plain
