/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Eliminate.Helpers
public import LeanQbe.T.Examples.Kissat.Proof.Eliminate.Spec
public import LeanQbe.T.Examples.Kissat.Src.Eliminate
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat BVE `Func.wp` Proofs — Part 1 (`Wp1`: `full_bve_commit_res_wp`)

Clean `CanonicalEnv` `Func.wp` proof for `full_bve_commit_res` (`Spec.fullBveCommitResTmkSpec`),
with `0` legacy `Full*` imports, `<= 100` cols, every decl `<= 450`L.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Eliminate

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Eliminate
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Definition.Spec
open LeanQbe.T.Examples.Kissat.Proof.Eliminate.EliminateTactics
open Kraken.Bedrock2.Test

open scoped FullArenaTactics
open scoped EliminateTactics

private abbrev CommitLoopInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 : FullState) (r_off r_end : BitVec 64) (R : Mem 64 → Prop) :
    Nat → Tup Val [i64] → Mem 64 → Prop :=
  fun rem (rp, ()) m =>
    ∃ s : FullState,
      FullDenseInvW c F0 F_cur s ∧ TmkZero s ∧
      s.core.cur_vars = s0.core.cur_vars ∧ s.core.fuel = s0.core.fuel ∧
      r_off.toNat ≤ rp.toNat ∧ rp.toNat ≤ r_end.toNat ∧ rem = r_end.toNat - rp.toNat ∧
      FullResBufOkW F_cur s r_end.toNat rp.toNat ∧ (FullMem c s ⋆ R) m

private abbrev CommitStepInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (sp : FullState) (R : Mem 64 → Prop) : Mem 64 → Prop :=
  fun m => ∃ s' : FullState,
    FullDenseInvW c F0 F_cur s' ∧ TmkZero s' ∧
    s'.core.cur_vars = sp.core.cur_vars ∧ s'.core.fuel = sp.core.fuel ∧
    s'.scratch.scratch_buf = sp.scratch.scratch_buf ∧ (FullMem c s' ⋆ R) m

private abbrev CommitCopyInv (c : FullCfg) (s1 : FullState) (ar0 : List (BitVec 32))
    (alen0 rp0 : Nat) (sz : BitVec 32) (R : Mem 64 → Prop) :
    Nat → Tup Val [i32] → Mem 64 → Prop :=
  fun rem (k, ()) m =>
    ∃ (ar' fl' : List (BitVec 32)),
      k.toNat ≤ sz.toNat ∧ rem = sz.toNat - k.toNat ∧
      ar'.length = c.arena_cap ∧ fl'.length = c.max_vars ∧
      (∀ i < alen0, ar'[i]? = ar0[i]?) ∧
      ar'[alen0]?.getD 0#32 &&& 8388608#32 = 0#32 ∧
      ar'[alen0]?.getD 0#32 &&& 524288#32 = 0#32 ∧
      (ar'[alen0 + 2]?.getD 0#32).toNat = sz.toNat ∧
      (∀ i < k.toNat,
        ar'[alen0 + 3 + i]? = s1.scratch.scratch_buf[rp0 + 1 + i]?) ∧
      (FullMem c { s1 with core := { s1.core with arena := ar', flags := fl' } } ⋆ R) m

private abbrev CommitWatchInv (c : FullCfg) (F_cur : List (List Nat)) (scp : FullState)
    (sz : BitVec 32) (R : Mem 64 → Prop) :
    Nat → Tup Val [i32] → Mem 64 → Prop :=
  fun rem (k, ()) m =>
    ∃ (wv' ws' : List (BitVec 32)) (wlen' : Nat) (wu' : BitVec 64)
      (wsort' : List (BitVec 32)),
      let sk : FullState :=
        { core := { scp.core with wlen := wlen', wusable := wu', wvec := wv', wstk := ws' }
          scratch := { scp.scratch with wsort := wsort' } }
      k.toNat ≤ sz.toNat ∧ rem = sz.toNat - k.toNat ∧
      sk.LengthsOk c ∧ DenseWatchesInv F_cur sk.core ∧ (FullMem c sk ⋆ R) m

private theorem commit_empty_unsat {F : CNF Nat} (h : F.EntailsClause (cnfClause [])) :
    F.Unsat := by
  intro α
  by_cases hs : CNF.Sat α F
  · exfalso
    obtain ⟨_, hm, _⟩ := (clause_sat_cnfClause_iff α []).mp ((CNF.entails_clause_def.mp h) α hs)
    exact List.not_mem_nil hm
  · exact Bool.eq_false_iff.mpr fun he => hs he

private theorem commit_resBufOk_congr {F_cur : List (List Nat)} {s1 s2 : FullState}
    {r_end p : Nat} (hscr : s2.scratch.scratch_buf = s1.scratch.scratch_buf)
    (hcv : s2.core.cur_vars = s1.core.cur_vars)
    (h : FullResBufOkW F_cur s1 r_end p) : FullResBufOkW F_cur s2 r_end p := by
  induction h with
  | nil => exact FullResBufOkW.nil
  | cons h1 h2 h3 h4 h5 _ ih =>
    rw [← hscr] at h2 h3 h4 h5; rw [← hcv] at h3
    exact FullResBufOkW.cons h1 h2 h3 h4 h5 ih

private theorem commit_dense_reloc {F_cur : List (List Nat)} {k k' : FullCoreState}
    (hdw : DenseWatchesInv F_cur k) (hlay' : WatchStackLayout k')
    (hvars : k'.cur_vars = k.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hkeep : ∀ l < 2 * k.cur_vars,
      fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ j < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k' l + j]? = k.wstk[fullWatchOffCore k l + j]?) :
    DenseWatchesInv F_cur k' := by
  refine ⟨hlay', fun l hl => ?_⟩
  rw [hvars] at hl
  have hk := hkeep l hl
  rw [hk.1]
  exact (hdw.slices l hl).relocate ((CNF.entails_def _ _).mpr fun _ h => h)
    (Nat.le_of_eq hvars.symm) hsub hk.2

private theorem commit_dense_push_occ {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit : Nat} {w0 cref : BitVec 32}
    (hdw : DenseWatchesInv F_cur k) (hlay' : WatchStackLayout k')
    (hlit_lt : lit < 2 * k.cur_vars) (hvars : k'.cur_vars = k.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hother : ∀ l < 2 * k.cur_vars, l ≠ lit →
      fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ j < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k' l + j]? = k.wstk[fullWatchOffCore k l + j]?)
    (hsz_eq : fullWatchSizeCore k' lit = fullWatchSizeCore k lit + 2)
    (hkeep : ∀ j < fullWatchSizeCore k lit,
      k'.wstk[fullWatchOffCore k' lit + j]? = k.wstk[fullWatchOffCore k lit + j]?)
    (hw0 : k'.wstk[fullWatchOffCore k' lit + fullWatchSizeCore k lit]? = some w0)
    (hw1 : k'.wstk[fullWatchOffCore k' lit + fullWatchSizeCore k lit + 1]? = some cref)
    (hflag : (w0 &&& 0x80000000#32) = 0#32) (hsz3 : 3 ≤ w0.toNat)
    (hlt : cref.toNat < 0x80000000) (href : cref.toNat ∈ fullArenaClauseRefsCore k') :
    DenseWatchesInv F_cur k' := by
  refine ⟨hlay', fun l hl => ?_⟩
  rw [hvars] at hl
  by_cases hll : l = lit
  · subst hll
    rw [hsz_eq]
    exact (hdw.slices l hlit_lt).append_occ (Nat.le_of_eq hvars.symm)
      hsub hkeep hw0 hw1 hflag hsz3 hlt href
  · have hk := hother l hl hll
    rw [hk.1]
    exact (hdw.slices l hl).relocate ((CNF.entails_def _ _).mpr fun _ h => h)
      (Nat.le_of_eq hvars.symm) hsub hk.2

private theorem commit_copied_lits_eq {c : FullCfg} {s s_k : FullState}
    {rp_n sz_n : Nat}
    (hlen_k : s_k.LengthsOk c) (_hlen0 : s.LengthsOk c)
    (_halen : s_k.core.arena_len = s.core.arena_len + 3 + sz_n)
    (hbd : s.core.arena_len + 3 + sz_n ≤ c.arena_cap)
    (hsz_eq : (s_k.core.arena[s.core.arena_len + 2]?.getD 0#32).toNat = sz_n)
    (hcopy : ∀ i < sz_n,
      s_k.core.arena[s.core.arena_len + 3 + i]? = s.scratch.scratch_buf[rp_n + 1 + i]?) :
    fullArenaClauseLitsCore s_k.core s.core.arena_len =
      (List.range sz_n).map
        (fun i => (s.scratch.scratch_buf[rp_n + 1 + i]?.getD 0#32).toNat) := by
  have har_len : s_k.core.arena.length = c.arena_cap := hlen_k.core_ok.arena_len_arr
  unfold fullArenaClauseLitsCore fullArenaClauseSizeCore
  have hal : (s_k.core.arena[s.core.arena_len + 2]?.getD 0#32).toNat = sz_n := hsz_eq
  rw [hal]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_take, List.length_drop, har_len, List.length_range]
    omega
  · intro i hi1 hi2
    have hi : i < sz_n := by simp at hi2; exact hi2
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop, List.getElem_range]
    have hc := hcopy i hi
    rw [List.getElem?_eq_getElem (by omega)] at hc
    simp [← hc]

private theorem commit_core_lengths_ok {c : FullCfg} {k1 k2 : FullCoreState}
    (h : FullCoreState.LengthsOk c k1)
    (hv : k2.vals = k1.vals) (hlm : k2.lit_mark = k1.lit_mark) (hmrk : k2.mrk = k1.mrk)
    (hfl : k2.flags.length = c.max_vars) (hlvl : k2.lvl = k1.lvl) (hrsn : k2.rsns = k1.rsns)
    (htrl : k2.trl = k1.trl) (htp : k2.trail_pos = k1.trail_pos) (htmp : k2.tmp = k1.tmp)
    (hmc : k2.min_clr = k1.min_clr) (hft : k2.frame_trail = k1.frame_trail)
    (hfd : k2.frame_dec = k1.frame_dec) (hwv : k2.wvec.length = 4 * c.max_vars)
    (hrep : k2.repr = k1.repr) (hms : k2.min_stk = k1.min_stk)
    (har : k2.arena.length = c.arena_cap) (hws : k2.wstk.length = c.wcap)
    (hcv : k2.cur_vars = k1.cur_vars) (hal : k2.arena_len ≤ c.arena_cap)
    (hwl : k2.wlen ≤ c.wcap) (hte : k2.trail_end = k1.trail_end)
    (hpr : k2.propagated = k1.propagated) (htl : k2.tmp_len = k1.tmp_len)
    (hmcl : k2.min_clr_len = k1.min_clr_len) :
    FullCoreState.LengthsOk c k2 :=
  ⟨hv ▸ h.vals_len, hlm ▸ h.lit_mark_len, hmrk ▸ h.mrk_len, hfl, hlvl ▸ h.lvl_len,
   hrsn ▸ h.rsns_len, htrl ▸ h.trl_len, htp ▸ h.trail_pos_len, htmp ▸ h.tmp_len_arr,
   hmc ▸ h.min_clr_len_arr, hft ▸ h.frame_trail_len, hfd ▸ h.frame_dec_len, hwv,
   hrep ▸ h.repr_len, hms ▸ h.min_stk_len, har, hws, hcv ▸ h.cur_vars_ge, hcv ▸ h.cur_vars_le,
   hal, hwl, hte ▸ hcv ▸ h.trail_end_le, hpr ▸ hte ▸ h.propagated_le,
   htl ▸ h.tmp_len_le, hmcl ▸ h.min_clr_len_le⟩

private theorem commit_or_16m_and_8m {w : BitVec 32} (h : w &&& 8388608#32 = 0#32) :
    (w ||| 16777216#32) &&& 8388608#32 = 0#32 := by
  rw [BitVec.and_or_distrib_right, h]; decide

private theorem commit_or_16m_and_512k {w : BitVec 32} (h : w &&& 524288#32 = 0#32) :
    (w ||| 16777216#32) &&& 524288#32 = 0#32 := by
  rw [BitVec.and_or_distrib_right, h]; decide

private theorem commit_or_512k_and_8m {w : BitVec 32} (h : w &&& 8388608#32 = 0#32) :
    (w ||| 524288#32) &&& 8388608#32 = 0#32 := by
  rw [BitVec.and_or_distrib_right, h]; decide

private theorem commit_or_512k_ne0 (w : BitVec 32) :
    (w ||| 524288#32) &&& 524288#32 ≠ 0#32 := by
  intro h0
  have hb := congrArg (fun x : BitVec 32 => x.getLsbD 19) h0
  simp at hb

private theorem commit_mem_congr {c : FullCfg} {s1 s2 : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (heq : s1 = s2) (hm : (FullMem c s1 ⋆ R) m) :
    (FullMem c s2 ⋆ R) m :=
  heq ▸ hm

private theorem commit_sz31_props {sz : BitVec 32} (hge3 : 3 ≤ sz.toNat)
    (hlt : sz.toNat < 2 ^ 28) :
    (sz &&& 0x7FFFFFFF#32).toNat = sz.toNat ∧
    (sz &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32 ∧
    ((sz &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32 ∧
    3 ≤ (sz &&& 0x7FFFFFFF#32).toNat := by
  have h1 : (sz &&& 0x7FFFFFFF#32) = sz := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 from rfl]
    exact Nat.and_two_pow_sub_one_eq_mod sz.toNat 31 |>.trans (Nat.mod_eq_of_lt (by omega))
  refine ⟨by rw [h1], ?_, ?_, by rw [h1]; exact hge3⟩
  · rw [h1]; exact elim_bv32_ne_sent_of_lt (by omega)
  · rw [h1]; exact elim_bv32_and_msb_zero_of_lt (by omega)

private theorem commit_lay_core_congr {k1 k2 : FullCoreState}
    (h : WatchStackLayout k1) (hcv : k2.cur_vars = k1.cur_vars)
    (hwl : k2.wlen = k1.wlen) (hwv : k2.wvec = k1.wvec) (hws : k2.wstk = k1.wstk) :
    WatchStackLayout k2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l hl
    have := h.bounds l (hcv ▸ hl)
    simpa [fullWatchOffCore, fullWatchSizeCore, hwv, hwl] using this
  · intro l hl hsz
    have := h.pos_off l (hcv ▸ hl) (by simpa [fullWatchSizeCore, hwv] using hsz)
    simpa [fullWatchOffCore, hwv] using this
  · intro l1 l2 hl1 hl2 hne hs1 hs2
    have := h.disjoint l1 l2 (hcv ▸ hl1) (hcv ▸ hl2) hne
      (by simpa [fullWatchSizeCore, hwv] using hs1)
      (by simpa [fullWatchSizeCore, hwv] using hs2)
    simpa [fullWatchOffCore, fullWatchSizeCore, hwv] using this
  · intro l hl idx hidx
    have := h.no_sentinel l (hcv ▸ hl) idx
      (by simpa [fullWatchSizeCore, hwv] using hidx)
    simpa [fullWatchOffCore, hwv, hws] using this

private theorem commit_alloc_init_ok {c : FullCfg} {sp : FullState}
    {arena1 : List (BitVec 32)} {sz : BitVec 32} {cr : BitVec 64}
    (hcr_eq : cr.toNat = sp.core.arena_len) (hcr_ar : cr.toNat < arena1.length)
    (har1_len : arena1.length = c.arena_cap)
    (har1_pre : ∀ i < sp.core.arena_len, arena1[i]? = sp.core.arena[i]?)
    (har1_8m : arena1[sp.core.arena_len]?.getD 0#32 &&& 8388608#32 = 0#32)
    (har1_512k : arena1[sp.core.arena_len]?.getD 0#32 &&& 524288#32 = 0#32)
    (har1_sz : (arena1[sp.core.arena_len + 2]?.getD 0#32).toNat = sz.toNat) :
    let w0 := arena1[cr.toNat]'hcr_ar
    let arena_i := arena1.set cr.toNat (w0 ||| 16777216#32)
    arena_i.length = c.arena_cap ∧
    (∀ i < sp.core.arena_len, arena_i[i]? = sp.core.arena[i]?) ∧
    arena_i[sp.core.arena_len]?.getD 0#32 &&& 8388608#32 = 0#32 ∧
    arena_i[sp.core.arena_len]?.getD 0#32 &&& 524288#32 = 0#32 ∧
    (arena_i[sp.core.arena_len + 2]?.getD 0#32).toNat = sz.toNat := by
  intro w0 arena_i
  have hset : arena_i[sp.core.arena_len]? = some (w0 ||| 16777216#32) := by
    simpa [arena_i, hcr_eq] using List.getElem?_set_self hcr_ar
  have hcr_len : sp.core.arena_len < arena1.length := hcr_eq ▸ hcr_ar
  rw [List.getElem?_eq_getElem hcr_len, Option.getD_some] at har1_8m har1_512k
  refine ⟨by simp [arena_i, har1_len], ?_, ?_, ?_, ?_⟩
  · intro i hi
    dsimp only [arena_i]
    rw [List.getElem?_set_ne (by rw [hcr_eq]; omega)]; exact har1_pre i hi
  · rw [hset, Option.getD_some]
    exact commit_or_16m_and_8m (by simpa [w0, hcr_eq] using har1_8m)
  · rw [hset, Option.getD_some]
    exact commit_or_16m_and_512k (by simpa [w0, hcr_eq] using har1_512k)
  · dsimp only [arena_i]
    rw [List.getElem?_set_ne (by rw [hcr_eq]; omega)]; exact har1_sz

private theorem commit_copy_step_ok {c : FullCfg} {sp s1 : FullState}
    {arc : List (BitVec 32)} {rp cr : BitVec 64} {sz kc lk : BitVec 32}
    (_hscr_eq : s1.scratch.scratch_buf = sp.scratch.scratch_buf)
    (hcr_eq : cr.toNat = sp.core.arena_len) (harc_len : arc.length = c.arena_cap)
    (har_fit : sp.core.arena_len + 3 + sz.toNat ≤ c.arena_cap)
    (harc : c.arena_cap < 2 * 2 ^ 28)
    (hkc_lt : kc.toNat < sz.toNat) (hk_lt_28 : sz.toNat < 2 ^ 28)
    (hrp_nxt : rp.toNat + 1 + sz.toNat ≤ c.scratch_cap) (hsc : c.scratch_cap < 2 ^ 28)
    (harc_pre : ∀ i < sp.core.arena_len, arc[i]? = sp.core.arena[i]?)
    (harc_8m : arc[sp.core.arena_len]?.getD 0#32 &&& 8388608#32 = 0#32)
    (harc_512k : arc[sp.core.arena_len]?.getD 0#32 &&& 524288#32 = 0#32)
    (harc_sz : (arc[sp.core.arena_len + 2]?.getD 0#32).toNat = sz.toNat)
    (hcopy : ∀ i < kc.toNat,
      arc[sp.core.arena_len + 3 + i]? = s1.scratch.scratch_buf[rp.toNat + 1 + i]?)
    (hsrc_sc : (rp + 1#64 + kc.setWidth 64).toNat < s1.scratch.scratch_buf.length)
    (hlk : lk = s1.scratch.scratch_buf[(rp + 1#64 + kc.setWidth 64).toNat]'hsrc_sc) :
    let arc' := arc.set (cr + 3#64 + kc.setWidth 64).toNat lk
    (rp + 1#64 + kc.setWidth 64).toNat = rp.toNat + 1 + kc.toNat ∧
    (kc + 1#32).toNat = kc.toNat + 1 ∧
    arc'.length = c.arena_cap ∧
    (∀ i < sp.core.arena_len, arc'[i]? = sp.core.arena[i]?) ∧
    arc'[sp.core.arena_len]?.getD 0#32 &&& 8388608#32 = 0#32 ∧
    arc'[sp.core.arena_len]?.getD 0#32 &&& 524288#32 = 0#32 ∧
    (arc'[sp.core.arena_len + 2]?.getD 0#32).toNat = sz.toNat ∧
    ∀ i < (kc + 1#32).toNat,
      arc'[sp.core.arena_len + 3 + i]? = s1.scratch.scratch_buf[rp.toNat + 1 + i]? := by
  intro arc'
  have hdst_eq : (cr + 3#64 + kc.setWidth 64).toNat = sp.core.arena_len + 3 + kc.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_add, elim_zext32_toNat, hcr_eq,
      show (3#64 : BitVec 64).toNat = 3 from rfl]
    rw [Nat.mod_eq_of_lt (by omega : sp.core.arena_len + 3 < 2 ^ 64)]
    exact Nat.mod_eq_of_lt (by omega)
  have hsrc_eq : (rp + 1#64 + kc.setWidth 64).toNat = rp.toNat + 1 + kc.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_add, elim_zext32_toNat,
      show (1#64 : BitVec 64).toNat = 1 from rfl]
    rw [Nat.mod_eq_of_lt (by omega : rp.toNat + 1 < 2 ^ 64)]
    exact Nat.mod_eq_of_lt (by omega)
  have hkc1_eq : (kc + 1#32).toNat = kc.toNat + 1 := by
    rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  have hdst_ar : (cr + 3#64 + kc.setWidth 64).toNat < arc.length := by
    rw [harc_len, hdst_eq]; omega
  refine ⟨hsrc_eq, hkc1_eq, by simp [arc', harc_len], ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    dsimp only [arc']
    rw [List.getElem?_set_ne (by rw [hdst_eq]; omega)]; exact harc_pre i hi
  · dsimp only [arc']
    rw [List.getElem?_set_ne (by rw [hdst_eq]; omega)]; exact harc_8m
  · dsimp only [arc']
    rw [List.getElem?_set_ne (by rw [hdst_eq]; omega)]; exact harc_512k
  · dsimp only [arc']
    rw [List.getElem?_set_ne (by rw [hdst_eq]; omega)]; exact harc_sz
  · intro i hi; rw [hkc1_eq] at hi
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hilt | hieq
    · dsimp only [arc']
      rw [List.getElem?_set_ne (by rw [hdst_eq]; omega)]; exact hcopy i hilt
    · subst hieq
      dsimp only [arc']
      rw [← hdst_eq, List.getElem?_set_self hdst_ar, hlk]
      have hsrc_sc' : rp.toNat + 1 + kc.toNat < s1.scratch.scratch_buf.length :=
        hsrc_eq ▸ hsrc_sc
      rw [List.getElem?_eq_getElem hsrc_sc']
      congr 1; simp only [hsrc_eq]

private theorem commit_post_copy_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {sp scp : FullState} {rp_n sz_n : Nat} {sz : BitVec 32}
    (hdwp : FullDenseInvW c F0 F_cur sp) (hlok_cp : scp.LengthsOk c)
    (hscp : scp.core.arena_len = sp.core.arena_len + 3 + sz.toNat)
    (hcv_cp : scp.core.cur_vars = sp.core.cur_vars)
    (hwl_cp : scp.core.wlen = sp.core.wlen) (hwv_cp : scp.core.wvec = sp.core.wvec)
    (hws_cp : scp.core.wstk = sp.core.wstk)
    (hsz_eq : sz.toNat = sz_n) (hsz_ge3 : 3 ≤ sz.toNat)
    (har_fit : sp.core.arena_len + 3 + sz.toNat ≤ c.arena_cap)
    (harc_pre : ∀ i < sp.core.arena_len, scp.core.arena[i]? = sp.core.arena[i]?)
    (harc_8m : scp.core.arena[sp.core.arena_len]?.getD 0#32 &&& 8388608#32 = 0#32)
    (harc_sz : (scp.core.arena[sp.core.arena_len + 2]?.getD 0#32).toNat = sz.toNat)
    (hcopy_all : ∀ i < sz.toNat,
      scp.core.arena[sp.core.arena_len + 3 + i]? = sp.scratch.scratch_buf[rp_n + 1 + i]?)
    (hlits_bd : ∀ k < sz_n, (sp.scratch.scratch_buf[rp_n + 1 + k]?.getD 0#32).toNat <
      2 * sp.core.cur_vars)
    (hnodup : (List.map (fun k => (sp.scratch.scratch_buf[rp_n + 1 + k]?.getD 0#32).toNat / 2)
      (List.range sz_n)).Nodup)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause (List.map
      (fun k => (sp.scratch.scratch_buf[rp_n + 1 + k]?.getD 0#32).toNat) (List.range sz_n)))) :
    fullArenaClauseRefsCore scp.core = fullArenaClauseRefsCore sp.core ++ [sp.core.arena_len] ∧
    DenseWatchesInv F_cur scp.core ∧
    (∀ l ∈ fullArenaClauseLitsCore scp.core sp.core.arena_len, l < 2 * sp.core.cur_vars) ∧
    (List.map (fun x => x / 2) (fullArenaClauseLitsCore scp.core sp.core.arena_len)).Nodup ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullArenaClauseLitsCore scp.core sp.core.arena_len)) := by
  have hrefs := fullArenaClauseRefsCore_append hdwp.2.1.arena hsz_ge3 hscp harc_pre harc_8m harc_sz
  have hsub : ∀ r ∈ fullArenaClauseRefsCore sp.core, r ∈ fullArenaClauseRefsCore scp.core := by
    intro r hr; rw [hrefs]; exact List.mem_append_left _ hr
  have hdw_sp : DenseWatchesInv F_cur sp.core := by
    have hmw := hdwp.2.1.watches; unfold ModeWatchesInv at hmw
    simpa [ite_eq_right (fun h0 => hdwp.2.2.2.2.2.2 h0)] using hmw
  have hlay_cp := commit_lay_core_congr hdw_sp.layout hcv_cp hwl_cp hwv_cp hws_cp
  have hdw_cp := commit_dense_reloc hdw_sp hlay_cp hcv_cp hsub fun _ _ =>
    ⟨by simp [fullWatchSizeCore, hwv_cp], fun _ _ => by
      simp [fullWatchOffCore, hwv_cp, hws_cp]⟩
  have hcl_eq : fullArenaClauseLitsCore scp.core sp.core.arena_len = (List.range sz_n).map
      (fun i => (sp.scratch.scratch_buf[rp_n + 1 + i]?.getD 0#32).toNat) :=
    commit_copied_lits_eq hlok_cp hdwp.1 (by rw [hscp, hsz_eq]) (by omega)
      (by rw [← hsz_eq]; exact harc_sz) (fun i hi => hcopy_all i (by omega))
  refine ⟨hrefs, hdw_cp, ?_, ?_, ?_⟩
  · intro l hl; rw [hcl_eq, List.mem_map] at hl
    obtain ⟨i, hi, rfl⟩ := hl; exact hlits_bd i (List.mem_range.mp hi)
  · rw [hcl_eq, List.map_map]; exact hnodup
  · rw [hcl_eq]; exact hent

private theorem commit_watch_oom_dw {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {sp scp sk' : FullState} {sz : BitVec 32} {cr : BitVec 64}
    {wv'' ws'' wsort'' : List (BitVec 32)} {wlen'' : Nat} {wu'' : BitVec 64}
    (hdwp : FullDenseInvW c F0 F_cur sp)
    (hlok_w' : sk'.LengthsOk c) (hdw_w' : DenseWatchesInv F_cur sk'.core)
    (hrefs_cp : fullArenaClauseRefsCore scp.core =
      fullArenaClauseRefsCore sp.core ++ [sp.core.arena_len])
    (hsk'_ar : sk'.core.arena = scp.core.arena)
    (hsk'_alen : sk'.core.arena_len = scp.core.arena_len)
    (hsk'_cv : sk'.core.cur_vars = sp.core.cur_vars)
    (hsk'_wl : sk'.core.wlen = wlen'') (hsk'_wv : sk'.core.wvec = wv'')
    (hsk'_ws : sk'.core.wstk = ws'')
    (hscp_al : scp.core.arena_len = sp.core.arena_len + 3 + sz.toNat)
    (hcr_eq : cr.toNat = sp.core.arena_len) (hcr_ar' : cr.toNat < sk'.core.arena.length)
    (hsz_ge3 : 3 ≤ sz.toNat) (hflc_len : scp.core.flags.length = c.max_vars)
    (harc_pre : ∀ i < sp.core.arena_len, scp.core.arena[i]? = sp.core.arena[i]?)
    (harc_8m : scp.core.arena[sp.core.arena_len]?.getD 0#32 &&& 8388608#32 = 0#32)
    (harc_sz : (scp.core.arena[sp.core.arena_len + 2]?.getD 0#32).toNat = sz.toNat)
    (hwsort_len : wsort''.length = 2 * c.max_vars) :
    let wg := sk'.core.arena[cr.toNat]'hcr_ar'
    let ar_g := sk'.core.arena.set cr.toNat (wg ||| 524288#32)
    let sg : FullState :=
      { core := { sp.core with
          arena_len := sp.core.arena_len + 3 + sz.toNat, wlen := wlen'', wusable := wu'',
          arena_garbage := sk'.core.arena_garbage + 3#64 + sz.setWidth 64, oom := 1#64,
          flags := scp.core.flags, wvec := wv'', arena := ar_g, wstk := ws'' }
        scratch := { sp.scratch with wsort := wsort'' } }
    FullDenseInvW c F0 F_cur sg := by
  intro wg ar_g sg
  let sg_base : FullState := { core := sg.core, scratch := sp.scratch }
  have harg_len : ar_g.length = c.arena_cap := by simp [ar_g, hlok_w'.core_ok.arena_len_arr]
  have harg_pre : ∀ i < sp.core.arena_len, ar_g[i]? = sp.core.arena[i]? := by
    intro i hi
    dsimp only [ar_g]
    rw [List.getElem?_set_ne (by rw [hcr_eq]; omega), hsk'_ar]; exact harc_pre i hi
  have hcr_len' : sp.core.arena_len < scp.core.arena.length := hcr_eq ▸ hsk'_ar ▸ hcr_ar'
  rw [List.getElem?_eq_getElem hcr_len', Option.getD_some] at harc_8m
  have harg_8m : ar_g[sp.core.arena_len]?.getD 0#32 &&& 8388608#32 = 0#32 := by
    have hset : ar_g[sp.core.arena_len]? = some (wg ||| 524288#32) := by
      simpa [ar_g, hcr_eq] using List.getElem?_set_self hcr_ar'
    rw [hset, Option.getD_some]
    exact commit_or_512k_and_8m (by simpa [wg, hcr_eq, hsk'_ar] using harc_8m)
  have harg_512k : ar_g[sp.core.arena_len]?.getD 0#32 &&& 524288#32 ≠ 0#32 := by
    have hset : ar_g[sp.core.arena_len]? = some (wg ||| 524288#32) := by
      simpa [ar_g, hcr_eq] using List.getElem?_set_self hcr_ar'
    rw [hset, Option.getD_some]; exact commit_or_512k_ne0 wg
  have harg_sz : (ar_g[sp.core.arena_len + 2]?.getD 0#32).toNat = sz.toNat := by
    dsimp only [ar_g]
    rw [List.getElem?_set_ne (by rw [hcr_eq]; omega), hsk'_ar]; exact harc_sz
  have hlok_base : sg_base.LengthsOk c :=
    ⟨commit_core_lengths_ok hdwp.1.core_ok rfl rfl rfl hflc_len rfl rfl rfl rfl rfl rfl rfl rfl
      (by dsimp only [sg_base, sg]; rw [← hsk'_wv]; exact hlok_w'.core_ok.wvec_len) rfl rfl
      harg_len (by dsimp only [sg_base, sg]; rw [← hsk'_ws]; exact hlok_w'.core_ok.wstk_len_arr)
      rfl
      (by
        dsimp only [sg_base, sg]; rw [← hscp_al, ← hsk'_alen]
        exact hlok_w'.core_ok.arena_len_le)
      (by dsimp only [sg_base, sg]; rw [← hsk'_wl]; exact hlok_w'.core_ok.wlen_le)
      rfl rfl rfl rfl,
     hdwp.1.scratch_ok⟩
  have hrefs_g := fullArenaClauseRefsCore_append (k' := sg_base.core) hdwp.2.1.arena hsz_ge3 rfl
    harg_pre harg_8m harg_sz
  have hsub_g : ∀ r ∈ fullArenaClauseRefsCore sk'.core,
      r ∈ fullArenaClauseRefsCore sg_base.core := by
    intro r hr
    have hsame : fullArenaClauseRefsCore sk'.core = fullArenaClauseRefsCore scp.core := by
      unfold fullArenaClauseRefsCore; simp [hsk'_ar, hsk'_alen]
    rw [hrefs_g]; rw [hsame, hrefs_cp] at hr; exact hr
  have hlay_g := commit_lay_core_congr (k2 := sg_base.core) hdw_w'.layout hsk'_cv.symm
    hsk'_wl.symm hsk'_wv.symm hsk'_ws.symm
  have hdw_g := commit_dense_reloc (k' := sg_base.core) hdw_w' hlay_g hsk'_cv.symm hsub_g
    fun _ _ => ⟨by simp [sg_base, sg, fullWatchSizeCore, hsk'_wv], fun _ _ => by
      simp [sg_base, sg, fullWatchOffCore, hsk'_wv, hsk'_ws]⟩
  have hmw_g : ModeWatchesInv F_cur sg_base.core := by
    unfold ModeWatchesInv
    simpa [sg_base, sg, ite_eq_right (fun h0 => hdwp.2.2.2.2.2.2 h0)] using hdw_g
  exact fullDenseInvW_with_wsort
    (fullDenseInvW_addGarbageClause hdwp hlok_base hsz_ge3 harg_pre harg_8m harg_512k
      harg_sz hmw_g) hwsort_len

private theorem commit_watch_done_dw {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {sp scp sk : FullState} {sz : BitVec 32}
    {wv' ws' wsort' : List (BitVec 32)} {wlen' : Nat} {wu' : BitVec 64}
    (hdwp : FullDenseInvW c F0 F_cur sp)
    (hlok_w : sk.LengthsOk c) (hdw_w : DenseWatchesInv F_cur sk.core)
    (hrefs_cp : fullArenaClauseRefsCore scp.core =
      fullArenaClauseRefsCore sp.core ++ [sp.core.arena_len])
    (hsk_ar : sk.core.arena = scp.core.arena) (hsk_alen : sk.core.arena_len = scp.core.arena_len)
    (hsk_cv : sk.core.cur_vars = sp.core.cur_vars)
    (hsk_wl : sk.core.wlen = wlen') (hsk_wv : sk.core.wvec = wv') (hsk_ws : sk.core.wstk = ws')
    (hscp_al : scp.core.arena_len = sp.core.arena_len + 3 + sz.toNat)
    (hsz_ge3 : 3 ≤ sz.toNat) (hflc_len : scp.core.flags.length = c.max_vars)
    (harc_len : scp.core.arena.length = c.arena_cap)
    (harc_pre : ∀ i < sp.core.arena_len, scp.core.arena[i]? = sp.core.arena[i]?)
    (harc_8m : scp.core.arena[sp.core.arena_len]?.getD 0#32 &&& 8388608#32 = 0#32)
    (harc_sz : (scp.core.arena[sp.core.arena_len + 2]?.getD 0#32).toNat = sz.toNat)
    (hlits_cp : ∀ l ∈ fullArenaClauseLitsCore scp.core sp.core.arena_len,
      l < 2 * sp.core.cur_vars)
    (hnodup_cp : (List.map (fun x => x / 2)
      (fullArenaClauseLitsCore scp.core sp.core.arena_len)).Nodup)
    (hent_cp : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (fullArenaClauseLitsCore scp.core sp.core.arena_len)))
    (hwsort_len : wsort'.length = 2 * c.max_vars) :
    let sf : FullState :=
      { core := { sp.core with
          arena_len := sp.core.arena_len + 3 + sz.toNat, wlen := wlen', wusable := wu',
          num_irred := sp.core.num_irred + 1#64, flags := scp.core.flags, wvec := wv',
          arena := scp.core.arena, wstk := ws' }
        scratch := { sp.scratch with wsort := wsort' } }
    FullDenseInvW c F0 F_cur sf := by
  intro sf
  let sf_base : FullState := { core := sf.core, scratch := sp.scratch }
  have hlok_base : sf_base.LengthsOk c :=
    ⟨commit_core_lengths_ok hdwp.1.core_ok rfl rfl rfl hflc_len rfl rfl rfl rfl rfl rfl rfl rfl
      (by dsimp only [sf_base, sf]; rw [← hsk_wv]; exact hlok_w.core_ok.wvec_len) rfl rfl
      harc_len (by dsimp only [sf_base, sf]; rw [← hsk_ws]; exact hlok_w.core_ok.wstk_len_arr)
      rfl
      (by
        dsimp only [sf_base, sf]; rw [← hscp_al, ← hsk_alen]
        exact hlok_w.core_ok.arena_len_le)
      (by dsimp only [sf_base, sf]; rw [← hsk_wl]; exact hlok_w.core_ok.wlen_le)
      rfl rfl rfl rfl,
     hdwp.1.scratch_ok⟩
  have hsub_f : ∀ r ∈ fullArenaClauseRefsCore sk.core,
      r ∈ fullArenaClauseRefsCore sf_base.core := by
    intro r hr
    have h1 := fullArenaClauseRefsCore_append (k' := sf_base.core) hdwp.2.1.arena hsz_ge3 rfl
      harc_pre harc_8m harc_sz
    have h2 : fullArenaClauseRefsCore sk.core = fullArenaClauseRefsCore scp.core := by
      unfold fullArenaClauseRefsCore; simp [hsk_ar, hsk_alen]
    rw [h1, ← hrefs_cp, ← h2]; exact hr
  have hlay_f := commit_lay_core_congr (k2 := sf_base.core) hdw_w.layout hsk_cv.symm
    hsk_wl.symm hsk_wv.symm hsk_ws.symm
  have hdw_f := commit_dense_reloc (k' := sf_base.core) hdw_w hlay_f hsk_cv.symm hsub_f
    fun _ _ => ⟨by simp [sf_base, sf, fullWatchSizeCore, hsk_wv], fun _ _ => by
      simp [sf_base, sf, fullWatchOffCore, hsk_wv, hsk_ws]⟩
  have hmw_f : ModeWatchesInv F_cur sf_base.core := by
    unfold ModeWatchesInv
    simpa [sf_base, sf, ite_eq_right (fun h0 => hdwp.2.2.2.2.2.2 h0)] using hdw_f
  exact fullDenseInvW_with_wsort
    (fullDenseInvW_addEntailedClause hdwp hlok_base hsz_ge3 hlits_cp hnodup_cp hent_cp
      harc_pre harc_8m harc_sz hmw_f) hwsort_len

private theorem commit_watch_false_dw {F_cur : List (List Nat)} {sk sk' : FullState}
    {lit : BitVec 32}
    (hdw_w : DenseWatchesInv F_cur sk.core) (hlay_w' : WatchStackLayout sk'.core)
    (hcv : sk'.core.cur_vars = sk.core.cur_vars)
    (har : sk'.core.arena = sk.core.arena) (halen : sk'.core.arena_len = sk.core.arena_len)
    (hother_w : ∀ l < 2 * sk.core.cur_vars, l ≠ lit.toNat →
      fullWatchSize sk' l = fullWatchSize sk l ∧
        ∀ k < fullWatchSize sk l,
          sk'.core.wstk[fullWatchOff sk' l + k]? = sk.core.wstk[fullWatchOff sk l + k]?)
    (hsame_lit : lit.toNat < 2 * sk.core.cur_vars →
      fullWatchSize sk' lit.toNat = fullWatchSize sk lit.toNat ∧
        ∀ k < fullWatchSize sk lit.toNat,
          sk'.core.wstk[fullWatchOff sk' lit.toNat + k]? =
            sk.core.wstk[fullWatchOff sk lit.toNat + k]?) :
    DenseWatchesInv F_cur sk'.core :=
  commit_dense_reloc (k' := sk'.core) hdw_w hlay_w' hcv
    (fun r hr => by
      have h : fullArenaClauseRefsCore sk'.core = fullArenaClauseRefsCore sk.core := by
        unfold fullArenaClauseRefsCore; simp [har, halen]
      rwa [h])
    fun l hl => by
      by_cases hne : l = lit.toNat
      · subst hne; exact hsame_lit hl
      · exact hother_w l hl hne

private theorem commit_lit_var_lt {buf : List (BitVec 32)} {idx v max_v : Nat}
    (hidx : idx < buf.length) (hb : (buf[idx]?.getD 0#32).toNat < 2 * v) (hv : v ≤ max_v) :
    ((buf[idx]'hidx >>> 1#32).setWidth 64).toNat < max_v := by
  rw [List.getElem?_eq_getElem hidx, Option.getD_some] at hb
  rw [elim_zext32_toNat]
  have : (buf[idx]'hidx >>> 1#32).toNat = (buf[idx]'hidx).toNat / 2 := by
    simp [Nat.shiftRight_eq_div_pow]
  omega

/-! ## 1. `full_bve_commit_res_wp` -/

public theorem full_bve_commit_res_wp (Γ : Env)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X)
    (hAllocCl : ∀ a m Q X, fullAllocClSpec a m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] a m Q X)
    (hWatchPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, Spec.fullBveCommitResTmkSpec a m Q X →
      Func.wp Γ full_bve_commit_res_body a m Q X := by
  rintro ⟨h, r_off, r_end, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s0, R, rfl, hdw0, htmk0, hoff_le, hend_le, hrb0, hm0, hQ⟩
  have hmx := c.hmaxv; have harc := c.harena; have hsc := c.hscr
  unfold dimacsBound at hmx harc hsc
  unfold Func.wp full_bve_commit_res_body
  elim_steps_nogrp
  refine wp_loop_group (ts := [i64]) (CommitLoopInv c F0 F_cur s0 r_off r_end R) ?_ ?_
  · rintro L rem ⟨rp, ⟨⟩⟩ mp hL ⟨sp, hdwp, htmkt, hcvp, hflp, hrp0, hrpe, hrem, hrbp, hmp⟩
    elim_steps_nogrp
    · have hrp_lt : rp.toNat < r_end.toNat := hc
      have hrp_sc : rp.toNat < sp.scratch.scratch_buf.length := by
        rw [hdwp.1.scratch_ok.scratch_buf_len]; omega
      generalize hpn : rp.toNat = p_n at hrbp
      cases hrbp with
      | nil => exact absurd hrp_lt (hpn ▸ Nat.lt_irrefl _)
      | @cons _ sz_n hsz_end hsz_get hlits_bd hnodup hent hrb_nxt =>
        let sz := sp.scratch.scratch_buf[rp.toNat]'hrp_sc
        have hsz_eq : sz.toNat = sz_n := by
          rw [← hpn] at hsz_get
          dsimp only [sz]
          rw [List.getElem?_eq_getElem hrp_sc, Option.getD_some] at hsz_get
          exact hsz_get
        have hsz_lt_sc : sz.toNat ≤ c.scratch_cap := by omega
        elim_steps_nogrp
        · have hsz0 : sz.toNat = 0 := by
            have := congrArg BitVec.toNat hc; dsimp only [sz]; exact this
          have hunsat_cur : (cnfOfClauses F_cur).Unsat := commit_empty_unsat (by
            have h0 : sz_n = 0 := by rw [← hsz_eq, hsz0]
            subst h0; exact hent)
          elim_steps!
          let s_inc : FullState := { sp with core := { sp.core with inconsistent := 1#64 } }
          have hdw_inc := fullDenseInvW_with_inconsistent hdwp 1#64 (fun _ => hunsat_cur)
          have htmk_inc : TmkZero s_inc := tmkZero_congr htmkt rfl rfl
          exact hQ 20#64 s_inc m hdw_inc htmk_inc hcvp hflp (Or.inr (Or.inr rfl))
            (fun _ => hdw_inc.2.1.ext_sound.2 hunsat_cur) hm
        · have hsz_nz : sz.toNat ≠ 0 := fun h0 => hc (BitVec.eq_of_toNat_eq h0)
          have hsz_ge1 : 1 ≤ sz.toNat := Nat.pos_of_ne_zero hsz_nz
          have hrp_nxt_lt : rp.toNat + 1 + sz.toNat ≤ r_end.toNat := by
            rw [hsz_eq, hpn]; exact hsz_end
          have hrpn_eq : (rp + 1#64 + sz.setWidth 64).toNat = rp.toNat + 1 + sz.toNat := by
            rw [BitVec.toNat_add, BitVec.toNat_add, elim_zext32_toNat,
              show (1#64 : BitVec 64).toNat = 1 from rfl]
            rw [Nat.mod_eq_of_lt (by omega : rp.toNat + 1 < 2 ^ 64)]
            exact Nat.mod_eq_of_lt (by omega)
          refine wp_join0 (CommitStepInv c F0 F_cur sp R) ?_ ?_
          · intro Jnext m' hm'; elim_steps!
            obtain ⟨s', hdw', htmk', hcv', hfl', hscr', hm'⟩ := hm'
            let rp' := rp + 1#64 + sz.setWidth 64
            have hrp'_eq : rp'.toNat = rp.toNat + 1 + sz.toNat := hrpn_eq
            have hrb' : FullResBufOkW F_cur s' r_end.toNat rp'.toNat := by
              rw [hrp'_eq, hsz_eq, hpn]
              exact commit_resBufOk_congr hscr' hcv' hrb_nxt
            exact hL (r_end.toNat - rp'.toNat) (rp', ()) m' (by rw [hrp'_eq]; omega)
              ⟨s', hdw', htmk', hcv'.trans hcvp, hfl'.trans hflp, by rw [hrp'_eq]; omega,
               by rw [hrp'_eq]; omega, rfl, hrb', hm'⟩
          · intro Jnext hJnext
            elim_steps_nogrp
            · have hsz1 : sz.toNat = 1 := by
                have := congrArg BitVec.toNat hc; dsimp only [sz]; exact this
              have hrp1_eq : (rp + 1#64).toNat = rp.toNat + 1 := by
                rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl]
                exact Nat.mod_eq_of_lt (by omega)
              have hrp1_sc : (rp + 1#64).toNat < sp.scratch.scratch_buf.length := by
                rw [hdwp.1.scratch_ok.scratch_buf_len]; omega
              let l0 := sp.scratch.scratch_buf[(rp + 1#64).toNat]'hrp1_sc
              have hl0_lt : l0.toNat < 2 * sp.core.cur_vars := by
                have hb := hlits_bd 0 (by omega)
                have hrp_sc1 : rp.toNat + 1 + 0 < sp.scratch.scratch_buf.length := by omega
                rw [← hpn] at hb
                rw [List.getElem?_eq_getElem hrp_sc1, Option.getD_some] at hb
                simpa [l0, hrp1_eq] using hb
              have hl0_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause [l0.toNat]) := by
                have hsz1n : sz_n = 1 := by rw [← hsz_eq, hsz1]
                have hrp_sc1 : rp.toNat + 1 + 0 < sp.scratch.scratch_buf.length := by omega
                subst hsz1n
                rw [← hpn] at hent
                rw [show List.range 1 = [0] from rfl, List.map_cons, List.map_nil,
                  List.getElem?_eq_getElem hrp_sc1, Option.getD_some] at hent
                simpa [l0, hrp1_eq] using hent
              elim_steps_nogrp
              elim_call hAddUnit
              refine ⟨c, F0, F_cur, sp, R, rfl, hdwp.1, hdwp.2.1, fun _ => hl0_ent, hmp, ?_⟩
              intro ok vals' fl' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
                ph' ta' ba' pt' pb' hp' ps' hl' qsi' qss' m' _s' hlok' hwi' hcl0 huns_lt _ hm'
              let s' : FullState :=
                { core := { sp.core with
                    unassigned := unass', unflushed := unfl', trail_end := te',
                    propagated := prop', cur_level := cl', inconsistent := inc',
                    vals := vals', flags := fl', lvl := lvl', rsns := rsns', trl := trl',
                    trail_pos := tp' }
                  scratch := { sp.scratch with
                    heap_len := hl', q_search_idx := qsi', q_search_stamp := qss',
                    target_assigned := ta', best_assigned := ba', phases := ph',
                    phases_target := pt', phases_best := pb', heap := hp', pos := ps' } }
              have hdw' := fullDenseInvW_of_addUnit hdwp hlok' hwi' ⟨rfl, rfl⟩ hcl0
              have htmk' : TmkZero s' := tmkZero_congr htmkt rfl rfl
              elim_steps_nogrp
              · exact hJnext m' ⟨s', hdw', htmk', rfl, rfl, rfl, hm'⟩
              · have hokf : ok = false := by cases ok <;> simp at hc ⊢
                have huns := (huns_lt hl0_lt hokf).1
                exact hQ 20#64 s' m' hdw' htmk' hcvp hflp (Or.inr (Or.inr rfl)) (fun _ => huns) hm'
            · have hsz_ne1 : sz.toNat ≠ 1 := fun h1 => hc (BitVec.eq_of_toNat_eq h1)
              have hsz_ge2 : 2 ≤ sz.toNat := by omega
              refine wp_join0 (CommitStepInv c F0 F_cur sp R) ?_ ?_
              · intro J27 m' hm'; elim_steps!; exact hJnext m' hm'
              · intro J27 hJ27
                elim_steps_nogrp
                · have hsz2 : sz.toNat = 2 := by
                    have := congrArg BitVec.toNat hc; dsimp only [sz]; exact this
                  have hrp1_eq : (rp + 1#64).toNat = rp.toNat + 1 := by
                    rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl]
                    exact Nat.mod_eq_of_lt (by omega)
                  have hrp2_eq : (rp + 1#64 + 1#64).toNat = rp.toNat + 2 := by
                    rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, hrp1_eq]
                    exact Nat.mod_eq_of_lt (by omega)
                  have hrp1_sc : (rp + 1#64).toNat < sp.scratch.scratch_buf.length := by
                    rw [hdwp.1.scratch_ok.scratch_buf_len]; omega
                  have hrp2_sc : (rp + 1#64 + 1#64).toNat < sp.scratch.scratch_buf.length := by
                    rw [hdwp.1.scratch_ok.scratch_buf_len]; omega
                  let l0 := sp.scratch.scratch_buf[(rp + 1#64).toNat]'hrp1_sc
                  let l1 := sp.scratch.scratch_buf[(rp + 1#64 + 1#64).toNat]'hrp2_sc
                  have hent2 : (cnfOfClauses F_cur).EntailsClause
                      (cnfClause [l0.toNat, l1.toNat]) := by
                    have hsz2n : sz_n = 2 := by rw [← hsz_eq, hsz2]
                    have hrp_sc1 : rp.toNat + 1 + 0 < sp.scratch.scratch_buf.length := by omega
                    have hrp_sc2 : rp.toNat + 1 + 1 < sp.scratch.scratch_buf.length := by omega
                    subst hsz2n
                    rw [← hpn] at hent
                    rw [show List.range 2 = [0, 1] from rfl, List.map_cons, List.map_cons,
                      List.map_nil, List.getElem?_eq_getElem hrp_sc1,
                      List.getElem?_eq_getElem hrp_sc2, Option.getD_some, Option.getD_some] at hent
                    simpa [l0, l1, hrp1_eq, hrp2_eq] using hent
                  elim_steps_nogrp
                  elim_call hAddBin
                  refine ⟨c, F0, F_cur, sp, R, rfl, hdwp.1, hdwp.2.1, hdwp.2.2.2.2.2.1,
                    fun _ _ => hent2, hmp, ?_⟩
                  intro r vals' fl' lvl' rsns' trl' tp' te' unass' unfl' wv' ws' wl' wu' nb'
                    oom' inc' ph' wsort' m' _s' hlok' hwi' hr_cases huns20 _ hm'
                  let s' : FullState :=
                    { core := { sp.core with
                        unassigned := unass', wlen := wl', wusable := wu', num_binary := nb',
                        unflushed := unfl', trail_end := te', oom := oom', inconsistent := inc',
                        vals := vals', flags := fl', lvl := lvl', rsns := rsns', trl := trl',
                        trail_pos := tp', wvec := wv', wstk := ws' }
                      scratch := { sp.scratch with phases := ph', wsort := wsort' } }
                  have hdw' := fullDenseInvW_of_addBin hdwp hlok' hwi'
                  have htmk' : TmkZero s' := tmkZero_congr htmkt rfl rfl
                  elim_steps_nogrp
                  · exact hQ 20#64 s' m' hdw' htmk' hcvp hflp (Or.inr (Or.inr rfl))
                      (fun _ => (huns20 hc).1) hm'
                  · exact hQ 2#64 s' m' hdw' htmk' hcvp hflp (Or.inr (Or.inl rfl))
                      (fun h => absurd h (by decide)) hm'
                  · refine wp_join0 (CommitStepInv c F0 F_cur sp R) ?_ ?_
                    · intro J42 m1 hm1
                      obtain ⟨s1, hdw1, htmk1, hcv1, hfl1, hscr1, hm1⟩ := hm1
                      refine wp_join0 (CommitStepInv c F0 F_cur sp R) ?_ ?_
                      · intro J44 m2 hm2; elim_steps!; exact hJ27 m2 hm2
                      · intro J44 hJ44
                        have hv1_ar :
                            ((l1 >>> 1#32).setWidth 64).toNat < s1.core.flags.length := by
                          rw [hdw1.1.core_ok.flags_len]
                          exact commit_lit_var_lt hrp2_sc
                            (by rw [hrp2_eq, hpn]; exact hlits_bd 1 (by omega))
                            hdwp.1.core_ok.cur_vars_le
                        elim_steps_nogrp
                        · refine wp_join_group (ts := [i32]) (fun _ mx => mx = m1) ?_ ?_
                          · intro J58 ⟨b, ⟨⟩⟩ mx rfl; elim_steps!
                            let fl'' := s1.core.flags.set ((l1 >>> 1#32).setWidth 64).toNat
                              ((s1.core.flags[((l1 >>> 1#32).setWidth 64).toNat] ||| 8#32 |||
                                16#32) ||| b)
                            let s2 : FullState :=
                              { s1 with core := { s1.core with flags := fl'' } }
                            have hfl''_len : fl''.length = c.max_vars := by
                              dsimp only [fl'']; rw [List.length_set]
                              exact hdw1.1.core_ok.flags_len
                            have hdw2 := fullDenseInvW_with_flags_unassigned hdw1
                              hfl''_len s1.core.unassigned
                            have htmk2 : TmkZero s2 := tmkZero_congr htmk1 rfl rfl
                            exact hJ44 m ⟨s2, hdw2, htmk2, hcv1, hfl1, hscr1, hm⟩
                          · intro J58 hJ58; elim_steps_nogrp
                            · exact hJ58 (64#32, ()) m1 rfl
                            · exact hJ58 (32#32, ()) m1 rfl
                        · elim_steps!
                          exact hJ44 m1 ⟨s1, hdw1, htmk1, hcv1, hfl1, hscr1, hm1⟩
                    · intro J42 hJ42
                      have hv0_ar :
                          ((l0 >>> 1#32).setWidth 64).toNat < s'.core.flags.length := by
                        rw [hdw'.1.core_ok.flags_len]
                        exact commit_lit_var_lt hrp1_sc
                          (by rw [hrp1_eq, hpn]; exact hlits_bd 0 (by omega))
                          hdwp.1.core_ok.cur_vars_le
                      elim_steps_nogrp
                      · refine wp_join_group (ts := [i32]) (fun _ mx => mx = m') ?_ ?_
                        · intro J74 ⟨b, ⟨⟩⟩ mx rfl; elim_steps!
                          let fl'' := s'.core.flags.set ((l0 >>> 1#32).setWidth 64).toNat
                            ((s'.core.flags[((l0 >>> 1#32).setWidth 64).toNat] ||| 8#32 |||
                              16#32) ||| b)
                          let s1 : FullState :=
                            { s' with core := { s'.core with flags := fl'' } }
                          have hfl''_len : fl''.length = c.max_vars := by
                            dsimp only [fl'']; rw [List.length_set]; exact hdw'.1.core_ok.flags_len
                          have hdw1 := fullDenseInvW_with_flags_unassigned hdw'
                            hfl''_len s'.core.unassigned
                          have htmk1 : TmkZero s1 := tmkZero_congr htmk' rfl rfl
                          exact hJ42 m ⟨s1, hdw1, htmk1, rfl, rfl, rfl, hm⟩
                        · intro J74 hJ74; elim_steps_nogrp
                          · exact hJ74 (64#32, ()) m' rfl
                          · exact hJ74 (32#32, ()) m' rfl
                      · elim_steps!
                        exact hJ42 m' ⟨s', hdw', htmk', rfl, rfl, rfl, hm'⟩
                · have hsz_ne2 : sz.toNat ≠ 2 := fun h2 => hc (BitVec.eq_of_toNat_eq h2)
                  have hsz_ge3 : 3 ≤ sz.toNat := by omega
                  elim_steps_nogrp
                  elim_call hAllocCl
                  refine ⟨c, sp, R, rfl, hdwp.1, hmp, ?_⟩
                  change if c.arena_cap - sp.core.arena_len < 3 + sz.toNat then _ else _
                  by_cases hoom_cl : c.arena_cap - sp.core.arena_len < 3 + sz.toNat
                  · simp only [hoom_cl, ↓reduceIte]
                    elim_steps!
                    let s_oom : FullState := { sp with core := { sp.core with oom := 1#64 } }
                    have hdw_oom := fullDenseInvW_with_oom hdwp 1#64
                    have htmk_oom : TmkZero s_oom := tmkZero_congr htmkt rfl rfl
                    exact hQ 2#64 s_oom m hdw_oom htmk_oom hcvp hflp (Or.inr (Or.inl rfl))
                      (fun h => absurd h (by decide)) hm
                  · simp only [hoom_cl, ↓reduceIte]
                    intro arena1 m1 hlok1 har1_pre har1_8m har1_512k _ har1_sz hm1
                    let cr := BitVec.ofNat 64 sp.core.arena_len
                    have hal_le : sp.core.arena_len ≤ c.arena_cap := hdwp.1.core_ok.arena_len_le
                    have har_fit : sp.core.arena_len + 3 + sz.toNat ≤ c.arena_cap := by omega
                    have hcr_eq : cr.toNat = sp.core.arena_len := Nat.mod_eq_of_lt (by omega)
                    have hcr_ar : cr.toNat < arena1.length := by
                      rw [hlok1.core_ok.arena_len_arr]; omega
                    let s1 : FullState :=
                      { sp with core := { sp.core with
                          arena_len := sp.core.arena_len + 3 + sz.toNat, arena := arena1 } }
                    elim_steps!
                    let w0 := arena1[cr.toNat]'hcr_ar
                    let arena_i := arena1.set cr.toNat (w0 ||| 16777216#32)
                    obtain ⟨hari_len, hari_pre, hari_8m, hari_512k, hari_sz⟩ :=
                      commit_alloc_init_ok hcr_eq hcr_ar hlok1.core_ok.arena_len_arr har1_pre
                        har1_8m har1_512k har1_sz
                    refine wp_loop_group (ts := [i32])
                      (CommitCopyInv c s1 sp.core.arena sp.core.arena_len rp.toNat sz R) ?_ ?_
                    · rintro Lc remc ⟨kc, ⟨⟩⟩ mc hLc
                        ⟨arc, flc, hkc_le, hremc, harc_len, hflc_len, harc_pre, harc_8m,
                         harc_512k, harc_sz, hcopy, hmc⟩
                      elim_steps_nogrp
                      · have hkc_lt : kc.toNat < sz.toNat := hc
                        have hsz_ub : sz.toNat ≤ c.scratch_cap := hsz_lt_sc
                        have : rp.toNat + 1 + sz.toNat ≤ c.scratch_cap := by omega
                        have hsrc_sc : (rp + 1#64 + kc.setWidth 64).toNat <
                            s1.scratch.scratch_buf.length := by
                          rw [hlok1.scratch_ok.scratch_buf_len]
                          rw [BitVec.toNat_add, BitVec.toNat_add, elim_zext32_toNat,
                            show (1#64 : BitVec 64).toNat = 1 from rfl]
                          rw [Nat.mod_eq_of_lt (by omega : rp.toNat + 1 < 2 ^ 64)]
                          rw [Nat.mod_eq_of_lt (by omega)]; omega
                        let lk := s1.scratch.scratch_buf[(rp + 1#64 + kc.setWidth 64).toNat]'hsrc_sc
                        let arc' := arc.set (cr + 3#64 + kc.setWidth 64).toNat lk
                        obtain ⟨_, hkc1_eq, harc'_len, harc'_pre, harc'_8m, harc'_512k,
                          harc'_sz, hcopy'⟩ := commit_copy_step_ok rfl hcr_eq harc_len har_fit
                            harc hkc_lt (by omega) (by omega) hsc harc_pre harc_8m harc_512k
                            harc_sz hcopy hsrc_sc rfl
                        elim_steps_nogrp
                        let sc1 : FullState :=
                          { s1 with core := { s1.core with arena := arc', flags := flc } }
                        refine wp_join0 (fun m_next =>
                          ∃ fl_next : List (BitVec 32), fl_next.length = c.max_vars ∧
                            (FullMem c { sc1 with core := { sc1.core with flags := fl_next } } ⋆
                              R) m_next) ?_ ?_
                        · intro J103 m_next ⟨fl_next, hfl_next, hm_next⟩
                          elim_steps!
                          exact hLc (sz.toNat - (kc + 1#32).toNat) (kc + 1#32, ()) m_next
                            (by omega) ⟨arc', fl_next, by omega, rfl, harc'_len, hfl_next,
                              harc'_pre, harc'_8m, harc'_512k, harc'_sz, hcopy', hm_next⟩
                        · intro J103 hJ103
                          have hvk_ar : ((lk >>> 1#32).setWidth 64).toNat < flc.length := by
                            rw [hflc_len]
                            have hsrc_eq : (rp + 1#64 + kc.setWidth 64).toNat =
                                rp.toNat + 1 + kc.toNat := by
                              rw [BitVec.toNat_add, BitVec.toNat_add, elim_zext32_toNat,
                                show (1#64 : BitVec 64).toNat = 1 from rfl]
                              rw [Nat.mod_eq_of_lt (by omega : rp.toNat + 1 < 2 ^ 64)]
                              exact Nat.mod_eq_of_lt (by omega)
                            exact commit_lit_var_lt hsrc_sc
                              (by rw [hsrc_eq, hpn]; exact hlits_bd kc.toNat (by omega))
                              hdwp.1.core_ok.cur_vars_le
                          elim_steps_nogrp
                          · refine wp_join_group (ts := [i32]) (fun _ mx => mx = m) ?_ ?_
                            · intro J118 ⟨b, ⟨⟩⟩ mx rfl; elim_steps!
                              let fl'' := flc.set ((lk >>> 1#32).setWidth 64).toNat
                                ((flc[((lk >>> 1#32).setWidth 64).toNat] ||| 8#32 ||| 16#32) ||| b)
                              exact hJ103 m ⟨fl'', by simp [fl'', hflc_len], hm⟩
                            · intro J118 hJ118; elim_steps_nogrp
                              · exact hJ118 (64#32, ()) m rfl
                              · exact hJ118 (32#32, ()) m rfl
                          · elim_steps!; exact hJ103 m ⟨flc, hflc_len, hm⟩
                      · have hkc_ge : sz.toNat ≤ kc.toNat := by dsimp only [sz] at hc ⊢; omega
                        have hkc_eq : kc.toNat = sz.toNat := by omega
                        have hcopy_all : ∀ i < sz.toNat,
                            arc[sp.core.arena_len + 3 + i]? =
                              sp.scratch.scratch_buf[rp.toNat + 1 + i]? :=
                          fun i hi => hcopy i (hkc_eq ▸ hi)
                        let scp : FullState :=
                          { s1 with core := { s1.core with arena := arc, flags := flc } }
                        have hlok_cp : scp.LengthsOk c :=
                          ⟨commit_core_lengths_ok hlok1.core_ok rfl rfl rfl hflc_len rfl rfl rfl
                            rfl rfl rfl rfl rfl hlok1.core_ok.wvec_len rfl rfl harc_len
                            hlok1.core_ok.wstk_len_arr rfl hlok1.core_ok.arena_len_le
                            hlok1.core_ok.wlen_le rfl rfl rfl rfl,
                           hlok1.scratch_ok⟩
                        obtain ⟨hrefs_cp, hdw_cp, hlits_cp, hnodup_cp, hent_cp⟩ :=
                          commit_post_copy_ok hdwp hlok_cp rfl rfl rfl rfl rfl hsz_eq hsz_ge3
                            har_fit harc_pre harc_8m harc_sz hcopy_all
                            (fun k hk => by rw [hpn]; exact hlits_bd k hk)
                            (by rw [hpn]; exact hnodup)
                            (by rw [hpn]; exact hent)
                        have hsz31 := commit_sz31_props hsz_ge3 (by omega)
                        have hcr32 : (cr.setWidth 32) ≠ 0xFFFFFFFF#32 := by
                          intro h; have h1 := congrArg BitVec.toNat h
                          rw [BitVec.toNat_setWidth, hcr_eq, Nat.mod_eq_of_lt (by omega)] at h1
                          rw [show (0xFFFFFFFF#32 : BitVec 32).toNat = 0xFFFFFFFF from rfl] at h1
                          omega
                        have hcr32_lt : (cr.setWidth 32).toNat < 0x80000000 := by
                          rw [BitVec.toNat_setWidth, hcr_eq, Nat.mod_eq_of_lt (by omega)]; omega
                        elim_steps_nogrp
                        refine wp_loop_group (ts := [i32]) (CommitWatchInv c F_cur scp sz R) ?_ ?_
                        · rintro Lw remw ⟨kw, ⟨⟩⟩ mw hLw
                            ⟨wv', ws', wlen', wu', wsort', hkw_le, hremw, hlok_w, hdw_w, hmw⟩
                          let sk : FullState :=
                            { core := { scp.core with
                                wlen := wlen', wusable := wu', wvec := wv', wstk := ws' }
                              scratch := { scp.scratch with wsort := wsort' } }
                          elim_steps_nogrp
                          · have hkw_lt : kw.toNat < sz.toNat := hc
                            have hidx_eq : (cr + 3#64 + kw.setWidth 64).toNat =
                                sp.core.arena_len + 3 + kw.toNat := by
                              rw [BitVec.toNat_add, BitVec.toNat_add, elim_zext32_toNat, hcr_eq,
                                show (3#64 : BitVec 64).toNat = 3 from rfl]
                              rw [Nat.mod_eq_of_lt (by omega : sp.core.arena_len + 3 < 2 ^ 64)]
                              exact Nat.mod_eq_of_lt (by omega)
                            have hidx_ar : (cr + 3#64 + kw.setWidth 64).toNat <
                                sk.core.arena.length := by
                              rw [hlok_w.core_ok.arena_len_arr]; omega
                            let lit := sk.core.arena[(cr + 3#64 + kw.setWidth 64).toNat]'hidx_ar
                            have hlit_lt : lit.toNat < 2 * sp.core.cur_vars := by
                              have hc_ar := hcopy_all kw.toNat hkw_lt
                              have hget : lit =
                                  sk.core.arena[sp.core.arena_len + 3 + kw.toNat]?.getD 0#32 := by
                                simp only [lit, hidx_eq]
                                rw [List.getElem?_eq_getElem
                                  (by rw [hlok_w.core_ok.arena_len_arr]; omega), Option.getD_some]
                              rw [hget]
                              have hsame_ar : sk.core.arena = arc := rfl
                              rw [hsame_ar, hc_ar, hpn]
                              exact hlits_bd kw.toNat (by omega)
                            elim_steps_nogrp
                            elim_call hWatchPush
                            refine ⟨c, sk, R, rfl, hlok_w, hdw_w.layout,
                              fun h => absurd h (by decide),
                              fun _ => ⟨hsz31.2.1, hcr32⟩, hmw, ?_⟩
                            intro ok wv'' ws'' wlen'' wu'' wsort'' mw' sk' hlok_w' hlay_w'
                              hother_w hok_t hok_f hmw'
                            have hcr_ar' : cr.toNat < sk'.core.arena.length := by
                              rw [show sk'.core.arena = arc from rfl, harc_len]; omega
                            elim_steps_nogrp
                            · have hrefs_eq : ∀ r ∈ fullArenaClauseRefsCore sk.core,
                                  r ∈ fullArenaClauseRefsCore sk'.core := fun _ h => h
                              have hcr_ref : (cr.setWidth 32).toNat ∈
                                  fullArenaClauseRefsCore sk'.core := by
                                rw [BitVec.toNat_setWidth, hcr_eq, Nat.mod_eq_of_lt (by omega)]
                                have hsame : fullArenaClauseRefsCore sk'.core =
                                    fullArenaClauseRefsCore scp.core := rfl
                                rw [hsame, hrefs_cp]
                                exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
                              obtain ⟨_, _, hsz_p, hkeep_p, hw0_p, hw1_p⟩ := hok_t hc
                              dsimp only at hsz_p hkeep_p hw0_p hw1_p
                              have hdw_w' : DenseWatchesInv F_cur sk'.core :=
                                commit_dense_push_occ hdw_w hlay_w' hlit_lt rfl hrefs_eq
                                  hother_w hsz_p hkeep_p hw0_p (hw1_p rfl) hsz31.2.2.1 hsz31.2.2.2
                                  hcr32_lt hcr_ref
                              have hkw1_eq : (kw + 1#32).toNat = kw.toNat + 1 := by
                                rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl]
                                exact Nat.mod_eq_of_lt (by omega)
                              exact hLw (sz.toNat - (kw + 1#32).toNat) (kw + 1#32, ()) mw'
                                (by omega) ⟨wv'', ws'', wlen'', wu'', wsort'', by omega, rfl,
                                  hlok_w', hdw_w', hmw'⟩
                            · have hokf : ok = false := by cases ok <;> simp at hc ⊢
                              have hdw_w' := commit_watch_false_dw hdw_w hlay_w' rfl rfl rfl
                                hother_w (hok_f hokf).1
                              let wg := sk'.core.arena[cr.toNat]'hcr_ar'
                              let ar_g := sk'.core.arena.set cr.toNat (wg ||| 524288#32)
                              let ag' := sk'.core.arena_garbage + 3#64 + sz.setWidth 64
                              let sg : FullState :=
                                { core := { sp.core with
                                    arena_len := sp.core.arena_len + 3 + sz.toNat, wlen := wlen'',
                                    wusable := wu'', arena_garbage := ag', oom := 1#64,
                                    flags := flc, wvec := wv'', arena := ar_g, wstk := ws'' }
                                  scratch := { sp.scratch with wsort := wsort'' } }
                              have hdw_g := commit_watch_oom_dw (wu'' := wu'') hdwp hlok_w' hdw_w'
                                hrefs_cp rfl rfl rfl rfl rfl rfl rfl hcr_eq hcr_ar' hsz_ge3
                                hflc_len harc_pre harc_8m harc_sz hlok_w'.scratch_ok.wsort_len
                              have htmk_g : TmkZero sg := tmkZero_congr htmkt rfl rfl
                              elim_steps!
                              exact hQ 2#64 sg m hdw_g htmk_g hcvp hflp (Or.inr (Or.inl rfl))
                                (fun h => absurd h (by decide)) hm
                          · elim_steps!
                            let sf : FullState :=
                              { core := { sp.core with
                                  arena_len := sp.core.arena_len + 3 + sz.toNat, wlen := wlen',
                                  wusable := wu', num_irred := sp.core.num_irred + 1#64,
                                  flags := flc, wvec := wv', arena := arc, wstk := ws' }
                                scratch := { sp.scratch with wsort := wsort' } }
                            have hdw_f := commit_watch_done_dw (wu' := wu') hdwp hlok_w hdw_w
                              hrefs_cp rfl rfl rfl rfl rfl rfl rfl hsz_ge3 hflc_len harc_len
                              harc_pre harc_8m harc_sz hlits_cp hnodup_cp hent_cp
                              hlok_w.scratch_ok.wsort_len
                            have htmk_f : TmkZero sf := tmkZero_congr htmkt rfl rfl
                            exact hJ27 m ⟨sf, hdw_f, htmk_f, rfl, rfl, rfl, hm⟩
                        · intro Lw hLw; elim_steps!
                          exact hLw sz.toNat (0#32, ()) mc
                            ⟨scp.core.wvec, scp.core.wstk, scp.core.wlen, scp.core.wusable,
                             scp.scratch.wsort, Nat.zero_le _, rfl, hlok_cp, hdw_cp, hmc⟩
                    · intro Lc hLc; elim_steps!
                      exact hLc sz.toNat (0#32, ()) m
                        ⟨arena_i, sp.core.flags, Nat.zero_le _, rfl, hari_len,
                         hlok1.core_ok.flags_len, hari_pre, hari_8m, hari_512k, hari_sz,
                         fun _ hi => absurd hi (Nat.not_lt_zero _),
                         commit_mem_congr rfl hm⟩
    · exact hQ 1#64 sp mp hdwp htmkt hcvp hflp (Or.inl rfl)
        (fun h => absurd h (by decide)) hmp
  · intro L hL; elim_steps!
    exact hL (r_end.toNat - r_off.toNat) (r_off, ()) m0
      ⟨s0, hdw0, htmk0, rfl, rfl, Nat.le_refl _, hoff_le, rfl, hrb0, hm0⟩

end LeanQbe.T.Examples.Kissat.Proof.Eliminate
