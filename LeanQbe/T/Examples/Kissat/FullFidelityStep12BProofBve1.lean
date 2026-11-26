/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep12BBveFwd
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas1
public import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullBveBvaLemmas3
import LeanQbe.T.Examples.Kissat.FullBveVarLemmas2
import LeanQbe.T.Examples.Kissat.FullM6BveFwdProof1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 12B — BVE Weaken-Unit & Commit-Resolvent Proofs
(`FullFidelityStep12BProofBve1`)

UNSAT-only `Func.wp` proofs (`public section`, `0` `@[expose]`, `0` `import all`, `XPost := False`):
1. `full_bve_weaken_unit_fid_s12b_wp`: certifies `FullFastBveBudgets.fullBveWeakenTmkSpec` for
   `full_bve_weaken_unit_fid` (`P1-2` single-unit weakening).
2. `full_bve_commit_res_s12b_wp`: certifies `FullFastBveBudgets.fullBveCommitResTmkSpec` for
   `full_bve_commit_res` (`P1-7` `FL_SUBSUME | FL_ELIM_C | FL_FACT_P/N` & `PH_SUBSUME` marking).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep12B

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM6BveFwd
open Kraken.Bedrock2.Test

open scoped FullArenaTactics

local macro "s12b_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-! ## 1. Private Helpers for `full_bve_weaken_unit_fid` & `full_bve_commit_res` -/

private theorem s12b_denseInvW_of_full {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : Full.FullDenseInvW c F0 F_cur s) :
    FullBveVarSpecs.FullDenseInvW c F0 F_cur s := h

private theorem s12b_denseInvW_to_full {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullBveVarSpecs.FullDenseInvW c F0 F_cur s) :
    Full.FullDenseInvW c F0 F_cur s := h

private theorem s12b_resBuf_to_bve {F_cur : List (List Nat)} {s : FullState} {r_end p : Nat}
    (h : Full.FullResBufOkW F_cur s r_end p) : FullBveVarSpecs.FullResBufOkW F_cur s r_end p := by
  induction h with
  | nil => exact .nil
  | cons hbd hsz hlts hnd hent _ ih => exact .cons hbd hsz hlts hnd hent ih

private theorem s12b_bveAddUnit_adapter {Γ : Env}
    (hAddUnit : ∀ a m Q X, Full.fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, FullBveVarSpecs.fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X := by
  rintro ⟨h, lit, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hent, hm, hQ⟩
  refine hAddUnit _ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hent, hm,
    fun ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
      phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss' m' hlen' hw' hcl0 hltf hof hm' => ?_⟩
  exact hQ ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
    { s.scratch with
      phases := phases', target_assigned := ta', best_assigned := ba',
      phases_target := pt', phases_best := pb', heap := hp', pos := ps',
      heap_len := hl', q_search_idx := qsi', q_search_stamp := qss' }
    m' hlen' hw' ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hcl0 hltf hof hm'

private theorem s12b_commit_arenaLits_eq_copied {k : FullCoreState} {scr : List (BitVec 32)}
    {cr0 p1 sz : Nat} (hbd : cr0 + 3 + sz ≤ k.arena.length) (hscr : p1 + sz ≤ scr.length)
    (hsz : (k.arena[cr0 + 2]?.getD 0#32).toNat = sz)
    (hcp : ∀ j < sz, k.arena[cr0 + 3 + j]? = scr[p1 + j]?) :
    fullArenaClauseLitsCore k cr0 =
      (List.range sz).map fun j => (scr[p1 + j]?.getD 0#32).toNat := by
  unfold fullArenaClauseLitsCore fullArenaClauseSizeCore
  rw [hsz]
  apply List.ext_getElem
  · simp [List.length_take, List.length_drop,
      Nat.min_eq_left (by omega : sz ≤ k.arena.length - (cr0 + 3))]
  · intro j hj1 _
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop, List.getElem_range]
    have hj : j < sz := by simp [List.length_take, List.length_drop] at hj1; omega
    have hlt_ar : cr0 + 3 + j < k.arena.length := by omega
    have hlt_scr : p1 + j < scr.length := by omega
    have heq := hcp j hj
    rw [List.getElem?_eq_getElem hlt_ar, List.getElem?_eq_getElem hlt_scr, Option.some.injEq]
      at heq
    rw [List.getElem?_eq_getElem hlt_scr, Option.getD_some, heq]

private theorem s12b_commit_resBuf_head_step {F_cur : List (List Nat)} {s : FullState}
    {r_end p : Nat} (hres : FullBveVarSpecs.FullResBufOkW F_cur s r_end p) (hlt : p < r_end) :
    p + 1 + (s.scratch.scratch_buf[p]?.getD 0#32).toNat ≤ r_end ∧
      let sz := (s.scratch.scratch_buf[p]?.getD 0#32).toNat
      (∀ k < sz, (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      ((List.range sz).map fun k =>
        (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat / 2).Nodup ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause ((List.range sz).map fun k =>
        (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat)) ∧
      FullBveVarSpecs.FullResBufOkW F_cur s r_end (p + 1 + sz) := by
  cases hres with
  | nil => exact absurd hlt (Nat.lt_irrefl _)
  | @cons _ sz0 hbd hsz hlts hnd hent htail =>
    subst hsz; exact ⟨hbd, hlts, hnd, hent, htail⟩

private theorem s12b_bv32_bit23_or_garb (x : BitVec 32) :
    ((x ||| 0x00080000#32) &&& 0x00800000#32) = (x &&& 0x00800000#32) := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or]
  have hbit : ∀ j : Fin 32,
      ((0x00080000#32 : BitVec 32).getLsbD j.val && (0x00800000#32 : BitVec 32).getLsbD j.val) =
        false := by decide
  have hj := hbit ⟨k, hk⟩
  cases hx : x.getLsbD k <;> cases h1 : (0x00080000#32 : BitVec 32).getLsbD k <;>
    cases h2 : (0x00800000#32 : BitVec 32).getLsbD k <;> simp_all

private theorem s12b_bv32_bit19_or_garb_ne0 (x : BitVec 32) :
    ((x ||| 0x00080000#32) &&& 0x00080000#32) ≠ 0#32 := by
  intro h
  have := congrArg (·.getLsbD 19) h
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] at this
  have h19 : (0x00080000#32 : BitVec 32).getLsbD 19 = true := by decide
  simp only [h19, Bool.or_true, Bool.and_true] at this; exact Bool.noConfusion this

private theorem s12b_commit_res_garb_inv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {sl : FullState} {flk ark : List (BitVec 32)} {wvec' wstk' wsort' : List (BitVec 32)}
    {wlen' : Nat} {wu' ag' : BitVec 64} {sz : Nat}
    (hinv : FullBveVarSpecs.FullDenseInvW c F0 F_cur sl)
    (hflk : flk.length = c.max_vars)
    (hsz_ge3 : 3 ≤ sz) (hark_len : ark.length = c.arena_cap)
    (hark_hold : ∀ i < sl.core.arena_len, ark[i]? = sl.core.arena[i]?)
    (hns2 : (ark[sl.core.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hsz2_ar : (ark[sl.core.arena_len + 2]?.getD 0#32).toNat = sz)
    (har_cr_idx : sl.core.arena_len < ark.length)
    (hlenw' : ({ sl with
      core := { sl.core with flags := flk, arena := ark, arena_len := sl.core.arena_len + 3 + sz,
                             wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
      scratch := { sl.scratch with wsort := wsort' } } : FullState).LengthsOk c)
    (hwatw' : ModeWatchesInv F_cur
      { sl.core with flags := flk, arena := ark, arena_len := sl.core.arena_len + 3 + sz,
                     wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' })
    (hrefs2 : fullArenaClauseRefsCore
      { sl.core with flags := flk, arena := ark, arena_len := sl.core.arena_len + 3 + sz } =
      fullArenaClauseRefsCore sl.core ++ [sl.core.arena_len]) :
    let cr0 := sl.core.arena_len
    let ark_g := ark.set cr0 ((ark[cr0]'har_cr_idx) ||| 0x00080000#32)
    Full.FullDenseInvW c F0 F_cur
      { sl with
        core := { sl.core with
          flags := flk, arena := ark_g, arena_len := cr0 + 3 + sz,
          wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu',
          arena_garbage := ag', oom := 1#64 }
        scratch := { sl.scratch with wsort := wsort' } } := by
  intro cr0 ark_g
  let s_ws : FullState :=
    { sl with core := { sl.core with flags := flk },
              scratch := { sl.scratch with wsort := wsort' } }
  have hinv_ws : FullBveVarSpecs.FullDenseInvW c F0 F_cur s_ws := by
    have hfl_inv := m6_fullDenseInvW_with_flags (s12b_denseInvW_to_full hinv) hflk
    exact ⟨⟨hfl_inv.1.core_ok,
        { hfl_inv.1.scratch_ok with wsort_len := hlenw'.scratch_ok.wsort_len }⟩,
      hfl_inv.2.1, hfl_inv.2.2.1, hfl_inv.2.2.2.1, hfl_inv.2.2.2.2.1,
      hfl_inv.2.2.2.2.2.1, hfl_inv.2.2.2.2.2.2⟩
  have hhold_g : ∀ i < cr0, ark_g[i]? = sl.core.arena[i]? :=
    fun i hi => by rw [List.getElem?_set_ne (by omega)]; exact hark_hold i hi
  have hns_g : (ark_g[cr0]?.getD 0#32 &&& 0x00800000#32) = 0#32 := by
    rw [List.getElem?_set_self har_cr_idx, Option.getD_some, s12b_bv32_bit23_or_garb]
    have := hns2; rw [List.getElem?_eq_getElem har_cr_idx, Option.getD_some] at this; exact this
  have hng_g : (ark_g[cr0]?.getD 0#32 &&& 0x00080000#32) ≠ 0#32 := by
    rw [List.getElem?_set_self har_cr_idx, Option.getD_some]
    exact s12b_bv32_bit19_or_garb_ne0 _
  have hsz_g : (ark_g[cr0 + 2]?.getD 0#32).toNat = sz := by
    rw [List.getElem?_set_ne (by omega)]; exact hsz2_ar
  have hlen_g : ({ s_ws with
    core := { s_ws.core with
      arena := ark_g, arena_len := cr0 + 3 + sz,
      wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu',
      arena_garbage := ag', oom := 1#64 } } : FullState).LengthsOk c :=
    ⟨{ hlenw'.core_ok with arena_len_arr := by simp [ark_g, hark_len] }, hlenw'.scratch_ok⟩
  have hrefs_g : fullArenaClauseRefsCore
      { s_ws.core with arena := ark_g, arena_len := cr0 + 3 + sz } =
      fullArenaClauseRefsCore sl.core ++ [cr0] :=
    fullArenaClauseRefsCore_append hinv.2.1.arena hsz_ge3 rfl hhold_g hns_g hsz_g
  have hwat_g : ModeWatchesInv F_cur
      { s_ws.core with
        arena := ark_g, arena_len := cr0 + 3 + sz,
        wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu',
        arena_garbage := ag', oom := 1#64 } :=
    hwatw'.with_wstk rfl rfl rfl rfl rfl (fun r hr => by
      change r ∈ fullArenaClauseRefsCore
        { sl.core with flags := flk, arena := ark, arena_len := cr0 + 3 + sz } at hr
      rw [hrefs2] at hr; exact hrefs_g ▸ hr)
  exact s12b_denseInvW_to_full (FullBveVarHelpers.addGarbageClause_preserves_witness hinv_ws
    hlen_g hsz_ge3 hhold_g hns_g hng_g hsz_g hwat_g)

private theorem s12b_commit_res_entailed_inv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {sl : FullState} {flk ark : List (BitVec 32)} {wvecw wstkw wsortw : List (BitVec 32)}
    {wlenw : Nat} {wuw : BitVec 64} {p_nat sz : Nat}
    (hinv : FullBveVarSpecs.FullDenseInvW c F0 F_cur sl)
    (hflk : flk.length = c.max_vars)
    (hsz_ge3 : 3 ≤ sz)
    (hlts : ∀ k < sz, (sl.scratch.scratch_buf[p_nat + 1 + k]?.getD 0#32).toNat <
      2 * sl.core.cur_vars)
    (hnd : ((List.range sz).map fun k =>
      (sl.scratch.scratch_buf[p_nat + 1 + k]?.getD 0#32).toNat / 2).Nodup)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause ((List.range sz).map fun k =>
      (sl.scratch.scratch_buf[p_nat + 1 + k]?.getD 0#32).toNat)))
    (hark_hold : ∀ i < sl.core.arena_len, ark[i]? = sl.core.arena[i]?)
    (hns2 : (ark[sl.core.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hsz2_ar : (ark[sl.core.arena_len + 2]?.getD 0#32).toNat = sz)
    (hlits_eq : fullArenaClauseLitsCore
      { sl.core with flags := flk, arena := ark, arena_len := sl.core.arena_len + 3 + sz }
        sl.core.arena_len =
      (List.range sz).map fun j => (sl.scratch.scratch_buf[p_nat + 1 + j]?.getD 0#32).toNat)
    (hlenw : ({ sl with
      core := { sl.core with flags := flk, arena := ark, arena_len := sl.core.arena_len + 3 + sz,
                             wvec := wvecw, wstk := wstkw, wlen := wlenw, wusable := wuw }
      scratch := { sl.scratch with wsort := wsortw } } : FullState).LengthsOk c)
    (hwatw : ModeWatchesInv F_cur
      { sl.core with flags := flk, arena := ark, arena_len := sl.core.arena_len + 3 + sz,
                     wvec := wvecw, wstk := wstkw, wlen := wlenw, wusable := wuw }) :
    let cr0 := sl.core.arena_len
    FullBveVarSpecs.FullDenseInvW c F0 F_cur
      { sl with
        core := { sl.core with
          flags := flk, arena := ark, arena_len := cr0 + 3 + sz,
          wvec := wvecw, wstk := wstkw, wlen := wlenw, wusable := wuw,
          num_irred := sl.core.num_irred + 1#64 }
        scratch := { sl.scratch with wsort := wsortw } } := by
  intro cr0
  let s_ws : FullState :=
    { sl with core := { sl.core with flags := flk },
              scratch := { sl.scratch with wsort := wsortw } }
  have hinv_ws : FullBveVarSpecs.FullDenseInvW c F0 F_cur s_ws := by
    have hfl_inv := m6_fullDenseInvW_with_flags (s12b_denseInvW_to_full hinv) hflk
    exact ⟨⟨hfl_inv.1.core_ok,
        { hfl_inv.1.scratch_ok with wsort_len := hlenw.scratch_ok.wsort_len }⟩,
      hfl_inv.2.1, hfl_inv.2.2.1, hfl_inv.2.2.2.1, hfl_inv.2.2.2.2.1,
      hfl_inv.2.2.2.2.2.1, hfl_inv.2.2.2.2.2.2⟩
  have hlen_c : ({ s_ws with
    core := { s_ws.core with
      arena := ark, arena_len := cr0 + 3 + sz,
      wvec := wvecw, wstk := wstkw, wlen := wlenw, wusable := wuw,
      num_irred := sl.core.num_irred + 1#64 } } : FullState).LengthsOk c :=
    ⟨{ hlenw.core_ok with arena_len_arr := hlenw.core_ok.arena_len_arr }, hlenw.scratch_ok⟩
  have hwat_c : ModeWatchesInv F_cur
      { s_ws.core with
        arena := ark, arena_len := cr0 + 3 + sz,
        wvec := wvecw, wstk := wstkw, wlen := wlenw, wusable := wuw,
        num_irred := sl.core.num_irred + 1#64 } :=
    hwatw.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
  exact FullBveVarHelpers.addEntailedClause_preserves_witness hinv_ws hlen_c hsz_ge3
    (fun l hl => by
      have hl' : l ∈ (List.range sz).map fun j =>
          (sl.scratch.scratch_buf[p_nat + 1 + j]?.getD 0#32).toNat := by
        simpa only [← hlits_eq] using hl
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hl'
      rw [List.mem_range] at hj; exact hlts j hj)
    (by rw [hlits_eq, List.map_map]; simpa only [Function.comp_def] using hnd)
    (by rw [hlits_eq]; exact hent)
    hark_hold hns2 hsz2_ar hwat_c

private theorem s12b_fullDenseInvW_push_ext1 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {ext' : List (BitVec 32)} {el' : Nat}
    (hext : ext'.length = c.extend_cap) (hel : el' ≤ c.extend_cap) :
    FullDenseInvW c F0 F_cur
      { s with scratch := { s.scratch with extend_stk := ext', extend_len := el' } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with extend_stk_len := hext }⟩,
   h.2.1, h.2.2.1, h.2.2.2.1, ⟨h.2.2.2.2.1.1, hel⟩, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

private theorem s12b_bv32_bit23_or_sub (x : BitVec 32) :
    ((x ||| 0x01000000#32) &&& 0x00800000#32) = (x &&& 0x00800000#32) := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or]
  have hbit : ∀ j : Fin 32,
      ((0x01000000#32 : BitVec 32).getLsbD j.val && (0x00800000#32 : BitVec 32).getLsbD j.val) =
        false := by decide
  have hj := hbit ⟨k, hk⟩
  cases hx : x.getLsbD k <;> cases h1 : (0x01000000#32 : BitVec 32).getLsbD k <;>
    cases h2 : (0x00800000#32 : BitVec 32).getLsbD k <;> simp_all

/-! ## 2. `full_bve_weaken_unit_fid` (`P1-2` Single-Unit Weakening) -/

/-- `full_bve_weaken_unit_fid` satisfies `FullFastBveBudgets.fullBveWeakenTmkSpec`. -/
theorem full_bve_weaken_unit_fid_s12b_wp (Γ : Env)
    (hDelBin : ∀ xs m Q X, fullDeleteBinarySpec xs m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] xs m Q X) :
    ∀ args m Q X, fullBveWeakenTmkSpec args m Q X →
      Func.wp Γ full_bve_weaken_unit_fid_body args m Q X := by
  rintro ⟨h, blk_lit, off, cnt, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, R, rfl, hdw, htmk, hblk, hoff, hitems, hm0, hQ⟩
  have hmv := c.hmaxv; have hsc := c.hscr; have harc := c.harena; have hexc := c.hext
  unfold dimacsBound at hmv hsc harc hexc
  unfold Func.wp full_bve_weaken_unit_fid_body
  c0_hsplit
  · c0_hsteps!; exact hQ true s m0 hdw htmk rfl rfl rfl rfl hm0
  · c0_hsplit
    · c0_hsteps!; exact hQ false s m0 hdw htmk rfl rfl rfl rfl hm0
    · have hel_lt : s.scratch.extend_len < c.extend_cap := by
        have hel_le := hdw.2.2.2.2.1.2
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc; omega
      c0_hsteps_nogrp
      refine wp_loop_group (ts := [i32])
        (fun rem (i, ()) mi =>
          ∃ si : FullState,
            i.toNat ≤ cnt.toNat ∧ rem = cnt.toNat - i.toNat ∧
            FullDenseInvW c F0 F_cur si ∧ TmkZero si ∧
            si.core.cur_vars = s.core.cur_vars ∧ si.core.fuel = s.core.fuel ∧
            si.scratch.scratch_buf = s.scratch.scratch_buf ∧
            si.scratch.extend_len = s.scratch.extend_len ∧
            fullArenaClauseRefs si = fullArenaClauseRefs s ∧
            (FullMem c si ⋆ R) mi)
        ?_ ?_
      · rintro L rem ⟨i, ⟨⟩⟩ mi hL
          ⟨si, hi_le, rfl, hdw_i, htmk_i, hcv_eq, hfuel_eq, hscr_eq, hel_eq, hrefs_eq, hm_i⟩
        have hcl_i := hdw_i.1.core_ok; have hsl_i := hdw_i.1.scratch_ok
        have hscrl_i : si.scratch.scratch_buf.length = c.scratch_cap := hsl_i.scratch_buf_len
        have harl_i : si.core.arena.length = c.arena_cap := hcl_i.arena_len_arr
        have harle_i : si.core.arena_len ≤ c.arena_cap := hcl_i.arena_len_le
        c0_hsplit
        · have hi_lt : i.toNat < cnt.toNat := hc
          have hoff_nat : (off + i).toNat = off.toNat + i.toNat := by c0_bound
          have hscr_lt : ((off + i).setWidth 64).toNat < si.scratch.scratch_buf.length := by
            rw [m6_zext32_toNat, hscrl_i, hoff_nat]; omega
          have hw_eq : si.scratch.scratch_buf[((off + i).setWidth 64).toNat]'hscr_lt =
              s.scratch.scratch_buf[off.toNat + i.toNat]?.getD 0#32 := by
            have h1 : si.scratch.scratch_buf[off.toNat + i.toNat]?.getD 0#32 =
                s.scratch.scratch_buf[off.toNat + i.toNat]?.getD 0#32 := by rw [hscr_eq]
            rw [← h1, List.getElem?_eq_getElem (by rw [hscrl_i]; omega), Option.getD_some]
            exact m6_getElem_congr (by rw [m6_zext32_toNat, hoff_nat]) _ _
          have hi1 : (i + 1#32).toNat = i.toNat + 1 := by c0_bound
          c0_hsteps_nogrp
          refine wp_join_state (ts := []) (α := FullState) (fun _ => ())
            (fun sj mj =>
              FullDenseInvW c F0 F_cur sj ∧ TmkZero sj ∧
              sj.core.cur_vars = s.core.cur_vars ∧ sj.core.fuel = s.core.fuel ∧
              sj.scratch.scratch_buf = s.scratch.scratch_buf ∧
              sj.scratch.extend_len = s.scratch.extend_len ∧
              fullArenaClauseRefs sj = fullArenaClauseRefs s ∧
              (FullMem c sj ⋆ R) mj)
            (fun _ sj mj ⟨hdwj, htmkj, hcvj, hflj, hscrj, helj, hrefsj, hmj⟩ => by
              c0_hsteps!
              exact hL (cnt.toNat - (i + 1#32).toNat) (i + 1#32, ()) mj (by omega)
                ⟨sj, by omega, rfl, hdwj, htmkj, hcvj, hflj, hscrj, helj, hrefsj, hmj⟩)
            (fun Jstep hJstep => by
              c0_hsplit
              · -- Binary entry: delete binary without pushing to `extend_stk`
                c0_hsteps_nogrp
                s12b_call hDelBin
                refine ⟨c, si, R, rfl, hdw_i.1, hdw_i.2.1.watches.layout, hm_i, ?_⟩
                intro wvec' wstk' wu' nb' m2 _ hlen2 _hwl2 hwat2 hm2
                let s2 : FullState :=
                  { si with core := { si.core with
                    wvec := wvec', wstk := wstk', wusable := wu', num_binary := nb' } }
                have hdw2 := FullBveBvaHelpers.fullDenseInvW_of_delete_binary hdw_i hlen2 hwat2
                have hrefs2 : fullArenaClauseRefs s2 = fullArenaClauseRefs si := by
                  unfold fullArenaClauseRefs fullArenaClauseRefsCore; rfl
                c0_hsteps!
                exact hJstep s2 m2 ⟨hdw2, htmk_i.congr rfl rfl, hcv_eq, hfuel_eq, hscr_eq,
                  hel_eq, hrefs2.trans hrefs_eq, hm2⟩
              · -- Large clause entry: mark `PH_GARB` without pushing to `extend_stk`
                let w := si.scratch.scratch_buf[((off + i).setWidth 64).toNat]'hscr_lt
                have hitem_i := hitems i.toNat hi_lt
                unfold FullBveWeakItemOk at hitem_i
                have hnb : ¬ (s.scratch.scratch_buf[off.toNat + i.toNat]?.getD 0#32 &&&
                    0x80000000#32) ≠ 0#32 := by
                  intro hne
                  have hhc : w &&& 0x80000000#32 = 0#32 := by
                    dsimp only [w]
                    have hcongr := m6_getElem_congr
                      (by rw [m6_zext32_toNat, hoff_nat, Nat.mod_eq_of_lt (by omega)] :
                        ((off + i).setWidth 64).toNat = (off.toNat + i.toNat) % 2 ^ 32)
                      hscr_lt (by rw [hscrl_i, Nat.mod_eq_of_lt (by omega)]; omega)
                    rw [hcongr]; exact hc
                  dsimp only [w] at hhc; rw [hw_eq] at hhc; exact hne hhc
                rw [ite_eq_right hnb] at hitem_i
                have hw_ref : w.toNat ∈ fullArenaClauseRefs si := by
                  dsimp only [w]; rw [hw_eq, hrefs_eq]; exact hitem_i
                have hwf := hdw_i.2.1.arena.refs_wf w.toNat hw_ref
                have hw_ar : ((si.scratch.scratch_buf[((off + i).setWidth 64).toNat]'hscr_lt
                    ).setWidth 64).toNat < si.core.arena.length := by
                  change (w.setWidth 64).toNat < si.core.arena.length
                  rw [m6_zext32_toNat, harl_i]; omega
                have hw_ar_nat : w.toNat < si.core.arena.length := by rw [harl_i]; omega
                have hw2_ar : ((si.scratch.scratch_buf[((off + i).setWidth 64).toNat]'hscr_lt
                    ).setWidth 64 + 2#64).toNat < si.core.arena.length := by
                  change (w.setWidth 64 + 2#64).toNat < si.core.arena.length
                  rw [harl_i]; c0_bound
                have hw2_ar_set : ((si.scratch.scratch_buf[((off + i).setWidth 64).toNat]'hscr_lt
                    ).setWidth 64 + 2#64).toNat < (si.core.arena.set
                    ((si.scratch.scratch_buf[((off + i).setWidth 64).toNat]'hscr_lt).setWidth
                      64).toNat
                    (si.core.arena[((si.scratch.scratch_buf[((off + i).setWidth 64).toNat]'hscr_lt
                      ).setWidth 64).toNat]'hw_ar ||| 0x00080000#32)).length := by
                  rw [List.length_set]; exact hw2_ar
                c0_hsteps!
                let ar' := si.core.arena.set (w.setWidth 64).toNat
                  (si.core.arena[(w.setWidth 64).toNat]'hw_ar ||| 0x00080000#32)
                let ag' := si.core.arena_garbage + 3#64 +
                  (ar'[(w.setWidth 64 + 2#64).toNat]'hw2_ar_set).setWidth 64
                let s2 : FullState :=
                  { si with core := { si.core with arena := ar', arena_garbage := ag' } }
                have hhdr_eq : si.core.arena[w.toNat]'hw_ar_nat = fullArenaHdr si w.toNat := by
                  unfold fullArenaHdr fullArenaHdrCore
                  rw [List.getElem?_eq_getElem hw_ar_nat, Option.getD_some]
                have har'_eq : ar' = si.core.arena.set w.toNat
                    (fullArenaHdr si w.toNat ||| 0x00080000#32) := by
                  dsimp only [ar']; rw [← hhdr_eq]
                  have hval := m6_getElem_congr (m6_zext32_toNat w) hw_ar hw_ar_nat
                  rw [hval, m6_zext32_toNat]
                have hmg := m6_fullDenseInvW_markGarb hdw_i hw_ref (arena' := ar') (ag' := ag')
                  (by simp [ar', harl_i])
                  (Or.inl (by rw [har'_eq]; exact List.getElem?_set_self hw_ar_nat))
                  (fun idx hne _ => by rw [har'_eq]; exact List.getElem?_set_ne hne.symm)
                exact hJstep s2 _ ⟨hmg.1, htmk_i.congr rfl rfl, hcv_eq, hfuel_eq, hscr_eq,
                  hel_eq, hmg.2.trans hrefs_eq, hm⟩)
        · -- Loop done: push single unit `(blk_lit & PW_LIT_MASK) | EXT_BLK_FLAG` to `extend_stk`
          have hp_lt : si.scratch.extend_len < si.scratch.extend_stk.length := by
            rw [hsl_i.extend_stk_len, hel_eq]; exact hel_lt
          have hp_bv : (BitVec.ofNat 64 si.scratch.extend_len).toNat = si.scratch.extend_len := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          have hp1_bv : (BitVec.ofNat 64 si.scratch.extend_len + 1#64).toNat =
              si.scratch.extend_len + 1 := by
            rw [BitVec.toNat_add, hp_bv, show (1#64 : BitVec 64).toNat = 1 from rfl,
              Nat.mod_eq_of_lt (by omega)]
          c0_hsteps!
          let ext' := si.scratch.extend_stk.set si.scratch.extend_len
            ((blk_lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32)
          let sf : FullState :=
            { si with scratch :=
              { si.scratch with extend_stk := ext', extend_len := si.scratch.extend_len + 1 } }
          have hdwf : FullDenseInvW c F0 F_cur sf :=
            s12b_fullDenseInvW_push_ext1 hdw_i (by simp [ext', hsl_i.extend_stk_len])
              (by rw [hel_eq]; omega)
          exact hQ true sf _ hdwf (htmk_i.congr rfl rfl) hcv_eq hfuel_eq hscr_eq hrefs_eq
            (by simpa [sf, ext', hp_bv, hp1_bv] using hm)
      · intro L hL; c0_hsteps!
        exact hL cnt.toNat (0#32, ()) m0
          ⟨s, Nat.zero_le _, by simp, hdw, htmk, rfl, rfl, rfl, rfl, rfl, hm0⟩

/-! ## 3. `full_bve_commit_res` (`P1-7` Resolvent Flags & `PH_SUBSUME`) -/

/-- `full_bve_commit_res` (Step-12B) satisfies `FullFastBveBudgets.fullBveCommitResTmkSpec`. -/
theorem full_bve_commit_res_s12b_wp (Γ : Env)
    (hAlloc : ∀ xs m Q X, Full.fullAllocClSpec xs m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] xs m Q X)
    (hWPush : ∀ xs m Q X, Full.fullWatchPushSpec xs m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] xs m Q X)
    (hAddBin : ∀ xs m Q X, Full.fullAddBinSpec xs m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] xs m Q X)
    (hAddUnit : ∀ xs m Q X, Full.fullAddUnitSpec xs m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] xs m Q X) :
    ∀ args m Q X, fullBveCommitResTmkSpec args m Q X →
      Func.wp Γ full_bve_commit_res_body args m Q X := by
  let hAU := s12b_bveAddUnit_adapter hAddUnit
  rintro ⟨h, r_off, r_end, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv0, htmk0, hle0, hcap0, hbuf0, hm0, hQ⟩
  have hmv := c.hmaxv; have harc := c.harena; have hsc := c.hscr
  unfold dimacsBound at hmv harc hsc
  unfold Func.wp full_bve_commit_res_body
  c0_hsteps_nogrp
  refine wp_loop_group (ts := [i64])
    (fun rem (p, ()) ml =>
      ∃ sl : FullState,
        FullBveVarSpecs.FullDenseInvW c F0 F_cur sl ∧ TmkZero sl ∧
        sl.core.cur_vars = s.core.cur_vars ∧ sl.core.fuel = s.core.fuel ∧
        p.toNat ≤ r_end.toNat ∧ rem = r_end.toNat - p.toNat ∧
        FullBveVarSpecs.FullResBufOkW F_cur sl r_end.toNat p.toNat ∧ (FullMem c sl ⋆ R) ml)
    ?_ ?_
  · rintro L rem ⟨p, ⟨⟩⟩ ml hL ⟨sl, hinv, htmk, hcv_eq, hfl_eq, hp_le, rfl, hres, hm_lp⟩
    have hcl := hinv.1.core_ok; have hsl := hinv.1.scratch_ok
    have hscrl := hsl.scratch_buf_len; have harl := hcl.arena_len_arr
    have harle := hcl.arena_len_le; have hcv := hcl.cur_vars_le
    c0_hsplit
    · have hp_lt : p.toNat < r_end.toNat := hc
      have hp_scr : p.toNat < sl.scratch.scratch_buf.length := by omega
      let sz_bv := sl.scratch.scratch_buf[p.toNat]'hp_scr
      let sz := sz_bv.toNat
      have hsz_def : (sl.scratch.scratch_buf[p.toNat]?.getD 0#32).toNat = sz := by
        rw [List.getElem?_eq_getElem hp_scr, Option.getD_some]
      obtain ⟨hbd, hlts, hnd, hent, htail⟩ := s12b_commit_resBuf_head_step hres hp_lt
      rw [hsz_def] at hbd hlts hnd hent htail
      have hp1_nat : (p + 1#64).toNat = p.toNat + 1 := by c0_bound
      have hnext_nat : (p + 1#64 + sz_bv.setWidth 64).toNat = p.toNat + 1 + sz := by
        rw [BitVec.toNat_add, hp1_nat, m6_zext32_toNat, Nat.mod_eq_of_lt (by omega)]
      c0_hsteps_nogrp
      c0_hsplit
      · -- `sz == 0`: empty resolvent -> UNSAT
        have hsz0 : sz = 0 := by
          have := congrArg BitVec.toNat hc; simpa [sz, sz_bv] using this
        rw [hsz0] at hent
        have hent_nil : (cnfOfClauses F_cur).EntailsClause (cnfClause []) := by simpa using hent
        have hunsat_cur : (cnfOfClauses F_cur).Unsat := unsat_of_entails_nil hent_nil
        have hunsat0 : F0.Unsat := hinv.2.1.ext_sound.2 hunsat_cur
        c0_hsteps!
        let sl' := { sl with core := { sl.core with inconsistent := 1#64 } }
        exact hQ 20#64 sl' _ (s12b_denseInvW_to_full
            (FullBveVarHelpers.FullDenseInvW.with_inconsistent hinv 1#64 (fun _ => hunsat_cur)))
          (htmk.congr rfl rfl) hcv_eq hfl_eq (Or.inr (Or.inr rfl)) (fun _ => hunsat0) hm
      · have hne0 : sz_bv ≠ 0#32 := hc
        -- Join after `if (sz == 1) ... else if (sz == 2) ... else ...` to advance `p = p + sz`
        refine wp_join_state (ts := []) (α := FullState) (fun _ => ())
          (fun sn mn =>
            FullBveVarSpecs.FullDenseInvW c F0 F_cur sn ∧ TmkZero sn ∧
            sn.core.cur_vars = s.core.cur_vars ∧ sn.core.fuel = s.core.fuel ∧
            FullBveVarSpecs.FullResBufOkW F_cur sn r_end.toNat (p.toNat + 1 + sz) ∧
            (FullMem c sn ⋆ R) mn)
          (fun _ sn mn ⟨hdwn, htmkn, hcvn, hfln, hresn, hmn⟩ => by
            c0_hsteps!
            exact hL (r_end.toNat - (p + 1#64 + sz_bv.setWidth 64).toNat)
              (p + 1#64 + sz_bv.setWidth 64, ()) mn (by rw [hnext_nat]; omega)
              ⟨sn, hdwn, htmkn, hcvn, hfln, by rw [hnext_nat]; omega, rfl,
               by rw [hnext_nat]; exact hresn, hmn⟩)
          (fun Jnext hJnext => by
            c0_hsplit
            · -- `sz == 1`: `full_add_unit`
              have hsz1 : sz = 1 := by
                have := congrArg BitVec.toNat hc; simpa [sz, sz_bv] using this
              have hp1_scr : (p + 1#64).toNat < sl.scratch.scratch_buf.length := by omega
              have hlit_lt : (sl.scratch.scratch_buf[(p + 1#64).toNat]'hp1_scr).toNat <
                  2 * sl.core.cur_vars := by
                have := hlts 0 (by omega)
                rw [List.getElem?_eq_getElem
                    (by omega : p.toNat + 1 < sl.scratch.scratch_buf.length),
                  Option.getD_some] at this
                simpa [hp1_nat] using this
              have hent1 : (cnfOfClauses F_cur).EntailsClause
                  (cnfClause [(sl.scratch.scratch_buf[(p + 1#64).toNat]'hp1_scr).toNat]) := by
                have hls : (List.range 1).map (fun k =>
                    (sl.scratch.scratch_buf[p.toNat + 1 + k]?.getD 0#32).toNat) =
                    [(sl.scratch.scratch_buf[(p + 1#64).toNat]'hp1_scr).toNat] := by
                  simp only [List.range_one, List.map_cons, List.map_nil, Nat.add_zero]
                  simp only [hp1_nat, List.getElem?_eq_getElem
                    (by omega : p.toNat + 1 < sl.scratch.scratch_buf.length), Option.getD_some]
                rw [hsz1] at hent; rw [← hls]; exact hent
              c0_hsteps_nogrp
              s12b_call hAU
              refine ⟨c, F0, F_cur, sl, R, rfl, hinv.1, hinv.2.1, (fun _ => hent1), hm_lp, ?_⟩
              dsimp only
              rintro ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
                sc' m' hlen' hw' hpres' hcl0 hokf_lt hokf hm'
              let s1 : FullState :=
                { sl with
                  core := { sl.core with
                    vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                    trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                    cur_level := cl', unassigned := unass', unflushed := unfl',
                    inconsistent := inc' }
                  scratch := sc' }
              have hinv' := FullBveVarHelpers.FullDenseInvW.of_addUnit hinv hlen' hw' hpres'.1 hcl0
              have htmk' : TmkZero s1 := htmk.congr rfl hpres'.2.2.2.1
              c0_hsplit
              · c0_hsteps!
                have hres' := FullBveVarHelpers.FullResBufOkW.with_state (s := sl) (s' := s1)
                  rfl (fun _ _ => by dsimp only [s1]; rw [hpres'.2.2.2.2.1]) htail
                exact hJnext s1 m' ⟨hinv', htmk', hcv_eq, hfl_eq, hres', hm'⟩
              · c0_hsteps!
                obtain ⟨hu0, _⟩ := hokf_lt hlit_lt (by simpa using hc)
                exact hQ 20#64 s1 m' (s12b_denseInvW_to_full hinv') htmk' hcv_eq hfl_eq
                  (Or.inr (Or.inr rfl)) (fun _ => hu0) hm'
            · have hne1 : sz_bv ≠ 1#32 := hc
              refine wp_join_state (ts := []) (α := FullState) (fun _ => ()) (fun sn mn =>
                  FullBveVarSpecs.FullDenseInvW c F0 F_cur sn ∧ TmkZero sn ∧
                  sn.core.cur_vars = s.core.cur_vars ∧ sn.core.fuel = s.core.fuel ∧
                  FullBveVarSpecs.FullResBufOkW F_cur sn r_end.toNat (p.toNat + 1 + sz) ∧
                  (FullMem c sn ⋆ R) mn)
                (fun _ sn mn h => by c0_hsteps!; exact hJnext sn mn h)
                (fun Jnext hJnext => by
              c0_hsplit
              · -- `sz == 2`: `full_add_bin` + `P1-7` `FL_SUBSUME | FL_ELIM_C | FL_FACT_P/N` flags
                have hsz2 : sz = 2 := by
                  have := congrArg BitVec.toNat hc; simpa [sz, sz_bv] using this
                have hp1_scr : (p + 1#64).toNat < sl.scratch.scratch_buf.length := by omega
                have hp2_nat : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by c0_bound
                have hp2_scr : (p + 1#64 + 1#64).toNat < sl.scratch.scratch_buf.length := by omega
                have hent2 : (cnfOfClauses F_cur).EntailsClause (cnfClause
                    [(sl.scratch.scratch_buf[(p + 1#64).toNat]'hp1_scr).toNat,
                     (sl.scratch.scratch_buf[(p + 1#64 + 1#64).toNat]'hp2_scr).toNat]) := by
                  have hls : (List.range 2).map (fun k =>
                      (sl.scratch.scratch_buf[p.toNat + 1 + k]?.getD 0#32).toNat) =
                      [(sl.scratch.scratch_buf[(p + 1#64).toNat]'hp1_scr).toNat,
                       (sl.scratch.scratch_buf[(p + 1#64 + 1#64).toNat]'hp2_scr).toNat] := by
                    simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append,
                      List.map_cons, List.map_nil, Nat.add_zero]
                    simp only [hp1_nat, hp2_nat,
                      List.getElem?_eq_getElem
                        (by omega : p.toNat + 1 < sl.scratch.scratch_buf.length),
                      List.getElem?_eq_getElem
                        (by omega : p.toNat + 2 < sl.scratch.scratch_buf.length),
                      Option.getD_some, List.cons_append, List.nil_append]
                  rw [hsz2] at hent; rw [← hls]; exact hent
                c0_hsteps_nogrp
                s12b_call hAddBin
                refine ⟨c, F0, F_cur, sl, R, rfl, hinv.1, hinv.2.1, hinv.2.2.2.2.2.1,
                  (fun _ _ => hent2), hm_lp, ?_⟩
                dsimp only
                rintro r vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu' nb'
                  oom' inc' phases' wsort' m' hlen' hw' hrcodes hr20 hr2 hm'
                let sb : FullState :=
                  { sl with
                    core := { sl.core with
                      vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                      trl := trl', trail_pos := tp', trail_end := te', unassigned := unass',
                      unflushed := unfl', wvec := wvec', wstk := wstk', wlen := wlen',
                      wusable := wu', num_binary := nb', oom := oom', inconsistent := inc' }
                    scratch := { sl.scratch with phases := phases', wsort := wsort' } }
                have hinv_b := FullBveVarHelpers.FullDenseInvW.of_addBin hinv hlen' hw'
                have htmk_b : TmkZero sb := htmk.congr rfl rfl
                c0_hsplit
                · c0_hsteps!
                  exact hQ 20#64 sb m' (s12b_denseInvW_to_full hinv_b) htmk_b hcv_eq hfl_eq
                    (Or.inr (Or.inr rfl)) (fun _ => (hr20 hc).1) hm'
                · c0_hsplit
                  · c0_hsteps!
                    exact hQ 2#64 sb m' (s12b_denseInvW_to_full hinv_b) htmk_b hcv_eq hfl_eq
                      (Or.inr (Or.inl rfl)) (fun h => by cases h) hm'
                  · c0_hsteps_nogrp
                    -- `P1-7`: set flags on `v0 = l0 >> 1` and `v1 = l1 >> 1`
                    refine wp_join_state (ts := []) (α := List (BitVec 32)) (fun _ => ())
                      (fun fl1 m1 => fl1.length = c.max_vars ∧
                        (FullMem c { sb with core := { sb.core with flags := fl1 } } ⋆ R) m1)
                      (fun _ fl1 m1 ⟨hfl1, hm1⟩ => by
                        c0_hsteps_nogrp
                        refine wp_join_state (ts := []) (α := List (BitVec 32)) (fun _ => ())
                          (fun fl2 m2 => fl2.length = c.max_vars ∧
                            (FullMem c { sb with core := { sb.core with flags := fl2 } } ⋆ R) m2)
                          (fun _ fl2 m2 ⟨hfl2, hm2⟩ => by
                            let sb2 : FullState := { sb with core := { sb.core with flags := fl2 } }
                            have hinv_b2 : FullBveVarSpecs.FullDenseInvW c F0 F_cur sb2 :=
                              s12b_denseInvW_of_full
                                (m6_fullDenseInvW_with_flags (s12b_denseInvW_to_full hinv_b) hfl2)
                            have hres_b2 := FullBveVarHelpers.FullResBufOkW.with_state
                              (s := sl) (s' := sb2) rfl (fun _ _ => rfl) htail
                            c0_hsteps!
                            exact hJnext sb2 m2 ⟨hinv_b2, htmk.congr rfl rfl, hcv_eq, hfl_eq,
                              hres_b2, hm2⟩)
                          (fun Jf2 hJf2 => by
                            c0_hsplit
                            · have hv1_lt : ((sl.scratch.scratch_buf[(p + 1#64 + 1#64).toNat]'
                                  hp2_scr >>> (1 : Nat)).setWidth 64).toNat < fl1.length := by
                                have hmod : s.core.cur_vars % 2 ^ 64 = s.core.cur_vars :=
                                  Nat.mod_eq_of_lt (by omega)
                                rw [hmod] at hc
                                rw [hfl1, m6_zext32_toNat, BitVec.toNat_ushiftRight,
                                  Nat.shiftRight_eq_div_pow]
                                have hdiv : (sl.scratch.scratch_buf[(p + 1#64 + 1#64).toNat]'
                                    hp2_scr).toNat / 2 < s.core.cur_vars := by
                                  simpa [hp2_nat, Nat.mod_eq_of_lt (by omega :
                                    p.toNat + 1 < 2 ^ 64), Nat.mod_eq_of_lt (by omega :
                                    p.toNat + 1 + 1 < 2 ^ 64)] using hc
                                omega
                              c0_hsteps_nogrp
                              refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
                                (fun x => (x, ())) (fun _ => True) ?_ ?_
                              · intro _ fv _
                                c0_hsteps!
                                exact hJf2 _ _ ⟨by simp [hfl1], hm⟩
                              · intro Jp1 hJp1
                                c0_hsplit <;> (c0_hsteps!; exact hJp1 _ trivial)
                            · c0_hsteps!; exact hJf2 fl1 m1 ⟨hfl1, hm1⟩))
                      (fun Jf1 hJf1 => by
                        c0_hsplit
                        · have hv0_lt : ((sl.scratch.scratch_buf[(p + 1#64).toNat]'
                              hp1_scr >>> (1 : Nat)).setWidth 64).toNat < flags'.length := by
                            have hmod : s.core.cur_vars % 2 ^ 64 = s.core.cur_vars :=
                              Nat.mod_eq_of_lt (by omega)
                            rw [hmod] at hc
                            rw [hlen'.core_ok.flags_len, m6_zext32_toNat, BitVec.toNat_ushiftRight,
                              Nat.shiftRight_eq_div_pow]
                            have hdiv : (sl.scratch.scratch_buf[(p + 1#64).toNat]'
                                hp1_scr).toNat / 2 < s.core.cur_vars := by
                              simpa [hp1_nat, Nat.mod_eq_of_lt (by omega :
                                p.toNat + 1 < 2 ^ 64)] using hc
                            omega
                          c0_hsteps_nogrp
                          refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
                            (fun x => (x, ())) (fun _ => True) ?_ ?_
                          · intro _ fv _
                            c0_hsteps!
                            exact hJf1 _ _ ⟨by simp [hlen'.core_ok.flags_len], hm⟩
                          · intro Jp0 hJp0
                            c0_hsplit <;> (c0_hsteps!; exact hJp0 _ trivial)
                        · c0_hsteps!; exact hJf1 flags' m' ⟨hlen'.core_ok.flags_len, hm'⟩)
              · -- `sz >= 3`: `full_alloc_cl` + `PH_SUBSUME` + copy + `P1-7` flags + watches
                have hne2 : sz_bv ≠ 2#32 := hc
                have hsz_ge3 : 3 ≤ sz := by
                  rcases Nat.lt_or_ge sz 3 with hlt3 | hge3
                  · exfalso
                    rcases (by omega : sz = 0 ∨ sz = 1 ∨ sz = 2) with h0 | h1 | h2
                    · exact hne0 (BitVec.eq_of_toNat_eq (by simp [sz, h0]))
                    · exact hne1 (BitVec.eq_of_toNat_eq (by simp [sz, h1]))
                    · exact hne2 (BitVec.eq_of_toNat_eq (by simp [sz, h2]))
                  · exact hge3
                have hsz_lt31 : sz < 2 ^ 31 := by omega
                have hsz_lt64 : sz < 2 ^ 64 := by omega
                c0_hsteps_nogrp
                s12b_call hAlloc
                refine ⟨c, sl, R, rfl, hinv.1, hm_lp, ?_⟩
                by_cases hoom_al : c.arena_cap - sl.core.arena_len < 3 + sz
                · refine Eq.mpr (ite_eq_left hoom_al) ?_
                  c0_hsplit
                  · c0_hsteps!
                    exact hQ 2#64 _ _ (s12b_denseInvW_to_full
                        (FullBveVarHelpers.FullDenseInvW.with_oom hinv 1#64))
                      (htmk.congr rfl rfl) hcv_eq hfl_eq (Or.inr (Or.inl rfl))
                      (fun h => by cases h) hm
                  · exfalso; exact hc rfl
                · refine Eq.mpr (ite_eq_right hoom_al) ?_
                  intro ar1 m1; try dsimp only
                  intro hlen1 hhold1 hns1 hng1 hred1 hsz1 hm1
                  let cr0 := sl.core.arena_len
                  have hcr0_le : cr0 + 3 + sz ≤ c.arena_cap := by dsimp only [cr0]; omega
                  let cr : BitVec 64 := BitVec.ofNat 64 cr0
                  have hcr0_lt31 : cr0 < 2 ^ 31 := by omega
                  have hcr_nat : cr.toNat = cr0 := by
                    simp [cr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : cr0 < 2 ^ 64)]
                  have hcr_ne : cr ≠ 0xFFFFFFFF#64 := by
                    intro heq; have := congrArg BitVec.toNat heq; rw [hcr_nat] at this
                    have h32 : (0xFFFFFFFF#64 : BitVec 64).toNat = 2 ^ 32 - 1 := rfl
                    omega
                  have hcr_ar1 : cr0 < ar1.length := by rw [hlen1.core_ok.arena_len_arr]; omega
                  c0_hsplit
                  · exfalso; exact hcr_ne hc
                  · -- `P1-7`: `ar[cr] = ar[cr] | PH_SUBSUME`
                    c0_hsteps_nogrp
                    let ar1s := ar1.set cr0 (ar1[cr0]'hcr_ar1 ||| 0x01000000#32)
                    have hhold1s : ∀ i < cr0, ar1s[i]? = sl.core.arena[i]? := fun i hi => by
                      rw [List.getElem?_set_ne (by omega)]; exact hhold1 i hi
                    have hns1s : (ar1s[cr0]?.getD 0#32 &&& 0x00800000#32) = 0#32 := by
                      rw [List.getElem?_set_self hcr_ar1, Option.getD_some, s12b_bv32_bit23_or_sub]
                      have := hns1; rw [List.getElem?_eq_getElem hcr_ar1, Option.getD_some] at this
                      exact this
                    have hsz1s : (ar1s[cr0 + 2]?.getD 0#32).toNat = sz := by
                      rw [List.getElem?_set_ne (by omega)]; exact hsz1
                    -- Copy loop: copies literals and sets `FL_SUBSUME | FL_ELIM_C | FL_FACT_P/N`
                    refine wp_loop_group (ts := [i32])
                      (fun rem_k (k, ()) mk =>
                        ∃ (flk ark : List (BitVec 32)),
                          k.toNat ≤ sz ∧ rem_k = sz - k.toNat ∧
                          flk.length = c.max_vars ∧ ark.length = c.arena_cap ∧
                          (∀ i < cr0, ark[i]? = sl.core.arena[i]?) ∧
                          ark[cr0]? = ar1s[cr0]? ∧ ark[cr0 + 2]? = ar1s[cr0 + 2]? ∧
                          (∀ j < k.toNat,
                            ark[cr0 + 3 + j]? = sl.scratch.scratch_buf[p.toNat + 1 + j]?) ∧
                          (FullMem c { sl with core := { sl.core with
                            flags := flk, arena := ark, arena_len := cr0 + 3 + sz } } ⋆ R) mk)
                      ?_ ?_
                    · rintro Lc rem_k ⟨k, ⟨⟩⟩ mk hLc
                        ⟨flk, ark, hk_le, rfl, hflk, hark_len, hark_hold, hark0, hark2, hark_cp,
                          hmk⟩
                      c0_hsplit
                      · have hk_lt : k.toNat < sz := hc
                        have hpk_nat : (p + 1#64 + k.setWidth 64).toNat =
                            p.toNat + 1 + k.toNat := by c0_bound
                        have hpk_scr : (p + 1#64 + k.setWidth 64).toNat <
                            sl.scratch.scratch_buf.length := by rw [hpk_nat, hscrl]; omega
                        have hack_nat : (cr + 3#64 + k.setWidth 64).toNat =
                            cr0 + 3 + k.toNat := by rw [← hcr_nat]; c0_bound
                        have hack_idx : (cr + 3#64 + k.setWidth 64).toNat < ark.length := by
                          rw [hack_nat, hark_len]; omega
                        have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
                        c0_hsteps_nogrp
                        let lk := sl.scratch.scratch_buf[(p + 1#64 + k.setWidth 64).toNat]'hpk_scr
                        let ark' := ark.set (cr + 3#64 + k.setWidth 64).toNat lk
                        refine wp_join_state (ts := []) (α := List (BitVec 32)) (fun _ => ())
                          (fun flk' mk' => flk'.length = c.max_vars ∧
                            (FullMem c { sl with core := { sl.core with
                              flags := flk', arena := ark', arena_len := cr0 + 3 + sz } } ⋆ R) mk')
                          (fun _ flk' mk' ⟨hflk', hmk'⟩ => by
                            c0_hsteps!
                            refine hLc (sz - (k + 1#32).toNat) (k + 1#32, ()) mk' (by omega)
                              ⟨flk', ark', by omega, rfl, hflk', by simp [ark', hark_len],
                               ?_, ?_, ?_, ?_, hmk'⟩
                            · intro i hi
                              dsimp only [ark']; rw [hack_nat, List.getElem?_set_ne (by omega)]
                              exact hark_hold i hi
                            · dsimp only [ark']; rw [hack_nat, List.getElem?_set_ne (by omega)]
                              exact hark0
                            · dsimp only [ark']; rw [hack_nat, List.getElem?_set_ne (by omega)]
                              exact hark2
                            · intro j hj
                              rw [hk1] at hj
                              dsimp only [ark']; rw [hack_nat]
                              by_cases hjk : j = k.toNat
                              · subst hjk
                                rw [List.getElem?_set_self (by rw [hark_len]; omega),
                                  List.getElem?_eq_getElem (by rw [hscrl]; omega)]
                                exact congrArg some (m6_getElem_congr hpk_nat _ _)
                              · rw [List.getElem?_set_ne (by omega)]; exact hark_cp j (by omega))
                          (fun Jfk hJfk => by
                            c0_hsplit
                            · have hvk_lt :
                                  ((lk >>> (1 : Nat)).setWidth 64).toNat < flk.length := by
                                have hmod : s.core.cur_vars % 2 ^ 64 = s.core.cur_vars :=
                                  Nat.mod_eq_of_lt (by omega)
                                rw [hmod] at hc
                                rw [hflk, m6_zext32_toNat, BitVec.toNat_ushiftRight,
                                  Nat.shiftRight_eq_div_pow]
                                have hdiv : lk.toNat / 2 < s.core.cur_vars := by
                                  have heq : sl.scratch.scratch_buf[(p.toNat + 1 + k.toNat) %
                                      2 ^ 64]'(by rw [hscrl]; omega) = lk :=
                                    m6_getElem_congr (by rw [hpk_nat, Nat.mod_eq_of_lt (by omega)])
                                      _ _
                                  simpa [heq, Nat.mod_eq_of_lt (by omega : p.toNat + 1 < 2 ^ 64)]
                                    using hc
                                omega
                              c0_hsteps_nogrp
                              refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
                                (fun x => (x, ())) (fun _ => True) ?_ ?_
                              · intro _ fv _
                                c0_hsteps!
                                exact hJfk _ _ ⟨by simp [hflk], hm⟩
                              · intro Jpk hJpk
                                c0_hsplit <;> (c0_hsteps!; exact hJpk _ trivial)
                            · c0_hsteps!; exact hJfk flk _ ⟨hflk, hm⟩)
                      · have hk_eq : k.toNat = sz := by
                          have hge : ¬ k.toNat < sz := hc
                          omega
                        rw [hk_eq] at hark_cp
                        let s2 : FullState :=
                          { sl with core := { sl.core with
                            flags := flk, arena := ark, arena_len := cr0 + 3 + sz } }
                        have hlen2 : s2.LengthsOk c :=
                          ⟨{ hcl with flags_len := hflk, arena_len_arr := hark_len,
                                      arena_len_le := hcr0_le }, hsl⟩
                        have hsz2_ar : (ark[cr0 + 2]?.getD 0#32).toNat = sz := by
                          rw [hark2]; exact hsz1s
                        have hs2_ar : cr0 + 3 + sz ≤ s2.core.arena.length := by
                          change cr0 + 3 + sz ≤ ark.length; rw [hark_len]; exact hcr0_le
                        have hs2_scr : p.toNat + 1 + sz ≤ sl.scratch.scratch_buf.length := by omega
                        have hlits_eq : fullArenaClauseLitsCore s2.core cr0 =
                            (List.range sz).map (fun j =>
                              (sl.scratch.scratch_buf[p.toNat + 1 + j]?.getD 0#32).toNat) :=
                          s12b_commit_arenaLits_eq_copied hs2_ar hs2_scr hsz2_ar hark_cp
                        have hns2 : (ark[cr0]?.getD 0#32 &&& 0x00800000#32) = 0#32 := by
                          rw [hark0]; exact hns1s
                        have hrefs2 : fullArenaClauseRefsCore s2.core =
                            fullArenaClauseRefsCore sl.core ++ [cr0] :=
                          fullArenaClauseRefsCore_append hinv.2.1.arena hsz_ge3 rfl
                            hark_hold hns2 hsz2_ar
                        have hwat2 : ModeWatchesInv F_cur s2.core :=
                          hinv.2.1.watches.with_wstk rfl rfl rfl rfl rfl
                            (fun r hr => by rw [hrefs2]; exact List.mem_append_left _ hr)
                        c0_hsteps_nogrp
                        -- Watch-push loop
                        refine wp_loop_group (ts := [i32])
                          (fun rem_w (kw, ()) mw =>
                            ∃ wvecw wstkw wlenw wuw wsortw,
                              kw.toNat ≤ sz ∧ rem_w = sz - kw.toNat ∧
                              let sw : FullState :=
                                { s2 with
                                  core := { s2.core with wvec := wvecw, wstk := wstkw,
                                                         wlen := wlenw, wusable := wuw }
                                  scratch := { s2.scratch with wsort := wsortw } }
                              sw.LengthsOk c ∧ ModeWatchesInv F_cur sw.core ∧
                              (FullMem c sw ⋆ R) mw)
                          ?_ ?_
                        · rintro Lw rem_w ⟨kw, ⟨⟩⟩ mw hLw
                            ⟨wvecw, wstkw, wlenw, wuw, wsortw, hkw_le, rfl, hlenw, hwatw, hmw⟩
                          c0_hsplit
                          · have hkw_lt : kw.toNat < sz := hc
                            have har_nat : (cr + 3#64 + kw.setWidth 64).toNat =
                                cr0 + 3 + kw.toNat := by rw [← hcr_nat]; c0_bound
                            have har_idx : (cr + 3#64 + kw.setWidth 64).toNat < ark.length := by
                              rw [har_nat, hark_len]; omega
                            let w0w := sz_bv &&& 0x7FFFFFFF#32
                            let cr32 := cr.setWidth 32
                            have hw0w_nat : w0w.toNat = sz := by
                              dsimp only [w0w]
                              rw [BitVec.toNat_and,
                                show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 from rfl,
                                Nat.and_two_pow_sub_one_eq_mod, show sz_bv.toNat = sz from rfl,
                                Nat.mod_eq_of_lt hsz_lt31]
                            have hw0w_ne : w0w ≠ 0xFFFFFFFF#32 := by
                              intro heq; have := congrArg BitVec.toNat heq; rw [hw0w_nat] at this
                              have : (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 := rfl; omega
                            have hw0w_msb : (w0w &&& 0x80000000#32) = 0#32 := by
                              dsimp only [w0w]
                              rw [BitVec.and_assoc,
                                show (0x7FFFFFFF#32 &&& 0x80000000#32) = 0#32 by decide,
                                BitVec.and_zero]
                            have hcr32_nat : cr32.toNat = cr0 := by
                              dsimp only [cr32]
                              rw [BitVec.toNat_setWidth, hcr_nat,
                                Nat.mod_eq_of_lt (by omega : cr0 < 2 ^ 32)]
                            have hcr32_ne : cr32 ≠ 0xFFFFFFFF#32 := by
                              intro heq; have := congrArg BitVec.toNat heq; rw [hcr32_nat] at this
                              have : (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 := rfl; omega
                            let sw : FullState :=
                              { s2 with
                                core := { s2.core with wvec := wvecw, wstk := wstkw,
                                                       wlen := wlenw, wusable := wuw }
                                scratch := { s2.scratch with wsort := wsortw } }
                            c0_hsteps_nogrp
                            s12b_call hWPush
                            refine ⟨c, sw, R, rfl, hlenw, hwatw.layout, (fun h => by cases h),
                              (fun _ => ⟨hw0w_ne, hcr32_ne⟩), hmw, ?_⟩
                            dsimp only
                            rintro okw wvec' wstk' wlen' wu' wsort' mw' hlenw' hlayw' hotherw
                              hokt hokf hm'
                            simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm]
                              at hotherw hokt hokf
                            have hwatw' : ModeWatchesInv F_cur
                                { sw.core with wvec := wvec', wstk := wstk',
                                               wlen := wlen', wusable := wu' } := by
                              refine FullBveVarHelpers.fullWatchPush_preserves_modeWatchesInv
                                (cnt := 2#32) hwatw hlayw'
                                rfl rfl (fun _ hr => hr) (fun h => by cases h) ?_ hotherw hokt
                                (fun hf => (hokf hf).1)
                              intro _
                              refine ⟨hw0w_msb, (fun _ => by
                                change 3 ≤ w0w.toNat; rw [hw0w_nat]; exact hsz_ge3),
                                (by rw [hcr32_nat]; omega), ?_⟩
                              change cr32.toNat ∈ fullArenaClauseRefsCore s2.core
                              rw [hcr32_nat, hrefs2]
                              exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
                            c0_hsplit
                            · have hkw1 : (kw + 1#32).toNat = kw.toNat + 1 := by c0_bound
                              c0_hsteps!
                              exact hLw (sz - (kw + 1#32).toNat) (kw + 1#32, ()) mw' (by omega)
                                ⟨wvec', wstk', wlen', wu', wsort', by omega, rfl,
                                 hlenw', hwatw', hm'⟩
                            · have har_cr_idx : cr0 < ark.length := by omega
                              have har_cr_bv : cr.toNat < ark.length := by
                                rw [hcr_nat]; exact har_cr_idx
                              c0_hsteps!
                              let ark_g := ark.set cr0 ((ark[cr0]'har_cr_idx) ||| 0x00080000#32)
                              let ag' := sw.core.arena_garbage + 3#64 + sz_bv.setWidth 64
                              have hinv_g := s12b_commit_res_garb_inv (ag' := ag') hinv hflk hsz_ge3
                                hark_len hark_hold hns2 hsz2_ar har_cr_idx hlenw' hwatw' hrefs2
                              refine hQ 2#64 _ _ hinv_g (htmk.congr rfl rfl) hcv_eq hfl_eq
                                (Or.inr (Or.inl rfl)) (fun h => by cases h) ?_
                              have har_g_eq :
                                  ark_g = ark.set cr.toNat ((ark[cr.toNat]'har_cr_bv) |||
                                    0x00080000#32) := by
                                simp only [ark_g, hcr_nat]
                              have hst_g : ({ sl with
                                core := { sl.core with
                                  flags := flk, arena := ark_g, arena_len := cr0 + 3 + sz,
                                  wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu',
                                  arena_garbage := ag', oom := 1#64 }
                                scratch := { sl.scratch with wsort := wsort' } } : FullState) =
                                { s2 with
                                  core := { s2.core with
                                    arena := ark.set cr.toNat
                                      ((ark[cr.toNat]'har_cr_bv) ||| 0x00080000#32),
                                    wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu',
                                    arena_garbage := sw.core.arena_garbage + 3#64 +
                                      sz_bv.setWidth 64,
                                    oom := 1#64 }
                                  scratch := { s2.scratch with wsort := wsort' } } := by
                                dsimp only [ag', s2, cr0]; rw [har_g_eq]
                              rw [hst_g]; exact hm
                          · c0_hsteps!
                            let s_fin : FullState :=
                              { sl with
                                core := { sl.core with
                                  flags := flk, arena := ark, arena_len := cr0 + 3 + sz,
                                  wvec := wvecw, wstk := wstkw, wlen := wlenw, wusable := wuw,
                                  num_irred := sl.core.num_irred + 1#64 }
                                scratch := { sl.scratch with wsort := wsortw } }
                            have hinv_c := s12b_commit_res_entailed_inv hinv hflk hsz_ge3 hlts hnd
                              hent hark_hold hns2 hsz2_ar hlits_eq hlenw hwatw
                            have hres_c := FullBveVarHelpers.FullResBufOkW.with_state
                              (s := sl) (s' := s_fin) rfl (fun _ _ => rfl) htail
                            exact hJnext s_fin _ ⟨hinv_c, htmk.congr rfl rfl, hcv_eq, hfl_eq,
                              hres_c, hm⟩
                        · intro Lw hLw; c0_hsteps!
                          exact hLw sz (0#32, ()) mk
                            ⟨sl.core.wvec, sl.core.wstk, sl.core.wlen, sl.core.wusable,
                             sl.scratch.wsort, Nat.zero_le _, by simp, hlen2, hwat2, hmk⟩
                    · intro Lc hLc; c0_hsteps!
                      refine hLc sz (0#32, ()) _
                        ⟨sl.core.flags, ar1s, Nat.zero_le _, by simp, hcl.flags_len,
                         by simp [ar1s, hlen1.core_ok.arena_len_arr], hhold1s, rfl, rfl,
                         (fun _ hj => by simp at hj), ?_⟩
                      have hcr_al : cr.toNat < ar1.length := by
                        rw [hcr_nat, hlen1.core_ok.arena_len_arr]; omega
                      have har1s_eq : ar1s = ar1.set cr.toNat ((ar1[cr.toNat]'hcr_al) |||
                          0x01000000#32) := by
                        dsimp only [ar1s]
                        have hval : ar1[cr0]'hcr_ar1 = ar1[cr.toNat]'hcr_al :=
                          (m6_getElem_congr hcr_nat hcr_al hcr_ar1).symm
                        rw [hval]
                        exact congrArg (fun idx => ar1.set idx _) hcr_nat.symm
                      rw [har1s_eq]
                      dsimp only [LeanQbe.T.Arg.val] at hm
                      exact hm))
    · c0_hsteps!
      exact hQ 1#64 sl ml (s12b_denseInvW_to_full hinv) htmk hcv_eq hfl_eq
        (Or.inl rfl) (fun h => by cases h) hm_lp
  · intro L hL; c0_hsteps!
    exact hL (r_end.toNat - r_off.toNat) (r_off, ()) m0
      ⟨s, s12b_denseInvW_of_full hinv0, htmk0, rfl, rfl, hle0, rfl, s12b_resBuf_to_bve hbuf0, hm0⟩

end LeanQbe.T.Examples.Kissat.FullFidelityStep12B
