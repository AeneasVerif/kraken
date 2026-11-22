module

public import LeanQbe.T.Examples.Kissat.FullM4Bva
public import LeanQbe.T.Examples.Kissat.FullBvaHeapLemmas2
public import LeanQbe.T.Logic.ControlComb
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` M4d BVA Proofs — Part 1 (`Specs, 3-Hop Shared Cache, Pick, Scan`)

Provides:
1. Upgraded matrix invariants `M4BvaRowEntryOk` (`3 ≤ sz ≤ 256`) and `M4BvaMatrixInv`
   (`16448 ≤ c.scratch_cap`, `step ≤ 32`, `qn ∈ [2..256]`, `qn_base = 32`, `row_base = 64`,
   `par_base = 8256`, stride `256`).
2. Specifications `m4BvaHop3Spec` (= `fullBvaHop2Spec`, shared `s1`/`s2` cache),
   `m4BvaScanCandsSpec` (`cur_qn ≤ 256`), `m4BvaFilterRowSpec`, and `m4BvaCommitSpec`.
3. Parametric `(Γ : Env)` `Func.wp` proofs for:
   - `FullM4Bva.full_bva_hop1_body` (`m4_bva_hop1_wp` → `fullBvaHop1Spec`)
   - `FullM4Bva.full_bva_hop2_body` (`m4_bva_hop2_wp` → `fullBvaHop2Spec`)
   - `FullM4Bva.full_bva_hop3_body` (`m4_bva_hop3_wp` → `m4BvaHop3Spec`)
   - `FullM4Bva.full_bva_pick_cand_body` (`m4_bva_pick_cand_wp` → `fullBvaPickCandSpec`)
   - `FullBvaHeap.full_bva_scan_cands_body` (`m4_bva_scan_cands_wp` → `m4BvaScanCandsSpec`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM4Bva

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapHelpers
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapTactics
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapScanHelpers
open Kraken.Bedrock2.Test
open scoped FullArenaTactics FullBvaHeapTactics

/-! ## 1. Upgraded M4d BVA Matrix Invariants & Specifications -/

/-- Soundness invariant for one entry `w` in an M4d BVA row with factor literal `fr`:
either a binary watch word `w = PW_BIN_FLAG | q` with residue `[q]`, or a live irredundant size
`3..256` arena clause ref containing `fr` with residue `(lits w).filter (· != fr)`. -/
def M4BvaRowEntryOk (F_cur : List (List Nat)) (s : FullState) (fr : Nat) (w : BitVec 32)
    (res : List Nat) : Prop :=
  if (w &&& 0x80000000#32) ≠ 0#32 then
    let q := (w &&& 0x7FFFFFFF#32).toNat
    q < 2 * s.core.cur_vars ∧ res = [q] ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [fr, q])
  else
    w.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s w.toNat = false ∧
    3 ≤ fullArenaClauseSize s w.toNat ∧ fullArenaClauseSize s w.toNat ≤ 256 ∧
    fr ∈ fullArenaClauseLits s w.toNat ∧
    res.Perm ((fullArenaClauseLits s w.toNat).filter (· != fr)) ∧
    (fullArenaClauseLits s w.toNat).Perm (fr :: res)

/-- Complete inductive invariant for the M4d `256 × 32` BVA scratch matrix over steps
`0 ..< step` (`1 ≤ step ≤ 32`): tracks `scr[0..step)` factor literals, `scr[32..32+step)` row
lengths `2..256`, `scr[64+r*256+m]` clauses, `scr[8256+r*256+m]` parent indices, and residue lists
`res` whose full Cartesian product with `scr[0..r]` is entailed by `F_cur`. -/
def M4BvaMatrixInv (c : FullCfg) (F_cur : List (List Nat)) (s : FullState) (step : Nat) : Prop :=
  16448 ≤ c.scratch_cap ∧ 1 ≤ step ∧ step ≤ 32 ∧
  (∀ r < step,
    let fr := (s.scratch.scratch_buf[r]?.getD 0#32).toNat
    let qn := (s.scratch.scratch_buf[32 + r]?.getD 0#32).toNat
    fr < 2 * s.core.cur_vars ∧ 2 ≤ qn ∧ qn ≤ 256 ∧
    ∀ m < qn, ∃ res : List Nat,
      (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
      M4BvaRowEntryOk F_cur s fr (s.scratch.scratch_buf[64 + r * 256 + m]?.getD 0#32) res ∧
      (∀ t ≤ r,
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res))) ∧
      (0 < r →
        let pi := (s.scratch.scratch_buf[8256 + r * 256 + m]?.getD 0#32).toNat
        pi < (s.scratch.scratch_buf[32 + (r - 1)]?.getD 0#32).toNat ∧
        M4BvaRowEntryOk F_cur s (s.scratch.scratch_buf[r - 1]?.getD 0#32).toNat
          (s.scratch.scratch_buf[64 + (r - 1) * 256 + pi]?.getD 0#32) res))

/-- Shared-cache 3-hop scorer spec (same shape as `fullBvaHop2Spec`: caller initializes and clears
`repr`/`sim_sig` memo tables via `min_clr`/`shrink_stk`). -/
abbrev m4BvaHop3Spec : Spec [i64, i32, i32] [i64] := fullBvaHop2Spec

/-- Upgraded candidate-scanner spec lifting `cur_qn ≤ 64` to `cur_qn ≤ 256`. -/
def m4BvaScanCandsSpec : Spec [i64, i32, i32, i64] [i32] :=
  fun (h, row_off, cur_qn, init_lits, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.cur_level = 0 ∧
      s.core.dense_mode ≠ 0#64 ∧
      init_lits.toNat ≤ 2 * s.core.cur_vars ∧
      (∀ l < 2 * c.max_vars, (s.core.lit_mark[l]?.getD 0#8 &&& 0xFE#8) = 0#8) ∧
      row_off.toNat + cur_qn.toNat ≤ c.scratch_cap ∧ cur_qn.toNat ≤ 256 ∧
      (∀ qi < cur_qn.toNat,
        let w := s.scratch.scratch_buf[row_off.toNat + qi]?.getD 0#32
        if (w &&& 0x80000000#32) ≠ 0#32 then (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars
        else w.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s w.toNat = false) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ncntd : BitVec 32) wsort' ws1' ws2' m',
        let s' : FullState :=
          { s with scratch :=
            { s.scratch with wsort := wsort', work_stk1 := ws1', work_stk2 := ws2' } }
        s'.LengthsOk c →
        ncntd.toNat ≤ init_lits.toNat →
        (∀ i < ncntd.toNat, (ws1'[i]?.getD 0#32).toNat < init_lits.toNat) →
        (FullMem c s' ⋆ R) m' → Q (ncntd, ()) m'

/-- Upgraded row-filter spec for the `256 × 32` (`16448`-word) matrix and `sz ∈ [3..256]`. -/
def m4BvaFilterRowSpec : Spec [i64, i32, i32, i32, i32, i32] [i32] :=
  fun (h, row_off, nrow_off, par_off, cur_qn, best_lit, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (R : Mem 64 → Prop) (step : Nat),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.cur_level = 0 ∧
      s.core.dense_mode ≠ 0#64 ∧
      1 ≤ step ∧ step < 32 ∧ 16448 ≤ c.scratch_cap ∧
      row_off.toNat = 64 + (step - 1) * 256 ∧
      nrow_off.toNat = 64 + step * 256 ∧
      par_off.toNat = 8256 + step * 256 ∧
      cur_qn.toNat = (s.scratch.scratch_buf[32 + (step - 1)]?.getD 0#32).toNat ∧
      best_lit.toNat < 2 * s.core.cur_vars ∧
      M4BvaMatrixInv c F_cur s step ∧
      (∀ l < 2 * c.max_vars, (s.core.lit_mark[l]?.getD 0#8 &&& 0xFE#8) = 0#8) ∧
      (∀ r < step, (s.core.lit_mark[(s.scratch.scratch_buf[r]?.getD 0#32).toNat]?.getD 0#8 &&&
        1#8) ≠ 0#8) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (new_qn : BitVec 32) sb' m',
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := sb' } }
        s'.LengthsOk c → new_qn.toNat ≤ 256 →
        (∀ idx < c.scratch_cap,
          ¬ (nrow_off.toNat ≤ idx ∧ idx < nrow_off.toNat + 256) →
          ¬ (par_off.toNat ≤ idx ∧ idx < par_off.toNat + 256) →
          sb'[idx]? = s.scratch.scratch_buf[idx]?) →
        (∀ nm < new_qn.toNat,
          let pi := (sb'[par_off.toNat + nm]?.getD 0#32).toNat
          pi < cur_qn.toNat ∧
          ∃ res : List Nat,
            (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
            M4BvaRowEntryOk F_cur s (s.scratch.scratch_buf[step - 1]?.getD 0#32).toNat
              (s.scratch.scratch_buf[row_off.toNat + pi]?.getD 0#32) res ∧
            M4BvaRowEntryOk F_cur s best_lit.toNat (sb'[nrow_off.toNat + nm]?.getD 0#32) res ∧
            (∀ t < step, (cnfOfClauses F_cur).EntailsClause
              (cnfClause ((s.scratch.scratch_buf[t]?.getD 0#32).toNat :: res))) ∧
            (cnfOfClauses F_cur).EntailsClause (cnfClause (best_lit.toNat :: res))) →
        (FullMem c s' ⋆ R) m' → Q (new_qn, ()) m'

/-- Upgraded commit spec for the `256 × 32` matrix and dynamic `need_ar`/`need_w`. -/
def m4BvaCommitSpec : Spec [i64, i32] [.bool] := fun (h, best_k, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧
    1 ≤ best_k.toNat ∧ best_k.toNat < 32 ∧
    M4BvaMatrixInv c F_cur s (best_k.toNat + 1) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) s' m',
      FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-! ## 2. Exact Shared-Cache 3-Hop Scorers (`m4_bva_hop1_wp`, `m4_bva_hop2_wp`, `m4_bva_hop3_wp`) -/

private theorem m4_hop_wvec_bounds {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvNoLm c F0 F_cur s) {sl : Nat}
    (hsl : sl < 2 * s.core.cur_vars) :
    fullWatchOffCore s.core sl + fullWatchSizeCore s.core sl ≤ s.core.wlen ∧
    DenseWatchSliceOk F_cur s.core sl (fullWatchOffCore s.core sl)
      (fullWatchSizeCore s.core sl) := by
  have hdw : DenseWatchesInv F_cur s.core := by
    have h := hinv.2.1.watches; unfold ModeWatchesInv at h
    rwa [ite_eq_right hinv.2.2.2.2.2] at h
  exact ⟨hdw.layout.bounds sl hsl, hdw.slices sl hsl⟩

theorem m4_bva_hop1_wp (Γ : Env) :
    ∀ args m Q X, fullBvaHop1Spec args m Q X → Func.wp Γ full_bva_hop1_body args m Q X := by
  rintro ⟨h, src_lit, dst_idx, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv, hsrc_lt, htc_le, hmclr_ok, hm, hQ⟩
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena
  unfold dimacsBound at hmx hwcap har_b
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hrepr_len := hcl.repr_len
  have hwv_len := hcl.wvec_len; have hws_len := hcl.wstk_len_arr; have har_len := hcl.arena_len_arr
  have hwlen_le := hcl.wlen_le; have hal_le := hcl.arena_len_le
  have hmclr_len := hcl.min_clr_len_arr
  have hsidx_lt : (src_lit >>> 1).toNat < s.core.cur_vars := by
    rw [bv32_lshr1_nat]; omega
  c0_hsteps_nogrp
  · exact hQ _ s.core.repr s.core.min_clr s.core.tmp_cnt s.scratch.ant_sz m
      hinv htc_le hmclr_ok (Nat.le_refl _) hm
  · refine wp_join_state1 (t := i64) (α := BitVec 64) (fun r => r) (fun _ ml => m = ml)
      (fun _ res0 ml hml => ?_) (fun J0 hJ0 => ?_)
    · rcases hml with rfl
      c0_hsteps_nogrp
      refine wp_loop_inv
        (fun (res, sgn, ()) ml => ∃ ant : BitVec 64,
          sgn.toNat ≤ 2 ∧ ant.toNat ≤ s.scratch.ant_sz.toNat ∧
          (FullMem c { s with scratch := { s.scratch with ant_sz := ant } } ⋆ R) ml)
        (fun (_, sgn, _) _ => 2 - sgn.toNat)
        (fun Js hJs => by
          c0_hsteps; exact hJs (res0, 0#32, ()) m ⟨s.scratch.ant_sz, by decide, Nat.le_refl _, hm⟩)
        (fun Js (res, sgn, ()) ml ⟨ant, hsgn_le, hant_le, hml⟩ ihs => ?_)
      c0_hsteps_nogrp
      refine wp_join_state0 (α := BitVec 64)
        (fun antF mf => antF.toNat ≤ s.scratch.ant_sz.toNat ∧
          (FullMem c { s with scratch := { s.scratch with ant_sz := antF } } ⋆ R) mf)
        (fun _ antF mf ⟨hantF, hmf⟩ => ?_)
        (fun Jend hJend => ?_)
      · -- Memo guard `if (h->ant_sz > 0ULL) { ... } return res;`
        c0_hsteps_nogrp
        refine wp_join_state1 (t := i64)
          (α := BitVec 64 × List (BitVec 32) × List (BitVec 32) × Nat) (fun st => st.1)
          (fun ⟨_resF, rpF, mcF, tcF⟩ mf1 =>
            FullDenseInvNoLm c F0 F_cur
              { core := { s.core with repr := rpF, min_clr := mcF, tmp_cnt := tcF }
                scratch := { s.scratch with ant_sz := antF } } ∧
            tcF ≤ s.core.cur_vars ∧
            (∀ i < tcF, (mcF[i]?.getD 0#32).toNat < c.max_vars) ∧
            (FullMem c
              { core := { s.core with repr := rpF, min_clr := mcF, tmp_cnt := tcF }
                scratch := { s.scratch with ant_sz := antF } } ⋆ R) mf1)
          (fun _ ⟨resF, rpF, mcF, tcF⟩ mf1 ⟨hinvF, htcF, hmcF, hmf1⟩ => by
            c0_hsteps; exact hQ resF rpF mcF tcF antF mf1 hinvF htcF hmcF hantF hmf1)
          (fun Jant hJant => ?_)
        c0_hsteps_nogrp
        · -- `antF > 0`: cap `res`, memoize into `s1[sidx]`, push to `st1`
          refine wp_join_state1 (t := i64) (α := BitVec 64) (fun r => r) (fun _ ml => mf = ml)
            (fun _ resC ml hml => ?_) (fun Jc hJc => ?_)
          · rcases hml with rfl
            c0_hsteps
            · have htc1 : s.core.tmp_cnt + 1 ≤ s.core.cur_vars := by c0_bound
              have hinv' : FullDenseInvNoLm c F0 F_cur
                  { core := { s.core with
                      repr := repr64Set s.core.repr (src_lit >>> 1).toNat (resC + 1)
                      min_clr := s.core.min_clr.set s.core.tmp_cnt (src_lit >>> 1)
                      tmp_cnt := s.core.tmp_cnt + 1 }
                    scratch := { s.scratch with ant_sz := antF } } :=
                fullDenseInvNoLm_with_core_aux hinv (by rw [repr64Set_length, hrepr_len])
                  (by simp [hmclr_len]) hcl.tmp_len_arr hcl.flags_len hcl.tmp_len_le
                  { hsc with } rfl rfl
              have hm' : (FullMem c
                  { core := { s.core with
                      repr := repr64Set s.core.repr (src_lit >>> 1).toNat (resC + 1)
                      min_clr := s.core.min_clr.set s.core.tmp_cnt (src_lit >>> 1)
                      tmp_cnt := s.core.tmp_cnt + 1 }
                    scratch := { s.scratch with ant_sz := antF } } ⋆ R) m := by
                have h1 : (BitVec.ofNat 64 s.core.tmp_cnt + 1).toNat = s.core.tmp_cnt + 1 := by
                  change (BitVec.ofNat 64 s.core.tmp_cnt + 1#64).toNat = _; c0_bound
                have h2 : (BitVec.ofNat 64 s.core.tmp_cnt).toNat = s.core.tmp_cnt := by c0_bound
                have h3 : (BitVec.setWidth 64 (src_lit >>> 1)).toNat = (src_lit >>> 1).toNat := by
                  c0_bound
                rw [h1, h2, h3] at hm; exact hm
              exact hJant ⟨resC, _, _, s.core.tmp_cnt + 1⟩ m ⟨hinv', htc1, fun i hi => by
                by_cases hie : i = s.core.tmp_cnt
                · subst hie; rw [List.getElem?_set_self (by omega), Option.getD_some]; omega
                · rw [List.getElem?_set_ne (Ne.symm hie)]; exact hmclr_ok i (by omega), hm'⟩
            · have hinv' : FullDenseInvNoLm c F0 F_cur
                  { core := { s.core with
                      repr := repr64Set s.core.repr (src_lit >>> 1).toNat (resC + 1) }
                    scratch := { s.scratch with ant_sz := antF } } :=
                fullDenseInvNoLm_with_core_aux hinv (by rw [repr64Set_length, hrepr_len])
                  hmclr_len hcl.tmp_len_arr hcl.flags_len hcl.tmp_len_le { hsc with } rfl rfl
              have hm' : (FullMem c
                  { core := { s.core with
                      repr := repr64Set s.core.repr (src_lit >>> 1).toNat (resC + 1) }
                    scratch := { s.scratch with ant_sz := antF } } ⋆ R) m := by
                have h3 : (BitVec.setWidth 64 (src_lit >>> 1)).toNat = (src_lit >>> 1).toNat := by
                  c0_bound
                rw [h3] at hm; exact hm
              exact hJant ⟨resC, _, s.core.min_clr, s.core.tmp_cnt⟩ m ⟨hinv', htc_le, hmclr_ok, hm'⟩
          · c0_hsteps
            · exact hJc 0x3FFFFFFFFFFFFFFF#64 mf rfl
            · exact hJc res mf rfl
        · -- `antF == 0`: skip memo write
          have hinv0 : FullDenseInvNoLm c F0 F_cur
              { core := s.core, scratch := { s.scratch with ant_sz := antF } } :=
            fullDenseInvNoLm_with_core_aux hinv hrepr_len hmclr_len hcl.tmp_len_arr hcl.flags_len
              hcl.tmp_len_le { hsc with } rfl rfl
          exact hJant ⟨res, s.core.repr, s.core.min_clr, s.core.tmp_cnt⟩ mf
            ⟨hinv0, htc_le, hmclr_ok, hmf⟩
      · c0_hsteps
        · have hsgn_lt : sgn.toNat < 2 := by c0_bound
          have hsl_nat : (((src_lit >>> (1 : Nat)) <<< (1 : Nat)) ||| sgn).toNat =
              2 * (src_lit >>> (1 : Nat)).toNat + sgn.toNat := by
            have hs01 : sgn.toNat = 0 ∨ sgn.toNat = 1 := by omega
            rcases hs01 with h0 | h1
            · have hs0 : sgn = 0#32 := BitVec.eq_of_toNat_eq h0; subst hs0
              rw [BitVec.or_zero]; c0_bound
            · have hs1 : sgn = 1#32 := BitVec.eq_of_toNat_eq h1; subst hs1
              rw [FullBvaFwdTactics.bv32_or1_of_even (by c0_bound)]; c0_bound
          have hsl_lt : (((src_lit >>> (1 : Nat)) <<< (1 : Nat)) ||| sgn).toNat <
              2 * s.core.cur_vars := by omega
          obtain ⟨hbd_sl, hslice_sl⟩ := m4_hop_wvec_bounds hinv hsl_lt
          let sl : BitVec 32 := ((src_lit >>> (1 : Nat)) <<< (1 : Nat)) ||| sgn
          have hsl_lt_sl : sl.toNat < 2 * s.core.cur_vars := hsl_lt
          have hwv_sl0 : (BitVec.setWidth 64 sl <<< (1 : Nat)).toNat < s.core.wvec.length := by
            c0_bound
          have hwv_sl1 : ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1).toNat <
              s.core.wvec.length := by
            change ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1#64).toNat < _; c0_bound
          have hoff_eq : (s.core.wvec[2 * sl.toNat]'(by omega)).toNat =
              fullWatchOffCore s.core sl.toNat := by
            unfold fullWatchOffCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          have hsz_eq : (s.core.wvec[2 * sl.toNat + 1]'(by omega)).toNat =
              fullWatchSizeCore s.core sl.toNat := by
            unfold fullWatchSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          let off0 := fullWatchOffCore s.core sl.toNat
          let sz0 := fullWatchSizeCore s.core sl.toNat
          have hoff_sz_le : off0 + sz0 ≤ s.core.wlen := hbd_sl
          have h2sl0 : (BitVec.setWidth 64 sl <<< (1 : Nat)).toNat = 2 * sl.toNat := by c0_bound
          have h2sl1 : ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1).toNat = 2 * sl.toNat + 1 := by
            change ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1#64).toNat = _; c0_bound
          have hoff_c0 : (BitVec.setWidth 64
              (s.core.wvec[(BitVec.setWidth 64 sl <<< (1 : Nat)).toNat]'hwv_sl0)).toNat = off0 := by
            rw [bv64_setWidth_32]; simp only [h2sl0]; exact hoff_eq
          have hmod0 : 2 * sl.toNat % 2 ^ 64 = 2 * sl.toNat := Nat.mod_eq_of_lt (by omega)
          have hmod1 : (2 * sl.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = 2 * sl.toNat + 1 :=
            by c0_bound
          have hend_mod : ((s.core.wvec[2 * sl.toNat % 2 ^ 64]'(by rw [hmod0]; omega)).toNat +
              (s.core.wvec[(2 * sl.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                rw [hmod1]; omega)).toNat) % 2 ^ 64 = off0 + sz0 := by
            simp only [hmod0, hmod1, hoff_eq, hsz_eq]; exact Nat.mod_eq_of_lt (by omega)
          c0_hsteps_nogrp
          refine wp_loop_inv
            (fun (res1, p, ()) mlp => ∃ antp : BitVec 64,
              off0 ≤ p.toNat ∧ p.toNat ≤ off0 + sz0 ∧ antp.toNat ≤ ant.toNat ∧
              DenseWatchSliceOk F_cur s.core sl.toNat p.toNat (off0 + sz0 - p.toNat) ∧
              (FullMem c { s with scratch := { s.scratch with ant_sz := antp } } ⋆ R) mlp)
            (fun (_, p, _) _ => off0 + sz0 - p.toNat)
            (fun Jp hJp => by
              c0_hfast
              exact hJp (res, _, ()) ml ⟨ant, by rw [hoff_c0]; exact Nat.le_refl _,
                by rw [hoff_c0]; omega, Nat.le_refl _,
                by rw [hoff_c0, Nat.add_sub_cancel_left]; exact hslice_sl, hml⟩)
            (fun Jp (res1, p, ()) mlp ⟨antp, hp_ge, hp_le, hantp_le, hrem, hmlp⟩ ihp => ?_)
          c0_hfast
          · have hp_lt : p.toNat < off0 + sz0 := by rw [← hend_mod]; assumption
            have hp_ws : p.toNat < s.core.wstk.length := by omega
            have hant1 : (antp - 1#64).toNat ≤ ant.toNat := by simp only [bv_c0]; omega
            have hp1_n : (p + 1).toNat = p.toNat + 1 := by
              change (p + 1#64).toNat = _; simp only [bv_c0]; omega
            have hp1_mod : (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = p.toNat + 1 := by
              rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega
            c0_hfast
            · have ⟨_, _, hrem_next⟩ := FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega) hp_ws
                (by assumption)
              exact ihp (_, p + 1, ()) m (by dsimp only; rw [hp1_n]; omega)
                ⟨antp - 1#64, by rw [hp1_n]; omega, by rw [hp1_n]; omega, hant1,
                 by rw [hp1_n, show off0 + sz0 - (p.toNat + 1) = off0 + sz0 - p.toNat - 1 by omega]
                    exact hrem_next, hm⟩
            · have ⟨_, _, hrem_next⟩ := FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega) hp_ws
                (by assumption)
              exact ihp (_, p + 1, ()) m (by dsimp only; rw [hp1_n]; omega)
                ⟨antp - 1#64, by rw [hp1_n]; omega, by rw [hp1_n]; omega, hant1,
                 by rw [hp1_n, show off0 + sz0 - (p.toNat + 1) = off0 + sz0 - p.toNat - 1 by omega]
                    exact hrem_next, hm⟩
            · have hm_flat : (FullMem c
                  { s with scratch := { s.scratch with ant_sz := antp - 1#64 } } ⋆ R) m := hm
              clear hm
              have ⟨h2le, hrem_next⟩ := FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hp_ws
                (by assumption)
              have hp1_ws : p.toNat + 1 < s.core.wstk.length := by omega
              have ⟨_, hcr_ref, _⟩ := FullBvaFwdHelpers.fwd_slice_occ_info hrem (by omega) hp_ws
                hp1_ws (by assumption)
              have hcr_wf := hinv.2.1.arena.refs_wf _ hcr_ref
              have hp2_n : (p + 1 + 1).toNat = p.toNat + 2 := by
                change (p + 1#64 + 1#64).toNat = _; simp only [bv_c0]; omega
              let cr := s.core.wstk[p.toNat + 1]'hp1_ws
              have hcr_al : cr.toNat + 3 + fullArenaClauseSizeCore s.core cr.toNat ≤
                  s.core.arena_len := by
                have h1 := hcr_wf.2.2.1; have h2 := hcr_wf.2.2.2.1; dsimp only [cr]; omega
              have hcr_eq : s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws) = cr := by
                dsimp only [cr]; simp only [hp1_n]
              have hcr0_eq : (BitVec.setWidth 64
                  (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws))).toNat = cr.toNat := by
                rw [bv64_setWidth_32, hcr_eq]
              have hcr_b0 : (BitVec.setWidth 64
                  (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws))).toNat <
                  s.core.arena.length := by rw [hcr0_eq]; omega
              have hcr2_eq : (BitVec.setWidth 64
                  (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 2).toNat =
                  cr.toNat + 2 := by
                change (BitVec.setWidth 64 _ + 2#64).toNat = _
                rw [hcr_eq]; simp only [bv_c0]; omega
              have hcr_b2 : (BitVec.setWidth 64
                  (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 2).toNat <
                  s.core.arena.length := by rw [hcr2_eq]; omega
              have hsz_cr : (s.core.arena[cr.toNat + 2]'(by omega)).toNat =
                  fullArenaClauseSizeCore s.core cr.toNat := by
                unfold fullArenaClauseSizeCore
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
              have hcr_sz_le : cr.toNat + 3 + (s.core.arena[cr.toNat + 2]'(by omega)).toNat ≤
                  s.core.arena.length := by rw [hsz_cr]; omega
              c0_hfast
              · clear hQ ihs hJend
                refine wp_loop_inv
                  (fun (resk, k, ()) mk =>
                    k.toNat ≤ (s.core.arena[cr.toNat + 2]'(by omega)).toNat ∧ mk = m)
                  (fun (_, k, _) _ => (s.core.arena[cr.toNat + 2]'(by omega)).toNat - k.toNat)
                  (fun Jk hJk => by c0_hfast; exact hJk (res1, 0#32, ()) m ⟨Nat.zero_le _, rfl⟩)
                  (fun Jk (resk, k, ()) mk ⟨hk_le, hmk⟩ ihk => ?_)
                subst hmk; c0_hsplit
                · have hk_lt : k.toNat < (s.core.arena[cr.toNat + 2]'(by omega)).toNat := by
                    have h1 : k.toNat < (s.core.arena[(BitVec.setWidth 64
                        (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) +
                        2).toNat]'hcr_b2).toNat := by assumption
                    simpa only [hcr2_eq] using h1
                  have hcrk_b : (BitVec.setWidth 64
                      (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 3 +
                      BitVec.setWidth 64 k).toNat < s.core.arena.length := by
                    change (BitVec.setWidth 64 _ + 3#64 + BitVec.setWidth 64 k).toNat < _
                    rw [hcr_eq]; simp only [bv_c0]; omega
                  have hk1 : (k + 1#32).toNat = k.toNat + 1 := by simp only [bv_c0]; omega
                  c0_hfast
                  all_goals
                    exact ihk (_, k + 1#32, ()) mk (by dsimp only; rw [hk1]; omega)
                      ⟨by rw [hk1]; omega, rfl⟩
                · c0_hfast
                  exact ihp (resk, p + 1 + 1, ()) mk (by dsimp only; rw [hp2_n]; omega)
                    ⟨antp - 1#64, by rw [hp2_n]; omega, by rw [hp2_n]; omega, hant1,
                     by rw [hp2_n, show off0 + sz0 - (p.toNat + 2) = off0 + sz0 - p.toNat - 2
                          by omega]; exact hrem_next, hm_flat⟩
              · exact ihp (res1, p + 1 + 1, ()) m (by dsimp only; rw [hp2_n]; omega)
                  ⟨antp - 1#64, by rw [hp2_n]; omega, by rw [hp2_n]; omega, hant1,
                   by rw [hp2_n, show off0 + sz0 - (p.toNat + 2) = off0 + sz0 - p.toNat - 2
                        by omega]; exact hrem_next, hm_flat⟩
            · exfalso
              have ⟨h2le, _⟩ := FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hp_ws
                (by assumption)
              have hge : ¬ (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 <
                  ((s.core.wvec[2 * sl.toNat % 2 ^ 64]'(by rw [hmod0]; omega)).toNat +
                   (s.core.wvec[(2 * sl.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                     rw [hmod1]; omega)).toNat) % 2 ^ 64 := by assumption
              rw [hend_mod, hp1_mod] at hge; omega
          all_goals
            exact ihs (res1, sgn + 1#32, ()) mlp (by simp only [bv_c0]; omega)
              ⟨antp, by simp only [bv_c0]; omega, Nat.le_trans hantp_le hant_le, hmlp⟩
        · exact hJend ant ml ⟨hant_le, hml⟩
        · exact hJend ant ml ⟨hant_le, hml⟩
    · c0_hsteps
      · exact hJ0 1#64 m rfl
      · exact hJ0 0#64 m rfl

theorem m4_bva_hop2_wp (Γ : Env)
    (hHop1 : ∀ args m Q X, fullBvaHop1Spec args m Q X →
      Γ "full_bva_hop1" [i64, i32, i32] [i64] args m Q X) :
    ∀ args m Q X, fullBvaHop2Spec args m Q X → Func.wp Γ full_bva_hop2_body args m Q X := by
  rintro ⟨h, src_lit, dst_idx, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv, hsrc_lt, htc_le, htl_le, hmclr_ok, hshrk_ok, hm, hQ⟩
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena
  unfold dimacsBound at hmx hwcap har_b
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hsig_len := hsc.sim_sig_len
  have hshrk_len := hsc.shrink_stk_len
  have hwv_len := hcl.wvec_len; have hws_len := hcl.wstk_len_arr; have har_len := hcl.arena_len_arr
  have hwlen_le := hcl.wlen_le; have hal_le := hcl.arena_len_le
  have hsidx_lt : (src_lit >>> 1).toNat < s.core.cur_vars := by rw [bv32_lshr1_nat]; omega
  c0_hsteps_nogrp
  · exact hQ _ s.core.repr s.core.min_clr s.core.tmp_cnt s.core.tmp_len s.scratch.ant_sz
      s.scratch.sim_sig s.scratch.shrink_stk m hinv htc_le htl_le hmclr_ok hshrk_ok
      (Nat.le_refl _) hm
  · refine wp_join_state1 (t := i64) (α := BitVec 64) (fun r => r) (fun _ ml => m = ml)
      (fun _ res0 ml hml => ?_) (fun J0 hJ0 => ?_)
    · rcases hml with rfl
      c0_hsteps_nogrp
      let mkSt (rp mc : List (BitVec 32)) (tc : Nat) (ant : BitVec 64) : FullState :=
        { core := { s.core with repr := rp, min_clr := mc, tmp_cnt := tc }
          scratch := { s.scratch with ant_sz := ant } }
      refine wp_loop_inv
        (fun (res, sgn, ()) ml => ∃ rp mc tc ant,
          sgn.toNat ≤ 2 ∧ tc ≤ s.core.cur_vars ∧ ant.toNat ≤ s.scratch.ant_sz.toNat ∧
          FullDenseInvNoLm c F0 F_cur (mkSt rp mc tc ant) ∧
          (∀ i < tc, (mc[i]?.getD 0#32).toNat < c.max_vars) ∧
          (FullMem c (mkSt rp mc tc ant) ⋆ R) ml)
        (fun (_, sgn, _) _ => 2 - sgn.toNat)
        (fun Js hJs => by
          c0_hsteps; exact hJs (res0, 0#32, ()) m
            ⟨s.core.repr, s.core.min_clr, s.core.tmp_cnt, s.scratch.ant_sz, by decide, htc_le,
             Nat.le_refl _, hinv, hmclr_ok, hm⟩)
        (fun Js (res, sgn, ()) ml
            ⟨rp, mc, tc, ant, hsgn_le, htc, hant, hinv_s, hmc_ok, hml⟩ ihs => ?_)
      c0_hsteps_nogrp
      refine wp_join_state0
        (α := List (BitVec 32) × List (BitVec 32) × Nat × BitVec 64)
        (fun ⟨rpF, mcF, tcF, antF⟩ mf =>
          tcF ≤ s.core.cur_vars ∧ antF.toNat ≤ s.scratch.ant_sz.toNat ∧
          FullDenseInvNoLm c F0 F_cur (mkSt rpF mcF tcF antF) ∧
          (∀ i < tcF, (mcF[i]?.getD 0#32).toNat < c.max_vars) ∧
          (FullMem c (mkSt rpF mcF tcF antF) ⋆ R) mf)
        (fun _ ⟨rpF, mcF, tcF, antF⟩ mf ⟨htcF, hantF, hinvF, hmcF, hmf⟩ => ?_)
        (fun Jend hJend => ?_)
      · -- Memo guard `if (h->ant_sz > 0ULL) { ... } return res;`
        dsimp only [mkSt] at hmf hinvF
        c0_hsteps_nogrp
        refine wp_join_state1 (t := i64)
          (α := BitVec 64 × Nat × List (BitVec 64) × List (BitVec 32)) (fun st => st.1)
          (fun ⟨_resF, tlF, sigF, shrkF⟩ mf1 =>
            FullDenseInvNoLm c F0 F_cur
              { core := { s.core with repr := rpF, min_clr := mcF, tmp_cnt := tcF,
                                      tmp_len := tlF }
                scratch := { s.scratch with ant_sz := antF, sim_sig := sigF,
                                            shrink_stk := shrkF } } ∧
            tlF ≤ s.core.cur_vars ∧
            (∀ i < tlF, (shrkF[i]?.getD 0#32).toNat < c.max_vars) ∧
            (FullMem c
              { core := { s.core with repr := rpF, min_clr := mcF, tmp_cnt := tcF,
                                      tmp_len := tlF }
                scratch := { s.scratch with ant_sz := antF, sim_sig := sigF,
                                            shrink_stk := shrkF } } ⋆ R) mf1)
          (fun _ ⟨resF, tlF, sigF, shrkF⟩ mf1 ⟨hinv1, htl1, hshrk1, hmf1⟩ => by
            c0_hsteps
            exact hQ resF rpF mcF tcF tlF antF sigF shrkF mf1 hinv1 htcF htl1 hmcF hshrk1 hantF
              hmf1)
          (fun Jant hJant => ?_)
        c0_hsteps_nogrp
        · refine wp_join_state1 (t := i64) (α := BitVec 64) (fun r => r) (fun _ ml => mf = ml)
            (fun _ resC ml hml => ?_) (fun Jc hJc => ?_)
          · rcases hml with rfl
            c0_hsteps
            · have htl1 : s.core.tmp_len + 1 ≤ s.core.cur_vars := by c0_bound
              let sc1 : FullScratch :=
                { s.scratch with
                  ant_sz := antF
                  sim_sig := s.scratch.sim_sig.set (src_lit >>> 1).toNat (resC + 1)
                  shrink_stk := s.scratch.shrink_stk.set s.core.tmp_len (src_lit >>> 1) }
              have hinv' := fullDenseInvNoLm_with_core_aux (tc' := tcF) (tl' := s.core.tmp_len + 1)
                (sc' := sc1) hinvF hinvF.1.core_ok.repr_len hinvF.1.core_ok.min_clr_len_arr
                hcl.tmp_len_arr hcl.flags_len (by omega)
                { hsc with sim_sig_len := by simp [sc1, hsig_len],
                           shrink_stk_len := by simp [sc1, hshrk_len] }
                rfl rfl
              have hm' : (FullMem c
                  { core := { s.core with repr := rpF, min_clr := mcF, tmp_cnt := tcF,
                                          tmp_len := s.core.tmp_len + 1 }
                    scratch := sc1 } ⋆ R) m := by
                have h1 : (BitVec.ofNat 64 s.core.tmp_len + 1).toNat = s.core.tmp_len + 1 := by
                  change (BitVec.ofNat 64 s.core.tmp_len + 1#64).toNat = _; c0_bound
                have h2 : (BitVec.ofNat 64 s.core.tmp_len).toNat = s.core.tmp_len := by c0_bound
                have h3 : (BitVec.setWidth 64 (src_lit >>> 1)).toNat = (src_lit >>> 1).toNat := by
                  c0_bound
                dsimp only [sc1]; rw [h1, h2, h3] at hm; exact hm
              exact hJant ⟨resC, s.core.tmp_len + 1, _, _⟩ m
                ⟨by dsimp only [sc1] at hinv'; exact hinv', htl1, fun i hi => by
                  by_cases hie : i = s.core.tmp_len
                  · subst hie; rw [List.getElem?_set_self (by omega), Option.getD_some]; omega
                  · rw [List.getElem?_set_ne (Ne.symm hie)]; exact hshrk_ok i (by omega), hm'⟩
            · let sc2 : FullScratch :=
                { s.scratch with
                  ant_sz := antF
                  sim_sig := s.scratch.sim_sig.set (src_lit >>> 1).toNat (resC + 1) }
              have hinv' := fullDenseInvNoLm_with_core_aux (tc' := tcF) (tl' := s.core.tmp_len)
                (sc' := sc2) hinvF hinvF.1.core_ok.repr_len hinvF.1.core_ok.min_clr_len_arr
                hcl.tmp_len_arr hcl.flags_len hcl.tmp_len_le
                { hsc with sim_sig_len := by simp [sc2, hsig_len] } rfl rfl
              have hm' : (FullMem c
                  { core := { s.core with repr := rpF, min_clr := mcF, tmp_cnt := tcF }
                    scratch := sc2 } ⋆ R) m := by
                have h3 : (BitVec.setWidth 64 (src_lit >>> 1)).toNat = (src_lit >>> 1).toNat := by
                  c0_bound
                dsimp only [sc2]; rw [h3] at hm; exact hm
              exact hJant ⟨resC, s.core.tmp_len, _, s.scratch.shrink_stk⟩ m
                ⟨by dsimp only [sc2] at hinv'; exact hinv', htl_le, hshrk_ok, hm'⟩
          · c0_hsteps
            · exact hJc 0x3FFFFFFFFFFFFFFF#64 mf rfl
            · exact hJc res mf rfl
        · exact hJant ⟨res, s.core.tmp_len, s.scratch.sim_sig, s.scratch.shrink_stk⟩ mf
            ⟨hinvF, htl_le, hshrk_ok, hmf⟩
      · dsimp only [mkSt] at hml
        c0_hsteps
        · have hsgn_lt : sgn.toNat < 2 := by c0_bound
          have hsl_nat : (((src_lit >>> (1 : Nat)) <<< (1 : Nat)) ||| sgn).toNat =
              2 * (src_lit >>> (1 : Nat)).toNat + sgn.toNat := by
            have hs01 : sgn.toNat = 0 ∨ sgn.toNat = 1 := by omega
            rcases hs01 with h0 | h1
            · have hs0 : sgn = 0#32 := BitVec.eq_of_toNat_eq h0; subst hs0
              rw [BitVec.or_zero]; c0_bound
            · have hs1 : sgn = 1#32 := BitVec.eq_of_toNat_eq h1; subst hs1
              rw [FullBvaFwdTactics.bv32_or1_of_even (by c0_bound)]; c0_bound
          have hsl_lt : (((src_lit >>> (1 : Nat)) <<< (1 : Nat)) ||| sgn).toNat <
              2 * s.core.cur_vars := by omega
          obtain ⟨hbd_sl, hslice_sl⟩ := m4_hop_wvec_bounds hinv hsl_lt
          let sl : BitVec 32 := ((src_lit >>> (1 : Nat)) <<< (1 : Nat)) ||| sgn
          have hsl_lt_sl : sl.toNat < 2 * s.core.cur_vars := hsl_lt
          have hwv_sl0 : (BitVec.setWidth 64 sl <<< (1 : Nat)).toNat < s.core.wvec.length := by
            c0_bound
          have hwv_sl1 : ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1).toNat <
              s.core.wvec.length := by
            change ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1#64).toNat < _; c0_bound
          have hoff_eq : (s.core.wvec[2 * sl.toNat]'(by omega)).toNat =
              fullWatchOffCore s.core sl.toNat := by
            unfold fullWatchOffCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          have hsz_eq : (s.core.wvec[2 * sl.toNat + 1]'(by omega)).toNat =
              fullWatchSizeCore s.core sl.toNat := by
            unfold fullWatchSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          let off0 := fullWatchOffCore s.core sl.toNat
          let sz0 := fullWatchSizeCore s.core sl.toNat
          have hoff_sz_le : off0 + sz0 ≤ s.core.wlen := hbd_sl
          have h2sl0 : (BitVec.setWidth 64 sl <<< (1 : Nat)).toNat = 2 * sl.toNat := by c0_bound
          have h2sl1 : ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1).toNat = 2 * sl.toNat + 1 := by
            change ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1#64).toNat = _; c0_bound
          have hoff_c0 : (BitVec.setWidth 64
              (s.core.wvec[(BitVec.setWidth 64 sl <<< (1 : Nat)).toNat]'hwv_sl0)).toNat = off0 := by
            rw [bv64_setWidth_32]; simp only [h2sl0]; exact hoff_eq
          have hmod0 : 2 * sl.toNat % 2 ^ 64 = 2 * sl.toNat := Nat.mod_eq_of_lt (by omega)
          have hmod1 : (2 * sl.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = 2 * sl.toNat + 1 :=
            by c0_bound
          have hend_mod : ((s.core.wvec[2 * sl.toNat % 2 ^ 64]'(by rw [hmod0]; omega)).toNat +
              (s.core.wvec[(2 * sl.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                rw [hmod1]; omega)).toNat) % 2 ^ 64 = off0 + sz0 := by
            simp only [hmod0, hmod1, hoff_eq, hsz_eq]; exact Nat.mod_eq_of_lt (by omega)
          c0_hsteps_nogrp
          refine wp_loop_inv
            (fun (res1, p, ()) mlp => ∃ rpp mcp tcp antp,
              off0 ≤ p.toNat ∧ p.toNat ≤ off0 + sz0 ∧ tcp ≤ s.core.cur_vars ∧
              antp.toNat ≤ ant.toNat ∧ FullDenseInvNoLm c F0 F_cur (mkSt rpp mcp tcp antp) ∧
              (∀ i < tcp, (mcp[i]?.getD 0#32).toNat < c.max_vars) ∧
              DenseWatchSliceOk F_cur s.core sl.toNat p.toNat (off0 + sz0 - p.toNat) ∧
              (FullMem c (mkSt rpp mcp tcp antp) ⋆ R) mlp)
            (fun (_, p, _) _ => off0 + sz0 - p.toNat)
            (fun Jp hJp => by
              c0_hfast
              exact hJp (res, _, ()) ml ⟨rp, mc, tc, ant, by rw [hoff_c0]; exact Nat.le_refl _,
                by rw [hoff_c0]; omega, htc, Nat.le_refl _, hinv_s, hmc_ok,
                by rw [hoff_c0, Nat.add_sub_cancel_left]; exact hslice_sl, hml⟩)
            (fun Jp (res1, p, ()) mlp ⟨rpp, mcp, tcp, antp, hp_ge, hp_le, htcp, hantp, hinvp,
                hmcp_ok, hrem, hmlp⟩ ihp => ?_)
          dsimp only [mkSt] at hmlp
          c0_hfast
          · have hp_lt : p.toNat < off0 + sz0 := by rw [← hend_mod]; assumption
            have hp_ws : p.toNat < s.core.wstk.length := by omega
            have hant1 : (antp - 1#64).toNat ≤ ant.toNat := by simp only [bv_c0]; omega
            have hp1_n : (p + 1).toNat = p.toNat + 1 := by
              change (p + 1#64).toNat = _; simp only [bv_c0]; omega
            have hp1_mod : (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = p.toNat + 1 := by
              rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega
            have hinvp1 : FullDenseInvNoLm c F0 F_cur (mkSt rpp mcp tcp (antp - 1#64)) :=
              fullDenseInvNoLm_with_core_aux (tc' := tcp) (tl' := s.core.tmp_len) hinvp
                hinvp.1.core_ok.repr_len hinvp.1.core_ok.min_clr_len_arr hcl.tmp_len_arr
                hcl.flags_len hcl.tmp_len_le { hsc with } rfl rfl
            c0_hfast
            · have ⟨hot_lt, _, hrem_next⟩ :=
                FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega) hp_ws (by assumption)
              c0_call hHop1
              refine ⟨c, F0, F_cur, mkSt rpp mcp tcp (antp - 1#64), R, rfl, hinvp1, hot_lt, htcp,
                hmcp_ok, hm, fun r1 rp1 mc1 tc1 ant1 m1 hinv1 htc1 hmc1 hant1' hm1 => ?_⟩
              c0_hfast
              exact ihp (res1 + r1, p + 1, ()) m1 (by dsimp only; rw [hp1_n]; omega)
                ⟨rp1, mc1, tc1, ant1, by rw [hp1_n]; omega, by rw [hp1_n]; omega, htc1,
                 Nat.le_trans hant1' hant1, hinv1, hmc1,
                 by rw [hp1_n, show off0 + sz0 - (p.toNat + 1) = off0 + sz0 - p.toNat - 1 by omega]
                    exact hrem_next, hm1⟩
            · have hm_flat : (FullMem c
                  { core := { s.core with repr := rpp, min_clr := mcp, tmp_cnt := tcp },
                    scratch := { s.scratch with ant_sz := antp - 1#64 } } ⋆ R) m := hm
              clear hm
              have ⟨h2le, hrem_next⟩ := FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hp_ws
                (by assumption)
              have hp1_ws : p.toNat + 1 < s.core.wstk.length := by omega
              have ⟨_, hcr_ref, _⟩ := FullBvaFwdHelpers.fwd_slice_occ_info hrem (by omega) hp_ws
                hp1_ws (by assumption)
              have hcr_wf := hinv.2.1.arena.refs_wf _ hcr_ref
              have hp2_n : (p + 1 + 1).toNat = p.toNat + 2 := by
                change (p + 1#64 + 1#64).toNat = _; simp only [bv_c0]; omega
              let cr := s.core.wstk[p.toNat + 1]'hp1_ws
              have hcr_al : cr.toNat + 3 + fullArenaClauseSizeCore s.core cr.toNat ≤
                  s.core.arena_len := by
                have h1 := hcr_wf.2.2.1; have h2 := hcr_wf.2.2.2.1; dsimp only [cr]; omega
              have hcr_eq : s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws) = cr := by
                dsimp only [cr]; simp only [hp1_n]
              have hcr0_eq : (BitVec.setWidth 64
                  (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws))).toNat = cr.toNat := by
                rw [bv64_setWidth_32, hcr_eq]
              have hcr_b0 : (BitVec.setWidth 64
                  (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws))).toNat <
                  s.core.arena.length := by rw [hcr0_eq]; omega
              have hcr2_eq : (BitVec.setWidth 64
                  (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 2).toNat =
                  cr.toNat + 2 := by
                change (BitVec.setWidth 64 _ + 2#64).toNat = _
                rw [hcr_eq]; simp only [bv_c0]; omega
              have hcr_b2 : (BitVec.setWidth 64
                  (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 2).toNat <
                  s.core.arena.length := by rw [hcr2_eq]; omega
              have hsz_cr : (s.core.arena[cr.toNat + 2]'(by omega)).toNat =
                  fullArenaClauseSizeCore s.core cr.toNat := by
                unfold fullArenaClauseSizeCore
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
              have hcr_sz_le : cr.toNat + 3 + (s.core.arena[cr.toNat + 2]'(by omega)).toNat ≤
                  s.core.arena.length := by rw [hsz_cr]; omega
              c0_hfast
              · have hng_cr : fullArenaClauseGarbCore s.core cr.toNat = false := by
                  unfold fullArenaClauseGarbCore fullArenaHdrCore
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                  have h1 : s.core.arena[(BitVec.setWidth 64
                      (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws))).toNat]'hcr_b0 &&&
                      (524288#32 ||| 4194304#32) = 0#32 := by assumption
                  exact FullBvaFwdHelpers.garb_false_of_and_garb_red_eq_zero (by
                    simpa only [hcr0_eq] using h1)
                clear hQ ihs hJend
                refine wp_loop_inv
                  (fun (resk, k, ()) mk => ∃ rpk mck tck antk,
                    k.toNat ≤ (s.core.arena[cr.toNat + 2]'(by omega)).toNat ∧
                    tck ≤ s.core.cur_vars ∧ antk.toNat ≤ ant.toNat ∧
                    FullDenseInvNoLm c F0 F_cur (mkSt rpk mck tck antk) ∧
                    (∀ i < tck, (mck[i]?.getD 0#32).toNat < c.max_vars) ∧
                    (FullMem c (mkSt rpk mck tck antk) ⋆ R) mk)
                  (fun (_, k, _) _ => (s.core.arena[cr.toNat + 2]'(by omega)).toNat - k.toNat)
                  (fun Jk hJk => by
                    c0_hfast; exact hJk (res1, 0#32, ()) m
                      ⟨rpp, mcp, tcp, antp - 1#64, Nat.zero_le _, htcp, hant1, hinvp1, hmcp_ok,
                       hm_flat⟩)
                  (fun Jk (resk, k, ()) mk ⟨rpk, mck, tck, antk, hk_le, htck, hantk, hinvk,
                      hmck_ok, hmk⟩ ihk => ?_)
                dsimp only [mkSt] at hmk
                c0_hsplit
                · have hk_lt : k.toNat < (s.core.arena[cr.toNat + 2]'(by omega)).toNat := by
                    have h1 : k.toNat < (s.core.arena[(BitVec.setWidth 64
                        (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) +
                        2).toNat]'hcr_b2).toNat := by assumption
                    simpa only [hcr2_eq] using h1
                  have hk1 : (k + 1#32).toNat = k.toNat + 1 := by simp only [bv_c0]; omega
                  c0_hsplit
                  · have hcrk_b : (BitVec.setWidth 64
                        (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 3 +
                        BitVec.setWidth 64 k).toNat < s.core.arena.length := by
                      change (BitVec.setWidth 64 _ + 3#64 + BitVec.setWidth 64 k).toNat < _
                      rw [hcr_eq]; simp only [bv_c0]; omega
                    have hol_mem : (s.core.arena[cr.toNat + 3 + k.toNat]'(by omega)).toNat ∈
                        fullArenaClauseLitsCore s.core cr.toNat :=
                      List.mem_of_getElem? (FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem
                        (by rw [← hsz_cr]; exact hk_lt) (by omega))
                    have hol_lt := hinv.2.1.arena.lits_lt cr.toNat hcr_ref hng_cr _ hol_mem
                    have hcrk_eq : (BitVec.setWidth 64 cr + 3 + BitVec.setWidth 64 k).toNat =
                        cr.toNat + 3 + k.toNat := by
                      change (BitVec.setWidth 64 cr + 3#64 + BitVec.setWidth 64 k).toNat = _
                      simp only [bv_c0]; omega
                    c0_hfast
                    · c0_call hHop1
                      refine ⟨c, F0, F_cur, mkSt rpk mck tck antk, R, rfl, hinvk, ?_, htck, hmck_ok,
                        hmk, fun r1 rp1 mc1 tc1 ant1 m1 hinv1 htc1 hmc1 hant1' hm1 => ?_⟩
                      · simpa only [hcr_eq, hcrk_eq] using hol_lt
                      · c0_hfast
                        exact ihk (resk + r1, k + 1#32, ()) m1 (by dsimp only; rw [hk1]; omega)
                          ⟨rp1, mc1, tc1, ant1, by rw [hk1]; omega, htc1,
                           Nat.le_trans hant1' hantk, hinv1, hmc1, hm1⟩
                    · exact ihk (resk, k + 1#32, ()) mk (by dsimp only; rw [hk1]; omega)
                        ⟨rpk, mck, tck, antk, by rw [hk1]; omega, htck, hantk, hinvk, hmck_ok, hmk⟩
                  · c0_hfast
                    exact ihp (resk, p + 1 + 1, ()) mk (by dsimp only; rw [hp2_n]; omega)
                      ⟨rpk, mck, tck, antk, by rw [hp2_n]; omega, by rw [hp2_n]; omega, htck, hantk,
                       hinvk, hmck_ok,
                       by rw [hp2_n, show off0 + sz0 - (p.toNat + 2) = off0 + sz0 - p.toNat - 2
                            by omega]; exact hrem_next, hmk⟩
                · c0_hfast
                  exact ihp (resk, p + 1 + 1, ()) mk (by dsimp only; rw [hp2_n]; omega)
                    ⟨rpk, mck, tck, antk, by rw [hp2_n]; omega, by rw [hp2_n]; omega, htck, hantk,
                     hinvk, hmck_ok,
                     by rw [hp2_n, show off0 + sz0 - (p.toNat + 2) = off0 + sz0 - p.toNat - 2
                          by omega]; exact hrem_next, hmk⟩
              · exact ihp (res1, p + 1 + 1, ()) m (by dsimp only; rw [hp2_n]; omega)
                  ⟨rpp, mcp, tcp, antp - 1#64, by rw [hp2_n]; omega, by rw [hp2_n]; omega, htcp,
                   hant1, hinvp1, hmcp_ok,
                   by rw [hp2_n, show off0 + sz0 - (p.toNat + 2) = off0 + sz0 - p.toNat - 2
                        by omega]; exact hrem_next, hm_flat⟩
            · exfalso
              have ⟨h2le, _⟩ := FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hp_ws
                (by assumption)
              have hge : ¬ (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 <
                  ((s.core.wvec[2 * sl.toNat % 2 ^ 64]'(by rw [hmod0]; omega)).toNat +
                   (s.core.wvec[(2 * sl.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                     rw [hmod1]; omega)).toNat) % 2 ^ 64 := by assumption
              rw [hend_mod, hp1_mod] at hge; omega
          all_goals
            exact ihs (res1, sgn + 1#32, ()) mlp (by simp only [bv_c0]; omega)
              ⟨rpp, mcp, tcp, antp, by simp only [bv_c0]; omega, htcp, Nat.le_trans hantp hant,
               hinvp, hmcp_ok, hmlp⟩
        · exact hJend ⟨rp, mc, tc, ant⟩ ml ⟨htc, hant, hinv_s, hmc_ok, hml⟩
        · exact hJend ⟨rp, mc, tc, ant⟩ ml ⟨htc, hant, hinv_s, hmc_ok, hml⟩
    · c0_hsteps
      · exact hJ0 1#64 m rfl
      · exact hJ0 0#64 m rfl

theorem m4_bva_hop3_wp (Γ : Env)
    (hHop2 : ∀ args m Q X, fullBvaHop2Spec args m Q X →
      Γ "full_bva_hop2" [i64, i32, i32] [i64] args m Q X) :
    ∀ args m Q X, m4BvaHop3Spec args m Q X → Func.wp Γ full_bva_hop3_body args m Q X := by
  rintro ⟨h, src_lit, dst_idx, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv, hsrc_lt, htc_le, htl_le, hmclr_ok, hshrk_ok, hm, hQ⟩
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena
  unfold dimacsBound at hmx hwcap har_b
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hwv_len := hcl.wvec_len
  have hws_len := hcl.wstk_len_arr; have har_len := hcl.arena_len_arr
  have hwlen_le := hcl.wlen_le; have hal_le := hcl.arena_len_le
  have hsidx_lt : (src_lit >>> 1).toNat < s.core.cur_vars := by rw [bv32_lshr1_nat]; omega
  c0_hsteps_nogrp
  refine wp_join_state1 (t := i64) (α := BitVec 64) (fun r => r) (fun _ ml => ml = m)
    (fun _ res0 ml hml => ?_) (fun J0 hJ0 => ?_)
  · subst hml
    let mkSt (rp mc : List (BitVec 32)) (tc tl : Nat) (ant : BitVec 64) (sig : List (BitVec 64))
        (shrk : List (BitVec 32)) : FullState :=
      { core := { s.core with repr := rp, min_clr := mc, tmp_cnt := tc, tmp_len := tl }
        scratch := { s.scratch with ant_sz := ant, sim_sig := sig, shrink_stk := shrk } }
    c0_hsteps
    refine wp_loop_inv
      (fun (res, sgn, ()) ml => ∃ rp mc tc tl ant sig shrk,
        sgn.toNat ≤ 2 ∧ tc ≤ s.core.cur_vars ∧ tl ≤ s.core.cur_vars ∧
        ant.toNat ≤ s.scratch.ant_sz.toNat ∧
        FullDenseInvNoLm c F0 F_cur (mkSt rp mc tc tl ant sig shrk) ∧
        (∀ i < tc, (mc[i]?.getD 0#32).toNat < c.max_vars) ∧
        (∀ i < tl, (shrk[i]?.getD 0#32).toNat < c.max_vars) ∧
        (FullMem c (mkSt rp mc tc tl ant sig shrk) ⋆ R) ml)
      (fun (_, sgn, _) _ => 2 - sgn.toNat)
      (fun Js hJs => by
        c0_hsteps; exact hJs (res0, 0#32, ()) ml
          ⟨s.core.repr, s.core.min_clr, s.core.tmp_cnt, s.core.tmp_len, s.scratch.ant_sz,
           s.scratch.sim_sig, s.scratch.shrink_stk, by decide, htc_le, htl_le, Nat.le_refl _,
           hinv, hmclr_ok, hshrk_ok, hm⟩)
      (fun Js (res, sgn, ()) ml ⟨rp, mc, tc, tl, ant, sig, shrk, hsgn_le, htc, htl, hant, hinv_s,
          hmc_ok, hshrk_ok', hml⟩ ihs => ?_)
    dsimp only [mkSt] at hml
    c0_hsteps
    · have hsgn_lt : sgn.toNat < 2 := by c0_bound
      have hsl_nat : (((src_lit >>> (1 : Nat)) <<< (1 : Nat)) ||| sgn).toNat =
          2 * (src_lit >>> (1 : Nat)).toNat + sgn.toNat := by
        have hs01 : sgn.toNat = 0 ∨ sgn.toNat = 1 := by omega
        rcases hs01 with h0 | h1
        · have hs0 : sgn = 0#32 := BitVec.eq_of_toNat_eq h0; subst hs0
          rw [BitVec.or_zero]; c0_bound
        · have hs1 : sgn = 1#32 := BitVec.eq_of_toNat_eq h1; subst hs1
          rw [FullBvaFwdTactics.bv32_or1_of_even (by c0_bound)]; c0_bound
      have hsl_lt : (((src_lit >>> (1 : Nat)) <<< (1 : Nat)) ||| sgn).toNat <
          2 * s.core.cur_vars := by omega
      obtain ⟨hbd_sl, hslice_sl⟩ := m4_hop_wvec_bounds hinv hsl_lt
      let sl : BitVec 32 := ((src_lit >>> (1 : Nat)) <<< (1 : Nat)) ||| sgn
      have hsl_lt_sl : sl.toNat < 2 * s.core.cur_vars := hsl_lt
      have hwv_sl0 : (BitVec.setWidth 64 sl <<< (1 : Nat)).toNat < s.core.wvec.length := by
        c0_bound
      have hwv_sl1 : ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1).toNat < s.core.wvec.length := by
        change ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1#64).toNat < _; c0_bound
      have hoff_eq : (s.core.wvec[2 * sl.toNat]'(by omega)).toNat =
          fullWatchOffCore s.core sl.toNat := by
        unfold fullWatchOffCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have hsz_eq : (s.core.wvec[2 * sl.toNat + 1]'(by omega)).toNat =
          fullWatchSizeCore s.core sl.toNat := by
        unfold fullWatchSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      let off0 := fullWatchOffCore s.core sl.toNat
      let sz0 := fullWatchSizeCore s.core sl.toNat
      have hoff_sz_le : off0 + sz0 ≤ s.core.wlen := hbd_sl
      have h2sl0 : (BitVec.setWidth 64 sl <<< (1 : Nat)).toNat = 2 * sl.toNat := by c0_bound
      have h2sl1 : ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1).toNat = 2 * sl.toNat + 1 := by
        change ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1#64).toNat = _; c0_bound
      have hoff_c0 : (BitVec.setWidth 64
          (s.core.wvec[(BitVec.setWidth 64 sl <<< (1 : Nat)).toNat]'hwv_sl0)).toNat = off0 := by
        rw [bv64_setWidth_32]; simp only [h2sl0]; exact hoff_eq
      have hmod0 : 2 * sl.toNat % 2 ^ 64 = 2 * sl.toNat := Nat.mod_eq_of_lt (by omega)
      have hmod1 : (2 * sl.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = 2 * sl.toNat + 1 :=
        by c0_bound
      have hend_mod : ((s.core.wvec[2 * sl.toNat % 2 ^ 64]'(by rw [hmod0]; omega)).toNat +
          (s.core.wvec[(2 * sl.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
            rw [hmod1]; omega)).toNat) % 2 ^ 64 = off0 + sz0 := by
        simp only [hmod0, hmod1, hoff_eq, hsz_eq]; exact Nat.mod_eq_of_lt (by omega)
      c0_hsteps_nogrp
      refine wp_loop_inv
        (fun (res1, p, ()) mlp => ∃ rpp mcp tcp tlp antp sigp shrkp,
          off0 ≤ p.toNat ∧ p.toNat ≤ off0 + sz0 ∧ tcp ≤ s.core.cur_vars ∧
          tlp ≤ s.core.cur_vars ∧ antp.toNat ≤ ant.toNat ∧
          FullDenseInvNoLm c F0 F_cur (mkSt rpp mcp tcp tlp antp sigp shrkp) ∧
          (∀ i < tcp, (mcp[i]?.getD 0#32).toNat < c.max_vars) ∧
          (∀ i < tlp, (shrkp[i]?.getD 0#32).toNat < c.max_vars) ∧
          DenseWatchSliceOk F_cur s.core sl.toNat p.toNat (off0 + sz0 - p.toNat) ∧
          (FullMem c (mkSt rpp mcp tcp tlp antp sigp shrkp) ⋆ R) mlp)
        (fun (_, p, _) _ => off0 + sz0 - p.toNat)
        (fun Jp hJp => by
          c0_hfast
          exact hJp (res, _, ()) ml ⟨rp, mc, tc, tl, ant, sig, shrk,
            by rw [hoff_c0]; exact Nat.le_refl _, by rw [hoff_c0]; omega, htc, htl, Nat.le_refl _,
            hinv_s, hmc_ok, hshrk_ok',
            by rw [hoff_c0, Nat.add_sub_cancel_left]; exact hslice_sl, hml⟩)
        (fun Jp (res1, p, ()) mlp ⟨rpp, mcp, tcp, tlp, antp, sigp, shrkp, hp_ge, hp_le, htcp,
            htlp, hantp, hinvp, hmcp_ok, hshrkp_ok, hrem, hmlp⟩ ihp => ?_)
      dsimp only [mkSt] at hmlp
      c0_hfast
      · have hp_lt : p.toNat < off0 + sz0 := by rw [← hend_mod]; assumption
        have hp_ws : p.toNat < s.core.wstk.length := by omega
        have hant1 : (antp - 1#64).toNat ≤ ant.toNat := by simp only [bv_c0]; omega
        have hp1_n : (p + 1).toNat = p.toNat + 1 := by
          change (p + 1#64).toNat = _; simp only [bv_c0]; omega
        have hp1_mod : (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = p.toNat + 1 := by
          rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega
        have hinvp1 : FullDenseInvNoLm c F0 F_cur
            (mkSt rpp mcp tcp tlp (antp - 1#64) sigp shrkp) :=
          fullDenseInvNoLm_with_core_aux (tc' := tcp) (tl' := tlp) hinvp
            hinvp.1.core_ok.repr_len hinvp.1.core_ok.min_clr_len_arr hcl.tmp_len_arr
            hcl.flags_len hinvp.1.core_ok.tmp_len_le { hinvp.1.scratch_ok with } rfl rfl
        c0_hfast
        · have ⟨hot_lt, _, hrem_next⟩ := FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega)
            hp_ws (by assumption)
          c0_call hHop2
          refine ⟨c, F0, F_cur, mkSt rpp mcp tcp tlp (antp - 1#64) sigp shrkp, R, rfl, hinvp1,
            hot_lt, htcp, htlp, hmcp_ok, hshrkp_ok, hm,
            fun r1 rp1 mc1 tc1 tl1 ant1 sig1 shrk1 m1 hinv1 htc1 htl1 hmc1 hshrk1 hant1' hm1 => ?_⟩
          c0_hfast
          exact ihp (res1 + r1, p + 1, ()) m1 (by dsimp only; rw [hp1_n]; omega)
            ⟨rp1, mc1, tc1, tl1, ant1, sig1, shrk1, by rw [hp1_n]; omega, by rw [hp1_n]; omega,
             htc1, htl1, Nat.le_trans hant1' hant1, hinv1, hmc1, hshrk1,
             by rw [hp1_n, show off0 + sz0 - (p.toNat + 1) = off0 + sz0 - p.toNat - 1 by omega]
                exact hrem_next, hm1⟩
        · have hm_flat : (FullMem c
              { core := { s.core with repr := rpp, min_clr := mcp,
                                      tmp_cnt := tcp, tmp_len := tlp }
                scratch := { s.scratch with ant_sz := antp - 1#64, sim_sig := sigp,
                                            shrink_stk := shrkp } } ⋆ R) m := hm
          clear hm
          have ⟨h2le, hrem_next⟩ := FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hp_ws
            (by assumption)
          have hp1_ws : p.toNat + 1 < s.core.wstk.length := by omega
          have ⟨_, hcr_ref, _⟩ := FullBvaFwdHelpers.fwd_slice_occ_info hrem (by omega) hp_ws
            hp1_ws (by assumption)
          have hcr_wf := hinv.2.1.arena.refs_wf _ hcr_ref
          have hp2_n : (p + 1 + 1).toNat = p.toNat + 2 := by
            change (p + 1#64 + 1#64).toNat = _; simp only [bv_c0]; omega
          let cr := s.core.wstk[p.toNat + 1]'hp1_ws
          have hcr_al : cr.toNat + 3 + fullArenaClauseSizeCore s.core cr.toNat ≤
              s.core.arena_len := by
            have h1 := hcr_wf.2.2.1; have h2 := hcr_wf.2.2.2.1; dsimp only [cr]; omega
          have hcr_eq : s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws) = cr := by
            dsimp only [cr]; simp only [hp1_n]
          have hcr0_eq : (BitVec.setWidth 64
              (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws))).toNat = cr.toNat := by
            rw [bv64_setWidth_32, hcr_eq]
          have hcr_b0 : (BitVec.setWidth 64
              (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws))).toNat <
              s.core.arena.length := by rw [hcr0_eq]; omega
          have hcr2_eq : (BitVec.setWidth 64
              (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 2).toNat =
              cr.toNat + 2 := by
            change (BitVec.setWidth 64 _ + 2#64).toNat = _; rw [hcr_eq]; simp only [bv_c0]; omega
          have hcr_b2 : (BitVec.setWidth 64
              (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 2).toNat <
              s.core.arena.length := by rw [hcr2_eq]; omega
          have hsz_cr : (s.core.arena[cr.toNat + 2]'(by omega)).toNat =
              fullArenaClauseSizeCore s.core cr.toNat := by
            unfold fullArenaClauseSizeCore
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          have hcr_sz_le : cr.toNat + 3 + (s.core.arena[cr.toNat + 2]'(by omega)).toNat ≤
              s.core.arena.length := by rw [hsz_cr]; omega
          c0_hfast
          · have hng_cr : fullArenaClauseGarbCore s.core cr.toNat = false := by
              unfold fullArenaClauseGarbCore fullArenaHdrCore
              rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
              have h1 : s.core.arena[(BitVec.setWidth 64
                  (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws))).toNat]'hcr_b0 &&&
                  (524288#32 ||| 4194304#32) = 0#32 := by assumption
              exact FullBvaFwdHelpers.garb_false_of_and_garb_red_eq_zero (by
                simpa only [hcr0_eq] using h1)
            clear hQ ihs
            refine wp_loop_inv
              (fun (resk, k, ()) mk => ∃ rpk mck tck tlk antk sigk shrkk,
                k.toNat ≤ (s.core.arena[cr.toNat + 2]'(by omega)).toNat ∧
                tck ≤ s.core.cur_vars ∧ tlk ≤ s.core.cur_vars ∧ antk.toNat ≤ ant.toNat ∧
                FullDenseInvNoLm c F0 F_cur (mkSt rpk mck tck tlk antk sigk shrkk) ∧
                (∀ i < tck, (mck[i]?.getD 0#32).toNat < c.max_vars) ∧
                (∀ i < tlk, (shrkk[i]?.getD 0#32).toNat < c.max_vars) ∧
                (FullMem c (mkSt rpk mck tck tlk antk sigk shrkk) ⋆ R) mk)
              (fun (_, k, _) _ => (s.core.arena[cr.toNat + 2]'(by omega)).toNat - k.toNat)
              (fun Jk hJk => by
                c0_hfast; exact hJk (res1, 0#32, ()) m
                  ⟨rpp, mcp, tcp, tlp, antp - 1#64, sigp, shrkp, Nat.zero_le _, htcp, htlp, hant1,
                   hinvp1, hmcp_ok, hshrkp_ok, hm_flat⟩)
              (fun Jk (resk, k, ()) mk ⟨rpk, mck, tck, tlk, antk, sigk, shrkk, hk_le, htck, htlk,
                  hantk, hinvk, hmck_ok, hshrkk_ok, hmk⟩ ihk => ?_)
            dsimp only [mkSt] at hmk
            c0_hsplit
            · have hk_lt : k.toNat < (s.core.arena[cr.toNat + 2]'(by omega)).toNat := by
                have h1 : k.toNat < (s.core.arena[(BitVec.setWidth 64
                    (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) +
                    2).toNat]'hcr_b2).toNat := by assumption
                simpa only [hcr2_eq] using h1
              have hk1 : (k + 1#32).toNat = k.toNat + 1 := by simp only [bv_c0]; omega
              c0_hsplit
              · have hcrk_b : (BitVec.setWidth 64
                    (s.core.wstk[(p + 1).toNat]'(by rw [hp1_n]; exact hp1_ws)) + 3 +
                    BitVec.setWidth 64 k).toNat < s.core.arena.length := by
                  change (BitVec.setWidth 64 _ + 3#64 + BitVec.setWidth 64 k).toNat < _
                  rw [hcr_eq]; simp only [bv_c0]; omega
                have hol_mem : (s.core.arena[cr.toNat + 3 + k.toNat]'(by omega)).toNat ∈
                    fullArenaClauseLitsCore s.core cr.toNat :=
                  List.mem_of_getElem? (FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem
                    (by rw [← hsz_cr]; exact hk_lt) (by omega))
                have hol_lt := hinv.2.1.arena.lits_lt cr.toNat hcr_ref hng_cr _ hol_mem
                have hcrk_eq : (BitVec.setWidth 64 cr + 3 + BitVec.setWidth 64 k).toNat =
                    cr.toNat + 3 + k.toNat := by
                  change (BitVec.setWidth 64 cr + 3#64 + BitVec.setWidth 64 k).toNat = _
                  simp only [bv_c0]; omega
                c0_hfast
                · c0_call hHop2
                  refine ⟨c, F0, F_cur, mkSt rpk mck tck tlk antk sigk shrkk, R, rfl, hinvk, ?_,
                    htck, htlk, hmck_ok, hshrkk_ok, hmk,
                    fun r1 rp1 mc1 tc1 tl1 ant1 sig1 shrk1 m1 hinv1 htc1 htl1 hmc1 hshrk1 hant1'
                        hm1 => ?_⟩
                  · simpa only [hcr_eq, hcrk_eq] using hol_lt
                  · c0_hfast
                    exact ihk (resk + r1, k + 1#32, ()) m1 (by dsimp only; rw [hk1]; omega)
                      ⟨rp1, mc1, tc1, tl1, ant1, sig1, shrk1, by rw [hk1]; omega, htc1, htl1,
                       Nat.le_trans hant1' hantk, hinv1, hmc1, hshrk1, hm1⟩
                · exact ihk (resk, k + 1#32, ()) mk (by dsimp only; rw [hk1]; omega)
                    ⟨rpk, mck, tck, tlk, antk, sigk, shrkk, by rw [hk1]; omega, htck, htlk, hantk,
                     hinvk, hmck_ok, hshrkk_ok, hmk⟩
              · c0_hfast
                exact ihp (resk, p + 1 + 1, ()) mk (by dsimp only; rw [hp2_n]; omega)
                  ⟨rpk, mck, tck, tlk, antk, sigk, shrkk, by rw [hp2_n]; omega,
                   by rw [hp2_n]; omega, htck, htlk, hantk, hinvk, hmck_ok, hshrkk_ok,
                   by rw [hp2_n, show off0 + sz0 - (p.toNat + 2) = off0 + sz0 - p.toNat - 2
                        by omega]; exact hrem_next, hmk⟩
            · c0_hfast
              exact ihp (resk, p + 1 + 1, ()) mk (by dsimp only; rw [hp2_n]; omega)
                ⟨rpk, mck, tck, tlk, antk, sigk, shrkk, by rw [hp2_n]; omega,
                 by rw [hp2_n]; omega, htck, htlk, hantk, hinvk, hmck_ok, hshrkk_ok,
                 by rw [hp2_n, show off0 + sz0 - (p.toNat + 2) = off0 + sz0 - p.toNat - 2
                      by omega]; exact hrem_next, hmk⟩
          · exact ihp (res1, p + 1 + 1, ()) m (by dsimp only; rw [hp2_n]; omega)
              ⟨rpp, mcp, tcp, tlp, antp - 1#64, sigp, shrkp, by rw [hp2_n]; omega,
               by rw [hp2_n]; omega, htcp, htlp, hant1, hinvp1, hmcp_ok, hshrkp_ok,
               by rw [hp2_n, show off0 + sz0 - (p.toNat + 2) = off0 + sz0 - p.toNat - 2
                    by omega]; exact hrem_next, hm_flat⟩
        · exfalso
          have ⟨h2le, _⟩ := FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hp_ws
            (by assumption)
          have hge : ¬ (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 <
              ((s.core.wvec[2 * sl.toNat % 2 ^ 64]'(by rw [hmod0]; omega)).toNat +
               (s.core.wvec[(2 * sl.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                 rw [hmod1]; omega)).toNat) % 2 ^ 64 := by assumption
          rw [hend_mod, hp1_mod] at hge; omega
      all_goals
        exact ihs (res1, sgn + 1#32, ()) mlp (by simp only [bv_c0]; omega)
          ⟨rpp, mcp, tcp, tlp, antp, sigp, shrkp, by simp only [bv_c0]; omega, htcp, htlp,
           Nat.le_trans hantp hant, hinvp, hmcp_ok, hshrkp_ok, hmlp⟩
    · exact hQ res rp mc tc tl ant sig shrk ml hinv_s htc htl hmc_ok hshrk_ok' hant hml
    · exact hQ res rp mc tc tl ant sig shrk ml hinv_s htc htl hmc_ok hshrk_ok' hant hml
  · c0_hsteps
    · exact hJ0 1#64 m rfl
    · exact hJ0 0#64 m rfl

/-! ## 3. Shared-Cache Tie-Breaker (`m4_bva_pick_cand_wp`) -/

theorem m4_bva_pick_cand_wp (Γ : Env)
    (hHop3 : ∀ args m Q X, m4BvaHop3Spec args m Q X →
      Γ "full_bva_hop3" [i64, i32, i32] [i64] args m Q X) :
    ∀ args m Q X, fullBvaPickCandSpec args m Q X →
      Func.wp Γ full_bva_pick_cand_body args m Q X := by
  rintro ⟨h, ncntd, f0, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv, hf0_lt, hnc_le, hcntd_ok, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hwv_len := hcl.wvec_len
  have hws_len := hsc.wsort_len; have hws1_len := hsc.work_stk1_len
  c0_hsteps
  -- Loop 1: find max count `best_c`, `best_lit`, `ties`
  refine wp_loop_inv
    (fun (best_c, best_lit, ties, ci, ()) ml =>
      ml = m ∧ ci.toNat ≤ ncntd.toNat ∧
      (0 < best_c.toNat → best_lit.toNat < 2 * s.core.cur_vars))
    (fun (_, _, _, ci, _) _ => ncntd.toNat - ci.toNat)
    (fun J1 hJ1 => by
      c0_hsteps; exact hJ1 (0#32, 0xFFFFFFFF#32, 0#32, 0#32, ()) m
        ⟨rfl, Nat.zero_le _, fun h => by simp only [bv_c0] at h; omega⟩)
    (fun J1 (best_c, best_lit, ties, ci, ()) ml ⟨hml, hci_le, hbl_ok⟩ ih1 => ?_)
  rcases hml with rfl
  c0_hsteps_nogrp
  · have hci_lt : ci.toNat < ncntd.toNat := by c0_bound
    have hci64 : (BitVec.setWidth 64 ci).toNat = ci.toNat := by c0_bound
    have hclit_lt : (s.scratch.work_stk1[ci.toNat]'(by omega)).toNat < 2 * s.core.cur_vars := by
      have := hcntd_ok ci.toNat hci_lt
      rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
    have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := by c0_bound
    c0_hsteps
    · refine ih1 (_, _, 1#32, ci + 1#32, ()) ml (by dsimp only; rw [hci1]; omega)
        ⟨rfl, by rw [hci1]; omega, fun _ => by simpa only [hci64] using hclit_lt⟩
    all_goals
      exact ih1 (_, best_lit, _, ci + 1#32, ()) ml (by dsimp only; rw [hci1]; omega)
        ⟨rfl, by rw [hci1]; omega, hbl_ok⟩
  · -- After Loop 1: optional shared-cache tie-break loop + cleanup, then zero `cnt[cntd[0..n)]`
    let mkSt (rp mc : List (BitVec 32)) (tc tl : Nat) (ws : List (BitVec 32)) (ant : BitVec 64)
        (sig : List (BitVec 64)) (shrk : List (BitVec 32)) : FullState :=
      { core := { s.core with repr := rp, min_clr := mc, tmp_cnt := tc, tmp_len := tl }
        scratch := { s.scratch with wsort := ws, ant_sz := ant, sim_sig := sig,
                                    shrink_stk := shrk } }
    refine wp_join_state
      (α := BitVec 32 × BitVec 32 × List (BitVec 32) × List (BitVec 32) × Nat × Nat × BitVec 64 ×
        List (BitVec 64) × List (BitVec 32))
      (fun st => (st.1, st.2.1, ()))
      (fun ⟨blF, _ciF, rpF, mcF, tcF, tlF, antF, sigF, shrkF⟩ mf =>
        (2 ≤ best_c.toNat → blF.toNat < 2 * s.core.cur_vars) ∧
        FullDenseInvNoLm c F0 F_cur (mkSt rpF mcF tcF tlF s.scratch.wsort antF sigF shrkF) ∧
        (FullMem c (mkSt rpF mcF tcF tlF s.scratch.wsort antF sigF shrkF) ⋆ R) mf)
      (fun _ ⟨blF, _ciF, rpF, mcF, tcF, tlF, antF, sigF, shrkF⟩ mf ⟨hblF, hinvF, hmf⟩ => ?_)
      (fun Jtb hJtb => ?_)
    · -- Loop 3: zero `cnt[cntd[0..ncntd)]`, then return `(best_c < 2) ? 0xFFFFFFFF : blF`
      c0_hsteps
      refine wp_loop_inv
        (fun (ci, ()) m3 => ∃ ws3,
          ci.toNat ≤ ncntd.toNat ∧ ws3.length = 2 * c.max_vars ∧
          (FullMem c (mkSt rpF mcF tcF tlF ws3 antF sigF shrkF) ⋆ R) m3)
        (fun (ci, ()) _ => ncntd.toNat - ci.toNat)
        (fun J3 hJ3 => by
          c0_hsteps; exact hJ3 (0#32, ()) mf ⟨s.scratch.wsort, Nat.zero_le _, hws_len, hmf⟩)
        (fun J3 (ci, ()) m3 ⟨ws3, hci_le, hws3_len, hm3⟩ ih3 => ?_)
      dsimp only [mkSt] at hm3
      c0_hsteps_nogrp
      · have hci_lt : ci.toNat < ncntd.toNat := by c0_bound
        have hclit_lt : (s.scratch.work_stk1[ci.toNat]'(by omega)).toNat < 2 * s.core.cur_vars := by
          have := hcntd_ok ci.toNat hci_lt
          rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
        have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := by c0_bound
        c0_hsteps
        exact ih3 (ci + 1#32, ()) m (by dsimp only; rw [hci1]; omega)
          ⟨_, by rw [hci1]; omega, by simp [hws3_len], hm⟩
      · have hinv_fin : FullDenseInvNoLm c F0 F_cur
            (mkSt rpF mcF tcF tlF ws3 antF sigF shrkF) :=
          fullDenseInvNoLm_with_core_aux hinvF hinvF.1.core_ok.repr_len
            hinvF.1.core_ok.min_clr_len_arr hcl.tmp_len_arr hcl.flags_len
            hinvF.1.core_ok.tmp_len_le
            { hinvF.1.scratch_ok with wsort_len := hws3_len } rfl rfl
        c0_hsteps
        · exact hQ 0xFFFFFFFF#32 rpF mcF tcF tlF ws3 antF sigF shrkF m3 hinv_fin (Or.inl rfl) hm3
        · exact hQ blF rpF mcF tcF tlF ws3 antF sigF shrkF m3 hinv_fin
            (Or.inr (hblF (by c0_bound))) hm3
    · -- Optional shared-cache tie-break branch: `if (best_c >= 2 && ties > 1)`
      c0_hsteps
      · have hbc_ge2 : 2 ≤ best_c.toNat := by c0_bound
        have hinv0 : FullDenseInvNoLm c F0 F_cur
            (mkSt s.core.repr s.core.min_clr 0 0 s.scratch.wsort 65536#64
              s.scratch.sim_sig s.scratch.shrink_stk) :=
          fullDenseInvNoLm_with_core_aux hinv hcl.repr_len hcl.min_clr_len_arr hcl.tmp_len_arr
            hcl.flags_len (Nat.zero_le _) { hsc with } rfl rfl
        refine wp_loop_inv
          (fun (best_lit2, ci2, best_sc, best_deg, tt, ()) m2 =>
            ∃ rp2 mc2 tc2 tl2 ant2 sig2 shrk2,
              ci2.toNat ≤ ncntd.toNat ∧ tt.toNat ≤ 128 ∧ best_lit2.toNat < 2 * s.core.cur_vars ∧
              tc2 ≤ s.core.cur_vars ∧ tl2 ≤ s.core.cur_vars ∧
              FullDenseInvNoLm c F0 F_cur
                (mkSt rp2 mc2 tc2 tl2 s.scratch.wsort ant2 sig2 shrk2) ∧
              (∀ i < tc2, (mc2[i]?.getD 0#32).toNat < c.max_vars) ∧
              (∀ i < tl2, (shrk2[i]?.getD 0#32).toNat < c.max_vars) ∧
              (FullMem c (mkSt rp2 mc2 tc2 tl2 s.scratch.wsort ant2 sig2 shrk2) ⋆ R) m2)
          (fun (_, ci2, _, _, _, _) _ => ncntd.toNat - ci2.toNat)
          (fun J2 hJ2 => by
            c0_hsteps; exact hJ2 (best_lit, 0#32, 0#64, 0#32, 0#32, ()) m
              ⟨s.core.repr, s.core.min_clr, 0, 0, 65536#64,
               s.scratch.sim_sig, s.scratch.shrink_stk, Nat.zero_le _, by decide,
               hbl_ok (by omega), Nat.zero_le _, Nat.zero_le _, hinv0,
               fun _ h => by omega, fun _ h => by omega, hm⟩)
          (fun J2 (best_lit2, ci2, best_sc, best_deg, tt, ()) m2
              ⟨rp2, mc2, tc2, tl2, ant2, sig2, shrk2, hci2_le, htt_le, hbl2, htc2, htl2, hinv2,
               hmc2_ok, hshrk2_ok, hm2⟩ ih2 => ?_)
        dsimp only [mkSt] at hm2
        c0_hsteps_nogrp
        -- Exit join point `J2end` before the `s1`/`s2` cleanup loops
        refine wp_join_state0 (α := Unit)
          (fun _ mf => mf = m2)
          (fun _ _ mf hmf => ?_)
          (fun J2end hJ2end => ?_)
        · -- Cleanup `s1[st1[0..tc2)] = 0`, `s2[st2[0..tl2)] = 0`, `tmp_cnt = 0; tmp_len = 0`
          subst mf
          have hmc2_len : mc2.length = c.max_vars := hinv2.1.core_ok.min_clr_len_arr
          have hshrk2_len : shrk2.length = c.max_vars := hinv2.1.scratch_ok.shrink_stk_len
          c0_hsteps
          refine wp_loop_inv
            (fun (i, ()) mi => ∃ rpi, i.toNat ≤ tc2 ∧ rpi.length = 2 * c.max_vars ∧
              (FullMem c (mkSt rpi mc2 tc2 tl2 s.scratch.wsort ant2 sig2 shrk2) ⋆ R) mi)
            (fun (i, ()) _ => tc2 - i.toNat)
            (fun Jc1 hJc1 => by
              c0_hsteps; exact hJc1 (0#64, ()) m2 ⟨rp2, Nat.zero_le _, hinv2.1.core_ok.repr_len,
                hm2⟩)
            (fun Jc1 (i, ()) mi ⟨rpi, hi_le, hrpi_len, hmi⟩ ihc1 => ?_)
          dsimp only [mkSt] at hmi
          c0_hsteps
          · have hi_lt : i.toNat < tc2 := by c0_bound
            have hidx_lt : (mc2[i.toNat]'(by omega)).toNat < c.max_vars := by
              have := hmc2_ok i.toNat hi_lt
              rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
            c0_hsteps
            exact ihc1 (i + 1#64, ()) m (by c0_bound)
              ⟨_, by c0_bound, by rw [repr64Set_length, hrpi_len], hm⟩
          · refine wp_loop_inv
              (fun (i, ()) mi2 => ∃ sigi, i.toNat ≤ tl2 ∧ sigi.length = c.max_vars ∧
                (FullMem c (mkSt rpi mc2 tc2 tl2 s.scratch.wsort ant2 sigi shrk2) ⋆ R) mi2)
              (fun (i, ()) _ => tl2 - i.toNat)
              (fun Jc2 hJc2 => by
                c0_hsteps; exact hJc2 (0#64, ()) mi ⟨sig2, Nat.zero_le _,
                  hinv2.1.scratch_ok.sim_sig_len, hmi⟩)
              (fun Jc2 (i, ()) mi2 ⟨sigi, hi2_le, hsigi_len, hmi2⟩ ihc2 => ?_)
            dsimp only [mkSt] at hmi2
            c0_hsteps
            · have hi2_lt : i.toNat < tl2 := by c0_bound
              have hidx_lt : (shrk2[i.toNat]'(by omega)).toNat < c.max_vars := by
                have := hshrk2_ok i.toNat hi2_lt
                rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
              c0_hsteps
              exact ihc2 (i + 1#64, ()) m (by c0_bound)
                ⟨_, by c0_bound, by simp [hsigi_len], hm⟩
            · have hsc_fin : ({ s.scratch with
                  ant_sz := ant2, sim_sig := sigi, shrink_stk := shrk2 } : FullScratch).LengthsOk
                    c :=
                { hsc with sim_sig_len := hsigi_len, shrink_stk_len := hshrk2_len }
              dsimp only [mkSt] at hinv2
              have hinv_fin := fullDenseInvNoLm_with_core_aux (tc' := 0) (tl' := 0) hinv2 hrpi_len
                hmc2_len hcl.tmp_len_arr hcl.flags_len (Nat.zero_le _) hsc_fin rfl rfl
              c0_hsteps
              exact hJtb ⟨best_lit2, ci2, rpi, mc2, 0, 0, ant2, sigi, shrk2⟩ m
                ⟨fun _ => hbl2, hinv_fin, hm⟩
        · c0_hsteps
          · have hci2_lt : ci2.toNat < ncntd.toNat := by c0_bound
            have hci2_64 : (BitVec.setWidth 64 ci2).toNat = ci2.toNat := by c0_bound
            have hclit_lt : (s.scratch.work_stk1[ci2.toNat]'(by omega)).toNat <
                2 * s.core.cur_vars := by
              have := hcntd_ok ci2.toNat hci2_lt
              rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
            have hci2_1 : (ci2 + 1#32).toNat = ci2.toNat + 1 := by c0_bound
            c0_hsteps
            · have htt1 : (tt + 1#32).toNat ≤ 128 := by c0_bound
              c0_call hHop3
              refine ⟨c, F0, F_cur, mkSt rp2 mc2 tc2 tl2 s.scratch.wsort ant2 sig2 shrk2, R, rfl,
                hinv2, by simpa only [hci2_64] using hclit_lt, htc2, htl2, hmc2_ok, hshrk2_ok, hm2,
                fun sc rp3 mc3 tc3 tl3 ant3 sig3 shrk3 m3 hinv3 htc3 htl3 hmc3 hshrk3 _ hm3 => ?_⟩
              dsimp only [mkSt] at hm3
              have h2clit : ((BitVec.setWidth 64 (s.scratch.work_stk1[ci2.toNat]'(by omega)) <<<
                  (1 : Nat)) + 1).toNat =
                  2 * (s.scratch.work_stk1[ci2.toNat]'(by omega)).toNat + 1 := by
                change ((BitVec.setWidth 64 _ <<< (1 : Nat)) + 1#64).toNat = _; c0_bound
              have hclit_wvec : ((BitVec.setWidth 64
                  (s.scratch.work_stk1[(BitVec.setWidth 64 ci2).toNat]'(by
                    rw [hci2_64]; omega)) <<< (1 : Nat)) + 1).toNat < s.core.wvec.length := by
                simp only [hci2_64, h2clit, hwv_len]; omega
              c0_hsteps_nogrp
              refine wp_join_state_pure (ts := [i32, i64, i32])
                (α := BitVec 32 × BitVec 64 × BitVec 32)
                (fun p => (p.1, p.2.1, p.2.2, ()))
                (fun p => p.1.toNat < 2 * s.core.cur_vars)
                (fun _ ⟨bl', bsc', bd'⟩ hbl' => by
                  c0_hfast
                  exact ih2 (bl', ci2 + 1#32, bsc', bd', tt + 1#32, ()) m3
                    (by dsimp only; rw [hci2_1]; omega)
                    ⟨rp3, mc3, tc3, tl3, ant3, sig3, shrk3, by rw [hci2_1]; omega, htt1, hbl',
                     htc3, htl3, hinv3, hmc3, hshrk3, hm3⟩)
                (fun Jupd hJupd => by
                  c0_hfast
                  all_goals first
                    | exact hJupd (_, _, _) (by simpa only [hci2_64] using hclit_lt)
                    | exact hJupd (best_lit2, best_sc, best_deg) hbl2)
            · exact ih2 (best_lit2, ci2 + 1#32, best_sc, best_deg, tt, ()) m2
                (by dsimp only; rw [hci2_1]; omega)
                ⟨rp2, mc2, tc2, tl2, ant2, sig2, shrk2, by rw [hci2_1]; omega, htt_le, hbl2,
                 htc2, htl2, hinv2, hmc2_ok, hshrk2_ok, hm2⟩
          · exact hJ2end () m2 rfl
          · exact hJ2end () m2 rfl
      all_goals
        exact hJtb ⟨best_lit, ci, s.core.repr, s.core.min_clr, s.core.tmp_cnt, s.core.tmp_len,
          s.scratch.ant_sz, s.scratch.sim_sig, s.scratch.shrink_stk⟩ ml
          ⟨fun h => hbl_ok (by omega), hinv, hm⟩

/-! ## 4. Upgraded Candidate Scanner (`m4_bva_scan_cands_wp`, `cur_qn ≤ 256`) -/

private def M4ScanArVivInv (c : FullCfg) (s : FullState) (ar : List (BitVec 32))
    (ql : List (BitVec 32)) (lo hi : Nat) : Prop :=
  ar.length = c.arena_cap ∧ ql.length = 2 * c.max_vars ∧ hi ≤ c.max_vars ∧
  (∀ t, lo ≤ t → t < hi → (ql[t]?.getD 0#32).toNat ∈ fullArenaClauseRefsCore s.core ∧
    (s.core.arena[(ql[t]?.getD 0#32).toNat]?.getD 0#32 &&& 0x00100000#32) = 0#32) ∧
  (∀ idx < c.arena_cap, ar[idx]? = s.core.arena[idx]? ∨
    (∃ t, lo ≤ t ∧ t < hi ∧ (ql[t]?.getD 0#32).toNat = idx ∧
      (s.core.arena[idx]?.getD 0#32 &&& 0x00100000#32) = 0#32 ∧
      ar[idx]? = some (s.core.arena[idx]?.getD 0#32 ||| 0x00100000#32)))

private theorem m4ScanArVivInv_init {c : FullCfg} {s : FullState} (hlen : s.LengthsOk c) :
    M4ScanArVivInv c s s.core.arena s.scratch.work_stk2 0 0 :=
  ⟨hlen.core_ok.arena_len_arr, hlen.scratch_ok.work_stk2_len, Nat.zero_le _,
   fun _ _ h => by omega, fun _ _ => Or.inl rfl⟩

private theorem m4ScanArVivInv_set_ql_hi {c : FullCfg} {s : FullState} {ar ql : List (BitVec 32)}
    {nql : Nat} (h : M4ScanArVivInv c s ar ql 0 nql) {idx : Nat} (hidx : c.max_vars ≤ idx)
    (v : BitVec 32) : M4ScanArVivInv c s ar (ql.set idx v) 0 nql := by
  obtain ⟨har, hql, hhi, hdom, hall⟩ := h
  refine ⟨har, by simp [hql], hhi, fun t h0 ht => ?_, fun i hi => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hdom t h0 ht
  · rcases hall i hi with heq | ⟨t, h0, ht, hqt, h0v, hset⟩
    · exact Or.inl heq
    · exact Or.inr ⟨t, h0, ht, by rw [List.getElem?_set_ne (by omega)]; exact hqt, h0v, hset⟩

private theorem m4ScanArVivInv_push {c : FullCfg} {s : FullState} {ar ql : List (BitVec 32)}
    {nql : Nat} (h : M4ScanArVivInv c s ar ql 0 nql) {dr : BitVec 32}
    (hnql_lt : nql < c.max_vars) (hdr_ref : dr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hdr_lt : dr.toNat < c.arena_cap)
    (hdr_nviv : (ar[dr.toNat]'(by rw [h.1]; exact hdr_lt) &&& 0x00100000#32) = 0#32) :
    (s.core.arena[dr.toNat]?.getD 0#32 &&& 0x00100000#32) = 0#32 ∧
    M4ScanArVivInv c s
      (ar.set dr.toNat ((ar[dr.toNat]'(by rw [h.1]; exact hdr_lt)) ||| 0x00100000#32))
      (ql.set nql dr) 0 (nql + 1) := by
  obtain ⟨har, hql, hhi, hdom, hall⟩ := h
  have horig : ar[dr.toNat]? = s.core.arena[dr.toNat]? := by
    rcases hall dr.toNat hdr_lt with heq | ⟨_, _, _, _, h0v, hset⟩
    · exact heq
    · rw [List.getElem?_eq_getElem (by omega)] at hset
      have hval := Option.some.inj hset
      have h1 : ((s.core.arena[dr.toNat]?.getD 0#32 ||| 0x00100000#32) &&& 0x00100000#32) =
          0x00100000#32 := by
        rw [BitVec.and_or_distrib_right,
          show (0x00100000#32 &&& 0x00100000#32) = 0x00100000#32 from rfl, h0v, BitVec.zero_or]
      rw [hval] at hdr_nviv
      exact absurd (hdr_nviv.symm.trans h1) (by decide)
  have hs_nviv : (s.core.arena[dr.toNat]?.getD 0#32 &&& 0x00100000#32) = 0#32 := by
    rw [← horig, List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hdr_nviv
  refine ⟨hs_nviv, by simp [har], by simp [hql], by omega, fun t h0 ht => ?_, fun i hi => ?_⟩
  · by_cases htn : t = nql
    · subst htn; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact ⟨hdr_ref, hs_nviv⟩
    · rw [List.getElem?_set_ne (Ne.symm htn)]; exact hdom t h0 (by omega)
  · by_cases hid : i = dr.toNat
    · subst hid
      refine Or.inr ⟨nql, Nat.zero_le _, by omega,
        by rw [List.getElem?_set_self (by omega), Option.getD_some], hs_nviv, ?_⟩
      rw [List.getElem?_set_self (by omega)]
      have har_eq : ar[dr.toNat]'(by omega) = s.core.arena[dr.toNat]?.getD 0#32 := by
        rw [← horig, List.getElem?_eq_getElem (by omega), Option.getD_some]
      rw [har_eq]
    · rw [List.getElem?_set_ne (Ne.symm hid)]
      rcases hall i hi with heq | ⟨t, h0, ht, hqt, h0v, hset⟩
      · exact Or.inl heq
      · exact Or.inr ⟨t, h0, by omega,
          by rw [List.getElem?_set_ne (by omega)]; exact hqt, h0v, hset⟩

private theorem m4ScanArVivInv_clear_step {c : FullCfg} {s : FullState} {ar ql : List (BitVec 32)}
    {ci nql : Nat} (hs_ar : s.core.arena.length = c.arena_cap)
    (h : M4ScanArVivInv c s ar ql ci nql) (hci : ci < nql)
    (hidx_lt : (ql[ci]'(by rw [h.2.1]; have := h.2.2.1; omega)).toNat < c.arena_cap) :
    let idx := (ql[ci]'(by rw [h.2.1]; have := h.2.2.1; omega)).toNat
    M4ScanArVivInv c s
      (ar.set idx ((ar[idx]'(by rw [h.1]; exact hidx_lt)) &&& ~~~0x00100000#32))
      ql (ci + 1) nql := by
  obtain ⟨har, hql, hhi, hdom, hall⟩ := h
  intro idx
  have hidx_eq : (ql[ci]?.getD 0#32).toNat = idx := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hidx_s0 : (s.core.arena[idx]?.getD 0#32 &&& 0x00100000#32) = 0#32 := by
    have := (hdom ci (Nat.le_refl _) hci).2; rwa [hidx_eq] at this
  have har_idx_clr :
      ((ar[idx]'(by omega)) &&& ~~~0x00100000#32) = s.core.arena[idx]?.getD 0#32 := by
    rcases hall idx hidx_lt with heq | ⟨_, _, _, _, _, hset⟩
    · have : ar[idx]'(by omega) = s.core.arena[idx]?.getD 0#32 := by
        rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some]
      rw [this]; exact bv32_clear_viv_of_zero hidx_s0
    · rw [List.getElem?_eq_getElem (by omega)] at hset
      rw [Option.some.inj hset]; exact bv32_viv_roundtrip hidx_s0
  refine ⟨by simp [har], hql, hhi, fun t ht1 ht2 => hdom t (by omega) ht2, fun i hi => ?_⟩
  by_cases hid : i = idx
  · subst hid
    left
    rw [List.getElem?_set_self (by omega), har_idx_clr,
      List.getElem?_eq_getElem (by omega), Option.getD_some]
  · rw [List.getElem?_set_ne (Ne.symm hid)]
    rcases hall i hi with heq | ⟨t, ht1, ht2, hqt, h0v, hset⟩
    · exact Or.inl heq
    · have htne : t ≠ ci := fun h => by subst h; rw [hidx_eq] at hqt; exact hid hqt.symm
      exact Or.inr ⟨t, by omega, ht2, hqt, h0v, hset⟩

private theorem m4ScanArVivInv_done {c : FullCfg} {s : FullState} {ar ql : List (BitVec 32)}
    {nql : Nat} (hs_ar : s.core.arena.length = c.arena_cap)
    (h : M4ScanArVivInv c s ar ql nql nql) : ar = s.core.arena := by
  apply list_eq_of_getElem?_eq (by rw [h.1, hs_ar])
  intro i hi
  rcases h.2.2.2.2 i (by omega) with heq | ⟨t, ht1, ht2, _⟩
  · exact heq
  · omega

private def M4LmBit4Inv (c : FullCfg) (lm1 : List (BitVec 8)) (ql : List (BitVec 32))
    (lo hi : Nat) (lm : List (BitVec 8)) : Prop :=
  lm.length = 2 * c.max_vars ∧ hi ≤ c.max_vars ∧
  (∀ t, lo ≤ t → t < hi → (ql[c.max_vars + t]?.getD 0#32).toNat < 2 * c.max_vars) ∧
  ∀ l < 2 * c.max_vars, lm[l]? = lm1[l]? ∨
    (∃ t, lo ≤ t ∧ t < hi ∧ (ql[c.max_vars + t]?.getD 0#32).toNat = l ∧
      lm[l]? = some (lm1[l]?.getD 0#8 ||| 4#8))

private theorem m4LmBit4Inv_init {c : FullCfg} {lm1 : List (BitVec 8)} {ql : List (BitVec 32)}
    (hlm1 : lm1.length = 2 * c.max_vars) : M4LmBit4Inv c lm1 ql 0 0 lm1 :=
  ⟨hlm1, Nat.zero_le _, fun _ _ h => by omega, fun _ _ => Or.inl rfl⟩

private theorem m4LmBit4Inv_set_ql_lo {c : FullCfg} {lm1 lm : List (BitVec 8)}
    {ql : List (BitVec 32)} {hi idx : Nat} (h : M4LmBit4Inv c lm1 ql 0 hi lm)
    (hidx : idx < c.max_vars) (v : BitVec 32) : M4LmBit4Inv c lm1 (ql.set idx v) 0 hi lm := by
  obtain ⟨hlm, hhi, hdom, hall⟩ := h
  refine ⟨hlm, hhi, fun t h0 ht => ?_, fun l hl => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hdom t h0 ht
  · rcases hall l hl with heq | ⟨t, h0, ht, hqt, hset⟩
    · exact Or.inl heq
    · exact Or.inr ⟨t, h0, ht, by rw [List.getElem?_set_ne (by omega)]; exact hqt, hset⟩

private theorem m4LmBit4Inv_push {c : FullCfg} {lm1 lm : List (BitVec 8)} {ql : List (BitVec 32)}
    {nnou : Nat} (hql : ql.length = 2 * c.max_vars) (h : M4LmBit4Inv c lm1 ql 0 nnou lm)
    {cand : BitVec 32} (hnn : nnou < c.max_vars) (hc_lt : cand.toNat < 2 * c.max_vars) :
    M4LmBit4Inv c lm1 (ql.set (c.max_vars + nnou) cand) 0 (nnou + 1)
      (lm.set cand.toNat ((lm[cand.toNat]'(by rw [h.1]; exact hc_lt)) ||| 4#8)) := by
  obtain ⟨hlm, hhi, hdom, hall⟩ := h
  refine ⟨by simp [hlm], by omega, fun t h0 ht => ?_, fun l hl => ?_⟩
  · by_cases htn : t = nnou
    · subst htn; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hc_lt
    · rw [List.getElem?_set_ne (by omega)]; exact hdom t h0 (by omega)
  · by_cases hlc : l = cand.toNat
    · subst hlc
      refine Or.inr ⟨nnou, Nat.zero_le _, by omega,
        by rw [List.getElem?_set_self (by omega), Option.getD_some], ?_⟩
      rw [List.getElem?_set_self (by omega)]
      rcases hall cand.toNat hc_lt with heq | ⟨_, _, _, _, hset⟩
      · have : lm[cand.toNat]'(by omega) = lm1[cand.toNat]?.getD 0#8 := by
          rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some]
        rw [this]
      · rw [List.getElem?_eq_getElem (by omega)] at hset
        rw [Option.some.inj hset, bv8_or4_idem]
    · rw [List.getElem?_set_ne (Ne.symm hlc)]
      rcases hall l hl with heq | ⟨t, h0, ht, hqt, hset⟩
      · exact Or.inl heq
      · exact Or.inr ⟨t, h0, by omega, by rw [List.getElem?_set_ne (by omega)]; exact hqt, hset⟩

private theorem m4LmBit4Inv_clear_step {c : FullCfg} {lm1 lm : List (BitVec 8)}
    {ql : List (BitVec 32)} {j nnou : Nat} (hlm1 : lm1.length = 2 * c.max_vars)
    (hql : ql.length = 2 * c.max_vars)
    (hlm1_b2 : ∀ l < 2 * c.max_vars, (lm1[l]?.getD 0#8 &&& 4#8) = 0#8)
    (h : M4LmBit4Inv c lm1 ql j nnou lm) (hj : j < nnou) :
    let cl := (ql[c.max_vars + j]'(by have := h.2.1; omega)).toNat
    cl < 2 * c.max_vars ∧
    M4LmBit4Inv c lm1 ql (j + 1) nnou
      (lm.set cl ((lm[cl]'(by
        have hdom := h.2.2.1 j (Nat.le_refl _) hj
        rw [List.getElem?_eq_getElem (by have := h.2.1; omega), Option.getD_some] at hdom
        rw [h.1]; exact hdom)) &&& 0xFB#8)) := by
  obtain ⟨hlm, hhi, hdom, hall⟩ := h
  intro cl
  have hcl_eq : (ql[c.max_vars + j]?.getD 0#32).toNat = cl := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hcl_lt : cl < 2 * c.max_vars := by have := hdom j (Nat.le_refl _) hj; rwa [hcl_eq] at this
  have hclr : ((lm[cl]'(by omega)) &&& 0xFB#8) = lm1[cl]?.getD 0#8 := by
    apply bv8_clear_bit2_eq_of_or4 (hlm1_b2 cl hcl_lt)
    rcases hall cl hcl_lt with heq | ⟨_, _, _, _, hset⟩
    · left; rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some]
    · right; rw [List.getElem?_eq_getElem (by omega)] at hset; exact Option.some.inj hset
  refine ⟨hcl_lt, by simp [hlm], hhi, fun t ht1 ht2 => hdom t (by omega) ht2, fun i hi => ?_⟩
  by_cases hic : i = cl
  · subst hic; left
    rw [List.getElem?_set_self (by omega), hclr,
      List.getElem?_eq_getElem (by omega), Option.getD_some]
  · rw [List.getElem?_set_ne (Ne.symm hic)]
    rcases hall i hi with heq | ⟨t, ht1, ht2, hqt, hset⟩
    · exact Or.inl heq
    · have htne : t ≠ j := fun h => by subst h; rw [hcl_eq] at hqt; exact hic hqt.symm
      exact Or.inr ⟨t, by omega, ht2, hqt, hset⟩

private theorem m4LmBit4Inv_done {c : FullCfg} {lm1 lm : List (BitVec 8)} {ql : List (BitVec 32)}
    {nnou : Nat} (hlm1 : lm1.length = 2 * c.max_vars)
    (h : M4LmBit4Inv c lm1 ql nnou nnou lm) : lm = lm1 := by
  apply list_eq_of_getElem?_eq (by rw [h.1, hlm1])
  intro i hi
  rcases h.2.2.2 i (by omega) with heq | ⟨t, ht1, ht2, _⟩
  · exact heq
  · omega

private theorem m4_scan_cands_ar_lits_eq {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {ar ql : List (BitVec 32)} {nql : Nat}
    (hcl : s.core.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hviv : M4ScanArVivInv c s ar ql 0 nql) {r : Nat} (hr : r ∈ fullArenaClauseRefsCore s.core) :
    ar[r + 2]? = s.core.arena[r + 2]? ∧
    (∀ j < fullArenaClauseSizeCore s.core r, ar[r + 3 + j]? = s.core.arena[r + 3 + j]?) := by
  have hwf := hw.arena.refs_wf r hr; have hal := hcl.arena_len_le
  constructor
  · rcases hviv.2.2.2.2 (r + 2) (by omega) with heq | ⟨t, _, ht, hqt, _, _⟩
    · exact heq
    · exfalso
      have ht_ref := (hviv.2.2.2.1 t (Nat.zero_le _) ht).1; rw [hqt] at ht_ref
      rcases Nat.lt_or_gt_of_ne (by omega : r ≠ r + 2) with hlt | hgt
      · have := fullArenaScanRefs_disjoint hr ht_ref hlt; omega
      · omega
  · intro j hj
    rcases hviv.2.2.2.2 (r + 3 + j) (by omega) with heq | ⟨t, _, ht, hqt, _, _⟩
    · exact heq
    · exfalso
      have ht_ref := (hviv.2.2.2.1 t (Nat.zero_le _) ht).1; rw [hqt] at ht_ref
      have := fullArenaScanRefs_disjoint hr ht_ref (by omega); omega

private theorem m4_scan_cands_dr_info {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {arp qlp : List (BitVec 32)} {nqlp : Nat} {dr csz_bv : BitVec 32}
    (hcl : s.core.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hvivp : M4ScanArVivInv c s arp qlp 0 nqlp)
    (hdr_ref : dr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hdr_lt : dr.toNat + 3 ≤ arp.length)
    (hdr_58 : (arp[dr.toNat]'(by omega) &&& 0x00580000#32) = 0#32)
    (hdr_sz_ar : arp[dr.toNat + 2]'(by omega) = csz_bv) :
    (arp[dr.toNat]'(by omega) &&& 0x00100000#32) = 0#32 ∧
    fullArenaClauseGarbCore s.core dr.toNat = false ∧
    fullArenaClauseSizeCore s.core dr.toNat = csz_bv.toNat := by
  have harp_l := hvivp.1
  have hdr_nviv := bv32_viv_zero_of_and_580000 hdr_58
  have hdr_ng_ar := bv32_garb_zero_of_and_580000 hdr_58
  refine ⟨hdr_nviv, ?_, ?_⟩
  · unfold fullArenaClauseGarbCore fullArenaHdrCore
    rcases hvivp.2.2.2.2 dr.toNat (by omega) with heq | ⟨_, _, _, _, _, hset'⟩
    · rw [← heq, List.getElem?_eq_getElem (by omega), Option.getD_some]; simp [hdr_ng_ar]
    · rw [List.getElem?_eq_getElem (by omega)] at hset'
      rw [Option.some.inj hset', bv32_or_viv_garb] at hdr_ng_ar; simp [hdr_ng_ar]
  · have h2 := (m4_scan_cands_ar_lits_eq hcl hw hvivp hdr_ref).1
    unfold fullArenaClauseSizeCore
    rw [← h2, List.getElem?_eq_getElem (by omega), Option.getD_some, hdr_sz_ar]

private theorem m4_scan_cands_stepB_inv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {arp qlA : List (BitVec 32)} {lm1 lmA : List (BitVec 8)}
    {nqlp nn1 : Nat} {dr : BitVec 32}
    (hcl : s.core.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hwp : FullWitnessInv c F0 F_cur { s.core with arena := arp }) (hl0 : s.core.cur_level = 0)
    (hvivA : M4ScanArVivInv c s arp qlA 0 nqlp) (hlm4A : M4LmBit4Inv c lm1 qlA 0 nn1 lmA)
    (hnq_lt : nqlp < c.max_vars) (hdr_ref : dr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hdr_lt : dr.toNat < c.arena_cap)
    (hdr_nviv : (arp[dr.toNat]'(by rw [hvivA.1]; exact hdr_lt) &&& 0x00100000#32) = 0#32) :
    let ar1 := arp.set dr.toNat ((arp[dr.toNat]'(by rw [hvivA.1]; exact hdr_lt)) ||| 0x00100000#32)
    M4ScanArVivInv c s ar1 (qlA.set nqlp dr) 0 (nqlp + 1) ∧
    M4LmBit4Inv c lm1 (qlA.set nqlp dr) 0 nn1 lmA ∧
    FullWitnessInv c F0 F_cur { s.core with arena := ar1 } := by
  have harp_l := hvivA.1
  have hcl_ar : ({ s.core with arena := arp }).LengthsOk c := { hcl with arena_len_arr := harp_l }
  have ⟨_, hviv_next⟩ := m4ScanArVivInv_push hvivA hnq_lt hdr_ref hdr_lt hdr_nviv
  have hlm4_next := m4LmBit4Inv_set_ql_lo hlm4A hnq_lt dr
  have hwp_refs : dr.toNat ∈ fullArenaClauseRefsCore { s.core with arena := arp } := by
    have h1 := (arViv_congr hcl hw fun i hi => by
      rcases hvivA.2.2.2.2 i hi with heq | ⟨t, h0, ht, hqt, _, hset'⟩
      · exact Or.inl heq
      · have ht_ref := (hvivA.2.2.2.1 t h0 ht).1; rw [hqt] at ht_ref
        exact Or.inr ⟨ht_ref, hset'⟩).1
    rw [h1]; exact hdr_ref
  have ⟨_, _, hw_next, _⟩ := fullWitnessInv_set_hdr_bit20 hcl_ar hwp hl0 hwp_refs
    ((arp[dr.toNat]'(by omega)) ||| 0x00100000#32)
    (by unfold fullArenaHdrCore; dsimp only
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact bv32_or_viv_garb _)
    (by unfold fullArenaHdrCore; dsimp only
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact bv32_or_viv_shrk _)
  exact ⟨hviv_next, hlm4_next, hw_next⟩

private theorem m4_scan_cands_lmj_lift {c : FullCfg} {ar : List (BitVec 32)}
    {lm0 lmj : List (BitVec 8)} {qw j csz : Nat}
    (h : LmBit2Inv c ar lm0 qw 0 j lmj) (hj : j ≤ csz) :
    LmBit2Inv c ar lm0 qw 0 csz lmj :=
  ⟨h.1, fun l hl => by
    rcases h.2 l hl with heq | ⟨k, h0, hk, har', hset'⟩
    · exact Or.inl heq
    · exact Or.inr ⟨k, h0, by omega, har', hset'⟩⟩

private def m4ScanCandsMpExpr (h : Val i64) (row_off cur_qn : Val i32) (init_lits : Val i64)
    (pVals pWvec pWstk pAr pLm pScr pCnt pCntd pFl pQl : Val i64)
    (Jq : Cont [i32, i32, i32]) (nql ncntd qi qw : Val i32) (J : Cont [i32, i32])
    (csz : Val i32) (Jm : Cont [i32, i32, i32, i32])
    (min_l min_d fc jf : Val i32) (Jscan : Cont [i32, i32, i32]) :
    Expr Val Cont [i32] :=
  let e0 := FullBvaHeap.full_bva_scan_cands_body Val Cont (h, row_off, cur_qn, init_lits, ())
  let e1 := eLoad64 pVals (eLet64 0#64 e0)
  let e2 := eLoad64 pWvec (eLet64 0#64 e1)
  let e3 := eLoad64 pWstk (eLet64 0#64 e2)
  let e4 := eLoad64 pAr (eLet64 0#64 e3)
  let e5 := eLoad64 pLm (eLet64 0#64 e4)
  let e6 := eLoad64 pScr (eLet64 0#64 e5)
  let e7 := eLoad64 pCnt (eLet64 0#64 e6)
  let e8 := eLoad64 pCntd (eLet64 0#64 e7)
  let e9 := eLoad64 pFl (eLet64 0#64 e8)
  let e10 := eLoad64 pQl (eLet64 0#64 e9)
  let e11 := eThen (eLetBool true (eGrp0_3 Jq (nql, ncntd, qi, ()) e10))
  let e12 := eLoad32 qw (eLet64 0#64 (eLet64 0#64 (eLet64 0#64 (eLet32 0#32 e11))))
  let eL := eElse (eLetBool true (eLet32 0#32 (eGrpBody_2 J e12)))
  let eCsz := eLoad32 csz (eLet64 0#64 (eLet64 0#64 (eLet64 0#64 (eLet64 0#64 eL))))
  let eAfter := eGrp0_4 Jm (min_l, min_d, fc, jf, ()) eCsz
  eGrpBody_3 Jscan eAfter

private def m4ScanCandsUpdExpr (h : Val i64) (row_off cur_qn : Val i32) (init_lits : Val i64)
    (pVals pWvec pWstk pAr pLm pScr pCnt pCntd pFl pQl : Val i64)
    (Jq : Cont [i32, i32, i32]) (nql ncntd qi qw : Val i32) (J : Cont [i32, i32])
    (csz : Val i32) (Jm : Cont [i32, i32, i32, i32]) (min_l min_d fc jf : Val i32)
    (Jscan : Cont [i32, i32, i32]) (mxv : Val i64)
    (Jmp : Cont [i32, i32, i64, i32]) (JmpL : Cont [i32, i32, i64, i32])
    (nqlp ncp : Val i32) (mp mp2 : Val i64) (nnoup dr cand : Val i32) (ok : Val .bool)
    (djf : Val i32) (Jdj : Cont [i32, .bool, i32]) : Expr Val Cont [i32] :=
  let eIf := m4ScanCandsMpExpr h row_off cur_qn init_lits pVals pWvec pWstk pAr pLm pScr pCnt pCntd
    pFl pQl Jq nql ncntd qi qw J csz Jm min_l min_d fc jf Jscan
  let eIn := eThen (eLetBool true (eThen (eLetBool true eIf)))
  let eMxv := eLoad64 mxv (eSkip 10 eIn)
  let eLoop := eThen (eLetBool true (eGrp0_mp JmpL (nqlp, ncp, mp, nnoup, ())
    (eGrpBody_mp Jmp eMxv)))
  let eNotBin := eElse (eSkip 6 eLoop)
  let eNotEnd := eElse (eSkip 1 eNotBin)
  let eNeQw := eElse (eLetBool true (eLet64 mp2 (eLoad32 dr (eSkip 2 eNotEnd))))
  let eHdrOk := eElse (eSkip 8 eNeQw)
  let eSzOk := eElse (eSkip 7 eHdrOk)
  eGrp0_dj Jdj (cand, ok, djf, ()) eSzOk

private theorem m4_scan_cands_upd_wp {Γ : Env} {Q : Post [i32]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {row_off cur_qn : Val i32} {init_lits : Val i64}
    {Jq : Cont [i32, i32, i32]} {nql ncntd qi qw csz min_l min_d fc jf : Val i32}
    {J : Cont [i32, i32]} {Jm : Cont [i32, i32, i32, i32]} {Jscan : Cont [i32, i32, i32]}
    {Jmp JmpL : Cont [i32, i32, i64, i32]}
    {nqlp ncp : Val i32} {mp mp2 : Val i64} {nnoup dr cand : Val i32} {ok : Val .bool}
    {djf : Val i32} {Jdj : Cont [i32, .bool, i32]}
    {arp wsp ws1p qlp : List (BitVec 32)} {lm1 lmp : List (BitVec 8)} {mlm : Mem 64}
    (hcl : s.core.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hl0 : s.core.cur_level = 0) (hil_le : init_lits.toNat ≤ 2 * s.core.cur_vars)
    (hncp_le : ncp.toNat ≤ init_lits.toNat)
    (hwsp_l : wsp.length = 2 * c.max_vars) (hws1p_l : ws1p.length = 2 * c.max_vars)
    (hvivp : M4ScanArVivInv c s arp qlp 0 nqlp.toNat)
    (hlm4p : M4LmBit4Inv c lm1 qlp 0 nnoup.toNat lmp)
    (hwp : FullWitnessInv c F0 F_cur { s.core with arena := arp })
    (hcntdp : ∀ i < ncp.toNat, (ws1p[i]?.getD 0#32).toNat < init_lits.toNat)
    (hdr_ref : dr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hdr_lt_ar : dr.toNat + 3 ≤ arp.length)
    (hdr_nviv : (arp[dr.toNat]'(by omega) &&& 0x00100000#32) = 0#32)
    (hmlm : (FullMem c (FullState.mk { s.core with arena := arp, lit_mark := lmp }
      { s.scratch with wsort := wsp, work_stk1 := ws1p, work_stk2 := qlp }) ⋆ R) mlm)
    (hNext : ∀ nql' nc' nnou' ar' lm' ws' ws1' ql' m',
      nc'.toNat ≤ init_lits.toNat ∧ ws'.length = 2 * c.max_vars ∧
      ws1'.length = 2 * c.max_vars ∧ M4ScanArVivInv c s ar' ql' 0 nql'.toNat ∧
      M4LmBit4Inv c lm1 ql' 0 nnou'.toNat lm' ∧
      FullWitnessInv c F0 F_cur { s.core with arena := ar' } ∧
      (∀ i < nc'.toNat, (ws1'[i]?.getD 0#32).toNat < init_lits.toNat) ∧
      (FullMem c (FullState.mk { s.core with arena := ar', lit_mark := lm' }
        { s.scratch with wsort := ws', work_stk1 := ws1', work_stk2 := ql' }) ⋆ R) m' →
      JmpL (nql', nc', mp2, nnou', ()) m') :
    wp Γ Q X (m4ScanCandsUpdExpr c.hdr row_off cur_qn init_lits
      c.pVals c.pWvec c.pWstk c.pArena c.pLitMark c.pScratchBuf c.pWsort
      c.pWorkStk1 c.pFlags c.pWorkStk2 Jq nql ncntd qi qw J csz Jm min_l min_d fc jf Jscan
      (BitVec.ofNat 64 c.max_vars) Jmp JmpL nqlp ncp mp mp2 nnoup dr cand ok djf Jdj)
      mlm := by
  have hmx := c.hmaxv; have har_b := c.harena; unfold dimacsBound at hmx har_b
  have hcv_le := hcl.cur_vars_le; have hvals_len := hcl.vals_len; have hfl_len := hcl.flags_len
  have harp_l := hvivp.1; have hqlp_l := hvivp.2.1; have hlmp_l := hlm4p.1
  have hset : ∀ x : BitVec 32, (BitVec.setWidth 64 x).toNat = x.toNat := bv64_setWidth_32
  let mkSt (ar : List (BitVec 32)) (lm : List (BitVec 8)) (ws ws1 ws2 : List (BitVec 32)) :
      FullState :=
    { core := { s.core with arena := ar, lit_mark := lm }
      scratch := { s.scratch with wsort := ws, work_stk1 := ws1, work_stk2 := ws2 } }
  dsimp only [m4ScanCandsUpdExpr, m4ScanCandsMpExpr, eLet64, eLet32, eLetBool, eLoad64, eLoad32,
    eThen, eElse, eGrp0_3, eGrp0_4, eGrpBody_2, eGrpBody_3, eGrpBody_mp, eGrp0_mp, eGrp0_dj,
    eSkip, FullBvaHeap.full_bva_scan_cands_body]
  refine wp_join_state (α := BitVec 32 × BitVec 32 × BitVec 32 ×
      List (BitVec 32) × List (BitVec 8) × List (BitVec 32) ×
      List (BitVec 32) × List (BitVec 32))
    (fun ⟨nql', nc', nnou', _, _, _, _, _⟩ => (nql', nc', nnou', ()))
    (fun ⟨nql', nc', nnou', ar', lm', ws', ws1', ql'⟩ m' =>
      nc'.toNat ≤ init_lits.toNat ∧ ws'.length = 2 * c.max_vars ∧
      ws1'.length = 2 * c.max_vars ∧ M4ScanArVivInv c s ar' ql' 0 nql'.toNat ∧
      M4LmBit4Inv c lm1 ql' 0 nnou'.toNat lm' ∧
      FullWitnessInv c F0 F_cur { s.core with arena := ar' } ∧
      (∀ i < nc'.toNat, (ws1'[i]?.getD 0#32).toNat < init_lits.toNat) ∧
      (FullMem c (mkSt ar' lm' ws' ws1' ql') ⋆ R) m')
    (fun _ ⟨nql', nc', nnou', ar', lm', ws', ws1', ql'⟩ m' h =>
      hNext nql' nc' nnou' ar' lm' ws' ws1' ql' m' h)
    (fun Jupd hJupd => ?_)
  c0_hsteps_nogrp
  · have hcand_il : cand.toNat < init_lits.toNat := by simp only [bv_c0] at *; omega
    have hcand_lt : cand.toNat < 2 * c.max_vars := by omega
    refine wp_join_state (α := BitVec 32 × List (BitVec 8) × List (BitVec 32))
      (fun ⟨nn1, _, _⟩ => (nn1, ()))
      (fun ⟨nn1, lmA, qlA⟩ mA =>
        M4ScanArVivInv c s arp qlA 0 nqlp.toNat ∧ M4LmBit4Inv c lm1 qlA 0 nn1.toNat lmA ∧
        (FullMem c (mkSt arp lmA wsp ws1p qlA) ⋆ R) mA)
      (fun _ ⟨nn1, lmA, qlA⟩ mA ⟨hvivA, hlm4A, hmA⟩ => ?_)
      (fun Ja hJa => ?_)
    · clear hmlm
      dsimp only [mkSt] at hmA
      have hqlA_l := hvivA.2.1
      c0_hsteps_nogrp
      refine wp_join_state (α := BitVec 32 × List (BitVec 32) × List (BitVec 32))
        (fun ⟨nq1, _, _⟩ => (nq1, ()))
        (fun ⟨nq1, arB, qlB⟩ mB =>
          M4ScanArVivInv c s arB qlB 0 nq1.toNat ∧ M4LmBit4Inv c lm1 qlB 0 nn1.toNat lmA ∧
          FullWitnessInv c F0 F_cur { s.core with arena := arB } ∧
          (FullMem c (mkSt arB lmA wsp ws1p qlB) ⋆ R) mB)
        (fun _ ⟨nq1, arB, qlB⟩ mB ⟨hvivB, hlm4B, hwB, hmB⟩ => ?_)
        (fun Jb hJb => ?_)
      · clear hmA
        dsimp only [mkSt] at hmB
        have hcand_ws : (BitVec.setWidth 64 cand).toNat < wsp.length := by rw [hset, hwsp_l]; omega
        c0_hsteps_nogrp
        refine wp_join_state1 (t := i32) (α := BitVec 32 × List (BitVec 32)) (fun st => st.1)
          (fun ⟨nc1, ws1C⟩ mC =>
            nc1.toNat ≤ init_lits.toNat ∧ ws1C.length = 2 * c.max_vars ∧
            (∀ i < nc1.toNat, (ws1C[i]?.getD 0#32).toNat < init_lits.toNat) ∧
            (FullMem c (mkSt arB lmA wsp ws1C qlB) ⋆ R) mC)
          (fun _ ⟨nc1, ws1C⟩ mC ⟨hnc1, hws1C_l, hcntdC, hmC⟩ => ?_)
          (fun Jc1 hJc1 => ?_)
        · clear hmB
          dsimp only [mkSt] at hmC
          c0_hfast
          · exact hJupd ⟨nq1, nc1, nn1, arB, lmA, _, ws1C, qlB⟩ m
              ⟨hnc1, by simp [hwsp_l], hws1C_l, hvivB, hlm4B, hwB, hcntdC, hm⟩
          · exact hJupd ⟨nq1, nc1, nn1, arB, lmA, wsp, ws1C, qlB⟩ mC
              ⟨hnc1, hwsp_l, hws1C_l, hvivB, hlm4B, hwB, hcntdC, hmC⟩
        · c0_hfast
          · dsimp only at hm
            have hnc1_n : (ncp + 1#32).toNat = ncp.toNat + 1 := by simp only [bv_c0] at *; omega
            refine hJc1 ⟨ncp + 1#32, _⟩ m ⟨by rw [hnc1_n]; omega,
              by simp [hws1p_l], fun i hi => ?_, hm⟩
            rw [hnc1_n] at hi
            by_cases hie : i = ncp.toNat
            · subst hie
              rw [hset, List.getElem?_set_self (by rw [hws1p_l]; omega), Option.getD_some]
              exact hcand_il
            · rw [hset, List.getElem?_set_ne (Ne.symm hie)]; exact hcntdp i (by omega)
          · exact hJc1 ⟨ncp, ws1p⟩ mB ⟨hncp_le, hws1p_l, hcntdp, hmB⟩
          · exact hJc1 ⟨ncp, ws1p⟩ mB ⟨hncp_le, hws1p_l, hcntdp, hmB⟩
      · c0_hsplit
        · have hnq_lt : nqlp.toNat < c.max_vars := by simp only [bv_c0] at *; omega
          have hnq1 : (nqlp + 1#32).toNat = nqlp.toNat + 1 := by simp only [bv_c0]; omega
          have hnq_ql : (BitVec.setWidth 64 nqlp).toNat < qlA.length := by rw [hset, hqlA_l]; omega
          have hdr_ar : (BitVec.setWidth 64 dr).toNat < arp.length := by rw [hset]; omega
          c0_hfast
          have ⟨hviv_next, hlm4_next, hw_next⟩ :=
            m4_scan_cands_stepB_inv hcl hw hwp hl0 hvivA hlm4A hnq_lt hdr_ref (by omega) hdr_nviv
          simp only [hset] at hm
          exact hJb ⟨nqlp + 1#32, _, _⟩ m ⟨by rw [hnq1]; exact hviv_next, hlm4_next, hw_next, hm⟩
        · c0_hfast; exact hJb ⟨nqlp, arp, qlA⟩ mA ⟨hvivA, hlm4A, hwp, hmA⟩
    · c0_hsplit
      · have hnn_lt : nnoup.toNat < c.max_vars := by simp only [bv_c0] at *; omega
        have hnn1 : (nnoup + 1#32).toNat = nnoup.toNat + 1 := by simp only [bv_c0]; omega
        have hmxnn : (BitVec.ofNat 64 c.max_vars + BitVec.setWidth 64 nnoup).toNat =
            c.max_vars + nnoup.toNat := by simp only [bv_c0]; omega
        have hmxnn_ql : (BitVec.ofNat 64 c.max_vars + BitVec.setWidth 64 nnoup).toNat <
            qlp.length := by rw [hmxnn, hqlp_l]; omega
        have hcand_lm : (BitVec.setWidth 64 cand).toNat < lmp.length := by rw [hset, hlmp_l]; omega
        c0_hfast
        simp only [hmxnn] at hm; simp only [hset] at hm
        try simp only [bv8_trunc_or_4] at hm
        try simp only [bv8_trunc_or_w] at hm
        exact hJa ⟨nnoup + 1#32, _, _⟩ _
          ⟨m4ScanArVivInv_set_ql_hi hvivp (by omega) cand,
           by rw [hnn1]; exact m4LmBit4Inv_push hqlp_l hlm4p hnn_lt hcand_lt, hm⟩
      · c0_hfast; exact hJa ⟨nnoup, lmp, qlp⟩ mlm ⟨hvivp, hlm4p, hmlm⟩
  all_goals
    exact hJupd ⟨nqlp, ncp, nnoup, arp, lmp, wsp, ws1p, qlp⟩ mlm
      ⟨hncp_le, hwsp_l, hws1p_l, hvivp, hlm4p, hwp, hcntdp, hmlm⟩

private theorem m4_scan_cands_mp_wp {Γ : Env} {Q : Post [i32]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {row_off cur_qn : Val i32} {init_lits : Val i64}
    {Jq : Cont [i32, i32, i32]} {nql ncntd qi qw csz min_l min_d fc jf : Val i32}
    {J : Cont [i32, i32]} {Jm : Cont [i32, i32, i32, i32]} {Jscan : Cont [i32, i32, i32]}
    {ar ws ws1 ws2 : List (BitVec 32)} {lm1 : List (BitVec 8)} {mf : Mem 64}
    (hcl : s.core.LengthsOk c) (_hsc : s.scratch.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur s.core) (hdw : DenseWatchesInv F_cur s.core)
    (hl0 : s.core.cur_level = 0) (hil_le : init_lits.toNat ≤ 2 * s.core.cur_vars)
    (hnc_le : ncntd.toNat ≤ init_lits.toNat)
    (hws_l : ws.length = 2 * c.max_vars) (hws1_l : ws1.length = 2 * c.max_vars)
    (hviv : M4ScanArVivInv c s ar ws2 0 nql.toNat)
    (hw_ar : FullWitnessInv c F0 F_cur { s.core with arena := ar })
    (hcntd_ok : ∀ i < ncntd.toNat, (ws1[i]?.getD 0#32).toNat < init_lits.toNat)
    (hlm1_l : lm1.length = 2 * c.max_vars)
    (hlm1_b2 : ∀ l < 2 * c.max_vars, (lm1[l]?.getD 0#8 &&& 4#8) = 0#8)
    (hmin_ok : min_l ≠ 0xFFFFFFFF#32 →
      min_l.toNat < 2 * s.core.cur_vars ∧ min_d.toNat = fullWatchSizeCore s.core min_l.toNat)
    (hmf : (FullMem c (FullState.mk { s.core with arena := ar, lit_mark := lm1 }
      { s.scratch with wsort := ws, work_stk1 := ws1, work_stk2 := ws2 }) ⋆ R) mf)
    (hJscan : ∀ nql2 nc2 jf2 ar2 ws2' ws12 ql2 mf2,
      nc2.toNat ≤ init_lits.toNat ∧ ws2'.length = 2 * c.max_vars ∧
      ws12.length = 2 * c.max_vars ∧ M4ScanArVivInv c s ar2 ql2 0 nql2.toNat ∧
      FullWitnessInv c F0 F_cur { s.core with arena := ar2 } ∧
      (∀ i < nc2.toNat, (ws12[i]?.getD 0#32).toNat < init_lits.toNat) ∧
      (FullMem c (FullState.mk { s.core with arena := ar2, lit_mark := lm1 }
        { s.scratch with wsort := ws2', work_stk1 := ws12, work_stk2 := ql2 }) ⋆ R) mf2 →
      Jscan (nql2, nc2, jf2, ()) mf2) :
    wp Γ Q X (m4ScanCandsMpExpr c.hdr row_off cur_qn init_lits
      c.pVals c.pWvec c.pWstk c.pArena c.pLitMark c.pScratchBuf c.pWsort
      c.pWorkStk1 c.pFlags c.pWorkStk2 Jq nql ncntd qi qw J csz Jm min_l min_d fc jf Jscan)
      mf := by
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena
  unfold dimacsBound at hmx hwcap har_b
  have hcv_le := hcl.cur_vars_le; have hwv_len := hcl.wvec_len; have hws_len := hcl.wstk_len_arr
  have hal_le := hcl.arena_len_le; have hwlen_le := hcl.wlen_le
  have hvals_len := hcl.vals_len; have hfl_len := hcl.flags_len
  have hset : ∀ x : BitVec 32, (BitVec.setWidth 64 x).toNat = x.toNat := bv64_setWidth_32
  let mkSt (ar : List (BitVec 32)) (lm : List (BitVec 8)) (ws ws1 ws2 : List (BitVec 32)) :
      FullState :=
    { core := { s.core with arena := ar, lit_mark := lm }
      scratch := { s.scratch with wsort := ws, work_stk1 := ws1, work_stk2 := ws2 } }
  dsimp only [m4ScanCandsMpExpr, eLet64, eLet32, eLetBool, eLoad64, eLoad32, eThen, eElse,
    eGrp0_3, eGrp0_4, eGrpBody_2, eGrpBody_3, FullBvaHeap.full_bva_scan_cands_body]
  c0_hfast
  · have hmin_ne : min_l ≠ 0xFFFFFFFF#32 := by assumption
    obtain ⟨hml_lt, hmd_eq⟩ := hmin_ok hmin_ne
    have hml_bd := hdw.layout.bounds min_l.toNat hml_lt
    have hml_sl := hdw.slices min_l.toNat hml_lt
    have h2ml_n : (BitVec.setWidth 64 min_l <<< (1 : Nat)).toNat = 2 * min_l.toNat := by
      simp only [bv_c0]; omega
    have h2ml_mod : 2 * min_l.toNat % 2 ^ 64 = 2 * min_l.toNat := Nat.mod_eq_of_lt (by omega)
    have hmoff_eq : (s.core.wvec[2 * min_l.toNat]'(by omega)).toNat =
        fullWatchOffCore s.core min_l.toNat := by
      unfold fullWatchOffCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    let moff0 := fullWatchOffCore s.core min_l.toNat
    let msz0 := fullWatchSizeCore s.core min_l.toNat
    c0_hsteps_nogrp
    refine wp_join_state (α := BitVec 32 × BitVec 32 × BitVec 64 × BitVec 32 ×
        List (BitVec 32) × List (BitVec 8) × List (BitVec 32) × List (BitVec 32) ×
        List (BitVec 32))
      (fun ⟨nql2, nc2, mp2, nnou2, _, _, _, _, _⟩ => (nql2, nc2, mp2, nnou2, ()))
      (fun ⟨nql2, nc2, _, nnou2, ar2, lm2, ws2', ws12, ql2⟩ mmp =>
        nc2.toNat ≤ init_lits.toNat ∧ ws2'.length = 2 * c.max_vars ∧
        ws12.length = 2 * c.max_vars ∧
        M4ScanArVivInv c s ar2 ql2 0 nql2.toNat ∧
        M4LmBit4Inv c lm1 ql2 0 nnou2.toNat lm2 ∧
        FullWitnessInv c F0 F_cur { s.core with arena := ar2 } ∧
        (∀ i < nc2.toNat, (ws12[i]?.getD 0#32).toNat < init_lits.toNat) ∧
        (FullMem c (mkSt ar2 lm2 ws2' ws12 ql2) ⋆ R) mmp)
      (fun _ ⟨nql2, nc2, _mp2, nnou2, ar2, lm2, ws2', ws12, ql2⟩ mmp
          ⟨hnc2, hws2'_l, hws12_l, hviv2, hlm4_2, hw2, hcntd2, hmmp⟩ => ?_)
      (fun Jmp hJmp => ?_)
    · clear hmf
      dsimp only [mkSt] at hmmp
      have hql2_l := hviv2.2.1
      refine wp_loop_inv
        (fun (j, ()) mj4 => ∃ lmj4,
          j.toNat ≤ nnou2.toNat ∧ M4LmBit4Inv c lm1 ql2 j.toNat nnou2.toNat lmj4 ∧
          (FullMem c (mkSt ar2 lmj4 ws2' ws12 ql2) ⋆ R) mj4)
        (fun (j, ()) _ => nnou2.toNat - j.toNat)
        (fun Jc4 hJc4 => by
          c0_hfast; exact hJc4 (0#32, ()) mmp ⟨lm2, Nat.zero_le _, hlm4_2, hmmp⟩)
        (fun Jc4 (j, ()) mj4 ⟨lmj4, hj4_le, hlmj4, hmj4⟩ ihc4 => ?_)
      clear hmmp
      dsimp only [mkSt] at hmj4
      have hlmj4_l := hlmj4.1; have hnn2_le := hlmj4.2.1
      c0_hsplit
      · have hj4_lt : j.toNat < nnou2.toNat := by assumption
        have hj4_1 : (j + 1#32).toNat = j.toNat + 1 := by simp only [bv_c0]; omega
        have hmxj : (BitVec.ofNat 64 c.max_vars + BitVec.setWidth 64 j).toNat =
            c.max_vars + j.toNat := by simp only [bv_c0]; omega
        have hmxj_ql : (BitVec.ofNat 64 c.max_vars + BitVec.setWidth 64 j).toNat < ql2.length := by
          rw [hmxj, hql2_l]; omega
        have ⟨hcl_lt, hstep4⟩ := m4LmBit4Inv_clear_step hlm1_l hql2_l hlm1_b2 hlmj4 hj4_lt
        have hcl_lm : (BitVec.setWidth 64 (ql2[(BitVec.ofNat 64 c.max_vars +
            BitVec.setWidth 64 j).toNat]'hmxj_ql)).toNat < lmj4.length := by
          simp only [hmxj, hset]; omega
        c0_hfast
        simp only [hmxj] at hm; simp only [hset] at hm
        try simp only [bv8_trunc_and_fb] at hm
        try simp only [bv8_trunc_and_w] at hm
        exact ihc4 (j + 1#32, ()) m (by dsimp only; rw [hj4_1]; omega)
          ⟨_, by rw [hj4_1]; omega, by rw [hj4_1]; exact hstep4, hm⟩
      · have hj4_eq : j.toNat = nnou2.toNat := by omega
        rw [hj4_eq] at hlmj4
        have hlm_eq1 : lmj4 = lm1 := m4LmBit4Inv_done hlm1_l hlmj4
        rw [hlm_eq1] at hmj4
        c0_hfast
        exact hJscan nql2 nc2 j ar2 ws2' ws12 ql2 mj4
          ⟨hnc2, hws2'_l, hws12_l, hviv2, hw2, hcntd2, hmj4⟩
    · refine wp_loop_inv
        (fun (nqlp, ncp, mp, nnoup, ()) mlm => ∃ arp lmp wsp ws1p qlp,
          moff0 ≤ mp.toNat ∧ mp.toNat ≤ moff0 + msz0 ∧ ncp.toNat ≤ init_lits.toNat ∧
          wsp.length = 2 * c.max_vars ∧ ws1p.length = 2 * c.max_vars ∧
          M4ScanArVivInv c s arp qlp 0 nqlp.toNat ∧
          M4LmBit4Inv c lm1 qlp 0 nnoup.toNat lmp ∧
          FullWitnessInv c F0 F_cur { s.core with arena := arp } ∧
          DenseWatchSliceOk F_cur s.core min_l.toNat mp.toNat (moff0 + msz0 - mp.toNat) ∧
          (∀ i < ncp.toNat, (ws1p[i]?.getD 0#32).toNat < init_lits.toNat) ∧
          (FullMem c (mkSt arp lmp wsp ws1p qlp) ⋆ R) mlm)
        (fun (_, _, mp, _, _) _ => moff0 + msz0 - mp.toNat)
        (fun JmpL hJmpL => by
          c0_hfast
          have h1 : (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 min_l <<<
              (1 : Nat)).toNat]'(by rw [h2ml_n]; omega))).toNat = moff0 := by
            simp only [h2ml_n, hset, hmoff_eq]; rfl
          dsimp only
          exact hJmpL (nql, ncntd, _, 0#32, ()) mf
            ⟨ar, lm1, ws, ws1, ws2, by rw [h1]; exact Nat.le_refl _, by rw [h1]; omega,
             hnc_le, hws_l, hws1_l, hviv, m4LmBit4Inv_init hlm1_l, hw_ar,
             by simpa only [h1, Nat.add_sub_cancel_left] using hml_sl, hcntd_ok, hmf⟩)
        (fun JmpL (nqlp, ncp, mp, nnoup, ()) mlm
            ⟨arp, lmp, wsp, ws1p, qlp, hmp_ge, hmp_le, hncp_le, hwsp_l, hws1p_l, hvivp,
             hlm4p, hwp, hrem, hcntdp, hmlm⟩ ihmp => ?_)
      clear hmf
      dsimp only [mkSt] at hmlm
      have harp_l := hvivp.1; have hqlp_l := hvivp.2.1; have hnqlp_le := hvivp.2.2.1
      have hlmp_l := hlm4p.1; have hnnoup_le := hlm4p.2.1
      have hm_end_mod : ((s.core.wvec[2 * min_l.toNat % 2 ^ 64]'(by
          rw [h2ml_mod]; omega)).toNat + min_d.toNat) % 2 ^ 64 = moff0 + msz0 := by
        simp only [h2ml_mod, hmoff_eq, hmd_eq]; exact Nat.mod_eq_of_lt (by omega)
      c0_hsplit
      · have hmp_lt : mp.toNat < moff0 + msz0 := by rw [← hm_end_mod]; assumption
        have hmp_ws : mp.toNat < s.core.wstk.length := by omega
        have hmp1_n : (mp + 1#64).toNat = mp.toNat + 1 := by simp only [bv_c0]; omega
        c0_hfast
        · have ⟨_, _, hrem_next⟩ :=
            FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega) hmp_ws (by assumption)
          exact ihmp (nqlp, ncp, mp + 1#64, nnoup, ()) mlm (by dsimp only; rw [hmp1_n]; omega)
            ⟨arp, lmp, wsp, ws1p, qlp, by rw [hmp1_n]; omega, by rw [hmp1_n]; omega,
             hncp_le, hwsp_l, hws1p_l, hvivp, hlm4p, hwp,
             by rw [hmp1_n, show moff0 + msz0 - (mp.toNat + 1) =
                  moff0 + msz0 - mp.toNat - 1 by omega]; exact hrem_next,
             hcntdp, hmlm⟩
        · exact hJmp ⟨nqlp, ncp, mp + 1#64, nnoup, arp, lmp, wsp, ws1p, qlp⟩ mlm
            ⟨hncp_le, hwsp_l, hws1p_l, hvivp, hlm4p, hwp, hcntdp, hmlm⟩
        · have ⟨_, hrem_next⟩ :=
            FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hmp_ws (by assumption)
          have hmp2_n : (mp + 1#64 + 1#64).toNat = mp.toNat + 2 := by simp only [bv_c0]; omega
          exact ihmp (nqlp, ncp, mp + 1#64 + 1#64, nnoup, ()) mlm
            (by dsimp only; rw [hmp2_n]; omega)
            ⟨arp, lmp, wsp, ws1p, qlp, by rw [hmp2_n]; omega, by rw [hmp2_n]; omega,
             hncp_le, hwsp_l, hws1p_l, hvivp, hlm4p, hwp,
             by rw [hmp2_n, show moff0 + msz0 - (mp.toNat + 2) =
                  moff0 + msz0 - mp.toNat - 2 by omega]; exact hrem_next,
             hcntdp, hmlm⟩
        · have ⟨h2le, hrem_next⟩ :=
            FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hmp_ws (by assumption)
          have hmp1_ws : mp.toNat + 1 < s.core.wstk.length := by omega
          have hmp1_mod : (mp.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = mp.toNat + 1 := by
            rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega
          have ⟨_, hdr_ref, _⟩ :=
            FullBvaFwdHelpers.fwd_slice_occ_info hrem (by omega) hmp_ws hmp1_ws (by assumption)
          have hdr_wf := hw.arena.refs_wf _ hdr_ref
          have hmp2_n : (mp + 1#64 + 1#64).toNat = mp.toNat + 2 := by simp only [bv_c0]; omega
          let dr := s.core.wstk[mp.toNat + 1]'hmp1_ws
          have hdr_lt_ar : dr.toNat + 3 ≤ arp.length := by
            dsimp only [dr]; have := hdr_wf.1; have := hcl.arena_len_le; omega
          have hdr_eq : s.core.wstk[(mp + 1#64).toNat]'(by rw [hmp1_n]; exact hmp1_ws) = dr := by
            dsimp only [dr]; simp only [hmp1_n]
          have hdr_mod : s.core.wstk[(mp.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(
              by rw [hmp1_mod]; exact hmp1_ws) = dr := by dsimp only [dr]; simp only [hmp1_mod]
          have hdr2_n : (BitVec.setWidth 64 dr + 2).toNat = dr.toNat + 2 := by
            change (BitVec.setWidth 64 dr + 2#64).toNat = _; simp only [bv_c0]; omega
          have hdr0_ar : (BitVec.setWidth 64 (s.core.wstk[(mp.toNat +
              BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                rw [hmp1_mod]; exact hmp1_ws))).toNat < arp.length := by rw [hdr_mod, hset]; omega
          have hdr2_ar : (BitVec.setWidth 64 (s.core.wstk[(mp.toNat +
              BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                rw [hmp1_mod]; exact hmp1_ws)) + 2).toNat < arp.length := by
            rw [hdr_mod, hdr2_n]; omega
          have hdr0_ar' : (BitVec.setWidth 64 (s.core.wstk[(mp + 1#64).toNat]'(by
              rw [hmp1_n]; exact hmp1_ws))).toNat < arp.length := by rw [hdr_eq, hset]; omega
          have hdr2_ar' : (BitVec.setWidth 64 (s.core.wstk[(mp + 1#64).toNat]'(by
              rw [hmp1_n]; exact hmp1_ws)) + 2).toNat < arp.length := by rw [hdr_eq, hdr2_n]; omega
          c0_hsteps_nogrp
          · exact ihmp (nqlp, ncp, mp + 1#64 + 1#64, nnoup, ()) mlm
              (by dsimp only; rw [hmp2_n]; omega)
              ⟨arp, lmp, wsp, ws1p, qlp, by rw [hmp2_n]; omega, by rw [hmp2_n]; omega,
               hncp_le, hwsp_l, hws1p_l, hvivp, hlm4p, hwp,
               by rw [hmp2_n, show moff0 + msz0 - (mp.toNat + 2) =
                    moff0 + msz0 - mp.toNat - 2 by omega]; exact hrem_next,
               hcntdp, hmlm⟩
          · exact ihmp (nqlp, ncp, mp + 1#64 + 1#64, nnoup, ()) mlm
              (by dsimp only; rw [hmp2_n]; omega)
              ⟨arp, lmp, wsp, ws1p, qlp, by rw [hmp2_n]; omega, by rw [hmp2_n]; omega,
               hncp_le, hwsp_l, hws1p_l, hvivp, hlm4p, hwp,
               by rw [hmp2_n, show moff0 + msz0 - (mp.toNat + 2) =
                    moff0 + msz0 - mp.toNat - 2 by omega]; exact hrem_next,
               hcntdp, hmlm⟩
          · have hdr_58 : (arp[dr.toNat]'(by omega) &&& 0x00580000#32) = 0#32 := by
              have h1 : (arp[(BitVec.setWidth 64
                  (s.core.wstk[(mp.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                    rw [hmp1_mod]; exact hmp1_ws))).toNat]'(by
                      rw [hdr_mod, hset]; omega) &&& (5767168 : BitVec 32)) = 0#32 := by
                simpa only [← hdr_mod] using (by assumption : _)
              simp only [hdr_mod] at h1
              simpa only [hset, show (5767168 : BitVec 32) = 0x00580000#32 from rfl] using h1
            have hdr_sz_ar : arp[dr.toNat + 2]'(by omega) = csz := by
              have hdr2_mod : (dr.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = dr.toNat + 2 :=
                by rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl]; omega
              have h2 : arp[(dr.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
                  rw [hdr2_mod]; omega) = csz := by
                simpa only [← hdr_mod] using (by assumption : _)
              simpa only [hdr2_mod] using h2
            have ⟨hdr_nviv, hdr_ng_s, hdr_sz_eq⟩ :=
              m4_scan_cands_dr_info hcl hw hvivp hdr_ref hdr_lt_ar hdr_58 hdr_sz_ar
            c0_hsteps_nogrp
            refine wp_join_state (α := BitVec 32 × Bool × BitVec 32)
              (fun ⟨cand, ok, djf⟩ => (cand, ok, djf, ()))
              (fun _ mdj => mdj = mlm)
              (fun _ ⟨cand, ok, _djf⟩ mdj hmdj => ?_)
              (fun Jdj hJdj => ?_)
            · rcases hmdj with rfl
              dsimp only
              have hupd := m4_scan_cands_upd_wp (Γ := Γ) (Q := Q) (X := X) (row_off := row_off)
                (cur_qn := cur_qn) (Jq := Jq) (nql := nql) (ncntd := ncntd) (qi := qi) (qw := qw)
                (J := J) (csz := csz) (Jm := Jm) (min_l := min_l) (min_d := min_d) (fc := fc)
                (jf := jf) (Jscan := Jscan) (Jmp := fun _ _ => True) (JmpL := JmpL) (mp := mp)
                (mp2 := mp + 1#64 + 1#64)
                (dr := s.core.wstk[(mp + 1#64).toNat]'(by rw [hmp1_n]; exact hmp1_ws))
                (cand := cand) (ok := ok) (djf := _djf) (Jdj := fun _ _ => True)
                hcl hw hl0 hil_le hncp_le hwsp_l hws1p_l hvivp hlm4p hwp hcntdp
                (by rw [hdr_eq]; exact hdr_ref) (by rw [hdr_eq]; exact hdr_lt_ar)
                (by simpa only [hdr_eq] using hdr_nviv) hmlm
                (fun nql' nc' nnou' ar' lm' ws' ws1' ql' m'
                    ⟨hnc', hws', hws1', hviv', hlm4', hw', hcntd', hm'⟩ =>
                  ihmp (nql', nc', mp + 1#64 + 1#64, nnou', ()) m'
                    (by dsimp only; rw [hmp2_n]; omega)
                    ⟨ar', lm', ws', ws1', ql', by rw [hmp2_n]; omega, by rw [hmp2_n]; omega,
                     hnc', hws', hws1', hviv', hlm4', hw',
                     by rw [hmp2_n, show moff0 + msz0 - (mp.toNat + 2) =
                          moff0 + msz0 - mp.toNat - 2 by omega]; exact hrem_next,
                     hcntd', hm'⟩)
              dsimp only [m4ScanCandsUpdExpr, m4ScanCandsMpExpr, eLet64, eLet32, eLetBool, eLoad64,
                eLoad32, eThen, eElse, eGrp0_3, eGrp0_4, eGrpBody_2, eGrpBody_3, eGrpBody_mp,
                eGrp0_mp, eGrp0_dj, eSkip, FullBvaHeap.full_bva_scan_cands_body] at hupd
              exact hupd
            · refine wp_loop_inv
                (fun (cand, dj, ()) mdj => mdj = mlm ∧ dj.toNat ≤ csz.toNat)
                (fun (_, dj, _) _ => csz.toNat - dj.toNat)
                (fun Jd hJd => by
                  c0_hfast; exact hJd (0xFFFFFFFF#32, 0#32, ()) mlm ⟨rfl, Nat.zero_le _⟩)
                (fun Jd (cand, dj, ()) mdj ⟨hmdj, hdj_le⟩ ihd => ?_)
              rcases hmdj with rfl
              c0_hsplit
              · have hdj_lt : dj.toNat < csz.toNat := by assumption
                have hdj1 : (dj + 1#32).toNat = dj.toNat + 1 := by simp only [bv_c0]; omega
                have har_len := hcl.arena_len_arr
                have hdr_end : dr.toNat + 3 + csz.toNat ≤ s.core.arena_len := by
                  dsimp only [dr]; have := hdr_wf.2.2.1; have := hdr_wf.2.2.2.1; omega
                have hdj_sz : dj.toNat < fullArenaClauseSizeCore s.core dr.toNat := by
                  rw [hdr_sz_eq]; exact hdj_lt
                have hdrj_n : (BitVec.setWidth 64 dr + 3 + BitVec.setWidth 64 dj).toNat =
                    dr.toNat + 3 + dj.toNat := by
                  change (BitVec.setWidth 64 dr + 3#64 + BitVec.setWidth 64 dj).toNat = _
                  simp only [bv_c0]; omega
                have hdl_eq : arp[dr.toNat + 3 + dj.toNat]'(by omega) =
                    s.core.arena[dr.toNat + 3 + dj.toNat]'(by omega) := by
                  have h1 := (m4_scan_cands_ar_lits_eq hcl hw hvivp hdr_ref).2 dj.toNat hdj_sz
                  rw [List.getElem?_eq_getElem (by omega),
                    List.getElem?_eq_getElem (by omega)] at h1
                  exact Option.some.inj h1
                have hdl_lt : (arp[dr.toNat + 3 + dj.toNat]'(by omega)).toNat <
                    2 * s.core.cur_vars := by
                  rw [hdl_eq]
                  exact hw.arena.lits_lt dr.toNat hdr_ref hdr_ng_s _ (List.mem_of_getElem?
                    (FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem hdj_sz (by omega)))
                have hdrj_ar : (BitVec.setWidth 64 (s.core.wstk[(mp.toNat +
                    BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                      rw [hmp1_mod]; exact hmp1_ws)) + 3 + BitVec.setWidth 64 dj).toNat <
                    arp.length := by rw [hdr_mod, hdrj_n, harp_l]; dsimp only [dr]; omega
                have hdl_lm : (BitVec.setWidth 64 (arp[(BitVec.setWidth 64
                    (s.core.wstk[(mp.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                      rw [hmp1_mod]; exact hmp1_ws)) + 3 +
                    BitVec.setWidth 64 dj).toNat]'hdrj_ar)).toNat < lmp.length := by
                  simp only [hdr_mod]; simp only [hdrj_n, hset]; omega
                have hdrj_ar' : (BitVec.setWidth 64 (s.core.wstk[(mp + 1#64).toNat]'(by
                    rw [hmp1_n]; exact hmp1_ws)) + 3 + BitVec.setWidth 64 dj).toNat <
                    arp.length := by rw [hdr_eq, hdrj_n, harp_l]; dsimp only [dr]; omega
                have hdl_lm' : (BitVec.setWidth 64 (arp[(BitVec.setWidth 64
                    (s.core.wstk[(mp + 1#64).toNat]'(by rw [hmp1_n]; exact hmp1_ws)) + 3 +
                    BitVec.setWidth 64 dj).toNat]'hdrj_ar')).toNat < lmp.length := by
                  simp only [hdr_eq]; simp only [hdrj_n, hset]; omega
                c0_hfast
                · exact hJdj ⟨cand, false, dj⟩ mdj rfl
                · exact hJdj ⟨cand, false, dj⟩ mdj rfl
                · exact ihd (_, dj + 1#32, ()) mdj (by dsimp only; rw [hdj1]; omega)
                    ⟨rfl, by rw [hdj1]; omega⟩
                · exact ihd (cand, dj + 1#32, ()) mdj (by dsimp only; rw [hdj1]; omega)
                    ⟨rfl, by rw [hdj1]; omega⟩
              · c0_hfast; exact hJdj ⟨cand, true, dj⟩ mdj rfl
      · c0_hfast
        exact hJmp ⟨nqlp, ncp, mp, nnoup, arp, lmp, wsp, ws1p, qlp⟩ mlm
          ⟨hncp_le, hwsp_l, hws1p_l, hvivp, hlm4p, hwp, hcntdp, hmlm⟩
  all_goals
    exact hJscan nql ncntd jf ar ws ws1 ws2 mf
      ⟨hnc_le, hws_l, hws1_l, hviv, hw_ar, hcntd_ok, hmf⟩

theorem m4_bva_scan_cands_wp (Γ : Env) :
    ∀ args m Q X, m4BvaScanCandsSpec args m Q X →
      Func.wp Γ FullBvaHeap.full_bva_scan_cands_body args m Q X := by
  rintro ⟨h, row_off, cur_qn, init_lits, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hslen, hw, hnodup, hext, hl0, hdm, hil_le, hlm_clr, hrow_bd, hqn_le,
     hrow_ok, hm, hQ⟩
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena; have hscr_b := c.hscr
  unfold dimacsBound at hmx hwcap har_b hscr_b
  have hcl := hslen.core_ok; have hsc := hslen.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hwv_len := hcl.wvec_len; have hws_len := hcl.wstk_len_arr
  have har_len := hcl.arena_len_arr; have hal_le := hcl.arena_len_le; have hwlen_le := hcl.wlen_le
  have hlm_len := hcl.lit_mark_len; have hvals_len := hcl.vals_len; have hfl_len := hcl.flags_len
  have hsb_len := hsc.scratch_buf_len; have hwsort_len := hsc.wsort_len
  have hws1_len := hsc.work_stk1_len; have hws2_len := hsc.work_stk2_len
  have hset : ∀ x : BitVec 32, (BitVec.setWidth 64 x).toNat = x.toNat := bv64_setWidth_32
  have hdw : DenseWatchesInv F_cur s.core := by
    have h1 := hw.watches; unfold ModeWatchesInv at h1; rwa [ite_eq_right hdm] at h1
  let mkSt (ar : List (BitVec 32)) (lm : List (BitVec 8)) (ws ws1 ws2 : List (BitVec 32)) :
      FullState :=
    { core := { s.core with arena := ar, lit_mark := lm }
      scratch := { s.scratch with wsort := ws, work_stk1 := ws1, work_stk2 := ws2 } }
  c0_hsteps
  refine wp_loop_inv
    (fun (nql, ncntd, qi, ()) ml => ∃ ar ws ws1 ws2,
      qi.toNat ≤ cur_qn.toNat ∧ ncntd.toNat ≤ init_lits.toNat ∧
      ws.length = 2 * c.max_vars ∧ ws1.length = 2 * c.max_vars ∧
      M4ScanArVivInv c s ar ws2 0 nql.toNat ∧
      FullWitnessInv c F0 F_cur { s.core with arena := ar } ∧
      (∀ i < ncntd.toNat, (ws1[i]?.getD 0#32).toNat < init_lits.toNat) ∧
      (FullMem c (mkSt ar s.core.lit_mark ws ws1 ws2) ⋆ R) ml)
    (fun (_, _, qi, _) _ => cur_qn.toNat - qi.toNat)
    (fun Jq hJq => by
      c0_hsteps; exact hJq (0#32, 0#32, 0#32, ()) m
        ⟨s.core.arena, s.scratch.wsort, s.scratch.work_stk1, s.scratch.work_stk2,
         Nat.zero_le _, Nat.zero_le _, hwsort_len, hws1_len, m4ScanArVivInv_init hslen,
         hw, fun _ h => by simp only [bv_c0] at h; omega, hm⟩)
    (fun Jq (nql, ncntd, qi, ()) ml
        ⟨ar, ws, ws1, ws2, hqi_le, hnc_le, hws_l, hws1_l, hviv, hw_ar, hcntd_ok, hml⟩ ihq => ?_)
  dsimp only [mkSt] at hml
  have har_l := hviv.1; have hws2_l := hviv.2.1; have hnql_le := hviv.2.2.1
  c0_hsteps_nogrp
  · have hqi_lt : qi.toNat < cur_qn.toNat := by c0_bound
    have hqi1 : (qi + 1#32).toNat = qi.toNat + 1 := by c0_bound
    have hrqi : (row_off + qi).toNat = row_off.toNat + qi.toNat := by c0_bound
    have hqw_ok := hrow_ok qi.toNat hqi_lt
    let qw := s.scratch.scratch_buf[row_off.toNat + qi.toNat]'(by omega)
    have hrqi_mod : (row_off.toNat + qi.toNat) % 2 ^ 32 = row_off.toNat + qi.toNat :=
      Nat.mod_eq_of_lt (by omega)
    have hqw_mod : s.scratch.scratch_buf[(row_off.toNat + qi.toNat) % 2 ^ 32]'(by
        rw [hrqi_mod]; omega) = qw := by dsimp only [qw]; simp only [hrqi_mod]
    have hqw_getD : s.scratch.scratch_buf[row_off.toNat + qi.toNat]?.getD 0#32 = qw := by
      dsimp only [qw]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    rw [hqw_getD] at hqw_ok
    c0_hstep; c0_hsplit
    · have hbin_ne : (qw &&& 0x80000000#32) ≠ 0#32 := by
        have h1 : (s.scratch.scratch_buf[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
          rw [hset, hrqi]; omega) &&& 0x80000000#32) ≠ 0#32 := by assumption
        simpa only [hset, hrqi] using h1
      rw [ite_eq_left hbin_ne] at hqw_ok
      let q := qw &&& 0x7FFFFFFF#32
      have hq_lt : q.toNat < 2 * s.core.cur_vars := hqw_ok
      have h2q_n : (BitVec.setWidth 64 q <<< (1 : Nat)).toNat = 2 * q.toNat := by c0_bound
      have h2q1_n : ((BitVec.setWidth 64 q <<< (1 : Nat)) + 1).toNat = 2 * q.toNat + 1 := by
        change ((BitVec.setWidth 64 q <<< (1 : Nat)) + 1#64).toNat = _; c0_bound
      have hq_bd := hdw.layout.bounds q.toNat hq_lt
      have hq_sl := hdw.slices q.toNat hq_lt
      have hoff_eq : (s.core.wvec[2 * q.toNat]'(by omega)).toNat =
          fullWatchOffCore s.core q.toNat := by
        unfold fullWatchOffCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have hsz_eq : (s.core.wvec[2 * q.toNat + 1]'(by omega)).toNat =
          fullWatchSizeCore s.core q.toNat := by
        unfold fullWatchSizeCore; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      let qoff0 := fullWatchOffCore s.core q.toNat
      let qsz0 := fullWatchSizeCore s.core q.toNat
      have hq_eq : s.scratch.scratch_buf[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
          rw [hset, hrqi]; omega) &&& 0x7FFFFFFF#32 = q := by
        dsimp only [q, qw]; simp only [hset, hrqi]
      have hq_mod : s.scratch.scratch_buf[(row_off.toNat + qi.toNat) % 2 ^ 32]'(by
          rw [hrqi_mod]; omega) &&& (2147483647 : BitVec 32) = q := by rw [hqw_mod]; rfl
      have h2q_mod : 2 * q.toNat % 2 ^ 64 = 2 * q.toNat := Nat.mod_eq_of_lt (by omega)
      have h2q_wvec : (BitVec.setWidth 64 (s.scratch.scratch_buf[(BitVec.setWidth 64
          (row_off + qi)).toNat]'(by rw [hset, hrqi]; omega) &&& 0x7FFFFFFF#32) <<<
          (1 : Nat)).toNat < s.core.wvec.length := by rw [hq_eq, h2q_n]; omega
      have h2q1_wvec : ((BitVec.setWidth 64 (s.scratch.scratch_buf[(BitVec.setWidth 64
          (row_off + qi)).toNat]'(by rw [hset, hrqi]; omega) &&& 0x7FFFFFFF#32) <<<
          (1 : Nat)) + 1).toNat < s.core.wvec.length := by rw [hq_eq, h2q1_n]; omega
      c0_hsteps_nogrp
      refine wp_loop_inv
        (fun (nc, qp, ()) mlp => ∃ wsp ws1p,
          qoff0 ≤ qp.toNat ∧ qp.toNat ≤ qoff0 + qsz0 ∧ nc.toNat ≤ init_lits.toNat ∧
          wsp.length = 2 * c.max_vars ∧ ws1p.length = 2 * c.max_vars ∧
          DenseWatchSliceOk F_cur s.core q.toNat qp.toNat (qoff0 + qsz0 - qp.toNat) ∧
          (∀ i < nc.toNat, (ws1p[i]?.getD 0#32).toNat < init_lits.toNat) ∧
          (FullMem c (mkSt ar s.core.lit_mark wsp ws1p ws2) ⋆ R) mlp)
        (fun (_, qp, _) _ => qoff0 + qsz0 - qp.toNat)
        (fun Jp hJp => by
          c0_hfast
          have h1 : (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64
              (s.scratch.scratch_buf[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
                rw [hset, hrqi]; omega) &&& (2147483647 : BitVec 32)) <<< (1 : Nat)).toNat]'(by
              rw [show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl, hq_eq, h2q_n]
              omega))).toNat = qoff0 := by
            simp only [show (2147483647 : BitVec 32) = 0x7FFFFFFF#32 from rfl, hq_eq]
            simp only [h2q_n, hset, hoff_eq]; rfl
          dsimp only
          refine hJp (ncntd, _, ()) ml ⟨ws, ws1, by rw [h1]; exact Nat.le_refl _,
            by rw [h1]; omega, hnc_le, hws_l, hws1_l,
            by simpa only [h1, Nat.add_sub_cancel_left] using hq_sl, hcntd_ok, hml⟩)
        (fun Jp (nc, qp, ()) mlp
            ⟨wsp, ws1p, hqp_ge, hqp_le, hncp_le, hwsp_l, hws1p_l, hrem, hcntdp, hmlp⟩ ihp => ?_)
      clear hm hml
      dsimp only [mkSt] at hmlp
      c0_hsplit
      · have hqp_lt : qp.toNat < qoff0 + qsz0 := by
          have hqend_mod : ((s.core.wvec[2 * q.toNat % 2 ^ 64]'(by rw [h2q_mod]; omega)).toNat +
              (s.core.wvec[(2 * q.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega)).toNat) % 2 ^ 64 =
              qoff0 + qsz0 := by
            simp only [h2q_mod, show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
              Nat.mod_eq_of_lt (by omega : 2 * q.toNat + 1 < 2 ^ 64), hoff_eq, hsz_eq]
            exact Nat.mod_eq_of_lt (by omega)
          rw [← hqend_mod]
          simpa only [← hq_mod] using (by assumption : _)
        have hqp_ws : qp.toNat < s.core.wstk.length := by omega
        have hqp1_n : (qp + 1#64).toNat = qp.toNat + 1 := by simp only [bv_c0]; omega
        c0_hsteps_nogrp; c0_hstep; c0_hsplit
        · have ⟨hc_lt2, _, hrem_next⟩ :=
            FullBvaFwdHelpers.bva_slice_bin_info hrem (by omega) hqp_ws (by assumption)
          let cand := s.core.wstk[qp.toNat]'hqp_ws &&& 0x7FFFFFFF#32
          have hcand_lt : cand.toNat < 2 * s.core.cur_vars := hc_lt2
          have hcand_shr : (cand >>> (1 : Nat)).toNat < c.max_vars := by
            rw [bv32_lshr1_nat]; omega
          have hcand_ws : (BitVec.setWidth 64 cand).toNat < wsp.length := by
            rw [hset, hwsp_l]; omega
          c0_hsteps_nogrp
          refine wp_join_state1 (t := i32)
            (α := BitVec 32 × List (BitVec 32) × List (BitVec 32)) (fun st => st.1)
            (fun ⟨nc1, wsp1, ws1p1⟩ mf =>
              nc1.toNat ≤ init_lits.toNat ∧ wsp1.length = 2 * c.max_vars ∧
              ws1p1.length = 2 * c.max_vars ∧
              (∀ i < nc1.toNat, (ws1p1[i]?.getD 0#32).toNat < init_lits.toNat) ∧
              (FullMem c (mkSt ar s.core.lit_mark wsp1 ws1p1 ws2) ⋆ R) mf)
            (fun _ ⟨nc1, wsp1, ws1p1⟩ mf ⟨hnc1, hwsp1, hws1p1, hcntd1, hmf⟩ => by
              c0_hfast
              exact ihp (nc1, qp + 1#64, ()) mf (by dsimp only; rw [hqp1_n]; omega)
                ⟨wsp1, ws1p1, by rw [hqp1_n]; omega, by rw [hqp1_n]; omega, hnc1, hwsp1, hws1p1,
                 by rw [hqp1_n, show qoff0 + qsz0 - (qp.toNat + 1) = qoff0 + qsz0 - qp.toNat - 1
                      by omega]; exact hrem_next, hcntd1, hmf⟩)
            (fun Jc hJc => ?_)
          have hil_u32 : init_lits.toNat < 2 ^ 32 := by
            have := c.hmaxv; unfold dimacsBound at *; omega
          c0_hfast
          all_goals
            first
            | exact hJc ⟨nc, wsp, ws1p⟩ mlp ⟨hncp_le, hwsp_l, hws1p_l, hcntdp, hmlp⟩
            | (dsimp only at hm
               have hm' : (FullMem c (mkSt ar s.core.lit_mark _ _ ws2) ⋆ R) m := hm
               refine hJc ⟨_, _, _⟩ m ⟨?_, ?_, ?_, ?_, hm'⟩
               · first
                 | exact hncp_le
                 | (simp only [show (1 : BitVec 32) = 1#32 from rfl, bv_c0] at *; omega)
               · (try simp only [List.length_set]); exact hwsp_l
               · (try simp only [List.length_set]); exact hws1p_l
               · intro i hi
                 first
                 | exact hcntdp i hi
                 | (have hcand_il : (s.core.wstk[qp.toNat]'hqp_ws &&&
                        (2147483647 : BitVec 32)).toNat < init_lits.toNat := by
                      simp only [bv_c0] at *; omega
                    have hnc1 : (nc + (1 : BitVec 32)).toNat = nc.toNat + 1 := by
                      simp only [show (1 : BitVec 32) = 1#32 from rfl, bv_c0] at *; omega
                    rw [hnc1] at hi
                    by_cases hie : i = nc.toNat
                    · subst hie; rw [hset, List.getElem?_set_self (by omega), Option.getD_some]
                      exact hcand_il
                    · rw [hset, List.getElem?_set_ne (Ne.symm hie)]; exact hcntdp i (by omega)))
        · have ⟨h2le, hrem_next⟩ :=
            FullBvaFwdHelpers.bva_slice_occ_info hrem (by omega) hqp_ws (by assumption)
          have hqp2_n : (qp + 2#64).toNat = qp.toNat + 2 := by simp only [bv_c0]; omega
          c0_hfast
          exact ihp (nc, qp + 2#64, ()) mlp (by dsimp only; rw [hqp2_n]; omega)
            ⟨wsp, ws1p, by rw [hqp2_n]; omega, by rw [hqp2_n]; omega, hncp_le, hwsp_l, hws1p_l,
             by rw [hqp2_n, show qoff0 + qsz0 - (qp.toNat + 2) = qoff0 + qsz0 - qp.toNat - 2
                  by omega]; exact hrem_next, hcntdp, hmlp⟩
      · c0_hfast
        exact ihq (nql, nc, qi + 1#32, ()) mlp (by dsimp only; rw [hqi1]; omega)
          ⟨ar, wsp, ws1p, ws2, by rw [hqi1]; omega, hncp_le, hwsp_l, hws1p_l, hviv, hw_ar,
           hcntdp, hmlp⟩
    · have hbin_eq : (qw &&& 0x80000000#32) = 0#32 := by
        have h1 : (s.scratch.scratch_buf[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
          rw [hset, hrqi]; omega) &&& 0x80000000#32) = 0#32 := by assumption
        simpa only [hset, hrqi] using h1
      rw [ite_eq_right (fun h' => h' hbin_eq)] at hqw_ok
      obtain ⟨hqw_ref, hqw_ng⟩ := hqw_ok
      have hqw_wf := hw.arena.refs_wf qw.toNat hqw_ref
      have hqw_sz_s : (s.core.arena[qw.toNat + 2]'(by omega)).toNat =
          fullArenaClauseSizeCore s.core qw.toNat := by
        unfold fullArenaClauseSizeCore
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have har_lits_eq := m4_scan_cands_ar_lits_eq hcl hw hviv hqw_ref
      have hqw_sz_eq : (ar[qw.toNat + 2]'(by omega)).toNat =
          fullArenaClauseSizeCore s.core qw.toNat := by
        have h1 := har_lits_eq.1
        rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at h1
        rw [Option.some.inj h1]; exact hqw_sz_s
      let csz_bv := ar[qw.toNat + 2]'(by omega)
      have hcsz_nat : csz_bv.toNat = fullArenaClauseSizeCore s.core qw.toNat := hqw_sz_eq
      have hqw_eq : s.scratch.scratch_buf[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
          rw [hset, hrqi]; omega) = qw := by dsimp only [qw]; simp only [hset, hrqi]
      have hqw2_n : (BitVec.setWidth 64 qw + 2).toNat = qw.toNat + 2 := by
        change (BitVec.setWidth 64 qw + 2#64).toNat = _; simp only [bv_c0]; omega
      have hqw2_mod : (qw.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = qw.toNat + 2 := by
        rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl]; omega
      have hcsz_mod : csz_bv = ar[(qw.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
          rw [hqw2_mod]; omega) := by dsimp only [csz_bv]; simp only [hqw2_mod]
      have hqw2_ar : (BitVec.setWidth 64 (s.scratch.scratch_buf[(BitVec.setWidth 64
          (row_off + qi)).toNat]'(by rw [hset, hrqi]; omega)) + 2).toNat < ar.length := by
        rw [hqw_eq, hqw2_n, har_l]; have := hqw_wf.1; omega
      c0_hsteps_nogrp
      refine wp_join_state (α := BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × List (BitVec 8))
        (fun ⟨min_l, min_d, fc, jf, _⟩ => (min_l, min_d, fc, jf, ()))
        (fun ⟨min_l, min_d, _, _, lm1⟩ mf =>
          LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat 0 csz_bv.toNat lm1 ∧
          (min_l ≠ 0xFFFFFFFF#32 →
            min_l.toNat < 2 * s.core.cur_vars ∧
            min_d.toNat = fullWatchSizeCore s.core min_l.toNat) ∧
          (FullMem c (mkSt ar lm1 ws ws1 ws2) ⋆ R) mf)
        (fun _ ⟨min_l, min_d, fc, _jf, lm1⟩ mf ⟨hlm1_inv, hmin_ok, hmf⟩ => ?_)
        (fun Jm hJm => ?_)
      · dsimp only [mkSt] at hmf
        c0_hsteps_nogrp
        refine wp_join_state (α := BitVec 32 × BitVec 32 × BitVec 32 × List (BitVec 32) ×
            List (BitVec 32) × List (BitVec 32) × List (BitVec 32))
          (fun ⟨nql2, nc2, jf2, _, _, _, _⟩ => (nql2, nc2, jf2, ()))
          (fun ⟨nql2, nc2, _, ar2, ws2', ws12, ql2⟩ mf2 =>
            nc2.toNat ≤ init_lits.toNat ∧ ws2'.length = 2 * c.max_vars ∧
            ws12.length = 2 * c.max_vars ∧
            M4ScanArVivInv c s ar2 ql2 0 nql2.toNat ∧
            FullWitnessInv c F0 F_cur { s.core with arena := ar2 } ∧
            (∀ i < nc2.toNat, (ws12[i]?.getD 0#32).toNat < init_lits.toNat) ∧
            (FullMem c (mkSt ar2 lm1 ws2' ws12 ql2) ⋆ R) mf2)
          (fun _ ⟨nql2, nc2, _jf2, ar2, ws2', ws12, ql2⟩ mf2
              ⟨hnc2, hws2'_l, hws12_l, hviv2, hw2, hcntd2, hmf2⟩ => ?_)
          (fun Jscan hJscan => ?_)
        · dsimp only [mkSt] at hmf2
          have har2_l := hviv2.1
          have har2_lits := (m4_scan_cands_ar_lits_eq hcl hw hviv2 hqw_ref).2
          refine wp_loop_inv
            (fun (j, ()) mj => ∃ lmj,
              j.toNat ≤ csz_bv.toNat ∧
              LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat j.toNat csz_bv.toNat lmj ∧
              (FullMem c (mkSt ar2 lmj ws2' ws12 ql2) ⋆ R) mj)
            (fun (j, ()) _ => csz_bv.toNat - j.toNat)
            (fun Jc2 hJc2 => by
              c0_hfast; exact hJc2 (0#32, ()) mf2 ⟨lm1, Nat.zero_le _, hlm1_inv, hmf2⟩)
            (fun Jc2 (j, ()) mj ⟨lmj, hj_le, hlmj_inv, hmj⟩ ihc2 => ?_)
          clear hm hml hmf hmf2
          dsimp only [mkSt] at hmj
          have hlmj_l := hlmj_inv.1
          c0_hsplit
          · have hj_lt : j.toNat < csz_bv.toNat := by
              rw [hcsz_mod]
              simpa only [← hqw_mod] using (by assumption : _)
            have hcj_eq : ar2[qw.toNat + 3 + j.toNat]'(by omega) =
                s.core.arena[qw.toNat + 3 + j.toNat]'(by omega) := by
              have h1 := har2_lits j.toNat (by omega)
              rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at h1
              exact Option.some.inj h1
            have hcj_lt : (s.core.arena[qw.toNat + 3 + j.toNat]'(by omega)).toNat <
                2 * s.core.cur_vars :=
              hw.arena.lits_lt qw.toNat hqw_ref hqw_ng _ (List.mem_of_getElem?
                (FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem (by omega) (by omega)))
            have hj1 : (j + 1#32).toNat = j.toNat + 1 := by simp only [bv_c0]; omega
            have hidx_n : (BitVec.setWidth 64 qw + 3 + BitVec.setWidth 64 j).toNat =
                qw.toNat + 3 + j.toNat := by
              change (BitVec.setWidth 64 qw + 3#64 + BitVec.setWidth 64 j).toNat = _
              simp only [bv_c0]; omega
            have hidx_ar : (BitVec.setWidth 64 (s.scratch.scratch_buf[(BitVec.setWidth 64
                (row_off + qi)).toNat]'(by rw [hset, hrqi]; omega)) + 3 +
                BitVec.setWidth 64 j).toNat < ar2.length := by rw [hqw_eq, hidx_n, har2_l]; omega
            have hcj_lm : (BitVec.setWidth 64 (ar2[(BitVec.setWidth 64
                (s.scratch.scratch_buf[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
                  rw [hset, hrqi]; omega)) + 3 + BitVec.setWidth 64 j).toNat]'hidx_ar)).toNat <
                lmj.length := by simp only [hqw_eq]; simp only [hidx_n, hset, hcj_eq]; omega
            c0_hfast
            simp only [hqw_eq] at hm; simp only [hidx_n, hset] at hm
            try simp only [bv8_trunc_and_fd] at hm
            try simp only [bv8_trunc_and_w] at hm
            have hstep : LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat (j.toNat + 1)
                csz_bv.toNat (lmj.set (ar2[qw.toNat + 3 + j.toNat]'(by omega)).toNat
                  ((lmj[(ar2[qw.toNat + 3 + j.toNat]'(by omega)).toNat]'(by
                    rw [hcj_eq]; omega)) &&& 0xFD#8)) := by
              have h0 := lmBit2Inv_clear_step hlm_len
                (fun l hl => (bv8_bit_zero_of_and_fe (hlm_clr l hl)).1)
                hlmj_inv hj_lt (by omega) (by omega)
              simpa only [← hcj_eq] using h0
            exact ihc2 (j + 1#32, ()) m (by dsimp only; rw [hj1]; omega)
              ⟨_, by rw [hj1]; omega, by rw [hj1]; exact hstep, hm⟩
          · have hj_eq : j.toNat = csz_bv.toNat := by
              rw [hcsz_mod] at hj_le ⊢
              have h1 : ¬ j.toNat < (ar[(qw.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
                rw [hqw2_mod]; omega)).toNat := by
                simpa only [← hqw_mod] using (by assumption : _)
              omega
            rw [hj_eq] at hlmj_inv
            have hlm_rest : lmj = s.core.lit_mark := lmBit2Inv_done hlm_len hlmj_inv
            rw [hlm_rest] at hmj
            c0_hfast
            exact ihq (nql2, nc2, qi + 1#32, ()) mj (by dsimp only; rw [hqi1]; omega)
              ⟨ar2, ws2', ws12, ql2, by rw [hqi1]; omega, hnc2, hws2'_l, hws12_l, hviv2, hw2,
               hcntd2, hmj⟩
        · dsimp only
          have hmp := m4_scan_cands_mp_wp (Γ := Γ) (Q := Q) (X := X) (row_off := row_off)
            (cur_qn := cur_qn) (Jq := Jq) (qi := qi)
            (qw := s.scratch.scratch_buf[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
              rw [hset, hrqi]; omega))
            (J := J)
            (csz := ar[(BitVec.setWidth 64 (s.scratch.scratch_buf[(BitVec.setWidth 64
              (row_off + qi)).toNat]'(by rw [hset, hrqi]; omega)) + 2).toNat]'hqw2_ar)
            (Jm := fun _ _ => True) (fc := fc) (jf := _jf)
            hcl hsc hw hdw hl0 hil_le hnc_le hws_l hws1_l hviv hw_ar hcntd_ok
            hlm1_inv.1 (fun l hl => by
              rw [lmBit2Inv_preserves_bit2 hlm1_inv hl]
              exact (bv8_bit_zero_of_and_fe (hlm_clr l hl)).2)
            hmin_ok hmf
            (fun nql2 nc2 jf2 ar2 ws2' ws12 ql2 mf2 h =>
              hJscan ⟨nql2, nc2, jf2, ar2, ws2', ws12, ql2⟩ mf2 h)
          dsimp only [m4ScanCandsMpExpr, eLet64, eLet32, eLetBool, eLoad64, eLoad32, eThen, eElse,
            eGrp0_3, eGrp0_4, eGrpBody_2, eGrpBody_3, FullBvaHeap.full_bva_scan_cands_body] at hmp
          exact hmp
      · refine wp_loop_inv
          (fun (min_l, min_d, fc, j, ()) mj => ∃ lmj,
            j.toNat ≤ csz_bv.toNat ∧
            LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat 0 j.toNat lmj ∧
            (min_l ≠ 0xFFFFFFFF#32 →
              min_l.toNat < 2 * s.core.cur_vars ∧
              min_d.toNat = fullWatchSizeCore s.core min_l.toNat) ∧
            (FullMem c (mkSt ar lmj ws ws1 ws2) ⋆ R) mj)
          (fun (_, _, _, j, _) _ => csz_bv.toNat - j.toNat)
          (fun JmL hJmL => by
            c0_hfast; exact hJmL (0xFFFFFFFF#32, 0xFFFFFFFF#32, 0#32, 0#32, ()) ml
              ⟨s.core.lit_mark, Nat.zero_le _, lmBit2Inv_init hlm_len,
               fun h => absurd rfl h, hml⟩)
          (fun JmL (min_l, min_d, fc, j, ()) mj ⟨lmj, hj_le, hlmj_inv, hmin_ok, hmj⟩ ihm => ?_)
        clear hm hml
        dsimp only [mkSt] at hmj
        have hlmj_l := hlmj_inv.1
        c0_hsplit
        · have hj_lt : j.toNat < csz_bv.toNat := by
            rw [hcsz_mod]
            simpa only [← hqw_mod] using (by assumption : _)
          have hj1 : (j + 1#32).toNat = j.toNat + 1 := by simp only [bv_c0]; omega
          have hqwj_n : (BitVec.setWidth 64 qw + 3 + BitVec.setWidth 64 j).toNat =
              qw.toNat + 3 + j.toNat := by
            change (BitVec.setWidth 64 qw + 3#64 + BitVec.setWidth 64 j).toNat = _
            simp only [bv_c0]; omega
          have hl_eq : ar[qw.toNat + 3 + j.toNat]'(by omega) =
              s.core.arena[qw.toNat + 3 + j.toNat]'(by omega) := by
            have h1 := har_lits_eq.2 j.toNat (by omega)
            rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at h1
            exact Option.some.inj h1
          have hl_lt : (ar[qw.toNat + 3 + j.toNat]'(by omega)).toNat < 2 * s.core.cur_vars := by
            rw [hl_eq]
            exact hw.arena.lits_lt qw.toNat hqw_ref hqw_ng _ (List.mem_of_getElem?
              (FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem (by omega) (by omega)))
          have h2l1_n : ((BitVec.setWidth 64 (ar[qw.toNat + 3 + j.toNat]'(by omega)) <<<
              (1 : Nat)) + 1).toNat =
              2 * (ar[qw.toNat + 3 + j.toNat]'(by omega)).toNat + 1 := by
            change ((BitVec.setWidth 64 _ <<< (1 : Nat)) + 1#64).toNat = _
            simp only [bv_c0]; omega
          have hqwj_ar : (BitVec.setWidth 64 (s.scratch.scratch_buf[(BitVec.setWidth 64
              (row_off + qi)).toNat]'(by rw [hset, hrqi]; omega)) + 3 +
              BitVec.setWidth 64 j).toNat < ar.length := by rw [hqw_eq, hqwj_n, har_l]; omega
          have hl_lm : (BitVec.setWidth 64 (ar[(BitVec.setWidth 64
              (s.scratch.scratch_buf[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
                rw [hset, hrqi]; omega)) + 3 + BitVec.setWidth 64 j).toNat]'hqwj_ar)).toNat <
              lmj.length := by simp only [hqw_eq]; simp only [hqwj_n, hset]; omega
          have h2l1_wv : ((BitVec.setWidth 64 (ar[(BitVec.setWidth 64
              (s.scratch.scratch_buf[(BitVec.setWidth 64 (row_off + qi)).toNat]'(by
                rw [hset, hrqi]; omega)) + 3 + BitVec.setWidth 64 j).toNat]'hqwj_ar) <<<
              (1 : Nat)) + 1).toNat < s.core.wvec.length := by
            simp only [hqw_eq]; simp only [hqwj_n, h2l1_n]; omega
          have hlmj_lift := m4_scan_cands_lmj_lift hlmj_inv hj_le
          have hl_lt_s : (s.core.arena[qw.toNat + 3 + j.toNat]'(by omega)).toNat <
              2 * c.max_vars := by rw [← hl_eq]; omega
          have hstep2_base : LmBit2Inv c s.core.arena s.core.lit_mark qw.toNat 0 (j.toNat + 1)
              (lmj.set (ar[qw.toNat + 3 + j.toNat]'(by omega)).toNat
                ((lmj[(ar[qw.toNat + 3 + j.toNat]'(by omega)).toNat]'(by omega)) ||| 2#8)) := by
            have h0 := lmBit2Inv_or2 hlm_len hlmj_inv (by omega) hl_lt_s
            simpa only [← hl_eq] using h0
          c0_hfast
          · exact hJm ⟨min_l, min_d, fc + 1#32, j, lmj⟩ mj ⟨hlmj_lift, hmin_ok, hmj⟩
          · exact ihm (min_l, min_d, fc + 1#32, j + 1#32, ()) mj (by dsimp only; rw [hj1]; omega)
              ⟨lmj, by rw [hj1]; omega, by rw [hj1]; exact lmBit2Inv_skip hlmj_inv, hmin_ok, hmj⟩
          · refine ihm (_, _, fc, j + 1#32, ()) m (by dsimp only; rw [hj1]; omega)
              ⟨_, by rw [hj1]; omega, by rw [hj1]; exact hstep2_base, fun _ => ?_, ?_⟩
            · simp only [hqw_eq]; simp only [hqwj_n, h2l1_n]
              refine ⟨hl_lt, ?_⟩
              unfold fullWatchSizeCore
              rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
            · simp only [hqw_eq] at hm; simp only [hqwj_n, hset] at hm
              try simp only [bv8_trunc_or_2] at hm
              try simp only [bv8_trunc_or_w] at hm
              exact hm
          · refine ihm (_, _, fc, j + 1#32, ()) m (by dsimp only; rw [hj1]; omega)
              ⟨_, by rw [hj1]; omega, by rw [hj1]; exact hstep2_base, fun _ => ?_, ?_⟩
            · simp only [hqw_eq]; simp only [hqwj_n, h2l1_n]
              refine ⟨hl_lt, ?_⟩
              unfold fullWatchSizeCore
              rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
            · simp only [hqw_eq] at hm; simp only [hqwj_n, hset] at hm
              try simp only [bv8_trunc_or_2] at hm
              try simp only [bv8_trunc_or_w] at hm
              exact hm
          · refine ihm (min_l, min_d, fc, j + 1#32, ()) m (by dsimp only; rw [hj1]; omega)
              ⟨_, by rw [hj1]; omega, by rw [hj1]; exact hstep2_base, hmin_ok, ?_⟩
            simp only [hqw_eq] at hm; simp only [hqwj_n, hset] at hm
            try simp only [bv8_trunc_or_2] at hm
            try simp only [bv8_trunc_or_w] at hm
            exact hm
        · have hj_eq : j.toNat = csz_bv.toNat := by
            rw [hcsz_mod] at hj_le ⊢
            have h1 : ¬ j.toNat < (ar[(qw.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
              rw [hqw2_mod]; omega)).toNat := by
              simpa only [← hqw_mod] using (by assumption : _)
            omega
          rw [hj_eq] at hlmj_inv
          c0_hfast
          exact hJm ⟨min_l, min_d, fc, j, lmj⟩ mj ⟨hlmj_inv, hmin_ok, hmj⟩
  · clear hm
    refine wp_loop_inv
      (fun (ci, ()) mci => ∃ arci,
        ci.toNat ≤ nql.toNat ∧ M4ScanArVivInv c s arci ws2 ci.toNat nql.toNat ∧
        (FullMem c (mkSt arci s.core.lit_mark ws ws1 ws2) ⋆ R) mci)
      (fun (ci, ()) _ => nql.toNat - ci.toNat)
      (fun Jc hJc => by c0_hfast; exact hJc (0#32, ()) ml ⟨ar, Nat.zero_le _, hviv, hml⟩)
      (fun Jc (ci, ()) mci ⟨arci, hci_le, hviv_ci, hmci⟩ ihc => ?_)
    clear hml
    dsimp only [mkSt] at hmci
    have harci_l := hviv_ci.1
    c0_hsplit
    · have hci_lt : ci.toNat < nql.toNat := by assumption
      have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := by simp only [bv_c0]; omega
      have hidx_ref := (hviv_ci.2.2.2.1 ci.toNat (Nat.le_refl _) hci_lt).1
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hidx_ref
      have hidx_wf := hw.arena.refs_wf _ hidx_ref
      have hstep := m4ScanArVivInv_clear_step har_len hviv_ci hci_lt (by omega)
      have hci_ws2 : (BitVec.setWidth 64 ci).toNat < ws2.length := by rw [hset, hws2_l]; omega
      have hidx_ar : (BitVec.setWidth 64 (ws2[(BitVec.setWidth 64 ci).toNat]'hci_ws2)).toNat <
          arci.length := by
        simp only [hset]; have := hidx_wf.1; have := hcl.arena_len_le; omega
      c0_hfast
      refine ihc (ci + 1#32, ()) m (by dsimp only; rw [hci1]; omega)
        ⟨_, by rw [hci1]; omega, by rw [hci1]; exact hstep, ?_⟩
      simp only [hset] at hm; exact hm
    · have hci_eq : ci.toNat = nql.toNat := by omega
      rw [hci_eq] at hviv_ci
      have har_rest : arci = s.core.arena := m4ScanArVivInv_done har_len hviv_ci
      rw [har_rest] at hmci
      c0_hfast
      exact hQ ncntd ws ws1 ws2 mci
        ⟨hcl, { hsc with wsort_len := hws_l, work_stk1_len := hws1_l, work_stk2_len := hws2_l }⟩
        hnc_le hcntd_ok hmci

end LeanQbe.T.Examples.Kissat.FullM4Bva
