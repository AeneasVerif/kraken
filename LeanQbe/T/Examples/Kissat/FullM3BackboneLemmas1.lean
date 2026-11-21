module

public import LeanQbe.T.Examples.Kissat.FullM3Backbone
public import LeanQbe.T.Examples.Kissat.FullTransLemmas
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` M3c Backbone & Wrap-Around `probe_run` `Func.wp` Proofs (`Part 1`, UNSAT-Only)

Proves axiom-clean, UNSAT-only `Func.wp` soundness for the three core M3c algorithms in
`FullM3Backbone.lean`:
1. **`full_probe_run(h, budget)`** (`m3_probe_run_cursor_wp`, `m3_probe_run_wp`,
   `m3_probe_run_fast_wp`): persistent wrap-around variable cursor in `h->iterating`, proving
   canonical `Full.fullProbeRunSpec`, `FullFastBveBudgets.fullProbeRunFastSpec`, and the
   cursor-bound invariant `s'.scratch.iterating.toNat < s'.core.cur_vars` on `r = 1#64` when active.
2. **`full_backbone_lit(h, cand)`** (`m3_backbone_lit_entails_wp`, `m3_backbone_lit_wp`):
   Kissat 4.0 `backbone.c` BIG BFS over binary watches with clean trail unwind and explicit
   semantic unit-entailment certification
   `r = 1#64 → cand.toNat < 2 * s.core.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause [cand]`
   and `r = 20#64 → F0.Unsat`.
3. **`full_backbone(h, tick_lim)`** (`m3_backbone_wp`): multi-round `FL_BONE0`/`FL_BONE1`
   candidate sweep, unit propagation cascade, `h->delayed_len` telemetry, and full-sweep re-arming.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM3Backbone

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. M3c Specifications (`fullProbeRunCursorSpec`, `fullBackbone*Spec`) -/

section Specs

/-- Strengthened `full_probe_run(h, budget)` spec certifying canonical UNSAT soundness, level-0
exit (`cur_level = 0`, `probing = 0`), and persistent wrap-around cursor safety
`s'.scratch.iterating.toNat < s'.core.cur_vars` whenever the sweep executes and returns `1#64`. -/
def fullProbeRunCursorSpec : Spec [i64, i64] [i64] := fun (h, budget, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInv c F0 s' → s'.core.cur_level = 0 → s'.core.probing = 0#64 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → 0 < s'.core.cur_vars → budget ≠ 0#64 → s.core.num_binary ≠ 0#64 →
        s'.scratch.iterating.toNat < s'.core.cur_vars) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Explicit-formula contract for `full_backbone_lit(h, cand)`: certifies that every discovered
backbone unit (`r = 1#64`) is semantically entailed by `cnfOfClauses F_cur` and that `r = 20#64`
certifies `F0.Unsat`. -/
def fullBackboneLitEntailsSpec : Spec [i64, i32] [i64] := fun (h, cand, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ s.core.cur_level = 0 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInvW c F0 F_cur s' → s'.core.cur_level = 0 →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      (r = 1#64 → cand.toNat < 2 * s.core.cur_vars ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause [cand.toNat])) →
      (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Canonical `FullSparseInv` contract for `full_backbone_lit(h, cand)`. -/
def fullBackboneLitSpec : Spec [i64, i32] [i64] := fun (h, _cand, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ s.core.cur_level = 0 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInv c F0 s' → s'.core.cur_level = 0 →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- Canonical `FullSparseInv` contract for `full_backbone(h, tick_lim)`. -/
def fullBackboneSpec : Spec [i64, i64] [i64] := fun (h, _tick_lim, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInv c F0 s' → s'.core.cur_level = 0 → s'.core.probing = 0#64 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

theorem fullProbeRunCursorSpec_of_canon {a m Q X} (h : Full.fullProbeRunSpec a m Q X) :
    fullProbeRunCursorSpec a m Q X := by
  rcases a with ⟨h_arg, budget, ⟨⟩⟩
  rcases h with ⟨c, F0, s, R, rfl, hsp, hm, hQ⟩
  exact ⟨c, F0, s, R, rfl, hsp, hm,
    fun r s' m' hsp' hcl' hpr' hfu' hr huns _ hm' => hQ r s' m' hsp' hcl' hpr' hfu' hr huns hm'⟩

theorem fullProbeRunCursorSpec_of_fast {a m Q X}
    (h : FullFastBveBudgets.fullProbeRunFastSpec a m Q X) :
    fullProbeRunCursorSpec a m Q X := by
  rcases a with ⟨h_arg, budget, ⟨⟩⟩
  rcases h with ⟨c, F0, s, R, rfl, hsp, hm, hQ⟩
  exact ⟨c, F0, s, R, rfl, hsp, hm,
    fun r s' m' hsp' hcl' hpr' hfu' hr huns _ hm' =>
      hQ r s' m' hsp' (fun _ => hcl') (fun _ => hpr') (fun _ _ => ⟨hcl', hpr'⟩)
        hfu' hr huns hm'⟩

end Specs

/-! ## 2. `m3_probe_run_cursor_wp` (Persistent Wrap-Around Cursor in `h->iterating`) -/

section ProbeRunProof

open FullProbeTransHelpers
open scoped FullArenaTactics FullProbeTransTactics

private theorem m3pr_otfs_to_canon {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullProbeTransSpecs.FullOtfsWitnessInv c F0 F_cur k) :
    FullOtfsWitnessInv c F0 F_cur k :=
  ⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
    h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le, h.dec_earliest,
    h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt,
    h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt, h.reason_inv_below,
    h.reason_lit_mem_below⟩

private theorem m3pr_canon_to_otfs {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (h : FullOtfsWitnessInv c F0 F_cur k) :
    FullProbeTransSpecs.FullOtfsWitnessInv c F0 F_cur k :=
  ⟨h.ext_sound, h.inconsistent_sound, h.arena, h.watches, h.cur_level_le, h.trail_lits_lt,
    h.trail_vars_nodup, h.vals_domain, h.vals_true_iff, h.vals_false_iff, h.lvl_le, h.dec_earliest,
    h.levels_inhabited, h.level0_sound, h.trail_pos_inv, h.level0_rsn_none, h.frame_trail_lt,
    h.frame_trail_mono, h.frame_trail_before_lt, h.frame_dec_lt, h.reason_inv_below,
    h.reason_lit_mem_below⟩

private theorem m3pr_backtrack_adapter {Γ : Env}
    (hBt : ∀ a m Q X, Full.fullBacktrackSpec a m Q X → Γ "full_backtrack" [i64, i64] [] a m Q X) :
    ∀ a m Q X, FullProbeTransSpecs.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X := by
  rintro ⟨h, tgt, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcl64, htgt, htrl, hm, hQ⟩
  refine hBt _ m Q X ⟨c, s, R, rfl, hlen, hcl64, htgt, htrl, hm,
    fun vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
      hlen' hte hpr hcl' hps hsc htrl' hvl hw_w hw_o hm' => ?_⟩
  have hshrk : sc'.shrink_stk = s.scratch.shrink_stk := by
    rcases hsc with ⟨_, _, _, _, _, _, _, _, _, rfl⟩; rfl
  exact hQ vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
    hlen' hte hpr hcl' hps hshrk htrl'
    (fun ⟨F0, Fc, hwo⟩ => hvl ⟨F0, Fc, hwo.elim Or.inl (Or.inr ∘ m3pr_otfs_to_canon)⟩)
    hw_w (fun F0 Fc ho hlt => hw_o F0 Fc (m3pr_otfs_to_canon ho) hlt) hm'

private theorem m3pr_assumePair_adapter {Γ : Env}
    (hAp : ∀ a m Q X, Full.fullProbeAssumePairSpec a m Q X →
      Γ "full_probe_assume_pair" [i64, i32] [i64] a m Q X) :
    ∀ a m Q X, FullProbeTransSpecs.fullProbeAssumePairSpec a m Q X →
      Γ "full_probe_assume_pair" [i64, i32] [i64] a m Q X := by
  rintro ⟨h, lit, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hcl0, hlt, hun, hm, hQ⟩
  refine hAp _ m Q X ⟨c, F0, s, R, rfl, hsp, hcl0, hlt, hun, hm,
    fun r s' m' h12 h20 hcv hfu hr hm' => ?_⟩
  exact hQ r s' m' h12
    (fun h => let ⟨hu, Fc, ho⟩ := h20 h; ⟨hu, Fc, ⟨ho.1, m3pr_canon_to_otfs ho.2.1, ho.2.2⟩⟩)
    hcv hfu hr hm'

private theorem m3pr_set_probing {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (p : BitVec 64) (hsp : FullSparseInv c F0 s) :
    FullSparseInv c F0 { s with core := { s.core with probing := p } } :=
  FullTransHelpers.fullSparseInv_with_probing hsp p

private theorem m3pr_set_iterating_otfs {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (it : BitVec 64) (hot : FullProbeTransSpecs.FullOtfsInvW c F0 F_cur s) :
    FullProbeTransSpecs.FullOtfsInvW c F0 F_cur
      { s with scratch := { s.scratch with iterating := it } } :=
  ⟨⟨hot.1.core_ok, { hot.1.scratch_ok with }⟩, hot.2.1, hot.2.2⟩

private abbrev m3prBtState (s : FullState) (vals' : List (BitVec 8))
    (lvl' rsns' trl' tp' : List (BitVec 32)) (te' prop' cl' : Nat) (unass' : BitVec 64)
    (sc' : FullScratch) : FullState :=
  { s with
    core := { s.core with
      vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
      trail_end := te', propagated := prop', cur_level := cl', unassigned := unass' }
    scratch := sc' }

private theorem m3prBtState_sparse {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {vals' : List (BitVec 8)} {lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' cl' : Nat} {unass' : BitVec 64} {sc' : FullScratch}
    (hlen' : (m3prBtState s vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc').LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur
      (m3prBtState s vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc').core)
    (hlm : FullLitMarksClear c s) (hnd : FullArenaVarsNodup s) (hext : FullExtScratchOk c s)
    (hdm : s.core.dense_mode = 0#64) (hpres : FullExtScratchPres s { s with scratch := sc' }) :
    FullSparseInv c F0 (m3prBtState s vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc') :=
  ⟨⟨hlen', F_cur, hw'⟩, ⟨hlm.1, hlm.2⟩, hnd,
    ⟨fun i hi => by
      change (sc'.last_learned[i]?.getD 0xFFFFFFFF#32) = 0xFFFFFFFF#32 ∨ _
      rw [hpres.1]; exact hext.1 i hi,
     by change sc'.extend_len ≤ c.extend_cap; rw [hpres.2]; exact hext.2⟩, hdm⟩

private theorem m3pr_bv8_sext32_eq0 {x : BitVec 8} (h : x.signExtend 32 = 0#32) : x = 0#8 := by
  revert x h; decide

private theorem m3pr_vals_eq_0_of_sext {vals : List (BitVec 8)} {i : Nat} (hi : i < vals.length)
    (heq : (vals[i]'hi).signExtend 32 = 0#32) : vals[i]?.getD 0#8 = 0#8 := by
  rw [List.getElem?_eq_getElem hi, Option.getD_some, m3pr_bv8_sext32_eq0 heq]

/-- `Func.wp` proof for wrap-around `full_probe_run(h, budget)` against
`fullProbeRunCursorSpec`. -/
theorem m3_probe_run_cursor_wp (Γ : Env)
    (hBacktrack : ∀ args m Q X, Full.fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X)
    (hAssumePair : ∀ args m Q X, Full.fullProbeAssumePairSpec args m Q X →
      Γ "full_probe_assume_pair" [i64, i32] [i64] args m Q X) :
    ∀ args m Q X, fullProbeRunCursorSpec args m Q X →
      Func.wp Γ full_probe_run_body args m Q X := by
  let hBt := m3pr_backtrack_adapter hBacktrack
  let hAp := m3pr_assumePair_adapter hAssumePair
  rintro ⟨h_arg, budget, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp0, hm0, hQ⟩
  obtain ⟨⟨hlen0, F_cur0, hw0⟩, hlm0, hnd0, hext0, hdm0⟩ := hsp0
  have hcl0_ok := hlen0.core_ok; have hmv := c.hmaxv; unfold dimacsBound at hmv
  have hcv_le := hcl0_ok.cur_vars_le
  have hcl_64 : s.core.cur_level < 2 ^ 64 := by
    have := hw0.cur_level_le; have := hcl0_ok.trail_end_le; omega
  have hpos_mv_if : 0 < s.core.cur_level → 0 < c.max_vars := fun _ => by
    have := hw0.cur_level_le; have := hcl0_ok.trail_end_le; omega
  have hsp0' : FullSparseInv c F0 s := ⟨⟨hlen0, F_cur0, hw0⟩, hlm0, hnd0, hext0, hdm0⟩
  unfold Func.wp full_probe_run_body
  pt_steps_nogrp
  -- Join after initial `if (h->cur_level != 0ULL) full_backtrack(h, 0ULL)`
  let entryInv : Tup Val [] → Mem 64 → Prop := fun () mj =>
    ∃ st0 : FullState, FullSparseInv c F0 st0 ∧ st0.core.cur_level = 0 ∧
      st0.core.cur_vars = s.core.cur_vars ∧ st0.core.num_binary = s.core.num_binary ∧
      st0.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c st0 ⋆ R) mj
  refine wp_join_group entryInv (fun _ () mj ⟨st0, hsp_e, hcl_e, hcv_e, hnb_e, hfu_e, hm_e⟩ => ?_)
    (fun Jentry hJentry => ?_)
  · have hcv_e64 : st0.core.cur_vars < 2 ^ 64 := by have := hsp_e.1.1.core_ok.cur_vars_le; omega
    pt_steps_nogrp
    -- Join for shared early-return body `{ h->probing = 0ULL; return 1ULL; }`
    let earlyInv : Tup Val [] → Mem 64 → Prop := fun () me =>
      me = mj ∧ (budget = 0#64 ∨ s.core.num_binary = 0#64 ∨ st0.core.cur_vars = 0)
    refine wp_join_group earlyInv (fun _ () me ⟨hme, hcond⟩ => ?_) (fun Jearly hJearly => ?_)
    · subst hme
      pt_steps_nogrp
      exact hQ 1#64 { st0 with core := { st0.core with probing := 0#64 } } m
        (m3pr_set_probing 0#64 hsp_e) hcl_e rfl hfu_e (Or.inl rfl) (fun h => by cases h)
        (fun _ hpos hb hnb => by
          rcases hcond with h1 | h2 | h3
          · exact absurd h1 hb
          · exact absurd h2 hnb
          · change 0 < st0.core.cur_vars at hpos; omega)
        (by simpa only [show (0 : BitVec 64) = 0#64 from rfl] using hm)
    · pt_steps_nogrp
      · exact hJearly () mj ⟨rfl, Or.inl hc⟩
      · exact hJearly () mj ⟨rfl, Or.inr (Or.inl (hnb_e ▸ hc))⟩
      · have hcv0 : st0.core.cur_vars = 0 := by
          pt_clear_big; have h := congrArg BitVec.toNat hc
          rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv_e64] at h
        exact hJearly () mj ⟨rfl, Or.inr (Or.inr hcv0)⟩
      · have hcv_pos : 0 < st0.core.cur_vars := by
          pt_clear_big; exact Nat.pos_of_ne_zero fun h0 => hc (by simp [h0])
        let st1 : FullState := { st0 with core := { st0.core with probing := 1#64 } }
        have hsp1 := m3pr_set_probing 1#64 hsp_e
        have hm1 : (FullMem c st1 ⋆ R) m := by
          simpa only [st1, show (1 : BitVec 64) = 1#64 from rfl] using hm
        -- Join after cursor clamp `if (v >= cv) v = 0;`
        let curInitInv : Tup Val [i64] → Mem 64 → Prop := fun (v0, ()) m0 =>
          v0.toNat < st1.core.cur_vars ∧ m0 = m
        refine wp_join_group curInitInv (fun _ (v0, ()) m0 ⟨hv0_lt, hm0_eq⟩ => ?_)
          (fun Jcur hJcur => ?_)
        · cases hm0_eq
          let exitInv : Tup Val [i64, i64, i64, i64] → Mem 64 → Prop :=
            fun (v_x, _sc, _d, res_v, ()) mx =>
              v_x.toNat < st1.core.cur_vars ∧
              ∃ st_x : FullState, st_x.LengthsOk c ∧ st_x.core.cur_vars = st1.core.cur_vars ∧
                (res_v = 1#64 → FullSparseInv c F0 st_x ∧ st_x.core.cur_level = 0) ∧
                (res_v = 20#64 →
                  F0.Unsat ∧ ∃ F_x, FullProbeTransSpecs.FullOtfsInvW c F0 F_x st_x) ∧
                (res_v = 1#64 ∨ res_v = 20#64) ∧ st_x.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                (FullMem c st_x ⋆ R) mx
          refine wp_join_group exitInv (fun _ (v_x, _sc, _d, res_v, ()) mx
              ⟨hvx_lt, st_x, hlen_x, hcv_x, h1, h20, hdom, hfu_x, hm_x⟩ => ?_)
            (fun Jexit hJexit => ?_)
          · pt_steps_nogrp
            let st_xi : FullState :=
              { st_x with scratch := { st_x.scratch with iterating := v_x } }
            have hlen_xi : st_xi.LengthsOk c := ⟨hlen_x.core_ok, { hlen_x.scratch_ok with }⟩
            have h1i : res_v = 1#64 → FullSparseInv c F0 st_xi ∧ st_xi.core.cur_level = 0 := by
              intro hr1; obtain ⟨hsp_x, hcl_x⟩ := h1 hr1
              exact ⟨hsp_x.of_safetySlice hlen_xi rfl ⟨rfl, rfl⟩, hcl_x⟩
            have h20i : res_v = 20#64 →
                F0.Unsat ∧ ∃ F_x, FullProbeTransSpecs.FullOtfsInvW c F0 F_x st_xi := by
              intro hr20; obtain ⟨huns, F_x, hot⟩ := h20 hr20
              exact ⟨huns, F_x, m3pr_set_iterating_otfs v_x hot⟩
            let retInv : Tup Val [] → Mem 64 → Prop := fun () mr => ∃ st_r : FullState,
              FullSparseInv c F0 st_r ∧ st_r.core.cur_level = 0 ∧
              st_r.core.cur_vars = st1.core.cur_vars ∧
              (res_v = 1#64 → st_r.scratch.iterating = v_x) ∧
              st_r.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (res_v = 20#64 → F0.Unsat) ∧
              (FullMem c st_r ⋆ R) mr
            refine wp_join_group retInv
              (fun _ () mr ⟨st_r, hsp_r, hcl_r, hcv_r, hit_r, hfu_r, huns, hm_r⟩ => ?_)
              (fun Jret hJret => ?_)
            · pt_steps_nogrp
              exact hQ res_v { st_r with core := { st_r.core with probing := 0#64 } } m
                (m3pr_set_probing 0#64 hsp_r) hcl_r rfl hfu_r hdom huns
                (fun hr1 _ _ _ => by change st_r.scratch.iterating.toNat < st_r.core.cur_vars
                                     rw [hit_r hr1, hcv_r]; exact hvx_lt)
                (by simpa only [show (0 : BitVec 64) = 0#64 from rfl] using hm)
            · have hcl_x64 : st_xi.core.cur_level < 2 ^ 64 := by
                have := hlen_xi.core_ok.trail_end_le; have := hlen_xi.core_ok.cur_vars_le
                rcases hdom with rfl | rfl; · rw [(h1i rfl).2]; decide
                · obtain ⟨_, F_x, hot⟩ := h20i rfl; have := hot.2.1.cur_level_le; omega
              pt_steps_nogrp
              · have hpos_cl : 0 < st_xi.core.cur_level := by
                  pt_clear_big; have : (0 : Nat) < st_xi.core.cur_level % 2 ^ 64 := hc; omega
                have hreq20 : res_v = 20#64 := by
                  rcases hdom with rfl | rfl; exact absurd (h1i rfl).2 (by omega); rfl
                obtain ⟨huns, F_x, hot⟩ := h20i hreq20
                have hpos_mv_x : 0 < c.max_vars := by
                  have := hot.2.1.cur_level_le; have := hlen_xi.core_ok.trail_end_le
                  have := hlen_xi.core_ok.cur_vars_le; omega
                c0_call hBt
                refine ⟨c, st_xi, R, rfl, hlen_xi, hcl_x64, fun _ => hpos_mv_x,
                  hot.2.1.trail_lits_lt, hm, ?_⟩; dsimp only
                intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt hlen_bt _ _ hcl_bt
                  hpres _ _ _ _ hbt_o hm_bt
                let st_bt := m3prBtState st_xi vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc'
                have hsp_bt := m3prBtState_sparse hlen_bt (hbt_o F0 F_x hot.2.1 hpos_cl)
                  hot.2.2.1 hot.2.2.2.1 hot.2.2.2.2.1 hot.2.2.2.2.2 hpres.1
                exact hJret () m_bt ⟨st_bt, hsp_bt, by simp [st_bt, hcl_bt], hcv_x,
                  fun hr1 => absurd (hr1.symm.trans hreq20) (by decide), hfu_x, fun _ => huns,
                  hm_bt⟩
              · have hcl_z : st_xi.core.cur_level = 0 := by
                  pt_clear_big; rw [Nat.mod_eq_of_lt hcl_x64] at hc; omega
                rcases hdom with rfl | rfl
                · exact hJret () m ⟨st_xi, (h1i rfl).1, hcl_z, hcv_x, fun _ => rfl, hfu_x,
                    fun h => absurd h (by decide), hm⟩
                · obtain ⟨huns, F_x, hot⟩ := h20i rfl
                  have hsw := hot.toSparse_of_level0 hcl_z
                  exact hJret () m ⟨st_xi, ⟨⟨hsw.1, F_x, hsw.2.1⟩, hsw.2.2⟩,
                    hcl_z, hcv_x, fun _ => rfl, hfu_x, fun _ => huns, hm⟩
          · -- Main wrap-around loop `(v, scanned, done)`
            let loopInv : Tup Val [i64, i64, i64] → Mem 64 → Prop :=
              fun (v_v, sc_v, _done_v, ()) ml =>
                sc_v.toNat ≤ st1.core.cur_vars ∧ v_v.toNat < st1.core.cur_vars ∧
                ∃ st : FullState, FullSparseInv c F0 st ∧
                  st.core.cur_level = 0 ∧ st.core.cur_vars = st1.core.cur_vars ∧
                  st.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c st ⋆ R) ml
            let meas : Tup Val [i64, i64, i64] → Mem 64 → Nat :=
              fun (_, sc_v, _, ()) _ => st1.core.cur_vars - sc_v.toNat
            refine wp_loop_inv loopInv meas (fun Jloop hJloop => ?_)
              (fun Jloop (v_v, sc_v, done_v, ()) ml
                ⟨hsc_le, hv_lt_cv, st, hsp, hcl_st, hcv_st, hfu_st, hm_st⟩ hJloop => ?_)
            · pt_steps_nogrp
              exact hJloop (v0, 0#64, 0#64, ()) m
                ⟨Nat.zero_le _, hv0_lt, st1, hsp1, hcl_e, rfl, hfu_e, hm1⟩
            · have hcl_sok := hsp.1.1.core_ok; have hcv_st_le := hcl_sok.cur_vars_le
              have hdone_exit : exitInv (v_v, sc_v, done_v, 1#64, ()) ml :=
                ⟨hv_lt_cv, st, hsp.1.1, hcv_st, fun _ => ⟨hsp, hcl_st⟩,
                 fun h => absurd h (by decide), Or.inl rfl, hfu_st, hm_st⟩
              pt_steps_nogrp
              · have hsc_lt : sc_v.toNat < st.core.cur_vars := by
                  pt_clear_big; rw [Nat.mod_eq_of_lt hcv_e64] at *
                  change sc_v.toNat < st1.core.cur_vars at *; omega
                have hv_lt : v_v.toNat < st.core.cur_vars := by rw [hcv_st]; exact hv_lt_cv
                have hv_fl : v_v.toNat < st.core.flags.length := by rw [hcl_sok.flags_len]; omega
                have hv_shl : (v_v <<< (1#32 : BitVec 32).signExtend 64).toNat = 2 * v_v.toNat := by
                  change (v_v <<< (1 : Nat)).toNat = 2 * v_v.toNat
                  exact FullProbeTransHelpers.bv64_shl1_toNat (by omega)
                have hv_val : (v_v <<< (1#32 : BitVec 32).signExtend 64).toNat <
                    st.core.vals.length := by rw [hv_shl, hcl_sok.vals_len]; omega
                have hv1_eq :=
                  FullProbeTransHelpers.bv64_add1_toNat (by omega : v_v.toNat + 1 < 2 ^ 64)
                have hsc1_eq :=
                  FullProbeTransHelpers.bv64_add1_toNat (by omega : sc_v.toNat + 1 < 2 ^ 64)
                let nextInv : Tup Val [i64, i64] → Mem 64 → Prop := fun (done_n, _, ()) mn =>
                  ∃ st_n : FullState, FullSparseInv c F0 st_n ∧ st_n.core.cur_level = 0 ∧
                    st_n.core.cur_vars = st1.core.cur_vars ∧
                    st_n.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c st_n ⋆ R) mn
                refine wp_join_group nextInv (fun _ (done_n, _r, ()) mn
                    ⟨st_n, hsp_n, hcl_n, hcv_n, hfu_n, hm_n⟩ => by
                  pt_steps_nogrp
                  -- Join after `if (v >= cv) v = 0;` wrap-around
                  let wrapInv : Tup Val [i64] → Mem 64 → Prop := fun (v_next, ()) mw =>
                    v_next.toNat < st1.core.cur_vars ∧ mw = mn
                  refine wp_join_group wrapInv (fun _ (v_next, ()) mw ⟨hvn_lt, hmw⟩ => by
                    cases hmw; pt_steps_nogrp
                    exact hJloop (v_next, sc_v + 1#64, done_n, ()) mn
                      (by dsimp only [meas]; rw [hsc1_eq]; omega)
                      ⟨by rw [hsc1_eq]; omega, hvn_lt, st_n, hsp_n, hcl_n, hcv_n, hfu_n, hm_n⟩)
                    (fun Jw hJw => by
                      pt_steps_nogrp
                      · exact hJw (0#64, ()) mn ⟨hcv_pos, rfl⟩
                      · have hv1_lt : (v_v + 1#64).toNat < st1.core.cur_vars := by
                          pt_clear_big
                          have hnot : ¬st0.core.cur_vars % 2 ^ 64 ≤
                              (v_v.toNat + 1) % 2 ^ 64 := hc
                          rw [Nat.mod_eq_of_lt hcv_e64,
                            Nat.mod_eq_of_lt (by omega : v_v.toNat + 1 < 2 ^ 64)] at hnot
                          change (v_v + 1#64).toNat < st0.core.cur_vars
                          rw [hv1_eq]; omega
                        exact hJw (v_v + 1#64, ()) mn ⟨hv1_lt, rfl⟩))
                  (fun Jnext hJnext => ?_)
                pt_steps_nogrp
                · have hlit_to : ((v_v <<< (1#32 : BitVec 32).signExtend 64).setWidth 32).toNat =
                      2 * v_v.toNat := by
                    rw [BitVec.toNat_setWidth, hv_shl, Nat.mod_eq_of_lt (by omega)]
                  have hlit_lt' : ((v_v <<< (1#32 : BitVec 32).signExtend 64).setWidth 32).toNat <
                      2 * st.core.cur_vars := by rw [hlit_to]; omega
                  have hun_lit : st.core.vals[((v_v <<<
                      (1#32 : BitVec 32).signExtend 64).setWidth 32).toNat]?.getD 0#8 = 0#8 :=
                    m3pr_vals_eq_0_of_sext (by rw [hlit_to, hcl_sok.vals_len]; omega) (by
                      pt_clear_big
                      simpa only [hlit_to,
                        Nat.mod_eq_of_lt (by omega : 2 * v_v.toNat < 2 ^ 64)] using hc)
                  c0_call hAp
                  refine ⟨c, F0, st, R, rfl, hsp, hcl_st, hlit_lt', hun_lit, hm_st, ?_⟩; dsimp only
                  intro ap st_ap m_ap hap12 hap20 hcv_ap hfu_ap hap_dom hm_ap
                  have hcv_aps := hcv_ap.trans hcv_st
                  have hfu_aps := Nat.le_trans hfu_ap hfu_st
                  pt_steps_nogrp
                  · have hap_eq20 : ap = 20#64 := by pt_clear_big; exact hc
                    obtain ⟨huns, F_ap, hot_ap'⟩ := hap20 hap_eq20
                    exact hJexit (v_v, sc_v, done_v + 1#64, 20#64, ()) m_ap
                      ⟨hv_lt_cv, st_ap, hot_ap'.1, hcv_aps,
                       fun h => absurd h (by decide), fun _ => ⟨huns, F_ap, hot_ap'⟩,
                       Or.inr rfl, hfu_aps, hm_ap⟩
                  · have hap_eq2 : ap = 2#64 := by pt_clear_big; exact hc
                    obtain ⟨hsp_ap, hcl_ap⟩ := hap12 (Or.inr hap_eq2)
                    exact hJexit (v_v, sc_v, done_v + 1#64, 1#64, ()) m_ap
                      ⟨hv_lt_cv, st_ap, hsp_ap.1.1, hcv_aps,
                       fun _ => ⟨hsp_ap, hcl_ap⟩, fun h => absurd h (by decide),
                       Or.inl rfl, hfu_aps, hm_ap⟩
                  · have hap_eq1 : ap = 1#64 := by
                      pt_clear_big; rcases hap_dom with h | h | h <;> simp_all
                    obtain ⟨hsp_ap, hcl_ap⟩ := hap12 (Or.inl hap_eq1)
                    exact hJnext (done_v + 1#64, 1#64, ()) m_ap
                      ⟨st_ap, hsp_ap, hcl_ap, hcv_aps, hfu_aps, hm_ap⟩
                all_goals
                  exact hJnext (done_v, 1#64, ()) ml ⟨st, hsp, hcl_st, hcv_st, hfu_st, hm_st⟩
              all_goals exact hJexit (v_v, sc_v, done_v, 1#64, ()) ml hdone_exit
        · c0_steps
          · exact hJcur (0#64, ()) m ⟨hcv_pos, rfl⟩
          · have hv_lt : st0.scratch.iterating.toNat < st1.core.cur_vars := by
              pt_clear_big
              have hnot : ¬st0.core.cur_vars % 2 ^ 64 ≤ st0.scratch.iterating.toNat := hc
              rw [Nat.mod_eq_of_lt hcv_e64] at hnot
              change st0.scratch.iterating.toNat < st0.core.cur_vars; omega
            exact hJcur (st0.scratch.iterating, ()) m ⟨hv_lt, rfl⟩
  · pt_steps_nogrp
    · c0_call hBt
      have hpos_cl : 0 < s.core.cur_level := by
        pt_clear_big; exact Nat.pos_of_ne_zero fun h0 => hc (by simp [h0])
      refine ⟨c, s, R, rfl, hlen0, hcl_64, fun _ => hpos_mv_if hpos_cl, hw0.trail_lits_lt, hm0, ?_⟩
      dsimp only; intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m_bt hlen_bt _ _ hcl_bt
        hpres _ _ _ hbt_w _ hm_bt
      let st_bt := m3prBtState s vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc'
      have hw_bt := hbt_w F0 F_cur0 hw0 (Nat.zero_le _)
      have hsp_bt := m3prBtState_sparse hlen_bt hw_bt hlm0 hnd0 hext0 hdm0 hpres.1
      exact hJentry () m_bt ⟨st_bt, hsp_bt, by simp [st_bt, hcl_bt], rfl, rfl, Nat.le_refl _, hm_bt⟩
    · have hcl_0 : s.core.cur_level = 0 := by
        pt_clear_big; have h := congrArg BitVec.toNat hc
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_64] at h
      exact hJentry () m ⟨s, hsp0', hcl_0, rfl, rfl, Nat.le_refl _, hm0⟩

/-- Canonical `Full.fullProbeRunSpec` `Func.wp` proof for wrap-around `full_probe_run`. -/
theorem m3_probe_run_wp (Γ : Env)
    (hBacktrack : ∀ args m Q X, Full.fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X)
    (hAssumePair : ∀ args m Q X, Full.fullProbeAssumePairSpec args m Q X →
      Γ "full_probe_assume_pair" [i64, i32] [i64] args m Q X) :
    ∀ args m Q X, Full.fullProbeRunSpec args m Q X →
      Func.wp Γ full_probe_run_body args m Q X :=
  fun _ _ _ _ h => m3_probe_run_cursor_wp Γ hBacktrack hAssumePair _ _ _ _
    (fullProbeRunCursorSpec_of_canon h)

/-- `FullFastBveBudgets.fullProbeRunFastSpec` `Func.wp` proof for wrap-around `full_probe_run`. -/
theorem m3_probe_run_fast_wp (Γ : Env)
    (hBacktrack : ∀ args m Q X, Full.fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X)
    (hAssumePair : ∀ args m Q X, Full.fullProbeAssumePairSpec args m Q X →
      Γ "full_probe_assume_pair" [i64, i32] [i64] args m Q X) :
    ∀ args m Q X, FullFastBveBudgets.fullProbeRunFastSpec args m Q X →
      Func.wp Γ full_probe_run_body args m Q X :=
  fun _ _ _ _ h => m3_probe_run_cursor_wp Γ hBacktrack hAssumePair _ _ _ _
    (fullProbeRunCursorSpec_of_fast h)

end ProbeRunProof

/-! ## 3. `m3_backbone_lit_entails_wp` & `m3_backbone_wp` (`backbone.c` BIG Unit Discovery) -/

section BackboneProofs

open FullTransHelpers
open scoped FullArenaTactics FullTransTactics

private theorem bb_bnds {c : FullCfg} {k : FullCoreState} (hl : k.LengthsOk c) :
    2 * k.cur_vars + 1 < 2 ^ 30 ∧ k.wlen ≤ c.wcap ∧ k.wlen < 2 ^ 64 ∧ k.trail_end < 2 ^ 64 := by
  have := hl.cur_vars_le; have := hl.wlen_le; have := hl.trail_end_le
  have := c.hmaxv; have := c.hwcap; unfold dimacsBound at *; omega

private theorem bb_vals_lt {c : FullCfg} {k : FullCoreState} {l : Nat}
    (hl : FullCoreState.LengthsOk c k) (h : l < 2 * k.cur_vars) : l < k.vals.length := by
  rw [hl.vals_len]; have := hl.cur_vars_le; omega

private theorem bb_wstk_lt {c : FullCfg} {k : FullCoreState} {p end_v : Nat}
    (hl : FullCoreState.LengthsOk c k) (hp : p < end_v) (he : end_v ≤ k.wlen) :
    p < k.wstk.length := by
  rw [hl.wstk_len_arr]; have := hl.wlen_le; omega

private theorem bb_getElem_toNat {xs : List (BitVec 32)} {i : Nat} (hi : i < xs.length) :
    (xs[i]'hi).toNat = (xs[i]?.getD 0#32).toNat := by simp [List.getElem?_eq_getElem hi]

private theorem bb_bv64_sub1 {n : Nat} (hn1 : 0 < n) (hn2 : n < 2 ^ 64) :
    (BitVec.ofNat 64 n - 1#64).toNat = n - 1 := by bv_omega

private theorem bb_bv64_lt_eq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a < BitVec.ofNat 64 b) ↔ a < b := by bv_omega

private theorem bb_vals_ff_of_domain {v : BitVec 8} {z : BitVec 32}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) (hz : z = 0#32)
    (hslt : (v.signExtend 32).slt z = true) : v = 0xFF#8 := by
  subst hz; rcases hdom with rfl | rfl | rfl <;> first | rfl | exact absurd hslt (by decide)

private theorem bb_vals_zero_of_domain {v : BitVec 8} {z : BitVec 32}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) (hz : z = 0#32) (heq : v.signExtend 32 = z) :
    v = 0#8 := by
  subst hz; rcases hdom with rfl | rfl | rfl <;> first | rfl | exact absurd heq (by decide)

private theorem bb_watchSlice_step {F_cur : List (List Nat)} {k : FullCoreState}
    {nl p rem : Nat} {w0 : BitVec 32} (hpos : 0 < rem) (hg : k.wstk[p]? = some w0)
    (hsl : WatchSliceOk F_cur k nl p rem) :
    ((w0 &&& 0x80000000#32) = 0#32 → 2 ≤ rem ∧ WatchSliceOk F_cur k nl (p + 2) (rem - 2)) ∧
    ((w0 &&& 0x80000000#32) ≠ 0#32 →
      (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [nl, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
      WatchSliceOk F_cur k nl (p + 1) (rem - 1)) := by
  cases hsl with
  | empty => omega
  | bin hp hfl _ hlt hent htail =>
    rw [hp] at hg; cases Option.some.inj hg
    exact ⟨fun h0 => absurd h0 hfl, fun _ => ⟨hlt, hent, htail⟩⟩
  | large hp _ hfl _ _ htail =>
    rw [hp] at hg; cases Option.some.inj hg
    exact ⟨fun _ => ⟨by omega, htail⟩, fun hne => absurd hfl hne⟩

/-- Clean unwind completion for `full_backbone_lit`: once `st.core.trail_end = s.core.trail_end`
and `h->ant_sz = ticks` is written, `FullSparseInvW c F0 F_cur` holds verbatim on the same `F_cur`
without touching any watches or arena clauses. -/
private theorem bb_unroll_done_sparseW {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {cand : Nat} (hsp : FullSparseInvW c F0 F_cur s)
    (hu : TransUnrollInv c F0 F_cur s s cand s.core.trail_end st)
    (hte : st.core.trail_end = s.core.trail_end) (ticks : BitVec 64) :
    FullSparseInvW c F0 F_cur { st with scratch := { st.scratch with ant_sz := ticks } } := by
  have hlen0 := hsp.1; have hw0 := hsp.2.1
  have hvals_eq : st.core.vals = s.core.vals := List.ext_getElem? fun l => by
    by_cases hl : l < 2 * s.core.cur_vars
    · have hl1 : l < st.core.vals.length := by
        rw [hu.len_ok.core_ok.vals_len]; have := hlen0.core_ok.cur_vars_le; omega
      have hl2 : l < s.core.vals.length := by
        rw [hlen0.core_ok.vals_len]; have := hlen0.core_ok.cur_vars_le; omega
      have hgd : st.core.vals[l]?.getD 0#8 = s.core.vals[l]?.getD 0#8 := by
        by_cases h0 : s.core.vals[l]?.getD 0#8 = 0#8
        · rw [h0]; exact Classical.byContradiction fun hnz => by
            obtain ⟨i, _, _, _⟩ := hu.vals_only_trl l hl h0 hnz; omega
        · exact hu.vals_pres l hl h0
      rw [List.getElem?_eq_getElem hl1, List.getElem?_eq_getElem hl2] at hgd ⊢
      exact congrArg some hgd
    · exact hu.vals_hi_pres l (by omega)
  have hc_eq : st.core = { s.core with trl := st.core.trl } := by
    rw [hu.same_core, hvals_eq, hte]
  have htr : ∀ i < s.core.trail_end, st.core.trl[i]? = s.core.trl[i]? := hu.trl_pres
  have htr_nat : ∀ i < s.core.trail_end,
      (st.core.trl[i]?.getD 0#32).toNat = (s.core.trl[i]?.getD 0#32).toNat :=
    fun i hi => by rw [htr i hi]
  have hw_st : FullWitnessInv c F0 F_cur st.core := by
    rw [hc_eq]
    have htr' : ∀ i < s.core.trail_end,
        (st.core.trl[i]?.getD 0#32).toNat = (s.core.trl[i]?.getD 0#32).toNat := htr_nat
    exact {
      ext_sound := hw0.ext_sound
      inconsistent_sound := hw0.inconsistent_sound
      arena := ⟨hw0.arena.len_ok, hw0.arena.refs_wf, hw0.arena.shrk_term,
        hw0.arena.lits_lt, hw0.arena.entails⟩
      watches := hw0.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
      cur_level_le := hw0.cur_level_le
      trail_lits_lt := fun i hi => by dsimp only; rw [htr' i hi]; exact hw0.trail_lits_lt i hi
      trail_vars_nodup := fun i j hi hj he => by
        dsimp only at he; rw [htr' i hi, htr' j hj] at he
        exact hw0.trail_vars_nodup i j hi hj he
      vals_domain := hw0.vals_domain
      vals_true_iff := fun l hl => by
        dsimp only; rw [hw0.vals_true_iff l hl]
        exact ⟨fun ⟨i, hi, e⟩ => ⟨i, hi, by rw [htr' i hi]; exact e⟩,
          fun ⟨i, hi, e⟩ => ⟨i, hi, by rw [← htr' i hi]; exact e⟩⟩
      vals_false_iff := fun l hl => by
        dsimp only; rw [hw0.vals_false_iff l hl]
        exact ⟨fun ⟨i, hi, e⟩ => ⟨i, hi, by rw [htr' i hi]; exact e⟩,
          fun ⟨i, hi, e⟩ => ⟨i, hi, by rw [← htr' i hi]; exact e⟩⟩
      lvl_le := fun i hi => by dsimp only; rw [htr' i hi]; exact hw0.lvl_le i hi
      dec_earliest := fun i j hi hj he hpos => by
        dsimp only at he hpos; rw [htr' i hi, htr' j hj] at he; rw [htr' j hj] at hpos
        exact hw0.dec_earliest i j hi hj he hpos
      levels_inhabited := fun L h1 h2 => by
        obtain ⟨i, hi, he⟩ := hw0.levels_inhabited L h1 h2
        exact ⟨i, hi, by dsimp only; rw [htr' i hi]; exact he⟩
      level0_sound := fun i hi hl0 => by
        dsimp only at hl0 ⊢; rw [htr' i hi] at hl0 ⊢; exact hw0.level0_sound i hi hl0
      trail_pos_inv := fun i hi => by dsimp only; rw [htr' i hi]; exact hw0.trail_pos_inv i hi
      level0_rsn_none := fun i hi hl0 => by
        dsimp only at hl0 ⊢; rw [htr' i hi] at hl0 ⊢; exact hw0.level0_rsn_none i hi hl0
      frame_trail_lt := hw0.frame_trail_lt
      frame_trail_mono := hw0.frame_trail_mono
      frame_trail_before_lt := fun L h1 h2 i hi => by
        have hilt : i < s.core.trail_end := Nat.lt_of_lt_of_le hi (hw0.frame_trail_lt L h2)
        dsimp only; rw [htr' i hilt]; exact hw0.frame_trail_before_lt L h1 h2 i hi
      frame_dec_lt := hw0.frame_dec_lt
      reason_inv := fun idx hidx => by
        dsimp only; rw [htr' idx hidx]
        have hri := hw0.reason_inv idx hidx; dsimp only at hri
        intro hne; specialize hri hne
        by_cases hbin :
            (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
              0x80000000#32) ≠ 0#32
        · rw [ite_eq_left hbin] at hri ⊢
          obtain ⟨h1, h2, m0, hm0, htm, hlv⟩ := hri
          exact ⟨h1, h2, m0, hm0, by rw [htr' m0 (Nat.lt_trans hm0 hidx)]; exact htm, hlv⟩
        · rw [ite_eq_right hbin] at hri ⊢
          obtain ⟨h1, h2, h3⟩ := hri
          refine ⟨h1, h2, fun q hq => (h3 q hq).elim Or.inl fun ⟨m0, hm0, htm, hlv⟩ =>
            Or.inr ⟨m0, hm0, by rw [htr' m0 (Nat.lt_trans hm0 hidx)]; exact htm, hlv⟩⟩
      reason_lit_mem := fun idx hidx => by
        dsimp only; rw [htr' idx hidx]; exact hw0.reason_lit_mem idx hidx }
  refine ⟨⟨hu.len_ok.core_ok, { hu.len_ok.scratch_ok with }⟩, hw_st, ?_, ?_, ?_, ?_⟩
  · unfold FullLitMarksClear FullMrkZero; dsimp only; rw [hc_eq]; exact hsp.2.2.1
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
      fullArenaClauseRefsCore fullArenaClauseGarbCore fullArenaHdrCore fullArenaClauseLitsCore
      fullArenaClauseSizeCore
    dsimp only; rw [hc_eq]; exact hsp.2.2.2.1
  · refine ⟨fun i hi => ?_, by dsimp only; rw [hu.same_scratch]; exact hsp.2.2.2.2.1.2⟩
    dsimp only; rw [hu.same_scratch]
    have h1 := hsp.2.2.2.2.1.1 i hi
    unfold fullArenaClauseRefs fullArenaClauseRefsCore at h1 ⊢; rwa [hc_eq]
  · dsimp only; rw [hc_eq]; exact hsp.2.2.2.2.2

private theorem bb_unroll_c0_aux {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st_r : FullState} {cand : Nat} (hw0 : FullWitnessInv c F0 F_cur s.core)
    (hlen0 : s.LengthsOk c) (hu_r : TransUnrollInv c F0 F_cur s s cand s.core.trail_end st_r)
    (hte_gt : s.core.trail_end < st_r.core.trail_end) (hte_r_lt : st_r.core.trail_end < 2 ^ 64) :
    let idx := (BitVec.ofNat 64 (BitVec.ofNat 64 st_r.core.trail_end - 1#64).toNat).toNat
    ∃ hidx : idx < st_r.core.trl.length, let ul := st_r.core.trl[idx]'hidx
      (BitVec.setWidth 64 ul).toNat < st_r.core.vals.length ∧
      (BitVec.setWidth 64 (ul ^^^ 1#32)).toNat < st_r.core.vals.length ∧
      (BitVec.ofNat 64 st_r.core.trail_end - 1#64).toNat = st_r.core.trail_end - 1 ∧
      TransUnrollInv c F0 F_cur s s cand s.core.trail_end { st_r with core := { st_r.core with
        vals := (st_r.core.vals.set (BitVec.setWidth 64 ul).toNat 0#8).set
          (BitVec.setWidth 64 (ul ^^^ 1#32)).toNat 0#8,
        trail_end := (BitVec.ofNat 64 st_r.core.trail_end - 1#64).toNat } } := by
  have hlen_r := hu_r.len_ok
  obtain ⟨ul, hul_get, hul_lt, hu_r'⟩ := hu_r.unroll_step hw0 rfl rfl hlen0 hte_gt
  have hte1_bv := bb_bv64_sub1 (n := st_r.core.trail_end) (by omega) hte_r_lt
  have hul_vlen := bb_vals_lt (l := ul.toNat) hlen_r.core_ok (by rw [hu_r.same_core]; exact hul_lt)
  have huln_vlen := bb_vals_lt (l := (ul ^^^ 1#32).toNat) hlen_r.core_ok
    (by rw [ft_bv32_xor1, hu_r.same_core]; exact litNeg_lt_two_mul hul_lt)
  have hte1_len : (BitVec.ofNat 64 st_r.core.trail_end - 1#64).toNat < st_r.core.trl.length := by
    rw [hte1_bv, hlen_r.core_ok.trl_len]
    have := hlen_r.core_ok.trail_end_le; have := hlen_r.core_ok.cur_vars_le; omega
  have hte1_bv_len : (BitVec.ofNat 64 (BitVec.ofNat 64 st_r.core.trail_end - 1#64).toNat).toNat <
      st_r.core.trl.length := by simpa using hte1_len
  have hul_ge2 : st_r.core.trl[(BitVec.ofNat 64
      (BitVec.ofNat 64 st_r.core.trail_end - 1#64).toNat).toNat]'hte1_bv_len = ul := by
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)] using
      Option.some.inj ((List.getElem?_eq_getElem hte1_len).symm.trans (by rw [hte1_bv, hul_get]))
  exact ⟨hte1_bv_len, by rw [hul_ge2, ft_bv32_setWidth64]; exact hul_vlen,
    by rw [hul_ge2, ft_bv32_setWidth64]; exact huln_vlen, hte1_bv,
    by rw [hul_ge2, ft_bv32_setWidth64, ft_bv32_setWidth64, hte1_bv, ft_bv32_xor1]; exact hu_r'⟩

private theorem bb_addUnit_sparseW {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' cl' : Nat} {unass' unfl' inc' : BitVec 64} {phases' : List (BitVec 8)}
    {ta' ba' : BitVec 64} {pt' pb' : List (BitVec 8)} {hp' ps' : List (BitVec 32)} {hl' : Nat}
    {qsi' qss' : BitVec 64} (hsp : FullSparseInvW c F0 F_cur s) (hs' : s' = { s with
      core := {
        s.core with
        vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
        trail_end := te', propagated := prop', cur_level := cl', unassigned := unass',
        unflushed := unfl', inconsistent := inc' },
      scratch := { s.scratch with
        phases := phases', target_assigned := ta', best_assigned := ba',
        phases_target := pt', phases_best := pb', heap := hp', pos := ps',
        heap_len := hl', q_search_idx := qsi', q_search_stamp := qss' } })
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core) :
    FullSparseInvW c F0 F_cur s' := by
  subst hs'
  exact ⟨hlen', hw', hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

/-- `Func.wp` proof for `full_backbone_lit(h, cand)` against `fullBackboneLitEntailsSpec`:
proves every discovered backbone unit (`r = 1#64`) is semantically entailed by `cnfOfClauses F_cur`
and `r = 20#64` certifies `F0.Unsat`. -/
theorem m3_backbone_lit_entails_wp (Γ : Env)
    (h_add_unit : ∀ args m Q X,
      fullAddUnitSpec args m Q X → Γ "full_add_unit" [i64, i32] [.bool] args m Q X) :
    ∀ args m Q X, fullBackboneLitEntailsSpec args m Q X →
      Func.wp Γ full_backbone_lit_body args m Q X := by
  rintro ⟨h, cand, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hsp, hcl0, hm, hQ⟩
  unfold full_backbone_lit_body; ft_unmdata
  have hlen0 := hsp.1; have hw0 := hsp.2.1; have hdm0 := hsp.2.2.2.2.2
  have hbnds0 := bb_bnds hlen0.core_ok
  have hcv64 : s.core.cur_vars < 2 ^ 64 := by omega
  have hnlits_eq : (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
    rw [ft_bv64_shl1 (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv64]; omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv64]
  -- Guard 1: `if ((u64)cand >= nlits) return 0;`
  ft_split
  · ft_steps
    exact hQ 0#64 s m hsp hcl0 rfl rfl (Or.inl rfl)
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hm
  have hcand_lt : cand.toNat < 2 * s.core.cur_vars := by
    have hc : ¬2 * (s.core.cur_vars % 2 ^ 64) % 2 ^ 64 ≤ cand.toNat := ‹_›
    rw [Nat.mod_eq_of_lt hcv64, Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64)] at hc
    omega
  have hcand_vlen := bb_vals_lt hlen0.core_ok hcand_lt
  have hcand_sw_vlen : (BitVec.setWidth 64 cand).toNat < s.core.vals.length := by
    rw [ft_bv32_setWidth64]; exact hcand_vlen
  -- Guard 2: `if (vals[cand] != 0) return 0;`
  ft_split
  · ft_steps
    exact hQ 0#64 s m hsp hcl0 rfl rfl (Or.inl rfl)
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hm
  have hcand0 : s.core.vals[cand.toNat]?.getD 0#8 = 0#8 :=
    bb_vals_zero_of_domain (z := 0#32) (hw0.vals_domain cand.toNat hcand_lt) rfl (by
      rw [List.getElem?_eq_getElem hcand_vlen, Option.getD_some]
      exact ‹BitVec.signExtend 32 s.core.vals[cand.toNat] = _›)
  have hcand64_1 : ((cand.setWidth 64 <<< (1 : Nat)) + 1#64).toNat = 2 * cand.toNat + 1 := by
    have h1 : (cand.setWidth 64 <<< (1 : Nat)).toNat = 2 * cand.toNat := by
      rw [ft_bv64_shl1 (by rw [ft_bv32_setWidth64]; omega), ft_bv32_setWidth64]
    rw [ft_bv64_add1 (by rw [h1]; omega), h1]
  have hwv_b : 2 * cand.toNat + 1 < s.core.wvec.length := by
    rw [hlen0.core_ok.wvec_len]; have := hlen0.core_ok.cur_vars_le; omega
  -- Guard 3: `if (csz == 0) return 0;`
  ft_split
  · ft_steps
    exact hQ 0#64 s m hsp hcl0 rfl rfl (Or.inl rfl)
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hm
  -- Guard 4: `if (ticks == 0) return 0;`
  ft_split
  · ft_steps
    exact hQ 0#64 s m hsp hcl0 rfl rfl (Or.inl rfl)
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hm
  -- Seed BFS with `not_cand = cand ^ 1`
  let not_cand := cand ^^^ 1#32
  have hnot_eq : not_cand.toNat = cand.toNat ^^^ 1 := ft_bv32_xor1 cand
  have hnot_lt : not_cand.toNat < 2 * s.core.cur_vars := by
    rw [hnot_eq]; exact litNeg_lt_two_mul hcand_lt
  have hnot_vlen := bb_vals_lt hlen0.core_ok hnot_lt
  let saved := s.core.trail_end
  obtain ⟨hsaved_lt, hu1, hte1⟩ :=
    TransUnrollInv.init (st_pre := s) hw0 hlen0 rfl rfl rfl hcand_lt hcand0
  have hte_len : saved < s.core.trl.length := by
    rw [hlen0.core_ok.trl_len]; exact Nat.lt_of_lt_of_le hsaved_lt hlen0.core_ok.cur_vars_le
  have hbv_not : BitVec.ofNat 32 (cand.toNat ^^^ 1) = not_cand := BitVec.eq_of_toNat_eq
    (by rw [hnot_eq, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega))
  have hsav_lt := hbnds0.2.2.2
  have hte64_len : (BitVec.ofNat 64 s.core.trail_end).toNat < s.core.trl.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsav_lt]; exact hte_len
  have hwat0 : WatchesInv F_cur s.core := by
    have hwm := hw0.watches; unfold ModeWatchesInv at hwm
    simp only [hdm0, ↓reduceIte] at hwm; exact hwm
  ft_to_group
  -- Outer BFS loop: `(ticks, prop, failed)` (check SSA tuple order!)
  refine wp_loop_group (ts := [i64, i64, Ty.bool])
    (Inv := fun nb xs m2 => let tk := xs.1; let prop := xs.2.1; let fb := xs.2.2.1
      ∃ st_b : FullState, saved ≤ prop.toNat ∧ prop.toNat ≤ st_b.core.trail_end ∧
        nb = s.core.cur_vars - prop.toNat ∧
        TransUnrollInv c F0 F_cur s s cand.toNat saved st_b ∧
        (fb = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [cand.toNat])) ∧
        (FullMem c st_b ⋆ R) m2) ?_ ?_
  rotate_left
  · intro Lbfs hLbfs
    have hs_eq : (BitVec.ofNat 64 saved).toNat = saved := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsav_lt]
    have hnot_sw : (BitVec.setWidth 64 (BitVec.ofNat 32 (cand.toNat ^^^ 1))).toNat =
        cand.toNat ^^^ 1 := by
      rw [ft_bv32_setWidth64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have h1_sw : BitVec.setWidth 8 (1 : BitVec 32) = 1#8 := rfl
    have hcand_sw : (BitVec.setWidth 64 cand).toNat = cand.toNat := ft_bv32_setWidth64 cand
    have hff_sw : (BitVec.setWidth 8 (-1 : BitVec 32)) = 0xFF#8 := by decide
    have hte_p1 : (BitVec.ofNat 64 s.core.trail_end + 1).toNat = saved + 1 := by
      rw [show (1 : BitVec 64) = 1#64 from rfl,
        ft_bv64_add1 (by rw [show (BitVec.ofNat 64 s.core.trail_end).toNat = saved from hs_eq]
                         omega)]
      exact congrArg (· + 1) hs_eq
    ft_steps
    refine hLbfs (s.core.cur_vars - saved) (s.scratch.ant_sz, BitVec.ofNat 64 saved, false, ()) _
      ⟨_, by dsimp only; rw [hs_eq]; exact Nat.le_refl _, ?_, by dsimp only; rw [hs_eq], ?_,
        fun hf => False.elim (Bool.noConfusion hf), by assumption⟩
    · rw [hs_eq, hte_p1]; exact Nat.le_of_lt hte1
    · dsimp only [not_cand] at hbv_not
      rw [show (1#32 : BitVec 32) = 1 from rfl] at hbv_not
      simpa only [saved, hnot_sw, h1_sw, hcand_sw, hff_sw, ← hbv_not, hte_p1,
        show (BitVec.ofNat 64 s.core.trail_end).toNat = saved from hs_eq] using hu1
  rintro Lbfs nb ⟨tk, prop, fb, ⟨⟩⟩ m2 hLbfs ⟨st_b, hsp_le, hpt_le, hbneq, hu_b, hfb, hm2⟩
  dsimp only at hsp_le hpt_le hbneq hfb; have hlen_b := hu_b.len_ok
  -- Post-BFS join leading into unwind loop + `h->ant_sz = tk` + `if (fb) full_add_unit`
  refine wp_join_group (P := fun _ m3 => ∃ st_u : FullState,
      TransUnrollInv c F0 F_cur s s cand.toNat saved st_u ∧
      (fb = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [cand.toNat])) ∧
      (FullMem c st_u ⋆ R) m3) ?_ ?_
  · rintro Junw ⟨⟩ m3 ⟨st_u, hu_u, hfb_u, hm3⟩; ft_to_group
    refine wp_loop_group (ts := []) (Inv := fun nu _ m4 => ∃ st_r : FullState,
        nu = st_r.core.trail_end - saved ∧
        TransUnrollInv c F0 F_cur s s cand.toNat saved st_r ∧ (FullMem c st_r ⋆ R) m4) ?_ ?_
    rotate_left
    · intro Lu hLu; exact hLu (st_u.core.trail_end - saved) () m3 ⟨st_u, rfl, hu_u, hm3⟩
    rintro Lu nu ⟨⟩ m4 hLu ⟨st_r, huneq, hu_r, hm4⟩; have hlen_r := hu_r.len_ok
    have hte_r_lt : st_r.core.trail_end < 2 ^ 64 := (bb_bnds hlen_r.core_ok).2.2.2; ft_split
    · have hte_gt : saved < st_r.core.trail_end :=
        (bb_bv64_lt_eq hsav_lt hte_r_lt).mp (by simpa [BitVec.ult] using ‹_›)
      obtain ⟨hte1_bv_len, hul_sw_bv, huln_sw_bv, hte1_bv, hu_r''⟩ :=
        bb_unroll_c0_aux hw0 hlen0 hu_r hte_gt hte_r_lt
      have huln_sw_set : (BitVec.setWidth 64 (st_r.core.trl[(BitVec.ofNat 64
          (BitVec.ofNat 64 st_r.core.trail_end - 1#64).toNat).toNat]'hte1_bv_len ^^^ 1#32)).toNat <
          (st_r.core.vals.set (BitVec.setWidth 64 (st_r.core.trl[(BitVec.ofNat 64 (BitVec.ofNat 64
            st_r.core.trail_end - 1#64).toNat).toNat]'hte1_bv_len)).toNat 0#8).length := by
        rw [List.length_set]; exact huln_sw_bv
      ft_steps; exact hLu (st_r.core.trail_end - 1 - saved) () _ (by omega)
        ⟨_, by dsimp only; rw [hte1_bv], hu_r'', by assumption⟩
    have hte_eq : st_r.core.trail_end = saved := by
      have hng : ¬(saved < st_r.core.trail_end) := fun hlt => ‹¬(_ < _)› (by
        rwa [Nat.mod_eq_of_lt hsav_lt, Nat.mod_eq_of_lt hte_r_lt])
      have := hu_r.saved_le_te; omega
    have hsp_tk := bb_unroll_done_sparseW hsp hu_r hte_eq tk
    let st_tk : FullState := { st_r with scratch := { st_r.scratch with ant_sz := tk } }
    have hcl_tk : st_tk.core.cur_level = 0 := by
      change st_r.core.cur_level = 0; rw [hu_r.same_core]; exact hcl0
    have hcv_tk : st_tk.core.cur_vars = s.core.cur_vars := by
      change st_r.core.cur_vars = _; rw [hu_r.same_core]
    have hfu_tk : st_tk.core.fuel = s.core.fuel := by
      change st_r.core.fuel = _; rw [hu_r.same_core]
    ft_steps; ft_split; rotate_left
    · ft_steps
      exact hQ 0#64 st_tk _ hsp_tk hcl_tk hcv_tk hfu_tk (Or.inl rfl)
        (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (by assumption)
    ft_to_group; ft_call h_add_unit
    have hent_cand : (cnfOfClauses F_cur).EntailsClause (cnfClause [cand.toNat]) := hfb_u ‹_›
    refine ⟨c, F0, F_cur, st_tk, R, rfl, hsp_tk.1, hsp_tk.2.1, fun _ => hent_cand, ‹_›,
      fun ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
        phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss' m5 hlen5 hw5 hcl5 huns5 _ hm5 => ?_⟩
    let st_au : FullState := { st_tk with
      core := { st_tk.core with
        vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
        trail_end := te', propagated := prop', cur_level := cl', unassigned := unass',
        unflushed := unfl', inconsistent := inc' },
      scratch := { st_tk.scratch with
        phases := phases', target_assigned := ta', best_assigned := ba',
        phases_target := pt', phases_best := pb', heap := hp', pos := ps',
        heap_len := hl', q_search_idx := qsi', q_search_stamp := qss' } }
    have hsp_au := bb_addUnit_sparseW hsp_tk rfl hlen5 hw5
    ft_split
    · ft_steps
      exact hQ 1#64 st_au m5 hsp_au hcl5 hcv_tk hfu_tk (Or.inr (Or.inl rfl))
        (fun _ => ⟨hcand_lt, hent_cand⟩) (fun h => absurd h (by decide)) hm5
    · ft_steps
      have hok_f : ok = false := by cases ok <;> simp_all
      exact hQ 20#64 st_au m5 hsp_au hcl5 hcv_tk hfu_tk (Or.inr (Or.inr rfl))
        (fun h => absurd h (by decide))
        (fun _ => (huns5 (by dsimp only [Arg.val_var] at *; omega) hok_f).1) hm5
  -- Outer BFS loop body
  intro Junw hJunw
  ft_split; · ft_steps; exact hJunw () m2 ⟨st_b, hu_b, hfb, hm2⟩
  ft_split; rotate_left; · ft_steps; exact hJunw () m2 ⟨st_b, hu_b, hfb, hm2⟩
  ft_split; rotate_left; · ft_steps; exact hJunw () m2 ⟨st_b, hu_b, hfb, hm2⟩
  have hte_b_lt := (bb_bnds hlen_b.core_ok).2.2.2; have hcv_b_le := hlen_b.core_ok.cur_vars_le
  have hpt_lt : prop.toNat < st_b.core.trail_end := by
    have h1 : prop.toNat < st_b.core.trail_end % 2 ^ 64 := ‹_›
    rwa [Nat.mod_eq_of_lt hte_b_lt] at h1
  have hprop_tlen : prop.toNat < st_b.core.trl.length := by
    rw [hlen_b.core_ok.trl_len]; have := hlen_b.core_ok.trail_end_le; omega
  have hprop1 := ft_bv64_add1 (by omega : prop.toNat + 1 < 2 ^ 64)
  obtain ⟨lit, hlit_get, hlit_lt, _, _, _, hent_lit⟩ := hu_b.bfs_trl_inv prop.toNat hsp_le hpt_lt
  let nl := lit ^^^ 1#32; have hnl_eq := ft_bv32_xor1 lit
  have hnl_lt0 : nl.toNat < 2 * s.core.cur_vars := by rw [hnl_eq]; exact litNeg_lt_two_mul hlit_lt
  have hnl_lt : nl.toNat < 2 * st_b.core.cur_vars := by rw [hu_b.same_core]; exact hnl_lt0
  have hlit_ge : st_b.core.trl[prop.toNat]'hprop_tlen = lit :=
    Option.some.inj ((List.getElem?_eq_getElem hprop_tlen).symm.trans hlit_get)
  have hnl_shl : (BitVec.setWidth 64 (lit ^^^ 1#32) <<< 1).toNat = 2 * nl.toNat := by
    rw [ft_bv64_shl1 (by rw [ft_bv32_setWidth64]; omega), ft_bv32_setWidth64]
  have hnl_wv0 : (BitVec.setWidth 64
      (st_b.core.trl[prop.toNat]'hprop_tlen ^^^ 1#32) <<< 1).toNat < st_b.core.wvec.length := by
    rw [hlit_ge, hnl_shl, hlen_b.core_ok.wvec_len]; omega
  have hnl_wv1 : ((BitVec.setWidth 64 (st_b.core.trl[prop.toNat]'hprop_tlen ^^^ 1#32) <<< 1) +
      1#64).toNat < st_b.core.wvec.length := by
    rw [hlit_ge, ft_bv64_add1 (by rw [hnl_shl]; omega), hnl_shl, hlen_b.core_ok.wvec_len]; omega
  have hnl_bnd : fullWatchOffCore st_b.core nl.toNat + fullWatchSizeCore st_b.core nl.toNat ≤
      st_b.core.wlen := by
    have hb := hwat0.layout.bounds nl.toNat hnl_lt0
    unfold fullWatchOffCore fullWatchSizeCore at hb ⊢; rwa [hu_b.same_core]
  have hnl_slice0 : WatchSliceOk F_cur st_b.core nl.toNat
      (fullWatchOffCore st_b.core nl.toNat) (fullWatchSizeCore st_b.core nl.toNat) := by
    have hs := hwat0.slices nl.toNat hnl_lt0
    rw [show fullWatchOffCore st_b.core nl.toNat = fullWatchOffCore s.core nl.toNat by
          unfold fullWatchOffCore; rw [hu_b.same_core],
        show fullWatchSizeCore st_b.core nl.toNat = fullWatchSizeCore s.core nl.toNat by
          unfold fullWatchSizeCore; rw [hu_b.same_core]]
    exact WatchSliceOk.relocate_same (k := s.core) (k' := st_b.core)
      (by rw [hu_b.same_core]; exact Nat.le_refl _)
      (fun r hr => by unfold fullArenaClauseRefsCore at hr ⊢; rwa [hu_b.same_core])
      (fun _ _ => by rw [hu_b.same_core]) hs
  ft_to_group
  -- Join after inner watch-scan loop: `(tk2, fb2, _q)`
  refine wp_join_group (P := fun xs m3 => let tk2 := xs.1; let f2 := xs.2.1; ∃ st_w : FullState,
      TransUnrollInv c F0 F_cur s s cand.toNat saved st_w ∧
      st_b.core.trail_end ≤ st_w.core.trail_end ∧
      (f2 = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [cand.toNat])) ∧
      (FullMem c st_w ⋆ R) m3) ?_ ?_
  · rintro Jinn ⟨tk2, f2, _q, ⟨⟩⟩ m3 ⟨st_w, hu_w, hte_w, hf2, hm3⟩
    have hpt_pre : prop.toNat < s.core.cur_vars := by
      have := hlen_b.core_ok.trail_end_le; rw [hu_b.same_core] at this
      exact Nat.lt_of_lt_of_le hpt_lt this
    ft_steps; refine hLbfs (s.core.cur_vars - (prop.toNat + 1)) (tk2, prop + 1#64, f2, ()) m3
      (by rw [hbneq]; omega) ⟨st_w, by rw [hprop1]; omega, by rw [hprop1]; omega,
        by rw [hprop1], hu_w, hf2, hm3⟩
  intro Jinn hJinn; let loff := fullWatchOffCore st_b.core nl.toNat
  let lsz := fullWatchSizeCore st_b.core nl.toNat; let lend := loff + lsz; ft_to_group
  -- Inner watch-scan loop `(tk_q, q)`
  refine wp_loop_group (ts := [i64, i64]) (Inv := fun nq xs m3 => let tk_q := xs.1; let q := xs.2.1
      ∃ st_q : FullState, loff ≤ q.toNat ∧ q.toNat ≤ lend ∧
        nq = lend - q.toNat ∧ st_b.core.trail_end ≤ st_q.core.trail_end ∧
        WatchSliceOk F_cur st_q.core nl.toNat q.toNat (lend - q.toNat) ∧
        TransUnrollInv c F0 F_cur s s cand.toNat saved st_q ∧ (FullMem c st_q ⋆ R) m3) ?_ ?_
  rotate_left
  · intro Lq hLq
    have hloff_lt : loff < 2 ^ 64 := by
      have := hnl_bnd; have := (bb_bnds hlen_b.core_ok).2.2.1; omega
    have hlo_eq : (BitVec.ofNat 64 loff).toNat = loff := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hloff_lt]
    have hlo_arg : BitVec.setWidth 64 (st_b.core.wvec[(BitVec.setWidth 64
        (st_b.core.trl[prop.toNat]'hprop_tlen ^^^ (1 : BitVec 32)) <<<
          (1 : Nat)).toNat]'hnl_wv0) = BitVec.ofNat 64 loff := by
      apply BitVec.eq_of_toNat_eq; rw [ft_bv32_setWidth64, hlo_eq]
      have hidx2 : (BitVec.setWidth 64 (st_b.core.trl[prop.toNat]'hprop_tlen ^^^
          (1 : BitVec 32)) <<< (1 : Nat)).toNat = 2 * nl.toNat := by simpa [hlit_ge] using hnl_shl
      have hnl0 : 2 * nl.toNat < st_b.core.wvec.length := by rw [← hidx2]; exact hnl_wv0
      simp only [hidx2]; exact bb_getElem_toNat hnl0
    ft_steps; rw [hlo_arg]; exact hLq (lend - loff) (tk, BitVec.ofNat 64 loff, ()) m2
      ⟨st_b, by rw [hlo_eq]; exact Nat.le_refl _, by rw [hlo_eq]; omega, by rw [hlo_eq],
        Nat.le_refl _, by rw [hlo_eq]; simpa [lend, loff, lsz] using hnl_slice0, hu_b, hm2⟩
  rintro Lq nq ⟨tk_q, q, ⟨⟩⟩ m3 hLq ⟨st_q, hql, hqh, hqneq, hte_q, hsl_q, hu_q, hm3⟩
  dsimp only at hql hqh hqneq hsl_q; have hlen_q := hu_q.len_ok
  ft_split; rotate_left; · ft_steps; exact hJinn (tk_q, fb, q, ()) m3 ⟨st_q, hu_q, hte_q, hfb, hm3⟩
  ft_split; rotate_left; · ft_steps; exact hJinn (tk_q, fb, q, ()) m3 ⟨st_q, hu_q, hte_q, hfb, hm3⟩
  have hq_lt : q.toNat < lend := by
    have hnl0_lt : 2 * nl.toNat < st_b.core.wvec.length := by rw [hlen_b.core_ok.wvec_len]; omega
    have hnl1_lt : 2 * nl.toNat + 1 < st_b.core.wvec.length := by
      rw [hlen_b.core_ok.wvec_len]; omega
    have hlo_w := bb_getElem_toNat hnl0_lt; have hls_w := bb_getElem_toNat hnl1_lt
    have hq_c0 := ‹q.toNat < _›
    have hidx_eq : (st_b.core.trl[prop.toNat]'hprop_tlen).toNat ^^^ 1 = nl.toNat := by
      rw [hlit_ge, hnl_eq]
    have h2nl_lt : 2 * nl.toNat + 1 < 2 ^ 64 := by have := (bb_bnds hlen_b.core_ok).1; omega
    have hmod0 : 2 * nl.toNat % 2 ^ 64 = 2 * nl.toNat := Nat.mod_eq_of_lt (by omega)
    have hmod1 : (2 * nl.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 = 2 * nl.toNat + 1 := by
      rw [show (1 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt h2nl_lt]
    simp only [hidx_eq, hmod0, hmod1, hlo_w, hls_w] at hq_c0
    have := hnl_bnd; have := (bb_bnds hlen_b.core_ok).2.2.1
    change q.toNat < (loff + lsz) % 2 ^ 64 at hq_c0; rwa [Nat.mod_eq_of_lt (by omega)] at hq_c0
  have hq_len : q.toNat < st_q.core.wstk.length := by
    rw [hlen_q.core_ok.wstk_len_arr]; have := hnl_bnd; have := hlen_b.core_ok.wlen_le; omega
  have hstep := bb_watchSlice_step (by omega) (List.getElem?_eq_getElem hq_len) hsl_q
  ft_split
  · have hfl0 : (st_q.core.wstk[q.toNat] &&& 0x80000000#32) = 0#32 := ‹_›
    obtain ⟨hle2, hsl'⟩ := hstep.1 hfl0
    ft_steps
    have hq2 : (q + 2#64).toNat = q.toNat + 2 :=
      ft_bv64_add2 (by have := hnl_bnd; have := (bb_bnds hlen_b.core_ok).2.2.1; omega)
    exact hLq (lend - (q.toNat + 2)) (tk_q - 1#64, q + 2#64, ()) m3 (by omega)
      ⟨st_q, by rw [hq2]; omega, by rw [hq2]; omega, by rw [hq2], hte_q,
       by rw [hq2]; rwa [show lend - q.toNat - 2 = lend - (q.toNat + 2) by omega] at hsl',
       hu_q, hm3⟩
  have hfl_nz : (st_q.core.wstk[q.toNat] &&& 0x80000000#32) ≠ 0#32 := ‹_›
  obtain ⟨hot_lt, hent_nl, htail⟩ := hstep.2 hfl_nz
  have hq1 : (q + 1#64).toNat = q.toNat + 1 :=
    ft_bv64_add1 (by have := hnl_bnd; have := (bb_bnds hlen_b.core_ok).2.2.1; omega)
  let ot := st_q.core.wstk[q.toNat] &&& 0x7FFFFFFF#32
  have hent_ot := entails_pair_trans hent_lit (by rwa [← hnl_eq])
  have hot_vlen := bb_vals_lt hlen_q.core_ok hot_lt
  have hot_st : ot.toNat < 2 * s.core.cur_vars := by
    have hcv_q : st_q.core.cur_vars = s.core.cur_vars := by rw [hu_q.same_core]
    rw [← hcv_q]; exact hot_lt
  have htail' : WatchSliceOk F_cur st_q.core nl.toNat (q.toNat + 1) (lend - (q.toNat + 1)) := by
    rwa [show lend - q.toNat - 1 = lend - (q.toNat + 1) by omega] at htail
  -- Join after `if ((u64)ot < nlits) { ... }` leading to `q = q + 1`
  refine wp_join_group (P := fun _ m4 => ∃ st_q2 : FullState,
      st_b.core.trail_end ≤ st_q2.core.trail_end ∧
      WatchSliceOk F_cur st_q2.core nl.toNat (q.toNat + 1) (lend - (q.toNat + 1)) ∧
      TransUnrollInv c F0 F_cur s s cand.toNat saved st_q2 ∧ (FullMem c st_q2 ⋆ R) m4) ?_ ?_
  · rintro Jstep ⟨_, ⟨⟩⟩ m4 ⟨st_q2, hte2, hsl2, hu2, hm4⟩
    ft_steps
    exact hLq (lend - (q.toNat + 1)) (tk_q - 1#64, q + 1#64, ()) m4 (by omega)
      ⟨st_q2, by rw [hq1]; omega, by rw [hq1]; omega, by rw [hq1], hte2,
       by rw [hq1]; exact hsl2, hu2, hm4⟩
  intro Jstep hJstep
  ft_split; rotate_left
  · ft_steps; exact hJstep (fb, ()) m3 ⟨st_q, hte_q, htail', hu_q, hm3⟩
  have hdom_ot := hu_q.vals_domain hw0 rfl rfl hot_st
  ft_split
  · rename_i hslt_c0
    change (BitVec.signExtend 32 st_q.core.vals[ot.toNat]).slt 0#32 = true at hslt_c0
    have hval_ff := bb_vals_ff_of_domain (z := 0#32) hdom_ot rfl
      (by rw [List.getElem?_eq_getElem hot_vlen]; exact hslt_c0)
    have hent_cand := hu_q.entails_src_of_falsified hw0 rfl rfl hcl0 hot_st hval_ff hent_ot
    ft_steps; exact hJinn (tk_q - 1#64, true, q, ()) m3 ⟨st_q, hu_q, hte_q, fun _ => hent_cand, hm3⟩
  refine wp_join_group (P := fun _ m4 => ∃ st_q2 : FullState,
      st_b.core.trail_end ≤ st_q2.core.trail_end ∧
      WatchSliceOk F_cur st_q2.core nl.toNat (q.toNat + 1) (lend - (q.toNat + 1)) ∧
      TransUnrollInv c F0 F_cur s s cand.toNat saved st_q2 ∧ (FullMem c st_q2 ⋆ R) m4) ?_ ?_
  · rintro Jpush ⟨⟩ m4 ⟨st_q2, hte2, hsl2, hu2, hm4⟩
    ft_steps; exact hJstep (fb, ()) m4 ⟨st_q2, hte2, hsl2, hu2, hm4⟩
  intro Jpush hJpush
  ft_split; rotate_left; · ft_steps; exact hJpush () m3 ⟨st_q, hte_q, htail', hu_q, hm3⟩
  ft_split; rotate_left; · ft_steps; exact hJpush () m3 ⟨st_q, hte_q, htail', hu_q, hm3⟩
  rename_i hval0 _
  change BitVec.signExtend 32 st_q.core.vals[ot.toNat] = 0#32 at hval0
  have hot0 := bb_vals_zero_of_domain (z := 0#32) hdom_ot rfl
    (by rw [List.getElem?_eq_getElem hot_vlen]; exact hval0)
  obtain ⟨hte_q_lt, hu_q'⟩ := hu_q.push hw0 rfl rfl (fun _ _ => rfl) rfl hot_st hot0 hent_ot
  have hbv_ot : BitVec.ofNat 32 ot.toNat = ot := by simp
  have hotn_vlen : (BitVec.setWidth 64 (ot ^^^ 1#32)).toNat < (st_q.core.vals.set
      (BitVec.setWidth 64 ot).toNat (BitVec.setWidth 8 (1 : BitVec 32))).length := by
    rw [List.length_set, ft_bv32_setWidth64, ft_bv32_xor1, hlen_q.core_ok.vals_len]
    have := litNeg_lt_two_mul hot_lt; have := hlen_q.core_ok.cur_vars_le; dsimp only [ot]; omega
  have hteq_lt : st_q.core.trail_end < 2 ^ 64 := (bb_bnds hlen_q.core_ok).2.2.2
  have hte_bv : (BitVec.ofNat 64 st_q.core.trail_end).toNat = st_q.core.trail_end := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hteq_lt]
  have hteq_tlen : (BitVec.ofNat 64 st_q.core.trail_end).toNat < st_q.core.trl.length := by
    rw [hte_bv, hlen_q.core_ok.trl_len]; have := hlen_q.core_ok.cur_vars_le; omega
  have hteq1 : (BitVec.ofNat 64 st_q.core.trail_end + 1#64).toNat = st_q.core.trail_end + 1 := by
    rw [ft_bv64_add1 (by omega), hte_bv]
  ft_steps
  let st_q2 : FullState := { st_q with core := { st_q.core with
      vals := (st_q.core.vals.set ot.toNat 1#8).set (ot.toNat ^^^ 1) 0xFF#8,
      trl := st_q.core.trl.set st_q.core.trail_end ot, trail_end := st_q.core.trail_end + 1 } }
  have hm_q2 : (FullMem c { st_q with core := { st_q.core with
      vals := (st_q.core.vals.set (BitVec.setWidth 64 ot).toNat 1#8).set
        (BitVec.setWidth 64 (ot ^^^ 1#32)).toNat 0xFF#8,
      trl := st_q.core.trl.set (BitVec.ofNat 64 st_q.core.trail_end).toNat ot,
      trail_end := (BitVec.ofNat 64 st_q.core.trail_end + 1#64).toNat } } ⋆ R) _ := ‹_›
  simp only [ft_bv32_setWidth64, ft_bv32_xor1, hte_bv, hteq1] at hm_q2
  exact hJpush () _ ⟨st_q2, Nat.le_trans hte_q (Nat.le_succ _),
    WatchSliceOk.relocate_same (k := st_q.core) (k' := st_q2.core) (Nat.le_refl _) (fun _ hr => hr)
      (fun _ _ => rfl) htail',
    by simpa only [hbv_ot] using hu_q', hm_q2⟩

/-- Canonical `FullSparseInv` `Func.wp` proof for `full_backbone_lit(h, cand)`. -/
theorem m3_backbone_lit_wp (Γ : Env)
    (h_add_unit : ∀ args m Q X,
      fullAddUnitSpec args m Q X → Γ "full_add_unit" [i64, i32] [.bool] args m Q X) :
    ∀ args m Q X, fullBackboneLitSpec args m Q X →
      Func.wp Γ full_backbone_lit_body args m Q X := by
  rintro ⟨h, cand, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hcl0, hm, hQ⟩
  obtain ⟨F_cur, hspW⟩ := hsp.exists_witness
  exact m3_backbone_lit_entails_wp Γ h_add_unit _ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hspW, hcl0, hm,
      fun r s' m' hspW' hcl' hcv' hfu' hr _ huns hm' =>
        hQ r s' m' hspW'.toSparse hcl' hcv' hfu' hr huns hm'⟩

private theorem fullSparseInv_with_delayed_len {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hsp : FullSparseInv c F0 s) (dl' : Nat) :
    FullSparseInv c F0 { s with scratch := { s.scratch with delayed_len := dl' } } :=
  hsp.of_safetySlice ⟨hsp.1.lengths.core_ok, { hsp.1.lengths.scratch_ok with }⟩ rfl ⟨rfl, rfl⟩

/-- `Func.wp` proof for multi-round `full_backbone(h, tick_lim)` against `fullBackboneSpec`. -/
theorem m3_backbone_wp (Γ : Env)
    (h_backtrack : ∀ args m Q X,
      fullBacktrackSpec args m Q X → Γ "full_backtrack" [i64, i64] [] args m Q X)
    (h_propagate : ∀ args m Q X,
      fullPropagateSpec args m Q X → Γ "full_propagate" [i64] [i64] args m Q X)
    (h_backbone_lit : ∀ args m Q X,
      fullBackboneLitSpec args m Q X → Γ "full_backbone_lit" [i64, i32] [i64] args m Q X) :
    ∀ args m Q X, fullBackboneSpec args m Q X → Func.wp Γ full_backbone_body args m Q X := by
  rintro ⟨h, tick_lim, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hm, hQ⟩
  unfold full_backbone_body; ft_unmdata
  -- Join after initial `if (h->cur_level != 0) full_backtrack(h, 0)`
  refine wp_join_group (P := fun _ m1 => ∃ s1 : FullState, FullSparseInv c F0 s1 ∧
      s1.core.cur_level = 0 ∧ s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m1) ?_ ?_
  · rintro Jbt ⟨⟩ m1 ⟨s1, hsp1, hcl1, hfu1, hm1⟩
    have hlen1 := hsp1.1.lengths; have hbnds1 := bb_bnds hlen1.core_ok
    ft_to_group
    -- Join for early return `if (num_binary == 0 || tick_lim == 0 || cv == 0)`
    refine wp_join_group (P := fun _ me => me = m1) ?_ ?_
    · rintro Jearly ⟨⟩ me rfl
      ft_steps
      exact hQ 1#64 _ _ (fullSparseInv_with_probing hsp1 0#64) hcl1 rfl hfu1 (Or.inl rfl)
        (fun h => absurd h (by decide)) (by assumption)
    intro Jearly hJearly
    ft_split; · ft_steps; exact hJearly () m1 rfl
    ft_split; · ft_steps; exact hJearly () m1 rfl
    ft_split; · ft_steps; exact hJearly () m1 rfl
    ft_steps
    let s1p := { s1 with core := { s1.core with probing := 1#64 } }
    have hsp1p := fullSparseInv_with_probing hsp1 1#64
    obtain ⟨F_c1, hw1p⟩ := hsp1p.1.witness
    ft_call h_propagate
    refine ⟨c, F0, F_c1, s1p, R, rfl, hsp1p.1.lengths, hw1p, hsp1p.2.2.2.2, (by assumption),
      fun pr0 vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
        fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m2 hlen2 hw2 _ hperm2 hfu2 _ _
        hpr1 _ _ hm2 => ?_⟩
    let s2 : FullState := { s1p with
      core := { s1p.core with
        vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
        trail_end := te', propagated := prop', unassigned := unass', unflushed := unfl',
        wvec := wvec', arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
        fuel := fuel', confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
        confl_lit1 := c1', oom := oom' },
      scratch := { s1p.scratch with search_ticks := ticks', wsort := wsort', phases := phases' } }
    have hsp2 := fullPropagate_sparse hsp1p rfl hlen2 hw2 hperm2
    have hfu2s : s2.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfu2 hfu1
    have hcl2 : s2.core.cur_level = 0 := hcl1
    have hcv2 : s2.core.cur_vars = s1.core.cur_vars := rfl
    ft_split
    · ft_steps
      exact hQ 20#64 _ _ (fullSparseInv_with_probing hsp2 0#64) hcl2 rfl hfu2s (Or.inr rfl)
        (fun _ => level0_unsat_of_conflict_okW hw2 hcl2 (hpr1 ‹_›).2.2) (by assumption)
    ft_split
    · ft_steps
      exact hQ 1#64 _ _ (fullSparseInv_with_probing hsp2 0#64) hcl2 rfl hfu2s (Or.inl rfl)
        (fun h => absurd h (by decide)) (by assumption)
    ft_to_group
    -- Outer round loop: `brkTs = [i64, i64]` (`res, round`), `lpTs = [i64, i64]` (`res, round`)
    refine wp_loop_break_group (brkTs := [i64, i64]) (lpTs := [i64, i64])
      (BrkPost := fun xs m' => let res := xs.1; ∃ sb : FullState, FullSparseInv c F0 sb ∧
        sb.core.cur_level = 0 ∧ sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (res = 1#64 ∨ res = 20#64) ∧ (res = 20#64 → F0.Unsat) ∧ (FullMem c sb ⋆ R) m')
      (Inv := fun nr xs m' => let res := xs.1; let rnd := xs.2.1
        ∃ sr : FullState, rnd.toNat ≤ 4 ∧ nr = 4 - rnd.toNat ∧
          FullSparseInv c F0 sr ∧ sr.core.cur_level = 0 ∧
          sr.core.cur_vars = s1.core.cur_vars ∧ sr.core.fuel.toNat ≤ s.core.fuel.toNat ∧
          (res = 1#64 ∨ res = 20#64) ∧ (res = 20#64 → F0.Unsat) ∧
          (FullMem c sr ⋆ R) m') ?_ ?_ ?_
    · rintro Bout ⟨res, _rnd, ⟨⟩⟩ mb ⟨sb, hspb, hclb, hfub, hresb, hunsb, hmb⟩
      ft_steps
      exact hQ res _ _ (fullSparseInv_with_probing hspb 0#64) hclb rfl hfub hresb hunsb
        (by assumption)
    · rintro Bout Lout nr ⟨res, rnd, ⟨⟩⟩ mr hBout hLout
        ⟨sr, hrnd_le, hnr, hspr, hclr, hcvr, hfur, hresr, hunsr, hmr⟩
      dsimp only at hrnd_le hnr
      have hBoutr : Bout (res, rnd, ()) mr := hBout (res, rnd, ()) mr ⟨sr, hspr, hclr, hfur,
        hresr, hunsr, hmr⟩
      ft_split; rotate_left; · ft_steps; exact hBoutr
      have hrnd_lt : rnd.toNat < 4 := by
        have hlt : rnd.toNat < (4#64 : BitVec 64).toNat := by simpa [BitVec.ult] using ‹_›
        exact hlt
      ft_split; rotate_left; · ft_steps; exact hBoutr
      ft_split; rotate_left; · ft_steps; exact hBoutr
      ft_split; rotate_left; · ft_steps; exact hBoutr
      ft_to_group
      -- Inner variable sweep loop: `(res_i, found, v)`
      refine wp_loop_break_group (brkTs := [i64, i64, i64]) (lpTs := [i64, i64])
        (BrkPost := fun xs m' => let res_i := xs.1
          ∃ sv : FullState, FullSparseInv c F0 sv ∧ sv.core.cur_level = 0 ∧
            sv.core.cur_vars = s1.core.cur_vars ∧ sv.core.fuel.toNat ≤ s.core.fuel.toNat ∧
            (res_i = 1#64 ∨ res_i = 20#64) ∧ (res_i = 20#64 → F0.Unsat) ∧ (FullMem c sv ⋆ R) m')
        (Inv := fun nv xs m' => let v := xs.2.1
          ∃ sv : FullState, v.toNat ≤ s1.core.cur_vars ∧ nv = s1.core.cur_vars - v.toNat ∧
            FullSparseInv c F0 sv ∧ sv.core.cur_level = 0 ∧
            sv.core.cur_vars = s1.core.cur_vars ∧ sv.core.fuel.toNat ≤ s.core.fuel.toNat ∧
            (FullMem c sv ⋆ R) m') ?_ ?_ ?_
      · -- Post inner-loop: check break, optional re-arm loop, check `found == 0`, next round
        rintro Bv ⟨res_i, _fnd_i, _v_i, ⟨⟩⟩ mv ⟨sv, hspv, hclv, hcvv, hfuv, hresv, hunsv, hmv⟩
        have hBov : Bout (res_i, rnd, ()) mv :=
          hBout (res_i, rnd, ()) mv ⟨sv, hspv, hclv, hfuv, hresv, hunsv, hmv⟩
        ft_split; · ft_steps; exact hBov
        ft_split; · ft_steps; exact hBov
        ft_split; · ft_steps; exact hBov
        -- Join after optional re-arm `if (v >= cv && h->ant_sz > 0)`
        refine wp_join_group (P := fun _ mra => ∃ sra : FullState, FullSparseInv c F0 sra ∧
            sra.core.cur_level = 0 ∧ sra.core.cur_vars = s1.core.cur_vars ∧
            sra.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sra ⋆ R) mra) ?_ ?_
        · rintro Jra ⟨⟩ mra ⟨sra, hspra, hclra, hcvra, hfura, hmra⟩
          ft_split
          · ft_steps
            exact hBout (res_i, rnd, ()) mra ⟨sra, hspra, hclra, hfura, hresv, hunsv, hmra⟩
          · ft_steps
            have hr1 : (rnd + 1#64).toNat = rnd.toNat + 1 := ft_bv64_add1 (by omega)
            exact hLout (4 - (rnd.toNat + 1)) (res_i, rnd + 1#64, ()) mra (by omega)
              ⟨sra, by dsimp only; rw [hr1]; omega, by dsimp only; rw [hr1],
                hspra, hclra, hcvra, hfura, hresv, hunsv, hmra⟩
        intro Jra hJra
        ft_split; rotate_left; · ft_steps; exact hJra () mv ⟨sv, hspv, hclv, hcvv, hfuv, hmv⟩
        ft_split; rotate_left; · ft_steps; exact hJra () mv ⟨sv, hspv, hclv, hcvv, hfuv, hmv⟩
        ft_to_group
        -- Re-arm loop: `while (r < cv) { ...; r++; }`
        refine wp_loop_group (ts := [i64]) (Inv := fun nra xs mra => let ri := xs.1
            ∃ sra : FullState, ri.toNat ≤ s1.core.cur_vars ∧ nra = s1.core.cur_vars - ri.toNat ∧
              FullSparseInv c F0 sra ∧ sra.core.cur_level = 0 ∧
              sra.core.cur_vars = s1.core.cur_vars ∧ sra.core.fuel.toNat ≤ s.core.fuel.toNat ∧
              (FullMem c sra ⋆ R) mra) ?_ ?_
        rotate_left
        · intro Lra hLra; ft_steps
          exact hLra s1.core.cur_vars (0#64, ()) mv
            ⟨sv, Nat.zero_le _, rfl, hspv, hclv, hcvv, hfuv, hmv⟩
        rintro Lra nra ⟨ri, ⟨⟩⟩ mra hLra ⟨sra, hrile, hnra, hspra, hclra, hcvra, hfura, hmra⟩
        dsimp only at hrile hnra
        ft_split; rotate_left; · ft_steps; exact hJra () mra ⟨sra, hspra, hclra, hcvra, hfura, hmra⟩
        have hcv_lt : s1.core.cur_vars < 2 ^ 64 := by omega
        have hri_lt : ri.toNat < s1.core.cur_vars := by
          have hlt : ri.toNat < (BitVec.ofNat 64 s1.core.cur_vars).toNat := by
            simpa [BitVec.ult] using ‹_›
          rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv_lt] at hlt
        have hri1 : (ri + 1#64).toNat = ri.toNat + 1 := ft_bv64_add1 (by omega)
        have hlen_ra := hspra.1.lengths
        have hri_fl : ri.toNat < sra.core.flags.length := by
          rw [hlen_ra.core_ok.flags_len]; have := hlen_ra.core_ok.cur_vars_le; omega
        have hri_v : (ri <<< (1 : Nat)).toNat < sra.core.vals.length := by
          rw [ft_bv64_shl1 (by omega), hlen_ra.core_ok.vals_len]
          have := hlen_ra.core_ok.cur_vars_le; omega
        refine wp_join_group (P := fun _ mra2 => ∃ sra2 : FullState, FullSparseInv c F0 sra2 ∧
            sra2.core.cur_level = 0 ∧ sra2.core.cur_vars = s1.core.cur_vars ∧
            sra2.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sra2 ⋆ R) mra2) ?_ ?_
        · rintro Jstep ⟨⟩ mra2 ⟨sra2, hsp2', hcl2', hcv2', hfu2', hm2'⟩
          ft_steps
          exact hLra (s1.core.cur_vars - (ri.toNat + 1)) (ri + 1#64, ()) mra2 (by omega)
            ⟨sra2, by dsimp only; rw [hri1]; omega, by dsimp only; rw [hri1],
              hsp2', hcl2', hcv2', hfu2', hm2'⟩
        intro Jstep hJstep
        ft_split; rotate_left
        · ft_steps; exact hJstep () mra ⟨sra, hspra, hclra, hcvra, hfura, hmra⟩
        ft_split; rotate_left
        · ft_steps; exact hJstep () mra ⟨sra, hspra, hclra, hcvra, hfura, hmra⟩
        ft_steps
        exact hJstep () _
          ⟨_, fullSparseInv_clear_fl_trans hspra, hclra, hcvra, hfura, by assumption⟩
      · -- Inner variable sweep body
        rintro Bv Lv nv ⟨fnd, v, ⟨⟩⟩ mv hBv hLv ⟨sv, hvle, hnv, hspv, hclv, hcvv, hfuv, hmv⟩
        dsimp only at hvle hnv
        have hlenv := hspv.1.lengths
        have hcv_lt : s1.core.cur_vars < 2 ^ 64 := by omega
        have hBv1 : Bv (res, fnd, v, ()) mv := hBv (res, fnd, v, ()) mv ⟨sv, hspv, hclv, hcvv,
          hfuv, hresr, hunsr, hmv⟩
        ft_split; rotate_left; · ft_steps; exact hBv1
        have hv_lt : v.toNat < s1.core.cur_vars := by
          have hlt : v.toNat < (BitVec.ofNat 64 s1.core.cur_vars).toNat := by
            simpa [BitVec.ult] using ‹_›
          rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv_lt] at hlt
        ft_split; rotate_left; · ft_steps; exact hBv1
        ft_split; rotate_left; · ft_steps; exact hBv1
        ft_split; rotate_left; · ft_steps; exact hBv1
        have hv_fl : v.toNat < sv.core.flags.length := by
          rw [hlenv.core_ok.flags_len]; have := hlenv.core_ok.cur_vars_le; omega
        have hv_v : (v <<< (1 : Nat)).toNat < sv.core.vals.length := by
          rw [ft_bv64_shl1 (by omega), hlenv.core_ok.vals_len]
          have := hlenv.core_ok.cur_vars_le; omega
        have hv1 : (v + 1#64).toNat = v.toNat + 1 := ft_bv64_add1 (by omega)
        -- Join at end of `if ((fl[v] & FL_ACTIVE) != 0 && vals[2*v] == 0)` leading to `v++`
        refine wp_join_group (P := fun _ m3 => ∃ sn : FullState,
            FullSparseInv c F0 sn ∧ sn.core.cur_level = 0 ∧ sn.core.cur_vars = s1.core.cur_vars ∧
            sn.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sn ⋆ R) m3) ?_ ?_
        · rintro Jnext ⟨_res', fnd', ⟨⟩⟩ m3 ⟨sn, hspn, hcln, hcvn, hfun, hm3⟩
          ft_steps
          exact hLv (s1.core.cur_vars - (v.toNat + 1)) (fnd', v + 1#64, ()) m3 (by omega)
            ⟨sn, by dsimp only; rw [hv1]; omega, by dsimp only; rw [hv1],
              hspn, hcln, hcvn, hfun, hm3⟩
        intro Jnext hJnext
        ft_split; rotate_left
        · ft_steps; exact hJnext (res, fnd, ()) mv ⟨sv, hspv, hclv, hcvv, hfuv, hmv⟩
        ft_split; rotate_left
        · ft_steps; exact hJnext (res, fnd, ()) mv ⟨sv, hspv, hclv, hcvv, hfuv, hmv⟩
        -- Join between `FL_BONE0` block and `FL_BONE1` block: `(res1, fnd1, ())`
        refine wp_join_group (P := fun xs m3 => xs.1 = res ∧ ∃ sm : FullState,
            FullSparseInv c F0 sm ∧ sm.core.cur_level = 0 ∧ sm.core.cur_vars = s1.core.cur_vars ∧
            sm.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sm ⋆ R) m3) ?_ ?_
        · -- `FL_BONE1` block
          rintro Jmid ⟨res1, fnd1, ⟨⟩⟩ m3 ⟨hres1, sm, hspm, hclm, hcvm, hfum, hm3⟩
          dsimp only at hres1; subst hres1
          have hlenm := hspm.1.lengths
          have hv_flm : v.toNat < sm.core.flags.length := by
            rw [hlenm.core_ok.flags_len]; have := hlenm.core_ok.cur_vars_le; omega
          have hv_vm : (v <<< (1 : Nat)).toNat < sm.core.vals.length := by
            rw [ft_bv64_shl1 (by omega), hlenm.core_ok.vals_len]
            have := hlenm.core_ok.cur_vars_le; omega
          ft_split; rotate_left
          · ft_steps; exact hJnext (res1, fnd1, ()) m3 ⟨sm, hspm, hclm, hcvm, hfum, hm3⟩
          ft_split; rotate_left
          · ft_steps; exact hJnext (res1, fnd1, ()) m3 ⟨sm, hspm, hclm, hcvm, hfum, hm3⟩
          ft_split; rotate_left
          · ft_steps; exact hJnext (res1, fnd1, ()) m3 ⟨sm, hspm, hclm, hcvm, hfum, hm3⟩
          ft_split; rotate_left
          · ft_steps; exact hJnext (res1, fnd1, ()) m3 ⟨sm, hspm, hclm, hcvm, hfum, hm3⟩
          ft_split; rotate_left
          · ft_steps; exact hJnext (res1, fnd1, ()) m3 ⟨sm, hspm, hclm, hcvm, hfum, hm3⟩
          ft_to_group; ft_call h_backbone_lit
          refine ⟨c, F0, sm, R, rfl, hspm, hclm, hm3,
            fun br1 sb1 m4 hspb1 hclb1 hcvb1 hfub1 _ hunsb1 hm4 => ?_⟩
          have hcvb1' : sb1.core.cur_vars = s1.core.cur_vars := hcvb1.trans hcvm
          have hfub1' : sb1.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hfub1]; exact hfum
          ft_split
          · ft_steps
            exact hBv (20#64, fnd1, v, ()) m4 ⟨sb1, hspb1, hclb1, hcvb1', hfub1', Or.inr rfl,
              fun _ => hunsb1 ‹_›, hm4⟩
          -- Join after `if (h->ant_sz > 0) fl[v] &= ~FL_BONE1`
          refine wp_join_group (P := fun _ m5 => ∃ sc1 : FullState, FullSparseInv c F0 sc1 ∧
              sc1.core.cur_level = 0 ∧ sc1.core.cur_vars = s1.core.cur_vars ∧
              sc1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sc1 ⋆ R) m5) ?_ ?_
          · rintro Jcl1 ⟨⟩ m5 ⟨sc1, hspc1, hclc1, hcvc1, hfuc1, hm5⟩
            ft_split; rotate_left
            · ft_steps; exact hJnext (res1, fnd1, ()) m5 ⟨sc1, hspc1, hclc1, hcvc1, hfuc1, hm5⟩
            ft_steps
            let sc1d := { sc1 with scratch := { sc1.scratch with
              delayed_len := (BitVec.ofNat 64 sc1.scratch.delayed_len + 1#64).toNat } }
            have hspc1d : FullSparseInv c F0 sc1d :=
              fullSparseInv_with_delayed_len hspc1 _
            obtain ⟨F_c1d, hw1d⟩ := hspc1d.1.witness
            ft_call h_propagate
            refine ⟨c, F0, F_c1d, sc1d, R, rfl, hspc1d.1.lengths, hw1d, hspc1d.2.2.2.2,
              (by assumption),
              fun p1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fuel1 _ _ _ _ _ _ _ _ m6 hlen6 hw6 _
                hperm6 hfu6 _ _ hp1 _ _ hm6 => ?_⟩
            have hspp1 := fullPropagate_sparse hspc1d rfl hlen6 hw6 hperm6
            have hfup1 : fuel1.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfu6 hfuc1
            ft_split
            · ft_steps
              exact hBv (20#64, fnd1 + 1#64, v, ()) m6 ⟨_, hspp1, hclc1, hcvc1, hfup1, Or.inr rfl,
                fun _ => level0_unsat_of_conflict_okW hw6 hclc1 (hp1 ‹_›).2.2, hm6⟩
            ft_split
            · ft_steps
              exact hBv (res1, fnd1 + 1#64, v, ()) m6 ⟨_, hspp1, hclc1, hcvc1, hfup1, hresr,
                hunsr, hm6⟩
            · ft_steps
              exact hJnext (res1, fnd1 + 1#64, ()) m6 ⟨_, hspp1, hclc1, hcvc1, hfup1, hm6⟩
          intro Jcl1 hJcl1
          have hv_fl1 : v.toNat < sb1.core.flags.length := by
            rw [hspb1.1.lengths.core_ok.flags_len]
            have := hspb1.1.lengths.core_ok.cur_vars_le; omega
          ft_split
          · ft_steps
            exact hJcl1 () _ ⟨_, fullSparseInv_clear_fl_trans hspb1, hclb1, hcvb1', hfub1',
              by assumption⟩
          · ft_steps; exact hJcl1 () m4 ⟨sb1, hspb1, hclb1, hcvb1', hfub1', hm4⟩
        -- `FL_BONE0` block
        intro Jmid hJmid
        ft_split; rotate_left
        · ft_steps; exact hJmid (res, fnd, ()) mv ⟨rfl, sv, hspv, hclv, hcvv, hfuv, hmv⟩
        ft_to_group; ft_call h_backbone_lit
        refine ⟨c, F0, sv, R, rfl, hspv, hclv, hmv,
          fun br0 sb0 m4 hspb0 hclb0 hcvb0 hfub0 _ hunsb0 hm4 => ?_⟩
        have hcvb0' : sb0.core.cur_vars = s1.core.cur_vars := hcvb0.trans hcvv
        have hfub0' : sb0.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hfub0]; exact hfuv
        ft_split
        · ft_steps
          exact hBv (20#64, fnd, v, ()) m4 ⟨sb0, hspb0, hclb0, hcvb0', hfub0', Or.inr rfl,
            fun _ => hunsb0 ‹_›, hm4⟩
        -- Join after `if (h->ant_sz > 0) fl[v] &= ~FL_BONE0`
        refine wp_join_group (P := fun _ m5 => ∃ sc0 : FullState, FullSparseInv c F0 sc0 ∧
            sc0.core.cur_level = 0 ∧ sc0.core.cur_vars = s1.core.cur_vars ∧
            sc0.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sc0 ⋆ R) m5) ?_ ?_
        · rintro Jcl0 ⟨⟩ m5 ⟨sc0, hspc0, hclc0, hcvc0, hfuc0, hm5⟩
          ft_split; rotate_left
          · ft_steps; exact hJmid (res, fnd, ()) m5 ⟨rfl, sc0, hspc0, hclc0, hcvc0, hfuc0, hm5⟩
          ft_steps
          let sc0d := { sc0 with scratch := { sc0.scratch with
            delayed_len := (BitVec.ofNat 64 sc0.scratch.delayed_len + 1#64).toNat } }
          have hspc0d : FullSparseInv c F0 sc0d :=
            fullSparseInv_with_delayed_len hspc0 _
          obtain ⟨F_c0d, hw0d⟩ := hspc0d.1.witness
          ft_call h_propagate
          refine ⟨c, F0, F_c0d, sc0d, R, rfl, hspc0d.1.lengths, hw0d, hspc0d.2.2.2.2,
            (by assumption),
            fun p0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fuel0 _ _ _ _ _ _ _ _ m6 hlen6 hw6 _
              hperm6 hfu6 _ _ hp0 _ _ hm6 => ?_⟩
          have hspp0 := fullPropagate_sparse hspc0d rfl hlen6 hw6 hperm6
          have hfup0 : fuel0.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfu6 hfuc0
          ft_split
          · ft_steps
            exact hBv (20#64, fnd + 1#64, v, ()) m6 ⟨_, hspp0, hclc0, hcvc0, hfup0, Or.inr rfl,
              fun _ => level0_unsat_of_conflict_okW hw6 hclc0 (hp0 ‹_›).2.2, hm6⟩
          ft_split
          · ft_steps
            exact hBv (res, fnd + 1#64, v, ()) m6 ⟨_, hspp0, hclc0, hcvc0, hfup0, hresr,
              hunsr, hm6⟩
          · ft_steps
            exact hJmid (res, fnd + 1#64, ()) m6 ⟨rfl, _, hspp0, hclc0, hcvc0, hfup0, hm6⟩
        intro Jcl0 hJcl0
        have hv_fl0 : v.toNat < sb0.core.flags.length := by
          rw [hspb0.1.lengths.core_ok.flags_len]; have := hspb0.1.lengths.core_ok.cur_vars_le; omega
        ft_split
        · ft_steps
          exact hJcl0 () _ ⟨_, fullSparseInv_clear_fl_trans hspb0, hclb0, hcvb0', hfub0',
            by assumption⟩
        · ft_steps; exact hJcl0 () m4 ⟨sb0, hspb0, hclb0, hcvb0', hfub0', hm4⟩
      · intro _ Lv _ hLv; ft_steps
        exact hLv s1.core.cur_vars (0#64, 0#64, ()) mr ⟨sr, Nat.zero_le _, rfl, hspr, hclr, hcvr,
          hfur, hmr⟩
    · intro _ Lout _ hLout; ft_steps
      exact hLout 4 (1#64, 0#64, ()) _ ⟨_, Nat.zero_le _, rfl,
        fullSparseInv_with_ant_sz hsp2 tick_lim, hcl2, hcv2, hfu2s, Or.inl rfl,
        fun h => absurd h (by decide), by assumption⟩
  -- Initial `if (h->cur_level != 0) full_backtrack(h, 0)`
  · intro Jbt hJbt; have hlen := hsp.1.lengths; obtain ⟨F_cur, hw⟩ := hsp.1.witness
    have hcl_lt : s.core.cur_level < 2 ^ 64 := by
      have := hw.cur_level_le; have := (bb_bnds hlen.core_ok).2.2.2; omega
    ft_split
    · ft_call h_backtrack
      have htl0 : ((Arg.imm 0).val : Val i64).toNat = 0 := by decide
      refine ⟨c, s, R, rfl, hlen, hcl_lt, (fun hpos => by
          have := hlen.core_ok.cur_vars_le; have := hw.cur_level_le
          have := hlen.core_ok.trail_end_le; rw [htl0] at hpos ⊢; omega), hw.trail_lits_lt, hm,
        fun _ _ _ _ _ _ _ _ _ _ _ hlen1 _ _ hcl1 hpr1 _ _ _ hw1 _ hm1 => hJbt () _ ⟨_,
          fullBacktrack_sparse hsp rfl hlen1 hpr1 hw1, by simp [hcl1], Nat.le_refl _, hm1⟩⟩
    · ft_steps
      have hcl0' : s.core.cur_level = 0 := by
        simpa [Nat.mod_eq_of_lt hcl_lt] using
          congrArg BitVec.toNat (‹BitVec.ofNat 64 s.core.cur_level = 0#64›)
      exact hJbt () m ⟨s, hsp, hcl0', Nat.le_refl _, hm⟩

end BackboneProofs

end LeanQbe.T.Examples.Kissat.FullM3Backbone
