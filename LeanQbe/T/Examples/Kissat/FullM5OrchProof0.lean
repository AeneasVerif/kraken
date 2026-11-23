module

public import LeanQbe.T.Examples.Kissat.FullM5Orch
public import LeanQbe.T.Examples.Kissat.FullSpec
public import LeanQbe.T.Examples.Kissat.FullFastSchedLemmas
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas1
public import LeanQbe.T.Examples.Kissat.FullDefSweepLemmas1
public import LeanQbe.T.Examples.Kissat.FullM4SweepSpec
public import LeanQbe.T.Examples.Kissat.FullM4VivBceProof1
public import LeanQbe.T.Examples.Kissat.FullM3BackboneLemmas1
import LeanQbe.T.Examples.Kissat.FullParseInitLemmas1
import LeanQbe.T.Examples.Kissat.FullParseInitLemmas2
import LeanQbe.T.Examples.Kissat.FullTransLemmas1
import LeanQbe.T.Examples.Kissat.FullTransLemmas
import LeanQbe.T.Examples.Kissat.FullVivTopLemmas1
import LeanQbe.T.Examples.Kissat.FullM4SweepLemmas1
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat `D-Full` M5 Orchestration Proofs — Part 0 (`FullM5OrchProof0`, `11/19` Functions)

Proves parametric `(Γ : Env)` `Func.wp` UNSAT-only theorems (`XPost := False`, zero SAT/model
proofs, `M1`-clean `.olean` with zero `@[expose]` and zero `import all`) for the `11`
cap/init/effort/budget/tail functions in `FullM5Orch`:
1. `full_calc_ext_cap_m5_wp` (`4M`), `full_calc_scr_cap_m5_wp` (`1M`), `full_init_state_m5_wp`
   (against `Full.fullInitStateSpec`, wiring both `[38]` & `[39]`).
2. `full_probe_dticks_m5_wp`, `full_elim_dticks_m5_wp` (`10M` `mineffort` floor, canonical specs).
3. `full_trans_lit_m5_wp` (`dst > src` + `ant_sz` inside BFS) & `full_transitive_m5_wp`
   (against canonical `Full.fullTransLitSpec` & `FullFastBveBudgets.fullTransitiveFastSpec`).
4. `full_vivify_tier_m5_wp`, `full_vivify_m5_wp` (`0xFFFFFFFFULL`, rolling 3:3:1:3 cumulative
   `tick_cap`, 100% tier 0 when `num_redundant == 0`, delegating to `FullM4VivBce`).
5. `full_sweep_dense_m5_wp` (lifted `16384` clamp, canonical `FullDefSweep.fullSweepDenseSpec`).
6. `full_probe_tail_m5_wp` (canonical `FullFastSched.schedProbeTailSpec`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM5Orch

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. Caps (`4M` / `1M`) & `full_init_state_m5` -/

/-- Relational specification matching `Full.fullCalcExtCapSpec` with `4194304` (`4M`) cap. -/
def fullCalcExtCapM5Spec : Spec [i64] [i64] := fun (rem, ()) m Q _ =>
  ∀ r : BitVec 64,
    r.toNat ≤ 4194304 → (rem.toNat < 8192 → r = 0#64) → 4 * r.toNat ≤ rem.toNat / 8 →
    Q (r, ()) m

theorem fullCalcExtCapM5Spec_noExit : ∀ a m Q X,
    fullCalcExtCapM5Spec a m Q X → fullCalcExtCapM5Spec a m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

/-- Relational specification matching `Full.fullCalcScrCapSpec` with `1048576` (`1M`) cap. -/
def fullCalcScrCapM5Spec : Spec [i64] [i64] := fun (rem, ()) m Q _ =>
  ∀ r : BitVec 64,
    r.toNat ≤ 1048576 → (rem.toNat < 8192 → r = 0#64) → 4 * r.toNat ≤ rem.toNat / 4 →
    Q (r, ()) m

theorem fullCalcScrCapM5Spec_noExit : ∀ a m Q X,
    fullCalcScrCapM5Spec a m Q X → fullCalcScrCapM5Spec a m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

section CapsAndInitProofs

open Full.FullParseInitSpecs
open Full.FullParseInitHelpers
open scoped Full.FullParseInitTactics

private def fullCalcExtCapM5 (rem : Nat) : Nat :=
  if rem < 8192 then 0 else ((min (rem / 32) 4194304) / 2) * 2

private def fullCalcScrCapM5 (rem : Nat) : Nat :=
  if rem < 8192 then 0 else
    let c := if 16384 ≤ rem then rem / 16 else rem / 32
    ((min c 1048576) / 2) * 2

private theorem fullCalcExtCapM5_le (rem : Nat) : fullCalcExtCapM5 rem ≤ 4194304 := by
  unfold fullCalcExtCapM5; split <;> omega

private theorem fullCalcExtCapM5_four_mul_le (rem : Nat) :
    4 * fullCalcExtCapM5 rem ≤ rem / 8 := by
  unfold fullCalcExtCapM5; split <;> omega

private theorem fullCalcScrCapM5_le (rem : Nat) : fullCalcScrCapM5 rem ≤ 1048576 := by
  unfold fullCalcScrCapM5; split; omega; dsimp only; split <;> omega

private theorem fullCalcScrCapM5_four_mul_le (rem : Nat) :
    4 * fullCalcScrCapM5 rem ≤ rem / 4 := by
  unfold fullCalcScrCapM5; split; omega; dsimp only; split <;> omega

private theorem m5_bv64_ule_nat {a b : BitVec 64} : a.ule b = decide (a.toNat ≤ b.toNat) := by
  simp [BitVec.ule]

private theorem m5_bv64_ult_nat {a b : BitVec 64} : a.ult b = decide (a.toNat < b.toNat) := by
  simp [BitVec.ult]

private theorem m5_fp_shr4 (x : BitVec 64) :
    x >>> (((4 : BitVec 32).signExtend 64).toNat % 64) = BitVec.ofNat 64 (x.toNat / 16) := by
  have h := fp_shr_sext4 x.isLt; rwa [bv_ofNat_toNat_eq x] at h

private theorem m5_fp_shr5 (x : BitVec 64) :
    x >>> (((5 : BitVec 32).signExtend 64).toNat % 64) = BitVec.ofNat 64 (x.toNat / 32) := by
  have h := fp_shr_sext5 x.isLt; rwa [bv_ofNat_toNat_eq x] at h

local macro "m5_fp_jnz_t" h:ident : tactic => `(tactic|
  (dsimp only [Arg.val_var] at $h:ident; rw [decide_eq_true_eq] at $h:ident; fp_head_steps))
local macro "m5_fp_jnz_f" h:ident : tactic => `(tactic|
  (dsimp only [Arg.val_var] at $h:ident; rw [decide_eq_false_iff_not] at $h:ident; fp_head_steps))
local macro "m5_fp_jnz_t'" h:ident : tactic => `(tactic|
  (simp only [Arg.val_var, i64, Ty.hasFloat, liftCmp, CmpOp.evalBits, evalBits_ult_eq,
     evalBits_ule_eq, evalBits_ugt_eq, evalBits_uge_eq] at $h:ident
   have $h:ident := of_decide_eq_true $h:ident
   fp_head_steps))
local macro "m5_fp_jnz_f'" h:ident : tactic => `(tactic|
  (simp only [Arg.val_var, i64, Ty.hasFloat, liftCmp, CmpOp.evalBits, evalBits_ult_eq,
     evalBits_ule_eq, evalBits_ugt_eq, evalBits_uge_eq] at $h:ident
   have $h:ident := of_decide_eq_false $h:ident
   fp_head_steps))

/-- Parametric `Func.wp` theorem for `full_calc_ext_cap_m5` (`4M` cap). -/
theorem full_calc_ext_cap_m5_wp (Γ : Env) :
    ∀ a m Q X, fullCalcExtCapM5Spec a m Q X → Func.wp Γ full_calc_ext_cap_m5_body a m Q X := by
  rintro ⟨rem, ⟨⟩⟩ m Q X hQ
  have hle := fullCalcExtCapM5_le rem.toNat
  have h4 := fullCalcExtCapM5_four_mul_le rem.toNat
  have hQ' := hQ (BitVec.ofNat 64 (fullCalcExtCapM5 rem.toNat))
    (by rw [bv64_ofNat_toNat (by omega)]; exact hle)
    (fun hlt => by unfold fullCalcExtCapM5; simp [hlt])
    (by rw [bv64_ofNat_toNat (by omega)]; exact h4)
  unfold Func.wp full_calc_ext_cap_m5_body; fp_head_steps
  rw [m5_bv64_ult_nat, show (8192 : BitVec 64).toNat = 8192 from rfl]
  refine wp_jnz_of (fun hlt => ?_) (fun hge => ?_)
  · m5_fp_jnz_t hlt
    have heq : fullCalcExtCapM5 rem.toNat = 0 := by unfold fullCalcExtCapM5; simp [hlt]
    rw [heq] at hQ'; exact hQ'
  · m5_fp_jnz_f hge; fp_head_steps; rw [m5_fp_shr5 rem]
    refine wp_join_group (fun (v : Tup Val [i64]) mc =>
        v.1 = BitVec.ofNat 64 (min (rem.toNat / 32) 4194304) ∧ mc = m) ?_ ?_
    · rintro _ ⟨cv, ⟨⟩⟩ mc ⟨rfl, rfl⟩; simp only [Blocks.get_here]; fp_head_steps
      rw [fp_and_not1, bv64_ofNat_toNat (by omega)]
      have heq : fullCalcExtCapM5 rem.toNat = (min (rem.toNat / 32) 4194304 / 2) * 2 := by
        unfold fullCalcExtCapM5; simp [hge]
      rw [heq] at hQ'; exact hQ'
    · intro J hJ; fp_head_steps
      rw [show (4194304 : BitVec 64) = BitVec.ofNat 64 4194304 from rfl,
        bv_ult_eq (by decide) (by have := rem.isLt; omega)]
      refine wp_jnz_of (fun hgt => ?_) (fun hle2 => ?_)
      · m5_fp_jnz_t hgt; refine hJ (_, ()) m ⟨?_, rfl⟩; rw [Nat.min_eq_right (by omega)]
      · m5_fp_jnz_f hle2; refine hJ (_, ()) m ⟨?_, rfl⟩; rw [Nat.min_eq_left (by omega)]

/-- Parametric `Func.wp` theorem for `full_calc_scr_cap_m5` (`1M` cap). -/
theorem full_calc_scr_cap_m5_wp (Γ : Env) :
    ∀ a m Q X, fullCalcScrCapM5Spec a m Q X → Func.wp Γ full_calc_scr_cap_m5_body a m Q X := by
  rintro ⟨rem, ⟨⟩⟩ m Q X hQ
  have hle := fullCalcScrCapM5_le rem.toNat
  have h4 := fullCalcScrCapM5_four_mul_le rem.toNat
  have hQ' := hQ (BitVec.ofNat 64 (fullCalcScrCapM5 rem.toNat))
    (by rw [bv64_ofNat_toNat (by omega)]; exact hle)
    (fun hlt => by unfold fullCalcScrCapM5; simp [hlt])
    (by rw [bv64_ofNat_toNat (by omega)]; exact h4)
  unfold Func.wp full_calc_scr_cap_m5_body; fp_head_steps
  rw [m5_bv64_ult_nat, show (8192 : BitVec 64).toNat = 8192 from rfl]
  refine wp_jnz_of (fun hlt => ?_) (fun hge => ?_)
  · m5_fp_jnz_t hlt
    have heq : fullCalcScrCapM5 rem.toNat = 0 := by unfold fullCalcScrCapM5; simp [hlt]
    rw [heq] at hQ'; exact hQ'
  · m5_fp_jnz_f hge
    refine wp_join_group (fun (v : Tup Val [i64]) mc0 =>
      v.1 = BitVec.ofNat 64 (if 16384 ≤ rem.toNat then rem.toNat / 16 else rem.toNat / 32) ∧
        mc0 = m) ?_ ?_
    · rintro _ ⟨c0, ⟨⟩⟩ mc0 ⟨rfl, rfl⟩; simp only [Blocks.get_here]; fp_head_steps
      let raw := if 16384 ≤ rem.toNat then rem.toNat / 16 else rem.toNat / 32
      have hraw64 : raw < 2 ^ 64 := by dsimp [raw]; have := rem.isLt; split <;> omega
      refine wp_join_group
        (fun (v : Tup Val [i64]) mc1 => v.1 = BitVec.ofNat 64 (min raw 1048576) ∧ mc1 = mc0)
        ?_ ?_
      · rintro _ ⟨c1, ⟨⟩⟩ mc1 ⟨rfl, rfl⟩; simp only [Blocks.get_here]; fp_head_steps
        rw [fp_and_not1, bv64_ofNat_toNat (by omega)]
        have heq : fullCalcScrCapM5 rem.toNat = (min raw 1048576 / 2) * 2 := by
          unfold fullCalcScrCapM5; simp [hge, raw]
        rw [heq] at hQ'; exact hQ'
      · intro J1 hJ1; fp_head_steps
        rw [show (1048576 : BitVec 64) = BitVec.ofNat 64 1048576 from rfl,
          bv_ult_eq (by decide) hraw64]
        refine wp_jnz_of (fun hgt => ?_) (fun hle2 => ?_)
        · m5_fp_jnz_t hgt; refine hJ1 (_, ()) mc0 ⟨?_, rfl⟩; rw [Nat.min_eq_right (by omega)]
        · m5_fp_jnz_f hle2; refine hJ1 (_, ()) mc0 ⟨?_, rfl⟩; rw [Nat.min_eq_left (by omega)]
    · intro J0 hJ0; fp_head_steps
      rw [show (16384 : BitVec 64).ule rem = decide (16384 ≤ rem.toNat) from by
        rw [m5_bv64_ule_nat]; rfl]
      refine wp_jnz_of (fun hge2 => ?_) (fun hlt2 => ?_)
      · m5_fp_jnz_t hge2; rw [m5_fp_shr4 rem]; exact hJ0 (_, ()) m ⟨by simp [hge2], rfl⟩
      · m5_fp_jnz_f hlt2; rw [m5_fp_shr5 rem]; exact hJ0 (_, ()) m ⟨by simp [hlt2], rfl⟩

private theorem m5_init_caps_bridge {rem nc : Nat} {ecap_v scap_v : BitVec 64}
    (hrem_fit : nc * 40 + 136 ≤ rem)
    (hecap_le : ecap_v.toNat ≤ 4194304) (_hecap_4 : 4 * ecap_v.toNat ≤ rem / 8)
    (hscap_le : scap_v.toNat ≤ 1048576) (_hscap_4 : 4 * scap_v.toNat ≤ rem / 4) :
    let del_cap := fullInitDelCap rem
    del_cap < dimacsBound ∧ ecap_v.toNat < dimacsBound ∧ scap_v.toNat < dimacsBound ∧
    (rem < 12 * del_cap + 4 * ecap_v.toNat + 4 * scap_v.toNat + nc * 40 + 136 →
      12 * del_cap + 40 ≤ rem) ∧
    (¬ rem < 12 * del_cap + 4 * ecap_v.toNat + 4 * scap_v.toNat + nc * 40 + 136 →
      12 * del_cap + 4 * ecap_v.toNat + 4 * scap_v.toNat + 40 ≤ rem) := by
  refine ⟨fullInitDelCap_lt, by unfold dimacsBound; omega, by unfold dimacsBound; omega,
    fun hlt => ?_, fun hge => ?_⟩
  · by_cases hbig : 524288 ≤ rem <;> simp [fullInitDelCap, hbig] <;> omega
  · omega

private structure M5InitArrs (c : FullCfg) where
  (vals lit_mark mrk walk_vals phases phases_target phases_best walk_best : List (BitVec 8))
  (flags lvl rsns trl trail_pos tmp min_clr frame_trail frame_dec wvec repr min_stk :
    List (BitVec 32))
  (arena wstk heap pos shrink_stk q_prev q_next q_stamp : List (BitVec 32))
  (wsort work_stk1 work_stk2 tarjan_mark tarjan_reach : List (BitVec 32))
  (score sim_sig : List (BitVec 64))
  (glue_used last_learned delayed red_refs extend_stk scratch_buf : List (BitVec 32))
  ok : vals.length = 2 * c.max_vars ∧ lit_mark.length = 2 * c.max_vars ∧
    mrk.length = c.max_vars ∧ walk_vals.length = 2 * c.max_vars ∧
    phases.length = c.max_vars ∧ phases_target.length = c.max_vars ∧
    phases_best.length = c.max_vars ∧ walk_best.length = c.max_vars ∧
    flags.length = c.max_vars ∧ lvl.length = c.max_vars ∧ rsns.length = c.max_vars ∧
    trl.length = c.max_vars ∧ trail_pos.length = c.max_vars ∧ tmp.length = c.max_vars ∧
    min_clr.length = c.max_vars ∧ frame_trail.length = c.max_vars + 1 ∧
    frame_dec.length = c.max_vars + 1 ∧ wvec.length = 4 * c.max_vars ∧
    repr.length = 2 * c.max_vars ∧ min_stk.length = 2 * c.minDepth ∧
    arena.length = c.arena_cap ∧ wstk.length = c.wcap ∧ heap.length = c.max_vars ∧
    pos.length = c.max_vars ∧ shrink_stk.length = c.max_vars ∧ q_prev.length = c.max_vars ∧
    q_next.length = c.max_vars ∧ q_stamp.length = c.max_vars ∧ wsort.length = 2 * c.max_vars ∧
    work_stk1.length = 2 * c.max_vars ∧ work_stk2.length = 2 * c.max_vars ∧
    tarjan_mark.length = 2 * c.max_vars ∧ tarjan_reach.length = 2 * c.max_vars ∧
    score.length = c.max_vars ∧ sim_sig.length = c.max_vars ∧ glue_used.length = 64 ∧
    last_learned.length = 16 ∧ delayed.length = 3 * c.delayed_cap ∧
    red_refs.length = c.red_cap ∧ extend_stk.length = c.extend_cap ∧
    scratch_buf.length = c.scratch_cap

private def m5InitFullState (c : FullCfg) (d_cur d_val fuel : BitVec 64) (a : M5InitArrs c) :
    FullState :=
  { core :=
      { d_cur := d_cur, d_val := d_val, cur_vars := c.mv,
        unassigned := BitVec.ofNat 64 c.mv, arena_len := 0, wlen := 1, wusable := 0#64,
        arena_garbage := 0#64, first_reducible := 0xFFFFFFFF#64, num_irred := 0#64,
        num_redundant := 0#64, num_binary := 0#64, unflushed := 0#64, probing := 0#64,
        trail_end := 0, propagated := 0, cur_level := 0, fuel := fuel,
        confl_ref := 0xFFFFFFFF#64, confl_type := 0#64, confl_lit0 := 0#64,
        confl_lit1 := 0#64, tmp_cnt := 0, tmp_len := 0, min_clr_len := 0,
        min_clr_full := 0#64, oom := 0#64, dense_mode := 0#64, inconsistent := 0#64,
        vals := a.vals, lit_mark := a.lit_mark, mrk := a.mrk, flags := a.flags, lvl := a.lvl,
        rsns := a.rsns, trl := a.trl, trail_pos := a.trail_pos, tmp := a.tmp,
        min_clr := a.min_clr, frame_trail := a.frame_trail, frame_dec := a.frame_dec,
        wvec := a.wvec, repr := a.repr, min_stk := a.min_stk, arena := a.arena, wstk := a.wstk }
    scratch :=
      { heap_len := c.mv, scinc := 1#64 <<< 28, rel_period := 1024#64,
        rel_limit := 1048576#64, rel_wait := 1024#64, rel_u := 1#64, rel_v := 1#64,
        rel_trigger := 0#64, conflicts := 0#64, learned_lits := 0#64, min_removed := 0#64,
        delayed_len := 0, stable := 0#64, switched := 0#64, mode_count := 0#64,
        mode_confl_lim := 1000#64, mode_tick_lim := 0#64, mode_saved_ticks := 0#64,
        search_ticks := 0#64,
        q_first := if c.mv = 0 then 0xFFFFFFFF#64 else 0#64,
        q_last := if c.mv = 0 then 0xFFFFFFFF#64 else BitVec.ofNat 64 (c.mv - 1),
        q_search_idx := if c.mv = 0 then 0xFFFFFFFF#64 else BitVec.ofNat 64 (c.mv - 1),
        q_search_stamp := BitVec.ofNat 64 c.mv, q_cur_stamp := BitVec.ofNat 64 c.mv,
        target_assigned := 0#64, best_assigned := 0#64, rephase_limit := 1000#64,
        rephased := 0#64, reduce_limit := 1000#64, reductions := 0#64, tier1 := 2#64,
        tier2 := 6#64, restarts := 0#64, restart_limit := 1#64, ema_fast_biased := 0#64,
        ema_fast_exp := 1#64 <<< 24, ema_slow_biased := 0#64, ema_slow_exp := 1#64 <<< 24,
        extend_len := 0, rng_state := 0x9E3779B97F4A7C15#64 ^^^ (BitVec.ofNat 64 c.mv + 1#64),
        chrono_levels := 100#64, otfs_cnt := 0#64, eager_sub_cnt := 0#64, probe_limit := 500#64,
        probings := 0#64, elim_limit := 1500#64, eliminations := 0#64, elim_bound := 0#64,
        iterating := 0#64, hbr_cnt := 0#64, trans_cnt := 0#64, viv_cnt := 0#64,
        subst_cnt := 0#64, cong_cnt := 0#64, sweep_cnt := 0#64, bve_cnt := 0#64,
        bce_cnt := 0#64, bva_cnt := 0#64, walk_cnt_stat := 0#64, fwd_sub_cnt := 0#64,
        fwd_str_cnt := 0#64, ant_sz := 0#64, res_sz := 0#64, walk_vals := a.walk_vals,
        phases := a.phases, phases_target := a.phases_target, phases_best := a.phases_best,
        walk_best := a.walk_best, heap := a.heap, pos := a.pos, shrink_stk := a.shrink_stk,
        q_prev := a.q_prev, q_next := a.q_next, q_stamp := a.q_stamp, wsort := a.wsort,
        work_stk1 := a.work_stk1, work_stk2 := a.work_stk2, tarjan_mark := a.tarjan_mark,
        tarjan_reach := a.tarjan_reach, score := a.score, sim_sig := a.sim_sig,
        glue_used := a.glue_used, last_learned := a.last_learned, delayed := a.delayed,
        red_refs := a.red_refs, extend_stk := a.extend_stk, scratch_buf := a.scratch_buf } }

private theorem m5_peel_bytes_block (c : FullCfg) {m : Mem 64}
    (hm : region (c.hdr + BitVec.ofNat 64 1152) (c.avail - 1152) m) :
    ∃ vals wvals lmrk mrk ph ptgt pbst wbst : List (BitVec 8),
      vals.length = 2 * c.max_vars ∧ wvals.length = 2 * c.max_vars ∧
      lmrk.length = 2 * c.max_vars ∧ mrk.length = c.max_vars ∧ ph.length = c.max_vars ∧
      ptgt.length = c.max_vars ∧ pbst.length = c.max_vars ∧ wbst.length = c.max_vars ∧
      ((((array (t := i8) c.pVals vals ⋆ array (t := i8) c.pLitMark lmrk ⋆
          array (t := i8) c.pMark mrk) ⋆
         (array (t := i8) c.pWalkVals wvals ⋆ array (t := i8) c.pPhases ph ⋆
          array (t := i8) c.pPhasesTarget ptgt ⋆ array (t := i8) c.pPhasesBest pbst ⋆
          array (t := i8) c.pWalkBest wbst)) ⋆ c.padBytes) ⋆
        region c.pFlags (c.avail - (1152 + 3 * valsBytes c.max_vars +
          5 * markBytes c.max_vars))) m := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hfit := c.havail_fit; have hsz := c.hsize; have hfx := fullFixedBytes_lt c.hmaxv
  have hv := valsBytes_ge c.max_vars; have hmk := markBytes_ge c.max_vars
  have hfb : fullFixedBytes c.max_vars = 1472 + 3 * valsBytes c.max_vars +
      5 * markBytes c.max_vars + 15 * u32FullBytes c.max_vars + 80 * c.max_vars +
      8 * c.minDepth := rfl
  have hle : fullFixedBytes c.max_vars ≤ c.avail := by omega
  have h0 : ((emp ⋆ emp) ⋆ region c.pVals (c.avail - 1152)) m := by
    rw [emp_sep, emp_sep]; exact hm
  let vb := valsBytes c.max_vars; let mb := markBytes c.max_vars
  let rem1 := c.avail - 1152 - vb
  obtain ⟨vals, hv1, h1⟩ := peel_step_i8 (b := c.pWalkVals) (2 * c.max_vars) vb rem1
    (c.avail - 1152) h0 (by rfl) (by omega) hv (by omega)
  obtain ⟨wvals, hv2, h2⟩ := peel_step_i8 (b := c.pLitMark) (2 * c.max_vars) vb (rem1 - vb)
    rem1 h1 (by rfl) (by omega) hv (by omega)
  obtain ⟨lmrk, hv3, h3⟩ := peel_step_i8 (b := c.pMark) (2 * c.max_vars) vb (rem1 - 2 * vb)
    (rem1 - vb) h2 (by rfl) (by omega) hv (by omega)
  obtain ⟨mrk, hm1, h4⟩ := peel_step_i8 (b := c.pPhases) c.max_vars mb
    (rem1 - 2 * vb - mb) (rem1 - 2 * vb) h3 (by rfl) (by omega) hmk (by omega)
  obtain ⟨ph, hm2, h5⟩ := peel_step_i8 (b := c.pPhasesTarget) c.max_vars mb
    (rem1 - 2 * vb - 2 * mb) (rem1 - 2 * vb - mb) h4 (by rfl) (by omega) hmk (by omega)
  obtain ⟨ptgt, hm3, h6⟩ := peel_step_i8 (b := c.pPhasesBest) c.max_vars mb
    (rem1 - 2 * vb - 3 * mb) (rem1 - 2 * vb - 2 * mb) h5 (by rfl) (by omega) hmk (by omega)
  obtain ⟨pbst, hm4, h7⟩ := peel_step_i8 (b := c.pWalkBest) c.max_vars mb
    (rem1 - 2 * vb - 4 * mb) (rem1 - 2 * vb - 3 * mb) h6 (by rfl) (by omega) hmk (by omega)
  obtain ⟨wbst, hm5, h8⟩ := peel_step_i8 (b := c.pFlags) c.max_vars mb
    (c.avail - (1152 + 3 * vb + 5 * mb)) (rem1 - 2 * vb - 4 * mb) h7
    (by rfl) (by omega) hmk (by omega)
  simp only [emp_sep] at h8
  refine ⟨vals, wvals, lmrk, mrk, ph, ptgt, pbst, wbst,
    hv1, hv2, hv3, hm1, hm2, hm3, hm4, hm5, ?_⟩
  unfold FullCfg.padBytes; dsimp only [vb, mb] at h8
  exact sep_mono2 (sep_mono2 (fun _ h => sep_ac h)
    (fun _ h => by simp only [sep_assoc] at h ⊢; exact h)) (fun _ h => h) m h8

private theorem m5_peel_u32_5_block (max_v : Nat) (k1 k2 k3 k4 k5 : Nat)
    (a1 a2 a3 a4 a5 b : BitVec 64) {rtot rnext : Nat} {m : Mem 64}
    (ha2 : a2 = a1 + BitVec.ofNat 64 (u32FullBytes max_v))
    (ha3 : a3 = a2 + BitVec.ofNat 64 (u32FullBytes max_v))
    (ha4 : a4 = a3 + BitVec.ofNat 64 (u32FullBytes max_v))
    (ha5 : a5 = a4 + BitVec.ofNat 64 (u32FullBytes max_v))
    (hb : b = a5 + BitVec.ofNat 64 (u32FullBytes max_v))
    (hm : region a1 rtot m)
    (hk1 : 4 * k1 ≤ u32FullBytes max_v := by omega)
    (hk2 : 4 * k2 ≤ u32FullBytes max_v := by omega)
    (hk3 : 4 * k3 ≤ u32FullBytes max_v := by omega)
    (hk4 : 4 * k4 ≤ u32FullBytes max_v := by omega)
    (hk5 : 4 * k5 ≤ u32FullBytes max_v := by omega)
    (hrem : 5 * u32FullBytes max_v + rnext = rtot := by omega)
    (hle : rtot ≤ 2 ^ 64 := by omega) :
    ∃ x1 x2 x3 x4 x5 : List (BitVec 32),
      x1.length = k1 ∧ x2.length = k2 ∧ x3.length = k3 ∧ x4.length = k4 ∧ x5.length = k5 ∧
      ((array (t := i32) a1 x1 ⋆ array (t := i32) a2 x2 ⋆ array (t := i32) a3 x3 ⋆
        array (t := i32) a4 x4 ⋆ array (t := i32) a5 x5) ⋆
       (region (a1 + BitVec.ofNat 64 (4 * k1)) (u32FullBytes max_v - 4 * k1) ⋆
        region (a2 + BitVec.ofNat 64 (4 * k2)) (u32FullBytes max_v - 4 * k2) ⋆
        region (a3 + BitVec.ofNat 64 (4 * k3)) (u32FullBytes max_v - 4 * k3) ⋆
        region (a4 + BitVec.ofNat 64 (4 * k4)) (u32FullBytes max_v - 4 * k4) ⋆
        region (a5 + BitVec.ofNat 64 (4 * k5)) (u32FullBytes max_v - 4 * k5)) ⋆
       region b rnext) m := by
  let ub := u32FullBytes max_v
  have h0 : ((emp ⋆ emp) ⋆ region a1 rtot) m := by rw [emp_sep, emp_sep]; exact hm
  obtain ⟨x1, hx1, h1⟩ := peel_step_i32 (b := a2) k1 ub (4 * ub + rnext) rtot h0
    ha2.symm (by omega) hk1 (by omega)
  obtain ⟨x2, hx2, h2⟩ := peel_step_i32 (b := a3) k2 ub (3 * ub + rnext) (4 * ub + rnext) h1
    ha3.symm (by omega) hk2 (by omega)
  obtain ⟨x3, hx3, h3⟩ := peel_step_i32 (b := a4) k3 ub (2 * ub + rnext) (3 * ub + rnext) h2
    ha4.symm (by omega) hk3 (by omega)
  obtain ⟨x4, hx4, h4⟩ := peel_step_i32 (b := a5) k4 ub (ub + rnext) (2 * ub + rnext) h3
    ha5.symm (by omega) hk4 (by omega)
  obtain ⟨x5, hx5, h5⟩ := peel_step_i32 (b := b) k5 ub rnext (ub + rnext) h4
    hb.symm (by omega) hk5 (by omega)
  simp only [emp_sep] at h5; exact ⟨x1, x2, x3, x4, x5, hx1, hx2, hx3, hx4, hx5, sep_ac h5⟩

private theorem m5_peel_tail_block (c : FullCfg) {m : Mem 64}
    (hm : region c.pWvec (c.avail - (1152 + 3 * valsBytes c.max_vars +
      5 * markBytes c.max_vars + 15 * u32FullBytes c.max_vars)) m) :
    ∃ (wvec repr wsort ws1 ws2 tmk trc : List (BitVec 32))
      (sc sig : List (BitVec 64))
      (mstk gu ll ar wstk del red ext sbuf : List (BitVec 32)),
      (wvec.length = 4 * c.max_vars ∧ repr.length = 2 * c.max_vars ∧
        wsort.length = 2 * c.max_vars ∧ ws1.length = 2 * c.max_vars ∧
        ws2.length = 2 * c.max_vars ∧ tmk.length = 2 * c.max_vars ∧
        trc.length = 2 * c.max_vars ∧ sc.length = c.max_vars ∧
        sig.length = c.max_vars ∧ mstk.length = 2 * c.minDepth ∧
        gu.length = 64 ∧ ll.length = 16 ∧ ar.length = c.arena_cap ∧
        wstk.length = c.wcap ∧ del.length = 3 * c.delayed_cap ∧
        red.length = c.red_cap ∧ ext.length = c.extend_cap ∧ sbuf.length = c.scratch_cap) ∧
      ((array (t := i32) c.pWvec wvec ⋆ array (t := i32) c.pRepr repr ⋆
        array (t := i32) c.pMinStk mstk ⋆
        array (t := i32) c.pArena ar ⋆ array (t := i32) c.pWstk wstk) ⋆
       ((array (t := i32) c.pWsort wsort ⋆ array (t := i32) c.pWorkStk1 ws1 ⋆
          array (t := i32) c.pWorkStk2 ws2 ⋆ array (t := i32) c.pTarjanMark tmk ⋆
          array (t := i32) c.pTarjanReach trc) ⋆
        (array64 c.pScore sc ⋆ array64 c.pSimSig sig ⋆
          array (t := i32) c.pGlueUsed gu ⋆ array (t := i32) c.pLastLearned ll) ⋆
        (array (t := i32) c.pDelayed del ⋆ array (t := i32) c.pRedRefs red ⋆
          array (t := i32) c.pExtendStk ext ⋆ array (t := i32) c.pScratchBuf sbuf)) ⋆
       region c.pSlack c.slack) m := by
  have hmx := c.hmaxv; have ha := c.harena; have hw := c.hwcap; have hd := c.hdel
  have hr := c.hred; have he := c.hext; have hs := c.hscr
  unfold dimacsBound at hmx ha hw hd hr he hs
  have hfit := c.havail_fit; have hsz := c.hsize; have hmd := fullMinDepthOf_le c.max_vars
  have hfb : fullFixedBytes c.max_vars = 1472 + 3 * valsBytes c.max_vars +
      5 * markBytes c.max_vars + 15 * u32FullBytes c.max_vars + 80 * c.max_vars +
      8 * c.minDepth := rfl
  have hslk : c.slack = c.avail - (fullFixedBytes c.max_vars + 4 * c.arena_cap + 4 * c.wcap +
      12 * c.delayed_cap + 4 * c.red_cap + 4 * c.extend_cap + 4 * c.scratch_cap) := rfl
  let r0 := c.avail - (1152 + 3 * valsBytes c.max_vars + 5 * markBytes c.max_vars +
    15 * u32FullBytes c.max_vars)
  have h0 : (emp ⋆ region c.pWvec r0) m := by rw [emp_sep]; exact hm
  obtain ⟨wvec, l1, h1⟩ := peel_step_exact_i32 (b := c.pRepr) (4 * c.max_vars)
    (r0 - 16 * c.max_vars) r0 h0 (show c.pWvec + BitVec.ofNat 64 (4 * (4 * c.max_vars)) = c.pRepr
      by unfold FullCfg.pRepr; rw [show 4 * (4 * c.max_vars) = 16 * c.max_vars by omega])
    (by omega) (by omega)
  obtain ⟨repr, l2, h2⟩ := peel_step_exact_i32 (b := c.pWsort) (2 * c.max_vars)
    (r0 - 24 * c.max_vars) (r0 - 16 * c.max_vars) h1
    (show c.pRepr + BitVec.ofNat 64 (4 * (2 * c.max_vars)) = c.pWsort by
      unfold FullCfg.pWsort; rw [show 4 * (2 * c.max_vars) = 8 * c.max_vars by omega])
    (by omega) (by omega)
  obtain ⟨wsort, l3, h3⟩ := peel_step_exact_i32 (b := c.pWorkStk1) (2 * c.max_vars)
    (r0 - 32 * c.max_vars) (r0 - 24 * c.max_vars) h2
    (show c.pWsort + BitVec.ofNat 64 (4 * (2 * c.max_vars)) = c.pWorkStk1 by
      unfold FullCfg.pWorkStk1; rw [show 4 * (2 * c.max_vars) = 8 * c.max_vars by omega])
    (by omega) (by omega)
  obtain ⟨ws1, l4, h4⟩ := peel_step_exact_i32 (b := c.pWorkStk2) (2 * c.max_vars)
    (r0 - 40 * c.max_vars) (r0 - 32 * c.max_vars) h3
    (show c.pWorkStk1 + BitVec.ofNat 64 (4 * (2 * c.max_vars)) = c.pWorkStk2 by
      unfold FullCfg.pWorkStk2; rw [show 4 * (2 * c.max_vars) = 8 * c.max_vars by omega])
    (by omega) (by omega)
  obtain ⟨ws2, l5, h5⟩ := peel_step_exact_i32 (b := c.pTarjanMark) (2 * c.max_vars)
    (r0 - 48 * c.max_vars) (r0 - 40 * c.max_vars) h4
    (show c.pWorkStk2 + BitVec.ofNat 64 (4 * (2 * c.max_vars)) = c.pTarjanMark by
      unfold FullCfg.pTarjanMark; rw [show 4 * (2 * c.max_vars) = 8 * c.max_vars by omega])
    (by omega) (by omega)
  obtain ⟨tmk, l6, h6⟩ := peel_step_exact_i32 (b := c.pTarjanReach) (2 * c.max_vars)
    (r0 - 56 * c.max_vars) (r0 - 48 * c.max_vars) h5
    (show c.pTarjanMark + BitVec.ofNat 64 (4 * (2 * c.max_vars)) = c.pTarjanReach by
      unfold FullCfg.pTarjanReach; rw [show 4 * (2 * c.max_vars) = 8 * c.max_vars by omega])
    (by omega) (by omega)
  obtain ⟨trc, l7, h7⟩ := peel_step_exact_i32 (b := c.pScore) (2 * c.max_vars)
    (r0 - 64 * c.max_vars) (r0 - 56 * c.max_vars) h6
    (show c.pTarjanReach + BitVec.ofNat 64 (4 * (2 * c.max_vars)) = c.pScore by
      unfold FullCfg.pScore; rw [show 4 * (2 * c.max_vars) = 8 * c.max_vars by omega])
    (by omega) (by omega)
  obtain ⟨sc, l8, h8⟩ := peel_step_exact_i64 (b := c.pSimSig) c.max_vars
    (r0 - 72 * c.max_vars) (r0 - 64 * c.max_vars) h7 rfl (by omega) (by omega)
  obtain ⟨sig, l9, h9⟩ := peel_step_exact_i64 (b := c.pMinStk) c.max_vars
    (r0 - 80 * c.max_vars) (r0 - 72 * c.max_vars) h8 rfl (by omega) (by omega)
  let r10 := r0 - 80 * c.max_vars
  obtain ⟨mstk, l10, h10⟩ := peel_step_exact_i32 (b := c.pGlueUsed) (2 * c.minDepth)
    (r10 - 8 * c.minDepth) r10 h9
    (show c.pMinStk + BitVec.ofNat 64 (4 * (2 * c.minDepth)) = c.pGlueUsed by
      unfold FullCfg.pGlueUsed; rw [show 4 * (2 * c.minDepth) = 8 * c.minDepth by omega])
    (by omega) (by omega)
  obtain ⟨gu, l11, h11⟩ := peel_step_exact_i32 (b := c.pLastLearned) 64
    (r10 - 8 * c.minDepth - 256) (r10 - 8 * c.minDepth) h10 rfl (by omega) (by omega)
  obtain ⟨ll, l12, h12⟩ := peel_step_exact_i32 (b := c.pArena) 16
    (r10 - 8 * c.minDepth - 320) (r10 - 8 * c.minDepth - 256) h11 rfl (by omega) (by omega)
  let r13 := r10 - 8 * c.minDepth - 320
  obtain ⟨ar, l13, h13⟩ := peel_step_exact_i32 (b := c.pWstk) c.arena_cap
    (r13 - 4 * c.arena_cap) r13 h12 rfl (by omega) (by omega)
  obtain ⟨wstk, l14, h14⟩ := peel_step_exact_i32 (b := c.pDelayed) c.wcap
    (r13 - 4 * c.arena_cap - 4 * c.wcap) (r13 - 4 * c.arena_cap) h13 rfl (by omega) (by omega)
  obtain ⟨del, l15, h15⟩ := peel_step_exact_i32 (b := c.pRedRefs) (3 * c.delayed_cap)
    (4 * c.red_cap + 4 * c.extend_cap + 4 * c.scratch_cap + c.slack)
    (r13 - 4 * c.arena_cap - 4 * c.wcap) h14
    (show c.pDelayed + BitVec.ofNat 64 (4 * (3 * c.delayed_cap)) = c.pRedRefs by
      unfold FullCfg.pRedRefs; rw [show 4 * (3 * c.delayed_cap) = 12 * c.delayed_cap by omega])
    (by omega) (by omega)
  obtain ⟨red, l16, h16⟩ := peel_step_exact_i32 (b := c.pExtendStk) c.red_cap
    (4 * c.extend_cap + 4 * c.scratch_cap + c.slack)
    (4 * c.red_cap + 4 * c.extend_cap + 4 * c.scratch_cap + c.slack) h15 rfl (by omega) (by omega)
  obtain ⟨ext, l17, h17⟩ := peel_step_exact_i32 (b := c.pScratchBuf) c.extend_cap
    (4 * c.scratch_cap + c.slack) (4 * c.extend_cap + 4 * c.scratch_cap + c.slack)
    h16 rfl (by omega) (by omega)
  obtain ⟨sbuf, l18, h18⟩ := peel_step_exact_i32 (b := c.pSlack) c.scratch_cap c.slack
    (4 * c.scratch_cap + c.slack) h17 rfl (by omega) (by omega)
  refine ⟨wvec, repr, wsort, ws1, ws2, tmk, trc, sc, sig, mstk, gu, ll, ar, wstk, del, red,
    ext, sbuf, ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18⟩,
    ?_⟩
  simp only [emp_sep] at h18; exact sep_mono2 (fun _ h => sep_ac h) (fun _ h => h) m h18

private theorem m5_zip_u2 {A1 A2 A3 A4 A5 P : Mem 64 → Prop} {m : Mem 64}
    (h : ((A1 ⋆ A2 ⋆ A3 ⋆ A4 ⋆ A5) ⋆ P) m) : (((A1 ⋆ A4) ⋆ (A2 ⋆ A3 ⋆ A5)) ⋆ P) m := sep_ac h

private theorem m5_zip_u3 {A1 A2 A3 A4 A5 P : Mem 64 → Prop} {m : Mem 64}
    (h : ((A1 ⋆ A2 ⋆ A3 ⋆ A4 ⋆ A5) ⋆ P) m) : (((A4 ⋆ A5) ⋆ (A1 ⋆ A2 ⋆ A3)) ⋆ P) m := sep_ac h

private theorem m5_zip_tl {W R M A K S SL : Mem 64 → Prop} {m : Mem 64}
    (h : ((W ⋆ R ⋆ M ⋆ A ⋆ K) ⋆ S ⋆ SL) m) : ((((W ⋆ R ⋆ M) ⋆ (A ⋆ K)) ⋆ S) ⋆ SL) m := sep_ac h

private structure M5U32_5 (k1 k2 k3 k4 k5 : Nat) where
  (x1 x2 x3 x4 x5 : List (BitVec 32))
  ok : x1.length = k1 ∧ x2.length = k2 ∧ x3.length = k3 ∧ x4.length = k4 ∧ x5.length = k5

private theorem m5_peel_u32_5_block_st (max_v : Nat) (k1 k2 k3 k4 k5 : Nat)
    (a1 a2 a3 a4 a5 b : BitVec 64) {rtot rnext : Nat} {m : Mem 64}
    (ha2 : a2 = a1 + BitVec.ofNat 64 (u32FullBytes max_v))
    (ha3 : a3 = a2 + BitVec.ofNat 64 (u32FullBytes max_v))
    (ha4 : a4 = a3 + BitVec.ofNat 64 (u32FullBytes max_v))
    (ha5 : a5 = a4 + BitVec.ofNat 64 (u32FullBytes max_v))
    (hb : b = a5 + BitVec.ofNat 64 (u32FullBytes max_v))
    (hm : region a1 rtot m)
    (hk1 : 4 * k1 ≤ u32FullBytes max_v := by omega)
    (hk2 : 4 * k2 ≤ u32FullBytes max_v := by omega)
    (hk3 : 4 * k3 ≤ u32FullBytes max_v := by omega)
    (hk4 : 4 * k4 ≤ u32FullBytes max_v := by omega)
    (hk5 : 4 * k5 ≤ u32FullBytes max_v := by omega)
    (hrem : 5 * u32FullBytes max_v + rnext = rtot := by omega)
    (hle : rtot ≤ 2 ^ 64 := by omega) :
    ∃ u : M5U32_5 k1 k2 k3 k4 k5,
      ((array (t := i32) a1 u.x1 ⋆ array (t := i32) a2 u.x2 ⋆ array (t := i32) a3 u.x3 ⋆
        array (t := i32) a4 u.x4 ⋆ array (t := i32) a5 u.x5) ⋆
       (region (a1 + BitVec.ofNat 64 (4 * k1)) (u32FullBytes max_v - 4 * k1) ⋆
        region (a2 + BitVec.ofNat 64 (4 * k2)) (u32FullBytes max_v - 4 * k2) ⋆
        region (a3 + BitVec.ofNat 64 (4 * k3)) (u32FullBytes max_v - 4 * k3) ⋆
        region (a4 + BitVec.ofNat 64 (4 * k4)) (u32FullBytes max_v - 4 * k4) ⋆
        region (a5 + BitVec.ofNat 64 (4 * k5)) (u32FullBytes max_v - 4 * k5)) ⋆
       region b rnext) m := by
  obtain ⟨x1, x2, x3, x4, x5, l1, l2, l3, l4, l5, h⟩ :=
    m5_peel_u32_5_block max_v k1 k2 k3 k4 k5 a1 a2 a3 a4 a5 b ha2 ha3 ha4 ha5 hb hm
      hk1 hk2 hk3 hk4 hk5 hrem hle
  exact ⟨⟨x1, x2, x3, x4, x5, l1, l2, l3, l4, l5⟩, h⟩

private structure M5TailBlk (c : FullCfg) where
  (wvec repr wsort ws1 ws2 tmk trc : List (BitVec 32))
  (sc sig : List (BitVec 64))
  (mstk gu ll ar wstk del red ext sbuf : List (BitVec 32))
  ok : wvec.length = 4 * c.max_vars ∧ repr.length = 2 * c.max_vars ∧
    wsort.length = 2 * c.max_vars ∧ ws1.length = 2 * c.max_vars ∧
    ws2.length = 2 * c.max_vars ∧ tmk.length = 2 * c.max_vars ∧
    trc.length = 2 * c.max_vars ∧ sc.length = c.max_vars ∧
    sig.length = c.max_vars ∧ mstk.length = 2 * c.minDepth ∧
    gu.length = 64 ∧ ll.length = 16 ∧ ar.length = c.arena_cap ∧
    wstk.length = c.wcap ∧ del.length = 3 * c.delayed_cap ∧
    red.length = c.red_cap ∧ ext.length = c.extend_cap ∧ sbuf.length = c.scratch_cap

private theorem m5_peel_tail_block_st (c : FullCfg) {m : Mem 64}
    (hm : region c.pWvec (c.avail - (1152 + 3 * valsBytes c.max_vars +
      5 * markBytes c.max_vars + 15 * u32FullBytes c.max_vars)) m) :
    ∃ t : M5TailBlk c,
      ((array (t := i32) c.pWvec t.wvec ⋆ array (t := i32) c.pRepr t.repr ⋆
        array (t := i32) c.pMinStk t.mstk ⋆
        array (t := i32) c.pArena t.ar ⋆ array (t := i32) c.pWstk t.wstk) ⋆
       ((array (t := i32) c.pWsort t.wsort ⋆ array (t := i32) c.pWorkStk1 t.ws1 ⋆
          array (t := i32) c.pWorkStk2 t.ws2 ⋆ array (t := i32) c.pTarjanMark t.tmk ⋆
          array (t := i32) c.pTarjanReach t.trc) ⋆
        (array64 c.pScore t.sc ⋆ array64 c.pSimSig t.sig ⋆
          array (t := i32) c.pGlueUsed t.gu ⋆ array (t := i32) c.pLastLearned t.ll) ⋆
        (array (t := i32) c.pDelayed t.del ⋆ array (t := i32) c.pRedRefs t.red ⋆
          array (t := i32) c.pExtendStk t.ext ⋆ array (t := i32) c.pScratchBuf t.sbuf)) ⋆
       region c.pSlack c.slack) m := by
  obtain ⟨wvec, repr, wsort, ws1, ws2, tmk, trc, sc, sig, mstk, gu, ll, ar, wstk, del, red,
    ext, sbuf, hok, hm⟩ := m5_peel_tail_block c hm
  exact ⟨⟨wvec, repr, wsort, ws1, ws2, tmk, trc, sc, sig, mstk, gu, ll, ar, wstk, del, red,
    ext, sbuf, hok⟩, hm⟩

private structure M5BytesBlk (c : FullCfg) where
  (vals wvals lmrk mrk ph ptgt pbst wbst : List (BitVec 8))
  ok : vals.length = 2 * c.max_vars ∧ wvals.length = 2 * c.max_vars ∧
    lmrk.length = 2 * c.max_vars ∧ mrk.length = c.max_vars ∧ ph.length = c.max_vars ∧
    ptgt.length = c.max_vars ∧ pbst.length = c.max_vars ∧ wbst.length = c.max_vars

private theorem m5_peel_bytes_block_st (c : FullCfg) {m : Mem 64}
    (hm : region (c.hdr + BitVec.ofNat 64 1152) (c.avail - 1152) m) :
    ∃ b : M5BytesBlk c,
      ((((array (t := i8) c.pVals b.vals ⋆ array (t := i8) c.pLitMark b.lmrk ⋆
          array (t := i8) c.pMark b.mrk) ⋆
         (array (t := i8) c.pWalkVals b.wvals ⋆ array (t := i8) c.pPhases b.ph ⋆
          array (t := i8) c.pPhasesTarget b.ptgt ⋆ array (t := i8) c.pPhasesBest b.pbst ⋆
          array (t := i8) c.pWalkBest b.wbst)) ⋆ c.padBytes) ⋆
        region c.pFlags (c.avail - (1152 + 3 * valsBytes c.max_vars +
          5 * markBytes c.max_vars))) m := by
  obtain ⟨vals, wvals, lmrk, mrk, ph, ptgt, pbst, wbst,
    hv1, hv2, hv3, hm1, hm2, hm3, hm4, hm5, hm⟩ := m5_peel_bytes_block c hm
  exact ⟨⟨vals, wvals, lmrk, mrk, ph, ptgt, pbst, wbst,
    hv1, hv2, hv3, hm1, hm2, hm3, hm4, hm5⟩, hm⟩

private theorem m5_step_u32_5 {Pre : Mem 64 → Prop} (max_v k1 k2 k3 k4 k5 : Nat)
    (a1 a2 a3 a4 a5 b : BitVec 64) {rtot rnext : Nat} {m : Mem 64}
    (ha2 : a2 = a1 + BitVec.ofNat 64 (u32FullBytes max_v))
    (ha3 : a3 = a2 + BitVec.ofNat 64 (u32FullBytes max_v))
    (ha4 : a4 = a3 + BitVec.ofNat 64 (u32FullBytes max_v))
    (ha5 : a5 = a4 + BitVec.ofNat 64 (u32FullBytes max_v))
    (hb : b = a5 + BitVec.ofNat 64 (u32FullBytes max_v))
    (hm : (Pre ⋆ region a1 rtot) m)
    (hk1 : 4 * k1 ≤ u32FullBytes max_v := by omega)
    (hk2 : 4 * k2 ≤ u32FullBytes max_v := by omega)
    (hk3 : 4 * k3 ≤ u32FullBytes max_v := by omega)
    (hk4 : 4 * k4 ≤ u32FullBytes max_v := by omega)
    (hk5 : 4 * k5 ≤ u32FullBytes max_v := by omega)
    (hrem : 5 * u32FullBytes max_v + rnext = rtot := by omega)
    (hle : rtot ≤ 2 ^ 64 := by omega) :
    ∃ u : M5U32_5 k1 k2 k3 k4 k5,
      ((Pre ⋆ ((array (t := i32) a1 u.x1 ⋆ array (t := i32) a2 u.x2 ⋆
        array (t := i32) a3 u.x3 ⋆ array (t := i32) a4 u.x4 ⋆ array (t := i32) a5 u.x5) ⋆
       (region (a1 + BitVec.ofNat 64 (4 * k1)) (u32FullBytes max_v - 4 * k1) ⋆
        region (a2 + BitVec.ofNat 64 (4 * k2)) (u32FullBytes max_v - 4 * k2) ⋆
        region (a3 + BitVec.ofNat 64 (4 * k3)) (u32FullBytes max_v - 4 * k3) ⋆
        region (a4 + BitVec.ofNat 64 (4 * k4)) (u32FullBytes max_v - 4 * k4) ⋆
        region (a5 + BitVec.ofNat 64 (4 * k5)) (u32FullBytes max_v - 4 * k5)))) ⋆
       region b rnext) m := by
  have h1 := sep_mono_r (fun _ h => m5_peel_u32_5_block_st max_v k1 k2 k3 k4 k5 a1 a2 a3 a4 a5 b
    ha2 ha3 ha4 ha5 hb h hk1 hk2 hk3 hk4 hk5 hrem hle) hm
  obtain ⟨u, h2⟩ := sep_ex_r.mp h1
  exact ⟨u, sep_ac h2⟩

private theorem m5_step_tail {Pre : Mem 64 → Prop} (c : FullCfg) {m : Mem 64}
    (hm : (Pre ⋆ region c.pWvec (c.avail - (1152 + 3 * valsBytes c.max_vars +
      5 * markBytes c.max_vars + 15 * u32FullBytes c.max_vars))) m) :
    ∃ t : M5TailBlk c,
      (Pre ⋆
       ((array (t := i32) c.pWvec t.wvec ⋆ array (t := i32) c.pRepr t.repr ⋆
         array (t := i32) c.pMinStk t.mstk ⋆
         array (t := i32) c.pArena t.ar ⋆ array (t := i32) c.pWstk t.wstk) ⋆
        ((array (t := i32) c.pWsort t.wsort ⋆ array (t := i32) c.pWorkStk1 t.ws1 ⋆
           array (t := i32) c.pWorkStk2 t.ws2 ⋆ array (t := i32) c.pTarjanMark t.tmk ⋆
           array (t := i32) c.pTarjanReach t.trc) ⋆
         (array64 c.pScore t.sc ⋆ array64 c.pSimSig t.sig ⋆
           array (t := i32) c.pGlueUsed t.gu ⋆ array (t := i32) c.pLastLearned t.ll) ⋆
         (array (t := i32) c.pDelayed t.del ⋆ array (t := i32) c.pRedRefs t.red ⋆
           array (t := i32) c.pExtendStk t.ext ⋆ array (t := i32) c.pScratchBuf t.sbuf)) ⋆
        region c.pSlack c.slack)) m := by
  have h1 := sep_mono_r (fun _ h => m5_peel_tail_block_st c h) hm
  exact sep_ex_r.mp h1

private theorem m5_full_avail_to_arrays (c : FullCfg) {m : Mem 64}
    (hm : region (c.hdr + BitVec.ofNat 64 1152) (c.avail - 1152) m) :
    ∃ a : M5InitArrs c, (FullCoreArrays c (m5InitFullState c 0#64 0#64 0#64 a).core ⋆
      FullScratchArrays c (m5InitFullState c 0#64 0#64 0#64 a).scratch ⋆ c.pad) m := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hfit := c.havail_fit; have hsz := c.hsize; have hfx := fullFixedBytes_lt c.hmaxv
  have hu4 := u32FullBytes_ge4 c.max_vars; have hu := u32FullBytes_ge c.max_vars
  have hfb : fullFixedBytes c.max_vars = 1472 + 3 * valsBytes c.max_vars +
      5 * markBytes c.max_vars + 15 * u32FullBytes c.max_vars + 80 * c.max_vars +
      8 * c.minDepth := rfl
  let ub := u32FullBytes c.max_vars
  let r15 := c.avail - (1152 + 3 * valsBytes c.max_vars + 5 * markBytes c.max_vars + 15 * ub)
  have h15le : 1152 + 3 * valsBytes c.max_vars + 5 * markBytes c.max_vars + 15 * ub ≤ c.avail := by
    dsimp only [ub]; omega
  have hrem0_eq : c.avail - (1152 + 3 * valsBytes c.max_vars + 5 * markBytes c.max_vars) =
      15 * ub + r15 := by dsimp only [r15, ub]; omega
  have h15_264 : 15 * ub + r15 ≤ 2 ^ 64 := by dsimp only [r15]; omega
  have h10_264 : 10 * ub + r15 ≤ 2 ^ 64 := by omega
  have h5_264 : 5 * ub + r15 ≤ 2 ^ 64 := by omega
  have hrem15 : 5 * u32FullBytes c.max_vars + (10 * ub + r15) = 15 * ub + r15 := by
    dsimp only [ub]; omega
  have hrem10 : 5 * u32FullBytes c.max_vars + (5 * ub + r15) = 10 * ub + r15 := by
    dsimp only [ub]; omega
  obtain ⟨b, h_0⟩ := m5_peel_bytes_block_st c hm
  rw [hrem0_eq] at h_0
  obtain ⟨u1, h_1⟩ := m5_step_u32_5 c.max_vars c.max_vars c.max_vars c.max_vars c.max_vars
    c.max_vars c.pFlags c.pLevel c.pReason c.pTrail c.pTrailPos c.pTmp (rtot := 15 * ub + r15)
    (rnext := 10 * ub + r15) rfl rfl rfl rfl rfl h_0 hu4 hu4 hu4 hu4 hu4 hrem15 h15_264
  obtain ⟨u2, h_2⟩ := m5_step_u32_5 c.max_vars c.max_vars c.max_vars c.max_vars c.max_vars
    c.max_vars c.pTmp c.pHeap c.pPos c.pMinClr c.pShrinkStk c.pQPrev (rtot := 10 * ub + r15)
    (rnext := 5 * ub + r15) rfl rfl rfl rfl rfl h_1 hu4 hu4 hu4 hu4 hu4 hrem10 h10_264
  obtain ⟨u3, h_3⟩ := m5_step_u32_5 c.max_vars c.max_vars c.max_vars c.max_vars (c.max_vars + 1)
    (c.max_vars + 1) c.pQPrev c.pQNext c.pQStamp c.pFrameTrail c.pFrameDec c.pWvec
    (rtot := 5 * ub + r15) (rnext := r15) rfl rfl rfl rfl rfl h_2 hu4 hu4 hu4 hu hu rfl h5_264
  have h_3r : (_ ⋆ region c.pWvec (c.avail - (1152 + 3 * valsBytes c.max_vars +
      5 * markBytes c.max_vars + 15 * u32FullBytes c.max_vars))) m := h_3
  obtain ⟨tl, h_4⟩ := m5_step_tail c h_3r
  obtain ⟨hv1, hv2, hv3, hm1, hm2, hm3, hm4, hm5⟩ := b.ok
  obtain ⟨lfl, llv, lrs, ltr, ltp⟩ := u1.ok
  obtain ⟨ltmp, lhp, lps, lmc, lsh⟩ := u2.ok
  obtain ⟨lqp, lqn, lqs, lft, lfd⟩ := u3.ok
  obtain ⟨lwv, lrp, lws, l1, l2, ltm, ltrc, lsc, lsg, lms, lgu, lll, lar, lwk, ldl, lrd,
    lex, lsb⟩ := tl.ok
  let a : M5InitArrs c :=
    ⟨b.vals, b.lmrk, b.mrk, b.wvals, b.ph, b.ptgt, b.pbst, b.wbst, u1.x1, u1.x2, u1.x3, u1.x4,
      u1.x5, u2.x1, u2.x4, u3.x4, u3.x5, tl.wvec, tl.repr, tl.mstk, tl.ar, tl.wstk, u2.x2, u2.x3,
      u2.x5, u3.x1, u3.x2, u3.x3, tl.wsort, tl.ws1, tl.ws2, tl.tmk, tl.trc, tl.sc, tl.sig, tl.gu,
      tl.ll, tl.del, tl.red, tl.ext, tl.sbuf, ⟨hv1, hv3, hm1, hv2, hm2, hm3, hm4, hm5, lfl, llv,
      lrs, ltr, ltp, ltmp, lmc, lft, lfd, lwv, lrp, lms, lar, lwk, lhp, lps, lsh, lqp, lqn, lqs,
      lws, l1, l2, ltm, ltrc, lsc, lsg, lgu, lll, ldl, lrd, lex, lsb⟩⟩
  have hm_flat : (FullCoreArrays c (m5InitFullState c 0#64 0#64 0#64 a).core ⋆
      FullScratchArrays c (m5InitFullState c 0#64 0#64 0#64 a).scratch ⋆ c.pad) m := by
    dsimp only [m5InitFullState]
    unfold FullCoreArrays FullCoreByteArrs FullCoreU32A FullCoreU32B FullCoreDynArrs
      FullScratchArrays FullScrByteArrs FullScrU32A FullScrWksArrs FullScrMetaArrs
      FullScrDynArrs FullCfg.pad FullCfg.padU32A FullCfg.padU32B FullCfg.padU32C
    exact sep_ac h_4
  exact ⟨a, hm_flat⟩

private theorem m5_init_hdr_remerge {cnf_ptr hdr_addr : BitVec 64} {avail : Nat}
    {cnfBytes : List UInt8} {R : Mem 64 → Prop} (h32 : 32 ≤ avail) (hle : avail ≤ 2 ^ 64)
    {mv' nc' cur' val' : BitVec 64} {m' : Mem 64}
    (hm' : (bytes cnf_ptr cnfBytes ⋆ dimacsState hdr_addr mv' nc' cur' val' ⋆
      region (hdr_addr + BitVec.ofNat 64 32) (avail - 32) ⋆ R) m') :
    (bytes cnf_ptr cnfBytes ⋆ region hdr_addr avail ⋆ R) m' := by
  have h2 := sep_mono2 (sep_mono2 (fun _ => Kissat.dimacsState_to_region) (fun _ h => h))
    (fun _ h => h) m' (show ((dimacsState hdr_addr mv' nc' cur' val' ⋆
      region (hdr_addr + BitVec.ofNat 64 32) (avail - 32)) ⋆
      (bytes cnf_ptr cnfBytes ⋆ R)) m' from sep_ac hm')
  rw [region_merge_eq (a := hdr_addr) (n1 := 32) (n2 := avail - 32) (n := avail)
    (by omega) hle] at h2
  exact sep_ac h2

private theorem m5_init_state_fail {cnf_ptr hdr_addr : BitVec 64} {avail : Nat}
    {cnfBytes rest : List UInt8} {mv nc : Nat} {cur' val' : BitVec 64}
    {R : Mem 64 → Prop} {Q : Post [.bool]} {m' : Mem 64} (h32 : 32 ≤ avail) (hle : avail ≤ 2 ^ 64)
    (hhdr : parseHeader cnfBytes = some (mv, nc, rest))
    (hfail : avail < fullFixedBytes mv + nc * 40 + 136)
    (hm' : (bytes cnf_ptr cnfBytes ⋆ dimacsState hdr_addr (BitVec.ofNat 64 mv)
      (BitVec.ofNat 64 nc) cur' val' ⋆ region (hdr_addr + 32#64) (avail - 32) ⋆ R) m')
    (hQfalse : ∀ m'', (bytes cnf_ptr cnfBytes ⋆ region hdr_addr avail ⋆ R) m'' →
      (∀ mv' nc' rest', parseHeader cnfBytes = some (mv', nc', rest') →
        avail < fullFixedBytes mv' + nc' * 40 + 136) → Q (false, ()) m'') : Q (false, ()) m' :=
  hQfalse m' (m5_init_hdr_remerge h32 hle hm') fun _ _ _ h => by
    rw [hhdr] at h; rcases Option.some.inj h with ⟨rfl, rfl, rfl⟩; exact hfail

private theorem m5_init_state_split_tail {hdr_addr : BitVec 64} {avail : Nat}
    {cnf_ptr : BitVec 64} {cnfBytes : List UInt8} {j nc mv : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} (h1152 : 1152 ≤ avail) (hav64 : avail ≤ 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ dimacsState hdr_addr (BitVec.ofNat 64 mv)
      (BitVec.ofNat 64 nc) (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 nc) ⋆
      region (hdr_addr + 32#64) (avail - 32) ⋆ R) m) :
    ∃ ws : List (BitVec 64), ws.length = 140 ∧
      (hdrTail4 hdr_addr (ws.take 35) ((ws.drop 35).take 35) ((ws.drop 70).take 35)
          ((ws.drop 105).take 35) ⋆
        (region (hdr_addr + 1152#64) (avail - 1152) ⋆ bytes cnf_ptr cnfBytes ⋆
          dimacsState hdr_addr (BitVec.ofNat 64 mv) (BitVec.ofNat 64 nc)
            (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 nc) ⋆ R)) m := by
  have h1 : ((region (hdr_addr + 32#64) 1120 ⋆ region (hdr_addr + 1152#64) (avail - 1152)) ⋆
      (bytes cnf_ptr cnfBytes ⋆ dimacsState hdr_addr (BitVec.ofNat 64 mv) (BitVec.ofNat 64 nc)
        (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 nc) ⋆ R)) m :=
    sep_mono (fun _ h => reg_peel (b := hdr_addr + 1152#64) (n1 := 1120) (n2 := avail - 1152) h
      (hb := by rw [BitVec.add_assoc]; rfl) (hn := by omega) (hle := by omega))
      (sep_ac hm : (region (hdr_addr + 32#64) (avail - 32) ⋆ (bytes cnf_ptr cnfBytes ⋆
        dimacsState hdr_addr (BitVec.ofNat 64 mv) (BitVec.ofNat 64 nc)
          (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 nc) ⋆ R)) m)
  have h1a : (region (hdr_addr + 32#64) 1120 ⋆
      (region (hdr_addr + 1152#64) (avail - 1152) ⋆ bytes cnf_ptr cnfBytes ⋆
        dimacsState hdr_addr (BitVec.ofNat 64 mv) (BitVec.ofNat 64 nc)
          (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 nc) ⋆ R)) m := sep_ac h1
  have h2 := sep_mono (fun _ (h : region (hdr_addr + 32#64) 1120 _) =>
    region_to_array64 140 (by decide) h) h1a
  obtain ⟨ws, h3⟩ := sep_ex_l.mp h2
  obtain ⟨hwl, h4⟩ := sep_pure_l.mp h3
  have h5 := sep_mono (fun _ (h : array64 (hdr_addr + 32#64) ws _) => by
    have ht := array64_to_hdrTail4 hwl (by rwa [sep_emp])
    rwa [sep_emp] at ht) h4
  exact ⟨ws, hwl, sep_ac h5⟩

/-- Parametric `Func.wp` theorem for `full_init_state_m5` against canonical
`Full.fullInitStateSpec`, wiring BOTH `[38] full_calc_ext_cap_m5` (`4M`) and
`[39] full_calc_scr_cap_m5` (`1M`). -/
theorem full_init_state_m5_wp (Γ : Env)
    (hHdr : ∀ a m Q X, Kissat.kissatParseHeaderSpec a m Q X →
      Γ "kissat_parse_header" [i64, i64, i64] [.bool] a m Q X)
    (hFixed : ∀ a m Q X, Full.fullFixedBytesSpec a m Q X →
      Γ "full_fixed_bytes" [i64] [i64] a m Q X)
    (hMaxV : ∀ a m Q X, Full.fullCalcMaxVSpec a m Q X →
      Γ "full_calc_max_v" [i64, i64, i64, i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, fullCalcExtCapM5Spec a m Q X →
      Γ "full_calc_ext_cap_m5" [i64] [i64] a m Q X)
    (hScr : ∀ a m Q X, fullCalcScrCapM5Spec a m Q X →
      Γ "full_calc_scr_cap_m5" [i64] [i64] a m Q X)
    (hArenas : ∀ a m Q X, Full.fullInitArenasSpec a m Q X →
      Γ "full_init_arenas" [i64, i64, i64, i64] [] a m Q X)
    (hInitHdr : ∀ a m Q X, Full.fullInitHdrSpec a m Q X →
      Γ "full_init_hdr" [i64, i64, i64, i64] [] a m Q X)
    (hZt1 : ∀ a m Q X, Full.fullZeroTables1Spec a m Q X →
      Γ "full_zero_tables1" [i64] [] a m Q X)
    (hZt2 : ∀ a m Q X, Full.fullZeroTables2Spec a m Q X →
      Γ "full_zero_tables2" [i64] [] a m Q X) :
    ∀ a m Q X, Full.fullInitStateSpec a m Q X →
      Func.wp Γ full_init_state_m5_body a m Q X := by
  rintro ⟨cnf_ptr, cend, hdr_addr, avail, fuel, ⟨⟩⟩ m Q X
    ⟨cnfBytes, R, rfl, hfit, havel_fit, h1152, hm_in, hQfalse, hQtrue⟩
  have hav_le : avail.toNat ≤ 2 ^ 64 := by omega
  have hm0 : (bytes cnf_ptr cnfBytes ⋆ (region hdr_addr 32 ⋆
      region (hdr_addr + BitVec.ofNat 64 32) (avail.toNat - 32)) ⋆ R) m := by
    rw [region_merge_eq (a := hdr_addr) (n1 := 32) (n2 := avail.toNat - 32) (n := avail.toNat)
      (by omega) hav_le]; exact hm_in
  have hm0a := sep_mono (fun _ => Kissat.region32_to_dimacsState)
    (sep_ac hm0 : (region hdr_addr 32 ⋆ (bytes cnf_ptr cnfBytes ⋆
      region (hdr_addr + BitVec.ofNat 64 32) (avail.toNat - 32) ⋆ R)) m)
  obtain ⟨mv0, hm0b⟩ := sep_ex_l.mp hm0a
  obtain ⟨nc0, hm0c⟩ := sep_ex_l.mp hm0b
  obtain ⟨cur0, hm0d⟩ := sep_ex_l.mp hm0c
  obtain ⟨val0, hm_pre⟩ := sep_ex_l.mp hm0d
  unfold Func.wp full_init_state_m5_body
  apply wp_call_of_spec; apply hHdr
  change kissatParseHeaderSpec (cnf_ptr, cnf_ptr + BitVec.ofNat 64 cnfBytes.length, hdr_addr, ())
    m _ _
  refine ⟨mv0, nc0, cur0, val0, cnfBytes,
    region (hdr_addr + BitVec.ofNat 64 32) (avail.toNat - 32) ⋆ R, rfl, hfit, sep_ac hm_pre, ?_⟩
  cases hhdr : parseHeader cnfBytes with
  | none =>
    intro _ _ _ _ m' hm'; refine wp_jnz_of (fun hc => by cases hc) (fun _ => ?_)
    rw [wp_ret]; exact hQfalse m' (m5_init_hdr_remerge (by omega) hav_le (sep_ac hm'))
      (fun _ _ _ h => by rw [hhdr] at h; cases h)
  | some p =>
    rcases p with ⟨mv, nc, rest⟩; intro j m0 hmv_bd hnc_bd hj hdrop hm0
    have hmv := hmv_bd; have hnc := hnc_bd; unfold dimacsBound at hmv hnc
    refine wp_jnz_of (fun _ => ?_) (fun hc => by cases hc)
    fp_head_steps
    apply wp_call_of_spec; apply hFixed
    change Full.fullFixedBytesSpec (BitVec.ofNat 64 mv, ()) m0 _ _
    have hmv_to : (BitVec.ofNat 64 mv).toNat = mv := bv64_ofNat_toNat (by omega)
    have hnc_to : (BitVec.ofNat 64 nc).toNat = nc := bv64_ofNat_toNat (by omega)
    refine ⟨by rw [hmv_to]; unfold dimacsBound; omega, ?_⟩
    rw [hmv_to]; have hfx0_lt := fullFixedBytes_lt (max_v := mv) (by unfold dimacsBound; omega)
    have hf0_to : (BitVec.ofNat 64 (fullFixedBytes mv)).toNat = fullFixedBytes mv :=
      bv64_ofNat_toNat (by omega)
    dsimp only; fp_head_steps
    rw [show avail.ult (BitVec.ofNat 64 (fullFixedBytes mv)) =
      decide (avail.toNat < fullFixedBytes mv) from by rw [BitVec.ult, hf0_to]]
    refine wp_jnz_of (fun hlt => ?_) (fun hge => ?_)
    · m5_fp_jnz_t' hlt
      exact m5_init_state_fail (by omega) hav_le hhdr (by omega) (sep_ac hm0) hQfalse
    · m5_fp_jnz_f' hge; fp_head_steps
      have hsub_f0 : avail - BitVec.ofNat 64 (fullFixedBytes mv) =
          BitVec.ofNat 64 (avail.toNat - fullFixedBytes mv) := by
        simpa [bv_ofNat_toNat_eq avail] using bv_sub_ofNat (by omega) avail.isLt
      have hnc40 : BitVec.ofNat 64 nc * (40 : BitVec 64) + 136 =
          BitVec.ofNat 64 (nc * 40 + 136) := by
        rw [show (40 : BitVec 64) = BitVec.ofNat 64 40 from rfl,
          show (136 : BitVec 64) = BitVec.ofNat 64 136 from rfl, bv64_mul_nat3, hnc_to,
          bv_add_ofNat]
      rw [hsub_f0, hnc40, bv_ult_eq (by have := avail.isLt; omega) (by omega)]
      refine wp_jnz_of (fun hlt2 => ?_) (fun hge2 => ?_)
      · m5_fp_jnz_t' hlt2
        exact m5_init_state_fail (by omega) hav_le hhdr (by omega) (sep_ac hm0) hQfalse
      · m5_fp_jnz_f' hge2
        apply wp_call_of_spec; apply hMaxV
        change Full.fullCalcMaxVSpec (avail, BitVec.ofNat 64 mv, BitVec.ofNat 64 nc,
          BitVec.ofNat 64 (fullFixedBytes mv), ()) m0 _ _
        refine ⟨by rw [hmv_to]; exact hmv_bd, by rw [hnc_to]; exact hnc_bd,
          by rw [hmv_to]; exact hf0_to, by rw [hf0_to, hnc_to]; omega, ?_⟩
        intro max_v hmv_le hmx_bd hmax_fit
        rw [hmv_to] at hmv_le; rw [hnc_to] at hmax_fit
        have hmx_b := hmx_bd; unfold dimacsBound at hmx_b
        have hfx_m_lt := fullFixedBytes_lt hmx_bd
        fp_head_steps; apply wp_call_of_spec; apply hFixed
        change Full.fullFixedBytesSpec (max_v, ()) m0 _ _
        refine ⟨hmx_bd, ?_⟩; dsimp only; fp_head_steps
        have hrem_eq : avail - BitVec.ofNat 64 (fullFixedBytes max_v.toNat) =
            BitVec.ofNat 64 (avail.toNat - fullFixedBytes max_v.toNat) := by
          simpa [bv_ofNat_toNat_eq avail] using bv_sub_ofNat (by omega) avail.isLt
        let rem := avail.toNat - fullFixedBytes max_v.toNat
        have hrem_to : (BitVec.ofNat 64 rem).toNat = rem :=
          bv64_ofNat_toNat (by have := avail.isLt; omega)
        have hrem136 : nc * 40 + 136 ≤ rem := by omega
        rw [hrem_eq]
        let del_cap := fullInitDelCap rem
        have hdel_bd : del_cap < dimacsBound := fullInitDelCap_lt
        have hdel_bd' := hdel_bd; unfold dimacsBound at hdel_bd'
        refine wp_join_group
          (fun (v : Tup Val [i64]) md => v.1 = BitVec.ofNat 64 del_cap ∧ md = m0) ?_ ?_
        · rintro _ ⟨d_v, ⟨⟩⟩ md ⟨rfl, rfl⟩; simp only [Blocks.get_here]; fp_head_steps
          apply wp_call_of_spec; apply hExt
          change fullCalcExtCapM5Spec (BitVec.ofNat 64 rem, ()) md _ _
          intro ecap_v hecap_le hecap_z hecap_4; dsimp only; fp_head_steps
          apply wp_call_of_spec; apply hScr
          change fullCalcScrCapM5Spec (BitVec.ofNat 64 rem, ()) md _ _
          intro scap_v hscap_le hscap_z hscap_4; dsimp only; fp_head_steps
          rw [hrem_to] at hecap_4 hscap_4
          obtain ⟨_, hecap_lt, hscap_lt, hbr_lt, hbr_ge⟩ :=
            m5_init_caps_bridge hrem136 hecap_le hecap_4 hscap_le hscap_4
          have hecap_bv : BitVec.ofNat 64 ecap_v.toNat = ecap_v := bv_ofNat_toNat_eq ecap_v
          have hscap_bv : BitVec.ofNat 64 scap_v.toNat = scap_v := bv_ofNat_toNat_eq scap_v
          have hdel_mul : BitVec.ofNat 64 del_cap * (12 : BitVec 64) =
              BitVec.ofNat 64 (12 * del_cap) := by
            rw [show (12 : BitVec 64) = BitVec.ofNat 64 12 from rfl, bv64_mul_nat3,
              bv64_ofNat_toNat (by omega), Nat.mul_comm]
          have hshl2_e : ecap_v <<< (((2 : BitVec 32).signExtend 64).toNat % 64) =
              BitVec.ofNat 64 (4 * ecap_v.toNat) := bv64_shl2_val (by omega)
          have hshl2_s : scap_v <<< (((2 : BitVec 32).signExtend 64).toNat % 64) =
              BitVec.ofNat 64 (4 * scap_v.toNat) := bv64_shl2_val (by omega)
          refine wp_join_group (fun (v : Tup Val [i64, i64, i64]) mg =>
            ∃ ec sc : Nat, ec < dimacsBound ∧ sc < dimacsBound ∧
              v.1 = BitVec.ofNat 64 ec ∧ v.2.1 = BitVec.ofNat 64 sc ∧
              v.2.2.1 = BitVec.ofNat 64 (12 * del_cap + 4 * ec + 4 * sc) ∧
              12 * del_cap + 4 * ec + 4 * sc + 40 ≤ rem ∧ mg = md) ?_ ?_
          · rintro _ ⟨ec_v, sc_v, dyn_v, ⟨⟩⟩ mg ⟨ec, sc, hec, hsc, rfl, rfl, rfl, hd40, rfl⟩
            simp only [Blocks.get_here]
            have hm0_ac : (bytes cnf_ptr cnfBytes ⋆ dimacsState hdr_addr (BitVec.ofNat 64 mv)
                (BitVec.ofNat 64 nc) (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 nc) ⋆
                region (hdr_addr + 32#64) (avail.toNat - 32) ⋆ R) mg := sep_ac hm0
            obtain ⟨ws, hwl, _⟩ := m5_init_state_split_tail h1152 hav_le hm0_ac
            clear hm_in hm_pre hm0; fp_head_steps
            have hw0l : (ws.take 35).length = 35 := by simp [hwl]
            have hw1l : ((ws.drop 35).take 35).length = 35 := by simp [hwl]
            have hw2l : ((ws.drop 70).take 35).length = 35 := by simp [hwl]
            have hw3l : ((ws.drop 105).take 35).length = 35 := by simp [hwl]
            let ws1 := ws.take 35 ++
              ((ws.drop 35).take 35).set 17 (BitVec.ofNat 64 del_cap) ++
              (ws.drop 70).take 35 ++
              (((ws.drop 105).take 35).set 4 (BitVec.ofNat 64 ec)).set 7 (BitVec.ofNat 64 sc)
            have hm_arr : (array64 (hdr_addr + 32) ws1 ⋆ (region (hdr_addr + 1152#64)
                (avail.toNat - 1152) ⋆ bytes cnf_ptr cnfBytes ⋆
                dimacsState hdr_addr (BitVec.ofNat 64 mv) (BitVec.ofNat 64 nc)
                  (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 nc) ⋆ R)) m := by
              rwa [hdrTail4_eq_array64 hw0l (by simp [hw1l]) hw2l (by simp [hw3l])] at hm
            have hws1_len : ws1.length = 140 := by simp [ws1, hw0l, hw1l, hw2l, hw3l]
            have h52_ws1 : ws1[52]? = some (BitVec.ofNat 64 del_cap) := by
              dsimp only [ws1]
              rw [append4_getElem?_1 hw0l (by simp [hw1l]) (by decide) (by decide)]
              simp [hw1l]
            have h109_ws1 : ws1[109]? = some (BitVec.ofNat 64 ec) := by
              dsimp only [ws1]; rw [append4_getElem?_3 hw0l (by simp [hw1l]) hw2l (by decide)]
              simp [hw3l]
            have h112_ws1 : ws1[112]? = some (BitVec.ofNat 64 sc) := by
              dsimp only [ws1]; rw [append4_getElem?_3 hw0l (by simp [hw1l]) hw2l (by decide)]
              simp [hw3l]
            have hsub_dyn : BitVec.ofNat 64 rem -
                BitVec.ofNat 64 (12 * del_cap + 4 * ec + 4 * sc) =
                BitVec.ofNat 64 (rem - (12 * del_cap + 4 * ec + 4 * sc)) :=
              bv_sub_ofNat (by omega) (by have := avail.isLt; omega)
            rw [hsub_dyn]
            apply wp_call_of_spec; apply hArenas
            change Full.fullInitArenasSpec (hdr_addr, hdr_addr, max_v,
              BitVec.ofNat 64 (rem - (12 * del_cap + 4 * ec + 4 * sc)), ()) m _ _
            let adyn := rem - (12 * del_cap + 4 * ec + 4 * sc)
            have hadyn_to : (BitVec.ofNat 64 adyn).toNat = adyn :=
              bv64_ofNat_toNat (by have := avail.isLt; omega)
            have hec' := hec; have hsc' := hsc; unfold dimacsBound at hec' hsc'
            refine ⟨ws1, del_cap, ec, sc, _, rfl, hws1_len, hmx_bd, hdel_bd, hec, hsc,
              h52_ws1, h109_ws1, h112_ws1, by rw [hadyn_to]; omega, hm_arr,
              fun acap wcap rcap ws2 m2 hws2l hac hwc hrc hsum hwpos hws2 hm2 => ?_⟩
            rw [hadyn_to] at hsum hwpos
            have hwcap_pos : 1 ≤ wcap := hwpos (by omega)
            let c : FullCfg :=
              { hdr := hdr_addr, avail := avail.toNat, mv := mv, max_vars := max_v.toNat,
                bva_cap := max_v.toNat - mv, nc := nc, arena_cap := acap, wcap := wcap,
                delayed_cap := del_cap, red_cap := rcap, extend_cap := ec, scratch_cap := sc,
                hbva := by omega, hmv := hmv_bd, hmaxv := hmx_bd, hnc := hnc_bd, harena := hac,
                hwcap := hwc, hdel := hdel_bd, hred := hrc, hext := hec, hscr := hsc,
                havail_fit := havel_fit, hsize := by omega }
            apply wp_call_of_spec; apply hInitHdr
            change Full.fullInitHdrSpec (hdr_addr, BitVec.ofNat 64 mv, max_v, fuel, ()) m2 _ _
            have hws2_c := hws2 c rfl rfl rfl rfl rfl rfl rfl rfl
            refine ⟨c, ws2, _, rfl, rfl, bv_ofNat_toNat_eq max_v |>.symm, hws2l,
              fun s0 i hi => ?_, hm2, fun s_hdr m3 hcv hal hwl hte hpr hcl htl hfu hunf hpb
                hmcl hmcf hoom hdm hinc hel hm3 => ?_⟩
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
              unfold Full.hdrTailWords Full.hdrTailWords0 Full.hdrTailWords1 Full.hdrTailWords2
                Full.hdrTailWords3
              repeat rcases hws2_c with ⟨h_, hws2_c⟩
              rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                rfl | rfl <;> assumption
            · have hm3a : (region (c.hdr + BitVec.ofNat 64 1152) (c.avail - 1152) ⋆
                  (bytes cnf_ptr cnfBytes ⋆ dimacsState c.hdr (BitVec.ofNat 64 mv)
                    (BitVec.ofNat 64 nc) (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 nc) ⋆
                    array64 (c.hdr + 32) (Full.hdrTailWords c s_hdr) ⋆ R)) m3 := sep_ac hm3
              obtain ⟨arrs, hcomb⟩ :=
                sep_ex_l.mp (sep_mono (fun _ => m5_full_avail_to_arrays c) hm3a)
              let s_pre : FullState :=
                { core := { s_hdr.core with
                    d_cur := cnf_ptr + BitVec.ofNat 64 j, d_val := BitVec.ofNat 64 nc,
                    vals := arrs.vals, lit_mark := arrs.lit_mark, mrk := arrs.mrk,
                    flags := arrs.flags, lvl := arrs.lvl, rsns := arrs.rsns, trl := arrs.trl,
                    trail_pos := arrs.trail_pos, tmp := arrs.tmp, min_clr := arrs.min_clr,
                    frame_trail := arrs.frame_trail, frame_dec := arrs.frame_dec,
                    wvec := arrs.wvec, repr := arrs.repr, min_stk := arrs.min_stk,
                    arena := arrs.arena, wstk := arrs.wstk },
                  scratch := { s_hdr.scratch with
                    walk_vals := arrs.walk_vals, phases := arrs.phases,
                    phases_target := arrs.phases_target, phases_best := arrs.phases_best,
                    walk_best := arrs.walk_best, heap := arrs.heap, pos := arrs.pos,
                    shrink_stk := arrs.shrink_stk, q_prev := arrs.q_prev, q_next := arrs.q_next,
                    q_stamp := arrs.q_stamp, wsort := arrs.wsort, work_stk1 := arrs.work_stk1,
                    work_stk2 := arrs.work_stk2, tarjan_mark := arrs.tarjan_mark,
                    tarjan_reach := arrs.tarjan_reach, score := arrs.score, sim_sig := arrs.sim_sig,
                    glue_used := arrs.glue_used, last_learned := arrs.last_learned,
                    delayed := arrs.delayed, red_refs := arrs.red_refs,
                    extend_stk := arrs.extend_stk, scratch_buf := arrs.scratch_buf } }
              have h_pre_ca : FullCoreArrays c s_pre.core =
                  FullCoreArrays c (m5InitFullState c 0#64 0#64 0#64 arrs).core := rfl
              have h_pre_sa : FullScratchArrays c s_pre.scratch =
                  FullScratchArrays c (m5InitFullState c 0#64 0#64 0#64 arrs).scratch := rfl
              have h_pre_ht : Full.hdrTailWords c s_pre = Full.hdrTailWords c s_hdr := rfl
              have hm_pre_full : (FullMem c s_pre ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m3 := by
                rw [← h_pre_ca, ← h_pre_sa] at hcomb
                change ((FullCoreArrays c s_pre.core ⋆ FullScratchArrays c s_pre.scratch ⋆
                    c.pad) ⋆
                  (bytes cnf_ptr cnfBytes ⋆
                    dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
                      s_pre.core.d_cur s_pre.core.d_val ⋆
                    array64 (c.hdr + 32) (Full.hdrTailWords c s_hdr) ⋆ R)) m3 at hcomb
                unfold FullMem; rw [h_pre_ht]
                exact sep_ac hcomb
              obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17,
                o18, o19, o20, o21, o22, o23, o24, o25, o26, o27, o28, o29, o30, o31, o32, o33,
                o34, o35, o36, o37, o38, o39, o40, o41⟩ := arrs.ok
              have hlen_pre : s_pre.LengthsOk c :=
                ⟨⟨o1, o2, o3, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19, o20, o21, o22,
                  by simp [s_pre, hcv], by simp [s_pre, hcv]; omega, by simp [s_pre, hal],
                  by simp [s_pre, hwl]; exact hwcap_pos, by simp [s_pre, hte],
                  by simp [s_pre, hpr, hte], by simp [s_pre, htl], by simp [s_pre, hmcl]⟩,
                 ⟨o4, o5, o6, o7, o8, o23, o24, o25, o26, o27, o28, o29, o30, o31, o32, o33, o34,
                  o35, o36, o37, o38, o39, o40, o41⟩⟩
              apply wp_call_of_spec; apply hZt1
              change Full.fullZeroTables1Spec (c.hdr, ()) m3 _ _
              refine ⟨c, s_pre, bytes cnf_ptr cnfBytes ⋆ R, rfl, hlen_pre, hm_pre_full,
                fun wstk' mstk' repr' sc1 m4 hwstk' hmstk' hrepr' hsc1 hext1 hll1 hm4 => ?_⟩
              let s_1 : FullState :=
                { s_pre with
                  core := {
                    s_pre.core with
                    vals := List.replicate (2 * c.max_vars) 0#8,
                    lit_mark := List.replicate (2 * c.max_vars) 0#8,
                    wvec := List.replicate (4 * c.max_vars) 0#32, wstk := wstk',
                    min_stk := mstk', repr := repr' },
                  scratch := sc1 }
              have hlen1 : s_1.LengthsOk c :=
                ⟨{
                  hlen_pre.core_ok with
                  vals_len := by simp [s_1], lit_mark_len := by simp [s_1],
                  wvec_len := by simp [s_1], repr_len := hrepr', min_stk_len := hmstk',
                  wstk_len_arr := hwstk' }, hsc1⟩
              apply wp_call_of_spec; apply hZt2
              change Full.fullZeroTables2Spec (c.hdr, ()) m4 _ _
              refine ⟨c, s_1, bytes cnf_ptr cnfBytes ⋆ R, rfl, hlen1, hm4,
                fun flags' fdec' sc2 m5 hfl' hfd' hsc2 hpres2 hm5 => ?_⟩
              dsimp only; rw [wp_ret]
              let s_2 : FullState :=
                { s_1 with
                  core := {
                    s_1.core with
                    mrk := List.replicate c.max_vars 0#8, flags := flags',
                    lvl := List.replicate c.max_vars 0#32,
                    rsns := List.replicate c.max_vars 0xFFFFFFFF#32,
                    frame_trail := List.replicate (c.max_vars + 1) 0#32,
                    frame_dec := fdec' },
                  scratch := sc2 }
              have hlen2 : s_2.LengthsOk c :=
                ⟨{
                  hlen1.core_ok with
                  mrk_len := by simp [s_2], flags_len := hfl', lvl_len := by simp [s_2],
                  rsns_len := by simp [s_2], frame_trail_len := by simp [s_2],
                  frame_dec_len := hfd' }, hsc2⟩
              have hll2 : ∀ i < 8, s_2.scratch.last_learned[i]?.getD 0xFFFFFFFF#32 =
                  0xFFFFFFFF#32 := fun i hi8 => by
                dsimp only [s_2]; rw [hpres2.1]; exact last_learned_getD_ff_of_zero hll1 i hi8
              have hext2 : s_2.scratch.extend_len = 0 := by
                dsimp only [s_2]; rw [hpres2.2, hext1]; exact hel
              have hft0 : (s_2.core.frame_trail[0]?.getD 0#32).toNat = 0 := by simp [s_2]
              have hinv2 := Full.fullInv_init_sparse (F0 := shiftDownCnf CNF.empty) hlen2
                hinc hal rfl hte hcl hft0 rfl rfl rfl hll2 hext2 hdm
              rw [sep_comm_l, ← sep_assoc] at hm5
              exact hQtrue c s_2 j rest m5 rfl rfl hhdr hj hdrop hinv2 hcv rfl hal hwl hte hpr hcl
                hfu hunf hpb hmcl hmcf hoom hinc rfl rfl rfl rfl hext2 hm5
          · intro Jg hJg; fp_head_steps
            rw [hdel_mul, hshl2_e, hshl2_s, show (40 : BitVec 64) = BitVec.ofNat 64 40 from rfl,
              show (136 : BitVec 64) = BitVec.ofNat 64 136 from rfl, bv64_mul_nat3, hnc_to,
              show BitVec.ofNat 64 (12 * del_cap) + BitVec.ofNat 64 (4 * ecap_v.toNat) +
                BitVec.ofNat 64 (4 * scap_v.toNat) =
                BitVec.ofNat 64 (12 * del_cap + 4 * ecap_v.toNat + 4 * scap_v.toNat) by
                repeat rw [bv_add_ofNat],
              bv_add_ofNat, bv_add_ofNat, bv_ult_eq (by have := avail.isLt; omega)
                (by unfold dimacsBound at *; omega)]
            refine wp_jnz_of (fun hdlt => ?_) (fun hdge => ?_)
            · m5_fp_jnz_t' hdlt
              exact hJg (0#64, 0#64, BitVec.ofNat 64 (12 * del_cap), ()) md
                ⟨0, 0, by unfold dimacsBound; omega, by unfold dimacsBound; omega,
                  rfl, rfl, rfl, hbr_lt hdlt, rfl⟩
            · m5_fp_jnz_f' hdge
              exact hJg (ecap_v, scap_v, _, ()) md ⟨ecap_v.toNat, scap_v.toNat, hecap_lt,
                hscap_lt, hecap_bv.symm, hscap_bv.symm, rfl, hbr_ge hdge, rfl⟩
        · intro Jd hJd; fp_head_steps
          rw [show (524288 : BitVec 64) = BitVec.ofNat 64 524288 from rfl,
            bv_ule_eq (by decide) (by have := avail.isLt; omega)]
          refine wp_jnz_of (fun hbig => ?_) (fun hsmall => ?_)
          · m5_fp_jnz_t' hbig; refine hJd (4096#64, ()) m0 ⟨?_, rfl⟩
            simp [del_cap, fullInitDelCap, rem, hbig]
          · m5_fp_jnz_f' hsmall; refine hJd (8#64, ()) m0 ⟨?_, rfl⟩
            simp [del_cap, fullInitDelCap, rem, hsmall]

end CapsAndInitProofs

/-! ## 2. Effort Floors (`10M` `mineffort`): `probe_dticks` & `elim_dticks` -/

section DticksProofs

open scoped Full.FullArenaTactics

/-- Parametric `Func.wp` theorem for `full_probe_dticks_m5` (`10M` floor) against canonical
`FullFastSched.schedProbeDticksSpec`. -/
theorem full_probe_dticks_m5_wp (Γ : Env)
    (hMax : ∀ a m Q X, FullFastSched.schedMaxU64Spec a m Q X →
      Γ "full_max_u64" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, FullFastSched.schedProbeDticksSpec a m Q X →
      Func.wp Γ full_probe_dticks_m5_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, _, hm, hQ⟩
  unfold Func.wp full_probe_dticks_m5_body; c0_hsteps_nogrp
  refine wp_join_state_pure (α := BitVec 64) (fun r => (r, ())) (fun _ => True)
    (fun _ raw _ => by
      c0_hsteps_nogrp
      refine wp_join_state_pure (α := BitVec 64) (fun dt => (dt, ())) (fun _ => True)
        (fun _ dt _ => by c0_hsteps; c0_call hMax; intro r _; c0_hsteps; exact hQ r)
        (fun J2 hJ2 => by c0_hsteps <;> exact hJ2 _ trivial))
    (fun J1 hJ1 => by c0_hsteps <;> exact hJ1 _ trivial)

/-- Parametric `Func.wp` theorem for `full_elim_dticks_m5` (`10M` floor) against canonical
`FullFastSched.schedElimDticksSpec`. -/
theorem full_elim_dticks_m5_wp (Γ : Env)
    (hMax : ∀ a m Q X, FullFastSched.schedMaxU64Spec a m Q X →
      Γ "full_max_u64" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, FullFastSched.schedElimDticksSpec a m Q X →
      Func.wp Γ full_elim_dticks_m5_body a m Q X := by
  rintro ⟨h, initial, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, _, hm, hQ⟩
  unfold Func.wp full_elim_dticks_m5_body; c0_hsteps_nogrp
  refine wp_join_state_pure (α := BitVec 64) (fun r => (r, ())) (fun _ => True)
    (fun _ raw _ => by
      c0_hsteps_nogrp
      refine wp_join_state_pure (α := BitVec 64) (fun dt => (dt, ())) (fun _ => True)
        (fun _ dt _ => by c0_hsteps; c0_call hMax; intro r _; c0_hsteps; exact hQ r)
        (fun J2 hJ2 => by c0_hsteps <;> exact hJ2 _ trivial))
    (fun J1 hJ1 => by c0_hsteps <;> exact hJ1 _ trivial)

end DticksProofs

/-! ## 3. Transitive Reduction (`dst > src` & `ant_sz` inside BFS) -/

section TransitiveProofs

open Full.FullTransHelpers
open scoped Full.FullArenaTactics Full.FullTransTactics

private def m5WithAntSz (st : FullState) (asz : BitVec 64) : FullState :=
  { st with scratch := { st.scratch with ant_sz := asz } }

private theorem m5_withAntSz_self (st : FullState) : m5WithAntSz st st.scratch.ant_sz = st := rfl

private theorem m5_trans_unroll_ant_sz {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st_pre st : FullState} {src saved : Nat} (a : BitVec 64)
    (h : TransUnrollInv c F0 F_cur s0 (m5WithAntSz st_pre st.scratch.ant_sz) src saved st) :
    TransUnrollInv c F0 F_cur s0 (m5WithAntSz st_pre a) src saved (m5WithAntSz st a) :=
  { len_ok := ⟨h.len_ok.core_ok,
      { h.len_ok.scratch_ok with walk_vals_len := h.len_ok.scratch_ok.walk_vals_len }⟩
    same_core := h.same_core
    same_scratch := by
      unfold m5WithAntSz at *
      rw [h.same_scratch]
    saved_eq := h.saved_eq
    saved_le_te := h.saved_le_te
    trl_pres := h.trl_pres
    vals_pres := h.vals_pres
    vals_hi_pres := h.vals_hi_pres
    bfs_trl_inv := h.bfs_trl_inv
    bfs_vars_nodup := h.bfs_vars_nodup
    vals_only_trl := h.vals_only_trl }

private theorem m5_trans_vals_ff_of_domain {v : BitVec 8} {z : BitVec 32}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) (hz : z = 0#32)
    (hslt : (v.signExtend 32).slt z = true) : v = 0xFF#8 := by
  subst hz; rcases hdom with rfl | rfl | rfl <;> first | rfl | exact absurd hslt (by decide)

private theorem m5_trans_vals_zero_of_domain {v : BitVec 8} {z : BitVec 32}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) (hz : z = 0#32) (heq : v.signExtend 32 = z) :
    v = 0#8 := by
  subst hz; rcases hdom with rfl | rfl | rfl <;> first | rfl | exact absurd heq (by decide)

private theorem m5_of_reduced0_full {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off p end_v : Nat} {st : FullState}
    (hsp0 : FullSparseInv c F0 s0) (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (h : TransOuterInv c F0 F_cur s0 src off p end_v 0 st) :
    FullSparseInv c F0 st ∧ FullWitnessInv c F0 F_cur st.core :=
  have hcl : WatchSliceOk F_cur st.core src
      (fullWatchOffCore st.core src) (fullWatchSizeCore st.core src) := by
    rw [h.base.src_off, h.base.src_sz]; exact h.src_full_tomb.to_watchSlice
  ⟨h.base.toSparse hsp0 hw0 hcl, h.base.toWitness_of_src_clean hw0 hcl⟩

private theorem m5_del_side_and_tomb {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off p end_v reduced dst : Nat} {st_r st' : FullState} {w0 : BitVec 32}
    {wvec' wstk' : List (BitVec 32)} {wu' tc' : BitVec 64}
    (hto : TransOuterInv c F0 F_cur s0 src off p end_v reduced st_r) (hp_lt : p < end_v)
    (hp_wc : p < c.wcap) (hs_lt : src < 2 * st_r.core.cur_vars)
    (hd_lt : dst < 2 * st_r.core.cur_vars) (hd_ne : dst ≠ src)
    (hget : st_r.core.wstk[p]? = some w0) (hfl : (w0 &&& 0x80000000#32) ≠ 0#32)
    (hst' : st' = { st_r with
      core := { st_r.core with wvec := wvec', wstk := wstk', wusable := wu' } })
    (hl' : st'.LengthsOk c) (hws : fullWatchOff st' dst = fullWatchOff st_r dst ∧
      fullWatchSize st' dst ≤ fullWatchSize st_r dst)
    (hows : ∀ l < 2 * st_r.core.cur_vars, l ≠ dst →
      fullWatchOff st' l = fullWatchOff st_r l ∧ fullWatchSize st' l = fullWatchSize st_r l)
    (hout : ∀ i < c.wcap, (i < fullWatchOff st_r dst ∨
      fullWatchOff st_r dst + fullWatchSize st_r dst ≤ i) → wstk'[i]? = st_r.core.wstk[i]?)
    (hsl : WatchSliceOk F_cur st_r.core dst (fullWatchOff st_r dst) (fullWatchSize st_r dst) →
      WatchSliceOk F_cur st'.core dst (fullWatchOff st' dst) (fullWatchSize st' dst)) :
    TransOuterInv c F0 F_cur s0 src off (p + 1) end_v (reduced + 1) { st' with
      core := { st'.core with wstk := wstk'.set p 0xFFFFFFFF#32 },
      scratch := { st_r.scratch with trans_cnt := tc' } } := by
  subst hst'
  have hp_out : p < fullWatchOff st_r dst ∨ fullWatchOff st_r dst + fullWatchSize st_r dst ≤ p := by
    by_cases hdz : fullWatchSize st_r dst = 0; · dsimp only [fullWatchSize] at hdz ⊢; omega
    rcases hto.base.disjoint_all src dst hs_lt hd_lt hd_ne.symm
        (by rw [hto.base.src_sz]; have := hto.off_le_p; omega) (Nat.pos_of_ne_zero hdz) with
      h1 | h2
    · left; have := hto.base.src_off; have := hto.base.src_sz; dsimp only [fullWatchOff]; omega
    · right; have := hto.off_le_p; have := hto.base.src_off
      dsimp only [fullWatchOff, fullWatchSize]; omega
  exact (hto.of_delete_bin_side hs_lt hd_lt hd_ne rfl hl' hws hows hout hsl).mark_tomb
    hp_lt hs_lt ((hout p hp_wc hp_out).trans hget) hfl

private theorem m5_ft_bnds {c : FullCfg} {k : FullCoreState} (hl : k.LengthsOk c) :
    2 * k.cur_vars + 1 < 2 ^ 30 ∧ k.wlen ≤ c.wcap ∧ k.wlen < 2 ^ 64 ∧ k.trail_end < 2 ^ 64 := by
  have := hl.cur_vars_le; have := hl.wlen_le; have := hl.trail_end_le
  have := c.hmaxv; have := c.hwcap; unfold dimacsBound at *; omega

private theorem m5_ft_wstk_lt {c : FullCfg} {k : FullCoreState} {p end_v : Nat}
    (hl : FullCoreState.LengthsOk c k) (hp : p < end_v) (he : end_v ≤ k.wlen) :
    p < k.wstk.length := by rw [hl.wstk_len_arr]; have := hl.wlen_le; omega

private theorem m5_ft_vals_lt {c : FullCfg} {k : FullCoreState} {l : Nat}
    (hl : FullCoreState.LengthsOk c k) (h : l < 2 * k.cur_vars) :
    l < k.vals.length := by rw [hl.vals_len]; have := hl.cur_vars_le; omega

private theorem m5_ft_getElem_toNat {xs : List (BitVec 32)} {i : Nat} (hi : i < xs.length) :
    (xs[i]'hi).toNat = (xs[i]?.getD 0#32).toNat := by simp [List.getElem?_eq_getElem hi]

private theorem m5_tomb_step_non_large {F_cur : List (List Nat)} {k : FullCoreState}
    {nl q lend nt : Nat} {qw : BitVec 32} (hq : q < lend) (hg : k.wstk[q]? = some qw)
    (hfl : (qw &&& 0x80000000#32) ≠ 0#32) (ht : TombWatchSliceOk F_cur k nl q (lend - q) nt) :
    ∃ nt2, TombWatchSliceOk F_cur k nl (q + 1) (lend - (q + 1)) nt2 := by
  have hs := ht.inv_step (by omega) hg; simp only [hfl, ↓reduceIte] at hs
  by_cases hq_t : qw = 0xFFFFFFFF#32 <;> simp only [hq_t, ↓reduceIte] at hs
  · exact ⟨nt - 1, by have hs2 := hs.2; rwa [show lend - q - 1 = lend - (q + 1) by omega] at hs2⟩
  · exact ⟨nt, by have hs3 := hs.2.2; rwa [show lend - q - 1 = lend - (q + 1) by omega] at hs3⟩

private theorem m5_ft_bv32_ofNat_toNat (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by simp

private theorem m5_ft_bv64_sub_sz (a b r : BitVec 64) {bn rn : Nat}
    (hb : b.toNat = bn) (hr : r.toNat = rn) (h : rn ≤ bn) (hbn : bn < 2 ^ 32) :
    BitVec.setWidth 32 (a + b - a - r) = BitVec.ofNat 32 (bn - rn) := by
  apply BitVec.eq_of_toNat_eq; have : (a + b - a - r).toNat = bn - rn := by bv_omega
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, this, Nat.mod_eq_of_lt (by omega)]

private theorem m5_ft_bv64_sub1' {n : Nat} (hn1 : 0 < n) (hn2 : n < 2 ^ 64) :
    (BitVec.ofNat 64 n - 1#64).toNat = n - 1 := by bv_omega

private theorem m5_ft_bv64_lt_eq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a < BitVec.ofNat 64 b) ↔ a < b := by bv_omega

private theorem m5_ft_compact_done_eq {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off end_v reduced : Nat} {wu' nb_bv : BitVec 64} {idx : Nat}
    {new_sz : BitVec 32} {st : FullState} (hsp0 : FullSparseInv c F0 s0)
    (hw0 : FullWitnessInv c F0 F_cur s0.core) (hb : TransOuterBase c F0 F_cur s0 src off end_v st)
    (hsrc_lt : src < 2 * st.core.cur_vars) (hred : reduced ≤ end_v - off)
    (hsl : WatchSliceOk F_cur st.core src off (end_v - off - reduced)) (hidx : idx = 2 * src + 1)
    (hsz : new_sz = BitVec.ofNat 32 (end_v - off - reduced)) :
    let st' := { st with core :=
      { st.core with wvec := st.core.wvec.set idx new_sz, wusable := wu', num_binary := nb_bv } }
    FullSparseInv c F0 st' ∧ FullWitnessInv c F0 F_cur st'.core := by
  subst hidx; subst hsz; have hnb : ((nb_bv.toNat : Nat) : BitVec 64) = nb_bv := by simp
  simpa only [hnb] using
    hb.of_compact_done_full hsp0 hw0 hsrc_lt hred hsl (wu' := wu') (nb' := nb_bv.toNat)

private theorem m5_ft_unroll_c0_aux {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st_pre st_r : FullState} {src saved : Nat} (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hpre_vals : st_pre.core.vals = s0.core.vals)
    (hpre_cv : st_pre.core.cur_vars = s0.core.cur_vars)
    (hlen_pre : st_pre.LengthsOk c) (hu_r : TransUnrollInv c F0 F_cur s0 st_pre src saved st_r)
    (hte_gt : saved < st_r.core.trail_end) (hte_r_lt : st_r.core.trail_end < 2 ^ 64) :
    let idx := (BitVec.ofNat 64 (BitVec.ofNat 64 st_r.core.trail_end - 1#64).toNat).toNat
    ∃ hidx : idx < st_r.core.trl.length, let ul := st_r.core.trl[idx]'hidx
      (BitVec.setWidth 64 ul).toNat < st_r.core.vals.length ∧
      (BitVec.setWidth 64 (ul ^^^ 1#32)).toNat < st_r.core.vals.length ∧
      (BitVec.ofNat 64 st_r.core.trail_end - 1#64).toNat = st_r.core.trail_end - 1 ∧
      TransUnrollInv c F0 F_cur s0 st_pre src saved { st_r with core := { st_r.core with
        vals := (st_r.core.vals.set (BitVec.setWidth 64 ul).toNat 0#8).set
          (BitVec.setWidth 64 (ul ^^^ 1#32)).toNat 0#8,
        trail_end := (BitVec.ofNat 64 st_r.core.trail_end - 1#64).toNat } } := by
  have hlen_r := hu_r.len_ok
  obtain ⟨ul, hul_get, hul_lt, hu_r'⟩ := hu_r.unroll_step hw0 hpre_vals hpre_cv hlen_pre hte_gt
  have hcv_r : st_pre.core.cur_vars ≤ c.max_vars := by
    have := hlen_r.core_ok.cur_vars_le; rw [hu_r.same_core] at this; exact this
  have hte1_bv := m5_ft_bv64_sub1' (n := st_r.core.trail_end) (by omega) hte_r_lt
  have hul_vlen := m5_ft_vals_lt (l := ul.toNat) hlen_r.core_ok
    (by rw [hu_r.same_core]; exact hul_lt)
  have huln_vlen := m5_ft_vals_lt (l := (ul ^^^ 1#32).toNat) hlen_r.core_ok
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

/-- Parametric `Func.wp` theorem for `full_trans_lit_m5` (`dst > src` & `ant_sz` inside BFS)
against canonical `Full.fullTransLitSpec`. -/
theorem full_trans_lit_m5_wp (Γ : Env)
    (h_del_bin : ∀ args m Q X, Full.fullDeleteBinSideSpec args m Q X →
      Γ "full_delete_bin_side" [i64, i32, i32] [] args m Q X)
    (h_add_unit : ∀ args m Q X, Full.fullAddUnitSpec args m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] args m Q X) :
    ∀ args m Q X, Full.fullTransLitSpec args m Q X →
      Func.wp Γ full_trans_lit_m5_body args m Q X := by
  rintro ⟨h, src, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hcl0, hsrc_lt, hm, hQ⟩
  unfold full_trans_lit_m5_body; ft_unmdata
  obtain ⟨F_cur, hw0⟩ := hsp.1.witness; have hlen0 := hsp.1.lengths
  have hsrc_vlen := m5_ft_vals_lt hlen0.core_ok hsrc_lt
  ft_split; · ft_steps; exact hQ true s m hsp hcl0 rfl rfl (fun hf => absurd hf (by decide)) hm
  have hsrc0 : s.core.vals[src.toNat]?.getD 0#8 = 0#8 := m5_trans_vals_zero_of_domain (z := 0#32)
    (hw0.vals_domain src.toNat hsrc_lt) rfl (by simpa [List.getElem?_eq_getElem hsrc_vlen] using
      ‹BitVec.signExtend 32 s.core.vals[BitVec.toNat src] = 0#32›)
  have hcv_lt : 2 * s.core.cur_vars < 2 ^ 32 := by have := (m5_ft_bnds hlen0.core_ok).1; omega
  have hsrc64 : (src.setWidth 64 <<< (1 : Nat)).toNat = 2 * src.toNat := by
    rw [ft_bv64_shl1 (by rw [ft_bv32_setWidth64]; omega), ft_bv32_setWidth64]
  have hsrc64_1 : ((src.setWidth 64 <<< (1 : Nat)) + 1#64).toNat = 2 * src.toNat + 1 := by
    rw [ft_bv64_add1 (by rw [hsrc64]; omega), hsrc64]
  let off := fullWatchOff s src.toNat; let sz := fullWatchSize s src.toNat; let end_v := off + sz
  have hws_b : end_v ≤ s.core.wlen := by
    have hwm := hw0.watches; unfold ModeWatchesInv at hwm
    simp only [hsp.2.2.2.2, ↓reduceIte] at hwm; exact hwm.layout.bounds src.toNat hsrc_lt
  have hwv_b : 2 * src.toNat + 1 < s.core.wvec.length := by
    rw [hlen0.core_ok.wvec_len]; have := hlen0.core_ok.cur_vars_le; omega
  have hwc_lt : c.wcap < 2 ^ 64 := by have := c.hwcap; unfold dimacsBound at *; omega
  have hoff_lt : off < 2 ^ 32 := BitVec.isLt _; have hsz_lt : sz < 2 ^ 32 := BitVec.isLt _
  ft_split; · ft_steps; exact hQ true s m hsp hcl0 rfl rfl (fun hf => absurd hf (by decide)) hm
  have hmod1 : (2 * src.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = 2 * src.toNat + 1 := by
    rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hsz_pos : 0 < sz := by
    have hc0 : ¬BitVec.setWidth 64 (s.core.wvec[(2 * src.toNat + BitVec.toNat (1 : BitVec 64)) %
        2 ^ 64]'(by rw [hmod1]; exact hwv_b)) = 0 := ‹_›
    have hsz_eq : (s.core.wvec[(2 * src.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'
        (by rw [hmod1]; exact hwv_b)).toNat = sz := by
      simp only [hmod1]; exact m5_ft_getElem_toNat hwv_b
    exact Nat.pos_of_ne_zero fun hz =>
      hc0 (BitVec.eq_of_toNat_eq (by rw [ft_bv32_setWidth64, hsz_eq, hz]; rfl))
  have hend_lt : end_v < 2 ^ 64 := by have := (m5_ft_bnds hlen0.core_ok).2.1; omega
  ft_to_group; have hw0_b2 : 2 * src.toNat < s.core.wvec.length := by omega
  have hmod0 : 2 * src.toNat % 2 ^ 64 = 2 * src.toNat := Nat.mod_eq_of_lt (by omega)
  have h_end_c0 : ((s.core.wvec[2 * src.toNat % 2 ^ 64]'(by rw [hmod0]; exact hw0_b2)).toNat +
      (s.core.wvec[(2 * src.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'
        (by rw [hmod1]; exact hwv_b)).toNat) % 2 ^ 64 = end_v := by
    simp only [hmod0, hmod1, m5_ft_getElem_toNat hw0_b2, m5_ft_getElem_toNat hwv_b]
    exact Nat.mod_eq_of_lt hend_lt
  have hof64 : (BitVec.ofNat 64 off).toNat = off := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hw0_b : (BitVec.setWidth 64 src <<< (1 : Nat)).toNat < s.core.wvec.length := by
    rw [hsrc64]; exact hw0_b2
  have h_off_arg : BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 src <<< (1 : Nat)).toNat]'
      hw0_b) = BitVec.ofNat 64 off := BitVec.eq_of_toNat_eq (by
    rw [ft_bv32_setWidth64, hof64]; simp only [hsrc64]; exact m5_ft_getElem_toNat hw0_b2)
  refine wp_loop_group (ts := [Ty.bool, i64, i64])
    (Inv := fun n xs m' => let failed := xs.1; let reduced := xs.2.1; let p := xs.2.2.1
      ∃ st : FullState, off ≤ p.toNat ∧ p.toNat ≤ end_v ∧ n = end_v - p.toNat ∧
        reduced.toNat ≤ p.toNat - off ∧
        TransOuterInv c F0 F_cur s src.toNat off p.toNat end_v reduced.toNat st ∧
        (failed = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat])) ∧
        st.core.cur_vars = s.core.cur_vars ∧ st.core.fuel = s.core.fuel ∧
        (FullMem c st ⋆ R) m') ?_ ?_
  rotate_left
  · intro L hL; ft_steps; rw [h_off_arg]
    have hto0 := TransOuterInv.init hlen0 hw0 hsp.2.2.2.2 hcl0 hsrc_lt hsz_pos
    exact hL (end_v - off) (false, 0#64, BitVec.ofNat 64 off, ()) m ⟨s,
      (by dsimp only; rw [hof64]; exact Nat.le_refl _),
      (by dsimp only; rw [hof64]; exact Nat.le_add_right off sz), (by dsimp only; rw [hof64]),
      (by dsimp only; simp), (by dsimp only; rw [hof64]; exact hto0),
      (by dsimp only; intro h; cases h), rfl, rfl, hm⟩
  rintro L n ⟨failed, reduced, p, ⟨⟩⟩ m1 hL
    ⟨st, hp_lo, hp_hi, hneq, hred_le, hto, hfail_ent, hcv_st, hfuel_st, hm1⟩
  dsimp only at hp_lo hp_hi hneq hred_le hto hfail_ent; have hlen_st := hto.base.len_ok
  refine wp_join_group (P := fun _ m2 => ∃ st2 : FullState,
      TransOuterInv c F0 F_cur s src.toNat off p.toNat end_v reduced.toNat st2 ∧
      (failed = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat])) ∧
      st2.core.cur_vars = s.core.cur_vars ∧ st2.core.fuel = s.core.fuel ∧
      (FullMem c st2 ⋆ R) m2) ?_ ?_
  · intro J4 ⟨⟩ m2 ⟨st2, hto2, hfail2, hcv2, hfuel2, hm2⟩; have hlen2 := hto2.base.len_ok
    refine wp_join_group (P := fun _ m3 => ∃ stf : FullState, FullSparseInv c F0 stf ∧
        FullWitnessInv c F0 F_cur stf.core ∧ stf.core.cur_level = 0 ∧
        stf.core.cur_vars = s.core.cur_vars ∧ stf.core.fuel = s.core.fuel ∧
        (failed = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat])) ∧
        (FullMem c stf ⋆ R) m3) ?_ ?_
    · rintro J6 ⟨_, ⟨⟩⟩ m3 ⟨stf, hspf, hwf, hclf, hcvf, hfuelf, hfailf, hm3⟩
      have hlenf := hspf.1.lengths; ft_split; rotate_left
      · ft_steps; exact hQ true stf m3 hspf hclf hcvf hfuelf (fun h => absurd h (by decide)) hm3
      ft_to_group; ft_call h_add_unit
      obtain ⟨hsp_tc, hw_tc⟩ := fullSparseInv_with_trans_cnt hspf hwf (stf.scratch.trans_cnt + 1#64)
      refine ⟨c, F0, F_cur, _, R, rfl, hsp_tc.1.lengths, hw_tc, fun _ => hfailf ‹_›, ‹_›,
        fun ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
          phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss' m4 hlen4 hw4 hcl4 huns4 _ hm4 => ?_⟩
      let st_au : FullState := { stf with
        core := { stf.core with
          vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
          trail_end := te', propagated := prop', cur_level := cl', unassigned := unass',
          unflushed := unfl', inconsistent := inc' },
        scratch := { stf.scratch with
          trans_cnt := stf.scratch.trans_cnt + 1#64, phases := phases', target_assigned := ta',
          best_assigned := ba', phases_target := pt', phases_best := pb', heap := hp', pos := ps',
          heap_len := hl', q_search_idx := qsi', q_search_stamp := qss' } }
      exact hQ ok st_au m4 (fullAddUnit_sparse hsp_tc rfl hlen4 hw4) hcl4 hcvf hfuelf
        (fun hok => (huns4 (by dsimp only [Arg.val_var] at *; omega) hok).1) hm4
    intro J6 hJ6; ft_split; rotate_left
    · have hred0 : reduced.toNat = 0 := by bv_omega
      ft_steps; rw [hred0] at hto2; obtain ⟨hsp2, hw2⟩ := m5_of_reduced0_full hsp hw0 hto2
      exact hJ6 (p, ()) m2 ⟨st2, hsp2, hw2, hto2.base.core_pres.2.1, hcv2, hfuel2, hfail2, hm2⟩
    ft_to_group; have hred_pos : 0 < reduced.toNat := by bv_omega
    refine wp_loop_group (ts := [i64, i64])
      (Inv := fun nc xs m3 => let pc := xs.1; let qc := xs.2.1
        ∃ stc : FullState, off ≤ qc.toNat ∧ qc.toNat ≤ pc.toNat ∧ pc.toNat ≤ end_v ∧
          nc = end_v - pc.toNat ∧
          TransCompactInv c F0 F_cur s src.toNat off qc.toNat pc.toNat end_v reduced.toNat stc ∧
          stc.core.cur_vars = s.core.cur_vars ∧ stc.core.fuel = s.core.fuel ∧
          (FullMem c stc ⋆ R) m3) ?_ ?_
    · rintro L8 nc ⟨pc, qc, ⟨⟩⟩ m3 hL8 ⟨stc, hql, hqp, hpe, hcneq, hci, hcvc, hfuelc, hm3⟩
      dsimp only at hql hqp hpe hcneq hci; have hlenc := hci.base.len_ok; ft_split
      · have hpc_lt : pc.toNat < end_v := by have := h_end_c0; omega
        have hpc_len := m5_ft_wstk_lt hlenc.core_ok hpc_lt hci.base.end_le_wlen
        have hpc1 : (pc + 1#64).toNat = pc.toNat + 1 := ft_bv64_add1 (by omega); ft_split
        · have ht_pc : stc.core.wstk[pc.toNat]? = some 0xFFFFFFFF#32 := by
            rw [List.getElem?_eq_getElem hpc_len]; exact congrArg some ‹_›
          ft_steps; refine hL8 (end_v - (pc.toNat + 1)) (pc + 1#64, qc, ()) m3 (by omega)
            ⟨stc, hql, by dsimp only; rw [hpc1]; omega, by dsimp only; rw [hpc1]; omega,
              by dsimp only; rw [hpc1],
              by dsimp only; rw [hpc1]; exact hci.step_tomb hpc_lt ht_pc rfl, hcvc, hfuelc, hm3⟩
        have hsrc_c : src.toNat < 2 * stc.core.cur_vars := by rw [hcvc]; exact hsrc_lt
        ft_split
        · have hne_c : stc.core.wstk[pc.toNat] ≠ 0xFFFFFFFF#32 := ‹_›
          have hfl_c : (stc.core.wstk[pc.toNat] &&& 0x80000000#32) ≠ 0#32 := ‹_›
          have hqc1 : (qc + 1#64).toNat = qc.toNat + 1 := ft_bv64_add1 (by omega)
          have hci_b := hci.step_bin hpc_lt hsrc_c (List.getElem?_eq_getElem hpc_len) hne_c hfl_c
          rw [← hpc1, ← hqc1] at hci_b; ft_steps
          exact hL8 (end_v - (pc.toNat + 1)) (pc + 1#64, qc + 1#64, ()) _ (by omega)
            ⟨_, by dsimp only; rw [hqc1]; omega, by dsimp only; rw [hpc1, hqc1]; omega,
              by dsimp only; rw [hpc1]; omega, by dsimp only; rw [hpc1],
              hci_b, hcvc, hfuelc, by assumption⟩
        have hfl0 : (stc.core.wstk[pc.toNat] &&& 0x80000000#32) = 0#32 := ‹_›
        obtain ⟨hp1_lt, w1, hw1_get, hci_l⟩ :=
          hci.step_large hpc_lt hsrc_c (List.getElem?_eq_getElem hpc_len) hfl0
        ft_split; rotate_left
        · exact False.elim (‹¬((pc + 1#64).toNat < _)› (by rw [hpc1, h_end_c0]; exact hp1_lt))
        have hpc2 := ft_bv64_add2 (by omega : pc.toNat + 2 < 2 ^ 64)
        have hqc2 := ft_bv64_add2 (by omega : qc.toNat + 2 < 2 ^ 64)
        have hqc1 := ft_bv64_add1 (by omega : qc.toNat + 1 < 2 ^ 64)
        have hpc1_len := m5_ft_wstk_lt (p := (pc + 1#64).toNat) hlenc.core_ok
          (by rw [hpc1]; exact hp1_lt) hci.base.end_le_wlen
        have hqc1_len := m5_ft_wstk_lt (p := (qc + 1#64).toNat) hlenc.core_ok
          (by rw [hqc1]; exact Nat.lt_of_lt_of_le (by omega) hp1_lt) hci.base.end_le_wlen
        ft_steps
        have hw1_hm : (stc.core.wstk.set qc.toNat stc.core.wstk[pc.toNat])[(pc + 1#64).toNat]'(
            by rw [List.length_set]; exact hpc1_len) = w1 := by
          rw [List.getElem_set_ne (by omega : qc.toNat ≠ (pc + 1#64).toNat)]
          exact Option.some.inj
            ((List.getElem?_eq_getElem hpc1_len).symm.trans (by rw [hpc1, hw1_get]))
        rw [← hpc2, ← hqc2, ← hqc1, ← hw1_hm] at hci_l
        exact hL8 (end_v - (pc.toNat + 2)) (pc + 2#64, qc + 2#64, ()) _ (by omega)
          ⟨_, by dsimp only; rw [hqc2]; omega, by dsimp only; rw [hpc2, hqc2]; omega,
            by dsimp only; rw [hpc2]; omega, by dsimp only; rw [hpc2], hci_l, hcvc, hfuelc,
            by assumption⟩
      have hpc_end : pc.toNat = end_v := by have := h_end_c0; omega
      rw [hpc_end] at hci; obtain ⟨hq_eq, hq_lo, hq_hi, hsl⟩ := hci.at_end; ft_to_group
      refine wp_loop_group (ts := [i64])
        (Inv := fun nq xs m4 => let qf := xs.1
          ∃ stq : FullState, off ≤ end_v - reduced.toNat ∧ end_v - reduced.toNat ≤ qf.toNat ∧
            qf.toNat ≤ end_v ∧ nq = end_v - qf.toNat ∧
            TransOuterBase c F0 F_cur s src.toNat off end_v stq ∧
            WatchSliceOk F_cur stq.core src.toNat off (end_v - off - reduced.toNat) ∧
            stq.core.cur_vars = s.core.cur_vars ∧ stq.core.fuel = s.core.fuel ∧
            (FullMem c stq ⋆ R) m4) ?_ ?_
      rotate_left
      · intro L11 hL11; ft_steps; exact hL11 (end_v - qc.toNat) (qc, ()) m3 ⟨stc, hq_lo,
          by dsimp only; rw [hq_eq]; exact Nat.le_refl _,
          by dsimp only; rw [hq_eq]; exact hq_hi, rfl, hci.base, hsl, hcvc, hfuelc, hm3⟩
      rintro L11 nq ⟨qf, ⟨⟩⟩ m4 hL11 ⟨stq, hqo, hql2, hqh, hqneq, hbq, hslq, hcvq, hfuelq, hm4⟩
      dsimp only at hqo hql2 hqh hqneq hbq hslq; have hlenq := hbq.len_ok
      have hsrc_q : src.toNat < 2 * stq.core.cur_vars := by rw [hcvq]; exact hsrc_lt
      ft_split
      · have hq_lt : qf.toNat < end_v := by have := h_end_c0; omega
        have hqf_len := m5_ft_wstk_lt hlenq.core_ok hq_lt hbq.end_le_wlen
        ft_steps; have hq1 : (qf + 1#64).toNat = qf.toNat + 1 := ft_bv64_add1 (by omega)
        obtain ⟨hbq', hslq'⟩ := hbq.sentinel_fill_step hsrc_q ⟨hqo, hql2, hq_lt⟩
          (by rwa [show (end_v - reduced.toNat) - off = end_v - off - reduced.toNat by omega])
        exact hL11 (end_v - (qf.toNat + 1)) (qf + 1#64, ()) _ (by omega) ⟨_, hqo,
          by dsimp only; rw [hq1]; omega, by dsimp only; rw [hq1]; omega, by dsimp only; rw [hq1],
          hbq', by simpa only [(show end_v - reduced.toNat - off =
            end_v - off - reduced.toNat by omega)] using hslq', hcvq, hfuelq, by assumption⟩
      have hred_off : reduced.toNat ≤ end_v - off := by omega
      have hw1_b : (BitVec.setWidth 64 src <<< (1 : Nat) + 1#64).toNat < s.core.wvec.length := by
        rw [hsrc64_1]; exact hwv_b
      have hq_wv1 : (BitVec.setWidth 64 src <<< 1 + 1#64).toNat < stq.core.wvec.length := by
        rw [hsrc64_1, hlenq.core_ok.wvec_len, ← hlen0.core_ok.wvec_len]; exact hwv_b
      have hclq : stq.core.cur_level = 0 := hbq.core_pres.2.1; have h_wsz_bv : BitVec.setWidth 32
          (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 src <<< (1 : Nat)).toNat]'hw0_b) +
            BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 src <<< (1 : Nat) + 1#64).toNat]'
              hw1_b) - BitVec.setWidth 64
              (s.core.wvec[(BitVec.setWidth 64 src <<< (1 : Nat)).toNat]'hw0_b) - reduced) =
          BitVec.ofNat 32 (end_v - off - reduced.toNat) := by
        have hb : (BitVec.setWidth 64 (s.core.wvec[(BitVec.setWidth 64 src <<< (1 : Nat) +
            1#64).toNat]'hw1_b)).toNat = sz := by
          rw [ft_bv32_setWidth64]; simp only [hsrc64_1]; exact m5_ft_getElem_toNat hwv_b
        rw [show end_v - off = sz from Nat.add_sub_cancel_left off sz]
        exact m5_ft_bv64_sub_sz _ _ reduced hb rfl (by omega) (by omega)
      ft_split
      · ft_steps; obtain ⟨hsp_d, hw_d⟩ := m5_ft_compact_done_eq hsp hw0 hbq hsrc_q hred_off hslq
          (wu' := stq.core.wusable + reduced) (nb_bv := stq.core.num_binary - reduced) hsrc64_1
          h_wsz_bv
        exact hJ6 (pc, ()) _ ⟨_, hsp_d, hw_d, hclq, hcvq, hfuelq, hfail2, by assumption⟩
      ft_steps; obtain ⟨hsp_d, hw_d⟩ := m5_ft_compact_done_eq hsp hw0 hbq hsrc_q hred_off hslq
        (wu' := stq.core.wusable + reduced) (nb_bv := stq.core.num_binary) hsrc64_1 h_wsz_bv
      exact hJ6 (pc, ()) _ ⟨_, hsp_d, hw_d, hclq, hcvq, hfuelq, hfail2, by assumption⟩
    intro L8 hL8; ft_steps; rw [h_off_arg]
    exact hL8 (end_v - off) (BitVec.ofNat 64 off, BitVec.ofNat 64 off, ()) m2 ⟨st2,
      (by dsimp only; rw [hof64]; exact Nat.le_refl _),
      (by dsimp only; rw [hof64]; exact Nat.le_refl _),
      by dsimp only; rw [hof64]; exact hto2.base.off_le_end, by dsimp only; rw [hof64],
      by dsimp only; rw [hof64]; exact TransCompactInv.init hto2, hcv2, hfuel2, hm2⟩
  intro J4 hJ4; have hst_cv_lt : st.core.cur_vars < 2 ^ 32 := by rw [hcv_st]; omega
  ft_split; rotate_left; · ft_steps; exact hJ4 () m1 ⟨st, hto, hfail_ent, hcv_st, hfuel_st, hm1⟩
  have hp_lt : p.toNat < end_v := by have := h_end_c0; omega
  ft_split; · ft_steps; exact hJ4 () m1 ⟨st, hto, hfail_ent, hcv_st, hfuel_st, hm1⟩
  have hfail_f : failed = false := by revert ‹_›; cases failed <;> simp
  ft_split; rotate_left; · ft_steps; exact hJ4 () m1 ⟨st, hto, hfail_ent, hcv_st, hfuel_st, hm1⟩
  have hp_len := m5_ft_wstk_lt hlen_st.core_ok hp_lt hto.base.end_le_wlen
  ft_split
  · have hfl0 : (st.core.wstk[p.toNat] &&& 0x80000000#32) = 0#32 := ‹_›
    obtain ⟨hp2, hto2⟩ := hto.skip_large hp_lt (List.getElem?_eq_getElem hp_len) hfl0
    ft_steps; have hp2_bv : (p + 2#64).toNat = p.toNat + 2 := ft_bv64_add2 (by omega)
    exact hL (end_v - (p.toNat + 2)) (failed, reduced, p + 2#64, ()) m1 (by omega) ⟨st,
      by dsimp only; rw [hp2_bv]; omega, by dsimp only; rw [hp2_bv]; omega,
      by dsimp only; rw [hp2_bv], by dsimp only; rw [hp2_bv]; omega,
      by dsimp only; rw [hp2_bv]; exact hto2, hfail_ent, hcv_st, hfuel_st, hm1⟩
  have hfl_nz : (st.core.wstk[p.toNat] &&& 0x80000000#32) ≠ 0#32 := ‹_›
  obtain ⟨hw0_ne, hdst_lt_st, hdst_ent, hto_skip⟩ :=
    hto.skip_bin hp_lt (List.getElem?_eq_getElem hp_len) hfl_nz
  let w0 := st.core.wstk[p.toNat]; let dst := w0 &&& 0x7FFFFFFF#32
  have hdst_lt0 : dst.toNat < 2 * s.core.cur_vars := by rw [← hcv_st]; exact hdst_lt_st
  refine wp_join_group (P := fun _ m2 => ∃ st_s : FullState,
      TransOuterInv c F0 F_cur s src.toNat off (p.toNat + 1) end_v reduced.toNat st_s ∧
      (failed = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat])) ∧
      st_s.core.cur_vars = s.core.cur_vars ∧ st_s.core.fuel = s.core.fuel ∧
      (FullMem c st_s ⋆ R) m2) ?_ ?_
  · rintro J9 ⟨⟩ m2 ⟨st_s, hto_s, hfail_s, hcv_s, hfuel_s, hm2⟩; ft_steps
    have hp1_bv : (p + 1#64).toNat = p.toNat + 1 := ft_bv64_add1 (by omega)
    exact hL (end_v - (p.toNat + 1)) (failed, reduced, p + 1#64, ()) m2 (by omega) ⟨st_s,
      by dsimp only; rw [hp1_bv]; omega, by dsimp only; rw [hp1_bv]; omega,
      by dsimp only; rw [hp1_bv], by dsimp only; rw [hp1_bv]; omega,
      by dsimp only; rw [hp1_bv]; exact hto_s, hfail_s, hcv_s, hfuel_s, hm2⟩
  intro J9 hJ9
  ft_split; · ft_steps; exact hJ9 () m1 ⟨st, hto_skip, hfail_ent, hcv_st, hfuel_st, hm1⟩
  ft_split; · ft_steps; exact hJ9 () m1 ⟨st, hto_skip, hfail_ent, hcv_st, hfuel_st, hm1⟩
  have hdst_ne : dst.toNat ≠ src.toNat := by
    have hng : ¬ dst.toNat ≤ src.toNat := by
      simpa [dst, w0, LeanQbe.T.lift2] using ‹¬ _ ≤ src.toNat›
    omega
  have hdst_vlen := m5_ft_vals_lt hlen_st.core_ok hdst_lt_st
  ft_split; · ft_steps; exact hJ9 () m1 ⟨st, hto_skip, hfail_ent, hcv_st, hfuel_st, hm1⟩
  have hdst0 : st.core.vals[dst.toNat]?.getD 0#8 = 0#8 := by
    have hv := hw0.vals_domain dst.toNat hdst_lt0
    rw [← hto.base.core_pres.2.2.2.2.2.2.2.2.2.2.1] at hv
    exact m5_trans_vals_zero_of_domain (z := 0#32) hv rfl (by
      rw [List.getElem?_eq_getElem hdst_vlen]
      exact ‹BitVec.signExtend 32 st.core.vals[dst.toNat] = 0#32›)
  let not_src := src ^^^ 1#32; have hnot_eq : not_src.toNat = src.toNat ^^^ 1 := ft_bv32_xor1 src
  have hnot_lt : not_src.toNat < 2 * st.core.cur_vars := by
    rw [hnot_eq, hcv_st]; exact litNeg_lt_two_mul hsrc_lt
  have hnot_vlen := m5_ft_vals_lt hlen_st.core_ok hnot_lt
  have hst_vals := hto.base.core_pres.2.2.2.2.2.2.2.2.2.2.1
  have hst_te := hto.base.core_pres.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hst_trl := hto.base.core_pres.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  let saved := st.core.trail_end
  obtain ⟨hsaved_lt, hu1, hte1⟩ := TransUnrollInv.init (st_pre := st) hw0 hlen_st
    hst_vals hst_te hcv_st (by rw [hcv_st]; exact hsrc_lt) (by rw [hst_vals]; exact hsrc0)
  have hte_len : saved < st.core.trl.length := by
    rw [hlen_st.core_ok.trl_len]; exact Nat.lt_of_lt_of_le hsaved_lt hlen_st.core_ok.cur_vars_le
  have hbv_not : BitVec.ofNat 32 (src.toNat ^^^ 1) = not_src := BitVec.eq_of_toNat_eq
    (by rw [hnot_eq, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega))
  have hsrc64_vlen : (BitVec.setWidth 64 src).toNat < st.core.vals.length := by
    rw [ft_bv32_setWidth64, hlen_st.core_ok.vals_len, ← hlen0.core_ok.vals_len]; exact hsrc_vlen
  have hsav_lt := (m5_ft_bnds hlen_st.core_ok).2.2.2
  have hte64_len : (BitVec.ofNat 64 st.core.trail_end).toNat < st.core.trl.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsav_lt]; exact hte_len
  ft_to_group; refine wp_loop_group (ts := [Ty.bool, i64, Ty.bool])
    (Inv := fun nb xs m2 => let fb := xs.1; let prop := xs.2.1; let tb := xs.2.2.1
      ∃ st_b : FullState, saved ≤ prop.toNat ∧ prop.toNat ≤ st_b.core.trail_end ∧
        nb = st.core.cur_vars - prop.toNat ∧
        TransUnrollInv c F0 F_cur s (m5WithAntSz st st_b.scratch.ant_sz) src.toNat saved st_b ∧
        ¬(fb = true ∧ tb = true) ∧
        (fb = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat])) ∧
        (tb = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat, dst.toNat])) ∧
        (FullMem c st_b ⋆ R) m2) ?_ ?_
  rotate_left
  · intro L13 hL13
    have hs_eq : (BitVec.ofNat 64 saved).toNat = saved := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsav_lt]
    have hnot_sw : (BitVec.setWidth 64 (BitVec.ofNat 32 (src.toNat ^^^ 1))).toNat =
        src.toNat ^^^ 1 := by
      rw [ft_bv32_setWidth64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have h1_sw : BitVec.setWidth 8 (1 : BitVec 32) = 1#8 := rfl
    have hsrc_sw : (BitVec.setWidth 64 src).toNat = src.toNat := ft_bv32_setWidth64 src
    have hff_sw : (BitVec.setWidth 8 (-1 : BitVec 32)) = 0xFF#8 := by decide
    have hte_p1 : (BitVec.ofNat 64 st.core.trail_end + 1).toNat = st.core.trail_end + 1 := by
      have hte_lt64 : (BitVec.ofNat 64 st.core.trail_end).toNat + 1 < 2 ^ 64 := by
        change (BitVec.ofNat 64 saved).toNat + 1 < 2 ^ 64; rw [hs_eq]
        have := (m5_ft_bnds hlen_st.core_ok).2.2.2; dsimp only [saved] at *; omega
      rw [show (1 : BitVec 64) = 1#64 from rfl, ft_bv64_add1 hte_lt64]
      exact congrArg (· + 1) hs_eq
    ft_steps; refine hL13 (st.core.cur_vars - saved) (failed, BitVec.ofNat 64 saved, false, ())
      _ ⟨_, by dsimp only; rw [hs_eq]; exact Nat.le_refl _, ?_, by dsimp only; rw [hs_eq], ?_,
        by dsimp only; simp [hfail_f], fun hf => by dsimp only at hf; simp [hfail_f] at hf,
        fun ht => False.elim (Bool.noConfusion ht), by assumption⟩
    · rw [hs_eq, hte_p1]; exact Nat.le_of_lt hte1
    · dsimp only [not_src] at hbv_not
      rw [show (1#32 : BitVec 32) = 1 from rfl] at hbv_not
      simpa only [m5WithAntSz, saved, hnot_sw, h1_sw, hsrc_sw, hff_sw, ← hbv_not, hte_p1,
        show (BitVec.ofNat 64 st.core.trail_end).toNat = saved from hs_eq] using hu1
  rintro L13 nb ⟨fb, prop, tb, ⟨⟩⟩ m2 hL13 ⟨st_b, hsp_le, hpt_le, hbneq, hu_b, hntf, hfb, htb, hm2⟩
  dsimp only at hsp_le hpt_le hbneq hntf hfb htb; have hlen_b := hu_b.len_ok
  refine wp_join_group (P := fun _ m3 => ∃ st_u : FullState,
      TransUnrollInv c F0 F_cur s (m5WithAntSz st st_u.scratch.ant_sz) src.toNat saved st_u ∧
      ¬(fb = true ∧ tb = true) ∧
      (fb = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat])) ∧
      (tb = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat, dst.toNat])) ∧
      (FullMem c st_u ⋆ R) m3) ?_ ?_
  · rintro J15 ⟨⟩ m3 ⟨st_u, hu_u, hntf_u, hfb_u, htb_u, hm3⟩; ft_to_group
    refine wp_loop_group (ts := []) (Inv := fun nu _ m4 => ∃ st_r : FullState,
        nu = st_r.core.trail_end - saved ∧
        TransUnrollInv c F0 F_cur s (m5WithAntSz st st_r.scratch.ant_sz) src.toNat saved st_r ∧
        (FullMem c st_r ⋆ R) m4) ?_ ?_
    rotate_left
    · intro L17 hL17; exact hL17 (st_u.core.trail_end - saved) () m3 ⟨st_u, rfl, hu_u, hm3⟩
    rintro L17 nu ⟨⟩ m4 hL17 ⟨st_r, huneq, hu_r, hm4⟩; have hlen_r := hu_r.len_ok
    have hte_r_lt : st_r.core.trail_end < 2 ^ 64 := (m5_ft_bnds hlen_r.core_ok).2.2.2; ft_split
    · have hte_gt : saved < st_r.core.trail_end :=
        (m5_ft_bv64_lt_eq hsav_lt hte_r_lt).mp (by simpa [BitVec.ult] using ‹_›)
      let st_pre_r := m5WithAntSz st st_r.scratch.ant_sz
      have hlen_pre_r : st_pre_r.LengthsOk c :=
        ⟨hlen_st.core_ok,
          { hlen_st.scratch_ok with walk_vals_len := hlen_st.scratch_ok.walk_vals_len }⟩
      have hpre_vals_r : st_pre_r.core.vals = s.core.vals := hst_vals
      have hpre_cv_r : st_pre_r.core.cur_vars = s.core.cur_vars := hcv_st
      obtain ⟨hte1_bv_len, hul_sw_bv, huln_sw_bv, hte1_bv, hu_r''⟩ :=
        m5_ft_unroll_c0_aux hw0 hpre_vals_r hpre_cv_r hlen_pre_r hu_r hte_gt hte_r_lt
      have huln_sw_set : (BitVec.setWidth 64 (st_r.core.trl[(BitVec.ofNat 64
          (BitVec.ofNat 64 st_r.core.trail_end - 1#64).toNat).toNat]'hte1_bv_len ^^^ 1#32)).toNat <
          (st_r.core.vals.set (BitVec.setWidth 64 (st_r.core.trl[(BitVec.ofNat 64 (BitVec.ofNat 64
            st_r.core.trail_end - 1#64).toNat).toNat]'hte1_bv_len)).toNat 0#8).length := by
        rw [List.length_set]; exact huln_sw_bv
      ft_steps; refine hL17 (st_r.core.trail_end - 1 - saved) () _ (by omega)
        ⟨_, ?_, hu_r'', by assumption⟩
      · dsimp only; rw [show (1 : BitVec 64) = 1#64 from rfl, hte1_bv]
    have hte_eq : st_r.core.trail_end = saved := by
      have hng : ¬(saved < st_r.core.trail_end) := fun hlt => ‹¬(_ < _)› (by
        rwa [Nat.mod_eq_of_lt hsav_lt, Nat.mod_eq_of_lt hte_r_lt])
      have := hu_r.saved_le_te; omega
    let st_pre_r := m5WithAntSz st st_r.scratch.ant_sz
    have hto_pre_r :
        TransOuterInv c F0 F_cur s src.toNat off p.toNat end_v reduced.toNat st_pre_r :=
      hto.with_scratch { hlen_st.scratch_ok with walk_vals_len := hlen_st.scratch_ok.walk_vals_len }
        rfl rfl
    have hto_done := hu_r.done hto_pre_r hte_eq; have hlen_d := hto_done.base.len_ok
    have hsame_r : st_r.core = let sc := st.core
        { sc with
          trail_end := st_r.core.trail_end, vals := st_r.core.vals, trl := st_r.core.trl } := by
      simpa [m5WithAntSz] using hu_r.same_core
    have hp1_bv : (p + 1#64).toNat = p.toNat + 1 := ft_bv64_add1 (by omega); ft_to_group
    refine wp_join_group (P := fun xs m5 => let red' := xs.1; ∃ st_d : FullState,
        red'.toNat ≤ p.toNat + 1 - off ∧
        TransOuterInv c F0 F_cur s src.toNat off (p.toNat + 1) end_v red'.toNat st_d ∧
        st_d.core.cur_vars = s.core.cur_vars ∧ st_d.core.fuel = s.core.fuel ∧
        (FullMem c st_d ⋆ R) m5) ?_ ?_
    · rintro J20 ⟨red', ⟨⟩⟩ m5 ⟨st_d, hrl_d, hto_d, hcv_d, hfuel_d, hm5⟩; ft_steps
      exact hL (end_v - (p.toNat + 1)) (fb, red', p + 1#64, ()) m5 (by omega) ⟨st_d,
        (by dsimp only; rw [hp1_bv]; omega), (by dsimp only; rw [hp1_bv]; omega),
        (by dsimp only; rw [hp1_bv]), (by dsimp only; rw [hp1_bv]; exact hrl_d),
        (by dsimp only; rw [hp1_bv]; exact hto_d), fun hf => hfb_u hf, hcv_d, hfuel_d, hm5⟩
    intro J20 hJ20; have hget_r : st_r.core.wstk[p.toNat]? = some w0 := by
      rw [hsame_r]; exact List.getElem?_eq_getElem hp_len
    ft_split; rotate_left
    · obtain ⟨_, _, _, hto_nxt⟩ := hto_done.skip_bin hp_lt hget_r hfl_nz; ft_steps
      exact hJ20 (reduced, ()) m4 ⟨st_r, by dsimp only; omega, hto_nxt,
        by rw [hsame_r, hcv_st], by rw [hsame_r, hfuel_st], hm4⟩
    ft_to_group; rw [show (Arg.var (lift2 (fun {n} x1 x2 => x1 &&& x2) (fun x1 x2 => x1 && x2) i32
      st.core.wstk[p.toNat] (2147483647 : BitVec 32))) = Arg.var dst from rfl]; ft_call h_del_bin
    have hdst_lt_d : dst.toNat < 2 * st_r.core.cur_vars := by
      rw [hsame_r, hcv_st]; exact hdst_lt0
    have hsrc_lt_d : src.toNat < 2 * st_r.core.cur_vars := by
      rw [hsame_r, hcv_st]; exact hsrc_lt
    refine ⟨c, st_r, R, rfl, hlen_r,
      fun _ => hto_done.base.other_bounds dst.toNat hdst_lt_d hdst_ne, hm4,
      fun wvec' wstk' wu' m5 hlen5 hdst_ws hother_ws hwstk_out hdst_sl _ _ _ hm5 => ?_⟩
    have hp_wc : p.toNat < c.wcap := by
      have := hto_done.base.end_le_wlen; have := hlen_r.core_ok.wlen_le; omega
    have hred1 : (reduced + 1#64).toNat = reduced.toNat + 1 :=
      ft_bv64_add1 (by have := hto_done.base.end_le_wlen; have := hlen_r.core_ok.wlen_le; omega)
    have hto_mk := m5_del_side_and_tomb hto_done hp_lt hp_wc hsrc_lt_d hdst_lt_d hdst_ne
      hget_r hfl_nz rfl hlen5 (by simpa only [Arg.val_var] using hdst_ws hdst_lt_d) hother_ws
      (fun idx hidx ho => hwstk_out idx hidx (fun _ => by simpa only [Arg.val_var] using ho))
      (by simpa only [Arg.val_var] using hdst_sl F_cur) (tc' := st_r.scratch.trans_cnt + 1#64)
    have hp_l5 : p.toNat < wstk'.length := by rw [hlen5.core_ok.wstk_len_arr]; omega
    ft_steps; exact hJ20 (reduced + 1#64, ()) _ ⟨_, by rw [hred1]; omega,
      by rw [hred1]; exact hto_mk, by dsimp only; rw [hsame_r, hcv_st],
      by dsimp only; rw [hsame_r, hfuel_st], by assumption⟩
  intro J15 hJ15; ft_split; · ft_steps; exact hJ15 () m2 ⟨st_b, hu_b, hntf, hfb, htb, hm2⟩
  ft_split; · ft_steps; exact hJ15 () m2 ⟨st_b, hu_b, hntf, hfb, htb, hm2⟩
  ft_split; rotate_left; · ft_steps; exact hJ15 () m2 ⟨st_b, hu_b, hntf, hfb, htb, hm2⟩
  ft_split; rotate_left; · ft_steps; exact hJ15 () m2 ⟨st_b, hu_b, hntf, hfb, htb, hm2⟩
  have hte_b_lt := (m5_ft_bnds hlen_b.core_ok).2.2.2; have hcv_b_le := hlen_b.core_ok.cur_vars_le
  have hpt_lt : prop.toNat < st_b.core.trail_end := by
    have h1 : prop.toNat < st_b.core.trail_end % 2 ^ 64 := ‹_›
    rwa [Nat.mod_eq_of_lt hte_b_lt] at h1
  have hprop_tlen : prop.toNat < st_b.core.trl.length := by
    rw [hlen_b.core_ok.trl_len]; have := hlen_b.core_ok.trail_end_le; omega
  have hprop1 := ft_bv64_add1 (by omega : prop.toNat + 1 < 2 ^ 64)
  let asz1 := st_b.scratch.ant_sz - 1#64
  let st_b1 := m5WithAntSz st_b asz1
  have hu_b1 := m5_trans_unroll_ant_sz asz1 hu_b
  let st_pre_b1 := m5WithAntSz st asz1
  have hto_pre_b1 :
      TransOuterInv c F0 F_cur s src.toNat off p.toNat end_v reduced.toNat st_pre_b1 :=
    hto.with_scratch { hlen_st.scratch_ok with walk_vals_len := hlen_st.scratch_ok.walk_vals_len }
      rfl rfl
  obtain ⟨lit, hlit_get, hlit_lt, _, _, _, hent_lit⟩ := hu_b1.bfs_trl_inv prop.toNat hsp_le hpt_lt
  let nl := lit ^^^ 1#32; have hnl_eq := ft_bv32_xor1 lit
  have hnl_lt : nl.toNat < 2 * st_b1.core.cur_vars := by
    rw [hnl_eq, hu_b1.same_core]; exact litNeg_lt_two_mul hlit_lt
  dsimp only [st_b1, m5WithAntSz] at hnl_lt
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
  obtain ⟨hnl_bnd, nt0, htomb0⟩ := hu_b1.watch_slice hto_pre_b1 hnl_lt
  dsimp only [st_b1, m5WithAntSz] at hnl_bnd htomb0
  ft_to_group
  refine wp_join_group (P := fun xs m3 => let f2 := xs.1; let t2 := xs.2.1; ∃ st_w : FullState,
      TransUnrollInv c F0 F_cur s (m5WithAntSz st st_w.scratch.ant_sz) src.toNat saved st_w ∧
      st_b.core.trail_end ≤ st_w.core.trail_end ∧ ¬(f2 = true ∧ t2 = true) ∧
      (f2 = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat])) ∧
      (t2 = true → (cnfOfClauses F_cur).EntailsClause (cnfClause [src.toNat, dst.toNat])) ∧
      (FullMem c st_w ⋆ R) m3) ?_ ?_
  · rintro J19 ⟨f2, t2, _q, ⟨⟩⟩ m3 ⟨st_w, hu_w, hte_w, hntf2, hf2, ht2, hm3⟩
    have hpt_pre : prop.toNat < st.core.cur_vars := by
      have := hlen_b.core_ok.trail_end_le; rw [hu_b.same_core] at this
      exact Nat.lt_of_lt_of_le hpt_lt this
    ft_steps; exact hL13 (st.core.cur_vars - (prop.toNat + 1)) (f2, prop + 1#64, t2, ()) m3
      (by rw [hbneq]; omega) ⟨st_w, by rw [hprop1]; omega, by rw [hprop1]; omega,
        by rw [hprop1], hu_w, hntf2, hf2, ht2, hm3⟩
  intro J19 hJ19; let loff := fullWatchOffCore st_b.core nl.toNat
  let lsz := fullWatchSizeCore st_b.core nl.toNat; let lend := loff + lsz; ft_steps
  refine wp_loop_group (ts := [i64]) (Inv := fun nq xs m3 => let q := xs.1
      ∃ st_q : FullState, ∃ nt : Nat, loff ≤ q.toNat ∧ q.toNat ≤ lend ∧
        nq = lend - q.toNat ∧ st_b.core.trail_end ≤ st_q.core.trail_end ∧
        TombWatchSliceOk F_cur st_q.core nl.toNat q.toNat (lend - q.toNat) nt ∧
        TransUnrollInv c F0 F_cur s (m5WithAntSz st st_q.scratch.ant_sz) src.toNat saved st_q ∧
        (FullMem c st_q ⋆ R) m3) ?_ ?_
  rotate_left
  · intro L20 hL20
    have hloff_lt : loff < 2 ^ 64 := by
      have := hnl_bnd; have := (m5_ft_bnds hlen_b.core_ok).2.2.1; omega
    have hlo_eq : (BitVec.ofNat 64 loff).toNat = loff := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hloff_lt]
    have hlo_arg : BitVec.setWidth 64 (st_b.core.wvec[(BitVec.setWidth 64
        (st_b.core.trl[prop.toNat]'hprop_tlen ^^^ (1 : BitVec 32)) <<<
          (1 : Nat)).toNat]'hnl_wv0) = BitVec.ofNat 64 loff := by
      apply BitVec.eq_of_toNat_eq; rw [ft_bv32_setWidth64, hlo_eq]
      have hidx2 : (BitVec.setWidth 64 (st_b.core.trl[prop.toNat]'hprop_tlen ^^^
          (1 : BitVec 32)) <<< (1 : Nat)).toNat = 2 * nl.toNat := by simpa [hlit_ge] using hnl_shl
      have hnl0 : 2 * nl.toNat < st_b.core.wvec.length := by rw [← hidx2]; exact hnl_wv0
      simp only [hidx2]; exact m5_ft_getElem_toNat hnl0
    ft_steps; rw [hlo_arg]; exact hL20 (lend - loff) (BitVec.ofNat 64 loff, ()) _
      ⟨st_b1, nt0, by rw [hlo_eq]; exact Nat.le_refl _, by rw [hlo_eq]; omega, by rw [hlo_eq],
        Nat.le_refl _, by rw [hlo_eq]; simpa [st_b1, m5WithAntSz, lend, loff, lsz] using htomb0,
        hu_b1, by assumption⟩
  rintro L20 nq ⟨q, ⟨⟩⟩ m3 hL20 ⟨st_q, nt, hql, hqh, hqneq, hte_q, htm_q, hu_q, hm3⟩
  dsimp only at hql hqh hqneq htm_q; have hlen_q := hu_q.len_ok
  ft_split; rotate_left
  · ft_steps; exact hJ19 (fb, tb, q, ()) m3 ⟨st_q, hu_q, hte_q, hntf, hfb, htb, hm3⟩
  ft_split; rotate_left
  · ft_steps; exact hJ19 (fb, tb, q, ()) m3 ⟨st_q, hu_q, hte_q, hntf, hfb, htb, hm3⟩
  have hq_lt : q.toNat < lend := by
    have hnl0_lt : 2 * nl.toNat < st_b.core.wvec.length := by rw [hlen_b.core_ok.wvec_len]; omega
    have hnl1_lt : 2 * nl.toNat + 1 < st_b.core.wvec.length := by
      rw [hlen_b.core_ok.wvec_len]; omega
    have hlo_w := m5_ft_getElem_toNat hnl0_lt; have hls_w := m5_ft_getElem_toNat hnl1_lt
    have hq_c0 := ‹q.toNat < _›
    have hidx_eq : (st_b.core.trl[prop.toNat]'hprop_tlen).toNat ^^^ 1 = nl.toNat := by
      rw [hlit_ge, hnl_eq]
    have h2nl_lt : 2 * nl.toNat + 1 < 2 ^ 64 := by have := (m5_ft_bnds hlen_b.core_ok).1; omega
    have hmod0 : 2 * nl.toNat % 2 ^ 64 = 2 * nl.toNat := Nat.mod_eq_of_lt (by omega)
    have hmod1 : (2 * nl.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 = 2 * nl.toNat + 1 := by
      rw [show (1 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt h2nl_lt]
    simp only [hidx_eq, hmod0, hmod1, hlo_w, hls_w] at hq_c0
    have := hnl_bnd; have := (m5_ft_bnds hlen_b.core_ok).2.2.1
    change q.toNat < (loff + lsz) % 2 ^ 64 at hq_c0; rwa [Nat.mod_eq_of_lt (by omega)] at hq_c0
  have hq_len : q.toNat < st_q.core.wstk.length := by
    rw [hlen_q.core_ok.wstk_len_arr]; have := hnl_bnd; have := hlen_b.core_ok.wlen_le; omega
  let asz2 := st_q.scratch.ant_sz - 1#64
  let st_q1 := m5WithAntSz st_q asz2
  have hu_q1 := m5_trans_unroll_ant_sz asz2 hu_q
  have hlen_q1 := hu_q1.len_ok
  have hstep := htm_q.inv_step (by omega) (List.getElem?_eq_getElem hq_len); ft_split
  · have hfl0 : (st_q.core.wstk[q.toNat] &&& 0x80000000#32) = 0#32 := ‹_›
    simp only [hfl0, ↓reduceIte] at hstep; obtain ⟨hle2, _, _, _, _, htm'⟩ := hstep; ft_steps
    have hq2 : (q + 2#64).toNat = q.toNat + 2 :=
      ft_bv64_add2 (by have := hnl_bnd; have := (m5_ft_bnds hlen_b.core_ok).2.2.1; omega)
    exact hL20 (lend - (q.toNat + 2)) (q + 2#64, ()) _ (by omega) ⟨st_q1, nt, by rw [hq2]; omega,
      by rw [hq2]; omega, by rw [hq2], hte_q,
      by rw [hq2]; rwa [show lend - q.toNat - 2 = lend - (q.toNat + 2) by omega] at htm',
      hu_q1, by assumption⟩
  have hfl_nz : (st_q.core.wstk[q.toNat] &&& 0x80000000#32) ≠ 0#32 := ‹_›
  have hq1 : (q + 1#64).toNat = q.toNat + 1 :=
    ft_bv64_add1 (by have := hnl_bnd; have := (m5_ft_bnds hlen_b.core_ok).2.2.1; omega)
  refine wp_join_group (P := fun _ m4 => (FullMem c st_q1 ⋆ R) m4) ?_ ?_
  rotate_left
  · intro J24 hJ24; ft_split
    · ft_split
      · obtain ⟨nt2, htm2⟩ :=
          m5_tomb_step_non_large hq_lt (List.getElem?_eq_getElem hq_len) hfl_nz htm_q
        ft_steps; exact hL20 (lend - (q.toNat + 1)) (q + 1#64, ()) _ (by omega)
          ⟨st_q1, nt2, by rw [hq1]; omega, by rw [hq1]; omega, by rw [hq1], hte_q,
            by rw [hq1]; exact htm2, hu_q1, by assumption⟩
      · ft_steps; exact hJ24 () _ (by assumption)
    · ft_steps; exact hJ24 () _ (by assumption)
  rintro J24 ⟨⟩ m4 hm4; simp only [hfl_nz, ↓reduceIte] at hstep
  have hsame_q : st_q.core = let sc := st.core
      { sc with
        trail_end := st_q.core.trail_end, vals := st_q.core.vals, trl := st_q.core.trl } := by
    simpa [m5WithAntSz] using hu_q.same_core
  let ot := st_q.core.wstk[q.toNat] &&& 0x7FFFFFFF#32
  have hot64 : (ot.setWidth 64).toNat = ot.toNat := ft_bv32_setWidth64 ot
  have hnlits_lt : (st_q.core.cur_vars <<< 1) = 2 * st_q.core.cur_vars := by omega
  ft_split
  · have hdst_eq : st_q.core.wstk[q.toNat] &&& 0x7FFFFFFF#32 = dst := ‹_›
    have hne_tomb : st_q.core.wstk[q.toNat] ≠ 0xFFFFFFFF#32 := fun ht => by
      have hdst_nat := congrArg BitVec.toNat hdst_eq; rw [ht] at hdst_nat
      have := (m5_ft_bnds hlen0.core_ok).1
      have hmsk : (0xFFFFFFFF#32 &&& 0x7FFFFFFF#32).toNat = 2147483647 := by decide
      omega
    simp only [hne_tomb, ↓reduceIte] at hstep; obtain ⟨hot_lt, hent_nl, _⟩ := hstep
    have hent_ot := entails_pair_trans hent_lit (by rwa [← hnl_eq])
    rw [congrArg BitVec.toNat hdst_eq] at hent_ot; ft_steps
    exact hJ19 (fb, true, q, ()) m4 ⟨st_q1, hu_q1, hte_q, by simp [‹fb = false›],
      fun hf => absurd hf (by simp [‹fb = false›]), fun _ => hent_ot, hm4⟩
  refine wp_join_group (P := fun _ m5 => ∃ st_q2 : FullState, ∃ nt2 : Nat,
      st_b.core.trail_end ≤ st_q2.core.trail_end ∧
      TombWatchSliceOk F_cur st_q2.core nl.toNat (q.toNat + 1) (lend - (q.toNat + 1)) nt2 ∧
      TransUnrollInv c F0 F_cur s (m5WithAntSz st st_q2.scratch.ant_sz) src.toNat saved st_q2 ∧
      (FullMem c st_q2 ⋆ R) m5) ?_ ?_
  · rintro J27 ⟨_, ⟨⟩⟩ m5 ⟨st_q2, nt2, hte_q2, htm_q2, hu_q2, hm5⟩; ft_steps
    exact hL20 (lend - (q.toNat + 1)) (q + 1#64, ()) m5 (by omega)
      ⟨st_q2, nt2, by rw [hq1]; omega, by rw [hq1]; omega, by rw [hq1], hte_q2,
        by rw [hq1]; exact htm_q2, hu_q2, hm5⟩
  intro J27 hJ27; ft_split; rotate_left
  · have htomb_q : st_q.core.wstk[q.toNat] = 0xFFFFFFFF#32 := Classical.byContradiction fun hne =>
        by
      simp only [hne, ↓reduceIte] at hstep
      have hlt_w : ¬((st_q.core.wstk[q.toNat] &&& (2147483647 : BitVec 32)).toNat <
          2 * (s.core.cur_vars % 2 ^ 64) % 2 ^ 64) := ‹_›
      have hcv_qs : st_q.core.cur_vars = s.core.cur_vars := by rw [hsame_q, hcv_st]
      have hlt2 := (m5_ft_bnds hlen0.core_ok).1; rw [Nat.mod_eq_of_lt (by omega :
        s.core.cur_vars < 2 ^ 64), Nat.mod_eq_of_lt (by omega : 2 * s.core.cur_vars < 2 ^ 64),
        ← hcv_qs] at hlt_w
      exact hlt_w hstep.1
    simp only [htomb_q, ↓reduceIte] at hstep; obtain ⟨_, hstep_t⟩ := hstep; ft_steps
    exact hJ27 (fb, ()) m4 ⟨st_q1, nt - 1, hte_q,
      by rwa [show lend - q.toNat - 1 = lend - (q.toNat + 1) by omega] at hstep_t, hu_q1, hm4⟩
  have hne_tomb : st_q.core.wstk[q.toNat] ≠ 0xFFFFFFFF#32 := fun ht => by
    have hlt_w : (st_q.core.wstk[q.toNat] &&& (2147483647 : BitVec 32)).toNat <
        2 * (s.core.cur_vars % 2 ^ 64) % 2 ^ 64 := ‹_›
    rw [ht] at hlt_w; have hmsk : (0xFFFFFFFF#32 &&& (2147483647 : BitVec 32)).toNat = 2147483647 :=
      by decide
    have := (m5_ft_bnds hlen0.core_ok).1; omega
  simp only [hne_tomb, ↓reduceIte] at hstep; obtain ⟨hot_lt, hent_nl, htail⟩ := hstep
  have hent_ot := entails_pair_trans hent_lit (by rwa [← hnl_eq])
  have hot_vlen := m5_ft_vals_lt hlen_q1.core_ok hot_lt
  have hot_st : ot.toNat < 2 * (m5WithAntSz st asz2).core.cur_vars := by
    have hcv_q_pre : st_q1.core.cur_vars = (m5WithAntSz st asz2).core.cur_vars := by
      rw [hu_q1.same_core]
    rw [← hcv_q_pre]; exact hot_lt
  have hpre_vals_q : (m5WithAntSz st asz2).core.vals = s.core.vals := hst_vals
  have hpre_te_q : (m5WithAntSz st asz2).core.trail_end = s.core.trail_end := hst_te
  have hpre_trl_q : ∀ i < s.core.trail_end,
      (m5WithAntSz st asz2).core.trl[i]? = s.core.trl[i]? := hst_trl
  have hpre_cv_q : (m5WithAntSz st asz2).core.cur_vars = s.core.cur_vars := hcv_st
  have hdom_ot := hu_q1.vals_domain hw0 hpre_vals_q hpre_cv_q hot_st; ft_split
  · rename_i hslt_c0
    change (BitVec.signExtend 32 st_q.core.vals[ot.toNat]).slt 0#32 = true at hslt_c0
    have hval_ff := m5_trans_vals_ff_of_domain (z := 0#32) hdom_ot rfl
      (by rw [List.getElem?_eq_getElem hot_vlen]; exact hslt_c0)
    have hent_src :=
      hu_q1.entails_src_of_falsified hw0 hpre_vals_q hpre_cv_q hcl0 hot_st hval_ff hent_ot
    ft_steps; exact hJ19 (true, tb, q, ()) m4 ⟨st_q1, hu_q1, hte_q, by simp [‹tb = false›],
      fun _ => hent_src, fun ht => absurd ht (by simp [‹tb = false›]), hm4⟩
  refine wp_join_group (P := fun _ m5 => ∃ st_q2 : FullState, ∃ nt2 : Nat,
      st_b.core.trail_end ≤ st_q2.core.trail_end ∧
      TombWatchSliceOk F_cur st_q2.core nl.toNat (q.toNat + 1) (lend - (q.toNat + 1)) nt2 ∧
      TransUnrollInv c F0 F_cur s (m5WithAntSz st st_q2.scratch.ant_sz) src.toNat saved st_q2 ∧
      (FullMem c st_q2 ⋆ R) m5) ?_ ?_
  · rintro J30 ⟨⟩ m5 ⟨st_q2, nt2, hte2, htm2, hu2, hm5⟩; ft_steps
    exact hJ27 (fb, ()) m5 ⟨st_q2, nt2, hte2, htm2, hu2, hm5⟩
  intro J30 hJ30
  have htail' : TombWatchSliceOk F_cur st_q.core nl.toNat (q.toNat + 1) (lend - (q.toNat + 1)) nt :=
    by rwa [show lend - q.toNat - 1 = lend - (q.toNat + 1) by omega] at htail
  ft_split; rotate_left; · ft_steps; exact hJ30 () m4 ⟨st_q1, nt, hte_q, htail', hu_q1, hm4⟩
  ft_split; rotate_left; · ft_steps; exact hJ30 () m4 ⟨st_q1, nt, hte_q, htail', hu_q1, hm4⟩
  rename_i hval0 _
  change BitVec.signExtend 32 st_q.core.vals[ot.toNat] = 0#32 at hval0
  have hot0 := m5_trans_vals_zero_of_domain (z := 0#32) hdom_ot rfl
    (by rw [List.getElem?_eq_getElem hot_vlen]; exact hval0)
  obtain ⟨hte_q_lt, hu_q'⟩ :=
    hu_q1.push hw0 hpre_vals_q hpre_te_q hpre_trl_q hpre_cv_q hot_st hot0 hent_ot
  have hbv_ot : BitVec.ofNat 32 ot.toNat = ot := m5_ft_bv32_ofNat_toNat ot
  have hotn_vlen : (BitVec.setWidth 64 (ot ^^^ 1#32)).toNat < (st_q.core.vals.set
      (BitVec.setWidth 64 ot).toNat (BitVec.setWidth 8 (1 : BitVec 32))).length := by
    rw [List.length_set, ft_bv32_setWidth64, ft_bv32_xor1, hlen_q.core_ok.vals_len]
    have := litNeg_lt_two_mul hot_lt; have := hlen_q.core_ok.cur_vars_le; dsimp only [ot]; omega
  have hteq_lt : st_q.core.trail_end < 2 ^ 64 := (m5_ft_bnds hlen_q.core_ok).2.2.2
  have hte_bv : (BitVec.ofNat 64 st_q.core.trail_end).toNat = st_q.core.trail_end := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hteq_lt]
  have hte_cv : st_q.core.trail_end < st_q.core.cur_vars := by
    change st_q1.core.trail_end < st_q1.core.cur_vars
    rw [hu_q1.same_core]; exact hte_q_lt
  have hte_max : st_q.core.trail_end < c.max_vars :=
    Nat.lt_of_lt_of_le hte_cv hlen_q.core_ok.cur_vars_le
  have hmx_bd := c.hmaxv; unfold dimacsBound at hmx_bd
  have hteq_tlen : (BitVec.ofNat 64 st_q.core.trail_end).toNat < st_q.core.trl.length := by
    rw [hte_bv, hlen_q.core_ok.trl_len]; exact hte_max
  have hteq1 : (BitVec.ofNat 64 st_q.core.trail_end + 1#64).toNat = st_q.core.trail_end + 1 := by
    rw [ft_bv64_add1 (by rw [hte_bv]; omega), hte_bv]
  ft_steps
  let st_q2 : FullState := { st_q1 with core := { st_q1.core with
      vals := (st_q.core.vals.set ot.toNat 1#8).set (ot.toNat ^^^ 1) 0xFF#8,
      trl := st_q.core.trl.set st_q.core.trail_end ot, trail_end := st_q.core.trail_end + 1 } }
  have hm_q2 : (FullMem c { st_q1 with core := { st_q1.core with
      vals := (st_q.core.vals.set (BitVec.setWidth 64 ot).toNat 1#8).set
        (BitVec.setWidth 64 (ot ^^^ 1#32)).toNat 0xFF#8,
      trl := st_q.core.trl.set (BitVec.ofNat 64 st_q.core.trail_end).toNat ot,
      trail_end := (BitVec.ofNat 64 st_q.core.trail_end + 1#64).toNat } } ⋆ R) _ := ‹_›
  simp only [ft_bv32_setWidth64, ft_bv32_xor1, hte_bv, hteq1] at hm_q2
  exact hJ30 () _ ⟨st_q2, nt, Nat.le_trans hte_q (Nat.le_succ _),
    TombWatchSliceOk.mono (k := st_q.core) (k' := st_q2.core) (Nat.le_refl _) (fun _ hr => hr)
      (fun _ _ _ => rfl) htail',
    by dsimp only [st_q2, st_q1, m5WithAntSz] at hu_q' ⊢; simpa only [hbv_ot] using hu_q', hm_q2⟩

/-- Parametric `Func.wp` theorem for `full_transitive_m5` against canonical
`FullFastBveBudgets.fullTransitiveFastSpec`. -/
theorem full_transitive_m5_wp (Γ : Env)
    (h_backtrack : ∀ args m Q X,
      Full.fullBacktrackSpec args m Q X → Γ "full_backtrack" [i64, i64] [] args m Q X)
    (h_trans_lit : ∀ args m Q X,
      Full.fullTransLitSpec args m Q X → Γ "full_trans_lit_m5" [i64, i32] [.bool] args m Q X)
    (h_propagate : ∀ args m Q X,
      Full.fullPropagateSpec args m Q X → Γ "full_propagate" [i64] [i64] args m Q X)
    (h_defrag : ∀ args m Q X,
      Full.fullWstackDefragSpec args m Q X → Γ "full_wstack_defrag" [i64] [] args m Q X) :
    ∀ args m Q X, FullFastBveBudgets.fullTransitiveFastSpec args m Q X →
      Func.wp Γ full_transitive_m5_body args m Q X := by
  rintro ⟨h, tick_lim, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hm, hQ⟩
  unfold full_transitive_m5_body; ft_unmdata
  have hlen0 := hsp.1.lengths
  ft_split
  · ft_steps
    exact hQ 1#64 s m hsp id id (fun hnb _ => absurd ‹_› hnb) (Nat.le_refl _) (Or.inl rfl)
      (fun h => absurd h (by decide)) hm
  ft_split
  · ft_steps
    exact hQ 1#64 s m hsp id id (fun _ htl => absurd ‹_› htl) (Nat.le_refl _) (Or.inl rfl)
      (fun h => absurd h (by decide)) hm
  refine wp_join_group (P := fun _ m' => ∃ s1 : FullState, FullSparseInv c F0 s1 ∧
      s1.core.cur_level = 0 ∧ s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m') ?_ ?_
  · rintro J ⟨⟩ m1 ⟨s1, hsp1, hcl1, hfuel1, hm1⟩; have hlen1 := hsp1.1.lengths; ft_to_group
    refine wp_loop_break_group (brkTs := [i64, i64]) (lpTs := [i64])
      (BrkPost := fun xs m' => let res := xs.2.1; ∃ sb : FullState, FullSparseInv c F0 sb ∧
        sb.core.cur_level = 0 ∧ sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (res = 1#64 ∨ res = 20#64) ∧ (res = 20#64 → F0.Unsat) ∧ (FullMem c sb ⋆ R) m')
      (Inv := fun n xs m' => let v := xs.1; ∃ sl : FullState, v.toNat ≤ s1.core.cur_vars ∧
        n = s1.core.cur_vars - v.toNat ∧ FullSparseInv c F0 sl ∧ sl.core.cur_level = 0 ∧
        sl.core.cur_vars = s1.core.cur_vars ∧ sl.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (FullMem c sl ⋆ R) m') ?_ ?_ ?_
    · rintro B ⟨_v, res, ⟨⟩⟩ m2 ⟨sb, hspb, hclb, hfuelb, hresb, hunsatb, hm2⟩
      refine wp_join_group (P := fun _ m3 => ∃ sd : FullState, FullSparseInv c F0 sd ∧
          sd.core.cur_level = 0 ∧ sd.core.fuel.toNat ≤ s.core.fuel.toNat ∧
          (FullMem c sd ⋆ R) m3) ?_ ?_
      · rintro Jd ⟨⟩ m3 ⟨sd, hspd, hcld, hfueld, hm3⟩; have hlend := hspd.1.lengths; ft_steps
        exact hQ res _ _ (fullSparseInv_with_probing hspd 0#64) (fun _ => hcld) (fun _ => rfl)
          (fun _ _ => ⟨hcld, rfl⟩) hfueld hresb hunsatb (by assumption)
      · intro Jd hJd; have hlenb := hspb.1.lengths; ft_split
        · ft_call h_defrag; obtain ⟨F_cb, hwb⟩ := hspb.1.witness
          have hm := hwb.watches; simp only [ModeWatchesInv, hspb.2.2.2.2, ↓reduceIte] at hm
          refine ⟨c, sb, R, rfl, hlenb, hm.layout, hm2, fun _ _ _ _ m3 hlen3 hlay3 _ hpres hm3 =>
            hJd () m3 ⟨_, fullWstackDefrag_sparse hspb rfl hlen3 hlay3 hpres, hclb, hfuelb, hm3⟩⟩
        · ft_steps; exact hJd () m2 ⟨sb, hspb, hclb, hfuelb, hm2⟩
    · rintro B L n ⟨v, ⟨⟩⟩ m2 hB hL ⟨sl, hvle, hneq, hspl, hcll, hcvl, hfuell, hm2⟩
      have hlenl := hspl.1.lengths
      have hcv_lt : s1.core.cur_vars < 2 ^ 64 := by have := (m5_ft_bnds hlen1.core_ok).1; omega
      have hB1 : B (v, 1#64, ()) m2 := hB (v, 1#64, ()) m2 ⟨sl, hspl, hcll, hfuell, Or.inl rfl,
        fun h => absurd (show (1#64 : BitVec 64) = 20#64 from h) (by decide), hm2⟩
      ft_split; rotate_left; · ft_steps; exact hB1
      have hv_lt : v.toNat < s1.core.cur_vars := by
        have hlt : v.toNat < (BitVec.ofNat 64 s1.core.cur_vars).toNat := by
          simpa [BitVec.ult] using ‹_›
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv_lt] at hlt
      ft_split; rotate_left; · ft_steps; exact hB1
      ft_split; rotate_left; · ft_steps; exact hB1
      refine wp_join_group (P := fun xs m3 => xs.1 = 1#64 ∧ ∃ sn : FullState,
          FullSparseInv c F0 sn ∧ sn.core.cur_level = 0 ∧ sn.core.cur_vars = s1.core.cur_vars ∧
          sn.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sn ⋆ R) m3) ?_ ?_
      · rintro J2 ⟨_, ⟨⟩⟩ m3 ⟨rfl, sn, hspn, hcln, hcvn, hfueln, hm3⟩; ft_steps
        have hv1 : (v + 1#64).toNat = v.toNat + 1 := ft_bv64_add1 (by omega)
        dsimp only at hvle hneq; exact hL (s1.core.cur_vars - (v.toNat + 1)) (v + 1#64, ()) m3
          (by omega) ⟨sn, by dsimp only; rw [hv1]; omega, by dsimp only; rw [hv1], hspn, hcln,
            hcvn, hfueln, hm3⟩
      · intro J2 hJ2
        have hv_fl : v.toNat < sl.core.flags.length := by
          rw [hlenl.core_ok.flags_len]; have := hlenl.core_ok.cur_vars_le; omega
        ft_split; rotate_left
        · ft_steps; exact hJ2 (1#64, ()) m2 ⟨rfl, sl, hspl, hcll, hcvl, hfuell, hm2⟩
        ft_to_group; have hsp_cl : FullSparseInv c F0 { sl with core := { sl.core with
            flags := sl.core.flags.set v.toNat (sl.core.flags[v.toNat] &&& ~~~512#32) } } :=
          fullSparseInv_clear_fl_trans hspl
        have hv32 : 2 * v.toNat + 1 < 2 ^ 32 := by have := (m5_ft_bnds hlenl.core_ok).1; omega
        have hlit0 : ((v <<< (1 : Nat)).setWidth 32).toNat < 2 * ({ sl.core with
            flags := sl.core.flags.set v.toNat (sl.core.flags[v.toNat] &&& ~~~512#32) } :
            FullCoreState).cur_vars := by rw [ft_bv64_shl1_setWidth32 (by omega)]; dsimp only; omega
        ft_call h_trans_lit; refine ⟨c, F0, _, R, rfl, hsp_cl, hcll, hlit0, (by assumption),
          fun ok s_t0 m3 hspt0 hclt0 hcvt0 hfuelt0 huns0 hm3 => ?_⟩
        have hcv_t0 : s_t0.core.cur_vars = s1.core.cur_vars := hcvt0.trans hcvl
        ft_split; rotate_left; · ft_steps; exact hB (v, 20#64, ()) m3 ⟨s_t0, hspt0, hclt0,
          by rw [hfuelt0]; exact hfuell, Or.inr rfl, fun _ => huns0 (by cases ok <;> simp_all), hm3⟩
        obtain ⟨F_ct0, hwt0⟩ := hspt0.1.witness; ft_call h_propagate
        refine ⟨c, F0, F_ct0, s_t0, R, rfl, hspt0.1.lengths, hwt0, hspt0.2.2.2.2, hm3,
          fun r_p0 vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk'
            wlen' wu' fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m4 hlen4 hw4 _ hperm4
            hfu4 _ _ hr1 _ _ hm4 => ?_⟩
        have hsp_p0 := fullPropagate_sparse hspt0 rfl hlen4 hw4 hperm4; ft_split
        · ft_steps; exact hB (v, 20#64, ()) m4 ⟨_, hsp_p0, hclt0,
            Nat.le_trans (Nat.le_trans hfu4 (by rw [hfuelt0]; exact Nat.le_refl _)) hfuell,
            Or.inr rfl, fun _ => Full.level0_unsat_of_conflict_okW hw4 hclt0 (hr1 ‹_›).2.2,
            hm4⟩
        · let st_p0 : FullState := { s_t0 with
            scratch := { s_t0.scratch with
              search_ticks := ticks', wsort := wsort', phases := phases' },
            core := { s_t0.core with
              vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
              trail_pos := tp', trail_end := te', propagated := prop', unassigned := unass',
              unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
              wusable := wu', fuel := fuel', confl_type := ctype', confl_ref := cref',
              confl_lit0 := c0', confl_lit1 := c1', oom := oom' } }
          have hlit1 : (((v <<< (1 : Nat)) ||| 1#64).setWidth 32).toNat <
              2 * st_p0.core.cur_vars := by rw [ft_bv64_shl1_or1_setWidth32 hv32, hcv_t0]; omega
          ft_to_group; ft_call h_trans_lit; refine ⟨c, F0, st_p0, R, rfl, hsp_p0, hclt0, hlit1,
            hm4, fun ok2 s_t1 m5 hspt1 hclt1 hcvt1 hfuelt1 huns1 hm5 => ?_⟩
          have hcv_t1 : s_t1.core.cur_vars = s1.core.cur_vars := hcvt1.trans hcv_t0
          ft_split; rotate_left; · ft_steps; exact hB (v, 20#64, ()) m5 ⟨s_t1, hspt1, hclt1,
            by rw [hfuelt1]; exact Nat.le_trans hfu4 (by rw [hfuelt0]; exact hfuell),
            Or.inr rfl, fun _ => huns1 (by cases ok2 <;> simp_all), hm5⟩
          obtain ⟨F_ct1, hwt1⟩ := hspt1.1.witness; ft_call h_propagate
          refine ⟨c, F0, F_ct1, s_t1, R, rfl, hspt1.1.lengths, hwt1, hspt1.2.2.2.2, hm5,
            fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fuel2 _ _ _ _ _ _ _ _ m6 hlen6 hw6 _ hperm6
              hfu6 _ _ hr1_2 _ _ hm6 => ?_⟩
          have hsp_p1 := fullPropagate_sparse hspt1 rfl hlen6 hw6 hperm6
          have hfuel_p1 : fuel2.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfu6
            (by rw [hfuelt1]; exact Nat.le_trans hfu4 (by rw [hfuelt0]; exact hfuell))
          ft_split
          · ft_steps; exact hB (v, 20#64, ()) m6 ⟨_, hsp_p1, hclt1, hfuel_p1, Or.inr rfl,
              fun _ => Full.level0_unsat_of_conflict_okW hw6 hclt1 (hr1_2 ‹_›).2.2, hm6⟩
          · ft_steps; exact hJ2 (1#64, ()) m6 ⟨rfl, _, hsp_p1, hclt1, hcv_t1, hfuel_p1, hm6⟩
    · intro B L hB hL; ft_steps; exact hL s1.core.cur_vars (0#64, ()) _ ⟨_, Nat.zero_le _, rfl,
        fullSparseInv_with_ant_sz (fullSparseInv_with_probing hsp1 1#64) tick_lim,
        hcl1, rfl, hfuel1, by assumption⟩
  · intro J hJ; have hlen := hsp.1.lengths; obtain ⟨F_cur, hw⟩ := hsp.1.witness
    have hcl_lt : s.core.cur_level < 2 ^ 64 := by
      have := hw.cur_level_le; have := (m5_ft_bnds hlen.core_ok).2.2.2; omega
    ft_split
    · ft_call h_backtrack
      have htl0 : ((Arg.imm 0).val : Val i64).toNat = 0 := by decide
      refine ⟨c, s, R, rfl, hlen, hcl_lt, (fun hpos => by
          have := hlen.core_ok.cur_vars_le; have := hw.cur_level_le
          have := hlen.core_ok.trail_end_le; rw [htl0] at hpos ⊢; omega), hw.trail_lits_lt, hm,
        fun _ _ _ _ _ _ _ _ _ _ _ hlen1 _ _ hcl1 hpr1 _ _ _ hw1 _ hm1 => hJ () _ ⟨_,
          fullBacktrack_sparse hsp rfl hlen1 hpr1 hw1, by simp [hcl1], Nat.le_refl _, hm1⟩⟩
    · ft_steps
      have hcl0' : s.core.cur_level = 0 := by
        simpa [Nat.mod_eq_of_lt hcl_lt] using
          congrArg BitVec.toNat (‹BitVec.ofNat 64 s.core.cur_level = 0#64›)
      exact hJ () m ⟨s, hsp, hcl0', Nat.le_refl _, hm⟩

end TransitiveProofs

/-! ## 4. Vivification (`full_vivify_tier_m5` & `full_vivify_m5`) -/

/-- Specification for M5 per-tier vivification
`full_vivify_tier_m5(h, tier_mode, budget, tick_lim)`. -/
def fullVivifyTierM5Spec : Spec [i64, i64, i64, i64] [i64] :=
  fun (h, _tier_mode, budget, _tick_lim, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
      ∀ r s' m',
        FullSparseInv c F0 s' →
        (s.core.cur_level = 0 → s'.core.cur_level = 0) →
        (s.core.probing = 0#64 → s'.core.probing = 0#64) →
        (budget ≠ 0#64 → s'.core.cur_level = 0 ∧ s'.core.probing = 0#64) →
        s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

theorem fullVivifyTierM5Spec_noExit : ∀ a m Q X,
    fullVivifyTierM5Spec a m Q X → fullVivifyTierM5Spec a m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

/-- Specification for M5 unified vivification driver `full_vivify_m5(h)`. -/
def m5VivifySpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInv c F0 s' → s'.core.cur_level = 0 → s'.core.probing = 0#64 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

theorem m5VivifySpec_noExit : ∀ a m Q X,
    m5VivifySpec a m Q X → m5VivifySpec a m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

section VivifyProofs

open FullM4VivBce FullVivTopTactics FullVivTop
open scoped Full.FullArenaTactics FullVivTopTactics

/-- Parametric `Func.wp` theorem for `full_vivify_tier_m5` against `fullVivifyTierM5Spec`. -/
theorem full_vivify_tier_m5_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hCollect : ∀ a m Q X, fullVivCollectM4Spec a m Q X →
      Γ "full_viv_collect_m4" [i64, i64] [i64] a m Q X)
    (hKeys : ∀ a m Q X, fullVivKeysM4Spec a m Q X →
      Γ "full_viv_keys_m4" [i64, i64] [] a m Q X)
    (hSortSched : ∀ a m Q X, fullVivSortSchedM4Spec a m Q X →
      Γ "full_viv_sort_sched_m4" [i64, i64] [] a m Q X)
    (hVivClause : ∀ a m Q X, fullVivClauseM4Spec a m Q X →
      Γ "full_viv_clause_m4" [i64, i32] [i64] a m Q X)
    (hProp : ∀ a m Q X, Full.fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hClearTier : ∀ a m Q X, fullVivClearTierM4Spec a m Q X →
      Γ "full_viv_clear_tier_m4" [i64, i64] [] a m Q X) :
    ∀ a m Q X, fullVivifyTierM5Spec a m Q X →
      Func.wp Γ full_vivify_tier_m5_body a m Q X := by
  rintro ⟨h, tier_mode, budget0, _tick_lim, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hsp0, hm0, hQ⟩
  have har_cap := c.harena; have hmx := c.hmaxv; have hrc := c.hred
  unfold dimacsBound at har_cap hmx hrc
  unfold Func.wp full_vivify_tier_m5_body; fvt_to_group
  · fvt_steps
    exact hQ 1#64 s m0 hsp0 id id (fun hnz => absurd (by c0_bound) hnz)
      (Nat.le_refl _) (Or.inl rfl) (fun h => by cases h) hm0
  refine wp_join_group (ts := [])
    (fun () m1 => ∃ s1 : FullState, FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m1) ?_ ?_
  · rintro _ ⟨⟩ m1 ⟨s1, hsp1, hcl1, hfl1, hm1⟩
    fvt_steps
    let s2 : FullState := { s1 with core := { s1.core with probing := 1#64 } }
    have hsp2 : FullSparseInv c F0 s2 := FullVivTop.FullSparseInv.with_probing hsp1 1#64
    have hm2 : (FullMem c s2 ⋆ R) _ := hm
    have hfl2 : s2.core.fuel.toNat ≤ s.core.fuel.toNat := hfl1
    clear_value s2
    clear hsp1 hcl1 hfl1
    c0_call hCollect
    refine ⟨c, F0, s2, R, rfl, hsp2, hm2, fun bn tr3 rr3 m3 h3bn htr3 hrr3 hok3 hm3 => ?_⟩
    let s3 : FullState :=
      { s2 with scratch := { s2.scratch with tarjan_reach := tr3, red_refs := rr3 } }
    have hsp3 : FullSparseInv c F0 s3 :=
      FullSparseInv.with_red_refs (FullSparseInv.with_tarjan_reach hsp2 htr3) hrr3
    c0_call hKeys
    refine ⟨c, F0, s3, R, rfl, hsp3, h3bn, hok3, hm3, fun rr4 m4 hrr4 hok4 hm4 => ?_⟩
    let s4 : FullState := { s3 with scratch := { s3.scratch with red_refs := rr4 } }
    have hsp4 : FullSparseInv c F0 s4 := FullSparseInv.with_red_refs hsp3 hrr4
    c0_call hSortSched
    refine ⟨c, s4, R, rfl, hsp4.1.lengths, h3bn, hok4, hm4,
      fun rr5 m5 hrr5_len hok5 hm5 => ?_⟩
    let s5 : FullState := { s4 with scratch := { s4.scratch with red_refs := rr5 } }
    have hsp5 : FullSparseInv c F0 s5 := FullSparseInv.with_red_refs hsp4 hrr5_len
    have hfl5 : s5.core.fuel.toNat ≤ s.core.fuel.toNat := hfl2
    have hrefs5 : fullArenaClauseRefs s5 = fullArenaClauseRefs s2 := rfl
    have hrr5 : s5.scratch.red_refs = rr5 := rfl
    have hok5' : ∀ k < bn.toNat, (rr5[3 * k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s2 := hok5
    have hm5' : (FullMem c s5 ⋆ R) m5 := hm5
    clear_value s5 s4 s3
    clear s4 s3 hsp4 hsp3 tr3 rr3 rr4 htr3 hrr3 hrr4 hok3 hok4 hok5 hm3 hm4 hm5 hsp2 hm2 hfl2
      hCollect hKeys hSortSched
    fvt_to_group
    refine wp_loop_break_group (brkTs := [i64, i64, i64, i64]) (lpTs := [i64, i64, i64])
      (fun (_budget_b, res_b, bi_b, _spent_b, ()) mb => ∃ sb : FullState,
        FullSparseInv c F0 sb ∧ sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        (res_b = 1#64 ∨ res_b = 20#64) ∧ (res_b = 20#64 → F0.Unsat) ∧
        (FullMem c sb ⋆ R) mb)
      (fun rem (budget, bi, spent, ()) mvi => ∃ svi : FullState,
        bi.toNat ≤ bn.toNat ∧ rem = bn.toNat - bi.toNat ∧
        FullSparseInv c F0 svi ∧ svi.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        fullArenaClauseRefs svi = fullArenaClauseRefs s2 ∧
        svi.scratch.red_refs = rr5 ∧ (FullMem c svi ⋆ R) mvi)
      ?_ ?_ ?_
    · rintro _ ⟨_, res_b, bi_b, _, ⟨⟩⟩ mb ⟨sb, hspb, hflb, hresb, h20b, hmb⟩
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
    · intro B L rem ⟨budget, bi, spent, ⟨⟩⟩ mvi hB hL
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
        have hcr_bnd : cr.toNat + 3 ≤ svi.core.arena_len :=
          (fullArenaScanRefs_mem_bounds hcr_ref).2
        have har_len : svi.core.arena.length = c.arena_cap :=
          hspv.1.lengths.core_ok.arena_len_arr
        have hal_le : svi.core.arena_len ≤ c.arena_cap := hspv.1.lengths.core_ok.arena_len_le
        have har_cr2 : (cr.setWidth 64 + 2#64).toNat < svi.core.arena.length := by bv_omega
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
        · exact hB (budget - 1#64, 20#64, bi, _, ()) m_vc
            ⟨s_vc, hsw_vc.toSparse, hfl_vc', Or.inr rfl, fun _ => h20_vc (by c0_bound), hm_vc⟩
        · exact hB (budget - 1#64, 1#64, bi, _, ()) m_vc
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
            m4_sparseInvW_of_prop_canon hsw_vc hlen_p hw_p hperm_p
          have hrefs_p : fullArenaClauseRefs s_p = fullArenaClauseRefs s_vc := hperm_p.2.1
          have hfl_p' : s_p.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfl_p hfl_vc'
          fvt_steps
          · have hpr_eq1 : pr = 1#64 := by c0_bound
            have hunsat : F0.Unsat :=
              FullVivTopSpecs.level0_unsat_of_conflict_okW hw_p hcl_vc0 (hpr1 hpr_eq1).2.2
            exact hB (budget - 1#64, 20#64, bi, _, ()) m_p
              ⟨s_p, hsw_p.toSparse, hfl_p', Or.inr rfl, fun _ => hunsat, hm_p⟩
          · exact hL (bn.toNat - (bi + 1#64).toNat) (budget - 1#64, bi + 1#64, _, ()) m_p
              (by rw [hbi1]; omega)
              ⟨s_p, by rw [hbi1]; omega, rfl, hsw_p.toSparse, hfl_p',
                hrefs_p.trans hrefs_vc2, hrr_vc5, hm_p⟩
        · exact hL (bn.toNat - (bi + 1#64).toNat) (budget - 1#64, bi + 1#64, _, ()) m_vc
            (by rw [hbi1]; omega)
            ⟨s_vc, by rw [hbi1]; omega, rfl, hsw_vc.toSparse, hfl_vc', hrefs_vc2, hrr_vc5, hm_vc⟩
      · exact hB (budget, 1#64, bi, _, ()) mvi
          ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
      · exact hB (budget, 1#64, bi, _, ()) mvi
          ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
      · exact hB (budget, 1#64, bi, _, ()) mvi
          ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
      · exact hB (budget, 1#64, bi, _, ()) mvi
          ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
      · exact hB (budget, 1#64, bi, _, ()) mvi
          ⟨svi, hspv, hflv, Or.inl rfl, (fun h => by cases h), hmvi⟩
    · intro B L _ hL; fvt_steps
      exact hL bn.toNat (budget0, 0#64, 0#64, ()) m5
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

/-- Parametric `Func.wp` theorem for `full_vivify_m5` against `m5VivifySpec`. -/
theorem full_vivify_m5_wp (Γ : Env)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hTier : ∀ a m Q X, fullVivifyTierM5Spec a m Q X →
      Γ "full_vivify_tier_m5" [i64, i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, m5VivifySpec a m Q X → Func.wp Γ full_vivify_m5_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hsp0, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hbud : (0xFFFFFFFF#64 : BitVec 64) ≠ 0#64 := by decide
  unfold Func.wp full_vivify_m5_body; fvt_to_group
  refine wp_join_group (ts := [])
    (fun () m1 => ∃ s1 : FullState, FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m1) ?_ ?_
  · rintro _ ⟨⟩ m1 ⟨s1, hsp1, hcl1, hfl1, hm1⟩
    fvt_to_group
    refine wp_join_group (ts := [i64]) (fun _ md => md = m1) ?_
      (fun Jd hJd => by fvt_steps <;> exact hJd _ m1 rfl)
    rintro _ ⟨delta, ⟨⟩⟩ md hmd; rw [hmd]; fvt_to_group
    refine wp_join_group (ts := [i64]) (fun _ me => me = m1) ?_
      (fun Je hJe => by fvt_steps <;> exact hJe _ m1 rfl)
    rintro _ ⟨eff_ref, ⟨⟩⟩ me hme; rw [hme]; fvt_steps
    · c0_call hTier
      refine ⟨c, F0, s1, R, rfl, hsp1, hm1, fun r2 s2 m2 hsp2 _ _ hnz2 hfl2 hr2 hu2 hm2 => ?_⟩
      obtain ⟨hcl2, hpr2⟩ := hnz2 hbud
      exact hQ r2 s2 m2 hsp2 hcl2 hpr2 (Nat.le_trans hfl2 hfl1) hr2 hu2 hm2
    · c0_call hTier
      refine ⟨c, F0, s1, R, rfl, hsp1, hm1, fun r2 s2 m2 hsp2 _ _ hnz2 hfl2 hr2 hu2 hm2 => ?_⟩
      obtain ⟨hcl2, hpr2⟩ := hnz2 hbud
      fvt_steps
      · exact hQ 20#64 s2 m2 hsp2 hcl2 hpr2 (Nat.le_trans hfl2 hfl1)
          (Or.inr rfl) (fun _ => hu2 hc) hm2
      · c0_call hTier
        refine ⟨c, F0, s2, R, rfl, hsp2, hm2, fun r3 s3 m3 hsp3 _ _ hnz3 hfl3 hr3 hu3 hm3 => ?_⟩
        obtain ⟨hcl3, hpr3⟩ := hnz3 hbud
        fvt_steps
        · exact hQ 20#64 s3 m3 hsp3 hcl3 hpr3 (Nat.le_trans hfl3 (Nat.le_trans hfl2 hfl1))
            (Or.inr rfl) (fun _ => hu3 hc) hm3
        · c0_call hTier
          refine ⟨c, F0, s3, R, rfl, hsp3, hm3, fun r4 s4 m4 hsp4 _ _ hnz4 hfl4 hr4 hu4 hm4 => ?_⟩
          obtain ⟨hcl4, hpr4⟩ := hnz4 hbud
          fvt_steps
          · exact hQ 20#64 s4 m4 hsp4 hcl4 hpr4
              (Nat.le_trans hfl4 (Nat.le_trans hfl3 (Nat.le_trans hfl2 hfl1)))
              (Or.inr rfl) (fun _ => hu4 hc) hm4
          · c0_call hTier
            refine ⟨c, F0, s4, R, rfl, hsp4, hm4, fun r5 s5 m5 hsp5 _ _ hnz5 hfl5 hr5 hu5 hm5 => ?_⟩
            obtain ⟨hcl5, hpr5⟩ := hnz5 hbud
            exact hQ r5 s5 m5 hsp5 hcl5 hpr5
              (Nat.le_trans hfl5 (Nat.le_trans hfl4 (Nat.le_trans hfl3 (Nat.le_trans hfl2 hfl1))))
              hr5 hu5 hm5
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

end VivifyProofs

/-! ## 5. Dense Sweeping (`full_sweep_dense_m5`, `16384` Clamp Lifted) -/

section SweepDenseProofs

open FullM4Sweep FullArenaTactics FullSweepVarHelpers
open scoped Full.FullArenaTactics M4SweepTactics

private theorem m5_tmkZero_congr {s s' : FullState} (h : M4TmkZero s)
    (hcv : s'.core.cur_vars = s.core.cur_vars)
    (ht : s'.scratch.tarjan_mark = s.scratch.tarjan_mark) : M4TmkZero s' := by
  intro v hv; rw [ht]; exact h v (hcv ▸ hv)

/-- Parametric `Func.wp` theorem for `full_sweep_dense_m5` against canonical
`FullDefSweep.fullSweepDenseSpec`. -/
theorem full_sweep_dense_m5_wp (Γ : Env)
    (hVar : ∀ a m Q X, m4SweepVarSpec a m Q X →
      Γ "full_m4_sweep_var" [i64, i32, i64] [i64] a m Q X) :
    ∀ args m Q X, FullDefSweep.fullSweepDenseSpec args m Q X →
      Func.wp Γ full_sweep_dense_m5_body args m Q X := by
  rintro ⟨h, budget, tick_lim, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hinv.lengths.core_ok.cur_vars_le
  have htmk_len := hinv.lengths.scratch_ok.tarjan_mark_len
  unfold Func.wp full_sweep_dense_m5_body; m4_steps
  m4_split
  · m4_steps; exact hQ 1#64 s m hinv rfl (le_refl _) (Or.inl rfl) (fun h => by cases h) hm
  m4_split
  · m4_steps; exact hQ 1#64 s m hinv rfl (le_refl _) (Or.inl rfl) (fun h => by cases h) hm
  m4_split
  · m4_steps; exact hQ 1#64 s m hinv rfl (le_refl _) (Or.inl rfl) (fun h => by cases h) hm
  have hcap : k5MinScr ≤ c.scratch_cap := by unfold k5MinScr; bv_omega
  m4_to_group
  refine wp_loop_inv (ts := [i64])
    (fun (i, ()) m0 => i.toNat ≤ s.core.cur_vars ∧ ∃ tmk0 : List (BitVec 32),
      tmk0.length = 2 * c.max_vars ∧ (∀ u < i.toNat, tmk0[u]?.getD 0#32 = 0#32) ∧
      (FullMem c { s with scratch := { s.scratch with tarjan_mark := tmk0 } } ⋆ R) m0)
    (fun (i, ()) _ => s.core.cur_vars - i.toNat)
    (fun _ hLi => by
      m4_steps
      exact hLi (0#64, ()) m
        ⟨Nat.zero_le _, s.scratch.tarjan_mark, htmk_len, fun _ hu => by simp at hu, hm⟩)
    (fun _ (i, ()) m0 ⟨hi_le, tmk0, ht0_len, ht0_cov, hm0⟩ hLi => by
      m4_split
      · have hi_lt : i.toNat < s.core.cur_vars := by bv_omega
        have hi_bd : i.toNat < tmk0.length := by omega
        have hi1 : (i + 1#64).toNat = i.toNat + 1 := m4_bv64_add1 (by omega)
        m4_steps; refine hLi (i + 1#64, ()) _ (by dsimp only; omega)
          ⟨by omega, tmk0.set i.toNat 0#32, List.length_set.trans ht0_len, fun u hu => ?_,
           by assumption⟩
        by_cases hui : u = i.toNat
        · subst hui; rw [List.getElem?_set_self (by omega)]; rfl
        · rw [List.getElem?_set_ne (Ne.symm hui)]; exact ht0_cov u (by omega)
      · have hi_eq : i.toNat = s.core.cur_vars := by
          have hlt : ¬ i.toNat < s.core.cur_vars := by
            rw [Nat.mod_eq_of_lt (by omega : s.core.cur_vars < 2 ^ 64)] at hc; exact hc
          omega
        let s0 : FullState := { s with scratch := { s.scratch with tarjan_mark := tmk0 } }
        have hinv0 : FullDenseInv c F0 s0 := fullDenseInv_with_tmk hinv ht0_len
        have ht0_zero : M4TmkZero s0 := fun u hu => ht0_cov u (hi_eq ▸ hu)
        m4_to_group
        refine wp_join_group (ts := [i64, i64, i64, i64])
          (fun (_bB, _rB, _vB, resB, ()) mB => ∃ sB, FullDenseInv c F0 sB ∧
            sB.core.cur_vars = s.core.cur_vars ∧ sB.core.fuel.toNat ≤ s.core.fuel.toNat ∧
            (resB = 1#64 ∨ resB = 20#64) ∧ (resB = 20#64 → F0.Unsat) ∧ (FullMem c sB ⋆ R) mB)
          (fun _ (_bB, _rB, _vB, resB, ()) mB ⟨sB, hinvB, hcvB, hfuelB, hresB, hunsB, hmB⟩ => by
            m4_to_group; refine wp_unroll_group fun _ _ => ?_
            m4_split
            · have hr20 : resB = 20#64 := by bv_omega
              m4_steps; exact hQ 20#64 sB mB hinvB hcvB hfuelB (Or.inr rfl)
                (fun _ => hunsB hr20) hmB
            m4_split
            · have hinc : sB.core.inconsistent ≠ 0#64 := by bv_omega
              obtain ⟨F_curB, hwB⟩ := hinvB.exists_witness
              have huns := hwB.2.1.ext_sound.2 (hwB.2.1.inconsistent_sound hinc)
              m4_steps; exact hQ 20#64 sB mB hinvB hcvB hfuelB (Or.inr rfl) (fun _ => huns) hmB
            · m4_steps; exact hQ 1#64 sB mB hinvB hcvB hfuelB (Or.inl rfl)
                (fun h => by cases h) hmB)
          (fun _ hJbrk => by
            refine wp_loop_inv (ts := [i64, i64, i64])
              (fun (budgetL, remL, vL, ()) ml => vL.toNat ≤ s.core.cur_vars ∧
                ∃ sL, FullDenseInv c F0 sL ∧ sL.core.cur_vars = s.core.cur_vars ∧
                  sL.core.fuel.toNat ≤ s.core.fuel.toNat ∧ M4TmkZero sL ∧
                  (FullMem c sL ⋆ R) ml)
              (fun (_, _, vL, ()) _ => s.core.cur_vars - vL.toNat)
              (fun _ hLv => by
                m4_steps
                exact hLv (budget, tick_lim, 0#64, ()) m0
                  ⟨Nat.zero_le _, s0, hinv0, rfl, le_refl _, ht0_zero, hm0⟩)
              (fun _ (budgetL, remL, vL, ()) ml
                  ⟨hv_le, sL, hinvL, hcvL, hfuelL, htmkL, hml⟩ hLv => by
                have hbrk := hJbrk (budgetL, remL, vL, 1#64, ()) ml
                  ⟨sL, hinvL, hcvL, hfuelL, Or.inl rfl, (fun h => by cases h), hml⟩
                m4_split; rotate_left; · m4_steps; exact hbrk
                m4_split; rotate_left; · m4_steps; exact hbrk
                m4_split; rotate_left; · m4_steps; exact hbrk
                m4_split; rotate_left; · m4_steps; exact hbrk
                m4_split; rotate_left; · m4_steps; exact hbrk
                have hcvL_le := hinvL.lengths.core_ok.cur_vars_le
                have hv_lt : vL.toNat < sL.core.cur_vars := by
                  have : vL.toNat < s.core.cur_vars % 2 ^ 64 := by bv_omega
                  omega
                have hfl_len := hinvL.lengths.core_ok.flags_len
                have hval_len := hinvL.lengths.core_ok.vals_len
                have hv_fl : vL.toNat < sL.core.flags.length := by omega
                have h2v_shl : (vL <<< (1 : Nat)).toNat = 2 * vL.toNat := by
                  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
                    Nat.mod_eq_of_lt (by omega : vL.toNat * 2 < 2 ^ 64)]; omega
                have h2v_vals : (vL <<< (1 : Nat)).toNat < sL.core.vals.length := by omega
                have hv1 : (vL + 1#64).toNat = vL.toNat + 1 := m4_bv64_add1 (by omega)
                m4_to_group; refine wp_unroll_group fun _ _ => ?_
                m4_split; rotate_left
                · m4_steps; exact hLv (budgetL, remL, vL + 1#64, ()) ml (by dsimp only; omega)
                    ⟨by omega, sL, hinvL, hcvL, hfuelL, htmkL, hml⟩
                m4_split; rotate_left
                · m4_steps; exact hLv (budgetL, remL, vL + 1#64, ()) ml (by dsimp only; omega)
                    ⟨by omega, sL, hinvL, hcvL, hfuelL, htmkL, hml⟩
                m4_to_group
                let flL' := sL.core.flags.set vL.toNat
                  ((sL.core.flags[vL.toNat]'hv_fl) &&& ~~~1024#32)
                let sL' : FullState := { sL with core := { sL.core with flags := flL' } }
                have hinvL' : FullDenseInv c F0 sL' :=
                  fullDenseInv_with_flags hinvL (List.length_set.trans hfl_len)
                have htmkL' : M4TmkZero sL' := m5_tmkZero_congr htmkL rfl rfl
                obtain ⟨F_curL, hwL⟩ := hinvL'.exists_witness
                have hv32 : (vL.setWidth 32).toNat < sL'.core.cur_vars := by
                  rw [bv64_to32_toNat vL (by omega)]; exact hv_lt
                m4_steps
                m4_call hVar
                refine ⟨c, F0, F_curL, sL', R, rfl, hwL, hcap, hv32, htmkL', hm,
                  fun rV sV mV hwV hcvV hfuelV htmkV _ hrV_uns hmV => ?_⟩
                have hfuelV0 := Nat.le_trans hfuelV hfuelL
                m4_split
                · have hrV20 : rV = 20#64 := by bv_omega
                  m4_steps; exact hJbrk (budgetL - 1#64, remL, vL, 20#64, ()) mV
                    ⟨sV, hwV.toDense, hcvV.trans hcvL, hfuelV0, Or.inr rfl,
                     (fun _ => hrV_uns hrV20), hmV⟩
                · have hk11V : 2304 + (BitVec.ofNat 64 11).toNat <
                      sV.scratch.scratch_buf.length := by
                    rw [hwV.1.scratch_ok.scratch_buf_len]; unfold k5MinScr at hcap; simp
                    omega
                  m4_to_group
                  refine wp_join_group (ts := [i64])
                    (fun (_remN, ()) mrN => mrN = mV)
                    (fun _ (remN, ()) mrN hmrN => by
                      subst mrN; m4_steps
                      exact hLv (budgetL - 1#64, remN, vL + 1#64, ()) mV
                        (by dsimp only; omega)
                        ⟨by omega, sV, hwV.toDense, hcvV.trans hcvL, hfuelV0, htmkV, hmV⟩)
                    (fun _ hJrn => by
                      m4_split <;> (m4_steps; exact hJrn _ mV rfl)))))

end SweepDenseProofs

/-! ## 6. `full_probe_tail_m5_wp` (Canonical `FullFastSched.schedProbeTailSpec`) -/

section ProbeTailProofs

open scoped Full.FullArenaTactics

/-- Parametric `Func.wp` theorem for `full_probe_tail_m5` against canonical
`FullFastSched.schedProbeTailSpec`. -/
theorem full_probe_tail_m5_wp (Γ : Env)
    (hBone : ∀ a m Q X, FullM3Backbone.fullBackboneSpec a m Q X →
      Γ "full_backbone" [i64, i64] [i64] a m Q X)
    (hTrans : ∀ a m Q X, FullFastBveBudgets.fullTransitiveFastSpec a m Q X →
      Γ "full_transitive_m5" [i64, i64] [i64] a m Q X)
    (hMin : ∀ a m Q X, FullFastSched.schedMinU64Spec a m Q X →
      Γ "full_min_u64" [i64, i64] [i64] a m Q X)
    (hPRun : ∀ a m Q X, FullM3Backbone.fullProbeRunCursorSpec a m Q X →
      Γ "full_probe_run" [i64, i64] [i64] a m Q X)
    (hViv : ∀ a m Q X, m5VivifySpec a m Q X →
      Γ "full_vivify_m5" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullFastSched.schedProbeTailSpec a m Q X →
      Func.wp Γ full_probe_tail_m5_body a m Q X := by
  rintro ⟨h, dticks, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hcl0, hm, hQ⟩
  unfold Func.wp full_probe_tail_m5_body
  c0_hsteps_nogrp
  refine wp_join_state0 (α := FullState)
    (fun s1 m1 => FullSparseInv c F0 s1 ∧ s1.core.cur_level = 0 ∧
      s1.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s1 ⋆ R) m1)
    (fun _ s1 m1 ⟨hinv1, hcl1, hfu1, hm1⟩ => by
      c0_hsteps_nogrp
      refine wp_join_state0 (α := FullState)
        (fun s2 m2 => FullSparseInv c F0 s2 ∧ s2.core.cur_level = 0 ∧
          s2.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s2 ⋆ R) m2)
        (fun _ s2 m2 ⟨hinv2, hcl2, hfu2, hm2⟩ => by
          c0_hsteps; c0_call hMin; intro pbud _
          c0_hsteps_nogrp
          refine wp_join_state0 (α := FullState)
            (fun s3 m3 => FullSparseInv c F0 s3 ∧ s3.core.cur_level = 0 ∧
              s3.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s3 ⋆ R) m3)
            (fun _ s3 m3 ⟨hinv3, hcl3, hfu3, hm3⟩ => by
              c0_hsteps; c0_call hViv; refine ⟨c, F0, s3, R, rfl, hinv3, hm3, ?_⟩
              intro r4 s4 m4 hinv4 hcl4 _ hfu4 _ hu4 hm4
              c0_hsteps
              · exact hQ 20#64 s4 m4 hinv4 hcl4 (by omega) (Or.inr rfl) (fun _ => hu4 hc) hm4
              · exact hQ 1#64 s4 m4 hinv4 hcl4 (by omega) (Or.inl rfl) (fun h => by cases h) hm4)
            (fun J3 hJ3 => by
              c0_hsplit
              · c0_hsteps; c0_call hPRun; refine ⟨c, F0, s2, R, rfl, hinv2, hm2, ?_⟩
                intro rp s3 m3 hinv3 hcl3 _ hfu3 _ hup3 _ hm3; c0_hsteps
                · exact hQ 20#64 s3 m3 hinv3 hcl3 (by omega) (Or.inr rfl) (fun _ => hup3 hc) hm3
                exact hJ3 s3 m3 ⟨hinv3, hcl3, by omega, hm3⟩
              · c0_hsteps; exact hJ3 s2 m2 ⟨hinv2, hcl2, hfu2, hm2⟩))
        (fun J2 hJ2 => by
          c0_hsplit
          · c0_hsteps; c0_call hTrans; refine ⟨c, F0, s1, R, rfl, hinv1, hm1, ?_⟩
            intro rt s2 m2 hinv2 hcl2 _ _ hfu2 _ hut2 hm2
            have hcl2' := hcl2 hcl1
            c0_hsteps
            · exact hQ 20#64 s2 m2 hinv2 hcl2' (by omega) (Or.inr rfl) (fun _ => hut2 hc) hm2
            exact hJ2 s2 m2 ⟨hinv2, hcl2', by omega, hm2⟩
          · c0_hsteps; exact hJ2 s1 m1 ⟨hinv1, hcl1, hfu1, hm1⟩))
    (fun J1 hJ1 => by
      c0_hsplit
      · c0_hsteps; c0_call hBone; refine ⟨c, F0, s, R, rfl, hinv, hm, ?_⟩
        intro rb s1 m1 hinv1 hcl1 _ hfu1 _ hub1 hm1; c0_hsteps
        · exact hQ 20#64 s1 m1 hinv1 hcl1 hfu1 (Or.inr rfl) (fun _ => hub1 hc) hm1
        exact hJ1 s1 m1 ⟨hinv1, hcl1, hfu1, hm1⟩
      · c0_hsteps; exact hJ1 s m ⟨hinv, hcl0, Nat.le_refl _, hm⟩)

end ProbeTailProofs

end LeanQbe.T.Examples.Kissat.FullM5Orch
