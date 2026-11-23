module

public import LeanQbe.T.Examples.Kissat.FullM7MemShrinkProof0
import LeanQbe.T.AbiLemmas
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullArena1
import LeanQbe.T.Logic.Bytes
import LeanQbe.T.Logic.Cells
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M7 Memory-Shrink Prototype A (`full_init_state_m7_wp`)

Proves `full_init_state_m7_wp` against `m7InitStateSpec` (`FullM7MemShrinkProof0`),
bridging the `region hdr avail` heap allocation into `MemShrinkMem` + `MemShrinkSparseInv`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM7MemShrink

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullParseInitHelpers
open LeanQbe.T.Examples.Kissat.Full.FullParseInitSpecs
open scoped FullArenaTactics FullParseInitTactics
open Kraken.Bedrock2.Test

private def m7InitExtCap (nc rem : Nat) : Nat :=
  let dyn := fullInitDelCap rem * 12 + 4 * m7CalcExtCap rem + 4 * m7CalcScrCap rem
  if rem < dyn + nc * 40 + 136 then 0 else m7CalcExtCap rem

private def m7InitScrCap (nc rem : Nat) : Nat :=
  let dyn := fullInitDelCap rem * 12 + 4 * m7CalcExtCap rem + 4 * m7CalcScrCap rem
  if rem < dyn + nc * 40 + 136 then 0 else m7CalcScrCap rem

private def m7InitDyn (nc rem : Nat) : Nat :=
  fullInitDelCap rem * 12 + 4 * m7InitExtCap nc rem + 4 * m7InitScrCap nc rem

private theorem m7InitDyn_le {nc rem : Nat} (hrem : nc * 40 + 136 ≤ rem) :
    m7InitDyn nc rem + 40 ≤ rem := by
  unfold m7InitDyn m7InitExtCap m7InitScrCap fullInitDelCap; dsimp only
  split <;> split <;> omega

private theorem m7InitArenas_le {nc avail_dyn : Nat} (hrem : nc * 40 + 136 ≤ avail_dyn) :
    let rem := avail_dyn - m7InitDyn nc avail_dyn
    8 * fullInitAp rem + 8 * fullInitWp rem + 8 * fullInitRp rem + m7InitDyn nc avail_dyn ≤
      avail_dyn := by
  have hd := m7InitDyn_le hrem
  have h1 := fullInitAp_add_rp_le (avail_dyn - m7InitDyn nc avail_dyn)
  have h2 : fullInitWp (avail_dyn - m7InitDyn nc avail_dyn) ≤
      (avail_dyn - m7InitDyn nc avail_dyn) / 8 -
      fullInitAp (avail_dyn - m7InitDyn nc avail_dyn) -
      fullInitRp (avail_dyn - m7InitDyn nc avail_dyn) := Nat.min_le_left _ _
  omega

private theorem m7InitWp_ge_one {rem : Nat} (hrem : 40 ≤ rem) : 1 ≤ fullInitWp rem := by
  unfold fullInitWp fullInitRp fullInitAp; omega

private theorem m7_hdr_region_rejoin {cnf_ptr hdr_addr mv' nc' cur' val' : BitVec 64}
    {avail : Nat} {cnfBytes : List UInt8} {w140 : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hav : 1152 ≤ avail) (hle : avail ≤ 2 ^ 64) (hw : w140.length = 140)
    (hm : (bytes cnf_ptr cnfBytes ⋆ dimacsState hdr_addr mv' nc' cur' val' ⋆
      array64 (hdr_addr + 32) w140 ⋆
      region (hdr_addr + 1152) (avail - 1152) ⋆ R) m) :
    (bytes cnf_ptr cnfBytes ⋆ region hdr_addr avail ⋆ R) m := by
  have h1 : (dimacsState hdr_addr mv' nc' cur' val' ⋆
      (array64 (hdr_addr + 32) w140 ⋆ region (hdr_addr + 1152) (avail - 1152) ⋆
        bytes cnf_ptr cnfBytes ⋆ R)) m := sep_ac hm
  have h2 : (region hdr_addr 32 ⋆
      (array64 (hdr_addr + 32) w140 ⋆ region (hdr_addr + 1152) (avail - 1152) ⋆
        bytes cnf_ptr cnfBytes ⋆ R)) m :=
    sep_mono (P' := region hdr_addr 32) (fun _ hd => dimacsState_to_region hd) h1
  have h3 : (array64 (hdr_addr + 32) w140 ⋆
      (region hdr_addr 32 ⋆ region (hdr_addr + 1152) (avail - 1152) ⋆
        bytes cnf_ptr cnfBytes ⋆ R)) m := sep_ac h2
  rw [array64_eq_word8Array] at h3
  have h4 : (region (hdr_addr + 32) 1120 ⋆
      (region hdr_addr 32 ⋆ region (hdr_addr + 1152) (avail - 1152) ⋆
        bytes cnf_ptr cnfBytes ⋆ R)) m :=
    sep_mono (P' := region (hdr_addr + 32) 1120)
      (fun _ hw8 => by simpa [hw] using word8Array_to_region (by omega) hw8) h3
  have h5 : ((region (hdr_addr + 32) 1120 ⋆ region (hdr_addr + 1152) (avail - 1152)) ⋆
      (region hdr_addr 32 ⋆ bytes cnf_ptr cnfBytes ⋆ R)) m := sep_ac h4
  have h6 : (region (hdr_addr + 32) (avail - 32) ⋆
      (region hdr_addr 32 ⋆ bytes cnf_ptr cnfBytes ⋆ R)) m := by
    refine sep_mono (fun _ hr => ?_) h5
    rw [show avail - 32 = 1120 + (avail - 1152) by omega, region_split (by omega),
      show (hdr_addr + 32) + BitVec.ofNat 64 1120 = hdr_addr + 1152 by
        rw [show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl,
          show (1152 : BitVec 64) = BitVec.ofNat 64 1152 from rfl, ptr_add_ofNat]]
    exact hr
  have h7 : ((region hdr_addr 32 ⋆ region (hdr_addr + 32) (avail - 32)) ⋆
      (bytes cnf_ptr cnfBytes ⋆ R)) m := sep_ac h6
  have h8 : (region hdr_addr avail ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m := by
    refine sep_mono (fun _ hr => ?_) h7
    rw [show avail = 32 + (avail - 32) by omega, region_split (by omega),
      show hdr_addr + BitVec.ofNat 64 32 = hdr_addr + 32 from rfl]
    exact hr
  exact sep_ac h8

private theorem m7_peel_res_i8 (a : BitVec 64) (n pad rest : Nat) (hn : n ≤ pad)
    (hfit : pad + rest ≤ 2 ^ 64) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region a (pad + rest) ⋆ R) m) :
    ∃ xs : List (BitVec 8), xs.length = n ∧
      (region (a + BitVec.ofNat 64 pad) rest ⋆
        ((array (t := i8) a xs ⋆ region (a + BitVec.ofNat 64 n) (pad - n)) ⋆ R)) m := by
  rw [region_split hfit] at hm
  have h1 : (region a pad ⋆ (region (a + BitVec.ofNat 64 pad) rest ⋆ R)) m := sep_ac hm
  have h2 : (((fun m1 => ∃ xs : List (BitVec 8), xs.length = n ∧ array (t := i8) a xs m1) ⋆
      region (a + BitVec.ofNat 64 n) (pad - n)) ⋆
      (region (a + BitVec.ofNat 64 pad) rest ⋆ R)) m := sep_mono (fun _ hr => by
    rw [show pad = n + (pad - n) by omega, region_split (by omega)] at hr
    exact sep_mono (fun _ h => region_to_array_i8 n (by omega) h) hr) h1
  have h3 : ((fun m1 => ∃ xs : List (BitVec 8), xs.length = n ∧ array (t := i8) a xs m1) ⋆
      (region (a + BitVec.ofNat 64 n) (pad - n) ⋆
        (region (a + BitVec.ofNat 64 pad) rest ⋆ R))) m := by
    rw [sep_assoc] at h2; exact h2
  obtain ⟨xs, h4⟩ := sep_ex_l.mp h3
  obtain ⟨hxs, h5⟩ := sep_pure_l.mp h4
  exact ⟨xs, hxs, sep_ac h5⟩

private theorem m7_peel_res_u32 (a : BitVec 64) (n pad rest : Nat) (hn : 4 * n ≤ pad)
    (hfit : pad + rest ≤ 2 ^ 64) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region a (pad + rest) ⋆ R) m) :
    ∃ xs : List (BitVec 32), xs.length = n ∧
      (region (a + BitVec.ofNat 64 pad) rest ⋆
        ((array (t := i32) a xs ⋆ region (a + BitVec.ofNat 64 (4 * n)) (pad - 4 * n)) ⋆ R)) m := by
  rw [region_split hfit] at hm
  have h1 : (region a pad ⋆ (region (a + BitVec.ofNat 64 pad) rest ⋆ R)) m := sep_ac hm
  have h2 : (((fun m1 => ∃ xs : List (BitVec 32), xs.length = n ∧ array (t := i32) a xs m1) ⋆
      region (a + BitVec.ofNat 64 (4 * n)) (pad - 4 * n)) ⋆
      (region (a + BitVec.ofNat 64 pad) rest ⋆ R)) m := sep_mono (fun _ hr => by
    rw [show pad = 4 * n + (pad - 4 * n) by omega, region_split (by omega)] at hr
    exact sep_mono (fun _ h => region_to_array_i32 n (by omega) h) hr) h1
  have h3 : ((fun m1 => ∃ xs : List (BitVec 32), xs.length = n ∧ array (t := i32) a xs m1) ⋆
      (region (a + BitVec.ofNat 64 (4 * n)) (pad - 4 * n) ⋆
        (region (a + BitVec.ofNat 64 pad) rest ⋆ R))) m := by
    rw [sep_assoc] at h2; exact h2
  obtain ⟨xs, h4⟩ := sep_ex_l.mp h3
  obtain ⟨hxs, h5⟩ := sep_pure_l.mp h4
  exact ⟨xs, hxs, sep_ac h5⟩

private theorem m7_peel_arr32 (a : BitVec 64) (n rest : Nat)
    (hfit : 4 * n + rest ≤ 2 ^ 64) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region a (4 * n + rest) ⋆ R) m) :
    ∃ xs : List (BitVec 32), xs.length = n ∧
      (region (a + BitVec.ofNat 64 (4 * n)) rest ⋆ (array (t := i32) a xs ⋆ R)) m := by
  rw [region_split hfit] at hm
  have h1 : (region a (4 * n) ⋆ (region (a + BitVec.ofNat 64 (4 * n)) rest ⋆ R)) m := sep_ac hm
  have h2 := sep_mono (fun _ h => region_to_array_i32 n (by omega) h) h1
  obtain ⟨xs, h3⟩ := sep_ex_l.mp h2
  obtain ⟨hxs, h4⟩ := sep_pure_l.mp h3
  exact ⟨xs, hxs, sep_ac h4⟩

private theorem m7_peel_arr64 (a : BitVec 64) (n rest : Nat)
    (hfit : 8 * n + rest ≤ 2 ^ 64) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region a (8 * n + rest) ⋆ R) m) :
    ∃ xs : List (BitVec 64), xs.length = n ∧
      (region (a + BitVec.ofNat 64 (8 * n)) rest ⋆ (array64 a xs ⋆ R)) m := by
  rw [region_split hfit] at hm
  have h1 : (region a (8 * n) ⋆ (region (a + BitVec.ofNat 64 (8 * n)) rest ⋆ R)) m := sep_ac hm
  have h2 := sep_mono (fun _ h => region_to_array64 n (by omega) h) h1
  obtain ⟨xs, h3⟩ := sep_ex_l.mp h2
  obtain ⟨hxs, h4⟩ := sep_pure_l.mp h3
  exact ⟨xs, hxs, sep_ac h4⟩

private theorem m7_peel_reg (a : BitVec 64) (n rest : Nat) (hfit : n + rest ≤ 2 ^ 64)
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (region a (n + rest) ⋆ R) m) :
    (region (a + BitVec.ofNat 64 n) rest ⋆ (region a n ⋆ R)) m := by
  rw [region_split hfit] at hm
  exact Eq.mp (congrFun (by ac_rfl) m) hm

private structure M7InitArrs (c : MemShrinkCfg) where
  (vals mrk lit_mark phases phases_target phases_best : List (BitVec 8))
  (flags lvl rsns trl trail_pos tmp min_clr : List (BitVec 32))
  (heap pos shrink_stk q_prev q_next q_stamp frame_trail frame_dec : List (BitVec 32))
  (wvec min_stk glue_used last_learned arena wstk delayed red_refs extend_stk scratch_buf :
    List (BitVec 32))
  (score : List (BitVec 64))
  (hvals : vals.length = 2 * c.max_vars) (hmrk : mrk.length = c.max_vars)
  (hlm : lit_mark.length = 2 * c.max_vars) (hph : phases.length = c.max_vars)
  (hpht : phases_target.length = c.max_vars) (hphb : phases_best.length = c.max_vars)
  (hfl : flags.length = c.max_vars) (hlv : lvl.length = c.max_vars)
  (hrs : rsns.length = c.max_vars) (htr : trl.length = c.max_vars)
  (htp : trail_pos.length = c.max_vars) (htm : tmp.length = c.max_vars)
  (hmc : min_clr.length = c.max_vars) (hhp : heap.length = c.max_vars)
  (hps : pos.length = c.max_vars) (hss : shrink_stk.length = c.max_vars)
  (hqp : q_prev.length = c.max_vars) (hqn : q_next.length = c.max_vars)
  (hqs : q_stamp.length = c.max_vars) (hft : frame_trail.length = c.max_vars + 1)
  (hfd : frame_dec.length = c.max_vars + 1) (hwv : wvec.length = 4 * c.max_vars)
  (hmst : min_stk.length = 2 * c.minDepth) (hgu : glue_used.length = 64)
  (hll : last_learned.length = 16) (har : arena.length = c.arena_cap)
  (hwk : wstk.length = c.wcap) (hdl : delayed.length = 3 * c.delayed_cap)
  (hrr : red_refs.length = c.red_cap) (hex : extend_stk.length = c.extend_cap)
  (hsc_b : scratch_buf.length = c.scratch_cap) (hscr : score.length = c.max_vars)

private def m7InitState (c : MemShrinkCfg) (d_cur d_val fuel : BitVec 64) (a : M7InitArrs c) :
    FullState :=
  { core :=
      { d_cur := d_cur, d_val := d_val, cur_vars := c.mv, unassigned := BitVec.ofNat 64 c.mv
        arena_len := 0, wlen := 1, wusable := 0#64, arena_garbage := 0#64
        first_reducible := 0xFFFFFFFF#64, num_irred := 0#64, num_redundant := 0#64
        num_binary := 0#64, unflushed := 0#64, probing := 0#64, trail_end := 0
        propagated := 0, cur_level := 0, fuel := fuel, confl_ref := 0xFFFFFFFF#64
        confl_type := 0#64, confl_lit0 := 0#64, confl_lit1 := 0#64, tmp_cnt := 0, tmp_len := 0
        min_clr_len := 0, min_clr_full := 0#64, oom := 0#64, dense_mode := 0#64
        inconsistent := 0#64, vals := a.vals, lit_mark := a.lit_mark, mrk := a.mrk
        flags := a.flags, lvl := a.lvl, rsns := a.rsns, trl := a.trl, trail_pos := a.trail_pos
        tmp := a.tmp, min_clr := a.min_clr, frame_trail := a.frame_trail
        frame_dec := a.frame_dec, wvec := a.wvec, repr := [], min_stk := a.min_stk
        arena := a.arena, wstk := a.wstk }
    scratch :=
      { heap_len := c.mv, scinc := 1#64 <<< 28, rel_period := 1024#64, rel_limit := 1048576#64
        rel_wait := 1024#64, rel_u := 1#64, rel_v := 1#64, rel_trigger := 0#64
        conflicts := 0#64, learned_lits := 0#64, min_removed := 0#64, delayed_len := 0
        stable := 0#64, switched := 0#64, mode_count := 0#64, mode_confl_lim := 1000#64
        mode_tick_lim := 0#64, mode_saved_ticks := 0#64, search_ticks := 0#64
        q_first := if c.mv == 0 then 0xFFFFFFFF#64 else 0#64
        q_last := if c.mv == 0 then 0xFFFFFFFF#64 else BitVec.ofNat 64 (c.mv - 1)
        q_search_idx := if c.mv == 0 then 0xFFFFFFFF#64 else BitVec.ofNat 64 (c.mv - 1)
        q_search_stamp := BitVec.ofNat 64 c.mv, q_cur_stamp := BitVec.ofNat 64 c.mv
        target_assigned := 0#64, best_assigned := 0#64, rephase_limit := 1000#64
        rephased := 0#64, reduce_limit := 1000#64, reductions := 0#64, tier1 := 2#64
        tier2 := 6#64, restarts := 0#64, restart_limit := 1#64, ema_fast_biased := 0#64
        ema_fast_exp := 1#64 <<< 24, ema_slow_biased := 0#64, ema_slow_exp := 1#64 <<< 24
        extend_len := 0
        rng_state := 0x9E3779B97F4A7C15#64 ^^^ BitVec.ofNat 64 (c.mv + 1)
        chrono_levels := 100#64, otfs_cnt := 0#64, eager_sub_cnt := 0#64, probe_limit := 2000#64
        probings := 0#64, elim_limit := 5000#64, eliminations := 0#64, elim_bound := 0#64
        iterating := 0#64, hbr_cnt := 0#64, trans_cnt := 0#64, viv_cnt := 0#64
        subst_cnt := 0#64, cong_cnt := 0#64, sweep_cnt := 0#64, bve_cnt := 0#64
        bce_cnt := 0#64, bva_cnt := 0#64, walk_cnt_stat := 0#64, fwd_sub_cnt := 0#64
        fwd_str_cnt := 0#64, ant_sz := 0#64, res_sz := 0#64, walk_vals := []
        phases := a.phases, phases_target := a.phases_target, phases_best := a.phases_best
        walk_best := [], heap := a.heap, pos := a.pos, shrink_stk := a.shrink_stk
        q_prev := a.q_prev, q_next := a.q_next, q_stamp := a.q_stamp, wsort := []
        work_stk1 := [], work_stk2 := [], tarjan_mark := [], tarjan_reach := []
        score := a.score, sim_sig := [], glue_used := a.glue_used
        last_learned := a.last_learned, delayed := a.delayed, red_refs := a.red_refs
        extend_stk := a.extend_stk, scratch_buf := a.scratch_buf } }

private theorem m7_init_lengthsOk (c : MemShrinkCfg) (hw1 : 1 ≤ c.wcap)
    (d_cur d_val fuel : BitVec 64) (a : M7InitArrs c) :
    MemShrinkLengthsOk c (m7InitState c d_cur d_val fuel a) :=
  { vals_len := a.hvals, lit_mark_len := a.hlm, mrk_len := a.hmrk, flags_len := a.hfl
    lvl_len := a.hlv, rsns_len := a.hrs, trl_len := a.htr, trail_pos_len := a.htp
    tmp_len_arr := a.htm, min_clr_len_arr := a.hmc, frame_trail_len := a.hft
    frame_dec_len := a.hfd, wvec_len := a.hwv, min_stk_len := a.hmst, arena_len_arr := a.har
    wstk_len_arr := a.hwk, phases_len := a.hph, phases_target_len := a.hpht
    phases_best_len := a.hphb, heap_len_arr := a.hhp, pos_len := a.hps, shrink_stk_len := a.hss
    q_prev_len := a.hqp, q_next_len := a.hqn, q_stamp_len := a.hqs, score_len := a.hscr
    glue_used_len := a.hgu, last_learned_len := a.hll, delayed_len_arr := a.hdl
    red_refs_len := a.hrr, extend_stk_len := a.hex, scratch_buf_len := a.hsc_b
    cur_vars_ge := by have := c.hbva; dsimp [m7InitState]; omega
    cur_vars_le := by have := c.hbva; dsimp [m7InitState]; omega
    arena_len_le := by dsimp [m7InitState]; omega
    wlen_le := by dsimp [m7InitState]; exact hw1
    trail_end_le := by dsimp [m7InitState]; omega
    propagated_le := by dsimp [m7InitState]; omega
    tmp_len_le := by dsimp [m7InitState]; omega
    min_clr_len_le := by dsimp [m7InitState]; omega
    heap_len_le := by have := c.hbva; dsimp [m7InitState]; omega
    delayed_len_le := by dsimp [m7InitState]; omega
    extend_len_le := by dsimp [m7InitState]; omega }

private theorem m7_pack5 {A1 A2 A3 A4 A5 Q R : Mem 64 → Prop} {m : Mem 64}
    (hQ : Q = (A1 ⋆ A2 ⋆ A3 ⋆ A4 ⋆ A5))
    (hm : (A5 ⋆ (A4 ⋆ (A3 ⋆ (A2 ⋆ (A1 ⋆ R))))) m) : (Q ⋆ R) m := by
  rw [hQ]; exact sep_ac hm

private theorem m7_pack6 {A1 A2 A3 A4 A5 A6 Q R : Mem 64 → Prop} {m : Mem 64}
    (hQ : Q = (A1 ⋆ A2 ⋆ A3 ⋆ A4 ⋆ A5 ⋆ A6))
    (hm : (A6 ⋆ (A5 ⋆ (A4 ⋆ (A3 ⋆ (A2 ⋆ (A1 ⋆ R)))))) m) : (Q ⋆ R) m := by
  rw [hQ]; exact sep_ac hm

private theorem m7_pack7 {A1 A2 A3 A4 A5 A6 A7 Q R : Mem 64 → Prop} {m : Mem 64}
    (hQ : Q = (A1 ⋆ A2 ⋆ A3 ⋆ A4 ⋆ A5 ⋆ A6 ⋆ A7))
    (hm : (A7 ⋆ (A6 ⋆ (A5 ⋆ (A4 ⋆ (A3 ⋆ (A2 ⋆ (A1 ⋆ R))))))) m) : (Q ⋆ R) m := by
  rw [hQ]; exact sep_ac hm

private theorem m7_pack8 {A1 A2 A3 A4 A5 A6 A7 A8 Q R : Mem 64 → Prop} {m : Mem 64}
    (hQ : Q = (A1 ⋆ A2 ⋆ A3 ⋆ A4 ⋆ A5 ⋆ A6 ⋆ A7 ⋆ A8))
    (hm : (A8 ⋆ (A7 ⋆ (A6 ⋆ (A5 ⋆ (A4 ⋆ (A3 ⋆ (A2 ⋆ (A1 ⋆ R)))))))) m) : (Q ⋆ R) m := by
  rw [hQ]; exact sep_ac hm

private def m7SegBytes (c : MemShrinkCfg) (v mk ph pht phb : List (BitVec 8)) : Mem 64 → Prop :=
  (array (t := i8) c.pVals v ⋆
    region (c.pVals + BitVec.ofNat 64 (2 * c.max_vars)) (valsBytes c.max_vars - 2 * c.max_vars)) ⋆
  (array (t := i8) c.pMark mk ⋆
    region (c.pMark + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
  (array (t := i8) c.pPhases ph ⋆
    region (c.pPhases + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
  (array (t := i8) c.pPhasesTarget pht ⋆
    region (c.pPhasesTarget + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars)) ⋆
  (array (t := i8) c.pPhasesBest phb ⋆
    region (c.pPhasesBest + BitVec.ofNat 64 c.max_vars) (markBytes c.max_vars - c.max_vars))

private def m7SegU32A (c : MemShrinkCfg)
    (fl lv rs tr tp tm hp ps : List (BitVec 32)) : Mem 64 → Prop :=
  (array (t := i32) c.pFlags fl ⋆
    region (c.pFlags + BitVec.ofNat 64 (4 * c.max_vars))
      (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pLevel lv ⋆
    region (c.pLevel + BitVec.ofNat 64 (4 * c.max_vars))
      (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pReason rs ⋆
    region (c.pReason + BitVec.ofNat 64 (4 * c.max_vars))
      (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pTrail tr ⋆
    region (c.pTrail + BitVec.ofNat 64 (4 * c.max_vars))
      (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pTrailPos tp ⋆
    region (c.pTrailPos + BitVec.ofNat 64 (4 * c.max_vars))
      (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pTmp tm ⋆
    region (c.pTmp + BitVec.ofNat 64 (4 * c.max_vars)) (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pHeap hp ⋆
    region (c.pHeap + BitVec.ofNat 64 (4 * c.max_vars))
      (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pPos ps ⋆
    region (c.pPos + BitVec.ofNat 64 (4 * c.max_vars)) (u32FullBytes c.max_vars - 4 * c.max_vars))

private def m7SegU32B (c : MemShrinkCfg)
    (mc ss qp qn qs ft fd : List (BitVec 32)) : Mem 64 → Prop :=
  (array (t := i32) c.pMinClr mc ⋆
    region (c.pMinClr + BitVec.ofNat 64 (4 * c.max_vars))
      (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pShrinkStk ss ⋆
    region (c.pShrinkStk + BitVec.ofNat 64 (4 * c.max_vars))
      (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pQPrev qp ⋆
    region (c.pQPrev + BitVec.ofNat 64 (4 * c.max_vars))
      (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pQNext qn ⋆
    region (c.pQNext + BitVec.ofNat 64 (4 * c.max_vars))
      (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pQStamp qs ⋆
    region (c.pQStamp + BitVec.ofNat 64 (4 * c.max_vars))
      (u32FullBytes c.max_vars - 4 * c.max_vars)) ⋆
  (array (t := i32) c.pFrameTrail ft ⋆
    region (c.pFrameTrail + BitVec.ofNat 64 (4 * (c.max_vars + 1)))
      (u32FullBytes c.max_vars - 4 * (c.max_vars + 1))) ⋆
  (array (t := i32) c.pFrameDec fd ⋆
    region (c.pFrameDec + BitVec.ofNat 64 (4 * (c.max_vars + 1)))
      (u32FullBytes c.max_vars - 4 * (c.max_vars + 1)))

private def m7SegTailA (c : MemShrinkCfg) (wv ms gu ll : List (BitVec 32))
    (sc : List (BitVec 64)) : Mem 64 → Prop :=
  array (t := i32) c.pWvec wv ⋆ array64 c.pScore sc ⋆ array (t := i32) c.pMinStk ms ⋆
  array (t := i32) c.pGlueUsed gu ⋆ array (t := i32) c.pLastLearned ll

private def m7SegTailB (c : MemShrinkCfg) (ar wk dl rr ex sb : List (BitVec 32)) : Mem 64 → Prop :=
  array (t := i32) c.pArena ar ⋆ array (t := i32) c.pWstk wk ⋆ array (t := i32) c.pDelayed dl ⋆
  array (t := i32) c.pRedRefs rr ⋆ array (t := i32) c.pExtendStk ex ⋆
  array (t := i32) c.pScratchBuf sb

private theorem m7_peel_segBytes (c : MemShrinkCfg) (rest : Nat)
    (hfit : valsBytes c.max_vars + 4 * markBytes c.max_vars + rest ≤ 2 ^ 64)
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region c.pVals (valsBytes c.max_vars + 4 * markBytes c.max_vars + rest) ⋆ R) m) :
    ∃ vals mrk ph pht phb : List (BitVec 8),
      vals.length = 2 * c.max_vars ∧ mrk.length = c.max_vars ∧ ph.length = c.max_vars ∧
      pht.length = c.max_vars ∧ phb.length = c.max_vars ∧
      (m7SegBytes c vals mrk ph pht phb ⋆ region c.pFlags rest ⋆ R) m := by
  have hvb : 2 * c.max_vars ≤ valsBytes c.max_vars := by unfold valsBytes; omega
  have hmb : c.max_vars ≤ markBytes c.max_vars := by unfold markBytes; omega
  rw [show valsBytes c.max_vars + 4 * markBytes c.max_vars + rest =
      valsBytes c.max_vars + (4 * markBytes c.max_vars + rest) by omega] at hm
  obtain ⟨vals, hv, hm⟩ := m7_peel_res_i8 c.pVals (2 * c.max_vars) (valsBytes c.max_vars)
    (4 * markBytes c.max_vars + rest) hvb (by omega) hm
  rw [← MemShrinkCfg.pMark_eq, show 4 * markBytes c.max_vars + rest =
      markBytes c.max_vars + (3 * markBytes c.max_vars + rest) by omega] at hm
  obtain ⟨mrk, hmk, hm⟩ := m7_peel_res_i8 c.pMark c.max_vars (markBytes c.max_vars)
    (3 * markBytes c.max_vars + rest) hmb (by omega) hm
  rw [← MemShrinkCfg.pPhases_eq, show 3 * markBytes c.max_vars + rest =
      markBytes c.max_vars + (2 * markBytes c.max_vars + rest) by omega] at hm
  obtain ⟨ph, hph, hm⟩ := m7_peel_res_i8 c.pPhases c.max_vars (markBytes c.max_vars)
    (2 * markBytes c.max_vars + rest) hmb (by omega) hm
  rw [← MemShrinkCfg.pPhasesTarget_eq, show 2 * markBytes c.max_vars + rest =
      markBytes c.max_vars + (markBytes c.max_vars + rest) by omega] at hm
  obtain ⟨pht, hpht, hm⟩ := m7_peel_res_i8 c.pPhasesTarget c.max_vars (markBytes c.max_vars)
    (markBytes c.max_vars + rest) hmb (by omega) hm
  rw [← MemShrinkCfg.pPhasesBest_eq] at hm
  obtain ⟨phb, hphb, hm⟩ := m7_peel_res_i8 c.pPhasesBest c.max_vars (markBytes c.max_vars)
    rest hmb (by omega) hm
  rw [← MemShrinkCfg.pFlags_eq] at hm
  have hm' : (region c.pFlags rest ⋆ (m7SegBytes c vals mrk ph pht phb ⋆ R)) m :=
    sep_mono_r (fun _ h => m7_pack5 (by unfold m7SegBytes; rfl) h) hm
  exact ⟨vals, mrk, ph, pht, phb, hv, hmk, hph, hpht, hphb, sep_ac hm'⟩

private theorem m7_peel_segU32A (c : MemShrinkCfg) (rest : Nat)
    (hfit : 8 * u32FullBytes c.max_vars + rest ≤ 2 ^ 64) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region c.pFlags (8 * u32FullBytes c.max_vars + rest) ⋆ R) m) :
    ∃ fl lv rs tr tp tm hp ps : List (BitVec 32),
      fl.length = c.max_vars ∧ lv.length = c.max_vars ∧ rs.length = c.max_vars ∧
      tr.length = c.max_vars ∧ tp.length = c.max_vars ∧ tm.length = c.max_vars ∧
      hp.length = c.max_vars ∧ ps.length = c.max_vars ∧
      (m7SegU32A c fl lv rs tr tp tm hp ps ⋆ region c.pMinClr rest ⋆ R) m := by
  have hub : 4 * c.max_vars ≤ u32FullBytes c.max_vars := by unfold u32FullBytes; omega
  rw [show 8 * u32FullBytes c.max_vars + rest =
      u32FullBytes c.max_vars + (7 * u32FullBytes c.max_vars + rest) by omega] at hm
  obtain ⟨fl, hfl, hm⟩ := m7_peel_res_u32 c.pFlags c.max_vars (u32FullBytes c.max_vars)
    (7 * u32FullBytes c.max_vars + rest) hub (by omega) hm
  rw [← MemShrinkCfg.pLevel_eq, show 7 * u32FullBytes c.max_vars + rest =
      u32FullBytes c.max_vars + (6 * u32FullBytes c.max_vars + rest) by omega] at hm
  obtain ⟨lv, hlv, hm⟩ := m7_peel_res_u32 c.pLevel c.max_vars (u32FullBytes c.max_vars)
    (6 * u32FullBytes c.max_vars + rest) hub (by omega) hm
  rw [← MemShrinkCfg.pReason_eq, show 6 * u32FullBytes c.max_vars + rest =
      u32FullBytes c.max_vars + (5 * u32FullBytes c.max_vars + rest) by omega] at hm
  obtain ⟨rs, hrs, hm⟩ := m7_peel_res_u32 c.pReason c.max_vars (u32FullBytes c.max_vars)
    (5 * u32FullBytes c.max_vars + rest) hub (by omega) hm
  rw [← MemShrinkCfg.pTrail_eq, show 5 * u32FullBytes c.max_vars + rest =
      u32FullBytes c.max_vars + (4 * u32FullBytes c.max_vars + rest) by omega] at hm
  obtain ⟨tr, htr, hm⟩ := m7_peel_res_u32 c.pTrail c.max_vars (u32FullBytes c.max_vars)
    (4 * u32FullBytes c.max_vars + rest) hub (by omega) hm
  rw [← MemShrinkCfg.pTrailPos_eq, show 4 * u32FullBytes c.max_vars + rest =
      u32FullBytes c.max_vars + (3 * u32FullBytes c.max_vars + rest) by omega] at hm
  obtain ⟨tp, htp, hm⟩ := m7_peel_res_u32 c.pTrailPos c.max_vars (u32FullBytes c.max_vars)
    (3 * u32FullBytes c.max_vars + rest) hub (by omega) hm
  rw [← MemShrinkCfg.pTmp_eq, show 3 * u32FullBytes c.max_vars + rest =
      u32FullBytes c.max_vars + (2 * u32FullBytes c.max_vars + rest) by omega] at hm
  obtain ⟨tm, htm, hm⟩ := m7_peel_res_u32 c.pTmp c.max_vars (u32FullBytes c.max_vars)
    (2 * u32FullBytes c.max_vars + rest) hub (by omega) hm
  rw [← MemShrinkCfg.pHeap_eq, show 2 * u32FullBytes c.max_vars + rest =
      u32FullBytes c.max_vars + (u32FullBytes c.max_vars + rest) by omega] at hm
  obtain ⟨hp, hhp, hm⟩ := m7_peel_res_u32 c.pHeap c.max_vars (u32FullBytes c.max_vars)
    (u32FullBytes c.max_vars + rest) hub (by omega) hm
  rw [← MemShrinkCfg.pPos_eq] at hm
  obtain ⟨ps, hps, hm⟩ := m7_peel_res_u32 c.pPos c.max_vars (u32FullBytes c.max_vars)
    rest hub (by omega) hm
  rw [← MemShrinkCfg.pMinClr_eq] at hm
  have hm' : (region c.pMinClr rest ⋆ (m7SegU32A c fl lv rs tr tp tm hp ps ⋆ R)) m :=
    sep_mono_r (fun _ h => m7_pack8 (by unfold m7SegU32A; rfl) h) hm
  exact ⟨fl, lv, rs, tr, tp, tm, hp, ps, hfl, hlv, hrs, htr, htp, htm, hhp, hps, sep_ac hm'⟩

private theorem m7_peel_segU32B (c : MemShrinkCfg) (rest : Nat)
    (hfit : 7 * u32FullBytes c.max_vars + rest ≤ 2 ^ 64) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region c.pMinClr (7 * u32FullBytes c.max_vars + rest) ⋆ R) m) :
    ∃ mc ss qp qn qs ft fd : List (BitVec 32),
      mc.length = c.max_vars ∧ ss.length = c.max_vars ∧ qp.length = c.max_vars ∧
      qn.length = c.max_vars ∧ qs.length = c.max_vars ∧
      ft.length = c.max_vars + 1 ∧ fd.length = c.max_vars + 1 ∧
      (m7SegU32B c mc ss qp qn qs ft fd ⋆ region c.pWvec rest ⋆ R) m := by
  have hub : 4 * c.max_vars ≤ u32FullBytes c.max_vars := by unfold u32FullBytes; omega
  have hub1 : 4 * (c.max_vars + 1) ≤ u32FullBytes c.max_vars := by unfold u32FullBytes; omega
  rw [show 7 * u32FullBytes c.max_vars + rest =
      u32FullBytes c.max_vars + (6 * u32FullBytes c.max_vars + rest) by omega] at hm
  obtain ⟨mc, hmc, hm⟩ := m7_peel_res_u32 c.pMinClr c.max_vars (u32FullBytes c.max_vars)
    (6 * u32FullBytes c.max_vars + rest) hub (by omega) hm
  rw [← MemShrinkCfg.pShrinkStk_eq, show 6 * u32FullBytes c.max_vars + rest =
      u32FullBytes c.max_vars + (5 * u32FullBytes c.max_vars + rest) by omega] at hm
  obtain ⟨ss, hss, hm⟩ := m7_peel_res_u32 c.pShrinkStk c.max_vars (u32FullBytes c.max_vars)
    (5 * u32FullBytes c.max_vars + rest) hub (by omega) hm
  rw [← MemShrinkCfg.pQPrev_eq, show 5 * u32FullBytes c.max_vars + rest =
      u32FullBytes c.max_vars + (4 * u32FullBytes c.max_vars + rest) by omega] at hm
  obtain ⟨qp, hqp, hm⟩ := m7_peel_res_u32 c.pQPrev c.max_vars (u32FullBytes c.max_vars)
    (4 * u32FullBytes c.max_vars + rest) hub (by omega) hm
  rw [← MemShrinkCfg.pQNext_eq, show 4 * u32FullBytes c.max_vars + rest =
      u32FullBytes c.max_vars + (3 * u32FullBytes c.max_vars + rest) by omega] at hm
  obtain ⟨qn, hqn, hm⟩ := m7_peel_res_u32 c.pQNext c.max_vars (u32FullBytes c.max_vars)
    (3 * u32FullBytes c.max_vars + rest) hub (by omega) hm
  rw [← MemShrinkCfg.pQStamp_eq, show 3 * u32FullBytes c.max_vars + rest =
      u32FullBytes c.max_vars + (2 * u32FullBytes c.max_vars + rest) by omega] at hm
  obtain ⟨qs, hqs, hm⟩ := m7_peel_res_u32 c.pQStamp c.max_vars (u32FullBytes c.max_vars)
    (2 * u32FullBytes c.max_vars + rest) hub (by omega) hm
  rw [← MemShrinkCfg.pFrameTrail_eq, show 2 * u32FullBytes c.max_vars + rest =
      u32FullBytes c.max_vars + (u32FullBytes c.max_vars + rest) by omega] at hm
  obtain ⟨ft, hft, hm⟩ := m7_peel_res_u32 c.pFrameTrail (c.max_vars + 1) (u32FullBytes c.max_vars)
    (u32FullBytes c.max_vars + rest) hub1 (by omega) hm
  rw [← MemShrinkCfg.pFrameDec_eq] at hm
  obtain ⟨fd, hfd, hm⟩ := m7_peel_res_u32 c.pFrameDec (c.max_vars + 1) (u32FullBytes c.max_vars)
    rest hub1 (by omega) hm
  rw [← MemShrinkCfg.pWvec_eq] at hm
  have hm' : (region c.pWvec rest ⋆ (m7SegU32B c mc ss qp qn qs ft fd ⋆ R)) m :=
    sep_mono_r (fun _ h => m7_pack7 (by unfold m7SegU32B; rfl) h) hm
  exact ⟨mc, ss, qp, qn, qs, ft, fd, hmc, hss, hqp, hqn, hqs, hft, hfd, sep_ac hm'⟩

private theorem m7_peel_segTailA (c : MemShrinkCfg) (rest : Nat)
    (hfit : 24 * c.max_vars + 8 * c.minDepth + 320 + rest ≤ 2 ^ 64)
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region c.pWvec (24 * c.max_vars + 8 * c.minDepth + 320 + rest) ⋆ R) m) :
    ∃ wv ms gu ll : List (BitVec 32), ∃ sc : List (BitVec 64),
      wv.length = 4 * c.max_vars ∧ sc.length = c.max_vars ∧ ms.length = 2 * c.minDepth ∧
      gu.length = 64 ∧ ll.length = 16 ∧
      (m7SegTailA c wv ms gu ll sc ⋆ region c.pArena rest ⋆ R) m := by
  rw [show 24 * c.max_vars + 8 * c.minDepth + 320 + rest =
      4 * (4 * c.max_vars) + (8 * c.max_vars + 8 * c.minDepth + 320 + rest) by omega] at hm
  obtain ⟨wv, hwv, hm⟩ := m7_peel_arr32 c.pWvec (4 * c.max_vars)
    (8 * c.max_vars + 8 * c.minDepth + 320 + rest) (by omega) hm
  rw [show 4 * (4 * c.max_vars) = 16 * c.max_vars by omega, ← MemShrinkCfg.pScore_eq,
    show 8 * c.max_vars + 8 * c.minDepth + 320 + rest =
      8 * c.max_vars + (8 * c.minDepth + 320 + rest) by omega] at hm
  obtain ⟨sc, hsc, hm⟩ := m7_peel_arr64 c.pScore c.max_vars
    (8 * c.minDepth + 320 + rest) (by omega) hm
  rw [← MemShrinkCfg.pMinStk_eq, show 8 * c.minDepth + 320 + rest =
      4 * (2 * c.minDepth) + (320 + rest) by omega] at hm
  obtain ⟨ms, hms, hm⟩ := m7_peel_arr32 c.pMinStk (2 * c.minDepth)
    (320 + rest) (by omega) hm
  rw [show 4 * (2 * c.minDepth) = 8 * c.minDepth by omega, ← MemShrinkCfg.pGlueUsed_eq,
    show 320 + rest = 4 * 64 + (64 + rest) by omega] at hm
  obtain ⟨gu, hgu, hm⟩ := m7_peel_arr32 c.pGlueUsed 64 (64 + rest) (by omega) hm
  rw [show (4 * 64 : Nat) = 256 by decide, ← MemShrinkCfg.pLastLearned_eq,
    show 64 + rest = 4 * 16 + rest by omega] at hm
  obtain ⟨ll, hll, hm⟩ := m7_peel_arr32 c.pLastLearned 16 rest (by omega) hm
  rw [show (4 * 16 : Nat) = 64 by decide, ← MemShrinkCfg.pArena_eq] at hm
  have hm' : (region c.pArena rest ⋆ (m7SegTailA c wv ms gu ll sc ⋆ R)) m :=
    sep_mono_r (fun _ h => m7_pack5 (by unfold m7SegTailA; rfl) h) hm
  exact ⟨wv, ms, gu, ll, sc, hwv, hsc, hms, hgu, hll, sep_ac hm'⟩

private theorem m7_peel_segTailB (c : MemShrinkCfg) (rest : Nat)
    (hfit : 4 * c.arena_cap + 4 * c.wcap + 12 * c.delayed_cap + 4 * c.red_cap +
      4 * c.extend_cap + 4 * c.scratch_cap + rest ≤ 2 ^ 64)
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region c.pArena (4 * c.arena_cap + 4 * c.wcap + 12 * c.delayed_cap +
      4 * c.red_cap + 4 * c.extend_cap + 4 * c.scratch_cap + rest) ⋆ R) m) :
    ∃ ar wk dl rr ex sb : List (BitVec 32),
      ar.length = c.arena_cap ∧ wk.length = c.wcap ∧ dl.length = 3 * c.delayed_cap ∧
      rr.length = c.red_cap ∧ ex.length = c.extend_cap ∧ sb.length = c.scratch_cap ∧
      (m7SegTailB c ar wk dl rr ex sb ⋆ region c.pTrans rest ⋆ R) m := by
  rw [show 4 * c.arena_cap + 4 * c.wcap + 12 * c.delayed_cap + 4 * c.red_cap +
      4 * c.extend_cap + 4 * c.scratch_cap + rest =
      4 * c.arena_cap + (4 * c.wcap + 12 * c.delayed_cap + 4 * c.red_cap +
      4 * c.extend_cap + 4 * c.scratch_cap + rest) by omega] at hm
  obtain ⟨ar, har, hm⟩ := m7_peel_arr32 c.pArena c.arena_cap
    (4 * c.wcap + 12 * c.delayed_cap + 4 * c.red_cap + 4 * c.extend_cap +
      4 * c.scratch_cap + rest) (by omega) hm
  rw [← MemShrinkCfg.pWstk_eq, show 4 * c.wcap + 12 * c.delayed_cap + 4 * c.red_cap +
      4 * c.extend_cap + 4 * c.scratch_cap + rest = 4 * c.wcap + (12 * c.delayed_cap +
      4 * c.red_cap + 4 * c.extend_cap + 4 * c.scratch_cap + rest) by omega] at hm
  obtain ⟨wk, hwk, hm⟩ := m7_peel_arr32 c.pWstk c.wcap
    (12 * c.delayed_cap + 4 * c.red_cap + 4 * c.extend_cap + 4 * c.scratch_cap + rest)
    (by omega) hm
  rw [← MemShrinkCfg.pDelayed_eq, show 12 * c.delayed_cap + 4 * c.red_cap + 4 * c.extend_cap +
      4 * c.scratch_cap + rest = 4 * (3 * c.delayed_cap) + (4 * c.red_cap + 4 * c.extend_cap +
      4 * c.scratch_cap + rest) by omega] at hm
  obtain ⟨dl, hdl, hm⟩ := m7_peel_arr32 c.pDelayed (3 * c.delayed_cap)
    (4 * c.red_cap + 4 * c.extend_cap + 4 * c.scratch_cap + rest) (by omega) hm
  rw [show 4 * (3 * c.delayed_cap) = 12 * c.delayed_cap by omega, ← MemShrinkCfg.pRedRefs_eq,
    show 4 * c.red_cap + 4 * c.extend_cap + 4 * c.scratch_cap + rest =
      4 * c.red_cap + (4 * c.extend_cap + 4 * c.scratch_cap + rest) by omega] at hm
  obtain ⟨rr, hrr, hm⟩ := m7_peel_arr32 c.pRedRefs c.red_cap
    (4 * c.extend_cap + 4 * c.scratch_cap + rest) (by omega) hm
  rw [← MemShrinkCfg.pExtendStk_eq, show 4 * c.extend_cap + 4 * c.scratch_cap + rest =
      4 * c.extend_cap + (4 * c.scratch_cap + rest) by omega] at hm
  obtain ⟨ex, hex, hm⟩ := m7_peel_arr32 c.pExtendStk c.extend_cap
    (4 * c.scratch_cap + rest) (by omega) hm
  rw [← MemShrinkCfg.pScratchBuf_eq] at hm
  obtain ⟨sb, hsb, hm⟩ := m7_peel_arr32 c.pScratchBuf c.scratch_cap rest (by omega) hm
  rw [← MemShrinkCfg.pTrans_eq] at hm
  have hm' : (region c.pTrans rest ⋆ (m7SegTailB c ar wk dl rr ex sb ⋆ R)) m :=
    sep_mono_r (fun _ h => m7_pack6 (by unfold m7SegTailB; rfl) h) hm
  exact ⟨ar, wk, dl, rr, ex, sb, har, hwk, hdl, hrr, hex, hsb, sep_ac hm'⟩

private theorem m7_peel_segTrans (c : MemShrinkCfg)
    (hfit : m7TransBytes c.max_vars + c.slack ≤ 2 ^ 64) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (region c.pTrans (m7TransBytes c.max_vars + c.slack) ⋆ R) m) :
    ∃ lit_mark : List (BitVec 8), lit_mark.length = 2 * c.max_vars ∧
      ((array (t := i8) c.pLitMark lit_mark ⋆
        region (c.pLitMark + BitVec.ofNat 64 (2 * c.max_vars))
          (valsBytes c.max_vars - 2 * c.max_vars)) ⋆
        MemShrinkTransRegions c ⋆ region c.pSlack c.slack ⋆ R) m := by
  have hvb : 2 * c.max_vars ≤ valsBytes c.max_vars := by unfold valsBytes; omega
  rw [m7TransBytes_def] at hfit hm
  rw [show 56 * c.max_vars + valsBytes c.max_vars + c.slack =
      8 * c.max_vars + (8 * c.max_vars + (8 * c.max_vars + (8 * c.max_vars +
      (8 * c.max_vars + (8 * c.max_vars + (8 * c.max_vars +
      (valsBytes c.max_vars + c.slack))))))) by omega] at hm
  have h1 := m7_peel_reg c.pTrans (8 * c.max_vars)
    (8 * c.max_vars + (8 * c.max_vars + (8 * c.max_vars + (8 * c.max_vars +
      (8 * c.max_vars + (8 * c.max_vars + (valsBytes c.max_vars + c.slack)))))))
    (by omega) hm
  rw [← MemShrinkCfg.pWorkStk1_eq] at h1
  have h2 := m7_peel_reg c.pWorkStk1 (8 * c.max_vars)
    (8 * c.max_vars + (8 * c.max_vars + (8 * c.max_vars + (8 * c.max_vars +
      (8 * c.max_vars + (valsBytes c.max_vars + c.slack)))))) (by omega) h1
  rw [← MemShrinkCfg.pWorkStk2_eq] at h2
  have h3 := m7_peel_reg c.pWorkStk2 (8 * c.max_vars)
    (8 * c.max_vars + (8 * c.max_vars + (8 * c.max_vars + (8 * c.max_vars +
      (valsBytes c.max_vars + c.slack))))) (by omega) h2
  rw [← MemShrinkCfg.pTarjanMark_eq] at h3
  have h4 := m7_peel_reg c.pTarjanMark (8 * c.max_vars)
    (8 * c.max_vars + (8 * c.max_vars + (8 * c.max_vars +
      (valsBytes c.max_vars + c.slack)))) (by omega) h3
  rw [← MemShrinkCfg.pTarjanReach_eq] at h4
  have h5 := m7_peel_reg c.pTarjanReach (8 * c.max_vars)
    (8 * c.max_vars + (8 * c.max_vars + (valsBytes c.max_vars + c.slack))) (by omega) h4
  rw [← MemShrinkCfg.pRepr_eq] at h5
  have h6 := m7_peel_reg c.pRepr (8 * c.max_vars)
    (8 * c.max_vars + (valsBytes c.max_vars + c.slack)) (by omega) h5
  rw [← MemShrinkCfg.pSimSig_eq] at h6
  have h7 := m7_peel_reg c.pSimSig (8 * c.max_vars)
    (valsBytes c.max_vars + c.slack) (by omega) h6
  rw [← MemShrinkCfg.pLitMark_eq] at h7
  obtain ⟨lm, hlm, h8⟩ := m7_peel_res_i8 c.pLitMark (2 * c.max_vars) (valsBytes c.max_vars)
    c.slack hvb (by omega) h7
  rw [← MemShrinkCfg.pSlack_eq] at h8
  have h8a : (region c.pSlack c.slack ⋆
      ((array (t := i8) c.pLitMark lm ⋆
        region (c.pLitMark + BitVec.ofNat 64 (2 * c.max_vars))
          (valsBytes c.max_vars - 2 * c.max_vars)) ⋆
      (MemShrinkTransRegions c ⋆ R))) m := by
    refine sep_mono_r (fun _ h1 => ?_) h8
    refine sep_mono_r (fun _ h2 => ?_) h1
    exact m7_pack7 (by rw [MemShrinkTransRegions_eq, MemShrinkCfg.pWsort_eq]) h2
  exact ⟨lm, hlm, sep_ac h8a⟩

private def m7R5 (c : MemShrinkCfg) : Nat := m7TransBytes c.max_vars + c.slack
private def m7R4 (c : MemShrinkCfg) : Nat :=
  4 * c.arena_cap + 4 * c.wcap + 12 * c.delayed_cap + 4 * c.red_cap +
  4 * c.extend_cap + 4 * c.scratch_cap + m7R5 c
private def m7R3 (c : MemShrinkCfg) : Nat := 24 * c.max_vars + 8 * c.minDepth + 320 + m7R4 c
private def m7R2 (c : MemShrinkCfg) : Nat := 7 * u32FullBytes c.max_vars + m7R3 c
private def m7R1 (c : MemShrinkCfg) : Nat := 8 * u32FullBytes c.max_vars + m7R2 c

private theorem m7_arrs_pack_res (c : MemShrinkCfg) (d_cur d_val fuel : BitVec 64)
    (a : M7InitArrs c) {R : Mem 64 → Prop} {m : Mem 64}
    (hm : ((array (t := i8) c.pLitMark a.lit_mark ⋆
        region (c.pLitMark + BitVec.ofNat 64 (2 * c.max_vars))
          (valsBytes c.max_vars - 2 * c.max_vars)) ⋆
        MemShrinkTransRegions c ⋆ region c.pSlack c.slack ⋆
        (m7SegTailB c a.arena a.wstk a.delayed a.red_refs a.extend_stk a.scratch_buf ⋆
        m7SegTailA c a.wvec a.min_stk a.glue_used a.last_learned a.score ⋆
        m7SegU32B c a.min_clr a.shrink_stk a.q_prev a.q_next a.q_stamp a.frame_trail
          a.frame_dec ⋆
        m7SegU32A c a.flags a.lvl a.rsns a.trl a.trail_pos a.tmp a.heap a.pos ⋆
        m7SegBytes c a.vals a.mrk a.phases a.phases_target a.phases_best ⋆ R)) m) :
    (MemShrinkResArrays c (m7InitState c d_cur d_val fuel a) ⋆
      MemShrinkLitMark c (m7InitState c d_cur d_val fuel a) ⋆
      MemShrinkTransRegions c ⋆ region c.pSlack c.slack ⋆ R) m := by
  have hB : m7SegBytes c a.vals a.mrk a.phases a.phases_target a.phases_best =
      MemShrinkResBytes c (m7InitState c d_cur d_val fuel a) := by
    rw [MemShrinkResBytes_eq]; dsimp only [m7InitState]; unfold m7SegBytes; rfl
  have hUA : m7SegU32A c a.flags a.lvl a.rsns a.trl a.trail_pos a.tmp a.heap a.pos =
      MemShrinkResU32A c (m7InitState c d_cur d_val fuel a) := by
    rw [MemShrinkResU32A_eq]; dsimp only [m7InitState]; unfold m7SegU32A; rfl
  have hUB : m7SegU32B c a.min_clr a.shrink_stk a.q_prev a.q_next a.q_stamp a.frame_trail
      a.frame_dec = MemShrinkResU32B c (m7InitState c d_cur d_val fuel a) := by
    rw [MemShrinkResU32B_eq]; dsimp only [m7InitState]; unfold m7SegU32B; rfl
  have hTl : (m7SegTailA c a.wvec a.min_stk a.glue_used a.last_learned a.score ⋆
      m7SegTailB c a.arena a.wstk a.delayed a.red_refs a.extend_stk a.scratch_buf) =
      MemShrinkResTail c (m7InitState c d_cur d_val fuel a) := by
    rw [MemShrinkResTail_eq]; dsimp only [m7InitState]
    unfold m7SegTailA m7SegTailB; ac_rfl
  have hLM : (array (t := i8) c.pLitMark a.lit_mark ⋆
      region (c.pLitMark + BitVec.ofNat 64 (2 * c.max_vars))
        (valsBytes c.max_vars - 2 * c.max_vars)) =
      MemShrinkLitMark c (m7InitState c d_cur d_val fuel a) := by
    rw [MemShrinkLitMark_eq]; dsimp only [m7InitState]
  rw [hLM, hB, hUA, hUB] at hm
  have hm' : ((m7SegTailA c a.wvec a.min_stk a.glue_used a.last_learned a.score ⋆
      m7SegTailB c a.arena a.wstk a.delayed a.red_refs a.extend_stk a.scratch_buf) ⋆
      MemShrinkResBytes c (m7InitState c d_cur d_val fuel a) ⋆
      MemShrinkResU32A c (m7InitState c d_cur d_val fuel a) ⋆
      MemShrinkResU32B c (m7InitState c d_cur d_val fuel a) ⋆
      MemShrinkLitMark c (m7InitState c d_cur d_val fuel a) ⋆
      MemShrinkTransRegions c ⋆ region c.pSlack c.slack ⋆ R) m := sep_ac hm
  rw [hTl] at hm'
  rw [MemShrinkResArrays_eq]
  exact sep_ac hm'

private theorem m7_avail_fit (c : MemShrinkCfg) :
    valsBytes c.max_vars + 4 * markBytes c.max_vars + m7R1 c ≤ 2 ^ 64 := by
  have hav_fit : c.avail < 2 ^ 64 := by have := c.havail_fit; omega
  have hsz := c.hsize
  unfold m7R1 m7R2 m7R3 m7R4 m7R5
  rw [MemShrinkCfg.slack_eq, MemShrinkCfg.minDepth_eq, m7FixedBytes_def, m7TransBytes_def]
  rw [m7FixedBytes_def, m7TransBytes_def] at hsz
  omega

private theorem m7_avail_len (c : MemShrinkCfg) (h1152 : 1152 ≤ c.avail) :
    c.avail - 1152 = valsBytes c.max_vars + 4 * markBytes c.max_vars + m7R1 c := by
  have hsz := c.hsize
  unfold m7R1 m7R2 m7R3 m7R4 m7R5
  rw [MemShrinkCfg.slack_eq, MemShrinkCfg.minDepth_eq, m7FixedBytes_def, m7TransBytes_def]
  rw [m7FixedBytes_def, m7TransBytes_def] at hsz
  omega

private theorem m7_peel_front (c : MemShrinkCfg) {R : Mem 64 → Prop} {m : Mem 64} {P : Prop}
    (hm : (region c.pVals (valsBytes c.max_vars + 4 * markBytes c.max_vars + m7R1 c) ⋆ R) m)
    (k : ∀ (vals mrk ph pht phb : List (BitVec 8))
      (fl lv rs tr tp tm mc hp ps ss qp qn qs ft fd : List (BitVec 32)),
      vals.length = 2 * c.max_vars → mrk.length = c.max_vars → ph.length = c.max_vars →
      pht.length = c.max_vars → phb.length = c.max_vars → fl.length = c.max_vars →
      lv.length = c.max_vars → rs.length = c.max_vars → tr.length = c.max_vars →
      tp.length = c.max_vars → tm.length = c.max_vars → mc.length = c.max_vars →
      hp.length = c.max_vars → ps.length = c.max_vars → ss.length = c.max_vars →
      qp.length = c.max_vars → qn.length = c.max_vars → qs.length = c.max_vars →
      ft.length = c.max_vars + 1 → fd.length = c.max_vars + 1 →
      (region c.pWvec (m7R3 c) ⋆
        (m7SegU32B c mc ss qp qn qs ft fd ⋆ m7SegU32A c fl lv rs tr tp tm hp ps ⋆
        m7SegBytes c vals mrk ph pht phb ⋆ R)) m → P) : P := by
  have hfit := m7_avail_fit c
  obtain ⟨vals, mrk, ph, pht, phb, hv, hmk, hph, hpht, hphb, hm⟩ :=
    m7_peel_segBytes c (m7R1 c) hfit hm
  have hm : (region c.pFlags (m7R1 c) ⋆ (m7SegBytes c vals mrk ph pht phb ⋆ R)) m := sep_ac hm
  rw [m7R1] at hm
  have h1 : 8 * u32FullBytes c.max_vars + m7R2 c ≤ m7R1 c := by unfold m7R1; omega
  obtain ⟨fl, lv, rs, tr, tp, tm, hp, ps, hfl, hlv, hrs, htr, htp, htm, hhp, hps, hm⟩ :=
    m7_peel_segU32A c (m7R2 c) (by omega) hm
  have hm : (region c.pMinClr (m7R2 c) ⋆ (m7SegU32A c fl lv rs tr tp tm hp ps ⋆
      m7SegBytes c vals mrk ph pht phb ⋆ R)) m := sep_ac hm
  rw [m7R2] at hm
  have h2 : 7 * u32FullBytes c.max_vars + m7R3 c ≤ m7R2 c := by unfold m7R2; omega
  obtain ⟨mc, ss, qp, qn, qs, ft, fd, hmc, hss, hqp, hqn, hqs, hft, hfd, hm⟩ :=
    m7_peel_segU32B c (m7R3 c) (by omega) hm
  have hm : (region c.pWvec (m7R3 c) ⋆ (m7SegU32B c mc ss qp qn qs ft fd ⋆
      m7SegU32A c fl lv rs tr tp tm hp ps ⋆ m7SegBytes c vals mrk ph pht phb ⋆ R)) m := sep_ac hm
  exact k vals mrk ph pht phb fl lv rs tr tp tm mc hp ps ss qp qn qs ft fd
    hv hmk hph hpht hphb hfl hlv hrs htr htp htm hmc hhp hps hss hqp hqn hqs hft hfd hm

private theorem m7_peel_back (c : MemShrinkCfg) {R : Mem 64 → Prop} {m : Mem 64} {P : Prop}
    (hfit3 : m7R3 c ≤ 2 ^ 64) (hm : (region c.pWvec (m7R3 c) ⋆ R) m)
    (k : ∀ (lm : List (BitVec 8)) (wv ms gu ll ar wk dl rr ex sb : List (BitVec 32))
      (sc : List (BitVec 64)),
      lm.length = 2 * c.max_vars → wv.length = 4 * c.max_vars → ms.length = 2 * c.minDepth →
      gu.length = 64 → ll.length = 16 → ar.length = c.arena_cap → wk.length = c.wcap →
      dl.length = 3 * c.delayed_cap → rr.length = c.red_cap → ex.length = c.extend_cap →
      sb.length = c.scratch_cap → sc.length = c.max_vars →
      ((array (t := i8) c.pLitMark lm ⋆
        region (c.pLitMark + BitVec.ofNat 64 (2 * c.max_vars))
          (valsBytes c.max_vars - 2 * c.max_vars)) ⋆
        MemShrinkTransRegions c ⋆ region c.pSlack c.slack ⋆
        (m7SegTailB c ar wk dl rr ex sb ⋆ m7SegTailA c wv ms gu ll sc ⋆ R)) m → P) : P := by
  rw [m7R3] at hm
  have h3 : 24 * c.max_vars + 8 * c.minDepth + 320 + m7R4 c ≤ m7R3 c := by unfold m7R3; omega
  obtain ⟨wv, ms, gu, ll, sc, hwv, hsc, hms, hgu, hll, hm⟩ :=
    m7_peel_segTailA c (m7R4 c) (by omega) hm
  have hm : (region c.pArena (m7R4 c) ⋆ (m7SegTailA c wv ms gu ll sc ⋆ R)) m := sep_ac hm
  rw [m7R4] at hm
  have h4 : 4 * c.arena_cap + 4 * c.wcap + 12 * c.delayed_cap + 4 * c.red_cap +
      4 * c.extend_cap + 4 * c.scratch_cap + m7R5 c ≤ m7R4 c := by unfold m7R4; omega
  obtain ⟨ar, wk, dl, rr, ex, sb, har, hwk, hdl, hrr, hex, hsb, hm⟩ :=
    m7_peel_segTailB c (m7R5 c) (by omega) hm
  have hm : (region c.pTrans (m7R5 c) ⋆
      (m7SegTailB c ar wk dl rr ex sb ⋆ m7SegTailA c wv ms gu ll sc ⋆ R)) m := sep_ac hm
  rw [m7R5] at hm
  have h5 : m7TransBytes c.max_vars + c.slack ≤ m7R5 c := by unfold m7R5; omega
  obtain ⟨lm, hlm, hm⟩ := m7_peel_segTrans c (by omega) hm
  exact k lm wv ms gu ll ar wk dl rr ex sb sc
    hlm hwv hms hgu hll har hwk hdl hrr hex hsb hsc hm

private theorem m7_region_to_mem (c : MemShrinkCfg) (d_cur d_val fuel : BitVec 64)
    {R : Mem 64 → Prop} {m : Mem 64} (h1152 : 1152 ≤ c.avail)
    (hm : (region (c.hdr + 1152) (c.avail - 1152) ⋆ R) m) :
    ∃ a : M7InitArrs c,
      (MemShrinkResArrays c (m7InitState c d_cur d_val fuel a) ⋆
        MemShrinkLitMark c (m7InitState c d_cur d_val fuel a) ⋆
        MemShrinkTransRegions c ⋆ region c.pSlack c.slack ⋆ R) m := by
  have hfit3 : m7R3 c ≤ 2 ^ 64 := by
    have := m7_avail_fit c; unfold m7R1 m7R2 at this; omega
  rw [m7_avail_len c h1152,
    show c.hdr + 1152 = c.pVals by rw [MemShrinkCfg.pVals_eq]; rfl] at hm
  refine m7_peel_front c hm fun vals mrk ph pht phb fl lv rs tr tp tm mc hp ps ss qp qn qs
      ft fd hv hmk hph hpht hphb hfl hlv hrs htr htp htm hmc hhp hps hss hqp hqn hqs hft hfd hm1 =>
    m7_peel_back c hfit3 hm1 fun lm wv ms gu ll ar wk dl rr ex sb sc hlm hwv hms hgu hll har hwk
        hdl hrr hex hsb hsc hm2 => ?_
  let a : M7InitArrs c :=
    ⟨vals, mrk, lm, ph, pht, phb, fl, lv, rs, tr, tp, tm, mc, hp, ps, ss, qp, qn, qs, ft, fd,
      wv, ms, gu, ll, ar, wk, dl, rr, ex, sb, sc, hv, hmk, hlm, hph, hpht, hphb, hfl, hlv, hrs,
      htr, htp, htm, hmc, hhp, hps, hss, hqp, hqn, hqs, hft, hfd, hwv, hms, hgu, hll, har, hwk, hdl,
      hrr, hex, hsb, hsc⟩
  refine ⟨a, @m7_arrs_pack_res c d_cur d_val fuel a R m ?_⟩
  dsimp only [a]; exact sep_ac hm2

private theorem m7_forall_lt_succ {n : Nat} {P : Nat → Prop}
    (h0 : P n) (hs : ∀ i < n, P i) : ∀ i < n + 1, P i := fun i hi =>
  if h : i = n then h ▸ h0 else hs i (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hi) h)

private theorem m7_list_eq_35 {a b : List (BitVec 64)} (ha : a.length = 35) (hb : b.length = 35)
    (h : ∀ i < 35, a[i]? = b[i]?) : a = b := by
  apply List.ext_getElem?; intro i
  by_cases hi : i < 35
  · exact h i hi
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

private theorem m7_bv_ofNat_mul (k n : Nat) :
    BitVec.ofNat 64 k * BitVec.ofNat 64 n = BitVec.ofNat 64 (k * n) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, Nat.mul_mod]

private theorem m7_hdrTail0_eq (c : MemShrinkCfg) (avail_dyn : Nat)
    (har_c : c.arena_cap = 2 * fullInitAp avail_dyn)
    (hwk_c : c.wcap = 2 * fullInitWp avail_dyn)
    (d_cur d_val fuel : BitVec 64) (a : M7InitArrs c)
    {w0 : List (BitVec 64)} (hw0l : w0.length = 35)
    (hAr : c.hdr + BitVec.ofNat 64 (m7FixedBytes c.max_vars) = c.pArena)
    (hWs : c.pArena + BitVec.ofNat 64 (8 * fullInitAp avail_dyn) = c.pWstk) :
    m7HdrW0 c.mv fuel (m7ArenasW0 c.hdr c.max_vars avail_dyn w0) =
      m7HdrTailWords0 c (m7InitState c d_cur d_val fuel a) := by
  have hp10 : (m7PtrsW0 c.hdr c.max_vars w0)[10]! = c.pArena := by
    rw [getElem!_pos (c := m7PtrsW0 c.hdr c.max_vars w0) (i := 10)
        (by simp [m7PtrsW0_eq, List.length_set, hw0l]), ← hAr]
    exact Option.some.inj
      ((List.getElem?_eq_getElem (by simp [m7PtrsW0_eq, List.length_set, hw0l])).symm.trans
        (m7PtrsW0_10 c.hdr c.max_vars hw0l))
  have hDl : c.pWstk + BitVec.ofNat 64 (8 * fullInitWp avail_dyn) = c.pDelayed := by
    rw [MemShrinkCfg.pDelayed_eq, hwk_c]; congr 2; omega
  rw [m7HdrW0_eq, m7ArenasW0_eq, hp10, m7PtrsW0_eq, m7HdrTailWords0_eq]
  dsimp only [m7InitState]
  rw [har_c, hwk_c, hWs, hDl, ← MemShrinkCfg.pVals_eq, ← MemShrinkCfg.pMark_eq,
    ← MemShrinkCfg.pPhases_eq, ← MemShrinkCfg.pPhasesTarget_eq, ← MemShrinkCfg.pPhasesBest_eq,
    ← MemShrinkCfg.pFlags_eq, ← MemShrinkCfg.pLevel_eq, ← MemShrinkCfg.pReason_eq,
    ← MemShrinkCfg.pTrail_eq, ← MemShrinkCfg.pTrailPos_eq, ← MemShrinkCfg.pTmp_eq,
    ← MemShrinkCfg.pHeap_eq, ← MemShrinkCfg.pPos_eq, ← MemShrinkCfg.pMinClr_eq,
    ← MemShrinkCfg.pShrinkStk_eq, ← MemShrinkCfg.pQPrev_eq, ← MemShrinkCfg.pQNext_eq,
    ← MemShrinkCfg.pQStamp_eq, ← MemShrinkCfg.pFrameTrail_eq, ← MemShrinkCfg.pFrameDec_eq,
    ← MemShrinkCfg.pWvec_eq, ← MemShrinkCfg.pScore_eq, ← MemShrinkCfg.minDepth_eq,
    ← MemShrinkCfg.pMinStk_eq, ← MemShrinkCfg.pGlueUsed_eq, ← MemShrinkCfg.pLastLearned_eq,
    ← MemShrinkCfg.pArena_eq]
  apply m7_list_eq_35 (by simp [List.length_set, hw0l]) (by simp)
  iterate 35
    (apply m7_forall_lt_succ
     · simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_set,
         List.length_set, hw0l, Nat.reduceEqDiff, Nat.reduceLT, ↓reduceIte] <;> rfl)
  intro i hi; omega

private theorem m7_hdrTail1_eq (c : MemShrinkCfg) (avail_dyn : Nat)
    (hrr_c : c.red_cap = 2 * fullInitRp avail_dyn)
    (d_cur d_val fuel : BitVec 64) (a : M7InitArrs c)
    {w1 : List (BitVec 64)} (hw1l : w1.length = 35)
    (hAr : c.hdr + BitVec.ofNat 64 (m7FixedBytes c.max_vars) = c.pArena)
    (hRr : c.pArena + BitVec.ofNat 64 (8 * fullInitAp avail_dyn + 8 * fullInitWp avail_dyn) +
      BitVec.ofNat 64 (12 * c.delayed_cap) = c.pRedRefs)
    (hTr1 : c.pRedRefs + BitVec.ofNat 64 (8 * fullInitRp avail_dyn + 4 * c.extend_cap +
      4 * c.scratch_cap) = c.pTrans) :
    m7HdrW1 (m7ArenasW1 c.hdr c.max_vars avail_dyn c.delayed_cap c.extend_cap c.scratch_cap
      (w1.set 17 (BitVec.ofNat 64 c.delayed_cap))) =
      m7HdrTailWords1 c (m7InitState c d_cur d_val fuel a) := by
  rw [m7HdrW1_eq, m7ArenasW1_eq, m7PtrsW1_eq, m7HdrTailWords1_eq]
  dsimp only [m7InitState]
  simp only [m7_bv_ofNat_mul, hAr, hRr, hTr1, hrr_c, MemShrinkCfg.pWsort_eq,
    MemShrinkCfg.pGlueUsed_eq, MemShrinkCfg.pMinStk_eq, MemShrinkCfg.pScore_eq,
    MemShrinkCfg.pWvec_eq, MemShrinkCfg.pFrameDec_eq, MemShrinkCfg.pFrameTrail_eq,
    MemShrinkCfg.pQStamp_eq, MemShrinkCfg.pQNext_eq, MemShrinkCfg.pQPrev_eq,
    MemShrinkCfg.pShrinkStk_eq, MemShrinkCfg.pMinClr_eq, MemShrinkCfg.pPos_eq,
    MemShrinkCfg.pHeap_eq, MemShrinkCfg.pTmp_eq, MemShrinkCfg.pTrailPos_eq,
    MemShrinkCfg.pTrail_eq, MemShrinkCfg.pReason_eq, MemShrinkCfg.pLevel_eq,
    MemShrinkCfg.pFlags_eq, MemShrinkCfg.pPhasesBest_eq, MemShrinkCfg.pPhasesTarget_eq,
    MemShrinkCfg.pPhases_eq, MemShrinkCfg.pMark_eq, MemShrinkCfg.pVals_eq,
    MemShrinkCfg.minDepth_eq, BitVec.add_assoc, ← BitVec.ofNat_add]
  apply m7_list_eq_35 (by simp [List.length_set, hw1l]) (by simp)
  iterate 35
    (apply m7_forall_lt_succ
     · simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_set,
         List.length_set, hw1l, Nat.reduceEqDiff, Nat.reduceLT, ↓reduceIte] <;>
       first | rfl | (apply congrArg some; congr 2; omega))
  intro i hi; omega

private theorem m7_hdrTail2_eq (c : MemShrinkCfg) (avail_dyn : Nat)
    (d_cur d_val fuel : BitVec 64) (a : M7InitArrs c)
    {w2 : List (BitVec 64)} (hw2l : w2.length = 35)
    (_hAr : c.hdr + BitVec.ofNat 64 (m7FixedBytes c.max_vars) = c.pArena)
    (hTr2 : c.pArena + BitVec.ofNat 64 (8 * fullInitAp avail_dyn + 8 * fullInitWp avail_dyn +
      12 * c.delayed_cap + 8 * fullInitRp avail_dyn + 4 * c.extend_cap + 4 * c.scratch_cap) =
      c.pTrans) :
    m7HdrW2 c.mv c.max_vars (m7ArenasW2 c.hdr c.max_vars avail_dyn
      c.delayed_cap c.extend_cap c.scratch_cap w2) =
      m7HdrTailWords2 c (m7InitState c d_cur d_val fuel a) := by
  have hpFl : c.hdr + BitVec.ofNat 64 (1152 + valsBytes c.max_vars + 4 * markBytes c.max_vars) =
      c.pFlags := by
    simp only [MemShrinkCfg.pFlags_eq, MemShrinkCfg.pPhasesBest_eq, MemShrinkCfg.pPhasesTarget_eq,
      MemShrinkCfg.pPhases_eq, MemShrinkCfg.pMark_eq, MemShrinkCfg.pVals_eq, BitVec.add_assoc,
      ← BitVec.ofNat_add]; congr 2; omega
  have hpFT : c.pFlags + 13#64 * BitVec.ofNat 64 (u32FullBytes c.max_vars) = c.pFrameTrail := by
    rw [show (13#64 : BitVec 64) = BitVec.ofNat 64 13 from rfl, m7_bv_ofNat_mul]
    simp only [MemShrinkCfg.pFrameTrail_eq, MemShrinkCfg.pQStamp_eq, MemShrinkCfg.pQNext_eq,
      MemShrinkCfg.pQPrev_eq, MemShrinkCfg.pShrinkStk_eq, MemShrinkCfg.pMinClr_eq,
      MemShrinkCfg.pPos_eq, MemShrinkCfg.pHeap_eq, MemShrinkCfg.pTmp_eq, MemShrinkCfg.pTrailPos_eq,
      MemShrinkCfg.pTrail_eq, MemShrinkCfg.pReason_eq, MemShrinkCfg.pLevel_eq, BitVec.add_assoc,
      ← BitVec.ofNat_add]; congr 2; omega
  have hpW1 : c.pTrans + BitVec.ofNat 64 (8 * c.max_vars) = c.pWorkStk1 := by
    rw [MemShrinkCfg.pWorkStk1_eq]
  have hpW2 : c.pTrans + BitVec.ofNat 64 (16 * c.max_vars) = c.pWorkStk2 := by
    simp only [MemShrinkCfg.pWorkStk2_eq, MemShrinkCfg.pWorkStk1_eq, BitVec.add_assoc,
      ← BitVec.ofNat_add]; congr 2; omega
  have hpTM : c.pTrans + BitVec.ofNat 64 (24 * c.max_vars) = c.pTarjanMark := by
    simp only [MemShrinkCfg.pTarjanMark_eq, ← hpW2, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  have hpRp : c.pTrans + BitVec.ofNat 64 (40 * c.max_vars) = c.pRepr := by
    simp only [MemShrinkCfg.pRepr_eq, MemShrinkCfg.pTarjanReach_eq, ← hpTM, BitVec.add_assoc,
      ← BitVec.ofNat_add]; congr 2; omega
  have hpSS : c.pTrans + BitVec.ofNat 64 (48 * c.max_vars) = c.pSimSig := by
    simp only [MemShrinkCfg.pSimSig_eq, ← hpRp, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  have hpLM : c.pTrans + BitVec.ofNat 64 (56 * c.max_vars) = c.pLitMark := by
    simp only [MemShrinkCfg.pLitMark_eq, ← hpSS, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  have hbva : c.max_vars - c.mv = c.bva_cap := by have := c.hbva; omega
  rw [m7HdrW2_eq, m7ArenasW2_eq, m7PtrsW2_eq, m7HdrTailWords2_eq]
  dsimp only [m7InitState]
  rw [_hAr, hTr2, hpFl, hpFT, ← MemShrinkCfg.pFrameDec_eq, hpLM, hpRp, hpSS, hpW1, hpW2, hpTM,
    hbva]
  apply m7_list_eq_35 (by simp [List.length_set, hw2l]) (by simp)
  iterate 35
    (apply m7_forall_lt_succ
     · simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_set,
         List.length_set, hw2l, Nat.reduceEqDiff, Nat.reduceLT, ↓reduceIte] <;> rfl)
  intro i hi; omega

private theorem m7_hdrTail3_eq (c : MemShrinkCfg) (avail_dyn : Nat)
    (d_cur d_val fuel : BitVec 64) (a : M7InitArrs c)
    {w3 : List (BitVec 64)} (hw3l : w3.length = 35)
    (_hAr : c.hdr + BitVec.ofNat 64 (m7FixedBytes c.max_vars) = c.pArena)
    (hEx : c.pArena + BitVec.ofNat 64 (8 * fullInitAp avail_dyn + 8 * fullInitWp avail_dyn +
      12 * c.delayed_cap + 8 * fullInitRp avail_dyn) = c.pExtendStk)
    (hSc : c.pExtendStk + BitVec.ofNat 64 (4 * c.extend_cap) = c.pScratchBuf)
    (hTr3 : c.pScratchBuf + BitVec.ofNat 64 (4 * c.scratch_cap) = c.pTrans) :
    m7HdrW3 c.mv (m7ArenasW3 c.hdr c.max_vars avail_dyn c.delayed_cap
      c.extend_cap c.scratch_cap
      ((w3.set 4 (BitVec.ofNat 64 c.extend_cap)).set 7 (BitVec.ofNat 64 c.scratch_cap))) =
      m7HdrTailWords3 c (m7InitState c d_cur d_val fuel a) := by
  have hpTR : c.pTrans + BitVec.ofNat 64 (32 * c.max_vars) = c.pTarjanReach := by
    simp only [MemShrinkCfg.pTarjanReach_eq, MemShrinkCfg.pTarjanMark_eq, MemShrinkCfg.pWorkStk2_eq,
      MemShrinkCfg.pWorkStk1_eq, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  have hpWV : c.pTrans + BitVec.ofNat 64 (40 * c.max_vars) = c.pWalkVals := by
    simp only [MemShrinkCfg.pWalkVals_eq, MemShrinkCfg.pRepr_eq, ← hpTR, BitVec.add_assoc,
      ← BitVec.ofNat_add]; congr 2; omega
  have hpWB : c.pTrans + BitVec.ofNat 64 (48 * c.max_vars) = c.pWalkBest := by
    simp only [MemShrinkCfg.pWalkBest_eq, MemShrinkCfg.pSimSig_eq, ← MemShrinkCfg.pWalkVals_eq,
      ← hpWV, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  have hpLL : c.hdr + BitVec.ofNat 64 (1152 + valsBytes c.max_vars + 4 * markBytes c.max_vars +
      15 * u32FullBytes c.max_vars + 24 * c.max_vars + 8 * fullMinDepthOf c.max_vars) +
      BitVec.ofNat 64 256 = c.pLastLearned := by
    rw [MemShrinkCfg.pLastLearned_eq]; congr 1
    simp only [MemShrinkCfg.pGlueUsed_eq, MemShrinkCfg.pMinStk_eq, MemShrinkCfg.pScore_eq,
      MemShrinkCfg.pWvec_eq, MemShrinkCfg.pFrameDec_eq, MemShrinkCfg.pFrameTrail_eq,
      MemShrinkCfg.pQStamp_eq, MemShrinkCfg.pQNext_eq, MemShrinkCfg.pQPrev_eq,
      MemShrinkCfg.pShrinkStk_eq, MemShrinkCfg.pMinClr_eq, MemShrinkCfg.pPos_eq,
      MemShrinkCfg.pHeap_eq, MemShrinkCfg.pTmp_eq, MemShrinkCfg.pTrailPos_eq,
      MemShrinkCfg.pTrail_eq, MemShrinkCfg.pReason_eq, MemShrinkCfg.pLevel_eq,
      MemShrinkCfg.pFlags_eq, MemShrinkCfg.pPhasesBest_eq, MemShrinkCfg.pPhasesTarget_eq,
      MemShrinkCfg.pPhases_eq, MemShrinkCfg.pMark_eq, MemShrinkCfg.pVals_eq,
      MemShrinkCfg.minDepth_eq, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  rw [m7HdrW3_eq, m7ArenasW3_eq, m7PtrsW3_eq, m7HdrTailWords3_eq]
  dsimp only [m7InitState]
  rw [_hAr, hEx, hSc, hTr3, hpTR, hpWV, hpWB, hpLL]
  apply m7_list_eq_35 (by simp [List.length_set, hw3l]) (by simp)
  iterate 35
    (apply m7_forall_lt_succ
     · simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_set,
         List.length_set, hw3l, Nat.reduceEqDiff, Nat.reduceLT, ↓reduceIte] <;> rfl)
  intro i hi; omega

private theorem m7_hdrTail_eq (c : MemShrinkCfg) (avail_dyn : Nat)
    (har_c : c.arena_cap = 2 * fullInitAp avail_dyn)
    (hwk_c : c.wcap = 2 * fullInitWp avail_dyn)
    (hrr_c : c.red_cap = 2 * fullInitRp avail_dyn)
    (d_cur d_val fuel : BitVec 64) (a : M7InitArrs c)
    {w0 w1 w2 w3 : List (BitVec 64)}
    (hw0l : w0.length = 35) (hw1l : w1.length = 35)
    (hw2l : w2.length = 35) (hw3l : w3.length = 35) :
    let w1' := w1.set 17 (BitVec.ofNat 64 c.delayed_cap)
    let w3'' := (w3.set 4 (BitVec.ofNat 64 c.extend_cap)).set 7 (BitVec.ofNat 64 c.scratch_cap)
    let s0 := m7InitState c d_cur d_val fuel a
    m7HdrW0 c.mv fuel (m7ArenasW0 c.hdr c.max_vars avail_dyn w0) = m7HdrTailWords0 c s0 ∧
    m7HdrW1 (m7ArenasW1 c.hdr c.max_vars avail_dyn c.delayed_cap c.extend_cap c.scratch_cap w1') =
      m7HdrTailWords1 c s0 ∧
    m7HdrW2 c.mv c.max_vars (m7ArenasW2 c.hdr c.max_vars avail_dyn
      c.delayed_cap c.extend_cap c.scratch_cap w2) = m7HdrTailWords2 c s0 ∧
    m7HdrW3 c.mv (m7ArenasW3 c.hdr c.max_vars avail_dyn c.delayed_cap
      c.extend_cap c.scratch_cap w3'') = m7HdrTailWords3 c s0 := by
  dsimp only
  have hAr : c.hdr + BitVec.ofNat 64 (m7FixedBytes c.max_vars) = c.pArena := by
    simp only [m7FixedBytes_def, MemShrinkCfg.pArena_eq, MemShrinkCfg.pLastLearned_eq,
      MemShrinkCfg.pGlueUsed_eq, MemShrinkCfg.pMinStk_eq, MemShrinkCfg.pScore_eq,
      MemShrinkCfg.pWvec_eq, MemShrinkCfg.pFrameDec_eq, MemShrinkCfg.pFrameTrail_eq,
      MemShrinkCfg.pQStamp_eq, MemShrinkCfg.pQNext_eq, MemShrinkCfg.pQPrev_eq,
      MemShrinkCfg.pShrinkStk_eq, MemShrinkCfg.pMinClr_eq, MemShrinkCfg.pPos_eq,
      MemShrinkCfg.pHeap_eq, MemShrinkCfg.pTmp_eq, MemShrinkCfg.pTrailPos_eq,
      MemShrinkCfg.pTrail_eq, MemShrinkCfg.pReason_eq, MemShrinkCfg.pLevel_eq,
      MemShrinkCfg.pFlags_eq, MemShrinkCfg.pPhasesBest_eq, MemShrinkCfg.pPhasesTarget_eq,
      MemShrinkCfg.pPhases_eq, MemShrinkCfg.pMark_eq, MemShrinkCfg.pVals_eq,
      MemShrinkCfg.minDepth_eq, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  have hWs : c.pArena + BitVec.ofNat 64 (8 * fullInitAp avail_dyn) = c.pWstk := by
    rw [MemShrinkCfg.pWstk_eq, har_c]; congr 2; omega
  have hDl : c.pWstk + BitVec.ofNat 64 (8 * fullInitWp avail_dyn) = c.pDelayed := by
    rw [MemShrinkCfg.pDelayed_eq, hwk_c]; congr 2; omega
  have hRr : c.pArena + BitVec.ofNat 64 (8 * fullInitAp avail_dyn + 8 * fullInitWp avail_dyn) +
      BitVec.ofNat 64 (12 * c.delayed_cap) = c.pRedRefs := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, hWs, hDl, MemShrinkCfg.pRedRefs_eq]
  have hEx : c.pArena + BitVec.ofNat 64 (8 * fullInitAp avail_dyn + 8 * fullInitWp avail_dyn +
      12 * c.delayed_cap + 8 * fullInitRp avail_dyn) = c.pExtendStk := by
    rw [MemShrinkCfg.pExtendStk_eq, MemShrinkCfg.pRedRefs_eq, MemShrinkCfg.pDelayed_eq,
      MemShrinkCfg.pWstk_eq, har_c, hwk_c, hrr_c]
    simp only [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  have hSc : c.pExtendStk + BitVec.ofNat 64 (4 * c.extend_cap) = c.pScratchBuf :=
    (MemShrinkCfg.pScratchBuf_eq c).symm
  have hTr1 : c.pRedRefs + BitVec.ofNat 64 (8 * fullInitRp avail_dyn + 4 * c.extend_cap +
      4 * c.scratch_cap) = c.pTrans := by
    rw [MemShrinkCfg.pTrans_eq, MemShrinkCfg.pScratchBuf_eq, MemShrinkCfg.pExtendStk_eq, hrr_c]
    simp only [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  have hTr2 : c.pArena + BitVec.ofNat 64 (8 * fullInitAp avail_dyn + 8 * fullInitWp avail_dyn +
      12 * c.delayed_cap + 8 * fullInitRp avail_dyn + 4 * c.extend_cap + 4 * c.scratch_cap) =
      c.pTrans := by
    rw [MemShrinkCfg.pTrans_eq, MemShrinkCfg.pScratchBuf_eq, MemShrinkCfg.pExtendStk_eq,
      MemShrinkCfg.pRedRefs_eq, MemShrinkCfg.pDelayed_eq, MemShrinkCfg.pWstk_eq,
      har_c, hwk_c, hrr_c]
    simp only [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  have hTr3 : c.pScratchBuf + BitVec.ofNat 64 (4 * c.scratch_cap) = c.pTrans :=
    (MemShrinkCfg.pTrans_eq c).symm
  exact ⟨m7_hdrTail0_eq c avail_dyn har_c hwk_c d_cur d_val fuel a hw0l hAr hWs,
    m7_hdrTail1_eq c avail_dyn hrr_c d_cur d_val fuel a hw1l hAr hRr hTr1,
    m7_hdrTail2_eq c avail_dyn d_cur d_val fuel a hw2l hAr hTr2,
    m7_hdrTail3_eq c avail_dyn d_cur d_val fuel a hw3l hAr hEx hSc hTr3⟩

private theorem m7_hdrTail4_words (c : MemShrinkCfg) (s : FullState) :
    hdrTail4 c.hdr (m7HdrTailWords0 c s) (m7HdrTailWords1 c s)
      (m7HdrTailWords2 c s) (m7HdrTailWords3 c s) =
      array64 (c.hdr + 32) (m7HdrTailWords c s) := by
  have ht0 : (m7HdrTailWords0 c s).length = 35 := by rw [m7HdrTailWords0_eq]; simp
  have ht1 : (m7HdrTailWords1 c s).length = 35 := by rw [m7HdrTailWords1_eq]; simp
  have ht2 : (m7HdrTailWords2 c s).length = 35 := by rw [m7HdrTailWords2_eq]; simp
  have ht3 : (m7HdrTailWords3 c s).length = 35 := by rw [m7HdrTailWords3_eq]; simp
  rw [hdrTail4_eq_array64 ht0 ht1 ht2 ht3, m7HdrTailWords_eq]

theorem full_init_state_m7_wp (Γ : Env)
    (hHdr : EnvSpec Γ "kissat_parse_header" kissatParseHeaderSpec)
    (hFixed : EnvSpec Γ "full_fixed_bytes_m7" m7FixedBytesSpec)
    (hTrans : EnvSpec Γ "full_trans_bytes_m7" m7TransBytesSpec)
    (hMaxV : EnvSpec Γ "full_calc_max_v_m7" m7CalcMaxVSpec)
    (hExt : EnvSpec Γ "full_calc_ext_cap_m7" m7CalcExtCapSpec)
    (hScr : EnvSpec Γ "full_calc_scr_cap_m7" m7CalcScrCapSpec)
    (hArenas : EnvSpec Γ "full_init_arenas_m7" m7InitArenasSpec)
    (hInitHdr : EnvSpec Γ "full_init_hdr_m7" m7InitHdrSpec)
    (hZt1 : EnvSpec Γ "full_zero_tables1_m7" m7ZeroTables1Spec)
    (hZt2 : EnvSpec Γ "full_zero_tables2_m7" m7ZeroTables2Spec) :
    ∀ a m Q X, m7InitStateSpec a m Q X → Func.wp Γ full_init_state_m7_body a m Q X := by
  rintro ⟨cnf_ptr, cend, hdr_addr, avail, fuel, _⟩ m Q X hsp
  rw [m7InitStateSpec_eq] at hsp
  rcases hsp with ⟨cnfBytes, R, rfl, hcfit, hfit_avail, hav1152, hm_in, hfails, hsucc⟩
  have hav_le : avail.toNat ≤ 2 ^ 64 := by omega
  have hm0 : (region hdr_addr 32 ⋆ (region (hdr_addr + 32) 1120 ⋆
      (region (hdr_addr + 1152) (avail.toNat - 1152) ⋆ (bytes cnf_ptr cnfBytes ⋆ R)))) m := by
    have ha1 : avail.toNat = 32 + (avail.toNat - 32) := by omega
    have ha2 : avail.toNat - 32 = 1120 + (avail.toNat - 1152) := by omega
    rw [ha1, region_split (by omega), ha2, region_split (by omega),
      show hdr_addr + BitVec.ofNat 64 32 = hdr_addr + 32 from rfl,
      show (hdr_addr + 32) + BitVec.ofNat 64 1120 = hdr_addr + 1152 by
        rw [show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl,
          show (1152 : BitVec 64) = BitVec.ofNat 64 1152 from rfl, ptr_add_ofNat]] at hm_in
    exact sep_ac hm_in
  have hm0a := sep_mono (fun _ hr => region32_to_dimacsState hr) hm0
  obtain ⟨mv0, hm0a⟩ := sep_ex_l.mp hm0a
  obtain ⟨nc0, hm0a⟩ := sep_ex_l.mp hm0a
  obtain ⟨cur0, hm0a⟩ := sep_ex_l.mp hm0a
  obtain ⟨val0, hm0a⟩ := sep_ex_l.mp hm0a
  have hm0b : (region (hdr_addr + 32) 1120 ⋆ (dimacsState hdr_addr mv0 nc0 cur0 val0 ⋆
      region (hdr_addr + 1152) (avail.toNat - 1152) ⋆ bytes cnf_ptr cnfBytes ⋆ R)) m :=
    sep_ac hm0a
  have hm0c := sep_mono (fun _ hw => region_to_array64 140 (by decide) hw) hm0b
  obtain ⟨w140, hm0c⟩ := sep_ex_l.mp hm0c
  obtain ⟨hw140, hm0c⟩ := sep_pure_l.mp hm0c
  have hm_pre : (bytes cnf_ptr cnfBytes ⋆ dimacsState hdr_addr mv0 nc0 cur0 val0 ⋆
      array64 (hdr_addr + 32) w140 ⋆ region (hdr_addr + 1152) (avail.toNat - 1152) ⋆ R) m :=
    sep_ac hm0c
  rw [envSpec_eq] at hHdr hFixed hTrans hMaxV hExt hScr hArenas hInitHdr hZt1 hZt2
  unfold full_init_state_m7_body; dsimp only [Func.wp]
  apply wp_call_of_spec; apply hHdr
  refine ⟨mv0, nc0, cur0, val0, cnfBytes, array64 (hdr_addr + 32) w140 ⋆
    region (hdr_addr + 1152) (avail.toNat - 1152) ⋆ R, rfl, hcfit,
    Eq.mp (congrFun (by ac_rfl) m) hm_pre, ?_⟩
  cases hhdr : parseHeader cnfBytes with
  | none =>
    intro mv' nc' cur' val' m1 hm1
    dsimp only [Arg.val] at hm1
    refine wp_jnz_of (fun hc => by cases hc) (fun _ => ?_)
    c0_hsteps
    have hm1_r : (bytes cnf_ptr cnfBytes ⋆ dimacsState hdr_addr mv' nc' cur' val' ⋆
        array64 (hdr_addr + 32) w140 ⋆ region (hdr_addr + 1152) (avail.toNat - 1152) ⋆ R) m1 :=
      Eq.mp (congrFun (by ac_rfl) m1) hm1
    have hm1' := m7_hdr_region_rejoin hav1152 hav_le hw140 hm1_r
    exact hfails m1 hm1' (fun _ _ _ h => by rw [hhdr] at h; cases h)
  | some p =>
    rcases p with ⟨mv, nc, rest⟩
    intro j m1 hmv_bd hnc_bd hj_le hdrop hm1
    dsimp only [Arg.val] at hm1
    refine wp_jnz_of (fun _ => ?_) (fun hc => by cases hc)
    · have hm1s : (array64 hdr_addr [BitVec.ofNat 64 mv, BitVec.ofNat 64 nc,
            cnf_ptr + BitVec.ofNat 64 j, BitVec.ofNat 64 nc] ⋆
          (bytes cnf_ptr cnfBytes ⋆ array64 (hdr_addr + 32) w140 ⋆
            region (hdr_addr + 1152) (avail.toNat - 1152) ⋆ R)) m1 := by
        have hm1_d := hm1; unfold dimacsState at hm1_d
        exact Eq.mp (congrFun (by ac_rfl) m1) hm1_d
      refine wp_load_array64 (i := 0) (by simp [Arg.val]) (by simp) hm1s ?_
      c0_hstep
      refine wp_load_array64 (i := 1) (by simp [Arg.val]) (by simp) hm1s ?_
      dsimp only [List.getElem_cons_zero, List.getElem_cons_succ]
      have hmv2 : mv < 2 * dimacsBound := by unfold dimacsBound at *; omega
      have hmv_tonat : (BitVec.ofNat 64 mv).toNat = mv := by
        simp [BitVec.toNat_ofNat]; unfold dimacsBound at *; omega
      have hnc_tonat : (BitVec.ofNat 64 nc).toNat = nc := by
        simp [BitVec.toNat_ofNat]; unfold dimacsBound at *; omega
      apply wp_call_of_spec; apply hFixed; rw [m7FixedBytesSpec_eq]
      refine ⟨by dsimp [vals, Arg.val]; rw [hmv_tonat]; exact hmv2, ?_⟩
      dsimp only [vals, Arg.val]; rw [hmv_tonat]
      apply wp_call_of_spec; apply hTrans; rw [m7TransBytesSpec_eq]
      refine ⟨by dsimp [vals, Arg.val]; rw [hmv_tonat]; exact hmv2, ?_⟩
      dsimp only [vals, Arg.val]; rw [hmv_tonat]
      have hfx_lt := m7FixedBytes_lt hmv2
      have htr_lt := m7TransBytes_lt hmv2
      have htot_lt : m7FixedBytes mv + m7TransBytes mv < 2 ^ 64 := by omega
      have hfxtr_eq : BitVec.ofNat 64 (m7FixedBytes mv) + BitVec.ofNat 64 (m7TransBytes mv) =
          BitVec.ofNat 64 (m7FixedBytes mv + m7TransBytes mv) := by rw [← BitVec.ofNat_add]
      have hfxtr_toNat : (BitVec.ofNat 64 (m7FixedBytes mv + m7TransBytes mv)).toNat =
          m7FixedBytes mv + m7TransBytes mv := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htot_lt]
      c0_hsplit
      · c0_hsteps
        have hm1_r : (bytes cnf_ptr cnfBytes ⋆ dimacsState hdr_addr (BitVec.ofNat 64 mv)
            (BitVec.ofNat 64 nc) (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 nc) ⋆
            array64 (hdr_addr + 32) w140 ⋆ region (hdr_addr + 1152) (avail.toNat - 1152) ⋆ R) m1 :=
          Eq.mp (congrFun (by ac_rfl) m1) hm1
        have hm1' := m7_hdr_region_rejoin hav1152 hav_le hw140 hm1_r
        refine hfails m1 hm1' fun mv' nc' rest' h' => ?_
        rw [hhdr] at h'; rcases Option.some.inj h' with ⟨rfl, rfl, rfl⟩
        rw [Nat.mod_eq_of_lt htot_lt] at hc
        omega
      · have hge_mv : m7FixedBytes mv + m7TransBytes mv ≤ avail.toNat := by
          rw [Nat.mod_eq_of_lt htot_lt] at hc; omega
        c0_hsplit
        · c0_hsteps
          have hm1_r : (bytes cnf_ptr cnfBytes ⋆ dimacsState hdr_addr (BitVec.ofNat 64 mv)
              (BitVec.ofNat 64 nc) (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 nc) ⋆
              array64 (hdr_addr + 32) w140 ⋆ region (hdr_addr + 1152) (avail.toNat - 1152) ⋆
              R) m1 :=
            Eq.mp (congrFun (by ac_rfl) m1) hm1
          have hm1' := m7_hdr_region_rejoin hav1152 hav_le hw140 hm1_r
          refine hfails m1 hm1' fun mv' nc' rest' h' => ?_
          rw [hhdr] at h'; rcases Option.some.inj h' with ⟨rfl, rfl, rfl⟩
          have hnc40 : nc * 40 + 136 < 2 ^ 64 := by unfold dimacsBound at *; omega
          have hnc64 : nc < 2 ^ 64 := by unfold dimacsBound at *; omega
          have hav_lt : avail.toNat < 2 ^ 64 := avail.isLt
          rw [Nat.mod_eq_of_lt htot_lt, Nat.mod_eq_of_lt hnc64,
            show BitVec.toNat 40 = 40 by decide, show BitVec.toNat 136 = 136 by decide,
            Nat.mod_eq_of_lt hnc40,
            show 2 ^ 64 - (m7FixedBytes mv + m7TransBytes mv) + avail.toNat =
              2 ^ 64 + (avail.toNat - (m7FixedBytes mv + m7TransBytes mv)) by omega,
            Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hc
          omega
        · have hbase : m7FixedBytes mv + m7TransBytes mv + nc * 40 + 136 ≤ avail.toNat := by
            have hnc40 : nc * 40 + 136 < 2 ^ 64 := by unfold dimacsBound at *; omega
            have hnc64 : nc < 2 ^ 64 := by unfold dimacsBound at *; omega
            have hav_lt : avail.toNat < 2 ^ 64 := avail.isLt
            rw [Nat.mod_eq_of_lt htot_lt, Nat.mod_eq_of_lt hnc64,
              show BitVec.toNat 40 = 40 by decide, show BitVec.toNat 136 = 136 by decide,
              Nat.mod_eq_of_lt hnc40,
              show 2 ^ 64 - (m7FixedBytes mv + m7TransBytes mv) + avail.toNat =
                2 ^ 64 + (avail.toNat - (m7FixedBytes mv + m7TransBytes mv)) by omega,
              Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hc
            omega
          let mx := m7CalcMaxV avail.toNat mv nc (m7FixedBytes mv)
          have hmx_ge : mv ≤ mx := m7CalcMaxV_ge
          have hmx_lt : mx < 2 * dimacsBound := m7CalcMaxV_lt hmv_bd
          have hmx_fits : m7FixedBytes mx + m7TransBytes mx + nc * 40 + 136 ≤ avail.toNat :=
            m7CalcMaxV_fits hbase
          have hfx_lt64 : m7FixedBytes mv < 2 ^ 64 := by omega
          apply wp_call_of_spec; apply hMaxV; rw [m7CalcMaxVSpec_eq]
          refine ⟨?_, ?_, ?_, ?_⟩
          · dsimp only [vals, Arg.val]; rw [hmv_tonat]; exact hmv_bd
          · dsimp only [vals, Arg.val]; rw [hnc_tonat]; exact hnc_bd
          · dsimp only [vals, Arg.val]
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfx_lt64]; omega
          · dsimp only [vals, Arg.val]; rw [hmv_tonat, hnc_tonat]
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfx_lt64]
            apply wp_call_of_spec; apply hTrans; rw [m7TransBytesSpec_eq]
            refine ⟨by dsimp [vals, Arg.val]; rw [BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by unfold dimacsBound at *; omega)]; exact hmx_lt, ?_⟩
            dsimp only [vals, Arg.val]
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold dimacsBound at *; omega)]
            apply wp_call_of_spec; apply hFixed; rw [m7FixedBytesSpec_eq]
            refine ⟨by dsimp [vals, Arg.val]; rw [BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by unfold dimacsBound at *; omega)]; exact hmx_lt, ?_⟩
            dsimp only [vals, Arg.val]
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold dimacsBound at *; omega)]
            have hfx_mx_lt : m7FixedBytes mx < 2 ^ 64 :=
              Nat.lt_trans (m7FixedBytes_lt hmx_lt) (by decide)
            have htr_mx_lt : m7TransBytes mx < 2 ^ 64 :=
              Nat.lt_trans (m7TransBytes_lt hmx_lt) (by decide)
            have hmx_fx_le : m7FixedBytes mx ≤ avail.toNat := by omega
            have hrem_fx_eq : avail - BitVec.ofNat 64 (m7FixedBytes mx) =
                BitVec.ofNat 64 (avail.toNat - m7FixedBytes mx) := by
              apply BitVec.eq_of_toNat_eq
              rw [BitVec.toNat_sub_of_le (by
                rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfx_mx_lt]
                exact hmx_fx_le),
                BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfx_mx_lt,
                Nat.mod_eq_of_lt (by omega)]
            c0_hsplit
            · exfalso
              have hnc64 : nc < 2 ^ 64 := by unfold dimacsBound at *; omega
              have hav_lt : avail.toNat < 2 ^ 64 := avail.isLt
              rw [Nat.mod_eq_of_lt hfx_mx_lt, Nat.mod_eq_of_lt hnc64,
                show BitVec.toNat 40 = 40 by decide, show BitVec.toNat 136 = 136 by decide] at hc
              change (2 ^ 64 - m7FixedBytes mx + avail.toNat) % 2 ^ 64 <
                (m7TransBytes mx + nc * 40 + 136) % 2 ^ 64 at hc
              rw [Nat.mod_eq_of_lt (by omega : m7TransBytes mx + nc * 40 + 136 < 2 ^ 64),
                show 2 ^ 64 - m7FixedBytes mx + avail.toNat =
                  2 ^ 64 + (avail.toNat - m7FixedBytes mx) by omega,
                Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hc
              omega
            · let avail_dyn := avail.toNat - (m7FixedBytes mx + m7TransBytes mx)
              have hav_dyn_ge : nc * 40 + 136 ≤ avail_dyn := by omega
              have hav_dyn_eq : (avail - BitVec.ofNat 64 (m7FixedBytes mx)) -
                  BitVec.ofNat 64 (m7TransBytes mx) = BitVec.ofNat 64 avail_dyn := by
                apply BitVec.eq_of_toNat_eq
                rw [hrem_fx_eq, BitVec.toNat_sub_of_le (by
                  rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt htr_mx_lt, Nat.mod_eq_of_lt (by omega)]; omega),
                  BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt htr_mx_lt, Nat.mod_eq_of_lt (by omega),
                  Nat.mod_eq_of_lt (by omega)]
                omega
              refine wp_join_state1 (fun x : BitVec 64 => x)
                (fun del_cap m2 => del_cap = BitVec.ofNat 64 (fullInitDelCap avail_dyn) ∧ m2 = m1)
                ?_ ?_
              · rintro J403 del_cap m2 ⟨rfl, hm2_eq⟩; subst m2
                dsimp only [Blocks.get_here]
                have hdyn_toNat : (BitVec.ofNat 64 avail_dyn).toNat = avail_dyn := by
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                have hav_dyn' : avail - BitVec.ofNat 64 (m7FixedBytes (m7CalcMaxV avail.toNat mv
                    nc (m7FixedBytes mv))) - BitVec.ofNat 64 (m7TransBytes (m7CalcMaxV
                    avail.toNat mv nc (m7FixedBytes mv))) = BitVec.ofNat 64 avail_dyn :=
                  hav_dyn_eq
                apply wp_call_of_spec; apply hExt; rw [m7CalcExtCapSpec_eq]
                dsimp only [vals, lift2, Arg.val]; rw [hav_dyn', hdyn_toNat]
                apply wp_call_of_spec; apply hScr; rw [m7CalcScrCapSpec_eq]
                dsimp only [vals, Arg.val]; rw [hdyn_toNat]
                c0_hsteps_nogrp
                refine wp_join_state (ts := [i64, i64, i64])
                  (fun p : BitVec 64 × BitVec 64 × BitVec 64 => (p.1, p.2.1, p.2.2, ()))
                  (fun p m3 =>
                    p = (BitVec.ofNat 64 (m7InitExtCap nc avail_dyn),
                         BitVec.ofNat 64 (m7InitScrCap nc avail_dyn),
                         BitVec.ofNat 64 (m7InitDyn nc avail_dyn)) ∧ m3 = m1)
                  ?_ ?_
                · rintro J632 p m3 ⟨rfl, hm3_eq⟩; subst m3
                  dsimp only [Blocks.get_here]
                  have hdyn_le := m7InitDyn_le hav_dyn_ge
                  have hdyn_eq : m7InitDyn nc avail_dyn =
                      fullInitDelCap avail_dyn * 12 + 4 * m7InitExtCap nc avail_dyn +
                        4 * m7InitScrCap nc avail_dyn := rfl
                  let rem := avail_dyn - m7InitDyn nc avail_dyn
                  have hrem_ge40 : 40 ≤ rem := by omega
                  have har_fits := m7InitArenas_le hav_dyn_ge
                  dsimp only at har_fits
                  have hw1 : 1 ≤ 2 * fullInitWp rem := by
                    have := m7InitWp_ge_one hrem_ge40; omega
                  have hext_bd0 : m7InitExtCap nc avail_dyn < dimacsBound := by
                    have := m7CalcExtCap_lt avail_dyn
                    unfold m7InitExtCap; dsimp only; split
                    · unfold dimacsBound; omega
                    · exact this
                  have hscr_bd0 : m7InitScrCap nc avail_dyn < dimacsBound := by
                    have := m7CalcScrCap_lt avail_dyn
                    unfold m7InitScrCap; dsimp only; split
                    · unfold dimacsBound; omega
                    · exact this
                  let c : MemShrinkCfg :=
                    { hdr := hdr_addr, avail := avail.toNat, mv := mv, max_vars := mx
                      bva_cap := mx - mv, nc := nc
                      arena_cap := 2 * fullInitAp rem, wcap := 2 * fullInitWp rem
                      delayed_cap := fullInitDelCap avail_dyn
                      red_cap := 2 * fullInitRp rem
                      extend_cap := m7InitExtCap nc avail_dyn
                      scratch_cap := m7InitScrCap nc avail_dyn
                      hbva := by omega
                      hmv := hmv_bd
                      hmaxv := hmx_lt
                      hnc := hnc_bd
                      harena := fullInitAp_lt
                      hwcap := fullInitWp_lt
                      hdel := fullInitDelCap_lt
                      hred := fullInitRp_lt
                      hext := hext_bd0
                      hscr := hscr_bd0
                      havail_fit := hfit_avail
                      hsize := by dsimp only [rem]; omega }
                  have hm1_w : (array64 (hdr_addr + 32) w140 ⋆
                      (array64 hdr_addr [BitVec.ofNat 64 mv, BitVec.ofNat 64 nc,
                        cnf_ptr + BitVec.ofNat 64 j, BitVec.ofNat 64 nc] ⋆
                        bytes cnf_ptr cnfBytes ⋆
                        region (hdr_addr + 1152) (avail.toNat - 1152) ⋆ R)) m1 := by
                    have hm1_d := hm1; unfold dimacsState at hm1_d
                    exact Eq.mp (congrFun (by ac_rfl) m1) hm1_d
                  let w0 := w140.take 35
                  let w1 := (w140.drop 35).take 35
                  let w2 := (w140.drop 70).take 35
                  let w3 := (w140.drop 105).take 35
                  have lw0 : w0.length = 35 := by simp [w0, hw140]
                  have lw1 : w1.length = 35 := by simp [w1, hw140]
                  have lw2 : w2.length = 35 := by simp [w2, hw140]
                  have lw3 : w3.length = 35 := by simp [w3, hw140]
                  have hm1_a : (array64 (hdr_addr + 312) w1 ⋆
                      (array64 (hdr_addr + 32) w0 ⋆ array64 (hdr_addr + 592) w2 ⋆
                        array64 (hdr_addr + 872) w3 ⋆
                        array64 hdr_addr [BitVec.ofNat 64 mv, BitVec.ofNat 64 nc,
                          cnf_ptr + BitVec.ofNat 64 j, BitVec.ofNat 64 nc] ⋆
                        bytes cnf_ptr cnfBytes ⋆
                        region (hdr_addr + 1152) (avail.toNat - 1152) ⋆ R)) m1 := by
                    have hm1_ht := array64_to_hdrTail4 hw140 hm1_w
                    have hm1_a0 := sep_mono (fun _ h => h.2.2.2.2) hm1_ht
                    exact Eq.mp (congrFun (by ac_rfl) m1) hm1_a0
                  c0_hstep
                  refine wp_store_array64 (base := hdr_addr + 312) (i := 17)
                    (by dsimp only [Arg.val]; rw [BitVec.add_assoc]; rfl) (by omega) hm1_a
                    fun m2 hm2 => ?_
                  have hm2_s : (array64 (hdr_addr + 872) w3 ⋆
                      (array64 (hdr_addr + 32) w0 ⋆
                        array64 (hdr_addr + 312) (w1.set 17 (BitVec.ofNat 64 c.delayed_cap)) ⋆
                        array64 (hdr_addr + 592) w2 ⋆
                        array64 hdr_addr [BitVec.ofNat 64 mv, BitVec.ofNat 64 nc,
                          cnf_ptr + BitVec.ofNat 64 j, BitVec.ofNat 64 nc] ⋆
                        bytes cnf_ptr cnfBytes ⋆
                        region (hdr_addr + 1152) (avail.toNat - 1152) ⋆ R)) m2 :=
                    Eq.mp (congrFun (by ac_rfl) m2) hm2
                  c0_hstep
                  refine wp_store_array64 (base := hdr_addr + 872) (i := 4)
                    (by dsimp only [Arg.val]; rw [BitVec.add_assoc]; rfl) (by omega) hm2_s
                    fun m3 hm3 => ?_
                  c0_hstep
                  refine wp_store_array64 (base := hdr_addr + 872) (i := 7)
                    (by dsimp only [Arg.val]; rw [BitVec.add_assoc]; rfl) (by simp [lw3]) hm3
                    fun m4 hm4 => ?_
                  have hm4_ht : (hdrTail4 hdr_addr w0 (w1.set 17 (BitVec.ofNat 64 c.delayed_cap))
                      w2 ((w3.set 4 (BitVec.ofNat 64 c.extend_cap)).set 7
                        (BitVec.ofNat 64 c.scratch_cap)) ⋆
                      (array64 hdr_addr [BitVec.ofNat 64 mv, BitVec.ofNat 64 nc,
                        cnf_ptr + BitVec.ofNat 64 j, BitVec.ofNat 64 nc] ⋆
                        bytes cnf_ptr cnfBytes ⋆
                        region (hdr_addr + 1152) (avail.toNat - 1152) ⋆ R)) m4 := by
                    have hm4' : ((array64 (hdr_addr + 32) w0 ⋆
                        array64 (hdr_addr + 312) (w1.set 17 (BitVec.ofNat 64 c.delayed_cap)) ⋆
                        array64 (hdr_addr + 592) w2 ⋆
                        array64 (hdr_addr + 872) ((w3.set 4 (BitVec.ofNat 64 c.extend_cap)).set 7
                          (BitVec.ofNat 64 c.scratch_cap))) ⋆
                        (array64 hdr_addr [BitVec.ofNat 64 mv, BitVec.ofNat 64 nc,
                          cnf_ptr + BitVec.ofNat 64 j, BitVec.ofNat 64 nc] ⋆
                          bytes cnf_ptr cnfBytes ⋆
                          region (hdr_addr + 1152) (avail.toNat - 1152) ⋆ R)) m4 :=
                      Eq.mp (congrFun (by ac_rfl) m4) hm4
                    exact sep_mono (fun _ h => ⟨lw0, by simp [lw1], lw2, by simp [lw3], h⟩) hm4'
                  have hrem_eq : BitVec.ofNat 64 avail_dyn -
                      BitVec.ofNat 64 (m7InitDyn nc avail_dyn) = BitVec.ofNat 64 rem := by
                    apply BitVec.eq_of_toNat_eq
                    rw [BitVec.toNat_sub_of_le (by
                      rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega),
                      BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
                      Nat.mod_eq_of_lt (by omega)]
                  have hdel_bd : c.delayed_cap < dimacsBound := c.hdel
                  have hext_bd : c.extend_cap < dimacsBound := c.hext
                  have hscr_bd : c.scratch_cap < dimacsBound := c.hscr
                  c0_hsteps
                  apply wp_call_of_spec; apply hArenas; rw [m7InitArenasSpec_eq]
                  refine ⟨rfl, ?_, ?_, c.delayed_cap, c.extend_cap, c.scratch_cap,
                    w0, w1.set 17 (BitVec.ofNat 64 c.delayed_cap), w2,
                    (w3.set 4 (BitVec.ofNat 64 c.extend_cap)).set 7 (BitVec.ofNat 64 c.scratch_cap),
                    array64 hdr_addr [BitVec.ofNat 64 mv, BitVec.ofNat 64 nc,
                      cnf_ptr + BitVec.ofNat 64 j, BitVec.ofNat 64 nc] ⋆
                      bytes cnf_ptr cnfBytes ⋆ region (hdr_addr + 1152) (avail.toNat - 1152) ⋆ R,
                    hdel_bd, hext_bd, hscr_bd, ?_, ?_, ?_, hm4_ht, fun m5 hm5 => ?_⟩
                  · dsimp [vals, Arg.val]; rw [BitVec.toNat_ofNat,
                      Nat.mod_eq_of_lt (by unfold dimacsBound at *; omega)]; exact hmx_lt
                  · have := c.havail_fit
                    have := c.hsize
                    dsimp [vals, Arg.val]; rw [BitVec.toNat_ofNat,
                      Nat.mod_eq_of_lt (by unfold dimacsBound at *; omega)]
                    change c.hdr.toNat + m7FixedBytes c.max_vars < 2 ^ 64
                    omega
                  · simp [lw1]
                  · simp [lw3]
                  · simp [lw3]
                  · have hmx_toNat :
                        (BitVec.ofNat 64 (m7CalcMaxV avail.toNat mv nc (m7FixedBytes mv))).toNat =
                          mx := by
                      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold dimacsBound at *; omega)]
                    have hrem_toNat : (BitVec.ofNat 64 avail_dyn -
                        BitVec.ofNat 64 (m7InitDyn nc avail_dyn)).toNat = rem := by
                      rw [hrem_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                    dsimp only [vals, Arg.val] at hm5
                    rw [hmx_toNat, hrem_toNat] at hm5
                    c0_hsteps
                    apply wp_call_of_spec; apply hInitHdr; rw [m7InitHdrSpec_eq]
                    refine ⟨?_, ?_,
                      m7ArenasW0 hdr_addr mx rem w0,
                      m7ArenasW1 hdr_addr mx rem c.delayed_cap c.extend_cap c.scratch_cap
                        (w1.set 17 (BitVec.ofNat 64 c.delayed_cap)),
                      m7ArenasW2 hdr_addr mx rem c.delayed_cap c.extend_cap c.scratch_cap w2,
                      m7ArenasW3 hdr_addr mx rem c.delayed_cap c.extend_cap c.scratch_cap
                        ((w3.set 4 (BitVec.ofNat 64 c.extend_cap)).set 7
                          (BitVec.ofNat 64 c.scratch_cap)),
                      array64 hdr_addr [BitVec.ofNat 64 mv, BitVec.ofNat 64 nc,
                        cnf_ptr + BitVec.ofNat 64 j, BitVec.ofNat 64 nc] ⋆
                        bytes cnf_ptr cnfBytes ⋆ region (hdr_addr + 1152) (avail.toNat - 1152) ⋆ R,
                      hm5, fun m6 hm6 => ?_⟩
                    · dsimp [vals, Arg.val]; rw [hmv_tonat, hmx_toNat]; exact hmx_ge
                    · dsimp [vals, Arg.val]; rw [hmx_toNat]; exact hmx_lt
                    · dsimp only [vals, Arg.val] at hm6
                      rw [hmv_tonat, hmx_toNat] at hm6
                      have hm6_r : (region (hdr_addr + 1152) (avail.toNat - 1152) ⋆
                          (hdrTail4 hdr_addr
                            (m7HdrW0 c.mv fuel (m7ArenasW0 c.hdr c.max_vars rem w0))
                            (m7HdrW1 (m7ArenasW1 c.hdr c.max_vars rem c.delayed_cap c.extend_cap
                              c.scratch_cap (w1.set 17 (BitVec.ofNat 64 c.delayed_cap))))
                            (m7HdrW2 c.mv c.max_vars (m7ArenasW2 c.hdr c.max_vars rem c.delayed_cap
                              c.extend_cap c.scratch_cap w2))
                            (m7HdrW3 c.mv (m7ArenasW3 c.hdr c.max_vars rem c.delayed_cap
                              c.extend_cap c.scratch_cap
                              ((w3.set 4 (BitVec.ofNat 64 c.extend_cap)).set 7
                                (BitVec.ofNat 64 c.scratch_cap)))) ⋆
                            array64 hdr_addr [BitVec.ofNat 64 mv, BitVec.ofNat 64 nc,
                              cnf_ptr + BitVec.ofNat 64 j, BitVec.ofNat 64 nc] ⋆
                            bytes cnf_ptr cnfBytes ⋆ R)) m6 := Eq.mp (congrFun (by ac_rfl) m6) hm6
                      obtain ⟨a, ha⟩ := m7_region_to_mem c (cnf_ptr + BitVec.ofNat 64 j)
                        (BitVec.ofNat 64 nc) fuel hav1152 hm6_r
                      let s0 := m7InitState c (cnf_ptr + BitVec.ofNat 64 j)
                        (BitVec.ofNat 64 nc) fuel a
                      obtain ⟨ht0, ht1, ht2, ht3⟩ := m7_hdrTail_eq c rem rfl rfl rfl
                        (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 nc) fuel a
                        lw0 lw1 lw2 lw3
                      rw [ht0, ht1, ht2, ht3,
                        show hdr_addr = c.hdr from rfl, m7_hdrTail4_words c s0] at ha
                      have hm6_s0 : (MemShrinkMem c s0 ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m6 := by
                        rw [MemShrinkMem_eq]; unfold dimacsState
                        exact Eq.mp (congrFun (by ac_rfl) m6) ha
                      have hlen0 := m7_init_lengthsOk c hw1 (cnf_ptr + BitVec.ofNat 64 j)
                        (BitVec.ofNat 64 nc) fuel a
                      c0_hsteps
                      apply wp_call_of_spec; apply hZt1; rw [m7ZeroTables1Spec_eq]
                      refine ⟨c, s0, bytes cnf_ptr cnfBytes ⋆ R, rfl, hlen0, hm6_s0,
                        fun s1 m7 hsc1 hvals1 hlm1 hwvec1 hmin1 hgu1 hll1 hlen1 hm7 => ?_⟩
                      c0_hsteps
                      apply wp_call_of_spec; apply hZt2; rw [m7ZeroTables2Spec_eq]
                      refine ⟨c, s1, bytes cnf_ptr cnfBytes ⋆ R, rfl, hlen1, hm7,
                        fun s2 m8 hsc2 hvals2 hlm2 hwvec2 hmin2 hgu2 hll2 hmrk2 hlen2 hm8 => ?_⟩
                      c0_hsteps
                      have hsc := fullHdrScalarsEq_trans hsc2 hsc1
                      rw [fullHdrScalarsEq_eq] at hsc
                      rcases hsc with ⟨hd1, hd2, hcv, hun, har_l, hwk_l, hte, hpr, hcl, hfl_s, hcr,
                        htc, htl, hmc, hmcf, hoo, hin, hni, hnr, hnb, huf, hpb, hdm, hex_l, hpl,
                        hel⟩
                      dsimp only [s0, m7InitState] at hd1 hd2 hcv hun har_l hwk_l hte hpr hcl hfl_s
                      dsimp only [s0, m7InitState] at hcr htc htl hmc hmcf hoo hin hni hnr hnb huf
                      dsimp only [s0, m7InitState] at hpb hdm hex_l hpl hel
                      refine hsucc c s2 j rest m8 rfl rfl hhdr hj_le hdrop
                        (m7_init_sparse_inv c hlen2 hmrk2 (hlm2.trans hlm1) (hll2.trans hll1) hex_l)
                        hcv hun hd1 hd2 har_l hwk_l hte hpr hcl hfl_s hcr htc htl hmc hmcf hoo
                        hin hni hnr hnb huf hpb hdm (hvals2.trans hvals1) (hwvec2.trans hwvec1)
                        hmrk2 (hlm2.trans hlm1) hex_l hpl hel (Eq.mp (congrFun (by ac_rfl) m8) hm8)
                · intro J632 hJ632
                  have hext_le : m7CalcExtCap avail_dyn ≤ 4194304 := m7CalcExtCap_le avail_dyn
                  have hscr_le : m7CalcScrCap avail_dyn ≤ 1048576 := m7CalcScrCap_le avail_dyn
                  have hdel_le : fullInitDelCap avail_dyn ≤ 4096 := by
                    unfold fullInitDelCap; split <;> omega
                  let dyn0 := fullInitDelCap avail_dyn * 12 + 4 * m7CalcExtCap avail_dyn +
                    4 * m7CalcScrCap avail_dyn
                  have hd0_lt : dyn0 + (nc * 40 + 136) < 2 ^ 64 := by
                    dsimp [dyn0]; unfold dimacsBound at *; omega
                  have hsh2_ext : BitVec.ofNat 64 (m7CalcExtCap avail_dyn) <<<
                      ((BitVec.signExtend 64 2#32).toNat % 64) =
                      BitVec.ofNat 64 (4 * m7CalcExtCap avail_dyn) := by
                    rw [show ((BitVec.signExtend 64 2#32).toNat % 64) = 2 by decide]
                    apply BitVec.eq_of_toNat_eq
                    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
                    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
                  have hsh2_scr : BitVec.ofNat 64 (m7CalcScrCap avail_dyn) <<<
                      ((BitVec.signExtend 64 2#32).toNat % 64) =
                      BitVec.ofNat 64 (4 * m7CalcScrCap avail_dyn) := by
                    rw [show ((BitVec.signExtend 64 2#32).toNat % 64) = 2 by decide]
                    apply BitVec.eq_of_toNat_eq
                    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
                    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
                  have hdel_mul_bv : BitVec.ofNat 64 (fullInitDelCap avail_dyn) * 12#64 =
                      BitVec.ofNat 64 (fullInitDelCap avail_dyn * 12) := by
                    rw [show (12#64 : BitVec 64) = BitVec.ofNat 64 12 from rfl, m7_bv_ofNat_mul]
                  have hdyn0_bv : BitVec.ofNat 64 (fullInitDelCap avail_dyn) * 12#64 +
                      BitVec.ofNat 64 (m7CalcExtCap avail_dyn) <<< 2 +
                      BitVec.ofNat 64 (m7CalcScrCap avail_dyn) <<< 2 = BitVec.ofNat 64 dyn0 := by
                    have he2 : BitVec.ofNat 64 (m7CalcExtCap avail_dyn) <<< 2 =
                        BitVec.ofNat 64 (4 * m7CalcExtCap avail_dyn) := by
                      simpa [show ((BitVec.signExtend 64 2#32).toNat % 64) = 2 by decide] using
                        hsh2_ext
                    have hs2 : BitVec.ofNat 64 (m7CalcScrCap avail_dyn) <<< 2 =
                        BitVec.ofNat 64 (4 * m7CalcScrCap avail_dyn) := by
                      simpa [show ((BitVec.signExtend 64 2#32).toNat % 64) = 2 by decide] using
                        hsh2_scr
                    rw [hdel_mul_bv, he2, hs2, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
                  have hav_d64 : avail_dyn < 2 ^ 64 := by omega
                  have hdel64 : fullInitDelCap avail_dyn < 2 ^ 64 := by omega
                  have hext64 : m7CalcExtCap avail_dyn < 2 ^ 64 := by omega
                  have hscr64 : m7CalcScrCap avail_dyn < 2 ^ 64 := by omega
                  have hnc64 : nc < 2 ^ 64 := by unfold dimacsBound at *; omega
                  have hsum64 : dyn0 + nc * 40 + 136 < 2 ^ 64 := by omega
                  c0_hsplit
                  · rw [Nat.mod_eq_of_lt hav_d64, Nat.mod_eq_of_lt hdel64, Nat.mod_eq_of_lt hext64,
                      Nat.mod_eq_of_lt hscr64, Nat.mod_eq_of_lt hnc64,
                      show BitVec.toNat 12 = 12 by decide, show BitVec.toNat 40 = 40 by decide,
                      show BitVec.toNat 136 = 136 by decide,
                      show (2 ^ OfNat.ofNat 2 : Nat) = 4 by decide,
                      Nat.mul_comm (m7CalcExtCap avail_dyn) 4,
                      Nat.mul_comm (m7CalcScrCap avail_dyn) 4] at hc
                    change avail_dyn < (dyn0 + nc * 40 + 136) % 2 ^ 64 at hc
                    rw [Nat.mod_eq_of_lt hsum64] at hc
                    refine hJ632 (0#64, 0#64, BitVec.ofNat 64 (fullInitDelCap avail_dyn) * 12#64) m1
                      ⟨?_, rfl⟩
                    unfold m7InitDyn; unfold m7InitExtCap m7InitScrCap; dsimp only
                    have hlt_d : avail_dyn < fullInitDelCap avail_dyn * 12 +
                        4 * m7CalcExtCap avail_dyn + 4 * m7CalcScrCap avail_dyn +
                        nc * 40 + 136 := by
                      dsimp only [dyn0] at hc; omega
                    simp only [hlt_d, ↓reduceIte, Nat.mul_zero, Nat.add_zero]
                    rw [hdel_mul_bv]
                  · rw [Nat.mod_eq_of_lt hav_d64, Nat.mod_eq_of_lt hdel64, Nat.mod_eq_of_lt hext64,
                      Nat.mod_eq_of_lt hscr64, Nat.mod_eq_of_lt hnc64,
                      show BitVec.toNat 12 = 12 by decide, show BitVec.toNat 40 = 40 by decide,
                      show BitVec.toNat 136 = 136 by decide,
                      show (2 ^ OfNat.ofNat 2 : Nat) = 4 by decide,
                      Nat.mul_comm (m7CalcExtCap avail_dyn) 4,
                      Nat.mul_comm (m7CalcScrCap avail_dyn) 4] at hc
                    change ¬ avail_dyn < (dyn0 + nc * 40 + 136) % 2 ^ 64 at hc
                    rw [Nat.mod_eq_of_lt hsum64] at hc
                    refine hJ632 (BitVec.ofNat 64 (m7CalcExtCap avail_dyn),
                      BitVec.ofNat 64 (m7CalcScrCap avail_dyn),
                      BitVec.ofNat 64 (fullInitDelCap avail_dyn) * 12#64 +
                        BitVec.ofNat 64 (m7CalcExtCap avail_dyn) <<< 2 +
                        BitVec.ofNat 64 (m7CalcScrCap avail_dyn) <<< 2) m1 ⟨?_, rfl⟩
                    rw [hdyn0_bv]
                    unfold m7InitDyn; unfold m7InitExtCap m7InitScrCap; dsimp only
                    have hge_d : ¬ avail_dyn < fullInitDelCap avail_dyn * 12 +
                        4 * m7CalcExtCap avail_dyn + 4 * m7CalcScrCap avail_dyn +
                        nc * 40 + 136 := by
                      dsimp only [dyn0] at hc; omega
                    simp only [hge_d, ↓reduceIte]; rfl
              · intro J403 hJ403
                have h524 : BitVec.toNat (524288 : BitVec 64) = 524288 := by decide
                have hdyn_toNat : (BitVec.ofNat 64 avail_dyn).toNat = avail_dyn := by
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                have hdyn' : avail - BitVec.ofNat 64 (m7FixedBytes (m7CalcMaxV avail.toNat mv nc
                    (m7FixedBytes mv))) - BitVec.ofNat 64 (m7TransBytes (m7CalcMaxV avail.toNat
                    mv nc (m7FixedBytes mv))) = BitVec.ofNat 64 avail_dyn := hav_dyn_eq
                c0_hsplit
                · have hge : 524288 ≤ avail_dyn := by
                    dsimp only [lift2, Arg.val] at hc
                    rw [hdyn', hdyn_toNat, h524] at hc
                    exact hc
                  refine hJ403 4096#64 m1 ⟨?_, rfl⟩
                  unfold fullInitDelCap; split <;> first | rfl | omega
                · have hlt : avail_dyn < 524288 := by
                    dsimp only [lift2, Arg.val] at hc
                    rw [hdyn', hdyn_toNat, h524] at hc
                    omega
                  refine hJ403 8#64 m1 ⟨?_, rfl⟩
                  unfold fullInitDelCap; split <;> first | rfl | omega

end LeanQbe.T.Examples.Kissat.FullM7MemShrink
