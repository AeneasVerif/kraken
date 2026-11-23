module

public import LeanQbe.T.Examples.Kissat.FullM6WatchGcProofWatch
public import LeanQbe.T.Examples.Kissat.FullM6WatchGcProof1b
public import LeanQbe.T.Examples.Kissat.FullM6WatchGcProof2
public import LeanQbe.T.Examples.Kissat.FullDimacsBodyLemmas
public import LeanQbe.T.Examples.Kissat.FullWalkExtLemmas1
public import LeanQbe.T.Examples.Kissat.FullFastCoreLemmas

/-!
# Kissat M6 Watch/GC Proofs Part 3: Remaining 5 Overrides, Closed `ModuleOk`, & UNSAT NV

Proves the remaining `5 / 17` standalone overrides and closes `m6WatchGcModule`:
1. `full_mark_reasons_m6_wp` (`Full.fullMarkReasonsSpec`, skipping level-0 and starting at
   `frame_trail[1]`).
2. `fullFlushTrailSpec` & `full_flush_trail_m6_wp` (`full_backtrack(h, 0)` + `full_propagate(h)`).
3. `m6IngestClSpec` & `full_parse_body_m6_wp` (`Full.fullParseBodySpec`, with parse-time level-0
   unit BCP preserving `fuel` and `oom = 0`).
4. `full_extend_push2_m6_wp` & `full_extend_push_cl_m6_wp` (`Full.fullExtendPush2Spec`,
   `Full.fullExtendPushClSpec`, skipping root-false literals with overflow-safe bounds).
5. Closed `25`-row `m6WatchGcSpecTable`, `m6WatchGc_noExit`, `m6WatchGc_tableImpl`,
   `m6WatchGc_moduleOk`, and concrete `Mem 64` UNSAT soundness (`nv_m6_watch_gc_sound`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6WatchGc

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open FullReduceSpecs FullReduceHelpers
open Kraken.Bedrock2.Test
open scoped FullArenaTactics FullReduceTactics M6Tactics1

/-! ## 1. `full_mark_reasons_m6_wp` (`Full.fullMarkReasonsSpec`) -/

private theorem bv32_div2_lt_of_u64_lt {cv : Nat} {v : BitVec 32}
    (h : (v.toNat : Nat) < cv) : v.toNat < cv := h

theorem full_mark_reasons_m6_wp (Γ : Env) :
    ∀ a m Q X, Full.fullMarkReasonsSpec a m Q X →
      Func.wp Γ full_mark_reasons_m6_body a m Q X := by
  rintro ⟨h, set_flag, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hm, hQ⟩
  have hte_le := hlen.core_ok.trail_end_le
  have hcv_le := hlen.core_ok.cur_vars_le
  have hmax_lt : c.max_vars < 2 * 2 ^ 28 := c.hmaxv
  have hcap_lt : c.arena_cap < 2 * 2 ^ 28 := c.harena
  have hal_le := hlen.core_ok.arena_len_le
  have htrl_len := hlen.core_ok.trl_len
  have hlvl_len := hlen.core_ok.lvl_len
  have hrsns_len := hlen.core_ok.rsns_len
  have hft_len := hlen.core_ok.frame_trail_len
  m6_to_jnz
  refine wp_jnz_of (fun hc => ?_) (fun hc => ?_)
  · have hcl0 : s.core.cur_level = 0 := by
      rw [Arg.val_var, beq_iff_eq] at hc
      have h0 := congrArg BitVec.toNat hc
      have hcl_lt : s.core.cur_level < 2 ^ 64 := by have := hw.cur_level_le; omega
      simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_lt] using h0
    fr_steps
    refine hQ s.core.arena m hlen rfl (fun _ _ => ⟨rfl, rfl, rfl⟩) (fun _ idx hidx => ?_) hw hm
    dsimp only; intro hl_pos _
    exact absurd hl_pos (by
      change ¬ 0 < (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
      exact Nat.not_lt_of_le (hcl0 ▸ hw.lvl_le idx hidx))
  · have hcl_pos : 0 < s.core.cur_level := by
      rw [Arg.val_var, beq_eq_false_iff_ne] at hc
      rcases Nat.eq_zero_or_pos s.core.cur_level with h0 | hpos
      · exact absurd (by simp [h0]) hc
      · exact hpos
    have hft1_lt : 1 < s.core.frame_trail.length := by
      have := hw.cur_level_le
      rw [hft_len]
      omega
    have hft1_le_te : (s.core.frame_trail[1]?.getD 0#32).toNat ≤ s.core.trail_end :=
      hw.frame_trail_lt 1 (by omega)
    have hpre_lv0 : ∀ idx < (s.core.frame_trail[1]?.getD 0#32).toNat,
        0 < (s.core.lvl[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat → False :=
      fun idx hidx hl => by
        have := hw.frame_trail_before_lt 1 (by omega) hcl_pos idx hidx
        omega
    m6_steps
    refine wp_load_of (by
      simpa [Arg.val_var] using FullArenaTactics.load_full_frame_trail (i := 1) hft1_lt hm) ?_
    m6_steps
    refine wp_loop_inv (ts := [i64])
      (fun (i, ()) mL =>
        i.toNat ≤ s.core.trail_end ∧
        ∃ arL : List (BitVec 32), arL.length = c.arena_cap ∧
          let sL : FullState := { s with core := { s.core with arena := arL } }
          FullWitnessInv c F0 F_cur sL.core ∧
          fullArenaClauseRefs sL = fullArenaClauseRefs s ∧
          (∀ r ∈ fullArenaClauseRefs s,
            fullArenaClauseSize sL r = fullArenaClauseSize s r ∧
            fullArenaClauseGarb sL r = fullArenaClauseGarb s r ∧
            fullArenaClauseLits sL r = fullArenaClauseLits s r) ∧
          (set_flag = true → ∀ idx < i.toNat,
            let v := (s.core.trl[idx]?.getD 0#32).toNat / 2
            let rsn := s.core.rsns[v]?.getD 0xFFFFFFFF#32
            0 < (s.core.lvl[v]?.getD 0#32).toNat →
            (rsn &&& 0x80000000#32) = 0#32 →
            (fullArenaHdr sL rsn.toNat &&& 0x00200000#32) ≠ 0#32) ∧
          (FullMem c sL ⋆ R) mL)
      (fun (i, ()) _ => s.core.trail_end - i.toNat) (fun J hLoop => ?_) ?_
    · refine hLoop ((s.core.frame_trail[1]'hft1_lt).setWidth 64, ()) m ?_
      have hstart_eq : ((s.core.frame_trail[1]'hft1_lt).setWidth 64).toNat =
          (s.core.frame_trail[1]?.getD 0#32).toNat := by
        rw [List.getElem?_eq_getElem hft1_lt, Option.getD_some, bv_c0_zext32_64]
      dsimp only
      rw [hstart_eq]
      exact ⟨hft1_le_te, s.core.arena, hlen.core_ok.arena_len_arr, hw, rfl,
        fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ idx hidx hl => absurd hl (hpre_lv0 idx hidx), hm⟩
    · rintro J ⟨i, ⟨⟩⟩ mL ⟨hi_le, arL, harL, hwL, hrefsL, hclL, hmkL, hmL⟩ hLoop
      let sL : FullState := { s with core := { s.core with arena := arL } }
      have hlenL : sL.LengthsOk c := ⟨{ hlen.core_ok with arena_len_arr := harL }, hlen.scratch_ok⟩
      have hdone : i.toNat = s.core.trail_end → Q () mL := fun heq =>
        hQ arL mL hlenL hrefsL hclL (fun hsf idx hidx => hmkL hsf idx (heq ▸ hidx)) hwL hmL
      fr_split
      · have hi_lt : i.toNat < s.core.trail_end := by c0_bound
        have hi_trl : i.toNat < sL.core.trl.length := by dsimp [sL]; rw [htrl_len]; omega
        have hlit_lt : (s.core.trl[i.toNat]'(by omega)).toNat < 2 * s.core.cur_vars := by
          have := hw.trail_lits_lt i.toNat hi_lt
          rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
        have hv_lt : (s.core.trl[i.toNat]'(by omega)).toNat / 2 < s.core.cur_vars := by omega
        have hv_lvl : (s.core.trl[i.toNat]'(by omega)).toNat / 2 < s.core.lvl.length := by omega
        have hv_rsn : (s.core.trl[i.toNat]'(by omega)).toNat / 2 < s.core.rsns.length := by omega
        have hi_next : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
        let vNat : Nat := (s.core.trl[i.toNat]'(by omega)).toNat / 2
        let r32 : BitVec 32 := s.core.rsns[vNat]'hv_rsn
        have hr32_eq : s.core.rsns[(s.core.trl[i.toNat]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
            = r32 := by
          simp [List.getElem?_eq_getElem (by omega : i.toNat < s.core.trl.length),
            List.getElem?_eq_getElem hv_rsn, r32, vNat]
        fr_to_group
        refine wp_join_group (fun () mJ =>
          ∃ ar' : List (BitVec 32), ar'.length = c.arena_cap ∧
            let s' : FullState := { s with core := { s.core with arena := ar' } }
            FullWitnessInv c F0 F_cur s'.core ∧
            fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
            (∀ r ∈ fullArenaClauseRefs s,
              fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
              fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
              fullArenaClauseLits s' r = fullArenaClauseLits s r) ∧
            (set_flag = true → ∀ idx < i.toNat + 1,
              let v := (s.core.trl[idx]?.getD 0#32).toNat / 2
              let rsn := s.core.rsns[v]?.getD 0xFFFFFFFF#32
              0 < (s.core.lvl[v]?.getD 0#32).toNat →
              (rsn &&& 0x80000000#32) = 0#32 →
              (fullArenaHdr s' rsn.toNat &&& 0x00200000#32) ≠ 0#32) ∧
            (FullMem c s' ⋆ R) mJ) ?_ ?_
        · rintro _ ⟨⟩ mJ ⟨ar', har', hw', hrefs', hcl', hmk', hmJ⟩
          fr_steps
          exact hLoop (i + 1#64, ()) mJ (by dsimp only; rw [hi_next]; omega)
            ⟨by rw [hi_next]; omega, ar', har', hw', hrefs', hcl',
             by simpa [hi_next] using hmk', hmJ⟩
        · intro Jj hJj
          have hmem_of_lt : r32.toNat < 0x80000000 →
              r32.toNat ∈ fullArenaClauseRefsCore sL.core := by
            intro hr_lt
            have hr_ne : r32 ≠ 0xFFFFFFFF#32 := fun h => by
              have := congrArg BitVec.toNat h; simp at this; omega
            have hr_lg : (r32 &&& 0x80000000#32) = 0#32 := (bv32_lt_highbit_iff r32).mp hr_lt
            have hri := hwL.reason_inv i.toNat hi_lt (by simpa [sL, hr32_eq] using hr_ne)
            have h1 : sL.core.rsns[(sL.core.trl[i.toNat]?.getD 0#32).toNat / 2]?.getD
                0xFFFFFFFF#32 = r32 := hr32_eq
            rw [h1, ite_eq_right (fun h => h hr_lg)] at hri; exact hri.1
          fr_steps
          · rename_i hv_lt_cv hlvl_pos hr_lt8 hr_le3
            have hr_lt : r32.toNat < 0x80000000 := by
              change (s.core.rsns[vNat]'hv_rsn).toNat < 0x80000000
              simpa [vNat, show (2147483648 : BitVec 32).toNat = 0x80000000 from rfl] using hr_lt8
            have hmem := hmem_of_lt hr_lt
            have hr_al : r32.toNat < arL.length := by
              have := (hwL.arena.refs_wf _ hmem).1; dsimp [sL] at this; omega
            have hbits := bv32_bit21_or_pres (arL[r32.toNat]'hr_al)
            have hhdr_eq : fullArenaHdrCore sL.core r32.toNat = arL[r32.toNat]'hr_al := by
              unfold fullArenaHdrCore; dsimp [sL]
              rw [List.getElem?_eq_getElem hr_al, Option.getD_some]
            obtain ⟨hrefs', hcl', hw'⟩ :=
              setHdrKeepGarbShrk_preserves_witness hlenL.core_ok hwL hmem
              (v := (arL[r32.toNat]'hr_al) ||| 0x00200000#32)
              (by rw [hhdr_eq]; exact hbits.1) (by rw [hhdr_eq]; exact hbits.2.1)
            refine hJj () _ ⟨arL.set r32.toNat ((arL[r32.toNat]'hr_al) ||| 0x00200000#32),
              by simp [harL], hw', hrefs'.trans hrefsL, fun r hr => ?_, fun _ idx hidx => ?_, hm⟩
            · have hrL : r ∈ fullArenaClauseRefsCore sL.core := by
                change r ∈ fullArenaClauseRefs sL; rw [hrefsL]; exact hr
              have h1 := hcl' r hrL; have h2 := hclL r hr
              exact ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩
            · dsimp only; intro hlpos hrlg
              by_cases hidx_eq : idx = i.toNat
              · subst hidx_eq; rw [hr32_eq]
                unfold fullArenaHdr fullArenaHdrCore; dsimp only
                rw [List.getElem?_set_self hr_al, Option.getD_some]; exact hbits.2.2
              · have hprev := hmkL hc idx (by omega) hlpos hrlg
                let rsn_i :=
                  s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32
                by_cases hre : rsn_i.toNat = r32.toNat
                · unfold fullArenaHdr fullArenaHdrCore; dsimp only
                  rw [show (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
                      0xFFFFFFFF#32).toNat = r32.toNat from hre,
                    List.getElem?_set_self hr_al, Option.getD_some]
                  exact hbits.2.2
                · unfold fullArenaHdr fullArenaHdrCore at hprev ⊢; dsimp only at hprev ⊢
                  rw [List.getElem?_set_ne (Ne.symm hre)]; exact hprev
          · rename_i hv_lt_cv hlvl_pos hr_lt8 hr_le3
            have hr_lt : r32.toNat < 0x80000000 := by
              change (s.core.rsns[vNat]'hv_rsn).toNat < 0x80000000
              simpa [vNat, show (2147483648 : BitVec 32).toNat = 0x80000000 from rfl] using hr_lt8
            have hmem := hmem_of_lt hr_lt
            have hr_al : r32.toNat < arL.length := by
              have := (hwL.arena.refs_wf _ hmem).1; dsimp [sL] at this; omega
            have hbits := bv32_bit21_clear_pres (arL[r32.toNat]'hr_al)
            have hhdr_eq : fullArenaHdrCore sL.core r32.toNat = arL[r32.toNat]'hr_al := by
              unfold fullArenaHdrCore; dsimp [sL]
              rw [List.getElem?_eq_getElem hr_al, Option.getD_some]
            obtain ⟨hrefs', hcl', hw'⟩ :=
              setHdrKeepGarbShrk_preserves_witness hlenL.core_ok hwL hmem
              (v := (arL[r32.toNat]'hr_al) &&& ~~~0x00200000#32)
              (by rw [hhdr_eq]; exact hbits.1) (by rw [hhdr_eq]; exact hbits.2)
            refine hJj () _ ⟨arL.set r32.toNat ((arL[r32.toNat]'hr_al) &&& ~~~0x00200000#32),
              by simp [harL], hw', hrefs'.trans hrefsL, fun r hr => ?_,
              fun h => by simp [h] at hc, hm⟩
            have hrL : r ∈ fullArenaClauseRefsCore sL.core := by
              change r ∈ fullArenaClauseRefs sL; rw [hrefsL]; exact hr
            have h1 := hcl' r hrL; have h2 := hclL r hr
            exact ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩
          · rename_i hv_lt_cv hlvl_pos hr_lt8
            have hr_lt : r32.toNat < 0x80000000 := by
              change (s.core.rsns[vNat]'hv_rsn).toNat < 0x80000000
              simpa [vNat, show (2147483648 : BitVec 32).toNat = 0x80000000 from rfl] using hr_lt8
            have hmem := hmem_of_lt hr_lt
            have hwf3 := (hwL.arena.refs_wf _ hmem).1
            dsimp [sL] at hwf3
            have hnot3 : ¬ (r32.toNat + 3) % 2 ^ 64 ≤ s.core.arena_len % 2 ^ 64 := by
              simpa [r32, vNat, show (3 : BitVec 64).toNat = 3 from rfl] using hc
            omega
          · rename_i hv_lt_cv hlvl_pos
            refine hJj () mL ⟨arL, harL, hwL, hrefsL, hclL, fun hsf idx hidx => ?_, hmL⟩
            by_cases hidx_eq : idx = i.toNat
            · subst hidx_eq; dsimp only; intro _ hrlg
              rw [hr32_eq] at hrlg
              have hlt := (bv32_lt_highbit_iff r32).mpr hrlg
              have hge : ¬ r32.toNat < 0x80000000 := by
                simpa [r32, vNat, show (2147483648 : BitVec 32).toNat = 0x80000000 from rfl]
                  using hc
              exact False.elim (hge hlt)
            · exact hmkL hsf idx (by omega)
          · rename_i hv_lt_cv
            refine hJj () mL ⟨arL, harL, hwL, hrefsL, hclL, fun hsf idx hidx => ?_, hmL⟩
            by_cases hidx_eq : idx = i.toNat
            · subst hidx_eq; dsimp only; intro hlpos _
              have h1 : (s.core.lvl[(s.core.trl[i.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
                  = (s.core.lvl[vNat]'hv_lvl).toNat := by
                simp [List.getElem?_eq_getElem (by omega : i.toNat < s.core.trl.length),
                  List.getElem?_eq_getElem hv_lvl, vNat]
              have hnot : ¬ (0 < (s.core.lvl[vNat]'hv_lvl).toNat) := by
                simpa [vNat, show (0 : BitVec 32).toNat = 0 from rfl] using hc
              rw [h1] at hlpos; exact False.elim (hnot hlpos)
            · exact hmkL hsf idx (by omega)
      · fr_steps; exact hdone (by c0_bound)

/-! ## 2. `fullFlushTrailSpec` & `full_flush_trail_m6_wp` (`full_flush_trail_m6`) -/

/-- Specification contract for `full_flush_trail_m6(h)`:
if inconsistent returns `20#64` (`F0.Unsat`); else backtracks to level 0 and propagates, returning
`20#64` on level-0 conflict (`F0.Unsat`), `0#64` on resource/OOM interruption, or `1#64` with
`cur_level = 0`, `unflushed = 0#64`, and `propagated = trail_end`. -/
def fullFlushTrailSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    s.core.dense_mode = 0#64 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      s'.core.dense_mode = 0#64 → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → s'.core.cur_level = 0 ∧ s'.core.unflushed = 0#64 ∧
        s'.core.propagated = s'.core.trail_end) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

private theorem level0_cur_unsat_of_conflict_okW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core)
    (hl0 : s.core.cur_level = 0) (hc : FullConflictOkW F_cur s) :
    (cnfOfClauses F_cur).Unsat := by
  rcases hc with ⟨_, h0lt, h1lt, hf0, hf1, hent⟩ | ⟨_, href, hng, hfals⟩
  · refine unsat_of_entails_nil (entails_of_mem_or_false hent fun l hl => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    right; rcases hl with rfl | rfl
    · obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff _ h0lt).mp hf0
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega)
      rwa [heq] at hs
    · obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff _ h1lt).mp hf1
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega)
      rwa [heq] at hs
  · refine unsat_of_entails_nil
      (entails_of_mem_or_false (hw.arena.entails _ href hng) fun l hl => ?_)
    right
    have hlt := hw.arena.lits_lt _ href hng l hl
    obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hlt).mp (hfals l hl)
    have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega)
    rwa [heq] at hs

private theorem fullWitnessInv_with_inconsistent {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (huns : (cnfOfClauses F_cur).Unsat) :
    FullWitnessInv c F0 F_cur { k with inconsistent := 1#64 } :=
  { hw with
    inconsistent_sound := fun _ => huns
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

private theorem fullWitnessInv_with_unflushed {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) :
    FullWitnessInv c F0 F_cur { k with unflushed := 0#64 } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

theorem full_flush_trail_m6_wp (Γ : Env)
    (hBack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hProp : ∀ a m Q X, Full.fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X) :
    ∀ a m Q X, fullFlushTrailSpec a m Q X → Func.wp Γ full_flush_trail_m6_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hdm0, hm, hQ⟩
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv_le := hlen.core_ok.cur_vars_le
  have hte_le := hlen.core_ok.trail_end_le
  have hcl_le := hw.cur_level_le
  have hcl_lt : s.core.cur_level < 2 ^ 64 := by omega
  m6_to_jnz; apply wp_jnz_of <;> intro hc
  · have hinc_ne : s.core.inconsistent ≠ 0#64 := by
      rw [Arg.val_var, bne_iff_ne] at hc; exact hc
    m6_c0_steps
    exact hQ 20#64 s m hlen hw hdm0 rfl (Nat.le_refl _) (Or.inr (Or.inr rfl))
      (fun _ => hw.ext_sound.2 (hw.inconsistent_sound hinc_ne)) (fun h => by cases h) hm
  · clear hc
    m6_to_group
    refine wp_join_group (fun () m1 => ∃ s1 : FullState,
      s1.LengthsOk c ∧ FullWitnessInv c F0 F_cur s1.core ∧
      s1.core.cur_level = 0 ∧ s1.core.dense_mode = 0#64 ∧
      s1.core.cur_vars = s.core.cur_vars ∧ s1.core.fuel = s.core.fuel ∧
      (FullMem c s1 ⋆ R) m1) ?_ ?_
    · rintro _ ⟨⟩ m1 ⟨s1, hlen1, hw1, hcl1, hdm1, hcv1, hfu1, hm1⟩
      clear hm hw hlen
      m6_steps; c0_call hProp
      refine ⟨c, F0, F_cur, s1, R, rfl, hlen1, hw1, hdm1, hm1, ?_⟩
      intro r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen'
        wu' fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' m' s2_d hlen2 hw2 htr2 hperm2
        hfu2 hr hr0 hr1 hr2 hnoop hm2
      let s2 : FullState :=
        { s1 with
          core := { s1.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                 trl := trl', trail_pos := tp', trail_end := te',
                                 propagated := prop', unassigned := unass', unflushed := unfl',
                                 wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
                                 wusable := wu', fuel := fuel', confl_type := ctype',
                                 confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1',
                                 oom := oom' }
          scratch := { s1.scratch with search_ticks := ticks', wsort := wsort',
                                       phases := phases' } }
      have hfu_le : s2.core.fuel.toNat ≤ s.core.fuel.toNat := by
        dsimp [s2]; rw [← hfu1]; exact hfu2
      m6_to_jnz; apply wp_jnz_of <;> intro hc1
      · have hr_eq1 : r = 1#64 := by simpa [Arg.val_var] using hc1
        clear hc1
        m6_c0_steps
        have hcur_uns := level0_cur_unsat_of_conflict_okW hw2 hcl1 (hr1 hr_eq1).2.2
        have hw2' := fullWitnessInv_with_inconsistent hw2 hcur_uns
        have hlen2' : ({ s2 with core := { s2.core with inconsistent := 1#64 } } :
            FullState).LengthsOk c :=
          ⟨{ hlen2.core_ok with vals_len := hlen2.core_ok.vals_len }, hlen2.scratch_ok⟩
        refine hQ 20#64 _ _ hlen2' hw2' hdm1 hcv1 hfu_le (Or.inr (Or.inr rfl))
          (fun _ => hw2.ext_sound.2 hcur_uns) (fun h => by cases h) ?_
        assumption
      · have hr_ne1 : r ≠ 1#64 := by simpa [Arg.val_var] using hc1
        clear hc1
        m6_to_jnz; apply wp_jnz_of <;> intro hc0
        · have hr_ne0 : r ≠ 0#64 := by simpa [Arg.val_var, bne_iff_ne] using hc0
          clear hc0
          m6_c0_steps
          exact hQ 0#64 s2 m' hlen2 hw2 hdm1 hcv1 hfu_le (Or.inl rfl)
            (fun h => by cases h) (fun h => by cases h) hm2
        · have hr_eq0 : r = 0#64 := by simpa [Arg.val_var, bne_eq_false_iff_eq] using hc0
          clear hc0
          m6_c0_steps
          have hw2' := fullWitnessInv_with_unflushed hw2
          have hlen2' : ({ s2 with core := { s2.core with unflushed := 0#64 } } :
              FullState).LengthsOk c :=
            ⟨{ hlen2.core_ok with vals_len := hlen2.core_ok.vals_len }, hlen2.scratch_ok⟩
          refine hQ 1#64 _ _ hlen2' hw2' hdm1 hcv1 hfu_le (Or.inr (Or.inl rfl))
            (fun h => by cases h) (fun _ => ⟨hcl1, rfl, (hr0 hr_eq0).1⟩) ?_
          assumption
    · intro J hJ; m6_to_jnz; apply wp_jnz_of <;> intro hc_cl
      · have hcl_pos : 0 < s.core.cur_level := by
          rw [Arg.val_var, BitVec.ult, decide_eq_true_eq] at hc_cl
          have : (0#64 : BitVec 64).toNat = 0 := rfl
          simpa [this, Nat.mod_eq_of_lt hcl_lt] using hc_cl
        clear hc_cl
        m6_steps; c0_call hBack
        refine ⟨c, s, R, rfl, hlen, hcl_lt,
          fun _ => by change 0 < c.max_vars; omega,
          hw.trail_lits_lt, hm, ?_⟩
        intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m1 s1_d hlen1 _ _ hcl1
          _ _ _ _ hw1 _ hm1
        let s1 : FullState :=
          { s with
            core := { s.core with vals := vals', lvl := lvl', rsns := rsns', trl := trl',
                                  trail_pos := tp', trail_end := te', propagated := prop',
                                  cur_level := cl', unassigned := unass' }
            scratch := sc' }
        have hcl_z : cl' = 0 := by
          change cl' = min s.core.cur_level 0 at hcl1; simpa using hcl1
        m6_c0_steps
        exact hJ () m1 ⟨s1, hlen1, hw1 _ _ hw (Nat.zero_le _), hcl_z, hdm0, rfl, rfl, hm1⟩
      · have hcl0 : s.core.cur_level = 0 := by
          rw [Arg.val_var, BitVec.ult, decide_eq_false_iff_not,
            BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcl_lt] at hc_cl
          change ¬ 0 < s.core.cur_level at hc_cl
          omega
        clear hc_cl
        m6_c0_steps
        exact hJ () m ⟨s, hlen, hw, hcl0, hdm0, rfl, rfl, hm⟩

/-! ## 3. `m6IngestClSpec` & `full_parse_body_m6_wp` (`full_parse_body_m6`) -/

/-- Exact extension of `Full.fullIngestClSpec` exposing `arena_len` and `num_binary` preservation
when ingesting a level-0 unit clause (`l < 2 * c.mv`), so `full_parse_body_m6` triggers parse-time
unit BCP only after at least one non-unit clause has been added to `arena` or `wvec`. -/
def m6IngestClSpec : Spec [i64, i64] [i64] := fun (h, cend, ()) m Q _ =>
  ∃ (c : FullCfg) (accCnf : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (cnf_ptr : BitVec 64) (cnfBytes : List UInt8) (i0 : Nat) (R : Mem 64 → Prop),
    h = c.hdr ∧ cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧ i0 ≤ cnfBytes.length ∧
    s.core.cur_vars = c.mv ∧ s.core.d_cur = cnf_ptr + BitVec.ofNat 64 i0 ∧
    s.core.cur_level = 0 ∧ FullSparseInvW c (shiftDownCnf accCnf) F_cur s ∧
    (shiftDownCnf accCnf).Entails (cnfOfClauses F_cur) ∧
    (bytes cnf_ptr cnfBytes ⋆ FullMem c s ⋆ R) m ∧
    match parseClause c.mv (cnfBytes.drop i0) with
    | none =>
      ∀ s' m', s'.LengthsOk c → s'.core.fuel = s.core.fuel → s'.core.oom = s.core.oom →
        s'.core.probing = s.core.probing →
        (bytes cnf_ptr cnfBytes ⋆ FullMem c s' ⋆ R) m' → Q (0#64, ()) m'
    | some (cl, rest) =>
      ∀ r s' j m',
        (∀ lit ∈ cl.literals, 1 ≤ lit.1) →
        i0 < j → j ≤ cnfBytes.length → cnfBytes.drop j = rest →
        s'.LengthsOk c → s'.core.cur_vars = c.mv →
        s'.core.d_cur = cnf_ptr + BitVec.ofNat 64 j →
        s'.core.cur_level = 0 → s'.core.fuel = s.core.fuel → s'.core.oom = s.core.oom →
        s'.core.probing = s.core.probing →
        (r = 1#64 ∨ r = 2#64 ∨ r = 3#64) →
        (r = 1#64 → ∃ F_cur', FullSparseInvW c (shiftDownCnf (accCnf.add cl)) F_cur' s' ∧
          (shiftDownCnf (accCnf.add cl)).Entails (cnfOfClauses F_cur')) →
        (r = 2#64 → (shiftDownCnf (accCnf.add cl)).Unsat) →
        (∀ l < 2 * c.mv, cl = CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l] →
          s.core.vals[l]?.getD 0#8 = 0#8 →
          r = 1#64 ∧
          (∀ k < 2 * c.mv, s'.core.vals[k]?.getD 0#8 =
            ((s.core.vals.set l 1#8).set (l ^^^ 1) 0xFF#8)[k]?.getD 0#8) ∧
          s'.core.trail_end = s.core.trail_end + 1 ∧ s'.core.propagated = s.core.propagated ∧
          s'.core.arena_len = s.core.arena_len ∧ s'.core.num_binary = s.core.num_binary) →
        (∀ l < 2 * c.mv, cl = CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l] →
          s.core.vals[l]?.getD 0#8 = 0xFF#8 → r = 2#64) →
        (bytes cnf_ptr cnfBytes ⋆ FullMem c s' ⋆ R) m' → Q (r, ()) m'

theorem m6IngestClSpec_to_full {a m Q X}
    (h : Full.fullIngestClSpec a m Q X) : m6IngestClSpec a m Q X := by
  rcases h with ⟨c, accCnf, F_cur, s, cnf_ptr, cnfBytes, i0, R,
    hh, hce, hfit, hi0, hcv, hdc, hcl, hinv, hent, hm, hrest⟩
  refine ⟨c, accCnf, F_cur, s, cnf_ptr, cnfBytes, i0, R,
    hh, hce, hfit, hi0, hcv, hdc, hcl, hinv, hent, hm, ?_⟩
  cases hpc : parseClause c.mv (cnfBytes.drop i0) with
  | none =>
    simp only [hpc] at hrest ⊢
    exact hrest
  | some p =>
    simp only [hpc] at hrest ⊢
    intro r s' j m' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hr hok huns hunit hfl hm'
    exact hrest r s' j m' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hr hok huns
      (fun l hl hcl hv => let ⟨a1, a2, a3, a4, _, _⟩ := hunit l hl hcl hv; ⟨a1, a2, a3, a4⟩)
      hfl hm'

private theorem m6_full_mem_to_dimacs {c : FullCfg} {s : FullState} {cnf_ptr : BitVec 64}
    {cnfBytes : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (bytes cnf_ptr cnfBytes ⋆ FullMem c s ⋆ R) m) :
    (bytes cnf_ptr cnfBytes ⋆
      dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
      (FullRest c s ⋆ R)) m := by
  have h1 := focus_dimacs (sep_ac h : (FullMem c s ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m)
  exact sep_ac h1

private theorem m6_full_dimacs_to_mem {c : FullCfg} {s : FullState} {cur' val' cnf_ptr : BitVec 64}
    {cnfBytes : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (bytes cnf_ptr cnfBytes ⋆
      dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) cur' val' ⋆
      (FullRest c s ⋆ R)) m) :
    (bytes cnf_ptr cnfBytes ⋆
      FullMem c { s with core := { s.core with d_cur := cur', d_val := val' } } ⋆ R) m :=
  sep_ac (unfocus_dimacs (R := bytes cnf_ptr cnfBytes ⋆ R) (sep_ac h))

private theorem m6_unitUnsatTrace_congr_vals {mv : Nat} :
    ∀ {bs : List UInt8} {n : Nat} {v1 v2 : List (BitVec 8)},
      2 * mv ≤ v1.length → 2 * mv ≤ v2.length →
      (∀ k < 2 * mv, v1[k]?.getD 0#8 = v2[k]?.getD 0#8) →
      UnitUnsatTrace mv v1 bs n → UnitUnsatTrace mv v2 bs n := by
  intro bs n v1 v2 hlen1 hlen2 hcongr hut
  induction hut generalizing v2 with
  | @conflict vals bs l rest k hl hpc hvf hrest =>
    exact .conflict hl hpc (by rw [← hcongr l hl]; exact hvf) hrest
  | @step vals bs l rest k hl hpc hv0 _ ih =>
    have hln_lt : l ^^^ 1 < 2 * mv := litNeg_lt_two_mul hl
    refine .step hl hpc (by rw [← hcongr l hl]; exact hv0)
      (ih (by simp [hlen1]) (by simp [hlen2]) fun m hm => ?_)
    by_cases hm2 : m = l ^^^ 1
    · subst hm2
      rw [List.getElem?_set_self (by simp; omega), List.getElem?_set_self (by simp; omega)]
    · rw [List.getElem?_set_ne (Ne.symm hm2), List.getElem?_set_ne (Ne.symm hm2)]
      by_cases hm1 : m = l
      · subst hm1; rw [List.getElem?_set_self (by omega), List.getElem?_set_self (by omega)]
      · rw [List.getElem?_set_ne (Ne.symm hm1), List.getElem?_set_ne (Ne.symm hm1)]
        exact hcongr m hm

private theorem m6_full_init_sparseW {c : FullCfg} {s : FullState}
    (hinv0 : Full.FullSparseInv c (shiftDownCnf CNF.empty) s)
    (hcv0 : s.core.cur_vars = c.mv) (hal0 : s.core.arena_len = 0)
    (hte0 : s.core.trail_end = 0) (hcl0 : s.core.cur_level = 0)
    (hinc0 : s.core.inconsistent = 0#64)
    (hvals0 : s.core.vals = List.replicate (2 * c.max_vars) 0#8)
    (hwvec0 : s.core.wvec = List.replicate (4 * c.max_vars) 0#32) :
    Full.FullSparseInvW c (shiftDownCnf CNF.empty) [] s ∧
      (shiftDownCnf CNF.empty).Entails (cnfOfClauses []) := by
  obtain ⟨F_init, hw_init⟩ := hinv0.1.witness
  have hft0 : (s.core.frame_trail[0]?.getD 0#32).toNat = 0 := by
    have := hw_init.frame_trail_lt 0 (by omega); omega
  have hcmv : s.core.cur_vars ≤ c.max_vars := hinv0.1.lengths.core_ok.cur_vars_le
  have hext : ExtUnsatSound (shiftDownCnf CNF.empty) s.core.cur_vars [] :=
    ⟨(fun _ hc => nomatch hc), fun hu => by
      rw [CNF.unsat_iff_not_sat] at hu
      exact False.elim (hu (fun _ => false)
        ((cnf_sat_cnfOfClauses_iff (fun _ => false) []).mpr fun _ hc => by cases hc))⟩
  have hw0 : ∀ l < 2 * s.core.cur_vars,
      fullWatchOffCore s.core l = 0 ∧ fullWatchSizeCore s.core l = 0 := fun l hl => by
    unfold fullWatchOffCore fullWatchSizeCore; rw [hwvec0]
    simp [show 2 * l < 4 * c.max_vars by omega, show 2 * l + 1 < 4 * c.max_vars by omega]
  have hv0 : ∀ l < 2 * s.core.cur_vars, s.core.vals[l]?.getD 0#8 = 0#8 := fun l hl => by
    rw [hvals0]; simp [show l < 2 * c.max_vars by omega]
  have hw_empty := fullWitnessInv_empty (c := c) hext hinc0 hal0 hw0 hte0 hcl0 hft0 hv0
  refine ⟨⟨hinv0.1.lengths, hw_empty, hinv0.2.1, hinv0.2.2.1, hinv0.2.2.2.1, hinv0.2.2.2.2⟩, ?_⟩
  rw [CNF.entails_def]
  intro α _; exact (cnf_sat_cnfOfClauses_iff α []).mpr fun _ hc => by cases hc

private structure M6ParseBodyInv (c : FullCfg) (s : FullState) (cnf_ptr : BitVec 64)
    (cnfBytes : List UInt8) (i0 i idx : Nat) (accCnf : CNF Nat) (unsat oom : Bool)
    (st : FullState) : Prop where
  i_le : i ≤ c.nc
  idx_le : idx ≤ cnfBytes.length
  cv_eq : st.core.cur_vars = c.mv
  d_cur_eq : st.core.d_cur = cnf_ptr + BitVec.ofNat 64 idx
  len_ok : st.LengthsOk c
  cl0 : st.core.cur_level = 0
  fuel_eq : st.core.fuel = s.core.fuel
  oom_eq : st.core.oom = 0#64
  prb_eq : st.core.probing = 0#64
  vars_pos : CnfVarsPos accCnf
  pc_eq : parseClauses c.mv (c.nc - i) accCnf (cnfBytes.drop idx) = parseDimacs cnfBytes
  uns_inv : unsat = true → (shiftDownCnf accCnf).Unsat
  ok_inv : unsat = false → oom = false →
    ∃ F_cur, Full.FullSparseInvW c (shiftDownCnf accCnf) F_cur st ∧
      (shiftDownCnf accCnf).Entails (cnfOfClauses F_cur)
  uns_tr : UnitUnsatTrace c.mv (s.core.vals.take (2 * c.mv)) (cnfBytes.drop i0) c.nc →
    oom = false ∧
    ((unsat = false ∧ st.core.arena_len = 0 ∧ st.core.num_binary = s.core.num_binary ∧
      UnitUnsatTrace c.mv st.core.vals (cnfBytes.drop idx) (c.nc - i)) ∨
     (unsat = true ∧ ∃ cnf, parseClauses c.mv (c.nc - i) CNF.empty (cnfBytes.drop idx) = some cnf))

private theorem m6_parse_body_skip_step {c : FullCfg} {s st st' : FullState}
    {cnf_ptr : BitVec 64} {cnfBytes rest : List UInt8} {i0 i idx j : Nat} {accCnf : CNF Nat}
    {oom : Bool} {cl : CNF.Clause Nat}
    (hp : M6ParseBodyInv c s cnf_ptr cnfBytes i0 i idx accCnf true oom st)
    (hi : i < c.nc) (hpc1 : parseClause c.mv (cnfBytes.drop idx) = some (cl, rest))
    (hcl_pos : ∀ lit ∈ cl.literals, 1 ≤ lit.1) (hj : j ≤ cnfBytes.length)
    (hdrop : cnfBytes.drop j = rest)
    (hst' : st' = { st with core := { st.core with d_cur := cnf_ptr + BitVec.ofNat 64 j,
                                                   d_val := 0#64 } }) :
    M6ParseBodyInv c s cnf_ptr cnfBytes i0 (i + 1) j (accCnf.add cl) true oom st' := by
  have hsub : c.nc - i = (c.nc - (i + 1)) + 1 := by omega
  refine ⟨by omega, hj, by rw [hst']; exact hp.cv_eq, by rw [hst'],
    by rw [hst']; exact ⟨{ hp.len_ok.core_ok with vals_len := hp.len_ok.core_ok.vals_len },
      hp.len_ok.scratch_ok⟩,
    by rw [hst']; exact hp.cl0, by rw [hst']; exact hp.fuel_eq, by rw [hst']; exact hp.oom_eq,
    by rw [hst']; exact hp.prb_eq, cnfVarsPos_add hp.vars_pos hcl_pos,
    by rw [← hp.pc_eq, hsub, parseClauses, hpc1, ← hdrop]; rfl,
    (fun _ => by rw [shiftDownCnf_add]; exact cnf_unsat_add (hp.uns_inv rfl)),
    (fun hc => by cases hc),
    (fun hut => by
      obtain ⟨hoom, hdisj⟩ := hp.uns_tr hut; refine ⟨hoom, Or.inr ⟨rfl, ?_⟩⟩
      rcases hdisj with ⟨hf, _⟩ | ⟨_, cnf_r, hr⟩
      · cases hf
      · rw [hsub, parseClauses, hpc1, ← hdrop] at hr; exact parseClauses_some_of_acc hr)⟩

private theorem m6_parse_body_ingest_step {c : FullCfg} {s st st' : FullState}
    {cnf_ptr : BitVec 64} {cnfBytes rest : List UInt8} {i0 i idx j : Nat} {accCnf : CNF Nat}
    {r_in : BitVec 64} {cl : CNF.Clause Nat}
    (hp : M6ParseBodyInv c s cnf_ptr cnfBytes i0 i idx accCnf false false st)
    (hi : i < c.nc) (hpc1 : parseClause c.mv (cnfBytes.drop idx) = some (cl, rest))
    (hcl_pos : ∀ lit ∈ cl.literals, 1 ≤ lit.1) (hj : j ≤ cnfBytes.length)
    (hdrop : cnfBytes.drop j = rest) (hlen' : st'.LengthsOk c) (hcv' : st'.core.cur_vars = c.mv)
    (hd' : st'.core.d_cur = cnf_ptr + BitVec.ofNat 64 j) (hcl' : st'.core.cur_level = 0)
    (hfu' : st'.core.fuel = st.core.fuel) (hoom' : st'.core.oom = st.core.oom)
    (hprb' : st'.core.probing = st.core.probing)
    (hr_dom : r_in = 1#64 ∨ r_in = 2#64 ∨ r_in = 3#64)
    (hok_in : r_in = 1#64 →
      ∃ F_cur', Full.FullSparseInvW c (shiftDownCnf (accCnf.add cl)) F_cur' st' ∧
        (shiftDownCnf (accCnf.add cl)).Entails (cnfOfClauses F_cur'))
    (huns_in : r_in = 2#64 → (shiftDownCnf (accCnf.add cl)).Unsat)
    (hunit_ok : ∀ l < 2 * c.mv, cl = CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l] →
      st.core.vals[l]?.getD 0#8 = 0#8 → r_in = 1#64 ∧
      (∀ k < 2 * c.mv, st'.core.vals[k]?.getD 0#8 =
        ((st.core.vals.set l 1#8).set (l ^^^ 1) 0xFF#8)[k]?.getD 0#8) ∧
      st'.core.trail_end = st.core.trail_end + 1 ∧ st'.core.propagated = st.core.propagated ∧
      st'.core.arena_len = st.core.arena_len ∧ st'.core.num_binary = st.core.num_binary)
    (hunit_fl : ∀ l < 2 * c.mv, cl = CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l] →
      st.core.vals[l]?.getD 0#8 = 0xFF#8 → r_in = 2#64) :
    M6ParseBodyInv c s cnf_ptr cnfBytes i0 (i + 1) j (accCnf.add cl)
      (decide (r_in = 2#64)) (decide (r_in = 3#64)) st' := by
  have hsub : c.nc - i = (c.nc - (i + 1)) + 1 := by omega
  have hpc_next : parseClauses c.mv (c.nc - (i + 1)) (accCnf.add cl) (cnfBytes.drop j) =
      parseDimacs cnfBytes := by rw [← hp.pc_eq, hsub, parseClauses, hpc1, ← hdrop]; rfl
  have hcmv_st : c.mv ≤ c.max_vars := hp.cv_eq ▸ hp.len_ok.core_ok.cur_vars_le
  have hcmv_st' : c.mv ≤ c.max_vars := hcv' ▸ hlen'.core_ok.cur_vars_le
  rcases hr_dom with rfl | rfl | rfl <;>
    refine ⟨by omega, hj, hcv', hd', hlen', hcl', hfu'.trans hp.fuel_eq, hoom'.trans hp.oom_eq,
      hprb'.trans hp.prb_eq, cnfVarsPos_add hp.vars_pos hcl_pos, hpc_next, ?_, ?_, ?_⟩
  · exact fun hc => by cases hc
  · exact fun _ _ => hok_in rfl
  · intro hut; refine ⟨rfl, Or.inl ?_⟩
    rcases (hp.uns_tr hut).2 with ⟨_, hal0, hnb0, htr⟩ | ⟨ht, _⟩
    · rw [hsub] at htr; cases htr with
      | conflict hl hpc_s hvf _ =>
        rw [hpc1] at hpc_s; rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
        have hr2 := hunit_fl _ hl hcl_eq hvf; cases hr2
      | step hl hpc_s hv0 htr_next =>
        rw [hpc1] at hpc_s; rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, hreq⟩
        obtain ⟨_, hvs, _, _, hal', hnb'⟩ := hunit_ok _ hl hcl_eq hv0
        refine ⟨rfl, hal'.trans hal0, hnb'.trans hnb0, ?_⟩
        rw [hdrop, hreq]
        exact m6_unitUnsatTrace_congr_vals
          (by simp [hp.len_ok.core_ok.vals_len]; omega)
          (by rw [hlen'.core_ok.vals_len]; omega)
          (fun k hk => (hvs k hk).symm) htr_next
    · cases ht
  · exact fun _ => huns_in rfl
  · exact fun hc => by cases hc
  · intro hut; refine ⟨rfl, Or.inr ⟨rfl, ?_⟩⟩
    rcases (hp.uns_tr hut).2 with ⟨_, _, _, htr⟩ | ⟨ht, _⟩
    · rw [hsub] at htr; cases htr with
      | conflict _ hpc_s _ hrest =>
        rw [hpc1] at hpc_s; rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨_, hreq⟩
        rwa [hdrop, hreq]
      | step hl hpc_s hv0 _ =>
        rw [hpc1] at hpc_s; rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
        exact absurd (hunit_ok _ hl hcl_eq hv0).1 (by decide)
    · cases ht
  · exact fun hc => by cases hc
  · exact fun _ hc => by cases hc
  · intro hut; rcases (hp.uns_tr hut).2 with ⟨_, _, _, htr⟩ | ⟨ht, _⟩
    · rw [hsub] at htr; cases htr with
      | conflict hl hpc_s hvf _ =>
        rw [hpc1] at hpc_s; rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
        exact absurd (hunit_fl _ hl hcl_eq hvf) (by decide)
      | step hl hpc_s hv0 _ =>
        rw [hpc1] at hpc_s; rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
        exact absurd (hunit_ok _ hl hcl_eq hv0).1 (by decide)
    · cases ht

private theorem full_sparse_invW_of_propagate {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s2 : FullState}
    (hsp : Full.FullSparseInvW c F0 F_cur s)
    (hlen2 : s2.LengthsOk c) (hw2 : FullWitnessInv c F0 F_cur s2.core)
    (hperm : FullArenaPermEq s.core s2.core)
    (hll : s2.scratch.last_learned = s.scratch.last_learned)
    (hel : s2.scratch.extend_len = s.scratch.extend_len)
    (hlm : s2.core.lit_mark = s.core.lit_mark)
    (hmrk : s2.core.mrk = s.core.mrk)
    (hdm : s2.core.dense_mode = 0#64) :
    Full.FullSparseInvW c F0 F_cur s2 := by
  have hnd2 : Full.FullArenaVarsNodup s2 := by
    intro r hr hng
    have hr1 : r ∈ fullArenaClauseRefsCore s.core := by
      rw [← hperm.2.1]; exact hr
    have h1 := hperm.2.2 r hr1
    have hng1 : fullArenaClauseGarb s r = false := by
      unfold fullArenaClauseGarb; rw [← h1.2.1]; exact hng
    exact (List.Perm.map (· / 2) h1.2.2).nodup_iff.mpr (hsp.2.2.2.1 r hr1 hng1)
  have hll2 : Full.FullLastLearnedWf s2 := by
    intro i hi; dsimp only; rw [hll]
    exact (hsp.2.2.2.2.1.1 i hi).elim Or.inl fun hr =>
      Or.inr (by show _ ∈ fullArenaClauseRefsCore s2.core; rw [hperm.2.1]; exact hr)
  refine ⟨hlen2, hw2, ⟨fun v hv => by rw [hmrk]; exact hsp.2.2.1.1 v hv,
      fun l hl => by rw [hlm]; exact hsp.2.2.1.2 l hl⟩,
    hnd2, ⟨hll2, hel ▸ hsp.2.2.2.2.1.2⟩, hdm⟩

private theorem m6_parse_body_oom_exit {c : FullCfg} {s st : FullState}
    {cnf_ptr : BitVec 64} {cnfBytes : List UInt8} {i0 i idx : Nat} {accCnf : CNF Nat}
    {unsat_v : Bool} {R : Mem 64 → Prop} {ml : Mem 64} {Q : Post [i64]}
    (hp : M6ParseBodyInv c s cnf_ptr cnfBytes i0 i idx accCnf unsat_v true st)
    (hml : (bytes cnf_ptr cnfBytes ⋆ FullMem c st ⋆ R) ml)
    (hQ : ∀ r st' m', st'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      st'.core.fuel = s.core.fuel → st'.core.oom = 0#64 → st'.core.probing = 0#64 →
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
      (r = 1#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
        Full.FullSparseInv c (shiftDownCnf cnf) st' ∧ st'.core.cur_level = 0) →
      (UnitUnsatTrace c.mv (s.core.vals.take (2 * c.mv)) (cnfBytes.drop i0) c.nc → r = 20#64) →
      (bytes cnf_ptr cnfBytes ⋆ FullMem c st' ⋆ R) m' → Q (r, ()) m') : Q (0#64, ()) ml :=
  hQ 0#64 st ml hp.len_ok (Or.inl rfl) hp.fuel_eq hp.oom_eq hp.prb_eq
    (fun h => by cases h) (fun h => by cases h)
    (fun hut => by cases (hp.uns_tr hut).1) hml

private theorem m6_parse_body_eof_ne {c : FullCfg} {s st : FullState}
    {cnf_ptr : BitVec 64} {cnfBytes : List UInt8} {i0 idx j : Nat} {accCnf : CNF Nat}
    {unsat_v oom_v : Bool} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hp : M6ParseBodyInv c s cnf_ptr cnfBytes i0 c.nc idx accCnf unsat_v oom_v st)
    (_hidx : idx ≤ cnfBytes.length) (hj : j ≤ cnfBytes.length)
    (hsw : cnfBytes.drop j = skipWsComments (cnfBytes.drop idx))
    (hne : cnf_ptr + BitVec.ofNat 64 j ≠ cnf_ptr + BitVec.ofNat 64 cnfBytes.length)
    (hfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ FullMem c
      { st with core := { st.core with d_cur := cnf_ptr + BitVec.ofNat 64 j } } ⋆ R) m')
    (hQ : ∀ r st' m', st'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      st'.core.fuel = s.core.fuel → st'.core.oom = 0#64 → st'.core.probing = 0#64 →
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
      (r = 1#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
        Full.FullSparseInv c (shiftDownCnf cnf) st' ∧ st'.core.cur_level = 0) →
      (UnitUnsatTrace c.mv (s.core.vals.take (2 * c.mv)) (cnfBytes.drop i0) c.nc → r = 20#64) →
      (bytes cnf_ptr cnfBytes ⋆ FullMem c st' ⋆ R) m' → Q (r, ()) m') : Q (0#64, ()) m' := by
  have hj_lt : j < cnfBytes.length := by
    have hj_ne : j ≠ cnfBytes.length := fun heq =>
      hne ((cursor_eq_iff (base := cnf_ptr) (by omega) (by omega)).mpr heq)
    omega
  have hne_emp : (skipWsComments (cnfBytes.drop idx)).isEmpty = false := by
    rw [← hsw, List.drop_eq_getElem_cons hj_lt]; rfl
  exact hQ 0#64 { st with core := { st.core with d_cur := cnf_ptr + BitVec.ofNat 64 j } } m'
    ⟨{ hp.len_ok.core_ok with vals_len := hp.len_ok.core_ok.vals_len }, hp.len_ok.scratch_ok⟩
    (Or.inl rfl) hp.fuel_eq hp.oom_eq hp.prb_eq (fun h => by cases h) (fun h => by cases h)
    (fun hut => by
      rcases (hp.uns_tr hut).2 with ⟨_, _, _, htr⟩ | ⟨_, _, hr⟩
      · rw [Nat.sub_self] at htr; cases htr
      · rw [Nat.sub_self] at hr
        simp only [parseClauses, hne_emp, Bool.false_eq_true, ↓reduceIte] at hr; cases hr) hm

private theorem m6_parse_body_eof_done {c : FullCfg} {s st : FullState}
    {cnf_ptr : BitVec 64} {cnfBytes : List UInt8} {i0 idx j : Nat} {accCnf : CNF Nat}
    {unsat_v oom_v : Bool} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hp : M6ParseBodyInv c s cnf_ptr cnfBytes i0 c.nc idx accCnf unsat_v oom_v st)
    (_hidx : idx ≤ cnfBytes.length) (hj : j ≤ cnfBytes.length)
    (hsw : cnfBytes.drop j = skipWsComments (cnfBytes.drop idx))
    (heq : cnf_ptr + BitVec.ofNat 64 j = cnf_ptr + BitVec.ofNat 64 cnfBytes.length)
    (hfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ FullMem c
      { st with core := { st.core with d_cur := cnf_ptr + BitVec.ofNat 64 j } } ⋆ R) m')
    (hQ : ∀ r st' m', st'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      st'.core.fuel = s.core.fuel → st'.core.oom = 0#64 → st'.core.probing = 0#64 →
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
      (r = 1#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
        Full.FullSparseInv c (shiftDownCnf cnf) st' ∧ st'.core.cur_level = 0) →
      (UnitUnsatTrace c.mv (s.core.vals.take (2 * c.mv)) (cnfBytes.drop i0) c.nc → r = 20#64) →
      (bytes cnf_ptr cnfBytes ⋆ FullMem c st' ⋆ R) m' → Q (r, ()) m')
    (hret : (unsat_v = true ∧ cnf_ptr = cnf_ptr) ∨ (unsat_v = false ∧ oom_v = false)) :
    Q (if unsat_v then 20#64 else 1#64, ()) m' := by
  have hj_len : j = cnfBytes.length := (cursor_eq_iff (by omega) (by omega)).mp heq
  have hemp : (skipWsComments (cnfBytes.drop idx)).isEmpty = true := by
    rw [← hsw, hj_len, List.drop_length]; rfl
  have hpc_eq := hp.pc_eq; simp only [Nat.sub_self, parseClauses] at hpc_eq
  have hpd_some : parseDimacs cnfBytes = some accCnf := by rw [← hpc_eq]; simp [hemp]
  let sf : FullState := { st with core := { st.core with d_cur := cnf_ptr + BitVec.ofNat 64 j } }
  have hlen_sf : sf.LengthsOk c :=
    ⟨{ hp.len_ok.core_ok with vals_len := hp.len_ok.core_ok.vals_len }, hp.len_ok.scratch_ok⟩
  rcases hret with ⟨hunt, _⟩ | ⟨huf, hnf⟩
  · subst hunt
    exact hQ 20#64 sf m' hlen_sf (Or.inr (Or.inr rfl)) hp.fuel_eq hp.oom_eq hp.prb_eq
      (fun _ => ⟨accCnf, hpd_some, shiftDownCnf_unsat hp.vars_pos (hp.uns_inv rfl)⟩)
      (fun h => by cases h) (fun _ => rfl) hm
  · subst huf hnf
    obtain ⟨F_cur, hinv_w, _⟩ := hp.ok_inv rfl rfl
    have hinv_sf : Full.FullSparseInv c (shiftDownCnf accCnf) sf :=
      FullDimacsBodySpecs.FullSparseInv.with_d
        (FullDimacsBodySpecs.FullSparseInvW.toSparse hinv_w)
        (cnf_ptr + BitVec.ofNat 64 j) st.core.d_val
    exact hQ 1#64 sf m' hlen_sf (Or.inr (Or.inl rfl)) hp.fuel_eq hp.oom_eq hp.prb_eq
      (fun h => by cases h) (fun _ => ⟨accCnf, hpd_some, hinv_sf, hp.cl0⟩)
      (fun hut => by rcases (hp.uns_tr hut).2 with ⟨_, _, _, htr⟩ | ⟨ht, _⟩
                     · rw [Nat.sub_self] at htr; cases htr
                     · cases ht) hm

theorem full_parse_body_m6_wp (Γ : Env)
    (hSkip : ∀ a m Q X, Full.fullSkipClSpec a m Q X → Γ "full_skip_cl" [i64, i64] [.bool] a m Q X)
    (hIngest : ∀ a m Q X, m6IngestClSpec a m Q X →
      Γ "full_ingest_cl" [i64, i64] [i64] a m Q X)
    (hProp : ∀ a m Q X, Full.fullPropagateSpec a m Q X →
      Γ "full_propagate" [i64] [i64] a m Q X)
    (hSwc : ∀ a m Q X, kissatSkipWsCommentsSpec a m Q X →
      Γ "kissat_skip_ws_comments" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, Full.fullParseBodySpec a m Q X → Func.wp Γ full_parse_body_m6_body a m Q X := by
  rintro ⟨h, cend, ⟨⟩⟩ m Q X
    ⟨c, s, cnf_ptr, cnfBytes, i0, R, rfl, rfl, hfit, hi0, hhdr, hcv0, hdcur, hcl0, hte0, hpr0,
      hal0, hoom0, hprb0, hinc0, hvals0, hwvec0, hinv0, hm, hQ⟩
  have hnc_bd := c.hnc; have hmv_bd := c.hmv; unfold dimacsBound at hnc_bd hmv_bd
  have hpd_init : parseClauses c.mv c.nc CNF.empty (cnfBytes.drop i0) = parseDimacs cnfBytes := by
    simp [parseDimacs, hhdr]
  obtain ⟨hinv_w0, hent_0⟩ :=
    m6_full_init_sparseW hinv0 hcv0 hal0 hte0 hcl0 hinc0 hvals0 hwvec0
  m6_to_group
  refine wp_loop_group (fun r (unsat_v, oom_v, iv, ()) ml => ∃ i idx accCnf st,
      r = c.nc - i ∧ iv = BitVec.ofNat 64 i ∧
      M6ParseBodyInv c s cnf_ptr cnfBytes i0 i idx accCnf unsat_v oom_v st ∧
      (bytes cnf_ptr cnfBytes ⋆ FullMem c st ⋆ R) ml) ?_ ?_
  · rintro L r ⟨unsat_v, oom_v, iv, ⟨⟩⟩ ml ih ⟨i, idx, accCnf, st, rfl, rfl, hp, hml⟩
    have hile := hp.i_le; have hidx := hp.idx_le; have hcv_st := hp.cv_eq
    have hdcur_st := hp.d_cur_eq; have hlen_st := hp.len_ok; have hcl_st := hp.cl0
    have hfu_st := hp.fuel_eq; have hoom_st := hp.oom_eq; have hprb_st := hp.prb_eq
    m6_to_jnz; apply wp_jnz_of <;> intro hc_loop
    · have hilt : i < c.nc := by
        rw [Arg.val_var, BitVec.ult, decide_eq_true_eq,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hc_loop
        exact hc_loop
      m6_to_jnz; apply wp_jnz_of <;> intro hc_uns
      · have hunt : unsat_v = true := by simpa [Arg.val_var] using hc_uns
        subst hunt; have hsub_eq : c.nc - i = (c.nc - (i + 1)) + 1 := by omega
        have hinc : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := by
          apply BitVec.eq_of_toNat_eq
          change (i % 2 ^ 64 + 1) % 2 ^ 64 = (i + 1) % 2 ^ 64; omega
        m6_steps; c0_call hSkip
        refine ⟨cnf_ptr, BitVec.ofNat 64 c.nc, st.core.d_val, c.mv, cnfBytes, idx,
          FullRest c st ⋆ R, rfl, hfit, by omega, hidx,
          by rw [← hdcur_st]; exact m6_full_mem_to_dimacs hml, ?_⟩
        cases hpc1 : parseClause c.mv (cnfBytes.drop idx) with
        | none =>
          intro cur' val' m' hm'; m6_steps
          exact hQ 0#64 { st with core := { st.core with d_cur := cur', d_val := val' } } m'
            ⟨{ hlen_st.core_ok with vals_len := hlen_st.core_ok.vals_len }, hlen_st.scratch_ok⟩
            (Or.inl rfl) hfu_st hoom_st hprb_st (fun h => by cases h) (fun h => by cases h)
            (fun hut => by
              rcases (hp.uns_tr hut).2 with ⟨hf, _⟩ | ⟨_, _, hr⟩
              · cases hf
              · rw [hsub_eq, parseClauses, hpc1] at hr; cases hr)
            (m6_full_dimacs_to_mem hm')
        | some p =>
          rcases p with ⟨cl, rest⟩; intro j m' hcl_pos _ hj hdrop hm'; m6_steps
          · exact ih (c.nc - (i + 1)) _ _ (by omega)
              ⟨i + 1, j, accCnf.add cl, _, rfl, hinc,
                m6_parse_body_skip_step hp hilt hpc1 hcl_pos hj hdrop rfl,
                m6_full_dimacs_to_mem hm'⟩
          · cases (by assumption : true = false)
      · have huf : unsat_v = false := by simpa [Arg.val_var] using hc_uns
        subst huf
        m6_to_jnz; apply wp_jnz_of <;> intro hc_oom
        · have hoo : oom_v = true := by simpa [Arg.val_var] using hc_oom
          subst hoo; m6_c0_steps; exact m6_parse_body_oom_exit hp hml hQ
        · have hnf : oom_v = false := by simpa [Arg.val_var] using hc_oom
          subst hnf; have hsub_eq : c.nc - i = (c.nc - (i + 1)) + 1 := by omega
          have hinc : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := by
            apply BitVec.eq_of_toNat_eq
            change (i % 2 ^ 64 + 1) % 2 ^ 64 = (i + 1) % 2 ^ 64; omega
          obtain ⟨F_cur, hinv_st, hent_st⟩ := hp.ok_inv rfl rfl
          m6_steps; c0_call hIngest
          refine ⟨c, accCnf, F_cur, st, cnf_ptr, cnfBytes, idx, R, rfl, rfl, hfit, hidx,
            hcv_st, hdcur_st, hcl_st, hinv_st, hent_st, hml, ?_⟩
          cases hpc1 : parseClause c.mv (cnfBytes.drop idx) with
          | none =>
            intro st' m' hlen' hfu' hoom' hprb' hm'
            m6_to_jnz; apply wp_jnz_of <;> intro hc0
            · m6_c0_steps
              exact hQ 0#64 st' m' hlen' (Or.inl rfl) (hfu'.trans hfu_st) (hoom'.trans hoom_st)
                (hprb'.trans hprb_st) (fun h => by cases h) (fun h => by cases h)
                (fun hut => by
                  rcases (hp.uns_tr hut).2 with ⟨_, _, _, htr⟩ | ⟨ht, _⟩
                  · rw [hsub_eq] at htr; cases htr with
                    | conflict _ hpc_s _ _ => rw [hpc1] at hpc_s; cases hpc_s
                    | step _ hpc_s _ _ => rw [hpc1] at hpc_s; cases hpc_s
                  · cases ht) hm'
            · exfalso; simp [Arg.val_var] at hc0
          | some p =>
            rcases p with ⟨cl, rest⟩
            intro r_in st' j m' hcl_pos _ hj hdrop hlen' hcv' hd' hcl' hfu' hoom' hprb' hr_dom
              hok_in huns_in hunit_ok hunit_fl hm'
            have hp_next := m6_parse_body_ingest_step hp hilt hpc1 hcl_pos hj hdrop hlen' hcv'
              hd' hcl' hfu' hoom' hprb' hr_dom hok_in huns_in hunit_ok hunit_fl
            rcases hr_dom with rfl | rfl | rfl
            · m6_to_jnz; apply wp_jnz_of <;> intro hc0
              · exfalso; simp [Arg.val_var] at hc0
              · m6_to_jnz; apply wp_jnz_of <;> intro hc2
                · exfalso; simp [Arg.val_var] at hc2
                · m6_to_jnz; apply wp_jnz_of <;> intro hc3
                  · exfalso; simp [Arg.val_var] at hc3
                  · m6_to_group
                    refine wp_join_group (fun (u1, o1, ()) mJ => ∃ stJ : FullState,
                      M6ParseBodyInv c s cnf_ptr cnfBytes i0 (i + 1) j (accCnf.add cl) u1 o1 stJ ∧
                      (bytes cnf_ptr cnfBytes ⋆ FullMem c stJ ⋆ R) mJ)
                      (fun _ (u1, o1, ()) mJ ⟨stJ, hpJ, hmJ⟩ => by
                        m6_c0_steps
                        exact ih (c.nc - (i + 1)) _ _ (by omega) ⟨i + 1, j, accCnf.add cl, stJ,
                          rfl, hinc, hpJ, hmJ⟩)
                      (fun Jb hJb => ?_)
                    m6_to_jnz; apply wp_jnz_of <;> intro hc_pr
                    · have hpr_lt : st'.core.propagated < st'.core.trail_end := by
                        have hte_bd : st'.core.trail_end < 2 ^ 64 := by
                          have := hlen'.core_ok.trail_end_le; have := c.hmaxv
                          unfold dimacsBound at this; omega
                        have hpr_bd : st'.core.propagated < 2 ^ 64 := by
                          have := hlen'.core_ok.propagated_le; omega
                        rw [Arg.val_var, BitVec.ult, decide_eq_true_eq,
                          BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpr_bd,
                          BitVec.toNat_ofNat, Nat.mod_eq_of_lt hte_bd] at hc_pr
                        exact hc_pr
                      m6_to_jnz; apply wp_jnz_of <;> intro hc_al
                      · have har_pos : 0 < st'.core.arena_len := by
                          have hal_bd : st'.core.arena_len < 2 ^ 64 := by
                            have := hlen'.core_ok.arena_len_le; have := c.harena
                            unfold dimacsBound at this; omega
                          rw [Arg.val_var, BitVec.ult, decide_eq_true_eq,
                            BitVec.toNat_ofNat, Nat.mod_eq_of_lt hal_bd] at hc_al
                          change 0 < st'.core.arena_len at hc_al
                          exact hc_al
                        have hno_hut :
                            ¬ UnitUnsatTrace c.mv (s.core.vals.take (2 * c.mv))
                                (cnfBytes.drop i0) c.nc := by
                          intro hut
                          rcases (hp_next.uns_tr hut).2 with ⟨_, hal0, _, _⟩ | ⟨hc, _⟩
                          · omega
                          · cases hc
                        obtain ⟨F_cur', hsp', hent'⟩ := hok_in rfl
                        m6_steps; c0_call hProp
                        refine ⟨c, shiftDownCnf (accCnf.add cl), F_cur', st',
                          bytes cnf_ptr cnfBytes ⋆ R, rfl, hlen', hsp'.2.1, hsp'.2.2.2.2.2,
                          sep_ac hm', ?_⟩
                        intro pr vals2 flags2 lvl2 rsns2 trl2 tp2 te2 prop2 unass2 unfl2 wvec2
                          arena2 wstk2 wlen2 wu2 fuel2 ctype2 cref2 c0_2 c1_2 oom2 ticks2 wsort2
                          phases2 m2 s2_d hlen2 hw2 htr2 hperm2 _hfu2 hpr_dom hpr0 hpr1 _hpr2
                          _hnoop hm2
                        let st2 : FullState :=
                          { st' with
                            core := { st'.core with
                              vals := vals2, flags := flags2, lvl := lvl2, rsns := rsns2,
                              trl := trl2, trail_pos := tp2, trail_end := te2, propagated := prop2,
                              unassigned := unass2, unflushed := unfl2, wvec := wvec2,
                              arena := arena2, wstk := wstk2, wlen := wlen2, wusable := wu2,
                              fuel := fuel2, confl_type := ctype2, confl_ref := cref2,
                              confl_lit0 := c0_2, confl_lit1 := c1_2, oom := oom2 }
                            scratch := { st'.scratch with
                              search_ticks := ticks2, wsort := wsort2, phases := phases2 } }
                        let st2f : FullState :=
                          { st2 with core := { st2.core with fuel := st'.core.fuel } }
                        have hlen2f : st2f.LengthsOk c :=
                          ⟨{ hlen2.core_ok with vals_len := hlen2.core_ok.vals_len },
                           hlen2.scratch_ok⟩
                        have hw2f : FullWitnessInv c (shiftDownCnf (accCnf.add cl)) F_cur'
                            st2f.core :=
                          { hw2 with
                            arena := { hw2.arena with len_ok := hw2.arena.len_ok }
                            watches := hw2.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
                        have hsp2f : Full.FullSparseInvW c (shiftDownCnf (accCnf.add cl)) F_cur'
                            st2f :=
                          full_sparse_invW_of_propagate hsp' hlen2f hw2f hperm2 rfl rfl rfl rfl
                            hsp'.2.2.2.2.2
                        m6_to_jnz
                        rcases hpr_dom with rfl | rfl | rfl
                        · have hoom2 : oom2 = 0#64 := (hpr0 rfl).2.1 (hoom'.trans hp.oom_eq)
                          m6_c0_steps
                          exact hJb (false, false, ()) _ ⟨st2f,
                            ⟨by omega, hj, hcv', hd', hlen2f, hcl', hfu'.trans hp.fuel_eq,
                              hoom2, hprb'.trans hp.prb_eq,
                              cnfVarsPos_add hp.vars_pos hcl_pos, hp_next.pc_eq,
                              (fun h => by cases h),
                              (fun _ _ => ⟨F_cur', hsp2f, hent'⟩),
                              (fun hut => absurd hut hno_hut)⟩,
                            sep_ac (by assumption)⟩
                        · have huns_after :=
                            level0_unsat_of_conflict_okW hw2 hcl' (hpr1 rfl).2.2
                          have hoom2 : oom2 = 0#64 := (hpr1 rfl).2.1
                          m6_to_jnz; apply wp_jnz_of <;> intro hc_p1
                          · m6_c0_steps
                            exact hJb (true, false, ()) _ ⟨st2f,
                              ⟨by omega, hj, hcv', hd', hlen2f, hcl', hfu'.trans hp.fuel_eq,
                                hoom2, hprb'.trans hp.prb_eq,
                                cnfVarsPos_add hp.vars_pos hcl_pos, hp_next.pc_eq,
                                (fun _ => huns_after), (fun h => by cases h),
                                (fun hut => absurd hut hno_hut)⟩,
                              sep_ac (by assumption)⟩
                          · exfalso; simp [Arg.val_var] at hc_p1
                        · m6_to_jnz; apply wp_jnz_of <;> intro hc_p1
                          · exfalso; simp [Arg.val_var] at hc_p1
                          · m6_to_jnz; apply wp_jnz_of <;> intro hc_p2
                            · m6_to_jnz; apply wp_jnz_of <;> intro hc_o2
                              · have hoom_ne : oom2 ≠ 0#64 := by
                                  rw [Arg.val_var, bne_iff_ne] at hc_o2; exact hc_o2
                                let st2fo : FullState :=
                                  { st2f with core := { st2f.core with oom := 0#64 } }
                                have hlen2fo : st2fo.LengthsOk c :=
                                  ⟨{ hlen2f.core_ok with vals_len := hlen2f.core_ok.vals_len },
                                   hlen2f.scratch_ok⟩
                                m6_c0_steps
                                exact hJb (false, true, ()) _ ⟨st2fo,
                                  ⟨by omega, hj, hcv', hd', hlen2fo, hcl', hfu'.trans hp.fuel_eq,
                                    rfl, hprb'.trans hp.prb_eq,
                                    cnfVarsPos_add hp.vars_pos hcl_pos,
                                    hp_next.pc_eq, (fun h => by cases h),
                                    (fun _ hc => by cases hc),
                                    (fun hut => absurd hut hno_hut)⟩,
                                  sep_ac (by assumption)⟩
                              · have hoom2 : oom2 = 0#64 := by
                                  simpa [Arg.val_var, bne_eq_false_iff_eq] using hc_o2
                                m6_c0_steps
                                exact hJb (false, false, ()) _ ⟨st2f,
                                  ⟨by omega, hj, hcv', hd', hlen2f, hcl', hfu'.trans hp.fuel_eq,
                                    hoom2, hprb'.trans hp.prb_eq,
                                    cnfVarsPos_add hp.vars_pos hcl_pos, hp_next.pc_eq,
                                    (fun h => by cases h),
                                    (fun _ _ => ⟨F_cur', hsp2f, hent'⟩),
                                    (fun hut => absurd hut hno_hut)⟩,
                                  sep_ac (by assumption)⟩
                            · exfalso; simp [Arg.val_var] at hc_p2
                      · m6_to_jnz; apply wp_jnz_of <;> intro hc_nb
                        · have hnb_ne : st'.core.num_binary ≠ s.core.num_binary := by
                            rw [Arg.val_var, bne_iff_ne] at hc_nb; exact hc_nb
                          have hno_hut :
                              ¬ UnitUnsatTrace c.mv (s.core.vals.take (2 * c.mv))
                                  (cnfBytes.drop i0) c.nc := by
                            intro hut
                            rcases (hp_next.uns_tr hut).2 with ⟨_, _, hnb0, _⟩ | ⟨hc, _⟩
                            · exact hnb_ne hnb0
                            · cases hc
                          obtain ⟨F_cur', hsp', hent'⟩ := hok_in rfl
                          m6_steps; c0_call hProp
                          refine ⟨c, shiftDownCnf (accCnf.add cl), F_cur', st',
                            bytes cnf_ptr cnfBytes ⋆ R, rfl, hlen', hsp'.2.1, hsp'.2.2.2.2.2,
                            sep_ac hm', ?_⟩
                          intro pr vals2 flags2 lvl2 rsns2 trl2 tp2 te2 prop2 unass2 unfl2 wvec2
                            arena2 wstk2 wlen2 wu2 fuel2 ctype2 cref2 c0_2 c1_2 oom2 ticks2 wsort2
                            phases2 m2 s2_d hlen2 hw2 htr2 hperm2 _hfu2 hpr_dom hpr0 hpr1 _hpr2
                            _hnoop hm2
                          let st2 : FullState :=
                            { st' with
                              core := { st'.core with
                                vals := vals2, flags := flags2, lvl := lvl2, rsns := rsns2,
                                trl := trl2, trail_pos := tp2, trail_end := te2,
                                propagated := prop2, unassigned := unass2, unflushed := unfl2,
                                wvec := wvec2, arena := arena2, wstk := wstk2, wlen := wlen2,
                                wusable := wu2, fuel := fuel2, confl_type := ctype2,
                                confl_ref := cref2, confl_lit0 := c0_2, confl_lit1 := c1_2,
                                oom := oom2 }
                              scratch := { st'.scratch with
                                search_ticks := ticks2, wsort := wsort2, phases := phases2 } }
                          let st2f : FullState :=
                            { st2 with core := { st2.core with fuel := st'.core.fuel } }
                          have hlen2f : st2f.LengthsOk c :=
                            ⟨{ hlen2.core_ok with vals_len := hlen2.core_ok.vals_len },
                             hlen2.scratch_ok⟩
                          have hw2f : FullWitnessInv c (shiftDownCnf (accCnf.add cl)) F_cur'
                              st2f.core :=
                            { hw2 with
                              arena := { hw2.arena with len_ok := hw2.arena.len_ok }
                              watches :=
                                hw2.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
                          have hsp2f : Full.FullSparseInvW c (shiftDownCnf (accCnf.add cl)) F_cur'
                              st2f :=
                            full_sparse_invW_of_propagate hsp' hlen2f hw2f hperm2 rfl rfl rfl rfl
                              hsp'.2.2.2.2.2
                          m6_to_jnz
                          rcases hpr_dom with rfl | rfl | rfl
                          · have hoom2 : oom2 = 0#64 := (hpr0 rfl).2.1 (hoom'.trans hp.oom_eq)
                            m6_c0_steps
                            exact hJb (false, false, ()) _ ⟨st2f,
                              ⟨by omega, hj, hcv', hd', hlen2f, hcl', hfu'.trans hp.fuel_eq,
                                hoom2, hprb'.trans hp.prb_eq,
                                cnfVarsPos_add hp.vars_pos hcl_pos, hp_next.pc_eq,
                                (fun h => by cases h),
                                (fun _ _ => ⟨F_cur', hsp2f, hent'⟩),
                                (fun hut => absurd hut hno_hut)⟩,
                              sep_ac (by assumption)⟩
                          · have huns_after :=
                              level0_unsat_of_conflict_okW hw2 hcl' (hpr1 rfl).2.2
                            have hoom2 : oom2 = 0#64 := (hpr1 rfl).2.1
                            m6_to_jnz; apply wp_jnz_of <;> intro hc_p1
                            · m6_c0_steps
                              exact hJb (true, false, ()) _ ⟨st2f,
                                ⟨by omega, hj, hcv', hd', hlen2f, hcl', hfu'.trans hp.fuel_eq,
                                  hoom2, hprb'.trans hp.prb_eq,
                                  cnfVarsPos_add hp.vars_pos hcl_pos, hp_next.pc_eq,
                                  (fun _ => huns_after), (fun h => by cases h),
                                  (fun hut => absurd hut hno_hut)⟩,
                                sep_ac (by assumption)⟩
                            · exfalso; simp [Arg.val_var] at hc_p1
                          · m6_to_jnz; apply wp_jnz_of <;> intro hc_p1
                            · exfalso; simp [Arg.val_var] at hc_p1
                            · m6_to_jnz; apply wp_jnz_of <;> intro hc_p2
                              · m6_to_jnz; apply wp_jnz_of <;> intro hc_o2
                                · have hoom_ne : oom2 ≠ 0#64 := by
                                    rw [Arg.val_var, bne_iff_ne] at hc_o2; exact hc_o2
                                  let st2fo : FullState :=
                                    { st2f with core := { st2f.core with oom := 0#64 } }
                                  have hlen2fo : st2fo.LengthsOk c :=
                                    ⟨{ hlen2f.core_ok with vals_len := hlen2f.core_ok.vals_len },
                                     hlen2f.scratch_ok⟩
                                  m6_c0_steps
                                  exact hJb (false, true, ()) _ ⟨st2fo,
                                    ⟨by omega, hj, hcv', hd', hlen2fo, hcl', hfu'.trans hp.fuel_eq,
                                      rfl, hprb'.trans hp.prb_eq,
                                      cnfVarsPos_add hp.vars_pos hcl_pos,
                                      hp_next.pc_eq, (fun h => by cases h),
                                      (fun _ hc => by cases hc),
                                      (fun hut => absurd hut hno_hut)⟩,
                                    sep_ac (by assumption)⟩
                                · have hoom2 : oom2 = 0#64 := by
                                    simpa [Arg.val_var, bne_eq_false_iff_eq] using hc_o2
                                  m6_c0_steps
                                  exact hJb (false, false, ()) _ ⟨st2f,
                                    ⟨by omega, hj, hcv', hd', hlen2f, hcl', hfu'.trans hp.fuel_eq,
                                      hoom2, hprb'.trans hp.prb_eq,
                                      cnfVarsPos_add hp.vars_pos hcl_pos, hp_next.pc_eq,
                                      (fun h => by cases h),
                                      (fun _ _ => ⟨F_cur', hsp2f, hent'⟩),
                                      (fun hut => absurd hut hno_hut)⟩,
                                    sep_ac (by assumption)⟩
                              · exfalso; simp [Arg.val_var] at hc_p2
                        · m6_c0_steps; exact hJb (false, false, ()) m' ⟨st', hp_next, hm'⟩
                    · m6_c0_steps; exact hJb (false, false, ()) m' ⟨st', hp_next, hm'⟩
            · m6_to_jnz; apply wp_jnz_of <;> intro hc0
              · exfalso; simp [Arg.val_var] at hc0
              · m6_to_jnz; apply wp_jnz_of <;> intro hc2
                · m6_c0_steps
                  exact ih (c.nc - (i + 1)) _ _ (by omega)
                    ⟨i + 1, j, accCnf.add cl, st', rfl, hinc, by simpa using hp_next, hm'⟩
                · exfalso; simp [Arg.val_var] at hc2
            · m6_to_jnz; apply wp_jnz_of <;> intro hc0
              · exfalso; simp [Arg.val_var] at hc0
              · m6_to_jnz; apply wp_jnz_of <;> intro hc2
                · exfalso; simp [Arg.val_var] at hc2
                · m6_to_jnz; apply wp_jnz_of <;> intro hc3
                  · m6_c0_steps
                    exact ih (c.nc - (i + 1)) _ _ (by omega)
                      ⟨i + 1, j, accCnf.add cl, st', rfl, hinc, by simpa using hp_next, hm'⟩
                  · exfalso; simp [Arg.val_var] at hc3
    · have hieq : i = c.nc := by
        rw [Arg.val_var, BitVec.ult, decide_eq_false_iff_not,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hc_loop
        omega
      subst hieq
      m6_to_jnz; apply wp_jnz_of <;> intro hc_oom2
      · have hoo : oom_v = true := by simpa [Arg.val_var] using hc_oom2
        subst hoo; m6_c0_steps; exact m6_parse_body_oom_exit hp hml hQ
      · have hnf : oom_v = false := by simpa [Arg.val_var] using hc_oom2
        subst hnf
        m6_steps; c0_call hSwc
        refine ⟨cnf_ptr, cnfBytes, idx, FullMem c st ⋆ R, hdcur_st, rfl, hfit, hidx,
          sep_ac hml, fun j _ hj hsw => ?_⟩
        m6_to_jnz; apply wp_jnz_of <;> intro hc_eof
        · m6_c0_steps
          exact m6_parse_body_eof_ne hp hidx hj hsw
            (by simpa [Arg.val_var, bne_iff_ne] using hc_eof) hfit (sep_ac hm) hQ
        · have heof_eq : cnf_ptr + BitVec.ofNat 64 j =
              cnf_ptr + BitVec.ofNat 64 cnfBytes.length := by
            simpa [Arg.val_var, bne_eq_false_iff_eq] using hc_eof
          m6_to_jnz; apply wp_jnz_of <;> intro hc_u2
          · have hunt : unsat_v = true := by simpa [Arg.val_var] using hc_u2
            m6_c0_steps
            simpa [hunt] using m6_parse_body_eof_done hp hidx hj hsw heof_eq hfit
              (sep_ac hm) hQ (Or.inl ⟨hunt, rfl⟩)
          · have huf : unsat_v = false := by simpa [Arg.val_var] using hc_u2
            m6_c0_steps
            simpa [huf] using m6_parse_body_eof_done hp hidx hj hsw heof_eq hfit
              (sep_ac hm) hQ (Or.inr ⟨huf, rfl⟩)
  · intro L hL; m6_c0_steps
    have hcmv0 : c.mv ≤ c.max_vars := hcv0 ▸ hinv0.1.lengths.core_ok.cur_vars_le
    exact hL c.nc _ m ⟨0, i0, CNF.empty, s, by simp, rfl,
      ⟨Nat.zero_le _, hi0, hcv0, hdcur, hinv0.1.lengths, hcl0, rfl, hoom0, hprb0,
        cnfVarsPos_empty, by simpa using hpd_init, (fun hc => by cases hc),
        fun _ _ => ⟨[], hinv_w0, hent_0⟩,
        fun hut => ⟨rfl, Or.inl ⟨rfl, hal0, rfl, by
          rw [Nat.sub_zero]
          refine m6_unitUnsatTrace_congr_vals
            (by rw [List.length_take, hinv0.1.lengths.core_ok.vals_len]; omega)
            (by rw [hinv0.1.lengths.core_ok.vals_len]; omega) (fun k hk => ?_) hut
          rw [List.getElem?_take_of_lt hk]⟩⟩⟩, hm⟩

/-! ## 4. `full_extend_push2_m6_wp` & `full_extend_push_cl_m6_wp` -/

private def m6SkipLit (vals : List (BitVec 8)) (lvl : List (BitVec 32)) (nlits : Nat)
    (bl lit : BitVec 32) : Bool :=
  (lit == bl) ||
    (decide (lit.toNat < nlits) && (lvl[lit.toNat / 2]?.getD 0#32 == 0#32) &&
     ((vals[lit.toNat]?.getD 0#8).signExtend 32).slt 0#32)

private def m6KeepPrefixCount (ar : List (BitVec 32)) (vals : List (BitVec 8))
    (lvl : List (BitVec 32)) (nlits cref : Nat) (bl : BitVec 32) (k : Nat) : Nat :=
  (List.range k).countP (fun j =>
    !m6SkipLit vals lvl nlits bl (ar[cref + 3 + j]?.getD 0#32 &&& 0x7FFFFFFF#32))

private theorem m6KeepPrefixCount_zero (ar : List (BitVec 32)) (vals : List (BitVec 8))
    (lvl : List (BitVec 32)) (nlits cref : Nat) (bl : BitVec 32) :
    m6KeepPrefixCount ar vals lvl nlits cref bl 0 = 0 := rfl

private theorem m6KeepPrefixCount_succ (ar : List (BitVec 32)) (vals : List (BitVec 8))
    (lvl : List (BitVec 32)) (nlits cref : Nat) (bl : BitVec 32) (k : Nat) :
    m6KeepPrefixCount ar vals lvl nlits cref bl (k + 1) =
      m6KeepPrefixCount ar vals lvl nlits cref bl k +
        (if m6SkipLit vals lvl nlits bl (ar[cref + 3 + k]?.getD 0#32 &&& 0x7FFFFFFF#32)
         then 0 else 1) := by
  unfold m6KeepPrefixCount
  rw [List.range_succ, List.countP_append, List.countP_cons, List.countP_nil]
  cases m6SkipLit vals lvl nlits bl (ar[cref + 3 + k]?.getD 0#32 &&& 0x7FFFFFFF#32) <;> simp

private theorem m6KeepPrefixCount_le (ar : List (BitVec 32)) (vals : List (BitVec 8))
    (lvl : List (BitVec 32)) (nlits cref : Nat) (bl : BitVec 32) :
    ∀ k, m6KeepPrefixCount ar vals lvl nlits cref bl k ≤ k := fun k => by
  simpa [m6KeepPrefixCount, List.length_range] using
    (List.countP_le_length (l := List.range k) (p := fun j =>
      !m6SkipLit vals lvl nlits bl (ar[cref + 3 + j]?.getD 0#32 &&& 0x7FFFFFFF#32)))

private theorem m6KeepPrefixCount_mono (ar : List (BitVec 32)) (vals : List (BitVec 8))
    (lvl : List (BitVec 32)) (nlits cref : Nat) (bl : BitVec 32)
    {a b : Nat} (hab : a ≤ b) :
    m6KeepPrefixCount ar vals lvl nlits cref bl a ≤
      m6KeepPrefixCount ar vals lvl nlits cref bl b := by
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst this; exact Nat.le_refl _
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le hab with rfl | hlt
    · exact Nat.le_refl _
    · have := ih (by omega)
      rw [m6KeepPrefixCount_succ]
      by_cases hsk :
          m6SkipLit vals lvl nlits bl (ar[cref + 3 + b]?.getD 0#32 &&& 0x7FFFFFFF#32) <;>
        simp [hsk] <;> omega

private theorem hot_lt_nlits_of_ult {x : BitVec 32} {cv : Nat} (hcv : cv < 2 ^ 63)
    (hc : BitVec.ult (x.setWidth 64) ((BitVec.ofNat 64 cv) <<< (1 : Nat)) = true) :
    x.toNat < 2 * cv := by
  rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (by have := x.isLt; omega),
    BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hc
  simp only [Nat.shiftLeft_eq] at hc; omega

private theorem not_hot_lt_nlits_of_ult {x : BitVec 32} {cv : Nat} (hcv : cv < 2 ^ 63)
    (hc : BitVec.ult (x.setWidth 64) ((BitVec.ofNat 64 cv) <<< (1 : Nat)) = false) :
    ¬ x.toNat < 2 * cv := by
  rw [BitVec.ult, decide_eq_false_iff_not, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (by have := x.isLt; omega),
    BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hc
  simp only [Nat.shiftLeft_eq] at hc; omega

theorem full_extend_push2_m6_wp (Γ : Env) :
    ∀ a m Q X, Full.fullExtendPush2Spec a m Q X →
      Func.wp Γ full_extend_push2_m6_body a m Q X := by
  rintro ⟨h, blk_lit, other, ⟨⟩⟩ m Q X ⟨c, s, R, ⟨rfl, hel⟩, hlen, hm, hQ⟩
  dsimp only [Full.fullSafetySlice_mem, Full.fullSafetySlice_coreProj,
    Full.fullSafetySlice_safe] at hlen hm hQ
  obtain hcap : c.extend_cap < dimacsBound := c.hext
  obtain hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hcap hmax
  have hco := hlen.core_ok
  have hcv := hco.cur_vars_le
  have hvl := hco.vals_len
  have hll := hco.lvl_len
  have hesl := hlen.scratch_ok.extend_stk_len
  let ot := other &&& 0x7FFFFFFF#32
  m6_to_group
  refine wp_join_group (fun (skip_ot, ()) m0 => m0 = m ∧
      (skip_ot = true → ot.toNat < 2 * s.core.cur_vars)) ?_ ?_
  · rintro _ ⟨skip_ot, ⟨⟩⟩ m0 ⟨hm0, _⟩
    subst m0
    m6_to_group
    refine wp_join_group (fun (need, ()) m1 =>
        m1 = m ∧ need = (if skip_ot then 1#64 else 2#64)) ?_ ?_
    · rintro _ ⟨need, ⟨⟩⟩ m1 ⟨hm1, rfl⟩
      subst m1
      m6_to_jnz; apply wp_jnz_of <;> intro hc1
      · m6_steps
        exact hQ (false, ()) s m rfl hlen ⟨rfl, hel, rfl⟩ hm
      · have hel_le : s.scratch.extend_len ≤ c.extend_cap := by
          rw [Arg.val_var, BitVec.ult, decide_eq_false_iff_not] at hc1
          bv_omega
        m6_to_jnz; apply wp_jnz_of <;> intro hc2
        · m6_steps
          exact hQ (false, ()) s m rfl hlen ⟨rfl, hel, rfl⟩ hm
        · have hfit : s.scratch.extend_len + (if skip_ot then 1 else 2) ≤ c.extend_cap := by
            rw [Arg.val_var, BitVec.ult, decide_eq_false_iff_not] at hc2
            cases skip_ot <;> simp at hc2 ⊢ <;> bv_omega
          have hp_lt : (BitVec.ofNat 64 s.scratch.extend_len).toNat <
              s.scratch.extend_stk.length := by
            rw [hesl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
            cases skip_ot <;> simp at hfit <;> omega
          cases skip_ot
          · have hp1_lt : (BitVec.ofNat 64 s.scratch.extend_len + 1#64).toNat <
                (s.scratch.extend_stk.set (BitVec.ofNat 64 s.scratch.extend_len).toNat
                  (blk_lit ||| 0x80000000#32)).length := by
              rw [List.length_set, hesl]
              simp at hfit; bv_omega
            m6_to_jnz; apply wp_jnz_of <;> intro hc_not
            · exfalso; simp [Arg.val_var] at hc_not
            · m6_steps
              let s' : FullState :=
                { s with scratch := { s.scratch with
                  extend_stk := (s.scratch.extend_stk.set
                    (BitVec.ofNat 64 s.scratch.extend_len).toNat
                    (blk_lit ||| 0x80000000#32)).set
                    (BitVec.ofNat 64 s.scratch.extend_len + 1#64).toNat ot,
                  extend_len := (BitVec.ofNat 64 s.scratch.extend_len + 2#64).toNat } }
              exact hQ (true, ()) s' _ rfl
                (hlen.with_scratch { hlen.scratch_ok with extend_stk_len := by simp [hesl] })
                ⟨rfl, by dsimp [s']; simp at hfit; bv_omega, rfl⟩ (by assumption)
          · m6_to_jnz; apply wp_jnz_of <;> intro hc_not
            · m6_steps
              let s' : FullState :=
                { s with scratch := { s.scratch with
                  extend_stk := s.scratch.extend_stk.set
                    (BitVec.ofNat 64 s.scratch.extend_len).toNat (blk_lit ||| 0x80000000#32),
                  extend_len := (BitVec.ofNat 64 s.scratch.extend_len + 1#64).toNat } }
              exact hQ (true, ()) s' _ rfl
                (hlen.with_scratch { hlen.scratch_ok with extend_stk_len := by simp [hesl] })
                ⟨rfl, by dsimp [s']; simp at hfit; bv_omega, rfl⟩ (by assumption)
            · exfalso; simp [Arg.val_var] at hc_not
    · intro Jn hJn
      m6_to_jnz; apply wp_jnz_of <;> intro hsk
      · have hst : skip_ot = true := by simpa [Arg.val_var] using hsk
        m6_c0_steps; exact hJn _ m ⟨rfl, by simp [hst]⟩
      · have hsf : skip_ot = false := by simpa [Arg.val_var] using hsk
        m6_c0_steps; exact hJn _ m ⟨rfl, by simp [hsf]⟩
  · intro J0 hJ0
    m6_to_jnz; apply wp_jnz_of <;> intro hc_nl
    · have hot_lt : ot.toNat < 2 * s.core.cur_vars :=
        hot_lt_nlits_of_ult (by omega) (by simpa [Arg.val_var, ot] using hc_nl)
      have hot_v : (ot >>> 1#32).toNat < s.core.lvl.length := by
        rw [show (ot >>> 1#32).toNat = ot.toNat / 2 from
          by simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow], hll]
        omega
      have hot_val : ot.toNat < s.core.vals.length := by rw [hvl]; omega
      m6_to_jnz; apply wp_jnz_of <;> intro hc_lv
      · m6_to_jnz; apply wp_jnz_of <;> intro hc_va
        · m6_steps; exact hJ0 (true, ()) m ⟨rfl, fun _ => hot_lt⟩
        · m6_steps; exact hJ0 (false, ()) m ⟨rfl, fun h => by cases h⟩
      · m6_steps; exact hJ0 (false, ()) m ⟨rfl, fun h => by cases h⟩
    · m6_steps; exact hJ0 (false, ()) m ⟨rfl, fun h => by cases h⟩

private theorem m6_ext_cl_step_true {ar : List (BitVec 32)} {vals : List (BitVec 8)}
    {lvl : List (BitVec 32)} {nlits cref k : Nat} {bl : BitVec 32}
    (hcv : cref + 3 + k < ar.length)
    (hsk : m6SkipLit vals lvl nlits bl ((ar[cref + 3 + k]'hcv) &&& 0x7FFFFFFF#32) = true) :
    m6KeepPrefixCount ar vals lvl nlits cref bl (k + 1) =
      m6KeepPrefixCount ar vals lvl nlits cref bl k := by
  simp only [m6KeepPrefixCount_succ, List.getElem?_eq_getElem hcv,
    Option.getD_some, hsk, ↓reduceIte, Nat.add_zero]

private theorem m6_ext_cl_step_false {ar : List (BitVec 32)} {vals : List (BitVec 8)}
    {lvl : List (BitVec 32)} {nlits cref k : Nat} {bl : BitVec 32}
    (hcv : cref + 3 + k < ar.length)
    (hsk : m6SkipLit vals lvl nlits bl ((ar[cref + 3 + k]'hcv) &&& 0x7FFFFFFF#32) = false) :
    m6KeepPrefixCount ar vals lvl nlits cref bl (k + 1) =
      m6KeepPrefixCount ar vals lvl nlits cref bl k + 1 := by
  simp only [m6KeepPrefixCount_succ, List.getElem?_eq_getElem hcv,
    Option.getD_some, hsk, Bool.false_eq_true, ↓reduceIte]

theorem full_extend_push_cl_m6_wp (Γ : Env) :
    ∀ a m Q X, Full.fullExtendPushClSpec a m Q X →
      Func.wp Γ full_extend_push_cl_m6_body a m Q X := by
  rintro ⟨h, blk_lit, cref, ⟨⟩⟩ m Q X ⟨c, s, R, ⟨rfl, hel⟩, hlen, hm, hQ⟩
  dsimp only [Full.fullSafetySlice_mem, Full.fullSafetySlice_coreProj,
    Full.fullSafetySlice_safe] at hlen hm hQ
  obtain haca : c.arena_cap < 2 * dimacsBound := c.harena
  obtain heca : c.extend_cap < dimacsBound := c.hext
  obtain hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at haca heca hmax
  have hco := hlen.core_ok
  obtain harl := hco.arena_len_arr
  obtain hale := hco.arena_len_le
  obtain hcv := hco.cur_vars_le
  obtain hvl := hco.vals_len
  obtain hll := hco.lvl_len
  obtain hesl := hlen.scratch_ok.extend_stk_len
  m6_to_jnz; apply wp_jnz_of <;> intro h_ar2
  · m6_steps; exact hQ (false, ()) s m rfl hlen ⟨rfl, hel, rfl⟩ hm
  · have hcr3 : cref.toNat + 3 ≤ s.core.arena_len := by
      rw [Arg.val_var, BitVec.ult, decide_eq_false_iff_not] at h_ar2
      bv_omega
    have hcr2_eq : (cref.setWidth 64 + 2#64).toNat = cref.toNat + 2 := by bv_omega
    have hcr2_lt : (cref.setWidth 64 + 2#64).toNat < s.core.arena.length := by
      rw [hcr2_eq, harl]; omega
    m6_to_jnz; apply wp_jnz_of <;> intro h_ar3
    · m6_steps; exact hQ (false, ()) s m rfl hlen ⟨rfl, hel, rfl⟩ hm
    · let sz32 := s.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr2_lt
      let sz := sz32.toNat
      have hsz32 : sz < 2 ^ 32 := sz32.isLt
      have hc3sz : cref.toNat + 3 + sz ≤ s.core.arena_len := by
        rw [Arg.val_var, BitVec.ult, decide_eq_false_iff_not] at h_ar3
        dsimp [sz, sz32] at h_ar3 ⊢; bv_omega
      let bl := blk_lit &&& 0x7FFFFFFF#32
      let nlits := 2 * s.core.cur_vars
      have hsh32 : ∀ x : BitVec 32, (x >>> (1 : Nat)).toNat = x.toNat / 2 := fun x => by
        simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      have hsh32b : ∀ x : BitVec 32, (x >>> 1#32).toNat = x.toNat / 2 := fun x => by
        simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      -- Pass 1: count `keep = m6KeepPrefixCount ... sz`
      m6_to_group
      refine wp_loop_inv
        (fun (keep, i, ()) m1 =>
          m1 = m ∧ i.toNat ≤ sz ∧
          keep.toNat =
            m6KeepPrefixCount s.core.arena s.core.vals s.core.lvl nlits cref.toNat bl i.toNat)
        (fun (_, i, ()) _ => sz - i.toNat) (fun J1 hLoop1 => ?_) ?_
      · m6_c0_steps
        exact hLoop1 (0#64, 0#32, ()) m ⟨rfl, Nat.zero_le _, rfl⟩
      · rintro J1 ⟨keep, i, ⟨⟩⟩ m1 ⟨rfl, hi_le, hkeep_eq⟩ hLoop1
        m6_to_jnz; apply wp_jnz_of <;> intro hc_i
        · have hi_lt : i.toNat < sz := by
            rw [Arg.val_var, BitVec.ult, decide_eq_true_eq] at hc_i; exact hc_i
          have hli_eq : (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat =
              cref.toNat + 3 + i.toNat := by bv_omega
          have hli_lt : (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat < s.core.arena.length := by
            rw [hli_eq, harl]; omega
          have hli_ar : cref.toNat + 3 + i.toNat < s.core.arena.length := by
            rw [← hli_eq]; exact hli_lt
          have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
          have hk_bd := m6KeepPrefixCount_le s.core.arena s.core.vals s.core.lvl nlits cref.toNat bl
            i.toNat
          have hk1_eq : (keep + 1#64).toNat = keep.toNat + 1 := by bv_omega
          let lit32 := (s.core.arena[cref.toNat + 3 + i.toNat]'hli_ar) &&& 0x7FFFFFFF#32
          m6_to_group
          refine wp_join_group (fun (keep', ()) m' =>
              m' = m1 ∧
              keep'.toNat = m6KeepPrefixCount s.core.arena s.core.vals s.core.lvl nlits
                cref.toNat bl (i.toNat + 1))
            (fun _ (keep', ()) m' ⟨hm', hkp'⟩ => by
              m6_c0_steps
              exact hLoop1 (keep', i + 1#32, ()) m' (by dsimp only; rw [hi1]; omega)
                ⟨hm', by rw [hi1]; omega, by rw [hi1]; exact hkp'⟩)
            (fun Jk hJk => ?_)
          m6_to_jnz; apply wp_jnz_of <;> intro hc_bl
          · have hne_b : (lit32 == bl) = false := by
              rw [Arg.val_var, bne_iff_ne] at hc_bl
              exact beq_false_of_ne (by simpa [lit32, bl, hli_eq] using hc_bl)
            m6_to_jnz; apply wp_jnz_of <;> intro hc_nl
            · have hlt_nl : lit32.toNat < nlits :=
                hot_lt_nlits_of_ult (by omega)
                  (by simpa [Arg.val_var, lit32, hli_eq] using hc_nl)
              have hmod64 : ∀ x : BitVec 32, (x.setWidth 64).toNat = x.toNat := fun x => by
                rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]
              have hlit_v : (lit32 >>> 1#32).toNat < s.core.lvl.length := by
                rw [hsh32b, hll]; omega
              have hlit_v64 :
                  (BitVec.setWidth 64
                    ((s.core.arena[(BitVec.setWidth 64 cref + 3 +
                      BitVec.setWidth 64 i).toNat]'hli_lt &&&
                      0x7FFFFFFF#32) >>> 1)).toNat < s.core.lvl.length := by
                simpa [lit32, hli_eq, hsh32, hmod64, Nat.shiftRight_eq_div_pow] using hlit_v
              have hlit_val : lit32.toNat < s.core.vals.length := by rw [hvl]; omega
              have hlit_val64 :
                  (BitVec.setWidth 64
                    (s.core.arena[(BitVec.setWidth 64 cref + 3 +
                      BitVec.setWidth 64 i).toNat]'hli_lt &&&
                      0x7FFFFFFF#32)).toNat < s.core.vals.length := by
                simpa [lit32, hli_eq, hmod64] using hlit_val
              m6_to_jnz; apply wp_jnz_of <;> intro hc_lv
              · have hlv0 : (s.core.lvl[lit32.toNat / 2]?.getD 0#32 == 0#32) = true := by
                  rw [List.getElem?_eq_getElem (by rw [hll]; omega), Option.getD_some]
                  simpa [Arg.val_var, lit32, hli_eq, hsh32, hmod64,
                    Nat.shiftRight_eq_div_pow] using hc_lv
                m6_to_jnz; apply wp_jnz_of <;> intro hc_va
                · have hslt : ((s.core.vals[lit32.toNat]?.getD 0#8).signExtend 32).slt 0#32 =
                      true := by
                    rw [List.getElem?_eq_getElem (by rw [hvl]; omega), Option.getD_some]
                    simpa [Arg.val_var, lit32, hli_eq, hmod64] using hc_va
                  have hsk_t : m6SkipLit s.core.vals s.core.lvl nlits bl lit32 = true := by
                    simp [m6SkipLit, hne_b, hlt_nl, hlv0, hslt]
                  m6_steps
                  exact hJk (keep, ()) m1 ⟨rfl, by rw [hkeep_eq, m6_ext_cl_step_true hli_ar hsk_t]⟩
                · have hnslt : ((s.core.vals[lit32.toNat]?.getD 0#8).signExtend 32).slt 0#32 =
                      false := by
                    rw [List.getElem?_eq_getElem (by rw [hvl]; omega), Option.getD_some]
                    simpa [Arg.val_var, lit32, hli_eq, hmod64] using hc_va
                  have hsk_f : m6SkipLit s.core.vals s.core.lvl nlits bl lit32 = false := by
                    simp [m6SkipLit, hne_b, hlt_nl, hlv0, hnslt]
                  m6_steps
                  exact hJk (keep + 1#64, ()) m1
                    ⟨rfl, by rw [hk1_eq, hkeep_eq, m6_ext_cl_step_false hli_ar hsk_f]⟩
              · have hlvne : (s.core.lvl[lit32.toNat / 2]?.getD 0#32 == 0#32) = false := by
                  rw [List.getElem?_eq_getElem (by rw [hll]; omega), Option.getD_some]
                  rw [Arg.val_var, beq_eq_false_iff_ne] at hc_lv
                  exact beq_false_of_ne
                    (by simpa [lit32, hli_eq, hsh32, hmod64, Nat.shiftRight_eq_div_pow] using hc_lv)
                have hsk_f : m6SkipLit s.core.vals s.core.lvl nlits bl lit32 = false := by
                  simp [m6SkipLit, hne_b, hlvne]
                m6_steps
                exact hJk (keep + 1#64, ()) m1
                  ⟨rfl, by rw [hk1_eq, hkeep_eq, m6_ext_cl_step_false hli_ar hsk_f]⟩
            · have hnlt : ¬ lit32.toNat < nlits :=
                not_hot_lt_nlits_of_ult (by omega)
                  (by simpa [Arg.val_var, lit32, hli_eq] using hc_nl)
              have hsk_f : m6SkipLit s.core.vals s.core.lvl nlits bl lit32 = false := by
                simp [m6SkipLit, hne_b, hnlt]
              m6_steps
              exact hJk (keep + 1#64, ()) m1
                ⟨rfl, by rw [hk1_eq, hkeep_eq, m6_ext_cl_step_false hli_ar hsk_f]⟩
          · have heq_b : (lit32 == bl) = true := by
              rw [Arg.val_var, bne_eq_false_iff_eq] at hc_bl
              exact beq_iff_eq.mpr (by simpa [lit32, bl, hli_eq] using hc_bl)
            have hsk_t : m6SkipLit s.core.vals s.core.lvl nlits bl lit32 = true := by
              simp [m6SkipLit, heq_b]
            m6_steps
            exact hJk (keep, ()) m1 ⟨rfl, by rw [hkeep_eq, m6_ext_cl_step_true hli_ar hsk_t]⟩
        · have hieq : i.toNat = sz := by
            rw [Arg.val_var, BitVec.ult, decide_eq_false_iff_not] at hc_i
            change ¬ i.toNat < sz at hc_i; omega
          have hk_fin : keep.toNat =
              m6KeepPrefixCount s.core.arena s.core.vals s.core.lvl nlits cref.toNat bl sz := by
            rwa [← hieq]
          have hk_bd := m6KeepPrefixCount_le
            s.core.arena s.core.vals s.core.lvl nlits cref.toNat bl sz
          m6_to_jnz; apply wp_jnz_of <;> intro hc_c1
          · m6_steps; exact hQ (false, ()) s m1 rfl hlen ⟨rfl, hel, rfl⟩ hm
          · have hel_le : s.scratch.extend_len ≤ c.extend_cap := by
              rw [Arg.val_var, BitVec.ult, decide_eq_false_iff_not] at hc_c1
              bv_omega
            m6_to_jnz; apply wp_jnz_of <;> intro hc_c2
            · m6_steps; exact hQ (false, ()) s m1 rfl hlen ⟨rfl, hel, rfl⟩ hm
            · have hext1k : s.scratch.extend_len + 1 +
                  m6KeepPrefixCount s.core.arena s.core.vals s.core.lvl nlits cref.toNat bl sz ≤
                  c.extend_cap := by
                rw [Arg.val_var, BitVec.ult, decide_eq_false_iff_not] at hc_c2
                rw [← hk_fin]; bv_omega
              have hp0_lt : (BitVec.ofNat 64 s.scratch.extend_len).toNat <
                  s.scratch.extend_stk.length := by rw [hesl]; bv_omega
              m6_to_group
              refine wp_loop_inv
                (fun ((i2 : BitVec 32), (p : BitVec 64), ()) m2 =>
                  i2.toNat ≤ sz ∧
                  p.toNat = s.scratch.extend_len + 1 +
                    m6KeepPrefixCount s.core.arena s.core.vals s.core.lvl nlits cref.toNat bl
                      i2.toNat ∧
                  ∃ ext2 : List (BitVec 32), ext2.length = c.extend_cap ∧
                    (FullMem c { s with scratch := { s.scratch with extend_stk := ext2 } } ⋆ R)
                      m2)
                (fun ((i2 : BitVec 32), (_ : BitVec 64), ()) _ => sz - i2.toNat)
                (fun J2 hLoop2 => ?_) ?_
              · let ext0 := s.scratch.extend_stk.set
                  (BitVec.ofNat 64 s.scratch.extend_len).toNat (bl ||| 0x80000000#32)
                m6_steps
                exact hLoop2 (0#32, BitVec.ofNat 64 s.scratch.extend_len + 1#64, ()) _
                  ⟨Nat.zero_le _,
                   by simp only [BitVec.toNat_zero, m6KeepPrefixCount_zero]; bv_omega,
                   ext0,
                   by simp [ext0, hesl], by assumption⟩
              · rintro J2 ⟨i2, p, ⟨⟩⟩ m2 ⟨hi2_le, hp_eq, ext2, hext2_len, hm2⟩ hLoop2
                m6_to_jnz; apply wp_jnz_of <;> intro hc_i2
                · have hi2_lt : i2.toNat < sz := by
                    rw [Arg.val_var, BitVec.ult, decide_eq_true_eq] at hc_i2
                    change i2.toNat < sz at hc_i2; exact hc_i2
                  have hli_eq : (cref.setWidth 64 + 3#64 + i2.setWidth 64).toNat =
                      cref.toNat + 3 + i2.toNat := by bv_omega
                  have hli_lt : (cref.setWidth 64 + 3#64 + i2.setWidth 64).toNat <
                      s.core.arena.length := by rw [hli_eq, harl]; omega
                  have hli_ar : cref.toNat + 3 + i2.toNat < s.core.arena.length := by
                    rw [← hli_eq]; exact hli_lt
                  have hi2_1 : (i2 + 1#32).toNat = i2.toNat + 1 := by bv_omega
                  have hk_step_bd := m6KeepPrefixCount_le s.core.arena s.core.vals s.core.lvl nlits
                    cref.toNat bl (i2.toNat + 1)
                  have hk_mono := m6KeepPrefixCount_mono s.core.arena s.core.vals s.core.lvl nlits
                    cref.toNat bl (show i2.toNat + 1 ≤ sz by omega)
                  let s2 : FullState :=
                    { s with scratch := { s.scratch with extend_stk := ext2 } }
                  let lit_raw :=
                    (s.core.arena[(BitVec.setWidth 64 cref + 3 +
                      BitVec.setWidth 64 i2).toNat]'hli_lt) &&& 0x7FFFFFFF#32
                  let lit32 := (s.core.arena[cref.toNat + 3 + i2.toNat]'hli_ar) &&& 0x7FFFFFFF#32
                  m6_to_group
                  refine wp_join_group (fun (p', ()) m' =>
                      p'.toNat = s.scratch.extend_len + 1 +
                        m6KeepPrefixCount s.core.arena s.core.vals s.core.lvl nlits cref.toNat bl
                          (i2.toNat + 1) ∧
                      ∃ ext' : List (BitVec 32), ext'.length = c.extend_cap ∧
                        (FullMem c { s with scratch := { s.scratch with extend_stk := ext' } } ⋆ R)
                          m')
                    (fun _ (p', ()) m' ⟨hp'eq, ext', hext'_len, hm'⟩ => by
                      m6_steps
                      exact hLoop2 (i2 + 1#32, p', ()) m' (by dsimp only; rw [hi2_1]; omega)
                        ⟨by rw [hi2_1]; omega, by rw [hi2_1]; exact hp'eq, ext', hext'_len, hm'⟩)
                    (fun Jp hJp => ?_)
                  m6_to_jnz; apply wp_jnz_of <;> intro hc_bl2
                  · have hne_b : (lit32 == bl) = false := by
                      rw [Arg.val_var, bne_iff_ne] at hc_bl2
                      exact beq_false_of_ne (by simpa [lit32, bl, hli_eq] using hc_bl2)
                    m6_to_jnz; apply wp_jnz_of <;> intro hc_nl2
                    · have hlt_nl : lit32.toNat < nlits :=
                        hot_lt_nlits_of_ult (by omega)
                          (by simpa [Arg.val_var, lit32, hli_eq] using hc_nl2)
                      have hmod64 : ∀ x : BitVec 32, (x.setWidth 64).toNat = x.toNat :=
                        fun x => by
                          rw [BitVec.toNat_setWidth,
                            Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]
                      have hlit_v : (lit32 >>> 1#32).toNat < s2.core.lvl.length := by
                        dsimp [s2]
                        simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hll]
                        change lit32.toNat / 2 < c.max_vars; omega
                      have hlit_v64 :
                          (BitVec.setWidth 64
                            ((s.core.arena[(BitVec.setWidth 64 cref + 3 +
                              BitVec.setWidth 64 i2).toNat]'hli_lt &&&
                              0x7FFFFFFF#32) >>> 1)).toNat < s2.core.lvl.length := by
                        simpa [s2, lit32, hli_eq, hsh32, hmod64,
                          Nat.shiftRight_eq_div_pow] using hlit_v
                      have hlit_val : lit32.toNat < s2.core.vals.length := by
                        dsimp [s2]; rw [hvl]; omega
                      have hlit_val64 :
                          (BitVec.setWidth 64
                            (s.core.arena[(BitVec.setWidth 64 cref + 3 +
                              BitVec.setWidth 64 i2).toNat]'hli_lt &&&
                              0x7FFFFFFF#32)).toNat < s2.core.vals.length := by
                        simpa [s2, lit32, hli_eq, hmod64] using hlit_val
                      m6_to_jnz; apply wp_jnz_of <;> intro hc_lv2
                      · have hlv0 : (s.core.lvl[lit32.toNat / 2]?.getD 0#32 == 0#32) = true := by
                          rw [List.getElem?_eq_getElem (by rw [hll]; omega), Option.getD_some]
                          simpa [Arg.val_var, lit32, hli_eq, hsh32, hmod64,
                            Nat.shiftRight_eq_div_pow] using hc_lv2
                        m6_to_jnz; apply wp_jnz_of <;> intro hc_va2
                        · have hslt : ((s.core.vals[lit32.toNat]?.getD 0#8).signExtend 32).slt 0#32
                              = true := by
                            rw [List.getElem?_eq_getElem (by rw [hvl]; omega), Option.getD_some]
                            simpa [Arg.val_var, lit32, hli_eq, hmod64] using hc_va2
                          have hsk_t : m6SkipLit s.core.vals s.core.lvl nlits bl lit32 = true := by
                            simp [m6SkipLit, hne_b, hlt_nl, hlv0, hslt]
                          m6_steps
                          exact hJp (p, ()) m2
                            ⟨by rw [hp_eq, m6_ext_cl_step_true hli_ar hsk_t],
                             ext2, hext2_len, hm2⟩
                        · have hnslt : ((s.core.vals[lit32.toNat]?.getD 0#8).signExtend 32).slt
                              0#32 = false := by
                            rw [List.getElem?_eq_getElem (by rw [hvl]; omega), Option.getD_some]
                            simpa [Arg.val_var, lit32, hli_eq, hmod64] using hc_va2
                          have hsk_f : m6SkipLit s.core.vals s.core.lvl nlits bl lit32 = false := by
                            simp [m6SkipLit, hne_b, hlt_nl, hlv0, hnslt]
                          have hp_lt_cap : p.toNat < c.extend_cap := by
                            have h0 := m6_ext_cl_step_false hli_ar hsk_f
                            omega
                          have hp_lt_ext2 : p.toNat < ext2.length := by
                            rw [hext2_len]; exact hp_lt_cap
                          have hp1_eq : (p + 1#64).toNat = p.toNat + 1 := by bv_omega
                          m6_steps
                          exact hJp (p + 1#64, ()) _
                            ⟨by rw [hp1_eq, hp_eq, m6_ext_cl_step_false hli_ar hsk_f]; omega,
                             ext2.set p.toNat lit_raw, by rw [List.length_set, hext2_len],
                             by assumption⟩
                      · have hlvne : (s.core.lvl[lit32.toNat / 2]?.getD 0#32 == 0#32) = false := by
                          rw [List.getElem?_eq_getElem (by rw [hll]; omega), Option.getD_some]
                          rw [Arg.val_var, beq_eq_false_iff_ne] at hc_lv2
                          exact beq_false_of_ne
                            (by simpa [lit32, hli_eq, hsh32, hmod64,
                              Nat.shiftRight_eq_div_pow] using hc_lv2)
                        have hsk_f : m6SkipLit s.core.vals s.core.lvl nlits bl lit32 = false := by
                          simp [m6SkipLit, hne_b, hlvne]
                        have hp_lt_cap : p.toNat < c.extend_cap := by
                          have h0 := m6_ext_cl_step_false hli_ar hsk_f
                          omega
                        have hp_lt_ext2 : p.toNat < ext2.length := by
                          rw [hext2_len]; exact hp_lt_cap
                        have hp1_eq : (p + 1#64).toNat = p.toNat + 1 := by bv_omega
                        m6_steps
                        exact hJp (p + 1#64, ()) _
                          ⟨by rw [hp1_eq, hp_eq, m6_ext_cl_step_false hli_ar hsk_f]; omega,
                           ext2.set p.toNat lit_raw, by rw [List.length_set, hext2_len],
                           by assumption⟩
                    · have hnlt : ¬ lit32.toNat < nlits :=
                        not_hot_lt_nlits_of_ult (by omega)
                          (by simpa [Arg.val_var, lit32, hli_eq] using hc_nl2)
                      have hsk_f : m6SkipLit s.core.vals s.core.lvl nlits bl lit32 = false := by
                        simp [m6SkipLit, hne_b, hnlt]
                      have hp_lt_cap : p.toNat < c.extend_cap := by
                        have h0 := m6_ext_cl_step_false hli_ar hsk_f
                        omega
                      have hp_lt_ext2 : p.toNat < ext2.length := by
                        rw [hext2_len]; exact hp_lt_cap
                      have hp1_eq : (p + 1#64).toNat = p.toNat + 1 := by bv_omega
                      m6_steps
                      exact hJp (p + 1#64, ()) _
                        ⟨by rw [hp1_eq, hp_eq, m6_ext_cl_step_false hli_ar hsk_f]; omega,
                         ext2.set p.toNat lit_raw, by rw [List.length_set, hext2_len],
                         by assumption⟩
                  · have heq_b : (lit32 == bl) = true := by
                      rw [Arg.val_var, bne_eq_false_iff_eq] at hc_bl2
                      exact beq_iff_eq.mpr (by simpa [lit32, bl, hli_eq] using hc_bl2)
                    have hsk_t : m6SkipLit s.core.vals s.core.lvl nlits bl lit32 = true := by
                      simp [m6SkipLit, heq_b]
                    m6_steps
                    exact hJp (p, ()) m2
                      ⟨by rw [hp_eq, m6_ext_cl_step_true hli_ar hsk_t], ext2, hext2_len, hm2⟩
                · have hi2_eq : i2.toNat = sz := by
                    rw [Arg.val_var, BitVec.ult, decide_eq_false_iff_not] at hc_i2
                    change ¬ i2.toNat < sz at hc_i2; omega
                  have hp_fin : p.toNat ≤ c.extend_cap := by
                    rw [hi2_eq] at hp_eq; omega
                  m6_steps
                  let s' : FullState :=
                    { s with scratch :=
                      { s.scratch with extend_stk := ext2, extend_len := p.toNat } }
                  exact hQ (true, ()) s' _ rfl
                    (hlen.with_scratch { hlen.scratch_ok with extend_stk_len := hext2_len })
                    ⟨rfl, hp_fin, rfl⟩ (by assumption)

/-! ## 5. Closed `25`-Row `m6WatchGcEnv` `TableImpl`, `ModuleOk`, & UNSAT Non-Vacuity -/

/-- Closed `25`-row specification table for `m6WatchGcModule` (`17` overrides + `8` externs),
certifying directly against canonical `Full` specs (`fullFlushTrailSpec` & `m6IngestClSpec` for
the two new M6 entry points). -/
def m6WatchGcSpecTable : List SpecEntry :=
  [ ⟨"full_wstack_radix_sort_m6", [i64, i64, i64, i64, i64, i64], [],
      fullWstackRadixSortSpec, true⟩
  , ⟨"full_wstack_defrag_m6", [i64], [], Full.fullWstackDefragSpec, true⟩
  , ⟨"full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
  , ⟨"full_lit_rank_m6", [i64, i64, i32], [i64], Full.fullLitRankSpec, true⟩
  , ⟨"full_sweep_bins_range_m6", [i64, i64], [], fullSweepBinsRangeSpec, true⟩
  , ⟨"full_sweep_bins_m6", [i64], [], Full.fullSweepBinsSpec, true⟩
  , ⟨"full_rewatch_range_m6", [i64, i64, i64], [.bool], fullRewatchRangeSpec, true⟩
  , ⟨"full_rewatch_arena_m6", [i64, i64], [.bool], Full.fullRewatchArenaSpec, true⟩
  , ⟨"full_move_red_pass2_m6", [i64, i64, i64, i64, i64], [], fullMoveRedPass2Spec, true⟩
  , ⟨"full_move_red_end_buf_m6", [i64, i64, i64, i64], [], fullMoveRedEndBufSpec, true⟩
  , ⟨"full_move_red_end_m6", [i64, i64, i64], [], fullMoveRedEndSpec, true⟩
  , ⟨"full_arena_sweep_m6", [i64], [i64], Full.fullArenaSweepSpec, true⟩
  , ⟨"full_mark_reasons_m6", [i64, .bool], [], Full.fullMarkReasonsSpec, true⟩
  , ⟨"full_flush_trail_m6", [i64], [i64], fullFlushTrailSpec, true⟩
  , ⟨"full_parse_body_m6", [i64, i64], [i64], Full.fullParseBodySpec, true⟩
  , ⟨"full_extend_push2_m6", [i64, i32, i32], [.bool], Full.fullExtendPush2Spec, true⟩
  , ⟨"full_extend_push_cl_m6", [i64, i32, i32], [.bool], Full.fullExtendPushClSpec, true⟩
  , ⟨"full_wsort_sift", [i64, i64, i64, i64], [], Full.fullWsortSiftSpec, true⟩
  , ⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩
  , ⟨"full_sweep_copy", [i64, i64, i64, i32, .bool], [i64], Full.fullSweepCopySpec, true⟩
  , ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩
  , ⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩
  , ⟨"full_ingest_cl", [i64, i64], [i64], m6IngestClSpec, true⟩
  , ⟨"full_skip_cl", [i64, i64], [.bool], Full.fullSkipClSpec, true⟩
  , ⟨"kissat_skip_ws_comments", [i64, i64], [i64], kissatSkipWsCommentsSpec, true⟩
  ]

/-- Closed specification environment for `m6WatchGcModule`. -/
def m6WatchGcEnv : Env := Env.ofTable m6WatchGcSpecTable

theorem m6WatchGcSpecTable_noExit : ∀ e ∈ m6WatchGcSpecTable, e.noExit = true := by
  intro e he
  simp only [m6WatchGcSpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rfl

theorem m6WatchGc_noExit :
    ∀ f as bs xs m Q X X',
      m6WatchGcEnv f as bs xs m Q X → m6WatchGcEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m6WatchGcSpecTable_noExit

private theorem m6WatchGcSpecTable_nodup :
    (m6WatchGcSpecTable.map SpecEntry.name).Nodup := by
  show (["full_wstack_radix_sort_m6", "full_wstack_defrag_m6", "full_watch_push_m6",
    "full_lit_rank_m6", "full_sweep_bins_range_m6", "full_sweep_bins_m6",
    "full_rewatch_range_m6", "full_rewatch_arena_m6", "full_move_red_pass2_m6",
    "full_move_red_end_buf_m6", "full_move_red_end_m6", "full_arena_sweep_m6",
    "full_mark_reasons_m6", "full_flush_trail_m6", "full_parse_body_m6",
    "full_extend_push2_m6", "full_extend_push_cl_m6",
    "full_wsort_sift", "full_arena_next", "full_sweep_copy", "full_backtrack",
    "full_propagate", "full_ingest_cl", "full_skip_cl",
    "kissat_skip_ws_comments"] : List String).Nodup
  decide

private theorem m6WatchGcEnv_row_at (i : Nat) (e : SpecEntry)
    (hi : m6WatchGcSpecTable[i]? = some e := by rfl)
    (hne : e.noExit = true := by rfl)
    (hx : ∀ xs m Q X X', e.spec xs m Q X → e.spec xs m Q X' := by
      intro _ _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → m6WatchGcEnv e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) m6WatchGcSpecTable_nodup
      (by simp only [SpecEntry.eff, hne, ite_true]; exact hx _ _ _ _ _ h)

private theorem m6_allFns_of_forall {P : Fn → Prop} :
    ∀ {fs : List Fn}, (∀ f ∈ fs, P f) → AllFns P fs
  | [], _ => trivial
  | _ :: _, h =>
    ⟨h _ List.mem_cons_self, m6_allFns_of_forall fun f hf => h f (List.mem_cons_of_mem _ hf)⟩

/-- Row-by-row `TableImpl` for all `17` functions in `m6WatchGc_fns`. -/
theorem m6WatchGc_tableImpl :
    TableImpl m6WatchGcEnv m6WatchGc_fns m6WatchGcSpecTable := by
  let hRadix := m6WatchGcEnv_row_at 0
    ⟨"full_wstack_radix_sort_m6", [i64, i64, i64, i64, i64, i64], [],
      fullWstackRadixSortSpec, true⟩
    (hx := fun _ _ _ _ _ h => fullWstackRadixSortSpec_xirrel h)
  let hDefrag := m6WatchGcEnv_row_at 1
    ⟨"full_wstack_defrag_m6", [i64], [], Full.fullWstackDefragSpec, true⟩
  let hPush := m6WatchGcEnv_row_at 2
    ⟨"full_watch_push_m6", [i64, i32, i32, i32, i32], [.bool], Full.fullWatchPushSpec, true⟩
  let hRank := m6WatchGcEnv_row_at 3
    ⟨"full_lit_rank_m6", [i64, i64, i32], [i64], Full.fullLitRankSpec, true⟩
  let hSweepR := m6WatchGcEnv_row_at 4
    ⟨"full_sweep_bins_range_m6", [i64, i64], [], fullSweepBinsRangeSpec, true⟩
    (hx := fun _ _ _ _ _ h => fullSweepBinsRangeSpec_xirrel h)
  let hRewatchR := m6WatchGcEnv_row_at 6
    ⟨"full_rewatch_range_m6", [i64, i64, i64], [.bool], fullRewatchRangeSpec, true⟩
    (hx := fun _ _ _ _ _ h => fullRewatchRangeSpec_xirrel h)
  let hPass2 := m6WatchGcEnv_row_at 8
    ⟨"full_move_red_pass2_m6", [i64, i64, i64, i64, i64], [], fullMoveRedPass2Spec, true⟩
    (hx := fun _ _ _ _ _ h => fullMoveRedPass2Spec_xirrel h)
  let hMoveBuf := m6WatchGcEnv_row_at 9
    ⟨"full_move_red_end_buf_m6", [i64, i64, i64, i64], [], fullMoveRedEndBufSpec, true⟩
    (hx := fun _ _ _ _ _ h => fullMoveRedEndBufSpec_xirrel h)
  let hMove := m6WatchGcEnv_row_at 10
    ⟨"full_move_red_end_m6", [i64, i64, i64], [], fullMoveRedEndSpec, true⟩
    (hx := fun _ _ _ _ _ h => fullMoveRedEndSpec_xirrel h)
  let hSift := m6WatchGcEnv_row_at 17
    ⟨"full_wsort_sift", [i64, i64, i64, i64], [], Full.fullWsortSiftSpec, true⟩
  let hNext := m6WatchGcEnv_row_at 18
    ⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩
  let hCopy := m6WatchGcEnv_row_at 19
    ⟨"full_sweep_copy", [i64, i64, i64, i32, .bool], [i64], Full.fullSweepCopySpec, true⟩
  let hBack := m6WatchGcEnv_row_at 20
    ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩
  let hProp := m6WatchGcEnv_row_at 21
    ⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩
  let hIngest := m6WatchGcEnv_row_at 22
    ⟨"full_ingest_cl", [i64, i64], [i64], m6IngestClSpec, true⟩
  let hSkip := m6WatchGcEnv_row_at 23
    ⟨"full_skip_cl", [i64, i64], [.bool], Full.fullSkipClSpec, true⟩
  let hSwc := m6WatchGcEnv_row_at 24
    ⟨"kissat_skip_ws_comments", [i64, i64], [i64], kissatSkipWsCommentsSpec, true⟩
  exact ⟨.of (full_wstack_radix_sort_m6_wp m6WatchGcEnv),
    ⟨.of (full_wstack_defrag_m6_wp m6WatchGcEnv hSift hRadix),
    ⟨.of (full_watch_push_m6_wp m6WatchGcEnv hDefrag),
    ⟨.of (full_lit_rank_m6_wp m6WatchGcEnv),
    ⟨.of (full_sweep_bins_range_m6_wp m6WatchGcEnv hDefrag),
    ⟨.of (full_sweep_bins_m6_wp m6WatchGcEnv hSweepR),
    ⟨.of (full_rewatch_range_m6_wp m6WatchGcEnv hRank hPush),
    ⟨.of (full_rewatch_arena_m6_wp m6WatchGcEnv hRewatchR),
    ⟨.of (full_move_red_pass2_m6_wp m6WatchGcEnv),
    ⟨.of (full_move_red_end_buf_m6_wp m6WatchGcEnv hPass2),
    ⟨.of (full_move_red_end_m6_wp m6WatchGcEnv hMoveBuf),
    ⟨.of (full_arena_sweep_m6_wp m6WatchGcEnv hSweepR hNext hCopy hMove hRewatchR),
    ⟨.of (full_mark_reasons_m6_wp m6WatchGcEnv),
    ⟨.of (full_flush_trail_m6_wp m6WatchGcEnv hBack hProp),
    ⟨.of (full_parse_body_m6_wp m6WatchGcEnv hSkip hIngest hProp hSwc),
    ⟨.of (full_extend_push2_m6_wp m6WatchGcEnv),
    ⟨.of (full_extend_push_cl_m6_wp m6WatchGcEnv), trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- Closed `ModuleOk` for `m6WatchGcModule` (`17` fns + `8` externs) under `m6WatchGcEnv`. -/
theorem m6WatchGc_moduleOk : ModuleOk m6WatchGcEnv m6WatchGcModule :=
  Env.ofTable_moduleOk m6WatchGc_acyclic (m6_allFns_of_forall m6WatchGc_fns_wf)
    m6WatchGc_tableImpl

/-- Concrete `Mem 64` UNSAT soundness/non-vacuity for `full_flush_trail_m6_body` under closed
`m6WatchGcEnv` (`XPost := fun _ _ _ _ => False`): exercises `nvFastPropMem` and derives
`Full.nvOneLitF0.Unsat` on conflict return (`r = 20#64`). -/
theorem nv_m6_watch_gc_sound :
    Func.wp m6WatchGcEnv full_flush_trail_m6_body (FastCore.nvFastPropCfg.hdr, ())
      FastCore.nvFastPropMem
      (fun (r, ()) m' =>
        (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) ∧
        (r = 20#64 → Full.nvOneLitF0.Unsat) ∧
        ∃ s', (FullMem FastCore.nvFastPropCfg s' ⋆ emp) m')
      (fun _ _ _ _ => False) := by
  let hBack := m6WatchGcEnv_row_at 20
    ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩
  let hProp := m6WatchGcEnv_row_at 21
    ⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩
  apply full_flush_trail_m6_wp m6WatchGcEnv hBack hProp
  refine ⟨FastCore.nvFastPropCfg, Full.nvOneLitF0, [[0], [1]], FastCore.nvFastPropState, emp,
    rfl, FastCore.nvFastProp_lengths, FastCore.nvFastProp_witness, rfl,
    by rw [sep_emp]; exact FastCore.nvFastPropMem_ok, ?_⟩
  intro r s' m' _ _ _ _ _ hr h20 _ hm'
  exact ⟨hr, h20, s', hm'⟩

end LeanQbe.T.Examples.Kissat.FullM6WatchGc

