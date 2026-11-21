module

public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas1
public import LeanQbe.T.Examples.Kissat.FullSccLemmas2
public import LeanQbe.T.Examples.Kissat.FullBveVarLemmas2
public import LeanQbe.T.Examples.Kissat.FullDeduce1UipNv
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` M2 Tier-A BVE / Tarjan / Budgeted Inprocessing — Hub (`Part 2`)

Re-exports `FullFastBveBudgetsLemmas1` (`TmkZero`, `FullDefGateUnsat`, gate soundness, upgraded
specs, and `fast_{init_hdr,forward_sub,transitive,vivify,probe_run}_wp`) and completes:
- Section 7: `fast_tarjan_scc_wp` & `fast_tarjan_scc_canon_wp` (`tmk`/`trc` zeroing → `TmkZero`)
- Section 8: `fast_bve_var_wp` & `fast_bve_var_def_wp` (`64u` occ cap + `P_ng × N_ng` gate skip)
- Section 9: Closed 28-row `fastBveBudgetsEnv`, `fastBveBudgets_moduleOk`, and concrete `Mem 64`
  UNSAT non-vacuity (`XPost := False`) for all `7` upgraded functions.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullFastBveBudgets

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 7. `fast_tarjan_scc_wp` (exit cleanup `tmk[i] = 0; trc[i] = 0;` → `TmkZero`) -/

section TarjanSccProof

open FullSccSpecs FullSccHelpers
open scoped FullArenaTactics FullSccTactics

private theorem scc_getElem_congr {α : Type} {xs : List α} {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) (h : i = j) : xs[i] = xs[j] := by subst h; rfl

private theorem scc_bv64_add {x y : BitVec 64} (h : x.toNat + y.toNat < 2 ^ 64) :
    (x + y).toNat = x.toNat + y.toNat := by rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]
private theorem scc_bv64_add1 {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 :=
  (scc_bv64_add (y := 1#64) (by simpa using h)).trans (by simp)
private theorem scc_bv32_add1 {x : BitVec 32} (h : x.toNat + 1 < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt h]
private theorem scc_bv32_add2 {x : BitVec 32} (h : x.toNat + 2 < 2 ^ 32) :
    (x + 2#32).toNat = x.toNat + 2 := by
  rw [BitVec.toNat_add, show (2#32 : BitVec 32).toNat = 2 from rfl, Nat.mod_eq_of_lt h]
private theorem scc_ult_false_ge {w : Nat} {x y : BitVec w} (h : x.ult y = false) :
    y.toNat ≤ x.toNat :=
  Nat.le_of_not_lt fun hlt => by
    have := BitVec.ult_iff_lt.mpr (BitVec.lt_def.mpr hlt); rw [this] at h; cases h

private theorem scc_dpos_step_nonbin {F_cur : List (List Nat)} {s0 st : FullState}
    {nl off sz pos pos2 : Nat} (hpos_lt : pos < sz) (hpos2 : pos2 = pos + 2)
    (hslc : WatchSliceOk F_cur s0.core nl (off + pos) (sz - pos))
    (hflag0 : (s0.core.wstk[off + pos]?.getD 0#32 &&& 0x80000000#32) = 0#32)
    (hsc : ∃ sc, sliceBinsFrom s0.core.wstk off sz =
        sc ++ sliceBinsFrom s0.core.wstk (off + pos) (sz - pos) ∧
      ∀ x ∈ sc, activeLit s0 x → 1 ≤ (st.scratch.tarjan_mark[x]?.getD 0#32).toNat) :
    pos2 ≤ sz ∧ WatchSliceOk F_cur s0.core nl (off + pos2) (sz - pos2) ∧
    ∃ sc, sliceBinsFrom s0.core.wstk off sz =
        sc ++ sliceBinsFrom s0.core.wstk (off + pos2) (sz - pos2) ∧
      ∀ x ∈ sc, activeLit s0 x → 1 ≤ (st.scratch.tarjan_mark[x]?.getD 0#32).toNat := by
  obtain ⟨_, _, h2le, _, _, _, _, _, hrest, hbins_eq⟩ :=
    watchSlice_step_nonbin hslc (by omega) hflag0
  obtain ⟨sc, hseq, hsok⟩ := hsc; refine ⟨by omega, ?_, sc, ?_, hsok⟩
  · rw [show off + pos2 = off + pos + 2 by omega, show sz - pos2 = sz - pos - 2 by omega]
    exact hrest
  · rw [hseq, hbins_eq, show off + pos2 = off + pos + 2 by omega,
      show sz - pos2 = sz - pos - 2 by omega]

private theorem scc_dpos_step_bin {F_cur : List (List Nat)} {s0 st : FullState}
    {nl off sz pos pos1 : Nat} (hpos_lt : pos < sz) (hpos1 : pos1 = pos + 1)
    (hslc : WatchSliceOk F_cur s0.core nl (off + pos) (sz - pos))
    (hflag1 : (s0.core.wstk[off + pos]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32)
    (hsc : ∃ sc, sliceBinsFrom s0.core.wstk off sz =
        sc ++ sliceBinsFrom s0.core.wstk (off + pos) (sz - pos) ∧
      ∀ x ∈ sc, activeLit s0 x → 1 ≤ (st.scratch.tarjan_mark[x]?.getD 0#32).toNat) :
    ∃ w0, s0.core.wstk[off + pos]? = some w0 ∧
      (w0 &&& 0x7FFFFFFF#32).toNat < 2 * s0.core.cur_vars ∧
      (w0 &&& 0x7FFFFFFF#32).toNat ∈ sliceBinsFrom s0.core.wstk off sz ∧
      pos1 ≤ sz ∧ WatchSliceOk F_cur s0.core nl (off + pos1) (sz - pos1) ∧
      ∃ sc, sliceBinsFrom s0.core.wstk off sz =
          sc ++ sliceBinsFrom s0.core.wstk (off + pos1) (sz - pos1) ∧
        ∀ x ∈ sc, activeLit s0 x →
          x = (w0 &&& 0x7FFFFFFF#32).toNat ∨ 1 ≤ (st.scratch.tarjan_mark[x]?.getD 0#32).toNat := by
  obtain ⟨w0, hw0_eq, _, _, hot_lt, _, hrest, hbins_eq⟩ :=
    watchSlice_step_bin hslc (by omega) hflag1
  obtain ⟨sc, hseq, hsok⟩ := hsc
  refine ⟨w0, hw0_eq, hot_lt,
    by rw [hseq, hbins_eq, List.mem_append, List.mem_cons]; exact Or.inr (Or.inl rfl),
    by omega, ?_, sc ++ [(w0 &&& 0x7FFFFFFF#32).toNat], ?_, fun x hx hax => ?_⟩
  · rw [show off + pos1 = off + pos + 1 by omega, show sz - pos1 = sz - pos - 1 by omega]
    exact hrest
  · rw [hseq, hbins_eq, List.append_assoc, List.singleton_append,
      show off + pos1 = off + pos + 1 by omega, show sz - pos1 = sz - pos - 1 by omega]
  · rcases List.mem_append.mp hx with h1 | h2
    · exact Or.inr (hsok x h1 hax)
    · simp only [List.mem_singleton] at h2; exact Or.inl h2

private theorem scc_pop_call_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s0 st3 : FullState}
    {R : Mem 64 → Prop} {m3 : Mem 64} {root dsp : BitVec 64} {reached rch lit mr : BitVec 32}
    {failb : Bool} {k0 : Nat} {Jpop : Cont [.bool]}
    (hPop : ∀ args m Q X, Full.fullTarjanPopSccSpec args m Q X →
      Γ "full_tarjan_pop_scc" [i64, i32, i32, i32] [.bool] args m Q X)
    (hw0 : FullWitnessInv c F0 F_cur s0.core) (hinc30 : st3.core.inconsistent = 0#64)
    (hdsp_pos : 0 < dsp.toNat) (hrt_lt : root.toNat < 2 * s0.core.cur_vars)
    (hlit_lt : lit.toNat < 2 * s0.core.cur_vars)
    (hd3 : TarjanDfsInv c F0 F_cur s0 root.toNat (reached.toNat + 1) rch.toNat dsp.toNat st3)
    (hlit_get : lit = st3.scratch.work_stk2[dsp.toNat - 1]?.getD 0#32)
    (hk0_lt : k0 < st3.core.tmp_cnt)
    (hk0_bv : st3.scratch.work_stk1[k0]?.getD 0#32 =
      st3.scratch.work_stk2[dsp.toNat - 1]?.getD 0#32)
    (hk0_uniq : ∀ j, k0 < j → j < st3.core.tmp_cnt →
      st3.scratch.work_stk1[j]?.getD 0#32 ≠ st3.scratch.work_stk2[dsp.toNat - 1]?.getD 0#32)
    (hk0_zero : dsp.toNat = 1 → k0 = 0)
    (hk0_eqv : ∀ j, k0 ≤ j → j < st3.core.tmp_cnt →
      LitEquiv (cnfOfClauses F_cur) (st3.scratch.work_stk1[j]?.getD 0#32).toNat
        (st3.scratch.work_stk2[dsp.toNat - 1]?.getD 0#32).toNat)
    (hmr_reach : mr ≠ 0xFFFFFFFF#32 →
      (∀ j, k0 ≤ j → j < st3.core.tmp_cnt → BinReach (cnfOfClauses F_cur)
        (BitVec.setWidth 32 root).toNat (st3.scratch.work_stk1[j]?.getD 0#32).toNat) ∧
      (∀ l < 2 * st3.core.cur_vars,
        mr.toNat ≤ (st3.scratch.tarjan_mark[l]?.getD 0#32).toNat →
        BinReach (cnfOfClauses F_cur) (BitVec.setWidth 32 root).toNat l))
    (hm3 : (FullMem c st3 ⋆ R) m3)
    (hPopJ : ∀ (b : Bool) mj, (∃ st4 : FullState, TarjanLoopBase c F_cur s0 st4 ∧
      (st4.core.inconsistent = 0#64 →
        TarjanDfsInv c F0 F_cur s0 root.toNat (reached.toNat + 1) rch.toNat (dsp.toNat - 1) st4 ∧
        TarjanDfsInv.measure c s0 st4 rch.toNat (dsp.toNat - 1) <
          TarjanDfsInv.measure c s0 st3 rch.toNat dsp.toNat ∧
        (dsp.toNat - 1 = 0 → st4.core.tmp_cnt = 0)) ∧ (FullMem c st4 ⋆ R) mj) →
      Jpop (b, ()) mj) :
    wp Γ Q X (Expr.call (as := [i64, i32, i32, i32]) (bs := [.bool]) "full_tarjan_pop_scc"
      (Arg.var c.hdr, Arg.var (BitVec.setWidth 32 root), Arg.var lit, Arg.var mr, ()) fun p =>
        Expr.jnz (Arg.var p.fst)
          (Expr.jump Jpop (Arg.imm true, ())) (Expr.jump Jpop (Arg.var failb, ()))) m3 := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv3 := hd3.agrees.get (·.core.cur_vars); have hcv_le := hd3.len_ok.core_ok.cur_vars_le
  have hk0_nat : (st3.scratch.work_stk1[k0]?.getD 0#32).toNat = lit.toNat := by
    rw [hk0_bv, ← hlit_get]
  scc_call hPop
  refine ⟨c, F0, F_cur, st3, k0, R, rfl, hd3.len_ok,
    tarjanScc_preserves_witness hw0 hd3.agrees (fun h => absurd hinc30 h), hinc30,
    by rw [bv32_trunc_toNat (by omega), hcv3]; exact hrt_lt, by rw [hcv3]; exact hlit_lt,
    by have := hd3.top_le; have := hd3.reached_le; rw [hcv3]; omega, hd3.rsz_le, hk0_lt,
    by rw [hk0_bv, ← hlit_get], fun j h1 h2 => by rw [hlit_get]; exact hk0_uniq j h1 h2,
    fun j hj => by rw [hcv3]; exact hd3.scc_lt j hj,
    fun j h1 h2 => by rw [hlit_get]; exact hk0_eqv j h1 h2,
    hd3.partial_repr, hd3.units_ok, hmr_reach, hm3, ?_⟩
  intro _ st4 m4 hag_p htop4 hlen4 _ hrsz4 hpr4 hus4 _ hinc4_u hinc4_eff hm4
  have hbase4 : TarjanLoopBase c F_cur s0 st4 :=
    ⟨agrees_popScc_to_tarjan hd3.agrees hag_p, hlen4, hrsz4, hpr4, hus4, hinc4_u⟩
  have hd4_fn : st4.core.inconsistent = 0#64 →
      TarjanDfsInv c F0 F_cur s0 root.toNat (reached.toNat + 1) rch.toNat (dsp.toNat - 1) st4 ∧
      TarjanDfsInv.measure c s0 st4 rch.toNat (dsp.toNat - 1) <
        TarjanDfsInv.measure c s0 st3 rch.toNat dsp.toNat ∧
      (dsp.toNat - 1 = 0 → st4.core.tmp_cnt = 0) := fun h40 => by
    obtain ⟨hset, hkeep⟩ := hinc4_eff h40
    obtain ⟨hd4, hm4_lt⟩ := tarjan_pop_root_after hd3 hdsp_pos hk0_lt
      (by rw [hk0_nat, ← hlit_get]) hag_p htop4 hlen4 h40 hrsz4 hpr4 hus4
      (fun j h1 h2 => (hset j h1 h2).2) (fun l hl hall => (hkeep l (by omega) hall).2)
    exact ⟨hd4, hm4_lt, fun hz => by rw [htop4]; exact hk0_zero (by omega)⟩
  scc_steps
  · exact hPopJ true m4 ⟨st4, hbase4, hd4_fn, hm4⟩
  · exact hPopJ failb m4 ⟨st4, hbase4, hd4_fn, hm4⟩

theorem fast_tarjan_scc_wp (Γ : Env)
    (hPop : ∀ args m Q X, Full.fullTarjanPopSccSpec args m Q X →
      Γ "full_tarjan_pop_scc" [i64, i32, i32, i32] [.bool] args m Q X) :
    ∀ args m Q X, fullTarjanSccFastSpec args m Q X →
      Func.wp Γ full_tarjan_scc_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s0, R, rfl, hsp0, _, hm, hQ⟩
  have hmx := c.hmaxv; have hwc := c.hwcap; unfold dimacsBound at hmx hwc
  have hlen0 := hsp0.1; have hw0 := hsp0.2.1; have hdm0 := hsp0.2.2.2.2.2
  have hcl0 := hlen0.core_ok; have hcv_le := hcl0.cur_vars_le
  have hwat0 : WatchesInv F_cur s0.core := by
    have hmw := hw0.watches; unfold ModeWatchesInv at hmw; rwa [ite_eq_left hdm0] at hmw
  have hnl_eq : (BitVec.ofNat 64 s0.core.cur_vars <<< (1 : Nat)).toNat = 2 * s0.core.cur_vars := by
    rw [FullArenaTactics.bv64_shl1_nat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : s0.core.cur_vars < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  unfold Func.wp full_tarjan_scc_body
  scc_to_group
  refine wp_loop_inv
    (fun (i, ()) ml => ∃ st : FullState,
      AgreesExcept tarjanSccMask s0 st ∧ st.LengthsOk c ∧
      st.core.inconsistent = s0.core.inconsistent ∧ i.toNat ≤ 2 * s0.core.cur_vars ∧
      (∀ l < i.toNat, st.core.repr[l]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 ∧
        (st.scratch.tarjan_mark[l]?.getD 0#32).toNat = 0 ∧
        (st.scratch.tarjan_reach[l]?.getD 0#32).toNat = 0) ∧ (FullMem c st ⋆ R) ml)
    (fun (i, ()) _ => 2 * s0.core.cur_vars - i.toNat) ?_ ?_
  · intro J hJ; scc_steps
    exact hJ (0#64, ()) m ⟨s0, AgreesExcept.refl _ _, hlen0, rfl, Nat.zero_le _,
      fun _ h => by simp at h, hm⟩
  rintro J ⟨i, ⟨⟩⟩ ml ⟨st, hag, hlen, hinc_st, hi_le, hinit, hml⟩ hJ
  have hrp_l := hlen.core_ok.repr_len; have htmk_l := hlen.scratch_ok.tarjan_mark_len
  have htrc_l := hlen.scratch_ok.tarjan_reach_len
  scc_split
  · have hi_lt : i.toNat < 2 * s0.core.cur_vars := by
      have := BitVec.lt_def.mp (BitVec.ult_iff_lt.mp hc); rwa [hnl_eq] at this
    have hi1 : (i + 1#64).toNat = i.toNat + 1 := scc_bv64_add1 (by omega)
    scc_steps
    let st1 : FullState :=
      { st with core := { st.core with repr := st.core.repr.set i.toNat 0xFFFFFFFF#32 }
                scratch := { st.scratch with
                  tarjan_mark := st.scratch.tarjan_mark.set i.toNat 0#32
                  tarjan_reach := st.scratch.tarjan_reach.set i.toNat 0#32 } }
    refine hJ (i + 1#64, ()) _ (by dsimp only; omega) ⟨st1, hag.update _,
      ⟨{ hlen.core_ok with repr_len := by simp [st1, hrp_l] },
       { hlen.scratch_ok with
         tarjan_mark_len := by simp [st1, htmk_l], tarjan_reach_len := by simp [st1, htrc_l] }⟩,
      hinc_st, by omega, fun l hl => ?_, hm⟩
    by_cases hli : l = i.toNat
    · subst hli; dsimp only [st1]
      rw [List.getElem?_set_self (by omega), List.getElem?_set_self (by omega),
        List.getElem?_set_self (by omega)]; exact ⟨rfl, rfl, rfl⟩
    · dsimp only [st1]; rw [List.getElem?_set_ne (Ne.symm hli), List.getElem?_set_ne (Ne.symm hli),
        List.getElem?_set_ne (Ne.symm hli)]; exact hinit l (by omega)
  have hi_eq : i.toNat = 2 * s0.core.cur_vars := by have := scc_ult_false_ge hc; omega
  scc_to_group
  refine wp_loop_inv
    (fun (reached, root, ()) ml => ∃ st : FullState,
      root.toNat ≤ 2 * s0.core.cur_vars ∧ TarjanLoopBase c F_cur s0 st ∧
      (st.core.inconsistent = 0#64 →
        st.core.tmp_cnt = 0 ∧ TarjanDfsInv c F0 F_cur s0 0 1 reached.toNat 0 st) ∧
      (FullMem c st ⋆ R) ml)
    (fun (_, root, ()) _ => 2 * s0.core.cur_vars - root.toNat) ?_ ?_
  · intro J2 hJ2; scc_steps
    let st1 : FullState := { st with core := { st.core with tmp_cnt := 0 }
                                     scratch := { st.scratch with res_sz := 0#64 } }
    have hag1 : AgreesExcept tarjanSccMask s0 st1 := hag.update _
    have hlen1 : st1.LengthsOk c :=
      ⟨{ hlen.core_ok with vals_len := hlen.core_ok.vals_len },
       { hlen.scratch_ok with work_stk1_len := hlen.scratch_ok.work_stk1_len }⟩
    have hpr1 : PartialReprInv F_cur st1.core := fun l hl hne => by
      rw [hag1.get (·.core.cur_vars)] at hl; exact absurd (hinit l (by omega)).1 hne
    have hinc_u1 : st1.core.inconsistent ≠ 0#64 → (cnfOfClauses F_cur).Unsat := fun hne => by
      dsimp only [st1] at hne; rw [hinc_st] at hne; exact hw0.inconsistent_sound hne
    refine hJ2 (0#32, 0#64, ()) _ ⟨st1, Nat.zero_le _,
      ⟨hag1, hlen1, by simp [st1], hpr1, fun _ h => by simp [st1] at h, hinc_u1⟩,
      fun h0 => ⟨rfl, {
        agrees := hag1, len_ok := hlen1, inc0 := h0, rsz_le := by simp [st1]
        partial_repr := hpr1, units_ok := fun _ h => by simp [st1] at h
        reached_le := Nat.zero_le _, top_le := by dsimp only [st1]; omega
        tmk_le := fun l hl => by dsimp only [st1]; rw [(hinit l (by omega)).2.1]; omega
        tmk_inj := fun a _ ha _ hp => by
          dsimp only [st1] at hp; rw [(hinit a (by omega)).2.1] at hp; omega
        tmk_surj := fun _ h1 h2 => by
          rw [show (0#32 : BitVec 32).toNat = 0 from rfl] at h2; omega
        tmk_active := fun l hl hp => by
          dsimp only [st1] at hp; rw [(hinit l (by omega)).2.1] at hp; omega
        scc_lt := fun _ h => by dsimp only [st1] at h; omega
        scc_tmk_ge := fun _ h => by dsimp only [st1] at h; omega
        scc_tmk_mono := fun _ _ _ h => by dsimp only [st1] at h; omega
        scc_iff_trc := fun l hl => ⟨fun ⟨_, h, _⟩ => by dsimp only [st1] at h; omega,
          fun ⟨hp, _⟩ => by dsimp only [st1] at hp; rw [(hinit l (by omega)).2.1] at hp; omega⟩
        trc_range := fun _ h => by dsimp only [st1] at h; omega
        trc_witness := fun _ h => by dsimp only [st1] at h; omega
        dsp_le := by omega, dv_on_scc := by omega, dv_tmk_mono := by omega, dv0_root := by omega
        dv_trc_eq := by omega, dpos_slice := by omega, scc_parent_ge := by omega
        mroot_reach := by omega
        pop_trc_lt := fun _ ⟨_, h, _⟩ => by dsimp only [st1] at h; omega
        pop_edges_vis := fun _ _ ⟨_, h, _⟩ => by dsimp only [st1] at h; omega
        pop_trc_fwd := fun _ _ ⟨_, h, _⟩ => by dsimp only [st1] at h; omega
        pop_dv_order := fun _ _ ⟨_, h, _⟩ => by dsimp only [st1] at h; omega }⟩, hm⟩
  rintro J2 ⟨reached, root, ⟨⟩⟩ ml ⟨st, hrt_le, hbase, hinc_dfs, hml⟩ hJ2
  clear hJ hinit hi_le hi_eq hinc_st hrp_l htmk_l htrc_l hag hlen
  obtain ⟨hag, hlen, hrsz, hpr, hus, hinc_u⟩ := hbase
  have hfl_l := hlen.core_ok.flags_len; have htmk_l := hlen.scratch_ok.tarjan_mark_len
  have htrc_l := hlen.scratch_ok.tarjan_reach_len; have hscc_l := hlen.scratch_ok.work_stk1_len
  have hdv_l := hlen.scratch_ok.work_stk2_len; have hdp_l := hlen.scratch_ok.wsort_len
  scc_to_group
  refine wp_join_group (ts := [])
    (fun () mj => ∃ st' : FullState, TarjanLoopBase c F_cur s0 st' ∧ (FullMem c st' ⋆ R) mj) ?_ ?_
  · -- Exit cleanup loop: fills unmapped `repr[i]` AND zeroes `tmk[i] = 0u; trc[i] = 0u;`
    rintro _ ⟨⟩ mj ⟨stf, ⟨hagf, hlenf, hrszf, hprf, husf, hincf⟩, hmj⟩
    scc_to_group
    refine wp_loop_inv
      (fun (idx, ()) mk => ∃ st4 : FullState,
        AgreesExcept tarjanSccMask s0 st4 ∧ st4.LengthsOk c ∧
        st4.core.inconsistent = stf.core.inconsistent ∧ st4.scratch.res_sz = stf.scratch.res_sz ∧
        st4.scratch.shrink_stk = stf.scratch.shrink_stk ∧ idx.toNat ≤ 2 * s0.core.cur_vars ∧
        PartialReprInv F_cur st4.core ∧
        (∀ l < idx.toNat, st4.core.repr[l]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 ∧
          st4.scratch.tarjan_mark[l]?.getD 0#32 = 0#32 ∧
          st4.scratch.tarjan_reach[l]?.getD 0#32 = 0#32) ∧
        (FullMem c st4 ⋆ R) mk)
      (fun (idx, ()) _ => 2 * s0.core.cur_vars - idx.toNat) ?_ ?_
    · intro J4 hJ4; scc_steps
      exact hJ4 (0#64, ()) mj ⟨stf, hagf, hlenf, rfl, rfl, rfl, Nat.zero_le _, hprf,
        fun _ h => by simp at h, hmj⟩
    rintro J4 ⟨idx, ⟨⟩⟩ mk ⟨st4, hag4, hlen4, hinc4, hrsz4, hsh4, hidx_le, hpr4, hfill4, hmk⟩ hJ4
    have hrp4 := hlen4.core_ok.repr_len; have hcv4 := hag4.get (·.core.cur_vars)
    have htmk4 := hlen4.scratch_ok.tarjan_mark_len
    have htrc4 := hlen4.scratch_ok.tarjan_reach_len
    scc_split
    · have hidx_lt : idx.toNat < 2 * s0.core.cur_vars := by
        have := BitVec.lt_def.mp (BitVec.ult_iff_lt.mp hc); rwa [hnl_eq] at this
      have hidx1 : (idx + 1#64).toNat = idx.toNat + 1 := scc_bv64_add1 (by omega)
      have hidx_lt32 : idx.toNat < 2 ^ 32 := by omega
      scc_to_group
      refine wp_join_group (ts := [])
        (fun () mn => ∃ st5 : FullState,
          AgreesExcept tarjanSccMask s0 st5 ∧ st5.LengthsOk c ∧
          st5.core.inconsistent = stf.core.inconsistent ∧ st5.scratch.res_sz = stf.scratch.res_sz ∧
          st5.scratch.shrink_stk = stf.scratch.shrink_stk ∧ PartialReprInv F_cur st5.core ∧
          (∀ l < idx.toNat + 1, st5.core.repr[l]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) ∧
          (∀ l < idx.toNat,
            st5.scratch.tarjan_mark[l]?.getD 0#32 = 0#32 ∧
            st5.scratch.tarjan_reach[l]?.getD 0#32 = 0#32) ∧
          (FullMem c st5 ⋆ R) mn) ?_ ?_
      · rintro _ ⟨⟩ mn ⟨st5, hag5, hlen5, hinc5, hrsz5, hsh5, hpr5, hrep5, hclr5, hmn⟩
        have htmk5 := hlen5.scratch_ok.tarjan_mark_len
        have htrc5 := hlen5.scratch_ok.tarjan_reach_len
        scc_steps
        let st6 : FullState := { st5 with scratch := { st5.scratch with
          tarjan_mark := st5.scratch.tarjan_mark.set idx.toNat 0#32
          tarjan_reach := st5.scratch.tarjan_reach.set idx.toNat 0#32 } }
        exact hJ4 (idx + 1#64, ()) _ (by dsimp only; omega)
          ⟨st6, hag5.update _,
           ⟨hlen5.core_ok, { hlen5.scratch_ok with
             tarjan_mark_len := by simp [st6, htmk5],
             tarjan_reach_len := by simp [st6, htrc5] }⟩,
           hinc5, hrsz5, hsh5, by omega, hpr5, fun l hl => by
             rw [hidx1] at hl; refine ⟨hrep5 l hl, ?_, ?_⟩
             · dsimp only [st6]; by_cases hli : l = idx.toNat
               · subst hli; rw [List.getElem?_set_self (by omega), Option.getD_some]
               · rw [List.getElem?_set_ne (Ne.symm hli)]; exact (hclr5 l (by omega)).1
             · dsimp only [st6]; by_cases hli : l = idx.toNat
               · subst hli; rw [List.getElem?_set_self (by omega), Option.getD_some]
               · rw [List.getElem?_set_ne (Ne.symm hli)]; exact (hclr5 l (by omega)).2, hm⟩
      · intro Jrep hJrep
        scc_steps
        · let st5 : FullState := { st4 with core := { st4.core with
              repr := st4.core.repr.set idx.toNat (BitVec.setWidth 32 idx) } }
          have hpr5 : PartialReprInv F_cur st5.core := fun l hl hne => by
            dsimp only [st5] at hl ⊢; by_cases hli : l = idx.toNat
            · subst hli; rw [List.getElem?_set_self (by omega), Option.getD_some,
                bv32_trunc_toNat hidx_lt32]; exact ⟨by omega, LitEquiv.refl _ _⟩
            · rw [List.getElem?_set_ne (Ne.symm hli)] at hne ⊢; exact hpr4 l hl hne
          have hrep5 : ∀ l < idx.toNat + 1,
              st5.core.repr[l]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := fun l hl => by
            dsimp only [st5]; by_cases hli : l = idx.toNat
            · subst hli; rw [List.getElem?_set_self (by omega), Option.getD_some]; intro heq
              have := congrArg BitVec.toNat heq; rw [bv32_trunc_toNat hidx_lt32] at this
              revert this; simp; omega
            · rw [List.getElem?_set_ne (Ne.symm hli)]; exact (hfill4 l (by omega)).1
          exact hJrep () _ ⟨st5, hag4.update _,
            ⟨{ hlen4.core_ok with repr_len := by simp [st5, hrp4] }, hlen4.scratch_ok⟩,
            hinc4, hrsz4, hsh4, hpr5, hrep5, fun l hl => (hfill4 l hl).2, hm⟩
        · have hne_idx : st4.core.repr[idx.toNat]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; assumption
          exact hJrep () mk ⟨st4, hag4, hlen4, hinc4, hrsz4, hsh4, hpr4,
            fun l hl => by
              by_cases hli : l = idx.toNat
              · subst hli; exact hne_idx
              · exact (hfill4 l (by omega)).1,
            fun l hl => (hfill4 l hl).2, hmk⟩
    · have hidx_eq : idx.toNat = 2 * s0.core.cur_vars := by have := scc_ult_false_ge hc; omega
      scc_steps
      have hsp4 := tarjanScc_preserves_sparse hsp0 hag4 hlen4 (fun h => hincf (hinc4 ▸ h))
      have hrepr4 : Full.FullReprEquiv F_cur st4 := fun l hl => by
        have hget : st4.core.repr[l]?.getD 0#32 = st4.core.repr[l]?.getD 0xFFFFFFFF#32 := by
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some, Option.getD_some]
        obtain ⟨hr_lt, h1, h2⟩ := hpr4 l hl (hfill4 l (by omega)).1
        rw [hget]; exact ⟨hr_lt, h2, h1⟩
      have hus4 : ∀ k < st4.scratch.res_sz.toNat,
          (st4.scratch.shrink_stk[k]?.getD 0#32).toNat < 2 * s0.core.cur_vars ∧
          (cnfOfClauses F_cur).EntailsClause
            (cnfClause [(st4.scratch.shrink_stk[k]?.getD 0#32).toNat]) := fun k hk => by
        rw [hrsz4] at hk; rw [hsh4]; have := husf k hk
        rwa [hagf.get (·.core.cur_vars)] at this
      have hzero4 : ∀ l < 2 * s0.core.cur_vars,
          st4.scratch.tarjan_mark[l]?.getD 0#32 = 0#32 ∧
          st4.scratch.tarjan_reach[l]?.getD 0#32 = 0#32 :=
        fun l hl => (hfill4 l (by omega)).2
      have htmkz4 : TmkZero st4 := fun v hv => (hzero4 v (by omega)).1
      have heq4 := agrees_tarjanSccMask_eq hag4
      exact hQ st4.scratch.res_sz st4.core.repr st4.core.tmp_cnt st4.core.inconsistent
        st4.scratch.tarjan_mark st4.scratch.tarjan_reach st4.scratch.work_stk1 st4.scratch.work_stk2
        st4.scratch.wsort st4.scratch.shrink_stk st4.scratch.res_sz mk
        (heq4.symm ▸ hsp4) (by rw [hrsz4]; exact hrszf) hus4
        (fun _ => heq4.symm ▸ hrepr4) hzero4 (heq4.symm ▸ htmkz4) (heq4.symm ▸ hmk)
  intro Jexit hExit; scc_split; rotate_left
  · scc_steps; exact hExit () ml ⟨st, ⟨hag, hlen, hrsz, hpr, hus, hinc_u⟩, hml⟩
  have hrt_lt : root.toNat < 2 * s0.core.cur_vars := by
    have := BitVec.lt_def.mp (BitVec.ult_iff_lt.mp hc); rwa [hnl_eq] at this
  have hrt1 : (root + 1#64).toNat = root.toNat + 1 := scc_bv64_add1 (by omega)
  scc_split; rotate_left
  · scc_steps; exact hExit () ml ⟨st, ⟨hag, hlen, hrsz, hpr, hus, hinc_u⟩, hml⟩
  have hst_inc0 : st.core.inconsistent = 0#64 := hc; obtain ⟨htop0, hdfs⟩ := hinc_dfs hst_inc0
  scc_to_group
  refine wp_join_group (ts := [i32])
    (fun (rch', ()) mj => ∃ st' : FullState, TarjanLoopBase c F_cur s0 st' ∧
      (st'.core.inconsistent = 0#64 →
        st'.core.tmp_cnt = 0 ∧ TarjanDfsInv c F0 F_cur s0 0 1 rch'.toNat 0 st') ∧
      (FullMem c st' ⋆ R) mj) ?_ ?_
  · rintro _ ⟨rch', ⟨⟩⟩ mj ⟨st', hbase', hdfs', hmj⟩
    scc_steps; exact hJ2 (rch', root + 1#64, ()) mj (by dsimp only; omega)
      ⟨st', by omega, hbase', hdfs', hmj⟩
  intro Jskip hSkip; scc_split; rotate_left
  · scc_steps; exact hSkip (reached, ()) ml ⟨st, ⟨hag, hlen, hrsz, hpr, hus, hinc_u⟩, hinc_dfs, hml⟩
  have htmk_rt0 : (st.scratch.tarjan_mark[root.toNat]?.getD 0#32).toNat = 0 := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hc]; rfl
  scc_split; rotate_left
  · scc_steps; exact hSkip (reached, ()) ml ⟨st, ⟨hag, hlen, hrsz, hpr, hus, hinc_u⟩, hinc_dfs, hml⟩
  have hact_rt : activeLit s0 root.toNat := by
    refine ⟨hrt_lt, ?_⟩
    rw [← hag.get (·.core.flags), List.getElem?_eq_getElem (by omega), Option.getD_some]
    simp only [FullSccTactics.bv64_ushr1_nat] at hc; exact hc
  have hr_lt := hdfs.reached_lt_of_unvisited hrt_lt htmk_rt0
  have hr1_nat : (reached + (1 : BitVec 32)).toNat = reached.toNat + 1 := scc_bv32_add1 (by omega)
  have hrt32_eq : BitVec.setWidth 32 root = BitVec.ofNat 32 root.toNat :=
    BitVec.eq_of_toNat_eq (by
      rw [bv32_trunc_toNat (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  have hr32_eq : reached + (1 : BitVec 32) = BitVec.ofNat 32 (reached.toNat + 1) :=
    BitVec.eq_of_toNat_eq (by rw [hr1_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  have hinit_dfs := tarjan_init_root hw0 hdm0 hdfs htop0 hact_rt htmk_rt0
  have hpos_mv : 0 < 2 * c.max_vars := by omega
  scc_to_group
  refine wp_loop_group (ts := [i32, .bool, i64])
    (fun n (rch, _failb, dsp, ()) m3 => ∃ st3 : FullState, TarjanLoopBase c F_cur s0 st3 ∧
      (st3.core.inconsistent = 0#64 →
        n = TarjanDfsInv.measure c s0 st3 rch.toNat dsp.toNat ∧
        TarjanDfsInv c F0 F_cur s0 root.toNat (reached.toNat + 1) rch.toNat dsp.toNat st3 ∧
        (dsp.toNat = 0 → st3.core.tmp_cnt = 0)) ∧ (FullMem c st3 ⋆ R) m3) ?_ ?_
  rotate_left
  · intro J3 hJ3; scc_steps
    let st_init : FullState :=
      { st with
        core := { st.core with tmp_cnt := 1 }
        scratch := { st.scratch with
          work_stk2 := st.scratch.work_stk2.set 0 (BitVec.ofNat 32 root.toNat)
          wsort := st.scratch.wsort.set 0 0#32
          tarjan_mark := st.scratch.tarjan_mark.set root.toNat (BitVec.ofNat 32 (reached.toNat + 1))
          tarjan_reach :=
            st.scratch.tarjan_reach.set root.toNat (BitVec.ofNat 32 (reached.toNat + 1))
          work_stk1 := st.scratch.work_stk1.set 0 (BitVec.ofNat 32 root.toNat) } }
    have hm_init : (FullMem c st_init ⋆ R) m := by
      rw [htop0, hrt32_eq, hr32_eq, show (BitVec.ofNat 64 0 + (1 : BitVec 64)).toNat = 1 from rfl,
        show (BitVec.ofNat 64 0).toNat = 0 from rfl] at hm; exact hm
    exact hJ3 _ (reached + (1 : BitVec 32), false, 1#64, ()) m
      ⟨st_init, hinit_dfs.2.toBase,
       fun _ => ⟨rfl, by rw [hr1_nat]; exact hinit_dfs.2, fun h => by simp at h⟩, hm_init⟩
  rintro J3 n ⟨rch, failb, dsp, ⟨⟩⟩ m3 hJ3 ⟨st3, hbase3, hdfs3, hm3⟩
  clear hinc_dfs hdfs hinit_dfs hact_rt htmk_rt0 hr_lt hrt32_eq hr32_eq hrsz hpr hus hinc_u
    hst_inc0 htop0
  scc_split; rotate_left
  · have hdsp0 : dsp.toNat = 0 := by
      have := scc_ult_false_ge hc; rw [show (0 : BitVec 64).toNat = 0 from rfl] at this; omega
    scc_steps; refine hSkip (rch, ()) m3 ⟨st3, hbase3, fun hinc30 => ?_, hm3⟩
    obtain ⟨_, hd3, htop3⟩ := hdfs3 hinc30; exact ⟨htop3 hdsp0, hd3.reset_empty (htop3 hdsp0)⟩
  have hdsp_pos : 0 < dsp.toNat := by
    have := BitVec.lt_def.mp (BitVec.ult_iff_lt.mp hc)
    rwa [show (0 : BitVec 64).toNat = 0 from rfl] at this
  scc_split; rotate_left
  · scc_steps; exact hSkip (rch, ()) m3 ⟨st3, hbase3, fun h => absurd h hc, hm3⟩
  have hinc30 : st3.core.inconsistent = 0#64 := hc; obtain ⟨rfl, hd3, _⟩ := hdfs3 hinc30
  obtain ⟨hag3, hlen3, hrsz3, hpr3, hus3, hinc3⟩ := hbase3
  have hcl3 := hlen3.core_ok; have hsl3 := hlen3.scratch_ok
  have hdv_l3 := hsl3.work_stk2_len; have hdp_l3 := hsl3.wsort_len
  have hscc_l3 := hsl3.work_stk1_len; have htmk_l3 := hsl3.tarjan_mark_len
  have htrc_l3 := hsl3.tarjan_reach_len; have hfl_l3 := hcl3.flags_len
  have hwv_l3 := hcl3.wvec_len; have hws_l3 := hcl3.wstk_len_arr
  have hcv3 := hag3.get (·.core.cur_vars); have hwv3 := hag3.get (·.core.wvec)
  have hws3 := hag3.get (·.core.wstk); have hfl3 := hag3.get (·.core.flags)
  have hdsp_sub : (dsp - (1 : BitVec 64)).toNat = dsp.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 1 ≤ _; omega))]; rfl
  have hdsp_lt3 : dsp.toNat ≤ 2 * s0.core.cur_vars := by
    have := hd3.dsp_le; have := hd3.top_le; have := hd3.reached_le; omega
  let lit := st3.scratch.work_stk2[(dsp - (1 : BitVec 64)).toNat]'(by rw [hdsp_sub]; omega)
  have hlit_get : lit = st3.scratch.work_stk2[dsp.toNat - 1]?.getD 0#32 := by
    have hlt : dsp.toNat - 1 < st3.scratch.work_stk2.length := by omega
    simp only [lit, hdsp_sub, List.getElem?_eq_getElem hlt, Option.getD_some]
  have hlit_lt : lit.toNat < 2 * s0.core.cur_vars := by rw [hlit_get]; exact hd3.dv_lt (by omega)
  have hnl_lt_nat : lit.toNat ^^^ 1 < 2 * s0.core.cur_vars := litNeg_lt_two_mul hlit_lt
  have hnl_lt : (lit ^^^ (1 : BitVec 32)).toNat < 2 * s0.core.cur_vars := by
    rw [show (1 : BitVec 32) = 1#32 from rfl, bv32_xor1_toNat]; exact hnl_lt_nat
  have hlit_act : activeLit s0 lit.toNat := by
    obtain ⟨j, hj, hjeq⟩ := hd3.dv_on_scc (dsp.toNat - 1) (by omega); rw [← hlit_get] at hjeq
    exact hd3.tmk_active lit.toNat hlit_lt
      (by have := hd3.scc_tmk_ge j hj; rw [hjeq] at this; omega)
  let pos32 := st3.scratch.wsort[(dsp - (1 : BitVec 64)).toNat]'(by rw [hdsp_sub]; omega)
  have hpos_get : pos32 = st3.scratch.wsort[dsp.toNat - 1]?.getD 0#32 := by
    have hlt : dsp.toNat - 1 < st3.scratch.wsort.length := by omega
    simp only [pos32, hdsp_sub, List.getElem?_eq_getElem hlt, Option.getD_some]
  have hnl2 : (BitVec.setWidth 64 (lit ^^^ (1 : BitVec 32)) <<< (1 : Nat)).toNat =
      2 * (lit.toNat ^^^ 1) := by
    rw [FullArenaTactics.bv64_shl1_nat, zext_toNat _ (by decide),
      show (1 : BitVec 32) = 1#32 from rfl, bv32_xor1_toNat]; exact Nat.mod_eq_of_lt (by omega)
  have hnl2_1 : ((BitVec.setWidth 64 (lit ^^^ (1 : BitVec 32)) <<< (1 : Nat)) +
      (1 : BitVec 64)).toNat = 2 * (lit.toNat ^^^ 1) + 1 :=
    (scc_bv64_add1 (by rw [hnl2]; omega)).trans (by rw [hnl2])
  have hnl2_u : (BitVec.setWidth 64
      (st3.scratch.work_stk2[(dsp - (1 : BitVec 64)).toNat]'(by rw [hdsp_sub]; omega) ^^^
        (1 : BitVec 32)) <<< (1 : Nat)).toNat = 2 * (lit.toNat ^^^ 1) := hnl2
  have hnl2_1_u : ((BitVec.setWidth 64
      (st3.scratch.work_stk2[(dsp - (1 : BitVec 64)).toNat]'(by rw [hdsp_sub]; omega) ^^^
        (1 : BitVec 32)) <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * (lit.toNat ^^^ 1) + 1 :=
    hnl2_1
  let off32 := st3.core.wvec[(BitVec.setWidth 64 (lit ^^^ (1 : BitVec 32)) <<< (1 : Nat)).toNat]'(
    by rw [hnl2]; omega)
  let sz32 := st3.core.wvec[((BitVec.setWidth 64 (lit ^^^ (1 : BitVec 32)) <<< (1 : Nat)) +
    (1 : BitVec 64)).toNat]'(by rw [hnl2_1]; omega)
  let woff := fullWatchOffCore s0.core (lit.toNat ^^^ 1)
  let wsz := fullWatchSizeCore s0.core (lit.toNat ^^^ 1)
  have hoff_get : off32.toNat = woff := by
    unfold woff fullWatchOffCore; rw [← hwv3]
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; dsimp only [off32]; simp only [hnl2]
  have hsz_get : sz32.toNat = wsz := by
    unfold wsz fullWatchSizeCore; rw [← hwv3]
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    dsimp only [sz32]; simp only [hnl2_1]
  have hslc3 := hd3.dpos_slice (dsp.toNat - 1) (by omega); rw [← hlit_get] at hslc3
  have hsb : woff + wsz ≤ s0.core.wlen := hwat0.layout.bounds (lit.toNat ^^^ 1) hnl_lt_nat
  have hwle0 := hlen0.core_ok.wlen_le
  scc_split
  · have hpos_lt : pos32.toNat < wsz := by
      rw [← hsz_get]; exact BitVec.lt_def.mp (BitVec.ult_iff_lt.mp hc)
    have hidx_eq : (BitVec.setWidth 64 off32 + BitVec.setWidth 64 pos32).toNat =
        woff + pos32.toNat := by
      rw [scc_bv64_add (by rw [zext_toNat _ (by decide), zext_toNat _ (by decide)]; omega),
        zext_toNat _ (by decide), zext_toNat _ (by decide), hoff_get]
    have hidx_lt : (BitVec.setWidth 64 off32 + BitVec.setWidth 64 pos32).toNat <
        st3.core.wstk.length := by rw [hidx_eq]; omega
    have hidx_lt_u : (BitVec.setWidth 64 off32 + BitVec.setWidth 64 pos32).toNat < c.wcap := by
      rw [hidx_eq]; omega
    dsimp only [off32, pos32, lit] at hidx_lt_u
    scc_split
    · have hflag0 : (s0.core.wstk[woff + pos32.toNat]?.getD 0#32 &&& 0x80000000#32) = 0#32 := by
        rw [← hws3, List.getElem?_eq_getElem (by omega), Option.getD_some]
        dsimp only [off32, pos32, lit] at hidx_eq; simp only [hidx_eq] at hc; exact hc
      have hp2 : (pos32 + (2 : BitVec 32)).toNat = pos32.toNat + 2 := scc_bv32_add2 (by omega)
      have hslc_nb := scc_dpos_step_nonbin hpos_lt hp2 (hpos_get ▸ hslc3.2.1)
        hflag0 (hpos_get ▸ hslc3.2.2)
      obtain ⟨hd4, hmeas4⟩ := tarjan_advance_dpos (pos' := pos32 + (2 : BitVec 32)) hd3 hdsp_pos
        (by rw [← hpos_get, hp2]; omega) (by rw [← hlit_get]; exact hslc_nb)
      scc_steps
      let st4 : FullState := { st3 with scratch := { st3.scratch with
        wsort := st3.scratch.wsort.set (dsp.toNat - 1) (pos32 + (2 : BitVec 32)) } }
      have hm4 : (FullMem c st4 ⋆ R) m := by
        have hw : st3.scratch.wsort.set (dsp - (1 : BitVec 64)).toNat (pos32 + (2 : BitVec 32)) =
            st3.scratch.wsort.set (dsp.toNat - 1) (pos32 + (2 : BitVec 32)) := by rw [hdsp_sub]
        dsimp only [st4]; rw [← hw]; exact hm
      exact hJ3 _ (rch, failb, dsp, ()) m hmeas4
        ⟨st4, hd4.toBase, fun _ => ⟨rfl, hd4, fun h => by omega⟩, hm4⟩
    have hflag1 : (s0.core.wstk[woff + pos32.toNat]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 := by
      rw [← hws3, List.getElem?_eq_getElem (by omega), Option.getD_some]
      dsimp only [off32, pos32, lit] at hidx_eq; simp only [hidx_eq] at hc; exact hc
    have hp1 : (pos32 + (1 : BitVec 32)).toNat = pos32.toNat + 1 := scc_bv32_add1 (by omega)
    obtain ⟨w0, hw0_eq, hot_lt, hbins_ot, hslc_b1⟩ :=
      scc_dpos_step_bin hpos_lt hp1 (hpos_get ▸ hslc3.2.1) hflag1 (hpos_get ▸ hslc3.2.2)
    have hw0_get : st3.core.wstk[(BitVec.setWidth 64 off32 +
        BitVec.setWidth 64 pos32).toNat]'hidx_lt = w0 := by
      have h1 := hw0_eq; rw [← hws3, List.getElem?_eq_getElem (by omega)] at h1
      simpa only [hidx_eq] using Option.some.inj h1
    dsimp only [off32, pos32, lit] at hw0_get
    let ot := w0 &&& (2147483647 : BitVec 32)
    have hot_lt' : ot.toNat < 2 * s0.core.cur_vars := hot_lt
    have hz_ot : (BitVec.setWidth 64 ot).toNat = ot.toNat := zext_toNat ot (by decide)
    have hdiv_ot : (BitVec.setWidth 64 (ot >>> (BitVec.toNat (1 : BitVec 32) % 32))).toNat =
        ot.toNat / 2 := by
      rw [zext_toNat _ (by decide), show BitVec.toNat (1 : BitVec 32) % 32 = 1 from rfl,
        FullSccTactics.bv32_ushr1_nat]
    have hot_z_lt : (BitVec.setWidth 64 (st3.core.wstk[(BitVec.setWidth 64 off32 +
        BitVec.setWidth 64 pos32).toNat]'hidx_lt &&& (2147483647 : BitVec 32))).toNat <
        2 * c.max_vars := by
      dsimp only [off32, pos32, lit]; rw [hw0_get]; change (BitVec.setWidth 64 ot).toNat < _
      rw [hz_ot]; omega
    have hot_div_lt : (BitVec.setWidth 64 ((st3.core.wstk[(BitVec.setWidth 64 off32 +
        BitVec.setWidth 64 pos32).toNat]'hidx_lt &&& (2147483647 : BitVec 32)) >>>
          (BitVec.toNat (1 : BitVec 32) % 32))).toNat < c.max_vars := by
      dsimp only [off32, pos32, lit]; rw [hw0_get]
      change (BitVec.setWidth 64 (ot >>> (BitVec.toNat (1 : BitVec 32) % 32))).toNat < _
      rw [hdiv_ot]; omega
    dsimp only [off32, pos32, lit] at hot_z_lt hot_div_lt
    scc_to_group
    refine wp_join_group (ts := [i32, i64])
      (fun (rch', dsp', ()) mj => ∃ st4 : FullState, 0 < dsp'.toNat ∧
        TarjanDfsInv c F0 F_cur s0 root.toNat (reached.toNat + 1) rch'.toNat dsp'.toNat st4 ∧
        TarjanDfsInv.measure c s0 st4 rch'.toNat dsp'.toNat <
          TarjanDfsInv.measure c s0 st3 rch.toNat dsp.toNat ∧ (FullMem c st4 ⋆ R) mj) ?_ ?_
    · rintro _ ⟨rch', dsp', ⟨⟩⟩ mj ⟨st4, hdsp4, hd4, hm4, hmj⟩
      scc_steps; exact hJ3 _ (rch', failb, dsp', ()) mj hm4
        ⟨st4, hd4.toBase, fun _ => ⟨rfl, hd4, fun h => by omega⟩, hmj⟩
    intro Jb hJb
    let st3a : FullState := { st3 with scratch := { st3.scratch with
      wsort := st3.scratch.wsort.set (dsp.toNat - 1) (pos32 + (1 : BitVec 32)) } }
    have hma : (FullMem c st3a ⋆ R) m := by
      have hw : st3.scratch.wsort.set (dsp - (1 : BitVec 64)).toNat (pos32 + (1 : BitVec 32)) =
          st3.scratch.wsort.set (dsp.toNat - 1) (pos32 + (1 : BitVec 32)) := by rw [hdsp_sub]
      dsimp only [st3a]; rw [← hw]; exact hm
    have hskip_ok : (¬ activeLit s0 ot.toNat ∨
        1 ≤ (st3.scratch.tarjan_mark[ot.toNat]?.getD 0#32).toNat) →
        TarjanDfsInv c F0 F_cur s0 root.toNat (reached.toNat + 1) rch.toNat dsp.toNat st3a ∧
        TarjanDfsInv.measure c s0 st3a rch.toNat dsp.toNat <
          TarjanDfsInv.measure c s0 st3 rch.toNat dsp.toNat := by
      intro hsk; obtain ⟨hle, hslc, sc, hseq, hsok⟩ := hslc_b1
      exact tarjan_advance_dpos (pos' := pos32 + (1 : BitVec 32)) hd3 hdsp_pos
        (by rw [← hpos_get, hp1]; omega)
        (by rw [← hlit_get]; refine ⟨hle, hslc, sc, hseq, fun x hx hax => ?_⟩
            rcases hsok x hx hax with rfl | hpos
            · exact hsk.elim (fun hna => absurd hax hna) id
            · exact hpos)
    clear hm
    have hfl_a : st3a.core.flags.length = c.max_vars := hfl_l3
    have htmk_a : st3a.scratch.tarjan_mark.length = 2 * c.max_vars := htmk_l3
    have htrc_a : st3a.scratch.tarjan_reach.length = 2 * c.max_vars := htrc_l3
    have hscc_a : st3a.scratch.work_stk1.length = 2 * c.max_vars := hscc_l3
    have hdv_a : st3a.scratch.work_stk2.length = 2 * c.max_vars := hdv_l3
    have hdp_a : st3a.scratch.wsort.length = 2 * c.max_vars := by
      dsimp only [st3a]; rw [List.length_set]; exact hdp_l3
    have hflag_ot : st3.core.flags[(BitVec.setWidth 64 ((st3.core.wstk[(BitVec.setWidth 64 off32 +
        BitVec.setWidth 64 pos32).toNat]'hidx_lt &&& (2147483647 : BitVec 32)) >>>
          (BitVec.toNat (1 : BitVec 32) % 32))).toNat]'(
            by rw [hfl_l3]; dsimp only [off32, pos32, lit]; exact hot_div_lt) =
        st3.core.flags[ot.toNat / 2]'(by omega) :=
      scc_getElem_congr _ _ (by dsimp only [off32, pos32, lit]; rw [hw0_get]; exact hdiv_ot)
    have htmk_ot : st3.scratch.tarjan_mark[(BitVec.setWidth 64 (st3.core.wstk[(BitVec.setWidth 64
        off32 + BitVec.setWidth 64 pos32).toNat]'hidx_lt &&& (2147483647 : BitVec 32))).toNat]'(
          by rw [htmk_l3]; dsimp only [off32, pos32, lit]; exact hot_z_lt) =
        st3.scratch.tarjan_mark[ot.toNat]'(by omega) :=
      scc_getElem_congr _ _ (by dsimp only [off32, pos32, lit]; rw [hw0_get]; exact hz_ot)
    dsimp only [off32, pos32, lit] at hflag_ot htmk_ot
    scc_split; rotate_left
    · exfalso; rw [hw0_get] at hc; have := scc_ult_false_ge hc; rw [hnl_eq, hz_ot] at this; omega
    scc_split; rotate_left
    · have hna : ¬ activeLit s0 ot.toNat := fun hact => hact.2 (by
        rw [← hfl3, List.getElem?_eq_getElem (by omega), Option.getD_some]
        dsimp only [st3a] at hc; rw [hflag_ot] at hc; exact Classical.not_not.mp hc)
      obtain ⟨hd4, hm4⟩ := hskip_ok (Or.inl hna)
      scc_steps; exact hJb (rch, dsp, ()) m ⟨st3a, hdsp_pos, hd4, hm4, hma⟩
    have hact_ot : activeLit s0 ot.toNat := ⟨hot_lt', by
      rw [← hfl3, List.getElem?_eq_getElem (by omega), Option.getD_some]
      dsimp only [st3a] at hc; rw [hflag_ot] at hc; exact hc⟩
    scc_split; rotate_left
    · have htmk_pos : 1 ≤ (st3.scratch.tarjan_mark[ot.toNat]?.getD 0#32).toNat := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        dsimp only [st3a] at hc; rw [htmk_ot] at hc
        exact Nat.pos_of_ne_zero fun h0 => hc (BitVec.eq_of_toNat_eq (by simpa using h0))
      obtain ⟨hd4, hm4⟩ := hskip_ok (Or.inr htmk_pos)
      scc_steps; exact hJb (rch, dsp, ()) m ⟨st3a, hdsp_pos, hd4, hm4, hma⟩
    have htmk_ot0 : (st3.scratch.tarjan_mark[ot.toNat]?.getD 0#32).toNat = 0 := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      dsimp only [st3a] at hc; rw [htmk_ot] at hc; rw [hc]; rfl
    have hr_lt3 := hd3.reached_lt_of_unvisited hot_lt' htmk_ot0
    have htop_lt3 : st3.core.tmp_cnt < 2 * s0.core.cur_vars := by have := hd3.top_le; omega
    have hdsp_lt3' : dsp.toNat < 2 * s0.core.cur_vars := by have := hd3.dsp_le; omega
    have hr1_3 : (rch + (1 : BitVec 32)).toNat = rch.toNat + 1 := scc_bv32_add1 (by omega)
    have hr32_3 : rch + (1 : BitVec 32) = BitVec.ofNat 32 (rch.toNat + 1) :=
      BitVec.eq_of_toNat_eq (by rw [hr1_3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
    have hdsp1 : (dsp + (1 : BitVec 64)).toNat = dsp.toNat + 1 := scc_bv64_add1 (by omega)
    have htc_mod : (BitVec.ofNat 64 st3.core.tmp_cnt).toNat = st3.core.tmp_cnt := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have htc_mod_a : (BitVec.ofNat 64 st3a.core.tmp_cnt).toNat = st3.core.tmp_cnt := htc_mod
    have htc1_a : (BitVec.ofNat 64 st3a.core.tmp_cnt + (1 : BitVec 64)).toNat =
        st3.core.tmp_cnt + 1 := (scc_bv64_add1 (by rw [htc_mod_a]; omega)).trans (by
          rw [htc_mod_a])
    obtain ⟨_, hdisc, hm_disc⟩ := tarjan_discover_node hw0 hdm0 hd3 hdsp_pos
      (by rw [← hpos_get]; exact hp1) (by rw [← hlit_get]; exact ⟨hlit_act, hact_ot, hbins_ot⟩)
      htmk_ot0 (by rw [← hlit_get]; exact hslc_b1)
    scc_steps
    let st4 : FullState :=
      { st3 with
        core := { st3.core with tmp_cnt := st3.core.tmp_cnt + 1 }
        scratch := { st3.scratch with
          wsort := (st3.scratch.wsort.set (dsp.toNat - 1) (pos32 + (1 : BitVec 32))).set
            dsp.toNat 0#32
          tarjan_mark := st3.scratch.tarjan_mark.set ot.toNat (BitVec.ofNat 32 (rch.toNat + 1))
          tarjan_reach := st3.scratch.tarjan_reach.set ot.toNat (BitVec.ofNat 32 (rch.toNat + 1))
          work_stk1 := st3.scratch.work_stk1.set st3.core.tmp_cnt ot
          work_stk2 := st3.scratch.work_stk2.set dsp.toNat ot } }
    have hm_d : (FullMem c st4 ⋆ R) m := by
      have hot_eq : (st3.core.wstk[(BitVec.setWidth 64 off32 +
          BitVec.setWidth 64 pos32).toNat]'hidx_lt &&& (2147483647 : BitVec 32)) = ot := by
        dsimp only [off32, pos32, lit]; rw [hw0_get]
      dsimp only [off32, pos32, lit] at hot_eq; dsimp only [st4, st3a] at hm ⊢
      rw [hot_eq, hz_ot, hr32_3, htc1_a, htc_mod_a] at hm; exact hm
    exact hJb (rch + (1 : BitVec 32), dsp + (1 : BitVec 64), ()) m
      ⟨st4, by rw [hdsp1]; omega, by rw [hr1_3, hdsp1]; exact hdisc,
       by rw [hr1_3, hdsp1]; exact hm_disc, hm_d⟩
  have hpos_ge : wsz ≤ (st3.scratch.wsort[dsp.toNat - 1]?.getD 0#32).toNat := by
    rw [← hpos_get, ← hsz_get]; exact scc_ult_false_ge hc
  have hlit_vis : ∀ v, activeEdge s0 lit.toNat v →
      1 ≤ (st3.scratch.tarjan_mark[v]?.getD 0#32).toNat := by
    intro v hv; obtain ⟨_, _, sc, hseq, hsok⟩ := hslc3
    have h0 : wsz - (st3.scratch.wsort[dsp.toNat - 1]?.getD 0#32).toNat = 0 := by omega
    rw [h0] at hseq; simp only [sliceBinsFrom, List.append_nil] at hseq
    exact hsok v (hseq ▸ hv.2.2) hv.2.1
  have hlit_tmk_eq : (st3.scratch.tarjan_reach[lit.toNat]?.getD 0#32).toNat =
      (st3.scratch.tarjan_mark[lit.toNat]?.getD 0#32).toNat := by
    have := hd3.dv_trc_eq (dsp.toNat - 1) (by omega); rwa [← hlit_get] at this
  have hlit_mroot : reached.toNat + 1 ≤ (st3.scratch.tarjan_mark[lit.toNat]?.getD 0#32).toNat := by
    obtain ⟨j, hj, hje⟩ := hd3.dv_on_scc (dsp.toNat - 1) (by omega)
    rw [← hlit_get] at hje; have := (hd3.scc_tmk_ge j hj).2; rwa [hje] at this
  have hz_lit : (BitVec.setWidth 64 lit).toNat = lit.toNat := zext_toNat lit (by decide)
  have hz_lit_u : (BitVec.setWidth 64
      (st3.scratch.work_stk2[(dsp - (1 : BitVec 64)).toNat]'(by rw [hdsp_sub]; omega))).toNat =
      lit.toNat := hz_lit
  have hz_lit_lt : (BitVec.setWidth 64
      (st3.scratch.work_stk2[(dsp - (1 : BitVec 64)).toNat]'(by rw [hdsp_sub]; omega))).toNat <
      2 * c.max_vars := by rw [hz_lit_u]; omega
  scc_to_group
  refine wp_loop_inv
    (fun (p, rlit, ()) mp => m3 = mp ∧ p.toNat ≤ wsz ∧
      WatchSliceOk F_cur s0.core (lit.toNat ^^^ 1) (woff + p.toNat) (wsz - p.toNat) ∧
      reached.toNat + 1 ≤ rlit.toNat ∧
      rlit.toNat ≤ (st3.scratch.tarjan_mark[lit.toNat]?.getD 0#32).toNat ∧
      (rlit.toNat < (st3.scratch.tarjan_mark[lit.toNat]?.getD 0#32).toNat →
        ∃ w < 2 * s0.core.cur_vars, onScc st3 w ∧
          (st3.scratch.tarjan_mark[w]?.getD 0#32).toNat = rlit.toNat ∧
          BinReach (cnfOfClauses F_cur) lit.toNat w) ∧
      ∃ sc, sliceBinsFrom s0.core.wstk woff wsz =
        sc ++ sliceBinsFrom s0.core.wstk (woff + p.toNat) (wsz - p.toNat) ∧
        ∀ ot ∈ sc, activeLit s0 ot → onScc st3 ot →
          rlit.toNat ≤ (st3.scratch.tarjan_reach[ot]?.getD 0#32).toNat)
    (fun (p, _, ()) _ => wsz - p.toNat) ?_ ?_
  · intro Jp hJp; scc_steps
    have htrc_get :
        st3.scratch.tarjan_reach[(BitVec.setWidth 64 lit).toNat]'(by rw [hz_lit]; omega) =
        st3.scratch.tarjan_reach[lit.toNat]?.getD 0#32 := by
      have hlt : lit.toNat < st3.scratch.tarjan_reach.length := by omega
      simp only [hz_lit, List.getElem?_eq_getElem hlt, Option.getD_some]
    dsimp only [lit] at htrc_get
    exact hJp (0#32, _, ()) m3 ⟨rfl, Nat.zero_le _, by
        rw [show (0#32 : BitVec 32).toNat = 0 from rfl, Nat.add_zero, Nat.sub_zero]
        exact hwat0.slices _ hnl_lt_nat,
      by rw [htrc_get, hlit_tmk_eq]; exact hlit_mroot,
      by rw [htrc_get, hlit_tmk_eq]; exact Nat.le_refl _,
      fun hlt => by rw [htrc_get, hlit_tmk_eq] at hlt; omega,
      [], by simp, fun _ hm => nomatch hm⟩
  rintro Jp ⟨p, rlit, ⟨⟩⟩ mp ⟨rfl, hp_le, hslc_p, hr_ge, hr_le, hr_wit, sc, hseq, hsok⟩ hJp
  scc_split
  · have hp_lt : p.toNat < wsz := by
      rw [← hsz_get]; exact BitVec.lt_def.mp (BitVec.ult_iff_lt.mp hc)
    have hidx_eq : (BitVec.setWidth 64 off32 + BitVec.setWidth 64 p).toNat = woff + p.toNat := by
      rw [scc_bv64_add (by rw [zext_toNat _ (by decide), zext_toNat _ (by decide)]; omega),
        zext_toNat _ (by decide), zext_toNat _ (by decide), hoff_get]
    have hidx_lt : (BitVec.setWidth 64 off32 + BitVec.setWidth 64 p).toNat <
        st3.core.wstk.length := by rw [hidx_eq]; omega
    have hidx_lt_u : (BitVec.setWidth 64 off32 + BitVec.setWidth 64 p).toNat < c.wcap := by
      rw [hidx_eq]; omega
    dsimp only [off32, lit] at hidx_lt_u
    scc_split
    · have hflag0 : (s0.core.wstk[woff + p.toNat]?.getD 0#32 &&& 0x80000000#32) = 0#32 := by
        rw [← hws3, List.getElem?_eq_getElem (by omega), Option.getD_some]
        dsimp only [off32, lit] at hidx_eq; simp only [hidx_eq] at hc; exact hc
      obtain ⟨_, _, h2le, _, _, _, _, _, hrest, hbins_eq⟩ :=
        watchSlice_step_nonbin hslc_p (by omega) hflag0
      have hp2 : (p + (2 : BitVec 32)).toNat = p.toNat + 2 := scc_bv32_add2 (by omega)
      scc_steps; exact hJp (p + (2 : BitVec 32), rlit, ()) m3 (by dsimp only; omega)
        ⟨rfl, by omega, by rw [hp2, ← Nat.add_assoc, Nat.sub_add_eq]; exact hrest, hr_ge, hr_le,
         hr_wit, sc, by rw [hseq, hbins_eq, hp2, ← Nat.add_assoc, Nat.sub_add_eq], hsok⟩
    have hflag1 : (s0.core.wstk[woff + p.toNat]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32 := by
      rw [← hws3, List.getElem?_eq_getElem (by omega), Option.getD_some]
      dsimp only [off32, lit] at hidx_eq; simp only [hidx_eq] at hc; exact hc
    obtain ⟨w0, hw0_eq, _, _, hot_lt, _, hrest, hbins_eq⟩ :=
      watchSlice_step_bin hslc_p (by omega) hflag1
    have hw0_get : st3.core.wstk[(BitVec.setWidth 64 off32 +
        BitVec.setWidth 64 p).toNat]'hidx_lt = w0 := by
      have h1 := hw0_eq; rw [← hws3, List.getElem?_eq_getElem (by omega)] at h1
      simpa only [hidx_eq] using Option.some.inj h1
    dsimp only [off32, lit] at hw0_get
    let ot := w0 &&& (2147483647 : BitVec 32)
    have hot_lt' : ot.toNat < 2 * s0.core.cur_vars := hot_lt
    have hz_ot : (BitVec.setWidth 64 ot).toNat = ot.toNat := zext_toNat ot (by decide)
    have hdiv_ot : (BitVec.setWidth 64 (ot >>> (BitVec.toNat (1 : BitVec 32) % 32))).toNat =
        ot.toNat / 2 := by
      rw [zext_toNat _ (by decide), show BitVec.toNat (1 : BitVec 32) % 32 = 1 from rfl,
        FullSccTactics.bv32_ushr1_nat]
    have hot_z_lt : (BitVec.setWidth 64 (st3.core.wstk[(BitVec.setWidth 64 off32 +
        BitVec.setWidth 64 p).toNat]'hidx_lt &&& (2147483647 : BitVec 32))).toNat <
        2 * c.max_vars := by
      dsimp only [off32, lit]; rw [hw0_get]; change (BitVec.setWidth 64 ot).toNat < _
      rw [hz_ot]; omega
    have hot_div_lt : (BitVec.setWidth 64 ((st3.core.wstk[(BitVec.setWidth 64 off32 +
        BitVec.setWidth 64 p).toNat]'hidx_lt &&& (2147483647 : BitVec 32)) >>>
          (BitVec.toNat (1 : BitVec 32) % 32))).toNat < c.max_vars := by
      dsimp only [off32, lit]; rw [hw0_get]
      change (BitVec.setWidth 64 (ot >>> (BitVec.toNat (1 : BitVec 32) % 32))).toNat < _
      rw [hdiv_ot]; omega
    have hflag_ot : st3.core.flags[(BitVec.setWidth 64 ((st3.core.wstk[(BitVec.setWidth 64 off32 +
        BitVec.setWidth 64 p).toNat]'hidx_lt &&& (2147483647 : BitVec 32)) >>>
          (BitVec.toNat (1 : BitVec 32) % 32))).toNat]'(
            by rw [hfl_l3]; dsimp only [off32, lit]; exact hot_div_lt) =
        st3.core.flags[ot.toNat / 2]'(by omega) :=
      scc_getElem_congr _ _ (by dsimp only [off32, lit]; rw [hw0_get]; exact hdiv_ot)
    have htrc_ot : st3.scratch.tarjan_reach[(BitVec.setWidth 64 (st3.core.wstk[(BitVec.setWidth 64
        off32 + BitVec.setWidth 64 p).toNat]'hidx_lt &&& (2147483647 : BitVec 32))).toNat]'(
          by rw [htrc_l3]; dsimp only [off32, lit]; exact hot_z_lt) =
        st3.scratch.tarjan_reach[ot.toNat]'(by omega) :=
      scc_getElem_congr _ _ (by dsimp only [off32, lit]; rw [hw0_get]; exact hz_ot)
    dsimp only [off32, lit] at hot_z_lt hot_div_lt hflag_ot htrc_ot
    have hp1 : (p + (1 : BitVec 32)).toNat = p.toNat + 1 := scc_bv32_add1 (by omega)
    have hbins_ot : ot.toNat ∈ sliceBinsFrom s0.core.wstk woff wsz := by
      rw [hseq, hbins_eq, List.mem_append, List.mem_cons]; exact Or.inr (Or.inl rfl)
    have hstep_rlit : ∀ (rlit' : BitVec 32), rlit'.toNat ≤ rlit.toNat →
        reached.toNat + 1 ≤ rlit'.toNat →
        (rlit'.toNat < (st3.scratch.tarjan_mark[lit.toNat]?.getD 0#32).toNat →
          ∃ w < 2 * s0.core.cur_vars, onScc st3 w ∧
            (st3.scratch.tarjan_mark[w]?.getD 0#32).toNat = rlit'.toNat ∧
            BinReach (cnfOfClauses F_cur) lit.toNat w) →
        (activeLit s0 ot.toNat → onScc st3 ot.toNat →
          rlit'.toNat ≤ (st3.scratch.tarjan_reach[ot.toNat]?.getD 0#32).toNat) →
        Jp (p + (1 : BitVec 32), rlit', ()) m3 := fun rlit' h1 h2 hw1 hot1 =>
      hJp (p + (1 : BitVec 32), rlit', ()) m3 (by dsimp only; omega)
        ⟨rfl, by omega, by rw [hp1, ← Nat.add_assoc, Nat.sub_add_eq]; exact hrest, h2, by omega,
         hw1, sc ++ [ot.toNat],
         by rw [hseq, hbins_eq, List.append_assoc, List.singleton_append, hp1, ← Nat.add_assoc,
              Nat.sub_add_eq]; rfl,
         fun x hx hax hox => by
           rcases List.mem_append.mp hx with ha | hb
           · exact Nat.le_trans h1 (hsok x ha hax hox)
           · simp only [List.mem_singleton] at hb; subst hb; exact hot1 hax hox⟩
    scc_to_group; scc_step; scc_split; rotate_left
    · exfalso; rw [hw0_get] at hc; have := scc_ult_false_ge hc; rw [hnl_eq, hz_ot] at this; omega
    scc_split; rotate_left
    · have hna : ¬ activeLit s0 ot.toNat := fun hact => hact.2 (by
        rw [← hfl3, List.getElem?_eq_getElem (by omega), Option.getD_some]
        rw [hflag_ot] at hc; exact Classical.not_not.mp hc)
      scc_steps; exact hstep_rlit rlit (Nat.le_refl _) hr_ge hr_wit (fun ha _ => absurd ha hna)
    have hact_ot : activeLit s0 ot.toNat := ⟨hot_lt', by
      rw [← hfl3, List.getElem?_eq_getElem (by omega), Option.getD_some]
      rw [hflag_ot] at hc; exact hc⟩
    scc_split; rotate_left
    · have hge : rlit.toNat ≤ (st3.scratch.tarjan_reach[ot.toNat]?.getD 0#32).toNat := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; rw [htrc_ot] at hc
        exact scc_ult_false_ge hc
      scc_steps; exact hstep_rlit rlit (Nat.le_refl _) hr_ge hr_wit (fun _ _ => hge)
    have htrc_lt : (st3.scratch.tarjan_reach[ot.toNat]?.getD 0#32).toNat < rlit.toNat := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; rw [htrc_ot] at hc
      exact BitVec.lt_def.mp (BitVec.ult_iff_lt.mp hc)
    have hot_vis := hlit_vis ot.toNat ⟨hlit_act, hact_ot, hbins_ot⟩
    have htrc_ne_ff : st3.scratch.tarjan_reach[ot.toNat]?.getD 0#32 ≠ 0xFFFFFFFF#32 := fun heq => by
      have := hd3.tmk_le lit.toNat hlit_lt; have := hd3.reached_le
      rw [heq] at htrc_lt; revert htrc_lt; simp; omega
    obtain ⟨jot, hjot, hjoteq⟩ := (hd3.scc_iff_trc ot.toNat hot_lt').mpr ⟨hot_vis, htrc_ne_ff⟩
    have hot_rng := hd3.trc_range jot hjot; rw [hjoteq] at hot_rng
    obtain ⟨w, hw_lt, hwon, hwtmk, hwbr⟩ := hd3.trc_witness jot hjot; rw [hjoteq] at hwtmk hwbr
    scc_steps; rw [htrc_ot]
    have htrc_some : st3.scratch.tarjan_reach[ot.toNat]'(by omega) =
        st3.scratch.tarjan_reach[ot.toNat]?.getD 0#32 := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    rw [htrc_some]
    exact hstep_rlit _ (by omega) hot_rng.1
      (fun _ => ⟨w, hw_lt, hwon, hwtmk, binReach_trans
        (BinReach.step (activeEdge_binEdge hw0 hdm0 ⟨hlit_act, hact_ot, hbins_ot⟩)
          (BinReach.refl _)) hwbr⟩) (fun _ _ => Nat.le_refl _)
  have hp_eq : p.toNat = wsz := by have := scc_ult_false_ge hc; rw [hsz_get] at this; omega
  have hscan : ∀ v, activeEdge s0 lit.toNat v → onScc st3 v →
      rlit.toNat ≤ (st3.scratch.tarjan_reach[v]?.getD 0#32).toNat := by
    intro v hv hov; have h0 : wsz - p.toNat = 0 := by omega
    rw [h0] at hseq; simp only [sliceBinsFrom, List.append_nil] at hseq
    exact hsok v (hseq ▸ hv.2.2) hv.2.1 hov
  have htmk_lit_get :
      st3.scratch.tarjan_mark[(BitVec.setWidth 64 lit).toNat]'(by rw [hz_lit]; omega) =
      st3.scratch.tarjan_mark[lit.toNat]?.getD 0#32 := by
    have hlt : lit.toNat < st3.scratch.tarjan_mark.length := by omega
    simp only [hz_lit, List.getElem?_eq_getElem hlt, Option.getD_some]
  dsimp only [lit] at htmk_lit_get
  scc_to_group
  refine wp_join_group (ts := [.bool])
    (fun (failb', ()) mj => ∃ st4 : FullState, TarjanLoopBase c F_cur s0 st4 ∧
      (st4.core.inconsistent = 0#64 →
        TarjanDfsInv c F0 F_cur s0 root.toNat (reached.toNat + 1) rch.toNat (dsp.toNat - 1) st4 ∧
        TarjanDfsInv.measure c s0 st4 rch.toNat (dsp.toNat - 1) <
          TarjanDfsInv.measure c s0 st3 rch.toNat dsp.toNat ∧
        (dsp.toNat - 1 = 0 → st4.core.tmp_cnt = 0)) ∧ (FullMem c st4 ⋆ R) mj) ?_ ?_
  · rintro _ ⟨failb', ⟨⟩⟩ mj ⟨st4, hbase4, hd4, hmj⟩; scc_steps
    by_cases hinc40 : st4.core.inconsistent = 0#64
    · obtain ⟨hd4', hm4', htop4'⟩ := hd4 hinc40
      exact hJ3 _ (rch, failb', dsp - (1 : BitVec 64), ()) mj hm4' ⟨st4, hbase4, fun _ =>
        ⟨by rw [hdsp_sub], by rwa [hdsp_sub], fun h => htop4' (by rwa [hdsp_sub] at h)⟩, hmj⟩
    · exact hJ3 0 (rch, failb', dsp - (1 : BitVec 64), ()) mj (TarjanDfsInv.measure_pos hdsp_pos)
        ⟨st4, hbase4, fun h => absurd h hinc40, hmj⟩
  intro Jpop hPopJ; scc_split
  · have hr_lt : rlit.toNat < (st3.scratch.tarjan_mark[lit.toNat]?.getD 0#32).toNat := by
      have hne : rlit ≠ st3.scratch.tarjan_mark[lit.toNat]?.getD 0#32 := by
        rw [← htmk_lit_get]; exact hc
      exact Nat.lt_of_le_of_ne hr_le fun heq => hne (BitVec.eq_of_toNat_eq heq)
    obtain ⟨hdsp_gt1, hd4, hm4⟩ := tarjan_pop_nonroot hd3 hdsp_pos
      (by rw [← hlit_get]; exact hpos_ge) hr_ge (by rw [← hlit_get]; exact hr_lt)
      (by rw [← hlit_get]; exact hscan) (by rw [← hlit_get]; exact hr_wit hr_lt)
    rw [← hlit_get] at hd4 hm4; scc_steps
    let st4 : FullState := { st3 with scratch := { st3.scratch with
      tarjan_reach := st3.scratch.tarjan_reach.set lit.toNat rlit } }
    have hm4' : (FullMem c st4 ⋆ R) m := by dsimp only [st4]; rw [hz_lit_u] at hm; exact hm
    exact hPopJ (failb, ()) m ⟨st4, hd4.toBase, fun _ => ⟨hd4, hm4, fun h => by omega⟩, hm4'⟩
  have hr_eq : rlit.toNat = (st3.scratch.tarjan_mark[lit.toNat]?.getD 0#32).toNat := by
    rw [← htmk_lit_get]; exact congrArg BitVec.toNat (Classical.not_not.mp hc)
  obtain ⟨k0, hk0_lt, hk0_bv, hk0_uniq, hk0_zero, hk0_eqv⟩ :=
    hd3.scc_pop_equiv hw0 hdm0 hdsp_pos (by rw [← hlit_get, ← hr_eq]; exact hscan)
  have hmr_reach : reached + (1 : BitVec 32) ≠ 0xFFFFFFFF#32 →
      (∀ j, k0 ≤ j → j < st3.core.tmp_cnt → BinReach (cnfOfClauses F_cur)
        (BitVec.setWidth 32 root).toNat (st3.scratch.work_stk1[j]?.getD 0#32).toNat) ∧
      (∀ l < 2 * st3.core.cur_vars,
        (reached + (1 : BitVec 32)).toNat ≤
          (st3.scratch.tarjan_mark[l]?.getD 0#32).toNat →
        BinReach (cnfOfClauses F_cur) (BitVec.setWidth 32 root).toNat l) := fun _ => by
    simp only [hr1_nat, bv32_trunc_toNat (x := root) (by omega)]
    exact ⟨fun j _ hj => hd3.mroot_reach hdsp_pos _ (hd3.scc_lt j hj) (hd3.scc_tmk_ge j hj).2,
      fun l hl hge => hd3.mroot_reach hdsp_pos l (by omega) hge⟩
  scc_steps
  · refine scc_pop_call_wp hPop hw0 hinc30 hdsp_pos hrt_lt hlit_lt hd3 hlit_get hk0_lt
      hk0_bv hk0_uniq hk0_zero hk0_eqv (fun h => absurd rfl h) hm3 (fun b mj h => ?_)
    dsimp only; scc_steps; first | exact h | exact hPopJ (b, ()) mj h
  · refine scc_pop_call_wp hPop hw0 hinc30 hdsp_pos hrt_lt hlit_lt hd3 hlit_get hk0_lt
      hk0_bv hk0_uniq hk0_zero hk0_eqv hmr_reach hm3 (fun b mj h => ?_)
    dsimp only; scc_steps; first | exact h | exact hPopJ (b, ()) mj h

theorem fast_tarjan_scc_canon_wp (Γ : Env)
    (hPop : ∀ args m Q X, Full.fullTarjanPopSccSpec args m Q X →
      Γ "full_tarjan_pop_scc" [i64, i32, i32, i32] [.bool] args m Q X) :
    ∀ args m Q X, Full.fullTarjanSccSpec args m Q X →
      Func.wp Γ full_tarjan_scc_body args m Q X :=
  fun _ _ _ _ h => fast_tarjan_scc_wp Γ hPop _ _ _ _ (fullTarjanSccFastSpec_of_canon h)

end TarjanSccProof

/-! ## 8. `fast_bve_var_wp` & `fast_bve_var_def_wp` (`64u` occ cap + `P_ng × N_ng` gate skip) -/

section BveVarProof

open FullBveVarTactics FullBveVarHelpers FullArenaTactics
open scoped FullArenaTactics FullBveVarTactics

private theorem bl_fst {α β : Type _} (a : α) (b : β) : (a, b).fst = a := rfl
private theorem bl_snd {α β : Type _} (a : α) (b : β) : (a, b).snd = b := rfl
private theorem bl_add32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {k m} :
    wp Γ Q X (.let_ (Op.mk (.add i32) (a, b, ())) k) m =
      wp Γ Q X (k (a.val + b.val, ())) m := by simp [wp_let_add_eq, lift2]
private theorem bl_add64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {k m} :
    wp Γ Q X (.let_ (Op.mk (.add i64) (a, b, ())) k) m =
      wp Γ Q X (k (a.val + b.val, ())) m := by simp [wp_let_add_eq, lift2]
private theorem bl_sub64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {k m} :
    wp Γ Q X (.let_ (Op.mk (.sub i64) (a, b, ())) k) m =
      wp Γ Q X (k (a.val - b.val, ())) m := by simp [wp_let_sub_eq, lift2]
private theorem bl_mul64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {k m} :
    wp Γ Q X (.let_ (Op.mk (.mul i64) (a, b, ())) k) m =
      wp Γ Q X (k (a.val * b.val, ())) m := by simp [wp_let_mul_eq, lift2]
private theorem bl_shl32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {k m} :
    wp Γ Q X (.let_ (Op.mk (.shl i32) (a, b, ())) k) m =
      wp Γ Q X (k (a.val <<< (b.val.toNat % 32), ())) m := by simp [wp_let_shl_eq, lift2]
private theorem bl_shl64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {k m} :
    wp Γ Q X (.let_ (Op.mk (.shl i64) (a, b, ())) k) m =
      wp Γ Q X (k (a.val <<< (b.val.toNat % 64), ())) m := by simp [wp_let_shl_eq, lift2]
private theorem bl_lshr64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {k m} :
    wp Γ Q X (.let_ (Op.mk (.lshr i64) (a, b, ())) k) m =
      wp Γ Q X (k (a.val >>> (b.val.toNat % 64), ())) m := by simp [wp_let_lshr_eq, lift2]
private theorem bl_and32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {k m} :
    wp Γ Q X (.let_ (Op.mk (.and i32) (a, b, ())) k) m =
      wp Γ Q X (k (a.val &&& b.val, ())) m := by simp [wp_let_and_eq, lift2]
private theorem bl_and64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {k m} :
    wp Γ Q X (.let_ (Op.mk (.and i64) (a, b, ())) k) m =
      wp Γ Q X (k (a.val &&& b.val, ())) m := by simp [wp_let_and_eq, lift2]
private theorem bl_or32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {k m} :
    wp Γ Q X (.let_ (Op.mk (.or i32) (a, b, ())) k) m =
      wp Γ Q X (k (a.val ||| b.val, ())) m := by simp [wp_let_or_eq, lift2]
private theorem bl_or64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {k m} :
    wp Γ Q X (.let_ (Op.mk (.or i64) (a, b, ())) k) m =
      wp Γ Q X (k (a.val ||| b.val, ())) m := by simp [wp_let_or_eq, lift2]
private theorem bl_not_bool {Γ} {rs : List Ty} {Q : Post rs} {X} {a : Arg Val .bool} {k m} :
    wp Γ Q X (.let_ (Op.mk (.not .bool) (a, ())) k) m =
      wp Γ Q X (k (!a.val, ())) m := by simp [wp_let_not_eq, lift1]
private theorem bl_zext32_64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a : Arg Val i32} {k m} :
    wp Γ Q X (.let_ (Op.mk (.zext 32 64) (a, ())) k) m =
      wp Γ Q X (k (a.val.setWidth 64, ())) m := by simp [wp_let_zext_eq]
private theorem bl_sext32_64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a : Arg Val i32} {k m} :
    wp Γ Q X (.let_ (Op.mk (.sext 32 64) (a, ())) k) m =
      wp Γ Q X (k (a.val.signExtend 64, ())) m := by simp [wp_let_sext_eq]
private theorem bl_trunc64_32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a : Arg Val i64} {k m} :
    wp Γ Q X (.let_ (Op.mk (.trunc 64 32) (a, ())) k) m =
      wp Γ Q X (k (a.val.setWidth 32, ())) m := by simp [wp_let_trunc_eq]
private theorem bl_ult32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ult i32 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (a.val.ult b.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_ult_eq]
private theorem bl_ugt32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ugt i32 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (b.val.ult a.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_ugt_eq]
private theorem bl_ult64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ult i64 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (a.val.ult b.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_ult_eq]
private theorem bl_ule64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ule i64 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (a.val.ule b.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_ule_eq]
private theorem bl_ugt64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ugt i64 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (b.val.ult a.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_ugt_eq]
private theorem bl_eq32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .eq i32 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (a.val == b.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_eq_beq]
private theorem bl_ne32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i32} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ne i32 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (a.val != b.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_ne_bne]
private theorem bl_eq64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .eq i64 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (a.val == b.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_eq_beq]
private theorem bl_ne64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a b : Arg Val i64} {h} {k m} :
    wp Γ Q X (.let_ (Op.mk (.cmp .ne i64 .bool h) (a, b, ())) k) m =
      wp Γ Q X (k (a.val != b.val, ())) m := by simp [wp_let_cmp_eq, liftCmp, evalBits_ne_bne]
private theorem bl_copy_bool {Γ} {rs : List Ty} {Q : Post rs} {X} {a : Arg Val .bool} {k m} :
    wp Γ Q X (.let_ (Op.mk (.copy .bool) (a, ())) k) m =
      wp Γ Q X (k (a.val, ())) m := by simp [wp_let_copy_eq]
private theorem bl_copy32 {Γ} {rs : List Ty} {Q : Post rs} {X} {a : Arg Val i32} {k m} :
    wp Γ Q X (.let_ (Op.mk (.copy i32) (a, ())) k) m =
      wp Γ Q X (k (a.val, ())) m := by simp [wp_let_copy_eq]
private theorem bl_copy64 {Γ} {rs : List Ty} {Q : Post rs} {X} {a : Arg Val i64} {k m} :
    wp Γ Q X (.let_ (Op.mk (.copy i64) (a, ())) k) m =
      wp Γ Q X (k (a.val, ())) m := by simp [wp_let_copy_eq]
private theorem bl_ret {Γ} {rs : List Ty} {Q : Post rs} {X} {args : Tup (Arg Val) rs} {m} :
    wp Γ Q X (.ret args) m = Q (LeanQbe.T.vals args) m := rfl
private theorem bl_jump {Γ} {rs ts : List Ty} {Q : Post rs} {X} {L : Cont ts}
    {args : Tup (Arg Val) ts} {m} : wp Γ Q X (.jump L args) m = L (LeanQbe.T.vals args) m := rfl
private theorem bl_jnz {Γ} {rs : List Ty} {Q : Post rs} {X} {c : Val .bool} {t e m} :
    wp Γ Q X (.jnz (.var c) t e) m =
      ((c = true → wp Γ Q X t m) ∧ (c = false → wp Γ Q X e m)) := rfl
private theorem bl_wp_beta {Γ : Env} {rs bs : List Ty} {Q : Post rs} {X : XPost}
    {k : Tup Val bs → Expr Val Cont rs} {r : Tup Val bs} {m' : Mem 64} :
    (fun r0 m0 => wp Γ Q X (k r0) m0) r m' = wp Γ Q X (k r) m' := rfl

local syntax "bve_lets" : tactic
local macro_rules
  | `(tactic| bve_lets) => `(tactic| (
      (try rw [bl_wp_beta]);
      repeat (first
        | rw [bl_fst] | rw [bl_snd]
        | rw [bl_add32] | rw [bl_add64] | rw [bl_sub64] | rw [bl_mul64]
        | rw [bl_shl32] | rw [bl_shl64] | rw [bl_lshr64]
        | rw [bl_and32] | rw [bl_and64] | rw [bl_or32] | rw [bl_or64] | rw [bl_not_bool]
        | rw [bl_zext32_64] | rw [bl_sext32_64] | rw [bl_trunc64_32]
        | rw [bl_ult32] | rw [bl_ugt32] | rw [bl_ult64] | rw [bl_ule64] | rw [bl_ugt64]
        | rw [bl_eq32] | rw [bl_ne32] | rw [bl_eq64] | rw [bl_ne64]
        | rw [bl_copy_bool] | rw [bl_copy32] | rw [bl_copy64]
        | rw [Arg.val_var] | rw [Arg.val_imm])))

local macro "bve_ld " lem:term : tactic =>
  `(tactic| (bve_lets; refine wp_load_of $lem ?_; bve_lets))

local macro "bve_st " m:ident ", " h:ident " := " lem:term : tactic =>
  `(tactic| ((bve_lets; apply wp_store_sep; · exact $lem); intro $m:ident $h:ident; bve_lets))

local macro "bve_jnz " hc:ident : tactic =>
  `(tactic| (bve_lets; rw [bl_jnz]; refine ⟨fun $hc:ident => ?_, fun $hc:ident => ?_⟩))

local macro "bve_ret" : tactic =>
  `(tactic| (bve_lets; rw [bl_ret]; simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]))

local macro "bve_jump" : tactic =>
  `(tactic| (bve_lets; rw [bl_jump]; simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]))

private theorem bve_resBuf_of_bve {F_cur : List (List Nat)} {s : FullState} {r_end p : Nat}
    (h : FullBveVarSpecs.FullResBufOkW F_cur s r_end p) : FullResBufOkW F_cur s r_end p := by
  induction h with
  | nil => exact .nil
  | cons hbd hsz hlts hnd hent _ ih => exact .cons hbd hsz hlts hnd hent ih

private theorem bve_setInact_adapter {Γ : Env}
    (hSetInact : ∀ a m Q X, fullSetInactiveSpec a m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] a m Q X) :
    ∀ a m Q X, FullBveVarSpecs.fullSetInactiveSpec a m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] a m Q X := by
  rintro ⟨h, v, flag, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  refine hSetInact _ m Q X ⟨c, s, R, rfl, hlen, hm, ?_⟩
  split
  · exact hQ s.core.flags s.core.unassigned m hlen.core_ok.flags_len hm
  · exact hQ

private theorem bve_tryBce_adapter {Γ : Env}
    (hTryBce : ∀ a m Q X, fullBveTryBceSpec a m Q X →
      Γ "full_bve_try_bce" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, FullBveVarSpecs.fullBveTryBceSpec a m Q X →
      Γ "full_bve_try_bce" [i64, i32, i32, i32, i32] [.bool] a m Q X := by
  rintro ⟨h, blk_lit, cr, opp_off, opp_n, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hdense, hblk, hcr, hoff, hopp, hm, hQ⟩
  have hcr_w : FullBveBceWeakOk c s cr := by
    unfold FullBveBceWeakOk; unfold FullBveVarSpecs.FullBveTryBceEntryOk at hcr
    by_cases hmsb : (cr &&& 0x80000000#32) ≠ 0#32
    · rw [ite_eq_left hmsb] at hcr ⊢; exact hcr
    · rw [ite_eq_right hmsb] at hcr ⊢; exact ⟨hcr.1, hcr.2.1, hcr.2.2.1⟩
  have hcr_nd : (cr &&& 0x80000000#32) = 0#32 →
      ((fullArenaClauseLits s cr.toNat).map (· / 2)).Nodup := by
    intro h0; unfold FullBveVarSpecs.FullBveTryBceEntryOk at hcr
    rw [ite_eq_right (Classical.not_not.mpr h0)] at hcr; exact hcr.2.2.2
  exact hTryBce _ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hdense, hblk, hcr_w, hcr_nd, hoff, hopp, hm, hQ⟩

/-- Shared invariant for the BCE fallback loop and its inner branches (`128`-entry occ buffer). -/
private def BveBceStepInv (TmkInv : FullState → Prop) (c : FullCfg) (F0 : CNF Nat)
    (F_cur : List (List Nat)) (s : FullState) (scr2 : List (BitVec 32))
    (np nn : BitVec 32) (R : Mem 64 → Prop) (sn : FullState) (mn : Mem 64) : Prop :=
  FullBveVarSpecs.FullDenseInvW c F0 F_cur sn ∧ TmkInv sn ∧
  sn.core.cur_vars = s.core.cur_vars ∧ sn.core.fuel.toNat ≤ s.core.fuel.toNat ∧
  (∀ idx < 128, sn.scratch.scratch_buf[idx]? = scr2[idx]?) ∧
  (∀ k < np.toNat, FullBveVarSpecs.FullBveTryBceEntryOk c sn (scr2[k]?.getD 0#32)) ∧
  (∀ j < nn.toNat, FullBveVarSpecs.FullBveTryBceOppOk c sn (scr2[64 + j]?.getD 0#32)) ∧
  (FullMem c sn ⋆ R) mn

/-- Parametric `full_bve_var` core proof (`64u` occ limit + `P_ng × N_ng` gate skip), parameterized
by `TmkInv` so both canonical `Full.fullBveVarSpec` (`TmkInv := fun _ => True`) and M2
`FullDefSweep`-compatible `fullBveVarDefSpec` (`TmkInv := TmkZero`) follow cleanly. -/
private theorem fast_bve_var_core_wp (Γ : Env) (TmkInv : FullState → Prop)
    (hTmk_cong : ∀ {s s' : FullState}, TmkInv s → s'.core.cur_vars = s.core.cur_vars →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark → TmkInv s')
    (hCollect : ∀ xs m Q X, FullBveVarSpecs.fullBveCollectSpec xs m Q X →
      Γ "full_bve_collect" [i64, i32, i64, i32] [i32] xs m Q X)
    (hExtNeed : ∀ xs m Q X, FullBveVarSpecs.fullBveExtNeedSpec xs m Q X →
      Γ "full_bve_ext_need" [i64, i32, i32] [i64] xs m Q X)
    (hWeaken : ∀ (h : BitVec 64) (blk_lit off cnt : BitVec 32) m Q X,
      (∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
        h = c.hdr ∧ FullBveVarSpecs.FullDenseInvW c F0 F_cur s ∧ TmkInv s ∧
        blk_lit.toNat < 2 * s.core.cur_vars ∧ off.toNat + cnt.toNat ≤ c.scratch_cap ∧
        (∀ i < cnt.toNat,
          FullBveVarSpecs.FullBveWeakItemOk s (s.scratch.scratch_buf[off.toNat + i]?.getD 0#32)) ∧
        (FullMem c s ⋆ R) m ∧
        ∀ (ok : Bool) s' m',
          FullBveVarSpecs.FullDenseInvW c F0 F_cur s' → TmkInv s' →
          s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
          s'.scratch.scratch_buf = s.scratch.scratch_buf →
          fullArenaClauseRefs s' = fullArenaClauseRefs s →
          (FullMem c s' ⋆ R) m' → Q (ok, ()) m') →
      Γ "full_bve_weaken" [i64, i32, i32, i32] [.bool] (h, blk_lit, off, cnt, ()) m Q X)
    (hSetInact : ∀ xs m Q X, FullBveVarSpecs.fullSetInactiveSpec xs m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] xs m Q X)
    (hGates : ∀ (h : BitVec 64) (v np nn : BitVec 32) m Q X,
      (∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
        h = c.hdr ∧ FullBveVarSpecs.FullDenseInvW c F0 F_cur s ∧ 132 ≤ c.scratch_cap ∧ TmkInv s ∧
        v.toNat < s.core.cur_vars ∧ np.toNat ≤ 64 ∧ nn.toNat ≤ 64 ∧
        (∀ i < np.toNat, FullBveVarSpecs.FullBveEntryOkW F_cur s (2 * v.toNat)
          (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
        (∀ j < nn.toNat, FullBveVarSpecs.FullBveEntryOkW F_cur s (2 * v.toNat + 1)
          (s.scratch.scratch_buf[64 + j]?.getD 0#32)) ∧
        (FullMem c s ⋆ R) m ∧
        ∀ s' m',
          FullBveVarSpecs.FullDenseInvW c F0 F_cur s' → TmkInv s' →
          s'.core.cur_vars = s.core.cur_vars →
          s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
          s'.core.fuel.toNat ≤ s.core.fuel.toNat →
          (∀ i < 128, s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) →
          (FullMem c s' ⋆ R) m' → Q () m') →
      Γ "full_bve_gates" [i64, i32, i32, i32] [] (h, v, np, nn, ()) m Q X)
    (hResolve : ∀ xs m Q X, FullBveVarSpecs.fullBveResolvePairSpec xs m Q X →
      Γ "full_bve_resolve_pair" [i64, i32, i32, i32] [.bool] xs m Q X)
    (hCommitRes : ∀ (h r_off r_end : BitVec 64) m Q X,
      (∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
        h = c.hdr ∧ FullBveVarSpecs.FullDenseInvW c F0 F_cur s ∧ TmkInv s ∧
        r_off.toNat ≤ r_end.toNat ∧ r_end.toNat ≤ c.scratch_cap ∧
        FullBveVarSpecs.FullResBufOkW F_cur s r_end.toNat r_off.toNat ∧ (FullMem c s ⋆ R) m ∧
        ∀ r s' m',
          FullBveVarSpecs.FullDenseInvW c F0 F_cur s' → TmkInv s' →
          s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
          (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
          (FullMem c s' ⋆ R) m' → Q (r, ()) m') →
      Γ "full_bve_commit_res" [i64, i64, i64] [i64] (h, r_off, r_end, ()) m Q X)
    (hTryBce : ∀ xs m Q X, FullBveVarSpecs.fullBveTryBceSpec xs m Q X →
      Γ "full_bve_try_bce" [i64, i32, i32, i32, i32] [.bool] xs m Q X)
    (hExtPush2 : ∀ (h : BitVec 64) (blk ot : BitVec 32) m Q X,
      (∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
        (h = c.hdr ∧ s.scratch.extend_len ≤ c.extend_cap) ∧ s.LengthsOk c ∧ TmkInv s ∧
        (FullMem c s ⋆ R) m ∧
        ∀ (r : Tup Val [.bool]) s' m',
          PreservesCoreSlice (fullSafetySlice c).coreProj s s' → s'.LengthsOk c →
          (s'.scratch.last_learned = s.scratch.last_learned ∧
           s'.scratch.extend_len ≤ c.extend_cap ∧
           s'.scratch.scratch_buf = s.scratch.scratch_buf) →
          TmkInv s' → (FullMem c s' ⋆ R) m' → Q r m') →
      Γ "full_extend_push2" [i64, i32, i32] [.bool] (h, blk, ot, ()) m Q X)
    (hDelBin : ∀ xs m Q X, FullBveVarSpecs.fullDeleteBinarySpec xs m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] xs m Q X)
    (hExtPushCl : ∀ (h : BitVec 64) (blk cr : BitVec 32) m Q X,
      (∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
        (h = c.hdr ∧ s.scratch.extend_len ≤ c.extend_cap) ∧ s.LengthsOk c ∧ TmkInv s ∧
        (FullMem c s ⋆ R) m ∧
        ∀ (r : Tup Val [.bool]) s' m',
          PreservesCoreSlice (fullSafetySlice c).coreProj s s' → s'.LengthsOk c →
          (s'.scratch.last_learned = s.scratch.last_learned ∧
           s'.scratch.extend_len ≤ c.extend_cap ∧
           s'.scratch.scratch_buf = s.scratch.scratch_buf) →
          TmkInv s' → (FullMem c s' ⋆ R) m' → Q r m') →
      Γ "full_extend_push_cl" [i64, i32, i32] [.bool] (h, blk, cr, ()) m Q X)
    {c : FullCfg} {F0 : CNF Nat} {s : FullState} {R : Mem 64 → Prop} {v : BitVec 32}
    {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hdense : FullBveVarSpecs.FullDenseInv c F0 s) (htmk0 : TmkInv s)
    (hv_lt : v.toNat < s.core.cur_vars) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ r s' m',
      FullBveVarSpecs.FullDenseInv c F0 s' → TmkInv s' →
      s.core.cur_vars ≤ s'.core.cur_vars → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    Func.wp Γ full_bve_var_body (c.hdr, v, ()) m Q X := by
  obtain ⟨F_cur, hinv⟩ := fullDenseInv_exists_witness hdense
  have hmv := c.hmaxv; have harc := c.harena; have hsc := c.hscr
  unfold dimacsBound at hmv harc hsc
  have hcv_le : s.core.cur_vars ≤ c.max_vars := hinv.1.core_ok.cur_vars_le
  have hv_lt32 : 2 * v.toNat < 2 ^ 32 := by omega
  let pl := v <<< ((1 : BitVec 32).toNat % 32)
  have hpl_nat : pl.toNat = 2 * v.toNat := by dsimp only [pl]; exact bv32_shl1_toNat hv_lt32
  have hnl_nat : (pl ||| 1#32).toNat = 2 * v.toNat + 1 := bv32_or1_even_toNat hpl_nat
  unfold Func.wp full_bve_var_body
  bve_ld load_full_scratch_cap hm
  bve_jnz hsc_ult
  · bve_ret
    exact hQ 1#64 s m hdense htmk0 (Nat.le_refl _) (Nat.le_refl _) (Or.inl rfl)
      (fun h => by cases h) hm
  · have hsc512 : 512 ≤ c.scratch_cap := by
      rw [BitVec.ult, decide_eq_false_iff_not, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : c.scratch_cap < 2 ^ 64),
        show (512 : BitVec 64).toNat = 512 from rfl] at hsc_ult
      omega
    bve_ld load_full_scratch_buf_ptr hm
    bve_lets
    refine wp_call_of_spec _ _ (hCollect _ _ _ X ?_)
    simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
    refine ⟨c, F0, F_cur, s, 0, R, rfl, hinv,
      (by change pl.toNat < 2 * s.core.cur_vars; rw [hpl_nat]; omega),
      (by rw [Nat.mul_zero]; exact (BitVec.add_zero c.pScratchBuf).symm),
      (by rw [show (64 : BitVec 32).toNat = 64 from rfl]; omega), hm, ?_⟩
    dsimp only; rintro np scr1 m1 hlen1 hkeep1 hres1 hm1
    let s1 : FullState := { s with scratch := { s.scratch with scratch_buf := scr1 } }
    have hinv1 := FullBveVarHelpers.FullDenseInvW.with_scratch_buf hinv hlen1
    have htmk1 : TmkInv s1 := hTmk_cong htmk0 rfl rfl
    have hptr64 : c.pScratchBuf + (BitVec.signExtend 64 64#32) * 4 =
        c.pScratchBuf + BitVec.ofNat 64 (4 * 64) := by
      apply congrArg (c.pScratchBuf + ·); decide
    bve_lets
    refine wp_call_of_spec _ _ (hCollect _ _ _ X ?_)
    simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
    refine ⟨c, F0, F_cur, s1, 64, R, rfl, hinv1,
      (by change (pl ||| 1#32).toNat < 2 * s.core.cur_vars; rw [hnl_nat]; omega),
      hptr64, (by rw [show (64 : BitVec 32).toNat = 64 from rfl]; omega), hm1, ?_⟩
    dsimp only; rintro nn scr2 m2 hlen2 hkeep2 hres2 hm2
    let s2 : FullState := { s1 with scratch := { s1.scratch with scratch_buf := scr2 } }
    have hinv2 := FullBveVarHelpers.FullDenseInvW.with_scratch_buf hinv1 hlen2
    have htmk2 : TmkInv s2 := hTmk_cong htmk1 rfl rfl
    bve_jnz hnp_eq
    · bve_ret
      exact hQ 1#64 s2 m2 hinv2.toDense htmk2 (Nat.le_refl _) (Nat.le_refl _) (Or.inl rfl)
        (fun h => by cases h) hm2
    · bve_jnz hnn_eq
      · bve_ret
        exact hQ 1#64 s2 m2 hinv2.toDense htmk2 (Nat.le_refl _) (Nat.le_refl _) (Or.inl rfl)
          (fun h => by cases h) hm2
      · have hnp_ne : np ≠ 0xFFFFFFFF#32 := by intro h; rw [h] at hnp_eq; cases hnp_eq
        have hnn_ne : nn ≠ 0xFFFFFFFF#32 := by intro h; rw [h] at hnn_eq; cases hnn_eq
        have hnp_res : np.toNat ≤ 64 ∧
            ∀ i < np.toNat, FullBveVarSpecs.FullBveEntryOkW F_cur s1 pl.toNat
              (scr1[i]?.getD 0#32) := by
          rcases hres1 with rfl | h
          · exact absurd rfl hnp_ne
          · exact ⟨by simpa only [show (64 : BitVec 32).toNat = 64 from rfl] using h.1,
              fun i hi => by simpa only [Nat.zero_add] using h.2 i hi⟩
        have hnn_res : nn.toNat ≤ 64 ∧
            ∀ j < nn.toNat, FullBveVarSpecs.FullBveEntryOkW F_cur s2 (pl ||| 1#32).toNat
              (scr2[64 + j]?.getD 0#32) := by
          rcases hres2 with rfl | h
          · exact absurd rfl hnn_ne
          · exact ⟨by simpa only [show (64 : BitVec 32).toNat = 64 from rfl] using h.1, h.2⟩
        have hnp_le : np.toNat ≤ 64 := hnp_res.1
        have hnn_le : nn.toNat ≤ 64 := hnn_res.1
        have hp_ok : ∀ i < np.toNat,
            FullBveVarSpecs.FullBveEntryOkW F_cur s2 (2 * v.toNat) (scr2[i]?.getD 0#32) :=
          fun i hi => by
            rw [hkeep2 i (by omega) (Or.inl (by omega)), ← hpl_nat]
            exact FullBveVarHelpers.FullBveEntryOkW.with_state
              (Nat.le_refl _) rfl rfl (hnp_res.2 i hi)
        have hn_ok : ∀ j < nn.toNat,
            FullBveVarSpecs.FullBveEntryOkW F_cur s2 (2 * v.toNat + 1)
              (scr2[64 + j]?.getD 0#32) := fun j hj => by rw [← hnl_nat]; exact hnn_res.2 j hj
        have hs2_cv : s2.core.cur_vars = s.core.cur_vars := rfl
        have hs2_fl : s2.core.fuel = s.core.fuel := rfl
        have h0_32 : (0 : BitVec 32).toNat = 0 := rfl
        have h64_32 : (64 : BitVec 32).toNat = 64 := rfl
        bve_lets
        refine wp_call_of_spec _ _ (hExtNeed _ _ _ X ?_)
        simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
        refine ⟨c, s2, R, rfl, hinv2.1, (by rw [h0_32]; omega),
          entries_to_extNeed hinv2 (off := 0) (lit := 2 * v.toNat) (fun i hi => by
            rw [Nat.zero_add]; exact hp_ok i hi), hm2, ?_⟩
        intro en1; bve_lets
        refine wp_call_of_spec _ _ (hExtNeed _ _ _ X ?_)
        simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
        refine ⟨c, s2, R, rfl, hinv2.1, (by rw [h64_32]; omega),
          entries_to_extNeed hinv2 (off := 64) (lit := 2 * v.toNat + 1) hn_ok, hm2, ?_⟩
        intro en2
        bve_ld load_full_extend_len hm2
        bve_ld load_full_extend_cap hm2
        bve_lets
        refine wp_join_group (ts := []) (fun _ ml => ml = m2) ?_ ?_
        · rintro J _ ml h_ml; subst ml; rw [Blocks.get_here]
          bve_lets; bve_ld load_full_elim_bound hm2; bve_lets
          refine wp_join_group (ts := [i64, i64, .bool]) (fun (_rc_f, rp_f, fit_f, _) ml =>
              ∃ sf, FullBveVarSpecs.FullDenseInvW c F0 F_cur sf ∧ TmkInv sf ∧
                sf.core.cur_vars = s2.core.cur_vars ∧ sf.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                sf.core.arena = s2.core.arena ∧ sf.core.arena_len = s2.core.arena_len ∧
                (∀ idx < 128, sf.scratch.scratch_buf[idx]? = scr2[idx]?) ∧
                (fit_f = true → 160 ≤ rp_f.toNat ∧ rp_f.toNat ≤ c.scratch_cap ∧
                  FullBveVarSpecs.FullResBufOkW F_cur sf rp_f.toNat 160) ∧
                (FullMem c sf ⋆ R) ml) ?_ ?_
          · rintro J_fit ⟨rc_f, rp_f, fit_f, ⟨⟩⟩ ml
              ⟨sf, hinvf, htmkf, hcvf, hflf, harf, half, hbuf_f, hres_f, hmf⟩
            rw [Blocks.get_here]; bve_lets
            refine wp_join_group (ts := []) (fun _ m_bce =>
                ∃ sb, FullBveVarSpecs.FullDenseInvW c F0 F_cur sb ∧ TmkInv sb ∧
                  sb.core.cur_vars = s2.core.cur_vars ∧ sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                  sb.core.arena = s2.core.arena ∧ sb.core.arena_len = s2.core.arena_len ∧
                  (∀ idx < 128, sb.scratch.scratch_buf[idx]? = scr2[idx]?) ∧
                  (FullMem c sb ⋆ R) m_bce) ?_ ?_
            · rintro J_bce _ m_bce ⟨sb, hinvb, htmkb, hcvb, hflb, harb, halb, hbuf_b, hmb⟩
              rw [Blocks.get_here]; bve_lets
              have hpbce : ∀ i < np.toNat,
                  FullBveVarSpecs.FullBveTryBceEntryOk c sb (scr2[i]?.getD 0#32) := fun i hi =>
                FullBveTryBceEntryOk.with_same_arena harb halb
                  (FullBveVarHelpers.FullBveEntryOkW.to_tryBceEntry hinv2 (hp_ok i hi))
              have hnbce : ∀ j < nn.toNat,
                  FullBveVarSpecs.FullBveTryBceOppOk c sb (scr2[64 + j]?.getD 0#32) := fun j hj =>
                FullBveTryBceOppOk.with_same_arena harb halb
                  (FullBveVarHelpers.FullBveEntryOkW.to_tryBceOpp hinv2 (hn_ok j hj))
              refine wp_loop_inv (ts := [i32])
                (fun (i, _) ml => ∃ sl, i.toNat ≤ np.toNat ∧
                  BveBceStepInv TmkInv c F0 F_cur s scr2 np nn R sl ml)
                (fun (i, _) _ => np.toNat - i.toNat)
                (fun Jlp hJlp => by
                  bve_jump
                  exact hJlp (0#32, PUnit.unit) m_bce ⟨sb, Nat.zero_le _, hinvb, htmkb,
                    by rw [hcvb, hs2_cv], hflb, hbuf_b, hpbce, hnbce, hmb⟩)
                (fun Jlp ⟨i, ⟨⟩⟩ ml
                    ⟨sl, hi_le, hinvl, htmkl, hcvl, hfll, hbuf_l, hpk, hnj, hml⟩ ihlp => by
                  rw [Blocks.get_here]; bve_jnz hi_lt
                  · have hi_nat : i.toNat < np.toNat := by
                      rw [BitVec.ult, decide_eq_true_eq] at hi_lt; exact hi_lt
                    have hscrl := hinvl.1.scratch_ok.scratch_buf_len
                    have hi_eq : (i.setWidth 64).toNat = i.toNat := by
                      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : i.toNat < 2 ^ 64)]
                    have hi_scr : (i.setWidth 64).toNat < sl.scratch.scratch_buf.length := by omega
                    have hwi_eq : sl.scratch.scratch_buf[i.toNat]'(by omega) =
                        scr2[i.toNat]?.getD 0#32 := by
                      have := hbuf_l i.toNat (by omega)
                      rw [List.getElem?_eq_getElem
                        (by omega : i.toNat < sl.scratch.scratch_buf.length)] at this
                      rw [← this]; rfl
                    refine wp_join_group (ts := [])
                      (fun _ mn => ∃ sn, BveBceStepInv TmkInv c F0 F_cur s scr2 np nn R sn mn) ?_ ?_
                    · rintro Jnxt _ mn ⟨sn, hstepn⟩; rw [Blocks.get_here]; bve_jump
                      have hi1 : (i + 1#32).toNat = i.toNat + 1 := by
                        rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
                          Nat.mod_eq_of_lt (by omega : i.toNat + 1 < 2 ^ 32)]
                      exact ihlp (i + 1#32, PUnit.unit) mn (by dsimp only; rw [hi1]; omega)
                        ⟨sn, by rw [hi1]; omega, hstepn⟩
                    · intro Jnxt hJnxt
                      bve_ld (c0_load_full_scratch_buf (i := i.setWidth 64) hi_scr hml)
                      bve_lets
                      refine wp_call_of_spec _ _ (hTryBce _ _ _ X ?_)
                      simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
                      refine ⟨c, F0, F_cur, sl, R, rfl, hinvl,
                        (by change pl.toNat < 2 * sl.core.cur_vars; rw [hpl_nat, hcvl]; omega),
                        (by simp only [hi_eq]; rw [hwi_eq]; exact hpk i.toNat hi_nat),
                        (by rw [h64_32]; omega),
                        (fun j hj => by rw [h64_32, hbuf_l (64 + j) (by omega)]; exact hnj j hj),
                        hml, ?_⟩
                      rintro blk lm' tmp' m_tb stb hinv_tb hm_tb
                      have htmk_tb : TmkInv stb := hTmk_cong htmkl rfl rfl
                      have htb_p := (full_bve_tryBce_pres (s := sl) (s' := stb) rfl rfl hpk hnj).1
                      have htb_n := (full_bve_tryBce_pres (s := sl) (s' := stb) rfl rfl hpk hnj).2
                      have htb_scr_idx : (i.setWidth 64).toNat < stb.scratch.scratch_buf.length :=
                        hi_scr
                      bve_jnz hblk
                      · refine wp_join_group (ts := [])
                          (fun _ mn => ∃ sn, BveBceStepInv TmkInv c F0 F_cur s scr2 np nn R sn mn)
                          ?_ ?_
                        · rintro J_try _ mn hmn; rw [Blocks.get_here]; bve_jump
                          exact hJnxt () mn hmn
                        · intro J_try hJ_try
                          bve_ld (c0_load_full_scratch_buf (i := i.setWidth 64) htb_scr_idx hm_tb)
                          bve_jnz hbin_flag
                          · refine wp_join_group (ts := [])
                              (fun _ mn =>
                                ∃ sn, BveBceStepInv TmkInv c F0 F_cur s scr2 np nn R sn mn) ?_ ?_
                            · rintro Jb _ mn hmn; rw [Blocks.get_here]; bve_jump
                              exact hJ_try () mn hmn
                            · intro Jb hJb
                              bve_ld (c0_load_full_scratch_buf (i := i.setWidth 64)
                                htb_scr_idx hm_tb)
                              bve_lets
                              refine wp_call_of_spec _ _ (hExtPush2 _ _ _ _ _ X ?_)
                              simp only [Arg.val_var]
                              refine ⟨c, stb, R, ⟨rfl, hinv_tb.2.2.2.2.1.2⟩, hinv_tb.1, htmk_tb,
                                hm_tb, ?_⟩
                              rintro ⟨okp, ⟨⟩⟩ se2 m_e2 hcore_e2 hlen_e2
                                ⟨hll_e2, hext_e2, hscr_e2⟩ htmk_e2 hm_e2
                              have heq_e2 : se2.core = stb.core :=
                                fullCoreState_agrees_with_scratch hcore_e2
                              have hinv_e2 : FullBveVarSpecs.FullDenseInvW c F0 F_cur se2 :=
                                denseInvW_of_extPush hinv_tb hlen_e2 hcore_e2 hll_e2 hext_e2
                              have he2_p := (full_bve_tryBce_pres (s := stb) (s' := se2)
                                (congrArg FullCoreState.arena heq_e2)
                                (congrArg FullCoreState.arena_len heq_e2) htb_p htb_n).1
                              have he2_n := (full_bve_tryBce_pres (s := stb) (s' := se2)
                                (congrArg FullCoreState.arena heq_e2)
                                (congrArg FullCoreState.arena_len heq_e2) htb_p htb_n).2
                              have hcv_e2 : se2.core.cur_vars = s.core.cur_vars :=
                                by rw [heq_e2]; exact hcvl
                              have hfl_e2 : se2.core.fuel.toNat ≤ s.core.fuel.toNat :=
                                by rw [heq_e2]; exact hfll
                              have hbuf_e2 : ∀ idx < 128, se2.scratch.scratch_buf[idx]? = scr2[idx]?
                                := fun idx hi => by rw [hscr_e2]; exact hbuf_l idx hi
                              bve_jnz hokp
                              · bve_ld (c0_load_full_scratch_buf (i := i.setWidth 64)
                                    (by rw [hinv_e2.1.scratch_ok.scratch_buf_len]; omega) hm_e2)
                                bve_lets
                                refine wp_call_of_spec _ _ (hDelBin _ _ _ X ?_)
                                simp only [vals_nil, vals_cons, Arg.val_var]
                                refine ⟨c, se2, R, rfl, hinv_e2.1, hinv_e2.2.1.watches.layout,
                                  hm_e2, ?_⟩
                                rintro wvec' wstk' wu' nb' m_db sdb hlen_db _ hwat_fn hm_db
                                have hinv_db := FullBveVarHelpers.FullDenseInvW.of_deleteBinary
                                  hinv_e2 hlen_db (hwat_fn F_cur hinv_e2.2.1.watches)
                                have hdb_p := (full_bve_tryBce_pres (s := se2) (s' := sdb)
                                  rfl rfl he2_p he2_n).1
                                have hdb_n := (full_bve_tryBce_pres (s := se2) (s' := sdb)
                                  rfl rfl he2_p he2_n).2
                                bve_ld load_full_bce_cnt hm_db
                                bve_st m_bce1, hm_bce1 := store_full_bce_cnt
                                  (sdb.scratch.bce_cnt + 1#64) hm_db
                                bve_jump
                                let sbce : FullState := { sdb with scratch :=
                                  { sdb.scratch with bce_cnt := sdb.scratch.bce_cnt + 1#64 } }
                                exact hJb () m_bce1 ⟨sbce,
                                  FullBveVarHelpers.FullDenseInvW.with_bce_cnt hinv_db _,
                                  hTmk_cong htmk_e2 rfl rfl, hcv_e2, hfl_e2, hbuf_e2,
                                  (full_bve_tryBce_pres (s := sdb) (s' := sbce)
                                    rfl rfl hdb_p hdb_n).1,
                                  (full_bve_tryBce_pres (s := sdb) (s' := sbce)
                                    rfl rfl hdb_p hdb_n).2, hm_bce1⟩
                              · bve_jump
                                exact hJb () m_e2 ⟨se2, hinv_e2, htmk_e2, hcv_e2, hfl_e2, hbuf_e2,
                                  he2_p, he2_n, hm_e2⟩
                          · refine wp_join_group (ts := [])
                              (fun _ mn =>
                                ∃ sn, BveBceStepInv TmkInv c F0 F_cur s scr2 np nn R sn mn) ?_ ?_
                            · rintro Jl _ mn hmn; rw [Blocks.get_here]; bve_jump
                              exact hJ_try () mn hmn
                            · intro Jl hJl
                              bve_ld (c0_load_full_scratch_buf (i := i.setWidth 64)
                                htb_scr_idx hm_tb)
                              bve_lets
                              refine wp_call_of_spec _ _ (hExtPushCl _ _ _ _ _ X ?_)
                              simp only [Arg.val_var]
                              refine ⟨c, stb, R, ⟨rfl, hinv_tb.2.2.2.2.1.2⟩, hinv_tb.1, htmk_tb,
                                hm_tb, ?_⟩
                              rintro ⟨okp, ⟨⟩⟩ se2 m_e2 hcore_e2 hlen_e2
                                ⟨hll_e2, hext_e2, hscr_e2⟩ htmk_e2 hm_e2
                              have heq_e2 : se2.core = stb.core :=
                                fullCoreState_agrees_with_scratch hcore_e2
                              have hinv_e2 : FullBveVarSpecs.FullDenseInvW c F0 F_cur se2 :=
                                denseInvW_of_extPush hinv_tb hlen_e2 hcore_e2 hll_e2 hext_e2
                              have he2_p := (full_bve_tryBce_pres (s := stb) (s' := se2)
                                (congrArg FullCoreState.arena heq_e2)
                                (congrArg FullCoreState.arena_len heq_e2) htb_p htb_n).1
                              have he2_n := (full_bve_tryBce_pres (s := stb) (s' := se2)
                                (congrArg FullCoreState.arena heq_e2)
                                (congrArg FullCoreState.arena_len heq_e2) htb_p htb_n).2
                              have hcv_e2 : se2.core.cur_vars = s.core.cur_vars := heq_e2 ▸ hcvl
                              have hfl_e2 : se2.core.fuel.toNat ≤ s.core.fuel.toNat :=
                                heq_e2 ▸ hfll
                              have hbuf_e2 : ∀ idx < 128, se2.scratch.scratch_buf[idx]? = scr2[idx]?
                                := fun idx hi => by rw [hscr_e2]; exact hbuf_l idx hi
                              bve_jnz hokp
                              · have hscr_e2_len := hinv_e2.1.scratch_ok.scratch_buf_len
                                have har_e2_len := hinv_e2.1.core_ok.arena_len_arr
                                have har_e2_le := hinv_e2.1.core_ok.arena_len_le
                                bve_ld load_full_arena_ptr hm_e2
                                bve_ld (c0_load_full_scratch_buf (i := i.setWidth 64)
                                    (by rw [hscr_e2_len]; omega) hm_e2)
                                let ccr := se2.scratch.scratch_buf[(i.setWidth 64).toNat]'(by
                                  rw [hscr_e2_len]; omega)
                                have hccr_eq : ccr = scr2[i.toNat]?.getD 0#32 := by
                                  have hli : (i.setWidth 64).toNat < se2.scratch.scratch_buf.length
                                    := by rw [hscr_e2_len]; omega
                                  have h0 : se2.scratch.scratch_buf[i.toNat]? = some ccr := by
                                    rw [← hi_eq, List.getElem?_eq_getElem hli]
                                  rw [← h0.symm.trans (hbuf_e2 i.toNat (by omega))]; rfl
                                have hnb_ccr : (ccr &&& 0x80000000#32) = 0#32 := by
                                  have h0 : (stb.scratch.scratch_buf[(i.setWidth 64).toNat]'
                                      htb_scr_idx &&& 0x80000000#32) = 0#32 :=
                                    bne_eq_false_iff_eq.mp hbin_flag
                                  simpa only [ccr, hscr_e2] using h0
                                have hbce_ccr := he2_p i.toNat hi_nat
                                rw [← hccr_eq] at hbce_ccr
                                unfold FullBveVarSpecs.FullBveTryBceEntryOk at hbce_ccr
                                simp only [hnb_ccr, ne_eq, not_true_eq_false, ↓reduceIte]
                                  at hbce_ccr
                                have hccr_nat : (ccr.setWidth 64).toNat = ccr.toNat := by
                                  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt
                                    (by have := ccr.isLt; omega : ccr.toNat < 2 ^ 64)]
                                have hccr_ar : (ccr.setWidth 64).toNat < se2.core.arena.length := by
                                  rw [hccr_nat]; omega
                                have hccr_sz : 3 ≤ fullArenaClauseSize se2 ccr.toNat :=
                                  (hinv_e2.2.1.arena.refs_wf ccr.toNat hbce_ccr.1).2.1
                                have hccr_p2 : ((ccr.setWidth 64) + 2#64).toNat <
                                    se2.core.arena.length := by
                                  rw [BitVec.toNat_add, show (2#64 : BitVec 64).toNat = 2 from rfl,
                                    hccr_nat, Nat.mod_eq_of_lt (by omega : ccr.toNat + 2 < 2 ^ 64)]
                                  unfold fullArenaClauseSize fullArenaClauseSizeCore at hbce_ccr
                                  omega
                                have hhdr_eq : se2.core.arena[(ccr.setWidth 64).toNat]'hccr_ar =
                                    fullArenaHdr se2 ccr.toNat := by
                                  unfold fullArenaHdr fullArenaHdrCore
                                  rw [← hccr_nat, List.getElem?_eq_getElem hccr_ar,
                                    Option.getD_some]
                                have har_eq :
                                    se2.core.arena.set (ccr.setWidth 64).toNat
                                      (se2.core.arena[(ccr.setWidth 64).toNat]'hccr_ar |||
                                        0x00080000#32) =
                                    se2.core.arena.set ccr.toNat
                                      (fullArenaHdr se2 ccr.toNat ||| 0x00080000#32) := by
                                  rw [hhdr_eq, hccr_nat]
                                bve_ld (c0_load_full_arena (i := ccr.setWidth 64) hccr_ar hm_e2)
                                bve_st m_ar, hm_ar := c0_store_full_arena (i := ccr.setWidth 64)
                                  (se2.core.arena[(ccr.setWidth 64).toNat]'hccr_ar |||
                                    0x00080000#32) hccr_ar hm_e2
                                bve_ld load_full_arena_garbage hm_ar
                                bve_ld (c0_load_full_arena (i := ccr.setWidth 64 + 2#64)
                                  (by rw [List.length_set]; exact hccr_p2) hm_ar)
                                bve_st m_ag, hm_ag := store_full_arena_garbage _ hm_ar
                                bve_ld load_full_bce_cnt hm_ag
                                bve_st m_bce1, hm_bce1 := store_full_bce_cnt _ hm_ag
                                bve_jump
                                simp only [har_eq] at hm_bce1
                                let ar_mg := se2.core.arena.set ccr.toNat
                                  (fullArenaHdr se2 ccr.toNat ||| 0x00080000#32)
                                let ag_mg := se2.core.arena_garbage + 3#64 +
                                  (ar_mg[((ccr.setWidth 64) + 2#64).toNat]'(by
                                    rw [List.length_set]; exact hccr_p2)).setWidth 64
                                let smg : FullState :=
                                  { se2 with
                                    core := { se2.core with arena := ar_mg, arena_garbage := ag_mg }
                                    scratch := { se2.scratch with
                                      bce_cnt := se2.scratch.bce_cnt + 1#64 } }
                                have hinv_mg := FullBveVarHelpers.FullDenseInvW.with_bce_cnt
                                  (FullBveVarHelpers.FullDenseInvW.of_markGarb_zero hinv_e2
                                    hbce_ccr.1 ag_mg) (se2.scratch.bce_cnt + 1#64)
                                have htbe := full_bve_tryBce_of_markGarb hinv_e2.1
                                  hinv_e2.2.1 hbce_ccr.1 ag_mg he2_p he2_n
                                exact hJl () m_bce1 ⟨smg, hinv_mg, hTmk_cong htmk_e2 rfl rfl,
                                  hcv_e2, hfl_e2, hbuf_e2,
                                  (full_bve_tryBce_pres (s' := smg) rfl rfl htbe.1 htbe.2).1,
                                  (full_bve_tryBce_pres (s' := smg) rfl rfl htbe.1 htbe.2).2,
                                  hm_bce1⟩
                              · bve_jump
                                exact hJl () m_e2 ⟨se2, hinv_e2, htmk_e2, hcv_e2, hfl_e2, hbuf_e2,
                                  he2_p, he2_n, hm_e2⟩
                      · bve_jump
                        exact hJnxt () m_tb ⟨stb, hinv_tb, htmk_tb, hcvl, hfll, hbuf_l,
                          htb_p, htb_n, hm_tb⟩
                  · bve_ret
                    exact hQ 1#64 sl ml hinvl.toDense htmkl (by rw [← hcvl]; exact Nat.le_refl _)
                      hfll (Or.inl rfl) (fun h => by cases h) hml)
            · intro J_bce hJ_bce
              bve_jnz hfit_c
              · bve_ld load_full_arena_len hmf
                bve_ld load_full_arena_cap hmf
                bve_jnz har_fit
                · refine wp_join_group (ts := []) (fun _ m_o =>
                      ∃ so, FullBveVarSpecs.FullDenseInvW c F0 F_cur so ∧ TmkInv so ∧
                        so.core.cur_vars = s.core.cur_vars ∧
                        so.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c so ⋆ R) m_o) ?_ ?_
                  · rintro J_oom2 _ m_o ⟨so, hinvo, htmko, hcvo, hflo, hmo⟩
                    rw [Blocks.get_here]
                    bve_st m_o1, hm_o1 := store_full_oom 1#64 hmo
                    bve_ret
                    let so1 : FullState := { so with core := { so.core with oom := 1#64 } }
                    exact hQ 2#64 so1 m_o1
                      (FullBveVarHelpers.FullDenseInvW.with_oom hinvo 1#64).toDense
                      (hTmk_cong htmko rfl rfl) (by rw [← hcvo]; exact Nat.le_refl _) hflo
                      (Or.inr (Or.inl rfl)) (fun h => by cases h) hm_o1
                  · intro J_oom2 hJ_oom2
                    refine wp_call_of_spec _ _ (hWeaken _ _ _ _ _ _ X ?_)
                    simp only [Arg.val_var, Arg.val_imm]
                    refine ⟨c, F0, F_cur, sf, R, rfl, hinvf, htmkf,
                      (by change pl.toNat < 2 * sf.core.cur_vars
                          rw [hpl_nat, hcvf, hs2_cv]; omega),
                      (by rw [h0_32]; omega),
                      (fun i hi => by
                        rw [h0_32, Nat.zero_add, hbuf_f i (by omega)]
                        exact fullBveWeakItemOk_of_pres (by rw [hcvf, hs2_cv])
                          (by unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [harf, half])
                          (FullBveVarHelpers.FullBveEntryOkW.to_weak (hp_ok i hi))), hmf, ?_⟩
                    intro ok1 sf1 m_w1 hinvf1 htmk1' hcv1 hfl1 hscr1 hrefs1 hm_w1
                    bve_jnz hok1
                    · refine wp_call_of_spec _ _ (hWeaken _ _ _ _ _ _ X ?_)
                      simp only [Arg.val_var, Arg.val_imm]
                      refine ⟨c, F0, F_cur, sf1, R, rfl, hinvf1, htmk1',
                        (by change (pl ||| 1#32).toNat < 2 * sf1.core.cur_vars
                            rw [hnl_nat, hcv1, hcvf, hs2_cv]; omega),
                        (by rw [h64_32]; omega),
                        (fun j hj => by
                          rw [h64_32, hscr1, hbuf_f (64 + j) (by omega)]
                          exact fullBveWeakItemOk_of_pres (by rw [hcv1, hcvf, hs2_cv])
                            (hrefs1.trans (by
                              unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [harf, half]))
                            (FullBveVarHelpers.FullBveEntryOkW.to_weak (hn_ok j hj))), hm_w1, ?_⟩
                      intro ok2 sf2 m_w2 hinvf2 htmk2' hcv2 hfl2 hscr2 _hrefs2 hm_w2
                      bve_jnz hok2
                      · refine wp_call_of_spec _ _ (hSetInact _ _ _ X ?_)
                        simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
                        refine ⟨c, sf2, R, rfl, hinvf2.1, hm_w2, ?_⟩
                        intro flags' unass' m_si hfl_len hm_si
                        let sf3 : FullState := { sf2 with core :=
                          { sf2.core with flags := flags', unassigned := unass' } }
                        have hinvf3 := FullBveVarHelpers.FullDenseInvW.with_flags_unassigned
                          hinvf2 hfl_len unass'
                        bve_ld load_full_bve_cnt hm_si
                        bve_st m_bve, hm_bve := store_full_bve_cnt
                          (sf3.scratch.bve_cnt + 1#64) hm_si
                        bve_lets
                        let sf4 : FullState := { sf3 with scratch :=
                          { sf3.scratch with bve_cnt := sf3.scratch.bve_cnt + 1#64 } }
                        have hinvf4 := FullBveVarHelpers.FullDenseInvW.with_bve_cnt hinvf3
                          (sf3.scratch.bve_cnt + 1#64)
                        obtain ⟨hrp160, hrp_cap, hres_fit⟩ := hres_f hfit_c
                        have hres4 : FullBveVarSpecs.FullResBufOkW F_cur sf4 rp_f.toNat 160 :=
                          FullBveVarHelpers.FullResBufOkW.with_state
                            (by dsimp only [sf4, sf3]; exact hcv2.trans hcv1)
                            (fun _ _ => by dsimp only [sf4, sf3]; rw [hscr2, hscr1]) hres_fit
                        refine wp_call_of_spec _ _ (hCommitRes _ _ _ _ _ X ?_)
                        simp only [Arg.val_var, Arg.val_imm]
                        refine ⟨c, F0, F_cur, sf4, R, rfl, hinvf4, hTmk_cong htmk2' rfl rfl,
                          (by rw [show (160 : BitVec 64).toNat = 160 from rfl]; exact hrp160),
                          hrp_cap,
                          (by rw [show (160 : BitVec 64).toNat = 160 from rfl]; exact hres4),
                          hm_bve, ?_⟩
                        intro r_cr sf_end m_end hinv_cr htmk_cr hcv_cr hfl_cr hrc_cr h20_cr hm_end
                        exact hQ r_cr sf_end m_end hinv_cr.toDense htmk_cr
                          (by rw [hcv_cr]; dsimp only [sf4, sf3]
                              rw [hcv2, hcv1, hcvf, hs2_cv]; exact Nat.le_refl _)
                          (by rw [hfl_cr]; dsimp only [sf4, sf3]; rw [hfl2, hfl1]; exact hflf)
                          hrc_cr h20_cr hm_end
                      · bve_jump; exact hJ_oom2 () m_w2 ⟨sf2, hinvf2, htmk2',
                          by rw [hcv2, hcv1, hcvf, hs2_cv], by rw [hfl2, hfl1]; exact hflf, hm_w2⟩
                    · bve_jump; exact hJ_oom2 () m_w1 ⟨sf1, hinvf1, htmk1',
                        by rw [hcv1, hcvf, hs2_cv], by rw [hfl1]; exact hflf, hm_w1⟩
                · bve_jump; exact hJ_bce () ml ⟨sf, hinvf, htmkf, hcvf, hflf, harf, half,
                    hbuf_f, hmf⟩
              · bve_jump; exact hJ_bce () ml ⟨sf, hinvf, htmkf, hcvf, hflf, harf, half,
                  hbuf_f, hmf⟩
          · intro J_fit hJ_fit
            bve_jnz hfit0
            · have hsc132 : 132 ≤ c.scratch_cap := by omega
              refine wp_call_of_spec _ _ (hGates _ _ _ _ _ _ X ?_)
              simp only [Arg.val_var]
              refine ⟨c, F0, F_cur, s2, R, rfl, hinv2, hsc132, htmk2, hv_lt, hnp_le, hnn_le,
                hp_ok, hn_ok, hm2, ?_⟩
              rintro s3 m3 hinv3 htmk3 hcv3 har3 hal3 hfl3 hkeep3 hm3
              have hsc3_len := hinv3.1.scratch_ok.scratch_buf_len
              bve_ld (load_full_scratch_buf (i := 128) (by omega) hm3)
              bve_ld (load_full_scratch_buf (i := 129) (by omega) hm3)
              bve_ld (load_full_scratch_buf (i := 130) (by omega) hm3)
              bve_ld (load_full_scratch_buf (i := 131) (by omega) hm3)
              bve_lets
              -- `bool gate_found = (pmask != 0ULL || nmask != 0ULL);`
              refine wp_join_group (ts := [.bool]) (fun (_gf, ()) mgf => mgf = m3) ?_ ?_
              · rintro J_gf ⟨gf, ⟨⟩⟩ mgf h_mgf; subst mgf; rw [Blocks.get_here]; bve_lets
                refine wp_loop_inv (ts := [i64, i64, .bool, i32])
                  (fun (rc, rp, fit_i, i, _) ml =>
                    ∃ sf, FullBveVarSpecs.FullDenseInvW c F0 F_cur sf ∧ TmkInv sf ∧
                      sf.core.cur_vars = s2.core.cur_vars ∧ sf.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                      sf.core.arena = s2.core.arena ∧ sf.core.arena_len = s2.core.arena_len ∧
                      (∀ idx < 128, sf.scratch.scratch_buf[idx]? = scr2[idx]?) ∧
                      i.toNat ≤ np.toNat ∧
                      (fit_i = true → 160 ≤ rp.toNat ∧ rp.toNat ≤ c.scratch_cap ∧
                        FullBveVarSpecs.FullResBufOkW F_cur sf rp.toNat 160) ∧
                      (FullMem c sf ⋆ R) ml)
                  (fun (_, _, fit_i, i, _) _ => if fit_i then np.toNat - i.toNat + 1 else 0)
                  (fun Jlp hJlp => by
                    bve_jump
                    exact hJlp (0#64, 160#64,
                        (BitVec.ofNat 64 s1.scratch.extend_len + (en1 + en2)).ule
                          (BitVec.ofNat 64 c.extend_cap), 0#32, ()) m3
                      ⟨s3, hinv3, htmk3, hcv3, hfl3, har3, hal3, hkeep3, Nat.zero_le _,
                        fun _ => ⟨by rw [show (160#64 : BitVec 64).toNat = 160 from rfl]; omega,
                          by rw [show (160#64 : BitVec 64).toNat = 160 from rfl]; omega,
                          by rw [show (160#64 : BitVec 64).toNat = 160 from rfl]; exact .nil⟩,
                        hm3⟩)
                  (fun Jlp ⟨rc, rp, fit_i, i, ⟨⟩⟩ ml
                      ⟨sf, hinvf, htmkf, hcvf, hflf, harf, half, hbuf_f, hi_le, hres_f, hml⟩
                      ihlp => by
                    rw [Blocks.get_here]; bve_jnz hi_lt
                    · bve_jnz hfit_i
                      · have hi_nat : i.toNat < np.toNat := by
                          rw [BitVec.ult, decide_eq_true_eq] at hi_lt; exact hi_lt
                        have hhi1 : (i + 1#32).toNat = i.toNat + 1 := by
                          rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
                            Nat.mod_eq_of_lt (by omega : i.toNat + 1 < 2 ^ 32)]
                        refine wp_join_group (ts := [i64, i64, .bool, i32])
                            (fun (rc_n, rp_n, fit_n, _, _) mn =>
                            ∃ sn, FullBveVarSpecs.FullDenseInvW c F0 F_cur sn ∧ TmkInv sn ∧
                              sn.core.cur_vars = s2.core.cur_vars ∧
                              sn.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                              sn.core.arena = s2.core.arena ∧
                              sn.core.arena_len = s2.core.arena_len ∧
                              (∀ idx < 128, sn.scratch.scratch_buf[idx]? = scr2[idx]?) ∧
                              (fit_n = true → 160 ≤ rp_n.toNat ∧ rp_n.toNat ≤ c.scratch_cap ∧
                                FullBveVarSpecs.FullResBufOkW F_cur sn rp_n.toNat 160) ∧
                              (FullMem c sn ⋆ R) mn) ?_ ?_
                        · rintro Js ⟨rc_n, rp_n, fit_n, _j_n, ⟨⟩⟩ mn
                            ⟨sn, hinvn, htmkn, hcvn, hfln, harn, haln, hbuf_n, hres_n, hmn⟩
                          rw [Blocks.get_here]; bve_jump
                          exact ihlp (rc_n, rp_n, fit_n, i + 1#32, ()) mn (by
                            dsimp only; cases fit_n <;> cases hfit_i <;> simp [hhi1]; omega)
                            ⟨sn, hinvn, htmkn, hcvn, hfln, harn, haln, hbuf_n, by rw [hhi1]; omega,
                              hres_n, hmn⟩
                        · intro Js hJs
                          obtain ⟨hrp_160, hrp_cap, hres_fit⟩ := hres_f hfit_i
                          refine wp_loop_inv (ts := [i64, i64, i32])
                            (fun (rc_j, rp_j, j, _) mj =>
                              ∃ sj, FullBveVarSpecs.FullDenseInvW c F0 F_cur sj ∧ TmkInv sj ∧
                                sj.core.cur_vars = s2.core.cur_vars ∧
                                sj.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                                sj.core.arena = s2.core.arena ∧
                                sj.core.arena_len = s2.core.arena_len ∧
                                (∀ idx < 128, sj.scratch.scratch_buf[idx]? = scr2[idx]?) ∧
                                j.toNat ≤ nn.toNat ∧ 160 ≤ rp_j.toNat ∧ rp_j.toNat ≤ c.scratch_cap ∧
                                FullBveVarSpecs.FullResBufOkW F_cur sj rp_j.toNat 160 ∧
                                (FullMem c sj ⋆ R) mj)
                            (fun (_, _, j, _) _ => nn.toNat - j.toNat)
                            (fun Js1 hJs1 => by
                              bve_jump
                              exact hJs1 (rc, rp, 0#32, ()) ml
                                ⟨sf, hinvf, htmkf, hcvf, hflf, harf, half, hbuf_f, Nat.zero_le _,
                                  hrp_160, hrp_cap, hres_fit, hml⟩)
                            (fun Js1 ⟨rc_j, rp_j, j, ⟨⟩⟩ mj
                                ⟨sj, hinvj, htmkj, hcvj, hflj, harj, halj, hbuf_j, hj_le, hrpj_160,
                                  hrpj_cap, hres_j, hmj⟩ ihj => by
                              rw [Blocks.get_here]; bve_jnz hj_lt
                              · bve_jnz hfit_j
                                · have hj_nat : j.toNat < nn.toNat := by
                                    rw [BitVec.ult, decide_eq_true_eq] at hj_lt; exact hj_lt
                                  have hhj1 : (j + 1#32).toNat = j.toNat + 1 := by
                                    rw [BitVec.toNat_add,
                                      show (1#32 : BitVec 32).toNat = 1 from rfl,
                                      Nat.mod_eq_of_lt (by omega : j.toNat + 1 < 2 ^ 32)]
                                  -- `need_pair = !gate_found || ((((pmask>>i)|(nmask>>j))&1)!=0)`
                                  refine wp_join_group (ts := [.bool])
                                    (fun (_need, ()) mnp => mnp = mj) ?_ ?_
                                  · rintro J_np ⟨need_p, ⟨⟩⟩ mnp h_mnp; subst mnp
                                    rw [Blocks.get_here]
                                    refine wp_join_group (ts := [i64, i64, .bool])
                                      (fun (rc_n, rp_n, _fit_n, _) mn =>
                                        ∃ sn, FullBveVarSpecs.FullDenseInvW c F0 F_cur sn ∧
                                          TmkInv sn ∧ sn.core.cur_vars = s2.core.cur_vars ∧
                                          sn.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                                          sn.core.arena = s2.core.arena ∧
                                          sn.core.arena_len = s2.core.arena_len ∧
                                          (∀ idx < 128, sn.scratch.scratch_buf[idx]? = scr2[idx]?) ∧
                                          160 ≤ rp_n.toNat ∧ rp_n.toNat ≤ c.scratch_cap ∧
                                          FullBveVarSpecs.FullResBufOkW F_cur sn rp_n.toNat 160 ∧
                                          (FullMem c sn ⋆ R) mn) ?_ ?_
                                    · rintro Js2 ⟨rc_n, rp_n, _fit_n, ⟨⟩⟩ mn
                                        ⟨sn, hinvn, htmkn, hcvn, hfln, harn, haln, hbuf_n, hrpn_160,
                                          hrpn_cap, hres_n, hmn⟩
                                      rw [Blocks.get_here]; bve_jump
                                      exact ihj (rc_n, rp_n, j + 1#32, ()) mn
                                        (by dsimp only; rw [hhj1]; omega)
                                        ⟨sn, hinvn, htmkn, hcvn, hfln, harn, haln, hbuf_n,
                                          by rw [hhj1]; omega, hrpn_160, hrpn_cap, hres_n, hmn⟩
                                    · intro Js2 hJs2
                                      bve_jnz hneed
                                      · have hsj_len := hinvj.1.scratch_ok.scratch_buf_len
                                        have hi_eq : (i.setWidth 64).toNat = i.toNat := by
                                          rw [BitVec.toNat_setWidth,
                                            Nat.mod_eq_of_lt (by omega : i.toNat < 2 ^ 64)]
                                        have hi_sj : (i.setWidth 64).toNat <
                                            sj.scratch.scratch_buf.length := by omega
                                        have hj64_eq : ((64#32 + j).setWidth 64).toNat =
                                            64 + j.toNat := by
                                          rw [BitVec.toNat_setWidth, BitVec.toNat_add,
                                            show (64#32 : BitVec 32).toNat = 64 from rfl,
                                            Nat.mod_eq_of_lt (by omega : 64 + j.toNat < 2 ^ 32),
                                            Nat.mod_eq_of_lt (by omega : 64 + j.toNat < 2 ^ 64)]
                                        have hj64_sj : ((64#32 + j).setWidth 64).toNat <
                                            sj.scratch.scratch_buf.length := by omega
                                        bve_ld (c0_load_full_scratch_buf (i := i.setWidth 64)
                                          hi_sj hmj)
                                        bve_ld (c0_load_full_scratch_buf
                                          (i := (64#32 + j).setWidth 64) hj64_sj hmj)
                                        bve_lets
                                        have hwi_j :
                                            sj.scratch.scratch_buf[(i.setWidth 64).toNat]'hi_sj =
                                              scr2[i.toNat]?.getD 0#32 := by
                                          have h0 : sj.scratch.scratch_buf[i.toNat]? =
                                              some (sj.scratch.scratch_buf[(i.setWidth 64).toNat]'
                                                hi_sj) := by
                                            rw [← hi_eq, List.getElem?_eq_getElem hi_sj]
                                          rw [← h0.symm.trans (hbuf_j i.toNat (by omega))]; rfl
                                        have hwj_j :
                                            sj.scratch.scratch_buf[((64#32 + j).setWidth 64).toNat]'
                                                hj64_sj =
                                              scr2[64 + j.toNat]?.getD 0#32 := by
                                          have h0 : sj.scratch.scratch_buf[64 + j.toNat]? =
                                              some (sj.scratch.scratch_buf[((64#32 + j).setWidth
                                                64).toNat]'hj64_sj) := by
                                            rw [← hj64_eq, List.getElem?_eq_getElem hj64_sj]
                                          rw [← h0.symm.trans (hbuf_j (64 + j.toNat) (by omega))]
                                          rfl
                                        refine wp_call_of_spec _ _ (hResolve _ _ _ X ?_)
                                        simp only [vals_nil, vals_cons, Arg.val_var]
                                        refine ⟨c, F0, F_cur, sj, R, rfl, hinvj,
                                          (by rw [hcvj, hs2_cv]; exact hv_lt),
                                          (by rw [hwi_j]
                                              exact FullBveVarHelpers.FullBveEntryOkW.with_state
                                                (by rw [hcvj]; exact Nat.le_refl _) harj halj
                                                (hp_ok i.toNat hi_nat)),
                                          (by rw [hwj_j]
                                              exact FullBveVarHelpers.FullBveEntryOkW.with_state
                                                (by rw [hcvj]; exact Nat.le_refl _) harj halj
                                                (hn_ok j.toNat hj_nat)), hmj, ?_⟩
                                        rintro ok_r lm' tmp' tl' m_r sr hinv_r htl_r hok_rt hm_r
                                        have htmk_r : TmkInv sr := hTmk_cong htmkj rfl rfl
                                        bve_jnz hok_r
                                        · obtain ⟨htl_lits, htl_nd, htl_ent⟩ := hok_rt hok_r
                                          bve_jnz hrc_ov
                                          · bve_jump
                                            exact hJs (rc_j + 1#64, rp_j, false, j, ()) m_r
                                              ⟨sr, hinv_r, htmk_r, hcvj, hflj, harj, halj, hbuf_j,
                                                (fun h => by cases h), hm_r⟩
                                          · bve_ld load_full_tmp_len hm_r
                                            bve_ld load_full_scratch_cap hm_r
                                            bve_jnz hrp_ov
                                            · bve_jump
                                              exact hJs (rc_j + 1#64, rp_j, false, j, ()) m_r
                                                ⟨sr, hinv_r, htmk_r, hcvj, hflj, harj, halj, hbuf_j,
                                                  (fun h => by cases h), hm_r⟩
                                            · have htl_lt64 : tl' < 2 ^ 64 := by omega
                                              have htl_lt32 : tl' < 2 ^ 32 := by omega
                                              have hrp_sum_nat :
                                                  (rp_j + 1#64 + BitVec.ofNat 64 tl').toNat =
                                                    rp_j.toNat + 1 + tl' := by
                                                rw [BitVec.toNat_add, BitVec.toNat_add,
                                                  show (1#64 : BitVec 64).toNat = 1 from rfl,
                                                  BitVec.toNat_ofNat, Nat.mod_eq_of_lt htl_lt64,
                                                  Nat.mod_eq_of_lt
                                                    (by omega : rp_j.toNat + 1 < 2 ^ 64),
                                                  Nat.mod_eq_of_lt
                                                    (by omega : rp_j.toNat + 1 + tl' < 2 ^ 64)]
                                              have hrp_fit :
                                                  rp_j.toNat + 1 + tl' ≤ c.scratch_cap := by
                                                change (BitVec.ofNat 64 c.scratch_cap).ult
                                                    (rp_j + 1#64 + BitVec.ofNat 64 tl') =
                                                  false at hrp_ov
                                                rw [BitVec.ult, decide_eq_false_iff_not,
                                                  BitVec.toNat_ofNat,
                                                  Nat.mod_eq_of_lt
                                                    (by omega : c.scratch_cap < 2 ^ 64),
                                                  hrp_sum_nat] at hrp_ov
                                                omega
                                              have hrp_lt_scr :
                                                  rp_j.toNat < sr.scratch.scratch_buf.length := by
                                                rw [hinv_r.1.scratch_ok.scratch_buf_len]; omega
                                              bve_ld load_full_tmp_len hm_r
                                              bve_st m_len, hm_len :=
                                                c0_store_full_scratch_buf (i := rp_j)
                                                  ((BitVec.ofNat 64 tl').setWidth 32)
                                                  hrp_lt_scr hm_r
                                              let sk0 : FullState := { sr with scratch :=
                                                { sr.scratch with scratch_buf :=
                                                    (sr.scratch.scratch_buf.set rp_j.toNat
                                                      ((BitVec.ofNat 64 tl').setWidth 32)) } }
                                              have hinv_k0 :
                                                  FullBveVarSpecs.FullDenseInvW c F0 F_cur sk0 :=
                                                FullBveVarHelpers.FullDenseInvW.with_scratch_buf
                                                  hinv_r (by
                                                    rw [List.length_set]
                                                    exact hinv_r.1.scratch_ok.scratch_buf_len)
                                              bve_ld load_full_tmp_lits_ptr hm_len
                                              refine wp_loop_inv (ts := [i32])
                                                (fun (k, _) mk =>
                                                  ∃ sk : FullState,
                                                    FullBveVarSpecs.FullDenseInvW c F0 F_cur sk ∧
                                                    TmkInv sk ∧ sk.core = sr.core ∧ k.toNat ≤ tl' ∧
                                                    (∀ idx < 128,
                                                      sk.scratch.scratch_buf[idx]? = scr2[idx]?) ∧
                                                    (∀ idx < rp_j.toNat,
                                                      sk.scratch.scratch_buf[idx]? =
                                                        sj.scratch.scratch_buf[idx]?) ∧
                                                    (sk.scratch.scratch_buf[rp_j.toNat]?.getD
                                                      0#32).toNat = tl' ∧
                                                    (∀ t < k.toNat,
                                                      sk.scratch.scratch_buf[rp_j.toNat + 1 + t]? =
                                                        tmp'[t]?) ∧ (FullMem c sk ⋆ R) mk)
                                                (fun (k, _) _ => tl' - k.toNat)
                                                (fun Jk hJk => by
                                                  bve_jump
                                                  exact hJk (0#32, PUnit.unit) m_len
                                                    ⟨sk0, hinv_k0, hTmk_cong htmk_r rfl rfl, rfl,
                                                      Nat.zero_le _,
                                                      (fun idx hi => by
                                                        dsimp only [sk0]
                                                        rw [List.getElem?_set_ne (by omega)]
                                                        exact hbuf_j idx hi),
                                                      (fun idx hi => by
                                                        dsimp only [sk0]
                                                        rw [List.getElem?_set_ne (by omega)]),
                                                      (by dsimp only [sk0]
                                                          rw [List.getElem?_set_self hrp_lt_scr,
                                                            Option.getD_some, BitVec.toNat_setWidth,
                                                            BitVec.toNat_ofNat,
                                                            Nat.mod_eq_of_lt htl_lt64,
                                                            Nat.mod_eq_of_lt htl_lt32]),
                                                      (fun _ ht => absurd ht (Nat.not_lt_zero _)),
                                                      hm_len⟩)
                                                (fun Jk ⟨k, ⟨⟩⟩ mk
                                                    ⟨sk, hinv_k, htmk_k, hcore_k, hk_le, hbuf_k128,
                                                      hbuf_krp, hsz_k, hcp_k, hmk⟩ ihk => by
                                                  rw [Blocks.get_here]
                                                  bve_ld load_full_tmp_len hmk
                                                  bve_jnz hk_lt
                                                  · have hk_eq :
                                                        (k.setWidth 64).toNat = k.toNat := by
                                                      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt
                                                        (by have := k.isLt; omega)]
                                                    have hk_nat : k.toNat < tl' := by
                                                      have h0 : BitVec.ult (k.setWidth 64)
                                                          (BitVec.ofNat 64 sk.core.tmp_len) =
                                                          true := hk_lt
                                                      rw [hcore_k] at h0
                                                      rw [BitVec.ult, decide_eq_true_eq, hk_eq,
                                                        BitVec.toNat_ofNat,
                                                        Nat.mod_eq_of_lt htl_lt64] at h0
                                                      exact h0
                                                    have hk_tmp : (k.setWidth 64).toNat <
                                                        sk.core.tmp.length := by
                                                      rw [hk_eq, hinv_k.1.core_ok.tmp_len_arr]
                                                      exact Nat.lt_of_lt_of_le hk_nat
                                                        (Nat.le_trans htl_r
                                                          (by rw [hcvj]; exact hcv_le))
                                                    have hk_scr_nat :
                                                        (rp_j + 1#64 + k.setWidth 64).toNat =
                                                          rp_j.toNat + 1 + k.toNat := by
                                                      rw [BitVec.toNat_add, BitVec.toNat_add,
                                                        show (1#64 : BitVec 64).toNat = 1 from rfl,
                                                        hk_eq,
                                                        Nat.mod_eq_of_lt
                                                          (by omega : rp_j.toNat + 1 < 2 ^ 64),
                                                        Nat.mod_eq_of_lt
                                                          (by omega :
                                                            rp_j.toNat + 1 + k.toNat < 2 ^ 64)]
                                                    have hk_scr :
                                                        (rp_j + 1#64 + k.setWidth 64).toNat <
                                                          sk.scratch.scratch_buf.length := by
                                                      rw [hk_scr_nat,
                                                        hinv_k.1.scratch_ok.scratch_buf_len]
                                                      omega
                                                    bve_ld (c0_load_full_tmp (i := k.setWidth 64)
                                                      hk_tmp hmk)
                                                    bve_st m_k1, hm_k1 :=
                                                      c0_store_full_scratch_buf
                                                        (i := rp_j + 1#64 + k.setWidth 64)
                                                        (sk.core.tmp[(k.setWidth 64).toNat]'hk_tmp)
                                                        hk_scr hmk
                                                    bve_jump
                                                    let sk1 : FullState := { sk with scratch :=
                                                      { sk.scratch with scratch_buf :=
                                                          (sk.scratch.scratch_buf.set
                                                            (rp_j + 1#64 + k.setWidth 64).toNat
                                                            (sk.core.tmp[(k.setWidth 64).toNat]'
                                                              hk_tmp)) } }
                                                    have hinv_k1 :
                                                        FullBveVarSpecs.FullDenseInvW c F0 F_cur
                                                          sk1 :=
                                                      FullDenseInvW.with_scratch_buf (s := sk)
                                                        hinv_k (by
                                                          have hlen_s :=
                                                            hinv_k.1.scratch_ok.scratch_buf_len
                                                          rw [List.length_set]; exact hlen_s)
                                                    have hk1 : (k + 1#32).toNat = k.toNat + 1 := by
                                                      rw [BitVec.toNat_add,
                                                        show (1#32 : BitVec 32).toNat = 1 from rfl,
                                                        Nat.mod_eq_of_lt
                                                          (by omega : k.toNat + 1 < 2 ^ 32)]
                                                    have hval_k :
                                                        some (sk.core.tmp[(k.setWidth 64).toNat]'
                                                          hk_tmp) = tmp'[k.toNat]? := by
                                                      have htmpeq : sk.core.tmp = tmp' := by
                                                        rw [hcore_k]
                                                      exact Eq.symm (by
                                                        rw [← htmpeq, ← hk_eq,
                                                          List.getElem?_eq_getElem hk_tmp])
                                                    exact ihk (k + 1#32, PUnit.unit) m_k1
                                                      (by dsimp only; rw [hk1]; omega)
                                                      ⟨sk1, hinv_k1, hTmk_cong htmk_k rfl rfl,
                                                        hcore_k, by rw [hk1]; omega,
                                                        (fun idx hi => by
                                                          dsimp only [sk1]
                                                          rw [List.getElem?_set_ne
                                                            (by rw [hk_scr_nat]; omega)]
                                                          exact hbuf_k128 idx hi),
                                                        (fun idx hi => by
                                                          dsimp only [sk1]
                                                          rw [List.getElem?_set_ne
                                                            (by rw [hk_scr_nat]; omega)]
                                                          exact hbuf_krp idx hi),
                                                        (by dsimp only [sk1]
                                                            rw [List.getElem?_set_ne
                                                              (by rw [hk_scr_nat]; omega)]
                                                            exact hsz_k),
                                                        (fun t ht => by
                                                          rw [hk1] at ht; dsimp only [sk1]
                                                          rcases Nat.lt_or_eq_of_le
                                                              (Nat.lt_succ_iff.mp ht) with hlt | rfl
                                                          · rw [List.getElem?_set_ne
                                                              (by rw [hk_scr_nat]; omega)]
                                                            exact hcp_k t hlt
                                                          · rw [hk_scr_nat,
                                                              List.getElem?_set_self (by
                                                                rw [← hk_scr_nat]; exact hk_scr)]
                                                            exact hval_k), hm_k1⟩
                                                  · have hk_eq_tl : k.toNat = tl' := by
                                                      have h0 : BitVec.ult (k.setWidth 64)
                                                          (BitVec.ofNat 64 sk.core.tmp_len) =
                                                          false := hk_lt
                                                      rw [hcore_k] at h0
                                                      rw [BitVec.ult, decide_eq_false_iff_not,
                                                        BitVec.toNat_setWidth,
                                                        Nat.mod_eq_of_lt (by
                                                          have := k.isLt; omega : k.toNat < 2 ^ 64),
                                                        BitVec.toNat_ofNat,
                                                        Nat.mod_eq_of_lt htl_lt64] at h0
                                                      omega
                                                    bve_ld load_full_tmp_len hmk
                                                    bve_jump
                                                    have htmp_tl : tl' ≤ tmp'.length := by
                                                      have := hinv_k.1.core_ok.tmp_len_arr
                                                      rw [hcore_k] at this
                                                      change tmp'.length = c.max_vars at this
                                                      rw [this]
                                                      exact Nat.le_trans htl_r
                                                        (by rw [hcvj]; exact hcv_le)
                                                    have hcp_tl : ∀ t < tl',
                                                        sk.scratch.scratch_buf[rp_j.toNat + 1 + t]?
                                                          = tmp'[t]? :=
                                                      fun t ht => hcp_k t (by omega)
                                                    have hres_sk :
                                                        FullBveVarSpecs.FullResBufOkW F_cur sk
                                                          (rp_j + 1#64 +
                                                            BitVec.ofNat 64 sk.core.tmp_len).toNat
                                                          160 := by
                                                      rw [hcore_k]
                                                      change FullBveVarSpecs.FullResBufOkW F_cur sk
                                                        (rp_j + 1#64 + BitVec.ofNat 64 tl').toNat
                                                        160
                                                      rw [hrp_sum_nat]
                                                      refine
                                                        FullBveVarHelpers.FullResBufOkW.append_block
                                                          (s := sj) (s' := sk) (r0 := 160)
                                                          (r1 := rp_j.toNat) (sz := tl')
                                                          (by rw [hcore_k]) hbuf_krp hsz_k ?_ ?_ ?_
                                                          hres_j
                                                      · intro t ht; rw [hcp_tl t ht, hcore_k]
                                                        exact htl_lits t ht
                                                      · rw [range_map_div2_eq_take_map
                                                          htmp_tl hcp_tl]
                                                        exact htl_nd
                                                      · rw [range_map_eq_take_map htmp_tl hcp_tl]
                                                        exact htl_ent
                                                    exact hJs2 (rc_j + 1#64,
                                                        rp_j + 1#64 +
                                                          BitVec.ofNat 64 sk.core.tmp_len,
                                                        fit_i, ()) mk
                                                      ⟨sk, hinv_k, htmk_k,
                                                        by rw [hcore_k]; exact hcvj,
                                                        by rw [hcore_k]; exact hflj,
                                                        by rw [hcore_k]; exact harj,
                                                        by rw [hcore_k]; exact halj, hbuf_k128,
                                                        (by rw [hcore_k]
                                                            change 160 ≤
                                                              (rp_j + 1#64 +
                                                                BitVec.ofNat 64 tl').toNat
                                                            rw [hrp_sum_nat]; omega),
                                                        (by rw [hcore_k]
                                                            change (rp_j + 1#64 +
                                                                BitVec.ofNat 64 tl').toNat ≤
                                                              c.scratch_cap
                                                            rw [hrp_sum_nat]; omega),
                                                        hres_sk, hmk⟩)
                                        · bve_jump
                                          exact hJs2 (rc_j, rp_j, fit_i, ()) m_r
                                            ⟨sr, hinv_r, htmk_r, hcvj, hflj, harj, halj, hbuf_j,
                                              hrpj_160, hrpj_cap,
                                              FullBveVarHelpers.FullResBufOkW.with_state
                                                (s := sj) (s' := sr) rfl (fun _ _ => rfl) hres_j,
                                              hm_r⟩
                                      · bve_jump
                                        exact hJs2 (rc_j, rp_j, fit_i, ()) mj
                                          ⟨sj, hinvj, htmkj, hcvj, hflj, harj, halj, hbuf_j,
                                            hrpj_160, hrpj_cap, hres_j, hmj⟩
                                  · intro J_np hJ_np
                                    bve_jnz hgf_not
                                    · bve_jnz hbit
                                      · bve_jump; exact hJ_np (true, ()) mj rfl
                                      · bve_jump; exact hJ_np (false, ()) mj rfl
                                    · bve_jump; exact hJ_np (true, ()) mj rfl
                                · exact absurd hfit_j (by rw [hfit_i]; decide)
                              · bve_jump
                                exact hJs (rc_j, rp_j, fit_i, j, ()) mj
                                  ⟨sj, hinvj, htmkj, hcvj, hflj, harj, halj, hbuf_j,
                                    (fun _ => ⟨hrpj_160, hrpj_cap, hres_j⟩), hmj⟩)
                      · bve_jump
                        exact hJ_fit (rc, rp, fit_i, ()) ml
                          ⟨sf, hinvf, htmkf, hcvf, hflf, harf, half, hbuf_f, hres_f, hml⟩
                    · bve_jump
                      exact hJ_fit (rc, rp, fit_i, ()) ml
                        ⟨sf, hinvf, htmkf, hcvf, hflf, harf, half, hbuf_f, hres_f, hml⟩)
              · intro J_gf hJ_gf
                bve_jnz hpm
                · bve_jump; exact hJ_gf (true, ()) m3 rfl
                · bve_jnz hnm
                  · bve_jump; exact hJ_gf (true, ()) m3 rfl
                  · bve_jump; exact hJ_gf (false, ()) m3 rfl
            · bve_jump; rw [hfit0]; exact hJ_fit (0#64, 160#64, false, PUnit.unit) m2
                ⟨s2, hinv2, htmk2, rfl, Nat.le_refl _, rfl, rfl, (fun _ _ => rfl),
                  (fun h => by cases h), hm2⟩
        · intro J hJ
          bve_jnz hext
          · refine wp_join_group (ts := []) (fun _ ml => (np = 0#32 ∨ nn = 0#32) ∧ ml = m2) ?_ ?_
            · rintro J1 _ ml ⟨_, h_ml⟩; subst ml; rw [Blocks.get_here]; bve_lets
              refine wp_join_group (ts := []) (fun _ ml =>
                  ∃ sw, FullBveVarSpecs.FullDenseInvW c F0 F_cur sw ∧ TmkInv sw ∧
                    sw.core.cur_vars = s.core.cur_vars ∧ sw.core.fuel = s.core.fuel ∧
                    (FullMem c sw ⋆ R) ml) ?_ ?_
              · rintro J_oom _ ml ⟨sw, hinvw, htmkw, hcvw, hflw, hmw⟩
                rw [Blocks.get_here]
                bve_st ml1, hm_oom := store_full_oom 1#64 hmw
                bve_ret
                let sw_o : FullState := { sw with core := { sw.core with oom := 1#64 } }
                exact hQ 2#64 sw_o ml1
                  (FullBveVarHelpers.FullDenseInvW.with_oom hinvw 1#64).toDense
                  (hTmk_cong htmkw rfl rfl) (by rw [← hcvw]; exact Nat.le_refl _)
                  (by rw [← hflw]; exact Nat.le_refl _)
                  (Or.inr (Or.inl rfl)) (fun h => by cases h) hm_oom
              · intro J_oom hJ_oom
                refine wp_join_group (ts := []) (fun _ ml =>
                    ∃ sw, FullBveVarSpecs.FullDenseInvW c F0 F_cur sw ∧ TmkInv sw ∧
                      sw.core.cur_vars = s.core.cur_vars ∧ sw.core.fuel = s.core.fuel ∧
                      fullArenaClauseRefs sw = fullArenaClauseRefs s2 ∧
                      sw.scratch.scratch_buf = scr2 ∧ (FullMem c sw ⋆ R) ml) ?_ ?_
                · rintro J_nn _ ml ⟨sw, hinvw, htmkw, hcvw, hflw, hrefs_sw, hscr_sw, hmw⟩
                  rw [Blocks.get_here]
                  refine wp_join_group (ts := []) (fun _ ml =>
                      ∃ sw1, FullBveVarSpecs.FullDenseInvW c F0 F_cur sw1 ∧ TmkInv sw1 ∧
                        sw1.core.cur_vars = s.core.cur_vars ∧ sw1.core.fuel = s.core.fuel ∧
                        (FullMem c sw1 ⋆ R) ml) ?_ ?_
                  · rintro J_inact _ ml1 ⟨sw1, hinvw1, htmkw1, hcvw1, hflw1, hmw1⟩
                    rw [Blocks.get_here]; bve_lets
                    refine wp_call_of_spec _ _ (hSetInact _ _ _ X ?_)
                    simp only [vals_nil, vals_cons, Arg.val_var, Arg.val_imm]
                    refine ⟨c, sw1, R, rfl, hinvw1.1, hmw1, ?_⟩
                    intro flags' unass' m_si hfl_len hm_si
                    let sw2 : FullState := { sw1 with core :=
                      { sw1.core with flags := flags', unassigned := unass' } }
                    have hinvw2 := FullBveVarHelpers.FullDenseInvW.with_flags_unassigned
                      hinvw1 hfl_len unass'
                    bve_ld load_full_bve_cnt hm_si
                    bve_st ml_bve, hm_bve := store_full_bve_cnt
                      (sw2.scratch.bve_cnt + 1#64) hm_si
                    bve_ret
                    let sw3 : FullState := { sw2 with scratch :=
                      { sw2.scratch with bve_cnt := sw2.scratch.bve_cnt + 1#64 } }
                    exact hQ 1#64 sw3 ml_bve
                      (FullBveVarHelpers.FullDenseInvW.with_bve_cnt hinvw2
                        (sw2.scratch.bve_cnt + 1#64)).toDense
                      (hTmk_cong htmkw1 rfl rfl) (by rw [← hcvw1]; exact Nat.le_refl _)
                      (by rw [← hflw1]; exact Nat.le_refl _) (Or.inl rfl)
                      (fun h => by cases h) hm_bve
                  · intro J_inact hJ_inact
                    bve_jnz hnn_pos
                    · refine wp_call_of_spec _ _ (hWeaken _ _ _ _ _ _ X ?_)
                      simp only [Arg.val_var, Arg.val_imm]
                      refine ⟨c, F0, F_cur, sw, R, rfl, hinvw, htmkw,
                        (by change (pl ||| 1#32).toNat < 2 * sw.core.cur_vars
                            rw [hnl_nat, hcvw, hs2_cv]; omega),
                        (by rw [h64_32]; omega),
                        (fun j hj => by
                          rw [hscr_sw, h64_32]
                          exact fullBveWeakItemOk_of_pres hcvw hrefs_sw
                            (FullBveVarHelpers.FullBveEntryOkW.to_weak (hn_ok j hj))), hmw, ?_⟩
                      intro ok2 sw' m_w2 hinvw' htmkw' hcvw' hflw' _ _ hm_w2
                      bve_jnz hok2
                      · bve_jump; exact hJ_inact () m_w2 ⟨sw', hinvw', htmkw',
                          hcvw'.trans hcvw, hflw'.trans hflw, hm_w2⟩
                      · bve_jump; exact hJ_oom () m_w2 ⟨sw', hinvw', htmkw',
                          hcvw'.trans hcvw, hflw'.trans hflw, hm_w2⟩
                    · bve_jump; exact hJ_inact () ml ⟨sw, hinvw, htmkw, hcvw, hflw, hmw⟩
                · intro J_nn hJ_nn
                  bve_jnz hnp_pos
                  · refine wp_call_of_spec _ _ (hWeaken _ _ _ _ _ _ X ?_)
                    simp only [Arg.val_var, Arg.val_imm]
                    refine ⟨c, F0, F_cur, s2, R, rfl, hinv2, htmk2,
                      (by change pl.toNat < 2 * s2.core.cur_vars; rw [hpl_nat, hs2_cv]; omega),
                      (by rw [h0_32]; omega),
                      (fun i hi => by
                        rw [h0_32, Nat.zero_add]
                        exact FullBveVarHelpers.FullBveEntryOkW.to_weak (hp_ok i hi)), hm2, ?_⟩
                    intro ok1 s2' m_w1 hinvw1 htmkw1 hcv1 hfl1 hscr_w1 hrefs_w1 hm_w1
                    bve_jnz hok1
                    · bve_jump; exact hJ_nn () m_w1 ⟨s2', hinvw1, htmkw1, hcv1, hfl1,
                        hrefs_w1, hscr_w1, hm_w1⟩
                    · bve_jump; exact hJ_oom () m_w1 ⟨s2', hinvw1, htmkw1, hcv1, hfl1, hm_w1⟩
                  · bve_jump; exact hJ_nn () m2 ⟨s2, hinv2, htmk2, rfl, rfl, rfl, rfl, hm2⟩
            · intro J1 hJ1
              bve_jnz hnp0
              · bve_jump; exact hJ1 () m2 ⟨Or.inl (by simpa using hnp0), rfl⟩
              · bve_jnz hnn0
                · bve_jump; exact hJ1 () m2 ⟨Or.inr (by simpa using hnn0), rfl⟩
                · bve_jump; exact hJ () m2 rfl
          · bve_jump; exact hJ () m2 rfl

/-- Canonical `Full.fullBveVarSpec` proof for upgraded `full_bve_var` (`64u` + gate skip). -/
theorem fast_bve_var_wp (Γ : Env)
    (hCollect : ∀ xs m Q X, fullBveCollectSpec xs m Q X →
      Γ "full_bve_collect" [i64, i32, i64, i32] [i32] xs m Q X)
    (hExtNeed : ∀ xs m Q X, fullBveExtNeedSpec xs m Q X →
      Γ "full_bve_ext_need" [i64, i32, i32] [i64] xs m Q X)
    (hWeaken : ∀ xs m Q X, fullBveWeakenSpec xs m Q X →
      Γ "full_bve_weaken" [i64, i32, i32, i32] [.bool] xs m Q X)
    (hSetInact : ∀ xs m Q X, fullSetInactiveSpec xs m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] xs m Q X)
    (hGates : ∀ xs m Q X, fullBveGatesSpec xs m Q X →
      Γ "full_bve_gates" [i64, i32, i32, i32] [] xs m Q X)
    (hResolve : ∀ xs m Q X, fullBveResolvePairSpec xs m Q X →
      Γ "full_bve_resolve_pair" [i64, i32, i32, i32] [.bool] xs m Q X)
    (hCommitRes : ∀ xs m Q X, fullBveCommitResSpec xs m Q X →
      Γ "full_bve_commit_res" [i64, i64, i64] [i64] xs m Q X)
    (hTryBce : ∀ xs m Q X, fullBveTryBceSpec xs m Q X →
      Γ "full_bve_try_bce" [i64, i32, i32, i32, i32] [.bool] xs m Q X)
    (hExtPush2 : ∀ xs m Q X, fullExtendPush2Spec xs m Q X →
      Γ "full_extend_push2" [i64, i32, i32] [.bool] xs m Q X)
    (hDelBin : ∀ xs m Q X, fullDeleteBinarySpec xs m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] xs m Q X)
    (hExtPushCl : ∀ xs m Q X, fullExtendPushClSpec xs m Q X →
      Γ "full_extend_push_cl" [i64, i32, i32] [.bool] xs m Q X) :
    ∀ args m Q X, Full.fullBveVarSpec args m Q X →
      Func.wp Γ full_bve_var_body args m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hdense, hv_lt, hm, hQ⟩
  refine fast_bve_var_core_wp Γ (fun _ => True) (fun _ _ _ => trivial) hCollect hExtNeed
    (fun h blk off cnt m0 Q0 X0 ⟨c0, F00, Fc0, s0, R0, hh, hd0, _, hblk, hoff, hw, hm0, hQ0⟩ =>
      hWeaken _ m0 Q0 X0 ⟨c0, F00, Fc0, s0, R0, hh, hd0, hblk, hoff, hw, hm0,
        fun ok s' m' h1 h2 h3 h4 h5 hm' => hQ0 ok s' m' h1 trivial h2 h3 h4 h5 hm'⟩)
    (bve_setInact_adapter hSetInact)
    (fun h v0 np0 nn0 m0 Q0 X0 ⟨c0, F00, Fc0, s0, R0, hh, hd0, hsc0, _, hv0, hnp0, hnn0, hp, hn,
        hm0, hQ0⟩ =>
      hGates _ m0 Q0 X0 ⟨c0, F00, Fc0, s0, R0, hh, hd0, hsc0, hv0, hnp0, hnn0, hp, hn, hm0,
        fun lm' scr' m' hd' hkp' hm' => hQ0 _ m' hd' trivial rfl rfl rfl (Nat.le_refl _)
          (fun i hi => hkp' i (by omega) (Or.inl hi)) hm'⟩)
    hResolve
    (fun h r_off r_end m0 Q0 X0 ⟨c0, F00, Fc0, s0, R0, hh, hd0, _, hle, hcap, hbuf, hm0, hQ0⟩ =>
      hCommitRes _ m0 Q0 X0 ⟨c0, F00, Fc0, s0, R0, hh, hd0, hle, hcap, bve_resBuf_of_bve hbuf, hm0,
        fun r s' m' h1 h2 h3 h4 h5 hm' => hQ0 r s' m' h1 trivial h2 h3 h4 h5 hm'⟩)
    (bve_tryBce_adapter hTryBce)
    (fun h blk ot m0 Q0 X0 ⟨c0, s0, R0, hpre, hlen0, _, hm0, hQ0⟩ =>
      hExtPush2 _ m0 Q0 X0 ⟨c0, s0, R0, hpre, hlen0, hm0,
        fun r s' m' hag hlen' hpost hm' => hQ0 r s' m' hag hlen' hpost trivial hm'⟩)
    hDelBin
    (fun h blk cr m0 Q0 X0 ⟨c0, s0, R0, hpre, hlen0, _, hm0, hQ0⟩ =>
      hExtPushCl _ m0 Q0 X0 ⟨c0, s0, R0, hpre, hlen0, hm0,
        fun r s' m' hag hlen' hpost hm' => hQ0 r s' m' hag hlen' hpost trivial hm'⟩)
    hdense trivial hv_lt hm
    (fun r s' m' hd' _ hcv hfl hr h20 hm' => hQ r s' m' hd' hcv hfl hr h20 hm')

/-- M2 `FullDefSweep`-compatible `fullBveVarDefSpec` proof preserving `TmkZero` and accepting
`FullDefGateUnsat`-carrying `fullBveGatesDefFastSpec`. -/
theorem fast_bve_var_def_wp (Γ : Env)
    (hCollect : ∀ xs m Q X, fullBveCollectSpec xs m Q X →
      Γ "full_bve_collect" [i64, i32, i64, i32] [i32] xs m Q X)
    (hExtNeed : ∀ xs m Q X, fullBveExtNeedSpec xs m Q X →
      Γ "full_bve_ext_need" [i64, i32, i32] [i64] xs m Q X)
    (hWeaken : ∀ xs m Q X, fullBveWeakenTmkSpec xs m Q X →
      Γ "full_bve_weaken" [i64, i32, i32, i32] [.bool] xs m Q X)
    (hSetInact : ∀ xs m Q X, fullSetInactiveSpec xs m Q X →
      Γ "full_set_inactive" [i64, i32, i32] [] xs m Q X)
    (hGates : ∀ xs m Q X, fullBveGatesDefFastSpec xs m Q X →
      Γ "full_bve_gates" [i64, i32, i32, i32] [] xs m Q X)
    (hResolve : ∀ xs m Q X, fullBveResolvePairSpec xs m Q X →
      Γ "full_bve_resolve_pair" [i64, i32, i32, i32] [.bool] xs m Q X)
    (hCommitRes : ∀ xs m Q X, fullBveCommitResTmkSpec xs m Q X →
      Γ "full_bve_commit_res" [i64, i64, i64] [i64] xs m Q X)
    (hTryBce : ∀ xs m Q X, fullBveTryBceSpec xs m Q X →
      Γ "full_bve_try_bce" [i64, i32, i32, i32, i32] [.bool] xs m Q X)
    (hExtPush2 : ∀ xs m Q X, fullExtendPush2TmkSpec xs m Q X →
      Γ "full_extend_push2" [i64, i32, i32] [.bool] xs m Q X)
    (hDelBin : ∀ xs m Q X, fullDeleteBinarySpec xs m Q X →
      Γ "full_delete_binary" [i64, i32, i32] [] xs m Q X)
    (hExtPushCl : ∀ xs m Q X, fullExtendPushClTmkSpec xs m Q X →
      Γ "full_extend_push_cl" [i64, i32, i32] [.bool] xs m Q X) :
    ∀ args m Q X, fullBveVarDefSpec args m Q X →
      Func.wp Γ full_bve_var_body args m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hdense, htmk, hv_lt, hm, hQ⟩
  refine fast_bve_var_core_wp Γ TmkZero (fun h hcv ht => h.congr hcv ht) hCollect hExtNeed
    (fun h blk off cnt m0 Q0 X0 ⟨c0, F00, Fc0, s0, R0, hh, hd0, htm0, hblk, hoff, hw, hm0, hQ0⟩ =>
      hWeaken _ m0 Q0 X0 ⟨c0, F00, Fc0, s0, R0, hh, hd0, htm0, hblk, hoff, hw, hm0, hQ0⟩)
    (bve_setInact_adapter hSetInact)
    (fun h v0 np0 nn0 m0 Q0 X0 ⟨c0, F00, Fc0, s0, R0, hh, hd0, hsc0, htm0, hv0, hnp0, hnn0,
        hp, hn, hm0, hQ0⟩ =>
      hGates _ m0 Q0 X0 ⟨c0, F00, Fc0, s0, R0, hh, hd0, hsc0, htm0, hv0, hnp0, hnn0, hp, hn, hm0,
        fun s' m' hd' htm' hcv' har' hal' hfl' hkp' _ hm' =>
          hQ0 s' m' hd' htm' hcv' har' hal' hfl' hkp' hm'⟩)
    hResolve
    (fun h r_off r_end m0 Q0 X0 ⟨c0, F00, Fc0, s0, R0, hh, hd0, htm0, hle, hcap, hbuf, hm0, hQ0⟩ =>
      hCommitRes _ m0 Q0 X0
        ⟨c0, F00, Fc0, s0, R0, hh, hd0, htm0, hle, hcap, bve_resBuf_of_bve hbuf, hm0, hQ0⟩)
    (bve_tryBce_adapter hTryBce)
    (fun h blk ot m0 Q0 X0 ⟨c0, s0, R0, hpre, hlen0, htm0, hm0, hQ0⟩ =>
      hExtPush2 _ m0 Q0 X0 ⟨c0, s0, R0, hpre, hlen0, hm0,
        fun r s' m' hag hlen' ⟨hll, hex, hscr, htmk_eq⟩ hm' =>
          hQ0 r s' m' hag hlen' ⟨hll, hex, hscr⟩
            (htm0.congr (congrArg FullCoreState.cur_vars (fullCoreState_agrees_with_scratch hag))
              htmk_eq) hm'⟩)
    hDelBin
    (fun h blk cr m0 Q0 X0 ⟨c0, s0, R0, hpre, hlen0, htm0, hm0, hQ0⟩ =>
      hExtPushCl _ m0 Q0 X0 ⟨c0, s0, R0, hpre, hlen0, hm0,
        fun r s' m' hag hlen' ⟨hll, hex, hscr, htmk_eq⟩ hm' =>
          hQ0 r s' m' hag hlen' ⟨hll, hex, hscr⟩
            (htm0.congr (congrArg FullCoreState.cur_vars (fullCoreState_agrees_with_scratch hag))
              htmk_eq) hm'⟩)
    hdense htmk hv_lt hm hQ

end BveVarProof

/-! ## 9. Closed `28`-Row Environment, `ModuleOk`, & Concrete `Mem 64` UNSAT Non-Vacuity -/

section ClosedEnvAndNonVacuity

/-- Closed `28`-row specification table (`7` upgraded functions + `21` externs, all `noExit`). -/
def fastBveBudgetsSpecTable : List SpecEntry :=
  [ ⟨"full_init_hdr", [i64, i64, i64, i64], [], fullFastInitHdrSpec, true⟩
  , ⟨"full_probe_run", [i64, i64], [i64], fullProbeRunFastSpec, true⟩
  , ⟨"full_transitive", [i64, i64], [i64], fullTransitiveFastSpec, true⟩
  , ⟨"full_vivify", [i64, i64, i64], [i64], fullVivifyFastSpec, true⟩
  , ⟨"full_tarjan_scc", [i64], [i64], fullTarjanSccFastSpec, true⟩
  , ⟨"full_forward_sub", [i64, i64], [i64], fullForwardSubFastSpec, true⟩
  , ⟨"full_bve_var", [i64, i32], [i64], Full.fullBveVarSpec, true⟩
  , ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  , ⟨"full_wstack_defrag", [i64], [], fullWstackDefragSpec, true⟩
  , ⟨"full_backtrack", [i64, i64], [], fullBacktrackSpec, true⟩
  , ⟨"full_propagate", [i64], [i64], fullPropagateSpec, true⟩
  , ⟨"full_extend_push2", [i64, i32, i32], [.bool], fullExtendPush2Spec, true⟩
  , ⟨"full_extend_push_cl", [i64, i32, i32], [.bool], fullExtendPushClSpec, true⟩
  , ⟨"full_delete_binary", [i64, i32, i32], [], fullDeleteBinarySpec, true⟩
  , ⟨"full_set_inactive", [i64, i32, i32], [], fullSetInactiveSpec, true⟩
  , ⟨"full_probe_assume_pair", [i64, i32], [i64], fullProbeAssumePairSpec, true⟩
  , ⟨"full_trans_lit", [i64, i32], [.bool], fullTransLitSpec, true⟩
  , ⟨"full_viv_clause", [i64, i32], [i64], fullVivClauseSpec, true⟩
  , ⟨"full_tarjan_pop_scc", [i64, i32, i32, i32], [.bool], fullTarjanPopSccSpec, true⟩
  , ⟨"full_fwd_dedup_bins", [i64], [.bool], fullFwdDedupBinsSpec, true⟩
  , ⟨"full_fwd_check_cl", [i64, i32], [.bool], fullFwdCheckClSpec, true⟩
  , ⟨"full_bve_collect", [i64, i32, i64, i32], [i32], fullBveCollectSpec, true⟩
  , ⟨"full_bve_gates", [i64, i32, i32, i32], [], fullBveGatesSpec, true⟩
  , ⟨"full_bve_resolve_pair", [i64, i32, i32, i32], [.bool], fullBveResolvePairSpec, true⟩
  , ⟨"full_bve_weaken", [i64, i32, i32, i32], [.bool], fullBveWeakenSpec, true⟩
  , ⟨"full_bve_try_bce", [i64, i32, i32, i32, i32], [.bool], fullBveTryBceSpec, true⟩
  , ⟨"full_bve_commit_res", [i64, i64, i64], [i64], fullBveCommitResSpec, true⟩
  , ⟨"full_bve_ext_need", [i64, i32, i32], [i64], fullBveExtNeedSpec, true⟩ ]

theorem fastBveBudgetsSpecTable_nodup :
    (fastBveBudgetsSpecTable.map SpecEntry.name).Nodup := by
  decide

theorem fastBveBudgetsSpecTable_noExit :
    ∀ e ∈ fastBveBudgetsSpecTable, e.noExit = true := by
  intro e he
  simp only [fastBveBudgetsSpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Closed environment for `fastBveBudgetsModule`. -/
def fastBveBudgetsEnv : Env := Env.ofTable fastBveBudgetsSpecTable

theorem fastBveBudgetsEnv_noExit :
    ∀ f as bs xs m Q X X',
      fastBveBudgetsEnv f as bs xs m Q X → fastBveBudgetsEnv f as bs xs m Q X' :=
  Env.ofTable_noExit fastBveBudgetsSpecTable_noExit

private theorem fastEnv_row {nm : String} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ fastBveBudgetsSpecTable)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    ∀ xs m Q X, sp xs m Q X → fastBveBudgetsEnv nm as bs xs m Q X :=
  fun xs m Q X hs =>
    Env.ofTable_of_mem (e := ⟨nm, as, bs, sp, true⟩) hmem fastBveBudgetsSpecTable_nodup
      (hno xs m Q X hs)

theorem fast_init_hdr_impl :
    SpecEntry.Impl fastBveBudgetsEnv
      ⟨"full_init_hdr", [i64, i64, i64, i64], [], full_init_hdr_body⟩
      ⟨"full_init_hdr", [i64, i64, i64, i64], [], fullFastInitHdrSpec, true⟩ :=
  SpecEntry.Impl.of (fast_init_hdr_wp fastBveBudgetsEnv)

theorem fast_probe_run_impl :
    SpecEntry.Impl fastBveBudgetsEnv
      ⟨"full_probe_run", [i64, i64], [i64], full_probe_run_body⟩
      ⟨"full_probe_run", [i64, i64], [i64], fullProbeRunFastSpec, true⟩ :=
  SpecEntry.Impl.of (fast_probe_run_wp fastBveBudgetsEnv
    (fastEnv_row (by simp [fastBveBudgetsSpecTable]) (fun _ _ _ _ h => h))
    (fastEnv_row (by simp [fastBveBudgetsSpecTable]) (fun _ _ _ _ h => h)))

theorem fast_transitive_impl :
    SpecEntry.Impl fastBveBudgetsEnv
      ⟨"full_transitive", [i64, i64], [i64], full_transitive_body⟩
      ⟨"full_transitive", [i64, i64], [i64], fullTransitiveFastSpec, true⟩ :=
  SpecEntry.Impl.of (fast_transitive_wp fastBveBudgetsEnv
    (fastEnv_row (by simp [fastBveBudgetsSpecTable]) (fun _ _ _ _ h => h))
    (fastEnv_row (by simp [fastBveBudgetsSpecTable]) (fun _ _ _ _ h => h))
    (fastEnv_row (by simp [fastBveBudgetsSpecTable]) (fun _ _ _ _ h => h))
    (fastEnv_row (by simp [fastBveBudgetsSpecTable]) (fun _ _ _ _ h => h)))

theorem fast_vivify_impl :
    SpecEntry.Impl fastBveBudgetsEnv
      ⟨"full_vivify", [i64, i64, i64], [i64], full_vivify_body⟩
      ⟨"full_vivify", [i64, i64, i64], [i64], fullVivifyFastSpec, true⟩ :=
  SpecEntry.Impl.of (fast_vivify_wp fastBveBudgetsEnv
    (fastEnv_row (by simp [fastBveBudgetsSpecTable]) (fun _ _ _ _ h => h))
    (fastEnv_row (by simp [fastBveBudgetsSpecTable]) (fun _ _ _ _ h => h))
    (fastEnv_row (by simp [fastBveBudgetsSpecTable]) (fun _ _ _ _ h => h))
    (fastEnv_row (by simp [fastBveBudgetsSpecTable]) (fun _ _ _ _ h => h)))

theorem fast_tarjan_scc_impl :
    SpecEntry.Impl fastBveBudgetsEnv
      ⟨"full_tarjan_scc", [i64], [i64], full_tarjan_scc_body⟩
      ⟨"full_tarjan_scc", [i64], [i64], fullTarjanSccFastSpec, true⟩ :=
  SpecEntry.Impl.of (fast_tarjan_scc_wp fastBveBudgetsEnv
    (fastEnv_row (by simp [fastBveBudgetsSpecTable]) (fun _ _ _ _ h => h)))

theorem fast_forward_sub_impl :
    SpecEntry.Impl fastBveBudgetsEnv
      ⟨"full_forward_sub", [i64, i64], [i64], full_forward_sub_body⟩
      ⟨"full_forward_sub", [i64, i64], [i64], fullForwardSubFastSpec, true⟩ :=
  SpecEntry.Impl.of (fast_forward_sub_wp fastBveBudgetsEnv
    (fastEnv_row (by simp [fastBveBudgetsSpecTable]) (fun _ _ _ _ h => h))
    (fastEnv_row (by simp [fastBveBudgetsSpecTable]) (fun _ _ _ _ h => h))
    (fastEnv_row (by simp [fastBveBudgetsSpecTable]) (fun _ _ _ _ h => h)))

theorem fast_bve_var_impl :
    SpecEntry.Impl fastBveBudgetsEnv
      ⟨"full_bve_var", [i64, i32], [i64], full_bve_var_body⟩
      ⟨"full_bve_var", [i64, i32], [i64], Full.fullBveVarSpec, true⟩ :=
  SpecEntry.Impl.of (fast_bve_var_wp fastBveBudgetsEnv
    (fastEnv_row (by simp [fastBveBudgetsSpecTable]) (fun _ _ _ _ h => h))
    (fastEnv_row (by simp [fastBveBudgetsSpecTable]) (fun _ _ _ _ h => h))
    (fastEnv_row (by simp [fastBveBudgetsSpecTable]) (fun _ _ _ _ h => h))
    (fastEnv_row (by simp [fastBveBudgetsSpecTable]) (fun _ _ _ _ h => h))
    (fastEnv_row (by simp [fastBveBudgetsSpecTable]) (fun _ _ _ _ h => h))
    (fastEnv_row (by simp [fastBveBudgetsSpecTable]) (fun _ _ _ _ h => h))
    (fastEnv_row (by simp [fastBveBudgetsSpecTable]) (fun _ _ _ _ h => h))
    (fastEnv_row (by simp [fastBveBudgetsSpecTable]) (fun _ _ _ _ h => h))
    (fastEnv_row (by simp [fastBveBudgetsSpecTable]) (fun _ _ _ _ h => h))
    (fastEnv_row (by simp [fastBveBudgetsSpecTable]) (fun _ _ _ _ h => h))
    (fastEnv_row (by simp [fastBveBudgetsSpecTable]) (fun _ _ _ _ h => h)))

theorem fastBveBudgets_allFns_wf : AllFns Fn.Wf fastBveBudgetsModule.fns :=
  ⟨full_init_hdr_wf, full_probe_run_wf, full_transitive_wf, full_vivify_wf,
    full_tarjan_scc_wf, full_forward_sub_wf, full_bve_var_wf, trivial⟩

theorem fastBveBudgets_tableImpl :
    TableImpl fastBveBudgetsEnv fastBveBudgetsModule.fns fastBveBudgetsSpecTable :=
  ⟨fast_init_hdr_impl, fast_probe_run_impl, fast_transitive_impl, fast_vivify_impl,
    fast_tarjan_scc_impl, fast_forward_sub_impl, fast_bve_var_impl, trivial⟩

/-- Headline `ModuleOk` certifying all `7` upgraded functions in `fastBveBudgetsModule`. -/
theorem fastBveBudgets_moduleOk : ModuleOk fastBveBudgetsEnv fastBveBudgetsModule :=
  Env.ofTable_moduleOk fastBveBudgets_acyclic fastBveBudgets_allFns_wf fastBveBudgets_tableImpl

/-! ### Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT proofs) -/

private theorem nvFast_sparseW :
    FullSparseInvW nvOneLitCfg nvOneLitF0 [[0], [1]] nvOneLitState := by
  have hmv : nvOneLitCfg.max_vars = 1 := rfl
  have hcv : nvOneLitState.core.cur_vars = 1 := rfl
  have hte : nvOneLitState.core.trail_end = 1 := rfl
  have hcl : nvOneLitState.core.cur_level = 0 := rfl
  have hdm : nvOneLitState.core.dense_mode = 0#64 := rfl
  have hrefs : fullArenaClauseRefsCore nvOneLitState.core = [] := rfl
  have hwat : ModeWatchesInv [[0], [1]] nvOneLitState.core := by
    unfold ModeWatchesInv; rw [ite_eq_left hdm]
    refine WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_) (fun l1 _ h1 _ _ hp => ?_)
      (fun l hl => ?_)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        (simp [fullWatchSizeCore, nvOneLitState] at hp)
    · rw [hcv] at h1; rcases (by omega : l1 = 0 ∨ l1 = 1) with rfl | rfl <;>
        (simp [fullWatchSizeCore, nvOneLitState] at hp)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> exact WatchSliceOk.empty
  have hent0 : (cnfOfClauses [[0], [1]]).EntailsClause (cnfClause [0]) := by
    rw [CNF.entails_clause_def]; intro α hα
    exact (CNF.sat_iff_all_mem_sat.mp hα) _ (CNF.Internal.mem_iff.mpr (by simp [cnfOfClauses]))
  have hw : FullWitnessInv nvOneLitCfg nvOneLitF0 [[0], [1]] nvOneLitState.core :=
    { ext_sound := ⟨(varsBoundedBool_iff 1 [[0], [1]]).mp rfl, id⟩
      inconsistent_sound := fun h => absurd rfl h
      arena := ⟨Or.inl rfl, fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr,
        fun r hr => by simp [hrefs] at hr, fun r hr => by simp [hrefs] at hr⟩
      watches := hwat, cur_level_le := Nat.zero_le _
      trail_lits_lt := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); decide
      trail_vars_nodup := fun i j hi hj _ => by rw [hte] at hi hj; omega
      vals_domain := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [nvOneLitState]
      vals_true_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
        · exact ⟨(fun h => by cases h), (fun ⟨i, hi, h⟩ => by
            rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h)⟩
      vals_false_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
        · exact ⟨(fun h => by cases h), (fun ⟨i, hi, h⟩ => by
            rw [hte] at hi; obtain rfl : i = 0 := (by omega); cases h)⟩
        · exact ⟨fun _ => ⟨0, Nat.zero_lt_one, rfl⟩, fun _ => rfl⟩
      lvl_le := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact Nat.le_refl 0
      dec_earliest := fun _ j _ hj _ hpos => by
        rw [hte] at hj; obtain rfl : j = 0 := (by omega); exact absurd hpos.1 (by decide)
      levels_inhabited := fun _ _ h2 => by rw [hcl] at h2; omega
      level0_sound := fun i hi _ => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact hent0
      trail_pos_inv := fun i hi => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      level0_rsn_none := fun i hi _ => by rw [hte] at hi; obtain rfl : i = 0 := (by omega); rfl
      frame_trail_lt := fun L hL => by rw [hcl] at hL; obtain rfl : L = 0 := (by omega); decide
      frame_trail_mono := fun L1 L2 _ hL2 => by
        rw [hcl] at hL2; obtain rfl : L1 = 0 := (by omega); obtain rfl : L2 = 0 := (by omega)
        exact Nat.le_refl _
      frame_trail_before_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      frame_dec_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      reason_inv := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne
      reason_lit_mem := fun i hi hne => by
        rw [hte] at hi; obtain rfl : i = 0 := (by omega); exact absurd rfl hne }
  refine ⟨nvOneLit_lengths, hw, ⟨fun v hv => ?_, fun l hl => ?_⟩, fun r hr => ?_,
    ⟨FullLastLearnedWf.of_cleared fun i hi => by
      simp only [nvOneLitState, nvOneLitScratch, List.getElem?_replicate, show i < 16 by omega,
        ↓reduceIte, Option.getD_some], Nat.le_refl 0⟩, rfl⟩
  · rw [hmv] at hv; obtain rfl : v = 0 := (by omega); rfl
  · rw [hmv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl
  · have : fullArenaClauseRefs nvOneLitState = [] := rfl; simp [this] at hr

/-- Concrete dense-mode UNSAT state (`dense_mode = 1`, `inconsistent = 1`) on `nvOneLitCfg`. -/
def nvDenseUnsatState : FullState :=
  { nvOneLitState with
    core := { nvOneLitState.core with dense_mode := 1#64, inconsistent := 1#64 } }

/-- Concrete `1756`-byte `Mem 64` image for `nvDenseUnsatState`. -/
def nvDenseUnsatMem : Mem 64 :=
  ((bytes64 [1#64, 2#64, 0#64, 0#64] ++
      bytes64 (Full.hdrTailWords nvOneLitCfg nvDenseUnsatState)) ++
    nvBlockBytes ++ nvBlockU32A ++ nvBlockU32B ++ nvBlockU32C ++ nvBlockWvec ++ nvBlockTail).At
    nvOneLitCfg.hdr

private theorem array64_unique {a : BitVec 64} {xs : List (BitVec 64)} {m1 m2 : Mem 64}
    (h1 : array64 a xs m1) (h2 : array64 a xs m2) : m1 = m2 := by
  induction xs generalizing a m1 m2 with
  | nil => exact h1.trans h2.symm
  | cons x xs ih =>
    obtain ⟨p1, q1, rfl, _, hp1, hq1⟩ := h1
    obtain ⟨p2, q2, rfl, _, hp2, hq2⟩ := h2
    rw [hp1.symm.trans hp2, ih hq1 hq2]

private theorem union_cancel_left {m1 m2 m2' : Mem 64}
    (hu : m1.union m2 = m1.union m2') (hd1 : m1.inter m2 = ∅) (hd2 : m1.inter m2' = ∅) :
    m2 = m2' := by
  apply ExtHashMap.ext_getElem?; intro k
  have h1 := congrArg (·[k]?) hu; simp only [union_eq, getElem?_union] at h1
  have d1 := eq_empty_iff_forall_not_mem.mp hd1 k
  have d2 := eq_empty_iff_forall_not_mem.mp hd2 k
  simp only [inter_eq, mem_inter_iff] at d1 d2
  cases hm1 : m1[k]? with
  | none => simpa only [hm1, Option.or_none] using h1
  | some _ =>
    have hmem : k ∈ m1 := mem_iff_isSome_getElem?.mpr (by simp [hm1])
    have hn1 : m2[k]? = none := Option.eq_none_iff_forall_ne_some.mpr fun _ hv =>
      d1 ⟨hmem, mem_iff_isSome_getElem?.mpr (by simp [hv])⟩
    have hn2 : m2'[k]? = none := Option.eq_none_iff_forall_ne_some.mpr fun _ hv =>
      d2 ⟨hmem, mem_iff_isSome_getElem?.mpr (by simp [hv])⟩
    rw [hn1, hn2]

private theorem nvDenseUnsatMem_ok : FullMem nvOneLitCfg nvDenseUnsatState nvDenseUnsatMem := by
  let c := nvOneLitCfg; let s := nvDenseUnsatState
  let bHdr0 := bytes64 [1#64, 2#64, 0#64, 0#64] ++ bytes64 (Full.hdrTailWords c nvOneLitState)
  let bHdr1 := bytes64 [1#64, 2#64, 0#64, 0#64] ++ bytes64 (Full.hdrTailWords c s)
  let bRest := nvBlockBytes ++ nvBlockU32A ++ nvBlockU32B ++ nvBlockU32C ++
    nvBlockWvec ++ nvBlockTail
  have hhdr_len0 : bHdr0.length = 1152 := by
    simp only [bHdr0, List.length_append, bytes64_length, Full.hdrTailWords_length]; decide
  have hrest_len : bRest.length = 604 := by
    simp only [bRest, nvBlockBytes, nvBlockU32A, nvBlockU32B, nvBlockU32C, nvBlockWvec,
      nvBlockTail, nvOneLitState, nvOneLitScratch, List.length_append, List.length_replicate,
      bytesOf_length, bytes64_length, List.length_cons, List.length_nil]
    decide
  have hHdr0 : bHdr0.length = 1152 ∧
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        nvOneLitState.core.d_cur nvOneLitState.core.d_val ⋆
        array64 (c.hdr + 32) (Full.hdrTailWords c nvOneLitState)) (bHdr0.At c.hdr) :=
    nv_join_pair
      (nv_arr64_p (a := c.hdr) (xs := [1#64, 2#64, 0#64, 0#64]) 32 rfl (by decide))
      (nv_arr64_p (a := c.hdr + 32) (xs := Full.hdrTailWords c nvOneLitState) 1120
        (by rw [Full.hdrTailWords_length]) (by decide)) (by decide) (by decide)
  have hHdr1 : bHdr1.length = 1152 ∧
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆ array64 (c.hdr + 32) (Full.hdrTailWords c s))
        (bHdr1.At c.hdr) :=
    nv_join_pair
      (nv_arr64_p (a := c.hdr) (xs := [1#64, 2#64, 0#64, 0#64]) 32 rfl (by decide))
      (nv_arr64_p (a := c.hdr + 32) (xs := Full.hdrTailWords c s) 1120
        (by rw [Full.hdrTailWords_length]) (by decide)) (by decide) (by decide)
  have hmem0 : FullMem c nvOneLitState ((bHdr0 ++ bRest).At c.hdr) := by
    have h0 := nvOneLitMem_ok
    unfold nvOneLitMem nvOneLitBytes nvBlockHdr at h0
    simpa only [bHdr0, bRest, List.append_assoc] using h0
  have hsep0 : ((dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        nvOneLitState.core.d_cur nvOneLitState.core.d_val ⋆
        array64 (c.hdr + 32) (Full.hdrTailWords c nvOneLitState)) ⋆
      (FullCoreArrays c nvOneLitState.core ⋆ FullScratchArrays c nvOneLitState.scratch ⋆ c.pad))
      ((bHdr0 ++ bRest).At c.hdr) := by
    unfold FullMem at hmem0; exact sep_ac hmem0
  have hEqRest : (FullCoreArrays c nvOneLitState.core ⋆
      FullScratchArrays c nvOneLitState.scratch ⋆ c.pad) (bRest.At (c.hdr + 1152#64)) := by
    have hsplit := congrFun (Mem.At_append_sep bHdr0 bRest c.hdr (by omega))
      ((bHdr0 ++ bRest).At c.hdr)
    have hm12 := hsplit.mp rfl
    obtain ⟨m1, m2, huni, hdisj, ⟨a1, b1, rfl, _, ha1, hb1⟩, hm2⟩ := hsep0
    obtain ⟨m1', m2', huni', hdisj', rfl, rfl⟩ := hm12
    obtain ⟨a0, b0, h0_eq, _, ha0, hb0⟩ := hHdr0.2
    have ha_eq : a1 = a0 := array64_unique (a := c.hdr) (xs := [1#64, 2#64, 0#64, 0#64]) ha1 ha0
    have hb_eq : b1 = b0 :=
      array64_unique (a := c.hdr + 32) (xs := Full.hdrTailWords c nvOneLitState) hb1 hb0
    have hm1_eq : a1.union b1 = bHdr0.At c.hdr := by rw [ha_eq, hb_eq, h0_eq]
    rw [hm1_eq] at huni hdisj
    have hm2_eq : m2 = bRest.At (c.hdr + BitVec.ofNat 64 bHdr0.length) :=
      union_cancel_left (huni.trans huni'.symm) hdisj hdisj'
    rw [hm2_eq, hhdr_len0] at hm2; exact hm2
  have hfin := nv_join_pair hHdr1 ⟨hrest_len, hEqRest⟩ (by decide) (by decide)
  have hfin' : FullMem c s ((bHdr1 ++ bRest).At c.hdr) := by
    unfold FullMem; exact sep_ac hfin.2
  simpa only [nvDenseUnsatMem, bHdr1, bRest, List.append_assoc] using hfin'

private theorem nvDenseUnsat_invW :
    FullDenseInvW nvOneLitCfg nvOneLitF0 [[0], [1]] nvDenseUnsatState := by
  have hsp := nvFast_sparseW
  have hdm : nvDenseUnsatState.core.dense_mode ≠ 0#64 := by decide
  have hwat : ModeWatchesInv [[0], [1]] nvDenseUnsatState.core := by
    unfold ModeWatchesInv; rw [ite_eq_right hdm]
    refine DenseWatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_)
      (fun l1 _ h1 _ _ hp => ?_) (fun l hl => ?_)
    · change l < 2 * 1 at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
    · change l < 2 * 1 at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        (simp [fullWatchSizeCore, nvDenseUnsatState, nvOneLitState] at hp)
    · change l1 < 2 * 1 at h1; rcases (by omega : l1 = 0 ∨ l1 = 1) with rfl | rfl <;>
        (simp [fullWatchSizeCore, nvDenseUnsatState, nvOneLitState] at hp)
    · change l < 2 * 1 at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;>
        exact DenseWatchSliceOk.empty
  exact ⟨⟨{ hsp.1.core_ok with vals_len := hsp.1.core_ok.vals_len }, hsp.1.scratch_ok⟩,
    { hsp.2.1 with
      inconsistent_sound := fun _ => nvDeduceF0_unsat
      arena := { hsp.2.1.arena with len_ok := hsp.2.1.arena.len_ok }
      watches := hwat },
    hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, rfl, hdm⟩

/-- Concrete `1120`-byte header-tail image for `nv_fast_init_hdr`. -/
def nvInitHdrMem : Mem 64 :=
  (bytes64 (Full.hdrTailWords nvOneLitCfg nvOneLitState)).At (nvOneLitCfg.hdr + 32)

/-- Concrete `Mem 64` non-vacuity (`XPost := False`): `full_init_hdr` sets `probe_limit = 2000`
and `elim_limit = 5000`. -/
theorem nv_fast_init_hdr :
    Func.wp fastBveBudgetsEnv full_init_hdr_body
      (nvOneLitCfg.hdr, 1#64, 1#64, 100#64, ()) nvInitHdrMem
      (fun () m' => ∃ s',
        s'.scratch.probe_limit = 2000#64 ∧ s'.scratch.elim_limit = 5000#64 ∧
        array64 (nvOneLitCfg.hdr + 32) (Full.hdrTailWords nvOneLitCfg s') m')
      (fun _ _ _ _ => False) := by
  have hm : (array64 (nvOneLitCfg.hdr + 32) (Full.hdrTailWords nvOneLitCfg nvOneLitState) ⋆ emp)
      nvInitHdrMem := by
    rw [sep_emp]; exact array64_bytes _ _ (by rw [Full.hdrTailWords_length]; decide)
  refine fast_init_hdr_wp fastBveBudgetsEnv _ _ _ _
    ⟨nvOneLitCfg, Full.hdrTailWords nvOneLitCfg nvOneLitState, emp, rfl, rfl, rfl,
      Full.hdrTailWords_length nvOneLitCfg nvOneLitState, fun s0 i hi => ?_, hm,
      fun s' m' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpl hel hm' => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · rw [sep_emp] at hm'; exact ⟨s', hpl, hel, hm'⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_probe_run`. -/
theorem nv_fast_probe_run :
    Func.wp fastBveBudgetsEnv full_probe_run_body
      (nvOneLitCfg.hdr, 10#64, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧ (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧
        FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  exact fast_probe_run_impl.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, nvOneLitState, emp, rfl, nvFast_sparseW.toSparse, hm,
      fun r s' m' hsp _ _ _ _ hr _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hsp, hr, nvDeduceF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_transitive`. -/
theorem nv_fast_transitive :
    Func.wp fastBveBudgetsEnv full_transitive_body
      (nvOneLitCfg.hdr, 10#64, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧ (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧
        FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  exact fast_transitive_impl.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, nvOneLitState, emp, rfl, nvFast_sparseW.toSparse, hm,
      fun r s' m' hsp _ _ _ _ hr _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hsp, hr, nvDeduceF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_vivify`. -/
theorem nv_fast_vivify :
    Func.wp fastBveBudgetsEnv full_vivify_body
      (nvOneLitCfg.hdr, 0#64, 10#64, ()) nvOneLitMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvOneLitCfg nvOneLitF0 s' ∧ s'.core.cur_level = 0 ∧
        s'.core.probing = 0#64 ∧ (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧
        FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  exact fast_vivify_impl.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, nvOneLitState, emp, rfl, nvFast_sparseW.toSparse, hm,
      fun r s' m' hsp _ _ hnz _ hr _ hm' => by
        obtain ⟨hcl0, hpr0⟩ := hnz (by decide)
        rw [sep_emp] at hm'; exact ⟨s', hsp, hcl0, hpr0, hr, nvDeduceF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_tarjan_scc`: certifies
`TmkZero s'` and zeroed `tmk`/`trc` on exit. -/
theorem nv_fast_tarjan_scc :
    Func.wp fastBveBudgetsEnv full_tarjan_scc_body
      (nvOneLitCfg.hdr, ()) nvOneLitMem
      (fun (_r, ()) m' => ∃ s',
        FullSparseInvW nvOneLitCfg nvOneLitF0 [[0], [1]] s' ∧ TmkZero s' ∧ nvOneLitF0.Unsat ∧
        (∀ l < 2 * nvOneLitState.core.cur_vars,
          s'.scratch.tarjan_mark[l]?.getD 0#32 = 0#32 ∧
          s'.scratch.tarjan_reach[l]?.getD 0#32 = 0#32) ∧
        FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  exact fast_tarjan_scc_impl.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, [[0], [1]], nvOneLitState, emp, rfl, nvFast_sparseW, rfl, hm,
      fun _ _ _ _ _ _ _ _ _ _ _ m' hsp _ _ _ hclr htmk hm' => by
        rw [sep_emp] at hm'; exact ⟨_, hsp, htmk, nvDeduceF0_unsat, hclr, hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_forward_sub`. -/
theorem nv_fast_forward_sub :
    Func.wp fastBveBudgetsEnv full_forward_sub_body
      (nvOneLitCfg.hdr, 10#64, ()) nvDenseUnsatMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvOneLitCfg nvOneLitF0 s' ∧ (r = 1#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧
        FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvDenseUnsatState ⋆ emp) nvDenseUnsatMem := by
    rw [sep_emp]; exact nvDenseUnsatMem_ok
  exact fast_forward_sub_impl.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, nvDenseUnsatState, emp, rfl, nvDenseUnsat_invW.toDense, hm,
      fun r s' m' hd _ _ hr _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hd, hr, nvDeduceF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` `r = 20#64` UNSAT non-vacuity (`XPost := False`) for `full_forward_sub`
under an UNSAT-returning `full_fwd_dedup_bins` witness env. -/
theorem nv_fast_forward_sub_unsat20 :
    let Γ20 : Env := fun f as bs xs m Q X =>
      if f = "full_fwd_dedup_bins" then
        ∃ (_ : as = [i64]) (h2 : bs = [.bool]), Q (h2 ▸ (false, ())) m
      else fastBveBudgetsEnv f as bs xs m Q X
    Func.wp Γ20 full_forward_sub_body
      (nvOneLitCfg.hdr, 10#64, ()) nvDenseUnsatMem
      (fun (r, ()) m' => r = 20#64 ∧ nvOneLitF0.Unsat ∧
        FullMem nvOneLitCfg nvDenseUnsatState m')
      (fun _ _ _ _ => False) := by
  intro Γ20
  unfold Func.wp full_forward_sub_body
  c0_steps
  refine wp_call_of_spec _ _ ?_
  dsimp only [Γ20]; rw [ite_eq_left rfl]
  refine ⟨rfl, rfl, ?_⟩
  exact ⟨(fun h => by cases h), fun _ => ⟨rfl, nvDeduceF0_unsat, nvDenseUnsatMem_ok⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_bve_var`. -/
theorem nv_fast_bve_var :
    Func.wp fastBveBudgetsEnv full_bve_var_body
      (nvOneLitCfg.hdr, 0#32, ()) nvDenseUnsatMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvOneLitCfg nvOneLitF0 s' ∧ (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧
        nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvDenseUnsatState ⋆ emp) nvDenseUnsatMem := by
    rw [sep_emp]; exact nvDenseUnsatMem_ok
  exact fast_bve_var_impl.2 _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, nvDenseUnsatState, emp, rfl, nvDenseUnsat_invW.toDense,
      by decide, hm, fun r s' m' hd _ _ hr _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hd, hr, nvDeduceF0_unsat, hm'⟩⟩

/-- Concrete `Mem 64` `TmkZero`-preserving UNSAT non-vacuity (`XPost := False`) for
`full_bve_var` (`fullBveVarDefSpec`). -/
theorem nv_fast_bve_var_def :
    let Γdef : Env := fun f as bs xs m Q X =>
      if f = "full_bve_gates" then
        ∃ (h1 : as = [i64, i32, i32, i32]) (h2 : bs = []),
          fullBveGatesDefFastSpec (h1 ▸ xs) m (h2 ▸ Q) X
      else if f = "full_bve_weaken" then
        ∃ (h1 : as = [i64, i32, i32, i32]) (h2 : bs = [.bool]),
          fullBveWeakenTmkSpec (h1 ▸ xs) m (h2 ▸ Q) X
      else if f = "full_bve_commit_res" then
        ∃ (h1 : as = [i64, i64, i64]) (h2 : bs = [i64]),
          fullBveCommitResTmkSpec (h1 ▸ xs) m (h2 ▸ Q) X
      else if f = "full_extend_push2" then
        ∃ (h1 : as = [i64, i32, i32]) (h2 : bs = [.bool]),
          fullExtendPush2TmkSpec (h1 ▸ xs) m (h2 ▸ Q) X
      else if f = "full_extend_push_cl" then
        ∃ (h1 : as = [i64, i32, i32]) (h2 : bs = [.bool]),
          fullExtendPushClTmkSpec (h1 ▸ xs) m (h2 ▸ Q) X
      else fastBveBudgetsEnv f as bs xs m Q X
    Func.wp Γdef full_bve_var_body
      (nvOneLitCfg.hdr, 0#32, ()) nvDenseUnsatMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvOneLitCfg nvOneLitF0 s' ∧ TmkZero s' ∧
        (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  intro Γdef
  have hm : (FullMem nvOneLitCfg nvDenseUnsatState ⋆ emp) nvDenseUnsatMem := by
    rw [sep_emp]; exact nvDenseUnsatMem_ok
  have htmk : TmkZero nvDenseUnsatState := fun v hv => by
    change v < 1 at hv; obtain rfl : v = 0 := (by omega); rfl
  refine fast_bve_var_def_wp Γdef
    (fun xs m Q X h =>
      fastEnv_row (by simp [fastBveBudgetsSpecTable]) (fun _ _ _ _ h => h) xs m Q X h)
    (fun xs m Q X h =>
      fastEnv_row (by simp [fastBveBudgetsSpecTable]) (fun _ _ _ _ h => h) xs m Q X h)
    (fun _ _ _ _ h => ⟨rfl, rfl, h⟩)
    (fun xs m Q X h =>
      fastEnv_row (by simp [fastBveBudgetsSpecTable]) (fun _ _ _ _ h => h) xs m Q X h)
    (fun _ _ _ _ h => ⟨rfl, rfl, h⟩)
    (fun xs m Q X h =>
      fastEnv_row (by simp [fastBveBudgetsSpecTable]) (fun _ _ _ _ h => h) xs m Q X h)
    (fun _ _ _ _ h => ⟨rfl, rfl, h⟩)
    (fun xs m Q X h =>
      fastEnv_row (by simp [fastBveBudgetsSpecTable]) (fun _ _ _ _ h => h) xs m Q X h)
    (fun _ _ _ _ h => ⟨rfl, rfl, h⟩)
    (fun xs m Q X h =>
      fastEnv_row (by simp [fastBveBudgetsSpecTable]) (fun _ _ _ _ h => h) xs m Q X h)
    (fun _ _ _ _ h => ⟨rfl, rfl, h⟩)
    _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, nvDenseUnsatState, emp, rfl, nvDenseUnsat_invW.toDense, htmk,
      by decide, hm, fun r s' m' hd htm' _ _ hr _ hm' => by
        rw [sep_emp] at hm'; exact ⟨s', hd, htm', hr, nvDeduceF0_unsat, hm'⟩⟩

end ClosedEnvAndNonVacuity

end LeanQbe.T.Examples.Kissat.FullFastBveBudgets
