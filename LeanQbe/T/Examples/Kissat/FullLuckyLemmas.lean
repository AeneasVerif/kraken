module

public import LeanQbe.T.Examples.Kissat.FullSpec3
public import LeanQbe.T.Examples.Kissat.FullLuckyLemmas1
public import LeanQbe.T.Examples.Kissat.FullLuckyLemmas2
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Lucky Probing Hub (`Stage 4`, Part 3: `full_lucky`)

Re-exports `FullLuckyLemmas1` (`full_lucky_polar_wp`) and `FullLuckyLemmas2`
(`full_lucky_scan_wp`), and proves `full_lucky_wp` parametrically over `Γ : Env`
targeting canonical `Full.fullLuckySpec`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open FullLuckyHelpers
open scoped FullArenaTactics FullLuckyTactics

private theorem bv64_four : BitVec.ofNat 64 4 = (4 : BitVec 64) := rfl
private theorem bv64_144 : BitVec.ofNat 64 144 = (144 : BitVec 64) := rfl
private theorem bv64_160 : BitVec.ofNat 64 160 = (160 : BitVec 64) := rfl
private theorem bv64_168 : BitVec.ofNat 64 168 = (168 : BitVec 64) := rfl
private theorem bv64_520 : BitVec.ofNat 64 520 = (520 : BitVec 64) := rfl
private theorem bv64_768 : BitVec.ofNat 64 768 = (768 : BitVec 64) := rfl
private theorem bv64_776 : BitVec.ofNat 64 776 = (776 : BitVec 64) := rfl

namespace FullLuckyHelpers

/-- Updating `probing` preserves `FullState.LengthsOk`. -/
theorem lengthsOk_with_probing {c : FullCfg} {s : FullState}
    (h : s.LengthsOk c) (v : BitVec 64) :
    ({ s with core := { s.core with probing := v } } : FullState).LengthsOk c :=
  ⟨{ h.core_ok with cur_vars_le := h.core_ok.cur_vars_le }, h.scratch_ok⟩

/-- Shared `full_backtrack(h, 0); s->probing = 0; return r` exit step from `FullSparseInv`. -/
theorem call_backtrack0_probing0_ret_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {s_init s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    {r : BitVec 64}
    (hBt : ∀ args m Q X, fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X)
    (hsp : FullSparseInv c F0 s) (hfl : s.core.fuel.toNat ≤ s_init.core.fuel.toNat)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ s' m', s'.LengthsOk c → s'.core.fuel.toNat ≤ s_init.core.fuel.toNat →
      s'.core.probing = 0#64 → FullSparseInv c F0 s' → s'.core.cur_level = 0 →
      (FullMem c s' ⋆ R) m' → Q (r, PUnit.unit) m') :
    wp Γ Q X (@Expr.call Val Cont [i64] "full_backtrack" [i64, i64] []
      (Arg.var c.hdr, Arg.imm (0 : BitVec 64), PUnit.unit)
      fun _ => Expr.let_
        { sig := [i64, i64], code := OpCode.add i64,
          args := (Arg.var c.hdr, Arg.imm (520 : BitVec 64), PUnit.unit) }
        fun p => Expr.store (t := i64) (Arg.imm (0 : BitVec 64)) (Arg.var p.fst)
          (Expr.ret (Arg.imm r, PUnit.unit))) m := by
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv_le := hsp.1.lengths.core_ok.cur_vars_le
  have hte_le := hsp.1.lengths.core_ok.trail_end_le
  obtain ⟨F_cur, hw⟩ := hsp.1.witness
  have hcl_lt : s.core.cur_level < 2 ^ 64 := by have := hw.cur_level_le; omega
  c0_call hBt
  refine ⟨c, s, R, rfl, hsp.1.lengths, hcl_lt,
    fun _ => by
      have h0 : (0 : BitVec 64).toNat = 0 := rfl
      rw [h0]; have := hw.cur_level_le; omega,
    hw.trail_lits_lt, hm, ?_⟩
  dsimp only
  intro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m'
    hlen' _hte _hprop hcl' hps _hsh _htrl _hbv hwt _hot hm'
  let s_bt : FullState :=
    { core := { s.core with
        vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
        trail_end := te', propagated := prop', cur_level := cl', unassigned := unass' }
      scratch := sc' }
  have hsp_bt : FullSparseInv c F0 s_bt :=
    fullSparseInv_of_fullBacktrack hsp hlen'
      (hwt F0 F_cur hw (Nat.zero_le _)) rfl rfl rfl rfl rfl hps.1.1 hps.1.2
  have hcl0_bt : s_bt.core.cur_level = 0 := by change cl' = 0; rw [hcl']; simp
  flk_steps
  let s' : FullState := { s_bt with core := { s_bt.core with probing := 0#64 } }
  have hsp' : FullSparseInv c F0 s' := FullSparseInv.with_probing hsp_bt 0#64
  exact hQ s' _ hsp'.1.lengths hfl rfl hsp' hcl0_bt (by assumption)

end FullLuckyHelpers

/-! ## `full_lucky` parametric `Func.wp` proof -/

theorem full_lucky_wp (Γ : Env)
    (hPolar : ∀ args m Q X, fullLuckyPolarSpec args m Q X →
      Γ "full_lucky_polar" [i64] [i64] args m Q X)
    (hScan : ∀ args m Q X, fullLuckyScanSpec args m Q X →
      Γ "full_lucky_scan" [i64, .bool, .bool] [i64] args m Q X)
    (hAssign : ∀ args m Q X, fullAssignSpec args m Q X →
      Γ "full_assign" [i64, i32, i32] [] args m Q X)
    (hBt : ∀ args m Q X, fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X)
    (hProp : ∀ args m Q X, fullPropagateSpec args m Q X →
      Γ "full_propagate" [i64] [i64] args m Q X) :
    ∀ args m Q X, fullLuckySpec args m Q X →
      Func.wp Γ full_lucky_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hcl0, hm, hQ⟩
  unfold full_lucky_body
  dsimp only [Func.wp]
  (try simp only [bv64_520])
  flk_steps
  let s0 : FullState := { s with core := { s.core with probing := 1#64 } }
  have hsp0 : FullSparseInv c F0 s0 := FullSparseInv.with_probing hsp 1#64
  have hcl0' : s0.core.cur_level = 0 := hcl0
  c0_call hPolar
  refine ⟨c, F0, s0, R, rfl, hsp0.1, by assumption, ?_⟩
  intro p2 hr2
  flk_unmdata
  flk_to_group
  · have hret_bt : ∀ r (s_b : FullState) mb,
        FullSparseInv c F0 s_b → s_b.core.fuel.toNat ≤ s.core.fuel.toNat →
        (FullMem c s_b ⋆ R) mb → (r = 0#64 ∨ r = 2#64) →
        wp Γ Q X (@Expr.call Val Cont [i64] "full_backtrack" [i64, i64] []
          (Arg.var c.hdr, Arg.imm (0 : BitVec 64), PUnit.unit)
          fun _ => Expr.let_
            { sig := [i64, i64], code := OpCode.add i64,
              args := (Arg.var c.hdr, Arg.imm (520 : BitVec 64), PUnit.unit) }
            fun p => Expr.store (t := i64) (Arg.imm (0 : BitVec 64)) (Arg.var p.fst)
              (Expr.ret (Arg.imm r, PUnit.unit))) mb := by
      intro r s_b mb hsb hfl_b hmb hr_or
      refine call_backtrack0_probing0_ret_wp hBt hsb hfl_b hmb
        fun s' m' hlen' hfl' hpr' hsp' hcl0' hm' => ?_
      exact hQ r s' m' hlen' (by rcases hr_or with rfl | rfl <;> simp) hfl' hpr'
        (fun h => by rcases hr_or with rfl | rfl <;> cases h)
        (fun _ => ⟨hsp', hcl0'⟩) (fun _ => hsp'.2.2.2.1.2) hm'
    refine wp_loop_group (ts := [i64])
      (fun rem (idx, _) ml => ∃ st : FullState,
        rem = s.core.cur_vars - idx.toNat ∧ idx.toNat ≤ s.core.cur_vars ∧
        st.core.cur_vars = s.core.cur_vars ∧ FullSparseInv c F0 st ∧
        st.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c st ⋆ R) ml) ?_ ?_
    · rintro Jloop rem ⟨idx, ⟨⟩⟩ ml ih ⟨st, rfl, hidx_le, hcv_eq, hst, hfl, hml⟩
      have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
      have hcv_le := hst.1.lengths.core_ok.cur_vars_le
      dsimp [Blocks.get]
      (try simp only [bv64_520, bv64_776])
      flk_unmdata
      flk_to_group
      · have hidx_lt : idx.toNat < st.core.cur_vars := by
          have hmod := Nat.mod_eq_of_lt (by omega : st.core.cur_vars < 2 ^ 64)
          simp only [hmod] at *
          assumption
        have hidx1_nat : (idx + 1#64).toNat = idx.toNat + 1 :=
          FullLuckyTactics.bv64_add1_toNat (by omega)
        refine wp_join_group (ts := []) (fun _ mn =>
            ∃ st' : FullState, st'.core.cur_vars = s.core.cur_vars ∧
              FullSparseInv c F0 st' ∧ st'.core.fuel.toNat ≤ s.core.fuel.toNat ∧
              (FullMem c st' ⋆ R) mn) ?_ ?_
        · rintro Jnext ⟨⟩ mn ⟨st', hcv', hst', hfl', hmn⟩
          dsimp [Blocks.get]; flk_steps
          exact ih (s.core.cur_vars - (idx.toNat + 1)) (idx + 1#64, PUnit.unit) mn (by omega)
            ⟨st', by simp [hidx1_nat], by omega, hcv', hst', hfl', hmn⟩
        · intro Jnext hJnext
          have hidx_fl : idx.toNat < st.core.flags.length := by
            have := hst.1.lengths.core_ok.flags_len; omega
          have hidx2_vl : (idx <<< 1#64).toNat < st.core.vals.length := by
            have := hst.1.lengths.core_ok.vals_len
            rw [FullLuckyTactics.bv64_shl1_toNat (by omega)]; omega
          flk_unmdata
          (try simp only [bv64_four, bv64_144, bv64_160, bv64_168, bv64_768])
          flk_to_group
          · exact hret_bt 2#64 st _ hst hfl (by assumption) (Or.inr rfl)
          · have hfl_ne : st.core.fuel ≠ 0#64 := by simpa using ‹_›
            have hfl_sub : (st.core.fuel - 1#64).toNat = st.core.fuel.toNat - 1 :=
              FullLuckyTactics.bv64_sub1_toNat hfl_ne
            have hval0 : st.core.vals[2 * idx.toNat]?.getD 0#8 = 0#8 := by
              have h2v : (idx <<< 1#64).toNat = 2 * idx.toNat :=
                FullLuckyTactics.bv64_shl1_toNat (by omega)
              have h_eq : BitVec.signExtend 32 st.core.vals[2 * idx.toNat % 2 ^ 64] = 0#32 := by
                assumption
              have h_mod : 2 * idx.toNat % 2 ^ 64 = 2 * idx.toNat := by omega
              rw [FullLuckyTactics.bv8_sext32_eq0_iff] at h_eq
              have h2_lt : 2 * idx.toNat < st.core.vals.length := by
                rw [← h2v]; exact hidx2_vl
              have h_eq0 : st.core.vals[2 * idx.toNat] = 0#8 := by simpa [h_mod] using h_eq
              simp [List.getElem?_eq_getElem h2_lt, h_eq0]
            let st1 : FullState :=
              { st with core := { st.core with fuel := st.core.fuel - 1#64 } }
            have hst1 : FullSparseInv c F0 st1 := FullSparseInv.with_fuel hst (st.core.fuel - 1#64)
            have hfl1 : st1.core.fuel.toNat ≤ s.core.fuel.toNat := by
              change (st.core.fuel - 1#64).toNat ≤ s.core.fuel.toNat; rw [hfl_sub]; omega
            refine wp_join_group (ts := [i32]) (fun (lit, _) mlit =>
                (FullMem c st1 ⋆ R) mlit ∧ lit.toNat / 2 = idx.toNat) ?_ ?_
            · rintro Jlit ⟨lit, ⟨⟩⟩ mlit ⟨hmlit, hlit_v⟩
              dsimp [Blocks.get]
              obtain ⟨_, _, _, hnlvl_bv, hft_len, hfd_len, hnlvl_ne⟩ :=
                decide_nlvl_ok hst1 hidx_lt hval0
              have hte32_1 : st1.core.trail_end < 2 ^ 32 := by
                have := hst1.1.lengths.core_ok.cur_vars_le; omega
              flk_unmdata
              (try simp only [bv64_four, bv64_144, bv64_160, bv64_768])
              c0_steps!
              rw [hnlvl_bv, FullLuckyTactics.bv64_trunc32_ofNat hte32_1] at *
              refine call_assign_prop_decide_wp (R := R) hAssign hProp hst1 hfl1 hidx_lt hval0
                hlit_v (by assumption) fun r1 _ _ s_p1 mp1 _ hsp1 _ _ hcv1
                  hfl_p1 _ _ _ _ _ _ hmp1 => ?_
              flk_unmdata; flk_to_group
              · exact hret_bt 0#64 s_p1 mp1 hsp1 hfl_p1 hmp1 (Or.inl rfl)
              · flk_steps
                exact hJnext PUnit.unit mp1 ⟨s_p1, by
                  change s_p1.core.cur_vars = s.core.cur_vars
                  rw [hcv1]; exact hcv_eq, hsp1, hfl_p1, hmp1⟩
            · intro Jlit hJlit; flk_steps
              · have hl : (BitVec.setWidth 32 (idx <<< 1)).toNat = 2 * idx.toNat := by bv_omega
                exact hJlit _ _ ⟨‹_›, by rw [hl]; omega⟩
              · have h_eq1 : (idx <<< 1) = (idx <<< 1#64) := rfl
                have hl : (BitVec.setWidth 32 (idx <<< 1) ||| 1#32).toNat =
                    2 * idx.toNat + 1 := by
                  rw [h_eq1]; exact FullLuckyTactics.bv32_shl1_or1_trunc32_toNat (by omega)
                exact hJlit _ _ ⟨‹_›, by rw [hl]; omega⟩
          · exact hJnext PUnit.unit _ ⟨st, hcv_eq, hst, hfl, hml⟩
          · exact hJnext PUnit.unit _ ⟨st, hcv_eq, hst, hfl, hml⟩
      · flk_steps
        let st' : FullState := { st with core := { st.core with probing := 0#64 } }
        exact hQ 10#64 st' _ (lengthsOk_with_probing hst.1.lengths 0#64)
          (Or.inr (Or.inr (Or.inl rfl))) hfl rfl
          (fun h => absurd h (by decide)) (fun h => by rcases h with h | h <;> cases h)
          (fun _ => hst.2.2.2.1.2) (by assumption)
    · intro Jloop hJloop; flk_steps
      exact hJloop s.core.cur_vars (0#64, PUnit.unit) _
        ⟨s0, by simp, Nat.zero_le _, rfl, hsp0, Nat.le_refl _, by assumption⟩
  · let LuckyRet : Tup Val [i64] → Mem 64 → Prop := fun (r, _) mr =>
      ∃ sr : FullState, sr.LengthsOk c ∧ (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) ∧
        sr.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (r = 20#64 → F0.Unsat) ∧
        (r = 0#64 ∨ r = 2#64 → FullSparseInv c F0 sr ∧ sr.core.cur_level = 0) ∧
        (r = 10#64 → sr.scratch.extend_len ≤ c.extend_cap) ∧ (FullMem c sr ⋆ R) mr
    c0_call hScan
    refine ⟨c, F0, s0, R, rfl, hsp0, hcl0', by assumption, ?_⟩
    intro r1 s1 m1 hlen1 hr1 hfl1 huns1 h02_1 h10_1 hm1
    flk_unmdata; flk_to_group
    refine wp_join_group (ts := [i64]) LuckyRet ?_ ?_
    · rintro JsA ⟨rA, ⟨⟩⟩ mA ⟨srA, hlenA, hrA, hflA, hunsA, h02A, h10A, hmA⟩
      dsimp [Blocks.get]; flk_unmdata; flk_to_group
      refine wp_join_group (ts := [i64]) LuckyRet ?_ ?_
      · rintro JsB ⟨rB, ⟨⟩⟩ mB ⟨srB, hlenB, hrB, hflB, hunsB, h02B, h10B, hmB⟩
        dsimp [Blocks.get]; flk_unmdata; flk_to_group
        refine wp_join_group (ts := [i64]) LuckyRet ?_ ?_
        · rintro JsC ⟨rC, ⟨⟩⟩ mC ⟨srC, hlenC, hrC, hflC, hunsC, h02C, h10C, hmC⟩
          dsimp [Blocks.get]; flk_unmdata; (try simp only [bv64_520]); flk_steps
          let s' : FullState := { srC with core := { srC.core with probing := 0#64 } }
          exact hQ rC s' _ (lengthsOk_with_probing hlenC 0#64) hrC hflC rfl hunsC
            (fun h => let ⟨hsp_c, hcl_c⟩ := h02C h; ⟨FullSparseInv.with_probing hsp_c 0#64, hcl_c⟩)
            (fun h => h10C h) (by assumption)
        · intro JsC hJsC
          flk_unmdata; flk_to_group
          · have hrB0 : rB = 0#64 := by assumption
            obtain ⟨hspB, hcl0B⟩ := h02B (Or.inl hrB0)
            c0_call hScan
            refine ⟨c, F0, srB, R, rfl, hspB, hcl0B, hmB, ?_⟩
            intro r4 s4 m4 hlen4 hr4 hfl4 huns4 h02_4 h10_4 hm4
            flk_steps
            exact hJsC _ m4 ⟨s4, hlen4, hr4, Nat.le_trans hfl4 hflB, huns4, h02_4, h10_4, hm4⟩
          · flk_steps
            exact hJsC _ mB ⟨srB, hlenB, hrB, hflB, hunsB, h02B, h10B, hmB⟩
      · intro JsB hJsB
        flk_unmdata; flk_to_group
        · have hrA0 : rA = 0#64 := by assumption
          obtain ⟨hspA, hcl0A⟩ := h02A (Or.inl hrA0)
          c0_call hScan
          refine ⟨c, F0, srA, R, rfl, hspA, hcl0A, hmA, ?_⟩
          intro r3 s3 m3 hlen3 hr3 hfl3 huns3 h02_3 h10_3 hm3
          flk_steps
          exact hJsB _ m3 ⟨s3, hlen3, hr3, Nat.le_trans hfl3 hflA, huns3, h02_3, h10_3, hm3⟩
        · flk_steps
          exact hJsB _ mA ⟨srA, hlenA, hrA, hflA, hunsA, h02A, h10A, hmA⟩
    · intro JsA hJsA
      flk_unmdata; flk_to_group
      · have hr10 : r1 = 0#64 := by assumption
        obtain ⟨hsp1, hcl01⟩ := h02_1 (Or.inl hr10)
        c0_call hScan
        refine ⟨c, F0, s1, R, rfl, hsp1, hcl01, hm1, ?_⟩
        intro r2 s2 m2 hlen2 hr2 hfl2 huns2 h02_2 h10_2 hm2
        flk_steps
        exact hJsA _ m2 ⟨s2, hlen2, hr2, Nat.le_trans hfl2 hfl1, huns2, h02_2, h10_2, hm2⟩
      · flk_steps
        exact hJsA _ m1 ⟨s1, hlen1, hr1, hfl1, huns1, h02_1, h10_1, hm1⟩

end LeanQbe.T.Examples.Kissat.Full
