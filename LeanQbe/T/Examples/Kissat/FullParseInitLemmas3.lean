module

public import LeanQbe.T.Examples.Kissat.FullParseInitLemmas1
import LeanQbe.T.Examples.Kissat.FullParseInitLemmas2
import all Kraken.Separation

/-!
# Kissat `D-Full` Array Peeling, Table Zeroing & `full_init_state` Proofs (Part 3, `Stage 4`)

Proves parametric `(Γ : Env)` `Func.wp` theorems for the remaining `3` `Full1.lean` init functions:
1. `full_zero_tables1_wp` (literal/watch/Tarjan/min_stk/glue_used/last_learned zeroing)
2. `full_zero_tables2_wp` (per-variable mark/phase/flag/heap/queue/score/frame zeroing)
3. `full_avail_to_arrays` & `full_init_state_wp` (full DIMACS header parse + arena split +
   `FullSparseInv c (shiftDownCnf CNF.empty) s`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
  LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test
open FullParseInitSpecs FullParseInitHelpers
open scoped FullArenaTactics FullParseInitTactics

private theorem fp3_sext1_mod64 : ((1 : BitVec 32).signExtend 64).toNat % 64 = 1 := rfl
private theorem fp3_sext2_mod64 : ((2 : BitVec 32).signExtend 64).toNat % 64 = 2 := rfl
attribute [local bv_c0] fp3_sext1_mod64 fp3_sext2_mod64

local macro "fp_ult_t" h:ident : tactic => `(tactic|
  (simp only [i64, Ty.hasFloat, liftCmp, CmpOp.evalBits, evalBits_ult_eq, evalBits_ule_eq,
     evalBits_ugt_eq, evalBits_uge_eq, Arg.val_var, Arg.val_imm, BitVec.ult,
     BitVec.ule] at $h:ident
   have $h:ident := of_decide_eq_true $h:ident))
local macro "fp_ult_f" h:ident : tactic => `(tactic|
  (simp only [i64, Ty.hasFloat, liftCmp, CmpOp.evalBits, evalBits_ult_eq, evalBits_ule_eq,
     evalBits_ugt_eq, evalBits_uge_eq, Arg.val_var, Arg.val_imm, BitVec.ult,
     BitVec.ule] at $h:ident
   have $h:ident := of_decide_eq_false $h:ident))

local macro "fp_jnz_t" h:ident : tactic => `(tactic|
  (simp only [Arg.val_var, i64, Ty.hasFloat, liftCmp, CmpOp.evalBits, evalBits_ult_eq,
     evalBits_ule_eq, evalBits_ugt_eq, evalBits_uge_eq] at $h:ident
   have $h:ident := of_decide_eq_true $h:ident
   fp_head_steps))
local macro "fp_jnz_f" h:ident : tactic => `(tactic|
  (simp only [Arg.val_var, i64, Ty.hasFloat, liftCmp, CmpOp.evalBits, evalBits_ult_eq,
     evalBits_ule_eq, evalBits_ugt_eq, evalBits_uge_eq] at $h:ident
   have $h:ident := of_decide_eq_false $h:ident
   fp_head_steps))

/-! ## 1. `full_zero_tables1_wp` -/

theorem full_zero_tables1_wp (Γ : Env) :
    ∀ a m Q X, fullZeroTables1Spec a m Q X → Func.wp Γ full_zero_tables1_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hc := hlen.core_ok; have hs := hlen.scratch_ok
  have hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  have hmd : c.minDepth ≤ 1000 := fullMinDepthOf_le c.max_vars
  unfold dimacsBound at hmx
  have hnlits : (BitVec.ofNat 64 c.max_vars <<<
      (((1 : BitVec 32).signExtend 64).toNat % 64)).toNat = 2 * c.max_vars :=
    bv64_shl1_eq_2mul (by omega)
  have hmcnt : (BitVec.ofNat 64 c.minDepth <<<
      (((1 : BitVec 32).signExtend 64).toNat % 64)).toNat = 2 * c.minDepth :=
    bv64_shl1_eq_2mul (by omega)
  unfold Func.wp full_zero_tables1_body
  fp_head_steps
  refine wp_loop_inv
    (fun (i_v : Tup Val [i64]) ml => ∃ st : FullState, i_v.1.toNat ≤ 2 * c.max_vars ∧
      st = { s with
        core := { s.core with
          vals := st.core.vals, lit_mark := st.core.lit_mark,
          wvec := st.core.wvec, repr := st.core.repr },
        scratch := { s.scratch with
          walk_vals := st.scratch.walk_vals, tarjan_mark := st.scratch.tarjan_mark,
          tarjan_reach := st.scratch.tarjan_reach } } ∧
      st.core.vals.length = 2 * c.max_vars ∧ st.core.lit_mark.length = 2 * c.max_vars ∧
      st.core.wvec.length = 4 * c.max_vars ∧ st.core.repr.length = 2 * c.max_vars ∧
      st.scratch.walk_vals.length = 2 * c.max_vars ∧
      st.scratch.tarjan_mark.length = 2 * c.max_vars ∧
      st.scratch.tarjan_reach.length = 2 * c.max_vars ∧
      (∀ j < i_v.1.toNat, st.core.vals[j]? = some 0#8 ∧ st.core.lit_mark[j]? = some 0#8 ∧
        st.core.wvec[2 * j]? = some 0#32 ∧ st.core.wvec[2 * j + 1]? = some 0#32) ∧
      (FullMem c st ⋆ R) ml)
    (fun i_v _ => 2 * c.max_vars - i_v.1.toNat) ?_ ?_
  · intro L1 hL1; fp_head_steps
    exact hL1 (0#64, ()) m ⟨s, Nat.zero_le _, rfl, hc.vals_len, hc.lit_mark_len, hc.wvec_len,
      hc.repr_len, hs.walk_vals_len, hs.tarjan_mark_len, hs.tarjan_reach_len,
      (fun _ h0 => by cases h0), hm⟩
  · intro L1 ⟨i_v, ⟨⟩⟩ ml ⟨st, hle, hag, hvl, hlm, hwv, hrp, hwv_s, htm, htr, hall, hm⟩ hL1
    dsimp only at hle hall
    fp_head_steps
    refine wp_jnz_of (fun hilt => ?_) (fun hige => ?_)
    · fp_ult_t hilt; rw [hnlits] at hilt
      have hilt' : i_v.toNat < 2 * c.max_vars := hilt
      have hi1 : (i_v + 1#64).toNat = i_v.toNat + 1 := by
        simp only [bv_c0, Nat.reducePow]; omega
      have hshl : (i_v <<< (((1 : BitVec 32).signExtend 64).toNat % 64)).toNat = 2 * i_v.toNat := by
        simp only [fp3_sext1_mod64, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
        rw [Nat.mul_comm, Nat.mod_eq_of_lt (by omega)]
      have hshl1 : (i_v <<< (((1 : BitVec 32).signExtend 64).toNat % 64) + (1 : BitVec 64)).toNat =
          2 * i_v.toNat + 1 := by
        simp only [BitVec.toNat_add, hshl, show (1 : BitVec 64).toNat = 1 from rfl]
        omega
      fp_head_steps
      refine hL1 (i_v + 1#64, ()) m (by dsimp only; rw [hi1]; omega)
        ⟨_, by dsimp only; rw [hi1]; omega, congrArg (fun x =>
          { x with
            core := { x.core with
              vals := st.core.vals.set i_v.toNat 0#8,
              lit_mark := st.core.lit_mark.set i_v.toNat 0#8,
              wvec := (st.core.wvec.set (2 * i_v.toNat) 0#32).set (2 * i_v.toNat + 1) 0#32,
              repr := st.core.repr.set i_v.toNat (i_v.setWidth 32) },
            scratch := { x.scratch with
              walk_vals := st.scratch.walk_vals.set i_v.toNat 0#8,
              tarjan_mark := st.scratch.tarjan_mark.set i_v.toNat 0#32,
              tarjan_reach := st.scratch.tarjan_reach.set i_v.toNat 0#32 } }) hag,
          by simp [hvl], by simp [hlm], by simp [hwv], by simp [hrp], by simp [hwv_s],
          by simp [htm], by simp [htr], fun j hj => ?_, ?_⟩
      · dsimp only at hj; rw [hi1] at hj
        by_cases hje : j = i_v.toNat
        · subst hje
          exact ⟨List.getElem?_set_self (by omega), List.getElem?_set_self (by omega),
            by rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)],
            List.getElem?_set_self (by rw [List.length_set, hwv]; omega)⟩
        · obtain ⟨ha1, ha2, ha3, ha4⟩ := hall j (by omega)
          rw [List.getElem?_set_ne (Ne.symm hje), List.getElem?_set_ne (Ne.symm hje),
            List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
            List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
          exact ⟨ha1, ha2, ha3, ha4⟩
      · rw [hshl, hshl1] at hm; exact hm
    · fp_ult_f hige; rw [hnlits] at hige
      have hieq : i_v.toNat = 2 * c.max_vars := by omega
      rw [hieq] at hall
      let s1 : FullState :=
        { s with
          core := { s.core with
            vals := List.replicate (2 * c.max_vars) 0#8,
            lit_mark := List.replicate (2 * c.max_vars) 0#8,
            wvec := List.replicate (4 * c.max_vars) 0#32,
            repr := st.core.repr },
          scratch := { s.scratch with
            walk_vals := st.scratch.walk_vals, tarjan_mark := st.scratch.tarjan_mark,
            tarjan_reach := st.scratch.tarjan_reach } }
      have hwv_eq : st.core.wvec = List.replicate (4 * c.max_vars) 0#32 := by
        simpa [show 2 * (2 * c.max_vars) = 4 * c.max_vars by omega] using
          wvec_eq_replicate_of_pairs (n := 2 * c.max_vars) (by omega)
            (fun j hj => (hall j hj).2.2)
      have hs1_eq : st = s1 := by
        rw [hag, list_eq_replicate_of_forall hvl (fun j hj => (hall j hj).1),
          list_eq_replicate_of_forall hlm (fun j hj => (hall j hj).2.1), hwv_eq]
      rw [hs1_eq] at hm
      fp_head_steps
      refine wp_join_group
        (fun (_ : Tup Val []) mw => ∃ wstk' : List (BitVec 32), wstk'.length = c.wcap ∧
          (FullMem c { s1 with core := { s1.core with wstk := wstk' } } ⋆ R) mw) ?_ ?_
      · rintro _ ⟨⟩ mw ⟨wstk', hwstk', hmw⟩
        simp only [Blocks.get_here]
        let s2 : FullState := { s1 with core := { s1.core with wstk := wstk' } }
        fp_head_steps
        refine wp_loop_inv
          (fun (k_v : Tup Val [i64]) ml2 => ∃ mstk' : List (BitVec 32),
            k_v.1.toNat ≤ 2 * c.minDepth ∧ mstk'.length = 2 * c.minDepth ∧
            (FullMem c { s2 with core := { s2.core with min_stk := mstk' } } ⋆ R) ml2)
          (fun k_v _ => 2 * c.minDepth - k_v.1.toNat) ?_ ?_
        · intro L2 hL2; fp_head_steps
          exact hL2 (0#64, ()) mw ⟨s2.core.min_stk, Nat.zero_le _, hc.min_stk_len, hmw⟩
        · intro L2 ⟨k_v, ⟨⟩⟩ ml2 ⟨mstk', hk_le, hmstl, hm2⟩ hL2
          dsimp only at hk_le
          fp_head_steps
          refine wp_jnz_of (fun hklt => ?_) (fun hkge => ?_)
          · fp_ult_t hklt; rw [hmcnt] at hklt
            have hklt' : k_v.toNat < 2 * c.minDepth := hklt
            have hk1 : (k_v + 1#64).toNat = k_v.toNat + 1 := by
              simp only [bv_c0, Nat.reducePow]; omega
            fp_head_steps
            exact hL2 (k_v + 1#64, ()) m (by dsimp only; rw [hk1]; omega)
              ⟨mstk'.set k_v.toNat 0#32, by dsimp only; rw [hk1]; omega, by simp [hmstl], hm⟩
          · fp_head_steps
            refine wp_loop_inv
              (fun (k3 : Tup Val [i64]) ml3 => ∃ gu' : List (BitVec 32),
                k3.1.toNat ≤ 64 ∧ gu'.length = 64 ∧
                (FullMem c { s2 with
                  core := { s2.core with min_stk := mstk' },
                  scratch := { s2.scratch with glue_used := gu' } } ⋆ R) ml3)
              (fun k3 _ => 64 - k3.1.toNat) ?_ ?_
            · intro L3 hL3; fp_head_steps
              exact hL3 (0#64, ()) ml2 ⟨s2.scratch.glue_used, Nat.zero_le _, hs.glue_used_len, hm2⟩
            · intro L3 ⟨k3, ⟨⟩⟩ ml3 ⟨gu', hk3_le, hgul, hm3⟩ hL3
              dsimp only at hk3_le
              fp_head_steps
              refine wp_jnz_of (fun hk3lt => ?_) (fun hk3ge => ?_)
              · fp_ult_t hk3lt
                have hk3lt' : k3.toNat < 64 := by simpa using hk3lt
                have hk31 : (k3 + 1#64).toNat = k3.toNat + 1 := by
                  simp only [bv_c0, Nat.reducePow]; omega
                fp_head_steps
                exact hL3 (k3 + 1#64, ()) m (by dsimp only; rw [hk31]; omega)
                  ⟨gu'.set k3.toNat 0#32, by dsimp only; rw [hk31]; omega, by simp [hgul], hm⟩
              · fp_head_steps
                refine wp_loop_inv
                  (fun (k4 : Tup Val [i64]) ml4 => ∃ ll' : List (BitVec 32),
                    k4.1.toNat ≤ 16 ∧ ll'.length = 16 ∧
                    (∀ j < k4.1.toNat, ll'[j]? = some 0xFFFFFFFF#32) ∧
                    (FullMem c { s2 with
                      core := { s2.core with min_stk := mstk' },
                      scratch := { s2.scratch with glue_used := gu', last_learned := ll' } } ⋆ R)
                      ml4)
                  (fun k4 _ => 16 - k4.1.toNat) ?_ ?_
                · intro L4 hL4; fp_head_steps
                  exact hL4 (0#64, ()) ml3
                    ⟨s2.scratch.last_learned, Nat.zero_le _, hs.last_learned_len,
                      (fun _ h0 => by cases h0), hm3⟩
                · intro L4 ⟨k4, ⟨⟩⟩ ml4 ⟨ll', hk4_le, hlll, hall4, hm4⟩ hL4
                  dsimp only at hk4_le hall4
                  fp_head_steps
                  refine wp_jnz_of (fun hk4lt => ?_) (fun hk4ge => ?_)
                  · fp_ult_t hk4lt
                    have hk4lt' : k4.toNat < 16 := by simpa using hk4lt
                    have hk41 : (k4 + 1#64).toNat = k4.toNat + 1 := by
                      simp only [bv_c0, Nat.reducePow]; omega
                    fp_head_steps
                    refine hL4 (k4 + 1#64, ()) m (by dsimp only; rw [hk41]; omega)
                      ⟨ll'.set k4.toNat 0xFFFFFFFF#32, by dsimp only; rw [hk41]; omega,
                        by simp [hlll], fun j hj => ?_, hm⟩
                    dsimp only at hj; rw [hk41] at hj
                    by_cases hje : j = k4.toNat
                    · subst hje; exact List.getElem?_set_self (by omega)
                    · rw [List.getElem?_set_ne (Ne.symm hje)]; exact hall4 j (by omega)
                  · fp_ult_f hk4ge
                    have hk4eq : k4.toNat = 16 := by simp at hk4ge; omega
                    rw [hk4eq] at hall4
                    fp_head_steps
                    let sc' : FullScratch := { s1.scratch with
                      glue_used := gu', last_learned := ll' }
                    have hsc' : sc'.LengthsOk c :=
                      { hs with
                        walk_vals_len := hwv_s, tarjan_mark_len := htm,
                        tarjan_reach_len := htr, glue_used_len := hgul,
                        last_learned_len := hlll }
                    exact hQ wstk' mstk' st.core.repr sc' ml4 hwstk' hmstl hrp hsc' rfl
                      (last_learned_getD_eq hall4) hm4
      · intro Jw hJw; fp_head_steps
        refine wp_jnz_of (fun hwpos => ?_) (fun hwz => ?_)
        · fp_ult_t hwpos
          have hwc : c.wcap < 2 * 2 ^ 28 := c.hwcap
          have hwpos' : 0 < s1.core.wstk.length := by
            dsimp only [s1]; rw [hc.wstk_len_arr]
            rw [show (BitVec.toNat 0 : Nat) = 0 from rfl, bv64_ofNat_toNat (by omega)] at hwpos
            exact hwpos
          fp_head_steps
          exact hJw () m ⟨_, by rw [List.length_set]; exact hc.wstk_len_arr, hm⟩
        · fp_head_steps
          exact hJw () ml ⟨s1.core.wstk, hc.wstk_len_arr, hm⟩

/-! ## 2. `full_zero_tables2_wp` -/

private theorem bv64_add1_toNat {v : BitVec 64} {n : Nat} (hv : v.toNat < n) (hn : n < 2 ^ 64) :
    (v + 1#64).toNat = v.toNat + 1 := by
  simp only [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl]; omega

@[irreducible] private def Zt2CorePres (s st : FullState) : Prop :=
  st.core = { s.core with
    mrk := st.core.mrk, flags := st.core.flags, lvl := st.core.lvl, rsns := st.core.rsns,
    frame_trail := st.core.frame_trail, frame_dec := st.core.frame_dec }

private def Zt2LoopInv (c : FullCfg) (s st : FullState) (n : Nat) : Prop :=
  n ≤ c.max_vars ∧
  Zt2CorePres s st ∧
  st.LengthsOk c ∧
  FullExtScratchPres s st ∧
  ∀ j < n, st.core.mrk[j]? = some 0#8 ∧ st.core.lvl[j]? = some 0#32 ∧
    st.core.rsns[j]? = some 0xFFFFFFFF#32 ∧ st.core.frame_trail[j]? = some 0#32

private theorem zt2_step_ok {c : FullCfg} {s st : FullState} {v : Nat}
    (hv : v < c.max_vars) (hinv : Zt2LoopInv c s st v)
    (flags' heap' pos' qp' qn' qs' : List (BitVec 32))
    (ph' ptgt' pbst' wbst' : List (BitVec 8)) (sc' sig' : List (BitVec 64))
    (hfl : flags'.length = c.max_vars) (hhp : heap'.length = c.max_vars)
    (hps : pos'.length = c.max_vars) (hqp : qp'.length = c.max_vars)
    (hqn : qn'.length = c.max_vars) (hqs : qs'.length = c.max_vars)
    (hph : ph'.length = c.max_vars) (hpt : ptgt'.length = c.max_vars)
    (hpb : pbst'.length = c.max_vars) (hwb : wbst'.length = c.max_vars)
    (hsc : sc'.length = c.max_vars) (hsig : sig'.length = c.max_vars) :
    let st' : FullState :=
      { core := { st.core with
          mrk := st.core.mrk.set v 0#8, flags := flags',
          lvl := st.core.lvl.set v 0#32, rsns := st.core.rsns.set v 0xFFFFFFFF#32,
          frame_trail := st.core.frame_trail.set v 0#32,
          frame_dec := st.core.frame_dec.set v 0xFFFFFFFF#32 },
        scratch := { st.scratch with
          phases := ph', phases_target := ptgt', phases_best := pbst', walk_best := wbst',
          heap := heap', pos := pos', q_prev := qp', q_next := qn', q_stamp := qs',
          score := sc', sim_sig := sig' } }
    Zt2LoopInv c s st' (v + 1) := by
  intro st'
  obtain ⟨_, hag, hlok, hpres, hall⟩ := hinv
  unfold Zt2CorePres at hag
  have hc := hlok.core_ok; have hs := hlok.scratch_ok
  refine ⟨by omega, ?_,
    ⟨{ hc with
        mrk_len := by simp [st', hc.mrk_len], flags_len := hfl,
        lvl_len := by simp [st', hc.lvl_len], rsns_len := by simp [st', hc.rsns_len],
        frame_trail_len := by simp [st', hc.frame_trail_len],
        frame_dec_len := by simp [st', hc.frame_dec_len] },
     { hs with
        phases_len := hph, phases_target_len := hpt, phases_best_len := hpb,
        walk_best_len := hwb, heap_len_arr := hhp, pos_len := hps, q_prev_len := hqp,
        q_next_len := hqn, q_stamp_len := hqs, score_len := hsc, sim_sig_len := hsig }⟩,
    hpres, fun j hj => ?_⟩
  · unfold Zt2CorePres
    exact congrArg (fun x =>
      { x with
        mrk := st'.core.mrk, flags := st'.core.flags, lvl := st'.core.lvl,
        rsns := st'.core.rsns, frame_trail := st'.core.frame_trail,
        frame_dec := st'.core.frame_dec }) hag
  by_cases hje : j = v
  · subst hje
    exact ⟨List.getElem?_set_self (by rw [hc.mrk_len]; exact hv),
      List.getElem?_set_self (by rw [hc.lvl_len]; exact hv),
      List.getElem?_set_self (by rw [hc.rsns_len]; exact hv),
      List.getElem?_set_self (by rw [hc.frame_trail_len]; omega)⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hall j (by omega)
    simp only [st', List.getElem?_set_ne (Ne.symm hje)]
    exact ⟨h1, h2, h3, h4⟩

@[irreducible] private def Zt2MidPres (c : FullCfg) (st st1 : FullState) (v : Nat) : Prop :=
  st1 = {
    core := { st.core with
      mrk := st.core.mrk.set v 0#8, lvl := st.core.lvl.set v 0#32,
      rsns := st.core.rsns.set v 0xFFFFFFFF#32,
      frame_trail := st.core.frame_trail.set v 0#32,
      frame_dec := st.core.frame_dec.set v 0xFFFFFFFF#32 },
    scratch := { st.scratch with
      phases := st.scratch.phases.set v 1#8,
      phases_target := st.scratch.phases_target.set v 0#8,
      phases_best := st.scratch.phases_best.set v 0#8,
      walk_best := st.scratch.walk_best.set v 1#8,
      score := st.scratch.score.set v 0#64, sim_sig := st.scratch.sim_sig.set v 0#64 } } ∧
  st1.core.flags.length = c.max_vars ∧ st1.scratch.heap.length = c.max_vars ∧
  st1.scratch.pos.length = c.max_vars ∧ st1.scratch.q_prev.length = c.max_vars ∧
  st1.scratch.q_next.length = c.max_vars ∧ st1.scratch.q_stamp.length = c.max_vars

private theorem zt2_finish_ok {c : FullCfg} {s st st1 : FullState} {v : Nat}
    (hv : v < c.max_vars) (hinv : Zt2LoopInv c s st v) (hmid : Zt2MidPres c st st1 v)
    (flags' heap' pos' qp' qn' qs' : List (BitVec 32))
    (hfl : flags'.length = c.max_vars) (hhp : heap'.length = c.max_vars)
    (hps : pos'.length = c.max_vars) (hqp : qp'.length = c.max_vars)
    (hqn : qn'.length = c.max_vars) (hqs : qs'.length = c.max_vars) :
    let st' : FullState :=
      { core := { st1.core with flags := flags' },
        scratch := { st1.scratch with
          heap := heap', pos := pos', q_prev := qp', q_next := qn', q_stamp := qs' } }
    Zt2LoopInv c s st' (v + 1) := by
  intro st'
  have hc := hinv.2.2.1.core_ok; have hs := hinv.2.2.1.scratch_ok
  have hm := hmid; unfold Zt2MidPres at hm
  have hbase := zt2_step_ok hv hinv flags' heap' pos' qp' qn' qs'
    (st.scratch.phases.set v 1#8) (st.scratch.phases_target.set v 0#8)
    (st.scratch.phases_best.set v 0#8) (st.scratch.walk_best.set v 1#8)
    (st.scratch.score.set v 0#64) (st.scratch.sim_sig.set v 0#64)
    hfl hhp hps hqp hqn hqs
    (by rw [List.length_set]; exact hs.phases_len)
    (by rw [List.length_set]; exact hs.phases_target_len)
    (by rw [List.length_set]; exact hs.phases_best_len)
    (by rw [List.length_set]; exact hs.walk_best_len)
    (by rw [List.length_set]; exact hs.score_len)
    (by rw [List.length_set]; exact hs.sim_sig_len)
  dsimp only [st']; rw [hm.1]; exact hbase

private theorem zt2_if_lt_mv_wp (Γ : Env) {c : FullCfg} {st1 : FullState}
    {v_v mv : Val i64} {m : Mem 64} {Q : Post []} {X : XPost} {R : Mem 64 → Prop}
    {Jif : Cont []}
    (hfl1 : st1.core.flags.length = c.max_vars) (hhp1 : st1.scratch.heap.length = c.max_vars)
    (hps1 : st1.scratch.pos.length = c.max_vars) (hqp1 : st1.scratch.q_prev.length = c.max_vars)
    (hqn1 : st1.scratch.q_next.length = c.max_vars)
    (hqs1 : st1.scratch.q_stamp.length = c.max_vars)
    (hvv : v_v.toNat < c.max_vars) (hm1 : (FullMem c st1 ⋆ R) m)
    (hJif : ∀ flags' heap' pos' qp' qn' qs' m',
      flags'.length = c.max_vars → heap'.length = c.max_vars → pos'.length = c.max_vars →
      qp'.length = c.max_vars → qn'.length = c.max_vars → qs'.length = c.max_vars →
      (FullMem c
        ({ core := { st1.core with flags := flags' },
           scratch := { st1.scratch with
             heap := heap', pos := pos', q_prev := qp', q_next := qn', q_stamp := qs' } } :
          FullState) ⋆ R) m' → Jif () m') :
    let e_qn (addr : Val i64) : Expr Val Cont [] :=
      Expr.group (sig := [[i32]])
        (fun _Js => Blocks.cons (fun p_6 =>
          Expr.store (Arg.var p_6.fst) (Arg.var addr) (Expr.jump Jif ())) Blocks.nil)
        (fun Js =>
          Expr.let_ (Op.mk (.add i64) (Arg.var v_v, Arg.imm 1, ())) fun p =>
          Expr.let_ (Op.mk (.cmp .uge i64 Ty.bool rfl) (Arg.var p.fst, Arg.var mv, ())) fun p =>
          Expr.jnz (Arg.var p.fst) (Expr.jump Js.fst (Arg.imm (t := i32) 4294967295, ()))
            (Expr.let_ (Op.mk (.add i64) (Arg.var v_v, Arg.imm 1, ())) fun p =>
             Expr.let_ (Op.mk (.trunc 64 32) (Arg.var p.fst, ())) fun p =>
             Expr.jump Js.fst (Arg.var p.fst, ())))
    let e_qp (addr : Val i64) : Expr Val Cont [] :=
      Expr.group (sig := [[i32]])
        (fun _Js => Blocks.cons (fun p_5 =>
          Expr.store (Arg.var p_5.fst) (Arg.var addr)
            (Expr.let_ (Op.mk (.mul i64) (Arg.var v_v, Arg.imm 4, ())) fun p =>
             Expr.let_ (Op.mk (.add i64) (Arg.var c.pQNext, Arg.var p.fst, ())) fun p =>
             e_qn p.fst)) Blocks.nil)
        (fun Js =>
          Expr.let_ (Op.mk (.cmp .eq i64 Ty.bool rfl) (Arg.var v_v, Arg.imm 0, ())) fun p =>
          Expr.jnz (Arg.var p.fst) (Expr.jump Js.fst (Arg.imm (t := i32) 4294967295, ()))
            (Expr.let_ (Op.mk (.sub i64) (Arg.var v_v, Arg.imm 1, ())) fun p =>
             Expr.let_ (Op.mk (.trunc 64 32) (Arg.var p.fst, ())) fun p =>
             Expr.jump Js.fst (Arg.var p.fst, ())))
    wp Γ Q X
      (Expr.let_ (Op.mk (.mul i64) (Arg.var v_v, Arg.imm 4, ())) fun p =>
       Expr.let_ (Op.mk (.add i64) (Arg.var c.pFlags, Arg.var p.fst, ())) fun p =>
       Expr.store (Arg.imm (t := i32) 2041) (Arg.var p.fst)
         (Expr.let_ (Op.mk (.mul i64) (Arg.var v_v, Arg.imm 4, ())) fun p =>
          Expr.let_ (Op.mk (.add i64) (Arg.var c.pHeap, Arg.var p.fst, ())) fun p =>
          Expr.let_ (Op.mk (.trunc 64 32) (Arg.var v_v, ())) fun p_1 =>
          Expr.store (Arg.var p_1.fst) (Arg.var p.fst)
            (Expr.let_ (Op.mk (.mul i64) (Arg.var v_v, Arg.imm 4, ())) fun p =>
             Expr.let_ (Op.mk (.add i64) (Arg.var c.pPos, Arg.var p.fst, ())) fun p =>
             Expr.let_ (Op.mk (.trunc 64 32) (Arg.var v_v, ())) fun p_2 =>
             Expr.store (Arg.var p_2.fst) (Arg.var p.fst)
               (Expr.let_ (Op.mk (.mul i64) (Arg.var v_v, Arg.imm 4, ())) fun p =>
                Expr.let_ (Op.mk (.add i64) (Arg.var c.pQStamp, Arg.var p.fst, ())) fun p =>
                Expr.let_ (Op.mk (.add i64) (Arg.var v_v, Arg.imm 1, ())) fun p_3 =>
                Expr.let_ (Op.mk (.trunc 64 32) (Arg.var p_3.fst, ())) fun p_4 =>
                Expr.store (Arg.var p_4.fst) (Arg.var p.fst)
                  (Expr.let_ (Op.mk (.mul i64) (Arg.var v_v, Arg.imm 4, ())) fun p =>
                   Expr.let_ (Op.mk (.add i64) (Arg.var c.pQPrev, Arg.var p.fst, ())) fun p =>
                   e_qp p.fst))))) m := by
  intro e_qn e_qp; fp_head_steps
  refine wp_join_group (fun (vq : Tup Val [i32]) mq => mq = m) ?_ ?_
  · rintro _ ⟨qp_val, ⟨⟩⟩ mq rfl; simp only [Blocks.get_here]; fp_head_steps
    refine wp_join_group (fun (vn : Tup Val [i32]) mn => mn = m) ?_ ?_
    · rintro _ ⟨qn_val, ⟨⟩⟩ mn rfl; simp only [Blocks.get_here]; fp_head_steps
      exact hJif _ _ _ _ _ _ m (by rw [List.length_set]; exact hfl1)
        (by rw [List.length_set]; exact hhp1) (by rw [List.length_set]; exact hps1)
        (by rw [List.length_set]; exact hqp1) (by rw [List.length_set]; exact hqn1)
        (by rw [List.length_set]; exact hqs1) hm
    · intro Jn hJn; fp_head_steps
      refine wp_jnz_of (fun _ => ?_) (fun _ => ?_) <;> (fp_head_steps; exact hJn (_, ()) m rfl)
  · intro Jp hJp; fp_head_steps
    refine wp_jnz_of (fun _ => ?_) (fun _ => ?_) <;> (fp_head_steps; exact hJp (_, ()) m rfl)

private theorem zt2_else_ge_mv_wp (Γ : Env) {c : FullCfg} {st1 : FullState}
    {v_v : Val i64} {m : Mem 64} {Q : Post []} {X : XPost} {R : Mem 64 → Prop} {Jif : Cont []}
    (hfl1 : st1.core.flags.length = c.max_vars) (hhp1 : st1.scratch.heap.length = c.max_vars)
    (hps1 : st1.scratch.pos.length = c.max_vars) (hqp1 : st1.scratch.q_prev.length = c.max_vars)
    (hqn1 : st1.scratch.q_next.length = c.max_vars)
    (hqs1 : st1.scratch.q_stamp.length = c.max_vars)
    (hvv : v_v.toNat < c.max_vars) (hm1 : (FullMem c st1 ⋆ R) m)
    (hJif : ∀ flags' heap' pos' qp' qn' qs' m',
      flags'.length = c.max_vars → heap'.length = c.max_vars → pos'.length = c.max_vars →
      qp'.length = c.max_vars → qn'.length = c.max_vars → qs'.length = c.max_vars →
      (FullMem c
        ({ core := { st1.core with flags := flags' },
           scratch := { st1.scratch with
             heap := heap', pos := pos', q_prev := qp', q_next := qn', q_stamp := qs' } } :
          FullState) ⋆ R) m' → Jif () m') :
    wp Γ Q X
      (Expr.let_ (Op.mk (.mul i64) (Arg.var v_v, Arg.imm 4, ())) fun p =>
       Expr.let_ (Op.mk (.add i64) (Arg.var c.pFlags, Arg.var p.1, ())) fun p =>
       Expr.store (Arg.imm (t := i32) 0) (Arg.var p.1)
         (Expr.let_ (Op.mk (.mul i64) (Arg.var v_v, Arg.imm 4, ())) fun p =>
          Expr.let_ (Op.mk (.add i64) (Arg.var c.pHeap, Arg.var p.1, ())) fun p =>
          Expr.store (Arg.imm (t := i32) 0) (Arg.var p.1)
            (Expr.let_ (Op.mk (.mul i64) (Arg.var v_v, Arg.imm 4, ())) fun p =>
             Expr.let_ (Op.mk (.add i64) (Arg.var c.pPos, Arg.var p.1, ())) fun p =>
             Expr.store (Arg.imm (t := i32) 4294967295) (Arg.var p.1)
               (Expr.let_ (Op.mk (.mul i64) (Arg.var v_v, Arg.imm 4, ())) fun p =>
                Expr.let_ (Op.mk (.add i64) (Arg.var c.pQPrev, Arg.var p.1, ())) fun p =>
                Expr.store (Arg.imm (t := i32) 4294967295) (Arg.var p.1)
                  (Expr.let_ (Op.mk (.mul i64) (Arg.var v_v, Arg.imm 4, ())) fun p =>
                   Expr.let_ (Op.mk (.add i64) (Arg.var c.pQNext, Arg.var p.1, ())) fun p =>
                   Expr.store (Arg.imm (t := i32) 4294967295) (Arg.var p.1)
                     (Expr.let_ (Op.mk (.mul i64) (Arg.var v_v, Arg.imm 4, ())) fun p =>
                      Expr.let_ (Op.mk (.add i64) (Arg.var c.pQStamp, Arg.var p.1, ())) fun p =>
                      Expr.store (Arg.imm (t := i32) 0) (Arg.var p.1) (Expr.jump Jif ())))))))
      m := by
  fp_head_steps
  exact hJif _ _ _ _ _ _ m (by rw [List.length_set]; exact hfl1)
    (by rw [List.length_set]; exact hhp1) (by rw [List.length_set]; exact hps1)
    (by rw [List.length_set]; exact hqp1) (by rw [List.length_set]; exact hqn1)
    (by rw [List.length_set]; exact hqs1) hm

theorem full_zero_tables2_wp (Γ : Env) :
    ∀ a m Q X, fullZeroTables2Spec a m Q X → Func.wp Γ full_zero_tables2_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hmx : c.max_vars < 2 * dimacsBound := c.hmaxv
  have hmv : c.mv < dimacsBound := c.hmv
  unfold dimacsBound at hmx hmv
  have hmx_to : (BitVec.ofNat 64 c.max_vars).toNat = c.max_vars := bv64_ofNat_toNat (by omega)
  have hmv_to : (BitVec.ofNat 64 c.mv).toNat = c.mv := bv64_ofNat_toNat (by omega)
  unfold Func.wp full_zero_tables2_body
  fp_head_steps
  refine wp_loop_inv
    (fun (v_v : Tup Val [i64]) ml => ∃ st : FullState, Zt2LoopInv c s st v_v.1.toNat ∧
      (FullMem c st ⋆ R) ml)
    (fun v_v _ => c.max_vars - v_v.1.toNat) ?_ ?_
  · intro L hL; fp_head_steps
    refine hL (0#64, ()) m ⟨s, ⟨Nat.zero_le _, ?_, hlen, ⟨rfl, rfl⟩, fun _ h0 => by cases h0⟩, hm⟩
    unfold Zt2CorePres; rfl
  · intro L ⟨v_v, ⟨⟩⟩ ml ⟨st, hinv, hm⟩ hL
    obtain ⟨hv_le, hag, hlok, hpres, hall⟩ := hinv
    dsimp only at hv_le
    have hc := hlok.core_ok; have hs := hlok.scratch_ok
    have hmrk_l : st.core.mrk.length = c.max_vars := hc.mrk_len
    have hlvl_l : st.core.lvl.length = c.max_vars := hc.lvl_len
    have hrsns_l : st.core.rsns.length = c.max_vars := hc.rsns_len
    have hft_l : st.core.frame_trail.length = c.max_vars + 1 := hc.frame_trail_len
    have hfd_l : st.core.frame_dec.length = c.max_vars + 1 := hc.frame_dec_len
    have hph_l : st.scratch.phases.length = c.max_vars := hs.phases_len
    have hpt_l : st.scratch.phases_target.length = c.max_vars := hs.phases_target_len
    have hpb_l : st.scratch.phases_best.length = c.max_vars := hs.phases_best_len
    have hwb_l : st.scratch.walk_best.length = c.max_vars := hs.walk_best_len
    have hsc_l : st.scratch.score.length = c.max_vars := hs.score_len
    have hsg_l : st.scratch.sim_sig.length = c.max_vars := hs.sim_sig_len
    fp_head_steps
    refine wp_jnz_of (fun hvlt => ?_) (fun hvge => ?_)
    · fp_ult_t hvlt; rw [hmx_to] at hvlt
      have hvlt' : v_v.toNat < c.max_vars := hvlt
      have hv1 := bv64_add1_toNat hvlt' (Nat.lt_trans hmx (by decide))
      fp_head_steps
      obtain ⟨st1, hmid, hm1⟩ : ∃ st1 : FullState, Zt2MidPres c st st1 v_v.toNat ∧
          (FullMem c st1 ⋆ R) m :=
        ⟨_, by unfold Zt2MidPres; exact ⟨rfl, hc.flags_len, hs.heap_len_arr, hs.pos_len,
          hs.q_prev_len, hs.q_next_len, hs.q_stamp_len⟩, hm⟩
      clear hm
      have hmid' := hmid; unfold Zt2MidPres at hmid'
      obtain ⟨hm_eq, hfl1, hhp1, hps1, hqp1, hqn1, hqs1⟩ := hmid'
      clear hm_eq
      refine wp_join_group
        (fun (_ : Tup Val []) mc => ∃ st_n : FullState, Zt2LoopInv c s st_n (v_v.toNat + 1) ∧
          (FullMem c st_n ⋆ R) mc) ?_ ?_
      · rintro _ ⟨⟩ mc ⟨st_n, hinv_n, hmc⟩
        simp only [Blocks.get_here]
        fp_head_steps
        exact hL (v_v + 1#64, ()) mc
          (by dsimp only; rw [hv1]; exact Nat.sub_lt_sub_left hvlt' (Nat.lt_succ_self _))
          ⟨st_n, by dsimp only; rw [hv1]; exact hinv_n, hmc⟩
      · intro Jif hJif; fp_head_steps
        refine wp_jnz_of (fun hvmv => ?_) (fun hvge_mv => ?_)
        · simp only [LeanQbe.T.lift2, i32,
            show (1 : BitVec 32) ||| 8 ||| 16 ||| 32 ||| 64 ||| 128 ||| 256 ||| 512 ||| 1024 =
              2041#32 from rfl]
          exact zt2_if_lt_mv_wp Γ hfl1 hhp1 hps1 hqp1 hqn1 hqs1 hvlt' hm1
            fun fl' hp' ps' qp' qn' qs' m' hf hh hps hqp hqn hqs hm' =>
              hJif () m' ⟨_, zt2_finish_ok hvlt' ⟨hv_le, hag, hlok, hpres, hall⟩ hmid
                fl' hp' ps' qp' qn' qs' hf hh hps hqp hqn hqs, hm'⟩
        · exact zt2_else_ge_mv_wp Γ hfl1 hhp1 hps1 hqp1 hqn1 hqs1 hvlt' hm1
            fun fl' hp' ps' qp' qn' qs' m' hf hh hps hqp hqn hqs hm' =>
              hJif () m' ⟨_, zt2_finish_ok hvlt' ⟨hv_le, hag, hlok, hpres, hall⟩ hmid
                fl' hp' ps' qp' qn' qs' hf hh hps hqp hqn hqs, hm'⟩
    · fp_ult_f hvge; rw [hmx_to] at hvge
      have hveq : v_v.toNat = c.max_vars := Nat.le_antisymm hv_le (Nat.not_lt.mp hvge)
      rw [hveq] at hall
      fp_head_steps
      have hmrk : st.core.mrk = List.replicate c.max_vars 0#8 :=
        list_eq_replicate_of_forall hmrk_l fun j hj => (hall j hj).1
      have hlvl : st.core.lvl = List.replicate c.max_vars 0#32 :=
        list_eq_replicate_of_forall hlvl_l fun j hj => (hall j hj).2.1
      have hrsns : st.core.rsns = List.replicate c.max_vars 0xFFFFFFFF#32 :=
        list_eq_replicate_of_forall hrsns_l fun j hj => (hall j hj).2.2.1
      let ftrl' := st.core.frame_trail.set c.max_vars 0#32
      let fdec' := st.core.frame_dec.set c.max_vars 0xFFFFFFFF#32
      have hftrl_len : ftrl'.length = c.max_vars + 1 := by
        dsimp only [ftrl']; rw [List.length_set, hft_l]
      have hfdec_len : fdec'.length = c.max_vars + 1 := by
        dsimp only [fdec']; rw [List.length_set, hfd_l]
      have hftrl : ftrl' = List.replicate (c.max_vars + 1) 0#32 := by
        refine list_eq_replicate_of_forall hftrl_len fun j hj => ?_
        by_cases hje : j = c.max_vars
        · subst hje; exact List.getElem?_set_self (by rw [hft_l]; exact Nat.lt_succ_self _)
        · rw [List.getElem?_set_ne (Ne.symm hje)]
          exact (hall j (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hj) hje)).2.2.2
      have hcore_eq :
          { s.core with
            mrk := List.replicate c.max_vars 0#8, flags := st.core.flags,
            lvl := List.replicate c.max_vars 0#32,
            rsns := List.replicate c.max_vars 0xFFFFFFFF#32,
            frame_trail := List.replicate (c.max_vars + 1) 0#32, frame_dec := fdec' } =
          { st.core with
            frame_trail := st.core.frame_trail.set c.max_vars 0#32,
            frame_dec := st.core.frame_dec.set c.max_vars 0xFFFFFFFF#32 } := by
        unfold Zt2CorePres at hag
        rw [hag, hmrk, hlvl, hrsns, ← hftrl]
      have hm_out : (FullMem c { s with
          core := { s.core with
            mrk := List.replicate c.max_vars 0#8, flags := st.core.flags,
            lvl := List.replicate c.max_vars 0#32, rsns := List.replicate c.max_vars 0xFFFFFFFF#32,
            frame_trail := List.replicate (c.max_vars + 1) 0#32, frame_dec := fdec' },
          scratch := st.scratch } ⋆ R) m := by
        rw [hcore_eq]; dsimp only [ftrl', fdec']; rw [hmx_to] at hm; exact hm
      exact hQ st.core.flags fdec' st.scratch m hc.flags_len hfdec_len hs hpres hm_out

/-! ## 3. Region peeling (`full_avail_to_arrays`) & `full_init_state_wp` -/

private structure FullInitArrs (c : FullCfg) where
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

private def initFullState (c : FullCfg) (d_cur d_val fuel : BitVec 64) (a : FullInitArrs c) :
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

private theorem peel_bytes_block (c : FullCfg) {m : Mem 64}
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
  unfold FullCfg.padBytes
  dsimp only [vb, mb] at h8
  exact sep_mono2 (sep_mono2 (fun _ h => sep_ac h)
    (fun _ h => by simp only [sep_assoc] at h ⊢; exact h)) (fun _ h => h) m h8

private theorem peel_u32_5_block (max_v : Nat) (k1 k2 k3 k4 k5 : Nat)
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
  simp only [emp_sep] at h5
  exact ⟨x1, x2, x3, x4, x5, hx1, hx2, hx3, hx4, hx5, sep_ac h5⟩

private theorem peel_tail_block (c : FullCfg) {m : Mem 64}
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
  simp only [emp_sep] at h18
  exact sep_mono2 (fun _ h => sep_ac h) (fun _ h => h) m h18

private theorem zip_u2 {A1 A2 A3 A4 A5 P : Mem 64 → Prop} {m : Mem 64}
    (h : ((A1 ⋆ A2 ⋆ A3 ⋆ A4 ⋆ A5) ⋆ P) m) :
    (((A1 ⋆ A4) ⋆ (A2 ⋆ A3 ⋆ A5)) ⋆ P) m := sep_ac h

private theorem zip_u3 {A1 A2 A3 A4 A5 P : Mem 64 → Prop} {m : Mem 64}
    (h : ((A1 ⋆ A2 ⋆ A3 ⋆ A4 ⋆ A5) ⋆ P) m) :
    (((A4 ⋆ A5) ⋆ (A1 ⋆ A2 ⋆ A3)) ⋆ P) m := sep_ac h

private theorem zip_tl {W R M A K S SL : Mem 64 → Prop} {m : Mem 64}
    (h : ((W ⋆ R ⋆ M ⋆ A ⋆ K) ⋆ S ⋆ SL) m) :
    ((((W ⋆ R ⋆ M) ⋆ (A ⋆ K)) ⋆ S) ⋆ SL) m := sep_ac h

private theorem zip_avail {CB SB PB U1 PA Uc2 Us2 PB2 Uc3 Us3 PC Tb Dyc S3 SL : Mem 64 → Prop}
    {m : Mem 64}
    (h : (((CB ⋆ SB) ⋆ PB) ⋆ ((U1 ⋆ PA) ⋆ (((Uc2 ⋆ Us2) ⋆ PB2) ⋆
      (((Uc3 ⋆ Us3) ⋆ PC) ⋆ (((Tb ⋆ Dyc) ⋆ S3) ⋆ SL))))) m) :
    ((CB ⋆ (U1 ⋆ Uc2) ⋆ (Uc3 ⋆ Tb) ⋆ Dyc) ⋆ (SB ⋆ (Us2 ⋆ Us3) ⋆ S3) ⋆
      (PB ⋆ PA ⋆ PB2 ⋆ PC ⋆ SL)) m := sep_ac h

private theorem zip_u32a_7 {A1 A2 A3 A4 A5 A6 A7 : Mem 64 → Prop} {m : Mem 64}
    (h : ((A1 ⋆ A2 ⋆ A3 ⋆ A4 ⋆ A5) ⋆ (A6 ⋆ A7)) m) :
    (A1 ⋆ A2 ⋆ A3 ⋆ A4 ⋆ A5 ⋆ A6 ⋆ A7) m := sep_ac h

private theorem zip_u32b_5 {A1 A2 A3 A4 A5 : Mem 64 → Prop} {m : Mem 64}
    (h : ((A1 ⋆ A2) ⋆ (A3 ⋆ A4 ⋆ A5)) m) :
    (A1 ⋆ A2 ⋆ A3 ⋆ A4 ⋆ A5) m := sep_ac h

private theorem zip_scr32a_6 {A1 A2 A3 A4 A5 A6 : Mem 64 → Prop} {m : Mem 64}
    (h : ((A1 ⋆ A2 ⋆ A3) ⋆ (A4 ⋆ A5 ⋆ A6)) m) :
    (A1 ⋆ A2 ⋆ A3 ⋆ A4 ⋆ A5 ⋆ A6) m := sep_ac h

private theorem zip_scr_fold {SB SU S1 S2 S3 : Mem 64 → Prop} {m : Mem 64}
    (h : (SB ⋆ SU ⋆ (S1 ⋆ S2 ⋆ S3)) m) : (SB ⋆ SU ⋆ S1 ⋆ S2 ⋆ S3) m := sep_ac h

private theorem full_avail_to_arrays (c : FullCfg) {m : Mem 64}
    (hm : region (c.hdr + BitVec.ofNat 64 1152) (c.avail - 1152) m) :
    ∃ a : FullInitArrs c, (FullCoreArrays c (initFullState c 0#64 0#64 0#64 a).core ⋆
      FullScratchArrays c (initFullState c 0#64 0#64 0#64 a).scratch ⋆ c.pad) m := by
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
      15 * ub + r15 := by
    dsimp only [r15, ub]; omega
  have h15_264 : 15 * ub + r15 ≤ 2 ^ 64 := by dsimp only [r15]; omega
  have h10_264 : 10 * ub + r15 ≤ 2 ^ 64 := by omega
  have h5_264 : 5 * ub + r15 ≤ 2 ^ 64 := by omega
  have hrem15 : 5 * u32FullBytes c.max_vars + (10 * ub + r15) = 15 * ub + r15 := by
    dsimp only [ub]; omega
  have hrem10 : 5 * u32FullBytes c.max_vars + (5 * ub + r15) = 10 * ub + r15 := by
    dsimp only [ub]; omega
  obtain ⟨vals, wvals, lmrk, mrk, ph, ptgt, pbst, wbst,
    hv1, hv2, hv3, hm1, hm2, hm3, hm4, hm5, m_b, m_u0, hu_b, hd_b, h_b, h_u0⟩ :=
    peel_bytes_block c hm
  rw [hrem0_eq] at h_u0
  obtain ⟨fl, lvl, rsns, trl, tpos, lfl, llv, lrs, ltr, ltp, h_u1⟩ :=
    peel_u32_5_block c.max_vars c.max_vars c.max_vars c.max_vars c.max_vars c.max_vars
      c.pFlags c.pLevel c.pReason c.pTrail c.pTrailPos c.pTmp (rtot := 15 * ub + r15)
      (rnext := 10 * ub + r15) rfl rfl rfl rfl rfl h_u0
      hu4 hu4 hu4 hu4 hu4 hrem15 h15_264
  obtain ⟨m_u1, m_u1r, hu_u1, hd_u1, h_u1a, h_u1r⟩ := h_u1
  obtain ⟨tmp, hp, pos, mclr, shrk, ltmp, lhp, lps, lmc, lsh, h_u2⟩ :=
    peel_u32_5_block c.max_vars c.max_vars c.max_vars c.max_vars c.max_vars c.max_vars
      c.pTmp c.pHeap c.pPos c.pMinClr c.pShrinkStk c.pQPrev (rtot := 10 * ub + r15)
      (rnext := 5 * ub + r15) rfl rfl rfl rfl rfl h_u1r
      hu4 hu4 hu4 hu4 hu4 hrem10 h10_264
  obtain ⟨m_u2, m_u2r, hu_u2, hd_u2, h_u2a, h_u2r⟩ := h_u2
  obtain ⟨qp, qn, qs, ftrl, fdec, lqp, lqn, lqs, lft, lfd, h_u3⟩ :=
    peel_u32_5_block c.max_vars c.max_vars c.max_vars c.max_vars (c.max_vars + 1) (c.max_vars + 1)
      c.pQPrev c.pQNext c.pQStamp c.pFrameTrail c.pFrameDec c.pWvec (rtot := 5 * ub + r15)
      (rnext := r15) rfl rfl rfl rfl rfl h_u2r
      hu4 hu4 hu4 hu hu rfl h5_264
  obtain ⟨m_u3, m_tl, hu_u3, hd_u3, h_u3a, h_tl⟩ := h_u3
  obtain ⟨wvec, repr, wsort, ws1, ws2, tmk, trc, sc, sig, mstk, gu, ll, ar, wstk, del, red,
    ext, sbuf, ⟨lwv, lrp, lws, l1, l2, ltm, ltrc, lsc, lsg, lms, lgu, lll, lar, lwk, ldl, lrd,
      lex, lsb⟩, h_tlp⟩ := peel_tail_block c h_tl
  have hm_comb := sep_push hu_b hd_b h_b (sep_push hu_u1 hd_u1 h_u1a
    (sep_push hu_u2 hd_u2 (zip_u2 h_u2a) (sep_push hu_u3 hd_u3 (zip_u3 h_u3a) (zip_tl h_tlp))))
  let a : FullInitArrs c :=
    ⟨vals, lmrk, mrk, wvals, ph, ptgt, pbst, wbst, fl, lvl, rsns, trl, tpos, tmp, mclr, ftrl,
      fdec, wvec, repr, mstk, ar, wstk, hp, pos, shrk, qp, qn, qs, wsort, ws1, ws2, tmk, trc, sc,
      sig, gu, ll, del, red, ext, sbuf, ⟨hv1, hv3, hm1, hv2, hm2, hm3, hm4, hm5, lfl, llv, lrs,
      ltr, ltp, ltmp, lmc, lft, lfd, lwv, lrp, lms, lar, lwk, lhp, lps, lsh, lqp, lqn, lqs, lws,
      l1, l2, ltm, ltrc, lsc, lsg, lgu, lll, ldl, lrd, lex, lsb⟩⟩
  have h_zip := zip_avail hm_comb
  refine ⟨a, sep_mono2 (sep_mono2 ?_ ?_) ?_ m h_zip⟩
  · intro m1 hm1
    unfold FullCoreArrays
    exact sep_mono2 (sep_mono2 (sep_mono2 (fun _ h => h)
      (fun _ h => zip_u32a_7 h)) (fun _ h => zip_u32b_5 h)) (fun _ h => h) m1 hm1
  · intro m2 hm2
    unfold FullScratchArrays
    refine zip_scr_fold (sep_mono2 (sep_mono2 (fun _ h => h)
      (fun _ h => zip_scr32a_6 h)) (fun _ h => h) m2 hm2)
  · intro m3 hm3
    unfold FullCfg.pad FullCfg.padU32A FullCfg.padU32B FullCfg.padU32C
    exact hm3

private theorem init_hdr_remerge {cnf_ptr hdr_addr : BitVec 64} {avail : Nat}
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

private theorem init_state_fail {cnf_ptr hdr_addr : BitVec 64} {avail : Nat}
    {cnfBytes rest : List UInt8} {mv nc : Nat} {cur' val' : BitVec 64}
    {R : Mem 64 → Prop} {Q : Post [.bool]} {m' : Mem 64} (h32 : 32 ≤ avail) (hle : avail ≤ 2 ^ 64)
    (hhdr : parseHeader cnfBytes = some (mv, nc, rest))
    (hfail : avail < fullFixedBytes mv + nc * 40 + 136)
    (hm' : (bytes cnf_ptr cnfBytes ⋆ dimacsState hdr_addr (BitVec.ofNat 64 mv)
      (BitVec.ofNat 64 nc) cur' val' ⋆ region (hdr_addr + 32#64) (avail - 32) ⋆ R) m')
    (hQfalse : ∀ m'', (bytes cnf_ptr cnfBytes ⋆ region hdr_addr avail ⋆ R) m'' →
      (∀ mv' nc' rest', parseHeader cnfBytes = some (mv', nc', rest') →
        avail < fullFixedBytes mv' + nc' * 40 + 136) → Q (false, ()) m'') : Q (false, ()) m' :=
  hQfalse m' (init_hdr_remerge h32 hle hm') fun _ _ _ h => by
    rw [hhdr] at h; rcases Option.some.inj h with ⟨rfl, rfl, rfl⟩; exact hfail

private theorem init_state_split_tail {hdr_addr : BitVec 64} {avail : Nat}
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
  obtain ⟨m_reg, m_rest, hu_r, hd_r, h_reg, h_rest⟩ :=
    (show (region (hdr_addr + 32#64) (avail - 32) ⋆
      (bytes cnf_ptr cnfBytes ⋆ dimacsState hdr_addr (BitVec.ofNat 64 mv) (BitVec.ofNat 64 nc)
        (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 nc) ⋆ R)) m from sep_ac hm)
  obtain ⟨m_h, m_t, hu_ht, hd_ht, h_h, h_t⟩ := reg_peel (b := hdr_addr + 1152#64) (n1 := 1120)
    (n2 := avail - 1152) h_reg (hb := by rw [BitVec.add_assoc]; rfl)
    (hn := by omega) (hle := by omega)
  obtain ⟨ws, hwl, h_ws⟩ := region_to_array64 140 (by decide) h_h
  have h1 : (hdrTail4 hdr_addr (ws.take 35) ((ws.drop 35).take 35) ((ws.drop 70).take 35)
      ((ws.drop 105).take 35) ⋆ emp) m_h := array64_to_hdrTail4 hwl (by rwa [sep_emp])
  rw [sep_emp] at h1
  exact ⟨ws, hwl, sep_ac (sep_push hu_r hd_r (sep_push hu_ht hd_ht h1 h_t) h_rest)⟩

theorem full_init_state_wp (Γ : Env)
    (hHdr : ∀ a m Q X, kissatParseHeaderSpec a m Q X →
      Γ "kissat_parse_header" [i64, i64, i64] [.bool] a m Q X)
    (hFixed : ∀ a m Q X, fullFixedBytesSpec a m Q X →
      Γ "full_fixed_bytes" [i64] [i64] a m Q X)
    (hMaxV : ∀ a m Q X, fullCalcMaxVSpec a m Q X →
      Γ "full_calc_max_v" [i64, i64, i64, i64] [i64] a m Q X)
    (hExt : ∀ a m Q X, fullCalcExtCapSpec a m Q X →
      Γ "full_calc_ext_cap" [i64] [i64] a m Q X)
    (hScr : ∀ a m Q X, fullCalcScrCapSpec a m Q X →
      Γ "full_calc_scr_cap" [i64] [i64] a m Q X)
    (hArenas : ∀ a m Q X, fullInitArenasSpec a m Q X →
      Γ "full_init_arenas" [i64, i64, i64, i64] [] a m Q X)
    (hInitHdr : ∀ a m Q X, fullInitHdrSpec a m Q X →
      Γ "full_init_hdr" [i64, i64, i64, i64] [] a m Q X)
    (hZt1 : ∀ a m Q X, fullZeroTables1Spec a m Q X → Γ "full_zero_tables1" [i64] [] a m Q X)
    (hZt2 : ∀ a m Q X, fullZeroTables2Spec a m Q X → Γ "full_zero_tables2" [i64] [] a m Q X) :
    ∀ a m Q X, fullInitStateSpec a m Q X → Func.wp Γ full_init_state_body a m Q X := by
  rintro ⟨cnf_ptr, cend, hdr_addr, avail, fuel, ⟨⟩⟩ m Q X
    ⟨cnfBytes, R, rfl, hfit, havel_fit, h1152, hm_in, hQfalse, hQtrue⟩
  have hav_le : avail.toNat ≤ 2 ^ 64 := by omega
  have hm0 : (bytes cnf_ptr cnfBytes ⋆ (region hdr_addr 32 ⋆
      region (hdr_addr + BitVec.ofNat 64 32) (avail.toNat - 32)) ⋆ R) m := by
    rw [region_merge_eq (a := hdr_addr) (n1 := 32) (n2 := avail.toNat - 32) (n := avail.toNat)
      (by omega) hav_le]; exact hm_in
  obtain ⟨m_d, m_o, hu, hd, h_d32, h_o⟩ := (show (region hdr_addr 32 ⋆ (bytes cnf_ptr cnfBytes ⋆
    region (hdr_addr + BitVec.ofNat 64 32) (avail.toNat - 32) ⋆ R)) m from sep_ac hm0)
  obtain ⟨mv0, nc0, cur0, val0, h_dstate⟩ := Kissat.region32_to_dimacsState h_d32
  have hm_pre : (dimacsState hdr_addr mv0 nc0 cur0 val0 ⋆ (bytes cnf_ptr cnfBytes ⋆
      region (hdr_addr + BitVec.ofNat 64 32) (avail.toNat - 32) ⋆ R)) m :=
    ⟨m_d, m_o, hu, hd, h_dstate, h_o⟩
  unfold Func.wp full_init_state_body
  apply wp_call_of_spec; apply hHdr
  change kissatParseHeaderSpec (cnf_ptr, cnf_ptr + BitVec.ofNat 64 cnfBytes.length, hdr_addr, ())
    m _ _
  refine ⟨mv0, nc0, cur0, val0, cnfBytes,
    region (hdr_addr + BitVec.ofNat 64 32) (avail.toNat - 32) ⋆ R, rfl, hfit, sep_ac hm_pre, ?_⟩
  cases hhdr : parseHeader cnfBytes with
  | none =>
    intro _ _ _ _ m' hm'; refine wp_jnz_of (fun hc => by cases hc) (fun _ => ?_)
    rw [wp_ret]; exact hQfalse m' (init_hdr_remerge (by omega) hav_le (sep_ac hm'))
      (fun _ _ _ h => by rw [hhdr] at h; cases h)
  | some p =>
    rcases p with ⟨mv, nc, rest⟩; intro j m0 hmv_bd hnc_bd hj hdrop hm0
    have hmv := hmv_bd; have hnc := hnc_bd; unfold dimacsBound at hmv hnc
    refine wp_jnz_of (fun _ => ?_) (fun hc => by cases hc)
    fp_head_steps
    apply wp_call_of_spec; apply hFixed
    change fullFixedBytesSpec (BitVec.ofNat 64 mv, ()) m0 _ _
    have hmv_to : (BitVec.ofNat 64 mv).toNat = mv := bv64_ofNat_toNat (by omega)
    have hnc_to : (BitVec.ofNat 64 nc).toNat = nc := bv64_ofNat_toNat (by omega)
    refine ⟨by rw [hmv_to]; unfold dimacsBound; omega, ?_⟩
    rw [hmv_to]; have hfx0_lt := fullFixedBytes_lt (max_v := mv) (by unfold dimacsBound; omega)
    have hf0_to : (BitVec.ofNat 64 (fullFixedBytes mv)).toNat = fullFixedBytes mv :=
      bv64_ofNat_toNat (by omega)
    dsimp only
    fp_head_steps
    have hult_f0 : avail.ult (BitVec.ofNat 64 (fullFixedBytes mv)) =
        decide (avail.toNat < fullFixedBytes mv) := by
      rw [BitVec.ult, hf0_to]
    rw [hult_f0]
    refine wp_jnz_of (fun hlt => ?_) (fun hge => ?_)
    · fp_jnz_t hlt
      exact init_state_fail (by omega) hav_le hhdr (by omega) (sep_ac hm0) hQfalse
    · fp_jnz_f hge; fp_head_steps
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
      · fp_jnz_t hlt2
        exact init_state_fail (by omega) hav_le hhdr (by omega) (sep_ac hm0) hQfalse
      · fp_jnz_f hge2
        apply wp_call_of_spec; apply hMaxV
        change fullCalcMaxVSpec (avail, BitVec.ofNat 64 mv, BitVec.ofNat 64 nc,
          BitVec.ofNat 64 (fullFixedBytes mv), ()) m0 _ _
        refine ⟨by rw [hmv_to]; exact hmv_bd, by rw [hnc_to]; exact hnc_bd,
          by rw [hmv_to]; exact hf0_to, by rw [hf0_to, hnc_to]; omega, ?_⟩
        intro max_v hmv_le hmx_bd hmax_fit
        rw [hmv_to] at hmv_le
        rw [hnc_to] at hmax_fit
        have hmx_b := hmx_bd; unfold dimacsBound at hmx_b
        have hfx_m_lt := fullFixedBytes_lt hmx_bd
        fp_head_steps
        apply wp_call_of_spec; apply hFixed
        change fullFixedBytesSpec (max_v, ()) m0 _ _
        refine ⟨hmx_bd, ?_⟩
        dsimp only
        fp_head_steps
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
        · rintro _ ⟨d_v, ⟨⟩⟩ md ⟨rfl, rfl⟩
          simp only [Blocks.get_here]; fp_head_steps
          apply wp_call_of_spec; apply hExt
          change fullCalcExtCapSpec (BitVec.ofNat 64 rem, ()) md _ _
          intro ecap_v hecap_le hecap_z hecap_4
          dsimp only; fp_head_steps
          apply wp_call_of_spec; apply hScr
          change fullCalcScrCapSpec (BitVec.ofNat 64 rem, ()) md _ _
          intro scap_v hscap_le hscap_z hscap_4
          dsimp only; fp_head_steps
          have hecap_lt : ecap_v.toNat < dimacsBound := by unfold dimacsBound; omega
          have hscap_lt : scap_v.toNat < dimacsBound := by unfold dimacsBound; omega
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
            obtain ⟨ws, hwl, hm_spl⟩ :=
              init_state_split_tail h1152 hav_le hm0_ac
            clear hm_in hm_pre hm0
            fp_head_steps
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
              dsimp only [ws1]
              rw [append4_getElem?_3 hw0l (by simp [hw1l]) hw2l (by decide)]
              simp [hw3l]
            have h112_ws1 : ws1[112]? = some (BitVec.ofNat 64 sc) := by
              dsimp only [ws1]
              rw [append4_getElem?_3 hw0l (by simp [hw1l]) hw2l (by decide)]
              simp [hw3l]
            have hsub_dyn : BitVec.ofNat 64 rem -
                BitVec.ofNat 64 (12 * del_cap + 4 * ec + 4 * sc) =
                BitVec.ofNat 64 (rem - (12 * del_cap + 4 * ec + 4 * sc)) :=
              bv_sub_ofNat (by omega) (by have := avail.isLt; omega)
            rw [hsub_dyn]
            apply wp_call_of_spec; apply hArenas
            change fullInitArenasSpec (hdr_addr, hdr_addr, max_v,
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
            change fullInitHdrSpec (hdr_addr, BitVec.ofNat 64 mv, max_v, fuel, ()) m2 _ _
            have hws2_c := hws2 c rfl rfl rfl rfl rfl rfl rfl rfl
            refine ⟨c, ws2, _, rfl, rfl, bv_ofNat_toNat_eq max_v |>.symm, hws2l,
              fun s0 i hi => ?_, hm2, fun s_hdr m3 hcv hal hwl hte hpr hcl htl hfu hunf hpb
                hmcl hmcf hoom hdm hinc hel hm3 => ?_⟩
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
              unfold hdrTailWords hdrTailWords0 hdrTailWords1 hdrTailWords2 hdrTailWords3
              repeat rcases hws2_c with ⟨h_, hws2_c⟩
              rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                rfl | rfl <;> assumption
            · obtain ⟨m_b, m_dr, hu_b, hd_b, h_reg, h_dr⟩ :=
                (show ((region (c.hdr + BitVec.ofNat 64 1152) (c.avail - 1152) ⋆
                  (bytes cnf_ptr cnfBytes ⋆ dimacsState c.hdr (BitVec.ofNat 64 mv)
                    (BitVec.ofNat 64 nc) (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 nc) ⋆
                    array64 (c.hdr + 32) (hdrTailWords c s_hdr) ⋆ R))) m3 from sep_ac hm3)
              obtain ⟨arrs, h_arrs⟩ := full_avail_to_arrays c h_reg
              let s_pre : FullState :=
                { core := { s_hdr.core with
                    d_cur := cnf_ptr + BitVec.ofNat 64 j,
                    d_val := BitVec.ofNat 64 nc,
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
                  FullCoreArrays c (initFullState c 0#64 0#64 0#64 arrs).core := rfl
              have h_pre_sa : FullScratchArrays c s_pre.scratch =
                  FullScratchArrays c (initFullState c 0#64 0#64 0#64 arrs).scratch := rfl
              have h_pre_ht : hdrTailWords c s_pre = hdrTailWords c s_hdr := by
                simp only [hdrTailWords, hdrTailWords0, hdrTailWords1, hdrTailWords2,
                  hdrTailWords3, s_pre]
              have hm_pre_full : (FullMem c s_pre ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m3 := by
                have hcomb := sep_push hu_b hd_b h_arrs h_dr
                rw [← h_pre_ca, ← h_pre_sa] at hcomb
                unfold FullMem; rw [h_pre_ht]
                exact sep_ac hcomb
              obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17,
                o18, o19, o20, o21, o22, o23, o24, o25, o26, o27, o28, o29, o30, o31, o32, o33, o34,
                o35, o36, o37, o38, o39, o40, o41⟩ := arrs.ok
              have hlen_pre : s_pre.LengthsOk c :=
                ⟨⟨o1, o2, o3, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19, o20, o21, o22,
                  by simp [s_pre, hcv], by simp [s_pre, hcv]; omega, by simp [s_pre, hal],
                  by simp [s_pre, hwl]; exact hwcap_pos, by simp [s_pre, hte],
                  by simp [s_pre, hpr, hte], by simp [s_pre, htl], by simp [s_pre, hmcl]⟩,
                 ⟨o4, o5, o6, o7, o8, o23, o24, o25, o26, o27, o28, o29, o30, o31, o32, o33, o34,
                  o35, o36, o37, o38, o39, o40, o41⟩⟩
              apply wp_call_of_spec; apply hZt1
              change fullZeroTables1Spec (c.hdr, ()) m3 _ _
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
                  vals_len := by simp [s_1],
                  lit_mark_len := by simp [s_1], wvec_len := by simp [s_1],
                  repr_len := hrepr', min_stk_len := hmstk', wstk_len_arr := hwstk' }, hsc1⟩
              apply wp_call_of_spec; apply hZt2
              change fullZeroTables2Spec (c.hdr, ()) m4 _ _
              refine ⟨c, s_1, bytes cnf_ptr cnfBytes ⋆ R, rfl, hlen1, hm4,
                fun flags' fdec' sc2 m5 hfl' hfd' hsc2 hpres2 hm5 => ?_⟩
              dsimp only
              rw [wp_ret]
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
                  mrk_len := by simp [s_2], flags_len := hfl',
                  lvl_len := by simp [s_2], rsns_len := by simp [s_2],
                  frame_trail_len := by simp [s_2], frame_dec_len := hfd' }, hsc2⟩
              have hll2 : ∀ i < 8, s_2.scratch.last_learned[i]?.getD 0xFFFFFFFF#32 =
                  0xFFFFFFFF#32 := by
                intro i hi8
                dsimp only [s_2]
                rw [hpres2.1]
                exact last_learned_getD_ff_of_zero hll1 i hi8
              have hext2 : s_2.scratch.extend_len = 0 := by
                dsimp only [s_2]; rw [hpres2.2, hext1]; exact hel
              have hft0 : (s_2.core.frame_trail[0]?.getD 0#32).toNat = 0 := by
                simp [s_2]
              have hinv2 := fullInv_init_sparse (F0 := shiftDownCnf CNF.empty) hlen2
                hinc hal rfl hte hcl hft0 rfl rfl rfl hll2 hext2 hdm
              rw [sep_comm_l, ← sep_assoc] at hm5
              exact hQtrue c s_2 j rest m5 rfl rfl hhdr hj hdrop hinv2 hcv rfl hal hwl hte hpr hcl
                hfu hunf hpb hmcl hmcf hoom hinc rfl rfl rfl rfl hext2 hm5
          · intro Jg hJg; fp_head_steps
            rw [hdel_mul, hshl2_e, hshl2_s, show (40 : BitVec 64) = BitVec.ofNat 64 40 from rfl,
              show (136 : BitVec 64) = BitVec.ofNat 64 136 from rfl,
              bv64_mul_nat3, hnc_to,
              show BitVec.ofNat 64 (12 * del_cap) + BitVec.ofNat 64 (4 * ecap_v.toNat) +
                BitVec.ofNat 64 (4 * scap_v.toNat) =
                BitVec.ofNat 64 (12 * del_cap + 4 * ecap_v.toNat + 4 * scap_v.toNat) by
                repeat rw [bv_add_ofNat],
              bv_add_ofNat, bv_add_ofNat, bv_ult_eq (by have := avail.isLt; omega)
                (by unfold dimacsBound at *; omega)]
            refine wp_jnz_of (fun hdlt => ?_) (fun hdge => ?_)
            · fp_jnz_t hdlt
              refine hJg (0#64, 0#64, BitVec.ofNat 64 (12 * del_cap), ()) md
                ⟨0, 0, by unfold dimacsBound; omega, by unfold dimacsBound; omega,
                  rfl, rfl, rfl, ?_, rfl⟩
              by_cases hrem_b : 524288 ≤ rem <;>
                simp [fullInitDelCap, del_cap, hrem_b] <;> omega
            · fp_jnz_f hdge
              refine hJg (ecap_v, scap_v, _, ()) md ⟨ecap_v.toNat, scap_v.toNat, hecap_lt,
                hscap_lt, hecap_bv.symm, hscap_bv.symm, rfl, by omega, rfl⟩
        · intro Jd hJd; fp_head_steps
          rw [show (524288 : BitVec 64) = BitVec.ofNat 64 524288 from rfl,
            bv_ule_eq (by decide) (by have := avail.isLt; omega)]
          refine wp_jnz_of (fun hbig => ?_) (fun hsmall => ?_)
          · fp_jnz_t hbig; refine hJd (4096#64, ()) m0 ⟨?_, rfl⟩
            simp [del_cap, fullInitDelCap, rem, hbig]
          · fp_jnz_f hsmall; refine hJd (8#64, ()) m0 ⟨?_, rfl⟩
            simp [del_cap, fullInitDelCap, rem, hsmall]

end LeanQbe.T.Examples.Kissat.Full
