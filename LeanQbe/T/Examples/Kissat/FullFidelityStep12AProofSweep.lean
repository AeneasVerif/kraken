/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep12A
public import LeanQbe.T.Examples.Kissat.FullM6SweepProofSpec
public import LeanQbe.T.Examples.Kissat.FullM6Sweep
import LeanQbe.T.Examples.Kissat.FullFidelitySweepProofVar
import LeanQbe.T.Examples.Kissat.FullM6SweepProofKittenLemmas
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullM6ProofUtil
import LeanQbe.T.Examples.Kissat.FullSpec1
import LeanQbe.T.Examples.Kissat.CoreLemmas1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step-12A Sweep Proofs (`FullFidelityStep12AProofSweep`)

Parametric `(Γ : Env)` `Func.wp` proofs (`public section`, `0` `@[expose]` on theorems/lemmas,
`0` `import all`, `std3`, `XPost`-polymorphic) for:
1. `full_m6_sweep_sim_step12a_wp` (`P1-1`: `sim_lim = tick_lim` preserving `m6SweepSimSpec`).
2. `full_m6_sweep_vars_step12a_wp` (`P0-1`: tracks swept count in `glue_used[32]` preserving
   `m6SweepVarsSpec`).
-/

set_option autoImplicit false

local elab "c0_hsteps_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

local macro "c0_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep12A

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full LeanQbe.T.Examples.Kissat.FullM4Sweep
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open LeanQbe.T.Examples.Kissat.FullFidelitySweep
open FullArenaTactics K6MemATactics FidVarMemTactics
open scoped FullArenaTactics K6MemATactics FidVarMemTactics

/-! ## 1. Shared Arithmetic, K6-Slab & `FullDenseInvW` Frame Helpers -/

private theorem swp_k6Layout_congr {n m : Nat} (e : n = m) (h1 : k6MinScr ≤ n)
    (h2 : n < dimacsBound) (h1' : k6MinScr ≤ m) (h2' : m < dimacsBound) :
    k6LayoutOfCap n h1 h2 = k6LayoutOfCap m h1' h2' := by
  subst e; rfl

private theorem swp_k6Ptr_eq (c : FullCfg) {L : K6Layout} (hL_mv : L.maxV = k6MaxV c.scratch_cap)
    (hmv30 : k6MaxV c.scratch_cap < 2 ^ 30) :
    c.pScratchBuf +
      BitVec.setWidth 64
        ((1280 : BitVec 32) +
          BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) <<< OfNat.ofNat 1) *
        4 =
      L.kPtr c.pScratchBuf := by
  have h1 : (BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap))).toNat =
      k6MaxV c.scratch_cap := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : k6MaxV c.scratch_cap < 2 ^ 64)]
    exact Nat.mod_eq_of_lt (by omega : k6MaxV c.scratch_cap < 2 ^ 32)
  have hsh : (BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) <<<
      OfNat.ofNat 1).toNat = 2 * k6MaxV c.scratch_cap := by
    rw [BitVec.toNat_shiftLeft, h1, show (OfNat.ofNat 1 : Nat) = 1 from rfl, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega : k6MaxV c.scratch_cap * 2 ^ 1 < 2 ^ 32)]
    omega
  have h2 : ((1280 : BitVec 32) + BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) <<<
      OfNat.ofNat 1).toNat = 1280 + 2 * k6MaxV c.scratch_cap := by
    rw [BitVec.toNat_add, show (1280 : BitVec 32).toNat = 1280 from rfl, hsh]
    exact Nat.mod_eq_of_lt (by omega : 1280 + 2 * k6MaxV c.scratch_cap < 2 ^ 32)
  unfold K6Layout.kPtr K6Layout.k6Base
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [hL_mv]
  simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, h2, show (4 : BitVec 64).toNat = 4 from rfl,
    BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : 1280 + 2 * k6MaxV c.scratch_cap < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : (1280 + 2 * k6MaxV c.scratch_cap) * 4 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 4 * (1280 + 2 * k6MaxV c.scratch_cap) < 2 ^ 64)]
  omega

private def swpSimSt (s : FullState) (fu rng : BitVec 64)
    (sig : List (BitVec 64)) (scr : List (BitVec 32)) : FullState :=
  { core := { s.core with fuel := fu },
    scratch := { s.scratch with rng_state := rng, sim_sig := sig, scratch_buf := scr } }

private theorem swp_k6_shapes_nassump0 {L : K6Layout} {ks : K6State}
    (h : ks.ShapesOk L) : (ks.putHdr .nassump 0#32).ShapesOk L :=
  ⟨h.hdrTail_len, h.lvlArr_len, h.rsn_len, h.qprev_len, h.qnext_len, h.qstampArr_len,
   h.trl_len, h.flags_len, h.ana_len, h.kl_len, h.assump_len, h.vals_len, h.whead_len,
   h.wnext_len, h.wblit_len, h.clOff_len, h.clSz_len, h.arena_len⟩

private theorem swp_k6Inv_nassump0 {L : K6Layout} {P : (Nat → Bool) → Prop}
    {ks : K6State} (h : K6Inv L P ks) : K6Inv L P (ks.putHdr .nassump 0#32) :=
  ⟨swp_k6_shapes_nassump0 h.shapes,
   ⟨h.clauses.acap_eq, h.clauses.max_v_eq, h.clauses.max_orig_eq, h.clauses.max_cl_eq,
    h.clauses.nv_le, h.clauses.nc_le, h.clauses.alen_le, Nat.zero_le _,
    h.clauses.nkl_le, h.clauses.nana_le, h.clauses.cl_wf, h.clauses.cl_mono,
    h.clauses.incons_ok, fun _ hi => absurd hi (Nat.not_lt_zero _), h.clauses.flags_clean⟩,
   h.watches,
   ⟨h.assign.trl_end_le, h.assign.prop_le, h.assign.unass_eq, h.assign.vals_dom,
    h.assign.vals_neg_iff, h.assign.vals_nz_iff_trl, h.assign.trl_nodup, h.assign.trl_lt,
    h.assign.trl_lvl_le, h.assign.unass_lvl_zero, h.assign.trl_lvl_mono,
    h.assign.dec_earliest, h.assign.lvl0_ok⟩,
   h.reasons⟩

private theorem swp_k6_unsat_empty_assump {F_cur : List (List Nat)} {ws : List (BitVec 32)}
    {nv : Nat} {L : K6Layout} {scr : List (BitVec 32)}
    (hna : (k6StateOfScratch L scr).nassump = 0#32)
    (hunsat : ∀ β, ConeModelSet F_cur ws nv β → ¬ (unitsCnf (k6AssumpLitsS L scr)).Sat β) :
    (cnfOfClauses F_cur).Unsat := by
  unfold CNF.Unsat
  intro α
  refine Bool.eq_false_iff.mpr fun hα => ?_
  have hcon : ConeModelSet F_cur ws nv (fun i => α (ws[i]?.getD 0#32).toNat) :=
    ⟨α, hα, fun _ _ => rfl⟩
  have hnil : k6AssumpLitsS L scr = [] := by
    unfold k6AssumpLitsS k6AssumpLits; rw [hna]; simp
  apply hunsat _ hcon
  rw [hnil, sat_unitsCnf_iff]
  intro _ hl; cases hl

private theorem swp_coneOk_of_sim_k6 {F_cur : List (List Nat)} {s : FullState}
    {hge_c : k6MinScr ≤ s.scratch.scratch_buf.length}
    {hlt_c : s.scratch.scratch_buf.length < dimacsBound}
    {nv : Val i32} {scr' : List (BitVec 32)}
    (hcone : M6SweepConeOk F_cur s nv.toNat)
    (hscr_eq : scr'.length = s.scratch.scratch_buf.length)
    (hK : K6Inv (k6LayoutOfCap s.scratch.scratch_buf.length hge_c hlt_c)
      (ConeModelSet F_cur s.scratch.work_stk1 nv.toNat)
      (k6StateOfScratch (k6LayoutOfCap s.scratch.scratch_buf.length hge_c hlt_c) scr'))
    (hnv : (k6StateOfScratch (k6LayoutOfCap s.scratch.scratch_buf.length hge_c hlt_c) scr').nv = nv)
    {fuel' rng' : BitVec 64} {sig' : List (BitVec 64)} :
    M6SweepConeOk F_cur
      { core := { s.core with fuel := fuel' },
        scratch := { s.scratch with rng_state := rng', sim_sig := sig', scratch_buf := scr' } }
      nv.toNat := by
  have hlt_scr : scr'.length < dimacsBound := hscr_eq ▸ hlt_c
  have hge_scr : k6MinScr ≤ scr'.length := hscr_eq ▸ hge_c
  have hLeq := swp_k6Layout_congr hscr_eq hge_scr hlt_scr hge_c hlt_c
  have hnv' : (k6StateOfScratch (k6LayoutOfCap s.scratch.scratch_buf.length hge_c hlt_c) scr').nv =
      BitVec.ofNat 32 nv.toNat :=
    hnv.trans (BitVec.eq_of_toNat_eq (by simp)).symm
  refine ⟨hcone.1, by rw [hscr_eq]; exact hcone.2.1, hcone.2.2.1, hcone.2.2.2.1,
    ⟨hge_scr, hlt_scr, hLeq ▸ hK⟩, ⟨hge_scr, hlt_scr, hLeq ▸ hnv'⟩⟩

private theorem swp_denseInvW_set_sim {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {fuel' rng' : BitVec 64} {sig' : List (BitVec 64)} {scr' : List (BitVec 32)}
    (hsig : sig'.length = c.max_vars) (hscr : scr'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur
      { core := { s.core with fuel := fuel' },
        scratch :=
          { s.scratch with rng_state := rng', sim_sig := sig', scratch_buf := scr' } } := by
  let s' : FullState :=
    { core := { s.core with fuel := fuel' },
      scratch := { s.scratch with rng_state := rng', sim_sig := sig', scratch_buf := scr' } }
  have hco := h.1.core_ok
  have hco' : FullCoreState.LengthsOk c s'.core :=
    ⟨hco.vals_len, hco.lit_mark_len, hco.mrk_len, hco.flags_len, hco.lvl_len, hco.rsns_len,
     hco.trl_len, hco.trail_pos_len, hco.tmp_len_arr, hco.min_clr_len_arr, hco.frame_trail_len,
     hco.frame_dec_len, hco.wvec_len, hco.repr_len, hco.min_stk_len, hco.arena_len_arr,
     hco.wstk_len_arr, hco.cur_vars_ge, hco.cur_vars_le, hco.arena_len_le, hco.wlen_le,
     hco.trail_end_le, hco.propagated_le, hco.tmp_len_le, hco.min_clr_len_le⟩
  have hw := h.2.1
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
  exact ⟨⟨hco', { h.1.scratch_ok with sim_sig_len := hsig, scratch_buf_len := hscr }⟩, hw',
    h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

private theorem swp_k6Slab_exit {c : FullCfg} {L : K6Layout} {s : FullState}
    {ks' : K6State} {R : Mem 64 → Prop} {m' : Mem 64}
    (hlen : s.LengthsOk c) (hL_len : L.scrLen = c.scratch_cap)
    (hsh' : ks'.ShapesOk L)
    (hm_ka : (K6MemA L (L.kPtr c.pScratchBuf) ks' ⋆ (FullK6Frame c L s ⋆ R)) m') :
    let scr' := s.scratch.scratch_buf.take L.k6Base ++ ks'.toSlab
    let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
    s'.LengthsOk c ∧ (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) ∧
      k6StateOfScratch L scr' = ks' ∧ (FullMem c s' ⋆ R) m' := by
  intro scr' s'
  have hscr : s.scratch.scratch_buf.length = c.scratch_cap := hlen.scratch_ok.scratch_buf_len
  have hscr_L : s.scratch.scratch_buf.length = L.scrLen := hscr.trans hL_len.symm
  have hkb : L.k6Base ≤ s.scratch.scratch_buf.length := by
    rw [hscr_L]; unfold K6Layout.scrLen; omega
  have htake : (s.scratch.scratch_buf.take L.k6Base).length = L.k6Base :=
    List.length_take_of_le hkb
  have hlen' : scr'.length = c.scratch_cap := by
    dsimp only [scr']
    rw [List.length_append, htake, ks'.toSlab_length hsh', ← hL_len]
    unfold K6Layout.scrLen; omega
  have hpre : ∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]? := fun i hi => by
    dsimp only [scr']
    rw [List.getElem?_append_left (by rw [htake]; exact hi), List.getElem?_take_of_lt hi]
  have hof : k6StateOfScratch L scr' = ks' := by
    unfold k6StateOfScratch; dsimp only [scr']
    rw [k6_slab_drop_exact _ _ htake]
    exact K6State.ofSlab_toSlab hsh'
  obtain ⟨_, hm_k⟩ := k6MemA_to_mem hm_ka
  have hm' : (FullMem c s' ⋆ R) m' :=
    fullMem_join_k6 (c := c) (L := L) (s := s) hkb hsh' (sep_ac hm_k)
  exact ⟨⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hlen' }⟩, hpre, hof, hm'⟩

private theorem swp_solve_call {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hSolve : M6EnvSpec Γ "full_m6_sweep_solve" m6SweepSolveSpec)
    {c : FullCfg} {s : FullState} {P : (Nat → Bool) → Prop} {L : K6Layout}
    {nv : Val i32} {tlim : Val i64} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Tup Val [i64] → Expr Val Cont rs}
    (hlen : s.LengthsOk c) (hL_len : L.scrLen = c.scratch_cap)
    (hL_mv : L.maxV = k6MaxV c.scratch_cap)
    (hK : K6Inv L P (k6StateOfScratch L s.scratch.scratch_buf))
    (hnv : (k6StateOfScratch L s.scratch.scratch_buf).nv = nv)
    (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ (r fuel' rng' : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState :=
        { core := { s.core with fuel := fuel' },
          scratch := { s.scratch with rng_state := rng', scratch_buf := scr' } }
      let ks := k6StateOfScratch L s.scratch.scratch_buf
      let ks' := k6StateOfScratch L scr'
      s'.LengthsOk c → fuel'.toNat ≤ s.core.fuel.toNat →
      (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
      K6Inv L P ks' → K6TrailSynced ks' → ks'.nv = nv → ks'.nassump = ks.nassump →
      k6AssumpLitsS L scr' = k6AssumpLitsS L s.scratch.scratch_buf → ks'.neq = ks.neq →
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
      (r = 20#64 → ∀ β, P β → ¬ CNF.Sat β (unitsCnf (k6AssumpLitsS L scr'))) →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X
      (Expr.call (as := [i64, i32, i64]) (bs := [i64]) "full_m6_sweep_solve"
        (Arg.var c.hdr, Arg.var nv, Arg.var tlim, ()) k) m :=
  wp_call_of_spec _ k
    (hSolve (c.hdr, nv, tlim, ()) m (fun r m' => wp Γ Q X (k r) m') X
      ⟨c, s, P, L, R, rfl, hlen, hL_len, hL_mv, hK, hnv, hm, hk⟩)

private theorem swp_ref_call {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hRef : M6EnvSpec Γ "full_m6_sweep_refine_sig" m6SweepRefineSigSpec)
    {c : FullCfg} {s : FullState} {nv bit_idx : Val i32} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Tup Val [] → Expr Val Cont rs}
    (hlen : s.LengthsOk c) (hcap : k6MinScr ≤ c.scratch_cap)
    (hnv_cap : nv.toNat ≤ k6MaxV c.scratch_cap) (hnv_mx : nv.toNat ≤ 2 * c.max_vars)
    (hws : ∀ i < nv.toNat, (s.scratch.work_stk1[i]?.getD 0#32).toNat < s.core.cur_vars)
    (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ sig' m', sig'.length = c.max_vars →
      (FullMem c { s with scratch := { s.scratch with sim_sig := sig' } } ⋆ R) m' →
      wp Γ Q X (k ()) m') :
    wp Γ Q X
      (Expr.call (as := [i64, i32, i32]) (bs := []) "full_m6_sweep_refine_sig"
        (Arg.var c.hdr, Arg.var nv, Arg.var bit_idx, ()) k) m :=
  wp_call_of_spec _ k
    (hRef (c.hdr, nv, bit_idx, ()) m (fun r m' => wp Γ Q X (k r) m') X
      ⟨c, s, R, rfl, hlen, hcap, hnv_cap, hnv_mx, hws, hm, hk⟩)

private theorem swp_flip_call {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hFlipR : M6EnvSpec Γ "full_m6_sweep_flip_round" m6SweepFlipRoundSpec)
    {c : FullCfg} {s : FullState} {P : (Nat → Bool) → Prop} {L : K6Layout}
    {nv : Val i32} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Tup Val [i32] → Expr Val Cont rs}
    (hlen : s.LengthsOk c) (hL_len : L.scrLen = c.scratch_cap)
    (hL_mv : L.maxV = k6MaxV c.scratch_cap)
    (hK : K6Inv L P (k6StateOfScratch L s.scratch.scratch_buf))
    (hnv : (k6StateOfScratch L s.scratch.scratch_buf).nv = nv)
    (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ (ret : Val i32) (rng' : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState :=
        { s with scratch := { s.scratch with rng_state := rng', scratch_buf := scr' } }
      let ks := k6StateOfScratch L s.scratch.scratch_buf
      let ks' := k6StateOfScratch L scr'
      s'.LengthsOk c → (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
      K6Inv L P ks' → ks'.nv = nv → ks'.nassump = ks.nassump →
      k6AssumpLitsS L scr' = k6AssumpLitsS L s.scratch.scratch_buf → ks'.neq = ks.neq →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k (ret, ())) m') :
    wp Γ Q X
      (Expr.call (as := [i64, i32]) (bs := [i32]) "full_m6_sweep_flip_round"
        (Arg.var c.hdr, Arg.var nv, ()) k) m :=
  wp_call_of_spec _ k
    (hFlipR (c.hdr, nv, ()) m (fun r m' => wp Γ Q X (k r) m') X
      ⟨c, s, P, L, R, rfl, hlen, hL_len, hL_mv, hK, hnv, hm, hk⟩)

/-! ## 2. `full_m6_sweep_sim_step12a_wp` (`P1-1`: `sim_lim = tick_lim`) -/

/-- Step-12A `full_m6_sweep_sim` (`sim_lim = tick_lim`) preserves `m6SweepSimSpec`. -/
theorem full_m6_sweep_sim_step12a_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hSolve : M6EnvSpec Γ "full_m6_sweep_solve" m6SweepSolveSpec)
    (hRef : M6EnvSpec Γ "full_m6_sweep_refine_sig" m6SweepRefineSigSpec)
    (hFlipR : M6EnvSpec Γ "full_m6_sweep_flip_round" m6SweepFlipRoundSpec) :
    ∀ args m Q X, m6SweepSimSpec args m Q X →
      Func.wp Γ full_m6_sweep_sim_body args m Q X := by
  rintro ⟨h, nv, tlim, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hdw, hcone, hm, hQ⟩
  unfold Func.wp full_m6_sweep_sim_body
  have hlen := hdw.1
  have hscr_len : s.scratch.scratch_buf.length = c.scratch_cap := hlen.scratch_ok.scratch_buf_len
  have hcap : k6MinScr ≤ c.scratch_cap := by
    rcases Nat.lt_or_ge c.scratch_cap k6MinScr with hlt | hle
    · have h0 := k6MaxV_eq_zero hlt; have h1 := hcone.1; have h2 := hcone.2.1
      rw [hscr_len] at h2; omega
    · exact hle
  have hcap_lt64 : c.scratch_cap < 2 ^ 64 := Nat.lt_trans c.hscr (by unfold dimacsBound; decide)
  have hscr_lt_db : c.scratch_cap < dimacsBound := c.hscr
  have hmv_bnds := k6MaxV_bounds hcap
  have hmv_pos : 0 < k6MaxV c.scratch_cap := by omega
  have hscr_lt30 : c.scratch_cap < 2 ^ 30 := Nat.lt_trans c.hscr (by unfold dimacsBound; decide)
  have hmv_lt30 : k6MaxV c.scratch_cap < 2 ^ 30 := by omega
  have hnv_le_mv : nv.toNat ≤ k6MaxV c.scratch_cap := by rw [← hscr_len]; exact hcone.2.1
  have hnv_le_cv : nv.toNat ≤ s.core.cur_vars := hcone.2.2.1
  have hcv_le_mx : s.core.cur_vars ≤ c.max_vars := hlen.core_ok.cur_vars_le
  have hnv_le_2mx : nv.toNat ≤ 2 * c.max_vars := by omega
  c0_hsteps_nogrp
  refine fid_call_max_v_cap hMaxV (cap := BitVec.ofNat 64 c.scratch_cap) ?_
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap_lt64]
  have hmv32_toNat : (BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap))).toNat =
      k6MaxV c.scratch_cap := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  c0_hsplit
  · exfalso
    have h0 : BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) = 0#32 := by
      assumption
    have h1 := congrArg BitVec.toNat h0
    rw [hmv32_toNat] at h1; simp at h1; omega
  c0_hsplit
  · exfalso
    have hgt : BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) < nv := by assumption
    have hlt := BitVec.lt_def.mp hgt
    rw [hmv32_toNat] at hlt; omega
  let L := k6LayoutOfCap c.scratch_cap hcap hscr_lt_db
  have hL_len : L.scrLen = c.scratch_cap := k6LayoutOfCap_scrLen hcap hscr_lt_db
  have hL_mv : L.maxV = k6MaxV c.scratch_cap := rfl
  c0_hsteps_nogrp
  refine wp_loop_inv
    (fun (i, ()) mi => i.toNat ≤ nv.toNat ∧ ∃ sig' : List (BitVec 64),
      sig'.length = c.max_vars ∧
      (FullMem c { s with scratch := { s.scratch with sim_sig := sig' } } ⋆ R) mi)
    (fun (i, ()) _ => nv.toNat - i.toNat)
    (fun Ji hJi => by
      c0_hsteps_nogrp
      exact hJi (0#32, ()) m ⟨Nat.zero_le _, s.scratch.sim_sig, hlen.scratch_ok.sim_sig_len, hm⟩)
    (fun Ji (i, ()) mi ⟨hi_le, sig', hsig', hmi⟩ ihi => ?_)
  c0_hsteps_nogrp
  · have hi_lt : i.toNat < nv.toNat := BitVec.lt_def.mp (by assumption)
    have hci_lt_cv := hcone.2.2.2.1 i.toNat hi_lt
    have hws_i_len : i.toNat < s.scratch.work_stk1.length := by
      rw [hlen.scratch_ok.work_stk1_len]; omega
    rw [List.getElem?_eq_getElem hws_i_len, Option.getD_some] at hci_lt_cv
    have hci_lt_sig : (s.scratch.work_stk1[i.toNat]'hws_i_len).toNat < sig'.length := by
      rw [hsig']; omega
    have hi1 : (i + 1#32).toNat = i.toNat + 1 := bv32_add1_toNat (by omega)
    c0_hsteps_nogrp
    exact ihi (i + 1#32, ()) _ (by dsimp only; rw [hi1]; omega)
      ⟨by rw [hi1]; omega, sig'.set _ 0#64, by simp [hsig'], by assumption⟩
  have hk_ptr := swp_k6Ptr_eq c hL_mv hmv_lt30
  let s_sig : FullState := { s with scratch := { s.scratch with sim_sig := sig' } }
  have hdw_sig : FullDenseInvW c F0 F_cur s_sig := swp_denseInvW_set_sim hdw hsig' hscr_len
  have hlen_sig := hdw_sig.1
  have hm_sig_k6 : (FullK6Frame c L s_sig ⋆
      K6MemA L (L.kPtr c.pScratchBuf)
        (k6StateOfScratch L s_sig.scratch.scratch_buf) ⋆ R) mi := by
    have hL_scr : s_sig.scratch.scratch_buf.length = L.scrLen := hscr_len.trans hL_len.symm
    have hm1 := hmi
    rw [fullMem_eq_k6Frame hL_scr] at hm1
    have hsh0 : (K6State.ofSlab L (s_sig.scratch.scratch_buf.drop L.k6Base)).ShapesOk L :=
      K6State.shapesOk_ofSlab_eq (L := L)
        (by rw [List.length_drop, hL_scr]; unfold K6Layout.scrLen; omega)
    have hm2 : (K6Mem L (L.kPtr c.pScratchBuf)
        (K6State.ofSlab L (s_sig.scratch.scratch_buf.drop L.k6Base)) ⋆
        (FullK6Frame c L s_sig ⋆ R)) mi := sep_ac hm1
    exact sep_ac (k6Mem_to_amem hsh0 hm2)
  have hK0 : K6Inv L (ConeModelSet F_cur s.scratch.work_stk1 nv.toNat)
      (k6StateOfScratch L s_sig.scratch.scratch_buf) := by
    obtain ⟨hge0, hlt0, hKi⟩ := hcone.2.2.2.2.1
    have hLeq := swp_k6Layout_congr hscr_len hge0 hlt0 hcap hscr_lt_db
    simpa only [hLeq] using hKi
  have hnv0 : (k6StateOfScratch L s_sig.scratch.scratch_buf).nv = nv := by
    obtain ⟨hge0, hlt0, hnvi⟩ := hcone.2.2.2.2.2
    have hLeq := swp_k6Layout_congr hscr_len hge0 hlt0 hcap hscr_lt_db
    have h1 := hnvi; rw [hLeq] at h1
    exact h1.trans (BitVec.eq_of_toNat_eq (by simp)).symm
  clear ihi
  rw [hk_ptr]
  c0_hsteps_nogrp
  have hm_pre : (K6MemA L (L.kPtr c.pScratchBuf)
      ((k6StateOfScratch L s_sig.scratch.scratch_buf).putHdr .nassump 0#32) ⋆
      (FullK6Frame c L s_sig ⋆ R)) m := by
    have h0 : (K6MemA L (L.kPtr c.pScratchBuf)
        ((k6StateOfScratch L s_sig.scratch.scratch_buf).putHdr .nassump 0) ⋆
        (FullK6Frame c L s_sig ⋆ R)) m :=
      sep_ac hm
    rwa [show (0 : BitVec 32) = 0#32 from rfl] at h0
  obtain ⟨hlen1, _, hof1, hm1⟩ := swp_k6Slab_exit hlen_sig hL_len
    (swp_k6_shapes_nassump0 hK0.shapes) hm_pre
  let s1 : FullState :=
    { s_sig with
      scratch := { s_sig.scratch with
        scratch_buf := s_sig.scratch.scratch_buf.take L.k6Base ++
          ((k6StateOfScratch L s_sig.scratch.scratch_buf).putHdr .nassump 0#32).toSlab } }
  have hK1 : K6Inv L (ConeModelSet F_cur s.scratch.work_stk1 nv.toNat)
      (k6StateOfScratch L s1.scratch.scratch_buf) := by rw [hof1]; exact swp_k6Inv_nassump0 hK0
  have hnv1 : (k6StateOfScratch L s1.scratch.scratch_buf).nv = nv := by rw [hof1]; exact hnv0
  have hna1 : (k6StateOfScratch L s1.scratch.scratch_buf).nassump = 0#32 := by rw [hof1]; rfl
  refine swp_solve_call hSolve hlen1 hL_len hL_mv hK1 hnv1 hm1
    fun st0 fuel2 rng2 scr2 m2 hlen2 hfu2 _ hK2 _ hnv2 hna2 _ _ _ hr20 hm2 => ?_
  have hs2_eq :
      ({ core := { s1.core with fuel := fuel2 },
         scratch := { s1.scratch with rng_state := rng2, scratch_buf := scr2 } } : FullState) =
        { s with
          core := { s.core with fuel := fuel2 },
          scratch := { s.scratch with
            rng_state := rng2, sim_sig := sig', scratch_buf := scr2 } } := by
    cases s with | mk co sc => cases co; cases sc; rfl
  rw [hs2_eq] at hm2
  have hscr2_len : scr2.length = c.scratch_cap := hlen2.scratch_ok.scratch_buf_len
  let s2 : FullState := swpSimSt s1 fuel2 rng2 s1.scratch.sim_sig scr2
  have hdw2 : FullDenseInvW c F0 F_cur s2 := swp_denseInvW_set_sim hdw_sig hsig' hscr2_len
  have hcone2 : M6SweepConeOk F_cur s2 nv.toNat := by
    have hge2 : k6MinScr ≤ s.scratch.scratch_buf.length := by rw [hscr_len]; exact hcap
    have hlt2 : s.scratch.scratch_buf.length < dimacsBound := by
      rw [hscr_len]; exact hscr_lt_db
    have hLeq2 := swp_k6Layout_congr hscr_len.symm hcap hscr_lt_db hge2 hlt2
    have hLeq2' : L = k6LayoutOfCap s.scratch.scratch_buf.length hge2 hlt2 := hLeq2
    exact swp_coneOk_of_sim_k6 hcone (hscr2_len.trans hscr_len.symm)
      (hLeq2' ▸ hK2) (hLeq2' ▸ hnv2)
  c0_hsplit
  · c0_hsteps_nogrp
    have hst0_eq : st0 = 20#64 := by assumption
    have hna2' : (k6StateOfScratch L scr2).nassump = 0#32 := hna2.trans hna1
    have hunsat : (cnfOfClauses F_cur).Unsat :=
      swp_k6_unsat_empty_assump hna2' (hr20 hst0_eq)
    exact hQ 0xFFFFFFFF#32 fuel2 rng2 sig' scr2 m2 hdw2 hfu2 hcone2
      (fun _ => hunsat) (fun hne => absurd rfl hne) hm2
  c0_hsplit
  · c0_hsteps_nogrp
    exact hQ 0#32 fuel2 rng2 sig' scr2 m2 hdw2 hfu2 hcone2
      (fun h => by cases h) (fun _ => by decide) hm2
  have hm2' : (FullMem c s2 ⋆ R) m2 := hm2
  refine swp_ref_call hRef hlen2 hcap hnv_le_mv hnv_le_2mx
    (fun k hk => hcone.2.2.2.1 k hk) hm2' fun sig3 m3 hsig3 hm3 => ?_
  let s3 : FullState := swpSimSt s2 fuel2 rng2 sig3 scr2
  have hdw3 : FullDenseInvW c F0 F_cur s3 := swp_denseInvW_set_sim hdw_sig hsig3 hscr2_len
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i32, i32]) (fun (rbit, _rnd, ()) mx =>
      rbit.toNat ≤ 64 ∧ ∃ rngX sigX scrX, sigX.length = c.max_vars ∧
      scrX.length = c.scratch_cap ∧
      (FullMem c (swpSimSt s fuel2 rngX sigX scrX) ⋆ R) mx ∧
      FullDenseInvW c F0 F_cur (swpSimSt s fuel2 rngX sigX scrX) ∧
      M6SweepConeOk F_cur (swpSimSt s fuel2 rngX sigX scrX) nv.toNat)
    ?_ ?_
  · rintro _ ⟨rbit, _rnd, ⟨⟩⟩ mx ⟨hr_le, rngX, sigX, scrX, _hsigX, _hscrX, hmx, hdwX, hconeX⟩
    c0_hsteps_nogrp
    exact hQ rbit fuel2 rngX sigX scrX mx hdwX hfu2 hconeX
      (fun hff => by have h1 := congrArg BitVec.toNat hff; simp at h1; omega)
      (fun _ => hr_le) hmx
  intro Jbrk hJbrk
  c0_hsteps_nogrp
  refine wp_loop_inv
    (fun (rbit, round, ()) ml => round.toNat ≤ 16 ∧ rbit.toNat = round.toNat + 1 ∧
      ∃ rngL sigL scrL, sigL.length = c.max_vars ∧ scrL.length = c.scratch_cap ∧
      (FullMem c (swpSimSt s fuel2 rngL sigL scrL) ⋆ R) ml ∧
      FullDenseInvW c F0 F_cur (swpSimSt s fuel2 rngL sigL scrL) ∧
      K6Inv L (ConeModelSet F_cur s.scratch.work_stk1 nv.toNat) (k6StateOfScratch L scrL) ∧
      (k6StateOfScratch L scrL).nv = nv)
    (fun (_, round, ()) _ => 16 - round.toNat)
    (fun Jl hJl => by
      c0_hsteps_nogrp
      exact hJl (1#32, 0#32, ()) m3 ⟨Nat.zero_le _, rfl, rng2, sig3, scr2, hsig3, hscr2_len,
        hm3, hdw3, hK2, hnv2⟩)
    (fun Jl (rbit, round, ()) ml ⟨hnd_le, hrbit_eq, rngL, sigL, scrL, hsigL, hscrL,
        hml, hdwL, hKL, hnvL⟩ ihl => ?_)
  · let sL : FullState := swpSimSt s fuel2 rngL sigL scrL
    have hconeL : M6SweepConeOk F_cur sL nv.toNat := by
      have hgeL : k6MinScr ≤ s.scratch.scratch_buf.length := by rw [hscr_len]; exact hcap
      have hltL : s.scratch.scratch_buf.length < dimacsBound := by
        rw [hscr_len]; exact hscr_lt_db
      have hLeqL := swp_k6Layout_congr hscr_len hgeL hltL hcap hscr_lt_db
      exact swp_coneOk_of_sim_k6 hcone (hscrL.trans hscr_len.symm)
        (by dsimp only [L] at hKL; exact hLeqL.symm ▸ hKL)
        (by dsimp only [L] at hnvL; exact hLeqL.symm ▸ hnvL)
    have hml_brk : Jbrk (rbit, round, ()) ml :=
      hJbrk (rbit, round, ()) ml ⟨by omega, rngL, sigL, scrL, hsigL, hscrL, hml, hdwL, hconeL⟩
    c0_hsteps_nogrp
    · have hnd_lt : round.toNat < 16 :=
        Nat.lt_of_lt_of_eq (BitVec.lt_def.mp (by assumption)) (by decide)
      have hrb_lt : rbit.toNat < 64 := by omega
      have hk11_idx := fid_k11_idx hL_len
      have hk11_scr : (BitVec.setWidth 64 (BitVec.ofNat 32 (L.k6Base + 11))).toNat <
          sL.scratch.scratch_buf.length := by
        dsimp only [sL, swpSimSt]; rw [hscrL]; exact hk11_idx
      rw [fid_k11_ptr hL_len]
      c0_hsteps_nogrp
      · refine swp_flip_call hFlipR hdwL.1 hL_len hL_mv hKL hnvL hml
          fun ret rngF scrF mF hlenF _ hKF hnvF _ _ _ hmF => ?_
        have hscrF_len : scrF.length = c.scratch_cap := hlenF.scratch_ok.scratch_buf_len
        c0_hsplit
        · refine swp_ref_call hRef hlenF hcap hnv_le_mv hnv_le_2mx
            (fun k hk => hcone.2.2.2.1 k hk) hmF fun sigF mF' hsigF hmF' => ?_
          have hrb1 : (rbit + 1#32).toNat = rbit.toNat + 1 := bv32_add1_toNat (by omega)
          have hnd1 : (round + 1#32).toNat = round.toNat + 1 := bv32_add1_toNat (by omega)
          have hdwF : FullDenseInvW c F0 F_cur (swpSimSt s fuel2 rngF sigF scrF) :=
            swp_denseInvW_set_sim hdw_sig hsigF hscrF_len
          c0_hsteps_nogrp
          exact ihl (rbit + 1#32, round + 1#32, ()) mF' (by dsimp only; rw [hnd1]; omega)
            ⟨by rw [hnd1]; omega, by rw [hrb1, hnd1]; omega, rngF, sigF, scrF, hsigF, hscrF_len,
             hmF', hdwF, hKF, hnvF⟩
        · have hconeF : M6SweepConeOk F_cur (swpSimSt s fuel2 rngF sigL scrF) nv.toNat := by
            have hgeF : k6MinScr ≤ s.scratch.scratch_buf.length := by rw [hscr_len]; exact hcap
            have hltF : s.scratch.scratch_buf.length < dimacsBound := by
              rw [hscr_len]; exact hscr_lt_db
            have hLeqF := swp_k6Layout_congr hscr_len hgeF hltF hcap hscr_lt_db
            dsimp only [L] at hKF hnvF
            exact swp_coneOk_of_sim_k6 hcone (hscrF_len.trans hscr_len.symm)
              (hLeqF.symm ▸ hKF) (hLeqF.symm ▸ hnvF)
          exact hJbrk (rbit, round, ()) mF ⟨by omega, rngF, sigL, scrF, hsigL, hscrF_len, hmF,
            swp_denseInvW_set_sim hdw_sig hsigL hscrF_len, hconeF⟩
      · exact hml_brk
      · exact hml_brk
    · exact hml_brk
    · exact hml_brk

/-! ## 3. `full_m6_sweep_vars_step12a_wp` (`P0-1`: tracks swept count in `glue_used[32]`) -/

private theorem swp_set_gu_inv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hdw : FullDenseInvW c F0 F_cur s) {gu' : List (BitVec 32)}
    (hgu : gu'.length = 64) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with glue_used := gu' } } :=
  fid_denseInvW_set_gu hdw hgu

private theorem swp_set_trc_ws2_inv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hdw : FullDenseInvW c F0 F_cur s) {trc' ws2' : List (BitVec 32)}
    (htrc : trc'.length = 2 * c.max_vars) (hws2 : ws2'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur
      { s with scratch := { s.scratch with tarjan_reach := trc', work_stk2 := ws2' } } :=
  fid_denseInvW_set_trc_ws2 hdw htrc hws2

private theorem swp_set_fl_inv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hdw : FullDenseInvW c F0 F_cur s) {fl' : List (BitVec 32)}
    (hfl : fl'.length = c.max_vars) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with flags := fl' } } :=
  fid_denseInvW_set_flags hdw hfl

private theorem swp_sub1_lt {a b : Nat} (h : a < b) : b - (a + 1) < b - a := by omega

private theorem swp_bv32_shr1 (x : BitVec 32) : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  bv_omega

private theorem swp_bv32_sub1 {x : BitVec 32} (h : 0 < x.toNat) :
    (x - 1#32).toNat = x.toNat - 1 := by
  bv_omega

private theorem swp_set_trc_inv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hdw : FullDenseInvW c F0 F_cur s) {trc' : List (BitVec 32)}
    (htrc : trc'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with tarjan_reach := trc' } } :=
  fid_denseInvW_set_trc hdw htrc

private theorem swp_trc_prefix_pres {trc : List (BitVec 32)} {cv idx nc : Nat} {rv : BitVec 32}
    (hnc_le : nc ≤ cv) (hprev : ∀ i < nc, (trc[i]?.getD 0#32).toNat < cv)
    (hcv_pos : cv ≤ cv + idx) :
    ∀ i < nc, ((trc.set (cv + idx) rv)[i]?.getD 0#32).toNat < cv := by
  intro i hi
  rw [List.getElem?_set_ne (by omega)]
  exact hprev i hi

private theorem swp_trc_isz_push {trc : List (BitVec 32)} {cv isz : Nat} {rv : BitVec 32}
    (hlen : cv + isz < trc.length) (hrv : rv.toNat < cv)
    (hprev : ∀ i < isz, (trc[cv + i]?.getD 0#32).toNat < cv) :
    ∀ i < isz + 1, ((trc.set (cv + isz) rv)[cv + i]?.getD 0#32).toNat < cv := by
  intro i hi
  rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | rfl
  · rw [List.getElem?_set_ne (by omega)]; exact hprev i hlt
  · rw [List.getElem?_set_self hlen, Option.getD_some]; exact hrv

private theorem swp_lex_dec_rb {rb1 rb2 rem1 rem2 cap : Nat}
    (hrb : rb2 + 1 ≤ rb1) (hrem2 : rem2 ≤ cap) :
    rb2 * (cap + 1) + rem2 < rb1 * (cap + 1) + rem1 := by
  have hmul : (rb2 + 1) * (cap + 1) ≤ rb1 * (cap + 1) := Nat.mul_le_mul_right _ hrb
  rw [Nat.add_one_mul] at hmul
  omega

private theorem swp_var_call {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hSV : M6EnvSpec Γ "full_m6_sweep_var" m6SweepVarSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {rv : BitVec 32} {tlim : BitVec 64}
    {k : Tup Val [i64] → Expr Val Cont rs}
    (hdw : FullDenseInvW c F0 F_cur s) (hcap : k6MinScr ≤ c.scratch_cap)
    (hrv : rv.toNat < s.core.cur_vars) (htmk : M6TmkZero s) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ r s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → M6TmkZero s' →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X
      (Expr.call (as := [i64, i32, i64]) (bs := [i64]) "full_m6_sweep_var"
        (Arg.var c.hdr, Arg.var rv, Arg.var tlim, ()) k) m :=
  fid_call_sweep_var hSV hdw hcap hrv htmk hm hk

private theorem swp12a_bv64_wvec_neg_toNat (v : BitVec 64) (hv : v.toNat < 2 ^ 60) :
    ((((v <<< (1 : Nat)) ||| 1#64) <<< (1 : Nat)) + 1#64).toNat = 4 * v.toNat + 3 := by
  have hsh1 : (v <<< (1 : Nat)).toNat = 2 * v.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one,
      Nat.mod_eq_of_lt (by omega : v.toNat * 2 < 2 ^ 64)]
    omega
  have hor : (v <<< (1 : Nat) ||| 1#64).toNat = 2 * v.toNat + 1 := by
    rw [BitVec.toNat_or, hsh1, show (1#64 : BitVec 64).toNat = 1 from rfl]
    apply Nat.eq_of_testBit_eq
    intro k
    cases k with
    | zero => simp [Nat.testBit_zero]
    | succ k =>
      rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
      rw [show 1 / 2 = 0 from rfl, show (2 * v.toNat) / 2 = v.toNat from by omega,
        show (2 * v.toNat + 1) / 2 = v.toNat from by omega, Nat.zero_testBit, Bool.or_false]
  have hsh2 : (((v <<< (1 : Nat)) ||| 1#64) <<< (1 : Nat)).toNat = 4 * v.toNat + 2 := by
    rw [BitVec.toNat_shiftLeft, hor, Nat.shiftLeft_eq, Nat.pow_one,
      Nat.mod_eq_of_lt (by omega : (2 * v.toNat + 1) * 2 < 2 ^ 64)]
    omega
  rw [BitVec.toNat_add, hsh2, show (1#64 : BitVec 64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega : 4 * v.toNat + 2 + 1 < 2 ^ 64)]

private theorem swp12a_eq_push_step_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {sEq : FullState} {R : Mem 64 → Prop} {mEq : Mem 64}
    {rv : Val i32} {iszE nc : BitVec 32} {cvP : Nat} {fuel0 : Nat} {J_r : Cont [i32]}
    (hmx : c.max_vars < 2 ^ 31)
    (hdwEq : FullDenseInvW c F0 F_cur sEq)
    (hcvEq : sEq.core.cur_vars = cvP)
    (hfuEq : sEq.core.fuel.toNat ≤ fuel0)
    (htmkEq : M6TmkZero sEq)
    (hnc_le : nc.toNat ≤ sEq.core.cur_vars)
    (hiszE_le : iszE.toNat ≤ cvP)
    (htrcEq_p : ∀ i < nc.toNat, (sEq.scratch.tarjan_reach[i]?.getD 0#32).toNat < cvP)
    (htrcEq_i : ∀ i < iszE.toNat, (sEq.scratch.tarjan_reach[cvP + i]?.getD 0#32).toNat < cvP)
    (hmEq : (FullMem c sEq ⋆ R) mEq)
    (hrv_lt : rv.toNat < sEq.core.cur_vars)
    (hfl_rv64 : (BitVec.setWidth 64 rv).toNat < sEq.core.flags.length)
    (hJe_r : ∀ xs mR, (match xs with
      | (iszR, ()) => iszR.toNat ≤ cvP ∧ ∃ sR : FullState,
        FullDenseInvW c F0 F_cur sR ∧ sR.core.cur_vars = cvP ∧ sR.core.fuel.toNat ≤ fuel0 ∧
        M6TmkZero sR ∧
        (∀ i < nc.toNat, (sR.scratch.tarjan_reach[i]?.getD 0#32).toNat < cvP) ∧
        (∀ i < iszR.toNat, (sR.scratch.tarjan_reach[cvP + i]?.getD 0#32).toNat < cvP) ∧
        (FullMem c sR ⋆ R) mR) → J_r xs mR) :
    wp Γ Q X
      (Expr.jnz
        (Arg.var ((sEq.core.flags[(BitVec.setWidth 64 rv).toNat]'hfl_rv64 &&& 1#32 != 0#32)))
        (Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var rv, Arg.imm 1, ())) fun p =>
          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p.fst, ())) fun p =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pVals, Arg.var p.fst, ())) fun p =>
              Expr.load i8 (Arg.var p.fst) fun ld =>
                Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm 0, ())) fun p =>
                  Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var ld, ())) fun p_1 =>
                    Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var p.fst, ())) fun p =>
                      Expr.let_
                        (Op.mk (OpCode.cmp CmpOp.eq i32 Ty.bool rfl)
                          (Arg.var p_1.fst, Arg.var p.fst, ())) fun p =>
                        Expr.jnz (Arg.var p.fst)
                          (Expr.group (sig := [[i32]])
                            (fun _Js =>
                              Blocks.cons
                                (fun p =>
                                  Expr.let_
                                    (Op.mk (OpCode.zext 32 64) (Arg.var rv, ())) fun p_2 =>
                                    Expr.let_
                                      (Op.mk (OpCode.mul i64)
                                        (Arg.var p_2.fst, Arg.imm 4, ())) fun p_3 =>
                                      Expr.let_
                                        (Op.mk (OpCode.add i64)
                                          (Arg.var c.pFlags, Arg.var p_3.fst, ())) fun p_4 =>
                                        Expr.let_
                                          (Op.mk (OpCode.zext 32 64) (Arg.var rv, ())) fun p_5 =>
                                          Expr.let_
                                            (Op.mk (OpCode.mul i64)
                                              (Arg.var p_5.fst, Arg.imm 4, ())) fun p_6 =>
                                            Expr.let_
                                              (Op.mk (OpCode.add i64)
                                                (Arg.var c.pFlags, Arg.var p_6.fst, ())) fun p_7 =>
                                              Expr.load i32 (Arg.var p_7.fst) fun ld =>
                                                Expr.let_
                                                  (Op.mk (OpCode.or i32)
                                                    (Arg.var ld, Arg.imm 1024, ())) fun p_8 =>
                                                  Expr.let_
                                                    (Op.mk (OpCode.or i32)
                                                      (Arg.var p_8.fst, Arg.imm 536870912, ()))
                                                    fun p_9 =>
                                                    Expr.store (Arg.var p_9.fst) (Arg.var p_4.fst)
                                                      (Expr.jump J_r (Arg.var p.fst, ())))
                                Blocks.nil)
                            fun Js =>
                            Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var rv, ())) fun p =>
                              Expr.let_
                                (Op.mk (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
                                Expr.let_
                                  (Op.mk (OpCode.add i64) (Arg.var c.pFlags, Arg.var p.fst, ()))
                                  fun p =>
                                  Expr.load i32 (Arg.var p.fst) fun ld =>
                                    Expr.let_
                                      (Op.mk (OpCode.and i32)
                                        (Arg.var ld, Arg.imm 536870912, ())) fun p =>
                                      Expr.let_
                                        (Op.mk (OpCode.cmp CmpOp.eq i32 Ty.bool rfl)
                                          (Arg.var p.fst, Arg.imm 0, ())) fun p =>
                                        Expr.jnz (Arg.var p.fst)
                                          (Expr.let_
                                            (Op.mk (OpCode.zext 32 64) (Arg.var iszE, ())) fun p =>
                                            Expr.let_
                                              (Op.mk (OpCode.cmp CmpOp.ult i64 Ty.bool rfl)
                                                (Arg.var p.fst, Arg.var (BitVec.ofNat 64 cvP), ()))
                                              fun p =>
                                              Expr.jnz (Arg.var p.fst)
                                                (Expr.let_
                                                  (Op.mk (OpCode.zext 32 64) (Arg.var iszE, ()))
                                                  fun p =>
                                                  Expr.let_
                                                    (Op.mk (OpCode.add i64)
                                                      (Arg.var (BitVec.ofNat 64 cvP),
                                                       Arg.var p.fst, ())) fun p =>
                                                    Expr.let_
                                                      (Op.mk (OpCode.mul i64)
                                                        (Arg.var p.fst, Arg.imm 4, ())) fun p =>
                                                      Expr.let_
                                                        (Op.mk (OpCode.add i64)
                                                          (Arg.var c.pTarjanReach,
                                                           Arg.var p.fst, ())) fun p =>
                                                        Expr.store (t := i32)
                                                          (Arg.var rv) (Arg.var p.fst)
                                                          (Expr.let_
                                                            (Op.mk (OpCode.add i32)
                                                              (Arg.var iszE, Arg.imm 1, ()))
                                                            fun p =>
                                                            Expr.jump Js.fst (Arg.var p.fst, ())))
                                                (Expr.jump Js.fst (Arg.var iszE, ())))
                                          (Expr.jump Js.fst (Arg.var iszE, ())))
                          (Expr.jump J_r (Arg.var iszE, ())))
        (Expr.jump J_r (Arg.var iszE, ()))) mEq := by
  have hcvEq_le := hdwEq.1.core_ok.cur_vars_le
  have h2cvEq_32 : 2 * sEq.core.cur_vars < 2 ^ 32 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 2 hcvEq_le)
      (Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hmx (by decide)) (by decide))
  have hcvEq_32 : sEq.core.cur_vars < 2 ^ 32 :=
    Nat.lt_of_le_of_lt hcvEq_le (Nat.lt_trans hmx (by decide))
  have hcvEq_64 : sEq.core.cur_vars < 2 ^ 64 := Nat.lt_trans hcvEq_32 (by decide)
  have hcvP_64 : cvP < 2 ^ 64 := hcvEq ▸ hcvEq_64
  have hval_rv : (BitVec.setWidth 64 (rv <<< (1 : Nat))).toNat < sEq.core.vals.length := by
    have hsh : (BitVec.setWidth 64 (rv <<< (1 : Nat))).toNat = 2 * rv.toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide)),
        BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one,
        Nat.mod_eq_of_lt (by
          rw [Nat.mul_comm]
          exact Nat.lt_trans (Nat.mul_lt_mul_of_pos_left hrv_lt (by decide)) h2cvEq_32)]
      exact Nat.mul_comm _ 2
    rw [hsh, hdwEq.1.core_ok.vals_len]
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hrv_lt (by decide))
      (Nat.mul_le_mul_left 2 hcvEq_le)
  c0_hsplit; rotate_left
  · c0_hstraight
    exact hJe_r (iszE, ()) mEq ⟨hiszE_le, sEq, hdwEq, hcvEq, hfuEq, htmkEq,
      htrcEq_p, htrcEq_i, hmEq⟩
  c0_hstraight
  c0_hsplit; rotate_left
  · c0_hstraight
    exact hJe_r (iszE, ()) mEq ⟨hiszE_le, sEq, hdwEq, hcvEq, hfuEq, htmkEq,
      htrcEq_p, htrcEq_i, hmEq⟩
  c0_hstraight
  refine wp_join_group (ts := [i32]) (fun (isz1, ()) mPsh =>
      isz1.toNat ≤ cvP ∧ ∃ sPsh : FullState,
        FullDenseInvW c F0 F_cur sPsh ∧ sPsh.core.cur_vars = cvP ∧
        sPsh.core.fuel.toNat ≤ fuel0 ∧ M6TmkZero sPsh ∧
        (∀ i < nc.toNat, (sPsh.scratch.tarjan_reach[i]?.getD 0#32).toNat < cvP) ∧
        (∀ i < isz1.toNat, (sPsh.scratch.tarjan_reach[cvP + i]?.getD 0#32).toNat < cvP) ∧
        (FullMem c sPsh ⋆ R) mPsh)
    ?_ ?_
  · rintro _ ⟨isz1, ⟨⟩⟩ mPsh ⟨hisz1_le, sPsh, hdwPsh, hcvPsh, hfuPsh, htmkPsh,
      htrcPsh_p, htrcPsh_i, hmPsh⟩
    have hfl_Psh64 : (BitVec.setWidth 64 rv).toNat < sPsh.core.flags.length := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide)),
        hdwPsh.1.core_ok.flags_len]
      exact Nat.lt_of_lt_of_le hrv_lt hcvEq_le
    c0_hstraight
    let fl_new : List (BitVec 32) :=
      sPsh.core.flags.set (BitVec.setWidth 64 rv).toNat
        (sPsh.core.flags[(BitVec.setWidth 64 rv).toNat]'hfl_Psh64 ||| 1024#32 ||| 536870912#32)
    have hfl_new_len : fl_new.length = c.max_vars := by
      dsimp only [fl_new]; rw [List.length_set, hdwPsh.1.core_ok.flags_len]
    have hm_new :
        (FullMem c { sPsh with core := { sPsh.core with flags := fl_new } } ⋆ R) m := by
      dsimp only [fl_new]; exact hm
    exact hJe_r (isz1, ()) m
      ⟨hisz1_le, { sPsh with core := { sPsh.core with flags := fl_new } },
       swp_set_fl_inv hdwPsh hfl_new_len, hcvPsh, hfuPsh,
       fid_tmkZero_congr htmkPsh rfl rfl, htrcPsh_p, htrcPsh_i, hm_new⟩
  · intro Jp hJp
    c0_hstraight
    c0_hsplit
    · c0_hstraight
      c0_hsplit; rotate_left
      · c0_hstraight
        exact hJp (iszE, ()) mEq ⟨hiszE_le, sEq, hdwEq, hcvEq, hfuEq, htmkEq,
          htrcEq_p, htrcEq_i, hmEq⟩
      have hiszE_lt : iszE.toNat < sEq.core.cur_vars := by
        have h1 : iszE.toNat < cvP % 2 ^ 64 := by assumption
        rw [Nat.mod_eq_of_lt hcvP_64, ← hcvEq] at h1; exact h1
      have hcv_add_isz_2 : sEq.core.cur_vars + iszE.toNat < 2 * sEq.core.cur_vars := by
        rw [Nat.two_mul]; exact Nat.add_lt_add_left hiszE_lt _
      have hcv_add_isz_64 : sEq.core.cur_vars + iszE.toNat < 2 ^ 64 :=
        Nat.lt_trans hcv_add_isz_2 (Nat.lt_trans h2cvEq_32 (by decide))
      have htrc_idx : (BitVec.ofNat 64 cvP + BitVec.setWidth 64 iszE).toNat =
          sEq.core.cur_vars + iszE.toNat := by
        rw [← hcvEq, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
          Nat.mod_eq_of_lt (Nat.lt_trans iszE.isLt (by decide)),
          Nat.mod_eq_of_lt hcvEq_64, Nat.mod_eq_of_lt hcv_add_isz_64]
      have htrc_len : (BitVec.ofNat 64 cvP + BitVec.setWidth 64 iszE).toNat <
          sEq.scratch.tarjan_reach.length := by
        rw [htrc_idx, hdwEq.1.scratch_ok.tarjan_reach_len]
        exact Nat.lt_of_lt_of_le hcv_add_isz_2 (Nat.mul_le_mul_left 2 hcvEq_le)
      have hisz1 : (iszE + 1#32).toNat = iszE.toNat + 1 := by
        rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hiszE_lt hcvEq_32)]
      c0_hstraight
      have htrc_idxP : (BitVec.ofNat 64 cvP + BitVec.setWidth 64 iszE).toNat =
          cvP + iszE.toNat := hcvEq ▸ htrc_idx
      let trc' := sEq.scratch.tarjan_reach.set (cvP + iszE.toNat) rv
      have htrc'_len : trc'.length = 2 * c.max_vars := by
        dsimp only [trc']; rw [List.length_set, hdwEq.1.scratch_ok.tarjan_reach_len]
      have hm' :
          (FullMem c { sEq with scratch := { sEq.scratch with tarjan_reach := trc' } } ⋆ R) m := by
        dsimp only [trc']; rw [← htrc_idxP]; exact by assumption
      have htrc'_p := swp_trc_prefix_pres (idx := iszE.toNat) (rv := rv)
        (hcvEq ▸ hnc_le) htrcEq_p (Nat.le_add_right _ _)
      have htrc'_i := swp_trc_isz_push (by rw [← htrc_idxP]; exact htrc_len)
        (hcvEq ▸ hrv_lt) htrcEq_i
      exact hJp (iszE + 1#32, ()) m
        ⟨by rw [hisz1, ← hcvEq]; exact hiszE_lt,
         { sEq with scratch := { sEq.scratch with tarjan_reach := trc' } },
         swp_set_trc_inv hdwEq htrc'_len,
         hcvEq, hfuEq, fid_tmkZero_congr htmkEq rfl rfl,
         htrc'_p, by simpa only [hisz1] using htrc'_i, hm'⟩
    · c0_hstraight
      exact hJp (iszE, ()) mEq ⟨hiszE_le, sEq, hdwEq, hcvEq, hfuEq, htmkEq,
        htrcEq_p, htrcEq_i, hmEq⟩

private theorem swp12a_post_fl_loop_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {sO : FullState}
    {R : Mem 64 → Prop} {mOut : Mem 64} {cvP : Nat} {max_occ : Val i64} {Jfl : Cont [i64, i64]}
    (hmx : c.max_vars < 2 ^ 31)
    (hdwO : FullDenseInvW c F0 F_cur sO)
    (hcvO : sO.core.cur_vars = cvP)
    (hmO : (FullMem c sO ⋆ R) mOut)
    (hJfl : ∀ (li_out vi_out : Val i64) (mFl : Mem 64),
      (∃ flL : List (BitVec 32), flL.length = c.max_vars ∧
        (FullMem c { sO with core := { sO.core with flags := flL } } ⋆ R) mFl) →
      Jfl (li_out, vi_out, ()) mFl) :
    wp Γ Q X (Expr.group (sig := [[i64]]) (fun Js =>
          Blocks.cons (fun p => Expr.let_
                (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var p.fst, Arg.var (BitVec.ofNat 64 cvP), ()))
                fun p_1 => Expr.jnz (Arg.var p_1.fst) (Expr.group (sig := [[i64]]) (fun _Js_1 =>
                      Blocks.cons (fun _p_2 =>
                          Expr.let_ (Op.mk (.add i64) (Arg.var p.fst, Arg.imm 1, ())) fun p =>
                            Expr.jump Js.fst (Arg.var p.fst, ()))
                        Blocks.nil) fun Js =>
                    Expr.let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p_2 =>
                      Expr.let_ (Op.mk (.add i64) (Arg.var c.pFlags, Arg.var p_2.fst, ()))
                        fun p_3 => Expr.load i32 (Arg.var p_3.fst) fun ld =>
                          Expr.let_ (Op.mk (.or i32) (Arg.imm 1, Arg.imm 1024, ())) fun p_4 =>
                            Expr.let_ (Op.mk (.or i32) (Arg.var p_4.fst, Arg.imm 1073741824, ()))
                              fun p_5 =>
                              Expr.let_ (Op.mk (.and i32) (Arg.var ld, Arg.var p_5.fst, ()))
                                fun p_6 =>
                                Expr.let_ (Op.mk (.or i32) (Arg.imm 1, Arg.imm 1024, ())) fun p_7 =>
                                  Expr.let_
                                    (Op.mk (.or i32) (Arg.var p_7.fst, Arg.imm 1073741824, ()))
                                    fun p_8 => Expr.let_ (Op.mk (.cmp .eq i32 .bool rfl)
                                        (Arg.var p_6.fst, Arg.var p_8.fst, ())) fun p_9 =>
                                      Expr.jnz (Arg.var p_9.fst) (Expr.group (sig := [[i64]])
                                          (fun _Js_1 =>
                                            Blocks.cons (fun p_10 => Expr.let_
                                                  (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ()))
                                                  fun p_11 => Expr.let_ (Op.mk (.add i64)
                                                      (Arg.var c.pFlags, Arg.var p_11.fst, ()))
                                                    fun p_12 => Expr.let_ (Op.mk (.mul i64)
                                                        (Arg.var p.fst, Arg.imm 4, ())) fun p =>
                                                      Expr.let_ (Op.mk (.add i64)
                                                          (Arg.var c.pFlags, Arg.var p.fst, ()))
                                                        fun p =>
                                                        Expr.load i32 (Arg.var p.fst) fun ld =>
                                                          Expr.let_ (Op.mk (.or i32)
                  (Arg.imm 1024, Arg.imm 1073741824, ())) fun p => Expr.let_ (Op.mk (.or i32)
                                                                (Arg.var p.fst, Arg.imm 536870912,
                                                                 ())) fun p => Expr.let_
                (Op.mk (.not i32) (Arg.var p.fst, ())) fun p => Expr.let_ (Op.mk (.and i32)
                                                                    (Arg.var ld, Arg.var p.fst, ()))
                                                                  fun p =>
                                                                  Expr.store (Arg.var p.fst)
                                                                    (Arg.var p_12.fst)
                                                                    (Expr.jump Js.fst
                                                                      (Arg.var p_10.fst, ())))
                                              Blocks.nil) fun Js =>
                  Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun p_10 => Expr.let_
                  (Op.mk (.shl i64) (Arg.var p.fst, Arg.var p_10.fst, ())) fun p_11 => Expr.let_
                                                (Op.mk (.add i64)
                  (Arg.var c.pVals, Arg.var p_11.fst, ())) fun p_12 =>
                                                Expr.load i8 (Arg.var p_12.fst) fun ld =>
                                                  Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 0, ()))
                                                    fun p_13 =>
                                                    Expr.let_ (Op.mk (.sext 8 32) (Arg.var ld, ()))
                                                      fun p_14 => Expr.let_
                                                        (Op.mk (.sext 8 32) (Arg.var p_13.fst, ()))
                                                        fun p_15 => Expr.let_
                                                          (Op.mk (.cmp .eq i32 .bool rfl)
                (Arg.var p_14.fst, Arg.var p_15.fst, ())) fun p_16 =>
                                                          Expr.jnz (Arg.var p_16.fst) (Expr.let_
                                                              (Op.mk (.sext 32 64) (Arg.imm 1, ()))
                                                              fun p_17 => Expr.let_
                                                                (Op.mk (.shl i64)
                                                                  (Arg.var p.fst, Arg.var p_17.fst,
                                                                   ())) fun p_18 => Expr.let_
                                                                  (Op.mk (.sext 32 64)
                                                                    (Arg.imm 1, ())) fun p_19 =>
                                                                  Expr.let_ (Op.mk (.shl i64)
                                                                      (Arg.var p_18.fst,
                                                                       Arg.var p_19.fst, ()))
                                                                    fun p_20 => Expr.let_
                                                                      (Op.mk (.add i64)
                                                                        (Arg.var p_20.fst,
                                                                         Arg.imm 1, ())) fun p_21 =>
                                                                      Expr.let_
                                                                        (Op.mk (.mul i64)
                                                                          (Arg.var p_21.fst,
                   Arg.imm 4, ())) fun p_22 => Expr.let_ (Op.mk (.add i64) (Arg.var c.pWvec,
                                                                             Arg.var p_22.fst, ()))
                                                                          fun p_23 =>
                                                                          Expr.load i32
                                                                            (Arg.var p_23.fst)
                                                                            fun ld => Expr.let_
                                                                              (Op.mk (.zext 32 64)
                                                                                (Arg.var ld, ()))
                                                                              fun p_24 =>
                                                                              Expr.let_
                                                                                (Op.mk (.sext 32 64)
                                                                                  (Arg.imm 1, ()))
                                                                                fun p_25 =>
                                                                                Expr.let_
                                                                                  (Op.mk (.shl i64)
                                                                                    (Arg.var p.fst,
                                                                                     Arg.var
                                                                                       p_25.fst,
                 ())) fun p_26 => Expr.let_ (Op.mk (.or i64) (Arg.var p_26.fst, Arg.imm 1, ()))
                                                                                    fun p_27 =>
                                                                                    Expr.let_
                                                                                      (Op.mk
                                                                                        (.sext 32
                                                                                          64)
                                                                                        (Arg.imm 1,
                                                                                         ()))
                                                                                      fun p_28 =>
                                                                                      Expr.let_
                                                                                        (Op.mk
                                                                                          (.shl i64)
                                                                                          (Arg.var
                p_27.fst, Arg.var p_28.fst, ())) fun p_29 => Expr.let_ (Op.mk (.add i64)
                                                                                            (Arg.var
                  p_29.fst, Arg.imm 1, ())) fun p_30 => Expr.let_ (Op.mk (.mul i64) (Arg.var
                p_30.fst, Arg.imm 4, ())) fun p_31 => Expr.let_ (Op.mk (.add i64) (Arg.var
                  c.pWvec, Arg.var p_31.fst, ())) fun p_32 => Expr.load i32 (Arg.var p_32.fst)
                fun ld => Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld, ())) fun p_33 => Expr.let_
                (Op.mk (.cmp .ugt i64 .bool rfl) (Arg.var p_24.fst, Arg.imm 0, ())) fun p_34 =>
                Expr.jnz (Arg.var p_34.fst) (Expr.let_ (Op.mk (.cmp .ugt i64 .bool rfl)
                  (Arg.var p_33.fst, Arg.imm 0, ())) fun p_35 => Expr.jnz (Arg.var p_35.fst)
                  (Expr.let_ (Op.mk (.cmp .ule i64 .bool rfl)
                  (Arg.var p_24.fst, Arg.var max_occ, ())) fun p_36 =>
                Expr.jnz (Arg.var p_36.fst) (Expr.let_ (Op.mk (.cmp .ule i64 .bool rfl)
                  (Arg.var p_33.fst, Arg.var max_occ, ())) fun p_37 =>
                Expr.jnz (Arg.var p_37.fst) (Expr.jump Jfl (Arg.imm 1, Arg.var p.fst, ()))
                  (Expr.jump Js.fst (Arg.imm 0, ()))) (Expr.jump Js.fst (Arg.imm 0, ())))
                  (Expr.jump Js.fst (Arg.imm 0, ()))) (Expr.jump Js.fst (Arg.imm 0, ())))
                                                            (Expr.jump Js.fst (Arg.imm 0, ())))
                                        (Expr.jump Js.fst (Arg.imm 0, ())))
                  (Expr.jump Jfl (Arg.imm 0, Arg.var p.fst, ())))
            Blocks.nil) fun Js => Expr.jump Js.fst (Arg.imm 0, ())) mOut := by
  have hcvO_le := hdwO.1.core_ok.cur_vars_le
  refine wp_loop_inv (ts := [i64])
    (fun (vi, ()) ml => vi.toNat ≤ sO.core.cur_vars ∧ ∃ flL : List (BitVec 32),
      flL.length = c.max_vars ∧
      (FullMem c { sO with core := { sO.core with flags := flL } } ⋆ R) ml)
    (fun (vi, ()) _ => sO.core.cur_vars - vi.toNat)
    (fun Jl hJl => by
      c0_hsteps_nogrp
      exact hJl (0#64, ()) mOut ⟨Nat.zero_le _, sO.core.flags, hdwO.1.core_ok.flags_len, hmO⟩)
    (fun Jl (vi, ()) ml ⟨hvi_le, flL, hflL, hml⟩ ihl => ?_)
  · c0_hsteps_nogrp
    · have hvi_lt : vi.toNat < sO.core.cur_vars := by
        have h1 : vi.toNat < cvP % 2 ^ 64 := by assumption
        rw [← hcvO, Nat.mod_eq_of_lt (by omega)] at h1; exact h1
      have hfl_lt : vi.toNat < flL.length := by rw [hflL]; omega
      have hvi_231 : vi.toNat < 2 ^ 31 := by omega
      have hval_lt : (vi <<< (1 : Nat)).toNat < sO.core.vals.length := by
        have hsh : (vi <<< (1 : Nat)).toNat = 2 * vi.toNat := by bv_omega
        rw [hsh, hdwO.1.core_ok.vals_len]; omega
      have hwvp_lt : (((vi <<< (1 : Nat)) <<< (1 : Nat)) + 1#64).toNat <
          sO.core.wvec.length := by
        have hsh : (((vi <<< (1 : Nat)) <<< (1 : Nat)) + 1#64).toNat = 4 * vi.toNat + 1 := by
          bv_omega
        rw [hsh, hdwO.1.core_ok.wvec_len]; omega
      have hwvn_lt : ((((vi <<< (1 : Nat)) ||| 1#64) <<< (1 : Nat)) + 1#64).toNat <
          sO.core.wvec.length := by
        rw [swp12a_bv64_wvec_neg_toNat vi (by omega), hdwO.1.core_ok.wvec_len]; omega
      have hvi1 : (vi + 1#64).toNat = vi.toNat + 1 := by bv_omega
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64]) (fun _ mf => ∃ flL' : List (BitVec 32),
          flL'.length = c.max_vars ∧
          (FullMem c { sO with core := { sO.core with flags := flL' } } ⋆ R) mf)
        (fun _ ⟨_li1, ⟨⟩⟩ mf ⟨flL', hflL', hmf⟩ => by
          c0_hsteps_nogrp
          exact ihl (vi + 1#64, ()) mf (by dsimp only; rw [hvi1]; omega)
            ⟨by rw [hvi1]; omega, flL', hflL', hmf⟩) ?_
      intro Jl1 hJl1
      c0_hsplit; rotate_left
      · c0_hsteps_nogrp; exact hJl1 (_, ()) ml ⟨flL, hflL, hml⟩
      refine wp_join_group (ts := [i64]) (fun _ mf2 => mf2 = ml)
        (fun _ ⟨_li2, ⟨⟩⟩ mf2 hm2 => by
          subst hm2; c0_hsteps_nogrp
          refine hJl1 (_, ()) _ ⟨_, ?_, by assumption⟩; rw [List.length_set, hflL])
        (fun _ hJl2 => by
          c0_hsplit; rotate_left
          · c0_hsteps_nogrp; exact hJl2 (_, ()) ml rfl
          c0_hsteps_nogrp
          c0_hsplit; rotate_left
          · c0_hsteps_nogrp; exact hJl2 (_, ()) ml rfl
          c0_hsplit; rotate_left
          · c0_hsteps_nogrp; exact hJl2 (_, ()) ml rfl
          c0_hsplit
          · c0_hsteps_nogrp; exact hJl2 (_, ()) ml rfl
          c0_hsplit; rotate_left
          · c0_hsteps_nogrp; exact hJl2 (_, ()) ml rfl
          · clear ihl; c0_hsteps_nogrp
            exact hJfl 1#64 vi ml ⟨flL, hflL, hml⟩)
    · clear ihl
      exact hJfl 0#64 vi ml ⟨flL, hflL, hml⟩

private theorem swp12a_eq_loop_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {sP2 : FullState}
    {R : Mem 64 → Prop} {mRt : Mem 64} {isz' nc qlen : Val i32} {cvP fuel0 : Nat}
    {J_out : Cont [i32]}
    (hmx : c.max_vars < 2 ^ 31)
    (hdwP2 : FullDenseInvW c F0 F_cur sP2)
    (hcvP2 : sP2.core.cur_vars = cvP)
    (hfuP2 : sP2.core.fuel.toNat ≤ fuel0)
    (htmkP2 : M6TmkZero sP2)
    (hnc_le : nc.toNat ≤ cvP)
    (hisz'_le : isz'.toNat ≤ cvP)
    (htrcP2_p : ∀ i < nc.toNat, (sP2.scratch.tarjan_reach[i]?.getD 0#32).toNat < cvP)
    (htrcP2_i : ∀ i < isz'.toNat, (sP2.scratch.tarjan_reach[cvP + i]?.getD 0#32).toNat < cvP)
    (hmRt : (FullMem c sP2 ⋆ R) mRt)
    (hJ_out : ∀ (isz_out : Val i32) (m_out : Mem 64),
      (isz_out.toNat ≤ cvP ∧ ∃ s_out : FullState,
        FullDenseInvW c F0 F_cur s_out ∧ s_out.core.cur_vars = cvP ∧
        s_out.core.fuel.toNat ≤ fuel0 ∧ M6TmkZero s_out ∧
        (∀ i < nc.toNat, (s_out.scratch.tarjan_reach[i]?.getD 0#32).toNat < cvP) ∧
        (∀ i < isz_out.toNat,
          (s_out.scratch.tarjan_reach[cvP + i]?.getD 0#32).toNat < cvP) ∧
        (FullMem c s_out ⋆ R) m_out) →
      J_out (isz_out, ()) m_out) :
    wp Γ Q X (Expr.group (sig := [[i32, i32]]) (fun Js =>
          Blocks.cons (fun p =>
              Expr.let_ (Op.mk (.cmp .ult i32 .bool rfl) (Arg.var p.snd.fst, Arg.var qlen, ()))
                fun p_1 => Expr.jnz (Arg.var p_1.fst)
                  (Expr.let_ (Op.mk (.zext 32 64) (Arg.var p.snd.fst, ())) fun p_2 => Expr.let_
                      (Op.mk (.cmp .ult i64 .bool rfl)
                        (Arg.var p_2.fst, Arg.var (BitVec.ofNat 64 cvP), ())) fun p_3 =>
                      Expr.jnz (Arg.var p_3.fst)
                        (Expr.let_ (Op.mk (.shl i32) (Arg.var p.snd.fst, Arg.imm 1, ())) fun p_4 =>
                          Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_4.fst, ())) fun p_5 =>
                            Expr.let_ (Op.mk (.mul i64) (Arg.var p_5.fst, Arg.imm 4, ())) fun p_6 =>
                              Expr.let_
                                (Op.mk (.add i64) (Arg.var c.pWorkStk2, Arg.var p_6.fst, ()))
                                fun p_7 => Expr.load i32 (Arg.var p_7.fst) fun ld =>
                                  Expr.group (sig := [[i32]]) (fun _Js_1 =>
                                      Blocks.cons (fun p_8 => Expr.let_
                                            (Op.mk (.add i32) (Arg.var p.snd.fst, Arg.imm 1, ()))
                                            fun p =>
                                            Expr.jump Js.fst (Arg.var p_8.fst, Arg.var p.fst, ()))
                                        Blocks.nil) fun Js =>
                                    Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld, ())) fun p_8 =>
                                      Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl)
                                          (Arg.var p_8.fst,
                                           Arg.var (BitVec.ofNat 64 cvP <<< (1 : Nat)), ()))
                                        fun p_9 => Expr.jnz (Arg.var p_9.fst)
                                          (Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld, ()))
                                            fun p_10 => Expr.let_
                                              (Op.mk (.mul i64) (Arg.var p_10.fst, Arg.imm 4, ()))
                                              fun p_11 => Expr.let_ (Op.mk (.add i64)
                                                  (Arg.var c.pRepr, Arg.var p_11.fst, ()))
                                                fun p_12 =>
                                                Expr.load i32 (Arg.var p_12.fst) fun ld =>
                                                  Expr.let_
                                                    (Op.mk (.lshr i32) (Arg.var ld, Arg.imm 1, ()))
                                                    fun p_13 => Expr.group (sig := [[i32]])
                                                      (fun _Js_1 =>
                                                        Blocks.cons (fun p =>
                                                            Expr.jump Js.fst (Arg.var p.fst, ()))
                                                          Blocks.nil) fun Js => Expr.let_
                                                        (Op.mk (.zext 32 64) (Arg.var p_13.fst, ()))
                                                        fun p_14 => Expr.let_
                                                          (Op.mk (.cmp .ult i64 .bool rfl)
                                                            (Arg.var p_14.fst,
                                                             Arg.var (BitVec.ofNat 64 cvP), ()))
                                                          fun p_15 =>
                                                          Expr.jnz (Arg.var p_15.fst) (Expr.let_
                                                              (Op.mk (.zext 32 64)
                                                                (Arg.var p_13.fst, ())) fun p_16 =>
                                                              Expr.let_ (Op.mk (.mul i64)
                                                                  (Arg.var p_16.fst, Arg.imm 4, ()))
                                                                fun p_17 => Expr.let_
                                                                  (Op.mk (.add i64)
                                                                    (Arg.var c.pFlags,
                                                                     Arg.var p_17.fst, ()))
                                                                  fun p_18 =>
                                                                  Expr.load i32 (Arg.var p_18.fst)
                                                                    fun ld => Expr.let_
                                                                      (Op.mk (.and i32)
                                                                        (Arg.var ld, Arg.imm 1, ()))
                                                                      fun p_19 => Expr.let_
                                                                        (Op.mk
                                                                          (.cmp .ne i32 .bool rfl)
                                                                          (Arg.var p_19.fst,
                                                                           Arg.imm 0, ()))
                                                                        fun p_20 =>
                                                                        Expr.jnz (Arg.var p_20.fst)
                                                                          (Expr.let_
                                                                            (Op.mk (.shl i32)
                                                                              (Arg.var p_13.fst,
                                                                               Arg.imm 1, ()))
                                                                            fun p_21 =>
                                                                            Expr.let_
                                                                              (Op.mk (.zext 32 64)
                                                                                (Arg.var p_21.fst,
                                                                                 ())) fun p_22 =>
                                                                              Expr.let_
                                                                                (Op.mk (.add i64)
                                                                                  (Arg.var c.pVals,
                                                                                   Arg.var p_22.fst,
                                                                                   ())) fun p_23 =>
                                                                                Expr.load i8
                                                                                  (Arg.var p_23.fst)
                                                                                  fun ld =>
                                                                                  Expr.let_
                                                                                    (Op.mk
                                                                                      (.trunc 32 8)
                                                                                      (Arg.imm 0,
                                                                                       ()))
                                                                                    fun p_24 =>
                                                                                    Expr.let_
                                                                                      (Op.mk
                                                                                        (.sext 8 32)
                                                                                        (Arg.var ld,
                                                                                         ()))
                                                                                      fun p_25 =>
                                                                                      Expr.let_
                                                                                        (Op.mk
                                                                                          (.sext 8
                                                                                            32)
                                                                                          (Arg.var
                p_24.fst, ())) fun p_26 => Expr.let_ (Op.mk (.cmp .eq i32 .bool rfl) (Arg.var
                  p_25.fst, Arg.var p_26.fst, ())) fun p_27 => Expr.jnz (Arg.var p_27.fst)
                (Expr.group (sig := [[i32]]) (fun _Js_1 =>
                Blocks.cons (fun p =>
                Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_13.fst, ())) fun p_28 =>
                  Expr.let_ (Op.mk (.mul i64) (Arg.var p_28.fst, Arg.imm 4, ())) fun p_29 =>
                Expr.let_ (Op.mk (.add i64) (Arg.var c.pFlags, Arg.var p_29.fst, ())) fun p_30 =>
                  Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_13.fst, ())) fun p_31 =>
                Expr.let_ (Op.mk (.mul i64) (Arg.var p_31.fst, Arg.imm 4, ())) fun p_32 =>
                  Expr.let_ (Op.mk (.add i64) (Arg.var c.pFlags, Arg.var p_32.fst, ())) fun p_33 =>
                Expr.load i32 (Arg.var p_33.fst) fun ld =>
                  Expr.let_ (Op.mk (.or i32) (Arg.var ld, Arg.imm 1024, ())) fun p_34 =>
                Expr.let_ (Op.mk (.or i32) (Arg.var p_34.fst, Arg.imm 536870912, ())) fun p_35 =>
                  Expr.store (Arg.var p_35.fst) (Arg.var p_30.fst)
                (Expr.jump Js.fst (Arg.var p.fst, ())))
                  Blocks.nil) fun Js => Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_13.fst, ()))
                fun p_28 => Expr.let_ (Op.mk (.mul i64) (Arg.var p_28.fst, Arg.imm 4, ()))
                  fun p_29 => Expr.let_ (Op.mk (.add i64) (Arg.var c.pFlags, Arg.var p_29.fst,
                   ())) fun p_30 => Expr.load i32 (Arg.var p_30.fst) fun ld => Expr.let_ (Op.mk
                  (.and i32) (Arg.var ld, Arg.imm 536870912, ())) fun p_31 => Expr.let_ (Op.mk
                (.cmp .eq i32 .bool rfl) (Arg.var p_31.fst, Arg.imm 0, ())) fun p_32 => Expr.jnz
                (Arg.var p_32.fst) (Expr.let_ (Op.mk (.zext 32 64) (Arg.var p.fst, ()))
                  fun p_33 => Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl) (Arg.var p_33.fst,
                   Arg.var (BitVec.ofNat 64 cvP), ())) fun p_34 => Expr.jnz (Arg.var p_34.fst)
                  (Expr.let_ (Op.mk (.zext 32 64) (Arg.var p.fst, ())) fun p_35 => Expr.let_
                  (Op.mk (.add i64) (Arg.var (BitVec.ofNat 64 cvP), Arg.var p_35.fst, ()))
                  fun p_36 => Expr.let_ (Op.mk (.mul i64) (Arg.var p_36.fst, Arg.imm 4, ()))
                fun p_37 => Expr.let_ (Op.mk (.add i64) (Arg.var c.pTarjanReach,
                 Arg.var p_37.fst, ())) fun p_38 => Expr.store (t := i32) (Arg.var p_13.fst)
                (Arg.var p_38.fst) (Expr.let_ (Op.mk (.add i32) (Arg.var p.fst, Arg.imm 1, ()))
                  fun p => Expr.jump Js.fst (Arg.var p.fst, ())))
                  (Expr.jump Js.fst (Arg.var p.fst, ())))
                (Expr.jump Js.fst (Arg.var p.fst, ()))) (Expr.jump Js.fst (Arg.var p.fst, ())))
                                                                          (Expr.jump Js.fst
                                                                            (Arg.var p.fst, ())))
                                                            (Expr.jump Js.fst (Arg.var p.fst, ())))
                                          (Expr.jump Js.fst (Arg.var p.fst, ())))
                        (Expr.jump J_out (Arg.var p.fst, ())))
                  (Expr.jump J_out (Arg.var p.fst, ())))
            Blocks.nil) fun Js => Expr.jump Js.fst (Arg.var isz', Arg.imm 0, ())) mRt := by
  refine wp_loop_inv (ts := [i32, i32])
    (fun (iszE, ei, ()) mEq =>
      iszE.toNat ≤ cvP ∧ ∃ sEq : FullState,
        FullDenseInvW c F0 F_cur sEq ∧ sEq.core.cur_vars = cvP ∧
        sEq.core.fuel.toNat ≤ fuel0 ∧ M6TmkZero sEq ∧
        (∀ i < nc.toNat, (sEq.scratch.tarjan_reach[i]?.getD 0#32).toNat < cvP) ∧
        (∀ i < iszE.toNat, (sEq.scratch.tarjan_reach[cvP + i]?.getD 0#32).toNat < cvP) ∧
        (FullMem c sEq ⋆ R) mEq)
    (fun (_, ei, ()) _ => sP2.core.cur_vars - ei.toNat)
    (fun Je hJe => by
      c0_hsteps_nogrp
      exact hJe (isz', 0#32, ()) mRt
        ⟨hisz'_le, sP2, hdwP2, hcvP2, hfuP2, htmkP2, htrcP2_p, htrcP2_i, hmRt⟩)
    (fun Je (iszE, ei, ()) mEq
        ⟨hiszE_le, sEq, hdwEq, hcvEq, hfuEq, htmkEq, htrcEq_p, htrcEq_i, hmEq⟩ ihe => ?_)
  · have hcvEq_le := hdwEq.1.core_ok.cur_vars_le
    have h2cvEq_32 : 2 * sEq.core.cur_vars < 2 ^ 32 :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 2 hcvEq_le)
        (Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hmx (by decide)) (by decide))
    have hcvEq_32 : sEq.core.cur_vars < 2 ^ 32 :=
      Nat.lt_of_le_of_lt hcvEq_le (Nat.lt_trans hmx (by decide))
    have hcvEq_64 : sEq.core.cur_vars < 2 ^ 64 := Nat.lt_trans hcvEq_32 (by decide)
    have hcvP_64 : cvP < 2 ^ 64 := hcvEq ▸ hcvEq_64
    have h2cvP_32 : 2 * cvP < 2 ^ 32 := hcvEq ▸ h2cvEq_32
    have hnc_le_cv : nc.toNat ≤ sEq.core.cur_vars := hcvEq.symm ▸ hnc_le
    c0_hsteps_nogrp
    · have hei_lt : ei.toNat < sEq.core.cur_vars := by
        have h1 : ei.toNat < cvP % 2 ^ 64 := by assumption
        rw [Nat.mod_eq_of_lt hcvP_64, ← hcvEq] at h1; exact h1
      have hei_2_lt_32 : ei.toNat * 2 < 2 ^ 32 := by
        rw [Nat.mul_comm]
        exact Nat.lt_trans (Nat.mul_lt_mul_of_pos_left hei_lt (by decide)) h2cvEq_32
      have hsh_ei : (BitVec.setWidth 64 (ei <<< (1 : Nat))).toNat = 2 * ei.toNat := by
        rw [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
          Nat.mod_eq_of_lt hei_2_lt_32,
          Nat.mod_eq_of_lt (Nat.lt_trans hei_2_lt_32 (by decide))]
        exact Nat.mul_comm ei.toNat 2
      have hws2_lt : (BitVec.setWidth 64 (ei <<< (1 : Nat))).toNat <
          sEq.scratch.work_stk2.length := by
        rw [hsh_ei, hdwEq.1.scratch_ok.work_stk2_len]
        exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hei_lt (by decide))
          (Nat.mul_le_mul_left 2 hcvEq_le)
      have hei1 : (ei + 1#32).toNat = ei.toNat + 1 := by
        rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hei_lt hcvEq_32)]
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i32]) (fun (isz', ()) mEq' =>
          isz'.toNat ≤ cvP ∧ ∃ sEq' : FullState,
            FullDenseInvW c F0 F_cur sEq' ∧ sEq'.core.cur_vars = cvP ∧
            sEq'.core.fuel.toNat ≤ fuel0 ∧ M6TmkZero sEq' ∧
            (∀ i < nc.toNat, (sEq'.scratch.tarjan_reach[i]?.getD 0#32).toNat < cvP) ∧
            (∀ i < isz'.toNat, (sEq'.scratch.tarjan_reach[cvP + i]?.getD 0#32).toNat < cvP) ∧
            (FullMem c sEq' ⋆ R) mEq') ?_ ?_
      · rintro _ ⟨isz', ⟨⟩⟩ mEq' hInv'
        c0_hsteps_nogrp
        exact ihe (isz', ei + 1#32, ()) mEq'
          (by dsimp only; rw [hei1]; exact swp_sub1_lt (by rw [hcvP2, ← hcvEq]; exact hei_lt))
          hInv'
      · intro _ hJe_next
        c0_hstraight
        c0_hsplit
        · have hlit_lt : (sEq.scratch.work_stk2[(BitVec.setWidth 64
              (ei <<< (1 : Nat))).toNat]'hws2_lt).toNat < sEq.core.cur_vars * 2 := by
            have hsh_ei32 : (ei <<< (1 : Nat)).toNat = 2 * ei.toNat := by
              rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one,
                Nat.mod_eq_of_lt hei_2_lt_32]; exact Nat.mul_comm ei.toNat 2
            have hws2_lt2 : (ei <<< (1 : Nat)).toNat < sEq.scratch.work_stk2.length := by
              rw [hsh_ei32, ← hsh_ei]; exact hws2_lt
            have h1 : (sEq.scratch.work_stk2[(ei <<< (1 : Nat)).toNat]'hws2_lt2).toNat <
                2 * (cvP % 2 ^ 64) % 2 ^ 64 := by assumption
            rw [Nat.mod_eq_of_lt hcvP_64, Nat.mod_eq_of_lt (Nat.lt_trans h2cvP_32 (by decide)),
              ← hcvEq, Nat.mul_comm] at h1
            simpa only [hsh_ei, hsh_ei32] using h1
          have hrp_lt : (BitVec.setWidth 64 (sEq.scratch.work_stk2[
              (BitVec.setWidth 64 (ei <<< (1 : Nat))).toNat]'hws2_lt)).toNat <
              sEq.core.repr.length := by
            rw [BitVec.toNat_setWidth,
              Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide)),
              hdwEq.1.core_ok.repr_len]
            exact Nat.lt_of_lt_of_le hlit_lt
              (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left 2 hcvEq_le)
          c0_hstraight
          refine wp_join_group (ts := [i32]) (fun (iszR, ()) mR =>
              iszR.toNat ≤ cvP ∧ ∃ sR : FullState,
                FullDenseInvW c F0 F_cur sR ∧ sR.core.cur_vars = cvP ∧
                sR.core.fuel.toNat ≤ fuel0 ∧ M6TmkZero sR ∧
                (∀ i < nc.toNat, (sR.scratch.tarjan_reach[i]?.getD 0#32).toNat < cvP) ∧
                (∀ i < iszR.toNat, (sR.scratch.tarjan_reach[cvP + i]?.getD 0#32).toNat < cvP) ∧
                (FullMem c sR ⋆ R) mR) ?_ ?_
          · rintro _ ⟨iszR, ⟨⟩⟩ mR
              ⟨hiszR_le, sR, hdwR, hcvR, hfuR, htmkR, htrcR_p, htrcR_i, hmR⟩
            c0_hstraight
            exact hJe_next (iszR, ()) mR
              ⟨hiszR_le, sR, hdwR, hcvR, hfuR, htmkR, htrcR_p, htrcR_i, hmR⟩
          intro _ hJe_r
          c0_hstraight
          c0_hsplit
          · let rv := (sEq.core.repr[(BitVec.setWidth 64 (sEq.scratch.work_stk2[(BitVec.setWidth 64
              (ei <<< (1 : Nat))).toNat]'hws2_lt)).toNat]'hrp_lt : BitVec 32) >>> (1 : Nat)
            have hrv_lt : rv.toNat < sEq.core.cur_vars := by
              rw [swp_bv32_shr1]
              have h1 : (sEq.core.repr[(BitVec.setWidth 64
                  (sEq.scratch.work_stk2[(BitVec.setWidth 64 (ei <<< (1 : Nat))).toNat]'hws2_lt
                  )).toNat]'hrp_lt).toNat / 2 < cvP % 2 ^ 64 := by assumption
              rw [Nat.mod_eq_of_lt hcvP_64, ← hcvEq] at h1; exact h1
            have hfl_rv64 : (BitVec.setWidth 64 rv).toNat < sEq.core.flags.length := by
              rw [BitVec.toNat_setWidth,
                Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide)),
                hdwEq.1.core_ok.flags_len]
              exact Nat.lt_of_lt_of_le hrv_lt hcvEq_le
            c0_hstraight
            exact swp12a_eq_push_step_wp hmx hdwEq hcvEq hfuEq htmkEq hnc_le_cv
              hiszE_le htrcEq_p htrcEq_i hmEq hrv_lt hfl_rv64 hJe_r
          · c0_hstraight
            exact hJe_r (iszE, ()) mEq
              ⟨hiszE_le, sEq, hdwEq, hcvEq, hfuEq, htmkEq, htrcEq_p, htrcEq_i, hmEq⟩
        · exact hJe_next (iszE, ()) mEq
            ⟨hiszE_le, sEq, hdwEq, hcvEq, hfuEq, htmkEq, htrcEq_p, htrcEq_i, hmEq⟩
    · clear ihe
      exact hJ_out iszE _
        ⟨hiszE_le, sEq, hdwEq, hcvEq, hfuEq, htmkEq, htrcEq_p, htrcEq_i, hmEq⟩
    · clear ihe
      exact hJ_out iszE _
        ⟨hiszE_le, sEq, hdwEq, hcvEq, hfuEq, htmkEq, htrcEq_p, htrcEq_i, hmEq⟩

private theorem swp12a_pre_mark_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {sc' : FullState}
    {R : Mem 64 → Prop} {mc : Mem 64} {max_occ' : Val i64} {nm' : Val .bool} {cvP : Nat}
    {Jm : Cont []}
    (hmx : c.max_vars < 2 ^ 31)
    (hdwC : FullDenseInvW c F0 F_cur sc')
    (hcvC : sc'.core.cur_vars = cvP)
    (htmkC : M6TmkZero sc')
    (hmc : (FullMem c sc' ⋆ R) mc)
    (hJm : ∀ xs mM, (∃ sM : FullState, FullDenseInvW c F0 F_cur sM ∧ sM.core.cur_vars = cvP ∧
      sM.core.fuel = sc'.core.fuel ∧ M6TmkZero sM ∧ (FullMem c sM ⋆ R) mM) → Jm xs mM) :
    wp Γ Q X (Expr.jnz (Arg.var nm') (Expr.group (sig := [[i64]]) (fun Js =>
            Blocks.cons (fun p => Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl)
                    (Arg.var p.fst, Arg.var (BitVec.ofNat 64 cvP), ())) fun p_1 =>
                  Expr.jnz (Arg.var p_1.fst) (Expr.group (sig := [[]]) (fun _Js_1 =>
                        Blocks.cons (fun _p_2 =>
                            Expr.let_ (Op.mk (.add i64) (Arg.var p.fst, Arg.imm 1, ())) fun p =>
                              Expr.jump Js.fst (Arg.var p.fst, ()))
                          Blocks.nil) fun Js => Expr.group (sig := [[]]) (fun _Js_1 =>
                          Blocks.cons (fun _p_2 =>
                              Expr.let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p_3 =>
                                Expr.let_ (Op.mk (.add i64) (Arg.var c.pFlags, Arg.var p_3.fst, ()))
                                  fun p_4 =>
                                  Expr.let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ()))
                                    fun p => Expr.let_
                                      (Op.mk (.add i64) (Arg.var c.pFlags, Arg.var p.fst, ()))
                                      fun p => Expr.load i32 (Arg.var p.fst) fun ld => Expr.let_
                                          (Op.mk (.or i32) (Arg.imm 1024, Arg.imm 1073741824, ()))
                                          fun p => Expr.let_
                                            (Op.mk (.or i32) (Arg.var p.fst, Arg.imm 536870912, ()))
                                            fun p =>
                Expr.let_ (Op.mk (.not i32) (Arg.var p.fst, ())) fun p => Expr.let_
                                                (Op.mk (.and i32) (Arg.var ld, Arg.var p.fst, ()))
                                                fun p =>
                                                Expr.store (Arg.var p.fst) (Arg.var p_4.fst)
                                                  (Expr.jump Js.fst ()))
                            Blocks.nil) fun Js_1 =>
                        Expr.let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p_2 =>
                          Expr.let_ (Op.mk (.add i64) (Arg.var c.pFlags, Arg.var p_2.fst, ()))
                            fun p_3 => Expr.load i32 (Arg.var p_3.fst) fun ld =>
                              Expr.let_ (Op.mk (.and i32) (Arg.var ld, Arg.imm 1, ())) fun p_4 =>
                                Expr.let_
                                  (Op.mk (.cmp .ne i32 .bool rfl) (Arg.var p_4.fst, Arg.imm 0, ()))
                                  fun p_5 => Expr.jnz (Arg.var p_5.fst)
                                    (Expr.let_ (Op.mk (.sext 32 64) (Arg.imm 1, ())) fun p_6 =>
                                      Expr.let_
                                        (Op.mk (.shl i64) (Arg.var p.fst, Arg.var p_6.fst, ()))
                                        fun p_7 => Expr.let_
                                          (Op.mk (.add i64) (Arg.var c.pVals, Arg.var p_7.fst, ()))
                                          fun p_8 => Expr.load i8 (Arg.var p_8.fst) fun ld =>
                                            Expr.let_ (Op.mk (.trunc 32 8) (Arg.imm 0, ()))
                                              fun p_9 =>
                                              Expr.let_ (Op.mk (.sext 8 32) (Arg.var ld, ()))
                                                fun p_10 =>
                                                Expr.let_ (Op.mk (.sext 8 32) (Arg.var p_9.fst, ()))
                                                  fun p_11 => Expr.let_
                                                    (Op.mk (.cmp .eq i32 .bool rfl)
                                                      (Arg.var p_10.fst, Arg.var p_11.fst, ()))
                                                    fun p_12 => Expr.jnz (Arg.var p_12.fst)
                                                      (Expr.let_
                                                        (Op.mk (.sext 32 64) (Arg.imm 1, ()))
                                                        fun p_13 => Expr.let_ (Op.mk (.shl i64)
                                                            (Arg.var p.fst, Arg.var p_13.fst, ()))
                                                          fun p_14 => Expr.let_
                                                            (Op.mk (.sext 32 64) (Arg.imm 1, ()))
                                                            fun p_15 => Expr.let_
                                                              (Op.mk (.shl i64)
                                                                (Arg.var p_14.fst, Arg.var p_15.fst,
                                                                 ())) fun p_16 => Expr.let_
                                                                (Op.mk (.add i64)
                                                                  (Arg.var p_16.fst, Arg.imm 1, ()))
                                                                fun p_17 => Expr.let_
                                                                  (Op.mk (.mul i64)
                                                                    (Arg.var p_17.fst, Arg.imm 4,
                                                                     ())) fun p_18 => Expr.let_
                                                                    (Op.mk (.add i64)
                                                                      (Arg.var c.pWvec,
                                                                       Arg.var p_18.fst, ()))
                                                                    fun p_19 => Expr.load i32
                                                                      (Arg.var p_19.fst) fun ld =>
                                                                      Expr.let_
                                                                        (Op.mk (.zext 32 64)
                                                                          (Arg.var ld, ()))
                                                                        fun p_20 => Expr.let_
                                                                          (Op.mk (.sext 32 64)
                                                                            (Arg.imm 1, ()))
                                                                          fun p_21 => Expr.let_
                                                                            (Op.mk (.shl i64)
                                                                              (Arg.var p.fst,
                                                                               Arg.var p_21.fst,
                                                                               ())) fun p_22 =>
                                                                            Expr.let_
                                                                              (Op.mk (.or i64)
                                                                                (Arg.var p_22.fst,
                                                                                 Arg.imm 1, ()))
                                                                              fun p_23 =>
                                                                              Expr.let_
                                                                                (Op.mk (.sext 32 64)
                                                                                  (Arg.imm 1, ()))
                                                                                fun p_24 =>
                                                                                Expr.let_
                                                                                  (Op.mk (.shl i64)
                                                                                    (Arg.var
                                                                                       p_23.fst,
                                                                                     Arg.var
                                                                                       p_24.fst,
                 ())) fun p_25 => Expr.let_ (Op.mk (.add i64) (Arg.var p_25.fst, Arg.imm 1, ()))
                                                                                    fun p_26 =>
                                                                                    Expr.let_
                                                                                      (Op.mk
                                                                                        (.mul i64)
                                                                                        (Arg.var
                                                                                          p_26.fst,
                                                                                         Arg.imm 4,
                                                                                         ()))
                                                                                      fun p_27 =>
                                                                                      Expr.let_
                                                                                        (Op.mk
                                                                                          (.add i64)
                                                                                          (Arg.var
                                                                                            c.pWvec,
                                                                                           Arg.var
                p_27.fst, ())) fun p_28 => Expr.load i32 (Arg.var p_28.fst) fun ld => Expr.let_
                                                                                            (Op.mk
                                                                                              (.zext
                                                                                                32
                                                                                                64)
                  (Arg.var ld, ())) fun p_29 => Expr.group (sig := [[]]) (fun _Js_2 =>
                Blocks.cons (fun _p => Expr.jump Js.fst ())
                  Blocks.nil) fun Js => Expr.group (sig := [[]]) (fun _Js_2 =>
                  Blocks.cons (fun _p_30 =>
                  Expr.let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p_31 =>
                Expr.let_ (Op.mk (.add i64) (Arg.var c.pFlags, Arg.var p_31.fst, ())) fun p_32 =>
                  Expr.let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
                Expr.let_ (Op.mk (.add i64) (Arg.var c.pFlags, Arg.var p.fst, ())) fun p =>
                  Expr.load i32 (Arg.var p.fst) fun ld =>
                Expr.let_ (Op.mk (.or i32) (Arg.imm 1024, Arg.imm 1073741824, ())) fun p =>
                  Expr.let_ (Op.mk (.or i32) (Arg.var p.fst, Arg.imm 536870912, ())) fun p =>
                Expr.let_ (Op.mk (.not i32) (Arg.var p.fst, ())) fun p =>
                  Expr.let_ (Op.mk (.and i32) (Arg.var ld, Arg.var p.fst, ())) fun p =>
                Expr.store (Arg.var p.fst) (Arg.var p_32.fst) (Expr.jump Js.fst ()))
                Blocks.nil) fun Js_2 => Expr.let_ (Op.mk (.cmp .ugt i64 .bool rfl)
                (Arg.var p_20.fst, Arg.imm 0, ())) fun p_30 => Expr.jnz (Arg.var p_30.fst)
                (Expr.let_ (Op.mk (.cmp .ugt i64 .bool rfl) (Arg.var p_29.fst, Arg.imm 0, ()))
                  fun p_31 => Expr.jnz (Arg.var p_31.fst) (Expr.let_
                  (Op.mk (.cmp .ule i64 .bool rfl) (Arg.var p_20.fst, Arg.var max_occ', ()))
                  fun p_32 => Expr.jnz (Arg.var p_32.fst) (Expr.let_
                  (Op.mk (.cmp .ule i64 .bool rfl) (Arg.var p_29.fst, Arg.var max_occ', ()))
                  fun p_33 => Expr.jnz (Arg.var p_33.fst)
                (Expr.let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p_34 =>
                  Expr.let_ (Op.mk (.add i64) (Arg.var c.pFlags, Arg.var p_34.fst, ())) fun p_35 =>
                Expr.let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
                  Expr.let_ (Op.mk (.add i64) (Arg.var c.pFlags, Arg.var p.fst, ())) fun p =>
                Expr.load i32 (Arg.var p.fst) fun ld =>
                  Expr.let_ (Op.mk (.not i32) (Arg.imm 536870912, ())) fun p =>
                Expr.let_ (Op.mk (.and i32) (Arg.var ld, Arg.var p.fst, ())) fun p =>
                  Expr.let_ (Op.mk (.or i32) (Arg.var p.fst, Arg.imm 1024, ())) fun p =>
                Expr.let_ (Op.mk (.or i32) (Arg.var p.fst, Arg.imm 1073741824, ())) fun p =>
                  Expr.store (Arg.var p.fst) (Arg.var p_35.fst) (Expr.jump Js.fst ()))
                (Expr.jump Js_2.fst ())) (Expr.jump Js_2.fst ())) (Expr.jump Js_2.fst ()))
                (Expr.jump Js_2.fst ())) (Expr.jump Js_1.fst ())) (Expr.jump Js_1.fst ()))
                  (Expr.let_ (Op.mk (.zext 32 64) (Arg.imm 29, ())) fun p =>
                    Expr.let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
                      Expr.let_ (Op.mk (.add i64) (Arg.var c.pGlueUsed, Arg.var p.fst, ())) fun p =>
                        Expr.store (t := i32) (Arg.imm 1) (Arg.var p.fst)
                          (Expr.let_ (Op.mk (.zext 32 64) (Arg.imm 30, ())) fun p =>
                            Expr.let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
                              Expr.let_
                                (Op.mk (.add i64) (Arg.var c.pGlueUsed, Arg.var p.fst, ())) fun p =>
                                Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
                                  (Expr.jump Jm ()))))
            Blocks.nil) fun Js => Expr.jump Js.fst (Arg.imm 0, ())) (Expr.jump Jm ())) mc := by
  c0_hsplit
  · c0_hsteps_nogrp
    have hcvC_le := hdwC.1.core_ok.cur_vars_le
    refine wp_loop_inv
      (fun (v, ()) mv => v.toNat ≤ sc'.core.cur_vars ∧ ∃ fl' : List (BitVec 32),
        fl'.length = c.max_vars ∧
        (FullMem c { sc' with core := { sc'.core with flags := fl' } } ⋆ R) mv)
      (fun (v, ()) _ => sc'.core.cur_vars - v.toNat)
      (fun Jv hJv => by
        c0_hsteps_nogrp
        exact hJv (0#64, ()) mc ⟨Nat.zero_le _, sc'.core.flags, hdwC.1.core_ok.flags_len, hmc⟩)
      (fun Jv (v, ()) mv ⟨hv_le, fl', hfl', hmv⟩ ihv => ?_)
    · c0_hsteps_nogrp
      · have hv_lt : v.toNat < sc'.core.cur_vars := by
          have h1 : v.toNat < cvP % 2 ^ 64 := by assumption
          rw [← hcvC, Nat.mod_eq_of_lt (by omega)] at h1; exact h1
        have hfl_lt : v.toNat < fl'.length := by rw [hfl']; omega
        have hv_231 : v.toNat < 2 ^ 31 := by omega
        have hval_lt : (v <<< (1 : Nat)).toNat < sc'.core.vals.length := by
          have hsh : (v <<< (1 : Nat)).toNat = 2 * v.toNat := by bv_omega
          rw [hsh, hdwC.1.core_ok.vals_len]; omega
        have hwvp_lt : (((v <<< (1 : Nat)) <<< (1 : Nat)) + 1#64).toNat <
            sc'.core.wvec.length := by
          have hsh : (((v <<< (1 : Nat)) <<< (1 : Nat)) + 1#64).toNat = 4 * v.toNat + 1 := by
            bv_omega
          rw [hsh, hdwC.1.core_ok.wvec_len]; omega
        have hwvn_lt : ((((v <<< (1 : Nat)) ||| 1#64) <<< (1 : Nat)) + 1#64).toNat <
            sc'.core.wvec.length := by
          rw [swp12a_bv64_wvec_neg_toNat v (by omega), hdwC.1.core_ok.wvec_len]; omega
        have hv1 : (v + 1#64).toNat = v.toNat + 1 := by bv_omega
        refine wp_join_group (ts := [])
          (fun () mv1 => ∃ fl1 : List (BitVec 32), fl1.length = c.max_vars ∧
            (FullMem c { sc' with core := { sc'.core with flags := fl1 } } ⋆ R) mv1)
          (fun _ () mv1 ⟨fl1, hfl1, hmv1⟩ => by
            c0_hsteps_nogrp
            exact ihv (v + 1#64, ()) mv1 (by dsimp only; rw [hv1]; omega)
              ⟨by rw [hv1]; omega, fl1, hfl1, hmv1⟩)
          (fun _ hJv1 => by
            refine wp_join_group (ts := []) (fun () m30 => m30 = mv)
              (fun _ () m30 hm30 => by
                subst hm30; c0_hsteps_nogrp
                refine hJv1 () _ ⟨_, ?_, by assumption⟩; simp [hfl'])
              (fun _ hJ30 => by
                c0_hsplit; rotate_left
                · c0_hsteps_nogrp; exact hJ30 () mv rfl
                c0_hsplit; rotate_left
                · c0_hsteps_nogrp; exact hJ30 () mv rfl
                c0_hsteps_nogrp
                refine wp_join_group (ts := [])
                  (fun () m36 => ∃ fl1 : List (BitVec 32), fl1.length = c.max_vars ∧
                    (FullMem c { sc' with core := { sc'.core with flags := fl1 } } ⋆ R) m36)
                  (fun _ () m36 h => by c0_hsteps_nogrp; exact hJv1 () m36 h)
                  (fun _ hJ36 => by
                    refine wp_join_group (ts := []) (fun () m38 => m38 = mv)
                      (fun _ () m38 hm38 => by
                        subst hm38; c0_hsteps_nogrp
                        refine hJ36 () _ ⟨_, ?_, by assumption⟩; simp [hfl'])
                      (fun _ hJ38 => by
                        c0_hsplit; rotate_left
                        · c0_hsteps_nogrp; exact hJ38 () mv rfl
                        c0_hsplit; rotate_left
                        · c0_hsteps_nogrp; exact hJ38 () mv rfl
                        c0_hsplit; rotate_left
                        · c0_hsteps_nogrp; exact hJ38 () mv rfl
                        c0_hsplit; rotate_left
                        · c0_hsteps_nogrp; exact hJ38 () mv rfl
                        c0_hsteps_nogrp
                        refine hJ36 () _ ⟨_, ?_, by assumption⟩; simp [hfl']))))
      · have hgu29 : (29 : BitVec 64).toNat < sc'.scratch.glue_used.length := by
          rw [hdwC.1.scratch_ok.glue_used_len]; decide
        c0_hsteps_nogrp
        have hgu1 : (sc'.scratch.glue_used.set (29 : BitVec 64).toNat 1#32).length = 64 := by
          simp [hdwC.1.scratch_ok.glue_used_len]
        have hgu30 : (30 : BitVec 64).toNat <
            (sc'.scratch.glue_used.set (29 : BitVec 64).toNat 1#32).length := by
          rw [hgu1]; decide
        c0_hsteps_nogrp
        have hdw' := swp_set_gu_inv (swp_set_fl_inv hdwC hfl')
          (by simp [hdwC.1.scratch_ok.glue_used_len] :
            ((sc'.scratch.glue_used.set (29 : BitVec 64).toNat 1#32).set
              (30 : BitVec 64).toNat 0#32).length = 64)
        exact hJm () _ ⟨_, hdw', hcvC, rfl, fid_tmkZero_congr htmkC rfl rfl, by assumption⟩
  · c0_hsteps_nogrp
    exact hJm () mc ⟨sc', hdwC, hcvC, rfl, htmkC, hmc⟩

/-- Step-12A `full_m6_sweep_vars` tracks actual `swept` variable count in `glue_used[32]`
and preserves `m6SweepVarsSpec`. -/
theorem full_m6_sweep_vars_step12a_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hDP : M6EnvSpec Γ "full_m6_dense_prop" m6DensePropSpec)
    (hCol : M6EnvSpec Γ "full_m6_collect_cands" m6CollectCandsSpec)
    (hSV : M6EnvSpec Γ "full_m6_sweep_var" m6SweepVarSpec) :
    ∀ args m Q X, m6SweepVarsSpec args m Q X →
      Func.wp Γ full_m6_sweep_vars_body args m Q X := by
  rintro ⟨h, budget, tlim, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, htmk, hm, hQ⟩
  unfold Func.wp full_m6_sweep_vars_body
  have hmx := maxVars_lt_2p31 c
  have hlen := hinv.lengths
  have hgu32_len : 32 < s.scratch.glue_used.length := by
    rw [hlen.scratch_ok.glue_used_len]; decide
  have hcap_lt64 : c.scratch_cap < 2 ^ 64 := Nat.lt_trans c.hscr (by unfold dimacsBound; decide)
  c0_hsteps_nogrp
  let s0 : FullState :=
    { s with scratch := { s.scratch with glue_used := s.scratch.glue_used.set 32 0#32 } }
  let sc0_ok := hlen.scratch_ok
  have hlen0 : s0.LengthsOk c :=
    ⟨hlen.core_ok, { sc0_ok with glue_used_len := (by rw [List.length_set, sc0_ok.glue_used_len]) }⟩
  have hinv0 : FullDenseInv c F0 s0 := hinv.of_safetySlice hlen0 rfl ⟨rfl, rfl⟩
  have htmk0 : M6TmkZero s0 := htmk
  refine fid_call_max_v_cap hMaxV (cap := BitVec.ofNat 64 c.scratch_cap) ?_
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap_lt64]
  c0_hsplit
  · c0_hsteps_nogrp
    exact hQ 1#64 s0 _ hinv0 rfl (Nat.le_refl _) htmk0 (Or.inl rfl) (fun h => by simp at h)
      (by assumption)
  have hcap_ge : k6MinScr ≤ c.scratch_cap := by
    rcases Nat.lt_or_ge c.scratch_cap k6MinScr with hlt | hle
    · exfalso
      have h0 := k6MaxV_eq_zero hlt
      have h1 : (BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap))) = 0#32 := by
        rw [h0]; rfl
      exact (by assumption : _ ≠ 0#32) h1
    · exact hle
  c0_hsplit
  · c0_hsteps_nogrp
    exact hQ 1#64 s0 _ hinv0 rfl (Nat.le_refl _) htmk0 (Or.inl rfl) (fun h => by simp at h)
      (by assumption)
  c0_hsplit
  · c0_hsteps_nogrp
    exact hQ 1#64 s0 _ hinv0 rfl (Nat.le_refl _) htmk0 (Or.inl rfl) (fun h => by simp at h)
      (by assumption)
  obtain ⟨F_cur, hdw0⟩ := hinv0.exists_witness
  refine fid_call_dense_prop hDP hdw0 (by assumption)
    fun okP sP mP hdwP hcvP hfuP htmkP _ hokP hnoP hmP => ?_
  have htmkP' : M6TmkZero sP := fid_tmkZero_congr htmk0 hcvP htmkP
  c0_hsplit
  rotate_left
  · have hok_f : okP = false := by cases okP; rfl; simp at *
    c0_hsteps_nogrp
    exact hQ 20#64 sP mP (fid_denseInv_of_W hdwP) hcvP (by rw [hfuP]; exact Nat.le_refl _)
      htmkP' (Or.inr rfl) (fun _ => (hnoP hok_f).1) hmP
  clear hMaxV hokP hnoP
  c0_hsteps_nogrp
  c0_hsplit
  · c0_hsteps_nogrp
    exact hQ 1#64 sP mP (fid_denseInv_of_W hdwP) hcvP (by rw [hfuP]; exact Nat.le_refl _)
      htmkP' (Or.inl rfl) (fun h => by simp at h) hmP
  have hcvP_pos : 0 < sP.core.cur_vars := by
    have h1 : sP.core.cur_vars % 2 ^ 64 ≠ 0 := by
      intro hz; apply (by assumption : BitVec.ofNat 64 sP.core.cur_vars ≠ 0#64)
      apply BitVec.eq_of_toNat_eq; simpa using hz
    exact Nat.pos_of_ne_zero fun h0 => h1 (by simp [h0])
  have hcvP_le : sP.core.cur_vars ≤ c.max_vars := hdwP.1.core_ok.cur_vars_le
  have hgu28P : 28 < sP.scratch.glue_used.length := by
    rw [hdwP.1.scratch_ok.glue_used_len]; decide
  have hgu29P : 29 < sP.scratch.glue_used.length := by
    rw [hdwP.1.scratch_ok.glue_used_len]; decide
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i32]) (fun (comp0, ()) mC0 =>
      comp0 = comp0 ∧ (FullMem c sP ⋆ R) mC0)
    ?_ (fun _ hJC0 => by
      c0_hsplit <;> (c0_hsteps_nogrp; exact hJC0 (_, ()) mP ⟨rfl, hmP⟩))
  rintro _ ⟨comp0, ⟨⟩⟩ mC0 ⟨_, hmC0⟩
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i32, i64, .bool]) (fun _ mc =>
      ∃ sc' : FullState,
      FullDenseInvW c F0 F_cur sc' ∧ sc'.core.cur_vars = sP.core.cur_vars ∧
      sc'.core.fuel = sP.core.fuel ∧ M6TmkZero sc' ∧ (FullMem c sc' ⋆ R) mc)
    ?_ ?_
  · rintro _ ⟨comp', max_occ', nm', ⟨⟩⟩ mc ⟨sc', hdwC, hcvC, hfuC, htmkC, hmc⟩
    c0_hsteps_nogrp
    refine wp_join_group (ts := []) (fun _ mM => ∃ sM : FullState,
        FullDenseInvW c F0 F_cur sM ∧ sM.core.cur_vars = sP.core.cur_vars ∧
        sM.core.fuel = sP.core.fuel ∧ M6TmkZero sM ∧ (FullMem c sM ⋆ R) mM)
      ?_ ?_
    · rintro _ ⟨⟩ mM ⟨sM, hdwM, hcvM, hfuM, htmkM, hmM⟩
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64]) (fun _ mT => (FullMem c sM ⋆ R) mT)
        (fun _ ⟨rem_ticks0, ⟨⟩⟩ mT hmT => ?_)
        (fun _ hJT => by c0_hsplit <;> (c0_hsteps_nogrp; exact hJT (_, ()) _ hmM))
      clear hmP hmC0 hinv0 hdw0 htmk0
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64, i64, i32])
        (fun (_rem_tk_out, rem_b_out, _pass_out, ()) mOut =>
          ∃ sO : FullState, FullDenseInvW c F0 F_cur sO ∧
          sO.core.cur_vars = sP.core.cur_vars ∧ sO.core.fuel.toNat ≤ s.core.fuel.toNat ∧
          M6TmkZero sO ∧ (FullMem c sO ⋆ R) mOut) ?_ ?_
      · rintro _ ⟨_rem_tk_out, rem_b_out, _pass_out, ⟨⟩⟩ mOut
          ⟨sO, hdwO, hcvO, hfuO, htmkO, hmO⟩
        have hcvO_le := hdwO.1.core_ok.cur_vars_le
        c0_hsteps_nogrp
        · exact hQ 20#64 sO mOut (fid_denseInv_of_W hdwO) (hcvO.trans hcvP) hfuO htmkO
            (Or.inr rfl) (fun _ => (fid_denseInv_of_W hdwO).inconsistent_unsat (by assumption))
            hmO
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i64, i64])
          (fun (_li_out, _vi_out, ()) mFl => ∃ flL : List (BitVec 32), flL.length = c.max_vars ∧
            (FullMem c { sO with core := { sO.core with flags := flL } } ⋆ R) mFl)
          ?_ ?_
        · rintro _ ⟨_li_out, _vi_out, ⟨⟩⟩ mFl ⟨flL, hflL, hmFl⟩
          have hdwL := swp_set_fl_inv hdwO hflL
          have htmkL : M6TmkZero { sO with core := { sO.core with flags := flL } } :=
            fid_tmkZero_congr htmkO rfl rfl
          have hgu28_lt : 28 < sO.scratch.glue_used.length := by
            rw [hdwL.1.scratch_ok.glue_used_len]; decide
          have hgu29_lt : 29 < sO.scratch.glue_used.length := by
            rw [hdwL.1.scratch_ok.glue_used_len]; decide
          have hgu30_lt : 30 < sO.scratch.glue_used.length := by
            rw [hdwL.1.scratch_ok.glue_used_len]; decide
          refine wp_join_group (ts := []) (fun _ mG => ∃ guG : List (BitVec 32),
              guG.length = 64 ∧
              (FullMem c
                { sO with
                  core := { sO.core with flags := flL }
                  scratch := { sO.scratch with glue_used := guG } } ⋆ R) mG)
            ?_ (fun _ hJG => by
              c0_hsplit
              · c0_hsteps_nogrp
                let gu_e1 := sO.scratch.glue_used.set (29 : BitVec 64).toNat 0#32
                let gu_e2 := gu_e1.set (30 : BitVec 64).toNat 0#32
                have hgu_e2_len : gu_e2.length = 64 := by
                  simp [gu_e2, gu_e1, hdwL.1.scratch_ok.glue_used_len]
                have hgu_e2_28 : (28 : BitVec 64).toNat < gu_e2.length := by
                  rw [hgu_e2_len]; decide
                refine wp_join_group (ts := [])
                  (fun () m_e2 => ∃ gu_e : List (BitVec 32), gu_e.length = 64 ∧
                    (FullMem c { sO with core := { sO.core with flags := flL }
                                         scratch := { sO.scratch with glue_used := gu_e } } ⋆ R)
                      m_e2)
                  (fun _ () m_e2 h => by c0_hsteps_nogrp; exact hJG () m_e2 h)
                  (fun _ hJe2 => by
                    c0_hsplit
                    · c0_hsteps_nogrp
                      refine hJe2 () _ ⟨_, ?_, by assumption⟩
                      simp only [List.length_set, hdwL.1.scratch_ok.glue_used_len]
                    · c0_hsteps_nogrp
                      refine hJe2 () _ ⟨_, ?_, by assumption⟩
                      simp only [List.length_set, hdwL.1.scratch_ok.glue_used_len])
              · c0_hsteps_nogrp
                exact hJG () mFl ⟨sO.scratch.glue_used, hdwL.1.scratch_ok.glue_used_len, hmFl⟩)
          rintro _ ⟨⟩ mG ⟨guG, hguG, hmG⟩
          have hgu32G : 32 < guG.length := by rw [hguG]; decide
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i32]) (fun _ mSwp => mSwp = mG)
            (fun _ ⟨_swp_v, ⟨⟩⟩ mSwp hmSwp => by
              subst hmSwp
              c0_hsteps_nogrp
              have hguS :
                  (guG.set (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 32)).toNat _swp_v).length =
                    64 := by
                rw [List.length_set, hguG]
              have hdwS := swp_set_gu_inv hdwL hguS
              exact hQ 1#64 _ _ (fid_denseInv_of_W hdwS) (hcvO.trans hcvP) hfuO htmkL
                (Or.inl rfl) (fun h => by cases h) (by assumption))
            (fun _ hJswp => by
              c0_hsplit <;> (c0_hsteps_nogrp; exact hJswp (_, ()) mG rfl))
        · intro Jfl hJfl
          c0_hsteps_nogrp
          exact swp12a_post_fl_loop_wp hmx hdwO hcvO hmO
            (fun li vi mFl hFl => hJfl (li, vi, ()) mFl hFl)
      · intro Jo hJo
        c0_hsteps_nogrp
        refine wp_loop_inv
          (fun (_rem_tk, rem_b, pass, ()) mP => pass.toNat ≤ 8 ∧ ∃ sL : FullState,
            FullDenseInvW c F0 F_cur sL ∧ sL.core.cur_vars = sP.core.cur_vars ∧
            sL.core.fuel.toNat ≤ s.core.fuel.toNat ∧ M6TmkZero sL ∧ (FullMem c sL ⋆ R) mP)
          (fun (_, _, pass, ()) _ => 8 - pass.toNat)
          (fun Jp hJp => by
            c0_hsteps_nogrp
            exact hJp (rem_ticks0, budget, 0#32, ()) mT
              ⟨Nat.zero_le _, sM, hdwM, hcvM, by rw [hfuM, hfuP]; exact Nat.le_refl _,
               htmkM, hmT⟩)
          (fun Jp (rem_tk, rem_b, pass, ()) mP ⟨hpa_le, sL, hdwL, hcvL, hfuL, htmkL, hmL⟩ ihp =>
            ?_)
        · c0_hsteps_nogrp
          · have hpa_lt : pass.toNat < 8 :=
              Nat.lt_of_lt_of_eq (BitVec.lt_def.mp (by assumption)) (by decide)
            have hpa1 : (pass + 1#32).toNat = pass.toNat + 1 := bv32_add1_toNat (by omega)
            refine fid_call_collect_cands hCol hdwL.1 hmL
              fun nc trcC ws2C mC hlenC hnc_le htrcC hmC => ?_
            let sC : FullState :=
              { sL with scratch := { sL.scratch with tarjan_reach := trcC, work_stk2 := ws2C } }
            have hdwC : FullDenseInvW c F0 F_cur sC :=
              swp_set_trc_ws2_inv hdwL hlenC.scratch_ok.tarjan_reach_len
                hlenC.scratch_ok.work_stk2_len
            have htmkC : M6TmkZero sC := fid_tmkZero_congr htmkL rfl rfl
            c0_hsplit
            · c0_hsteps_nogrp
              exact hJo (rem_tk, rem_b, pass, ()) mC ⟨sC, hdwC, hcvL, hfuL, htmkC, hmC⟩
            refine wp_join_group (ts := [i64, i64, i32, i32])
              (fun (rt_in, rb_in, _ci_in, _isz_in, ()) mIn => ∃ sI : FullState,
                FullDenseInvW c F0 F_cur sI ∧ sI.core.cur_vars = sP.core.cur_vars ∧
                sI.core.fuel.toNat ≤ s.core.fuel.toNat ∧ M6TmkZero sI ∧ (FullMem c sI ⋆ R) mIn)
              ?_ ?_
            · rintro _ ⟨rt_in, rb_in, _ci_in, _isz_in, ⟨⟩⟩ mIn
                ⟨sI, hdwI, hcvI, hfuI, htmkI, hmIn⟩
              c0_hsteps_nogrp
              exact ihp (rt_in, rb_in, pass + 1#32, ()) mIn (by dsimp only; rw [hpa1]; omega)
                ⟨by rw [hpa1]; omega, sI, hdwI, hcvI, hfuI, htmkI, hmIn⟩
            · intro Jin hJin
              c0_hsteps_nogrp
              refine wp_loop_inv
                (fun (_rt_w, rb_w, ci, isz, ()) mW =>
                  ci.toNat ≤ nc.toNat ∧ isz.toNat ≤ sP.core.cur_vars ∧
                  ∃ sW : FullState, FullDenseInvW c F0 F_cur sW ∧
                    sW.core.cur_vars = sP.core.cur_vars ∧
                    sW.core.fuel.toNat ≤ s.core.fuel.toNat ∧ M6TmkZero sW ∧
                    (∀ i < nc.toNat, (sW.scratch.tarjan_reach[i]?.getD 0#32).toNat <
                      sP.core.cur_vars) ∧
                    (∀ i < isz.toNat,
                      (sW.scratch.tarjan_reach[sP.core.cur_vars + i]?.getD 0#32).toNat <
                        sP.core.cur_vars) ∧
                    (FullMem c sW ⋆ R) mW)
                (fun (_, rb_w, ci, isz, ()) _ =>
                  rb_w.toNat * (2 * c.max_vars + 1) + (nc.toNat - ci.toNat) + isz.toNat)
                (fun Jw hJw => by
                  c0_hsteps_nogrp
                  exact hJw (rem_tk, rem_b, 0#32, 0#32, ()) mC
                    ⟨Nat.zero_le _, Nat.zero_le _, sC, hdwC, hcvL, hfuL, htmkC,
                     by simpa [hcvL] using htrcC, fun _ hi => absurd hi (Nat.not_lt_zero _), hmC⟩)
                (fun Jw (rt_w, rb_w, ci, isz, ()) mW
                    ⟨hci_le, hisz_le, sW, hdwW, hcvW, hfuW, htmkW, htrc_p, htrc_i, hmW⟩ ihw => ?_)
              · have hExit : (FullMem c sW ⋆ R) mW →
                    Jin (rt_w, rb_w, ci, isz, ()) mW := fun hmE =>
                  hJin (rt_w, rb_w, ci, isz, ()) mW ⟨sW, hdwW, hcvW, hfuW, htmkW, hmE⟩
                c0_hsteps_nogrp
                · have hcvW_pos : 0 < sW.core.cur_vars := hcvW ▸ hcvP_pos
                  have hcvW_le : sW.core.cur_vars ≤ c.max_vars := hdwW.1.core_ok.cur_vars_le
                  have hnc_le_cvW : nc.toNat ≤ sW.core.cur_vars := by
                    rw [hcvW, ← hcvL]; exact hnc_le
                  have hgu30W : 30 < sW.scratch.glue_used.length := by
                    rw [hdwW.1.scratch_ok.glue_used_len]; decide
                  have hrb_pos : 0 < rb_w.toNat := by
                    simpa using (by assumption : BitVec.toNat 0 < rb_w.toNat)
                  have hrb1 : (rb_w - 1#64).toNat = rb_w.toNat - 1 := by bv_omega
                  have hK6L := k6LayoutOfCap_scrLen hcap_ge c.hscr
                  refine wp_join_group (ts := [i32, i32, i32])
                    (fun (ci', isz', v, ()) mV =>
                      ci'.toNat ≤ nc.toNat ∧ isz'.toNat ≤ sP.core.cur_vars ∧
                      v.toNat < sP.core.cur_vars ∧
                      (nc.toNat - ci'.toNat) + isz'.toNat < (nc.toNat - ci.toNat) + isz.toNat ∧
                      ∃ sV : FullState, FullDenseInvW c F0 F_cur sV ∧
                        sV.core.cur_vars = sP.core.cur_vars ∧
                        sV.core.fuel.toNat ≤ s.core.fuel.toNat ∧ M6TmkZero sV ∧
                        (∀ i < nc.toNat, (sV.scratch.tarjan_reach[i]?.getD 0#32).toNat <
                          sP.core.cur_vars) ∧
                        (∀ i < isz'.toNat,
                          (sV.scratch.tarjan_reach[sP.core.cur_vars + i]?.getD 0#32).toNat <
                            sP.core.cur_vars) ∧
                        (FullMem c sV ⋆ R) mV)
                    ?_ ?_
                  · rintro _ ⟨ci', isz', v, ⟨⟩⟩ mV
                      ⟨hci'_le, hisz'_le, hv_ltP, hrem_dec, sV, hdwV, hcvV, hfuV, htmkV,
                       htrcV_p, htrcV_i, hmV⟩
                    have hcvV_le := hdwV.1.core_ok.cur_vars_le
                    have hv_lt : v.toNat < sV.core.cur_vars := hcvV ▸ hv_ltP
                    have hfl_lt : v.toNat < sV.core.flags.length := by
                      rw [hdwV.1.core_ok.flags_len]; omega
                    have hval_lt : (BitVec.setWidth 64 (v <<< (1 : Nat))).toNat <
                        sV.core.vals.length := by
                      have hsh : (BitVec.setWidth 64 (v <<< (1 : Nat))).toNat = 2 * v.toNat := by
                        rw [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
                          Nat.pow_one, Nat.mod_eq_of_lt (by omega : v.toNat * 2 < 2 ^ 32),
                          Nat.mod_eq_of_lt (by omega : v.toNat * 2 < 2 ^ 64)]
                        omega
                      rw [hsh, hdwV.1.core_ok.vals_len]; omega
                    refine wp_join_group (ts := [i64, i64, i32])
                      (fun (_rt_n, rb_n, isz_n, ()) mn =>
                        (rb_n.toNat < rb_w.toNat ∨
                          (rb_n = rb_w ∧
                            nc.toNat - ci'.toNat + isz_n.toNat <
                              nc.toNat - ci.toNat + isz.toNat)) ∧
                        isz_n.toNat ≤ sP.core.cur_vars ∧
                        ∃ sN : FullState, FullDenseInvW c F0 F_cur sN ∧
                          sN.core.cur_vars = sP.core.cur_vars ∧
                          sN.core.fuel.toNat ≤ s.core.fuel.toNat ∧ M6TmkZero sN ∧
                          (∀ i < nc.toNat, (sN.scratch.tarjan_reach[i]?.getD 0#32).toNat <
                            sP.core.cur_vars) ∧
                          (∀ i < isz_n.toNat,
                            (sN.scratch.tarjan_reach[sP.core.cur_vars + i]?.getD 0#32).toNat <
                              sP.core.cur_vars) ∧
                          (FullMem c sN ⋆ R) mn)
                      ?_ ?_
                    · rintro _ ⟨rt_n, rb_n, isz_n, ⟨⟩⟩ mn
                        ⟨hrb_ord, hisz_n, sN, hdwN, hcvN, hfuN, htmkN, htrcN_p, htrcN_i, hmN⟩
                      c0_hsteps_nogrp
                      refine ihw (rt_n, rb_n, ci', isz_n, ()) mn ?_
                        ⟨hci'_le, hisz_n, sN, hdwN, hcvN, hfuN, htmkN, htrcN_p, htrcN_i, hmN⟩
                      dsimp only
                      rcases hrb_ord with hlt | ⟨rfl, hlt⟩
                      · have hmul : (rb_n.toNat + 1) * (2 * c.max_vars + 1) ≤
                            rb_w.toNat * (2 * c.max_vars + 1) :=
                          Nat.mul_le_mul_right _ hlt
                        rw [Nat.succ_mul] at hmul
                        have : nc.toNat - ci'.toNat + isz_n.toNat < 2 * c.max_vars + 1 := by
                          rw [hcvL] at hnc_le; omega
                        omega
                      · omega
                    intro _ hJlp
                    c0_hsteps_nogrp
                    · have hflV1_ex : ∃ flV1 : List (BitVec 32),
                          flV1.length = c.max_vars ∧
                          (FullMem c { sV with core := { sV.core with flags := flV1 } } ⋆ R) m := by
                        refine ⟨_, ?_, hm⟩
                        rw [List.length_set]
                        exact hdwV.1.core_ok.flags_len
                      obtain ⟨flV1, hflV1_len, hmV1⟩ := hflV1_ex
                      let sV1 : FullState := { sV with core := { sV.core with flags := flV1 } }
                      have hdwV1 : FullDenseInvW c F0 F_cur sV1 := swp_set_fl_inv hdwV hflV1_len
                      have htmkV1 : M6TmkZero sV1 := fid_tmkZero_congr htmkV rfl rfl
                      refine swp_var_call hSV hdwV1 hcap_ge hv_lt htmkV1 hmV1
                        fun rSV sSV mSV hdwSV hcvSV hfuSV htmkSV htrcSV hrSV huSV hmSV => ?_
                      have hcvSV_P : sSV.core.cur_vars = sP.core.cur_vars := hcvSV.trans hcvV
                      have hfuSV_s : sSV.core.fuel.toNat ≤ s.core.fuel.toNat :=
                        Nat.le_trans hfuSV hfuV
                      have htrcSV_p : ∀ i < nc.toNat,
                          (sSV.scratch.tarjan_reach[i]?.getD 0#32).toNat < sP.core.cur_vars := by
                        rw [htrcSV]; exact htrcV_p
                      have htrcSV_i : ∀ i < isz'.toNat,
                          (sSV.scratch.tarjan_reach[sP.core.cur_vars + i]?.getD 0#32).toNat <
                            sP.core.cur_vars := by rw [htrcSV]; exact htrcV_i
                      c0_hsplit
                      · c0_hsteps_nogrp
                        exact hQ 20#64 sSV mSV (fid_denseInv_of_W hdwSV) (hcvSV_P.trans hcvP)
                          hfuSV_s htmkSV (Or.inr rfl) (fun _ => huSV ‹_›) hmSV
                      refine wp_join_group (ts := []) (fun _ mP2 => ∃ sP2 : FullState,
                          FullDenseInvW c F0 F_cur sP2 ∧ sP2.core.cur_vars = sP.core.cur_vars ∧
                          sP2.core.fuel.toNat ≤ s.core.fuel.toNat ∧ M6TmkZero sP2 ∧
                          (∀ i < nc.toNat, (sP2.scratch.tarjan_reach[i]?.getD 0#32).toNat <
                            sP.core.cur_vars) ∧
                          (∀ i < isz'.toNat,
                            (sP2.scratch.tarjan_reach[sP.core.cur_vars + i]?.getD 0#32).toNat <
                              sP.core.cur_vars) ∧
                          (FullMem c sP2 ⋆ R) mP2)
                        ?_ ?_
                      · rintro _ ⟨⟩ mP2 ⟨sP2, hdwP2, hcvP2, hfuP2, htmkP2, htrcP2_p, htrcP2_i, hmP2⟩
                        let k6L := k6LayoutOfCap c.scratch_cap hcap_ge c.hscr
                        have hk_mv32 : BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) =
                            k6L.mv32 := by
                          have hmL := k6L.hmaxV
                          apply BitVec.eq_of_toNat_eq
                          change (BitVec.setWidth 32 (BitVec.ofNat 64 k6L.maxV)).toNat =
                            (BitVec.ofNat 32 k6L.maxV).toNat
                          simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
                          have hlt32 : k6L.maxV < 2 ^ 32 := Nat.lt_of_le_of_lt hmL.2 (by decide)
                          have hlt64 : k6L.maxV < 2 ^ 64 := Nat.lt_of_le_of_lt hmL.2 (by decide)
                          rw [Nat.mod_eq_of_lt hlt64, Nat.mod_eq_of_lt hlt32]
                        have hkptr_c0 : c.pScratchBuf + BitVec.setWidth 64
                            ((1280 : BitVec 32) +
                              BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) <<<
                                (1 : Nat)) * 4 = k6L.kPtr c.pScratchBuf := by
                          rw [hk_mv32]
                          exact k6_ptr_base_k6Base k6L c.pScratchBuf
                        have hk11_idx := fid_k11_idx hK6L
                        have hk11_scr : (BitVec.setWidth 64 (BitVec.ofNat 32
                            ((k6LayoutOfCap c.scratch_cap hcap_ge c.hscr).k6Base + 11))).toNat <
                            sP2.scratch.scratch_buf.length := by
                          rw [hdwP2.1.scratch_ok.scratch_buf_len]; exact hk11_idx
                        c0_hsteps_nogrp
                        try rw [hkptr_c0]
                        try rw [fid_k11_ptr hK6L]
                        c0_hsteps_nogrp
                        refine wp_join_group (ts := [i64]) (fun _ mRt =>
                            (FullMem c sP2 ⋆ R) mRt)
                          (fun _ ⟨rt', ⟨⟩⟩ mRt hmRt => ?_)
                          (fun _ hJR => by
                            c0_hsplit <;> (c0_hsteps_nogrp; exact hJR (_, ()) _ hmP2))
                        try rw [← fid_k11_ptr hK6L]
                        have hdec_rb : (rb_w - 1#64).toNat * (2 * c.max_vars + 1) +
                            (nc.toNat - ci'.toNat) + isz'.toNat <
                            rb_w.toNat * (2 * c.max_vars + 1) +
                            (nc.toNat - ci.toNat) + isz.toNat := by
                          rw [Nat.add_assoc, Nat.add_assoc]
                          exact swp_lex_dec_rb (rb1 := rb_w.toNat) (cap := 2 * c.max_vars)
                            (by omega) (by rw [hcvW] at hnc_le_cvW; omega)
                        refine wp_join_group (ts := [i32])
                          (fun (isz_out, ()) m_out =>
                            isz_out.toNat ≤ sP.core.cur_vars ∧ ∃ s_out : FullState,
                              FullDenseInvW c F0 F_cur s_out ∧
                              s_out.core.cur_vars = sP.core.cur_vars ∧
                              s_out.core.fuel.toNat ≤ s.core.fuel.toNat ∧ M6TmkZero s_out ∧
                              (∀ i < nc.toNat,
                                (s_out.scratch.tarjan_reach[i]?.getD 0#32).toNat <
                                  sP.core.cur_vars) ∧
                              (∀ i < isz_out.toNat,
                                (s_out.scratch.tarjan_reach[sP.core.cur_vars + i]?.getD
                                  0#32).toNat < sP.core.cur_vars) ∧
                              (FullMem c s_out ⋆ R) m_out)
                          (fun _ ⟨isz_out, ⟨⟩⟩ m_out
                              ⟨hisz_o, s_o, hdw_o, hcv_o, hfu_o, htmk_o, htrc_op, htrc_oi,
                               hm_o⟩ => by
                            c0_hsteps_nogrp
                            exact hJlp (rt', rb_w - 1#64, isz_out, ()) m_out
                              ⟨Or.inl (by rw [hrb1]; omega), hisz_o, s_o, hdw_o, hcv_o,
                               hfu_o, htmk_o, htrc_op, htrc_oi, hm_o⟩)
                          (fun _ hJ_out => ?_)
                        c0_hsplit
                        · have hk24_idx := fid_k24_idx hK6L
                          have hk24_scr : (BitVec.setWidth 64 (BitVec.ofNat 32
                              (k6L.k6Base + 24))).toNat < sP2.scratch.scratch_buf.length := by
                            rw [hdwP2.1.scratch_ok.scratch_buf_len]; exact hk24_idx
                          c0_hsteps_nogrp
                          try rw [hkptr_c0]
                          try rw [fid_k24_ptr hK6L]
                          c0_hsteps_nogrp
                          refine swp12a_eq_loop_wp hmx hdwP2 hcvP2 hfuP2 htmkP2
                            (hcvW ▸ hnc_le_cvW) hisz'_le htrcP2_p htrcP2_i hmRt
                            (fun isz_out m_out hOut => hJ_out (isz_out, ()) m_out hOut)
                        · c0_hsteps_nogrp
                          exact hJ_out (isz', ()) mRt
                            ⟨hisz'_le, sP2, hdwP2, hcvP2, hfuP2, htmkP2, htrcP2_p, htrcP2_i,
                             hmRt⟩
                      · intro J2 hJ2
                        c0_hsteps_nogrp
                        · refine fid_call_dense_prop hDP hdwSV hmSV
                            fun okS sS mS hdwS hcvS hfuS htmkS htrcS _ hnoS hmS => ?_
                          have htmkS' := fid_tmkZero_congr htmkSV hcvS htmkS
                          c0_hsplit
                          · c0_hsteps_nogrp
                            exact hJ2 () mS ⟨sS, hdwS, hcvS.trans hcvSV_P,
                              Nat.le_trans (by rw [hfuS]; exact hfuSV) hfuV, htmkS',
                              by rw [htrcS]; exact htrcSV_p,
                              by rw [htrcS]; exact htrcSV_i, hmS⟩
                          · have hokf : okS = false := by
                              cases okS <;> first | rfl | exact hc
                            c0_hsteps_nogrp
                            exact hQ 20#64 sS mS (fid_denseInv_of_W hdwS)
                              (hcvS.trans hcvSV_P |>.trans hcvP)
                              (Nat.le_trans (by rw [hfuS]; exact hfuSV) hfuV)
                              htmkS' (Or.inr rfl) (fun _ => (hnoS hokf).1) hmS
                        · c0_hsteps_nogrp
                          exact hJ2 () mSV ⟨sSV, hdwSV, hcvSV_P, hfuSV_s, htmkSV,
                            htrcSV_p, htrcSV_i, hmSV⟩
                    all_goals
                      exact hJlp (rt_w, rb_w, isz', ()) mV
                        ⟨Or.inr ⟨rfl, hrem_dec⟩, hisz'_le, sV, hdwV, hcvV, hfuV, htmkV,
                         htrcV_p, htrcV_i, hmV⟩
                  · intro Jv hJv
                    c0_hsplit
                    · have hisz_pos : 0 < isz.toNat := by
                        have h1 : BitVec.toNat 0#32 < isz.toNat := by assumption
                        exact h1
                      have hisz1 : (isz - 1#32).toNat = isz.toNat - 1 := swp_bv32_sub1 hisz_pos
                      have hidx_len : (BitVec.ofNat 64 sP.core.cur_vars +
                          BitVec.setWidth 64 (isz - 1#32)).toNat <
                          sW.scratch.tarjan_reach.length := by
                        try clear htrc_p htrc_i hmW hJv hExit hJlp hJe_next
                        rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
                          Nat.mod_eq_of_lt (Nat.lt_trans (isz - 1#32).isLt (by decide)),
                          Nat.mod_eq_of_lt (by omega), hisz1,
                          Nat.mod_eq_of_lt (by omega), hdwW.1.scratch_ok.tarjan_reach_len]
                        omega
                      have hv_ok : (sW.scratch.tarjan_reach[(BitVec.ofNat 64 sP.core.cur_vars +
                          BitVec.setWidth 64 (isz - 1#32)).toNat]'hidx_len).toNat <
                          sP.core.cur_vars := by
                        have h1 := htrc_i (isz.toNat - 1) (by omega)
                        rw [List.getElem?_eq_getElem (by
                            rw [hdwW.1.scratch_ok.tarjan_reach_len]; omega),
                          Option.getD_some] at h1
                        have hidx_eq : (BitVec.ofNat 64 sP.core.cur_vars +
                            BitVec.setWidth 64 (isz - 1#32)).toNat =
                            sP.core.cur_vars + (isz.toNat - 1) := by
                          try clear h1 htrc_p htrc_i hmW hJv hExit hJlp hJe_next
                          rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
                            Nat.mod_eq_of_lt (Nat.lt_trans (isz - 1#32).isLt (by decide)),
                            Nat.mod_eq_of_lt (by omega), hisz1,
                            Nat.mod_eq_of_lt (by omega)]
                        simpa only [hidx_eq] using h1
                      c0_hsteps_nogrp
                      exact hJv (ci, isz - 1#32, _, ()) mW
                        ⟨hci_le, by rw [hisz1]; omega, hv_ok, by rw [hisz1]; omega,
                         sW, hdwW, hcvW, hfuW, htmkW, htrc_p,
                         fun i hi => htrc_i i (by rw [hisz1] at hi; omega), hmW⟩
                    · c0_hsplit
                      · have hci_lt : ci.toNat < nc.toNat := BitVec.lt_def.mp (by assumption)
                        have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := bv32_add1_toNat (by omega)
                        have htrc_len : (BitVec.setWidth 64 ci).toNat <
                            sW.scratch.tarjan_reach.length := by
                          rw [BitVec.toNat_setWidth,
                            Nat.mod_eq_of_lt (Nat.lt_trans ci.isLt (by decide)),
                            hdwW.1.scratch_ok.tarjan_reach_len]; omega
                        have hv_ok : (sW.scratch.tarjan_reach[
                            (BitVec.setWidth 64 ci).toNat]'htrc_len).toNat < sP.core.cur_vars := by
                          have h1 := htrc_p ci.toNat hci_lt
                          rw [List.getElem?_eq_getElem (by
                              rw [hdwW.1.scratch_ok.tarjan_reach_len]; omega),
                            Option.getD_some] at h1
                          have hci_eq : (BitVec.setWidth 64 ci).toNat = ci.toNat := by
                            rw [BitVec.toNat_setWidth,
                              Nat.mod_eq_of_lt (Nat.lt_trans ci.isLt (by decide))]
                          simpa only [hci_eq] using h1
                        c0_hsteps_nogrp
                        refine wp_join_group (ts := [i32])
                          (fun _ mGu => ∃ gu' : List (BitVec 32), gu'.length = 64 ∧
                            (FullMem c { sW with scratch := { sW.scratch with glue_used := gu' } }
                              ⋆ R) mGu)
                          (fun _ ⟨nval, ⟨⟩⟩ mGu ⟨gu', hgu', hmGu⟩ => by
                            have hgu30' : (30 : BitVec 64).toNat < gu'.length := by
                              rw [hgu']; decide
                            c0_hsteps_nogrp
                            let gu'' :=
                              gu'.set (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 30)).toNat nval
                            have hgu'' : gu''.length = 64 := by
                              simp only [gu'', List.length_set, hgu']
                            refine hJv (ci + 1#32, isz, _, ()) _
                              ⟨by rw [hci1]; omega, hisz_le, hv_ok,
                               by rw [hci1]; omega,
                               { sW with scratch := { sW.scratch with glue_used := gu'' } },
                               swp_set_gu_inv hdwW hgu'',
                               hcvW, hfuW, fid_tmkZero_congr htmkW rfl rfl,
                               htrc_p, htrc_i, by assumption⟩)
                          (fun _ hJgu => by
                            c0_hsplit <;>
                              (c0_hsteps_nogrp
                               refine hJgu (_, ()) _ ⟨_, ?_, by assumption⟩
                               simp [hdwW.1.scratch_ok.glue_used_len]))
                      · c0_hsteps_nogrp; exact hExit hmW
                all_goals exact hExit hmW
          · exact hJo (rem_tk, rem_b, pass, ()) mP ⟨sL, hdwL, hcvL, hfuL, htmkL, hmL⟩
          all_goals exact hJo (rem_tk, rem_b, pass, ()) mP ⟨sL, hdwL, hcvL, hfuL, htmkL, hmL⟩
    · intro Jm hJm
      exact swp12a_pre_mark_wp hmx hdwC hcvC htmkC hmc fun xs mM
        ⟨sM, hdwM, hcvM, hfuM, htmkM, hmM⟩ =>
        hJm xs mM ⟨sM, hdwM, hcvM, hfuM.trans hfuC, htmkM, hmM⟩
  · intro Jc hJc
    c0_hsplit
    · c0_hsteps_nogrp
      exact hJc (_, _, _, ()) mC0 ⟨sP, hdwP, rfl, rfl, htmkP', hmC0⟩
    · c0_hsteps_nogrp
      refine wp_loop_inv (ts := [i64, i64])
        (fun (_ri, v, ()) mv => v.toNat ≤ sP.core.cur_vars ∧ ∃ fl' : List (BitVec 32),
          fl'.length = c.max_vars ∧
          (FullMem c { sP with core := { sP.core with flags := fl' } } ⋆ R) mv)
        (fun (_, v, ()) _ => sP.core.cur_vars - v.toNat)
        (fun Jv hJv => by
          c0_hsteps_nogrp
          exact hJv (0#64, 0#64, ()) mC0
            ⟨Nat.zero_le _, sP.core.flags, hdwP.1.core_ok.flags_len, hmC0⟩)
        (fun Jv (ri, v, ()) mv ⟨hv_le, fl', hfl', hmv⟩ ihv => ?_)
      · c0_hsteps_nogrp
        · have hv_lt : v.toNat < sP.core.cur_vars := by
            have h1 : v.toNat < sP.core.cur_vars % 2 ^ 64 := by assumption
            rw [Nat.mod_eq_of_lt (by omega)] at h1; exact h1
          have hfl_lt : v.toNat < fl'.length := by rw [hfl']; omega
          have hv_231 : v.toNat < 2 ^ 31 := by omega
          have hval_lt : (v <<< (1 : Nat)).toNat < sP.core.vals.length := by
            have hsh : (v <<< (1 : Nat)).toNat = 2 * v.toNat := by bv_omega
            rw [hsh, hdwP.1.core_ok.vals_len]; omega
          have hwvp_lt : (((v <<< (1 : Nat)) <<< (1 : Nat)) + 1).toNat <
              sP.core.wvec.length := by
            have hsh : (((v <<< (1 : Nat)) <<< (1 : Nat)) + 1).toNat = 4 * v.toNat + 1 := by
              bv_omega
            rw [hsh, hdwP.1.core_ok.wvec_len]; omega
          have hwvn_lt : ((((v <<< (1 : Nat)) ||| 1#64) <<< (1 : Nat)) + 1).toNat <
              sP.core.wvec.length := by
            rw [show (1 : BitVec 64) = 1#64 from rfl,
              swp12a_bv64_wvec_neg_toNat v (by omega), hdwP.1.core_ok.wvec_len]; omega
          have hv1 : (v + 1).toNat = v.toNat + 1 := by bv_omega
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i64]) (fun (_ri', ()) mf => ∃ fl'' : List (BitVec 32),
              fl''.length = c.max_vars ∧
              (FullMem c { sP with core := { sP.core with flags := fl'' } } ⋆ R) mf)
            (fun _ ⟨ri', ⟨⟩⟩ mf ⟨fl'', hfl'', hmf⟩ => by
              c0_hsteps_nogrp
              exact ihv (ri', v + 1, ()) mf (by dsimp only; rw [hv1]; omega)
                ⟨by rw [hv1]; omega, fl'', hfl'', hmf⟩) ?_
          intro Jri hJri
          c0_hsteps_nogrp
          · refine wp_join_group (ts := [i64]) (fun (_ri2, ()) mf2 => ∃ fl2 : List (BitVec 32),
                fl2.length = c.max_vars ∧
                (FullMem c { sP with core := { sP.core with flags := fl2 } } ⋆ R) mf2)
              (fun _ ⟨ri2, ⟨⟩⟩ mf2 ⟨fl2, hfl2, hmf2⟩ => by
                c0_hsteps_nogrp; exact hJri (ri2, ()) mf2 ⟨fl2, hfl2, hmf2⟩) ?_
            intro Jri2 hJri2
            c0_hsteps_nogrp
            · refine wp_join_group (ts := [i64]) (fun (_ri3, ()) mf3 => ∃ fl3 : List (BitVec 32),
                  fl3.length = c.max_vars ∧
                  (FullMem c { sP with core := { sP.core with flags := fl3 } } ⋆ R) mf3)
                (fun _ ⟨ri3, ⟨⟩⟩ mf3 ⟨fl3, hfl3, hmf3⟩ => by
                  c0_hsteps_nogrp; exact hJri2 (ri3, ()) mf3 ⟨fl3, hfl3, hmf3⟩) ?_
              intro _ hJri3
              refine wp_join_group (ts := []) (fun () m34 => m34 = mv)
                (fun _ () m34 hm34 => by
                  subst hm34; c0_hsteps_nogrp
                  refine hJri3 (_, ()) _ ⟨_, ?_, by assumption⟩; simp [hfl'])
                (fun _ hJ34 => by
                  c0_hsplit; rotate_left
                  · c0_hsteps_nogrp; exact hJ34 () mv rfl
                  c0_hsplit; rotate_left
                  · c0_hsteps_nogrp; exact hJ34 () mv rfl
                  c0_hsplit; rotate_left
                  · c0_hsteps_nogrp; exact hJ34 () mv rfl
                  c0_hsplit; rotate_left
                  · c0_hsteps_nogrp; exact hJ34 () mv rfl
                  c0_hsteps_nogrp
                  exact hJri3 (_, ()) mv ⟨fl', hfl', hmv⟩)
            · refine hJri2 (_, ()) _ ⟨_, ?_, by assumption⟩; simp [hfl']
          · exact hJri (ri, ()) mv ⟨fl', hfl', hmv⟩
        · have hdwU := swp_set_fl_inv hdwP hfl'
          have hgu28U : (28 : BitVec 64).toNat < sP.scratch.glue_used.length := by
            rw [hdwU.1.scratch_ok.glue_used_len]; decide
          refine wp_join_group (ts := [i32, i64, .bool]) (fun _ mf => ∃ sJc : FullState,
              FullDenseInvW c F0 F_cur sJc ∧ sJc.core.cur_vars = sP.core.cur_vars ∧
              sJc.core.fuel = sP.core.fuel ∧ M6TmkZero sJc ∧ (FullMem c sJc ⋆ R) mf)
            (fun _ ⟨_c, _mo, _nm, ⟨⟩⟩ mf ⟨sJc, hdwJ, hcvJ, hfuJ, htmkJ, hmJ⟩ => by
              c0_hsteps_nogrp
              exact hJc (_, _, _, ()) mf ⟨sJc, hdwJ, hcvJ, hfuJ, htmkJ, hmJ⟩) ?_
          intro _Jc' hJc'
          c0_hsplit
          · c0_hsteps_nogrp
            refine wp_join_group (ts := []) (fun _ mB => ∃ guB : List (BitVec 32),
                guB.length = 64 ∧
                (FullMem c
                  { sP with
                    core := { sP.core with flags := fl' }
                    scratch := { sP.scratch with glue_used := guB } } ⋆ R) mB)
              ?_ (fun _ hJB => by
                c0_hsplit <;>
                  (c0_hsteps_nogrp
                   first
                   | (refine hJB () _ ⟨_, ?_, by assumption⟩
                      simp [hdwU.1.scratch_ok.glue_used_len])
                   | exact hJB () _ ⟨sP.scratch.glue_used, hdwU.1.scratch_ok.glue_used_len,
                       by assumption⟩))
            rintro _ ⟨⟩ mB ⟨guB, hguB, hmB⟩
            have hgu28B : (28 : BitVec 64).toNat < guB.length := by rw [hguB]; decide
            have hdwB := swp_set_gu_inv hdwU hguB
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i32])
              (fun _ mCp => (FullMem c
                { sP with
                  core := { sP.core with flags := fl' }
                  scratch := { sP.scratch with glue_used := guB } } ⋆ R) mCp)
              (fun _ ⟨compB, ⟨⟩⟩ mCp hmCp => by
                c0_hsteps_nogrp
                exact hJc' (_, _, true, ()) mCp ⟨_, hdwB, rfl, rfl, htmkP', hmCp⟩)
              (fun _ hJCp => by c0_hsplit <;> (c0_hsteps_nogrp; exact hJCp (_, ()) _ hmB))
          · c0_hsteps_nogrp
            exact hJc' (_, _, _, ()) _ ⟨_, hdwU, rfl, rfl, htmkP', by assumption⟩

end LeanQbe.T.Examples.Kissat.FullFidelityStep12A

end
