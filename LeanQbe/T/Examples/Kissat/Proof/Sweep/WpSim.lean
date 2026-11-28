/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Sweep.LemmasCommon

/-!
# Simulation & Random-Sampling WP Proofs (`Kissat.Proof.Sweep.WpSim`)

Clean `Func.wp` proofs against `Src.Sweep` and `Proof.Sweep.Spec`:
1. `full_m6_sweep_refine_sig_wp` (`fullM6SweepRefineSigSpec`)
2. `full_m6_sweep_rand_phases_wp` (`fullM6SweepRandPhasesSpec`)
3. `full_m6_sweep_solve_wp` (`fullM6SweepSolveSpec`)
4. `full_m6_sweep_flip_round_wp` (`fullM6SweepFlipRoundSpec`)
5. `full_m6_sweep_sim_wp` (`fullM6SweepSimSpec`)

Zero legacy `Full*` imports; zero `@[expose]` on theorems, lemmas, or sections.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Sweep

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src
open LeanQbe.T.Examples.Kissat.Src.Sweep
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Kitten
open LeanQbe.T.Examples.Kissat.Proof.Kitten.Spec
open LeanQbe.T.Examples.Kissat.Proof.Sweep.Spec

open FullArenaTactics K6MemATactics K6PtrTactics M6SweepTactics
open scoped FullArenaTactics M6SweepTactics

/-! ## 1. Shared Arithmetic, `K6TailEq` / `FullMem`, & Callee Helpers -/

private theorem m6_mv32_eq {c : FullCfg} {L : K6Layout} (hLmv : L.maxV = k6MaxV c.scratch_cap) :
    (BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32 = L.mv32 := by
  have hm := L.hmaxV
  apply BitVec.eq_of_toNat_eq
  simp only [k6_mv32_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [← hLmv]; omega

private theorem m6_mv32_toNat {c : FullCfg} {L : K6Layout}
    (hLmv : L.maxV = k6MaxV c.scratch_cap) :
    ((BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32).toNat = L.maxV := by
  rw [m6_mv32_eq hLmv, k6_mv32_toNat]

private theorem m6_scrCap_lt64 (c : FullCfg) : c.scratch_cap < 2 ^ 64 := by
  have := c.hscr; unfold dimacsBound at this; omega

private theorem m6_maxV_pos {c : FullCfg} {L : K6Layout}
    (hLmv : L.maxV = k6MaxV c.scratch_cap) : 0 < k6MaxV c.scratch_cap := by
  have := L.hmaxV; omega

private theorem m6_maxV_lt30 {c : FullCfg} {L : K6Layout}
    (hLmv : L.maxV = k6MaxV c.scratch_cap) : k6MaxV c.scratch_cap < 2 ^ 30 := by
  have := L.hmaxV; omega

private theorem m6_k6StateOfScratch_set19 (L : K6Layout) (scr : List (BitVec 32))
    (v : BitVec 32) (hlen : L.scrLen = scr.length) :
    k6StateOfScratch L (scr.set (L.k6Base + 19) v) =
      (k6StateOfScratch L scr).putHdr .phase v := by
  have hm := L.hmaxV; have ha := L.hacap
  have hbd : 19 < (scr.drop L.k6Base).length := by
    rw [List.length_drop, ← hlen]; unfold K6Layout.scrLen K6Layout.k6Fixed; omega
  have hdrop : (scr.set (L.k6Base + 19) v).drop L.k6Base = (scr.drop L.k6Base).set 19 v := by
    rw [m6_list_drop_set_ge scr v (Nat.le_add_right _ _)]; simp
  have hsub : ∀ i, i ≠ 19 →
      ((scr.drop L.k6Base).set 19 v)[i]?.getD 0#32 = (scr.drop L.k6Base)[i]?.getD 0#32 :=
    fun i hi => by rw [List.getElem?_set_ne (Ne.symm hi)]
  have h19 : ((scr.drop L.k6Base).set 19 v)[19]?.getD 0#32 = v := by
    rw [List.getElem?_set_self hbd, Option.getD_some]
  have htail : (((scr.drop L.k6Base).set 19 v).drop 25).take 7 =
      ((scr.drop L.k6Base).drop 25).take 7 := by
    rw [m6_list_drop_set_lt _ v (by decide)]
  have hdl : ∀ k, 25 < k →
      ((scr.drop L.k6Base).set 19 v).drop k = (scr.drop L.k6Base).drop k :=
    fun k hk => m6_list_drop_set_lt _ v (by omega)
  unfold k6StateOfScratch K6State.ofSlab K6State.putHdr
  rw [hdrop]
  simp only [hsub 0 (by decide), hsub 1 (by decide), hsub 2 (by decide), hsub 3 (by decide),
    hsub 4 (by decide), hsub 5 (by decide), hsub 6 (by decide), hsub 7 (by decide),
    hsub 8 (by decide), hsub 9 (by decide), hsub 10 (by decide), hsub 11 (by decide),
    hsub 12 (by decide), hsub 13 (by decide), hsub 14 (by decide), hsub 15 (by decide),
    hsub 16 (by decide), hsub 17 (by decide), hsub 18 (by decide), h19, hsub 20 (by decide),
    hsub 21 (by decide), hsub 22 (by decide), hsub 23 (by decide), hsub 24 (by decide), htail,
    hdl L.oLvl (by unfold K6Layout.oLvl; decide),
    hdl L.oRsn (by unfold K6Layout.oRsn; omega),
    hdl L.oQPrev (by unfold K6Layout.oQPrev; omega),
    hdl L.oQNext (by unfold K6Layout.oQNext; omega),
    hdl L.oQStamp (by unfold K6Layout.oQStamp; omega),
    hdl L.oTrl (by unfold K6Layout.oTrl; omega),
    hdl L.oFlags (by unfold K6Layout.oFlags; omega),
    hdl L.oAna (by unfold K6Layout.oAna; omega),
    hdl L.oKl (by unfold K6Layout.oKl; omega),
    hdl L.oAssump (by unfold K6Layout.oAssump; omega),
    hdl L.oVals (by unfold K6Layout.oVals; omega),
    hdl L.oWHead (by unfold K6Layout.oWHead; omega),
    hdl L.oWNext (by unfold K6Layout.oWNext; omega),
    hdl L.oWBlit (by unfold K6Layout.oWBlit; omega),
    hdl L.oClOff (by unfold K6Layout.oClOff; omega),
    hdl L.oClSz (by unfold K6Layout.oClSz; omega),
    hdl L.oArena (by unfold K6Layout.oArena; omega)]

private theorem m6_split_k6 {c : FullCfg} {L : K6Layout} {s : FullState} {P : (Nat → Bool) → Prop}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hLscr : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hK : K6Inv L P (k6StateOfScratch L s.scratch.scratch_buf))
    (hm : (FullMem c s ⋆ R) m) :
    (K6MemA L (L.kPtr c.pScratchBuf) (k6StateOfScratch L s.scratch.scratch_buf) ⋆
      (FullK6Frame c L s ⋆ R)) m := by
  have hsl : s.scratch.scratch_buf.length = L.scrLen := hscr.trans hLscr.symm
  rw [fullMem_eq_k6Frame hsl] at hm
  exact k6Mem_to_amem hK.shapes (sep_ac hm)

private def m6_xorshift32_step (rs : BitVec 32) : BitVec 32 :=
  let rs1 := rs ^^^ (rs <<< (13 : Nat))
  let rs2 := rs1 ^^^ (rs1 >>> (17 : Nat))
  rs2 ^^^ (rs2 <<< (5 : Nat))

private theorem m6_call_rand_phases {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hRand : Γ.Has "full_m6_sweep_rand_phases" fullM6SweepRandPhasesSpec)
    {c : FullCfg} {s : FullState} {P : (Nat → Bool) → Prop} {L : K6Layout}
    {nv : Val i32} {R : Mem 64 → Prop} {m : Mem 64} {k : Tup Val [] → Expr Val Cont rs}
    (hlen : s.LengthsOk c) (hLscr : L.scrLen = c.scratch_cap)
    (hLmv : L.maxV = k6MaxV c.scratch_cap)
    (hK : K6Inv L P (k6StateOfScratch L s.scratch.scratch_buf))
    (hnv : (k6StateOfScratch L s.scratch.scratch_buf).nv = nv)
    (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ scr' m',
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      let ks := k6StateOfScratch L s.scratch.scratch_buf
      let ks' := k6StateOfScratch L scr'
      s'.LengthsOk c → (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
      K6Inv L P ks' → ks'.nv = nv → K6TailEq L ks ks' → ks'.nassump = ks.nassump →
      k6AssumpLitsS L scr' = k6AssumpLitsS L s.scratch.scratch_buf → ks'.neq = ks.neq →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call (as := [i64, i32]) (bs := []) "full_m6_sweep_rand_phases"
      (Arg.var c.hdr, Arg.var nv, ()) k) m := by
  m6_call hRand
  exact ⟨c, s, P, L, R, rfl, hlen, hLscr, hLmv, hK, hnv, hm, hk⟩

private theorem m6_call_k6_solve {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hSolve : Γ.Has "full_k6_solve" step13K6SolveSpec)
    {c : FullCfg} {s : FullState} {P : (Nat → Bool) → Prop} {L : K6Layout}
    {tlim : Val i64} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Tup Val [i64] → Expr Val Cont rs}
    (hlen : s.LengthsOk c) (hLscr : L.scrLen = c.scratch_cap)
    (hLmv : L.maxV = k6MaxV c.scratch_cap)
    (hK : K6Inv L P (k6StateOfScratch L s.scratch.scratch_buf))
    (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ (r fuel' : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState :=
        { s with core := { s.core with fuel := fuel' }
                 scratch := { s.scratch with scratch_buf := scr' } }
      let ks := k6StateOfScratch L s.scratch.scratch_buf
      let ks' := k6StateOfScratch L scr'
      s'.LengthsOk c → fuel'.toNat ≤ s.core.fuel.toNat →
      (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
      K6Inv L P ks' → K6TrailSynced ks' → ks'.nv = ks.nv → K6TailEq L ks ks' →
      ks'.nassump = ks.nassump →
      k6AssumpLitsS L scr' = k6AssumpLitsS L s.scratch.scratch_buf → ks'.neq = ks.neq →
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
      (r = 20#64 → ∀ β, P β → ¬ (unitsCnf (k6AssumpLitsS L scr')).Sat β) →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call (as := [i64, i64]) (bs := [i64]) "full_k6_solve"
      (Arg.var c.hdr, Arg.var tlim, ()) k) m := by
  m6_call hSolve
  exact ⟨c, s, P, L, R, rfl, hlen, hLscr, hLmv, hK, hm, hk⟩

private theorem m6_call_k6_flip {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hFlip : Γ.Has "full_k6_flip" step13K6FlipSpec)
    {c : FullCfg} {s : FullState} {P : (Nat → Bool) → Prop} {L : K6Layout}
    {lit : Val i32} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Tup Val [.bool] → Expr Val Cont rs}
    (hlen : s.LengthsOk c) (hLscr : L.scrLen = c.scratch_cap)
    (hLmv : L.maxV = k6MaxV c.scratch_cap)
    (hK : K6Inv L P (k6StateOfScratch L s.scratch.scratch_buf))
    (hlit : lit.toNat < 2 * (k6StateOfScratch L s.scratch.scratch_buf).nv.toNat)
    (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ (ok : Bool) (scr' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      let ks := k6StateOfScratch L s.scratch.scratch_buf
      let ks' := k6StateOfScratch L scr'
      s'.LengthsOk c → (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
      K6Inv L P ks' → ks'.nv = ks.nv → K6TailEq L ks ks' → ks'.nassump = ks.nassump →
      k6AssumpLitsS L scr' = k6AssumpLitsS L s.scratch.scratch_buf → ks'.neq = ks.neq →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k (ok, ())) m') :
    wp Γ Q X (.call (as := [i64, i32]) (bs := [.bool]) "full_k6_flip"
      (Arg.var c.hdr, Arg.var lit, ()) k) m := by
  m6_call hFlip
  exact ⟨c, s, P, L, R, rfl, hlen, hLscr, hLmv, hK, hlit, hm, hk⟩

private theorem m6_call_sweep_solve {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hSolve : Γ.Has "full_m6_sweep_solve" fullM6SweepSolveSpec)
    {c : FullCfg} {s : FullState} {P : (Nat → Bool) → Prop} {L : K6Layout}
    {nv : Val i32} {tlim : Val i64} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Tup Val [i64] → Expr Val Cont rs}
    (hlen : s.LengthsOk c) (hLscr : L.scrLen = c.scratch_cap)
    (hLmv : L.maxV = k6MaxV c.scratch_cap)
    (hK : K6Inv L P (k6StateOfScratch L s.scratch.scratch_buf))
    (hnv : (k6StateOfScratch L s.scratch.scratch_buf).nv = nv)
    (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ (r fuel' : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState :=
        { s with core := { s.core with fuel := fuel' }
                 scratch := { s.scratch with scratch_buf := scr' } }
      let ks := k6StateOfScratch L s.scratch.scratch_buf
      let ks' := k6StateOfScratch L scr'
      s'.LengthsOk c → fuel'.toNat ≤ s.core.fuel.toNat →
      (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
      K6Inv L P ks' → K6TrailSynced ks' → ks'.nv = nv → K6TailEq L ks ks' →
      ks'.nassump = ks.nassump →
      k6AssumpLitsS L scr' = k6AssumpLitsS L s.scratch.scratch_buf → ks'.neq = ks.neq →
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
      (r = 20#64 → ∀ β, P β → ¬ (unitsCnf (k6AssumpLitsS L scr')).Sat β) →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (.call (as := [i64, i32, i64]) (bs := [i64]) "full_m6_sweep_solve"
      (Arg.var c.hdr, Arg.var nv, Arg.var tlim, ()) k) m := by
  m6_call hSolve
  exact ⟨c, s, P, L, R, rfl, hlen, hLscr, hLmv, hK, hnv, hm, hk⟩

private theorem m6_call_refine_sig {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hRef : Γ.Has "full_m6_sweep_refine_sig" fullM6SweepRefineSigSpec)
    {c : FullCfg} {s : FullState} {nv bit_idx : Val i32} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Tup Val [] → Expr Val Cont rs}
    (hlen : s.LengthsOk c) (hcap : k6MinScr ≤ c.scratch_cap)
    (hnv_mv : nv.toNat ≤ k6MaxV c.scratch_cap) (hnv_mx : nv.toNat ≤ 2 * c.max_vars)
    (hcone : ∀ i < nv.toNat, (s.scratch.work_stk1[i]?.getD 0#32).toNat < s.core.cur_vars)
    (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ sig' m', sig'.length = c.max_vars →
      (FullMem c { s with scratch := { s.scratch with sim_sig := sig' } } ⋆ R) m' →
      wp Γ Q X (k ()) m') :
    wp Γ Q X (.call (as := [i64, i32, i32]) (bs := []) "full_m6_sweep_refine_sig"
      (Arg.var c.hdr, Arg.var nv, Arg.var bit_idx, ()) k) m := by
  m6_call hRef
  exact ⟨c, s, R, rfl, hlen, hcap, hnv_mv, hnv_mx, hcone, hm, hk⟩

private theorem m6_call_flip_round {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hFlipR : Γ.Has "full_m6_sweep_flip_round" fullM6SweepFlipRoundSpec)
    {c : FullCfg} {s : FullState} {P : (Nat → Bool) → Prop} {L : K6Layout}
    {nv : Val i32} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Tup Val [i32] → Expr Val Cont rs}
    (hlen : s.LengthsOk c) (hLscr : L.scrLen = c.scratch_cap)
    (hLmv : L.maxV = k6MaxV c.scratch_cap)
    (hK : K6Inv L P (k6StateOfScratch L s.scratch.scratch_buf))
    (hnv : (k6StateOfScratch L s.scratch.scratch_buf).nv = nv)
    (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ ret scr' m',
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      let ks := k6StateOfScratch L s.scratch.scratch_buf
      let ks' := k6StateOfScratch L scr'
      s'.LengthsOk c → (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
      K6Inv L P ks' → ks'.nv = nv → K6TailEq L ks ks' → ks'.nassump = ks.nassump →
      k6AssumpLitsS L scr' = k6AssumpLitsS L s.scratch.scratch_buf → ks'.neq = ks.neq →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k (ret, ())) m') :
    wp Γ Q X (.call (as := [i64, i32]) (bs := [i32]) "full_m6_sweep_flip_round"
      (Arg.var c.hdr, Arg.var nv, ()) k) m := by
  m6_call hFlipR
  exact ⟨c, s, P, L, R, rfl, hlen, hLscr, hLmv, hK, hnv, hm, hk⟩

private theorem m6_unsat_empty_assump {F_cur : List (List Nat)} {ws : List (BitVec 32)}
    {nv : Nat} {L : K6Layout} {scr : List (BitVec 32)}
    (hna : (k6StateOfScratch L scr).nassump = 0#32)
    (hunsat : ∀ β, ConeModelSet F_cur ws nv β → ¬ (unitsCnf (k6AssumpLitsS L scr)).Sat β) :
    (cnfOfClauses F_cur).Unsat := by
  refine m6_coneModelSet_unsat_of_empty (F_cur := F_cur) (cone_v := ws) (nv := nv) fun β hcon => ?_
  have hnil : k6AssumpLitsS L scr = [] := by
    unfold k6AssumpLitsS k6AssumpLits; rw [hna]; simp
  apply hunsat β hcon
  rw [hnil, sat_unitsCnf_iff]
  intro _ hl; cases hl

private abbrev m6SimSt (s : FullState) (fu : BitVec 64) (sig : List (BitVec 64))
    (scr : List (BitVec 32)) : FullState :=
  { s with
    core := { s.core with fuel := fu }
    scratch := { s.scratch with sim_sig := sig, scratch_buf := scr } }

private theorem m6_coneOk_sim {c : FullCfg} {F_cur : List (List Nat)} {L : K6Layout}
    {s : FullState} {fuel' : BitVec 64} {sig' : List (BitVec 64)} {scr' : List (BitVec 32)}
    {nv : Nat}
    (hcone : M6SweepConeOk F_cur s nv) (hL : L.scrLen = c.scratch_cap)
    (hLmv : L.maxV = k6MaxV c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hscr' : scr'.length = c.scratch_cap)
    (hK : K6Inv L (ConeModelSet F_cur s.scratch.work_stk1 nv) (k6StateOfScratch L scr'))
    (hnv : (k6StateOfScratch L scr').nv = BitVec.ofNat 32 nv) :
    M6SweepConeOk F_cur
      { s with
        core := { s.core with fuel := fuel' }
        scratch := { s.scratch with sim_sig := sig', scratch_buf := scr' } } nv :=
  m6_coneOk_of_tailEq hcone hL hLmv hscr hscr' hK hnv

private theorem m6_coneHwm_sim {c : FullCfg} {L : K6Layout} {s : FullState}
    {ks0 ks' : K6State} {scr' : List (BitVec 32)}
    (hLscr : L.scrLen = c.scratch_cap) (hLmv : L.maxV = k6MaxV c.scratch_cap)
    (hks' : ks' = k6StateOfScratch L scr')
    (hhwm0 : K6HwmClean L (s.scratch.glue_used[33]?.getD 0#32) ks0) (htl : K6TailEq L ks0 ks')
    (hhw_ok : s.scratch.glue_used[33]? = some 0xFFFFFFFF#32 ∨
      ks0.nv.toNat ≤ (s.scratch.glue_used[33]?.getD 0#32).toNat)
    (hnv' : ks'.nv = ks0.nv) :
    ∃ L' : K6Layout, L'.scrLen = c.scratch_cap ∧ L'.maxV = k6MaxV c.scratch_cap ∧
      let ks1 := k6StateOfScratch L' scr'
      K6HwmClean L' (s.scratch.glue_used[33]?.getD 0#32) ks1 ∧
      (s.scratch.glue_used[33]? = some 0xFFFFFFFF#32 ∨
        ks1.nv.toNat ≤ (s.scratch.glue_used[33]?.getD 0#32).toNat) := by
  let gu33 := s.scratch.glue_used[33]?.getD 0#32
  have hhw_ok' : gu33 = 0xFFFFFFFF#32 ∨ ks0.nv.toNat ≤ gu33.toNat := by
    rcases hhw_ok with h | h
    · exact Or.inl (by dsimp [gu33]; rw [h]; rfl)
    · exact Or.inr h
  refine ⟨L, hLscr, hLmv, ?_⟩
  dsimp only
  rw [← hks']
  refine ⟨m6_coneHwm_of_tailEq hhwm0 htl hhw_ok', ?_⟩
  rw [hnv']
  exact hhw_ok

/-! ## 2. `full_m6_sweep_refine_sig_wp` (`fullM6SweepRefineSigSpec`) -/

private theorem m6_sweep_refine_sig_core (Γ : Env)
    (hMaxV : Γ.Has "full_m6_max_v" m6MaxVSpec)
    {c : FullCfg} {s : FullState} {nv bit_idx : BitVec 32} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post []} {X : XPost}
    (hlen : s.LengthsOk c) (hcap : k6MinScr ≤ c.scratch_cap)
    (hnv_mv : nv.toNat ≤ k6MaxV c.scratch_cap) (hnv_mx : nv.toNat ≤ 2 * c.max_vars)
    (hcone : ∀ i < nv.toNat, (s.scratch.work_stk1[i]?.getD 0#32).toNat < s.core.cur_vars)
    (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ sig' m', sig'.length = c.max_vars →
      (FullMem c { s with scratch := { s.scratch with sim_sig := sig' } } ⋆ R) m' → Q () m') :
    Func.wp Γ full_m6_sweep_refine_sig_body (c.hdr, nv, bit_idx, ()) m Q X := by
  have hcv_le := hlen.core_ok.cur_vars_le
  have hws_len := hlen.scratch_ok.work_stk1_len
  have hsig_len := hlen.scratch_ok.sim_sig_len
  have hscr_len := hlen.scratch_ok.scratch_buf_len
  let L := k6LayoutOfCap c.scratch_cap hcap c.hscr
  have hL_len : L.scrLen = c.scratch_cap := k6LayoutOfCap_scrLen hcap c.hscr
  have hL_mv : L.maxV = k6MaxV c.scratch_cap := rfl
  have hmL := L.hmaxV
  have hmv_pos := m6_maxV_pos hL_mv
  have hmv_lt30 := m6_maxV_lt30 hL_mv
  have hmv_eq := m6_mv32_eq hL_mv
  have hkptr_c0 := m6_k6Ptr_eq hL_mv hmv_lt30
  have hvals_c0 : L.kPtr c.pScratchBuf +
      ((32 : BitVec 32) + (10 : BitVec 32) * L.mv32).setWidth 64 * 4 =
      L.kPtr c.pScratchBuf + BitVec.ofNat 64 (4 * L.oVals) :=
    k6_ptr_vals L (L.kPtr c.pScratchBuf)
  unfold Func.wp full_m6_sweep_refine_sig_body
  m6_steps
  refine m6_call_max_v hMaxV (m6_scrCap_lt64 c) ?_
  m6_split
  · exfalso
    have h0 := congrArg BitVec.toNat hc
    rw [hmv_eq, k6_mv32_toNat] at h0; simp at h0; omega
  clear hc
  m6_split
  · exfalso
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc; omega
  clear hc
  m6_to_group
  refine wp_loop_inv (ts := [i32])
    (fun (i, ()) ml => i.toNat ≤ nv.toNat ∧ ∃ sig : List (BitVec 64),
      sig.length = c.max_vars ∧
      (FullMem c { s with scratch := { s.scratch with sim_sig := sig } } ⋆ R) ml)
    (fun (i, ()) _ => nv.toNat - i.toNat)
    (fun _ hJ => by
      m6_steps; exact hJ (0#32, ()) m ⟨Nat.zero_le _, s.scratch.sim_sig, hsig_len, hm⟩)
    (fun _ (i, ()) ml ⟨hi_le, sig, hsigL, hml⟩ hJ => by
      m6_split; rotate_left
      · have hi_eq : i.toNat = nv.toNat := by bv_omega
        m6_steps; exact hQ sig ml hsigL hml
      have hi_lt : i.toNat < nv.toNat := hc
      let st : FullState := { s with scratch := { s.scratch with sim_sig := sig } }
      have hi_ws : (BitVec.setWidth 64 i).toNat < st.scratch.work_stk1.length := by
        dsimp only [st]; rw [hws_len, bv_c0_zext32_64]; omega
      have hgv_lt : (st.scratch.work_stk1[(BitVec.setWidth 64 i).toNat]'hi_ws).toNat <
          c.max_vars := by
        have hg := hcone i.toNat hi_lt
        rw [List.getElem?_eq_getElem (by rw [hws_len]; omega), Option.getD_some] at hg
        simp only [st, bv_c0_zext32_64]; exact Nat.lt_of_lt_of_le hg hcv_le
      have hgv_sig : (BitVec.setWidth 64
          (st.scratch.work_stk1[(BitVec.setWidth 64 i).toNat]'hi_ws)).toNat <
          st.scratch.sim_sig.length := by
        dsimp only [st] at *; rw [hsigL, bv_c0_zext32_64]; exact hgv_lt
      have hi_2v : (i <<< (1 : Nat)).toNat < 2 * L.maxV := by
        have h1 := m6_bv32_shl1_lt (by omega : i.toNat < 2 ^ 31); omega
      have hi1 : (i + 1#32).toNat = i.toNat + 1 := m6_bv32_add1 (by omega)
      m6_to_group; refine wp_unroll_group fun _ _ => ?_
      change wp _ _ _ _ _
      c0_hsteps_nogrp
      dsimp only [Prod.fst]
      try rw [hkptr_c0]; try rw [hmv_eq]; try rw [hvals_c0]
      open scoped FullK6DynMem in m6_split
      all_goals
        change wp _ _ _ _ _
        c0_hsteps
        try dsimp only [Prod.fst]
        try rw [hkptr_c0]; try rw [hmv_eq]; try rw [hvals_c0]
        open scoped FullK6DynMem in c0_hsteps!
        refine hJ (i + 1#32, ()) _
          (by dsimp only; rw [hi1]; exact Nat.sub_lt_sub_left hi_lt (by omega))
          ⟨by omega, _, ?_, by assumption⟩
        simp [hsigL])

theorem full_m6_sweep_refine_sig_wp (Γ : Env)
    (hMaxV : Γ.Has "full_m6_max_v" m6MaxVSpec) :
    ∀ args m Q X, fullM6SweepRefineSigSpec args m Q X →
      Func.wp Γ full_m6_sweep_refine_sig_body args m Q X := by
  rintro ⟨h, nv, bit_idx, ⟨⟩⟩ m Q X
    ⟨c, s, R, rfl, hlen, hcap, hnv_mv, hnv_mx, hcone, hm, hQ⟩
  exact m6_sweep_refine_sig_core Γ hMaxV hlen hcap hnv_mv hnv_mx hcone hm hQ

/-! ## 3. `full_m6_sweep_rand_phases_wp` (`fullM6SweepRandPhasesSpec`) -/

theorem full_m6_sweep_rand_phases_wp (Γ : Env)
    (hMaxV : Γ.Has "full_m6_max_v" m6MaxVSpec) :
    ∀ args m Q X, fullM6SweepRandPhasesSpec args m Q X →
      Func.wp Γ full_m6_sweep_rand_phases_body args m Q X := by
  rintro ⟨h, nv, ⟨⟩⟩ m Q X ⟨c, s, P, L, R, rfl, hlen, hL_len, hL_mv, hK0, hnv_eq, hm, hQ⟩
  have hscr_len := hlen.scratch_ok.scratch_buf_len
  have hmL := L.hmaxV
  have hnv_le : nv.toNat ≤ L.maxV := by rw [← hnv_eq]; exact hK0.clauses.nv_le
  have hmv_pos := m6_maxV_pos hL_mv
  have hmv_lt30 := m6_maxV_lt30 hL_mv
  have hmv_eq := m6_mv32_eq hL_mv
  have hkptr_c0 := m6_k6Ptr_eq hL_mv hmv_lt30
  have hfl_c0 : L.kPtr c.pScratchBuf +
      ((32 : BitVec 32) + (6 : BitVec 32) * L.mv32).setWidth 64 * 4 =
      L.kPtr c.pScratchBuf + BitVec.ofNat 64 (4 * L.oFlags) :=
    k6_ptr_flags L (L.kPtr c.pScratchBuf)
  unfold Func.wp full_m6_sweep_rand_phases_body
  m6_steps
  refine m6_call_max_v hMaxV (m6_scrCap_lt64 c) ?_
  m6_split
  · exfalso
    have h0 := congrArg BitVec.toNat hc
    rw [hmv_eq, k6_mv32_toNat] at h0; simp at h0; omega
  clear hc
  m6_split
  · exfalso
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc; omega
  clear hc
  change wp _ _ _ _ _
  c0_hsteps_nogrp
  try dsimp only [Prod.fst]
  try rw [hkptr_c0]; try rw [hmv_eq]
  open scoped FullK6DynMem in c0_hsteps_nogrp
  refine wp_join_group (ts := [i32]) (fun (_, ()) m0 => (FullMem c s ⋆ R) m0)
    (fun _ (rs0, ()) m0 hm0 => by
      m6_to_group
      let ks0 := k6StateOfScratch L s.scratch.scratch_buf
      have hm_ka0 : (K6MemA L (L.kPtr c.pScratchBuf) ks0 ⋆ (FullK6Frame c L s ⋆ R)) m0 :=
        m6_split_k6 hL_len hscr_len hK0 hm0
      refine wp_loop_inv (ts := [i32, i64, i32])
        (fun (rsL, rbits, i, ()) ml => i.toNat ≤ nv.toNat ∧ ∃ ksL : K6State,
          K6Inv L P ksL ∧ ksL.nv = nv ∧ K6TailEq L ks0 ksL ∧
          ksL.nassump = ks0.nassump ∧ k6AssumpLits ksL = k6AssumpLits ks0 ∧
          ksL.neq = ks0.neq ∧ (K6MemA L (L.kPtr c.pScratchBuf) ksL ⋆ (FullK6Frame c L s ⋆ R)) ml)
        (fun (_, _, i, ()) _ => nv.toNat - i.toNat)
        (fun _ hJ => by
          m6_steps
          exact hJ (m6_xorshift32_step rs0, (m6_xorshift32_step rs0).setWidth 64, 0#32, ()) m0
            ⟨Nat.zero_le _, ks0, hK0, hnv_eq, k6TailEq_refl L ks0, rfl, rfl, rfl, hm_ka0⟩)
        (fun _ (rsL, rbits, i, ()) ml
            ⟨hi_le, ksL, hKL, hnvL, htlL, hnaL, hassL, hnqL, hml⟩ hJ => by
          m6_split
          · have hi_lt : i.toNat < nv.toNat := hc
            clear hc
            have hi_mv : i.toNat < L.maxV := by omega
            have hi1 : (i + 1#32).toNat = i.toNat + 1 := m6_bv32_add1 (by omega)
            m6_to_group
            refine wp_join_group (ts := [i32, i64])
              (fun (_, _, ()) m_rb =>
                (K6MemA L (L.kPtr c.pScratchBuf) ksL ⋆ (FullK6Frame c L s ⋆ R)) m_rb)
              (fun _ (rs1, rb1, ()) m_rb hm_rb => by
                change wp _ _ _ _ _
                c0_hsteps_nogrp
                try dsimp only [Prod.fst]
                try rw [hkptr_c0]; try rw [hmv_eq]; try rw [hfl_c0]
                open scoped K6MemATactics K6PtrTactics in c0_hsteps!
                let v_fl : BitVec 32 := (ksL.flags[i.toNat]?.getD 0#32 &&& ~~~1#32) |||
                  (rb1.setWidth 32 &&& 1#32)
                have hK1 := k6Inv_set_flags_bit0 (i := i.toNat) hi_mv (rb1.setWidth 32) hKL
                have htl1 : K6TailEq L ksL (ksL.putArr .flags i.toNat v_fl) :=
                  k6TailEq_putArr_var (Or.inr (Or.inr rfl)) (by rw [hnvL]; exact hi_lt) v_fl
                exact hJ (rs1, rb1 >>> 1#64, i + 1#32, ()) _
                  (by dsimp only; rw [hi1]; exact Nat.sub_lt_sub_left hi_lt (by omega))
                  ⟨by omega, ksL.putArr .flags i.toNat v_fl, hK1, hnvL,
                   k6TailEq_trans htlL htl1, hnaL, hassL, hnqL, by assumption⟩)
              (fun _ hJrb => by
                m6_split
                · m6_split
                  · m6_steps; exact hJrb (_, _, ()) ml hml
                  · m6_steps; exact hJrb (_, _, ()) ml hml
                · m6_steps; exact hJrb (_, _, ()) ml hml)
          · clear hc
            obtain ⟨hslL, hpreL, hofL, hm_f⟩ := m6_join_k6_ofSlab hL_len hscr_len hKL.shapes hml
            let scrL_full := s.scratch.scratch_buf.take L.k6Base ++ ksL.toSlab
            let sL : FullState := { s with scratch := { s.scratch with scratch_buf := scrL_full } }
            have hK_sL : K6Inv L P (k6StateOfScratch L sL.scratch.scratch_buf) := by
              rw [hofL]; exact hKL
            have hbd_25 : L.k6Base + 25 < scrL_full.length := by
              have := L.hmaxV; have := L.hacap
              change L.k6Base + 25 < (s.scratch.scratch_buf.take L.k6Base ++ ksL.toSlab).length
              rw [hslL, ← hL_len]; unfold K6Layout.scrLen K6Layout.k6Fixed; omega
            have hbd_19 : L.k6Base + 19 < (scrL_full.set (L.k6Base + 25) rsL).length := by
              rw [List.length_set]; omega
            change wp _ _ _ _ _
            c0_hsteps_nogrp
            try dsimp only [Prod.fst]
            try rw [hkptr_c0]; try rw [hmv_eq]
            open scoped FullK6DynMem in c0_hsteps!
            let scr2 := sL.scratch.scratch_buf.set (L.k6Base + 25) rsL
            let scr3 := scr2.set (L.k6Base + 19) (scr2[L.k6Base + 19] ^^^ 1#32)
            let s3 : FullState := { s with scratch := { s.scratch with scratch_buf := scr3 } }
            have hof2 : k6StateOfScratch L scr2 = k6PutHdr25 ksL rsL := by
              rw [m6_k6StateOfScratch_set25 L _ rsL (hL_len.trans hslL.symm), hofL]
            have hK2 : K6Inv L P (k6StateOfScratch L scr2) := by
              rw [hof2]; exact k6PutHdr25_inv rsL hKL
            have htl2 : K6TailEq L ks0 (k6StateOfScratch L scr2) := by
              rw [hof2]; exact k6TailEq_trans htlL (k6PutHdr25_tailEq rsL)
            have hscr2_len : scr2.length = c.scratch_cap := by
              simp only [scr2, List.length_set]; exact hslL
            have hof3 : k6StateOfScratch L scr3 =
                (k6PutHdr25 ksL rsL).putHdr .phase (scr2[L.k6Base + 19] ^^^ 1#32) := by
              rw [m6_k6StateOfScratch_set19 L scr2 _ (hL_len.trans hscr2_len.symm), hof2]
            have hK3 : K6Inv L P (k6StateOfScratch L scr3) := by
              rw [hof3]; exact k6Inv_set_phase _ (hof2 ▸ hK2)
            have htl3 : K6TailEq L ks0 (k6StateOfScratch L scr3) := by
              rw [hof3]
              exact k6TailEq_trans (hof2 ▸ htl2)
                (k6TailEq_of_putHdr_ne_nv (f := .phase) (by decide) _)
            have hscr3_len : scr3.length = c.scratch_cap := by
              simp only [scr3, List.length_set]; exact hscr2_len
            have hpre3 : ∀ j < L.k6Base, scr3[j]? = s.scratch.scratch_buf[j]? := fun j hj => by
              dsimp only [scr3, scr2]
              rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
              exact hpreL j hj
            have hlen3 : s3.LengthsOk c :=
              ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hscr3_len }⟩
            exact hQ scr3 _ hlen3 hpre3 hK3 (by rw [hof3]; exact hnvL) htl3
              (by rw [hof3]; exact hnaL)
              (by unfold k6AssumpLitsS; rw [hof3]; exact hassL)
              (by rw [hof3]; exact hnqL) (by assumption)))
    (fun _ hJ0 => by
      m6_split
      · m6_steps; exact hJ0 (_, ()) _ (by assumption)
      · m6_steps; exact hJ0 (_, ()) _ (by assumption))

/-! ## 4. `full_m6_sweep_solve_wp` (`fullM6SweepSolveSpec`) -/

theorem full_m6_sweep_solve_wp (Γ : Env)
    (hRand : Γ.Has "full_m6_sweep_rand_phases" fullM6SweepRandPhasesSpec)
    (hSolve : Γ.Has "full_k6_solve" step13K6SolveSpec) :
    ∀ args m Q X, fullM6SweepSolveSpec args m Q X →
      Func.wp Γ full_m6_sweep_solve_body args m Q X := by
  rintro ⟨h, nv, tick_lim, ⟨⟩⟩ m Q X ⟨c, s, P, L, R, rfl, hlen, hL_len, hL_mv, hK0, hnv0, hm, hQ⟩
  unfold Func.wp full_m6_sweep_solve_body
  refine m6_call_rand_phases hRand hlen hL_len hL_mv hK0 hnv0 hm
    fun scr1 m1 hlen1 hpre1 hK1 hnv1 htl1 hna1 hass1 hnq1 hm1 => ?_
  m6_steps
  refine m6_call_k6_solve hSolve hlen1 hL_len hL_mv hK1 hm1
    fun r fuel2 scr2 m2 hlen2 hfuel2 hpre2 hK2 hsync2 hnv2 htl2 hna2 hass2 hnq2 hr huns hm2 => ?_
  m6_steps
  exact hQ r fuel2 scr2 m2 hlen2 hfuel2
    (fun i hi => (hpre2 i hi).trans (hpre1 i hi))
    hK2 hsync2 (hnv2.trans hnv1) (k6TailEq_trans htl1 htl2) (hna2.trans hna1)
    (hass2.trans hass1) (hnq2.trans hnq1) hr huns hm2

/-! ## 5. `full_m6_sweep_flip_round_wp` (`fullM6SweepFlipRoundSpec`) -/

theorem full_m6_sweep_flip_round_wp (Γ : Env)
    (hMaxV : Γ.Has "full_m6_max_v" m6MaxVSpec)
    (hFlip : Γ.Has "full_k6_flip" step13K6FlipSpec) :
    ∀ args m Q X, fullM6SweepFlipRoundSpec args m Q X →
      Func.wp Γ full_m6_sweep_flip_round_body args m Q X := by
  rintro ⟨h, nv, ⟨⟩⟩ m Q X ⟨c, s, P, L, R, rfl, hlen, hL_len, hL_mv, hK0, hnv_eq, hm, hQ⟩
  have hscr_len := hlen.scratch_ok.scratch_buf_len
  have hmL := L.hmaxV
  have hnv_le : nv.toNat ≤ L.maxV := by rw [← hnv_eq]; exact hK0.clauses.nv_le
  have hmv_pos := m6_maxV_pos hL_mv
  have hmv_lt30 := m6_maxV_lt30 hL_mv
  have hmv_eq := m6_mv32_eq hL_mv
  have hkptr_c0 := m6_k6Ptr_eq hL_mv hmv_lt30
  have hvals_c0 : L.kPtr c.pScratchBuf +
      ((32 : BitVec 32) + (10 : BitVec 32) * L.mv32).setWidth 64 * 4 =
      L.kPtr c.pScratchBuf + BitVec.ofNat 64 (4 * L.oVals) :=
    k6_ptr_vals L (L.kPtr c.pScratchBuf)
  unfold Func.wp full_m6_sweep_flip_round_body
  m6_steps
  m6_split
  · m6_steps
    exact hQ 0#32 s.scratch.scratch_buf m hlen (fun _ _ => rfl) hK0 hnv_eq
      (k6TailEq_refl L _) rfl rfl rfl hm
  have hnv_pos : 0 < nv.toNat := by bv_omega
  clear hc
  m6_steps
  refine m6_call_max_v hMaxV (m6_scrCap_lt64 c) ?_
  m6_split
  · exfalso
    have h0 := congrArg BitVec.toNat hc
    rw [hmv_eq, k6_mv32_toNat] at h0; simp at h0; omega
  clear hc
  m6_split
  · exfalso
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc; omega
  clear hc
  let ks0 := k6StateOfScratch L s.scratch.scratch_buf
  change wp _ _ _ _ _
  c0_hsteps_nogrp
  try dsimp only [Prod.fst]
  try rw [hkptr_c0]; try rw [hmv_eq]
  open scoped FullK6DynMem in c0_hsteps_nogrp
  refine wp_join_group (ts := [i32]) (fun (_, ()) m0 => (FullMem c s ⋆ R) m0)
    (fun _ (rs0, ()) m0 hm0 => by
      m6_to_group
      let rs1 := m6_xorshift32_step rs0
      let start := rs1 % nv
      let rs2 := m6_xorshift32_step rs1
      let rb0 := rs2.setWidth 64
      have hstart_lt : start.toNat < nv.toNat := by
        dsimp only [start]; rw [BitVec.toNat_umod]; exact Nat.mod_lt _ hnv_pos
      refine wp_loop_inv (ts := [i32, i64, i32, i32])
        (fun (rsL, rbits, flipped, step, ()) ml =>
          step.toNat ≤ nv.toNat ∧ ∃ scrL : List (BitVec 32),
          scrL.length = c.scratch_cap ∧
          (∀ j < L.k6Base, scrL[j]? = s.scratch.scratch_buf[j]?) ∧
          K6Inv L P (k6StateOfScratch L scrL) ∧ (k6StateOfScratch L scrL).nv = nv ∧
          K6TailEq L ks0 (k6StateOfScratch L scrL) ∧
          (k6StateOfScratch L scrL).nassump = ks0.nassump ∧
          k6AssumpLitsS L scrL = k6AssumpLitsS L s.scratch.scratch_buf ∧
          (k6StateOfScratch L scrL).neq = ks0.neq ∧
          (FullMem c { s with scratch := { s.scratch with scratch_buf := scrL } } ⋆ R) ml)
        (fun (_, _, _, step, ()) _ => nv.toNat - step.toNat)
        (fun _ hJ => by
          m6_steps
          exact hJ (rs2, rb0, 0#32, 0#32, ()) m0
            ⟨Nat.zero_le _, s.scratch.scratch_buf, hscr_len, fun _ _ => rfl, hK0, hnv_eq,
             k6TailEq_refl L ks0, rfl, rfl, rfl, hm0⟩)
        (fun _ (rsL, rbits, flipped, step, ()) ml
            ⟨hs_le, scrL, hslL, hpreL, hKL, hnvL, htlL, hnaL, hassL, hnqL, hml⟩ hJ => by
          let sL : FullState := { s with scratch := { s.scratch with scratch_buf := scrL } }
          have hlenL : sL.LengthsOk c :=
            ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hslL }⟩
          m6_split
          · have hs_lt : step.toNat < nv.toNat := hc
            clear hc
            have hs1 : (step + 1#32).toNat = step.toNat + 1 := m6_bv32_add1 (by omega)
            m6_to_group
            refine wp_join_group (ts := [i32, i64])
              (fun (_, _, ()) m_rb => (FullMem c sL ⋆ R) m_rb)
              (fun _ (rs1L, rb1, ()) m_rb hm_rb => by
                m6_to_group
                refine wp_join_group (ts := [i32])
                  (fun (fl2, ()) m2 => ∃ scr2 : List (BitVec 32),
                    scr2.length = c.scratch_cap ∧
                    (∀ j < L.k6Base, scr2[j]? = s.scratch.scratch_buf[j]?) ∧
                    K6Inv L P (k6StateOfScratch L scr2) ∧ (k6StateOfScratch L scr2).nv = nv ∧
                    K6TailEq L ks0 (k6StateOfScratch L scr2) ∧
                    (k6StateOfScratch L scr2).nassump = ks0.nassump ∧
                    k6AssumpLitsS L scr2 = k6AssumpLitsS L s.scratch.scratch_buf ∧
                    (k6StateOfScratch L scr2).neq = ks0.neq ∧
                    (FullMem c { s with scratch := { s.scratch with scratch_buf := scr2 } } ⋆ R) m2)
                  (fun _ (fl2, ()) m2
                      ⟨scr2, hsl2, hpre2, hK2, hnv2, htl2, hna2, hass2, hnq2, hm2⟩ => by
                    m6_steps
                    exact hJ (rs1L, rb1 >>> 1#64, fl2, step + 1#32, ()) m2
                      (by dsimp only; rw [hs1]; exact Nat.sub_lt_sub_left hs_lt (by omega))
                      ⟨by omega, scr2, hsl2, hpre2, hK2, hnv2, htl2, hna2, hass2, hnq2, hm2⟩)
                  (fun _ hJfl => by
                    m6_split; rotate_left
                    · clear hc; m6_steps
                      exact hJfl (flipped, ()) m_rb
                        ⟨scrL, hslL, hpreL, hKL, hnvL, htlL, hnaL, hassL, hnqL, hm_rb⟩
                    clear hc; m6_to_group
                    refine wp_join_group (ts := [i32])
                      (fun (v, ()) mv_ => (FullMem c sL ⋆ R) mv_ ∧ v.toNat < nv.toNat)
                      (fun _ (v, ()) mv_ ⟨hmv_, hv_lt⟩ => by
                        have hv_2v : (v <<< (1 : Nat)).toNat < 2 * L.maxV := by
                          have h1 := m6_bv32_shl1_lt (by omega : v.toNat < 2 ^ 31); omega
                        m6_to_group
                        refine wp_join_group (ts := [i32])
                          (fun (lit, ()) mlit =>
                            (FullMem c sL ⋆ R) mlit ∧ lit.toNat < 2 * nv.toNat)
                          (fun _ (lit, ()) mlit ⟨hmlit, hlit_lt⟩ => by
                            m6_to_group; refine wp_unroll_group fun _ _ => ?_
                            refine m6_call_k6_flip hFlip hlenL hL_len hL_mv hKL
                              (by rw [hnvL]; exact hlit_lt) hmlit
                              fun ok scr2 m2 hlen2 hpre_f hK2 hnv2 htl_f hna2 hass2 hnq2 hm2 => ?_
                            have hpre2 : ∀ j < L.k6Base, scr2[j]? = s.scratch.scratch_buf[j]? :=
                              fun j hj => (hpre_f j hj).trans (hpreL j hj)
                            m6_split
                            · m6_steps
                              exact hJfl (flipped + 1#32, ()) m2
                                ⟨scr2, hlen2.scratch_ok.scratch_buf_len, hpre2, hK2,
                                 hnv2.trans hnvL, k6TailEq_trans htlL htl_f, hna2.trans hnaL,
                                 hass2.trans hassL, hnq2.trans hnqL, hm2⟩
                            · m6_steps
                              exact hJfl (flipped, ()) m2
                                ⟨scr2, hlen2.scratch_ok.scratch_buf_len, hpre2, hK2,
                                 hnv2.trans hnvL, k6TailEq_trans htlL htl_f, hna2.trans hnaL,
                                 hass2.trans hassL, hnq2.trans hnqL, hm2⟩)
                          (fun _ hJlit => by
                            change wp _ _ _ _ _
                            c0_hsteps_nogrp
                            try dsimp only [Prod.fst]
                            try rw [hkptr_c0]; try rw [hmv_eq]; try rw [hvals_c0]
                            open scoped FullK6DynMem in m6_split
                            · m6_steps
                              exact hJlit (v <<< (1 : Nat), ()) _ ⟨by assumption, by bv_omega⟩
                            · m6_steps
                              refine hJlit ((v <<< (1 : Nat)) ||| 1#32, ()) _ ⟨by assumption, ?_⟩
                              rw [m6_bv32_shl1_or_pol v 1#32 (by omega) (by decide)]
                              simp; omega))
                      (fun _ hJv => by
                        have hnv_bd : nv.toNat ≤ 8192 := Nat.le_trans hnv_le hmL.2
                        have hsum_lt : start.toNat + step.toNat < 2 ^ 32 := by omega
                        m6_split
                        · have hge_nv : nv ≤ start + step := hc
                          have h1 : (start + step - nv).toNat < nv.toNat := by bv_omega
                          m6_steps; exact hJv (start + step - nv, ()) _ ⟨hm_rb, h1⟩
                        · have hlt_nv : ¬ (nv ≤ start + step) := hc
                          have h1 : (start + step).toNat < nv.toNat := by bv_omega
                          m6_steps; exact hJv (start + step, ()) _ ⟨hm_rb, h1⟩)))
              (fun _ hJrb => by
                m6_split
                · m6_split
                  · m6_steps; exact hJrb (_, _, ()) ml hml
                  · m6_steps; exact hJrb (_, _, ()) ml hml
                · m6_steps; exact hJrb (_, _, ()) ml hml)
          · clear hc
            change wp _ _ _ _ _
            c0_hsteps_nogrp
            try dsimp only [Prod.fst]
            try rw [hkptr_c0]; try rw [hmv_eq]
            open scoped FullK6DynMem in c0_hsteps!
            let scr2 := scrL.set (L.k6Base + 25) rsL
            let s2 : FullState := { s with scratch := { s.scratch with scratch_buf := scr2 } }
            have hof2 : k6StateOfScratch L scr2 = k6PutHdr25 (k6StateOfScratch L scrL) rsL :=
              m6_k6StateOfScratch_set25 L scrL rsL (hL_len.trans hslL.symm)
            have hK2 : K6Inv L P (k6StateOfScratch L scr2) := by
              rw [hof2]; exact k6PutHdr25_inv rsL hKL
            have htl2 : K6TailEq L ks0 (k6StateOfScratch L scr2) := by
              rw [hof2]; exact k6TailEq_trans htlL (k6PutHdr25_tailEq rsL)
            have hscr2_len : scr2.length = c.scratch_cap := by
              simp only [scr2, List.length_set]; exact hslL
            have hpre2 : ∀ j < L.k6Base, scr2[j]? = s.scratch.scratch_buf[j]? := fun j hj => by
              dsimp only [scr2]; rw [List.getElem?_set_ne (by omega)]; exact hpreL j hj
            have hlen2 : s2.LengthsOk c :=
              ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hscr2_len }⟩
            exact hQ flipped scr2 _ hlen2 hpre2 hK2 (by rw [hof2]; exact hnvL) htl2
              (by rw [hof2]; exact hnaL)
              (by unfold k6AssumpLitsS; rw [hof2]; exact hassL)
              (by rw [hof2]; exact hnqL) (by assumption)))
    (fun _ hJ0 => by
      m6_split
      · m6_steps; exact hJ0 (_, ()) _ (by assumption)
      · m6_steps; exact hJ0 (_, ()) _ (by assumption))

/-! ## 6. `full_m6_sweep_sim_wp` (`fullM6SweepSimSpec`) -/

private def m6SimLoopExpr (hdr kPtr : Val i64) (nv : Val i32) (simLim : Val i64) :
    Expr Val Cont [i32] :=
  Expr.group
    (fun _ => Blocks.cons (fun pb : Tup Val [i32, i32] => Expr.ret (Arg.var pb.fst, ()))
      Blocks.nil)
    fun Jbrk =>
      Expr.group
        (fun Jl => Blocks.cons
          (fun p : Tup Val [i32, i32] =>
            Expr.let_ (Op.mk (.cmp .ult i32 .bool rfl) (Arg.var p.snd.fst, Arg.imm 16, ()))
              fun p1 =>
            Expr.jnz (Arg.var p1.fst)
              (Expr.let_ (Op.mk (.cmp .ult i32 .bool rfl) (Arg.var p.fst, Arg.imm 64, ()))
                fun p2 =>
               Expr.jnz (Arg.var p2.fst)
                 (Expr.let_ (Op.mk (.zext 32 64) (Arg.imm 11, ())) fun p3 =>
                  Expr.let_ (Op.mk (.mul i64) (Arg.var p3.fst, Arg.imm 4, ())) fun p4 =>
                  Expr.let_ (Op.mk (.add i64) (Arg.var kPtr, Arg.var p4.fst, ())) fun p5 =>
                  Expr.load i32 (Arg.var p5.fst) fun ld =>
                  Expr.let_ (Op.mk (.zext 32 64) (Arg.var ld, ())) fun p6 =>
                  Expr.let_ (Op.mk (.cmp .ult i64 .bool rfl)
                    (Arg.var p6.fst, Arg.var simLim, ())) fun p7 =>
                  Expr.jnz (Arg.var p7.fst)
                    (Expr.let_ (Op.mk (.add i64) (Arg.var hdr, Arg.imm 168, ())) fun p8 =>
                     Expr.load i64 (Arg.var p8.fst) fun ld =>
                     Expr.let_ (Op.mk (.cmp .ugt i64 .bool rfl) (Arg.var ld, Arg.imm 0, ()))
                       fun p9 =>
                     Expr.jnz (Arg.var p9.fst)
                       (Expr.call (as := [i64, i32]) (bs := [i32]) "full_m6_sweep_flip_round"
                         (Arg.var hdr, Arg.var nv, ()) fun p10 =>
                        Expr.let_ (Op.mk (.cmp .ugt i32 .bool rfl)
                          (Arg.var p10.fst, Arg.imm 0, ())) fun p11 =>
                        Expr.jnz (Arg.var p11.fst)
                          (Expr.call (as := [i64, i32, i32]) (bs := [])
                            "full_m6_sweep_refine_sig"
                            (Arg.var hdr, Arg.var nv, Arg.var p.fst, ()) fun _ =>
                           Expr.let_ (Op.mk (.add i32) (Arg.var p.fst, Arg.imm 1, ())) fun p13 =>
                           Expr.let_ (Op.mk (.add i32) (Arg.var p.snd.fst, Arg.imm 1, ()))
                             fun p14 =>
                           Expr.jump Jl.fst (Arg.var p13.fst, Arg.var p14.fst, ()))
                          (Expr.jump Jbrk.fst (Arg.var p.fst, Arg.var p.snd.fst, ())))
                       (Expr.jump Jbrk.fst (Arg.var p.fst, Arg.var p.snd.fst, ())))
                    (Expr.jump Jbrk.fst (Arg.var p.fst, Arg.var p.snd.fst, ())))
                 (Expr.jump Jbrk.fst (Arg.var p.fst, Arg.var p.snd.fst, ())))
              (Expr.jump Jbrk.fst (Arg.var p.fst, Arg.var p.snd.fst, ())))
          Blocks.nil)
        fun Jl => Expr.jump Jl.fst (Arg.imm 1, Arg.imm 0, ())

private theorem m6_sim_loop_wp {Γ : Env}
    (hRef : Γ.Has "full_m6_sweep_refine_sig" fullM6SweepRefineSigSpec)
    (hFlipR : Γ.Has "full_m6_sweep_flip_round" fullM6SweepFlipRoundSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {L : K6Layout}
    {s0 : FullState} {ks0 : K6State} {nv : BitVec 32} {simLim : BitVec 64}
    {R : Mem 64 → Prop} {m3 : Mem 64} {Q : Post [i32]} {X : XPost}
    (hinv0 : FullDenseInvW c F0 F_cur s0) (hcone0 : M6SweepConeOk F_cur s0 nv.toNat)
    (hLscr : L.scrLen = c.scratch_cap) (hLmv : L.maxV = k6MaxV c.scratch_cap)
    (hcap : k6MinScr ≤ c.scratch_cap) (hnv_mv : nv.toNat ≤ k6MaxV c.scratch_cap)
    (hnv_mx : nv.toNat ≤ 2 * c.max_vars)
    (hK0 : K6Inv L (ConeModelSet F_cur s0.scratch.work_stk1 nv.toNat)
      (k6StateOfScratch L s0.scratch.scratch_buf))
    (hnv_eq : (k6StateOfScratch L s0.scratch.scratch_buf).nv = nv)
    (htl0 : K6TailEq L ks0 (k6StateOfScratch L s0.scratch.scratch_buf))
    (hm3 : (FullMem c s0 ⋆ R) m3)
    (hQ : ∀ (rbit : BitVec 32) (sigX : List (BitVec 64)) (scrX : List (BitVec 32))
      (mX : Mem 64),
      let sX : FullState :=
        { s0 with scratch := { s0.scratch with sim_sig := sigX, scratch_buf := scrX } }
      FullDenseInvW c F0 F_cur sX → M6SweepConeOk F_cur sX nv.toNat →
      K6TailEq L ks0 (k6StateOfScratch L scrX) → (k6StateOfScratch L scrX).nv = nv →
      rbit ≠ 0xFFFFFFFF#32 → rbit.toNat ≤ 64 → (FullMem c sX ⋆ R) mX → Q (rbit, ()) mX) :
    wp Γ Q X (m6SimLoopExpr c.hdr (L.kPtr c.pScratchBuf) nv simLim) m3 := by
  have hlen0 := hinv0.1
  have hsig0 := hlen0.scratch_ok.sim_sig_len
  have hscr0 := hlen0.scratch_ok.scratch_buf_len
  have hws0 := hcone0.2.2.2.1
  let mkSt := fun (sigX : List (BitVec 64)) (scrX : List (BitVec 32)) =>
    ({ s0 with scratch := { s0.scratch with sim_sig := sigX, scratch_buf := scrX } } : FullState)
  unfold m6SimLoopExpr
  refine wp_join_group (ts := [i32, i32])
    (fun (rbit, _rnd, ()) mx => rbit.toNat ≤ 64 ∧ ∃ sigX scrX,
      sigX.length = c.max_vars ∧ scrX.length = c.scratch_cap ∧
      FullDenseInvW c F0 F_cur (mkSt sigX scrX) ∧
      M6SweepConeOk F_cur (mkSt sigX scrX) nv.toNat ∧
      K6TailEq L ks0 (k6StateOfScratch L scrX) ∧ (k6StateOfScratch L scrX).nv = nv ∧
      (FullMem c (mkSt sigX scrX) ⋆ R) mx)
    (fun _ (rbit, _rnd, ⟨⟩) mx ⟨hr_le, _, _, _, _, hdwX, hconeX, htlX, hnvX, hmx⟩ => by
      m6_steps
      exact hQ rbit _ _ mx hdwX hconeX htlX hnvX
        (fun hff => by have h1 := congrArg BitVec.toNat hff; simp at h1; omega) hr_le hmx)
    (fun _ hJbrk => by
      refine wp_loop_inv (ts := [i32, i32])
        (fun (rbit, round, ()) ml => round.toNat ≤ 16 ∧ rbit.toNat = round.toNat + 1 ∧
          ∃ sigL scrL, sigL.length = c.max_vars ∧ scrL.length = c.scratch_cap ∧
          K6Inv L (ConeModelSet F_cur s0.scratch.work_stk1 nv.toNat) (k6StateOfScratch L scrL) ∧
          (k6StateOfScratch L scrL).nv = nv ∧ K6TailEq L ks0 (k6StateOfScratch L scrL) ∧
          (FullMem c (mkSt sigL scrL) ⋆ R) ml)
        (fun (_, round, ()) _ => 16 - round.toNat)
        (fun _ hJl => by
          m6_steps
          exact hJl (1#32, 0#32, ()) m3
            ⟨Nat.zero_le _, rfl, s0.scratch.sim_sig, s0.scratch.scratch_buf, hsig0, hscr0,
             hK0, hnv_eq, htl0, hm3⟩)
        (fun _ (rbit, round, ()) ml
            ⟨hrd_le, hrb_eq, sigL, scrL, hsigL, hscrL, hKL, hnvL, htlL, hml⟩ hJl => by
          let sL := mkSt sigL scrL
          have hdwL : FullDenseInvW c F0 F_cur sL :=
            m6_fullDenseInvW_with_fuel_scr hinv0 hsigL hscrL
          have hconeL : M6SweepConeOk F_cur sL nv.toNat :=
            m6_coneOk_sim hcone0 hLscr hLmv hscr0 hscrL hKL (BitVec.eq_of_toNat_eq (by simp [hnvL]))
          have hm_ka : (K6MemA L (L.kPtr c.pScratchBuf) (k6StateOfScratch L scrL) ⋆
              (FullK6Frame c L sL ⋆ R)) ml :=
            m6_split_k6 (L := L) (s := sL) hLscr hscrL hKL hml
          open scoped K6MemATactics K6PtrTactics in
            m6_split; rotate_left
          · clear hc; m6_steps; exact hJbrk (rbit, round, ()) ml
              ⟨by omega, sigL, scrL, hsigL, hscrL, hdwL, hconeL, htlL, hnvL, hml⟩
          have hrd_lt : round.toNat < 16 := hc; clear hc
          have hrb_lt : rbit.toNat < 64 := by omega
          m6_split; rotate_left
          · clear hc; m6_steps; exact hJbrk (rbit, round, ()) ml
              ⟨by omega, sigL, scrL, hsigL, hscrL, hdwL, hconeL, htlL, hnvL, hml⟩
          clear hc
          m6_split; rotate_left
          · clear hc; m6_steps; exact hJbrk (rbit, round, ()) ml
              ⟨by omega, sigL, scrL, hsigL, hscrL, hdwL, hconeL, htlL, hnvL, hml⟩
          clear hc
          m6_split; rotate_left
          · clear hc; m6_steps; exact hJbrk (rbit, round, ()) ml
              ⟨by omega, sigL, scrL, hsigL, hscrL, hdwL, hconeL, htlL, hnvL, hml⟩
          clear hc
          refine m6_call_flip_round hFlipR hdwL.1 hLscr hLmv hKL hnvL hml
            fun ret scrF mF hlenF _ hKF hnvF htl_f _ _ _ hmF => ?_
          have hscrF : scrF.length = c.scratch_cap := hlenF.scratch_ok.scratch_buf_len
          have htlF : K6TailEq L ks0 (k6StateOfScratch L scrF) := k6TailEq_trans htlL htl_f
          m6_split; rotate_left
          · clear hc
            have hdwF : FullDenseInvW c F0 F_cur (mkSt sigL scrF) :=
              m6_fullDenseInvW_with_fuel_scr hinv0 hsigL hscrF
            have hconeF : M6SweepConeOk F_cur (mkSt sigL scrF) nv.toNat :=
              m6_coneOk_sim hcone0 hLscr hLmv hscr0 hscrF hKF
                (BitVec.eq_of_toNat_eq (by simp [hnvF]))
            m6_steps
            exact hJbrk (rbit, round, ()) mF
              ⟨by omega, sigL, scrF, hsigL, hscrF, hdwF, hconeF, htlF, hnvF, hmF⟩
          clear hc
          refine m6_call_refine_sig hRef hlenF hcap hnv_mv hnv_mx
            (fun j hj => hws0 j hj) hmF fun sigF mF' hsigF hmF' => ?_
          have hrb1 : (rbit + 1#32).toNat = rbit.toNat + 1 := m6_bv32_add1 (by omega)
          have hrd1 : (round + 1#32).toNat = round.toNat + 1 := m6_bv32_add1 (by omega)
          m6_steps
          exact hJl (rbit + 1#32, round + 1#32, ()) mF' (by dsimp only; rw [hrd1]; omega)
            ⟨by omega, by omega, sigF, scrF, hsigF, hscrF, hKF, hnvF, htlF, hmF'⟩))

theorem full_m6_sweep_sim_wp (Γ : Env)
    (hMaxV : Γ.Has "full_m6_max_v" m6MaxVSpec)
    (hSolve : Γ.Has "full_m6_sweep_solve" fullM6SweepSolveSpec)
    (hRef : Γ.Has "full_m6_sweep_refine_sig" fullM6SweepRefineSigSpec)
    (hFlipR : Γ.Has "full_m6_sweep_flip_round" fullM6SweepFlipRoundSpec) :
    ∀ args m Q X, fullM6SweepSimSpec args m Q X →
      Func.wp Γ full_m6_sweep_sim_body args m Q X := by
  rintro ⟨h, nv, tick_lim, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hinv, hcone, hhw_ex, hm, hQ⟩
  have ⟨hnv1, hnv_mv, hnv_cv, hws_lt, hK_scr, hge_s, hlt_s, hnv_eq⟩ := hcone
  obtain ⟨L, hL_len, hL_mv, hhwm0, hhw_ok⟩ := hhw_ex
  have hlen := hinv.1
  have hcv_le := hlen.core_ok.cur_vars_le
  have hws_len := hlen.scratch_ok.work_stk1_len
  have hsig_len := hlen.scratch_ok.sim_sig_len
  have hscr_len := hlen.scratch_ok.scratch_buf_len
  have hnv_mv_c : nv.toNat ≤ k6MaxV c.scratch_cap := hscr_len ▸ hnv_mv
  have hcap : k6MinScr ≤ c.scratch_cap := hscr_len ▸ hge_s
  have hnv_mx : nv.toNat ≤ 2 * c.max_vars := by omega
  let P := ConeModelSet F_cur s.scratch.work_stk1 nv.toNat
  have hmL := L.hmaxV
  let ks0 := k6StateOfScratch L s.scratch.scratch_buf
  have hK0 : K6Inv L P ks0 :=
    k6ScratchInv_to_inv (L := L) (hL_len.trans hscr_len.symm) (hscr_len ▸ hL_mv) hK_scr
  have hnv0_bv : ks0.nv = nv := by
    have hL_eq : L = k6LayoutOfCap s.scratch.scratch_buf.length hge_s hlt_s :=
      (k6LayoutOfCap_eq (hL_len.trans hscr_len.symm) (hscr_len ▸ hL_mv) hge_s hlt_s).symm
    change (k6StateOfScratch L s.scratch.scratch_buf).nv = nv
    rw [hL_eq, hnv_eq]; exact BitVec.eq_of_toNat_eq (by simp)
  have hmv_pos := m6_maxV_pos hL_mv
  have hmv_lt30 := m6_maxV_lt30 hL_mv
  have hmv_eq := m6_mv32_eq hL_mv
  have hkptr_c0 := m6_k6Ptr_eq hL_mv hmv_lt30
  have hnv_L : nv.toNat ≤ L.maxV := by rw [hL_mv, ← hscr_len]; exact hnv_mv
  have hmk_dense : ∀ (fuel' : BitVec 64) (sig' : List (BitVec 64)) (scr' : List (BitVec 32)),
      sig'.length = c.max_vars → scr'.length = c.scratch_cap →
      FullDenseInvW c F0 F_cur
        { s with core := { s.core with fuel := fuel' }
                 scratch := { s.scratch with sim_sig := sig', scratch_buf := scr' } } :=
    fun _ _ _ hsg hsc => m6_fullDenseInvW_with_fuel_scr hinv hsg hsc
  unfold Func.wp full_m6_sweep_sim_body
  m6_steps
  refine m6_call_max_v hMaxV (m6_scrCap_lt64 c) ?_
  m6_split
  · exfalso
    have h0 := congrArg BitVec.toNat hc
    rw [hmv_eq, k6_mv32_toNat] at h0; simp at h0; omega
  clear hc
  m6_split
  · exfalso
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc; omega
  clear hc
  m6_to_group
  refine wp_loop_inv (ts := [i32])
    (fun (i, ()) m1 => i.toNat ≤ nv.toNat ∧ ∃ sig1 : List (BitVec 64),
      sig1.length = c.max_vars ∧
      (FullMem c { s with scratch := { s.scratch with sim_sig := sig1 } } ⋆ R) m1)
    (fun (i, ()) _ => nv.toNat - i.toNat)
    (fun _ hJ0 => by
      m6_steps; exact hJ0 (0#32, ()) m ⟨Nat.zero_le _, s.scratch.sim_sig, hsig_len, hm⟩)
    (fun _ (i, ()) m1 ⟨hi_le, sig1, hsig1_len, hm1⟩ hJ0 => by
      m6_split
      · have hi_lt : i.toNat < nv.toNat := hc
        clear hc
        have hi1 : (i + 1#32).toNat = i.toNat + 1 := m6_bv32_add1 (by omega)
        have hi_ws : (i.setWidth 64).toNat < s.scratch.work_stk1.length := by
          rw [hws_len, bv_c0_zext32_64]; omega
        have hgv_sig : (BitVec.setWidth 64
            (s.scratch.work_stk1[(i.setWidth 64).toNat]'hi_ws)).toNat < sig1.length := by
          have hg := hws_lt i.toNat hi_lt
          rw [List.getElem?_eq_getElem (by rw [hws_len]; omega), Option.getD_some] at hg
          rw [hsig1_len, bv_c0_zext32_64]; simp only [bv_c0_zext32_64]; omega
        m6_steps
        exact hJ0 (i + 1#32, ()) _
          (by dsimp only; rw [hi1]; exact Nat.sub_lt_sub_left hi_lt (by omega))
          ⟨by omega, _, List.length_set.trans hsig1_len, by assumption⟩
      · clear hc
        let sS1 : FullState := { s with scratch := { s.scratch with sim_sig := sig1 } }
        have hscr_s1 : sS1.scratch.scratch_buf.length = c.scratch_cap := hscr_len
        have hK_s1 : K6Inv L P (k6StateOfScratch L sS1.scratch.scratch_buf) := hK0
        have hm_ka : (K6MemA L (L.kPtr c.pScratchBuf) ks0 ⋆ (FullK6Frame c L sS1 ⋆ R)) m1 :=
          m6_split_k6 (s := sS1) hL_len hscr_s1 hK_s1 hm1
        change wp _ _ _ _ _
        c0_hsteps_nogrp
        try dsimp only [Prod.fst]
        try rw [hkptr_c0]; try rw [hmv_eq]
        open scoped K6MemATactics K6PtrTactics in c0_hsteps!
        have hK_a0 := k6Inv_set_nassump0 hK0
        have htl_a0 : K6TailEq L ks0 (ks0.putHdr .nassump 0#32) :=
          k6TailEq_of_putHdr_ne_nv (f := .nassump) (by decide) 0#32
        obtain ⟨hscrA0, _, hofA0, hmA0⟩ :=
          m6_join_k6_ofSlab (s := sS1) hL_len hscr_s1 hK_a0.shapes
            (by simpa [show (0 : BitVec 32) = 0#32 from rfl] using
              (by assumption : (K6MemA L _ _ ⋆ (FullK6Frame c L sS1 ⋆ R)) _))
        let scrA0 := sS1.scratch.scratch_buf.take L.k6Base ++ (ks0.putHdr .nassump 0#32).toSlab
        let sA0 : FullState := { sS1 with scratch := { sS1.scratch with scratch_buf := scrA0 } }
        have hlenA0 : sA0.LengthsOk c :=
          ⟨hlen.core_ok, { hlen.scratch_ok with
            sim_sig_len := hsig1_len, scratch_buf_len := hscrA0 }⟩
        have hnv_a0 : (k6StateOfScratch L scrA0).nv = nv := by rw [hofA0]; exact hnv0_bv
        have hna_a0 : (k6StateOfScratch L scrA0).nassump = 0#32 := by rw [hofA0]; rfl
        refine m6_call_sweep_solve hSolve hlenA0 hL_len hL_mv (hofA0 ▸ hK_a0) hnv_a0 hmA0
          fun st0 fuel0 scr0 m0 hlen0 hfuel0 _ hK0s _ hnv0s htl_s hna0s _ _ hst0 huns0 hm0 => ?_
        have hscr0_len : scr0.length = c.scratch_cap := hlen0.scratch_ok.scratch_buf_len
        have htl0 : K6TailEq L ks0 (k6StateOfScratch L scr0) :=
          k6TailEq_trans htl_a0 (by rw [hofA0] at htl_s; exact htl_s)
        have hdw0 := hmk_dense fuel0 sig1 scr0 hsig1_len hscr0_len
        have hcone0 : M6SweepConeOk F_cur (m6SimSt s fuel0 sig1 scr0) nv.toNat :=
          m6_coneOk_sim hcone hL_len hL_mv hscr_len hscr0_len hK0s
            (BitVec.eq_of_toNat_eq (by simp [hnv0s]))
        have hhw0 := m6_coneHwm_sim hL_len hL_mv rfl hhwm0 htl0 hhw_ok (hnv0s.trans hnv0_bv.symm)
        m6_split
        · have hst_20 : st0 = 20#64 := hc
          clear hc
          m6_steps
          have huns : (cnfOfClauses F_cur).Unsat :=
            m6_unsat_empty_assump (hna0s.trans hna_a0) (huns0 hst_20)
          exact hQ 0xFFFFFFFF#32 fuel0 sig1 scr0 m0 hdw0 hfuel0 hcone0 hhw0
            (fun _ => huns) (fun hne => absurd rfl hne) hm0
        clear hc
        m6_split
        · clear hc; m6_steps
          exact hQ 0#32 fuel0 sig1 scr0 m0 hdw0 hfuel0 hcone0 hhw0
            (fun h => by cases h) (fun _ => by decide) hm0
        clear hc
        refine m6_call_refine_sig hRef hlen0 hcap hnv_mv_c hnv_mx
          (fun j hj => hws_lt j hj) hm0 fun sig3 m3 hsig3 hm3 => ?_
        let s3 := m6SimSt s fuel0 sig3 scr0
        have hdw3 := hmk_dense fuel0 sig3 scr0 hsig3 hscr0_len
        have hcone3 : M6SweepConeOk F_cur s3 nv.toNat :=
          m6_coneOk_sim hcone hL_len hL_mv hscr_len hscr0_len hK0s
            (BitVec.eq_of_toNat_eq (by simp [hnv0s]))
        m6_to_group
        change wp Γ Q X (m6SimLoopExpr c.hdr (L.kPtr c.pScratchBuf) nv tick_lim) m3
        refine m6_sim_loop_wp hRef hFlipR hdw3 hcone3 hL_len hL_mv hcap hnv_mv_c hnv_mx
          hK0s hnv0s htl0 hm3 fun rbit sigX scrX mx hdwX hconeX htlX hnvX hrff hrle hmx => ?_
        have hhwX := m6_coneHwm_sim hL_len hL_mv rfl hhwm0 htlX hhw_ok (hnvX.trans hnv0_bv.symm)
        exact hQ rbit fuel0 sigX scrX mx hdwX hfuel0 hconeX hhwX
          (fun hff => absurd hff hrff) (fun _ => hrle) hmx)

end LeanQbe.T.Examples.Kissat.Proof.Sweep

end
