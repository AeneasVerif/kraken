module

public import LeanQbe.T.Examples.Kissat.FullM6SweepProofCone

/-!
# Kissat `D-Full` M6 — Variable-Sweeping Phase & Simulation Proofs (`18..22/39`)

Parametric `(Γ : Env)` `Func.wp` proofs for `5/39` owned functions (`22/39` cumulative):
- `18/39`: `full_m6_sweep_refine_sig_wp`
- `19/39`: `full_m6_sweep_rand_phases_wp`
- `20/39`: `full_m6_sweep_solve_wp`
- `21/39`: `full_m6_sweep_flip_round_wp`
- `22/39`: `full_m6_sweep_sim_wp`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6Sweep

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full LeanQbe.T.Examples.Kissat.FullM4Sweep
open Kraken.Bedrock2.Test
open FullArenaTactics K6MemATactics K6PtrTactics
open scoped FullArenaTactics M6SweepTactics

/-! ## 1. Dynamic `K6` Memory & `K6Inv` / `ConeModelSet` Helpers -/

theorem m6_call_rng_next {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hRng : M6EnvSpec Γ "full_rng_next" fullRngNextSpec)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Tup Val [i64] → Expr Val Cont rs}
    (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ (r rng' : BitVec 64) (m' : Mem 64),
      let s' : FullState := { s with scratch := { s.scratch with rng_state := rng' } }
      s'.LengthsOk c → (FullMem c s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (Expr.call (as := [i64]) (bs := [i64]) "full_rng_next" (Arg.var c.hdr, ()) k) m := by
  refine wp_call_of_spec _ k ?_
  refine hRng (c.hdr, ()) m (fun r m' => wp Γ Q X (k r) m') X ⟨c, s, R, rfl, hlen, hm, ?_⟩
  rintro ⟨r, ⟨⟩⟩ st_r mr hcore_r hlen_r hscr_r hmr
  dsimp only [fullSafetySlice] at hcore_r hlen_r hmr
  generalize st_r.scratch.rng_state = rng' at hscr_r
  have hst_eq : ({ s with scratch :=
      { s.scratch with rng_state := rng' } } : FullState) = st_r := by
    cases st_r; exact congr (congrArg FullState.mk hcore_r.symm) hscr_r.symm
  exact hk r rng' mr (hst_eq ▸ hlen_r) (hst_eq ▸ hmr)

theorem m6_join_k6_ofSlab {c : FullCfg} {L : K6Layout} {s : FullState} {ks' : K6State}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hL : L.scrLen = c.scratch_cap) (hs : s.scratch.scratch_buf.length = c.scratch_cap)
    (hsh : ks'.ShapesOk L)
    (hm : (K6MemA L (L.kPtr c.pScratchBuf) ks' ⋆ (FullK6Frame c L s ⋆ R)) m) :
    let scr' := s.scratch.scratch_buf.take L.k6Base ++ ks'.toSlab
    let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
    scr'.length = c.scratch_cap ∧
    (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) ∧
    k6StateOfScratch L scr' = ks' ∧ (FullMem c s' ⋆ R) m := by
  intro scr' s'
  have hmL := L.hmaxV; have hac := L.hacap
  have hkb_le : L.k6Base ≤ s.scratch.scratch_buf.length := by
    rw [hs, ← hL]; unfold K6Layout.scrLen K6Layout.k6Base; omega
  have htk : (s.scratch.scratch_buf.take L.k6Base).length = L.k6Base :=
    List.length_take_of_le hkb_le
  have hsl : scr'.length = c.scratch_cap := by
    dsimp only [scr']
    rw [List.length_append, htk, ks'.toSlab_length hsh, ← hL]
    unfold K6Layout.scrLen; omega
  have hpre : ∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]? := fun i hi => by
    dsimp only [scr']
    rw [List.getElem?_append_left (by rw [htk]; exact hi), List.getElem?_take_of_lt hi]
  have hof : k6StateOfScratch L scr' = ks' := by
    unfold k6StateOfScratch; dsimp only [scr']
    rw [k6_slab_drop_exact _ _ htk]; exact K6State.ofSlab_toSlab hsh
  obtain ⟨_, hkm⟩ := k6MemA_to_mem hm
  exact ⟨hsl, hpre, hof, fullMem_join_k6 hkb_le hsh (sep_ac hkm)⟩

namespace FullK6DynMem
@[scoped c0_load] theorem load_m6_full_kvals {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < 2 * L.maxV) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 ((L.kPtr c.pScratchBuf + BitVec.ofNat 64 (4 * L.oVals)) +
        idx.setWidth 64 * 4) =
      some (s.scratch.scratch_buf[L.k6Base + L.oVals + idx.toNat]'(by
        have := L.hmaxV; have := L.hacap
        rw [hscr, ← hL]; unfold K6Layout.scrLen K6Layout.k6Fixed K6Layout.oVals; omega)) := by
  have hlt : idx.toNat < 2 ^ 28 := by have := L.hmaxV; omega
  have hptr : (L.kPtr c.pScratchBuf + BitVec.ofNat 64 (4 * L.oVals)) + idx.setWidth 64 * 4 =
      c.pScratchBuf + BitVec.ofNat 64 (4 * (L.k6Base + L.oVals + idx.toNat)) := by
    rw [show idx.setWidth 64 = BitVec.ofNat 64 idx.toNat from by apply BitVec.eq_of_toNat_eq; simp,
      k6_ptr_nat_mul4 _ idx.toNat hlt, K6Layout.kPtr, BitVec.add_assoc, BitVec.add_assoc,
      ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    congr 2; unfold K6Layout.k6Base K6Layout.oVals; omega
  rw [hptr]; exact load_full_scratch_buf _ hm

@[scoped c0_load] theorem load_m6_full_k6_hdr {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {idx : Nat}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hidx : idx < 32) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (L.kPtr c.pScratchBuf + BitVec.ofNat 64 idx * 4) =
      some (s.scratch.scratch_buf[L.k6Base + idx]'(by
        have := L.hmaxV; have := L.hacap
        rw [hscr, ← hL]; unfold K6Layout.scrLen K6Layout.k6Fixed; omega)) := by
  have hptr : L.kPtr c.pScratchBuf + BitVec.ofNat 64 idx * 4 =
      c.pScratchBuf + BitVec.ofNat 64 (4 * (L.k6Base + idx)) := by
    have := L.hmaxV
    rw [K6Layout.kPtr, k6_ptr_nat_mul4 _ idx (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; unfold K6Layout.k6Base; omega
  rw [hptr]; exact load_full_scratch_buf _ hm
end FullK6DynMem

private theorem m6_fl_bit0_and2 (fl b : BitVec 32) (h : (fl &&& 2#32) = 0#32) :
    (((fl &&& ~~~1#32) ||| (b &&& 1#32)) &&& 2#32) = 0#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  have hk0 := congrArg (·.getLsbD k) h
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
    BitVec.getLsbD_zero, hk, decide_true, Bool.true_and] at hk0 ⊢
  cases k with
  | zero => simp
  | succ k =>
    cases k with
    | zero => simpa using hk0
    | succ k =>
      have hf : Nat.testBit 2 (k + 2) = false :=
        Nat.testBit_lt_two_pow
          (by have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 2 ≤ k + 2); omega)
      simp [BitVec.getLsbD, hf]

theorem k6Inv_set_flags_bit0 {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    {i : Nat} (hi : i < L.maxV) (b : BitVec 32) (hinv : K6Inv L P ks) :
    let v := (ks.flags[i]?.getD 0#32 &&& ~~~1#32) ||| (b &&& 1#32)
    K6Inv L P (ks.putArr .flags i v) := by
  intro v
  have hcl := hinv.clauses
  refine ⟨hinv.shapes.putArr .flags i v,
    { acap_eq := hcl.acap_eq, max_v_eq := hcl.max_v_eq, max_orig_eq := hcl.max_orig_eq,
      max_cl_eq := hcl.max_cl_eq, nv_le := hcl.nv_le, nc_le := hcl.nc_le, alen_le := hcl.alen_le,
      nassump_le := hcl.nassump_le, nkl_le := hcl.nkl_le, nana_le := hcl.nana_le,
      cl_wf := hcl.cl_wf, cl_mono := hcl.cl_mono, incons_ok := hcl.incons_ok,
      assump_ok := hcl.assump_ok,
      flags_clean := fun u hu => by
        change (((ks.flags).set i v)[u]?.getD 0#32 &&& 2#32) = 0#32
        by_cases hui : u = i
        · subst hui
          rw [List.getElem?_set_self (by rw [hinv.shapes.flags_len]; exact hi), Option.getD_some]
          exact m6_fl_bit0_and2 _ _ (hcl.flags_clean u hu)
        · rw [List.getElem?_set_ne (Ne.symm hui)]; exact hcl.flags_clean u hu },
    by dsimp only [K6State.putArr]; exact hinv.watches,
    k6BaseAssignOk_cast hinv.assign (by k6_field) (by k6_field) (by k6_field) (by k6_field)
      (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field),
    by dsimp only [K6State.putArr]; exact hinv.reasons⟩

theorem k6Inv_set_phase {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (v : BitVec 32) (hinv : K6Inv L P ks) :
    K6Inv L P (ks.putHdr .phase v) :=
  ⟨hinv.shapes.putHdr .phase v,
   k6ClausesOk_cast hinv.clauses (by k6_field) (by k6_field) (by k6_field) (by k6_field)
     (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field)
     (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field),
   by dsimp only [K6State.putHdr]; exact hinv.watches,
   k6BaseAssignOk_cast hinv.assign (by k6_field) (by k6_field) (by k6_field) (by k6_field)
     (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field),
   by dsimp only [K6State.putHdr]; exact hinv.reasons⟩

theorem k6Inv_set_nassump0 {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) :
    K6Inv L P (ks.putHdr .nassump 0#32) :=
  have hcl := hinv.clauses
  ⟨hinv.shapes.putHdr .nassump 0#32,
   { acap_eq := hcl.acap_eq, max_v_eq := hcl.max_v_eq, max_orig_eq := hcl.max_orig_eq,
     max_cl_eq := hcl.max_cl_eq, nv_le := hcl.nv_le, nc_le := hcl.nc_le, alen_le := hcl.alen_le,
     nassump_le := by dsimp only [K6State.putHdr]; simp,
     nkl_le := hcl.nkl_le, nana_le := hcl.nana_le, cl_wf := hcl.cl_wf, cl_mono := hcl.cl_mono,
     incons_ok := hcl.incons_ok,
     assump_ok := fun i hi => by dsimp only [K6State.putHdr] at hi; simp at hi,
     flags_clean := hcl.flags_clean },
   by dsimp only [K6State.putHdr]; exact hinv.watches,
   k6BaseAssignOk_cast hinv.assign (by k6_field) (by k6_field) (by k6_field) (by k6_field)
     (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field),
   by dsimp only [K6State.putHdr]; exact hinv.reasons⟩

theorem m6_coneModelSet_unsat_of_empty {F_cur : List (List Nat)} {ws1 : List (BitVec 32)}
    {nv : Nat} (h : ∀ β, ¬ ConeModelSet F_cur ws1 nv β) : (cnfOfClauses F_cur).Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro α hα
  exact h (fun i => α (ws1[i]?.getD 0#32).toNat) ⟨α, hα, fun _ _ => rfl⟩

theorem m6_fullDenseInvW_with_fuel_rng_sig_scr {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {fuel' rng' : BitVec 64} {sig' : List (BitVec 64)} {scr' : List (BitVec 32)}
    (hsig : sig'.length = c.max_vars) (hscr : scr'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with fuel := fuel' }
        scratch :=
          { s.scratch with rng_state := rng', sim_sig := sig', scratch_buf := scr' } } := by
  let s' : FullState :=
    { s with
      core := { s.core with fuel := fuel' }
      scratch := { s.scratch with rng_state := rng', sim_sig := sig', scratch_buf := scr' } }
  have hlen' : s'.LengthsOk c :=
    ⟨{ h.1.core_ok with vals_len := h.1.core_ok.vals_len },
     { h.1.scratch_ok with sim_sig_len := hsig, scratch_buf_len := hscr }⟩
  have hw := h.2.1
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
  exact ⟨hlen', hw', h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem m6_fullDenseInvW_with_flags {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {flags' : List (BitVec 32)}
    (hfl : flags'.length = c.max_vars) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with flags := flags' } } := by
  let s' : FullState := { s with core := { s.core with flags := flags' } }
  have hw := h.2.1
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
  exact ⟨⟨{ h.1.core_ok with flags_len := hfl }, h.1.scratch_ok⟩, hw',
    h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-! ## 2. `full_m6_sweep_refine_sig_wp` (`18/39`) -/

theorem full_m6_sweep_refine_sig_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec) :
    ∀ args m Q X, m6SweepRefineSigSpec args m Q X →
      Func.wp Γ full_m6_sweep_refine_sig_body args m Q X := by
  rintro ⟨h, nv, bit_idx, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcap, hnv_mv, hnv_mx, hcone, hm, hQ⟩
  have hcv_le := hlen.core_ok.cur_vars_le
  have hws_len := hlen.scratch_ok.work_stk1_len
  have hscr_len := hlen.scratch_ok.scratch_buf_len
  have hsig_len := hlen.scratch_ok.sim_sig_len
  obtain ⟨L, hL_def⟩ : ∃ L : K6Layout, L = k6LayoutOfCap c.scratch_cap hcap c.hscr := ⟨_, rfl⟩
  have hL_len : L.scrLen = c.scratch_cap := by
    rw [hL_def]; exact k6LayoutOfCap_scrLen hcap c.hscr
  have hL_mv : L.maxV = k6MaxV c.scratch_cap := by rw [hL_def]; rfl
  have hmL := L.hmaxV
  have hmv64_lt : k6MaxV c.scratch_cap < 2 ^ 32 := by omega
  have hmv_eq : BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) = L.mv32 := by
    apply BitVec.eq_of_toNat_eq
    simp only [k6_mv32_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [← hL_mv]; omega
  have hkptr_c0 : c.pScratchBuf + BitVec.setWidth 64
      ((1280 : BitVec 32) + (BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) <<<
        (1 : Nat))) * 4 = L.kPtr c.pScratchBuf := by
    rw [hmv_eq]; exact k6_ptr_base_k6Base L c.pScratchBuf
  have hvals_c0 : L.kPtr c.pScratchBuf + BitVec.setWidth 64
      ((32 : BitVec 32) + (10 : BitVec 32) * L.mv32) * 4 =
      L.kPtr c.pScratchBuf + BitVec.ofNat 64 (4 * L.oVals) :=
    k6_ptr_vals L (L.kPtr c.pScratchBuf)
  clear hL_def
  unfold Func.wp full_m6_sweep_refine_sig_body
  m6_steps
  refine m6_call_max_v hMaxV (c := c) rfl ?_
  m6_split
  · exfalso
    have h0 := congrArg BitVec.toNat hc
    rw [hmv_eq, k6_mv32_toNat] at h0; simp at h0; omega
  m6_split
  · exfalso
    rw [← hL_mv, Nat.mod_eq_of_lt (by omega)] at hc; omega
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
        have h1 := m6_bv32_shl1_or_pol i 0#32 (by omega) (by decide)
        rw [BitVec.or_zero, show (0#32 : BitVec 32).toNat = 0 from rfl] at h1
        omega
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
        refine hJ (i + 1#32, ()) _ (by dsimp only; rw [hi1]; exact Nat.sub_lt_sub_left hi_lt (by
          omega))
          ⟨by omega, _, ?_, by assumption⟩
        simp [hsigL])

/-! ## 3. `full_m6_sweep_rand_phases_wp` (`19/39`) -/

theorem full_m6_sweep_rand_phases_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hRng : M6EnvSpec Γ "full_rng_next" fullRngNextSpec) :
    ∀ args m Q X, m6SweepRandPhasesSpec args m Q X →
      Func.wp Γ full_m6_sweep_rand_phases_body args m Q X := by
  rintro ⟨h, nv, ⟨⟩⟩ m Q X ⟨c, s, P, L, R, rfl, hlen, hL_len, hL_mv, hK0, hnv_eq, hm, hQ⟩
  have hscr_len := hlen.scratch_ok.scratch_buf_len
  have hmL := L.hmaxV
  have hnv_le : nv.toNat ≤ L.maxV := by rw [← hnv_eq]; exact hK0.clauses.nv_le
  have hmv64_lt : k6MaxV c.scratch_cap < 2 ^ 32 := by rw [← hL_mv]; omega
  have hmv_eq : BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) = L.mv32 := by
    apply BitVec.eq_of_toNat_eq
    simp only [k6_mv32_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [← hL_mv]; omega
  have hkptr_c0 : c.pScratchBuf + BitVec.setWidth 64
      ((1280 : BitVec 32) + (BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) <<<
        (1 : Nat))) * 4 = L.kPtr c.pScratchBuf := by
    rw [hmv_eq]; exact k6_ptr_base_k6Base L c.pScratchBuf
  have hfl_c0 : L.kPtr c.pScratchBuf + BitVec.setWidth 64
      ((32 : BitVec 32) + (6 : BitVec 32) * L.mv32) * 4 =
      L.kPtr c.pScratchBuf + BitVec.ofNat 64 (4 * L.oFlags) :=
    k6_ptr_flags L (L.kPtr c.pScratchBuf)
  unfold Func.wp full_m6_sweep_rand_phases_body
  m6_steps
  refine m6_call_max_v hMaxV (c := c) rfl ?_
  m6_split
  · exfalso
    have h0 := congrArg BitVec.toNat hc
    rw [hmv_eq, k6_mv32_toNat] at h0; simp at h0; omega
  m6_split
  · exfalso
    rw [← hL_mv, Nat.mod_eq_of_lt (by omega)] at hc; omega
  m6_steps
  refine m6_call_rng_next hRng hlen hm fun r0 rng0 m0 hlen0 hm0 => ?_
  m6_to_group
  refine wp_loop_inv (ts := [i64, i32])
    (fun (rbits, i, ()) ml => i.toNat ≤ nv.toNat ∧ ∃ rngL scrL,
      scrL.length = c.scratch_cap ∧
      (∀ j < L.k6Base, scrL[j]? = s.scratch.scratch_buf[j]?) ∧
      K6Inv L P (k6StateOfScratch L scrL) ∧ (k6StateOfScratch L scrL).nv = nv ∧
      (k6StateOfScratch L scrL).nassump = (k6StateOfScratch L s.scratch.scratch_buf).nassump ∧
      k6AssumpLitsS L scrL = k6AssumpLitsS L s.scratch.scratch_buf ∧
      (k6StateOfScratch L scrL).neq = (k6StateOfScratch L s.scratch.scratch_buf).neq ∧
      (FullMem c { s with scratch := { s.scratch with rng_state := rngL, scratch_buf := scrL } }
        ⋆ R) ml)
    (fun (_, i, ()) _ => nv.toNat - i.toNat)
    (fun _ hJ => by
      m6_steps
      exact hJ (r0, 0#32, ()) m0
        ⟨Nat.zero_le _, rng0, s.scratch.scratch_buf, hscr_len, fun _ _ => rfl, hK0, hnv_eq,
         rfl, rfl, rfl, hm0⟩)
    (fun _ (rbits, i, ()) ml
        ⟨hi_le, rngL, scrL, hslL, hpreL, hKL, hnvL, hnaL, hassL, hnqL, hml⟩ hJ => by
      let sL : FullState :=
        { s with scratch := { s.scratch with rng_state := rngL, scratch_buf := scrL } }
      have hlenL : sL.LengthsOk c :=
        ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hslL }⟩
      m6_split
      · have hi_lt : i.toNat < nv.toNat := hc
        have hi_mv : i.toNat < L.maxV := by omega
        have hi1 : (i + 1#32).toNat = i.toNat + 1 := m6_bv32_add1 (by omega)
        m6_to_group
        refine wp_join_group (ts := [i64])
          (fun (rb1, ()) m1 => ∃ rng1,
            (FullMem c { s with scratch :=
              { s.scratch with rng_state := rng1, scratch_buf := scrL } } ⋆ R) m1)
          (fun _ (rb1, ()) m1 ⟨rng1, hm1⟩ => by
            let s1 : FullState :=
              { s with scratch := { s.scratch with rng_state := rng1, scratch_buf := scrL } }
            have hslL_L : s1.scratch.scratch_buf.length = L.scrLen := by
              rw [hL_len]; exact hslL
            obtain ⟨Rfr, hRfr⟩ : ∃ Rfr : Mem 64 → Prop, Rfr = (FullK6Frame c L s1 ⋆ R) := ⟨_, rfl⟩
            have hm_ka : (K6MemA L (L.kPtr c.pScratchBuf) (k6StateOfScratch L scrL) ⋆ Rfr) m1 := by
              rw [fullMem_eq_k6Frame hslL_L] at hm1; rw [hRfr]
              exact k6Mem_to_amem hKL.shapes (sep_ac hm1)
            change wp _ _ _ _ _
            c0_hsteps
            dsimp only [Prod.fst]
            try rw [hkptr_c0]; try rw [hmv_eq]; try rw [hfl_c0]
            open scoped K6MemATactics K6PtrTactics in c0_hsteps!
            have hK1 := k6Inv_set_flags_bit0 (i := i.toNat) hi_mv (rb1.setWidth 32) hKL
            rw [hRfr] at hm
            have hscr_s1 : s1.scratch.scratch_buf.length = c.scratch_cap := hslL
            let v_fl : BitVec 32 := ((k6StateOfScratch L scrL).flags[i.toNat]?.getD 0#32 &&&
              ~~~1#32) ||| (rb1.setWidth 32 &&& 1#32)
            let scr2 := s1.scratch.scratch_buf.take L.k6Base ++
              ((k6StateOfScratch L scrL).putArr .flags i.toNat v_fl).toSlab
            obtain ⟨hsl1, hpre_s, hof1, hm_j⟩ :=
              m6_join_k6_ofSlab (s := s1) hL_len hscr_s1 hK1.shapes hm
            change scr2.length = c.scratch_cap at hsl1
            change k6StateOfScratch L scr2 = (k6StateOfScratch L scrL).putArr .flags i.toNat v_fl
              at hof1
            change (FullMem c { s with scratch :=
              { s.scratch with rng_state := rng1, scratch_buf := scr2 } } ⋆ R) _ at hm_j
            refine hJ (rb1 >>> 1#64, i + 1#32, ()) _
              (by dsimp only; rw [hi1]; exact Nat.sub_lt_sub_left hi_lt (by omega))
              ⟨by omega, rng1, scr2, hsl1, fun j hj => (hpre_s j hj).trans (hpreL j hj),
               ?_, ?_, ?_, ?_, ?_, hm_j⟩
            · rw [hof1]; exact hK1
            · rw [hof1]; exact hnvL
            · rw [hof1]; exact hnaL
            · unfold k6AssumpLitsS k6AssumpLits at hassL ⊢; rw [hof1]; exact hassL
            · rw [hof1]; exact hnqL)
          (fun _ hJrb => by
            m6_split
            · m6_split
              · refine m6_call_rng_next hRng hlenL hml fun rb1 rng1 m1 _ hm1 => ?_
                m6_steps; exact hJrb (rb1, ()) m1 ⟨rng1, hm1⟩
              · m6_steps; exact hJrb (rbits, ()) ml ⟨rngL, hml⟩
            · m6_steps; exact hJrb (rbits, ()) ml ⟨rngL, hml⟩)
      · have hslL_L : sL.scratch.scratch_buf.length = L.scrLen := by rw [hL_len]; exact hslL
        obtain ⟨Rfr, hRfr⟩ : ∃ Rfr : Mem 64 → Prop, Rfr = (FullK6Frame c L sL ⋆ R) := ⟨_, rfl⟩
        have hm_ka : (K6MemA L (L.kPtr c.pScratchBuf) (k6StateOfScratch L scrL) ⋆ Rfr) ml := by
          rw [fullMem_eq_k6Frame hslL_L] at hml; rw [hRfr]
          exact k6Mem_to_amem hKL.shapes (sep_ac hml)
        change wp _ _ _ _ _
        c0_hsteps
        dsimp only [Prod.fst]
        try rw [hkptr_c0]
        open scoped K6MemATactics K6PtrTactics in c0_hsteps!
        let v19 : BitVec 32 := (k6StateOfScratch L scrL).phase ^^^ 1#32
        have hK1 := k6Inv_set_phase v19 hKL
        rw [hRfr] at hm
        have hscr_sL : sL.scratch.scratch_buf.length = c.scratch_cap := hslL
        let scr2 := sL.scratch.scratch_buf.take L.k6Base ++
          ((k6StateOfScratch L scrL).putHdr .phase v19).toSlab
        obtain ⟨hsl1, hpre_s, hof1, hm_j⟩ :=
          m6_join_k6_ofSlab (s := sL) hL_len hscr_sL hK1.shapes hm
        change scr2.length = c.scratch_cap at hsl1
        change k6StateOfScratch L scr2 = (k6StateOfScratch L scrL).putHdr .phase v19 at hof1
        change (FullMem c { s with scratch :=
          { s.scratch with rng_state := rngL, scratch_buf := scr2 } } ⋆ R) _ at hm_j
        refine hQ rngL scr2 _
          ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hsl1 }⟩
          (fun j hj => (hpre_s j hj).trans (hpreL j hj))
          ?_ ?_ ?_ ?_ ?_ hm_j
        · rw [hof1]; exact hK1
        · rw [hof1]; exact hnvL
        · rw [hof1]; exact hnaL
        · unfold k6AssumpLitsS k6AssumpLits at hassL ⊢; rw [hof1]; exact hassL
        · rw [hof1]; exact hnqL)

/-! ## 4. `full_m6_sweep_solve_wp` (`20/39`) -/

theorem full_m6_sweep_solve_wp (Γ : Env)
    (hRand : M6EnvSpec Γ "full_m6_sweep_rand_phases" m6SweepRandPhasesSpec)
    (hSolve : M6EnvSpec Γ "full_k6_solve" k6SolveSpec) :
    ∀ args m Q X, m6SweepSolveSpec args m Q X →
      Func.wp Γ full_m6_sweep_solve_body args m Q X := by
  rintro ⟨h, nv, tick_lim, ⟨⟩⟩ m Q X ⟨c, s, P, L, R, rfl, hlen, hL_len, hL_mv, hK0, hnv0, hm, hQ⟩
  unfold Func.wp full_m6_sweep_solve_body
  m6_call hRand
  refine ⟨c, s, P, L, R, rfl, hlen, hL_len, hL_mv, hK0, hnv0, hm,
    fun rng1 scr1 m1 hlen1 hpre1 hK1 hnv1 hna1 hass1 hnq1 hm1 => ?_⟩
  m6_steps
  m6_call hSolve
  refine ⟨c, _, P, L, R, rfl, hlen1, hL_len, hL_mv, hK1, hm1,
    fun r fuel2 scr2 m2 hlen2 hfuel2 hpre2 hK2 _ hnv2 hna2 hass2 hnq2 hr huns hm2 => ?_⟩
  m6_steps
  exact hQ r fuel2 rng1 scr2 m2 hlen2 hfuel2
    (fun i hi => (hpre2 i hi).trans (hpre1 i hi))
    hK2 (by assumption) (hnv2.trans hnv1) (hna2.trans hna1) (hass2.trans hass1)
    (hnq2.trans hnq1) hr huns hm2

/-! ## 5. `full_m6_sweep_flip_round_wp` (`21/39`) -/

theorem full_m6_sweep_flip_round_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hRng : M6EnvSpec Γ "full_rng_next" fullRngNextSpec)
    (hFlip : M6EnvSpec Γ "full_k6_flip" k6FlipSpec) :
    ∀ args m Q X, m6SweepFlipRoundSpec args m Q X →
      Func.wp Γ full_m6_sweep_flip_round_body args m Q X := by
  rintro ⟨h, nv, ⟨⟩⟩ m Q X ⟨c, s, P, L, R, rfl, hlen, hL_len, hL_mv, hK0, hnv_eq, hm, hQ⟩
  have hscr_len := hlen.scratch_ok.scratch_buf_len
  have hmL := L.hmaxV
  have hnv_le : nv.toNat ≤ L.maxV := by rw [← hnv_eq]; exact hK0.clauses.nv_le
  have hmv64_lt : k6MaxV c.scratch_cap < 2 ^ 32 := by rw [← hL_mv]; omega
  have hmv_eq : BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) = L.mv32 := by
    apply BitVec.eq_of_toNat_eq
    simp only [k6_mv32_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [← hL_mv]; omega
  have hkptr_c0 : c.pScratchBuf + BitVec.setWidth 64
      ((1280 : BitVec 32) + (BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) <<<
        (1 : Nat))) * 4 = L.kPtr c.pScratchBuf := by
    rw [hmv_eq]; exact k6_ptr_base_k6Base L c.pScratchBuf
  have hvals_c0 : L.kPtr c.pScratchBuf + BitVec.setWidth 64
      ((32 : BitVec 32) + (10 : BitVec 32) * L.mv32) * 4 =
      L.kPtr c.pScratchBuf + BitVec.ofNat 64 (4 * L.oVals) :=
    k6_ptr_vals L (L.kPtr c.pScratchBuf)
  unfold Func.wp full_m6_sweep_flip_round_body
  m6_steps
  m6_split
  · m6_steps
    exact hQ 0#32 s.scratch.rng_state s.scratch.scratch_buf m hlen (fun _ _ => rfl) hK0 hnv_eq
      rfl rfl rfl hm
  have hnv_pos : 0 < nv.toNat := by bv_omega
  have hnv64_nz : nv.setWidth 64 ≠ 0#64 := by
    intro h0; have := congrArg BitVec.toNat h0; simp at this; omega
  m6_steps
  refine m6_call_max_v hMaxV (c := c) rfl ?_
  m6_split
  · exfalso
    have h0 := congrArg BitVec.toNat hc
    rw [hmv_eq, k6_mv32_toNat] at h0; simp at h0; omega
  m6_split
  · exfalso
    rw [← hL_mv, Nat.mod_eq_of_lt (by omega)] at hc; omega
  m6_steps
  refine m6_call_rng_next hRng hlen hm fun r0 rng0 m0 hlen0 hm0 => ?_
  m6_steps
  refine m6_call_rng_next hRng hlen0 hm0 fun rb0 rng1 m1 hlen1 hm1 => ?_
  let start : BitVec 32 := (r0 % nv.setWidth 64).setWidth 32
  have hstart_lt : start.toNat < nv.toNat := by
    have hrem : (r0 % nv.setWidth 64).toNat < nv.toNat := by
      rw [BitVec.toNat_umod, bv_c0_zext32_64]; exact Nat.mod_lt _ hnv_pos
    dsimp only [start]; rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact hrem
  m6_to_group
  refine wp_loop_inv (ts := [i64, i32, i32])
    (fun (rbits, flipped, step, ()) ml => step.toNat ≤ nv.toNat ∧ ∃ rngL scrL,
      scrL.length = c.scratch_cap ∧
      (∀ j < L.k6Base, scrL[j]? = s.scratch.scratch_buf[j]?) ∧
      K6Inv L P (k6StateOfScratch L scrL) ∧ (k6StateOfScratch L scrL).nv = nv ∧
      (k6StateOfScratch L scrL).nassump = (k6StateOfScratch L s.scratch.scratch_buf).nassump ∧
      k6AssumpLitsS L scrL = k6AssumpLitsS L s.scratch.scratch_buf ∧
      (k6StateOfScratch L scrL).neq = (k6StateOfScratch L s.scratch.scratch_buf).neq ∧
      (FullMem c { s with scratch := { s.scratch with rng_state := rngL, scratch_buf := scrL } }
        ⋆ R) ml)
    (fun (_, _, step, ()) _ => nv.toNat - step.toNat)
    (fun _ hJ => by
      m6_steps
      exact hJ (rb0, 0#32, 0#32, ()) m1
        ⟨Nat.zero_le _, rng1, s.scratch.scratch_buf, hscr_len, fun _ _ => rfl, hK0, hnv_eq,
         rfl, rfl, rfl, hm1⟩)
    (fun _ (rbits, flipped, step, ()) ml
        ⟨hs_le, rngL, scrL, hslL, hpreL, hKL, hnvL, hnaL, hassL, hnqL, hml⟩ hJ => by
      let sL : FullState :=
        { s with scratch := { s.scratch with rng_state := rngL, scratch_buf := scrL } }
      have hlenL : sL.LengthsOk c :=
        ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hslL }⟩
      m6_split
      · have hs_lt : step.toNat < nv.toNat := hc
        have hs1 : (step + 1#32).toNat = step.toNat + 1 := m6_bv32_add1 (by omega)
        m6_to_group
        refine wp_join_group (ts := [i64])
          (fun (rb1, ()) m_rb => ∃ rng1,
            (FullMem c { s with scratch :=
              { s.scratch with rng_state := rng1, scratch_buf := scrL } } ⋆ R) m_rb)
          (fun _ (rb1, ()) m_rb ⟨rng1, hm_rb⟩ => by
            m6_to_group
            refine wp_join_group (ts := [i32])
              (fun (fl2, ()) m2 => ∃ scr2,
                scr2.length = c.scratch_cap ∧
                (∀ j < L.k6Base, scr2[j]? = s.scratch.scratch_buf[j]?) ∧
                K6Inv L P (k6StateOfScratch L scr2) ∧ (k6StateOfScratch L scr2).nv = nv ∧
                (k6StateOfScratch L scr2).nassump =
                  (k6StateOfScratch L s.scratch.scratch_buf).nassump ∧
                k6AssumpLitsS L scr2 = k6AssumpLitsS L s.scratch.scratch_buf ∧
                (k6StateOfScratch L scr2).neq =
                  (k6StateOfScratch L s.scratch.scratch_buf).neq ∧
                (FullMem c { s with scratch :=
                  { s.scratch with rng_state := rng1, scratch_buf := scr2 } } ⋆ R) m2)
              (fun _ (fl2, ()) m2 ⟨scr2, hsl2, hpre2, hK2, hnv2, hna2, hass2, hnq2, hm2⟩ => by
                m6_steps
                exact hJ (rb1 >>> 1#64, fl2, step + 1#32, ()) m2
                  (by dsimp only; rw [hs1]; exact Nat.sub_lt_sub_left hs_lt (by omega))
                  ⟨by omega, rng1, scr2, hsl2, hpre2, hK2, hnv2, hna2, hass2, hnq2, hm2⟩)
              (fun _ hJfl => by
                m6_split; rotate_left
                · m6_steps
                  exact hJfl (flipped, ()) m_rb ⟨scrL, hslL, hpreL, hKL, hnvL, hnaL, hassL, hnqL,
                    hm_rb⟩
                m6_to_group
                refine wp_join_group (ts := [i32])
                  (fun (v, ()) mv_ => mv_ = m_rb ∧ v.toNat < nv.toNat)
                  (fun _ (v, ()) mv_ ⟨hmv_, hv_lt⟩ => by
                    subst mv_
                    have hv_2v : (v <<< (1 : Nat)).toNat < 2 * L.maxV := by
                      have h1 := m6_bv32_shl1_or_pol v 0#32 (by omega) (by decide)
                      rw [BitVec.or_zero, show (0#32 : BitVec 32).toNat = 0 from rfl] at h1
                      omega
                    m6_to_group
                    refine wp_join_group (ts := [i32])
                      (fun (lit, ()) mlit => mlit = m_rb ∧ lit.toNat < 2 * nv.toNat)
                      (fun _ (lit, ()) mlit ⟨hmlit, hlit_lt⟩ => by
                        subst hmlit
                        let s1 : FullState :=
                          { s with scratch :=
                            { s.scratch with rng_state := rng1, scratch_buf := scrL } }
                        have hlen1' : s1.LengthsOk c :=
                          ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hslL }⟩
                        m6_to_group; refine wp_unroll_group fun _ _ => ?_
                        m6_call hFlip
                        refine ⟨c, s1, P, L, R, rfl, hlen1', hL_len, hL_mv, hKL,
                          by rw [hnvL]; exact hlit_lt, hm_rb,
                          fun ok scr2 m2 hlen2 hpre_f hK2 hnv2 hna2 hass2 hnq2 hm2 => ?_⟩
                        have hpre2 : ∀ j < L.k6Base, scr2[j]? = s.scratch.scratch_buf[j]? :=
                          fun j hj => (hpre_f j hj).trans (hpreL j hj)
                        m6_split
                        · m6_steps
                          exact hJfl (flipped + 1#32, ()) m2
                            ⟨scr2, hlen2.scratch_ok.scratch_buf_len, hpre2, hK2, hnv2.trans hnvL,
                             hna2.trans hnaL, hass2.trans hassL, hnq2.trans hnqL, hm2⟩
                        · m6_steps
                          exact hJfl (flipped, ()) m2
                            ⟨scr2, hlen2.scratch_ok.scratch_buf_len, hpre2, hK2, hnv2.trans hnvL,
                             hna2.trans hnaL, hass2.trans hassL, hnq2.trans hnqL, hm2⟩)
                      (fun _ hJlit => by
                        change wp _ _ _ _ _
                        c0_hsteps_nogrp
                        dsimp only [Prod.fst]
                        try rw [hkptr_c0]; try rw [hmv_eq]; try rw [hvals_c0]
                        open scoped FullK6DynMem in m6_split
                        · m6_steps; exact hJlit (v <<< (1 : Nat), ()) m_rb ⟨rfl, by bv_omega⟩
                        · m6_steps
                          refine hJlit ((v <<< (1 : Nat)) ||| 1#32, ()) m_rb ⟨rfl, ?_⟩
                          rw [m6_bv32_shl1_or_pol v 1#32 (by omega) (by decide)]
                          simp; omega))
                  (fun _ hJv => by
                    m6_split
                    · m6_steps; exact hJv (start + step - nv, ()) m_rb
                        ⟨rfl, by dsimp only [start] at hstart_lt ⊢; bv_omega⟩
                    · m6_steps; exact hJv (start + step, ()) m_rb
                        ⟨rfl, by dsimp only [start] at hstart_lt ⊢; bv_omega⟩)))
          (fun _ hJrb => by
            m6_split
            · m6_split
              · refine m6_call_rng_next hRng hlenL hml fun rb1 rng1 m1 _ hm1 => ?_
                m6_steps; exact hJrb (rb1, ()) m1 ⟨rng1, hm1⟩
              · m6_steps; exact hJrb (rbits, ()) ml ⟨rngL, hml⟩
            · m6_steps; exact hJrb (rbits, ()) ml ⟨rngL, hml⟩)
      · m6_steps; exact hQ flipped rngL scrL ml hlenL hpreL hKL hnvL hnaL hassL hnqL hml)

/-! ## 6. `full_m6_sweep_sim_wp` (`22/39`) -/

theorem full_m6_sweep_sim_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hSolve : M6EnvSpec Γ "full_m6_sweep_solve" m6SweepSolveSpec)
    (hRef : M6EnvSpec Γ "full_m6_sweep_refine_sig" m6SweepRefineSigSpec)
    (hFlipR : M6EnvSpec Γ "full_m6_sweep_flip_round" m6SweepFlipRoundSpec) :
    ∀ args m Q X, m6SweepSimSpec args m Q X →
      Func.wp Γ full_m6_sweep_sim_body args m Q X := by
  rintro ⟨h, nv, tick_lim, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hinv, hcone, hm, hQ⟩
  obtain ⟨hnv1, hnv_mv, hnv_cv, hws_lt, hK_scr, hge_s, hlt_s, hnv_eq⟩ := hcone
  have hlen := hinv.1
  have hcv_le := hlen.core_ok.cur_vars_le
  have hws_len := hlen.scratch_ok.work_stk1_len
  have hsig_len := hlen.scratch_ok.sim_sig_len
  have hscr_len := hlen.scratch_ok.scratch_buf_len
  have hcap : k6MinScr ≤ c.scratch_cap := hscr_len ▸ hge_s
  have hnv_mx : nv.toNat ≤ 2 * c.max_vars := by omega
  let P := ConeModelSet F_cur s.scratch.work_stk1 nv.toNat
  obtain ⟨L, hL_def⟩ : ∃ L : K6Layout, L = k6LayoutOfCap c.scratch_cap hcap c.hscr := ⟨_, rfl⟩
  have hL_len : L.scrLen = c.scratch_cap := by
    rw [hL_def]; exact k6LayoutOfCap_scrLen hcap c.hscr
  have hL_mv : L.maxV = k6MaxV c.scratch_cap := by rw [hL_def]; rfl
  have hmL := L.hmaxV
  have hK0 : K6Inv L P (k6StateOfScratch L s.scratch.scratch_buf) := by
    have h1 := k6ScratchInv_to_inv (L := L) (hL_len.trans hscr_len.symm)
      (by rw [hscr_len]; exact hL_mv) hK_scr
    exact h1
  have hnv0_bv : (k6StateOfScratch L s.scratch.scratch_buf).nv = nv := by
    have hL_eq : L = k6LayoutOfCap s.scratch.scratch_buf.length hge_s hlt_s :=
      (k6LayoutOfCap_eq (hL_len.trans hscr_len.symm)
        (by rw [hscr_len]; exact hL_mv) hge_s hlt_s).symm
    rw [hL_eq, hnv_eq]; exact BitVec.eq_of_toNat_eq (by simp)
  have hmv64_lt : k6MaxV c.scratch_cap < 2 ^ 32 := by rw [← hL_mv]; omega
  have hmv_eq : BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) = L.mv32 := by
    apply BitVec.eq_of_toNat_eq
    simp only [k6_mv32_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [← hL_mv]; omega
  have hkptr_c0 : c.pScratchBuf + BitVec.setWidth 64
      ((1280 : BitVec 32) + (BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) <<<
        (1 : Nat))) * 4 = L.kPtr c.pScratchBuf := by
    rw [hmv_eq]; exact k6_ptr_base_k6Base L c.pScratchBuf
  have hmk_dense : ∀ (fuel' rng' : BitVec 64) (sig' : List (BitVec 64)) (scr' : List (BitVec 32)),
      sig'.length = c.max_vars → scr'.length = c.scratch_cap →
      FullDenseInvW c F0 F_cur
        { s with
          core := { s.core with fuel := fuel' }
          scratch := { s.scratch with rng_state := rng', sim_sig := sig', scratch_buf := scr' } }
      := fun _ _ _ _ hsg hsc =>
    m6_fullDenseInvW_with_fuel_rng_sig_scr hinv hsg hsc
  have hmk_cone : ∀ (fuel' rng' : BitVec 64) (sig' : List (BitVec 64)) (scr' : List (BitVec 32)),
      scr'.length = c.scratch_cap → K6Inv L P (k6StateOfScratch L scr') →
      (k6StateOfScratch L scr').nv = nv →
      M6SweepConeOk F_cur
        { s with
          core := { s.core with fuel := fuel' }
          scratch := { s.scratch with rng_state := rng', sim_sig := sig', scratch_buf := scr' } }
        nv.toNat := fun _ _ _ scr' hsc hK' hnv' => by
    have hsc_ge : k6MinScr ≤ scr'.length := hsc ▸ hcap
    have hsc_lt : scr'.length < dimacsBound := hsc ▸ c.hscr
    have hL_can : L = k6LayoutOfCap scr'.length hsc_ge hsc_lt :=
      (k6LayoutOfCap_eq (hL_len.trans hsc.symm) (by rw [hsc]; exact hL_mv) hsc_ge hsc_lt).symm
    refine ⟨hnv1, by rw [hsc, ← hscr_len]; exact hnv_mv, hnv_cv, hws_lt,
      K6Inv.to_scratchInv (hL_len ▸ hsc) (hsc ▸ hL_mv) hsc_ge hsc_lt hK',
      ⟨hsc_ge, hsc_lt, by rw [← hL_can, hnv']; exact BitVec.eq_of_toNat_eq (by simp)⟩⟩
  have hnv_L : nv.toNat ≤ L.maxV := by rw [hL_mv, ← hscr_len]; exact hnv_mv
  clear hL_def
  unfold Func.wp full_m6_sweep_sim_body
  m6_steps
  refine m6_call_max_v hMaxV (c := c) rfl ?_
  m6_split
  · exfalso
    have h0 := congrArg BitVec.toNat hc
    rw [hmv_eq, k6_mv32_toNat] at h0; simp at h0; omega
  m6_split
  · exfalso
    rw [← hL_mv, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc
    omega
  m6_to_group
  -- Loop 1: zero `sig[cone_v[i]] = 0ULL` for `i < nv`
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
      · -- Initial unconditional solve (`k[K6H_NASSUMP] = 0u; st0 = full_m6_sweep_solve(...)`)
        let sS1 : FullState := { s with scratch := { s.scratch with sim_sig := sig1 } }
        have hsl_S1 : sS1.scratch.scratch_buf.length = L.scrLen := by
          dsimp only [sS1]; rw [hL_len]; exact hscr_len
        obtain ⟨Rfr, hRfr⟩ : ∃ Rfr : Mem 64 → Prop, Rfr = (FullK6Frame c L sS1 ⋆ R) := ⟨_, rfl⟩
        have hm_ka : (K6MemA L (L.kPtr c.pScratchBuf)
            (k6StateOfScratch L s.scratch.scratch_buf) ⋆ Rfr) m1 := by
          change (FullMem c sS1 ⋆ R) m1 at hm1
          rw [fullMem_eq_k6Frame hsl_S1] at hm1; rw [hRfr]
          exact k6Mem_to_amem hK0.shapes (sep_ac hm1)
        change wp _ _ _ _ _
        c0_hsteps
        dsimp only [Prod.fst]
        try rw [hkptr_c0]
        open scoped K6MemATactics K6PtrTactics in c0_hsteps!
        have hK_a0 := k6Inv_set_nassump0 hK0
        rw [hRfr, show (0 : BitVec 32) = 0#32 from rfl] at hm
        have hscr_S1 : sS1.scratch.scratch_buf.length = c.scratch_cap := hscr_len
        let scrA0 := sS1.scratch.scratch_buf.take L.k6Base ++
          ((k6StateOfScratch L s.scratch.scratch_buf).putHdr .nassump 0#32).toSlab
        let sA0 : FullState := { sS1 with scratch := { sS1.scratch with scratch_buf := scrA0 } }
        obtain ⟨hscrA0, _hpreA0, hofA0, hmA0⟩ :=
          m6_join_k6_ofSlab (s := sS1) hL_len hscr_S1 hK_a0.shapes hm
        change scrA0.length = c.scratch_cap at hscrA0
        change k6StateOfScratch L scrA0 =
          (k6StateOfScratch L s.scratch.scratch_buf).putHdr .nassump 0#32 at hofA0
        change (FullMem c sA0 ⋆ R) _ at hmA0
        have hlenA0 : sA0.LengthsOk c :=
          ⟨hlen.core_ok, { hlen.scratch_ok with
            sim_sig_len := hsig1_len, scratch_buf_len := hscrA0 }⟩
        have hnv_a0 : (k6StateOfScratch L scrA0).nv = nv := by rw [hofA0]; exact hnv0_bv
        have hass_a0 : k6AssumpLitsS L scrA0 = [] := by
          unfold k6AssumpLitsS k6AssumpLits; rw [hofA0]; simp [K6State.putHdr]
        m6_call hSolve
        refine ⟨c, sA0, P, L, R, rfl, hlenA0, hL_len, hL_mv, hofA0 ▸ hK_a0, hnv_a0, hmA0,
          fun st0 fuel0 rng0 scr0 m0 hlen0 hfuel0 _ hK_s0 _ hnv_s0 _ hass_s0 _ hst0 huns0 hm0
            => ?_⟩
        have hscr0_len := hlen0.scratch_ok.scratch_buf_len
        m6_split
        · have hst20 : st0 = 20#64 := hc
          have huns_cur : (cnfOfClauses F_cur).Unsat := by
            apply m6_coneModelSet_unsat_of_empty (ws1 := s.scratch.work_stk1) (nv := nv.toNat)
            intro β hβ
            have hna := huns0 hst20 β hβ
            rw [hass_s0, hass_a0] at hna
            exact hna (by simp [unitsCnf])
          m6_steps
          exact hQ 0xFFFFFFFF#32 fuel0 rng0 sig1 scr0 m0
            (hmk_dense fuel0 rng0 sig1 scr0 hsig1_len hscr0_len)
            hfuel0 (hmk_cone fuel0 rng0 sig1 scr0 hscr0_len hK_s0 hnv_s0) (fun _ => huns_cur)
            (fun h => absurd rfl h) hm0
        m6_split
        · m6_steps
          exact hQ 0#32 fuel0 rng0 sig1 scr0 m0
            (hmk_dense fuel0 rng0 sig1 scr0 hsig1_len hscr0_len)
            hfuel0 (hmk_cone fuel0 rng0 sig1 scr0 hscr0_len hK_s0 hnv_s0) (fun h => by cases h)
            (fun _ => by decide) hm0
        -- Refine bit 0, compute `sim_lim`, and enter round loop
        m6_call hRef
        refine ⟨c, _, R, rfl, hlen0, hcap, by rw [← hL_mv]; exact hnv_L, hnv_mx,
          hws_lt, hm0, fun sig2 m2 hsig2_len hm2 => ?_⟩
        m6_to_group
        refine wp_join_group (ts := [i64])
          (fun (_sim_lim, ()) msl => msl = m2)
          (fun _ (sim_lim, ()) msl hmsl => by
            subst msl
            m6_to_group
            refine wp_join_group (ts := [i32, i32])
              (fun (rbitB, _roundB, ()) mB => rbitB.toNat ≤ 64 ∧
                ∃ fuelB rngB sigB scrB,
                  fuelB.toNat ≤ s.core.fuel.toNat ∧ sigB.length = c.max_vars ∧
                  scrB.length = c.scratch_cap ∧ K6Inv L P (k6StateOfScratch L scrB) ∧
                  (k6StateOfScratch L scrB).nv = nv ∧
                  (FullMem c { s with
                    core := { s.core with fuel := fuelB }
                    scratch := { s.scratch with rng_state := rngB, sim_sig := sigB,
                                                scratch_buf := scrB } } ⋆ R) mB)
              (fun _ (rbitB, _, ()) mB ⟨hr_le, fuelB, rngB, sigB, scrB, hflB, hsgB, hscB, hKB,
                  hnvB, hmB⟩ => by
                m6_steps
                exact hQ rbitB fuelB rngB sigB scrB mB (hmk_dense fuelB rngB sigB scrB hsgB hscB)
                  hflB (hmk_cone fuelB rngB sigB scrB hscB hKB hnvB)
                  (fun h => by rw [h] at hr_le; exfalso; revert hr_le; decide)
                  (fun _ => hr_le) hmB)
              (fun _ hJbrk => by
                refine wp_loop_inv (ts := [i32, i32])
                  (fun (rbit, round, ()) ml => round.toNat ≤ 4 ∧ rbit.toNat ≤ 64 ∧
                    ∃ fuelL rngL sigL scrL,
                      fuelL.toNat ≤ s.core.fuel.toNat ∧ sigL.length = c.max_vars ∧
                      scrL.length = c.scratch_cap ∧ K6Inv L P (k6StateOfScratch L scrL) ∧
                      (k6StateOfScratch L scrL).nv = nv ∧
                      (FullMem c { s with
                        core := { s.core with fuel := fuelL }
                        scratch := { s.scratch with rng_state := rngL, sim_sig := sigL,
                                                    scratch_buf := scrL } } ⋆ R) ml)
                  (fun (_, round, ()) _ => 4 - round.toNat)
                  (fun _ hJrd => by
                    m6_steps
                    exact hJrd (1#32, 0#32, ()) m2
                      ⟨Nat.zero_le _, by decide, fuel0, rng0, sig2, scr0, hfuel0, hsig2_len,
                       hscr0_len, hK_s0, hnv_s0, hm2⟩)
                  (fun _ (rbit, round, ()) ml
                      ⟨hrd_le, hrb_le, fuelL, rngL, sigL, scrL, hflL, hsgL, hscL, hKL, hnvL,
                        hml⟩ hJrd => by
                    have hbrkL := hJbrk (rbit, round, ()) ml
                      ⟨hrb_le, fuelL, rngL, sigL, scrL, hflL, hsgL, hscL, hKL, hnvL, hml⟩
                    m6_split; rotate_left; · m6_steps; exact hbrkL
                    m6_split; rotate_left; · m6_steps; exact hbrkL
                    m6_split; rotate_left; · m6_steps; exact hbrkL
                    have hrd_lt : round.toNat < 4 := ‹_›
                    have hrd1 : (round + 1#32).toNat = round.toNat + 1 := m6_bv32_add1 (by omega)
                    -- Inner flip loop: `while (fr < 3u && rbit < 64u)`
                    m6_to_group
                    refine wp_join_group (ts := [i32, i32])
                      (fun (rbitF, _frF, ()) mF => rbitF.toNat ≤ 64 ∧
                        ∃ rngF sigF scrF,
                          sigF.length = c.max_vars ∧ scrF.length = c.scratch_cap ∧
                          K6Inv L P (k6StateOfScratch L scrF) ∧ (k6StateOfScratch L scrF).nv = nv ∧
                          (FullMem c { s with
                            core := { s.core with fuel := fuelL }
                            scratch := { s.scratch with rng_state := rngF, sim_sig := sigF,
                                                        scratch_buf := scrF } } ⋆ R) mF)
                      (fun _ (rbitF, _, ()) mF
                          ⟨hrbF_le, rngF, sigF, scrF, hsgF, hscF, hKF, hnvF, hmF⟩ => by
                        have hnext := hJrd (rbitF, round + 1#32, ()) mF
                          (by dsimp only; rw [hrd1]; exact Nat.sub_lt_sub_left hrd_lt (by omega))
                          ⟨by omega, hrbF_le, fuelL, rngF, sigF, scrF, hflL, hsgF, hscF, hKF, hnvF,
                            hmF⟩
                        let sF : FullState :=
                          { s with
                            core := { s.core with fuel := fuelL }
                            scratch := { s.scratch with rng_state := rngF, sim_sig := sigF,
                                                        scratch_buf := scrF } }
                        have hsl_sF : sF.scratch.scratch_buf.length = L.scrLen := by
                          dsimp only [sF]; rw [hL_len]; exact hscF
                        obtain ⟨Rfr, hRfr⟩ :
                            ∃ Rfr : Mem 64 → Prop, Rfr = (FullK6Frame c L sF ⋆ R) := ⟨_, rfl⟩
                        have hm_ka : (K6MemA L (L.kPtr c.pScratchBuf)
                            (k6StateOfScratch L scrF) ⋆ Rfr) mF := by
                          have hmF' := hmF
                          change (FullMem c sF ⋆ R) mF at hmF'
                          rw [fullMem_eq_k6Frame hsl_sF] at hmF'; rw [hRfr]
                          exact k6Mem_to_amem hKF.shapes (sep_ac hmF')
                        m6_to_group
                        try refine wp_unroll_group fun _ _ => ?_
                        try refine wp_unroll_group fun _ _ => ?_
                        m6_split; rotate_left; · m6_steps; exact hnext
                        m6_split; rotate_left; · m6_steps; exact hnext
                        change wp _ _ _ _ _
                        c0_hsteps_nogrp
                        try dsimp only [Prod.fst]
                        try rw [hkptr_c0]
                        open scoped FullK6DynMem in m6_split; rotate_left
                        · m6_steps; exact hnext
                        have hrbF_lt : rbitF.toNat < 64 := ‹_›
                        have hrbF1 : (rbitF + 1#32).toNat = rbitF.toNat + 1 :=
                          m6_bv32_add1 (by omega)
                        change wp _ _ _ _ _
                        c0_hsteps
                        try dsimp only [Prod.fst]
                        try rw [hkptr_c0]
                        open scoped K6MemATactics K6PtrTactics in c0_hsteps!
                        have hKF0 := k6Inv_set_nassump0 hKF
                        rw [hRfr, show (0 : BitVec 32) = 0#32 from rfl] at hm
                        have hscF' : sF.scratch.scratch_buf.length = c.scratch_cap := hscF
                        let scrR0 := sF.scratch.scratch_buf.take L.k6Base ++
                          ((k6StateOfScratch L scrF).putHdr .nassump 0#32).toSlab
                        let sR0 : FullState :=
                          { sF with scratch := { sF.scratch with scratch_buf := scrR0 } }
                        obtain ⟨hscrR0, _, hofR0, hmR0⟩ :=
                          m6_join_k6_ofSlab (s := sF) hL_len hscF' hKF0.shapes hm
                        change scrR0.length = c.scratch_cap at hscrR0
                        change k6StateOfScratch L scrR0 =
                          (k6StateOfScratch L scrF).putHdr .nassump 0#32 at hofR0
                        change (FullMem c sR0 ⋆ R) _ at hmR0
                        have hlenR0 : sR0.LengthsOk c :=
                          ⟨{ hlen.core_ok with vals_len := hlen.core_ok.vals_len },
                           { hlen.scratch_ok with
                            sim_sig_len := hsgF, scratch_buf_len := hscrR0 }⟩
                        have hnvR0 : (k6StateOfScratch L scrR0).nv = nv := by rw [hofR0]; exact hnvF
                        have hassR0 : k6AssumpLitsS L scrR0 = [] := by
                          unfold k6AssumpLitsS k6AssumpLits; rw [hofR0]; simp [K6State.putHdr]
                        m6_call hSolve
                        refine ⟨c, sR0, P, L, R, rfl, hlenR0, hL_len, hL_mv, hofR0 ▸ hKF0, hnvR0,
                          hmR0,
                          fun stS fuelS rngS scrS mS hlenS hfuelS _ hKS _ hnvS _ hassS _ hstS hunsS
                            hmS => ?_⟩
                        have hscS := hlenS.scratch_ok.scratch_buf_len
                        have hflS0 : fuelS.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfuelS hflL
                        m6_split
                        · have hstS20 : stS = 20#64 := hc
                          have huns_cur : (cnfOfClauses F_cur).Unsat := by
                            apply m6_coneModelSet_unsat_of_empty
                              (ws1 := s.scratch.work_stk1) (nv := nv.toNat)
                            intro β hβ
                            have hna := hunsS hstS20 β hβ
                            rw [hassS, hassR0] at hna
                            exact hna (by simp [unitsCnf])
                          m6_steps
                          exact hQ 0xFFFFFFFF#32 fuelS rngS sigF scrS mS
                            (hmk_dense fuelS rngS sigF scrS hsgF hscS)
                            hflS0 (hmk_cone fuelS rngS sigF scrS hscS hKS hnvS)
                            (fun _ => huns_cur) (fun h => absurd rfl h) hmS
                        m6_split
                        · m6_steps
                          exact hJbrk (rbitF, round + 1#32, ()) mS
                            ⟨hrbF_le, fuelS, rngS, sigF, scrS, hflS0, hsgF, hscS, hKS, hnvS, hmS⟩
                        m6_call hRef
                        refine ⟨c, _, R, rfl, hlenS, hcap, by rw [← hL_mv]; exact hnv_L, hnv_mx,
                          hws_lt, hmS, fun sigS mS' hsgS hmS' => ?_⟩
                        m6_steps
                        exact hJrd (rbitF + 1#32, round + 1#32, ()) mS'
                          (by dsimp only; rw [hrd1]; exact Nat.sub_lt_sub_left hrd_lt (by omega))
                          ⟨by omega, by omega, fuelS, rngS, sigS, scrS, hflS0, hsgS, hscS, hKS,
                           hnvS, hmS'⟩)
                      (fun _ hJfrBrk => by
                        refine wp_loop_inv (ts := [i32, i32])
                          (fun (rbitI, fr, ()) mI => fr.toNat ≤ 3 ∧ rbitI.toNat ≤ 64 ∧
                            ∃ rngI sigI scrI,
                              sigI.length = c.max_vars ∧ scrI.length = c.scratch_cap ∧
                              K6Inv L P (k6StateOfScratch L scrI) ∧
                              (k6StateOfScratch L scrI).nv = nv ∧
                              (FullMem c { s with
                                core := { s.core with fuel := fuelL }
                                scratch := { s.scratch with rng_state := rngI, sim_sig := sigI,
                                                            scratch_buf := scrI } } ⋆ R) mI)
                          (fun (_, fr, ()) _ => 3 - fr.toNat)
                          (fun _ hJfr => by
                            m6_steps
                            exact hJfr (rbit, 0#32, ()) ml
                              ⟨Nat.zero_le _, hrb_le, rngL, sigL, scrL, hsgL, hscL, hKL, hnvL,
                               hml⟩)
                          (fun _ (rbitI, fr, ()) mI
                              ⟨hfr_le, hrbI_le, rngI, sigI, scrI, hsgI, hscI, hKI, hnvI,
                                hmI⟩ hJfr => by
                            have hbrkI := hJfrBrk (rbitI, fr, ()) mI
                              ⟨hrbI_le, rngI, sigI, scrI, hsgI, hscI, hKI, hnvI, hmI⟩
                            m6_split; rotate_left; · m6_steps; exact hbrkI
                            m6_split; rotate_left; · m6_steps; exact hbrkI
                            have hfr_lt : fr.toNat < 3 := ‹_›
                            have hrbI_lt : rbitI.toNat < 64 := hc
                            have hfr1 : (fr + 1#32).toNat = fr.toNat + 1 := m6_bv32_add1 (by omega)
                            have hrbI1 : (rbitI + 1#32).toNat = rbitI.toNat + 1 :=
                              m6_bv32_add1 (by omega)
                            let sI : FullState :=
                              { s with
                                core := { s.core with fuel := fuelL }
                                scratch := { s.scratch with rng_state := rngI, sim_sig := sigI,
                                                            scratch_buf := scrI } }
                            have hlenI : sI.LengthsOk c :=
                              ⟨{ hlen.core_ok with vals_len := hlen.core_ok.vals_len },
                               { hlen.scratch_ok with
                                sim_sig_len := hsgI, scratch_buf_len := hscI }⟩
                            m6_call hFlipR
                            refine ⟨c, sI, P, L, R, rfl, hlenI, hL_len, hL_mv, hKI, hnvI, hmI,
                              fun flp rngF1 scrF1 mF1 hlenF1 _ hKF1 hnvF1 _ _ _ hmF1 => ?_⟩
                            have hscF1 := hlenF1.scratch_ok.scratch_buf_len
                            m6_split; rotate_left
                            · m6_steps
                              exact hJfrBrk (rbitI, fr, ()) mF1
                                ⟨hrbI_le, rngF1, sigI, scrF1, hsgI, hscF1, hKF1, hnvF1, hmF1⟩
                            m6_call hRef
                            refine ⟨c, _, R, rfl, hlenF1, hcap, by rw [← hL_mv]; exact hnv_L,
                              hnv_mx, hws_lt, hmF1, fun sigF1 mF2 hsgF1 hmF2 => ?_⟩
                            m6_steps
                            exact hJfr (rbitI + 1#32, fr + 1#32, ()) mF2
                              (by dsimp only; rw [hfr1]
                                  exact Nat.sub_lt_sub_left hfr_lt (by omega))
                              ⟨by omega, by omega, rngF1, sigF1, scrF1, hsgF1, hscF1, hKF1,
                               hnvF1, hmF2⟩)))))
          (fun _ hJsl => by
            m6_split <;> (m6_steps; exact hJsl _ m2 rfl)))

end LeanQbe.T.Examples.Kissat.FullM6Sweep
