module

public import LeanQbe.T.Examples.Kissat.FullM4SweepLemmas1

/-!
# Kissat `D-Full` M4b — 512-Var Cone Extraction `Func.wp` Proof (`19/24`)

Proves the parametric `(Γ : Env)` `Func.wp` contract for `full_m4_sweep_cone` (`19/24`):
- BFS up to `K512_MAX_V = 512` variables and `K512_MAX_ORIG = 1536` clauses from `root_v`.
- Tracks `ConeModelSet F_cur work_stk1 nv`, `K512LitsBounded nv`, `K512TrailSynced`, `lvl = 0`,
  `trl_end = 0`, `prop = 0`, `incons = 0`, `nassump = 0`, and `K512ScratchInv`.
- Shrinks `k[K5H_NV]`, `k[K5H_UNASS]`, `k[K5H_QLAST]`, `k[K5H_QSEARCH]`, and
  `k[K5O_QNEXT + nv - 1]` to `nv` via `k5ShrinkNv_preserves_inv`, yielding `M4SweepConeOk`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM4Sweep

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test
open FullArenaTactics FullSweepFwdHelpers FullSweepVarHelpers
open scoped FullArenaTactics M4SweepTactics

/-! ## 1. Pure Helpers for `full_m4_sweep_cone` -/

private theorem m4_getElem_eq_getD {α : Type} (xs : List α) {i : Nat}
    (h : i < xs.length) (d : α) : xs[i]'h = xs[i]?.getD d := by
  rw [List.getElem?_eq_getElem h, Option.getD_some]

private theorem m4_list_getElem_congr {α : Type} {xs : List α} {i j : Nat}
    (hij : i = j) (hi : i < xs.length) (hj : j < xs.length) :
    xs[i]'hi = xs[j]'hj := by subst hij; rfl

private theorem m4_bv32_shr1_toNat (x : BitVec 32) : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem m4_bv32_and1_toNat (x : BitVec 32) : (x &&& 1#32).toNat = x.toNat % 2 := by
  rw [BitVec.toNat_and, show (1#32).toNat = 1 from rfl]
  simp [Nat.and_two_pow_sub_one_eq_mod x.toNat 1]

private theorem m4_bv32_shl1_or_and1 (t l : BitVec 32) (ht : t.toNat < 2 ^ 31) :
    ((t <<< (1 : Nat)) ||| (l &&& 1#32)).toNat = 2 * t.toNat + l.toNat % 2 := by
  have h1 : (l &&& 1#32).toNat < 2 := by rw [m4_bv32_and1_toNat]; omega
  simpa [m4_bv32_and1_toNat] using FullSweepVarHelpers.bv32_shl1_or_pol t (l &&& 1#32) ht h1

private theorem m4_bv32_add1_sub1_eq (x : BitVec 32) : x + 1#32 - 1#32 = x := by bv_omega

private theorem m4_bv32_add1_sub1_toNat (x : BitVec 32) :
    (x + (1 : BitVec 32) - (1 : BitVec 32)).toNat = x.toNat := by bv_omega

private theorem m4_bv32_ofNat_add1 (x : BitVec 32) :
    BitVec.ofNat 32 (x.toNat + 1) = x + 1#32 := by bv_omega

private theorem m4_bv32_sub1_of_eq (x y : BitVec 32) (h : x - 1#32 = y) : x = y + 1#32 := by
  bv_omega

private theorem m4_bv32_ofNat_add1_sub1 (q : BitVec 32) :
    BitVec.ofNat 32 (q.toNat + 1) - 1#32 = q := by bv_omega

private theorem m4_bv64_shl1 (x : BitVec 32) :
    (x.setWidth 64 <<< (1 : Nat)).toNat = 2 * x.toNat := by
  have hx := x.isLt
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega : x.toNat * 2 < 2 ^ 64)]; omega

private theorem m4_bv64_shl1_add1 (x : BitVec 32) :
    ((x.setWidth 64 <<< (1 : Nat)) + 1#64).toNat = 2 * x.toNat + 1 := by
  have hx := x.isLt
  rw [BitVec.toNat_add, m4_bv64_shl1, show (1#64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega : 2 * x.toNat + 1 < 2 ^ 64)]

private theorem m4_pack_nv_nc (nv nc : BitVec 32) (hnv : nv.toNat ≤ 512) (_hnc : nc.toNat ≤ 1536) :
    ((nv.setWidth 64 ||| (nc.setWidth 64 <<< (16 : Nat))) &&& 0xFFFF#64).toNat = nv.toNat := by
  have hlt16 : ∀ {x : Nat}, x < 2 ^ 16 → ∀ j, 16 ≤ j → x.testBit j = false := fun hx j hj =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hj))
  have hmask : ∀ j, Nat.testBit 65535 j = decide (j < 16) := fun j => by
    rw [show (65535 : Nat) = 2 ^ 16 - 1 from rfl, Nat.testBit_two_pow_sub_one]
  have h1 : (nv.setWidth 64 ||| (nc.setWidth 64 <<< (16 : Nat))) &&& 0xFFFF#64 =
      nv.setWidth 64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and, hmask]
    by_cases h16 : i < 16
    · have h32 : i < 32 := by omega
      simp [h16, h32]
    · simp only [h16, decide_false, Bool.and_false]
      rw [BitVec.getLsbD]
      exact (hlt16 (by omega : nv.toNat < 2 ^ 16) i (by omega)).symm
  rw [h1, bv_c0_zext32_64]

private theorem semEntails_coneModelSet_of_entails {F_cur : List (List Nat)}
    {ws1 : List (BitVec 32)} {nv : Nat} {lits : List Nat}
    (hlts : ∀ l ∈ lits, l < 2 * nv)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause (lits.map (FullSweepFwdSpecs.coneLift ws1)))) :
    SemEntails (ConeModelSet F_cur ws1 nv) lits := by
  intro β ⟨α, hα, hβ⟩
  have hsat := (CNF.entails_clause_def.mp hent) α hα
  rw [clause_sat_cnfClause_iff] at hsat ⊢
  obtain ⟨gl, hgl_m, hgl_s⟩ := hsat
  obtain ⟨l, hl_m, rfl⟩ := List.mem_map.mp hgl_m
  refine ⟨l, hl_m, ?_⟩
  have hl_lt := hlts l hl_m
  have hvar : litVar (FullSweepFwdSpecs.coneLift ws1 l) = (ws1[l / 2]?.getD 0#32).toNat := by
    unfold litVar FullSweepFwdSpecs.coneLift; omega
  have hsign : litSign (FullSweepFwdSpecs.coneLift ws1 l) = litSign l := by
    unfold litSign FullSweepFwdSpecs.coneLift; simp [Nat.add_mod]
  rw [hvar, hsign] at hgl_s
  rw [show litVar l = l / 2 from rfl, hβ (l / 2) (by omega)]
  exact hgl_s

private theorem k5ShrinkNv_preserves_inv {acap : Nat} {P : (Nat → Bool) → Prop}
    {ks : K512State} {nv : BitVec 32}
    (hinv : K512Inv acap P ks) (_hnv1 : 1 ≤ nv.toNat) (hnv512 : nv.toNat ≤ 512)
    (hks_nv : ks.nv = 512#32) (htrl0 : ks.trl_end = 0#32) (hprop0 : ks.prop = 0#32)
    (_hlvl0 : ks.lvl = 0#32) (hna0 : ks.nassump = 0#32)
    (hbdd : K512LitsBounded nv.toNat ks) :
    let ks' := (((((ks.putHdr .nv nv).putHdr .unass nv).putHdr .qlast (nv - 1#32)).putHdr
      .qsearch (nv - 1#32)).putHdr .qstamp nv).putArr .qnext (nv.toNat - 1) 0xFFFFFFFF#32
    K512Inv acap P ks' ∧ ks'.nv = nv := by
  intro ks'
  have hks'_nv : ks'.nv.toNat = nv.toNat := rfl
  have hsh' : ks'.ShapesOk acap :=
    (((((hinv.shapes.putHdr _ _).putHdr _ _).putHdr _ _).putHdr _ _).putHdr _ _).putArr _ _ _
  have hnv_le_old : nv.toNat ≤ ks.nv.toNat := by rw [hks_nv]; simpa using hnv512
  have hcl' : K512ClausesOk acap P ks' :=
    { acap_ge := hinv.clauses.acap_ge
      acap_lt := hinv.clauses.acap_lt
      acap_eq := hinv.clauses.acap_eq
      nv_le := hnv512
      nc_le := hinv.clauses.nc_le
      alen_le := hinv.clauses.alen_le
      nassump_le := hinv.clauses.nassump_le
      nkl_le := hinv.clauses.nkl_le
      nana_le := hinv.clauses.nana_le
      cl_wf := fun cid hc => by
        have hw := hinv.clauses.cl_wf cid hc
        exact ⟨hw.1, hw.2.1, hbdd.1 cid hc, hw.2.2.2⟩
      cl_mono := hinv.clauses.cl_mono
      incons_ok := hinv.clauses.incons_ok
      assump_ok := fun i hi => by
        change i < ks.nassump.toNat at hi; rw [hna0] at hi; simp at hi
      flags_clean := fun v hv => hinv.clauses.flags_clean v (by omega) }
  have hwat' : K512WatchesOk ks' := by
    obtain ⟨chains, hlen, hnd, hch, hmem⟩ := hinv.watches
    refine ⟨chains.take (2 * nv.toNat), by simp [hlen]; omega, ?_, fun l hl => ?_,
      fun l hl w hw => ?_⟩
    · have hcat : chains = chains.take (2 * nv.toNat) ++ chains.drop (2 * nv.toNat) :=
        (List.take_append_drop _ _).symm
      rw [hcat, List.flatten_append, List.nodup_append] at hnd
      exact hnd.1
    · have hget : (chains.take (2 * nv.toNat))[l]? = chains[l]? := List.getElem?_take_of_lt hl
      rw [hget]; exact hch l (by omega)
    · have hget : (chains.take (2 * nv.toNat))[l]? = chains[l]? := List.getElem?_take_of_lt hl
      rw [hget] at hw
      have hm := hmem l (by omega) w hw
      exact ⟨hm.1, hm.2.1, hm.2.2.1, hbdd.2 w hm.1⟩
  have hasgn' : K512BaseAssignOk P ks' :=
    { trl_end_le := by change ks.trl_end.toNat ≤ nv.toNat; rw [htrl0]; simp
      prop_le := by change ks.prop.toNat ≤ ks.trl_end.toNat; rw [hprop0, htrl0]; simp
      unass_eq := by change nv.toNat + ks.trl_end.toNat = nv.toNat; rw [htrl0]; simp
      vals_dom := fun l hl => hinv.assign.vals_dom l (by omega)
      vals_neg_iff := fun l hl => hinv.assign.vals_neg_iff l (by omega)
      vals_nz_iff_trl := fun l hl => hinv.assign.vals_nz_iff_trl l (by omega)
      trl_nodup := hinv.assign.trl_nodup
      trl_lt := fun l hl => by
        change l ∈ k5TrailLits ks at hl; unfold k5TrailLits at hl; rw [htrl0] at hl; simp at hl
      trl_lvl_le := fun v hv => hinv.assign.trl_lvl_le v (by omega)
      unass_lvl_zero := fun v hv => hinv.assign.unass_lvl_zero v (by omega)
      trl_lvl_mono := hinv.assign.trl_lvl_mono
      dec_earliest := hinv.assign.dec_earliest
      lvl0_ok := hinv.assign.lvl0_ok }
  exact ⟨⟨hsh', hcl', hwat', hasgn', hinv.reasons⟩, rfl⟩

private def m4ConeMask (t : FullState) : FullState :=
  { core := { t.core with tmp := [] }
    scratch := { t.scratch with work_stk1 := [], tarjan_mark := [], scratch_buf := [] } }

private theorem m4ConeMask_core_eq {s st : FullState} (h : AgreesExcept m4ConeMask s st) :
    st.core = { s.core with tmp := st.core.tmp } := by
  have hc : ({ st.core with tmp := [] } : FullCoreState) = { s.core with tmp := [] } :=
    congrArg FullState.core h
  cases h1 : st.core; cases h2 : s.core
  rw [h1, h2] at hc; cases hc; rfl

private theorem m4ConeMask_state_eq {s st : FullState} (h : AgreesExcept m4ConeMask s st) :
    st = { s with
      core := { s.core with tmp := st.core.tmp }
      scratch := { s.scratch with
        work_stk1 := st.scratch.work_stk1
        tarjan_mark := st.scratch.tarjan_mark
        scratch_buf := st.scratch.scratch_buf } } := by
  have hc := m4ConeMask_core_eq h
  have hs : (m4ConeMask st).scratch = (m4ConeMask s).scratch := congrArg FullState.scratch h
  cases st with | mk c1 sc1 => cases s with | mk c2 sc2 =>
  dsimp only [m4ConeMask] at hc hs ⊢
  cases sc1; cases sc2; cases hs; rw [hc]

private theorem m4ConeMask_preserves_dense {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} (hag : AgreesExcept m4ConeMask s st)
    (hlen : st.LengthsOk c) (hdw : FullDenseInvW c F0 F_cur s) :
    FullDenseInvW c F0 F_cur st := by
  have hc0 := m4ConeMask_core_eq hag
  generalize st.core.tmp = tmp' at hc0
  have hll : st.scratch.last_learned = s.scratch.last_learned := hag.get (·.scratch.last_learned)
  have hex : st.scratch.extend_len = s.scratch.extend_len := hag.get (·.scratch.extend_len)
  refine ⟨hlen, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc0]; exact fullWitnessInv_with_tmp_flags_fuel hdw.2.1 tmp' s.core.flags s.core.fuel
  · have hmc := hdw.2.2.1
    exact ⟨fun v hv => by simpa [hc0] using hmc.1 v hv,
      fun l hl => by simpa [hc0] using hmc.2 l hl⟩
  · have hnda := hdw.2.2.2.1; intro r hr hng
    dsimp only [fullArenaClauseRefs, fullArenaClauseGarb, fullArenaClauseLits] at hr hng ⊢
    simp only [fullArenaClauseRefsCore, fullArenaClauseGarbCore, fullArenaClauseLitsCore, hc0]
      at hr hng ⊢
    exact hnda r hr hng
  · refine ⟨fun i hi => ?_, by simpa [hex] using hdw.2.2.2.2.1.2⟩
    have h1 := hdw.2.2.2.2.1.1 i hi
    dsimp only at h1 ⊢; rw [hll, fullArenaClauseRefs, hc0]; exact h1
  · rw [hc0]; exact hdw.2.2.2.2.2.1
  · rw [hc0]; exact hdw.2.2.2.2.2.2

/-- Loop invariant for 512-var cone extraction (`full_m4_sweep_cone`). -/
private structure M4ConeInv (F_cur : List (List Nat)) (st : FullState) (nv nc : Nat) : Prop where
  nv_ge1 : 1 ≤ nv
  nv_le512 : nv ≤ 512
  nv_le_cv : nv ≤ st.core.cur_vars
  nc_le : nc ≤ 1536
  k5_inv : K512ScratchInv (ConeModelSet F_cur st.scratch.work_stk1 nv) st.scratch.scratch_buf
  k5_sync : K512TrailSynced (k5StateOfScratch st.scratch.scratch_buf)
  k5_nv : (k5StateOfScratch st.scratch.scratch_buf).nv = 512#32
  k5_lvl : (k5StateOfScratch st.scratch.scratch_buf).lvl = 0#32
  k5_trl : (k5StateOfScratch st.scratch.scratch_buf).trl_end = 0#32
  k5_prop : (k5StateOfScratch st.scratch.scratch_buf).prop = 0#32
  k5_unass : (k5StateOfScratch st.scratch.scratch_buf).unass = 512#32
  k5_incons : (k5StateOfScratch st.scratch.scratch_buf).incons = 0#32
  k5_na : (k5StateOfScratch st.scratch.scratch_buf).nassump = 0#32
  k5_bdd : K512LitsBounded nv (k5StateOfScratch st.scratch.scratch_buf)
  fwd : ∀ i < nv,
    (st.scratch.work_stk1[i]?.getD 0#32).toNat < st.core.cur_vars ∧
    st.scratch.tarjan_mark[(st.scratch.work_stk1[i]?.getD 0#32).toNat]?.getD 0#32 =
      BitVec.ofNat 32 (i + 1)
  rev : ∀ v < st.core.cur_vars,
    st.scratch.tarjan_mark[v]?.getD 0#32 = 0#32 ∨
    ∃ i < nv,
      (st.scratch.work_stk1[i]?.getD 0#32).toNat = v ∧
      st.scratch.tarjan_mark[v]?.getD 0#32 = BitVec.ofNat 32 (i + 1)

private theorem m4ConeInv_tmp_irrel {F_cur : List (List Nat)} {st : FullState} {nv nc : Nat}
    {tmp' : List (BitVec 32)} (h : M4ConeInv F_cur st nv nc) :
    M4ConeInv F_cur { st with core := { st.core with tmp := tmp' } } nv nc :=
  ⟨h.nv_ge1, h.nv_le512, h.nv_le_cv, h.nc_le, h.k5_inv, h.k5_sync, h.k5_nv, h.k5_lvl,
   h.k5_trl, h.k5_prop, h.k5_unass, h.k5_incons, h.k5_na, h.k5_bdd, h.fwd, h.rev⟩

private theorem m4ConeInv_init {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {scr0 : List (BitVec 32)} {root_v : BitVec 32}
    (hlen : s.LengthsOk c) (hroot : root_v.toNat < s.core.cur_vars) (htmk : M4TmkZero s)
    (hscr0 : scr0.length = c.scratch_cap)
    (hK : ∀ P, K512ScratchInv P scr0) (hsy : K512TrailSynced (k5StateOfScratch scr0))
    (hnv : (k5StateOfScratch scr0).nv = 512#32) (hnc : (k5StateOfScratch scr0).nc = 0#32)
    (hlvl : (k5StateOfScratch scr0).lvl = 0#32) (hpr : (k5StateOfScratch scr0).prop = 0#32)
    (htr : (k5StateOfScratch scr0).trl_end = 0#32) (hun : (k5StateOfScratch scr0).unass = 512#32)
    (hin : (k5StateOfScratch scr0).incons = 0#32) (hna : (k5StateOfScratch scr0).nassump = 0#32) :
    let s1 : FullState :=
      { s with scratch :=
        { s.scratch with
          scratch_buf := scr0
          work_stk1 := s.scratch.work_stk1.set 0 root_v
          tarjan_mark := s.scratch.tarjan_mark.set root_v.toNat 1#32 } }
    s1.LengthsOk c ∧ AgreesExcept m4ConeMask s s1 ∧ M4ConeInv F_cur s1 1 0 := by
  intro s1
  have hcv_le := hlen.core_ok.cur_vars_le
  have hwk_len := hlen.scratch_ok.work_stk1_len
  have htm_len := hlen.scratch_ok.tarjan_mark_len
  refine ⟨⟨hlen.core_ok, { hlen.scratch_ok with
      work_stk1_len := by simp [s1, hwk_len]
      tarjan_mark_len := by simp [s1, htm_len]
      scratch_buf_len := by simp [s1, hscr0] }⟩,
    rfl,
    { nv_ge1 := Nat.le_refl 1
      nv_le512 := by decide
      nv_le_cv := by dsimp [s1]; omega
      nc_le := by decide
      k5_inv := hK _
      k5_sync := hsy
      k5_nv := hnv
      k5_lvl := hlvl
      k5_trl := htr
      k5_prop := hpr
      k5_unass := hun
      k5_incons := hin
      k5_na := hna
      k5_bdd := ⟨fun cid hc => by rw [hnc] at hc; simp at hc,
                 fun w hw => by rw [hnc] at hw; simp at hw⟩
      fwd := fun i hi => by
        have hi0 : i = 0 := by omega
        subst hi0; dsimp only [s1]
        rw [List.getElem?_set_self (by omega), Option.getD_some,
          List.getElem?_set_self (by omega), Option.getD_some]
        exact ⟨hroot, rfl⟩
      rev := fun v hv => by
        dsimp only [s1]
        by_cases hvr : v = root_v.toNat
        · subst hvr; right; refine ⟨0, Nat.zero_lt_one, ?_, ?_⟩
          · rw [List.getElem?_set_self (by omega), Option.getD_some]
          · rw [List.getElem?_set_self (by omega), Option.getD_some]
        · left; rw [List.getElem?_set_ne (Ne.symm hvr)]; exact htmk v hv }⟩

private theorem m4ConeInv_push_var {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {nv nc : Nat} {ov : BitVec 32}
    (hlen : s.LengthsOk c) (hc : M4ConeInv F_cur s nv nc)
    (hnv512 : nv < 512) (hov : ov.toNat < s.core.cur_vars)
    (hmiss : s.scratch.tarjan_mark[ov.toNat]?.getD 0#32 = 0#32) :
    nv < s.core.cur_vars ∧
    let s' : FullState :=
      { s with scratch :=
        { s.scratch with
          tarjan_mark := s.scratch.tarjan_mark.set ov.toNat (BitVec.ofNat 32 (nv + 1))
          work_stk1 := s.scratch.work_stk1.set nv ov } }
    M4ConeInv F_cur s' (nv + 1) nc := by
  have hcv_le := hlen.core_ok.cur_vars_le
  have hwk_len := hlen.scratch_ok.work_stk1_len
  have htm_len := hlen.scratch_ok.tarjan_mark_len
  have hne_ov : ∀ i < nv, (s.scratch.work_stk1[i]?.getD 0#32).toNat ≠ ov.toNat := fun i hi heq => by
    have hti := (hc.fwd i hi).2; rw [heq, hmiss] at hti
    have htn := congrArg BitVec.toNat hti
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i + 1 < 2 ^ 32)] at htn; omega
  have hnv_lt : nv < s.core.cur_vars :=
    inj_lt_of_missing (fun i => (s.scratch.work_stk1[i]?.getD 0#32).toNat)
      (fun i j hi hj heq => by
        have hti := (hc.fwd i hi).2; have htj := (hc.fwd j hj).2
        rw [heq] at hti
        have htn := congrArg BitVec.toNat (hti.symm.trans htj)
        simp only [BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : i + 1 < 2 ^ 32),
          Nat.mod_eq_of_lt (by omega : j + 1 < 2 ^ 32)] at htn; omega)
      (fun i hi => (hc.fwd i hi).1) hov hne_ov
  refine ⟨hnv_lt, ?_⟩
  intro s'
  have hwk_lt : ∀ i < nv, s'.scratch.work_stk1[i]? = s.scratch.work_stk1[i]? := fun i hi =>
    List.getElem?_set_ne (by omega)
  have hwk_nv : s'.scratch.work_stk1[nv]? = some ov := List.getElem?_set_self (by omega)
  exact
    { nv_ge1 := by omega
      nv_le512 := by omega
      nv_le_cv := by dsimp [s']; omega
      nc_le := hc.nc_le
      k5_inv := k5ScratchInv_mono_P (fun β hβ => coneModelSet_push_var β hβ) hc.k5_inv
      k5_sync := hc.k5_sync
      k5_nv := hc.k5_nv
      k5_lvl := hc.k5_lvl
      k5_trl := hc.k5_trl
      k5_prop := hc.k5_prop
      k5_unass := hc.k5_unass
      k5_incons := hc.k5_incons
      k5_na := hc.k5_na
      k5_bdd := ⟨fun cid hcid l hl => Nat.lt_trans (hc.k5_bdd.1 cid hcid l hl) (by omega),
                 fun w hw => Nat.lt_trans (hc.k5_bdd.2 w hw) (by omega)⟩
      fwd := fun i hi => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · rw [hwk_lt i hi']
          have hne := hne_ov i hi'
          refine ⟨(hc.fwd i hi').1, ?_⟩
          dsimp only [s']; rw [List.getElem?_set_ne (Ne.symm hne)]; exact (hc.fwd i hi').2
        · rw [hwk_nv, Option.getD_some]
          refine ⟨hov, ?_⟩
          dsimp only [s']; rw [List.getElem?_set_self (by omega), Option.getD_some]
      rev := fun v hv => by
        dsimp only [s']
        by_cases hvo : v = ov.toNat
        · subst hvo; right; refine ⟨nv, by omega, ?_, ?_⟩
          · rw [hwk_nv, Option.getD_some]
          · rw [List.getElem?_set_self (by omega), Option.getD_some]
        · rw [List.getElem?_set_ne (Ne.symm hvo)]
          rcases hc.rev v hv with hz | ⟨i, hi, hwi, hti⟩
          · exact Or.inl hz
          · exact Or.inr ⟨i, by omega, by rw [List.getElem?_set_ne (by omega)]; exact hwi, hti⟩ }

private theorem m4_cone_clause_entails_filtered {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} {cr : Nat} {kept : List Nat}
    (hw : FullWitnessInv c F0 F_cur k) (hl0 : k.cur_level = 0)
    (href : cr ∈ fullArenaClauseRefsCore k) (hng : fullArenaClauseGarbCore k cr = false)
    (hcov : ∀ l ∈ fullArenaClauseLitsCore k cr, k.vals[l]?.getD 0#8 = 0xFF#8 ∨ l ∈ kept) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause kept) := by
  rw [CNF.entails_clause_def]; intro α hα
  have hent := hw.arena.entails cr href hng; rw [CNF.entails_clause_def] at hent
  obtain ⟨l, hl_mem, hl_sat⟩ := (clause_sat_cnfClause_iff _ _).mp (hent α hα)
  rcases hcov l hl_mem with hfals | hkept
  · exact absurd ((sat_cnfClause_singleton _ _).mpr hl_sat)
      (level0_false_not_sat hw hl0 (hw.arena.lits_lt cr href hng l hl_mem) hfals hα)
  · exact (clause_sat_cnfClause_iff _ _).mpr ⟨l, hkept, hl_sat⟩

private theorem m4_arenaClauseLitsCore_mem_iff {k : FullCoreState} {cr l : Nat}
    (hbd : cr + 3 + (k.arena[cr + 2]?.getD 0#32).toNat ≤ k.arena.length) :
    l ∈ fullArenaClauseLitsCore k cr ↔
      ∃ i < (k.arena[cr + 2]?.getD 0#32).toNat, (k.arena[cr + 3 + i]?.getD 0#32).toNat = l := by
  unfold fullArenaClauseLitsCore fullArenaClauseSizeCore
  generalize (k.arena[cr + 2]?.getD 0#32).toNat = sz at hbd ⊢
  simp only [List.mem_map]; constructor
  · rintro ⟨w, hw, rfl⟩; obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hw
    simp only [List.length_take, List.length_drop,
      Nat.min_eq_left (by omega : sz ≤ k.arena.length - (cr + 3))] at hi
    refine ⟨i, hi, ?_⟩; simp only [List.getElem_take, List.getElem_drop] at heq
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some, heq]
  · rintro ⟨i, hi, rfl⟩
    have hmem : ((k.arena.drop (cr + 3)).take sz)[i]'(by simp; omega) ∈
        (k.arena.drop (cr + 3)).take sz := List.getElem_mem _
    exact ⟨k.arena[cr + 3 + i]'(by omega),
      by simpa [List.getElem_take, List.getElem_drop] using hmem,
      by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]⟩

private theorem m4_cone_occ_hdr_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st_w : FullState} {cr sz : BitVec 32} (hlen : s.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur s.core) (hnd : FullArenaVarsNodup s)
    (har_eq : st_w.core.arena = s.core.arena) (hcr_ref : cr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hsz_core : sz.toNat = fullArenaClauseSizeCore s.core cr.toNat)
    (hgr0 : (st_w.core.arena[cr.toNat]'(by
      have := (hw.arena.refs_wf cr.toNat hcr_ref).1; have := hlen.core_ok.arena_len_le
      rw [har_eq, hlen.core_ok.arena_len_arr]; omega) &&& (0x00080000#32 ||| 0x00400000#32)) =
      0#32) :
    fullArenaClauseGarbCore s.core cr.toNat = false ∧
    cr.toNat + 3 + sz.toNat ≤ s.core.arena_len ∧ sz.toNat ≤ s.core.cur_vars ∧
    cr.toNat + 3 + sz.toNat ≤ s.core.arena.length := by
  have hwf := hw.arena.refs_wf cr.toNat hcr_ref
  have hal := hlen.core_ok.arena_len_le; have har := hlen.core_ok.arena_len_arr
  have hng : fullArenaClauseGarbCore s.core cr.toNat = false := by
    unfold fullArenaClauseGarbCore fullArenaHdrCore
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    have h0 := bv32_garb_false_of_and_garb_red hgr0; simp [har_eq] at h0; simp [h0]
  have hsz_le : cr.toNat + 3 + sz.toNat ≤ s.core.arena_len := by have := hwf.2.2; omega
  have hsz_cv : sz.toNat ≤ s.core.cur_vars := by
    have hlen_lits : (fullArenaClauseLits s cr.toNat).length = sz.toNat := by
      unfold fullArenaClauseLits fullArenaClauseLitsCore
      rw [List.length_map, List.length_take, List.length_drop, ← hsz_core]
      exact Nat.min_eq_left (by omega)
    rw [← hlen_lits]
    have hle := nodup_length_le_of_lt (xs := (fullArenaClauseLits s cr.toNat).map (· / 2))
      (n := s.core.cur_vars) (hnd cr.toNat hcr_ref hng) fun v hv => by
        rcases List.mem_map.mp hv with ⟨l, hl, rfl⟩
        have := hw.arena.lits_lt cr.toNat hcr_ref hng l hl; omega
    simpa [List.length_map] using hle
  exact ⟨hng, hsz_le, hsz_cv, by omega⟩

private theorem m4_cone_bin_lits_ok {st : FullState}
    {cv qi pol lit ot ov nv : BitVec 32} {iov : Nat}
    (hqi_lt : qi.toNat < nv.toNat) (hnv512 : nv.toNat ≤ 512) (hpol_lt : pol.toNat < 2)
    (hlit_eq : lit.toNat = 2 * cv.toNat + pol.toNat) (hov_eq : ov.toNat = ot.toNat / 2)
    (hiov : iov < nv.toNat)
    (htca : st.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 (qi.toNat + 1))
    (hwca : (st.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat = cv.toNat)
    (htov : st.scratch.tarjan_mark[ov.toNat]?.getD 0#32 = BitVec.ofNat 32 (iov + 1))
    (hwov : (st.scratch.work_stk1[iov]?.getD 0#32).toNat = ov.toNat) :
    let l0 := (((st.scratch.tarjan_mark[cv.toNat]?.getD 0#32) - 1#32) <<< (1 : Nat)) ||| pol
    let l1 := (((st.scratch.tarjan_mark[ov.toNat]?.getD 0#32) - 1#32) <<< (1 : Nat)) |||
      (ot &&& 1#32)
    l0.toNat < 2 * nv.toNat ∧ l1.toNat < 2 * nv.toNat ∧
    FullSweepFwdSpecs.coneLift st.scratch.work_stk1 l0.toNat = lit.toNat ∧
    FullSweepFwdSpecs.coneLift st.scratch.work_stk1 l1.toNat = ot.toNat := by
  intro l0 l1
  have hm0 : BitVec.ofNat 32 (qi.toNat + 1) - 1#32 = BitVec.ofNat 32 qi.toNat := by bv_omega
  have hm1 : BitVec.ofNat 32 (iov + 1) - 1#32 = BitVec.ofNat 32 iov := by bv_omega
  have hl0 : l0.toNat = 2 * qi.toNat + pol.toNat := by
    dsimp only [l0]; rw [htca, hm0]
    have := FullSweepVarHelpers.bv32_shl1_or_pol (BitVec.ofNat 32 qi.toNat) pol
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega) hpol_lt
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : qi.toNat < 2 ^ 32)] using this
  have hl1 : l1.toNat = 2 * iov + ot.toNat % 2 := by
    dsimp only [l1]; rw [htov, hm1]
    have := m4_bv32_shl1_or_and1 (BitVec.ofNat 32 iov) ot
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : iov < 2 ^ 32)] using this
  refine ⟨by omega, by omega, ?_, by rw [hl1]; exact coneLift_of_tmk_pair hwov hov_eq.symm⟩
  rw [hl0]; simpa [show lit.toNat % 2 = pol.toNat by omega] using
    coneLift_of_tmk_pair (wk := st.scratch.work_stk1) (idx := qi.toNat) (v := cv.toNat)
      (l := lit.toNat) hwca (by omega)

private theorem m4_cone_call_add_clause {Γ : Env}
    (hAddCl : M4EnvSpec Γ "full_k512_add_clause" k5AddClauseSpec)
    {c : FullCfg} {F_cur : List (List Nat)} {s0 st : FullState}
    {nv nc sz : BitVec 32} {aSz : Arg Val i32}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    {k : Tup Val [.bool] → Expr Val Cont [i64]}
    (haSz : aSz.val = sz) (hlen : st.LengthsOk c) (hag : AgreesExcept m4ConeMask s0 st)
    (hcone : M4ConeInv F_cur st nv.toNat nc.toNat)
    (hnc : nc.toNat < 1536) (hsz2 : 2 ≤ sz.toNat) (hsz16 : sz.toNat < 2 ^ 16)
    (hsz_tmp : sz.toNat ≤ st.core.tmp.length)
    (hlts : ∀ j < sz.toNat, (st.core.tmp[j]?.getD 0#32).toNat < 2 * nv.toNat)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause
      ((st.core.tmp.take sz.toNat).map (fun x => FullSweepFwdSpecs.coneLift st.scratch.work_stk1
        x.toNat))))
    (hm : (FullMem c st ⋆ R) m)
    (hk : ∀ (ok : Bool) (st' : FullState) (m' : Mem 64),
      st'.LengthsOk c → AgreesExcept m4ConeMask s0 st' →
      M4ConeInv F_cur st' nv.toNat (if ok then nc + 1#32 else nc).toNat →
      st'.scratch.tarjan_mark = st.scratch.tarjan_mark →
      st'.scratch.work_stk1 = st.scratch.work_stk1 →
      (FullMem c st' ⋆ R) m' → wp Γ Q X (k (ok, ())) m') :
    wp Γ Q X (Expr.call (as := [i64, i64, i32]) (bs := [.bool])
      "full_k512_add_clause" (Arg.var c.hdr, Arg.var c.pTmp, aSz, ()) k) m := by
  have hnv512 : nv.toNat ≤ 512 := hcone.nv_le512
  have hlts512 : ∀ j < sz.toNat,
      (st.core.tmp[j]?.getD 0#32).toNat < 2 * (k5StateOfScratch st.scratch.scratch_buf).nv.toNat :=
    fun j hj => by rw [hcone.k5_nv]; simp; have := hlts j hj; omega
  have hsem : SemEntails (ConeModelSet F_cur st.scratch.work_stk1 nv.toNat)
      ((st.core.tmp.take sz.toNat).map BitVec.toNat) := by
    refine semEntails_coneModelSet_of_entails (fun l hl => ?_) ?_
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hl
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
      have hjl : j < sz.toNat := by rw [List.length_take] at hj; omega
      have hxj := hlts j hjl
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hxj
      rwa [List.getElem_take]
    · simp only [List.map_map]; simpa [Function.comp_def] using hent
  refine wp_call_of_spec _ k ?_
  simp only [vals, Arg.val_var, haSz]
  refine hAddCl (c.hdr, c.pTmp, sz, ()) m (fun r m' => wp Γ Q X (k r) m') X
    ⟨c, st, ConeModelSet F_cur st.scratch.work_stk1 nv.toNat, st.scratch.scratch_buf,
      st.core.tmp, fullSweepAddRestTmp c st ⋆ R,
      rfl, hlen, rfl, hcone.k5_inv, hcone.k5_sync, hcone.k5_lvl, hsz_tmp, hsz16, hlts512, hsem,
      fullMem_focus_addCl_tmp hm,
      fun ok scr' m' hsl _ hK' hsy' hlvl' hnv' hna' _ hge2 hbdd' hm' => ?_⟩
  let st' : FullState := { st with scratch := { st.scratch with scratch_buf := scr' } }
  have hlen' : st'.LengthsOk c := ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hsl }⟩
  have hag' : AgreesExcept m4ConeMask s0 st' := hag.update _ (fun _ => rfl)
  have hhdr : Full.hdrTailWords c st' = Full.hdrTailWords c
      { st with scratch := { st.scratch with scratch_buf := scr', res_sz := st.scratch.res_sz } } :=
    rfl
  rw [hhdr] at hm'
  have hm_un := fullMem_unfocus_addCl_tmp hm'
  obtain ⟨htr', hun', hin'⟩ := hge2 hsz2
  have hpr' : (k5StateOfScratch scr').prop = 0#32 := by
    have hp := hK'.2.2.assign.prop_le
    rw [htr', hcone.k5_trl] at hp
    have : (k5StateOfScratch scr').prop.toNat = 0 := by simp at hp; omega
    exact BitVec.eq_of_toNat_eq (by simpa using this)
  have hbdd_nv : K512LitsBounded nv.toNat (k5StateOfScratch scr') :=
    hbdd' nv.toNat hlts hcone.k5_bdd
  have hnc1 : (nc + 1#32).toNat = nc.toNat + 1 := m4_bv32_add1 (by omega)
  cases ok
  · refine hk false st' m' hlen' hag'
      { hcone with k5_inv := hK', k5_sync := hsy', k5_nv := hnv'.trans hcone.k5_nv,
                   k5_lvl := hlvl', k5_trl := htr'.trans hcone.k5_trl, k5_prop := hpr',
                   k5_unass := hun'.trans hcone.k5_unass, k5_incons := hin'.trans hcone.k5_incons,
                   k5_na := hna'.trans hcone.k5_na, k5_bdd := hbdd_nv } rfl rfl hm_un
  · refine hk true st' m' hlen' hag'
      { hcone with nc_le := by simp only [↓reduceIte, hnc1]; omega
                   k5_inv := hK', k5_sync := hsy', k5_nv := hnv'.trans hcone.k5_nv,
                   k5_lvl := hlvl', k5_trl := htr'.trans hcone.k5_trl, k5_prop := hpr',
                   k5_unass := hun'.trans hcone.k5_unass, k5_incons := hin'.trans hcone.k5_incons,
                   k5_na := hna'.trans hcone.k5_na, k5_bdd := hbdd_nv } rfl rfl hm_un

private theorem m4_cone_k_unassigned_step {c : FullCfg}
    {F_cur : List (List Nat)} {s st_k st_u : FullState}
    {cr sz k cnt nv_k nv_u lit_k : BitVec 32} {nc_w ilv : Nat}
    (hlu : st_u.LengthsOk c) (htmpu_eq : st_u.core.tmp = st_k.core.tmp)
    (hwku_eq : ∀ j < nv_k.toNat, st_u.scratch.work_stk1[j]? = st_k.scratch.work_stk1[j]?)
    (hnvku : nv_k.toNat ≤ nv_u.toNat) (hnvu512 : nv_u.toNat ≤ 512)
    (hk_lt : k.toNat < sz.toNat) (hsz_le12 : sz.toNat ≤ 12) (hsz_cv : sz.toNat ≤ s.core.cur_vars)
    (hcv_le : s.core.cur_vars ≤ c.max_vars) (hcnt_le : cnt.toNat ≤ k.toNat)
    (hlit_ar : (s.core.arena[cr.toNat + 3 + k.toNat]?.getD 0#32).toNat = lit_k.toNat)
    (hilv : ilv < nv_u.toNat)
    (hwlv : (st_u.scratch.work_stk1[ilv]?.getD 0#32).toNat = lit_k.toNat / 2)
    (htlv_v : st_u.scratch.tarjan_mark[lit_k.toNat / 2]?.getD 0#32 = BitVec.ofNat 32 (ilv + 1))
    (hlts_k : ∀ j < cnt.toNat, (st_k.core.tmp[j]?.getD 0#32).toNat < 2 * nv_k.toNat)
    (hcov_k : ∀ i < k.toNat,
      let l := (s.core.arena[cr.toNat + 3 + i]?.getD 0#32).toNat
      s.core.vals[l]?.getD 0#8 = 0xFF#8 ∨
      l ∈ (st_k.core.tmp.take cnt.toNat).map
        (fun x => FullSweepFwdSpecs.coneLift st_k.scratch.work_stk1 x.toNat))
    (_hc_u : M4ConeInv F_cur st_u nv_u.toNat nc_w) :
    let new_l : BitVec 32 :=
      (((st_u.scratch.tarjan_mark[lit_k.toNat / 2]?.getD 0#32) - 1#32) <<< (1 : Nat)) |||
        (lit_k &&& 1#32)
    let st_u' : FullState :=
      { st_u with core := { st_u.core with tmp := st_u.core.tmp.set cnt.toNat new_l } }
    (cnt + 1#32).toNat = cnt.toNat + 1 ∧ st_u'.LengthsOk c ∧
    (∀ j < (cnt + 1#32).toNat, (st_u'.core.tmp[j]?.getD 0#32).toNat < 2 * nv_u.toNat) ∧
    (∀ i < (k + 1#32).toNat,
      let l := (s.core.arena[cr.toNat + 3 + i]?.getD 0#32).toNat
      s.core.vals[l]?.getD 0#8 = 0xFF#8 ∨
      l ∈ (st_u'.core.tmp.take (cnt + 1#32).toNat).map
        (fun x => FullSweepFwdSpecs.coneLift st_u'.scratch.work_stk1 x.toNat)) := by
  intro new_l st_u'
  have htmp_u := hlu.core_ok.tmp_len_arr
  have htmp_k : st_k.core.tmp.length = c.max_vars := htmpu_eq ▸ htmp_u
  have hcnt1 : (cnt + 1#32).toNat = cnt.toNat + 1 := by bv_omega
  have hk1 : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
  have hm1 : BitVec.ofNat 32 (ilv + 1) - 1#32 = BitVec.ofNat 32 ilv := by bv_omega
  have hnew_n : new_l.toNat = 2 * ilv + lit_k.toNat % 2 := by
    simp only [new_l, htlv_v, hm1]
    have := m4_bv32_shl1_or_and1 (BitVec.ofNat 32 ilv) lit_k
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : ilv < 2 ^ 32)] using this
  have hnew_lift : FullSweepFwdSpecs.coneLift st_u'.scratch.work_stk1 new_l.toNat = lit_k.toNat :=
    by
    rw [hnew_n]; exact coneLift_of_tmk_pair hwlv rfl
  have htake_u' : st_u'.core.tmp.take (cnt + 1#32).toNat =
      st_u.core.tmp.take cnt.toNat ++ [new_l] := by
    have hlen_tk : (st_u.core.tmp.take cnt.toNat).length = cnt.toNat := by simp [htmp_u]; omega
    rw [hcnt1]; dsimp only [st_u']; apply List.ext_getElem; · simp [htmp_u]; omega
    intro j hj1 _; have hj : j < cnt.toNat + 1 := by simp [htmp_u] at hj1; omega
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · rw [List.getElem_take, List.getElem_set_ne (by omega : cnt.toNat ≠ j),
        List.getElem_append_left (by omega), List.getElem_take]
    · simp [List.getElem_take, List.getElem_set_self, List.getElem_append_right, hlen_tk]
  refine ⟨hcnt1, ⟨{ hlu.core_ok with tmp_len_arr := by simp [st_u', htmp_u] }, hlu.scratch_ok⟩,
    fun j hj => ?_, fun i hi => ?_⟩
  · rw [hcnt1] at hj; rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · dsimp only [st_u']; rw [List.getElem?_set_ne (by omega : cnt.toNat ≠ j), htmpu_eq]
      exact Nat.lt_of_lt_of_le (hlts_k j hlt) (by omega)
    · dsimp only [st_u']; rw [List.getElem?_set_self (by omega), Option.getD_some]; omega
  · rw [hk1] at hi; rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
    · rcases hcov_k i hlt with hfals | hmem
      · exact Or.inl hfals
      · right; rw [htake_u', List.map_append]; apply List.mem_append_left
        rcases List.mem_map.mp hmem with ⟨x, hx, heq_l⟩
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
        have hj_cnt : j < cnt.toNat := by simp at hj; omega
        have hx_lt := hlts_k j hj_cnt
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hx_lt
        have hwk_eq_x : st_u.scratch.work_stk1[(st_k.core.tmp[j]'(by omega)).toNat / 2]? =
            st_k.scratch.work_stk1[(st_k.core.tmp[j]'(by omega)).toNat / 2]? :=
          hwku_eq _ (by omega)
        refine List.mem_map.mpr ⟨st_u.core.tmp[j]'(by omega), ?_, ?_⟩
        · have hmem' : (st_u.core.tmp.take cnt.toNat)[j]'(by simp [htmp_u]; omega) ∈
              st_u.core.tmp.take cnt.toNat := List.getElem_mem _
          simpa [List.getElem_take] using hmem'
        · rw [← heq_l]
          simp only [List.getElem_take, FullSweepFwdSpecs.coneLift, st_u', htmpu_eq, hwk_eq_x]
    · right; rw [htake_u', List.map_append]
      exact List.mem_append_right _ (by simp [hlit_ar, hnew_lift])

/-! ## 2. `full_m4_sweep_cone_wp` (`19/24`) -/

private theorem m4_of_ite_false {P A B : Prop} [Decidable P] (h : ¬ P) (hb : B) :
    if P then A else B := by
  cases ‹Decidable P› with
  | isTrue hp => exact absurd hp h
  | isFalse _ => exact hb

private theorem m4_cone_exit_post {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st_e : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {nv nc : BitVec 32} {m : Mem 64}
    (hdw : FullDenseInvW c F0 F_cur s) (hcap : k5MinScr ≤ c.scratch_cap)
    (hlen_e : st_e.LengthsOk c) (hag_e : AgreesExcept m4ConeMask s st_e)
    (hcone_e : M4ConeInv F_cur st_e nv.toNat nc.toNat)
    (hm : (K512MemA (c.pScratchBuf + BitVec.ofNat 64 2304 * 4)
        (st_e.scratch.scratch_buf.length - (k5Base + k5SlabFixed))
        (((((((k5StateOfScratch st_e.scratch.scratch_buf).putHdr .nv nv).putHdr .unass nv).putHdr
          .qlast (nv - 1#32)).putHdr .qsearch (nv - 1#32)).putHdr .qstamp nv).putArr .qnext
          (nv.toNat - 1) 0xFFFFFFFF#32) ⋆
        (FullK512Frame c st_e ⋆ R)) m)
    (hQ : ∀ (r : BitVec 64) (tmp' ws1' tmk' scr' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState :=
        { s with
          core := { s.core with tmp := tmp' }
          scratch :=
            { s.scratch with work_stk1 := ws1', tarjan_mark := tmk', scratch_buf := scr' } }
      let nv' := (r &&& 0xFFFF#64).toNat
      FullDenseInvW c F0 F_cur s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.core.vals = s.core.vals → s'.core.inconsistent = s.core.inconsistent →
      M4SweepConeOk F_cur s' nv' →
      (∀ v < s.core.cur_vars, tmk'[v]?.getD 0#32 ≠ 0#32 →
        ∃ i < nv', (ws1'[i]?.getD 0#32).toNat = v) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    Q (nv.setWidth 64 ||| (nc.setWidth 64 <<< (16 : Nat)), ()) m := by
  have hscr_e := hlen_e.scratch_ok.scratch_buf_len
  have h2304 : 2304 ≤ st_e.scratch.scratch_buf.length := by
    rw [hscr_e]; unfold k5MinScr at hcap; omega
  let acap := st_e.scratch.scratch_buf.length - (k5Base + k5SlabFixed)
  let ks_e := k5StateOfScratch st_e.scratch.scratch_buf
  have hnv1 : 1 ≤ nv.toNat := hcone_e.nv_ge1
  have hnv512 : nv.toNat ≤ 512 := hcone_e.nv_le512
  have hnc1536 : nc.toNat ≤ 1536 := hcone_e.nc_le
  obtain ⟨hinv_f, hnv_f⟩ := k5ShrinkNv_preserves_inv hcone_e.k5_inv.2.2 hnv1 hnv512
    hcone_e.k5_nv hcone_e.k5_trl hcone_e.k5_prop hcone_e.k5_lvl hcone_e.k5_na hcone_e.k5_bdd
  let ks_f := (((((ks_e.putHdr .nv nv).putHdr .unass nv).putHdr .qlast (nv - 1#32)).putHdr
    .qsearch (nv - 1#32)).putHdr .qstamp nv).putArr .qnext (nv.toNat - 1) 0xFFFFFFFF#32
  have hsh_f : ks_f.ShapesOk acap := hinv_f.shapes
  have hm_join : (FullMem c { st_e with scratch := { st_e.scratch with
      scratch_buf := st_e.scratch.scratch_buf.take 2304 ++ ks_f.toSlab } } ⋆ R) m := by
    obtain ⟨_, hkm⟩ := k5MemA_to_mem hm
    rw [k5Ptr_base_eq] at hkm
    exact fullMem_join_k5 h2304 hsh_f (sep_ac hkm)
  let scr_f := st_e.scratch.scratch_buf.take 2304 ++ ks_f.toSlab
  let s_f : FullState := { st_e with scratch := { st_e.scratch with scratch_buf := scr_f } }
  have hscr_f_len : scr_f.length = c.scratch_cap := by
    dsimp only [scr_f]
    rw [List.length_append, List.length_take_of_le h2304, ks_f.toSlab_length hsh_f]
    dsimp only [acap]; unfold k5Base k5SlabFixed; unfold k5MinScr at hcap; omega
  have hlen_f : s_f.LengthsOk c :=
    ⟨hlen_e.core_ok, { hlen_e.scratch_ok with scratch_buf_len := hscr_f_len }⟩
  have hag_f : AgreesExcept m4ConeMask s s_f := hag_e.update _ (fun _ => rfl)
  have hdw_f := m4ConeMask_preserves_dense hag_f hlen_f hdw
  have hof_f : k5StateOfScratch scr_f = ks_f := by
    unfold k5StateOfScratch; dsimp only [scr_f]
    rw [k5_slab_drop_exact _ _ (by rw [List.length_take_of_le h2304]; rfl)]
    exact K512State.ofSlab_toSlab hsh_f
  have hK_f : K512ScratchInv (ConeModelSet F_cur st_e.scratch.work_stk1 nv.toNat) scr_f := by
    refine ⟨by rw [hscr_f_len]; exact hcap, by rw [hscr_f_len]; exact c.hscr, ?_⟩
    rw [hof_f, show scr_f.length - (k5Base + k5SlabFixed) = acap by rw [hscr_f_len, ← hscr_e]]
    exact hinv_f
  have hpk : ((nv.setWidth 64 ||| (nc.setWidth 64 <<< (16 : Nat))) &&& 0xFFFF#64).toNat =
      nv.toNat := m4_pack_nv_nc nv nc hnv512 hnc1536
  have hQ' := hQ (nv.setWidth 64 ||| (nc.setWidth 64 <<< (16 : Nat)))
    st_e.core.tmp st_e.scratch.work_stk1 st_e.scratch.tarjan_mark scr_f m
  rw [← m4ConeMask_state_eq hag_f, hpk] at hQ'
  refine hQ' hdw_f (hag_e.get (·.core.cur_vars)) (hag_e.get (·.core.fuel))
    (hag_e.get (·.core.vals)) (hag_e.get (·.core.inconsistent))
    ⟨hnv1, hnv512, hcone_e.nv_le_cv, fun i hi => (hcone_e.fwd i hi).1, hK_f,
      by rw [hof_f, hnv_f, BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩
    (fun v hv hne => by
      have hcv_e := hag_e.get (·.core.cur_vars)
      rcases hcone_e.rev v (hcv_e.symm ▸ hv) with hz | ⟨i, hi, hwi, _⟩
      · exact absurd hz hne
      · exact ⟨i, hi, hwi⟩)
    hm_join

private theorem m4_cone_bin_tmp_prep {c : FullCfg} {F_cur : List (List Nat)}
    {st_a : FullState} {nv_a lit ot l0_b l1_b : BitVec 32}
    (hla : st_a.LengthsOk c) (htmp_a1 : 1 < st_a.core.tmp.length)
    (hl0_lt : l0_b.toNat < 2 * nv_a.toNat) (hl1_lt : l1_b.toNat < 2 * nv_a.toNat)
    (hlift0 : FullSweepFwdSpecs.coneLift st_a.scratch.work_stk1 l0_b.toNat = lit.toNat)
    (hlift1 : FullSweepFwdSpecs.coneLift st_a.scratch.work_stk1 l1_b.toNat = ot.toNat)
    (hent_bin : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat, ot.toNat])) :
    let st_ab : FullState :=
      { st_a with core := { st_a.core with tmp := (st_a.core.tmp.set 0 l0_b).set 1 l1_b } }
    st_ab.LengthsOk c ∧
    (∀ j < 2, (st_ab.core.tmp[j]?.getD 0#32).toNat < 2 * nv_a.toNat) ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause
      ((st_ab.core.tmp.take 2).map
        (fun x => FullSweepFwdSpecs.coneLift st_ab.scratch.work_stk1 x.toNat))) := by
  intro st_ab
  have htmp_a := hla.core_ok.tmp_len_arr
  refine ⟨⟨{ hla.core_ok with tmp_len_arr := by simp [st_ab, htmp_a] }, hla.scratch_ok⟩,
    fun j hj => ?_, ?_⟩
  · rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · dsimp only [st_ab]
      rw [List.getElem?_set_ne (by decide), List.getElem?_set_self (by omega), Option.getD_some]
      exact hl0_lt
    · dsimp only [st_ab]
      rw [List.getElem?_set_self (by simp; omega), Option.getD_some]
      exact hl1_lt
  · have htake : st_ab.core.tmp.take 2 = [l0_b, l1_b] := by
      dsimp only [st_ab]
      cases h_t : st_a.core.tmp with
      | nil => simp [h_t] at htmp_a1
      | cons x0 tl0 =>
        cases tl0 with
        | nil => simp [h_t] at htmp_a1
        | cons x1 tl1 => simp
    rw [htake]; simpa only [List.map_cons, List.map_nil, st_ab, hlift0, hlift1] using hent_bin

theorem full_m4_sweep_cone_wp (Γ : Env)
    (hInit : M4EnvSpec Γ "full_k512_init" k5InitSpec)
    (hAddCl : M4EnvSpec Γ "full_k512_add_clause" k5AddClauseSpec) :
    ∀ args m Q X, m4SweepConeSpec args m Q X →
      Func.wp Γ full_m4_sweep_cone_body args m Q X := by
  rintro ⟨h, root_v, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hdw, hcap, hroot, htmk, hm, hQ⟩
  have hlen := hdw.1; have hw := hdw.2.1; have hnd := hdw.2.2.2.1
  have hcl0 := hdw.2.2.2.2.2.1; have hdm := hdw.2.2.2.2.2.2
  have hcv_le := hlen.core_ok.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hdwatches : DenseWatchesInv F_cur s.core := by
    have hmw := hw.watches; unfold ModeWatchesInv at hmw; rwa [ite_eq_right hdm] at hmw
  unfold Func.wp full_m4_sweep_cone_body
  m4_steps
  m4_call hInit
  refine ⟨c, s, R, rfl, hlen, hm, ?_⟩
  dsimp only [Arg.val]
  have hcond : ¬ (c.scratch_cap < k5MinScr ∨ k5MaxV < (512#32 : BitVec 32).toNat) := by
    unfold k5MinScr at hcap; unfold k5MinScr k5MaxV; simp; omega
  refine m4_of_ite_false hcond ?_
  intro scr0 m0 hlen0 hpre0 hK0 hsy0 hnv0 hnc0 hlvl0 hpr0 htr0 hun0 hin0 hna0 hm0
  let s0 : FullState := { s with scratch := { s.scratch with scratch_buf := scr0 } }
  have hscr0 := hlen0.scratch_ok.scratch_buf_len
  have h0_wk0 : (BitVec.signExtend 64 (0 : BitVec 32)).toNat < s0.scratch.work_stk1.length := by
    rw [hlen0.scratch_ok.work_stk1_len,
      show (BitVec.signExtend 64 (0 : BitVec 32)).toNat = 0 from rfl]; omega
  let s0w : FullState :=
    { s0 with scratch := { s0.scratch with
        work_stk1 :=
          s0.scratch.work_stk1.set (BitVec.signExtend 64 (0 : BitVec 32)).toNat root_v } }
  have hrt_tm0 : (BitVec.setWidth 64 root_v).toNat < s0w.scratch.tarjan_mark.length := by
    rw [hlen0.scratch_ok.tarjan_mark_len, bv_c0_zext32_64]; omega
  obtain ⟨hlen1, hag1, hcone1⟩ :=
    m4ConeInv_init (F_cur := F_cur) hlen hroot htmk hscr0 hK0 hsy0 hnv0 hnc0 hlvl0 hpr0 htr0 hun0
      hin0 hna0
  m4_steps
  -- Outer BFS loop: `while (qi < nv && nc < 1536u)` with `(nv, nc, qi)`
  refine wp_loop_inv (ts := [i32, i32, i32])
    (fun (nv, nc, qi, ()) mo =>
      qi.toNat ≤ nv.toNat ∧ ∃ st : FullState,
        st.LengthsOk c ∧ AgreesExcept m4ConeMask s st ∧ M4ConeInv F_cur st nv.toNat nc.toNat ∧
        (FullMem c st ⋆ R) mo)
    (fun (_, _, qi, ()) _ => 512 - qi.toNat)
    (fun _ hJ_out => by
      m4_steps
      refine hJ_out (1#32, 0#32, 0#32, ()) _ ⟨Nat.zero_le _, _, hlen1, hag1, hcone1, ?_⟩
      rw [show (1 : BitVec 32) = 1#32 from rfl] at hm
      simpa only [s0w, s0, show (0#64 : BitVec 64).toNat = 0 from rfl,
        show (BitVec.signExtend 64 (0 : BitVec 32)).toNat = 0 from rfl,
        bv_c0_zext32_64] using hm)
    (fun _ (nv, nc, qi, ()) mo ⟨hqi_le, st, hlen_st, hag_st, hcone_st, hmo⟩ hJ_out => by
      clear hm m hcone1 hag1 hlen1 hrt_tm0 s0w h0_wk0 hlen0 hpre0 s0 hK0 hsy0 hnv0 hnc0 hlvl0 hpr0
        htr0 hun0 hin0 hna0 hscr0 scr0
      m4_to_group
      refine wp_join_group (ts := [])
        (fun () m_ex => ∃ st_e : FullState,
          st_e.LengthsOk c ∧ AgreesExcept m4ConeMask s st_e ∧
          M4ConeInv F_cur st_e nv.toNat nc.toNat ∧ (FullMem c st_e ⋆ R) m_ex)
        (fun _ () m_ex ⟨st_e, hlen_e, hag_e, hcone_e, hm_e⟩ => by
          -- Shrink `k512` `nv` from `512` down to `nv` using `K512MemATactics`!
          have hscr_e := hlen_e.scratch_ok.scratch_buf_len
          have h21792 : 21792 ≤ st_e.scratch.scratch_buf.length := by
            rw [hscr_e]; unfold k5MinScr at hcap; omega
          have h2304 : 2304 ≤ st_e.scratch.scratch_buf.length := by omega
          let acap := st_e.scratch.scratch_buf.length - (k5Base + k5SlabFixed)
          let ks_e := k5StateOfScratch st_e.scratch.scratch_buf
          have hsh_e : ks_e.ShapesOk acap := hcone_e.k5_inv.2.2.shapes
          have hnv1 : 1 ≤ nv.toNat := hcone_e.nv_ge1
          have hnv512 : nv.toNat ≤ 512 := hcone_e.nv_le512
          have hnc1536 : nc.toNat ≤ 1536 := hcone_e.nc_le
          obtain ⟨Rfr, hRfr⟩ : ∃ Rfr : Mem 64 → Prop, Rfr = (FullK512Frame c st_e ⋆ R) := ⟨_, rfl⟩
          have hm_ka : (K512MemA (c.pScratchBuf + BitVec.ofNat 64 2304 * 4) acap ks_e ⋆ Rfr) m_ex :=
            by
            rw [fullMem_eq_k5Frame h21792] at hm_e
            rw [hRfr, k5Ptr_base_eq]
            exact k5Mem_to_amem hsh_e (sep_ac hm_e)
          have hload_sb : loadVal m_ex i64 (c.hdr + 920) = some c.pScratchBuf := by
            rw [hRfr] at hm_ka
            exact K512MemATactics.load_k5fr_scratch_buf (R := K512MemA _ acap ks_e ⋆ R) (by ecancel)
          have hnv_pos : 0 < nv.toNat := by omega
          have hnv_sub512 : nv.toNat - 1 < 512 := by omega
          -- Step load of `h->scratch_buf` then use `K512MemATactics` for header & VMTF stores
          change wp _ _ _ _ _
          refine head_wp_load rfl hload_sb ?_
          open scoped K512MemATactics in c0_hsteps!
          rw [hRfr] at hm
          exact m4_cone_exit_post hdw hcap hlen_e hag_e hcone_e hm hQ)
        (fun _ hJ_ex => by
          clear hQ hInit
          m4_split
          · have hqi_lt : qi.toNat < nv.toNat := hc
            m4_split; rotate_left
            · m4_steps; exact hJ_ex () mo ⟨st, hlen_st, hag_st, hcone_st, hmo⟩
            have hnc_lt : nc.toNat < 1536 := hc
            have hwk_st := hlen_st.scratch_ok.work_stk1_len
            have htm_st := hlen_st.scratch_ok.tarjan_mark_len
            have hnv512_st := hcone_st.nv_le512
            have hqi_z : (BitVec.setWidth 64 qi).toNat = qi.toNat := bv_c0_zext32_64 qi
            have hqi_ws : (BitVec.setWidth 64 qi).toNat < st.scratch.work_stk1.length := by
              have := hcone_st.nv_le_cv; have := hlen_st.core_ok.cur_vars_le
              rw [hqi_z, hwk_st]; omega
            let cv := st.scratch.work_stk1[(BitVec.setWidth 64 qi).toNat]'hqi_ws
            have hwk_qi : st.scratch.work_stk1[qi.toNat]?.getD 0#32 = cv := by
              rw [List.getElem?_eq_getElem (by rw [hwk_st]; omega), Option.getD_some]
              simp [cv, hqi_z]
            have hcv_lt_s : cv.toNat < s.core.cur_vars := by
              have hf := (hcone_st.fwd qi.toNat hqi_lt).1
              rw [hwk_qi, hag_st.get (·.core.cur_vars)] at hf; exact hf
            have hcv_idx : st.scratch.tarjan_mark[cv.toNat]?.getD 0#32 =
                BitVec.ofNat 32 (qi.toNat + 1) := by
              have hf := (hcone_st.fwd qi.toNat hqi_lt).2
              rw [hwk_qi] at hf; exact hf
            have hcv_tmk : (BitVec.setWidth 64 cv).toNat < st.scratch.tarjan_mark.length := by
              rw [htm_st, bv_c0_zext32_64]; omega
            have hqi1 : (qi + 1#32).toNat = qi.toNat + 1 := m4_bv32_add1 (by omega)
            m4_steps
            have hmap_c : ((st.scratch.tarjan_mark[(BitVec.setWidth 64 cv).toNat]'hcv_tmk) - 1#32) =
                qi := by
              have htm_cv :
                  st.scratch.tarjan_mark[(BitVec.setWidth 64 cv).toNat]'hcv_tmk =
                    BitVec.ofNat 32 (qi.toNat + 1) := by
                rw [← Option.getD_some (a :=
                    st.scratch.tarjan_mark[(BitVec.setWidth 64 cv).toNat]'hcv_tmk),
                  ← List.getElem?_eq_getElem hcv_tmk, bv_c0_zext32_64, hcv_idx]
              rw [htm_cv]; exact m4_bv32_ofNat_add1_sub1 qi
            -- `pol` loop: `while (pol < 2u && nc < 1536u)`
            refine wp_loop_inv (ts := [i32, i32, i32])
              (fun (nv_p, nc_p, pol, ()) mp =>
                pol.toNat ≤ 2 ∧ nv.toNat ≤ nv_p.toNat ∧ ∃ st_p : FullState,
                  st_p.LengthsOk c ∧ AgreesExcept m4ConeMask s st_p ∧
                  M4ConeInv F_cur st_p nv_p.toNat nc_p.toNat ∧
                  st_p.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 (qi.toNat + 1) ∧
                  (st_p.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat = cv.toNat ∧
                  (FullMem c st_p ⋆ R) mp)
              (fun (_, _, pol, ()) _ => 2 - pol.toNat)
              (fun _ hJ_pol => by
                m4_steps
                exact hJ_pol (nv, nc, 0#32, ()) mo ⟨Nat.zero_le _, Nat.le_refl _, st,
                  hlen_st, hag_st, hcone_st, hcv_idx, by rw [hwk_qi], hmo⟩)
              (fun _ (nv_p, nc_p, pol, ()) mp
                  ⟨hpol_le, hnv_mono, st_p, hlen_p, hag_p, hcone_p, htmk_cv, hwk_cv,
                    hmp⟩ hJ_pol => by
                m4_split; rotate_left
                · m4_steps; exact hJ_out (nv_p, nc_p, qi + 1#32, ()) mp (by dsimp only; omega)
                    ⟨by omega, st_p, hlen_p, hag_p, hcone_p, hmp⟩
                have hpol_lt : pol.toNat < 2 := hc
                m4_split; rotate_left
                · m4_steps; exact hJ_out (nv_p, nc_p, qi + 1#32, ()) mp (by dsimp only; omega)
                    ⟨by omega, st_p, hlen_p, hag_p, hcone_p, hmp⟩
                have hncp_lt : nc_p.toNat < 1536 := hc
                let lit : BitVec 32 := (cv <<< (1 : Nat)) ||| pol
                have hlit_eq : lit.toNat = 2 * cv.toNat + pol.toNat :=
                  FullSweepVarHelpers.bv32_shl1_or_pol cv pol (by omega) hpol_lt
                have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by omega
                have hwvec_p := hlen_p.core_ok.wvec_len
                have h2lit : (BitVec.setWidth 64 lit <<< (1 : Nat)).toNat = 2 * lit.toNat :=
                  m4_bv64_shl1 _
                have h2lit1 : ((BitVec.setWidth 64 lit <<< (1 : Nat)) + 1#64).toNat =
                    2 * lit.toNat + 1 := m4_bv64_shl1_add1 _
                have hwvec_eq : st_p.core.wvec = s.core.wvec := hag_p.get (·.core.wvec)
                have hbounds := hdwatches.layout.bounds lit.toNat hlit_lt
                have hwlen_le := hlen.core_ok.wlen_le
                have hwcap_lt := c.hwcap; unfold dimacsBound at hwcap_lt
                have h2l_bd : (BitVec.setWidth 64 ((cv <<< (1 : Nat)) ||| pol) <<<
                    (OfNat.ofNat 1 : Nat)).toNat < st_p.core.wvec.length := by
                  rw [hwvec_p, h2lit]; omega
                have h2l1_bd : ((BitVec.setWidth 64 ((cv <<< (1 : Nat)) ||| pol) <<<
                    (OfNat.ofNat 1 : Nat)) + 1#64).toNat < st_p.core.wvec.length := by
                  rw [hwvec_p, h2lit1]; omega
                let wOff := (st_p.core.wvec[(BitVec.setWidth 64 lit <<< (1 : Nat)).toNat]'(
                  by rw [hwvec_p, h2lit]; omega)).setWidth 64
                let wSz := (st_p.core.wvec[((BitVec.setWidth 64 lit <<< (1 : Nat)) + 1#64).toNat]'(
                  by rw [hwvec_p, h2lit1]; omega)).setWidth 64
                have hwOff_n : wOff.toNat = fullWatchOffCore s.core lit.toNat := by
                  dsimp only [wOff]; unfold fullWatchOffCore
                  rw [bv_c0_zext32_64, List.getElem?_eq_getElem (by rw [← hwvec_eq]; omega),
                    Option.getD_some]
                  simp [hwvec_eq, h2lit]
                have hwSz_n : wSz.toNat = fullWatchSizeCore s.core lit.toNat := by
                  dsimp only [wSz]; unfold fullWatchSizeCore
                  rw [bv_c0_zext32_64, List.getElem?_eq_getElem (by rw [← hwvec_eq]; omega),
                    Option.getD_some]
                  simp [hwvec_eq, h2lit1]
                obtain ⟨wEnd, hwEnd⟩ : ∃ wEnd : BitVec 64, wEnd = wOff + wSz := ⟨_, rfl⟩
                have hend_eq : wEnd.toNat =
                    fullWatchOffCore s.core lit.toNat + fullWatchSizeCore s.core lit.toNat := by
                  rw [hwEnd, BitVec.toNat_add, hwOff_n, hwSz_n, Nat.mod_eq_of_lt (by omega)]
                have hpol1 : (pol + 1#32).toNat = pol.toNat + 1 :=
                  m4_bv32_add1 (Nat.lt_trans hpol_lt (by decide))
                m4_to_group
                refine wp_join_group (ts := [i32, i32, i64])
                  (fun (nv_e, nc_e, _, ()) m_we =>
                    nv.toNat ≤ nv_e.toNat ∧ ∃ st_we : FullState,
                      st_we.LengthsOk c ∧ AgreesExcept m4ConeMask s st_we ∧
                      M4ConeInv F_cur st_we nv_e.toNat nc_e.toNat ∧
                      st_we.scratch.tarjan_mark[cv.toNat]?.getD 0#32 =
                        BitVec.ofNat 32 (qi.toNat + 1) ∧
                      (st_we.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat = cv.toNat ∧
                      (FullMem c st_we ⋆ R) m_we)
                  (fun _ (nv_e, nc_e, _, ()) m_we
                      ⟨hnve, st_we, hl_e, ha_e, hc_e, ht_e, hw_e, hm_e⟩ => by
                    m4_steps
                    exact hJ_pol (nv_e, nc_e, pol + 1#32, ()) m_we (by dsimp only; omega)
                      ⟨by omega, hnve, st_we, hl_e, ha_e, hc_e, ht_e, hw_e, hm_e⟩)
                  (fun _ hJ_we => by
                    m4_steps
                    -- Watch loop: `while (p < end && nc < 1536u)` with `(nv, nc, p)`
                    refine wp_loop_inv (ts := [i32, i32, i64])
                      (fun (nv_w, nc_w, p, ()) mw =>
                        p.toNat ≤ wEnd.toNat ∧ nv.toNat ≤ nv_w.toNat ∧
                        DenseWatchSliceOk F_cur s.core lit.toNat p.toNat (wEnd.toNat - p.toNat) ∧
                        ∃ st_w : FullState,
                          st_w.LengthsOk c ∧ AgreesExcept m4ConeMask s st_w ∧
                          M4ConeInv F_cur st_w nv_w.toNat nc_w.toNat ∧
                          st_w.scratch.tarjan_mark[cv.toNat]?.getD 0#32 =
                            BitVec.ofNat 32 (qi.toNat + 1) ∧
                          (st_w.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat = cv.toNat ∧
                          (FullMem c st_w ⋆ R) mw)
                      (fun (_, _, p, ()) _ => wEnd.toNat - p.toNat)
                      (fun _ hJ_w => by
                        m4_steps
                        refine hJ_w (nv_p, nc_p, wOff, ()) mp ⟨by omega, hnv_mono, ?_,
                          st_p, hlen_p, hag_p, hcone_p, htmk_cv, hwk_cv, hmp⟩
                        rw [hwOff_n, show wEnd.toNat - fullWatchOffCore s.core lit.toNat =
                          fullWatchSizeCore s.core lit.toNat by omega]
                        exact hdwatches.slices lit.toNat hlit_lt)
                      (fun J_w (nv_w, nc_w, p, ()) mw
                          ⟨hp_le, hnv_w_mono, hslice, st_w, hlen_w, hag_w, hcone_w,
                           htmk_w, hwk_w, hmw⟩ hJ_w => by
                        clear hJ_out hJ_ex hJ_pol hmp hlen_p hag_p hcone_p htmk_cv hwk_cv hmo
                          hlen_st hag_st hcone_st hwk_qi hcv_idx
                        m4_split; rotate_left
                        · m4_steps; exact hJ_we (nv_w, nc_w, p, ()) mw
                            ⟨hnv_w_mono, st_w, hlen_w, hag_w, hcone_w, htmk_w, hwk_w, hmw⟩
                        have hcv_qi : ∀ (h : qi.toNat < st.scratch.work_stk1.length),
                            st.scratch.work_stk1[qi.toNat]'h = cv := fun h =>
                          Option.some.inj (by
                            dsimp only [cv]
                            rw [← List.getElem?_eq_getElem h,
                              ← List.getElem?_eq_getElem hqi_ws, hqi_z])
                        have h2l_mod : (2 * lit.toNat) % 2 ^ 64 =
                            (BitVec.setWidth 64 lit <<< (1 : Nat)).toNat := by
                          rw [h2lit, Nat.mod_eq_of_lt (by omega)]
                        have h2l1_mod : (2 * lit.toNat + 1) % 2 ^ 64 =
                            ((BitVec.setWidth 64 lit <<< (1 : Nat)) + 1#64).toNat := by
                          rw [h2lit1, Nat.mod_eq_of_lt (by omega)]
                        have hwv0_eq : ∀ (h : (2 * lit.toNat) % 2 ^ 64 < st_p.core.wvec.length),
                            st_p.core.wvec[(2 * lit.toNat) % 2 ^ 64]'h =
                              st_p.core.wvec[(BitVec.setWidth 64 lit <<< (1 : Nat)).toNat]'
                                h2l_bd := fun h => Option.some.inj (by
                          rw [← List.getElem?_eq_getElem h,
                            ← List.getElem?_eq_getElem h2l_bd, h2l_mod])
                        have hwv1_eq :
                            ∀ (h : (2 * lit.toNat + BitVec.toNat 1) % 2 ^ 64 <
                                st_p.core.wvec.length),
                              st_p.core.wvec[(2 * lit.toNat + BitVec.toNat 1) % 2 ^ 64]'h =
                                st_p.core.wvec[((BitVec.setWidth 64 lit <<< (1 : Nat)) +
                                    1#64).toNat]'h2l1_bd := fun h => Option.some.inj (by
                          rw [← List.getElem?_eq_getElem h, ← List.getElem?_eq_getElem h2l1_bd,
                            show BitVec.toNat (1 : BitVec 64) = 1 from rfl, h2l1_mod])
                        have hshl_1 : ∀ x : BitVec 32,
                            (x <<< (BitVec.toNat (1 : BitVec 32) % 32)) = x <<< (1 : Nat) :=
                          fun _ => rfl
                        have hp_lt : p.toNat < wEnd.toNat := by
                          simp only [hcv_qi] at hc
                          change BitVec.toNat p < _ at hc
                          rw [hwv0_eq, hwv1_eq] at hc
                          change BitVec.toNat p < (wOff.toNat + wSz.toNat) % 2 ^ 64 at hc
                          simpa only [hwEnd, BitVec.toNat_add] using hc
                        m4_split; rotate_left
                        · m4_steps; exact hJ_we (nv_w, nc_w, p, ()) mw
                            ⟨hnv_w_mono, st_w, hlen_w, hag_w, hcone_w, htmk_w, hwk_w, hmw⟩
                        have hncw_lt : nc_w.toNat < 1536 := hc
                        have hwstk_eq : st_w.core.wstk = s.core.wstk := hag_w.get (·.core.wstk)
                        have hcv_w : st_w.core.cur_vars = s.core.cur_vars :=
                          hag_w.get (·.core.cur_vars)
                        have hwstk_w := hlen_w.core_ok.wstk_len_arr
                        have hp1 : (p + 1#64).toNat = p.toNat + 1 := m4_bv64_add1 (by omega)
                        let w0 := st_w.core.wstk[p.toNat]'(by omega)
                        have hw0_s : s.core.wstk[p.toNat]? = some w0 := by
                          rw [List.getElem?_eq_getElem (by rw [← hwstk_eq]; omega)]
                          exact congrArg some (by simp [w0, hwstk_eq])
                        m4_split
                        · -- Binary watch branch
                          have hbin : (w0 &&& 0x80000000#32) ≠ 0#32 := by
                            dsimp only [w0]; exact hc
                          obtain ⟨_, hot_lt, hent_bin, hslice1⟩ :=
                            denseWatchSlice_step_bin hslice (by omega) hw0_s hbin
                          let ot : BitVec 32 := w0 &&& 0x7FFFFFFF#32
                          have hot_lt' : ot.toNat < 2 * s.core.cur_vars := hot_lt
                          let ov : BitVec 32 := ot >>> (1 : Nat)
                          have hov_eq : ov.toNat = ot.toNat / 2 := m4_bv32_shr1_toNat ot
                          have hov_lt : ov.toNat < s.core.cur_vars := by omega
                          have hvals_w := hlen_w.core_ok.vals_len
                          have htm_w := hlen_w.scratch_ok.tarjan_mark_len
                          have hwk_w_len := hlen_w.scratch_ok.work_stk1_len
                          have hot_vals : (BitVec.setWidth 64 ot).toNat < st_w.core.vals.length :=
                            by
                            rw [hvals_w, bv_c0_zext32_64]; omega
                          m4_to_group
                          refine wp_join_group (ts := [i32, i32])
                            (fun (nv_b, nc_b, ()) m_b =>
                              nv.toNat ≤ nv_b.toNat ∧ ∃ st_b : FullState,
                                st_b.LengthsOk c ∧ AgreesExcept m4ConeMask s st_b ∧
                                M4ConeInv F_cur st_b nv_b.toNat nc_b.toNat ∧
                                st_b.scratch.tarjan_mark[cv.toNat]?.getD 0#32 =
                                  BitVec.ofNat 32 (qi.toNat + 1) ∧
                                (st_b.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat = cv.toNat ∧
                                (FullMem c st_b ⋆ R) m_b)
                            (fun _ (nv_b, nc_b, ()) m_b
                                ⟨hnvb, st_b, hlb, hab, hcb, htb, hwb, hmb⟩ => by
                              m4_steps
                              exact hJ_w (nv_b, nc_b, p + 1#64, ()) m_b (by dsimp only; omega)
                                ⟨by omega, hnvb, by rw [hp1, show wEnd.toNat - (p.toNat + 1) =
                                    wEnd.toNat - p.toNat - 1 by omega]; exact hslice1,
                                  st_b, hlb, hab, hcb, htb, hwb, hmb⟩)
                            (fun _ hJ_bin => by
                              -- `ov != cv`
                              m4_split; rotate_left
                              · m4_steps; exact hJ_bin (nv_w, nc_w, ()) mw
                                  ⟨hnv_w_mono, st_w, hlen_w, hag_w, hcone_w, htmk_w, hwk_w, hmw⟩
                              -- `vals[ot] == 0`
                              m4_split; rotate_left
                              · m4_steps; exact hJ_bin (nv_w, nc_w, ()) mw
                                  ⟨hnv_w_mono, st_w, hlen_w, hag_w, hcone_w, htmk_w, hwk_w, hmw⟩
                              have hov_tmk : (BitVec.setWidth 64 ov).toNat <
                                  st_w.scratch.tarjan_mark.length := by
                                rw [htm_w, bv_c0_zext32_64]; omega
                              have htm_w_idx :
                                  ∀ {j : Nat} (hj : j < st_w.scratch.tarjan_mark.length),
                                    j = ov.toNat →
                                    st_w.scratch.tarjan_mark[j]'hj =
                                      st_w.scratch.tarjan_mark[ov.toNat]'(by omega) :=
                                fun _ hij => Option.some.inj (by subst hij; rfl)
                              m4_to_group
                              refine wp_join_group (ts := [])
                                (fun () m_or => m_or = mw ∧
                                  (st_w.scratch.tarjan_mark[ov.toNat]?.getD 0#32 ≠ 0#32 ∨
                                    nv_w.toNat < 512))
                                (fun _ () m_or ⟨hmor, hor⟩ => by
                                  subst m_or
                                  refine wp_join_group (ts := [i32])
                                    (fun (nv_a, ()) m_a =>
                                      nv.toNat ≤ nv_a.toNat ∧ ∃ st_a : FullState,
                                        st_a.LengthsOk c ∧ AgreesExcept m4ConeMask s st_a ∧
                                        M4ConeInv F_cur st_a nv_a.toNat nc_w.toNat ∧
                                        st_a.scratch.tarjan_mark[cv.toNat]?.getD 0#32 =
                                          BitVec.ofNat 32 (qi.toNat + 1) ∧
                                        (st_a.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat =
                                          cv.toNat ∧
                                        st_a.scratch.tarjan_mark[ov.toNat]?.getD 0#32 ≠ 0#32 ∧
                                        (FullMem c st_a ⋆ R) m_a)
                                    (fun _ (nv_a, ()) m_a
                                        ⟨hnva, st_a, hla, haa, hca, htca, hwca, htoa, hma⟩ => by
                                      m4_to_group; refine wp_unroll_group fun _ _ => ?_
                                      m4_split; rotate_left
                                      · m4_steps; exact hJ_bin (nv_a, nc_w, ()) m_a
                                          ⟨hnva, st_a, hla, haa, hca, htca, hwca, hma⟩
                                      have htm_a := hla.scratch_ok.tarjan_mark_len
                                      have htmp_a := hla.core_ok.tmp_len_arr
                                      have hcv_a := haa.get (·.core.cur_vars)
                                      rcases hca.rev ov.toNat (by rw [hcv_a]; exact hov_lt) with
                                        hz | ⟨iov, hiov, hwov, htov⟩
                                      · exact absurd hz htoa
                                      obtain ⟨hl0_lt, hl1_lt, hlift0, hlift1⟩ :=
                                        m4_cone_bin_lits_ok (Nat.lt_of_lt_of_le hqi_lt hnva)
                                          hca.nv_le512 hpol_lt hlit_eq hov_eq hiov htca hwca
                                          htov hwov
                                      have hcv_tm : cv.toNat < st_a.scratch.tarjan_mark.length := by
                                        omega
                                      have hov_tm : ov.toNat < st_a.scratch.tarjan_mark.length := by
                                        omega
                                      rw [List.getElem?_eq_getElem hcv_tm, Option.getD_some]
                                        at hl0_lt hlift0
                                      rw [List.getElem?_eq_getElem hov_tm, Option.getD_some]
                                        at hl1_lt hlift1
                                      have htm_cv_s_eq_a :
                                          st.scratch.tarjan_mark[
                                              (BitVec.setWidth 64 cv).toNat]'hcv_tmk =
                                            st_a.scratch.tarjan_mark[cv.toNat]'hcv_tm := by
                                        have hs1 : st.scratch.tarjan_mark[
                                            (BitVec.setWidth 64 cv).toNat]'hcv_tmk = qi + 1#32 :=
                                          m4_bv32_sub1_of_eq _ _ hmap_c
                                        have ha : st_a.scratch.tarjan_mark[cv.toNat]'hcv_tm =
                                            BitVec.ofNat 32 (qi.toNat + 1) := by
                                          simpa only [List.getElem?_eq_getElem hcv_tm,
                                            Option.getD_some] using htca
                                        rw [hs1, ha]
                                        exact BitVec.eq_of_toNat_eq (by
                                          rw [hqi1, BitVec.toNat_ofNat,
                                            Nat.mod_eq_of_lt (by omega)])
                                      let l0_b :=
                                        ((st.scratch.tarjan_mark[
                                            (BitVec.setWidth 64 cv).toNat]'hcv_tmk - 1#32) <<<
                                          (1 : Nat)) ||| pol
                                      have hl0_lt' : l0_b.toNat < 2 * nv_a.toNat := by
                                        dsimp only [l0_b]; rw [htm_cv_s_eq_a]; exact hl0_lt
                                      have hlift0' :
                                          FullSweepFwdSpecs.coneLift st_a.scratch.work_stk1
                                            l0_b.toNat = lit.toNat := by
                                        dsimp only [l0_b]; rw [htm_cv_s_eq_a]; exact hlift0
                                      have htm_a_ov : (BitVec.setWidth 64 ov).toNat <
                                          st_a.scratch.tarjan_mark.length := by
                                        rw [htm_a, bv_c0_zext32_64]; omega
                                      let l1_b :=
                                        ((st_a.scratch.tarjan_mark[(BitVec.setWidth 64 ov).toNat]'
                                            htm_a_ov - 1#32) <<< (1 : Nat)) ||| (ot &&& 1#32)
                                      have htm_a_ov_eq :
                                          st_a.scratch.tarjan_mark[(BitVec.setWidth 64 ov).toNat]'
                                              htm_a_ov =
                                            st_a.scratch.tarjan_mark[ov.toNat]'hov_tm := by
                                        simp only [bv_c0_zext32_64]
                                      have htmp_a1 : 1 < st_a.core.tmp.length := by
                                        have := hca.nv_le_cv; have := hla.core_ok.cur_vars_le
                                        have hne_cv_ov : cv.toNat ≠ ov.toNat := by
                                          intro heq
                                          have : ov = cv := BitVec.eq_of_toNat_eq heq.symm
                                          exact absurd this ‹_›
                                        omega
                                      have h0_tmp_a : (0#64 : BitVec 64).toNat <
                                          st_a.core.tmp.length := by
                                        rw [show (0#64 : BitVec 64).toNat = 0 from rfl]; omega
                                      have h1_tmp_a : (1#64 : BitVec 64).toNat <
                                          st_a.core.tmp.length := by
                                        rw [show (1#64 : BitVec 64).toNat = 1 from rfl]; omega
                                      clear hJ_w hslice hmw hag_w hcone_w htmk_w hwk_w
                                        hw0_s hbin hov_tmk htm_w_idx hor
                                      m4_steps
                                      let st_ab : FullState :=
                                        { st_a with core := { st_a.core with
                                          tmp := (st_a.core.tmp.set 0 l0_b).set 1 l1_b } }
                                      obtain ⟨hlen_ab, hlts_ab, hent_ab⟩ :=
                                        m4_cone_bin_tmp_prep hla htmp_a1 hl0_lt'
                                          (by simpa only [l1_b, htm_a_ov_eq] using hl1_lt) hlift0'
                                          (by simpa only [l1_b, htm_a_ov_eq] using hlift1) hent_bin
                                      have hm_ab : (FullMem c st_ab ⋆ R) m := by
                                        dsimp only [st_ab, l0_b, l1_b, ov, ot, w0, cv]
                                        exact hm
                                      refine m4_cone_call_add_clause hAddCl (aSz := Arg.imm 2)
                                        (sz := 2#32) rfl
                                        hlen_ab (haa.update _ fun _ => rfl)
                                        (m4ConeInv_tmp_irrel hca) hncw_lt (Nat.le_refl 2)
                                        (by decide)
                                        (by rw [show (2#32 : BitVec 32).toNat = 2 from rfl,
                                              hlen_ab.core_ok.tmp_len_arr, ← htmp_a]; exact htmp_a1)
                                        hlts_ab hent_ab hm_ab
                                        (fun ok st' m' hl' ha' hc' ht' hw' hm' => by
                                          m4_split
                                          · m4_steps
                                            exact hJ_bin (nv_a, nc_w + 1#32, ()) m'
                                              ⟨hnva, st', hl', ha',
                                               by simpa only [hc, ↓reduceIte] using hc',
                                               ht' ▸ htca, hw' ▸ hwca, hm'⟩
                                          · m4_steps
                                            exact hJ_bin (nv_a, nc_w, ()) m'
                                              ⟨hnva, st', hl', ha',
                                               by simpa only [hc, Bool.false_eq_true, ↓reduceIte]
                                                 using hc',
                                               ht' ▸ htca, hw' ▸ hwca, hm'⟩))
                                    (fun _ hJ_a => by
                                      m4_split
                                      · have hmiss : st_w.scratch.tarjan_mark[ov.toNat]?.getD 0#32 =
                                            0#32 := by
                                          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                                          rw [htm_w_idx _ (by rw [hov_eq]; rfl)] at hc; exact hc
                                        have hnv_lt512_w : nv_w.toNat < 512 :=
                                          hor.elim (absurd hmiss) id
                                        have hnv_w_lt : nv_w.toNat < s.core.cur_vars := by
                                          rw [← hcv_w]
                                          exact (m4ConeInv_push_var hlen_w hcone_w hnv_lt512_w
                                            (by rw [hcv_w]; exact hov_lt) hmiss).1
                                        have hnv1 : (nv_w + 1#32).toNat = nv_w.toNat + 1 :=
                                          m4_bv32_add1 (Nat.lt_trans hnv_lt512_w (by decide))
                                        have hnv_ws : (BitVec.setWidth 64 ((nv_w + 1#32) -
                                            1#32)).toNat < st_w.scratch.work_stk1.length := by
                                          rw [hwk_w_len, bv_c0_zext32_64,
                                            m4_bv32_add1_sub1_eq nv_w]; omega
                                        m4_steps
                                        have hpush := m4ConeInv_push_var hlen_w hcone_w hnv_lt512_w
                                          (by rw [hcv_w]; exact hov_lt) hmiss
                                        let st_a : FullState :=
                                          { st_w with scratch :=
                                            { st_w.scratch with
                                              tarjan_mark := st_w.scratch.tarjan_mark.set ov.toNat
                                                (nv_w + 1#32)
                                              work_stk1 := st_w.scratch.work_stk1.set nv_w.toNat
                                                ov } }
                                        have hne_cv : cv.toNat ≠ ov.toNat := fun heq => by
                                          rw [← heq, htmk_w] at hmiss
                                          have := congrArg BitVec.toNat hmiss
                                          simp [BitVec.toNat_ofNat] at this; omega
                                        have hne_nv_qi : nv_w.toNat ≠ qi.toNat := by omega
                                        have hm_a : (FullMem c st_a ⋆ R) m := by
                                          have h2 := m4_bv32_add1_sub1_toNat nv_w
                                          have h3 : (nv_w + 1 : BitVec 32) = nv_w + 1#32 := rfl
                                          have hw0' : (st_w.core.wstk[p.toNat]'(by omega) &&&
                                              2147483647) >>> OfNat.ofNat 1 = ov := rfl
                                          dsimp only [LeanQbe.T.lift2, Arg.val_var, Arg.val_imm]
                                            at hm
                                          rw [bv_c0_zext32_64, h2, hw0', bv_c0_zext32_64, h3] at hm
                                          exact hm
                                        exact hJ_a (nv_w + 1#32, ()) m
                                          ⟨by omega, st_a,
                                            ⟨hlen_w.core_ok, { hlen_w.scratch_ok with
                                              tarjan_mark_len := by simp [st_a, htm_w]
                                              work_stk1_len := by simp [st_a, hwk_w_len] }⟩,
                                            hag_w.update _ (fun _ => rfl),
                                            by rw [hnv1]; simpa [st_a, m4_bv32_ofNat_add1 nv_w]
                                              using hpush.2,
                                            by dsimp only [st_a]
                                               rw [List.getElem?_set_ne (Ne.symm hne_cv)]
                                               exact htmk_w,
                                            by dsimp only [st_a]
                                               rw [List.getElem?_set_ne hne_nv_qi]
                                               exact hwk_w,
                                            by dsimp only [st_a]
                                               rw [List.getElem?_set_self (by omega),
                                                 Option.getD_some]
                                               intro h; have := congrArg BitVec.toNat h
                                               simp [hnv1] at this,
                                            hm_a⟩
                                      · have hne_ov :
                                            st_w.scratch.tarjan_mark[ov.toNat]?.getD 0#32 ≠
                                              0#32 := by
                                          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                                          rw [htm_w_idx _ (by rw [hov_eq]; rfl)] at hc; exact hc
                                        m4_steps
                                        exact hJ_a (nv_w, ()) mw
                                          ⟨hnv_w_mono, st_w, hlen_w, hag_w, hcone_w, htmk_w, hwk_w,
                                           hne_ov, hmw⟩))
                                (fun _ hJ_or => by
                                  m4_split
                                  · have hne :
                                        st_w.scratch.tarjan_mark[ov.toNat]?.getD 0#32 ≠ 0#32 := by
                                      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                                      rw [htm_w_idx _ (by rw [hov_eq]; rfl)] at hc; exact hc
                                    m4_steps; exact hJ_or () mw ⟨rfl, Or.inl hne⟩
                                  · m4_split
                                    · have hlt : nv_w.toNat < 512 := hc
                                      m4_steps; exact hJ_or () mw ⟨rfl, Or.inr hlt⟩
                                    · m4_steps; exact hJ_bin (nv_w, nc_w, ()) mw
                                        ⟨hnv_w_mono, st_w, hlen_w, hag_w, hcone_w, htmk_w,
                                         hwk_w, hmw⟩))
                        · -- Occurrence watch branch
                          have hocc : (w0 &&& 0x80000000#32) = 0#32 := by
                            dsimp only [w0]; exact hc
                          obtain ⟨hrem2, _, cr, hcr_s, hcr_lt, hcr_ref, hslice2⟩ :=
                            denseWatchSlice_step_occ hslice (by omega) hw0_s hocc
                          m4_split
                          · exfalso
                            simp only [hcv_qi] at hc
                            rw [hwv0_eq, hwv1_eq] at hc
                            have hge : wEnd.toNat ≤ (p + 1#64).toNat := by
                              rw [hwEnd, BitVec.toNat_add, BitVec.toNat_add]; exact hc
                            omega
                          have hp2 : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by
                            rw [m4_bv64_add1 (by rw [hp1]; omega), hp1]
                          clear hslice hw0_s hocc hwv0_eq hwv1_eq h2l_mod h2l1_mod hcv_qi
                            hshl_1 hdwatches
                          have har_w := hlen_w.core_ok.arena_len_arr
                          have har_s := hlen.core_ok.arena_len_arr
                          have hcr_wf := hw.arena.refs_wf cr.toNat hcr_ref
                          have hacap_lt := c.harena; unfold dimacsBound at hacap_lt
                          have hal_le := hlen.core_ok.arena_len_le
                          have hcr_eq : st_w.core.wstk[p.toNat + 1]'(by omega) = cr := by
                            rw [List.getElem?_eq_getElem (by rw [← hwstk_eq]; omega)] at hcr_s
                            simpa [hwstk_eq] using Option.some.inj hcr_s
                          have hcr_idx :
                              ∀ {j : Nat} (hj : j < st_w.core.wstk.length), j = p.toNat + 1 →
                                st_w.core.wstk[j]'hj = cr := fun _ hij =>
                            Option.some.inj (by subst hij; exact congrArg some hcr_eq)
                          have hcr2_lt : (BitVec.setWidth 64 cr + 2#64).toNat = cr.toNat + 2 := by
                            simp only [BitVec.toNat_add, bv_c0_zext32_64,
                              show (2#64 : BitVec 64).toNat = 2 from rfl]; omega
                          have har_eq : st_w.core.arena = s.core.arena := hag_w.get (·.core.arena)
                          have har_cr_bd : cr.toNat < st_w.core.arena.length := by
                            rw [har_eq, har_s]; omega
                          have har_cr2_bd : (BitVec.setWidth 64 cr + 2#64).toNat <
                              st_w.core.arena.length := by
                            rw [har_eq, har_s, hcr2_lt]; omega
                          let sz : BitVec 32 :=
                            st_w.core.arena[(BitVec.setWidth 64 cr + 2#64).toNat]'har_cr2_bd
                          have har_cr_idx :
                              ∀ {k : Nat} (hk : k < st_w.core.arena.length), k = cr.toNat →
                                st_w.core.arena[k]'hk = st_w.core.arena[cr.toNat]'har_cr_bd :=
                            fun _ hkeq => Option.some.inj (by subst hkeq; rfl)
                          have har_sz_idx :
                              ∀ {k : Nat} (hk : k < st_w.core.arena.length),
                                k = (BitVec.setWidth 64 cr + 2#64).toNat →
                                st_w.core.arena[k]'hk = sz :=
                            fun _ hkeq => Option.some.inj (by subst hkeq; rfl)
                          have hsz_core : sz.toNat = fullArenaClauseSizeCore s.core cr.toNat := by
                            unfold fullArenaClauseSizeCore; dsimp only [sz]
                            rw [List.getElem?_eq_getElem (by rw [har_s]; omega), Option.getD_some]
                            simp only [har_eq, hcr2_lt]
                          have hstep_occ : ∀ (nv_x nc_x : BitVec 32) (st_x : FullState)
                              (mx : Mem 64),
                              nv.toNat ≤ nv_x.toNat → st_x.LengthsOk c →
                              AgreesExcept m4ConeMask s st_x →
                              M4ConeInv F_cur st_x nv_x.toNat nc_x.toNat →
                              st_x.scratch.tarjan_mark[cv.toNat]?.getD 0#32 =
                                BitVec.ofNat 32 (qi.toNat + 1) →
                              (st_x.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat = cv.toNat →
                              (FullMem c st_x ⋆ R) mx →
                              J_w (nv_x, nc_x, p + 1#64 + 1#64, ()) mx :=
                            fun nv_x nc_x st_x mx hnvx hlx hax hcx htx hwx hmx =>
                              hJ_w (nv_x, nc_x, p + 1#64 + 1#64, ()) mx (by dsimp only; omega)
                                ⟨by omega, hnvx, by rw [hp2, show wEnd.toNat - (p.toNat + 2) =
                                    wEnd.toNat - p.toNat - 2 by omega]; exact hslice2,
                                  st_x, hlx, hax, hcx, htx, hwx, hmx⟩
                          have hocc_done : J_w (nv_w, nc_w, p + 1#64 + 1#64, ()) mw :=
                            hstep_occ nv_w nc_w st_w mw hnv_w_mono hlen_w hag_w hcone_w
                              htmk_w hwk_w hmw
                          have hp_mod :
                              (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = p.toNat + 1 := by
                            rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
                              Nat.mod_eq_of_lt (by omega)]
                          have hp1_wstk : (p + 1#64).toNat < st_w.core.wstk.length := by omega
                          have hcr_w_p1 : st_w.core.wstk[(p + 1#64).toNat]'hp1_wstk = cr :=
                            hcr_idx _ hp1
                          have har_cr_bd' :
                              (BitVec.setWidth 64
                                (st_w.core.wstk[(p + 1#64).toNat]'hp1_wstk)).toNat <
                                st_w.core.arena.length := by
                            rw [hcr_w_p1, bv_c0_zext32_64]; exact har_cr_bd
                          have har_cr2_bd' :
                              (BitVec.setWidth 64
                                (st_w.core.wstk[(p + 1#64).toNat]'hp1_wstk) + 2#64).toNat <
                                st_w.core.arena.length := by
                            rw [hcr_w_p1]; exact har_cr2_bd
                          m4_split; · m4_steps; exact hocc_done
                          have hgr0 : (st_w.core.arena[cr.toNat]'(by omega) &&&
                              (0x00080000#32 ||| 0x00400000#32)) = 0#32 := by
                            rw [har_cr_idx] at hc
                            · exact hc
                            · rw [hcr_idx _ hp_mod]
                          m4_split; · m4_steps; exact hocc_done
                          have hsz_ge3 : 3 ≤ sz.toNat := by
                            rw [har_sz_idx] at hc
                            · exact Nat.le_of_not_lt hc
                            · rw [hcr_idx]
                              · rw [hcr2_lt, show BitVec.toNat (2 : BitVec 64) = 2 from rfl,
                                  Nat.mod_eq_of_lt (by omega)]
                              · exact hp_mod
                          m4_split; · m4_steps; exact hocc_done
                          have hsz_le12 : sz.toNat ≤ 12 := by
                            rw [har_sz_idx] at hc
                            · have h8 : sz.toNat ≤ 8 := Nat.le_of_not_lt hc; omega
                            · rw [hcr_idx]
                              · rw [hcr2_lt, show BitVec.toNat (2 : BitVec 64) = 2 from rfl,
                                  Nat.mod_eq_of_lt (by omega)]
                              · exact hp_mod
                          obtain ⟨hng, hcr_sz_le, hsz_cv, hcr3_bd⟩ :=
                            m4_cone_occ_hdr_ok hlen hw hnd har_eq hcr_ref hsz_core hgr0
                          have hsz_ar : (s.core.arena[cr.toNat + 2]?.getD 0#32).toNat = sz.toNat :=
                            hsz_core.symm
                          -- Inner clause scan loop (`while (idx < sz)`) + post-scan `add_clause`
                          m4_to_group
                          refine wp_join_group (ts := [i32, .bool, i32, i32])
                            (fun (nv_e, sat_e, cnt_e, idx_e, ()) m_e =>
                              nv.toNat ≤ nv_e.toNat ∧ ∃ st_e : FullState,
                                st_e.LengthsOk c ∧ AgreesExcept m4ConeMask s st_e ∧
                                M4ConeInv F_cur st_e nv_e.toNat nc_w.toNat ∧
                                st_e.scratch.tarjan_mark[cv.toNat]?.getD 0#32 =
                                  BitVec.ofNat 32 (qi.toNat + 1) ∧
                                (st_e.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat = cv.toNat ∧
                                (sat_e = false →
                                  idx_e.toNat = sz.toNat ∧ cnt_e.toNat ≤ idx_e.toNat ∧
                                  (∀ j < cnt_e.toNat,
                                    (st_e.core.tmp[j]?.getD 0#32).toNat < 2 * nv_e.toNat) ∧
                                  (∀ i < idx_e.toNat,
                                    let l := (s.core.arena[cr.toNat + 3 + i]?.getD 0#32).toNat
                                    s.core.vals[l]?.getD 0#8 = 0xFF#8 ∨
                                    l ∈ (st_e.core.tmp.take cnt_e.toNat).map
                                      (fun x => FullSweepFwdSpecs.coneLift
                                        st_e.scratch.work_stk1 x.toNat))) ∧
                                (FullMem c st_e ⋆ R) m_e)
                            (fun _ (nv_e, sat_e, cnt_e, idx_e, ()) m_e
                                ⟨hnve, st_e, hle, hae, hce, hte, hwe, hfalse, hme⟩ => by
                              m4_to_group; refine wp_unroll_group fun _ _ => ?_
                              m4_split
                              · m4_steps
                                exact hstep_occ nv_e nc_w st_e m_e hnve hle hae hce hte hwe hme
                              obtain ⟨hk_eq, hcnt_le, hlts_e, hcov_e⟩ :=
                                hfalse (by cases sat_e <;> simp at hc ⊢)
                              m4_split; rotate_left
                              · m4_steps
                                exact hstep_occ nv_e nc_w st_e m_e hnve hle hae hce hte hwe hme
                              have hcnt_ge2 : 2 ≤ cnt_e.toNat := by simpa using hc
                              have hcnt_le12 : cnt_e.toNat ≤ 12 :=
                                Nat.le_trans hcnt_le (hk_eq ▸ hsz_le12)
                              have hcnt_tmp : cnt_e.toNat ≤ st_e.core.tmp.length := by
                                rw [hle.core_ok.tmp_len_arr]
                                exact Nat.le_trans hcnt_le
                                  (hk_eq ▸ Nat.le_trans hsz_cv hcv_le)
                              have hent_ke : (cnfOfClauses F_cur).EntailsClause (cnfClause
                                  ((st_e.core.tmp.take cnt_e.toNat).map (fun x =>
                                    FullSweepFwdSpecs.coneLift st_e.scratch.work_stk1
                                      x.toNat))) := by
                                refine m4_cone_clause_entails_filtered hw hcl0 hcr_ref hng
                                  fun l hl => ?_
                                obtain ⟨i, hi, rfl⟩ :=
                                  (m4_arenaClauseLitsCore_mem_iff
                                    (by rw [hsz_ar]; exact hcr3_bd)).mp hl
                                rw [hsz_ar] at hi
                                exact hcov_e i (hk_eq.symm ▸ hi)
                              m4_steps
                              refine m4_cone_call_add_clause hAddCl (aSz := Arg.var cnt_e) rfl
                                hle hae hce hncw_lt hcnt_ge2
                                (Nat.lt_of_le_of_lt hcnt_le12 (by decide)) hcnt_tmp hlts_e
                                hent_ke hme (fun ok st' m' hl' ha' hc' ht_eq hw_eq hm' => by
                                  m4_split
                                  · m4_steps
                                    exact hstep_occ nv_e (nc_w + 1#32) st' m' hnve hl' ha'
                                      (by simpa only [hc, ↓reduceIte] using hc')
                                      (ht_eq ▸ hte) (hw_eq ▸ hwe) hm'
                                  · m4_steps
                                    exact hstep_occ nv_e nc_w st' m' hnve hl' ha'
                                      (by simpa only [hc, Bool.false_eq_true, ↓reduceIte]
                                        using hc')
                                      (ht_eq ▸ hte) (hw_eq ▸ hwe) hm'))
                            (fun _ hJ_occ => by
                              m4_to_group
                              refine wp_loop_inv (ts := [i32, i32, i32])
                                (fun (nv_k, cnt, idx, ()) mk =>
                                  idx.toNat ≤ sz.toNat ∧ cnt.toNat ≤ idx.toNat ∧
                                    nv.toNat ≤ nv_k.toNat ∧
                                  ∃ st_k : FullState,
                                    st_k.LengthsOk c ∧ AgreesExcept m4ConeMask s st_k ∧
                                    M4ConeInv F_cur st_k nv_k.toNat nc_w.toNat ∧
                                    st_k.scratch.tarjan_mark[cv.toNat]?.getD 0#32 =
                                      BitVec.ofNat 32 (qi.toNat + 1) ∧
                                    (st_k.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat = cv.toNat ∧
                                    (∀ j < cnt.toNat,
                                      (st_k.core.tmp[j]?.getD 0#32).toNat < 2 * nv_k.toNat) ∧
                                    (∀ i < idx.toNat,
                                      let l := (s.core.arena[cr.toNat + 3 + i]?.getD 0#32).toNat
                                      s.core.vals[l]?.getD 0#8 = 0xFF#8 ∨
                                      l ∈ (st_k.core.tmp.take cnt.toNat).map
                                        (fun x => FullSweepFwdSpecs.coneLift
                                          st_k.scratch.work_stk1 x.toNat)) ∧
                                    (FullMem c st_k ⋆ R) mk)
                                (fun (_, _, idx, ()) _ => sz.toNat - idx.toNat)
                                (fun _ hJ_k => by
                                  m4_steps
                                  exact hJ_k (nv_w, 0#32, 0#32, ()) mw
                                    ⟨Nat.zero_le _, Nat.zero_le _, hnv_w_mono, st_w, hlen_w, hag_w,
                                     hcone_w, htmk_w, hwk_w, fun _ hj => by simp at hj,
                                     fun _ hi => by simp at hi, hmw⟩)
                                (fun _ (nv_k, cnt, idx, ()) mk
                                    ⟨hk_le, hcnt_le, hnv_k_mono, st_k, hlen_k, hag_k, hcone_k,
                                      htmk_k,
                                     hwk_k, hlts_k, hcov_k, hmk⟩ hJ_k => by
                              clear hJ_we hJ_w hmw hlen_w hag_w hcone_w htmk_w hwk_w hslice2
                                hocc_done hstep_occ hcr_s har_cr_idx hgr0 hsz_core hpol1 hmap_c
                                hcond htmk hdw hnd hdm hAddCl
                              m4_split; rotate_left
                              · have hidx_ge : sz.toNat ≤ idx.toNat := by
                                  rw [har_sz_idx] at hc
                                  · exact Nat.le_of_not_lt hc
                                  · rw [hcr_idx]
                                    · rw [hcr2_lt, show BitVec.toNat (2 : BitVec 64) = 2 from rfl,
                                        Nat.mod_eq_of_lt (by omega)]
                                    · exact hp_mod
                                have hk_eq : idx.toNat = sz.toNat := Nat.le_antisymm hk_le hidx_ge
                                m4_steps
                                exact hJ_occ (nv_k, false, cnt, idx, ()) mk
                                  ⟨hnv_k_mono, st_k, hlen_k, hag_k, hcone_k, htmk_k, hwk_k,
                                   fun _ => ⟨hk_eq, hcnt_le, hlts_k, hcov_k⟩, hmk⟩
                              · -- Body of `idx < sz` loop
                                have hk_lt : idx.toNat < sz.toNat := by
                                  rw [har_sz_idx] at hc
                                  · exact hc
                                  · rw [hcr_idx]
                                    · rw [hcr2_lt, show BitVec.toNat (2 : BitVec 64) = 2 from rfl,
                                        Nat.mod_eq_of_lt (by omega)]
                                    · exact hp_mod
                                have hae_k := hag_k.get (·.core.arena)
                                have hve_k := hag_k.get (·.core.vals)
                                have har_k := hlen_k.core_ok.arena_len_arr
                                have hvals_k := hlen_k.core_ok.vals_len
                                have hidx_k : (BitVec.setWidth 64 cr + 3#64 +
                                    BitVec.setWidth 64 idx).toNat = cr.toNat + 3 + idx.toNat := by
                                  simp only [bv_c0_zext32_64, BitVec.toNat_add,
                                    show (3#64 : BitVec 64).toNat = 3 from rfl]; omega
                                have hidx_bd : (BitVec.setWidth 64 cr + 3#64 +
                                    BitVec.setWidth 64 idx).toNat < st_k.core.arena.length := by
                                  rw [har_k, hidx_k]; omega
                                have hl_in_cl :
                                    (st_k.core.arena[cr.toNat + 3 + idx.toNat]'(by
                                        rw [har_k]; omega)).toNat ∈
                                      fullArenaClauseLitsCore s.core cr.toNat := by
                                  rw [m4_arenaClauseLitsCore_mem_iff
                                    (by rw [hsz_ar]; exact hcr3_bd)]
                                  refine ⟨idx.toNat, by rw [hsz_ar]; exact hk_lt, ?_⟩
                                  rw [List.getElem?_eq_getElem (by rw [← hae_k, har_k]; omega),
                                    Option.getD_some]
                                  simp [hae_k]
                                let lit_k : BitVec 32 :=
                                  st_k.core.arena[(BitVec.setWidth 64 cr + 3#64 +
                                    BitVec.setWidth 64 idx).toNat]'hidx_bd
                                have hl_lt_s : lit_k.toNat < 2 * s.core.cur_vars := by
                                  dsimp only [lit_k]
                                  simpa only [hidx_k] using
                                    hw.arena.lits_lt cr.toNat hcr_ref hng _ hl_in_cl
                                have hval_bd : lit_k.toNat < st_k.core.vals.length := by
                                  rw [hvals_k]; omega
                                have hk1 : (idx + 1#32).toNat = idx.toNat + 1 :=
                                  m4_bv32_add1 (by omega)
                                have hlit_ar : (s.core.arena[cr.toNat + 3 + idx.toNat]?.getD
                                    0#32).toNat = lit_k.toNat := by
                                  rw [List.getElem?_eq_getElem (by rw [← hae_k, har_k]; omega),
                                    Option.getD_some]
                                  simp only [lit_k, hidx_k, hae_k]
                                have h_ar_lk : ∀ {pf},
                                    st_k.core.arena[(BitVec.setWidth 64 cr + (3 : BitVec 64) +
                                      BitVec.setWidth 64 idx).toNat]'pf = lit_k := fun {_} => rfl
                                have har_hc_idx :
                                    (cr.toNat + BitVec.toNat (3 : BitVec 64) +
                                      BitVec.toNat idx) % 2 ^ 64 = cr.toNat + 3 + idx.toNat := by
                                  rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
                                    Nat.mod_eq_of_lt (by omega)]
                                have hidx_bd_w : (BitVec.setWidth 64
                                    (st_w.core.wstk[(p + 1#64).toNat]'hp1_wstk) + 3#64 +
                                    BitVec.setWidth 64 idx).toNat < st_k.core.arena.length := by
                                  rw [hcr_w_p1]; exact hidx_bd
                                have h_ar_lk_w : st_k.core.arena[(BitVec.setWidth 64
                                    (st_w.core.wstk[(p + 1#64).toNat]'hp1_wstk) + 3#64 +
                                    BitVec.setWidth 64 idx).toNat]'hidx_bd_w = lit_k :=
                                  m4_list_getElem_congr (by rw [hcr_w_p1]) hidx_bd_w hidx_bd
                                have h_ar_lk_w1 : ∀ {pf1 pf2},
                                    st_k.core.arena[(BitVec.setWidth 64
                                      (st_w.core.wstk[(p + (1 : BitVec 64)).toNat]'pf1) +
                                      (3 : BitVec 64) + BitVec.setWidth 64 idx).toNat]'pf2 =
                                      lit_k := fun {_ _} =>
                                  m4_list_getElem_congr (by
                                    have hw1 :
                                        st_w.core.wstk[(p + (1 : BitVec 64)).toNat]'hp1_wstk = cr :=
                                      hcr_w_p1
                                    rw [hw1]; rfl) _ hidx_bd
                                have hval_bd_w : (BitVec.setWidth 64
                                    (st_k.core.arena[(BitVec.setWidth 64
                                      (st_w.core.wstk[(p + 1#64).toNat]'hp1_wstk) + 3#64 +
                                      BitVec.setWidth 64 idx).toNat]'hidx_bd_w)).toNat <
                                    st_k.core.vals.length := by
                                  rw [bv_c0_zext32_64, h_ar_lk_w]; exact hval_bd
                                m4_split
                                · m4_steps
                                  exact hJ_occ (nv_k, true, cnt, idx, ()) mk
                                    ⟨hnv_k_mono, st_k, hlen_k, hag_k, hcone_k, htmk_k, hwk_k,
                                     (fun h => by cases h), hmk⟩
                                have hnot_pos : s.core.vals[lit_k.toNat]?.getD 0#8 ≠ 1#8 :=
                                  fun h1 => by
                                    rw [m4_getElem_eq_getD st_k.core.vals (d := 0#8),
                                      m4_getElem_eq_getD st_k.core.arena (d := 0#32),
                                      hcr_idx _ hp_mod, har_hc_idx, hae_k, hlit_ar, hve_k, h1] at hc
                                    exact absurd hc (by decide)
                                m4_to_group; refine wp_unroll_group fun _ _ => ?_; m4_split
                                · have hl_zero : s.core.vals[lit_k.toNat]?.getD 0#8 = 0#8 := by
                                    rcases hw.vals_domain lit_k.toNat hl_lt_s with h0 | h1 | hf
                                    · exact h0
                                    · exact absurd h1 hnot_pos
                                    · rw [m4_getElem_eq_getD st_k.core.vals (d := 0#8),
                                        m4_getElem_eq_getD st_k.core.arena (d := 0#32),
                                        hcr_idx _ hp_mod, har_hc_idx, hae_k, hlit_ar, hve_k,
                                        hf] at hc
                                      exact absurd hc (by decide)
                                  have hlv_eq : (lit_k >>> (1 : Nat)).toNat = lit_k.toNat / 2 :=
                                    m4_bv32_shr1_toNat lit_k
                                  have hlv_lt : (lit_k >>> (1 : Nat)).toNat < s.core.cur_vars := by
                                    omega
                                  have hlv_tm_k :
                                      (BitVec.setWidth 64 (lit_k >>> (1 : Nat))).toNat <
                                        st_k.scratch.tarjan_mark.length := by
                                    rw [hlen_k.scratch_ok.tarjan_mark_len, bv_c0_zext32_64]; omega
                                  have hlv_tm_k_w : (BitVec.setWidth 64
                                      (st_k.core.arena[(BitVec.setWidth 64
                                        (st_w.core.wstk[(p + 1#64).toNat]'hp1_wstk) + 3#64 +
                                        BitVec.setWidth 64 idx).toNat]'hidx_bd_w >>>
                                        (1 : Nat))).toNat < st_k.scratch.tarjan_mark.length := by
                                    rw [h_ar_lk_w]; exact hlv_tm_k
                                  -- Dedup guard: `if ((ltm != 0 && ltm < cur_tmk) || (lv == cv &&
                                  -- (l & 1) < pol))`
                                  m4_to_group
                                  refine wp_join_group (ts := [])
                                    (fun () m_d => m_d = mk)
                                    (fun _ () m_d hmd => by
                                      subst m_d
                                      refine wp_join_group (ts := [])
                                        (fun () m_c => m_c = mk)
                                        (fun _ () m_c hmc => by
                                          subst m_c
                                          m4_to_group
                                          refine wp_join_group (ts := [i32])
                                            (fun (nv_u, ()) m_u =>
                                              nv.toNat ≤ nv_u.toNat ∧ ∃ st_u : FullState,
                                                st_u.LengthsOk c ∧ AgreesExcept m4ConeMask s st_u ∧
                                                M4ConeInv F_cur st_u nv_u.toNat nc_w.toNat ∧
                                                st_u.scratch.tarjan_mark[cv.toNat]?.getD 0#32 =
                                                  BitVec.ofNat 32 (qi.toNat + 1) ∧
                                                (st_u.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat
                                                  =
                                                  cv.toNat ∧
                                                st_u.core.tmp = st_k.core.tmp ∧
                                                (∀ j < nv_k.toNat, st_u.scratch.work_stk1[j]? =
                                                  st_k.scratch.work_stk1[j]?) ∧
                                                nv_k.toNat ≤ nv_u.toNat ∧ (FullMem c st_u ⋆ R) m_u)
                                            (fun _ (nv_u, ()) m_u
                                                ⟨hnvu, st_u, hlu, hau, hcu, htu, hwu, htmpu_eq,
                                                  hwku_eq,
                                                 hnvku, hmu⟩ => by
                                              have htm_u := hlu.scratch_ok.tarjan_mark_len
                                              have htmp_u := hlu.core_ok.tmp_len_arr
                                              have hcv_u := hau.get (·.core.cur_vars)
                                              have hlv_tm_u :
                                                  (BitVec.setWidth 64 (lit_k >>> (1 : Nat))).toNat <
                                                    st_u.scratch.tarjan_mark.length := by
                                                rw [htm_u, bv_c0_zext32_64]; omega
                                              have hlv_tm_u_w : (BitVec.setWidth 64
                                                  (st_k.core.arena[(BitVec.setWidth 64
                                                    (st_w.core.wstk[(p + 1#64).toNat]'hp1_wstk) +
                                                    3#64 + BitVec.setWidth 64 idx).toNat]'hidx_bd_w
                                                      >>>
                                                    (1 : Nat))).toNat <
                                                  st_u.scratch.tarjan_mark.length := by
                                                rw [h_ar_lk_w]; exact hlv_tm_u
                                              m4_split
                                              · m4_steps
                                                exact hJ_occ (nv_u, true, cnt, idx, ()) m_u
                                                  ⟨hnvu, st_u, hlu, hau, hcu, htu, hwu,
                                                   (fun h => by cases h), hmu⟩
                                              have hne_lv :
                                                  st_u.scratch.tarjan_mark[
                                                      (lit_k >>>
                                                        (1 : Nat)).toNat]?.getD 0#32 ≠ 0#32 := by
                                                rw [m4_getElem_eq_getD st_u.scratch.tarjan_mark
                                                  (d := 0#32),
                                                  m4_getElem_eq_getD st_k.core.arena (d := 0#32),
                                                  hcr_idx _ hp_mod, har_hc_idx, hae_k, hlit_ar,
                                                  ← hlv_eq] at hc
                                                exact hc
                                              rcases hcu.rev (lit_k >>> (1 : Nat)).toNat
                                                  (by rw [hcv_u]; exact hlv_lt) with
                                                hz | ⟨ilv, hilv, hwlv, htlv⟩
                                              · exact absurd hz hne_lv
                                              obtain ⟨hcnt1, hlen_u', hlts_u', hcov_u'⟩ :=
                                                m4_cone_k_unassigned_step hlu htmpu_eq hwku_eq hnvku
                                                  hcu.nv_le512 hk_lt hsz_le12 hsz_cv hcv_le hcnt_le
                                                    hlit_ar
                                                  hilv (hlv_eq ▸ hwlv)
                                                    (hlv_eq ▸ htlv) hlts_k hcov_k hcu
                                              have hcnt_tmp : (BitVec.setWidth 64 cnt).toNat <
                                                  st_u.core.tmp.length := by
                                                rw [htmp_u, bv_c0_zext32_64]; omega
                                              clear hne_lv hc hlts_k hcov_k htmpu_eq hwku_eq
                                              c0_hsteps!
                                              have htm_u_lk : ∀ {pf1 pf2 pf3},
                                                  st_u.scratch.tarjan_mark[(BitVec.setWidth 64
                                                    (st_k.core.arena[(BitVec.setWidth 64
                                                      (st_w.core.wstk[
                                                        (p + (1 : BitVec 64)).toNat]'pf1) +
                                                      (3 : BitVec 64) +
                                                      BitVec.setWidth 64 idx).toNat]'pf2 >>>
                                                      (OfNat.ofNat 1 : Nat))).toNat]'pf3 =
                                                    st_u.scratch.tarjan_mark[lit_k.toNat / 2]?.getD
                                                      0#32 := fun {_ _ _} => by
                                                have hlen_t :
                                                    lit_k.toNat / 2 <
                                                      st_u.scratch.tarjan_mark.length := by
                                                  rw [htm_u]; omega
                                                rw [List.getElem?_eq_getElem hlen_t,
                                                  Option.getD_some]
                                                exact m4_list_getElem_congr
                                                  (by rw [h_ar_lk_w1,
                                                    bv_c0_zext32_64]; exact hlv_eq)
                                                  _ _
                                              have hcnt_n :
                                                  (BitVec.setWidth 64 cnt).toNat = cnt.toNat :=
                                                bv_c0_zext32_64 cnt
                                              have hm_u' : (FullMem c { st_u with
                                                  core := { st_u.core with tmp :=
                                                    (st_u.core.tmp.set cnt.toNat
                                                      (((st_u.scratch.tarjan_mark[lit_k.toNat /
                                                        2]?.getD
                                                        0#32 - 1#32) <<< (1 : Nat)) |||
                                                        (lit_k &&& 1#32))) } } ⋆ R) m := by
                                                have hm' := hm
                                                dsimp only [LeanQbe.T.lift2, Arg.val_var,
                                                  Arg.val_imm,
                                                  Prod.fst] at hm'
                                                rw [hcnt_n, htm_u_lk, h_ar_lk_w1] at hm'
                                                exact hm'
                                              exact hJ_k (nv_u, cnt + 1#32, idx + 1#32, ()) m
                                                (by dsimp only; omega)
                                                ⟨by omega, by omega, hnvu, _, hlen_u',
                                                 hau.update _ fun _ => rfl,
                                                 m4ConeInv_tmp_irrel hcu, htu, hwu, hlts_u',
                                                 hcov_u', hm_u'⟩)
                                            (fun _ hJ_u => by
                                              have htm_k := hlen_k.scratch_ok.tarjan_mark_len
                                              have hwk_k_len := hlen_k.scratch_ok.work_stk1_len
                                              m4_split
                                              · have hc_tmk := hc
                                                m4_split
                                                · have hmiss :
                                                      st_k.scratch.tarjan_mark[
                                                          (lit_k >>> (1 : Nat)).toNat]?.getD 0#32 =
                                                        0#32 := by
                                                    rw [m4_getElem_eq_getD st_k.scratch.tarjan_mark
                                                        (d := 0#32),
                                                      m4_getElem_eq_getD st_k.core.arena (d :=
                                                        0#32),
                                                      hcr_idx _ hp_mod, har_hc_idx, hae_k, hlit_ar,
                                                      ← hlv_eq] at hc_tmk
                                                    exact hc_tmk
                                                  have hnv_k_512 : nv_k.toNat < 512 := hc
                                                  have hcv_k := hag_k.get (·.core.cur_vars)
                                                  have hnv_k_lt : nv_k.toNat < s.core.cur_vars := by
                                                    rw [← hcv_k]
                                                    exact (m4ConeInv_push_var hlen_k hcone_k
                                                      hnv_k_512
                                                      (by rw [hcv_k]; exact hlv_lt) hmiss).1
                                                  have hnv1 :
                                                      (nv_k + 1#32).toNat = nv_k.toNat + 1 :=
                                                    m4_bv32_add1 (by omega)
                                                  have hnv_ws :
                                                      (BitVec.setWidth 64 ((nv_k +
                                                        1#32) - 1#32)).toNat <
                                                        st_k.scratch.work_stk1.length := by
                                                    rw [hwk_k_len, bv_c0_zext32_64,
                                                      m4_bv32_add1_sub1_eq nv_k]
                                                    omega
                                                  c0_hsteps!
                                                  have hpush :=
                                                    m4ConeInv_push_var hlen_k hcone_k hnv_k_512
                                                    (by rw [hcv_k]; exact hlv_lt) hmiss
                                                  obtain ⟨st_u, hst_u⟩ : ∃ st_u : FullState, st_u =
                                                    { st_k with scratch :=
                                                      { st_k.scratch with
                                                        tarjan_mark := st_k.scratch.tarjan_mark.set
                                                          (lit_k >>> (1 : Nat)).toNat (nv_k + 1#32)
                                                        work_stk1 := st_k.scratch.work_stk1.set
                                                          nv_k.toNat (lit_k >>> (1 : Nat)) } } :=
                                                            ⟨_, rfl⟩
                                                  have hne_cv :
                                                      cv.toNat ≠ (lit_k >>> (1 : Nat)).toNat :=
                                                    fun heq => by
                                                      rw [← heq, htmk_k] at hmiss
                                                      have := congrArg BitVec.toNat hmiss
                                                      simp [BitVec.toNat_ofNat] at this; omega
                                                  have hne_nv_qi : nv_k.toNat ≠ qi.toNat := by omega
                                                  have h2 :
                                                      (BitVec.setWidth 64 (nv_k + (1 : BitVec 32) -
                                                      (1 : BitVec 32))).toNat = nv_k.toNat := by
                                                    rw [bv_c0_zext32_64]
                                                    exact m4_bv32_add1_sub1_toNat nv_k
                                                  have htm_idx : (BitVec.setWidth 64
                                                      (lit_k >>> (OfNat.ofNat 1 : Nat))).toNat =
                                                      (lit_k >>> (1 : Nat)).toNat :=
                                                        bv_c0_zext32_64 _
                                                  have hm_u : (FullMem c st_u ⋆ R) m := by
                                                    have hm' := hm
                                                    dsimp only [LeanQbe.T.lift2, Arg.val_var,
                                                      Arg.val_imm,
                                                      Prod.fst] at hm'
                                                    rw [h_ar_lk_w1, htm_idx, h2] at hm'
                                                    exact (congrArg (fun stx =>
                                                      (FullMem c stx ⋆ R) m)
                                                      (by rw [hst_u]; rfl)).mp hm'
                                                  refine hJ_u (nv_k + 1#32, ()) m
                                                    ⟨by omega, st_u,
                                                      by rw [hst_u]; exact ⟨hlen_k.core_ok,
                                                        { hlen_k.scratch_ok with
                                                          tarjan_mark_len := by simp [htm_k]
                                                          work_stk1_len := by simp [hwk_k_len] }⟩,
                                                      hst_u ▸ hag_k.update _ fun _ => rfl,
                                                      by rw [hnv1, hst_u]
                                                         have hb := m4_bv32_ofNat_add1 nv_k
                                                         rw [hb] at hpush; exact hpush.2,
                                                      by rw [hst_u,
                                                        List.getElem?_set_ne (Ne.symm hne_cv)]
                                                         exact htmk_k,
                                                      by rw [hst_u, List.getElem?_set_ne hne_nv_qi]
                                                         exact hwk_k,
                                                      by rw [hst_u],
                                                      fun j hj => by
                                                        rw [hst_u]
                                                        exact List.getElem?_set_ne (by omega),
                                                      by omega, hm_u⟩
                                                · m4_steps; exact hJ_u (nv_k, ()) mk
                                                    ⟨hnv_k_mono, st_k, hlen_k, hag_k, hcone_k,
                                                      htmk_k,
                                                     hwk_k, rfl, fun _ _ => rfl, le_refl _, hmk⟩
                                              · m4_steps; exact hJ_u (nv_k, ()) mk
                                                  ⟨hnv_k_mono, st_k, hlen_k, hag_k, hcone_k, htmk_k,
                                                   hwk_k, rfl, fun _ _ => rfl, le_refl _, hmk⟩))
                                        (fun _ hJcont => by
                                          m4_split
                                          · m4_split
                                            · m4_steps
                                              exact hJ_occ (nv_k, true, cnt, idx, ()) mk
                                                ⟨hnv_k_mono, st_k, hlen_k, hag_k, hcone_k, htmk_k,
                                                 hwk_k, (fun h => by cases h), hmk⟩
                                            · m4_steps; exact hJcont () mk rfl
                                          · m4_steps; exact hJcont () mk rfl))
                                    (fun _ hJdup => by
                                      m4_split
                                      · m4_split
                                        · m4_steps
                                          exact hJ_occ (nv_k, true, cnt, idx, ()) mk
                                            ⟨hnv_k_mono, st_k, hlen_k, hag_k, hcone_k, htmk_k,
                                             hwk_k, (fun h => by cases h), hmk⟩
                                        · m4_steps; exact hJdup () mk rfl
                                      · m4_steps; exact hJdup () mk rfl)
                                · have hne0 : s.core.vals[lit_k.toNat]?.getD 0#8 ≠ 0#8 :=
                                    fun h0 => by
                                      rw [m4_getElem_eq_getD st_k.core.vals (d := 0#8),
                                        m4_getElem_eq_getD st_k.core.arena (d := 0#32),
                                        hcr_idx _ hp_mod, har_hc_idx, hae_k, hlit_ar, hve_k,
                                        h0] at hc
                                      exact absurd (by decide) hc
                                  have hfals_k : s.core.vals[lit_k.toNat]?.getD 0#8 = 0xFF#8 :=
                                    (hw.vals_domain lit_k.toNat hl_lt_s).elim
                                      (absurd · hne0) (·.elim (absurd · hnot_pos) id)
                                  m4_steps
                                  refine hJ_k (nv_k, cnt, idx + 1#32, ()) mk (by dsimp only; omega)
                                    ⟨by omega, by omega, hnv_k_mono, st_k, hlen_k, hag_k, hcone_k,
                                     htmk_k, hwk_k, hlts_k, fun i hi => ?_, hmk⟩
                                  rw [hk1] at hi
                                  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
                                  · exact hcov_k i hlt
                                  · left; rwa [hlit_ar])))))
          · m4_steps; exact hJ_ex () mo ⟨st, hlen_st, hag_st, hcone_st, hmo⟩))

end LeanQbe.T.Examples.Kissat.FullM4Sweep
