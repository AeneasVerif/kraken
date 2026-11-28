/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Sweep.LemmasCommon

/-!
# Top-Level Driver WP Proofs Part 0 (`Kissat.Proof.Sweep.WpDriver0`)

Flat `CanonicalEnv` `Func.wp` proofs for `3/5` driver functions in `Src.Sweep`:
1. `full_m6_sweep_units_wp` (`fullM6SweepUnitsSpec`)
2. `full_m6_sweep_var_wp` (`fullM6SweepVarSpec`)
3. `full_sweep_dense_m6_wp` (`fullSweepDenseM6Spec`)

Zero legacy `Full*` imports; zero expose attributes on theorems, lemmas, or sections.
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

/-! ## 1. Shared Assumption Memory, `K6Inv`/`K6TailEq`, & Alignment Helpers -/

namespace M6UnitMem

@[scoped c0_store] theorem store_k6_assump0_ofnat {L : K6Layout} {kPtr : BitVec 64}
    {ks : K6State} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32)
    (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32 ((kPtr + BitVec.ofNat 64 (4 * L.oAssump)) + BitVec.ofNat 64 0 * 4) ∧
      (K6MemA L kPtr (ks.putArr .assump 0 v) ⋆ R)
        (storeMem m i32
          ((kPtr + BitVec.ofNat 64 (4 * L.oAssump)) + BitVec.ofNat 64 0 * 4) v) := by
  simpa using store_k6_assump0 v hm

@[scoped c0_store] theorem store_k6_assump0_dyn {L : K6Layout} {kPtr : BitVec 64} {ks : K6State}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32
        ((kPtr + BitVec.setWidth 64 ((32 : BitVec 32) + (9 : BitVec 32) * L.mv32) * 4) +
          BitVec.ofNat 64 0 * 4) ∧
      (K6MemA L kPtr (ks.putArr .assump 0 v) ⋆ R)
        (storeMem m i32
          ((kPtr + BitVec.setWidth 64 ((32 : BitVec 32) + (9 : BitVec 32) * L.mv32) * 4) +
            BitVec.ofNat 64 0 * 4) v) := by
  rw [k6_ptr_assump L kPtr]; exact store_k6_assump0_ofnat v hm

end M6UnitMem

private theorem m6_scrCap_lt64 (c : FullCfg) : c.scratch_cap < 2 ^ 64 := by
  have := c.hscr; unfold dimacsBound at this; omega

private theorem m6_mv32_eq {c : FullCfg} {L : K6Layout} (hLmv : L.maxV = k6MaxV c.scratch_cap) :
    (BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32 = L.mv32 := by
  have hm := L.hmaxV
  apply BitVec.eq_of_toNat_eq
  simp only [k6_mv32_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [← hLmv]; omega

private theorem m6_ptr_phtMerged (L : K6Layout) (pScr : BitVec 64) :
    pScr + BitVec.setWidth 64 ((1280 : BitVec 32) + L.mv32) * 4 =
      pScr + BitVec.ofNat 64 (4 * L.phtMerged) := by
  have := L.hmaxV
  congr 1; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_add, k6_mv32_toNat,
    BitVec.toNat_ofNat]
  rw [show (1280 : BitVec 32).toNat = 1280 from rfl, show (4 : BitVec 64).toNat = 4 from rfl]
  unfold K6Layout.phtMerged
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

private theorem m6_hwm_step {L : K6Layout} {gu : List (BitVec 32)} {nv : BitVec 32}
    {ks ks' : K6State}
    (hhw_le : gu[33]? = some 0xFFFFFFFF#32 ∨ nv.toNat ≤ (gu[33]?.getD 0#32).toNat)
    (hnv : ks.nv = nv) (hhwm : K6HwmClean L (gu[33]?.getD 0#32) ks)
    (ht : K6TailEq L ks ks') : K6HwmClean L (gu[33]?.getD 0#32) ks' :=
  k6HwmClean_of_tailEq (hnv ▸ hhw_le) rfl hhwm ht

private theorem k6Inv_set_assump1 {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    {a0 : BitVec 32} (ha0 : a0.toNat < 2 * ks.nv.toNat) (hinv : K6Inv L P ks) :
    let ks' := (ks.putHdr .nassump 1#32).putArr .assump 0 a0
    K6Inv L P ks' ∧ ks'.nv = ks.nv ∧ K6TailEq L ks ks' ∧
    k6AssumpLits ks' = [a0.toNat] ∧ ks'.neq = ks.neq := by
  intro ks'
  have hmL := L.hmaxV; have hcl := hinv.clauses
  have ha0_lt : 0 < ks.assump.length := by rw [hinv.shapes.assump_len]; omega
  refine ⟨⟨(hinv.shapes.putHdr .nassump 1#32).putArr .assump 0 a0,
    { acap_eq := hcl.acap_eq, max_v_eq := hcl.max_v_eq, max_orig_eq := hcl.max_orig_eq,
      max_cl_eq := hcl.max_cl_eq, nv_le := hcl.nv_le, nc_le := hcl.nc_le, alen_le := hcl.alen_le,
      nassump_le := by dsimp only [ks', K6State.putArr, K6State.putHdr]; simp; omega
      nkl_le := hcl.nkl_le, nana_le := hcl.nana_le,
      cl_wf := fun cid hc => hcl.cl_wf cid hc,
      cl_mono := fun c1 c2 h12 h2c => hcl.cl_mono c1 c2 h12 h2c,
      incons_ok := hcl.incons_ok,
      assump_ok := fun i hi => by
        dsimp only [ks', K6State.putArr, K6State.putHdr] at hi ⊢
        have hi0 : i = 0 := by simp at hi; omega
        subst hi0; rw [List.getElem?_set_self ha0_lt, Option.getD_some]; exact ha0
      flags_clean := hcl.flags_clean },
    hinv.watches,
    k6BaseAssignOk_cast hinv.assign rfl rfl rfl rfl rfl rfl rfl rfl rfl,
    hinv.reasons⟩, rfl, ⟨rfl, fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩, ?_, rfl⟩
  unfold k6AssumpLits; dsimp only [ks', K6State.putArr, K6State.putHdr]
  cases h : ks.assump with
  | nil => simp [h] at ha0_lt
  | cons x xs => simp [List.set, List.take]

private theorem m6_coneModelSet_unsat_unit {F_cur : List (List Nat)} {ws1 : List (BitVec 32)}
    {nv a : Nat} (_ha : a < 2 * nv)
    (h : ∀ β, ConeModelSet F_cur ws1 nv β → ¬ (unitsCnf [a]).Sat β) :
    SemEntails (ConeModelSet F_cur ws1 nv) [a ^^^ 1] ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [m6ConeLift ws1 (a ^^^ 1)]) := by
  have hsem : SemEntails (ConeModelSet F_cur ws1 nv) [a ^^^ 1] := fun β hβ => by
    rw [show a ^^^ 1 = litNeg a from rfl, sat_cnfClause_litNeg_iff]
    intro hsat
    exact h β hβ ((sat_unitsCnf_iff β [a]).mpr fun l hl => by
      simp only [List.mem_singleton] at hl; subst hl; exact hsat)
  refine ⟨hsem, ?_⟩
  rw [CNF.entails_clause_def]; intro α hα
  exact (coneLift_sat_iff (α := α) (cone_v := ws1) (l := a ^^^ 1)).mp
    (hsem (fun i => α (ws1[i]?.getD 0#32).toNat) ⟨α, hα, fun _ _ => rfl⟩)

private theorem m6_unit_lit_align {ws1 : List (BitVec 32)} {i gv wf : BitVec 32}
    (hi : i.toNat < 2 ^ 31) (hgv : gv.toNat < 2 ^ 31)
    (hws : (ws1[i.toNat]?.getD 0#32).toNat = gv.toNat) (hwf : wf = 0#32 ∨ wf = 1#32) :
    let test_lit := (i <<< (1 : Nat)) ||| wf
    let gl := (gv <<< (1 : Nat)) ||| (1#32 - wf)
    test_lit.toNat = 2 * i.toNat + wf.toNat ∧
    gl.toNat = m6ConeLift ws1 (test_lit.toNat ^^^ 1) ∧
    gl.toNat = 2 * gv.toNat + (1 - wf.toNat) := by
  intro test_lit gl
  have hwf_lt : wf.toNat < 2 := by rcases hwf with rfl | rfl <;> decide
  have h1w_lt : (1#32 - wf).toNat < 2 := by rcases hwf with rfl | rfl <;> decide
  have htl : test_lit.toNat = 2 * i.toNat + wf.toNat := m6_bv32_shl1_or_pol i wf hi hwf_lt
  have hgl : gl.toNat = 2 * gv.toNat + (1 - wf.toNat) := by
    rw [m6_bv32_shl1_or_pol gv (1#32 - wf) hgv h1w_lt]; rcases hwf with rfl | rfl <;> rfl
  have hlift : m6ConeLift ws1 (test_lit.toNat ^^^ 1) = 2 * gv.toNat + (1 - wf.toNat) := by
    have hc := coneLift_of_tmk_pair (cone_v := ws1) (idx := i.toNat) (v := gv.toNat)
      (l := 2 * gv.toNat + (1 - wf.toNat)) hws (by omega)
    rw [htl]; rcases hwf with rfl | rfl
    · have hx : (2 * i.toNat + (0#32).toNat) ^^^ 1 =
          2 * i.toNat + (2 * gv.toNat + (1 - (0#32).toNat)) % 2 := by
        rw [show (0#32).toNat = 0 from rfl, Nat.add_zero, m6_nat_xor1_even i.toNat]; omega
      rw [hx]; exact hc
    · have hx : (2 * i.toNat + (1#32).toNat) ^^^ 1 =
          2 * i.toNat + (2 * gv.toNat + (1 - (1#32).toNat)) % 2 := by
        rw [show (1#32).toNat = 1 from rfl, m6_nat_xor1_odd i.toNat]; omega
      rw [hx]; exact hc
  exact ⟨htl, hgl.trans hlift.symm, hgl⟩

/-! ## 2. `full_m6_sweep_units_wp` (`1/5`) -/

private structure M6UnitState (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 : FullState) (L : K6Layout) (nv rbit : BitVec 32) (R : Mem 64 → Prop) (m : Mem 64) where
  rbit_le : rbit.toNat ≤ 64
  st : FullState
  inv : FullDenseInvW c F0 F_cur st
  cv : st.core.cur_vars = s0.core.cur_vars
  fuel : st.core.fuel.toNat ≤ s0.core.fuel.toNat
  repr : st.core.repr = s0.core.repr
  ws : st.scratch.work_stk1 = s0.scratch.work_stk1
  tmk : st.scratch.tarjan_mark = s0.scratch.tarjan_mark
  trh : st.scratch.tarjan_reach = s0.scratch.tarjan_reach
  ws2 : st.scratch.work_stk2 = s0.scratch.work_stk2
  gu : st.scratch.glue_used = s0.scratch.glue_used
  cone : M6SweepConeOk F_cur st nv.toNat
  hwm : K6HwmClean L (s0.scratch.glue_used[33]?.getD 0#32)
    (k6StateOfScratch L st.scratch.scratch_buf)
  mem : (FullMem c st ⋆ R) m

private theorem m6_unit_d20_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s sS : FullState}
    {L : K6Layout} {nv rbit i gv wf test_lit : Val i32} {h kPtr pmPtr smask : Val i64}
    {R : Mem 64 → Prop} {mS : Mem 64} {jIf : Cont [i32, i64]}
    (hAddU : Γ.Has "full_add_unit" fullAddUnitSpec)
    (hLive : Γ.Has "full_k512_add_live_m6" step13K6AddLiveSpec)
    (hRearm : Γ.Has "full_m6_sweep_rearm" fullM6SweepRearmSpec)
    (hQ_ff : ∀ (s' : FullState) m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.core.repr = s.core.repr →
      s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.work_stk2 = s.scratch.work_stk2 → s'.scratch.glue_used = s.scratch.glue_used →
      M6SweepConeOk F_cur s' nv.toNat →
      K6HwmClean L (s'.scratch.glue_used[33]?.getD 0#32)
        (k6StateOfScratch L s'.scratch.scratch_buf) →
      (k6StateOfScratch L s'.scratch.scratch_buf).nv = nv →
      F0.Unsat → (FullMem c s' ⋆ R) m' → Q (0xFFFFFFFFFFFFFFFF#64, ()) m')
    (h_hdr : h = c.hdr) (hkptr : kPtr = L.kPtr c.pScratchBuf)
    (hpmp : pmPtr = c.pScratchBuf + BitVec.ofNat 64 (4 * L.phtMerged))
    (hL_len : L.scrLen = c.scratch_cap) (hL_mv : L.maxV = k6MaxV c.scratch_cap)
    (hhw_le : s.scratch.glue_used[33]? = some 0xFFFFFFFF#32 ∨
      nv.toNat ≤ (s.scratch.glue_used[33]?.getD 0#32).toNat)
    (hinvS : FullDenseInvW c F0 F_cur sS) (hrb_le : rbit.toNat ≤ 64)
    (hcvS : sS.core.cur_vars = s.core.cur_vars)
    (hfuelS : sS.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hreprS : sS.core.repr = s.core.repr) (hwsS : sS.scratch.work_stk1 = s.scratch.work_stk1)
    (htmkS : sS.scratch.tarjan_mark = s.scratch.tarjan_mark)
    (htrhS : sS.scratch.tarjan_reach = s.scratch.tarjan_reach)
    (hws2S : sS.scratch.work_stk2 = s.scratch.work_stk2)
    (hguS : sS.scratch.glue_used = s.scratch.glue_used)
    (hconeS : M6SweepConeOk F_cur sS nv.toNat)
    (hKS : K6Inv L (ConeModelSet F_cur s.scratch.work_stk1 nv.toNat)
      (k6StateOfScratch L sS.scratch.scratch_buf))
    (hnvS : (k6StateOfScratch L sS.scratch.scratch_buf).nv = nv)
    (hhwmS : K6HwmClean L (s.scratch.glue_used[33]?.getD 0#32)
      (k6StateOfScratch L sS.scratch.scratch_buf))
    (hi_mv : i.toNat < L.maxV) (htl_x_lt : (test_lit ^^^ 1#32).toNat < 2 * nv.toNat)
    (hgl_lt : ((gv <<< (1 : Nat)) ||| (1#32 - wf)).toNat < 2 * sS.core.cur_vars)
    (hent_gl : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [((gv <<< (1 : Nat)) ||| (1#32 - wf)).toNat]))
    (hsem_u : SemEntails (ConeModelSet F_cur s.scratch.work_stk1 nv.toNat)
      [(test_lit ^^^ 1#32).toNat])
    (hmS : (FullMem c sS ⋆ R) mS)
    (hJif : ∀ m', M6UnitState c F0 F_cur s L nv rbit R m' →
      wp Γ Q X (Expr.jump jIf (Arg.var rbit, Arg.var smask, ())) m') :
    wp Γ Q X
      (Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var gv, Arg.imm 1, ())) fun p0 =>
       Expr.let_ (Op.mk (OpCode.sub i32) (Arg.imm 1, Arg.var wf, ())) fun p1 =>
       Expr.let_ (Op.mk (OpCode.or i32) (Arg.var p0.fst, Arg.var p1.fst, ())) fun p2 =>
       Expr.call "full_add_unit" (as := [i64, i32]) (bs := [.bool])
        (Arg.var h, Arg.var p2.fst, ()) fun pok =>
       Expr.jnz (Arg.var pok.fst)
        (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var i, ())) fun q0 =>
         Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var q0.fst, Arg.imm 4, ())) fun q1 =>
         Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pmPtr, Arg.var q1.fst, ())) fun q2 =>
         Expr.store (t := i32) (Arg.imm 1) (Arg.var q2.fst)
         (Expr.let_ (Op.mk (OpCode.xor i32) (Arg.var test_lit, Arg.imm 1, ())) fun q3 =>
          Expr.call "full_k512_add_live_m6" (as := [i64, i32, i32]) (bs := [])
           (Arg.var h, Arg.var q3.fst, Arg.imm 0xFFFFFFFF#32, ()) fun _ =>
          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 6, ())) fun r0 =>
          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var r0.fst, Arg.imm 4, ())) fun r1 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var kPtr, Arg.var r1.fst, ())) fun r2 =>
          Expr.load i32 (Arg.var r2.fst) fun ld =>
          Expr.let_ (Op.mk (OpCode.cmp CmpOp.ne i32) (Arg.var ld, Arg.imm 0, ())) fun rc =>
          Expr.jnz (Arg.var rc.fst)
           (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var h, Arg.imm 1024, ())) fun rh =>
            Expr.store (t := i64) (Arg.imm 1) (Arg.var rh.fst)
             (Expr.ret (Arg.imm 0xFFFFFFFFFFFFFFFF#64, ())))
           (Expr.call "full_m6_sweep_rearm" (as := [i64, i32]) (bs := [])
             (Arg.var h, Arg.var gv, ()) fun _ =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var h, Arg.imm 1080, ())) fun s0 =>
            Expr.load i64 (Arg.var s0.fst) fun ld2 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var ld2, Arg.imm 1, ())) fun s1 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var h, Arg.imm 1080, ())) fun s2 =>
            Expr.store (t := i64) (Arg.var s1.fst) (Arg.var s2.fst)
             (Expr.jump jIf (Arg.var rbit, Arg.var smask, ())))))
        (Expr.ret (Arg.imm 0xFFFFFFFFFFFFFFFF#64, ())))
      mS := by
  subst h_hdr hkptr hpmp
  have hmL := L.hmaxV; have haL := L.hacap
  have hscrS_len := hinvS.1.scratch_ok.scratch_buf_len
  have hnv_ofNat : nv = BitVec.ofNat 32 nv.toNat :=
    BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt nv.isLt])
  m6_steps; m6_call hAddU
  refine ⟨c, F0, F_cur, sS, R, rfl, hinvS.1, hinvS.2.1, fun _ => hent_gl, hmS, ?_⟩
  intro okU valsU flagsU lvlU rsnsU trlU tpU teU propU clU unassU unflU incU phasesU taU baU
    ptU pbU hpU psU hlU qsiU qssU mU sU hlenU hwU hclU hokF _ hmU
  have hinvU : FullDenseInvW c F0 F_cur sU :=
    ⟨hlenU, hwU, hinvS.2.2.1, hinvS.2.2.2.1, hinvS.2.2.2.2.1, hclU, hinvS.2.2.2.2.2.2⟩
  have hconeU : M6SweepConeOk F_cur sU nv.toNat := hconeS
  m6_split; rotate_left
  · have hok_f : okU = false := by cases okU <;> simp at hc ⊢
    m6_steps
    exact hQ_ff sU mU hinvU hcvS hfuelS hreprS hwsS htmkS htrhS hws2S hguS hconeU
      (hguS.symm ▸ hhwmS) hnvS (hokF hgl_lt hok_f).1 hmU
  change wp _ _ _ _ _
  c0_hsteps_nogrp; try dsimp only [Prod.fst]
  open scoped M6PhtMem in m6_steps
  have hlt_k6 : L.phtMerged + i.toNat < L.k6Base := by
    unfold K6Layout.phtMerged K6Layout.k6Base; omega
  let scrM2 := sU.scratch.scratch_buf.set (L.phtMerged + i.toNat) 1#32
  let sM2 : FullState := { sU with scratch := { sU.scratch with scratch_buf := scrM2 } }
  have hscrM2_len : scrM2.length = c.scratch_cap := List.length_set.trans hscrS_len
  have hofM2 : k6StateOfScratch L scrM2 = k6StateOfScratch L sS.scratch.scratch_buf :=
    m6_k6Inv_of_prefix_set hlt_k6
  have hinvM2 := m6_fullDenseInvW_with_scratch hinvU hscrM2_len (fuel' := sU.core.fuel)
  m6_call hLive
  refine ⟨c, sM2, ConeModelSet F_cur s.scratch.work_stk1 nv.toNat, L, R, rfl, hinvM2.1, hL_len,
    hL_mv, hofM2 ▸ hKS, by dsimp only [Arg.val]; rw [hofM2, hnvS]; exact htl_x_lt,
    fun _ => hsem_u, fun h => absurd rfl h, by assumption,
    fun scrL2 mL2 hlenL2 _ hKL2 _ hnvL2 htlL2 _ _ _ hmL2 => ?_⟩
  let sL2 : FullState := { sU with scratch := { sU.scratch with scratch_buf := scrL2 } }
  have hscrL2_len := hlenL2.scratch_ok.scratch_buf_len
  have hinvL2 := m6_fullDenseInvW_with_scratch hinvU hscrL2_len (fuel' := sU.core.fuel)
  have hnvL2' : (k6StateOfScratch L scrL2).nv = nv := hnvL2.trans (hofM2.symm ▸ hnvS)
  have hhwmL2 : K6HwmClean L (s.scratch.glue_used[33]?.getD 0#32) (k6StateOfScratch L scrL2) :=
    m6_hwm_step hhw_le (by rw [hofM2]; exact hnvS) (by rw [hofM2]; exact hhwmS) htlL2
  have hconeL2 : M6SweepConeOk F_cur sL2 nv.toNat :=
    m6_coneOk_of_tailEq hconeU hL_len hL_mv hscrS_len hscrL2_len (hwsS.symm ▸ hKL2)
      (hnvL2'.trans hnv_ofNat)
  change wp _ _ _ _ _; c0_hsteps_nogrp; try dsimp only [Prod.fst]
  open scoped FullK6DynMem in m6_split
  · have hk_inc : (k6StateOfScratch L scrL2).incons ≠ 0#32 := by
      rw [m6_k6StateOfScratch_incons (by
        rw [hscrL2_len, ← hL_len]; unfold K6Layout.scrLen K6Layout.k6Fixed; omega)]
      exact ‹_›
    have huns_cur : (cnfOfClauses F_cur).Unsat :=
      m6_coneModelSet_unsat_of_empty (hKL2.clauses.incons_ok hk_inc)
    m6_steps
    exact hQ_ff _ _ (m6_fullDenseInvW_set_inconsistent hinvL2 huns_cur) hcvS hfuelS hreprS hwsS
      htmkS htrhS hws2S hguS hconeL2 (hguS.symm ▸ hhwmL2) hnvL2'
      (hinvL2.2.1.ext_sound.2 huns_cur) (by assumption)
  m6_call hRearm
  refine ⟨c, F0, F_cur, sL2, R, rfl, hinvL2, hmL2, fun flR mR _ hinvR hmR => ?_⟩
  let sR2 : FullState := { sL2 with core := { sL2.core with flags := flR } }
  m6_steps
  let sC2 : FullState :=
    { sR2 with scratch := { sR2.scratch with sweep_cnt := sR2.scratch.sweep_cnt + 1#64 } }
  have hinvC2 := m6_fullDenseInvW_set_sweep_cnt hinvR (sR2.scratch.sweep_cnt + 1#64)
  exact hJif _ ⟨hrb_le, sC2, hinvC2, hcvS, hfuelS, hreprS, hwsS, htmkS, htrhS, hws2S, hguS,
    hconeL2, hhwmL2, by assumption⟩

theorem full_m6_sweep_units_wp (Γ : Env)
    (hMaxV : Γ.Has "full_m6_max_v" m6MaxVSpec)
    (hFlip : Γ.Has "full_k6_flip" step13K6FlipSpec)
    (hRef : Γ.Has "full_m6_sweep_refine_sig" fullM6SweepRefineSigSpec)
    (hSolve : Γ.Has "full_m6_sweep_solve" fullM6SweepSolveSpec)
    (hAddU : Γ.Has "full_add_unit" fullAddUnitSpec)
    (hLive : Γ.Has "full_k512_add_live_m6" step13K6AddLiveSpec)
    (hRearm : Γ.Has "full_m6_sweep_rearm" fullM6SweepRearmSpec) :
    ∀ args m Q X, fullM6SweepUnitsSpec args m Q X →
      Func.wp Γ full_m6_sweep_units_body args m Q X := by
  rintro ⟨h, nv, rbit_in, tick_lim, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv, hcone, hrb_in, ⟨L, hL_len, hL_mv, hhwm0, hhw_le0⟩, hm, hQ⟩
  have hlen := hinv.1; have hcv_le := hlen.core_ok.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hscr_len := hlen.scratch_ok.scratch_buf_len
  obtain ⟨hK0, hnv_bv0, _⟩ :=
    m6SweepConeOk_to_k6Inv (hL_len.trans hscr_len.symm) (hscr_len.symm ▸ hL_mv) hcone
  have hnv_bv : (k6StateOfScratch L s.scratch.scratch_buf).nv = nv :=
    hnv_bv0.trans (BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt nv.isLt]))
  have hhw_le : s.scratch.glue_used[33]? = some 0xFFFFFFFF#32 ∨
      nv.toNat ≤ (s.scratch.glue_used[33]?.getD 0#32).toNat := by rwa [hnv_bv] at hhw_le0
  have hnv_ofNat : nv = BitVec.ofNat 32 nv.toNat :=
    BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt nv.isLt])
  have hcap : k6MinScr ≤ c.scratch_cap := hscr_len ▸ hcone.2.2.2.2.2.1
  have hnv_cv : nv.toNat ≤ s.core.cur_vars := hcone.2.2.1
  have hws_lt := hcone.2.2.2.1; have hnv_mx : nv.toNat ≤ 2 * c.max_vars := by omega
  let ws1 := s.scratch.work_stk1; let P := ConeModelSet F_cur ws1 nv.toNat
  have hmL := L.hmaxV; have haL := L.hacap
  have hnv_L : nv.toNat ≤ L.maxV := by rw [hL_mv, ← hscr_len]; exact hcone.2.1
  have hmv_eq := m6_mv32_eq (c := c) hL_mv
  have hkptr_c0 := m6_k6Ptr_eq (c := c) hL_mv (by omega)
  have hpm_c0 := m6_ptr_phtMerged L c.pScratchBuf
  have hpm_end : L.phtMerged + L.maxV = L.k6Base := by
    unfold K6Layout.phtMerged K6Layout.k6Base; omega
  have hass_c0 := k6_ptr_assump L (L.kPtr c.pScratchBuf)
  unfold Func.wp full_m6_sweep_units_body
  m6_steps
  refine m6_call_max_v hMaxV (m6_scrCap_lt64 c) ?_
  m6_to_group
  refine wp_join_group (ts := []) (fun () _ => False) (fun _ () _ h => False.elim h) ?_
  intro _ _
  m6_split
  · exfalso; have h0 := congrArg BitVec.toNat hc
    rw [hmv_eq, k6_mv32_toNat] at h0; simp at h0; omega
  m6_split
  · exfalso
    rw [← hL_mv, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc; omega
  m6_to_group
  refine wp_loop_inv (ts := [i32])
    (fun (i, ()) m1 => i.toNat ≤ nv.toNat ∧ ∃ scr1 : List (BitVec 32),
      scr1.length = c.scratch_cap ∧ k6StateOfScratch L scr1 =
        k6StateOfScratch L s.scratch.scratch_buf ∧
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr1 } } ⋆ R) m1)
    (fun (i, ()) _ => nv.toNat - i.toNat)
    (fun _ hJ0 => by
      m6_steps; exact hJ0 (0#32, ()) m ⟨Nat.zero_le _, s.scratch.scratch_buf, hscr_len, rfl, hm⟩)
    (fun _ (i, ()) m1 ⟨hi_le, scr1, hsl1, hof1, hm1⟩ hJ0 => by
      m6_split
      · have hi_lt : i.toNat < nv.toNat := hc
        have hi_mv : i.toNat < L.maxV := Nat.lt_of_lt_of_le hi_lt hnv_L
        have hi1 : (i + 1#32).toNat = i.toNat + 1 := m6_bv32_add1 (by omega)
        change wp _ _ _ _ _
        c0_hsteps_nogrp; try dsimp only [Prod.fst]; try rw [hmv_eq]; try rw [hpm_c0]
        open scoped M6PhtMem in m6_steps
        have hlt_k6 : L.phtMerged + i.toNat < L.k6Base := by omega
        exact hJ0 (i + 1#32, ()) m (by dsimp only; rw [hi1]; exact Nat.sub_lt_sub_left hi_lt (by
          omega))
          ⟨by omega, scr1.set (L.phtMerged + i.toNat) 0#32, List.length_set.trans hsl1,
           (m6_k6Inv_of_prefix_set hlt_k6).trans hof1, by assumption⟩
      · let s1 : FullState := { s with scratch := { s.scratch with scratch_buf := scr1 } }
        have hinv1 := m6_fullDenseInvW_with_scratch hinv hsl1 (fuel' := s.core.fuel)
        have hcone1 := m6_coneOk_of_tailEq hcone hL_len hL_mv hscr_len hsl1 (hof1 ▸ hK0)
          ((hof1 ▸ hnv_bv).trans hnv_ofNat)
        m6_to_group
        refine wp_join_group (ts := [i64]) (fun (_smask0, ()) ms => ms = m1)
          (fun _ (smask0, ()) ms hms => by
            subst ms; m6_to_group
            refine wp_loop_inv (ts := [i32, i32, i64])
              (fun (i, rbit, _smask, ()) ml => i.toNat ≤ nv.toNat ∧
                ∃ _ : M6UnitState c F0 F_cur s L nv rbit R ml, True)
              (fun (i, _, _, ()) _ => nv.toNat - i.toNat)
              (fun _ hJu => by
                m6_steps
                exact hJu (0#32, rbit_in, smask0, ()) m1
                  ⟨Nat.zero_le _, ⟨hrb_in, s1, hinv1, rfl, le_refl _, rfl, rfl, rfl, rfl, rfl,
                    rfl, hcone1, hof1 ▸ hhwm0, hm1⟩, trivial⟩)
              (fun _ (i, rbit, smask, ()) ml ⟨hi_le, U, _⟩ hJu => by
                clear hm hm1
                have hQ_ff : ∀ (s' : FullState) m',
                    FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
                    s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.core.repr = s.core.repr →
                    s'.scratch.work_stk1 = s.scratch.work_stk1 →
                    s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
                    s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
                    s'.scratch.work_stk2 = s.scratch.work_stk2 →
                    s'.scratch.glue_used = s.scratch.glue_used →
                    M6SweepConeOk F_cur s' nv.toNat →
                    K6HwmClean L (s'.scratch.glue_used[33]?.getD 0#32)
                      (k6StateOfScratch L s'.scratch.scratch_buf) →
                    (k6StateOfScratch L s'.scratch.scratch_buf).nv = nv →
                    F0.Unsat → (FullMem c s' ⋆ R) m' → Q (0xFFFFFFFFFFFFFFFF#64, ()) m' :=
                  fun s' m' hi hc' hf hr hw ht htr hw2 hg hcn hh hnv' hu hm' =>
                    hQ 0xFFFFFFFFFFFFFFFF#64 s' m' hi hc' hf hr hw ht htr hw2 hg hcn
                      ⟨L, hL_len, hL_mv, hh, by rw [hg, hnv']; exact hhw_le⟩
                      (fun _ => hu) (fun h => absurd rfl h) hm'
                m6_to_group
                refine wp_join_group (ts := []) (fun () m_ex => m_ex = ml)
                  (fun _ () m_ex hm_ex => by
                    subst hm_ex
                    have hm_ex_mem : (FullMem c U.st ⋆ R) m_ex := U.mem
                    have hscrU := U.inv.1.scratch_ok.scratch_buf_len
                    obtain ⟨_, hnvU0, _⟩ := m6SweepConeOk_to_k6Inv (hL_len.trans hscrU.symm)
                      (hscrU.symm ▸ hL_mv) U.cone
                    have hnvU : (k6StateOfScratch L U.st.scratch.scratch_buf).nv = nv :=
                      hnvU0.trans hnv_ofNat.symm
                    m6_to_group; refine wp_unroll_group fun _ _ => ?_
                    m6_split
                    · have huns := U.inv.2.1.ext_sound.2 (U.inv.2.1.inconsistent_sound hc)
                      m6_steps
                      exact hQ_ff U.st m_ex U.inv U.cv U.fuel U.repr U.ws U.tmk U.trh U.ws2 U.gu
                        U.cone (U.gu.symm ▸ U.hwm) hnvU huns hm_ex_mem
                    · m6_steps
                      have hrb64 : (rbit.setWidth 64).toNat ≤ 64 := by
                        rw [bv_c0_zext32_64]; exact U.rbit_le
                      have hne_ff : rbit.setWidth 64 ≠ 0xFFFFFFFFFFFFFFFF#64 := by
                        intro h; rw [h] at hrb64; revert hrb64; decide
                      exact hQ (rbit.setWidth 64) U.st m_ex U.inv U.cv U.fuel U.repr U.ws U.tmk
                        U.trh U.ws2 U.gu U.cone
                        ⟨L, hL_len, hL_mv, U.gu.symm ▸ U.hwm, by rw [U.gu, hnvU]; exact hhw_le⟩
                        (fun h => absurd h hne_ff) (fun _ => hrb64) hm_ex_mem)
                  (fun _ hJex => by
                    have hml := U.mem; have hlenL := U.inv.1
                    have hscrL_len := hlenL.scratch_ok.scratch_buf_len
                    m6_split; rotate_left; · m6_steps; exact hJex () ml rfl
                    m6_split; rotate_left; · m6_steps; exact hJex () ml rfl
                    m6_split; rotate_left; · m6_steps; exact hJex () ml rfl
                    change wp _ _ _ _ _
                    c0_hsteps_nogrp; try dsimp only [Prod.fst]; try rw [hkptr_c0]; try rw [hmv_eq]
                    open scoped FullK6DynMem in m6_split
                    rotate_left; · m6_steps; exact hJex () ml rfl
                    have hi_lt : i.toNat < nv.toNat := ‹_›
                    have hi_mv : i.toNat < L.maxV := Nat.lt_of_lt_of_le hi_lt hnv_L
                    have hi1 : (i + 1#32).toNat = i.toNat + 1 := m6_bv32_add1 (by omega)
                    have hwsL_len := hlenL.scratch_ok.work_stk1_len
                    obtain ⟨hKL0, hnvL0, _⟩ := m6SweepConeOk_to_k6Inv (hL_len.trans hscrL_len.symm)
                      (hscrL_len.symm ▸ hL_mv) U.cone
                    have hKL : K6Inv L P (k6StateOfScratch L U.st.scratch.scratch_buf) := by
                      dsimp only [P, ws1]; rw [← U.ws]; exact hKL0
                    have hnvL : (k6StateOfScratch L U.st.scratch.scratch_buf).nv = nv :=
                      hnvL0.trans hnv_ofNat.symm
                    have hi_ws : (i.setWidth 64).toNat < U.st.scratch.work_stk1.length := by
                      rw [hwsL_len, bv_c0_zext32_64]; omega
                    let gv := U.st.scratch.work_stk1[(i.setWidth 64).toNat]'hi_ws
                    have hgv_eq_ws : (ws1[i.toNat]?.getD 0#32).toNat = gv.toNat := by
                      dsimp only [gv, ws1]
                      rw [← U.ws, List.getElem?_eq_getElem (by rw [hwsL_len]; omega),
                        Option.getD_some]
                      exact congrArg BitVec.toNat (m6_list_getElem_congr (bv_c0_zext32_64 i)
                        (by rw [hwsL_len]; omega) (by rw [hwsL_len]; omega)).symm
                    have hgv_lt : gv.toNat < s.core.cur_vars := by
                      rw [← hgv_eq_ws]; exact hws_lt i.toNat hi_lt
                    have hgv_fl : (gv.setWidth 64).toNat < U.st.core.flags.length := by
                      rw [hlenL.core_ok.flags_len, bv_c0_zext32_64]; omega
                    have h2gv_lt : ((gv <<< (1 : Nat)).setWidth 64).toNat < U.st.core.vals.length :=
                      by rw [hlenL.core_ok.vals_len, bv_c0_zext32_64, m6_bv32_shl1_lt (by omega)]
                         omega
                    m6_to_group
                    refine wp_join_group (ts := []) (fun () mM => mM = ml)
                      (fun _ () mM hmM => by
                        subst mM; change wp _ _ _ _ _
                        c0_hsteps_nogrp; try dsimp only [Prod.fst]; try rw [hmv_eq]; try rw [hpm_c0]
                        open scoped M6PhtMem in m6_steps
                        have hlt_k6 : L.phtMerged + i.toNat < L.k6Base := by omega
                        let scrM := U.st.scratch.scratch_buf.set (L.phtMerged + i.toNat) 1#32
                        let sM : FullState :=
                          { U.st with scratch := { U.st.scratch with scratch_buf := scrM } }
                        have hslM : scrM.length = c.scratch_cap := List.length_set.trans hscrL_len
                        have hofM : k6StateOfScratch L scrM =
                            k6StateOfScratch L U.st.scratch.scratch_buf :=
                          m6_k6Inv_of_prefix_set hlt_k6
                        exact hJu (i + 1#32, rbit, smask, ()) _
                          (by dsimp only; rw [hi1]; exact Nat.sub_lt_sub_left hi_lt (by omega))
                          ⟨by omega, ⟨U.rbit_le, sM, m6_fullDenseInvW_with_scratch U.inv hslM
                            (fuel' := U.st.core.fuel), U.cv, U.fuel, U.repr, U.ws, U.tmk, U.trh,
                            U.ws2, U.gu, m6_coneOk_of_tailEq U.cone hL_len hL_mv hscrL_len hslM
                              (hofM.symm ▸ hKL0) (hofM.symm ▸ hnvL0),
                            hofM ▸ U.hwm, by assumption⟩, trivial⟩)
                      (fun _ hJ_m => by
                        m6_split; · m6_steps; exact hJ_m () ml rfl
                        m6_split; · m6_steps; exact hJ_m () ml rfl
                        have hgv_sig : (gv.setWidth 64).toNat < U.st.scratch.sim_sig.length := by
                          rw [hlenL.scratch_ok.sim_sig_len, bv_c0_zext32_64]; omega
                        m6_to_group
                        refine wp_join_group (ts := [i32, i64])
                          (fun (rbitN, _smaskN, ()) mN =>
                            ∃ _ : M6UnitState c F0 F_cur s L nv rbitN R mN, True)
                          (fun _ (rbitN, smaskN, ()) mN ⟨hN, _⟩ => by
                            m6_steps
                            exact hJu (i + 1#32, rbitN, smaskN, ()) mN
                              (by dsimp only; rw [hi1]; exact Nat.sub_lt_sub_left hi_lt (by omega))
                              ⟨by omega, hN, trivial⟩)
                          (fun _ hJif => by
                            refine wp_join_group (ts := []) (fun () mdo => mdo = ml)
                              (fun _ () mdo hmdo => by
                                subst mdo; m6_to_group
                                refine wp_join_group (ts := [i32])
                                  (fun (wf, ()) mwf => mwf = ml ∧ (wf = 0#32 ∨ wf = 1#32))
                                  (fun _ (wf, ()) mwf ⟨hmwf, hwf⟩ => by
                                    subst mwf
                                    let test_lit : BitVec 32 := (i <<< (1 : Nat)) ||| wf
                                    obtain ⟨htl_eq, hgl_lift, hgl_eq⟩ :=
                                      m6_unit_lit_align (by omega) (by omega) hgv_eq_ws hwf
                                    have hwf_lt : wf.toNat < 2 := by
                                      rcases hwf with rfl | rfl <;> decide
                                    have htl_lt : test_lit.toNat < 2 * nv.toNat := by
                                      dsimp only [test_lit]; omega
                                    have htl_x_to :
                                        (test_lit ^^^ 1#32).toNat = test_lit.toNat ^^^ 1 := by simp
                                    have htl_x_lt : (test_lit ^^^ 1#32).toNat < 2 * nv.toNat := by
                                      rw [htl_x_to, m6_nat_xor1_cases]; split <;> omega
                                    m6_steps; m6_call hFlip
                                    refine ⟨c, U.st, P, L, R, rfl, hlenL, hL_len, hL_mv, hKL,
                                      by rw [hnvL]; exact htl_x_lt, hml,
                                      fun okF scrF mF hlenF _ hKF hnvF htlF _ _ _ hmF => ?_⟩
                                    let sF : FullState :=
                                      { U.st with scratch := { U.st.scratch with
                                        scratch_buf := scrF } }
                                    have hscrF_len := hlenF.scratch_ok.scratch_buf_len
                                    have hinvF := m6_fullDenseInvW_with_scratch U.inv hscrF_len
                                      (fuel' := U.st.core.fuel)
                                    have hnvF' : (k6StateOfScratch L scrF).nv = nv :=
                                      hnvF.trans hnvL
                                    have hhwmF := m6_hwm_step hhw_le hnvL U.hwm htlF
                                    have hconeF := m6_coneOk_of_tailEq U.cone hL_len hL_mv
                                      hscrL_len hscrF_len (U.ws.symm ▸ hKF) (hnvF'.trans hnv_ofNat)
                                    m6_split
                                    · m6_to_group; refine wp_unroll_group fun _ _ => ?_
                                      m6_split; rotate_left
                                      · m6_steps
                                        exact hJif (rbit, smask, ()) mF
                                          ⟨⟨U.rbit_le, sF, hinvF, U.cv, U.fuel, U.repr, U.ws,
                                            U.tmk, U.trh, U.ws2, U.gu, hconeF, hhwmF, hmF⟩,
                                            trivial⟩
                                      have hrb_lt : rbit.toNat < 64 := ‹_›
                                      have hrb1 : (rbit + 1#32).toNat = rbit.toNat + 1 :=
                                        m6_bv32_add1 (by omega)
                                      m6_call hRef
                                      refine ⟨c, sF, R, rfl, hlenF, hcap,
                                        by rw [← hL_mv]; exact hnv_L, hnv_mx,
                                        fun j hj => by rw [U.ws, U.cv]; exact hws_lt j hj, hmF,
                                        fun sigR mR hsigR hmR => ?_⟩
                                      let sR : FullState :=
                                        { sF with scratch := { sF.scratch with sim_sig := sigR } }
                                      m6_steps
                                      exact hJif (rbit + 1#32, _, ()) mR
                                        ⟨⟨by omega, sR, m6_fullDenseInvW_with_sig hinvF hsigR,
                                          U.cv, U.fuel, U.repr, U.ws, U.tmk, U.trh, U.ws2, U.gu,
                                          hconeF, hhwmF, hmR⟩, trivial⟩
                                    · obtain ⟨Rfr, hRfr⟩ :
                                          ∃ Rfr : Mem 64 → Prop, Rfr = (FullK6Frame c L sF ⋆ R) :=
                                        ⟨_, rfl⟩
                                      have hm_ka : (K6MemA L (L.kPtr c.pScratchBuf)
                                          (k6StateOfScratch L scrF) ⋆ Rfr) mF := by
                                        change (FullMem c sF ⋆ R) mF at hmF
                                        rw [fullMem_eq_k6Frame (hscrF_len.trans hL_len.symm)] at hmF
                                        rw [hRfr]; exact k6Mem_to_amem hKF.shapes (sep_ac hmF)
                                      change wp _ _ _ _ _; c0_hsteps
                                      try dsimp only [Prod.fst]
                                      try rw [hkptr_c0]; try rw [hmv_eq]; try rw [hass_c0]
                                      open scoped K6MemATactics K6PtrTactics FullK6DynMem
                                        M6UnitMem in c0_hsteps!
                                      obtain ⟨hKA, hnvA, htlA, hassA, _⟩ := k6Inv_set_assump1
                                        (by rw [hnvF']; exact htl_lt) hKF
                                      rw [hRfr] at hm
                                      let ksA := ((k6StateOfScratch L scrF).putHdr .nassump
                                        1#32).putArr .assump 0 test_lit
                                      let scrA := scrF.take L.k6Base ++ ksA.toSlab
                                      let sA : FullState :=
                                        { sF with scratch := { sF.scratch with
                                          scratch_buf := scrA } }
                                      obtain ⟨hscrA_len, _, hofA, hmA⟩ :=
                                        m6_join_k6_ofSlab (s := sF) hL_len hscrF_len hKA.shapes hm
                                      have hlenA : sA.LengthsOk c :=
                                        ⟨hlenF.core_ok,
                                         { hlenF.scratch_ok with scratch_buf_len := hscrA_len }⟩
                                      have hnvA' : (k6StateOfScratch L scrA).nv = nv := by
                                        rw [hofA]; exact hnvA.trans hnvF'
                                      have hhwmA : K6HwmClean L (s.scratch.glue_used[33]?.getD 0#32)
                                          (k6StateOfScratch L scrA) :=
                                        hofA.symm ▸ m6_hwm_step hhw_le hnvF' hhwmF htlA
                                      have hassA' : k6AssumpLitsS L scrA = [test_lit.toNat] := by
                                        unfold k6AssumpLitsS; rw [hofA]; exact hassA
                                      m6_call hSolve
                                      refine ⟨c, sA, P, L, R, rfl, hlenA, hL_len, hL_mv,
                                        hofA ▸ hKA, hnvA', hmA,
                                        fun d fuelS scrS mS hlenS hfuelS _ hKS _ hnvS htlS _
                                          hassS _ _ hunsS hmS => ?_⟩
                                      let sS : FullState :=
                                        { sA with
                                          core := { sA.core with fuel := fuelS }
                                          scratch := { sA.scratch with scratch_buf := scrS } }
                                      have hscrS_len := hlenS.scratch_ok.scratch_buf_len
                                      have hinvS := m6_fullDenseInvW_with_scratch U.inv hscrS_len
                                        (fuel' := fuelS)
                                      have hfuelS0 := Nat.le_trans hfuelS U.fuel
                                      have hhwmS := m6_hwm_step hhw_le hnvA' hhwmA htlS
                                      have hconeS := m6_coneOk_of_tailEq U.cone hL_len hL_mv
                                        hscrL_len hscrS_len (U.ws.symm ▸ hKS) (hnvS.trans hnv_ofNat)
                                      m6_to_group; refine wp_unroll_group fun _ _ => ?_
                                      m6_split
                                      · have huns_t :
                                            ∀ β, P β → ¬ (unitsCnf [test_lit.toNat]).Sat β :=
                                          fun β hβ => by
                                            have := hunsS hc β hβ; rwa [hassS, hassA'] at this
                                        obtain ⟨hsem_u, hent_u⟩ :=
                                          m6_coneModelSet_unsat_unit htl_lt huns_t
                                        have hgl_ltS : ((gv <<< (1 : Nat)) ||| (1#32 - wf)).toNat <
                                            2 * sS.core.cur_vars := by
                                          change _ < 2 * U.st.core.cur_vars
                                          rw [hgl_eq, U.cv]; omega
                                        change wp _ _ _ _ _
                                        try rw [hkptr_c0]; try rw [hmv_eq]; try rw [hpm_c0]
                                        exact m6_unit_d20_wp hAddU hLive hRearm hQ_ff rfl rfl hpm_c0
                                          hL_len hL_mv hhw_le hinvS U.rbit_le U.cv hfuelS0 U.repr
                                          U.ws U.tmk U.trh U.ws2 U.gu hconeS hKS hnvS hhwmS hi_mv
                                          htl_x_lt hgl_ltS (by rw [hgl_lift]; exact hent_u)
                                          (by rw [htl_x_to]; exact hsem_u) hmS
                                          (fun m' u' => by
                                            m6_steps; exact hJif (rbit, smask, ()) m' ⟨u', trivial⟩)
                                      · m6_to_group; refine wp_unroll_group fun _ _ => ?_
                                        m6_split; rotate_left
                                        · m6_steps
                                          exact hJif (rbit, smask, ()) mS
                                            ⟨⟨U.rbit_le, sS, hinvS, U.cv, hfuelS0, U.repr, U.ws,
                                              U.tmk, U.trh, U.ws2, U.gu, hconeS, hhwmS, hmS⟩,
                                              trivial⟩
                                        m6_split; rotate_left
                                        · m6_steps
                                          exact hJif (rbit, smask, ()) mS
                                            ⟨⟨U.rbit_le, sS, hinvS, U.cv, hfuelS0, U.repr, U.ws,
                                              U.tmk, U.trh, U.ws2, U.gu, hconeS, hhwmS, hmS⟩,
                                              trivial⟩
                                        have hrb_lt : rbit.toNat < 64 := ‹_›
                                        have hrb1 : (rbit + 1#32).toNat = rbit.toNat + 1 :=
                                          m6_bv32_add1 (by omega)
                                        m6_call hRef
                                        refine ⟨c, sS, R, rfl, hlenS, hcap,
                                          by rw [← hL_mv]; exact hnv_L, hnv_mx,
                                          fun j hj => by rw [U.ws, U.cv]; exact hws_lt j hj, hmS,
                                          fun sigR mR hsigR hmR => ?_⟩
                                        let sR : FullState :=
                                          { sS with scratch := { sS.scratch with sim_sig := sigR } }
                                        m6_steps
                                        exact hJif (rbit + 1#32, _, ()) mR
                                          ⟨⟨by omega, sR, m6_fullDenseInvW_with_sig hinvS hsigR,
                                            U.cv, hfuelS0, U.repr, U.ws, U.tmk, U.trh, U.ws2,
                                            U.gu, hconeS, hhwmS, hmR⟩, trivial⟩)
                                  (fun _ hJwf => by
                                    m6_split
                                    · m6_steps; exact hJwf (0#32, ()) ml ⟨rfl, Or.inl rfl⟩
                                    · m6_steps; exact hJwf (1#32, ()) ml ⟨rfl, Or.inr rfl⟩))
                              (fun _ hJdo => by
                                m6_split; · m6_steps; exact hJdo () ml rfl
                                m6_split; · m6_steps; exact hJdo () ml rfl
                                m6_steps; exact hJif (rbit, smask, ()) ml ⟨U, trivial⟩))))))
          (fun _ hJsm => by
            m6_split
            · m6_steps; exact hJsm _ m1 rfl
            · m6_steps; exact hJsm _ m1 rfl))

/-! ## 3. `full_m6_sweep_var_wp` (`3/5`) -/

private theorem m6_sweep_tmk_clear_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {sX : FullState}
    {R : Mem 64 → Prop} {nv : BitVec 32} {ws1' tmk' : List (BitVec 32)}
    {pWorkStk1 pTarjanMark : BitVec 64} {mX : Mem 64} {cont : Expr Val Cont rs}
    (hpws : pWorkStk1 = c.pWorkStk1) (hptmk : pTarjanMark = c.pTarjanMark)
    (hnv_mx : nv.toNat ≤ 2 * c.max_vars) (hinvX : FullDenseInvW c F0 F_cur sX)
    (hwsX : sX.scratch.work_stk1 = ws1') (htmkX : sX.scratch.tarjan_mark = tmk')
    (hconeX : ∀ i < nv.toNat, (sX.scratch.work_stk1[i]?.getD 0#32).toNat < sX.core.cur_vars)
    (htmk1' : ∀ u < sX.core.cur_vars, tmk'[u]?.getD 0#32 ≠ 0#32 →
      ∃ k < nv.toNat, (ws1'[k]?.getD 0#32).toNat = u)
    (hmX : (FullMem c sX ⋆ R) mX)
    (hcont : ∀ (tmk_c : List (BitVec 32)) m_end,
      tmk_c.length = 2 * c.max_vars →
      M6TmkZero { sX with scratch := { sX.scratch with tarjan_mark := tmk_c } } →
      (FullMem c { sX with scratch := { sX.scratch with tarjan_mark := tmk_c } } ⋆ R) m_end →
      wp Γ Q X cont m_end) :
    wp Γ Q X
      (Expr.group (sig := [[i32]])
        (fun Js => Blocks.cons (fun (p : Tup Val [i32]) =>
          Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i32) (Arg.var p.fst, Arg.var nv, ())) fun p1 =>
          Expr.jnz (Arg.var p1.fst)
            (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p.fst, ())) fun p2 =>
             Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p2.fst, Arg.imm 4, ())) fun p3 =>
             Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pWorkStk1, Arg.var p3.fst, ())) fun p4 =>
             Expr.load i32 (Arg.var p4.fst) fun ld =>
             Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld, ())) fun p5 =>
             Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p5.fst, Arg.imm 4, ())) fun p6 =>
             Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pTarjanMark, Arg.var p6.fst, ())) fun p7 =>
             Expr.store (t := i32) (Arg.imm 0) (Arg.var p7.fst)
               (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var p.fst, Arg.imm 1, ())) fun p8 =>
                 Expr.jump Js.fst (Arg.var p8.fst, ())))
            cont) Blocks.nil)
        (fun Js => Expr.jump Js.fst (Arg.imm 0, ()))) mX := by
  subst hpws hptmk
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hws_len := hinvX.1.scratch_ok.work_stk1_len
  have hcvX_le := hinvX.1.core_ok.cur_vars_le
  have htmkX_sym : tmk' = sX.scratch.tarjan_mark := htmkX.symm
  refine wp_loop_inv (ts := [i32])
    (fun (i, ()) mi => i.toNat ≤ nv.toNat ∧ ∃ tmk_c : List (BitVec 32),
      tmk_c.length = 2 * c.max_vars ∧
      (∀ u < sX.core.cur_vars, tmk_c[u]?.getD 0#32 ≠ 0#32 →
        ∃ k, i.toNat ≤ k ∧ k < nv.toNat ∧ (ws1'[k]?.getD 0#32).toNat = u) ∧
      (FullMem c { sX with scratch := { sX.scratch with tarjan_mark := tmk_c } } ⋆ R) mi)
    (fun (i, ()) _ => nv.toNat - i.toNat)
    (fun _ hLc => by
      m6_steps
      exact hLc (0#32, ()) mX ⟨Nat.zero_le _, tmk', htmkX ▸ hinvX.1.scratch_ok.tarjan_mark_len,
        fun u hu hne => let ⟨k, hk, hwk⟩ := htmk1' u hu hne; ⟨k, Nat.zero_le _, hk, hwk⟩,
        htmkX_sym ▸ hmX⟩)
    (fun _ (i, ()) mi ⟨hi_le, tmk_c, ht_len, ht_inv, hmi⟩ hLc => by
      m6_split
      · have hi_lt : i.toNat < nv.toNat := hc
        have hws_bd : i.toNat < ws1'.length := by rw [← hwsX, hws_len]; omega
        have hv_lt : (ws1'[i.toNat]'hws_bd).toNat < 2 * c.max_vars := by
          have := hconeX i.toNat hi_lt
          rw [hwsX, List.getElem?_eq_getElem hws_bd, Option.getD_some] at this; omega
        have hi_ws : (BitVec.setWidth 64 i).toNat <
            ({ sX with scratch := { sX.scratch with tarjan_mark := tmk_c } } :
              FullState).scratch.work_stk1.length := by
          change (BitVec.setWidth 64 i).toNat < sX.scratch.work_stk1.length
          rw [hws_len, bv_c0_zext32_64]; omega
        have hcur_eq : ({ sX with scratch := { sX.scratch with tarjan_mark := tmk_c } } :
            FullState).scratch.work_stk1[(BitVec.setWidth 64 i).toNat]'hi_ws =
            ws1'[i.toNat]'hws_bd := by
          change sX.scratch.work_stk1[(BitVec.setWidth 64 i).toNat]'hi_ws = _
          have h1 : sX.scratch.work_stk1[(BitVec.setWidth 64 i).toNat]'hi_ws =
              sX.scratch.work_stk1[i.toNat]'(by rw [hws_len]; omega) := Option.some.inj (by
            rw [← List.getElem?_eq_getElem hi_ws,
              ← List.getElem?_eq_getElem (by rw [hws_len]; omega), bv_c0_zext32_64])
          rw [h1]; cases hwsX; rfl
        have hgv_tmk : (BitVec.setWidth 64 (({ sX with scratch :=
            { sX.scratch with tarjan_mark := tmk_c } } :
            FullState).scratch.work_stk1[(BitVec.setWidth 64 i).toNat]'hi_ws)).toNat <
            ({ sX with scratch := { sX.scratch with tarjan_mark := tmk_c } } :
              FullState).scratch.tarjan_mark.length := by
          change (BitVec.setWidth 64 _).toNat < tmk_c.length
          rw [hcur_eq, bv_c0_zext32_64, ht_len]; exact hv_lt
        have hi1 : (i + 1#32).toNat = i.toNat + 1 := m6_bv32_add1 (by omega)
        m6_steps
        refine hLc (i + 1#32, ()) _ (by dsimp only; rw [hi1]; exact Nat.sub_lt_sub_left hi_lt (by
          omega)) ⟨by omega, _, List.length_set.trans ht_len, fun u hu hne => ?_, by assumption⟩
        rw [hcur_eq, bv_c0_zext32_64] at hne
        by_cases huv : u = (ws1'[i.toNat]'hws_bd).toNat
        · rw [huv, List.getElem?_set_self (by rw [ht_len]; exact hv_lt)] at hne
          exact absurd rfl hne
        · rw [List.getElem?_set_ne (Ne.symm huv)] at hne
          obtain ⟨k, hk1, hk2, hwk⟩ := ht_inv u hu hne
          have hkne : k ≠ i.toNat := by
            rintro rfl; rw [List.getElem?_eq_getElem hws_bd, Option.getD_some] at hwk
            exact huv hwk.symm
          exact ⟨k, by omega, hk2, hwk⟩
      · refine hcont tmk_c mi ht_len (fun u hu => ?_) hmi
        exact Classical.byContradiction fun hne => by
          obtain ⟨k, hk1, hk2, _⟩ := ht_inv u hu hne; omega)

theorem full_m6_sweep_var_wp (Γ : Env)
    (hMaxV : Γ.Has "full_m6_max_v" m6MaxVSpec)
    (hFind : Γ.Has "full_cong_find" fullCongFindSpec)
    (hCone : Γ.Has "full_m6_sweep_cone" fullM6SweepConeSpec)
    (hSim : Γ.Has "full_m6_sweep_sim" fullM6SweepSimSpec)
    (hUnits : Γ.Has "full_m6_sweep_units" fullM6SweepUnitsSpec)
    (hClasses : Γ.Has "full_m6_sweep_classes" fullM6SweepClassesSpec)
    (hEls : Γ.Has "full_m6_dense_els" fullM6DenseElsSpec) :
    ∀ args m Q X, fullM6SweepVarSpec args m Q X →
      Func.wp Γ full_m6_sweep_var_body args m Q X := by
  rintro ⟨h, root_v, tick_lim, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv, hcap, hroot, htmk, hrepr, ⟨L, hL_len, hL_mv, hhwm0⟩, hm, hQ⟩
  have hcv_le := hinv.1.core_ok.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hmL := L.hmaxV; have haL := L.hacap
  have hmv_eq := m6_mv32_eq (c := c) hL_mv
  have hkptr_c0 := m6_k6Ptr_eq (c := c) hL_mv (by omega)
  unfold Func.wp full_m6_sweep_var_body
  m6_steps
  refine m6_call_max_v hMaxV (m6_scrCap_lt64 c) ?_
  m6_split
  · exfalso; have h0 := congrArg BitVec.toNat hc
    rw [hmv_eq, k6_mv32_toNat] at h0; simp at h0; omega
  have hrl0_lt : (root_v <<< (1 : Nat)).toNat < 2 * s.core.cur_vars := by
    rw [m6_bv32_shl1_lt (by omega)]; omega
  m6_steps; m6_call hFind
  refine ⟨F_cur, 2 * s.core.cur_vars, s.core.repr, ArrayField.repr.rest c s ⋆ R, hrepr, hrl0_lt,
    ArrayField.repr.focus hm, fun r0 repr0 m0 hrepr0_len hrepr0 _ _ _ hm0_f => ?_⟩
  let s0 : FullState := { s with core := { s.core with repr := repr0 } }
  have hm0 : (FullMem c s0 ⋆ R) m0 := ArrayField.repr.unfocus hm0_f
  have hinv0 := m6_fullDenseInvW_set_repr hinv (hrepr0_len.trans hinv.1.core_ok.repr_len)
  m6_split
  · m6_steps
    exact hQ 1#64 s0 m0 hinv0 rfl (le_refl _) htmk hrepr0 rfl (fun _ _ _ => rfl)
      ⟨L, hL_len, hL_mv, hhwm0⟩ (Or.inl rfl) (fun h => by cases h) hm0
  m6_call hCone
  refine ⟨c, F0, F_cur, s0, R, rfl, hinv0, hcap, hroot, htmk, ⟨L, hL_len, hL_mv, hhwm0⟩, hm0,
    fun pk tmp' ws1' tmk' scr' gu' m1 hinv1 hcv1 hfuel1 _ _ hcone1 _ _ hgu1
      ⟨L1, hL1_len, hL1_mv, hhwm1, hhw_ge2⟩ htmk1 hm1 => ?_⟩
  have hL1_eq : L1 = L := K6Layout.eq_of_scrLen_maxV (hL1_len.trans hL_len.symm)
    (hL1_mv.trans hL_mv.symm)
  subst L1
  let s1 : FullState :=
    { s0 with core := { s0.core with tmp := tmp' }
              scratch := { s0.scratch with work_stk1 := ws1', tarjan_mark := tmk',
                                           scratch_buf := scr', glue_used := gu' } }
  let nv : BitVec 32 := (pk &&& 0xFFFF#64).setWidth 32
  have hnv_eq : nv.toNat = (pk &&& 0xFFFF#64).toNat := by
    dsimp only [nv]; rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by
      have := hcone1.2.1; have hscr1 := hinv1.1.scratch_ok.scratch_buf_len
      rw [hscr1, ← hL_mv] at this; omega)]
  have hcone1' : M6SweepConeOk F_cur s1 nv.toNat := by rw [hnv_eq]; exact hcone1
  clear hcone1
  have hnv_mx : nv.toNat ≤ 2 * c.max_vars := by
    have := hcone1'.2.2.1; change nv.toNat ≤ s.core.cur_vars at this; omega
  have htmk1' : ∀ u < s.core.cur_vars, tmk'[u]?.getD 0#32 ≠ 0#32 →
      ∃ k < nv.toNat, (ws1'[k]?.getD 0#32).toNat = u := fun u hu hne =>
    let ⟨k, hk, hwk⟩ := htmk1 u hu hne; ⟨k, hnv_eq ▸ hk, hwk⟩
  have hws_ok1 := hcone1'.2.2.2.1
  have hscr1_len := hinv1.1.scratch_ok.scratch_buf_len
  change wp _ _ _ _ _
  c0_hsteps_nogrp; try dsimp only [Prod.fst]; try rw [hkptr_c0]; try rw [hmv_eq]
  open scoped FullK6DynMem in m6_split
  · obtain ⟨hK1, _, _⟩ := m6SweepConeOk_to_k6Inv (hL_len.trans hscr1_len.symm)
      (hscr1_len.symm ▸ hL_mv) hcone1'
    have hk_inc : (k6StateOfScratch L scr').incons ≠ 0#32 := by
      rw [m6_k6StateOfScratch_incons (by
        rw [hscr1_len, ← hL_len]; unfold K6Layout.scrLen K6Layout.k6Fixed; omega)]
      dsimp only [s1] at *; assumption
    have huns_cur := m6_coneModelSet_unsat_of_empty (hK1.clauses.incons_ok hk_inc)
    m6_to_group
    exact m6_sweep_tmk_clear_wp rfl rfl hnv_mx hinv1 rfl rfl hws_ok1 htmk1' hm1
      fun tmk_c m_end ht_len ht_done hm_end => by
        m6_steps
        exact hQ 20#64 _ _ (m6_fullDenseInvW_set_inconsistent
          (m6_fullDenseInvW_with_tmk hinv1 ht_len) huns_cur) hcv1 (hfuel1 ▸ le_refl _) ht_done
          hrepr0 rfl hgu1 ⟨L, hL_len, hL_mv, hhwm1⟩ (Or.inr rfl)
          (fun _ => hinv1.2.1.ext_sound.2 huns_cur) (by assumption)
  m6_to_group
  refine wp_join_group (ts := []) (fun () mJ => mJ = m1)
    (fun _ () mJ hmJ => by
      subst hmJ; m6_to_group
      exact m6_sweep_tmk_clear_wp rfl rfl hnv_mx hinv1 rfl rfl hws_ok1 htmk1' hm1
        fun tmk_c m_end ht_len ht_done hm_end => by
          m6_steps
          exact hQ 1#64 _ m_end (m6_fullDenseInvW_with_tmk hinv1 ht_len) hcv1 (hfuel1 ▸ le_refl _)
            ht_done hrepr0 rfl hgu1 ⟨L, hL_len, hL_mv, hhwm1⟩ (Or.inl rfl) (fun h => by cases h)
            hm_end)
    (fun _ hJearly => by
      m6_split; · m6_steps; exact hJearly () m1 rfl
      have hnv_ge2 : 2 ≤ (pk &&& 0xFFFF#64).toNat := by
        have : ¬ nv.toNat < 2 := hc; omega
      m6_split; · m6_steps; exact hJearly () m1 rfl
      obtain ⟨_, _, hks1_nv⟩ := m6SweepConeOk_to_k6Inv (hL_len.trans hscr1_len.symm)
        (hscr1_len.symm ▸ hL_mv) hcone1'
      have hhw_le1 : gu'[33]? = some 0xFFFFFFFF#32 ∨
          (k6StateOfScratch L scr').nv.toNat ≤ (gu'[33]?.getD 0#32).toNat := by
        rw [hks1_nv, hnv_eq]; exact hhw_ge2 hnv_ge2
      m6_call hSim
      refine ⟨c, F0, F_cur, s1, R, rfl, hinv1, hcone1', ⟨L, hL_len, hL_mv, hhwm1, hhw_le1⟩, hm1,
        fun rbit fuel2 sig2 scr2 m2 hinv2 hfuel2 hcone2 hhwm2_ex huns2 hrb_le2 hm2 => ?_⟩
      clear hcone1'
      let s2 : FullState :=
        { s1 with core := { s1.core with fuel := fuel2 }
                  scratch := { s1.scratch with sim_sig := sig2, scratch_buf := scr2 } }
      have hfuel2_0 : fuel2.toNat ≤ s.core.fuel.toNat := hfuel1 ▸ hfuel2
      m6_split
      · have huns_cur := huns2 (by bv_omega)
        obtain ⟨L2, hL2_len, hL2_mv, hhwm2, _⟩ := hhwm2_ex
        m6_to_group
        exact m6_sweep_tmk_clear_wp rfl rfl hnv_mx hinv2 rfl rfl hcone2.2.2.2.1 htmk1' hm2
          fun tmk_c m_end ht_len ht_done hm_end => by
            m6_steps
            exact hQ 20#64 _ _ (m6_fullDenseInvW_set_inconsistent
              (m6_fullDenseInvW_with_tmk hinv2 ht_len) huns_cur) hcv1 hfuel2_0 ht_done hrepr0 rfl
              hgu1 ⟨L2, hL2_len, hL2_mv, hhwm2⟩ (Or.inr rfl)
              (fun _ => hinv2.2.1.ext_sound.2 huns_cur) (by assumption)
      have hrb_64 : rbit.toNat ≤ 64 := hrb_le2 (by bv_omega)
      m6_split
      · obtain ⟨L2, hL2_len, hL2_mv, hhwm2, _⟩ := hhwm2_ex
        m6_to_group
        exact m6_sweep_tmk_clear_wp rfl rfl hnv_mx hinv2 rfl rfl hcone2.2.2.2.1 htmk1' hm2
          fun tmk_c m_end ht_len ht_done hm_end => by
            m6_steps
            exact hQ 1#64 _ m_end (m6_fullDenseInvW_with_tmk hinv2 ht_len) hcv1 hfuel2_0 ht_done
              hrepr0 rfl hgu1 ⟨L2, hL2_len, hL2_mv, hhwm2⟩ (Or.inl rfl) (fun h => by cases h) hm_end
      m6_call hUnits
      refine ⟨c, F0, F_cur, s2, R, rfl, hinv2, hcone2, hrb_64, hhwm2_ex, hm2,
        fun ur s3 m3 hinv3 hcv3 hfuel3 hrepr3 hws3 htmk3 htrh3 _ hgu3 hcone3 hhwm3_ex huns3
          hur_le3 hm3 => ?_⟩
      clear hcone2
      have hfuel3_0 := Nat.le_trans hfuel3 hfuel2_0
      have hcv3_0 := hcv3.trans hcv1
      have hrepr3_inv : FullCongReprInv F_cur (2 * s3.core.cur_vars) s3.core.repr := by
        rw [hcv3_0, hrepr3]; exact hrepr0
      have hgu3_0 : ∀ i < 64, i ≠ 33 → s3.scratch.glue_used[i]? = s.scratch.glue_used[i]? :=
        fun i hi hne => by rw [hgu3]; exact hgu1 i hi hne
      m6_split
      · obtain ⟨L3, hL3_len, hL3_mv, hhwm3, _⟩ := hhwm3_ex
        m6_to_group
        exact m6_sweep_tmk_clear_wp rfl rfl hnv_mx hinv3 hws3 htmk3 hcone3.2.2.2.1
          (fun u hu => htmk1' u (hcv3_0 ▸ hu)) hm3 fun tmk_c m_end ht_len ht_done hm_end => by
            m6_steps
            exact hQ 20#64 _ m_end (m6_fullDenseInvW_with_tmk hinv3 ht_len) hcv3_0 hfuel3_0
              ht_done hrepr3_inv htrh3 hgu3_0 ⟨L3, hL3_len, hL3_mv, hhwm3⟩ (Or.inr rfl)
              (fun _ => huns3 (by bv_omega)) hm_end
      have hur_64 : (ur.setWidth 32).toNat ≤ 64 := by
        have h1 := hur_le3 (by bv_omega)
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact h1
      m6_steps; m6_call hClasses
      refine ⟨c, F0, F_cur, s3, R, rfl, hinv3, hcone3, hur_64, hhwm3_ex, hm3,
        fun cr s4 m4 hinv4 hcv4 hfuel4 hrepr4 hws4 htmk4 htrh4 hgu4 hhwm4_ex hcr_dom hcr_uns
          hcr_eq hm4 => ?_⟩
      clear hcone3
      have hfuel4_0 := Nat.le_trans hfuel4 hfuel3_0
      have hcv4_0 := hcv4.trans hcv3_0
      have hrepr4_inv : FullCongReprInv F_cur (2 * s4.core.cur_vars) s4.core.repr := by
        rw [hcv4, hrepr4]; exact hrepr3_inv
      have hws4_0 := hws4.trans hws3
      have htmk4_0 := htmk4.trans htmk3
      have htrh4_0 := htrh4.trans htrh3
      have hgu4_0 : ∀ i < 64, i ≠ 33 → s4.scratch.glue_used[i]? = s.scratch.glue_used[i]? :=
        fun i hi hne => by rw [hgu4]; exact hgu3_0 i hi hne
      have hws_ok4 : ∀ i < nv.toNat, (s4.scratch.work_stk1[i]?.getD 0#32).toNat <
          s4.core.cur_vars := fun i hi => by rw [hws4_0, hcv4_0]; exact hws_ok1 i hi
      m6_to_group
      exact m6_sweep_tmk_clear_wp rfl rfl hnv_mx hinv4 hws4_0 htmk4_0 hws_ok4
        (fun u hu => htmk1' u (hcv4_0 ▸ hu)) hm4 fun tmk_c m_end ht_len ht_done hm_end => by
          let sF : FullState := { s4 with scratch := { s4.scratch with tarjan_mark := tmk_c } }
          have hinvF := m6_fullDenseInvW_with_tmk hinv4 ht_len
          have hscrF_len := hinvF.1.scratch_ok.scratch_buf_len
          m6_split
          · m6_steps
            exact hQ 20#64 sF m_end hinvF hcv4_0 hfuel4_0 ht_done hrepr4_inv htrh4_0 hgu4_0
              hhwm4_ex (Or.inr rfl) (fun _ => hcr_uns (by bv_omega)) hm_end
          m6_split
          · have huns_f0 := hinv4.2.1.ext_sound.2 (hinv4.2.1.inconsistent_sound (by bv_omega))
            m6_steps
            exact hQ 20#64 sF m_end hinvF hcv4_0 hfuel4_0 ht_done hrepr4_inv htrh4_0 hgu4_0
              hhwm4_ex (Or.inr rfl) (fun _ => huns_f0) hm_end
          have hcr_1 : cr = 1#64 := hcr_dom.elim id fun h20 => absurd h20 ‹_›
          obtain ⟨L', hL'_len, hL'_mv, heqb4⟩ := hcr_eq hcr_1
          have hLL' : L' = L := K6Layout.eq_of_scrLen_maxV (hL'_len.trans hL_len.symm)
            (hL'_mv.trans hL_mv.symm)
          rw [hLL'] at heqb4
          have heqbF : M6EqBufOk F_cur sF (sF.scratch.scratch_buf[L.k6Base + 24]'(by
              rw [hscrF_len, ← hL_len]; unfold K6Layout.scrLen K6Layout.k6Fixed; omega)).toNat := by
            have h1 := m6_k6StateOfScratch_neq (L := L) (scr := s4.scratch.scratch_buf) (by
              rw [hinv4.1.scratch_ok.scratch_buf_len, ← hL_len]
              unfold K6Layout.scrLen K6Layout.k6Fixed; omega)
            rw [← h1]; exact heqb4
          change wp _ _ _ _ _
          c0_hsteps_nogrp; try dsimp only [Prod.fst]; try rw [hkptr_c0]; try rw [hmv_eq]
          open scoped FullK6DynMem in m6_to_group
          refine wp_join_group (ts := [])
            (fun () mE => ∃ sE : FullState, FullDenseInvW c F0 F_cur sE ∧
              sE.core.cur_vars = s.core.cur_vars ∧ sE.core.fuel.toNat ≤ s.core.fuel.toNat ∧
              M6TmkZero sE ∧ FullCongReprInv F_cur (2 * sE.core.cur_vars) sE.core.repr ∧
              sE.scratch.tarjan_reach = s.scratch.tarjan_reach ∧
              (∀ i < 64, i ≠ 33 → sE.scratch.glue_used[i]? = s.scratch.glue_used[i]?) ∧
              (∃ L : K6Layout, L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap ∧
                K6HwmClean L (sE.scratch.glue_used[33]?.getD 0#32)
                  (k6StateOfScratch L sE.scratch.scratch_buf)) ∧
              (FullMem c sE ⋆ R) mE)
            (fun _ () mE ⟨sE, hinvE, hcvE, hfuelE, htmkE, hrepE, htrhE, hguE, hhwmE, hmE⟩ => by
              m6_to_group; refine wp_unroll_group fun _ _ => ?_
              m6_split
              · have huns_f0 := hinvE.2.1.ext_sound.2 (hinvE.2.1.inconsistent_sound ‹_›)
                m6_steps
                exact hQ 20#64 sE mE hinvE hcvE hfuelE htmkE hrepE htrhE hguE hhwmE (Or.inr rfl)
                  (fun _ => huns_f0) hmE
              · m6_steps
                exact hQ 1#64 sE mE hinvE hcvE hfuelE htmkE hrepE htrhE hguE hhwmE (Or.inl rfl)
                  (fun h => by cases h) hmE)
            (fun _ hJels => by
              change wp _ _ _ _ _
              c0_hsteps_nogrp; try dsimp only [Prod.fst]; try rw [hkptr_c0]; try rw [hmv_eq]
              open scoped FullK6DynMem in m6_split; rotate_left
              · m6_steps
                exact hJels () m_end ⟨sF, hinvF, hcv4_0, hfuel4_0, ht_done, hrepr4_inv, htrh4_0,
                  hgu4_0, hhwm4_ex, hm_end⟩
              m6_call hEls
              refine ⟨c, F0, F_cur, sF, R, rfl, hinvF, heqbF, hrepr4_inv, hm_end,
                fun ok5 s5 m5 hinv5 hcv5 hfuel5 hrep5 htmk5 htrh5 hscr5 _ hgu5 hok_f hm5 => ?_⟩
              have hcv5_0 := hcv5.trans hcv4_0
              have hfuel5_0 : s5.core.fuel.toNat ≤ s.core.fuel.toNat := by
                rw [hfuel5]; exact hfuel4_0
              have htmk5_z : M6TmkZero s5 := m6TmkZero_congr ht_done hcv5 htmk5
              have htrh5_0 := htrh5.trans htrh4_0
              have hgu5_0 : ∀ i < 64, i ≠ 33 →
                  s5.scratch.glue_used[i]? = s.scratch.glue_used[i]? :=
                fun i hi hne => by rw [hgu5]; exact hgu4_0 i hi hne
              have hhwm5_ex : ∃ L : K6Layout, L.scrLen = c.scratch_cap ∧
                  L.maxV = k6MaxV c.scratch_cap ∧
                  K6HwmClean L (s5.scratch.glue_used[33]?.getD 0#32)
                    (k6StateOfScratch L s5.scratch.scratch_buf) := by
                rw [hgu5, hscr5]; exact hhwm4_ex
              m6_split; rotate_left
              · have hok5_f : ok5 = false := by cases ok5 <;> simp at hc ⊢
                m6_steps
                exact hQ 20#64 s5 m5 hinv5 hcv5_0 hfuel5_0 htmk5_z hrep5 htrh5_0 hgu5_0 hhwm5_ex
                  (Or.inr rfl) (fun _ => (hok_f hok5_f).1) hm5
              · m6_steps
                exact hJels () m5 ⟨s5, hinv5, hcv5_0, hfuel5_0, htmk5_z, hrep5, htrh5_0, hgu5_0,
                  hhwm5_ex, hm5⟩))

/-! ## 4. `full_sweep_dense_m6_wp` (`5/5`) -/

theorem full_sweep_dense_m6_wp (Γ : Env)
    (hMaxV : Γ.Has "full_m6_max_v" m6MaxVSpec)
    (hSweepVars : Γ.Has "full_m6_sweep_vars" fullM6SweepVarsSpec) :
    ∀ args m Q X, fullSweepDenseM6Spec args m Q X →
      Func.wp Γ full_sweep_dense_m6_body args m Q X := by
  rintro ⟨h, budget, tick_lim, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  have hlen := hinv.lengths
  have hcv_le := hlen.core_ok.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv64 : s.core.cur_vars < 2 ^ 64 := by omega
  unfold Func.wp full_sweep_dense_m6_body
  m6_steps
  refine m6_call_max_v hMaxV (m6_scrCap_lt64 c) ?_
  m6_split
  · m6_steps; exact hQ 1#64 s m hinv rfl (le_refl _) (Or.inl rfl) (fun h => by cases h) hm
  m6_split
  · m6_steps; exact hQ 1#64 s m hinv rfl (le_refl _) (Or.inl rfl) (fun h => by cases h) hm
  m6_split
  · m6_steps; exact hQ 1#64 s m hinv rfl (le_refl _) (Or.inl rfl) (fun h => by cases h) hm
  m6_to_group
  refine wp_loop_inv (ts := [i64])
    (fun (i, ()) mi => i.toNat ≤ s.core.cur_vars ∧ ∃ tmk_i : List (BitVec 32),
      tmk_i.length = 2 * c.max_vars ∧
      (∀ v < i.toNat, tmk_i[v]?.getD 0#32 = 0#32) ∧
      (FullMem c { s with scratch := { s.scratch with tarjan_mark := tmk_i } } ⋆ R) mi)
    (fun (i, ()) _ => s.core.cur_vars - i.toNat)
    (fun _ hJt => by
      m6_steps
      exact hJt (0#64, ()) m ⟨Nat.zero_le _, s.scratch.tarjan_mark,
        hlen.scratch_ok.tarjan_mark_len, fun _ h => absurd h (Nat.not_lt_zero _), hm⟩)
    (fun _ (i, ()) mi ⟨hi_le, tmk_i, ht_len, ht_z, hmi⟩ hJt => by
      m6_split
      · have hi_lt : i.toNat < s.core.cur_vars := by
          have h1 : i.toNat < s.core.cur_vars % 2 ^ 64 := hc
          rwa [Nat.mod_eq_of_lt hcv64] at h1
        have hi1 : (i + 1#64).toNat = i.toNat + 1 := m6_bv64_add1 (by omega)
        have hi_bd : i.toNat < tmk_i.length := by rw [ht_len]; omega
        m6_steps
        refine hJt (i + 1#64, ()) _ (by dsimp only; rw [hi1]; omega)
          ⟨by omega, tmk_i.set i.toNat 0#32, List.length_set.trans ht_len, fun v hv => ?_,
           by assumption⟩
        rw [hi1] at hv
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hv) with hlt | rfl
        · rw [List.getElem?_set_ne (by omega)]; exact ht_z v hlt
        · rw [List.getElem?_set_self hi_bd, Option.getD_some]
      · have hi_eq : i.toNat = s.core.cur_vars := by
          have h1 : ¬ i.toNat < s.core.cur_vars % 2 ^ 64 := hc
          rw [Nat.mod_eq_of_lt hcv64] at h1; omega
        let s1 : FullState := { s with scratch := { s.scratch with tarjan_mark := tmk_i } }
        obtain ⟨F_cur, hdw⟩ := hinv.exists_witness
        have hinv1 : FullDenseInv c F0 s1 := (m6_fullDenseInvW_with_tmk hdw ht_len).toDense
        have htmk1 : M6TmkZero s1 := fun v hv => ht_z v (hi_eq ▸ hv)
        m6_call hSweepVars
        refine ⟨c, F0, s1, R, rfl, hinv1, htmk1, hmi,
          fun r s2 m2 hinv2 hcv2 hfuel2 _ _ huns2 hm2 => ?_⟩
        m6_split
        · m6_steps
          exact hQ 20#64 s2 m2 hinv2 hcv2 hfuel2 (Or.inr rfl) (fun _ => huns2 hc) hm2
        m6_to_group; refine wp_unroll_group fun _ _ => ?_
        m6_split
        · m6_steps
          exact hQ 20#64 s2 m2 hinv2 hcv2 hfuel2 (Or.inr rfl)
            (fun _ => hinv2.inconsistent_unsat hc) hm2
        · m6_steps
          exact hQ 1#64 s2 m2 hinv2 hcv2 hfuel2 (Or.inl rfl) (fun h => by cases h) hm2)

end LeanQbe.T.Examples.Kissat.Proof.Sweep

end
