module

public import LeanQbe.T.Examples.Kissat.FullM6SweepProofVar2a

/-!
# Kissat `D-Full` M6 — Partition Classes & Variable Sweep Proofs (`28, 33/39`)

Parametric `(Γ : Env)` `Func.wp` proofs for `2/39` owned functions:
- `28/39`: `full_m6_sweep_classes_wp` (`m6SweepClassesSpec`)
- `33/39`: `full_m6_sweep_var_wp` (`m6SweepVarSpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6Sweep

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full LeanQbe.T.Examples.Kissat.FullM4Sweep
open Kraken.Bedrock2.Test
open FullArenaTactics K6MemATactics K6PtrTactics M6ElsBv
open scoped FullArenaTactics M6SweepTactics

/-! ## 1. `full_m6_sweep_classes_wp` Helpers & Proof (`28/39`) -/

private structure M6ClassData (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 : FullState) (L : K6Layout) (nv : BitVec 32) (ncls neq rbit : BitVec 32)
    (R : Mem 64 → Prop) (m : Mem 64) where
  rbit_le : rbit.toNat ≤ 64
  ncls_le : ncls.toNat ≤ c.max_vars
  neq_le : neq.toNat ≤ s0.core.cur_vars
  st : FullState
  inv : FullDenseInvW c F0 F_cur st
  cv : st.core.cur_vars = s0.core.cur_vars
  fuel : st.core.fuel.toNat ≤ s0.core.fuel.toNat
  ws : st.scratch.work_stk1 = s0.scratch.work_stk1
  tmk : st.scratch.tarjan_mark = s0.scratch.tarjan_mark
  trh : st.scratch.tarjan_reach = s0.scratch.tarjan_reach
  k6 : K6Inv L (ConeModelSet F_cur s0.scratch.work_stk1 nv.toNat)
    (k6StateOfScratch L st.scratch.scratch_buf)
  nv_eq : (k6StateOfScratch L st.scratch.scratch_buf).nv = nv
  neq_eq : (k6StateOfScratch L st.scratch.scratch_buf).neq = neq
  part : M6PartitionOk nv.toNat ncls.toNat st.scratch.scratch_buf st.scratch.shrink_stk
  eqb : M6EqBufOk F_cur st neq.toNat
  mem : (FullMem c st ⋆ R) m

private theorem m6_class_refine_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {L : K6Layout} {nv nclsL neq rbit : Val i32} {R : Mem 64 → Prop} {mFl : Mem 64}
    {h : Val i64} {steps1 : Val i32} {jLoop : Cont [i32, i32, i32, i32]}
    (hRef : M6EnvSpec Γ "full_m6_sweep_refine_sig" m6SweepRefineSigSpec)
    (hRefP : M6EnvSpec Γ "full_m6_refine_partition" m6RefinePartitionSpec)
    (h_hdr : h = c.hdr) (hL_len : L.scrLen = c.scratch_cap)
    (hL_mv : L.maxV = k6MaxV c.scratch_cap) (hcap : k6MinScr ≤ c.scratch_cap)
    (hnv_L : nv.toNat ≤ L.maxV) (hnv_mx : nv.toNat ≤ c.max_vars)
    (hnv_2mx : nv.toNat ≤ 2 * c.max_vars)
    (hws_lt : ∀ i < nv.toNat, (s.scratch.work_stk1[i]?.getD 0#32).toNat < s.core.cur_vars)
    (hcongr : ∀ {scrA scrB : List (BitVec 32)},
      (∀ i < c.scratch_cap, L.phtMerged ≤ i → scrB[i]? = scrA[i]?) →
      scrA.length = c.scratch_cap → scrB.length = c.scratch_cap →
      k6StateOfScratch L scrB = k6StateOfScratch L scrA)
    (dFl : M6ClassData c F0 F_cur s L nv nclsL neq rbit R mFl)
    (hJump : ∀ (rbitR new_n : BitVec 32) mP,
      M6ClassData c F0 F_cur s L nv new_n neq rbitR R mP →
      wp Γ Q X (Expr.jump jLoop (Arg.var rbitR, Arg.var new_n, Arg.var neq, Arg.var steps1, ()))
        mP) :
    wp Γ Q X
      (Expr.group (sig := [[i32]])
        (fun _ =>
          Blocks.cons
            (fun (p_r : Tup Val [i32]) =>
              Expr.call "full_m6_refine_partition" (as := [i64, i32, i32]) (bs := [i32])
                (Arg.var h, Arg.var nv, Arg.var nclsL, ())
                fun (p_n : Tup Val [i32]) =>
                  Expr.jump jLoop
                    (Arg.var p_r.fst, Arg.var p_n.fst, Arg.var neq, Arg.var steps1, ()))
            Blocks.nil)
        (fun Js =>
          Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i32) (Arg.var rbit, Arg.imm 64, ()))
            fun (p_c : Tup Val [.bool]) =>
              Expr.jnz (Arg.var p_c.fst)
                (Expr.call "full_m6_sweep_refine_sig" (as := [i64, i32, i32]) (bs := [])
                  (Arg.var h, Arg.var nv, Arg.var rbit, ())
                  fun (_ : Tup Val []) =>
                    Expr.let_ (Op.mk (OpCode.add i32) (Arg.var rbit, Arg.imm 1, ()))
                      fun (p_1 : Tup Val [i32]) => Expr.jump Js.fst (Arg.var p_1.fst, ()))
                (Expr.jump Js.fst (Arg.var rbit, ()))))
      mFl := by
  subst h_hdr
  refine wp_join_group (ts := [i32])
    (fun (rbitR, ()) mR => ∃ sR, rbitR.toNat ≤ 64 ∧ FullDenseInvW c F0 F_cur sR ∧
      sR.core.cur_vars = s.core.cur_vars ∧ sR.core.fuel.toNat ≤ s.core.fuel.toNat ∧
      sR.scratch.work_stk1 = s.scratch.work_stk1 ∧
      sR.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
      sR.scratch.tarjan_reach = s.scratch.tarjan_reach ∧
      K6Inv L (ConeModelSet F_cur s.scratch.work_stk1 nv.toNat)
        (k6StateOfScratch L sR.scratch.scratch_buf) ∧
      (k6StateOfScratch L sR.scratch.scratch_buf).nv = nv ∧
      (k6StateOfScratch L sR.scratch.scratch_buf).neq = neq ∧
      M6PartitionOk nv.toNat nclsL.toNat sR.scratch.scratch_buf sR.scratch.shrink_stk ∧
      M6EqBufOk F_cur sR neq.toNat ∧ (FullMem c sR ⋆ R) mR)
    (fun _ (rbitR, ()) mR
        ⟨sR, hrbR, hinvR, hcvR, hflR, hwsR, htmkR, htrhR, hKR, hnvR, hnqR, hptR, heqR, hmR⟩ => by
      m6_call hRefP
      refine ⟨c, sR, L, R, rfl, hinvR.1, hL_len, hL_mv, hnv_L, hnv_mx, dFl.ncls_le, ?_, hptR,
        hmR, ?_⟩
      · exact fun j hj => by rw [hwsR, hcvR]; exact hws_lt j hj
      · intro new_n scrP sstkP wsoP mP _ _ hscrP hsstP hwsoP hpreP hnnP hpartP hmP
        have hofP : k6StateOfScratch L scrP = k6StateOfScratch L sR.scratch.scratch_buf :=
          hcongr (fun i hi hdom => hpreP i hi (Or.inr hdom)) hinvR.1.scratch_ok.scratch_buf_len
            hscrP
        let sP : FullState :=
          { sR with scratch :=
            { sR.scratch with scratch_buf := scrP, shrink_stk := sstkP, wsort := wsoP } }
        have hinvP := m6_fullDenseInvW_with_cls_scratch hinvR hscrP hsstP
          hinvR.1.core_ok.min_clr_len_arr hwsoP
        have heqbP := m6_eqBufOk_congr heqR rfl rfl
        m6_steps
        exact hJump rbitR new_n mP
          ⟨hrbR, hnnP, dFl.neq_le, sP, hinvP, hcvR, hflR, hwsR, htmkR, htrhR, hofP ▸ hKR,
           hofP ▸ hnvR, hofP ▸ hnqR, hpartP, heqbP, hmP⟩)
    (fun _ hJrb => by
      m6_split; rotate_left
      · m6_steps
        exact hJrb (rbit, ()) mFl ⟨dFl.st, dFl.rbit_le, dFl.inv, dFl.cv, dFl.fuel, dFl.ws,
          dFl.tmk, dFl.trh, dFl.k6, dFl.nv_eq, dFl.neq_eq, dFl.part, dFl.eqb, dFl.mem⟩
      have hrb_lt : rbit.toNat < 64 := hc
      have hrb1 : (rbit + 1#32).toNat = rbit.toNat + 1 := m6_bv32_add1 (by omega)
      m6_call hRef
      refine ⟨c, dFl.st, R, rfl, dFl.inv.1, hcap, by rw [← hL_mv]; exact hnv_L, hnv_2mx,
        fun j hj => by rw [dFl.ws, dFl.cv]; exact hws_lt j hj,
        dFl.mem, fun sigR mR hsigR hmR => ?_⟩
      let sR := { dFl.st with scratch := { dFl.st.scratch with sim_sig := sigR } }
      m6_steps
      exact hJrb (rbit + 1#32, ()) mR
        ⟨sR, by omega, m6_fullDenseInvW_with_sig dFl.inv hsigR, dFl.cv, dFl.fuel, dFl.ws, dFl.tmk,
         dFl.trh, dFl.k6, dFl.nv_eq, dFl.neq_eq, dFl.part, m6_eqBufOk_congr dFl.eqb rfl rfl,
         hmR⟩)

private theorem m6_class_unlink_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {L : K6Layout} {nv nclsL neq rbit a cNode steps1 : Val i32} {phtNextPtr : Val i64}
    {R : Mem 64 → Prop} {mU : Mem 64} {jLoop : Cont [i32, i32, i32, i32]}
    (hL_len : L.scrLen = c.scratch_cap) (hnv_L : nv.toNat ≤ L.maxV)
    (hncls_pos : 0 < nclsL.toNat) (ha_lt : a.toNat < nv.toNat) (hc_lt : cNode.toNat < nv.toNat)
    (dU : M6ClassData c F0 F_cur s L nv nclsL neq rbit R mU)
    (hc_eq : cNode = dU.st.scratch.scratch_buf[k6PhtNext + a.toNat]?.getD 0xFFFFFFFF#32)
    (hpht : phtNextPtr = c.pScratchBuf + BitVec.ofNat 64 (4 * k6PhtNext))
    (hJump : ∀ (ncls' : Val i32) m',
      M6ClassData c F0 F_cur s L nv ncls' neq rbit R m' →
      wp Γ Q X (Expr.jump jLoop (Arg.var rbit, Arg.var ncls', Arg.var neq, Arg.var steps1, ()))
        m') :
    wp Γ Q X
      (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var a, ())) fun p0 =>
        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p0.fst, Arg.imm 4, ())) fun p1 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var phtNextPtr, Arg.var p1.fst, ())) fun p2 =>
            Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var cNode, ())) fun p3 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p3.fst, Arg.imm 4, ())) fun p4 =>
                Expr.let_ (Op.mk (OpCode.add i64)
                    (Arg.var phtNextPtr, Arg.var p4.fst, ())) fun p5 =>
                  Expr.load i32 (Arg.var p5.fst) fun ld =>
                    Expr.store (t := i32) (Arg.var ld) (Arg.var p2.fst)
                      (Expr.group (sig := [[i32]])
                        (fun _ => Blocks.cons (fun (pn : Tup Val [i32]) =>
                          Expr.jump jLoop
                            (Arg.var rbit, Arg.var pn.fst, Arg.var neq, Arg.var steps1, ()))
                          Blocks.nil)
                        (fun Js =>
                          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var a, ())) fun q0 =>
                            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var q0.fst, Arg.imm 4, ()))
                              fun q1 =>
                              Expr.let_ (Op.mk (OpCode.add i64)
                                  (Arg.var phtNextPtr, Arg.var q1.fst, ())) fun q2 =>
                                Expr.load i32 (Arg.var q2.fst) fun ld2 =>
                                  Expr.let_ (Op.mk (OpCode.cmp CmpOp.uge i32)
                                      (Arg.var ld2, Arg.var nv, ())) fun qc =>
                                    Expr.jnz (Arg.var qc.fst)
                                      (Expr.let_ (Op.mk (OpCode.sub i32)
                                          (Arg.var nclsL, Arg.imm 1, ())) fun qn =>
                                        Expr.jump Js.fst (Arg.var qn.fst, ()))
                                      (Expr.jump Js.fst (Arg.var nclsL, ())))))
      mU := by
  subst hpht
  have hmL := L.hmaxV; have haL := L.hacap
  have hscrU_len := dU.inv.1.scratch_ok.scratch_buf_len
  have ha_mv : a.toNat < L.maxV := Nat.lt_of_lt_of_le ha_lt hnv_L
  have hc_mv : cNode.toNat < L.maxV := Nat.lt_of_lt_of_le hc_lt hnv_L
  have hpht_cap : k6PhtNext + L.maxV < c.scratch_cap := by
    unfold k6PhtNext; unfold K6Layout.scrLen K6Layout.k6Base K6Layout.k6Fixed at hL_len; omega
  have hpht_k6b : k6PhtNext + L.maxV < L.k6Base := by
    unfold k6PhtNext K6Layout.k6Base; omega
  have hc_bd : k6PhtNext + cNode.toNat < dU.st.scratch.scratch_buf.length := by
    rw [hscrU_len]; exact Nat.lt_trans (Nat.add_lt_add_left hc_mv _) hpht_cap
  have ha_bd : k6PhtNext + a.toNat < dU.st.scratch.scratch_buf.length := by
    rw [hscrU_len]; exact Nat.lt_trans (Nat.add_lt_add_left ha_mv _) hpht_cap
  let nxtU := dU.st.scratch.scratch_buf[k6PhtNext + cNode.toNat]'hc_bd
  let scrU := dU.st.scratch.scratch_buf.set (k6PhtNext + a.toNat) nxtU
  have hlt_u : k6PhtNext + a.toNat < L.k6Base :=
    Nat.lt_trans (Nat.add_lt_add_left ha_mv _) hpht_k6b
  have hslU : scrU.length = c.scratch_cap := List.length_set.trans hscrU_len
  have hKU : K6Inv L (ConeModelSet F_cur s.scratch.work_stk1 nv.toNat)
      (k6StateOfScratch L scrU) := by
    rw [m6_k6Inv_of_prefix_set hlt_u dU.k6]; exact dU.k6
  have hnvU : (k6StateOfScratch L scrU).nv = nv := by
    rw [m6_k6Inv_of_prefix_set hlt_u dU.k6, dU.nv_eq]
  have hnqU : (k6StateOfScratch L scrU).neq = neq := by
    rw [m6_k6Inv_of_prefix_set hlt_u dU.k6, dU.neq_eq]
  let sU : FullState := { dU.st with scratch := { dU.st.scratch with scratch_buf := scrU } }
  have hinvU := m6_fullDenseInvW_with_scratch dU.inv hslU (fuel' := dU.st.core.fuel)
  have heqbU := m6_eqBufOk_congr dU.eqb rfl rfl
  have hunk := m6_partOk_unlink (Nat.le_trans hnv_L (by omega)) ha_lt hc_eq hc_lt ha_bd hc_bd
    dU.part
  have hmD := dU.mem
  change wp _ _ _ _ _
  open scoped M6PhtMem M6Var2PhtMem in
    (c0_hsteps_nogrp; try dsimp only [Prod.fst]
     m6_to_group; refine wp_unroll_group fun _ _ => ?_
     c0_hsteps_nogrp; try dsimp only [Prod.fst]
     m6_split
     · have hn1 : (nclsL - 1#32).toNat ≤ c.max_vars := by
         rw [bv32_sub1_of_pos hncls_pos]; exact Nat.le_trans (Nat.sub_le _ _) dU.ncls_le
       m6_steps
       exact hJump (nclsL - 1#32) _
         ⟨dU.rbit_le, hn1, dU.neq_le, sU, hinvU, dU.cv, dU.fuel, dU.ws, dU.tmk, dU.trh,
          hKU, hnvU, hnqU, (by rw [bv32_sub1_of_pos hncls_pos]; exact hunk.2), heqbU,
          by dsimp only [sU, scrU, nxtU]; assumption⟩
     · m6_steps
       exact hJump nclsL _
         ⟨dU.rbit_le, dU.ncls_le, dU.neq_le, sU, hinvU, dU.cv, dU.fuel, dU.ws, dU.tmk, dU.trh,
          hKU, hnvU, hnqU, hunk.1, heqbU, by dsimp only [sU, scrU, nxtU]; assumption⟩)

private theorem m6_class_solve2_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {L : K6Layout} {nv nclsL neq rbit : Val i32} {R : Mem 64 → Prop} {mIn mKa : Mem 64}
    {h : Val i64} {rem : Val i64} {a0 a1 : BitVec 32}
    {k : Tup Val [i64] → Expr Val Cont rs}
    (hSolve : M6EnvSpec Γ "full_m6_sweep_solve" m6SweepSolveSpec)
    (h_hdr : h = c.hdr) (hL_len : L.scrLen = c.scratch_cap)
    (hL_mv : L.maxV = k6MaxV c.scratch_cap) (hpht_k6b : k6PhtNext + L.maxV < L.k6Base)
    (hnv_L : nv.toNat ≤ L.maxV)
    (dIn : M6ClassData c F0 F_cur s L nv nclsL neq rbit R mIn)
    (ha0 : a0.toNat < 2 * nv.toNat) (ha1 : a1.toNat < 2 * nv.toNat)
    (hm_ka : (K6MemA L (L.kPtr c.pScratchBuf)
      ((((k6StateOfScratch L dIn.st.scratch.scratch_buf).putHdr .nassump 2#32).putArr
        .assump 0 a0).putArr .assump 1 a1) ⋆ (FullK6Frame c L dIn.st ⋆ R)) mKa)
    (hk : ∀ (dOut : Val i64) mOut (dS : M6ClassData c F0 F_cur s L nv nclsL neq rbit R mOut),
      (∀ i < L.k6Base, dS.st.scratch.scratch_buf[i]? = dIn.st.scratch.scratch_buf[i]?) →
      (dOut = 20#64 → ∀ β, ConeModelSet F_cur s.scratch.work_stk1 nv.toNat β →
        ¬ (unitsCnf [a0.toNat, a1.toNat]).Sat β) →
      wp Γ Q X (k (dOut, ())) mOut) :
    wp Γ Q X
      (Expr.call "full_m6_sweep_solve" (as := [i64, i32, i64]) (bs := [i64])
        (Arg.var h, Arg.var nv, Arg.var rem, ()) k) mKa := by
  subst h_hdr
  have hmL := L.hmaxV; have haL := L.hacap
  have hscr_in := dIn.inv.1.scratch_ok.scratch_buf_len
  obtain ⟨hK1, hnv1_s, _, hass1, _⟩ := k6Inv_set_assump2
    (by rw [dIn.nv_eq]; exact ha0) (by rw [dIn.nv_eq]; exact ha1) dIn.k6
  obtain ⟨hscr1_len, hpre1, hof1, hm1⟩ :=
    m6_join_k6_ofSlab (s := dIn.st) hL_len hscr_in hK1.shapes hm_ka
  let ks1 := (((k6StateOfScratch L dIn.st.scratch.scratch_buf).putHdr .nassump 2#32).putArr
    .assump 0 a0).putArr .assump 1 a1
  let scr1 := dIn.st.scratch.scratch_buf.take L.k6Base ++ ks1.toSlab
  let s1 : FullState := { dIn.st with scratch := { dIn.st.scratch with scratch_buf := scr1 } }
  have hlen1 : s1.LengthsOk c :=
    ⟨dIn.inv.1.core_ok, { dIn.inv.1.scratch_ok with scratch_buf_len := hscr1_len }⟩
  have hnv1' : (k6StateOfScratch L scr1).nv = nv := by
    rw [hof1]; exact hnv1_s.trans dIn.nv_eq
  have hass1' : k6AssumpLitsS L scr1 = [a0.toNat, a1.toNat] := by
    unfold k6AssumpLitsS; rw [hof1]; exact hass1
  m6_call hSolve
  refine ⟨c, s1, ConeModelSet F_cur s.scratch.work_stk1 nv.toNat, L, R, rfl, hlen1, hL_len, hL_mv,
    hof1 ▸ hK1, hnv1', hm1, fun dOut fuelS rngS scrS mOut hlenS hfuelS hpreS hKS _
      hnvS _ hassS hnqS _ hunsS hmOut => ?_⟩
  let sS : FullState :=
    { s1 with
      core := { s1.core with fuel := fuelS }
      scratch := { s1.scratch with rng_state := rngS, scratch_buf := scrS } }
  have hscrS_len := hlenS.scratch_ok.scratch_buf_len
  have hinvS := m6_fullDenseInvW_with_fuel_rng_sig_scr dIn.inv dIn.inv.1.scratch_ok.sim_sig_len
    hscrS_len (fuel' := fuelS) (rng' := rngS)
  have hfuelS0 : fuelS.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfuelS dIn.fuel
  have hnqS' : (k6StateOfScratch L scrS).neq = neq := by rw [hnqS, hof1]; exact dIn.neq_eq
  have hpre_comb : ∀ i < L.k6Base, scrS[i]? = dIn.st.scratch.scratch_buf[i]? := fun i hi => by
    rw [hpreS i hi, hpre1 i hi]
  have hpartS : M6PartitionOk nv.toNat nclsL.toNat scrS dIn.st.scratch.shrink_stk :=
    ⟨dIn.part.1, fun i hi => by
      have hiL : k6PhtNext + i < L.k6Base :=
        Nat.lt_trans (Nat.add_lt_add_left (Nat.lt_of_lt_of_le hi hnv_L) _) hpht_k6b
      rw [hpre_comb (k6PhtNext + i) hiL]; exact dIn.part.2.1 i hi, dIn.part.2.2⟩
  have heqbS := m6_eqBufOk_congr dIn.eqb rfl rfl
  let dS : M6ClassData c F0 F_cur s L nv nclsL neq rbit R mOut :=
    ⟨dIn.rbit_le, dIn.ncls_le, dIn.neq_le, sS, hinvS, dIn.cv, hfuelS0, dIn.ws, dIn.tmk,
     dIn.trh, hKS, hnvS, hnqS', hpartS, heqbS, hmOut⟩
  refine hk dOut mOut dS hpre_comb fun hdOut β hβ => ?_
  have := hunsS hdOut β hβ; rwa [hassS, hass1'] at this

private theorem m6_partOk_merge_unlink {L : K6Layout} {scr heads : List (BitVec 32)}
    {nv nclsL : Nat} {a cNode : BitVec 32} {P : (Nat → Bool) → Prop}
    (hL_len : L.scrLen = scr.length) (hnv_L : nv ≤ L.maxV) (hnv_lt : nv ≤ 2 ^ 31)
    (ha_lt : a.toNat < nv) (hc_lt : cNode.toNat < nv)
    (hc_eq : cNode = scr[k6PhtNext + a.toNat]?.getD 0xFFFFFFFF#32)
    (hpart : M6PartitionOk nv nclsL scr heads) (hK : K6Inv L P (k6StateOfScratch L scr)) :
    let scrM0 := scr.set (L.phtMerged + cNode.toNat) 1#32
    let nxtC2 := scrM0[k6PhtNext + cNode.toNat]'(by
      have hmL := L.hmaxV; have haL := L.hacap
      rw [List.length_set, ← hL_len]
      unfold k6PhtNext K6Layout.scrLen K6Layout.k6Base K6Layout.k6Fixed; omega)
    let scrM := scrM0.set (k6PhtNext + a.toNat) nxtC2
    scrM.length = L.scrLen ∧
    k6StateOfScratch L scrM = k6StateOfScratch L scr ∧
    M6PartitionOk nv nclsL scrM heads ∧
    M6PartitionOk nv (nclsL - 1) scrM heads ∧
    (∀ i < L.phtMerged, i < k6PhtNext ∨ i ≥ k6PhtNext + nv → scrM[i]? = scr[i]?) := by
  intro scrM0 nxtC2 scrM
  have hmL := L.hmaxV; have haL := L.hacap
  have hscr_L : scr.length = L.scrLen := hL_len.symm
  have hlt_m0 : L.phtMerged + cNode.toNat < L.k6Base := by
    unfold K6Layout.phtMerged K6Layout.k6Base; omega
  have hlt_m1 : k6PhtNext + a.toNat < L.k6Base := by
    unfold k6PhtNext K6Layout.k6Base; omega
  have hslM : scrM.length = L.scrLen := by
    dsimp only [scrM, scrM0]; rw [List.length_set, List.length_set, hscr_L]
  have hofM : k6StateOfScratch L scrM = k6StateOfScratch L scr := by
    dsimp only [scrM, scrM0]
    rw [m6_k6Inv_of_prefix_set hlt_m1, m6_k6Inv_of_prefix_set hlt_m0]
    · exact hK
    · rw [m6_k6Inv_of_prefix_set hlt_m0 hK]; exact hK
  have hp_m0 : M6PartitionOk nv nclsL scrM0 heads :=
    ⟨hpart.1, fun i hi => by
      dsimp only [scrM0]
      rw [List.getElem?_set_ne (by unfold k6PhtNext K6Layout.phtMerged; omega)]
      exact hpart.2.1 i hi, hpart.2.2⟩
  have hc_eq_M0 : cNode = scrM0[k6PhtNext + a.toNat]?.getD 0xFFFFFFFF#32 := by
    dsimp only [scrM0]
    rw [List.getElem?_set_ne (by unfold k6PhtNext K6Layout.phtMerged; omega), hc_eq]
  have hunkM := m6_partOk_unlink hnv_lt ha_lt hc_eq_M0 hc_lt
    (by dsimp only [scrM0]; rw [List.length_set, hscr_L]
        unfold k6PhtNext K6Layout.scrLen K6Layout.k6Base K6Layout.k6Fixed; omega)
    (by dsimp only [scrM0]; rw [List.length_set, hscr_L]
        unfold k6PhtNext K6Layout.scrLen K6Layout.k6Base K6Layout.k6Fixed; omega)
    hp_m0
  refine ⟨hslM, hofM, hunkM.1, hunkM.2, fun i hi hdisj => ?_⟩
  dsimp only [scrM, scrM0]
  rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]

private theorem m6_class_add_live_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {L : K6Layout} {nv nclsL neq rbit l0 l1 : Val i32} {h kPtr : Val i64}
    {R : Mem 64 → Prop} {mIn : Mem 64} {cont : Expr Val Cont [i64]}
    (hLive : M6EnvSpec Γ "full_k512_add_live_m6" k6AddLiveSpec)
    (hQ_20 : ∀ (s' : FullState) m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach → F0.Unsat →
      (FullMem c s' ⋆ R) m' → Q (20#64, ()) m')
    (h_hdr : h = c.hdr) (hkptr : kPtr = L.kPtr c.pScratchBuf)
    (hL_len : L.scrLen = c.scratch_cap) (hL_mv : L.maxV = k6MaxV c.scratch_cap)
    (hpht_k6b : k6PhtNext + L.maxV < L.k6Base) (hnv_L : nv.toNat ≤ L.maxV)
    (dIn : M6ClassData c F0 F_cur s L nv nclsL neq rbit R mIn)
    (hl0 : l0.toNat < 2 * nv.toNat) (hl1 : l1.toNat < 2 * nv.toNat)
    (hsem : SemEntails (ConeModelSet F_cur s.scratch.work_stk1 nv.toNat)
      [l0.toNat, l1.toNat])
    (hcont : ∀ mL (dOut : M6ClassData c F0 F_cur s L nv nclsL neq rbit R mL),
      (∀ i < L.k6Base, dOut.st.scratch.scratch_buf[i]? = dIn.st.scratch.scratch_buf[i]?) →
      wp Γ Q X cont mL) :
    wp Γ Q X
      (Expr.call "full_k512_add_live_m6" (as := [i64, i32, i32]) (bs := [])
        (Arg.var h, Arg.var l0, Arg.var l1, ())
        fun (_ : Tup Val []) =>
          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 6, ())) fun p0 =>
            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p0.fst, Arg.imm 4, ())) fun p1 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var kPtr, Arg.var p1.fst, ())) fun p2 =>
                Expr.load i32 (Arg.var p2.fst) fun ld =>
                  Expr.let_ (Op.mk (OpCode.cmp CmpOp.ne i32) (Arg.var ld, Arg.imm 0, ()))
                    fun pc =>
                    Expr.jnz (Arg.var pc.fst)
                      (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var h, Arg.imm 1024, ())) fun ph =>
                        Expr.store (t := i64) (Arg.imm 1) (Arg.var ph.fst)
                          (Expr.ret (Arg.imm 20, ())))
                      cont)
      mIn := by
  subst h_hdr hkptr
  have hmL := L.hmaxV; have haL := L.hacap
  m6_call hLive
  refine ⟨c, dIn.st, ConeModelSet F_cur s.scratch.work_stk1 nv.toNat, L, R, rfl, dIn.inv.1,
    hL_len, hL_mv, dIn.k6, by rw [dIn.nv_eq]; exact hl0,
    fun hff => by
      have := congrArg BitVec.toNat hff
      dsimp only [Arg.val] at this
      rw [show (0xFFFFFFFF#32).toNat = 4294967295 from rfl] at this; omega,
    fun _ => ⟨by rw [dIn.nv_eq]; exact hl1, hsem⟩, dIn.mem,
    fun scrL mL hlenL hpreL hKL _ hnvL _ _ hnqL hmL => ?_⟩
  let sL : FullState := { dIn.st with scratch := { dIn.st.scratch with scratch_buf := scrL } }
  have hscrL := hlenL.scratch_ok.scratch_buf_len
  have hinvL := m6_fullDenseInvW_with_scratch dIn.inv hscrL (fuel' := dIn.st.core.fuel)
  have hnvL' : (k6StateOfScratch L scrL).nv = nv := hnvL.trans dIn.nv_eq
  have hnqL' : (k6StateOfScratch L scrL).neq = neq := hnqL.trans dIn.neq_eq
  have hpre_k6b : ∀ i < L.k6Base, scrL[i]? = dIn.st.scratch.scratch_buf[i]? := fun i hi =>
    hpreL i hi
  have hpartL : M6PartitionOk nv.toNat nclsL.toNat scrL dIn.st.scratch.shrink_stk :=
    ⟨dIn.part.1, fun i hi => by
      have hiL : k6PhtNext + i < L.k6Base :=
        Nat.lt_trans (Nat.add_lt_add_left (Nat.lt_of_lt_of_le hi hnv_L) _) hpht_k6b
      rw [hpre_k6b (k6PhtNext + i) hiL]; exact dIn.part.2.1 i hi, dIn.part.2.2⟩
  have heqbL := m6_eqBufOk_congr dIn.eqb rfl rfl
  let dOut : M6ClassData c F0 F_cur s L nv nclsL neq rbit R mL :=
    ⟨dIn.rbit_le, dIn.ncls_le, dIn.neq_le, sL, hinvL, dIn.cv, dIn.fuel, dIn.ws, dIn.tmk,
     dIn.trh, hKL, hnvL', hnqL', hpartL, heqbL, hmL⟩
  change wp _ _ _ _ _
  c0_hsteps_nogrp; try dsimp only [Prod.fst]
  open scoped FullK6DynMem in m6_split
  · have hk_inc : (k6StateOfScratch L scrL).incons ≠ 0#32 := by
      rw [m6_k6StateOfScratch_incons (by
        rw [hscrL, ← hL_len]; unfold K6Layout.scrLen K6Layout.k6Fixed; omega)]
      exact (by assumption)
    have huns_cur : (cnfOfClauses F_cur).Unsat :=
      m6_coneModelSet_unsat_of_empty (ws1 := s.scratch.work_stk1) (nv := nv.toNat)
        (hKL.clauses.incons_ok hk_inc)
    have huns_f0 : F0.Unsat := hinvL.2.1.ext_sound.2 huns_cur
    m6_steps
    exact hQ_20 _ _ (m6_denseInvW_set_inconsistent hinvL huns_cur) dIn.cv dIn.fuel dIn.ws dIn.tmk
      dIn.trh huns_f0 (by assumption)
  · exact hcont mL dOut hpre_k6b

private theorem m6_class_rearm_jump_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {L : K6Layout} {nv nclsM neq' rbit steps1 gv_a gv_c : Val i32} {h : Val i64}
    {R : Mem 64 → Prop} {mEq : Mem 64} {jLoop : Cont [i32, i32, i32, i32]}
    (hRearm : M6EnvSpec Γ "full_m6_sweep_rearm" m6SweepRearmSpec)
    (h_hdr : h = c.hdr) (dEq : M6ClassData c F0 F_cur s L nv nclsM neq' rbit R mEq)
    (hJump : ∀ m',
      M6ClassData c F0 F_cur s L nv nclsM neq' rbit R m' →
      wp Γ Q X (Expr.jump jLoop (Arg.var rbit, Arg.var nclsM, Arg.var neq', Arg.var steps1, ()))
        m') :
    wp Γ Q X
      (Expr.call "full_m6_sweep_rearm" (as := [i64, i32]) (bs := []) (Arg.var h, Arg.var gv_a, ())
        fun _ => Expr.call "full_m6_sweep_rearm" (as := [i64, i32]) (bs := [])
          (Arg.var h, Arg.var gv_c, ())
          fun _ =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var h, Arg.imm 1080, ())) fun p0 =>
              Expr.load i64 (Arg.var p0.fst) fun ld =>
                Expr.let_ (Op.mk (OpCode.add i64) (Arg.var ld, Arg.imm 1, ())) fun p1 =>
                  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var h, Arg.imm 1080, ())) fun p2 =>
                    Expr.store (t := i64) (Arg.var p1.fst) (Arg.var p2.fst)
                      (Expr.jump jLoop (Arg.var rbit, Arg.var nclsM, Arg.var neq',
                        Arg.var steps1, ())))
      mEq := by
  subst h_hdr
  m6_call hRearm
  refine ⟨c, F0, F_cur, dEq.st, R, rfl, dEq.inv, dEq.mem, fun flR1 mR1 _ hinvR1 hmR1 => ?_⟩
  let sR1 := { dEq.st with core := { dEq.st.core with flags := flR1 } }
  m6_call hRearm
  refine ⟨c, F0, F_cur, sR1, R, rfl, hinvR1, hmR1, fun flR2 mR2 _ hinvR2 hmR2 => ?_⟩
  let sR2 := { sR1 with core := { sR1.core with flags := flR2 } }
  m6_steps
  let sFin := { sR2 with scratch := { sR2.scratch with sweep_cnt := sR2.scratch.sweep_cnt + 1#64 } }
  have hinvFin := m6_fullDenseInvW_with_sweep_cnt hinvR2 (sR2.scratch.sweep_cnt + 1#64)
  exact hJump _
    ⟨dEq.rbit_le, dEq.ncls_le, dEq.neq_le, sFin, hinvFin, dEq.cv, dEq.fuel, dEq.ws, dEq.tmk,
     dEq.trh, dEq.k6, dEq.nv_eq, dEq.neq_eq, dEq.part, dEq.eqb, by assumption⟩

private theorem m6_class_eq_push_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {L : K6Layout} {nv nclsM neq rbit steps1 gv_a gv_c pol : Val i32}
    {h kPtr eqbPtr : Val i64} {R : Mem 64 → Prop} {mL2 : Mem 64}
    {jLoop : Cont [i32, i32, i32, i32]}
    (hRearm : M6EnvSpec Γ "full_m6_sweep_rearm" m6SweepRearmSpec)
    (h_hdr : h = c.hdr) (hkptr : kPtr = L.kPtr c.pScratchBuf) (heqb_p : eqbPtr = c.pWorkStk2)
    (hL_len : L.scrLen = c.scratch_cap) (_hL_mv : L.maxV = k6MaxV c.scratch_cap)
    (hpht_k6b : k6PhtNext + L.maxV < L.k6Base) (hnv_L : nv.toNat ≤ L.maxV)
    (hncM : nclsM.toNat ≤ c.max_vars)
    (hgva_lt : gv_a.toNat < s.core.cur_vars) (hgvc_lt : gv_c.toNat < s.core.cur_vars)
    (hpol : pol = 0#32 ∨ pol = 1#32)
    (hla_eq : (gv_a <<< (1 : Nat)).toNat = 2 * gv_a.toNat)
    (hlc_eq : ((gv_c <<< (1 : Nat)) ||| pol).toNat = 2 * gv_c.toNat + pol.toNat)
    (heq_f : LitEquiv (cnfOfClauses F_cur)
      (gv_a <<< (1 : Nat)).toNat ((gv_c <<< (1 : Nat)) ||| pol).toNat)
    (dL2 : M6ClassData c F0 F_cur s L nv nclsM neq rbit R mL2)
    (hJump : ∀ (neq' : Val i32) mF,
      M6ClassData c F0 F_cur s L nv nclsM neq' rbit R mF →
      wp Γ Q X (Expr.jump jLoop (Arg.var rbit, Arg.var nclsM, Arg.var neq', Arg.var steps1, ()))
        mF) :
    wp Γ Q X
      (Expr.group (sig := [[i32]])
        (fun _ => Blocks.cons (fun (p_neq : Tup Val [i32]) =>
          Expr.call "full_m6_sweep_rearm" (as := [i64, i32]) (bs := [])
            (Arg.var h, Arg.var gv_a, ()) fun _ =>
            Expr.call "full_m6_sweep_rearm" (as := [i64, i32]) (bs := [])
              (Arg.var h, Arg.var gv_c, ()) fun _ =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var h, Arg.imm 1080, ())) fun p0 =>
                Expr.load i64 (Arg.var p0.fst) fun ld =>
                  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var ld, Arg.imm 1, ())) fun p1 =>
                    Expr.let_ (Op.mk (OpCode.add i64) (Arg.var h, Arg.imm 1080, ())) fun p2 =>
                      Expr.store (t := i64) (Arg.var p1.fst) (Arg.var p2.fst)
                        (Expr.jump jLoop (Arg.var rbit, Arg.var nclsM, Arg.var p_neq.fst,
                          Arg.var steps1, ())))
          Blocks.nil)
        (fun Js =>
          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var neq, ())) fun p0 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var h, Arg.imm 776, ())) fun p1 =>
              Expr.load i64 (Arg.var p1.fst) fun ld =>
                Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i64) (Arg.var p0.fst, Arg.var ld, ()))
                  fun p2 =>
                  Expr.jnz (Arg.var p2.fst)
                    (Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var neq, Arg.imm 1, ())) fun q0 =>
                      Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var q0.fst, ())) fun q1 =>
                        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var q1.fst, Arg.imm 4, ())) fun q2 =>
                          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var eqbPtr, Arg.var q2.fst, ()))
                            fun q3 =>
                            Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var gv_a, Arg.imm 1, ()))
                              fun q4 =>
                              Expr.store (t := i32) (Arg.var q4.fst) (Arg.var q3.fst)
                                (Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var neq, Arg.imm 1, ()))
                                  fun q5 =>
                                  Expr.let_ (Op.mk (OpCode.add i32)
                                      (Arg.var q5.fst, Arg.imm 1, ())) fun q6 =>
                                    Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var q6.fst, ()))
                                      fun q7 =>
                                      Expr.let_ (Op.mk (OpCode.mul i64)
                                          (Arg.var q7.fst, Arg.imm 4, ())) fun q8 =>
                                        Expr.let_ (Op.mk (OpCode.add i64)
                                            (Arg.var eqbPtr, Arg.var q8.fst, ())) fun q9 =>
                                          Expr.let_ (Op.mk (OpCode.shl i32)
                                              (Arg.var gv_c, Arg.imm 1, ())) fun q10 =>
                                            Expr.let_ (Op.mk (OpCode.or i32)
                                                (Arg.var q10.fst, Arg.var pol, ())) fun q11 =>
                                              Expr.store (t := i32) (Arg.var q11.fst)
                                                (Arg.var q9.fst)
                                                (Expr.let_ (Op.mk (OpCode.add i32)
                                                    (Arg.var neq, Arg.imm 1, ())) fun q12 =>
                                                  Expr.let_ (Op.mk (OpCode.zext 32 64)
                                                      (Arg.imm 24, ())) fun q13 =>
                                                    Expr.let_ (Op.mk (OpCode.mul i64)
                                                        (Arg.var q13.fst, Arg.imm 4, ())) fun q14 =>
                                                      Expr.let_ (Op.mk (OpCode.add i64)
                                                          (Arg.var kPtr, Arg.var q14.fst, ()))
                                                        fun q15 =>
                                                        Expr.store (t := i32) (Arg.var q12.fst)
                                                          (Arg.var q15.fst)
                                                          (Expr.jump Js.fst
                                                            (Arg.var q12.fst, ())))))
                    (Expr.jump Js.fst (Arg.var neq, ()))))
      mL2 := by
  subst h_hdr hkptr heqb_p
  have hmL := L.hmaxV; have haL := L.hacap
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hlenL2 := dL2.inv.1
  have hcv_le : s.core.cur_vars ≤ c.max_vars := by
    have := hlenL2.core_ok.cur_vars_le; rw [dL2.cv] at this; exact this
  have hpol_lt : pol.toNat < 2 := by rcases hpol with rfl | rfl <;> decide
  have hmL2 := dL2.mem
  refine wp_join_group (ts := [i32])
    (fun (neq', ()) mEq =>
      ∃ dEq : M6ClassData c F0 F_cur s L nv nclsM neq' rbit R mEq, True)
    (fun _ (neq', ()) mEq ⟨dEq, _⟩ =>
      m6_class_rearm_jump_wp hRearm rfl dEq (hJump neq'))
    (fun _ hJeq => by
      m6_split; rotate_left
      · m6_steps; exact hJeq (neq, ()) mL2 ⟨dL2, trivial⟩
      have hnq_lt : neq.toNat < s.core.cur_vars := by
        have h1 : neq.toNat < (dL2.st.core.cur_vars % 2 ^ 64) := hc
        rw [dL2.cv] at h1; omega
      have hnq1 : (neq + 1#32).toNat = neq.toNat + 1 := m6_bv32_add1 (by omega)
      have h2nq0' : (neq <<< (1 : Nat)).toNat = 2 * neq.toNat := m6_bv32_shl1_lt (by omega)
      have h2nq1' : ((neq <<< (1 : Nat)) + 1#32).toNat = 2 * neq.toNat + 1 := by
        have hs := m6_bv32_shl1_lt (v := neq) (by omega); bv_omega
      have h2nq0 : ((neq <<< (1 : Nat)).setWidth 64).toNat = 2 * neq.toNat := by
        rw [bv_c0_zext32_64]; exact h2nq0'
      have h2nq1 : (((neq <<< (1 : Nat)) + 1#32).setWidth 64).toNat = 2 * neq.toNat + 1 := by
        rw [bv_c0_zext32_64]; exact h2nq1'
      have hws2_0 : ((neq <<< (1 : Nat)).setWidth 64).toNat <
          dL2.st.scratch.work_stk2.length := by
        rw [hlenL2.scratch_ok.work_stk2_len, h2nq0]; omega
      have hws2_1 : (((neq <<< (1 : Nat)) + 1#32).setWidth 64).toNat <
          (dL2.st.scratch.work_stk2.set
            ((neq <<< (1 : Nat)).setWidth 64).toNat (gv_a <<< (1 : Nat))).length := by
        rw [List.length_set, hlenL2.scratch_ok.work_stk2_len, h2nq1]; omega
      have hK_eq_fin := k6Inv_set_neq (neq + 1#32) dL2.k6
      have hscrL2_len := hlenL2.scratch_ok.scratch_buf_len
      have hsl_L2 : dL2.st.scratch.scratch_buf.length = L.scrLen := hscrL2_len.trans hL_len.symm
      let la := gv_a <<< (1 : Nat)
      let lc := (gv_c <<< (1 : Nat)) ||| pol
      let ws2' := (dL2.st.scratch.work_stk2.set (2 * neq.toNat) la).set (2 * neq.toNat + 1) lc
      have hws2'_len : ws2'.length = 2 * c.max_vars := by
        dsimp only [ws2']; rw [List.length_set, List.length_set, hlenL2.scratch_ok.work_stk2_len]
      let sEq0 : FullState := { dL2.st with scratch := { dL2.st.scratch with work_stk2 := ws2' } }
      have hinvEq0 := m6_fullDenseInvW_with_ws2 dL2.inv hws2'_len
      have heqbEq0 : M6EqBufOk F_cur sEq0 (neq + 1#32).toNat := by
        have h_w2l := hlenL2.scratch_ok.work_stk2_len
        rw [hnq1]
        exact m6_eqBufOk_push (m6_eqBufOk_congr dL2.eqb rfl rfl) (dL2.cv ▸ hnq_lt)
          (dL2.cv ▸ by rw [hla_eq]; omega) (dL2.cv ▸ by rw [hlc_eq]; omega) heq_f
          (by rw [h_w2l]; omega)
      change wp _ _ _ _ _; c0_hsteps
      have hmEq0 : (FullMem c sEq0 ⋆ R) m := by
        have hs_eq : ({ dL2.st with scratch :=
            { dL2.st.scratch with work_stk2 :=
              ((dL2.st.scratch.work_stk2.set ((neq <<< (1 : Nat)).setWidth 64).toNat la) |>.set
                (((neq <<< (1 : Nat)) + 1#32).setWidth 64).toNat lc) } } : FullState) = sEq0 := by
          simp only [sEq0, ws2', h2nq0, h2nq1]
        rw [← hs_eq]; exact hm
      obtain ⟨RfrE, hRfrE⟩ : ∃ RfrE : Mem 64 → Prop, RfrE = (FullK6Frame c L sEq0 ⋆ R) := ⟨_, rfl⟩
      have hm_kaE : (K6MemA L (L.kPtr c.pScratchBuf)
          (k6StateOfScratch L dL2.st.scratch.scratch_buf) ⋆ RfrE) m := by
        change (FullMem c sEq0 ⋆ R) m at hmEq0
        rw [fullMem_eq_k6Frame (s := sEq0) hsl_L2] at hmEq0; rw [hRfrE]
        exact k6Mem_to_amem dL2.k6.shapes (sep_ac hmEq0)
      change wp _ _ _ _ _
      open scoped K6MemATactics K6PtrTactics in c0_hsteps!
      rw [hRfrE] at hm
      let ksEqFin := (k6StateOfScratch L dL2.st.scratch.scratch_buf).putHdr .neq (neq + 1#32)
      let scrEqFin := dL2.st.scratch.scratch_buf.take L.k6Base ++ ksEqFin.toSlab
      let sEqFin : FullState :=
        { sEq0 with scratch := { sEq0.scratch with scratch_buf := scrEqFin } }
      obtain ⟨hscrEqFin_len, hpreEqFin, hofEqFin, hmEqFin⟩ :=
        m6_join_k6_ofSlab (s := sEq0) hL_len hscrL2_len hK_eq_fin.shapes hm
      have hinvEqFin := m6_fullDenseInvW_with_scratch hinvEq0 hscrEqFin_len
        (fuel' := sEq0.core.fuel)
      have hpartEqFin : M6PartitionOk nv.toNat nclsM.toNat scrEqFin sEq0.scratch.shrink_stk :=
        ⟨dL2.part.1, fun i hi => by
          have hiL : k6PhtNext + i < L.k6Base :=
            Nat.lt_trans (Nat.add_lt_add_left (Nat.lt_of_lt_of_le hi hnv_L) _) hpht_k6b
          rw [hpreEqFin (k6PhtNext + i) hiL]; exact dL2.part.2.1 i hi, dL2.part.2.2⟩
      try dsimp only [Prod.fst]
      exact hJeq (neq + 1#32, ()) _
        ⟨⟨dL2.rbit_le, hncM, by omega, sEqFin, hinvEqFin, dL2.cv, dL2.fuel, dL2.ws, dL2.tmk,
          dL2.trh, hofEqFin ▸ hK_eq_fin, by rw [hofEqFin]; exact dL2.nv_eq,
          by rw [hofEqFin]; rfl, hpartEqFin, heqbEq0, hmEqFin⟩, trivial⟩)

private theorem m6_class_flip2_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {L : K6Layout} {nv nclsL neq rbit fa fc : Val i32} {h : Val i64}
    {R : Mem 64 → Prop} {mIn : Mem 64} {jFl : Cont []} {cont : Expr Val Cont rs}
    (hFlip : M6EnvSpec Γ "full_k6_flip" k6FlipSpec)
    (h_hdr : h = c.hdr) (hL_len : L.scrLen = c.scratch_cap)
    (hL_mv : L.maxV = k6MaxV c.scratch_cap) (hpht_k6b : k6PhtNext + L.maxV < L.k6Base)
    (hnv_L : nv.toNat ≤ L.maxV) (hfa_lt : fa.toNat < 2 * nv.toNat)
    (hfc_lt : fc.toNat < 2 * nv.toNat)
    (dIn : M6ClassData c F0 F_cur s L nv nclsL neq rbit R mIn)
    (hJumpFl : ∀ mFl, M6ClassData c F0 F_cur s L nv nclsL neq rbit R mFl →
      wp Γ Q X (Expr.jump jFl ()) mFl)
    (hCont : ∀ mFc (dFc : M6ClassData c F0 F_cur s L nv nclsL neq rbit R mFc),
      (∀ i < L.k6Base, dFc.st.scratch.scratch_buf[i]? = dIn.st.scratch.scratch_buf[i]?) →
      wp Γ Q X cont mFc) :
    wp Γ Q X
      (Expr.call "full_k6_flip" (as := [i64, i32]) (bs := [.bool]) (Arg.var h, Arg.var fa, ())
        fun p0 => Expr.jnz (Arg.var p0.fst) (Expr.jump jFl ())
          (Expr.call "full_k6_flip" (as := [i64, i32]) (bs := [.bool])
            (Arg.var h, Arg.var fc, ()) fun p1 => Expr.jnz (Arg.var p1.fst)
              (Expr.jump jFl ()) cont))
      mIn := by
  subst h_hdr
  let P := ConeModelSet F_cur s.scratch.work_stk1 nv.toNat
  have h_idx_k6b : ∀ x < nv.toNat, k6PhtNext + x < L.k6Base := fun x hx =>
    Nat.lt_trans (Nat.add_lt_add_left (Nat.lt_of_lt_of_le hx hnv_L) _) hpht_k6b
  m6_call hFlip
  refine ⟨c, dIn.st, P, L, R, rfl, dIn.inv.1, hL_len, hL_mv, dIn.k6,
    by rw [dIn.nv_eq]; exact hfa_lt, dIn.mem,
    fun okFa scrFa mFa hlenFa hpreFa hKFa hnvFa _ _ hnqFa hmFa => ?_⟩
  have hscrFa := hlenFa.scratch_ok.scratch_buf_len
  obtain ⟨dFa, hdFa_pre⟩ : ∃ dFa : M6ClassData c F0 F_cur s L nv nclsL neq rbit R mFa,
      ∀ i < L.k6Base, dFa.st.scratch.scratch_buf[i]? = dIn.st.scratch.scratch_buf[i]? :=
    ⟨⟨dIn.rbit_le, dIn.ncls_le, dIn.neq_le,
      { dIn.st with scratch := { dIn.st.scratch with scratch_buf := scrFa } },
      m6_fullDenseInvW_with_scratch dIn.inv hscrFa (fuel' := dIn.st.core.fuel),
      dIn.cv, dIn.fuel, dIn.ws, dIn.tmk, dIn.trh, hKFa, hnvFa.trans dIn.nv_eq,
      hnqFa.trans dIn.neq_eq,
      ⟨dIn.part.1, fun i hi => by
        rw [hpreFa (k6PhtNext + i) (h_idx_k6b i hi)]; exact dIn.part.2.1 i hi, dIn.part.2.2⟩,
      m6_eqBufOk_congr dIn.eqb rfl rfl, hmFa⟩, fun i hi => hpreFa i hi⟩
  m6_split; · m6_steps; exact hJumpFl mFa dFa
  m6_call hFlip
  refine ⟨c, dFa.st, P, L, R, rfl, dFa.inv.1, hL_len, hL_mv, dFa.k6,
    by rw [dFa.nv_eq]; exact hfc_lt, dFa.mem,
    fun okFc scrFc mFc hlenFc hpreFc hKFc hnvFc _ _ hnqFc hmFc => ?_⟩
  have hscrFc := hlenFc.scratch_ok.scratch_buf_len
  obtain ⟨dFc, hdFc_pre⟩ : ∃ dFc : M6ClassData c F0 F_cur s L nv nclsL neq rbit R mFc,
      ∀ i < L.k6Base, dFc.st.scratch.scratch_buf[i]? = dIn.st.scratch.scratch_buf[i]? :=
    ⟨⟨dFa.rbit_le, dFa.ncls_le, dFa.neq_le,
      { dFa.st with scratch := { dFa.st.scratch with scratch_buf := scrFc } },
      m6_fullDenseInvW_with_scratch dFa.inv hscrFc (fuel' := dFa.st.core.fuel),
      dFa.cv, dFa.fuel, dFa.ws, dFa.tmk, dFa.trh, hKFc, hnvFc.trans dFa.nv_eq,
      hnqFc.trans dFa.neq_eq,
      ⟨dFa.part.1, fun i hi => by
        rw [hpreFc (k6PhtNext + i) (h_idx_k6b i hi)]; exact dFa.part.2.1 i hi, dFa.part.2.2⟩,
      m6_eqBufOk_congr dFa.eqb rfl rfl, hmFc⟩, fun i hi => by
        rw [hpreFc i hi, hdFa_pre i hi]⟩
  m6_split; · m6_steps; exact hJumpFl mFc dFc
  exact hCont mFc dFc hdFc_pre

private theorem m6_class_merge_body_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {L : K6Layout} {nv nclsM neq rbit a cNode gv_c pol : Val i32}
    {h kPtr flPtr : Val i64} {R : Mem 64 → Prop} {mM : Mem 64}
    {eqExpr : Expr Val Cont [i64]}
    (hLive : M6EnvSpec Γ "full_k512_add_live_m6" k6AddLiveSpec)
    (hQ : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      r = 1#64 ∨ r = 20#64 → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → ∃ L : K6Layout, L.scrLen = c.scratch_cap ∧
        L.maxV = k6MaxV c.scratch_cap ∧
        M6EqBufOk F_cur s' (k6StateOfScratch L s'.scratch.scratch_buf).neq.toNat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (h_hdr : h = c.hdr) (hkptr : kPtr = L.kPtr c.pScratchBuf) (hflp : flPtr = c.pFlags)
    (hL_len : L.scrLen = c.scratch_cap) (hL_mv : L.maxV = k6MaxV c.scratch_cap)
    (hpht_k6b : k6PhtNext + L.maxV < L.k6Base) (hnv_L : nv.toNat ≤ L.maxV)
    (hgvc_lt : gv_c.toNat < s.core.cur_vars)
    (ha_lt : a.toNat < nv.toNat) (hc_lt : cNode.toNat < nv.toNat)
    (hpol : pol = 0#32 ∨ pol = 1#32)
    (ha01 : (a <<< (1 : Nat)).toNat = 2 * a.toNat)
    (ha12 : ((cNode <<< (1 : Nat)) ||| pol).toNat = 2 * cNode.toNat + pol.toNat)
    (hll1_0 : ((a <<< (1 : Nat)) ^^^ 1#32).toNat = (a <<< (1 : Nat)).toNat ^^^ 1)
    (hll2_1 : (((cNode <<< (1 : Nat)) ||| pol) ^^^ 1#32).toNat =
      ((cNode <<< (1 : Nat)) ||| pol).toNat ^^^ 1)
    (hsem1 : SemEntails (ConeModelSet F_cur s.scratch.work_stk1 nv.toNat)
      [((a <<< (1 : Nat)) ^^^ 1#32).toNat, ((cNode <<< (1 : Nat)) ||| pol).toNat])
    (hsem2 : SemEntails (ConeModelSet F_cur s.scratch.work_stk1 nv.toNat)
      [(a <<< (1 : Nat)).toNat, (((cNode <<< (1 : Nat)) ||| pol) ^^^ 1#32).toNat])
    (dM : M6ClassData c F0 F_cur s L nv nclsM neq rbit R mM)
    (hEq : ∀ mL2, M6ClassData c F0 F_cur s L nv nclsM neq rbit R mL2 →
      wp Γ Q X eqExpr mL2) :
    wp Γ Q X
      (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var gv_c, ())) fun pf0 =>
        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var pf0.fst, Arg.imm 4, ())) fun pf1 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var flPtr, Arg.var pf1.fst, ())) fun pf2 =>
            Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var gv_c, ())) fun pf3 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var pf3.fst, Arg.imm 4, ())) fun pf4 =>
                Expr.let_ (Op.mk (OpCode.add i64) (Arg.var flPtr, Arg.var pf4.fst, ())) fun pf5 =>
                  Expr.load i32 (Arg.var pf5.fst) fun ld =>
                    Expr.let_ (Op.mk (OpCode.not i32) (Arg.imm 1024, ())) fun pf6 =>
                      Expr.let_ (Op.mk (OpCode.and i32) (Arg.var ld, Arg.var pf6.fst, ()))
                        fun pf7 =>
                        Expr.store (t := i32) (Arg.var pf7.fst) (Arg.var pf2.fst)
                          (Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var a, Arg.imm 1, ())) fun l0 =>
                            Expr.let_ (Op.mk (OpCode.xor i32) (Arg.var l0.fst, Arg.imm 1, ()))
                              fun l1 =>
                              Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var cNode, Arg.imm 1, ()))
                                fun l2 =>
                                Expr.let_ (Op.mk (OpCode.or i32) (Arg.var l2.fst, Arg.var pol, ()))
                                  fun l3 =>
                                  Expr.call "full_k512_add_live_m6" (as := [i64, i32, i32])
                                    (bs := []) (Arg.var h, Arg.var l1.fst, Arg.var l3.fst, ())
                                    fun (_ : Tup Val []) =>
                                    Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 6, ())) fun p0 =>
                                      Expr.let_ (Op.mk (OpCode.mul i64)
                                          (Arg.var p0.fst, Arg.imm 4, ())) fun p1 =>
                                        Expr.let_ (Op.mk (OpCode.add i64)
                                            (Arg.var kPtr, Arg.var p1.fst, ())) fun p2 =>
                                          Expr.load i32 (Arg.var p2.fst) fun ld =>
                                            Expr.let_ (Op.mk (OpCode.cmp CmpOp.ne i32)
                                                (Arg.var ld, Arg.imm 0, ())) fun pc =>
                                              Expr.jnz (Arg.var pc.fst)
                                                (Expr.let_ (Op.mk (OpCode.add i64)
                                                    (Arg.var h, Arg.imm 1024, ())) fun ph =>
                                                  Expr.store (t := i64) (Arg.imm 1) (Arg.var ph.fst)
                                                    (Expr.ret (Arg.imm 20, ())))
                                                (Expr.let_ (Op.mk (OpCode.shl i32)
                                                    (Arg.var a, Arg.imm 1, ())) fun m0 =>
                                                  Expr.let_ (Op.mk (OpCode.shl i32)
                                                      (Arg.var cNode, Arg.imm 1, ())) fun m1 =>
                                                    Expr.let_ (Op.mk (OpCode.or i32)
                                                        (Arg.var m1.fst, Arg.var pol, ())) fun m2 =>
                                                      Expr.let_ (Op.mk (OpCode.xor i32)
                                                          (Arg.var m2.fst, Arg.imm 1, ())) fun m3 =>
                                                        Expr.call "full_k512_add_live_m6"
                                                          (as := [i64, i32, i32]) (bs := [])
                                                          (Arg.var h, Arg.var m0.fst,
                                                            Arg.var m3.fst, ())
                                                          fun (_ : Tup Val []) =>
                                                          Expr.let_ (Op.mk (OpCode.zext 32 64)
                                                              (Arg.imm 6, ())) fun p0 =>
                                                            Expr.let_ (Op.mk (OpCode.mul i64)
                                                                (Arg.var p0.fst, Arg.imm 4, ()))
                                                              fun p1 =>
                                                              Expr.let_ (Op.mk (OpCode.add i64)
                                                                  (Arg.var kPtr, Arg.var p1.fst,
                                                                    ())) fun p2 =>
                                                                Expr.load i32 (Arg.var p2.fst)
                                                                  fun ld =>
                                                                  Expr.let_ (Op.mk
                                                                      (OpCode.cmp CmpOp.ne i32)
                                                                      (Arg.var ld, Arg.imm 0, ()))
                                                                    fun pc =>
                                                                    Expr.jnz (Arg.var pc.fst)
                                                                      (Expr.let_
                                                                        (Op.mk (OpCode.add i64)
                                                                          (Arg.var h,
                                                                            Arg.imm 1024, ()))
                                                                        fun ph =>
                                                                        Expr.store (t := i64)
                                                                          (Arg.imm 1)
                                                                          (Arg.var ph.fst)
                                                                          (Expr.ret (Arg.imm 20,
                                                                            ())))
                                                                      eqExpr)))
      mM := by
  subst h_hdr hkptr hflp
  have hpol_lt : pol.toNat < 2 := by rcases hpol with rfl | rfl <;> decide
  have hgvc_fl : (gv_c.setWidth 64).toNat < dM.st.core.flags.length := by
    rw [dM.inv.1.core_ok.flags_len, bv_c0_zext32_64]
    have := dM.inv.1.core_ok.cur_vars_le; rw [dM.cv] at this; omega
  let flC := dM.st.core.flags.set (gv_c.setWidth 64).toNat
    ((dM.st.core.flags[(gv_c.setWidth 64).toNat]'hgvc_fl) &&& ~~~1024#32)
  let sC : FullState := { dM.st with core := { dM.st.core with flags := flC } }
  have hinvC := m6_fullDenseInvW_with_flags dM.inv (flags' := flC)
    (List.length_set.trans dM.inv.1.core_ok.flags_len)
  have hmM := dM.mem
  m6_steps
  obtain ⟨dC, _⟩ : ∃ dC : M6ClassData c F0 F_cur s L nv nclsM neq rbit R _, True :=
    ⟨⟨dM.rbit_le, dM.ncls_le, dM.neq_le, sC, hinvC, dM.cv, dM.fuel, dM.ws, dM.tmk, dM.trh,
      dM.k6, dM.nv_eq, dM.neq_eq, dM.part, m6_eqBufOk_congr dM.eqb rfl rfl,
      by dsimp only [sC, flC]; assumption⟩, trivial⟩
  have hQ20 : ∀ (s' : FullState) m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach → F0.Unsat →
      (FullMem c s' ⋆ R) m' → Q (20#64, ()) m' :=
    fun s' m' hi hc' hf' hw' ht' hr' hu hm' =>
      hQ 20#64 s' m' hi hc' hf' hw' ht' hr' (Or.inr rfl) (fun _ => hu) (fun h => by cases h) hm'
  refine m6_class_add_live_wp hLive hQ20 rfl rfl hL_len hL_mv hpht_k6b hnv_L dC
    (by change ((a <<< (1 : Nat)) ^^^ 1#32).toNat < 2 * nv.toNat
        rw [hll1_0, ha01, m6_nat_xor1_cases]; split <;> omega)
    (by change ((cNode <<< (1 : Nat)) ||| pol).toNat < 2 * nv.toNat; rw [ha12]; omega) hsem1
    fun mL1 dL1 _ => ?_
  refine m6_class_add_live_wp hLive hQ20 rfl rfl hL_len hL_mv hpht_k6b hnv_L dL1
    (by change (a <<< (1 : Nat)).toNat < 2 * nv.toNat; rw [ha01]; omega)
    (by change (((cNode <<< (1 : Nat)) ||| pol) ^^^ 1#32).toNat < 2 * nv.toNat
        rw [hll2_1, ha12, m6_nat_xor1_cases]; split <;> omega) hsem2
    fun mL2 dL2 _ => hEq mL2 dL2

private theorem m6_class_d2_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {L : K6Layout} {nv nclsL neq rbit steps1 a cNode gv_a gv_c pol : Val i32}
    {h kPtr assPtr flPtr pmPtr pnPtr eqbPtr tick_lim : Val i64}
    {R : Mem 64 → Prop} {mS1 : Mem 64} {jLoop : Cont [i32, i32, i32, i32]}
    (hRef : M6EnvSpec Γ "full_m6_sweep_refine_sig" m6SweepRefineSigSpec)
    (hRefP : M6EnvSpec Γ "full_m6_refine_partition" m6RefinePartitionSpec)
    (hSolve : M6EnvSpec Γ "full_m6_sweep_solve" m6SweepSolveSpec)
    (hLive : M6EnvSpec Γ "full_k512_add_live_m6" k6AddLiveSpec)
    (hRearm : M6EnvSpec Γ "full_m6_sweep_rearm" m6SweepRearmSpec)
    (hQ : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → s'.scratch.work_stk1 = s.scratch.work_stk1 →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      r = 1#64 ∨ r = 20#64 → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → ∃ L : K6Layout, L.scrLen = c.scratch_cap ∧
        L.maxV = k6MaxV c.scratch_cap ∧
        M6EqBufOk F_cur s' (k6StateOfScratch L s'.scratch.scratch_buf).neq.toNat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (h_hdr : h = c.hdr) (hkptr : kPtr = L.kPtr c.pScratchBuf)
    (hassp : assPtr = L.kPtr c.pScratchBuf + BitVec.ofNat 64 (4 * L.oAssump))
    (hflp : flPtr = c.pFlags)
    (hpmp : pmPtr = c.pScratchBuf + BitVec.ofNat 64 (4 * L.phtMerged))
    (hpnp : pnPtr = c.pScratchBuf + BitVec.ofNat 64 (4 * k6PhtNext))
    (heqb_p : eqbPtr = c.pWorkStk2)
    (hL_len : L.scrLen = c.scratch_cap) (hL_mv : L.maxV = k6MaxV c.scratch_cap)
    (hcap : k6MinScr ≤ c.scratch_cap)
    (hpht_k6b : k6PhtNext + L.maxV < L.k6Base) (hnv_L : nv.toNat ≤ L.maxV)
    (hnv_mx : nv.toNat ≤ c.max_vars) (hnv_2mx : nv.toNat ≤ 2 * c.max_vars)
    (hws_lt : ∀ i < nv.toNat, (s.scratch.work_stk1[i]?.getD 0#32).toNat < s.core.cur_vars)
    (hcongr : ∀ {scrA scrB : List (BitVec 32)},
      (∀ i < c.scratch_cap, L.phtMerged ≤ i → scrB[i]? = scrA[i]?) →
      scrA.length = c.scratch_cap → scrB.length = c.scratch_cap →
      k6StateOfScratch L scrB = k6StateOfScratch L scrA)
    (hncls_pos : 0 < nclsL.toNat) (ha_lt : a.toNat < nv.toNat) (hc_lt : cNode.toNat < nv.toNat)
    (hgva_lt : gv_a.toNat < s.core.cur_vars) (hgvc_lt : gv_c.toNat < s.core.cur_vars)
    (hpol : pol = 0#32 ∨ pol = 1#32)
    (ha01 : (a <<< (1 : Nat)).toNat = 2 * a.toNat)
    (ha02 : ((a <<< (1 : Nat)) ||| 1#32).toNat = 2 * a.toNat + 1)
    (ha12 : ((cNode <<< (1 : Nat)) ||| pol).toNat = 2 * cNode.toNat + pol.toNat)
    (hla_eq : (gv_a <<< (1 : Nat)).toNat = 2 * gv_a.toNat)
    (hlc_eq : ((gv_c <<< (1 : Nat)) ||| pol).toNat = 2 * gv_c.toNat + pol.toNat)
    (hll1_0 : ((a <<< (1 : Nat)) ^^^ 1#32).toNat = (a <<< (1 : Nat)).toNat ^^^ 1)
    (hll1_1 : ((cNode <<< (1 : Nat)) ||| pol).toNat =
      ((cNode <<< (1 : Nat)) ||| (1#32 ^^^ pol)).toNat ^^^ 1)
    (hll2_0 : (a <<< (1 : Nat)).toNat = ((a <<< (1 : Nat)) ||| 1#32).toNat ^^^ 1)
    (hll2_1 : (((cNode <<< (1 : Nat)) ||| pol) ^^^ 1#32).toNat =
      ((cNode <<< (1 : Nat)) ||| pol).toNat ^^^ 1)
    (hgl1_0 : ((gv_a <<< (1 : Nat)) ^^^ 1#32).toNat =
      m6ConeLift s.scratch.work_stk1 ((a <<< (1 : Nat)).toNat ^^^ 1))
    (hgl1_1 : ((gv_c <<< (1 : Nat)) ||| pol).toNat =
      m6ConeLift s.scratch.work_stk1 (((cNode <<< (1 : Nat)) ||| (1#32 ^^^ pol)).toNat ^^^ 1))
    (hgl2_0 : (gv_a <<< (1 : Nat)).toNat =
      m6ConeLift s.scratch.work_stk1 (((a <<< (1 : Nat)) ||| 1#32).toNat ^^^ 1))
    (hgl2_1 : (((gv_c <<< (1 : Nat)) ||| pol) ^^^ 1#32).toNat =
      m6ConeLift s.scratch.work_stk1 (((cNode <<< (1 : Nat)) ||| pol).toNat ^^^ 1))
    (hsem1 : SemEntails (ConeModelSet F_cur s.scratch.work_stk1 nv.toNat)
      [(a <<< (1 : Nat)).toNat ^^^ 1, ((cNode <<< (1 : Nat)) ||| (1#32 ^^^ pol)).toNat ^^^ 1])
    (hent1 : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [m6ConeLift s.scratch.work_stk1 ((a <<< (1 : Nat)).toNat ^^^ 1),
        m6ConeLift s.scratch.work_stk1 (((cNode <<< (1 : Nat)) ||| (1#32 ^^^ pol)).toNat ^^^ 1)]))
    (dS1 : M6ClassData c F0 F_cur s L nv nclsL neq rbit R mS1)
    (hc_get : cNode = dS1.st.scratch.scratch_buf[k6PhtNext + a.toNat]?.getD 0xFFFFFFFF#32)
    (hJ : ∀ (rbit' ncls' neq' : Val i32) m',
      M6ClassData c F0 F_cur s L nv ncls' neq' rbit' R m' →
      wp Γ Q X (Expr.jump jLoop (Arg.var rbit', Arg.var ncls', Arg.var neq',
        Arg.var steps1, ())) m') :
    wp Γ Q X
      (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 11, ())) fun p0 =>
       Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p0.fst, Arg.imm 4, ())) fun p1 =>
       Expr.let_ (Op.mk (OpCode.add i64) (Arg.var kPtr, Arg.var p1.fst, ())) fun p2 =>
       Expr.load i32 (Arg.var p2.fst) fun ld =>
       Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld, ())) fun p3 =>
       Expr.let_ (Op.mk (OpCode.sub i64) (Arg.var tick_lim, Arg.var p3.fst, ())) fun prem =>
       Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 15, ())) fun p4 =>
       Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p4.fst, Arg.imm 4, ())) fun p5 =>
       Expr.let_ (Op.mk (OpCode.add i64) (Arg.var kPtr, Arg.var p5.fst, ())) fun p6 =>
       Expr.store (t := i32) (Arg.imm 2) (Arg.var p6.fst)
       (Expr.let_ (Op.mk (OpCode.sext 32 64) (Arg.imm 0, ())) fun q0 =>
        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var q0.fst, Arg.imm 4, ())) fun q1 =>
        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var assPtr, Arg.var q1.fst, ())) fun q2 =>
        Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var a, Arg.imm 1, ())) fun q3 =>
        Expr.let_ (Op.mk (OpCode.or i32) (Arg.var q3.fst, Arg.imm 1, ())) fun q4 =>
        Expr.store (t := i32) (Arg.var q4.fst) (Arg.var q2.fst)
        (Expr.let_ (Op.mk (OpCode.sext 32 64) (Arg.imm 1, ())) fun r0 =>
         Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var r0.fst, Arg.imm 4, ())) fun r1 =>
         Expr.let_ (Op.mk (OpCode.add i64) (Arg.var assPtr, Arg.var r1.fst, ())) fun r2 =>
         Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var cNode, Arg.imm 1, ())) fun r3 =>
         Expr.let_ (Op.mk (OpCode.or i32) (Arg.var r3.fst, Arg.var pol, ())) fun r4 =>
         Expr.store (t := i32) (Arg.var r4.fst) (Arg.var r2.fst)
         (Expr.call "full_m6_sweep_solve" (as := [i64, i32, i64]) (bs := [i64])
          (Arg.var h, Arg.var nv, Arg.var prem.fst, ())
          fun pd2 =>
          Expr.let_ (Op.mk (OpCode.cmp CmpOp.eq i64) (Arg.var pd2.fst, Arg.imm 10, ()))
           fun c10 =>
          Expr.jnz (Arg.var c10.fst)
           (Expr.group (sig := [[i32]])
            (fun _ => Blocks.cons (fun (p_r : Tup Val [i32]) =>
              Expr.call "full_m6_refine_partition" (as := [i64, i32, i32]) (bs := [i32])
               (Arg.var h, Arg.var nv, Arg.var nclsL, ())
               fun (p_n : Tup Val [i32]) =>
               Expr.jump jLoop
                (Arg.var p_r.fst, Arg.var p_n.fst, Arg.var neq, Arg.var steps1, ()))
              Blocks.nil)
            (fun Js =>
             Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i32) (Arg.var rbit, Arg.imm 64, ()))
              fun (p_c : Tup Val [.bool]) =>
             Expr.jnz (Arg.var p_c.fst)
              (Expr.call "full_m6_sweep_refine_sig" (as := [i64, i32, i32]) (bs := [])
               (Arg.var h, Arg.var nv, Arg.var rbit, ())
               fun (_ : Tup Val []) =>
               Expr.let_ (Op.mk (OpCode.add i32) (Arg.var rbit, Arg.imm 1, ()))
                fun (p_1 : Tup Val [i32]) => Expr.jump Js.fst (Arg.var p_1.fst, ()))
              (Expr.jump Js.fst (Arg.var rbit, ()))))
           (Expr.let_ (Op.mk (OpCode.cmp CmpOp.ne i64) (Arg.var pd2.fst, Arg.imm 20, ()))
             fun c20 =>
            Expr.jnz (Arg.var c20.fst)
             (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var a, ())) fun p0 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p0.fst, Arg.imm 4, ())) fun p1 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pnPtr, Arg.var p1.fst, ())) fun p2 =>
              Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var cNode, ())) fun p3 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p3.fst, Arg.imm 4, ())) fun p4 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pnPtr, Arg.var p4.fst, ())) fun p5 =>
              Expr.load i32 (Arg.var p5.fst) fun ld =>
              Expr.store (t := i32) (Arg.var ld) (Arg.var p2.fst)
              (Expr.group (sig := [[i32]])
               (fun _ => Blocks.cons (fun (pn : Tup Val [i32]) =>
                 Expr.jump jLoop
                  (Arg.var rbit, Arg.var pn.fst, Arg.var neq, Arg.var steps1, ()))
                 Blocks.nil)
               (fun Js =>
                Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var a, ())) fun q0 =>
                Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var q0.fst, Arg.imm 4, ())) fun q1 =>
                Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pnPtr, Arg.var q1.fst, ()))
                 fun q2 =>
                Expr.load i32 (Arg.var q2.fst) fun ld2 =>
                Expr.let_ (Op.mk (OpCode.cmp CmpOp.uge i32) (Arg.var ld2, Arg.var nv, ()))
                 fun qc =>
                Expr.jnz (Arg.var qc.fst)
                 (Expr.let_ (Op.mk (OpCode.sub i32) (Arg.var nclsL, Arg.imm 1, ())) fun qn =>
                   Expr.jump Js.fst (Arg.var qn.fst, ()))
                 (Expr.jump Js.fst (Arg.var nclsL, ())))))
             (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var cNode, ())) fun u0 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var u0.fst, Arg.imm 4, ())) fun u1 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pmPtr, Arg.var u1.fst, ())) fun u2 =>
              Expr.store (t := i32) (Arg.imm 1) (Arg.var u2.fst)
              (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var a, ())) fun v0 =>
               Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var v0.fst, Arg.imm 4, ())) fun v1 =>
               Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pnPtr, Arg.var v1.fst, ())) fun v2 =>
               Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var cNode, ())) fun v3 =>
               Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var v3.fst, Arg.imm 4, ())) fun v4 =>
               Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pnPtr, Arg.var v4.fst, ())) fun v5 =>
               Expr.load i32 (Arg.var v5.fst) fun ld =>
               Expr.store (t := i32) (Arg.var ld) (Arg.var v2.fst)
               (Expr.group (sig := [[i32]])
                (fun _ => Blocks.cons (fun (p_nc : Tup Val [i32]) =>
                  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var gv_c, ())) fun pf0 =>
                  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var pf0.fst, Arg.imm 4, ())) fun pf1 =>
                  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var flPtr, Arg.var pf1.fst, ()))
                   fun pf2 =>
                  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var gv_c, ())) fun pf3 =>
                  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var pf3.fst, Arg.imm 4, ())) fun pf4 =>
                  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var flPtr, Arg.var pf4.fst, ()))
                   fun pf5 =>
                  Expr.load i32 (Arg.var pf5.fst) fun ld =>
                  Expr.let_ (Op.mk (OpCode.not i32) (Arg.imm 1024, ())) fun pf6 =>
                  Expr.let_ (Op.mk (OpCode.and i32) (Arg.var ld, Arg.var pf6.fst, ()))
                   fun pf7 =>
                  Expr.store (t := i32) (Arg.var pf7.fst) (Arg.var pf2.fst)
                  (Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var a, Arg.imm 1, ())) fun l0 =>
                   Expr.let_ (Op.mk (OpCode.xor i32) (Arg.var l0.fst, Arg.imm 1, ())) fun l1 =>
                   Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var cNode, Arg.imm 1, ())) fun l2 =>
                   Expr.let_ (Op.mk (OpCode.or i32) (Arg.var l2.fst, Arg.var pol, ())) fun l3 =>
                   Expr.call "full_k512_add_live_m6" (as := [i64, i32, i32]) (bs := [])
                    (Arg.var h, Arg.var l1.fst, Arg.var l3.fst, ()) fun (_ : Tup Val []) =>
                    Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 6, ())) fun p0 =>
                    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p0.fst, Arg.imm 4, ())) fun p1 =>
                    Expr.let_ (Op.mk (OpCode.add i64) (Arg.var kPtr, Arg.var p1.fst, ()))
                     fun p2 =>
                    Expr.load i32 (Arg.var p2.fst) fun ld =>
                    Expr.let_ (Op.mk (OpCode.cmp CmpOp.ne i32) (Arg.var ld, Arg.imm 0, ()))
                     fun pc =>
                    Expr.jnz (Arg.var pc.fst)
                     (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var h, Arg.imm 1024, ())) fun ph =>
                      Expr.store (t := i64) (Arg.imm 1) (Arg.var ph.fst)
                       (Expr.ret (Arg.imm 20, ())))
                     (Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var a, Arg.imm 1, ())) fun m0 =>
                      Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var cNode, Arg.imm 1, ())) fun m1 =>
                      Expr.let_ (Op.mk (OpCode.or i32) (Arg.var m1.fst, Arg.var pol, ()))
                       fun m2 =>
                      Expr.let_ (Op.mk (OpCode.xor i32) (Arg.var m2.fst, Arg.imm 1, ()))
                       fun m3 =>
                      Expr.call "full_k512_add_live_m6" (as := [i64, i32, i32]) (bs := [])
                       (Arg.var h, Arg.var m0.fst, Arg.var m3.fst, ()) fun (_ : Tup Val []) =>
                       Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 6, ())) fun p0 =>
                       Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p0.fst, Arg.imm 4, ())) fun p1 =>
                       Expr.let_ (Op.mk (OpCode.add i64) (Arg.var kPtr, Arg.var p1.fst, ()))
                        fun p2 =>
                       Expr.load i32 (Arg.var p2.fst) fun ld =>
                       Expr.let_ (Op.mk (OpCode.cmp CmpOp.ne i32) (Arg.var ld, Arg.imm 0, ()))
                        fun pc =>
                       Expr.jnz (Arg.var pc.fst)
                        (Expr.let_ (Op.mk (OpCode.add i64) (Arg.var h, Arg.imm 1024, ()))
                          fun ph =>
                         Expr.store (t := i64) (Arg.imm 1) (Arg.var ph.fst)
                          (Expr.ret (Arg.imm 20, ())))
                        (Expr.group (sig := [[i32]])
                         (fun _ => Blocks.cons (fun (p_neq : Tup Val [i32]) =>
                           Expr.call "full_m6_sweep_rearm" (as := [i64, i32]) (bs := [])
                            (Arg.var h, Arg.var gv_a, ()) fun _ =>
                            Expr.call "full_m6_sweep_rearm" (as := [i64, i32]) (bs := [])
                             (Arg.var h, Arg.var gv_c, ()) fun _ =>
                             Expr.let_ (Op.mk (OpCode.add i64) (Arg.var h, Arg.imm 1080, ()))
                              fun p0 =>
                             Expr.load i64 (Arg.var p0.fst) fun ld =>
                             Expr.let_ (Op.mk (OpCode.add i64) (Arg.var ld, Arg.imm 1, ()))
                              fun p1 =>
                             Expr.let_ (Op.mk (OpCode.add i64) (Arg.var h, Arg.imm 1080, ()))
                              fun p2 =>
                             Expr.store (t := i64) (Arg.var p1.fst) (Arg.var p2.fst)
                              (Expr.jump jLoop (Arg.var rbit, Arg.var p_nc.fst,
                                Arg.var p_neq.fst, Arg.var steps1, ())))
                           Blocks.nil)
                         (fun Js =>
                          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var neq, ())) fun p0 =>
                          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var h, Arg.imm 776, ())) fun p1 =>
                          Expr.load i64 (Arg.var p1.fst) fun ld =>
                          Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i64)
                            (Arg.var p0.fst, Arg.var ld, ())) fun p2 =>
                          Expr.jnz (Arg.var p2.fst)
                           (Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var neq, Arg.imm 1, ()))
                             fun q0 =>
                            Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var q0.fst, ())) fun q1 =>
                            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var q1.fst, Arg.imm 4, ()))
                             fun q2 =>
                            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var eqbPtr, Arg.var q2.fst, ()))
                             fun q3 =>
                            Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var gv_a, Arg.imm 1, ()))
                             fun q4 =>
                            Expr.store (t := i32) (Arg.var q4.fst) (Arg.var q3.fst)
                            (Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var neq, Arg.imm 1, ()))
                              fun q5 =>
                             Expr.let_ (Op.mk (OpCode.add i32) (Arg.var q5.fst, Arg.imm 1, ()))
                              fun q6 =>
                             Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var q6.fst, ())) fun q7 =>
                             Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var q7.fst, Arg.imm 4, ()))
                              fun q8 =>
                             Expr.let_ (Op.mk (OpCode.add i64)
                               (Arg.var eqbPtr, Arg.var q8.fst, ())) fun q9 =>
                             Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var gv_c, Arg.imm 1, ()))
                              fun q10 =>
                             Expr.let_ (Op.mk (OpCode.or i32) (Arg.var q10.fst, Arg.var pol, ()))
                              fun q11 =>
                             Expr.store (t := i32) (Arg.var q11.fst) (Arg.var q9.fst)
                             (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var neq, Arg.imm 1, ()))
                               fun q12 =>
                              Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 24, ())) fun q13 =>
                              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var q13.fst, Arg.imm 4, ()))
                               fun q14 =>
                              Expr.let_ (Op.mk (OpCode.add i64)
                                (Arg.var kPtr, Arg.var q14.fst, ())) fun q15 =>
                              Expr.store (t := i32) (Arg.var q12.fst) (Arg.var q15.fst)
                              (Expr.jump Js.fst (Arg.var q12.fst, ())))))
                           (Expr.jump Js.fst (Arg.var neq, ())))))))
                  Blocks.nil)
                (fun Js =>
                 Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var a, ())) fun q0 =>
                 Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var q0.fst, Arg.imm 4, ())) fun q1 =>
                 Expr.let_ (Op.mk (OpCode.add i64) (Arg.var pnPtr, Arg.var q1.fst, ())) fun q2 =>
                 Expr.load i32 (Arg.var q2.fst) fun ld2 =>
                 Expr.let_ (Op.mk (OpCode.cmp CmpOp.uge i32) (Arg.var ld2, Arg.var nv, ()))
                  fun qc =>
                 Expr.jnz (Arg.var qc.fst)
                  (Expr.let_ (Op.mk (OpCode.sub i32) (Arg.var nclsL, Arg.imm 1, ())) fun qn =>
                    Expr.jump Js.fst (Arg.var qn.fst, ()))
                  (Expr.jump Js.fst (Arg.var nclsL, ())))))))))))
      mS1 := by
  subst h_hdr hkptr hassp hflp hpmp hpnp heqb_p
  have hmL := L.hmaxV; have haL := L.hacap
  have hpol_lt : pol.toNat < 2 := by rcases hpol with rfl | rfl <;> decide
  let P := ConeModelSet F_cur s.scratch.work_stk1 nv.toNat
  have hscrS1_len := dS1.inv.1.scratch_ok.scratch_buf_len
  have hsl_S1 : dS1.st.scratch.scratch_buf.length = L.scrLen := hscrS1_len.trans hL_len.symm
  have h_idx_cap : ∀ x < nv.toNat, k6PhtNext + x < c.scratch_cap := fun x hx => by
    unfold K6Layout.k6Base at hpht_k6b
    unfold K6Layout.scrLen K6Layout.k6Fixed at hL_len
    unfold k6PhtNext at hpht_k6b ⊢; omega
  have h_idx_k6b : ∀ x < nv.toNat, k6PhtNext + x < L.k6Base := fun x hx =>
    Nat.lt_trans (Nat.add_lt_add_left (Nat.lt_of_lt_of_le hx hnv_L) _) hpht_k6b
  obtain ⟨Rfr2, hRfr2⟩ : ∃ Rfr2 : Mem 64 → Prop, Rfr2 = (FullK6Frame c L dS1.st ⋆ R) :=
    ⟨_, rfl⟩
  have hm_ka2 : (K6MemA L (L.kPtr c.pScratchBuf)
      (k6StateOfScratch L dS1.st.scratch.scratch_buf) ⋆ Rfr2) mS1 := by
    have hmF' := dS1.mem
    rw [fullMem_eq_k6Frame hsl_S1] at hmF'; rw [hRfr2]
    exact k6Mem_to_amem dS1.k6.shapes (sep_ac hmF')
  change wp _ _ _ _ _
  c0_hsteps
  try dsimp only [Prod.fst]
  open scoped K6MemATactics K6PtrTactics FullK6DynMem M6Var2PhtMem in c0_hsteps!
  rw [hRfr2] at hm
  refine m6_class_solve2_wp hSolve rfl hL_len hL_mv hpht_k6b hnv_L dS1
    (by change ((a <<< (1 : Nat)) ||| 1#32).toNat < 2 * nv.toNat; rw [ha02]; omega)
    (by change ((cNode <<< (1 : Nat)) ||| pol).toNat < 2 * nv.toNat; rw [ha12]; omega)
    hm fun d2 mS2 dS2 hpreS2 hunsS2 => ?_
  have hc_get_S2 : cNode = dS2.st.scratch.scratch_buf[k6PhtNext + a.toNat]?.getD
      0xFFFFFFFF#32 := by
    rw [hpreS2 _ (h_idx_k6b _ ha_lt)]; exact hc_get
  m6_split
  · m6_to_group
    refine m6_class_refine_wp hRef hRefP rfl hL_len hL_mv hcap hnv_L hnv_mx hnv_2mx hws_lt
      (@hcongr) dS2 fun rbitR new_n mP hdP => by
        m6_steps; exact hJ rbitR new_n neq mP hdP
  m6_split; rotate_left
  · have hd2_20 : d2 = 20#64 := by bv_omega
    obtain ⟨hsem2, hent2⟩ := m6_coneModelSet_unsat_bin
      (by change ((a <<< (1 : Nat)) ||| 1#32).toNat < 2 * nv.toNat; rw [ha02]; omega)
      (by change ((cNode <<< (1 : Nat)) ||| pol).toNat < 2 * nv.toNat; rw [ha12]; omega)
      (hunsS2 hd2_20)
    have hscrS2_len := dS2.inv.1.scratch_ok.scratch_buf_len
    have hsl_S2 : dS2.st.scratch.scratch_buf.length = L.scrLen := hscrS2_len.trans hL_len.symm
    obtain ⟨hslM, hofM, hpkM1, hpkM2, _⟩ := m6_partOk_merge_unlink hsl_S2.symm hnv_L (by omega)
      ha_lt hc_lt hc_get_S2 dS2.part dS2.k6
    let scrM0 := dS2.st.scratch.scratch_buf.set (L.phtMerged + cNode.toNat) 1#32
    let nxtC2 := scrM0[k6PhtNext + cNode.toNat]'(by
      dsimp only [scrM0]; rw [List.length_set, hscrS2_len]; exact h_idx_cap cNode.toNat hc_lt)
    let scrM := scrM0.set (k6PhtNext + a.toNat) nxtC2
    let sM : FullState :=
      { dS2.st with scratch := { dS2.st.scratch with scratch_buf := scrM } }
    have hinvM := m6_fullDenseInvW_with_scratch dS2.inv (hslM.trans hL_len)
      (fuel' := dS2.st.core.fuel)
    have hKM : K6Inv L P (k6StateOfScratch L scrM) := by rw [hofM]; exact dS2.k6
    have hnvM : (k6StateOfScratch L scrM).nv = nv := by rw [hofM]; exact dS2.nv_eq
    have hnqM : (k6StateOfScratch L scrM).neq = neq := by rw [hofM]; exact dS2.neq_eq
    have heqbM := m6_eqBufOk_congr dS2.eqb rfl rfl
    have hmS2 := dS2.mem
    change wp _ _ _ _ _
    open scoped M6PhtMem M6Var2PhtMem in (c0_hsteps_nogrp; try dsimp only [Prod.fst])
    open scoped M6PhtMem M6Var2PhtMem in m6_to_group
    refine wp_join_group (ts := [i32])
      (fun (nclsM, ()) mM => nclsM.toNat ≤ c.max_vars ∧
        ∃ dM : M6ClassData c F0 F_cur s L nv nclsM neq rbit R mM, True)
      (fun _ (nclsM, ()) mM ⟨hncM, dM, _⟩ => by
        have hsem1' : SemEntails (ConeModelSet F_cur s.scratch.work_stk1 nv.toNat)
            [((a <<< (1 : Nat)) ^^^ 1#32).toNat, ((cNode <<< (1 : Nat)) ||| pol).toNat] := by
          rw [hll1_0, hll1_1]; exact hsem1
        have hsem2' : SemEntails (ConeModelSet F_cur s.scratch.work_stk1 nv.toNat)
            [(a <<< (1 : Nat)).toNat, (((cNode <<< (1 : Nat)) ||| pol) ^^^ 1#32).toNat] := by
          rw [hll2_0, hll2_1]; exact hsem2
        refine m6_class_merge_body_wp hLive hQ rfl rfl rfl hL_len hL_mv hpht_k6b hnv_L (by omega)
          ha_lt hc_lt hpol ha01 ha12 hll1_0 hll2_1 hsem1' hsem2' dM ?_
        intro mL2 dL2
        have heq_f : LitEquiv (cnfOfClauses F_cur)
            (gv_a <<< (1 : Nat)).toNat ((gv_c <<< (1 : Nat)) ||| pol).toNat := by
          have he1 : (cnfOfClauses F_cur).EntailsClause
              (cnfClause [(gv_a <<< (1 : Nat)).toNat ^^^ 1,
                ((gv_c <<< (1 : Nat)) ||| pol).toNat]) := by
            rw [show (gv_a <<< (1 : Nat)).toNat ^^^ 1 = ((gv_a <<< (1 : Nat)) ^^^ 1#32).toNat
                by simp, hgl1_0, hgl1_1]
            exact hent1
          have he2 : (cnfOfClauses F_cur).EntailsClause
              (cnfClause [(gv_a <<< (1 : Nat)).toNat,
                ((gv_c <<< (1 : Nat)) ||| pol).toNat ^^^ 1]) := by
            rw [show ((gv_c <<< (1 : Nat)) ||| pol).toNat ^^^ 1 =
                (((gv_c <<< (1 : Nat)) ||| pol) ^^^ 1#32).toNat by simp, hgl2_0, hgl2_1]
            exact hent2
          refine ⟨he1, ?_⟩
          rw [CNF.entails_clause_def] at he2 ⊢; intro β hβ
          have h2 := (clauseEvalVal_iff β _).mpr (he2 β hβ)
          rw [← clauseEvalVal_iff]
          simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false,
            show ((gv_c <<< (1 : Nat)) ||| pol).toNat ^^^ 1 =
              litNeg ((gv_c <<< (1 : Nat)) ||| pol).toNat from rfl] at h2 ⊢
          simpa [Bool.or_comm] using h2
        m6_to_group
        exact m6_class_eq_push_wp hRearm rfl rfl rfl hL_len hL_mv hpht_k6b hnv_L hncM (by omega)
          (by omega) hpol hla_eq hlc_eq heq_f dL2 fun neq' mF hdF =>
            hJ rbit nclsM neq' mF hdF)
      (fun _ hJncl => by
        change wp _ _ _ _ _
        open scoped M6PhtMem M6Var2PhtMem in (c0_hsteps_nogrp; try dsimp only [Prod.fst])
        open scoped M6PhtMem M6Var2PhtMem in m6_split
        · have hn1 : (nclsL - 1#32).toNat ≤ c.max_vars := by
            rw [bv32_sub1_of_pos hncls_pos]; exact Nat.le_trans (Nat.sub_le _ _) dS2.ncls_le
          m6_steps
          exact hJncl (nclsL - 1#32, ()) _
            ⟨hn1, ⟨dS2.rbit_le, hn1, dS2.neq_le, sM, hinvM, dS2.cv, dS2.fuel, dS2.ws, dS2.tmk,
              dS2.trh, hKM, hnvM, hnqM, (by rw [bv32_sub1_of_pos hncls_pos]; exact hpkM2),
              heqbM, by dsimp only [sM, scrM, scrM0, nxtC2]; assumption⟩, trivial⟩
        · m6_steps
          exact hJncl (nclsL, ()) _
            ⟨dS2.ncls_le, ⟨dS2.rbit_le, dS2.ncls_le, dS2.neq_le, sM, hinvM, dS2.cv, dS2.fuel,
              dS2.ws, dS2.tmk, dS2.trh, hKM, hnvM, hnqM, hpkM1, heqbM,
              by dsimp only [sM, scrM, scrM0, nxtC2]; assumption⟩, trivial⟩)
  · refine m6_class_unlink_wp hL_len hnv_L hncls_pos ha_lt hc_lt dS2 hc_get_S2 rfl
      fun ncls' m' hd' => by m6_steps; exact hJ rbit ncls' neq m' hd'

theorem full_m6_sweep_classes_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hBuild : M6EnvSpec Γ "full_m6_sweep_build_pht" m6SweepBuildPhtSpec)
    (hExt : M6EnvSpec Γ "full_m6_extract_pht" m6ExtractPhtSpec)
    (hFlip : M6EnvSpec Γ "full_k6_flip" k6FlipSpec)
    (hRef : M6EnvSpec Γ "full_m6_sweep_refine_sig" m6SweepRefineSigSpec)
    (hRefP : M6EnvSpec Γ "full_m6_refine_partition" m6RefinePartitionSpec)
    (hSolve : M6EnvSpec Γ "full_m6_sweep_solve" m6SweepSolveSpec)
    (hLive : M6EnvSpec Γ "full_k512_add_live_m6" k6AddLiveSpec)
    (hRearm : M6EnvSpec Γ "full_m6_sweep_rearm" m6SweepRearmSpec) :
    ∀ args m Q X, m6SweepClassesSpec args m Q X →
      Func.wp Γ full_m6_sweep_classes_body args m Q X := by
  rintro ⟨h, nv, rbit_in, tick_lim, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv, hcone, hrb_in, hm, hQ⟩
  obtain ⟨hnv1, hnv_mv, hnv_cv, hws_lt, hK_scr, hge_s, hlt_s, hnv_eq⟩ := hcone
  have hlen := hinv.1
  have hcv_le := hlen.core_ok.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hscr_len := hlen.scratch_ok.scratch_buf_len
  have hcap : k6MinScr ≤ c.scratch_cap := hscr_len ▸ hge_s
  have hnv_mx : nv.toNat ≤ c.max_vars := Nat.le_trans hnv_cv hcv_le
  have hnv_2mx : nv.toNat ≤ 2 * c.max_vars := by omega
  let ws1 := s.scratch.work_stk1
  let P := ConeModelSet F_cur ws1 nv.toNat
  obtain ⟨L, hL_def⟩ : ∃ L : K6Layout, L = k6LayoutOfCap c.scratch_cap hcap c.hscr := ⟨_, rfl⟩
  have hL_len : L.scrLen = c.scratch_cap := by
    rw [hL_def]; exact k6LayoutOfCap_scrLen hcap c.hscr
  have hL_mv : L.maxV = k6MaxV c.scratch_cap := by rw [hL_def]; rfl
  clear hL_def
  have hmL := L.hmaxV; have haL := L.hacap
  have hnv_L : nv.toNat ≤ L.maxV := by rw [hL_mv, ← hscr_len]; exact hnv_mv
  have hK0 : K6Inv L P (k6StateOfScratch L s.scratch.scratch_buf) :=
    k6ScratchInv_to_inv (L := L) (hL_len.trans hscr_len.symm) (by rw [hscr_len]; exact hL_mv) hK_scr
  clear hK_scr
  have hnv_bv : (k6StateOfScratch L s.scratch.scratch_buf).nv = nv := by
    have hL_eq : L = k6LayoutOfCap s.scratch.scratch_buf.length hge_s hlt_s :=
      (k6LayoutOfCap_eq (hL_len.trans hscr_len.symm)
        (by rw [hscr_len]; exact hL_mv) hge_s hlt_s).symm
    rw [hL_eq, hnv_eq]
    exact BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt nv.isLt])
  clear hge_s hlt_s hnv_eq
  have hmv64_lt : k6MaxV c.scratch_cap < 2 ^ 32 := by rw [← hL_mv]; omega
  have hmv_eq : BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) = L.mv32 := by
    apply BitVec.eq_of_toNat_eq
    simp only [k6_mv32_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; rw [← hL_mv]; omega
  have hkptr_c0 : c.pScratchBuf + BitVec.setWidth 64
      ((1280 : BitVec 32) + (BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) <<<
        (1 : Nat))) * 4 = L.kPtr c.pScratchBuf := by
    rw [hmv_eq]; exact k6_ptr_base_k6Base L c.pScratchBuf
  have hpm_c0 := m6_ptr_phtMerged L c.pScratchBuf
  have hpm_end : L.phtMerged + L.maxV = L.k6Base := by
    unfold K6Layout.phtMerged K6Layout.k6Base; omega
  have hpht_cap : k6PhtNext + L.maxV < c.scratch_cap := by
    unfold k6PhtNext; unfold K6Layout.phtMerged at hpm_end
    unfold K6Layout.scrLen K6Layout.k6Fixed at hL_len; omega
  have hpht_k6b : k6PhtNext + L.maxV < L.k6Base := by
    unfold k6PhtNext; unfold K6Layout.phtMerged at hpm_end; omega
  have hk6b_bd : L.k6Base < c.scratch_cap := by
    rw [← hL_len]; unfold K6Layout.scrLen K6Layout.k6Fixed; omega
  have h_idx_cap : ∀ x < nv.toNat, k6PhtNext + x < c.scratch_cap := fun x hx =>
    Nat.lt_trans (Nat.add_lt_add_left (Nat.lt_of_lt_of_le hx hnv_L) _) hpht_cap
  have h_idx_k6b : ∀ x < nv.toNat, k6PhtNext + x < L.k6Base := fun x hx =>
    Nat.lt_trans (Nat.add_lt_add_left (Nat.lt_of_lt_of_le hx hnv_L) _) hpht_k6b
  have hpn_c0 : c.pScratchBuf + BitVec.setWidth 64 (1280 : BitVec 32) * 4 =
      c.pScratchBuf + BitVec.ofNat 64 (4 * k6PhtNext) := rfl
  have hpn_c0' : c.pScratchBuf + BitVec.ofNat 64 1280 * 4 =
      c.pScratchBuf + BitVec.ofNat 64 (4 * k6PhtNext) := rfl
  have hass_c0 := k6_ptr_assump L (L.kPtr c.pScratchBuf)
  have hkvals_c0 := k6_ptr_vals L (L.kPtr c.pScratchBuf)
  have hcongr_k6 : ∀ {scrA scrB : List (BitVec 32)}
      (hpre : ∀ i < c.scratch_cap, L.phtMerged ≤ i → scrB[i]? = scrA[i]?)
      (hla : scrA.length = c.scratch_cap) (hlb : scrB.length = c.scratch_cap),
      k6StateOfScratch L scrB = k6StateOfScratch L scrA := fun {scrA scrB} hpre hla hlb => by
    unfold k6StateOfScratch; congr 1
    apply List.ext_getElem
    · simp only [List.length_drop, hla, hlb]
    · intro j hj1 _
      have hj_len : L.k6Base + j < c.scratch_cap := by simp [hlb] at hj1; omega
      have hdom : L.phtMerged ≤ L.k6Base + j := by omega
      have hq := hpre (L.k6Base + j) hj_len hdom
      rw [List.getElem?_eq_getElem (by rw [hlb]; exact hj_len),
        List.getElem?_eq_getElem (by rw [hla]; exact hj_len)] at hq
      simpa only [List.getElem_drop] using Option.some.inj hq
  unfold Func.wp
  run_tac do
    let g ← Lean.Elab.Tactic.getMainGoal
    let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData.headBeta
    let e' ← Lean.Meta.whnf (ty.getArg! 4)
    let ty' := Lean.mkAppN ty.getAppFn (ty.getAppArgs.set! 4 e')
    Lean.Elab.Tactic.replaceMainGoal [← g.change ty' (checkDefEq := false)]
  m6_steps
  refine m6_call_max_v hMaxV (c := c) rfl ?_
  m6_split
  · exfalso; have h0 := congrArg BitVec.toNat hc
    rw [hmv_eq, k6_mv32_toNat] at h0; simp at h0; omega
  m6_split
  · exfalso; rw [← hL_mv, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc; omega
  have hsl_s : s.scratch.scratch_buf.length = L.scrLen := hscr_len.trans hL_len.symm
  obtain ⟨Rfr0, hRfr0⟩ : ∃ Rfr0 : Mem 64 → Prop, Rfr0 = (FullK6Frame c L s ⋆ R) := ⟨_, rfl⟩
  have hm_ka0 : (K6MemA L (L.kPtr c.pScratchBuf) (k6StateOfScratch L s.scratch.scratch_buf) ⋆
      Rfr0) m := by
    rw [fullMem_eq_k6Frame hsl_s] at hm; rw [hRfr0]
    exact k6Mem_to_amem hK0.shapes (sep_ac hm)
  change wp _ _ _ _ _
  c0_hsteps
  try dsimp only [Prod.fst]
  try rw [hkptr_c0]; try rw [hmv_eq]
  open scoped K6MemATactics K6PtrTactics in (c0_hstep; c0_hsteps_nogrp)
  have hKnq0 := k6Inv_set_neq 0#32 hK0
  rw [hRfr0, show (0 : BitVec 32) = 0#32 from rfl] at hm
  let ksNq0 := (k6StateOfScratch L s.scratch.scratch_buf).putHdr .neq 0#32
  let scrNq0 := s.scratch.scratch_buf.take L.k6Base ++ ksNq0.toSlab
  let sNq0 : FullState := { s with scratch := { s.scratch with scratch_buf := scrNq0 } }
  obtain ⟨hscrNq0_len, _, hofNq0, hmNq0⟩ :=
    m6_join_k6_ofSlab (s := s) hL_len hscr_len hKnq0.shapes hm
  change scrNq0.length = c.scratch_cap at hscrNq0_len
  change k6StateOfScratch L scrNq0 = ksNq0 at hofNq0
  change (FullMem c sNq0 ⋆ R) _ at hmNq0
  have hlenNq0 : sNq0.LengthsOk c :=
    ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hscrNq0_len }⟩
  m6_to_group
  refine wp_join_group (ts := [i64])
    (fun (_smask0, ()) ms => ms = m)
    (fun _ (smask0, ()) ms hms => by
      subst ms
      m6_call hBuild
      refine ⟨c, sNq0, L, R, rfl, hlenNq0, hL_len, hL_mv, hnv_L, hnv_2mx, hws_lt, hmNq0,
        fun scrB mB hscrB_len hpreB hphtB hmB => ?_⟩
      let sB : FullState := { sNq0 with scratch := { sNq0.scratch with scratch_buf := scrB } }
      have hlenB : sB.LengthsOk c :=
        ⟨hlenNq0.core_ok, { hlenNq0.scratch_ok with scratch_buf_len := hscrB_len }⟩
      have hofB : k6StateOfScratch L scrB = ksNq0 := by
        rw [← hofNq0]
        exact hcongr_k6 (fun i hi hdom => hpreB i hi (Or.inr hdom)) hscrNq0_len hscrB_len
      m6_call hExt
      refine ⟨c, sB, L, R, rfl, hlenB, hL_len, hL_mv, hnv_L, hnv_mx, hws_lt, hphtB, hmB,
        fun ncls scrE sstkE mclrE mE hscrE_len hsstE_len hmcE_len hpreE hnclsE hpartE hmE => ?_⟩
      let sE : FullState :=
        { sB with
          core := { sB.core with min_clr := mclrE }
          scratch := { sB.scratch with scratch_buf := scrE, shrink_stk := sstkE } }
      have hofE : k6StateOfScratch L scrE = ksNq0 := by
        rw [← hofB]
        exact hcongr_k6 (fun i hi hdom => hpreE i hi (Or.inr hdom)) hscrB_len hscrE_len
      have hinvE := m6_fullDenseInvW_with_cls_scratch hinv hscrE_len hsstE_len hmcE_len
        hlen.scratch_ok.wsort_len
      have hKE : K6Inv L P (k6StateOfScratch L scrE) := by rw [hofE]; exact hKnq0
      have hnvE : (k6StateOfScratch L scrE).nv = nv := by rw [hofE]; exact hnv_bv
      have hnqE : (k6StateOfScratch L scrE).neq = 0#32 := by rw [hofE]; rfl
      have heqbE : M6EqBufOk F_cur sE 0 := ⟨Nat.zero_le _, fun _ h => by cases h⟩
      obtain ⟨initD, _⟩ :
          ∃ d : M6ClassData c F0 F_cur s L nv ncls 0#32 rbit_in R mE, True :=
        ⟨⟨hrb_in, hnclsE, Nat.zero_le _, sE, hinvE, rfl, le_refl _, rfl, rfl, rfl,
          hKE, hnvE, hnqE, hpartE, heqbE, hmE⟩, trivial⟩
      clear heqbE hpartE hnqE hnvE hKE hinvE hofE hpreE hnclsE hmE hmcE_len hsstE_len hscrE_len
      clear sE scrE sstkE mclrE
      clear hmB hphtB hofB hpreB hlenB hscrB_len sB scrB
      clear hmNq0 hofNq0 hlenNq0 hscrNq0_len sNq0 scrNq0 ksNq0 hm
      let steps0 : BitVec 32 := (nv <<< (2 : Nat)) + 64#32
      m6_to_group
      refine wp_loop_inv (ts := [i32, i32, i32, i32])
        (fun (rbit, nclsL, neq, steps, ()) ml =>
          ∃ d : M6ClassData c F0 F_cur s L nv nclsL neq rbit R ml, True)
        (fun (_, _, _, steps, ()) _ => steps.toNat)
        (fun _ hJ => by
          m6_steps; exact hJ (rbit_in, ncls, 0#32, steps0, ()) mE ⟨initD, trivial⟩)
        (fun _ (rbit, nclsL, neq, steps, ()) ml ⟨D, _⟩ hJ => by
          clear initD
          m6_to_group
          refine wp_join_group (ts := [])
            (fun () m_ex => m_ex = ml)
            (fun _ () m_ex hm_ex => by
              have hm_ex_mem : (FullMem c D.st ⋆ R) m_ex := hm_ex ▸ D.mem
              m6_to_group; refine wp_unroll_group fun _ _ => ?_
              m6_split
              · have hinc : D.st.core.inconsistent ≠ 0#64 := by bv_omega
                have huns : F0.Unsat := D.inv.2.1.ext_sound.2 (D.inv.2.1.inconsistent_sound hinc)
                m6_steps
                exact hQ 20#64 D.st m_ex D.inv D.cv D.fuel D.ws D.tmk D.trh (Or.inr rfl)
                  (fun _ => huns) (fun h => by cases h) hm_ex_mem
              · m6_steps
                refine hQ 1#64 D.st m_ex D.inv D.cv D.fuel D.ws D.tmk D.trh (Or.inl rfl)
                  (fun h => by cases h) (fun _ => ⟨L, hL_len, hL_mv, ?_⟩) hm_ex_mem
                rw [D.neq_eq]; exact D.eqb)
            (fun _ hJex => by
              have hml := D.mem
              have hlenD := D.inv.1
              have hscrD_len := hlenD.scratch_ok.scratch_buf_len
              m6_split; rotate_left; · m6_steps; exact hJex () ml rfl
              m6_split; rotate_left; · m6_steps; exact hJex () ml rfl
              m6_split; rotate_left; · m6_steps; exact hJex () ml rfl
              m6_split; rotate_left; · m6_steps; exact hJex () ml rfl
              m6_split; rotate_left; · m6_steps; exact hJex () ml rfl
              change wp _ _ _ _ _
              c0_hsteps_nogrp; try dsimp only [Prod.fst]; try rw [hkptr_c0]; try rw [hmv_eq]
              open scoped FullK6DynMem in m6_split; rotate_left
              · m6_steps; exact hJex () ml rfl
              have hncls_pos : 0 < nclsL.toNat := ‹_›
              have hsteps_pos : 0 < steps.toNat := ‹_›
              have hsteps1 : (steps - 1#32).toNat = steps.toNat - 1 := bv32_sub1_of_pos hsteps_pos
              have ha_idx : ((nclsL - 1#32).setWidth 64).toNat <
                  D.st.scratch.shrink_stk.length := by
                rw [hlenD.scratch_ok.shrink_stk_len, bv_c0_zext32_64]
                rw [bv32_sub1_of_pos hncls_pos]; have := D.ncls_le; omega
              let a := D.st.scratch.shrink_stk[((nclsL - 1#32).setWidth 64).toNat]'ha_idx
              have ha_lt : a.toNat < nv.toNat := by
                have hp := D.part.2.2 (nclsL.toNat - 1) (by omega)
                have hlen_ss := hlenD.scratch_ok.shrink_stk_len
                have hn_le := D.ncls_le
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hp
                dsimp only [a]
                rwa [m6_list_getElem_congr (by rw [bv_c0_zext32_64, bv32_sub1_of_pos hncls_pos])
                  ha_idx (by omega)]
              let cNode := D.st.scratch.scratch_buf[k6PhtNext + a.toNat]'(by
                rw [hscrD_len]; exact h_idx_cap a.toNat ha_lt)
              have hc_get : cNode = D.st.scratch.scratch_buf[k6PhtNext + a.toNat]?.getD
                  0xFFFFFFFF#32 := by
                dsimp only [cNode]
                rw [List.getElem?_eq_getElem (by rw [hscrD_len]; exact h_idx_cap a.toNat ha_lt),
                  Option.getD_some]
              have ha_mv : a.toNat < L.maxV := Nat.lt_of_lt_of_le ha_lt hnv_L
              change wp _ _ _ _ _
              c0_hsteps_nogrp; try dsimp only [Prod.fst]
              try rw [hmv_eq]; try rw [hpm_c0]; try rw [hpn_c0]; try rw [hpn_c0']
              open scoped M6PhtMem in m6_split
              · -- `c >= nv`: drop empty class `ncls = ncls - 1`
                m6_steps
                exact hJ (rbit, nclsL - 1#32, neq, steps - 1#32, ()) ml
                  (by dsimp only; rw [hsteps1]; omega)
                  ⟨⟨D.rbit_le,
                    (by rw [bv32_sub1_of_pos hncls_pos]
                        exact Nat.le_trans (Nat.sub_le _ _) D.ncls_le),
                    D.neq_le, D.st, D.inv, D.cv, D.fuel, D.ws, D.tmk, D.trh, D.k6,
                    D.nv_eq, D.neq_eq,
                    (by rw [bv32_sub1_of_pos hncls_pos]; exact m6_partOk_drop_head D.part),
                    D.eqb, D.mem⟩, trivial⟩
              · have hc_lt : cNode.toNat < nv.toNat := by
                  have : ¬ nv.toNat ≤ cNode.toNat := ‹_›; omega
                have hc_mv : cNode.toNat < L.maxV := Nat.lt_of_lt_of_le hc_lt hnv_L
                have ha_ws : (a.setWidth 64).toNat < D.st.scratch.work_stk1.length := by
                  rw [hlenD.scratch_ok.work_stk1_len, bv_c0_zext32_64]; omega
                have hc_ws : (cNode.setWidth 64).toNat < D.st.scratch.work_stk1.length := by
                  rw [hlenD.scratch_ok.work_stk1_len, bv_c0_zext32_64]; omega
                let gv_a := D.st.scratch.work_stk1[(a.setWidth 64).toNat]'ha_ws
                let gv_c := D.st.scratch.work_stk1[(cNode.setWidth 64).toNat]'hc_ws
                have hgva_ws : (ws1[a.toNat]?.getD 0#32).toNat = gv_a.toNat := by
                  have h_wlen := hlenD.scratch_ok.work_stk1_len
                  dsimp only [gv_a, ws1]
                  rw [← D.ws, List.getElem?_eq_getElem (by rw [h_wlen]; omega), Option.getD_some]
                  exact congrArg BitVec.toNat (m6_list_getElem_congr (bv_c0_zext32_64 a)
                    (by rw [h_wlen]; omega) (by rw [h_wlen]; omega)).symm
                have hgvc_ws : (ws1[cNode.toNat]?.getD 0#32).toNat = gv_c.toNat := by
                  have h_wlen := hlenD.scratch_ok.work_stk1_len
                  dsimp only [gv_c, ws1]
                  rw [← D.ws, List.getElem?_eq_getElem (by rw [h_wlen]; omega), Option.getD_some]
                  exact congrArg BitVec.toNat (m6_list_getElem_congr (bv_c0_zext32_64 cNode)
                    (by rw [h_wlen]; omega) (by rw [h_wlen]; omega)).symm
                have hgva_lt : gv_a.toNat < s.core.cur_vars := by
                  rw [← hgva_ws]; exact hws_lt a.toNat ha_lt
                have hgvc_lt : gv_c.toNat < s.core.cur_vars := by
                  rw [← hgvc_ws]; exact hws_lt cNode.toNat hc_lt
                have ha_fl : (gv_a.setWidth 64).toNat < D.st.core.flags.length := by
                  rw [hlenD.core_ok.flags_len, bv_c0_zext32_64]; omega
                have hc_fl : (gv_c.setWidth 64).toNat < D.st.core.flags.length := by
                  rw [hlenD.core_ok.flags_len, bv_c0_zext32_64]; omega
                change wp _ _ _ _ _
                c0_hsteps_nogrp; try dsimp only [Prod.fst]
                try rw [hmv_eq]; try rw [hpm_c0]; try rw [hpn_c0]; try rw [hpn_c0']
                open scoped M6PhtMem M6Var2PhtMem in m6_to_group
                refine wp_join_group (ts := [])
                  (fun () mU => mU = ml)
                  (fun _ () mU hmU => by
                    subst mU
                    exact m6_class_unlink_wp hL_len hnv_L hncls_pos ha_lt hc_lt D hc_get rfl
                      fun ncls' m' hd' => by
                        m6_steps
                        exact hJ (rbit, ncls', neq, steps - 1#32, ()) m'
                          (by dsimp only; rw [hsteps1]; omega) ⟨hd', trivial⟩)
                  (fun _ hJ_un => by
                  open scoped M6PhtMem M6Var2PhtMem in m6_split
                  · m6_steps; exact hJ_un () ml rfl
                  open scoped M6PhtMem M6Var2PhtMem in m6_split
                  · m6_steps; exact hJ_un () ml rfl
                  m6_split
                  · m6_steps; exact hJ_un () ml rfl
                  m6_split
                  · m6_steps; exact hJ_un () ml rfl
                  -- Active, unmerged pair `(a, c)`: check flip, `d1`, `d2`, merge
                  have ha_mc : (a.setWidth 64).toNat < D.st.core.min_clr.length := by
                    rw [hlenD.core_ok.min_clr_len_arr, bv_c0_zext32_64]; omega
                  have hc_mc : (cNode.setWidth 64).toNat < D.st.core.min_clr.length := by
                    rw [hlenD.core_ok.min_clr_len_arr, bv_c0_zext32_64]; omega
                  let pol : BitVec 32 :=
                    (D.st.core.min_clr[(a.setWidth 64).toNat]'ha_mc &&& 1#32) ^^^
                    (D.st.core.min_clr[(cNode.setWidth 64).toNat]'hc_mc &&& 1#32)
                  have hpol : pol = 0#32 ∨ pol = 1#32 := m6_pol_01 _ _
                  obtain ⟨hpol_lt0, hpol_lt1⟩ : pol.toNat < 2 ∧ (1#32 ^^^ pol).toNat < 2 := by
                    rcases hpol with hp | hp <;> rw [hp] <;> decide
                  obtain ⟨ha01, ha11, ha02, ha12, hla_eq, hlc_eq, hll1_0, hll1_1, hll2_0, hll2_1,
                    hgl1_0, hgl1_1, hgl2_0, hgl2_1⟩ :=
                    m6_bin_lits_align (by omega) (by omega) (by omega) (by omega) hgva_ws hgvc_ws
                      hpol
                  have ha2_lt : (a <<< (1 : Nat)).toNat < 2 * L.maxV := by
                    rw [m6_bv32_shl1_lt (by omega)]; omega
                  have hc2_lt : (cNode <<< (1 : Nat)).toNat < 2 * L.maxV := by
                    rw [m6_bv32_shl1_lt (by omega)]; omega
                  m6_to_group
                  refine wp_join_group (ts := [i32])
                    (fun (fa, ()) mfa => mfa = ml ∧ fa.toNat < 2 * nv.toNat)
                    (fun _ (fa, ()) mfa ⟨hmfa, hfa_lt⟩ => by
                      subst mfa
                      m6_to_group
                      refine wp_join_group (ts := [i32])
                        (fun (fc, ()) mfc => mfc = ml ∧ fc.toNat < 2 * nv.toNat)
                        (fun _ (fc, ()) mfc ⟨hmfc, hfc_lt⟩ => by
                          subst mfc
                          m6_to_group
                          refine wp_join_group (ts := [])
                            (fun () mFl => ∃ dFl : M6ClassData c F0 F_cur s L nv nclsL neq rbit R
                              mFl, True)
                            (fun _ () mFl ⟨dFl, _⟩ => by
                              m6_to_group
                              refine m6_class_refine_wp hRef hRefP rfl hL_len hL_mv hcap hnv_L
                                hnv_mx hnv_2mx hws_lt (@hcongr_k6) dFl
                                fun rbitR new_n mP hdP => by
                                  m6_steps
                                  exact hJ (rbitR, new_n, neq, steps - 1#32, ()) mP
                                    (by dsimp only; rw [hsteps1]; omega) ⟨hdP, trivial⟩)
                            (fun _ hJfl =>
                              m6_class_flip2_wp hFlip rfl hL_len hL_mv hpht_k6b hnv_L hfa_lt hfc_lt
                                D (fun mFl dFl => by m6_steps; exact hJfl () mFl ⟨dFl, trivial⟩)
                                fun mFc dFc hdFc_pre => by
                              -- Both flips failed: solve `d1`
                              let a0_1 := a <<< (1 : Nat)
                              let a1_1 := (cNode <<< (1 : Nat)) ||| (1#32 ^^^ pol)
                              have hscrFc := dFc.inv.1.scratch_ok.scratch_buf_len
                              have hsl_Fc : dFc.st.scratch.scratch_buf.length = L.scrLen :=
                                hscrFc.trans hL_len.symm
                              obtain ⟨Rfr1, hRfr1⟩ :
                                  ∃ Rfr1 : Mem 64 → Prop, Rfr1 = (FullK6Frame c L dFc.st ⋆ R) :=
                                ⟨_, rfl⟩
                              have hm_ka1 : (K6MemA L (L.kPtr c.pScratchBuf)
                                  (k6StateOfScratch L dFc.st.scratch.scratch_buf) ⋆ Rfr1) mFc := by
                                have hmF' := dFc.mem
                                rw [fullMem_eq_k6Frame hsl_Fc] at hmF'; rw [hRfr1]
                                exact k6Mem_to_amem dFc.k6.shapes (sep_ac hmF')
                              change wp _ _ _ _ _
                              c0_hsteps
                              try dsimp only [Prod.fst]
                              try rw [hkptr_c0]; try rw [hmv_eq]; try rw [hass_c0]
                              open scoped K6MemATactics K6PtrTactics FullK6DynMem M6Var2PhtMem in
                                c0_hsteps!
                              rw [hRfr1] at hm
                              refine m6_class_solve2_wp hSolve rfl hL_len hL_mv hpht_k6b hnv_L dFc
                                (by change (a <<< (1 : Nat)).toNat < 2 * nv.toNat; rw [ha01]; omega)
                                (by change ((cNode <<< (1 : Nat)) ||| (1#32 ^^^ pol)).toNat <
                                      2 * nv.toNat
                                    rw [ha11]; omega)
                                hm fun d1 mS1 dS1 hpreS1 hunsS1 => ?_
                              have hc_get_S1 : cNode = dS1.st.scratch.scratch_buf[k6PhtNext +
                                  a.toNat]?.getD 0xFFFFFFFF#32 := by
                                rw [hpreS1 _ (h_idx_k6b _ ha_lt), hdFc_pre _ (h_idx_k6b _ ha_lt),
                                  ← hc_get]
                              m6_split
                              · m6_to_group
                                refine m6_class_refine_wp hRef hRefP rfl hL_len hL_mv hcap hnv_L
                                  hnv_mx hnv_2mx hws_lt (@hcongr_k6) dS1
                                  fun rbitR new_n mP hdP => by
                                    m6_steps
                                    exact hJ (rbitR, new_n, neq, steps - 1#32, ()) mP
                                      (by dsimp only; rw [hsteps1]; omega) ⟨hdP, trivial⟩
                              m6_to_group
                              refine wp_join_group (ts := [])
                                (fun () mU1 => mU1 = mS1)
                                (fun _ () mU1 hmU1 => by
                                  subst mU1
                                  exact m6_class_unlink_wp hL_len hnv_L hncls_pos ha_lt hc_lt dS1
                                    hc_get_S1 rfl fun ncls' m' hd' => by
                                      m6_steps
                                      exact hJ (rbit, ncls', neq, steps - 1#32, ()) m'
                                        (by dsimp only; rw [hsteps1]; omega) ⟨hd', trivial⟩)
                                (fun _ hJu1 => by
                                  m6_split
                                  · m6_steps; exact hJu1 () mS1 rfl
                                  have hscrS1_len := dS1.inv.1.scratch_ok.scratch_buf_len
                                  have hmS1 := dS1.mem
                                  change wp _ _ _ _ _
                                  c0_hsteps_nogrp; try dsimp only [Prod.fst]
                                  try rw [hkptr_c0]; try rw [hmv_eq]
                                  open scoped FullK6DynMem in m6_split
                                  · m6_steps; exact hJu1 () mS1 rfl
                                  have hd1_20 : d1 = 20#64 := by bv_omega
                                  obtain ⟨hsem1, hent1⟩ := m6_coneModelSet_unsat_bin
                                    (by change (a <<< (1 : Nat)).toNat < 2 * nv.toNat
                                        rw [ha01]; omega)
                                    (by change ((cNode <<< (1 : Nat)) ||| (1#32 ^^^ pol)).toNat <
                                          2 * nv.toNat
                                        rw [ha11]; omega)
                                    (hunsS1 hd1_20)
                                  exact m6_class_d2_wp hRef hRefP hSolve hLive hRearm hQ rfl
                                    rfl hass_c0 rfl hpm_c0 hpn_c0' rfl
                                    hL_len hL_mv hcap hpht_k6b hnv_L hnv_mx hnv_2mx hws_lt
                                    (@hcongr_k6) hncls_pos ha_lt hc_lt hgva_lt hgvc_lt hpol
                                    ha01 ha02 ha12 hla_eq hlc_eq hll1_0 hll1_1 hll2_0 hll2_1
                                    hgl1_0 hgl1_1 hgl2_0 hgl2_1 hsem1 hent1 dS1 hc_get_S1
                                    fun rbit' ncls' neq' m' hd' =>
                                      hJ (rbit', ncls', neq', steps - 1#32, ()) m'
                                        (by dsimp only; rw [hsteps1]; omega) ⟨hd', trivial⟩)))
                        (fun _ hJfc => by
                          dsimp only [cNode] at hc2_lt
                          change wp _ _ _ _ _
                          c0_hsteps_nogrp; try dsimp only [Prod.fst]
                          try rw [hkptr_c0]; try rw [hmv_eq]; try rw [hkvals_c0]
                          open scoped FullK6DynMem M6Var2PhtMem in m6_split
                          · m6_steps; exact hJfc (cNode <<< (1 : Nat), ()) ml ⟨rfl, by
                              rw [m6_bv32_shl1_lt (by omega)]; omega⟩
                          · m6_steps
                            have hcc1 : ((cNode <<< (1 : Nat)) ||| 1#32).toNat =
                                2 * cNode.toNat + 1 :=
                              m6_bv32_shl1_or_pol cNode 1#32 (by omega) (by decide)
                            exact hJfc ((cNode <<< (1 : Nat)) ||| 1#32, ()) ml
                              ⟨rfl, by omega⟩))
                    (fun _ hJfa => by
                      dsimp only [a] at ha2_lt
                      change wp _ _ _ _ _
                      c0_hsteps_nogrp; try dsimp only [Prod.fst]
                      try rw [hkptr_c0]; try rw [hmv_eq]; try rw [hkvals_c0]
                      open scoped FullK6DynMem M6Var2PhtMem in m6_split
                      · m6_steps; exact hJfa (a <<< (1 : Nat), ()) ml ⟨rfl, by
                          rw [m6_bv32_shl1_lt (by omega)]; omega⟩
                      · m6_steps
                        have haa1 : ((a <<< (1 : Nat)) ||| 1#32).toNat = 2 * a.toNat + 1 :=
                          m6_bv32_shl1_or_pol a 1#32 (by omega) (by decide)
                        exact hJfa ((a <<< (1 : Nat)) ||| 1#32, ()) ml ⟨rfl, by omega⟩)))))
    (fun _ hJsm => by
      m6_split
      · m6_steps; exact hJsm _ _ rfl
      · m6_steps; exact hJsm _ _ rfl)

/-! ## 2. `full_m6_sweep_var_wp` (`33/39`) -/

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
        (fun Js =>
          Blocks.cons
            (fun (p : Tup Val [i32]) =>
              Expr.let_ (Op.mk (OpCode.cmp CmpOp.ult i32) (Arg.var p.fst, Arg.var nv, ()))
                fun p_1 =>
                Expr.jnz (Arg.var p_1.fst)
                  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p.fst, ()))
                    fun p_2 =>
                    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_2.fst, Arg.imm 4, ()))
                      fun p_3 =>
                      Expr.let_
                        (Op.mk (OpCode.add i64) (Arg.var pWorkStk1, Arg.var p_3.fst, ()))
                        fun p_4 =>
                        Expr.load i32 (Arg.var p_4.fst) fun ld =>
                          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld, ()))
                            fun p_5 =>
                            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p_5.fst, Arg.imm 4, ()))
                              fun p_6 =>
                              Expr.let_
                                (Op.mk (OpCode.add i64)
                                  (Arg.var pTarjanMark, Arg.var p_6.fst, ()))
                                fun p_7 =>
                                Expr.store (t := i32) (Arg.imm 0) (Arg.var p_7.fst)
                                  (Expr.let_
                                    (Op.mk (OpCode.add i32) (Arg.var p.fst, Arg.imm 1, ()))
                                    fun p => Expr.jump Js.fst (Arg.var p.fst, ())))
                  cont)
            Blocks.nil)
        (fun Js => Expr.jump Js.fst (Arg.imm 0, ())))
      mX := by
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
      exact hLc (0#32, ()) mX ⟨Nat.zero_le _, tmk',
        htmkX ▸ hinvX.1.scratch_ok.tarjan_mark_len,
        fun u hu hne => let ⟨k, hk, hwk⟩ := htmk1' u hu hne; ⟨k, Nat.zero_le _, hk, hwk⟩,
        htmkX_sym ▸ hmX⟩)
    (fun _ (i, ()) mi ⟨hi_le, tmk_c, ht_len, ht_inv, hmi⟩ hLc => by
      m6_split
      · have hi_lt : i.toNat < nv.toNat := hc
        have hv_lt : (ws1'[i.toNat]'(by rw [← hwsX, hws_len]; omega)).toNat <
            2 * c.max_vars := by
          have := hconeX i.toNat hi_lt
          rw [hwsX, List.getElem?_eq_getElem (by rw [← hwsX, hws_len]; omega),
            Option.getD_some] at this; omega
        have hi_ws : (BitVec.setWidth 64 i).toNat <
            ({ sX with scratch := { sX.scratch with tarjan_mark := tmk_c } } :
              FullState).scratch.work_stk1.length := by
          change (BitVec.setWidth 64 i).toNat < sX.scratch.work_stk1.length
          rw [hws_len, bv_c0_zext32_64]; omega
        have hwsX_eq : ({ sX with scratch := { sX.scratch with tarjan_mark := tmk_c } } :
            FullState).scratch.work_stk1 = ws1' := hwsX
        have hgv_tmk : (BitVec.setWidth 64 (({ sX with scratch :=
            { sX.scratch with tarjan_mark := tmk_c } } :
            FullState).scratch.work_stk1[(BitVec.setWidth 64 i).toNat]'hi_ws)).toNat <
            ({ sX with scratch := { sX.scratch with tarjan_mark := tmk_c } } :
              FullState).scratch.tarjan_mark.length := by
          change (BitVec.setWidth 64 _).toNat < tmk_c.length
          rw [bv_c0_zext32_64, ht_len]
          have h1 : sX.scratch.work_stk1[(BitVec.setWidth 64 i).toNat]'hi_ws =
              ws1'[i.toNat]'(by rw [← hwsX, hws_len]; omega) := by
            have := congrArg (·[(BitVec.setWidth 64 i).toNat]?) hwsX_eq
            have h64 : (BitVec.setWidth 64 i).toNat = i.toNat := bv_c0_zext32_64 i
            have he : sX.scratch.work_stk1[(BitVec.setWidth 64 i).toNat]'hi_ws =
                sX.scratch.work_stk1[i.toNat]'(by rw [hws_len]; omega) := Option.some.inj (by
              rw [← List.getElem?_eq_getElem hi_ws,
                ← List.getElem?_eq_getElem (by rw [hws_len]; omega), h64])
            rw [he]; cases hwsX; rfl
          rw [h1]; exact hv_lt
        have hi1 : (i + 1#32).toNat = i.toNat + 1 := m6_bv32_add1 (by omega)
        m6_steps
        refine hLc (i + 1#32, ()) _ (by dsimp only; rw [hi1]; exact Nat.sub_lt_sub_left hi_lt (by
          omega)) ⟨by omega, _, List.length_set.trans ht_len, fun u hu hne => ?_, by assumption⟩
        have h64_i : (BitVec.setWidth 64 i).toNat = i.toNat := bv_c0_zext32_64 i
        have hcur1 : sX.scratch.work_stk1[(BitVec.setWidth 64 i).toNat]'hi_ws =
            sX.scratch.work_stk1[i.toNat]'(by rw [hws_len]; omega) := Option.some.inj (by
          rw [← List.getElem?_eq_getElem hi_ws,
            ← List.getElem?_eq_getElem (by rw [hws_len]; omega), h64_i])
        have hcur2 : sX.scratch.work_stk1[i.toNat]'(by rw [hws_len]; omega) =
            ws1'[i.toNat]'(by rw [← hwsX, hws_len]; omega) := by cases hwsX; rfl
        have hcur_eq : ({ sX with scratch := { sX.scratch with tarjan_mark := tmk_c } } :
            FullState).scratch.work_stk1[(BitVec.setWidth 64 i).toNat]'hi_ws =
            ws1'[i.toNat]'(by rw [← hwsX, hws_len]; omega) := hcur1.trans hcur2
        rw [hcur_eq, bv_c0_zext32_64] at hne
        by_cases huv : u = (ws1'[i.toNat]'(by rw [← hwsX, hws_len]; omega)).toNat
        · rw [huv] at hne
          rw [List.getElem?_set_self (by rw [ht_len]; exact hv_lt)] at hne
          exact absurd rfl hne
        · rw [List.getElem?_set_ne (Ne.symm huv)] at hne
          obtain ⟨k, hk1, hk2, hwk⟩ := ht_inv u hu hne
          have hkne : k ≠ i.toNat := by
            rintro rfl
            rw [List.getElem?_eq_getElem (by rw [← hwsX, hws_len]; omega), Option.getD_some] at hwk
            exact huv hwk.symm
          exact ⟨k, by omega, hk2, hwk⟩
      · refine hcont tmk_c mi ht_len (fun u hu => ?_) hmi
        exact Classical.byContradiction fun hne => by
          obtain ⟨k, hk1, hk2, _⟩ := ht_inv u hu hne; omega)

theorem full_m6_sweep_var_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hCone : M6EnvSpec Γ "full_m6_sweep_cone" m6SweepConeSpec)
    (hSim : M6EnvSpec Γ "full_m6_sweep_sim" m6SweepSimSpec)
    (hUnits : M6EnvSpec Γ "full_m6_sweep_units" m6SweepUnitsSpec)
    (hClasses : M6EnvSpec Γ "full_m6_sweep_classes" m6SweepClassesSpec)
    (hEls : M6EnvSpec Γ "full_m6_dense_els" m6DenseElsSpec) :
    ∀ args m Q X, m6SweepVarSpec args m Q X →
      Func.wp Γ full_m6_sweep_var_body args m Q X := by
  rintro ⟨h, root_v, tick_lim, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv, hcap, hroot, htmk, hm, hQ⟩
  have hcv_le := hinv.1.core_ok.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  obtain ⟨L, hL_def⟩ : ∃ L : K6Layout, L = k6LayoutOfCap c.scratch_cap hcap c.hscr := ⟨_, rfl⟩
  have hL_len : L.scrLen = c.scratch_cap := by
    rw [hL_def]; exact k6LayoutOfCap_scrLen hcap c.hscr
  have hL_mv : L.maxV = k6MaxV c.scratch_cap := by rw [hL_def]; rfl
  clear hL_def
  have hmL := L.hmaxV; have haL := L.hacap
  have hmv64_lt : k6MaxV c.scratch_cap < 2 ^ 32 := by rw [← hL_mv]; omega
  have hmv_eq : BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) = L.mv32 := by
    apply BitVec.eq_of_toNat_eq
    simp only [k6_mv32_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; rw [← hL_mv]; omega
  have hkptr_c0 : c.pScratchBuf + BitVec.setWidth 64
      ((1280 : BitVec 32) + (BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) <<<
        (1 : Nat))) * 4 = L.kPtr c.pScratchBuf := by
    rw [hmv_eq]; exact k6_ptr_base_k6Base L c.pScratchBuf
  unfold Func.wp full_m6_sweep_var_body
  m6_steps
  refine m6_call_max_v hMaxV (c := c) rfl ?_
  m6_split
  · exfalso; have h0 := congrArg BitVec.toNat hc
    rw [hmv_eq, k6_mv32_toNat] at h0; simp at h0; omega
  m6_call hCone
  refine ⟨c, F0, F_cur, s, R, rfl, hinv, hcap, hroot, htmk, hm,
    fun pk tmp' ws1' tmk' scr' m1 hinv1 hcv1 hfuel1 _ _ hcone1 _ _ htmk1 hm1 => ?_⟩
  let s1 : FullState :=
    { s with
      core := { s.core with tmp := tmp' }
      scratch := { s.scratch with work_stk1 := ws1', tarjan_mark := tmk', scratch_buf := scr' } }
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
  have hws_ok1 : ∀ i < nv.toNat, (s1.scratch.work_stk1[i]?.getD 0#32).toNat < s1.core.cur_vars :=
    hcone1'.2.2.2.1
  have hscr1_len := hinv1.1.scratch_ok.scratch_buf_len
  change wp _ _ _ _ _
  c0_hsteps_nogrp; try dsimp only [Prod.fst]; try rw [hkptr_c0]; try rw [hmv_eq]
  open scoped FullK6DynMem in m6_split
  · -- `k[K6H_INCONS] != 0u`: UNSAT!
    have hK1 : K6Inv L (ConeModelSet F_cur ws1' nv.toNat) (k6StateOfScratch L scr') :=
      k6ScratchInv_to_inv (L := L) (hL_len.trans hscr1_len.symm)
        (by rw [hscr1_len]; exact hL_mv) hcone1'.2.2.2.2.1
    clear hcone1'
    have hk_inc : (k6StateOfScratch L scr').incons ≠ 0#32 := by
      rw [m6_k6StateOfScratch_incons (by
        rw [hscr1_len, ← hL_len]; unfold K6Layout.scrLen K6Layout.k6Fixed; omega)]
      dsimp only [s1] at *; assumption
    have huns_cur : (cnfOfClauses F_cur).Unsat :=
      m6_coneModelSet_unsat_of_empty (ws1 := ws1') (nv := nv.toNat)
        (hK1.clauses.incons_ok hk_inc)
    have huns_f0 : F0.Unsat := hinv1.2.1.ext_sound.2 huns_cur
    m6_to_group
    refine m6_sweep_tmk_clear_wp rfl rfl hnv_mx hinv1 rfl rfl hws_ok1 htmk1' hm1
      fun tmk_c m_end ht_len ht_done hm_end => by
        m6_steps
        exact hQ 20#64 _ _ (m6_denseInvW_set_inconsistent (m6_fullDenseInvW_with_tmk hinv1 ht_len)
          huns_cur) hcv1 (hfuel1 ▸ le_refl _) ht_done rfl (Or.inr rfl) (fun _ => huns_f0)
          (by assumption)
  m6_to_group
  refine wp_join_group (ts := [])
    (fun () mJ => mJ = m1)
    (fun _ () mJ hmJ => by
      subst hmJ
      m6_to_group
      refine m6_sweep_tmk_clear_wp rfl rfl hnv_mx hinv1 rfl rfl hws_ok1 htmk1' hm1
        fun tmk_c m_end ht_len ht_done hm_end => by
          m6_steps
          exact hQ 1#64 _ m_end (m6_fullDenseInvW_with_tmk hinv1 ht_len) hcv1
            (hfuel1 ▸ le_refl _) ht_done rfl (Or.inl rfl) (fun h => by cases h) hm_end)
    (fun _ hJearly => by
      m6_split; · m6_steps; exact hJearly () m1 rfl
      m6_split; · m6_steps; exact hJearly () m1 rfl
      m6_call hSim
      refine ⟨c, F0, F_cur, s1, R, rfl, hinv1, hcone1', hm1,
        fun rbit fuel2 rng2 sig2 scr2 m2 hinv2 hfuel2 hcone2 huns2 hrb_le2 hm2 => ?_⟩
      clear hcone1'
      let s2 : FullState :=
        { s1 with
          core := { s1.core with fuel := fuel2 }
          scratch := { s1.scratch with rng_state := rng2, sim_sig := sig2, scratch_buf := scr2 } }
      have hfuel2_0 : fuel2.toNat ≤ s.core.fuel.toNat := hfuel1 ▸ hfuel2
      m6_split
      · have hrb_ff : rbit = 0xFFFFFFFF#32 := by bv_omega
        have huns_cur := huns2 hrb_ff
        have huns_f0 : F0.Unsat := hinv2.2.1.ext_sound.2 huns_cur
        m6_to_group
        refine m6_sweep_tmk_clear_wp rfl rfl hnv_mx hinv2 rfl rfl hcone2.2.2.2.1 htmk1' hm2
          fun tmk_c m_end ht_len ht_done hm_end => by
            m6_steps
            exact hQ 20#64 _ _ (m6_denseInvW_set_inconsistent
              (m6_fullDenseInvW_with_tmk hinv2 ht_len) huns_cur) hcv1 hfuel2_0 ht_done rfl
              (Or.inr rfl) (fun _ => huns_f0) (by assumption)
      have hrb_ne_ff : rbit ≠ 0xFFFFFFFF#32 := by bv_omega
      have hrb_64 : rbit.toNat ≤ 64 := hrb_le2 hrb_ne_ff
      m6_split
      · m6_to_group
        refine m6_sweep_tmk_clear_wp rfl rfl hnv_mx hinv2 rfl rfl hcone2.2.2.2.1 htmk1' hm2
          fun tmk_c m_end ht_len ht_done hm_end => by
            m6_steps
            exact hQ 1#64 _ m_end (m6_fullDenseInvW_with_tmk hinv2 ht_len) hcv1 hfuel2_0 ht_done rfl
              (Or.inl rfl) (fun h => by cases h) hm_end
      m6_call hUnits
      refine ⟨c, F0, F_cur, s2, R, rfl, hinv2, hcone2, hrb_64, hm2,
        fun ur s3 m3 hinv3 hcv3 hfuel3 hws3 htmk3 htrh3 hcone3 huns3 hur_le3 hm3 => ?_⟩
      clear hcone2
      have hfuel3_0 : s3.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfuel3 hfuel2_0
      have hcv3_0 : s3.core.cur_vars = s.core.cur_vars := hcv3.trans hcv1
      m6_split
      · have hur_ff : ur = 0xFFFFFFFFFFFFFFFF#64 := by bv_omega
        m6_to_group
        refine m6_sweep_tmk_clear_wp rfl rfl hnv_mx hinv3 hws3 htmk3 hcone3.2.2.2.1
          (fun u hu => htmk1' u (hcv3_0 ▸ hu)) hm3 fun tmk_c m_end ht_len ht_done hm_end => by
            m6_steps
            exact hQ 20#64 _ m_end (m6_fullDenseInvW_with_tmk hinv3 ht_len) hcv3_0 hfuel3_0
              ht_done htrh3 (Or.inr rfl) (fun _ => huns3 hur_ff) hm_end
      have hur_ne_ff : ur ≠ 0xFFFFFFFFFFFFFFFF#64 := by bv_omega
      have hur_64 : (ur.setWidth 32).toNat ≤ 64 := by
        have h1 := hur_le3 hur_ne_ff
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact h1
      m6_steps
      m6_call hClasses
      refine ⟨c, F0, F_cur, s3, R, rfl, hinv3, hcone3, hur_64, hm3,
        fun cr s4 m4 hinv4 hcv4 hfuel4 hws4 htmk4 htrh4 hcr_dom hcr_uns hcr_eq hm4 => ?_⟩
      clear hcone3
      have hfuel4_0 : s4.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfuel4 hfuel3_0
      have hcv4_0 : s4.core.cur_vars = s.core.cur_vars := hcv4.trans hcv3_0
      have hws4_0 : s4.scratch.work_stk1 = ws1' := hws4.trans hws3
      have htmk4_0 : s4.scratch.tarjan_mark = tmk' := htmk4.trans htmk3
      have htrh4_0 : s4.scratch.tarjan_reach = s.scratch.tarjan_reach := htrh4.trans htrh3
      have hws_ok4 : ∀ i < nv.toNat, (s4.scratch.work_stk1[i]?.getD 0#32).toNat <
          s4.core.cur_vars := fun i hi => by
        rw [hws4_0, hcv4_0]; exact hws_ok1 i hi
      m6_to_group
      refine m6_sweep_tmk_clear_wp rfl rfl hnv_mx hinv4 hws4_0 htmk4_0 hws_ok4
        (fun u hu => htmk1' u (hcv4_0 ▸ hu)) hm4 fun tmk_c m_end ht_len ht_done hm_end => by
          let sF : FullState := { s4 with scratch := { s4.scratch with tarjan_mark := tmk_c } }
          have hinvF := m6_fullDenseInvW_with_tmk hinv4 ht_len
          have htmkF_z : M6TmkZero sF := ht_done
          have hscrF_len := hinvF.1.scratch_ok.scratch_buf_len
          m6_split
          · have hcr20 : cr = 20#64 := by bv_omega
            m6_steps
            exact hQ 20#64 sF m_end hinvF hcv4_0 hfuel4_0 htmkF_z htrh4_0 (Or.inr rfl)
              (fun _ => hcr_uns hcr20) hm_end
          m6_split
          · have hinc : s4.core.inconsistent ≠ 0#64 := by bv_omega
            have huns_f0 := hinv4.2.1.ext_sound.2 (hinv4.2.1.inconsistent_sound hinc)
            m6_steps
            exact hQ 20#64 sF m_end hinvF hcv4_0 hfuel4_0 htmkF_z htrh4_0 (Or.inr rfl)
              (fun _ => huns_f0) hm_end
          have hcr_1 : cr = 1#64 := by
            rcases hcr_dom with h1 | h20
            · exact h1
            · exact absurd h20 ‹_›
          have hinc_0 : s4.core.inconsistent = 0#64 := ‹_›
          obtain ⟨L', hL'_len, hL'_mv, heqb4⟩ := hcr_eq hcr_1
          have hLL' : L' = L :=
            K6Layout.eq_of_scrLen_maxV (hL'_len.trans hL_len.symm) (hL'_mv.trans hL_mv.symm)
          rw [hLL'] at heqb4
          have heqbF : M6EqBufOk F_cur sF
              (sF.scratch.scratch_buf[L.k6Base + 24]'(by
                rw [hscrF_len, ← hL_len]; unfold K6Layout.scrLen K6Layout.k6Fixed
                omega)).toNat := by
            have h1 : (k6StateOfScratch L s4.scratch.scratch_buf).neq =
                sF.scratch.scratch_buf[L.k6Base + 24]'(by
                  rw [hscrF_len, ← hL_len]; unfold K6Layout.scrLen K6Layout.k6Fixed
                  omega) :=
              m6_k6StateOfScratch_neq (by
                rw [hinv4.1.scratch_ok.scratch_buf_len, ← hL_len]
                unfold K6Layout.scrLen K6Layout.k6Fixed; omega)
            rw [← h1]; exact heqb4
          change wp _ _ _ _ _
          c0_hsteps_nogrp; try dsimp only [Prod.fst]; try rw [hkptr_c0]; try rw [hmv_eq]
          open scoped FullK6DynMem in m6_to_group
          refine wp_join_group (ts := [])
            (fun () mE => ∃ sE : FullState, FullDenseInvW c F0 F_cur sE ∧
              sE.core.cur_vars = s.core.cur_vars ∧ sE.core.fuel.toNat ≤ s.core.fuel.toNat ∧
              M6TmkZero sE ∧ sE.scratch.tarjan_reach = s.scratch.tarjan_reach ∧
              (sE.core.inconsistent = 0#64 ∨ F0.Unsat) ∧ (FullMem c sE ⋆ R) mE)
            (fun _ () mE ⟨sE, hinvE, hcvE, hfuelE, htmkE, htrhE, hincE, hmE⟩ => by
              m6_to_group; refine wp_unroll_group fun _ _ => ?_
              m6_split
              · have huns_f0 : F0.Unsat := hinvE.2.1.ext_sound.2
                  (hinvE.2.1.inconsistent_sound ‹_›)
                m6_steps
                exact hQ 20#64 sE mE hinvE hcvE hfuelE htmkE htrhE (Or.inr rfl)
                  (fun _ => huns_f0) hmE
              · m6_steps
                exact hQ 1#64 sE mE hinvE hcvE hfuelE htmkE htrhE (Or.inl rfl)
                  (fun h => by cases h) hmE)
            (fun _ hJels => by
              change wp _ _ _ _ _
              c0_hsteps_nogrp; try dsimp only [Prod.fst]; try rw [hkptr_c0]; try rw [hmv_eq]
              open scoped FullK6DynMem in m6_split; rotate_left
              · m6_steps
                exact hJels () m_end ⟨sF, hinvF, hcv4_0, hfuel4_0, htmkF_z, htrh4_0,
                  Or.inl hinc_0, hm_end⟩
              m6_call hEls
              refine ⟨c, F0, F_cur, sF, R, rfl, hinvF, heqbF, hm_end,
                fun ok5 s5 m5 hinv5 hcv5 hfuel5 htmk5 htrh5 _ hok_t hok_f hm5 => ?_⟩
              have hcv5_0 := hcv5.trans hcv4_0
              have hfuel5_0 : s5.core.fuel.toNat ≤ s.core.fuel.toNat := by
                rw [hfuel5]; exact hfuel4_0
              have htmk5_z : M6TmkZero s5 := fun u hu => htmk5 ▸ htmkF_z u (hcv5 ▸ hu)
              have htrh5_0 := htrh5.trans htrh4_0
              m6_split; rotate_left
              · have hok5_f : ok5 = false := by cases ok5 <;> simp at hc ⊢
                m6_steps
                exact hQ 20#64 s5 m5 hinv5 hcv5_0 hfuel5_0 htmk5_z htrh5_0 (Or.inr rfl)
                  (fun _ => (hok_f hok5_f).1) hm5
              · have hok5_t : ok5 = true := by cases ok5 <;> simp at hc ⊢
                m6_steps
                exact hJels () m5 ⟨s5, hinv5, hcv5_0, hfuel5_0, htmk5_z, htrh5_0,
                  Or.inl (hok_t.mp hok5_t), hm5⟩))

end LeanQbe.T.Examples.Kissat.FullM6Sweep
