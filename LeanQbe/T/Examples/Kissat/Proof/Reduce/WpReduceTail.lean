module

public import LeanQbe.T.Examples.Kissat.Proof.Reduce.WpReduceShared
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts2
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Reduce

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Proof.Spec
open scoped FullArenaTactics

local macro "c0_hsteps_ng" : tactic => `(tactic| c0_hsteps_nogrp)

/-- Post-state predicate for `full_reduce_m6` matching `fullReduceM6Spec`. -/
structure RedEndSt (c : FullCfg) (F0 : Std.Sat.CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (force : Bool) (r : BitVec 64) (c' : FullCfg)
    (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64) : Prop where
  compat : FullCfgCompat c c'
  inv : FullM6HdrInv c' F0 ext' s'
  ret : r = 0#64 ∨ r = 1#64 ∨ r = 20#64
  cv_le : s'.core.cur_vars ≤ s.core.cur_vars
  fu_le : s'.core.fuel.toNat ≤ s.core.fuel.toNat
  unsat : r = 20#64 → F0.Unsat
  cl1 : r = 1#64 → s'.core.cur_level ≤ s.core.cur_level
  force_pres : force = true →
    c' = c ∧ RedSt c F0 F_cur s R ext' s' m' ∧ (r = 1#64 → s.core.oom = 0#64 → s'.core.oom = 0#64)
  mem : (FullM6HdrMem c' ext' s' ⋆ R) m'

private theorem fullCfgCompat_refl (c : FullCfg) : FullCfgCompat c c :=
  ⟨rfl, rfl, Nat.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem fullM6HdrInv_of_w2a {c : FullCfg} {F0 : Std.Sat.CNF Nat}
    {ext ext' : List (BitVec 64)} {s s' : FullState}
    (hinv : FullM6HdrInv c F0 ext s) (hcore : s'.core = s.core)
    (hlen : FullState.LengthsOk c s') (hpres : M6HdrScratchPres s s')
    (hext : M6HdrExtOk ext') : FullM6HdrInv c F0 ext' s' := by
  unfold FullM6HdrInv FullSparseInv FullExtScratchOk at hinv ⊢
  rcases hinv with ⟨hcfg, _, ⟨_, hwit⟩, hlm, hnodup, ⟨hll, hextl⟩, hdm⟩
  refine ⟨hcfg, hext, ⟨hlen, ?_⟩, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · simpa [hcore] using hwit
  · simpa [FullLitMarksClear, FullMrkZero, hcore] using hlm
  · intro r hr hg
    simpa [fullArenaClauseRefs, fullArenaClauseRefsCore, fullArenaClauseGarb,
      fullArenaClauseGarbCore, fullArenaClauseLits, fullArenaClauseLitsCore,
      fullArenaClauseSizeCore, fullArenaHdrCore, hcore] using
      hnodup r (by simpa [fullArenaClauseRefs, fullArenaClauseRefsCore, hcore] using hr)
        (by simpa [fullArenaClauseGarb, fullArenaClauseGarbCore, fullArenaHdrCore, hcore] using hg)
  · intro i hi
    have h0 := hll i hi
    dsimp only at h0 ⊢
    rw [hpres.extPres.1]
    simpa [fullArenaClauseRefs, fullArenaClauseRefsCore, hcore] using h0
  · rw [hpres.extPres.2]; exact hextl
  · simpa [hcore] using hdm

theorem redEndSt_of_redSt {c : FullCfg} {F0 : Std.Sat.CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml : Mem 64}
    {force : Bool} {r : BitVec 64}
    (hst : RedSt c F0 F_cur s R ext st ml) (hr : r = 0#64 ∨ r = 1#64 ∨ r = 20#64)
    (huns : r = 20#64 → F0.Unsat) (hoom : r = 1#64 → s.core.oom = 0#64 → st.core.oom = 0#64) :
    RedEndSt c F0 F_cur s R force r c ext st ml :=
  ⟨fullCfgCompat_refl c, hst.inv.toInv, hr, Nat.le_of_eq hst.cv, hst.fu, huns, fun _ => hst.cl,
    fun _ => ⟨rfl, hst, hoom⟩, hst.mem⟩

theorem redEndSt_w2a {c c' : FullCfg} {F0 : Std.Sat.CNF Nat} {F_cur : List (List Nat)}
    {s st s' : FullState} {R : Mem 64 → Prop} {ext ext' : List (BitVec 64)} {m m' : Mem 64}
    {force : Bool} {r : BitVec 64}
    (hst : RedEndSt c F0 F_cur s R force r c' ext st m)
    (hcore : s'.core = st.core) (hlen : FullState.LengthsOk c' s')
    (hpres : M6HdrScratchPres st s') (hext : M6HdrExtOk ext')
    (hm' : (FullM6HdrMem c' ext' s' ⋆ R) m') :
    RedEndSt c F0 F_cur s R force r c' ext' s' m' := by
  refine ⟨hst.compat, fullM6HdrInv_of_w2a hst.inv hcore hlen hpres hext, hst.ret,
    ?_, ?_, hst.unsat, ?_, ?_, hm'⟩
  · simpa [hcore] using hst.cv_le
  · simpa [hcore] using hst.fu_le
  · intro hr1; simpa [hcore] using hst.cl1 hr1
  · intro hf
    obtain ⟨hc, hstW, hoom⟩ := hst.force_pres hf
    subst hc
    exact ⟨rfl, redSt_w2a hstW hcore hlen hpres hext hm',
      fun hr1 hoom0 => by simpa [hcore] using hoom hr1 hoom0⟩

theorem reduce_ret_wm_wp {Γ : Env}
    (hSetWm : Γ.Has "m6_hdr_set_watermark" (m6HdrW2aSpec [i64, i64] []))
    (hClassify : Γ.Has "full_update_classify_fid" (m6HdrW2aSpec [] []))
    {c c' : FullCfg} {F0 : Std.Sat.CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml : Mem 64}
    {force : Bool} {r : BitVec 64} {Q : Post [i64]} {X : XPost}
    (hst : RedEndSt c F0 F_cur s R force r c' ext st ml)
    (hQ : ∀ r0 c0 ext0 s0 m0,
      FullCfgCompat c c0 → FullM6HdrInv c0 F0 ext0 s0 →
      (r0 = 0#64 ∨ r0 = 1#64 ∨ r0 = 20#64) →
      s0.core.cur_vars ≤ s.core.cur_vars → s0.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r0 = 20#64 → F0.Unsat) → (r0 = 1#64 → s0.core.cur_level ≤ s.core.cur_level) →
      (force = true →
        c0 = c ∧ FullM6HdrInvW c F0 F_cur ext0 s0 ∧
        s0.core.cur_level ≤ s.core.cur_level ∧ s0.core.cur_vars = s.core.cur_vars ∧
        s0.core.tmp = s.core.tmp ∧ s0.core.tmp_len = s.core.tmp_len ∧
        s0.core.probing = s.core.probing ∧ s0.core.min_clr_len = s.core.min_clr_len ∧
        s0.scratch.work_stk1 = s.scratch.work_stk1 ∧
        s0.scratch.work_stk2 = s.scratch.work_stk2 ∧
        (r0 = 1#64 → s.core.oom = 0#64 → s0.core.oom = 0#64) ∧
        (0 < s0.core.cur_level →
          s0.core.cur_level = s.core.cur_level ∧ s0.core.vals = s.core.vals ∧
          s0.core.lvl = s.core.lvl ∧ s0.core.trl = s.core.trl ∧
          s0.core.trail_pos = s.core.trail_pos ∧ s0.core.trail_end = s.core.trail_end)) →
      (FullM6HdrMem c0 ext0 s0 ⋆ R) m0 → Q (r0, ()) m0) :
    wp Γ Q X
      (Expr.let_ {
          sig := [i64, i64], code := OpCode.add i64,
          args := (Arg.var c.hdr, Arg.imm 336, ()) } fun p_12 =>
        Expr.load i64 (Arg.var p_12.fst) fun ld =>
        Expr.call (as := [i64, i64, i64]) (bs := []) "m6_hdr_set_watermark"
          (Arg.var c.hdr, Arg.imm 2, Arg.var ld, ()) fun _ =>
        Expr.let_ {
            sig := [i64, i64], code := OpCode.add i64,
            args := (Arg.var c.hdr, Arg.imm 600, ()) } fun p_14 =>
        Expr.load i64 (Arg.var p_14.fst) fun ld =>
        Expr.call (as := [i64, i64, i64]) (bs := []) "m6_hdr_set_watermark"
          (Arg.var c.hdr, Arg.imm 3, Arg.var ld, ()) fun _ =>
        Expr.call (as := [i64]) (bs := []) "full_update_classify_fid"
          (Arg.var c.hdr, ()) fun _ =>
        Expr.ret (Arg.var r, ())) ml := by
  have hhdr : c.hdr = c'.hdr := hst.compat.hdr.symm
  have hinv := hst.inv
  unfold FullM6HdrInv FullSparseInv at hinv
  have hcfg' := hinv.1
  have hext' := hinv.2.1
  have hlen : FullState.LengthsOk c' st := hinv.2.2.1.lengths
  refine wp_m6Hdr_focus_frame hst.mem fun hmF => ?_
  rw [hhdr]
  c0_hsteps_ng
  refine m6Hdr_call_m6HdrW2a rfl (hSetWm _ _) hcfg' hext' hlen
    (fullM6HdrMem_unfocus_full hmF) (fun _ ext1 s1 m1 hc1 hl1 hp1 he1 _ hm1 => ?_)
  have hst1 := redEndSt_w2a hst hc1 hl1 hp1 he1 hm1
  refine wp_m6Hdr_focus_frame hst1.mem fun hmF1 => ?_
  c0_hsteps_ng
  refine m6Hdr_call_m6HdrW2a rfl (hSetWm _ _) hcfg' he1 hl1
    (fullM6HdrMem_unfocus_full hmF1) (fun _ ext2 s2 m2 hc2 hl2 hp2 he2 _ hm2 => ?_)
  have hst2 := redEndSt_w2a hst1 hc2 hl2 hp2 he2 hm2
  refine m6Hdr_call_m6HdrW2a rfl (hClassify _ _) hcfg' he2 hl2 hst2.mem
    (fun _ ext3 s3 m3 hc3 hl3 hp3 he3 _ hm3 => ?_)
  have hst3 := redEndSt_w2a hst2 hc3 hl3 hp3 he3 hm3
  c0_hsteps_ng
  refine hQ r c' ext3 s3 m3 hst3.compat hst3.inv hst3.ret hst3.cv_le hst3.fu_le
    hst3.unsat hst3.cl1 (fun hf => ?_) hst3.mem
  obtain ⟨rfl, hstW, hoom⟩ := hst3.force_pres hf
  exact ⟨rfl, hstW.inv, hstW.cl, hstW.cv, hstW.tmp, hstW.tl, hstW.prb, hstW.mcl,
    hstW.ws1, hstW.ws2, hoom, hstW.pos⟩

theorem reduce_unflushed_wp {Γ : Env}
    (hBtk : Γ.Has "full_backtrack" fullBacktrackSpec)
    (hProp : Γ.Has "full_propagate" PropSearch.Spec.propagateM6Spec)
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml : Mem 64}
    {Js : Cont [i64]} {Q : Post [i64]} {X : XPost}
    (hst : RedSt c F0 F_cur s R ext st ml) (hoom_s : st.core.oom = s.core.oom)
    (hJs : ∀ r ext' st' ml',
      RedSt c F0 F_cur s R ext' st' ml' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → st'.core.unflushed = 0#64) →
      (r = 1#64 → s.core.oom = 0#64 → st'.core.oom = 0#64) → Js (r, ()) ml') :
    wp Γ Q X
      (Expr.let_ {
          sig := [i64, i64], code := OpCode.add i64,
          args := (Arg.var c.hdr, Arg.imm 512, ()) } fun p_10 =>
        Expr.load i64 (Arg.var p_10.fst) fun ld =>
        Expr.let_ {
            sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64,
            args := (Arg.var ld, Arg.imm 0, ()) } fun p_11 =>
        Expr.jnz (Arg.var p_11.fst)
          (Expr.group
            (fun _Js_1 => Blocks.cons (fun (_ : Tup Val []) =>
              Expr.call (as := [i64]) (bs := [i64]) "full_propagate"
                (Arg.var c.hdr, ()) fun p_13 =>
              Expr.group (fun _ => Blocks.cons (fun (p : Tup Val [i64]) =>
                  Expr.jump Js (Arg.var p.fst, ())) Blocks.nil) fun Js_a =>
              Expr.let_ {
                  sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64,
                  args := (Arg.var p_13.fst, Arg.imm 1, ()) } fun p_14 =>
              Expr.jnz (Arg.var p_14.fst) (Expr.jump Js_a.fst (Arg.imm 20, ()))
                (Expr.group (fun _ => Blocks.cons (fun (p : Tup Val [i64]) =>
                    Expr.jump Js_a.fst (Arg.var p.fst, ())) Blocks.nil) fun Js_b =>
                  Expr.let_ {
                      sig := [i64, i64], code := OpCode.cmp CmpOp.ne i64,
                      args := (Arg.var p_13.fst, Arg.imm 0, ()) } fun p_15 =>
                  Expr.jnz (Arg.var p_15.fst) (Expr.jump Js_b.fst (Arg.imm 0, ()))
                    (Expr.let_ {
                        sig := [i64, i64], code := OpCode.add i64,
                        args := (Arg.var c.hdr, Arg.imm 512, ()) } fun p_u =>
                      Expr.store (Arg.imm (t := i64) 0) (Arg.var p_u.fst)
                        (Expr.jump Js_b.fst (Arg.imm 1, ()))))) Blocks.nil)
            (fun Js_1 =>
              Expr.let_ {
                  sig := [i64, i64], code := OpCode.add i64,
                  args := (Arg.var c.hdr, Arg.imm 160, ()) } fun p_12 =>
              Expr.load i64 (Arg.var p_12.fst) fun ld =>
              Expr.let_ {
                  sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64,
                  args := (Arg.var ld, Arg.imm 0, ()) } fun p_13 =>
              Expr.jnz (Arg.var p_13.fst)
                (Expr.call (as := [i64, i64]) (bs := []) "full_backtrack"
                  (Arg.var c.hdr, Arg.imm 0, ()) fun _ => Expr.jump Js_1.fst ())
                (Expr.jump Js_1.fst ())))
          (Expr.jump Js (Arg.imm 1, ()))) ml := by
  have hsp := hst.inv.toInv.sparse
  unfold FullSparseInv at hsp
  have hlen : FullState.LengthsOk c st := hsp.1.lengths
  obtain ⟨_, hwit⟩ := hsp.1.witness
  refine wp_m6Hdr_focus_frame hst.mem fun hmF => ?_
  c0_hsteps_ng
  · refine wp_join_group (fun (_ : Tup Val []) mb =>
        ∃ sB : FullState, RedSt c F0 F_cur s R ext sB mb ∧
          sB.core.cur_level = 0 ∧ sB.core.oom = s.core.oom)
      (fun _ _ mb ⟨sB, hstB, hclB, hoomB⟩ => by
        refine red_call_propagate0 rfl hProp hstB hclB
          (fun rp ext' s' m' hst' _ _ hret hoomP huns => ?_)
        refine wp_join_group (fun (xs : Tup Val [i64]) ma => Js xs ma)
          (fun _ (xs : Tup Val [i64]) ma h => by rcases xs with ⟨x, ⟨⟩⟩; c0_hsteps_ng; exact h)
          (fun _ hJa => ?_)
        c0_hsteps_ng
        · have hrp : rp = 1#64 := by assumption
          exact hJa (20#64, ()) m' (hJs 20#64 ext' s' m' hst' (Or.inr (Or.inr rfl))
            (fun _ => huns hrp) (fun h => by cases h) (fun h => by cases h))
        · have hrp_ne1 : rp ≠ 1#64 := by assumption
          refine wp_join_group (fun (xs : Tup Val [i64]) ma => Js xs ma)
            (fun _ (xs : Tup Val [i64]) ma h => by
              rcases xs with ⟨x, ⟨⟩⟩; c0_hsteps_ng; exact hJa (x, ()) ma h)
            (fun _ hJb => ?_)
          c0_hsteps_ng
          · exact hJb (0#64, ()) m' (hJs 0#64 ext' s' m' hst' (Or.inl rfl)
              (fun h => by cases h) (fun h => by cases h) (fun h => by cases h))
          · have hrp0 : rp = 0#64 := by
              rcases hret with rfl | rfl | rfl
              · rfl
              · exact False.elim (hrp_ne1 rfl)
              · exact False.elim (by cases (by assumption : (2#64 : BitVec 64) = 0#64))
            have hlen' : FullState.LengthsOk c s' := hst'.inv.toInv.sparse.lengths
            refine wp_m6Hdr_focus_frame hst'.mem fun hmF' => ?_
            c0_hsteps_ng
            have hst0 := redSt_with_unflushed hst' 0#64 (fullM6HdrMem_unfocus_full (by assumption))
            exact hJb (1#64, ()) _ (hJs 1#64 ext' _ _ hst0 (Or.inr (Or.inl rfl))
              (fun h => by cases h) (fun _ => rfl)
              (fun _ hs => hoomP hrp0 (hoomB.symm ▸ hs))))
      (fun _ hJ1 => by
        refine wp_m6Hdr_focus_frame (fullM6HdrMem_unfocus_full hmF) fun hmF' => ?_
        c0_hsteps_ng
        · refine red_call_backtrack0 rfl hBtk hst fun sB mB hstB hclB hoomB => ?_
          c0_hsteps_ng
          exact hJ1 () mB ⟨sB, hstB, hclB, hoomB.trans hoom_s⟩
        · have hclz : st.core.cur_level = 0 := by
            have hcl_lt : st.core.cur_level < 2 ^ 64 := by
              have := hwit.cur_level_le; have := hlen.core_ok.trail_end_le
              have := hlen.core_ok.cur_vars_le; have := c.hmaxv
              have : 2 * LeanQbe.T.Examples.Kissat.Ref.dimacsBound < 2 ^ 32 := by decide
              omega
            have hcl_bv :
                ¬ (0#64 : BitVec 64).toNat < st.core.cur_level % 2 ^ 64 := by assumption
            rw [Nat.mod_eq_of_lt hcl_lt] at hcl_bv
            change ¬ 0 < st.core.cur_level at hcl_bv
            omega
          exact hJ1 () ml ⟨st, hst, hclz, hoom_s⟩)
  · have hu_hc : ¬ (0#64 : BitVec 64).toNat < st.core.unflushed.toNat := by assumption
    change ¬ 0 < st.core.unflushed.toNat at hu_hc
    have huf : st.core.unflushed = 0#64 := BitVec.eq_of_toNat_eq (by
      rw [show (0#64 : BitVec 64).toNat = 0 from rfl]; omega)
    exact hJs 1#64 ext st ml hst (Or.inr (Or.inl rfl)) (fun h => by cases h) (fun _ => huf)
      (fun _ h => hoom_s.trans h)

theorem reduce_keep_bool_wp {Γ : Env} {Js : Cont [.bool]} {Q : Post [i64]} {X : XPost}
    {glue tier1 tier2 : BitVec 64} {used32 : BitVec 32} {ml : Mem 64}
    (hJs : ∀ b : Bool, Js (b, ()) ml) :
    wp Γ Q X
      (Expr.group
        (fun _Js_4 => Blocks.cons (fun (_ : Tup Val []) =>
          Expr.let_ {
              sig := [i64, i64], code := OpCode.cmp CmpOp.ule i64,
              args := (Arg.var glue, Arg.var tier2, ()) } fun p_u1 =>
          Expr.jnz (Arg.var p_u1.fst)
            (Expr.let_ {
                sig := [i32, i32], code := OpCode.cmp CmpOp.uge i32,
                args := (Arg.var used32, Arg.imm 30, ()) } fun p_u2 =>
              Expr.jnz (Arg.var p_u2.fst) (Expr.jump Js (Arg.imm true, ()))
                (Expr.jump Js (Arg.imm false, ())))
            (Expr.jump Js (Arg.imm false, ()))) Blocks.nil)
        (fun Js_4 =>
          Expr.let_ {
              sig := [i64, i64], code := OpCode.cmp CmpOp.ule i64,
              args := (Arg.var glue, Arg.var tier1, ()) } fun p_u1 =>
          Expr.jnz (Arg.var p_u1.fst)
            (Expr.let_ {
                sig := [i32, i32], code := OpCode.cmp CmpOp.ugt i32,
                args := (Arg.var used32, Arg.imm 0, ()) } fun p_u2 =>
              Expr.jnz (Arg.var p_u2.fst) (Expr.jump Js (Arg.imm true, ()))
                (Expr.jump Js_4.fst ()))
            (Expr.jump Js_4.fst ()))) ml := by
  refine wp_join_group (fun (_ : Tup Val []) mb => mb = ml)
    (fun _ _ mb hmb => by subst hmb; c0_hsteps_ng <;> exact hJs _)
    (fun _ hJ4 => by c0_hsteps_ng <;> first | exact hJs true | exact hJ4 () ml rfl)

theorem reduce_collect_push_wp {Γ : Env}
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml : Mem 64}
    {Js : Cont [i64]} {Q : Post [i64]} {X : XPost}
    {keep : Bool} {rc pos : BitVec 64}
    (hst : RedSt c F0 F_cur s R ext st ml) (hrm : FullReasonsMarked st)
    (hrr : RedRefsOk st rc.toNat)
    (hp_mem : pos.toNat ∈ fullArenaClauseRefs st) (hp_lt : pos.toNat < 2 ^ 32)
    (hnrsn : fullArenaHdr st pos.toNat &&& 2097152#32 = 0#32)
    (hJs : ∀ rc' st' ml',
      RedSt c F0 F_cur s R ext st' ml' → FullReasonsMarked st' →
      RedRefsOk st' rc'.toNat → rc'.toNat ≤ c.red_cap →
      st'.core = st.core → st'.scratch.scratch_buf = st.scratch.scratch_buf →
      st'.scratch.glue_used = st.scratch.glue_used →
      st'.scratch.tier1 = st.scratch.tier1 → st'.scratch.tier2 = st.scratch.tier2 →
      Js (rc', ()) ml') :
    rc.toNat ≤ c.red_cap →
    wp Γ Q X
      (Expr.group (fun _ => Blocks.cons (fun (p : Tup Val [i64]) =>
          Expr.jump Js (Arg.var p.fst, ())) Blocks.nil)
        fun Js_i =>
        Expr.jnz (Arg.var keep) (Expr.jump Js_i.fst (Arg.var rc, ()))
          (Expr.let_ {
              sig := [i64, i64], code := OpCode.add i64,
              args := (Arg.var c.hdr, Arg.imm 440, ()) } fun p_cap =>
            Expr.load i64 (Arg.var p_cap.fst) fun ld_cap =>
            Expr.let_ {
                sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64,
                args := (Arg.var rc, Arg.var ld_cap, ()) } fun p_lt =>
            Expr.jnz (Arg.var p_lt.fst)
              (Expr.let_ {
                  sig := [i64, i64], code := OpCode.mul i64,
                  args := (Arg.var rc, Arg.imm 4, ()) } fun p_off =>
                Expr.let_ {
                    sig := [i64, i64], code := OpCode.add i64,
                    args := (Arg.var c.pRedRefs, Arg.var p_off.fst, ()) } fun p_addr =>
                Expr.let_ {
                    sig := [i64], code := OpCode.trunc 64 32,
                    args := (Arg.var pos, ()) } fun p_tr =>
                Expr.store (Arg.var p_tr.fst) (Arg.var p_addr.fst)
                  (Expr.let_ {
                      sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var rc, Arg.imm 1, ()) } fun p_rc1 =>
                    Expr.jump Js_i.fst (Arg.var p_rc1.fst, ())))
              (Expr.jump Js_i.fst (Arg.var rc, ())))) ml := by
  intro hrc_le
  refine wp_join_group (fun (xs : Tup Val [i64]) mb => Js xs mb)
    (fun _ (xs : Tup Val [i64]) mb h => by c0_hsteps_ng; exact h) (fun _ hJi => ?_)
  have hlen : FullState.LengthsOk c st := hst.inv.toInv.sparse.lengths
  have hrr_len : st.scratch.red_refs.length = c.red_cap := hlen.scratch_ok.red_refs_len
  refine wp_m6Hdr_focus_frame hst.mem fun hmF => ?_
  c0_hsteps_ng
  · exact hJi (rc, ()) ml (hJs rc st ml hst hrm hrr hrc_le rfl rfl rfl rfl rfl)
  · have hrc_lt : rc.toNat < c.red_cap := by
      have hrc_b : rc.toNat < (BitVec.ofNat 64 c.red_cap).toNat := by assumption
      have hcap64 : c.red_cap < 2 ^ 64 := by have := c.havail_fit; have := c.hsize; omega
      simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap64] using hrc_b
    have hrc_arr : rc.toNat < st.scratch.red_refs.length := by omega
    have hrc_64 : rc.toNat + 1 < 2 ^ 64 := by have := c.havail_fit; have := c.hsize; omega
    c0_hsteps_ng
    have hm' := fullM6HdrMem_unfocus_full (by assumption)
    let sc' : FullScratch :=
      { st.scratch with red_refs := st.scratch.red_refs.set rc.toNat (BitVec.truncate 32 pos) }
    have hsc_len : FullScratch.LengthsOk c sc' :=
      { hlen.scratch_ok with red_refs_len := by simp [sc', hrr_len] }
    have hst' := redSt_with_scratch hst hsc_len rfl rfl rfl rfl hm'
    have htr : BitVec.truncate 32 pos = BitVec.ofNat 32 pos.toNat := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
      simp [Nat.mod_eq_of_lt hp_lt]
    have hrr' : RedRefsOk { core := st.core, scratch := sc' } (rc + 1#64).toNat := by
      rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
        Nat.mod_eq_of_lt hrc_64, show sc' = { st.scratch with
          red_refs := st.scratch.red_refs.set rc.toNat (BitVec.truncate 32 pos) } from rfl, htr]
      exact redRefsOk_push hrr_len hrc_lt hp_lt hp_mem hnrsn hrr
    exact hJi (rc + 1#64, ()) _ (hJs (rc + 1#64) _ _ hst' hrm hrr'
      (by rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
        Nat.mod_eq_of_lt hrc_64]; omega) rfl rfl rfl rfl rfl)
  · exact hJi (rc, ()) ml (hJs rc st ml hst hrm hrr hrc_le rfl rfl rfl rfl rfl)

theorem red_pos_lt_arena {c : FullCfg} {F0 : Std.Sat.CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml : Mem 64}
    {pos : Nat} (hst : RedSt c F0 F_cur s R ext st ml)
    (hp_mem : pos ∈ fullArenaClauseRefs st) : pos < st.core.arena.length := by
  have hsp := hst.inv.toInv.sparse
  have hlen := hsp.lengths
  unfold FullSparseInv at hsp
  obtain ⟨_, hw⟩ := hsp.1.witness
  have hp_refs := (hw.arena.refs_wf pos hp_mem).1
  have hal_le := hlen.core_ok.arena_len_le
  have har_len := hlen.core_ok.arena_len_arr
  omega

theorem reduce_collect_jr_wp {Γ : Env}
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml : Mem 64}
    {Js_lp : Cont [i64, i64]} {Q : Post [i64]} {X : XPost}
    {rc pos : BitVec 64} {next32 : BitVec 32} {tier1 tier2 : BitVec 64}
    (hst : RedSt c F0 F_cur s R ext st ml) (hrm : FullReasonsMarked st)
    (hrr : RedRefsOk st rc.toNat) (hrc_le : rc.toNat ≤ c.red_cap)
    (hp_mem : pos.toNat ∈ fullArenaClauseRefs st)
    (hJs : ∀ rc' st' ml',
      RedSt c F0 F_cur s R ext st' ml' → FullReasonsMarked st' →
      RedRefsOk st' rc'.toNat → rc'.toNat ≤ c.red_cap →
      (BitVec.zeroExtend 64 next32).toNat ∈ fullArenaClauseRefs st' ∨
        (BitVec.zeroExtend 64 next32).toNat = st'.core.arena_len →
      st'.core.arena_len = st.core.arena_len →
      st'.core.cur_level = st.core.cur_level → st'.core.oom = st.core.oom →
      st'.core.unflushed = st.core.unflushed →
      st'.scratch.tier1 = st.scratch.tier1 → st'.scratch.tier2 = st.scratch.tier2 →
      Js_lp (rc', BitVec.zeroExtend 64 next32, ()) ml') :
    ((BitVec.zeroExtend 64 next32).toNat ∈ fullArenaClauseRefs st ∨
      (BitVec.zeroExtend 64 next32).toNat = st.core.arena_len) →
    let ld_6 := st.core.arena[pos.toNat]'(red_pos_lt_arena hst hp_mem)
    wp Γ Q X
      (Expr.group
        (fun _ => Blocks.cons (fun (p : Tup Val [i64]) =>
          Expr.let_ {
              sig := [i32], code := OpCode.zext 32 64, args := (Arg.var next32, ()) }
            fun p_26 => Expr.jump Js_lp (Arg.var p.fst, Arg.var p_26.fst, ())) Blocks.nil)
        fun Js_n =>
        Expr.let_ {
            sig := [i32, i32], code := OpCode.and i32,
            args := (Arg.var ld_6, Arg.imm 4194304, ()) } fun p_26 =>
        Expr.let_ {
            sig := [i32, i32], code := OpCode.cmp CmpOp.ne i32,
            args := (Arg.var p_26.fst, Arg.imm 0, ()) } fun p_27 =>
        Expr.jnz (Arg.var p_27.fst)
          (Expr.let_ {
              sig := [i32, i32], code := OpCode.and i32,
              args := (Arg.var ld_6, Arg.imm 524288, ()) } fun p_28 =>
            Expr.let_ {
                sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32,
                args := (Arg.var p_28.fst, Arg.imm 0, ()) } fun p_29 =>
            Expr.jnz (Arg.var p_29.fst)
              (Expr.let_ {
                  sig := [i32, i32], code := OpCode.lshr i32,
                  args := (Arg.var ld_6, Arg.imm 27, ()) } fun p_30 =>
                Expr.let_ {
                    sig := [i32, i32], code := OpCode.and i32,
                    args := (Arg.var p_30.fst, Arg.imm 31, ()) } fun p_31 =>
                Expr.group (fun _Js_3 => Blocks.cons (fun (_ : Tup Val []) =>
                    Expr.group (fun _ => Blocks.cons (fun (p : Tup Val [i64]) =>
                        Expr.jump Js_n.fst (Arg.var p.fst, ())) Blocks.nil) fun Js_f =>
                    Expr.let_ {
                        sig := [i32, i32], code := OpCode.and i32,
                        args := (Arg.var ld_6, Arg.imm 2097152, ()) } fun p_33 =>
                    Expr.let_ {
                        sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32,
                        args := (Arg.var p_33.fst, Arg.imm 0, ()) } fun p_34 =>
                    Expr.jnz (Arg.var p_34.fst)
                      (Expr.let_ {
                          sig := [i32, i32], code := OpCode.and i32,
                          args := (Arg.var ld_6, Arg.imm 524287, ()) } fun p_35 =>
                        Expr.let_ {
                            sig := [i32], code := OpCode.zext 32 64,
                            args := (Arg.var p_35.fst, ()) } fun p_36 =>
                        Expr.group (fun _ => Blocks.cons (fun (p_37 : Tup Val [.bool]) =>
                            Expr.group (fun _ => Blocks.cons (fun (p : Tup Val [i64]) =>
                                Expr.jump Js_f.fst (Arg.var p.fst, ())) Blocks.nil) fun Js_i =>
                            Expr.jnz (Arg.var p_37.fst) (Expr.jump Js_i.fst (Arg.var rc, ()))
                              (Expr.let_ {
                                  sig := [i64, i64], code := OpCode.add i64,
                                  args := (Arg.var c.hdr, Arg.imm 440, ()) } fun p_cap =>
                                Expr.load i64 (Arg.var p_cap.fst) fun ld_cap =>
                                Expr.let_ {
                                    sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64,
                                    args := (Arg.var rc, Arg.var ld_cap, ()) } fun p_lt =>
                                Expr.jnz (Arg.var p_lt.fst)
                                  (Expr.let_ {
                                      sig := [i64, i64], code := OpCode.mul i64,
                                      args := (Arg.var rc, Arg.imm 4, ()) } fun p_off =>
                                    Expr.let_ {
                                        sig := [i64, i64], code := OpCode.add i64,
                                        args := (Arg.var c.pRedRefs, Arg.var p_off.fst, ()) }
                                      fun p_addr =>
                                    Expr.let_ {
                                        sig := [i64], code := OpCode.trunc 64 32,
                                        args := (Arg.var pos, ()) } fun p_tr =>
                                    Expr.store (Arg.var p_tr.fst) (Arg.var p_addr.fst)
                                      (Expr.let_ {
                                          sig := [i64, i64], code := OpCode.add i64,
                                          args := (Arg.var rc, Arg.imm 1, ()) } fun p_rc1 =>
                                        Expr.jump Js_i.fst (Arg.var p_rc1.fst, ())))
                                  (Expr.jump Js_i.fst (Arg.var rc, ())))) Blocks.nil)
                          (fun Js_k =>
                            Expr.group (fun _Js_4 => Blocks.cons (fun (_ : Tup Val []) =>
                                Expr.let_ {
                                    sig := [i64, i64], code := OpCode.cmp CmpOp.ule i64,
                                    args := (Arg.var p_36.fst, Arg.var tier2, ()) } fun p_u1 =>
                                Expr.jnz (Arg.var p_u1.fst)
                                  (Expr.let_ {
                                      sig := [i32, i32], code := OpCode.cmp CmpOp.uge i32,
                                      args := (Arg.var p_31.fst, Arg.imm 30, ()) } fun p_u2 =>
                                    Expr.jnz (Arg.var p_u2.fst)
                                      (Expr.jump Js_k.fst (Arg.imm true, ()))
                                      (Expr.jump Js_k.fst (Arg.imm false, ())))
                                  (Expr.jump Js_k.fst (Arg.imm false, ()))) Blocks.nil)
                              (fun Js_4 =>
                                Expr.let_ {
                                    sig := [i64, i64], code := OpCode.cmp CmpOp.ule i64,
                                    args := (Arg.var p_36.fst, Arg.var tier1, ()) } fun p_u1 =>
                                Expr.jnz (Arg.var p_u1.fst)
                                  (Expr.let_ {
                                      sig := [i32, i32], code := OpCode.cmp CmpOp.ugt i32,
                                      args := (Arg.var p_31.fst, Arg.imm 0, ()) } fun p_u2 =>
                                    Expr.jnz (Arg.var p_u2.fst)
                                      (Expr.jump Js_k.fst (Arg.imm true, ()))
                                      (Expr.jump Js_4.fst ()))
                                  (Expr.jump Js_4.fst ()))))
                      (Expr.jump Js_f.fst (Arg.var rc, ()))) Blocks.nil)
                  (fun Js_3 =>
                    Expr.let_ {
                        sig := [i32, i32], code := OpCode.cmp CmpOp.ugt i32,
                        args := (Arg.var p_31.fst, Arg.imm 0, ()) } fun p_ug =>
                    Expr.jnz (Arg.var p_ug.fst)
                      (Expr.let_ {
                          sig := [i64, i64], code := OpCode.mul i64,
                          args := (Arg.var pos, Arg.imm 4, ()) } fun p_off =>
                        Expr.let_ {
                            sig := [i64, i64], code := OpCode.add i64,
                            args := (Arg.var c.pArena, Arg.var p_off.fst, ()) } fun p_addr =>
                        Expr.let_ {
                            sig := [i32, i32], code := OpCode.and i32,
                            args := (Arg.var ld_6, Arg.imm 134217727, ()) } fun p_lo =>
                        Expr.let_ {
                            sig := [i32, i32], code := OpCode.sub i32,
                            args := (Arg.var p_31.fst, Arg.imm 1, ()) } fun p_dec =>
                        Expr.let_ {
                            sig := [i32, i32], code := OpCode.shl i32,
                            args := (Arg.var p_dec.fst, Arg.imm 27, ()) } fun p_hi =>
                        Expr.let_ {
                            sig := [i32, i32], code := OpCode.or i32,
                            args := (Arg.var p_lo.fst, Arg.var p_hi.fst, ()) } fun p_nv =>
                        Expr.store (Arg.var p_nv.fst) (Arg.var p_addr.fst)
                          (Expr.jump Js_3.fst ()))
                      (Expr.jump Js_3.fst ())))
              (Expr.jump Js_n.fst (Arg.var rc, ())))
          (Expr.jump Js_n.fst (Arg.var rc, ()))) ml := by
  intro hnxt ld_6
  refine wp_join_group (fun (xs : Tup Val [i64]) mb =>
      Js_lp (xs.fst, BitVec.zeroExtend 64 next32, ()) mb)
    (fun _ (xs : Tup Val [i64]) mb h => by c0_hsteps_ng; exact h) (fun _ hJn => ?_)
  have hp_ar : pos.toNat < st.core.arena.length := red_pos_lt_arena hst hp_mem
  have hp_lt32 : pos.toNat < 2 ^ 32 := by
    have := c.harena
    have := hst.inv.toInv.sparse.lengths.core_ok.arena_len_arr
    have : 2 * LeanQbe.T.Examples.Kissat.Ref.dimacsBound < 2 ^ 32 := by decide
    omega
  c0_hsteps_ng
  · refine wp_join_group (fun (_ : Tup Val []) mb =>
        ∃ stU : FullState, RedSt c F0 F_cur s R ext stU mb ∧ FullReasonsMarked stU ∧
          fullArenaClauseRefs stU = fullArenaClauseRefs st ∧ RedRefsOk stU rc.toNat ∧
          fullArenaHdr stU pos.toNat &&& 2097152#32 = ld_6 &&& 2097152#32 ∧
          stU.core.arena_len = st.core.arena_len ∧ stU.core.cur_level = st.core.cur_level ∧
          stU.core.oom = st.core.oom ∧ stU.core.unflushed = st.core.unflushed ∧
          stU.scratch.tier1 = st.scratch.tier1 ∧ stU.scratch.tier2 = st.scratch.tier2)
      (fun _ _ mb ⟨stU, hstU, hrmU, hrfU, hrrU, hnhU, h1, h2, h3, h4, h5, h6⟩ => by
        refine wp_join_group (fun (xs : Tup Val [i64]) ma =>
            Js_lp (xs.fst, BitVec.zeroExtend 64 next32, ()) ma)
          (fun _ (xs : Tup Val [i64]) ma h => by c0_hsteps_ng; exact hJn xs ma h)
          (fun _ hJf => ?_)
        c0_hsteps_ng
        · have hnrsn : fullArenaHdr stU pos.toNat &&& 2097152#32 = 0#32 := by
            rw [hnhU]; exact (by assumption : ld_6 &&& 2097152#32 = 0#32)
          refine wp_join_group (fun (b, _) ma => b = b ∧ ma = mb)
            (fun _ ⟨b, _⟩ ma ⟨_, hma⟩ => by
              subst hma
              exact reduce_collect_push_wp hstU hrmU hrrU (hrfU ▸ hp_mem) hp_lt32 hnrsn
                (fun rc' st' ml' h1' h2' h3' h4' hcore' _ _ ht1 ht2 =>
                  have hrf' : fullArenaClauseRefs st' = fullArenaClauseRefs st := by
                    simpa [fullArenaClauseRefs, fullArenaClauseRefsCore, hcore'] using hrfU
                  hJf (rc', ()) ml' (hJs rc' st' ml' h1' h2' h3' h4'
                    (by rw [hrf', hcore', h1]; exact hnxt) (by rw [hcore', h1])
                    (by rw [hcore', h2]) (by rw [hcore', h3]) (by rw [hcore', h4])
                    (ht1.trans h5) (ht2.trans h6)))
                hrc_le)
            (fun _ hJk => reduce_keep_bool_wp fun b => hJk (b, ()) mb ⟨rfl, rfl⟩)
        · exact hJf (rc, ()) mb (hJs rc stU mb hstU hrmU hrrU hrc_le
            (by rw [hrfU, h1]; exact hnxt) h1 h2 h3 h4 h5 h6))
      (fun _ hJ3 => by
        refine wp_m6Hdr_focus_frame hst.mem fun hmF => ?_
        c0_hsteps_ng
        · have hm' := fullM6HdrMem_unfocus_full (by assumption)
          obtain ⟨hstU, hrmU, hrfU, hrrU, hnhU⟩ :=
            redSt_update_used hst hrm hrr hp_mem hp_ar hm'
          exact hJ3 () _ ⟨_, hstU, hrmU, hrfU, hrrU, hnhU, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · have hnh : fullArenaHdr st pos.toNat &&& 2097152#32 = ld_6 &&& 2097152#32 := by
            simp [fullArenaHdr, fullArenaHdrCore, List.getElem?_eq_getElem hp_ar, ld_6]
          exact hJ3 () ml ⟨st, hst, hrm, rfl, hrr, hnh, rfl, rfl, rfl, rfl, rfl, rfl⟩)
  · exact hJn (rc, ()) ml (hJs rc st ml hst hrm hrr hrc_le hnxt rfl rfl rfl rfl rfl rfl)
  · exact hJn (rc, ()) ml (hJs rc st ml hst hrm hrr hrc_le hnxt rfl rfl rfl rfl rfl rfl)

theorem reduce_mark_garb_loop_wp {Γ : Env}
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml : Mem 64}
    {Js_exit : Cont []} {Q : Post [i64]} {X : XPost}
    {rc target : BitVec 64}
    (hst : RedSt c F0 F_cur s R ext st ml) (hrm : FullReasonsMarked st)
    (hrr : RedRefsOk st rc.toNat) (hrc_le : rc.toNat ≤ c.red_cap)
    (hEx : ∀ st' ml',
      RedSt c F0 F_cur s R ext st' ml' → FullReasonsMarked st' →
      st'.core.cur_level = st.core.cur_level → st'.core.oom = st.core.oom →
      st'.core.unflushed = st.core.unflushed → Js_exit () ml') :
    wp Γ Q X
      (Expr.group
        (fun Js_5 => Blocks.cons (fun (p_33 : Tup Val [i64]) =>
          Expr.let_ {
              sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64,
              args := (Arg.var p_33.fst, Arg.var target, ()) } fun p_34 =>
          Expr.jnz (Arg.var p_34.fst)
            (Expr.let_ {
                sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64,
                args := (Arg.var p_33.fst, Arg.var rc, ()) } fun p_35 =>
              Expr.jnz (Arg.var p_35.fst)
                (Expr.let_ {
                    sig := [i64, i64], code := OpCode.mul i64,
                    args := (Arg.var p_33.fst, Arg.imm 4, ()) } fun p_36 =>
                  Expr.let_ {
                      sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var c.pRedRefs, Arg.var p_36.fst, ()) } fun p_37 =>
                  Expr.load i32 (Arg.var p_37.fst) fun ld_6 =>
                  Expr.let_ {
                      sig := [i32], code := OpCode.zext 32 64,
                      args := (Arg.var ld_6, ()) } fun p_38 =>
                  Expr.let_ {
                      sig := [i64, i64], code := OpCode.mul i64,
                      args := (Arg.var p_38.fst, Arg.imm 4, ()) } fun p_39 =>
                  Expr.let_ {
                      sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var c.pArena, Arg.var p_39.fst, ()) } fun p_40 =>
                  Expr.load i32 (Arg.var p_40.fst) fun ld_7 =>
                  Expr.group (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
                      Expr.let_ {
                          sig := [i64, i64], code := OpCode.add i64,
                          args := (Arg.var p_33.fst, Arg.imm 1, ()) } fun p_n =>
                      Expr.jump Js_5.fst (Arg.var p_n.fst, ())) Blocks.nil)
                    fun Js_n =>
                    Expr.let_ {
                        sig := [i32, i32], code := OpCode.and i32,
                        args := (Arg.var ld_7, Arg.imm 524288, ()) } fun p_41 =>
                    Expr.let_ {
                        sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32,
                        args := (Arg.var p_41.fst, Arg.imm 0, ()) } fun p_42 =>
                    Expr.jnz (Arg.var p_42.fst)
                      (Expr.let_ {
                          sig := [i64, i64], code := OpCode.mul i64,
                          args := (Arg.var p_38.fst, Arg.imm 4, ()) } fun p_43 =>
                        Expr.let_ {
                            sig := [i64, i64], code := OpCode.add i64,
                            args := (Arg.var c.pArena, Arg.var p_43.fst, ()) } fun p_44 =>
                        Expr.let_ {
                            sig := [i32, i32], code := OpCode.or i32,
                            args := (Arg.var ld_7, Arg.imm 524288, ()) } fun p_45 =>
                        Expr.store (Arg.var p_45.fst) (Arg.var p_44.fst)
                          (Expr.let_ {
                              sig := [i64, i64], code := OpCode.add i64,
                              args := (Arg.var c.hdr, Arg.imm 472, ()) } fun p_46 =>
                            Expr.load i64 (Arg.var p_46.fst) fun ld_8 =>
                            Expr.let_ {
                                sig := [i64, i64], code := OpCode.add i64,
                                args := (Arg.var ld_8, Arg.imm 3, ()) } fun p_47 =>
                            Expr.let_ {
                                sig := [i64, i64], code := OpCode.add i64,
                                args := (Arg.var p_38.fst, Arg.imm 2, ()) } fun p_48 =>
                            Expr.let_ {
                                sig := [i64, i64], code := OpCode.mul i64,
                                args := (Arg.var p_48.fst, Arg.imm 4, ()) } fun p_49 =>
                            Expr.let_ {
                                sig := [i64, i64], code := OpCode.add i64,
                                args := (Arg.var c.pArena, Arg.var p_49.fst, ()) } fun p_50 =>
                            Expr.load i32 (Arg.var p_50.fst) fun ld =>
                            Expr.let_ {
                                sig := [i32], code := OpCode.zext 32 64,
                                args := (Arg.var ld, ()) } fun p_51 =>
                            Expr.let_ {
                                sig := [i64, i64], code := OpCode.add i64,
                                args := (Arg.var p_47.fst, Arg.var p_51.fst, ()) } fun p_52 =>
                            Expr.let_ {
                                sig := [i64, i64], code := OpCode.add i64,
                                args := (Arg.var c.hdr, Arg.imm 472, ()) } fun p_ag =>
                            Expr.store (Arg.var p_52.fst) (Arg.var p_ag.fst)
                              (Expr.jump Js_n.fst ())))
                      (Expr.jump Js_n.fst ()))
                (Expr.jump Js_exit ()))
            (Expr.jump Js_exit ())) Blocks.nil)
        (fun Js_5 => Expr.jump Js_5.fst (Arg.imm 0, ()))) ml := by
  let Inv : (BitVec 64 × FullState) → Mem 64 → Prop := fun (i, stI) mI =>
    i.toNat ≤ rc.toNat ∧ RedSt c F0 F_cur s R ext stI mI ∧ FullReasonsMarked stI ∧
    RedRefsOk stI rc.toNat ∧ stI.core.cur_level = st.core.cur_level ∧
    stI.core.oom = st.core.oom ∧ stI.core.unflushed = st.core.unflushed
  refine wp_while_state
    (fun (p : BitVec 64 × FullState) => (p.1, ()))
    (fun (p : BitVec 64 × FullState) => rc.toNat - p.1.toNat) Inv
    (fun J hJ => by
      c0_hsteps_ng
      exact hJ (0#64, st) ml ⟨Nat.zero_le _, hst, hrm, hrr, rfl, rfl, rfl⟩)
    (fun J (i, stI) mI ⟨hi_le, hstI, hrmI, hrrI, hclI, hoomI, hufI⟩ hL => by
      c0_hsteps_ng
      · have hi_lt : i.toNat < rc.toNat := by assumption
        have hspI := hstI.inv.toInv.sparse
        have hlenI := hspI.lengths
        unfold FullSparseInv at hspI
        obtain ⟨_, hwI⟩ := hspI.1.witness
        have hir_len : i.toNat < stI.scratch.red_refs.length := by
          rw [hlenI.scratch_ok.red_refs_len]; omega
        obtain ⟨hcr_mem, hcr_nrsn⟩ := hrrI i.toNat hi_lt
        have hcr_wf := hwI.arena.refs_wf _ hcr_mem
        have hal_le := hlenI.core_ok.arena_len_le
        have har_len := hlenI.core_ok.arena_len_arr
        have hcr_eq : (BitVec.zeroExtend 64
            (stI.scratch.red_refs[i.toNat]'hir_len)).toNat =
            (stI.scratch.red_refs[i.toNat]?.getD 0#32).toNat := by
          rw [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth,
            List.getElem?_eq_getElem hir_len, Option.getD_some,
            Nat.mod_eq_of_lt (by have := (stI.scratch.red_refs[i.toNat]'hir_len).isLt; omega)]
        have hidx_eq : (stI.scratch.red_refs[i.toNat]'hir_len).toNat =
            (stI.scratch.red_refs[i.toNat]?.getD 0#32).toNat := by
          simp [List.getElem?_eq_getElem hir_len]
        have hcr_sw : ∀ h : i.toNat < stI.scratch.red_refs.length,
            (BitVec.setWidth 64 (stI.scratch.red_refs[i.toNat]'h)).toNat =
            (stI.scratch.red_refs[i.toNat]?.getD 0#32).toNat := by
          intro h
          rw [BitVec.toNat_setWidth, List.getElem?_eq_getElem h, Option.getD_some,
            Nat.mod_eq_of_lt (by have := (stI.scratch.red_refs[i.toNat]'h).isLt; omega)]
        have hcr_ar : (stI.scratch.red_refs[i.toNat]?.getD 0#32).toNat < stI.core.arena.length := by
          omega
        have hcr_ar' : (stI.scratch.red_refs[i.toNat]'hir_len).toNat < stI.core.arena.length := by
          omega
        have hcr_ar2 : (stI.scratch.red_refs[i.toNat]'hir_len).toNat + 2 <
            stI.core.arena.length := by omega
        have hcr_64 : (stI.scratch.red_refs[i.toNat]'hir_len).toNat + 2 < 2 ^ 64 := by
          have := c.havail_fit; have := c.hsize; omega
        have hi64 : i.toNat + 1 < 2 ^ 64 := by
          have := c.havail_fit; have := c.hsize; omega
        refine wp_m6Hdr_focus_frame hstI.mem fun _hmF => ?_
        c0_hsteps_ng
        refine wp_join_group (fun (_ : Tup Val []) mb =>
            ∃ stN : FullState, RedSt c F0 F_cur s R ext stN mb ∧ FullReasonsMarked stN ∧
              RedRefsOk stN rc.toNat ∧ stN.core.cur_level = st.core.cur_level ∧
              stN.core.oom = st.core.oom ∧ stN.core.unflushed = st.core.unflushed)
          (fun _ _ mb ⟨stN, hstN, hrmN, hrrN, hclN, hoomN, hufN⟩ => by
            c0_hsteps_ng
            refine hL (i + 1#64, stN) mb
              (by dsimp only at *; rw [BitVec.toNat_add,
                show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt hi64]; omega)
              ⟨by rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl,
                Nat.mod_eq_of_lt hi64]; omega, hstN, hrmN, hrrN, hclN, hoomN, hufN⟩)
          (fun _ hJn => by
            c0_hsteps_ng
            · have hm' := fullM6HdrMem_unfocus_full (by assumption)
              simp only [hcr_sw] at hm'
              obtain ⟨hstN, hrmN, _, hrrN⟩ :=
                redSt_mark_garb hstI hrmI hrrI hcr_mem hcr_nrsn hcr_ar hm'
              exact hJn () _ ⟨_, hstN, hrmN, hrrN, hclI, hoomI, hufI⟩
            · exact hJn () mI ⟨stI, hstI, hrmI, hrrI, hclI, hoomI, hufI⟩)
      · exact hEx stI mI hstI hrmI hclI hoomI hufI
      · exact hEx stI mI hstI hrmI hclI hoomI hufI)

private theorem reduce_sweep_loop_wp {Γ : Env}
    (hSweep : Γ.Has "full_arena_sweep" Collect.Spec.step13ArenaSweepSpec)
    (hProp : Γ.Has "full_propagate" PropSearch.Spec.propagateM6Spec)
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml : Mem 64}
    {Js_ret : Cont [i64]} {Q : Post [i64]} {X : XPost} {r_unfl : BitVec 64}
    (hr_u : r_unfl = 1#64) (hst : RedSt c F0 F_cur s R ext st ml)
    (hrm : 0 < st.core.cur_level → FullReasonsMarked st)
    (hoom : s.core.oom = 0#64 → st.core.oom = 0#64)
    (hJs : ∀ r ext' st' ml',
      RedSt c F0 F_cur s R ext' st' ml' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → s.core.oom = 0#64 → st'.core.oom = 0#64) → Js_ret (r, ()) ml') :
    wp Γ Q X
      (Expr.group
        (fun _Js_4 => Blocks.cons (fun (p : Tup Val [i64]) =>
          Expr.jump Js_ret (Arg.var p.fst, ())) Blocks.nil)
        fun Js_ex =>
        Expr.group
          (fun Js_5 => Blocks.cons (fun (_ : Tup Val []) =>
            Expr.jnz (Arg.imm true)
              (Expr.call (as := [i64]) (bs := [i64]) "full_arena_sweep"
                (Arg.var c.hdr, ()) fun p_25 =>
                Expr.let_ {
                    sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64,
                    args := (Arg.var p_25.fst, Arg.imm 2, ()) } fun p_26 =>
                Expr.jnz (Arg.var p_26.fst) (Expr.jump Js_ex.fst (Arg.imm 20, ()))
                  (Expr.let_ {
                      sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64,
                      args := (Arg.var p_25.fst, Arg.imm 3, ()) } fun p_27 =>
                    Expr.jnz (Arg.var p_27.fst) (Expr.jump Js_ex.fst (Arg.imm 0, ()))
                      (Expr.let_ {
                          sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64,
                          args := (Arg.var p_25.fst, Arg.imm 0, ()) } fun p_28 =>
                        Expr.jnz (Arg.var p_28.fst) (Expr.jump Js_ex.fst (Arg.var r_unfl, ()))
                          (Expr.call (as := [i64]) (bs := [i64]) "full_propagate"
                            (Arg.var c.hdr, ()) fun p_29 =>
                            Expr.let_ {
                                sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64,
                                args := (Arg.var p_29.fst, Arg.imm 1, ()) } fun p_30 =>
                            Expr.jnz (Arg.var p_30.fst) (Expr.jump Js_ex.fst (Arg.imm 20, ()))
                              (Expr.let_ {
                                  sig := [i64, i64], code := OpCode.cmp CmpOp.ne i64,
                                  args := (Arg.var p_29.fst, Arg.imm 0, ()) } fun p_31 =>
                                Expr.jnz (Arg.var p_31.fst) (Expr.jump Js_ex.fst (Arg.imm 0, ()))
                                  (Expr.let_ {
                                      sig := [i64, i64], code := OpCode.add i64,
                                      args := (Arg.var c.hdr, Arg.imm 512, ()) } fun p_u =>
                                    Expr.store (Arg.imm (t := i64) 0) (Arg.var p_u.fst)
                                      (Expr.jump Js_5.fst ())))))))
              (Expr.jump Js_ex.fst (Arg.var r_unfl, ()))) Blocks.nil)
          (fun Js_5 => Expr.jump Js_5.fst ())) ml := by
  subst hr_u
  let Brk := BitVec 64 × List (BitVec 64) × FullState
  let St := List (BitVec 64) × FullState
  refine wp_while_break_state (brkTs := [i64]) (lpTs := [])
    (fun b : Brk => (b.1, ()))
    (fun b m' =>
      RedSt c F0 F_cur s R b.2.1 b.2.2 m' ∧
      (b.1 = 0#64 ∨ b.1 = 1#64 ∨ b.1 = 20#64) ∧ (b.1 = 20#64 → F0.Unsat) ∧
      (b.1 = 1#64 → s.core.oom = 0#64 → b.2.2.core.oom = 0#64))
    (fun _ : St => ())
    (fun stI => c.max_vars - stI.2.core.trail_end)
    (fun stI mI =>
      RedSt c F0 F_cur s R stI.1 stI.2 mI ∧ (0 < stI.2.core.cur_level → FullReasonsMarked stI.2) ∧
      (s.core.oom = 0#64 → stI.2.core.oom = 0#64))
    (fun _ b m' ⟨h1, h2, h3, h4⟩ => by
      c0_hsteps_ng; exact hJs b.1 b.2.1 b.2.2 m' h1 h2 h3 h4)
    (fun B L (extI, stI) mI hB hL ⟨hstI, hrmI, hoomI⟩ => by
      have h0_20 : (0#64 : BitVec 64) ≠ 20#64 := by decide
      have h0_1 : (0#64 : BitVec 64) ≠ 1#64 := by decide
      have h1_20 : (1#64 : BitVec 64) ≠ 20#64 := by decide
      have h20_1 : (20#64 : BitVec 64) ≠ 1#64 := by decide
      c0_hsteps_ng
      · refine red_call_sweep13 rfl hSweep hstI hrmI
          (fun sr sA mA hstA hsr hsoom _ hs1 hs2 => ?_)
        c0_hsteps_ng
        · exact hB (20#64, extI, sA) mA
            ⟨hstA, Or.inr (Or.inr rfl), fun _ => (hs2 (by assumption)).2,
              fun h => absurd h h20_1⟩
        · exact hB (0#64, extI, sA) mA
            ⟨hstA, Or.inl rfl, fun h => absurd h h0_20, fun h => absurd h h0_1⟩
        · exact hB (1#64, extI, sA) mA
            ⟨hstA, Or.inr (Or.inl rfl), fun h => absurd h h1_20,
              fun _ _ => hsoom (Or.inl (by assumption))⟩
        · have hsr1 : sr = 1#64 := by
            rcases hsr with rfl | rfl | rfl | rfl
            · exact False.elim ((by assumption : ¬(0#64 : BitVec 64) = 0#64) rfl)
            · rfl
            · exact False.elim ((by assumption : ¬(2#64 : BitVec 64) = 2#64) rfl)
            · exact False.elim ((by assumption : ¬(3#64 : BitVec 64) = 3#64) rfl)
          have ⟨hclA, hteA⟩ := hs1 hsr1
          refine red_call_propagate0 rfl hProp hstA hclA
            (fun rp extP sP mP hstP hclP hteP hrp hoomP hunsP => ?_)
          c0_hsteps_ng
          · exact hB (20#64, extP, sP) mP
              ⟨hstP, Or.inr (Or.inr rfl), fun _ => hunsP (by assumption),
                fun h => absurd h h20_1⟩
          · exact hB (0#64, extP, sP) mP
              ⟨hstP, Or.inl rfl, fun h => absurd h h0_20, fun h => absurd h h0_1⟩
          · have hrp0 : rp = 0#64 := by
              rcases hrp with rfl | rfl | rfl
              · rfl
              · exact False.elim ((by assumption : ¬(1#64 : BitVec 64) = 1#64) rfl)
              · exact False.elim (by cases (by assumption : (2#64 : BitVec 64) = 0#64))
            have hlenP := hstP.inv.toInv.sparse.lengths
            refine wp_m6Hdr_focus_frame hstP.mem fun _hmF => ?_
            c0_hsteps_ng
            have hst0 := redSt_with_unflushed hstP 0#64
              (fullM6HdrMem_unfocus_full (by assumption))
            have hte_leP : sP.core.trail_end ≤ c.max_vars := by
              have := hlenP.core_ok.trail_end_le; have := hlenP.core_ok.cur_vars_le; omega
            have hmeas : c.max_vars - sP.core.trail_end < c.max_vars - stI.core.trail_end := by
              dsimp only at hteA; omega
            exact hL (extP, _) _ (by simpa using hmeas)
              ⟨hst0, fun h => by simp [hclP] at h,
                fun _ => hoomP hrp0 (hsoom (Or.inr hsr1))⟩
      · exact False.elim (Bool.noConfusion (by assumption : true = false)))
    (fun _ L _ hL => by c0_hsteps_ng; exact hL (ext, st) ml ⟨hst, hrm, hoom⟩)

theorem reduce_sweep_tail_wp {Γ : Env}
    (hSweep : Γ.Has "full_arena_sweep" Collect.Spec.step13ArenaSweepSpec)
    (hProp : Γ.Has "full_propagate" PropSearch.Spec.propagateM6Spec)
    (hMrk : Γ.Has "full_mark_reasons" fullMarkReasonsSpec)
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {F_cur : List (List Nat)}
    {s st : FullState} {R : Mem 64 → Prop} {ext : List (BitVec 64)} {ml : Mem 64}
    {Js_ret : Cont [i64]} {Q : Post [i64]} {X : XPost}
    {force do_compact : Bool} {r_unfl : BitVec 64}
    (hr_u : r_unfl = 1#64) (hst : RedSt c F0 F_cur s R ext st ml)
    (hrm : 0 < st.core.cur_level → FullReasonsMarked st)
    (hoom : s.core.oom = 0#64 → st.core.oom = 0#64)
    (hJs : ∀ r ext' st' ml',
      RedSt c F0 F_cur s R ext' st' ml' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → s.core.oom = 0#64 → st'.core.oom = 0#64) → Js_ret (r, ()) ml') :
    wp Γ Q X
      (Expr.group
        (fun _Js_4 => Blocks.cons (fun (_ : Tup Val []) =>
          Expr.group (fun _Js_x => Blocks.cons (fun (p : Tup Val [i64]) =>
              Expr.jump Js_ret (Arg.var p.fst, ())) Blocks.nil)
            fun Js_ex =>
            Expr.group
              (fun Js_5 => Blocks.cons (fun (_ : Tup Val []) =>
                Expr.jnz (Arg.imm true)
                  (Expr.call (as := [i64]) (bs := [i64]) "full_arena_sweep"
                    (Arg.var c.hdr, ()) fun p_25 =>
                    Expr.let_ {
                        sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64,
                        args := (Arg.var p_25.fst, Arg.imm 2, ()) } fun p_26 =>
                    Expr.jnz (Arg.var p_26.fst) (Expr.jump Js_ex.fst (Arg.imm 20, ()))
                      (Expr.let_ {
                          sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64,
                          args := (Arg.var p_25.fst, Arg.imm 3, ()) } fun p_27 =>
                        Expr.jnz (Arg.var p_27.fst) (Expr.jump Js_ex.fst (Arg.imm 0, ()))
                          (Expr.let_ {
                              sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64,
                              args := (Arg.var p_25.fst, Arg.imm 0, ()) } fun p_28 =>
                            Expr.jnz (Arg.var p_28.fst) (Expr.jump Js_ex.fst (Arg.var r_unfl, ()))
                              (Expr.call (as := [i64]) (bs := [i64]) "full_propagate"
                                (Arg.var c.hdr, ()) fun p_29 =>
                                Expr.let_ {
                                    sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64,
                                    args := (Arg.var p_29.fst, Arg.imm 1, ()) } fun p_30 =>
                                Expr.jnz (Arg.var p_30.fst) (Expr.jump Js_ex.fst (Arg.imm 20, ()))
                                  (Expr.let_ {
                                      sig := [i64, i64], code := OpCode.cmp CmpOp.ne i64,
                                      args := (Arg.var p_29.fst, Arg.imm 0, ()) } fun p_31 =>
                                    Expr.jnz (Arg.var p_31.fst)
                                      (Expr.jump Js_ex.fst (Arg.imm 0, ()))
                                      (Expr.let_ {
                                          sig := [i64, i64], code := OpCode.add i64,
                                          args := (Arg.var c.hdr, Arg.imm 512, ()) } fun p_u =>
                                        Expr.store (Arg.imm (t := i64) 0) (Arg.var p_u.fst)
                                          (Expr.jump Js_5.fst ())))))))
                  (Expr.jump Js_ex.fst (Arg.var r_unfl, ()))) Blocks.nil)
              (fun Js_5 => Expr.jump Js_5.fst ())) Blocks.nil)
        (fun Js_4 =>
          Expr.jnz (Arg.var force) (Expr.jump Js_4.fst ())
            (Expr.jnz (Arg.var do_compact) (Expr.jump Js_4.fst ())
              (Expr.group (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
                  Expr.call (as := [i64, .bool]) (bs := []) "full_mark_reasons"
                    (Arg.var c.hdr, Arg.imm false, ()) fun _ =>
                    Expr.jump Js_ret (Arg.var r_unfl, ())) Blocks.nil)
                fun Js_el =>
                Expr.let_ {
                    sig := [i64, i64], code := OpCode.add i64,
                    args := (Arg.var c.hdr, Arg.imm 512, ()) } fun p_23 =>
                Expr.load i64 (Arg.var p_23.fst) fun ld =>
                Expr.let_ {
                    sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64,
                    args := (Arg.var ld, Arg.imm 0, ()) } fun p_24 =>
                Expr.jnz (Arg.var p_24.fst)
                  (Expr.let_ {
                      sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var c.hdr, Arg.imm 472, ()) } fun p_25 =>
                    Expr.load i64 (Arg.var p_25.fst) fun ld =>
                    Expr.let_ {
                        sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64,
                        args := (Arg.var ld, Arg.imm 0, ()) } fun p_26 =>
                    Expr.jnz (Arg.var p_26.fst) (Expr.jump Js_4.fst ())
                      (Expr.let_ {
                          sig := [i64, i64], code := OpCode.add i64,
                          args := (Arg.var c.hdr, Arg.imm 160, ()) } fun p_cl =>
                        Expr.load i64 (Arg.var p_cl.fst) fun ld =>
                        Expr.let_ {
                            sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64,
                            args := (Arg.var ld, Arg.imm 0, ()) } fun p_cl0 =>
                        Expr.jnz (Arg.var p_cl0.fst) (Expr.jump Js_4.fst ())
                          (Expr.jump Js_el.fst ())))
                  (Expr.jump Js_el.fst ()))))) ml := by
  refine wp_join_group (fun (_ : Tup Val []) mb => mb = ml)
    (fun _ _ mb hmb => by
      subst hmb
      exact reduce_sweep_loop_wp hSweep hProp hr_u hst hrm hoom hJs)
    (fun _ hJ4 => by
      c0_hsteps_ng
      · exact hJ4 () ml rfl
      · exact hJ4 () ml rfl
      · refine wp_join_group (fun (_ : Tup Val []) mb => mb = ml)
          (fun _ _ mb hmb => by
            subst hmb
            refine red_call_mark_reasons rfl hMrk hst fun s' m' hst' _ hoom' => ?_
            c0_hsteps_ng
            subst hr_u
            exact hJs 1#64 ext s' m' hst' (Or.inr (Or.inl rfl)) (fun h => by cases h)
              (fun _ hs => by rw [hoom']; exact hoom hs))
          (fun _ hJel => by
            have hlen := hst.inv.toInv.sparse.lengths
            refine wp_m6Hdr_focus_frame hst.mem fun _hmF => ?_
            c0_hsteps_ng
            · exact hJ4 () ml rfl
            · exact hJ4 () ml rfl
            · exact hJel () ml rfl
            · exact hJel () ml rfl))

end LeanQbe.T.Examples.Kissat.Proof.Reduce
