module

public import LeanQbe.T.Examples.Bitblast.Proof.OpsDivCpopHelpers
public import LeanQbe.T.Examples.Bitblast.Proof.OpsDivCpop1Helpers
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.ProofKit

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Proof.OpsDivCpop

open LeanQbe.T
open LeanQbe.T.Examples.Bitblast.Src.OpsDivCpop
open LeanQbe.T.Examples.Bitblast.Ref

/-!
## Division and Remainder Operator Correctness (`OpsDivCpop1`)

Proves `Func.wp` theorems for `bv_blast_udiv_umod`, `bv_blast_udiv`, and `bv_blast_umod`
against `bvBlastUdivUmodSpec`, `bvBlastUdivSpec`, and `bvBlastUmodSpec`.
-/

private abbrev udivFinishExpr (h : Val i64)
    (n_off w mark0 mark1 out_off q_off r_off rp_off want_rem d_is_zero
      dum_in : Val i32) (ld : Val i64) : Expr Val Cont [i32] :=
  Expr.group
    (fun Js => Blocks.cons
      (fun _ : Tup Val [i32] =>
        Expr.call (as := [i64, i32]) (bs := []) "bv_lits_release"
          (Arg.var h, Arg.var mark1, ()) fun _ =>
          Expr.ret (Arg.var out_off, ()))
      Blocks.nil)
    (fun Js =>
      Expr.let_ (op2 (OpCode.cmp CmpOp.ne i32 Ty.bool (by decide))
        (Arg.var want_rem) (Arg.imm 0#32)) fun p_31 =>
      Expr.jnz (Arg.var p_31.fst)
        (Expr.call (as := [i64, i32, i32, i32, i32, i32]) (bs := [Ty.bool]) "bv_blast_ite_into"
          (Arg.var h, Arg.var d_is_zero, Arg.var n_off, Arg.var r_off,
            Arg.var out_off, Arg.var w, ()) fun p_32 =>
          Expr.jnz (Arg.var p_32.fst)
            (Expr.jump Js.fst (Arg.var dum_in, ()))
            (udivRelRetExpr h mark0))
        (udivZeroRprimeExpr w rp_off ld fun p_32 =>
          Expr.call (as := [i64, i32, i32, i32, i32, i32]) (bs := [Ty.bool]) "bv_blast_ite_into"
            (Arg.var h, Arg.var d_is_zero, Arg.var rp_off, Arg.var q_off,
              Arg.var out_off, Arg.var w, ()) fun p_34 =>
            Expr.jnz (Arg.var p_34.fst)
              (Expr.jump Js.fst (Arg.var p_32.fst, ()))
              (udivRelRetExpr h mark0)))

private theorem bv_udiv_oom_ret_q
    {h : Val i64} {n_off d_off w want_rem : BitVec 32}
    {hdr0 hdrF : BVHdrState} {g0 gF : Aig}
    {awF : List (BitVec 64)} {htF lp0 lpF : List (BitVec 32)}
    {R : Mem 64 → Prop} {mF : Mem 64}
    {Q : Post [i32]}
    (hQ : ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Aig)
      (aw' : List (BitVec 64)) (ht' lp' : List (BitVec 32)) (m' : Mem 64),
      hdr0.DcBlastFrame hdr' → g0 ≤ g' →
      g'.nodes.size ≤ g0.nodes.size + (7 * w.toNat + 12 * w.toNat * w.toNat) →
      AigInv hdr' g' aw' ht' → lp'.length = lp0.length →
      (∀ p, p < hdr0.lits_len.toNat → lp'.getD p 0#32 = lp0.getD p 0#32) →
      (hdr0.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
      (hdr0.oom = 0#32 → hdr0.lits_len.toNat ≤ hdr0.lits_cap.toNat →
        (0 < w.toNat → hdr0.lits_ptr ≠ 0#64) →
        n_off.toNat + w.toNat ≤ hdr0.lits_len.toNat →
        d_off.toNat + w.toNat ≤ hdr0.lits_len.toNat →
        5 * w.toNat ≤ hdr0.lits_cap.toNat - hdr0.lits_len.toNat →
        g0.A + 1 + g0.nodes.size + (7 * w.toNat + 12 * w.toNat * w.toNat) ≤ hdr0.aig_cap.toNat →
        g0.nodes.size + (7 * w.toNat + 12 * w.toNat * w.toNat) ≤ bvMaxGates → hdr'.oom = 0#32) →
      (hdr'.oom ≠ 0#32 → ret = 0xFFFFFFFF#32 ∧ hdr'.lits_len = hdr0.lits_len) →
      (hdr'.oom = 0#32 → ret = hdr0.lits_len ∧ hdr'.lits_len = hdr0.lits_len + w ∧
        hdr'.lits_len.toNat ≤ hdr'.lits_cap.toNat ∧ SliceLitsWf hdr' lp' ret.toNat w.toNat ∧
        ∀ ρ, sliceVal g' ρ lp' ret.toNat w.toNat =
          if want_rem ≠ 0#32 then
            sliceVal g0 ρ lp0 n_off.toNat w.toNat % sliceVal g0 ρ lp0 d_off.toNat w.toNat
          else
            sliceVal g0 ρ lp0 n_off.toNat w.toNat / sliceVal g0 ρ lp0 d_off.toNat w.toNat) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aw' ⋆
        array (t := i32) hdr'.ht_ptr ht' ⋆ array (t := i32) hdr'.lits_ptr lp' ⋆ R) m' →
      Q (ret, ()) m')
    (hf : hdr0.DcBlastFrame hdrF) (hle : g0 ≤ gF)
    (hnd : gF.nodes.size ≤ g0.nodes.size + (7 * w.toNat + 12 * w.toNat * w.toNat))
    (hinv : AigInv hdrF gF awF htF) (hlen : lpF.length = lp0.length)
    (hpres : ∀ p, p < hdr0.lits_len.toNat → lpF.getD p 0#32 = lp0.getD p 0#32)
    (hoom : hdrF.oom ≠ 0#32) (hlenc : hdrF.lits_len = hdr0.lits_len)
    (hnob : hdr0.oom = 0#32 → hdr0.lits_len.toNat ≤ hdr0.lits_cap.toNat →
      (0 < w.toNat → hdr0.lits_ptr ≠ 0#64) →
      n_off.toNat + w.toNat ≤ hdr0.lits_len.toNat →
      d_off.toNat + w.toNat ≤ hdr0.lits_len.toNat →
      5 * w.toNat ≤ hdr0.lits_cap.toNat - hdr0.lits_len.toNat →
      g0.A + 1 + g0.nodes.size + (7 * w.toNat + 12 * w.toNat * w.toNat) ≤ hdr0.aig_cap.toNat →
      g0.nodes.size + (7 * w.toNat + 12 * w.toNat * w.toNat) ≤ bvMaxGates → False)
    (hmem : (bvHdrMem h hdrF ⋆ array64 hdrF.aig_ptr awF ⋆
      array (t := i32) hdrF.ht_ptr htF ⋆ array (t := i32) hdrF.lits_ptr lpF ⋆ R) mF) :
    Q (0xFFFFFFFF#32, ()) mF :=
  hQ 0xFFFFFFFF#32 hdrF gF awF htF lpF mF hf hle hnd hinv hlen hpres
    (fun _ => hoom)
    (fun h0 h1 h2 h3 h4 h5 h6 h7 => False.elim (hnob h0 h1 h2 h3 h4 h5 h6 h7))
    (fun _ => ⟨rfl, hlenc⟩) (fun hz => False.elim (hoom hz)) hmem

private theorem udiv_hdr0_oom_frame (hdr0 : BVHdrState) :
    hdr0.DcBlastFrame { hdr0 with oom := 1#32 } :=
  { work_base := rfl, work_end := rfl, prog_ptr := rfl, aig_ptr := rfl, ht_ptr := rfl,
    atom_base_ptr := rfl, slice_off_ptr := rfl, lits_ptr := rfl, marks_ptr := rfl,
    dimacs_start := rfl, n_vars := rfl, n_nodes := rfl, n_cwords := rfl, root_node := rfl,
    num_atoms := rfl, aig_cap := rfl, ht_mask := rfl, lits_cap := rfl, dimacs_len := rfl }

private theorem bv_udiv_finish_wp (Γ : Env)
    (hite : Γ.Has "bv_blast_ite_into" bvBlastIteIntoSpec)
    (hrel : Γ.Has "bv_lits_release" bvLitsReleaseSpec)
    {h : Val i64} {n_off d_off w mark0 mark1 out_off q_off r_off rp_off diff_off : BitVec 32}
    {want_rem d_is_zero dum_in : BitVec 32} {ld : Val i64}
    {hdr0 hdrInit hdrW : BVHdrState} {g0 gInit gW : Aig}
    {awW : List (BitVec 64)} {htW lp0 lpW : List (BitVec 32)}
    {R : Mem 64 → Prop} {mW : Mem 64} {Q : Post [i32]} {X : XPost}
    (hoom0 : hdr0.oom = 0#32) (hw : 0 < w.toNat)
    (hframe0 : hdr0.DcBlastFrame hdrInit) (hframeW : hdrInit.DcBlastFrame hdrW)
    (hle0 : g0 ≤ gInit) (hleW : gInit ≤ gW)
    (hnodes0 : gInit.nodes.size ≤ g0.nodes.size + 4 * w.toNat)
    (hnodesW : gW.nodes.size ≤ gInit.nodes.size + w.toNat * (12 * w.toNat))
    (hinvW : AigInv hdrW gW awW htW) (hld : ld = hdrW.lits_ptr)
    (hoomW : hdrW.oom = 0#32) (hlencapW : hdrW.lits_len.toNat ≤ hdrW.lits_cap.toNat)
    (hcaplenW : hdrW.lits_cap.toNat ≤ lpW.length) (hptrW : hdrW.lits_ptr ≠ 0#64)
    (hmark0 : mark0 = hdr0.lits_len) (hmark1 : mark1 = out_off + w)
    (hout : out_off = hdr0.lits_len)
    (hq_eq : q_off.toNat = out_off.toNat + w.toNat)
    (hr_eq : r_off.toNat = q_off.toNat + w.toNat)
    (hrp_eq : rp_off.toNat = r_off.toNat + w.toNat)
    (hdiff_eq : diff_off.toNat = rp_off.toNat + w.toNat)
    (hlen5 : diff_off.toNat + w.toNat = hdrInit.lits_len.toNat)
    (hlenW : hdrW.lits_len = hdrInit.lits_len)
    (hlen_lp : lpW.length = lp0.length)
    (hpres0 : ∀ p, p < hdr0.lits_len.toNat → lpW.getD p 0#32 = lp0.getD p 0#32)
    (hn : n_off.toNat + w.toNat ≤ hdr0.lits_len.toNat)
    (hwfn : SliceLitsWf hdrW lpW n_off.toNat w.toNat)
    (hwfq : SliceLitsWf hdrW lpW q_off.toNat w.toNat)
    (hwfr : SliceLitsWf hdrW lpW r_off.toNat w.toNat)
    (hd0_lt : (d_is_zero >>> 1).toNat < hdrW.aig_len.toNat)
    (hd0_val : ∀ ρ, gW.evalLit ρ (UInt32.ofBitVec d_is_zero) =
      decide (sliceVal g0 ρ lp0 d_off.toNat w.toNat = 0#w.toNat))
    (hdiv_val : ∀ ρ,
      let out := BitVec.divRec w.toNat
        { n := sliceVal g0 ρ lp0 n_off.toNat w.toNat,
          d := sliceVal g0 ρ lp0 d_off.toNat w.toNat }
        (BitVec.DivModState.init w.toNat)
      sliceVal gW ρ lpW q_off.toNat w.toNat = out.q ∧
      sliceVal gW ρ lpW r_off.toNat w.toNat = out.r)
    (hagree_n : ∀ ρ, sliceVal gW ρ lpW n_off.toNat w.toNat =
      sliceVal g0 ρ lp0 n_off.toNat w.toNat)
    (hmem : (bvHdrMem h hdrW ⋆ array64 hdrW.aig_ptr awW ⋆
      array (t := i32) hdrW.ht_ptr htW ⋆ array (t := i32) hdrW.lits_ptr lpW ⋆ R) mW)
    (hQ : ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Aig)
      (aw' : List (BitVec 64)) (ht' lp' : List (BitVec 32)) (m' : Mem 64),
      hdr0.DcBlastFrame hdr' → g0 ≤ g' →
      g'.nodes.size ≤ g0.nodes.size + (7 * w.toNat + 12 * w.toNat * w.toNat) →
      AigInv hdr' g' aw' ht' → lp'.length = lp0.length →
      (∀ p, p < hdr0.lits_len.toNat → lp'.getD p 0#32 = lp0.getD p 0#32) →
      (hdr0.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
      (hdr0.oom = 0#32 → hdr0.lits_len.toNat ≤ hdr0.lits_cap.toNat →
        (0 < w.toNat → hdr0.lits_ptr ≠ 0#64) →
        n_off.toNat + w.toNat ≤ hdr0.lits_len.toNat →
        d_off.toNat + w.toNat ≤ hdr0.lits_len.toNat →
        5 * w.toNat ≤ hdr0.lits_cap.toNat - hdr0.lits_len.toNat →
        g0.A + 1 + g0.nodes.size + (7 * w.toNat + 12 * w.toNat * w.toNat) ≤ hdr0.aig_cap.toNat →
        g0.nodes.size + (7 * w.toNat + 12 * w.toNat * w.toNat) ≤ bvMaxGates → hdr'.oom = 0#32) →
      (hdr'.oom ≠ 0#32 → ret = 0xFFFFFFFF#32 ∧ hdr'.lits_len = hdr0.lits_len) →
      (hdr'.oom = 0#32 → ret = hdr0.lits_len ∧ hdr'.lits_len = hdr0.lits_len + w ∧
        hdr'.lits_len.toNat ≤ hdr'.lits_cap.toNat ∧ SliceLitsWf hdr' lp' ret.toNat w.toNat ∧
        ∀ ρ, sliceVal g' ρ lp' ret.toNat w.toNat =
          if want_rem ≠ 0#32 then
            sliceVal g0 ρ lp0 n_off.toNat w.toNat % sliceVal g0 ρ lp0 d_off.toNat w.toNat
          else
            sliceVal g0 ρ lp0 n_off.toNat w.toNat / sliceVal g0 ρ lp0 d_off.toNat w.toNat) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aw' ⋆
        array (t := i32) hdr'.ht_ptr ht' ⋆ array (t := i32) hdr'.lits_ptr lp' ⋆ R) m' →
      Q (ret, ()) m') :
    wp Γ Q X (udivFinishExpr h n_off w mark0 mark1 out_off q_off r_off rp_off
      want_rem d_is_zero dum_in ld) mW := by
  have hout_nat : out_off.toNat = hdr0.lits_len.toNat := congrArg BitVec.toNat hout
  have hcap32 : hdrW.lits_cap.toNat < 2 ^ 32 := hdrW.lits_cap.isLt
  have hframe0W : hdr0.DcBlastFrame hdrW := hframe0.trans hframeW
  have hle0W : g0 ≤ gW := Aig.extends_trans hle0 hleW
  have hmulW : w.toNat * (12 * w.toNat) = 12 * w.toNat * w.toNat := by
    rw [Nat.mul_comm w.toNat (12 * w.toNat), Nat.mul_assoc]
  let InvSucc : BitVec 32 → Mem 64 → Prop := fun _ ml =>
    ∃ (hdr' : BVHdrState) (g' : Aig) (aw' : List (BitVec 64)) (ht' lp' : List (BitVec 32)),
      hdr0.DcBlastFrame hdr' ∧ g0 ≤ g' ∧
      g'.nodes.size ≤ g0.nodes.size + (7 * w.toNat + 12 * w.toNat * w.toNat) ∧
      AigInv hdr' g' aw' ht' ∧ hdr'.oom = 0#32 ∧ hdr'.lits_len = hdrW.lits_len ∧
      lp'.length = lp0.length ∧
      (∀ p, p < hdr0.lits_len.toNat → lp'.getD p 0#32 = lp0.getD p 0#32) ∧
      SliceLitsWf hdr' lp' out_off.toNat w.toNat ∧
      (∀ ρ, sliceVal g' ρ lp' out_off.toNat w.toNat =
        if want_rem ≠ 0#32 then
          sliceVal g0 ρ lp0 n_off.toNat w.toNat % sliceVal g0 ρ lp0 d_off.toNat w.toNat
        else
          sliceVal g0 ρ lp0 n_off.toNat w.toNat / sliceVal g0 ρ lp0 d_off.toNat w.toNat) ∧
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aw' ⋆
        array (t := i32) hdr'.ht_ptr ht' ⋆ array (t := i32) hdr'.lits_ptr lp' ⋆ R) ml
  dsimp only [udivFinishExpr]
  apply wp_join_state1 (fun st : BitVec 32 => st) InvSucc
  · intro J st m' ⟨hdr', g', aw', ht', lp', hf', hle', hnd', hinv', hoom', hlen', hlp',
      hpres', hwf', hval', hm'⟩
    c0_hcall hrel
    refine ⟨hdr', _, opMem_to_hdr hm', ?_⟩
    have hm1_nat : mark1.toNat = out_off.toNat + w.toNat := by
      rw [hmark1, BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have hm1_le : mark1.toNat ≤ hdr'.lits_len.toNat := by
      rw [hlen', hlenW]; omega
    simp only [hm1_le, ↓reduceIte]
    intro m'' hm''
    have hm''_full := opMem_of_hdr hm''
    have hf_m1 := blastFrame_with_lits_len hdr' mark1
    have hm1_eq : mark1 = hdr0.lits_len + w := by rw [hmark1, hout]
    have hlencap_m1 : ({ hdr' with lits_len := mark1 } : BVHdrState).lits_len.toNat ≤
        ({ hdr' with lits_len := mark1 } : BVHdrState).lits_cap.toNat := by
      have hlen_lt : mark1.toNat ≤ hdrW.lits_len.toNat :=
        Nat.le_trans hm1_le (Nat.le_of_eq (congrArg BitVec.toNat hlen'))
      have hcap_eq : hdr'.lits_cap = hdrW.lits_cap := by
        have h1 := hf'.lits_cap; have h2 := hframe0W.lits_cap; rw [h1, ← h2]
      dsimp only; rw [hcap_eq]; exact Nat.le_trans hlen_lt hlencapW
    c0_hfast_nogrp
    refine hQ out_off { hdr' with lits_len := mark1 } g' aw' ht' lp' m''
      (hf'.trans hf_m1) hle' hnd' (aigInv_blastFrame hinv' hf_m1 rfl) hlp' hpres'
      (fun hne0 => False.elim (hne0 hoom0))
      (fun _ _ _ _ _ _ _ _ => hoom')
      (fun hne => False.elim (hne hoom'))
      (fun _ => ⟨hout, hm1_eq, hlencap_m1, ⟨by dsimp only; omega, hwf'.2⟩, hval'⟩) hm''_full
  · intro J hJ
    c0_hfast_nogrp
    · by_cases hrem : want_rem ≠ 0#32
      · c0_hcall hite
        refine ⟨hdrW, gW, awW, htW, lpW, R, hinvW, hcaplenW, ?_, hmem, ?_⟩
        · intro _ _ _ _ _ _
          exact ⟨fun _ => hd0_lt, hwfn, hwfr,
            by unfold DisjointSlice; omega, by unfold DisjointSlice; omega⟩
        · intro ite_ok hdrF gF awF htF lpF mF hfF hleF hnodesF hinvF hlenF hpresF _
            hoomF_iff hboundF hite_valF hmemF
          have hframe0F : hdr0.DcBlastFrame hdrF := hframe0W.trans hfF.toDcBlastFrame
          have hle0F : g0 ≤ gF := Aig.extends_trans hle0W hleF
          have hlenF_0 : lpF.length = lp0.length := hlenF.trans hlen_lp
          have hpresF_0 : ∀ p, p < hdr0.lits_len.toNat → lpF.getD p 0#32 = lp0.getD p 0#32 :=
            fun p hp => by rw [hpresF p (Or.inl (by omega)), hpres0 p hp]
          by_cases hokF : ite_ok = true
          · simp only [hokF]
            have hoomF : hdrF.oom = 0#32 := hoomF_iff.mp hokF
            obtain ⟨hwf_outF, hout_valF⟩ := hite_valF hokF
            c0_hfast_nogrp <;> first | contradiction | skip
            apply hJ dum_in mF ⟨hdrF, gF, awF, htF, lpF, hframe0F, hle0F, by omega, hinvF,
              hoomF, hfF.lits_len, hlenF_0, hpresF_0, hwf_outF, ?_, hmemF⟩
            intro ρ
            simp only [hrem, ne_eq, not_false_eq_true, ↓reduceIte]
            rw [hout_valF ρ, hd0_val ρ, hagree_n ρ, (hdiv_val ρ).2, umod_eq_of_divRec]
            simp only [decide_eq_true_eq]
          · simp only [hokF]
            have hoomF : hdrF.oom ≠ 0#32 := fun h0 => hokF (hoomF_iff.mpr h0)
            c0_hfast_nogrp <;> first | contradiction | skip
            apply bv_udiv_rel_ret_wp Γ hrel (by rw [hfF.lits_len, hlenW, hmark0]; omega) hmemF
            intro mR hmR
            have hfR := blastFrame_with_lits_len hdrF mark0
            refine bv_udiv_oom_ret_q (n_off := n_off) (d_off := d_off) (w := w)
              (want_rem := want_rem) hQ (hframe0F.trans hfR) hle0F (by omega)
              (aigInv_blastFrame hinvF hfR rfl) hlenF_0 hpresF_0 hoomF hmark0 ?_ hmR
            intro h0 hlencap0 hptr0 _ _ _ hcap0 hmax0
            have hA_eq : g0.A = gW.A := hle0W.1
            have haigc : hdrW.aig_cap = hdr0.aig_cap := hframe0W.aig_cap
            exact hoomF (hboundF hoomW hlencapW (fun _ => hptrW)
              (by rw [hlenW]; omega) (by rw [hlenW]; omega) (by rw [hlenW]; omega)
              (by rw [← hA_eq, haigc]; omega) (by omega))
      · exfalso; apply hrem; bv_omega
    · by_cases hrem : want_rem = 0#32
      · apply bv_udiv_zero_rprime_wp Γ hinvW hld (by rw [hlenW]; omega) hlencapW hcaplenW hmem
        intro dum_z lpZ mZ _ hlenZ hpresZ hwf_rpZ hrpz_val hmZ
        have hlenZ_0 : lpZ.length = lp0.length := hlenZ.trans hlen_lp
        have hpresZ_0 : ∀ p, p < q_off.toNat → lpZ.getD p 0#32 = lpW.getD p 0#32 :=
          fun p hp => hpresZ p (by omega)
        have hpresZ_0' : ∀ p, p < hdr0.lits_len.toNat → lpZ.getD p 0#32 = lp0.getD p 0#32 :=
          fun p hp => by rw [hpresZ_0 p (by omega), hpres0 p hp]
        have hwf_qZ : SliceLitsWf hdrW lpZ q_off.toNat w.toNat :=
          sliceLitsWf_of_agree (fun p hp1 hp2 => hpresZ p (by omega)) hwfq
        c0_hcall hite
        refine ⟨hdrW, gW, awW, htW, lpZ, R, hinvW, by rw [hlenZ]; exact hcaplenW,
          ?_, hmZ, ?_⟩
        · intro _ _ _ _ _ _
          exact ⟨fun _ => hd0_lt, hwf_rpZ, hwf_qZ,
            by unfold DisjointSlice; omega, by unfold DisjointSlice; omega⟩
        · intro ite_ok hdrF gF awF htF lpF mF hfF hleF hnodesF hinvF hlenF hpresF _
            hoomF_iff hboundF hite_valF hmemF
          have hframe0F : hdr0.DcBlastFrame hdrF := hframe0W.trans hfF.toDcBlastFrame
          have hle0F : g0 ≤ gF := Aig.extends_trans hle0W hleF
          have hlenF_0 : lpF.length = lp0.length := hlenF.trans hlenZ_0
          have hpresF_0 : ∀ p, p < hdr0.lits_len.toNat → lpF.getD p 0#32 = lp0.getD p 0#32 :=
            fun p hp => by rw [hpresF p (Or.inl (by omega)), hpresZ_0' p hp]
          by_cases hokF : ite_ok = true
          · simp only [hokF]
            have hoomF : hdrF.oom = 0#32 := hoomF_iff.mp hokF
            obtain ⟨hwf_outF, hout_valF⟩ := hite_valF hokF
            c0_hfast_nogrp <;> first | contradiction | skip
            apply hJ dum_z mF ⟨hdrF, gF, awF, htF, lpF, hframe0F, hle0F, by omega, hinvF,
              hoomF, hfF.lits_len, hlenF_0, hpresF_0, hwf_outF, ?_, hmemF⟩
            intro ρ
            simp only [hrem, ne_eq, not_true_eq_false, ↓reduceIte]
            have hqZ_val : sliceVal gW ρ lpZ q_off.toNat w.toNat =
                (BitVec.divRec w.toNat
                  { n := sliceVal g0 ρ lp0 n_off.toNat w.toNat,
                    d := sliceVal g0 ρ lp0 d_off.toNat w.toNat }
                  (BitVec.DivModState.init w.toNat)).q := by
              rw [sliceVal_eq_of_agree (fun p hp1 hp2 => hpresZ p (by omega)), (hdiv_val ρ).1]
            rw [hout_valF ρ, hd0_val ρ, hrpz_val ρ, hqZ_val, udiv_eq_of_divRec]
            simp only [decide_eq_true_eq]
          · simp only [hokF]
            have hoomF : hdrF.oom ≠ 0#32 := fun h0 => hokF (hoomF_iff.mpr h0)
            c0_hfast_nogrp <;> first | contradiction | skip
            apply bv_udiv_rel_ret_wp Γ hrel (by rw [hfF.lits_len, hlenW, hmark0]; omega) hmemF
            intro mR hmR
            have hfR := blastFrame_with_lits_len hdrF mark0
            refine bv_udiv_oom_ret_q (n_off := n_off) (d_off := d_off) (w := w)
              (want_rem := want_rem) hQ (hframe0F.trans hfR) hle0F (by omega)
              (aigInv_blastFrame hinvF hfR rfl) hlenF_0 hpresF_0 hoomF hmark0 ?_ hmR
            intro h0 hlencap0 hptr0 _ _ _ hcap0 hmax0
            have hA_eq : g0.A = gW.A := hle0W.1
            have haigc : hdrW.aig_cap = hdr0.aig_cap := hframe0W.aig_cap
            exact hoomF (hboundF hoomW hlencapW (fun _ => hptrW)
              (by rw [hlenW]; omega) (by rw [hlenW]; omega) (by rw [hlenW]; omega)
              (by rw [← hA_eq, haigc]; omega) (by omega))
      · exfalso; apply hrem; bv_omega

private theorem bv_udiv_post_alloc_wp (Γ : Env)
    (heq : Γ.Has "bv_blast_eq" bvBlastEqSpec)
    (hnot : Γ.Has "bv_aig_not" bvAigNotSpec)
    (hsub : Γ.Has "bv_blast_sub_with_borrow" bvBlastSubWithBorrowSpec)
    (hite : Γ.Has "bv_blast_ite_into" bvBlastIteIntoSpec)
    (hrel : Γ.Has "bv_lits_release" bvLitsReleaseSpec)
    {h : Val i64} {n_off d_off w mark0 mark1 out_off q_off r_off rp_off diff_off : BitVec 32}
    {want_rem : BitVec 32}
    {hdr0 hdrInit : BVHdrState} {g0 : Aig}
    {aw0 : List (BitVec 64)} {ht0 lp0 : List (BitVec 32)}
    {R : Mem 64 → Prop} {mInit : Mem 64} {Q : Post [i32]} {X : XPost}
    (hoom0 : hdr0.oom = 0#32) (hw : 0 < w.toNat) (hframe0 : hdr0.DcBlastFrame hdrInit)
    (hinvInit : AigInv hdrInit g0 aw0 ht0)
    (hoomInit : hdrInit.oom = 0#32) (hlencapInit : hdrInit.lits_len.toNat ≤ hdrInit.lits_cap.toNat)
    (hcaplenInit : hdrInit.lits_cap.toNat ≤ lp0.length) (hptrInit : hdrInit.lits_ptr ≠ 0#64)
    (hmark0 : mark0 = hdr0.lits_len) (hmark1 : mark1 = out_off + w)
    (hout : out_off = hdr0.lits_len)
    (hq_eq : q_off.toNat = out_off.toNat + w.toNat)
    (hr_eq : r_off.toNat = q_off.toNat + w.toNat)
    (hrp_eq : rp_off.toNat = r_off.toNat + w.toNat)
    (hdiff_eq : diff_off.toNat = rp_off.toNat + w.toNat)
    (hlen5 : diff_off.toNat + w.toNat = hdrInit.lits_len.toNat)
    (hn : n_off.toNat + w.toNat ≤ hdr0.lits_len.toNat)
    (hd : d_off.toNat + w.toNat ≤ hdr0.lits_len.toNat)
    (hwfn : SliceLitsWf hdrInit lp0 n_off.toNat w.toNat)
    (hwfd : SliceLitsWf hdrInit lp0 d_off.toNat w.toNat)
    (hmemInit : (bvHdrMem h hdrInit ⋆ array64 hdrInit.aig_ptr aw0 ⋆
      array (t := i32) hdrInit.ht_ptr ht0 ⋆ array (t := i32) hdrInit.lits_ptr lp0 ⋆ R) mInit)
    (hQ : ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Aig)
      (aw' : List (BitVec 64)) (ht' lp' : List (BitVec 32)) (m' : Mem 64),
      hdr0.DcBlastFrame hdr' → g0 ≤ g' →
      g'.nodes.size ≤ g0.nodes.size + (7 * w.toNat + 12 * w.toNat * w.toNat) →
      AigInv hdr' g' aw' ht' → lp'.length = lp0.length →
      (∀ p, p < hdr0.lits_len.toNat → lp'.getD p 0#32 = lp0.getD p 0#32) →
      (hdr0.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
      (hdr0.oom = 0#32 → hdr0.lits_len.toNat ≤ hdr0.lits_cap.toNat →
        (0 < w.toNat → hdr0.lits_ptr ≠ 0#64) →
        n_off.toNat + w.toNat ≤ hdr0.lits_len.toNat →
        d_off.toNat + w.toNat ≤ hdr0.lits_len.toNat →
        5 * w.toNat ≤ hdr0.lits_cap.toNat - hdr0.lits_len.toNat →
        g0.A + 1 + g0.nodes.size + (7 * w.toNat + 12 * w.toNat * w.toNat) ≤ hdr0.aig_cap.toNat →
        g0.nodes.size + (7 * w.toNat + 12 * w.toNat * w.toNat) ≤ bvMaxGates → hdr'.oom = 0#32) →
      (hdr'.oom ≠ 0#32 → ret = 0xFFFFFFFF#32 ∧ hdr'.lits_len = hdr0.lits_len) →
      (hdr'.oom = 0#32 → ret = hdr0.lits_len ∧ hdr'.lits_len = hdr0.lits_len + w ∧
        hdr'.lits_len.toNat ≤ hdr'.lits_cap.toNat ∧ SliceLitsWf hdr' lp' ret.toNat w.toNat ∧
        ∀ ρ, sliceVal g' ρ lp' ret.toNat w.toNat =
          if want_rem ≠ 0#32 then
            sliceVal g0 ρ lp0 n_off.toNat w.toNat % sliceVal g0 ρ lp0 d_off.toNat w.toNat
          else
            sliceVal g0 ρ lp0 n_off.toNat w.toNat / sliceVal g0 ρ lp0 d_off.toNat w.toNat) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aw' ⋆
        array (t := i32) hdr'.ht_ptr ht' ⋆ array (t := i32) hdr'.lits_ptr lp' ⋆ R) m' →
      Q (ret, ()) m') :
    wp Γ Q X
      (Expr.let_ (op2 (OpCode.add i64) (Arg.var h) (Arg.imm (t := i64) 56#64)) fun p_23 =>
        Expr.load i64 (Arg.var p_23.fst) fun ld =>
        udivZeroLoopExpr w q_off r_off ld fun p_24 =>
          Expr.call (as := [i64, i32, i32, i32]) (bs := [i32]) "bv_blast_eq"
            (Arg.var h, Arg.var d_off, Arg.var q_off, Arg.var w, ()) fun p_26 =>
          Expr.let_ (op2 (OpCode.add i64) (Arg.var h) (Arg.imm (t := i64) 120#64)) fun p_27 =>
          Expr.load i32 (Arg.var p_27.fst) fun ld_1 =>
          Expr.let_ (op2 (OpCode.cmp CmpOp.ne i32 Ty.bool (by decide))
            (Arg.var ld_1) (Arg.imm 0#32)) fun p_28 =>
          Expr.jnz (Arg.var p_28.fst) (udivRelRetExpr h mark0)
            (udivStepLoopExpr h n_off d_off w mark0 q_off r_off rp_off diff_off p_24.fst ld
              fun p_29 => udivFinishExpr h n_off w mark0 mark1 out_off q_off r_off
                rp_off want_rem p_26.fst p_29.fst ld)) mInit := by
  have hout_nat : out_off.toNat = hdr0.lits_len.toNat := congrArg BitVec.toNat hout
  apply wp_load_hdr_lits_ptr hmemInit
  apply bv_udiv_zero_loop_wp Γ hinvInit rfl (by omega) (by omega) hlencapInit hcaplenInit
    (by unfold DisjointSlice; omega) hmemInit
  intro dum0 lpZ mZ _ hlenZ hpresZ hwf_qZ hwf_rZ hqZ hrZ hmZ
  have hpresZ_0 : ∀ p, p < q_off.toNat → lpZ.getD p 0#32 = lp0.getD p 0#32 :=
    fun p hp => hpresZ p (by omega) (by omega)
  have hpresZ_lt : ∀ p, p < hdr0.lits_len.toNat → lpZ.getD p 0#32 = lp0.getD p 0#32 :=
    fun p hp => hpresZ_0 p (by omega)
  have hwf_nZ : SliceLitsWf hdrInit lpZ n_off.toNat w.toNat :=
    sliceLitsWf_of_agree (fun p _ hp2 => hpresZ_0 p (by omega)) hwfn
  have hwf_dZ : SliceLitsWf hdrInit lpZ d_off.toNat w.toNat :=
    sliceLitsWf_of_agree (fun p _ hp2 => hpresZ_0 p (by omega)) hwfd
  c0_hcall heq
  refine ⟨hdrInit, g0, aw0, ht0, lpZ, R, hinvInit, by rw [hlenZ]; exact hcaplenInit, hlencapInit,
    ?_, hmZ, ?_⟩
  · intro _ _ _ _ _
    exact ⟨hwf_dZ, hwf_qZ⟩
  · intro d_is_zero hdrEq gEq awEq htEq mEq hfEq hleEq hnodesEq hinvEq _ hboundEq
      hoomEq_val hokEq hmemEq
    have hfEq_blast : hdrInit.DcBlastFrame hdrEq := hfEq.toDcBlastFrame
    have hframe0Eq : hdr0.DcBlastFrame hdrEq := hframe0.trans hfEq_blast
    apply wp_load_hdr_oom hmemEq
    by_cases hoomEq : hdrEq.oom = 0#32
    · c0_hfast_nogrp
      · exfalso; exact absurd hoomEq ‹_›
      · obtain ⟨_, _, _, _, _, hd0_lt, hd0_val⟩ := hokEq hoomEq
        have hlencapEq : hdrEq.lits_len.toNat ≤ hdrEq.lits_cap.toNat := by
          rw [hfEq.lits_len, hfEq.lits_cap]; exact hlencapInit
        have hcaplenEq : hdrEq.lits_cap.toNat ≤ lpZ.length := by
          rw [hlenZ, hfEq.lits_cap]; exact hcaplenInit
        have hptrEq : hdrEq.lits_ptr ≠ 0#64 := by rw [hfEq.lits_ptr]; exact hptrInit
        have hwf_nEq : SliceLitsWf hdrEq lpZ n_off.toNat w.toNat :=
          sliceLitsWf_of_inv_le hinvInit hinvEq hleEq (by rw [hfEq.lits_len]; exact Nat.le_refl _)
            hwf_nZ (fun _ _ _ => rfl)
        have hwf_dEq : SliceLitsWf hdrEq lpZ d_off.toNat w.toNat :=
          sliceLitsWf_of_inv_le hinvInit hinvEq hleEq (by rw [hfEq.lits_len]; exact Nat.le_refl _)
            hwf_dZ (fun _ _ _ => rfl)
        have hwf_qEq : SliceLitsWf hdrEq lpZ q_off.toNat w.toNat :=
          sliceLitsWf_of_inv_le hinvInit hinvEq hleEq (by rw [hfEq.lits_len]; exact Nat.le_refl _)
            hwf_qZ (fun _ _ _ => rfl)
        have hwf_rEq : SliceLitsWf hdrEq lpZ r_off.toNat w.toNat :=
          sliceLitsWf_of_inv_le hinvInit hinvEq hleEq (by rw [hfEq.lits_len]; exact Nat.le_refl _)
            hwf_rZ (fun _ _ _ => rfl)
        have hqEq : ∀ ρ, sliceVal gEq ρ lpZ q_off.toNat w.toNat = 0#w.toNat := fun ρ => by
          rw [sliceVal_extend hinvInit hleEq hwf_qZ]; exact hqZ ρ
        have hrEq : ∀ ρ, sliceVal gEq ρ lpZ r_off.toNat w.toNat = 0#w.toNat := fun ρ => by
          rw [sliceVal_extend hinvInit hleEq hwf_rZ]; exact hrZ ρ
        apply bv_udiv_step_loop_wp Γ hnot hsub hite hrel hw hframe0Eq hleEq hnodesEq hinvEq
          hfEq.lits_ptr.symm hoomEq hlencapEq hcaplenEq hptrEq hmark0
          (by omega) hr_eq hrp_eq hdiff_eq (by rw [hfEq.lits_len]; exact hlen5) hn hd
          hwf_nEq hwf_dEq hwf_qEq hwf_rEq hqEq hrEq hmemEq
        · intro hdrF gF awF htF lpF mF hfF hleF hndF hinvF hlenF hpresF hoomF hlencF hnobF hmF
          exact bv_udiv_oom_ret_q (n_off := n_off) (d_off := d_off) (w := w)
            (want_rem := want_rem) hQ hfF hleF hndF hinvF (hlenF.trans hlenZ)
            (fun p hp => by rw [hpresF p hp, hpresZ_lt p hp]) hoomF hlencF
            (fun _ _ _ _ _ _ ha hc => hnobF ha hc) hmF
        · intro dumW hdrW gW awW htW lpW mW hfW hleW hnodesW hinvW hoomW hlenW hlenW_lp
            hpresW hwfqW hwfrW hdivW hmW
          have hd_agree : ∀ ρ, sliceVal g0 ρ lpZ d_off.toNat w.toNat =
              sliceVal g0 ρ lp0 d_off.toNat w.toNat := fun ρ =>
            sliceVal_eq_of_agree (fun p _ hp2 => hpresZ_0 p (by omega))
          have hn_agree : ∀ ρ, sliceVal gW ρ lpW n_off.toNat w.toNat =
              sliceVal g0 ρ lp0 n_off.toNat w.toNat := fun ρ => by
            have hle_0W : g0 ≤ gW := Aig.extends_trans hleEq hleW
            have h1 : sliceVal gW ρ lpW n_off.toNat w.toNat =
                sliceVal gW ρ lp0 n_off.toNat w.toNat :=
              sliceVal_eq_of_agree (fun p _ hp2 => by
                rw [hpresW p (by omega), hpresZ_0 p (by omega)])
            have h2 : sliceVal gW ρ lp0 n_off.toNat w.toNat =
                sliceVal g0 ρ lp0 n_off.toNat w.toNat :=
              sliceVal_extend hinvInit hle_0W hwfn
            exact h1.trans h2
          have hd0_valW : ∀ ρ, gW.evalLit ρ (UInt32.ofBitVec d_is_zero) =
              decide (sliceVal g0 ρ lp0 d_off.toNat w.toNat = 0#w.toNat) := fun ρ => by
            rw [evalLit_extend_of_inv hinvEq hleW hd0_lt, hd0_val ρ, hqZ ρ, hd_agree ρ]
          have hdivW' : ∀ ρ,
              let out := BitVec.divRec w.toNat
                { n := sliceVal g0 ρ lp0 n_off.toNat w.toNat,
                  d := sliceVal g0 ρ lp0 d_off.toNat w.toNat }
                (BitVec.DivModState.init w.toNat)
              sliceVal gW ρ lpW q_off.toNat w.toNat = out.q ∧
              sliceVal gW ρ lpW r_off.toNat w.toNat = out.r := fun ρ => by
            have hn_eq : sliceVal gEq ρ lpZ n_off.toNat w.toNat =
                sliceVal g0 ρ lp0 n_off.toNat w.toNat := by
              rw [sliceVal_extend hinvInit hleEq hwf_nZ]
              exact sliceVal_eq_of_agree (fun p _ hp2 => hpresZ_0 p (by omega))
            have hd_eq : sliceVal gEq ρ lpZ d_off.toNat w.toNat =
                sliceVal g0 ρ lp0 d_off.toNat w.toNat := by
              rw [sliceVal_extend hinvInit hleEq hwf_dZ]
              exact hd_agree ρ
            simpa [hn_eq, hd_eq] using hdivW ρ
          have hwf_nW : SliceLitsWf hdrW lpW n_off.toNat w.toNat :=
            sliceLitsWf_of_inv_le hinvEq hinvW hleW (by rw [hlenW]; exact Nat.le_refl _)
              hwf_nEq (fun p _ hp2 => hpresW p (by omega))
          apply bv_udiv_finish_wp Γ hite hrel hoom0 hw hframe0Eq hfW hleEq hleW hnodesEq hnodesW
            hinvW (by rw [hfW.lits_ptr, hfEq.lits_ptr]) hoomW
            (by rw [hlenW, hfW.lits_cap]; exact hlencapEq)
            (by rw [hlenW_lp, hfW.lits_cap]; exact hcaplenEq)
            (by rw [hfW.lits_ptr]; exact hptrEq) hmark0 hmark1 hout (by omega) hr_eq hrp_eq
            hdiff_eq (by rw [hfEq.lits_len]; exact hlen5) hlenW (hlenW_lp.trans hlenZ)
            (fun p hp => by rw [hpresW p (by omega), hpresZ_lt p hp]) hn hwf_nW hwfqW hwfrW
            (by have := aigLen_le_of_inv_le hinvEq hinvW hleW; omega) hd0_valW hdivW' hn_agree
            hmW hQ
    · c0_hfast_nogrp
      · apply bv_udiv_rel_ret_wp Γ hrel (by rw [hfEq.lits_len, hmark0]; omega) hmemEq
        intro mR hmR
        have hfR := blastFrame_with_lits_len hdrEq mark0
        refine bv_udiv_oom_ret_q (n_off := n_off) (d_off := d_off) (w := w)
          (want_rem := want_rem) hQ (hframe0Eq.trans hfR) hleEq (by omega)
          (aigInv_blastFrame hinvEq hfR rfl) hlenZ hpresZ_lt hoomEq hmark0 ?_ hmR
        intro h0 hlencap0 hptr0 _ _ _ hcap0 hmax0
        have haigc : hdrInit.aig_cap = hdr0.aig_cap := hframe0.aig_cap
        exact hoomEq (hboundEq hoomInit hlencapInit (fun _ => hptrInit) (by omega) (by omega)
          (by rw [haigc]; omega) (by omega))
      · exfalso; apply hoomEq; bv_omega

private theorem bv_udiv_alloc4_wp (Γ : Env)
    (hmark : Γ.Has "bv_lits_mark" bvLitsMarkSpec)
    (halloc : Γ.Has "bv_lits_alloc" bvLitsAllocSpec)
    (hrel : Γ.Has "bv_lits_release" bvLitsReleaseSpec)
    (heq : Γ.Has "bv_blast_eq" bvBlastEqSpec)
    (hnot : Γ.Has "bv_aig_not" bvAigNotSpec)
    (hsub : Γ.Has "bv_blast_sub_with_borrow" bvBlastSubWithBorrowSpec)
    (hite : Γ.Has "bv_blast_ite_into" bvBlastIteIntoSpec)
    {h : Val i64} {n_off d_off w want_rem out_off : BitVec 32}
    {hdr0 : BVHdrState} {g0 : Aig}
    {aw0 : List (BitVec 64)} {ht0 lp0 : List (BitVec 32)}
    {R : Mem 64 → Prop} {m1 : Mem 64} {Q : Post [i32]} {X : XPost}
    (hw : 0 < w.toNat) (hoom0 : hdr0.oom = 0#32)
    (hlencap0 : hdr0.lits_len.toNat ≤ hdr0.lits_cap.toNat)
    (hcaplen0 : hdr0.lits_cap.toNat ≤ lp0.length) (hptr0 : hdr0.lits_ptr ≠ 0#64)
    (hout : out_off = hdr0.lits_len) (hfit1 : w.toNat ≤ hdr0.lits_cap.toNat - hdr0.lits_len.toNat)
    (hn : n_off.toNat + w.toNat ≤ hdr0.lits_len.toNat)
    (hd : d_off.toNat + w.toNat ≤ hdr0.lits_len.toNat)
    (hinv0 : AigInv hdr0 g0 aw0 ht0) (hwfn0 : SliceLitsWf hdr0 lp0 n_off.toNat w.toNat)
    (hwfd0 : SliceLitsWf hdr0 lp0 d_off.toNat w.toNat)
    (hmem1 : (bvHdrMem h { hdr0 with lits_len := hdr0.lits_len + w } ⋆ array64 hdr0.aig_ptr aw0 ⋆
      array (t := i32) hdr0.ht_ptr ht0 ⋆ array (t := i32) hdr0.lits_ptr lp0 ⋆ R) m1)
    (hQ : ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Aig)
      (aw' : List (BitVec 64)) (ht' lp' : List (BitVec 32)) (m' : Mem 64),
      hdr0.DcBlastFrame hdr' → g0 ≤ g' →
      g'.nodes.size ≤ g0.nodes.size + (7 * w.toNat + 12 * w.toNat * w.toNat) →
      AigInv hdr' g' aw' ht' → lp'.length = lp0.length →
      (∀ p, p < hdr0.lits_len.toNat → lp'.getD p 0#32 = lp0.getD p 0#32) →
      (hdr0.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
      (hdr0.oom = 0#32 → hdr0.lits_len.toNat ≤ hdr0.lits_cap.toNat →
        (0 < w.toNat → hdr0.lits_ptr ≠ 0#64) →
        n_off.toNat + w.toNat ≤ hdr0.lits_len.toNat →
        d_off.toNat + w.toNat ≤ hdr0.lits_len.toNat →
        5 * w.toNat ≤ hdr0.lits_cap.toNat - hdr0.lits_len.toNat →
        g0.A + 1 + g0.nodes.size + (7 * w.toNat + 12 * w.toNat * w.toNat) ≤ hdr0.aig_cap.toNat →
        g0.nodes.size + (7 * w.toNat + 12 * w.toNat * w.toNat) ≤ bvMaxGates → hdr'.oom = 0#32) →
      (hdr'.oom ≠ 0#32 → ret = 0xFFFFFFFF#32 ∧ hdr'.lits_len = hdr0.lits_len) →
      (hdr'.oom = 0#32 → ret = hdr0.lits_len ∧ hdr'.lits_len = hdr0.lits_len + w ∧
        hdr'.lits_len.toNat ≤ hdr'.lits_cap.toNat ∧ SliceLitsWf hdr' lp' ret.toNat w.toNat ∧
        ∀ ρ, sliceVal g' ρ lp' ret.toNat w.toNat =
          if want_rem ≠ 0#32 then
            sliceVal g0 ρ lp0 n_off.toNat w.toNat % sliceVal g0 ρ lp0 d_off.toNat w.toNat
          else
            sliceVal g0 ρ lp0 n_off.toNat w.toNat / sliceVal g0 ρ lp0 d_off.toNat w.toNat) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aw' ⋆
        array (t := i32) hdr'.ht_ptr ht' ⋆ array (t := i32) hdr'.lits_ptr lp' ⋆ R) m' →
      Q (ret, ()) m') :
    wp Γ Q X
      (Expr.call (as := [i64]) (bs := [i32]) "bv_lits_mark" (Arg.var h, ()) fun p_10 =>
        Expr.call (as := [i64, i32]) (bs := [i32]) "bv_lits_alloc"
          (Arg.var h, Arg.var w, ()) fun p_11 =>
        Expr.let_ (op2 (OpCode.add i64) (Arg.var h) (Arg.imm (t := i64) 120#64)) fun p_12 =>
        Expr.load i32 (Arg.var p_12.fst) fun ld_1 =>
        Expr.let_ (op2 (OpCode.cmp CmpOp.ne i32 Ty.bool (by decide))
          (Arg.var ld_1) (Arg.imm 0#32)) fun p_13 =>
        Expr.jnz (Arg.var p_13.fst) (udivRelRetExpr h hdr0.lits_len)
          (Expr.call (as := [i64, i32]) (bs := [i32]) "bv_lits_alloc"
            (Arg.var h, Arg.var w, ()) fun p_14 =>
          Expr.let_ (op2 (OpCode.add i64) (Arg.var h) (Arg.imm (t := i64) 120#64)) fun p_15 =>
          Expr.load i32 (Arg.var p_15.fst) fun ld_2 =>
          Expr.let_ (op2 (OpCode.cmp CmpOp.ne i32 Ty.bool (by decide))
            (Arg.var ld_2) (Arg.imm 0#32)) fun p_16 =>
          Expr.jnz (Arg.var p_16.fst) (udivRelRetExpr h hdr0.lits_len)
            (Expr.call (as := [i64, i32]) (bs := [i32]) "bv_lits_alloc"
              (Arg.var h, Arg.var w, ()) fun p_17 =>
            Expr.let_ (op2 (OpCode.add i64) (Arg.var h) (Arg.imm (t := i64) 120#64)) fun p_18 =>
            Expr.load i32 (Arg.var p_18.fst) fun ld_3 =>
            Expr.let_ (op2 (OpCode.cmp CmpOp.ne i32 Ty.bool (by decide))
              (Arg.var ld_3) (Arg.imm 0#32)) fun p_19 =>
            Expr.jnz (Arg.var p_19.fst) (udivRelRetExpr h hdr0.lits_len)
              (Expr.call (as := [i64, i32]) (bs := [i32]) "bv_lits_alloc"
                (Arg.var h, Arg.var w, ()) fun p_20 =>
              Expr.let_ (op2 (OpCode.add i64) (Arg.var h) (Arg.imm (t := i64) 120#64)) fun p_21 =>
              Expr.load i32 (Arg.var p_21.fst) fun ld_4 =>
              Expr.let_ (op2 (OpCode.cmp CmpOp.ne i32 Ty.bool (by decide))
                (Arg.var ld_4) (Arg.imm 0#32)) fun p_22 =>
              Expr.jnz (Arg.var p_22.fst) (udivRelRetExpr h hdr0.lits_len)
                (Expr.let_ (op2 (OpCode.add i64) (Arg.var h) (Arg.imm (t := i64) 56#64)) fun p_23 =>
                  Expr.load i64 (Arg.var p_23.fst) fun ld =>
                  udivZeroLoopExpr w p_11.fst p_14.fst ld fun p_24 =>
                    Expr.call (as := [i64, i32, i32, i32]) (bs := [i32]) "bv_blast_eq"
                      (Arg.var h, Arg.var d_off, Arg.var p_11.fst, Arg.var w, ()) fun p_26 =>
                    Expr.let_ (op2 (OpCode.add i64) (Arg.var h) (Arg.imm (t := i64) 120#64))
                      fun p_27 =>
                    Expr.load i32 (Arg.var p_27.fst) fun ld_1 =>
                    Expr.let_ (op2 (OpCode.cmp CmpOp.ne i32 Ty.bool (by decide))
                      (Arg.var ld_1) (Arg.imm 0#32)) fun p_28 =>
                    Expr.jnz (Arg.var p_28.fst) (udivRelRetExpr h hdr0.lits_len)
                      (udivStepLoopExpr h n_off d_off w hdr0.lits_len p_11.fst p_14.fst p_17.fst
                        p_20.fst p_24.fst ld fun p_29 => udivFinishExpr h n_off w
                        hdr0.lits_len p_10.fst out_off p_11.fst p_14.fst p_17.fst want_rem
                        p_26.fst p_29.fst ld)))))) m1 := by
  have hcap32 : hdr0.lits_cap.toNat < 2 ^ 32 := hdr0.lits_cap.isLt
  have hout_nat : out_off.toNat = hdr0.lits_len.toNat := congrArg BitVec.toNat hout
  let hdr1 := { hdr0 with lits_len := hdr0.lits_len + w }
  have h1_cap : hdr1.lits_cap = hdr0.lits_cap := rfl
  have h1_len : hdr1.lits_len.toNat = hdr0.lits_len.toNat + w.toNat := by
    change (hdr0.lits_len + w).toNat = _; rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  c0_hcall hmark
  refine ⟨hdr1, _, opMem_to_hdr hmem1, ?_⟩
  apply bv_udiv_alloc_rel_wp Γ halloc hrel (hdr := hdr1) hoom0
    (by rw [h1_cap, h1_len]; omega) (by rw [h1_len]; omega) hmem1
  · intro hnofit mF hmF
    exact bv_udiv_oom_ret_q (n_off := n_off) (d_off := d_off) (w := w) (want_rem := want_rem) hQ
      (udiv_hdr0_oom_frame hdr0) (Aig.extends_rfl (g := g0)) (by simp)
      (aigInv_blastFrame hinv0 (udiv_hdr0_oom_frame hdr0) rfl) rfl (fun _ _ => rfl) (by simp) rfl
      (fun _ _ _ _ _ h5 _ _ => hnofit (by rw [h1_cap, h1_len]; omega)) hmF
  · intro hfit2 m2 hm2
    dsimp only
    rw [h1_cap, h1_len] at hfit2
    let hdr2 := { hdr1 with lits_len := hdr1.lits_len + w }
    have h2_cap : hdr2.lits_cap = hdr0.lits_cap := rfl
    have h2_len : hdr2.lits_len.toNat = hdr0.lits_len.toNat + 2 * w.toNat := by
      change (hdr1.lits_len + w).toNat = _
      rw [BitVec.toNat_add, h1_len, Nat.mod_eq_of_lt (by omega)]; omega
    apply bv_udiv_alloc_rel_wp Γ halloc hrel (hdr := hdr2) hoom0
      (by rw [h2_cap, h2_len]; omega) (by rw [h2_len]; omega) hm2
    · intro hnofit mF hmF
      exact bv_udiv_oom_ret_q (n_off := n_off) (d_off := d_off) (w := w) (want_rem := want_rem) hQ
        (udiv_hdr0_oom_frame hdr0) (Aig.extends_rfl (g := g0)) (by simp)
        (aigInv_blastFrame hinv0 (udiv_hdr0_oom_frame hdr0) rfl) rfl (fun _ _ => rfl) (by simp) rfl
        (fun _ _ _ _ _ h5 _ _ => hnofit (by rw [h2_cap, h2_len]; omega)) hmF
    · intro hfit3 m3 hm3
      dsimp only
      rw [h2_cap, h2_len] at hfit3
      let hdr3 := { hdr2 with lits_len := hdr2.lits_len + w }
      have h3_cap : hdr3.lits_cap = hdr0.lits_cap := rfl
      have h3_len : hdr3.lits_len.toNat = hdr0.lits_len.toNat + 3 * w.toNat := by
        change (hdr2.lits_len + w).toNat = _
        rw [BitVec.toNat_add, h2_len, Nat.mod_eq_of_lt (by omega)]; omega
      apply bv_udiv_alloc_rel_wp Γ halloc hrel (hdr := hdr3) hoom0
        (by rw [h3_cap, h3_len]; omega) (by rw [h3_len]; omega) hm3
      · intro hnofit mF hmF
        exact bv_udiv_oom_ret_q (n_off := n_off) (d_off := d_off) (w := w) (want_rem := want_rem)
          hQ (udiv_hdr0_oom_frame hdr0) (Aig.extends_rfl (g := g0)) (by simp)
          (aigInv_blastFrame hinv0 (udiv_hdr0_oom_frame hdr0) rfl) rfl (fun _ _ => rfl) (by simp)
          rfl (fun _ _ _ _ _ h5 _ _ => hnofit (by rw [h3_cap, h3_len]; omega)) hmF
      · intro hfit4 m4 hm4
        dsimp only
        rw [h3_cap, h3_len] at hfit4
        let hdr4 := { hdr3 with lits_len := hdr3.lits_len + w }
        have h4_cap : hdr4.lits_cap = hdr0.lits_cap := rfl
        have h4_len : hdr4.lits_len.toNat = hdr0.lits_len.toNat + 4 * w.toNat := by
          change (hdr3.lits_len + w).toNat = _
          rw [BitVec.toNat_add, h3_len, Nat.mod_eq_of_lt (by omega)]; omega
        apply bv_udiv_alloc_rel_wp Γ halloc hrel (hdr := hdr4) hoom0
          (by rw [h4_cap, h4_len]; omega) (by rw [h4_len]; omega) hm4
        · intro hnofit mF hmF
          exact bv_udiv_oom_ret_q (n_off := n_off) (d_off := d_off) (w := w) (want_rem := want_rem)
            hQ (udiv_hdr0_oom_frame hdr0) (Aig.extends_rfl (g := g0)) (by simp)
            (aigInv_blastFrame hinv0 (udiv_hdr0_oom_frame hdr0) rfl) rfl (fun _ _ => rfl) (by simp)
            rfl (fun _ _ _ _ _ h5 _ _ => hnofit (by rw [h4_cap, h4_len]; omega)) hmF
        · intro hfit5 m5 hm5
          dsimp only
          rw [h4_cap, h4_len] at hfit5
          let hdr5 := { hdr4 with lits_len := hdr4.lits_len + w }
          have h5_cap : hdr5.lits_cap = hdr0.lits_cap := rfl
          have h5_len : hdr5.lits_len.toNat = hdr0.lits_len.toNat + 5 * w.toNat := by
            change (hdr4.lits_len + w).toNat = _
            rw [BitVec.toNat_add, h4_len, Nat.mod_eq_of_lt (by omega)]; omega
          have hlencap5 : hdr5.lits_len.toNat ≤ hdr5.lits_cap.toNat := by
            rw [h5_cap, h5_len]; omega
          have hf05 := blastFrame_with_lits_len hdr0 hdr5.lits_len
          have hinv5 : AigInv hdr5 g0 aw0 ht0 := aigInv_blastFrame hinv0 hf05 rfl
          have hwfn5 : SliceLitsWf hdr5 lp0 n_off.toNat w.toNat :=
            sliceLitsWf_mono hwfn0 (Nat.le_refl _) (by rw [h5_len]; omega) (fun _ _ _ => rfl)
          have hwfd5 : SliceLitsWf hdr5 lp0 d_off.toNat w.toNat :=
            sliceLitsWf_mono hwfd0 (Nat.le_refl _) (by rw [h5_len]; omega) (fun _ _ _ => rfl)
          have hmark1 : hdr1.lits_len = out_off + w := by dsimp [hdr1]; rw [hout]
          exact bv_udiv_post_alloc_wp Γ heq hnot hsub hite hrel hoom0 hw hf05 hinv5 hoom0
            hlencap5 hcaplen0 hptr0 rfl hmark1 hout
            (by rw [h1_len]; omega) (by rw [h2_len, h1_len]; omega)
            (by rw [h3_len, h2_len]; omega) (by rw [h4_len, h3_len]; omega)
            (by rw [h5_len, h4_len]; omega) hn hd hwfn5 hwfd5 hm5 hQ

public theorem bv_blast_udiv_umod_wp (Γ : Env)
    (hsok : Γ.Has "bv_slice_ok" bvSliceOkSpec)
    (hmark : Γ.Has "bv_lits_mark" bvLitsMarkSpec)
    (halloc : Γ.Has "bv_lits_alloc" bvLitsAllocSpec)
    (hrel : Γ.Has "bv_lits_release" bvLitsReleaseSpec)
    (heq : Γ.Has "bv_blast_eq" bvBlastEqSpec)
    (hnot : Γ.Has "bv_aig_not" bvAigNotSpec)
    (hsub : Γ.Has "bv_blast_sub_with_borrow" bvBlastSubWithBorrowSpec)
    (hite : Γ.Has "bv_blast_ite_into" bvBlastIteIntoSpec) :
    bvBlastUdivUmodSpec.Le (Func.wp Γ bv_blast_udiv_umod_body) := by
  unfold bvBlastUdivUmodSpec
  intro x m Q X hpre
  rcases x with ⟨h, n_off, d_off, w, want_rem, _⟩
  rcases hpre with ⟨hdr0, g0, aw0, ht0, lp0, R, hinv0, hcaplen0, hpre_ok, hmem0, hQ⟩
  dsimp only [Func.wp]
  unfold bv_blast_udiv_umod_body
  let InvFail : Unit → Mem 64 → Prop := fun _ ml =>
    (bvHdrMem h hdr0 ⋆ array64 hdr0.aig_ptr aw0 ⋆
      array (t := i32) hdr0.ht_ptr ht0 ⋆ array (t := i32) hdr0.lits_ptr lp0 ⋆ R) ml ∧
    (hdr0.oom = 0#32 → hdr0.lits_len.toNat ≤ hdr0.lits_cap.toNat →
      (0 < w.toNat → hdr0.lits_ptr ≠ 0#64) →
      n_off.toNat + w.toNat ≤ hdr0.lits_len.toNat →
      d_off.toNat + w.toNat ≤ hdr0.lits_len.toNat → False)
  apply wp_join_state0 InvFail
  · intro J _ ml ⟨hm', hnob⟩
    dsimp only [Blocks.get]
    apply wp_store_hdr_oom hm'
    intro m'' hm''
    c0_hfast_nogrp
    have hf0 := blastFrame_with_lits_len hdr0 hdr0.lits_len
    exact bv_udiv_oom_ret_q (n_off := n_off) (d_off := d_off) (w := w) (want_rem := want_rem) hQ
      (udiv_hdr0_oom_frame hdr0) (Aig.extends_rfl (g := g0)) (by simp)
      (aigInv_blastFrame hinv0 (udiv_hdr0_oom_frame hdr0) rfl)
      rfl (fun _ _ => rfl) (by simp) rfl (fun h0 h1 h2 h3 h4 _ _ _ => hnob h0 h1 h2 h3 h4) hm''
  · intro J hJ
    apply wp_load_hdr_oom hmem0
    by_cases hoom0 : hdr0.oom = 0#32
    · c0_hfast_nogrp
      · exfalso; exact absurd hoom0 ‹_›
      · c0_hcall hsok
        refine ⟨hdr0, _, opMem_to_hdr hmem0, ?_⟩
        dsimp only
        c0_hsplit
        · have hn_ok : hdr0.lits_len.toNat ≤ hdr0.lits_cap.toNat ∧
              (0 < w.toNat → hdr0.lits_ptr ≠ 0#64) ∧
              n_off.toNat ≤ hdr0.lits_len.toNat ∧
              w.toNat ≤ hdr0.lits_len.toNat - n_off.toNat := by
            simpa using hc
          clear hc
          c0_hcall hsok
          refine ⟨hdr0, _, opMem_to_hdr hmem0, ?_⟩
          dsimp only
          c0_hsplit
          · have hd_ok : hdr0.lits_len.toNat ≤ hdr0.lits_cap.toNat ∧
                (0 < w.toNat → hdr0.lits_ptr ≠ 0#64) ∧
                d_off.toNat ≤ hdr0.lits_len.toNat ∧
                w.toNat ≤ hdr0.lits_len.toNat - d_off.toNat := by
              simpa using hc
            clear hc
            obtain ⟨hwfn0, hwfd0⟩ := hpre_ok hoom0 hn_ok.1 hn_ok.2.1 (by omega) (by omega)
            c0_hcall hmark
            refine ⟨hdr0, _, opMem_to_hdr hmem0, ?_⟩
            c0_hcall halloc
            refine ⟨hdr0, _, opMem_to_hdr hmem0, ?_⟩
            by_cases hfit1 : w.toNat ≤ hdr0.lits_cap.toNat - hdr0.lits_len.toNat
            · simp only [hoom0, hn_ok.1, hfit1, and_self, ↓reduceIte]
              intro m1 hm1
              have hm1' : (bvHdrMem h { hdr0 with lits_len := hdr0.lits_len + w } ⋆
                  array64 hdr0.aig_ptr aw0 ⋆ array (t := i32) hdr0.ht_ptr ht0 ⋆
                  array (t := i32) hdr0.lits_ptr lp0 ⋆ R) m1 := by
                simpa [hoom0] using opMem_of_hdr hm1
              apply wp_load_hdr_oom hm1'
              c0_hfast_nogrp
              · exfalso; exact absurd hoom0 ‹_›
              · subst ‹w = 0#32›
                have hlen_same : hdr0.lits_len + 0#32 = hdr0.lits_len := by bv_omega
                refine hQ hdr0.lits_len { hdr0 with lits_len := hdr0.lits_len + 0#32 }
                  g0 aw0 ht0 lp0 m1
                  (blastFrame_with_lits_len hdr0 (hdr0.lits_len + 0#32))
                  (Aig.extends_rfl (g := g0)) (by simp)
                  (aigInv_blastFrame hinv0
                    (blastFrame_with_lits_len hdr0 (hdr0.lits_len + 0#32)) rfl)
                  rfl (fun _ _ => rfl)
                  (fun hne => False.elim (hne hoom0))
                  (fun _ _ _ _ _ _ _ _ => hoom0)
                  (fun hne => False.elim (hne hoom0))
                  (fun _ => ⟨rfl, rfl, by simp [hlen_same]; exact hn_ok.1,
                    sliceLitsWf_zero _ (by simp [hlen_same]),
                    fun _ => BitVec.eq_of_getLsbD_eq fun _ hi =>
                      False.elim (by simp at hi)⟩) hm1'
              · have hw_pos : 0 < w.toNat := by bv_omega
                exact bv_udiv_alloc4_wp Γ hmark halloc hrel heq hnot hsub hite
                  hw_pos hoom0 hn_ok.1 hcaplen0 (hn_ok.2.1 hw_pos) rfl hfit1
                  (by omega) (by omega) hinv0 hwfn0 hwfd0 hm1' hQ
            · simp only [hoom0, hn_ok.1, hfit1, and_false, ↓reduceIte]
              intro m1 hm1
              have hm1' : (bvHdrMem h { hdr0 with oom := 1#32 } ⋆ array64 hdr0.aig_ptr aw0 ⋆
                  array (t := i32) hdr0.ht_ptr ht0 ⋆
                  array (t := i32) hdr0.lits_ptr lp0 ⋆ R) m1 := by
                simpa [hoom0] using opMem_of_hdr hm1
              apply wp_load_hdr_oom hm1'
              c0_hfast_nogrp
              · exact bv_udiv_oom_ret_q (n_off := n_off) (d_off := d_off) (w := w)
                  (want_rem := want_rem) hQ (udiv_hdr0_oom_frame hdr0)
                  (Aig.extends_rfl (g := g0)) (by simp)
                  (aigInv_blastFrame hinv0 (udiv_hdr0_oom_frame hdr0) rfl)
                  rfl (fun _ _ => rfl) (by simp) rfl
                  (fun _ _ _ _ _ h5 _ _ => hfit1 (by omega)) hm1'
              · exfalso; bv_omega
              · exfalso; bv_omega
          · have hd_bad : ¬ (hdr0.lits_len.toNat ≤ hdr0.lits_cap.toNat ∧
                (0 < w.toNat → hdr0.lits_ptr ≠ 0#64) ∧
                d_off.toNat ≤ hdr0.lits_len.toNat ∧
                w.toNat ≤ hdr0.lits_len.toNat - d_off.toNat) := by
              simpa using hc
            clear hc
            c0_hfast_nogrp
            exact hJ () m ⟨hmem0, fun _ h1 h2 h3 h4 => hd_bad ⟨h1, h2, by omega, by omega⟩⟩
        · have hn_bad : ¬ (hdr0.lits_len.toNat ≤ hdr0.lits_cap.toNat ∧
              (0 < w.toNat → hdr0.lits_ptr ≠ 0#64) ∧
              n_off.toNat ≤ hdr0.lits_len.toNat ∧
              w.toNat ≤ hdr0.lits_len.toNat - n_off.toNat) := by
            simpa using hc
          clear hc
          c0_hfast_nogrp
          exact hJ () m ⟨hmem0, fun _ h1 h2 h3 h4 => hn_bad ⟨h1, h2, by omega, by omega⟩⟩
    · c0_hfast_nogrp
      · exact hJ () m ⟨hmem0, fun h0 _ _ _ _ => hoom0 h0⟩
      · exfalso; apply hoom0; bv_omega

public theorem bv_blast_udiv_wp (Γ : Env)
    (hudiv : Γ.Has "bv_blast_udiv_umod" bvBlastUdivUmodSpec) :
    bvBlastUdivSpec.Le (Func.wp Γ bv_blast_udiv_body) := by
  unfold bvBlastUdivSpec
  intro x m Q X hpre
  rcases x with ⟨h, n_off, d_off, w, _⟩
  dsimp only [Func.wp]
  unfold bv_blast_udiv_body
  c0_hcall hudiv
  simpa using hpre

public theorem bv_blast_umod_wp (Γ : Env)
    (hudiv : Γ.Has "bv_blast_udiv_umod" bvBlastUdivUmodSpec) :
    bvBlastUmodSpec.Le (Func.wp Γ bv_blast_umod_body) := by
  unfold bvBlastUmodSpec
  intro x m Q X hpre
  rcases x with ⟨h, n_off, d_off, w, _⟩
  dsimp only [Func.wp]
  unfold bv_blast_umod_body
  c0_hcall hudiv
  simpa using hpre

end LeanQbe.T.Examples.Bitblast.Proof.OpsDivCpop
