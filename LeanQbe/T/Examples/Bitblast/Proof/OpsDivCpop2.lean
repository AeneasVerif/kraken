module

public import LeanQbe.T.Examples.Bitblast.Proof.OpsDivCpop2CpopHelpers
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.Rules

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Proof.OpsDivCpop

open LeanQbe.T
open LeanQbe.T.Examples.Bitblast.Ref
open LeanQbe.T.Examples.Bitblast.Src.OpsDivCpop

/-!
## Proofs for `bv_blast_add_into`, `bv_blast_cpop_layer`, and `bv_blast_cpop` (`OpsDivCpop2`)

Proves canonical `Func.wp` theorems (`BVBlastSpec.Le`) for the remaining three C0 functions in
`LeanQbe/T/Examples/Bitblast/Src/OpsDivCpop.lean`:
* `bv_blast_add_into_wp`
* `bv_blast_cpop_layer_wp`
* `bv_blast_cpop_wp`
-/

section

private theorem ofNat_1_32 : (1 : BitVec 32) = 1#32 := rfl

private theorem mul_w_sub_one_le (w : Nat) : 9 * (w - 1) * w ≤ 9 * w * w := by
  have h1 : 9 * (w - 1) ≤ 9 * w := Nat.mul_le_mul_left 9 (by omega)
  exact Nat.mul_le_mul_right w h1

/-! ## `bv_blast_add_into` -/

public theorem bv_blast_add_into_wp (Γ : Env)
    (hΓ_ok : Γ.Has "bv_slice_ok" bvSliceOkSpec)
    (hΓ_xor : Γ.Has "bv_aig_xor" bvAigXorSpec)
    (hΓ_and : Γ.Has "bv_mk_and" bvMkAndSpec)
    (hΓ_or : Γ.Has "bv_aig_or" bvAigOrSpec) :
    bvBlastAddIntoSpec.Le (Func.wp Γ bv_blast_add_into_body) := by
  intro (h, a_off, b_off, out_off, w, ()) m Q X
  rintro ⟨hdr, g, aw, ht, litsPool, R, hinv, hlcap, hwf, hm, hpost⟩
  dsimp only [Func.wp, bv_blast_add_into_body]
  let FailP : Unit → Mem 64 → Prop := fun _ ml =>
    (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aw ⋆
      array (t := i32) hdr.ht_ptr ht ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R) ml ∧
    (hdr.oom ≠ 0#32 ∨ ¬ (hdr.lits_len.toNat ≤ hdr.lits_cap.toNat ∧
      (0 < w.toNat → hdr.lits_ptr ≠ 0#64) ∧
      a_off.toNat + w.toNat ≤ hdr.lits_len.toNat ∧
      b_off.toNat + w.toNat ≤ hdr.lits_len.toNat ∧
      out_off.toNat + w.toNat ≤ hdr.lits_len.toNat))
  apply wp_join_state0 FailP
  · intro _ _ ml ⟨hml, hbad⟩
    simp only [Std.ExtHashMap.sep_assoc] at hml
    c0_hfast_nogrp
    let hdr' : BVHdrState := { hdr with oom := 1#32 }
    have hoom' : hdr'.oom ≠ 0#32 := by dsimp [hdr']; decide
    refine hpost false hdr' g aw ht litsPool m hdr_with_oom_aigFrame
      (Aig.extends_rfl g) (by omega) (aigInv_with_lits_len_oom hinv hdr.lits_len 1#32) rfl
      (fun _ _ => rfl) (fun _ => hoom') ⟨fun h => absurd h (by decide), fun hz => absurd hz hoom'⟩
      (fun ho hl hc ha hb ho' _ _ => by
        exfalso
        rcases hbad with hne | hnot
        · exact hne ho
        · exact hnot ⟨hl, hc, ha, hb, ho'⟩)
      (fun h => absurd h (by decide)) ?_
    simpa only [← Std.ExtHashMap.sep_assoc, ofNat_1_32, hdr'] using hm
  · intro J hJ
    have hmr : (bvHdrMem h hdr ⋆ (array64 hdr.aig_ptr aw ⋆
        (array (t := i32) hdr.ht_ptr ht ⋆ (array (t := i32) hdr.lits_ptr litsPool ⋆ R)))) m := by
      simpa only [Std.ExtHashMap.sep_assoc] using hm
    c0_hfast_nogrp
    · exact hJ () m ⟨hm, Or.inl hc⟩
    · have ho : hdr.oom = 0#32 := hc
      clear hc
      c0_hcall hΓ_ok
      refine ⟨hdr, _, opMem_to_hdr hm, ?_⟩
      dsimp only
      c0_hsplit
      · have hok_a := hc; clear hc
        c0_hcall hΓ_ok
        refine ⟨hdr, _, opMem_to_hdr hm, ?_⟩
        dsimp only
        c0_hsplit
        · have hok_b := hc; clear hc
          c0_hcall hΓ_ok
          refine ⟨hdr, _, opMem_to_hdr hm, ?_⟩
          dsimp only
          c0_hsplit
          · have hok_o := hc; clear hc
            have hlencap : hdr.lits_len.toNat ≤ hdr.lits_cap.toNat := hok_a.1
            have hptr : 0 < w.toNat → hdr.lits_ptr ≠ 0#64 := hok_a.2.1
            have haw : a_off.toNat + w.toNat ≤ hdr.lits_len.toNat := by omega
            have hbw : b_off.toNat + w.toNat ≤ hdr.lits_len.toNat := by omega
            have how : out_off.toNat + w.toNat ≤ hdr.lits_len.toNat := by omega
            obtain ⟨hwf_a, hwf_b, hdisj_a, hdisj_b⟩ := hwf ho hlencap hptr haw hbw how
            c0_hstraight
            exact bv_add_loop_wp Γ hΓ_xor hΓ_and hΓ_or hinv rfl hlcap ho hlencap haw hbw how
              hwf_a hwf_b hdisj_a hdisj_b hm hpost
          · have hno := hc; clear hc
            c0_hfast_nogrp
            exact hJ () m ⟨hm, Or.inr (fun ⟨_, _, _, _, h⟩ => hno ⟨hok_a.1, hok_a.2.1, by omega⟩)⟩
        · have hno := hc; clear hc
          c0_hfast_nogrp
          exact hJ () m ⟨hm, Or.inr (fun ⟨_, _, _, h, _⟩ => hno ⟨hok_a.1, hok_a.2.1, by omega⟩)⟩
      · have hno := hc; clear hc
        c0_hfast_nogrp
        exact hJ () m ⟨hm, Or.inr (fun ⟨h1, h2, h3, _, _⟩ => hno ⟨h1, h2, by omega⟩)⟩

/-! ## `bv_blast_cpop_layer` -/

public theorem bv_blast_cpop_layer_wp (Γ : Env)
    (hΓ_ok : Γ.Has "bv_slice_ok" bvSliceOkSpec)
    (hΓ_add : Γ.Has "bv_blast_add_into" bvBlastAddIntoSpec) :
    bvBlastCpopLayerSpec.Le (Func.wp Γ bv_blast_cpop_layer_body) := by
  intro (h, in_off, out_off, in_len, w, ()) m Q X
  rintro ⟨hdr, g, aw, ht, lp, R, hinv, hcaplen, hwf, hmem, hpost⟩
  dsimp only [Func.wp, bv_blast_cpop_layer_body]
  let FailP : Unit → Mem 64 → Prop := fun _ ml =>
    (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aw ⋆
      array (t := i32) hdr.ht_ptr ht ⋆ array (t := i32) hdr.lits_ptr lp ⋆ R) ml ∧
    (hdr.oom ≠ 0#32 ∨ ¬ (hdr.lits_len.toNat ≤ hdr.lits_cap.toNat ∧
      in_len.toNat * w.toNat < 2 ^ 32 ∧ (in_len.toNat + 1) / 2 * w.toNat < 2 ^ 32 ∧
      (0 < in_len.toNat * w.toNat → hdr.lits_ptr ≠ 0#64) ∧
      (0 < (in_len.toNat + 1) / 2 * w.toNat → hdr.lits_ptr ≠ 0#64) ∧
      in_off.toNat + in_len.toNat * w.toNat ≤ hdr.lits_len.toNat ∧
      out_off.toNat + (in_len.toNat + 1) / 2 * w.toNat ≤ hdr.lits_len.toNat))
  have hin64 : (BitVec.zeroExtend 64 in_len).toNat = in_len.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt]; have := in_len.isLt; omega
  have hw64 : (BitVec.zeroExtend 64 w).toNat = w.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt]; have := w.isLt; omega
  have hin1_lt64 : in_len.toNat + 1 < 2 ^ 64 := by have := in_len.isLt; omega
  have hprod1_lt64 : in_len.toNat * w.toNat < 2 ^ 64 :=
    Nat.lt_of_lt_of_eq (Nat.mul_lt_mul_of_lt_of_lt in_len.isLt w.isLt) rfl
  have hprod2_lt64 : (in_len.toNat + 1) / 2 * w.toNat < 2 ^ 64 := by
    have := in_len.isLt
    have hhalf : (in_len.toNat + 1) / 2 < 2 ^ 32 := by omega
    exact Nat.lt_of_lt_of_eq (Nat.mul_lt_mul_of_lt_of_lt hhalf w.isLt) rfl
  have hprod1 : (BitVec.zeroExtend 64 in_len * BitVec.zeroExtend 64 w).toNat =
      in_len.toNat * w.toNat := by
    rw [BitVec.toNat_mul, hin64, hw64, Nat.mod_eq_of_lt hprod1_lt64]
  have hdiv64 : ((BitVec.zeroExtend 64 in_len + 1#64) >>> 1).toNat = (in_len.toNat + 1) / 2 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, hin64,
      show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt hin1_lt64,
      Nat.shiftRight_eq_div_pow, Nat.pow_one]
  have hprod2 : (((BitVec.zeroExtend 64 in_len + 1#64) >>> 1) * BitVec.zeroExtend 64 w).toNat =
      (in_len.toNat + 1) / 2 * w.toNat := by
    rw [BitVec.toNat_mul, hdiv64, hw64, Nat.mod_eq_of_lt hprod2_lt64]
  c0_hstraight
  apply wp_join_state0 FailP
  · intro _ _ ml ⟨hml, hbad⟩
    simp only [Std.ExtHashMap.sep_assoc] at hml
    c0_hfast_nogrp
    let hdr' : BVHdrState := { hdr with oom := 1#32 }
    have hoom' : hdr'.oom ≠ 0#32 := by dsimp [hdr']; decide
    refine hpost false hdr' g aw ht lp m hdr_with_oom_aigFrame
      (Aig.extends_rfl g) (by omega) (aigInv_with_lits_len_oom hinv hdr.lits_len 1#32) rfl
      (fun _ _ => rfl) (fun _ => hoom') ⟨fun h => absurd h (by decide), fun hz => absurd hz hoom'⟩
      (fun ho hl h32a h32b hpa hpb ha hb _ _ => by
        exfalso
        rcases hbad with hne | hnot
        · exact hne ho
        · exact hnot ⟨hl, h32a, h32b, hpa, hpb, ha, hb⟩)
      (fun h => absurd h (by decide)) ?_
    simpa only [← Std.ExtHashMap.sep_assoc, ofNat_1_32, hdr'] using hm
  · intro J hJ
    have hmem_r : (bvHdrMem h hdr ⋆ (array64 hdr.aig_ptr aw ⋆
        (array (t := i32) hdr.ht_ptr ht ⋆ (array (t := i32) hdr.lits_ptr lp ⋆ R)))) m := by
      simpa only [Std.ExtHashMap.sep_assoc] using hmem
    c0_hsplit
    · c0_hfast_nogrp; exact hJ () m ⟨hmem, Or.inl hc⟩
    · have ho : hdr.oom = 0#32 := hc
      clear hc
      c0_hsplit
      · have hbad : 4294967295 < in_len.toNat * w.toNat := by
          rw [show (4294967295 : BitVec 64).toNat = 4294967295 from rfl,
            Nat.mod_eq_of_lt hprod1_lt64] at hc
          exact hc
        c0_hfast_nogrp
        exact hJ () m ⟨hmem, Or.inr (fun ⟨_, h32a, _, _⟩ => by omega)⟩
      · have hin32 : in_len.toNat * w.toNat < 2 ^ 32 := by
          rw [show (4294967295 : BitVec 64).toNat = 4294967295 from rfl,
            Nat.mod_eq_of_lt hprod1_lt64] at hc
          omega
        clear hc
        c0_hsplit
        · c0_hfast_nogrp
          have hbad : 4294967295 < (in_len.toNat + 1) / 2 * w.toNat := by
            rw [show (4294967295 : BitVec 64).toNat = 4294967295 from rfl,
              show (1 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt hin1_lt64,
              Nat.pow_one, Nat.mod_eq_of_lt hprod2_lt64] at hc
            exact hc
          exact hJ () m ⟨hmem, Or.inr (fun ⟨_, _, h32b, _⟩ => by omega)⟩
        · have hout32 : (in_len.toNat + 1) / 2 * w.toNat < 2 ^ 32 := by
            rw [show (4294967295 : BitVec 64).toNat = 4294967295 from rfl,
              show (1 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt hin1_lt64,
              Nat.pow_one, Nat.mod_eq_of_lt hprod2_lt64] at hc
            omega
          clear hc
          have htr1 : (BitVec.truncate 32 (BitVec.zeroExtend 64 in_len *
              BitVec.zeroExtend 64 w)).toNat = in_len.toNat * w.toNat := by
            rw [BitVec.truncate, BitVec.toNat_setWidth, hprod1, Nat.mod_eq_of_lt hin32]
          have htr2 : (BitVec.truncate 32 (((BitVec.zeroExtend 64 in_len + 1#64) >>> 1) *
              BitVec.zeroExtend 64 w)).toNat = (in_len.toNat + 1) / 2 * w.toNat := by
            rw [BitVec.truncate, BitVec.toNat_setWidth, hprod2, Nat.mod_eq_of_lt hout32]
          c0_hstraight
          c0_hcall hΓ_ok
          refine ⟨hdr, _, opMem_to_hdr hmem, ?_⟩
          dsimp only
          c0_hsplit
          · have hok1 := hc; clear hc
            rw [Nat.mod_eq_of_lt hprod1_lt64, Nat.mod_eq_of_lt hin32] at hok1
            c0_hstraight
            c0_hcall hΓ_ok
            refine ⟨hdr, _, opMem_to_hdr hmem, ?_⟩
            dsimp only
            c0_hsplit
            · have hok2 := hc; clear hc
              rw [show (1 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt hin1_lt64,
                Nat.pow_one, Nat.mod_eq_of_lt hprod2_lt64, Nat.mod_eq_of_lt hout32] at hok2
              have hlencap : hdr.lits_len.toNat ≤ hdr.lits_cap.toNat := hok1.1
              have hptr : (0 < in_len.toNat * w.toNat ∨
                  0 < (in_len.toNat + 1) / 2 * w.toNat) → hdr.lits_ptr ≠ 0#64 := fun h => by
                rcases h with h1 | h2
                · exact hok1.2.1 h1
                · exact hok2.2.1 h2
              have hin : in_off.toNat + in_len.toNat * w.toNat ≤ hdr.lits_len.toNat := by omega
              have hout : out_off.toNat + (in_len.toNat + 1) / 2 * w.toNat ≤
                  hdr.lits_len.toNat := by omega
              obtain ⟨hwf_in, hdisj⟩ := hwf ho hlencap hin32 hout32 (fun h1 => hptr (Or.inl h1))
                (fun h2 => hptr (Or.inr h2)) hin hout
              c0_hstraight
              have hout64 : ((BitVec.zeroExtend 64 in_len + 1#64) >>> 1) =
                  BitVec.ofNat 64 ((in_len.toNat + 1) / 2) := by
                apply BitVec.eq_of_toNat_eq; rw [hdiv64, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt (by have := in_len.isLt; omega)]
              exact bv_cpop_layer_loop_wp Γ hΓ_add hinv ho rfl hlencap hcaplen hptr hout64
                hin32 hout32 hin hout hwf_in hdisj hmem hpost
            · have hno2 := hc; clear hc
              rw [show (1 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt hin1_lt64,
                Nat.pow_one, Nat.mod_eq_of_lt hprod2_lt64, Nat.mod_eq_of_lt hout32] at hno2
              c0_hfast_nogrp
              exact hJ () m ⟨hmem, Or.inr (fun ⟨hl, _, _, _, hp2, _, hb⟩ =>
                hno2 ⟨hl, hp2, by omega⟩)⟩
          · have hno1 := hc; clear hc
            rw [Nat.mod_eq_of_lt hprod1_lt64, Nat.mod_eq_of_lt hin32] at hno1
            c0_hfast_nogrp
            exact hJ () m ⟨hmem, Or.inr (fun ⟨hl, _, _, hp1, _, ha, _⟩ =>
              hno1 ⟨hl, hp1, by omega⟩)⟩

/-! ## `bv_blast_cpop` -/

private theorem bv_cpop_body_high_wp (Γ : Env)
    (hΓ_rel : Γ.Has "bv_lits_release" bvLitsReleaseSpec)
    (hΓ_mark : Γ.Has "bv_lits_mark" bvLitsMarkSpec)
    (hΓ_alloc : Γ.Has "bv_lits_alloc" bvLitsAllocSpec)
    (hΓ_layer : Γ.Has "bv_blast_cpop_layer" bvBlastCpopLayerSpec)
    {h : Val i64} {a_off w mark0 out_off : BitVec 32} {ld : Val i64}
    {hdr hdr1 : BVHdrState} {g : Aig} {aw : List (BitVec 64)} {ht lp : List (BitVec 32)}
    {R : Mem 64 → Prop} {m1 : Mem 64} {Q : Post [i32]} {X : XPost}
    (hinv : AigInv hdr g aw ht) (hinv1 : AigInv hdr1 g aw ht)
    (hld : ld = hdr.lits_ptr) (ho : hdr.oom = 0#32) (ho1 : hdr1.oom = 0#32)
    (hw1 : 1 < w.toNat) (hmark0 : mark0 = hdr.lits_len) (hout_eq : out_off = hdr.lits_len)
    (hf01 : hdr.DcBlastFrame hdr1) (haig01 : hdr1.aig_len = hdr.aig_len)
    (hl1_eq : hdr1.lits_len = hdr.lits_len + w)
    (hl1_nat : hdr1.lits_len.toNat = hdr.lits_len.toNat + w.toNat)
    (hlencap : hdr.lits_len.toNat ≤ hdr.lits_cap.toNat) (hcaplen : hdr.lits_cap.toNat ≤ lp.length)
    (hl1_cap : hdr1.lits_len.toNat ≤ hdr1.lits_cap.toNat)
    (haw_ok : a_off.toNat + w.toNat ≤ hdr.lits_len.toNat)
    (hwf_a : SliceLitsWf hdr1 lp a_off.toNat w.toNat)
    (hm1 : (bvHdrMem h hdr1 ⋆ array64 hdr1.aig_ptr aw ⋆
      array (t := i32) hdr1.ht_ptr ht ⋆ array (t := i32) hdr1.lits_ptr lp ⋆ R) m1)
    (hpost : ∀ ret hdr' g' aw' ht' lp' m',
      hdr.DcBlastFrame hdr' → g ≤ g' → g'.nodes.size ≤ g.nodes.size + 9 * w.toNat * w.toNat →
      AigInv hdr' g' aw' ht' → lp'.length = lp.length →
      (∀ p, p < hdr.lits_len.toNat → lp'.getD p 0#32 = lp.getD p 0#32) →
      (hdr.oom ≠ 0#32 → hdr'.oom ≠ 0#32) →
      (hdr.oom = 0#32 → hdr.lits_len.toNat ≤ hdr.lits_cap.toNat →
        (0 < w.toNat → hdr.lits_ptr ≠ 0#64) → a_off.toNat + w.toNat ≤ hdr.lits_len.toNat →
        w.toNat * w.toNat < 2 ^ 32 → (w.toNat + 1) / 2 * w.toNat < 2 ^ 32 →
        (w.toNat + if w.toNat ≤ 1 then 0 else w.toNat * w.toNat + (w.toNat + 1) / 2 * w.toNat) ≤
          hdr.lits_cap.toNat - hdr.lits_len.toNat →
        g.A + 1 + g.nodes.size + 9 * w.toNat * w.toNat ≤ hdr.aig_cap.toNat →
        g.nodes.size + 9 * w.toNat * w.toNat ≤ bvMaxGates → hdr'.oom = 0#32) →
      (hdr'.oom ≠ 0#32 → ret = 4294967295#32 ∧ hdr.lits_len.toNat ≤ hdr'.lits_len.toNat ∧
        (w.toNat * w.toNat < 2 ^ 32 → (w.toNat + 1) / 2 * w.toNat < 2 ^ 32 →
          hdr'.lits_len = hdr.lits_len)) →
      (hdr'.oom = 0#32 → ret = hdr.lits_len ∧ hdr'.lits_len = hdr.lits_len + w ∧
        hdr'.lits_len.toNat ≤ hdr'.lits_cap.toNat ∧
        SliceLitsWf hdr' lp' ret.toNat w.toNat ∧
        ∀ ρ, sliceVal g' ρ lp' ret.toNat w.toNat =
          (sliceVal g ρ lp a_off.toNat w.toNat).cpop) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aw' ⋆
        array (t := i32) hdr'.ht_ptr ht' ⋆ array (t := i32) hdr'.lits_ptr lp' ⋆ R) m' →
      Q (ret, ()) m') :
    wp Γ Q X (
      Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var w)) fun p_11 =>
      Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var w)) fun p_12 =>
      Expr.let_ (op2 (OpCode.mul i64) (Arg.var p_11.fst) (Arg.var p_12.fst)) fun p_13 =>
      Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var w)) fun p_14 =>
      Expr.let_ (op2 (OpCode.add i64) (Arg.var p_14.fst) (Arg.imm 1#64)) fun p_15 =>
      Expr.let_ (op1 (OpCode.sext 32 64) (Arg.imm 1#32)) fun p_16 =>
      Expr.let_ (op2 (OpCode.lshr i64) (Arg.var p_15.fst) (Arg.var p_16.fst)) fun p_17 =>
      Expr.let_ (op1 (OpCode.zext 32 64) (Arg.var w)) fun p_18 =>
      Expr.let_ (op2 (OpCode.mul i64) (Arg.var p_17.fst) (Arg.var p_18.fst)) fun p_19 =>
      Expr.group
        (fun _Js => Blocks.cons
          (fun _ : Tup Val [] =>
            Expr.let_ (op2 (OpCode.add i64) (Arg.var h) (Arg.imm 120#64)) fun p_21 =>
            Expr.store (Arg.imm (t := i32) 1#32) (Arg.var p_21.fst)
              (Expr.call (as := [i64, i32]) (bs := []) "bv_lits_release"
                (Arg.var h, Arg.var mark0, ()) fun _ => Expr.ret (Arg.imm 4294967295#32, ())))
          Blocks.nil)
        (fun Js =>
          Expr.let_ (op2 (OpCode.cmp CmpOp.ugt i64 Ty.bool (by decide))
            (Arg.var p_13.fst) (Arg.imm 4294967295#64)) fun p_20 =>
          Expr.jnz (Arg.var p_20.fst) (Expr.jump Js.fst ())
            (Expr.let_ (op2 (OpCode.cmp CmpOp.ugt i64 Ty.bool (by decide))
              (Arg.var p_19.fst) (Arg.imm 4294967295#64)) fun p_21 =>
            Expr.jnz (Arg.var p_21.fst) (Expr.jump Js.fst ())
              (Expr.call (as := [i64]) (bs := [i32]) "bv_lits_mark" (Arg.var h, ()) fun p_22 =>
              Expr.let_ (op1 (OpCode.trunc 64 32) (Arg.var p_13.fst)) fun p_23 =>
              Expr.call (as := [i64, i32]) (bs := [i32]) "bv_lits_alloc"
                (Arg.var h, Arg.var p_23.fst, ()) fun p_24 =>
              Expr.let_ (op2 (OpCode.add i64) (Arg.var h) (Arg.imm 120#64)) fun p_25 =>
              Expr.load i32 (Arg.var p_25.fst) fun ld_1 =>
              Expr.let_ (op2 (OpCode.cmp CmpOp.ne i32 Ty.bool (by decide))
                (Arg.var ld_1) (Arg.imm 0#32)) fun p_26 =>
              Expr.jnz (Arg.var p_26.fst)
                (Expr.call (as := [i64, i32]) (bs := []) "bv_lits_release"
                  (Arg.var h, Arg.var mark0, ()) fun _ => Expr.ret (Arg.imm 4294967295#32, ()))
                (Expr.let_ (op1 (OpCode.trunc 64 32) (Arg.var p_19.fst)) fun p_27 =>
                Expr.call (as := [i64, i32]) (bs := [i32]) "bv_lits_alloc"
                  (Arg.var h, Arg.var p_27.fst, ()) fun p_28 =>
                Expr.let_ (op2 (OpCode.add i64) (Arg.var h) (Arg.imm 120#64)) fun p_29 =>
                Expr.load i32 (Arg.var p_29.fst) fun ld_2 =>
                Expr.let_ (op2 (OpCode.cmp CmpOp.ne i32 Ty.bool (by decide))
                  (Arg.var ld_2) (Arg.imm 0#32)) fun p_30 =>
                Expr.jnz (Arg.var p_30.fst)
                  (Expr.call (as := [i64, i32]) (bs := []) "bv_lits_release"
                    (Arg.var h, Arg.var mark0, ()) fun _ => Expr.ret (Arg.imm 4294967295#32, ()))
                  (cpopInitLoopExpr a_off w p_24.fst ld (cpopHalveLoopExpr h out_off w p_24.fst
                    p_28.fst mark0 p_22.fst ld))))))) m1 := by
  subst hld
  have hw64 : (BitVec.zeroExtend 64 w).toNat = w.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt]; have := w.isLt; omega
  have hw1_64 : w.toNat + 1 < 2 ^ 64 := by have := w.isLt; omega
  have hw2_lt64 : w.toNat * w.toNat < 2 ^ 64 :=
    Nat.lt_of_lt_of_eq (Nat.mul_lt_mul_of_lt_of_lt w.isLt w.isLt) rfl
  have hwh_lt64 : (w.toNat + 1) / 2 * w.toNat < 2 ^ 64 := by
    have := w.isLt
    have hhalf : (w.toNat + 1) / 2 < 2 ^ 32 := by omega
    exact Nat.lt_of_lt_of_eq (Nat.mul_lt_mul_of_lt_of_lt hhalf w.isLt) rfl
  have hw2_64 : (BitVec.zeroExtend 64 w * BitVec.zeroExtend 64 w).toNat = w.toNat * w.toNat := by
    rw [BitVec.toNat_mul, hw64, Nat.mod_eq_of_lt hw2_lt64]
  have hdiv64 : ((BitVec.zeroExtend 64 w + 1#64) >>> 1).toNat = (w.toNat + 1) / 2 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, hw64,
      show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt hw1_64,
      Nat.shiftRight_eq_div_pow, Nat.pow_one]
  have hwh_64 : (((BitVec.zeroExtend 64 w + 1#64) >>> 1) * BitVec.zeroExtend 64 w).toNat =
      (w.toNat + 1) / 2 * w.toNat := by
    rw [BitVec.toNat_mul, hdiv64, hw64, Nat.mod_eq_of_lt hwh_lt64]
  let FailP : Unit → Mem 64 → Prop := fun _ ml =>
    (bvHdrMem h hdr1 ⋆ array64 hdr1.aig_ptr aw ⋆
      array (t := i32) hdr1.ht_ptr ht ⋆ array (t := i32) hdr1.lits_ptr lp ⋆ R) ml ∧
    ¬ (w.toNat * w.toNat < 2 ^ 32 ∧ (w.toNat + 1) / 2 * w.toNat < 2 ^ 32)
  c0_hstraight
  apply wp_join_state0 FailP
  · intro _ _ ml ⟨hml, hnot⟩
    simp only [Std.ExtHashMap.sep_assoc] at hml
    c0_hfast_nogrp
    c0_hcall hΓ_rel
    have hmark0_le : mark0.toNat ≤ hdr1.lits_len.toNat := by rw [hmark0]; omega
    refine ⟨{ hdr1 with oom := 1#32 }, _,
      opMem_to_hdr (by simpa only [← Std.ExtHashMap.sep_assoc, ofNat_1_32] using hm),
      fun m'' hm'' => ?_⟩
    dsimp only
    simp only [hmark0_le, ↓reduceIte] at hm''
    let hdr' : BVHdrState := { hdr1 with lits_len := mark0, oom := 1#32 }
    have hoom' : hdr'.oom ≠ 0#32 := by dsimp [hdr']; decide
    have hf0' : hdr.DcBlastFrame hdr' := hf01.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    c0_hfast_nogrp
    refine hpost 4294967295#32 hdr' g aw ht lp m'' hf0' (Aig.extends_rfl g) (by omega)
      (aigInv_with_lits_len_oom hinv1 mark0 1#32) rfl (fun _ _ => rfl) (fun _ => hoom')
      (fun _ _ _ _ hw2 hwh _ _ _ => absurd ⟨hw2, hwh⟩ hnot)
      (fun _ => ⟨rfl, by dsimp [hdr']; rw [hmark0]; omega,
        fun hw2 hwh => absurd ⟨hw2, hwh⟩ hnot⟩)
      (fun hz => absurd hz hoom') (by simpa only [← Std.ExtHashMap.sep_assoc] using hm'')
  · intro J hJ
    c0_hsplit
    · c0_hfast_nogrp
      have hgt : 4294967295 < w.toNat * w.toNat := by
        rw [Nat.mod_eq_of_lt hw2_lt64, Nat.mod_eq_of_lt (by omega : 4294967295 < 2 ^ 64)] at hc
        exact hc
      exact hJ () m1 ⟨hm1, fun ⟨h1, _⟩ => by omega⟩
    · have hw2_32 : w.toNat * w.toNat < 2 ^ 32 := by
        rw [Nat.mod_eq_of_lt hw2_lt64, Nat.mod_eq_of_lt (by omega : 4294967295 < 2 ^ 64)] at hc
        omega
      clear hc
      c0_hsplit
      · c0_hfast_nogrp
        have hgt : 4294967295 < (w.toNat + 1) / 2 * w.toNat := by
          rw [Nat.mod_eq_of_lt hw1_64, Nat.pow_one, Nat.mod_eq_of_lt hwh_lt64,
            Nat.mod_eq_of_lt (by omega : 4294967295 < 2 ^ 64)] at hc
          exact hc
        exact hJ () m1 ⟨hm1, fun ⟨_, h2⟩ => by omega⟩
      · have hwh_32 : (w.toNat + 1) / 2 * w.toNat < 2 ^ 32 := by
          rw [Nat.mod_eq_of_lt hw1_64, Nat.pow_one, Nat.mod_eq_of_lt hwh_lt64,
            Nat.mod_eq_of_lt (by omega : 4294967295 < 2 ^ 64)] at hc
          omega
        clear hc
        have htr2 : (BitVec.setWidth 32 (BitVec.setWidth 64 w *
            BitVec.setWidth 64 w)).toNat = w.toNat * w.toNat := by
          rw [BitVec.toNat_setWidth, show BitVec.setWidth 64 w = BitVec.zeroExtend 64 w from rfl,
            hw2_64, Nat.mod_eq_of_lt hw2_32]
        have htrh : (BitVec.setWidth 32 (((BitVec.setWidth 64 w + 1#64) >>> 1) *
            BitVec.setWidth 64 w)).toNat = (w.toNat + 1) / 2 * w.toNat := by
          rw [BitVec.toNat_setWidth, show BitVec.setWidth 64 w = BitVec.zeroExtend 64 w from rfl,
            hwh_64, Nat.mod_eq_of_lt hwh_32]
        c0_hcall hΓ_mark
        refine ⟨hdr1, _, opMem_to_hdr hm1, ?_⟩
        dsimp only
        c0_hstraight
        c0_hcall hΓ_alloc
        refine ⟨hdr1, _, opMem_to_hdr hm1, ?_⟩
        dsimp only
        rw [htr2]
        by_cases hfit2 : hdr1.oom = 0#32 ∧ hdr1.lits_len.toNat ≤ hdr1.lits_cap.toNat ∧
            w.toNat * w.toNat ≤ hdr1.lits_cap.toNat - hdr1.lits_len.toNat
        · simp only [hfit2]
          intro m2 hm2
          let buf0 := hdr1.lits_len
          let hdr2 : BVHdrState := {
            hdr1 with
            lits_len := (hdr1.lits_len +
              BitVec.setWidth 32 (BitVec.setWidth 64 w * BitVec.setWidth 64 w)),
            oom := 0#32 }
          have hl2_nat : hdr2.lits_len.toNat = hdr1.lits_len.toNat + w.toNat * w.toNat := by
            dsimp [hdr2]
            rw [htr2, Nat.mod_eq_of_lt (by have := hdr1.lits_cap.isLt; omega)]
          have hl2_cap : hdr2.lits_len.toNat ≤ hdr2.lits_cap.toNat := by
            dsimp [hdr2]; omega
          have hf02 : hdr.DcBlastFrame hdr2 := hf01.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
            rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          have hm2' : (bvHdrMem h hdr2 ⋆ array64 hdr2.aig_ptr aw ⋆
              array (t := i32) hdr2.ht_ptr ht ⋆ array (t := i32) hdr2.lits_ptr lp ⋆ R) m2 := by
            simpa only [← Std.ExtHashMap.sep_assoc, hdr2, hf01.aig_ptr, hf01.ht_ptr,
              hf01.lits_ptr] using hm2
          simp only [Std.ExtHashMap.sep_assoc] at hm2
          c0_hfast_nogrp
          · exfalso; simp at ‹_›
          · c0_hcall hΓ_alloc
            refine ⟨hdr2, _, opMem_to_hdr hm2', ?_⟩
            dsimp only
            rw [htrh]
            by_cases hfit3 : hdr2.oom = 0#32 ∧ hdr2.lits_len.toNat ≤ hdr2.lits_cap.toNat ∧
                (w.toNat + 1) / 2 * w.toNat ≤ hdr2.lits_cap.toNat - hdr2.lits_len.toNat
            · simp only [hfit3]
              intro m3 hm3
              let buf1 := hdr2.lits_len
              let hdr3 : BVHdrState := {
                hdr2 with
                lits_len := (hdr2.lits_len + BitVec.setWidth 32
                  (((BitVec.setWidth 64 w + 1#64) >>> 1) * BitVec.setWidth 64 w)),
                oom := 0#32 }
              have hl3_nat : hdr3.lits_len.toNat =
                  hdr2.lits_len.toNat + (w.toNat + 1) / 2 * w.toNat := by
                dsimp [hdr3]
                rw [htrh, Nat.mod_eq_of_lt (by have := hdr2.lits_cap.isLt; omega)]
              have hf03 : hdr.DcBlastFrame hdr3 := hf02.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
              have hinv3 : AigInv hdr3 g aw ht := aigInv_of_dcBlastFrame hinv hf03 haig01
              have hm3' : (bvHdrMem h hdr3 ⋆ array64 hdr3.aig_ptr aw ⋆
                  array (t := i32) hdr3.ht_ptr ht ⋆ array (t := i32) hdr3.lits_ptr lp ⋆ R) m3 := by
                simpa only [← Std.ExtHashMap.sep_assoc, hdr3, hf02.aig_ptr, hf02.ht_ptr,
                  hf02.lits_ptr] using hm3
              simp only [Std.ExtHashMap.sep_assoc] at hm3
              c0_hfast_nogrp
              · exfalso; simp at ‹_›
              · have hwf_a3 : SliceLitsWf hdr3 lp a_off.toNat w.toNat :=
                  ⟨by omega, fun j hj => by
                    have h := hwf_a.2 j hj
                    dsimp [hdr3, hdr2]
                    simpa using h⟩
                apply bv_cpop_init_loop_wp hinv3 (by rw [hf03.lits_ptr]) hw1 hw2_32
                  (by omega) (by omega) (by dsimp [hdr3]; omega)
                  (by rw [hf03.lits_cap]; exact hcaplen) hwf_a3 hm3'
                intro lpInit m4 hlenInit hpresInit hwfInit hsumInit hm4
                have hagreeOrig : ∀ p, p < hdr.lits_len.toNat →
                    lpInit.getD p 0#32 = lp.getD p 0#32 :=
                  fun p hp => hpresInit p (Or.inl (by omega))
                apply bv_cpop_halve_loop_wp hΓ_layer hΓ_rel hinv3 (by rw [hf03.lits_ptr]) rfl
                  hw1 hw2_32 hwh_32 hmark0 (by rw [hl1_eq]) hout_eq (by rw [hout_eq]; omega)
                  (by omega) (by omega) (by dsimp [hdr3]; omega)
                  (by rw [hf03.lits_cap]; exact hcaplen) hlenInit hagreeOrig hwfInit hf03 hm4
                intro ret hdr' g' aw' ht' lp' m' hf' hg' hsz' hinv' hlen' hpres' hok' hoom'
                  hbound' hm'
                have hf_tot : hdr.DcBlastFrame hdr' := hf03.trans hf'
                have hsz_tot : g'.nodes.size ≤ g.nodes.size + 9 * w.toNat * w.toNat := by
                  have := mul_w_sub_one_le w.toNat; omega
                exact hpost ret hdr' g' aw' ht' lp' m' hf_tot hg' hsz_tot hinv' hlen' hpres'
                  (fun hne => absurd ho hne)
                  (fun _ _ hptr _ _ _ _ haig hgmax => by
                    apply hbound' hptr
                    · have := mul_w_sub_one_le w.toNat; omega
                    · have := mul_w_sub_one_le w.toNat; omega)
                  (fun hne => by
                    let h := hoom' hne
                    rw [h.2]
                    exact ⟨h.1, Nat.le_refl _, fun _ _ => rfl⟩)
                  (fun hz => by
                    obtain ⟨hr, hl, hc, hwf', hval'⟩ := hok' hz
                    refine ⟨hr, hl, hc, ?_, ?_⟩
                    · rw [hr, ← hout_eq]; exact hwf'
                    · intro ρ; rw [hr, ← hout_eq, hval' ρ, hsumInit ρ])
                  hm'
            · simp only [hfit3, ↓reduceIte]
              intro m3 hm3
              c0_hfast_nogrp
              · c0_hcall hΓ_rel
                have hmark0_le : mark0.toNat ≤ hdr2.lits_len.toNat := by rw [hmark0]; omega
                refine ⟨{ hdr2 with oom := 1#32 }, _,
                  opMem_to_hdr (by
                    simpa only [← Std.ExtHashMap.sep_assoc, hf02.aig_ptr, hf02.ht_ptr,
                      hf02.lits_ptr, show hdr2.oom = 0#32 from rfl, ne_eq, not_true_eq_false,
                      ↓reduceIte] using hm3), fun m'' hm'' => ?_⟩
                dsimp only
                simp only [hmark0_le, ↓reduceIte] at hm''
                let hdr' : BVHdrState := { hdr2 with lits_len := mark0, oom := 1#32 }
                have hoom' : hdr'.oom ≠ 0#32 := by dsimp [hdr']; decide
                have hf' : hdr.DcBlastFrame hdr' := hf02.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                  rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
                c0_hfast_nogrp
                refine hpost 4294967295#32 hdr' g aw ht lp m'' hf' (Aig.extends_rfl g) (by omega)
                  (aigInv_with_lits_len_oom (aigInv_of_dcBlastFrame hinv hf02 haig01) mark0 1#32)
                  rfl (fun _ _ => rfl) (fun _ => hoom')
                  (fun _ _ _ _ _ _ hcap _ _ => by
                    exfalso; apply hfit3
                    refine ⟨rfl, hl2_cap, ?_⟩
                    have hle1 : ¬ w.toNat ≤ 1 := by omega
                    simp only [hle1, ↓reduceIte] at hcap
                    rw [hf02.lits_cap]; omega)
                  (fun _ => ⟨rfl, by dsimp [hdr']; rw [hmark0]; omega, fun _ _ => hmark0⟩)
                  (fun hz => absurd hz hoom')
                  (by simpa only [← Std.ExtHashMap.sep_assoc] using hm'')
              · exfalso; simp [hdr2] at ‹_›
        · simp only [hfit2, ↓reduceIte]
          intro m2 hm2
          c0_hfast_nogrp
          · c0_hcall hΓ_rel
            have hmark0_le : mark0.toNat ≤ hdr1.lits_len.toNat := by rw [hmark0]; omega
            refine ⟨{ hdr1 with oom := 1#32 }, _,
              opMem_to_hdr (by
                simpa only [← Std.ExtHashMap.sep_assoc, hf01.aig_ptr, hf01.ht_ptr,
                  hf01.lits_ptr, ho1, ne_eq, not_true_eq_false, ↓reduceIte] using hm2),
              fun m'' hm'' => ?_⟩
            dsimp only
            simp only [hmark0_le, ↓reduceIte] at hm''
            let hdr' : BVHdrState := { hdr1 with lits_len := mark0, oom := 1#32 }
            have hoom' : hdr'.oom ≠ 0#32 := by dsimp [hdr']; decide
            have hf' : hdr.DcBlastFrame hdr' := hf01.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
              rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            c0_hfast_nogrp
            refine hpost 4294967295#32 hdr' g aw ht lp m'' hf' (Aig.extends_rfl g) (by omega)
              (aigInv_with_lits_len_oom hinv1 mark0 1#32) rfl (fun _ _ => rfl) (fun _ => hoom')
              (fun _ _ _ _ _ _ hcap _ _ => by
                exfalso; apply hfit2
                refine ⟨ho1, hl1_cap, ?_⟩
                have hle1 : ¬ w.toNat ≤ 1 := by omega
                simp only [hle1, ↓reduceIte] at hcap
                rw [hf01.lits_cap]; omega)
              (fun _ => ⟨rfl, by dsimp [hdr']; rw [hmark0]; omega, fun _ _ => hmark0⟩)
              (fun hz => absurd hz hoom') (by simpa only [← Std.ExtHashMap.sep_assoc] using hm'')
          · exfalso; simp [ho1] at ‹_›

public theorem bv_blast_cpop_wp (Γ : Env)
    (hΓ_ok : Γ.Has "bv_slice_ok" bvSliceOkSpec)
    (hΓ_mark : Γ.Has "bv_lits_mark" bvLitsMarkSpec)
    (hΓ_alloc : Γ.Has "bv_lits_alloc" bvLitsAllocSpec)
    (hΓ_rel : Γ.Has "bv_lits_release" bvLitsReleaseSpec)
    (hΓ_layer : Γ.Has "bv_blast_cpop_layer" bvBlastCpopLayerSpec) :
    bvBlastCpopSpec.Le (Func.wp Γ bv_blast_cpop_body) := by
  intro (h, a_off, w, ()) m Q X
  rintro ⟨hdr, g, aw, ht, lp, R, hinv, hcaplen, hwf, hm, hpost⟩
  dsimp only [Func.wp, bv_blast_cpop_body]
  let FailP0 : Unit → Mem 64 → Prop := fun _ ml =>
    (bvHdrMem h hdr ⋆ array64 hdr.aig_ptr aw ⋆
      array (t := i32) hdr.ht_ptr ht ⋆ array (t := i32) hdr.lits_ptr lp ⋆ R) ml ∧
    (hdr.oom ≠ 0#32 ∨ ¬ (hdr.lits_len.toNat ≤ hdr.lits_cap.toNat ∧
      (0 < w.toNat → hdr.lits_ptr ≠ 0#64) ∧ a_off.toNat + w.toNat ≤ hdr.lits_len.toNat))
  apply wp_join_state0 FailP0
  · intro _ _ ml ⟨hml, hbad⟩
    simp only [Std.ExtHashMap.sep_assoc] at hml
    c0_hfast_nogrp
    let hdr' : BVHdrState := { hdr with oom := 1#32 }
    have hoom' : hdr'.oom ≠ 0#32 := by dsimp [hdr']; decide
    refine hpost 4294967295#32 hdr' g aw ht lp m
      (hdr_with_oom_aigFrame (hdr := hdr) (noom := 1#32)).toDcBlastFrame
      (Aig.extends_rfl g) (by omega) (aigInv_with_lits_len_oom hinv hdr.lits_len 1#32) rfl
      (fun _ _ => rfl) (fun _ => hoom')
      (fun ho hl hp ha _ _ _ _ _ => by
        exfalso
        rcases hbad with hne | hnot
        · exact hne ho
        · exact hnot ⟨hl, hp, ha⟩)
      (fun _ => ⟨rfl, Nat.le_refl _, fun _ _ => rfl⟩) (fun hz => absurd hz hoom')
      (by simpa only [← Std.ExtHashMap.sep_assoc, ofNat_1_32, hdr'] using hm)
  · intro J hJ
    have hmr : (bvHdrMem h hdr ⋆ (array64 hdr.aig_ptr aw ⋆
        (array (t := i32) hdr.ht_ptr ht ⋆ (array (t := i32) hdr.lits_ptr lp ⋆ R)))) m := by
      simpa only [Std.ExtHashMap.sep_assoc] using hm
    c0_hfast_nogrp
    · exact hJ () m ⟨hm, Or.inl hc⟩
    · have ho : hdr.oom = 0#32 := hc
      clear hc
      c0_hcall hΓ_ok
      refine ⟨hdr, _, opMem_to_hdr hm, ?_⟩
      dsimp only
      c0_hsplit
      · have hok := hc; clear hc
        have hlencap : hdr.lits_len.toNat ≤ hdr.lits_cap.toNat := hok.1
        have hptr : 0 < w.toNat → hdr.lits_ptr ≠ 0#64 := hok.2.1
        have haw_ok : a_off.toNat + w.toNat ≤ hdr.lits_len.toNat := by omega
        have hwf_a := hwf ho hlencap hptr haw_ok
        c0_hcall hΓ_mark
        refine ⟨hdr, _, opMem_to_hdr hm, ?_⟩
        dsimp only
        c0_hcall hΓ_alloc
        refine ⟨hdr, _, opMem_to_hdr hm, ?_⟩
        dsimp only
        by_cases hfit1 : hdr.oom = 0#32 ∧ hdr.lits_len.toNat ≤ hdr.lits_cap.toNat ∧
            w.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat
        · simp only [hfit1]
          intro m1 hm1
          let out_off := hdr.lits_len
          let hdr1 : BVHdrState := { hdr with lits_len := hdr.lits_len + w, oom := 0#32 }
          have hl1_nat : hdr1.lits_len.toNat = hdr.lits_len.toNat + w.toNat := by
            dsimp [hdr1]
            rw [Nat.mod_eq_of_lt (by have := hdr.lits_cap.isLt; omega)]
          have hl1_cap : hdr1.lits_len.toNat ≤ hdr1.lits_cap.toNat := by dsimp [hdr1]; omega
          have hf01 : hdr.DcBlastFrame hdr1 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
            rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          have hinv1 : AigInv hdr1 g aw ht := aigInv_of_dcBlastFrame hinv hf01 rfl
          have hm1' : (bvHdrMem h hdr1 ⋆ array64 hdr1.aig_ptr aw ⋆
              array (t := i32) hdr1.ht_ptr ht ⋆ array (t := i32) hdr1.lits_ptr lp ⋆ R) m1 := by
            simpa only [← Std.ExtHashMap.sep_assoc, hdr1] using hm1
          simp only [Std.ExtHashMap.sep_assoc] at hm1
          c0_hsplit
          · exfalso; exact absurd (by assumption : ¬ 0#32 = 0#32) (by decide)
          · clear hc
            c0_hsplit
            · have hw0 : w = 0#32 := hc; clear hc; subst hw0
              c0_hfast_nogrp
              refine hpost hdr.lits_len hdr1 g aw ht lp m1 hf01 (Aig.extends_rfl g) (by omega)
                hinv1 rfl (fun _ _ => rfl) (fun hne => absurd ho hne)
                (fun _ _ _ _ _ _ _ _ _ => rfl) (fun hne => absurd rfl hne)
                (fun _ => ⟨rfl, rfl, hl1_cap,
                  ⟨by dsimp [hdr1]; omega, fun _ hj => False.elim (Nat.not_lt_zero _ hj)⟩,
                  fun ρ => by
                    apply BitVec.eq_of_getLsbD_eq
                    intro k hk
                    exact False.elim (Nat.not_lt_zero _ hk)⟩)
                hm1'
            · have hnw0 : w ≠ 0#32 := hc; clear hc
              have hw_pos : 0 < w.toNat := by
                have : w.toNat ≠ 0 := fun hz => hnw0 (BitVec.eq_of_toNat_eq hz)
                omega
              c0_hstraight
              c0_hsplit
              · have hw1_eq : w = 1#32 := hc; clear hc; subst hw1_eq
                have ha_lp : a_off.toNat < lp.length := by omega
                have ho_lp : out_off.toNat < lp.length := by dsimp [out_off]; omega
                have hsw_dst : (BitVec.setWidth 64 hdr.lits_len).toNat =
                    hdr.lits_len.toNat := by
                  have := hdr.lits_len.isLt
                  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                have hsw_src : (BitVec.setWidth 64 a_off).toNat = a_off.toNat := by
                  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := a_off.isLt; omega)]
                c0_hfast_nogrp
                let lp1 := lp.set hdr.lits_len.toNat lp[a_off.toNat]
                have hpres1 : ∀ p, p < hdr.lits_len.toNat → lp1.getD p 0#32 = lp.getD p 0#32 :=
                  fun p hp => by dsimp [lp1]; exact list_getD_set_ne lp 0#32 _ (by omega)
                have hget_a : lp1.getD hdr.lits_len.toNat 0#32 = lp.getD a_off.toNat 0#32 := by
                  dsimp [lp1]; rw [list_getD_set_self lp 0#32 _ (by omega)]
                  simp [List.getD_eq_getElem?_getD, ha_lp]
                have hwf1 : SliceLitsWf hdr1 lp1 hdr.lits_len.toNat 1 :=
                  ⟨by omega, fun j hj => by
                    obtain rfl : j = 0 := by omega
                    rw [Nat.add_zero, hget_a]; simpa using hwf_a.2 0 (by omega)⟩
                have hm_raw : (array (t := i32) hdr.lits_ptr
                    (lp.set (BitVec.setWidth 64 hdr.lits_len).toNat
                      lp[(BitVec.setWidth 64 a_off).toNat]) ⋆
                    (bvHdrMem h hdr1 ⋆ (array64 hdr1.aig_ptr aw ⋆
                      (array (t := i32) hdr1.ht_ptr ht ⋆ (R ⋆ Std.ExtHashMap.emp))))) m := hm
                have hm_out : (bvHdrMem h hdr1 ⋆ array64 hdr1.aig_ptr aw ⋆
                    array (t := i32) hdr1.ht_ptr ht ⋆ array (t := i32) hdr1.lits_ptr lp1 ⋆ R)
                    m := by
                  refine opMem_of_lits ?_
                  simpa only [Std.ExtHashMap.sep_emp, ← Std.ExtHashMap.sep_assoc,
                    hsw_dst, hsw_src] using hm_raw
                refine hpost hdr.lits_len hdr1 g aw ht lp1 m hf01 (Aig.extends_rfl g) (by omega)
                  hinv1 (by simp [lp1]) hpres1 (fun hne => absurd ho hne)
                  (fun _ _ _ _ _ _ _ _ _ => rfl) (fun hne => absurd rfl hne)
                  (fun _ => ⟨rfl, rfl, hl1_cap, hwf1, fun ρ => by
                    have hval_eq : sliceVal g ρ lp1 hdr.lits_len.toNat 1 =
                        sliceVal g ρ lp a_off.toNat 1 := by
                      apply BitVec.eq_of_getLsbD_eq; intro k hk
                      obtain rfl : k = 0 := by omega
                      rw [sliceVal_getLsbD (by omega), sliceVal_getLsbD (by omega),
                        Nat.add_zero, Nat.add_zero, hget_a]
                    rw [show (1#32).toNat = 1 from rfl, hval_eq, cpop_w1]⟩)
                  hm_out
              · have hnw1 : w ≠ 1#32 := hc; clear hc
                have hw1_gt : 1 < w.toNat := by
                  have : w.toNat ≠ 1 := fun hz => hnw1 (BitVec.eq_of_toNat_eq
                    (by simpa using hz))
                  omega
                have hwf_a1 : SliceLitsWf hdr1 lp a_off.toNat w.toNat :=
                  ⟨by omega, fun j hj => by simpa using hwf_a.2 j hj⟩
                exact bv_cpop_body_high_wp Γ hΓ_rel hΓ_mark hΓ_alloc hΓ_layer hinv hinv1 rfl ho
                  rfl hw1_gt rfl rfl hf01 rfl rfl hl1_nat hlencap hcaplen hl1_cap haw_ok hwf_a1
                  hm1' hpost
        · simp only [hfit1]
          intro m1 hm1
          simp only [Std.ExtHashMap.sep_assoc] at hm1
          simp [ho] at hm1
          c0_hsplit
          · c0_hfast_nogrp
            let hdr' : BVHdrState := { hdr with oom := 1#32 }
            have hoom' : hdr'.oom ≠ 0#32 := by dsimp [hdr']; decide
            have hf' : hdr.DcBlastFrame hdr' := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
              rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            refine hpost 4294967295#32 hdr' g aw ht lp m1 hf' (Aig.extends_rfl g) (by omega)
              (aigInv_with_lits_len_oom hinv hdr.lits_len 1#32) rfl (fun _ _ => rfl)
              (fun hne => absurd ho hne)
              (fun _ _ _ _ _ _ hcap _ _ => by exfalso; apply hfit1; refine ⟨ho, hlencap, by omega⟩)
              (fun _ => ⟨rfl, Nat.le_refl _, fun _ _ => rfl⟩) (fun hz => absurd hz hoom')
              (by simpa only [← Std.ExtHashMap.sep_assoc, hdr'] using hm1)
          · exfalso; exact absurd (by assumption : 1#32 = 0) (by decide)
      · have hno := hc; clear hc
        c0_hfast_nogrp
        exact hJ () m ⟨hm, Or.inr (fun ⟨h1, h2, h3⟩ => hno ⟨h1, h2, by omega⟩)⟩

end

end LeanQbe.T.Examples.Bitblast.Proof.OpsDivCpop
