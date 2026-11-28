/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Proof.Driver0Base
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0StepAttr
meta import LeanQbe.T.Logic.C0StepAttr
import Kraken.Separation

/-!
# ARiSCA Truth-Table Sim & Dense Canonicalization (`Arisca.Proof.Driver0`)

Re-exports all `7` contracts and first `5` WP proofs from `Driver0Base`, and supplies
`XPost`-polymorphic WP proofs for `ar_dcanon` (`ar_dcanon_wp`) and `ar_ttsim` (`ar_ttsim_wp`).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Arisca.Proof

open Std
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Arisca (Aig xmask xmask_bit)
open LeanQbe.T.Examples.Arisca.Src
open LeanQbe.T.Examples.Arisca.Src.Driver

public section

private abbrev DcanonRpad (s : ArCtxState) (gsy0 : List (BitVec 32)) (R : Mem 64 → Prop) :
    Mem 64 → Prop :=
  region (s.gsy + BitVec.ofNat 64 (4 * gsy0.length))
    (align8 (4 * gsy0.length) - 4 * gsy0.length) ⋆ R

private abbrev DcanonPost (cx dPtr : Val i64) (s : ArCtxState) (d : List (BitVec 64))
    (gsy0 : List (BitVec 32)) (gcl0 gch0 : List (BitVec 64))
    (R : Mem 64 → Prop) (Q : Post [i32]) : Prop :=
  ∀ (k : BitVec 32) (gsy' : List (BitVec 32)) (gcl' gch' : List (BitVec 64)) (m' : Mem 64),
    k.toNat ≤ 16 → gsy'.length = gsy0.length →
    gcl'.length = gcl0.length → gch'.length = gch0.length →
    (∀ i < k.toNat, MonoSliceOk gsy' (5 * i) 80 ∧ (gsy'.getD (5 * i) 0#32).toNat ≤ 4 ∧
      ∀ sym ∈ symListAt gsy' (5 * i), ∃ j < 4, sym = (s.g_vs.getD j 0#32).toNat) →
    (∀ i < k.toNat, MonoSorted gsy' (5 * i)) →
    (∀ σ : Nat → Bool, polyEval s.n_out.toNat σ gsy' gsyMOff gcl' gch' k.toNat =
        denseEvalNOut s.n_out.toNat σ s.g_vs d) →
    (arCtxMem cx s ⋆ array64 dPtr d ⋆ arrayPad i32 s.gsy gsy' ⋆
      array64 s.gcl gcl' ⋆ array64 s.gch gch' ⋆ R) m' → Q (k, ⟨⟩) m'

/-! ## 4B. WP Proof: `ar_dcanon` -/
private def dcanonP23 (cx tPtr : Val i64) (n : Val i32) : Expr Val Cont [i32] :=
  match ar_dcanon_body Val Cont (cx, cx, ()) with
  | @Expr.let_ _ _ _ [.bits 64] _ k1 => match k1 (cx, ()) with
    | @Expr.load _ _ _ (.bits 64) _ k2 => match k2 tPtr with
      | @Expr.group _ _ _ [[.bits 32, .bits 32]] bs _ => match bs (fun _ _ => False, ()) with
        | .cons b _ => match b (n, 0#32, ()) with
          | @Expr.let_ _ _ _ [.bool] _ k3 => match k3 (false, ()) with
            | .jnz _ _ f => f
            | _ => .ret (Arg.imm 0, ())
          | _ => .ret (Arg.imm 0, ())
        | _ => .ret (Arg.imm 0, ())
      | _ => .ret (Arg.imm 0, ())
    | _ => .ret (Arg.imm 0, ())
  | _ => .ret (Arg.imm 0, ())
private def evalSimple : {rs : List Ty} → Op Val rs → Option (Tup Val rs)
  | [.bits 64], ⟨.sext 32 64, (a, ())⟩ => some (BitVec.signExtend 64 a.val, ())
  | [.bits 64], ⟨.zext 32 64, (a, ())⟩ => some (BitVec.setWidth 64 a.val, ())
  | [.bits 64], ⟨.add (.bits 64), (a, b, ())⟩ => some (a.val + b.val, ())
  | [.bits 64], ⟨.mul (.bits 64), (a, b, ())⟩ => some (a.val * b.val, ())
  | [.bits 32], ⟨.add (.bits 32), (a, b, ())⟩ => some (a.val + b.val, ())
  | [.bits 32], ⟨.sub (.bits 32), (a, b, ())⟩ => some (a.val - b.val, ())
  | [.bits 32], ⟨.mul (.bits 32), (a, b, ())⟩ => some (a.val * b.val, ())
  | _, _ => none
private def skipToJc (gclPtr tl gchPtr th : Val i64) :
    Nat → Expr Val Cont [i32] → Expr Val Cont [i32]
  | n, .let_ op k =>
    match evalSimple op with | some r => skipToJc gclPtr tl gchPtr th n (k r) | none => .hlt
  | 0, .load (.bits 64) _ k => skipToJc gclPtr tl gchPtr th 1 (k gclPtr)
  | 1, .load (.bits 64) _ k => skipToJc gclPtr tl gchPtr th 2 (k tl)
  | 2, .load (.bits 64) _ k => skipToJc gclPtr tl gchPtr th 3 (k gchPtr)
  | 3, .load (.bits 64) _ k => skipToJc gclPtr tl gchPtr th 4 (k th)
  | _, e => e
private def dcanonP2J (cx gsyPtr gclPtr gchPtr : Val i64) (nV iV kV : Val i32)
    (tl th : Val i64) (Jp2 : Cont [i32]) : Expr Val Cont [i32] :=
  match dcanonP23 cx gsyPtr nV with
  | @Expr.group _ _ _ [[.bits 32]] bs2 _ => match bs2 (Jp2, ()) with
    | .cons b2 _ => match b2 (iV, ()) with
      | @Expr.let_ _ _ _ [.bool] _ kc => match kc (false, ()) with
        | .jnz _ ti _ => match skipToJc gclPtr tl gchPtr th 0 ti with
          | @Expr.group _ _ _ [[.bits 32]] bsc _ => match bsc (fun _ _ => False, ()) with
            | .cons bc _ => match bc (kV, ()) with
              | @Expr.let_ _ _ _ [.bool] _ k => match k (false, ()) with
                | .jnz _ _ fc => fc
                | _ => .ret (Arg.imm 0, ())
              | _ => .ret (Arg.imm 0, ())
            | _ => .ret (Arg.imm 0, ())
          | _ => .ret (Arg.imm 0, ())
        | _ => .ret (Arg.imm 0, ())
      | _ => .ret (Arg.imm 0, ())
    | _ => .ret (Arg.imm 0, ())
  | _ => .ret (Arg.imm 0, ())
private def dcanonP3 (cx tPtr : Val i64) (n : Val i32) : Expr Val Cont [i32] :=
  match dcanonP23 cx tPtr n with
  | @Expr.group _ _ _ [[.bits 32]] bs _ => match bs (fun _ _ => False, ()) with
    | .cons b _ => match b (n, ()) with
      | @Expr.let_ _ _ _ [.bool] _ k => match k (false, ()) with
        | .jnz _ _ f => f
        | _ => .ret (Arg.imm 0, ())
      | _ => .ret (Arg.imm 0, ())
    | _ => .ret (Arg.imm 0, ())
  | _ => .ret (Arg.imm 0, ())
private theorem ar_dcanon_p3 (Γ : LeanQbe.T.Env)
    (hCadd : ∀ xs m Q X, arCaddSpec xs m Q X →
      Γ "ar_cadd" [i64, i64, i64, i64, i64] [i64, i64] xs m Q X)
    (hMcmp : ∀ xs m Q X, arMcmpSliceSpec xs m Q X → Γ "ar_mcmp" [i64, i64] [i32] xs m Q X)
    {cx dPtr : Val i64} {nV : Val i32} {s : ArCtxState} {d gcl0 gch0 gcl2 gch2 : List (BitVec 64)}
    {gsy0 gsy2 : List (BitVec 32)} {R Rpad : Mem 64 → Prop}
    {Q : Post [i32]} {X : XPost} {m2 : Mem 64} (hRpad : Rpad = DcanonRpad s gsy0 R)
    (hmasks : MasksOk s.n_out.toNat s.mlo s.mhi)
    (hgsy_len : 85 ≤ gsy0.length) (hgcl_len : 16 ≤ gcl0.length) (hgch_len : 16 ≤ gch0.length)
    (hgsy2 : gsy2.length = gsy0.length)
    (hgcl2 : gcl2.length = gcl0.length) (hgch2 : gch2.length = gch0.length)
    (hinv2 : DcanonTermInv s gsy2 nV.toNat) (heval2 : ∀ σ : Nat → Bool,
      polyEval s.n_out.toNat σ gsy2 gsyMOff gcl2 gch2 nV.toNat =
        denseEvalNOut s.n_out.toNat σ s.g_vs d)
    (hm2 : (arCtxMem cx s ⋆ array64 dPtr d ⋆ array (t := i32) s.gsy gsy2 ⋆
      array64 s.gcl gcl2 ⋆ array64 s.gch gch2 ⋆ Rpad) m2)
    (hQ : DcanonPost cx dPtr s d gsy0 gcl0 gch0 R Q) :
    wp Γ Q X (dcanonP3 cx s.gsy nV) m2 := by
  unfold dcanonP3 dcanonP23
  refine wp_loop_group (fun rem3 ⟨iV3, kV, ⟨⟩⟩ m3 =>
      rem3 = nV.toNat - iV3.toNat ∧ ∃ gsy3 gcl3 gch3,
        Phase3IInv s gsy0 gsy2 gsy3 gcl2 gcl3 gch2 gch3 nV.toNat kV.toNat iV3.toNat ∧
        (arCtxMem cx s ⋆ array64 dPtr d ⋆ array (t := i32) s.gsy gsy3 ⋆
          array64 s.gcl gcl3 ⋆ array64 s.gch gch3 ⋆ Rpad) m3) ?_ ?_
  · intro Jp3 rem3 ⟨iV3, kV, ⟨⟩⟩ m3 hrecp3 ⟨_, gsy3, gcl3, gch3, hp3i, hm3⟩
    have hki := hp3i.1; have hin3 := hp3i.2.1; have hgsy3 := hp3i.2.2.1
    have hgcl3 := hp3i.2.2.2.1; have hgch3 := hp3i.2.2.2.2.1
    have htail3 := hp3i.2.2.2.2.2.2.1; have hn16 := hinv2.1
    c0_hsteps_nogrp
    · have hi_lt : iV3.toNat < nV.toNat := hc
      have hip1 := bv32_add1_toNat (by omega : iV3.toNat + 1 < 2 ^ 32); c0_hsteps_nogrp
      refine wp_loop_group (fun remj ⟨lV, hV, jV, ⟨⟩⟩ mj =>
          iV3.toNat + 1 ≤ jV.toNat ∧ jV.toNat ≤ nV.toNat ∧ remj = nV.toNat - jV.toNat ∧
          mj = m3 ∧ (∀ dlt < jV.toNat - iV3.toNat,
            symListAt gsy2 (5 * (iV3.toNat + dlt)) = symListAt gsy2 (5 * iV3.toNat)) ∧
          coeff128 s.n_out.toNat lV hV = (List.range (jV.toNat - iV3.toNat)).foldl
            (fun acc dlt => acc + coeff128 s.n_out.toNat
              (gcl2.getD (iV3.toNat + dlt) 0#64) (gch2.getD (iV3.toNat + dlt) 0#64))
            0#(s.n_out.toNat)) ?_ ?_
      · intro Jj remj ⟨lV, hV, jV, ⟨⟩⟩ mj hrecj ⟨hij, hjn, _, hmj_eq, hsymj, hlhj⟩; subst mj
        refine wp_join0 (fun mj' => mj' = m3) (fun _ mj' hmj' => by
            subst mj'
            refine wp_join_group (fun ⟨kN, ⟨⟩⟩ mk' => ∃ gsy_k gcl_k gch_k,
                Phase3IInv s gsy0 gsy2 gsy_k gcl2 gcl_k gch2 gch_k nV.toNat kN.toNat jV.toNat ∧
                (arCtxMem cx s ⋆ array64 dPtr d ⋆ array (t := i32) s.gsy gsy_k ⋆
                  array64 s.gcl gcl_k ⋆ array64 s.gch gch_k ⋆ Rpad) mk')
              (fun _ ⟨kN, ⟨⟩⟩ mk' ⟨gsy_k, gcl_k, gch_k, hpn, hmk'⟩ => by
                c0_hsteps; exact hrecp3 (nV.toNat - jV.toNat) (jV, kN, ⟨⟩) mk' (by omega)
                  ⟨rfl, gsy_k, gcl_k, gch_k, hpn, hmk'⟩)
              (fun Jkn hJkn => by
                refine wp_join0 (fun mk' => mk' = m3 ∧ (lV ≠ 0#64 ∨ hV ≠ 0#64))
                  (fun _ mk' ⟨hmk', _⟩ => by
                    subst mk'; c0_hsteps_nogrp
                    refine wp_loop_group (fun remq ⟨qV, ⟨⟩⟩ mq => remq = 5 - qV.toNat ∧
                        ∃ gsy_q, Copy5Inv gsy3 gsy_q (5 * kV.toNat) (5 * iV3.toNat) qV.toNat ∧
                        (arCtxMem cx s ⋆ array64 dPtr d ⋆ array (t := i32) s.gsy gsy_q ⋆
                          array64 s.gcl gcl3 ⋆ array64 s.gch gch3 ⋆ Rpad) mq) ?_ ?_
                    · intro Jq remq ⟨qV, ⟨⟩⟩ mq hrecq ⟨_, gsy_q, hcpq, hmq⟩
                      have hq_le := hcpq.1; have hgl_q := hcpq.2.1
                      c0_hsteps_nogrp
                      · have hq5 : qV.toNat < 5 := hc; clear hc
                        have hqp1 := bv32_add1_toNat (by omega : qV.toNat + 1 < 2 ^ 32)
                        have h5k := bv32_mul5_toNat (by omega : 5 * kV.toNat < 2 ^ 32)
                        have h5i3 := bv32_mul5_toNat (by omega : 5 * iV3.toNat < 2 ^ 32)
                        have h5kq : (BitVec.setWidth 64 (5 * kV + qV)).toNat < gsy_q.length :=
                          bv64_sw_mul5_add_lt (by omega) hq5 (by omega)
                        c0_hsteps_nogrp
                        refine hrecq (5 - (qV + 1).toNat) (qV + 1, ⟨⟩) _ (by omega)
                          ⟨rfl, gsy_q.set (5 * kV.toNat + qV.toNat)
                            (gsy_q.getD (5 * iV3.toNat + qV.toNat) 0#32), ?_, ?_⟩
                        · rw [hqp1]; exact copy5Inv_step hcpq hq5 (by omega) (by omega)
                            (by rcases Nat.eq_or_lt_of_le hki with he | _
                                · exact Or.inl (by omega)
                                · exact Or.inr (Or.inl (by omega)))
                        · rw [set_eq_of_eq (j := 5 * kV.toNat + qV.toNat)
                              (w := gsy_q.getD (5 * iV3.toNat + qV.toNat) 0#32)
                              (bv64_sw_mul5_add_eq (by omega) hq5)
                              (getElem_eq_getD 0#32 (by rw [h5i3]; omega) (by rw [h5i3]))] at hm
                          c0_frame
                      · have hq5 : qV.toNat = 5 := by simp only [BitVec.reduceToNat] at hc; omega
                        rw [hq5] at hcpq
                        have hkp1 := bv32_add1_toNat (by omega : kV.toNat + 1 < 2 ^ 32); c0_hsteps
                        refine hJkn (kV + 1, ⟨⟩) _
                          ⟨gsy_q, gcl3.set kV.toNat lV, gch3.set kV.toNat hV, ?_, ?_⟩
                        · rw [hkp1]; exact phase3_step_nonzero hp3i hinv2 hij hjn hcpq
                            (by omega) (by omega) hsymj hlhj
                        · rw [set_eq_of_eq (j := kV.toNat) (w := hV) bv64_sw_toNat rfl,
                            set_eq_of_eq (j := kV.toNat) (w := lV) bv64_sw_toNat rfl] at hm
                          c0_frame
                    · intro Jq hJq; c0_hsteps
                      exact hJq 5 (0#32, ⟨⟩) m3 ⟨rfl, gsy3, copy5Inv_init gsy3 _ _, hm3⟩)
                  (fun Js hJs => by
                    c0_hsteps
                    · exact hJs m3 ⟨rfl, Or.inl hc⟩
                    · exact hJs m3 ⟨rfl, Or.inr hc⟩
                    · rw [‹lV = 0#64›, ‹hV = 0#64›, coeff128_zero] at hlhj
                      exact hJkn (kV, ⟨⟩) m3 ⟨gsy3, gcl3, gch3,
                        phase3_step_zero hp3i hinv2 hij hjn hsymj hlhj.symm, hm3⟩)))
          (fun Jex3 hJex3 => by
            c0_hsteps_nogrp
            · have hjn' : jV.toNat < nV.toNat := hc; clear hc
              have hjp1 := bv32_add1_toNat (by omega : jV.toNat + 1 < 2 ^ 32)
              have hsi_0 : (gsy3.getD (5 * iV3.toNat) 0#32).toNat ≤ 4 := by
                have := congrArg (fun x => x.getD 0 0#32) (htail3 iV3.toNat (by omega) (by omega)).1
                rw [slice5_getD _ _ 0 (by decide), slice5_getD _ _ 0 (by decide)] at this
                have ht0 : gsy3.getD (5 * iV3.toNat) 0#32 = gsy2.getD (5 * iV3.toNat) 0#32 := by
                  simpa only [Nat.add_zero] using this
                rw [ht0]; exact (hinv2.2.1 iV3.toNat hi_lt).2.1
              have hsj_0 : (gsy3.getD (5 * jV.toNat) 0#32).toNat ≤ 4 := by
                have := congrArg (fun x => x.getD 0 0#32) (htail3 jV.toNat (by omega) hjn').1
                rw [slice5_getD _ _ 0 (by decide), slice5_getD _ _ 0 (by decide)] at this
                have ht0 : gsy3.getD (5 * jV.toNat) 0#32 = gsy2.getD (5 * jV.toNat) 0#32 := by
                  simpa only [Nat.add_zero] using this
                rw [ht0]; exact (hinv2.2.1 jV.toNat hjn').2.1
              c0_hsteps_nogrp; dsimp only [Arg.val]; apply wp_call_of_spec
              refine ar_mcmp_gsy hMcmp (offA := 5 * jV.toNat) (offB := 5 * iV3.toNat)
                (base := s.gsy) (gsy := gsy3)
                (R := arCtxMem cx s ⋆ array64 dPtr d ⋆ array64 s.gcl gcl3 ⋆
                  array64 s.gch gch3 ⋆ Rpad)
                ?_ ?_ (by omega) (by omega) (Or.inr (by omega)) hsj_0 hsi_0
                (sep_cast hm3 (by ac_rfl)) fun r hr => ?_
              · dsimp only [Arg.val]; congr 1; apply BitVec.eq_of_toNat_eq
                rw [BitVec.toNat_mul, bv64_sw_toNat, bv32_mul5_toNat (by omega),
                  BitVec.toNat_ofNat, show (4 : BitVec 64).toNat = 4 from rfl,
                  Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
              · dsimp only [Arg.val]; congr 1; apply BitVec.eq_of_toNat_eq
                rw [BitVec.toNat_mul, bv64_sw_toNat, bv32_mul5_toNat (by omega),
                  BitVec.toNat_ofNat, show (4 : BitVec 64).toNat = 4 from rfl,
                  Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
              · c0_hsteps_nogrp
                · have hr0 : r = 0#32 := hc
                  have hsym_j : symListAt gsy2 (5 * jV.toNat) = symListAt gsy2 (5 * iV3.toNat) := by
                    have h3 := hr hr0
                    have hsj := symListAt_congr_slice5 (htail3 jV.toNat (by omega) hjn').1 hsj_0
                    have hsi := symListAt_congr_slice5
                      (htail3 iV3.toNat (by omega) (by omega)).1 hsi_0
                    rw [hsj, hsi] at h3; exact h3
                  clear hc; apply wp_call_of_spec; apply hCadd
                  refine ⟨s, array64 dPtr d ⋆ array (t := i32) s.gsy gsy3 ⋆
                      array64 s.gcl gcl3 ⋆ array64 s.gch gch3 ⋆ Rpad,
                    hmasks, sep_cast hm3 (by ac_rfl), fun l' h' hlh' => ?_⟩
                  c0_hsteps
                  refine hrecj (nV.toNat - (jV + 1).toNat) (l', h', jV + 1, ⟨⟩) m3
                    (by omega) ⟨by omega, by omega, rfl, rfl, fun dlt hdlt => ?_, ?_⟩
                  · rw [hjp1] at hdlt; have hdlt' : dlt < (jV.toNat - iV3.toNat) + 1 := by omega
                    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hdlt') with rfl | hlt
                    · simpa [show iV3.toNat + (jV.toNat - iV3.toNat) = jV.toNat by omega]
                        using hsym_j
                    · exact hsymj dlt (by omega)
                  · rw [hjp1, show jV.toNat + 1 - iV3.toNat = (jV.toNat - iV3.toNat) + 1 by omega,
                      List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
                      show iV3.toNat + (jV.toNat - iV3.toNat) = jV.toNat by omega,
                      ← hlhj, ← (htail3 jV.toNat (by omega) hjn').2.1,
                      ← (htail3 jV.toNat (by omega) hjn').2.2]
                    dsimp only [Arg.val] at hlh'
                    simpa only [bv64_sw_toNat,
                      d_getD_eq_getElem gcl3 0#64 (i := jV.toNat) (by omega),
                      d_getD_eq_getElem gch3 0#64 (i := jV.toNat) (by omega)] using hlh'
                · exact hJex3 m3 rfl
            · exact hJex3 m3 rfl)
      · intro Jj hJj; c0_hsteps
        simp only [bv64_sw_toNat, ← d_getD_eq_getElem gcl3 0#64 (i := iV3.toNat) (by omega),
          ← d_getD_eq_getElem gch3 0#64 (i := iV3.toNat) (by omega)]
        refine hJj (nV.toNat - (iV3 + 1).toNat)
          (gcl3.getD iV3.toNat 0#64, gch3.getD iV3.toNat 0#64, iV3 + 1, ⟨⟩) m3
          ⟨by omega, by omega, rfl, rfl, fun dlt hdlt => ?_, ?_⟩
        · rw [show dlt = 0 by omega, Nat.add_zero]
        · rw [hip1, show iV3.toNat + 1 - iV3.toNat = 1 by omega, List.range_one,
            List.foldl_cons, List.foldl_nil, BitVec.zero_add,
            (htail3 iV3.toNat (Nat.le_refl _) hi_lt).2.1,
            (htail3 iV3.toNat (Nat.le_refl _) hi_lt).2.2, Nat.add_zero]
    · have hin_eq : iV3.toNat = nV.toNat := by omega
      have hpe := hp3i.2.2.2.2.2.2.2
      simp only [hin_eq, Nat.sub_self, polyEvalRange_zero, BitVec.add_zero] at hpe; c0_hsteps
      have hm_pad : (arCtxMem cx s ⋆ array64 dPtr d ⋆ arrayPad i32 s.gsy gsy3 ⋆
          array64 s.gcl gcl3 ⋆ array64 s.gch gch3 ⋆ R) m3 := by
        have hm3' : (array (t := i32) s.gsy gsy3 ⋆
            region (s.gsy + BitVec.ofNat 64 (4 * gsy3.length))
              (align8 (4 * gsy3.length) - 4 * gsy3.length) ⋆
            (arCtxMem cx s ⋆ array64 dPtr d ⋆ array64 s.gcl gcl3 ⋆ array64 s.gch gch3 ⋆ R)) m3 := by
          rw [hRpad, DcanonRpad] at hm3; rw [hgsy3]; exact sep_cast hm3 (by ac_rfl)
        exact sep_cast (region_merge_pad_u32 hm3') (by ac_rfl)
      refine hQ kV gsy3 gcl3 gch3 m3 (by omega) hgsy3 (by omega) (by omega)
        hp3i.2.2.2.2.2.1.2.1 hp3i.2.2.2.2.2.1.2.2 (fun σ => ?_) hm_pad
      rw [hpe σ, heval2 σ]
  · intro Jp3 hJp3; c0_hsteps
    exact hJp3 nV.toNat (0#32, 0#32, ⟨⟩) m2 ⟨Nat.sub_zero _, gsy2, gcl2, gch2,
      ⟨Nat.zero_le _, Nat.zero_le _, hgsy2, rfl, rfl,
        ⟨Nat.zero_le _, fun _ hk => absurd hk (Nat.not_lt_zero _),
          fun _ hk => absurd hk (Nat.not_lt_zero _)⟩,
        fun _ _ _ => ⟨rfl, rfl, rfl⟩, fun σ => by simp [polyEval_zero]; rfl⟩, hm2⟩

private theorem ar_dcanon_p2_j (Γ : LeanQbe.T.Env)
    (hMcmp : ∀ xs m Q X, arMcmpSliceSpec xs m Q X → Γ "ar_mcmp" [i64, i64] [i32] xs m Q X)
    {cx dPtr : Val i64} {nV iV kV : Val i32} {tl th : BitVec 64} {s : ArCtxState}
    {d gcl0 gch0 gcl1 gch1 gcl2 gch2 : List (BitVec 64)} {gsy0 gsy1 gsy2 gsy_c : List (BitVec 32)}
    {Rpad : Mem 64 → Prop} {Q : Post [i32]} {X : XPost} {Jp2 : Cont [i32]} {mc : Mem 64}
    (hgsy_len : 85 ≤ gsy0.length) (hgcl_len : 16 ≤ gcl0.length) (hgch_len : 16 ≤ gch0.length)
    (hgsy1 : gsy1.length = gsy0.length)
    (hgcl1 : gcl1.length = gcl0.length) (hgch1 : gch1.length = gch0.length)
    (hp2i : Phase2IInv s gsy0 gsy1 gsy2 gcl1 gcl2 gch1 gch2 nV.toNat) (hi_n : iV.toNat < nV.toNat)
    (htl : tl = gcl2.getD iV.toNat 0#64) (hth : th = gch2.getD iV.toNat 0#64)
    (hcp : Copy5Inv gsy2 gsy_c 80 (5 * iV.toNat) kV.toNat) (hk5 : kV.toNat = 5)
    (hmc : (arCtxMem cx s ⋆ array64 dPtr d ⋆ array (t := i32) s.gsy gsy_c ⋆
      array64 s.gcl gcl2 ⋆ array64 s.gch gch2 ⋆ Rpad) mc)
    (hrecp2 : ∀ rem' (xs' : Tup Val [i32]) m', rem' < nV.toNat - iV.toNat → (match xs' with
      | (i', ⟨⟩) => (i'.toNat ≤ nV.toNat ∨ nV.toNat = 0 ∧ i'.toNat = 1) ∧
        rem' = nV.toNat - i'.toNat ∧
        ∃ gsy' gcl' gch', Phase2IInv s gsy0 gsy1 gsy' gcl1 gcl' gch1 gch' nV.toNat ∧
          (arCtxMem cx s ⋆ array64 dPtr d ⋆ array (t := i32) s.gsy gsy' ⋆
            array64 s.gcl gcl' ⋆ array64 s.gch gch' ⋆ Rpad) m') → Jp2 xs' m') :
    wp Γ Q X (dcanonP2J cx s.gsy s.gcl s.gch nV iV kV tl th Jp2) mc := by
  have hgsy2 := hp2i.1; have hgcl2 := hp2i.2.1; have hgch2 := hp2i.2.2.1
  have hn16 := hp2i.2.2.2.1.1
  have hi_gcl : iV.toNat < gcl2.length := by omega
  have hi_gch : iV.toNat < gch2.length := by omega
  unfold dcanonP2J dcanonP23
  refine wp_loop_group (fun remj ⟨_kV, jV, ⟨⟩⟩ mj => remj = jV.toNat ∧
      ∃ gsy_j gcl_j gch_j, Phase2JInv s gsy0 gsy2 gsy_j gcl2 gcl_j gch2 gch_j
        nV.toNat iV.toNat jV.toNat tl th ∧
      (arCtxMem cx s ⋆ array64 dPtr d ⋆ array (t := i32) s.gsy gsy_j ⋆
        array64 s.gcl gcl_j ⋆ array64 s.gch gch_j ⋆ Rpad) mj) ?_ ?_
  · intro Jj remj ⟨_kV, jV, ⟨⟩⟩ mj hrecj ⟨_, gsy_j, gcl_j, gch_j, hjinv, hmj⟩
    have hji := hjinv.1; have hgsy_j := hjinv.2.1
    have hgcl_j := hjinv.2.2.1; have hgch_j := hjinv.2.2.2.1
    refine wp_join0 (fun mj' =>
        (arCtxMem cx s ⋆ array64 dPtr d ⋆ array (t := i32) s.gsy gsy_j ⋆
          array64 s.gcl gcl_j ⋆ array64 s.gch gch_j ⋆ Rpad) mj')
      (fun _ mj' hmj' => by
        c0_hsteps_nogrp
        refine wp_loop_group (fun remf ⟨kV, ⟨⟩⟩ mf => remf = 5 - kV.toNat ∧ ∃ gsy_f,
            Copy5Inv gsy_j gsy_f (5 * jV.toNat) 80 kV.toNat ∧
            (arCtxMem cx s ⋆ array64 dPtr d ⋆ array (t := i32) s.gsy gsy_f ⋆
              array64 s.gcl gcl_j ⋆ array64 s.gch gch_j ⋆ Rpad) mf) ?_ ?_
        · intro Jf remf ⟨kV, ⟨⟩⟩ mf hrecf ⟨_, gsy_f, hcpf, hmf⟩
          have hk_le := hcpf.1; have hgl_f := hcpf.2.1
          c0_hsteps_nogrp
          · have hk5f : kV.toNat < 5 := hc
            have hkp1 := bv32_add1_toNat (by omega : kV.toNat + 1 < 2 ^ 32)
            have h5jk : (BitVec.setWidth 64 (5 * jV + kV)).toNat < gsy_f.length :=
              bv64_sw_mul5_add_lt (by omega) hk5f (by omega)
            have h80k :
                (BitVec.ofNat 64 80).toNat + (BitVec.setWidth 64 kV).toNat < gsy_f.length := by
              rw [BitVec.toNat_ofNat, bv64_sw_toNat, Nat.mod_eq_of_lt (by decide)]; omega
            c0_hsteps_nogrp
            refine hrecf (5 - (kV + 1).toNat) (kV + 1, ⟨⟩) _ (by omega)
              ⟨rfl, gsy_f.set (5 * jV.toNat + kV.toNat) (gsy_f.getD (80 + kV.toNat) 0#32), ?_, ?_⟩
            · rw [hkp1]
              exact copy5Inv_step hcpf hk5f (by omega) (by omega) (Or.inr (Or.inl (by omega)))
            · have h80k' : BitVec.toNat (80 : BitVec 64) + BitVec.toNat kV < gsy_f.length := by
                rw [show (80 : BitVec 64).toNat = 80 from rfl]; omega
              have hm1 : (arCtxMem cx s ⋆ array64 dPtr d ⋆
                  array (t := i32) s.gsy (gsy_f.set (BitVec.setWidth 64 (5 * jV + kV)).toNat
                    (gsy_f[BitVec.toNat (80 : BitVec 64) + BitVec.toNat kV]'h80k')) ⋆
                  array64 s.gcl gcl_j ⋆ array64 s.gch gch_j ⋆ Rpad) m := sep_cast hm (by ac_rfl)
              have hi1 : (BitVec.setWidth 64 (5 * jV + kV)).toNat = 5 * jV.toNat + kV.toNat :=
                bv64_sw_mul5_add_eq (by omega) hk5f
              have hv1 : gsy_f[BitVec.toNat (80 : BitVec 64) + BitVec.toNat kV]'h80k' =
                  gsy_f.getD (80 + kV.toNat) 0#32 :=
                getElem_eq_getD 0#32 h80k' (by rw [show (80 : BitVec 64).toNat = 80 from rfl])
              rwa [set_eq_of_eq hi1 hv1] at hm1
          · have hk5f : kV.toNat = 5 := by simp only [BitVec.reduceToNat] at hc; omega
            rw [hk5f] at hcpf; have hip1 := bv32_add1_toNat (by omega : iV.toNat + 1 < 2 ^ 32)
            c0_hsteps
            refine hrecp2 (nV.toNat - (iV + 1).toNat) (iV + 1, ⟨⟩) _ (by omega)
              ⟨Or.inl (by omega), rfl, _, _, _,
                phase2_finish_j hp2i hjinv hi_n hcpf (by omega) (by omega), ?_⟩
            rw [set_eq_of_eq (j := jV.toNat) (w := th) bv64_sw_toNat rfl,
              set_eq_of_eq (j := jV.toNat) (w := tl) bv64_sw_toNat rfl] at hm
            c0_frame
        · intro Jf hJf; c0_hsteps
          exact hJf 5 (0#32, ⟨⟩) mj' ⟨rfl, gsy_j, copy5Inv_init gsy_j _ _, hmj'⟩)
      (fun Jex2 hJex2 => by
        c0_hsteps_nogrp
        · have hj0 : 0 < jV.toNat := hc; have hjm1 := bv32_sub1_toNat hj0
          have h5jm1 : (5 * (jV - 1)).toNat = 5 * (jV.toNat - 1) := by
            rw [bv32_mul5_toNat (by omega), hjm1]
          c0_hsteps_nogrp; dsimp only [Arg.val]; apply wp_call_of_spec
          refine ar_mcmp_gsy hMcmp (offA := 5 * (jV.toNat - 1)) (offB := 80)
            (base := s.gsy) (gsy := gsy_j)
            (R := arCtxMem cx s ⋆ array64 dPtr d ⋆ array64 s.gcl gcl_j ⋆ array64 s.gch gch_j ⋆ Rpad)
            ?_ rfl (by omega) (by omega)
            (Or.inl (by omega)) (hjinv.2.2.2.2.2.2.1.2.1 (jV.toNat - 1) (by omega)).2.1
            hjinv.2.2.2.2.1 (sep_cast hmj (by ac_rfl)) fun r _ => ?_
          · dsimp only [Arg.val]; congr 1; apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_mul, bv64_sw_toNat, h5jm1, BitVec.toNat_ofNat,
              show (4 : BitVec 64).toNat = 4 from rfl, Nat.mod_eq_of_lt (by omega),
              Nat.mod_eq_of_lt (by omega)]; omega
          · c0_hsteps_nogrp
            · clear hc
              refine wp_loop_group (fun remm ⟨kV, ⟨⟩⟩ mm =>
                  remm = 5 - kV.toNat ∧ ∃ gsy_m,
                    Copy5Inv gsy_j gsy_m (5 * jV.toNat) (5 * (jV.toNat - 1)) kV.toNat ∧
                    (arCtxMem cx s ⋆ array64 dPtr d ⋆ array (t := i32) s.gsy gsy_m ⋆
                      array64 s.gcl gcl_j ⋆ array64 s.gch gch_j ⋆ Rpad) mm) ?_ ?_
              · intro Jm remm ⟨kV, ⟨⟩⟩ mm hrecm ⟨_, gsy_m, hcpm, hmm⟩
                have hk_le := hcpm.1; have hgl_m := hcpm.2.1
                c0_hsteps_nogrp
                · have hk5m : kV.toNat < 5 := hc
                  have hkp1 := bv32_add1_toNat (by omega : kV.toNat + 1 < 2 ^ 32)
                  have h5jk : (BitVec.setWidth 64 (5 * jV + kV)).toNat < gsy_m.length :=
                    bv64_sw_mul5_add_lt (by omega) hk5m (by omega)
                  c0_hsteps_nogrp
                  refine hrecm (5 - (kV + 1).toNat) (kV + 1, ⟨⟩) _ (by omega)
                    ⟨rfl, gsy_m.set (5 * jV.toNat + kV.toNat)
                      (gsy_m.getD (5 * (jV.toNat - 1) + kV.toNat) 0#32), ?_, ?_⟩
                  · rw [hkp1]; exact copy5Inv_step hcpm hk5m (by omega) (by omega)
                      (Or.inr (Or.inr (by omega)))
                  · rw [set_eq_of_eq (j := 5 * jV.toNat + kV.toNat)
                        (w := gsy_m.getD (5 * (jV.toNat - 1) + kV.toNat) 0#32)
                        (bv64_sw_mul5_add_eq (by omega) hk5m)
                        (getElem_eq_getD 0#32 (by rw [h5jm1]; omega) (by rw [h5jm1]))] at hm
                    c0_frame
                · have hk5m : kV.toNat = 5 := by simp only [BitVec.reduceToNat] at hc; omega
                  rw [hk5m] at hcpm; c0_hsteps
                  refine hrecj (jV - 1).toNat (kV, jV - 1, ⟨⟩) m (by omega)
                    ⟨rfl, gsy_m, gcl_j.set jV.toNat (gcl_j.getD (jV.toNat - 1) 0#64),
                      gch_j.set jV.toNat (gch_j.getD (jV.toNat - 1) 0#64), ?_, ?_⟩
                  · rw [hjm1]; exact phase2_step_j hj0 hjinv hi_n hcpm (by omega) (by omega)
                  · rw [set_eq_of_eq (j := jV.toNat) (w := gch_j.getD (jV.toNat - 1) 0#64)
                        bv64_sw_toNat
                        (getElem_eq_getD 0#64 (by rw [bv64_sw_toNat, hjm1]; omega)
                          (by rw [bv64_sw_toNat, hjm1])),
                      set_eq_of_eq (j := jV.toNat) (w := gcl_j.getD (jV.toNat - 1) 0#64)
                        bv64_sw_toNat
                        (getElem_eq_getD 0#64 (by rw [bv64_sw_toNat, hjm1]; omega)
                          (by rw [bv64_sw_toNat, hjm1]))] at hm
                    c0_frame
              · intro Jm hJm; c0_hsteps
                exact hJm 5 (0#32, ⟨⟩) mj ⟨rfl, gsy_j, copy5Inv_init gsy_j _ _, hmj⟩
            · exact hJex2 mj hmj
        · exact hJex2 mj hmj)
  · intro Jj hJj; c0_hsteps
    exact hJj iV.toNat (kV, iV, ⟨⟩) mc ⟨rfl, gsy_c, gcl2, gch2,
      htl ▸ hth ▸ phase2_start_j hi_n hp2i (hk5 ▸ hcp), hmc⟩

private theorem ar_dcanon_p2 (Γ : LeanQbe.T.Env)
    (hCadd : ∀ xs m Q X, arCaddSpec xs m Q X →
      Γ "ar_cadd" [i64, i64, i64, i64, i64] [i64, i64] xs m Q X)
    (hMcmp : ∀ xs m Q X, arMcmpSliceSpec xs m Q X → Γ "ar_mcmp" [i64, i64] [i32] xs m Q X)
    {cx dPtr : Val i64} {nV : Val i32} {s : ArCtxState} {d gcl0 gch0 gcl1 gch1 : List (BitVec 64)}
    {gsy0 gsy1 : List (BitVec 32)} {R Rpad : Mem 64 → Prop}
    {Q : Post [i32]} {X : XPost} {m1 : Mem 64} (hRpad : Rpad = DcanonRpad s gsy0 R)
    (hmasks : MasksOk s.n_out.toNat s.mlo s.mhi)
    (hgsy_len : 85 ≤ gsy0.length) (hgcl_len : 16 ≤ gcl0.length) (hgch_len : 16 ≤ gch0.length)
    (hpinv : Phase1MaskInv s d gsy0 gsy1 gcl0 gcl1 gch0 gch1 nV.toNat 16)
    (hm1 : (arCtxMem cx s ⋆ array64 dPtr d ⋆ array (t := i32) s.gsy gsy1 ⋆
      array64 s.gcl gcl1 ⋆ array64 s.gch gch1 ⋆ Rpad) m1)
    (hQ : DcanonPost cx dPtr s d gsy0 gcl0 gch0 R Q) :
    wp Γ Q X (dcanonP23 cx s.gsy nV) m1 := by
  have hgsy1 := hpinv.2.1; have hgcl1 := hpinv.2.2.1; have hgch1 := hpinv.2.2.2.1; unfold dcanonP23
  refine wp_loop_group (fun rem2 ⟨iV, ⟨⟩⟩ m2 =>
      (iV.toNat ≤ nV.toNat ∨ nV.toNat = 0 ∧ iV.toNat = 1) ∧ rem2 = nV.toNat - iV.toNat ∧
      ∃ gsy2 gcl2 gch2, Phase2IInv s gsy0 gsy1 gsy2 gcl1 gcl2 gch1 gch2 nV.toNat ∧
        (arCtxMem cx s ⋆ array64 dPtr d ⋆ array (t := i32) s.gsy gsy2 ⋆
          array64 s.gcl gcl2 ⋆ array64 s.gch gch2 ⋆ Rpad) m2) ?_ ?_
  · intro Jp2 rem2 ⟨iV, ⟨⟩⟩ m2 hrecp2 ⟨hi_b, _, gsy2, gcl2, gch2, hp2i, hm2⟩
    have hgsy2 := hp2i.1; have hgcl2 := hp2i.2.1; have hgch2 := hp2i.2.2.1
    have hn16 := hp2i.2.2.2.1.1
    c0_hsteps_nogrp
    · have hi_n : iV.toNat < nV.toNat := hc
      have h5i := bv32_mul5_toNat (by omega : 5 * iV.toNat < 2 ^ 32)
      have hi_gcl : iV.toNat < gcl2.length := by omega
      have hi_gch : iV.toNat < gch2.length := by omega
      have hi_gcl' : (BitVec.setWidth 64 iV).toNat < gcl2.length := by rw [bv64_sw_toNat]; omega
      have hi_gch' : (BitVec.setWidth 64 iV).toNat < gch2.length := by rw [bv64_sw_toNat]; omega
      c0_hsteps_nogrp
      let tl := gcl2[(BitVec.setWidth 64 iV).toNat]'hi_gcl'
      let th := gch2[(BitVec.setWidth 64 iV).toNat]'hi_gch'
      have htl_eq : tl = gcl2.getD iV.toNat 0#64 := getElem_eq_getD 0#64 hi_gcl' bv64_sw_toNat
      have hth_eq : th = gch2.getD iV.toNat 0#64 := getElem_eq_getD 0#64 hi_gch' bv64_sw_toNat
      refine wp_loop_group (fun remc ⟨kV, ⟨⟩⟩ mc => remc = 5 - kV.toNat ∧ ∃ gsy_c,
          Copy5Inv gsy2 gsy_c 80 (5 * iV.toNat) kV.toNat ∧
          (arCtxMem cx s ⋆ array64 dPtr d ⋆ array (t := i32) s.gsy gsy_c ⋆
            array64 s.gcl gcl2 ⋆ array64 s.gch gch2 ⋆ Rpad) mc) ?_ ?_
      · intro Jc remc ⟨kV, ⟨⟩⟩ mc hrecc ⟨_, gsy_c, hcp, hmc⟩
        have hk_le := hcp.1; have hgl_c := hcp.2.1
        c0_hsteps_nogrp
        · have hk5 : kV.toNat < 5 := hc
          have hkp1 := bv32_add1_toNat (by omega : kV.toNat + 1 < 2 ^ 32)
          have hsrc : (5 * iV).toNat + kV.toNat < gsy_c.length := by rw [h5i]; omega
          have h80k :
              (BitVec.ofNat 64 80).toNat + (BitVec.setWidth 64 kV).toNat < gsy_c.length := by
            rw [BitVec.toNat_ofNat, bv64_sw_toNat, Nat.mod_eq_of_lt (by decide)]; omega
          c0_hsteps_nogrp
          refine hrecc (5 - (kV + 1).toNat) (kV + 1, ⟨⟩) _ (by omega)
            ⟨rfl, gsy_c.set (80 + kV.toNat) (gsy_c.getD (5 * iV.toNat + kV.toNat) 0#32), ?_, ?_⟩
          · rw [hkp1]
            exact copy5Inv_step hcp hk5 (by omega) (by omega) (Or.inr (Or.inr (by omega)))
          · rw [set_eq_of_eq (j := 80 + kV.toNat) (w := gsy_c.getD (5 * iV.toNat + kV.toNat) 0#32)
                (by rw [BitVec.toNat_ofNat, bv64_sw_toNat, Nat.mod_eq_of_lt (by decide)])
                (getElem_eq_getD 0#32 (by rw [h5i]; omega) (by rw [h5i]))] at hm
            c0_frame
        · have hk5 : kV.toNat = 5 := by simp only [BitVec.reduceToNat] at hc; omega
          c0_hsteps_nogrp
          change wp Γ Q X (dcanonP2J cx s.gsy s.gcl s.gch nV iV kV tl th Jp2) mc
          exact ar_dcanon_p2_j Γ hMcmp hgsy_len hgcl_len hgch_len hgsy1 hgcl1 hgch1
            hp2i hi_n htl_eq hth_eq hcp hk5 hmc (fun r x m' h => hrecp2 r x m' (by omega))
      · intro Jc hJc; c0_hsteps; exact hJc 5 (0#32, ⟨⟩) m2 ⟨rfl, gsy2, copy5Inv_init gsy2 _ _, hm2⟩
    · have heval2 : ∀ σ : Nat → Bool, polyEval s.n_out.toNat σ gsy2 gsyMOff gcl2 gch2 nV.toNat =
          denseEvalNOut s.n_out.toNat σ s.g_vs d := fun σ => by
        rw [polyEval_eq_of_perm s.n_out.toNat σ gsy2 gsy1 gcl2 gch2 gcl1 gch1 nV.toNat hn16
          hp2i.2.2.2.2, hpinv.2.2.2.2.2 σ]; rfl
      change wp Γ Q X (dcanonP3 cx s.gsy nV) m2
      exact ar_dcanon_p3 Γ hCadd hMcmp hRpad hmasks hgsy_len hgcl_len hgch_len hgsy2
        (hgcl2.trans hgcl1) (hgch2.trans hgch1) hp2i.2.2.2.1 heval2 hm2 hQ
  · intro Jp2 hJp2; c0_hsteps
    refine hJp2 (nV.toNat - 1) (1#32, ⟨⟩) m1 ⟨?_, rfl, gsy1, gcl1, gch1,
      ⟨hgsy1, rfl, rfl, hpinv.2.2.2.2.1, List.Perm.refl _⟩, hm1⟩
    by_cases hn0 : nV.toNat = 0
    · exact Or.inr ⟨hn0, by decide⟩
    · exact Or.inl (by simp; omega)

theorem ar_dcanon_wp (Γ : LeanQbe.T.Env)
    (hCfrom : ∀ xs m Q X, arCfromSmallSpec xs m Q X →
      Γ "ar_cfrom_small" [i64, i64] [i64, i64] xs m Q X)
    (hCadd : ∀ xs m Q X, arCaddSpec xs m Q X →
      Γ "ar_cadd" [i64, i64, i64, i64, i64] [i64, i64] xs m Q X)
    (hMcmp : ∀ xs m Q X, arMcmpSliceSpec xs m Q X → Γ "ar_mcmp" [i64, i64] [i32] xs m Q X) :
    ∀ xs m Q X, arDcanonSpec xs m Q X → Func.wp Γ ar_dcanon_body xs m Q X := by
  rintro ⟨cx, dPtr, ⟨⟩⟩ m Q X
    ⟨s, d, gcl0, gch0, gsy0, R, hmasks, hd_len, hgsy_len, hgcl_len, hgch_len, hm, hQ⟩
  rw [arrayPad, SlabSeg.ofArrayAlign8, SlabSeg.ofArray] at hm
  dsimp only [Ty.bytes, Ty.size, Nat.reduceDiv, Nat.reduceAdd] at hm
  let Rpad : Mem 64 → Prop :=
    region (s.gsy + BitVec.ofNat 64 (4 * gsy0.length))
      (align8 (4 * gsy0.length) - 4 * gsy0.length) ⋆ R
  have hm0 : (arCtxMem cx s ⋆ array64 dPtr d ⋆ array (t := i32) s.gsy gsy0 ⋆
      array64 s.gcl gcl0 ⋆ array64 s.gch gch0 ⋆ Rpad) m := by
    simpa only [Rpad] using sep_cast hm (by ac_rfl)
  have hvs_len : s.g_vs.length = 4 := by
    have hm0' : (arCtxMem cx s ⋆ (array64 dPtr d ⋆ array (t := i32) s.gsy gsy0 ⋆
        array64 s.gcl gcl0 ⋆ array64 s.gch gch0 ⋆ Rpad)) m := sep_cast hm0 (by ac_rfl)
    unfold arCtxMem at hm0'
    exact (sep_pure_l (φ := ArCtxLengthsOk s) (P := fun m => (arCtxTree cx s).eval m)
      (R := array64 dPtr d ⋆ array (t := i32) s.gsy gsy0 ⋆
        array64 s.gcl gcl0 ⋆ array64 s.gch gch0 ⋆ Rpad) |>.mp hm0').1.g_vs
  c0_hsteps_nogrp
  refine wp_loop_group (fun rem ⟨nV, maskV, ⟨⟩⟩ m1 =>
      maskV.toNat ≤ 16 ∧ rem = 16 - maskV.toNat ∧
      ∃ gsy1 gcl1 gch1, Phase1MaskInv s d gsy0 gsy1 gcl0 gcl1 gch0 gch1 nV.toNat maskV.toNat ∧
        (arCtxMem cx s ⋆ array64 dPtr d ⋆ array (t := i32) s.gsy gsy1 ⋆
          array64 s.gcl gcl1 ⋆ array64 s.gch gch1 ⋆ Rpad) m1) ?_ ?_
  · intro J1 rem ⟨nV, maskV, ⟨⟩⟩ m1 hrec1 ⟨hmask_le, _, gsy1, gcl1, gch1, hpinv, hm1⟩
    have hn_le := hpinv.1; have hgsy1 := hpinv.2.1
    have hgcl1 := hpinv.2.2.1; have hgch1 := hpinv.2.2.2.1
    c0_hsteps_nogrp
    · have hmask16 : maskV.toNat < 16 := hc; clear hc
      refine wp_join_group (fun ⟨n2V, ⟨⟩⟩ m2 => ∃ gsy2 gcl2 gch2,
          Phase1MaskInv s d gsy0 gsy2 gcl0 gcl2 gch0 gch2 n2V.toNat (maskV.toNat + 1) ∧
          (arCtxMem cx s ⋆ array64 dPtr d ⋆ array (t := i32) s.gsy gsy2 ⋆
            array64 s.gcl gcl2 ⋆ array64 s.gch gch2 ⋆ Rpad) m2)
        (fun _ ⟨n2V, ⟨⟩⟩ m2 ⟨gsy2, gcl2, gch2, hpinv2, hm2⟩ => by
          c0_hsteps; have hmp1 := bv32_add1_toNat (by omega : maskV.toNat + 1 < 2 ^ 32)
          exact hrec1 (16 - (maskV + 1).toNat) (n2V, maskV + 1, ⟨⟩) m2 (by omega)
            ⟨by omega, rfl, gsy2, gcl2, gch2, by simpa [hmp1] using hpinv2, hm2⟩)
        (fun J2 hJ2 => by
          have hd_idx : maskV.toNat < d.length := by omega
          c0_hsteps_nogrp
          · clear hc; dsimp only [Arg.val]; apply wp_call_of_spec; apply hCfrom
            refine ⟨s, array64 dPtr d ⋆ array (t := i32) s.gsy gsy1 ⋆
                array64 s.gcl gcl1 ⋆ array64 s.gch gch1 ⋆ Rpad,
              hmasks, sep_cast hm1 (by ac_rfl), fun l h hlh => ?_⟩
            dsimp only [Arg.val] at hlh; simp only [bv64_sw_toNat] at hlh
            refine wp_join_group (fun ⟨n2V, ⟨⟩⟩ m2 => ∃ gsy2 gcl2 gch2,
                Phase1MaskInv s d gsy0 gsy2 gcl0 gcl2 gch0 gch2 n2V.toNat (maskV.toNat + 1) ∧
                (arCtxMem cx s ⋆ array64 dPtr d ⋆ array (t := i32) s.gsy gsy2 ⋆
                  array64 s.gcl gcl2 ⋆ array64 s.gch gch2 ⋆ Rpad) m2)
              (fun _ ⟨n2V, ⟨⟩⟩ m2 h => hJ2 (n2V, ⟨⟩) m2 h)
              (fun J2a hJ2a => by
                refine wp_join0 (fun m' => m' = m1 ∧ (l ≠ 0#64 ∨ h ≠ 0#64)) (fun _ m' ⟨hm', _⟩ => by
                    subst hm'; c0_hsteps_nogrp
                    refine wp_loop_group (fun rem ⟨lenV, jV, ⟨⟩⟩ mj =>
                        rem = 4 - jV.toNat ∧ ∃ gsy_j,
                          Phase1JInv s gsy0 gsy1 gsy_j nV.toNat maskV.toNat jV.toNat lenV.toNat ∧
                          (arCtxMem cx s ⋆ array64 dPtr d ⋆ array (t := i32) s.gsy gsy_j ⋆
                            array64 s.gcl gcl1 ⋆ array64 s.gch gch1 ⋆ Rpad) mj) ?_ ?_
                    · intro Jj rem ⟨lenV, jV, ⟨⟩⟩ mj hrecj ⟨_, gsy_j, hjinv, hmj⟩
                      have hlen_le := hjinv.2.1; have hgsy_j := hjinv.2.2.1
                      c0_hsteps_nogrp
                      · have hj4 : jV.toNat < 4 := hc; clear hc
                        refine wp_join_group (fun ⟨lenN, ⟨⟩⟩ mj' => ∃ gsy_n,
                            Phase1JInv s gsy0 gsy1 gsy_n nV.toNat maskV.toNat
                              (jV.toNat + 1) lenN.toNat ∧
                            (arCtxMem cx s ⋆ array64 dPtr d ⋆ array (t := i32) s.gsy gsy_n ⋆
                              array64 s.gcl gcl1 ⋆ array64 s.gch gch1 ⋆ Rpad) mj')
                          (fun _ ⟨lenN, ⟨⟩⟩ mj' ⟨gsy_n, hninv, hmj'⟩ => by
                            c0_hsteps
                            have hjp1 := bv32_add1_toNat (by omega : jV.toNat + 1 < 2 ^ 32)
                            exact hrecj (4 - (jV + 1).toNat) (lenN, jV + 1, ⟨⟩) mj' (by omega)
                              ⟨rfl, gsy_n, by simpa [hjp1] using hninv, hmj'⟩)
                          (fun Jjn hJjn => by
                            c0_hsteps_nogrp
                            · have hbit : maskV.toNat.testBit jV.toNat = true := by
                                rw [← bv32_shr_and1_ne0 maskV.toNat jV.toNat hmask16 hj4]
                                simpa [BitVec.ofNat_toNat] using hc
                              clear hc
                              have h5n := bv32_mul5_toNat (by omega : 5 * nV.toNat < 2 ^ 32)
                              c0_hsteps_nogrp
                              refine wp_loop_group (fun remq ⟨qV, ⟨⟩⟩ mq =>
                                  mq = mj ∧ qV.toNat ≤ lenV.toNat ∧ remq = qV.toNat ∧
                                  (∀ r, qV.toNat + 1 ≤ r → r ≤ lenV.toNat →
                                    (s.g_vs.getD jV.toNat 0#32).toNat <
                                      (gsy_j.getD (5 * nV.toNat + r) 0#32).toNat)) ?_ ?_
                              · intro Jq remq ⟨qV, ⟨⟩⟩ mq hrecq ⟨hmq, hq_le, _, hq_gt⟩; subst mq
                                refine wp_join0 (fun mq' => mq' = mj ∧
                                    (qV.toNat = 0 ∨
                                      (gsy_j.getD (5 * nV.toNat + qV.toNat) 0#32).toNat ≤
                                        (s.g_vs.getD jV.toNat 0#32).toNat))
                                  (fun _ mq' ⟨hmq', hq_le_x⟩ => by
                                    subst mq'
                                    refine wp_join_group (fun ⟨lenN, ⟨⟩⟩ mj' => ∃ gsy_n,
                                        Phase1JInv s gsy0 gsy1 gsy_n nV.toNat maskV.toNat
                                          (jV.toNat + 1) lenN.toNat ∧
                                        (arCtxMem cx s ⋆ array64 dPtr d ⋆
                                          array (t := i32) s.gsy gsy_n ⋆
                                          array64 s.gcl gcl1 ⋆ array64 s.gch gch1 ⋆ Rpad) mj')
                                      (fun _ ⟨lenN, ⟨⟩⟩ mj' h => hJjn (lenN, ⟨⟩) mj' h)
                                      (fun Jdup hJdup => by
                                        refine wp_join0 (fun mq' => mq' = mj ∧
                                            (qV.toNat = 0 ∨
                                              (gsy_j.getD (5 * nV.toNat + qV.toNat) 0#32).toNat <
                                                (s.g_vs.getD jV.toNat 0#32).toNat))
                                          (fun _ mq' ⟨hmq', hq_lt_x⟩ => by
                                            subst mq'; c0_hsteps_nogrp
                                            refine wp_loop_group (fun remk ⟨kV, ⟨⟩⟩ mk =>
                                                remk = kV.toNat - qV.toNat ∧ ∃ gsy_k,
                                                  Phase1KInv s gsy0 gsy1 gsy_j gsy_k
                                                    nV.toNat qV.toNat
                                                    lenV.toNat kV.toNat ∧
                                                  (arCtxMem cx s ⋆ array64 dPtr d ⋆
                                                    array (t := i32) s.gsy gsy_k ⋆
                                                    array64 s.gcl gcl1 ⋆ array64 s.gch gch1 ⋆ Rpad)
                                                    mk) ?_ ?_
                                            · intro Jk remk ⟨kV, ⟨⟩⟩ mk hreck ⟨_, gsy_k, hkinv, hmk⟩
                                              have hqk := hkinv.1; have hkl := hkinv.2.1
                                              have hgsy_k := hkinv.2.2.1
                                              c0_hsteps_nogrp
                                              · have hkgt : qV.toNat < kV.toNat := hc
                                                have hkp1 :=
                                                  bv32_add1_toNat (by omega : kV.toNat + 1 < 2 ^ 32)
                                                have hkm1 :=
                                                  bv32_sub1_toNat (by omega : 1 ≤ kV.toNat)
                                                have h5nr :=
                                                  bv32_mul5_r_toNat
                                                    (by omega : 5 * nV.toNat < 2 ^ 32)
                                                have hk_src :
                                                    (5 * nV).toNat + kV.toNat < gsy_k.length := by
                                                  rw [h5n]; omega
                                                have hk_dst : (5 * nV).toNat + (kV + 1).toNat <
                                                    gsy_k.length := by rw [h5n, hkp1]; omega
                                                c0_hsteps_nogrp
                                                refine hreck ((kV - 1).toNat - qV.toNat)
                                                  (kV - 1, ⟨⟩) _ (by omega)
                                                  ⟨rfl, gsy_k.set (5 * nV.toNat + kV.toNat + 1)
                                                    (gsy_k.getD (5 * nV.toNat + kV.toNat)
                                                      0#32), ?_, ?_⟩
                                                · rw [hkm1]; exact phase1KInv_step hkinv hkgt
                                                    (by omega) (by omega)
                                                · rw [set_eq_of_eq
                                                      (j := 5 * nV.toNat + kV.toNat + 1)
                                                      (w := gsy_k.getD
                                                        (5 * nV.toNat + kV.toNat) 0#32)
                                                      (by rw [hkp1, h5n]; omega)
                                                      (getElem_eq_getD 0#32 (by rw [h5n]; omega)
                                                        (by rw [h5n]))] at hm
                                                  c0_frame
                                              · have hkeq : kV.toNat = qV.toNat := by omega
                                                rw [hkeq] at hkinv
                                                have hqp1 :=
                                                  bv32_add1_toNat (by omega : qV.toNat + 1 < 2 ^ 32)
                                                have hlp1 :=
                                                  bv32_add1_toNat
                                                    (by omega : lenV.toNat + 1 < 2 ^ 32)
                                                have hdst : (5 * nV).toNat + (qV + 1).toNat <
                                                    gsy_k.length := by rw [h5n, hqp1]; omega
                                                c0_hsteps
                                                refine hJdup (lenV + 1, ⟨⟩) _
                                                  ⟨gsy_k.set (5 * nV.toNat + qV.toNat + 1)
                                                    (s.g_vs.getD jV.toNat 0#32), ?_, ?_⟩
                                                · rw [hlp1]
                                                  exact phase1KInv_done hjinv hkinv hj4 hbit
                                                    (by omega) hq_lt_x hq_gt
                                                · rw [set_eq_of_eq
                                                      (j := 5 * nV.toNat + qV.toNat + 1)
                                                      (w := s.g_vs.getD jV.toNat 0#32)
                                                      (by rw [hqp1, h5n]; omega)
                                                      (getElem_eq_getD 0#32 (by omega) rfl)] at hm
                                                  c0_frame
                                            · intro Jk hJk; c0_hsteps
                                              exact hJk (lenV.toNat - qV.toNat) (lenV, ⟨⟩) mj
                                                ⟨rfl, gsy_j, ⟨hq_le, Nat.le_refl _, hgsy_j,
                                                  hjinv.2.2.2.1, fun _ _ _ => rfl,
                                                  fun r hr1 hr2 => by omega⟩, hmj⟩)
                                          (fun Jndup hJndup => by
                                            by_cases hq0 : 0 < qV.toNat
                                            · have h5nr :=
                                                bv32_mul5_r_toNat (by omega : 5 * nV.toNat < 2 ^ 32)
                                              c0_hsteps_nogrp
                                              · have hmemq :
                                                  gsy_j.getD (5 * nV.toNat + qV.toNat) 0#32 =
                                                    s.g_vs.getD jV.toNat 0#32 := by
                                                  rw [d_getD_eq_getElem gsy_j 0#32 (by omega),
                                                    d_getD_eq_getElem s.g_vs 0#32 (by omega)]
                                                  simpa [h5nr, Nat.add_comm] using hc
                                                exact hJdup (lenV, ⟨⟩) mj
                                                  ⟨gsy_j, phase1JInv_dup hjinv hj4 hbit hq0 hq_le
                                                    hmemq, hmj⟩
                                              · refine hJndup mj ⟨rfl, Or.inr ?_⟩
                                                have hne :
                                                    gsy_j.getD (5 * nV.toNat + qV.toNat) 0#32 ≠
                                                    s.g_vs.getD jV.toNat 0#32 := by
                                                  intro he
                                                  rw [d_getD_eq_getElem gsy_j 0#32 (by omega),
                                                    d_getD_eq_getElem s.g_vs 0#32 (by omega)] at he
                                                  exact hc (by simpa [h5nr, Nat.add_comm] using he)
                                                rcases hq_le_x with h0 | hle
                                                · omega
                                                · exact Nat.lt_of_le_of_ne hle
                                                    (fun h => hne (BitVec.eq_of_toNat_eq h))
                                            · c0_hsteps_nogrp <;>
                                                exact hJndup mj ⟨rfl, Or.inl (by omega)⟩)))
                                  (fun Jwhile hJwhile => by
                                    by_cases hq0 : 0 < qV.toNat
                                    · have h5nr :=
                                        bv32_mul5_r_toNat (by omega : 5 * nV.toNat < 2 ^ 32)
                                      c0_hsteps_nogrp
                                      · have hqm1 := bv32_sub1_toNat hq0
                                        have hgt : (s.g_vs.getD jV.toNat 0#32).toNat <
                                            (gsy_j.getD (5 * nV.toNat + qV.toNat) 0#32).toNat := by
                                          rw [d_getD_eq_getElem gsy_j 0#32 (by omega),
                                            d_getD_eq_getElem s.g_vs 0#32 (by omega)]
                                          simpa [BitVec.lt_def, h5nr, Nat.add_comm] using hc
                                        exact hrecq (qV - 1).toNat (qV - 1, ⟨⟩) mj (by omega)
                                          ⟨rfl, by omega, rfl, fun r hr1 hr2 => by
                                            rw [hqm1] at hr1
                                            by_cases hrq : r = qV.toNat
                                            · subst hrq; exact hgt
                                            · exact hq_gt r (by omega) hr2⟩
                                      · have hnotlt :
                                            (gsy_j.getD (5 * nV.toNat + qV.toNat) 0#32).toNat ≤
                                              (s.g_vs.getD jV.toNat 0#32).toNat := by
                                          rw [d_getD_eq_getElem gsy_j 0#32 (by omega),
                                            d_getD_eq_getElem s.g_vs 0#32 (by omega)]
                                          have hnot : ¬ (s.g_vs[jV.toNat]'(by omega)).toNat <
                                              (gsy_j[5 * nV.toNat + qV.toNat]'(by omega)).toNat :=
                                                by
                                            simpa [BitVec.lt_def, h5nr, Nat.add_comm] using hc
                                          omega
                                        exact hJwhile mj ⟨rfl, Or.inr hnotlt⟩
                                    · c0_hsteps_nogrp <;> exact hJwhile mj ⟨rfl, Or.inl (by omega)⟩)
                              · intro Jq hJq; c0_hsteps
                                exact hJq lenV.toNat (lenV, ⟨⟩) mj
                                  ⟨rfl, Nat.le_refl _, rfl, fun r hr1 hr2 => by omega⟩
                            · have hnbit : maskV.toNat.testBit jV.toNat = false := by
                                cases hb0 : maskV.toNat.testBit jV.toNat
                                · rfl
                                · exfalso
                                  have hne :=
                                    (bv32_shr_and1_ne0 maskV.toNat jV.toNat hmask16 hj4).mpr hb0
                                  rw [BitVec.ofNat_toNat, BitVec.ofNat_toNat] at hne
                                  simp only [Nat.mod_eq_of_lt (by omega : jV.toNat < 32)] at hc
                                  exact hne hc
                              c0_hsteps
                              exact hJjn (lenV, ⟨⟩) mj
                                ⟨gsy_j, phase1JInv_skip hjinv hj4 hnbit, hmj⟩)
                      · have hjeq : jV.toNat = 4 := by
                          have := hjinv.1; simp only [BitVec.reduceToNat] at hc; omega
                        rw [hjeq] at hjinv hlen_le
                        have h5n0 : (5 * nV).toNat + (BitVec.ofNat 64 0 * 4).toNat / 4 <
                            gsy_j.length := by
                          rw [bv32_mul5_toNat (by omega),
                            show (BitVec.ofNat 64 0 * 4).toNat = 0 from rfl,
                            Nat.zero_div, Nat.add_zero]; omega
                        have h5n0_mod : (BitVec.ofNat 64 0 * 4).toNat % 4 = 0 := rfl
                        have hgcl_lt : nV.toNat < gcl1.length := by omega
                        have hgch_lt : nV.toNat < gch1.length := by omega
                        c0_hsteps_nogrp
                        have hnp1 := bv32_add1_toNat (by omega : nV.toNat + 1 < 2 ^ 32)
                        refine hJ2a (nV + 1, ⟨⟩) _
                          ⟨gsy_j.set (5 * nV.toNat) lenV, gcl1.set nV.toNat l, gch1.set nV.toNat h,
                            ?_, ?_⟩
                        · rw [hnp1]
                          refine phase1MaskInv_step_nonzero hpinv hmask16 hjinv (by omega)
                            (by omega) (by omega) ?_
                          rw [d_getD_eq_getElem d 0#64 hd_idx]; exact hlh
                        · have h5n' : (5 * nV).toNat + (BitVec.ofNat 64 0 * 4).toNat / 4 =
                              5 * nV.toNat := by
                            rw [bv32_mul5_toNat (by omega),
                            show (BitVec.ofNat 64 0 * 4).toNat = 0 from rfl,
                              Nat.zero_div, Nat.add_zero]
                          rw [bv64_sw_toNat, h5n', Std.ExtHashMap.sep_emp] at hm
                          exact sep_cast hm (by ac_rfl)
                    · intro Jj hJj; c0_hsteps
                      exact hJj 4 (0#32, 0#32, ⟨⟩) m' ⟨rfl, gsy1, ⟨by decide, by decide, hgsy1,
                        fun _ _ => rfl, fun z => by
                          simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.not_lt_zero,
                            false_and, exists_false], List.Pairwise.nil⟩, hm1⟩)
                  (fun Js1 hJs1 => by
                    c0_hsteps
                    · exact hJs1 m1 ⟨rfl, Or.inl hc⟩
                    · exact hJs1 m1 ⟨rfl, Or.inr hc⟩
                    · rw [‹l = 0#64›, ‹h = 0#64›, coeff128_zero] at hlh
                      refine hJ2a (nV, ⟨⟩) m1
                        ⟨gsy1, gcl1, gch1, phase1MaskInv_step_zero hpinv ?_, hm1⟩
                      rw [d_getD_eq_getElem d 0#64 hd_idx, ← hlh]))
          · have hdz : d.getD maskV.toNat 0#64 = 0#64 := by
              rw [d_getD_eq_getElem d 0#64 hd_idx]; exact hc
            c0_hsteps
            refine hJ2 (nV, ⟨⟩) m1 ⟨gsy1, gcl1, gch1, phase1MaskInv_step_zero hpinv ?_, hm1⟩
            rw [hdz]; rfl)
    · have hmeq : maskV.toNat = 16 := by simp only [BitVec.reduceToNat] at hc; omega
      rw [hmeq] at hpinv; c0_hsteps_nogrp; change wp Γ Q X (dcanonP23 cx s.gsy nV) m1
      exact ar_dcanon_p2 Γ hCadd hMcmp rfl hmasks hgsy_len hgcl_len hgch_len hpinv hm1 hQ
  · intro J1 hJ1; c0_hsteps
    refine hJ1 16 (0#32, 0#32, ⟨⟩) m ⟨by decide, rfl, gsy0, gcl0, gch0,
      ⟨by decide, rfl, rfl, rfl,
        ⟨by decide, fun _ hk => absurd hk (Nat.not_lt_zero _),
          fun _ hk => absurd hk (Nat.not_lt_zero _)⟩,
        fun σ => by simp [polyEval_zero]⟩, hm0⟩


/-! ## 5B. WP Proof: `ar_ttsim` -/

private theorem ar_ttsim_exit {Γ : LeanQbe.T.Env}
    {cx : Val i64} {lit nleaf sp nm nexp : Val i32} {all : Val i64} {s : ArCtxState} {g : Aig}
    {rhs0 rhs1 olit stkN0 stkP0 memoN0 stkN stkP memoN : List (BitVec 32)}
    {memoV0 memoV dense : List (BitVec 64)} {gsy : List (BitVec 32)} {gcl gch : List (BitVec 64)}
    {R Rrest : Mem 64 → Prop} {Q : Post [.bool, i64]} {X : XPost} {m : Mem 64} (hRrest :
      Rrest = TtsimRest s rhs0 rhs1 olit stkN0 stkP0 memoN0 dense gsy gcl gch R)
    (hnl : nleaf.toNat ≤ 6) (hmn_len : 64 ≤ memoN0.length) (hmv_len : 64 ≤ memoV0.length)
    (hsn : stkN.length = stkN0.length) (hsp : stkP.length = stkP0.length)
    (hmn : memoN.length = memoN0.length) (hmv : memoV.length = memoV0.length) (hnm : nm.toNat ≤ 64)
    (hmemo : TtMemoOk g nleaf.toNat s.g_lnode s.g_lmask all nm.toNat memoN memoV)
    (hm : TtsimMem cx s rhs0 rhs1 stkN stkP memoN memoV Rrest m)
    (hQ : TtsimQ cx lit nleaf all s g rhs0 rhs1 olit
      stkN0 stkP0 memoN0 memoV0 dense gsy gcl gch R Q) :
    wp Γ Q X (ttsimExit cx lit nleaf all s.stk_n s.stk_p s.memo_n s.memo_v sp nm nexp) m := by
  dsimp only [TtsimMem] at hm; unfold ttsimExit ttsimOuter
  have hlens := arCtxLengths_of_mem (R := array (t := i32) s.rhs0 rhs0 ⋆
    array (t := i32) s.rhs1 rhs1 ⋆ array (t := i32) s.stk_n stkN ⋆ array (t := i32) s.stk_p stkP ⋆
    array (t := i32) s.memo_n memoN ⋆ array64 s.memo_v memoV ⋆ Rrest) (sep_cast hm (by ac_rfl))
  have hlnode_len := hlens.g_lnode; have hlmask_len := hlens.g_lmask; c0_hsteps_nogrp
  refine wp_loop_group (fun rem ⟨fV, vV, jV, ⟨⟩⟩ m1 =>
      jV.toNat ≤ nleaf.toNat ∧ rem = nleaf.toNat - jV.toNat ∧ m1 = m ∧
      (fV = true → NodeMaskOk g nleaf.toNat s.g_lnode s.g_lmask all (lit >>> 1).toNat vV)) ?_ ?_
  · intro J1 rem ⟨fV, vV, jV, ⟨⟩⟩ m1 hrec1 ⟨hj_le, _, hm1, hf1⟩; subst m1; c0_hsteps_nogrp
    · have hj_lt : jV.toNat < nleaf.toNat := hc
      have hjp1 := bv32_add1_toNat (by omega : jV.toNat + 1 < 2 ^ 32)
      refine wp_join_group (fun ⟨f', v', ⟨⟩⟩ m2 => m2 = m ∧
          (f' = true → NodeMaskOk g nleaf.toNat s.g_lnode s.g_lmask all (lit >>> 1).toNat v'))
        (fun _ ⟨f', v', ⟨⟩⟩ m2 ⟨hm2, hf'⟩ => by
          subst m2; c0_hsteps
          exact hrec1 (nleaf.toNat - (jV + 1).toNat) (f', v', jV + 1, ⟨⟩) m
            (by omega) ⟨by omega, rfl, rfl, hf'⟩)
        (fun Jj hJj => by
          c0_hsteps_nogrp
          · exact hJj (fV, vV, ⟨⟩) m ⟨rfl, hf1⟩
          · exact hJj (true, s.g_lmask[jV.toNat]'(by omega), ⟨⟩) m
              ⟨rfl, fun _ => nodeMaskOk_lnode_idx hj_lt (by omega) (by omega) hc⟩
          · exact hJj (fV, vV, ⟨⟩) m ⟨rfl, hf1⟩)
    · refine wp_join_group (fun ⟨f2, v2, ⟨⟩⟩ m2 => m2 = m ∧
          (f2 = true → NodeMaskOk g nleaf.toNat s.g_lnode s.g_lmask all (lit >>> 1).toNat v2))
        (fun _ ⟨f2, v2, ⟨⟩⟩ m2 ⟨hm2, hf2⟩ => by
          subst m2; c0_hsteps_nogrp
          refine wp_loop_group (fun rem2 ⟨fM, vM, jM, ⟨⟩⟩ m3 =>
              jM.toNat ≤ nm.toNat ∧ rem2 = nm.toNat - jM.toNat ∧ m3 = m ∧ (fM = true →
                NodeMaskOk g nleaf.toNat s.g_lnode s.g_lmask all (lit >>> 1).toNat vM)) ?_ ?_
          · intro J2 rem2 ⟨fM, vM, jM, ⟨⟩⟩ m3 hrec2 ⟨hjM_le, _, hm3, hfM⟩; subst m3; c0_hsteps_nogrp
            · have hjM_lt : jM.toNat < nm.toNat := hc
              have hjMp1 := bv32_add1_toNat (by omega : jM.toNat + 1 < 2 ^ 32)
              refine wp_join_group (fun ⟨f', v', ⟨⟩⟩ m4 => m4 = m ∧ (f' = true →
                    NodeMaskOk g nleaf.toNat s.g_lnode s.g_lmask all (lit >>> 1).toNat v'))
                (fun _ ⟨f', v', ⟨⟩⟩ m4 ⟨hm4, hf'⟩ => by
                  subst m4; c0_hsteps
                  exact hrec2 (nm.toNat - (jM + 1).toNat) (f', v', jM + 1, ⟨⟩) m
                    (by omega) ⟨by omega, rfl, rfl, hf'⟩)
                (fun Jj2 hJj2 => by
                  c0_hsteps_nogrp
                  · exact hJj2 (fM, vM, ⟨⟩) m ⟨rfl, hfM⟩
                  · have hmn_j : (BitVec.setWidth 64 jM).toNat < memoN.length := by
                      rw [bv64_sw_toNat]; omega
                    have hmv_j : (BitVec.setWidth 64 jM).toNat < memoV.length := by
                      rw [bv64_sw_toNat]; omega
                    exact hJj2 (true, memoV[(BitVec.setWidth 64 jM).toNat]'hmv_j, ⟨⟩) m
                      ⟨rfl, fun _ => nodeMaskOk_memo_sw hmemo hjM_lt hmn_j hmv_j hc⟩
                  · exact hJj2 (fM, vM, ⟨⟩) m ⟨rfl, hfM⟩)
            · have hfM_t : fM = true := hc; clear hc
              refine wp_join_group (fun ⟨vOut, ⟨⟩⟩ m4 => m4 = m ∧
                  ∀ (t : Nat) (ρ : Nat → Bool), t < 64 → all.toNat.testBit t = true →
                    (∀ j < nleaf.toNat, (s.g_lmask.getD j 0#64).toNat.testBit t =
                        g.nodeVal ρ (s.g_lnode.getD j 0#32).toNat) →
                    vOut.toNat.testBit t = g.litVal ρ lit.toNat)
                (fun _ ⟨vOut, ⟨⟩⟩ m4 ⟨hm4, hvOut⟩ => by
                  subst m4; c0_hsteps; rw [hRrest] at hm
                  exact hQ true vOut stkN stkP memoN memoV m hsn hsp hmn hmv (fun _ => hvOut)
                    (ttsim_repack_mem hsn hsp hmn hm))
                (fun Jo hJo => by
                  c0_hsteps_nogrp
                  · refine hJo (~~~vM &&& all, ⟨⟩) m ⟨rfl, fun t ρ ht hall hleaf => ?_⟩
                    have hl := litVal_cond_mask g ρ lit vM all ht hall (hfM hfM_t t ρ ht hall hleaf)
                    have hne : lit &&& 1 ≠ 0#32 := by assumption
                    rw [ite_eq_left hne] at hl; exact hl
                  · refine hJo (vM, ⟨⟩) m ⟨rfl, fun t ρ ht hall hleaf => ?_⟩
                    have hl := litVal_cond_mask g ρ lit vM all ht hall (hfM hfM_t t ρ ht hall hleaf)
                    have heq0 : ¬ (lit &&& 1 ≠ 0#32) := fun hne => hne (by assumption)
                    rw [ite_eq_right heq0] at hl; exact hl)
            · rw [hRrest] at hm
              exact hQ false 0#64 stkN stkP memoN memoV m hsn hsp hmn hmv (fun h => by cases h)
                (ttsim_repack_mem hsn hsp hmn hm)
          · intro J2 hJ2; c0_hsteps
            exact hJ2 nm.toNat (f2, v2, 0#32, ⟨⟩) m ⟨Nat.zero_le _, rfl, rfl, hf2⟩)
        (fun J0 hJ0 => by
          c0_hsteps_nogrp
          · exact hJ0 (fV, vV, ⟨⟩) m ⟨rfl, hf1⟩
          · exact hJ0 (true, 0#64, ⟨⟩) m ⟨rfl, fun _ => by rw [hc]; exact nodeMaskOk_zero⟩
          · exact hJ0 (fV, vV, ⟨⟩) m ⟨rfl, hf1⟩)
  · intro J1 hJ1; c0_hsteps
    exact hJ1 nleaf.toNat (false, 0#64, 0#32, ⟨⟩) m
      ⟨Nat.zero_le _, rfl, rfl, fun h => by cases h⟩
private def ttsimGoSeq : List (Val i32) → List (Val i64) → Expr Val Cont [.bool, i64] →
    Expr Val Cont [.bool, i64]
  | v32s, v64s, e@(@Expr.let_ _ _ _ rs op k) => match rs with
    | [.bool] => e
    | _ => match evalTtsimOp op with | some r => ttsimGoSeq v32s v64s (k r) | none => .hlt
  | v :: v32s, v64s, .load (.bits 32) _ k => ttsimGoSeq v32s v64s (k v)
  | v32s, v :: v64s, .load (.bits 64) _ k => ttsimGoSeq v32s v64s (k v)
  | _, _, e => e
private def ttsimEval (cx : Val i64) (lit nleaf : Val i32) (all sn sph mn mv : Val i64)
    (spV nmV nexpV nd sI sM a0 b0 u2 : Val i32) (rhs0p rhs1p : Val i64)
    (G28 : Cont [i32, i32, i32, i32]) : Expr Val Cont [.bool, i64] :=
  let afterSp : Expr Val Cont [.bool, i64] := match ttsimOuter cx lit nleaf all sn sph mn mv with
    | @Expr.group _ _ _ [[.bits 32, .bits 32, .bits 32]] bs _ =>
      match bs (fun _ _ => False, ()) with
      | .cons b _ => match b (spV, nmV, nexpV, ()) with
        | @Expr.let_ _ _ _ [.bool] _ kc =>
          match kc (true, ()) with | .jnz _ t _ => ttsimGoSeq [nd] [] t | _ => .hlt
        | _ => .hlt
      | _ => .hlt
    | _ => .hlt
  let afterKnown : Expr Val Cont [.bool, i64] := match afterSp with
    | @Expr.group _ _ _ [[.bool, .bits 32]] bs _ => match bs (fun _ _ => False, ()) with
      | .cons b _ => match b (false, 0#32, ()) with
        | @Expr.let_ _ _ _ [.bool] _ kc => match kc (false, ()) with | .jnz _ _ f => f | _ => .hlt
        | _ => .hlt
      | _ => .hlt
    | _ => .hlt
  let afterJm : Expr Val Cont [.bool, i64] := match afterKnown with
    | @Expr.group _ _ _ [[.bool]] bs0 _ => match bs0 (fun _ _ => False, ()) with
      | .cons b0f _ => match b0f (false, ()) with
        | @Expr.group _ _ _ [[.bool, .bits 32]] bs1 _ => match bs1 (fun _ _ => False, ()) with
          | .cons b1f _ => match b1f (false, u2, ()) with | .jnz _ _ f => f | _ => .hlt
          | _ => .hlt
        | _ => .hlt
      | _ => .hlt
    | _ => .hlt
  let beforeG28 : Expr Val Cont [.bool, i64] := match ttsimGoSeq [sI] [] afterJm with
    | @Expr.let_ _ _ _ [.bool] _ kc1 => match kc1 (false, ()) with
      | .jnz _ _ f1 => match ttsimGoSeq [sM] [] f1 with
        | @Expr.let_ _ _ _ [.bool] _ kc2 => match kc2 (false, ()) with
          | .jnz _ _ f2 => ttsimGoSeq [sI, a0, b0] [rhs0p, rhs1p] f2
          | _ => .hlt
        | _ => .hlt
      | _ => .hlt
    | _ => .hlt
  match beforeG28 with
  | @Expr.group _ _ _ [[.bits 32, .bits 32, .bits 32, .bits 32]] _ k =>
    match ttsimGoSeq [0#32] [] (k (G28, ())) with
    | @Expr.let_ _ _ _ [.bool] _ kc3 => match kc3 (false, ()) with
      | .jnz _ _ f3 => match f3 with
        | @Expr.let_ _ _ _ _rs1 op1 k1 => match evalTtsimOp op1 with
          | some r1 => match k1 r1 with
            | @Expr.let_ _ _ _ _rs2 op2 k2 =>
              match evalTtsimOp op2 with | some r2 => k2 r2 | none => .hlt
            | _ => .hlt
          | none => .hlt
        | _ => .hlt
      | _ => .hlt
    | _ => .hlt
  | _ => .hlt
private def ttsimEvalMemo (cx : Val i64) (lit nleaf : Val i32) (all sn sph mn mv : Val i64)
    (spV nmV nexpV nd sI sM a0 b0 u2 : Val i32) (rhs0p rhs1p : Val i64)
    (G28 : Cont [i32, i32, i32, i32]) (va1 vb1 : Val i64) (fa1 fb1 : Val Ty.bool) :
    Expr Val Cont [.bool, i64] :=
  match ttsimEval cx lit nleaf all sn sph mn mv spV nmV nexpV nd sI sM a0 b0 u2 rhs0p rhs1p G28 with
  | @Expr.group _ _ _ [[.bits 32, .bits 64, .bits 64, .bool, .bool]] bs _ =>
    match bs (fun _ _ => False, ()) with
    | .cons b _ => match ttsimGoSeq [] [] (b (0#32, 0#64, 0#64, false, false, ())) with
      | @Expr.let_ _ _ _ [.bool] _ kc => match kc (false, ()) with
        | .jnz _ _ f => match f with
          | @Expr.group _ _ _ [[.bits 64, .bool]] bs1 _ => match bs1 (fun _ _ => False, ()) with
            | .cons b1 _ => match b1 (va1, fa1, ()) with
              | @Expr.group _ _ _ [[.bits 64, .bool]] bs2 _ =>
                match bs2 (fun _ _ => False, ()) with | .cons b2 _ => b2 (vb1, fb1, ()) | _ => .hlt
              | _ => .hlt
            | _ => .hlt
          | _ => .hlt
        | _ => .hlt
      | _ => .hlt
    | _ => .hlt
  | _ => .hlt
private theorem ar_ttsim_memo {Γ : LeanQbe.T.Env}
    {cx : Val i64} {lit nleaf spV nmV nexpV nd a0 b0 u2 : Val i32} {all : Val i64}
    {s : ArCtxState} {g : Aig}
    {rhs0 rhs1 olit stkN0 stkP0 memoN0 stkN stkP memoN : List (BitVec 32)}
    {memoV0 memoV dense : List (BitVec 64)} {gsy : List (BitVec 32)} {gcl gch : List (BitVec 64)}
    {R Rrest : Mem 64 → Prop} {Q : Post [.bool, i64]} {X : XPost} {ms : Mem 64}
    {G28 : Cont [i32, i32, i32, i32]} {va1 vb1 : Val i64} {fa1 fb1 : Val Ty.bool} (hRrest :
      Rrest = TtsimRest s rhs0 rhs1 olit stkN0 stkP0 memoN0 dense gsy gcl gch R)
    (ha : AigRep g rhs0 rhs1 olit) (hmn_len : 64 ≤ memoN0.length) (hmv_len : 64 ≤ memoV0.length)
    (hsn : stkN.length = stkN0.length) (hsp : stkP.length = stkP0.length)
    (hmn : memoN.length = memoN0.length) (hmv : memoV.length = memoV0.length)
    (hsp_pos : 0 < spV.toNat) (hsp_le : spV.toNat ≤ 160)
    (hnm_le : nmV.toNat ≤ 64) (hnexp_le : nexpV.toNat ≤ 64)
    (hnd_gt : g.I < nd.toNat) (hnd_le : nd.toNat ≤ g.M)
    (ha_eq : a0 = rhs0.getD (nd.toNat - g.I - 1) 0#32)
    (hb_eq : b0 = rhs1.getD (nd.toNat - g.I - 1) 0#32)
    (hmemo : TtMemoOk g nleaf.toNat s.g_lnode s.g_lmask all nmV.toNat memoN memoV)
    (hfa1 : fa1 = true → NodeMaskOk g nleaf.toNat s.g_lnode s.g_lmask all (a0 >>> 1).toNat va1)
    (hfb1 : fb1 = true → NodeMaskOk g nleaf.toNat s.g_lnode s.g_lmask all (b0 >>> 1).toNat vb1)
    (hms : TtsimMem cx s rhs0 rhs1 stkN stkP memoN memoV Rrest ms)
    (hQ : TtsimQ cx lit nleaf all s g rhs0 rhs1 olit
      stkN0 stkP0 memoN0 memoV0 dense gsy gcl gch R Q)
    (hG28 : ∀ xs m2, TtsimG28Inv cx nleaf all s g rhs0 rhs1
      stkN0 stkP0 memoN0 memoV0 Rrest
      (3 * (64 - nexpV.toNat) + spV.toNat) xs m2 → G28 xs m2) :
    wp Γ Q X (ttsimEvalMemo cx lit nleaf all s.stk_n s.stk_p s.memo_n s.memo_v
      spV nmV nexpV nd s.I s.M a0 b0 u2 s.rhs0 s.rhs1 G28 va1 vb1 fa1 fb1) ms := by
  unfold ttsimEvalMemo ttsimEval ttsimOuter ttsimOuterGo ttsimGoSeq evalTtsimOp; dsimp only
  dsimp only [TtsimMem] at hms; let an := a0 >>> 1; let bn := b0 >>> 1; c0_hsteps_nogrp
  refine wp_loop_group (fun remm (xs : Tup Val [i32, i64, i64, Ty.bool, Ty.bool]) mm =>
      match xs with
      | (jm, vaM, vbM, faM, fbM, PUnit.unit) =>
        jm.toNat ≤ nmV.toNat ∧ remm = nmV.toNat - jm.toNat ∧ mm = ms ∧
        (faM = true → NodeMaskOk g nleaf.toNat s.g_lnode s.g_lmask all an.toNat vaM) ∧
        (fbM = true → NodeMaskOk g nleaf.toNat s.g_lnode s.g_lmask all bn.toNat vbM)) ?_ ?_
  · intro Jm remm ⟨jm, vaM, vbM, faM, fbM, ⟨⟩⟩ mm hrecm ⟨hjm_le, _, hmm, hfaM, hfbM⟩
    subst mm; c0_hsteps_nogrp
    · have hjm_lt : jm.toNat < nmV.toNat := hc
      have hjmp1 := bv32_add1_toNat (by omega : jm.toNat + 1 < 2 ^ 32)
      refine wp_join_group (TtsimNmInv g nleaf s all an.toNat ms) ?_ ?_
      · rintro _ ⟨va', fa', ⟨⟩⟩ m3 ⟨hm3, hfa'⟩; subst m3
        refine wp_join_group (TtsimNmInv g nleaf s all bn.toNat ms) ?_ ?_
        · rintro _ ⟨vb', fb', ⟨⟩⟩ m4 ⟨hm4, hfb'⟩; subst m4; c0_hsteps
          exact hrecm (nmV.toNat - (jm + 1).toNat) (jm + 1, va', vb', fa', fb', ⟨⟩) ms
            (by omega) ⟨by omega, rfl, rfl, hfa', hfb'⟩
        · intro Jmb hJmb
          have hmn_j : (BitVec.setWidth 64 jm).toNat < memoN.length := by rw [bv64_sw_toNat]; omega
          have hmv_j : (BitVec.setWidth 64 jm).toNat < memoV.length := by rw [bv64_sw_toNat]; omega
          c0_hsteps_nogrp
          · exact hJmb (vbM, fbM, ⟨⟩) ms ⟨rfl, hfbM⟩
          · exact hJmb (memoV[(BitVec.setWidth 64 jm).toNat]'hmv_j, true, ⟨⟩) ms
              ⟨rfl, fun _ => nodeMaskOk_memo_sw hmemo hjm_lt hmn_j hmv_j hc⟩
          · exact hJmb (vbM, fbM, ⟨⟩) ms ⟨rfl, hfbM⟩
      · intro Jma hJma
        have hmn_j : (BitVec.setWidth 64 jm).toNat < memoN.length := by rw [bv64_sw_toNat]; omega
        have hmv_j : (BitVec.setWidth 64 jm).toNat < memoV.length := by rw [bv64_sw_toNat]; omega
        c0_hsteps_nogrp
        · exact hJma (vaM, faM, ⟨⟩) ms ⟨rfl, hfaM⟩
        · exact hJma (memoV[(BitVec.setWidth 64 jm).toNat]'hmv_j, true, ⟨⟩) ms
            ⟨rfl, fun _ => nodeMaskOk_memo_sw hmemo hjm_lt hmn_j hmv_j hc⟩
        · exact hJma (vaM, faM, ⟨⟩) ms ⟨rfl, hfaM⟩
    · have hfaT : faM = true := by assumption
      have hfbT : fbM = true := hc; clear hc
      refine wp_join_group (fun (xs : Tup Val [i64]) m3 =>
          match xs with
          | (vaF, PUnit.unit) =>
            m3 = ms ∧ vaF = if a0 &&& 1 ≠ 0#32 then ~~~vaM &&& all else vaM) ?_ ?_
      · rintro _ ⟨vaF, ⟨⟩⟩ m3 ⟨hm3, hvaF⟩; subst m3
        refine wp_join_group (fun (xs : Tup Val [i64]) m4 =>
            match xs with
            | (vbF, PUnit.unit) =>
              m4 = ms ∧ vbF = if b0 &&& 1 ≠ 0#32 then ~~~vbM &&& all else vbM) ?_ ?_
        · rintro _ ⟨vbF, ⟨⟩⟩ m4 ⟨hm4, hvbF⟩; subst m4; c0_hsteps_nogrp
          · rw [hRrest] at hms
            exact hQ false 0#64 stkN stkP memoN memoV ms hsn hsp hmn hmv
              (fun h => by cases h) (ttsim_repack_mem hsn hsp hmn hms)
          · have hnm_lt : nmV.toNat < 64 := by
              rw [show BitVec.toNat (64 : BitVec 32) = 64 from rfl] at hc; omega
            have hspm1 := bv32_sub1_toNat hsp_pos
            have hnmp1 := bv32_add1_toNat (by omega : nmV.toNat + 1 < 2 ^ 32)
            have hmn_nm : (BitVec.setWidth 64 nmV).toNat < memoN.length := by
              rw [bv64_sw_toNat]; omega
            have hmv_nm : (BitVec.setWidth 64 nmV).toNat < memoV.length := by
              rw [bv64_sw_toNat]; omega
            c0_hsteps
            refine hG28 (spV - 1, nmV + 1, nexpV, jm, ⟨⟩) _
              ⟨by rw [hspm1]; omega, by rw [hnmp1]; omega, hnexp_le, by rw [hspm1]; omega,
               stkN, stkP, memoN.set (BitVec.setWidth 64 nmV).toNat nd,
               memoV.set (BitVec.setWidth 64 nmV).toNat (vaF &&& vbF),
               hsn, hsp, by simp [hmn], by simp [hmv], ?_, by dsimp only [TtsimMem]; c0_frame⟩
            rw [hnmp1, set_eq_of_eq (j := nmV.toNat) (w := nd) bv64_sw_toNat rfl,
                set_eq_of_eq (j := nmV.toNat) (w := vaF &&& vbF) bv64_sw_toNat rfl]
            refine ttMemoOk_set hmemo (by omega) (by omega) ?_
            rw [hvaF, hvbF, ha_eq, hb_eq]
            exact nodeMaskOk_and ha hnd_gt hnd_le
              (by rw [← ha_eq]; exact hfaM hfaT) (by rw [← hb_eq]; exact hfbM hfbT)
        · intro Jb2 hJb2; c0_hsteps_nogrp
          · exact hJb2 (~~~vbM &&& all, ⟨⟩) ms ⟨rfl, ttsim_neg_branch_t hc⟩
          · exact hJb2 (vbM, ⟨⟩) ms ⟨rfl, ttsim_neg_branch_f hc⟩
      · intro Ja2 hJa2; c0_hsteps_nogrp
        · exact hJa2 (~~~vaM &&& all, ⟨⟩) ms ⟨rfl, ttsim_neg_branch_t hc⟩
        · exact hJa2 (vaM, ⟨⟩) ms ⟨rfl, ttsim_neg_branch_f hc⟩
    · rw [hRrest] at hms
      exact hQ false 0#64 stkN stkP memoN memoV ms hsn hsp hmn hmv
        (fun h => by cases h) (ttsim_repack_mem hsn hsp hmn hms)
    · rw [hRrest] at hms
      exact hQ false 0#64 stkN stkP memoN memoV ms hsn hsp hmn hmv
        (fun h => by cases h) (ttsim_repack_mem hsn hsp hmn hms)
  · intro Jm hJm; c0_hsteps
    exact hJm nmV.toNat (0#32, va1, vb1, fa1, fb1, ⟨⟩) ms
      ⟨Nat.zero_le _, rfl, rfl, hfa1, hfb1⟩
private theorem ar_ttsim_eval {Γ : LeanQbe.T.Env}
    {cx : Val i64} {lit nleaf spV nmV nexpV nd a0 b0 u2 : Val i32} {all : Val i64}
    {s : ArCtxState} {g : Aig}
    {rhs0 rhs1 olit stkN0 stkP0 memoN0 stkN stkP memoN : List (BitVec 32)}
    {memoV0 memoV dense : List (BitVec 64)} {gsy : List (BitVec 32)} {gcl gch : List (BitVec 64)}
    {R Rrest : Mem 64 → Prop} {Q : Post [.bool, i64]} {X : XPost} {ms : Mem 64}
    {G28 : Cont [i32, i32, i32, i32]} (hRrest :
      Rrest = TtsimRest s rhs0 rhs1 olit stkN0 stkP0 memoN0 dense gsy gcl gch R)
    (ha : AigRep g rhs0 rhs1 olit)
    (hnl : nleaf.toNat ≤ 6) (hmn_len : 64 ≤ memoN0.length) (hmv_len : 64 ≤ memoV0.length)
    (hsn : stkN.length = stkN0.length) (hsp : stkP.length = stkP0.length)
    (hmn : memoN.length = memoN0.length) (hmv : memoV.length = memoV0.length)
    (hsp_pos : 0 < spV.toNat) (hsp_le : spV.toNat ≤ 160)
    (hnm_le : nmV.toNat ≤ 64) (hnexp_le : nexpV.toNat ≤ 64)
    (hnd_gt : g.I < nd.toNat) (hnd_le : nd.toNat ≤ g.M)
    (ha_eq : a0 = rhs0.getD (nd.toNat - g.I - 1) 0#32)
    (hb_eq : b0 = rhs1.getD (nd.toNat - g.I - 1) 0#32)
    (hmemo : TtMemoOk g nleaf.toNat s.g_lnode s.g_lmask all nmV.toNat memoN memoV)
    (hms : TtsimMem cx s rhs0 rhs1 stkN stkP memoN memoV Rrest ms)
    (hQ : TtsimQ cx lit nleaf all s g rhs0 rhs1 olit
      stkN0 stkP0 memoN0 memoV0 dense gsy gcl gch R Q)
    (hG28 : ∀ xs m2, TtsimG28Inv cx nleaf all s g rhs0 rhs1
      stkN0 stkP0 memoN0 memoV0 Rrest
      (3 * (64 - nexpV.toNat) + spV.toNat) xs m2 → G28 xs m2) :
    wp Γ Q X (ttsimEval cx lit nleaf all s.stk_n s.stk_p s.memo_n s.memo_v
      spV nmV nexpV nd s.I s.M a0 b0 u2 s.rhs0 s.rhs1 G28) ms := by
  unfold ttsimEval ttsimOuter ttsimOuterGo ttsimGoSeq evalTtsimOp; dsimp only
  dsimp only [TtsimMem] at hms
  have hlens := arCtxLengths_of_mem (R := array (t := i32) s.rhs0 rhs0 ⋆
    array (t := i32) s.rhs1 rhs1 ⋆ array (t := i32) s.stk_n stkN ⋆
    array (t := i32) s.stk_p stkP ⋆ array (t := i32) s.memo_n memoN ⋆
    array64 s.memo_v memoV ⋆ Rrest) (sep_cast hms (by ac_rfl))
  have hlnode_len := hlens.g_lnode; have hlmask_len := hlens.g_lmask
  let an := a0 >>> 1; let bn := b0 >>> 1
  refine wp_loop_group (fun reme (xs : Tup Val [i32, i64, i64, Ty.bool, Ty.bool]) me =>
      match xs with
      | (jE, va, vb, fa, fb, PUnit.unit) =>
        jE.toNat ≤ nleaf.toNat ∧ reme = nleaf.toNat - jE.toNat ∧ me = ms ∧
        (fa = true → NodeMaskOk g nleaf.toNat s.g_lnode s.g_lmask all an.toNat va) ∧
        (fb = true → NodeMaskOk g nleaf.toNat s.g_lnode s.g_lmask all bn.toNat vb)) ?_ ?_
  · intro Je reme ⟨jE, va, vb, fa, fb, ⟨⟩⟩ me hrece ⟨hjE_le, _, hme, hfa, hfb⟩
    subst me; c0_hsteps_nogrp
    · have hjE_lt : jE.toNat < nleaf.toNat := hc
      have hjEp1 := bv32_add1_toNat (by omega : jE.toNat + 1 < 2 ^ 32)
      refine wp_join_group (TtsimNmInv g nleaf s all an.toNat ms) ?_ ?_
      · rintro _ ⟨va', fa', ⟨⟩⟩ m1 ⟨hm1, hfa'⟩; subst m1
        refine wp_join_group (TtsimNmInv g nleaf s all bn.toNat ms) ?_ ?_
        · rintro _ ⟨vb', fb', ⟨⟩⟩ m2 ⟨hm2, hfb'⟩; subst m2; c0_hsteps
          exact hrece (nleaf.toNat - (jE + 1).toNat) (jE + 1, va', vb', fa', fb', ⟨⟩) ms (by omega)
            ⟨by omega, rfl, rfl, hfa', hfb'⟩
        · intro Jb hJb
          have hjE_ln : (BitVec.setWidth 64 jE).toNat < s.g_lnode.length := by
            rw [bv64_sw_toNat]; omega
          have hjE_lm : (BitVec.setWidth 64 jE).toNat < s.g_lmask.length := by
            rw [bv64_sw_toNat]; omega
          c0_hsteps_nogrp
          · exact hJb (vb, fb, ⟨⟩) ms ⟨rfl, hfb⟩
          · exact hJb (s.g_lmask[jE.toNat]'(by omega), true, ⟨⟩) ms
              ⟨rfl, fun _ => nodeMaskOk_lnode_idx hjE_lt (by omega) (by omega) hc⟩
          · exact hJb (vb, fb, ⟨⟩) ms ⟨rfl, hfb⟩
      · intro Ja hJa
        have hjE_ln : (BitVec.setWidth 64 jE).toNat < s.g_lnode.length := by
          rw [bv64_sw_toNat]; omega
        have hjE_lm : (BitVec.setWidth 64 jE).toNat < s.g_lmask.length := by
          rw [bv64_sw_toNat]; omega
        c0_hsteps_nogrp
        · exact hJa (va, fa, ⟨⟩) ms ⟨rfl, hfa⟩
        · exact hJa (s.g_lmask[jE.toNat]'(by omega), true, ⟨⟩) ms
            ⟨rfl, fun _ => nodeMaskOk_lnode_idx hjE_lt (by omega) (by omega) hc⟩
        · exact hJa (va, fa, ⟨⟩) ms ⟨rfl, hfa⟩
    · refine wp_join_group (TtsimNmInv g nleaf s all an.toNat ms) ?_ ?_
      · rintro _ ⟨va1, fa1, ⟨⟩⟩ m1 ⟨hm1, hfa1⟩; subst m1
        refine wp_join_group (TtsimNmInv g nleaf s all bn.toNat ms) ?_ ?_
        · rintro _ ⟨vb1, fb1, ⟨⟩⟩ m2 ⟨hm2, hfb1⟩; subst m2
          change wp Γ Q X (ttsimEvalMemo cx lit nleaf all s.stk_n s.stk_p s.memo_n s.memo_v
            spV nmV nexpV nd s.I s.M a0 b0 u2 s.rhs0 s.rhs1 G28 va1 vb1 fa1 fb1) ms
          exact ar_ttsim_memo hRrest ha hmn_len hmv_len hsn hsp hmn hmv hsp_pos hsp_le
            hnm_le hnexp_le hnd_gt hnd_le ha_eq hb_eq hmemo hfa1 hfb1 hms hQ hG28
        · intro Jb0 hJb0; c0_hsteps_nogrp
          · exact hJb0 (vb, fb, ⟨⟩) ms ⟨rfl, hfb⟩
          · have hbn0 : bn = 0#32 := hc
            exact hJb0 (0#64, true, ⟨⟩) ms ⟨rfl, fun _ => by rw [hbn0]; exact nodeMaskOk_zero⟩
          · exact hJb0 (vb, fb, ⟨⟩) ms ⟨rfl, hfb⟩
      · intro Ja0 hJa0; c0_hsteps_nogrp
        · exact hJa0 (va, fa, ⟨⟩) ms ⟨rfl, hfa⟩
        · have han0 : an = 0#32 := hc
          exact hJa0 (0#64, true, ⟨⟩) ms ⟨rfl, fun _ => by rw [han0]; exact nodeMaskOk_zero⟩
        · exact hJa0 (va, fa, ⟨⟩) ms ⟨rfl, hfa⟩
  · intro Je hJe; c0_hsteps
    exact hJe nleaf.toNat (0#32, 0#64, 0#64, false, false, ⟨⟩) ms
      ⟨Nat.zero_le _, rfl, rfl, (fun h => by cases h), (fun h => by cases h)⟩

theorem ar_ttsim_wp (Γ : LeanQbe.T.Env) :
    ∀ xs m Q X, arTtsimSpec xs m Q X → Func.wp Γ ar_ttsim_body xs m Q X := by
  rintro ⟨cx, lit, nleaf, all, ⟨⟩⟩ m Q X
    ⟨s, g, rhs0, rhs1, olit, stkN0, stkP0, memoN0, memoV0, dense, gsy, gcl, gch, R,
     hI_eq, hM_eq, ha, hnl, hsn_len, hsp_len, hmn_len, hmv_len, hm, hQ⟩
  let Rrest := TtsimRest s rhs0 rhs1 olit stkN0 stkP0 memoN0 dense gsy gcl gch R
  have hRrest : Rrest = TtsimRest s rhs0 rhs1 olit stkN0 stkP0 memoN0 dense gsy gcl gch R := rfl
  have hm0 : TtsimMem cx s rhs0 rhs1 stkN0 stkP0 memoN0 memoV0 Rrest m := ttsim_unpack_mem hm
  dsimp only [TtsimMem] at hm0
  have hlens := arCtxLengths_of_mem (R := array (t := i32) s.rhs0 rhs0 ⋆
    array (t := i32) s.rhs1 rhs1 ⋆ array (t := i32) s.stk_n stkN0 ⋆ array (t := i32) s.stk_p stkP0 ⋆
    array (t := i32) s.memo_n memoN0 ⋆ array64 s.memo_v memoV0 ⋆ Rrest) (sep_cast hm0 (by ac_rfl))
  have hlnode_len := hlens.g_lnode; have hlmask_len := hlens.g_lmask
  have h0_sn : (BitVec.signExtend 64 0#32).toNat < stkN0.length := by
    rw [show (BitVec.signExtend 64 0#32).toNat = 0 from rfl]; omega
  have h0_sp : (BitVec.signExtend 64 0#32).toNat < stkP0.length := by
    rw [show (BitVec.signExtend 64 0#32).toNat = 0 from rfl]; omega
  c0_hsteps_nogrp
  refine wp_loop_group (fun rem ⟨spV, nmV, nexpV, ⟨⟩⟩ ms =>
      spV.toNat ≤ 160 ∧ nmV.toNat ≤ 64 ∧ nexpV.toNat ≤ 64 ∧
      rem = 3 * (64 - nexpV.toNat) + spV.toNat ∧
      ∃ stkN stkP memoN memoV, stkN.length = stkN0.length ∧ stkP.length = stkP0.length ∧
        memoN.length = memoN0.length ∧ memoV.length = memoV0.length ∧
        TtMemoOk g nleaf.toNat s.g_lnode s.g_lmask all nmV.toNat memoN memoV ∧
        (arCtxMem cx s ⋆ array (t := i32) s.rhs0 rhs0 ⋆ array (t := i32) s.rhs1 rhs1 ⋆
          array (t := i32) s.stk_n stkN ⋆ array (t := i32) s.stk_p stkP ⋆
          array (t := i32) s.memo_n memoN ⋆ array64 s.memo_v memoV ⋆ Rrest) ms) ?_ ?_
  · intro Jw rem ⟨spV, nmV, nexpV, ⟨⟩⟩ ms hrec
      ⟨hsp_le, hnm_le, hnexp_le, hrem_eq, stkN, stkP, memoN, memoV, hsn, hsp, hmn, hmv, hmemo, hms⟩
    c0_hsteps_nogrp
    · have hsp_pos : 0 < spV.toNat := hc; have hspm1 := bv32_sub1_toNat hsp_pos
      have hsn_sp : (BitVec.setWidth 64 (spV - 1)).toNat < stkN.length := by
        rw [bv64_sw_toNat, hspm1]; omega
      c0_hsteps_nogrp
      let nd := stkN[(BitVec.setWidth 64 (spV - 1)).toNat]'hsn_sp
      refine wp_loop_group (fun remk ⟨known, j, ⟨⟩⟩ mk =>
          j.toNat ≤ nleaf.toNat ∧ remk = nleaf.toNat - j.toNat ∧ mk = ms) ?_ ?_
      · intro Jk remk ⟨known, j, ⟨⟩⟩ mk hreck ⟨hj_le, _, hmk⟩; subst mk; c0_hsteps_nogrp
        · have hj_lt : j.toNat < nleaf.toNat := hc
          have hjp1 := bv32_add1_toNat (by omega : j.toNat + 1 < 2 ^ 32)
          have hj6 : (BitVec.setWidth 64 j).toNat < 6 := by rw [bv64_sw_toNat]; omega
          refine wp_join_group (fun ⟨_known', ⟨⟩⟩ mk' => mk' = ms)
            (fun _ ⟨known', ⟨⟩⟩ mk' hmk' => by
              subst mk'; c0_hsteps
              exact hreck (nleaf.toNat - (j + 1).toNat) (known', j + 1, ⟨⟩) ms
                (by omega) ⟨by omega, rfl, rfl⟩)
            (fun Jj hJj => by
              c0_hsteps_nogrp
              · exact hJj (true, ⟨⟩) ms rfl
              · exact hJj (known, ⟨⟩) ms rfl)
        · refine wp_join_group (fun (_ : Tup Val [Ty.bool]) mk' => mk' = ms)
            (fun _ (xs1 : Tup Val [Ty.bool]) mk' hmk' => by
              rcases xs1 with ⟨known', ⟨⟩⟩; subst mk'
              refine wp_join_group (fun (_ : Tup Val [Ty.bool, i32]) mk'' => mk'' = ms)
                (fun _ (xs2 : Tup Val [Ty.bool, i32]) mk'' hmk'' => by
                  rcases xs2 with ⟨known'', _j2, ⟨⟩⟩
                  subst mk''; c0_hsteps_nogrp
                  · exact hrec (3 * (64 - nexpV.toNat) + (spV - 1).toNat)
                      (spV - 1, nmV, nexpV, ⟨⟩) ms (by omega)
                      ⟨by omega, hnm_le, hnexp_le, rfl, stkN, stkP, memoN, memoV,
                        hsn, hsp, hmn, hmv, hmemo, hms⟩
                  · rw [hRrest] at hms
                    exact hQ false 0#64 stkN stkP memoN memoV ms hsn hsp hmn hmv
                      (fun h => by cases h) (ttsim_repack_mem hsn hsp hmn hms)
                  · rw [hRrest] at hms
                    exact hQ false 0#64 stkN stkP memoN memoV ms hsn hsp hmn hmv
                      (fun h => by cases h) (ttsim_repack_mem hsn hsp hmn hms)
                  · have hnd_mod : (2 ^ 32 - (1 : BitVec 32).toNat + spV.toNat) % 2 ^ 32 =
                        spV.toNat - 1 := by rw [show (1 : BitVec 32).toNat = 1 from rfl]; omega
                    have hnd_val : nd =
                        stkN[(2 ^ 32 - (1 : BitVec 32).toNat + spV.toNat) % 2 ^ 32]'(by
                        omega) := by dsimp [nd]; congr 1
                    have hnd_lt_I : ¬ nd.toNat ≤ s.I.toNat := by rw [hnd_val]; assumption
                    have hnd_gt_M : ¬ s.M.toNat < nd.toNat := by rw [hnd_val]; exact hc
                    have hnd_gt : g.I < nd.toNat := by rw [← hI_eq]; omega
                    have hnd_le : nd.toNat ≤ g.M := by rw [← hM_eq]; omega
                    have hsi_le : s.I ≤ nd := BitVec.le_def.mpr (by rw [hI_eq]; omega)
                    have h1_le : (1 : BitVec 32) ≤ nd - s.I :=
                      BitVec.le_def.mpr (by
                        rw [BitVec.toNat_sub_of_le hsi_le, show (1 : BitVec 32).toNat = 1 from rfl,
                          hI_eq]; omega)
                    have hidx_eq : (nd - s.I - 1).toNat = nd.toNat - g.I - 1 := by
                      rw [BitVec.toNat_sub_of_le h1_le, BitVec.toNat_sub_of_le hsi_le,
                        show (1 : BitVec 32).toNat = 1 from rfl, hI_eq]
                    have hidx_lt :
                        (BitVec.setWidth 64 (nd - s.I - 1)).toNat < rhs0.length := by
                      rw [bv64_sw_toNat, hidx_eq, ha.rhs0_len]
                      have := ha.m_eq; omega
                    have hidx_lt1 :
                        (BitVec.setWidth 64 (nd - s.I - 1)).toNat < rhs1.length := by
                      rw [ha.rhs1_len, ← ha.rhs0_len]; exact hidx_lt
                    have hsp_p : (BitVec.setWidth 64 (spV - 1)).toNat < stkP.length := by
                      rw [bv64_sw_toNat, hspm1]; omega
                    c0_hsteps_nogrp
                    refine wp_join_group (fun (xs28 : Tup Val [i32, i32, i32, i32]) m2 =>
                        match xs28 with
                        | (sp2, nm2, nexp2, _u2, PUnit.unit) =>
                          sp2.toNat ≤ 160 ∧ nm2.toNat ≤ 64 ∧ nexp2.toNat ≤ 64 ∧
                          3 * (64 - nexp2.toNat) + sp2.toNat < rem ∧ ∃ stkN2 stkP2 memoN2 memoV2,
                            stkN2.length = stkN0.length ∧ stkP2.length = stkP0.length ∧
                            memoN2.length = memoN0.length ∧ memoV2.length = memoV0.length ∧
                            TtMemoOk g nleaf.toNat s.g_lnode s.g_lmask all
                              nm2.toNat memoN2 memoV2 ∧
                            (arCtxMem cx s ⋆ array (t := i32) s.rhs0 rhs0 ⋆
                              array (t := i32) s.rhs1 rhs1 ⋆ array (t := i32) s.stk_n stkN2 ⋆
                              array (t := i32) s.stk_p stkP2 ⋆ array (t := i32) s.memo_n memoN2 ⋆
                              array64 s.memo_v memoV2 ⋆ Rrest) m2) ?_ ?_
                    · intro _ xs28 m2 h28
                      rcases xs28 with ⟨sp2, nm2, nexp2, _u2, ⟨⟩⟩
                      rcases h28 with ⟨h1, h2, h3, hlt, rest⟩; c0_hsteps
                      exact hrec (3 * (64 - nexp2.toNat) + sp2.toNat) (sp2, nm2, nexp2, ⟨⟩)
                        m2 hlt ⟨h1, h2, h3, rfl, rest⟩
                    · intro G28 hG28
                      have hstkP_set :
                          (stkP.set (BitVec.setWidth 64 (spV - 1)).toNat 1).length =
                            stkP0.length := by simp [hsp]
                      c0_hsteps_nogrp
                      · exact hQ false 0#64 stkN
                          (stkP.set (BitVec.setWidth 64 (spV - 1)).toNat 1) memoN memoV m
                          hsn hstkP_set hmn hmv (fun h => by cases h)
                          (ttsim_repack_mem hsn hstkP_set hmn (by rw [← hRrest]; c0_frame))
                      · exact hQ false 0#64 stkN
                          (stkP.set (BitVec.setWidth 64 (spV - 1)).toNat 1) memoN memoV m
                          hsn hstkP_set hmn hmv (fun h => by cases h)
                          (ttsim_repack_mem hsn hstkP_set hmn (by rw [← hRrest]; c0_frame))
                      · have hnexp1 := bv32_add1_toNat (by omega : nexpV.toNat + 1 < 2 ^ 32)
                        have hnexp_le64 : nexpV.toNat + 1 ≤ 64 := by
                          have h' : ¬ BitVec.toNat (64 : BitVec 32) <
                              (nexpV.toNat + BitVec.toNat (1 : BitVec 32)) % 2 ^ 32 := by assumption
                          rw [show BitVec.toNat (64 : BitVec 32) = 64 from rfl,
                            show BitVec.toNat (1 : BitVec 32) = 1 from rfl] at h'
                          omega
                        have hsp2_le : spV.toNat + 2 ≤ 160 := by
                          rw [show BitVec.toNat (160 : BitVec 32) = 160 from rfl,
                            show BitVec.toNat (2 : BitVec 32) = 2 from rfl] at hc
                          omega
                        have hspp1 := bv32_add1_toNat (by omega : spV.toNat + 1 < 2 ^ 32)
                        have hspp2 :=
                          bv32_add1_toNat (by omega : (spV + 1).toNat + 1 < 2 ^ 32)
                        have hsp_sp : (BitVec.setWidth 64 spV).toNat <
                            (stkP.set (BitVec.setWidth 64 (spV - 1)).toNat 1).length := by
                          rw [List.length_set, bv64_sw_toNat]; omega
                        have hsn_sp2 : (BitVec.setWidth 64 (spV + 1)).toNat <
                            (stkN.set (BitVec.setWidth 64 spV).toNat
                              (rhs0[(BitVec.setWidth 64 (nd - s.I - 1)).toNat]'hidx_lt >>>
                                1)).length := by rw [List.length_set, bv64_sw_toNat, hspp1]; omega
                        dsimp only [nd] at hsn_sp2
                        have hsp_sp2 : (BitVec.setWidth 64 (spV + 1)).toNat <
                            ((stkP.set (BitVec.setWidth 64 (spV - 1)).toNat 1).set
                              (BitVec.setWidth 64 spV).toNat 0).length := by
                          rw [List.length_set, List.length_set, bv64_sw_toNat, hspp1]; omega
                        c0_hsteps
                        let stkN2 := (stkN.set (BitVec.setWidth 64 spV).toNat
                          (rhs0[(BitVec.setWidth 64 (nd - s.I - 1)).toNat]'hidx_lt >>> 1)).set
                          (BitVec.setWidth 64 (spV + 1)).toNat
                          (rhs1[(BitVec.setWidth 64 (nd - s.I - 1)).toNat]'hidx_lt1 >>> 1)
                        let stkP2 := ((stkP.set (BitVec.setWidth 64 (spV - 1)).toNat 1).set
                          (BitVec.setWidth 64 spV).toNat 0).set
                          (BitVec.setWidth 64 (spV + 1)).toNat 0
                        refine hG28 (spV + 1 + 1, nmV, nexpV + 1, _j2, ⟨⟩) _
                          ⟨by rw [hspp2, hspp1]; omega, hnm_le, by rw [hnexp1]; omega,
                           by rw [hrem_eq, hnexp1, hspp2, hspp1]; omega, stkN2, stkP2, memoN, memoV,
                           by simp [stkN2, hsn], by simp [stkP2, hsp], hmn, hmv, hmemo, ?_⟩
                        dsimp only [stkN2, stkP2, nd]; rw [Std.ExtHashMap.sep_emp] at hm
                        exact sep_cast hm (by ac_rfl)
                      · change wp Γ Q X
                          (ttsimEval cx lit nleaf all s.stk_n s.stk_p s.memo_n s.memo_v
                            spV nmV nexpV nd s.I s.M
                            (rhs0[(BitVec.setWidth 64 (nd - s.I - 1)).toNat]'hidx_lt)
                            (rhs1[(BitVec.setWidth 64 (nd - s.I - 1)).toNat]'hidx_lt1)
                            _j2 s.rhs0 s.rhs1 G28) ms
                        exact ar_ttsim_eval hRrest ha hnl hmn_len hmv_len hsn hsp hmn hmv
                          hsp_pos hsp_le hnm_le hnexp_le hnd_gt hnd_le
                          (getElem_eq_getD 0#32 hidx_lt (by rw [bv64_sw_toNat, hidx_eq]))
                          (getElem_eq_getD 0#32 hidx_lt1 (by rw [bv64_sw_toNat, hidx_eq]))
                          hmemo hms hQ (fun xs m2 hxs => by
                            rcases xs with ⟨sp2, nm2, nexp2, u2, ⟨⟩⟩; rw [← hrem_eq] at hxs
                            exact hG28 (sp2, nm2, nexp2, u2, ⟨⟩) m2 hxs))
                (fun Jm hJm => by
                  c0_hsteps_nogrp
                  · exact hJm (known', _, ⟨⟩) ms rfl
                  · refine wp_loop_group (fun remm ⟨knm, jm, ⟨⟩⟩ mm =>
                        jm.toNat ≤ nmV.toNat ∧ remm = nmV.toNat - jm.toNat ∧ mm = ms) ?_ ?_
                    · intro Jm2 remm ⟨knm, jm, ⟨⟩⟩ mm hrecm2 ⟨hjm_le, _, hmm⟩
                      subst mm; c0_hsteps_nogrp
                      · have hjm_lt : jm.toNat < nmV.toNat := hc
                        have hjmp1 := bv32_add1_toNat (by omega : jm.toNat + 1 < 2 ^ 32)
                        have hmn_j : (BitVec.setWidth 64 jm).toNat < memoN.length := by
                          rw [bv64_sw_toNat]; omega
                        refine wp_join_group (fun ⟨_kn', ⟨⟩⟩ mm' => mm' = ms)
                          (fun _ ⟨kn', ⟨⟩⟩ mm' hmm' => by
                            subst mm'; c0_hsteps
                            exact hrecm2 (nmV.toNat - (jm + 1).toNat) (kn', jm + 1, ⟨⟩) ms
                              (by omega) ⟨by omega, rfl, rfl⟩)
                          (fun Jj3 hJj3 => by
                            c0_hsteps_nogrp
                            · exact hJj3 (true, ⟨⟩) ms rfl
                            · exact hJj3 (knm, ⟨⟩) ms rfl)
                      · exact hJm (knm, jm, ⟨⟩) ms rfl
                    · intro Jm2 hJm2; c0_hsteps
                      exact hJm2 nmV.toNat (known', 0#32, ⟨⟩) ms ⟨Nat.zero_le _, rfl, rfl⟩))
            (fun J0 hJ0 => by
              c0_hsteps_nogrp
              · exact hJ0 (known, ⟨⟩) ms rfl
              · exact hJ0 (true, ⟨⟩) ms rfl
              · exact hJ0 (known, ⟨⟩) ms rfl)
      · intro Jk hJk; c0_hsteps
        exact hJk nleaf.toNat (false, 0#32, ⟨⟩) ms ⟨Nat.zero_le _, rfl, rfl⟩
    · change wp Γ Q X (ttsimExit cx lit nleaf all s.stk_n s.stk_p s.memo_n s.memo_v
          spV nmV nexpV) ms
      exact ar_ttsim_exit hRrest hnl hmn_len hmv_len hsn hsp hmn hmv hnm_le hmemo hms hQ
  · intro Jw hJw; have hsn_0 : (BitVec.signExtend 64 0#32 * 4#64).toNat = 0 := rfl; c0_hsteps
    refine hJw (3 * 64 + 1) (1#32, 0#32, 0#32, ⟨⟩) _
      ⟨by decide, by decide, by decide, rfl, stkN0.set 0 (lit >>> 1), stkP0.set 0 0, memoN0, memoV0,
       by simp, by simp, rfl, rfl, fun t ρ ht hall hl k hk => absurd hk (Nat.not_lt_zero _), ?_⟩
    rw [Std.ExtHashMap.sep_emp] at hm; exact sep_cast hm (by ac_rfl)
