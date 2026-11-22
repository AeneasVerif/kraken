module

public import LeanQbe.T.Examples.Kissat.FullM6MinShrink
public import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.Examples.Kissat.FullPropDecLemmas
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M6 `PR-W2B` Proof Shard 0 (`decision_rate` & `full_decide_m6`, UNSAT-Only)

Proves `Func.wp` against canonical / Wave-2B specs for:
1. `full_dr_init_m6` (`m6DrInitSpec`)
2. `full_dr_update_m6` (`m6DrUpdateSpec`)
3. `full_dr_allow_m6` (`m6DrAllowSpec`)
4. `full_decide_m6` (`Full.fullDecideSpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6MinShrink

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full hiding
  full_decide_body full_decide_wf full_decide_wp
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open Kraken.Bedrock2.Test

/-! ## 1. Wave-2B `decision_rate` specs & bridge theorems -/

/-- Decision-rate initializer & update contract (`full_dr_init_m6`, `full_dr_update_m6`). -/
def m6DrInitSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    ∀ dl' del' m',
      let s' : FullState :=
        { s with scratch := { s.scratch with delayed_len := dl', delayed := del' } }
      s'.LengthsOk c → (FullMem c s' ⋆ R) m' → Q () m'

/-- Decision-rate EMA update contract (preserves all core & non-`delayed*` fields). -/
def m6DrUpdateSpec : Spec [i64] [] := m6DrInitSpec

/-- Read-only decision-rate gate contract (`full_dr_allow_m6`). -/
def m6DrAllowSpec : Spec [i64] [.bool] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧ ∀ r : Bool, Q (r, ()) m

theorem m6DrInitSpec_of {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post []} {X : XPost} (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ dl' del' m',
      let s' : FullState :=
        { s with scratch := { s.scratch with delayed_len := dl', delayed := del' } }
      s'.LengthsOk c → (FullMem c s' ⋆ R) m' → Q () m') :
    m6DrInitSpec (c.hdr, ()) m Q X :=
  ⟨c, s, R, rfl, hlen, hm, hQ⟩

theorem m6DrUpdateSpec_of {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post []} {X : XPost} (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ dl' del' m',
      let s' : FullState :=
        { s with scratch := { s.scratch with delayed_len := dl', delayed := del' } }
      s'.LengthsOk c → (FullMem c s' ⋆ R) m' → Q () m') :
    m6DrUpdateSpec (c.hdr, ()) m Q X :=
  m6DrInitSpec_of hlen hm hQ

theorem m6DrAllowSpec_of {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [.bool]} {X : XPost} (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ r : Bool, Q (r, ()) m) :
    m6DrAllowSpec (c.hdr, ()) m Q X :=
  ⟨c, s, R, rfl, hlen, hm, hQ⟩

theorem m6DrInitSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post []} {X X' : XPost}
    (h : m6DrInitSpec xs m Q X) : m6DrInitSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem m6DrUpdateSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post []} {X X' : XPost}
    (h : m6DrUpdateSpec xs m Q X) : m6DrUpdateSpec xs m Q X' := by
  exact m6DrInitSpec_monoX h

theorem m6DrAllowSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [.bool]} {X X' : XPost}
    (h : m6DrAllowSpec xs m Q X) : m6DrAllowSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

/-! ## 2. Private arithmetic helpers -/

private theorem bv32_dec_lit_even {v : BitVec 64} (hv : v.toNat < 2 ^ 30) :
    ((v <<< (1 : Nat)).setWidth 32).toNat = 2 * v.toNat := by
  have h1 : (v <<< (1 : Nat)).toNat = (2 * v.toNat) % 2 ^ 64 := FullArenaTactics.bv64_shl1_nat v
  rw [BitVec.toNat_setWidth, h1, Nat.mod_eq_of_lt (by omega : 2 * v.toNat < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 2 * v.toNat < 2 ^ 32)]

private theorem bv32_dec_lit_odd {v : BitVec 64} (hv : v.toNat < 2 ^ 30) :
    (((v <<< (1 : Nat)).setWidth 32) ||| 1#32).toNat = 2 * v.toNat + 1 := by
  have hev := bv32_dec_lit_even hv
  have h1 : ((v <<< (1 : Nat)).setWidth 32 ||| 1#32).toNat =
      ((v <<< (1 : Nat)).setWidth 32).toNat ||| 1 := by simp [BitVec.toNat_or]
  rw [h1, hev]
  have : ∀ n : Nat, (2 * n) ||| 1 = 2 * n + 1 := fun n => by
    apply Nat.eq_of_testBit_eq; intro i
    cases i with
    | zero => simp [Nat.testBit_zero]
    | succ k =>
      have h0 : Nat.testBit 1 (k + 1) = false := by rw [Nat.testBit_succ]; simp
      rw [Nat.testBit_or, h0, Bool.or_false, Nat.testBit_succ, Nat.testBit_succ]
      congr 1; omega
  exact this v.toNat

/-! ## 3. `full_dr_init_m6`, `full_dr_update_m6`, `full_dr_allow_m6` `Func.wp` proofs -/

theorem full_dr_init_m6_wp (Γ : Env) :
    ∀ args m Q X, m6DrInitSpec args m Q X →
      Func.wp Γ full_dr_init_m6_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hd_bnd : c.delayed_cap < dimacsBound := c.hdel
  have hdl_len : s.scratch.delayed.length = 3 * c.delayed_cap := hlen.scratch_ok.delayed_len_arr
  let dl1 : Nat :=
    ((1#64 <<< (63 : Nat)) ||| ((s.scratch.switched &&& 127#64) <<< (56 : Nat))).toNat
  let s1 : FullState := { s with scratch := { s.scratch with delayed_len := dl1 } }
  have hlen1 : s1.LengthsOk c := ⟨hlen.core_ok,
    { hlen.scratch_ok with walk_vals_len := hlen.scratch_ok.walk_vals_len }⟩
  c0_hsteps_nogrp
  · exact hQ s.scratch.delayed_len s.scratch.delayed m hlen hm
  · exact hQ dl1 s.scratch.delayed m hlen1 hm
  · have hc_ge : 4 ≤ c.delayed_cap := by
      have hlt : ¬ c.delayed_cap % 2 ^ 64 < (4#64).toNat := by assumption
      rw [Nat.mod_eq_of_lt (by unfold dimacsBound at hd_bnd; omega),
        show (4#64).toNat = 4 from rfl] at hlt
      exact Nat.le_of_not_lt hlt
    refine wp_loop_inv
      (fun (i, ()) m2 => i.toNat ≤ 12 ∧ ∃ del2 : List (BitVec 32),
        del2.length = 3 * c.delayed_cap ∧
        (FullMem c { s1 with scratch := { s1.scratch with delayed := del2 } } ⋆ R) m2)
      (fun (i, ()) _ => 12 - i.toNat) (fun J hJ => ?_)
      (fun J (i, ()) m2 ⟨hi_le, del2, hdel2_len, hm2⟩ hJ => ?_)
    · c0_hsteps; exact hJ (0#64, ()) m ⟨by simp, s1.scratch.delayed, hdl_len, hm⟩
    · c0_hsteps
      · have hi_lt : i.toNat < 12 := by c0_bound
        have hi_arr : i.toNat < del2.length := by rw [hdel2_len]; omega
        c0_hsteps
        exact hJ _ m (by c0_bound) ⟨by c0_bound, del2.set i.toNat 0#32, by
          simp [hdel2_len], hm⟩
      · have h7 : (7#64).toNat < del2.length := by
          rw [hdel2_len, show (7#64).toNat = 7 from rfl]; omega
        have h11 : (11#64).toNat < (del2.set 7 1#32).length := by
          rw [show (11#64).toNat = 11 from rfl]; simp [hdel2_len]; omega
        c0_hsteps
        refine hQ dl1 ((del2.set 7 1#32).set 11 1#32) m ?_ hm
        exact ⟨hlen1.core_ok, { hlen1.scratch_ok with delayed_len_arr := by simp [hdel2_len] }⟩

theorem full_dr_update_m6_wp (Γ : Env)
    (hDrInit : ∀ a m Q X, m6DrInitSpec a m Q X → Γ "full_dr_init_m6" [i64] [] a m Q X) :
    ∀ args m Q X, m6DrUpdateSpec args m Q X →
      Func.wp Γ full_dr_update_m6_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hd_bnd : c.delayed_cap < dimacsBound := c.hdel
  c0_hsteps_nogrp
  c0_call hDrInit
  refine ⟨c, s, R, rfl, hlen, hm, fun dl1 del1 m1 hlen1 hm1 => ?_⟩
  dsimp only; clear m hm
  let s1 : FullState :=
    { s with scratch := { s.scratch with delayed_len := dl1, delayed := del1 } }
  have hm1' : (FullMem c s1 ⋆ R) m1 := hm1
  have hdl1_len : del1.length = 3 * c.delayed_cap := hlen1.scratch_ok.delayed_len_arr
  c0_hsteps_nogrp
  · exact hQ dl1 del1 m1 hlen1 hm1'
  · have hc_ge : 4 ≤ c.delayed_cap := by
      have hlt : ¬ c.delayed_cap % 2 ^ 64 < (4#64).toNat := by assumption
      rw [Nat.mod_eq_of_lt (by unfold dimacsBound at hd_bnd; omega),
        show (4#64).toNat = 4 from rfl] at hlt
      exact Nat.le_of_not_lt hlt
    refine wp_join_group (fun (off, ()) m2 => m1 = m2 ∧ off.toNat ≤ 2)
      (fun Joff (off, ()) m2 ⟨hm2, hoff⟩ => ?_) (fun Joff hJoff => ?_)
    · rcases hm2 with rfl; rw [Blocks.get_here]; dsimp only
      c0_hsteps_nogrp
      refine wp_join_group (fun (eoff, ()) m3 => m1 = m3 ∧ eoff.toNat ≤ 8)
        (fun Jeoff (eoff, ()) m3 ⟨hm3, heoff⟩ => ?_) (fun Jeoff hJeoff => ?_)
      · rcases hm3 with rfl; rw [Blocks.get_here]; dsimp only
        have ho0 : off.toNat < s1.scratch.delayed.length := by
          change off.toNat < del1.length; rw [hdl1_len]; omega
        have ho1 : (off + 1#64).toNat < s1.scratch.delayed.length := by
          change (off + 1#64).toNat < del1.length
          have := BitVec.toNat_add off 1#64
          rw [hdl1_len, this, show (1#64).toNat = 1 from rfl,
            Nat.mod_eq_of_lt (by omega : off.toNat + 1 < 2 ^ 64)]; omega
        have he0 : eoff.toNat < s1.scratch.delayed.length := by
          change eoff.toNat < del1.length; rw [hdl1_len]; omega
        have he1 : (eoff + 1#64).toNat < s1.scratch.delayed.length := by
          change (eoff + 1#64).toNat < del1.length
          have := BitVec.toNat_add eoff 1#64
          rw [hdl1_len, this, show (1#64).toNat = 1 from rfl,
            Nat.mod_eq_of_lt (by omega : eoff.toNat + 1 < 2 ^ 64)]; omega
        have he2 : (eoff + 2#64).toNat < s1.scratch.delayed.length := by
          change (eoff + 2#64).toNat < del1.length
          have := BitVec.toNat_add eoff 2#64
          rw [hdl1_len, this, show (2#64).toNat = 2 from rfl,
            Nat.mod_eq_of_lt (by omega : eoff.toNat + 2 < 2 ^ 64)]; omega
        have he3 : (eoff + 3#64).toNat < s1.scratch.delayed.length := by
          change (eoff + 3#64).toNat < del1.length
          have := BitVec.toNat_add eoff 3#64
          rw [hdl1_len, this, show (3#64).toNat = 3 from rfl,
            Nat.mod_eq_of_lt (by omega : eoff.toNat + 3 < 2 ^ 64)]; omega
        clear hm1
        c0_hsteps_nogrp
        · c0_hsteps_nogrp
          refine hQ _ _ m ?_ (by simpa only [s1] using hm)
          exact ⟨hlen1.core_ok, { hlen1.scratch_ok with delayed_len_arr := by simp [hdl1_len] }⟩
        · let del2 :=
            (del1.set off.toNat (BitVec.setWidth 32 (BitVec.ofNat 64 s1.scratch.delayed_len &&&
              (1#64 <<< (56 : Nat) - 1#64)))).set (off + 1#64).toNat (BitVec.setWidth 32
              ((BitVec.ofNat 64 s1.scratch.delayed_len &&&
                (1#64 <<< (56 : Nat) - 1#64)) >>> (32 : Nat)))
          let s2 : FullState := { s1 with scratch := { s1.scratch with delayed := del2 } }
          have hdl2_len : del2.length = 3 * c.delayed_cap := by simp [del2, hdl1_len]
          have h2e0 : eoff.toNat < del2.length := by rw [hdl2_len]; omega
          have h2e1 : (eoff + 1#64).toNat < del2.length := by
            have := BitVec.toNat_add eoff 1#64
            rw [hdl2_len, this, show (1#64).toNat = 1 from rfl,
              Nat.mod_eq_of_lt (by omega : eoff.toNat + 1 < 2 ^ 64)]; omega
          have h2e2 : (eoff + 2#64).toNat < del2.length := by
            have := BitVec.toNat_add eoff 2#64
            rw [hdl2_len, this, show (2#64).toNat = 2 from rfl,
              Nat.mod_eq_of_lt (by omega : eoff.toNat + 2 < 2 ^ 64)]; omega
          have h2e3 : (eoff + 3#64).toNat < del2.length := by
            have := BitVec.toNat_add eoff 3#64
            rw [hdl2_len, this, show (3#64).toNat = 3 from rfl,
              Nat.mod_eq_of_lt (by omega : eoff.toNat + 3 < 2 ^ 64)]; omega
          let m_pre := m
          have hm_pre : (FullMem c s2 ⋆ R) m_pre := hm
          refine wp_join_group (fun _ m4 => m_pre = m4) (fun Jd _ m4 hm4 => ?_)
            (fun Jd hJd => ?_)
          · rcases hm4 with rfl; rw [Blocks.get_here]
            c0_hsteps_nogrp
            refine wp_join_group (fun _ m5 => m_pre = m5) (fun Jc _ m5 hm5 => ?_)
              (fun Jc hJc => ?_)
            · rcases hm5 with rfl; rw [Blocks.get_here]
              c0_hsteps_nogrp
              refine wp_join_group (ts := [i64]) (fun (sb, ()) m6 => m_pre = m6)
                (fun Jsb (sb, ()) m6 hm6 => ?_) (fun Jsb hJsb => ?_)
              · rcases hm6 with rfl; rw [Blocks.get_here]
                c0_hsteps_nogrp
                refine wp_join_group
                  (fun _ m7 => ∃ del7 : List (BitVec 32), del7.length = 3 * c.delayed_cap ∧
                    (FullMem c { s1 with scratch := { s1.scratch with
                      delayed := del7 } } ⋆ R) m7)
                  (fun Jse _ m7 ⟨del7, hdl7, hm7⟩ => ?_) (fun Jse hJse => ?_)
                · have h7e0 : eoff.toNat < del7.length := by rw [hdl7]; omega
                  have h7e1 : (eoff + 1#64).toNat < del7.length := by
                    have := BitVec.toNat_add eoff 1#64
                    rw [hdl7, this, show (1#64).toNat = 1 from rfl,
                      Nat.mod_eq_of_lt (by omega : eoff.toNat + 1 < 2 ^ 64)]; omega
                  have h7e2 : (eoff + 2#64).toNat < del7.length := by
                    have := BitVec.toNat_add eoff 2#64
                    rw [hdl7, this, show (2#64).toNat = 2 from rfl,
                      Nat.mod_eq_of_lt (by omega : eoff.toNat + 2 < 2 ^ 64)]; omega
                  have h7e3 : (eoff + 3#64).toNat < del7.length := by
                    have := BitVec.toNat_add eoff 3#64
                    rw [hdl7, this, show (3#64).toNat = 3 from rfl,
                      Nat.mod_eq_of_lt (by omega : eoff.toNat + 3 < 2 ^ 64)]; omega
                  c0_hsteps
                  refine hQ _ _ m ?_ (by simpa only [s1] using hm)
                  exact ⟨hlen1.core_ok, { hlen1.scratch_ok with
                    delayed_len_arr := by simp [hdl7] }⟩
                · c0_hsteps_nogrp
                  · refine wp_join_group (fun _ m7 => m_pre = m7)
                      (fun Jse1 _ m7 hm7 => ?_) (fun Jse1 hJse1 => ?_)
                    · rcases hm7 with rfl
                      c0_hsteps
                      refine hJse _ m ⟨_, ?_, hm⟩
                      simp only [List.length_set]; exact hdl1_len
                    · c0_hsteps
                      · exact hJse1 _ m_pre rfl
                      · exact hJse1 _ m_pre rfl
                  · c0_hsteps
                    refine hJse _ m ⟨_, ?_, hm⟩
                    simp only [List.length_set]; exact hdl1_len
              · c0_hsteps <;> exact hJsb _ m_pre rfl
            · c0_hsteps <;> exact hJc _ m_pre rfl
          · c0_hsteps <;> exact hJd _ m_pre rfl
      · c0_hsteps <;> exact hJeoff _ m1 ⟨rfl, by decide⟩
    · c0_hsteps <;> exact hJoff _ m1 ⟨rfl, by decide⟩

theorem full_dr_allow_m6_wp (Γ : Env) :
    ∀ args m Q X, m6DrAllowSpec args m Q X →
      Func.wp Γ full_dr_allow_m6_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hd_bnd : c.delayed_cap < dimacsBound := c.hdel
  have hdl_len : s.scratch.delayed.length = 3 * c.delayed_cap := hlen.scratch_ok.delayed_len_arr
  c0_hsteps_nogrp
  · exact hQ true
  · exact hQ true
  · have hc_ge : 4 ≤ c.delayed_cap := by
      have hlt : ¬ c.delayed_cap % 2 ^ 64 < (4#64).toNat := by assumption
      rw [Nat.mod_eq_of_lt (by unfold dimacsBound at hd_bnd; omega),
        show (4#64).toNat = 4 from rfl] at hlt
      exact Nat.le_of_not_lt hlt
    refine wp_join_group (fun (eoff, ()) m1 => m = m1 ∧ eoff.toNat ≤ 8)
      (fun Jeoff (eoff, ()) m1 ⟨hm1, heoff⟩ => ?_) (fun Jeoff hJeoff => ?_)
    · rcases hm1 with rfl; rw [Blocks.get_here]; dsimp only
      have he0 : eoff.toNat < s.scratch.delayed.length := by rw [hdl_len]; omega
      have he1 : (eoff + 1#64).toNat < s.scratch.delayed.length := by
        have := BitVec.toNat_add eoff 1#64
        rw [hdl_len, this, show (1#64).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (by omega : eoff.toNat + 1 < 2 ^ 64)]; omega
      have he2 : (eoff + 2#64).toNat < s.scratch.delayed.length := by
        have := BitVec.toNat_add eoff 2#64
        rw [hdl_len, this, show (2#64).toNat = 2 from rfl,
          Nat.mod_eq_of_lt (by omega : eoff.toNat + 2 < 2 ^ 64)]; omega
      have he3 : (eoff + 3#64).toNat < s.scratch.delayed.length := by
        have := BitVec.toNat_add eoff 3#64
        rw [hdl_len, this, show (3#64).toNat = 3 from rfl,
          Nat.mod_eq_of_lt (by omega : eoff.toNat + 3 < 2 ^ 64)]; omega
      c0_hsteps_nogrp
      refine wp_join_group (fun _ m2 => m = m2) (fun Jsd _ m2 hm2 => ?_)
        (fun Jsd hJsd => ?_)
      · rcases hm2 with rfl; rw [Blocks.get_here]; dsimp only
        c0_hsteps
        · exact hQ true
        · exact hQ _
      · c0_hsteps <;> exact hJsd _ m rfl
    · c0_hsteps <;> exact hJeoff _ m ⟨rfl, by decide⟩

/-! ## 4. `full_decide_m6` `Func.wp` proof against canonical `Full.fullDecideSpec` -/

theorem full_decide_m6_wp (Γ : Env)
    (hNextDec : ∀ args m Q X, Full.fullNextDecVarSpec args m Q X →
      Γ "full_next_dec_var" [i64] [i64] args m Q X)
    (hAssign : ∀ args m Q X, Full.fullAssignSpec args m Q X →
      Γ "full_assign" [i64, i32, i32] [] args m Q X)
    (hDrInit : ∀ args m Q X, m6DrInitSpec args m Q X →
      Γ "full_dr_init_m6" [i64] [] args m Q X) :
    ∀ args m Q X, Full.fullDecideSpec args m Q X →
      Func.wp Γ full_decide_m6_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  c0_hsteps_nogrp
  c0_call hNextDec
  refine ⟨c, s, R, rfl, hinv.lengths, hm, fun ⟨chosen, ⟨⟩⟩ s1 m1 hs1_core hs1_safe hch hm1 => ?_⟩
  dsimp only [Full.fullSafetySlice_mem, Full.fullSafetySlice_coreProj,
    Full.fullSafetySlice_safe] at hs1_core hs1_safe hm1 hch ⊢
  clear m hm
  have hcs1 : s1.core = s.core := @Full.fullCoreState_agrees_with_scratch c s s1 hs1_core
  have hinv1 : FullCoreInv c F0 s1 := hinv.with_scratch hs1_safe hs1_core
  rcases s1 with ⟨c1, sc1⟩; dsimp only at hcs1; subst hcs1
  have hcl1 := hinv1.lengths.core_ok
  have hsc1_ok := hinv1.lengths.scratch_ok
  have hcv1 : s.core.cur_vars ≤ c.max_vars := hcl1.cur_vars_le
  have hph1 := hsc1_ok.phases_len; have hptgt1 := hsc1_ok.phases_target_len
  have hftrl1 : s.core.frame_trail.length = c.max_vars + 1 := hcl1.frame_trail_len
  have hfdec1 : s.core.frame_dec.length = c.max_vars + 1 := hcl1.frame_dec_len
  c0_hsteps_nogrp
  · exact hQ 0#64 s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl s.core.trail_pos
      s.core.frame_trail s.core.frame_dec s.core.trail_end s.core.cur_level s.core.unassigned
      s.core.unflushed sc1 m1 hinv1 hch.1 (Or.inl rfl) (fun _ => ⟨rfl, rfl⟩)
      (fun h1 => by cases h1) hm1
  · have hch_ne : chosen ≠ 0xFFFFFFFFFFFFFFFF#64 := hc
    obtain ⟨hv_lt, hval0⟩ := hch.2.resolve_left hch_ne
    have hch_lt_max : chosen.toNat < c.max_vars := by omega
    have hch_lt30 : chosen.toNat < 2 ^ 30 := by omega
    c0_hsteps_nogrp
    refine wp_join_group (fun (dph, ()) m2 => m1 = m2) ?_ ?_
    · rintro _ ⟨dph, ⟨⟩⟩ _ hm2; rcases hm2 with rfl
      c0_hsteps_nogrp
      refine wp_join_group (fun (lit, ()) m3 =>
        m1 = m3 ∧ (lit.toNat = 2 * chosen.toNat ∨ lit.toNat = 2 * chosen.toNat + 1)) ?_ ?_
      · rintro _ ⟨lit, ⟨⟩⟩ _ ⟨hm3, hlit_eq⟩; rcases hm3 with rfl
        have hnlvl_nat : (BitVec.ofNat 64 s.core.cur_level + 1#64).toNat =
            s.core.cur_level + 1 := by
          have hte1 : s.core.trail_end ≤ s.core.cur_vars := hcl1.trail_end_le
          obtain ⟨_, hw⟩ := hinv1.witness
          have hcl1_le : s.core.cur_level ≤ s.core.trail_end := hw.cur_level_le
          bv_omega
        c0_hsteps_nogrp
        · exact hQ 0#64 s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl s.core.trail_pos
            s.core.frame_trail s.core.frame_dec s.core.trail_end s.core.cur_level s.core.unassigned
            s.core.unflushed sc1 m1 hinv1 hch.1 (Or.inl rfl) (fun _ => ⟨rfl, rfl⟩)
            (fun h1 => by cases h1) hm1
        · have hnlvl_le : s.core.cur_level + 1 ≤ c.max_vars := by
            have hte1 : s.core.trail_end ≤ s.core.cur_vars := hcl1.trail_end_le
            obtain ⟨_, hw⟩ := hinv1.witness
            have hcl1_le : s.core.cur_level ≤ s.core.trail_end := hw.cur_level_le
            have hlt : ¬ c.max_vars % 2 ^ 64 <
                (s.core.cur_level + (1#64).toNat) % 2 ^ 64 := hc
            rw [Nat.mod_eq_of_lt (by omega), show (1#64).toNat = 1 from rfl,
              Nat.mod_eq_of_lt (by omega)] at hlt
            omega
          have ⟨_, hun, hte_lt, _⟩ := Full.full_decide_preserves_fullCore hinv1 hsc1_ok
            hcl1.flags_len hv_lt hval0 hlit_eq (flags' := s.core.flags)
            (unas' := s.core.unassigned) (unfl' := s.core.unflushed)
          let nlvl := s.core.cur_level + 1
          let ftrl' := s.core.frame_trail.set nlvl (BitVec.ofNat 32 s.core.trail_end)
          let fdec' := s.core.frame_dec.set nlvl lit
          let s2 : FullState :=
            { core := { s.core with frame_trail := ftrl', frame_dec := fdec', cur_level := nlvl }
              scratch := sc1 }
          have hlen2 : s2.LengthsOk c :=
            ⟨{ hcl1 with
                frame_trail_len := by simp [s2, ftrl', hftrl1]
                frame_dec_len := by simp [s2, fdec', hfdec1] }, hsc1_ok⟩
          have hm2' : (FullMem c s2 ⋆ R) m := by
            have hte_le : s.core.trail_end ≤ s.core.cur_vars := hcl1.trail_end_le
            have hte_bv : (BitVec.ofNat 64 s.core.trail_end).setWidth 32 =
                BitVec.ofNat 32 s.core.trail_end := by
              apply BitVec.eq_of_toNat_eq
              rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt (by omega : s.core.trail_end < 2 ^ 64),
                Nat.mod_eq_of_lt (by omega : s.core.trail_end < 2 ^ 32)]
            have hnlvl_nat' : (BitVec.ofNat 64 s.core.cur_level + 1).toNat =
                s.core.cur_level + 1 := hnlvl_nat
            simpa only [s2, ftrl', fdec', nlvl, hnlvl_nat', hte_bv] using hm
          have hng : ¬ (s2.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ s2.core.trail_end ∨
              s2.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8) := by
            change ¬ (s.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ s.core.trail_end ∨
              s.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8)
            simp only [hun, ne_eq, not_true_eq_false, or_false]
            have hte_lt' : s.core.trail_end < s.core.cur_vars := hte_lt
            omega
          c0_call hAssign
          refine ⟨c, s2, R, rfl, hlen2, by dsimp [s2, nlvl]; omega, hm2', ?_⟩
          simp only [hng, ↓reduceIte]
          intro flags' unas' phases' m3 hfl_l hph_l hm3
          clear hm
          have hsc3 : ({ sc1 with phases := phases' } : FullScratch).LengthsOk c :=
            { hsc1_ok with phases_len := hph_l }
          have ⟨hinv3, _, _, _⟩ := Full.full_decide_preserves_fullCore hinv1 hsc3 hfl_l
            hv_lt hval0 hlit_eq (flags' := flags') (unas' := unas') (unfl' := s.core.unflushed)
          have hnl_ne0 : nlvl ≠ 0 := by dsimp [nlvl]; omega
          have hff : (4294967295 : BitVec 32) = 0xFFFFFFFF#32 := rfl
          let s3 : FullState :=
            { core := { s.core with
                vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8,
                flags := flags', lvl := s.core.lvl.set (lit.toNat / 2) (BitVec.ofNat 32 nlvl),
                rsns := s.core.rsns.set (lit.toNat / 2) 0xFFFFFFFF#32,
                trl := s.core.trl.set s.core.trail_end lit,
                trail_pos := s.core.trail_pos.set (lit.toNat / 2)
                  (BitVec.ofNat 32 s.core.trail_end),
                frame_trail := ftrl', frame_dec := fdec', trail_end := s.core.trail_end + 1,
                cur_level := nlvl, unassigned := unas' },
              scratch := { sc1 with phases := phases' } }
          have hm3' : (FullMem c s3 ⋆ R) m3 := by
            simpa only [s3, s2, hnl_ne0, ↓reduceIte, hff] using hm3
          have hinv3' : FullCoreInv c F0 s3 := by
            simpa only [s3, nlvl, hnl_ne0, ↓reduceIte] using hinv3
          c0_hsteps_nogrp
          c0_call hDrInit
          refine ⟨c, s3, R, rfl, hinv3'.lengths, hm3', fun dl4 del4 m4 hlen4 hm4 => ?_⟩
          dsimp only; clear hm3
          let s4 : FullState :=
            { s3 with scratch := { s3.scratch with delayed_len := dl4, delayed := del4 } }
          have hinv4 : FullCoreInv c F0 s4 := hinv3'.with_fuel_scratch_spec hlen4 rfl
          c0_hsteps
          · refine hQ 1#64 s3.core.vals flags' s3.core.lvl s3.core.rsns s3.core.trl
              s3.core.trail_pos ftrl' fdec' (s.core.trail_end + 1) nlvl unas' s.core.unflushed
              _ m ?_ ?_ (Or.inr rfl) (fun h0 => by cases h0) (fun _ => ⟨rfl, rfl⟩) hm
            · exact hinv4.with_fuel_scratch_spec ⟨hlen4.core_ok,
                { hlen4.scratch_ok with walk_vals_len := hlen4.scratch_ok.walk_vals_len }⟩ rfl
            · exact ⟨hch.1.1, hch.1.2⟩
          · refine hQ 1#64 s3.core.vals flags' s3.core.lvl s3.core.rsns s3.core.trl
              s3.core.trail_pos ftrl' fdec' (s.core.trail_end + 1) nlvl unas' s.core.unflushed
              s4.scratch m4 hinv4 ⟨hch.1.1, hch.1.2⟩ (Or.inr rfl) (fun h0 => by cases h0)
              (fun _ => ⟨rfl, rfl⟩) hm4
      · intro Jlit hJlit; c0_hsteps
        · exact hJlit ((chosen <<< (1 : Nat)).setWidth 32 ||| 1#32, ()) m1
            ⟨rfl, Or.inr (bv32_dec_lit_odd hch_lt30)⟩
        · exact hJlit ((chosen <<< (1 : Nat)).setWidth 32, ()) m1
            ⟨rfl, Or.inl (bv32_dec_lit_even hch_lt30)⟩
    · intro Jdph hJdph; c0_hsteps
      · exact hJdph _ m1 rfl
      · exact hJdph _ m1 rfl
      · exact hJdph _ m1 rfl

end LeanQbe.T.Examples.Kissat.FullM6MinShrink
