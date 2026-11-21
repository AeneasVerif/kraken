module

public import LeanQbe.T.Examples.Kissat.FullKittenLemmas1

/-!
# Kissat `D-Full` Scratch `kitten` Helper `Func.wp` Proofs (`Part 2`)

Proves parametric `(Γ : Env)` `Func.wp` contracts for the `6` foundational `full_kitten_*`
functions (`6/15`):
- `full_kitten_watch_wp`
- `full_kitten_assign_wp`
- `full_kitten_mtf_wp`
- `full_kitten_backtrack_wp`
- `full_kitten_init_wp`
- `full_kitten_add_clause_wp`
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

open scoped KittenMemTactics KittenMemATactics KittenProjTactics

/-! ## 5. Parametric `Func.wp` Proofs (`watch`, `assign`, `mtf`, `bt`, `init`, `add_clause`) -/

private theorem kitten_shl1_toNat (x : BitVec 32) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat % 2 ^ 32 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

/-- Parametric `Func.wp` proof for `full_kitten_watch`. -/
theorem full_kitten_watch_wp (Γ : Env) :
    ∀ args m Q X, fullKittenWatchSpec args m Q X → Func.wp Γ full_kitten_watch_body args m Q X := by
  rintro ⟨kPtr, cid, l0, l1, ⟨⟩⟩ m Q X ⟨acap, ks, R, hsh, hcap, hnv, hcid, hl0, hl1, hm, hQ⟩
  have hmc : kMaxCl ≤ 896 := Nat.le_refl _
  have hmv : kMaxV ≤ 128 := Nat.le_refl _
  have h0 := bv32_cid_w0 hcid hmc
  have h1 := bv32_cid_w1 hcid hmc
  have hw0_wrap : (cid <<< (1 : Nat)).toNat < 2 ^ 28 := by
    have := h0.2; unfold kMaxCl at this; omega
  have hw1_wrap : ((cid <<< (1 : Nat)) ||| (1 : BitVec 32)).toNat < 2 ^ 28 := by
    have := h1.2; unfold kMaxCl at this; omega
  have hw0_len : (cid <<< (1 : Nat)).toNat < 1792 := by
    have := h0.2; unfold kMaxCl at this; omega
  have hw1_len : ((cid <<< (1 : Nat)) ||| (1 : BitVec 32)).toNat < 1792 := by
    have := h1.2; unfold kMaxCl at this; omega
  have hl0_wrap : l0.toNat < 2 ^ 28 := by unfold kMaxV at hnv; omega
  have hl1_wrap : l1.toNat < 2 ^ 28 := by unfold kMaxV at hnv; omega
  have hl0_len : l0.toNat < 256 := by unfold kMaxV at hnv; omega
  have hl1_len : l1.toNat < 256 := by unfold kMaxV at hnv; omega
  have hmA := kittenMem_to_amem hsh hm; clear hm
  c0_hsteps!
  obtain ⟨_, hm'⟩ := kittenMemA_to_mem hm
  refine hQ _ (Eq.mp (congrArg (fun x => (KittenMem kPtr x ⋆ R) _) ?_) hm')
  dsimp only [kittenWatchStep, kittenWatchStep0]
  kstate_ext <;> try rfl

/-- Parametric `Func.wp` proof for `full_kitten_assign`. -/
theorem full_kitten_assign_wp (Γ : Env) :
    ∀ args m Q X, fullKittenAssignSpec args m Q X →
      Func.wp Γ full_kitten_assign_body args m Q X := by
  rintro ⟨kPtr, lit, rsn, ⟨⟩⟩ m Q X ⟨acap, ks, R, hsh, hcap, hnv, hlit, hte, hm, hQ⟩
  have hmv : kMaxV ≤ 128 := Nat.le_refl _
  obtain ⟨hv_eq, hv_lt⟩ := bv32_lit_div2_bv hlit
  obtain ⟨hn_eq, hn_lt⟩ := bv32_xor1_eq_litNeg hlit
  have hv_max : (lit >>> (1 : Nat)).toNat < 2 ^ 28 := by unfold kMaxV at hnv; omega
  have hl_wrap : lit.toNat < 2 ^ 28 := by unfold kMaxV at hnv; omega
  have hnl_wrap : (lit ^^^ (1 : BitVec 32)).toNat < 2 ^ 28 := by unfold kMaxV at hnv; omega
  have hte_wrap : ks.trl_end.toNat < 2 ^ 28 := by unfold kMaxV at hnv; omega
  have hl_len : lit.toNat < 256 := by unfold kMaxV at hnv; omega
  have hnl_len : (lit ^^^ (1 : BitVec 32)).toNat < 256 := by unfold kMaxV at hnv; omega
  have hv_128 : (lit >>> (1 : Nat)).toNat < 128 := by unfold kMaxV at hnv; omega
  have hte_128 : ks.trl_end.toNat < 128 := by unfold kMaxV at hnv; omega
  have hfl_len : (lit >>> (1 : Nat)).toNat < ks.flags.length := by
    rw [hsh.flags_len]; exact hv_128
  have hmA := kittenMem_to_amem hsh hm; clear hm
  c0_hsteps_nogrp
  let ksPre := ((((((ks.putArr .vals lit.toNat (1 : BitVec 32)).putArr .vals
    (lit ^^^ (1 : BitVec 32)).toNat (2 : BitVec 32)).putArr .lvlArr
    (lit >>> (1 : Nat)).toNat ks.lvl).putArr .rsn (lit >>> (1 : Nat)).toNat rsn).putArr
    .trl ks.trl_end.toNat lit).putHdr .trl_end (ks.trl_end + (1 : BitVec 32)))
  let ksU :=
    if (0 : BitVec 32).ult ks.unass then ksPre.putHdr .unass (ks.unass - 1#32) else ksPre
  have hult_iff : (0 : BitVec 32).ult ks.unass = true ↔ 0 < ks.unass.toNat := decide_eq_true_iff
  have hpre_un : ksPre.unass = ks.unass := by dsimp only [ksPre]; kp_field
  refine wp_join0 (fun m' => (KittenMemA kPtr acap ksU ⋆ R) m') ?_ ?_
  · intro J m' hm'
    c0_hsteps!
    · obtain ⟨_, hm''⟩ := kittenMemA_to_mem hm
      refine hQ _ (Eq.mp (congrArg (fun x => (KittenMem kPtr x ⋆ R) _) ?_) hm'')
      have hcond : (lit &&& 1#32) ≠ 0#32 := by simpa [bv32_one_eq] using ‹_›
      by_cases hu : (0 : BitVec 32).ult ks.unass = true
      · have hu_nat : 0 < ks.unass.toNat := hult_iff.mp hu
        dsimp only [ksU, ksPre, kittenAssignStep]
        simp only [hu, ite_true, hu_nat, hcond, ne_eq, not_false_eq_true]
        kstate_ext <;> simp [hv_eq]
      · have hu_nat : ¬ (0 < ks.unass.toNat) := fun hp => hu (hult_iff.mpr hp)
        dsimp only [ksU, ksPre, kittenAssignStep]
        simp only [hu, ite_false, hu_nat, hcond, ne_eq, not_false_eq_true, ite_true]
        kstate_ext <;> simp [hv_eq]
    · obtain ⟨_, hm''⟩ := kittenMemA_to_mem hm
      refine hQ _ (Eq.mp (congrArg (fun x => (KittenMem kPtr x ⋆ R) _) ?_) hm'')
      · have hcond : (lit &&& 1#32) = 0#32 := by simpa [bv32_one_eq] using ‹_›
        by_cases hu : (0 : BitVec 32).ult ks.unass = true
        · have hu_nat : 0 < ks.unass.toNat := hult_iff.mp hu
          dsimp only [ksU, ksPre, kittenAssignStep]
          simp only [hu, ite_true, hu_nat, hcond, ne_eq, not_true_eq_false, ite_false]
          kstate_ext <;> simp [hv_eq]
        · have hu_nat : ¬ (0 < ks.unass.toNat) := fun hp => hu (hult_iff.mpr hp)
          dsimp only [ksU, ksPre, kittenAssignStep]
          simp only [hu, ite_false, hu_nat, hcond, ne_eq, not_true_eq_false]
          kstate_ext <;> simp [hv_eq]
  · intro J hJ
    c0_hsteps!
    · have hu : (0 : BitVec 32).ult ks.unass = true := by
        apply hult_iff.mpr
        revert hc; kp_field; intro hc; bv_omega
      refine hJ _ (Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ R) _) ?_) hm)
      dsimp only [ksU, ksPre]; simp only [hu, ite_true]
      kstate_ext <;> (first | rfl | (simp only [hv_eq, bv32_one_eq]; rfl))
    · have hu : (0 : BitVec 32).ult ks.unass = false := by
        apply Bool.eq_false_iff.mpr
        intro h
        have hpos := hult_iff.mp h
        revert hc; kp_field; intro hc; bv_omega
      refine hJ _ (Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ R) _) ?_) hm)
      dsimp only [ksU, ksPre]; simp only [hu, Bool.false_eq_true, ite_false]
      kstate_ext <;> (first | rfl | (simp only [hv_eq, bv32_one_eq]; rfl))

private def MtfSt (acap : Nat) (ks ks' : KittenState) : Prop :=
  ks'.ShapesOk acap ∧
  ∃ qf ql qs qst qp qn qsa,
    ks' = { ks with qfirst := qf, qlast := ql, qsearch := qs, qstamp := qst,
                    qprev := qp, qnext := qn, qstampArr := qsa }

private theorem MtfSt.base {acap : Nat} {ks : KittenState} (hsh : ks.ShapesOk acap) :
    MtfSt acap ks ks :=
  ⟨hsh, ks.qfirst, ks.qlast, ks.qsearch, ks.qstamp, ks.qprev, ks.qnext, ks.qstampArr,
    by cases ks; rfl⟩

private theorem MtfSt.sh {acap : Nat} {ks ks' : KittenState} (r : MtfSt acap ks ks') :
    ks'.ShapesOk acap := r.1

private theorem MtfSt.nv_eq {acap : Nat} {ks ks' : KittenState} (r : MtfSt acap ks ks') :
    ks'.nv = ks.nv := by rcases r.2 with ⟨_, _, _, _, _, _, _, rfl⟩; rfl

private theorem MtfSt.putQfirst {acap : Nat} {ks ks' : KittenState}
    (r : MtfSt acap ks ks') (v : BitVec 32) : MtfSt acap ks (ks'.putHdr .qfirst v) := by
  rcases r with ⟨hsh, qf, ql, qs, qst, qp, qn, qsa, rfl⟩
  exact ⟨hsh.putHdr .qfirst v, v, ql, qs, qst, qp, qn, qsa, rfl⟩

private theorem MtfSt.putQlast {acap : Nat} {ks ks' : KittenState}
    (r : MtfSt acap ks ks') (v : BitVec 32) : MtfSt acap ks (ks'.putHdr .qlast v) := by
  rcases r with ⟨hsh, qf, ql, qs, qst, qp, qn, qsa, rfl⟩
  exact ⟨hsh.putHdr .qlast v, qf, v, qs, qst, qp, qn, qsa, rfl⟩

private theorem MtfSt.putQsearch {acap : Nat} {ks ks' : KittenState}
    (r : MtfSt acap ks ks') (v : BitVec 32) : MtfSt acap ks (ks'.putHdr .qsearch v) := by
  rcases r with ⟨hsh, qf, ql, qs, qst, qp, qn, qsa, rfl⟩
  exact ⟨hsh.putHdr .qsearch v, qf, ql, v, qst, qp, qn, qsa, rfl⟩

private theorem MtfSt.putQstamp {acap : Nat} {ks ks' : KittenState}
    (r : MtfSt acap ks ks') (v : BitVec 32) : MtfSt acap ks (ks'.putHdr .qstamp v) := by
  rcases r with ⟨hsh, qf, ql, qs, qst, qp, qn, qsa, rfl⟩
  exact ⟨hsh.putHdr .qstamp v, qf, ql, qs, v, qp, qn, qsa, rfl⟩

private theorem MtfSt.putQprev {acap : Nat} {ks ks' : KittenState}
    (r : MtfSt acap ks ks') (i : Nat) (v : BitVec 32) :
    MtfSt acap ks (ks'.putArr .qprev i v) := by
  rcases r with ⟨hsh, qf, ql, qs, qst, qp, qn, qsa, rfl⟩
  exact ⟨hsh.putArr .qprev i v, qf, ql, qs, qst, qp.set i v, qn, qsa, rfl⟩

private theorem MtfSt.putQnext {acap : Nat} {ks ks' : KittenState}
    (r : MtfSt acap ks ks') (i : Nat) (v : BitVec 32) :
    MtfSt acap ks (ks'.putArr .qnext i v) := by
  rcases r with ⟨hsh, qf, ql, qs, qst, qp, qn, qsa, rfl⟩
  exact ⟨hsh.putArr .qnext i v, qf, ql, qs, qst, qp, qn.set i v, qsa, rfl⟩

private theorem MtfSt.putQstampArr {acap : Nat} {ks ks' : KittenState}
    (r : MtfSt acap ks ks') (i : Nat) (v : BitVec 32) :
    MtfSt acap ks (ks'.putArr .qstampArr i v) := by
  rcases r with ⟨hsh, qf, ql, qs, qst, qp, qn, qsa, rfl⟩
  exact ⟨hsh.putArr .qstampArr i v, qf, ql, qs, qst, qp, qn, qsa.set i v, rfl⟩

private theorem MtfSt.finishA {acap : Nat} {ks ks' : KittenState} {kPtr : BitVec 64}
    {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post []}
    (hQ : ∀ qf' ql' qs' qst' qp' qn' qsa' m',
      let ks' : KittenState :=
        { ks with qfirst := qf', qlast := ql', qsearch := qs', qstamp := qst',
                  qprev := qp', qnext := qn', qstampArr := qsa' }
      ks'.ShapesOk acap → (KittenMem kPtr ks' ⋆ R) m' → Q () m')
    (r : MtfSt acap ks ks') (hm' : (KittenMemA kPtr acap ks' ⋆ R) m') : Q () m' := by
  obtain ⟨hsh, hm''⟩ := kittenMemA_to_mem hm'
  rcases r with ⟨_, qf, ql, qs, qst, qp, qn, qsa, rfl⟩
  exact hQ qf ql qs qst qp qn qsa m' hsh hm''

/-- Parametric `Func.wp` proof for `full_kitten_mtf`. -/
theorem full_kitten_mtf_wp (Γ : Env) :
    ∀ args m Q X, fullKittenMtfSpec args m Q X → Func.wp Γ full_kitten_mtf_body args m Q X := by
  rintro ⟨kPtr, v, ⟨⟩⟩ m Q X ⟨acap, ks, R, hsh, hcap, hnv, hm, hQ⟩
  have hmv : kMaxV ≤ 128 := Nat.le_refl _
  have hmA := kittenMem_to_amem hsh hm; clear hm
  c0_hsteps_nogrp
  · exact hQ _ _ _ _ _ _ _ m hsh (kittenMemA_to_mem hmA).2
  · exact hQ _ _ _ _ _ _ _ m hsh (kittenMemA_to_mem hmA).2
  · have hv_lt : v.toNat < ks.nv.toNat := by bv_omega
    have hv_wrap : v.toNat < 2 ^ 28 := by unfold kMaxV at hnv; omega
    have hv_128 : v.toNat < 128 := by unfold kMaxV at hnv; omega
    have hv2_lt : (v <<< (1 : Nat)).toNat < 2 * ks.nv.toNat := by
      have := kitten_shl1_toNat v; unfold kMaxV at hnv; omega
    have hv2_wrap : (v <<< (1 : Nat)).toNat < 2 ^ 28 := by unfold kMaxV at hnv; omega
    have hv2_256 : (v <<< (1 : Nat)).toNat < 256 := by unfold kMaxV at hnv; omega
    c0_hsteps_nogrp
    let pv := ks.qprev[v.toNat]?.getD 0#32
    let nxt := ks.qnext[v.toNat]?.getD 0#32
    refine wp_join_state0 (α := KittenState)
      (fun st m' => MtfSt acap ks st ∧ (KittenMemA kPtr acap st ⋆ R) m') ?_ ?_
    · intro J1 ks1 m1 ⟨hr1, hm1⟩
      have hnv1 : ks1.nv = ks.nv := hr1.nv_eq
      c0_hsteps_nogrp
      refine wp_join_state0 (α := KittenState)
        (fun st m' => MtfSt acap ks st ∧ (KittenMemA kPtr acap st ⋆ R) m') ?_ ?_
      · intro J2 ks2 m2 ⟨hr2, hm2⟩
        have hnv2 : ks2.nv = ks.nv := hr2.nv_eq
        c0_hsteps_nogrp
        refine wp_join_state0 (α := KittenState)
          (fun st m' => MtfSt acap ks st ∧ (KittenMemA kPtr acap st ⋆ R) m') ?_ ?_
        · intro J3 ks3 m3 ⟨hr3, hm3⟩
          have hnv3 : ks3.nv = ks.nv := hr3.nv_eq
          c0_hsteps_nogrp
          let ol := ks3.qlast
          refine wp_join_state0 (α := KittenState)
            (fun st m' => MtfSt acap ks st ∧ (KittenMemA kPtr acap st ⋆ R) m') ?_ ?_
          · intro J4 ks4 m4 ⟨hr4, hm4⟩
            c0_hsteps_nogrp
            refine wp_join_state0 (α := KittenState)
              (fun st m' => MtfSt acap ks st ∧ (KittenMemA kPtr acap st ⋆ R) m') ?_ ?_
            · intro J5 ks5 m5 ⟨hr5, hm5⟩
              c0_hsteps!
              · exact (hr5.putQsearch v).finishA hQ hm
              · exact hr5.finishA hQ hm5
            · intro J5 hJ5
              c0_hsteps!
              · exact hJ5 _ _ ⟨(hr4.putQstamp _).putQstampArr _ _, hm⟩
              · exact hJ5 _ _ ⟨hr4, hm4⟩
          · intro J4 hJ4
            c0_hsteps!
            · exact hJ4 _ _ ⟨(((hr3.putQprev v.toNat ol).putQnext v.toNat
                0xFFFFFFFF#32).putQlast v).putQfirst v, hm⟩
            · have hol_lt : ol.toNat < ks.nv.toNat := by dsimp only [ol]; rw [← hnv3]; bv_omega
              have hol_wrap : ol.toNat < 2 ^ 28 := by unfold kMaxV at hnv; omega
              have hol_128 : ol.toNat < 128 := by unfold kMaxV at hnv; omega
              c0_hsteps!
              exact hJ4 _ _ ⟨(((hr3.putQprev v.toNat ol).putQnext v.toNat
                0xFFFFFFFF#32).putQlast v).putQnext ol.toNat v, hm⟩
        · intro J3 hJ3
          c0_hsteps!
          · exact hJ3 _ _ ⟨hr2.putQlast pv, hm⟩
          · have hn_lt : nxt.toNat < ks.nv.toNat := by dsimp only [nxt]; rw [← hnv2]; bv_omega
            have hn_wrap : nxt.toNat < 2 ^ 28 := by unfold kMaxV at hnv; omega
            have hn_128 : nxt.toNat < 128 := by unfold kMaxV at hnv; omega
            c0_hsteps!
            exact hJ3 _ _ ⟨hr2.putQprev nxt.toNat pv, hm⟩
      · intro J2 hJ2
        c0_hsteps!
        · exact hJ2 _ _ ⟨hr1.putQfirst nxt, hm⟩
        · have hp_lt : pv.toNat < ks.nv.toNat := by dsimp only [pv]; rw [← hnv1]; bv_omega
          have hp_wrap : pv.toNat < 2 ^ 28 := by unfold kMaxV at hnv; omega
          have hp_128 : pv.toNat < 128 := by unfold kMaxV at hnv; omega
          c0_hsteps!
          exact hJ2 _ _ ⟨hr1.putQnext pv.toNat nxt, hm⟩
    · intro J1 hJ1
      c0_hsteps!
      · exact hJ1 _ _ ⟨MtfSt.base hsh |>.putQsearch pv, hm⟩
      · exact hJ1 _ _ ⟨MtfSt.base hsh |>.putQsearch nxt, hm⟩
      · exact hJ1 _ _ ⟨MtfSt.base hsh, hmA⟩
      · exact hJ1 _ _ ⟨MtfSt.base hsh, hmA⟩
      · exact hJ1 _ _ ⟨MtfSt.base hsh, hmA⟩

/-- Parametric `Func.wp` proof for `full_kitten_backtrack`. -/
theorem full_kitten_backtrack_wp (Γ : Env) :
    ∀ args m Q X, fullKittenBacktrackSpec args m Q X →
      Func.wp Γ full_kitten_backtrack_body args m Q X := by
  rintro ⟨kPtr, target_lvl, ⟨⟩⟩ m Q X ⟨acap, ks, R, hinv, hsync_below, hm, hQ⟩
  have hnv := hinv.clauses.nv_le
  have hsh := hinv.shapes
  have hmA := kittenMem_to_amem hsh hm; clear hm
  c0_hsteps_nogrp
  refine wp_join_state1 (fun st : BitVec 32 => st)
    (fun _ m' => (KittenMemA kPtr acap ks ⋆ R) m') ?_ ?_
  · intro J0 best_st m0 hm0
    refine wp_while_break_state
      (β := BitVec 32 × BitVec 32 × KittenState)
      (fun bst => (bst.1, bst.2.1, ()))
      (fun bst m' =>
        BtLoopInv acap ks target_lvl bst.1 bst.2.2 ∧
        (bst.1 = 0#32 ∨
          ∃ i < bst.1.toNat, i = bst.1.toNat - 1 ∧
            (bst.2.2.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
              target_lvl.toNat) ∧
        (KittenMemA kPtr acap bst.2.2 ⋆ R) m')
      (α := BitVec 32 × BitVec 32 × KittenState)
      (fun st => (st.1, st.2.1, ()))
      (fun st => st.1.toNat)
      (fun st m' => BtLoopInv acap ks target_lvl st.1 st.2.2 ∧
        (KittenMemA kPtr acap st.2.2 ⋆ R) m')
      ?_ ?_ ?_
    · rintro B ⟨te, _best_st, st⟩ m' ⟨hbt, hexit, hm'⟩
      dsimp only at hbt hexit hm'
      c0_hsteps_nogrp
      let stProp := if te.toNat < st.prop.toNat then (st.putHdr .trl_end te).putHdr .prop te
        else st.putHdr .trl_end te
      refine wp_join0 (fun m'' => (KittenMemA kPtr acap stProp ⋆ R) m'') ?_ ?_
      · intro Jf m'' hm''
        c0_hsteps!
        obtain ⟨_, hmFin⟩ := kittenMemA_to_mem hm
        have hfin := bt_loopInv_finish hinv hbt hsync_below hexit
        have heq_st : stProp.putHdr .lvl target_lvl =
            ((st.putHdr .trl_end te).putHdr .prop
              (if te.toNat < st.prop.toNat then te else st.prop)).putHdr .lvl target_lvl := by
          dsimp only [stProp]
          by_cases hp : te.toNat < st.prop.toNat <;> simp only [hp, ite_true, ite_false] <;>
            kstate_ext
        rw [heq_st] at hmFin
        rcases hfin with ⟨h1, h2, h3, h4, h5, h6, h7⟩
        have h8 : ∀ i < ks.trl_end.toNat,
            (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
              target_lvl.toNat →
            i < (((st.putHdr .trl_end te).putHdr .prop
              (if te.toNat < st.prop.toNat then te else st.prop)).putHdr .lvl
              target_lvl).trl_end.toNat := by
          intro i hi hle
          have hte : (((st.putHdr .trl_end te).putHdr .prop
              (if te.toNat < st.prop.toNat then te else st.prop)).putHdr .lvl
              target_lvl).trl_end = te := by kp_field
          rw [hte]
          rcases Nat.lt_or_ge i te.toNat with hlt | hge
          · exact hlt
          · exfalso
            have := hbt.popped_gt i hge hi
            omega
        exact hQ _ _ h1 h2 h3 h4 h5 h6 h7 h8 hmFin
      · intro Jf hJf
        have hpr_eq : (st.putHdr .trl_end te).prop = st.prop := by kp_field
        c0_hsteps!
        · apply hJf _
          have hp : te.toNat < st.prop.toNat := by rw [← hpr_eq]; bv_omega
          simpa [stProp, hp] using hm
        · apply hJf _
          have hp : ¬ te.toNat < st.prop.toNat := by rw [← hpr_eq]; bv_omega
          simpa [stProp, hp] using hm
    · rintro B L ⟨te, bst, st⟩ m' hB hL ⟨hbt, hm'⟩
      dsimp only at hbt hm'
      c0_hsplit
      · have hpos : 0 < te.toNat := by bv_omega
        have hte1_lt : te.toNat - 1 < ks.trl_end.toNat := by have := hbt.te_le; omega
        have hte1_wrap : te.toNat - 1 < 2 ^ 28 := by
          have := hinv.assign.trl_end_le; have := hbt.te_le; unfold kMaxV at hnv; omega
        have hte1_128 : te.toNat - 1 < 128 := by
          have := hinv.assign.trl_end_le; have := hbt.te_le; unfold kMaxV at hnv; omega
        have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
          rw [hsh.trl_len]; have := hinv.assign.trl_end_le; unfold kMaxV at hnv; omega
        let lit := ks.trl[te.toNat - 1]'(by omega)
        have hlit_get : st.trl[te.toNat - 1]?.getD 0#32 = lit := by
          rw [hbt.trl_eq, List.getElem?_eq_getElem (by omega : te.toNat - 1 < ks.trl.length),
            Option.getD_some]
        have hlit_lt : lit.toNat < 2 * ks.nv.toNat := by
          have hm1 := mem_kittenTrailLits_of_lt (i := te.toNat - 1) hte1_lt htrl_len
          rw [List.getElem?_eq_getElem (by omega : te.toNat - 1 < ks.trl.length),
            Option.getD_some] at hm1
          exact hinv.assign.trl_lt lit.toNat hm1
        obtain ⟨hv_eq, hv_lt⟩ := bv32_lit_div2_bv hlit_lt
        obtain ⟨hn_eq, hn_lt⟩ := bv32_xor1_eq_litNeg hlit_lt
        have hv_wrap : lit.toNat / 2 < 2 ^ 28 := by unfold kMaxV at hnv; omega
        have hv_128 : lit.toNat / 2 < 128 := by unfold kMaxV at hnv; omega
        have hv_st_wrap : ((st.trl[te.toNat - 1]?.getD 0#32) >>> (1 : Nat)).toNat < 2 ^ 28 := by
          rw [hlit_get, hv_eq]; exact hv_wrap
        have hv_st_128 : ((st.trl[te.toNat - 1]?.getD 0#32) >>> (1 : Nat)).toNat < 128 := by
          rw [hlit_get, hv_eq]; exact hv_128
        have hl_wrap : lit.toNat < 2 ^ 28 := by unfold kMaxV at hnv; omega
        have hl_256 : lit.toNat < 256 := by unfold kMaxV at hnv; omega
        have hnl_wrap : (lit ^^^ 1#32).toNat < 2 ^ 28 := by
          rw [← bv32_one_eq, hn_eq]; unfold kMaxV at hnv; omega
        have hnl_256 : (lit ^^^ 1#32).toNat < 256 := by
          rw [← bv32_one_eq, hn_eq]; unfold kMaxV at hnv; omega
        have hnl_st_wrap :
            (st.trl[te.toNat - 1]?.getD 0#32 ^^^ (1 : BitVec 32)).toNat < 2 ^ 28 := by
          rw [hlit_get, hn_eq]; unfold kMaxV at hnv; omega
        have hnl_st_256 :
            (st.trl[te.toNat - 1]?.getD 0#32 ^^^ (1 : BitVec 32)).toNat < 256 := by
          rw [hlit_get, hn_eq]; unfold kMaxV at hnv; omega
        c0_hsplit
        · refine hB (te, bst, st) m'
            ⟨hbt, Or.inr ⟨te.toNat - 1, Nat.sub_lt hpos Nat.one_pos, rfl, ?_⟩, hm'⟩
          rw [List.getElem?_eq_getElem (by omega : te.toNat - 1 < ks.trl.length),
            Option.getD_some]
          have hle_raw : (st.lvlArr[(st.trl[te.toNat - 1]?.getD 0#32).toNat / 2]?.getD
              0#32).toNat ≤ target_lvl.toNat := by bv_omega
          rwa [hlit_get] at hle_raw
        · have hstep := bt_loopInv_step hinv hbt hpos (by
            have hle_raw : ¬ ((st.lvlArr[(st.trl[te.toNat - 1]?.getD 0#32).toNat / 2]?.getD
                0#32).toNat ≤ target_lvl.toNat) := ‹_›
            rw [← hbt.trl_eq]
            omega)
          c0_hsteps!
          · have hs2 := hstep.2 (st.trl[te.toNat - 1]?.getD 0#32 >>> (1 : Nat))
            refine hL (te - 1#32, _, _) _ (by dsimp only; bv_omega) ⟨hs2, ?_⟩
            refine Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ R) _) ?_) hm
            kstate_ext <;>
              (first | rfl | (simp only [lit, hlit_get, hv_eq, bv32_one_eq]; rfl))
          · refine hL (te - 1#32, bst, _) _ (by dsimp only; bv_omega) ⟨hstep.1, ?_⟩
            refine Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ R) _) ?_) hm
            kstate_ext <;>
              (first | rfl | (simp only [lit, hlit_get, hv_eq, bv32_one_eq]; rfl))
      · exact hB (te, bst, st) m' ⟨hbt, Or.inl (by bv_omega), hm'⟩
    · intro B L hB hL
      exact wp_jump_state
        (proj := fun st : BitVec 32 × BitVec 32 × KittenState => (st.1, st.2.1, ()))
        (ks.trl_end, best_st, ks) rfl (hL (ks.trl_end, best_st, ks) m0 ⟨bt_loopInv_init hinv, hm0⟩)
  · intro J0 hJ0
    c0_hsplit
    · have hqs_lt : ks.qsearch.toNat < ks.nv.toNat := by bv_omega
      have hqs_wrap : ks.qsearch.toNat < 2 ^ 28 := by unfold kMaxV at hnv; omega
      have hqs_128 : ks.qsearch.toNat < 128 := by unfold kMaxV at hnv; omega
      c0_hsteps!
      exact hJ0 _ m hmA
    · c0_hsteps!
      exact hJ0 _ m hmA

private structure InitScalarState (nv0 ta0 ac0 : BitVec 32) (st : KittenState) : Prop where
  nv : st.nv = nv0
  nc : st.nc = 0#32
  orig_nc : st.orig_nc = 0#32
  lvl : st.lvl = 0#32
  prop : st.prop = 0#32
  trl_end : st.trl_end = 0#32
  unass : st.unass = nv0
  acap : st.acap = ac0
  alen : st.alen = 0#32
  incons : st.incons = 0xFFFFFFFF#32
  failing : st.failing = 0xFFFFFFFF#32
  ante : st.ante = ta0
  nassump : st.nassump = 0#32
  nunits : st.nunits = 0#32
  nres : st.nres = 0#32
  nkl : st.nkl = 0#32
  nana : st.nana = 0#32

private theorem InitScalarState.putArr {nv ta ac : BitVec 32} {st : KittenState}
    (h : InitScalarState nv ta ac st) (f : KArrField) (i : Nat) (v : BitVec 32) :
    InitScalarState nv ta ac (st.putArr f i v) := by
  cases f <;> exact ⟨h.nv, h.nc, h.orig_nc, h.lvl, h.prop, h.trl_end, h.unass, h.acap,
    h.alen, h.incons, h.failing, h.ante, h.nassump, h.nunits, h.nres, h.nkl, h.nana⟩

/-- Parametric `Func.wp` proof for `full_kitten_init`. -/
theorem full_kitten_init_wp (Γ : Env) :
    ∀ args m Q X, fullKittenInitSpec args m Q X → Func.wp Γ full_kitten_init_body args m Q X := by
  rintro ⟨hPtr, nv, track_ante, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hsc_lt : c.scratch_cap < 2 ^ 64 := Nat.lt_trans c.hscr (by decide)
  c0_hsteps_nogrp
  · have hcap_lt : c.scratch_cap < kMinScratchCap := by
      unfold kMinScratchCap; bv_omega
    have hif : c.scratch_cap < kMinScratchCap ∨ kMaxV < nv.toNat := Or.inl hcap_lt
    simp only [hif, ite_true] at hQ; exact hQ
  · have hnv_gt : kMaxV < nv.toNat := by unfold kMaxV; bv_omega
    have hif : c.scratch_cap < kMinScratchCap ∨ kMaxV < nv.toNat := Or.inr hnv_gt
    simp only [hif, ite_true] at hQ; exact hQ
  · have hcap_ge : kMinScratchCap ≤ c.scratch_cap := by
      unfold kMinScratchCap; bv_omega
    have hnv_le : nv.toNat ≤ kMaxV := by unfold kMaxV; bv_omega
    have hnot : ¬ (c.scratch_cap < kMinScratchCap ∨ kMaxV < nv.toNat) := by omega
    simp only [hnot, ite_false] at hQ
    let scr := s.scratch.scratch_buf
    have hscr_len : scr.length = c.scratch_cap := hlen.scratch_ok.scratch_buf_len
    have hscr_ge : 8864 ≤ scr.length := by unfold kMinScratchCap at hcap_ge; omega
    let acap := scr.length - 8864
    have hacap_ge : kMinScratchCap - kBase - kSlabFixed ≤ acap := by
      unfold kMinScratchCap kBase kSlabFixed at *; omega
    have hacap_lt : acap < dimacsBound := by
      have := c.hscr; unfold dimacsBound at *; omega
    let ks0 := KittenState.ofSlab (scr.drop 256)
    have hlen_drop : 8608 ≤ (scr.drop 256).length := by simp; omega
    have hsh0 : ks0.ShapesOk acap := by
      have h1 := KittenState.shapesOk_ofSlab (xs := scr.drop 256) hlen_drop
      rwa [show (scr.drop 256).length - 8608 = acap by simp [acap]; omega] at h1
    have hmF : (FullKittenFrame c s ⋆ KittenMem (c.pScratchBuf + 1024#64) ks0 ⋆ R) m := by
      have hfull := fullMem_eq_kittenFrame (c := c) (s := s) hscr_ge
      rw [hfull] at hm; exact sep_ac hm
    clear hm
    c0_hsteps_nogrp
    let kPtr := c.pScratchBuf + 1024#64
    have hmHdr : (array (t := i32) (c.pScratchBuf + BitVec.ofNat 64 256 * 4)
        (kittenHdrWords ks0) ⋆ ((KittenTree kPtr ks0).rest (kPath 0) ⋆
          (FullKittenFrame c s ⋆ R))) m := by
      have hm1 : (KittenMem kPtr ks0 ⋆ (FullKittenFrame c s ⋆ R)) m := sep_ac hmF
      exact KittenMemTactics.focus_kitten_hdr hm1
    clear hmF
    refine wp_while_state1 (fun p : BitVec 32 × List (BitVec 32) => p.1)
      (fun p => 32 - p.1.toNat)
      (fun p m' => p.1.toNat ≤ 32 ∧ p.2.length = 32 ∧
        (∀ j < p.1.toNat, p.2[j]? = some 0#32) ∧
        (array (t := i32) (c.pScratchBuf + BitVec.ofNat 64 256 * 4) p.2 ⋆
          ((KittenTree kPtr ks0).rest (kPath 0) ⋆ (FullKittenFrame c s ⋆ R))) m')
      ?_ ?_
    · intro J hJ
      exact wp_jump_state (proj := fun p : BitVec 32 × List (BitVec 32) => (p.1, ()))
        (0#32, kittenHdrWords ks0) rfl
        (hJ _ m ⟨by simp, kittenHdrWords_length hsh0, fun j hj => by simp at hj, hmHdr⟩)
    · rintro J ⟨i, hdrWs⟩ m' ⟨hi_le, hlen_w, hzeros, hm'⟩ ih
      dsimp only at hi_le hlen_w hzeros hm'
      c0_hsplit
      · have hi_lt : i.toNat < 32 := by bv_omega
        have hi_wrap : i.toNat < 2 ^ 28 := by omega
        have hi_w : i.toNat < hdrWs.length := by rw [hlen_w]; exact hi_lt
        c0_hsteps!
        have hsw : (BitVec.setWidth 64 i).toNat = i.toNat := by
          have := i.isLt; simp; omega
        rw [hsw] at hm
        refine ih (i + 1#32, hdrWs.set i.toNat 0#32) _ (by bv_omega) ⟨by bv_omega,
          by simp [hlen_w], ?_, hm⟩
        intro j hj
        have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
        rw [hi1] at hj
        by_cases hji : j = i.toNat
        · subst hji; exact List.getElem?_set_self hi_w
        · rw [List.getElem?_set_ne (Ne.symm hji)]; exact hzeros j (by omega)
      · have hi_eq : i.toNat = 32 := by bv_omega
        have hrep : hdrWs = List.replicate 32 0#32 := by
          apply List.ext_getElem (by simp [hlen_w])
          intro j hj _
          have hj32 : j < 32 := by simp [hlen_w] at hj; exact hj
          have hz := hzeros j (by omega)
          rw [List.getElem?_eq_getElem (by omega : j < hdrWs.length)] at hz
          rw [List.getElem_replicate]; exact Option.some.inj hz
        rw [hrep] at hm'
        let hm'k : (array (t := i32) kPtr (List.replicate 32 0#32) ⋆
            ((KittenTree kPtr ks0).rest (kPath 0) ⋆ (FullKittenFrame c s ⋆ R))) m' := hm'
        let ks1 : KittenState :=
          { ks0 with
            nv := 0#32, nc := 0#32, orig_nc := 0#32, lvl := 0#32, prop := 0#32,
            trl_end := 0#32, unass := 0#32, incons := 0#32, failing := 0#32, ante := 0#32,
            qfirst := 0#32, qlast := 0#32, qsearch := 0#32, qstamp := 0#32, ticks := 0#32,
            tick_lim := 0#32, alen := 0#32, acap := 0#32, nassump := 0#32, nunits := 0#32,
            nres := 0#32, nkl := 0#32, nana := 0#32, status := 0#32, phase := 0#32,
            hdrTail := List.replicate 7 0#32 }
        have hsh1 : ks1.ShapesOk acap := by
          refine ⟨by simp [ks1], hsh0.lvlArr_len, hsh0.rsn_len, hsh0.qprev_len, hsh0.qnext_len,
            hsh0.qstampArr_len, hsh0.trl_len, hsh0.flags_len, hsh0.vals_len, hsh0.assump_len,
            hsh0.ana_len, hsh0.kl_len, hsh0.units_len, hsh0.res_len, hsh0.whead_len,
            hsh0.wnext_len, hsh0.wblit_len, hsh0.clOff_len, hsh0.clMeta_len, hsh0.clAux_len,
            hsh0.arena_len⟩
        have hunf : (KittenMem kPtr ks1 ⋆ (FullKittenFrame c s ⋆ R)) m' := by
          refine KittenMemTactics.unfocus_kitten_hdr (ks := ks0) (ks' := ks1)
            (hdr' := List.replicate 32 0#32) ?_ hm'k
          simp only [KittenMem, KittenTree, kPath, SepTree.set, SepTree.eval, kittenHdrWords,
            ks1, List.replicate]
          congr 1
        let kPtr0 := c.pScratchBuf + BitVec.ofNat 64 256 * 4
        have hmA1 : (KittenMemA kPtr0 acap ks1 ⋆ (FullKittenFrame c s ⋆ R)) m' :=
          kittenMem_to_amem hsh1 hunf
        clear hm' hm'k hunf
        c0_hsteps_nogrp
        let ksH0 := ((((((ks1.putHdr .nv nv).putHdr .unass nv).putHdr .ante track_ante).putHdr
          .incons 0xFFFFFFFF#32).putHdr .failing 0xFFFFFFFF#32).putHdr .tick_lim 8192#32
          ).putHdr .acap ((BitVec.ofNat 64 c.scratch_cap - 256#64 - 8608#64).setWidth 32)
        let ksH := if nv == 0#32 then
            ((ksH0.putHdr .qfirst 0xFFFFFFFF#32).putHdr .qlast 0xFFFFFFFF#32).putHdr
              .qsearch 0xFFFFFFFF#32
          else
            (((ksH0.putHdr .qfirst 0#32).putHdr .qlast (nv - 1#32)).putHdr
              .qsearch (nv - 1#32)).putHdr .qstamp nv
        have hshH : ksH.ShapesOk acap := by
          have hh0 := ((((((hsh1.putHdr .nv nv).putHdr .unass nv).putHdr .ante
            track_ante).putHdr .incons 0xFFFFFFFF#32).putHdr .failing 0xFFFFFFFF#32).putHdr
            .tick_lim 8192#32).putHdr .acap
              ((BitVec.ofNat 64 c.scratch_cap - 256#64 - 8608#64).setWidth 32)
          dsimp only [ksH]; split
          · exact ((hh0.putHdr .qfirst _).putHdr .qlast _).putHdr .qsearch _
          · exact (((hh0.putHdr .qfirst _).putHdr .qlast _).putHdr .qsearch _).putHdr .qstamp _
        have e_acap : ksH.acap = BitVec.ofNat 32 acap := by
          have hh : ksH.acap =
              (BitVec.ofNat 64 c.scratch_cap - 256#64 - 8608#64).setWidth 32 := by
            dsimp only [ksH]; split <;> dsimp only [ksH0] <;> kp_field
          rw [hh]; apply BitVec.eq_of_toNat_eq
          have hsc := c.hscr; unfold dimacsBound at hsc
          simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
          have hmod : c.scratch_cap < 2 ^ 64 := by omega
          omega
        refine wp_join0 (fun m2 => (KittenMemA kPtr0 acap ksH ⋆ (FullKittenFrame c s ⋆ R)) m2)
          ?_ ?_
        · intro J2 m2 hm2
          c0_hsteps_nogrp
          have hInitH : InitScalarState nv track_ante ksH.acap ksH := by
            dsimp only [ksH]; split <;> dsimp only [ksH0, ks1] <;>
              refine ⟨by kp_field, by kp_field, by kp_field, by kp_field, by kp_field,
                by kp_field, by kp_field, by kp_field, by kp_field, by kp_field,
                by kp_field, by kp_field, by kp_field, by kp_field, by kp_field,
                by kp_field, by kp_field⟩
          refine wp_while_state1 (fun p : BitVec 32 × KittenState => p.1)
            (fun p => nv.toNat - p.1.toNat)
            (fun p m3 => p.1.toNat ≤ nv.toNat ∧ p.2.ShapesOk acap ∧
              InitScalarState nv track_ante ksH.acap p.2 ∧
              (∀ v < p.1.toNat, p.2.lvlArr[v]? = some 0#32 ∧
                p.2.rsn[v]? = some 0xFFFFFFFF#32 ∧ p.2.flags[v]? = some 0#32) ∧
              (KittenMemA kPtr0 acap p.2 ⋆ (FullKittenFrame c s ⋆ R)) m3)
            ?_ ?_
          · intro J3 hJ3
            exact wp_jump_state (proj := fun p : BitVec 32 × KittenState => (p.1, ()))
              (0#32, ksH) rfl (hJ3 _ m2 ⟨by simp, hshH, hInitH, fun _ h => by simp at h, hm2⟩)
          · rintro J3 ⟨j, st⟩ m3 ⟨hj_le, hsh_st, hsc_st, hvars_st, hm3⟩ ih3
            dsimp only at hj_le hsh_st hsc_st hvars_st hm3
            c0_hsplit
            · have hj_lt : j.toNat < nv.toNat := by bv_omega
              have hj_wrap : j.toNat < 2 ^ 28 := by unfold kMaxV at hnv_le; omega
              have hj_128 : j.toNat < 128 := by unfold kMaxV at hnv_le; omega
              c0_hsteps!
              all_goals
                have hj1 : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
                refine ih3 (j + 1#32, _) _ (by dsimp only; rw [hj1]; omega)
                  ⟨by dsimp only; rw [hj1]; omega, ?_, ?_, ?_, hm⟩
                · exact (((((hsh_st.putArr .lvlArr _ _).putArr .rsn _ _).putArr
                    .flags _ _).putArr .qstampArr _ _).putArr .qprev _ _).putArr .qnext _ _
                · exact (((((hsc_st.putArr .lvlArr _ _).putArr .rsn _ _).putArr
                    .flags _ _).putArr .qstampArr _ _).putArr .qprev _ _).putArr .qnext _ _
                · intro v hv
                  rw [hj1] at hv
                  by_cases hvj : v = j.toNat
                  · subst hvj
                    have hv1 : j.toNat < st.lvlArr.length := by
                      rw [hsh_st.lvlArr_len]; exact hj_128
                    have hv2 : j.toNat < st.rsn.length := by
                      rw [hsh_st.rsn_len]; exact hj_128
                    have hv3 : j.toNat < st.flags.length := by
                      rw [hsh_st.flags_len]; exact hj_128
                    exact ⟨by kp_field; rw [List.getElem?_set_self hv1]; rfl,
                      by kp_field; rw [List.getElem?_set_self hv2]; rfl,
                      by kp_field; rw [List.getElem?_set_self hv3]; rfl⟩
                  · have hvv := hvars_st v (by omega)
                    exact ⟨by kp_field; rw [List.getElem?_set_ne (Ne.symm hvj)]; exact hvv.1,
                      by kp_field; rw [List.getElem?_set_ne (Ne.symm hvj)]; exact hvv.2.1,
                      by kp_field; rw [List.getElem?_set_ne (Ne.symm hvj)]; exact hvv.2.2⟩
            · have hj_eq : j.toNat = nv.toNat := by bv_omega
              rw [hj_eq] at hvars_st
              c0_hsteps_nogrp
              have hnl_eq : (nv <<< (1 : Nat)).toNat = 2 * nv.toNat := by
                rw [kitten_shl1_toNat]; unfold kMaxV at hnv_le; omega
              refine wp_while_state1 (fun p : BitVec 32 × KittenState => p.1)
                (fun p => 2 * nv.toNat - p.1.toNat)
                (fun p m4 => p.1.toNat ≤ 2 * nv.toNat ∧ p.2.ShapesOk acap ∧
                  InitScalarState nv track_ante ksH.acap p.2 ∧
                  (∀ v < nv.toNat, p.2.lvlArr[v]? = some 0#32 ∧
                    p.2.rsn[v]? = some 0xFFFFFFFF#32 ∧ p.2.flags[v]? = some 0#32) ∧
                  (∀ l < p.1.toNat, p.2.vals[l]? = some 0#32 ∧
                    p.2.whead[l]? = some 0xFFFFFFFF#32) ∧
                  (KittenMemA kPtr0 acap p.2 ⋆ (FullKittenFrame c s ⋆ R)) m4)
                ?_ ?_
              · intro J4 hJ4
                exact wp_jump_state (proj := fun p : BitVec 32 × KittenState => (p.1, ()))
                  (0#32, st) rfl
                  (hJ4 _ m3 ⟨by simp, hsh_st, hsc_st, hvars_st, fun _ h => by simp at h, hm3⟩)
              · rintro J4 ⟨k, st4⟩ m4 ⟨hk_le, hsh4, hsc4, hvars4, hlits4, hm4⟩ ih4
                dsimp only at hk_le hsh4 hsc4 hvars4 hlits4 hm4
                c0_hsplit
                · have hk_lt : k.toNat < 2 * nv.toNat := by rw [← hnl_eq]; bv_omega
                  have hk_wrap : k.toNat < 2 ^ 28 := by unfold kMaxV at hnv_le; omega
                  have hk_256 : k.toNat < 256 := by unfold kMaxV at hnv_le; omega
                  c0_hsteps!
                  let st4' := (st4.putArr .vals k.toNat 0#32).putArr .whead k.toNat
                    0xFFFFFFFF#32
                  have hk1 : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
                  refine ih4 (k + 1#32, st4') _ (by dsimp only; rw [hk1]; omega)
                    ⟨by dsimp only; rw [hk1]; omega, ?_, ?_, ?_, ?_, hm⟩
                  · exact (hsh4.putArr .vals k.toNat 0#32).putArr .whead k.toNat 0xFFFFFFFF#32
                  · exact (hsc4.putArr .vals k.toNat 0#32).putArr .whead k.toNat
                      0xFFFFFFFF#32
                  · intro v hv
                    have hvv := hvars4 v hv
                    exact ⟨by kp_field; exact hvv.1, by kp_field; exact hvv.2.1,
                      by kp_field; exact hvv.2.2⟩
                  · intro l hl
                    rw [hk1] at hl
                    by_cases hlk : l = k.toNat
                    · subst hlk
                      have hv_len : k.toNat < st4.vals.length := by
                        rw [hsh4.vals_len]; exact hk_256
                      have hw_len : k.toNat < st4.whead.length := by
                        rw [hsh4.whead_len]; exact hk_256
                      exact ⟨by dsimp only [st4']; kp_field; rw [List.getElem?_set_self hv_len],
                        by dsimp only [st4']; kp_field; rw [List.getElem?_set_self hw_len]⟩
                    · have hll := hlits4 l (by omega)
                      exact ⟨by dsimp only [st4']; kp_field
                                rw [List.getElem?_set_ne (Ne.symm hlk)]; exact hll.1,
                        by dsimp only [st4']; kp_field
                           rw [List.getElem?_set_ne (Ne.symm hlk)]; exact hll.2⟩
                · have hk_eq : k.toNat = 2 * nv.toNat := by
                    have hge : 2 * nv.toNat ≤ k.toNat := by
                      have hnl : ¬ k.toNat < (nv <<< (1 : Nat)).toNat := ‹_›
                      rw [hnl_eq] at hnl; omega
                    omega
                  rw [hk_eq] at hlits4
                  c0_hsteps!
                  have hfin := init_finish_inv hsh4 hacap_ge hacap_lt hnv_le hsc4.nv hsc4.nc
                    hsc4.orig_nc hsc4.lvl hsc4.prop hsc4.trl_end hsc4.unass
                    (hsc4.acap.trans e_acap) hsc4.alen hsc4.incons hsc4.failing hsc4.nassump
                    hsc4.nunits hsc4.nres hsc4.nkl hsc4.nana hvars4 hlits4
                  obtain ⟨_, hm4'⟩ := kittenMemA_to_mem hm4
                  have hm4'_exp : (FullKittenFrame c s ⋆ KittenMem kPtr st4 ⋆ R) m4 := sep_ac hm4'
                  have hmJ := fullMem_join_kitten (c := c) (s := s) (acap := acap)
                    (ks' := st4) (R := R) (by change 256 ≤ scr.length; omega) hsh4 hm4'_exp
                  let scr' := s.scratch.scratch_buf.take 256 ++ st4.toSlab
                  have hscr_s_eq : s.scratch.scratch_buf = scr := rfl
                  have hscr'_len : scr'.length = c.scratch_cap := by
                    simp only [scr', hscr_s_eq, List.length_append,
                      List.length_take_of_le (by omega : 256 ≤ scr.length),
                      KittenState.toSlab_length hsh4]
                    dsimp only [acap]; omega
                  have hpre : ∀ x < kBase, scr'[x]? = s.scratch.scratch_buf[x]? := by
                    intro x hx
                    have htk : x < (s.scratch.scratch_buf.take 256).length := by
                      rw [hscr_s_eq, List.length_take_of_le (by omega : 256 ≤ scr.length)]
                      unfold kBase at hx; omega
                    rw [List.getElem?_append_left htk, List.getElem?_take_of_lt
                      (by unfold kBase at hx; omega)]
                  have hof : kittenStateOfScratch scr' = st4 := by
                    unfold kittenStateOfScratch
                    rw [slab_drop_exact _ st4.toSlab (by
                      rw [hscr_s_eq, List.length_take_of_le (by omega : 256 ≤ scr.length)])]
                    exact KittenState.ofSlab_toSlab hsh4
                  have hks_inv : KittenScratchInv scr' := by
                    refine ⟨by omega, by rw [hscr'_len]; exact c.hscr, ?_⟩
                    rw [hof, show scr'.length - 8864 = acap by dsimp only [acap]; omega]
                    exact hfin.1
                  exact hQ scr' m4 (fullState_lengthsOk_scratch hlen hscr'_len) hpre hks_inv
                    (by rw [hof]; exact hfin.2.1) (by rw [hof]; exact hsc4.nv)
                    (by rw [hof]; exact hsc4.nc) (by rw [hof]; exact hsc4.orig_nc)
                    (by rw [hof]; exact hsc4.lvl) (by rw [hof]; exact hsc4.prop)
                    (by rw [hof]; exact hsc4.trl_end) (by rw [hof]; exact hsc4.unass)
                    (by rw [hof]; exact hsc4.incons) (by rw [hof]; exact hsc4.failing)
                    (by rw [hof]; exact hsc4.ante) (by rw [hof]; exact hsc4.nassump)
                    (by rw [hof]; exact hsc4.nunits)
                    (by unfold kittenOrigClausesS; rw [hof]; exact hfin.2.2.1)
                    (by unfold kittenAssumpLitsS; rw [hof]; exact hfin.2.2.2) hmJ
        · intro J2 hJ2
          c0_hsteps!
          · exact hJ2 _ (by simp [ksH, show nv = 0#32 from by bv_omega]; exact hm)
          · exact hJ2 _ (by simp [ksH, show ¬(nv = 0#32) from by bv_omega]; exact hm)

/-- Parametric `Func.wp` proof for `full_kitten_add_clause`. -/
theorem full_kitten_add_clause_wp (Γ : Env)
    (hWatch : ∀ args m Q X, fullKittenWatchSpec args m Q X →
      Γ "full_kitten_watch" [i64, i32, i32, i32] [] args m Q X) :
    ∀ args m Q X, fullKittenAddClauseSpec args m Q X →
      Func.wp Γ full_kitten_add_clause_body args m Q X := by
  rintro ⟨hPtr, cid, litsPtr, sz, ⟨⟩⟩ m Q X ⟨c, s, scr, xs, R, rfl, hlen, hscr_buf,
    hinv_s, hsync, hlvl0, hte0, heq_nc, hsz_xs, hsz_max, hxlits, hm, hQ⟩
  rcases hinv_s with ⟨hscr_ge, hscr_lt, hinv⟩
  let acap := scr.length - 8864
  let ks := kittenStateOfScratch scr
  have hsh := hinv.shapes
  have hnv := hinv.clauses.nv_le
  have hal := hinv.clauses.alen_le
  have hacap_lt : acap < 2 ^ 28 := hinv.clauses.acap_lt
  have hca_eq : ks.acap.toNat = acap := by
    rw [hinv.clauses.acap_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hscr_len : scr.length = c.scratch_cap := by
    rw [← hscr_buf]; exact hlen.scratch_ok.scratch_buf_len
  have hscr_8864 : 8864 ≤ scr.length := by unfold kMinScratchCap at hscr_ge; omega
  let kPtr := c.pScratchBuf + BitVec.ofNat 64 256 * 4
  let Rrest : Mem 64 → Prop := array (t := i32) litsPtr xs ⋆
    (array (t := i32) c.pScratchBuf (scr.take 256) ⋆ R)
  have hof_ks : KittenState.ofSlab (scr.drop 256) = ks := rfl
  have hmA : (KittenMemA kPtr acap ks ⋆
      (array64 (c.hdr + 32) (hdrTailWords c s) ⋆ Rrest)) m :=
    fullAddClause_mem_to_ka hscr_8864 hsh hof_ks hm
  clear hm
  have hreorg : ∀ {ks' : KittenState} {m' : Mem 64} (hsh' : ks'.ShapesOk acap),
      (KittenMemA kPtr acap ks' ⋆
        (array64 (c.hdr + 32) (hdrTailWords c s) ⋆ Rrest)) m' →
      let scr' := scr.take 256 ++ ks'.toSlab
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      scr'.length = c.scratch_cap ∧ (∀ i < kBase, scr'[i]? = scr[i]?) ∧
      (array64 (c.hdr + 32) (hdrTailWords c s') ⋆ array (t := i32) c.pScratchBuf scr' ⋆
        array (t := i32) litsPtr xs ⋆ R) m' := by
    intro ks' m' hsh' hm' scr' s'
    have htk : (scr.take 256).length = 256 := List.length_take_of_le (by omega)
    have hlen' : scr'.length = c.scratch_cap := by
      simp only [scr', List.length_append, htk, KittenState.toSlab_length hsh']; omega
    have hpre : ∀ i < kBase, scr'[i]? = scr[i]? := by
      intro i hi
      rw [List.getElem?_append_left (by unfold kBase at hi; omega),
        List.getElem?_take_of_lt (by unfold kBase at hi; omega)]
    exact ⟨hlen', hpre, fullAddClause_ka_to_mem (by omega) hsh' hm'⟩
  have hscr_orig : scr.take 256 ++ ks.toSlab = scr := by
    unfold ks kittenStateOfScratch
    rw [KittenState.toSlab_ofSlab (by simp; omega), List.take_append_drop]
  have hof_slab : ∀ {ks' : KittenState} (hsh' : ks'.ShapesOk acap),
      kittenStateOfScratch (scr.take 256 ++ ks'.toSlab) = ks' := by
    intro ks' hsh'
    unfold kittenStateOfScratch
    rw [slab_drop_exact _ ks'.toSlab (by simp; omega)]
    exact KittenState.ofSlab_toSlab hsh'
  c0_hsplit
  · c0_hsteps!
    have hmF := hreorg hsh hmA
    have hinv_fin : KittenScratchInv scr := ⟨hscr_ge, hscr_lt, hinv⟩
    rw [hscr_orig] at hmF
    exact hQ false scr m hscr_len (fun _ _ => rfl) hinv_fin hsync hlvl0 hte0 rfl heq_nc
      rfl rfl rfl (fun _ => rfl) (fun h => by cases h) hmF.2.2
  · c0_hsplit
    · c0_hsteps!
      have hmF := hreorg hsh hmA
      have hinv_fin : KittenScratchInv scr := ⟨hscr_ge, hscr_lt, hinv⟩
      rw [hscr_orig] at hmF
      exact hQ false scr m hscr_len (fun _ _ => rfl) hinv_fin hsync hlvl0 hte0 rfl heq_nc
        rfl rfl rfl (fun _ => rfl) (fun h => by cases h) hmF.2.2
    · have hal_ks : ks.alen.toNat ≤ ks.acap.toNat := by rw [hca_eq]; exact hal
      have hcap_lt : ks.acap.toNat < 2 ^ 28 := by rw [hca_eq]; exact hacap_lt
      have hnc_lt : ks.nc.toNat < kMaxOrig := by unfold kMaxOrig; bv_omega
      have hnc_896 : ks.nc.toNat < 896 := by unfold kMaxOrig at hnc_lt; omega
      have hnc_wrap : ks.nc.toNat < 2 ^ 28 := by omega
      have hoff_fit : ks.alen.toNat + sz.toNat ≤ ks.acap.toNat := by bv_omega
      c0_hsplit
      · c0_hsteps!
        · have hin_eq : (ks.incons == 0xFFFFFFFF#32) = true := beq_iff_eq.mpr ‹_›
          have hpres := addClause_empty_preserves (cid := cid) hinv hsync hlvl0 hte0 heq_nc hnc_lt
          let st0 := ((ks.putArr .clOff ks.nc.toNat ks.alen).putArr .clMeta ks.nc.toNat
            0#32).putArr .clAux ks.nc.toNat cid
          let st1 := if ks.incons == 0xFFFFFFFF#32 then st0.putHdr .incons ks.nc else st0
          let ks' := (st1.putHdr .nc (ks.nc + 1#32)).putHdr .orig_nc (ks.nc + 1#32)
          have hk_nv : ks'.nv = ks.nv := by dsimp only [ks', st1, st0]; split <;> kp_field
          have hk_an : ks'.ante = ks.ante := by dsimp only [ks', st1, st0]; split <;> kp_field
          have hk_na : ks'.nassump = ks.nassump := by
            dsimp only [ks', st1, st0]; split <;> kp_field
          have hm_ks' : (KittenMemA kPtr acap ks' ⋆
              (array64 (c.hdr + 32) (hdrTailWords c s) ⋆ Rrest)) m := by
            refine Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ _) _) ?_) hm
            dsimp only [ks', st1, st0]; simp only [hin_eq, ite_true]; rfl
          have hsh' := hpres.1.shapes
          have hmF := hreorg hsh' hm_ks'
          have hinv' : KittenScratchInv (scr.take 256 ++ ks'.toSlab) := by
            refine ⟨by rw [hmF.1]; omega, by rw [hmF.1]; exact c.hscr, ?_⟩
            rw [hof_slab hsh', show (scr.take 256 ++ ks'.toSlab).length - 8864 = acap by
              rw [hmF.1]; omega]
            exact hpres.1
          have hsz0 : sz = 0#32 := ‹_›
          have htk0 : ((xs.take sz.toNat).map BitVec.toNat) = [] := by rw [hsz0]; simp
          have horig' : kittenOrigClausesS (scr.take 256 ++ ks'.toSlab) =
              kittenOrigClausesS scr ++ [(xs.take sz.toNat).map BitVec.toNat] := by
            unfold kittenOrigClausesS; rw [hof_slab hsh', htk0]; exact hpres.2.2.2.2.2.2.2.2.1
          exact hQ true _ _ hmF.1 hmF.2.1 hinv'
            (by rw [hof_slab hsh']; exact hpres.2.1) (by rw [hof_slab hsh']; exact hpres.2.2.1)
            (by rw [hof_slab hsh']; exact hpres.2.2.2.1)
            (by rw [hof_slab hsh']; exact hk_nv)
            (by rw [hof_slab hsh']; exact hpres.2.2.2.2.1)
            (by rw [hof_slab hsh']; exact hk_an)
            (by rw [hof_slab hsh']; exact hk_na)
            (by unfold kittenAssumpLitsS; rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.2.2.1)
            (fun h => by cases h)
            (fun _ => ⟨by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.1,
              by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.1,
              by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.2.2.2,
              by rw [hof_slab hsh', hsz0]; exact hpres.2.2.2.2.2.2.2.1, horig',
              fun _ _ => by
                rw [hof_slab hsh']
                have hwb : ks'.wblit = ks.wblit := by dsimp only [ks', st1, st0]; split <;> kp_field
                rw [hwb],
              fun h2 => by rw [hsz0] at h2; simp at h2⟩)
            hmF.2.2
        · have hin_ne : (ks.incons == 0xFFFFFFFF#32) = false := beq_false_of_ne ‹_›
          have hpres := addClause_empty_preserves (cid := cid) hinv hsync hlvl0 hte0 heq_nc hnc_lt
          let st0 := ((ks.putArr .clOff ks.nc.toNat ks.alen).putArr .clMeta ks.nc.toNat
            0#32).putArr .clAux ks.nc.toNat cid
          let st1 := if ks.incons == 0xFFFFFFFF#32 then st0.putHdr .incons ks.nc else st0
          let ks' := (st1.putHdr .nc (ks.nc + 1#32)).putHdr .orig_nc (ks.nc + 1#32)
          have hk_nv : ks'.nv = ks.nv := by dsimp only [ks', st1, st0]; split <;> kp_field
          have hk_an : ks'.ante = ks.ante := by dsimp only [ks', st1, st0]; split <;> kp_field
          have hk_na : ks'.nassump = ks.nassump := by
            dsimp only [ks', st1, st0]; split <;> kp_field
          have hm_ks' : (KittenMemA kPtr acap ks' ⋆
              (array64 (c.hdr + 32) (hdrTailWords c s) ⋆ Rrest)) m := by
            refine Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ _) _) ?_) hm
            dsimp only [ks', st1, st0]; simp only [hin_ne, Bool.false_eq_true, ite_false]; rfl
          have hsh' := hpres.1.shapes
          have hmF := hreorg hsh' hm_ks'
          have hinv' : KittenScratchInv (scr.take 256 ++ ks'.toSlab) := by
            refine ⟨by rw [hmF.1]; omega, by rw [hmF.1]; exact c.hscr, ?_⟩
            rw [hof_slab hsh', show (scr.take 256 ++ ks'.toSlab).length - 8864 = acap by
              rw [hmF.1]; omega]
            exact hpres.1
          have hsz0 : sz = 0#32 := ‹_›
          have htk0 : ((xs.take sz.toNat).map BitVec.toNat) = [] := by rw [hsz0]; simp
          have horig' : kittenOrigClausesS (scr.take 256 ++ ks'.toSlab) =
              kittenOrigClausesS scr ++ [(xs.take sz.toNat).map BitVec.toNat] := by
            unfold kittenOrigClausesS; rw [hof_slab hsh', htk0]; exact hpres.2.2.2.2.2.2.2.2.1
          exact hQ true _ _ hmF.1 hmF.2.1 hinv'
            (by rw [hof_slab hsh']; exact hpres.2.1) (by rw [hof_slab hsh']; exact hpres.2.2.1)
            (by rw [hof_slab hsh']; exact hpres.2.2.2.1)
            (by rw [hof_slab hsh']; exact hk_nv)
            (by rw [hof_slab hsh']; exact hpres.2.2.2.2.1)
            (by rw [hof_slab hsh']; exact hk_an)
            (by rw [hof_slab hsh']; exact hk_na)
            (by unfold kittenAssumpLitsS; rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.2.2.1)
            (fun h => by cases h)
            (fun _ => ⟨by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.1,
              by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.1,
              by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.2.2.2,
              by rw [hof_slab hsh', hsz0]; exact hpres.2.2.2.2.2.2.2.1, horig',
              fun _ _ => by
                rw [hof_slab hsh']
                have hwb : ks'.wblit = ks.wblit := by dsimp only [ks', st1, st0]; split <;> kp_field
                rw [hwb],
              fun h2 => by rw [hsz0] at h2; simp at h2⟩)
            hmF.2.2
      · have hsz_pos : 1 ≤ sz.toNat := by
          have hne : sz ≠ 0#32 := ‹_›
          exact Nat.pos_of_ne_zero fun hz => hne (BitVec.eq_of_toNat_eq hz)
        refine wp_while_state1 (fun p : BitVec 32 × List (BitVec 32) => p.1)
          (fun p => sz.toNat - p.1.toNat)
          (fun p m' => p.1.toNat ≤ sz.toNat ∧ p.2.length = acap ∧
            (∀ j < ks.alen.toNat, p.2[j]? = ks.arena[j]?) ∧
            (∀ j < p.1.toNat, p.2[ks.alen.toNat + j]? = xs[j]?) ∧
            (KittenMemA kPtr acap { ks with arena := p.2 } ⋆
              (array64 (c.hdr + 32) (hdrTailWords c s) ⋆
                (array (t := i32) litsPtr xs ⋆
                  (array (t := i32) c.pScratchBuf (scr.take 256) ⋆ R)))) m')
          ?_ ?_
        · intro J hJ
          exact wp_jump_state (proj := fun p : BitVec 32 × List (BitVec 32) => (p.1, ()))
            (0#32, ks.arena) rfl
            (hJ _ m ⟨by simp, hsh.arena_len, fun _ _ => rfl, fun _ hj => by simp at hj, hmA⟩)
        · rintro J ⟨i, ar⟩ m' ⟨hi_le, har_len, har_old, har_new, hm'⟩ ih
          dsimp only at hi_le har_len har_old har_new hm' ⊢
          have hsh_ar : ({ ks with arena := ar } : KittenState).ShapesOk acap :=
            { hsh with arena_len := har_len }
          c0_hsplit
          · have hi_lt : i.toNat < sz.toNat := by bv_omega
            have hi_xs : i.toNat < xs.length := by omega
            have hsw_i : (BitVec.setWidth 64 i).toNat = i.toNat := by
              simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : i.toNat < 2 ^ 64)]
            have hi_sw : (BitVec.setWidth 64 i).toNat < xs.length := by rw [hsw_i]; exact hi_xs
            have hi_wrap : i.toNat < 2 ^ 28 := by omega
            have hoff_i_wrap : ks.alen.toNat + i.toNat < 2 ^ 28 := by omega
            have hoff_i_cap : ks.alen.toNat + i.toNat < acap := by omega
            c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
            c0_hstep; c0_hstep; c0_hstep; c0_hstep
            refine wp_store_sep
              (KittenMemATactics.store_ka_arena_off _ hoff_i_wrap hoff_i_cap hm')
              fun m hm => ?_
            c0_hsteps!
            have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
            refine ih (i + 1#32, ar.set (ks.alen.toNat + i.toNat) (xs[i.toNat]'hi_xs)) _
              (by dsimp only; rw [hi1]; omega)
              ⟨by dsimp only; rw [hi1]; omega, by simp [har_len], ?_, ?_, ?_⟩
            · intro j hj
              rw [List.getElem?_set_ne (by omega)]; exact har_old j hj
            · intro j hj
              rw [hi1] at hj
              by_cases hji : j = i.toNat
              · subst hji
                rw [List.getElem?_set_self (by rw [har_len]; exact hoff_i_cap),
                  List.getElem?_eq_getElem hi_xs]
              · rw [List.getElem?_set_ne (by omega)]; exact har_new j (by omega)
            · refine Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ _) m) ?_) hm
              have hxs_eq : xs[(BitVec.setWidth 64 i).toNat]'hi_sw = xs[i.toNat]'hi_xs := by
                simp only [hsw_i]
              kstate_ext <;> (first | rfl | rw [hxs_eq])
          · have hi_eq : i.toNat = sz.toNat := by bv_omega
            rw [hi_eq] at har_new
            have hpres := addClause_nonempty_preserves (cid := cid) hinv hlvl0 hte0 heq_nc
              hnc_lt hsz_pos hsz_max hsz_xs hoff_fit har_len har_old har_new hxlits
            c0_hsplit
            · have h1 : (sz == 1#32) = true := beq_iff_eq.mpr ‹_›
              c0_hsteps_nogrp
              c0_hstep
              c0_hsplit
              · have hnu_lt : ks.nunits.toNat < 256 := by
                  revert hc; kp_field; intro hc; bv_omega
                have hnu_wrap : ks.nunits.toNat < 2 ^ 28 := by omega
                c0_hsteps!
                let stBase : KittenState := { ks with arena := ar }
                let stMeta := (((((stBase.putHdr .alen (ks.alen + sz)).putArr .clOff
                  ks.nc.toNat ks.alen).putArr .clMeta ks.nc.toNat sz).putArr .clAux
                  ks.nc.toNat cid).putHdr .nc (ks.nc + 1#32)).putHdr .orig_nc (ks.nc + 1#32)
                let ks' := (stMeta.putArr .units stMeta.nunits.toNat ks.nc).putHdr .nunits
                  (stMeta.nunits + 1#32)
                have hm_ks' : (KittenMemA kPtr acap ks' ⋆
                    (array64 (c.hdr + 32) (hdrTailWords c s) ⋆ Rrest)) m := by
                  refine Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ _) _) ?_) hm
                  dsimp only [ks', stMeta, stBase]; rfl
                dsimp only at hpres
                rw [ite_eq_left ?_] at hpres
                have hsh' := hpres.1.shapes
                have hmF := hreorg hsh' hm_ks'
                have hinv' : KittenScratchInv (scr.take 256 ++ ks'.toSlab) := by
                  refine ⟨by rw [hmF.1]; omega, by rw [hmF.1]; exact c.hscr, ?_⟩
                  rw [hof_slab hsh', show (scr.take 256 ++ ks'.toSlab).length - 8864 = acap by
                    rw [hmF.1]; omega]
                  exact hpres.1
                have horig' : kittenOrigClausesS (scr.take 256 ++ ks'.toSlab) =
                    kittenOrigClausesS scr ++ [(xs.take sz.toNat).map BitVec.toNat] := by
                  unfold kittenOrigClausesS; rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.2.2.2.1
                exact hQ true _ _ hmF.1 hmF.2.1 hinv'
                  (by rw [hof_slab hsh']; exact hpres.2.1)
                  (by rw [hof_slab hsh']; exact hpres.2.2.1)
                  (by rw [hof_slab hsh']; exact hpres.2.2.2.1)
                  (by rw [hof_slab hsh']; rfl)
                  (by rw [hof_slab hsh']; exact hpres.2.2.2.2.1)
                  (by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.1)
                  (by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.1)
                  (by unfold kittenAssumpLitsS; rw [hof_slab hsh']
                      exact hpres.2.2.2.2.2.2.2.2.2.2.2.1)
                  (fun h => by cases h)
                  (fun _ => ⟨by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.1,
                    by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.2.1,
                    by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.2.2.2.2.2,
                    by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.2.2.1, horig',
                    fun _ _ => by rw [hof_slab hsh']; rfl,
                    fun h2 => by
                      have hsz1 : sz = 1#32 := beq_iff_eq.mp h1; rw [hsz1] at h2; simp at h2⟩)
                  hmF.2.2
                exact ⟨h1, by kp_field; exact hnu_lt⟩
              · have hnu_ge : ¬ (ks.nunits.toNat < 256) := by
                  revert hc; kp_field; intro hc; bv_omega
                c0_hsteps!
                let stBase : KittenState := { ks with arena := ar }
                let stMeta := (((((stBase.putHdr .alen (ks.alen + sz)).putArr .clOff
                  ks.nc.toNat ks.alen).putArr .clMeta ks.nc.toNat sz).putArr .clAux
                  ks.nc.toNat cid).putHdr .nc (ks.nc + 1#32)).putHdr .orig_nc (ks.nc + 1#32)
                have hm_stM : (KittenMemA kPtr acap stMeta ⋆
                    (array64 (c.hdr + 32) (hdrTailWords c s) ⋆ Rrest)) m := by
                  refine Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ _) _) ?_) hm
                  dsimp only [stMeta, stBase]; rfl
                dsimp only at hpres
                rw [ite_eq_right ?_, ite_eq_left h1] at hpres
                have hsh' := hpres.1.shapes
                have hmF := hreorg hsh' hm_stM
                have hinv' : KittenScratchInv (scr.take 256 ++ stMeta.toSlab) := by
                  refine ⟨by rw [hmF.1]; omega, by rw [hmF.1]; exact c.hscr, ?_⟩
                  rw [hof_slab hsh', show (scr.take 256 ++ stMeta.toSlab).length - 8864 = acap by
                    rw [hmF.1]; omega]
                  exact hpres.1
                have horig' : kittenOrigClausesS (scr.take 256 ++ stMeta.toSlab) =
                    kittenOrigClausesS scr ++ [(xs.take sz.toNat).map BitVec.toNat] := by
                  unfold kittenOrigClausesS; rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.2.2.2.1
                exact hQ true _ _ hmF.1 hmF.2.1 hinv'
                  (by rw [hof_slab hsh']; exact hpres.2.1)
                  (by rw [hof_slab hsh']; exact hpres.2.2.1)
                  (by rw [hof_slab hsh']; exact hpres.2.2.2.1)
                  (by rw [hof_slab hsh']; rfl)
                  (by rw [hof_slab hsh']; exact hpres.2.2.2.2.1)
                  (by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.1)
                  (by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.1)
                  (by unfold kittenAssumpLitsS; rw [hof_slab hsh']
                      exact hpres.2.2.2.2.2.2.2.2.2.2.2.1)
                  (fun h => by cases h)
                  (fun _ => ⟨by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.1,
                    by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.2.1,
                    by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.2.2.2.2.2,
                    by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.2.2.1, horig',
                    fun _ _ => by rw [hof_slab hsh']; rfl,
                    fun h2 => by
                      have hsz1 : sz = 1#32 := beq_iff_eq.mp h1; rw [hsz1] at h2; simp at h2⟩)
                  hmF.2.2
                exact fun h => hnu_ge (by have h2 := h.2; revert h2; kp_field; exact id)
            · have hne1 : (sz == 1#32) = false := beq_false_of_ne ‹_›
              have hne1' : (sz == 1#32) ≠ true := by simp [hne1]
              have hsz2 : 2 ≤ sz.toNat := by
                have hne : sz.toNat ≠ 1 := fun hz => (‹sz ≠ 1#32›) (BitVec.eq_of_toNat_eq hz)
                omega
              have h0_lt : 0 < xs.length := by omega
              have h1_lt : 1 < xs.length := by omega
              c0_hsteps_nogrp
              let stBase : KittenState := { ks with arena := ar }
              let stMeta := (((((stBase.putHdr .alen (ks.alen + sz)).putArr .clOff
                ks.nc.toNat ks.alen).putArr .clMeta ks.nc.toNat sz).putArr .clAux
                ks.nc.toNat cid).putHdr .nc (ks.nc + 1#32)).putHdr .orig_nc (ks.nc + 1#32)
              dsimp only at hpres
              rw [ite_eq_right (fun h => hne1' h.1), ite_eq_right hne1'] at hpres
              c0_call hWatch
              have hsh_meta := hsh_ar.putHdr .alen (ks.alen + sz) |>.putArr .clOff ks.nc.toNat
                ks.alen |>.putArr .clMeta ks.nc.toNat sz |>.putArr .clAux ks.nc.toNat cid
                |>.putHdr .nc (ks.nc + 1#32) |>.putHdr .orig_nc (ks.nc + 1#32)
              have hm_nv : stMeta.nv = ks.nv := by dsimp only [stMeta, stBase]; kp_field
              have hx0 : (xs[0]'h0_lt).toNat < 2 * stMeta.nv.toNat := by
                rw [hm_nv]; have := hxlits 0 (by omega)
                rwa [List.getElem?_eq_getElem h0_lt, Option.getD_some] at this
              have hx1 : (xs[1]'h1_lt).toNat < 2 * stMeta.nv.toNat := by
                rw [hm_nv]; have := hxlits 1 (by omega)
                rwa [List.getElem?_eq_getElem h1_lt, Option.getD_some] at this
              obtain ⟨_, hm_w⟩ := kittenMemA_to_mem hm
              refine ⟨acap, stMeta, array64 (c.hdr + 32) (hdrTailWords c s) ⋆ Rrest,
                hsh_meta, hacap_lt, by rw [hm_nv]; exact hnv, hnc_896, hx0, hx1, hm_w,
                fun mW hmW => ?_⟩
              c0_hsteps!
              have hx0_bang : xs[0]! = xs[0]'h0_lt := by
                simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h0_lt]
              have hx1_bang : xs[1]! = xs[1]'h1_lt := by
                simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h1_lt]
              let ks' := kittenWatchStep stMeta ks.nc (xs[0]!) (xs[1]!)
              have hmW' : (KittenMem kPtr ks' ⋆
                  (array64 (c.hdr + 32) (hdrTailWords c s) ⋆ Rrest)) mW := by
                refine Eq.mp (congrArg (fun x => (KittenMem kPtr x ⋆
                    (array64 (c.hdr + 32) (hdrTailWords c s) ⋆ Rrest)) mW) ?_) hmW
                dsimp only [ks']; rw [hx0_bang, hx1_bang]; rfl
              have hsh' := hpres.1.shapes
              have hmF := hreorg hsh' (kittenMem_to_amem hsh' hmW')
              have hinv' : KittenScratchInv (scr.take 256 ++ ks'.toSlab) := by
                refine ⟨by rw [hmF.1]; omega, by rw [hmF.1]; exact c.hscr, ?_⟩
                rw [hof_slab hsh', show (scr.take 256 ++ ks'.toSlab).length - 8864 = acap by
                  rw [hmF.1]; omega]
                exact hpres.1
              have horig' : kittenOrigClausesS (scr.take 256 ++ ks'.toSlab) =
                  kittenOrigClausesS scr ++ [(xs.take sz.toNat).map BitVec.toNat] := by
                unfold kittenOrigClausesS; rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.2.2.2.1
              have hw0_n : (ks.nc <<< (1 : Nat)).toNat = 2 * ks.nc.toNat :=
                (bv32_cid_to_w0_lt hnc_896 (Nat.le_refl _)).1
              have hw1_n : ((ks.nc <<< (1 : Nat)) ||| 1#32).toNat = 2 * ks.nc.toNat + 1 :=
                (bv32_cid_to_w1_lt hnc_896 (Nat.le_refl _)).1
              have hwb_len : stMeta.wblit.length = 1792 := hsh_meta.wblit_len
              have hwb_old : ∀ w < 2 * ks.nc.toNat, ks'.wblit[w]? = ks.wblit[w]? := by
                intro w hw
                change ((stMeta.wblit.set (ks.nc <<< (1 : Nat)).toNat (xs[1]!)).set
                  ((ks.nc <<< (1 : Nat)) ||| 1#32).toNat (xs[0]!))[w]? = ks.wblit[w]?
                rw [hw0_n, hw1_n, List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                rfl
              have hwb_new : ks'.wblit[2 * ks.nc.toNat]? = xs[1]? ∧
                  ks'.wblit[2 * ks.nc.toNat + 1]? = xs[0]? := by
                constructor
                · change ((stMeta.wblit.set (ks.nc <<< (1 : Nat)).toNat (xs[1]!)).set
                    ((ks.nc <<< (1 : Nat)) ||| 1#32).toNat (xs[0]!))[2 * ks.nc.toNat]? = xs[1]?
                  rw [hw0_n, hw1_n, List.getElem?_set_ne (by omega),
                    List.getElem?_set_self (by rw [hwb_len]; omega),
                    List.getElem?_eq_getElem h1_lt, hx1_bang]
                · change ((stMeta.wblit.set (ks.nc <<< (1 : Nat)).toNat (xs[1]!)).set
                    ((ks.nc <<< (1 : Nat)) ||| 1#32).toNat (xs[0]!))[2 * ks.nc.toNat + 1]? = xs[0]?
                  rw [hw0_n, hw1_n,
                    List.getElem?_set_self (by rw [List.length_set, hwb_len]; omega),
                    List.getElem?_eq_getElem h0_lt, hx0_bang]
              exact hQ true _ _ hmF.1 hmF.2.1 hinv'
                (by rw [hof_slab hsh']; exact hpres.2.1)
                (by rw [hof_slab hsh']; exact hpres.2.2.1)
                (by rw [hof_slab hsh']; exact hpres.2.2.2.1)
                (by rw [hof_slab hsh']; rfl)
                (by rw [hof_slab hsh']; exact hpres.2.2.2.2.1)
                (by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.1)
                (by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.1)
                (by unfold kittenAssumpLitsS; rw [hof_slab hsh']
                    exact hpres.2.2.2.2.2.2.2.2.2.2.2.1)
                (fun h => by cases h)
                (fun _ => ⟨by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.1,
                  by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.2.1,
                  by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.2.2.2.2.2,
                  by rw [hof_slab hsh']; exact hpres.2.2.2.2.2.2.2.2.2.1, horig',
                  fun w hw => by rw [hof_slab hsh']; exact hwb_old w hw,
                  fun _ => by rw [hof_slab hsh']; exact hwb_new⟩)
                hmF.2.2

/-! ### `full_kitten_learn_unit0` Pure Helpers & `Func.wp` Proof (`7/15`) -/

private def learnUnit0RcsTake (ks : KittenState) (lit src_cid : BitVec 32) (n : Nat) :
    List (BitVec 32) :=
  let soff := kittenClauseOff ks src_cid.toNat
  let ssz := kittenClauseSize ks src_cid.toNat
  (((ks.arena.drop soff).take ssz).take n).filterMap fun ot =>
    if ot ≠ lit then
      let rc := ks.rsn[ot.toNat / 2]?.getD 0xFFFFFFFF#32
      if rc ≠ 0xFFFFFFFF#32 then some rc else none
    else none

private def learnUnit0Ants (ks : KittenState) (lit src_cid : BitVec 32) (from_res : Bool) :
    List (BitVec 32) :=
  if ks.ante = 0#32 then []
  else if from_res then ks.res.take ks.nres.toNat
  else src_cid :: learnUnit0RcsTake ks lit src_cid (kittenClauseSize ks src_cid.toNat)

private theorem learnUnit0RcsTake_zero (ks : KittenState) (lit src_cid : BitVec 32) :
    learnUnit0RcsTake ks lit src_cid 0 = [] := by
  simp [learnUnit0RcsTake]

private theorem list_filterMap_take_le {α β : Type} (f : α → Option β) (xs : List α)
    {m n : Nat} (hmn : m ≤ n) :
    ((xs.take m).filterMap f).length ≤ ((xs.take n).filterMap f).length := by
  induction h : n - m generalizing m n with
  | zero =>
    have heq : m = n := by omega
    subst heq; exact Nat.le_refl _
  | succ d ih =>
    have hm_lt : m < n := by omega
    have h1 := ih (m := m) (n := n - 1) (by omega) (by omega)
    have hstep : ((xs.take (n - 1)).filterMap f).length ≤ ((xs.take n).filterMap f).length := by
      by_cases hlen : n - 1 < xs.length
      · rw [show n = n - 1 + 1 by omega, List.take_succ_eq_append_getElem hlen,
          List.filterMap_append, List.length_append]
        exact Nat.le_add_right _ _
      · rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
        exact Nat.le_refl _
    exact Nat.le_trans h1 hstep

private theorem learnUnit0RcsTake_mono {ks : KittenState} {lit src_cid : BitVec 32}
    {m n : Nat} (hmn : m ≤ n) :
    (learnUnit0RcsTake ks lit src_cid m).length ≤ (learnUnit0RcsTake ks lit src_cid n).length :=
  list_filterMap_take_le _ _ hmn

private theorem learnUnit0RcsTake_le {ks : KittenState} {lit src_cid : BitVec 32} {n : Nat} :
    (learnUnit0RcsTake ks lit src_cid n).length ≤ n := by
  unfold learnUnit0RcsTake; dsimp only
  exact Nat.le_trans (List.length_filterMap_le _ _) (List.length_take_le _ _)

private theorem learnUnit0RcsTake_succ {ks : KittenState} {lit src_cid : BitVec 32} {i : Nat}
    (hi : i < kittenClauseSize ks src_cid.toNat)
    (hle : kittenClauseOff ks src_cid.toNat + kittenClauseSize ks src_cid.toNat ≤ ks.arena.length) :
    let ot := ks.arena[kittenClauseOff ks src_cid.toNat + i]'(by omega)
    let rc := ks.rsn[ot.toNat / 2]?.getD 0xFFFFFFFF#32
    learnUnit0RcsTake ks lit src_cid (i + 1) =
      learnUnit0RcsTake ks lit src_cid i ++
        if ot ≠ lit then if rc ≠ 0xFFFFFFFF#32 then [rc] else [] else [] := by
  intro ot rc
  unfold learnUnit0RcsTake
  dsimp only
  have hlen : ((ks.arena.drop (kittenClauseOff ks src_cid.toNat)).take
      (kittenClauseSize ks src_cid.toNat)).length = kittenClauseSize ks src_cid.toNat := by
    simp [List.length_take, List.length_drop]; omega
  have htake := List.take_succ_eq_append_getElem (i := i) (by omega :
    i < ((ks.arena.drop (kittenClauseOff ks src_cid.toNat)).take
      (kittenClauseSize ks src_cid.toNat)).length)
  have hget : ((ks.arena.drop (kittenClauseOff ks src_cid.toNat)).take
      (kittenClauseSize ks src_cid.toNat))[i]'(by omega) = ot := by
    simp [ot, List.getElem_take, List.getElem_drop]
  rw [htake, hget, List.filterMap_append]
  congr 1
  simp only [List.filterMap_cons, List.filterMap_nil]
  by_cases h1 : ot = lit <;> by_cases h2 : rc = 0xFFFFFFFF#32 <;> simp [rc, h1, h2]

private theorem learnUnit0RcsTake_eq_res {ks : KittenState} {lit src_cid : BitVec 32}
    (hle : kittenClauseOff ks src_cid.toNat + kittenClauseSize ks src_cid.toNat ≤ ks.arena.length)
    (hfls : ∀ l ∈ kittenClauseLits ks src_cid.toNat, l ≠ lit.toNat →
      let r := (ks.rsn[l / 2]?.getD 0xFFFFFFFF#32).toNat
      r < ks.nc.toNat ∧ kittenClauseLits ks r = [l ^^^ 1])
    (hnc : ks.nc.toNat ≤ kMaxCl) (hsrc : src_cid.toNat < ks.nc.toNat) :
    let ants := src_cid :: learnUnit0RcsTake ks lit src_cid (kittenClauseSize ks src_cid.toNat)
    (∀ a ∈ ants.map BitVec.toNat, a < ks.nc.toNat) ∧
    (cnfOfClauses ((ants.map BitVec.toNat).map (kittenClauseLits ks))).EntailsClause
      (cnfClause [lit.toNat]) := by
  intro ants
  let ssz := kittenClauseSize ks src_cid.toNat
  let soff := kittenClauseOff ks src_cid.toNat
  have hrcs_lt : ∀ a ∈ learnUnit0RcsTake ks lit src_cid ssz, a.toNat < ks.nc.toNat := by
    intro a ha
    unfold learnUnit0RcsTake at ha
    dsimp only at ha
    rw [List.mem_filterMap] at ha
    obtain ⟨ot, hot, hif⟩ := ha
    have hot' : ot ∈ (ks.arena.drop (kittenClauseOff ks src_cid.toNat)).take
        (kittenClauseSize ks src_cid.toNat) := by
      rw [show ssz = kittenClauseSize ks src_cid.toNat from rfl,
        List.take_take, Nat.min_self] at hot
      exact hot
    have hot_l : ot.toNat ∈ kittenClauseLits ks src_cid.toNat :=
      List.mem_map.mpr ⟨ot, hot', rfl⟩
    split at hif
    · rename_i hne
      have hne' : ot.toNat ≠ lit.toNat := fun he => hne (BitVec.eq_of_toNat_eq he)
      have hr := hfls ot.toNat hot_l hne'
      split at hif
      · simp only [Option.some.injEq] at hif
        rw [← hif]; exact hr.1
      · simp at hif
    · simp at hif
  refine ⟨?_, ?_⟩
  · intro a ha
    rw [List.mem_map] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    rcases List.mem_cons.mp hb with rfl | hmem
    · exact hsrc
    · exact hrcs_lt b hmem
  · rw [CNF.entails_clause_def]
    intro α hα
    rw [cnf_sat_cnfOfClauses_iff] at hα
    have hsat_src := hα (kittenClauseLits ks src_cid.toNat)
      (List.mem_map.mpr ⟨src_cid.toNat, List.mem_map.mpr
        ⟨src_cid, List.mem_cons_self, rfl⟩, rfl⟩)
    obtain ⟨l, hl_mem, hlsat⟩ := (clause_sat_cnfClause_iff α _).mp hsat_src
    by_cases hll : l = lit.toNat
    · rw [hll] at hlsat; exact (sat_cnfClause_singleton α _).mpr hlsat
    · have hl_lit : l ∈ kittenClauseLits ks src_cid.toNat := hl_mem
      unfold kittenClauseLits at hl_mem
      rw [List.mem_map] at hl_mem
      obtain ⟨ot, hot, rfl⟩ := hl_mem
      have hne : ot ≠ lit := fun he => hll (congrArg BitVec.toNat he)
      have hr := hfls ot.toNat hl_lit hll
      let rc := ks.rsn[ot.toNat / 2]?.getD 0xFFFFFFFF#32
      have hrc_ne : rc ≠ 0xFFFFFFFF#32 := by
        intro heq
        have hlt := hr.1
        dsimp only [rc] at heq
        rw [heq] at hlt
        unfold kMaxCl at hnc
        change 2 ^ 32 - 1 < ks.nc.toNat at hlt
        omega
      have hrc_mem : rc ∈ learnUnit0RcsTake ks lit src_cid ssz := by
        unfold learnUnit0RcsTake
        dsimp only
        rw [List.mem_filterMap]
        refine ⟨ot, ?_, by simp [rc, hne, hrc_ne]⟩
        rw [show ssz = kittenClauseSize ks src_cid.toNat from rfl, List.take_take, Nat.min_self]
        exact hot
      have hsat_rc := hα (kittenClauseLits ks rc.toNat)
        (List.mem_map.mpr ⟨rc.toNat, List.mem_map.mpr
          ⟨rc, List.mem_cons_of_mem _ hrc_mem, rfl⟩, rfl⟩)
      rw [hr.2] at hsat_rc
      have hneg := (sat_cnfClause_litNeg_iff α ot.toNat).mp hsat_rc
      exact absurd ((sat_cnfClause_singleton α ot.toNat).mpr hlsat) hneg

private theorem learnUnit0AddUnit_preserves {acap : Nat} {ks : KittenState} {cid : BitVec 32}
    (hsh : ks.ShapesOk acap) (hcl : KittenClausesOk acap ks)
    (hcid : cid.toNat < ks.nc.toNat) (hsz1 : kittenClauseSize ks cid.toNat = 1)
    (hnu : ks.nunits.toNat < 256) :
    let stU : KittenState :=
      { ks with units := ks.units.set ks.nunits.toNat cid, nunits := ks.nunits + 1#32 }
    stU.ShapesOk acap ∧ KittenClausesOk acap stU := by
  intro stU
  have hsh' : stU.ShapesOk acap :=
    (hsh.putArr .units ks.nunits.toNat cid).putHdr .nunits (ks.nunits + 1#32)
  have hun_len : ks.nunits.toNat < ks.units.length := by rw [hsh.units_len]; exact hnu
  have hun1 : (ks.nunits + 1#32).toNat = ks.nunits.toNat + 1 := by bv_omega
  have hcl' : KittenClausesOk acap stU := by
    refine ⟨hcl.acap_ge, hcl.acap_lt, hcl.acap_eq, hcl.nv_le, hcl.nc_le,
      hcl.orig_nc_le, hcl.orig_nc_max, hcl.alen_le, hcl.nassump_le,
      by change (ks.nunits + 1#32).toNat ≤ kMaxL; rw [hun1]; unfold kMaxL; exact hnu,
      hcl.nres_le, hcl.nkl_le, hcl.nana_le, hcl.cl_wf, hcl.cl_mono,
      ?_, hcl.incons_ok, hcl.failing_ok, hcl.assump_ok, hcl.flags_clean⟩
    intro ui hui
    change ui < (ks.nunits + 1#32).toNat at hui
    rw [hun1] at hui
    by_cases huin : ui = ks.nunits.toNat
    · subst huin
      have hget : stU.units[ks.nunits.toNat]? = some cid := by
        change (ks.units.set ks.nunits.toNat cid)[ks.nunits.toNat]? = some cid
        rw [List.getElem?_set_self hun_len]
      dsimp only; rw [hget, Option.getD_some]
      exact ⟨hcid, hsz1⟩
    · have hget : stU.units[ui]? = ks.units[ui]? := by
        change (ks.units.set ks.nunits.toNat cid)[ui]? = ks.units[ui]?
        rw [List.getElem?_set_ne (Ne.symm huin)]
      dsimp only; rw [hget]
      exact hcl.units_ok ui (by omega)
  exact ⟨hsh', hcl'⟩

private theorem learnUnit0Meta_preserves {acap : Nat} {ks : KittenState} {lit src_cid : BitVec 32}
    {from_res : Bool} {ar' : List (BitVec 32)}
    (hsh : ks.ShapesOk acap) (hcl : KittenClausesOk acap ks)
    (hlit : lit.toNat < 2 * ks.nv.toNat)
    (hsrc : from_res = false → src_cid.toNat < ks.nc.toNat)
    (hfls : ks.ante ≠ 0#32 → from_res = false →
      ∀ l ∈ kittenClauseLits ks src_cid.toNat, l ≠ lit.toNat →
        let r := (ks.rsn[l / 2]?.getD 0xFFFFFFFF#32).toNat
        r < ks.nc.toNat ∧ kittenClauseLits ks r = [l ^^^ 1])
    (hres : ks.ante ≠ 0#32 → from_res = true → ks.nres.toNat ≤ kMaxL ∧
      (∀ i < ks.nres.toNat, (ks.res[i]?.getD 0xFFFFFFFF#32).toNat < ks.nc.toNat) ∧
      (cnfOfClauses ((ks.res.take ks.nres.toNat).map fun c =>
        kittenClauseLits ks c.toNat)).EntailsClause (cnfClause [lit.toNat]))
    (hent_lit : (cnfOfClauses (kittenOrigClauses ks)).EntailsClause (cnfClause [lit.toNat]))
    (hnc_lt : ks.nc.toNat < kMaxCl)
    (hfit : ks.alen.toNat + 1 + (learnUnit0Ants ks lit src_cid from_res).length ≤ ks.acap.toNat)
    (har_len : ar'.length = acap)
    (har_old : ∀ j < ks.alen.toNat, ar'[j]? = ks.arena[j]?)
    (har_lit : ar'[ks.alen.toNat]? = some lit)
    (har_ants : ∀ j < (learnUnit0Ants ks lit src_cid from_res).length,
      ar'[ks.alen.toNat + 1 + j]? = some ((learnUnit0Ants ks lit src_cid from_res)[j]!)) :
    let ants := learnUnit0Ants ks lit src_cid from_res
    let na := BitVec.ofNat 32 ants.length
    let ap := ks.alen + 1#32 + na
    let nc := ks.nc
    let off := ks.alen
    let stMeta : KittenState :=
      { ks with
        alen := ap, nc := nc + 1#32, arena := ar',
        clOff := ks.clOff.set nc.toNat off,
        clMeta := ks.clMeta.set nc.toNat (1#32 ||| kmLrn),
        clAux := ks.clAux.set nc.toNat na }
    stMeta.ShapesOk acap ∧ KittenClausesOk acap stMeta ∧ stMeta.nc = nc + 1#32 ∧
    KittenUnit0Preserved ks stMeta ∧ kittenClauseSize stMeta nc.toNat = 1 ∧
    kittenClauseLits stMeta nc.toNat = [lit.toNat] := by
  intro ants na ap nc off stMeta
  have hnc_wrap : nc.toNat < kMaxCl := hnc_lt
  have hnc1 : (nc + 1#32).toNat = nc.toNat + 1 := by
    dsimp only [nc] at hnc_wrap ⊢; unfold kMaxCl at hnc_wrap; bv_omega
  have hacap_32 : acap < 2 ^ 32 := Nat.lt_trans hcl.acap_lt (by decide)
  have hca : ks.acap.toNat = acap := by
    rw [hcl.acap_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hacap_32]
  have hna_lt : ants.length < 2 ^ 32 := by dsimp only [ants]; have := hcl.acap_lt; omega
  have hna_toNat : na.toNat = ants.length := by
    dsimp only [na, ants]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by dsimp only [ants] at hna_lt; exact hna_lt)]
  have hap_toNat : ap.toNat = off.toNat + 1 + ants.length := by
    have hal := hcl.alen_le
    have hac : acap < 2 ^ 28 := hcl.acap_lt
    dsimp only [ap, off] at hfit ⊢
    rw [← hna_toNat] at hfit ⊢
    have hna_le : na.toNat ≤ acap := by omega
    bv_omega
  have hap_le : ap.toNat ≤ acap := by dsimp only [off, ants] at hap_toNat hfit ⊢; omega
  have har_old_len := hsh.arena_len
  have hco_len : nc.toNat < ks.clOff.length := by rw [hsh.clOff_len]; exact hnc_lt
  have hcm_len : nc.toNat < ks.clMeta.length := by rw [hsh.clMeta_len]; exact hnc_lt
  have hca_len : nc.toNat < ks.clAux.length := by rw [hsh.clAux_len]; exact hnc_lt
  have hsh_meta : stMeta.ShapesOk acap := by
    refine ⟨hsh.hdrTail_len, hsh.lvlArr_len, hsh.rsn_len, hsh.qprev_len, hsh.qnext_len,
      hsh.qstampArr_len, hsh.trl_len, hsh.flags_len, hsh.vals_len, hsh.assump_len, hsh.ana_len,
      hsh.kl_len, hsh.units_len, hsh.res_len, hsh.whead_len, hsh.wnext_len, hsh.wblit_len,
      by simp [stMeta, hsh.clOff_len], by simp [stMeta, hsh.clMeta_len],
      by simp [stMeta, hsh.clAux_len], har_len⟩
  have hcl_old : ∀ c < nc.toNat,
      kittenClauseOff stMeta c = kittenClauseOff ks c ∧
      kittenClauseMeta stMeta c = kittenClauseMeta ks c ∧
      kittenClauseAux stMeta c = kittenClauseAux ks c ∧
      kittenClauseSize stMeta c = kittenClauseSize ks c ∧
      kittenClauseIsLrn stMeta c = kittenClauseIsLrn ks c ∧
      kittenClauseSpan stMeta c = kittenClauseSpan ks c ∧
      kittenClauseLits stMeta c = kittenClauseLits ks c ∧
      kittenClauseAnts stMeta c = kittenClauseAnts ks c := by
    intro c hc
    have hne : nc.toNat ≠ c := Nat.ne_of_gt hc
    have hco : kittenClauseOff stMeta c = kittenClauseOff ks c := by
      simp only [kittenClauseOff, stMeta, List.getElem?_set_ne hne]
    have hcm : kittenClauseMeta stMeta c = kittenClauseMeta ks c := by
      simp only [kittenClauseMeta, stMeta, List.getElem?_set_ne hne]
    have hca' : kittenClauseAux stMeta c = kittenClauseAux ks c := by
      simp only [kittenClauseAux, stMeta, List.getElem?_set_ne hne]
    have hsz : kittenClauseSize stMeta c = kittenClauseSize ks c := by
      simp only [kittenClauseSize, hcm]
    have his : kittenClauseIsLrn stMeta c = kittenClauseIsLrn ks c := by
      simp only [kittenClauseIsLrn, hcm]
    have hsp : kittenClauseSpan stMeta c = kittenClauseSpan ks c := by
      simp only [kittenClauseSpan, hsz, his, hca']
    have hwf := hcl.cl_wf c hc
    have hle_c : kittenClauseOff ks c + kittenClauseSpan ks c ≤ ks.alen.toNat := hwf.2.2.1
    have hsz_le : kittenClauseOff ks c + kittenClauseSize ks c ≤ ks.alen.toNat := by
      unfold kittenClauseSpan at hle_c; omega
    have har_lits : (ar'.drop (kittenClauseOff ks c)).take (kittenClauseSize ks c) =
        (ks.arena.drop (kittenClauseOff ks c)).take (kittenClauseSize ks c) := by
      apply List.ext_getElem
      · simp [List.length_take, List.length_drop, har_len, har_old_len]
      · intro j hj1 hj2
        have hj_sz : j < kittenClauseSize ks c := by simp at hj1; omega
        simp only [List.getElem_take, List.getElem_drop]
        have ha1 := har_old (kittenClauseOff ks c + j) (by omega)
        rw [List.getElem?_eq_getElem (by have := hcl.alen_le; omega :
            kittenClauseOff ks c + j < ar'.length),
          List.getElem?_eq_getElem (by have := hcl.alen_le; omega :
            kittenClauseOff ks c + j < ks.arena.length)] at ha1
        exact Option.some.inj ha1
    have hlits : kittenClauseLits stMeta c = kittenClauseLits ks c := by
      simp only [kittenClauseLits, hco, hsz]
      exact congrArg (List.map BitVec.toNat) har_lits
    have hants : kittenClauseAnts stMeta c = kittenClauseAnts ks c := by
      unfold kittenClauseAnts
      rw [his, hco, hsz, hca']
      split
      · congr 1
        apply List.ext_getElem
        · simp [List.length_take, List.length_drop, show stMeta.arena.length = acap from har_len,
            har_old_len]
        · intro j hj1 hj2
          have hj_au : j < kittenClauseAux ks c := by simp at hj1; omega
          simp only [List.getElem_take, List.getElem_drop]
          have hsp_eq : kittenClauseSpan ks c = kittenClauseSize ks c + kittenClauseAux ks c := by
            simp [kittenClauseSpan, ‹kittenClauseIsLrn ks c = true›]
          have ha1 := har_old (kittenClauseOff ks c + kittenClauseSize ks c + j) (by omega)
          rw [List.getElem?_eq_getElem (by have := hcl.alen_le; omega :
              kittenClauseOff ks c + kittenClauseSize ks c + j < ar'.length),
            List.getElem?_eq_getElem (by have := hcl.alen_le; omega :
              kittenClauseOff ks c + kittenClauseSize ks c + j < ks.arena.length)] at ha1
          exact Option.some.inj ha1
      · rfl
    exact ⟨hco, hcm, hca', hsz, his, hsp, hlits, hants⟩
  have hco_new : kittenClauseOff stMeta nc.toNat = off.toNat := by
    simp [kittenClauseOff, stMeta, List.getElem?_set_self hco_len]
  have hcm_new : kittenClauseMeta stMeta nc.toNat = (1#32 ||| kmLrn) := by
    simp [kittenClauseMeta, stMeta, List.getElem?_set_self hcm_len]
  have hca_new : kittenClauseAux stMeta nc.toNat = ants.length := by
    simp [kittenClauseAux, stMeta, List.getElem?_set_self hca_len, hna_toNat]
  have hsz_new : kittenClauseSize stMeta nc.toNat = 1 := by
    rw [kittenClauseSize, hcm_new]; decide
  have his_new : kittenClauseIsLrn stMeta nc.toNat = true := by
    rw [kittenClauseIsLrn, hcm_new]; decide
  have hsp_new : kittenClauseSpan stMeta nc.toNat = 1 + ants.length := by
    simp [kittenClauseSpan, hsz_new, his_new, hca_new]
  have hlits_new : kittenClauseLits stMeta nc.toNat = [lit.toNat] := by
    simp only [kittenClauseLits, hco_new, hsz_new]
    change ((ar'.drop off.toNat).take 1).map BitVec.toNat = [lit.toNat]
    have hlt_ar : off.toNat < ar'.length := by dsimp only [off]; have := hcl.alen_le; omega
    have htake1 : (ar'.drop off.toNat).take 1 = [ar'[off.toNat]'hlt_ar] := by
      apply List.ext_getElem
      · simp [List.length_take, List.length_drop]; omega
      · intro k hk1 hk2
        have hk0 : k = 0 := by simp at hk1; omega
        subst hk0; simp [List.getElem_take, List.getElem_drop]
    rw [htake1, List.map_singleton]
    have ha := har_lit
    rw [List.getElem?_eq_getElem hlt_ar] at ha
    rw [← Option.some.inj ha]
  have hants_new : kittenClauseAnts stMeta nc.toNat = ants.map BitVec.toNat := by
    simp only [kittenClauseAnts, his_new, ite_true, hco_new, hsz_new, hca_new]
    change ((ar'.drop (off.toNat + 1)).take ants.length).map BitVec.toNat = ants.map BitVec.toNat
    congr 1
    apply List.ext_getElem
    · simp [List.length_take, List.length_drop]; omega
    · intro j hj1 hj2
      simp only [List.getElem_take, List.getElem_drop]
      have ha := har_ants j hj2
      rw [List.getElem?_eq_getElem (by omega : off.toNat + 1 + j < ar'.length)] at ha
      have hbang : ants[j]! = ants[j] := by
        simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hj2]
      rw [hbang] at ha
      exact Option.some.inj ha
  have horig_meta : kittenOrigClauses stMeta = kittenOrigClauses ks :=
    kittenOrigClauses_eq_of rfl fun i hi =>
      (hcl_old i (Nat.lt_of_lt_of_le hi hcl.orig_nc_le)).2.2.2.2.2.2.1
  have hants_ok : ks.ante ≠ 0#32 →
      (∀ a ∈ ants.map BitVec.toNat, a < nc.toNat) ∧
      (cnfOfClauses ((ants.map BitVec.toNat).map (kittenClauseLits stMeta))).EntailsClause
        (cnfClause [lit.toNat]) := by
    intro hante
    have hsub : ∀ xs : List Nat, (∀ a ∈ xs, a < nc.toNat) →
        xs.map (kittenClauseLits stMeta) = xs.map (kittenClauseLits ks) := fun xs hxs =>
      List.map_congr_left fun a ha => (hcl_old a (hxs a ha)).2.2.2.2.2.2.1
    cases hfr : from_res with
    | true =>
      have ⟨_, hr_lt, hr_ent⟩ := hres hante hfr
      have hants_eq : ants = ks.res.take ks.nres.toNat := by
        dsimp only [ants, learnUnit0Ants]; simp [hante, hfr]
      have hall : ∀ a ∈ ants.map BitVec.toNat, a < nc.toNat := by
        intro a ha
        rw [hants_eq, List.mem_map] at ha
        obtain ⟨b, hb, rfl⟩ := ha
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
        have hj_nr : j < ks.nres.toNat := by simp at hj; omega
        have hj_res : j < ks.res.length := by
          rw [hsh.res_len]; have := (hres hante hfr).1; unfold kMaxL at this; omega
        have hj_lt := hr_lt j hj_nr
        rw [List.getElem?_eq_getElem hj_res, Option.getD_some] at hj_lt
        rw [List.getElem_take]
        exact hj_lt
      refine ⟨hall, ?_⟩
      rw [hsub _ hall, hants_eq]
      simp only [List.map_take, List.map_map, Function.comp_def] at hr_ent ⊢
      exact hr_ent
    | false =>
      have hants_eq : ants =
          src_cid :: learnUnit0RcsTake ks lit src_cid (kittenClauseSize ks src_cid.toNat) := by
        dsimp only [ants, learnUnit0Ants]; simp [hante, hfr]
      have hsrc' := hsrc hfr
      have hle_src := (hcl.cl_wf src_cid.toNat hsrc').2.2.1
      have hle_ar : kittenClauseOff ks src_cid.toNat + kittenClauseSize ks src_cid.toNat ≤
          ks.arena.length := by
        have := hcl.alen_le; unfold kittenClauseSpan at hle_src; omega
      have ⟨hall, hent⟩ := learnUnit0RcsTake_eq_res hle_ar (hfls hante hfr) hcl.nc_le hsrc'
      rw [← hants_eq] at hall hent
      exact ⟨hall, by rw [hsub _ hall]; exact hent⟩
  have hcl_meta : KittenClausesOk acap stMeta := by
    refine ⟨hcl.acap_ge, hcl.acap_lt, hcl.acap_eq, hcl.nv_le,
      by change (nc + 1#32).toNat ≤ kMaxCl; rw [hnc1]; exact hnc_lt,
      by change ks.orig_nc.toNat ≤ (nc + 1#32).toNat
         rw [hnc1]; exact Nat.le_succ_of_le hcl.orig_nc_le,
      hcl.orig_nc_max,
      by change ap.toNat ≤ acap; exact hap_le,
      hcl.nassump_le, hcl.nunits_le, hcl.nres_le, hcl.nkl_le, hcl.nana_le,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro c hc
      change c < (nc + 1#32).toNat at hc
      rw [hnc1] at hc
      by_cases hcn : c = nc.toNat
      · subst hcn
        have hdecide : decide (stMeta.orig_nc.toNat ≤ nc.toNat) = true :=
          decide_eq_true hcl.orig_nc_le
        refine ⟨by rw [his_new, hdecide], fun _ => by rw [hsz_new]; exact Nat.le_refl _,
          by rw [hco_new, hsp_new, show stMeta.alen = ap from rfl]; omega,
          fun l hl => by rw [hlits_new] at hl; simp at hl; rw [hl]; exact hlit,
          by rw [hlits_new, horig_meta]; exact hent_lit,
          fun hante _ => by
            have ⟨h1, h2⟩ := hants_ok hante
            rw [hants_new, hlits_new]; exact ⟨h1, h2⟩⟩
      · have hc' : c < nc.toNat := by omega
        have ho := hcl_old c hc'
        have hw := hcl.cl_wf c hc'
        refine ⟨by rw [ho.2.2.2.2.1]; exact hw.1,
          fun h => by rw [ho.2.2.2.1]; exact hw.2.1 h,
          by rw [ho.1, ho.2.2.2.2.2.1, show stMeta.alen = ap from rfl]
             have := hw.2.2.1; change kittenClauseOff ks c + kittenClauseSpan ks c ≤ _
             dsimp only [off] at hap_toNat; omega,
          fun l hl => by rw [ho.2.2.2.2.2.2.1] at hl; exact hw.2.2.2.1 l hl,
          by rw [ho.2.2.2.2.2.2.1, horig_meta]; exact hw.2.2.2.2.1,
          fun hante hge => ?_⟩
        have ⟨ha1, ha2⟩ := hw.2.2.2.2.2 hante hge
        refine ⟨by rw [ho.2.2.2.2.2.2.2]; exact ha1, ?_⟩
        rw [ho.2.2.2.2.2.2.2, ho.2.2.2.2.2.2.1]
        have hmeq : (kittenClauseAnts ks c).map (kittenClauseLits stMeta) =
            (kittenClauseAnts ks c).map (kittenClauseLits ks) :=
          List.map_congr_left fun a ha =>
            (hcl_old a (Nat.lt_trans (ha1 a ha) hc')).2.2.2.2.2.2.1
        rw [hmeq]; exact ha2
    · intro c1 c2 h12 hc2
      change c2 < (nc + 1#32).toNat at hc2
      rw [hnc1] at hc2
      have ho1 := hcl_old c1 (by omega)
      by_cases hc2n : c2 = nc.toNat
      · subst hc2n; rw [ho1.1, ho1.2.2.2.2.2.1, hco_new]
        exact (hcl.cl_wf c1 (by omega)).2.2.1
      · have hc2_lt : c2 < nc.toNat := by omega
        have ho2 := hcl_old c2 hc2_lt
        rw [ho1.1, ho1.2.2.2.2.2.1, ho2.1]
        exact hcl.cl_mono c1 c2 h12 hc2_lt
    · intro ui hui
      have hst_nu : stMeta.nunits = ks.nunits := rfl
      have hst_un : stMeta.units = ks.units := rfl
      have hst_nc : stMeta.nc = nc + 1#32 := rfl
      rw [hst_nu] at hui
      have hu := hcl.units_ok ui hui
      have ho := hcl_old (ks.units[ui]?.getD 0#32).toNat hu.1
      rw [hst_un, hst_nc, hnc1]
      dsimp only [nc]
      exact ⟨by omega, by rw [ho.2.2.2.1]; exact hu.2⟩
    · intro hi
      have hst_in : stMeta.incons = ks.incons := rfl
      have hst_nc : stMeta.nc = nc + 1#32 := rfl
      have hst_an : stMeta.ante = ks.ante := rfl
      have hst_va : stMeta.vals = ks.vals := rfl
      have hst_la : stMeta.lvlArr = ks.lvlArr := rfl
      have hst_rs : stMeta.rsn = ks.rsn := rfl
      rw [hst_in] at hi ⊢
      have hinc := hcl.incons_ok hi
      rw [hst_nc, hnc1]
      refine ⟨Nat.lt_trans hinc.1 (Nat.lt_succ_self _),
        by rw [horig_meta]; exact hinc.2.1, fun l hl => ?_⟩
      rw [(hcl_old _ hinc.1).2.2.2.2.2.2.1] at hl
      have hr := hinc.2.2 l hl
      dsimp only at hr ⊢
      rw [hst_va, hst_la, hst_rs]
      refine ⟨hr.1, hr.2.1, fun hante => ?_⟩
      have hrr := hr.2.2 (by rwa [← hst_an])
      rw [(hcl_old _ hrr.1).2.2.2.2.2.2.1]
      exact ⟨Nat.lt_trans hrr.1 (Nat.lt_succ_self _), hrr.2⟩
    · intro ha
      refine failingOk_append_nonCore (ks := ks) (ks' := stMeta)
        (by change (nc + 1#32).toNat = ks.nc.toNat + 1; dsimp only [nc]; rw [hnc1])
        rfl rfl rfl ?_ (fun c hc => ⟨(hcl_old c hc).2.1, (hcl_old c hc).2.2.2.2.2.2.1⟩)
        (hcl.failing_ok ha)
      change (kittenClauseMeta stMeta nc.toNat &&& kmCore) = 0#32
      rw [hcm_new]; decide
    · exact hcl.assump_ok
    · exact hcl.flags_clean
  have hpres : KittenUnit0Preserved ks stMeta :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl,
      fun c hc => have ho := hcl_old c hc; ⟨ho.1, ho.2.1, ho.2.2.1, ho.2.2.2.2.2.2.1⟩,
      fun j hj => har_old j hj⟩
  exact ⟨hsh_meta, hcl_meta, rfl, hpres, hsz_new, hlits_new⟩

private theorem learnUnit0Ants_length_le {ks : KittenState} {lit src_cid : BitVec 32}
    {from_res : Bool} (hres : ks.res.length = 256) :
    (learnUnit0Ants ks lit src_cid from_res).length ≤ 65536 := by
  unfold learnUnit0Ants
  split
  · simp
  · split
    · rw [List.length_take, hres]; omega
    · rw [List.length_cons]
      have hle := learnUnit0RcsTake_le (ks := ks) (lit := lit) (src_cid := src_cid)
        (n := kittenClauseSize ks src_cid.toNat)
      have hsz : kittenClauseSize ks src_cid.toNat < 2 ^ 16 := by
        unfold kittenClauseSize
        have : (kittenClauseMeta ks src_cid.toNat &&& 0xFFFF#32).toNat ≤ 65535 := by
          rw [BitVec.toNat_and]
          exact Nat.le_trans Nat.and_le_right (by decide)
        omega
      omega

/-- Parametric `Func.wp` proof for `full_kitten_learn_unit0`. -/
theorem full_kitten_learn_unit0_wp (Γ : Env) :
    ∀ args m Q X, fullKittenLearnUnit0Spec args m Q X →
      Func.wp Γ full_kitten_learn_unit0_body args m Q X := by
  rintro ⟨kPtr, lit, src_cid, from_res, ⟨⟩⟩ m Q X
    ⟨acap, ks, R, hsh, hcl, hlit, hsrc, hfls, hres, hent_lit, hm, hQ⟩
  have hnv := hcl.nv_le
  have hal := hcl.alen_le
  have hacap_lt : acap < 2 ^ 28 := hcl.acap_lt
  have hca_eq : ks.acap.toNat = acap := by
    rw [hcl.acap_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmA := kittenMem_to_amem hsh hm; clear hm
  let ants := learnUnit0Ants ks lit src_cid from_res
  have hants_bd : ants.length ≤ 65536 := learnUnit0Ants_length_le hsh.res_len
  c0_hsteps_nogrp
  refine wp_join_state_pure (proj := fun n : BitVec 32 => (n, ()))
    (fun n => n.toNat = 1 + ants.length) ?_ ?_
  · intro J0 need hneed
    have hsum_wrap : ks.alen.toNat + need.toNat < 2 ^ 32 := by
      unfold kMaxV at hnv; omega
    c0_hsplit
    · c0_hsteps!
      obtain ⟨_, hm'⟩ := kittenMemA_to_mem hmA
      exact hQ 0xFFFFFFFF#32 ks m hsh hcl (fun _ => rfl) (fun h => absurd rfl h) hm'
    · c0_hsplit
      · c0_hsteps!
        obtain ⟨_, hm'⟩ := kittenMemA_to_mem hmA
        exact hQ 0xFFFFFFFF#32 ks m hsh hcl (fun _ => rfl) (fun h => absurd rfl h) hm'
      · have hnc_lt : ks.nc.toNat < kMaxCl := by
          have : ¬ (BitVec.toNat 896 ≤ ks.nc.toNat) := ‹_›
          unfold kMaxCl; bv_omega
        have hfit : ks.alen.toNat + 1 + ants.length ≤ ks.acap.toNat := by
          have hhc : ¬ (ks.acap.toNat < (ks.alen.toNat + need.toNat) % 2 ^ 32) := ‹_›
          rw [Nat.mod_eq_of_lt hsum_wrap] at hhc
          omega
        have hal_wrap : ks.alen.toNat < 2 ^ 28 := by omega
        have hal_cap : ks.alen.toNat < acap := by omega
        c0_hsteps_nogrp
        let ar0 := ks.arena.set ks.alen.toNat lit
        let st0 : KittenState := { ks with arena := ar0 }
        refine wp_join_state
          (proj := fun st : BitVec 32 × BitVec 32 × List (BitVec 32) => (st.1, st.2.1, ()))
          (fun st m' =>
            st.2.2.length = acap ∧
            st.1.toNat = ks.alen.toNat + 1 + ants.length ∧
            st.2.1.toNat = ants.length ∧
            (∀ j < ks.alen.toNat, st.2.2[j]? = ks.arena[j]?) ∧
            st.2.2[ks.alen.toNat]? = some lit ∧
            (∀ j < ants.length, st.2.2[ks.alen.toNat + 1 + j]? = some ants[j]!) ∧
            (KittenMemA kPtr acap { ks with arena := st.2.2 } ⋆ R) m')
          ?_ ?_
        · intro J1 ⟨ap, na, ar'⟩ m' ⟨har_len, hap_eq, hna_eq, har_old, har_lit, har_ants, hm'⟩
          dsimp only at hap_eq hna_eq har_old har_lit har_ants hm' ⊢
          obtain ⟨ksA, hksA⟩ : ∃ x : KittenState, x = { ks with arena := ar' } := ⟨_, rfl⟩
          rw [← hksA] at hm'
          have hnc_896 : ks.nc.toNat < 896 := by unfold kMaxCl at hnc_lt; exact hnc_lt
          have hnc_wrap : ks.nc.toNat < 2 ^ 28 := by omega
          have hnc1_wrap : (ks.nc + 1#32).toNat = ks.nc.toNat + 1 := by bv_omega
          have hap_28 : ap.toNat < 2 ^ 28 := by omega
          have hna_28 : na.toNat < 2 ^ 28 := by omega
          have hna_eq_bv : na = BitVec.ofNat 32 ants.length := by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hna_eq]
          have hap_eq_bv : ap = ks.alen + 1#32 + BitVec.ofNat 32 ants.length := by
            apply BitVec.eq_of_toNat_eq
            have h1 : (ks.alen + 1#32 + BitVec.ofNat 32 ants.length).toNat =
                ks.alen.toNat + 1 + ants.length := by
              have hal2 : ks.alen.toNat ≤ acap := hal
              rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
              simp only [Nat.mod_eq_of_lt (by omega : 1 < 2 ^ 32),
                Nat.mod_eq_of_lt (by omega : ants.length < 2 ^ 32),
                Nat.mod_eq_of_lt (by omega : ks.alen.toNat + 1 < 2 ^ 32),
                Nat.mod_eq_of_lt (by omega : ks.alen.toNat + 1 + ants.length < 2 ^ 32)]
            omega
          obtain ⟨hsh_m, hcl_m, hm_nc, hm_pres, hm_sz, hm_lits⟩ :=
            learnUnit0Meta_preserves hsh hcl hlit hsrc hfls hres hent_lit hnc_lt hfit
              har_len har_old har_lit har_ants
          have hnc_ne_ff : ks.nc ≠ 0xFFFFFFFF#32 := by
            intro h
            have h' := congrArg BitVec.toNat h
            change ks.nc.toNat = 2 ^ 32 - 1 at h'
            omega
          c0_hsteps_nogrp
          c0_hstep
          c0_hsplit
          · have hnu_28 : _ := Nat.lt_trans hc (by decide : 256 < 2 ^ 28)
            have hnu_lt : ks.nunits.toNat < 256 := by
              have hc' := hc; revert hc'; try kp_field; intro hc'; rw [hksA] at hc'; exact hc'
            c0_hsteps!
            let ants_bv := BitVec.ofNat 32 ants.length
            let stMeta : KittenState :=
              { ks with
                alen := ks.alen + 1#32 + ants_bv, nc := ks.nc + 1#32, arena := ar',
                clOff := ks.clOff.set ks.nc.toNat ks.alen,
                clMeta := ks.clMeta.set ks.nc.toNat (1#32 ||| kmLrn),
                clAux := ks.clAux.set ks.nc.toNat ants_bv }
            let stU : KittenState :=
              { stMeta with units := stMeta.units.set stMeta.nunits.toNat ks.nc,
                            nunits := stMeta.nunits + 1#32 }
            have ⟨hsh_u, hcl_u⟩ := learnUnit0AddUnit_preserves hsh_m hcl_m
              (by change ks.nc.toNat < stMeta.nc.toNat; rw [hm_nc, hnc1_wrap]; omega)
              hm_sz hnu_lt
            have hm_pres_u : KittenUnit0Preserved ks stU :=
              ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                rfl, rfl, rfl, rfl, rfl, rfl,
                fun c hc => hm_pres.old_clauses c hc, fun j hj => hm_pres.arena_old j hj⟩
            obtain ⟨_, hmFin⟩ := kittenMemA_to_mem hm
            refine hQ ks.nc stU _ hsh_u hcl_u (fun h => absurd h hnc_ne_ff)
              (fun _ => ⟨rfl, hm_nc, hm_pres_u, hm_sz, hm_lits⟩)
              (Eq.mp (congrArg (fun x => (KittenMem kPtr x ⋆ R) _) ?_) hmFin)
            dsimp only [stU, stMeta, ants_bv]
            rw [hap_eq_bv, hna_eq_bv, hksA]
            kstate_ext <;> (first | rfl | kp_field)
          · have hnu_ge : ¬ (ks.nunits.toNat < 256) := by
              revert hc; try kp_field; intro hc; rw [hksA] at hc; exact hc
            c0_hsteps!
            let ants_bv := BitVec.ofNat 32 ants.length
            let stMeta : KittenState :=
              { ks with
                alen := ks.alen + 1#32 + ants_bv, nc := ks.nc + 1#32, arena := ar',
                clOff := ks.clOff.set ks.nc.toNat ks.alen,
                clMeta := ks.clMeta.set ks.nc.toNat (1#32 ||| kmLrn),
                clAux := ks.clAux.set ks.nc.toNat ants_bv }
            obtain ⟨_, hmFin⟩ := kittenMemA_to_mem hm
            refine hQ ks.nc stMeta _ hsh_m hcl_m (fun h => absurd h hnc_ne_ff)
              (fun _ => ⟨rfl, hm_nc, hm_pres, hm_sz, hm_lits⟩)
              (Eq.mp (congrArg (fun x => (KittenMem kPtr x ⋆ R) _) ?_) hmFin)
            dsimp only [stMeta, ants_bv]
            rw [hap_eq_bv, hna_eq_bv, hksA]
            kstate_ext <;> (first | rfl | kp_field)
        · intro J1 hJ1
          c0_hsplit
          · have hante : ks.ante ≠ 0#32 := by bv_omega
            c0_hstep
            refine wp_jnz_bool from_res rfl ?_ ?_
            · intro hfr
              have hnr_le := (hres hante hfr).1
              have hnr_wrap : ks.nres.toNat < 2 ^ 28 := by unfold kMaxL at hnr_le; omega
              have hants_eq : ants = ks.res.take ks.nres.toNat := by
                dsimp only [ants, learnUnit0Ants]; simp [hante, hfr]
              have hants_len : ants.length = ks.nres.toNat := by
                rw [hants_eq, List.length_take, hsh.res_len]
                unfold kMaxL at hnr_le; omega
              c0_hsteps_nogrp
              refine wp_while_state
                (proj := fun st : BitVec 32 × BitVec 32 × BitVec 32 × List (BitVec 32) =>
                  (st.1, st.2.1, st.2.2.1, ()))
                (fun st => ks.nres.toNat - st.2.2.1.toNat)
                (fun st m' =>
                  st.2.2.1.toNat ≤ ks.nres.toNat ∧
                  st.1.toNat = ks.alen.toNat + 1 + st.2.2.1.toNat ∧
                  st.2.1 = st.2.2.1 ∧
                  st.2.2.2.length = acap ∧
                  (∀ j < ks.alen.toNat, st.2.2.2[j]? = ks.arena[j]?) ∧
                  st.2.2.2[ks.alen.toNat]? = some lit ∧
                  (∀ j < st.2.2.1.toNat,
                    st.2.2.2[ks.alen.toNat + 1 + j]? = some ants[j]!) ∧
                  (KittenMemA kPtr acap { ks with arena := st.2.2.2 } ⋆ R) m')
                ?_ ?_
              · intro L0 hL0
                refine hL0 (ks.alen + 1#32, 0#32, 0#32, ar0) m
                  ⟨Nat.zero_le _, by bv_omega, rfl,
                    by simp [ar0, List.length_set, hsh.arena_len],
                    fun j hj => by simp [ar0, List.getElem?_set_ne (by omega : ks.alen.toNat ≠ j)],
                    by simp [ar0, List.getElem?_set_self (by rw [hsh.arena_len]; omega)],
                    fun j hj => by simp at hj, ?_⟩
                simpa [ar0, KittenState.putArr] using hm
              · intro L0 ⟨ap, na, i, ar⟩ m'
                  ⟨hi_le, hap_eq, hna_eq, har_len, har_old, har_lit, har_prev, hm'⟩ ih
                dsimp only at hi_le hap_eq hna_eq har_len har_old har_lit har_prev hm' ⊢
                c0_hsplit
                · have hi_lt : i.toNat < ks.nres.toNat := by bv_omega
                  have hi_256 : i.toNat < 256 := by unfold kMaxL at hnr_le; omega
                  have hi_28 : i.toNat < 2 ^ 28 := by omega
                  have hfit_i : ks.alen.toNat + 1 + i.toNat < ks.acap.toNat := by
                    rw [← hants_len] at hi_lt; omega
                  have hap_lt : ap.toNat < acap := by omega
                  have hap_28 : ap.toNat < 2 ^ 28 := by omega
                  have hi1_wrap : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
                  have hap1_wrap : (ap + 1#32).toNat = ap.toNat + 1 := by bv_omega
                  c0_hsteps!
                  let vres := ks.res[i.toNat]?.getD 0#32
                  refine ih (ap + 1#32, na + 1#32, i + 1#32, ar.set ap.toNat vres) _
                    (by dsimp only; rw [hi1_wrap]; omega)
                    ⟨by dsimp only; rw [hi1_wrap]; omega,
                      by dsimp only; rw [hap1_wrap, hi1_wrap]; omega,
                      by dsimp only; rw [hna_eq], by simp [List.length_set, har_len],
                      fun j hj => by
                        rw [List.getElem?_set_ne (by omega : ap.toNat ≠ j)]; exact har_old j hj,
                      by rw [List.getElem?_set_ne (by omega : ap.toNat ≠ ks.alen.toNat)]
                         exact har_lit,
                      fun j hj => ?_, ?_⟩
                  · rw [hi1_wrap] at hj
                    by_cases hj_i : j = i.toNat
                    · subst hj_i
                      rw [show ks.alen.toNat + 1 + i.toNat = ap.toNat by omega,
                        List.getElem?_set_self (by omega : ap.toNat < ar.length)]
                      have hi_res : i.toNat < ks.res.length := by rw [hsh.res_len]; exact hi_256
                      have hget_a : ants[i.toNat]! = ks.res[i.toNat]'hi_res := by
                        rw [hants_eq, List.getElem!_eq_getElem?_getD,
                          List.getElem?_take_of_lt hi_lt, List.getElem?_eq_getElem hi_res]
                        rfl
                      dsimp only [vres]
                      rw [hget_a, List.getElem?_eq_getElem hi_res, Option.getD_some]
                    · rw [List.getElem?_set_ne (by omega : ap.toNat ≠ ks.alen.toNat + 1 + j)]
                      exact har_prev j (by omega)
                  · simpa [vres, KittenState.putArr] using hm
                · have hi_eq : i.toNat = ks.nres.toNat := by bv_omega
                  rw [hi_eq, ← hants_len] at har_prev hap_eq
                  c0_hsteps!
                  refine hJ1 (ap, na, ar) m' ⟨har_len, hap_eq, ?_, har_old, har_lit, har_prev, hm'⟩
                  dsimp only; rw [hna_eq, hi_eq, hants_len]
            · intro hfr
              have hsrc_lt := hsrc hfr
              have hnc_le := hcl.nc_le
              have hsrc_896 : src_cid.toNat < 896 := by unfold kMaxCl at hnc_le; omega
              have hsrc_28 : src_cid.toNat < 2 ^ 28 := by omega
              have hwf_src := hcl.cl_wf src_cid.toNat hsrc_lt
              have hsoff_ssz_le : kittenClauseOff ks src_cid.toNat +
                  kittenClauseSize ks src_cid.toNat ≤ ks.alen.toNat := by
                have := hwf_src.2.2.1; unfold kittenClauseSpan at this; omega
              have hants_eq : ants = src_cid ::
                  learnUnit0RcsTake ks lit src_cid (kittenClauseSize ks src_cid.toNat) := by
                dsimp only [ants, learnUnit0Ants]; simp [hante, hfr]
              have hap0_wrap : (ks.alen + 1#32).toNat = ks.alen.toNat + 1 := by bv_omega
              have hap0_28 : (ks.alen + 1#32).toNat < 2 ^ 28 := by omega
              have hap0_cap : (ks.alen + 1#32).toNat < acap := by
                have h1a : 1 ≤ ants.length := by rw [hants_eq]; simp
                omega
              c0_hsteps_nogrp
              let ar1 := ar0.set (ks.alen.toNat + 1) src_cid
              let ssz := ks.clMeta[src_cid.toNat]?.getD 0#32 &&& 0xFFFF#32
              let soff := ks.clOff[src_cid.toNat]?.getD 0#32
              have har1_len : ar1.length = acap := by
                simp [ar1, ar0, List.length_set, hsh.arena_len]
              have har1_old : ∀ j < ks.alen.toNat, ar1[j]? = ks.arena[j]? := fun j hj => by
                dsimp only [ar1, ar0]
                rw [List.getElem?_set_ne (by omega : ks.alen.toNat + 1 ≠ j),
                  List.getElem?_set_ne (by omega : ks.alen.toNat ≠ j)]
              have har1_lit : ar1[ks.alen.toNat]? = some lit := by
                dsimp only [ar1, ar0]
                rw [List.getElem?_set_ne (by omega : ks.alen.toNat + 1 ≠ ks.alen.toNat)]
                exact List.getElem?_set_self (by rw [hsh.arena_len]; omega)
              have har1_src : ar1[ks.alen.toNat + 1]? = some src_cid := by
                dsimp only [ar1]
                exact List.getElem?_set_self (by simp [ar0, List.length_set, hsh.arena_len]; omega)
              refine wp_while_state
                (proj := fun st : BitVec 32 × BitVec 32 × BitVec 32 × List (BitVec 32) =>
                  (st.1, st.2.1, st.2.2.1, ()))
                (fun st => ssz.toNat - st.2.2.1.toNat)
                (fun st m' =>
                  let rcs := learnUnit0RcsTake ks lit src_cid st.2.2.1.toNat
                  st.2.2.1.toNat ≤ ssz.toNat ∧
                  st.1.toNat = ks.alen.toNat + 2 + rcs.length ∧
                  st.2.1.toNat = 1 + rcs.length ∧
                  st.1.toNat ≤ ks.alen.toNat + 1 + ants.length ∧
                  st.2.2.2.length = acap ∧
                  (∀ j < ks.alen.toNat, st.2.2.2[j]? = ks.arena[j]?) ∧
                  st.2.2.2[ks.alen.toNat]? = some lit ∧
                  st.2.2.2[ks.alen.toNat + 1]? = some src_cid ∧
                  (∀ j < rcs.length, st.2.2.2[ks.alen.toNat + 2 + j]? = some rcs[j]!) ∧
                  (KittenMemA kPtr acap { ks with arena := st.2.2.2 } ⋆ R) m')
                ?_ ?_
              · intro L0 hL0
                refine hL0 (ks.alen + 1#32 + 1#32, 1#32, 0#32, ar1) m
                  ⟨Nat.zero_le _,
                    by dsimp only
                       rw [show (0#32).toNat = 0 from rfl, learnUnit0RcsTake_zero, List.length_nil]
                       bv_omega,
                    by dsimp only
                       rw [show (0#32).toNat = 0 from rfl, learnUnit0RcsTake_zero]; rfl,
                    by change (ks.alen + 1#32 + 1#32).toNat ≤ ks.alen.toNat + 1 + ants.length
                       have hal28 : ks.alen.toNat < 2 ^ 28 := by omega
                       rw [hants_eq, List.length_cons]
                       bv_omega,
                    har1_len, har1_old, har1_lit, har1_src,
                    fun j hj => by simp [learnUnit0RcsTake_zero] at hj, ?_⟩
                simpa [ar1, ar0, hap0_wrap, KittenState.putArr] using hm
              · intro L0 ⟨ap, na, i, ar⟩ m'
                  ⟨hi_le, hap_eq, hna_eq, hap_fit, har_len, har_old, har_lit, har_src, har_prev,
                    hm'⟩ ih
                dsimp only at hi_le hap_eq hna_eq hap_fit har_len har_old har_lit har_src ⊢
                dsimp only at har_prev hm'
                c0_hsplit
                · have hi_lt : i.toNat < ssz.toNat := by dsimp only [ssz]; exact ‹_›
                  have hi_sz : i.toNat < kittenClauseSize ks src_cid.toNat := hi_lt
                  have hsoff_wrap : soff.toNat + i.toNat < 2 ^ 28 := by
                    change kittenClauseOff ks src_cid.toNat + i.toNat < 2 ^ 28; omega
                  have hsoff_cap : soff.toNat + i.toNat < acap := by
                    change kittenClauseOff ks src_cid.toNat + i.toNat < acap; omega
                  have har_elem_lt : kittenClauseOff ks src_cid.toNat + i.toNat <
                      ks.arena.length := by
                    rw [hsh.arena_len]; change kittenClauseOff ks src_cid.toNat + i.toNat < acap
                    omega
                  have hot_mem : (ks.arena[soff.toNat + i.toNat]'har_elem_lt).toNat ∈
                      kittenClauseLits ks src_cid.toNat := by
                    unfold kittenClauseLits; rw [List.mem_map]
                    refine ⟨ks.arena[kittenClauseOff ks src_cid.toNat + i.toNat]'har_elem_lt, ?_,
                      rfl⟩
                    rw [List.mem_iff_getElem]
                    exact ⟨i.toNat, by
                        simp [List.length_take, List.length_drop]
                        change i.toNat < min (kittenClauseSize ks src_cid.toNat)
                          (ks.arena.length - kittenClauseOff ks src_cid.toNat)
                        rw [hsh.arena_len]; omega,
                      by simp [List.getElem_take, List.getElem_drop]⟩
                  have hot_lt : (ks.arena[soff.toNat + i.toNat]'har_elem_lt).toNat <
                      2 * ks.nv.toNat := hwf_src.2.2.2.1 _ hot_mem
                  have hsoff_eq : soff.toNat = kittenClauseOff ks src_cid.toNat := rfl
                  have har_ot : ar[soff.toNat + i.toNat]? =
                      ks.arena[kittenClauseOff ks src_cid.toNat + i.toNat]? :=
                    har_old _ (by change kittenClauseOff ks src_cid.toNat + i.toNat < _; omega)
                  let ot := ar[soff.toNat + i.toNat]?.getD 0#32
                  have hot_eq_k : ot = ks.arena[kittenClauseOff ks src_cid.toNat + i.toNat]'
                      har_elem_lt := by
                    dsimp only [ot]; rw [har_ot, List.getElem?_eq_getElem har_elem_lt,
                      Option.getD_some]
                  have hnv := hcl.nv_le
                  have hot_lt' : ot.toNat < 2 * ks.nv.toNat := by
                    rw [hot_eq_k]; simpa [hsoff_eq] using hot_lt
                  have hov_128 : (ot >>> (1 : Nat)).toNat < 128 := by
                    have hnv1 := (bv32_lit_div2_bv hot_lt').2
                    unfold kMaxV at hnv; omega
                  have hov_28 : (ot >>> (1 : Nat)).toNat < 2 ^ 28 := by omega
                  have hov_div : (ot >>> (1 : Nat)).toNat = ot.toNat / 2 :=
                    (bv32_lit_div2_bv hot_lt').1
                  have hstep_rcs := learnUnit0RcsTake_succ (lit := lit)
                    (i := i.toNat) hi_lt (by rw [hsh.arena_len]; omega)
                  have hi1_wrap : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
                  c0_hsteps_nogrp
                  c0_hstep
                  try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                  c0_hsplit
                  · have hne : ot ≠ lit := by dsimp only [ot]; assumption
                    c0_hsplit
                    try (refine LeanQbe.T.wp_unroll_group fun _ _ => ?_; c0_hsplit)
                    · let rc := ks.rsn[ot.toNat >>> 1]?.getD 0#32
                      have hrc_ne : rc ≠ 0xFFFFFFFF#32 := by
                        dsimp only [rc, ot]; rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]
                        assumption
                      have hrc_fff : rc = ks.rsn[ot.toNat / 2]?.getD 0xFFFFFFFF#32 := by
                        dsimp only [rc]; rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]
                        rw [List.getElem?_eq_getElem
                          (by rw [hsh.rsn_len, ← hov_div]; exact hov_128)]
                        rfl
                      have hstep' : learnUnit0RcsTake ks lit src_cid (i.toNat + 1) =
                          learnUnit0RcsTake ks lit src_cid i.toNat ++ [rc] := by
                        rw [hstep_rcs, ← hot_eq_k, ← hrc_fff]
                        simp only [hne, hrc_ne, ne_eq, not_false_eq_true, ↓reduceIte]
                      have hsub : (learnUnit0RcsTake ks lit src_cid (i.toNat + 1)).length ≤
                          (learnUnit0RcsTake ks lit src_cid
                            (kittenClauseSize ks src_cid.toNat)).length :=
                        learnUnit0RcsTake_mono (by omega)
                      have hants_l : ants.length = 1 + (learnUnit0RcsTake ks lit src_cid
                          (kittenClauseSize ks src_cid.toNat)).length := by
                        rw [hants_eq, List.length_cons, Nat.add_comm]
                      have hap_lt : ap.toNat < acap := by
                        rw [hstep', List.length_append, List.length_singleton] at hsub
                        omega
                      have hap_28 : ap.toNat < 2 ^ 28 := by omega
                      have hap1_wrap : (ap + 1#32).toNat = ap.toNat + 1 := by bv_omega
                      c0_hsteps!
                      refine ih (ap + 1#32, na + 1#32, i + 1#32, ar.set ap.toNat rc) _
                        (by dsimp only; rw [hi1_wrap]; omega)
                        ⟨by dsimp only; rw [hi1_wrap]; omega,
                          by dsimp only; rw [hap1_wrap, hi1_wrap, hstep', List.length_append,
                               List.length_singleton]; omega,
                          by dsimp only; rw [hi1_wrap, hstep', List.length_append,
                               List.length_singleton]
                             have : na.toNat + 1 < 2 ^ 32 := by omega
                             bv_omega,
                          by dsimp only; rw [hap1_wrap, hap_eq]
                             rw [hstep', List.length_append, List.length_singleton] at hsub
                             omega,
                          by simp [List.length_set, har_len],
                          fun j hj => by
                            rw [List.getElem?_set_ne (by omega : ap.toNat ≠ j)]; exact har_old j hj,
                          by rw [List.getElem?_set_ne (by omega : ap.toNat ≠ ks.alen.toNat)]
                             exact har_lit,
                          by rw [List.getElem?_set_ne (by omega : ap.toNat ≠ ks.alen.toNat + 1)]
                             exact har_src,
                          fun j hj => ?_, ?_⟩
                      · rw [hi1_wrap, hstep'] at hj ⊢
                        rw [List.length_append, List.length_singleton] at hj
                        by_cases hj_end : j = (learnUnit0RcsTake ks lit src_cid i.toNat).length
                        · subst hj_end
                          rw [show ks.alen.toNat + 2 + (learnUnit0RcsTake ks lit src_cid
                              i.toNat).length = ap.toNat by omega,
                            List.getElem?_set_self (by omega : ap.toNat < ar.length)]
                          have hbang : (learnUnit0RcsTake ks lit src_cid i.toNat ++ [rc])[
                              (learnUnit0RcsTake ks lit src_cid i.toNat).length]! = rc := by
                            simp
                          rw [hbang]
                        · rw [List.getElem?_set_ne (by omega : ap.toNat ≠ ks.alen.toNat + 2 + j)]
                          have hlt_j : j < (learnUnit0RcsTake ks lit src_cid i.toNat).length := by
                            omega
                          have hbang : (learnUnit0RcsTake ks lit src_cid i.toNat ++ [rc])[j]! =
                              (learnUnit0RcsTake ks lit src_cid i.toNat)[j]! := by
                            rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
                              List.getElem?_append_left hlt_j]
                          rw [hbang]; exact har_prev j hlt_j
                      · simpa [rc, ot, KittenState.putArr] using hm
                    · have hrc_eq : ks.rsn[ot.toNat / 2]?.getD 0xFFFFFFFF#32 =
                          0xFFFFFFFF#32 := by
                        have hlen : ot.toNat / 2 < ks.rsn.length := by
                          rw [hsh.rsn_len, ← hov_div]; exact hov_128
                        rw [List.getElem?_eq_getElem hlen,
                          ← Option.getD_some (a := ks.rsn[ot.toNat / 2]'hlen) (b := 0#32),
                          ← List.getElem?_eq_getElem hlen]
                        dsimp only [ot, soff]; assumption
                      have hstep' : learnUnit0RcsTake ks lit src_cid (i.toNat + 1) =
                          learnUnit0RcsTake ks lit src_cid i.toNat := by
                        rw [hstep_rcs, ← hot_eq_k]
                        simp [hne, hrc_eq]
                      c0_hsteps!
                      refine ih (ap, na, i + 1#32, ar) _ (by dsimp only; rw [hi1_wrap]; omega)
                        ⟨by dsimp only; rw [hi1_wrap]; omega,
                          by dsimp only; rw [hi1_wrap, hstep']; exact hap_eq,
                          by dsimp only; rw [hi1_wrap, hstep']; exact hna_eq,
                          hap_fit, har_len, har_old, har_lit, har_src,
                          by dsimp only; rw [hi1_wrap, hstep']; exact har_prev, hm'⟩
                  · have heq : ot = lit := by dsimp only [ot]; assumption
                    have hstep' : learnUnit0RcsTake ks lit src_cid (i.toNat + 1) =
                        learnUnit0RcsTake ks lit src_cid i.toNat := by
                      rw [hstep_rcs, ← hot_eq_k]
                      simp [heq]
                    c0_hsteps!
                    refine ih (ap, na, i + 1#32, ar) _ (by dsimp only; rw [hi1_wrap]; omega)
                      ⟨by dsimp only; rw [hi1_wrap]; omega,
                        by dsimp only; rw [hi1_wrap, hstep']; exact hap_eq,
                        by dsimp only; rw [hi1_wrap, hstep']; exact hna_eq,
                        hap_fit, har_len, har_old, har_lit, har_src,
                        by dsimp only; rw [hi1_wrap, hstep']; exact har_prev, hm'⟩
                · have hi_eq : i.toNat = ssz.toNat := by
                    have hhc : ¬ i.toNat < ssz.toNat := by
                      dsimp only [ssz]; revert hc; kp_field; intro hc'; exact hc'
                    omega
                  have hssz_eq : ssz.toNat = kittenClauseSize ks src_cid.toNat := rfl
                  have har_ants' : ∀ j < ants.length,
                      ar[ks.alen.toNat + 1 + j]? = some ants[j]! := by
                    intro j hj
                    rw [hants_eq] at hj ⊢
                    cases j with
                    | zero =>
                      simpa [List.getElem!_eq_getElem?_getD] using har_src
                    | succ k =>
                      rw [List.length_cons] at hj
                      have h1 := har_prev k (by rw [hi_eq, hssz_eq]; omega)
                      rw [show ks.alen.toNat + 1 + (k + 1) = ks.alen.toNat + 2 + k by omega, h1]
                      simp [List.getElem!_eq_getElem?_getD, hi_eq, hssz_eq]
                  c0_hsteps!
                  refine hJ1 (ap, na, ar) m' ⟨har_len, ?_, ?_, har_old, har_lit, har_ants', hm'⟩
                  · rw [hap_eq, hi_eq, hssz_eq, hants_eq, List.length_cons]; omega
                  · rw [hna_eq, hi_eq, hssz_eq, hants_eq, List.length_cons]; omega
          · have hante : ks.ante = 0#32 := by bv_omega
            have hants_eq : ants = [] := by dsimp only [ants, learnUnit0Ants]; simp [hante]
            c0_hsteps!
            exact hJ1 (ks.alen + 1#32, 0#32, ar0) m ⟨by
                simp [ar0, List.length_set, hsh.arena_len],
              by simp [hants_eq]; bv_omega, by simp [hants_eq],
              fun j hj => by simp [ar0, List.getElem?_set_ne (by omega : ks.alen.toNat ≠ j)],
              by simp [ar0, List.getElem?_set_self (by rw [hsh.arena_len]; omega)],
              fun j hj => by simp [hants_eq] at hj, by simpa [ar0, KittenState.putArr] using hm⟩
  · intro J0 hJ0
    c0_hsplit
    · have hante : ks.ante ≠ 0#32 := by bv_omega
      c0_hstep
      refine wp_jnz_bool from_res rfl ?_ ?_
      · intro hfr
        c0_hsplit
        · have hgt : 256 < ks.nres.toNat := by bv_omega
          have hnr := (hres hante hfr).1
          unfold kMaxL at hnr; omega
        · have hnr_le : ks.nres.toNat ≤ 256 := by bv_omega
          have hants_eq : ants = ks.res.take ks.nres.toNat := by
            dsimp only [ants, learnUnit0Ants]; simp [hante, hfr]
          have hants_len : ants.length = ks.nres.toNat := by
            rw [hants_eq, List.length_take, hsh.res_len]; omega
          c0_hsteps!
          exact hJ0 (1#32 + ks.nres) (by rw [hants_len]; bv_omega)
      · intro hfr
        have hsrc_lt := hsrc hfr
        have hnc_le := hcl.nc_le
        have hsrc_896 : src_cid.toNat < 896 := by unfold kMaxCl at hnc_le; omega
        have hsrc_28 : src_cid.toNat < 2 ^ 28 := by omega
        have hwf_src := hcl.cl_wf src_cid.toNat hsrc_lt
        have hsoff_ssz_le : kittenClauseOff ks src_cid.toNat +
            kittenClauseSize ks src_cid.toNat ≤ ks.alen.toNat := by
          have := hwf_src.2.2.1; unfold kittenClauseSpan at this; omega
        have hants_eq : ants = src_cid ::
            learnUnit0RcsTake ks lit src_cid (kittenClauseSize ks src_cid.toNat) := by
          dsimp only [ants, learnUnit0Ants]; simp [hante, hfr]
        let ssz := ks.clMeta[src_cid.toNat]?.getD 0#32 &&& 0xFFFF#32
        let soff := ks.clOff[src_cid.toNat]?.getD 0#32
        c0_hsteps_nogrp
        refine wp_while_state_pure
          (proj := fun st : BitVec 32 × BitVec 32 => (st.1, st.2, ()))
          (fun st => ssz.toNat - st.2.toNat)
          (fun st =>
            let rcs := learnUnit0RcsTake ks lit src_cid st.2.toNat
            st.2.toNat ≤ ssz.toNat ∧ st.1.toNat = 2 + rcs.length)
          ?_ ?_
        · intro L0 hL0
          exact hL0 (2#32, 0#32) ⟨Nat.zero_le _, by simp [learnUnit0RcsTake_zero]⟩
        · intro L0 ⟨need, i⟩ ⟨hi_le, hnd_eq⟩ ih
          dsimp only at hi_le hnd_eq ⊢
          c0_hsplit
          · have hi_lt : i.toNat < ssz.toNat := by dsimp only [ssz]; exact ‹_›
            have hi_sz : i.toNat < kittenClauseSize ks src_cid.toNat := hi_lt
            have hsoff_wrap : soff.toNat + i.toNat < 2 ^ 28 := by
              change kittenClauseOff ks src_cid.toNat + i.toNat < 2 ^ 28; omega
            have hsoff_cap : soff.toNat + i.toNat < acap := by
              change kittenClauseOff ks src_cid.toNat + i.toNat < acap; omega
            have har_elem_lt : kittenClauseOff ks src_cid.toNat + i.toNat <
                ks.arena.length := by
              rw [hsh.arena_len]; change kittenClauseOff ks src_cid.toNat + i.toNat < acap; omega
            have hot_mem : (ks.arena[soff.toNat + i.toNat]'har_elem_lt).toNat ∈
                kittenClauseLits ks src_cid.toNat := by
              unfold kittenClauseLits; rw [List.mem_map]
              refine ⟨ks.arena[kittenClauseOff ks src_cid.toNat + i.toNat]'har_elem_lt, ?_, rfl⟩
              rw [List.mem_iff_getElem]
              exact ⟨i.toNat, by
                  simp [List.length_take, List.length_drop]
                  change i.toNat < min (kittenClauseSize ks src_cid.toNat)
                    (ks.arena.length - kittenClauseOff ks src_cid.toNat)
                  rw [hsh.arena_len]; omega,
                by simp [List.getElem_take, List.getElem_drop]⟩
            have hot_lt : (ks.arena[soff.toNat + i.toNat]'har_elem_lt).toNat < 2 * ks.nv.toNat :=
              hwf_src.2.2.2.1 _ hot_mem
            let ot := ks.arena[soff.toNat + i.toNat]?.getD 0#32
            have hsoff_eq : soff.toNat = kittenClauseOff ks src_cid.toNat := rfl
            have hot_eq_k : ot = ks.arena[kittenClauseOff ks src_cid.toNat + i.toNat]'
                har_elem_lt := by
              dsimp only [ot]; rw [hsoff_eq, List.getElem?_eq_getElem har_elem_lt,
                Option.getD_some]
            have hnv := hcl.nv_le
            have hot_lt' : ot.toNat < 2 * ks.nv.toNat := by
              rw [hot_eq_k]; simpa [hsoff_eq] using hot_lt
            have hov_128 : (ot >>> (1 : Nat)).toNat < 128 := by
              have hnv1 := (bv32_lit_div2_bv hot_lt').2
              unfold kMaxV at hnv; omega
            have hov_28 : (ot >>> (1 : Nat)).toNat < 2 ^ 28 := by omega
            have hov_div : (ot >>> (1 : Nat)).toNat = ot.toNat / 2 :=
              (bv32_lit_div2_bv hot_lt').1
            have hstep_rcs := learnUnit0RcsTake_succ (lit := lit)
              (i := i.toNat) hi_lt (by rw [hsh.arena_len]; omega)
            have hi1_wrap : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
            have hnd_le : need.toNat ≤ 2 + i.toNat := by
              have := learnUnit0RcsTake_le (ks := ks) (lit := lit) (src_cid := src_cid)
                (n := i.toNat)
              omega
            have hnd1_wrap : (need + 1#32).toNat = need.toNat + 1 := by
              have hsz16 : kittenClauseSize ks src_cid.toNat < 2 ^ 16 := by
                unfold kittenClauseSize
                have : (kittenClauseMeta ks src_cid.toNat &&& 0xFFFF#32).toNat ≤ 65535 := by
                  rw [BitVec.toNat_and]
                  exact Nat.le_trans Nat.and_le_right (by decide)
                omega
              bv_omega
            c0_hsteps_nogrp
            c0_hstep
            try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
            c0_hsplit
            · have hne : ot ≠ lit := by dsimp only [ot]; assumption
              c0_hsplit
              try (refine LeanQbe.T.wp_unroll_group fun _ _ => ?_; c0_hsplit)
              · have hrc_ne : ks.rsn[ot.toNat / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
                  have hlen : ot.toNat / 2 < ks.rsn.length := by
                    rw [hsh.rsn_len, ← hov_div]; exact hov_128
                  rw [List.getElem?_eq_getElem hlen,
                    ← Option.getD_some (a := ks.rsn[ot.toNat / 2]'hlen) (b := 0#32),
                    ← List.getElem?_eq_getElem hlen]
                  dsimp only [ot, soff]; assumption
                have hstep' : learnUnit0RcsTake ks lit src_cid (i.toNat + 1) =
                    learnUnit0RcsTake ks lit src_cid i.toNat ++
                      [ks.rsn[ot.toNat / 2]?.getD 0xFFFFFFFF#32] := by
                  rw [hstep_rcs, ← hot_eq_k]
                  simp only [hne, hrc_ne, ne_eq, not_false_eq_true, ↓reduceIte]
                c0_hsteps!
                exact ih (need + 1#32, i + 1#32) (by dsimp only; rw [hi1_wrap]; omega)
                  ⟨by dsimp only; rw [hi1_wrap]; omega,
                   by dsimp only; rw [hnd1_wrap, hi1_wrap, hstep', List.length_append,
                        List.length_singleton]; omega⟩
              · have hrc_eq : ks.rsn[ot.toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 := by
                  have hlen : ot.toNat / 2 < ks.rsn.length := by
                    rw [hsh.rsn_len, ← hov_div]; exact hov_128
                  rw [List.getElem?_eq_getElem hlen,
                    ← Option.getD_some (a := ks.rsn[ot.toNat / 2]'hlen) (b := 0#32),
                    ← List.getElem?_eq_getElem hlen]
                  dsimp only [ot, soff]; assumption
                have hstep' : learnUnit0RcsTake ks lit src_cid (i.toNat + 1) =
                    learnUnit0RcsTake ks lit src_cid i.toNat := by
                  rw [hstep_rcs, ← hot_eq_k]
                  simp [hne, hrc_eq]
                c0_hsteps!
                exact ih (need, i + 1#32) (by dsimp only; rw [hi1_wrap]; omega)
                  ⟨by dsimp only; rw [hi1_wrap]; omega,
                   by dsimp only; rw [hi1_wrap, hstep']; exact hnd_eq⟩
            · have heq : ot = lit := by dsimp only [ot]; assumption
              have hstep' : learnUnit0RcsTake ks lit src_cid (i.toNat + 1) =
                  learnUnit0RcsTake ks lit src_cid i.toNat := by
                rw [hstep_rcs, ← hot_eq_k]
                simp [heq]
              c0_hsteps!
              exact ih (need, i + 1#32) (by dsimp only; rw [hi1_wrap]; omega)
                ⟨by dsimp only; rw [hi1_wrap]; omega,
                 by dsimp only; rw [hi1_wrap, hstep']; exact hnd_eq⟩
          · have hi_eq : i.toNat = ssz.toNat := by
              have hhc : ¬ i.toNat < ssz.toNat := by
                dsimp only [ssz]; assumption
              omega
            have hssz_eq : ssz.toNat = kittenClauseSize ks src_cid.toNat := rfl
            rw [hi_eq, hssz_eq] at hnd_eq
            have hants_l : ants.length = 1 + (learnUnit0RcsTake ks lit src_cid
                (kittenClauseSize ks src_cid.toNat)).length := by
              rw [hants_eq, List.length_cons, Nat.add_comm]
            c0_hsteps!
            exact hJ0 need (by rw [hnd_eq]; omega)
    · have hante : ks.ante = 0#32 := by bv_omega
      have hants_eq : ants = [] := by dsimp only [ants, learnUnit0Ants]; simp [hante]
      c0_hsteps!
      exact hJ0 1#32 (by simp [hants_eq])


end LeanQbe.T.Examples.Kissat.Full
