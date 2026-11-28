/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Kitten.LemmasBtAdd

/-!
# Leaf `Func.wp` Proofs for `Src.Kitten` (`5/14` fns, `Kissat.Proof.Kitten.WpLeaf`)

Certifies:
- `full_m6_max_v_wp` (`m6MaxVSpec`)
- `full_k6_add_ticks_wp` (`k6AddTicksSpec`)
- `full_k6_watch_wp` (`k6WatchSpec`)
- `full_k6_assign_wp` (`k6AssignSpec`)
- `full_k6_mtf_wp` (`k6MtfSpec`)

Zero legacy `Full*` imports; zero `@[expose]` on theorems/lemmas.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Kitten

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Kitten.Spec
open LeanQbe.T.Examples.Kissat.Src.Kitten

open K6MemATactics K6PtrTactics
open scoped K6MemATactics K6PtrTactics

/-- `1/14`: Parametric `Func.wp` proof for `full_m6_max_v`. -/
theorem full_m6_max_v_wp (Γ : Env) :
    ∀ args m Q X, m6MaxVSpec args m Q X → Func.wp Γ full_m6_max_v_body args m Q X := by
  rintro ⟨cap, ⟨⟩⟩ m Q X hQ
  have hbv := k6MaxV_bv64_eq cap.isLt
  have hcap : BitVec.ofNat 64 cap.toNat = cap := BitVec.eq_of_toNat_eq (by simp)
  dsimp only at hbv; rw [hcap] at hbv
  rw [show (0#64 : BitVec 64) = 0 from rfl, show (512#64 : BitVec 64) = 512 from rfl,
    show (1312#64 : BitVec 64) = 1312 from rfl, show (45#64 : BitVec 64) = 45 from rfl,
    show (8192#64 : BitVec 64) = 8192 from rfl, show (24576#64 : BitVec 64) = 24576 from rfl,
    show (524288#64 : BitVec 64) = 524288 from rfl,
    show (0xFFFFFFFFFFFFFFC0#64 : BitVec 64) = 18446744073709551552 from rfl] at hbv
  dsimp only [m6MaxVSpec] at hQ; rw [← hbv] at hQ
  c0_hsteps! <;>
    exact Eq.mp (congrArg (fun v => Q (v, ()) m) (by
      repeat (first | rfl | bv_omega | split))) hQ

/-- `2/14`: Parametric `Func.wp` proof for `full_k6_add_ticks`. -/
theorem full_k6_add_ticks_wp (Γ : Env) :
    ∀ args m Q X, k6AddTicksSpec args m Q X → Func.wp Γ full_k6_add_ticks_body args m Q X := by
  rintro ⟨kPtr, delta, ⟨⟩⟩ m Q X ⟨L, ks, R, hsh, hm, hQ⟩
  have hmA := k6Mem_to_amem hsh hm; clear hm
  c0_hsteps! <;> (obtain ⟨_, hm'⟩ := k6MemA_to_mem hm; exact hQ _ _ hm')

/-- `4/14`: Parametric `Func.wp` proof for `full_k6_watch`. -/
theorem full_k6_watch_wp (Γ : Env) :
    ∀ args m Q X, k6WatchSpec args m Q X → Func.wp Γ full_k6_watch_body args m Q X := by
  rintro ⟨kPtr, cid, l0, l1, ⟨⟩⟩ m Q X ⟨L, ks, R, hsh, hmv, hcid, hl0, hl1, hm, hQ⟩
  have hmc : L.maxCl ≤ 32768 := by have := L.hmaxV; unfold K6Layout.maxCl; omega
  have h0 := k6_bv32_cid_w0 hcid hmc
  have h1 := k6_bv32_cid_w1 hcid hmc
  have hw0_len : (cid <<< (1 : Nat)).toNat < sz2Cl L := by
    unfold sz2Cl K6Layout.maxCl at *; omega
  have hw1_len : ((cid <<< (1 : Nat)) ||| 1#32).toNat < sz2Cl L := by
    unfold sz2Cl K6Layout.maxCl at *; omega
  have hcid_len : cid.toNat < szCl L := by unfold szCl; exact hcid
  have hl0_len : l0.toNat < sz2V L := by unfold sz2V; exact hl0
  have hl1_len : l1.toNat < sz2V L := by unfold sz2V; exact hl1
  have hmA := k6Mem_to_amem hsh hm; clear hm
  c0_hsteps_nogrp
  rw [hmv]
  c0_hsteps!
  · obtain ⟨_, hm'⟩ := k6MemA_to_mem hm
    refine hQ _ (Eq.mp (congrArg (fun x => (K6Mem L kPtr x ⋆ R) _) ?_) hm')
    have hsz2 : (ks.clSz[cid.toNat]?.getD 0#32).toNat = 2 := by bv_omega
    dsimp only [k6WatchStep, k6WatchStep0]; simp only [hsz2, ite_true]; k6_ext
  · obtain ⟨_, hm'⟩ := k6MemA_to_mem hm
    refine hQ _ (Eq.mp (congrArg (fun x => (K6Mem L kPtr x ⋆ R) _) ?_) hm')
    dsimp only [k6WatchStep, k6WatchStep0]
    have hne : (ks.clSz[cid.toNat]?.getD 0#32).toNat ≠ 2 := by bv_omega
    simp only [hne, ite_false]; k6_ext

/-- `5/14`: Parametric `Func.wp` proof for `full_k6_assign`. -/
theorem full_k6_assign_wp (Γ : Env) :
    ∀ args m Q X, k6AssignSpec args m Q X → Func.wp Γ full_k6_assign_body args m Q X := by
  rintro ⟨kPtr, lit, rsn, ⟨⟩⟩ m Q X ⟨L, ks, R, hsh, hmv, hlit, hte, hm, hQ⟩
  obtain ⟨hv_eq, hv_lt⟩ := k6_bv32_div2_lt hlit
  obtain ⟨hn_eq, hn_lt⟩ := k6_bv32_xor1_lt hlit
  have hl_len : lit.toNat < sz2V L := by unfold sz2V; exact hlit
  have hnl_len : (lit ^^^ 1#32).toNat < sz2V L := by unfold sz2V; exact hn_lt
  have hv_len : (lit >>> (1 : Nat)).toNat < szV L := by unfold szV; exact hv_lt
  have hte_len : ks.trl_end.toNat < szV L := by unfold szV; exact hte
  have hmA := k6Mem_to_amem hsh hm; clear hm
  c0_hsteps_nogrp
  rw [hmv]
  c0_hsteps_nogrp
  let ksPre := ((((((ks.putArr .vals lit.toNat 1#32).putArr .vals (lit ^^^ 1#32).toNat 2#32).putArr
    .lvlArr (lit >>> (1 : Nat)).toNat ks.lvl).putArr .rsn (lit >>> (1 : Nat)).toNat rsn).putArr
    .trl ks.trl_end.toNat lit).putHdr .trl_end (ks.trl_end + 1#32))
  let ksU := if (0 : BitVec 32).ult ks.unass then ksPre.putHdr .unass (ks.unass - 1#32) else ksPre
  have hult_iff : (0 : BitVec 32).ult ks.unass = true ↔ 0 < ks.unass.toNat := decide_eq_true_iff
  refine wp_join0 (fun m' => (K6MemA L kPtr ksU ⋆ R) m') ?_ ?_
  · intro J m' hm'
    c0_hsteps!
    · obtain ⟨_, hm''⟩ := k6MemA_to_mem hm
      refine hQ _ (Eq.mp (congrArg (fun x => (K6Mem L kPtr x ⋆ R) _) ?_) hm'')
      have hcond : (lit &&& 1#32) ≠ 0#32 := by
        simpa [K6PtrTactics.k6_bv32_one] using ‹_›
      by_cases hu : (0 : BitVec 32).ult ks.unass = true
      · have hu_nat := hult_iff.mp hu
        dsimp only [ksU, ksPre, k6AssignStep]
        simp only [hu, ite_true, hu_nat, hcond, ne_eq, not_false_eq_true]
        k6_ext <;> simp [hv_eq]
      · have hu_nat : ¬ 0 < ks.unass.toNat := fun hp => hu (hult_iff.mpr hp)
        dsimp only [ksU, ksPre, k6AssignStep]
        simp only [hu, ite_false, hu_nat, hcond, ne_eq, not_false_eq_true, ite_true]
        k6_ext <;> simp [hv_eq]
    · obtain ⟨_, hm''⟩ := k6MemA_to_mem hm
      refine hQ _ (Eq.mp (congrArg (fun x => (K6Mem L kPtr x ⋆ R) _) ?_) hm'')
      have hcond : (lit &&& 1#32) = 0#32 := by
        simpa [K6PtrTactics.k6_bv32_one] using ‹_›
      by_cases hu : (0 : BitVec 32).ult ks.unass = true
      · have hu_nat := hult_iff.mp hu
        dsimp only [ksU, ksPre, k6AssignStep]
        simp only [hu, ite_true, hu_nat, hcond, ne_eq, not_true_eq_false, ite_false]
        k6_ext <;> simp [hv_eq]
      · have hu_nat : ¬ 0 < ks.unass.toNat := fun hp => hu (hult_iff.mpr hp)
        dsimp only [ksU, ksPre, k6AssignStep]
        simp only [hu, ite_false, hu_nat, hcond, ne_eq, not_true_eq_false]
        k6_ext <;> simp [hv_eq]
  · intro J hJ
    c0_hsteps!
    · have hu : (0 : BitVec 32).ult ks.unass = true := by
        apply hult_iff.mpr; revert hc; k6_field; intro hc; bv_omega
      refine hJ _ (Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ R) _) ?_) hm)
      dsimp only [ksU, ksPre]; simp only [hu, ite_true]
      k6_ext <;> (first | rfl | (simp only [hv_eq, K6PtrTactics.k6_bv32_one]; rfl))
    · have hu : (0 : BitVec 32).ult ks.unass = false :=
        Bool.eq_false_iff.mpr fun h => by
          have := hult_iff.mp h; revert hc; k6_field; intro hc; bv_omega
      refine hJ _ (Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ R) _) ?_) hm)
      dsimp only [ksU, ksPre]; simp only [hu, Bool.false_eq_true, ite_false]
      k6_ext <;> (first | rfl | (simp only [hv_eq, K6PtrTactics.k6_bv32_one]; rfl))

private def K6MtfSt (L : K6Layout) (ks ks' : K6State) : Prop :=
  ks'.ShapesOk L ∧ ∃ qf ql qs qst qp qn qsa,
    ks' = { ks with qfirst := qf, qlast := ql, qsearch := qs, qstamp := qst,
                    qprev := qp, qnext := qn, qstampArr := qsa }

private theorem K6MtfSt.base {L : K6Layout} {ks : K6State} (hsh : ks.ShapesOk L) :
    K6MtfSt L ks ks :=
  ⟨hsh, ks.qfirst, ks.qlast, ks.qsearch, ks.qstamp, ks.qprev, ks.qnext, ks.qstampArr,
    by cases ks; rfl⟩

private theorem K6MtfSt.nv_eq {L : K6Layout} {ks ks' : K6State} (r : K6MtfSt L ks ks') :
    ks'.nv = ks.nv := by rcases r.2 with ⟨_, _, _, _, _, _, _, rfl⟩; rfl

private theorem K6MtfSt.mv_eq {L : K6Layout} {ks ks' : K6State} (r : K6MtfSt L ks ks') :
    ks'.max_v = ks.max_v := by rcases r.2 with ⟨_, _, _, _, _, _, _, rfl⟩; rfl

private theorem K6MtfSt.putQf {L : K6Layout} {ks ks' : K6State} (r : K6MtfSt L ks ks')
    (v : BitVec 32) : K6MtfSt L ks (ks'.putHdr .qfirst v) := by
  rcases r with ⟨hsh, qf, ql, qs, qst, qp, qn, qsa, rfl⟩
  exact ⟨hsh.putHdr .qfirst v, v, ql, qs, qst, qp, qn, qsa, rfl⟩

private theorem K6MtfSt.putQl {L : K6Layout} {ks ks' : K6State} (r : K6MtfSt L ks ks')
    (v : BitVec 32) : K6MtfSt L ks (ks'.putHdr .qlast v) := by
  rcases r with ⟨hsh, qf, ql, qs, qst, qp, qn, qsa, rfl⟩
  exact ⟨hsh.putHdr .qlast v, qf, v, qs, qst, qp, qn, qsa, rfl⟩

private theorem K6MtfSt.putQs {L : K6Layout} {ks ks' : K6State} (r : K6MtfSt L ks ks')
    (v : BitVec 32) : K6MtfSt L ks (ks'.putHdr .qsearch v) := by
  rcases r with ⟨hsh, qf, ql, qs, qst, qp, qn, qsa, rfl⟩
  exact ⟨hsh.putHdr .qsearch v, qf, ql, v, qst, qp, qn, qsa, rfl⟩

private theorem K6MtfSt.putQst {L : K6Layout} {ks ks' : K6State} (r : K6MtfSt L ks ks')
    (v : BitVec 32) : K6MtfSt L ks (ks'.putHdr .qstamp v) := by
  rcases r with ⟨hsh, qf, ql, qs, qst, qp, qn, qsa, rfl⟩
  exact ⟨hsh.putHdr .qstamp v, qf, ql, qs, v, qp, qn, qsa, rfl⟩

private theorem K6MtfSt.putQp {L : K6Layout} {ks ks' : K6State} (r : K6MtfSt L ks ks')
    (i : Nat) (v : BitVec 32) : K6MtfSt L ks (ks'.putArr .qprev i v) := by
  rcases r with ⟨hsh, qf, ql, qs, qst, qp, qn, qsa, rfl⟩
  exact ⟨hsh.putArr .qprev i v, qf, ql, qs, qst, qp.set i v, qn, qsa, rfl⟩

private theorem K6MtfSt.putQn {L : K6Layout} {ks ks' : K6State} (r : K6MtfSt L ks ks')
    (i : Nat) (v : BitVec 32) : K6MtfSt L ks (ks'.putArr .qnext i v) := by
  rcases r with ⟨hsh, qf, ql, qs, qst, qp, qn, qsa, rfl⟩
  exact ⟨hsh.putArr .qnext i v, qf, ql, qs, qst, qp, qn.set i v, qsa, rfl⟩

private theorem K6MtfSt.putQsa {L : K6Layout} {ks ks' : K6State} (r : K6MtfSt L ks ks')
    (i : Nat) (v : BitVec 32) : K6MtfSt L ks (ks'.putArr .qstampArr i v) := by
  rcases r with ⟨hsh, qf, ql, qs, qst, qp, qn, qsa, rfl⟩
  exact ⟨hsh.putArr .qstampArr i v, qf, ql, qs, qst, qp, qn, qsa.set i v, rfl⟩

private theorem K6MtfSt.finishA {L : K6Layout} {ks ks' : K6State} {kPtr : BitVec 64}
    {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post []}
    (hQ : ∀ qf' ql' qs' qst' qp' qn' qsa' m',
      let ks' : K6State := { ks with qfirst := qf', qlast := ql', qsearch := qs', qstamp := qst',
                                     qprev := qp', qnext := qn', qstampArr := qsa' }
      ks'.ShapesOk L → (K6Mem L kPtr ks' ⋆ R) m' → Q () m')
    (r : K6MtfSt L ks ks') (hm' : (K6MemA L kPtr ks' ⋆ R) m') : Q () m' := by
  obtain ⟨hsh, hm''⟩ := k6MemA_to_mem hm'
  rcases r with ⟨_, qf, ql, qs, qst, qp, qn, qsa, rfl⟩
  exact hQ qf ql qs qst qp qn qsa m' hsh hm''

/-- `7/14`: Parametric `Func.wp` proof for `full_k6_mtf`. -/
theorem full_k6_mtf_wp (Γ : Env) :
    ∀ args m Q X, k6MtfSpec args m Q X → Func.wp Γ full_k6_mtf_body args m Q X := by
  rintro ⟨kPtr, v, ⟨⟩⟩ m Q X ⟨L, ks, R, hsh, hmv, hnv, hm, hQ⟩
  have hmA := k6Mem_to_amem hsh hm; clear hm
  c0_hsteps_nogrp
  · exact hQ _ _ _ _ _ _ _ m hsh (k6MemA_to_mem hmA).2
  · exact hQ _ _ _ _ _ _ _ m hsh (k6MemA_to_mem hmA).2
  · have hv_lt : v.toNat < ks.nv.toNat := by bv_omega
    have hv_len : v.toNat < szV L := by unfold szV; omega
    have hv2_len : (v <<< (1 : Nat)).toNat < sz2V L := by
      have := K6PtrTactics.k6_shl1_toNat v; unfold sz2V; omega
    rw [hmv]
    c0_hsteps_nogrp
    let pv := ks.qprev[v.toNat]?.getD 0#32
    let nxt := ks.qnext[v.toNat]?.getD 0#32
    refine wp_join_state0 (α := K6State)
      (fun st m' => K6MtfSt L ks st ∧ (K6MemA L kPtr st ⋆ R) m') ?_ ?_
    · intro J1 ks1 m1 ⟨hr1, hm1⟩
      have hnv1 := hr1.nv_eq; have hmv1 := hr1.mv_eq
      c0_hsteps_nogrp
      refine wp_join_state0 (α := K6State)
        (fun st m' => K6MtfSt L ks st ∧ (K6MemA L kPtr st ⋆ R) m') ?_ ?_
      · intro J2 ks2 m2 ⟨hr2, hm2⟩
        have hnv2 := hr2.nv_eq; have hmv2 := hr2.mv_eq
        c0_hsteps_nogrp
        refine wp_join_state0 (α := K6State)
          (fun st m' => K6MtfSt L ks st ∧ (K6MemA L kPtr st ⋆ R) m') ?_ ?_
        · intro J3 ks3 m3 ⟨hr3, hm3⟩
          have hnv3 := hr3.nv_eq; have hmv3 := hr3.mv_eq
          c0_hsteps_nogrp
          let ol := ks3.qlast
          refine wp_join_state0 (α := K6State)
            (fun st m' => K6MtfSt L ks st ∧ (K6MemA L kPtr st ⋆ R) m') ?_ ?_
          · intro J4 ks4 m4 ⟨hr4, hm4⟩
            c0_hsteps_nogrp
            refine wp_join_state0 (α := K6State)
              (fun st m' => K6MtfSt L ks st ∧ (K6MemA L kPtr st ⋆ R) m') ?_ ?_
            · intro J5 ks5 m5 ⟨hr5, hm5⟩
              c0_hsteps!
              · exact (hr5.putQs v).finishA hQ hm
              · exact hr5.finishA hQ hm5
            · intro J5 hJ5
              c0_hsteps!
              · exact hJ5 _ _ ⟨(hr4.putQst _).putQsa _ _, hm⟩
              · exact hJ5 _ _ ⟨hr4, hm4⟩
          · intro J4 hJ4
            c0_hsteps_nogrp
            · c0_hsteps!
              exact hJ4 _ _ ⟨(((hr3.putQp v.toNat ol).putQn v.toNat 0xFFFFFFFF#32).putQl v).putQf
                v, hm⟩
            · have hol_len : ol.toNat < szV L := by
                have : ol.toNat < ks.nv.toNat := by dsimp only [ol]; rw [← hnv3]; bv_omega
                unfold szV; omega
              c0_hsteps!
              exact hJ4 _ _ ⟨(((hr3.putQp v.toNat ol).putQn v.toNat 0xFFFFFFFF#32).putQl v).putQn
                ol.toNat v, hm⟩
        · intro J3 hJ3
          c0_hsteps_nogrp
          · c0_hsteps!; exact hJ3 _ _ ⟨hr2.putQl pv, hm⟩
          · have hn_len : nxt.toNat < szV L := by
              have : nxt.toNat < ks.nv.toNat := by dsimp only [nxt]; rw [← hnv2]; bv_omega
              unfold szV; omega
            c0_hsteps!
            exact hJ3 _ _ ⟨hr2.putQp nxt.toNat pv, hm⟩
      · intro J2 hJ2
        c0_hsteps_nogrp
        · c0_hsteps!; exact hJ2 _ _ ⟨hr1.putQf nxt, hm⟩
        · have hp_len : pv.toNat < szV L := by
            have : pv.toNat < ks.nv.toNat := by dsimp only [pv]; rw [← hnv1]; bv_omega
            unfold szV; omega
          c0_hsteps!
          exact hJ2 _ _ ⟨hr1.putQn pv.toNat nxt, hm⟩
    · intro J1 hJ1
      c0_hsteps!
      · exact hJ1 _ _ ⟨(K6MtfSt.base hsh).putQs pv, hm⟩
      · exact hJ1 _ _ ⟨(K6MtfSt.base hsh).putQs nxt, hm⟩
      · exact hJ1 _ _ ⟨K6MtfSt.base hsh, hmA⟩
      · exact hJ1 _ _ ⟨K6MtfSt.base hsh, hmA⟩
      · exact hJ1 _ _ ⟨K6MtfSt.base hsh, hmA⟩

end LeanQbe.T.Examples.Kissat.Proof.Kitten

end
