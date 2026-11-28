/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Kitten.LemmasBtAdd

/-!
# Step-13 `Func.wp` Proof for `full_k6_ana_clause` (`10/14`, `Kissat.Proof.Kitten.WpAnaClause`)

Certifies `full_k6_ana_clause_wp` (`step13K6AnaClauseSpec`) against
`Src.Kitten.full_k6_ana_clause_body` with `K6TailEq` preservation, plus shared `K6AnaInv` helpers
for `WpAnalyze0`/`WpAnalyze`. Zero legacy `Full*` imports; zero `@[expose]` on theorems/lemmas;
`<= 100` cols; every decl `<= 450` LOC.
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

/-! ## 1. Pure `K6AnaLit` / `K6AnaPrefix` Helpers -/

theorem k6a_ite_t {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

theorem k6a_ite_f {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬c) :
    (if c then a else b) = b := by simp [h]

theorem k6a_fl_or2_and2_nz (x : BitVec 32) : ((x ||| 2#32) &&& 2#32) ≠ 0#32 := by
  intro h; exact absurd (congrArg (·.getLsbD 1) h) (by simp)

theorem k6a_fl_andnot2_and2_zero (x : BitVec 32) :
    ((x &&& ~~~2#32) &&& 2#32) = 0#32 := by
  c0_bv_bit_grind

theorem k6a_xor1_div2 (l : Nat) : (l ^^^ 1) / 2 = l / 2 := by
  rcases k6_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;> omega

theorem k6a_setQueue_preserves_inv {L : K6Layout} {P : (Nat → Bool) → Prop}
    {ks : K6State} (hinv : K6Inv L P ks) {qf ql qs qst : BitVec 32}
    {qp qn qsa : List (BitVec 32)}
    (hqp : qp.length = L.maxV) (hqn : qn.length = L.maxV) (hqsa : qsa.length = L.maxV) :
    let ks' : K6State :=
      { ks with qfirst := qf, qlast := ql, qsearch := qs, qstamp := qst,
                qprev := qp, qnext := qn, qstampArr := qsa }
    K6Inv L P ks' :=
  ⟨{ hinv.shapes with qprev_len := hqp, qnext_len := hqn, qstampArr_len := hqsa },
   k6ClausesOk_cast hinv.clauses, hinv.watches, k6BaseAssignOk_cast hinv.assign, hinv.reasons⟩

theorem k6a_filter_length_flip_one {α : Type} [DecidableEq α]
    {l : List α} (hnd : l.Nodup) {a : α} (ha : a ∈ l) {P Q : α → Bool}
    (hP : P a = false) (hQ : Q a = true) (hother : ∀ x ∈ l, x ≠ a → Q x = P x) :
    (l.filter Q).length = (l.filter P).length + 1 := by
  induction l with
  | nil => cases ha
  | cons x tl ih =>
    rcases List.nodup_cons.mp hnd with ⟨hx_not, hnd_tl⟩
    rcases List.mem_cons.mp ha with rfl | ha_tl
    · have heq : tl.filter Q = tl.filter P := List.filter_congr fun y hy =>
        hother y (List.mem_cons_of_mem _ hy) (fun heq => hx_not (heq ▸ hy))
      simp only [List.filter_cons, hP, hQ, heq, Bool.false_eq_true, ↓reduceIte, List.length_cons]
    · have hqx : Q x = P x := hother x List.mem_cons_self (fun heq => hx_not (heq ▸ ha_tl))
      have hrec := ih hnd_tl ha_tl (fun y hy => hother y (List.mem_cons_of_mem _ hy))
      simp only [List.filter_cons, hqx]; cases P x <;> simp [hrec]

theorem k6a_filterMap_congr {α β : Type} {f g : α → Option β} {xs : List α}
    (h : ∀ x ∈ xs, f x = g x) : xs.filterMap f = xs.filterMap g := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    simp only [List.filterMap_cons, h x List.mem_cons_self]
    rw [ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem k6a_mem_resolvent_iff {ks : K6State} {idx l : Nat} :
    l ∈ k6ResolventLits ks idx ↔
      (∃ j < idx, (ks.trl[j]?.getD 0#32).toNat = l ^^^ 1 ∧
        ks.lvlArr[(l ^^^ 1) / 2]?.getD 0#32 = ks.lvl ∧
        (ks.flags[(l ^^^ 1) / 2]?.getD 0#32 &&& 2#32) ≠ 0#32) ∨
      (∃ i, 1 ≤ i ∧ i < min ks.nkl.toNat ks.kl.length ∧ (ks.kl[i]?.getD 0#32).toNat = l) := by
  unfold k6ResolventLits; rw [List.mem_append, List.mem_filterMap, List.mem_map]
  constructor
  · rintro (⟨j, hj, hif⟩ | ⟨b, hb, rfl⟩)
    · left; rw [List.mem_range] at hj; dsimp only at hif; split at hif
      · rename_i hc; simp only [Option.some.injEq] at hif
        have hx : (ks.trl[j]?.getD 0#32).toNat = l ^^^ 1 := by rw [← hif, k6_nat_xor1_xor1]
        exact ⟨j, hj, hx, hx ▸ hc.1, hx ▸ hc.2⟩
      · cases hif
    · right; rw [List.mem_iff_getElem] at hb; obtain ⟨k, hk, rfl⟩ := hb
      have hk' : k + 1 < min ks.nkl.toNat ks.kl.length := by
        simp [List.length_take] at hk; omega
      refine ⟨k + 1, by omega, hk', ?_⟩
      simp [List.getElem_take, List.getElem?_eq_getElem (by omega : k + 1 < ks.kl.length)]
  · rintro (⟨j, hj, htrl, hlvl, hfl⟩ | ⟨i, hi1, hi2, rfl⟩)
    · left; refine ⟨j, List.mem_range.mpr hj, ?_⟩
      simp only [htrl, hlvl, hfl, ne_eq, not_false_eq_true, and_self, ↓reduceIte,
        k6_nat_xor1_xor1]
    · right; have hi_lt : i < ks.kl.length := by omega
      refine ⟨ks.kl[i]'hi_lt, ?_, by simp [List.getElem?_eq_getElem hi_lt]⟩
      rw [List.mem_iff_getElem]; refine ⟨i - 1, by simp [List.length_take]; omega, ?_⟩
      simp only [List.getElem_drop, List.getElem_take, show 1 + (i - 1) = i by omega]

theorem k6AnaPreserved_refl (ks : K6State) : K6AnaPreserved ks ks :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem k6AnaPreserved_frame (ks : K6State) {fl an na op kl nk} :
    K6AnaPreserved ks
      { ks with flags := fl, ana := an, nana := na, openCnt := op, kl := kl, nkl := nk } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem k6AnaPreserved_trans {ks1 ks2 ks3 : K6State}
    (h12 : K6AnaPreserved ks1 ks2) (h23 : K6AnaPreserved ks2 ks3) : K6AnaPreserved ks1 ks3 :=
  ⟨h23.nv.trans h12.nv, h23.nc.trans h12.nc, h23.lvl.trans h12.lvl, h23.prop.trans h12.prop,
   h23.trl_end.trans h12.trl_end, h23.unass.trans h12.unass, h23.incons.trans h12.incons,
   h23.alen.trans h12.alen, h23.acap.trans h12.acap, h23.nassump.trans h12.nassump,
   h23.status.trans h12.status, h23.max_v.trans h12.max_v, h23.max_orig.trans h12.max_orig,
   h23.max_cl.trans h12.max_cl, h23.neq.trans h12.neq, h23.lvlArr.trans h12.lvlArr,
   h23.rsn.trans h12.rsn, h23.trl.trans h12.trl, h23.vals.trans h12.vals,
   h23.assump.trans h12.assump, h23.whead.trans h12.whead, h23.wnext.trans h12.wnext,
   h23.wblit.trans h12.wblit, h23.clOff.trans h12.clOff, h23.clSz.trans h12.clSz,
   h23.arena.trans h12.arena⟩

theorem k6a_inv_of_ana_clean {L : K6Layout} {P : (Nat → Bool) → Prop} {ks st : K6State}
    (hinv : K6Inv L P ks) (hsync : K6TrailSynced ks) (hsh : st.ShapesOk L)
    (hp : K6AnaPreserved ks st) (hnkl : st.nkl.toNat ≤ L.maxV) (hnana : st.nana.toNat ≤ L.maxV)
    (hfl : ∀ v < st.nv.toNat, (st.flags[v]?.getD 0#32 &&& 2#32) = 0#32) :
    K6Inv L P st ∧ K6TrailSynced st := by
  have hcl := k6ClausesOk_cast hinv.clauses hp.acap hp.max_v hp.max_orig hp.max_cl hp.nv hp.nc
    hp.alen hp.nassump (Or.inl hp.incons) hp.assump hp.clOff hp.clSz hp.arena (Or.inr hnkl)
    (Or.inr hnana) (Or.inr hfl)
  have hba := k6BaseAssignOk_cast hinv.assign hp.nv hp.trl_end hp.prop hp.unass hp.vals hp.trl
    hp.lvl hp.lvlArr hp.rsn
  have hw : K6WatchesOk st := by
    obtain ⟨ch, h1, h2, h3, h4⟩ := hinv.watches
    refine ⟨ch, by rw [hp.nv]; exact h1, h2,
      fun l hl => by rw [hp.wnext, hp.whead]; exact h3 l (by rwa [← hp.nv]),
      fun l hl w hw => by
        simp only [k6ClauseLits, k6ClauseSize, k6ClauseOff, hp.nc, hp.nv, hp.arena, hp.wblit,
          hp.clSz, hp.clOff] at *
        exact h4 l hl w hw⟩
  have hrsn : K6ReasonOk st := fun i hi => by
    rw [hp.trl_end] at hi
    simpa only [hp.trl, hp.rsn, hp.nc, k6ClauseLits, k6ClauseOff, k6ClauseSize, hp.clOff, hp.clSz,
      hp.arena] using hinv.reasons i hi
  exact ⟨⟨hsh, hcl, hw, hba, hrsn⟩, k6TrailSynced_cast hsync hp.trl_end hp.trl hp.vals⟩

private def k6AnaLit (L : K6Layout) (skip : BitVec 32) (ks : K6State) (l : BitVec 32) :
    K6State :=
  let v := (l >>> 1).toNat
  let vlvl := ks.lvlArr[v]?.getD 0#32
  let fl := ks.flags[v]?.getD 0#32
  if l >>> 1 = skip then ks
  else if vlvl = 0#32 then ks
  else if (fl &&& 2#32) = 0#32 then
    let ks1 : K6State := { ks with flags := ks.flags.set v (fl ||| 2#32) }
    let ks2 : K6State := if ks1.nana.toNat < L.maxV then
      { ks1 with ana := ks1.ana.set ks1.nana.toNat (l >>> 1), nana := ks1.nana + 1#32 }
      else ks1
    if vlvl = ks.lvl then { ks2 with openCnt := ks2.openCnt + 1#32 }
    else if ks2.nkl.toNat < L.maxV then
      { ks2 with kl := ks2.kl.set ks2.nkl.toNat l, nkl := ks2.nkl + 1#32 }
    else ks2
  else ks

private def k6AnaPrefix (L : K6Layout) (skip : BitVec 32) (ks0 : K6State) (off : Nat) :
    Nat → K6State
  | 0 => ks0
  | n + 1 =>
    let st := k6AnaPrefix L skip ks0 off n
    k6AnaLit L skip st (st.arena[off + n]?.getD 0#32)

private theorem k6AnaLit_shape_diff (L : K6Layout) (skip : BitVec 32) (ks : K6State)
    (l : BitVec 32) :
    ∃ fl an na op kl nk, k6AnaLit L skip ks l =
      { ks with flags := fl, ana := an, nana := na, openCnt := op, kl := kl, nkl := nk } ∧
      ∀ v, v ≠ (l >>> 1).toNat → fl[v]? = ks.flags[v]? := by
  have hself : ∃ fl an na op kl nk, ks =
      { ks with flags := fl, ana := an, nana := na, openCnt := op, kl := kl, nkl := nk } ∧
      ∀ v, v ≠ (l >>> 1).toNat → fl[v]? = ks.flags[v]? :=
    ⟨ks.flags, ks.ana, ks.nana, ks.openCnt, ks.kl, ks.nkl, by cases ks; rfl, fun _ _ => rfl⟩
  unfold k6AnaLit; dsimp only
  by_cases h1 : l >>> 1 = skip
  · rw [k6a_ite_t h1]; exact hself
  rw [k6a_ite_f h1]
  by_cases h2 : ks.lvlArr[(l >>> 1).toNat]?.getD 0#32 = 0#32
  · rw [k6a_ite_t h2]; exact hself
  rw [k6a_ite_f h2]
  by_cases h3 : (ks.flags[(l >>> 1).toNat]?.getD 0#32 &&& 2#32) = 0#32
  · rw [k6a_ite_t h3]
    let ks1 : K6State := { ks with flags :=
      (ks.flags.set (l >>> 1).toNat (ks.flags[(l >>> 1).toNat]?.getD 0#32 ||| 2#32)) }
    by_cases ha : ks1.nana.toNat < L.maxV <;>
    · (first | rw [k6a_ite_t ha] | rw [k6a_ite_f ha])
      dsimp only
      by_cases ht : ks.lvlArr[(l >>> 1).toNat]?.getD 0#32 = ks.lvl
      · rw [k6a_ite_t ht]
        exact ⟨_, _, _, _, _, _, rfl, fun v hv => List.getElem?_set_ne hv.symm⟩
      · rw [k6a_ite_f ht]
        split <;> exact ⟨_, _, _, _, _, _, rfl, fun v hv => List.getElem?_set_ne hv.symm⟩
  · rw [k6a_ite_f h3]; exact hself

private theorem k6AnaLit_frame (L : K6Layout) (skip : BitVec 32) (ks : K6State) (l : BitVec 32) :
    ∃ fl an na op kl nk, k6AnaLit L skip ks l =
      { ks with flags := fl, ana := an, nana := na, openCnt := op, kl := kl, nkl := nk } :=
  let ⟨fl, an, na, op, kl, nk, h, _⟩ := k6AnaLit_shape_diff L skip ks l
  ⟨fl, an, na, op, kl, nk, h⟩

private theorem k6AnaLit_tailEq (L : K6Layout) (skip : BitVec 32) (ks : K6State) (l : BitVec 32)
    (hl : l.toNat < 2 * ks.nv.toNat) : K6TailEq L ks (k6AnaLit L skip ks l) := by
  obtain ⟨fl, an, na, op, kl, nk, heq, hfl⟩ := k6AnaLit_shape_diff L skip ks l
  rw [heq]; have := (k6_bv32_div2_lt hl).1
  exact ⟨rfl, fun v hv _ => ⟨rfl, rfl, hfl v (by omega), rfl, rfl, rfl, rfl⟩⟩

private theorem k6AnaPrefix_frame (L : K6Layout) (skip : BitVec 32) (ks0 : K6State)
    (off n : Nat) :
    ∃ fl an na op kl nk, k6AnaPrefix L skip ks0 off n =
      { ks0 with flags := fl, ana := an, nana := na, openCnt := op, kl := kl, nkl := nk } := by
  induction n with
  | zero =>
    exact ⟨ks0.flags, ks0.ana, ks0.nana, ks0.openCnt, ks0.kl, ks0.nkl, by cases ks0; rfl⟩
  | succ k ih =>
    obtain ⟨_, _, _, _, _, _, h1⟩ := ih; dsimp only [k6AnaPrefix]
    obtain ⟨fl2, an2, na2, op2, kl2, nk2, h2⟩ := k6AnaLit_frame L skip _ _
    rw [h2, h1]; exact ⟨fl2, an2, na2, op2, kl2, nk2, rfl⟩

private theorem k6a_resolvent_mono_of_fl {ks ks3 : K6State} {idx : Nat}
    (hidx : idx ≤ ks.trl_end.toNat) (htrl_len : ks.trl_end.toNat ≤ ks.trl.length)
    (htrl_lt : ∀ l ∈ k6TrailLits ks, l < 2 * ks.nv.toNat)
    (htrl_eq : ks3.trl = ks.trl) (hlv_eq : ks3.lvlArr = ks.lvlArr) (hlv : ks3.lvl = ks.lvl)
    (hfl_mono : ∀ v < ks.nv.toNat,
      (ks.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32 → (ks3.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32)
    (hkl_sub : ∀ i, 1 ≤ i → i < min ks.nkl.toNat ks.kl.length →
      ∃ i', 1 ≤ i' ∧ i' < min ks3.nkl.toNat ks3.kl.length ∧ ks3.kl[i']? = ks.kl[i]?) :
    ∀ x ∈ k6ResolventLits ks idx, x ∈ k6ResolventLits ks3 idx := fun x hx => by
  rw [k6a_mem_resolvent_iff] at hx ⊢
  rcases hx with ⟨j, hj, htrl, hlvl, hfl⟩ | ⟨i, hi1, hi2, rfl⟩
  · left
    have hlt := htrl_lt _ (k6_mem_trailLits_of_lt (Nat.lt_of_lt_of_le hj hidx) htrl_len)
    rw [htrl] at hlt
    exact ⟨j, hj, htrl_eq.symm ▸ htrl, hlv_eq.symm ▸ hlv.symm ▸ hlvl, hfl_mono _ (by omega) hfl⟩
  · right; obtain ⟨i', hi1', hi2', heq⟩ := hkl_sub i hi1 hi2
    exact ⟨i', hi1', hi2', by rw [heq]⟩

private theorem k6AnaLit_inv_of_ks2 {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    {idx : Nat} {fl an kl : List (BitVec 32)} {op nk : BitVec 32}
    (hinv : K6AnaInv L P ks idx)
    (hnana1 : (ks.nana + 1#32).toNat = ks.nana.toNat + 1)
    (hnana_lt_nv : ks.nana.toNat < ks.nv.toNat)
    (hana_nodup2 : ((an.take (ks.nana + 1#32).toNat).map BitVec.toNat).Nodup)
    (hana_lt2 : ∀ i < (ks.nana + 1#32).toNat, (an[i]?.getD 0#32).toNat < ks.nv.toNat)
    (hflags_seen2 : ∀ u < ks.nv.toNat, ((fl[u]?.getD 0#32 &&& 2#32) ≠ 0#32) ↔
      ∃ i < (ks.nana + 1#32).toNat, (an[i]?.getD 0#32).toNat = u)
    (hnkl_count2 : ∀ u < ks.nv.toNat,
      (fl[u]?.getD 0#32 &&& 2#32) ≠ 0#32 → 0 < (ks.lvlArr[u]?.getD 0#32).toNat)
    (hseen_trl2 : ∀ u < ks.nv.toNat,
      (fl[u]?.getD 0#32 &&& 2#32) ≠ 0#32 → ks.lvlArr[u]?.getD 0#32 = ks.lvl →
      ∃ j < ks.trl_end.toNat, (ks.trl[j]?.getD 0#32).toNat / 2 = u)
    (hrest : let ks3 : K6State :=
        { ks with flags := fl, ana := an, nana := ks.nana + 1#32, openCnt := op, kl := kl, nkl :=
          nk }
      ks3.ShapesOk L ∧ 1 ≤ nk.toNat ∧ nk.toNat ≤ ks.nv.toNat ∧
      (∀ i, 1 ≤ i → i < nk.toNat →
        let x := (kl[i]?.getD 0#32).toNat
        x < 2 * ks.nv.toNat ∧ (fl[x / 2]?.getD 0#32 &&& 2#32) ≠ 0#32 ∧
        0 < (ks.lvlArr[x / 2]?.getD 0#32).toNat ∧
        (ks.lvlArr[x / 2]?.getD 0#32).toNat < ks.lvl.toNat ∧ ks.vals[x]? = some 2#32) ∧
      (∀ u < ks.nv.toNat, (fl[u]?.getD 0#32 &&& 2#32) ≠ 0#32 →
        (ks.lvlArr[u]?.getD 0#32).toNat < ks.lvl.toNat →
        ∃ i, 1 ≤ i ∧ i < nk.toNat ∧ (kl[i]?.getD 0#32).toNat / 2 = u) ∧
      (((kl.take nk.toNat).drop 1).map (fun x => x.toNat / 2)).Nodup ∧
      op.toNat = ((List.range idx).filter fun j =>
        let u := (ks.trl[j]?.getD 0#32).toNat / 2
        decide (ks.lvlArr[u]?.getD 0#32 = ks.lvl ∧ (fl[u]?.getD 0#32 &&& 2#32) ≠ 0#32)).length) :
    K6AnaInv L P ({ ks with
        flags := fl, ana := an, nana := ks.nana + 1#32, openCnt := op, kl := kl, nkl := nk })
      idx := by
  rcases hrest with ⟨hsh3, hnk1, hnk_le, hkl_nt, hkl_inj, hkl_nd, hop_eq⟩
  exact ⟨hsh3, hinv.acap_eq, hinv.max_v_eq, hinv.max_orig_eq, hinv.max_cl_eq, hinv.nv_le,
    hinv.nc_le, hinv.alen_le, hinv.nassump_le, hinv.lvl_pos, hinv.idx_le, hinv.cl_wf, hinv.cl_mono,
    hinv.incons_ok, hinv.assump_ok, hinv.watches, k6BaseAssignOk_cast hinv.assign, hinv.synced,
    hinv.reasons, hnk1, hnk_le, by change (ks.nana + 1#32).toNat ≤ ks.nv.toNat; rw [hnana1]; omega,
    hana_nodup2, hana_lt2, hflags_seen2, hkl_nt, hkl_inj, hnkl_count2, hkl_nd, hop_eq, hseen_trl2⟩

private theorem k6AnaLit_preserves_anaInv {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    {idx : Nat} {skip l : BitVec 32} (hinv : K6AnaInv L P ks idx)
    (hvdec : ∃ v_dec < ks.nv.toNat, ks.lvlArr[v_dec]?.getD 0#32 = ks.lvl)
    (hl_lt : l.toNat < 2 * ks.nv.toNat)
    (hl_ok : l.toNat / 2 ≠ skip.toNat → ks.vals[l.toNat]? = some 2#32 ∧
      (ks.lvlArr[l.toNat / 2]?.getD 0#32 = ks.lvl →
        ∃ j < idx, (ks.trl[j]?.getD 0#32).toNat = l.toNat ^^^ 1)) :
    K6AnaInv L P (k6AnaLit L skip ks l) idx ∧
    K6AnaPreserved ks (k6AnaLit L skip ks l) ∧
    (∀ v < ks.nv.toNat, (ks.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32 →
      ((k6AnaLit L skip ks l).flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32) ∧
    (∀ x ∈ k6ResolventLits ks idx, x ∈ k6ResolventLits (k6AnaLit L skip ks l) idx) := by
  have hm := L.hmaxV; have hnv := hinv.nv_le; have hsh := hinv.shapes
  obtain ⟨hv_eq, hv_lt⟩ := k6_bv32_div2_lt hl_lt
  unfold k6AnaLit; dsimp only
  by_cases hskip : l >>> 1 = skip
  · rw [k6a_ite_t hskip]; exact ⟨hinv, k6AnaPreserved_refl ks, fun _ _ h => h, fun _ h => h⟩
  rw [k6a_ite_f hskip]
  by_cases hvlvl0 : ks.lvlArr[(l >>> 1).toNat]?.getD 0#32 = 0#32
  · rw [k6a_ite_t hvlvl0]; exact ⟨hinv, k6AnaPreserved_refl ks, fun _ _ h => h, fun _ h => h⟩
  rw [k6a_ite_f hvlvl0]
  by_cases hfl0 : (ks.flags[(l >>> 1).toNat]?.getD 0#32 &&& 2#32) = 0#32
  · rw [k6a_ite_t hfl0]
    have hskip_ne : l.toNat / 2 ≠ skip.toNat := fun heq =>
      hskip (BitVec.eq_of_toNat_eq (by rw [hv_eq]; exact heq))
    obtain ⟨hl_val2, hl_top_trl⟩ := hl_ok hskip_ne
    have hv_mv : (l >>> 1).toNat < L.maxV := by omega
    have hv_not_ana : (l >>> 1).toNat ∉ (ks.ana.take ks.nana.toNat).map BitVec.toNat := by
      intro hmem; rw [List.mem_map] at hmem; obtain ⟨b, hb, hbeq⟩ := hmem
      rw [List.mem_take_iff_getElem] at hb; obtain ⟨i, hi, hget⟩ := hb
      exact (hinv.flags_seen (l >>> 1).toNat hv_lt).mpr ⟨i, by omega, by
        rw [List.getElem?_eq_getElem (by omega : i < ks.ana.length), Option.getD_some, hget,
          hbeq]⟩ hfl0
    have hana_take_len : ((ks.ana.take ks.nana.toNat).map BitVec.toNat).length = ks.nana.toNat := by
      rw [List.length_map, List.length_take, hsh.ana_len]; have := hinv.nana_le; omega
    have hnana_lt_nv : ks.nana.toNat < ks.nv.toNat := by
      have hnd : ((l >>> 1).toNat :: (ks.ana.take ks.nana.toNat).map BitVec.toNat).Nodup :=
        List.nodup_cons.mpr ⟨hv_not_ana, hinv.ana_nodup⟩
      have hlt_all : ∀ x ∈ (l >>> 1).toNat :: (ks.ana.take ks.nana.toNat).map BitVec.toNat,
          x < ks.nv.toNat := fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hv_lt
        · rw [List.mem_map] at hx'; obtain ⟨b, hb, rfl⟩ := hx'
          rw [List.mem_take_iff_getElem] at hb; obtain ⟨i, hi, hget⟩ := hb
          have ha := hinv.ana_lt i (by omega)
          rwa [List.getElem?_eq_getElem (by omega : i < ks.ana.length), Option.getD_some,
            hget] at ha
      have hle := k6_nodup_subset_length hnd hlt_all
      simp only [List.length_cons, hana_take_len] at hle; omega
    have hnana_mv : ks.nana.toNat < L.maxV := by omega
    have hnana1 : (ks.nana + 1#32).toNat = ks.nana.toNat + 1 := by bv_omega
    let v := (l >>> 1).toNat; let fl := ks.flags[v]?.getD 0#32
    let fls2 := ks.flags.set v (fl ||| 2#32); let ana2 := ks.ana.set ks.nana.toNat (l >>> 1)
    let ks1 : K6State := { ks with flags := fls2 }
    let ks2 : K6State := { ks1 with ana := ana2, nana := ks1.nana + 1#32 }
    have hks2_ite : (if ks1.nana.toNat < L.maxV then
        { ks1 with ana := ks1.ana.set ks1.nana.toNat (l >>> 1), nana := ks1.nana + 1#32 }
        else ks1) = ks2 := k6a_ite_t hnana_mv
    change K6AnaInv L P _ idx ∧ K6AnaPreserved ks _ ∧ _
    rw [show (let ks1_0 : K6State := { ks with flags := fls2 }
        let ks2_0 : K6State := if ks1_0.nana.toNat < L.maxV then
          { ks1_0 with ana := ks1_0.ana.set ks1_0.nana.toNat (l >>> 1), nana := ks1_0.nana + 1#32 }
          else ks1_0
        if ks.lvlArr[v]?.getD 0#32 = ks.lvl then { ks2_0 with openCnt := ks2_0.openCnt + 1#32 }
        else if ks2_0.nkl.toNat < L.maxV then
          { ks2_0 with kl := ks2_0.kl.set ks2_0.nkl.toNat l, nkl := ks2_0.nkl + 1#32 }
        else ks2_0) =
        (if ks.lvlArr[v]?.getD 0#32 = ks.lvl then { ks2 with openCnt := ks2.openCnt + 1#32 }
        else if ks2.nkl.toNat < L.maxV then
          { ks2 with kl := ks2.kl.set ks2.nkl.toNat l, nkl := ks2.nkl + 1#32 }
        else ks2) from by dsimp only; rw [hks2_ite]]
    have hfl_len : v < ks.flags.length := by rw [hsh.flags_len]; exact hv_mv
    have hana_len : ks.nana.toNat < ks.ana.length := by rw [hsh.ana_len]; exact hnana_mv
    have hfl_set_self : (fls2[v]?.getD 0#32 &&& 2#32) ≠ 0#32 := by
      rw [List.getElem?_set_self hfl_len, Option.getD_some]; exact k6a_fl_or2_and2_nz fl
    have hfl_set_ne : ∀ u, u ≠ v → fls2[u]? = ks.flags[u]? := fun u hu =>
      List.getElem?_set_ne (Ne.symm hu)
    have hfl_mono : ∀ u < ks.nv.toNat,
        (ks.flags[u]?.getD 0#32 &&& 2#32) ≠ 0#32 → (fls2[u]?.getD 0#32 &&& 2#32) ≠ 0#32 := by
      intro u _ hnz; by_cases huv : u = v
      · subst huv; exact hfl_set_self
      · rwa [hfl_set_ne u huv]
    have hsh2 : ks2.ShapesOk L :=
      ((hsh.putArr .flags v (fl ||| 2#32)).putArr .ana ks.nana.toNat (l >>> 1)).putHdr .nana
        (ks.nana + 1#32)
    have hana_nodup2 : ((ana2.take (ks.nana + 1#32).toNat).map BitVec.toNat).Nodup := by
      rw [hnana1, List.take_add_one, List.map_append, List.take_set_of_le (Nat.le_refl _),
        List.getElem?_set_self hana_len]; simp only [Option.toList_some, List.map_cons,
          List.map_nil, List.nodup_append]
      exact ⟨hinv.ana_nodup, by simp, fun x hx y hy heq => by
        rw [List.mem_singleton] at hy; subst hy; subst heq; exact hv_not_ana hx⟩
    have hana_lt2 : ∀ i < (ks.nana + 1#32).toNat, (ana2[i]?.getD 0#32).toNat < ks.nv.toNat := by
      intro i hi; rw [hnana1] at hi; by_cases hie : i = ks.nana.toNat
      · subst hie; rw [List.getElem?_set_self hana_len, Option.getD_some]; exact hv_lt
      · rw [List.getElem?_set_ne (Ne.symm hie)]; exact hinv.ana_lt i (by omega)
    have hflags_seen2 : ∀ u < ks.nv.toNat, ((fls2[u]?.getD 0#32 &&& 2#32) ≠ 0#32) ↔
          ∃ i < (ks.nana + 1#32).toNat, (ana2[i]?.getD 0#32).toNat = u := by
      intro u hu; rw [hnana1]; by_cases huv : u = v
      · subst huv; exact ⟨fun _ => ⟨ks.nana.toNat, by omega, by
          rw [List.getElem?_set_self hana_len, Option.getD_some]⟩, fun _ => hfl_set_self⟩
      · rw [hfl_set_ne u huv, hinv.flags_seen u hu]; constructor
        · rintro ⟨i, hi, heq⟩; exact ⟨i, by omega, by rwa [List.getElem?_set_ne (by omega)]⟩
        · rintro ⟨i, hi, heq⟩; by_cases hie : i = ks.nana.toNat
          · subst hie; rw [List.getElem?_set_self hana_len, Option.getD_some] at heq
            exact absurd heq.symm huv
          · rw [List.getElem?_set_ne (Ne.symm hie)] at heq; exact ⟨i, by omega, heq⟩
    have hnkl_count2 : ∀ u < ks.nv.toNat,
        (fls2[u]?.getD 0#32 &&& 2#32) ≠ 0#32 → 0 < (ks.lvlArr[u]?.getD 0#32).toNat := by
      intro u hu hnz; by_cases huv : u = v
      · subst huv; exact Nat.pos_of_ne_zero fun hz => hvlvl0 (BitVec.eq_of_toNat_eq hz)
      · rw [hfl_set_ne u huv] at hnz; exact hinv.nkl_count u hu hnz
    have hseen_trl2 : ∀ u < ks.nv.toNat,
        (fls2[u]?.getD 0#32 &&& 2#32) ≠ 0#32 → ks.lvlArr[u]?.getD 0#32 = ks.lvl →
        ∃ j < ks.trl_end.toNat, (ks.trl[j]?.getD 0#32).toNat / 2 = u := by
      intro u hu hnz hlvl; by_cases huv : u = v
      · subst huv; obtain ⟨j0, hj0_idx, hj0_eq⟩ := hl_top_trl (by rw [← hv_eq]; exact hlvl)
        exact ⟨j0, Nat.lt_of_lt_of_le hj0_idx hinv.idx_le, by
          rw [hj0_eq, k6a_xor1_div2]; exact hv_eq.symm⟩
      · rw [hfl_set_ne u huv] at hnz; exact hinv.seen_in_trl u hu hnz hlvl
    have hvlvl_le := hinv.assign.trl_lvl_le v hv_lt
    have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
      rw [hsh.trl_len]; have := hinv.assign.trl_end_le; omega
    by_cases htop : ks.lvlArr[v]?.getD 0#32 = ks.lvl
    · rw [k6a_ite_t htop]
      obtain ⟨j0, hj0_idx, hj0_eq⟩ := hl_top_trl (by rw [← hv_eq]; exact htop)
      have hj0_te : j0 < ks.trl_end.toNat := Nat.lt_of_lt_of_le hj0_idx hinv.idx_le
      have hj0_var : (ks.trl[j0]?.getD 0#32).toNat / 2 = v := by
        rw [hj0_eq, k6a_xor1_div2]; exact hv_eq.symm
      have hfilter_succ :
          ((List.range idx).filter fun j =>
            let u := (ks.trl[j]?.getD 0#32).toNat / 2
            decide (ks.lvlArr[u]?.getD 0#32 = ks.lvl ∧
              (fls2[u]?.getD 0#32 &&& 2#32) ≠ 0#32)).length =
          ((List.range idx).filter fun j =>
            let u := (ks.trl[j]?.getD 0#32).toNat / 2
            decide (ks.lvlArr[u]?.getD 0#32 = ks.lvl ∧
              (ks.flags[u]?.getD 0#32 &&& 2#32) ≠ 0#32)).length + 1 := by
        refine k6a_filter_length_flip_one List.nodup_range (List.mem_range.mpr hj0_idx) ?_ ?_ ?_
        · simp only [decide_eq_false_iff_not]; rw [hj0_var]; exact fun h => h.2 hfl0
        · simp only [decide_eq_true_eq]
          rw [hj0_var]; exact ⟨htop, hfl_set_self⟩
        · intro j hj hne; rw [List.mem_range] at hj
          have hvar_ne : (ks.trl[j]?.getD 0#32).toNat / 2 ≠ v := by
            rw [← hj0_var]
            exact k6_trl_nodup_var_ne hsh hnv hinv.assign (Nat.lt_of_lt_of_le hj hinv.idx_le) hj0_te
              hne
          change decide (ks.lvlArr[_]?.getD 0#32 = ks.lvl ∧
            (fls2[_]?.getD 0#32 &&& 2#32) ≠ 0#32) = _
          rw [hfl_set_ne _ hvar_ne]
      have hop_le : ks.openCnt.toNat ≤ idx := by
        rw [hinv.open_eq]; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
      have hop1 : (ks.openCnt + 1#32).toNat = ks.openCnt.toNat + 1 := by
        have := hinv.idx_le; have := hinv.assign.trl_end_le; bv_omega
      have hinv3 := k6AnaLit_inv_of_ks2 hinv hnana1 hnana_lt_nv hana_nodup2 hana_lt2 hflags_seen2
        hnkl_count2 hseen_trl2 ⟨hsh2.putHdr .openCnt (ks2.openCnt + 1#32), hinv.nkl_pos,
          hinv.nkl_le,
        fun i hi1 hi2 => let hk := hinv.kl_nonTop i hi1 hi2
          ⟨hk.1, hfl_mono _ (Nat.div_lt_of_lt_mul hk.1) hk.2.1, hk.2.2⟩,
        fun u hu hnz hlt_lv => by
          by_cases huv : u = v
          · subst huv; change (ks.lvlArr[v]?.getD 0#32).toNat < ks.lvl.toNat at hlt_lv
            rw [htop] at hlt_lv; omega
          · rw [hfl_set_ne u huv] at hnz; exact hinv.kl_injective u hu hnz hlt_lv,
        hinv.kl_nodup, by rw [hop1, hinv.open_eq, ← hfilter_succ]⟩
      exact ⟨hinv3, k6AnaPreserved_frame ks, hfl_mono, k6a_resolvent_mono_of_fl hinv.idx_le htrl_len
        hinv.assign.trl_lt rfl rfl rfl hfl_mono fun i hi1 hi2 => ⟨i, hi1, hi2, rfl⟩⟩
    · rw [k6a_ite_f htop]
      have hvlvl_lt : (ks.lvlArr[v]?.getD 0#32).toNat < ks.lvl.toNat := by
        have hne : (ks.lvlArr[v]?.getD 0#32).toNat ≠ ks.lvl.toNat := fun h =>
          htop (BitVec.eq_of_toNat_eq h)
        omega
      obtain ⟨v_dec, hvdec_lt, hvdec_lvl⟩ := hvdec
      have hv_ne_vdec : v ≠ v_dec := fun h => by subst h; rw [hvdec_lvl] at hvlvl_lt; omega
      let klVars := ((ks.kl.take ks.nkl.toNat).drop 1).map (fun x => x.toNat / 2)
      have hklVars_len : klVars.length = ks.nkl.toNat - 1 := by
        simp only [klVars, List.length_map, List.length_drop, List.length_take, hsh.kl_len]
        have := hinv.nkl_le; omega
      have hklVars_prop : ∀ u ∈ klVars, u < ks.nv.toNat ∧
          (ks.flags[u]?.getD 0#32 &&& 2#32) ≠ 0#32 ∧
          (ks.lvlArr[u]?.getD 0#32).toNat < ks.lvl.toNat := by
        intro u hm_u; rw [List.mem_map] at hm_u; obtain ⟨b, hb, rfl⟩ := hm_u
        rw [List.mem_iff_getElem] at hb; obtain ⟨k, hk, rfl⟩ := hb
        have hk1 : k + 1 < ks.nkl.toNat := by
          simp [List.length_take, hsh.kl_len] at hk; have := hinv.nkl_le; omega
        have hnt := hinv.kl_nonTop (k + 1) (by omega) hk1; dsimp only at hnt
        have hget : (ks.kl[k + 1]?.getD 0#32).toNat =
            (((ks.kl.take ks.nkl.toNat).drop 1)[k]'hk).toNat := by
          simp only [List.getElem_drop, List.getElem_take]
          rw [List.getElem?_eq_getElem (by rw [hsh.kl_len]; have := hinv.nkl_le; omega),
            Option.getD_some]; congr 2; omega
        rw [hget] at hnt; exact ⟨by omega, hnt.2.1, hnt.2.2.2.1⟩
      have hv_not_kl : v ∉ klVars := fun hm_v => (hklVars_prop v hm_v).2.1 hfl0
      have hvdec_not_kl : v_dec ∉ klVars := fun hm_vd => by
        have hlt := (hklVars_prop v_dec hm_vd).2.2; rw [hvdec_lvl] at hlt; omega
      have hnkl_lt_nv : ks.nkl.toNat < ks.nv.toNat := by
        have hnd : (v :: v_dec :: klVars).Nodup :=
          List.nodup_cons.mpr ⟨by simp [hv_ne_vdec, hv_not_kl],
            List.nodup_cons.mpr ⟨hvdec_not_kl, hinv.kl_nodup⟩⟩
        have hlt_all : ∀ x ∈ v :: v_dec :: klVars, x < ks.nv.toNat := fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx1
          · exact hv_lt
          · rcases List.mem_cons.mp hx1 with rfl | hx2
            · exact hvdec_lt
            · exact (hklVars_prop x hx2).1
        have hle := k6_nodup_subset_length hnd hlt_all
        simp only [List.length_cons, hklVars_len] at hle; have := hinv.nkl_pos; omega
      have hnkl_mv : ks.nkl.toNat < L.maxV := by omega
      have hnkl1 : (ks.nkl + 1#32).toNat = ks.nkl.toNat + 1 := by bv_omega
      have hkl_len : ks.nkl.toNat < ks.kl.length := by rw [hsh.kl_len]; exact hnkl_mv
      let kl3 := ks.kl.set ks.nkl.toNat l
      rw [k6a_ite_t hnkl_mv]
      have hkl_nodup3 : (((kl3.take (ks.nkl + 1#32).toNat).drop 1).map
          (fun x => x.toNat / 2)).Nodup := by
        have htake : (((kl3.take (ks.nkl + 1#32).toNat).drop 1).map (fun x => x.toNat / 2)) =
            klVars ++ [v] := by
          rw [hnkl1, List.take_add_one, List.take_set_of_le (Nat.le_refl _),
            List.getElem?_set_self hkl_len, Option.toList_some,
            List.drop_append_of_le_length
              (by rw [List.length_take, hsh.kl_len]; have := hinv.nkl_pos; omega),
            List.map_append]
          simp [klVars, v, hv_eq]
        rw [htake, List.nodup_append]
        exact ⟨hinv.kl_nodup, by simp, fun x hx y hy heq => by
          rw [List.mem_singleton] at hy; subst hy; subst heq; exact hv_not_kl hx⟩
      have hfilter_eq :
          ((List.range idx).filter fun j =>
            let u := (ks.trl[j]?.getD 0#32).toNat / 2
            decide (ks.lvlArr[u]?.getD 0#32 = ks.lvl ∧ (fls2[u]?.getD 0#32 &&& 2#32) ≠ 0#32)) =
          ((List.range idx).filter fun j =>
            let u := (ks.trl[j]?.getD 0#32).toNat / 2
            decide (ks.lvlArr[u]?.getD 0#32 = ks.lvl ∧
              (ks.flags[u]?.getD 0#32 &&& 2#32) ≠ 0#32)) := by
        refine List.filter_congr fun j _ => ?_
        by_cases huv : (ks.trl[j]?.getD 0#32).toNat / 2 = v
        · rw [huv]; simp [htop]
        · change decide (ks.lvlArr[_]?.getD 0#32 = ks.lvl ∧
          (fls2[_]?.getD 0#32 &&& 2#32) ≠ 0#32) = _
          rw [hfl_set_ne _ huv]
      have hinv3 := k6AnaLit_inv_of_ks2 hinv hnana1 hnana_lt_nv hana_nodup2 hana_lt2 hflags_seen2
        hnkl_count2 hseen_trl2 ⟨(hsh2.putArr .kl ks.nkl.toNat l).putHdr .nkl (ks.nkl + 1#32),
        by change 1 ≤ (ks.nkl + 1#32).toNat; rw [hnkl1]; omega,
        by change (ks.nkl + 1#32).toNat ≤ ks.nv.toNat; rw [hnkl1]; omega,
        fun i hi1 hi2 => by
          dsimp only [K6State.putArr, ks2, ks1]
          rw [hnkl1] at hi2; by_cases hie : i = ks.nkl.toNat
          · subst hie; rw [List.getElem?_set_self hkl_len, Option.getD_some]
            refine ⟨hl_lt, ?_, ?_, ?_, hl_val2⟩
            · rw [← hv_eq]; exact hfl_set_self
            · rw [← hv_eq]; exact Nat.pos_of_ne_zero fun hz => hvlvl0 (BitVec.eq_of_toNat_eq hz)
            · rw [← hv_eq]; exact hvlvl_lt
          · rw [List.getElem?_set_ne (Ne.symm hie)]
            have hk := hinv.kl_nonTop i hi1 (by omega)
            exact ⟨hk.1, hfl_mono _ (Nat.div_lt_of_lt_mul hk.1) hk.2.1, hk.2.2⟩,
        fun u hu hnz hlt_lv => by
          dsimp only [K6State.putArr, ks2, ks1]
          by_cases huv : u = v
          · subst huv; refine ⟨ks.nkl.toNat, hinv.nkl_pos, by rw [hnkl1]; omega, ?_⟩
            rw [List.getElem?_set_self hkl_len, Option.getD_some]; exact hv_eq.symm
          · rw [hfl_set_ne u huv] at hnz
            obtain ⟨i, hi1, hi2, _⟩ := hinv.kl_injective u hu hnz hlt_lv
            refine ⟨i, hi1, by rw [hnkl1]; omega, ?_⟩
            rwa [List.getElem?_set_ne (by omega)],
        hkl_nodup3, by rw [hfilter_eq]; exact hinv.open_eq⟩
      exact ⟨hinv3, k6AnaPreserved_frame ks, hfl_mono, k6a_resolvent_mono_of_fl hinv.idx_le htrl_len
        hinv.assign.trl_lt rfl rfl rfl hfl_mono fun i hi1 hi2 => by
          have hi_lt : i < ks.nkl.toNat := Nat.lt_of_lt_of_le hi2 (Nat.min_le_left _ _)
          exact ⟨i, hi1, by change i < min (ks.nkl + 1#32).toNat kl3.length
                            rw [hnkl1, List.length_set, hsh.kl_len]; omega,
            List.getElem?_set_ne (Ne.symm (Nat.ne_of_lt hi_lt))⟩⟩
  · rw [k6a_ite_f hfl0]; exact ⟨hinv, k6AnaPreserved_refl ks, fun _ _ h => h, fun _ h => h⟩

private theorem k6AnaLit_effect_on_lit {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    {idx : Nat} {skip l : BitVec 32} (hinv : K6AnaInv L P ks idx)
    (hvdec : ∃ v_dec < ks.nv.toNat, ks.lvlArr[v_dec]?.getD 0#32 = ks.lvl)
    (hl_lt : l.toNat < 2 * ks.nv.toNat)
    (hl_ok : l.toNat / 2 ≠ skip.toNat → ks.vals[l.toNat]? = some 2#32 ∧
      (ks.lvlArr[l.toNat / 2]?.getD 0#32 = ks.lvl →
        ∃ j < idx, (ks.trl[j]?.getD 0#32).toNat = l.toNat ^^^ 1))
    (hskip_ne : l.toNat / 2 ≠ skip.toNat) :
    let ks' := k6AnaLit L skip ks l
    (ks.lvlArr[l.toNat / 2]?.getD 0#32 = 0#32 → SemEntails P [l.toNat ^^^ 1]) ∧
    (ks.lvlArr[l.toNat / 2]?.getD 0#32 ≠ 0#32 → l.toNat ∈ k6ResolventLits ks' idx) := by
  have hm := L.hmaxV; obtain ⟨hv_eq, _⟩ := k6_bv32_div2_lt hl_lt
  obtain ⟨hl_val2, hl_top_trl⟩ := hl_ok hskip_ne
  have hskip_bv : l >>> 1 ≠ skip := fun h => hskip_ne (by rw [← hv_eq, h])
  obtain ⟨hinv', hpres', hfl_mono, _⟩ := k6AnaLit_preserves_anaInv hinv hvdec hl_lt hl_ok
  constructor
  · intro hvlvl0
    obtain ⟨j0, hj0_te, hj0_eq⟩ := k6_falsified_to_trail hinv.assign hinv.synced hl_lt hl_val2
    have hj0_var : (ks.trl[j0]?.getD 0#32).toNat / 2 = l.toNat / 2 := by
      rw [hj0_eq, k6a_xor1_div2]
    have h0 := hinv.assign.lvl0_ok j0 hj0_te (by rwa [hj0_var])
    rw [hj0_eq] at h0; exact h0.2.2
  · intro hvlvl_ne
    have hfl_nz' : ((k6AnaLit L skip ks l).flags[l.toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32 := by
      by_cases hfl0 : (ks.flags[(l >>> 1).toNat]?.getD 0#32 &&& 2#32) = 0#32
      · unfold k6AnaLit; dsimp only
        have hv_ne' : ks.lvlArr[(l >>> 1).toNat]?.getD 0#32 ≠ 0#32 := by rwa [hv_eq]
        rw [k6a_ite_f hskip_bv, k6a_ite_f hv_ne', k6a_ite_t hfl0]
        have hfl_len : (l >>> 1).toNat < ks.flags.length := by
          rw [hinv.shapes.flags_len]; have := hinv.nv_le; omega
        have hks1_fl : ∀ s : K6State, s.flags = ks.flags.set (l >>> 1).toNat
            (ks.flags[(l >>> 1).toNat]?.getD 0#32 ||| 2#32) →
            (s.flags[l.toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32 := fun s hs => by
          rw [hs, ← hv_eq, List.getElem?_set_self hfl_len, Option.getD_some]
          exact k6a_fl_or2_and2_nz _
        split <;> (split <;> (try split) <;> exact hks1_fl _ rfl)
      · exact hfl_mono (l.toNat / 2) (by omega) (by rwa [← hv_eq])
    rw [k6a_mem_resolvent_iff]
    by_cases htop : ks.lvlArr[l.toNat / 2]?.getD 0#32 = ks.lvl
    · left; obtain ⟨j0, hj0_idx, hj0_eq⟩ := hl_top_trl htop
      refine ⟨j0, hj0_idx, by rw [hpres'.trl]; exact hj0_eq,
        by rw [hpres'.lvlArr, hpres'.lvl, k6a_xor1_div2]; exact htop,
        by rw [k6a_xor1_div2]; exact hfl_nz'⟩
    · right
      have hvlvl_lt : ((k6AnaLit L skip ks l).lvlArr[l.toNat / 2]?.getD 0#32).toNat <
          (k6AnaLit L skip ks l).lvl.toNat := by
        rw [hpres'.lvlArr, hpres'.lvl]
        have hle := hinv.assign.trl_lvl_le (l.toNat / 2) (by omega)
        have hne : (ks.lvlArr[l.toNat / 2]?.getD 0#32).toNat ≠ ks.lvl.toNat := fun h =>
          htop (BitVec.eq_of_toNat_eq h)
        omega
      obtain ⟨i, hi1, hi2, hieq⟩ :=
        hinv'.kl_injective (l.toNat / 2) (by rw [hpres'.nv]; omega) hfl_nz' hvlvl_lt
      have hnt := hinv'.kl_nonTop i hi1 hi2
      obtain ⟨j0, hj0_te, hj0_eq⟩ :=
        k6_falsified_to_trail hinv.assign hinv.synced hl_lt hl_val2
      have hsync0 := hinv.synced j0 hj0_te; dsimp only at hsync0
      rw [hj0_eq, k6_nat_xor1_xor1] at hsync0
      have hkl_eq : ((k6AnaLit L skip ks l).kl[i]?.getD 0#32).toNat = l.toNat := by
        rcases (litVar_eq_iff ((k6AnaLit L skip ks l).kl[i]?.getD 0#32).toNat l.toNat).mp
            (by simpa [litVar] using hieq) with h1 | h1
        · exact h1
        · exfalso; have hv2 : ks.vals[l.toNat ^^^ 1]? = some 2#32 := by
            have := hnt.2.2.2.2
            rw [hpres'.vals, h1, show litNeg l.toNat = l.toNat ^^^ 1 from rfl] at this; exact this
          rw [hsync0.1] at hv2; cases hv2
      have hmin : i < min (k6AnaLit L skip ks l).nkl.toNat (k6AnaLit L skip ks l).kl.length := by
        rw [hinv'.shapes.kl_len]; have := hinv'.nkl_le; have := hinv'.nv_le; omega
      exact ⟨i, hi1, hmin, hkl_eq⟩

private theorem k6AnaPrefix_properties {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    {idx : Nat} {cid skip : BitVec 32} (hinv : K6AnaInv L P ks idx)
    (hcid : cid.toNat < ks.nc.toNat)
    (hvdec : ∃ v_dec < ks.nv.toNat, ks.lvlArr[v_dec]?.getD 0#32 = ks.lvl)
    (hlits : ∀ l ∈ k6ClauseLits ks cid.toNat, l / 2 ≠ skip.toNat →
      ks.vals[l]? = some 2#32 ∧
      (ks.lvlArr[l / 2]?.getD 0#32 = ks.lvl →
        ∃ j < idx, (ks.trl[j]?.getD 0#32).toNat = l ^^^ 1)) :
    let off := k6ClauseOff ks cid.toNat; let sz := k6ClauseSize ks cid.toNat
    ∀ n ≤ sz,
      let st := k6AnaPrefix L skip ks off n
      K6AnaInv L P st idx ∧ K6AnaPreserved ks st ∧ K6TailEq L ks st ∧
      (∀ v < ks.nv.toNat, (ks.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32 →
        (st.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32) ∧
      (∀ x ∈ k6ResolventLits ks idx, x ∈ k6ResolventLits st idx) ∧
      (∀ k < n,
        let l := (ks.arena[off + k]?.getD 0#32).toNat
        l / 2 ≠ skip.toNat →
        (ks.lvlArr[l / 2]?.getD 0#32 = 0#32 → SemEntails P [l ^^^ 1]) ∧
        (ks.lvlArr[l / 2]?.getD 0#32 ≠ 0#32 → l ∈ k6ResolventLits st idx)) := by
  intro off sz n
  have hwf := hinv.cl_wf cid.toNat hcid
  have hbd : off + sz ≤ ks.arena.length := by
    rw [hinv.shapes.arena_len]; have := hwf.2.1; have := hinv.alen_le; omega
  induction n with
  | zero =>
    intro _; exact ⟨hinv, k6AnaPreserved_refl ks, k6TailEq_refl L ks,
      fun _ _ h => h, fun _ h => h, fun _ hk => by omega⟩
  | succ k ih =>
    intro hk_le
    obtain ⟨hinv_k, hpres_k, htl_k, hfl_k, hres_k, hdone_k⟩ := ih (Nat.le_of_succ_le hk_le)
    let st := k6AnaPrefix L skip ks off k; let lit := ks.arena[off + k]?.getD 0#32
    have hlit_mem : lit.toNat ∈ k6ClauseLits ks cid.toNat :=
      (k6_mem_clauseLits_iff hbd).mpr ⟨k, by omega, rfl⟩
    have hlit_lt : lit.toNat < 2 * st.nv.toNat := by rw [hpres_k.nv]; exact hwf.2.2.1 _ hlit_mem
    have hlit_ok : lit.toNat / 2 ≠ skip.toNat → st.vals[lit.toNat]? = some 2#32 ∧
        (st.lvlArr[lit.toNat / 2]?.getD 0#32 = st.lvl →
          ∃ j < idx, (st.trl[j]?.getD 0#32).toNat = lit.toNat ^^^ 1) := fun hne => by
      rw [hpres_k.vals, hpres_k.lvlArr, hpres_k.lvl, hpres_k.trl]; exact hlits _ hlit_mem hne
    have hvdec_st : ∃ v_dec < st.nv.toNat, st.lvlArr[v_dec]?.getD 0#32 = st.lvl := by
      rw [hpres_k.nv, hpres_k.lvlArr, hpres_k.lvl]; exact hvdec
    have hstep_eq : k6AnaPrefix L skip ks off (k + 1) = k6AnaLit L skip st lit := by
      change k6AnaLit L skip st (st.arena[off + k]?.getD 0#32) = k6AnaLit L skip st lit
      rw [hpres_k.arena]
    rw [hstep_eq]
    obtain ⟨hinv_s, hpres_s, hfl_s, hres_s⟩ :=
      k6AnaLit_preserves_anaInv hinv_k hvdec_st hlit_lt hlit_ok
    have htl_s := k6TailEq_trans htl_k (k6AnaLit_tailEq L skip st lit hlit_lt)
    refine ⟨hinv_s, k6AnaPreserved_trans hpres_k hpres_s, htl_s,
      fun v hv hnz => hfl_s v (by rw [hpres_k.nv]; exact hv) (hfl_k v hv hnz),
      fun x hx => hres_s x (hres_k x hx), fun m hm hne => ?_⟩
    by_cases hmk : m = k
    · subst hmk; have heff := k6AnaLit_effect_on_lit hinv_k hvdec_st hlit_lt hlit_ok hne
      rw [hpres_k.lvlArr] at heff; exact heff
    · have hprev := hdone_k m (by omega) hne; exact ⟨hprev.1, fun hnz => hres_s _ (hprev.2 hnz)⟩

private theorem k6AnaPrefix_entails {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    {idx : Nat} {cid skip : BitVec 32} (hinv : K6AnaInv L P ks idx)
    (hcid : cid.toNat < ks.nc.toNat)
    (hvdec : ∃ v_dec < ks.nv.toNat, ks.lvlArr[v_dec]?.getD 0#32 = ks.lvl)
    (hlits : ∀ l ∈ k6ClauseLits ks cid.toNat, l / 2 ≠ skip.toNat →
      ks.vals[l]? = some 2#32 ∧
      (ks.lvlArr[l / 2]?.getD 0#32 = ks.lvl →
        ∃ j < idx, (ks.trl[j]?.getD 0#32).toNat = l ^^^ 1))
    (hskip : skip ≠ 0xFFFFFFFF#32 →
      ∃ l ∈ k6ClauseLits ks cid.toNat, l / 2 = skip.toNat ∧
        (∀ l' ∈ k6ClauseLits ks cid.toNat, l' / 2 = skip.toNat → l' = l) ∧
        (ks.flags[skip.toNat]?.getD 0#32 &&& 2#32) ≠ 0#32 ∧
        ks.lvlArr[skip.toNat]?.getD 0#32 = ks.lvl ∧
        SemEntails P ((l ^^^ 1) :: k6ResolventLits ks idx)) :
    let ks' := k6AnaPrefix L skip ks (k6ClauseOff ks cid.toNat) (k6ClauseSize ks cid.toNat)
    K6AnaInv L P ks' idx ∧ K6AnaPreserved ks ks' ∧ K6TailEq L ks ks' ∧
    SemEntails P (k6ResolventLits ks' idx) ∧
    (∀ v < ks.nv.toNat, (ks.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32 →
      (ks'.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32) := by
  intro ks'; have hm := L.hmaxV; have hwf := hinv.cl_wf cid.toNat hcid
  have hbd : k6ClauseOff ks cid.toNat + k6ClauseSize ks cid.toNat ≤ ks.arena.length := by
    rw [hinv.shapes.arena_len]; have := hwf.2.1; have := hinv.alen_le; omega
  obtain ⟨hinv', hpres', htl', hfl', hres_sub, hdone⟩ :=
    k6AnaPrefix_properties hinv hcid hvdec hlits (k6ClauseSize ks cid.toNat) (Nat.le_refl _)
  have hlit_done : ∀ l ∈ k6ClauseLits ks cid.toNat, l / 2 ≠ skip.toNat →
      (ks.lvlArr[l / 2]?.getD 0#32 = 0#32 → SemEntails P [l ^^^ 1]) ∧
      (ks.lvlArr[l / 2]?.getD 0#32 ≠ 0#32 → l ∈ k6ResolventLits ks' idx) := fun l hl hne => by
    obtain ⟨k, hk, rfl⟩ := (k6_mem_clauseLits_iff hbd).mp hl; exact hdone k hk hne
  have hresolve : ∀ β, P β →
      (∃ l ∈ k6ClauseLits ks cid.toNat, l / 2 = skip.toNat ∧ (cnfClause [l]).Sat β) ∨
      (cnfClause (k6ResolventLits ks' idx)).Sat β := fun β hP => by
    obtain ⟨l, hl_mem, hlsat⟩ := (clause_sat_cnfClause_iff β _).mp (hwf.2.2.2 β hP)
    by_cases hlv : l / 2 = skip.toNat
    · exact Or.inl ⟨l, hl_mem, hlv, (sat_cnfClause_singleton β l).mpr hlsat⟩
    · by_cases h0 : ks.lvlArr[l / 2]?.getD 0#32 = 0#32
      · have hneg := (hlit_done l hl_mem hlv).1 h0 β hP
        rw [show (l ^^^ 1 : Nat) = litNeg l from rfl] at hneg
        exact absurd ((sat_cnfClause_singleton β l).mpr hlsat)
          ((sat_cnfClause_litNeg_iff β l).mp hneg)
      · exact Or.inr ((clause_sat_cnfClause_iff β _).mpr
          ⟨l, (hlit_done l hl_mem hlv).2 h0, hlsat⟩)
  refine ⟨hinv', hpres', htl', fun β hP => ?_, hfl'⟩
  by_cases hff : skip = 0xFFFFFFFF#32
  · rcases hresolve β hP with ⟨l, hl, hlv, _⟩ | hsat
    · exfalso; have hl_lt := hwf.2.2.1 l hl; have := hinv.nv_le
      rw [hff] at hlv; have : (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 := by decide
      omega
    · exact hsat
  · obtain ⟨p, _, _, hp_uniq, _, _, hent_p⟩ := hskip hff
    obtain ⟨x, hx_mem, hxsat⟩ := (clause_sat_cnfClause_iff β _).mp (hent_p β hP)
    rcases List.mem_cons.mp hx_mem with rfl | hx_old
    · rcases hresolve β hP with ⟨l, hl, hlv, hlsat⟩ | hsat
      · have hlp := hp_uniq l hl hlv; subst hlp
        exact absurd hlsat
          ((sat_cnfClause_litNeg_iff β l).mp ((sat_cnfClause_singleton β _).mpr hxsat))
      · exact hsat
    · exact (clause_sat_cnfClause_iff β _).mpr ⟨x, hres_sub x hx_old, hxsat⟩

/-! ## 2. `full_k6_ana_clause_wp` (`10/14`) -/

/-- `10/14`: Parametric `Func.wp` proof for `full_k6_ana_clause`. -/
theorem full_k6_ana_clause_wp (Γ : Env) :
    ∀ args m Q X, step13K6AnaClauseSpec args m Q X →
      Func.wp Γ full_k6_ana_clause_body args m Q X := by
  rintro ⟨kPtr, cid, skip_v, ⟨⟩⟩ m Q X ⟨L, P, ks, idx, R, hinv, hcid, hvdec, hlits, hskip,
    hm, hQ⟩
  have hm_v := L.hmaxV; have hac := L.hacap
  have hsh := hinv.shapes; have hnv := hinv.nv_le; have hnc := hinv.nc_le
  have hmv : ks.max_v = L.mv32 := hinv.max_v_eq
  have hcid_len : cid.toNat < szCl L := by unfold szCl; omega
  have hmA := k6Mem_to_amem hsh hm; clear hm
  let off := ks.clOff[cid.toNat]?.getD 0#32; let sz := ks.clSz[cid.toNat]?.getD 0#32
  have hwf := hinv.cl_wf cid.toNat hcid
  have hspan : off.toNat + sz.toNat ≤ ks.alen.toNat := hwf.2.1
  have hal := hinv.alen_le
  have hbd : k6ClauseOff ks cid.toNat + k6ClauseSize ks cid.toNat ≤ ks.arena.length := by
    rw [hsh.arena_len]; omega
  have hlit_lt : ∀ n < sz.toNat,
      (ks.arena[off.toNat + n]?.getD 0#32).toNat < 2 * ks.nv.toNat := fun n hn =>
    hwf.2.2.1 _ ((k6_mem_clauseLits_iff hbd).mpr ⟨n, hn, rfl⟩)
  c0_hsteps_nogrp; rw [hmv]; c0_hsteps_nogrp
  refine wp_while_state1 (proj := fun st : BitVec 32 × K6State => st.1)
    (fun st => sz.toNat - st.1.toNat)
    (fun st m' => st.1.toNat ≤ sz.toNat ∧ st.2 = k6AnaPrefix L skip_v ks off.toNat st.1.toNat ∧
      (K6MemA L kPtr st.2 ⋆ R) m') ?_ ?_
  · intro Lp hL; exact hL (0#32, ks) m ⟨Nat.zero_le _, rfl, hmA⟩
  · rintro Lp ⟨i, st⟩ m'' ⟨hi_le, hst, hm''⟩ ih
    dsimp only at hi_le hst hm'' ⊢
    c0_hsplit
    · have hi_lt : i.toNat < sz.toNat := by bv_omega
      have hi1 : (i + 1#32).toNat = i.toNat + 1 := by unfold dimacsBound at hac; bv_omega
      have hoi_cap : off.toNat + i.toNat < szAr L := by unfold szAr; omega
      have hoi_28 : off.toNat + i.toNat < 2 ^ 28 := by unfold dimacsBound at hac; omega
      have hoi_32 : off.toNat + i.toNat < 2 ^ 32 := by omega
      have hoi_eq : (off + i).toNat = off.toNat + i.toNat := by
        rw [BitVec.toNat_add, Nat.mod_eq_of_lt hoi_32]
      have hoi_mod : ((ks.clOff[cid.toNat]?.getD 0#32).toNat + i.toNat) % 2 ^ 32 =
          off.toNat + i.toNat := Nat.mod_eq_of_lt hoi_32
      have hoi_ar : (ks.clOff[cid.toNat]?.getD 0#32 + i).toNat < szAr L := by
        change (off + i).toNat < szAr L; rw [hoi_eq]; exact hoi_cap
      obtain ⟨_, _, _, _, _, _, hfr_eq⟩ := k6AnaPrefix_frame L skip_v ks off.toNat i.toNat
      rw [← hst] at hfr_eq
      have har : st.arena = ks.arena := by rw [hfr_eq]
      have hlv_eq : st.lvl = ks.lvl := by rw [hfr_eq]
      have hl := hlit_lt i.toNat hi_lt
      let l := ks.arena[off.toNat + i.toNat]?.getD 0#32
      have hl_st : st.arena[off.toNat + i.toNat]?.getD 0#32 = l := by rw [har]
      have hl_st_mod : st.arena[((ks.clOff[cid.toNat]?.getD 0#32).toNat + i.toNat) % 2 ^ 32]?.getD
          0#32 = l := by rw [hoi_mod]; exact hl_st
      have hl_st_add : st.arena[(ks.clOff[cid.toNat]?.getD 0#32 + i).toNat]?.getD 0#32 = l := by
        change st.arena[(off + i).toNat]?.getD 0#32 = l; rw [hoi_eq]; exact hl_st
      obtain ⟨hv_eq, hv_lt⟩ := k6_bv32_div2_lt hl
      have hv_mv : (l >>> 1).toNat < szV L := by unfold szV; dsimp only [l]; omega
      have hv_st_mv : (st.arena[off.toNat + i.toNat]?.getD 0#32 >>> 1).toNat < szV L := by
        rw [hl_st]; exact hv_mv
      have hv_st_mv' :
          (st.arena[(ks.clOff[cid.toNat]?.getD 0#32 + i).toNat]?.getD 0#32 >>> 1).toNat <
            szV L := by rw [hl_st_add]; exact hv_mv
      have hnext_eq : k6AnaPrefix L skip_v ks off.toNat (i.toNat + 1) = k6AnaLit L skip_v st l := by
        rw [hst]
        change k6AnaLit L skip_v (k6AnaPrefix L skip_v ks off.toNat i.toNat)
          ((k6AnaPrefix L skip_v ks off.toNat i.toNat).arena[off.toNat + i.toNat]?.getD 0#32) = _
        rw [← hst]; exact congrArg (k6AnaLit L skip_v st) hl_st
      have hsk_noop : ∀ (h1 : l >>> 1 = skip_v ∨ st.lvlArr[(l >>> 1).toNat]?.getD 0#32 = 0#32 ∨
          (st.flags[(l >>> 1).toNat]?.getD 0#32 &&& 2#32) ≠ 0#32),
          k6AnaLit L skip_v st l = st := by
        intro h1; unfold k6AnaLit; dsimp only
        rcases h1 with h | h | h
        · rw [k6a_ite_t h]
        · by_cases hs : l >>> 1 = skip_v
          · rw [k6a_ite_t hs]
          · rw [k6a_ite_f hs, k6a_ite_t h]
        · by_cases hs : l >>> 1 = skip_v
          · rw [k6a_ite_t hs]
          · by_cases hv : st.lvlArr[(l >>> 1).toNat]?.getD 0#32 = 0#32
            · rw [k6a_ite_f hs, k6a_ite_t hv]
            · rw [k6a_ite_f hs, k6a_ite_f hv, k6a_ite_f h]
      c0_hsteps_nogrp
      refine wp_join0 (fun m3 => (K6MemA L kPtr (k6AnaLit L skip_v st l) ⋆ R) m3) ?_ ?_
      · intro Jv m3 hm3; c0_hsteps!
        exact ih (i + 1#32, k6AnaLit L skip_v st l) m3 (by dsimp only; rw [hi1]; omega)
          ⟨by dsimp only; rw [hi1]; omega, by dsimp only; rw [hi1, hnext_eq], hm3⟩
      · intro Jv hJv; c0_hsplit
        · have hsk_ne : l >>> 1 ≠ skip_v := by rw [← hl_st_mod]; exact ‹_›
          c0_hsteps_nogrp
          refine wp_join0 (fun m3 => (K6MemA L kPtr (k6AnaLit L skip_v st l) ⋆ R) m3) ?_ ?_
          · intro Jf m3 hm3; c0_hsteps!; exact hJv m3 hm3
          · intro Jf hJf; try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
            c0_hsplit
            · have hv_nz : st.lvlArr[(l >>> 1).toNat]?.getD 0#32 ≠ 0#32 := by
                have h1 : 0 < (st.lvlArr[(st.arena[((ks.clOff[cid.toNat]?.getD 0#32).toNat +
                    i.toNat) % 2 ^ 32]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
                  have hlt := hc; rw [hl_st_mod] at hlt; bv_omega
                rw [hl_st_mod] at h1; rw [hv_eq]; intro hz; rw [hz] at h1; simp at h1
              have hl_st' := hl_st_mod
              c0_hsplit
              · have hfl0 : (st.flags[(l >>> 1).toNat]?.getD 0#32 &&& 2#32) = 0#32 := by
                  rw [← hl_st_mod]; exact ‹_›
                let fl' := st.flags[(l >>> 1).toNat]?.getD 0#32 ||| 2#32
                let st1 : K6State := { st with flags := st.flags.set (l >>> 1).toNat fl' }
                let st2 : K6State := if st1.nana.toNat < L.maxV then
                  { st1 with ana := st1.ana.set st1.nana.toNat (l >>> 1), nana := st1.nana + 1#32 }
                  else st1
                c0_hsteps_nogrp
                refine wp_join0 (fun m3 => (K6MemA L kPtr st2 ⋆ R) m3) ?_ ?_
                · intro Jna m3 hm3
                  have hkana_st2 : k6AnaLit L skip_v st l =
                      if st.lvlArr[(l >>> 1).toNat]?.getD 0#32 = st.lvl then
                        { st2 with openCnt := st2.openCnt + 1#32 }
                      else if st2.nkl.toNat < L.maxV then
                        { st2 with kl := st2.kl.set st2.nkl.toNat l, nkl := st2.nkl + 1#32 }
                      else st2 := by
                    unfold k6AnaLit; dsimp only
                    rw [k6a_ite_f hsk_ne, k6a_ite_f hv_nz, k6a_ite_t hfl0]
                  c0_hsteps!
                  · have htop : st.lvlArr[(l >>> 1).toNat]?.getD 0#32 = st.lvl := by
                      have h1 : st.lvlArr[(st.arena[((ks.clOff[cid.toNat]?.getD 0#32).toNat +
                          i.toNat) % 2 ^ 32]?.getD 0#32 >>> 1).toNat]?.getD 0#32 = ks.lvl := ‹_›
                      rw [hl_st_mod, ← hlv_eq] at h1; exact h1
                    refine hJf _ (Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ R) _) ?_) hm)
                    rw [hkana_st2, k6a_ite_t htop]; k6_ext
                  · have hntop : st.lvlArr[(l >>> 1).toNat]?.getD 0#32 ≠ st.lvl := by
                      rw [← hl_st_mod, hlv_eq]; assumption
                    have hnk_mv : st2.nkl.toNat < L.maxV := by bv_omega
                    have hnk_len : st2.nkl.toNat < szV L := by unfold szV; exact hnk_mv
                    refine hJf _ (Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ R) _) ?_) hm)
                    rw [hkana_st2, k6a_ite_f hntop, k6a_ite_t hnk_mv]; k6_ext; rw [hl_st_add]
                  · have hntop : st.lvlArr[(l >>> 1).toNat]?.getD 0#32 ≠ st.lvl := by
                      rw [← hl_st_mod, hlv_eq]; assumption
                    have hnk_ge : ¬ st2.nkl.toNat < L.maxV := by bv_omega
                    exact hJf _ ((by rw [hkana_st2, k6a_ite_f hntop, k6a_ite_f hnk_ge] :
                      st2 = k6AnaLit L skip_v st l) ▸ hm3)
                · intro Jna hJna
                  have hl_sr : l.toNat >>> 1 = (l >>> 1).toNat := by
                    rw [Nat.shiftRight_eq_div_pow, Nat.pow_one, hv_eq]
                  have hl_b1 : l >>> (1#32 : BitVec 32) = l >>> (1 : Nat) := by simp
                  c0_hsplit
                  · have hna_mv : st.nana.toNat < L.maxV := by
                      dsimp only [K6State.putArr] at *; bv_omega
                    have hna_len : st.nana.toNat < szV L := by unfold szV; exact hna_mv
                    c0_hsteps!
                    refine hJna _ (Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ R) _) ?_) hm)
                    dsimp only [st2, st1, fl']; rw [k6a_ite_t hna_mv]
                    k6_ext <;> simp only [hl_st_add] <;> rfl
                  · have hna_ge : ¬ st.nana.toNat < L.maxV := by
                      dsimp only [K6State.putArr] at *; bv_omega
                    c0_hsteps!
                    refine hJna _ (Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ R) _) ?_) hm)
                    dsimp only [st2, st1, fl']; rw [k6a_ite_f hna_ge]
                    k6_ext <;> simp only [hl_st_add] <;> rfl
              · have hfl_nz : (st.flags[(l >>> 1).toNat]?.getD 0#32 &&& 2#32) ≠ 0#32 := by
                  rw [← hl_st_mod]; exact ‹_›
                c0_hsteps!; exact hJf m'' ((hsk_noop (Or.inr (Or.inr hfl_nz))).symm ▸ hm'')
            · have hv0 : st.lvlArr[(l >>> 1).toNat]?.getD 0#32 = 0#32 := by
                have hle : (st.lvlArr[(st.arena[((ks.clOff[cid.toNat]?.getD 0#32).toNat +
                    i.toNat) % 2 ^ 32]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
                  have hlt := hc; rw [hl_st_mod] at hlt; bv_omega
                rw [hl_st_mod, ← hv_eq] at hle; exact BitVec.eq_of_toNat_eq hle
              c0_hsteps!; exact hJf m'' ((hsk_noop (Or.inr (Or.inl hv0))).symm ▸ hm'')
        · have hsk_eq : l >>> 1 = skip_v := by rw [← hl_st_mod]; exact ‹_›
          c0_hsteps!; exact hJv m'' ((hsk_noop (Or.inl hsk_eq)).symm ▸ hm'')
    · have hi_eq : i.toNat = sz.toNat := by dsimp only [sz] at hi_le ⊢; bv_omega
      c0_hsteps!; obtain ⟨_, hmFin⟩ := k6MemA_to_mem hm''
      have hent := k6AnaPrefix_entails hinv hcid hvdec hlits hskip
      have hst_fin : st = k6AnaPrefix L skip_v ks (k6ClauseOff ks cid.toNat)
          (k6ClauseSize ks cid.toNat) := by rw [hst, hi_eq]; rfl
      rw [hst_fin] at hmFin
      exact hQ _ _ hent.1 hent.2.1 hent.2.2.1 hent.2.2.2.1 hent.2.2.2.2 hmFin

end LeanQbe.T.Examples.Kissat.Proof.Kitten
end
