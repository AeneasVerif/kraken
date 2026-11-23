module

public import LeanQbe.T.Examples.Kissat.FullM6SweepProofKitten2a

/-!
# Kissat `D-Full` M6 — Scaled `K6` Sub-Solver Proofs (`Part 2b`, `13/39` cumulative)

Parametric `(Γ : Env)` `Func.wp` proofs for `2/39` owned functions (`13/39` cumulative):
- `12/39`: `full_k6_ana_clause_wp`
- `13/39`: `full_k6_analyze_wp`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6Sweep

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4Sweep
open Kraken.Bedrock2.Test

open K6MemATactics K6PtrTactics
open scoped K6MemATactics K6PtrTactics

section DynKlMem
@[scoped bv_c0] private theorem k6b_sext_1 :
    BitVec.signExtend 64 1#32 = BitVec.ofNat 64 1 := rfl
@[scoped c0_load] private theorem load_k6_kl_dyn_z0 {L : K6Layout} {kPtr : BitVec 64}
    {ks : K6State} {R : Mem 64 → Prop} {m : Mem 64} (hm : (K6MemA L kPtr ks ⋆ R) m) :
    loadVal m i32
      ((kPtr + ((32 : BitVec 32) + (8 : BitVec 32) * L.mv32).setWidth 64 * 4) +
        BitVec.ofNat 64 0 * 4) = some (ks.kl[0]?.getD 0#32) := by
  rw [k6_ptr_kl L kPtr]; exact load_k6_kl0 hm
@[scoped c0_store] private theorem store_k6_kl_dyn_z0 {L : K6Layout} {kPtr : BitVec 64}
    {ks : K6State} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32)
    (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32
      ((kPtr + ((32 : BitVec 32) + (8 : BitVec 32) * L.mv32).setWidth 64 * 4) +
        BitVec.ofNat 64 0 * 4) ∧
      (K6MemA L kPtr (ks.putArr .kl 0 v) ⋆ R)
        (storeMem m i32
          ((kPtr + ((32 : BitVec 32) + (8 : BitVec 32) * L.mv32).setWidth 64 * 4) +
            BitVec.ofNat 64 0 * 4) v) := by
  rw [k6_ptr_kl L kPtr]; exact store_k6_kl0 v hm
@[scoped c0_load] private theorem load_k6_kl_dyn_z1 {L : K6Layout} {kPtr : BitVec 64}
    {ks : K6State} {R : Mem 64 → Prop} {m : Mem 64} (hm : (K6MemA L kPtr ks ⋆ R) m) :
    loadVal m i32
      ((kPtr + ((32 : BitVec 32) + (8 : BitVec 32) * L.mv32).setWidth 64 * 4) +
        BitVec.ofNat 64 1 * 4) = some (ks.kl[1]?.getD 0#32) := by
  rw [k6_ptr_kl L kPtr]; exact load_k6_kl1 hm
@[scoped c0_store] private theorem store_k6_kl_dyn_z1 {L : K6Layout} {kPtr : BitVec 64}
    {ks : K6State} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32)
    (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32
      ((kPtr + ((32 : BitVec 32) + (8 : BitVec 32) * L.mv32).setWidth 64 * 4) +
        BitVec.ofNat 64 1 * 4) ∧
      (K6MemA L kPtr (ks.putArr .kl 1 v) ⋆ R)
        (storeMem m i32
          ((kPtr + ((32 : BitVec 32) + (8 : BitVec 32) * L.mv32).setWidth 64 * 4) +
            BitVec.ofNat 64 1 * 4) v) := by
  rw [k6_ptr_kl L kPtr]; exact store_k6_kl1 v hm
end DynKlMem

/-! ## 1. Pure Helpers & `full_k6_ana_clause_wp` (`12/39`) -/

private theorem k6a_ite_t {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

private theorem k6a_ite_f {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬c) :
    (if c then a else b) = b := by simp [h]

private theorem k6a_fl_or2_and2_nz (x : BitVec 32) : ((x ||| 2#32) &&& 2#32) ≠ 0#32 := by
  intro h; have h1 := congrArg (fun b : BitVec 32 => b[1]) h; revert h1; simp

private theorem k6a_fl_andnot2_and2_zero (x : BitVec 32) :
    ((x &&& ~~~2#32) &&& 2#32) = 0#32 := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]
  by_cases h1 : i = 1
  · subst h1; simp
  · have h2 : (2#32 : BitVec 32)[i] = false := by revert i hi h1; decide
    simp [h2]

private theorem k6a_xor1_div2 (l : Nat) : (l ^^^ 1) / 2 = l / 2 := by
  rcases k6_nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;> omega

private theorem k6a_semEntails_subset {P : (Nat → Bool) → Prop} {c1 c2 : List Nat}
    (hsub : ∀ x ∈ c1, x ∈ c2) (h : SemEntails P c1) : SemEntails P c2 := fun β hP => by
  obtain ⟨x, hx, hxs⟩ := (clause_sat_cnfClause_iff β _).mp (h β hP)
  exact (clause_sat_cnfClause_iff β _).mpr ⟨x, hsub x hx, hxs⟩

private theorem k6a_setQueue_preserves_inv {L : K6Layout} {P : (Nat → Bool) → Prop}
    {ks : K6State} (hinv : K6Inv L P ks) {qf ql qs qst : BitVec 32}
    {qp qn qsa : List (BitVec 32)}
    (hqp : qp.length = L.maxV) (hqn : qn.length = L.maxV) (hqsa : qsa.length = L.maxV) :
    let ks' : K6State :=
      { ks with qfirst := qf, qlast := ql, qsearch := qs, qstamp := qst,
                qprev := qp, qnext := qn, qstampArr := qsa }
    K6Inv L P ks' :=
  ⟨{ hinv.shapes with qprev_len := hqp, qnext_len := hqn, qstampArr_len := hqsa },
   k6ClausesOk_cast hinv.clauses rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl,
   hinv.watches,
   k6BaseAssignOk_cast hinv.assign rfl rfl rfl rfl rfl rfl rfl rfl rfl,
   hinv.reasons⟩

private theorem k6a_filter_length_flip_one {α : Type} [DecidableEq α]
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

private theorem k6a_filterMap_congr {α β : Type} {f g : α → Option β} {xs : List α}
    (h : ∀ x ∈ xs, f x = g x) : xs.filterMap f = xs.filterMap g := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    simp only [List.filterMap_cons, h x List.mem_cons_self]
    rw [ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

private theorem k6a_mem_resolvent_iff {ks : K6State} {idx l : Nat} :
    l ∈ k6ResolventLits ks idx ↔
      (∃ j < idx, (ks.trl[j]?.getD 0#32).toNat = l ^^^ 1 ∧
        ks.lvlArr[(l ^^^ 1) / 2]?.getD 0#32 = ks.lvl ∧
        (ks.flags[(l ^^^ 1) / 2]?.getD 0#32 &&& 2#32) ≠ 0#32) ∨
      (∃ i, 1 ≤ i ∧ i < min ks.nkl.toNat ks.kl.length ∧ (ks.kl[i]?.getD 0#32).toNat = l) := by
  unfold k6ResolventLits
  rw [List.mem_append, List.mem_filterMap, List.mem_map]
  constructor
  · rintro (⟨j, hj, hif⟩ | ⟨b, hb, rfl⟩)
    · left; rw [List.mem_range] at hj; dsimp only at hif
      split at hif
      · rename_i hc; simp only [Option.some.injEq] at hif
        have hx : (ks.trl[j]?.getD 0#32).toNat = l ^^^ 1 := by
          rw [← hif, k6_nat_xor1_xor1]
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
      rw [List.mem_iff_getElem]
      refine ⟨i - 1, by simp [List.length_take]; omega, ?_⟩
      simp only [List.getElem_drop, List.getElem_take, show 1 + (i - 1) = i by omega]

private theorem k6AnaPreserved_refl (ks : K6State) : K6AnaPreserved ks ks :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem k6AnaPreserved_trans {ks1 ks2 ks3 : K6State}
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

private theorem k6a_inv_of_ana_clean {L : K6Layout} {P : (Nat → Bool) → Prop} {ks st : K6State}
    (hinv : K6Inv L P ks) (hsync : K6TrailSynced ks) (hsh : st.ShapesOk L)
    (hp : K6AnaPreserved ks st) (hnkl : st.nkl.toNat ≤ L.maxV) (hnana : st.nana.toNat ≤ L.maxV)
    (hfl : ∀ v < st.nv.toNat, (st.flags[v]?.getD 0#32 &&& 2#32) = 0#32) :
    K6Inv L P st ∧ K6TrailSynced st := by
  have hcl_eq : ∀ c, k6ClauseOff st c = k6ClauseOff ks c ∧
      k6ClauseSize st c = k6ClauseSize ks c ∧ k6ClauseLits st c = k6ClauseLits ks c := fun c =>
    ⟨by simp [k6ClauseOff, hp.clOff], by simp [k6ClauseSize, hp.clSz],
     by simp [k6ClauseLits, k6ClauseOff, k6ClauseSize, hp.clOff, hp.clSz, hp.arena]⟩
  have hcl : K6ClausesOk L P st :=
    ⟨by rw [hp.acap]; exact hinv.clauses.acap_eq,
     by rw [hp.max_v]; exact hinv.clauses.max_v_eq,
     by rw [hp.max_orig]; exact hinv.clauses.max_orig_eq,
     by rw [hp.max_cl]; exact hinv.clauses.max_cl_eq,
     by rw [hp.nv]; exact hinv.clauses.nv_le,
     by rw [hp.nc]; exact hinv.clauses.nc_le,
     by rw [hp.alen]; exact hinv.clauses.alen_le,
     by rw [hp.nassump]; exact hinv.clauses.nassump_le,
     hnkl, hnana,
     fun c hc => by
       rw [hp.nc] at hc; have hw := hinv.clauses.cl_wf c hc; have he := hcl_eq c
       rw [he.1, he.2.1, he.2.2, hp.alen, hp.nv]; exact hw,
     fun c1 c2 h12 hc2 => by
       rw [hp.nc] at hc2; rw [(hcl_eq c1).1, (hcl_eq c1).2.1, (hcl_eq c2).1]
       exact hinv.clauses.cl_mono c1 c2 h12 hc2,
     by rw [hp.incons]; exact hinv.clauses.incons_ok,
     fun i hi => by rw [hp.nassump] at hi; rw [hp.assump, hp.nv]; exact hinv.clauses.assump_ok i hi,
     hfl⟩
  have hba := k6BaseAssignOk_cast hinv.assign hp.nv hp.lvl hp.prop hp.trl_end hp.unass hp.lvlArr
    hp.rsn hp.trl hp.vals
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
  have hsync' : K6TrailSynced st := fun i hi => by
    rw [hp.trl_end] at hi; rw [hp.trl, hp.vals]; exact hsync i hi
  exact ⟨⟨hsh, hcl, hw, hba, hrsn⟩, hsync'⟩

/-- Pure model of one loop iteration of `full_k6_ana_clause`. -/
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

/-- State after the first `n` iterations of `full_k6_ana_clause`. -/
private def k6AnaPrefix (L : K6Layout) (skip : BitVec 32) (ks0 : K6State) (off : Nat) :
    Nat → K6State
  | 0 => ks0
  | n + 1 =>
    let st := k6AnaPrefix L skip ks0 off n
    k6AnaLit L skip st (st.arena[off + n]?.getD 0#32)

private theorem k6AnaLit_frame (L : K6Layout) (skip : BitVec 32) (ks : K6State) (l : BitVec 32) :
    ∃ fl an na op kl nk, k6AnaLit L skip ks l =
      { ks with flags := fl, ana := an, nana := na, openCnt := op, kl := kl, nkl := nk } := by
  have hself : ∃ fl an na op kl nk, ks =
      { ks with flags := fl, ana := an, nana := na, openCnt := op, kl := kl, nkl := nk } :=
    ⟨ks.flags, ks.ana, ks.nana, ks.openCnt, ks.kl, ks.nkl, by cases ks; rfl⟩
  unfold k6AnaLit; dsimp only
  by_cases h1 : l >>> 1 = skip
  · rw [k6a_ite_t h1]; exact hself
  rw [k6a_ite_f h1]
  by_cases h2 : ks.lvlArr[(l >>> 1).toNat]?.getD 0#32 = 0#32
  · rw [k6a_ite_t h2]; exact hself
  rw [k6a_ite_f h2]
  by_cases h3 : (ks.flags[(l >>> 1).toNat]?.getD 0#32 &&& 2#32) = 0#32
  · rw [k6a_ite_t h3]
    let fl' := ks.flags[(l >>> 1).toNat]?.getD 0#32 ||| 2#32
    let ks1 : K6State := { ks with flags := ks.flags.set (l >>> 1).toNat fl' }
    let ks2 : K6State := if ks1.nana.toNat < L.maxV then
        { ks1 with ana := ks1.ana.set ks1.nana.toNat (l >>> 1), nana := ks1.nana + 1#32 }
        else ks1
    have hks2 : ∃ an na, ks2 = { ks with flags := ks.flags.set (l >>> 1).toNat fl',
                                         ana := an, nana := na } := by
      dsimp only [ks2, ks1]
      by_cases ha : ks.nana.toNat < L.maxV
      · rw [k6a_ite_t ha]; exact ⟨_, _, rfl⟩
      · rw [k6a_ite_f ha]; exact ⟨ks.ana, ks.nana, rfl⟩
    obtain ⟨an, na, h2eq⟩ := hks2
    change ∃ fl an na op kl nk,
      (if ks.lvlArr[(l >>> 1).toNat]?.getD 0#32 = ks.lvl then
        { ks2 with openCnt := ks2.openCnt + 1#32 }
      else if ks2.nkl.toNat < L.maxV then
        { ks2 with kl := ks2.kl.set ks2.nkl.toNat l, nkl := ks2.nkl + 1#32 }
      else ks2) = _
    rw [h2eq]
    by_cases ht : ks.lvlArr[(l >>> 1).toNat]?.getD 0#32 = ks.lvl
    · rw [k6a_ite_t ht]; exact ⟨_, an, na, _, _, _, rfl⟩
    · rw [k6a_ite_f ht]
      by_cases hk : ks.nkl.toNat < L.maxV
      · rw [k6a_ite_t hk]; exact ⟨_, an, na, _, _, _, rfl⟩
      · rw [k6a_ite_f hk]; exact ⟨_, an, na, _, _, _, rfl⟩
  · rw [k6a_ite_f h3]; exact hself

private theorem k6AnaPrefix_frame (L : K6Layout) (skip : BitVec 32) (ks0 : K6State)
    (off n : Nat) :
    ∃ fl an na op kl nk, k6AnaPrefix L skip ks0 off n =
      { ks0 with flags := fl, ana := an, nana := na, openCnt := op, kl := kl, nkl := nk } := by
  induction n with
  | zero =>
    exact ⟨ks0.flags, ks0.ana, ks0.nana, ks0.openCnt, ks0.kl, ks0.nkl, by cases ks0; rfl⟩
  | succ k ih =>
    obtain ⟨_, _, _, _, _, _, h1⟩ := ih
    dsimp only [k6AnaPrefix]
    obtain ⟨fl2, an2, na2, op2, kl2, nk2, h2⟩ := k6AnaLit_frame L skip _ _
    rw [h2, h1]; exact ⟨fl2, an2, na2, op2, kl2, nk2, rfl⟩

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
      have hfl_nz := (hinv.flags_seen (l >>> 1).toNat hv_lt).mpr ⟨i, by omega, by
        rw [List.getElem?_eq_getElem (by omega : i < ks.ana.length), Option.getD_some, hget, hbeq]⟩
      exact hfl_nz hfl0
    have hana_take_len : ((ks.ana.take ks.nana.toNat).map BitVec.toNat).length = ks.nana.toNat := by
      rw [List.length_map, List.length_take, hsh.ana_len]; have := hinv.nana_le; omega
    have hnana_lt_nv : ks.nana.toNat < ks.nv.toNat := by
      have hnd : ((l >>> 1).toNat :: (ks.ana.take ks.nana.toNat).map BitVec.toNat).Nodup :=
        List.nodup_cons.mpr ⟨hv_not_ana, hinv.ana_nodup⟩
      have hlt_all : ∀ x ∈ (l >>> 1).toNat :: (ks.ana.take ks.nana.toNat).map BitVec.toNat,
          x < ks.nv.toNat := by
        intro x hx; rcases List.mem_cons.mp hx with rfl | hx'
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
    let v := (l >>> 1).toNat
    let fl := ks.flags[v]?.getD 0#32
    let ks1 : K6State := { ks with flags := ks.flags.set v (fl ||| 2#32) }
    let ks2 : K6State :=
      { ks1 with ana := ks1.ana.set ks1.nana.toNat (l >>> 1), nana := ks1.nana + 1#32 }
    have hks2_ite : (if ks1.nana.toNat < L.maxV then
        { ks1 with ana := ks1.ana.set ks1.nana.toNat (l >>> 1), nana := ks1.nana + 1#32 }
        else ks1) = ks2 := k6a_ite_t hnana_mv
    have hks2_body : (let ks1_0 : K6State := { ks with flags := ks.flags.set v (fl ||| 2#32) }
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
        else ks2) := by dsimp only; rw [hks2_ite]
    change K6AnaInv L P _ idx ∧ K6AnaPreserved ks _ ∧ _
    rw [hks2_body]
    have hfl_len : v < ks.flags.length := by rw [hsh.flags_len]; exact hv_mv
    have hana_len : ks.nana.toNat < ks.ana.length := by rw [hsh.ana_len]; exact hnana_mv
    have hfl_set_self : (ks2.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32 := by
      change ((ks.flags.set v (fl ||| 2#32))[v]?.getD 0#32 &&& 2#32) ≠ 0#32
      rw [List.getElem?_set_self hfl_len, Option.getD_some]; exact k6a_fl_or2_and2_nz fl
    have hfl_set_ne : ∀ u, u ≠ v → ks2.flags[u]? = ks.flags[u]? := fun u hu =>
      List.getElem?_set_ne (Ne.symm hu)
    have hfl_mono : ∀ u < ks.nv.toNat,
        (ks.flags[u]?.getD 0#32 &&& 2#32) ≠ 0#32 → (ks2.flags[u]?.getD 0#32 &&& 2#32) ≠ 0#32 := by
      intro u _ hnz; by_cases huv : u = v
      · subst huv; exact hfl_set_self
      · rwa [hfl_set_ne u huv]
    have hsh2 : ks2.ShapesOk L :=
      ((hsh.putArr .flags v (fl ||| 2#32)).putArr .ana ks.nana.toNat (l >>> 1)).putHdr .nana
        (ks.nana + 1#32)
    have hana_take2 : (ks2.ana.take ks2.nana.toNat).map BitVec.toNat =
        (ks.ana.take ks.nana.toNat).map BitVec.toNat ++ [v] := by
      change ((ks.ana.set ks.nana.toNat (l >>> 1)).take (ks.nana + 1#32).toNat).map BitVec.toNat = _
      rw [hnana1, List.take_add_one, List.map_append, List.take_set_of_le (Nat.le_refl _),
        List.getElem?_set_self hana_len]
      simp [v]
    have hana_nodup2 : ((ks2.ana.take ks2.nana.toNat).map BitVec.toNat).Nodup := by
      rw [hana_take2, List.nodup_append]
      exact ⟨hinv.ana_nodup, by simp, fun x hx y hy heq => by
        rw [List.mem_singleton] at hy; subst hy; subst heq; exact hv_not_ana hx⟩
    have hana_lt2 : ∀ i < ks2.nana.toNat, (ks2.ana[i]?.getD 0#32).toNat < ks2.nv.toNat := by
      intro i hi; change i < (ks.nana + 1#32).toNat at hi; rw [hnana1] at hi
      by_cases hie : i = ks.nana.toNat
      · subst hie; change ((ks.ana.set ks.nana.toNat (l >>> 1))[ks.nana.toNat]?.getD 0#32).toNat < _
        rw [List.getElem?_set_self hana_len, Option.getD_some]; exact hv_lt
      · change ((ks.ana.set ks.nana.toNat (l >>> 1))[i]?.getD 0#32).toNat < ks.nv.toNat
        rw [List.getElem?_set_ne (Ne.symm hie)]; exact hinv.ana_lt i (by omega)
    have hflags_seen2 : ∀ u < ks2.nv.toNat,
        ((ks2.flags[u]?.getD 0#32 &&& 2#32) ≠ 0#32) ↔
          ∃ i < ks2.nana.toNat, (ks2.ana[i]?.getD 0#32).toNat = u := by
      intro u hu
      change (ks2.flags[u]?.getD 0#32 &&& 2#32) ≠ 0#32 ↔
        ∃ i < (ks.nana + 1#32).toNat, ((ks.ana.set ks.nana.toNat (l >>> 1))[i]?.getD 0#32).toNat = u
      rw [hnana1]
      by_cases huv : u = v
      · subst huv; refine ⟨fun _ => ⟨ks.nana.toNat, by omega, by
          rw [List.getElem?_set_self hana_len, Option.getD_some]⟩, fun _ => hfl_set_self⟩
      · rw [hfl_set_ne u huv, hinv.flags_seen u hu]
        constructor
        · rintro ⟨i, hi, heq⟩; exact ⟨i, by omega, by rwa [List.getElem?_set_ne (by omega)]⟩
        · rintro ⟨i, hi, heq⟩; by_cases hie : i = ks.nana.toNat
          · subst hie; rw [List.getElem?_set_self hana_len, Option.getD_some] at heq
            exact absurd heq.symm huv
          · rw [List.getElem?_set_ne (Ne.symm hie)] at heq; exact ⟨i, by omega, heq⟩
    have hnkl_count2 : ∀ u < ks2.nv.toNat,
        (ks2.flags[u]?.getD 0#32 &&& 2#32) ≠ 0#32 → 0 < (ks2.lvlArr[u]?.getD 0#32).toNat := by
      intro u hu hnz; by_cases huv : u = v
      · subst huv; exact Nat.pos_of_ne_zero fun hz => hvlvl0 (BitVec.eq_of_toNat_eq hz)
      · rw [hfl_set_ne u huv] at hnz; exact hinv.nkl_count u hu hnz
    have hseen_trl2 : ∀ u < ks2.nv.toNat,
        (ks2.flags[u]?.getD 0#32 &&& 2#32) ≠ 0#32 → ks2.lvlArr[u]?.getD 0#32 = ks2.lvl →
        ∃ j < ks2.trl_end.toNat, (ks2.trl[j]?.getD 0#32).toNat / 2 = u := by
      intro u hu hnz hlvl; by_cases huv : u = v
      · subst huv
        obtain ⟨j0, hj0_idx, hj0_eq⟩ := hl_top_trl (by rw [← hv_eq]; exact hlvl)
        refine ⟨j0, Nat.lt_of_lt_of_le hj0_idx hinv.idx_le, ?_⟩
        change (ks.trl[j0]?.getD 0#32).toNat / 2 = v; rw [hj0_eq, k6a_xor1_div2]; exact hv_eq.symm
      · rw [hfl_set_ne u huv] at hnz; exact hinv.seen_in_trl u hu hnz hlvl
    have hvlvl_le := hinv.assign.trl_lvl_le v hv_lt
    by_cases htop : ks.lvlArr[v]?.getD 0#32 = ks.lvl
    · rw [k6a_ite_t htop]
      obtain ⟨j0, hj0_idx, hj0_eq⟩ := hl_top_trl (by rw [← hv_eq]; exact htop)
      have hj0_te : j0 < ks.trl_end.toNat := Nat.lt_of_lt_of_le hj0_idx hinv.idx_le
      have hj0_var : (ks.trl[j0]?.getD 0#32).toNat / 2 = v := by
        rw [hj0_eq, k6a_xor1_div2]; exact hv_eq.symm
      let ks3 : K6State := { ks2 with openCnt := ks2.openCnt + 1#32 }
      have hfilter_succ :
          ((List.range idx).filter fun j =>
            let u := (ks3.trl[j]?.getD 0#32).toNat / 2
            decide (ks3.lvlArr[u]?.getD 0#32 = ks3.lvl ∧
              (ks3.flags[u]?.getD 0#32 &&& 2#32) ≠ 0#32)).length =
          ((List.range idx).filter fun j =>
            let u := (ks.trl[j]?.getD 0#32).toNat / 2
            decide (ks.lvlArr[u]?.getD 0#32 = ks.lvl ∧
              (ks.flags[u]?.getD 0#32 &&& 2#32) ≠ 0#32)).length + 1 := by
        refine k6a_filter_length_flip_one List.nodup_range (List.mem_range.mpr hj0_idx) ?_ ?_ ?_
        · simp only [decide_eq_false_iff_not]; rw [hj0_var]; exact fun h => h.2 hfl0
        · simp only [decide_eq_true_eq]
          exact ⟨by change ks.lvlArr[(ks.trl[j0]?.getD 0#32).toNat / 2]?.getD 0#32 = ks.lvl
                    rw [hj0_var]; exact htop,
                 by change (ks2.flags[(ks.trl[j0]?.getD 0#32).toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32
                    rw [hj0_var]; exact hfl_set_self⟩
        · intro j hj hne; rw [List.mem_range] at hj
          have hvar_ne : (ks.trl[j]?.getD 0#32).toNat / 2 ≠ v := by
            rw [← hj0_var]
            exact k6_trl_nodup_var_ne hsh hnv hinv.assign (Nat.lt_of_lt_of_le hj hinv.idx_le)
              hj0_te hne
          change decide (ks.lvlArr[(ks.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32 = ks.lvl ∧
            (ks2.flags[(ks.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32) = _
          rw [hfl_set_ne _ hvar_ne]
      have hop_le : ks.openCnt.toNat ≤ idx := by
        rw [hinv.open_eq]; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
      have hop1 : (ks.openCnt + 1#32).toNat = ks.openCnt.toNat + 1 := by
        have := hinv.idx_le; have := hinv.assign.trl_end_le; bv_omega
      have hinv3 : K6AnaInv L P ks3 idx :=
        ⟨hsh2.putHdr .openCnt (ks2.openCnt + 1#32), hinv.acap_eq, hinv.max_v_eq, hinv.max_orig_eq,
         hinv.max_cl_eq, hinv.nv_le, hinv.nc_le, hinv.alen_le, hinv.nassump_le, hinv.lvl_pos,
         hinv.idx_le, hinv.cl_wf, hinv.cl_mono, hinv.incons_ok, hinv.assump_ok, hinv.watches,
         k6BaseAssignOk_cast hinv.assign rfl rfl rfl rfl rfl rfl rfl rfl rfl, hinv.synced,
         hinv.reasons, hinv.nkl_pos, hinv.nkl_le,
         by change (ks.nana + 1#32).toNat ≤ ks.nv.toNat; rw [hnana1]; omega,
         hana_nodup2, hana_lt2, hflags_seen2,
         fun i hi1 hi2 => by
           have hk := hinv.kl_nonTop i hi1 hi2
           exact ⟨hk.1, hfl_mono _ (by dsimp only [ks3, ks2, ks1] at *; omega) hk.2.1, hk.2.2⟩,
         fun u hu hnz hlt_lv => by
           by_cases huv : u = v
           · subst huv; change (ks.lvlArr[v]?.getD 0#32).toNat < ks.lvl.toNat at hlt_lv
             rw [htop] at hlt_lv; omega
           · rw [hfl_set_ne u huv] at hnz; exact hinv.kl_injective u hu hnz hlt_lv,
         hnkl_count2, hinv.kl_nodup,
         by change (ks.openCnt + 1#32).toNat = _; rw [hop1, hinv.open_eq, ← hfilter_succ],
         hseen_trl2⟩
      refine ⟨hinv3, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hfl_mono, fun x hx => ?_⟩
      rw [k6a_mem_resolvent_iff] at hx ⊢
      rcases hx with ⟨j, hj, htrl, hlvl, hfl⟩ | hr
      · left
        have hx_lt : (x ^^^ 1) / 2 < ks.nv.toNat := by
          have hmem := k6_mem_trailLits_of_lt (Nat.lt_of_lt_of_le hj hinv.idx_le)
            (by rw [hsh.trl_len]; have := hinv.assign.trl_end_le; omega)
          have hlt := hinv.assign.trl_lt _ hmem; rw [htrl] at hlt; omega
        exact ⟨j, hj, htrl, hlvl, hfl_mono _ hx_lt hfl⟩
      · exact Or.inr hr
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
            Option.getD_some]
          congr 2; omega
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
      let ks3 : K6State := { ks2 with kl := ks2.kl.set ks2.nkl.toNat l, nkl := ks2.nkl + 1#32 }
      have hks3_ite : (if ks2.nkl.toNat < L.maxV then
          { ks2 with kl := ks2.kl.set ks2.nkl.toNat l, nkl := ks2.nkl + 1#32 }
          else ks2) = ks3 := k6a_ite_t hnkl_mv
      rw [hks3_ite]
      have hkl_take3 : (((ks3.kl.take ks3.nkl.toNat).drop 1).map (fun x => x.toNat / 2)) =
          klVars ++ [v] := by
        change (((ks.kl.set ks.nkl.toNat l).take (ks.nkl + 1#32).toNat).drop 1).map
          (fun x => x.toNat / 2) = _
        rw [hnkl1, List.take_add_one, List.take_set_of_le (Nat.le_refl _),
          List.getElem?_set_self hkl_len]
        have htk_len : 1 ≤ (ks.kl.take ks.nkl.toNat).length := by
          rw [List.length_take, hsh.kl_len]; have := hinv.nkl_pos; omega
        rw [Option.toList_some, List.drop_append_of_le_length htk_len, List.map_append]
        simp [klVars, v, hv_eq]
      have hkl_nodup3 : (((ks3.kl.take ks3.nkl.toNat).drop 1).map
          (fun x => x.toNat / 2)).Nodup := by
        rw [hkl_take3, List.nodup_append]
        exact ⟨hinv.kl_nodup, by simp, fun x hx y hy heq => by
          rw [List.mem_singleton] at hy; subst hy; subst heq; exact hv_not_kl hx⟩
      have hfilter_eq :
          ((List.range idx).filter fun j =>
            let u := (ks3.trl[j]?.getD 0#32).toNat / 2
            decide (ks3.lvlArr[u]?.getD 0#32 = ks3.lvl ∧
              (ks3.flags[u]?.getD 0#32 &&& 2#32) ≠ 0#32)) =
          ((List.range idx).filter fun j =>
            let u := (ks.trl[j]?.getD 0#32).toNat / 2
            decide (ks.lvlArr[u]?.getD 0#32 = ks.lvl ∧
              (ks.flags[u]?.getD 0#32 &&& 2#32) ≠ 0#32)) := by
        refine List.filter_congr fun j _ => ?_
        by_cases huv : (ks.trl[j]?.getD 0#32).toNat / 2 = v
        · change decide (ks.lvlArr[(ks.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32 = ks.lvl ∧ _) =
            decide (ks.lvlArr[(ks.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32 = ks.lvl ∧ _)
          rw [huv]; simp [htop]
        · change decide (ks.lvlArr[(ks.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32 = ks.lvl ∧
            (ks2.flags[(ks.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32) = _
          rw [hfl_set_ne _ huv]
      have hinv3 : K6AnaInv L P ks3 idx :=
        ⟨(hsh2.putArr .kl ks.nkl.toNat l).putHdr .nkl (ks.nkl + 1#32), hinv.acap_eq,
         hinv.max_v_eq, hinv.max_orig_eq, hinv.max_cl_eq, hinv.nv_le, hinv.nc_le, hinv.alen_le,
         hinv.nassump_le, hinv.lvl_pos, hinv.idx_le, hinv.cl_wf, hinv.cl_mono, hinv.incons_ok,
         hinv.assump_ok, hinv.watches,
         k6BaseAssignOk_cast hinv.assign rfl rfl rfl rfl rfl rfl rfl rfl rfl, hinv.synced,
         hinv.reasons, by change 1 ≤ (ks.nkl + 1#32).toNat; rw [hnkl1]; omega,
         by change (ks.nkl + 1#32).toNat ≤ ks.nv.toNat; rw [hnkl1]; omega,
         by change (ks.nana + 1#32).toNat ≤ ks.nv.toNat; rw [hnana1]; omega,
         hana_nodup2, hana_lt2, hflags_seen2,
         fun i hi1 hi2 => by
           change i < (ks.nkl + 1#32).toNat at hi2; rw [hnkl1] at hi2
           by_cases hie : i = ks.nkl.toNat
           · subst hie
             change let x := ((ks.kl.set ks.nkl.toNat l)[ks.nkl.toNat]?.getD 0#32).toNat; _
             rw [List.getElem?_set_self hkl_len, Option.getD_some]
             refine ⟨hl_lt, ?_, ?_, ?_, hl_val2⟩
             · rw [← hv_eq]; exact hfl_set_self
             · rw [← hv_eq]; exact Nat.pos_of_ne_zero fun hz => hvlvl0 (BitVec.eq_of_toNat_eq hz)
             · rw [← hv_eq]; exact hvlvl_lt
           · change let x := ((ks.kl.set ks.nkl.toNat l)[i]?.getD 0#32).toNat; _
             rw [List.getElem?_set_ne (Ne.symm hie)]
             have hk := hinv.kl_nonTop i hi1 (by omega)
             exact ⟨hk.1, hfl_mono _ (by omega) hk.2.1, hk.2.2⟩,
         fun u hu hnz hlt_lv => by
           by_cases huv : u = v
           · subst huv; refine ⟨ks.nkl.toNat, hinv.nkl_pos,
               (by change ks.nkl.toNat < (ks.nkl + 1#32).toNat; rw [hnkl1]; omega), ?_⟩
             change ((ks.kl.set ks.nkl.toNat l)[ks.nkl.toNat]?.getD 0#32).toNat / 2 = v
             rw [List.getElem?_set_self hkl_len, Option.getD_some]; exact hv_eq.symm
           · rw [hfl_set_ne u huv] at hnz
             obtain ⟨i, hi1, hi2, hieq⟩ := hinv.kl_injective u hu hnz hlt_lv
             refine ⟨i, hi1, (by change i < (ks.nkl + 1#32).toNat; rw [hnkl1]; omega), ?_⟩
             change ((ks.kl.set ks.nkl.toNat l)[i]?.getD 0#32).toNat / 2 = u
             rwa [List.getElem?_set_ne (by omega)],
         hnkl_count2, hkl_nodup3, by rw [hfilter_eq]; exact hinv.open_eq, hseen_trl2⟩
      refine ⟨hinv3, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hfl_mono, fun x hx => ?_⟩
      rw [k6a_mem_resolvent_iff] at hx ⊢
      rcases hx with ⟨j, hj, htrl, hlvl, hfl⟩ | ⟨i, hi1, hi2, hieq⟩
      · left
        have hx_lt : (x ^^^ 1) / 2 < ks.nv.toNat := by
          have hmem := k6_mem_trailLits_of_lt (Nat.lt_of_lt_of_le hj hinv.idx_le)
            (by rw [hsh.trl_len]; have := hinv.assign.trl_end_le; omega)
          have hlt := hinv.assign.trl_lt _ hmem; rw [htrl] at hlt; omega
        exact ⟨j, hj, htrl, hlvl, hfl_mono _ hx_lt hfl⟩
      · right
        have hi_lt : i < ks.nkl.toNat := by omega
        have hi_min : i < min ks3.nkl.toNat ks3.kl.length := by
          change i < min (ks.nkl + 1#32).toNat (ks.kl.set ks.nkl.toNat l).length
          rw [hnkl1, List.length_set, hsh.kl_len]; omega
        refine ⟨i, hi1, hi_min, ?_⟩
        change ((ks.kl.set ks.nkl.toNat l)[i]?.getD 0#32).toNat = x
        rwa [List.getElem?_set_ne (by omega)]
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
  have hm := L.hmaxV
  obtain ⟨hv_eq, _⟩ := k6_bv32_div2_lt hl_lt
  obtain ⟨hl_val2, hl_top_trl⟩ := hl_ok hskip_ne
  have hskip_bv : l >>> 1 ≠ skip := fun h => hskip_ne (by rw [← hv_eq, h])
  obtain ⟨hinv', hpres', hfl_mono, _⟩ := k6AnaLit_preserves_anaInv hinv hvdec hl_lt hl_ok
  constructor
  · intro hvlvl0
    obtain ⟨j0, hj0_te, hj0_eq⟩ :=
      k6_falsified_to_trail hinv.assign hinv.synced hl_lt hl_val2
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
        have hfl_check : ∀ fl : BitVec 32,
            ((ks.flags.set (l >>> 1).toNat (fl ||| 2#32))[l.toNat / 2]?.getD 0#32 &&& 2#32) ≠
              0#32 := fun fl => by
          rw [← hv_eq, List.getElem?_set_self hfl_len, Option.getD_some]
          exact k6a_fl_or2_and2_nz fl
        let fl' := ks.flags[(l >>> 1).toNat]?.getD 0#32 ||| 2#32
        let ks1 : K6State := { ks with flags := ks.flags.set (l >>> 1).toNat fl' }
        have hks2_fl : ∀ s : K6State, s.flags = ks1.flags →
            ((if ks.lvlArr[(l >>> 1).toNat]?.getD 0#32 = ks.lvl then
                { s with openCnt := s.openCnt + 1#32 }
              else if s.nkl.toNat < L.maxV then
                { s with kl := s.kl.set s.nkl.toNat l, nkl := s.nkl + 1#32 }
              else s).flags[l.toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32 := by
          intro s hs
          by_cases ht : ks.lvlArr[(l >>> 1).toNat]?.getD 0#32 = ks.lvl
          · rw [k6a_ite_t ht]; change (s.flags[l.toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32
            rw [hs]; exact hfl_check _
          · rw [k6a_ite_f ht]; by_cases hk : s.nkl.toNat < L.maxV
            · rw [k6a_ite_t hk]; change (s.flags[l.toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32
              rw [hs]; exact hfl_check _
            · rw [k6a_ite_f hk]; rw [hs]; exact hfl_check _
        apply hks2_fl
        by_cases ha : ks1.nana.toNat < L.maxV
        · rw [k6a_ite_t ha]
        · rw [k6a_ite_f ha]
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
        · exfalso
          have hv2 : ks.vals[l.toNat ^^^ 1]? = some 2#32 := by
            have := hnt.2.2.2.2
            rw [hpres'.vals, h1, show litNeg l.toNat = l.toNat ^^^ 1 from rfl] at this
            exact this
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
    let off := k6ClauseOff ks cid.toNat
    let sz := k6ClauseSize ks cid.toNat
    ∀ n ≤ sz,
      let st := k6AnaPrefix L skip ks off n
      K6AnaInv L P st idx ∧ K6AnaPreserved ks st ∧
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
    intro _
    exact ⟨hinv, k6AnaPreserved_refl ks, fun _ _ h => h, fun _ h => h, fun _ hk => by omega⟩
  | succ k ih =>
    intro hk_le
    obtain ⟨hinv_k, hpres_k, hfl_k, hres_k, hdone_k⟩ := ih (Nat.le_of_succ_le hk_le)
    let st := k6AnaPrefix L skip ks off k
    let lit := ks.arena[off + k]?.getD 0#32
    have hlit_mem : lit.toNat ∈ k6ClauseLits ks cid.toNat :=
      (k6_mem_clauseLits_iff hbd).mpr ⟨k, by omega, rfl⟩
    have hlit_lt : lit.toNat < 2 * st.nv.toNat := by
      rw [hpres_k.nv]; exact hwf.2.2.1 _ hlit_mem
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
    refine ⟨hinv_s, k6AnaPreserved_trans hpres_k hpres_s,
      fun v hv hnz => hfl_s v (by rw [hpres_k.nv]; exact hv) (hfl_k v hv hnz),
      fun x hx => hres_s x (hres_k x hx), fun m hm hne => ?_⟩
    by_cases hmk : m = k
    · subst hmk
      have heff := k6AnaLit_effect_on_lit hinv_k hvdec_st hlit_lt hlit_ok hne
      rw [hpres_k.lvlArr] at heff; exact heff
    · have hprev := hdone_k m (by omega) hne
      exact ⟨hprev.1, fun hnz => hres_s _ (hprev.2 hnz)⟩

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
    K6AnaInv L P ks' idx ∧ K6AnaPreserved ks ks' ∧
    SemEntails P (k6ResolventLits ks' idx) ∧
    (∀ v < ks.nv.toNat, (ks.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32 →
      (ks'.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32) := by
  intro ks'
  have hm := L.hmaxV; have hwf := hinv.cl_wf cid.toNat hcid
  have hbd : k6ClauseOff ks cid.toNat + k6ClauseSize ks cid.toNat ≤ ks.arena.length := by
    rw [hinv.shapes.arena_len]; have := hwf.2.1; have := hinv.alen_le; omega
  obtain ⟨hinv', hpres', hfl', hres_sub, hdone⟩ :=
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
  refine ⟨hinv', hpres', fun β hP => ?_, hfl'⟩
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

/-- `12/39`: Parametric `Func.wp` proof for `full_k6_ana_clause`. -/
theorem full_k6_ana_clause_wp (Γ : Env) :
    ∀ args m Q X, k6AnaClauseSpec args m Q X →
      Func.wp Γ full_k6_ana_clause_body args m Q X := by
  rintro ⟨kPtr, cid, skip_v, ⟨⟩⟩ m Q X ⟨L, P, ks, idx, R, hinv, hcid, hvdec, hlits, hskip,
    hm, hQ⟩
  have hm_v := L.hmaxV; have hac := L.hacap
  have hsh := hinv.shapes; have hnv := hinv.nv_le; have hnc := hinv.nc_le
  have hmv : ks.max_v = L.mv32 := hinv.max_v_eq
  have hcid_len : cid.toNat < szCl L := by unfold szCl; omega
  have hmA := k6Mem_to_amem hsh hm; clear hm
  let off := ks.clOff[cid.toNat]?.getD 0#32
  let sz := ks.clSz[cid.toNat]?.getD 0#32
  have hwf := hinv.cl_wf cid.toNat hcid
  have hspan : off.toNat + sz.toNat ≤ ks.alen.toNat := hwf.2.1
  have hal := hinv.alen_le
  have hbd : k6ClauseOff ks cid.toNat + k6ClauseSize ks cid.toNat ≤ ks.arena.length := by
    rw [hsh.arena_len]; omega
  have hlit_lt : ∀ n < sz.toNat,
      (ks.arena[off.toNat + n]?.getD 0#32).toNat < 2 * ks.nv.toNat := fun n hn =>
    hwf.2.2.1 _ ((k6_mem_clauseLits_iff hbd).mpr ⟨n, hn, rfl⟩)
  c0_hsteps_nogrp
  rw [hmv]
  c0_hsteps_nogrp
  refine wp_while_state1 (proj := fun st : BitVec 32 × K6State => st.1)
    (fun st => sz.toNat - st.1.toNat)
    (fun st m' => st.1.toNat ≤ sz.toNat ∧ st.2 = k6AnaPrefix L skip_v ks off.toNat st.1.toNat ∧
      (K6MemA L kPtr st.2 ⋆ R) m') ?_ ?_
  · intro Lp hL; exact hL (0#32, ks) m ⟨Nat.zero_le _, rfl, hmA⟩
  · rintro Lp ⟨i, st⟩ m'' ⟨hi_le, hst, hm''⟩ ih
    dsimp only at hi_le hst hm'' ⊢
    c0_hsplit
    · have hi_lt : i.toNat < sz.toNat := by bv_omega
      have hi1 : (i + 1#32).toNat = i.toNat + 1 := by
        unfold dimacsBound at hac; bv_omega
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
      c0_hsteps_nogrp
      refine wp_join0 (fun m3 => (K6MemA L kPtr (k6AnaLit L skip_v st l) ⋆ R) m3) ?_ ?_
      · intro Jv m3 hm3; c0_hsteps!
        exact ih (i + 1#32, k6AnaLit L skip_v st l) m3 (by dsimp only; rw [hi1]; omega)
          ⟨by dsimp only; rw [hi1]; omega, by dsimp only; rw [hi1, hnext_eq], hm3⟩
      · intro Jv hJv
        c0_hsplit
        · have hsk_ne : l >>> 1 ≠ skip_v := by rw [← hl_st_mod]; exact ‹_›
          c0_hsteps_nogrp
          refine wp_join0 (fun m3 => (K6MemA L kPtr (k6AnaLit L skip_v st l) ⋆ R) m3) ?_ ?_
          · intro Jf m3 hm3; c0_hsteps!; exact hJv m3 hm3
          · intro Jf hJf
            try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
            c0_hsplit
            · have hv_nz : st.lvlArr[(l >>> 1).toNat]?.getD 0#32 ≠ 0#32 := by
                have h1 : 0 < (st.lvlArr[(st.arena[((ks.clOff[cid.toNat]?.getD 0#32).toNat +
                    i.toNat) % 2 ^ 32]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
                  have hlt := hc; rw [hl_st_mod] at hlt; bv_omega
                rw [hl_st_mod] at h1
                have hdiv : (l >>> 1).toNat = l.toNat / 2 := hv_eq
                rw [hdiv]; intro hz; rw [hz] at h1; simp at h1
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
                    rw [hkana_st2, k6a_ite_f hntop, k6a_ite_t hnk_mv]
                    k6_ext; rw [hl_st_add]
                  · have hntop : st.lvlArr[(l >>> 1).toNat]?.getD 0#32 ≠ st.lvl := by
                      rw [← hl_st_mod, hlv_eq]; assumption
                    have hnk_ge : ¬ st2.nkl.toNat < L.maxV := by bv_omega
                    have hst2_eq : st2 = k6AnaLit L skip_v st l := by
                      rw [hkana_st2, k6a_ite_f hntop, k6a_ite_f hnk_ge]
                    exact hJf _ (hst2_eq ▸ hm3)
                · intro Jna hJna
                  c0_hsplit
                  · have hna_mv : st.nana.toNat < L.maxV := by bv_omega
                    have hna_len : st.nana.toNat < szV L := by unfold szV; exact hna_mv
                    c0_hsteps!
                    refine hJna _ (Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ R) _) ?_) hm)
                    dsimp only [st2, st1, fl']; rw [k6a_ite_t hna_mv]
                    k6_ext <;> simp only [hl_st_add] <;> rfl
                  · have hna_ge : ¬ st.nana.toNat < L.maxV := by bv_omega
                    c0_hsteps!
                    refine hJna _ (Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ R) _) ?_) hm)
                    dsimp only [st2, st1, fl']; rw [k6a_ite_f hna_ge]
                    k6_ext <;> simp only [hl_st_add] <;> rfl
              · have hfl_nz : (st.flags[(l >>> 1).toNat]?.getD 0#32 &&& 2#32) ≠ 0#32 := by
                  rw [← hl_st_mod]; exact ‹_›
                have heq : k6AnaLit L skip_v st l = st := by
                  unfold k6AnaLit; dsimp only
                  rw [k6a_ite_f hsk_ne, k6a_ite_f hv_nz, k6a_ite_f hfl_nz]
                c0_hsteps!; exact hJf m'' (heq.symm ▸ hm'')
            · have hv0 : st.lvlArr[(l >>> 1).toNat]?.getD 0#32 = 0#32 := by
                have hle : (st.lvlArr[(st.arena[((ks.clOff[cid.toNat]?.getD 0#32).toNat +
                    i.toNat) % 2 ^ 32]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
                  have hlt := hc; rw [hl_st_mod] at hlt; bv_omega
                rw [hl_st_mod, ← hv_eq] at hle; exact BitVec.eq_of_toNat_eq hle
              have heq : k6AnaLit L skip_v st l = st := by
                unfold k6AnaLit; dsimp only; rw [k6a_ite_f hsk_ne, k6a_ite_t hv0]
              c0_hsteps!; exact hJf m'' (heq.symm ▸ hm'')
        · have hsk_eq : l >>> 1 = skip_v := by rw [← hl_st_mod]; exact ‹_›
          have heq : k6AnaLit L skip_v st l = st := by
            unfold k6AnaLit; dsimp only; rw [k6a_ite_t hsk_eq]
          c0_hsteps!; exact hJv m'' (heq.symm ▸ hm'')
    · have hi_eq : i.toNat = sz.toNat := by dsimp only [sz] at hi_le ⊢; bv_omega
      c0_hsteps!
      obtain ⟨_, hmFin⟩ := k6MemA_to_mem hm''
      have hent := k6AnaPrefix_entails hinv hcid hvdec hlits hskip
      have hst_fin : st = k6AnaPrefix L skip_v ks (k6ClauseOff ks cid.toNat)
          (k6ClauseSize ks cid.toNat) := by rw [hst, hi_eq]; rfl
      rw [hst_fin] at hmFin
      exact hQ _ _ hent.1 hent.2.1 hent.2.2.1 hent.2.2.2 hmFin

/-! ## 2. Pure Helpers & `full_k6_analyze_wp` (`13/39`) -/

private theorem k6a_init_anaInv {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (hinv : K6Inv L P ks) (hsync : K6TrailSynced ks) (hlvl_pos : 0 < ks.lvl.toNat)
    (hvdec : ∃ v < ks.nv.toNat, ks.lvlArr[v]?.getD 0#32 = ks.lvl) :
    let ks0 : K6State := { ks with nkl := 1#32, nana := 0#32, openCnt := 0#32 }
    K6AnaInv L P ks0 ks.trl_end.toNat ∧ K6AnaPreserved ks ks0 := by
  intro ks0
  have hm := L.hmaxV
  have hsh0 : ks0.ShapesOk L := by
    have heq : ks0 = ((ks.putHdr .nkl 1#32).putHdr .nana 0#32).putHdr .openCnt 0#32 := by k6_ext
    rw [heq]; exact ((hinv.shapes.putHdr .nkl 1#32).putHdr .nana 0#32).putHdr .openCnt 0#32
  have hnv_pos : 1 ≤ ks.nv.toNat := by obtain ⟨v, hv, _⟩ := hvdec; omega
  have hfl_clean := hinv.clauses.flags_clean
  have hfilt0 : ((List.range ks.trl_end.toNat).filter fun j =>
      let v := (ks0.trl[j]?.getD 0#32).toNat / 2
      decide (ks0.lvlArr[v]?.getD 0#32 = ks0.lvl ∧
        (ks0.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32)) = [] := by
    rw [List.filter_eq_nil_iff]; intro j hj; rw [List.mem_range] at hj
    have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
      rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; have := hinv.clauses.nv_le; omega
    have hlt := hinv.assign.trl_lt _ (k6_mem_trailLits_of_lt hj htrl_len)
    simp only [decide_eq_true_eq]; intro h
    exact h.2 (hfl_clean _ (by change (ks.trl[j]?.getD 0#32).toNat / 2 < ks.nv.toNat; omega))
  refine ⟨⟨hsh0, hinv.clauses.acap_eq, hinv.clauses.max_v_eq, hinv.clauses.max_orig_eq,
    hinv.clauses.max_cl_eq, hinv.clauses.nv_le, hinv.clauses.nc_le, hinv.clauses.alen_le,
    hinv.clauses.nassump_le, hlvl_pos, Nat.le_refl _, hinv.clauses.cl_wf, hinv.clauses.cl_mono,
    hinv.clauses.incons_ok, hinv.clauses.assump_ok, hinv.watches,
    k6BaseAssignOk_cast hinv.assign rfl rfl rfl rfl rfl rfl rfl rfl rfl, hsync, hinv.reasons,
    by change 1 ≤ (1#32 : BitVec 32).toNat; decide, by change 1 ≤ ks.nv.toNat; exact hnv_pos,
    by change (0#32 : BitVec 32).toNat ≤ ks.nv.toNat; simp,
    by change ((ks.ana.take 0).map BitVec.toNat).Nodup; simp,
    fun i hi => by change i < (0#32 : BitVec 32).toNat at hi; simp at hi,
    fun v hv => ⟨fun h => absurd (hfl_clean v hv) h,
      fun ⟨_, hi, _⟩ => by change _ < (0#32 : BitVec 32).toNat at hi; simp at hi⟩,
    fun i hi1 hi2 => by change i < (1#32 : BitVec 32).toNat at hi2; simp at hi2; omega,
    fun v hv hnz _ => absurd (hfl_clean v hv) hnz,
    fun v hv hnz => absurd (hfl_clean v hv) hnz,
    by change (((ks.kl.take 1).drop 1).map _).Nodup
       have : (ks.kl.take 1).drop 1 = [] := List.drop_eq_nil_of_le (by simp; omega)
       rw [this]; simp,
    by rw [hfilt0]; rfl,
    fun v hv hnz _ => absurd (hfl_clean v hv) hnz⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
     rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

private theorem k6a_resolvent_step_skip {L : K6Layout} {P : (Nat → Bool) → Prop} {st : K6State}
    {idx' : Nat} (hinv : K6AnaInv L P st (idx' + 1))
    (hskip : ¬ ((st.flags[(st.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32 ∧
      st.lvlArr[(st.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32 = st.lvl)) :
    K6AnaInv L P st idx' ∧ k6ResolventLits st (idx' + 1) = k6ResolventLits st idx' := by
  have hdec_f : decide (st.lvlArr[(st.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32 = st.lvl ∧
      (st.flags[(st.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32) = false :=
    decide_eq_false fun h => hskip ⟨h.2, h.1⟩
  have hop_eq : st.openCnt.toNat = ((List.range idx').filter fun j =>
      let v := (st.trl[j]?.getD 0#32).toNat / 2
      decide (st.lvlArr[v]?.getD 0#32 = st.lvl ∧
        (st.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32)).length := by
    have h := hinv.open_eq
    rw [List.range_succ, List.filter_append, List.filter_cons] at h
    simpa only [hdec_f, Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.append_nil] using h
  refine ⟨⟨hinv.shapes, hinv.acap_eq, hinv.max_v_eq, hinv.max_orig_eq, hinv.max_cl_eq,
    hinv.nv_le, hinv.nc_le, hinv.alen_le, hinv.nassump_le, hinv.lvl_pos,
    by have := hinv.idx_le; omega, hinv.cl_wf, hinv.cl_mono, hinv.incons_ok, hinv.assump_ok,
    hinv.watches, hinv.assign, hinv.synced, hinv.reasons, hinv.nkl_pos, hinv.nkl_le, hinv.nana_le,
    hinv.ana_nodup, hinv.ana_lt, hinv.flags_seen, hinv.kl_nonTop, hinv.kl_injective, hinv.nkl_count,
    hinv.kl_nodup, hop_eq, hinv.seen_in_trl⟩, ?_⟩
  unfold k6ResolventLits
  rw [List.range_succ, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  have hno : ¬ (st.lvlArr[(st.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32 = st.lvl ∧
      (st.flags[(st.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32) :=
    fun h => hskip ⟨h.2, h.1⟩
  simp [hno]

private theorem k6a_resolvent_step_hit {L : K6Layout} {P : (Nat → Bool) → Prop} {st : K6State}
    {idx' : Nat} (hinv : K6AnaInv L P st (idx' + 1))
    (hhit : (st.flags[(st.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32 ∧
      st.lvlArr[(st.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32 = st.lvl) :
    let p := st.trl[idx']?.getD 0#32
    let st1 : K6State := { st with openCnt := st.openCnt - 1#32 }
    0 < st.openCnt.toNat ∧ K6AnaInv L P st1 idx' ∧ K6AnaPreserved st st1 ∧
    ∀ x ∈ k6ResolventLits st (idx' + 1), x ∈ (p.toNat ^^^ 1) :: k6ResolventLits st1 idx' := by
  intro p st1
  have hdec_t : decide (st.lvlArr[(st.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32 = st.lvl ∧
      (st.flags[(st.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32) = true :=
    decide_eq_true ⟨hhit.2, hhit.1⟩
  have hop_succ : st.openCnt.toNat = ((List.range idx').filter fun j =>
      let v := (st.trl[j]?.getD 0#32).toNat / 2
      decide (st.lvlArr[v]?.getD 0#32 = st.lvl ∧
        (st.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32)).length + 1 := by
    have h := hinv.open_eq
    rw [List.range_succ, List.filter_append, List.filter_cons] at h
    simpa only [hdec_t, ↓reduceIte, List.filter_nil, List.length_append, List.length_singleton]
      using h
  have hpos : 0 < st.openCnt.toNat := by omega
  have hsub : (st.openCnt - 1#32).toNat = st.openCnt.toNat - 1 := by bv_omega
  have hsh1 : st1.ShapesOk L := by
    have heq : st1 = st.putHdr .openCnt (st.openCnt - 1#32) := by k6_ext
    rw [heq]; exact hinv.shapes.putHdr .openCnt _
  have hinv1 : K6AnaInv L P st1 idx' :=
    ⟨hsh1, hinv.acap_eq, hinv.max_v_eq, hinv.max_orig_eq, hinv.max_cl_eq, hinv.nv_le, hinv.nc_le,
     hinv.alen_le, hinv.nassump_le, hinv.lvl_pos,
     by change idx' ≤ st.trl_end.toNat; have := hinv.idx_le; omega,
     hinv.cl_wf, hinv.cl_mono, hinv.incons_ok, hinv.assump_ok, hinv.watches,
     k6BaseAssignOk_cast hinv.assign rfl rfl rfl rfl rfl rfl rfl rfl rfl, hinv.synced,
     hinv.reasons, hinv.nkl_pos, hinv.nkl_le, hinv.nana_le, hinv.ana_nodup, hinv.ana_lt,
     hinv.flags_seen, hinv.kl_nonTop, hinv.kl_injective, hinv.nkl_count, hinv.kl_nodup,
     by change (st.openCnt - 1#32).toNat = ((List.range idx').filter fun j =>
          let v := (st.trl[j]?.getD 0#32).toNat / 2
          decide (st.lvlArr[v]?.getD 0#32 = st.lvl ∧
            (st.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32)).length
        rw [hsub, hop_succ]; omega,
     hinv.seen_in_trl⟩
  refine ⟨hpos, hinv1, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, fun x hx => ?_⟩
  rw [k6a_mem_resolvent_iff] at hx
  rw [List.mem_cons, k6a_mem_resolvent_iff]
  rcases hx with ⟨j, hj, htrl, hlvl, hfl⟩ | hr
  · by_cases hji : j = idx'
    · left; subst hji; have hx_eq : p.toNat = x ^^^ 1 := htrl; rw [hx_eq, k6_nat_xor1_xor1]
    · right; left; exact ⟨j, by omega, htrl, hlvl, hfl⟩
  · right; right; exact hr

private theorem k6a_uip_exit {L : K6Layout} {P : (Nat → Bool) → Prop} {st1 : K6State} {idx' : Nat}
    (hinv : K6AnaInv L P st1 idx') (hop0 : st1.openCnt = 0#32) :
    k6ResolventLits st1 idx' = ((st1.kl.take st1.nkl.toNat).drop 1).map BitVec.toNat := by
  have hfilt_nil : ((List.range idx').filter fun j =>
      let v := (st1.trl[j]?.getD 0#32).toNat / 2
      decide (st1.lvlArr[v]?.getD 0#32 = st1.lvl ∧
        (st1.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32)) = [] := by
    have h := hinv.open_eq; rw [hop0] at h
    exact List.eq_nil_of_length_eq_zero (by simpa using h.symm)
  have hno : ∀ j < idx', ¬ (st1.lvlArr[(st1.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32 = st1.lvl ∧
      (st1.flags[(st1.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32) := by
    intro j hj hc
    have hmem : j ∈ ((List.range idx').filter fun j =>
        let v := (st1.trl[j]?.getD 0#32).toNat / 2
        decide (st1.lvlArr[v]?.getD 0#32 = st1.lvl ∧
          (st1.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32)) :=
      List.mem_filter.mpr ⟨List.mem_range.mpr hj, decide_eq_true hc⟩
    rw [hfilt_nil] at hmem; cases hmem
  unfold k6ResolventLits
  have hfm : ((List.range idx').filterMap fun j =>
      let l := (st1.trl[j]?.getD 0#32).toNat
      if st1.lvlArr[l / 2]?.getD 0#32 = st1.lvl ∧ (st1.flags[l / 2]?.getD 0#32 &&& 2#32) ≠ 0#32
      then some (l ^^^ 1) else none) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro j hj; rw [List.mem_range] at hj; dsimp only; rw [k6a_ite_f (hno j hj)]
  rw [hfm, List.nil_append]

private theorem k6a_rsn_pre {L : K6Layout} {P : (Nat → Bool) → Prop} {st1 : K6State} {idx' : Nat}
    (hinv : K6AnaInv L P st1 idx') (hidx' : idx' < st1.trl_end.toNat)
    (hpos : 0 < st1.openCnt.toNat)
    (hlvl_p : st1.lvlArr[(st1.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32 = st1.lvl) :
    let p := st1.trl[idx']?.getD 0#32
    let pv := p >>> 1
    let rsn := st1.rsn[pv.toNat]?.getD 0#32
    p.toNat < 2 * st1.nv.toNat ∧ pv.toNat = p.toNat / 2 ∧ pv.toNat < st1.nv.toNat ∧
    rsn ≠ 0xFFFFFFFF#32 ∧ rsn.toNat < st1.nc.toNat ∧
    p.toNat ∈ k6ClauseLits st1 rsn.toNat ∧
    (∀ l ∈ k6ClauseLits st1 rsn.toNat, l / 2 = pv.toNat → l = p.toNat) ∧
    (∀ l ∈ k6ClauseLits st1 rsn.toNat, l / 2 ≠ pv.toNat →
      st1.vals[l]? = some 2#32 ∧ ∃ j < idx', (st1.trl[j]?.getD 0#32).toNat = l ^^^ 1) := by
  intro p pv rsn
  have hm := L.hmaxV
  have htrl_len : st1.trl_end.toNat ≤ st1.trl.length := by
    rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; have := hinv.nv_le; omega
  have hp_lt : p.toNat < 2 * st1.nv.toNat :=
    hinv.assign.trl_lt _ (k6_mem_trailLits_of_lt hidx' htrl_len)
  obtain ⟨hpv_eq, hpv_lt⟩ := k6_bv32_div2_lt hp_lt
  have hrl : p.toNat / 2 < st1.rsn.length := by
    rw [hinv.shapes.rsn_len]; have := hinv.nv_le; omega
  have hfilt_ne : ((List.range idx').filter fun j =>
      let v := (st1.trl[j]?.getD 0#32).toNat / 2
      decide (st1.lvlArr[v]?.getD 0#32 = st1.lvl ∧
        (st1.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32)) ≠ [] := by
    intro hnil; have h := hinv.open_eq; rw [hnil] at h; simp at h; omega
  obtain ⟨j0, hj0_mem⟩ := List.exists_mem_of_ne_nil _ hfilt_ne
  rw [List.mem_filter, List.mem_range, decide_eq_true_eq] at hj0_mem
  have hrsn_ne : rsn ≠ 0xFFFFFFFF#32 := by
    have hd := hinv.assign.dec_earliest idx' j0 hj0_mem.1 hidx'
      (by rw [hlvl_p]; exact hinv.lvl_pos) (hj0_mem.2.1.trans hlvl_p.symm)
    dsimp only [rsn]; rw [hpv_eq, List.getElem?_eq_getElem hrl, Option.getD_some]
    simpa only [p, List.getElem?_eq_getElem hrl, Option.getD_some] using hd
  have hro := hinv.reasons idx' hidx'; dsimp only at hro
  have hrsn_eq : st1.rsn[p.toNat / 2]?.getD 0xFFFFFFFF#32 = rsn := by
    dsimp only [rsn, pv]; rw [hpv_eq]
    simp only [List.getElem?_eq_getElem hrl, Option.getD_some]
  rw [hrsn_eq] at hro
  rcases hro with hff | ⟨hr_lt, hp_mem, hall⟩
  · exact absurd hff hrsn_ne
  · refine ⟨hp_lt, hpv_eq, hpv_lt, hrsn_ne, hr_lt, hp_mem, ?_, ?_⟩
    · intro l hl hlv
      by_cases hlp : l = p.toNat
      · exact hlp
      · exfalso; obtain ⟨j, hj, hjeq⟩ := hall l hl hlp
        have hvar : (st1.trl[j]?.getD 0#32).toNat / 2 = p.toNat / 2 := by
          rw [hjeq, k6a_xor1_div2, hlv, hpv_eq]
        exact k6_trl_nodup_var_ne hinv.shapes hinv.nv_le hinv.assign
          (Nat.lt_trans hj hidx') hidx' (by omega) hvar
    · intro l hl hne
      have hlp : l ≠ p.toNat := fun heq => hne (by rw [heq, hpv_eq])
      obtain ⟨j, hj, hjeq⟩ := hall l hl hlp
      have hsy := hinv.synced j (Nat.lt_trans hj hidx'); dsimp only at hsy
      rw [hjeq, k6_nat_xor1_xor1] at hsy
      exact ⟨hsy.2, j, hj, hjeq⟩

private theorem k6a_swap_kl_preserves {L : K6Layout} {P : (Nat → Bool) → Prop}
    {stClean : K6State} {uip wi jlvl : BitVec 32}
    (hinv : K6Inv L P stClean) (hsync : K6TrailSynced stClean)
    (hnkl_pos : 1 ≤ stClean.nkl.toNat) (hnkl_le : stClean.nkl.toNat ≤ stClean.nv.toNat)
    (hwi : 2 ≤ stClean.nkl.toNat → 1 ≤ wi.toNat ∧ wi.toNat < stClean.nkl.toNat)
    (hkl_nt : ∀ k, 1 ≤ k → k < stClean.nkl.toNat →
      let l := (stClean.kl[k]?.getD 0#32).toNat
      l < 2 * stClean.nv.toNat ∧ 0 < (stClean.lvlArr[l / 2]?.getD 0#32).toNat ∧
      (stClean.lvlArr[l / 2]?.getD 0#32).toNat ≤ jlvl.toNat ∧ stClean.vals[l]? = some 2#32) :
    let stKl0 := stClean.putArr .kl 0 uip
    let stSw := if 2 ≤ stClean.nkl.toNat ∧ wi ≠ 1#32 then
      (stKl0.putArr .kl 1 (stKl0.kl[wi.toNat]?.getD 0#32)).putArr .kl wi.toNat
        (stKl0.kl[1]?.getD 0#32)
      else stKl0
    K6Inv L P stSw ∧ K6TrailSynced stSw ∧ K6AnaPreserved stClean stSw ∧
    stSw.nkl = stClean.nkl ∧ stSw.nana = stClean.nana ∧ stSw.ana = stClean.ana ∧
    stSw.kl[0]? = some uip ∧
    (∀ x ∈ uip.toNat :: ((stClean.kl.take stClean.nkl.toNat).drop 1).map BitVec.toNat,
      x ∈ (stSw.kl.take stClean.nkl.toNat).map BitVec.toNat) ∧
    (∀ k, 1 ≤ k → k < stSw.nkl.toNat →
      let l := (stSw.kl[k]?.getD 0#32).toNat
      l < 2 * stSw.nv.toNat ∧ 0 < (stSw.lvlArr[l / 2]?.getD 0#32).toNat ∧
      (stSw.lvlArr[l / 2]?.getD 0#32).toNat ≤ jlvl.toNat ∧ stSw.vals[l]? = some 2#32) := by
  intro stKl0 stSw
  have hm := L.hmaxV
  have hnv := hinv.clauses.nv_le; have hkl_len : stClean.kl.length = L.maxV := hinv.shapes.kl_len
  have hsh0 : stKl0.ShapesOk L := hinv.shapes.putArr .kl 0 uip
  have hshSw : stSw.ShapesOk L := by
    dsimp only [stSw]; by_cases hc : 2 ≤ stClean.nkl.toNat ∧ wi ≠ 1#32
    · rw [k6a_ite_t hc]; exact (hsh0.putArr .kl _ _).putArr .kl _ _
    · rw [k6a_ite_f hc]; exact hsh0
  have hfr : ∃ kl', stSw = { stClean with kl := kl' } := by
    dsimp only [stSw, stKl0]; by_cases hc : 2 ≤ stClean.nkl.toNat ∧ wi ≠ 1#32
    · rw [k6a_ite_t hc]; exact ⟨_, by k6_ext⟩
    · rw [k6a_ite_f hc]; exact ⟨_, by k6_ext⟩
  obtain ⟨kl', hfr_eq⟩ := hfr
  have hpres : K6AnaPreserved stClean stSw := by
    rw [hfr_eq]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have ⟨hinvSw, hsyncSw⟩ := k6a_inv_of_ana_clean hinv hsync hshSw hpres
    (by rw [hfr_eq]; exact hinv.clauses.nkl_le) (by rw [hfr_eq]; exact hinv.clauses.nana_le)
    (by rw [hfr_eq]; exact hinv.clauses.flags_clean)
  have hkl0_0 : stKl0.kl[0]? = some uip := by
    dsimp only [stKl0]; k6_field; exact List.getElem?_set_self (by omega)
  have hkl0_pos : ∀ k, 1 ≤ k → stKl0.kl[k]? = stClean.kl[k]? := fun k hk => by
    dsimp only [stKl0]; k6_field; exact List.getElem?_set_ne (by omega)
  have hsw_nkl : stSw.nkl = stClean.nkl := by rw [hfr_eq]
  have hsw0 : stSw.kl[0]? = some uip := by
    dsimp only [stSw]; by_cases hc : 2 ≤ stClean.nkl.toNat ∧ wi ≠ 1#32
    · rw [k6a_ite_t hc]; have ⟨hw1, _⟩ := hwi hc.1
      k6_field; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hkl0_0
    · rw [k6a_ite_f hc]; exact hkl0_0
  have hmem_of_idx : ∀ k < stClean.nkl.toNat,
      (stSw.kl[k]?.getD 0#32).toNat ∈ (stSw.kl.take stSw.nkl.toNat).map BitVec.toNat := by
    intro k hk
    have hk_len : k < stSw.kl.length := by rw [hshSw.kl_len]; omega
    rw [List.mem_map]
    refine ⟨stSw.kl[k]'hk_len, ?_, by simp [List.getElem?_eq_getElem hk_len]⟩
    rw [List.mem_take_iff_getElem]; exact ⟨k, by rw [hsw_nkl]; omega, rfl⟩
  have hbij : ∀ k, 1 ≤ k → k < stClean.nkl.toNat →
      ∃ k', 1 ≤ k' ∧ k' < stClean.nkl.toNat ∧ stSw.kl[k]? = stClean.kl[k']? := by
    intro k hk1 hk_lt; by_cases hc : 2 ≤ stClean.nkl.toNat ∧ wi ≠ 1#32
    · obtain ⟨hw1, hw_lt⟩ := hwi hc.1
      have hw_ne1 : wi.toNat ≠ 1 := fun h => hc.2 (BitVec.eq_of_toNat_eq h)
      have hkl_sw : stSw.kl = (stKl0.kl.set 1 (stKl0.kl[wi.toNat]?.getD 0#32)).set wi.toNat
          (stKl0.kl[1]?.getD 0#32) := by dsimp only [stSw]; rw [k6a_ite_t hc]; k6_field
      have hl1 : 1 < stClean.kl.length := by omega
      have hlw : wi.toNat < stClean.kl.length := by omega
      by_cases hkw : k = wi.toNat
      · subst hkw; refine ⟨1, by omega, by omega, ?_⟩
        rw [hkl_sw, List.getElem?_set_self (by rw [List.length_set, hsh0.kl_len]; omega),
          hkl0_pos 1 (by omega), List.getElem?_eq_getElem hl1, Option.getD_some]
      · by_cases hk_1 : k = 1
        · subst hk_1; refine ⟨wi.toNat, hw1, hw_lt, ?_⟩
          rw [hkl_sw, List.getElem?_set_ne (by omega),
            List.getElem?_set_self (by rw [hsh0.kl_len]; omega),
            hkl0_pos wi.toNat hw1, List.getElem?_eq_getElem hlw, Option.getD_some]
        · refine ⟨k, hk1, hk_lt, ?_⟩
          rw [hkl_sw, List.getElem?_set_ne (Ne.symm hkw), List.getElem?_set_ne (Ne.symm hk_1),
            hkl0_pos k hk1]
    · refine ⟨k, hk1, hk_lt, ?_⟩
      have hkl_sw : stSw.kl = stKl0.kl := by dsimp only [stSw]; rw [k6a_ite_f hc]
      rw [hkl_sw, hkl0_pos k hk1]
  refine ⟨hinvSw, hsyncSw, hpres, hsw_nkl, by rw [hfr_eq], by rw [hfr_eq], hsw0, ?_, ?_⟩
  · intro x hx; rw [← hsw_nkl]; rcases List.mem_cons.mp hx with rfl | hx_tl
    · have h0 := hmem_of_idx 0 (by omega); rwa [hsw0, Option.getD_some] at h0
    · rw [List.mem_map] at hx_tl; obtain ⟨b, hb, rfl⟩ := hx_tl
      rw [List.mem_iff_getElem] at hb; obtain ⟨k, hk, rfl⟩ := hb
      have hk1 : k + 1 < stClean.nkl.toNat := by
        simp [List.length_take, hkl_len] at hk; omega
      have hb_eq : (((stClean.kl.take stClean.nkl.toNat).drop 1)[k]'hk) =
          stClean.kl[k + 1]?.getD 0#32 := by
        simp only [List.getElem_drop, List.getElem_take]
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; congr 1; omega
      rw [hb_eq]
      by_cases hc : 2 ≤ stClean.nkl.toNat ∧ wi ≠ 1#32
      · obtain ⟨hw1, hw_lt⟩ := hwi hc.1
        have hw_ne1 : wi.toNat ≠ 1 := fun h => hc.2 (BitVec.eq_of_toNat_eq h)
        have hkl_sw : stSw.kl = (stKl0.kl.set 1 (stKl0.kl[wi.toNat]?.getD 0#32)).set wi.toNat
            (stKl0.kl[1]?.getD 0#32) := by dsimp only [stSw]; rw [k6a_ite_t hc]; k6_field
        have h1 : stSw.kl[wi.toNat]? = stClean.kl[1]? := by
          have hlen_w : wi.toNat < (stKl0.kl.set 1 (stKl0.kl[wi.toNat]?.getD 0#32)).length := by
            rw [List.length_set, hsh0.kl_len]; omega
          rw [hkl_sw, List.getElem?_set_self hlen_w, hkl0_pos 1 (by omega),
            List.getElem?_eq_getElem (by omega : 1 < stClean.kl.length), Option.getD_some]
        have h2 : stSw.kl[1]? = stClean.kl[wi.toNat]? := by
          rw [hkl_sw, List.getElem?_set_ne (by omega),
            List.getElem?_set_self (by rw [hsh0.kl_len]; omega), hkl0_pos wi.toNat hw1,
            List.getElem?_eq_getElem (by omega : wi.toNat < stClean.kl.length), Option.getD_some]
        by_cases hk_1 : k + 1 = 1
        · rw [hk_1, ← h1]; exact hmem_of_idx wi.toNat hw_lt
        · by_cases hk_w : k + 1 = wi.toNat
          · rw [hk_w, ← h2]; exact hmem_of_idx 1 (by omega)
          · have h3 : stSw.kl[k + 1]? = stClean.kl[k + 1]? := by
              rw [hkl_sw, List.getElem?_set_ne (Ne.symm hk_w), List.getElem?_set_ne (Ne.symm hk_1),
                hkl0_pos (k + 1) (by omega)]
            rw [← h3]; exact hmem_of_idx (k + 1) hk1
      · have h3 : stSw.kl[k + 1]? = stClean.kl[k + 1]? := by
          have hkl_sw : stSw.kl = stKl0.kl := by dsimp only [stSw]; rw [k6a_ite_f hc]
          rw [hkl_sw, hkl0_pos (k + 1) (by omega)]
        rw [← h3]; exact hmem_of_idx (k + 1) hk1
  · intro k hk1 hk_lt; rw [hsw_nkl] at hk_lt
    obtain ⟨k', hk'1, hk'lt, hkeq⟩ := hbij k hk1 hk_lt
    dsimp only; rw [hkeq, hfr_eq]; exact hkl_nt k' hk'1 hk'lt

private theorem k6a_after_bt_facts {L : K6Layout} {P : (Nat → Bool) → Prop}
    {ks stSw ksBt : K6State} {uip jlvl : BitVec 32}
    (hinvSw : K6Inv L P stSw) (hsyncSw : K6TrailSynced stSw) (hpresSw : K6AnaPreserved ks stSw)
    (huip_lt : uip.toNat < 2 * ks.nv.toNat)
    (huip_lvl : ks.lvlArr[uip.toNat / 2]?.getD 0#32 = ks.lvl)
    (hjlvl_lt : jlvl.toNat < ks.lvl.toNat)
    (hinvBt : K6Inv L P ksBt) (hlvlBt : ksBt.lvl = jlvl)
    (hte_le : ksBt.trl_end.toNat ≤ stSw.trl_end.toNat) (hbtPres : K6BtPreserved stSw ksBt)
    (hbtKept : ∀ i < ksBt.trl_end.toNat,
      ksBt.trl[i]? = stSw.trl[i]? ∧ ksBt.rsn[(ksBt.trl[i]?.getD 0#32).toNat / 2]? =
        stSw.rsn[(ksBt.trl[i]?.getD 0#32).toNat / 2]? ∧
      (ksBt.lvlArr[(ksBt.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ jlvl.toNat)
    (hB1 : ∀ i < stSw.trl_end.toNat,
      (stSw.lvlArr[(stSw.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ jlvl.toNat →
      i < ksBt.trl_end.toNat) :
    (¬ ∃ i < ksBt.trl_end.toNat, (ksBt.trl[i]?.getD 0#32).toNat / 2 = uip.toNat / 2) ∧
    ksBt.vals[uip.toNat]? = some 0#32 ∧ ksBt.trl_end.toNat < ksBt.nv.toNat ∧
    (∀ l < 2 * ks.nv.toNat, stSw.vals[l]? = some 2#32 →
      (ks.lvlArr[l / 2]?.getD 0#32).toNat ≤ jlvl.toNat →
      ∃ j < ksBt.trl_end.toNat, (ksBt.trl[j]?.getD 0#32).toNat = l ^^^ 1) ∧
    (∀ d ∈ k6TrailDecisions ksBt, ∃ i < ks.trl_end.toNat,
      (ks.trl[i]?.getD 0#32).toNat = d ∧ d ∈ k6TrailDecisions ks ∧
      (ks.lvlArr[d / 2]?.getD 0#32).toNat ≤ jlvl.toNat) ∧
    (∀ i < ks.trl_end.toNat,
      (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ jlvl.toNat →
      i < ksBt.trl_end.toNat ∧ ksBt.trl[i]? = ks.trl[i]? ∧
      ksBt.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]? =
        ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?) := by
  have hm := L.hmaxV; have hnv_eq : ksBt.nv = ks.nv := hbtPres.nv.trans hpresSw.nv
  have hnv := hinvBt.clauses.nv_le
  have htrl_i : ∀ i < ksBt.trl_end.toNat, ksBt.trl[i]? = ks.trl[i]? := fun i hi =>
    (hbtKept i hi).1.trans (by rw [hpresSw.trl])
  have huip_none : ¬ ∃ i < ksBt.trl_end.toNat,
      (ksBt.trl[i]?.getD 0#32).toNat / 2 = uip.toNat / 2 := by
    rintro ⟨i, hi, hiv⟩
    have hkept := hbtPres.lvlArr_kept i hi; rw [hiv, hpresSw.lvlArr] at hkept
    have hle := hinvBt.assign.trl_lvl_le (uip.toNat / 2) (by rw [hnv_eq]; omega)
    rw [hkept, huip_lvl, hlvlBt] at hle; omega
  have huip_v0 : ksBt.vals[uip.toNat]? = some 0#32 := by
    have hlen : uip.toNat < ksBt.vals.length := by
      rw [hinvBt.shapes.vals_len]; rw [hnv_eq] at hnv; omega
    have h0 : ksBt.vals[uip.toNat]?.getD 0#32 = 0#32 := by
      by_cases h : ksBt.vals[uip.toNat]?.getD 0#32 = 0#32
      · exact h
      · exact absurd ((hinvBt.assign.vals_nz_iff_trl uip.toNat
        (by rw [hnv_eq]; exact huip_lt)).mp h) huip_none
    rw [List.getElem?_eq_getElem hlen] at h0 ⊢; exact congrArg some h0
  have hte_lt_nv : ksBt.trl_end.toNat < ksBt.nv.toNat :=
    k6_trl_end_lt_of_unassigned hinvBt.shapes hnv hinvBt.assign (by rw [hnv_eq]; exact huip_lt)
      (by simp [huip_v0])
  have htrl_len_bt : ksBt.trl_end.toNat ≤ ksBt.trl.length := by
    rw [hinvBt.shapes.trl_len]; have := hinvBt.assign.trl_end_le; omega
  have htrl_len_ks : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [← hpresSw.trl, ← hpresSw.trl_end, hinvSw.shapes.trl_len]
    have := hinvSw.assign.trl_end_le; have := hinvSw.clauses.nv_le; omega
  refine ⟨huip_none, huip_v0, hte_lt_nv, ?_, ?_, ?_⟩
  · intro l hl hval hlv
    obtain ⟨j, hj, hjeq⟩ :=
      k6_falsified_to_trail hinvSw.assign hsyncSw (by rw [hpresSw.nv]; exact hl) hval
    have hj_lv : (stSw.lvlArr[(stSw.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        jlvl.toNat := by rw [hjeq, k6a_xor1_div2, hpresSw.lvlArr]; exact hlv
    have hj_bt := hB1 j hj hj_lv
    exact ⟨j, hj_bt, by rw [htrl_i j hj_bt, ← hpresSw.trl, hjeq]⟩
  · intro d hd
    obtain ⟨i, hi_bt, hd_eq, hpos_bt, hrsn_bt⟩ := (k6_mem_trailDecisions_iff htrl_len_bt).mp hd
    have hi_ks : i < ks.trl_end.toNat := by rw [← hpresSw.trl_end]; omega
    have hkept := hbtPres.lvlArr_kept i hi_bt
    have hrsn_k := (hbtKept i hi_bt).2.1
    rw [htrl_i i hi_bt] at hd_eq hkept hrsn_k
    rw [hpresSw.lvlArr] at hkept; rw [hpresSw.rsn] at hrsn_k
    have hpos_ks : 0 < (ks.lvlArr[d / 2]?.getD 0#32).toNat := by
      rw [← hd_eq, ← hkept, hd_eq]; exact hpos_bt
    have hrsn_ks : ks.rsn[d / 2]?.getD 0#32 = 0xFFFFFFFF#32 := by
      rw [← hd_eq, ← hrsn_k, hd_eq]; exact hrsn_bt
    have hd_ks : d ∈ k6TrailDecisions ks :=
      (k6_mem_trailDecisions_iff htrl_len_ks).mpr ⟨i, hi_ks, hd_eq, hpos_ks, hrsn_ks⟩
    have hlv_le : (ks.lvlArr[d / 2]?.getD 0#32).toNat ≤ jlvl.toNat := by
      have h1 := (hbtKept i hi_bt).2.2; rw [htrl_i i hi_bt, hkept, hd_eq] at h1; exact h1
    exact ⟨i, hi_ks, hd_eq, hd_ks, hlv_le⟩
  · intro i hi hlv
    have hi_bt := hB1 i (by rw [hpresSw.trl_end]; exact hi)
      (by rw [hpresSw.lvlArr, hpresSw.trl]; exact hlv)
    have hkept := hbtPres.lvlArr_kept i hi_bt
    rw [htrl_i i hi_bt, hpresSw.lvlArr] at hkept
    exact ⟨hi_bt, htrl_i i hi_bt, hkept⟩

private theorem k6a_assignStep_decisions_eq {L : K6Layout} {P : (Nat → Bool) → Prop}
    {ks : K6State} {lit rsn : BitVec 32} (hinv : K6Inv L P ks)
    (hlit : lit.toNat < 2 * ks.nv.toNat) (hte_lt : ks.trl_end.toNat < ks.nv.toNat)
    (hunass : ¬ ∃ i < ks.trl_end.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = lit.toNat / 2)
    (hnot_dec : ks.lvl = 0#32 ∨ rsn ≠ 0xFFFFFFFF#32) :
    let ks' := k6AssignStep ks lit rsn
    k6TrailDecisions ks' = k6TrailDecisions ks ∧
    (0 < ks'.lvl.toNat → ∃ i < ks'.trl_end.toNat,
      ks'.lvlArr[(ks'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 = ks'.lvl) ∧
    (∀ i < ks.trl_end.toNat, i < ks'.trl_end.toNat ∧ ks'.trl[i]? = ks.trl[i]? ∧
      ks'.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]? =
        ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?) := by
  intro ks'
  have hm := L.hmaxV; have hnv := hinv.clauses.nv_le
  have hte1 : (ks.trl_end + 1#32).toNat = ks.trl_end.toNat + 1 := by bv_omega
  have hv_eq : (lit >>> 1).toNat = lit.toNat / 2 := (k6_bv32_div2_lt hlit).1
  have hte_len : ks.trl_end.toNat < ks.trl.length := by rw [hinv.shapes.trl_len]; omega
  have hv_len : lit.toNat / 2 < ks.lvlArr.length := by rw [hinv.shapes.lvlArr_len]; omega
  have hr_len : lit.toNat / 2 < ks.rsn.length := by rw [hinv.shapes.rsn_len]; omega
  have htr_self : ks'.trl[ks.trl_end.toNat]? = some lit := List.getElem?_set_self hte_len
  have htr_old : ∀ k < ks.trl_end.toNat, ks'.trl[k]? = ks.trl[k]? := fun k hk =>
    List.getElem?_set_ne (by omega)
  have hlv_self : ks'.lvlArr[lit.toNat / 2]? = some ks.lvl := by
    dsimp only [ks', k6AssignStep]; rw [hv_eq]; exact List.getElem?_set_self hv_len
  have hlv_ne : ∀ v, v ≠ lit.toNat / 2 → ks'.lvlArr[v]? = ks.lvlArr[v]? := fun v hne => by
    dsimp only [ks', k6AssignStep]; rw [hv_eq]; exact List.getElem?_set_ne (Ne.symm hne)
  have hrs_self : ks'.rsn[lit.toNat / 2]? = some rsn := by
    dsimp only [ks', k6AssignStep]; rw [hv_eq]; exact List.getElem?_set_self hr_len
  have hrs_ne : ∀ v, v ≠ lit.toNat / 2 → ks'.rsn[v]? = ks.rsn[v]? := fun v hne => by
    dsimp only [ks', k6AssignStep]; rw [hv_eq]; exact List.getElem?_set_ne (Ne.symm hne)
  have htrl_take : ks'.trl.take ks'.trl_end.toNat = ks.trl.take ks.trl_end.toNat ++ [lit] := by
    change (ks.trl.set ks.trl_end.toNat lit).take (ks.trl_end + 1#32).toNat = _
    rw [hte1, List.take_add_one, List.take_set_of_le (Nat.le_refl _),
      List.getElem?_set_self hte_len, Option.toList_some]
  have hnot_cond : ¬ (0 < ks.lvl.toNat ∧ rsn = 0xFFFFFFFF#32) := by
    rcases hnot_dec with h0 | hne
    · rw [h0]; simp
    · exact fun h => hne h.2
  refine ⟨?_,
    fun _ => ⟨ks.trl_end.toNat, (by change ks.trl_end.toNat < (ks.trl_end + 1#32).toNat; omega),
      by rw [htr_self, Option.getD_some, hlv_self, Option.getD_some]; rfl⟩,
    fun i hi => ⟨(by change i < (ks.trl_end + 1#32).toNat; omega), htr_old i hi,
      hlv_ne _ fun h => hunass ⟨i, hi, h⟩⟩⟩
  unfold k6TrailDecisions
  rw [htrl_take, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
    hlv_self, hrs_self, Option.getD_some, Option.getD_some, k6a_ite_f hnot_cond, List.append_nil]
  refine k6a_filterMap_congr fun x hx => ?_
  rw [List.mem_take_iff_getElem] at hx; obtain ⟨i, hi, rfl⟩ := hx
  have hne_v : (ks.trl[i]'(by omega)).toNat / 2 ≠ lit.toNat / 2 := fun h =>
    hunass ⟨i, by omega, by
      rw [List.getElem?_eq_getElem (by omega : i < ks.trl.length), Option.getD_some]; exact h⟩
  rw [hlv_ne _ hne_v, hrs_ne _ hne_v]

private structure K6AnaBrkPost (L : K6Layout) (P : (Nat → Bool) → Prop) (ks : K6State)
    (uip : BitVec 32) (st : K6State) : Prop where
  sh : st.ShapesOk L
  pres : K6AnaPreserved ks st
  nkl_pos : 1 ≤ st.nkl.toNat
  nkl_le : st.nkl.toNat ≤ st.nv.toNat
  nana_le : st.nana.toNat ≤ st.nv.toNat
  ana_lt : ∀ i < st.nana.toNat, (st.ana[i]?.getD 0#32).toNat < st.nv.toNat
  flags_seen : ∀ v < st.nv.toNat,
    ((st.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32) ↔
      ∃ i < st.nana.toNat, (st.ana[i]?.getD 0#32).toNat = v
  uip_ok : uip ≠ 0xFFFFFFFF#32 →
    uip.toNat < 2 * st.nv.toNat ∧ st.lvlArr[uip.toNat / 2]?.getD 0#32 = st.lvl ∧
    (∀ i, 1 ≤ i → i < st.nkl.toNat →
      let l := (st.kl[i]?.getD 0#32).toNat
      l < 2 * st.nv.toNat ∧ 0 < (st.lvlArr[l / 2]?.getD 0#32).toNat ∧
      (st.lvlArr[l / 2]?.getD 0#32).toNat < st.lvl.toNat ∧ st.vals[l]? = some 2#32) ∧
    SemEntails P (uip.toNat :: ((st.kl.take st.nkl.toNat).drop 1).map BitVec.toNat)

private theorem k6AnaBrkPost_of_uip_ff {L : K6Layout} {P : (Nat → Bool) → Prop} {ks st : K6State}
    {idx : Nat} (hinv : K6AnaInv L P st idx) (hp : K6AnaPreserved ks st) :
    K6AnaBrkPost L P ks 0xFFFFFFFF#32 st :=
  ⟨hinv.shapes, hp, hinv.nkl_pos, hinv.nkl_le, hinv.nana_le, hinv.ana_lt, hinv.flags_seen,
   fun h => absurd rfl h⟩

/-- `13/39`: Parametric `Func.wp` proof for `full_k6_analyze`. -/
theorem full_k6_analyze_wp (Γ : Env)
    (hAnaCl : M6EnvSpec Γ "full_k6_ana_clause" k6AnaClauseSpec)
    (hBt : M6EnvSpec Γ "full_k6_backtrack" k6BacktrackSpec)
    (hMtf : M6EnvSpec Γ "full_k6_mtf" k6MtfSpec)
    (hWatch : M6EnvSpec Γ "full_k6_watch" k6WatchSpec)
    (hAssign : M6EnvSpec Γ "full_k6_assign" k6AssignSpec) :
    ∀ args m Q X, k6AnalyzeSpec args m Q X → Func.wp Γ full_k6_analyze_body args m Q X := by
  rintro ⟨kPtr, confl_cid, ⟨⟩⟩ m Q X ⟨L, P, ks, R, hinv, hsync, hlvl_pos, hlvl_wit,
    hconfl_lt, hconfl_fals, hm, hQ⟩
  have hm_v := L.hmaxV; have hac := L.hacap; have hsh := hinv.shapes; have hnv := hinv.clauses.nv_le
  have hmv : ks.max_v = L.mv32 := hinv.clauses.max_v_eq
  have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [hsh.trl_len]; have := hinv.assign.trl_end_le; omega
  have hvdec : ∃ v < ks.nv.toNat, ks.lvlArr[v]?.getD 0#32 = ks.lvl := by
    obtain ⟨i0, hi0, hl0⟩ := hlvl_wit
    have hlt := hinv.assign.trl_lt _ (k6_mem_trailLits_of_lt hi0 htrl_len)
    exact ⟨(ks.trl[i0]?.getD 0#32).toNat / 2, by omega, hl0⟩
  have hret_false : ∀ (ks' : K6State) (m' : Mem 64),
      K6Inv L P ks' → K6TrailSynced ks' → ks'.nv = ks.nv → ks'.nassump = ks.nassump →
      ks'.assump = ks.assump → ks'.incons = ks.incons → ks'.status = ks.status →
      ks'.neq = ks.neq → (K6Mem L kPtr ks' ⋆ R) m' → Q (false, ()) m' :=
    fun ks' m' hi hsy h1 h2 h3 h4 h5 h6 hm' =>
      hQ false ks' m' hi hsy h1 h2 h3 h4 h5 h6 (fun h => by cases h) hm'
  have hmA := k6Mem_to_amem hsh hm; clear hm
  c0_hsteps_nogrp
  rw [hmv]
  c0_hsteps_nogrp
  let ks0 : K6State := { ks with nkl := 1#32, nana := 0#32, openCnt := 0#32 }
  obtain ⟨hinv0, hpres0⟩ := k6a_init_anaInv hinv hsync hlvl_pos hvdec
  have hm0 : (K6Mem L kPtr ks0 ⋆ R) m := by
    obtain ⟨_, hm0'⟩ := k6MemA_to_mem hm
    exact Eq.mp (congrArg (fun x => (K6Mem L kPtr x ⋆ R) _) (by k6_ext)) hm0'
  c0_call hAnaCl
  refine ⟨L, P, ks0, ks.trl_end.toNat, R, hinv0, hconfl_lt, hvdec, ?_,
    fun h => absurd rfl h, hm0, fun ks1 m1 hinv1 hpres1 hent1 _ hm1 => ?_⟩
  · intro l hl _
    have hwf := hinv.clauses.cl_wf confl_cid.toNat hconfl_lt
    refine ⟨hconfl_fals l hl, fun _ => ?_⟩
    exact k6_falsified_to_trail hinv.assign hsync (hwf.2.2.1 l hl) (hconfl_fals l hl)
  · have hpres_k1 := k6AnaPreserved_trans hpres0 hpres1
    dsimp only [Arg.val] at hm1
    have hm1A := k6Mem_to_amem hinv1.shapes hm1; clear hm1 hm hm0
    c0_hsteps_nogrp
    refine wp_while_break_state
      (brkTs := [i32, i32]) (lpTs := [i32]) (β := BitVec 32 × BitVec 32 × K6State)
      (fun b => (b.1, b.2.1, ()))
      (fun b mb => K6AnaBrkPost L P ks b.2.1 b.2.2 ∧ (K6MemA L kPtr b.2.2 ⋆ R) mb)
      (α := BitVec 32 × K6State) (fun p => (p.1, ())) (fun p => p.1.toNat)
      (fun p ml => K6AnaInv L P p.2 p.1.toNat ∧ K6AnaPreserved ks p.2 ∧
        SemEntails P (k6ResolventLits p.2 p.1.toNat) ∧ (K6MemA L kPtr p.2 ⋆ R) ml)
      ?_ ?_ ?_
    · rintro B ⟨_, uip, stB⟩ mB ⟨hBrk, hmB⟩
      dsimp only at hBrk hmB ⊢
      have hnvB : stB.nv = ks.nv := hBrk.pres.nv
      have hna_mv : stB.nana.toNat ≤ L.maxV := by have := hBrk.nana_le; rw [hnvB] at this; omega
      have hnk_mv : stB.nkl.toNat ≤ L.maxV := by have := hBrk.nkl_le; rw [hnvB] at this; omega
      c0_hsteps_nogrp
      refine wp_while_state1 (fun p : BitVec 32 × List (BitVec 32) => p.1)
        (fun p => stB.nana.toNat - p.1.toNat)
        (fun p mf => p.1.toNat ≤ stB.nana.toNat ∧ p.2.length = L.maxV ∧
          (∀ v < stB.nv.toNat, (∃ j < p.1.toNat, (stB.ana[j]?.getD 0#32).toNat = v) →
            (p.2[v]?.getD 0#32 &&& 2#32) = 0#32) ∧
          (∀ v < stB.nv.toNat, (stB.flags[v]?.getD 0#32 &&& 2#32) = 0#32 →
            (p.2[v]?.getD 0#32 &&& 2#32) = 0#32) ∧
          (K6MemA L kPtr { stB with flags := p.2 } ⋆ R) mf) ?_ ?_
      · intro Lf hLf
        exact hLf (0#32, stB.flags) mB
          ⟨Nat.zero_le _, hBrk.sh.flags_len, fun _ _ ⟨_, hj, _⟩ => by simp at hj,
           fun _ _ h => h, by simpa using hmB⟩
      · rintro Lf ⟨ai, fls⟩ mf ⟨hai_le, hfls_len, hcl_done, hcl_orig, hmf⟩ ihf
        dsimp only at hai_le hfls_len hcl_done hcl_orig hmf ⊢
        obtain ⟨stF, hstF⟩ : ∃ x : K6State, x = { stB with flags := fls } := ⟨_, rfl⟩
        rw [← hstF] at hmf
        c0_hsplit
        · have hai_lt : ai.toNat < stB.nana.toNat := by rw [hstF] at hc; exact hc
          have hai_mv : ai.toNat < szV L := by unfold szV; omega
          have hav_lt : (stB.ana[ai.toNat]?.getD 0#32).toNat < stB.nv.toNat :=
            hBrk.ana_lt ai.toNat hai_lt
          have hav_mv : (stF.ana[ai.toNat]?.getD 0#32).toNat < szV L := by
            unfold szV; rw [hstF]; change (stB.ana[ai.toNat]?.getD 0#32).toNat < L.maxV
            rw [hnvB] at hav_lt; omega
          have hai1 : (ai + 1#32).toNat = ai.toNat + 1 := by bv_omega
          c0_hsteps!
          let av := (stB.ana[ai.toNat]?.getD 0#32).toNat
          let fls' := fls.set av (fls[av]?.getD 0#32 &&& ~~~2#32)
          have hav_len : av < fls.length := by rw [hfls_len]; rw [hnvB] at hav_lt; omega
          refine ihf (ai + 1#32, fls') _ (by dsimp only; rw [hai1]; omega)
            ⟨by dsimp only; rw [hai1]; omega, by simp [fls', hfls_len], ?_, ?_, ?_⟩
          · intro v hv ⟨j, hj, hjeq⟩; dsimp only at hj; rw [hai1] at hj
            by_cases hvv : v = av
            · subst hvv; simp only [fls', List.getElem?_set_self hav_len, Option.getD_some]
              exact k6a_fl_andnot2_and2_zero _
            · simp only [fls', List.getElem?_set_ne (Ne.symm hvv)]
              by_cases hja : j = ai.toNat
              · subst hja; exact absurd hjeq.symm hvv
              · exact hcl_done v hv ⟨j, by omega, hjeq⟩
          · intro v hv h0; by_cases hvv : v = av
            · subst hvv; simp only [fls', List.getElem?_set_self hav_len, Option.getD_some]
              exact k6a_fl_andnot2_and2_zero _
            · simp only [fls', List.getElem?_set_ne (Ne.symm hvv)]; exact hcl_orig v hv h0
          · refine Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ R) _) ?_) hm
            rw [hstF]; k6_ext
        · have hai_eq : ai.toNat = stB.nana.toNat := by
            have h1 : ¬ ai.toNat < stF.nana.toNat := hc
            rw [hstF] at h1; dsimp only at h1; omega
          have hfl_clean : ∀ v < stF.nv.toNat, (stF.flags[v]?.getD 0#32 &&& 2#32) = 0#32 := by
            intro v hv; rw [hstF] at hv ⊢; dsimp only at hv ⊢
            by_cases hnz : (stB.flags[v]?.getD 0#32 &&& 2#32) = 0#32
            · exact hcl_orig v hv hnz
            · exact hcl_done v hv (by rw [hai_eq]; exact (hBrk.flags_seen v hv).mp hnz)
          have hshF : stF.ShapesOk L := by
            rw [hstF]; exact { hBrk.sh with flags_len := hfls_len }
          have hpresF : K6AnaPreserved ks stF := by
            rw [hstF]
            exact ⟨hBrk.pres.nv, hBrk.pres.nc, hBrk.pres.lvl, hBrk.pres.prop, hBrk.pres.trl_end,
              hBrk.pres.unass, hBrk.pres.incons, hBrk.pres.alen, hBrk.pres.acap, hBrk.pres.nassump,
              hBrk.pres.status, hBrk.pres.max_v, hBrk.pres.max_orig, hBrk.pres.max_cl,
              hBrk.pres.neq, hBrk.pres.lvlArr, hBrk.pres.rsn, hBrk.pres.trl, hBrk.pres.vals,
              hBrk.pres.assump, hBrk.pres.whead, hBrk.pres.wnext, hBrk.pres.wblit, hBrk.pres.clOff,
              hBrk.pres.clSz, hBrk.pres.arena⟩
          have ⟨hinvF, hsyncF⟩ := k6a_inv_of_ana_clean hinv hsync hshF hpresF
            (by rw [hstF]; exact hnk_mv) (by rw [hstF]; exact hna_mv) hfl_clean
          c0_hsplit
          · c0_hsteps!; obtain ⟨_, hmF⟩ := k6MemA_to_mem hmf
            exact hret_false stF mf hinvF hsyncF hpresF.nv hpresF.nassump hpresF.assump
              hpresF.incons hpresF.status hpresF.neq hmF
          · have huip_ne : uip ≠ 0xFFFFFFFF#32 := ‹_›
            obtain ⟨huip_lt, huip_lvl, hkl_ntB, hent_uip⟩ := hBrk.uip_ok huip_ne
            have huip_lt_k : uip.toNat < 2 * ks.nv.toNat := by rwa [hnvB] at huip_lt
            have huip_lvl_k : ks.lvlArr[uip.toNat / 2]?.getD 0#32 = ks.lvl := by
              rwa [hBrk.pres.lvlArr, hBrk.pres.lvl] at huip_lvl
            have hkl_ntF : ∀ i, 1 ≤ i → i < stF.nkl.toNat →
                let l := (stF.kl[i]?.getD 0#32).toNat
                l < 2 * stF.nv.toNat ∧ 0 < (stF.lvlArr[l / 2]?.getD 0#32).toNat ∧
                (stF.lvlArr[l / 2]?.getD 0#32).toNat < stF.lvl.toNat ∧
                stF.vals[l]? = some 2#32 := by rw [hstF]; exact hkl_ntB
            let stKl0 := stF.putArr .kl 0 uip
            c0_hsteps_nogrp
            refine wp_while_state_pure (ts := [i32, i32, i32])
              (α := BitVec 32 × BitVec 32 × BitVec 32) (fun t => (t.1, t.2.1, t.2.2, ()))
              (fun t => stF.nkl.toNat - t.2.2.toNat)
              (fun t => 1 ≤ t.2.2.toNat ∧ t.2.2.toNat ≤ stF.nkl.toNat ∧
                t.1.toNat < ks.lvl.toNat ∧
                (t.2.2.toNat = 1 → t.1 = 0#32 ∧ t.2.1 = 1#32) ∧
                (2 ≤ t.2.2.toNat → 1 ≤ t.2.1.toNat ∧ t.2.1.toNat < t.2.2.toNat ∧
                  0 < t.1.toNat ∧
                  stF.lvlArr[(stF.kl[t.2.1.toNat]?.getD 0#32).toNat / 2]?.getD 0#32 = t.1) ∧
                (∀ k, 1 ≤ k → k < t.2.2.toNat →
                  (stF.lvlArr[(stF.kl[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ t.1.toNat))
              ?_ ?_
            · intro L3 hL3
              exact wp_jump_state
                (proj := fun t : BitVec 32 × BitVec 32 × BitVec 32 => (t.1, t.2.1, t.2.2, ()))
                (0#32, 1#32, 1#32) rfl
                (hL3 (0#32, 1#32, 1#32) ⟨by decide, by rw [hstF]; exact hBrk.nkl_pos,
                  hlvl_pos, fun _ => ⟨rfl, rfl⟩, fun h => by simp at h,
                  fun k h1 h2 => by simp at h2; omega⟩)
            · rintro L3 ⟨jlvl, wi, i⟩ ⟨hi1, hi_le, hj_lt, hi_eq1, hi_ge2, hall_le⟩ ih3
              dsimp only at hi1 hi_le hj_lt hi_eq1 hi_ge2 hall_le ⊢
              have hkl0_nkl : stKl0.nkl = stF.nkl := by dsimp only [stKl0]; k6_field
              c0_hsplit
              · have hi_lt : i.toNat < stF.nkl.toNat := by rw [← hkl0_nkl]; exact hc
                have hi_mv : i.toNat < szV L := by
                  unfold szV; rw [hstF] at hi_lt; dsimp only at hi_lt; omega
                have hkl0_i : stKl0.kl[i.toNat]? = stF.kl[i.toNat]? := by
                  dsimp only [stKl0]; k6_field; exact List.getElem?_set_ne (by omega)
                have hnt_i := hkl_ntF i.toNat hi1 hi_lt; dsimp only at hnt_i
                have hlv_div : (stKl0.kl[i.toNat]?.getD 0#32 >>> 1).toNat =
                    (stF.kl[i.toNat]?.getD 0#32).toNat / 2 := by
                  rw [hkl0_i]; exact (k6_bv32_div2_lt hnt_i.1).1
                have hlv_mv : (stKl0.kl[i.toNat]?.getD 0#32 >>> 1).toNat < szV L := by
                  unfold szV; rw [hlv_div]; have := hinvF.clauses.nv_le; omega
                have hi1_add : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
                have hil_pos : 0 < (stF.lvlArr[(stF.kl[i.toNat]?.getD 0#32).toNat / 2]?.getD
                    0#32).toNat := hnt_i.2.1
                have hil_lt : (stF.lvlArr[(stF.kl[i.toNat]?.getD 0#32).toNat / 2]?.getD
                    0#32).toNat < ks.lvl.toNat := by rw [← hpresF.lvl]; exact hnt_i.2.2.1
                have hkl0_lv : stKl0.lvlArr = stF.lvlArr := by dsimp only [stKl0]; k6_field
                c0_hsteps!
                · let il := stF.lvlArr[(stF.kl[i.toNat]?.getD 0#32).toNat / 2]?.getD 0#32
                  have hgt : jlvl.toNat < il.toNat := by
                    dsimp only [il]; rw [← hlv_div, ← hkl0_lv]; exact hc
                  rw [hkl0_lv, hlv_div]
                  refine ih3 (il, i, i + 1#32) (by dsimp only; rw [hi1_add]; omega)
                    ⟨by dsimp only; rw [hi1_add]; omega, by dsimp only; rw [hi1_add]; omega,
                     hil_lt, fun h => by dsimp only at h; rw [hi1_add] at h; omega,
                     fun _ => ⟨hi1, by dsimp only; rw [hi1_add]; omega, hil_pos, rfl⟩,
                     fun k hk1 hk_lt => by
                       dsimp only at hk_lt ⊢; rw [hi1_add] at hk_lt
                       by_cases hki : k = i.toNat
                       · subst hki; exact Nat.le_refl _
                       · have := hall_le k hk1 (by omega); dsimp only [il] at hgt ⊢; omega⟩
                · let il := stF.lvlArr[(stF.kl[i.toNat]?.getD 0#32).toNat / 2]?.getD 0#32
                  have hle : il.toNat ≤ jlvl.toNat := by
                    have h1 : ¬ jlvl.toNat < (stKl0.lvlArr[(stKl0.kl[i.toNat]?.getD 0#32 >>>
                        1).toNat]?.getD 0#32).toNat := hc
                    rw [hkl0_lv, hlv_div] at h1; dsimp only [il]; omega
                  have hi_ge2_cur : 2 ≤ i.toNat := by
                    by_cases h1 : i.toNat = 1
                    · have hj0 := (hi_eq1 h1).1; rw [hj0] at hle; simp at hle
                      dsimp only [il] at hle; omega
                    · omega
                  obtain ⟨hw1, hw_lt, hj_pos, hw_lvl⟩ := hi_ge2 hi_ge2_cur
                  refine ih3 (jlvl, wi, i + 1#32) (by dsimp only; rw [hi1_add]; omega)
                    ⟨by dsimp only; rw [hi1_add]; omega, by dsimp only; rw [hi1_add]; omega,
                     hj_lt, fun h => by dsimp only at h; rw [hi1_add] at h; omega,
                     fun _ => ⟨hw1, by dsimp only; rw [hi1_add]; omega, hj_pos, hw_lvl⟩,
                     fun k hk1 hk_lt => by
                       dsimp only at hk_lt ⊢; rw [hi1_add] at hk_lt
                       by_cases hki : k = i.toNat
                       · subst hki; exact hle
                       · exact hall_le k hk1 (by omega)⟩
              · have hi_eq : i.toNat = stF.nkl.toNat := by
                  have h1 : ¬ i.toNat < stKl0.nkl.toNat := hc; rw [hkl0_nkl] at h1; omega
                rw [hi_eq] at hi_eq1 hi_ge2 hall_le
                let stSw := if 2 ≤ stF.nkl.toNat ∧ wi ≠ 1#32 then
                  (stKl0.putArr .kl 1 (stKl0.kl[wi.toNat]?.getD 0#32)).putArr .kl wi.toNat
                    (stKl0.kl[1]?.getD 0#32)
                  else stKl0
                obtain ⟨hinvSw, hsyncSw, hpresSwF, hsw_nkl, hsw_nana, hsw_ana, hsw0, hsw_mem,
                  hsw_nt⟩ := k6a_swap_kl_preserves hinvF hsyncF (by rw [hstF]; exact hBrk.nkl_pos)
                    (by rw [hstF]; exact hBrk.nkl_le) (fun h2 => ⟨(hi_ge2 h2).1, (hi_ge2 h2).2.1⟩)
                    (fun k hk1 hk_lt => let h := hkl_ntF k hk1 hk_lt
                      ⟨h.1, h.2.1, hall_le k hk1 hk_lt, h.2.2.2⟩)
                have hpresSw := k6AnaPreserved_trans hpresF hpresSwF
                c0_hsteps_nogrp
                refine wp_join0 (fun m4 => (K6MemA L kPtr stSw ⋆ R) m4) ?_ ?_
                · intro J4 m4 hm4
                  obtain ⟨_, hm4_bt⟩ := k6MemA_to_mem hm4
                  c0_hsteps_nogrp; c0_call hBt
                  refine ⟨L, P, stSw, R, hinvSw, Or.inr hsyncSw, hm4_bt,
                    fun ksBt mBt hinvBt hsyncBt hlvlBt hte_le hbtPres hbtKept hB1 hmBt => ?_⟩
                  dsimp only [Arg.val] at hlvlBt
                  obtain ⟨huip_none, huip_v0, hte_lt_nv, hkl_bt_trl, hdec_ks, hA2_bt⟩ :=
                    k6a_after_bt_facts hinvSw hsyncSw hpresSw huip_lt_k huip_lvl_k hj_lt
                      hinvBt hlvlBt hte_le hbtPres hbtKept hB1
                  have hbt_nv : ksBt.nv = ks.nv := hbtPres.nv.trans hpresSw.nv
                  have hbt_na : ksBt.nassump = ks.nassump := hbtPres.nassump.trans hpresSw.nassump
                  have hbt_as : ksBt.assump = ks.assump := hbtPres.assump.trans hpresSw.assump
                  have hbt_in : ksBt.incons = ks.incons := hbtPres.incons.trans hpresSw.incons
                  have hbt_st : ksBt.status = ks.status := hbtPres.status.trans hpresSw.status
                  have hbt_nq : ksBt.neq = ks.neq := hbtPres.neq.trans hpresSw.neq
                  have hbt_nkl : ksBt.nkl = stF.nkl := hbtPres.nkl.trans hsw_nkl
                  have hmBtA := k6Mem_to_amem hinvBt.shapes hmBt; clear hmBt hm4 hm4_bt
                  c0_hsteps_nogrp
                  refine wp_while_state1 (fun p : BitVec 32 × K6State => p.1)
                    (fun p => ksBt.nana.toNat - p.1.toNat)
                    (fun p m5 => p.1.toNat ≤ ksBt.nana.toNat ∧
                      (∃ qf ql qs qst qp qn qsa, p.2 =
                        { ksBt with qfirst := qf, qlast := ql, qsearch := qs, qstamp := qst,
                                    qprev := qp, qnext := qn, qstampArr := qsa }) ∧
                      p.2.ShapesOk L ∧ (K6MemA L kPtr p.2 ⋆ R) m5) ?_ ?_
                  · intro L5 hL5
                    exact wp_jump_state (proj := fun p : BitVec 32 × K6State => (p.1, ()))
                      (0#32, ksBt) rfl
                      (hL5 (0#32, ksBt) mBt ⟨Nat.zero_le _,
                        ⟨ksBt.qfirst, ksBt.qlast, ksBt.qsearch, ksBt.qstamp, ksBt.qprev,
                         ksBt.qnext, ksBt.qstampArr, rfl⟩, hinvBt.shapes, hmBtA⟩)
                  · rintro L5 ⟨ai5, st5⟩ m5 ⟨hai5_le, hq5, hsh5, hm5⟩ ih5
                    dsimp only at hai5_le hq5 hsh5 hm5 ⊢
                    obtain ⟨qf, ql, qs, qst, qp, qn, qsa, hst5_eq⟩ := hq5
                    c0_hsplit
                    · have hai5_lt : ai5.toNat < ksBt.nana.toNat := by rw [hst5_eq] at hc; exact hc
                      have hai5_mv : ai5.toNat < szV L := by
                        unfold szV; have := hinvBt.clauses.nana_le; omega
                      have hai5_1 : (ai5 + 1#32).toNat = ai5.toNat + 1 := by bv_omega
                      c0_hsteps_nogrp; obtain ⟨_, hm5_m⟩ := k6MemA_to_mem hm5
                      c0_call hMtf
                      refine ⟨L, st5, R, hsh5, by rw [hst5_eq]; exact hinvBt.clauses.max_v_eq,
                        by rw [hst5_eq]; exact hinvBt.clauses.nv_le, hm5_m,
                        fun qf' ql' qs' qst' qp' qn' qsa' m5' hsh5' hm5' => ?_⟩
                      c0_hsteps!
                      let st5' : K6State :=
                        { st5 with qfirst := qf', qlast := ql', qsearch := qs', qstamp := qst',
                                   qprev := qp', qnext := qn', qstampArr := qsa' }
                      refine ih5 (ai5 + 1#32, st5') m5' (by dsimp only; rw [hai5_1]; omega)
                        ⟨by dsimp only; rw [hai5_1]; omega,
                         ⟨qf', ql', qs', qst', qp', qn', qsa', by dsimp only [st5']; rw [hst5_eq]⟩,
                         hsh5', k6Mem_to_amem hsh5' hm5'⟩
                    · have hinv5 : K6Inv L P st5 := by
                        rw [hst5_eq] at hsh5 ⊢
                        exact k6a_setQueue_preserves_inv hinvBt hsh5.qprev_len hsh5.qnext_len
                          hsh5.qstampArr_len
                      have hsync5 : K6TrailSynced st5 := by rw [hst5_eq]; exact hsyncBt
                      have hent_kl5 :
                          SemEntails P ((st5.kl.take st5.nkl.toNat).map BitVec.toNat) := by
                        rw [hst5_eq, hbtPres.kl, hbtPres.nkl]
                        have huip' : SemEntails P (uip.toNat ::
                            ((stF.kl.take stF.nkl.toNat).drop 1).map BitVec.toNat) := by
                          rw [hstF]; exact hent_uip
                        refine k6a_semEntails_subset (fun x hx => ?_) huip'
                        dsimp only [stSw, stKl0]; rw [hsw_nkl]; exact hsw_mem x hx
                      c0_hsplit
                      · have hnkl1 : stF.nkl = 1#32 := by rw [← hkl0_nkl]; exact hc
                        have hj0 : jlvl = 0#32 := (hi_eq1 (by rw [hnkl1]; decide)).1
                        have hkl_take1 : (st5.kl.take st5.nkl.toNat).map BitVec.toNat =
                            [uip.toNat] := by
                          rw [hst5_eq, hbtPres.kl, hbt_nkl, hnkl1]
                          change (stSw.kl.take 1).map BitVec.toNat = [uip.toNat]
                          rw [List.take_add_one, List.take_zero, List.nil_append, hsw0,
                            Option.toList_some]; rfl
                        rw [hkl_take1] at hent_kl5
                        obtain ⟨_, hm5_a⟩ := k6MemA_to_mem hm5
                        c0_hsteps_nogrp; c0_call hAssign
                        refine ⟨L, st5, R, hsh5, hinv5.clauses.max_v_eq,
                          Nat.lt_of_lt_of_le huip_lt_k (by omega),
                          by rw [hst5_eq]
                             exact Nat.lt_of_lt_of_le hte_lt_nv (by rw [hbt_nv]; omega),
                          hm5_a, fun mFin hmFin => ?_⟩
                        c0_hsteps!; dsimp only [Arg.val] at hmFin
                        have hst5_lvl0 : st5.lvl = 0#32 := by rw [hst5_eq, hlvlBt, hj0]
                        obtain ⟨hinvFin, hsyncFin⟩ := k6AssignStep_preserves_inv hinv5 hsync5
                          (lit := uip) (rsn := 0xFFFFFFFF#32)
                          (by rw [hst5_eq, hbt_nv]; exact huip_lt_k)
                          (by rw [hst5_eq]; exact huip_v0) (fun _ => hent_kl5)
                          (fun h => by rw [hst5_lvl0] at h; simp at h) (Or.inl rfl)
                        obtain ⟨hdecFin, hlwFin, htrFin⟩ := k6a_assignStep_decisions_eq hinv5
                          (lit := uip) (rsn := 0xFFFFFFFF#32)
                          (by rw [hst5_eq, hbt_nv]; exact huip_lt_k)
                          (by rw [hst5_eq]; exact hte_lt_nv)
                          (by rw [hst5_eq]; exact huip_none) (Or.inl hst5_lvl0)
                        have f_lvl : (k6AssignStep st5 uip 0xFFFFFFFF#32).lvl = jlvl := by
                          change st5.lvl = jlvl; rw [hst5_eq, hlvlBt]
                        have f_dec : k6TrailDecisions (k6AssignStep st5 uip 0xFFFFFFFF#32) =
                            k6TrailDecisions ksBt := by
                          rw [hdecFin]; unfold k6TrailDecisions; rw [hst5_eq]
                        exact hQ true (k6AssignStep st5 uip 0xFFFFFFFF#32) mFin hinvFin hsyncFin
                          (by rw [hst5_eq]; exact hbt_nv) (by rw [hst5_eq]; exact hbt_na)
                          (by rw [hst5_eq]; exact hbt_as) (by rw [hst5_eq]; exact hbt_in)
                          (by rw [hst5_eq]; exact hbt_st) (by rw [hst5_eq]; exact hbt_nq)
                          (fun _ => ⟨by rw [f_lvl]; exact hj_lt, hlwFin,
                            fun d hd => by rw [f_dec] at hd; rw [f_lvl]; exact hdec_ks d hd,
                            fun i hi hlv => by
                              rw [f_lvl] at hlv
                              obtain ⟨hi_bt, ht_bt, hl_bt⟩ := hA2_bt i hi hlv
                              obtain ⟨hi_f, ht_f, hl_f⟩ := htrFin i (by rw [hst5_eq]; exact hi_bt)
                              have ht_f' : (k6AssignStep st5 uip 0xFFFFFFFF#32).trl[i]? =
                                  ksBt.trl[i]? := ht_f.trans (by rw [hst5_eq])
                              have hl_f' : (k6AssignStep st5 uip 0xFFFFFFFF#32).lvlArr[
                                  (ks.trl[i]?.getD 0#32).toNat / 2]? =
                                  ksBt.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]? := by
                                have h1 := hl_f
                                have htr_st5 : st5.trl[i]? = ks.trl[i]? := by
                                  rw [hst5_eq]; exact ht_bt
                                rw [htr_st5] at h1; exact h1.trans (by rw [hst5_eq])
                              exact ⟨hi_f, ht_f'.trans ht_bt, hl_f'.trans hl_bt⟩⟩) hmFin
                      · have hnkl_ne1 : stF.nkl ≠ 1#32 := by rw [← hkl0_nkl]; exact hc
                        have hnkl_ge2 : 2 ≤ stF.nkl.toNat := by
                          have h1 : 1 ≤ stF.nkl.toNat := by rw [hstF]; exact hBrk.nkl_pos
                          have hne : stF.nkl.toNat ≠ 1 := fun h =>
                            hnkl_ne1 (BitVec.eq_of_toNat_eq h)
                          omega
                        have hca5 : st5.acap.toNat = L.acap := by
                          rw [hinv5.clauses.acap_eq, BitVec.toNat_ofNat,
                            Nat.mod_eq_of_lt (by unfold dimacsBound at hac; omega)]
                        have hmc5 : st5.max_cl.toNat = L.maxCl := by
                          rw [hinv5.clauses.max_cl_eq, BitVec.toNat_ofNat,
                            Nat.mod_eq_of_lt (by unfold K6Layout.maxCl; omega)]
                        try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                        c0_hsplit
                        · c0_hsteps!; obtain ⟨_, hm5'⟩ := k6MemA_to_mem hm5
                          exact hret_false st5 m5 hinv5 hsync5 (by rw [hst5_eq]; exact hbt_nv)
                            (by rw [hst5_eq]; exact hbt_na) (by rw [hst5_eq]; exact hbt_as)
                            (by rw [hst5_eq]; exact hbt_in) (by rw [hst5_eq]; exact hbt_st)
                            (by rw [hst5_eq]; exact hbt_nq) hm5'
                        · have hnc_lt : st5.nc.toNat < L.maxCl := by
                            have hnl : ¬ st5.max_cl.toNat ≤ st5.nc.toNat := hc
                            rw [hmc5] at hnl; omega
                          c0_hsplit
                          · c0_hsteps!; obtain ⟨_, hm5'⟩ := k6MemA_to_mem hm5
                            exact hret_false st5 m5 hinv5 hsync5 (by rw [hst5_eq]; exact hbt_nv)
                              (by rw [hst5_eq]; exact hbt_na) (by rw [hst5_eq]; exact hbt_as)
                              (by rw [hst5_eq]; exact hbt_in) (by rw [hst5_eq]; exact hbt_st)
                              (by rw [hst5_eq]; exact hbt_nq) hm5'
                          · have hfit : st5.alen.toNat + st5.nkl.toNat ≤ L.acap := by
                              have hnk5 : st5.nkl = stF.nkl := by rw [hst5_eq]; exact hbt_nkl
                              have h1 : ¬ st5.acap.toNat < (st5.alen + stKl0.nkl).toNat := hc
                              rw [hca5, hkl0_nkl, ← hnk5] at h1
                              have := hinv5.clauses.alen_le; have := hinv5.clauses.nkl_le
                              unfold dimacsBound at hac; bv_omega
                            c0_hsteps_nogrp
                            refine wp_while_state1 (fun p : BitVec 32 × List (BitVec 32) => p.1)
                              (fun p => st5.nkl.toNat - p.1.toNat)
                              (fun p m7 => p.1.toNat ≤ st5.nkl.toNat ∧ p.2.length = L.acap ∧
                                (∀ k < st5.alen.toNat, p.2[k]? = st5.arena[k]?) ∧
                                (∀ k < p.1.toNat, p.2[st5.alen.toNat + k]? = st5.kl[k]?) ∧
                                (K6MemA L kPtr { st5 with arena := p.2 } ⋆ R) m7) ?_ ?_
                            · intro L7 hL7
                              exact wp_jump_state
                                (proj := fun p : BitVec 32 × List (BitVec 32) => (p.1, ()))
                                (0#32, st5.arena) rfl
                                (hL7 (0#32, st5.arena) m5 ⟨Nat.zero_le _, hsh5.arena_len,
                                  fun _ _ => rfl, fun _ h => by simp at h, by simpa using hm5⟩)
                            · rintro L7 ⟨i7, ar7⟩ m7 ⟨hi7_le, har7_len, har7_old, har7_lits, hm7⟩
                                ih7
                              dsimp only at hi7_le har7_len har7_old har7_lits hm7 ⊢
                              obtain ⟨st7, hst7⟩ : ∃ x : K6State, x = { st5 with arena := ar7 } :=
                                ⟨_, rfl⟩
                              rw [← hst7] at hm7
                              c0_hsplit
                              · have hi7_lt : i7.toNat < st5.nkl.toNat := by
                                  have : st5.nkl = stKl0.nkl := by rw [hst5_eq, hbt_nkl, hkl0_nkl]
                                  rw [this]; exact hc
                                have hi7_mv : i7.toNat < szV L := by
                                  unfold szV; have := hinv5.clauses.nkl_le; omega
                                have hoff7_cap : st5.alen.toNat + i7.toNat < L.acap := by omega
                                have hoff7_32 : st5.alen.toNat + i7.toNat < 2 ^ 32 := by
                                  unfold dimacsBound at hac; omega
                                have hoff7_eq : (st5.alen + i7).toNat =
                                    st5.alen.toNat + i7.toNat := by
                                  rw [BitVec.toNat_add, Nat.mod_eq_of_lt hoff7_32]
                                have hoff7_ar : (st5.alen + i7).toNat < szAr L := by
                                  unfold szAr; rw [hoff7_eq]; exact hoff7_cap
                                have hi7_1 : (i7 + 1#32).toNat = i7.toNat + 1 := by bv_omega
                                c0_hsteps!
                                let ar7' := ar7.set (st5.alen.toNat + i7.toNat)
                                  (st5.kl[i7.toNat]?.getD 0#32)
                                refine ih7 (i7 + 1#32, ar7') _ (by dsimp only; rw [hi7_1]; omega)
                                  ⟨by dsimp only; rw [hi7_1]; omega, by simp [ar7', har7_len],
                                   fun k hk => by rw [List.getElem?_set_ne (by omega)]
                                                  exact har7_old k hk,
                                   fun k hk => by
                                     rw [hi7_1] at hk; by_cases hki : k = i7.toNat
                                     · subst hki
                                       rw [List.getElem?_set_self (by omega),
                                         List.getElem?_eq_getElem (by rw [hsh5.kl_len]; omega),
                                         Option.getD_some]
                                     · rw [List.getElem?_set_ne (by omega)]
                                       exact har7_lits k (by omega), ?_⟩
                                refine Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ R) _) ?_) hm
                                rw [hst7]; k6_ext; simp only [hoff7_eq]; rfl
                              · have hi7_eq : i7.toNat = st5.nkl.toNat := by
                                  have h1 : ¬ i7.toNat < stKl0.nkl.toNat := hc
                                  have h2 : st5.nkl = stKl0.nkl := by
                                    rw [hst5_eq, hbt_nkl, hkl0_nkl]
                                  rw [← h2] at h1; omega
                                rw [hi7_eq] at har7_lits
                                have hnc_len : st5.nc.toNat < szCl L := by unfold szCl; exact hnc_lt
                                have hkl5_lt : ∀ k < st5.nkl.toNat,
                                    (st5.kl[k]?.getD 0#32).toNat < 2 * st5.nv.toNat := by
                                  intro k hk; rw [hst5_eq, hbtPres.nkl] at hk
                                  rw [hst5_eq, hbtPres.kl, hbtPres.nv]
                                  by_cases hk0 : k = 0
                                  · subst hk0; rw [hsw0, Option.getD_some, hpresSw.nv]
                                    exact huip_lt_k
                                  · exact (hsw_nt k (by omega) hk).1
                                have hnkl5_ge2 : 2 ≤ st5.nkl.toNat := by
                                  rw [hst5_eq, hbt_nkl]; exact hnkl_ge2
                                have hnkl5_mv : st5.nkl.toNat ≤ L.maxV := hinv5.clauses.nkl_le
                                have hkl5_len : st5.kl.length = L.maxV := hsh5.kl_len
                                have hkl5_0 : st5.kl[0]?.getD 0#32 = uip := by
                                  rw [hst5_eq, hbtPres.kl, hsw0, Option.getD_some]
                                have hkl0_lt : (st5.kl[0]?.getD 0#32).toNat < 2 * st5.nv.toNat :=
                                  hkl5_lt 0 (by omega)
                                have hkl1_lt : (st5.kl[1]?.getD 0#32).toNat < 2 * st5.nv.toNat :=
                                  hkl5_lt 1 (by omega)
                                c0_hsteps_nogrp
                                let stM := (((({ st5 with arena := ar7 } : K6State).putHdr .alen
                                    (st5.alen + st5.nkl)).putArr .clOff st5.nc.toNat
                                    st5.alen).putArr .clSz st5.nc.toNat st5.nkl).putHdr .nc
                                    (st5.nc + 1#32)
                                have hstM_eq : (((((st7.putHdr .alen (st5.alen + stKl0.nkl)).putArr
                                    .clOff st5.nc.toNat st5.alen).putArr .clSz st5.nc.toNat
                                    stKl0.nkl).putHdr .nc (st5.nc + 1#32))) = stM := by
                                  have h2 : stKl0.nkl = st5.nkl := by
                                    rw [hst5_eq, hbt_nkl, hkl0_nkl]
                                  rw [hst7, h2]
                                have hshM : stM.ShapesOk L := by
                                  have h0 : ({ st5 with arena := ar7 } : K6State).ShapesOk L :=
                                    { hsh5 with arena_len := har7_len }
                                  exact (((h0.putHdr .alen _).putArr .clOff _ _).putArr .clSz _
                                    _).putHdr .nc _
                                obtain ⟨_, hmM⟩ := k6MemA_to_mem hm
                                change (K6Mem L kPtr (((((st7.putHdr .alen
                                  (st5.alen + stKl0.nkl)).putArr .clOff st5.nc.toNat
                                  st5.alen).putArr .clSz st5.nc.toNat stKl0.nkl).putHdr .nc
                                  (st5.nc + 1#32))) ⋆ R) _ at hmM
                                rw [hstM_eq] at hmM
                                have hnv5 := hinv5.clauses.nv_le
                                c0_call hWatch
                                refine ⟨L, stM, R, hshM,
                                  by dsimp only [stM]; k6_field; exact hinv5.clauses.max_v_eq,
                                  hnc_lt,
                                  by dsimp only [Arg.val, stM]; rw [hst7]; k6_field; omega,
                                  by dsimp only [Arg.val, stM]; rw [hst7]; k6_field; omega,
                                  hmM, fun mW hmW => ?_⟩
                                dsimp only [Arg.val] at hmW
                                have hget0 : st5.kl[0]'(by omega) = st5.kl[0]?.getD 0#32 := by
                                  simp [List.getElem?_eq_getElem (by omega : 0 < st5.kl.length)]
                                have hget1 : st5.kl[1]'(by omega) = st5.kl[1]?.getD 0#32 := by
                                  simp [List.getElem?_eq_getElem (by omega : 1 < st5.kl.length)]
                                have hnkl5_28 : st5.nkl.toNat < 2 ^ 28 := by omega
                                obtain ⟨hinvW, hsyncW, w_lvl, w_nv, w_na, w_as, w_te, _, w_inc,
                                  _⟩ :=
                                  k6AddClause_ge2_preserves hinv5 hsync5 hnc_lt hnkl5_ge2 hnkl5_28
                                    (by omega) hfit har7_len har7_old har7_lits hkl5_lt hent_kl5
                                rw [hget0, hget1] at hinvW hsyncW w_lvl w_nv w_na w_as w_te w_inc
                                let stW := k6WatchStep stM st5.nc (st5.kl[0]?.getD 0#32)
                                  (st5.kl[1]?.getD 0#32)
                                have hstW_eq : k6WatchStep stM st5.nc
                                    (stM.kl[0]?.getD 0#32) (stM.kl[1]?.getD 0#32) = stW := by
                                  dsimp only [stW, stM]; k6_field
                                have hstM_eq' : (((((st7.putHdr .alen
                                    (st5.alen + (stF.putArr K6ArrField.kl 0 uip).nkl)).putArr
                                    .clOff st5.nc.toNat st5.alen).putArr .clSz st5.nc.toNat
                                    (stF.putArr K6ArrField.kl 0 uip).nkl).putHdr .nc
                                    (st5.nc + 1))) = stM := by
                                  have h2 : (stF.putArr K6ArrField.kl 0 uip).nkl = st5.nkl := by
                                    rw [hst5_eq, hbt_nkl]; exact hkl0_nkl
                                  rw [hst7, h2]; rfl
                                rw [hstM_eq'] at hmW
                                rw [hstW_eq] at hmW
                                dsimp only
                                c0_hsteps_nogrp; c0_call hAssign
                                refine ⟨L, stW, R, hinvW.shapes, hinvW.clauses.max_v_eq,
                                  by dsimp only [Arg.val]
                                     exact Nat.lt_of_lt_of_le huip_lt_k (by omega),
                                  by rw [w_te, hst5_eq]
                                     exact Nat.lt_of_lt_of_le hte_lt_nv (by rw [hbt_nv]; omega),
                                  hmW, fun mFin hmFin => ?_⟩
                                c0_hsteps!; dsimp only [Arg.val] at hmFin
                                have hnc_ne : st5.nc ≠ 0xFFFFFFFF#32 := by
                                  unfold K6Layout.maxCl at hnc_lt; bv_omega
                                have hnc1 : (st5.nc + 1#32).toNat = st5.nc.toNat + 1 := by
                                  unfold K6Layout.maxCl at hnc_lt; bv_omega
                                have hstW_nc : stW.nc = st5.nc + 1#32 := by
                                  dsimp only [stW, k6WatchStep, k6WatchStep0, stM]; k6_field
                                have hnc_ltW : st5.nc.toNat < stW.nc.toNat := by
                                  rw [hstW_nc, hnc1]; omega
                                have hstW_lits : k6ClauseLits stW st5.nc.toNat =
                                    (st5.kl.take st5.nkl.toNat).map BitVec.toNat := by
                                  have hoffW : k6ClauseOff stW st5.nc.toNat = st5.alen.toNat := by
                                    unfold k6ClauseOff; dsimp only [stW, k6WatchStep, k6WatchStep0,
                                      stM]; k6_field
                                    rw [List.getElem?_set_self (by rw [hsh5.clOff_len]; omega),
                                      Option.getD_some]
                                  have hszW : k6ClauseSize stW st5.nc.toNat = st5.nkl.toNat := by
                                    unfold k6ClauseSize; dsimp only [stW, k6WatchStep, k6WatchStep0,
                                      stM]; k6_field
                                    rw [List.getElem?_set_self (by rw [hsh5.clSz_len]; omega),
                                      Option.getD_some]
                                  have harW : stW.arena = ar7 := by
                                    dsimp only [stW, k6WatchStep, k6WatchStep0, stM]; k6_field
                                  unfold k6ClauseLits; rw [hoffW, hszW, harW]; congr 1
                                  apply List.ext_getElem
                                  · simp [List.length_take, List.length_drop, har7_len, hkl5_len]
                                    omega
                                  · intro k hk1 _; have hk_n : k < st5.nkl.toNat := by
                                      simp [List.length_take] at hk1; omega
                                    simp only [List.getElem_take, List.getElem_drop]
                                    have hg := har7_lits k hk_n
                                    rw [List.getElem?_eq_getElem (by omega),
                                      List.getElem?_eq_getElem (by omega)] at hg
                                    exact Option.some.inj hg
                                have huip_memW : uip.toNat ∈ k6ClauseLits stW st5.nc.toNat := by
                                  rw [hstW_lits, List.mem_map]
                                  refine ⟨uip, ?_, rfl⟩
                                  rw [List.mem_take_iff_getElem]
                                  refine ⟨0, by omega, ?_⟩
                                  have := hkl5_0
                                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
                                  exact this
                                have hjlvl_pos : 0 < jlvl.toNat := (hi_ge2 hnkl_ge2).2.2.1
                                have hstW_lvl_pos : 0 < stW.lvl.toNat := by
                                  rw [w_lvl, hst5_eq, hlvlBt]; exact hjlvl_pos
                                have hstW_trl : stW.trl = ksBt.trl := by
                                  dsimp only [stW, k6WatchStep, k6WatchStep0, stM]; k6_field
                                  rw [hst5_eq]
                                have hstW_vals : stW.vals = ksBt.vals := by
                                  dsimp only [stW, k6WatchStep, k6WatchStep0, stM]; k6_field
                                  rw [hst5_eq]
                                have hstW_rsn : stW.rsn = ksBt.rsn := by
                                  dsimp only [stW, k6WatchStep, k6WatchStep0, stM]; k6_field
                                  rw [hst5_eq]
                                have hstW_lvlArr : stW.lvlArr = ksBt.lvlArr := by
                                  dsimp only [stW, k6WatchStep, k6WatchStep0, stM]; k6_field
                                  rw [hst5_eq]
                                have hstW_st : stW.status = ks.status := by
                                  have h1 : stW.status = st5.status := by
                                    dsimp only [stW, k6WatchStep, k6WatchStep0, stM]; k6_field
                                  rw [h1, hst5_eq]; exact hbt_st
                                have hstW_nq : stW.neq = ks.neq := by
                                  have h1 : stW.neq = st5.neq := by
                                    dsimp only [stW, k6WatchStep, k6WatchStep0, stM]; k6_field
                                  rw [h1, hst5_eq]; exact hbt_nq
                                have hothersW : ∀ x ∈ k6ClauseLits stW st5.nc.toNat, x ≠ uip.toNat →
                                    ∃ j < stW.trl_end.toNat, (stW.trl[j]?.getD 0#32).toNat =
                                      x ^^^ 1 := by
                                  intro x hx hne; rw [hstW_lits, List.mem_map] at hx
                                  obtain ⟨b, hb, rfl⟩ := hx
                                  rw [List.mem_take_iff_getElem] at hb; obtain ⟨k, hk, rfl⟩ := hb
                                  have hk_n : k < st5.nkl.toNat := by omega
                                  have hk_pos : 1 ≤ k := by
                                    by_cases hk0 : k = 0
                                    · exfalso; subst hk0; apply hne; have := hkl5_0
                                      rw [List.getElem?_eq_getElem (by omega),
                                        Option.getD_some] at this
                                      rw [this]
                                    · omega
                                  have hswk := hsw_nt k hk_pos (by rw [hst5_eq, hbtPres.nkl] at hk_n
                                                                   exact hk_n)
                                  dsimp only at hswk
                                  have hst5_kl : st5.kl = ksBt.kl := by rw [hst5_eq]
                                  have hst5_te : st5.trl_end = ksBt.trl_end := by rw [hst5_eq]
                                  have hgetk : (stSw.kl[k]?.getD 0#32).toNat =
                                      (st5.kl[k]'(by omega)).toNat := by
                                    rw [← hbtPres.kl, ← hst5_kl,
                                      List.getElem?_eq_getElem (by omega), Option.getD_some]
                                  rw [hgetk] at hswk
                                  rw [w_te, hst5_te, hstW_trl]
                                  exact hkl_bt_trl _ (by rw [← hpresSw.nv]; exact hswk.1)
                                    hswk.2.2.2 (by rw [← hpresSw.lvlArr]; exact hswk.2.2.1)
                                obtain ⟨hinvFin, hsyncFin⟩ := k6AssignStep_preserves_inv hinvW
                                  hsyncW (lit := uip) (rsn := st5.nc)
                                  (by rw [w_nv, hst5_eq, hbt_nv]; exact huip_lt_k)
                                  (by rw [hstW_vals]; exact huip_v0)
                                  (fun h => by rw [h] at hstW_lvl_pos; simp at hstW_lvl_pos)
                                  (fun _ h => absurd h hnc_ne)
                                  (Or.inr ⟨hnc_ltW, huip_memW, hothersW⟩)
                                obtain ⟨hdecFin, hlwFin, htrFin⟩ := k6a_assignStep_decisions_eq
                                  hinvW (lit := uip) (rsn := st5.nc)
                                  (by rw [w_nv, hst5_eq, hbt_nv]; exact huip_lt_k)
                                  (by rw [w_te, w_nv, hst5_eq]; exact hte_lt_nv)
                                  (by rw [hstW_trl, w_te, hst5_eq]; exact huip_none)
                                  (Or.inr hnc_ne)
                                have f_lvl : (k6AssignStep stW uip st5.nc).lvl = jlvl := by
                                  change stW.lvl = jlvl; rw [w_lvl, hst5_eq, hlvlBt]
                                have f_dec : k6TrailDecisions (k6AssignStep stW uip st5.nc) =
                                    k6TrailDecisions ksBt := by
                                  rw [hdecFin]; unfold k6TrailDecisions
                                  rw [hstW_trl, hstW_lvlArr, hstW_rsn, w_te, hst5_eq]
                                exact hQ true (k6AssignStep stW uip st5.nc) mFin hinvFin hsyncFin
                                  (w_nv.trans (by rw [hst5_eq]; exact hbt_nv))
                                  (w_na.trans (by rw [hst5_eq]; exact hbt_na))
                                  (w_as.trans (by rw [hst5_eq]; exact hbt_as))
                                  (w_inc.trans (by rw [hst5_eq]; exact hbt_in))
                                  hstW_st hstW_nq
                                  (fun _ => ⟨by rw [f_lvl]; exact hj_lt, hlwFin,
                                    fun d hd => by rw [f_dec] at hd; rw [f_lvl]; exact hdec_ks d hd,
                                    fun i hi hlv => by
                                      rw [f_lvl] at hlv
                                      obtain ⟨hi_bt, ht_bt, hl_bt⟩ := hA2_bt i hi hlv
                                      obtain ⟨hi_f, ht_f, hl_f⟩ :=
                                        htrFin i (by rw [w_te, hst5_eq]; exact hi_bt)
                                      rw [hstW_trl] at ht_f hl_f; rw [hstW_lvlArr, ht_bt] at hl_f
                                      exact ⟨hi_f, ht_f.trans ht_bt, hl_f.trans hl_bt⟩⟩) hmFin
                · intro J4 hJ4
                  try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                  c0_hsplit
                  · have hnkl_ge2 : 2 ≤ stF.nkl.toNat := by rw [← hkl0_nkl]; bv_omega
                    c0_hsplit
                    · have hwi_ne1 : wi ≠ 1#32 := ‹_›
                      have hwi_lt := (hi_ge2 hnkl_ge2).2.1
                      have hwi_mv : wi.toNat < szV L := by
                        unfold szV; rw [hstF] at hwi_lt; dsimp only at hwi_lt; omega
                      c0_hsteps!
                      refine hJ4 _ (Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ R) _) ?_) hm)
                      dsimp only [stSw]; rw [k6a_ite_t ⟨hnkl_ge2, hwi_ne1⟩]
                    · have hwi_eq1 : wi = 1#32 := by
                        first | exact ‹_› | exact Classical.not_not.mp ‹_›
                      c0_hsteps!
                      refine hJ4 _ (Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ R) _) ?_) hm)
                      dsimp only [stSw]; rw [k6a_ite_f (fun h => h.2 hwi_eq1)]
                  · have hnkl_lt2 : ¬ 2 ≤ stF.nkl.toNat := by rw [← hkl0_nkl]; bv_omega
                    c0_hsteps!
                    refine hJ4 _ (Eq.mp (congrArg (fun x => (K6MemA L kPtr x ⋆ R) _) ?_) hm)
                    dsimp only [stSw]; rw [k6a_ite_f (fun h => hnkl_lt2 h.1)]
    · rintro B L' ⟨idx_bv, st⟩ mL hB hL ⟨hinvL, hpresL, hentL, hmL⟩
      dsimp only at hinvL hpresL hentL hmL
      c0_hsplit
      · have hop_pos : 0 < st.openCnt.toNat := by bv_omega
        c0_hsplit
        · c0_hsteps!
          exact hB (idx_bv, 0xFFFFFFFF#32, st) mL ⟨k6AnaBrkPost_of_uip_ff hinvL hpresL, hmL⟩
        · have hidx_pos : 0 < idx_bv.toNat := by bv_omega
          have hidx_sub : (idx_bv - 1#32).toNat = idx_bv.toNat - 1 := by bv_omega
          have hidx'_lt : idx_bv.toNat - 1 < st.trl_end.toNat := by have := hinvL.idx_le; omega
          have hidx'_mv : (idx_bv - 1#32).toNat < szV L := by
            unfold szV; rw [hidx_sub]; have := hinvL.assign.trl_end_le; have := hinvL.nv_le; omega
          have htrl_lenL : st.trl_end.toNat ≤ st.trl.length := by
            rw [hinvL.shapes.trl_len]; have := hinvL.assign.trl_end_le; have := hinvL.nv_le; omega
          let p := st.trl[idx_bv.toNat - 1]?.getD 0#32
          have hp_lt : p.toNat < 2 * st.nv.toNat :=
            hinvL.assign.trl_lt _ (k6_mem_trailLits_of_lt hidx'_lt htrl_lenL)
          obtain ⟨hpv_eq, hpv_lt⟩ := k6_bv32_div2_lt hp_lt
          have hpv_mv : (p >>> 1).toNat < szV L := by unfold szV; have := hinvL.nv_le; omega
          have hidx_succ : idx_bv.toNat = (idx_bv.toNat - 1) + 1 := by omega
          have hinvL' : K6AnaInv L P st ((idx_bv.toNat - 1) + 1) := by
            rwa [← hidx_succ]
          have hentL' : SemEntails P (k6ResolventLits st ((idx_bv.toNat - 1) + 1)) := by
            rwa [← hidx_succ]
          have hp_eq : st.trl[(idx_bv - 1#32).toNat]?.getD 0#32 = p := by rw [hidx_sub]
          have hpv_mv' : (st.trl[(idx_bv - 1#32).toNat]?.getD 0#32 >>> 1).toNat < szV L := by
            rw [hp_eq]; exact hpv_mv
          c0_hsteps_nogrp
          try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
          try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
          c0_hsplit
          · have hfl_hit : (st.flags[p.toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32 := by
              rw [← hpv_eq, ← hp_eq]; exact ‹_›
            c0_hsplit
            · have hlvl_hit : st.lvlArr[p.toNat / 2]?.getD 0#32 = st.lvl := by
                rw [← hpv_eq, ← hp_eq, hpresL.lvl, ← hpres_k1.lvl]; exact ‹_›
              obtain ⟨_, hinv1, hpres1, hres_hit⟩ :=
                k6a_resolvent_step_hit hinvL' ⟨hfl_hit, hlvl_hit⟩
              have hent_hit : SemEntails P ((p.toNat ^^^ 1) ::
                  k6ResolventLits { st with openCnt := st.openCnt - 1#32 } (idx_bv.toNat - 1)) :=
                k6a_semEntails_subset hres_hit hentL'
              let st1 := st.putHdr .openCnt (st.openCnt - 1#32)
              have hst1_eq : st1 = { st with openCnt := st.openCnt - 1#32 } := by k6_ext
              c0_hsplit
              · have hop0 : st1.openCnt = 0#32 := by dsimp only [st1]; k6_field; exact ‹_›
                c0_hsteps!
                have hkl_eq := k6a_uip_exit hinv1 (by rw [← hst1_eq]; exact hop0)
                rw [hkl_eq] at hent_hit
                have huip_eq : (p ^^^ 1#32).toNat = p.toNat ^^^ 1 := by simp
                have huip_lt : (p ^^^ 1#32).toNat < 2 * st1.nv.toNat := by
                  rw [huip_eq]; change p.toNat ^^^ 1 < 2 * st.nv.toNat
                  rcases k6_nat_xor1_cases p.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
                have huip_lvl : st1.lvlArr[(p ^^^ 1#32).toNat / 2]?.getD 0#32 = st1.lvl := by
                  rw [huip_eq, k6a_xor1_div2]; exact hlvl_hit
                rw [show st.trl[(idx_bv - 1).toNat]?.getD 0#32 = p from hp_eq]
                refine hB (idx_bv - 1#32, p ^^^ 1#32, st1) _ ⟨⟨hinv1.shapes,
                  k6AnaPreserved_trans hpresL hpres1, hinv1.nkl_pos, hinv1.nkl_le, hinv1.nana_le,
                  hinv1.ana_lt, hinv1.flags_seen, fun _ => ⟨huip_lt, huip_lvl,
                    fun i hi1 hi2 => let hk := hinv1.kl_nonTop i hi1 hi2
                      ⟨hk.1, hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2⟩,
                    by rw [huip_eq, hst1_eq]; exact hent_hit⟩⟩, hm⟩
              · have hst1_pos : 0 < ({ st with openCnt :=
                st.openCnt - 1#32 } : K6State).openCnt.toNat := by
                  have hne : (st.putHdr .openCnt (st.openCnt - 1#32)).openCnt ≠ 0#32 := ‹_›
                  dsimp only [K6State.putHdr] at hne ⊢; bv_omega
                obtain ⟨_, _, _, hrsn_ne, hrsn_lt, hp_mem, hp_uniq, hoth⟩ :=
                  k6a_rsn_pre hinv1 hidx'_lt hst1_pos hlvl_hit
                c0_hsplit
                · exfalso
                  have heq : st.rsn[(st.trl[(idx_bv - 1#32).toNat]?.getD 0#32 >>> 1).toNat]?.getD
                      0#32 = 0xFFFFFFFF#32 := ‹_›
                  rw [hp_eq] at heq; exact hrsn_ne heq
                · obtain ⟨_, hm1_m⟩ := k6MemA_to_mem hm
                  change (K6Mem L kPtr st1 ⋆ R) _ at hm1_m
                  rw [hst1_eq] at hm1_m
                  have hp_eq' : st.trl[(idx_bv - 1).toNat]?.getD 0#32 = p := hp_eq
                  c0_call hAnaCl
                  refine ⟨L, P, { st with openCnt := st.openCnt - 1#32 }, idx_bv.toNat - 1, R,
                    hinv1, by dsimp only [Arg.val, K6State.putHdr]; rw [hp_eq']; exact hrsn_lt,
                    ⟨p.toNat / 2, by dsimp only; omega, hlvl_hit⟩,
                    fun l hl hne => ?_, fun _ => ?_, hm1_m,
                    fun ks2 m2 hinv2 hpres2 hent2 _ hm2 => ?_⟩
                  · dsimp only [Arg.val, K6State.putHdr] at hl hne
                    rw [hp_eq'] at hl hne
                    have h1 := hoth l hl (by rw [hpv_eq] at hne; exact hne)
                    exact ⟨h1.1, fun _ => h1.2⟩
                  · dsimp only [Arg.val, K6State.putHdr]
                    rw [hp_eq']
                    refine ⟨p.toNat, hp_mem, hpv_eq.symm, fun l' hl' hlv' => hp_uniq l' hl' hlv',
                      by rw [hpv_eq]; exact hfl_hit, by rw [hpv_eq]; exact hlvl_hit, hent_hit⟩
                  · c0_hsteps!; dsimp only [Arg.val] at hm2
                    refine hL (idx_bv - 1#32, ks2) m2 (by dsimp only; rw [hidx_sub]; omega)
                      ⟨by dsimp only; rw [hidx_sub]; exact hinv2,
                       k6AnaPreserved_trans hpresL (k6AnaPreserved_trans hpres1 hpres2),
                       by dsimp only; rw [hidx_sub]; exact hent2,
                       k6Mem_to_amem hinv2.shapes hm2⟩
            · have hlvl_ne : st.lvlArr[p.toNat / 2]?.getD 0#32 ≠ st.lvl := by
                rw [← hpv_eq, ← hp_eq, hpresL.lvl, ← hpres_k1.lvl]; exact ‹_›
              obtain ⟨hinvS, hresS⟩ := k6a_resolvent_step_skip hinvL' (fun h => hlvl_ne h.2)
              c0_hsteps!
              refine hL (idx_bv - 1#32, st) mL (by dsimp only; rw [hidx_sub]; omega)
                ⟨by dsimp only; rw [hidx_sub]; exact hinvS, hpresL,
                 by dsimp only; rw [hidx_sub, ← hresS]; exact hentL', hmL⟩
          · have hfl_0 : (st.flags[p.toNat / 2]?.getD 0#32 &&& 2#32) = 0#32 := by
              rw [← hpv_eq, ← hp_eq]; exact ‹_›
            obtain ⟨hinvS, hresS⟩ := k6a_resolvent_step_skip hinvL' (fun h => h.1 hfl_0)
            c0_hsteps!
            refine hL (idx_bv - 1#32, st) mL (by dsimp only; rw [hidx_sub]; omega)
              ⟨by dsimp only; rw [hidx_sub]; exact hinvS, hpresL,
               by dsimp only; rw [hidx_sub, ← hresS]; exact hentL', hmL⟩
      · c0_hsteps!
        exact hB (idx_bv, 0xFFFFFFFF#32, st) mL ⟨k6AnaBrkPost_of_uip_ff hinvL hpresL, hmL⟩
    · intro B L' hB hL
      exact wp_jump_state (proj := fun p : BitVec 32 × K6State => (p.1, ()))
        (ks1.trl_end, ks1) rfl
        (hL (ks1.trl_end, ks1) m1
          ⟨by rw [hpres_k1.trl_end]; exact hinv1, hpres_k1,
           by rw [hpres_k1.trl_end]; exact hent1, hm1A⟩)

end LeanQbe.T.Examples.Kissat.FullM6Sweep
