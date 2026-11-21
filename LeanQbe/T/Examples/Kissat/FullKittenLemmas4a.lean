module

public import LeanQbe.T.Examples.Kissat.FullKittenSpec1
public import LeanQbe.T.Examples.Kissat.FullKittenLemmas1

/-!
# Kissat `D-Full` Scratch `kitten` 1UIP Clause-Analysis `Func.wp` Proof (`Part 4a`)

Proves parametric `(Γ : Env)` `Func.wp` contracts for the `2` 1UIP conflict-analysis functions:
- `full_kitten_ana_clause_wp` (`[11]`): per-clause literal analysis, flag/seen-variable recording,
  lower-level learned-clause collection, level-0 antecedent tracking, and resolution soundness.
- `full_kitten_analyze_wp` (`[12]`): 1UIP resolution loop, flag cleanup, jump-level selection,
  backtrack + VMTF bump, unit/multi-literal clause learning, watch attachment, and UIP assignment.
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

/-! ## 1. Pure Bitvector, List, & Step Model Helpers -/

theorem kana_ite_t {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

theorem kana_ite_f {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬c) :
    (if c then a else b) = b := by simp [h]

private theorem kana_fl_or2_and2_nz (x : BitVec 32) :
    ((x ||| 2#32) &&& 2#32) ≠ 0#32 := by
  intro h
  have h1 := congrArg (fun b : BitVec 32 => b[1]) h
  revert h1; simp

theorem kana_fl_andnot2_and2_zero (x : BitVec 32) :
    ((x &&& ~~~2#32) &&& 2#32) = 0#32 := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]
  by_cases h1 : i = 1
  · subst h1; simp
  · have h2 : (2#32 : BitVec 32)[i] = false := by revert i hi h1; decide
    simp [h2]

theorem kana_nodup_subset_length {n : Nat} :
    ∀ {xs : List Nat}, xs.Nodup → (∀ x ∈ xs, x < n) → xs.length ≤ n := by
  induction n with
  | zero =>
    intro xs _ hlt
    cases xs with
    | nil => simp
    | cons x _ => exact absurd (hlt x List.mem_cons_self) (by omega)
  | succ k ih =>
    intro xs hnd hlt
    by_cases hmem : k ∈ xs
    · have hnd' : (xs.erase k).Nodup := hnd.erase k
      have hlt' : ∀ x ∈ xs.erase k, x < k := by
        intro x hx
        have hne : x ≠ k := fun heq => by
          subst heq; exact absurd hx (List.Nodup.not_mem_erase hnd)
        have := hlt x (List.mem_of_mem_erase hx); omega
      have hlen := List.length_erase_of_mem hmem
      have := ih hnd' hlt'
      omega
    · have hlt' : ∀ x ∈ xs, x < k := fun x hx => by
        have := hlt x hx; have : x ≠ k := fun heq => hmem (heq ▸ hx); omega
      exact Nat.le_trans (ih hnd hlt') (Nat.le_succ k)

private theorem kana_filter_length_flip_one {α : Type} [DecidableEq α]
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
      simp only [List.filter_cons, hP, hQ, heq, Bool.false_eq_true, ↓reduceIte,
        List.length_cons]
    · have hxa : x ≠ a := fun heq => hx_not (heq ▸ ha_tl)
      have hqx : Q x = P x := hother x List.mem_cons_self hxa
      have hrec := ih hnd_tl ha_tl (fun y hy => hother y (List.mem_cons_of_mem _ hy))
      simp only [List.filter_cons, hqx]
      cases P x <;> simp [hrec]

private theorem kana_mem_clauseLits_iff {ks : KittenState} {cid : Nat}
    (hbd : kittenClauseOff ks cid + kittenClauseSize ks cid ≤ ks.arena.length) {l : Nat} :
    l ∈ kittenClauseLits ks cid ↔
      ∃ n < kittenClauseSize ks cid,
        (ks.arena[kittenClauseOff ks cid + n]?.getD 0#32).toNat = l := by
  unfold kittenClauseLits
  rw [List.mem_map]
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [List.mem_iff_getElem] at hb
    obtain ⟨n, hn, rfl⟩ := hb
    have hn_sz : n < kittenClauseSize ks cid := by simp [List.length_take] at hn; omega
    have hlt : kittenClauseOff ks cid + n < ks.arena.length := by omega
    refine ⟨n, hn_sz, ?_⟩
    simp [List.getElem_take, List.getElem_drop, List.getElem?_eq_getElem hlt]
  · rintro ⟨n, hn, rfl⟩
    have hlt : kittenClauseOff ks cid + n < ks.arena.length := by omega
    refine ⟨ks.arena[kittenClauseOff ks cid + n]'hlt, ?_, ?_⟩
    · rw [List.mem_iff_getElem]
      exact ⟨n, by simp [List.length_take, List.length_drop]; omega,
        by simp [List.getElem_take, List.getElem_drop]⟩
    · simp [List.getElem?_eq_getElem hlt]

theorem kana_trl_nodup_var_ne {acap : Nat} {ks : KittenState} (hsh : ks.ShapesOk acap)
    (hnv : ks.nv.toNat ≤ kMaxV) (hba : KittenBaseAssignOk ks)
    {i j : Nat} (hi : i < ks.trl_end.toNat) (hj : j < ks.trl_end.toNat) (hne : i ≠ j) :
    (ks.trl[i]?.getD 0#32).toNat / 2 ≠ (ks.trl[j]?.getD 0#32).toNat / 2 := by
  have hlen : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [hsh.trl_len]; have := hba.trl_end_le; unfold kMaxV at hnv; omega
  have hnd := hba.trl_nodup
  unfold kittenTrailLits at hnd
  rw [List.map_map] at hnd
  have hm_len : (List.map ((fun x => x / 2) ∘ BitVec.toNat)
      (ks.trl.take ks.trl_end.toNat)).length = ks.trl_end.toNat := by
    simp [List.length_take]; omega
  intro heq
  have hinj := list_nodup_getElem_inj hnd (by omega) (by omega)
    (show (List.map ((fun x => x / 2) ∘ BitVec.toNat) (ks.trl.take ks.trl_end.toNat))[i] =
        (List.map ((fun x => x / 2) ∘ BitVec.toNat) (ks.trl.take ks.trl_end.toNat))[j] by
      simp only [List.getElem_map, List.getElem_take, Function.comp_def]
      rw [List.getElem?_eq_getElem (by omega : i < ks.trl.length),
        List.getElem?_eq_getElem (by omega : j < ks.trl.length), Option.getD_some,
        Option.getD_some] at heq
      exact heq)
  exact hne hinj

theorem kana_clause_entails_of_subset {F : CNF Nat} {c1 c2 : List Nat}
    (hsub : ∀ l ∈ c1, l ∈ c2) (h : F.EntailsClause (cnfClause c1)) :
    F.EntailsClause (cnfClause c2) := by
  rw [CNF.entails_clause_def] at h ⊢
  intro α hα
  obtain ⟨l, hl, hs⟩ := (clause_sat_cnfClause_iff α c1).mp (h α hα)
  exact (clause_sat_cnfClause_iff α c2).mpr ⟨l, hsub l hl, hs⟩

private theorem kana_cnf_entails_of_subset {F1 F2 : List (List Nat)} {c : CNF.Clause Nat}
    (hsub : ∀ cl ∈ F1, cl ∈ F2) (h : (cnfOfClauses F1).EntailsClause c) :
    (cnfOfClauses F2).EntailsClause c := by
  rw [CNF.entails_clause_def] at h ⊢
  intro α hα
  apply h α
  rw [cnf_sat_cnfOfClauses_iff] at hα ⊢
  exact fun cl hcl => hα cl (hsub cl hcl)

theorem kana_mem_resolvent_iff {ks : KittenState} {idx l : Nat} :
    l ∈ kittenResolventLits ks idx ↔
      (∃ j < idx,
        (ks.trl[j]?.getD 0#32).toNat = l ^^^ 1 ∧
        ks.lvlArr[(l ^^^ 1) / 2]?.getD 0#32 = ks.lvl ∧
        (ks.flags[(l ^^^ 1) / 2]?.getD 0#32 &&& 2#32) ≠ 0#32) ∨
      (∃ i, 1 ≤ i ∧ i < min ks.nkl.toNat ks.kl.length ∧
        (ks.kl[i]?.getD 0#32).toNat = l) := by
  unfold kittenResolventLits
  rw [List.mem_append, List.mem_filterMap, List.mem_map]
  constructor
  · rintro (⟨j, hj, hif⟩ | ⟨b, hb, rfl⟩)
    · left
      rw [List.mem_range] at hj
      dsimp only at hif
      split at hif
      · rename_i hcond
        simp only [Option.some.injEq] at hif
        have hxor : (ks.trl[j]?.getD 0#32).toNat = l ^^^ 1 := by
          rw [← hif, litNeg_eq_xor1, litNeg_eq_xor1, litNeg_litNeg]
        exact ⟨j, hj, hxor, hxor ▸ hcond.1, hxor ▸ hcond.2⟩
      · cases hif
    · right
      rw [List.mem_iff_getElem] at hb
      obtain ⟨k, hk, rfl⟩ := hb
      have hk' : k + 1 < min ks.nkl.toNat ks.kl.length := by
        simp [List.length_take] at hk; omega
      refine ⟨k + 1, by omega, hk', ?_⟩
      simp [List.getElem_take,
        List.getElem?_eq_getElem (by omega : k + 1 < ks.kl.length)]
  · rintro (⟨j, hj, htrl, hlvl, hfl⟩ | ⟨i, hi1, hi2, rfl⟩)
    · left
      refine ⟨j, List.mem_range.mpr hj, ?_⟩
      simp only [htrl, hlvl, hfl, ne_eq, not_false_eq_true, and_self, ↓reduceIte,
        Option.some.injEq]
      rw [litNeg_eq_xor1, litNeg_eq_xor1, litNeg_litNeg]
    · right
      have hi_lt : i < ks.kl.length := by omega
      refine ⟨ks.kl[i]'hi_lt, ?_, by simp [List.getElem?_eq_getElem hi_lt]⟩
      rw [List.mem_iff_getElem]
      refine ⟨i - 1, by simp [List.length_take]; omega, ?_⟩
      simp only [List.getElem_drop, List.getElem_take, show 1 + (i - 1) = i by omega]

/-! ## 2. Pure Step Model & Soundness of `full_kitten_ana_clause` -/

/-- Saturating push onto the resolution-chain buffer `res` (`nres` saturates at `257`). -/
private def kResPush (ks : KittenState) (c : BitVec 32) : KittenState :=
  if ks.nres.toNat < 256 then
    { ks with res := ks.res.set ks.nres.toNat c, nres := ks.nres + 1#32 }
  else if ks.nres = 256#32 then { ks with nres := 257#32 } else ks

/-- Effect of one loop iteration of `full_kitten_ana_clause` on literal `l`. -/
private def kAnaLit (skip : BitVec 32) (ks : KittenState) (l : BitVec 32) : KittenState :=
  let v := (l >>> 1).toNat
  let vlvl := ks.lvlArr[v]?.getD 0#32
  let fl := ks.flags[v]?.getD 0#32
  if l >>> 1 = skip then ks
  else if vlvl = 0#32 then
    if ks.ante ≠ 0#32 ∧ ks.rsn[v]?.getD 0#32 ≠ 0xFFFFFFFF#32 then
      kResPush ks (ks.rsn[v]?.getD 0#32) else ks
  else if (fl &&& 2#32) = 0#32 then
    let ks1 : KittenState := { ks with flags := ks.flags.set v (fl ||| 2#32) }
    let ks2 : KittenState := if ks1.nana.toNat < 128 then
      { ks1 with ana := ks1.ana.set ks1.nana.toNat (l >>> 1), nana := ks1.nana + 1#32 }
      else ks1
    if vlvl = ks.lvl then { ks2 with status := ks2.status + 1#32 }
    else if ks2.nkl.toNat < 128 then
      { ks2 with kl := ks2.kl.set ks2.nkl.toNat l, nkl := ks2.nkl + 1#32 }
    else ks2
  else ks

/-- State after the first `n` iterations of the `full_kitten_ana_clause` loop. -/
private def kAnaPrefix (skip : BitVec 32) (ks0 : KittenState) (off : Nat) : Nat → KittenState
  | 0 => ks0
  | n + 1 =>
    let st := kAnaPrefix skip ks0 off n
    kAnaLit skip st (st.arena[off + n]?.getD 0#32)

/-- Entry state of the `full_kitten_ana_clause` loop (after recording `cid` in `res`). -/
private def kAnaInit (ks : KittenState) (cid : BitVec 32) : KittenState :=
  if ks.ante ≠ 0#32 then kResPush ks cid else ks

private theorem kResPush_frame (ks : KittenState) (c : BitVec 32) :
    ∃ rs nr, kResPush ks c = { ks with res := rs, nres := nr } := by
  unfold kResPush
  by_cases h1 : ks.nres.toNat < 256
  · rw [kana_ite_t h1]; exact ⟨_, _, rfl⟩
  · rw [kana_ite_f h1]
    by_cases h2 : ks.nres = 256#32
    · rw [kana_ite_t h2]; exact ⟨ks.res, 257#32, rfl⟩
    · rw [kana_ite_f h2]; exact ⟨ks.res, ks.nres, by cases ks; rfl⟩

private theorem kAnaInit_frame (ks : KittenState) (cid : BitVec 32) :
    ∃ rs nr, kAnaInit ks cid = { ks with res := rs, nres := nr } := by
  unfold kAnaInit
  by_cases h : ks.ante ≠ 0#32
  · rw [kana_ite_t h]; exact kResPush_frame ks cid
  · rw [kana_ite_f h]; exact ⟨ks.res, ks.nres, by cases ks; rfl⟩

private theorem kAnaLit_frame (skip : BitVec 32) (ks : KittenState) (l : BitVec 32) :
    ∃ fl an na st kl nk rs nr, kAnaLit skip ks l =
      { ks with flags := fl, ana := an, nana := na, status := st, kl := kl, nkl := nk,
                res := rs, nres := nr } := by
  have hself : ∃ fl an na st kl nk rs nr, ks =
      { ks with flags := fl, ana := an, nana := na, status := st, kl := kl, nkl := nk,
                res := rs, nres := nr } :=
    ⟨ks.flags, ks.ana, ks.nana, ks.status, ks.kl, ks.nkl, ks.res, ks.nres, by cases ks; rfl⟩
  unfold kAnaLit; dsimp only
  by_cases h1 : l >>> 1 = skip
  · rw [kana_ite_t h1]; exact hself
  rw [kana_ite_f h1]
  by_cases h2 : ks.lvlArr[(l >>> 1).toNat]?.getD 0#32 = 0#32
  · rw [kana_ite_t h2]
    by_cases h3 : ks.ante ≠ 0#32 ∧ ks.rsn[(l >>> 1).toNat]?.getD 0#32 ≠ 0xFFFFFFFF#32
    · rw [kana_ite_t h3]
      obtain ⟨rs, nr, h⟩ := kResPush_frame ks _
      exact ⟨ks.flags, ks.ana, ks.nana, ks.status, ks.kl, ks.nkl, rs, nr, h⟩
    · rw [kana_ite_f h3]; exact hself
  rw [kana_ite_f h2]
  by_cases h3 : (ks.flags[(l >>> 1).toNat]?.getD 0#32 &&& 2#32) = 0#32
  · rw [kana_ite_t h3]
    let fl' := ks.flags[(l >>> 1).toNat]?.getD 0#32 ||| 2#32
    let ks1 : KittenState := { ks with flags := ks.flags.set (l >>> 1).toNat fl' }
    let ks2_fn := if ks1.nana.toNat < 128 then
        { ks1 with ana := ks1.ana.set ks1.nana.toNat (l >>> 1), nana := ks1.nana + 1#32 }
        else ks1
    have hks2 : ∃ an na, ks2_fn = { ks with flags := ks.flags.set (l >>> 1).toNat fl',
                                            ana := an, nana := na } := by
      dsimp only [ks2_fn, ks1]
      by_cases ha : ks.nana.toNat < 128
      · rw [kana_ite_t ha]; exact ⟨_, _, rfl⟩
      · rw [kana_ite_f ha]; exact ⟨ks.ana, ks.nana, rfl⟩
    obtain ⟨an, na, h2eq⟩ := hks2
    change ∃ fl an na st kl nk rs nr,
      (if ks.lvlArr[(l >>> 1).toNat]?.getD 0#32 = ks.lvl then
        { ks2_fn with status := ks2_fn.status + 1#32 }
      else if ks2_fn.nkl.toNat < 128 then
        { ks2_fn with kl := ks2_fn.kl.set ks2_fn.nkl.toNat l, nkl := ks2_fn.nkl + 1#32 }
      else ks2_fn) = _
    rw [h2eq]
    by_cases ht : ks.lvlArr[(l >>> 1).toNat]?.getD 0#32 = ks.lvl
    · rw [kana_ite_t ht]; exact ⟨_, an, na, _, _, _, _, _, rfl⟩
    · rw [kana_ite_f ht]
      by_cases hk : ks.nkl.toNat < 128
      · rw [kana_ite_t hk]; exact ⟨_, an, na, _, _, _, _, _, rfl⟩
      · rw [kana_ite_f hk]; exact ⟨_, an, na, _, _, _, _, _, rfl⟩
  · rw [kana_ite_f h3]; exact hself

private theorem kAnaPrefix_frame (skip : BitVec 32) (ks0 : KittenState) (off n : Nat) :
    ∃ fl an na st kl nk rs nr, kAnaPrefix skip ks0 off n =
      { ks0 with flags := fl, ana := an, nana := na, status := st, kl := kl, nkl := nk,
                 res := rs, nres := nr } := by
  induction n with
  | zero =>
    dsimp only [kAnaPrefix]
    exact ⟨ks0.flags, ks0.ana, ks0.nana, ks0.status, ks0.kl, ks0.nkl, ks0.res, ks0.nres,
      by cases ks0; rfl⟩
  | succ k ih =>
    obtain ⟨fl1, an1, na1, st1, kl1, nk1, rs1, nr1, h1⟩ := ih
    dsimp only [kAnaPrefix]
    obtain ⟨fl2, an2, na2, st2, kl2, nk2, rs2, nr2, h2⟩ := kAnaLit_frame skip _ _
    rw [h2, h1]
    exact ⟨fl2, an2, na2, st2, kl2, nk2, rs2, nr2, rfl⟩

private theorem kAnaPrefix_arena (skip : BitVec 32) (ks0 : KittenState) (off n : Nat) :
    (kAnaPrefix skip ks0 off n).arena = ks0.arena := by
  obtain ⟨_, _, _, _, _, _, _, _, h⟩ := kAnaPrefix_frame skip ks0 off n; rw [h]

private theorem kAnaPrefix_lvlArr (skip : BitVec 32) (ks0 : KittenState) (off n : Nat) :
    (kAnaPrefix skip ks0 off n).lvlArr = ks0.lvlArr := by
  obtain ⟨_, _, _, _, _, _, _, _, h⟩ := kAnaPrefix_frame skip ks0 off n; rw [h]

theorem kana_anaClausePreserved_refl (ks : KittenState) :
    KittenAnaClausePreserved ks ks :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ h => h⟩

theorem kana_anaClausePreserved_trans {ks1 ks2 ks3 : KittenState}
    (h12 : KittenAnaClausePreserved ks1 ks2) (h23 : KittenAnaClausePreserved ks2 ks3) :
    KittenAnaClausePreserved ks1 ks3 :=
  ⟨h23.nv.trans h12.nv, h23.nc.trans h12.nc, h23.orig_nc.trans h12.orig_nc,
   h23.lvl.trans h12.lvl, h23.prop.trans h12.prop, h23.trl_end.trans h12.trl_end,
   h23.unass.trans h12.unass, h23.incons.trans h12.incons, h23.failing.trans h12.failing,
   h23.ante.trans h12.ante, h23.alen.trans h12.alen, h23.acap.trans h12.acap,
   h23.nassump.trans h12.nassump, h23.nunits.trans h12.nunits,
   h23.lvlArr.trans h12.lvlArr, h23.rsn.trans h12.rsn, h23.trl.trans h12.trl,
   h23.vals.trans h12.vals, h23.assump.trans h12.assump, h23.units.trans h12.units,
   h23.whead.trans h12.whead, h23.wnext.trans h12.wnext, h23.wblit.trans h12.wblit,
   h23.clOff.trans h12.clOff, h23.clMeta.trans h12.clMeta, h23.clAux.trans h12.clAux,
   h23.arena.trans h12.arena,
   fun v hv h3 => h12.flags2_mono v hv (h23.flags2_mono v (by rw [h12.nv]; exact hv) h3)⟩

theorem kana_baseAssign_of_eq {ks1 ks2 : KittenState} (h : KittenBaseAssignOk ks1)
    (hnv : ks2.nv = ks1.nv := by rfl) (hnc : ks2.nc = ks1.nc := by rfl)
    (honc : ks2.orig_nc = ks1.orig_nc := by rfl) (hlvl : ks2.lvl = ks1.lvl := by rfl)
    (hprop : ks2.prop = ks1.prop := by rfl) (hte : ks2.trl_end = ks1.trl_end := by rfl)
    (hun : ks2.unass = ks1.unass := by rfl) (hante : ks2.ante = ks1.ante := by rfl)
    (hlvA : ks2.lvlArr = ks1.lvlArr := by rfl) (hrsn : ks2.rsn = ks1.rsn := by rfl)
    (htrl : ks2.trl = ks1.trl := by rfl) (hvals : ks2.vals = ks1.vals := by rfl)
    (hco : ks2.clOff = ks1.clOff := by rfl) (hcm : ks2.clMeta = ks1.clMeta := by rfl)
    (har : ks2.arena = ks1.arena := by rfl) : KittenBaseAssignOk ks2 := by
  have htl : kittenTrailLits ks2 = kittenTrailLits ks1 := by
    unfold kittenTrailLits; rw [htrl, hte]
  have hcl : ∀ c, kittenClauseLits ks2 c = kittenClauseLits ks1 c := fun c => by
    unfold kittenClauseLits kittenClauseOff kittenClauseSize kittenClauseMeta; rw [hco, hcm, har]
  have horig : kittenOrigClauses ks2 = kittenOrigClauses ks1 := by
    unfold kittenOrigClauses; rw [honc]; exact List.map_congr_left fun c _ => hcl c
  exact ⟨by rw [hte, hnv]; exact h.trl_end_le, by rw [hprop, hte]; exact h.prop_le,
    by rw [hun, hte, hnv]; exact h.unass_eq, by rw [hnv, hvals]; exact h.vals_dom,
    by rw [hnv, hvals]; exact h.vals_neg_iff,
    by rw [hnv, hvals, hte, htrl]; exact h.vals_nz_iff_trl,
    by rw [htl]; exact h.trl_nodup, by rw [htl, hnv]; exact h.trl_lt,
    by rw [hnv, hlvA, hlvl]; exact h.trl_lvl_le,
    by rw [hnv, hvals, hlvA, hrsn]; exact h.unass_lvl_zero,
    by rw [hte, hlvA, htrl]; exact h.trl_lvl_mono,
    by rw [hte, hlvA, htrl, hrsn]; exact h.dec_earliest,
    fun i hi hl0 => by
      rw [hte] at hi; rw [htrl, hlvA] at hl0
      have h0 := h.lvl0_ok i hi hl0
      refine ⟨by rw [htrl, hrsn]; exact h0.1, by rw [htrl, hvals]; exact h0.2.1,
        by rw [htrl, hvals]; exact h0.2.2.1, by rw [horig, htrl]; exact h0.2.2.2.1, fun ha => ?_⟩
      rw [hante] at ha; have h1 := h0.2.2.2.2 ha
      dsimp only; rw [hnc, hcl, htrl, hrsn]; exact h1⟩

private theorem kResPush_preserves_anaInv {acap : Nat} {ks : KittenState} {F0 : List (List Nat)}
    {idx : Nat} (hinv : KittenAnaInv acap ks F0 idx) (c : BitVec 32) :
    KittenAnaInv acap (kResPush ks c) F0 idx ∧ KittenAnaClausePreserved ks (kResPush ks c) := by
  unfold kResPush
  by_cases hlt : ks.nres.toNat < 256
  · rw [kana_ite_t hlt]
    have hsh' : ({ ks with res := ks.res.set ks.nres.toNat c,
                           nres := ks.nres + 1#32 } : KittenState).ShapesOk acap :=
      (hinv.shapes.putArr .res ks.nres.toNat c).putHdr .nres (ks.nres + 1#32)
    have hnr1 : (ks.nres + 1#32).toNat = ks.nres.toNat + 1 := by bv_omega
    exact ⟨⟨hsh', hinv.nv_le, hinv.nc_le, hinv.orig_nc_le, hinv.orig_nc_max, hinv.alen_le,
      hinv.acap_lt, hinv.acap_eq, hinv.lvl_pos, hinv.idx_le, hinv.cl_wf, hinv.cl_mono,
      hinv.orig_eq, hinv.watches, kana_baseAssign_of_eq hinv.assign, hinv.synced, hinv.reasons,
      by unfold kMaxL; change (ks.nres + 1#32).toNat ≤ 257; omega,
      hinv.nkl_pos, hinv.nkl_le, hinv.nana_le, hinv.ana_nodup, hinv.ana_lt, hinv.flags_seen,
      hinv.kl_nonTop, hinv.kl_injective, hinv.nkl_count, hinv.kl_nodup, hinv.status_eq,
      hinv.seen_in_trl⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
       rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ h => h⟩⟩
  · rw [kana_ite_f hlt]
    by_cases heq : ks.nres = 256#32
    · rw [kana_ite_t heq]
      have hsh' : ({ ks with nres := 257#32 } : KittenState).ShapesOk acap :=
        hinv.shapes.putHdr .nres 257#32
      exact ⟨⟨hsh', hinv.nv_le, hinv.nc_le, hinv.orig_nc_le, hinv.orig_nc_max, hinv.alen_le,
        hinv.acap_lt, hinv.acap_eq, hinv.lvl_pos, hinv.idx_le, hinv.cl_wf, hinv.cl_mono,
        hinv.orig_eq, hinv.watches, kana_baseAssign_of_eq hinv.assign, hinv.synced, hinv.reasons,
        by unfold kMaxL; change (257#32 : BitVec 32).toNat ≤ 256 + 1; decide,
        hinv.nkl_pos, hinv.nkl_le, hinv.nana_le, hinv.ana_nodup, hinv.ana_lt, hinv.flags_seen,
        hinv.kl_nonTop, hinv.kl_injective, hinv.nkl_count, hinv.kl_nodup, hinv.status_eq,
        hinv.seen_in_trl⟩,
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
         rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ h => h⟩⟩
    · rw [kana_ite_f heq]
      exact ⟨hinv, kana_anaClausePreserved_refl ks⟩

private theorem kResPush_res_props {acap : Nat} {ks : KittenState} (hsh : ks.ShapesOk acap)
    (_hnl : ks.nres.toNat ≤ kMaxL + 1) (c : BitVec 32) :
    let ks' := kResPush ks c
    ks.nres.toNat ≤ ks'.nres.toNat ∧
    (ks'.nres.toNat ≤ kMaxL →
      ks.nres.toNat < 256 ∧ ks'.nres.toNat = ks.nres.toNat + 1 ∧
      (∀ i < ks.nres.toNat, ks'.res[i]? = ks.res[i]?) ∧
      ks'.res[ks.nres.toNat]? = some c) := by
  dsimp only; unfold kResPush
  by_cases hlt : ks.nres.toNat < 256
  · rw [kana_ite_t hlt]
    have hnr1 : (ks.nres + 1#32).toNat = ks.nres.toNat + 1 := by bv_omega
    refine ⟨by change ks.nres.toNat ≤ (ks.nres + 1#32).toNat; omega, fun _ => ⟨hlt, hnr1, ?_, ?_⟩⟩
    · intro i hi; exact List.getElem?_set_ne (by omega)
    · exact List.getElem?_set_self (by rw [hsh.res_len]; exact hlt)
  · rw [kana_ite_f hlt]
    by_cases heq : ks.nres = 256#32
    · rw [kana_ite_t heq]
      have h257 : (257#32 : BitVec 32).toNat = 257 := by decide
      have h256 : ks.nres.toNat = 256 := by rw [heq]; decide
      refine ⟨by change ks.nres.toNat ≤ (257#32 : BitVec 32).toNat; omega,
        fun h => by unfold kMaxL at h; change (257#32 : BitVec 32).toNat ≤ 256 at h; omega⟩
    · rw [kana_ite_f heq]
      have hge : 257 ≤ ks.nres.toNat := by
        have hne : ks.nres.toNat ≠ 256 := fun h => heq (BitVec.eq_of_toNat_eq h)
        omega
      exact ⟨Nat.le_refl _, fun h => by unfold kMaxL at h; omega⟩

private theorem kAnaLit_preserves_anaInv {acap : Nat} {ks : KittenState} {F0 : List (List Nat)}
    {idx : Nat} {skip l : BitVec 32}
    (hinv : KittenAnaInv acap ks F0 idx)
    (hvdec : ∃ v_dec < ks.nv.toNat, ks.lvlArr[v_dec]?.getD 0#32 = ks.lvl)
    (hl_lt : l.toNat < 2 * ks.nv.toNat)
    (hl_trl : l.toNat / 2 ≠ skip.toNat → ∃ j < idx, (ks.trl[j]?.getD 0#32).toNat = l.toNat ^^^ 1) :
    KittenAnaInv acap (kAnaLit skip ks l) F0 idx ∧
    KittenAnaClausePreserved ks (kAnaLit skip ks l) ∧
    (∀ x ∈ kittenResolventLits ks idx, x ∈ kittenResolventLits (kAnaLit skip ks l) idx) ∧
    ks.nres.toNat ≤ (kAnaLit skip ks l).nres.toNat ∧
    ((kAnaLit skip ks l).nres.toNat ≤ kMaxL →
      ∀ i < ks.nres.toNat, (kAnaLit skip ks l).res[i]? = ks.res[i]?) := by
  have hnv := hinv.nv_le
  have hsh := hinv.shapes
  obtain ⟨hv_eq, hv_lt⟩ := bv32_lit_div2_bv hl_lt
  unfold kAnaLit
  dsimp only
  by_cases hskip : l >>> 1 = skip
  · rw [kana_ite_t hskip]
    exact ⟨hinv, kana_anaClausePreserved_refl ks, fun _ h => h, Nat.le_refl _, fun _ _ _ => rfl⟩
  rw [kana_ite_f hskip]
  by_cases hvlvl0 : ks.lvlArr[(l >>> 1).toNat]?.getD 0#32 = 0#32
  · rw [kana_ite_t hvlvl0]
    by_cases hante : ks.ante ≠ 0#32 ∧ ks.rsn[(l >>> 1).toNat]?.getD 0#32 ≠ 0xFFFFFFFF#32
    · rw [kana_ite_t hante]
      have ⟨hi', hp'⟩ := kResPush_preserves_anaInv hinv (ks.rsn[(l >>> 1).toNat]?.getD 0#32)
      have hres := kResPush_res_props hsh hinv.nres_le (ks.rsn[(l >>> 1).toNat]?.getD 0#32)
      obtain ⟨rs, nr, hfr⟩ := kResPush_frame ks (ks.rsn[(l >>> 1).toNat]?.getD 0#32)
      refine ⟨hi', hp', fun x hx => ?_, hres.1, fun hle i hi => (hres.2 hle).2.2.1 i hi⟩
      rw [hfr]; exact hx
    · rw [kana_ite_f hante]
      exact ⟨hinv, kana_anaClausePreserved_refl ks, fun _ h => h, Nat.le_refl _, fun _ _ _ => rfl⟩
  rw [kana_ite_f hvlvl0]
  by_cases hfl0 : (ks.flags[(l >>> 1).toNat]?.getD 0#32 &&& 2#32) = 0#32
  · rw [kana_ite_t hfl0]
    -- New unseen variable `v = (l >>> 1).toNat` with `vlvl ≠ 0`
    have hskip_ne : l.toNat / 2 ≠ skip.toNat := fun heq =>
      hskip (BitVec.eq_of_toNat_eq (by rw [hv_eq]; exact heq))
    obtain ⟨j0, hj0_idx, hj0_eq⟩ := hl_trl hskip_ne
    have hj0_te : j0 < ks.trl_end.toNat := Nat.lt_of_lt_of_le hj0_idx hinv.idx_le
    have hsync0 := hinv.synced j0 hj0_te
    dsimp only at hsync0
    have hxor1 : (l.toNat ^^^ 1) ^^^ 1 = l.toNat := by
      rw [litNeg_eq_xor1, litNeg_eq_xor1, litNeg_litNeg]
    rw [hj0_eq, hxor1] at hsync0
    have hl_val2 : ks.vals[l.toNat]? = some 2#32 := hsync0.2
    have hnv_128 : ks.nv.toNat ≤ 128 := hnv
    have hv_128 : (l >>> 1).toNat < 128 := by omega
    -- Prove `ks.nana.toNat < ks.nv.toNat` (hence `< 128`) by pigeonhole
    have hv_not_ana : (l >>> 1).toNat ∉ (ks.ana.take ks.nana.toNat).map BitVec.toNat := by
      intro hmem
      rw [List.mem_map] at hmem
      obtain ⟨b, hb, hbeq⟩ := hmem
      rw [List.mem_take_iff_getElem] at hb
      obtain ⟨i, hi, hget⟩ := hb
      have hi_na : i < ks.nana.toNat := by omega
      have hfl_nz := (hinv.flags_seen (l >>> 1).toNat hv_lt).mpr ⟨i, hi_na, by
        rw [List.getElem?_eq_getElem (by omega : i < ks.ana.length), Option.getD_some, hget, hbeq]⟩
      exact hfl_nz hfl0
    have hana_take_len : ((ks.ana.take ks.nana.toNat).map BitVec.toNat).length = ks.nana.toNat := by
      rw [List.length_map, List.length_take, hsh.ana_len]
      have := hinv.nana_le; omega
    have hnana_lt_nv : ks.nana.toNat < ks.nv.toNat := by
      have hnd : ((l >>> 1).toNat :: (ks.ana.take ks.nana.toNat).map BitVec.toNat).Nodup :=
        List.nodup_cons.mpr ⟨hv_not_ana, hinv.ana_nodup⟩
      have hlt_all : ∀ x ∈ (l >>> 1).toNat :: (ks.ana.take ks.nana.toNat).map BitVec.toNat,
          x < ks.nv.toNat := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hv_lt
        · rw [List.mem_map] at hx'
          obtain ⟨b, hb, rfl⟩ := hx'
          rw [List.mem_take_iff_getElem] at hb
          obtain ⟨i, hi, hget⟩ := hb
          have ha := hinv.ana_lt i (by omega)
          rwa [List.getElem?_eq_getElem (by omega : i < ks.ana.length),
            Option.getD_some, hget] at ha
      have hle := kana_nodup_subset_length hnd hlt_all
      simp only [List.length_cons, hana_take_len] at hle; omega
    have hnana_128 : ks.nana.toNat < 128 := by omega
    have hnana1 : (ks.nana + 1#32).toNat = ks.nana.toNat + 1 := by bv_omega
    let v := (l >>> 1).toNat
    let fl := ks.flags[v]?.getD 0#32
    let ks1 : KittenState := { ks with flags := ks.flags.set v (fl ||| 2#32) }
    let ks2 : KittenState :=
      { ks1 with ana := ks1.ana.set ks1.nana.toNat (l >>> 1), nana := ks1.nana + 1#32 }
    have hks2_ite : (if ks1.nana.toNat < 128 then
        { ks1 with ana := ks1.ana.set ks1.nana.toNat (l >>> 1), nana := ks1.nana + 1#32 }
        else ks1) = ks2 := kana_ite_t hnana_128
    have hks2_body : (let ks1_0 : KittenState :=
        { ks with flags := ks.flags.set v (fl ||| 2#32) }
        let ks2_0 : KittenState := if ks1_0.nana.toNat < 128 then
          { ks1_0 with ana := ks1_0.ana.set ks1_0.nana.toNat (l >>> 1), nana := ks1_0.nana + 1#32 }
          else ks1_0
        if ks.lvlArr[v]?.getD 0#32 = ks.lvl then { ks2_0 with status := ks2_0.status + 1#32 }
        else if ks2_0.nkl.toNat < 128 then
          { ks2_0 with kl := ks2_0.kl.set ks2_0.nkl.toNat l, nkl := ks2_0.nkl + 1#32 }
        else ks2_0) =
        (if ks.lvlArr[v]?.getD 0#32 = ks.lvl then { ks2 with status := ks2.status + 1#32 }
        else if ks2.nkl.toNat < 128 then
          { ks2 with kl := ks2.kl.set ks2.nkl.toNat l, nkl := ks2.nkl + 1#32 }
        else ks2) := by
      dsimp only; rw [hks2_ite]
    change KittenAnaInv acap _ F0 idx ∧ KittenAnaClausePreserved ks _ ∧ _
    rw [hks2_body]
    have hfl_len : v < ks.flags.length := by rw [hsh.flags_len]; exact hv_128
    have hana_len : ks.nana.toNat < ks.ana.length := by rw [hsh.ana_len]; exact hnana_128
    have hfl_set_self : (ks2.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32 := by
      change ((ks.flags.set v (fl ||| 2#32))[v]?.getD 0#32 &&& 2#32) ≠ 0#32
      rw [List.getElem?_set_self hfl_len, Option.getD_some]
      exact kana_fl_or2_and2_nz fl
    have hfl_set_ne : ∀ u, u ≠ v → ks2.flags[u]? = ks.flags[u]? := fun u hu =>
      List.getElem?_set_ne (Ne.symm hu)
    have hfl_mono : ∀ u < ks.nv.toNat,
        (ks2.flags[u]?.getD 0#32 &&& 2#32) = 0#32 → (ks.flags[u]?.getD 0#32 &&& 2#32) = 0#32 := by
      intro u _ h0
      by_cases huv : u = v
      · subst huv; exact absurd h0 hfl_set_self
      · rwa [hfl_set_ne u huv] at h0
    have hsh2 : ks2.ShapesOk acap := by
      have h := (hsh.putArr .flags v (fl ||| 2#32)).putArr .ana ks.nana.toNat (l >>> 1)
        |>.putHdr .nana (ks.nana + 1#32)
      exact h
    have hana_take2 : (ks2.ana.take ks2.nana.toNat).map BitVec.toNat =
        (ks.ana.take ks.nana.toNat).map BitVec.toNat ++ [v] := by
      change ((ks.ana.set ks.nana.toNat (l >>> 1)).take (ks.nana + 1#32).toNat).map BitVec.toNat =
        _
      rw [hnana1, List.take_add_one, List.map_append, list_take_set_out _ _ (Nat.le_refl _),
        List.getElem?_set_self hana_len]
      simp [v]
    have hana_nodup2 : ((ks2.ana.take ks2.nana.toNat).map BitVec.toNat).Nodup := by
      rw [hana_take2, List.nodup_append]
      exact ⟨hinv.ana_nodup, by simp, fun x hx y hy heq => by
        rw [List.mem_singleton] at hy; subst hy; subst heq; exact hv_not_ana hx⟩
    have hana_lt2 : ∀ i < ks2.nana.toNat, (ks2.ana[i]?.getD 0#32).toNat < ks2.nv.toNat := by
      intro i hi
      change i < (ks.nana + 1#32).toNat at hi; rw [hnana1] at hi
      by_cases hie : i = ks.nana.toNat
      · subst hie
        change ((ks.ana.set ks.nana.toNat (l >>> 1))[ks.nana.toNat]?.getD 0#32).toNat < ks.nv.toNat
        rw [List.getElem?_set_self hana_len, Option.getD_some]; exact hv_lt
      · change ((ks.ana.set ks.nana.toNat (l >>> 1))[i]?.getD 0#32).toNat < ks.nv.toNat
        rw [List.getElem?_set_ne (Ne.symm hie)]
        exact hinv.ana_lt i (by omega)
    have hflags_seen2 : ∀ u < ks2.nv.toNat,
        ((ks2.flags[u]?.getD 0#32 &&& 2#32) ≠ 0#32) ↔
          ∃ i < ks2.nana.toNat, (ks2.ana[i]?.getD 0#32).toNat = u := by
      intro u hu
      change (ks2.flags[u]?.getD 0#32 &&& 2#32) ≠ 0#32 ↔
        ∃ i < (ks.nana + 1#32).toNat,
          ((ks.ana.set ks.nana.toNat (l >>> 1))[i]?.getD 0#32).toNat = u
      rw [hnana1]
      by_cases huv : u = v
      · subst huv
        refine ⟨fun _ => ⟨ks.nana.toNat, by omega, by
          rw [List.getElem?_set_self hana_len, Option.getD_some]⟩, fun _ => hfl_set_self⟩
      · rw [hfl_set_ne u huv, hinv.flags_seen u hu]
        constructor
        · rintro ⟨i, hi, heq⟩
          exact ⟨i, by omega, by rwa [List.getElem?_set_ne (by omega)]⟩
        · rintro ⟨i, hi, heq⟩
          by_cases hie : i = ks.nana.toNat
          · subst hie
            rw [List.getElem?_set_self hana_len, Option.getD_some] at heq
            exact absurd heq.symm huv
          · rw [List.getElem?_set_ne (Ne.symm hie)] at heq
            exact ⟨i, by omega, heq⟩
    have hnkl_count2 : ∀ u < ks2.nv.toNat,
        (ks2.flags[u]?.getD 0#32 &&& 2#32) ≠ 0#32 → 0 < (ks2.lvlArr[u]?.getD 0#32).toNat := by
      intro u hu hnz
      by_cases huv : u = v
      · subst huv
        exact Nat.pos_of_ne_zero fun hz => hvlvl0 (BitVec.eq_of_toNat_eq hz)
      · rw [hfl_set_ne u huv] at hnz
        exact hinv.nkl_count u hu hnz
    have hseen_trl2 : ∀ u < ks2.nv.toNat,
        (ks2.flags[u]?.getD 0#32 &&& 2#32) ≠ 0#32 → ks2.lvlArr[u]?.getD 0#32 = ks2.lvl →
        ∃ j < ks2.trl_end.toNat, (ks2.trl[j]?.getD 0#32).toNat / 2 = u := by
      intro u hu hnz hlvl
      by_cases huv : u = v
      · subst huv
        refine ⟨j0, hj0_te, ?_⟩
        change (ks.trl[j0]?.getD 0#32).toNat / 2 = (l >>> 1).toNat
        rw [hj0_eq, litNeg_eq_xor1]
        have := litVar_litNeg l.toNat
        unfold litVar at this; omega
      · rw [hfl_set_ne u huv] at hnz
        exact hinv.seen_in_trl u hu hnz hlvl
    have hvlvl_le : (ks.lvlArr[v]?.getD 0#32).toNat ≤ ks.lvl.toNat :=
      hinv.assign.trl_lvl_le v hv_lt
    -- Split on `vlvl = ks.lvl`
    by_cases htop : ks.lvlArr[v]?.getD 0#32 = ks.lvl
    · rw [kana_ite_t htop]
      -- Top-level literal: increment `status`
      let ks3 : KittenState := { ks2 with status := ks2.status + 1#32 }
      have hj0_var : (ks.trl[j0]?.getD 0#32).toNat / 2 = v := by
        rw [hj0_eq, litNeg_eq_xor1]
        have := litVar_litNeg l.toNat; unfold litVar at this; omega
      have hfilter_succ :
          ((List.range idx).filter fun j =>
            let u := (ks3.trl[j]?.getD 0#32).toNat / 2
            decide (ks3.lvlArr[u]?.getD 0#32 = ks3.lvl ∧
              (ks3.flags[u]?.getD 0#32 &&& 2#32) ≠ 0#32)).length =
          ((List.range idx).filter fun j =>
            let u := (ks.trl[j]?.getD 0#32).toNat / 2
            decide (ks.lvlArr[u]?.getD 0#32 = ks.lvl ∧
              (ks.flags[u]?.getD 0#32 &&& 2#32) ≠ 0#32)).length + 1 := by
        refine kana_filter_length_flip_one List.nodup_range (List.mem_range.mpr hj0_idx) ?_ ?_ ?_
        · simp only [decide_eq_false_iff_not]; rw [hj0_var]; exact fun h => h.2 hfl0
        · simp only [decide_eq_true_eq]
          exact ⟨by change ks.lvlArr[(ks.trl[j0]?.getD 0#32).toNat / 2]?.getD 0#32 = ks.lvl
                    rw [hj0_var]; exact htop,
                 by change (ks2.flags[(ks.trl[j0]?.getD 0#32).toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32
                    rw [hj0_var]; exact hfl_set_self⟩
        · intro j hj hne
          rw [List.mem_range] at hj
          have hvar_ne : (ks.trl[j]?.getD 0#32).toNat / 2 ≠ v := by
            rw [← hj0_var]
            exact kana_trl_nodup_var_ne hsh hnv hinv.assign (Nat.lt_of_lt_of_le hj hinv.idx_le)
              hj0_te hne
          change decide (ks.lvlArr[(ks.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32 = ks.lvl ∧
            (ks2.flags[(ks.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32) = _
          rw [hfl_set_ne _ hvar_ne]
      have hst_le : ks.status.toNat ≤ idx := by
        rw [hinv.status_eq]
        exact Nat.le_trans (List.length_filter_le _ _) (by simp)
      have hst1 : (ks.status + 1#32).toNat = ks.status.toNat + 1 := by
        have := hinv.idx_le; have := hinv.assign.trl_end_le; bv_omega
      have hinv3 : KittenAnaInv acap ks3 F0 idx :=
        ⟨hsh2.putHdr .status (ks2.status + 1#32), hinv.nv_le, hinv.nc_le, hinv.orig_nc_le,
          hinv.orig_nc_max, hinv.alen_le, hinv.acap_lt, hinv.acap_eq, hinv.lvl_pos, hinv.idx_le,
          hinv.cl_wf, hinv.cl_mono, hinv.orig_eq, hinv.watches, kana_baseAssign_of_eq hinv.assign,
          hinv.synced, hinv.reasons, hinv.nres_le, hinv.nkl_pos, hinv.nkl_le,
          by change (ks.nana + 1#32).toNat ≤ ks.nv.toNat; rw [hnana1]; omega,
          hana_nodup2, hana_lt2, hflags_seen2,
          fun i hi1 hi2 => by
            have hk := hinv.kl_nonTop i hi1 hi2
            refine ⟨hk.1, fun h0 => hk.2.1 (hfl_mono _ (by omega) h0), hk.2.2⟩,
          fun u hu hnz hlt_lv => by
            by_cases huv : u = v
            · subst huv
              change (ks.lvlArr[v]?.getD 0#32).toNat < ks.lvl.toNat at hlt_lv
              rw [htop] at hlt_lv; omega
            · rw [hfl_set_ne u huv] at hnz; exact hinv.kl_injective u hu hnz hlt_lv,
          hnkl_count2, hinv.kl_nodup,
          by change (ks.status + 1#32).toNat = _; rw [hst1, hinv.status_eq, ← hfilter_succ],
          hseen_trl2⟩
      have hpres3 : KittenAnaClausePreserved ks ks3 :=
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
         rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hfl_mono⟩
      refine ⟨hinv3, hpres3, fun x hx => ?_, Nat.le_refl _, fun _ _ _ => rfl⟩
      rw [kana_mem_resolvent_iff] at hx ⊢
      rcases hx with ⟨j, hj, htrl, hlvl, hfl⟩ | hr
      · left
        have hx_lt : (x ^^^ 1) / 2 < ks.nv.toNat := by
          have hmem := mem_kittenTrailLits_of_lt (Nat.lt_of_lt_of_le hj hinv.idx_le)
            (by rw [hsh.trl_len]; have := hinv.assign.trl_end_le; omega)
          have hlt := hinv.assign.trl_lt _ hmem
          rw [htrl] at hlt; omega
        exact ⟨j, hj, htrl, hlvl, fun h0 => hfl (hfl_mono _ hx_lt h0)⟩
      · exact Or.inr hr
    · rw [kana_ite_f htop]
      -- Lower-level literal (`0 < vlvl < ks.lvl`): push `l` onto `kl`
      have hvlvl_lt : (ks.lvlArr[v]?.getD 0#32).toNat < ks.lvl.toNat := by
        have hne : (ks.lvlArr[v]?.getD 0#32).toNat ≠ ks.lvl.toNat := fun h =>
          htop (BitVec.eq_of_toNat_eq h)
        omega
      -- Prove `ks.nkl.toNat < ks.nv.toNat` (hence `< 128`) using `v`, `v_dec`, and `kl[1..nkl)`
      obtain ⟨v_dec, hvdec_lt, hvdec_lvl⟩ := hvdec
      have hv_ne_vdec : v ≠ v_dec := fun h => by subst h; rw [hvdec_lvl] at hvlvl_lt; omega
      let klVars := ((ks.kl.take ks.nkl.toNat).drop 1).map (fun x => x.toNat / 2)
      have hklVars_len : klVars.length = ks.nkl.toNat - 1 := by
        simp only [klVars, List.length_map, List.length_drop, List.length_take, hsh.kl_len]
        have := hinv.nkl_le; omega
      have hklVars_prop : ∀ u ∈ klVars, u < ks.nv.toNat ∧
          (ks.flags[u]?.getD 0#32 &&& 2#32) ≠ 0#32 ∧
          (ks.lvlArr[u]?.getD 0#32).toNat < ks.lvl.toNat := by
        intro u hm
        rw [List.mem_map] at hm
        obtain ⟨b, hb, rfl⟩ := hm
        rw [List.mem_iff_getElem] at hb
        obtain ⟨k, hk, rfl⟩ := hb
        have hk1 : k + 1 < ks.nkl.toNat := by
          simp [List.length_take, hsh.kl_len] at hk
          have := hinv.nkl_le; omega
        have hnt := hinv.kl_nonTop (k + 1) (by omega) hk1
        dsimp only at hnt
        have hget : (ks.kl[k + 1]?.getD 0#32).toNat =
            (((ks.kl.take ks.nkl.toNat).drop 1)[k]'hk).toNat := by
          simp only [List.getElem_drop, List.getElem_take]
          rw [List.getElem?_eq_getElem (by rw [hsh.kl_len]; have := hinv.nkl_le; omega),
            Option.getD_some]
          congr 2; omega
        rw [hget] at hnt
        exact ⟨by omega, hnt.2.1, hnt.2.2.2.1⟩
      have hv_not_kl : v ∉ klVars := fun hm => (hklVars_prop v hm).2.1 hfl0
      have hvdec_not_kl : v_dec ∉ klVars := fun hm => by
        have hlt := (hklVars_prop v_dec hm).2.2; rw [hvdec_lvl] at hlt; omega
      have hnkl_lt_nv : ks.nkl.toNat < ks.nv.toNat := by
        have hnd : (v :: v_dec :: klVars).Nodup :=
          List.nodup_cons.mpr ⟨by simp [hv_ne_vdec, hv_not_kl],
            List.nodup_cons.mpr ⟨hvdec_not_kl, hinv.kl_nodup⟩⟩
        have hlt_all : ∀ x ∈ v :: v_dec :: klVars, x < ks.nv.toNat := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx1
          · exact hv_lt
          · rcases List.mem_cons.mp hx1 with rfl | hx2
            · exact hvdec_lt
            · exact (hklVars_prop x hx2).1
        have hle := kana_nodup_subset_length hnd hlt_all
        simp only [List.length_cons, hklVars_len] at hle
        have := hinv.nkl_pos; omega
      have hnkl_128 : ks.nkl.toNat < 128 := by omega
      have hnkl1 : (ks.nkl + 1#32).toNat = ks.nkl.toNat + 1 := by bv_omega
      have hkl_len : ks.nkl.toNat < ks.kl.length := by rw [hsh.kl_len]; exact hnkl_128
      let ks3 : KittenState :=
        { ks2 with kl := ks2.kl.set ks2.nkl.toNat l, nkl := ks2.nkl + 1#32 }
      have hks3_ite : (if ks2.nkl.toNat < 128 then
          { ks2 with kl := ks2.kl.set ks2.nkl.toNat l, nkl := ks2.nkl + 1#32 }
          else ks2) = ks3 := kana_ite_t hnkl_128
      rw [hks3_ite]
      have hkl_take3 : (((ks3.kl.take ks3.nkl.toNat).drop 1).map (fun x => x.toNat / 2)) =
          klVars ++ [v] := by
        change (((ks.kl.set ks.nkl.toNat l).take (ks.nkl + 1#32).toNat).drop 1).map
          (fun x => x.toNat / 2) = _
        rw [hnkl1, List.take_add_one, list_take_set_out _ _ (Nat.le_refl _),
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
      have hinv3 : KittenAnaInv acap ks3 F0 idx :=
        ⟨(hsh2.putArr .kl ks.nkl.toNat l).putHdr .nkl (ks.nkl + 1#32),
          hinv.nv_le, hinv.nc_le, hinv.orig_nc_le, hinv.orig_nc_max, hinv.alen_le, hinv.acap_lt,
          hinv.acap_eq, hinv.lvl_pos, hinv.idx_le, hinv.cl_wf, hinv.cl_mono, hinv.orig_eq,
          hinv.watches, kana_baseAssign_of_eq hinv.assign, hinv.synced, hinv.reasons, hinv.nres_le,
          by change 1 ≤ (ks.nkl + 1#32).toNat; rw [hnkl1]; omega,
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
              exact ⟨hk.1, fun h0 => hk.2.1 (hfl_mono _ (by omega) h0), hk.2.2⟩,
          fun u hu hnz hlt_lv => by
            by_cases huv : u = v
            · subst huv
              refine ⟨ks.nkl.toNat, hinv.nkl_pos,
                (by change ks.nkl.toNat < (ks.nkl + 1#32).toNat; rw [hnkl1]; omega), ?_⟩
              change ((ks.kl.set ks.nkl.toNat l)[ks.nkl.toNat]?.getD 0#32).toNat / 2 = v
              rw [List.getElem?_set_self hkl_len, Option.getD_some]; exact hv_eq.symm
            · rw [hfl_set_ne u huv] at hnz
              obtain ⟨i, hi1, hi2, hieq⟩ := hinv.kl_injective u hu hnz hlt_lv
              refine ⟨i, hi1, (by change i < (ks.nkl + 1#32).toNat; rw [hnkl1]; omega), ?_⟩
              change ((ks.kl.set ks.nkl.toNat l)[i]?.getD 0#32).toNat / 2 = u
              rwa [List.getElem?_set_ne (by omega)],
          hnkl_count2, hkl_nodup3, by rw [hfilter_eq]; exact hinv.status_eq, hseen_trl2⟩
      have hpres3 : KittenAnaClausePreserved ks ks3 :=
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
         rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hfl_mono⟩
      refine ⟨hinv3, hpres3, fun x hx => ?_, Nat.le_refl _, fun _ _ _ => rfl⟩
      rw [kana_mem_resolvent_iff] at hx ⊢
      rcases hx with ⟨j, hj, htrl, hlvl, hfl⟩ | ⟨i, hi1, hi2, hieq⟩
      · left
        have hx_lt : (x ^^^ 1) / 2 < ks.nv.toNat := by
          have hmem := mem_kittenTrailLits_of_lt (Nat.lt_of_lt_of_le hj hinv.idx_le)
            (by rw [hsh.trl_len]; have := hinv.assign.trl_end_le; omega)
          have hlt := hinv.assign.trl_lt _ hmem
          rw [htrl] at hlt; omega
        exact ⟨j, hj, htrl, hlvl, fun h0 => hfl (hfl_mono _ hx_lt h0)⟩
      · right
        have hi_lt : i < ks.nkl.toNat := by omega
        have hi_min : i < min ks3.nkl.toNat ks3.kl.length := by
          change i < min (ks.nkl + 1#32).toNat (ks.kl.set ks.nkl.toNat l).length
          rw [hnkl1, List.length_set, hsh.kl_len]; omega
        refine ⟨i, hi1, hi_min, ?_⟩
        change ((ks.kl.set ks.nkl.toNat l)[i]?.getD 0#32).toNat = x
        rwa [List.getElem?_set_ne (by omega)]
  · rw [kana_ite_f hfl0]
    exact ⟨hinv, kana_anaClausePreserved_refl ks, fun _ h => h, Nat.le_refl _, fun _ _ _ => rfl⟩

private theorem kAnaLit_effect_on_lit {acap : Nat} {ks : KittenState} {F0 : List (List Nat)}
    {idx : Nat} {skip l : BitVec 32}
    (hinv : KittenAnaInv acap ks F0 idx)
    (hvdec : ∃ v_dec < ks.nv.toNat, ks.lvlArr[v_dec]?.getD 0#32 = ks.lvl)
    (hl_lt : l.toNat < 2 * ks.nv.toNat)
    (hl_trl : l.toNat / 2 ≠ skip.toNat → ∃ j < idx, (ks.trl[j]?.getD 0#32).toNat = l.toNat ^^^ 1)
    (hskip_ne : l.toNat / 2 ≠ skip.toNat) :
    let ks' := kAnaLit skip ks l
    (ks.lvlArr[l.toNat / 2]?.getD 0#32 = 0#32 →
      (cnfOfClauses F0).EntailsClause (cnfClause [l.toNat ^^^ 1]) ∧
      (ks.ante ≠ 0#32 → ks'.nres.toNat ≤ kMaxL →
        ∃ i < ks'.nres.toNat,
          (ks'.res[i]?.getD 0xFFFFFFFF#32).toNat < ks.nc.toNat ∧
          kittenClauseLits ks (ks'.res[i]?.getD 0xFFFFFFFF#32).toNat = [l.toNat ^^^ 1])) ∧
    (ks.lvlArr[l.toNat / 2]?.getD 0#32 ≠ 0#32 →
      l.toNat ∈ kittenResolventLits ks' idx) := by
  have ⟨hv_eq, hv_lt⟩ := bv32_lit_div2_bv hl_lt
  obtain ⟨j0, hj0_idx, hj0_eq⟩ := hl_trl hskip_ne
  have hj0_te : j0 < ks.trl_end.toNat := Nat.lt_of_lt_of_le hj0_idx hinv.idx_le
  have hj0_var : (ks.trl[j0]?.getD 0#32).toNat / 2 = l.toNat / 2 := by
    rw [hj0_eq, litNeg_eq_xor1]; have := litVar_litNeg l.toNat; unfold litVar at this; omega
  have hskip_bv : l >>> 1 ≠ skip := fun h => hskip_ne (by rw [← hv_eq, h])
  have ⟨hinv', hpres', _, _, _⟩ := kAnaLit_preserves_anaInv hinv hvdec hl_lt hl_trl
  constructor
  · intro hvlvl0
    have h0 := hinv.assign.lvl0_ok j0 hj0_te (by rwa [hj0_var])
    dsimp only at h0
    rw [hj0_eq, hinv.orig_eq] at h0
    refine ⟨h0.2.2.2.1, fun hante hnr_le => ?_⟩
    have hr0_ne : ks.rsn[(l >>> 1).toNat]?.getD 0#32 ≠ 0xFFFFFFFF#32 := by
      have hdiv : (l.toNat ^^^ 1) / 2 = l.toNat / 2 := by
        rw [litNeg_eq_xor1]; exact litVar_litNeg l.toNat
      rw [hv_eq, ← hdiv]; exact h0.1
    have hks'_eq : kAnaLit skip ks l = kResPush ks (ks.rsn[(l >>> 1).toNat]?.getD 0#32) := by
      unfold kAnaLit; dsimp only
      have hv0' : ks.lvlArr[(l >>> 1).toNat]?.getD 0#32 = 0#32 := by rwa [hv_eq]
      simp only [hskip_bv, hv0', hante, hr0_ne, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
    have hpush := kResPush_res_props hinv.shapes hinv.nres_le (ks.rsn[(l >>> 1).toNat]?.getD 0#32)
    rw [hks'_eq] at hnr_le ⊢
    obtain ⟨_, hnr_eq, _, hres_get⟩ := hpush.2 hnr_le
    refine ⟨ks.nres.toNat, by omega, ?_⟩
    rw [hres_get, Option.getD_some]
    have h1 := h0.2.2.2.2 hante
    have hr_eq : ks.rsn[(l >>> 1).toNat]?.getD 0#32 =
        ks.rsn[(l.toNat ^^^ 1) / 2]?.getD 0xFFFFFFFF#32 := by
      have hlen : l.toNat / 2 < ks.rsn.length := by
        rw [hinv.shapes.rsn_len]; have := hinv.nv_le; unfold kMaxV at this; omega
      have hdiv : (l.toNat ^^^ 1) / 2 = l.toNat / 2 := by
        rw [litNeg_eq_xor1]; exact litVar_litNeg l.toNat
      rw [hv_eq, hdiv, List.getElem?_eq_getElem hlen, Option.getD_some, Option.getD_some]
    rw [hr_eq]; exact h1
  · intro hvlvl_ne
    have hfl_nz' : ((kAnaLit skip ks l).flags[l.toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32 := by
      by_cases hfl0 : (ks.flags[(l >>> 1).toNat]?.getD 0#32 &&& 2#32) = 0#32
      · unfold kAnaLit; dsimp only
        have hv_ne' : ks.lvlArr[(l >>> 1).toNat]?.getD 0#32 ≠ 0#32 := by rwa [hv_eq]
        rw [kana_ite_f hskip_bv, kana_ite_f hv_ne', kana_ite_t hfl0]
        have hfl_len : (l >>> 1).toNat < ks.flags.length := by
          rw [hinv.shapes.flags_len]; have := hinv.nv_le; unfold kMaxV at this; omega
        have hfl_check : ∀ (fl : BitVec 32),
            ((ks.flags.set (l >>> 1).toNat (fl ||| 2#32))[l.toNat / 2]?.getD 0#32 &&& 2#32) ≠
              0#32 := fun fl => by
          rw [← hv_eq, List.getElem?_set_self hfl_len, Option.getD_some]
          exact kana_fl_or2_and2_nz fl
        let fl' := ks.flags[(l >>> 1).toNat]?.getD 0#32 ||| 2#32
        let ks1 : KittenState := { ks with flags := ks.flags.set (l >>> 1).toNat fl' }
        have hks2_fl : ∀ s : KittenState, s.flags = ks1.flags →
            ((if ks.lvlArr[(l >>> 1).toNat]?.getD 0#32 = ks.lvl then
                { s with status := s.status + 1#32 }
              else if s.nkl.toNat < 128 then
                { s with kl := s.kl.set s.nkl.toNat l, nkl := s.nkl + 1#32 }
              else s).flags[l.toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32 := by
          intro s hs
          by_cases ht : ks.lvlArr[(l >>> 1).toNat]?.getD 0#32 = ks.lvl
          · rw [kana_ite_t ht]; change (s.flags[l.toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32
            rw [hs]; exact hfl_check _
          · rw [kana_ite_f ht]
            by_cases hk : s.nkl.toNat < 128
            · rw [kana_ite_t hk]; change (s.flags[l.toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32
              rw [hs]; exact hfl_check _
            · rw [kana_ite_f hk]; rw [hs]; exact hfl_check _
        apply hks2_fl
        by_cases ha : ks1.nana.toNat < 128
        · rw [kana_ite_t ha]
        · rw [kana_ite_f ha]
      · exact fun h0 => hfl0 (by rw [hv_eq]; exact hpres'.flags2_mono (l.toNat / 2) (by omega) h0)
    rw [kana_mem_resolvent_iff]
    by_cases htop : ks.lvlArr[l.toNat / 2]?.getD 0#32 = ks.lvl
    · left
      have hdiv : (l.toNat ^^^ 1) / 2 = l.toNat / 2 := by
        rw [litNeg_eq_xor1]; exact litVar_litNeg l.toNat
      refine ⟨j0, hj0_idx, by rw [hpres'.trl]; exact hj0_eq,
        by rw [hpres'.lvlArr, hpres'.lvl, hdiv]; exact htop,
        by rw [hdiv]; exact hfl_nz'⟩
    · right
      have hvlvl_lt : ((kAnaLit skip ks l).lvlArr[l.toNat / 2]?.getD 0#32).toNat <
          (kAnaLit skip ks l).lvl.toNat := by
        rw [hpres'.lvlArr, hpres'.lvl]
        have hle := hinv.assign.trl_lvl_le (l.toNat / 2) (by omega)
        have hne : (ks.lvlArr[l.toNat / 2]?.getD 0#32).toNat ≠ ks.lvl.toNat := fun h =>
          htop (BitVec.eq_of_toNat_eq h)
        omega
      obtain ⟨i, hi1, hi2, hieq⟩ :=
        hinv'.kl_injective (l.toNat / 2) (by rw [hpres'.nv]; omega) hfl_nz' hvlvl_lt
      have hnt := hinv'.kl_nonTop i hi1 hi2
      have hsync0 := hinv.synced j0 hj0_te
      dsimp only at hsync0
      rw [hj0_eq, litNeg_eq_xor1, litNeg_eq_xor1, litNeg_litNeg] at hsync0
      have hkl_eq : ((kAnaLit skip ks l).kl[i]?.getD 0#32).toNat = l.toNat := by
        rcases (litVar_eq_iff ((kAnaLit skip ks l).kl[i]?.getD 0#32).toNat l.toNat).mp
            (by simpa [litVar] using hieq) with h1 | h1
        · exact h1
        · exfalso
          have hv2 : ks.vals[l.toNat ^^^ 1]? = some 2#32 := by
            have := hnt.2.2.2.2
            rw [hpres'.vals, h1, ← litNeg_eq_xor1] at this; exact this
          rw [litNeg_eq_xor1] at hv2
          rw [hsync0.1] at hv2; cases hv2
      have hmin : i < min (kAnaLit skip ks l).nkl.toNat (kAnaLit skip ks l).kl.length := by
        rw [hinv'.shapes.kl_len]
        have := hinv'.nkl_le; have := hinv'.nv_le; unfold kMaxV at this; omega
      exact ⟨i, hi1, hmin, hkl_eq⟩

private theorem kAnaPrefix_properties {acap : Nat} {ks : KittenState} {F0 : List (List Nat)}
    {idx : Nat} {cid skip : BitVec 32}
    (hinv : KittenAnaInv acap ks F0 idx)
    (hcid : cid.toNat < ks.nc.toNat)
    (hvdec : ∃ v_dec < ks.nv.toNat, ks.lvlArr[v_dec]?.getD 0#32 = ks.lvl)
    (hlits : ∀ l ∈ kittenClauseLits ks cid.toNat, l / 2 ≠ skip.toNat →
      ∃ j < idx, (ks.trl[j]?.getD 0#32).toNat = l ^^^ 1) :
    let ks0 := kAnaInit ks cid
    let off := kittenClauseOff ks cid.toNat
    let sz := kittenClauseSize ks cid.toNat
    ∀ n ≤ sz,
      let st := kAnaPrefix skip ks0 off n
      KittenAnaInv acap st F0 idx ∧
      KittenAnaClausePreserved ks st ∧
      (∀ x ∈ kittenResolventLits ks idx, x ∈ kittenResolventLits st idx) ∧
      ks0.nres.toNat ≤ st.nres.toNat ∧
      (st.nres.toNat ≤ kMaxL → ∀ i < ks0.nres.toNat, st.res[i]? = ks0.res[i]?) ∧
      (∀ k < n,
        let l := (ks.arena[off + k]?.getD 0#32).toNat
        l / 2 ≠ skip.toNat →
        (ks.lvlArr[l / 2]?.getD 0#32 = 0#32 →
          (cnfOfClauses F0).EntailsClause (cnfClause [l ^^^ 1]) ∧
          (ks.ante ≠ 0#32 → st.nres.toNat ≤ kMaxL →
            ∃ i < st.nres.toNat,
              (st.res[i]?.getD 0xFFFFFFFF#32).toNat < ks.nc.toNat ∧
              kittenClauseLits ks (st.res[i]?.getD 0xFFFFFFFF#32).toNat = [l ^^^ 1])) ∧
        (ks.lvlArr[l / 2]?.getD 0#32 ≠ 0#32 → l ∈ kittenResolventLits st idx)) := by
  intro ks0 off sz n
  have hwf := hinv.cl_wf cid.toNat hcid
  have hbd : off + sz ≤ ks.arena.length := by
    rw [hinv.shapes.arena_len]
    have := hwf.2.2.1; unfold kittenClauseSpan at this
    have := hinv.alen_le; omega
  have hinit_inv : KittenAnaInv acap ks0 F0 idx ∧ KittenAnaClausePreserved ks ks0 := by
    unfold ks0 kAnaInit
    split
    · exact kResPush_preserves_anaInv hinv cid
    · exact ⟨hinv, kana_anaClausePreserved_refl ks⟩
  have hinit_res : ∀ x ∈ kittenResolventLits ks idx, x ∈ kittenResolventLits ks0 idx := by
    obtain ⟨rs, nr, hfr⟩ := kAnaInit_frame ks cid
    intro x hx; dsimp only [ks0]; rw [hfr]; exact hx
  induction n with
  | zero =>
    intro _
    exact ⟨hinit_inv.1, hinit_inv.2, hinit_res, Nat.le_refl _, fun _ _ _ => rfl,
      fun _ hk => by omega⟩
  | succ k ih =>
    intro hk_le
    obtain ⟨hinv_k, hpres_k, hres_k, hnr_k, hres_eq_k, hdone_k⟩ := ih (Nat.le_of_succ_le hk_le)
    let st := kAnaPrefix skip ks0 off k
    have har_st : st.arena = ks.arena := by
      rw [kAnaPrefix_arena]
      obtain ⟨rs, nr, hfr⟩ := kAnaInit_frame ks cid; dsimp only [ks0]; rw [hfr]
    let lit := ks.arena[off + k]?.getD 0#32
    have hlit_mem : lit.toNat ∈ kittenClauseLits ks cid.toNat :=
      (kana_mem_clauseLits_iff hbd).mpr ⟨k, by omega, rfl⟩
    have hlit_lt : lit.toNat < 2 * st.nv.toNat := by
      rw [hpres_k.nv]; exact hwf.2.2.2.1 _ hlit_mem
    have hlit_trl : lit.toNat / 2 ≠ skip.toNat →
        ∃ j < idx, (st.trl[j]?.getD 0#32).toNat = lit.toNat ^^^ 1 := fun hne => by
      rw [hpres_k.trl]; exact hlits _ hlit_mem hne
    have hvdec_st : ∃ v_dec < st.nv.toNat, st.lvlArr[v_dec]?.getD 0#32 = st.lvl := by
      rw [hpres_k.nv, hpres_k.lvlArr, hpres_k.lvl]; exact hvdec
    have hstep_eq : kAnaPrefix skip ks0 off (k + 1) = kAnaLit skip st lit := by
      change kAnaLit skip st (st.arena[off + k]?.getD 0#32) = kAnaLit skip st lit
      rw [har_st]
    rw [hstep_eq]
    obtain ⟨hinv_s, hpres_s, hres_s, hnr_s, hres_eq_s⟩ :=
      kAnaLit_preserves_anaInv hinv_k hvdec_st hlit_lt hlit_trl
    refine ⟨hinv_s, kana_anaClausePreserved_trans hpres_k hpres_s,
      fun x hx => hres_s x (hres_k x hx), Nat.le_trans hnr_k hnr_s,
      fun hle i hi => (hres_eq_s hle i (Nat.lt_of_lt_of_le hi hnr_k)).trans
        (hres_eq_k (Nat.le_trans hnr_s hle) i hi),
      fun m hm hne => ?_⟩
    by_cases hmk : m = k
    · subst hmk
      have heff := kAnaLit_effect_on_lit hinv_k hvdec_st hlit_lt hlit_trl hne
      rw [hpres_k.lvlArr, hpres_k.ante, hpres_k.nc] at heff
      have hcl_eq : ∀ c, kittenClauseLits st c = kittenClauseLits ks c := fun c => by
        unfold kittenClauseLits kittenClauseOff kittenClauseSize kittenClauseMeta
        rw [hpres_k.clOff, hpres_k.clMeta, hpres_k.arena]
      refine ⟨fun h0 => ⟨(heff.1 h0).1, fun ha hle => ?_⟩, heff.2⟩
      obtain ⟨i, hi, hlt, hli⟩ := (heff.1 h0).2 ha hle
      exact ⟨i, hi, hlt, by rw [← hcl_eq]; exact hli⟩
    · have hprev := hdone_k m (by omega) hne
      refine ⟨fun h0 => ⟨(hprev.1 h0).1, fun ha hle => ?_⟩,
        fun hnz => hres_s _ (hprev.2 hnz)⟩
      obtain ⟨i, hi, hlt, hli⟩ := (hprev.1 h0).2 ha (Nat.le_trans hnr_s hle)
      refine ⟨i, Nat.lt_of_lt_of_le hi hnr_s, ?_⟩
      have hreq := hres_eq_s hle i hi
      rw [hreq]; exact ⟨hlt, hli⟩

private theorem kAnaPrefix_entails {acap : Nat} {ks : KittenState} {F0 : List (List Nat)}
    {idx : Nat} {cid skip : BitVec 32}
    (hinv : KittenAnaInv acap ks F0 idx)
    (hcid : cid.toNat < ks.nc.toNat)
    (hvdec : ∃ v_dec < ks.nv.toNat, ks.lvlArr[v_dec]?.getD 0#32 = ks.lvl)
    (hlits : ∀ l ∈ kittenClauseLits ks cid.toNat, l / 2 ≠ skip.toNat →
      ∃ j < idx, (ks.trl[j]?.getD 0#32).toNat = l ^^^ 1)
    (hcase :
      (skip = 0xFFFFFFFF#32 ∧ ks.status = 0#32 ∧ ks.nkl = 1#32 ∧
        ks.nana = 0#32 ∧ ks.nres = 0#32) ∨
      (∃ p, p / 2 = skip.toNat ∧ p ∈ kittenClauseLits ks cid.toNat ∧
        (∀ l ∈ kittenClauseLits ks cid.toNat, l / 2 = skip.toNat → l = p) ∧
        (cnfOfClauses F0).EntailsClause (cnfClause ((p ^^^ 1) :: kittenResolventLits ks idx)) ∧
        (ks.ante ≠ 0#32 → ks.nres.toNat ≤ kMaxL →
          (∀ i < ks.nres.toNat, (ks.res[i]?.getD 0xFFFFFFFF#32).toNat < ks.nc.toNat) ∧
          (cnfOfClauses ((ks.res.take ks.nres.toNat).map fun c =>
            kittenClauseLits ks c.toNat)).EntailsClause
              (cnfClause ((p ^^^ 1) :: kittenResolventLits ks idx))))) :
    let ks' := kAnaPrefix skip (kAnaInit ks cid) (kittenClauseOff ks cid.toNat)
      (kittenClauseSize ks cid.toNat)
    KittenAnaInv acap ks' F0 idx ∧
    KittenAnaClausePreserved ks ks' ∧
    (cnfOfClauses F0).EntailsClause (cnfClause (kittenResolventLits ks' idx)) ∧
    (ks'.ante ≠ 0#32 → ks'.nres.toNat ≤ kMaxL →
      (∀ i < ks'.nres.toNat, (ks'.res[i]?.getD 0xFFFFFFFF#32).toNat < ks'.nc.toNat) ∧
      (cnfOfClauses ((ks'.res.take ks'.nres.toNat).map fun c =>
        kittenClauseLits ks' c.toNat)).EntailsClause
          (cnfClause (kittenResolventLits ks' idx))) := by
  intro ks'
  have hwf := hinv.cl_wf cid.toNat hcid
  have hbd : kittenClauseOff ks cid.toNat + kittenClauseSize ks cid.toNat ≤ ks.arena.length := by
    rw [hinv.shapes.arena_len]
    have := hwf.2.2.1; unfold kittenClauseSpan at this
    have := hinv.alen_le; omega
  obtain ⟨hinv', hpres', hres_sub, hnr_le, hres_eq, hdone⟩ :=
    kAnaPrefix_properties hinv hcid hvdec hlits (kittenClauseSize ks cid.toNat) (Nat.le_refl _)
  have hlit_done : ∀ l ∈ kittenClauseLits ks cid.toNat, l / 2 ≠ skip.toNat →
      (ks.lvlArr[l / 2]?.getD 0#32 = 0#32 →
        (cnfOfClauses F0).EntailsClause (cnfClause [l ^^^ 1]) ∧
        (ks.ante ≠ 0#32 → ks'.nres.toNat ≤ kMaxL →
          ∃ i < ks'.nres.toNat,
            (ks'.res[i]?.getD 0xFFFFFFFF#32).toNat < ks.nc.toNat ∧
            kittenClauseLits ks (ks'.res[i]?.getD 0xFFFFFFFF#32).toNat = [l ^^^ 1])) ∧
      (ks.lvlArr[l / 2]?.getD 0#32 ≠ 0#32 → l ∈ kittenResolventLits ks' idx) := by
    intro l hl hne
    obtain ⟨k, hk, rfl⟩ := (kana_mem_clauseLits_iff hbd).mp hl
    exact hdone k hk hne
  have hres_all_lt : ks.ante ≠ 0#32 → ks'.nres.toNat ≤ kMaxL →
      (∀ i < ks.nres.toNat, (ks.res[i]?.getD 0xFFFFFFFF#32).toNat < ks.nc.toNat) →
      ∀ i < ks'.nres.toNat, (ks'.res[i]?.getD 0xFFFFFFFF#32).toNat < ks.nc.toNat := by
    intro hante hnr_fin hlt_old
    have hinit_eq : kAnaInit ks cid = kResPush ks cid := by unfold kAnaInit; rw [kana_ite_t hante]
    have hnr0_le : (kResPush ks cid).nres.toNat ≤ kMaxL := by
      rw [← hinit_eq]; exact Nat.le_trans hnr_le hnr_fin
    obtain ⟨_, hnr0_succ, hres0_old, hres0_cid⟩ :=
      (kResPush_res_props hinv.shapes hinv.nres_le cid).2 hnr0_le
    suffices ∀ n ≤ kittenClauseSize ks cid.toNat,
        (kAnaPrefix skip (kAnaInit ks cid) (kittenClauseOff ks cid.toNat) n).nres.toNat ≤ kMaxL →
        ∀ i < (kAnaPrefix skip (kAnaInit ks cid) (kittenClauseOff ks cid.toNat) n).nres.toNat,
          ((kAnaPrefix skip (kAnaInit ks cid) (kittenClauseOff ks cid.toNat) n).res[i]?.getD
            0xFFFFFFFF#32).toNat < ks.nc.toNat from
      this (kittenClauseSize ks cid.toNat) (Nat.le_refl _) hnr_fin
    intro n; induction n with
    | zero =>
      intro _ _ i hi
      dsimp only [kAnaPrefix] at hi ⊢; rw [hinit_eq, hnr0_succ] at hi; rw [hinit_eq]
      by_cases hie : i = ks.nres.toNat
      · subst hie; rw [hres0_cid, Option.getD_some]; exact hcid
      · rw [hres0_old i (by omega)]; exact hlt_old i (by omega)
    | succ k ih =>
      intro hk_le hle_s
      obtain ⟨hinv_k, hpres_k, _, _, _, _⟩ :=
        kAnaPrefix_properties hinv hcid hvdec hlits k (Nat.le_of_succ_le hk_le)
      let st := kAnaPrefix skip (kAnaInit ks cid) (kittenClauseOff ks cid.toNat) k
      have har_st : st.arena = ks.arena := by
        rw [kAnaPrefix_arena, hinit_eq]
        obtain ⟨rs, nr, hfr⟩ := kResPush_frame ks cid; rw [hfr]
      let lit := ks.arena[kittenClauseOff ks cid.toNat + k]?.getD 0#32
      have hlit_mem : lit.toNat ∈ kittenClauseLits ks cid.toNat :=
        (kana_mem_clauseLits_iff hbd).mpr ⟨k, by omega, rfl⟩
      have hlit_lt : lit.toNat < 2 * ks.nv.toNat := hwf.2.2.2.1 _ hlit_mem
      have hstep_eq : kAnaPrefix skip (kAnaInit ks cid) (kittenClauseOff ks cid.toNat) (k + 1) =
          kAnaLit skip st lit := by
        change kAnaLit skip st (st.arena[kittenClauseOff ks cid.toNat + k]?.getD 0#32) = _
        rw [har_st]
      rw [hstep_eq] at hle_s ⊢
      have hsame : ∀ s : KittenState, s.res = st.res → s.nres = st.nres →
          s.nres.toNat ≤ kMaxL → ∀ i < s.nres.toNat,
            (s.res[i]?.getD 0xFFFFFFFF#32).toNat < ks.nc.toNat := fun s hr hn hl => by
        rw [hr, hn]; exact ih (Nat.le_of_succ_le hk_le) (by rwa [← hn])
      unfold kAnaLit at hle_s ⊢; dsimp only at hle_s ⊢
      by_cases hsk : lit >>> 1 = skip
      · rw [kana_ite_t hsk] at hle_s ⊢; exact ih (Nat.le_of_succ_le hk_le) hle_s
      rw [kana_ite_f hsk] at hle_s ⊢
      by_cases hv0 : st.lvlArr[(lit >>> 1).toNat]?.getD 0#32 = 0#32
      · rw [kana_ite_t hv0] at hle_s ⊢
        by_cases ha0 : st.ante ≠ 0#32 ∧ st.rsn[(lit >>> 1).toNat]?.getD 0#32 ≠ 0xFFFFFFFF#32
        · rw [kana_ite_t ha0] at hle_s ⊢
          obtain ⟨hnr_lt_s, hns, hro, hrs⟩ :=
            (kResPush_res_props hinv_k.shapes hinv_k.nres_le _).2 hle_s
          have hih := ih (Nat.le_of_succ_le hk_le) (Nat.le_of_lt hnr_lt_s)
          intro i hi
          change i < (kResPush st _).nres.toNat at hi; rw [hns] at hi
          by_cases hie : i = st.nres.toNat
          · subst hie; rw [hrs, Option.getD_some, hpres_k.rsn]
            obtain ⟨hv_eq, _⟩ := bv32_lit_div2_bv hlit_lt
            have hskip_ne : lit.toNat / 2 ≠ skip.toNat := fun h =>
              hsk (BitVec.eq_of_toNat_eq (by rw [hv_eq]; exact h))
            obtain ⟨j0, hj0, hj0_eq⟩ := hlits _ hlit_mem hskip_ne
            have hj0_v : (ks.trl[j0]?.getD 0#32).toNat / 2 = lit.toNat / 2 := by
              rw [hj0_eq, litNeg_eq_xor1]; exact litVar_litNeg lit.toNat
            have h0 := hinv.assign.lvl0_ok j0 (Nat.lt_of_lt_of_le hj0 hinv.idx_le)
              (by rw [hj0_v, ← hv_eq, ← hpres_k.lvlArr]; exact hv0)
            have hlen : lit.toNat / 2 < ks.rsn.length := by
              rw [hinv.shapes.rsn_len]; have := hinv.nv_le; unfold kMaxV at this; omega
            have h1 := h0.2.2.2.2 hante
            rw [hv_eq, List.getElem?_eq_getElem hlen, Option.getD_some]
            rw [hj0_v, List.getElem?_eq_getElem hlen, Option.getD_some] at h1; exact h1.1
          · have hi_st : i < st.nres.toNat := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hi) hie
            rw [hro i hi_st]; exact hih i hi_st
        · rw [kana_ite_f ha0] at hle_s ⊢; exact ih (Nat.le_of_succ_le hk_le) hle_s
      · rw [kana_ite_f hv0] at hle_s ⊢
        by_cases hf : (st.flags[(lit >>> 1).toNat]?.getD 0#32 &&& 2#32) = 0#32
        · rw [kana_ite_t hf] at hle_s ⊢
          apply hsame _ _ _ hle_s
          · by_cases ha : st.nana.toNat < 128 <;> simp only [ha, ↓reduceIte] <;>
              by_cases ht : st.lvlArr[(lit >>> 1).toNat]?.getD 0#32 = st.lvl <;>
              simp only [ht, ↓reduceIte] <;>
              by_cases hk : st.nkl.toNat < 128 <;> simp only [hk, ↓reduceIte]
          · by_cases ha : st.nana.toNat < 128 <;> simp only [ha, ↓reduceIte] <;>
              by_cases ht : st.lvlArr[(lit >>> 1).toNat]?.getD 0#32 = st.lvl <;>
              simp only [ht, ↓reduceIte] <;>
              by_cases hk : st.nkl.toNat < 128 <;> simp only [hk, ↓reduceIte]
        · rw [kana_ite_f hf] at hle_s ⊢; exact ih (Nat.le_of_succ_le hk_le) hle_s
  have hres_mem_of_lt : ∀ {c : BitVec 32} {i : Nat}, i < ks'.nres.toNat →
      ks'.res[i]? = some c →
      kittenClauseLits ks c.toNat ∈
        (ks'.res.take ks'.nres.toNat).map fun x => kittenClauseLits ks' x.toNat := by
    intro c i hi hget
    have hcl_eq : kittenClauseLits ks' c.toNat = kittenClauseLits ks c.toNat := by
      unfold kittenClauseLits kittenClauseOff kittenClauseSize kittenClauseMeta
      rw [hpres'.clOff, hpres'.clMeta, hpres'.arena]
    rw [← hcl_eq, List.mem_map]
    refine ⟨c, ?_, rfl⟩
    rw [List.mem_take_iff_getElem]
    have hlen : i < ks'.res.length := (List.getElem?_eq_some_iff.mp hget).1
    exact ⟨i, by omega, Option.some.inj (by rw [← List.getElem?_eq_getElem hlen, hget])⟩
  have hres_init_sub : ks.ante ≠ 0#32 → ks'.nres.toNat ≤ kMaxL →
      kittenClauseLits ks cid.toNat ∈
        ((ks'.res.take ks'.nres.toNat).map fun x => kittenClauseLits ks' x.toNat) ∧
      ∀ cl ∈ ((ks.res.take ks.nres.toNat).map fun c => kittenClauseLits ks c.toNat),
        cl ∈ ((ks'.res.take ks'.nres.toNat).map fun c => kittenClauseLits ks' c.toNat) := by
    intro hante hnr_fin
    have hinit_eq : kAnaInit ks cid = kResPush ks cid := by unfold kAnaInit; rw [kana_ite_t hante]
    have hnr0_le : (kResPush ks cid).nres.toNat ≤ kMaxL := by
      rw [← hinit_eq]; exact Nat.le_trans hnr_le hnr_fin
    obtain ⟨_, hnr0_succ, hres0_old, hres0_cid⟩ :=
      (kResPush_res_props hinv.shapes hinv.nres_le cid).2 hnr0_le
    refine ⟨hres_mem_of_lt (Nat.lt_of_lt_of_le
      (show ks.nres.toNat < (kAnaInit ks cid).nres.toNat by rw [hinit_eq, hnr0_succ]; omega) hnr_le)
        (by rw [hres_eq hnr_fin ks.nres.toNat (by rw [hinit_eq, hnr0_succ]; omega),
          hinit_eq, hres0_cid]), ?_⟩
    intro cl hcl
    rw [List.mem_map] at hcl; obtain ⟨c, hc, rfl⟩ := hcl
    rw [List.mem_take_iff_getElem] at hc; obtain ⟨i, hi, rfl⟩ := hc
    have hi_len : i < ks.res.length := by omega
    exact hres_mem_of_lt (Nat.lt_of_lt_of_le
      (show i < (kAnaInit ks cid).nres.toNat by rw [hinit_eq, hnr0_succ]; omega) hnr_le)
      (by rw [hres_eq hnr_fin i (by rw [hinit_eq, hnr0_succ]; omega),
        hinit_eq, hres0_old i (by omega), List.getElem?_eq_getElem hi_len])
  -- Shared resolution step: given an assignment `α` satisfying `cid` and all lvl-0 units
  have hresolve : ∀ (α : Nat → Bool),
      (cnfClause (kittenClauseLits ks cid.toNat)).Sat α →
      (∀ l ∈ kittenClauseLits ks cid.toNat, l / 2 ≠ skip.toNat →
        ks.lvlArr[l / 2]?.getD 0#32 = 0#32 → (cnfClause [l ^^^ 1]).Sat α) →
      (∃ l ∈ kittenClauseLits ks cid.toNat, l / 2 = skip.toNat ∧
        (cnfClause [l]).Sat α) ∨
      (cnfClause (kittenResolventLits ks' idx)).Sat α := by
    intro α hα_cid hα_lvl0
    obtain ⟨l, hl_mem, hlsat⟩ := (clause_sat_cnfClause_iff α _).mp hα_cid
    by_cases hlv : l / 2 = skip.toNat
    · exact Or.inl ⟨l, hl_mem, hlv, (sat_cnfClause_singleton α l).mpr hlsat⟩
    · by_cases h0 : ks.lvlArr[l / 2]?.getD 0#32 = 0#32
      · have hneg := hα_lvl0 l hl_mem hlv h0
        rw [litNeg_eq_xor1] at hneg
        exact absurd ((sat_cnfClause_singleton α l).mpr hlsat)
          ((sat_cnfClause_litNeg_iff α l).mp hneg)
      · exact Or.inr ((clause_sat_cnfClause_iff α _).mpr ⟨l, (hlit_done l hl_mem hlv).2 h0, hlsat⟩)
  have hskip_no_match : skip = 0xFFFFFFFF#32 →
      ∀ l ∈ kittenClauseLits ks cid.toNat, l / 2 ≠ skip.toNat := by
    intro hff l hl; have hl_lt := hwf.2.2.2.1 l hl
    rw [hff]; have := hinv.nv_le; unfold kMaxV at this
    have : (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 := by decide
    omega
  refine ⟨hinv', hpres', ?_, ?_⟩
  · refine CNF.entails_clause_def.mpr fun α hα => ?_
    have hres_α := hresolve α (CNF.entails_clause_def.mp hwf.2.2.2.2.1 α hα)
      (fun l hl hlv h0 => CNF.entails_clause_def.mp ((hlit_done l hl hlv).1 h0).1 α hα)
    rcases hcase with ⟨hff, _, _, _, _⟩ | ⟨p, _, _, hp_uniq, hF0_p, _⟩
    · rcases hres_α with ⟨l, hl, hlv, _⟩ | hsat
      · exact absurd hlv (hskip_no_match hff l hl)
      · exact hsat
    · obtain ⟨x, hx_mem, hxsat⟩ :=
        (clause_sat_cnfClause_iff α _).mp (CNF.entails_clause_def.mp hF0_p α hα)
      rcases List.mem_cons.mp hx_mem with rfl | hx_old
      · rcases hres_α with ⟨l, hl, hlv, hlsat⟩ | hsat
        · have hlp := hp_uniq l hl hlv; subst hlp
          exact absurd hlsat
            ((sat_cnfClause_litNeg_iff α l).mp ((sat_cnfClause_singleton α _).mpr hxsat))
        · exact hsat
      · exact (clause_sat_cnfClause_iff α _).mpr ⟨x, hres_sub x hx_old, hxsat⟩
  · intro hante' hnr_fin
    have hante : ks.ante ≠ 0#32 := by rwa [← hpres'.ante]
    obtain ⟨hcid_in, hold_sub⟩ := hres_init_sub hante hnr_fin
    have hres_α : ∀ α, (cnfOfClauses ((ks'.res.take ks'.nres.toNat).map fun c =>
          kittenClauseLits ks' c.toNat)).Sat α →
        (∃ l ∈ kittenClauseLits ks cid.toNat, l / 2 = skip.toNat ∧
          (cnfClause [l]).Sat α) ∨
        (cnfClause (kittenResolventLits ks' idx)).Sat α := fun α hα =>
      hresolve α ((cnf_sat_cnfOfClauses_iff α _).mp hα _ hcid_in) fun l hl hlv h0 => by
        obtain ⟨i, hi, _, hunit⟩ := ((hlit_done l hl hlv).1 h0).2 hante hnr_fin
        have hi_len : i < ks'.res.length := by
          rw [hinv'.shapes.res_len]; unfold kMaxL at hnr_fin; omega
        have hmem_u := hres_mem_of_lt hi (List.getElem?_eq_getElem hi_len)
        rw [List.getElem?_eq_getElem hi_len, Option.getD_some] at hunit
        rw [hunit] at hmem_u
        exact (cnf_sat_cnfOfClauses_iff α _).mp hα _ hmem_u
    rcases hcase with ⟨hff, _, _, _, hnr0⟩ | ⟨p, _, _, hp_uniq, _, hres_p⟩
    · have hall : ∀ i < ks'.nres.toNat,
          (ks'.res[i]?.getD 0xFFFFFFFF#32).toNat < ks'.nc.toNat := by
        rw [hpres'.nc]
        exact hres_all_lt hante hnr_fin (fun i hi => by rw [hnr0] at hi; simp at hi)
      refine ⟨hall, CNF.entails_clause_def.mpr fun α hα => ?_⟩
      rcases hres_α α hα with ⟨l, hl, hlv, _⟩ | hsat
      · exact absurd hlv (hskip_no_match hff l hl)
      · exact hsat
    · have hnr_old_le : ks.nres.toNat ≤ kMaxL := by
        have hinit_eq : kAnaInit ks cid = kResPush ks cid := by
          unfold kAnaInit; rw [kana_ite_t hante]
        exact Nat.le_trans (kResPush_res_props hinv.shapes hinv.nres_le cid).1
          (by rw [← hinit_eq]; exact Nat.le_trans hnr_le hnr_fin)
      obtain ⟨hlt_old, hent_old⟩ := hres_p hante hnr_old_le
      refine ⟨by rw [hpres'.nc]; exact hres_all_lt hante hnr_fin hlt_old,
        CNF.entails_clause_def.mpr fun α hα => ?_⟩
      obtain ⟨x, hx_mem, hxsat⟩ := (clause_sat_cnfClause_iff α _).mp
        (CNF.entails_clause_def.mp (kana_cnf_entails_of_subset hold_sub hent_old) α hα)
      rcases List.mem_cons.mp hx_mem with rfl | hx_old
      · rcases hres_α α hα with ⟨l, hl, hlv, hlsat⟩ | hsat
        · have hlp := hp_uniq l hl hlv; subst hlp
          exact absurd hlsat
            ((sat_cnfClause_litNeg_iff α l).mp ((sat_cnfClause_singleton α _).mpr hxsat))
        · exact hsat
      · exact (clause_sat_cnfClause_iff α _).mpr ⟨x, hres_sub x hx_old, hxsat⟩

/-! ## 3. Parametric `Func.wp` Proof for `full_kitten_ana_clause` -/

/-- Parametric `Func.wp` proof for `full_kitten_ana_clause` (`[11]`). -/
theorem full_kitten_ana_clause_wp (Γ : Env) :
    ∀ args m Q X, fullKittenAnaClauseSpec args m Q X →
      Func.wp Γ full_kitten_ana_clause_body args m Q X := by
  rintro ⟨kPtr, cid, skip_v, ⟨⟩⟩ m Q X ⟨acap, ks, F0, idx, R, hinv, hcid, hskip, hvdec, hlits,
    hcase, hm, hQ⟩
  have hsh := hinv.shapes
  have hnv := hinv.nv_le
  have hnc := hinv.nc_le
  have hcid_28 : cid.toNat < 2 ^ 28 := by unfold kMaxCl at hnc; omega
  have hcid_896 : cid.toNat < 896 := by unfold kMaxCl at hnc; omega
  have hmA := kittenMem_to_amem hsh hm; clear hm
  c0_hsteps_nogrp
  refine wp_join0 (fun m' => (KittenMemA kPtr acap (kAnaInit ks cid) ⋆ R) m') ?_ ?_
  · intro J m' hm'
    let sz := ks.clMeta[cid.toNat]?.getD 0#32 &&& 65535
    let off := ks.clOff[cid.toNat]?.getD 0#32
    let ks0 := kAnaInit ks cid
    have hwf := hinv.cl_wf cid.toNat hcid
    have hspan : off.toNat + sz.toNat ≤ ks.alen.toNat := by
      have h1 := hwf.2.2.1; unfold kittenClauseSpan kittenClauseSize kittenClauseMeta at h1
      unfold kittenClauseOff at h1
      change off.toNat + (sz.toNat + _) ≤ ks.alen.toNat at h1; omega
    have hal := hinv.alen_le
    have hacap := hinv.acap_lt
    have hbd : kittenClauseOff ks cid.toNat + kittenClauseSize ks cid.toNat ≤ ks.arena.length := by
      rw [hsh.arena_len]
      have := hwf.2.2.1; unfold kittenClauseSpan at this; omega
    have hlit_lt : ∀ n < sz.toNat,
        (ks.arena[off.toNat + n]?.getD 0#32).toNat < 2 * ks.nv.toNat := fun n hn =>
      hwf.2.2.2.1 _ ((kana_mem_clauseLits_iff hbd).mpr ⟨n, hn, rfl⟩)
    have hsz_16 : sz.toNat < 2 ^ 16 := by
      have : sz.toNat ≤ 65535 := by
        dsimp only [sz]; rw [BitVec.toNat_and]
        exact Nat.le_trans Nat.and_le_right (by decide)
      omega
    refine wp_while_state1 (proj := fun st : BitVec 32 × KittenState => st.1)
      (fun st => sz.toNat - st.1.toNat)
      (fun st m' => st.1.toNat ≤ sz.toNat ∧ st.2 = kAnaPrefix skip_v ks0 off.toNat st.1.toNat ∧
        (KittenMemA kPtr acap st.2 ⋆ R) m') ?_ ?_
    · intro L hL
      exact hL (0#32, ks0) m' ⟨Nat.zero_le _, rfl, hm'⟩
    · rintro L ⟨i, st⟩ m'' ⟨hi_le, hst, hm''⟩ ih
      dsimp only at hi_le hst hm'' ⊢
      c0_hsplit
      · have hi_lt : i.toNat < sz.toNat := by bv_omega
        have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
        have hoi_cap : off.toNat + i.toNat < acap := by omega
        have hoi_28 : off.toNat + i.toNat < 2 ^ 28 := by unfold dimacsBound at hacap; omega
        have hfr : ∃ fl an na stv kl nk rs nr, st =
            { ks with flags := fl, ana := an, nana := na, status := stv, kl := kl, nkl := nk,
                      res := rs, nres := nr } := by
          rw [hst]
          obtain ⟨fl, an, na, stv, kl, nk, rs, nr, h1⟩ :=
            kAnaPrefix_frame skip_v ks0 off.toNat i.toNat
          obtain ⟨rs0, nr0, h0⟩ := kAnaInit_frame ks cid
          dsimp only [ks0] at h1
          rw [h1, h0]
          exact ⟨fl, an, na, stv, kl, nk, rs, nr, rfl⟩
        obtain ⟨_, _, _, _, _, _, _, _, hfr_eq⟩ := hfr
        have har : st.arena = ks.arena := by rw [hfr_eq]
        have hlv_eq : st.lvl = ks.lvl := by rw [hfr_eq]
        have hnv_eq : st.nv = ks.nv := by rw [hfr_eq]
        have hl := hlit_lt i.toNat hi_lt
        let l := ks.arena[(ks.clOff[cid.toNat]?.getD 0#32).toNat + i.toNat]?.getD 0#32
        have hl_st :
            st.arena[(ks.clOff[cid.toNat]?.getD 0#32).toNat + i.toNat]?.getD 0#32 = l := by
          rw [har]
        obtain ⟨hv_eq, hv_lt⟩ := bv32_lit_div2_bv hl
        have hv_128 : (l >>> 1).toNat < 128 := by
          change (l >>> 1).toNat < ks.nv.toNat at hv_lt; unfold kMaxV at hnv; omega
        have hv_28 : (l >>> 1).toNat < 2 ^ 28 := by omega
        have hv_st_128 :
            (st.arena[(ks.clOff[cid.toNat]?.getD 0#32).toNat + i.toNat]?.getD 0#32 >>> 1).toNat <
              128 := by
          rw [hl_st]; exact hv_128
        have hv_st_28 :
            (st.arena[(ks.clOff[cid.toNat]?.getD 0#32).toNat + i.toNat]?.getD 0#32 >>> 1).toNat <
              2 ^ 28 := by omega
        have hv_eq' : (l >>> 1).toNat = l.toNat / 2 := hv_eq
        have hnext_eq : kAnaPrefix skip_v ks0 off.toNat (i.toNat + 1) = kAnaLit skip_v st l := by
          rw [hst]; change kAnaLit skip_v (kAnaPrefix skip_v ks0 off.toNat i.toNat)
            ((kAnaPrefix skip_v ks0 off.toNat i.toNat).arena[off.toNat + i.toNat]?.getD 0#32) = _
          rw [← hst]; exact congrArg (kAnaLit skip_v st) hl_st
        c0_hsteps_nogrp
        refine wp_join0 (fun m3 => (KittenMemA kPtr acap (kAnaLit skip_v st l) ⋆ R) m3) ?_ ?_
        · intro Jv m3 hm3
          c0_hsteps!
          exact ih (i + 1#32, kAnaLit skip_v st l) m3 (by dsimp only; rw [hi1]; omega)
            ⟨by dsimp only; rw [hi1]; omega, by dsimp only; rw [hi1, hnext_eq], hm3⟩
        · intro Jv hJv
          c0_hsteps_nogrp
          c0_hsplit
          · -- `l >>> 1 ≠ skip_v`
            have hsk_ne : l >>> 1 ≠ skip_v := by rw [← hl_st]; exact ‹_›
            c0_hsteps_nogrp
            refine wp_join0 (fun m3 => (KittenMemA kPtr acap (kAnaLit skip_v st l) ⋆ R) m3)
              ?_ ?_
            · intro Jvlvl m3 hm3; c0_hsteps!; exact hJv m3 hm3
            · intro Jvlvl hJvlvl
              c0_hsteps_nogrp
              c0_hsplit
              · -- `vlvl = 0`
                have hv0 : st.lvlArr[(l >>> 1).toNat]?.getD 0#32 = 0#32 := by
                  rw [hv_eq', ← hl_st]; exact hc
                c0_hsteps_nogrp
                refine wp_join0 (fun m3 => (KittenMemA kPtr acap (kAnaLit skip_v st l) ⋆ R) m3)
                  ?_ ?_
                · intro Ja m3 hm3; c0_hsteps!; exact hJvlvl m3 hm3
                · intro Ja hJa
                  c0_hsteps_nogrp
                  refine wp_unroll_group fun _ _ => ?_
                  c0_hsteps!
                  · -- `ante ≠ 0 ∧ r0 ≠ 0xFFFFFFFF ∧ nres < 256`
                    have ha_ne : st.ante ≠ 0#32 := by assumption
                    have hr0_ne : st.rsn[(l >>> 1).toNat]?.getD 0#32 ≠ 0xFFFFFFFF#32 := by
                      rw [hv_eq', ← hl_st]; assumption
                    have hnr_256 : st.nres.toNat < 256 := by bv_omega
                    refine hJa _ (Eq.mp (congrArg (fun x =>
                      (KittenMemA kPtr acap x ⋆ R) _) ?_) hm)
                    unfold kAnaLit; dsimp only
                    rw [kana_ite_f hsk_ne, kana_ite_t hv0, kana_ite_t ⟨ha_ne, hr0_ne⟩]
                    unfold kResPush; rw [kana_ite_t hnr_256]
                    kstate_ext <;> (first | rfl | simp [hl_st])
                  · -- `ante ≠ 0 ∧ r0 ≠ 0xFFFFFFFF ∧ nres = 256`
                    have ha_ne : st.ante ≠ 0#32 := by assumption
                    have hr0_ne : st.rsn[(l >>> 1).toNat]?.getD 0#32 ≠ 0xFFFFFFFF#32 := by
                      rw [hv_eq', ← hl_st]; assumption
                    have hnr_ge : ¬ st.nres.toNat < 256 := by bv_omega
                    have hnr_eq : st.nres = 256#32 := hc
                    refine hJa _ (Eq.mp (congrArg (fun x =>
                      (KittenMemA kPtr acap x ⋆ R) _) ?_) hm)
                    unfold kAnaLit; dsimp only
                    rw [kana_ite_f hsk_ne, kana_ite_t hv0, kana_ite_t ⟨ha_ne, hr0_ne⟩]
                    unfold kResPush; rw [kana_ite_f hnr_ge, kana_ite_t hnr_eq]; kstate_ext <;> rfl
                  · -- `ante ≠ 0 ∧ r0 ≠ 0xFFFFFFFF ∧ nres > 256`
                    have ha_ne : st.ante ≠ 0#32 := by assumption
                    have hr0_ne : st.rsn[(l >>> 1).toNat]?.getD 0#32 ≠ 0xFFFFFFFF#32 := by
                      rw [hv_eq', ← hl_st]; assumption
                    have hnr_ge : ¬ st.nres.toNat < 256 := by bv_omega
                    have hnr_ne : st.nres ≠ 256#32 := hc
                    have hkana_eq : kAnaLit skip_v st l = st := by
                      unfold kAnaLit; dsimp only
                      rw [kana_ite_f hsk_ne, kana_ite_t hv0, kana_ite_t ⟨ha_ne, hr0_ne⟩]
                      unfold kResPush; rw [kana_ite_f hnr_ge, kana_ite_f hnr_ne]
                    exact hJa m'' (hkana_eq.symm ▸ hm'')
                  · -- `ante ≠ 0 ∧ r0 = 0xFFFFFFFF`
                    have hr0_eq : st.rsn[(l >>> 1).toNat]?.getD 0#32 = 0xFFFFFFFF#32 := by
                      rw [hv_eq', ← hl_st]; exact hc
                    have hkana_eq : kAnaLit skip_v st l = st := by
                      unfold kAnaLit; dsimp only
                      rw [kana_ite_f hsk_ne, kana_ite_t hv0, kana_ite_f (fun h => h.2 hr0_eq)]
                    exact hJa m'' (hkana_eq.symm ▸ hm'')
                  · -- `ante = 0`
                    have ha_eq : st.ante = 0#32 := hc
                    have hkana_eq : kAnaLit skip_v st l = st := by
                      unfold kAnaLit; dsimp only
                      rw [kana_ite_f hsk_ne, kana_ite_t hv0, kana_ite_f (fun h => h.1 ha_eq)]
                    exact hJa m'' (hkana_eq.symm ▸ hm'')
              · -- `vlvl ≠ 0`
                have hv_nz : st.lvlArr[(l >>> 1).toNat]?.getD 0#32 ≠ 0#32 := by
                  rw [hv_eq', ← hl_st]; exact hc
                c0_hsteps_nogrp
                refine wp_join0 (fun m3 => (KittenMemA kPtr acap (kAnaLit skip_v st l) ⋆ R) m3)
                  ?_ ?_
                · intro Jf m3 hm3; c0_hsteps!; exact hJvlvl m3 hm3
                · intro Jf hJf
                  c0_hsteps_nogrp
                  c0_hsplit
                  · -- `(fl &&& 2) = 0`: mark flag, push ana, then status / kl
                    have hfl0 : (st.flags[(l >>> 1).toNat]?.getD 0#32 &&& 2#32) = 0#32 := by
                      rw [hv_eq', ← hl_st]; exact hc
                    let fl' := st.flags[(l >>> 1).toNat]?.getD 0#32 ||| 2#32
                    let st1 : KittenState := { st with flags := st.flags.set (l >>> 1).toNat fl' }
                    let st2 : KittenState := if st1.nana.toNat < 128 then
                      { st1 with ana := st1.ana.set st1.nana.toNat (l >>> 1),
                                 nana := st1.nana + 1#32 }
                      else st1
                    c0_hsteps_nogrp
                    refine wp_join0 (fun m3 => (KittenMemA kPtr acap st2 ⋆ R) m3) ?_ ?_
                    · intro Jna m3 hm3
                      have hkana_st2 : kAnaLit skip_v st l =
                          if st.lvlArr[(l >>> 1).toNat]?.getD 0#32 = st.lvl then
                            { st2 with status := st2.status + 1#32 }
                          else if st2.nkl.toNat < 128 then
                            { st2 with kl := st2.kl.set st2.nkl.toNat l, nkl := st2.nkl + 1#32 }
                          else st2 := by
                        unfold kAnaLit; dsimp only
                        rw [kana_ite_f hsk_ne, kana_ite_f hv_nz, kana_ite_t hfl0]
                      c0_hsteps!
                      · -- `vlvl = clvl`
                        have htop : st.lvlArr[(l >>> 1).toNat]?.getD 0#32 = st.lvl := by
                          rw [hv_eq', ← hl_st, hlv_eq]; exact hc
                        refine hJf _ (Eq.mp (congrArg (fun x =>
                          (KittenMemA kPtr acap x ⋆ R) _) ?_) hm)
                        rw [hkana_st2, kana_ite_t htop]; kstate_ext <;> rfl
                      · -- `vlvl ≠ clvl ∧ nkl < 128`
                        have hntop : st.lvlArr[(l >>> 1).toNat]?.getD 0#32 ≠ st.lvl := by
                          rw [hv_eq', ← hl_st, hlv_eq]; assumption
                        have hnk_128 : st2.nkl.toNat < 128 := by bv_omega
                        refine hJf _ (Eq.mp (congrArg (fun x =>
                          (KittenMemA kPtr acap x ⋆ R) _) ?_) hm)
                        rw [hkana_st2, kana_ite_f hntop, kana_ite_t hnk_128]
                        kstate_ext <;> (first | rfl | simp only [hl_st])
                      · -- `vlvl ≠ clvl ∧ ¬ nkl < 128`
                        have hntop : st.lvlArr[(l >>> 1).toNat]?.getD 0#32 ≠ st.lvl := by
                          rw [hv_eq', ← hl_st, hlv_eq]; assumption
                        have hnk_ge : ¬ st2.nkl.toNat < 128 := by bv_omega
                        refine hJf _ (Eq.mp (congrArg (fun x =>
                          (KittenMemA kPtr acap x ⋆ R) _) ?_) hm3)
                        rw [hkana_st2, kana_ite_f hntop, kana_ite_f hnk_ge]
                    · intro Jna hJna
                      c0_hsteps_nogrp
                      c0_hsplit
                      · have hna_128 : st.nana.toNat < 128 := by bv_omega
                        have hna_28 : st.nana.toNat < 2 ^ 28 := by omega
                        c0_hsteps!
                        refine hJna _ (Eq.mp (congrArg (fun x =>
                          (KittenMemA kPtr acap x ⋆ R) _) ?_) hm)
                        dsimp only [st2, st1, fl']; rw [kana_ite_t hna_128]
                        kstate_ext <;> (first | rfl | (simp only [hl_st, hv_eq']; try rfl))
                      · have hna_ge : ¬ st.nana.toNat < 128 := by bv_omega
                        c0_hsteps!
                        refine hJna _ (Eq.mp (congrArg (fun x =>
                          (KittenMemA kPtr acap x ⋆ R) _) ?_) hm)
                        dsimp only [st2, st1, fl']; rw [kana_ite_f hna_ge]
                        kstate_ext <;> (first | rfl | (simp only [hl_st, hv_eq']; try rfl))
                  · -- `(fl &&& 2) ≠ 0`: already seen
                    have hfl_nz : (st.flags[(l >>> 1).toNat]?.getD 0#32 &&& 2#32) ≠ 0#32 := by
                      rw [hv_eq', ← hl_st]; exact hc
                    have hkana_eq : kAnaLit skip_v st l = st := by
                      unfold kAnaLit; dsimp only
                      rw [kana_ite_f hsk_ne, kana_ite_f hv_nz, kana_ite_f hfl_nz]
                    c0_hsteps!
                    exact hJf m'' (hkana_eq.symm ▸ hm'')
          · -- `l >>> 1 = skip_v`
            have hsk_eq : l >>> 1 = skip_v := by rw [← hl_st]; exact ‹_›
            have hkana_eq : kAnaLit skip_v st l = st := by
              unfold kAnaLit; dsimp only; rw [kana_ite_t hsk_eq]
            c0_hsteps!
            exact hJv m'' (hkana_eq.symm ▸ hm'')
      · -- Loop exit: `i = sz`
        have hi_eq : i.toNat = sz.toNat := by dsimp only [sz] at hi_le ⊢; bv_omega
        c0_hsteps!
        obtain ⟨_, hmFin⟩ := kittenMemA_to_mem hm''
        have hent := kAnaPrefix_entails hinv hcid hvdec hlits hcase
        dsimp only at hent
        have hst_fin : st = kAnaPrefix skip_v (kAnaInit ks cid) (kittenClauseOff ks cid.toNat)
            (kittenClauseSize ks cid.toNat) := by
          rw [hst, hi_eq]; rfl
        rw [hst_fin] at hmFin
        exact hQ _ _ hent.1 hent.2.1 hent.2.2.1 hent.2.2.2 hmFin
  · -- Entry `if (k[KH_ANTE] != 0u)` block
    intro J hJ
    c0_hsteps_nogrp
    c0_hsplit
    · have ha_ne : ks.ante ≠ 0#32 := ‹_›
      c0_hsteps_nogrp
      refine wp_join0 (fun m' => (KittenMemA kPtr acap (kAnaInit ks cid) ⋆ R) m') ?_ ?_
      · intro Jr m' hm'; c0_hsteps!; exact hJ m' hm'
      · intro Jr hJr
        c0_hsteps_nogrp
        c0_hsplit
        · have hnr_256 : ks.nres.toNat < 256 := by bv_omega
          have hnr_28 : ks.nres.toNat < 2 ^ 28 := by omega
          c0_hsteps!
          refine hJr _ (Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ R) _) ?_) hm)
          unfold kAnaInit kResPush; rw [kana_ite_t ha_ne, kana_ite_t hnr_256]; kstate_ext <;> rfl
        · have hnr_ge : ¬ ks.nres.toNat < 256 := by bv_omega
          c0_hsteps_nogrp
          refine wp_join0 (fun m' => (KittenMemA kPtr acap (kAnaInit ks cid) ⋆ R) m') ?_ ?_
          · intro Jr2 m' hm'; c0_hsteps!; exact hJr m' hm'
          · intro Jr2 hJr2
            c0_hsteps_nogrp
            c0_hsplit
            · have hnr_eq : ks.nres = 256#32 := ‹_›
              c0_hsteps!
              refine hJr2 _ (Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ R) _) ?_) hm)
              unfold kAnaInit kResPush; rw [kana_ite_t ha_ne, kana_ite_f hnr_ge, kana_ite_t hnr_eq]
              kstate_ext <;> rfl
            · have hnr_ne : ks.nres ≠ 256#32 := ‹_›
              c0_hsteps!
              refine hJr2 _ (Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ R) _) ?_) hmA)
              unfold kAnaInit kResPush; rw [kana_ite_t ha_ne, kana_ite_f hnr_ge, kana_ite_f hnr_ne]
    · have ha_eq : ks.ante = 0#32 := ‹_›
      c0_hsteps!
      refine hJ _ (Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ R) _) ?_) hmA)
      unfold kAnaInit; rw [kana_ite_f (fun h => h ha_eq)]

end LeanQbe.T.Examples.Kissat.Full
