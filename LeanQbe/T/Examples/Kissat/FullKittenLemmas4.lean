module

public import LeanQbe.T.Examples.Kissat.FullKittenLemmas4a

/-!
# Kissat `D-Full` Scratch `kitten` 1UIP Conflict Analysis `Func.wp` Proof (`Part 4`)

Re-exports `full_kitten_ana_clause_wp` (`[11]`, from `FullKittenLemmas4a`) and proves the
parametric `(Γ : Env)` `Func.wp` contract for `full_kitten_analyze_wp` (`[12]`):
1UIP resolution loop, flag cleanup, jump-level selection, backtrack + VMTF bump,
unit/multi-literal clause learning, watch attachment, and UIP assignment.
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

/-! ## 1. Pure Soundness Lemmas for `full_kitten_analyze` (`[12]`) -/

private theorem kana_xor1_div2 (l : Nat) : (l ^^^ 1) / 2 = l / 2 := by
  rw [litNeg_eq_xor1]; exact litVar_litNeg l

private theorem kana_litNeg_div2 (l : Nat) : litNeg l / 2 = l / 2 := litVar_litNeg l

private theorem kana_filterMap_congr {α β : Type} {f g : α → Option β} {xs : List α}
    (h : ∀ x ∈ xs, f x = g x) : xs.filterMap f = xs.filterMap g := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    simp only [List.filterMap_cons, h x List.mem_cons_self]
    rw [ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

private theorem kana_clauses_of_eq {acap : Nat} {ks1 ks2 : KittenState}
    (h : KittenClausesOk acap ks1)
    (hnres : ks2.nres.toNat ≤ kMaxL + 1) (hnkl : ks2.nkl.toNat ≤ kMaxV)
    (hnana : ks2.nana.toNat ≤ kMaxV)
    (hfl : ∀ v < ks2.nv.toNat, (ks2.flags[v]?.getD 0#32 &&& 2#32) = 0#32)
    (hac : ks2.acap = ks1.acap := by rfl) (hnv : ks2.nv = ks1.nv := by rfl)
    (hnc : ks2.nc = ks1.nc := by rfl) (honc : ks2.orig_nc = ks1.orig_nc := by rfl)
    (hal : ks2.alen = ks1.alen := by rfl) (hna : ks2.nassump = ks1.nassump := by rfl)
    (hnu : ks2.nunits = ks1.nunits := by rfl) (hinc : ks2.incons = ks1.incons := by rfl)
    (hfail : ks2.failing = ks1.failing := by rfl) (hante : ks2.ante = ks1.ante := by rfl)
    (hass : ks2.assump = ks1.assump := by rfl) (huni : ks2.units = ks1.units := by rfl)
    (hco : ks2.clOff = ks1.clOff := by rfl) (hcm : ks2.clMeta = ks1.clMeta := by rfl)
    (hca : ks2.clAux = ks1.clAux := by rfl) (har : ks2.arena = ks1.arena := by rfl)
    (hlvA : ks2.lvlArr = ks1.lvlArr := by rfl) (hrsn : ks2.rsn = ks1.rsn := by rfl)
    (hvals : ks2.vals = ks1.vals := by rfl) : KittenClausesOk acap ks2 := by
  have hcl : ∀ c, kittenClauseOff ks2 c = kittenClauseOff ks1 c ∧
      kittenClauseMeta ks2 c = kittenClauseMeta ks1 c ∧
      kittenClauseSize ks2 c = kittenClauseSize ks1 c ∧
      kittenClauseIsLrn ks2 c = kittenClauseIsLrn ks1 c ∧
      kittenClauseAux ks2 c = kittenClauseAux ks1 c ∧
      kittenClauseSpan ks2 c = kittenClauseSpan ks1 c ∧
      kittenClauseLits ks2 c = kittenClauseLits ks1 c ∧
      kittenClauseAnts ks2 c = kittenClauseAnts ks1 c := fun c =>
    ⟨by simp [kittenClauseOff, hco], by simp [kittenClauseMeta, hcm],
     by simp [kittenClauseSize, kittenClauseMeta, hcm],
     by simp [kittenClauseIsLrn, kittenClauseMeta, hcm], by simp [kittenClauseAux, hca],
     by simp [kittenClauseSpan, kittenClauseSize, kittenClauseIsLrn, kittenClauseAux,
       kittenClauseMeta, hcm, hca],
     by simp [kittenClauseLits, kittenClauseOff, kittenClauseSize, kittenClauseMeta, hco, hcm, har],
     by simp [kittenClauseAnts, kittenClauseIsLrn, kittenClauseOff, kittenClauseSize,
       kittenClauseAux, kittenClauseMeta, hco, hcm, hca, har]⟩
  have horig : kittenOrigClauses ks2 = kittenOrigClauses ks1 :=
    kittenOrigClauses_eq_of honc fun c _ => (hcl c).2.2.2.2.2.2.1
  refine ⟨h.acap_ge, h.acap_lt, by rw [hac]; exact h.acap_eq, by rw [hnv]; exact h.nv_le,
    by rw [hnc]; exact h.nc_le, by rw [honc, hnc]; exact h.orig_nc_le,
    by rw [honc]; exact h.orig_nc_max, by rw [hal]; exact h.alen_le,
    by rw [hna]; exact h.nassump_le, by rw [hnu]; exact h.nunits_le, hnres, hnkl, hnana,
    ?_, ?_, ?_, ?_, ?_, ?_, hfl⟩
  · intro c hc; rw [hnc] at hc
    have hw := h.cl_wf c hc; have he := hcl c
    rw [he.2.2.2.1, he.2.2.1, he.1, he.2.2.2.2.2.1, he.2.2.2.2.2.2.1, he.2.2.2.2.2.2.2,
      List.map_congr_left (fun a _ => (hcl a).2.2.2.2.2.2.1), horig, honc, hal, hnv, hante]
    exact hw
  · intro c1 c2 h12 hc2; rw [hnc] at hc2
    rw [(hcl c1).1, (hcl c1).2.2.2.2.2.1, (hcl c2).1]; exact h.cl_mono c1 c2 h12 hc2
  · intro ui hui; rw [hnu] at hui
    have hu := h.units_ok ui hui
    dsimp only; rw [huni, hnc, (hcl _).2.2.1]; exact hu
  · intro hi; rw [hinc] at hi
    have h1 := h.incons_ok hi
    refine ⟨by rw [hinc, hnc]; exact h1.1, by rw [horig]; exact h1.2.1, fun l hl => ?_⟩
    rw [hinc, (hcl _).2.2.2.2.2.2.1] at hl
    have h2 := h1.2.2 l hl
    refine ⟨by rw [hvals]; exact h2.1, by rw [hlvA]; exact h2.2.1, fun ha => ?_⟩
    rw [hante] at ha; have h3 := h2.2.2 ha
    dsimp only; rw [hnc, hrsn, (hcl _).2.2.2.2.2.2.1]; exact h3
  · intro ha hf; rw [hante] at ha; rw [hfail] at hf
    have h1 := h.failing_ok ha hf
    have hcm' : (fun ci => (kittenClauseMeta ks2 ci &&& kmCore) != 0#32) =
        (fun ci => (kittenClauseMeta ks1 ci &&& kmCore) != 0#32) :=
      funext fun ci => by rw [(hcl ci).2.1]
    have hmp' : List.map (kittenClauseLits ks2) = List.map (kittenClauseLits ks1) :=
      congrArg List.map (funext fun ci => (hcl ci).2.2.2.2.2.2.1)
    unfold kittenAssumpLits at h1 ⊢; rwa [hnc, hcm', hmp', hna, hass]
  · intro i hi; rw [hna] at hi; rw [hass, hnv]; exact h.assump_ok i hi

private theorem kana_inv_of_ana_clean {acap : Nat} {ks st : KittenState}
    (hinv : ks.Inv acap) (hsync : KittenTrailSynced ks) (hsh : st.ShapesOk acap)
    (hp : KittenAnaClausePreserved ks st)
    (hnres : st.nres.toNat ≤ kMaxL + 1) (hnkl : st.nkl.toNat ≤ kMaxV)
    (hnana : st.nana.toNat ≤ kMaxV)
    (hfl : ∀ v < st.nv.toNat, (st.flags[v]?.getD 0#32 &&& 2#32) = 0#32) :
    st.Inv acap ∧ KittenTrailSynced st := by
  have hcl := kana_clauses_of_eq hinv.clauses hnres hnkl hnana hfl hp.acap hp.nv hp.nc hp.orig_nc
    hp.alen hp.nassump hp.nunits hp.incons hp.failing hp.ante hp.assump hp.units hp.clOff hp.clMeta
    hp.clAux hp.arena hp.lvlArr hp.rsn hp.vals
  have hba := kana_baseAssign_of_eq hinv.assign hp.nv hp.nc hp.orig_nc hp.lvl hp.prop hp.trl_end
    hp.unass hp.ante hp.lvlArr hp.rsn hp.trl hp.vals hp.clOff hp.clMeta hp.arena
  have hw : KittenWatchesOk st := by
    obtain ⟨ch, h1, h2, h3, h4⟩ := hinv.watches
    refine ⟨ch, by rw [hp.nv]; exact h1, h2,
      fun l hl => by rw [hp.wnext, hp.whead]; exact h3 l (by rwa [← hp.nv]),
      fun l hl w hw => by
        simpa only [hp.nc, hp.nv, hp.arena, hp.wblit, kittenClauseSize, kittenClauseMeta,
          kittenClauseOff, hp.clMeta, hp.clOff] using h4 l (by rwa [← hp.nv]) w hw⟩
  have hrsn : ReasonOk st := fun i hi => by
    rw [hp.trl_end] at hi
    simpa only [hp.trl, hp.rsn, hp.nc, kittenClauseLits, kittenClauseOff, kittenClauseSize,
      kittenClauseMeta, hp.clOff, hp.clMeta, hp.arena] using hinv.reasons i hi
  have hsync' : KittenTrailSynced st := fun i hi => by
    rw [hp.trl_end] at hi; rw [hp.trl, hp.vals]; exact hsync i hi
  exact ⟨⟨hsh, hcl, hw, hba, hrsn⟩, hsync'⟩

private theorem kana_init_anaInv {acap : Nat} {ks : KittenState}
    (hinv : ks.Inv acap) (hsync : KittenTrailSynced ks) (hlvl_pos : 0 < ks.lvl.toNat)
    (hvdec : ∃ v < ks.nv.toNat, ks.lvlArr[v]?.getD 0#32 = ks.lvl) :
    let ks0 : KittenState := { ks with nres := 0#32, nkl := 1#32, nana := 0#32, status := 0#32 }
    KittenAnaInv acap ks0 (kittenOrigClauses ks) ks.trl_end.toNat ∧
    KittenAnaClausePreserved ks ks0 := by
  intro ks0
  have hsh0 : ks0.ShapesOk acap := by
    have heq : ks0 = (((ks.putHdr .nres 0#32).putHdr .nkl 1#32).putHdr .nana 0#32).putHdr
        .status 0#32 := by kstate_ext <;> rfl
    rw [heq]
    exact (((hinv.shapes.putHdr .nres 0#32).putHdr .nkl 1#32).putHdr .nana 0#32).putHdr .status 0#32
  have hnv_pos : 1 ≤ ks.nv.toNat := by obtain ⟨v, hv, _⟩ := hvdec; omega
  have hfl_clean : ∀ v < ks.nv.toNat, (ks.flags[v]?.getD 0#32 &&& 2#32) = 0#32 :=
    hinv.clauses.flags_clean
  have hfilt0 : ((List.range ks.trl_end.toNat).filter fun j =>
      let v := (ks0.trl[j]?.getD 0#32).toNat / 2
      decide (ks0.lvlArr[v]?.getD 0#32 = ks0.lvl ∧
        (ks0.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro j hj; rw [List.mem_range] at hj
    have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
      rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; have := hinv.clauses.nv_le
      unfold kMaxV at *; omega
    have hlt := hinv.assign.trl_lt _ (mem_kittenTrailLits_of_lt hj htrl_len)
    simp only [decide_eq_true_eq]
    intro h
    have hv_lt : (ks0.trl[j]?.getD 0#32).toNat / 2 < ks.nv.toNat := by
      change (ks.trl[j]?.getD 0#32).toNat / 2 < ks.nv.toNat; omega
    exact h.2 (hfl_clean _ hv_lt)
  refine ⟨⟨hsh0, hinv.clauses.nv_le, hinv.clauses.nc_le, hinv.clauses.orig_nc_le,
    hinv.clauses.orig_nc_max, hinv.clauses.alen_le, hinv.clauses.acap_lt, hinv.clauses.acap_eq,
    hlvl_pos, Nat.le_refl _, hinv.clauses.cl_wf, hinv.clauses.cl_mono, rfl, hinv.watches,
    kana_baseAssign_of_eq hinv.assign, hsync, hinv.reasons,
    by unfold kMaxL; change (0#32 : BitVec 32).toNat ≤ 256 + 1; decide,
    by change 1 ≤ (1#32 : BitVec 32).toNat; decide,
    by change (1#32 : BitVec 32).toNat ≤ ks.nv.toNat; exact hnv_pos,
    by change (0#32 : BitVec 32).toNat ≤ ks.nv.toNat; simp,
    by change ((ks.kl.take 0).map BitVec.toNat).Nodup; simp,
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
     rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ h => h⟩⟩

private theorem kana_resolvent_step_skip {acap : Nat} {st : KittenState} {F0 : List (List Nat)}
    {idx' : Nat} (hinv : KittenAnaInv acap st F0 (idx' + 1))
    (hskip : ¬ ((st.flags[(st.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32 ∧
      st.lvlArr[(st.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32 = st.lvl)) :
    KittenAnaInv acap st F0 idx' ∧
    kittenResolventLits st (idx' + 1) = kittenResolventLits st idx' := by
  have hdec_f : decide (st.lvlArr[(st.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32 = st.lvl ∧
      (st.flags[(st.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32) = false :=
    decide_eq_false fun h => hskip ⟨h.2, h.1⟩
  have hst_eq : st.status.toNat = ((List.range idx').filter fun j =>
      let v := (st.trl[j]?.getD 0#32).toNat / 2
      decide (st.lvlArr[v]?.getD 0#32 = st.lvl ∧
        (st.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32)).length := by
    have h := hinv.status_eq
    rw [List.range_succ, List.filter_append, List.filter_cons] at h
    simpa only [hdec_f, Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.append_nil] using h
  refine ⟨⟨hinv.shapes, hinv.nv_le, hinv.nc_le, hinv.orig_nc_le, hinv.orig_nc_max, hinv.alen_le,
    hinv.acap_lt, hinv.acap_eq, hinv.lvl_pos, by have := hinv.idx_le; omega, hinv.cl_wf,
    hinv.cl_mono, hinv.orig_eq, hinv.watches, hinv.assign, hinv.synced, hinv.reasons, hinv.nres_le,
    hinv.nkl_pos, hinv.nkl_le, hinv.nana_le, hinv.ana_nodup, hinv.ana_lt, hinv.flags_seen,
    hinv.kl_nonTop, hinv.kl_injective, hinv.nkl_count, hinv.kl_nodup, hst_eq, hinv.seen_in_trl⟩,
    ?_⟩
  unfold kittenResolventLits
  rw [List.range_succ, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  have hno : ¬ (st.lvlArr[(st.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32 = st.lvl ∧
      (st.flags[(st.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32) :=
    fun h => hskip ⟨h.2, h.1⟩
  simp [hno]

private theorem kana_resolvent_step_hit {acap : Nat} {st : KittenState} {F0 : List (List Nat)}
    {idx' : Nat} (hinv : KittenAnaInv acap st F0 (idx' + 1))
    (hhit : (st.flags[(st.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32 ∧
      st.lvlArr[(st.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32 = st.lvl) :
    let p := st.trl[idx']?.getD 0#32
    let st1 : KittenState := { st with status := st.status - 1#32 }
    0 < st.status.toNat ∧ KittenAnaInv acap st1 F0 idx' ∧
    KittenAnaClausePreserved st st1 ∧
    ∀ x ∈ kittenResolventLits st (idx' + 1),
      x ∈ (p.toNat ^^^ 1) :: kittenResolventLits st1 idx' := by
  intro p st1
  have hdec_t : decide (st.lvlArr[(st.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32 = st.lvl ∧
      (st.flags[(st.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32) = true :=
    decide_eq_true ⟨hhit.2, hhit.1⟩
  have hst_succ : st.status.toNat = ((List.range idx').filter fun j =>
      let v := (st.trl[j]?.getD 0#32).toNat / 2
      decide (st.lvlArr[v]?.getD 0#32 = st.lvl ∧
        (st.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32)).length + 1 := by
    have h := hinv.status_eq
    rw [List.range_succ, List.filter_append, List.filter_cons] at h
    simpa only [hdec_t, ↓reduceIte, List.filter_nil, List.length_append, List.length_singleton]
      using h
  have hpos : 0 < st.status.toNat := by omega
  have hsub : (st.status - 1#32).toNat = st.status.toNat - 1 := by bv_omega
  have hsh1 : st1.ShapesOk acap := by
    have heq : st1 = st.putHdr .status (st.status - 1#32) := by kstate_ext <;> rfl
    rw [heq]; exact hinv.shapes.putHdr .status _
  have hinv1 : KittenAnaInv acap st1 F0 idx' :=
    ⟨hsh1, hinv.nv_le, hinv.nc_le, hinv.orig_nc_le, hinv.orig_nc_max, hinv.alen_le,
      hinv.acap_lt, hinv.acap_eq, hinv.lvl_pos,
      (by change idx' ≤ st.trl_end.toNat; have := hinv.idx_le; omega),
      hinv.cl_wf, hinv.cl_mono, hinv.orig_eq, hinv.watches, kana_baseAssign_of_eq hinv.assign,
      hinv.synced, hinv.reasons, hinv.nres_le, hinv.nkl_pos, hinv.nkl_le, hinv.nana_le,
      hinv.ana_nodup, hinv.ana_lt, hinv.flags_seen, hinv.kl_nonTop, hinv.kl_injective,
      hinv.nkl_count, hinv.kl_nodup,
      (by change (st.status - 1#32).toNat = ((List.range idx').filter fun j =>
            let v := (st.trl[j]?.getD 0#32).toNat / 2
            decide (st.lvlArr[v]?.getD 0#32 = st.lvl ∧
              (st.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32)).length
          rw [hsub, hst_succ]; omega), hinv.seen_in_trl⟩
  refine ⟨hpos, hinv1,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
     rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ h => h⟩, fun x hx => ?_⟩
  rw [kana_mem_resolvent_iff] at hx
  rw [List.mem_cons, kana_mem_resolvent_iff]
  rcases hx with ⟨j, hj, htrl, hlvl, hfl⟩ | hr
  · by_cases hji : j = idx'
    · left; subst hji
      have hx_eq : p.toNat = x ^^^ 1 := htrl
      rw [hx_eq, litNeg_eq_xor1, litNeg_eq_xor1, litNeg_litNeg]
    · right; left; exact ⟨j, by omega, htrl, hlvl, hfl⟩
  · right; right; exact hr

private theorem kana_uip_exit {acap : Nat} {st1 : KittenState} {F0 : List (List Nat)} {idx' : Nat}
    (hinv : KittenAnaInv acap st1 F0 idx') (hst0 : st1.status = 0#32) :
    kittenResolventLits st1 idx' = ((st1.kl.take st1.nkl.toNat).drop 1).map BitVec.toNat := by
  have hfilt_nil : ((List.range idx').filter fun j =>
      let v := (st1.trl[j]?.getD 0#32).toNat / 2
      decide (st1.lvlArr[v]?.getD 0#32 = st1.lvl ∧
        (st1.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32)) = [] := by
    have h := hinv.status_eq
    rw [hst0] at h
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
  unfold kittenResolventLits
  have hfm : ((List.range idx').filterMap fun j =>
      let l := (st1.trl[j]?.getD 0#32).toNat
      if st1.lvlArr[l / 2]?.getD 0#32 = st1.lvl ∧ (st1.flags[l / 2]?.getD 0#32 &&& 2#32) ≠ 0#32
      then some (l ^^^ 1) else none) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro j hj; rw [List.mem_range] at hj; dsimp only; rw [kana_ite_f (hno j hj)]
  rw [hfm, List.nil_append]

private theorem kana_rsn_pre {acap : Nat} {st1 : KittenState} {F0 : List (List Nat)} {idx' : Nat}
    (hinv : KittenAnaInv acap st1 F0 idx') (hidx' : idx' < st1.trl_end.toNat)
    (hpos : 0 < st1.status.toNat)
    (hlvl_p : st1.lvlArr[(st1.trl[idx']?.getD 0#32).toNat / 2]?.getD 0#32 = st1.lvl) :
    let p := st1.trl[idx']?.getD 0#32
    let pv := p >>> 1
    let rsn := st1.rsn[pv.toNat]?.getD 0#32
    p.toNat < 2 * st1.nv.toNat ∧ pv.toNat = p.toNat / 2 ∧ pv.toNat < st1.nv.toNat ∧
    rsn ≠ 0xFFFFFFFF#32 ∧ rsn.toNat < st1.nc.toNat ∧
    p.toNat ∈ kittenClauseLits st1 rsn.toNat ∧
    (∀ l ∈ kittenClauseLits st1 rsn.toNat, l / 2 = pv.toNat → l = p.toNat) ∧
    (∀ l ∈ kittenClauseLits st1 rsn.toNat, l / 2 ≠ pv.toNat →
      ∃ j < idx', (st1.trl[j]?.getD 0#32).toNat = l ^^^ 1) := by
  intro p pv rsn
  have htrl_len : st1.trl_end.toNat ≤ st1.trl.length := by
    rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; have := hinv.nv_le
    unfold kMaxV at *; omega
  have hp_lt : p.toNat < 2 * st1.nv.toNat :=
    hinv.assign.trl_lt _ (mem_kittenTrailLits_of_lt hidx' htrl_len)
  obtain ⟨hpv_eq, hpv_lt⟩ := bv32_lit_div2_bv hp_lt
  have hfilt_ne : ((List.range idx').filter fun j =>
      let v := (st1.trl[j]?.getD 0#32).toNat / 2
      decide (st1.lvlArr[v]?.getD 0#32 = st1.lvl ∧
        (st1.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32)) ≠ [] := by
    intro hnil; have h := hinv.status_eq; rw [hnil] at h; simp at h; omega
  obtain ⟨j0, hj0_mem⟩ := List.exists_mem_of_ne_nil _ hfilt_ne
  rw [List.mem_filter, List.mem_range, decide_eq_true_eq] at hj0_mem
  have hrsn_ne : rsn ≠ 0xFFFFFFFF#32 := by
    dsimp only [rsn]; rw [hpv_eq]
    exact hinv.assign.dec_earliest idx' j0 hj0_mem.1 hidx' (hj0_mem.2.1.trans hlvl_p.symm)
  have hro := hinv.reasons idx' hidx'
  dsimp only at hro
  have hrsn_eq : st1.rsn[p.toNat / 2]?.getD 0#32 = rsn := by dsimp only [rsn]; rw [hpv_eq]
  rw [hrsn_eq] at hro
  rcases hro with hff | ⟨hr_lt, hp_mem, hall⟩
  · exact absurd hff hrsn_ne
  · refine ⟨hp_lt, hpv_eq, hpv_lt, hrsn_ne, hr_lt, hp_mem, ?_, ?_⟩
    · intro l hl hlv
      by_cases hlp : l = p.toNat
      · exact hlp
      · exfalso
        obtain ⟨j, hj, hjeq⟩ := hall l hl hlp
        have hvar : (st1.trl[j]?.getD 0#32).toNat / 2 = p.toNat / 2 := by
          rw [hjeq, kana_xor1_div2, hlv, hpv_eq]
        exact kana_trl_nodup_var_ne hinv.shapes hinv.nv_le hinv.assign
          (Nat.lt_trans hj hidx') hidx' (by omega) hvar
    · intro l hl hne
      have hlp : l ≠ p.toNat := fun heq => hne (by rw [heq, hpv_eq])
      exact hall l hl hlp

private theorem kana_swap_kl_preserves {acap : Nat} {stClean : KittenState}
    {uip wi jlvl : BitVec 32}
    (hinv : stClean.Inv acap) (hsync : KittenTrailSynced stClean)
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
    stSw.Inv acap ∧ KittenTrailSynced stSw ∧ KittenAnaClausePreserved stClean stSw ∧
    stSw.nkl = stClean.nkl ∧ stSw.nana = stClean.nana ∧ stSw.ana = stClean.ana ∧
    stSw.nres = stClean.nres ∧ stSw.res = stClean.res ∧
    stSw.kl[0]? = some uip ∧
    (∀ x ∈ uip.toNat :: ((stClean.kl.take stClean.nkl.toNat).drop 1).map BitVec.toNat,
      x ∈ (stSw.kl.take stSw.nkl.toNat).map BitVec.toNat) ∧
    (∀ k, 1 ≤ k → k < stSw.nkl.toNat →
      let l := (stSw.kl[k]?.getD 0#32).toNat
      l < 2 * stSw.nv.toNat ∧ 0 < (stSw.lvlArr[l / 2]?.getD 0#32).toNat ∧
      (stSw.lvlArr[l / 2]?.getD 0#32).toNat ≤ jlvl.toNat ∧ stSw.vals[l]? = some 2#32) := by
  intro stKl0 stSw
  have hnv := hinv.clauses.nv_le
  have hkl_len : stClean.kl.length = 128 := hinv.shapes.kl_len
  have hsh0 : stKl0.ShapesOk acap := hinv.shapes.putArr .kl 0 uip
  have hshSw : stSw.ShapesOk acap := by
    dsimp only [stSw]; by_cases hc : 2 ≤ stClean.nkl.toNat ∧ wi ≠ 1#32
    · rw [kana_ite_t hc]; exact (hsh0.putArr .kl _ _).putArr .kl _ _
    · rw [kana_ite_f hc]; exact hsh0
  have hfr : ∃ kl', stSw = { stClean with kl := kl' } := by
    dsimp only [stSw, stKl0]; by_cases hc : 2 ≤ stClean.nkl.toNat ∧ wi ≠ 1#32
    · rw [kana_ite_t hc]; exact ⟨_, by kstate_ext <;> rfl⟩
    · rw [kana_ite_f hc]; exact ⟨_, by kstate_ext <;> rfl⟩
  obtain ⟨kl', hfr_eq⟩ := hfr
  have hpres : KittenAnaClausePreserved stClean stSw := by
    rw [hfr_eq]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ h => h⟩
  have ⟨hinvSw, hsyncSw⟩ := kana_inv_of_ana_clean hinv hsync hshSw hpres
    (by rw [hfr_eq]; exact hinv.clauses.nres_le) (by rw [hfr_eq]; exact hinv.clauses.nkl_le)
    (by rw [hfr_eq]; exact hinv.clauses.nana_le) (by rw [hfr_eq]; exact hinv.clauses.flags_clean)
  have hkl0_0 : stKl0.kl[0]? = some uip := by
    dsimp only [stKl0]; kp_field; exact List.getElem?_set_self (by omega)
  have hkl0_pos : ∀ k, 1 ≤ k → stKl0.kl[k]? = stClean.kl[k]? := fun k hk => by
    dsimp only [stKl0]; kp_field; exact List.getElem?_set_ne (by omega)
  have hsw_nkl : stSw.nkl = stClean.nkl := by rw [hfr_eq]
  have hsw0 : stSw.kl[0]? = some uip := by
    dsimp only [stSw]; by_cases hc : 2 ≤ stClean.nkl.toNat ∧ wi ≠ 1#32
    · rw [kana_ite_t hc]; have ⟨hw1, _⟩ := hwi hc.1
      kp_field; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact hkl0_0
    · rw [kana_ite_f hc]; exact hkl0_0
  have hmem_of_idx : ∀ k < stClean.nkl.toNat,
      (stSw.kl[k]?.getD 0#32).toNat ∈ (stSw.kl.take stSw.nkl.toNat).map BitVec.toNat := by
    intro k hk
    have hk_len : k < stSw.kl.length := by rw [hshSw.kl_len]; unfold kMaxV at hnv; omega
    rw [List.mem_map]
    refine ⟨stSw.kl[k]'hk_len, ?_, by simp [List.getElem?_eq_getElem hk_len]⟩
    rw [List.mem_take_iff_getElem]; exact ⟨k, by rw [hsw_nkl]; omega, rfl⟩
  have hbij : ∀ k, 1 ≤ k → k < stClean.nkl.toNat →
      ∃ k', 1 ≤ k' ∧ k' < stClean.nkl.toNat ∧ stSw.kl[k]? = stClean.kl[k']? := by
    intro k hk1 hk_lt
    by_cases hc : 2 ≤ stClean.nkl.toNat ∧ wi ≠ 1#32
    · obtain ⟨hw1, hw_lt⟩ := hwi hc.1
      have hw_ne1 : wi.toNat ≠ 1 := fun h => hc.2 (BitVec.eq_of_toNat_eq h)
      have hkl_sw : stSw.kl = (stKl0.kl.set 1 (stKl0.kl[wi.toNat]?.getD 0#32)).set wi.toNat
          (stKl0.kl[1]?.getD 0#32) := by dsimp only [stSw]; rw [kana_ite_t hc]; kp_field
      have hl1 : 1 < stClean.kl.length := by omega
      have hlw : wi.toNat < stClean.kl.length := by unfold kMaxV at hnv; omega
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
      have hkl_sw : stSw.kl = stKl0.kl := by dsimp only [stSw]; rw [kana_ite_f hc]
      rw [hkl_sw, hkl0_pos k hk1]
  refine ⟨hinvSw, hsyncSw, hpres, hsw_nkl, by rw [hfr_eq], by rw [hfr_eq], by rw [hfr_eq],
    by rw [hfr_eq], hsw0, ?_, ?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx_tl
    · have h0 := hmem_of_idx 0 (by omega)
      rwa [hsw0, Option.getD_some] at h0
    · rw [List.mem_map] at hx_tl; obtain ⟨b, hb, rfl⟩ := hx_tl
      rw [List.mem_iff_getElem] at hb; obtain ⟨k, hk, rfl⟩ := hb
      have hk1 : k + 1 < stClean.nkl.toNat := by
        simp [List.length_take, hkl_len] at hk; unfold kMaxV at hnv; omega
      have hb_eq : (((stClean.kl.take stClean.nkl.toNat).drop 1)[k]'hk) =
          stClean.kl[k + 1]?.getD 0#32 := by
        simp only [List.getElem_drop, List.getElem_take]
        rw [List.getElem?_eq_getElem (by unfold kMaxV at hnv; omega), Option.getD_some]
        congr 1; omega
      rw [hb_eq]
      by_cases hc : 2 ≤ stClean.nkl.toNat ∧ wi ≠ 1#32
      · obtain ⟨hw1, hw_lt⟩ := hwi hc.1
        have hw_ne1 : wi.toNat ≠ 1 := fun h => hc.2 (BitVec.eq_of_toNat_eq h)
        have hkl_sw : stSw.kl = (stKl0.kl.set 1 (stKl0.kl[wi.toNat]?.getD 0#32)).set wi.toNat
            (stKl0.kl[1]?.getD 0#32) := by dsimp only [stSw]; rw [kana_ite_t hc]; kp_field
        have h1 : stSw.kl[wi.toNat]? = stClean.kl[1]? := by
          have hlen_w : wi.toNat < (stKl0.kl.set 1 (stKl0.kl[wi.toNat]?.getD 0#32)).length := by
            rw [List.length_set, hsh0.kl_len]; unfold kMaxV at hnv; omega
          rw [hkl_sw, List.getElem?_set_self hlen_w,
            hkl0_pos 1 (by omega), List.getElem?_eq_getElem (by omega : 1 < stClean.kl.length),
            Option.getD_some]
        have h2 : stSw.kl[1]? = stClean.kl[wi.toNat]? := by
          rw [hkl_sw, List.getElem?_set_ne (by omega),
            List.getElem?_set_self (by rw [hsh0.kl_len]; decide),
            hkl0_pos wi.toNat hw1,
            List.getElem?_eq_getElem (by unfold kMaxV at hnv; omega : wi.toNat < stClean.kl.length),
            Option.getD_some]
        by_cases hk_1 : k + 1 = 1
        · rw [hk_1, ← h1]; exact hmem_of_idx wi.toNat hw_lt
        · by_cases hk_w : k + 1 = wi.toNat
          · rw [hk_w, ← h2]; exact hmem_of_idx 1 (by omega)
          · have h3 : stSw.kl[k + 1]? = stClean.kl[k + 1]? := by
              rw [hkl_sw, List.getElem?_set_ne (Ne.symm hk_w), List.getElem?_set_ne (Ne.symm hk_1),
                hkl0_pos (k + 1) (by omega)]
            rw [← h3]; exact hmem_of_idx (k + 1) hk1
      · have h3 : stSw.kl[k + 1]? = stClean.kl[k + 1]? := by
          have hkl_sw : stSw.kl = stKl0.kl := by dsimp only [stSw]; rw [kana_ite_f hc]
          rw [hkl_sw, hkl0_pos (k + 1) (by omega)]
        rw [← h3]; exact hmem_of_idx (k + 1) hk1
  · intro k hk1 hk_lt
    rw [hsw_nkl] at hk_lt
    obtain ⟨k', hk'1, hk'lt, hkeq⟩ := hbij k hk1 hk_lt
    dsimp only; rw [hkeq, hfr_eq]; exact hkl_nt k' hk'1 hk'lt

private theorem kana_after_bt_facts {acap : Nat} {ks stSw ksBt : KittenState}
    {uip jlvl : BitVec 32}
    (hinvSw : stSw.Inv acap) (hsyncSw : KittenTrailSynced stSw)
    (hpresSw : KittenAnaClausePreserved ks stSw)
    (huip_lt : uip.toNat < 2 * ks.nv.toNat)
    (huip_lvl : ks.lvlArr[uip.toNat / 2]?.getD 0#32 = ks.lvl)
    (hjlvl_lt : jlvl.toNat < ks.lvl.toNat)
    (hinvBt : ksBt.Inv acap) (hlvlBt : ksBt.lvl = jlvl)
    (hte_le : ksBt.trl_end.toNat ≤ stSw.trl_end.toNat)
    (htake : ksBt.trl.take ksBt.trl_end.toNat = stSw.trl.take ksBt.trl_end.toNat)
    (hbtPres : KittenBtPreserved stSw ksBt)
    (hdecBt : ∀ d ∈ kittenTrailDecisions ksBt, ∃ i < ksBt.trl_end.toNat,
      (stSw.trl[i]?.getD 0#32).toNat = d ∧ d ∈ kittenTrailDecisions stSw)
    (hB1 : ∀ i < stSw.trl_end.toNat,
      (stSw.lvlArr[(stSw.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ jlvl.toNat →
      i < ksBt.trl_end.toNat) :
    (¬ ∃ i < ksBt.trl_end.toNat, (ksBt.trl[i]?.getD 0#32).toNat / 2 = uip.toNat / 2) ∧
    ksBt.vals[uip.toNat]? = some 0#32 ∧ ksBt.vals[uip.toNat ^^^ 1]? = some 0#32 ∧
    ksBt.trl_end.toNat < ksBt.nv.toNat ∧
    (∀ l < 2 * ks.nv.toNat, stSw.vals[l]? = some 2#32 →
      (ks.lvlArr[l / 2]?.getD 0#32).toNat ≤ jlvl.toNat →
      ∃ j < ksBt.trl_end.toNat, (ksBt.trl[j]?.getD 0#32).toNat = l ^^^ 1) ∧
    (∀ d ∈ kittenTrailDecisions ksBt, ∃ i < ks.trl_end.toNat,
      (ks.trl[i]?.getD 0#32).toNat = d ∧ d ∈ kittenTrailDecisions ks ∧
      (ks.lvlArr[d / 2]?.getD 0#32).toNat ≤ jlvl.toNat) ∧
    (∀ i < ks.trl_end.toNat,
      (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ jlvl.toNat →
      i < ksBt.trl_end.toNat ∧ ksBt.trl[i]? = ks.trl[i]? ∧
      ksBt.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]? =
        ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?) := by
  have hnv_eq : ksBt.nv = ks.nv := hbtPres.nv.trans hpresSw.nv
  have hnv := hinvBt.clauses.nv_le
  have htrl_i : ∀ i < ksBt.trl_end.toNat, ksBt.trl[i]? = ks.trl[i]? := fun i hi => by
    have h1 := congrArg (fun l => l[i]?) htake
    rw [List.getElem?_take_of_lt hi, List.getElem?_take_of_lt hi, hpresSw.trl] at h1
    exact h1
  have huip_none : ¬ ∃ i < ksBt.trl_end.toNat,
      (ksBt.trl[i]?.getD 0#32).toNat / 2 = uip.toNat / 2 := by
    rintro ⟨i, hi, hiv⟩
    have hkept := hbtPres.lvlArr_kept i hi
    rw [hiv, hpresSw.lvlArr] at hkept
    have hle := hinvBt.assign.trl_lvl_le (uip.toNat / 2) (by rw [hnv_eq]; omega)
    rw [hkept, huip_lvl, hlvlBt] at hle; omega
  have huip_v0 : ksBt.vals[uip.toNat]? = some 0#32 := by
    have hlen : uip.toNat < ksBt.vals.length := by
      rw [hinvBt.shapes.vals_len]; rw [hnv_eq] at hnv; unfold kMaxV at hnv; omega
    have h0 : ksBt.vals[uip.toNat]?.getD 0#32 = 0#32 := by
      by_cases h : ksBt.vals[uip.toNat]?.getD 0#32 = 0#32
      · exact h
      · have hex := (hinvBt.assign.vals_nz_iff_trl uip.toNat (by rw [hnv_eq]; exact huip_lt)).mp h
        exact absurd hex huip_none
    rw [List.getElem?_eq_getElem hlen] at h0 ⊢; exact congrArg some h0
  have huip_nv0 : ksBt.vals[uip.toNat ^^^ 1]? = some 0#32 := by
    have hnl_lt : (uip.toNat ^^^ 1) < 2 * ksBt.nv.toNat := by
      rw [hnv_eq]; rcases nat_xor1_cases uip.toNat with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega
    have hlen : (uip.toNat ^^^ 1) < ksBt.vals.length := by
      rw [hinvBt.shapes.vals_len]; unfold kMaxV at hnv; omega
    have h0 : ksBt.vals[uip.toNat ^^^ 1]?.getD 0#32 = 0#32 := by
      by_cases h : ksBt.vals[uip.toNat ^^^ 1]?.getD 0#32 = 0#32
      · exact h
      · obtain ⟨i, hi, hiv⟩ := (hinvBt.assign.vals_nz_iff_trl (uip.toNat ^^^ 1) hnl_lt).mp h
        rw [kana_xor1_div2] at hiv
        exact absurd ⟨i, hi, hiv⟩ huip_none
    rw [List.getElem?_eq_getElem hlen] at h0 ⊢; exact congrArg some h0
  have hte_lt_nv : ksBt.trl_end.toNat < ksBt.nv.toNat := by
    have htrl_len : ksBt.trl_end.toNat ≤ ksBt.trl.length := by
      rw [hinvBt.shapes.trl_len]; have := hinvBt.assign.trl_end_le; unfold kMaxV at hnv; omega
    let vs := (kittenTrailLits ksBt).map (· / 2)
    have hv_not : uip.toNat / 2 ∉ vs := by
      intro hm; rw [List.mem_map] at hm; obtain ⟨t, ht, htv⟩ := hm
      unfold kittenTrailLits at ht; rw [List.mem_map] at ht; obtain ⟨b, hb, rfl⟩ := ht
      rw [List.mem_take_iff_getElem] at hb; obtain ⟨i, hi, rfl⟩ := hb
      exact huip_none ⟨i, by omega, by
        rw [List.getElem?_eq_getElem (by omega : i < ksBt.trl.length), Option.getD_some]; exact htv⟩
    have hnd : (uip.toNat / 2 :: vs).Nodup := List.nodup_cons.mpr ⟨hv_not, hinvBt.assign.trl_nodup⟩
    have hlt_all : ∀ x ∈ uip.toNat / 2 :: vs, x < ksBt.nv.toNat := fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · rw [hnv_eq]; omega
      · rw [List.mem_map] at hx'; obtain ⟨t, ht, rfl⟩ := hx'
        have := hinvBt.assign.trl_lt t ht; omega
    have hle := kana_nodup_subset_length hnd hlt_all
    simp only [vs, kittenTrailLits, List.length_cons, List.length_map, List.length_take] at hle
    omega
  have hdec_eq : kittenTrailDecisions stSw = kittenTrailDecisions ks := by
    unfold kittenTrailDecisions; rw [hpresSw.trl, hpresSw.trl_end, hpresSw.rsn]
  refine ⟨huip_none, huip_v0, huip_nv0, hte_lt_nv, ?_, ?_, ?_⟩
  · intro l hl hval hlv
    obtain ⟨j, hj, hjeq⟩ := kitten_falsified_to_trail hinvSw.shapes hinvSw.clauses.nv_le
      hinvSw.assign hsyncSw (by rw [hpresSw.nv]; exact hl) hval
    have hj_lv : (stSw.lvlArr[(stSw.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        jlvl.toNat := by
      rw [hjeq, kana_litNeg_div2, hpresSw.lvlArr]; exact hlv
    have hj_bt := hB1 j hj hj_lv
    refine ⟨j, hj_bt, ?_⟩
    rw [htrl_i j hj_bt, ← hpresSw.trl, hjeq, ← litNeg_eq_xor1]
  · intro d hd
    obtain ⟨i, hi_bt, htrl_d, hd_sw⟩ := hdecBt d hd
    have hi_ks : i < ks.trl_end.toNat := by rw [← hpresSw.trl_end]; omega
    rw [hpresSw.trl] at htrl_d
    rw [hdec_eq] at hd_sw
    have hkept := hbtPres.lvlArr_kept i hi_bt
    rw [htrl_i i hi_bt, htrl_d, hpresSw.lvlArr] at hkept
    have htrl_len : ksBt.trl_end.toNat ≤ ksBt.trl.length := by
      rw [hinvBt.shapes.trl_len]; have := hinvBt.assign.trl_end_le; unfold kMaxV at hnv; omega
    have hd_lt : d < 2 * ksBt.nv.toNat := by
      have hm := mem_kittenTrailLits_of_lt hi_bt htrl_len
      rw [htrl_i i hi_bt, htrl_d] at hm; exact hinvBt.assign.trl_lt d hm
    have hlv := hinvBt.assign.trl_lvl_le (d / 2) (by omega)
    rw [hkept, hlvlBt] at hlv
    exact ⟨i, hi_ks, htrl_d, hd_sw, hlv⟩
  · intro i hi hlv
    have hi_bt := hB1 i (by rw [hpresSw.trl_end]; exact hi)
      (by rw [hpresSw.lvlArr, hpresSw.trl]; exact hlv)
    have hkept := hbtPres.lvlArr_kept i hi_bt
    rw [htrl_i i hi_bt, hpresSw.lvlArr] at hkept
    exact ⟨hi_bt, htrl_i i hi_bt, hkept⟩

private theorem kana_unit0_to_inv {acap : Nat} {ks ks' : KittenState}
    (hinv : ks.Inv acap) (hsync : KittenTrailSynced ks)
    (hsh' : ks'.ShapesOk acap) (hcl' : KittenClausesOk acap ks')
    (hnc' : ks'.nc = ks.nc + 1#32) (hp : KittenUnit0Preserved ks ks') :
    ks'.Inv acap ∧ KittenTrailSynced ks' ∧
    kittenOrigClauses ks' = kittenOrigClauses ks ∧
    (∀ ci < ks.orig_nc.toNat, ks'.clAux[ci]? = ks.clAux[ci]? ∧
      (ks'.clMeta[ci]?.getD 0#32 &&& kmCore) = (ks.clMeta[ci]?.getD 0#32 &&& kmCore)) := by
  have hnc_lt : ks.nc.toNat < ks'.nc.toNat := by
    have := hinv.clauses.nc_le; unfold kMaxCl at this; rw [hnc']; bv_omega
  have horig : kittenOrigClauses ks' = kittenOrigClauses ks :=
    kittenOrigClauses_eq_of hp.orig_nc fun c hc => by
      rw [hp.orig_nc] at hc
      exact (hp.old_clauses c (Nat.lt_of_lt_of_le hc hinv.clauses.orig_nc_le)).2.2.2
  have hw' : KittenWatchesOk ks' := by
    obtain ⟨ch, h1, h2, h3, h4⟩ := hinv.watches
    refine ⟨ch, by rw [hp.nv]; exact h1, h2,
      fun l hl => by rw [hp.wnext, hp.whead]; exact h3 l (by rwa [← hp.nv]),
      fun l hl w hw => ?_⟩
    have hb := h4 l (by rwa [← hp.nv]) w hw
    have hc_lt : w / 2 < ks.nc.toNat := Nat.div_lt_of_lt_mul hb.1
    have ho := hp.old_clauses (w / 2) hc_lt
    have hwf := hinv.clauses.cl_wf (w / 2) hc_lt
    have hbd : kittenClauseOff ks (w / 2) + w % 2 < ks.alen.toNat := by
      have := hwf.2.2.1; unfold kittenClauseSpan at this; omega
    refine ⟨by omega, by rw [kittenClauseSize, ho.2.1]; exact hb.2.1, ?_,
      by rw [hp.wblit, hp.nv]; exact hb.2.2.2⟩
    rw [ho.1, hp.arena_old _ hbd]; exact hb.2.2.1
  have hba' : KittenBaseAssignOk ks' :=
    ⟨by rw [hp.trl_end, hp.nv]; exact hinv.assign.trl_end_le,
     by rw [hp.prop, hp.trl_end]; exact hinv.assign.prop_le,
     by rw [hp.unass, hp.trl_end, hp.nv]; exact hinv.assign.unass_eq,
     by rw [hp.nv, hp.vals]; exact hinv.assign.vals_dom,
     by rw [hp.nv, hp.vals]; exact hinv.assign.vals_neg_iff,
     by rw [hp.nv, hp.vals, hp.trl_end, hp.trl]; exact hinv.assign.vals_nz_iff_trl,
     by unfold kittenTrailLits; rw [hp.trl, hp.trl_end]; exact hinv.assign.trl_nodup,
     by unfold kittenTrailLits; rw [hp.trl, hp.trl_end, hp.nv]; exact hinv.assign.trl_lt,
     by rw [hp.nv, hp.lvlArr, hp.lvl]; exact hinv.assign.trl_lvl_le,
     by rw [hp.nv, hp.vals, hp.lvlArr, hp.rsn]; exact hinv.assign.unass_lvl_zero,
     by rw [hp.trl_end, hp.lvlArr, hp.trl]; exact hinv.assign.trl_lvl_mono,
     by rw [hp.trl_end, hp.lvlArr, hp.trl, hp.rsn]; exact hinv.assign.dec_earliest,
     fun i hi hl0 => by
       rw [hp.trl_end] at hi; rw [hp.trl, hp.lvlArr] at hl0
       have h0 := hinv.assign.lvl0_ok i hi hl0
       refine ⟨by rw [hp.trl, hp.rsn]; exact h0.1, by rw [hp.trl, hp.vals]; exact h0.2.1,
         by rw [hp.trl, hp.vals]; exact h0.2.2.1, by rw [horig, hp.trl]; exact h0.2.2.2.1,
         fun ha => ?_⟩
       rw [hp.ante] at ha; have h1 := h0.2.2.2.2 ha
       dsimp only; rw [hp.trl, hp.rsn]
       exact ⟨by omega, by rw [(hp.old_clauses _ h1.1).2.2.2]; exact h1.2⟩⟩
  have hrsn' : ReasonOk ks' := fun i hi => by
    rw [hp.trl_end] at hi; dsimp only; rw [hp.trl, hp.rsn]
    rcases hinv.reasons i hi with hff | ⟨hr_lt, hmem, hall⟩
    · exact Or.inl hff
    · exact Or.inr ⟨by omega, by rw [(hp.old_clauses _ hr_lt).2.2.2]; exact hmem,
        fun x hx hne => by
          rw [(hp.old_clauses _ hr_lt).2.2.2] at hx; exact hall x hx hne⟩
  have hsync' : KittenTrailSynced ks' := fun i hi => by
    rw [hp.trl_end] at hi; rw [hp.trl, hp.vals]; exact hsync i hi
  refine ⟨⟨hsh', hcl', hw', hba', hrsn'⟩, hsync', horig, fun ci hci => ?_⟩
  have hc_lt : ci < ks.nc.toNat := Nat.lt_of_lt_of_le hci hinv.clauses.orig_nc_le
  have ho := hp.old_clauses ci hc_lt
  have hci_896 : ci < 896 := by have := hinv.clauses.nc_le; unfold kMaxCl at this; omega
  have hca_eq : ks'.clAux[ci]? = ks.clAux[ci]? := by
    have h1 := ho.2.2.1; unfold kittenClauseAux at h1
    rw [List.getElem?_eq_getElem (by rw [hsh'.clAux_len]; exact hci_896),
      List.getElem?_eq_getElem (by rw [hinv.shapes.clAux_len]; exact hci_896)] at h1 ⊢
    exact congrArg some (BitVec.eq_of_toNat_eq (by simpa using h1))
  exact ⟨hca_eq, congrArg (· &&& kmCore) ho.2.1⟩

private theorem kana_lrn_meta_bits (nkl : BitVec 32) (h : nkl.toNat < 2 ^ 16) :
    ((nkl ||| kmLrn) &&& 0xFFFF#32) = nkl ∧
    ((nkl ||| kmLrn) &&& kmLrn) ≠ 0#32 ∧
    ((nkl ||| kmLrn) &&& kmCore) = 0#32 := by
  refine ⟨?_, ?_, ?_⟩
  · apply BitVec.eq_of_getElem_eq; intro i hi
    simp only [BitVec.getElem_and, BitVec.getElem_or]
    by_cases h16 : i < 16
    · have hm : (0xFFFF#32 : BitVec 32)[i] = true := by revert i hi h16; decide
      have hl : (kmLrn : BitVec 32)[i] = false := by unfold kmLrn; revert i hi h16; decide
      simp [hm, hl]
    · have hm : (0xFFFF#32 : BitVec 32)[i] = false := by revert i hi h16; decide
      have hn : nkl[i] = false := by
        rw [BitVec.getElem_eq_testBit_toNat]
        have hpow : 2 ^ 16 ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
        exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h hpow)
      simp [hm, hn]
  · intro hz; have h17 := congrArg (fun b : BitVec 32 => b[17]) hz
    unfold kmLrn at h17; revert h17; simp
  · apply BitVec.eq_of_getElem_eq; intro i hi
    simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_zero]
    by_cases h16 : i = 16
    · subst h16
      have hn : nkl[16] = false := by
        rw [BitVec.getElem_eq_testBit_toNat]; exact Nat.testBit_lt_two_pow h
      have hl : (0x20000#32 : BitVec 32)[16] = false := by
        simp [BitVec.getElem_eq_testBit_toNat]; decide
      unfold kmLrn; simp [hn, hl]
    · have hc : (kmCore : BitVec 32)[i] = false := by unfold kmCore; revert i hi h16; decide
      simp [hc]

private theorem kana_append_lrn_inv {acap : Nat} {ks : KittenState}
    {nr : BitVec 32} {ar' : List (BitVec 32)}
    (hinv : ks.Inv acap) (hsync : KittenTrailSynced ks)
    (hnc_lt : ks.nc.toNat < kMaxCl)
    (hnkl_ge2 : 2 ≤ ks.nkl.toNat) (hnkl_le : ks.nkl.toNat ≤ ks.nv.toNat)
    (hnr_eq : nr = if ks.ante ≠ 0#32 then ks.nres else 0#32)
    (hnr_le : nr.toNat ≤ kMaxL)
    (hfit : ks.alen.toNat + ks.nkl.toNat + nr.toNat ≤ acap)
    (har_len : ar'.length = acap)
    (har_old : ∀ i < ks.alen.toNat, ar'[i]? = ks.arena[i]?)
    (har_lits : ∀ i < ks.nkl.toNat, ar'[ks.alen.toNat + i]? = ks.kl[i]?)
    (har_ants : ∀ i < nr.toNat, ar'[ks.alen.toNat + ks.nkl.toNat + i]? = ks.res[i]?)
    (hkl_lt : ∀ i < ks.nkl.toNat, (ks.kl[i]?.getD 0#32).toNat < 2 * ks.nv.toNat)
    (hF0_ent : (cnfOfClauses (kittenOrigClauses ks)).EntailsClause
      (cnfClause ((ks.kl.take ks.nkl.toNat).map BitVec.toNat)))
    (hres_ent : ks.ante ≠ 0#32 →
      (∀ i < ks.nres.toNat, (ks.res[i]?.getD 0xFFFFFFFF#32).toNat < ks.nc.toNat) ∧
      (cnfOfClauses ((ks.res.take ks.nres.toNat).map fun c =>
        kittenClauseLits ks c.toNat)).EntailsClause
          (cnfClause ((ks.kl.take ks.nkl.toNat).map BitVec.toNat))) :
    let nc := ks.nc; let off := ks.alen; let nkl := ks.nkl
    let stMeta : KittenState :=
      { ks with arena := ar', alen := off + nkl + nr,
                clOff := ks.clOff.set nc.toNat off,
                clMeta := ks.clMeta.set nc.toNat (nkl ||| kmLrn),
                clAux := ks.clAux.set nc.toNat nr, nc := nc + 1#32 }
    let stW := kittenWatchStep stMeta nc (ks.kl[0]?.getD 0#32) (ks.kl[1]?.getD 0#32)
    stMeta.ShapesOk acap ∧ stW.Inv acap ∧ KittenTrailSynced stW ∧
    stW.nc = ks.nc + 1#32 ∧ stW.nv = ks.nv ∧ stW.orig_nc = ks.orig_nc ∧ stW.lvl = ks.lvl ∧
    stW.trl_end = ks.trl_end ∧ stW.ante = ks.ante ∧ stW.nassump = ks.nassump ∧
    stW.assump = ks.assump ∧ stW.incons = ks.incons ∧ stW.failing = ks.failing ∧
    stW.trl = ks.trl ∧ stW.lvlArr = ks.lvlArr ∧ stW.rsn = ks.rsn ∧ stW.vals = ks.vals ∧
    kittenOrigClauses stW = kittenOrigClauses ks ∧
    kittenClauseLits stW nc.toNat = (ks.kl.take nkl.toNat).map BitVec.toNat ∧
    (∀ ci < ks.orig_nc.toNat, stW.clAux[ci]? = ks.clAux[ci]? ∧
      (stW.clMeta[ci]?.getD 0#32 &&& kmCore) = (ks.clMeta[ci]?.getD 0#32 &&& kmCore)) := by
  intro nc off nkl stMeta stW
  have hnv := hinv.clauses.nv_le
  have hnc1 : (ks.nc + 1#32).toNat = ks.nc.toNat + 1 := by unfold kMaxCl at hnc_lt; bv_omega
  have hoff_add : (ks.alen + ks.nkl + nr).toNat = ks.alen.toNat + ks.nkl.toNat + nr.toNat := by
    have := hinv.clauses.acap_lt; unfold dimacsBound at this; bv_omega
  have hshM : stMeta.ShapesOk acap :=
    ⟨hinv.shapes.hdrTail_len, hinv.shapes.lvlArr_len, hinv.shapes.rsn_len, hinv.shapes.qprev_len,
     hinv.shapes.qnext_len, hinv.shapes.qstampArr_len, hinv.shapes.trl_len, hinv.shapes.flags_len,
     hinv.shapes.vals_len, hinv.shapes.assump_len, hinv.shapes.ana_len, hinv.shapes.kl_len,
     hinv.shapes.units_len, hinv.shapes.res_len, hinv.shapes.whead_len, hinv.shapes.wnext_len,
     hinv.shapes.wblit_len, by simp [stMeta, hinv.shapes.clOff_len],
     by simp [stMeta, hinv.shapes.clMeta_len], by simp [stMeta, hinv.shapes.clAux_len], har_len⟩
  have hshW : stW.ShapesOk acap := kittenWatchStep_preserves_shapes hshM _ _ _
  have hco_len : ks.nc.toNat < ks.clOff.length := by rw [hinv.shapes.clOff_len]; exact hnc_lt
  have hcm_len : ks.nc.toNat < ks.clMeta.length := by rw [hinv.shapes.clMeta_len]; exact hnc_lt
  have hca_len : ks.nc.toNat < ks.clAux.length := by rw [hinv.shapes.clAux_len]; exact hnc_lt
  have hslice : ∀ {a b : Nat} {ys : List (BitVec 32)},
      a + b ≤ acap → b ≤ ys.length → (∀ j < b, ar'[a + j]? = ys[j]?) →
      ((ar'.drop a).take b).map BitVec.toNat = (ys.take b).map BitVec.toNat := by
    intro a b ys hab hb hget; congr 1
    apply List.ext_getElem
    · simp [List.length_take, har_len]; omega
    · intro j hj1 _; have hj : j < b := by simp at hj1; omega
      simp only [List.getElem_take, List.getElem_drop]
      have h1 := hget j hj
      rw [List.getElem?_eq_getElem (by omega : a + j < ar'.length),
        List.getElem?_eq_getElem (by omega : j < ys.length)] at h1
      exact Option.some.inj h1
  have hcl_old : ∀ c < ks.nc.toNat,
      kittenClauseOff stMeta c = kittenClauseOff ks c ∧
      kittenClauseMeta stMeta c = kittenClauseMeta ks c ∧
      kittenClauseSize stMeta c = kittenClauseSize ks c ∧
      kittenClauseIsLrn stMeta c = kittenClauseIsLrn ks c ∧
      kittenClauseAux stMeta c = kittenClauseAux ks c ∧
      kittenClauseSpan stMeta c = kittenClauseSpan ks c ∧
      kittenClauseLits stMeta c = kittenClauseLits ks c ∧
      kittenClauseAnts stMeta c = kittenClauseAnts ks c := by
    intro c hc
    have hne : ks.nc.toNat ≠ c := by omega
    have hco : stMeta.clOff[c]? = ks.clOff[c]? := List.getElem?_set_ne hne
    have hcm : stMeta.clMeta[c]? = ks.clMeta[c]? := List.getElem?_set_ne hne
    have hca : stMeta.clAux[c]? = ks.clAux[c]? := List.getElem?_set_ne hne
    have hwf := hinv.clauses.cl_wf c hc
    have hsp := hwf.2.2.1; unfold kittenClauseSpan at hsp
    have hal := hinv.clauses.alen_le
    have hlits_eq : kittenClauseLits stMeta c = kittenClauseLits ks c := by
      simp only [kittenClauseLits, kittenClauseOff, kittenClauseSize, kittenClauseMeta, hco, hcm]
      change ((ar'.drop (kittenClauseOff ks c)).take (kittenClauseSize ks c)).map BitVec.toNat = _
      congr 1; apply List.ext_getElem
      · simp [List.length_take, List.length_drop, har_len, hinv.shapes.arena_len]; rfl
      · intro j hj1 _; have hj : j < kittenClauseSize ks c := by simp at hj1; omega
        simp only [List.getElem_take, List.getElem_drop]
        have ha := har_old (kittenClauseOff ks c + j) (by omega)
        rw [List.getElem?_eq_getElem (by omega : kittenClauseOff ks c + j < ar'.length),
          List.getElem?_eq_getElem (by rw [hinv.shapes.arena_len]; omega)] at ha
        exact Option.some.inj ha
    have hants_eq : kittenClauseAnts stMeta c = kittenClauseAnts ks c := by
      unfold kittenClauseAnts
      have hlrn_eq : kittenClauseIsLrn stMeta c = kittenClauseIsLrn ks c := by
        simp [kittenClauseIsLrn, kittenClauseMeta, hcm]
      rw [hlrn_eq]
      by_cases hlrn : kittenClauseIsLrn ks c = true
      · rw [kana_ite_t hlrn, kana_ite_t hlrn]
        have hsp' : kittenClauseOff ks c + kittenClauseSize ks c + kittenClauseAux ks c ≤
            ks.alen.toNat := by
          have h1 := hwf.2.2.1; unfold kittenClauseSpan at h1
          rw [hlrn] at h1; simp only [ite_true] at h1; omega
        simp only [kittenClauseOff, kittenClauseSize, kittenClauseAux, kittenClauseMeta,
          hco, hcm, hca]
        change ((ar'.drop (kittenClauseOff ks c + kittenClauseSize ks c)).take
          (kittenClauseAux ks c)).map BitVec.toNat = _
        congr 1; apply List.ext_getElem
        · simp [List.length_take, List.length_drop, har_len, hinv.shapes.arena_len]; rfl
        · intro j hj1 _; have hj : j < kittenClauseAux ks c := by simp at hj1; omega
          simp only [List.getElem_take, List.getElem_drop]
          have ha := har_old (kittenClauseOff ks c + kittenClauseSize ks c + j) (by omega)
          have h1 : kittenClauseOff ks c + kittenClauseSize ks c + j < ar'.length := by omega
          have h2 : kittenClauseOff ks c + kittenClauseSize ks c + j < ks.arena.length := by
            rw [hinv.shapes.arena_len]; omega
          rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] at ha
          exact Option.some.inj ha
      · rw [kana_ite_f hlrn, kana_ite_f hlrn]
    exact ⟨by simp [kittenClauseOff, hco], by simp [kittenClauseMeta, hcm],
      by simp [kittenClauseSize, kittenClauseMeta, hcm],
      by simp [kittenClauseIsLrn, kittenClauseMeta, hcm], by simp [kittenClauseAux, hca],
      by simp [kittenClauseSpan, kittenClauseSize, kittenClauseIsLrn, kittenClauseAux,
        kittenClauseMeta, hcm, hca], hlits_eq, hants_eq⟩
  obtain ⟨hmb_sz, hmb_lrn, hmb_core⟩ := kana_lrn_meta_bits ks.nkl (by unfold kMaxV at hnv; omega)
  have hcl_new : kittenClauseOff stMeta ks.nc.toNat = ks.alen.toNat ∧
      kittenClauseMeta stMeta ks.nc.toNat = (ks.nkl ||| kmLrn) ∧
      kittenClauseSize stMeta ks.nc.toNat = ks.nkl.toNat ∧
      kittenClauseIsLrn stMeta ks.nc.toNat = true ∧
      kittenClauseAux stMeta ks.nc.toNat = nr.toNat ∧
      kittenClauseSpan stMeta ks.nc.toNat = ks.nkl.toNat + nr.toNat ∧
      kittenClauseLits stMeta ks.nc.toNat = (ks.kl.take ks.nkl.toNat).map BitVec.toNat ∧
      kittenClauseAnts stMeta ks.nc.toNat = (ks.res.take nr.toNat).map BitVec.toNat := by
    have hco : stMeta.clOff[ks.nc.toNat]? = some ks.alen := List.getElem?_set_self hco_len
    have hcm : stMeta.clMeta[ks.nc.toNat]? = some (ks.nkl ||| kmLrn) :=
      List.getElem?_set_self hcm_len
    have hca : stMeta.clAux[ks.nc.toNat]? = some nr := List.getElem?_set_self hca_len
    have hlrn_b : ((ks.nkl ||| kmLrn) &&& kmLrn != 0#32) = true := bne_iff_ne.mpr hmb_lrn
    refine ⟨by simp [kittenClauseOff, hco], by simp [kittenClauseMeta, hcm],
      by simp [kittenClauseSize, kittenClauseMeta, hcm, hmb_sz],
      by simp [kittenClauseIsLrn, kittenClauseMeta, hcm, hlrn_b],
      by simp [kittenClauseAux, hca],
      by simp [kittenClauseSpan, kittenClauseSize, kittenClauseIsLrn, kittenClauseAux,
        kittenClauseMeta, hcm, hca, hmb_sz, hlrn_b],
      by simp only [kittenClauseLits, kittenClauseOff, kittenClauseSize, kittenClauseMeta,
          hco, hcm, Option.getD_some, hmb_sz]
         exact hslice (by omega) (by rw [hinv.shapes.kl_len]; unfold kMaxV at hnv; omega) har_lits,
      by simp only [kittenClauseAnts, kittenClauseIsLrn, kittenClauseOff, kittenClauseSize,
          kittenClauseAux, kittenClauseMeta, hco, hcm, hca, Option.getD_some, hmb_sz, hlrn_b,
          ite_true]
         exact hslice (by omega) (by rw [hinv.shapes.res_len]; unfold kMaxL at hnr_le; omega)
           har_ants⟩
  have horigM : kittenOrigClauses stMeta = kittenOrigClauses ks :=
    kittenOrigClauses_eq_of rfl fun c hc =>
      (hcl_old c (Nat.lt_of_lt_of_le hc hinv.clauses.orig_nc_le)).2.2.2.2.2.2.1
  have hclM : KittenClausesOk acap stMeta := by
    refine ⟨hinv.clauses.acap_ge, hinv.clauses.acap_lt, hinv.clauses.acap_eq,
      hinv.clauses.nv_le, by change (ks.nc + 1#32).toNat ≤ kMaxCl; omega,
      by change ks.orig_nc.toNat ≤ (ks.nc + 1#32).toNat; have := hinv.clauses.orig_nc_le; omega,
      hinv.clauses.orig_nc_max, by change (ks.alen + ks.nkl + nr).toNat ≤ acap; omega,
      hinv.clauses.nassump_le, hinv.clauses.nunits_le, hinv.clauses.nres_le, hinv.clauses.nkl_le,
      hinv.clauses.nana_le, ?_, ?_, ?_, ?_, ?_, hinv.clauses.assump_ok, hinv.clauses.flags_clean⟩
    · intro c hc; change c < (ks.nc + 1#32).toNat at hc; rw [hnc1] at hc
      by_cases hcn : c = ks.nc.toNat
      · subst hcn
        have hon_le : ks.orig_nc.toNat ≤ ks.nc.toNat := hinv.clauses.orig_nc_le
        refine ⟨by rw [hcl_new.2.2.2.1, decide_eq_true hon_le],
          fun _ => by rw [hcl_new.2.2.1]; omega,
          by rw [hcl_new.1, hcl_new.2.2.2.2.2.1]
             change ks.alen.toNat + (ks.nkl.toNat + nr.toNat) ≤ (ks.alen + ks.nkl + nr).toNat
             omega,
          fun l hl => ?_, by rw [hcl_new.2.2.2.2.2.2.1, horigM]; exact hF0_ent,
          fun ha _ => ?_⟩
        · rw [hcl_new.2.2.2.2.2.2.1, List.mem_map] at hl; obtain ⟨b, hb, rfl⟩ := hl
          rw [List.mem_take_iff_getElem] at hb; obtain ⟨i, hi, rfl⟩ := hb
          have h1 := hkl_lt i (by omega)
          rwa [List.getElem?_eq_getElem (by omega : i < ks.kl.length), Option.getD_some] at h1
        · have hnr_res : nr = ks.nres := by rw [hnr_eq, kana_ite_t ha]
          obtain ⟨hlt_r, hent_r⟩ := hres_ent ha
          have hants_lt : ∀ a ∈ kittenClauseAnts stMeta ks.nc.toNat, a < ks.nc.toNat := by
            intro a ha'; rw [hcl_new.2.2.2.2.2.2.2, hnr_res, List.mem_map] at ha'
            obtain ⟨b, hb, rfl⟩ := ha'; rw [List.mem_take_iff_getElem] at hb
            obtain ⟨i, hi, rfl⟩ := hb
            have h1 := hlt_r i (by omega)
            rwa [List.getElem?_eq_getElem (by omega : i < ks.res.length), Option.getD_some] at h1
          refine ⟨hants_lt, ?_⟩
          rw [hcl_new.2.2.2.2.2.2.1, hcl_new.2.2.2.2.2.2.2, hnr_res, List.map_map]
          have hmp : (ks.res.take ks.nres.toNat).map (kittenClauseLits stMeta ∘ BitVec.toNat) =
              (ks.res.take ks.nres.toNat).map fun c => kittenClauseLits ks c.toNat := by
            refine List.map_congr_left fun b hb => ?_
            have hb_lt : b.toNat < ks.nc.toNat := hants_lt b.toNat (by
              rw [hcl_new.2.2.2.2.2.2.2, hnr_res]; exact List.mem_map.mpr ⟨b, hb, rfl⟩)
            exact (hcl_old b.toNat hb_lt).2.2.2.2.2.2.1
          rw [hmp]; exact hent_r
      · have hc' : c < ks.nc.toNat := by omega
        have hw := hinv.clauses.cl_wf c hc'; have ho := hcl_old c hc'
        refine ⟨by rw [ho.2.2.2.1]; exact hw.1, fun hge => by rw [ho.2.2.1]; exact hw.2.1 hge,
          by rw [ho.1, ho.2.2.2.2.2.1]
             change _ ≤ (ks.alen + ks.nkl + nr).toNat; have := hw.2.2.1; omega,
          fun l hl => by rw [ho.2.2.2.2.2.2.1] at hl; exact hw.2.2.2.1 l hl,
          by rw [ho.2.2.2.2.2.2.1, horigM]; exact hw.2.2.2.2.1,
          fun ha hge => ?_⟩
        obtain ⟨ha_lt, ha_ent⟩ := hw.2.2.2.2.2 ha hge
        rw [ho.2.2.2.2.2.2.2, ho.2.2.2.2.2.2.1]
        refine ⟨ha_lt, ?_⟩
        have hmp := List.map_congr_left fun a ha' =>
          (hcl_old a (Nat.lt_trans (ha_lt a ha') hc')).2.2.2.2.2.2.1
        rw [hmp]; exact ha_ent
    · intro c1 c2 h12 hc2; change c2 < (ks.nc + 1#32).toNat at hc2; rw [hnc1] at hc2
      have ho1 := hcl_old c1 (by omega)
      by_cases hc2n : c2 = ks.nc.toNat
      · subst hc2n; rw [ho1.1, ho1.2.2.2.2.2.1, hcl_new.1]
        exact (hinv.clauses.cl_wf c1 (by omega)).2.2.1
      · have ho2 := hcl_old c2 (by omega)
        rw [ho1.1, ho1.2.2.2.2.2.1, ho2.1]; exact hinv.clauses.cl_mono c1 c2 h12 (by omega)
    · intro ui hui
      have hu := hinv.clauses.units_ok ui hui
      dsimp only; rw [(hcl_old _ hu.1).2.2.1]
      exact ⟨by change (ks.units[ui]?.getD 0#32).toNat < (ks.nc + 1#32).toNat; omega, hu.2⟩
    · intro hi
      have hinc := hinv.clauses.incons_ok hi
      refine ⟨by change ks.incons.toNat < (ks.nc + 1#32).toNat; omega,
        by rw [horigM]; exact hinc.2.1, fun l hl => ?_⟩
      rw [(hcl_old _ hinc.1).2.2.2.2.2.2.1] at hl
      have hr := hinc.2.2 l hl
      refine ⟨hr.1, hr.2.1, fun ha => ?_⟩
      have hrr := hr.2.2 ha
      dsimp only; rw [(hcl_old _ hrr.1).2.2.2.2.2.2.1]
      exact ⟨by change (ks.rsn[l / 2]?.getD 0xFFFFFFFF#32).toNat < (ks.nc + 1#32).toNat; omega,
        hrr.2⟩
    · intro ha
      exact failingOk_append_nonCore (ks := ks) (ks' := stMeta)
        (by change (ks.nc + 1#32).toNat = ks.nc.toNat + 1; exact hnc1)
        rfl rfl rfl (by rw [hcl_new.2.1]; exact hmb_core)
        (fun c hc => ⟨(hcl_old c hc).2.1, (hcl_old c hc).2.2.2.2.2.2.1⟩)
        (hinv.clauses.failing_ok ha)
  have hwM : KittenWatchesOk stMeta := by
    obtain ⟨ch, h1, h2, h3, h4⟩ := hinv.watches
    refine ⟨ch, h1, h2, h3, fun l hl w hw => ?_⟩
    have hb := h4 l hl w hw
    have hw_div : w / 2 < ks.nc.toNat := Nat.div_lt_of_lt_mul hb.1
    have ho := hcl_old (w / 2) hw_div
    have hwf := hinv.clauses.cl_wf (w / 2) hw_div
    have hlt_a : kittenClauseOff ks (w / 2) + w % 2 < ks.alen.toNat := by
      have := hwf.2.2.1; unfold kittenClauseSpan at this; omega
    refine ⟨by change w < 2 * (ks.nc + 1#32).toNat; omega, by rw [ho.2.2.1]; exact hb.2.1, ?_,
      hb.2.2.2⟩
    change (ar'[kittenClauseOff stMeta (w / 2) + w % 2]?.getD 0#32).toNat = l
    rw [ho.1, har_old _ hlt_a]; exact hb.2.2.1
  have hwW : KittenWatchesOk stW := by
    have hwn_lt : stMeta.wnext.length < 2 ^ 32 := by rw [hshM.wnext_len]; decide
    refine kittenWatchStep_preserves_watches hshM hwM
      (by change ks.nc.toNat < (ks.nc + 1#32).toNat; omega) hclM.nc_le hclM.nv_le
      (hkl_lt 0 (by omega)) (hkl_lt 1 (by omega)) (by rw [hcl_new.2.2.1]; exact hnkl_ge2)
      (by rw [hcl_new.1]; change (ar'[ks.alen.toNat]?.getD 0#32).toNat = _
          have := har_lits 0 (by omega); simp at this; rw [this])
      (by rw [hcl_new.1]; change (ar'[ks.alen.toNat + 1]?.getD 0#32).toNat = _
          rw [har_lits 1 (by omega)]) ?_
    intro ch hchl _ hwc
    change ch.length = 2 * ks.nv.toNat at hchl
    obtain ⟨ch0, hch0_len, _, hwc0, hbnd0⟩ := hinv.watches
    have hlt_all : ∀ w ∈ ch.flatten, w < 2 * ks.nc.toNat := by
      intro w hw; rw [List.mem_flatten] at hw; obtain ⟨c, hc, hwc'⟩ := hw
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
      have hk0 : k < ch0.length := by omega
      have hc1 := hwc k (by change k < 2 * ks.nv.toNat; omega)
      rw [List.getElem?_eq_getElem hk, Option.getD_some] at hc1
      have hc0 := hwc0 k (by omega); rw [List.getElem?_eq_getElem hk0, Option.getD_some] at hc0
      rw [WChain.unique hwn_lt hc1 hc0] at hwc'
      exact (hbnd0 k (by omega) w (by simpa [List.getElem?_eq_getElem hk0] using hwc')).1
    change 2 * ks.nc.toNat ∉ ch.flatten ∧ 2 * ks.nc.toNat + 1 ∉ ch.flatten
    exact ⟨fun h => absurd (hlt_all _ h) (by omega), fun h => absurd (hlt_all _ h) (by omega)⟩
  have hclW : KittenClausesOk acap stW :=
    kana_clauses_of_eq hclM hclM.nres_le hclM.nkl_le hclM.nana_le hclM.flags_clean
  have w_tr : stW.trl = ks.trl := rfl
  have w_rs : stW.rsn = ks.rsn := rfl
  have hbaW : KittenBaseAssignOk stW :=
    ⟨hinv.assign.trl_end_le, hinv.assign.prop_le, hinv.assign.unass_eq, hinv.assign.vals_dom,
     hinv.assign.vals_neg_iff, hinv.assign.vals_nz_iff_trl, hinv.assign.trl_nodup,
     hinv.assign.trl_lt, hinv.assign.trl_lvl_le, hinv.assign.unass_lvl_zero,
     hinv.assign.trl_lvl_mono, hinv.assign.dec_earliest,
     fun i hi hl0 => by
       have h0 := hinv.assign.lvl0_ok i hi hl0
       refine ⟨h0.1, h0.2.1, h0.2.2.1,
         (by change (cnfOfClauses (kittenOrigClauses stMeta)).EntailsClause _
             rw [horigM]; exact h0.2.2.2.1),
         fun ha => ?_⟩
       have h1 := h0.2.2.2.2 ha
       dsimp only; rw [w_tr, w_rs]
       exact ⟨by change (ks.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat <
           (ks.nc + 1#32).toNat; omega,
         by change kittenClauseLits stMeta _ = _; rw [(hcl_old _ h1.1).2.2.2.2.2.2.1]; exact h1.2⟩⟩
  have hrsnW : ReasonOk stW := fun i hi => by
    dsimp only; rw [w_tr, w_rs]
    rcases hinv.reasons i hi with hff | ⟨hr_lt, hmem, hall⟩
    · exact Or.inl hff
    · exact Or.inr ⟨by change (ks.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat <
          (ks.nc + 1#32).toNat; omega,
        by change _ ∈ kittenClauseLits stMeta _; rw [(hcl_old _ hr_lt).2.2.2.2.2.2.1]; exact hmem,
        fun x hx hne => by
          change x ∈ kittenClauseLits stMeta _ at hx
          rw [(hcl_old _ hr_lt).2.2.2.2.2.2.1] at hx; exact hall x hx hne⟩
  refine ⟨hshM, ⟨hshW, hclW, hwW, hbaW, hrsnW⟩, hsync, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, horigM, hcl_new.2.2.2.2.2.2.1, fun ci hci => ?_⟩
  have hne : ks.nc.toNat ≠ ci := by have := hinv.clauses.orig_nc_le; omega
  exact ⟨List.getElem?_set_ne hne,
    by change ((ks.clMeta.set ks.nc.toNat _)[ci]?.getD 0#32 &&& kmCore) = _
       rw [List.getElem?_set_ne hne]⟩

private theorem kana_fl_bit0_clean (x : BitVec 32) (h : (x &&& 2#32) = 0#32) :
    ((x ||| 1#32) &&& 2#32) = 0#32 ∧ ((x &&& ~~~1#32) &&& 2#32) = 0#32 := by
  have h1 : x[1] = false := by
    have := congrArg (fun b : BitVec 32 => b[1]) h; simpa using this
  constructor
  · apply BitVec.eq_of_getElem_eq; intro i hi
    simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_zero]
    by_cases hi1 : i = 1
    · subst hi1; simp [h1]
    · have h2 : (2#32 : BitVec 32)[i] = false := by revert i hi hi1; decide
      simp [h2]
  · apply BitVec.eq_of_getElem_eq; intro i hi
    simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]
    by_cases hi1 : i = 1
    · subst hi1; simp [h1]
    · have h2 : (2#32 : BitVec 32)[i] = false := by revert i hi hi1; decide
      simp [h2]

private theorem kana_assignStep_preserves_inv {acap : Nat} {ks : KittenState} {lit rsn : BitVec 32}
    (hinv : ks.Inv acap) (hsync : KittenTrailSynced ks)
    (hlit : lit.toNat < 2 * ks.nv.toNat) (hte_lt : ks.trl_end.toNat < ks.nv.toNat)
    (hunass : ¬ ∃ i < ks.trl_end.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 = lit.toNat / 2)
    (hrsn_ne : rsn ≠ 0xFFFFFFFF#32) (hrsn_lt : rsn.toNat < ks.nc.toNat)
    (hlit_mem : lit.toNat ∈ kittenClauseLits ks rsn.toNat)
    (hothers : ∀ x ∈ kittenClauseLits ks rsn.toNat, x ≠ lit.toNat →
      ∃ j < ks.trl_end.toNat, (ks.trl[j]?.getD 0#32).toNat = x ^^^ 1)
    (hlvl0_req : ks.lvl = 0#32 →
      (cnfOfClauses (kittenOrigClauses ks)).EntailsClause (cnfClause [lit.toNat]) ∧
      (ks.ante ≠ 0#32 → kittenClauseLits ks rsn.toNat = [lit.toNat])) :
    let ks' := kittenAssignStep ks lit rsn
    ks'.Inv acap ∧ KittenTrailSynced ks' ∧
    ks'.nv = ks.nv ∧ ks'.orig_nc = ks.orig_nc ∧ ks'.lvl = ks.lvl ∧ ks'.ante = ks.ante ∧
    ks'.nassump = ks.nassump ∧ ks'.assump = ks.assump ∧ ks'.incons = ks.incons ∧
    ks'.failing = ks.failing ∧ kittenOrigClauses ks' = kittenOrigClauses ks ∧
    (∀ ci < ks.orig_nc.toNat, ks'.clAux[ci]? = ks.clAux[ci]? ∧
      (ks'.clMeta[ci]?.getD 0#32 &&& kmCore) = (ks.clMeta[ci]?.getD 0#32 &&& kmCore)) ∧
    (0 < ks'.lvl.toNat → ∃ i < ks'.trl_end.toNat,
      ks'.lvlArr[(ks'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 = ks'.lvl) ∧
    kittenTrailDecisions ks' = kittenTrailDecisions ks ∧
    (∀ i < ks.trl_end.toNat, i < ks'.trl_end.toNat ∧ ks'.trl[i]? = ks.trl[i]? ∧
      ks'.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]? =
        ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?) := by
  intro ks'
  have hnv := hinv.clauses.nv_le
  obtain ⟨hv_eq, hv_lt⟩ := bv32_lit_div2_bv hlit
  obtain ⟨hnl_eq', hnl_lt⟩ := bv32_xor1_eq_litNeg hlit
  have hnl_eq : (lit ^^^ 1#32).toNat = litNeg lit.toNat := hnl_eq'
  have hte1 : (ks.trl_end + 1#32).toNat = ks.trl_end.toNat + 1 := by unfold kMaxV at hnv; bv_omega
  have hun_pos : 0 < ks.unass.toNat := by have := hinv.assign.unass_eq; omega
  have hun_sub : (ks.unass - 1#32).toNat = ks.unass.toNat - 1 := by bv_omega
  have hun' : ks'.unass = ks.unass - 1#32 := by
    dsimp only [ks', kittenAssignStep]; rw [kana_ite_t hun_pos]
  have hsh' : ks'.ShapesOk acap := kittenAssignStep_preserves_shapes hinv.shapes lit rsn
  have hv_len : (lit >>> 1).toNat < ks.lvlArr.length := by
    rw [hinv.shapes.lvlArr_len]; unfold kMaxV at hnv; omega
  have hr_len : (lit >>> 1).toNat < ks.rsn.length := by
    rw [hinv.shapes.rsn_len]; unfold kMaxV at hnv; omega
  have hfl_len : (lit >>> 1).toNat < ks.flags.length := by
    rw [hinv.shapes.flags_len]; unfold kMaxV at hnv; omega
  have hl_len : lit.toNat < ks.vals.length := by
    rw [hinv.shapes.vals_len]; unfold kMaxV at hnv; omega
  have hnl_len : (lit ^^^ 1#32).toNat < ks.vals.length := by
    rw [hinv.shapes.vals_len, hnl_eq]; unfold kMaxV at hnv; omega
  have hte_len : ks.trl_end.toNat < ks.trl.length := by
    rw [hinv.shapes.trl_len]; unfold kMaxV at hnv; omega
  have hl_ne_nl : lit.toNat ≠ (lit ^^^ 1#32).toNat := by
    rw [hnl_eq, ← litNeg_eq_xor1]
    rcases nat_xor1_cases lit.toNat with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega
  have hval_ne_v : ∀ l, l / 2 ≠ lit.toNat / 2 → ks'.vals[l]? = ks.vals[l]? := fun l hne => by
    have h1 : (lit ^^^ 1#32).toNat ≠ l := fun he =>
      hne (by rw [← he, hnl_eq, kana_litNeg_div2])
    have h2 : lit.toNat ≠ l := fun he => hne (by rw [he])
    change ((ks.vals.set lit.toNat 1#32).set (lit ^^^ 1#32).toNat 2#32)[l]? = _
    rw [List.getElem?_set_ne h1, List.getElem?_set_ne h2]
  have hval_l : ks'.vals[lit.toNat]? = some 1#32 := by
    change ((ks.vals.set lit.toNat 1#32).set (lit ^^^ 1#32).toNat 2#32)[lit.toNat]? = _
    rw [List.getElem?_set_ne hl_ne_nl.symm, List.getElem?_set_self hl_len]
  have hval_nl : ks'.vals[lit.toNat ^^^ 1]? = some 2#32 := by
    change ((ks.vals.set lit.toNat 1#32).set (lit ^^^ 1#32).toNat 2#32)[lit.toNat ^^^ 1]? = _
    rw [show lit.toNat ^^^ 1 = (lit ^^^ 1#32).toNat by rw [hnl_eq, litNeg_eq_xor1]]
    exact List.getElem?_set_self (by rw [List.length_set]; exact hnl_len)
  have htr_self : ks'.trl[ks.trl_end.toNat]? = some lit := List.getElem?_set_self hte_len
  have htr_old : ∀ k < ks.trl_end.toNat, ks'.trl[k]? = ks.trl[k]? := fun k hk =>
    List.getElem?_set_ne (by omega)
  have hlv_self : ks'.lvlArr[lit.toNat / 2]? = some ks.lvl := by
    change (ks.lvlArr.set (lit >>> 1).toNat ks.lvl)[lit.toNat / 2]? = _
    rw [← hv_eq]; exact List.getElem?_set_self hv_len
  have hlv_ne : ∀ v, v ≠ lit.toNat / 2 → ks'.lvlArr[v]? = ks.lvlArr[v]? := fun v hne =>
    List.getElem?_set_ne (by rw [hv_eq]; exact Ne.symm hne)
  have hrs_self : ks'.rsn[lit.toNat / 2]? = some rsn := by
    change (ks.rsn.set (lit >>> 1).toNat rsn)[lit.toNat / 2]? = _
    rw [← hv_eq]; exact List.getElem?_set_self hr_len
  have hrs_ne : ∀ v, v ≠ lit.toNat / 2 → ks'.rsn[v]? = ks.rsn[v]? := fun v hne =>
    List.getElem?_set_ne (by rw [hv_eq]; exact Ne.symm hne)
  have hfl_clean : ∀ v < ks'.nv.toNat, (ks'.flags[v]?.getD 0#32 &&& 2#32) = 0#32 := by
    intro v hv; dsimp only [ks', kittenAssignStep]
    by_cases hvv : v = (lit >>> 1).toNat
    · subst hvv; rw [List.getElem?_set_self hfl_len, Option.getD_some]
      have hc := kana_fl_bit0_clean _ (hinv.clauses.flags_clean _ hv)
      by_cases hb : (lit &&& 1#32) ≠ 0#32
      · rw [kana_ite_t hb]; exact hc.1
      · rw [kana_ite_f hb]; exact hc.2
    · rw [List.getElem?_set_ne (Ne.symm hvv)]; exact hinv.clauses.flags_clean v hv
  have hcl' : KittenClausesOk acap ks' := by
    refine ⟨hinv.clauses.acap_ge, hinv.clauses.acap_lt, hinv.clauses.acap_eq, hinv.clauses.nv_le,
      hinv.clauses.nc_le, hinv.clauses.orig_nc_le, hinv.clauses.orig_nc_max, hinv.clauses.alen_le,
      hinv.clauses.nassump_le, hinv.clauses.nunits_le, hinv.clauses.nres_le, hinv.clauses.nkl_le,
      hinv.clauses.nana_le, hinv.clauses.cl_wf, hinv.clauses.cl_mono, hinv.clauses.units_ok,
      ?_, hinv.clauses.failing_ok, hinv.clauses.assump_ok, hfl_clean⟩
    intro hi
    have hinc := hinv.clauses.incons_ok hi
    refine ⟨hinc.1, hinc.2.1, fun l hl => ?_⟩
    have hll := hinc.2.2 l hl
    have hl_lt := (hinv.clauses.cl_wf _ hinc.1).2.2.2.1 l hl
    have hne_v : l / 2 ≠ lit.toNat / 2 := by
      intro heq
      have hnz : ks.vals[l]?.getD 0#32 ≠ 0#32 := by simp [hll.1]
      obtain ⟨i, hi, hiv⟩ := (hinv.assign.vals_nz_iff_trl l hl_lt).mp hnz
      exact hunass ⟨i, hi, hiv.trans heq⟩
    rw [hval_ne_v l hne_v, hlv_ne _ hne_v]
    refine ⟨hll.1, hll.2.1, fun ha => ?_⟩
    dsimp only; rw [hrs_ne _ hne_v]; exact hll.2.2 ha
  have htrl_take : ks'.trl.take ks'.trl_end.toNat = ks.trl.take ks.trl_end.toNat ++ [lit] := by
    change (ks.trl.set ks.trl_end.toNat lit).take (ks.trl_end + 1#32).toNat = _
    rw [hte1, List.take_add_one, list_take_set_out _ _ (Nat.le_refl _),
      List.getElem?_set_self hte_len, Option.toList_some]
  have hsync' : KittenTrailSynced ks' := by
    intro i hi; change i < (ks.trl_end + 1#32).toNat at hi; rw [hte1] at hi
    dsimp only
    by_cases hie : i = ks.trl_end.toNat
    · subst hie; rw [htr_self, Option.getD_some]; exact ⟨hval_l, hval_nl⟩
    · have hi_old : i < ks.trl_end.toNat := by omega
      have hne_v : (ks.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := fun h =>
        hunass ⟨i, hi_old, h⟩
      have hne_nv : ((ks.trl[i]?.getD 0#32).toNat ^^^ 1) / 2 ≠ lit.toNat / 2 := by
        rw [kana_xor1_div2]; exact hne_v
      rw [htr_old i hi_old, hval_ne_v _ hne_v, hval_ne_v _ hne_nv]
      exact hsync i hi_old
  have hba' : KittenBaseAssignOk ks' := by
    refine ⟨by change (ks.trl_end + 1#32).toNat ≤ ks.nv.toNat; omega,
      by change ks.prop.toNat ≤ (ks.trl_end + 1#32).toNat; have := hinv.assign.prop_le; omega,
      by rw [hun']; change (ks.unass - 1#32).toNat + (ks.trl_end + 1#32).toNat = ks.nv.toNat
         have := hinv.assign.unass_eq; omega,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro l hl
      by_cases hv : l / 2 = lit.toNat / 2
      · rcases (litVar_eq_iff l lit.toNat).mp (by simpa [litVar] using hv) with rfl | hneg
        · rw [hval_l]; exact Or.inr (Or.inl rfl)
        · rw [hneg, ← litNeg_eq_xor1, hval_nl]; exact Or.inr (Or.inr rfl)
      · rw [hval_ne_v l hv]; exact hinv.assign.vals_dom l hl
    · intro l hl
      by_cases hv : l / 2 = lit.toNat / 2
      · rcases (litVar_eq_iff l lit.toNat).mp (by simpa [litVar] using hv) with rfl | hneg
        · simp [hval_l, hval_nl]
        · have hneg' : l = lit.toNat ^^^ 1 := by rw [hneg, litNeg_eq_xor1]
          have hx : (lit.toNat ^^^ 1) ^^^ 1 = lit.toNat := by
            rw [litNeg_eq_xor1, litNeg_eq_xor1, litNeg_litNeg]
          rw [hneg', hx]; simp [hval_l, hval_nl]
      · rw [hval_ne_v l hv, hval_ne_v (l ^^^ 1) (by rw [kana_xor1_div2]; exact hv)]
        exact hinv.assign.vals_neg_iff l hl
    · intro l hl
      by_cases hv : l / 2 = lit.toNat / 2
      · constructor
        · intro _
          have hlt_te : ks.trl_end.toNat < ks'.trl_end.toNat := by
            change ks.trl_end.toNat < (ks.trl_end + 1#32).toNat; omega
          exact ⟨ks.trl_end.toNat, hlt_te, by rw [htr_self, Option.getD_some]; exact hv.symm⟩
        · intro _
          rcases (litVar_eq_iff l lit.toNat).mp (by simpa [litVar] using hv) with rfl | hneg
          · rw [hval_l]; decide
          · rw [hneg, ← litNeg_eq_xor1, hval_nl]; decide
      · rw [hval_ne_v l hv, hinv.assign.vals_nz_iff_trl l hl]
        constructor
        · rintro ⟨i, hi, hiv⟩
          refine ⟨i, by change i < (ks.trl_end + 1#32).toNat; omega, ?_⟩
          rwa [htr_old i hi]
        · rintro ⟨i, hi, hiv⟩
          change i < (ks.trl_end + 1#32).toNat at hi; rw [hte1] at hi
          by_cases hie : i = ks.trl_end.toNat
          · subst hie; rw [htr_self, Option.getD_some] at hiv; exact absurd hiv.symm hv
          · rw [htr_old i (by omega)] at hiv; exact ⟨i, by omega, hiv⟩
    · unfold kittenTrailLits; rw [htrl_take, List.map_append, List.map_append, List.nodup_append]
      refine ⟨hinv.assign.trl_nodup, by simp, fun x hx y hy heq => ?_⟩
      simp only [List.map_singleton, List.mem_singleton] at hy; subst hy; subst heq
      rw [List.mem_map] at hx; obtain ⟨t, ht, htv⟩ := hx
      rw [List.mem_map] at ht; obtain ⟨b, hb, rfl⟩ := ht
      rw [List.mem_take_iff_getElem] at hb; obtain ⟨i, hi, rfl⟩ := hb
      exact hunass ⟨i, by omega, by
        rw [List.getElem?_eq_getElem (by omega : i < ks.trl.length), Option.getD_some]; exact htv⟩
    · intro l hl
      unfold kittenTrailLits at hl; rw [htrl_take, List.map_append, List.mem_append] at hl
      rcases hl with hold | hnew
      · exact hinv.assign.trl_lt l hold
      · simp at hnew; subst hnew; exact hlit
    · intro v hv
      by_cases hvv : v = lit.toNat / 2
      · subst hvv; rw [hlv_self, Option.getD_some]; exact Nat.le_refl _
      · rw [hlv_ne v hvv]; exact hinv.assign.trl_lvl_le v hv
    · intro v hv hv0
      have hne_v : v ≠ lit.toNat / 2 := by
        intro heq; have h2v : (2 * v) / 2 = lit.toNat / 2 := by omega
        rcases (litVar_eq_iff (2 * v) lit.toNat).mp (by simpa [litVar] using h2v) with h1 | h1
        · rw [h1, hval_l] at hv0; cases hv0
        · rw [h1, ← litNeg_eq_xor1, hval_nl] at hv0; cases hv0
      rw [hval_ne_v (2 * v) (by omega)] at hv0
      rw [hlv_ne v hne_v, hrs_ne v hne_v]; exact hinv.assign.unass_lvl_zero v hv hv0
    · intro i j hij hj
      change j < (ks.trl_end + 1#32).toNat at hj; rw [hte1] at hj
      by_cases hje : j = ks.trl_end.toNat
      · subst hje
        by_cases hie : i = ks.trl_end.toNat
        · subst hie; exact Nat.le_refl _
        · have hi_old : i < ks.trl_end.toNat := by omega
          have hnei : (ks.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := fun h =>
            hunass ⟨i, hi_old, h⟩
          rw [htr_old i hi_old, hlv_ne _ hnei, htr_self, Option.getD_some, hlv_self,
            Option.getD_some]
          have hli := hinv.assign.trl_lt _ (mem_kittenTrailLits_of_lt hi_old (by omega))
          exact hinv.assign.trl_lvl_le _ (by omega)
      · have hj_old : j < ks.trl_end.toNat := by omega
        have hi_old : i < ks.trl_end.toNat := by omega
        have hnei : (ks.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := fun h =>
          hunass ⟨i, hi_old, h⟩
        have hnej : (ks.trl[j]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := fun h =>
          hunass ⟨j, hj_old, h⟩
        rw [htr_old i hi_old, htr_old j hj_old, hlv_ne _ hnei, hlv_ne _ hnej]
        exact hinv.assign.trl_lvl_mono i j hij hj_old
    · intro i j hji hi heq
      change i < (ks.trl_end + 1#32).toNat at hi; rw [hte1] at hi
      by_cases hie : i = ks.trl_end.toNat
      · subst hie; rw [htr_self, Option.getD_some, hrs_self, Option.getD_some]; exact hrsn_ne
      · have hi_old : i < ks.trl_end.toNat := by omega
        have hj_old : j < ks.trl_end.toNat := by omega
        have hnei : (ks.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := fun h =>
          hunass ⟨i, hi_old, h⟩
        have hnej : (ks.trl[j]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := fun h =>
          hunass ⟨j, hj_old, h⟩
        rw [htr_old i hi_old, htr_old j hj_old, hlv_ne _ hnei, hlv_ne _ hnej] at heq
        rw [htr_old i hi_old, hrs_ne _ hnei]
        exact hinv.assign.dec_earliest i j hji hi_old heq
    · intro i hi l hl0
      change i < (ks.trl_end + 1#32).toNat at hi; rw [hte1] at hi
      dsimp only [l] at hl0 ⊢
      by_cases hie : i = ks.trl_end.toNat
      · subst hie
        rw [htr_self, Option.getD_some, hlv_self, Option.getD_some] at hl0
        rw [htr_self, Option.getD_some, hrs_self, Option.getD_some]
        obtain ⟨hent0, hante0⟩ := hlvl0_req hl0
        exact ⟨hrsn_ne, hval_l, hval_nl, hent0, fun ha => ⟨hrsn_lt, hante0 ha⟩⟩
      · have hi_old : i < ks.trl_end.toNat := by omega
        have hne_v : (ks.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := fun h =>
          hunass ⟨i, hi_old, h⟩
        have hne_nv : ((ks.trl[i]?.getD 0#32).toNat ^^^ 1) / 2 ≠ lit.toNat / 2 := by
          rw [kana_xor1_div2]; exact hne_v
        rw [htr_old i hi_old, hlv_ne _ hne_v] at hl0
        have h0 := hinv.assign.lvl0_ok i hi_old hl0
        rw [htr_old i hi_old, hrs_ne _ hne_v, hval_ne_v _ hne_v, hval_ne_v _ hne_nv]
        exact h0
  have hrsn' : ReasonOk ks' := by
    intro i hi; change i < (ks.trl_end + 1#32).toNat at hi; rw [hte1] at hi
    dsimp only
    by_cases hie : i = ks.trl_end.toNat
    · subst hie; rw [htr_self, Option.getD_some, hrs_self, Option.getD_some]
      refine Or.inr ⟨hrsn_lt, hlit_mem, fun x hx hne => ?_⟩
      obtain ⟨j, hj, hjeq⟩ := hothers x hx hne
      exact ⟨j, hj, by rw [htr_old j hj]; exact hjeq⟩
    · have hi_old : i < ks.trl_end.toNat := by omega
      have hne_v : (ks.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := fun h =>
        hunass ⟨i, hi_old, h⟩
      rw [htr_old i hi_old, hrs_ne _ hne_v]
      rcases hinv.reasons i hi_old with hff | ⟨hr_lt, hmem, hall⟩
      · exact Or.inl hff
      · refine Or.inr ⟨hr_lt, hmem, fun x hx hne => ?_⟩
        obtain ⟨j, hj, hjeq⟩ := hall x hx hne
        exact ⟨j, hj, by rw [htr_old j (Nat.lt_trans hj hi_old)]; exact hjeq⟩
  have hdec' : kittenTrailDecisions ks' = kittenTrailDecisions ks := by
    unfold kittenTrailDecisions
    rw [htrl_take, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
      hrs_self, Option.getD_some, kana_ite_f hrsn_ne, List.append_nil]
    refine kana_filterMap_congr fun x hx => ?_
    rw [List.mem_take_iff_getElem] at hx; obtain ⟨i, hi, rfl⟩ := hx
    have hne_v : (ks.trl[i]'(by omega)).toNat / 2 ≠ lit.toNat / 2 := fun h =>
      hunass ⟨i, by omega, by
        rw [List.getElem?_eq_getElem (by omega : i < ks.trl.length), Option.getD_some]; exact h⟩
    rw [hrs_ne _ hne_v]
  refine ⟨⟨hsh', hcl', kittenAssignStep_preserves_watches hinv.watches lit rsn, hba', hrsn'⟩,
    hsync', rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => ⟨rfl, rfl⟩,
    fun _ => ⟨ks.trl_end.toNat, by change ks.trl_end.toNat < (ks.trl_end + 1#32).toNat; omega, ?_⟩,
    hdec', fun i hi => ?_⟩
  · rw [htr_self, Option.getD_some, hlv_self, Option.getD_some]; rfl
  · have hne_v : (ks.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := fun h => hunass ⟨i, hi, h⟩
    exact ⟨by change i < (ks.trl_end + 1#32).toNat; omega, htr_old i hi, hlv_ne _ hne_v⟩

/-! ## 2. Parametric `Func.wp` Proof for `full_kitten_analyze` (`[12]`) -/

private structure AnaBrkPost (acap : Nat) (ks : KittenState) (F0 : List (List Nat))
    (uip : BitVec 32) (st : KittenState) : Prop where
  sh : st.ShapesOk acap
  pres : KittenAnaClausePreserved ks st
  nres_le : st.nres.toNat ≤ kMaxL + 1
  nkl_pos : 1 ≤ st.nkl.toNat
  nkl_le : st.nkl.toNat ≤ st.nv.toNat
  nana_le : st.nana.toNat ≤ st.nv.toNat
  ana_lt : ∀ i < st.nana.toNat, (st.ana[i]?.getD 0#32).toNat < st.nv.toNat
  flags_seen : ∀ v < st.nv.toNat,
    ((st.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32) ↔
      ∃ i < st.nana.toNat, (st.ana[i]?.getD 0#32).toNat = v
  uip_ok : uip ≠ 0xFFFFFFFF#32 →
    uip.toNat < 2 * st.nv.toNat ∧
    st.lvlArr[uip.toNat / 2]?.getD 0#32 = st.lvl ∧
    (∀ i, 1 ≤ i → i < st.nkl.toNat →
      let l := (st.kl[i]?.getD 0#32).toNat
      l < 2 * st.nv.toNat ∧ 0 < (st.lvlArr[l / 2]?.getD 0#32).toNat ∧
      (st.lvlArr[l / 2]?.getD 0#32).toNat < st.lvl.toNat ∧ st.vals[l]? = some 2#32) ∧
    (cnfOfClauses F0).EntailsClause
      (cnfClause (uip.toNat :: ((st.kl.take st.nkl.toNat).drop 1).map BitVec.toNat)) ∧
    (st.ante ≠ 0#32 → st.nres.toNat ≤ kMaxL →
      (∀ i < st.nres.toNat, (st.res[i]?.getD 0xFFFFFFFF#32).toNat < st.nc.toNat) ∧
      (cnfOfClauses ((st.res.take st.nres.toNat).map fun c =>
        kittenClauseLits st c.toNat)).EntailsClause
          (cnfClause (uip.toNat :: ((st.kl.take st.nkl.toNat).drop 1).map BitVec.toNat)))

private theorem anaBrkPost_of_uip_ff {acap : Nat} {ks st : KittenState} {F0 : List (List Nat)}
    {idx : Nat} (hinv : KittenAnaInv acap st F0 idx) (hp : KittenAnaClausePreserved ks st) :
    AnaBrkPost acap ks F0 0xFFFFFFFF#32 st :=
  ⟨hinv.shapes, hp, hinv.nres_le, hinv.nkl_pos, hinv.nkl_le, hinv.nana_le, hinv.ana_lt,
    hinv.flags_seen, fun h => absurd rfl h⟩

local macro "c0_hcall" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-- Parametric `Func.wp` proof for `full_kitten_analyze` (`[12]`). -/
theorem full_kitten_analyze_wp (Γ : Env)
    (hAnaCl : ∀ args m Q X, fullKittenAnaClauseSpec args m Q X →
      Γ "full_kitten_ana_clause" [i64, i32, i32] [] args m Q X)
    (hBt : ∀ args m Q X, fullKittenBacktrackSpec args m Q X →
      Γ "full_kitten_backtrack" [i64, i32] [] args m Q X)
    (hMtf : ∀ args m Q X, fullKittenMtfSpec args m Q X →
      Γ "full_kitten_mtf" [i64, i32] [] args m Q X)
    (hUnit0 : ∀ args m Q X, fullKittenLearnUnit0Spec args m Q X →
      Γ "full_kitten_learn_unit0" [i64, i32, i32, .bool] [i32] args m Q X)
    (hAssign : ∀ args m Q X, fullKittenAssignSpec args m Q X →
      Γ "full_kitten_assign" [i64, i32, i32] [] args m Q X)
    (hWatch : ∀ args m Q X, fullKittenWatchSpec args m Q X →
      Γ "full_kitten_watch" [i64, i32, i32, i32] [] args m Q X) :
    ∀ args m Q X, fullKittenAnalyzeSpec args m Q X →
      Func.wp Γ full_kitten_analyze_body args m Q X := by
  rintro ⟨kPtr, confl_cid, ⟨⟩⟩ m Q X ⟨acap, ks, R, hinv, hsync, hlvl_pos, hlvl_wit,
    hconfl_lt, hconfl_fals, hm, hQ⟩
  let F0 := kittenOrigClauses ks
  have hsh := hinv.shapes
  have hnv := hinv.clauses.nv_le
  have hnv_128 : ks.nv.toNat ≤ 128 := hnv
  have hacap_lt : acap < 2 ^ 28 := hinv.clauses.acap_lt
  have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [hsh.trl_len]; have := hinv.assign.trl_end_le; omega
  have hvdec : ∃ v < ks.nv.toNat, ks.lvlArr[v]?.getD 0#32 = ks.lvl := by
    obtain ⟨i0, hi0, hl0⟩ := hlvl_wit
    have hlt := hinv.assign.trl_lt _ (mem_kittenTrailLits_of_lt hi0 htrl_len)
    exact ⟨(ks.trl[i0]?.getD 0#32).toNat / 2, by omega, hl0⟩
  -- Helper for all `return false` exits
  have hret_false : ∀ (ks' : KittenState) (m' : Mem 64),
      ks'.Inv acap → ks'.nv = ks.nv → ks'.orig_nc = ks.orig_nc → ks'.ante = ks.ante →
      ks'.nassump = ks.nassump → ks'.assump = ks.assump → ks'.incons = ks.incons →
      ks'.failing = ks.failing → kittenOrigClauses ks' = F0 →
      (∀ ci < ks.orig_nc.toNat, ks'.clAux[ci]? = ks.clAux[ci]?) →
      (∀ ci < ks.orig_nc.toNat,
        (ks'.clMeta[ci]?.getD 0#32 &&& kmCore) = (ks.clMeta[ci]?.getD 0#32 &&& kmCore)) →
      (KittenMem kPtr ks' ⋆ R) m' → Q (false, ()) m' :=
    fun ks' m' hi h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hm' =>
      hQ false ks' m' hi h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 (fun h => by cases h) hm'
  have hmA : (KittenMemA kPtr acap ks ⋆ R) m := kittenMem_to_amem hsh hm; clear hm
  -- Phase 0: initialize header counters and call `full_kitten_ana_clause(k, confl_cid, 0xFFFFFFFF)`
  c0_hsteps_nogrp
  let ks0 : KittenState := { ks with nres := 0#32, nkl := 1#32, nana := 0#32, status := 0#32 }
  obtain ⟨hinv0, hpres0⟩ := kana_init_anaInv hinv hsync hlvl_pos hvdec
  have hm0 : (KittenMem kPtr ks0 ⋆ R) m := by
    obtain ⟨_, hm0'⟩ := kittenMemA_to_mem hm
    refine Eq.mp (congrArg (fun x => (KittenMem kPtr x ⋆ R) _) ?_) hm0'
    kstate_ext <;> rfl
  c0_hcall hAnaCl
  refine ⟨acap, ks0, F0, ks.trl_end.toNat, R, hinv0, hconfl_lt, Or.inl rfl, hvdec, ?_,
    Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩, hm0, fun ks1 m1 hinv1 hpres1 hF0_1 hres_1 hm1 => ?_⟩
  · intro l hl _
    have hwf := hinv.clauses.cl_wf confl_cid.toNat hconfl_lt
    obtain ⟨j, hj, hjeq⟩ := kitten_falsified_to_trail hsh hnv hinv.assign hsync
      (hwf.2.2.2.1 l hl) (hconfl_fals l hl)
    exact ⟨j, hj, by rw [hjeq, ← litNeg_eq_xor1]⟩
  · have hpres_k1 : KittenAnaClausePreserved ks ks1 :=
      kana_anaClausePreserved_trans hpres0 hpres1
    have hm1A : (KittenMemA kPtr acap ks1 ⋆ R) m1 := kittenMem_to_amem hinv1.shapes hm1
    clear hm1 hm hm0
    c0_hsteps_nogrp
    -- Phase 1: 1UIP `while (k[KH_STATUS] > 0u)` loop (`group#0` break + `group#1` loop)
    refine wp_while_break_state
      (brkTs := [i32, i32]) (lpTs := [i32])
      (β := BitVec 32 × BitVec 32 × KittenState)
      (fun b => (b.1, b.2.1, ()))
      (fun b mb => AnaBrkPost acap ks F0 b.2.1 b.2.2 ∧ (KittenMemA kPtr acap b.2.2 ⋆ R) mb)
      (α := BitVec 32 × KittenState)
      (fun p => (p.1, ()))
      (fun p => p.1.toNat)
      (fun p ml => KittenAnaInv acap p.2 F0 p.1.toNat ∧ KittenAnaClausePreserved ks p.2 ∧
        (cnfOfClauses F0).EntailsClause (cnfClause (kittenResolventLits p.2 p.1.toNat)) ∧
        (p.2.ante ≠ 0#32 → p.2.nres.toNat ≤ kMaxL →
          (∀ i < p.2.nres.toNat, (p.2.res[i]?.getD 0xFFFFFFFF#32).toNat < p.2.nc.toNat) ∧
          (cnfOfClauses ((p.2.res.take p.2.nres.toNat).map fun c =>
            kittenClauseLits p.2 c.toNat)).EntailsClause
              (cnfClause (kittenResolventLits p.2 p.1.toNat))) ∧
        (KittenMemA kPtr acap p.2 ⋆ R) ml)
      ?_ ?_ ?_
    · -- After Phase 1 (`J0_0(idx, uip)`): Phases 2–7
      rintro B ⟨_, uip, stB⟩ mB ⟨hBrk, hmB⟩
      dsimp only at hBrk hmB ⊢
      have hnvB : stB.nv = ks.nv := hBrk.pres.nv
      have hnvB_nat : stB.nv.toNat = ks.nv.toNat := congrArg BitVec.toNat hnvB
      have hna_128 : stB.nana.toNat ≤ 128 := by have := hBrk.nana_le; omega
      have hnk_128 : stB.nkl.toNat ≤ 128 := by have := hBrk.nkl_le; omega
      -- Phase 2: Flag-clear loop `while (ai < k[KH_NANA])`
      c0_hsteps_nogrp
      refine wp_while_state1 (fun p : BitVec 32 × List (BitVec 32) => p.1)
        (fun p => stB.nana.toNat - p.1.toNat)
        (fun p mf => p.1.toNat ≤ stB.nana.toNat ∧ p.2.length = 128 ∧
          (∀ v < stB.nv.toNat, (∃ j < p.1.toNat, (stB.ana[j]?.getD 0#32).toNat = v) →
            (p.2[v]?.getD 0#32 &&& 2#32) = 0#32) ∧
          (∀ v < stB.nv.toNat, (p.2[v]?.getD 0#32 &&& 2#32) ≠ 0#32 →
            (stB.flags[v]?.getD 0#32 &&& 2#32) ≠ 0#32) ∧
          (KittenMemA kPtr acap { stB with flags := p.2 } ⋆ R) mf)
        ?_ ?_
      · intro Lf hLf
        exact wp_jump_state (proj := fun p : BitVec 32 × List (BitVec 32) => (p.1, ()))
          (0#32, stB.flags) rfl
          (hLf (0#32, stB.flags) mB ⟨Nat.zero_le _, hBrk.sh.flags_len,
            fun _ _ ⟨_, hj, _⟩ => by simp at hj, fun _ _ h => h,
            by simpa using hmB⟩)
      · rintro Lf ⟨ai, fls⟩ mf ⟨hai_le, hfls_len, hclr, hsub, hmf⟩ ihf
        dsimp only at hai_le hfls_len hclr hsub hmf ⊢
        obtain ⟨stF, hstF⟩ : ∃ x : KittenState, x = { stB with flags := fls } := ⟨_, rfl⟩
        rw [← hstF] at hmf
        c0_hsplit
        · have hai_lt : ai.toNat < stB.nana.toNat := by
            have : stF.nana = stB.nana := by rw [hstF]
            rw [← this]; exact hc
          have hai_128 : ai.toNat < 128 := by omega
          have hai_28 : ai.toNat < 2 ^ 28 := by omega
          have hav_lt : (stB.ana[ai.toNat]?.getD 0#32).toNat < stB.nv.toNat :=
            hBrk.ana_lt ai.toNat hai_lt
          have hav_st_128 : (stF.ana[ai.toNat]?.getD 0#32).toNat < 128 := by
            rw [hstF]; dsimp only; omega
          have hav_st_28 : (stF.ana[ai.toNat]?.getD 0#32).toNat < 2 ^ 28 := by omega
          have hai1 : (ai + 1#32).toNat = ai.toNat + 1 := by bv_omega
          c0_hsteps!
          let av := stB.ana[ai.toNat]?.getD 0#32
          let fls' := fls.set av.toNat (fls[av.toNat]?.getD 0#32 &&& ~~~2#32)
          refine ihf (ai + 1#32, fls') _ (by dsimp only; rw [hai1]; omega)
            ⟨by dsimp only; rw [hai1]; omega, by simp [fls', hfls_len], ?_, ?_, ?_⟩
          · intro v hv ⟨j, hj, hjeq⟩; rw [hai1] at hj
            by_cases hva : v = av.toNat
            · subst hva
              rw [List.getElem?_set_self (by omega), Option.getD_some]
              exact kana_fl_andnot2_and2_zero _
            · rw [List.getElem?_set_ne (Ne.symm hva)]
              have hj_lt : j < ai.toNat := by
                by_cases hja : j = ai.toNat
                · subst hja; exact absurd hjeq.symm hva
                · omega
              exact hclr v hv ⟨j, hj_lt, hjeq⟩
          · intro v hv hnz
            by_cases hva : v = av.toNat
            · subst hva
              rw [List.getElem?_set_self (by omega), Option.getD_some] at hnz
              exact absurd (kana_fl_andnot2_and2_zero _) hnz
            · rw [List.getElem?_set_ne (Ne.symm hva)] at hnz
              exact hsub v hv hnz
          · refine Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ R) _) ?_) hm
            rw [hstF]; kstate_ext <;> (first | rfl | kp_field)
        · -- Exit flag-clear loop: `ai = stB.nana`
          have hai_eq : ai.toNat = stB.nana.toNat := by
            have h1 : ¬ ai.toNat < stF.nana.toNat := hc
            have h2 : stF.nana = stB.nana := by rw [hstF]
            rw [h2] at h1; omega
          have hfl_clean : ∀ v < stF.nv.toNat, (stF.flags[v]?.getD 0#32 &&& 2#32) = 0#32 := by
            intro v hv; rw [hstF] at hv ⊢
            by_cases h0 : (fls[v]?.getD 0#32 &&& 2#32) = 0#32
            · exact h0
            · have hseen := (hBrk.flags_seen v hv).mp (hsub v hv h0)
              rw [← hai_eq] at hseen; exact hclr v hv hseen
          have hshF : stF.ShapesOk acap := by
            rw [hstF]; exact ⟨hBrk.sh.hdrTail_len, hBrk.sh.lvlArr_len, hBrk.sh.rsn_len,
              hBrk.sh.qprev_len, hBrk.sh.qnext_len, hBrk.sh.qstampArr_len, hBrk.sh.trl_len,
              hfls_len, hBrk.sh.vals_len, hBrk.sh.assump_len, hBrk.sh.ana_len, hBrk.sh.kl_len,
              hBrk.sh.units_len, hBrk.sh.res_len, hBrk.sh.whead_len, hBrk.sh.wnext_len,
              hBrk.sh.wblit_len, hBrk.sh.clOff_len, hBrk.sh.clMeta_len, hBrk.sh.clAux_len,
              hBrk.sh.arena_len⟩
          have hpresF : KittenAnaClausePreserved ks stF := by
            rw [hstF]
            exact ⟨hBrk.pres.nv, hBrk.pres.nc, hBrk.pres.orig_nc, hBrk.pres.lvl, hBrk.pres.prop,
              hBrk.pres.trl_end, hBrk.pres.unass, hBrk.pres.incons, hBrk.pres.failing,
              hBrk.pres.ante, hBrk.pres.alen, hBrk.pres.acap, hBrk.pres.nassump, hBrk.pres.nunits,
              hBrk.pres.lvlArr, hBrk.pres.rsn, hBrk.pres.trl, hBrk.pres.vals, hBrk.pres.assump,
              hBrk.pres.units, hBrk.pres.whead, hBrk.pres.wnext, hBrk.pres.wblit, hBrk.pres.clOff,
              hBrk.pres.clMeta, hBrk.pres.clAux, hBrk.pres.arena,
              fun v hv _ => hinv.clauses.flags_clean v hv⟩
          have ⟨hinvF, hsyncF⟩ := kana_inv_of_ana_clean hinv hsync hshF hpresF
            (by rw [hstF]; exact hBrk.nres_le) (by rw [hstF]; exact hnk_128)
            (by rw [hstF]; exact hna_128) hfl_clean
          have horigF : kittenOrigClauses stF = F0 :=
            kittenOrigClauses_eq_of hpresF.orig_nc fun c _ => by
              simp [kittenClauseLits, kittenClauseOff, kittenClauseSize, kittenClauseMeta,
                hpresF.clOff, hpresF.clMeta, hpresF.arena]
          -- Phase 3a: early return if `uip == 0xFFFFFFFF || (ante != 0 && nres > 256)`
          c0_hsplit
          · -- `uip == 0xFFFFFFFF` -> `return false`
            c0_hsteps!
            obtain ⟨_, hmF⟩ := kittenMemA_to_mem hmf
            exact hret_false stF mf hinvF hpresF.nv hpresF.orig_nc hpresF.ante hpresF.nassump
              hpresF.assump hpresF.incons hpresF.failing horigF
              (fun _ _ => by rw [hpresF.clAux]) (fun _ _ => by rw [hpresF.clMeta]) hmF
          · have huip_ne : uip ≠ 0xFFFFFFFF#32 := ‹_›
            c0_hsteps_nogrp
            refine wp_join0
              (fun m2 => m2 = mf ∧ (stF.ante ≠ 0#32 → stF.nres.toNat ≤ kMaxL)) ?_ ?_
            · -- Non-early-return (`J2_0 []`): store `kl[0] := uip`, find `jlvl`/`wi`, swap
              intro J2 m2 ⟨rfl, hante_nres⟩
              obtain ⟨huip_lt, huip_lvl, hkl_ntB, hF0_uip, hres_uip⟩ := hBrk.uip_ok huip_ne
              have huip_lt_k : uip.toNat < 2 * ks.nv.toNat := by rwa [hnvB] at huip_lt
              have huip_lvl_k : ks.lvlArr[uip.toNat / 2]?.getD 0#32 = ks.lvl := by
                rwa [hBrk.pres.lvlArr, hBrk.pres.lvl] at huip_lvl
              have hkl_ntF : ∀ i, 1 ≤ i → i < stF.nkl.toNat →
                  let l := (stF.kl[i]?.getD 0#32).toNat
                  l < 2 * stF.nv.toNat ∧ 0 < (stF.lvlArr[l / 2]?.getD 0#32).toNat ∧
                  (stF.lvlArr[l / 2]?.getD 0#32).toNat < stF.lvl.toNat ∧
                  stF.vals[l]? = some 2#32 := by
                rw [hstF]; exact hkl_ntB
              have h0_128 : (0 : Nat) < 128 := by decide
              have h0_28 : (0 : Nat) < 2 ^ 28 := by decide
              let stKl0 := stF.putArr .kl 0 uip
              c0_hsteps_nogrp
              -- Phase 3b: pure read-only loop finding `jlvl` and `wi` (`group#3`)
              refine wp_while_state_pure
                (ts := [i32, i32, i32])
                (α := BitVec 32 × BitVec 32 × BitVec 32)
                (fun t => (t.1, t.2.1, t.2.2, ()))
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
                have hkl0_nkl : stKl0.nkl = stF.nkl := by dsimp only [stKl0]; kp_field
                c0_hsplit
                · have hi_lt : i.toNat < stF.nkl.toNat := by rw [← hkl0_nkl]; exact hc
                  have hi_128 : i.toNat < 128 := by rw [hstF] at hi_lt; dsimp only at hi_lt; omega
                  have hi_28 : i.toNat < 2 ^ 28 := by omega
                  have hkl0_i : stKl0.kl[i.toNat]? = stF.kl[i.toNat]? := by
                    dsimp only [stKl0]; kp_field; exact List.getElem?_set_ne (by omega)
                  have hnt_i := hkl_ntF i.toNat hi1 hi_lt
                  dsimp only at hnt_i
                  have hlv_div : (stKl0.kl[i.toNat]?.getD 0#32 >>> 1).toNat =
                      (stF.kl[i.toNat]?.getD 0#32).toNat / 2 := by
                    rw [hkl0_i]; exact (bv32_lit_div2_bv hnt_i.1).1
                  have hlv_128 : (stKl0.kl[i.toNat]?.getD 0#32 >>> 1).toNat < 128 := by
                    rw [hlv_div]; have := hinvF.clauses.nv_le; unfold kMaxV at this; omega
                  have hlv_28 : (stKl0.kl[i.toNat]?.getD 0#32 >>> 1).toNat < 2 ^ 28 := by omega
                  have hi1_add : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
                  have hil_pos : 0 < (stF.lvlArr[(stF.kl[i.toNat]?.getD 0#32).toNat / 2]?.getD
                      0#32).toNat := hnt_i.2.1
                  have hil_lt : (stF.lvlArr[(stF.kl[i.toNat]?.getD 0#32).toNat / 2]?.getD
                      0#32).toNat < ks.lvl.toNat := by rw [← hpresF.lvl]; exact hnt_i.2.2.1
                  have hkl0_lv : stKl0.lvlArr = stF.lvlArr := by dsimp only [stKl0]; kp_field
                  c0_hsteps!
                  · -- `il > jlvl`
                    let il := stF.lvlArr[(stF.kl[i.toNat]?.getD 0#32).toNat / 2]?.getD 0#32
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
                  · -- `¬ (il > jlvl)`
                    let il := stF.lvlArr[(stF.kl[i.toNat]?.getD 0#32).toNat / 2]?.getD 0#32
                    have hle : il.toNat ≤ jlvl.toNat := by
                      have h1 : ¬ jlvl.toNat <
                          (stKl0.lvlArr[(stKl0.kl[i.toNat]?.getD 0#32 >>> 1).toNat]?.getD
                            0#32).toNat := hc
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
                · -- Exit jump-level loop (`i == nkl`): Phase 3c conditional swap (`group#4`)
                  have hi_eq : i.toNat = stF.nkl.toNat := by
                    have h1 : ¬ i.toNat < stKl0.nkl.toNat := hc
                    rw [hkl0_nkl] at h1; omega
                  rw [hi_eq] at hi_eq1 hi_ge2 hall_le
                  let stSw := if 2 ≤ stF.nkl.toNat ∧ wi ≠ 1#32 then
                    (stKl0.putArr .kl 1 (stKl0.kl[wi.toNat]?.getD 0#32)).putArr .kl wi.toNat
                      (stKl0.kl[1]?.getD 0#32)
                    else stKl0
                  obtain ⟨hinvSw, hsyncSw, hpresSwF, hsw_nkl, hsw_nana, hsw_ana, hsw_nres,
                    hsw_res, hsw0, hsw_mem, hsw_nt⟩ :=
                    kana_swap_kl_preserves hinvF hsyncF (by rw [hstF]; exact hBrk.nkl_pos)
                      (by rw [hstF]; exact hBrk.nkl_le)
                      (fun h2 => ⟨(hi_ge2 h2).1, (hi_ge2 h2).2.1⟩)
                      (fun k hk1 hk_lt =>
                        let h := hkl_ntF k hk1 hk_lt
                        ⟨h.1, h.2.1, hall_le k hk1 hk_lt, h.2.2.2⟩)
                  have hpresSw : KittenAnaClausePreserved ks stSw :=
                    kana_anaClausePreserved_trans hpresF hpresSwF
                  c0_hsteps_nogrp
                  refine wp_join0 (fun m4 => (KittenMemA kPtr acap stSw ⋆ R) m4) ?_ ?_
                  · -- After swap (`J4_0 []`): Phase 4 `backtrack`, Phase 5 `mtf`, Phases 6–7
                    intro J4 m4 hm4
                    obtain ⟨_, hm4_bt⟩ := kittenMemA_to_mem hm4
                    c0_hsteps_nogrp
                    c0_hcall hBt
                    refine ⟨acap, stSw, R, hinvSw, fun i hi _ => hsyncSw i hi, hm4_bt,
                      fun ksBt mBt hinvBt hsyncBt hlvlBt hte_le htake hbtPres hdecBt hB1 hmBt => ?_⟩
                    dsimp only [Arg.val] at hlvlBt
                    obtain ⟨huip_none, huip_v0, huip_nv0, hte_lt_nv, hkl_bt_trl, hdec_ks, hA2_bt⟩ :=
                      kana_after_bt_facts hinvSw hsyncSw hpresSw huip_lt_k huip_lvl_k hj_lt
                        hinvBt hlvlBt hte_le htake hbtPres hdecBt hB1
                    have hbt_nv : ksBt.nv = ks.nv := hbtPres.nv.trans hpresSw.nv
                    have hbt_on : ksBt.orig_nc = ks.orig_nc := hbtPres.orig_nc.trans hpresSw.orig_nc
                    have hbt_an : ksBt.ante = ks.ante := hbtPres.ante.trans hpresSw.ante
                    have hbt_na : ksBt.nassump = ks.nassump := hbtPres.nassump.trans hpresSw.nassump
                    have hbt_as : ksBt.assump = ks.assump := hbtPres.assump.trans hpresSw.assump
                    have hbt_in : ksBt.incons = ks.incons := hbtPres.incons.trans hpresSw.incons
                    have hbt_fa : ksBt.failing = ks.failing := hbtPres.failing.trans hpresSw.failing
                    have hbt_ca : ksBt.clAux = ks.clAux := hbtPres.clAux.trans hpresSw.clAux
                    have hbt_cm : ksBt.clMeta = ks.clMeta := hbtPres.clMeta.trans hpresSw.clMeta
                    have hbt_co : ksBt.clOff = ks.clOff := hbtPres.clOff.trans hpresSw.clOff
                    have hbt_ar : ksBt.arena = ks.arena := hbtPres.arena.trans hpresSw.arena
                    have hbt_nkl : ksBt.nkl = stF.nkl := hbtPres.nkl.trans hsw_nkl
                    have hbt_nana : ksBt.nana = stF.nana := hbtPres.nana.trans hsw_nana
                    have hbt_nres : ksBt.nres = stF.nres := hbtPres.nres.trans hsw_nres
                    have hbt_res : ksBt.res = stF.res := hbtPres.res.trans hsw_res
                    have horigBt : kittenOrigClauses ksBt = F0 :=
                      kittenOrigClauses_eq_of hbt_on fun c _ => by
                        simp [kittenClauseLits, kittenClauseOff, kittenClauseSize, kittenClauseMeta,
                          hbt_co, hbt_cm, hbt_ar]
                    -- Phase 5: VMTF bump loop `while (ai < k[KH_NANA])` (`group#5`)
                    have hmBtA : (KittenMemA kPtr acap ksBt ⋆ R) mBt :=
                      kittenMem_to_amem hinvBt.shapes hmBt
                    clear hmBt hm4 hm4_bt
                    c0_hsteps_nogrp
                    refine wp_while_state1 (fun p : BitVec 32 × KittenState => p.1)
                      (fun p => ksBt.nana.toNat - p.1.toNat)
                      (fun p m5 => p.1.toNat ≤ ksBt.nana.toNat ∧
                        (∃ qf ql qs qst qp qn qsa, p.2 =
                          { ksBt with qfirst := qf, qlast := ql, qsearch := qs, qstamp := qst,
                                      qprev := qp, qnext := qn, qstampArr := qsa }) ∧
                        p.2.ShapesOk acap ∧ (KittenMemA kPtr acap p.2 ⋆ R) m5)
                      ?_ ?_
                    · intro L5 hL5
                      exact wp_jump_state (proj := fun p : BitVec 32 × KittenState => (p.1, ()))
                        (0#32, ksBt) rfl
                        (hL5 (0#32, ksBt) mBt ⟨Nat.zero_le _,
                          ⟨ksBt.qfirst, ksBt.qlast, ksBt.qsearch, ksBt.qstamp, ksBt.qprev,
                           ksBt.qnext, ksBt.qstampArr, rfl⟩,
                          hinvBt.shapes, hmBtA⟩)
                    · rintro L5 ⟨ai5, st5⟩ m5 ⟨hai5_le, hq5, hsh5, hm5⟩ ih5
                      dsimp only at hai5_le hq5 hsh5 hm5 ⊢
                      obtain ⟨qf, ql, qs, qst, qp, qn, qsa, hst5_eq⟩ := hq5
                      c0_hsplit
                      · have hai5_lt : ai5.toNat < ksBt.nana.toNat := by
                          rw [hst5_eq] at hc; exact hc
                        have hai5_128 : ai5.toNat < 128 := by
                          have := hinvBt.clauses.nana_le; unfold kMaxV at this; omega
                        have hai5_28 : ai5.toNat < 2 ^ 28 := by omega
                        have hai5_1 : (ai5 + 1#32).toNat = ai5.toNat + 1 := by bv_omega
                        c0_hsteps_nogrp
                        obtain ⟨_, hm5_m⟩ := kittenMemA_to_mem hm5
                        c0_hcall hMtf
                        refine ⟨acap, st5, R, hsh5, hacap_lt,
                          by rw [hst5_eq]; exact hinvBt.clauses.nv_le,
                          hm5_m, fun qf' ql' qs' qst' qp' qn' qsa' m5' hsh5' hm5' => ?_⟩
                        c0_hsteps!
                        let st5' : KittenState :=
                          { st5 with qfirst := qf', qlast := ql', qsearch := qs', qstamp := qst',
                                     qprev := qp', qnext := qn', qstampArr := qsa' }
                        refine ih5 (ai5 + 1#32, st5') m5' (by dsimp only; rw [hai5_1]; omega)
                          ⟨by dsimp only; rw [hai5_1]; omega,
                           ⟨qf', ql', qs', qst', qp', qn', qsa',
                            by dsimp only [st5']; rw [hst5_eq]⟩,
                           hsh5', kittenMem_to_amem hsh5' hm5'⟩
                      · -- Exit MTF loop (`ai5 == nana`): Phases 6 & 7!
                        have hinv5 : st5.Inv acap := by
                          rw [hst5_eq] at hsh5 ⊢
                          exact kittenState_setQueue_preserves_inv hinvBt hsh5.qprev_len
                            hsh5.qnext_len hsh5.qstampArr_len
                        have hsync5 : KittenTrailSynced st5 := by rw [hst5_eq]; exact hsyncBt
                        have horig5 : kittenOrigClauses st5 = F0 := by rw [hst5_eq]; exact horigBt
                        have hF0_kl5 : (cnfOfClauses (kittenOrigClauses st5)).EntailsClause
                            (cnfClause ((st5.kl.take st5.nkl.toNat).map BitVec.toNat)) := by
                          rw [horig5, hst5_eq, hbtPres.kl, hbtPres.nkl]
                          exact kana_clause_entails_of_subset hsw_mem
                            (by rw [hstF]; exact hF0_uip)
                        have hres_kl5 : st5.ante ≠ 0#32 →
                            (∀ i < st5.nres.toNat,
                              (st5.res[i]?.getD 0xFFFFFFFF#32).toNat < st5.nc.toNat) ∧
                            (cnfOfClauses ((st5.res.take st5.nres.toNat).map fun c =>
                              kittenClauseLits st5 c.toNat)).EntailsClause
                                (cnfClause ((st5.kl.take st5.nkl.toNat).map BitVec.toNat)) := by
                          intro ha5
                          have haB : stB.ante ≠ 0#32 := by
                            rw [hst5_eq, hbtPres.ante, hpresSwF.ante, hstF] at ha5; exact ha5
                          have hnrB : stB.nres.toNat ≤ kMaxL := by
                            have := hante_nres (by rw [hstF]; exact haB); rwa [hstF] at this
                          obtain ⟨hltB, hentB⟩ := hres_uip haB hnrB
                          have hst5_cl : ∀ c, kittenClauseLits st5 c = kittenClauseLits stB c := by
                            intro c
                            have hco : st5.clOff = stB.clOff := by
                              rw [hst5_eq]
                              exact hbtPres.clOff.trans (hpresSwF.clOff.trans (by rw [hstF]))
                            have hcm : st5.clMeta = stB.clMeta := by
                              rw [hst5_eq]
                              exact hbtPres.clMeta.trans (hpresSwF.clMeta.trans (by rw [hstF]))
                            have har : st5.arena = stB.arena := by
                              rw [hst5_eq]
                              exact hbtPres.arena.trans (hpresSwF.arena.trans (by rw [hstF]))
                            simp only [kittenClauseLits, kittenClauseOff, kittenClauseSize,
                              kittenClauseMeta, hco, hcm, har]
                          refine ⟨by rw [hst5_eq, hbtPres.nres, hbtPres.res, hbtPres.nc,
                            hsw_nres, hsw_res, hpresSwF.nc, hstF]; exact hltB, ?_⟩
                          have hmp : (st5.res.take st5.nres.toNat).map
                              (fun c => kittenClauseLits st5 c.toNat) =
                              (stB.res.take stB.nres.toNat).map fun c =>
                                kittenClauseLits stB c.toNat := by
                            have hr : st5.res = stB.res := by
                              rw [hst5_eq]; exact hbtPres.res.trans (hsw_res.trans (by rw [hstF]))
                            have hnr : st5.nres = stB.nres := by
                              rw [hst5_eq]; exact hbtPres.nres.trans (hsw_nres.trans (by rw [hstF]))
                            rw [hr, hnr]
                            exact List.map_congr_left fun c _ => hst5_cl c.toNat
                          rw [hmp, hst5_eq, hbtPres.kl, hbtPres.nkl]
                          exact kana_clause_entails_of_subset hsw_mem (by rw [hstF]; exact hentB)
                        -- Branch on `nkl == 1u`
                        c0_hsplit
                        · -- Phase 6: Unit clause branch (`nkl == 1u`)
                          have hnkl1 : stF.nkl = 1#32 := by rw [← hkl0_nkl]; exact hc
                          have hj0 : jlvl = 0#32 := (hi_eq1 (by rw [hnkl1]; decide)).1
                          have hkl_take1 : (st5.kl.take st5.nkl.toNat).map BitVec.toNat =
                              [uip.toNat] := by
                            rw [hst5_eq, hbtPres.kl, hbt_nkl, hnkl1]
                            change (stSw.kl.take 1).map BitVec.toNat = [uip.toNat]
                            rw [List.take_add_one, List.take_zero, List.nil_append, hsw0,
                              Option.toList_some]; rfl
                          rw [hkl_take1] at hF0_kl5 hres_kl5
                          obtain ⟨_, hm5_u⟩ := kittenMemA_to_mem hm5
                          c0_hsteps_nogrp
                          c0_hcall hUnit0
                          refine ⟨acap, st5, R, hsh5, hinv5.clauses,
                            by rw [hst5_eq, hbt_nv]; exact huip_lt_k,
                            fun h => absurd h (by decide), fun _ h => absurd h (by decide),
                            fun ha _ =>
                              ⟨(by
                                  rw [hst5_eq, hbt_nres]
                                  exact hante_nres
                                    (by rw [hst5_eq, hbtPres.ante, hpresSwF.ante] at ha
                                        exact ha)),
                                (hres_kl5 ha).1, (hres_kl5 ha).2⟩,
                            hF0_kl5, hm5_u, fun ucid ksU mU hshU hclU hfailU hokU hmU => ?_⟩
                          c0_hsplit
                          · -- `ucid == 0xFFFFFFFF`: `return false`
                            have hksU_eq : ksU = st5 := hfailU hc
                            c0_hsteps!
                            exact hret_false ksU mU (by rw [hksU_eq]; exact hinv5)
                              (by rw [hksU_eq, hst5_eq]; exact hbt_nv)
                              (by rw [hksU_eq, hst5_eq]; exact hbt_on)
                              (by rw [hksU_eq, hst5_eq]; exact hbt_an)
                              (by rw [hksU_eq, hst5_eq]; exact hbt_na)
                              (by rw [hksU_eq, hst5_eq]; exact hbt_as)
                              (by rw [hksU_eq, hst5_eq]; exact hbt_in)
                              (by rw [hksU_eq, hst5_eq]; exact hbt_fa)
                              (by rw [hksU_eq]; exact horig5)
                              (fun _ _ => by rw [hksU_eq, hst5_eq, hbt_ca])
                              (fun _ _ => by rw [hksU_eq, hst5_eq, hbt_cm]) hmU
                          · -- `ucid ≠ 0xFFFFFFFF`: assign `(uip, ucid)` and `return true`
                            have huc_ne : ucid ≠ 0xFFFFFFFF#32 := hc
                            obtain ⟨huc_eq, hncU, hpU, _, hclU_lits⟩ := hokU huc_ne
                            obtain ⟨hinvU, hsyncU, horigU, hca_cmU⟩ :=
                              kana_unit0_to_inv hinv5 hsync5 hshU hclU hncU hpU
                            have huc_lt : ucid.toNat < ksU.nc.toNat := by
                              rw [huc_eq, hncU]; have := hinv5.clauses.nc_le
                              unfold kMaxCl at this; bv_omega
                            c0_hsteps_nogrp
                            c0_hcall hAssign
                            refine ⟨acap, ksU, R, hshU, hacap_lt, hinvU.clauses.nv_le,
                              by rw [hpU.nv, hst5_eq, hbt_nv]; exact huip_lt_k,
                              by rw [hpU.trl_end, hpU.nv, hst5_eq]; exact hte_lt_nv, hmU,
                              fun mFin hmFin => ?_⟩
                            c0_hsteps!
                            dsimp only [Arg.val] at hmFin
                            obtain ⟨hinvFin, hsyncFin, f_nv, f_on, f_lvl, f_an, f_na, f_as, f_in,
                              f_fa, f_orig, f_ca_cm, f_lvl_wit, f_dec, f_trl_old⟩ :=
                              kana_assignStep_preserves_inv (lit := uip) (rsn := ucid) hinvU hsyncU
                                (by rw [hpU.nv, hst5_eq, hbt_nv]; exact huip_lt_k)
                                (by rw [hpU.trl_end, hpU.nv, hst5_eq]; exact hte_lt_nv)
                                (by rw [hpU.trl_end, hpU.trl, hst5_eq]; exact huip_none)
                                huc_ne huc_lt (by rw [hclU_lits]; exact List.mem_cons_self)
                                (fun x hx hne => by
                                  rw [hclU_lits] at hx; simp at hx; exact absurd hx hne)
                                (fun _ => ⟨by rw [horigU]; exact hF0_kl5, fun _ => hclU_lits⟩)
                            have f_lvl_eq : (kittenAssignStep ksU uip ucid).lvl = jlvl := by
                              rw [f_lvl, hpU.lvl, hst5_eq, hlvlBt]
                            have f_dec_eq : kittenTrailDecisions (kittenAssignStep ksU uip ucid) =
                                kittenTrailDecisions ksBt := by
                              rw [f_dec]; unfold kittenTrailDecisions
                              rw [hpU.trl, hpU.trl_end, hpU.rsn, hst5_eq]
                            have hci_u : ∀ ci < ks.orig_nc.toNat,
                                (kittenAssignStep ksU uip ucid).clAux[ci]? = ks.clAux[ci]? ∧
                                ((kittenAssignStep ksU uip ucid).clMeta[ci]?.getD 0#32 &&& kmCore) =
                                  (ks.clMeta[ci]?.getD 0#32 &&& kmCore) := by
                              intro ci hci
                              have h1 := f_ca_cm ci
                                (by rw [hpU.orig_nc, hst5_eq, hbt_on]; exact hci)
                              have h2 := hca_cmU ci (by rw [hst5_eq, hbt_on]; exact hci)
                              exact ⟨h1.1.trans (h2.1.trans (by rw [hst5_eq, hbt_ca])),
                                h1.2.trans (h2.2.trans (by rw [hst5_eq, hbt_cm]))⟩
                            exact hQ true (kittenAssignStep ksU uip ucid) mFin hinvFin
                              (f_nv.trans (hpU.nv.trans (by rw [hst5_eq]; exact hbt_nv)))
                              (f_on.trans (hpU.orig_nc.trans (by rw [hst5_eq]; exact hbt_on)))
                              (f_an.trans (hpU.ante.trans (by rw [hst5_eq]; exact hbt_an)))
                              (f_na.trans (hpU.nassump.trans (by rw [hst5_eq]; exact hbt_na)))
                              (f_as.trans (hpU.assump.trans (by rw [hst5_eq]; exact hbt_as)))
                              (f_in.trans (hpU.incons.trans (by rw [hst5_eq]; exact hbt_in)))
                              (f_fa.trans (hpU.failing.trans (by rw [hst5_eq]; exact hbt_fa)))
                              (f_orig.trans (horigU.trans horig5))
                              (fun ci hci => (hci_u ci hci).1)
                              (fun ci hci => (hci_u ci hci).2)
                              (fun _ => ⟨hsyncFin, by rw [f_lvl_eq]; exact hj_lt, f_lvl_wit,
                                fun d hd => by
                                  rw [f_dec_eq] at hd; rw [f_lvl_eq]; exact hdec_ks d hd,
                                fun i hi hlv => by
                                  rw [f_lvl_eq] at hlv
                                  obtain ⟨hi_bt, ht_bt, hl_bt⟩ := hA2_bt i hi hlv
                                  obtain ⟨hi_f, ht_f, hl_f⟩ :=
                                    f_trl_old i (by rw [hpU.trl_end, hst5_eq]; exact hi_bt)
                                  rw [hpU.trl, hst5_eq] at ht_f
                                  rw [hpU.trl, hpU.lvlArr, hst5_eq, ht_bt] at hl_f
                                  exact ⟨hi_f, ht_f.trans ht_bt, hl_f.trans hl_bt⟩⟩) hmFin
                        · -- Phase 7: Multi-literal learned clause branch (`nkl ≥ 2`)
                          have hnkl_ne1 : stF.nkl ≠ 1#32 := by rw [← hkl0_nkl]; exact hc
                          have hnkl_ge2 : 2 ≤ stF.nkl.toNat := by
                            have h1 : 1 ≤ stF.nkl.toNat := by rw [hstF]; exact hBrk.nkl_pos
                            have hne : stF.nkl.toNat ≠ 1 := fun h =>
                              hnkl_ne1 (BitVec.eq_of_toNat_eq h)
                            omega
                          have hjlvl_pos : 0 < jlvl.toNat := (hi_ge2 hnkl_ge2).2.2.1
                          -- `group#6`: compute `nr = (ante != 0) ? nres : 0`
                          c0_hsteps_nogrp
                          refine wp_join_state_pure (ts := [i32]) (α := BitVec 32)
                            (fun nr => (nr, ()))
                            (fun nr => nr = (if st5.ante ≠ 0#32 then st5.nres else 0#32) ∧
                              nr.toNat ≤ kMaxL) ?_ ?_
                          · rintro J6 nr ⟨hnr_eq, hnr_le⟩
                            have hnr_256 : nr.toNat ≤ 256 := hnr_le
                            have hca5 : st5.acap.toNat = acap := by
                              rw [hinv5.clauses.acap_eq, BitVec.toNat_ofNat,
                                Nat.mod_eq_of_lt (by omega)]
                            have hsum_noov : (st5.alen + st5.nkl + nr).toNat =
                                st5.alen.toNat + st5.nkl.toNat + nr.toNat := by
                              have := hinv5.clauses.alen_le
                              have := hinv5.clauses.nkl_le; unfold kMaxV at this; bv_omega
                            c0_hsplit
                            · -- `nc >= 896` -> `return false`
                              c0_hsteps!
                              obtain ⟨_, hm5'⟩ := kittenMemA_to_mem hm5
                              exact hret_false st5 m5 hinv5 (by rw [hst5_eq]; exact hbt_nv)
                                (by rw [hst5_eq]; exact hbt_on) (by rw [hst5_eq]; exact hbt_an)
                                (by rw [hst5_eq]; exact hbt_na) (by rw [hst5_eq]; exact hbt_as)
                                (by rw [hst5_eq]; exact hbt_in) (by rw [hst5_eq]; exact hbt_fa)
                                horig5 (fun _ _ => by rw [hst5_eq, hbt_ca])
                                (fun _ _ => by rw [hst5_eq, hbt_cm]) hm5'
                            · have hnc_lt : st5.nc.toNat < kMaxCl := by
                                unfold kMaxCl; bv_omega
                              c0_hsplit
                              · -- `off + nkl + nr > cap` -> `return false`
                                c0_hsteps!
                                obtain ⟨_, hm5'⟩ := kittenMemA_to_mem hm5
                                exact hret_false st5 m5 hinv5 (by rw [hst5_eq]; exact hbt_nv)
                                  (by rw [hst5_eq]; exact hbt_on) (by rw [hst5_eq]; exact hbt_an)
                                  (by rw [hst5_eq]; exact hbt_na) (by rw [hst5_eq]; exact hbt_as)
                                  (by rw [hst5_eq]; exact hbt_in) (by rw [hst5_eq]; exact hbt_fa)
                                  horig5 (fun _ _ => by rw [hst5_eq, hbt_ca])
                                  (fun _ _ => by rw [hst5_eq, hbt_cm]) hm5'
                              · have hfit : st5.alen.toNat + st5.nkl.toNat + nr.toNat ≤ acap := by
                                  have hnk5 : st5.nkl = stF.nkl := by rw [hst5_eq]; exact hbt_nkl
                                  have h1 : ¬ st5.acap.toNat <
                                      (st5.alen.toNat + stF.nkl.toNat + nr.toNat) % 2 ^ 32 := hc
                                  rw [hca5, ← hnk5] at h1
                                  have := hinv5.clauses.alen_le
                                  have := hinv5.clauses.nkl_le; unfold kMaxV at this; omega
                                -- Copy loop 1 (`group#7`): `kl[0..nkl)` -> `arena[off..off+nkl)`
                                c0_hsteps_nogrp
                                refine wp_while_state1
                                  (fun p : BitVec 32 × List (BitVec 32) => p.1)
                                  (fun p => st5.nkl.toNat - p.1.toNat)
                                  (fun p m7 => p.1.toNat ≤ st5.nkl.toNat ∧ p.2.length = acap ∧
                                    (∀ k < st5.alen.toNat, p.2[k]? = st5.arena[k]?) ∧
                                    (∀ k < p.1.toNat, p.2[st5.alen.toNat + k]? = st5.kl[k]?) ∧
                                    (KittenMemA kPtr acap { st5 with arena := p.2 } ⋆ R) m7)
                                  ?_ ?_
                                · intro L7 hL7
                                  exact wp_jump_state
                                    (proj := fun p : BitVec 32 × List (BitVec 32) => (p.1, ()))
                                    (0#32, st5.arena) rfl
                                    (hL7 (0#32, st5.arena) m5 ⟨Nat.zero_le _, hsh5.arena_len,
                                      fun _ _ => rfl, fun _ h => by simp at h, by simpa using hm5⟩)
                                · rintro L7 ⟨i7, ar7⟩ m7
                                      ⟨hi7_le, har7_len, har7_old, har7_lits, hm7⟩ ih7
                                  dsimp only at hi7_le har7_len har7_old har7_lits hm7 ⊢
                                  obtain ⟨st7, hst7⟩ : ∃ x : KittenState,
                                      x = { st5 with arena := ar7 } := ⟨_, rfl⟩
                                  rw [← hst7] at hm7
                                  c0_hsplit
                                  · have hi7_lt : i7.toNat < st5.nkl.toNat := by
                                      have : st5.nkl = stKl0.nkl := by
                                        rw [hst5_eq, hbt_nkl, hkl0_nkl]
                                      rw [this]; exact hc
                                    have hi7_128 : i7.toNat < 128 := by
                                      have := hinv5.clauses.nkl_le; unfold kMaxV at this; omega
                                    have hi7_28 : i7.toNat < 2 ^ 28 := by omega
                                    have hoff7_cap : st5.alen.toNat + i7.toNat < acap := by omega
                                    have hoff7_28 : st5.alen.toNat + i7.toNat < 2 ^ 28 := by omega
                                    have hi7_1 : (i7 + 1#32).toNat = i7.toNat + 1 := by bv_omega
                                    c0_hsteps!
                                    let ar7' := ar7.set (st5.alen.toNat + i7.toNat)
                                      (st5.kl[i7.toNat]?.getD 0#32)
                                    refine ih7 (i7 + 1#32, ar7') _
                                      (by dsimp only; rw [hi7_1]; omega)
                                      ⟨by dsimp only; rw [hi7_1]; omega, by simp [ar7', har7_len],
                                       fun k hk => by
                                         rw [List.getElem?_set_ne (by omega)]; exact har7_old k hk,
                                       fun k hk => by
                                         rw [hi7_1] at hk
                                         by_cases hki : k = i7.toNat
                                         · subst hki
                                           rw [List.getElem?_set_self (by omega),
                                             List.getElem?_eq_getElem (by rw [hsh5.kl_len]; omega),
                                             Option.getD_some]
                                         · rw [List.getElem?_set_ne (by omega)]
                                           exact har7_lits k (by omega), ?_⟩
                                    refine Eq.mp (congrArg (fun x =>
                                      (KittenMemA kPtr acap x ⋆ R) _) ?_) hm
                                    rw [hst7]; kstate_ext <;> rfl
                                  · -- Exit copy loop 1 (`i7 == nkl`): Copy loop 2 (`group#8`)
                                    have hi7_eq : i7.toNat = st5.nkl.toNat := by
                                      have h1 : ¬ i7.toNat < stKl0.nkl.toNat := hc
                                      have h2 : st5.nkl = stKl0.nkl := by
                                        rw [hst5_eq, hbt_nkl, hkl0_nkl]
                                      rw [← h2] at h1; omega
                                    rw [hi7_eq] at har7_lits
                                    c0_hsteps_nogrp
                                    refine wp_while_state1
                                      (fun p : BitVec 32 × List (BitVec 32) => p.1)
                                      (fun p => nr.toNat - p.1.toNat)
                                      (fun p m8 => p.1.toNat ≤ nr.toNat ∧ p.2.length = acap ∧
                                        (∀ k < st5.alen.toNat, p.2[k]? = st5.arena[k]?) ∧
                                        (∀ k < st5.nkl.toNat,
                                          p.2[st5.alen.toNat + k]? = st5.kl[k]?) ∧
                                        (∀ k < p.1.toNat,
                                          p.2[st5.alen.toNat + st5.nkl.toNat + k]? = st5.res[k]?) ∧
                                        (KittenMemA kPtr acap { st5 with arena := p.2 } ⋆ R) m8)
                                      ?_ ?_
                                    · intro L8 hL8
                                      exact wp_jump_state
                                        (proj := fun p : BitVec 32 × List (BitVec 32) => (p.1, ()))
                                        (0#32, ar7) rfl
                                        (hL8 (0#32, ar7) m7 ⟨Nat.zero_le _, har7_len, har7_old,
                                          har7_lits, fun _ h => by simp at h, by rwa [← hst7]⟩)
                                    · rintro L8 ⟨i8, ar8⟩ m8
                                        ⟨hi8_le, har8_len, har8_old, har8_lits, har8_ants, hm8⟩ ih8
                                      dsimp only at hi8_le har8_len har8_old har8_lits
                                      dsimp only at har8_ants hm8 ⊢
                                      obtain ⟨st8, hst8⟩ : ∃ x : KittenState,
                                          x = { st5 with arena := ar8 } := ⟨_, rfl⟩
                                      rw [← hst8] at hm8
                                      c0_hsplit
                                      · have hi8_lt : i8.toNat < nr.toNat := hc
                                        have hi8_256 : i8.toNat < 256 := by omega
                                        have hi8_28 : i8.toNat < 2 ^ 28 := by omega
                                        have hnkl_st5 : stKl0.nkl = st5.nkl := by
                                          rw [hst5_eq, hbt_nkl, hkl0_nkl]
                                        have hoff8_cap :
                                            st5.alen.toNat + stKl0.nkl.toNat + i8.toNat < acap := by
                                          rw [hnkl_st5]; omega
                                        have hoff8_28 :
                                            st5.alen.toNat + stKl0.nkl.toNat + i8.toNat <
                                              2 ^ 28 := by
                                          omega
                                        have hi8_1 : (i8 + 1#32).toNat = i8.toNat + 1 := by bv_omega
                                        c0_hsteps!
                                        let ar8' := ar8.set
                                          (st5.alen.toNat + st5.nkl.toNat + i8.toNat)
                                          (st5.res[i8.toNat]?.getD 0#32)
                                        refine ih8 (i8 + 1#32, ar8') _
                                          (by dsimp only; rw [hi8_1]; omega)
                                          ⟨by dsimp only; rw [hi8_1]; omega,
                                           by simp [ar8', har8_len],
                                           fun k hk => by
                                             rw [List.getElem?_set_ne (by omega)]
                                             exact har8_old k hk,
                                           fun k hk => by
                                             rw [List.getElem?_set_ne (by omega)]
                                             exact har8_lits k hk,
                                           fun k hk => by
                                             rw [hi8_1] at hk
                                             by_cases hki : k = i8.toNat
                                             · subst hki
                                               rw [List.getElem?_set_self (by omega),
                                                 List.getElem?_eq_getElem
                                                   (by rw [hsh5.res_len]; omega), Option.getD_some]
                                             · rw [List.getElem?_set_ne (by omega)]
                                               exact har8_ants k (by omega), ?_⟩
                                        refine Eq.mp (congrArg (fun x =>
                                          (KittenMemA kPtr acap x ⋆ R) _) ?_) hm
                                        have hnkl_f : stF.nkl = st5.nkl := by rw [hst5_eq, hbt_nkl]
                                        rw [hst8]; kstate_ext <;>
                                          (first | rfl | (dsimp only [ar8']; rw [hnkl_f]))
                                      · -- Exit copy loop 2 (`i8 == nr`): meta, watch, assign!
                                        have hi8_eq : i8.toNat = nr.toNat := by
                                          have h1 : ¬ i8.toNat < nr.toNat := hc; omega
                                        rw [hi8_eq] at har8_ants
                                        have hkl5_lt : ∀ k < st5.nkl.toNat,
                                            (st5.kl[k]?.getD 0#32).toNat < 2 * st5.nv.toNat := by
                                          intro k hk
                                          rw [hst5_eq, hbtPres.nkl] at hk
                                          rw [hst5_eq, hbtPres.kl, hbtPres.nv]
                                          by_cases hk0 : k = 0
                                          · subst hk0; rw [hsw0, Option.getD_some, hpresSw.nv]
                                            exact huip_lt_k
                                          · exact (hsw_nt k (by omega) hk).1
                                        obtain ⟨hshM, hinvW, hsyncW, w_nc, w_nv, w_on, w_lvl,
                                          w_te, w_an, w_na, w_as, w_in, w_fa, w_tr, w_la, w_rs,
                                          w_va, w_orig, w_lits, w_ca_cm⟩ :=
                                          kana_append_lrn_inv hinv5 hsync5 hnc_lt
                                            (by rw [hst5_eq, hbt_nkl]; exact hnkl_ge2)
                                            (by rw [hst5_eq, hbt_nkl, hbt_nv, ← hpresF.nv, hstF]
                                                exact hBrk.nkl_le)
                                            hnr_eq hnr_le hfit har8_len har8_old har8_lits
                                            har8_ants hkl5_lt hF0_kl5 hres_kl5
                                        let stMeta : KittenState :=
                                          { st5 with
                                            arena := ar8, alen := st5.alen + st5.nkl + nr,
                                            clOff := st5.clOff.set st5.nc.toNat st5.alen,
                                            clMeta := st5.clMeta.set st5.nc.toNat
                                              (st5.nkl ||| kmLrn),
                                            clAux := st5.clAux.set st5.nc.toNat nr,
                                            nc := st5.nc + 1#32 }
                                        have hnc_896 : st5.nc.toNat < 896 := hnc_lt
                                        have hnc_28 : st5.nc.toNat < 2 ^ 28 := by omega
                                        have h1_128 : (1#32 : BitVec 32).toNat < 128 := by decide
                                        have h1_28 : (1#32 : BitVec 32).toNat < 2 ^ 28 := by decide
                                        c0_hsteps_nogrp
                                        obtain ⟨_, hmMeta⟩ := kittenMemA_to_mem hm
                                        have hmMeta' : (KittenMem kPtr stMeta ⋆ R) m := by
                                          refine Eq.mp (congrArg (fun x =>
                                            (KittenMem kPtr x ⋆ R) _) ?_) hmMeta
                                          rw [hst8]; have hnk_eq : stF.nkl = st5.nkl := by
                                            rw [hst5_eq, hbt_nkl]
                                          kstate_ext <;> (first | rfl | (rw [hnk_eq]; try rfl))
                                        c0_hcall hWatch
                                        refine ⟨acap, stMeta, R, hshM, hacap_lt,
                                          hinv5.clauses.nv_le, hnc_lt,
                                          (by dsimp only [Arg.val]; kp_field; rw [hst8]
                                              exact hkl5_lt 0 (by rw [hst5_eq, hbt_nkl]; omega)),
                                          (by dsimp only [Arg.val]; kp_field; rw [hst8]
                                              exact hkl5_lt 1 (by rw [hst5_eq, hbt_nkl]; omega)),
                                          hmMeta', fun mW hmW => ?_⟩
                                        let stW := kittenWatchStep stMeta st5.nc
                                          (st5.kl[0]?.getD 0#32) (st5.kl[1]?.getD 0#32)
                                        have hmW' : (KittenMem kPtr stW ⋆ R) mW := by
                                          refine Eq.mp (congrArg (fun x =>
                                            (KittenMem kPtr x ⋆ R) _) ?_) hmW
                                          dsimp only [stW, Arg.val]; kp_field; rw [hst8]; rfl
                                        c0_hsteps_nogrp
                                        c0_hcall hAssign
                                        refine ⟨acap, stW, R, hinvW.shapes, hacap_lt,
                                          hinvW.clauses.nv_le,
                                          by rw [w_nv, hst5_eq, hbt_nv]; exact huip_lt_k,
                                          by rw [w_te, w_nv, hst5_eq]; exact hte_lt_nv, hmW',
                                          fun mFin hmFin => ?_⟩
                                        c0_hsteps!
                                        dsimp only [Arg.val] at hmFin
                                        have hnc_ltW : st5.nc.toNat < stW.nc.toNat := by
                                          rw [w_nc]; unfold kMaxCl at hnc_lt; bv_omega
                                        have huip_inW : uip.toNat ∈ kittenClauseLits stW
                                            st5.nc.toNat := by
                                          rw [w_lits, hst5_eq, hbtPres.kl, hbt_nkl]
                                          have hk0_len : 0 < stSw.kl.length := by
                                            rw [hinvSw.shapes.kl_len]; decide
                                          have hk0 : (stSw.kl[0]?.getD 0#32).toNat ∈
                                              (stSw.kl.take stF.nkl.toNat).map BitVec.toNat := by
                                            rw [List.mem_map]
                                            refine ⟨stSw.kl[0]'hk0_len, ?_,
                                              by simp [List.getElem?_eq_getElem hk0_len]⟩
                                            rw [List.mem_take_iff_getElem]
                                            exact ⟨0, by omega, rfl⟩
                                          rwa [hsw0, Option.getD_some] at hk0
                                        have hothersW : ∀ x ∈ kittenClauseLits stW st5.nc.toNat,
                                            x ≠ uip.toNat → ∃ j < stW.trl_end.toNat,
                                              (stW.trl[j]?.getD 0#32).toNat = x ^^^ 1 := by
                                          intro x hx hne
                                          rw [w_lits, hst5_eq, hbtPres.kl, hbt_nkl,
                                            List.mem_map] at hx
                                          obtain ⟨b, hb, rfl⟩ := hx
                                          rw [List.mem_take_iff_getElem] at hb
                                          obtain ⟨k, hk, rfl⟩ := hb
                                          have hk_ne0 : k ≠ 0 := by
                                            intro hk0; subst hk0
                                            have h1 : stSw.kl[0]'(by omega) = uip :=
                                              Option.some.inj (by
                                                rw [← List.getElem?_eq_getElem (by omega), hsw0])
                                            exact hne (congrArg BitVec.toNat h1)
                                          have hnt_k := hsw_nt k (by omega) (by rw [hsw_nkl]; omega)
                                          dsimp only at hnt_k
                                          have hget :
                                              stSw.kl[k]?.getD 0#32 = stSw.kl[k]'(by omega) := by
                                            rw [List.getElem?_eq_getElem (by omega),
                                              Option.getD_some]
                                          rw [hget] at hnt_k
                                          rw [w_te, w_tr, hst5_eq]
                                          exact hkl_bt_trl _ (by rw [← hpresSw.nv]; exact hnt_k.1)
                                            hnt_k.2.2.2
                                            (by rw [← hpresSw.lvlArr]; exact hnt_k.2.2.1)
                                        obtain ⟨hinvFin, hsyncFin, f_nv, f_on, f_lvl, f_an, f_na,
                                          f_as, f_in, f_fa, f_orig, f_ca_cm, f_lvl_wit, f_dec,
                                          f_trl_old⟩ :=
                                          kana_assignStep_preserves_inv hinvW hsyncW
                                            (by rw [w_nv, hst5_eq, hbt_nv]; exact huip_lt_k)
                                            (by rw [w_te, w_nv, hst5_eq]; exact hte_lt_nv)
                                            (by rw [w_te, w_tr, hst5_eq]; exact huip_none)
                                            (by intro hff; have := congrArg BitVec.toNat hff
                                                unfold kMaxCl at hnc_lt
                                                have : (0xFFFFFFFF#32 : BitVec 32).toNat =
                                                    2 ^ 32 - 1 := by decide
                                                omega)
                                            hnc_ltW huip_inW hothersW
                                            (fun hl0 => by rw [w_lvl, hst5_eq, hlvlBt] at hl0
                                                           rw [hl0] at hjlvl_pos; simp at hjlvl_pos)
                                        have f_lvl_eq :
                                            (kittenAssignStep stW uip st5.nc).lvl = jlvl := by
                                          rw [f_lvl, w_lvl, hst5_eq, hlvlBt]
                                        have f_dec_eq :
                                            kittenTrailDecisions (kittenAssignStep stW uip st5.nc) =
                                              kittenTrailDecisions ksBt := by
                                          rw [f_dec]; unfold kittenTrailDecisions
                                          rw [w_tr, w_te, w_rs, hst5_eq]
                                        have hci_ca_cm : ∀ ci < ks.orig_nc.toNat,
                                            (kittenAssignStep stW uip st5.nc).clAux[ci]? =
                                              ks.clAux[ci]? ∧
                                            ((kittenAssignStep stW uip st5.nc).clMeta[ci]?.getD
                                              0#32 &&& kmCore) =
                                              (ks.clMeta[ci]?.getD 0#32 &&& kmCore) := by
                                          intro ci hci
                                          have h1 := f_ca_cm ci
                                            (by rw [w_on, hst5_eq, hbt_on]; exact hci)
                                          have h2 := w_ca_cm ci (by rw [hst5_eq, hbt_on]; exact hci)
                                          exact ⟨h1.1.trans (h2.1.trans (by rw [hst5_eq, hbt_ca])),
                                            h1.2.trans (h2.2.trans (by rw [hst5_eq, hbt_cm]))⟩
                                        exact hQ true (kittenAssignStep stW uip st5.nc) mFin hinvFin
                                          (f_nv.trans (w_nv.trans (by rw [hst5_eq]; exact hbt_nv)))
                                          (f_on.trans (w_on.trans (by rw [hst5_eq]; exact hbt_on)))
                                          (f_an.trans (w_an.trans (by rw [hst5_eq]; exact hbt_an)))
                                          (f_na.trans (w_na.trans (by rw [hst5_eq]; exact hbt_na)))
                                          (f_as.trans (w_as.trans (by rw [hst5_eq]; exact hbt_as)))
                                          (f_in.trans (w_in.trans (by rw [hst5_eq]; exact hbt_in)))
                                          (f_fa.trans (w_fa.trans (by rw [hst5_eq]; exact hbt_fa)))
                                          (f_orig.trans (w_orig.trans horig5))
                                          (fun ci hci => (hci_ca_cm ci hci).1)
                                          (fun ci hci => (hci_ca_cm ci hci).2)
                                          (fun _ => ⟨hsyncFin, by rw [f_lvl_eq]; exact hj_lt,
                                            f_lvl_wit,
                                            fun d hd => by
                                              rw [f_dec_eq] at hd; rw [f_lvl_eq]
                                              exact hdec_ks d hd,
                                            fun i hi hlv => by
                                              rw [f_lvl_eq] at hlv
                                              obtain ⟨hi_bt, ht_bt, hl_bt⟩ := hA2_bt i hi hlv
                                              obtain ⟨hi_f, ht_f, hl_f⟩ :=
                                                f_trl_old i (by rw [w_te, hst5_eq]; exact hi_bt)
                                              have htr_w : stW.trl = ksBt.trl := by
                                                rw [w_tr, hst5_eq]
                                              have hla_w : stW.lvlArr = ksBt.lvlArr := by
                                                rw [w_la, hst5_eq]
                                              have ht_f' :
                                                  (kittenAssignStep stW uip st5.nc).trl[i]? =
                                                    ks.trl[i]? :=
                                                ht_f.trans (by rw [htr_w, ht_bt])
                                              let v := (ks.trl[i]?.getD 0#32).toNat / 2
                                              have hl_f' :
                                                  (kittenAssignStep stW uip st5.nc).lvlArr[v]? =
                                                    ks.lvlArr[v]? := by
                                                rw [htr_w, hla_w, ht_bt] at hl_f
                                                exact hl_f.trans hl_bt
                                              exact ⟨hi_f, ht_f', hl_f'⟩⟩)
                                          hmFin
                          · -- `entry#6`: compute `nr = (ante != 0) ? nres : 0`
                            intro J6 hJ6
                            c0_hsteps!
                            · have ha5 : st5.ante ≠ 0#32 := hc
                              have hnr5 : st5.nres.toNat ≤ kMaxL := by
                                rw [hst5_eq, hbt_nres]
                                exact hante_nres
                                  (by rw [hst5_eq, hbtPres.ante, hpresSwF.ante] at ha5; exact ha5)
                              exact hJ6 st5.nres ⟨by rw [kana_ite_t ha5], hnr5⟩
                            · have ha5 : st5.ante = 0#32 := hc
                              exact hJ6 0#32 ⟨by rw [kana_ite_f (fun h => h ha5)],
                                by unfold kMaxL; decide⟩
                  · -- `entry#4`: conditional swap `if (nkl >= 2u && wi != 1u)`
                    intro J4 hJ4
                    have h1_128 : (1#32 : BitVec 32).toNat < 128 := by decide
                    have h1_28 : (1#32 : BitVec 32).toNat < 2 ^ 28 := by decide
                    c0_hsplit
                    · have hge2 : 2 ≤ stF.nkl.toNat := by rw [← hkl0_nkl]; bv_omega
                      have hwi_128 : wi.toNat < 128 := by
                        have := (hi_ge2 hge2).2.1; rw [hstF] at this; dsimp only at this; omega
                      have hwi_28 : wi.toNat < 2 ^ 28 := by omega
                      c0_hsplit
                      · have hwi_ne : wi ≠ 1#32 := hc
                        c0_hsteps!
                        refine hJ4 _ (Eq.mp (congrArg (fun x =>
                          (KittenMemA kPtr acap x ⋆ R) _) ?_) hm)
                        dsimp only [stSw]; rw [kana_ite_t ⟨hge2, hwi_ne⟩]; kstate_ext <;> rfl
                      · have hwi_eq : wi = 1#32 := hc
                        c0_hsteps!
                        refine hJ4 _ (Eq.mp (congrArg (fun x =>
                          (KittenMemA kPtr acap x ⋆ R) _) ?_) hm)
                        dsimp only [stSw]; rw [kana_ite_f (fun h => h.2 hwi_eq)]
                    · have hlt2 : ¬ 2 ≤ stF.nkl.toNat := by rw [← hkl0_nkl]; bv_omega
                      c0_hsteps!
                      refine hJ4 _ (Eq.mp (congrArg (fun x =>
                        (KittenMemA kPtr acap x ⋆ R) _) ?_) hm)
                      dsimp only [stSw]; rw [kana_ite_f (fun h => hlt2 h.1)]
            · -- `entry#2`: short-circuit `ante != 0 && nres > 256`
              intro J2 hJ2
              c0_hsplit
              · have haF : stF.ante ≠ 0#32 := hc
                c0_hsplit
                · c0_hsteps!
                  obtain ⟨_, hmF⟩ := kittenMemA_to_mem hmf
                  exact hret_false stF mf hinvF hpresF.nv hpresF.orig_nc hpresF.ante hpresF.nassump
                    hpresF.assump hpresF.incons hpresF.failing horigF
                    (fun _ _ => by rw [hpresF.clAux]) (fun _ _ => by rw [hpresF.clMeta]) hmF
                · have hnrF : stF.nres.toNat ≤ kMaxL := by unfold kMaxL; bv_omega
                  c0_hsteps!
                  exact hJ2 mf ⟨rfl, fun _ => hnrF⟩
              · have haF : stF.ante = 0#32 := hc
                c0_hsteps!
                exact hJ2 mf ⟨rfl, fun h => absurd haF h⟩
    · -- Phase 1 loop body (`J1_0(idx)`): `while (k[KH_STATUS] > 0u)`
      rintro B L ⟨idx, st⟩ ml hB hL ⟨hinvL, hpresL, hF0_L, hres_L, hml⟩
      dsimp only at hinvL hpresL hF0_L hres_L hml ⊢
      c0_hsplit
      · -- `status > 0`
        have hst_pos : 0 < st.status.toNat := by bv_omega
        c0_hsplit
        · -- `idx == 0` -> break with `uip = 0xFFFFFFFF`
          c0_hsteps!
          exact hB (idx, 0xFFFFFFFF#32, st) ml ⟨anaBrkPost_of_uip_ff hinvL hpresL, hml⟩
        · have hidx_pos : 0 < idx.toNat := by bv_omega
          have hidx' : (idx - 1#32).toNat = idx.toNat - 1 := by bv_omega
          have hidx_mod : (2 ^ 32 - (1 : BitVec 32).toNat + idx.toNat) % 2 ^ 32 =
              (idx - 1#32).toNat := by
            rw [hidx']; change (2 ^ 32 - 1 + idx.toNat) % 2 ^ 32 = idx.toNat - 1; omega
          have hidx'_te : (idx - 1#32).toNat < st.trl_end.toNat := by
            have := hinvL.idx_le; omega
          have hidx'_128 : (idx - 1#32).toNat < 128 := by
            have := hinvL.assign.trl_end_le; have := hinvL.nv_le; unfold kMaxV at this; omega
          have hidx'_28 : (idx - 1#32).toNat < 2 ^ 28 := by omega
          have htrl_lenL : st.trl_end.toNat ≤ st.trl.length := by
            rw [hinvL.shapes.trl_len]; have := hinvL.assign.trl_end_le; have := hinvL.nv_le
            unfold kMaxV at *; omega
          let p := st.trl[(idx - 1#32).toNat]?.getD 0#32
          have hp_lt : p.toNat < 2 * st.nv.toNat :=
            hinvL.assign.trl_lt _ (mem_kittenTrailLits_of_lt hidx'_te htrl_lenL)
          obtain ⟨hpv_eq, hpv_lt⟩ := bv32_lit_div2_bv hp_lt
          have hpv_128 : (p >>> 1).toNat < 128 := by
            have := hinvL.nv_le; unfold kMaxV at this; omega
          have hpv_28 : (p >>> 1).toNat < 2 ^ 28 := by omega
          have hidx_succ : (idx - 1#32).toNat + 1 = idx.toNat := by omega
          have hinvL' : KittenAnaInv acap st F0 ((idx - 1#32).toNat + 1) := by
            rwa [hidx_succ]
          c0_hsteps_nogrp
          -- `group#2`: join after `if ((flags & 2) != 0 && lvl == clvl)` -> jumps to `L(idx - 1)`
          refine wp_join_state1 (proj := fun _ : KittenState => 0xFFFFFFFF#32)
            (fun st' m2 => KittenAnaInv acap st' F0 (idx - 1#32).toNat ∧
              KittenAnaClausePreserved ks st' ∧
              (cnfOfClauses F0).EntailsClause
                (cnfClause (kittenResolventLits st' (idx - 1#32).toNat)) ∧
              (st'.ante ≠ 0#32 → st'.nres.toNat ≤ kMaxL →
                (∀ i < st'.nres.toNat, (st'.res[i]?.getD 0xFFFFFFFF#32).toNat < st'.nc.toNat) ∧
                (cnfOfClauses ((st'.res.take st'.nres.toNat).map fun c =>
                  kittenClauseLits st' c.toNat)).EntailsClause
                    (cnfClause (kittenResolventLits st' (idx - 1#32).toNat))) ∧
              (KittenMemA kPtr acap st' ⋆ R) m2)
            ?_ ?_
          · intro J2 st' m2 hst'
            c0_hsteps!
            exact hL (idx - 1#32, st') m2 (by dsimp only; omega) hst'
          · intro J2 hJ2
            c0_hsplit
            · -- `(flags[pv] & 2) != 0`
              have hfl_nz : (st.flags[p.toNat / 2]?.getD 0#32 &&& 2#32) ≠ 0#32 := by
                rw [hidx_mod] at hc; exact hc
              c0_hsplit
              · -- `lvlArr[pv] == clvl`: hit! decrement `status`
                have hlvl_hit : st.lvlArr[p.toNat / 2]?.getD 0#32 = st.lvl := by
                  rw [hidx_mod] at hc; rw [hpresL.lvl, ← hpres_k1.lvl]; exact hc
                let st1 : KittenState := { st with status := st.status - 1#32 }
                obtain ⟨_, hinv_s1, hpres_s1, hsub_s1⟩ :=
                  kana_resolvent_step_hit hinvL' ⟨hfl_nz, hlvl_hit⟩
                have hpres_ks1 : KittenAnaClausePreserved ks st1 :=
                  kana_anaClausePreserved_trans hpresL hpres_s1
                have hF0_s1 : (cnfOfClauses F0).EntailsClause
                    (cnfClause ((p.toNat ^^^ 1) :: kittenResolventLits st1 (idx - 1#32).toNat)) :=
                  kana_clause_entails_of_subset hsub_s1 (by rwa [hidx_succ])
                have hres_s1 : st1.ante ≠ 0#32 → st1.nres.toNat ≤ kMaxL →
                    (∀ i < st1.nres.toNat,
                      (st1.res[i]?.getD 0xFFFFFFFF#32).toNat < st1.nc.toNat) ∧
                    (cnfOfClauses ((st1.res.take st1.nres.toNat).map fun c =>
                      kittenClauseLits st1 c.toNat)).EntailsClause
                        (cnfClause ((p.toNat ^^^ 1) ::
                          kittenResolventLits st1 (idx - 1#32).toNat)) := by
                  intro ha1 hnr1
                  obtain ⟨hlt1, hent1⟩ := hres_L ha1 hnr1
                  exact ⟨hlt1, kana_clause_entails_of_subset hsub_s1 (by rwa [hidx_succ])⟩
                c0_hsplit
                · -- `status == 0`: 1UIP found! `uip = p ^ 1`, `break`!
                  have hst1_0 : st1.status = 0#32 := by
                    dsimp only [st1]; simp only [KittenState.putHdr] at hc; exact hc
                  have hm_s1 : (KittenMemA kPtr acap st1 ⋆ R) m := by
                    refine Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ R) _) ?_) hm
                    kstate_ext <;> rfl
                  have huip_eq := kana_uip_exit hinv_s1 hst1_0
                  obtain ⟨hnl_eq', hnl_lt⟩ := bv32_xor1_eq_litNeg hp_lt
                  have hnl_eq : (p ^^^ 1#32).toNat = p.toNat ^^^ 1 := by
                    rw [show (p ^^^ 1#32).toNat = litNeg p.toNat from hnl_eq', litNeg_eq_xor1]
                  c0_hsteps!
                  refine hB (idx - 1#32, p ^^^ 1#32, st1) m ⟨⟨hinv_s1.shapes, hpres_ks1,
                    hinv_s1.nres_le, hinv_s1.nkl_pos, hinv_s1.nkl_le, hinv_s1.nana_le,
                    hinv_s1.ana_lt, hinv_s1.flags_seen, fun _ => ?_⟩, hm_s1⟩
                  refine ⟨by dsimp only; rw [hnl_eq, litNeg_eq_xor1]; exact hnl_lt,
                    by dsimp only; rw [hnl_eq, kana_xor1_div2]; exact hlvl_hit,
                    fun i hi1 hi2 => let h := hinv_s1.kl_nonTop i hi1 hi2
                      ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩,
                    by dsimp only; rw [hnl_eq, ← huip_eq]; exact hF0_s1,
                    fun ha hnr => by dsimp only; rw [hnl_eq, ← huip_eq]; exact hres_s1 ha hnr⟩
                · -- `status != 0`: resolve with `rsn = k[KO_RSN + pv]`
                  have hst1_pos : 0 < st1.status.toNat := by
                    dsimp only [st1]; simp only [KittenState.putHdr] at hc; bv_omega
                  have hm_s1 : (KittenMemA kPtr acap st1 ⋆ R) m := by
                    refine Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ R) _) ?_) hm
                    kstate_ext <;> rfl
                  obtain ⟨_, _, _, hrsn_ne, hrsn_lt, hp_mem, hp_uniq, hothers⟩ :=
                    kana_rsn_pre hinv_s1 hidx'_te hst1_pos hlvl_hit
                  c0_hsplit
                  · -- `rsn == 0xFFFFFFFF`: dead code!
                    rw [hidx_mod] at hc; exact absurd hc hrsn_ne
                  · -- `rsn != 0xFFFFFFFF`: call `full_kitten_ana_clause(k, rsn, pv)`
                    obtain ⟨_, hm_s1m⟩ := kittenMemA_to_mem hm_s1
                    c0_hcall hAnaCl
                    refine ⟨acap, st1, F0, (idx - 1#32).toNat, R, hinv_s1, hrsn_lt,
                      Or.inr hpv_lt,
                      by rw [hpres_ks1.nv, hpres_ks1.lvlArr, hpres_ks1.lvl]; exact hvdec,
                      hothers, Or.inr ⟨p.toNat, hpv_eq.symm, hp_mem, hp_uniq, hF0_s1, hres_s1⟩,
                      hm_s1m, fun st2 m2 hinv2 hpres2 hF0_2 hres_2 hm2 => ?_⟩
                    c0_hsteps!
                    exact hJ2 st2 m2 ⟨hinv2, kana_anaClausePreserved_trans hpres_ks1 hpres2,
                      hF0_2, hres_2, kittenMem_to_amem hinv2.shapes hm2⟩
              · -- `lvlArr[pv] != clvl`: skip
                have hne_lv : st.lvlArr[p.toNat / 2]?.getD 0#32 ≠ st.lvl := by
                  rw [hidx_mod] at hc; rw [hpresL.lvl, ← hpres_k1.lvl]; exact hc
                obtain ⟨hinv_sk, hres_eq_sk⟩ :=
                  kana_resolvent_step_skip hinvL' (fun h => hne_lv h.2)
                rw [hidx_succ] at hres_eq_sk
                c0_hsteps!
                exact hJ2 st ml ⟨hinv_sk, hpresL, by rwa [← hres_eq_sk],
                  fun ha hnr => by rw [← hres_eq_sk]; exact hres_L ha hnr, hml⟩
            · -- `(flags[pv] & 2) == 0`: skip
              have hfl_0 : (st.flags[p.toNat / 2]?.getD 0#32 &&& 2#32) = 0#32 := by
                rw [hidx_mod] at hc; exact hc
              obtain ⟨hinv_sk, hres_eq_sk⟩ :=
                kana_resolvent_step_skip hinvL' (fun h => h.1 hfl_0)
              rw [hidx_succ] at hres_eq_sk
              c0_hsteps!
              exact hJ2 st ml ⟨hinv_sk, hpresL, by rwa [← hres_eq_sk],
                fun ha hnr => by rw [← hres_eq_sk]; exact hres_L ha hnr, hml⟩
      · -- `status == 0` at loop header -> break with `uip = 0xFFFFFFFF`
        c0_hsteps!
        exact hB (idx, 0xFFFFFFFF#32, st) ml ⟨anaBrkPost_of_uip_ff hinvL hpresL, hml⟩
    · -- Phase 1 loop entry: jump to `L(ks.trl_end)`
      intro B L _ hL
      exact wp_jump_state (proj := fun p : BitVec 32 × KittenState => (p.1, ()))
        (ks.trl_end, ks1) (by rw [hpres_k1.trl_end]; rfl)
        (hL (ks.trl_end, ks1) m1 ⟨hinv1, hpres_k1, hF0_1, hres_1, hm1A⟩)

end LeanQbe.T.Examples.Kissat.Full
