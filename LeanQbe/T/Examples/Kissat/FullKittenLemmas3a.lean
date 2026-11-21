module

public import LeanQbe.T.Examples.Kissat.FullKittenSpec1
public import LeanQbe.T.Examples.Kissat.FullKittenLemmas1

/-!
# Kissat `D-Full` Scratch `kitten` 2WL BCP: `full_kitten_propagate_wp` (`Part 3a`)

Proves `full_kitten_propagate` (`10/15`) against `fullKittenPropagateSpec`:
1. Private copies of the shared 2WL watch-chain cursor helpers (`WChainCursor`, keep/relocate
   preservation) and trail helpers from `FullKittenLemmas3` (kept `private` so both files can be
   imported together).
2. `PropFrame`: the entry-to-exit frame relation required by `fullKittenPropagateSpec`.
3. Invariant transfer across `full_kitten_learn_unit0` (`kittenUnit0_transfer`) and across a
   BCP `full_kitten_assign` with a falsified-others reason (`kittenPropAssign_preserves`).
4. `full_kitten_propagate_wp`: nested outer trail / inner watch-list / replacement-search loops.
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

/-! ## 1. Shared CNF, Trail, \& 2WL Watch-Chain Helpers (private copies) -/

/-- If `F` entails clause `c`, `u ∈ c`, and `F` entails `[x^1]` for every `x ∈ c` (`x ≠ u`),
then `F` entails unit `[u]`. -/
private theorem cnf_entails_unit_of_falsified_others {F : CNF Nat} {c : List Nat} {u : Nat}
    (hc : F.EntailsClause (cnfClause c)) (_hu : u ∈ c)
    (hothers : ∀ x ∈ c, x ≠ u → F.EntailsClause (cnfClause [litNeg x])) :
    F.EntailsClause (cnfClause [u]) := by
  rw [CNF.entails_clause_def]
  intro α hα
  obtain ⟨x, hx_mem, hxsat⟩ := (clause_sat_cnfClause_iff α c).mp
    (CNF.entails_clause_def.mp hc α hα)
  by_cases hxu : x = u
  · rw [hxu] at hxsat; exact (sat_cnfClause_singleton α u).mpr hxsat
  · have hneg := CNF.entails_clause_def.mp (hothers x hx_mem hxu) α hα
    exact absurd ((sat_cnfClause_singleton α x).mpr hxsat)
      ((sat_cnfClause_litNeg_iff α x).mp hneg)

private theorem list_nodup_subset_length {n : Nat} :
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
        have hmem_x := List.mem_of_mem_erase hx
        have hne : x ≠ k := fun h => by
          subst h; exact List.Nodup.not_mem_erase hnd hx
        have := hlt x hmem_x; omega
      have hle := ih hnd' hlt'
      have hlen := List.length_erase_of_mem hmem
      omega
    · have hle := ih hnd (fun x hx => by
        have := hlt x hx
        have hne : x ≠ k := fun heq => hmem (heq ▸ hx)
        omega)
      omega

private theorem list_nodup_mem_of_length_ge {n : Nat} {xs : List Nat}
    (hnd : xs.Nodup) (hlt : ∀ x ∈ xs, x < n) (hlen : n ≤ xs.length) {v : Nat} (hv : v < n) :
    v ∈ xs := by
  by_cases hmem : v ∈ xs
  · exact hmem
  · exfalso
    have h1 : (v :: xs).Nodup := List.nodup_cons.mpr ⟨hmem, hnd⟩
    have h2 : ∀ x ∈ (v :: xs), x < n := fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hv
      · exact hlt x hx'
    have hle := list_nodup_subset_length h1 h2
    simp at hle; omega

/-- If literal `l < 2 * nv` is unassigned (`vals[l] = 0`), then `trl_end < nv`. -/
private theorem trl_end_lt_of_unassigned {acap : Nat} {ks : KittenState}
    (hsh : ks.ShapesOk acap) (hnv : ks.nv.toNat ≤ kMaxV) (hba : KittenBaseAssignOk ks)
    {l : Nat} (hl : l < 2 * ks.nv.toNat) (h0 : ks.vals[l]? = some 0#32) :
    ks.trl_end.toNat < ks.nv.toNat := by
  have hle := hba.trl_end_le
  by_cases hlt : ks.trl_end.toNat < ks.nv.toNat
  · exact hlt
  · exfalso
    have heq : ks.trl_end.toNat = ks.nv.toNat := by omega
    have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
      rw [hsh.trl_len]; unfold kMaxV at hnv; omega
    let vs := (kittenTrailLits ks).map (· / 2)
    have hvs_nd : vs.Nodup := hba.trl_nodup
    have hvs_lt : ∀ x ∈ vs, x < ks.nv.toNat := by
      intro x hx; rw [List.mem_map] at hx; obtain ⟨t, ht, rfl⟩ := hx
      have := hba.trl_lt t ht; omega
    have hvs_len : ks.nv.toNat ≤ vs.length := by
      simp only [vs, kittenTrailLits, List.length_map, List.length_take]; omega
    have hv_mem := list_nodup_mem_of_length_ge hvs_nd hvs_lt hvs_len (v := l / 2) (by omega)
    rw [List.mem_map] at hv_mem
    obtain ⟨t, ht, htv⟩ := hv_mem
    unfold kittenTrailLits at ht
    rw [List.mem_map] at ht
    obtain ⟨bv, hbv, rfl⟩ := ht
    obtain ⟨i, hi, heq_bv⟩ := List.getElem_of_mem hbv
    have hi_te : i < ks.trl_end.toNat := by simp [List.length_take] at hi; omega
    have hi_trl : i < ks.trl.length := by omega
    simp only [List.getElem_take] at heq_bv
    have hnz : ks.vals[l]?.getD 0#32 ≠ 0#32 := (hba.vals_nz_iff_trl l hl).mpr ⟨i, hi_te, by
      rw [List.getElem?_eq_getElem hi_trl, Option.getD_some, heq_bv]; exact htv⟩
    rw [h0] at hnz; exact hnz rfl

/-- Updating only `prop` (`≤ trl_end`) and `ticks` preserves `Inv` and `TrailSynced`. -/
private theorem kittenBumpPropTicks_preserves_inv {acap : Nat} {ks : KittenState}
    (hinv : ks.Inv acap) (hsync : KittenTrailSynced ks) {pr' tk' : BitVec 32}
    (hpr : pr'.toNat ≤ ks.trl_end.toNat) :
    let ks' := (ks.putHdr .prop pr').putHdr .ticks tk'
    ks'.Inv acap ∧ KittenTrailSynced ks' := by
  intro ks'
  have hsh' : ks'.ShapesOk acap := (hinv.shapes.putHdr .prop pr').putHdr .ticks tk'
  have e_pr : ks'.prop = pr' := rfl; have e_nv : ks'.nv = ks.nv := rfl
  have e_nc : ks'.nc = ks.nc := rfl; have e_on : ks'.orig_nc = ks.orig_nc := rfl
  have e_lvl : ks'.lvl = ks.lvl := rfl; have e_te : ks'.trl_end = ks.trl_end := rfl
  have e_un : ks'.unass = ks.unass := rfl; have e_in : ks'.incons = ks.incons := rfl
  have e_fa : ks'.failing = ks.failing := rfl; have e_an : ks'.ante = ks.ante := rfl
  have e_al : ks'.alen = ks.alen := rfl; have e_ac : ks'.acap = ks.acap := rfl
  have e_na : ks'.nassump = ks.nassump := rfl; have e_nu : ks'.nunits = ks.nunits := rfl
  have e_nr : ks'.nres = ks.nres := rfl; have e_nk : ks'.nkl = ks.nkl := rfl
  have e_nn : ks'.nana = ks.nana := rfl; have e_la : ks'.lvlArr = ks.lvlArr := rfl
  have e_rs : ks'.rsn = ks.rsn := rfl; have e_tr : ks'.trl = ks.trl := rfl
  have e_fl : ks'.flags = ks.flags := rfl; have e_va : ks'.vals = ks.vals := rfl
  have e_as : ks'.assump = ks.assump := rfl; have e_un_a : ks'.units = ks.units := rfl
  have e_wh : ks'.whead = ks.whead := rfl; have e_wn : ks'.wnext = ks.wnext := rfl
  have e_wb : ks'.wblit = ks.wblit := rfl; have e_co : ks'.clOff = ks.clOff := rfl
  have e_cm : ks'.clMeta = ks.clMeta := rfl; have e_ca : ks'.clAux = ks.clAux := rfl
  have e_ar : ks'.arena = ks.arena := rfl
  have hba : KittenBaseAssignOk ks' :=
    ⟨by rw [e_te, e_nv]; exact hinv.assign.trl_end_le,
      by rw [e_pr, e_te]; exact hpr,
      by rw [e_un, e_te, e_nv]; exact hinv.assign.unass_eq,
      by rw [e_nv, e_va]; exact hinv.assign.vals_dom,
      by rw [e_nv, e_va]; exact hinv.assign.vals_neg_iff,
      by rw [e_nv, e_va, e_te, e_tr]; exact hinv.assign.vals_nz_iff_trl,
      by unfold kittenTrailLits; rw [e_te, e_tr]; exact hinv.assign.trl_nodup,
      by unfold kittenTrailLits; rw [e_nv, e_te, e_tr]; exact hinv.assign.trl_lt,
      by rw [e_nv, e_la, e_lvl]; exact hinv.assign.trl_lvl_le,
      by rw [e_nv, e_va, e_la, e_rs]; exact hinv.assign.unass_lvl_zero,
      by rw [e_te, e_la, e_tr]; exact hinv.assign.trl_lvl_mono,
      by rw [e_te, e_la, e_tr, e_rs]; exact hinv.assign.dec_earliest,
      by unfold kittenOrigClauses kittenClauseLits kittenClauseOff kittenClauseSize kittenClauseMeta
         rw [e_te, e_tr, e_la, e_rs, e_va, e_on, e_nc, e_an, e_co, e_cm, e_ar]
         exact hinv.assign.lvl0_ok⟩
  have hcl : KittenClausesOk acap ks' := by
    have h0 := hinv.clauses
    have hcm_eq : ∀ c, kittenClauseMeta ks' c = kittenClauseMeta ks c := fun _ => rfl
    have hsz_eq : ∀ c, kittenClauseSize ks' c = kittenClauseSize ks c := fun _ => rfl
    have his_eq : ∀ c, kittenClauseIsLrn ks' c = kittenClauseIsLrn ks c := fun _ => rfl
    have hoff_eq : ∀ c, kittenClauseOff ks' c = kittenClauseOff ks c := fun _ => rfl
    have hsp_eq : ∀ c, kittenClauseSpan ks' c = kittenClauseSpan ks c := fun _ => rfl
    have hlits_eq : ∀ c, kittenClauseLits ks' c = kittenClauseLits ks c := fun _ => rfl
    have hants_eq : ∀ c, kittenClauseAnts ks' c = kittenClauseAnts ks c := fun _ => rfl
    have horig_eq : kittenOrigClauses ks' = kittenOrigClauses ks :=
      kittenOrigClauses_eq_of e_on fun c _ => hlits_eq c
    refine ⟨h0.acap_ge, h0.acap_lt, by rw [e_ac]; exact h0.acap_eq,
      by rw [e_nv]; exact h0.nv_le, by rw [e_nc]; exact h0.nc_le,
      by rw [e_on, e_nc]; exact h0.orig_nc_le, by rw [e_on]; exact h0.orig_nc_max,
      by rw [e_al]; exact h0.alen_le, by rw [e_na]; exact h0.nassump_le,
      by rw [e_nu]; exact h0.nunits_le, by rw [e_nr]; exact h0.nres_le,
      by rw [e_nk]; exact h0.nkl_le, by rw [e_nn]; exact h0.nana_le, ?_, ?_, ?_,
      h0.incons_ok, h0.failing_ok, h0.assump_ok, h0.flags_clean⟩
    · intro c hc; rw [e_nc] at hc
      rw [his_eq, hsz_eq, hoff_eq, hsp_eq, hlits_eq, horig_eq, hants_eq,
        List.map_congr_left (fun a _ => hlits_eq a), e_on, e_al, e_nv, e_an]
      exact h0.cl_wf c hc
    · intro c1 c2 h12 h2; rw [e_nc] at h2
      rw [hoff_eq, hsp_eq, hoff_eq]; exact h0.cl_mono c1 c2 h12 h2
    · intro ui hui; rw [e_nu] at hui
      dsimp only; rw [e_un_a, e_nc, hsz_eq]; exact h0.units_ok ui hui
  exact ⟨⟨hsh', hcl, hinv.watches, hba, hinv.reasons⟩, hsync⟩

private theorem list_flatten_set_sub_perm {α : Type} (xs : List (List α)) {l : Nat}
    (hi : l < xs.length) (done todo' : List α) (w0 : α)
    (heq : xs[l]'hi = done ++ w0 :: todo') :
    xs.flatten.Perm (w0 :: (xs.set l (done ++ todo')).flatten) := by
  induction xs generalizing l with
  | nil => simp at hi
  | cons x tl ih =>
    cases l with
    | zero =>
      simp only [List.getElem_cons_zero] at heq
      simp only [List.set_cons_zero, List.flatten_cons, heq, List.append_assoc]
      exact List.perm_middle
    | succ l' =>
      simp only [List.getElem_cons_succ] at heq
      simp only [List.set_cons_succ, List.flatten_cons]
      exact ((ih (by simp at hi; omega) heq).append_left x).trans List.perm_middle

private theorem list_flatten_nodup_getElem {α : Type} :
    ∀ {xs : List (List α)}, xs.flatten.Nodup → ∀ {i : Nat} (hi : i < xs.length),
      (xs[i]'hi).Nodup ∧ ∀ j, j ≠ i → (hj : j < xs.length) → ∀ a ∈ xs[i]'hi, a ∉ xs[j]'hj
  | [], _, i, hi => absurd hi (by simp)
  | x :: tl, hnd, 0, hi => by
    simp only [List.flatten_cons] at hnd
    have ha := List.nodup_append.mp hnd
    refine ⟨ha.1, fun j hne hj a hai haj => ?_⟩
    cases j with
    | zero => exact hne rfl
    | succ j' =>
      have hj' : j' < tl.length := by simp at hj; exact hj
      simp only [List.getElem_cons_zero] at hai
      simp only [List.getElem_cons_succ] at haj
      exact ha.2.2 a hai a (List.mem_flatten.mpr ⟨tl[j'], List.getElem_mem hj', haj⟩) rfl
  | x :: tl, hnd, i + 1, hi => by
    simp only [List.flatten_cons] at hnd
    have ha := List.nodup_append.mp hnd
    have hi' : i < tl.length := by simp at hi; exact hi
    have ihr := list_flatten_nodup_getElem ha.2.1 hi'
    refine ⟨ihr.1, fun j hne hj a hai haj => ?_⟩
    cases j with
    | zero =>
      simp only [List.getElem_cons_succ] at hai
      simp only [List.getElem_cons_zero] at haj
      exact ha.2.2 a haj a (List.mem_flatten.mpr ⟨tl[i], List.getElem_mem hi', hai⟩) rfl
    | succ j' =>
      have hj' : j' < tl.length := by simp at hj; exact hj
      exact ihr.2 j' (fun h => hne (congrArg Nat.succ h)) hj' a hai haj

private theorem trl_nodup_var_ne' {acap : Nat} {ks : KittenState} (hsh : ks.ShapesOk acap)
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

/-- Unlinking node `w0` right after predecessor `u` in `WChain wn hd (pfx ++ u :: w0 :: todo')`
preserves `WChain` on `wn.set u wn[w0]`. -/
private theorem wchain_bypass {wn : List (BitVec 32)} {hd nxt : BitVec 32}
    {pfx : List Nat} {u w0 : Nat} {todo' : List Nat}
    (hc : WChain wn hd (pfx ++ u :: w0 :: todo'))
    (hnd : (pfx ++ u :: w0 :: todo').Nodup)
    (hu : u < wn.length) (hw0 : w0 < wn.length) (hnxt : wn[w0]'hw0 = nxt) :
    WChain (wn.set u nxt) hd (pfx ++ [u] ++ todo') := by
  induction pfx generalizing hd with
  | nil =>
    simp only [List.nil_append, List.singleton_append] at hc hnd ⊢
    rcases WChain_cases hc with ⟨_, hc_nil⟩ | ⟨u', ws1, hu', hhd, hcons, htail⟩
    · cases hc_nil
    · obtain ⟨hu_eq, hws1⟩ := List.cons.inj hcons
      subst hhd hu_eq hws1
      rcases WChain_cases htail with ⟨_, hnil⟩ | ⟨w', ws2, hw', hw_eq, hcons2, htail2⟩
      · cases hnil
      · obtain ⟨hw0_eq, hws2⟩ := List.cons.inj hcons2
        subst hw0_eq hws2
        have hnd_u : u ∉ w0 :: todo' := (List.nodup_cons.mp hnd).1
        have hu_nt : u ∉ todo' := fun h => hnd_u (List.mem_cons_of_mem _ h)
        have htail_congr : WChain (wn.set u nxt) nxt todo' := by
          rw [← hnxt]
          exact htail2.congr fun y hy =>
            (List.getElem?_set_ne (fun h : u = y => hu_nt (h ▸ hy))).symm
        have hus : u < (wn.set u nxt).length := by simp [hu]
        have hset_u : (wn.set u nxt)[u]'hus = nxt := by simp [List.getElem_set_self]
        exact WChain.cons hus (by rw [hset_u]; exact htail_congr)
  | cons x xs ih =>
    simp only [List.cons_append] at hc hnd ⊢
    rcases WChain_cases hc with ⟨_, hc_nil⟩ | ⟨x', ws1, hx', hhd, hcons, htail⟩
    · cases hc_nil
    · obtain ⟨hx_eq, hws1⟩ := List.cons.inj hcons
      subst hhd hx_eq hws1
      have hnd_x := List.nodup_cons.mp hnd
      have hxu : x ≠ u := fun h => hnd_x.1 (h ▸ List.mem_append_right xs List.mem_cons_self)
      have hxs_s : x < (wn.set u nxt).length := by simp [hx']
      have hset_x : (wn.set u nxt)[x]'hxs_s = wn[x]'hx' := List.getElem_set_ne hxu.symm hxs_s
      have ih' := ih htail hnd_x.2
      rw [← hset_x] at ih'
      exact WChain.cons hxs_s ih'

/-- Cursor invariant while traversing watch list `whead[l]` (`done ++ todo = chains[l]`). -/
private structure WChainCursor (ks : KittenState) (l : Nat) (chains : List (List Nat))
    (done todo : List Nat) (prev w : BitVec 32) : Prop where
  len_eq : chains.length = 2 * ks.nv.toNat
  nodup : chains.flatten.Nodup
  chain_l : chains[l]?.getD [] = done ++ todo
  chains_wc : ∀ x < 2 * ks.nv.toNat,
    WChain ks.wnext (ks.whead[x]?.getD 0xFFFFFFFF#32) (chains[x]?.getD [])
  chains_bnd : ∀ x < 2 * ks.nv.toNat, ∀ u ∈ chains[x]?.getD [],
    u < 2 * ks.nc.toNat ∧ 2 ≤ kittenClauseSize ks (u / 2) ∧
    (ks.arena[kittenClauseOff ks (u / 2) + (u % 2)]?.getD 0#32).toNat = x ∧
    (ks.wblit[u]?.getD 0#32).toNat < 2 * ks.nv.toNat
  tail_wc : WChain ks.wnext w todo
  prev_rel : (done = [] ∧ prev = 0xFFFFFFFF#32 ∧ ks.whead[l]?.getD 0xFFFFFFFF#32 = w) ∨
    (∃ pfx u, done = pfx ++ [u] ∧ prev = BitVec.ofNat 32 u ∧
      u < ks.wnext.length ∧ ks.wnext[u]?.getD 0xFFFFFFFF#32 = w)

private theorem WChainCursor.watchesOk {ks : KittenState} {l : Nat} {chains : List (List Nat)}
    {done todo : List Nat} {prev w : BitVec 32}
    (wc : WChainCursor ks l chains done todo prev w) : KittenWatchesOk ks :=
  ⟨chains, wc.len_eq, wc.nodup, wc.chains_wc, wc.chains_bnd⟩

private theorem WChainCursor.init {acap : Nat} {ks : KittenState} (hsh : ks.ShapesOk acap)
    (hnv : ks.nv.toNat ≤ kMaxV) (hw : KittenWatchesOk ks) {l : Nat} (hl : l < 2 * ks.nv.toNat) :
    ∃ chains, WChainCursor ks l chains [] (chains[l]?.getD []) 0xFFFFFFFF#32
      (ks.whead[l]?.getD 0#32) := by
  obtain ⟨chains, hlen, hnd, hwc, hbnd⟩ := hw
  have hwh_len : l < ks.whead.length := by rw [hsh.whead_len]; unfold kMaxV at hnv; omega
  have hwh_eq : ks.whead[l]?.getD 0#32 = ks.whead[l]?.getD 0xFFFFFFFF#32 := by
    rw [List.getElem?_eq_getElem hwh_len]; rfl
  rw [hwh_eq]
  exact ⟨chains, hlen, hnd, rfl, hwc, hbnd, hwc l hl, Or.inl ⟨rfl, rfl, rfl⟩⟩

private theorem WChainCursor.step_unfold {acap : Nat} {ks : KittenState} (_hsh : ks.ShapesOk acap)
    (hnc : ks.nc.toNat ≤ kMaxCl) {l : Nat} (hl : l < 2 * ks.nv.toNat)
    {chains : List (List Nat)} {done todo : List Nat} {prev w : BitVec 32}
    (wc : WChainCursor ks l chains done todo prev w) (hne : w ≠ 0xFFFFFFFF#32) :
    ∃ w0 todo', w0 < ks.wnext.length ∧
      todo = w0 :: todo' ∧ w = BitVec.ofNat 32 w0 ∧ w0 < 2 * ks.nc.toNat ∧ w0 < 1792 ∧
      w.toNat = w0 ∧ (w >>> (1 : Nat)).toNat = w0 / 2 ∧ (w &&& 1#32).toNat = w0 % 2 ∧
      2 ≤ kittenClauseSize ks (w0 / 2) ∧
      (ks.arena[kittenClauseOff ks (w0 / 2) + (w0 % 2)]?.getD 0#32).toNat = l ∧
      (ks.wblit[w0]?.getD 0#32).toNat < 2 * ks.nv.toNat ∧
      WChain ks.wnext (ks.wnext[w0]?.getD 0#32) todo' := by
  obtain ⟨w0, todo', hw0, htd, hw_eq, htail⟩ := WChain_getElem_of_eq wc.tail_wc hne
  have hm_l : w0 ∈ chains[l]?.getD [] := by
    rw [wc.chain_l, htd]; exact List.mem_append_right _ List.mem_cons_self
  have hb := wc.chains_bnd l hl w0 hm_l
  have hw0_1792 : w0 < 1792 := by unfold kMaxCl at hnc; omega
  have hw_tn : w.toNat = w0 := by
    rw [hw_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hw_div2 : (w >>> (1 : Nat)).toNat = w0 / 2 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one, hw_tn]
  have hw_mod2 : (w &&& 1#32).toNat = w0 % 2 := by
    rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod w.toNat 1, hw_tn]
  have hnxt_eq : ks.wnext[w0]?.getD 0#32 = ks.wnext[w0]'hw0 := by
    rw [List.getElem?_eq_getElem hw0, Option.getD_some]
  refine ⟨w0, todo', hw0, htd, hw_eq, hb.1, hw0_1792, hw_tn, hw_div2, hw_mod2,
    hb.2.1, hb.2.2.1, hb.2.2.2, ?_⟩
  rw [hnxt_eq]; exact htail

/-- Updating `wblit[w0] := other` keeps node `w0` on list `l` and advances `(prev, w)` to
`(w, nxt)`. -/
private theorem kittenWatchKeep_preserves {acap : Nat} {ks : KittenState}
    (hsh : ks.ShapesOk acap) (hinv : ks.Inv acap) (hsync : KittenTrailSynced ks)
    {l : Nat} (hl : l < 2 * ks.nv.toNat) {chains : List (List Nat)}
    {done todo' : List Nat} {prev : BitVec 32} {w0 : Nat}
    (wc : WChainCursor ks l chains done (w0 :: todo') prev (BitVec.ofNat 32 w0))
    {other : BitVec 32} (hoth : other.toNat < 2 * ks.nv.toNat) :
    let w := BitVec.ofNat 32 w0
    let nxt := ks.wnext[w0]?.getD 0#32
    let ks' := ks.putArr .wblit w0 other
    ks'.Inv acap ∧ KittenTrailSynced ks' ∧
    WChainCursor ks' l chains (done ++ [w0]) todo' w nxt ∧
    ks'.nv = ks.nv ∧ ks'.nc = ks.nc ∧ ks'.orig_nc = ks.orig_nc ∧ ks'.lvl = ks.lvl ∧
    ks'.prop = ks.prop ∧ ks'.trl_end = ks.trl_end ∧ ks'.unass = ks.unass ∧
    ks'.incons = ks.incons ∧ ks'.failing = ks.failing ∧ ks'.ante = ks.ante ∧
    ks'.nassump = ks.nassump ∧ ks'.assump = ks.assump ∧ ks'.vals = ks.vals ∧
    ks'.lvlArr = ks.lvlArr ∧ ks'.rsn = ks.rsn ∧ ks'.trl = ks.trl ∧
    ks'.clOff = ks.clOff ∧ ks'.clMeta = ks.clMeta ∧ ks'.clAux = ks.clAux ∧
    ks'.arena = ks.arena := by
  intro w nxt ks'
  have hsh' : ks'.ShapesOk acap := hsh.putArr .wblit w0 other
  have hnc := hinv.clauses.nc_le
  have hm_l : w0 ∈ chains[l]?.getD [] := by
    rw [wc.chain_l]; exact List.mem_append_right _ List.mem_cons_self
  have hb0 := wc.chains_bnd l hl w0 hm_l
  have hw0_nc : w0 < 2 * ks.nc.toNat := hb0.1
  have hwb_len : w0 < ks.wblit.length := by rw [hsh.wblit_len]; unfold kMaxCl at hnc; omega
  have hwn_len : w0 < ks.wnext.length := by rw [hsh.wnext_len]; unfold kMaxCl at hnc; omega
  have hnxt_eq : ks.wnext[w0]?.getD 0#32 = ks.wnext[w0]?.getD 0xFFFFFFFF#32 := by
    rw [List.getElem?_eq_getElem hwn_len]; rfl
  rcases WChain_cases wc.tail_wc with ⟨_, hnil⟩ | ⟨w0', todo'', hw0', hw_eq, hcons, htail'⟩
  · cases hnil
  · obtain ⟨_, htd_eq⟩ := List.cons.inj hcons
    subst htd_eq
    have hw0_eq : w0 = w0' := by
      have ht := congrArg BitVec.toNat hw_eq
      have h1 : w0 < 2 ^ 32 := by unfold kMaxCl at hnc; omega
      have hwn' : w0' < 1792 := by rw [hsh.wnext_len] at hw0'; exact hw0'
      have h2 : w0' < 2 ^ 32 := by omega
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at ht
      exact ht
    subst hw0_eq
    have wc' : WChainCursor ks' l chains (done ++ [w0]) todo' w nxt := by
      refine ⟨wc.len_eq, wc.nodup, ?_, wc.chains_wc, ?_, ?_, Or.inr ⟨done, w0, rfl, rfl,
        hwn_len, hnxt_eq.symm⟩⟩
      · rw [wc.chain_l]; simp
      · intro x hx u hu
        have hbu := wc.chains_bnd x hx u hu
        by_cases hu0 : u = w0
        · rw [hu0] at hbu; rw [hu0]; exact ⟨hbu.1, hbu.2.1, hbu.2.2.1, by
            change ((ks.wblit.set w0 other)[w0]?.getD 0#32).toNat < 2 * ks.nv.toNat
            rw [List.getElem?_set_self hwb_len, Option.getD_some]; exact hoth⟩
        · exact ⟨hbu.1, hbu.2.1, hbu.2.2.1, by
            change ((ks.wblit.set w0 other)[u]?.getD 0#32).toNat < 2 * ks.nv.toNat
            rw [List.getElem?_set_ne (Ne.symm hu0)]; exact hbu.2.2.2⟩
      · change WChain ks.wnext nxt todo'
        have hget : nxt = ks.wnext[w0]'hw0' := by
          dsimp only [nxt]; rw [List.getElem?_eq_getElem hw0', Option.getD_some]
        rw [hget]; exact htail'
    let c := hinv.clauses; let a := hinv.assign
    have hcl' : KittenClausesOk acap ks' :=
      ⟨c.acap_ge, c.acap_lt, c.acap_eq, c.nv_le, c.nc_le, c.orig_nc_le, c.orig_nc_max,
        c.alen_le, c.nassump_le, c.nunits_le, c.nres_le, c.nkl_le, c.nana_le, c.cl_wf,
        c.cl_mono, c.units_ok, c.incons_ok, c.failing_ok, c.assump_ok, c.flags_clean⟩
    have hba' : KittenBaseAssignOk ks' :=
      ⟨a.trl_end_le, a.prop_le, a.unass_eq, a.vals_dom, a.vals_neg_iff, a.vals_nz_iff_trl,
        a.trl_nodup, a.trl_lt, a.trl_lvl_le, a.unass_lvl_zero, a.trl_lvl_mono, a.dec_earliest,
        a.lvl0_ok⟩
    exact ⟨⟨hsh', hcl', wc'.watchesOk, hba', hinv.reasons⟩, hsync, wc',
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl⟩

/-- Unlinking node `w0` (`slot = w0 % 2`) from watch list `l`, swapping `arena[off+slot] ↔
arena[off+ri]` (`ri ≥ 2`), and prepending `w0` to `whead[repl]` preserves `KittenInv`,
`KittenTrailSynced`, perm-equivalent clauses, and advances the cursor to `(prev, nxt)`. -/
private theorem kittenWatchReloc_preserves {acap : Nat} {ks : KittenState}
    (hsh : ks.ShapesOk acap) (hinv : ks.Inv acap) (hsync : KittenTrailSynced ks)
    {l : Nat} (hl : l < 2 * ks.nv.toNat) {chains : List (List Nat)}
    {done todo' : List Nat} {prev : BitVec 32} {w0 : Nat}
    (wc : WChainCursor ks l chains done (w0 :: todo') prev (BitVec.ofNat 32 w0))
    {ri : Nat} (hri_ge : 2 ≤ ri) (hri_lt : ri < kittenClauseSize ks (w0 / 2))
    {repl other : BitVec 32} (hrepl_ne : repl.toNat ≠ l)
    (hother_eq : other = ks.arena[kittenClauseOff ks (w0 / 2) + ((w0 % 2) ^^^ 1)]?.getD 0#32)
    (hrepl_eq : repl = ks.arena[kittenClauseOff ks (w0 / 2) + ri]?.getD 0#32) :
    let w := BitVec.ofNat 32 w0
    let nxt := ks.wnext[w0]?.getD 0#32
    let cid := w0 / 2
    let slot := w0 % 2
    let off := kittenClauseOff ks cid
    let ar' := (ks.arena.set (off + slot) repl).set (off + ri) (BitVec.ofNat 32 l)
    let wh1 := if prev = 0xFFFFFFFF#32 then ks.whead.set l nxt else ks.whead
    let wn1 := if prev = 0xFFFFFFFF#32 then ks.wnext else ks.wnext.set prev.toNat nxt
    let ks1 : KittenState := { ks with arena := ar', whead := wh1, wnext := wn1 }
    let ks' := kittenWatchStep0 ks1 w repl other
    ks'.Inv acap ∧ KittenTrailSynced ks' ∧
    (∀ c < ks.nc.toNat, (kittenClauseLits ks' c).Perm (kittenClauseLits ks c)) ∧
    (∀ c < ks.nc.toNat, c ≠ cid → kittenClauseLits ks' c = kittenClauseLits ks c) ∧
    (∀ c < ks.nc.toNat, kittenClauseAnts ks' c = kittenClauseAnts ks c) ∧
    KittenCnfPermEquiv (kittenOrigClauses ks') (kittenOrigClauses ks) ∧
    (∃ chains', WChainCursor ks' l chains' done todo' prev nxt) ∧
    ks'.nv = ks.nv ∧ ks'.nc = ks.nc ∧ ks'.orig_nc = ks.orig_nc ∧ ks'.lvl = ks.lvl ∧
    ks'.prop = ks.prop ∧ ks'.trl_end = ks.trl_end ∧ ks'.unass = ks.unass ∧
    ks'.incons = ks.incons ∧ ks'.failing = ks.failing ∧ ks'.ante = ks.ante ∧
    ks'.nassump = ks.nassump ∧ ks'.assump = ks.assump ∧ ks'.vals = ks.vals ∧
    ks'.lvlArr = ks.lvlArr ∧ ks'.rsn = ks.rsn ∧ ks'.trl = ks.trl ∧
    ks'.clOff = ks.clOff ∧ ks'.clMeta = ks.clMeta ∧ ks'.clAux = ks.clAux ∧
    ks'.flags = ks.flags := by
  intro w nxt cid slot off ar' wh1 wn1 ks1 ks'
  have hnv := hinv.clauses.nv_le
  have hnc := hinv.clauses.nc_le
  have hch_l : l < chains.length := by rw [wc.len_eq]; exact hl
  have hm_l : w0 ∈ chains[l]?.getD [] := by
    rw [wc.chain_l]; exact List.mem_append_right _ List.mem_cons_self
  have hb0 := wc.chains_bnd l hl w0 hm_l
  have hcid_lt : cid < ks.nc.toNat := by dsimp only [cid]; omega
  have hwf_c := hinv.clauses.cl_wf cid hcid_lt
  have hri_lt' : ri < kittenClauseSize ks cid := hri_lt
  have hsz_ge : 2 ≤ kittenClauseSize ks cid := hb0.2.1
  have hslot_lt : slot < 2 := Nat.mod_lt w0 (by decide)
  have hother_slot_lt : (slot ^^^ 1) < 2 := by
    rcases Nat.mod_two_eq_zero_or_one w0 with h | h <;> simp [slot, h]
  have hoff_le : off + kittenClauseSpan ks cid ≤ ks.alen.toNat := hwf_c.2.2.1
  have hsp_ge : kittenClauseSize ks cid ≤ kittenClauseSpan ks cid := by
    unfold kittenClauseSpan; omega
  have har_len : ks.arena.length = acap := hsh.arena_len
  have hal_le : ks.alen.toNat ≤ acap := hinv.clauses.alen_le
  have hwn_len : w0 < ks.wnext.length := by rw [hsh.wnext_len]; unfold kMaxCl at hnc; omega
  have hwh_len : l < ks.whead.length := by rw [hsh.whead_len]; unfold kMaxV at hnv; omega
  have hnxt_eq : nxt = ks.wnext[w0]'hwn_len := by
    dsimp only [nxt]; rw [List.getElem?_eq_getElem hwn_len, Option.getD_some]
  have har_slot : ks.arena[off + slot]'(by dsimp only [off]; omega) = BitVec.ofNat 32 l := by
    have ha := hb0.2.2.1
    rw [List.getElem?_eq_getElem (by dsimp only [off]; omega : off + slot < ks.arena.length),
      Option.getD_some] at ha
    exact BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold kMaxV at hnv; omega)]; exact ha)
  have hrepl_lt_ar : off + ri < ks.arena.length := by dsimp only [off]; omega
  have hrepl_mem : repl.toNat ∈ kittenClauseLits ks cid := by
    rw [hrepl_eq]
    change (ks.arena[kittenClauseOff ks cid + ri]?.getD 0#32).toNat ∈ kittenClauseLits ks cid
    rw [List.getElem?_eq_getElem hrepl_lt_ar, Option.getD_some]
    unfold kittenClauseLits; rw [List.mem_map]
    refine ⟨ks.arena[off + ri]'hrepl_lt_ar, ?_, rfl⟩
    rw [List.mem_iff_getElem]
    dsimp only [off] at hrepl_lt_ar hoff_le
    exact ⟨ri, by simp [List.length_take, List.length_drop, har_len]; omega,
      by dsimp only [off]; simp [List.getElem_take, List.getElem_drop]⟩
  have hrepl_nv : repl.toNat < 2 * ks.nv.toNat := hwf_c.2.2.2.1 _ hrepl_mem
  have hother_lt_ar : off + (slot ^^^ 1) < ks.arena.length := by dsimp only [off]; omega
  have hother_mem : other.toNat ∈ kittenClauseLits ks cid := by
    rw [hother_eq]
    change (ks.arena[kittenClauseOff ks cid + (slot ^^^ 1)]?.getD 0#32).toNat ∈
      kittenClauseLits ks cid
    rw [List.getElem?_eq_getElem hother_lt_ar, Option.getD_some]
    unfold kittenClauseLits; rw [List.mem_map]
    refine ⟨ks.arena[off + (slot ^^^ 1)]'hother_lt_ar, ?_, rfl⟩
    rw [List.mem_iff_getElem]
    dsimp only [off] at hother_lt_ar hoff_le
    exact ⟨slot ^^^ 1, by
        simp [List.length_take, List.length_drop, har_len]; omega,
      by dsimp only [off]; simp [List.getElem_take, List.getElem_drop]⟩
  have hother_nv : other.toNat < 2 * ks.nv.toNat := hwf_c.2.2.2.1 _ hother_mem
  have har'_eq : ar' = (ks.arena.set (off + slot) (ks.arena[off + ri]'hrepl_lt_ar)).set
      (off + ri) (ks.arena[off + slot]'(by dsimp only [off]; omega)) := by
    dsimp only [ar']
    rw [har_slot, hrepl_eq]
    change (ks.arena.set (off + slot) (ks.arena[off + ri]?.getD 0#32)).set (off + ri) _ = _
    rw [List.getElem?_eq_getElem hrepl_lt_ar, Option.getD_some]
  have hsh1 : ks1.ShapesOk acap := by
    refine ⟨hsh.hdrTail_len, hsh.lvlArr_len, hsh.rsn_len, hsh.qprev_len, hsh.qnext_len,
      hsh.qstampArr_len, hsh.trl_len, hsh.flags_len, hsh.vals_len, hsh.assump_len, hsh.ana_len,
      hsh.kl_len, hsh.units_len, hsh.res_len, ?_, ?_, hsh.wblit_len, hsh.clOff_len,
      hsh.clMeta_len, hsh.clAux_len, ?_⟩
    · dsimp only [ks1, wh1]; split <;> simp [List.length_set, hsh.whead_len]
    · dsimp only [ks1, wn1]; split <;> simp [List.length_set, hsh.wnext_len]
    · simp [ks1, ar', List.length_set, hsh.arena_len]
  have hsh' : ks'.ShapesOk acap := kittenWatchStep0_preserves_shapes hsh1 w repl other
  have hlits_other :
      ∀ c < ks.nc.toNat, c ≠ cid → kittenClauseLits ks' c = kittenClauseLits ks c := by
    intro c hclt hcne
    change kittenClauseLits ks1 c = kittenClauseLits ks c
    unfold kittenClauseLits
    change ((ar'.drop (kittenClauseOff ks c)).take (kittenClauseSize ks c)).map BitVec.toNat =
      ((ks.arena.drop (kittenClauseOff ks c)).take (kittenClauseSize ks c)).map BitVec.toNat
    have hout : ∀ idx, idx = off + slot ∨ idx = off + ri →
        idx < kittenClauseOff ks c ∨ kittenClauseOff ks c + kittenClauseSize ks c ≤ idx := by
      intro idx hidx
      by_cases hcl : c < cid
      · right
        have hm := hinv.clauses.cl_mono c cid hcl hcid_lt
        have hsp := show kittenClauseSize ks c ≤ kittenClauseSpan ks c by
          unfold kittenClauseSpan; omega
        change kittenClauseOff ks c + kittenClauseSpan ks c ≤ off at hm
        dsimp only [off] at hm ⊢
        rcases hidx with rfl | rfl <;> omega
      · left
        have hm := hinv.clauses.cl_mono cid c (by omega) hclt
        change off + kittenClauseSpan ks cid ≤ kittenClauseOff ks c at hm
        dsimp only [off] at hm ⊢
        rcases hidx with rfl | rfl <;> omega
    dsimp only [ar']
    rw [drop_take_set_out _ _ (hout _ (Or.inr rfl)),
      drop_take_set_out _ _ (hout _ (Or.inl rfl))]
  have hlits_perm_all : ∀ c < ks.nc.toNat,
      (kittenClauseLits ks' c).Perm (kittenClauseLits ks c) := by
    intro c hclt
    by_cases hccid : c = cid
    · subst hccid
      change (kittenClauseLits ks1 cid).Perm (kittenClauseLits ks cid)
      unfold kittenClauseLits
      change (((ar'.drop off).take (kittenClauseSize ks cid)).map BitVec.toNat).Perm
        (((ks.arena.drop off).take (kittenClauseSize ks cid)).map BitVec.toNat)
      rw [har'_eq]
      exact (drop_take_set_swap ks.arena (off := off) (sz := kittenClauseSize ks cid)
        (p := slot) (q := ri) (by omega) hri_lt' (by dsimp only [off]; omega)).map _
    · rw [hlits_other c hclt hccid]
  have hants_all : ∀ c < ks.nc.toNat, kittenClauseAnts ks' c = kittenClauseAnts ks c := by
    intro c hclt
    change kittenClauseAnts ks1 c = kittenClauseAnts ks c
    unfold kittenClauseAnts
    change (if kittenClauseIsLrn ks c then
        ((ar'.drop (kittenClauseOff ks c + kittenClauseSize ks c)).take
          (kittenClauseAux ks c)).map BitVec.toNat else [c]) = _
    split
    · have hout : ∀ idx, idx = off + slot ∨ idx = off + ri →
          idx < kittenClauseOff ks c + kittenClauseSize ks c ∨
            kittenClauseOff ks c + kittenClauseSize ks c + kittenClauseAux ks c ≤ idx := by
        intro idx hidx
        by_cases hcc : c = cid
        · subst hcc; left; dsimp only [off] at hidx; rcases hidx with rfl | rfl <;> omega
        · by_cases hcl : c < cid
          · right
            have hm := hinv.clauses.cl_mono c cid hcl hcid_lt
            have : kittenClauseSize ks c + kittenClauseAux ks c ≤ kittenClauseSpan ks c := by
              unfold kittenClauseSpan; simp [*]
            change kittenClauseOff ks c + kittenClauseSpan ks c ≤ off at hm
            dsimp only [off] at hm ⊢
            rcases hidx with rfl | rfl <;> omega
          · left
            have hm := hinv.clauses.cl_mono cid c (by omega) hclt
            change off + kittenClauseSpan ks cid ≤ kittenClauseOff ks c at hm
            dsimp only [off] at hm ⊢
            rcases hidx with rfl | rfl <;> omega
      dsimp only [ar']
      rw [drop_take_set_out _ _ (hout _ (Or.inr rfl)),
        drop_take_set_out _ _ (hout _ (Or.inl rfl))]
    · rfl
  have e_on : ks'.orig_nc = ks.orig_nc := rfl
  have e_nc : ks'.nc = ks.nc := rfl
  have e_nv : ks'.nv = ks.nv := rfl
  have e_cm : ∀ c, kittenClauseMeta ks' c = kittenClauseMeta ks c := fun _ => rfl
  have horig_perm : KittenCnfPermEquiv (kittenOrigClauses ks') (kittenOrigClauses ks) := by
    refine ⟨by simp [kittenOrigClauses, e_on], fun i hi => ?_⟩
    unfold kittenOrigClauses at hi ⊢
    simp only [List.length_map, List.length_range] at hi
    rw [e_on] at hi
    rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD]
    have hl1 : i < ((List.range ks'.orig_nc.toNat).map (kittenClauseLits ks')).length := by
      simp [e_on, hi]
    have hl2 : i < ((List.range ks.orig_nc.toNat).map (kittenClauseLits ks)).length := by
      simp [hi]
    rw [List.getElem?_eq_getElem hl1, List.getElem?_eq_getElem hl2,
      Option.getD_some, Option.getD_some]
    simp only [List.getElem_map, List.getElem_range]
    exact hlits_perm_all i (Nat.lt_of_lt_of_le hi hinv.clauses.orig_nc_le)
  have horig_ent_iff : ∀ cl,
      (cnfOfClauses (kittenOrigClauses ks')).EntailsClause cl ↔
        (cnfOfClauses (kittenOrigClauses ks)).EntailsClause cl := fun cl =>
    ⟨fun h => horig_perm.entailsClause h, fun h => horig_perm.symm.entailsClause h⟩
  have hcl' : KittenClausesOk acap ks' := by
    have h0 := hinv.clauses
    refine ⟨h0.acap_ge, h0.acap_lt, h0.acap_eq, h0.nv_le, h0.nc_le, h0.orig_nc_le, h0.orig_nc_max,
      h0.alen_le, h0.nassump_le, h0.nunits_le, h0.nres_le, h0.nkl_le, h0.nana_le,
      ?_, ?_, ?_, ?_, ?_, h0.assump_ok, h0.flags_clean⟩
    · intro c hc
      have hc' : c < ks.nc.toNat := hc
      have hw := h0.cl_wf c hc'
      have hp := hlits_perm_all c hc'
      have hmem : ∀ l, l ∈ kittenClauseLits ks' c ↔ l ∈ kittenClauseLits ks c := fun l => hp.mem_iff
      refine ⟨hw.1, hw.2.1, hw.2.2.1, fun l hl => hw.2.2.2.1 l ((hmem l).mp hl), ?_, ?_⟩
      · rw [horig_ent_iff, CNF.entails_clause_def]
        intro α hα
        exact (cnfClause_sat_perm α hp).mpr (CNF.entails_clause_def.mp hw.2.2.2.2.1 α hα)
      · intro hante hge
        have ⟨ha1, ha2⟩ := hw.2.2.2.2.2 hante hge
        refine ⟨by rw [hants_all c hc']; exact ha1, ?_⟩
        rw [hants_all c hc', CNF.entails_clause_def]
        intro α hα
        have hp_cnf : KittenCnfPermEquiv ((kittenClauseAnts ks c).map (kittenClauseLits ks'))
            ((kittenClauseAnts ks c).map (kittenClauseLits ks)) := by
          refine ⟨by simp, fun i hi => ?_⟩
          simp only [List.length_map] at hi
          rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
            List.getElem?_eq_getElem (by simpa using hi),
            List.getElem?_eq_getElem (by simpa using hi), Option.getD_some, Option.getD_some]
          simp only [List.getElem_map]
          exact hlits_perm_all _ (Nat.lt_trans (ha1 _ (List.getElem_mem hi)) hc')
        exact (cnfClause_sat_perm α hp).mpr
          (CNF.entails_clause_def.mp ha2 α ((hp_cnf.sat_iff α).mp hα))
    · exact h0.cl_mono
    · intro ui hui; exact h0.units_ok ui hui
    · intro hi
      have hinc := h0.incons_ok hi
      have hp_inc := hlits_perm_all ks.incons.toNat hinc.1
      refine ⟨hinc.1, CNF.unsat_iff_not_sat.mpr (fun α hα =>
          (CNF.unsat_iff_not_sat.mp hinc.2.1) α ((horig_perm.sat_iff α).mp hα)), fun l hl => ?_⟩
      have hl' := hp_inc.mem_iff.mp hl
      have hr := hinc.2.2 l hl'
      refine ⟨hr.1, hr.2.1, fun hante => ?_⟩
      have hrr := hr.2.2 hante
      let rr := (ks.rsn[l / 2]?.getD 0xFFFFFFFF#32).toNat
      have hne_c : rr ≠ cid := by
        intro heq
        have hlen1 := congrArg List.length hrr.2
        have hbd_r : kittenClauseOff ks rr + kittenClauseSize ks rr ≤ ks.arena.length := by
          have := (h0.cl_wf _ hrr.1).2.2.1; unfold kittenClauseSpan at this
          dsimp only [rr]; rw [har_len]; omega
        have hsz1 : kittenClauseSize ks cid = 1 := by
          unfold kittenClauseLits at hlen1
          dsimp only [rr] at hbd_r heq
          rw [List.length_map, List.length_take, List.length_drop,
            Nat.min_eq_left (by omega)] at hlen1
          rw [← heq]; exact hlen1
        omega
      have hlits_rr : kittenClauseLits ks' rr = kittenClauseLits ks rr :=
        hlits_other rr hrr.1 hne_c
      exact ⟨hrr.1, by change kittenClauseLits ks' rr = [l ^^^ 1]; rw [hlits_rr]; exact hrr.2⟩
    · intro ha hf
      have hfa := h0.failing_ok ha hf
      have hp_fail : KittenCnfPermEquiv
          (((List.range ks'.nc.toNat).filter fun ci =>
            (kittenClauseMeta ks' ci &&& kmCore) != 0#32).map (kittenClauseLits ks'))
          (((List.range ks.nc.toNat).filter fun ci =>
            (kittenClauseMeta ks ci &&& kmCore) != 0#32).map (kittenClauseLits ks)) := by
        have hflt : (List.range ks'.nc.toNat).filter
              (fun ci => (kittenClauseMeta ks' ci &&& kmCore) != 0#32) =
            (List.range ks.nc.toNat).filter
              (fun ci => (kittenClauseMeta ks ci &&& kmCore) != 0#32) := by
          rw [e_nc]; exact List.filter_congr fun i _ => by rw [e_cm]
        refine ⟨by simp [hflt], fun i hi => ?_⟩
        simp only [List.length_map, hflt] at hi
        rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
          List.getElem?_eq_getElem (by simp [hflt, hi]),
          List.getElem?_eq_getElem (by simp [hi]), Option.getD_some, Option.getD_some]
        simp only [List.getElem_map, hflt]
        have hmem_f := List.mem_filter.mp (List.getElem_mem hi)
        rw [List.mem_range] at hmem_f
        exact hlits_perm_all _ hmem_f.1
      exact (hp_fail.unsat_iff (unitsCnf (kittenAssumpLits ks))).mpr hfa
  have hba' : KittenBaseAssignOk ks' := by
    have h0 := hinv.assign
    refine ⟨h0.trl_end_le, h0.prop_le, h0.unass_eq, h0.vals_dom, h0.vals_neg_iff,
      h0.vals_nz_iff_trl, h0.trl_nodup, h0.trl_lt, h0.trl_lvl_le, h0.unass_lvl_zero,
      h0.trl_lvl_mono, h0.dec_earliest, fun i hi hlv => ?_⟩
    have hl0 := h0.lvl0_ok i hi hlv
    have hnt_ent : (cnfOfClauses (kittenOrigClauses ks')).EntailsClause
        (cnfClause [(ks.trl[i]?.getD 0#32).toNat]) :=
      horig_perm.symm.entailsClause hl0.2.2.2.1
    refine ⟨hl0.1, hl0.2.1, hl0.2.2.1, hnt_ent, fun hante => ?_⟩
    have hrr := hl0.2.2.2.2 hante
    let rr := (ks.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat
    have hne_c : rr ≠ cid := by
      intro heq
      have hlen1 := congrArg List.length hrr.2
      have hbd_r : kittenClauseOff ks rr + kittenClauseSize ks rr ≤ ks.arena.length := by
        have := (hinv.clauses.cl_wf _ hrr.1).2.2.1; unfold kittenClauseSpan at this
        dsimp only [rr]; rw [har_len]; omega
      have hsz1 : kittenClauseSize ks cid = 1 := by
        unfold kittenClauseLits at hlen1
        dsimp only [rr] at hbd_r heq
        rw [List.length_map, List.length_take, List.length_drop,
          Nat.min_eq_left (by omega)] at hlen1
        rw [← heq]; exact hlen1
      omega
    have hlits_rr : kittenClauseLits ks' rr = kittenClauseLits ks rr :=
      hlits_other rr hrr.1 hne_c
    refine ⟨hrr.1, ?_⟩
    change kittenClauseLits ks' rr = [(ks.trl[i]?.getD 0#32).toNat]
    rw [hlits_rr]; exact hrr.2
  have hrsn' : ReasonOk ks' := by
    intro i hi
    have hro := hinv.reasons i hi
    dsimp only at hro ⊢
    rcases hro with hdec | ⟨hr_lt, hmem, hall⟩
    · exact Or.inl hdec
    · right
      have hp := hlits_perm_all _ hr_lt
      exact ⟨hr_lt, hp.mem_iff.mpr hmem, fun x hx => hall x (hp.mem_iff.mp hx)⟩
  let chains1 := chains.set l (done ++ todo')
  have hch1_len : chains1.length = 2 * ks1.nv.toNat := by
    simp only [chains1, List.length_set]; exact wc.len_eq
  have hch_l_eq : chains[l]'hch_l = done ++ w0 :: todo' := by
    have := wc.chain_l
    rwa [List.getElem?_eq_getElem hch_l, Option.getD_some] at this
  have hperm1 : chains.flatten.Perm (w0 :: chains1.flatten) :=
    list_flatten_set_sub_perm chains hch_l done todo' w0 hch_l_eq
  have hnd_cons : (w0 :: chains1.flatten).Nodup := hperm1.nodup_iff.mp wc.nodup
  have hw0_not_in : w0 ∉ chains1.flatten := (List.nodup_cons.mp hnd_cons).1
  have hch1_nd : chains1.flatten.Nodup := (List.nodup_cons.mp hnd_cons).2
  have hch1_sub : ∀ x < 2 * ks.nv.toNat, ∀ u ∈ chains1[x]?.getD [], u ∈ chains[x]?.getD [] := by
    intro x hx u hu
    have hx1 : x < chains1.length := by
      simp only [chains1, List.length_set]; rw [wc.len_eq]; exact hx
    have hx0 : x < chains.length := by rw [wc.len_eq]; exact hx
    rw [List.getElem?_eq_getElem hx1, Option.getD_some] at hu
    rw [List.getElem?_eq_getElem hx0, Option.getD_some]
    by_cases hxl : x = l
    · subst hxl
      simp only [chains1, List.getElem_set_self] at hu
      rw [hch_l_eq]
      rcases List.mem_append.mp hu with hd | ht
      · exact List.mem_append_left _ hd
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ ht)
    · simp only [chains1, List.getElem_set_ne (Ne.symm hxl)] at hu
      exact hu
  have hdone_elim : prev = 0xFFFFFFFF#32 → done = [] := fun hprev => by
    rcases wc.prev_rel with ⟨hd, _, _⟩ | ⟨_, u, _, hp_eq, hu_len, _⟩
    · exact hd
    · exfalso
      have h2 : u < 1792 := by rw [hsh.wnext_len] at hu_len; exact hu_len
      have h3 := congrArg BitVec.toNat (hp_eq.symm.trans hprev)
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        show (0xFFFFFFFF#32 : BitVec 32).toNat = 2 ^ 32 - 1 by decide] at h3
      omega
  have hwc1 : ∀ x < 2 * ks1.nv.toNat,
      WChain ks1.wnext (ks1.whead[x]?.getD 0xFFFFFFFF#32) (chains1[x]?.getD []) := by
    intro x hx
    have hx_nv : x < 2 * ks.nv.toNat := hx
    have hx1 : x < chains1.length := by
      simp only [chains1, List.length_set]; rw [wc.len_eq]; exact hx_nv
    have hx0 : x < chains.length := by rw [wc.len_eq]; exact hx_nv
    by_cases hprev : prev = 0xFFFFFFFF#32
    · have hdone_nil := hdone_elim hprev
      have hwh1 : wh1 = ks.whead.set l nxt := by simp [wh1, hprev]
      have hwn1 : wn1 = ks.wnext := by simp [wn1, hprev]
      by_cases hxl : l = x
      · subst hxl
        rw [List.getElem?_eq_getElem hx1, Option.getD_some]
        simp only [chains1, List.getElem_set_self, hdone_nil, List.nil_append, ks1, hwh1, hwn1]
        rw [List.getElem?_set_self hwh_len, Option.getD_some]
        rcases WChain_cases wc.tail_wc with ⟨_, hn⟩ | ⟨w0', _, hw0', hw_eq', hcons, htail'⟩
        · cases hn
        · obtain ⟨_, htd_eq⟩ := List.cons.inj hcons
          subst htd_eq
          have hw0_eq : w0 = w0' := by
            have ht := congrArg BitVec.toNat hw_eq'
            have h1 : w0 < 2 ^ 32 := by unfold kMaxCl at hnc; omega
            have hwn' : w0' < 1792 := by rw [hsh.wnext_len] at hw0'; exact hw0'
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1,
              Nat.mod_eq_of_lt (by omega : w0' < 2 ^ 32)] at ht
            exact ht
          subst hw0_eq
          have hg : nxt = ks.wnext[w0]'hw0' := by
            dsimp only [nxt]; rw [List.getElem?_eq_getElem hw0', Option.getD_some]
          rw [hg]; exact htail'
      · have hwc0 := wc.chains_wc x hx_nv
        rw [List.getElem?_eq_getElem hx1, Option.getD_some]
        rw [List.getElem?_eq_getElem hx0, Option.getD_some] at hwc0
        simp only [chains1, List.getElem_set_ne hxl, ks1, hwh1, hwn1] at hwc0 ⊢
        rwa [List.getElem?_set_ne hxl]
    · rcases wc.prev_rel with ⟨_, hp_fff, _⟩ | ⟨pfx, u, hdone_eq, hp_eq, hu_len, _⟩
      · exact absurd hp_fff hprev
      · have hu_tn : prev.toNat = u := by
          rw [hp_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
            rw [hsh.wnext_len] at hu_len; omega)]
        have hwh1 : wh1 = ks.whead := by simp [wh1, hprev]
        have hwn1 : wn1 = ks.wnext.set u nxt := by simp [wn1, hprev, hu_tn]
        have hnd_get := list_flatten_nodup_getElem wc.nodup hch_l
        by_cases hxl : l = x
        · subst hxl
          rw [List.getElem?_eq_getElem hx1, Option.getD_some]
          simp only [chains1, List.getElem_set_self, hdone_eq, List.append_assoc, ks1, hwh1, hwn1]
          have hwc0 := wc.chains_wc l hx_nv
          rw [List.getElem?_eq_getElem hch_l, Option.getD_some, hch_l_eq, hdone_eq,
            List.append_assoc] at hwc0
          have hnd_l := hnd_get.1
          rw [hch_l_eq, hdone_eq, List.append_assoc] at hnd_l
          simpa [List.append_assoc] using wchain_bypass hwc0 hnd_l hu_len hwn_len hnxt_eq.symm
        · have hu_not_x : u ∉ chains[x]'hx0 := by
            refine hnd_get.2 x (Ne.symm hxl) hx0 u ?_
            rw [hch_l_eq, hdone_eq]; simp
          have hwc0 := wc.chains_wc x hx_nv
          rw [List.getElem?_eq_getElem hx1, Option.getD_some]
          rw [List.getElem?_eq_getElem hx0, Option.getD_some] at hwc0
          simp only [chains1, List.getElem_set_ne hxl, ks1, hwh1, hwn1]
          exact hwc0.congr fun y hy =>
            (List.getElem?_set_ne (fun h : u = y => hu_not_x (h ▸ hy))).symm
  have hbnd1 : ∀ x < 2 * ks1.nv.toNat, ∀ u ∈ chains1[x]?.getD [],
      u < 2 * ks1.nc.toNat ∧ 2 ≤ kittenClauseSize ks1 (u / 2) ∧
      (ks1.arena[kittenClauseOff ks1 (u / 2) + (u % 2)]?.getD 0#32).toNat = x ∧
      (ks1.wblit[u]?.getD 0#32).toNat < 2 * ks1.nv.toNat := by
    intro x hx u hu
    have hbu := wc.chains_bnd x hx u (hch1_sub x hx u hu)
    have hu_ne : u ≠ w0 := fun h => hw0_not_in (by
      rw [← h, List.mem_flatten]
      have hx1 : x < chains1.length := by
        simp only [chains1, List.length_set]; rw [wc.len_eq]; exact hx
      exact ⟨chains1[x], List.getElem_mem hx1, by
        simpa [List.getElem?_eq_getElem hx1] using hu⟩)
    have har_u : ks1.arena[kittenClauseOff ks (u / 2) + u % 2]? =
        ks.arena[kittenClauseOff ks (u / 2) + u % 2]? := by
      dsimp only [ks1, ar']
      by_cases huc : u / 2 = cid
      · have hmod_ne1 : u % 2 ≠ slot := fun hm => hu_ne (by omega)
        have hmod_ne2 : u % 2 ≠ ri := by
          have : u % 2 < 2 := Nat.mod_lt u (by decide); omega
        rw [huc, List.getElem?_set_ne (by dsimp only [off]; omega),
          List.getElem?_set_ne (by dsimp only [off]; omega)]
      · have hu_lt : u / 2 < ks.nc.toNat := Nat.div_lt_of_lt_mul hbu.1
        have hne_off : ∀ idx < kittenClauseSpan ks cid,
            off + idx ≠ kittenClauseOff ks (u / 2) + u % 2 := by
          intro idx hidx; dsimp only [off]
          by_cases hlu : u / 2 < cid
          · have hm := hinv.clauses.cl_mono (u / 2) cid hlu hcid_lt
            have hsp_u : 2 ≤ kittenClauseSpan ks (u / 2) := by
              unfold kittenClauseSpan; have := hbu.2.1; omega
            have hu_m : u % 2 < 2 := Nat.mod_lt u (by decide)
            change kittenClauseOff ks (u / 2) + kittenClauseSpan ks (u / 2) ≤
              kittenClauseOff ks cid at hm
            omega
          · have hm := hinv.clauses.cl_mono cid (u / 2) (by omega) hu_lt
            change kittenClauseOff ks cid + kittenClauseSpan ks cid ≤
              kittenClauseOff ks (u / 2) at hm
            omega
        have hne1 := hne_off slot (by unfold kittenClauseSpan; omega)
        have hne2 := hne_off ri (by unfold kittenClauseSpan; omega)
        rw [List.getElem?_set_ne hne2, List.getElem?_set_ne hne1]
    have har_u' : (ks1.arena[kittenClauseOff ks1 (u / 2) + u % 2]?.getD 0#32).toNat = x := by
      change (ks1.arena[kittenClauseOff ks (u / 2) + u % 2]?.getD 0#32).toNat = x
      rw [har_u]; exact hbu.2.2.1
    exact ⟨hbu.1, hbu.2.1, har_u', hbu.2.2.2⟩
  have hsz_ks1 : ∀ c, kittenClauseSize ks1 c = kittenClauseSize ks c := fun _ => rfl
  have hoff_ks1 : ∀ c, kittenClauseOff ks1 c = kittenClauseOff ks c := fun _ => rfl
  have hw_tn : w.toNat = w0 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold kMaxCl at hnc; omega)]
  have hw_step0 := kittenWatchStep0_preserves_watches_with hsh1 hch1_len hch1_nd hwc1 hbnd1
    (w := w) (l := repl) (vo := other)
    (by change w.toNat < 2 * ks.nc.toNat; rw [hw_tn]; exact hb0.1)
    hnc hnv hrepl_nv hother_nv
    (by rw [hsz_ks1, hw_tn]; exact hsz_ge)
    (by rw [hoff_ks1, hw_tn]
        change (ar'[off + slot]?.getD 0#32).toNat = repl.toNat
        have hslot_ri : off + slot ≠ off + ri := by omega
        have hoff_len2 : off + slot < ks.arena.length := by dsimp only [off]; omega
        simp [ar', List.getElem?_set_ne hslot_ri.symm,
          List.getElem?_set_self (by simp [hoff_len2] : off + slot < ks.arena.length)])
    (by rw [hw_tn]; exact hw0_not_in)
  have hrl1 : repl.toNat < chains1.length := by
    rw [hch1_len]; exact hrepl_nv
  let chains' := chains1.set repl.toNat (w.toNat :: chains1[repl.toNat]'hrl1)
  have hwc_cur' : WChainCursor ks' l chains' done todo' prev nxt := by
    have hl1 : l < 2 * ks1.nv.toNat := hl
    have hch'_l : l < chains'.length := by
      simp only [chains', List.length_set]; rw [hch1_len]; exact hl1
    have hcl'_eq : chains'[l]?.getD [] = done ++ todo' := by
      rw [List.getElem?_eq_getElem hch'_l, Option.getD_some]
      simp only [chains', List.getElem_set_ne hrepl_ne]
      simp only [chains1, List.getElem_set_self]
    have htail_ks : WChain ks.wnext nxt todo' := by
      rcases WChain_cases wc.tail_wc with ⟨_, hn⟩ | ⟨w0', _, hw0', hw_eq', hcons, htail'⟩
      · cases hn
      · obtain ⟨_, htd_eq⟩ := List.cons.inj hcons
        subst htd_eq
        have hw0_eq : w0 = w0' := by
          have ht := congrArg BitVec.toNat hw_eq'
          have h1 : w0 < 2 ^ 32 := by unfold kMaxCl at hnc; omega
          have hwn' : w0' < 1792 := by rw [hsh.wnext_len] at hw0'; exact hw0'
          simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1,
            Nat.mod_eq_of_lt (by omega : w0' < 2 ^ 32)] at ht
          exact ht
        subst hw0_eq
        have hg : nxt = ks.wnext[w0]'hw0' := by
          dsimp only [nxt]; rw [List.getElem?_eq_getElem hw0', Option.getD_some]
        rw [hg]; exact htail'
    have hnd_l := (list_flatten_nodup_getElem wc.nodup hch_l).1
    have hw0_nt : w0 ∉ todo' := by
      rw [hch_l_eq] at hnd_l
      have hnd2 := (List.nodup_append.mp hnd_l).2.1
      exact (List.nodup_cons.mp hnd2).1
    have htail1 : WChain ks1.wnext nxt todo' := by
      by_cases hprev : prev = 0xFFFFFFFF#32
      · simp [ks1, wn1, hprev, htail_ks]
      · rcases wc.prev_rel with ⟨_, hp, _⟩ | ⟨pfx, u, hde, hp_eq, hu_len, _⟩
        · exact absurd hp hprev
        · have hu_tn : prev.toNat = u := by
            rw [hp_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
              rw [hsh.wnext_len] at hu_len; omega)]
          have hu_nt : u ∉ todo' := by
            rw [hch_l_eq, hde] at hnd_l
            have hd := (List.nodup_append.mp hnd_l).2.2 u (by simp)
            exact fun h => hd u (List.mem_cons_of_mem _ h) rfl
          simp only [ks1, wn1, hprev, ↓reduceIte, hu_tn]
          exact htail_ks.congr fun y hy =>
            (List.getElem?_set_ne (fun h : u = y => hu_nt (h ▸ hy))).symm
    have htail' : WChain ks'.wnext nxt todo' := by
      change WChain (ks1.wnext.set w.toNat _) nxt todo'
      rw [hw_tn]
      exact htail1.congr fun y hy =>
        (List.getElem?_set_ne (fun h : w0 = y => hw0_nt (h ▸ hy))).symm
    have hprev' : (done = [] ∧ prev = 0xFFFFFFFF#32 ∧
        ks'.whead[l]?.getD 0xFFFFFFFF#32 = nxt) ∨
        (∃ pfx u, done = pfx ++ [u] ∧ prev = BitVec.ofNat 32 u ∧
          u < ks'.wnext.length ∧ ks'.wnext[u]?.getD 0xFFFFFFFF#32 = nxt) := by
      by_cases hprev : prev = 0xFFFFFFFF#32
      · left
        have hdone_nil := hdone_elim hprev
        refine ⟨hdone_nil, hprev, ?_⟩
        change (ks1.whead.set repl.toNat w)[l]?.getD 0xFFFFFFFF#32 = nxt
        rw [List.getElem?_set_ne hrepl_ne]
        change (wh1)[l]?.getD 0xFFFFFFFF#32 = nxt
        dsimp only [wh1]
        simp only [hprev, ↓reduceIte, List.getElem?_set_self hwh_len, Option.getD_some]
      · right
        rcases wc.prev_rel with ⟨_, hp, _⟩ | ⟨pfx, u, hde, hp_eq, hu_len, _⟩
        · exact absurd hp hprev
        · have hu_tn : prev.toNat = u := by
            rw [hp_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
              rw [hsh.wnext_len] at hu_len; omega)]
          have hune : w0 ≠ u := by
            intro heq
            rw [hch_l_eq, hde] at hnd_l
            have hd := (List.nodup_append.mp hnd_l).2.2 u (by simp)
            exact hd w0 List.mem_cons_self heq.symm
          refine ⟨pfx, u, hde, hp_eq, by simpa [ks', kittenWatchStep0, ks1, wn1, hprev] using
            hu_len, ?_⟩
          change (ks1.wnext.set w.toNat _)[u]?.getD 0xFFFFFFFF#32 = nxt
          rw [hw_tn, List.getElem?_set_ne hune]
          change wn1[u]?.getD 0xFFFFFFFF#32 = nxt
          dsimp only [wn1]
          simp only [hprev, ↓reduceIte, hu_tn, List.getElem?_set_self hu_len, Option.getD_some]
    exact ⟨hw_step0.1, hw_step0.2.1, hcl'_eq, hw_step0.2.2.1, hw_step0.2.2.2.1, htail', hprev'⟩
  exact ⟨⟨hsh', hcl', hwc_cur'.watchesOk, hba', hrsn'⟩, hsync, hlits_perm_all, hlits_other,
    hants_all, horig_perm, ⟨chains', hwc_cur'⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


/-! ## 2. `PropFrame`: Entry-to-Exit Frame Relation -/

/-- Frame relation between the `propagate` entry state `ks0` and a later state `ks`. -/
private structure PropFrame (ks0 ks : KittenState) : Prop where
  nv : ks.nv = ks0.nv
  orig_nc : ks.orig_nc = ks0.orig_nc
  lvl : ks.lvl = ks0.lvl
  incons : ks.incons = ks0.incons
  failing : ks.failing = ks0.failing
  ante : ks.ante = ks0.ante
  nassump : ks.nassump = ks0.nassump
  assump : ks.assump = ks0.assump
  perm : KittenCnfPermEquiv (kittenOrigClauses ks) (kittenOrigClauses ks0)
  clAux : ∀ ci < ks0.orig_nc.toNat, ks.clAux[ci]? = ks0.clAux[ci]?
  clMetaCore : ∀ ci < ks0.orig_nc.toNat,
    (ks.clMeta[ci]?.getD 0#32 &&& kmCore) = (ks0.clMeta[ci]?.getD 0#32 &&& kmCore)
  dec : kittenTrailDecisions ks = kittenTrailDecisions ks0
  te_ge : ks0.trl_end.toNat ≤ ks.trl_end.toNat
  trl : ∀ i < ks0.trl_end.toNat, ks.trl[i]? = ks0.trl[i]? ∧
    ks.lvlArr[(ks0.trl[i]?.getD 0#32).toNat / 2]? =
      ks0.lvlArr[(ks0.trl[i]?.getD 0#32).toNat / 2]?

private theorem PropFrame.refl (ks : KittenState) : PropFrame ks ks :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, KittenCnfPermEquiv.refl _,
    fun _ _ => rfl, fun _ _ => rfl, rfl, Nat.le_refl _, fun _ _ => ⟨rfl, rfl⟩⟩

private theorem PropFrame.trans {ks0 ks1 ks2 : KittenState} (h1 : PropFrame ks0 ks1)
    (h2 : PropFrame ks1 ks2) : PropFrame ks0 ks2 := by
  refine ⟨h2.nv.trans h1.nv, h2.orig_nc.trans h1.orig_nc, h2.lvl.trans h1.lvl,
    h2.incons.trans h1.incons, h2.failing.trans h1.failing, h2.ante.trans h1.ante,
    h2.nassump.trans h1.nassump, h2.assump.trans h1.assump, h2.perm.trans h1.perm,
    fun ci hci => (h2.clAux ci (by rw [h1.orig_nc]; exact hci)).trans (h1.clAux ci hci),
    fun ci hci =>
      (h2.clMetaCore ci (by rw [h1.orig_nc]; exact hci)).trans (h1.clMetaCore ci hci),
    h2.dec.trans h1.dec, Nat.le_trans h1.te_ge h2.te_ge, fun i hi => ?_⟩
  have h1i := h1.trl i hi
  have h2i := h2.trl i (Nat.lt_of_lt_of_le hi h1.te_ge)
  refine ⟨h2i.1.trans h1i.1, ?_⟩
  rw [h1i.1] at h2i
  exact h2i.2.trans h1i.2

/-- Steps that leave the trail, levels, reasons, and all frame scalars untouched. -/
private theorem PropFrame.of_eq {ks ks' : KittenState}
    (h_nv : ks'.nv = ks.nv) (h_on : ks'.orig_nc = ks.orig_nc) (h_lvl : ks'.lvl = ks.lvl)
    (h_in : ks'.incons = ks.incons) (h_fa : ks'.failing = ks.failing)
    (h_an : ks'.ante = ks.ante) (h_na : ks'.nassump = ks.nassump)
    (h_as : ks'.assump = ks.assump)
    (h_perm : KittenCnfPermEquiv (kittenOrigClauses ks') (kittenOrigClauses ks))
    (h_ca : ∀ ci < ks.orig_nc.toNat, ks'.clAux[ci]? = ks.clAux[ci]?)
    (h_cm : ∀ ci < ks.orig_nc.toNat,
      (ks'.clMeta[ci]?.getD 0#32 &&& kmCore) = (ks.clMeta[ci]?.getD 0#32 &&& kmCore))
    (h_te : ks'.trl_end = ks.trl_end) (h_trl : ks'.trl = ks.trl)
    (h_la : ks'.lvlArr = ks.lvlArr) (h_rs : ks'.rsn = ks.rsn) : PropFrame ks ks' :=
  ⟨h_nv, h_on, h_lvl, h_in, h_fa, h_an, h_na, h_as, h_perm, h_ca, h_cm,
    by unfold kittenTrailDecisions; rw [h_te, h_trl, h_rs],
    by rw [h_te]; exact Nat.le_refl _, fun _ _ => ⟨by rw [h_trl], by rw [h_la]⟩⟩

/-! ## 3. Cursor / Invariant Transfer across `learn_unit0`, `assign`, and `ticks` -/

/-- `WChainCursor` only depends on watch arrays, `nv`, and the first two slots of watched
clauses. -/
private theorem WChainCursor.transfer {ks ks' : KittenState} {l : Nat}
    {ch : List (List Nat)} {done todo : List Nat} {prev w : BitVec 32}
    (wc : WChainCursor ks l ch done todo prev w)
    (h_nv : ks'.nv = ks.nv) (h_wn : ks'.wnext = ks.wnext) (h_wh : ks'.whead = ks.whead)
    (h_wb : ks'.wblit = ks.wblit) (h_nc : ks.nc.toNat ≤ ks'.nc.toNat)
    (h_cl : ∀ c < ks.nc.toNat, kittenClauseSize ks' c = kittenClauseSize ks c ∧
      kittenClauseOff ks' c = kittenClauseOff ks c)
    (h_ar : ∀ c < ks.nc.toNat, 2 ≤ kittenClauseSize ks c → ∀ q < 2,
      ks'.arena[kittenClauseOff ks c + q]? = ks.arena[kittenClauseOff ks c + q]?) :
    WChainCursor ks' l ch done todo prev w := by
  refine ⟨by rw [h_nv]; exact wc.len_eq, wc.nodup, wc.chain_l,
    fun x hx => by rw [h_nv] at hx; rw [h_wn, h_wh]; exact wc.chains_wc x hx,
    fun x hx u hu => ?_, by rw [h_wn]; exact wc.tail_wc,
    by rw [h_wh, h_wn]; exact wc.prev_rel⟩
  rw [h_nv] at hx
  have hbu := wc.chains_bnd x hx u hu
  have hc_lt : u / 2 < ks.nc.toNat := Nat.div_lt_of_lt_mul hbu.1
  have hcl := h_cl (u / 2) hc_lt
  have har := h_ar (u / 2) hc_lt hbu.2.1 (u % 2) (Nat.mod_lt u (by decide))
  refine ⟨by omega, by rw [hcl.1]; exact hbu.2.1, ?_, by rw [h_wb, h_nv]; exact hbu.2.2.2⟩
  rw [hcl.2, har]; exact hbu.2.2.1

/-- Advancing the watch-chain cursor without changing `ks` (`wblit[w0]` already true). -/
private theorem WChainCursor.advance {acap : Nat} {ks : KittenState} (hsh : ks.ShapesOk acap)
    (hnc : ks.nc.toNat ≤ kMaxCl) {l : Nat} (_hl : l < 2 * ks.nv.toNat)
    {ch : List (List Nat)} {done todo' : List Nat} {prev : BitVec 32} {w0 : Nat}
    (wc : WChainCursor ks l ch done (w0 :: todo') prev (BitVec.ofNat 32 w0))
    (hw0_nc : w0 < 2 * ks.nc.toNat) :
    WChainCursor ks l ch (done ++ [w0]) todo' (BitVec.ofNat 32 w0) (ks.wnext[w0]?.getD 0#32) := by
  have hwn_len : w0 < ks.wnext.length := by rw [hsh.wnext_len]; unfold kMaxCl at hnc; omega
  have hnxt_eq : ks.wnext[w0]?.getD 0#32 = ks.wnext[w0]?.getD 0xFFFFFFFF#32 := by
    rw [List.getElem?_eq_getElem hwn_len]; rfl
  rcases WChain_cases wc.tail_wc with ⟨_, hnil⟩ | ⟨w0', _, hw0', hw_eq, hcons, htail'⟩
  · cases hnil
  · obtain ⟨_, htd_eq⟩ := List.cons.inj hcons
    subst htd_eq
    have hw0_eq : w0 = w0' := by
      have ht := congrArg BitVec.toNat hw_eq
      have h1 : w0 < 2 ^ 32 := by unfold kMaxCl at hnc; omega
      have hwn' : w0' < 1792 := by rw [hsh.wnext_len] at hw0'; exact hw0'
      have h2 : w0' < 2 ^ 32 := by omega
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at ht
      exact ht
    subst hw0_eq
    refine ⟨wc.len_eq, wc.nodup, by rw [wc.chain_l]; simp, wc.chains_wc, wc.chains_bnd, ?_,
      Or.inr ⟨done, w0, rfl, rfl, hwn_len, hnxt_eq.symm⟩⟩
    have hget : ks.wnext[w0]?.getD 0#32 = ks.wnext[w0]'hw0' := by
      rw [List.getElem?_eq_getElem hw0', Option.getD_some]
    rw [hget]; exact htail'

/-- Bumping `prop` (`≤ trl_end`) and `ticks` preserves `Inv`, `TrailSynced`, `PropFrame`, and any
watch cursor. -/
private theorem kittenBumpPropTicks_preserves {acap : Nat} {ks : KittenState}
    (hinv : ks.Inv acap) (hsync : KittenTrailSynced ks) {pr' tk' : BitVec 32}
    (hpr : pr'.toNat ≤ ks.trl_end.toNat) :
    let ks' := (ks.putHdr .prop pr').putHdr .ticks tk'
    ks'.Inv acap ∧ KittenTrailSynced ks' ∧ PropFrame ks ks' ∧ ks'.prop = pr' ∧
    ks'.vals = ks.vals ∧ ks'.trl = ks.trl ∧ ks'.trl_end = ks.trl_end ∧
    (∀ {l ch done todo prev w}, WChainCursor ks l ch done todo prev w →
      WChainCursor ks' l ch done todo prev w) := by
  intro ks'
  have ⟨hinv', hsync'⟩ := kittenBumpPropTicks_preserves_inv (tk' := tk') hinv hsync hpr
  have hfr : PropFrame ks ks' := by
    refine PropFrame.of_eq ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (try (dsimp only [ks']; kp_field))
    · have horig : kittenOrigClauses ks' = kittenOrigClauses ks := by
        unfold kittenOrigClauses kittenClauseLits kittenClauseOff kittenClauseSize kittenClauseMeta
        dsimp only [ks']; kp_field
      rw [horig]; exact KittenCnfPermEquiv.refl _
    · intro _ _; trivial
    · intro _ _; trivial
  have hwc : ∀ {l ch done todo prev w}, WChainCursor ks l ch done todo prev w →
      WChainCursor ks' l ch done todo prev w := by
    intro l ch done todo prev w wc
    refine wc.transfer ?_ ?_ ?_ ?_ (by dsimp only [ks']; kp_field; exact Nat.le_refl _)
      (fun _ _ => ⟨by unfold kittenClauseSize kittenClauseMeta; dsimp only [ks']; kp_field,
        by unfold kittenClauseOff; dsimp only [ks']; kp_field⟩)
      (fun _ _ _ _ _ => by dsimp only [ks']; kp_field) <;>
      (dsimp only [ks']; kp_field)
  exact ⟨hinv', hsync', hfr, by dsimp only [ks']; kp_field, by dsimp only [ks']; kp_field,
    by dsimp only [ks']; kp_field, by dsimp only [ks']; kp_field, @hwc⟩

/-- Bumping only `ticks` preserves `Inv`, `TrailSynced`, the frame, and any cursor. -/
private theorem kittenTicks_preserves {acap : Nat} {ks : KittenState}
    (hinv : ks.Inv acap) (hsync : KittenTrailSynced ks) (tk : BitVec 32) :
    let ks' := ks.putHdr .ticks tk
    ks'.Inv acap ∧ KittenTrailSynced ks' ∧ PropFrame ks ks' ∧ ks'.prop = ks.prop ∧
    ks'.vals = ks.vals ∧ ks'.trl = ks.trl ∧ ks'.trl_end = ks.trl_end ∧
    (∀ {l ch done todo prev w}, WChainCursor ks l ch done todo prev w →
      WChainCursor ks' l ch done todo prev w) := by
  intro ks'
  have heq : ks' = (ks.putHdr .prop ks.prop).putHdr .ticks tk := by
    dsimp only [ks']; kstate_ext <;> (first | rfl | kp_field)
  rw [heq]
  exact kittenBumpPropTicks_preserves hinv hsync hinv.assign.prop_le

/-- Successful `full_kitten_learn_unit0` (fresh size-1 learned clause `nc`) preserves `Inv`,
`TrailSynced`, the frame, and any watch cursor. -/
private theorem kittenUnit0_transfer {acap : Nat} {ks ks' : KittenState}
    (hinv : ks.Inv acap) (hsync : KittenTrailSynced ks)
    (hsh' : ks'.ShapesOk acap) (hcl' : KittenClausesOk acap ks')
    (hnc' : ks'.nc = ks.nc + 1#32) (hp : KittenUnit0Preserved ks ks') :
    ks'.Inv acap ∧ KittenTrailSynced ks' ∧ PropFrame ks ks' ∧ ks'.prop = ks.prop ∧
    ks.nc.toNat < ks'.nc.toNat ∧
    (∀ c < ks.nc.toNat, kittenClauseLits ks' c = kittenClauseLits ks c) ∧
    (∀ {l ch done todo prev w}, WChainCursor ks l ch done todo prev w →
      WChainCursor ks' l ch done todo prev w) := by
  have hnc_lt : ks.nc.toNat < ks'.nc.toNat := by
    have := hcl'.nc_le; unfold kMaxCl at this
    have h1 : ks.nc.toNat < 896 := by
      have hc0 := hinv.clauses.nc_le; unfold kMaxCl at hc0
      by_cases h896 : ks.nc.toNat = 896
      · exfalso
        have hwrap : (ks.nc + 1#32).toNat = 897 := by
          rw [BitVec.toNat_add, h896]; decide
        rw [hnc'] at this; omega
      · omega
    rw [hnc']; have : ks.nc.toNat < 2 ^ 32 - 1 := by omega
    bv_omega
  have hcl_lits : ∀ c < ks.nc.toNat, kittenClauseLits ks' c = kittenClauseLits ks c :=
    fun c hc => (hp.old_clauses c hc).2.2.2
  have har_slot : ∀ c < ks.nc.toNat, 2 ≤ kittenClauseSize ks c → ∀ q < 2,
      ks'.arena[kittenClauseOff ks c + q]? = ks.arena[kittenClauseOff ks c + q]? := by
    intro c hc hsz q hq
    have hwf := (hinv.clauses.cl_wf c hc).2.2.1
    have hsp : kittenClauseSize ks c ≤ kittenClauseSpan ks c := by unfold kittenClauseSpan; omega
    exact hp.arena_old (kittenClauseOff ks c + q) (by omega)
  have hw' : KittenWatchesOk ks' := by
    obtain ⟨ch, hlen, hnd, hwc, hbnd⟩ := hinv.watches
    refine ⟨ch, by rw [hp.nv]; exact hlen, hnd,
      fun l hl => by rw [hp.nv] at hl; rw [hp.wnext, hp.whead]; exact hwc l hl,
      fun l hl w hw => ?_⟩
    rw [hp.nv] at hl
    have hbu := hbnd l hl w hw
    have hc_lt : w / 2 < ks.nc.toNat := Nat.div_lt_of_lt_mul hbu.1
    have hold := hp.old_clauses (w / 2) hc_lt
    have hsz : kittenClauseSize ks' (w / 2) = kittenClauseSize ks (w / 2) := by
      unfold kittenClauseSize; rw [hold.2.1]
    refine ⟨by omega, by rw [hsz]; exact hbu.2.1, ?_, by rw [hp.wblit, hp.nv]; exact hbu.2.2.2⟩
    rw [hold.1, har_slot (w / 2) hc_lt hbu.2.1 (w % 2) (Nat.mod_lt w (by decide))]
    exact hbu.2.2.1
  have horig : kittenOrigClauses ks' = kittenOrigClauses ks :=
    kittenOrigClauses_eq_of hp.orig_nc fun c hc =>
      hcl_lits c (Nat.lt_of_lt_of_le (by rwa [← hp.orig_nc]) hinv.clauses.orig_nc_le)
  have hba' : KittenBaseAssignOk ks' := by
    have h0 := hinv.assign
    refine ⟨by rw [hp.trl_end, hp.nv]; exact h0.trl_end_le,
      by rw [hp.prop, hp.trl_end]; exact h0.prop_le,
      by rw [hp.unass, hp.trl_end, hp.nv]; exact h0.unass_eq,
      by rw [hp.nv, hp.vals]; exact h0.vals_dom,
      by rw [hp.nv, hp.vals]; exact h0.vals_neg_iff,
      by rw [hp.nv, hp.vals, hp.trl_end, hp.trl]; exact h0.vals_nz_iff_trl,
      by unfold kittenTrailLits; rw [hp.trl_end, hp.trl]; exact h0.trl_nodup,
      by unfold kittenTrailLits; rw [hp.nv, hp.trl_end, hp.trl]; exact h0.trl_lt,
      by rw [hp.nv, hp.lvlArr, hp.lvl]; exact h0.trl_lvl_le,
      by rw [hp.nv, hp.vals, hp.lvlArr, hp.rsn]; exact h0.unass_lvl_zero,
      by rw [hp.trl_end, hp.lvlArr, hp.trl]; exact h0.trl_lvl_mono,
      by rw [hp.trl_end, hp.lvlArr, hp.trl, hp.rsn]; exact h0.dec_earliest,
      fun i hi hlv => ?_⟩
    rw [hp.trl_end] at hi
    rw [hp.trl, hp.lvlArr] at hlv
    have hl0 := h0.lvl0_ok i hi hlv
    rw [hp.rsn, hp.trl, hp.vals, horig, hp.ante]
    refine ⟨hl0.1, hl0.2.1, hl0.2.2.1, hl0.2.2.2.1, fun ha => ?_⟩
    have hr := hl0.2.2.2.2 ha
    exact ⟨Nat.lt_trans hr.1 hnc_lt, by rw [hcl_lits _ hr.1]; exact hr.2⟩
  have hsync' : KittenTrailSynced ks' := by
    intro i hi; rw [hp.trl_end] at hi; rw [hp.trl, hp.vals]; exact hsync i hi
  have hrsn' : ReasonOk ks' := by
    intro i hi; rw [hp.trl_end] at hi
    have hro := hinv.reasons i hi
    dsimp only at hro ⊢
    rw [hp.trl, hp.rsn]
    rcases hro with hdec | ⟨hr_lt, hmem, hall⟩
    · exact Or.inl hdec
    · right
      refine ⟨Nat.lt_trans hr_lt hnc_lt, by rw [hcl_lits _ hr_lt]; exact hmem, fun x hx => ?_⟩
      rw [hcl_lits _ hr_lt] at hx
      exact hall x hx
  have hfr : PropFrame ks ks' := by
    refine PropFrame.of_eq hp.nv hp.orig_nc hp.lvl hp.incons hp.failing hp.ante hp.nassump
      hp.assump (by rw [horig]; exact KittenCnfPermEquiv.refl _) ?_ ?_ hp.trl_end hp.trl
      hp.lvlArr hp.rsn
    · intro ci hci
      have hci_nc := Nat.lt_of_lt_of_le hci hinv.clauses.orig_nc_le
      have haux := (hp.old_clauses ci hci_nc).2.2.1
      unfold kittenClauseAux at haux
      have h896 : ci < 896 := by have := hinv.clauses.orig_nc_max; unfold kMaxOrig at this; omega
      have h1 : ci < ks'.clAux.length := by rw [hsh'.clAux_len]; exact h896
      have h2 : ci < ks.clAux.length := by rw [hinv.shapes.clAux_len]; exact h896
      rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2, Option.getD_some,
        Option.getD_some] at haux
      rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2]
      exact congrArg some (BitVec.eq_of_toNat_eq haux)
    · intro ci hci
      have hci_nc := Nat.lt_of_lt_of_le hci hinv.clauses.orig_nc_le
      have hcm := (hp.old_clauses ci hci_nc).2.1
      unfold kittenClauseMeta at hcm
      rw [hcm]
  have hwc : ∀ {l ch done todo prev w}, WChainCursor ks l ch done todo prev w →
      WChainCursor ks' l ch done todo prev w := by
    intro l ch done todo prev w wc
    refine wc.transfer hp.nv hp.wnext hp.whead hp.wblit (Nat.le_of_lt hnc_lt)
      (fun c hc => ⟨by unfold kittenClauseSize; rw [(hp.old_clauses c hc).2.1],
        (hp.old_clauses c hc).1⟩)
      har_slot
  exact ⟨⟨hsh', hcl', hw', hba', hrsn'⟩, hsync', hfr, hp.prop, hnc_lt, hcl_lits, @hwc⟩

/-- BCP `full_kitten_assign` of an unassigned literal whose reason clause has all other
literals falsified preserves `Inv`, `TrailSynced`, the frame, and any watch cursor. -/
private theorem flags_or1_clean_3a (x : BitVec 32) (h : (x &&& 2#32) = 0#32) :
    ((x ||| 1#32) &&& 2#32) = 0#32 := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  have h1 : x[1] = false := by
    have := congrArg (fun b : BitVec 32 => b[1]) h; simpa using this
  simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_zero]
  by_cases hi1 : i = 1
  · subst hi1; simp [h1]
  · have h2 : (2#32 : BitVec 32)[i] = false := by clear h1 h x; revert i hi hi1; decide
    simp [h2]

private theorem flags_andnot1_clean_3a (x : BitVec 32) (h : (x &&& 2#32) = 0#32) :
    ((x &&& ~~~1#32) &&& 2#32) = 0#32 := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  have h1 : x[1] = false := by
    have := congrArg (fun b : BitVec 32 => b[1]) h; simpa using this
  simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]
  by_cases hi1 : i = 1
  · subst hi1; simp [h1]
  · have h2 : (2#32 : BitVec 32)[i] = false := by clear h1 h x; revert i hi hi1; decide
    simp [h2]

private theorem list_filterMap_congr_mem_3a {α β : Type} {xs : List α} {f g : α → Option β}
    (h : ∀ x ∈ xs, f x = g x) : xs.filterMap f = xs.filterMap g := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    simp only [List.filterMap_cons, h x List.mem_cons_self]
    rw [ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

private theorem kittenPropAssign_preserves {acap : Nat} {ks : KittenState}
    (hinv : ks.Inv acap) (hsync : KittenTrailSynced ks)
    {lit rsn : BitVec 32} (hlit : lit.toNat < 2 * ks.nv.toNat)
    (hval0 : ks.vals[lit.toNat]? = some 0#32)
    (hrsn_lt : rsn.toNat < ks.nc.toNat) (hmem : lit.toNat ∈ kittenClauseLits ks rsn.toNat)
    (hfals : ∀ x ∈ kittenClauseLits ks rsn.toNat, x ≠ lit.toNat → ks.vals[x]? = some 2#32)
    (hunit : ks.lvl = 0#32 → ks.ante ≠ 0#32 → kittenClauseLits ks rsn.toNat = [lit.toNat]) :
    let ks' := kittenAssignStep ks lit rsn
    ks'.Inv acap ∧ KittenTrailSynced ks' ∧ PropFrame ks ks' ∧ ks'.prop = ks.prop ∧
    ks'.trl_end.toNat = ks.trl_end.toNat + 1 ∧
    (∀ i < ks.trl_end.toNat, ks'.trl[i]? = ks.trl[i]?) ∧
    (∀ {l ch done todo prev w}, WChainCursor ks l ch done todo prev w →
      WChainCursor ks' l ch done todo prev w) := by
  intro ks'
  have hsh := hinv.shapes
  have hcl := hinv.clauses
  have hba := hinv.assign
  have hnv := hcl.nv_le
  have hnc := hcl.nc_le
  have hte_lt := trl_end_lt_of_unassigned hsh hnv hba hlit hval0
  have hte1 : (ks.trl_end + 1#32).toNat = ks.trl_end.toNat + 1 := by
    unfold kMaxV at hnv; bv_omega
  have hte' : ks'.trl_end.toNat = ks.trl_end.toNat + 1 := hte1
  have hsh' : ks'.ShapesOk acap := kittenAssignStep_preserves_shapes hsh lit rsn
  obtain ⟨hv_div, hv_lt⟩ := bv32_lit_div2_bv hlit
  have hnl_pair := bv32_xor1_eq_litNeg hlit
  have hnl_eq : (lit ^^^ 1#32).toNat = litNeg lit.toNat := by
    simpa [bv32_one_eq] using hnl_pair.1
  have hnl_lt : litNeg lit.toNat < 2 * ks.nv.toNat := hnl_pair.2
  let v := (lit >>> 1).toNat
  let li := lit.toNat
  let nli := (lit ^^^ 1#32).toNat
  have hv_eq : v = li / 2 := hv_div
  have hli_lt : li < 2 * ks.nv.toNat := hlit
  have hnli_lt : nli < 2 * ks.nv.toNat := by dsimp only [nli]; rw [hnl_eq]; exact hnl_lt
  have hli_256 : li < 256 := by unfold kMaxV at hnv; omega
  have hnli_256 : nli < 256 := by unfold kMaxV at hnv; omega
  have hli_len : li < ks.vals.length := by rw [hsh.vals_len]; exact hli_256
  have hnli_len : nli < ks.vals.length := by rw [hsh.vals_len]; exact hnli_256
  have hv_128 : v < 128 := by dsimp only [v]; unfold kMaxV at hnv; omega
  have hla_len : v < ks.lvlArr.length := by rw [hsh.lvlArr_len]; exact hv_128
  have hrs_len : v < ks.rsn.length := by rw [hsh.rsn_len]; exact hv_128
  have hfl_len : v < ks.flags.length := by rw [hsh.flags_len]; exact hv_128
  have hte_128 : ks.trl_end.toNat < 128 := by unfold kMaxV at hnv; omega
  have htrl_len : ks.trl_end.toNat < ks.trl.length := by rw [hsh.trl_len]; exact hte_128
  have hne_li_nli : li ≠ nli := by
    dsimp only [li, nli]; rw [hnl_eq, ← litNeg_eq_xor1]
    rcases nat_xor1_cases lit.toNat with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have hnli_div : nli / 2 = v := by
    dsimp only [nli]; rw [hnl_eq, hv_eq, ← litNeg_eq_xor1]
    rcases nat_xor1_cases lit.toNat with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have hv_not_trl : ∀ i < ks.trl_end.toNat, (ks.trl[i]?.getD 0#32).toNat / 2 ≠ v := by
    intro i hi heq
    have hnz := (hba.vals_nz_iff_trl li hlit).mpr ⟨i, hi, by rw [← hv_eq]; exact heq⟩
    rw [hval0] at hnz; exact hnz rfl
  have hval0_nli : ks.vals[nli]? = some 0#32 := by
    by_cases he : ks.vals[nli]?.getD 0#32 = 0#32
    · rw [List.getElem?_eq_getElem hnli_len, Option.getD_some] at he
      rw [List.getElem?_eq_getElem hnli_len, he]
    · obtain ⟨i, hi, hveq⟩ := (hba.vals_nz_iff_trl nli hnli_lt).mp he
      exact absurd (by rw [← hnli_div]; exact hveq) (hv_not_trl i hi)
  have hdiv_cases : ∀ l < 2 * ks.nv.toNat, l / 2 = v → l = li ∨ l = nli := by
    intro l _ hdv
    rw [hv_eq] at hdv; dsimp only [li, nli] at hdv ⊢
    rw [hnl_eq, ← litNeg_eq_xor1]
    rcases nat_xor1_cases lit.toNat with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have hvals_ne : ∀ l < 2 * ks.nv.toNat, l / 2 ≠ v →
      ks'.vals[l]? = ks.vals[l]? := by
    intro l hl hdv
    have h1 : li ≠ l := fun h => hdv (by rw [← h, ← hv_eq])
    have h2 : nli ≠ l := fun h => hdv (by rw [← h, ← hnli_div])
    change ((ks.vals.set li 1#32).set nli 2#32)[l]? = ks.vals[l]?
    rw [List.getElem?_set_ne h2, List.getElem?_set_ne h1]
  have hvals_li : ks'.vals[li]? = some 1#32 := by
    change ((ks.vals.set li 1#32).set nli 2#32)[li]? = some 1#32
    rw [List.getElem?_set_ne hne_li_nli.symm, List.getElem?_set_self hli_len]
  have hvals_nli : ks'.vals[nli]? = some 2#32 := by
    change ((ks.vals.set li 1#32).set nli 2#32)[nli]? = some 2#32
    rw [List.getElem?_set_self (by simp [hnli_len])]
  have htrl_old : ∀ i < ks.trl_end.toNat, ks'.trl[i]? = ks.trl[i]? := fun i hi => by
    change (ks.trl.set ks.trl_end.toNat lit)[i]? = ks.trl[i]?
    exact List.getElem?_set_ne (by omega)
  have htrl_new : ks'.trl[ks.trl_end.toNat]? = some lit := by
    change (ks.trl.set ks.trl_end.toNat lit)[ks.trl_end.toNat]? = some lit
    exact List.getElem?_set_self htrl_len
  have htrl_take : ks'.trl.take ks'.trl_end.toNat =
      ks.trl.take ks.trl_end.toNat ++ [lit] := by
    have hte_eq : ks'.trl_end.toNat = ks.trl_end.toNat + 1 := hte1
    apply List.ext_getElem
    · simp only [hte_eq, List.length_take, List.length_append, List.length_singleton,
        hsh'.trl_len, hsh.trl_len]
      omega
    · intro i hi1 hi2
      have hi' : i < ks.trl_end.toNat + 1 := by
        simp only [hte_eq, List.length_take] at hi1; omega
      simp only [hte_eq, List.getElem_take]
      by_cases hil : i < ks.trl_end.toNat
      · rw [List.getElem_append_left (by simp [List.length_take]; omega), List.getElem_take]
        have heq := htrl_old i hil
        rw [List.getElem?_eq_getElem (by rw [hsh'.trl_len]; omega),
          List.getElem?_eq_getElem (by rw [hsh.trl_len]; omega)] at heq
        exact Option.some.inj heq
      · have hie : i = ks.trl_end.toNat := by omega
        subst hie
        rw [List.getElem_append_right (by simp [List.length_take]; omega)]
        simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt htrl_len), Nat.sub_self,
          List.getElem_singleton]
        exact List.getElem_set_self (by simpa using htrl_len)
  have hcl' : KittenClausesOk acap ks' := by
    refine ⟨hcl.acap_ge, hcl.acap_lt, hcl.acap_eq, hcl.nv_le, hcl.nc_le, hcl.orig_nc_le,
      hcl.orig_nc_max, hcl.alen_le, hcl.nassump_le, hcl.nunits_le, hcl.nres_le, hcl.nkl_le,
      hcl.nana_le, hcl.cl_wf, hcl.cl_mono, hcl.units_ok, ?_, hcl.failing_ok, hcl.assump_ok, ?_⟩
    · intro hi
      have hinc := hcl.incons_ok hi
      refine ⟨hinc.1, hinc.2.1, fun l hl => ?_⟩
      have hl_lt := (hcl.cl_wf _ hinc.1).2.2.2.1 l hl
      have hr := hinc.2.2 l hl
      have hdv : l / 2 ≠ v := by
        intro heq
        rcases hdiv_cases l hl_lt heq with rfl | rfl
        · rw [hr.1] at hval0; cases hval0
        · rw [hr.1] at hval0_nli; cases hval0_nli
      have hla_ne : ks'.lvlArr[l / 2]? = ks.lvlArr[l / 2]? :=
        List.getElem?_set_ne (Ne.symm hdv)
      have hrs_ne : ks'.rsn[l / 2]? = ks.rsn[l / 2]? :=
        List.getElem?_set_ne (Ne.symm hdv)
      rw [hvals_ne l hl_lt hdv, hla_ne, hrs_ne]
      exact hr
    · intro w hw
      change (ks.flags.set v (if (lit &&& 1#32) ≠ 0#32 then ks.flags[v]?.getD 0#32 ||| 1#32
        else ks.flags[v]?.getD 0#32 &&& ~~~1#32))[w]?.getD 0#32 &&& 2#32 = 0#32
      by_cases hwv : w = v
      · subst hwv
        have hclean := hcl.flags_clean _ hw
        rw [List.getElem?_set_self hfl_len, Option.getD_some]
        split
        · exact flags_or1_clean_3a _ hclean
        · exact flags_andnot1_clean_3a _ hclean
      · rw [List.getElem?_set_ne (Ne.symm hwv)]; exact hcl.flags_clean w hw
  have hba' : KittenBaseAssignOk ks' := by
    have hrsn_ne_ff : rsn ≠ 0xFFFFFFFF#32 := by
      intro h; have h' := congrArg BitVec.toNat h
      change rsn.toNat = 2 ^ 32 - 1 at h'; unfold kMaxCl at hnc; omega
    have hnv' : ks'.nv = ks.nv := rfl
    have hpr' : ks'.prop = ks.prop := rfl
    refine ⟨by rw [hte', hnv']; omega, by rw [hte', hpr']; have := hba.prop_le; omega,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hun0 : 0 < ks.unass.toNat := by have := hba.unass_eq; omega
      have hun' : ks'.unass.toNat = ks.unass.toNat - 1 := by
        change (if ks.unass.toNat > 0 then ks.unass - 1#32 else ks.unass).toNat = ks.unass.toNat - 1
        simp only [hun0, ↓reduceIte]; bv_omega
      rw [hun', hte', hnv']; have := hba.unass_eq; omega
    · intro l hl
      rw [hnv'] at hl
      by_cases h1 : l = nli
      · subst h1; simp [hvals_nli]
      · by_cases h2 : l = li
        · subst h2; simp [hvals_li]
        · have hdv : l / 2 ≠ v := fun hd => (hdiv_cases l hl hd).elim h2 h1
          rw [hvals_ne l hl hdv]; exact hba.vals_dom l hl
    · intro l hl
      rw [hnv'] at hl
      have hxl_lt : l ^^^ 1 < 2 * ks.nv.toNat := by
        rcases nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
      by_cases h1 : l = li
      · subst h1; have hxo : li ^^^ 1 = nli := by dsimp only [li, nli]; rw [hnl_eq, litNeg_eq_xor1]
        simp [hvals_li, hxo, hvals_nli]
      · by_cases h2 : l = nli
        · subst h2
          have hxo : nli ^^^ 1 = li := by
            dsimp only [li, nli]; rw [hnl_eq, litNeg_eq_xor1, litNeg_litNeg]
          simp [hvals_nli, hxo, hvals_li]
        · have hdv : l / 2 ≠ v := fun hd => (hdiv_cases l hl hd).elim h1 h2
          have hdv_x : (l ^^^ 1) / 2 ≠ v := by
            rcases nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
          rw [hvals_ne l hl hdv, hvals_ne (l ^^^ 1) hxl_lt hdv_x]
          exact hba.vals_neg_iff l hl
    · intro l hl
      rw [hnv'] at hl
      by_cases hdv : l / 2 = v
      · constructor
        · intro _; refine ⟨ks.trl_end.toNat, by rw [hte']; omega, ?_⟩
          rw [htrl_new, Option.getD_some, ← hv_eq]; exact hdv.symm
        · intro _
          rcases hdiv_cases l hl hdv with rfl | rfl
          · simp [hvals_li]
          · simp [hvals_nli]
      · rw [hvals_ne l hl hdv]
        constructor
        · intro hnz
          obtain ⟨i, hi, heq⟩ := (hba.vals_nz_iff_trl l hl).mp hnz
          refine ⟨i, by rw [hte']; omega, ?_⟩
          rw [htrl_old i hi]; exact heq
        · rintro ⟨i, hi, heq⟩
          rw [hte'] at hi
          by_cases hie : i = ks.trl_end.toNat
          · subst hie
            rw [htrl_new, Option.getD_some, ← hv_eq] at heq
            exact absurd heq.symm hdv
          · have hi0 : i < ks.trl_end.toNat := by omega
            rw [htrl_old i hi0] at heq
            exact (hba.vals_nz_iff_trl l hl).mpr ⟨i, hi0, heq⟩
    · unfold kittenTrailLits
      rw [htrl_take, List.map_append, List.map_append, List.map_singleton, List.map_singleton,
        List.nodup_append]
      refine ⟨hba.trl_nodup, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
        fun x hx y hy hxy => ?_⟩
      simp only [List.mem_singleton] at hy; subst hy
      rw [List.mem_map] at hx; obtain ⟨t, ht, htv⟩ := hx
      rw [List.mem_map] at ht; obtain ⟨bv, hbv, rfl⟩ := ht
      obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hbv
      have hi_te : i < ks.trl_end.toNat := by simp at hi; omega
      have hti : (ks.trl[i]?.getD 0#32).toNat = bv.toNat := by
        simp only [List.getElem_take] at heq
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some, heq]
      exact hv_not_trl i hi_te (by rw [hti, htv, hxy, hv_eq])
    · intro l hl_m
      rw [hnv']
      unfold kittenTrailLits at hl_m
      rw [htrl_take, List.map_append, List.map_singleton, List.mem_append,
        List.mem_singleton] at hl_m
      rcases hl_m with hm | rfl
      · exact hba.trl_lt l hm
      · exact hlit
    · intro w hw
      rw [hnv'] at hw
      by_cases hwv : w = v
      · subst hwv
        change ((ks.lvlArr.set v ks.lvl)[v]?.getD 0#32).toNat ≤ ks.lvl.toNat
        rw [List.getElem?_set_self hla_len, Option.getD_some]
        exact Nat.le_refl _
      · change ((ks.lvlArr.set v ks.lvl)[w]?.getD 0#32).toNat ≤ ks.lvl.toNat
        rw [List.getElem?_set_ne (Ne.symm hwv)]
        exact hba.trl_lvl_le w hw
    · intro w hw h0
      rw [hnv'] at hw
      have h2w : 2 * w < 2 * ks.nv.toNat := by omega
      have h2wd : (2 * w) / 2 = w := by omega
      have hwv : w ≠ v := by
        intro heq; subst heq
        rcases hdiv_cases (2 * v) h2w h2wd with h | h
        · rw [h, hvals_li] at h0; cases h0
        · rw [h, hvals_nli] at h0; cases h0
      rw [hvals_ne (2 * w) h2w (by rw [h2wd]; exact hwv)] at h0
      change (ks.lvlArr.set v ks.lvl)[w]?.getD 0#32 = 0#32 ∧
        (ks.rsn.set v rsn)[w]?.getD 0#32 = 0xFFFFFFFF#32
      rw [List.getElem?_set_ne (Ne.symm hwv), List.getElem?_set_ne (Ne.symm hwv)]
      exact hba.unass_lvl_zero w hw h0
    · intro i j hij hj
      rw [hte'] at hj
      by_cases hje : j = ks.trl_end.toNat
      · subst hje
        have htl_j : ks'.trl[ks.trl_end.toNat]?.getD 0#32 = lit := by
          rw [htrl_new, Option.getD_some]
        rw [htl_j]
        change _ ≤ (ks'.lvlArr[v]?.getD 0#32).toNat
        have hla_v : ks'.lvlArr[v]?.getD 0#32 = ks.lvl := by
          change (ks.lvlArr.set v ks.lvl)[v]?.getD 0#32 = ks.lvl
          rw [List.getElem?_set_self hla_len, Option.getD_some]
        rw [hla_v]
        by_cases hie : i = ks.trl_end.toNat
        · subst hie; rw [htrl_new, Option.getD_some, ← hv_eq, hla_v]; exact Nat.le_refl _
        · have hi0 : i < ks.trl_end.toNat := by omega
          rw [htrl_old i hi0]
          have hvi : (ks.trl[i]?.getD 0#32).toNat / 2 < ks.nv.toNat := by
            have := hba.trl_lt _ (mem_kittenTrailLits_of_lt hi0 (Nat.le_of_lt htrl_len))
            omega
          have hne_iv := hv_not_trl i hi0
          change ((ks.lvlArr.set v ks.lvl)[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ _
          rw [List.getElem?_set_ne (Ne.symm hne_iv)]
          exact hba.trl_lvl_le _ hvi
      · have hj0 : j < ks.trl_end.toNat := by omega
        have hi0 : i < ks.trl_end.toNat := by omega
        rw [htrl_old i hi0, htrl_old j hj0]
        change ((ks.lvlArr.set v ks.lvl)[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
          ((ks.lvlArr.set v ks.lvl)[(ks.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
        rw [List.getElem?_set_ne (Ne.symm (hv_not_trl i hi0)),
          List.getElem?_set_ne (Ne.symm (hv_not_trl j hj0))]
        exact hba.trl_lvl_mono i j hij hj0
    · intro i j hji hi heq
      rw [hte'] at hi
      by_cases hie : i = ks.trl_end.toNat
      · subst hie
        rw [htrl_new, Option.getD_some, ← hv_eq]
        change (ks.rsn.set v rsn)[v]?.getD 0#32 ≠ 0xFFFFFFFF#32
        rw [List.getElem?_set_self hrs_len, Option.getD_some]
        exact hrsn_ne_ff
      · have hi0 : i < ks.trl_end.toNat := by omega
        have hj0 : j < ks.trl_end.toNat := by omega
        rw [htrl_old i hi0, htrl_old j hj0] at heq; rw [htrl_old i hi0]
        change (ks.lvlArr.set v ks.lvl)[(ks.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32 =
            (ks.lvlArr.set v ks.lvl)[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 at heq
        rw [List.getElem?_set_ne (Ne.symm (hv_not_trl j hj0)),
          List.getElem?_set_ne (Ne.symm (hv_not_trl i hi0))] at heq
        change (ks.rsn.set v rsn)[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 ≠ 0xFFFFFFFF#32
        rw [List.getElem?_set_ne (Ne.symm (hv_not_trl i hi0))]
        exact hba.dec_earliest i j hji hi0 heq
    · intro i hi
      dsimp only
      intro hlv0
      rw [hte'] at hi
      have horig : kittenOrigClauses ks' = kittenOrigClauses ks := rfl
      by_cases hie : i = ks.trl_end.toNat
      · subst hie
        rw [htrl_new, Option.getD_some] at hlv0 ⊢
        have hlvl_zero : ks.lvl = 0#32 := by
          change (ks.lvlArr.set v ks.lvl)[li / 2]?.getD 0#32 = 0#32 at hlv0
          rw [← hv_eq, List.getElem?_set_self hla_len, Option.getD_some] at hlv0
          exact hlv0
        have hrs_v : ks'.rsn[li / 2]?.getD 0#32 = rsn := by
          change (ks.rsn.set v rsn)[li / 2]?.getD 0#32 = rsn
          rw [← hv_eq, List.getElem?_set_self hrs_len, Option.getD_some]
        have hrs_v_ff : ks'.rsn[li / 2]?.getD 0xFFFFFFFF#32 = rsn := by
          change (ks.rsn.set v rsn)[li / 2]?.getD 0xFFFFFFFF#32 = rsn
          rw [← hv_eq, List.getElem?_set_self hrs_len, Option.getD_some]
        have hxo : li ^^^ 1 = nli := by dsimp only [li, nli]; rw [hnl_eq, litNeg_eq_xor1]
        refine ⟨by rw [hrs_v]; exact hrsn_ne_ff, hvals_li,
          by change ks'.vals[li ^^^ 1]? = some 2#32; rw [hxo]; exact hvals_nli,
          ?_, fun ha => by
            rw [hrs_v_ff]
            exact ⟨hrsn_lt, hunit hlvl_zero ha⟩⟩
        rw [horig]
        refine cnf_entails_unit_of_falsified_others (hcl.cl_wf rsn.toNat hrsn_lt).2.2.2.2.1 hmem
          fun x hx hne => ?_
        have hx_lt := (hcl.cl_wf rsn.toNat hrsn_lt).2.2.2.1 x hx
        have hxf := hfals x hx hne
        obtain ⟨j, hj, hj_eq⟩ := kitten_falsified_to_trail hsh hnv hba hsync hx_lt hxf
        have hlv_j : ks.lvlArr[(ks.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32 = 0#32 := by
          have hle := hba.trl_lvl_le ((ks.trl[j]?.getD 0#32).toNat / 2) (by
            have := hba.trl_lt _ (mem_kittenTrailLits_of_lt hj (Nat.le_of_lt htrl_len)); omega)
          rw [hlvl_zero, show (0#32 : BitVec 32).toNat = 0 from rfl] at hle
          exact BitVec.eq_of_toNat_eq (by change _ = 0; omega)
        have hjl := hba.lvl0_ok j hj hlv_j
        simpa [hj_eq] using hjl.2.2.2.1
      · have hi0 : i < ks.trl_end.toNat := by omega
        rw [htrl_old i hi0] at hlv0 ⊢
        have hne_i := hv_not_trl i hi0
        have hla_i : ks'.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 =
            ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 := by
          change (ks.lvlArr.set v ks.lvl)[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 = _
          rw [List.getElem?_set_ne (Ne.symm hne_i)]
        rw [hla_i] at hlv0
        have hl0 := hba.lvl0_ok i hi0 hlv0
        have hl_lt := hba.trl_lt _ (mem_kittenTrailLits_of_lt hi0 (Nat.le_of_lt htrl_len))
        have hxl_lt : (ks.trl[i]?.getD 0#32).toNat ^^^ 1 < 2 * ks.nv.toNat := by
          rcases nat_xor1_cases (ks.trl[i]?.getD 0#32).toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
        have hdv_x : ((ks.trl[i]?.getD 0#32).toNat ^^^ 1) / 2 ≠ v := by
          rcases nat_xor1_cases (ks.trl[i]?.getD 0#32).toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
        have hrs_i1 : ks'.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 =
            ks.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 := by
          change (ks.rsn.set v rsn)[_]?.getD 0#32 = _; rw [List.getElem?_set_ne (Ne.symm hne_i)]
        have hrs_i2 : ks'.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
            ks.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 := by
          change (ks.rsn.set v rsn)[_]?.getD 0xFFFFFFFF#32 = _
          rw [List.getElem?_set_ne (Ne.symm hne_i)]
        rw [hrs_i1, hvals_ne _ hl_lt hne_i, hvals_ne _ hxl_lt hdv_x, horig, hrs_i2]
        exact hl0
  have hsync' : KittenTrailSynced ks' := by
    intro i hi
    dsimp only
    rw [hte'] at hi
    by_cases hie : i = ks.trl_end.toNat
    · subst hie
      rw [htrl_new, Option.getD_some]
      have hxo : li ^^^ 1 = nli := by dsimp only [li, nli]; rw [hnl_eq, litNeg_eq_xor1]
      exact ⟨hvals_li, by change ks'.vals[li ^^^ 1]? = some 2#32; rw [hxo]; exact hvals_nli⟩
    · have hi0 : i < ks.trl_end.toNat := by omega
      rw [htrl_old i hi0]
      have hne_i := hv_not_trl i hi0
      have hl_lt := hba.trl_lt _ (mem_kittenTrailLits_of_lt hi0 (Nat.le_of_lt htrl_len))
      have hxl_lt : (ks.trl[i]?.getD 0#32).toNat ^^^ 1 < 2 * ks.nv.toNat := by
        rcases nat_xor1_cases (ks.trl[i]?.getD 0#32).toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
      have hdv_x : ((ks.trl[i]?.getD 0#32).toNat ^^^ 1) / 2 ≠ v := by
        rcases nat_xor1_cases (ks.trl[i]?.getD 0#32).toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
      rw [hvals_ne _ hl_lt hne_i, hvals_ne _ hxl_lt hdv_x]
      exact hsync i hi0
  have hrsn' : ReasonOk ks' := by
    intro i hi
    dsimp only
    rw [hte'] at hi
    by_cases hie : i = ks.trl_end.toNat
    · subst hie
      rw [htrl_new, Option.getD_some]
      have hrs_v : ks'.rsn[li / 2]?.getD 0#32 = rsn := by
        change (ks.rsn.set v rsn)[li / 2]?.getD 0#32 = rsn
        rw [← hv_eq, List.getElem?_set_self hrs_len, Option.getD_some]
      rw [hrs_v]; right
      refine ⟨hrsn_lt, hmem, fun x hx hne => ?_⟩
      have hx_lt := (hcl.cl_wf rsn.toNat hrsn_lt).2.2.2.1 x hx
      obtain ⟨j, hj, hj_eq⟩ := kitten_falsified_to_trail hsh hnv hba hsync hx_lt (hfals x hx hne)
      exact ⟨j, hj, by rw [htrl_old j hj, hj_eq, litNeg_eq_xor1]⟩
    · have hi0 : i < ks.trl_end.toNat := by omega
      have hne_i := hv_not_trl i hi0
      have hro := hinv.reasons i hi0
      dsimp only at hro ⊢
      rw [htrl_old i hi0]
      have hrs_i : ks'.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 =
          ks.rsn[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 := by
        change (ks.rsn.set v rsn)[_]?.getD 0#32 = _; rw [List.getElem?_set_ne (Ne.symm hne_i)]
      rw [hrs_i]
      rcases hro with hdec | ⟨hr_lt, hm, hall⟩
      · exact Or.inl hdec
      · right; refine ⟨hr_lt, hm, fun x hx hne => ?_⟩
        obtain ⟨j, hj, hj_eq⟩ := hall x hx hne
        exact ⟨j, hj, by rw [htrl_old j (Nat.lt_trans hj hi0)]; exact hj_eq⟩
  have hdec' : kittenTrailDecisions ks' = kittenTrailDecisions ks := by
    unfold kittenTrailDecisions
    rw [htrl_take, List.filterMap_append]
    have h1 : (ks.trl.take ks.trl_end.toNat).filterMap (fun l =>
          if ks'.rsn[l.toNat / 2]?.getD 0#32 = 0xFFFFFFFF#32 then some l.toNat else none) =
        (ks.trl.take ks.trl_end.toNat).filterMap (fun l =>
          if ks.rsn[l.toNat / 2]?.getD 0#32 = 0xFFFFFFFF#32 then some l.toNat else none) := by
      refine list_filterMap_congr_mem_3a fun l hl => ?_
      obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hl
      have hi_te : i < ks.trl_end.toNat := by simp at hi; omega
      simp only [List.getElem_take] at heq
      have hne : l.toNat / 2 ≠ v := by
        have := hv_not_trl i hi_te
        rwa [List.getElem?_eq_getElem (by omega), Option.getD_some, heq] at this
      have hrs_l : ks'.rsn[l.toNat / 2]?.getD 0#32 = ks.rsn[l.toNat / 2]?.getD 0#32 := by
        change (ks.rsn.set v rsn)[l.toNat / 2]?.getD 0#32 = _
        rw [List.getElem?_set_ne (Ne.symm hne)]
      rw [hrs_l]
    have hrsn_ne_ff : rsn ≠ 0xFFFFFFFF#32 := by
      intro h; have h' := congrArg BitVec.toNat h
      change rsn.toNat = 2 ^ 32 - 1 at h'; unfold kMaxCl at hnc; omega
    have h2 : [lit].filterMap (fun l =>
        if ks'.rsn[l.toNat / 2]?.getD 0#32 = 0xFFFFFFFF#32 then some l.toNat else none) = [] := by
      have hrs_v : ks'.rsn[lit.toNat / 2]?.getD 0#32 = rsn := by
        change (ks.rsn.set v rsn)[li / 2]?.getD 0#32 = rsn
        rw [← hv_eq, List.getElem?_set_self hrs_len, Option.getD_some]
      simp [hrs_v, hrsn_ne_ff]
    rw [h1, h2, List.append_nil]
  have hfr : PropFrame ks ks' := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, KittenCnfPermEquiv.refl _,
      fun _ _ => rfl, fun _ _ => rfl, hdec', by rw [hte']; omega, fun i hi => ?_⟩
    refine ⟨htrl_old i hi, ?_⟩
    change (ks.lvlArr.set v ks.lvl)[(ks.trl[i]?.getD 0#32).toNat / 2]? = _
    rw [List.getElem?_set_ne (Ne.symm (hv_not_trl i hi))]
  have hwc : ∀ {l ch done todo prev w}, WChainCursor ks l ch done todo prev w →
      WChainCursor ks' l ch done todo prev w := by
    intro l ch done todo prev w wc
    exact wc.transfer rfl rfl rfl rfl (Nat.le_refl _)
      (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ _ _ _ => rfl)
  exact ⟨⟨hsh', hcl', hinv.watches, hba', hrsn'⟩, hsync', hfr, rfl, hte', htrl_old, @hwc⟩

/-- Every literal of clause `c` sits at some slot `q < size` of the arena. -/
private theorem kittenClauseLits_mem_slot {ks : KittenState} {c x : Nat}
    (hx : x ∈ kittenClauseLits ks c) :
    ∃ q < kittenClauseSize ks c, (ks.arena[kittenClauseOff ks c + q]?.getD 0#32).toNat = x := by
  unfold kittenClauseLits at hx
  rw [List.mem_map] at hx
  obtain ⟨bv, hbv, rfl⟩ := hx
  obtain ⟨q, hq, hget⟩ := List.getElem_of_mem hbv
  simp only [List.length_take, List.length_drop] at hq
  refine ⟨q, by omega, ?_⟩
  simp only [List.getElem_take, List.getElem_drop] at hget
  rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hget]

/-! ## 4. `full_kitten_propagate_wp` (`10/15`) -/

/-- Pure facts for an unlinked watched clause (`ri = 0xFFFFFFFF#32`): every literal besides `other`
is falsified; at level `0` with active antecedents, non-`other` literals have unit reasons and
the original clauses entail `[other.toNat]`. -/
private theorem kitten_prop_unlinked_clause {acap w0 : Nat} {lit other : BitVec 32}
    {ksW ksK : KittenState} (hinvK : ksK.Inv acap) (hsyncK : KittenTrailSynced ksK)
    (hnl_val2W : ksW.vals[(lit ^^^ 1#32).toNat]? = some 2#32)
    (har_slot_l : (ksW.arena[kittenClauseOff ksW (w0 / 2) + w0 % 2]?.getD 0#32).toNat =
      (lit ^^^ 1#32).toNat)
    (hsz_eq_cs : (ksW.clMeta[w0 / 2]?.getD 0#32 &&& 0xFFFF#32).toNat =
      kittenClauseSize ksW (w0 / 2))
    (h_all2 : ∀ q, 2 ≤ q → q < (ksW.clMeta[w0 / 2]?.getD 0#32 &&& 0xFFFF#32).toNat →
      ksW.vals[(ksW.arena[(ksW.clOff[w0 / 2]?.getD 0#32).toNat + q]?.getD 0#32).toNat]? =
        some 2#32)
    (hva_eq : ksK.vals = ksW.vals) (har_eq : ksK.arena = ksW.arena)
    (hco_eq : ksK.clOff = ksW.clOff) (hcm_eq : ksK.clMeta = ksW.clMeta)
    (hcid_ltK : w0 / 2 < ksK.nc.toNat) (hother_mem : other.toNat ∈ kittenClauseLits ksW (w0 / 2))
    (hother_eq : other = ksW.arena[kittenClauseOff ksW (w0 / 2) + (w0 % 2 ^^^ 1)]?.getD 0#32) :
    (∀ x ∈ kittenClauseLits ksK (w0 / 2), x ≠ other.toNat → ksK.vals[x]? = some 2#32) ∧
    (ksK.lvl = 0#32 → ksK.ante ≠ 0#32 →
      (∀ l ∈ kittenClauseLits ksK (w0 / 2), l ≠ other.toNat →
        let r := (ksK.rsn[l / 2]?.getD 0xFFFFFFFF#32).toNat
        r < ksK.nc.toNat ∧ kittenClauseLits ksK r = [l ^^^ 1]) ∧
      (cnfOfClauses (kittenOrigClauses ksK)).EntailsClause (cnfClause [other.toNat])) := by
  have hk_sz : ∀ c, kittenClauseSize ksK c = kittenClauseSize ksW c := fun c => by
    unfold kittenClauseSize kittenClauseMeta; rw [hcm_eq]
  have hk_off : ∀ c, kittenClauseOff ksK c = kittenClauseOff ksW c := fun c => by
    unfold kittenClauseOff; rw [hco_eq]
  have hk_lits : ∀ c, kittenClauseLits ksK c = kittenClauseLits ksW c := fun c => by
    unfold kittenClauseLits; rw [har_eq, hk_off, hk_sz]
  have hfals : ∀ x ∈ kittenClauseLits ksK (w0 / 2), x ≠ other.toNat →
      ksK.vals[x]? = some 2#32 := by
    intro x hx hne
    obtain ⟨q, hq_sz, hqx⟩ := kittenClauseLits_mem_slot hx
    rw [hk_sz] at hq_sz
    have hq_szW : q < (ksW.clMeta[w0 / 2]?.getD 0#32 &&& 0xFFFF#32).toNat := by
      rw [hsz_eq_cs]; exact hq_sz
    have hqxW : (ksW.arena[(ksW.clOff[w0 / 2]?.getD 0#32).toNat + q]?.getD 0#32).toNat = x := by
      rw [har_eq, hk_off] at hqx; exact hqx
    rw [hva_eq]
    by_cases hqs : q = w0 % 2
    · rw [hqs] at hqxW
      have hxl : x = (lit ^^^ 1#32).toNat := by rw [← hqxW]; exact har_slot_l
      rw [hxl]; exact hnl_val2W
    · by_cases hqo : q = w0 % 2 ^^^ 1
      · exfalso; apply hne
        rw [← hqxW, hqo, hother_eq]; rfl
      · have hq2 : 2 ≤ q := by
          rcases Nat.mod_two_eq_zero_or_one w0 with h | h <;> simp [h] at hqs hqo <;> omega
        rw [← hqxW]; exact h_all2 q hq2 hq_szW
  refine ⟨hfals, fun hlvl0K hanteK => ?_⟩
  have htrl_lenK : ksK.trl_end.toNat ≤ ksK.trl.length := by
    rw [hinvK.shapes.trl_len]
    have := hinvK.assign.trl_end_le; have := hinvK.clauses.nv_le; unfold kMaxV at *; omega
  have htr_ex : ∀ l ∈ kittenClauseLits ksK (w0 / 2), l ≠ other.toNat →
      ∃ j < ksK.trl_end.toNat, (ksK.trl[j]?.getD 0#32).toNat = l ^^^ 1 ∧
        ksK.lvlArr[(ksK.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32 = 0#32 := by
    intro l hl hne
    have hl_lt := (hinvK.clauses.cl_wf (w0 / 2) hcid_ltK).2.2.2.1 l hl
    obtain ⟨j, hj, hj_eq⟩ := kitten_falsified_to_trail hinvK.shapes hinvK.clauses.nv_le
      hinvK.assign hsyncK hl_lt (hfals l hl hne)
    have hle := hinvK.assign.trl_lvl_le ((ksK.trl[j]?.getD 0#32).toNat / 2)
      (by have := hinvK.assign.trl_lt _ (mem_kittenTrailLits_of_lt hj htrl_lenK); omega)
    rw [hlvl0K, show (0#32 : BitVec 32).toNat = 0 from rfl] at hle
    exact ⟨j, hj, by rw [hj_eq, litNeg_eq_xor1], BitVec.eq_of_toNat_eq (by change _ = 0; omega)⟩
  refine ⟨fun l hl hne => ?_, ?_⟩
  · obtain ⟨j, hj, hj_eq, hlv0⟩ := htr_ex l hl hne
    have hdiv_x : (l ^^^ 1) / 2 = l / 2 := by
      rcases nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
    have hl0 := (hinvK.assign.lvl0_ok j hj hlv0).2.2.2.2 hanteK
    rw [hj_eq, hdiv_x] at hl0; exact hl0
  · refine cnf_entails_unit_of_falsified_others
      (hinvK.clauses.cl_wf (w0 / 2) hcid_ltK).2.2.2.2.1 (by rw [hk_lits]; exact hother_mem)
      fun l hl hne => ?_
    obtain ⟨j, hj, hj_eq, hlv0⟩ := htr_ex l hl hne
    have hl0 := (hinvK.assign.lvl0_ok j hj hlv0).2.2.2.1
    rw [hj_eq, litNeg_eq_xor1] at hl0; exact hl0

/-- Parametric `Func.wp` proof for `full_kitten_propagate`. -/
theorem full_kitten_propagate_wp (Γ : Env)
    (hAssign : ∀ args m Q X, fullKittenAssignSpec args m Q X →
      Γ "full_kitten_assign" [i64, i32, i32] [] args m Q X)
    (hLearn : ∀ args m Q X, fullKittenLearnUnit0Spec args m Q X →
      Γ "full_kitten_learn_unit0" [i64, i32, i32, .bool] [i32] args m Q X) :
    ∀ args m Q X, fullKittenPropagateSpec args m Q X →
      Func.wp Γ full_kitten_propagate_body args m Q X := by
  rintro ⟨kPtr, ⟨⟩⟩ m Q X ⟨acap, ks0, R, hinv0, hsync0, hm, hQ⟩
  have hmA := kittenMem_to_amem hinv0.shapes hm; clear hm
  have hret : ∀ (confl : BitVec 32) (ksF : KittenState) (mF : Mem 64),
      ksF.Inv acap → KittenTrailSynced ksF → PropFrame ks0 ksF →
      (confl = 0xFFFFFFFF#32 → ksF.prop = ksF.trl_end) →
      (confl ≠ 0xFFFFFFFF#32 → confl ≠ 0xFFFFFFFE#32 →
        confl.toNat < ksF.nc.toNat ∧
        ∀ l ∈ kittenClauseLits ksF confl.toNat, ksF.vals[l]? = some 2#32) →
      (KittenMemA kPtr acap ksF ⋆ R) mF → Q (confl, ()) mF := by
    intro confl ksF mF hinvF hsyncF hfr hpr hconfl hmF
    obtain ⟨_, hmF'⟩ := kittenMemA_to_mem hmF
    exact hQ confl ksF mF hinvF hsyncF hfr.nv hfr.orig_nc hfr.lvl hfr.incons hfr.failing
      hfr.ante hfr.nassump hfr.assump hfr.perm hfr.clAux hfr.clMetaCore hfr.te_ge
      hfr.dec hfr.trl hpr hconfl hmF'
  c0_hsteps_nogrp
  refine wp_while_state0 (α := KittenState)
    (fun st => ks0.nv.toNat - st.prop.toNat)
    (fun st m' => st.Inv acap ∧ KittenTrailSynced st ∧ PropFrame ks0 st ∧
      (KittenMemA kPtr acap st ⋆ R) m') ?_ ?_
  · intro L0 hL0
    exact hL0 ks0 m ⟨hinv0, hsync0, PropFrame.refl ks0, hmA⟩
  · intro L0 ksO mO ⟨hinvO, hsyncO, hfrO, hmO⟩ ihO
    dsimp only at hinvO hsyncO hfrO hmO ⊢
    c0_hsplit
    · have hpO_lt : ksO.prop.toNat < ksO.trl_end.toNat := hc
      have hshO := hinvO.shapes
      have hclO := hinvO.clauses
      have hbaO := hinvO.assign
      have hnvO := hclO.nv_le
      have hpO_128 : ksO.prop.toNat < 128 := by
        have := hbaO.trl_end_le; unfold kMaxV at hnvO; omega
      have hpO_28 : ksO.prop.toNat < 2 ^ 28 := by omega
      have hpO1_wrap : (ksO.prop + 1#32).toNat = ksO.prop.toNat + 1 := by
        rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (by omega)]
      let pO := ksO.prop
      let lit := ksO.trl[pO.toNat]?.getD 0#32
      have htrl_lenO : ksO.trl_end.toNat ≤ ksO.trl.length := by
        rw [hshO.trl_len]; have := hbaO.trl_end_le; unfold kMaxV at hnvO; omega
      have hlit_lt : lit.toNat < 2 * ksO.nv.toNat :=
        hbaO.trl_lt lit.toNat (mem_kittenTrailLits_of_lt hpO_lt htrl_lenO)
      have hnl_pair := bv32_xor1_eq_litNeg hlit_lt
      have hnl_eq : (lit ^^^ 1#32).toNat = litNeg lit.toNat := by
        simpa [bv32_one_eq] using hnl_pair.1
      have hnl_lt : (lit ^^^ 1#32).toNat < 2 * ksO.nv.toNat := by
        rw [hnl_eq]; exact hnl_pair.2
      have hnl_256 : (lit ^^^ 1#32).toNat < 256 := by unfold kMaxV at hnvO; omega
      have hnl_28 : (lit ^^^ 1#32).toNat < 2 ^ 28 := by omega
      let ksB := (ksO.putHdr .prop (pO + 1#32)).putHdr .ticks (ksO.ticks + 1#32)
      obtain ⟨hinvB, hsyncB, hfrB, hb_pr, hb_va, hb_tr, hb_te, _⟩ :=
        kittenBumpPropTicks_preserves hinvO hsyncO (pr' := pO + 1#32) (tk' := ksO.ticks + 1#32)
          (by dsimp only [pO]; omega)
      have hnl_ltB : (lit ^^^ 1#32).toNat < 2 * ksB.nv.toNat := by
        change _ < 2 * ksO.nv.toNat; exact hnl_lt
      obtain ⟨ch0, hwc0⟩ := WChainCursor.init hinvB.shapes hinvB.clauses.nv_le
        hinvB.watches hnl_ltB
      c0_hsteps_nogrp
      refine wp_while_state
        (proj := fun st : BitVec 32 × BitVec 32 × List Nat × List Nat × KittenState ×
          List (List Nat) => (st.1, st.2.1, ()))
        (fun st => st.2.2.2.1.length)
        (fun st m' =>
          let prev := st.1; let w := st.2.1; let done := st.2.2.1
          let todo := st.2.2.2.1; let ksW := st.2.2.2.2.1; let ch := st.2.2.2.2.2
          WChainCursor ksW (lit ^^^ 1#32).toNat ch done todo prev w ∧
          ksW.Inv acap ∧ KittenTrailSynced ksW ∧ PropFrame ks0 ksW ∧
          ksW.prop.toNat = pO.toNat + 1 ∧ pO.toNat < ksW.trl_end.toNat ∧
          ksW.trl[pO.toNat]? = some lit ∧ (KittenMemA kPtr acap ksW ⋆ R) m')
        ?_ ?_
      · intro L1 hL1
        have hlt_eq : ksO.trl[pO.toNat]? = some lit := by
          dsimp only [lit, pO]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        refine hL1 (0xFFFFFFFF#32, ksB.whead[(lit ^^^ 1#32).toNat]?.getD 0#32, [],
          ch0[(lit ^^^ 1#32).toNat]?.getD [], ksB, ch0) m
          ⟨hwc0, hinvB, hsyncB, hfrO.trans hfrB, by rw [hb_pr]; exact hpO1_wrap,
            by rw [hb_te]; exact hpO_lt, by rw [hb_tr]; exact hlt_eq, ?_⟩
        simpa only [ksB, bv32_one_eq, putHdr_ticks,
          show KHdrField.prop ≠ KHdrField.ticks from by decide, ↓reduceIte] using hm
      · intro L1 ⟨prev, w, done, todo, ksW, chW⟩ mW
          ⟨hwc, hinvW, hsyncW, hfrW, hw_pr, hw_te, hw_lit, hmW⟩ ihW
        dsimp only at hwc hinvW hsyncW hfrW hw_pr hw_te hw_lit hmW ⊢
        have hshW := hinvW.shapes
        have hclW := hinvW.clauses
        have hnvW := hclW.nv_le
        have hncW := hclW.nc_le
        have hw_nl_lt : (lit ^^^ 1#32).toNat < 2 * ksW.nv.toNat := by
          rw [hfrW.nv, ← hfrO.nv]; exact hnl_lt
        have hnl_val2W : ksW.vals[(lit ^^^ 1#32).toNat]? = some 2#32 := by
          have hs := (hsyncW pO.toNat hw_te).2
          rw [hw_lit, Option.getD_some] at hs
          have hxo : lit.toNat ^^^ 1 = (lit ^^^ 1#32).toNat := by
            rw [hnl_eq, litNeg_eq_xor1]
          rwa [hxo] at hs
        c0_hsplit
        · have hw_ne : w ≠ 0xFFFFFFFF#32 := ‹w ≠ 0xFFFFFFFF#32›
          obtain ⟨w0, todo', hw0_wn, rfl, rfl, hw0_nc, hw0_1792, hw_tn, hw_div2, hw_mod2,
            hsz_ge, har_slot_l, hwb_lt, htail_nxt⟩ :=
            hwc.step_unfold hshW hncW hw_nl_lt hw_ne
          have hw_28 : (BitVec.ofNat 32 w0).toNat < 2 ^ 28 := by omega
          have hw_1792 : (BitVec.ofNat 32 w0).toNat < 1792 := by omega
          have hwb_256 : (ksW.wblit[w0]?.getD 0#32).toNat < 256 := by unfold kMaxV at hnvW; omega
          have hwb_28 : (ksW.wblit[w0]?.getD 0#32).toNat < 2 ^ 28 := by omega
          have hwb_256' : (ksW.wblit[(BitVec.ofNat 32 w0).toNat]?.getD 0#32).toNat < 256 := by
            rw [hw_tn]; exact hwb_256
          have hwb_28' : (ksW.wblit[(BitVec.ofNat 32 w0).toNat]?.getD 0#32).toNat < 2 ^ 28 := by
            rw [hw_tn]; exact hwb_28
          c0_hsteps_nogrp
          try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
          c0_hsplit
          · c0_hsteps!
            rw [hw_tn]
            exact ihW (BitVec.ofNat 32 w0, ksW.wnext[w0]?.getD 0#32, done ++ [w0], todo',
              ksW, chW) mW (by dsimp; omega)
              ⟨hwc.advance hshW hncW hw_nl_lt hw0_nc, hinvW, hsyncW, hfrW,
                hw_pr, hw_te, hw_lit, hmW⟩
          · have hcid_lt : w0 / 2 < ksW.nc.toNat := by omega
            have hcid_896 : w0 / 2 < 896 := by unfold kMaxCl at hncW; omega
            have hcid_28 : w0 / 2 < 2 ^ 28 := by omega
            have hwf_c := hclW.cl_wf (w0 / 2) hcid_lt
            have hoff_ssz : kittenClauseOff ksW (w0 / 2) + kittenClauseSize ksW (w0 / 2) ≤
                ksW.alen.toNat := by
              have := hwf_c.2.2.1; unfold kittenClauseSpan at this; omega
            have hother_slot_lt : (w0 % 2 ^^^ 1) < kittenClauseSize ksW (w0 / 2) := by
              rcases Nat.mod_two_eq_zero_or_one w0 with h | h <;> simp [h] <;> omega
            have har_idx_ok : ∀ i < kittenClauseSize ksW (w0 / 2),
                kittenClauseOff ksW (w0 / 2) + i < acap ∧
                kittenClauseOff ksW (w0 / 2) + i < 2 ^ 28 ∧
                (ksW.arena[kittenClauseOff ksW (w0 / 2) + i]?.getD 0#32).toNat ∈
                  kittenClauseLits ksW (w0 / 2) ∧
                (ksW.arena[kittenClauseOff ksW (w0 / 2) + i]?.getD 0#32).toNat <
                  2 * ksW.nv.toNat := by
              intro i hi
              have hlen : kittenClauseOff ksW (w0 / 2) + i < ksW.arena.length := by
                rw [hshW.arena_len]; have := hclW.alen_le; omega
              have hcap : kittenClauseOff ksW (w0 / 2) + i < acap := by
                have := hclW.alen_le; omega
              have hwrp : kittenClauseOff ksW (w0 / 2) + i < 2 ^ 28 := by
                have := hclW.acap_lt; unfold dimacsBound at *; omega
              have hmem : (ksW.arena[kittenClauseOff ksW (w0 / 2) + i]'hlen).toNat ∈
                  kittenClauseLits ksW (w0 / 2) := by
                unfold kittenClauseLits; rw [List.mem_map]
                refine ⟨_, ?_, rfl⟩; rw [List.mem_iff_getElem]
                exact ⟨i, by
                    simp [List.length_take, List.length_drop, hshW.arena_len]
                    have := hclW.alen_le; omega,
                  by simp [List.getElem_take, List.getElem_drop]⟩
              rw [List.getElem?_eq_getElem hlen, Option.getD_some]
              exact ⟨hcap, hwrp, hmem, hwf_c.2.2.2.1 _ hmem⟩
            let other := ksW.arena[kittenClauseOff ksW (w0 / 2) + (w0 % 2 ^^^ 1)]?.getD 0#32
            have hother_mem : other.toNat ∈ kittenClauseLits ksW (w0 / 2) :=
              (har_idx_ok _ hother_slot_lt).2.2.1
            have hother_nv : other.toNat < 2 * ksW.nv.toNat :=
              (har_idx_ok _ hother_slot_lt).2.2.2
            have hother_256 : other.toNat < 256 := by unfold kMaxV at hnvW; omega
            have hother_28 : other.toNat < 2 ^ 28 := by omega
            have hw_sh1_nat : (BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat = w0 / 2 := by
              simp [Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega : w0 < 2 ^ 32)]
            have hw_sh1 : (BitVec.ofNat 32 w0 >>> (1 : BitVec 32)).toNat = w0 / 2 := by
              simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
                Nat.mod_eq_of_lt (by omega : w0 < 2 ^ 32)]
            have hslot_other_eq :
                (BitVec.ofNat 32 w0 &&& (1 : BitVec 32) ^^^ (1 : BitVec 32)).toNat =
                  w0 % 2 ^^^ 1 := by
              rw [BitVec.toNat_xor, BitVec.toNat_and, BitVec.toNat_ofNat,
                Nat.mod_eq_of_lt (by omega : w0 < 2 ^ 32)]
              simp [Nat.and_one_is_mod]
            have hslot_lt2 :
                (BitVec.ofNat 32 w0 &&& (1 : BitVec 32) ^^^ (1 : BitVec 32)).toNat < 2 := by
              rw [hslot_other_eq]; rcases Nat.mod_two_eq_zero_or_one w0 with h | h <;> simp [h]
            have hcl_off_wrap :
                (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32).toNat +
                  (BitVec.ofNat 32 w0 &&& (1 : BitVec 32) ^^^ (1 : BitVec 32)).toNat <
                  2 ^ 28 := by
              rw [hw_sh1_nat]; change kittenClauseOff ksW (w0 / 2) + _ < 2 ^ 28
              have := hclW.alen_le; have := hclW.acap_lt; unfold dimacsBound at *; omega
            have hcl_off_acap :
                (ksW.clOff[(BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat]?.getD 0#32).toNat +
                  (BitVec.ofNat 32 w0 &&& (1 : BitVec 32) ^^^ (1 : BitVec 32)).toNat <
                  acap := by
              rw [hw_sh1_nat]; change kittenClauseOff ksW (w0 / 2) + _ < acap
              have := hclW.alen_le; omega
            have hother_bv_256 :
                (ksW.arena[(ksW.clOff[(BitVec.ofNat 32 w0 >>>
                    (1 : Nat)).toNat]?.getD 0#32).toNat +
                  (BitVec.ofNat 32 w0 &&& (1 : BitVec 32) ^^^ (1 : BitVec 32)).toNat]?.getD
                  0#32).toNat < 256 := by
              rw [hw_sh1_nat, hslot_other_eq]; exact hother_256
            have hother_bv_28 :
                (ksW.arena[(ksW.clOff[(BitVec.ofNat 32 w0 >>>
                    (1 : Nat)).toNat]?.getD 0#32).toNat +
                  (BitVec.ofNat 32 w0 &&& (1 : BitVec 32) ^^^ (1 : BitVec 32)).toNat]?.getD
                  0#32).toNat < 2 ^ 28 := by omega
            c0_hsteps_nogrp
            try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
            c0_hsplit
            · obtain ⟨hkp_inv, hkp_sync, hkp_wc, hkp_nv, hkp_nc, hkp_on, hkp_lv, hkp_pr, hkp_te,
                  _, hkp_in, hkp_fa, hkp_an, hkp_na, hkp_as, _, hkp_la, hkp_rs, hkp_tr,
                  _, _, hkp_ca, _⟩ :=
                kittenWatchKeep_preserves hshW hinvW hsyncW hw_nl_lt hwc hother_nv
              have hkp_cm : ∀ (c : Nat), (ksW.putArr .wblit w0 other).clMeta[c]? = ksW.clMeta[c]? :=
                fun _ => rfl
              have hkp_orig : kittenOrigClauses (ksW.putArr .wblit w0 other) =
                  kittenOrigClauses ksW := rfl
              have hfr_keep : PropFrame ksW (ksW.putArr .wblit w0 other) :=
                PropFrame.of_eq hkp_nv hkp_on hkp_lv hkp_in hkp_fa hkp_an hkp_na hkp_as
                  (by rw [hkp_orig]; exact KittenCnfPermEquiv.refl _) (fun _ _ => by rw [hkp_ca])
                  (fun ci _ => by rw [hkp_cm ci]) hkp_te hkp_tr hkp_la hkp_rs
              c0_hsteps!
              rw [hw_tn]
              exact ihW (BitVec.ofNat 32 w0, ksW.wnext[w0]?.getD 0#32, done ++ [w0],
                  todo', ksW.putArr .wblit w0 other, chW) m (by dsimp; omega)
                ⟨hkp_wc, hkp_inv, hkp_sync, hfrW.trans hfr_keep, by rw [hkp_pr]; exact hw_pr,
                  by rw [hkp_te]; exact hw_te, by rw [hkp_tr]; exact hw_lit, by
                    have hm' := hm
                    rw [hw_tn, hslot_other_eq, hw_sh1_nat] at hm'
                    exact hm'⟩
            · let ksT := ksW.putHdr .ticks (ksW.ticks + 1#32)
              obtain ⟨hinvT, hsyncT, hfrT, ht_pr, ht_va, ht_tr, ht_te, hwcT⟩ :=
                kittenTicks_preserves hinvW hsyncW (ksW.ticks + 1#32)
              c0_hsteps_nogrp
              let sz := ksW.clMeta[w0 / 2]?.getD 0#32 &&& 0xFFFF#32
              let off := ksW.clOff[w0 / 2]?.getD 0#32
              have hsz_eq_cs : sz.toNat = kittenClauseSize ksW (w0 / 2) := rfl
              refine wp_while_break_state
                (projBrk := fun b : BitVec 32 × BitVec 32 × BitVec 32 =>
                  (b.1, b.2.1, b.2.2, ()))
                (fun b mb =>
                  (KittenMemA kPtr acap ksT ⋆ R) mb ∧
                  ((b.2.1 = 0xFFFFFFFF#32 ∧ ∀ q, 2 ≤ q → q < sz.toNat →
                    ksW.vals[(ksW.arena[off.toNat + q]?.getD 0#32).toNat]? = some 2#32) ∨
                   (2 ≤ b.2.1.toNat ∧ b.2.1.toNat < sz.toNat ∧
                    b.2.2 = ksW.arena[off.toNat + b.2.1.toNat]?.getD 0#32 ∧
                    ksW.vals[b.2.2.toNat]? ≠ some 2#32)))
                (projLp := fun st : BitVec 32 => (st, ()))
                (fun st => sz.toNat - st.toNat)
                (fun r m'' =>
                  (KittenMemA kPtr acap ksT ⋆ R) m'' ∧
                  r.toNat ≤ sz.toNat ∧ 2 ≤ r.toNat ∧
                  ∀ q, 2 ≤ q → q < r.toNat →
                    ksW.vals[(ksW.arena[off.toNat + q]?.getD 0#32).toNat]? = some 2#32)
                ?_ ?_ ?_
              · rintro B ⟨_r_fin, ri, repl⟩ mb ⟨hmb, hbrk⟩
                dsimp only at hbrk ⊢
                c0_hsplit
                · have hri_ne : ri ≠ 0xFFFFFFFF#32 := ‹ri ≠ 0xFFFFFFFF#32›
                  obtain ⟨hri_ge, hri_lt, hrepl_eq, hrepl_ne2⟩ :=
                    hbrk.resolve_left (fun h => hri_ne h.1)
                  have hri_lt' : ri.toNat < kittenClauseSize ksT (w0 / 2) := hri_lt
                  have hrepl_ne : repl.toNat ≠ (lit ^^^ 1#32).toNat := fun h =>
                    hrepl_ne2 (by rw [h]; exact hnl_val2W)
                  have hnl_ltT : (lit ^^^ 1#32).toNat < 2 * ksT.nv.toNat := hw_nl_lt
                  obtain ⟨hrl_inv, hrl_sync, _, _, _, hrl_perm, ⟨chR, hwcR⟩,
                      hrl_nv, hrl_nc, hrl_on, hrl_lv, hrl_pr, hrl_te, hrl_un,
                      hrl_in, hrl_fa, hrl_an, hrl_na, hrl_as, hrl_va,
                      hrl_la, hrl_rs, hrl_tr, _, hrl_cm, hrl_ca, _⟩ :=
                    kittenWatchReloc_preserves hinvT.shapes hinvT hsyncT hnl_ltT (hwcT hwc)
                      hri_ge hri_lt' hrepl_ne rfl hrepl_eq
                  have hfrR := PropFrame.of_eq hrl_nv hrl_on hrl_lv hrl_in hrl_fa hrl_an hrl_na
                    hrl_as hrl_perm (fun _ _ => by rw [hrl_ca]) (fun _ _ => by rw [hrl_cm])
                    hrl_te hrl_tr hrl_la hrl_rs
                  have hrl_prW := (congrArg BitVec.toNat (hrl_pr.trans ht_pr)).trans hw_pr
                  have hrl_teW : pO.toNat < _ := (hrl_te.trans ht_te).symm ▸ hw_te
                  have hrl_trW : _ = some lit :=
                    (congrArg (fun a => a[pO.toNat]?) (hrl_tr.trans ht_tr)).trans hw_lit
                  have hT_ar : ksT.arena = ksW.arena := rfl
                  have hT_wh : ksT.whead = ksW.whead := rfl
                  have hT_wn : ksT.wnext = ksW.wnext := rfl
                  have hT_wb : ksT.wblit = ksW.wblit := rfl
                  have hslot_ltW : w0 % 2 < kittenClauseSize ksW (w0 / 2) := by
                    have := Nat.mod_lt w0 (by decide : 0 < 2); omega
                  obtain ⟨hri_cap, hri_wrap, _, hri_lit⟩ := har_idx_ok ri.toNat hri_lt
                  obtain ⟨hslot_cap, hslot_wrap, _, _⟩ := har_idx_ok (w0 % 2) hslot_ltW
                  have hrepl_256 : repl.toNat < 256 := by
                    rw [hrepl_eq]
                    have : (ksW.arena[off.toNat + ri.toNat]?.getD 0#32).toNat < 2 * ksW.nv.toNat :=
                      hri_lit
                    unfold kMaxV at hnvW; omega
                  have hrepl_28 : repl.toNat < 2 ^ 28 := by omega
                  have hslot_eq : (BitVec.ofNat 32 w0 &&& (1 : BitVec 32)).toNat = w0 % 2 := by
                    rw [BitVec.toNat_and, BitVec.toNat_ofNat,
                      Nat.mod_eq_of_lt (by omega : w0 < 2 ^ 32)]
                    simp [Nat.and_one_is_mod]
                  have hslot_bv_wrap : (ksW.clOff[(BitVec.ofNat 32 w0 >>>
                      (1 : Nat)).toNat]?.getD 0#32).toNat +
                      (BitVec.ofNat 32 w0 &&& (1 : BitVec 32)).toNat < 2 ^ 28 := by
                    rw [hw_sh1_nat, hslot_eq]; exact hslot_wrap
                  have hslot_bv_cap : (ksW.clOff[(BitVec.ofNat 32 w0 >>>
                      (1 : Nat)).toNat]?.getD 0#32).toNat +
                      (BitVec.ofNat 32 w0 &&& (1 : BitVec 32)).toNat < acap := by
                    rw [hw_sh1_nat, hslot_eq]; exact hslot_cap
                  have hri_bv_wrap : (ksW.clOff[(BitVec.ofNat 32 w0 >>>
                      (1 : Nat)).toNat]?.getD 0#32).toNat + ri.toNat < 2 ^ 28 := by
                    rw [hw_sh1_nat]; exact hri_wrap
                  have hri_bv_cap : (ksW.clOff[(BitVec.ofNat 32 w0 >>>
                      (1 : Nat)).toNat]?.getD 0#32).toNat + ri.toNat < acap := by
                    rw [hw_sh1_nat]; exact hri_cap
                  have hnl_bv_256 : (lit ^^^ (1 : BitVec 32)).toNat < 256 := hnl_256
                  have hnl_bv_28 : (lit ^^^ (1 : BitVec 32)).toNat < 2 ^ 28 := hnl_28
                  have hprv_lt : prev ≠ 0xFFFFFFFF#32 → prev.toNat < 1792 := by
                    intro hp
                    rcases hwc.prev_rel with ⟨_, hpf, _⟩ | ⟨_, u, _, hp_eq, hu_len, _⟩
                    · exact absurd hpf hp
                    · rw [hp_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
                        rw [hshW.wnext_len] at hu_len; omega)]
                      rw [hshW.wnext_len] at hu_len; exact hu_len
                  c0_hsteps_nogrp
                  try refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                  c0_hsplit
                  · have hpeq : prev = 0xFFFFFFFF#32 := ‹prev = 0xFFFFFFFF#32›
                    c0_hsteps!
                    rw [hw_tn]
                    exact ihW (prev, ksW.wnext[w0]?.getD 0#32, done, todo', _, chR) _
                      (by dsimp; omega) ⟨hwcR, hrl_inv, hrl_sync, (hfrW.trans hfrT).trans hfrR,
                        hrl_prW, hrl_teW, hrl_trW, by
                          refine Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ R) _) ?_) hm
                          dsimp only [kittenWatchStep0, kittenClauseOff]
                          kstate_ext <;> (first | rfl | kp_field |
                            (simp [hT_ar, hT_wh, hT_wn, hT_wb, hw_tn, hw_div2, hw_mod2,
                              hpeq] <;> rfl))⟩
                  · have hpne : prev ≠ 0xFFFFFFFF#32 := ‹prev ≠ 0xFFFFFFFF#32›
                    have hprv_1792 := hprv_lt hpne
                    have hprv_28 : prev.toNat < 2 ^ 28 := by omega
                    c0_hsteps!
                    rw [hw_tn]
                    exact ihW (prev, ksW.wnext[w0]?.getD 0#32, done, todo', _, chR) _
                      (by dsimp; omega) ⟨hwcR, hrl_inv, hrl_sync, (hfrW.trans hfrT).trans hfrR,
                        hrl_prW, hrl_teW, hrl_trW, by
                          refine Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ R) _) ?_) hm
                          dsimp only [kittenWatchStep0, kittenClauseOff]
                          kstate_ext <;> (first | rfl | kp_field |
                            (simp [hT_ar, hT_wh, hT_wn, hT_wb, hw_tn, hw_div2, hw_mod2,
                              hpne] <;> rfl))⟩
                · have hri_eq : ri = 0xFFFFFFFF#32 := ‹ri = 0xFFFFFFFF#32›
                  have hsz_bd : sz.toNat < 65536 := by
                    dsimp only [sz]; rw [BitVec.toNat_and]
                    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
                  have h_all2 : ∀ q, 2 ≤ q → q < sz.toNat →
                      ksW.vals[(ksW.arena[off.toNat + q]?.getD 0#32).toNat]? = some 2#32 :=
                    (hbrk.resolve_right (by
                      intro h
                      have hlt := h.2.1
                      rw [hri_eq, show (0xFFFFFFFF#32 : BitVec 32).toNat = 4294967295 from rfl]
                        at hlt
                      omega)).2
                  have hnl_ltT : (lit ^^^ 1#32).toNat < 2 * ksT.nv.toNat := hw_nl_lt
                  have hother_nvT : other.toNat < 2 * ksT.nv.toNat := hother_nv
                  obtain ⟨hkp_inv, hkp_sync, hkp_wc, hkp_nv, hkp_nc, hkp_on, hkp_lv, hkp_pr,
                      hkp_te, _, hkp_in, hkp_fa, hkp_an, hkp_na, hkp_as, _, hkp_la, hkp_rs,
                      hkp_tr, _, _, hkp_ca, _⟩ :=
                    kittenWatchKeep_preserves hinvT.shapes hinvT hsyncT hnl_ltT (hwcT hwc)
                      hother_nvT
                  let ksK := ksT.putArr .wblit w0 other
                  have hinvK : ksK.Inv acap := hkp_inv
                  have hsyncK : KittenTrailSynced ksK := hkp_sync
                  have hkp_cm : ∀ c : Nat, ksK.clMeta[c]? = ksT.clMeta[c]? := fun _ => rfl
                  have hkp_orig : kittenOrigClauses ksK = kittenOrigClauses ksT := rfl
                  have hfr_k : PropFrame ksT ksK :=
                    PropFrame.of_eq hkp_nv hkp_on hkp_lv hkp_in hkp_fa hkp_an hkp_na hkp_as
                      (by rw [hkp_orig]; exact KittenCnfPermEquiv.refl _)
                      (fun _ _ => by rw [hkp_ca]) (fun ci _ => by rw [hkp_cm ci])
                      hkp_te hkp_tr hkp_la hkp_rs
                  have hfrK : PropFrame ks0 ksK := (hfrW.trans hfrT).trans hfr_k
                  have hcid_ltK : (BitVec.ofNat 32 w0 >>> (1 : Nat)).toNat < ksK.nc.toNat := by
                    rw [hkp_nc]; change _ < ksW.nc.toNat; rw [hw_sh1_nat]; exact hcid_lt
                  have hcid_nat_ltK : w0 / 2 < ksK.nc.toNat := by
                    rw [hkp_nc]; change w0 / 2 < ksW.nc.toNat; exact hcid_lt
                  obtain ⟨hclause_fals, hclause_ante⟩ := kitten_prop_unlinked_clause hinvK hsyncK
                    hnl_val2W har_slot_l hsz_eq_cs h_all2 rfl rfl rfl rfl hcid_nat_ltK
                    hother_mem rfl
                  have hother_bv_nat : ksW.arena[(ksW.clOff[(BitVec.ofNat 32 w0 >>>
                      (1 : Nat)).toNat]?.getD 0#32).toNat + (BitVec.ofNat 32 w0 &&&
                      (1 : BitVec 32) ^^^ (1 : BitVec 32)).toNat]?.getD 0#32 = other := by
                    dsimp only [other, kittenClauseOff]; rw [hw_sh1_nat, hslot_other_eq]
                  have hwm32 : w0 % 2 ^ 32 = w0 := Nat.mod_eq_of_lt (by omega)
                  c0_hsteps_nogrp
                  c0_hsplit
                  · have hov2 : ksK.vals[other.toNat]? = some 2#32 := by
                      have hc' : ksK.vals[other.toNat]?.getD 0#32 = 2#32 := by
                        rw [hwm32] at hc; exact hc
                      have hvl : other.toNat < ksK.vals.length := by
                        rw [hinvK.shapes.vals_len]; exact hother_256
                      rw [List.getElem?_eq_getElem hvl] at hc' ⊢
                      simpa using hc'
                    c0_hsteps!
                    have hmK : (KittenMemA kPtr acap ksK ⋆ R) m := by
                      have h1 := hm; rw [hw_tn, hother_bv_nat] at h1; exact h1
                    refine hret (BitVec.ofNat 32 w0 >>> (1 : Nat)) ksK _ hinvK hsyncK hfrK
                      (fun h => by
                        have := congrArg BitVec.toNat h; rw [hw_sh1_nat] at this
                        change w0 / 2 = 4294967295 at this; omega)
                      (fun _ _ => ⟨hcid_ltK, fun x hx => ?_⟩) hmK
                    by_cases hxo : x = other.toNat
                    · rw [hxo]; exact hov2
                    · rw [hw_sh1_nat] at hx; exact hclause_fals x hx hxo
                  · refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
                    c0_hsplit
                    · have hov0 : ksK.vals[other.toNat]? = some 0#32 := by
                        have hc' : ksK.vals[other.toNat]?.getD 0#32 = 0#32 := by
                          rw [hwm32] at hc; exact hc
                        have hvl : other.toNat < ksK.vals.length := by
                          rw [hinvK.shapes.vals_len]; exact hother_256
                        rw [List.getElem?_eq_getElem hvl] at hc' ⊢
                        simpa using hc'
                      have hmK : (KittenMemA kPtr acap ksK ⋆ R) m := by
                        have h1 := hm; rw [hw_tn, hother_bv_nat] at h1; exact h1
                      let cid : BitVec 32 := BitVec.ofNat 32 w0 >>> (1 : Nat)
                      c0_hsteps_nogrp
                      refine wp_join_state
                        (proj := fun st : BitVec 32 × KittenState => (st.1, ()))
                        (fun st mA =>
                          st.2.Inv acap ∧ KittenTrailSynced st.2 ∧ PropFrame ks0 st.2 ∧
                          st.2.prop.toNat = pO.toNat + 1 ∧ pO.toNat < st.2.trl_end.toNat ∧
                          st.2.trl[pO.toNat]? = some lit ∧
                          WChainCursor st.2 (lit ^^^ 1#32).toNat chW (done ++ [w0]) todo'
                            (BitVec.ofNat 32 w0) (ksW.wnext[w0]?.getD 0#32) ∧
                          other.toNat < 2 * st.2.nv.toNat ∧
                          st.2.vals[other.toNat]? = some 0#32 ∧
                          st.1.toNat < st.2.nc.toNat ∧
                          other.toNat ∈ kittenClauseLits st.2 st.1.toNat ∧
                          (∀ x ∈ kittenClauseLits st.2 st.1.toNat, x ≠ other.toNat →
                            st.2.vals[x]? = some 2#32) ∧
                          (st.2.lvl = 0#32 → st.2.ante ≠ 0#32 →
                            kittenClauseLits st.2 st.1.toNat = [other.toNat]) ∧
                          (KittenMemA kPtr acap st.2 ⋆ R) mA) ?_ ?_
                      · intro J_rsn ⟨rsn, ksA⟩ mA
                          ⟨hinvA, hsyncA, hfrA, ha_pr, ha_te, ha_lit, hwcA, ha_oth_lt, ha_val0,
                            ha_rsn_lt, ha_mem, ha_fals, ha_unit, hmA'⟩
                        dsimp only at hinvA hsyncA hfrA ha_pr ha_te ha_lit hwcA ha_oth_lt
                        dsimp only at ha_val0 ha_rsn_lt ha_mem ha_fals ha_unit hmA' ⊢
                        have hte_ltA := trl_end_lt_of_unassigned hinvA.shapes hinvA.clauses.nv_le
                          hinvA.assign ha_oth_lt ha_val0
                        c0_hsteps_nogrp
                        c0_call hAssign
                        obtain ⟨_, hmA_raw⟩ := kittenMemA_to_mem hmA'
                        refine ⟨acap, ksA, R, hinvA.shapes, hinvA.clauses.acap_lt,
                          hinvA.clauses.nv_le, by rw [hother_bv_nat]; exact ha_oth_lt,
                          hte_ltA, hmA_raw, fun mF hmF => ?_⟩
                        rw [hother_bv_nat] at hmF
                        obtain ⟨hinvF, hsyncF, hfr_af, hf_pr, hf_te, hf_trl, hwcF⟩ :=
                          kittenPropAssign_preserves hinvA hsyncA ha_oth_lt ha_val0 ha_rsn_lt
                            ha_mem ha_fals ha_unit
                        c0_hsteps!
                        rw [hw_tn]
                        exact ihW (BitVec.ofNat 32 w0, ksW.wnext[w0]?.getD 0#32, done ++ [w0],
                            todo', kittenAssignStep ksA other rsn, chW) mF (by dsimp; omega)
                          ⟨hwcF hwcA, hinvF, hsyncF, hfrA.trans hfr_af,
                            by rw [hf_pr]; exact ha_pr, by rw [hf_te]; omega,
                            by rw [hf_trl pO.toNat ha_te]; exact ha_lit,
                            kittenMem_to_amem hinvF.shapes hmF⟩
                      · intro J_rsn hJ_rsn
                        have hother_memK : other.toNat ∈ kittenClauseLits ksK cid.toNat := by
                          change other.toNat ∈ kittenClauseLits ksW cid.toNat
                          dsimp only [cid]; rw [hw_sh1_nat]; exact hother_mem
                        have hk_pr : ksK.prop.toNat = pO.toNat + 1 := by
                          rw [hkp_pr, ht_pr]; exact hw_pr
                        have hk_te : pO.toNat < ksK.trl_end.toNat := by
                          rw [hkp_te, ht_te]; exact hw_te
                        have hk_lit : ksK.trl[pO.toNat]? = some lit := by
                          rw [hkp_tr, ht_tr]; exact hw_lit
                        have hk_wc : WChainCursor ksK (lit ^^^ 1#32).toNat chW (done ++ [w0])
                            todo' (BitVec.ofNat 32 w0) (ksW.wnext[w0]?.getD 0#32) := by
                          have h1 : (ksW.putHdr .ticks (ksW.ticks + 1#32)).wnext = ksW.wnext := rfl
                          exact h1 ▸ hkp_wc
                        have hcid_mem_l : ∀ x ∈ kittenClauseLits ksK cid.toNat,
                            x ≠ other.toNat → ksK.vals[x]? = some 2#32 := by
                          intro x hx; dsimp only [cid] at hx; rw [hw_sh1_nat] at hx
                          exact hclause_fals x hx
                        c0_hsteps_nogrp
                        · have hlvl0K : ksK.lvl = 0#32 := ‹ksK.lvl = 0#32›
                          have hanteK : ksK.ante ≠ 0#32 := ‹ksK.ante ≠ 0#32›
                          obtain ⟨hante_rsn, hent_oth⟩ := hclause_ante hlvl0K hanteK
                          c0_call hLearn
                          obtain ⟨_, hmK_raw⟩ := kittenMemA_to_mem hmK
                          refine ⟨acap, ksK, R, hinvK.shapes, hinvK.clauses,
                            by rw [hother_bv_nat]; exact hother_nv, fun _ => hcid_ltK,
                            fun _ _ l hl hne => by
                              dsimp only [cid] at hante_rsn
                              rw [hw_sh1_nat] at hl; rw [hother_bv_nat] at hne
                              exact hante_rsn l hl hne,
                            (fun _ h => by cases h), by rw [hother_bv_nat]; exact hent_oth,
                            hmK_raw, fun ucid ksU mU hshU hclU hfff hsucc hmU => ?_⟩
                          c0_hsteps_nogrp
                          c0_hsplit
                          · have huc : ucid = 0xFFFFFFFF#32 := ‹ucid = 0xFFFFFFFF#32›
                            subst huc
                            obtain rfl := hfff rfl
                            c0_hsteps!
                            exact hret 0xFFFFFFFE#32 ksK mU hinvK hsyncK hfrK
                              (fun h => absurd h (by decide)) (fun _ h => absurd rfl h)
                              (kittenMem_to_amem hshU hmU)
                          · have huc_ne : ucid ≠ 0xFFFFFFFF#32 := ‹ucid ≠ 0xFFFFFFFF#32›
                            obtain ⟨rfl, hnc_u, hpres_u, hsz_u, hlits_u⟩ := hsucc huc_ne
                            obtain ⟨hinvU, hsyncU, hfrKU, hu_pr, hnc_ltU, _, hwcU⟩ :=
                              kittenUnit0_transfer hinvK hsyncK hshU hclU hnc_u hpres_u
                            rw [hother_bv_nat] at hlits_u
                            c0_hsteps!
                            exact hJ_rsn (ksK.nc, ksU) mU
                              ⟨hinvU, hsyncU, hfrK.trans hfrKU, by rw [hu_pr]; exact hk_pr,
                                by rw [hpres_u.trl_end]; exact hk_te,
                                by rw [hpres_u.trl]; exact hk_lit, hwcU hk_wc,
                                by rw [hpres_u.nv]; exact hother_nv,
                                by rw [hpres_u.vals]; exact hov0, hnc_ltU,
                                by rw [hlits_u]; exact List.mem_cons_self,
                                fun x hx hne => by
                                  rw [hlits_u, List.mem_singleton] at hx
                                  exact absurd hx hne,
                                fun _ _ => hlits_u, kittenMem_to_amem hshU hmU⟩
                        · have hante0 : ksK.ante = 0#32 := ‹ksK.ante = 0#32›
                          exact hJ_rsn (cid, ksK) _
                            ⟨hinvK, hsyncK, hfrK, hk_pr, hk_te, hk_lit, hk_wc, hother_nv,
                              hov0, hcid_ltK, hother_memK, hcid_mem_l,
                              fun _ ha => absurd hante0 ha, hmK⟩
                        · have hlvl_nz : ksK.lvl ≠ 0#32 := ‹ksK.lvl ≠ 0#32›
                          exact hJ_rsn (cid, ksK) _
                            ⟨hinvK, hsyncK, hfrK, hk_pr, hk_te, hk_lit, hk_wc, hother_nv,
                              hov0, hcid_ltK, hother_memK, hcid_mem_l,
                              fun hl => absurd hl hlvl_nz, hmK⟩
                    · c0_hsteps!
                      have hmK : (KittenMemA kPtr acap ksK ⋆ R) m := by
                        have h1 := hm; rw [hw_tn, hother_bv_nat] at h1; exact h1
                      have hwcK : WChainCursor ksK (lit ^^^ 1#32).toNat chW (done ++ [w0])
                          todo' (BitVec.ofNat 32 w0) (ksW.wnext[w0]?.getD 0#32) := by
                        have h1 : (ksW.putHdr .ticks (ksW.ticks + 1#32)).wnext = ksW.wnext := rfl
                        exact h1 ▸ hkp_wc
                      rw [hw_tn]
                      exact ihW (BitVec.ofNat 32 w0, ksW.wnext[w0]?.getD 0#32, done ++ [w0],
                          todo', ksK, chW) _ (by dsimp; omega)
                        ⟨hwcK, hinvK, hsyncK, hfrK,
                          by rw [hkp_pr, ht_pr]; exact hw_pr, by rw [hkp_te, ht_te]; exact hw_te,
                          by rw [hkp_tr, ht_tr]; exact hw_lit, hmK⟩
              · intro B L2 r m2 hB ih2 ⟨hm2, hr_le, hr2, hr_fals⟩
                dsimp only at hr_le hr2 hr_fals ⊢
                c0_hsplit
                · have hr_lt : r.toNat < sz.toNat := by
                    simpa [sz, Nat.mod_eq_of_lt (by omega : w0 < 2 ^ 32)] using hc
                  have hr_lt_cs : r.toNat < kittenClauseSize ksW (w0 / 2) := by
                    rwa [← hsz_eq_cs]
                  obtain ⟨hr_cap, hr_wrap, _, hr_lit⟩ := har_idx_ok r.toNat hr_lt_cs
                  have hr_bv_wrap : (ksW.clOff[(BitVec.ofNat 32 w0 >>>
                      (1 : Nat)).toNat]?.getD 0#32).toNat + r.toNat < 2 ^ 28 := by
                    rw [hw_sh1_nat]; exact hr_wrap
                  have hr_bv_cap : (ksW.clOff[(BitVec.ofNat 32 w0 >>>
                      (1 : Nat)).toNat]?.getD 0#32).toNat + r.toNat < acap := by
                    rw [hw_sh1_nat]; exact hr_cap
                  have hcand_256 : (ksW.arena[off.toNat + r.toNat]?.getD 0#32).toNat < 256 := by
                    have : (ksW.arena[off.toNat + r.toNat]?.getD 0#32).toNat < 2 * ksW.nv.toNat :=
                      hr_lit
                    unfold kMaxV at hnvW; omega
                  have hcand_28 : (ksW.arena[off.toNat + r.toNat]?.getD 0#32).toNat < 2 ^ 28 := by
                    omega
                  have ht_ar : ksT.arena = ksW.arena := rfl
                  have ht_va' : ksT.vals = ksW.vals := rfl
                  have hcand_bv_256 : (ksT.arena[(ksW.clOff[(BitVec.ofNat 32 w0 >>>
                      (1 : Nat)).toNat]?.getD 0#32).toNat + r.toNat]?.getD
                      0#32).toNat < 256 := by rw [ht_ar, hw_sh1_nat]; exact hcand_256
                  have hcand_bv_28 : (ksT.arena[(ksW.clOff[(BitVec.ofNat 32 w0 >>>
                      (1 : Nat)).toNat]?.getD 0#32).toNat + r.toNat]?.getD
                      0#32).toNat < 2 ^ 28 := by omega
                  have hr1_wrap : (r + 1#32).toNat = r.toNat + 1 := by
                    have : sz.toNat < 65536 := by
                      dsimp only [sz]; rw [BitVec.toNat_and]
                      exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
                    rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
                      Nat.mod_eq_of_lt (by omega)]
                  c0_hsteps_nogrp
                  · have hc_ne2 : ksW.vals[(ksW.arena[off.toNat + r.toNat]?.getD
                        0#32).toNat]? ≠ some 2#32 := by
                      intro heq
                      have h1 : ksW.vals[(ksW.arena[off.toNat + r.toNat]?.getD
                          0#32).toNat]?.getD 0#32 = 2#32 := by rw [heq, Option.getD_some]
                      apply hc
                      simpa [off, hw_sh1, ht_va', ht_ar,
                        Nat.mod_eq_of_lt (by omega : w0 < 2 ^ 32)] using h1
                    c0_hsteps!
                    have hB' := hB (r, r, ksW.arena[off.toNat + r.toNat]?.getD 0#32) m2
                      ⟨hm2, Or.inr ⟨hr2, hr_lt, rfl, hc_ne2⟩⟩
                    dsimp only [off] at hB'
                    rw [← ht_ar, ← hw_sh1_nat] at hB'
                    exact hB'
                  · have hc_eq2 : ksW.vals[(ksW.arena[off.toNat + r.toNat]?.getD
                        0#32).toNat]? = some 2#32 := by
                      have hc' : ksW.vals[(ksW.arena[off.toNat + r.toNat]?.getD
                          0#32).toNat]?.getD 0#32 = 2#32 := by
                        simpa [off, hw_sh1, ht_va', ht_ar,
                          Nat.mod_eq_of_lt (by omega : w0 < 2 ^ 32)] using hc
                      rw [List.getElem?_eq_getElem (by rw [hshW.vals_len]; exact hcand_256)]
                        at hc' ⊢
                      simpa using hc'
                    c0_hsteps!
                    refine ih2 (r + 1#32) m2 (by rw [hr1_wrap]; omega)
                      ⟨hm2, by rw [hr1_wrap]; omega, by rw [hr1_wrap]; omega, fun q hq2 hqr => ?_⟩
                    rw [hr1_wrap] at hqr
                    by_cases hqr_eq : q = r.toNat
                    · subst hqr_eq; exact hc_eq2
                    · exact hr_fals q hq2 (by omega)
                · have hr_not_lt : ¬ r.toNat < sz.toNat := by
                    simpa [sz, Nat.mod_eq_of_lt (by omega : w0 < 2 ^ 32)] using hc
                  have hr_eq : r.toNat = sz.toNat := by omega
                  c0_hsteps!
                  exact hB (r, 0xFFFFFFFF#32, 0#32) m2
                    ⟨hm2, Or.inl ⟨rfl, fun q hq2 hqsz => hr_fals q hq2 (by omega)⟩⟩
              · intro B L2 _hB hL2
                exact hL2 2#32 _ ⟨by simpa [ksT] using hm, hsz_ge, le_refl _, fun _ _ hq => by
                  rw [show (2#32 : BitVec 32).toNat = 2 from rfl] at hq; omega⟩
        · have hweq : w = 0xFFFFFFFF#32 := ‹w = 0xFFFFFFFF#32›
          c0_hsteps!
          exact ihO ksW mW (by
            have h1 := hinvO.assign.trl_end_le
            have h2 : ksO.nv.toNat = ks0.nv.toNat := congrArg BitVec.toNat hfrO.nv
            have h3 : ksW.prop.toNat = ksO.prop.toNat + 1 := hw_pr
            omega) ⟨hinvW, hsyncW, hfrW, hmW⟩
    · have hp_ge : ksO.trl_end.toNat ≤ ksO.prop.toNat := by omega
      have hpr_eq : ksO.prop = ksO.trl_end :=
        BitVec.eq_of_toNat_eq (by have := hinvO.assign.prop_le; omega)
      c0_hsteps!
      exact hret 0xFFFFFFFF#32 ksO mO hinvO hsyncO hfrO (fun _ => hpr_eq)
        (fun h => absurd rfl h) hmO

end LeanQbe.T.Examples.Kissat.Full

section
open LeanQbe.T LeanQbe.T.Examples.Kissat.Full

/-- Single-line `#print axioms` audit for `full_kitten_propagate_wp`. -/
theorem kitten_prop_ax : ∀ (Γ : Env),
    (∀ args m Q X, fullKittenAssignSpec args m Q X →
      Γ "full_kitten_assign" [i64, i32, i32] [] args m Q X) →
    (∀ args m Q X, fullKittenLearnUnit0Spec args m Q X →
      Γ "full_kitten_learn_unit0" [i64, i32, i32, .bool] [i32] args m Q X) →
    ∀ args m Q X, fullKittenPropagateSpec args m Q X →
      Func.wp Γ full_kitten_propagate_body args m Q X :=
  full_kitten_propagate_wp

#print axioms kitten_prop_ax
end
