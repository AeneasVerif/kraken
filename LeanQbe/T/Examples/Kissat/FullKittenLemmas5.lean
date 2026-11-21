module

public import LeanQbe.T.Examples.Kissat.FullKittenLemmas5a

/-!
# Kissat `D-Full` Scratch `kitten` Verification (`Part 5`: `core` & `shrink`)

Re-exports `[13] full_kitten_core_wp` from `FullKittenLemmas5a` and proves parametric `(Γ : Env)`
`Func.wp` contract for:
- `[14] full_kitten_shrink_wp` (`clAux` core-filter, `kmCore = 0#32`, `Sublist`, `KittenInv`)
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

/-! ## 1. Pure Helpers for `full_kitten_shrink` -/

private def shrinkCoreIds (ks : KittenState) (n : Nat) : List Nat :=
  (List.range n).filter fun ci => (kittenClauseMeta ks ci &&& kmCore) != 0#32

private theorem shrinkCoreIds_zero (ks : KittenState) : shrinkCoreIds ks 0 = [] := rfl

private theorem shrinkCoreIds_succ_skip (ks : KittenState) (n : Nat)
    (h : (kittenClauseMeta ks n &&& kmCore) = 0#32) :
    shrinkCoreIds ks (n + 1) = shrinkCoreIds ks n := by
  unfold shrinkCoreIds
  rw [List.range_succ, List.filter_append, List.filter_cons, List.filter_nil]
  simp [h]

private theorem shrinkCoreIds_succ_keep (ks : KittenState) (n : Nat)
    (h : (kittenClauseMeta ks n &&& kmCore) ≠ 0#32) :
    shrinkCoreIds ks (n + 1) = shrinkCoreIds ks n ++ [n] := by
  unfold shrinkCoreIds
  rw [List.range_succ, List.filter_append, List.filter_cons, List.filter_nil]
  have hb : ((kittenClauseMeta ks n &&& kmCore) != 0#32) = true := by simpa [bne_iff_ne] using h
  simp [hb]

private theorem shrinkCoreIds_length_le (ks : KittenState) (n : Nat) :
    (shrinkCoreIds ks n).length ≤ n := by
  unfold shrinkCoreIds
  calc ((List.range n).filter _).length ≤ (List.range n).length := List.length_filter_le _ _
    _ = n := List.length_range

private theorem shrinkCoreIds_mem_lt {ks : KittenState} {n x : Nat}
    (hx : x ∈ shrinkCoreIds ks n) : x < n :=
  List.mem_range.mp (List.mem_filter.mp hx).1

private theorem bv32_and_0xffff_lt (x : BitVec 32) : (x &&& 0xFFFF#32).toNat < 2 ^ 16 := by
  rw [BitVec.toNat_and, show (0xFFFF#32 : BitVec 32).toNat = 2 ^ 16 - 1 by decide]
  have hle := Nat.and_le_right (n := x.toNat) (m := 2 ^ 16 - 1)
  omega

private theorem bv32_and_0xffff_and_core (x : BitVec 32) :
    ((x &&& 0xFFFF#32) &&& kmCore) = 0#32 := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_and, BitVec.getElem_zero]
  by_cases hi16 : i = 16
  · subst hi16
    have h0 : (0xFFFF#32 : BitVec 32)[16]'(by decide) = false := by decide
    simp [h0]
  · have h0 : (kmCore : BitVec 32)[i] = false := by unfold kmCore; revert i hi16; decide
    simp [h0]

private theorem bv32_and_0xffff_and_lrn (x : BitVec 32) :
    ((x &&& 0xFFFF#32) &&& kmLrn) = 0#32 := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_and, BitVec.getElem_zero]
  by_cases hi17 : i = 17
  · subst hi17
    have h0 : (0xFFFF#32 : BitVec 32)[17]'(by decide) = false := by decide
    simp [h0]
  · have h0 : (kmLrn : BitVec 32)[i] = false := by unfold kmLrn; revert i hi17; decide
    simp [h0]

private theorem bv32_shl1_toNat (x : BitVec 32) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat % 2 ^ 32 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

/-- Phase-1 compaction invariant (`i` scanning `0..orig_nc`, `dst`/`ap` writing clauses). -/
private structure ShrinkP1Inv (acap : Nat) (ks : KittenState) (i dst ap : BitVec 32)
    (st : KittenState) : Prop where
  eq_with : st = { ks with clOff := st.clOff, clMeta := st.clMeta,
                           clAux := st.clAux, arena := st.arena }
  clOff_len : st.clOff.length = 896
  clMeta_len : st.clMeta.length = 896
  clAux_len : st.clAux.length = 896
  arena_len : st.arena.length = acap
  i_le : i.toNat ≤ ks.orig_nc.toNat
  dst_eq : dst.toNat = (shrinkCoreIds ks i.toNat).length
  ap_le : ap.toNat ≤ ks.alen.toNat
  ap_le_off : ∀ k, i.toNat ≤ k → k < ks.orig_nc.toNat → ap.toNat ≤ kittenClauseOff ks k
  unread_meta : ∀ k, i.toNat ≤ k → k < ks.orig_nc.toNat →
    st.clOff[k]? = ks.clOff[k]? ∧ st.clMeta[k]? = ks.clMeta[k]? ∧ st.clAux[k]? = ks.clAux[k]?
  unread_arena : ∀ idx, ap.toNat ≤ idx → idx < acap → st.arena[idx]? = ks.arena[idx]?
  compacted : ∀ d (hd : d < (shrinkCoreIds ks i.toNat).length),
    let orig := (shrinkCoreIds ks i.toNat)[d]'hd
    kittenClauseOff st d + kittenClauseSize st d ≤ ap.toNat ∧
    kittenClauseMeta st d = (kittenClauseMeta ks orig &&& 0xFFFF#32) ∧
    st.clAux[d]? = ks.clAux[orig]? ∧
    kittenClauseLits st d = kittenClauseLits ks orig
  comp_mono : ∀ d1 d2, d1 < d2 → d2 < dst.toNat →
    kittenClauseOff st d1 + kittenClauseSize st d1 ≤ kittenClauseOff st d2

private theorem ShrinkP1Inv.shapes {acap : Nat} {ks : KittenState} {i dst ap : BitVec 32}
    {st : KittenState} (hsh : ks.ShapesOk acap) (h : ShrinkP1Inv acap ks i dst ap st) :
    st.ShapesOk acap := by
  rw [h.eq_with]
  exact ⟨hsh.hdrTail_len, hsh.lvlArr_len, hsh.rsn_len, hsh.qprev_len, hsh.qnext_len,
    hsh.qstampArr_len, hsh.trl_len, hsh.flags_len, hsh.vals_len, hsh.assump_len, hsh.ana_len,
    hsh.kl_len, hsh.units_len, hsh.res_len, hsh.whead_len, hsh.wnext_len, hsh.wblit_len,
    h.clOff_len, h.clMeta_len, h.clAux_len, h.arena_len⟩

private theorem shrinkP1_init {acap : Nat} {ks : KittenState} (hsh : ks.ShapesOk acap) :
    ShrinkP1Inv acap ks 0#32 0#32 0#32 ks :=
  ⟨by cases ks; rfl, hsh.clOff_len, hsh.clMeta_len, hsh.clAux_len, hsh.arena_len,
   Nat.zero_le _, rfl, Nat.zero_le _, fun _ _ _ => Nat.zero_le _,
   fun _ _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ _ => rfl,
   fun _ hd => by simp [shrinkCoreIds_zero] at hd, fun _ _ _ h => by simp at h⟩

private theorem shrinkP1_skip {acap : Nat} {ks : KittenState} {i dst ap : BitVec 32}
    {st : KittenState} (hinv : ks.Inv acap) (hp : ShrinkP1Inv acap ks i dst ap st)
    (hi : i.toNat < ks.orig_nc.toNat)
    (hskip : (kittenClauseMeta ks i.toNat &&& kmCore) = 0#32) :
    ShrinkP1Inv acap ks (i + 1#32) dst ap st := by
  have hi1 : (i + 1#32).toNat = i.toNat + 1 := by
    have := hinv.clauses.orig_nc_max; unfold kMaxOrig at this; bv_omega
  have hids : shrinkCoreIds ks (i + 1#32).toNat = shrinkCoreIds ks i.toNat := by
    rw [hi1]; exact shrinkCoreIds_succ_skip ks i.toNat hskip
  refine ⟨hp.eq_with, hp.clOff_len, hp.clMeta_len, hp.clAux_len, hp.arena_len,
    by rw [hi1]; omega, by rw [hids]; exact hp.dst_eq, hp.ap_le,
    fun k hk1 hk2 => hp.ap_le_off k (by rw [hi1] at hk1; omega) hk2,
    fun k hk1 hk2 => hp.unread_meta k (by rw [hi1] at hk1; omega) hk2,
    hp.unread_arena, ?_, hp.comp_mono⟩
  intro d hd
  have hd' : d < (shrinkCoreIds ks i.toNat).length := hids ▸ hd
  have hget : (shrinkCoreIds ks (i + 1#32).toNat)[d]'hd = (shrinkCoreIds ks i.toNat)[d]'hd' := by
    simp only [hids]
  dsimp only
  rw [hget]
  exact hp.compacted d hd'

private theorem shrinkP1_keep {acap : Nat} {ks : KittenState} {i dst ap : BitVec 32}
    {st stA : KittenState} (hinv : ks.Inv acap) (hp : ShrinkP1Inv acap ks i dst ap st)
    (hi : i.toNat < ks.orig_nc.toNat)
    (hkeep : (kittenClauseMeta ks i.toNat &&& kmCore) ≠ 0#32)
    (hA_eq : stA = { st with arena := stA.arena })
    (hA_len : stA.arena.length = acap)
    (hA_lo : ∀ idx < ap.toNat, stA.arena[idx]? = st.arena[idx]?)
    (hA_mid : ∀ t < kittenClauseSize ks i.toNat,
      stA.arena[ap.toNat + t]? = ks.arena[kittenClauseOff ks i.toNat + t]?)
    (hA_hi : ∀ idx, ap.toNat + kittenClauseSize ks i.toNat ≤ idx → idx < acap →
      stA.arena[idx]? = ks.arena[idx]?) :
    let sz : BitVec 32 := kittenClauseMeta ks i.toNat &&& 0xFFFF#32
    let st' := ((stA.putArr .clOff dst.toNat ap).putArr .clMeta dst.toNat sz).putArr
      .clAux dst.toNat (ks.clAux[i.toNat]?.getD 0#32)
    ShrinkP1Inv acap ks (i + 1#32) (dst + 1#32) (ap + sz) st' := by
  intro sz st'
  have honc_max := hinv.clauses.orig_nc_max
  have honc_le := hinv.clauses.orig_nc_le
  have hal_le := hinv.clauses.alen_le
  have hacap_lt := hinv.clauses.acap_lt
  have hi_nc : i.toNat < ks.nc.toNat := Nat.lt_of_lt_of_le hi honc_le
  have hwf_i := hinv.clauses.cl_wf i.toNat hi_nc
  have hsz_eq : sz.toNat = kittenClauseSize ks i.toNat := rfl
  have hsz_lt : sz.toNat < 2 ^ 16 := bv32_and_0xffff_lt _
  have hap_le_i : ap.toNat ≤ kittenClauseOff ks i.toNat := hp.ap_le_off i.toNat (Nat.le_refl _) hi
  have hspan_i : kittenClauseOff ks i.toNat + sz.toNat ≤ ks.alen.toNat := by
    have h1 := hwf_i.2.2.1; unfold kittenClauseSpan at h1; omega
  have hap_add : (ap + sz).toNat = ap.toNat + sz.toNat := by
    unfold dimacsBound at hacap_lt; bv_omega
  have hdst_le_i : dst.toNat ≤ i.toNat := by
    rw [hp.dst_eq]; exact shrinkCoreIds_length_le ks i.toNat
  have hdst_896 : dst.toNat < 896 := by unfold kMaxOrig at honc_max; omega
  have hi1 : (i + 1#32).toNat = i.toNat + 1 := by unfold kMaxOrig at honc_max; bv_omega
  have hdst1 : (dst + 1#32).toNat = dst.toNat + 1 := by unfold kMaxOrig at honc_max; bv_omega
  have hids : shrinkCoreIds ks (i + 1#32).toNat = shrinkCoreIds ks i.toNat ++ [i.toNat] := by
    rw [hi1]; exact shrinkCoreIds_succ_keep ks i.toNat hkeep
  have hco_eq : st'.clOff = st.clOff.set dst.toNat ap := by
    dsimp only [st']; kp_field; rw [hA_eq]
  have hcm_eq : st'.clMeta = st.clMeta.set dst.toNat sz := by
    dsimp only [st']; kp_field; rw [hA_eq]
  have hca_eq : st'.clAux = st.clAux.set dst.toNat (ks.clAux[i.toNat]?.getD 0#32) := by
    dsimp only [st']; kp_field; rw [hA_eq]
  have har_eq : st'.arena = stA.arena := by dsimp only [st']; kp_field
  have hco_len : dst.toNat < st.clOff.length := by rw [hp.clOff_len]; exact hdst_896
  have hcm_len : dst.toNat < st.clMeta.length := by rw [hp.clMeta_len]; exact hdst_896
  have hca_len : dst.toNat < st.clAux.length := by rw [hp.clAux_len]; exact hdst_896
  have hst'_with : st' = { ks with clOff := st'.clOff, clMeta := st'.clMeta,
                                   clAux := st'.clAux, arena := st'.arena } := by
    have h1 : st' = { stA with clOff := st'.clOff, clMeta := st'.clMeta, clAux := st'.clAux } := by
      dsimp only [st', KittenState.putArr]
    rw [h1, hA_eq, hp.eq_with]
  refine ⟨hst'_with, by rw [hco_eq, List.length_set, hp.clOff_len],
    by rw [hcm_eq, List.length_set, hp.clMeta_len],
    by rw [hca_eq, List.length_set, hp.clAux_len],
    by rw [har_eq, hA_len], by rw [hi1]; omega,
    by rw [hdst1, hids, List.length_append, List.length_singleton, hp.dst_eq],
    by rw [hap_add]; omega, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk1 hk2
    rw [hi1] at hk1; rw [hap_add]
    have hmono := hinv.clauses.cl_mono i.toNat k (by omega) (Nat.lt_of_lt_of_le hk2 honc_le)
    unfold kittenClauseSpan at hmono
    omega
  · intro k hk1 hk2
    rw [hi1] at hk1
    have hne : dst.toNat ≠ k := by omega
    have hu := hp.unread_meta k (by omega) hk2
    rw [hco_eq, hcm_eq, hca_eq, List.getElem?_set_ne hne, List.getElem?_set_ne hne,
      List.getElem?_set_ne hne]
    exact hu
  · intro idx hidx1 hidx2
    rw [hap_add] at hidx1
    rw [har_eq]; exact hA_hi idx hidx1 hidx2
  · intro d hd
    have hd_len : d < (shrinkCoreIds ks i.toNat).length + 1 := by
      rw [hids, List.length_append, List.length_singleton] at hd; exact hd
    by_cases hdd : d < (shrinkCoreIds ks i.toNat).length
    · have hget : (shrinkCoreIds ks (i + 1#32).toNat)[d]'hd =
          (shrinkCoreIds ks i.toNat)[d]'hdd := by
        simp only [hids, List.getElem_append_left hdd]
      dsimp only
      rw [hget]
      have hne : dst.toNat ≠ d := by rw [hp.dst_eq]; omega
      have hold := hp.compacted d hdd
      have hoff_d : kittenClauseOff st' d = kittenClauseOff st d := by
        simp only [kittenClauseOff, hco_eq, List.getElem?_set_ne hne]
      have hcm_d : kittenClauseMeta st' d = kittenClauseMeta st d := by
        simp only [kittenClauseMeta, hcm_eq, List.getElem?_set_ne hne]
      have hsz_d : kittenClauseSize st' d = kittenClauseSize st d := by
        simp only [kittenClauseSize, hcm_d]
      refine ⟨by rw [hoff_d, hsz_d, hap_add]; omega, by rw [hcm_d]; exact hold.2.1,
        by rw [hca_eq, List.getElem?_set_ne hne]; exact hold.2.2.1, ?_⟩
      rw [← hold.2.2.2]
      unfold kittenClauseLits
      rw [hoff_d, hsz_d, har_eq]
      congr 1
      apply List.ext_getElem
      · simp only [List.length_take, List.length_drop, hA_len, hp.arena_len]
      · intro t ht1 ht2
        have ht_sz : t < kittenClauseSize st d := by simp at ht1; omega
        simp only [List.getElem_take, List.getElem_drop]
        have hidx : kittenClauseOff st d + t < ap.toNat := by omega
        have heq := hA_lo (kittenClauseOff st d + t) hidx
        rw [List.getElem?_eq_getElem (by rw [hA_len]; omega),
          List.getElem?_eq_getElem (by rw [hp.arena_len]; omega)] at heq
        exact Option.some.inj heq
    · have hdeq : d = dst.toNat := by rw [hp.dst_eq]; omega
      have hget : (shrinkCoreIds ks (i + 1#32).toNat)[d]'hd = i.toNat := by
        simp only [hids, show d = (shrinkCoreIds ks i.toNat).length by omega,
          List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_singleton]
      dsimp only
      rw [hget, hdeq]
      have hoff_n : kittenClauseOff st' dst.toNat = ap.toNat := by
        simp only [kittenClauseOff, hco_eq, List.getElem?_set_self hco_len, Option.getD_some]
      have hcm_n : kittenClauseMeta st' dst.toNat = sz := by
        simp only [kittenClauseMeta, hcm_eq, List.getElem?_set_self hcm_len, Option.getD_some]
      have hsz_n : kittenClauseSize st' dst.toNat = sz.toNat := by
        simp only [kittenClauseSize, hcm_n, bv32_and_0xffff_of_lt hsz_lt]
      have hca_n : st'.clAux[dst.toNat]? = ks.clAux[i.toNat]? := by
        have hi_ca : i.toNat < ks.clAux.length := by
          rw [hinv.shapes.clAux_len]; unfold kMaxOrig at honc_max; omega
        rw [hca_eq, List.getElem?_set_self hca_len, List.getElem?_eq_getElem hi_ca,
          Option.getD_some]
      refine ⟨by rw [hoff_n, hsz_n, hap_add]; exact Nat.le_refl _, hcm_n, hca_n, ?_⟩
      unfold kittenClauseLits
      rw [hoff_n, hsz_n, hsz_eq, har_eq]
      congr 1
      apply List.ext_getElem
      · simp only [List.length_take, List.length_drop, hA_len, hinv.shapes.arena_len]; omega
      · intro t ht1 ht2
        have ht_sz : t < kittenClauseSize ks i.toNat := by simp at ht1; omega
        simp only [List.getElem_take, List.getElem_drop]
        have heq := hA_mid t ht_sz
        rw [List.getElem?_eq_getElem (by rw [hA_len]; omega),
          List.getElem?_eq_getElem (by rw [hinv.shapes.arena_len]; omega)] at heq
        exact Option.some.inj heq
  · intro d1 d2 h12 hd2
    rw [hdst1] at hd2
    have hne1 : dst.toNat ≠ d1 := by omega
    have hoff1 : kittenClauseOff st' d1 = kittenClauseOff st d1 := by
      simp only [kittenClauseOff, hco_eq, List.getElem?_set_ne hne1]
    have hsz1 : kittenClauseSize st' d1 = kittenClauseSize st d1 := by
      simp only [kittenClauseSize, kittenClauseMeta, hcm_eq, List.getElem?_set_ne hne1]
    by_cases hd2_eq : d2 = dst.toNat
    · subst hd2_eq
      have hoff2 : kittenClauseOff st' dst.toNat = ap.toNat := by
        simp only [kittenClauseOff, hco_eq, List.getElem?_set_self hco_len, Option.getD_some]
      rw [hoff1, hsz1, hoff2]
      exact (hp.compacted d1 (by rw [← hp.dst_eq]; omega)).1
    · have hne2 : dst.toNat ≠ d2 := by omega
      have hoff2 : kittenClauseOff st' d2 = kittenClauseOff st d2 := by
        simp only [kittenClauseOff, hco_eq, List.getElem?_set_ne hne2]
      rw [hoff1, hsz1, hoff2]
      exact hp.comp_mono d1 d2 h12 (by omega)

/-- Phase-3 loop invariant (`i = 0..dst`): only `incons`, `nunits`, `units`, and watches change. -/
private structure ShrinkP3Inv (acap : Nat) (st3 : KittenState) (i : BitVec 32)
    (st : KittenState) : Prop where
  eq_with : st = { st3 with incons := st.incons, nunits := st.nunits, units := st.units,
                            whead := st.whead, wnext := st.wnext, wblit := st.wblit }
  sh : st.ShapesOk acap
  i_le : i.toNat ≤ st3.nc.toNat
  nunits_le : st.nunits.toNat ≤ kMaxL
  units_ok : ∀ ui < st.nunits.toNat,
    let ucid := (st.units[ui]?.getD 0#32).toNat
    ucid < st3.nc.toNat ∧ kittenClauseSize st3 ucid = 1
  incons_ok : st.incons ≠ 0xFFFFFFFF#32 →
    st.incons.toNat < st3.nc.toNat ∧ kittenClauseLits st3 st.incons.toNat = []
  watches_lt : ∃ chains : List (List Nat),
    chains.length = 2 * st3.nv.toNat ∧
    chains.flatten.Nodup ∧
    (∀ l < 2 * st3.nv.toNat,
      WChain st.wnext (st.whead[l]?.getD 0xFFFFFFFF#32) (chains[l]?.getD [])) ∧
    (∀ l < 2 * st3.nv.toNat, ∀ w ∈ chains[l]?.getD [],
      w < 2 * i.toNat ∧ 2 ≤ kittenClauseSize st3 (w / 2) ∧
      (st3.arena[kittenClauseOff st3 (w / 2) + (w % 2)]?.getD 0#32).toNat = l ∧
      (st.wblit[w]?.getD 0#32).toNat < 2 * st3.nv.toNat)
  wblit_ok : ∀ w < 2 * i.toNat, 2 ≤ kittenClauseSize st3 (w / 2) →
    (st.wblit[w]?.getD 0#32).toNat ∈ kittenClauseLits st3 (w / 2)

private theorem shrinkP2_build_st3 {acap : Nat} {ks st1 st3 : KittenState} {dst ap : BitVec 32}
    (hinv : ks.Inv acap) (hp1 : ShrinkP1Inv acap ks ks.orig_nc dst ap st1)
    (hst3_eq : st3 =
      { st1 with
        nc := dst, orig_nc := dst, alen := ap, lvl := 0#32, prop := 0#32,
        trl_end := 0#32, unass := ks.nv, incons := 0xFFFFFFFF#32, failing := 0xFFFFFFFF#32,
        nunits := 0#32, phase := ks.phase ^^^ 1#32, qsearch := ks.qlast,
        vals := st3.vals, whead := st3.whead, lvlArr := st3.lvlArr, rsn := st3.rsn })
    (hsh3 : st3.ShapesOk acap)
    (hlits3 : ∀ l < 2 * ks.nv.toNat, st3.vals[l]? = some 0#32 ∧ st3.whead[l]? = some 0xFFFFFFFF#32)
    (hvars3 : ∀ v < ks.nv.toNat, st3.lvlArr[v]? = some 0#32 ∧ st3.rsn[v]? = some 0xFFFFFFFF#32) :
    st3.Inv acap ∧ KittenTrailSynced st3 ∧ ShrinkP3Inv acap st3 0#32 st3 ∧
    st3.nv = ks.nv ∧ st3.lvl = 0#32 ∧ st3.trl_end = 0#32 ∧ st3.nc = st3.orig_nc ∧
    st3.ante = ks.ante ∧ st3.nassump = ks.nassump ∧
    kittenAssumpLits st3 = kittenAssumpLits ks ∧
    kittenOrigClauses st3 = kittenCoreClauses ks ∧
    (kittenOrigClauses st3).Sublist (kittenOrigClauses ks) ∧
    (∀ cl ∈ kittenOrigClauses st3, cl ∈ kittenOrigClauses ks) ∧
    ((List.range st3.orig_nc.toNat).map (kittenClauseAux st3) =
      ((List.range ks.orig_nc.toNat).filter fun ci =>
        (kittenClauseMeta ks ci &&& kmCore) != 0#32).map (kittenClauseAux ks)) ∧
    (∀ ci < st3.orig_nc.toNat, (kittenClauseMeta st3 ci &&& kmCore) = 0#32) := by
  have e_nv : st3.nv = ks.nv := by rw [hst3_eq, hp1.eq_with]
  have e_nc : st3.nc = dst := by rw [hst3_eq]
  have e_on : st3.orig_nc = dst := by rw [hst3_eq]
  have e_al : st3.alen = ap := by rw [hst3_eq]
  have e_ac : st3.acap = ks.acap := by rw [hst3_eq, hp1.eq_with]
  have e_lv : st3.lvl = 0#32 := by rw [hst3_eq]
  have e_pr : st3.prop = 0#32 := by rw [hst3_eq]
  have e_te : st3.trl_end = 0#32 := by rw [hst3_eq]
  have e_un : st3.unass = ks.nv := by rw [hst3_eq]
  have e_in : st3.incons = 0xFFFFFFFF#32 := by rw [hst3_eq]
  have e_fa : st3.failing = 0xFFFFFFFF#32 := by rw [hst3_eq]
  have e_an : st3.ante = ks.ante := by rw [hst3_eq, hp1.eq_with]
  have e_na : st3.nassump = ks.nassump := by rw [hst3_eq, hp1.eq_with]
  have e_nu : st3.nunits = 0#32 := by rw [hst3_eq]
  have e_nr : st3.nres = ks.nres := by rw [hst3_eq, hp1.eq_with]
  have e_nk : st3.nkl = ks.nkl := by rw [hst3_eq, hp1.eq_with]
  have e_nn : st3.nana = ks.nana := by rw [hst3_eq, hp1.eq_with]
  have e_fl : st3.flags = ks.flags := by rw [hst3_eq, hp1.eq_with]
  have e_as : st3.assump = ks.assump := by rw [hst3_eq, hp1.eq_with]
  have e_co : st3.clOff = st1.clOff := by rw [hst3_eq]
  have e_cm : st3.clMeta = st1.clMeta := by rw [hst3_eq]
  have e_ca : st3.clAux = st1.clAux := by rw [hst3_eq]
  have e_ar : st3.arena = st1.arena := by rw [hst3_eq]
  have hdst_le_onc : dst.toNat ≤ ks.orig_nc.toNat := by
    rw [hp1.dst_eq]; exact shrinkCoreIds_length_le ks ks.orig_nc.toNat
  have hcl_eq1 : ∀ c, kittenClauseOff st3 c = kittenClauseOff st1 c ∧
      kittenClauseMeta st3 c = kittenClauseMeta st1 c ∧
      kittenClauseSize st3 c = kittenClauseSize st1 c ∧
      kittenClauseLits st3 c = kittenClauseLits st1 c := fun c =>
    ⟨by simp [kittenClauseOff, e_co], by simp [kittenClauseMeta, e_cm],
     by simp [kittenClauseSize, kittenClauseMeta, e_cm],
     by simp [kittenClauseLits, kittenClauseOff, kittenClauseSize, kittenClauseMeta,
       e_co, e_cm, e_ar]⟩
  have hcore_eq : kittenOrigClauses st3 = kittenCoreClauses ks := by
    unfold kittenOrigClauses kittenCoreClauses
    rw [e_on, hp1.dst_eq]
    apply List.ext_getElem
    · simp [shrinkCoreIds]
    · intro d hd1 hd2
      have hd : d < (shrinkCoreIds ks ks.orig_nc.toNat).length := by simp at hd1; exact hd1
      simp only [List.getElem_map, List.getElem_range]
      rw [(hcl_eq1 d).2.2.2]
      exact (hp1.compacted d hd).2.2.2
  have haux_eq : (List.range st3.orig_nc.toNat).map (kittenClauseAux st3) =
      ((List.range ks.orig_nc.toNat).filter fun ci =>
        (kittenClauseMeta ks ci &&& kmCore) != 0#32).map (kittenClauseAux ks) := by
    rw [e_on, hp1.dst_eq]
    apply List.ext_getElem
    · simp [shrinkCoreIds]
    · intro d hd1 hd2
      have hd : d < (shrinkCoreIds ks ks.orig_nc.toNat).length := by simp at hd1; exact hd1
      simp only [List.getElem_map, List.getElem_range]
      unfold kittenClauseAux
      rw [e_ca, (hp1.compacted d hd).2.2.1]; rfl
  have hsub : (kittenOrigClauses st3).Sublist (kittenOrigClauses ks) := by
    rw [hcore_eq]
    unfold kittenCoreClauses kittenOrigClauses
    exact List.Sublist.map _ List.filter_sublist
  have hmem : ∀ cl ∈ kittenOrigClauses st3, cl ∈ kittenOrigClauses ks :=
    fun cl hcl => hsub.subset hcl
  have hnocore : ∀ ci < st3.orig_nc.toNat, (kittenClauseMeta st3 ci &&& kmCore) = 0#32 := by
    intro ci hci
    rw [e_on, hp1.dst_eq] at hci
    rw [(hcl_eq1 ci).2.1, (hp1.compacted ci hci).2.1]
    exact bv32_and_0xffff_and_core _
  have hcl3 : KittenClausesOk acap st3 := by
    refine ⟨hinv.clauses.acap_ge, hinv.clauses.acap_lt, by rw [e_ac]; exact hinv.clauses.acap_eq,
      by rw [e_nv]; exact hinv.clauses.nv_le,
      by rw [e_nc]; have := hinv.clauses.orig_nc_max; unfold kMaxOrig kMaxCl at *; omega,
      by rw [e_on, e_nc]; exact Nat.le_refl _,
      by rw [e_on]; have := hinv.clauses.orig_nc_max; omega,
      by rw [e_al]; have := hinv.clauses.alen_le; have := hp1.ap_le; omega,
      by rw [e_na]; exact hinv.clauses.nassump_le,
      by rw [e_nu]; decide,
      by rw [e_nr]; exact hinv.clauses.nres_le,
      by rw [e_nk]; exact hinv.clauses.nkl_le,
      by rw [e_nn]; exact hinv.clauses.nana_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro d hd
      rw [e_nc] at hd
      have hd' : d < (shrinkCoreIds ks ks.orig_nc.toNat).length := hp1.dst_eq ▸ hd
      have hcomp := hp1.compacted d hd'
      let orig := (shrinkCoreIds ks ks.orig_nc.toNat)[d]'hd'
      have horig_lt : orig < ks.orig_nc.toNat := shrinkCoreIds_mem_lt (List.getElem_mem hd')
      have hwf_o := hinv.clauses.cl_wf orig (Nat.lt_of_lt_of_le horig_lt hinv.clauses.orig_nc_le)
      have hlrn_f : kittenClauseIsLrn st3 d = false := by
        unfold kittenClauseIsLrn
        rw [(hcl_eq1 d).2.1, hcomp.2.1, bv32_and_0xffff_and_lrn]; rfl
      have hspan_d : kittenClauseSpan st3 d = kittenClauseSize st3 d := by
        unfold kittenClauseSpan; rw [hlrn_f]; simp
      refine ⟨by rw [hlrn_f, e_on, decide_eq_false (by omega)],
        fun hge => by rw [e_on] at hge; omega,
        by rw [hspan_d, (hcl_eq1 d).1, (hcl_eq1 d).2.2.1, e_al]; exact hcomp.1,
        fun l hl => by
          rw [(hcl_eq1 d).2.2.2, hcomp.2.2.2] at hl; rw [e_nv]; exact hwf_o.2.2.2.1 l hl,
        by apply cnfOfClauses_entailsClause_of_mem
           unfold kittenOrigClauses; rw [List.mem_map]
           exact ⟨d, List.mem_range.mpr (by rw [e_on]; exact hd), rfl⟩,
        fun _ hge => by rw [e_on] at hge; omega⟩
    · intro d1 d2 h12 hd2
      rw [e_nc] at hd2
      have hd1' : d1 < (shrinkCoreIds ks ks.orig_nc.toNat).length := by rw [← hp1.dst_eq]; omega
      have hlrn_f : kittenClauseIsLrn st3 d1 = false := by
        unfold kittenClauseIsLrn
        rw [(hcl_eq1 d1).2.1, (hp1.compacted d1 hd1').2.1, bv32_and_0xffff_and_lrn]; rfl
      have hspan1 : kittenClauseSpan st3 d1 = kittenClauseSize st3 d1 := by
        unfold kittenClauseSpan; rw [hlrn_f]; simp
      rw [hspan1, (hcl_eq1 d1).1, (hcl_eq1 d1).2.2.1, (hcl_eq1 d2).1]
      exact hp1.comp_mono d1 d2 h12 hd2
    · intro ui hui; rw [e_nu] at hui; simp at hui
    · intro hi; exact absurd e_in hi
    · intro _ hf; exact absurd e_fa hf
    · intro i hi; rw [e_as, e_nv]; exact hinv.clauses.assump_ok i (e_na ▸ hi)
    · intro v hv; rw [e_fl]; exact hinv.clauses.flags_clean v (e_nv ▸ hv)
  have hw_empty : ∃ chains : List (List Nat),
      chains.length = 2 * st3.nv.toNat ∧ chains.flatten.Nodup ∧
      (∀ l < 2 * st3.nv.toNat,
        WChain st3.wnext (st3.whead[l]?.getD 0xFFFFFFFF#32) (chains[l]?.getD [])) ∧
      (∀ l < 2 * st3.nv.toNat, ∀ w ∈ chains[l]?.getD [],
        w < 2 * (0#32 : BitVec 32).toNat ∧ 2 ≤ kittenClauseSize st3 (w / 2) ∧
        (st3.arena[kittenClauseOff st3 (w / 2) + (w % 2)]?.getD 0#32).toNat = l ∧
        (st3.wblit[w]?.getD 0#32).toNat < 2 * st3.nv.toNat) := by
    let ch : List (List Nat) := List.replicate (2 * st3.nv.toNat) []
    refine ⟨ch, by simp [ch], by simp [ch, List.flatten_replicate_nil], ?_, ?_⟩
    · intro l hl
      have hch_l : l < ch.length := by simp [ch, hl]
      rw [List.getElem?_eq_getElem hch_l, Option.getD_some, show ch[l]'hch_l = [] by simp [ch]]
      rw [(hlits3 l (e_nv ▸ hl)).2]; exact WChain.nil
    · intro l hl w hw
      have hch_l : l < ch.length := by simp [ch, hl]
      rw [List.getElem?_eq_getElem hch_l, Option.getD_some, show ch[l]'hch_l = [] by simp [ch]]
        at hw
      nomatch hw
  have hw3 : KittenWatchesOk st3 := by
    obtain ⟨ch, h1, h2, h3, h4⟩ := hw_empty
    exact ⟨ch, h1, h2, h3, fun l hl w hw => by
      have hb := h4 l hl w hw
      have h0 : w < 0 := by simpa using hb.1
      omega⟩
  have hba3 : KittenBaseAssignOk st3 := by
    refine ⟨by rw [e_te]; simp, by rw [e_pr, e_te]; exact Nat.le_refl _,
      by rw [e_un, e_te, e_nv]; simp,
      fun l hl => by rw [(hlits3 l (e_nv ▸ hl)).1]; exact Or.inl rfl,
      fun l hl => by
        have hnl : (l ^^^ 1) < 2 * ks.nv.toNat := by
          rw [e_nv] at hl; rcases nat_xor1_cases l with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega
        rw [(hlits3 l (e_nv ▸ hl)).1, (hlits3 (l ^^^ 1) hnl).1]; simp,
      fun l hl => by rw [(hlits3 l (e_nv ▸ hl)).1, e_te]; simp,
      by unfold kittenTrailLits; rw [e_te]; simp,
      fun l hl => by unfold kittenTrailLits at hl; rw [e_te] at hl; simp at hl,
      fun v hv => by rw [(hvars3 v (e_nv ▸ hv)).1]; simp,
      fun v hv _ => ⟨by rw [(hvars3 v (e_nv ▸ hv)).1]; rfl,
        by rw [(hvars3 v (e_nv ▸ hv)).2]; rfl⟩,
      fun _ _ _ hj => by rw [e_te] at hj; simp at hj,
      fun _ _ _ hi => by rw [e_te] at hi; simp at hi,
      fun _ hi => by rw [e_te] at hi; simp at hi⟩
  have hsync3 : KittenTrailSynced st3 := fun _ hi => by rw [e_te] at hi; simp at hi
  have hrsn3 : ReasonOk st3 := fun _ hi => by rw [e_te] at hi; simp at hi
  have hp3 : ShrinkP3Inv acap st3 0#32 st3 :=
    ⟨by cases st3; rfl, hsh3, Nat.zero_le _, by rw [e_nu]; decide,
     fun _ hu => by rw [e_nu] at hu; simp at hu,
     fun hi => absurd e_in hi, hw_empty, fun _ hw _ => by simp at hw⟩
  exact ⟨⟨hsh3, hcl3, hw3, hba3, hrsn3⟩, hsync3, hp3, e_nv, e_lv, e_te,
    by rw [e_nc, e_on], e_an, e_na, by unfold kittenAssumpLits; rw [e_na, e_as],
    hcore_eq, hsub, hmem, haux_eq, hnocore⟩

private theorem shrinkP3_step_noop {acap : Nat} {st3 st : KittenState} {i : BitVec 32}
    (hp : ShrinkP3Inv acap st3 i st) (hi : i.toNat < st3.nc.toNat) (hnc : st3.nc.toNat ≤ kMaxCl)
    (hsz_lt : kittenClauseSize st3 i.toNat < 2) :
    ShrinkP3Inv acap st3 (i + 1#32) st := by
  have hi1 : (i + 1#32).toNat = i.toNat + 1 := by unfold kMaxCl at hnc; bv_omega
  obtain ⟨ch, h1, h2, h3, h4⟩ := hp.watches_lt
  exact ⟨hp.eq_with, hp.sh, by rw [hi1]; omega, hp.nunits_le, hp.units_ok, hp.incons_ok,
    ⟨ch, h1, h2, h3, fun l hl w hw => by
      have hb := h4 l hl w hw; exact ⟨by rw [hi1]; omega, hb.2⟩⟩,
    fun w hw hsz => by
      rw [hi1] at hw
      by_cases hlt : w < 2 * i.toNat
      · exact hp.wblit_ok w hlt hsz
      · have hdiv : w / 2 = i.toNat := by omega
        rw [hdiv] at hsz; omega⟩

private theorem shrinkP3_step_incons {acap : Nat} {st3 st : KittenState} {i : BitVec 32}
    (hp : ShrinkP3Inv acap st3 i st) (hi : i.toNat < st3.nc.toNat) (hnc : st3.nc.toNat ≤ kMaxCl)
    (hsz0 : kittenClauseSize st3 i.toNat = 0) :
    ShrinkP3Inv acap st3 (i + 1#32) (st.putHdr .incons i) := by
  have hi1 : (i + 1#32).toNat = i.toNat + 1 := by unfold kMaxCl at hnc; bv_omega
  obtain ⟨ch, h1, h2, h3, h4⟩ := hp.watches_lt
  refine ⟨by rw [hp.eq_with]; rfl, hp.sh.putHdr .incons i, by rw [hi1]; omega,
    by kp_field; exact hp.nunits_le, by kp_field; exact hp.units_ok, ?_,
    ⟨ch, h1, h2, by kp_field; exact h3, fun l hl w hw => by
      have hb := h4 l hl w hw; kp_field; exact ⟨by rw [hi1]; omega, hb.2⟩⟩,
    fun w hw hsz => by
      rw [hi1] at hw; kp_field
      by_cases hlt : w < 2 * i.toNat
      · exact hp.wblit_ok w hlt hsz
      · have hdiv : w / 2 = i.toNat := by omega
        rw [hdiv, hsz0] at hsz; omega⟩
  intro _
  kp_field
  exact ⟨hi, by unfold kittenClauseLits; rw [hsz0]; simp⟩

private theorem shrinkP3_step_unit {acap : Nat} {st3 st : KittenState} {i : BitVec 32}
    (hp : ShrinkP3Inv acap st3 i st) (hi : i.toNat < st3.nc.toNat) (hnc : st3.nc.toNat ≤ kMaxCl)
    (hnu : st.nunits.toNat < 256) (hsz1 : kittenClauseSize st3 i.toNat = 1) :
    ShrinkP3Inv acap st3 (i + 1#32)
      ((st.putArr .units st.nunits.toNat i).putHdr .nunits (st.nunits + 1#32)) := by
  have hi1 : (i + 1#32).toNat = i.toNat + 1 := by unfold kMaxCl at hnc; bv_omega
  have hnu1 : (st.nunits + 1#32).toNat = st.nunits.toNat + 1 := by bv_omega
  have hun_len : st.nunits.toNat < st.units.length := by rw [hp.sh.units_len]; exact hnu
  obtain ⟨ch, h1, h2, h3, h4⟩ := hp.watches_lt
  refine ⟨by rw [hp.eq_with]; rfl, (hp.sh.putArr .units _ _).putHdr .nunits _,
    by rw [hi1]; omega, by kp_field; rw [hnu1]; unfold kMaxL; omega, ?_,
    by kp_field; exact hp.incons_ok,
    ⟨ch, h1, h2, by kp_field; exact h3, fun l hl w hw => by
      have hb := h4 l hl w hw; kp_field; exact ⟨by rw [hi1]; omega, hb.2⟩⟩,
    fun w hw hsz => by
      rw [hi1] at hw; kp_field
      by_cases hlt : w < 2 * i.toNat
      · exact hp.wblit_ok w hlt hsz
      · have hdiv : w / 2 = i.toNat := by omega
        rw [hdiv, hsz1] at hsz; omega⟩
  intro ui hui
  have hui' : ui < st.nunits.toNat + 1 := by
    revert hui; kp_field; intro hui; rwa [hnu1] at hui
  dsimp only; kp_field
  by_cases hu : ui = st.nunits.toNat
  · subst hu
    rw [List.getElem?_set_self hun_len, Option.getD_some]
    exact ⟨hi, hsz1⟩
  · rw [List.getElem?_set_ne (Ne.symm hu)]
    exact hp.units_ok ui (by omega)

private theorem shrinkP3_step_watch {acap : Nat} {st3 st : KittenState} {i l0 l1 : BitVec 32}
    (hinv3 : st3.Inv acap) (hp : ShrinkP3Inv acap st3 i st)
    (hi : i.toNat < st3.nc.toNat) (hsz2 : 2 ≤ kittenClauseSize st3 i.toNat)
    (hl0 : l0.toNat < 2 * st3.nv.toNat) (hl1 : l1.toNat < 2 * st3.nv.toNat)
    (har0 : (st3.arena[kittenClauseOff st3 i.toNat]?.getD 0#32).toNat = l0.toNat)
    (har1 : (st3.arena[kittenClauseOff st3 i.toNat + 1]?.getD 0#32).toNat = l1.toNat) :
    ShrinkP3Inv acap st3 (i + 1#32) (kittenWatchStep st i l0 l1) := by
  have hnc := hinv3.clauses.nc_le
  have hnv := hinv3.clauses.nv_le
  have hi1 : (i + 1#32).toNat = i.toNat + 1 := by unfold kMaxCl at hnc; bv_omega
  have e_nv : st.nv = st3.nv := by rw [hp.eq_with]
  have e_nc : st.nc = st3.nc := by rw [hp.eq_with]
  have e_ar : st.arena = st3.arena := by rw [hp.eq_with]
  have e_co : st.clOff = st3.clOff := by rw [hp.eq_with]
  have e_cm : st.clMeta = st3.clMeta := by rw [hp.eq_with]
  have hsz_st : ∀ c, kittenClauseSize st c = kittenClauseSize st3 c := fun c => by
    simp [kittenClauseSize, kittenClauseMeta, e_cm]
  have hoff_st : ∀ c, kittenClauseOff st c = kittenClauseOff st3 c := fun c => by
    simp [kittenClauseOff, e_co]
  obtain ⟨ch, hlen, hnd, hwc, hbnd⟩ := hp.watches_lt
  have hmc : kMaxCl ≤ 896 := Nat.le_refl _
  have hw0 := bv32_cid_w0 hi (by omega)
  have hw1 := bv32_cid_w1 hi (by omega)
  let w0 := i <<< 1
  let w1 := w0 ||| 1#32
  have hw0_nat : w0.toNat = 2 * i.toNat := hw0.1
  have hw1_nat : w1.toNat = 2 * i.toNat + 1 := hw1.1
  have hfresh : ∀ u ∈ ch.flatten, u < 2 * i.toNat := by
    intro u hu
    rw [List.mem_flatten] at hu
    obtain ⟨c, hc, huc⟩ := hu
    obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hc
    have hl_nv : l < 2 * st3.nv.toNat := by omega
    exact (hbnd l hl_nv u (by simpa [List.getElem?_eq_getElem hl] using huc)).1
  have hstep0 := kittenWatchStep0_preserves_watches_with hp.sh (e_nv ▸ hlen) hnd
    (fun x hx => hwc x (e_nv ▸ hx))
    (fun x hx u hu => by
      have hb := hbnd x (e_nv ▸ hx) u hu
      exact ⟨by rw [e_nc]; omega, by rw [hsz_st]; exact hb.2.1,
        by rw [e_ar, hoff_st]; exact hb.2.2.1, by rw [e_nv]; exact hb.2.2.2⟩)
    (w := w0) (l := l0) (vo := l1) (by rw [e_nc]; omega) (e_nc ▸ hnc) (e_nv ▸ hnv)
    (e_nv ▸ hl0) (e_nv ▸ hl1)
    (by rw [hsz_st, hw0_nat, show 2 * i.toNat / 2 = i.toNat by omega]; exact hsz2)
    (by rw [e_ar, hoff_st, hw0_nat, show 2 * i.toNat / 2 = i.toNat by omega,
      show 2 * i.toNat % 2 = 0 by omega]; exact har0)
    (fun hm => absurd (hfresh _ hm) (by omega))
  have hsh0 := kittenWatchStep0_preserves_shapes hp.sh w0 l0 l1
  have hstep1 := kittenWatchStep0_preserves_watches_with hsh0 hstep0.1 hstep0.2.1 hstep0.2.2.1
    hstep0.2.2.2.1 (w := w1) (l := l1) (vo := l0)
    (by change w1.toNat < 2 * st.nc.toNat; rw [e_nc]; omega)
    (by change st.nc.toNat ≤ kMaxCl; rw [e_nc]; exact hnc)
    (by change st.nv.toNat ≤ kMaxV; rw [e_nv]; exact hnv)
    (by change l1.toNat < 2 * st.nv.toNat; rw [e_nv]; exact hl1)
    (by change l0.toNat < 2 * st.nv.toNat; rw [e_nv]; exact hl0)
    (by change 2 ≤ kittenClauseSize st (w1.toNat / 2)
        rw [hsz_st, hw1_nat, show (2 * i.toNat + 1) / 2 = i.toNat by omega]; exact hsz2)
    (by change (st.arena[kittenClauseOff st (w1.toNat / 2) + (w1.toNat % 2)]?.getD 0#32).toNat =
          l1.toNat
        rw [e_ar, hoff_st, hw1_nat, show (2 * i.toNat + 1) / 2 = i.toNat by omega,
          show (2 * i.toNat + 1) % 2 = 1 by omega]; exact har1)
    (fun hm => by
      rcases (hstep0.2.2.2.2 w1.toNat).mp hm with heq | hmem
      · omega
      · exact absurd (hfresh _ hmem) (by omega))
  refine ⟨by rw [hp.eq_with]; rfl, kittenWatchStep_preserves_shapes hp.sh i l0 l1,
    by rw [hi1]; omega, hp.nunits_le, hp.units_ok, hp.incons_ok, ?_, ?_⟩
  · have hlen1 : ((ch.set l0.toNat (w0.toNat :: ch[l0.toNat]'(by omega))).set l1.toNat
        (w1.toNat :: (ch.set l0.toNat (w0.toNat :: ch[l0.toNat]'(by omega)))[l1.toNat]'(by
          simp; omega))).length = 2 * st3.nv.toNat := by
      simp [List.length_set, hlen]
    refine ⟨_, hlen1, hstep1.2.1,
      fun l hl => hstep1.2.2.1 l (e_nv ▸ hl), fun l hl u hu => ?_⟩
    have hb := hstep1.2.2.2.1 l (e_nv ▸ hl) u hu
    have hu_mem : u ∈ ((ch.set l0.toNat (w0.toNat :: ch[l0.toNat]'(by omega))).set l1.toNat
        (w1.toNat :: (ch.set l0.toNat (w0.toNat :: ch[l0.toNat]'(by omega)))[l1.toNat]'(by
          simp; omega))).flatten := by
      rw [List.mem_flatten]
      have hl_len : l < ((ch.set l0.toNat (w0.toNat :: ch[l0.toNat]'(by omega))).set l1.toNat
          (w1.toNat :: (ch.set l0.toNat (w0.toNat :: ch[l0.toNat]'(by omega)))[l1.toNat]'(by
            simp; omega))).length := by simp [hlen, hl]
      exact ⟨_, List.getElem_mem hl_len, by simpa [List.getElem?_eq_getElem hl_len] using hu⟩
    have hu_lt : u < 2 * (i + 1#32).toNat := by
      rw [hi1]
      rcases (hstep1.2.2.2.2 u).mp hu_mem with rfl | hm0
      · omega
      · rcases (hstep0.2.2.2.2 u).mp hm0 with rfl | hm_old
        · omega
        · have := hfresh u hm_old; omega
    refine ⟨hu_lt, ?_, ?_, ?_⟩
    · have h1 := hb.2.1; change 2 ≤ kittenClauseSize st (u / 2) at h1; rwa [hsz_st] at h1
    · have h2 := hb.2.2.1
      change (st.arena[kittenClauseOff st (u / 2) + (u % 2)]?.getD 0#32).toNat = l at h2
      rwa [e_ar, hoff_st] at h2
    · have h3 := hb.2.2.2; rwa [← e_nv]
  · intro w hw hsz_w
    rw [hi1] at hw
    have hwb_len : st.wblit.length = 1792 := hp.sh.wblit_len
    have hspan_i :
        kittenClauseOff st3 i.toNat + kittenClauseSize st3 i.toNat ≤ st3.arena.length := by
      have hwf := hinv3.clauses.cl_wf i.toNat hi
      have h1 := hwf.2.2.1; unfold kittenClauseSpan at h1
      have h2 := hinv3.clauses.alen_le
      rw [hinv3.shapes.arena_len]; omega
    have hmem_ar : ∀ k < 2, (st3.arena[kittenClauseOff st3 i.toNat + k]?.getD 0#32).toNat ∈
        kittenClauseLits st3 i.toNat := by
      intro k hk
      unfold kittenClauseLits
      rw [List.mem_map]
      have hlt_a : kittenClauseOff st3 i.toNat + k < st3.arena.length := by omega
      refine ⟨st3.arena[kittenClauseOff st3 i.toNat + k]'hlt_a, ?_, by
        rw [List.getElem?_eq_getElem hlt_a, Option.getD_some]⟩
      have hlen_t : ((st3.arena.drop (kittenClauseOff st3 i.toNat)).take
          (kittenClauseSize st3 i.toNat)).length = kittenClauseSize st3 i.toNat := by
        simp [List.length_take, List.length_drop]; omega
      have hget : ((st3.arena.drop (kittenClauseOff st3 i.toNat)).take
          (kittenClauseSize st3 i.toNat))[k]'(by omega) =
          st3.arena[kittenClauseOff st3 i.toNat + k]'hlt_a := by
        simp [List.getElem_take, List.getElem_drop]
      rw [← hget]
      exact List.getElem_mem (by omega)
    change (((st.wblit.set w0.toNat l1).set w1.toNat l0)[w]?.getD 0#32).toNat ∈
      kittenClauseLits st3 (w / 2)
    rw [hw0_nat, hw1_nat]
    by_cases hlt : w < 2 * i.toNat
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact hp.wblit_ok w hlt hsz_w
    · rcases (by omega : w = 2 * i.toNat ∨ w = 2 * i.toNat + 1) with rfl | rfl
      · rw [List.getElem?_set_ne (by omega),
          List.getElem?_set_self (by rw [hwb_len]; unfold kMaxCl at hnc; omega),
          Option.getD_some, show 2 * i.toNat / 2 = i.toNat by omega, ← har1]
        exact hmem_ar 1 (by omega)
      · rw [List.getElem?_set_self (by rw [List.length_set, hwb_len]; unfold kMaxCl at hnc; omega),
          Option.getD_some, show (2 * i.toNat + 1) / 2 = i.toNat by omega, ← har0]
        simpa [Nat.add_zero] using hmem_ar 0 (by omega)

private theorem shrinkP3_finish {acap : Nat} {st3 st : KittenState}
    (hinv3 : st3.Inv acap) (hsync3 : KittenTrailSynced st3)
    (hp : ShrinkP3Inv acap st3 st3.nc st) :
    st.Inv acap ∧ KittenTrailSynced st := by
  have e_nv : st.nv = st3.nv := by rw [hp.eq_with]
  have e_nc : st.nc = st3.nc := by rw [hp.eq_with]
  have e_on : st.orig_nc = st3.orig_nc := by rw [hp.eq_with]
  have e_al : st.alen = st3.alen := by rw [hp.eq_with]
  have e_ac : st.acap = st3.acap := by rw [hp.eq_with]
  have e_lv : st.lvl = st3.lvl := by rw [hp.eq_with]
  have e_pr : st.prop = st3.prop := by rw [hp.eq_with]
  have e_te : st.trl_end = st3.trl_end := by rw [hp.eq_with]
  have e_un : st.unass = st3.unass := by rw [hp.eq_with]
  have e_fa : st.failing = st3.failing := by rw [hp.eq_with]
  have e_an : st.ante = st3.ante := by rw [hp.eq_with]
  have e_na : st.nassump = st3.nassump := by rw [hp.eq_with]
  have e_nr : st.nres = st3.nres := by rw [hp.eq_with]
  have e_nk : st.nkl = st3.nkl := by rw [hp.eq_with]
  have e_nn : st.nana = st3.nana := by rw [hp.eq_with]
  have e_va : st.vals = st3.vals := by rw [hp.eq_with]
  have e_la : st.lvlArr = st3.lvlArr := by rw [hp.eq_with]
  have e_rs : st.rsn = st3.rsn := by rw [hp.eq_with]
  have e_tr : st.trl = st3.trl := by rw [hp.eq_with]
  have e_fl : st.flags = st3.flags := by rw [hp.eq_with]
  have e_as : st.assump = st3.assump := by rw [hp.eq_with]
  have e_co : st.clOff = st3.clOff := by rw [hp.eq_with]
  have e_cm : st.clMeta = st3.clMeta := by rw [hp.eq_with]
  have e_ca : st.clAux = st3.clAux := by rw [hp.eq_with]
  have e_ar : st.arena = st3.arena := by rw [hp.eq_with]
  have hcl_eq : ∀ c, kittenClauseOff st c = kittenClauseOff st3 c ∧
      kittenClauseMeta st c = kittenClauseMeta st3 c ∧
      kittenClauseSize st c = kittenClauseSize st3 c ∧
      kittenClauseIsLrn st c = kittenClauseIsLrn st3 c ∧
      kittenClauseAux st c = kittenClauseAux st3 c ∧
      kittenClauseSpan st c = kittenClauseSpan st3 c ∧
      kittenClauseLits st c = kittenClauseLits st3 c ∧
      kittenClauseAnts st c = kittenClauseAnts st3 c := fun c =>
    ⟨by simp [kittenClauseOff, e_co], by simp [kittenClauseMeta, e_cm],
     by simp [kittenClauseSize, kittenClauseMeta, e_cm],
     by simp [kittenClauseIsLrn, kittenClauseMeta, e_cm],
     by simp [kittenClauseAux, e_ca],
     by simp [kittenClauseSpan, kittenClauseSize, kittenClauseIsLrn, kittenClauseAux,
       kittenClauseMeta, e_cm, e_ca],
     by simp [kittenClauseLits, kittenClauseOff, kittenClauseSize, kittenClauseMeta,
       e_co, e_cm, e_ar],
     by simp [kittenClauseAnts, kittenClauseIsLrn, kittenClauseOff, kittenClauseSize,
       kittenClauseAux, kittenClauseMeta, e_co, e_cm, e_ca, e_ar]⟩
  have horig : kittenOrigClauses st = kittenOrigClauses st3 :=
    kittenOrigClauses_eq_of e_on fun ci _ => (hcl_eq ci).2.2.2.2.2.2.1
  have hcl : KittenClausesOk acap st := by
    refine ⟨hinv3.clauses.acap_ge, hinv3.clauses.acap_lt, by rw [e_ac]; exact hinv3.clauses.acap_eq,
      by rw [e_nv]; exact hinv3.clauses.nv_le, by rw [e_nc]; exact hinv3.clauses.nc_le,
      by rw [e_on, e_nc]; exact hinv3.clauses.orig_nc_le,
      by rw [e_on]; exact hinv3.clauses.orig_nc_max, by rw [e_al]; exact hinv3.clauses.alen_le,
      by rw [e_na]; exact hinv3.clauses.nassump_le, hp.nunits_le,
      by rw [e_nr]; exact hinv3.clauses.nres_le, by rw [e_nk]; exact hinv3.clauses.nkl_le,
      by rw [e_nn]; exact hinv3.clauses.nana_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro c hc
      have hw := hinv3.clauses.cl_wf c (e_nc ▸ hc)
      have hf := hcl_eq c
      rw [hf.2.2.2.1, hf.2.2.1, hf.1, hf.2.2.2.2.2.1, hf.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2,
        List.map_congr_left (fun a _ => (hcl_eq a).2.2.2.2.2.2.1),
        e_on, e_al, e_nv, e_an, horig]
      exact hw
    · intro c1 c2 h12 hc2
      rw [(hcl_eq c1).1, (hcl_eq c1).2.2.2.2.2.1, (hcl_eq c2).1]
      exact hinv3.clauses.cl_mono c1 c2 h12 (e_nc ▸ hc2)
    · intro ui hui
      dsimp only
      rw [e_nc, (hcl_eq _).2.2.1]
      exact hp.units_ok ui hui
    · intro hi
      have ⟨hinc_lt, hlits_nil⟩ := hp.incons_ok hi
      have hinc_orig : st.incons.toNat < st3.orig_nc.toNat := by
        have hwf := hinv3.clauses.cl_wf st.incons.toNat hinc_lt
        by_cases hlt : st.incons.toNat < st3.orig_nc.toNat
        · exact hlt
        · exfalso
          have hge' : st3.orig_nc.toNat ≤ st.incons.toNat := Nat.le_of_not_lt hlt
          have hpos := hwf.2.1 hge'
          have hlen_lits : (kittenClauseLits st3 st.incons.toNat).length =
              kittenClauseSize st3 st.incons.toNat := by
            have h1 := hwf.2.2.1; unfold kittenClauseSpan at h1
            have h2 := hinv3.clauses.alen_le
            simp only [kittenClauseLits, List.length_map, List.length_take, List.length_drop,
              hinv3.shapes.arena_len]; omega
          rw [hlits_nil] at hlen_lits; simp at hlen_lits; omega
      refine ⟨e_nc.symm ▸ hinc_lt, ?_, fun l hl => by
        rw [(hcl_eq _).2.2.2.2.2.2.1, hlits_nil] at hl; nomatch hl⟩
      rw [horig, CNF.unsat_iff_not_sat]
      intro α hα
      have hmem : [] ∈ kittenOrigClauses st3 := by
        unfold kittenOrigClauses; rw [List.mem_map]
        exact ⟨st.incons.toNat, List.mem_range.mpr hinc_orig, hlits_nil⟩
      have hsat := (cnf_sat_cnfOfClauses_iff α _).mp hα [] hmem
      rw [clause_sat_cnfClause_iff] at hsat
      obtain ⟨_, hl, _⟩ := hsat; nomatch hl
    · intro ha hf
      have hfa := hinv3.clauses.failing_ok (e_an ▸ ha) (e_fa ▸ hf)
      have hcm_eq : (fun ci => (kittenClauseMeta st ci &&& kmCore) != 0#32) =
          (fun ci => (kittenClauseMeta st3 ci &&& kmCore) != 0#32) :=
        funext fun ci => by rw [(hcl_eq ci).2.1]
      have hmap_eq : List.map (kittenClauseLits st) = List.map (kittenClauseLits st3) :=
        congrArg List.map (funext fun ci => (hcl_eq ci).2.2.2.2.2.2.1)
      unfold kittenAssumpLits at hfa ⊢
      rwa [e_nc, hcm_eq, hmap_eq, e_na, e_as]
    · intro i hi; rw [e_as, e_nv]; exact hinv3.clauses.assump_ok i (e_na ▸ hi)
    · intro v hv; rw [e_fl]; exact hinv3.clauses.flags_clean v (e_nv ▸ hv)
  have hw : KittenWatchesOk st := by
    obtain ⟨ch, h1, h2, h3, h4⟩ := hp.watches_lt
    refine ⟨ch, e_nv ▸ h1, h2, fun l hl => h3 l (e_nv ▸ hl), fun l hl w hw => ?_⟩
    have hb := h4 l (e_nv ▸ hl) w hw
    rw [e_nc, e_nv, e_ar, (hcl_eq _).2.2.1, (hcl_eq _).1]; exact hb
  have hba : KittenBaseAssignOk st :=
    ⟨by rw [e_te, e_nv]; exact hinv3.assign.trl_end_le,
     by rw [e_pr, e_te]; exact hinv3.assign.prop_le,
     by rw [e_un, e_te, e_nv]; exact hinv3.assign.unass_eq,
     by rw [e_nv, e_va]; exact hinv3.assign.vals_dom,
     by rw [e_nv, e_va]; exact hinv3.assign.vals_neg_iff,
     by rw [e_nv, e_va, e_te, e_tr]; exact hinv3.assign.vals_nz_iff_trl,
     by unfold kittenTrailLits; rw [e_te, e_tr]; exact hinv3.assign.trl_nodup,
     by unfold kittenTrailLits; rw [e_nv, e_te, e_tr]; exact hinv3.assign.trl_lt,
     by rw [e_nv, e_la, e_lv]; exact hinv3.assign.trl_lvl_le,
     by rw [e_nv, e_va, e_la, e_rs]; exact hinv3.assign.unass_lvl_zero,
     by rw [e_te, e_la, e_tr]; exact hinv3.assign.trl_lvl_mono,
     by rw [e_te, e_la, e_tr, e_rs]; exact hinv3.assign.dec_earliest,
     by intro i hi l hlv
        rw [e_te] at hi; dsimp only [l] at hlv ⊢
        rw [e_tr, e_la] at hlv; rw [e_tr, e_rs, e_va, horig, e_nc]
        have h0 := hinv3.assign.lvl0_ok i hi hlv
        refine ⟨h0.1, h0.2.1, h0.2.2.1, h0.2.2.2.1, fun ha => ?_⟩
        have hr := h0.2.2.2.2 (e_an ▸ ha)
        dsimp only at hr ⊢; rw [(hcl_eq _).2.2.2.2.2.2.1]; exact hr⟩
  have hsync : KittenTrailSynced st := by
    unfold KittenTrailSynced; rw [e_te, e_tr, e_va]; exact hsync3
  have hrsn : ReasonOk st := by
    intro i hi; rw [e_te] at hi; dsimp only; rw [e_tr, e_rs, e_nc]
    have hr := hinv3.reasons i hi; dsimp only at hr
    simpa only [(hcl_eq _).2.2.2.2.2.2.1] using hr
  exact ⟨⟨hp.sh, hcl, hw, hba, hrsn⟩, hsync⟩

private def shrinkHdrState (st1 : KittenState) (dst ap : BitVec 32) : KittenState :=
  { st1 with
    nc := dst, orig_nc := dst, alen := ap, lvl := 0#32, prop := 0#32, trl_end := 0#32,
    unass := st1.nv, incons := 0xFFFFFFFF#32, failing := 0xFFFFFFFF#32, nunits := 0#32,
    phase := st1.phase ^^^ 1#32, qsearch := st1.qlast }

private theorem shrinkHdrState_shapes {acap : Nat} {st1 : KittenState} (dst ap : BitVec 32)
    (hsh : st1.ShapesOk acap) : (shrinkHdrState st1 dst ap).ShapesOk acap :=
  ⟨hsh.hdrTail_len, hsh.lvlArr_len, hsh.rsn_len, hsh.qprev_len, hsh.qnext_len,
   hsh.qstampArr_len, hsh.trl_len, hsh.flags_len, hsh.vals_len, hsh.assump_len, hsh.ana_len,
   hsh.kl_len, hsh.units_len, hsh.res_len, hsh.whead_len, hsh.wnext_len, hsh.wblit_len,
   hsh.clOff_len, hsh.clMeta_len, hsh.clAux_len, hsh.arena_len⟩

private theorem shrink_hdr_store_norm (st1 : KittenState) (dst ap : BitVec 32) :
    let s1 := (((((st1.putHdr .nc dst).putHdr .orig_nc dst).putHdr .alen ap).putHdr
      .lvl 0).putHdr .prop 0).putHdr .trl_end 0
    let s2 := (((s1.putHdr .unass s1.nv).putHdr .incons 4294967295).putHdr
      .failing 4294967295).putHdr .nunits 0
    let s3 := s2.putHdr .phase (s2.phase ^^^ 1)
    s3.putHdr .qsearch s3.qlast = shrinkHdrState st1 dst ap ∧
    (s3.putHdr .qsearch s3.qlast).nv = st1.nv := by
  intro s1 s2 s3
  have hnv1 : s1.nv = st1.nv := by dsimp only [s1]; kp_field
  have hph2 : s2.phase = st1.phase := by dsimp only [s2, s1]; kp_field
  have hql3 : s3.qlast = st1.qlast := by dsimp only [s3, s2, s1]; kp_field
  have heq : s3.putHdr .qsearch s3.qlast = shrinkHdrState st1 dst ap := by
    rw [hql3]; dsimp only [s3]; rw [hph2]; dsimp only [s2]; rw [hnv1]
    dsimp only [s1, shrinkHdrState]
    kstate_ext <;> rfl
  exact ⟨heq, by rw [heq]; rfl⟩

/-! ## 2. Parametric `Func.wp` Proof for `full_kitten_shrink` -/

/-- Parametric `Func.wp` proof for `full_kitten_shrink`. -/
theorem full_kitten_shrink_wp (Γ : Env)
    (hWatch : ∀ args m Q X, fullKittenWatchSpec args m Q X →
      Γ "full_kitten_watch" [i64, i32, i32, i32] [] args m Q X) :
    ∀ args m Q X, fullKittenShrinkSpec args m Q X →
      Func.wp Γ full_kitten_shrink_body args m Q X := by
  rintro ⟨hPtr, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hinv_s, hm, hQ⟩
  rcases hinv_s with ⟨hscr_ge, hscr_lt, hinv⟩
  let scr := s.scratch.scratch_buf
  change kMinScratchCap ≤ scr.length at hscr_ge
  change scr.length < dimacsBound at hscr_lt
  have hscr_len : scr.length = c.scratch_cap := hlen.scratch_ok.scratch_buf_len
  have hscr_8864 : 8864 ≤ scr.length := by unfold kMinScratchCap at hscr_ge; omega
  let acap := scr.length - 8864
  let ks := kittenStateOfScratch scr
  change ks.Inv acap at hinv
  have hsh := hinv.shapes
  have hcl := hinv.clauses
  have hnv := hcl.nv_le
  have hnc := hcl.nc_le
  have honc_le := hcl.orig_nc_le
  have honc_max := hcl.orig_nc_max
  have hal := hcl.alen_le
  have hacap_lt : acap < 2 ^ 28 := hcl.acap_lt
  have hmF : (FullKittenFrame c s ⋆ KittenMem (c.pScratchBuf + 1024#64) ks ⋆ R) m := by
    have hfull := fullMem_eq_kittenFrame (c := c) (s := s) hscr_8864
    rw [hfull] at hm; exact sep_ac hm
  clear hm
  c0_hsteps_nogrp
  let kPtr := c.pScratchBuf + BitVec.ofNat 64 256 * 4
  have hmA : (KittenMemA kPtr acap ks ⋆ (FullKittenFrame c s ⋆ R)) m := by
    have hm1 : (KittenMem kPtr ks ⋆ (FullKittenFrame c s ⋆ R)) m := by
      dsimp only [kPtr]; rw [kPtr_base_eq]; exact sep_ac hmF
    exact kittenMem_to_amem hsh hm1
  clear hmF
  c0_hsteps_nogrp
  -- Phase 1: Compact core-marked original clauses in `0..orig_nc`
  refine wp_while_state
    (fun p : BitVec 32 × BitVec 32 × BitVec 32 × KittenState => (p.1, (p.2.1, (p.2.2.1, ()))))
    (fun p => ks.orig_nc.toNat - p.2.2.1.toNat)
    (fun p m1 => ShrinkP1Inv acap ks p.2.2.1 p.1 p.2.1 p.2.2.2 ∧
      (KittenMemA kPtr acap p.2.2.2 ⋆ (FullKittenFrame c s ⋆ R)) m1)
    ?_ ?_
  · intro J1 hJ1
    exact wp_jump_state
      (proj := fun p : BitVec 32 × BitVec 32 × BitVec 32 × KittenState =>
        (p.1, (p.2.1, (p.2.2.1, ()))))
      (0#32, 0#32, 0#32, ks) rfl (hJ1 _ m ⟨shrinkP1_init hsh, hmA⟩)
  · rintro J1 ⟨dst, ap, i, st1⟩ m1 ⟨hp1, hm1⟩ ih1
    dsimp only at hp1 hm1
    c0_hsplit
    · have hi_lt : i.toNat < ks.orig_nc.toNat := by bv_omega
      have hi_896 : i.toNat < 896 := by unfold kMaxOrig at honc_max; omega
      have hi_wrap : i.toNat < 2 ^ 28 := by omega
      have hi1 : (i + 1#32).toNat = i.toNat + 1 := by unfold kMaxOrig at honc_max; bv_omega
      have hun_i := hp1.unread_meta i.toNat (Nat.le_refl _) hi_lt
      c0_hsteps_nogrp
      let mval := st1.clMeta[i.toNat]?.getD 0#32
      have hmval_eq : mval = kittenClauseMeta ks i.toNat := by
        simp only [mval, kittenClauseMeta, hun_i.2.1]
      refine wp_join_state
        (fun p : BitVec 32 × BitVec 32 × KittenState => (p.1, (p.2.1, ())))
        (fun p m2 => ShrinkP1Inv acap ks (i + 1#32) p.1 p.2.1 p.2.2 ∧
          (KittenMemA kPtr acap p.2.2 ⋆ (FullKittenFrame c s ⋆ R)) m2)
        ?_ ?_
      · rintro J2 ⟨dst', ap', st2⟩ m2 ⟨hp2, hm2⟩
        dsimp only at hp2 hm2
        c0_hsteps!
        exact ih1 (dst', ap', i + 1#32, st2) m2 (by dsimp only; rw [hi1]; omega) ⟨hp2, hm2⟩
      · intro J2 hJ2
        c0_hsplit
        · have hkeep : (kittenClauseMeta ks i.toNat &&& kmCore) ≠ 0#32 := by
            rw [← hmval_eq]; exact ‹_›
          c0_hsteps_nogrp
          let off := st1.clOff[i.toNat]?.getD 0#32
          let sz := mval &&& 0xFFFF#32
          have hoff_eq : off.toNat = kittenClauseOff ks i.toNat := by
            simp only [off, kittenClauseOff, hun_i.1]
          have hsz_eq : sz.toNat = kittenClauseSize ks i.toNat := by
            simp only [sz, kittenClauseSize, hmval_eq]
          have hsz_def : sz = kittenClauseMeta ks i.toNat &&& 0xFFFF#32 := by
            simp only [sz, hmval_eq]
          have hap_le_off : ap.toNat ≤ off.toNat := by
            rw [hoff_eq]; exact hp1.ap_le_off i.toNat (Nat.le_refl _) hi_lt
          have hwf_i := hcl.cl_wf i.toNat (Nat.lt_of_lt_of_le hi_lt honc_le)
          have hoff_sz_le : off.toNat + sz.toNat ≤ acap := by
            have h1 := hwf_i.2.2.1; unfold kittenClauseSpan at h1; omega
          have hdst_le_i : dst.toNat ≤ i.toNat := by
            rw [hp1.dst_eq]; exact shrinkCoreIds_length_le ks i.toNat
          have hdst_896 : dst.toNat < 896 := by unfold kMaxOrig at honc_max; omega
          have hdst_wrap : dst.toNat < 2 ^ 28 := by omega
          refine wp_join_state0 (α := KittenState)
            (fun stA mA =>
              stA = { st1 with arena := stA.arena } ∧ stA.arena.length = acap ∧
              (∀ idx < ap.toNat, stA.arena[idx]? = st1.arena[idx]?) ∧
              (∀ t < sz.toNat, stA.arena[ap.toNat + t]? = ks.arena[off.toNat + t]?) ∧
              (∀ idx, ap.toNat + sz.toNat ≤ idx → idx < acap → stA.arena[idx]? = ks.arena[idx]?) ∧
              (KittenMemA kPtr acap stA ⋆ (FullKittenFrame c s ⋆ R)) mA) ?_ ?_
          · intro J3 stA mA ⟨hA_eq, hA_len, hA_lo, hA_mid, hA_hi, hmA'⟩
            c0_hsteps!
            have haux_i : stA.clAux[i.toNat]?.getD 0#32 = ks.clAux[i.toNat]?.getD 0#32 := by
              rw [hA_eq]; simp only [hun_i.2.2]
            let st' := ((stA.putArr .clOff dst.toNat ap).putArr .clMeta dst.toNat sz).putArr
              .clAux dst.toNat (ks.clAux[i.toNat]?.getD 0#32)
            have hm_eq : (KittenMemA kPtr acap st' ⋆ (FullKittenFrame c s ⋆ R)) m := by
              refine Eq.mp (congrArg (fun x => (KittenMemA kPtr acap x ⋆ _) _) ?_) hm
              dsimp only [st']; kp_field; rw [haux_i]; rfl
            have hkeep_inv := shrinkP1_keep hinv hp1 hi_lt hkeep hA_eq hA_len hA_lo
              (fun t ht => by rw [← hoff_eq]; exact hA_mid t (hsz_eq ▸ ht))
              (fun idx h1 h2 => hA_hi idx (hsz_eq ▸ h1) h2)
            rw [← hsz_def] at hkeep_inv
            exact hJ2 (dst + 1#32, ap + sz, st') m ⟨hkeep_inv, hm_eq⟩
          · intro J3 hJ3
            c0_hsplit
            · have hap_lt_off : ap.toNat < off.toNat := by
                have hne : ap ≠ off := ‹_›
                have : ap.toNat ≠ off.toNat := fun he => hne (BitVec.eq_of_toNat_eq he)
                omega
              c0_hsteps_nogrp
              refine wp_while_state1 (fun p : BitVec 32 × KittenState => p.1)
                (fun p => sz.toNat - p.1.toNat)
                (fun p mA => p.1.toNat ≤ sz.toNat ∧
                  p.2 = { st1 with arena := p.2.arena } ∧ p.2.arena.length = acap ∧
                  (∀ idx < ap.toNat, p.2.arena[idx]? = st1.arena[idx]?) ∧
                  (∀ t < p.1.toNat, p.2.arena[ap.toNat + t]? = ks.arena[off.toNat + t]?) ∧
                  (∀ idx, ap.toNat + p.1.toNat ≤ idx → idx < acap →
                    p.2.arena[idx]? = ks.arena[idx]?) ∧
                  (KittenMemA kPtr acap p.2 ⋆ (FullKittenFrame c s ⋆ R)) mA)
                ?_ ?_
              · intro J4 hJ4
                exact wp_jump_state (proj := fun p : BitVec 32 × KittenState => (p.1, ()))
                  (0#32, st1) rfl
                  (hJ4 _ m1 ⟨by simp, by cases st1; rfl, hp1.arena_len,
                    fun _ _ => rfl, fun _ h => by simp at h,
                    fun idx h1 h2 => hp1.unread_arena idx (by simpa using h1) h2, hm1⟩)
              · rintro J4 ⟨j, stJ⟩ mA ⟨hj_le, hJ_eq, hJ_len, hJ_lo, hJ_mid, hJ_hi, hmJ⟩ ih4
                dsimp only at hj_le hJ_eq hJ_len hJ_lo hJ_mid hJ_hi hmJ
                c0_hsplit
                · have hj_lt : j.toNat < sz.toNat := by change j.toNat < sz.toNat at hc; exact hc
                  have hsrc_lt : off.toNat + j.toNat < acap := by omega
                  have hsrc_wrap : off.toNat + j.toNat < 2 ^ 28 := by omega
                  have hdst_lt : ap.toNat + j.toNat < acap := by omega
                  have hdst_wrap : ap.toNat + j.toNat < 2 ^ 28 := by omega
                  have hj1 : (j + 1#32).toNat = j.toNat + 1 := by
                    have := bv32_and_0xffff_lt mval; bv_omega
                  c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
                  c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
                  refine head_wp_load rfl
                    (KittenMemATactics.load_ka_arena_off hsrc_wrap hsrc_lt hmJ) ?_
                  refine head_wp_store rfl rfl
                    (KittenMemATactics.store_ka_arena_off _ hdst_wrap hdst_lt hmJ)
                    fun mA' hmA' => ?_
                  c0_hsteps!
                  let val := stJ.arena[off.toNat + j.toNat]?.getD 0#32
                  let stJ' := stJ.putArr .arena (ap.toNat + j.toNat) val
                  have hval_eq : val = ks.arena[off.toNat + j.toNat]?.getD 0#32 := by
                    dsimp only [val]
                    rw [hJ_hi (off.toNat + j.toNat) (by omega) hsrc_lt]
                  have har_lt' : ap.toNat + j.toNat < stJ.arena.length := by
                    rw [hJ_len]; exact hdst_lt
                  have hks_lt : off.toNat + j.toNat < ks.arena.length := by
                    rw [hsh.arena_len]; exact hsrc_lt
                  refine ih4 (j + 1#32, stJ') mA' (by dsimp only; rw [hj1]; omega)
                    ⟨by dsimp only; rw [hj1]; omega,
                     by dsimp only [stJ', KittenState.putArr]; rw [hJ_eq],
                     by dsimp only [stJ', KittenState.putArr]; simp [hJ_len],
                     ?_, ?_, ?_, hmA'⟩
                  · intro idx hidx
                    dsimp only [stJ', KittenState.putArr]
                    rw [List.getElem?_set_ne (by omega)]
                    exact hJ_lo idx hidx
                  · intro t ht
                    rw [hj1] at ht
                    dsimp only [stJ', KittenState.putArr]
                    by_cases htj : t = j.toNat
                    · subst htj
                      rw [List.getElem?_set_self har_lt', hval_eq,
                        List.getElem?_eq_getElem hks_lt, Option.getD_some]
                    · rw [List.getElem?_set_ne (by omega)]
                      exact hJ_mid t (by omega)
                  · intro idx h1 h2
                    rw [hj1] at h1
                    dsimp only [stJ', KittenState.putArr]
                    rw [List.getElem?_set_ne (by omega)]
                    exact hJ_hi idx (by omega) h2
                · have hj_eq : j.toNat = sz.toNat := by
                    change ¬ j.toNat < sz.toNat at hc; omega
                  rw [hj_eq] at hJ_mid hJ_hi
                  c0_hsteps!
                  exact hJ3 stJ mA ⟨hJ_eq, hJ_len, hJ_lo, hJ_mid, hJ_hi, hmJ⟩
            · have hap_eq_off : ap = off := ‹_›
              c0_hsteps!
              exact hJ3 st1 m1 ⟨by cases st1; rfl, hp1.arena_len,
                fun _ _ => rfl,
                fun t ht => by
                  rw [hap_eq_off]; exact hp1.unread_arena (off.toNat + t)
                    (by rw [hap_eq_off]; omega) (by omega),
                fun idx h1 h2 => hp1.unread_arena idx (by omega) h2, hm1⟩
        · have hskip : (kittenClauseMeta ks i.toNat &&& kmCore) = 0#32 := by
            rw [← hmval_eq]; exact ‹_›
          c0_hsteps!
          exact hJ2 (dst, ap, st1) m1 ⟨shrinkP1_skip hinv hp1 hi_lt hskip, hm1⟩
    · have hi_eq : i.toNat = ks.orig_nc.toNat := by have := hp1.i_le; bv_omega
      have hi_bv : i = ks.orig_nc := BitVec.eq_of_toNat_eq hi_eq
      rw [hi_bv] at hp1
      c0_hsteps_nogrp
      -- Phase 2: Header resets, then clear `vals`/`whead` (`0..2*nv`) and `lvl`/`rsn` (`0..nv`)
      obtain ⟨hstH_eq, hstH_nv_raw⟩ := shrink_hdr_store_norm st1 dst ap
      change (KittenMemA kPtr acap _ ⋆ (FullKittenFrame c s ⋆ R)) m at hm
      rw [hstH_eq] at hm
      rw [hstH_nv_raw]
      let stH := shrinkHdrState st1 dst ap
      have e_st1_nv : st1.nv = ks.nv := by rw [hp1.eq_with]
      have e_st1_ph : st1.phase = ks.phase := by rw [hp1.eq_with]
      have e_st1_ql : st1.qlast = ks.qlast := by rw [hp1.eq_with]
      have hsh1 : st1.ShapesOk acap := hp1.shapes hsh
      have hshH : stH.ShapesOk acap := shrinkHdrState_shapes dst ap hsh1
      have hnl_eq : (ks.nv <<< (1 : Nat)).toNat = 2 * ks.nv.toNat := by
        rw [bv32_shl1_toNat]; unfold kMaxV at hnv; omega
      have hstH_nv : stH.nv = ks.nv := by dsimp only [stH, shrinkHdrState]; exact e_st1_nv
      refine wp_while_state1 (fun p : BitVec 32 × KittenState => p.1)
        (fun p => 2 * ks.nv.toNat - p.1.toNat)
        (fun p m2 => p.1.toNat ≤ 2 * ks.nv.toNat ∧
          p.2 = { stH with vals := p.2.vals, whead := p.2.whead } ∧
          p.2.vals.length = 256 ∧ p.2.whead.length = 256 ∧
          (∀ l < p.1.toNat, p.2.vals[l]? = some 0#32 ∧ p.2.whead[l]? = some 0xFFFFFFFF#32) ∧
          (KittenMemA kPtr acap p.2 ⋆ (FullKittenFrame c s ⋆ R)) m2)
        ?_ ?_
      · intro J2 hJ2
        exact wp_jump_state (proj := fun p : BitVec 32 × KittenState => (p.1, ()))
          (0#32, stH) rfl
          (hJ2 _ m ⟨by simp, rfl,
            hshH.vals_len, hshH.whead_len, fun _ h => by simp at h, hm⟩)
      · rintro J2 ⟨k, st2a⟩ m2 ⟨hk_le, h2a_eq, h2a_vl, h2a_wh, hlits2a, hm2⟩ ih2
        dsimp only at hk_le h2a_eq h2a_vl h2a_wh hlits2a hm2
        c0_hsplit
        · have hk_lt : k.toNat < 2 * ks.nv.toNat := by
            rw [e_st1_nv, hnl_eq] at hc; exact hc
          have hk_256 : k.toNat < 256 := by unfold kMaxV at hnv; omega
          have hk_wrap : k.toNat < 2 ^ 28 := by omega
          have hk1 : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
          c0_hsteps!
          let st2a' := (st2a.putArr .vals k.toNat 0#32).putArr .whead k.toNat 0xFFFFFFFF#32
          refine ih2 (k + 1#32, st2a') _ (by dsimp only; rw [hk1]; omega)
            ⟨by dsimp only; rw [hk1]; omega,
             by dsimp only [st2a', KittenState.putArr]; rw [h2a_eq],
             by dsimp only [st2a', KittenState.putArr]; simp [h2a_vl],
             by dsimp only [st2a', KittenState.putArr]; simp [h2a_wh], ?_, hm⟩
          intro l hl
          rw [hk1] at hl
          dsimp only [st2a', KittenState.putArr]
          by_cases hlk : l = k.toNat
          · subst hlk
            rw [List.getElem?_set_self (by omega), List.getElem?_set_self (by omega)]
            exact ⟨rfl, rfl⟩
          · rw [List.getElem?_set_ne (Ne.symm hlk), List.getElem?_set_ne (Ne.symm hlk)]
            exact hlits2a l (by omega)
        · have hk_eq : k.toNat = 2 * ks.nv.toNat := by
            rw [e_st1_nv, hnl_eq] at hc; omega
          rw [hk_eq] at hlits2a
          c0_hsteps_nogrp
          have h2a_nv : st2a.nv = ks.nv := by rw [h2a_eq]; exact hstH_nv
          refine wp_while_state1 (fun p : BitVec 32 × KittenState => p.1)
            (fun p => ks.nv.toNat - p.1.toNat)
            (fun p m3 => p.1.toNat ≤ ks.nv.toNat ∧
              p.2 = { st2a with lvlArr := p.2.lvlArr, rsn := p.2.rsn } ∧
              p.2.lvlArr.length = 128 ∧ p.2.rsn.length = 128 ∧
              (∀ v < p.1.toNat, p.2.lvlArr[v]? = some 0#32 ∧ p.2.rsn[v]? = some 0xFFFFFFFF#32) ∧
              (KittenMemA kPtr acap p.2 ⋆ (FullKittenFrame c s ⋆ R)) m3)
            ?_ ?_
          · intro J3 hJ3
            exact wp_jump_state (proj := fun p : BitVec 32 × KittenState => (p.1, ()))
              (0#32, st2a) rfl
              (hJ3 _ m2 ⟨by simp, by cases st2a; rfl, by rw [h2a_eq]; exact hshH.lvlArr_len,
                by rw [h2a_eq]; exact hshH.rsn_len, fun _ h => by simp at h, hm2⟩)
          · rintro J3 ⟨v, st3⟩ m3 ⟨hv_le, h3_eq, h3_la, h3_rs, hvars3, hm3⟩ ih3
            dsimp only at hv_le h3_eq h3_la h3_rs hvars3 hm3
            have h3_nv : st3.nv = ks.nv := by rw [h3_eq]; exact h2a_nv
            c0_hsplit
            · have hv_lt : v.toNat < ks.nv.toNat := by rw [← h3_nv]; bv_omega
              have hv_128 : v.toNat < 128 := by unfold kMaxV at hnv; omega
              have hv_wrap : v.toNat < 2 ^ 28 := by omega
              have hv1 : (v + 1#32).toNat = v.toNat + 1 := by bv_omega
              c0_hsteps!
              let st3' := (st3.putArr .lvlArr v.toNat 0#32).putArr .rsn v.toNat 0xFFFFFFFF#32
              refine ih3 (v + 1#32, st3') _ (by dsimp only; rw [hv1]; omega)
                ⟨by dsimp only; rw [hv1]; omega,
                 by dsimp only [st3', KittenState.putArr]; rw [h3_eq],
                 by dsimp only [st3', KittenState.putArr]; simp [h3_la],
                 by dsimp only [st3', KittenState.putArr]; simp [h3_rs], ?_, hm⟩
              intro w hw
              rw [hv1] at hw
              dsimp only [st3', KittenState.putArr]
              by_cases hwv : w = v.toNat
              · subst hwv
                rw [List.getElem?_set_self (by omega), List.getElem?_set_self (by omega)]
                exact ⟨rfl, rfl⟩
              · rw [List.getElem?_set_ne (Ne.symm hwv), List.getElem?_set_ne (Ne.symm hwv)]
                exact hvars3 w (by omega)
            · have hv_eq : v.toNat = ks.nv.toNat := by rw [h3_nv] at hc; omega
              rw [hv_eq] at hvars3
              have hsh3 : st3.ShapesOk acap := (kittenMemA_to_mem hm3).1
              have hst3_from_st1 : st3 =
                  { st1 with
                    nc := dst, orig_nc := dst, alen := ap, lvl := 0#32, prop := 0#32,
                    trl_end := 0#32, unass := ks.nv, incons := 0xFFFFFFFF#32,
                    failing := 0xFFFFFFFF#32, nunits := 0#32, phase := ks.phase ^^^ 1#32,
                    qsearch := ks.qlast, vals := st3.vals, whead := st3.whead,
                    lvlArr := st3.lvlArr, rsn := st3.rsn } := by
                rw [h3_eq, h2a_eq]
                dsimp only [stH, shrinkHdrState]
                rw [e_st1_nv, e_st1_ph, e_st1_ql]
              have hlits3 : ∀ l < 2 * ks.nv.toNat,
                  st3.vals[l]? = some 0#32 ∧ st3.whead[l]? = some 0xFFFFFFFF#32 := by
                intro l hl; rw [h3_eq]; exact hlits2a l hl
              have hb3 := shrinkP2_build_st3 hinv hp1 hst3_from_st1 hsh3 hlits3 hvars3
              have hinv3 := hb3.1
              have hsync3 := hb3.2.1
              have hp3_0 := hb3.2.2.1
              have h3_nc : st3.nc = dst := by rw [hst3_from_st1]
              c0_hsteps_nogrp
              -- Phase 3: Re-register empty, unit, and 2WL-watched clauses (`0..dst`)
              refine wp_while_state1 (fun p : BitVec 32 × KittenState => p.1)
                (fun p => dst.toNat - p.1.toNat)
                (fun p m4 => ShrinkP3Inv acap st3 p.1 p.2 ∧
                  (KittenMemA kPtr acap p.2 ⋆ (FullKittenFrame c s ⋆ R)) m4)
                ?_ ?_
              · intro J4 hJ4
                exact wp_jump_state (proj := fun p : BitVec 32 × KittenState => (p.1, ()))
                  (0#32, st3) rfl (hJ4 _ m3 ⟨hp3_0, hm3⟩)
              · rintro J4 ⟨ci, st4⟩ m4 ⟨hp4, hm4⟩ ih4
                dsimp only at hp4 hm4
                c0_hsplit
                · have hci_lt : ci.toNat < st3.nc.toNat := by rw [h3_nc]; bv_omega
                  have hci_896 : ci.toNat < 896 := by
                    have := hinv3.clauses.nc_le; unfold kMaxCl at this; omega
                  have hci_wrap : ci.toNat < 2 ^ 28 := by omega
                  have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := by
                    have := hinv3.clauses.nc_le; unfold kMaxCl at this; bv_omega
                  c0_hsteps_nogrp
                  let off := st4.clOff[ci.toNat]?.getD 0#32
                  let sz := st4.clMeta[ci.toNat]?.getD 0#32 &&& 0xFFFF#32
                  have hoff_eq : off.toNat = kittenClauseOff st3 ci.toNat := by
                    have e_co : st4.clOff = st3.clOff := by rw [hp4.eq_with]
                    simp only [off, kittenClauseOff, e_co]
                  have hsz_eq : sz.toNat = kittenClauseSize st3 ci.toNat := by
                    have e_cm : st4.clMeta = st3.clMeta := by rw [hp4.eq_with]
                    simp only [sz, kittenClauseSize, kittenClauseMeta, e_cm]
                  refine wp_join_state0 (α := KittenState)
                    (fun st5 m5 => ShrinkP3Inv acap st3 (ci + 1#32) st5 ∧
                      (KittenMemA kPtr acap st5 ⋆ (FullKittenFrame c s ⋆ R)) m5) ?_ ?_
                  · intro J5 st5 m5 ⟨hp5, hm5⟩
                    c0_hsteps!
                    exact ih4 (ci + 1#32, st5) m5
                      (by dsimp only; rw [hci1, ← h3_nc]; omega) ⟨hp5, hm5⟩
                  · intro J5 hJ5
                    c0_hsplit
                    · have hsz0 : kittenClauseSize st3 ci.toNat = 0 := by
                        rw [← hsz_eq, show sz = 0#32 from ‹_›]; rfl
                      c0_hsteps!
                      · exact hJ5 _ _
                          ⟨shrinkP3_step_incons hp4 hci_lt hinv3.clauses.nc_le hsz0, hm⟩
                      · exact hJ5 _ _
                          ⟨shrinkP3_step_noop hp4 hci_lt hinv3.clauses.nc_le (by omega), hm4⟩
                    · c0_hstep; c0_hsplit
                      · have hsz1 : kittenClauseSize st3 ci.toNat = 1 := by
                          rw [← hsz_eq, show sz = 1#32 from ‹_›]; rfl
                        c0_hsteps_nogrp
                        c0_hstep; c0_hsplit
                        · have hnu_lt : st4.nunits.toNat < 256 := by bv_omega
                          have hnu_wrap : st4.nunits.toNat < 2 ^ 28 := by omega
                          c0_hsteps!
                          exact hJ5 _ _
                            ⟨shrinkP3_step_unit hp4 hci_lt hinv3.clauses.nc_le hnu_lt hsz1, hm⟩
                        · c0_hsteps!
                          exact hJ5 _ _
                            ⟨shrinkP3_step_noop hp4 hci_lt hinv3.clauses.nc_le (by omega), hm4⟩
                      · have hsz2 : 2 ≤ kittenClauseSize st3 ci.toNat := by
                          have hne0 : sz ≠ 0#32 := ‹_›
                          have hne1 : sz ≠ 1#32 := ‹_›
                          have h0 : sz.toNat ≠ 0 := fun h => hne0 (BitVec.eq_of_toNat_eq h)
                          have h1 : sz.toNat ≠ 1 := fun h => hne1 (BitVec.eq_of_toNat_eq h)
                          omega
                        have hwf_ci := hinv3.clauses.cl_wf ci.toNat hci_lt
                        have hspan_ci : off.toNat + sz.toNat ≤ acap := by
                          have h1 := hwf_ci.2.2.1; unfold kittenClauseSpan at h1
                          have h2 := hinv3.clauses.alen_le; omega
                        have ho0_lt : off.toNat < acap := by omega
                        have ho0_wrap : off.toNat < 2 ^ 28 := by omega
                        have ho1_lt : off.toNat + (1#32 : BitVec 32).toNat < acap := by simp; omega
                        have ho1_wrap : off.toNat + (1#32 : BitVec 32).toNat < 2 ^ 28 := by
                          simp; omega
                        c0_hstep; c0_hstep; c0_hstep; c0_hstep
                        refine head_wp_load rfl
                          (KittenMemATactics.load_ka_arena ho0_wrap ho0_lt hm4) ?_
                        c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
                        refine head_wp_load rfl
                          (KittenMemATactics.load_ka_arena_off ho1_wrap ho1_lt hm4) ?_
                        let l0 := st4.arena[off.toNat]?.getD 0#32
                        let l1 := st4.arena[off.toNat + (1#32 : BitVec 32).toNat]?.getD 0#32
                        have har_eq4 : st4.arena = st3.arena := by rw [hp4.eq_with]
                        have hmem0 : l0.toNat ∈ kittenClauseLits st3 ci.toNat := by
                          unfold kittenClauseLits; rw [List.mem_map]
                          have hlt : off.toNat < st3.arena.length := by
                            rw [hsh3.arena_len]; exact ho0_lt
                          refine ⟨st3.arena[off.toNat]'hlt, ?_, ?_⟩
                          · rw [List.mem_iff_getElem]
                            exact ⟨0, by simp [List.length_take, List.length_drop,
                              hsh3.arena_len, ← hoff_eq]; omega,
                              by simp [List.getElem_take, List.getElem_drop, ← hoff_eq]⟩
                          · simp only [l0, har_eq4, List.getElem?_eq_getElem hlt, Option.getD_some]
                        have hmem1 : l1.toNat ∈ kittenClauseLits st3 ci.toNat := by
                          unfold kittenClauseLits; rw [List.mem_map]
                          have hlt : off.toNat + 1 < st3.arena.length := by
                            rw [hsh3.arena_len]; omega
                          refine ⟨st3.arena[off.toNat + 1]'hlt, ?_, ?_⟩
                          · rw [List.mem_iff_getElem]
                            exact ⟨1, by simp [List.length_take, List.length_drop,
                              hsh3.arena_len, ← hoff_eq]; omega,
                              by simp [List.getElem_take, List.getElem_drop, ← hoff_eq]⟩
                          · simp only [l1, har_eq4, show (1#32 : BitVec 32).toNat = 1 by decide,
                              List.getElem?_eq_getElem hlt, Option.getD_some]
                        have hl0_lt : l0.toNat < 2 * st3.nv.toNat := hwf_ci.2.2.2.1 _ hmem0
                        have hl1_lt : l1.toNat < 2 * st3.nv.toNat := hwf_ci.2.2.2.1 _ hmem1
                        have e_nv4 : st4.nv = st3.nv := by rw [hp4.eq_with]
                        c0_call hWatch
                        obtain ⟨hsh4, hm4_raw⟩ := kittenMemA_to_mem hm4
                        refine ⟨acap, st4, FullKittenFrame c s ⋆ R, hsh4, hacap_lt,
                          by rw [e_nv4]; exact hinv3.clauses.nv_le, hci_896,
                          by rw [e_nv4]; exact hl0_lt, by rw [e_nv4]; exact hl1_lt, hm4_raw,
                          fun mW hmW => ?_⟩
                        c0_hsteps!
                        have hp5 := shrinkP3_step_watch hinv3 hp4 hci_lt hsz2 hl0_lt hl1_lt
                          (by rw [← hoff_eq, ← har_eq4])
                          (by rw [← hoff_eq, ← har_eq4]; rfl)
                        exact hJ5 _ mW ⟨hp5, kittenMem_to_amem hp5.sh hmW⟩
                · have hci_eq : ci = st3.nc := by
                    apply BitVec.eq_of_toNat_eq
                    have hge : dst.toNat ≤ ci.toNat := by bv_omega
                    have hle := hp4.i_le; rw [h3_nc] at hle ⊢; omega
                  rw [hci_eq] at hp4
                  c0_hsteps!
                  obtain ⟨hinv4, hsync4⟩ := shrinkP3_finish hinv3 hsync3 hp4
                  have hsh4 := hp4.sh
                  obtain ⟨_, hm4'⟩ := kittenMemA_to_mem hm4
                  have hm4'_exp :
                      (FullKittenFrame c s ⋆ KittenMem (c.pScratchBuf + 1024#64) st4 ⋆ R) m4 := by
                    dsimp only [kPtr] at hm4'; rw [kPtr_base_eq] at hm4'; exact sep_ac hm4'
                  have hmJ := fullMem_join_kitten (c := c) (s := s) (acap := acap) (ks' := st4)
                    (R := R) (by change 256 ≤ scr.length; omega) hsh4 hm4'_exp
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
                    exact hinv4
                  have horig4 : kittenOrigClauses st4 = kittenOrigClauses st3 :=
                    kittenOrigClauses_eq_of (by rw [hp4.eq_with]) fun ci _ => by
                      unfold kittenClauseLits kittenClauseOff kittenClauseSize kittenClauseMeta
                      rw [hp4.eq_with]
                  have hass4 : kittenAssumpLits st4 = kittenAssumpLits st3 := by
                    unfold kittenAssumpLits; rw [hp4.eq_with]
                  exact hQ scr' m4 (fullState_lengthsOk_scratch hlen hscr'_len) hpre hks_inv
                    (by rw [hof]; exact hsync4)
                    (by rw [hof, hp4.eq_with]; exact hb3.2.2.2.1)
                    (by rw [hof, hp4.eq_with]; exact hb3.2.2.2.2.1)
                    (by rw [hof, hp4.eq_with]; exact hb3.2.2.2.2.2.1)
                    (by rw [hof, hp4.eq_with]; exact hb3.2.2.2.2.2.2.1)
                    (by rw [hof, hp4.eq_with]; exact hb3.2.2.2.2.2.2.2.1)
                    (by rw [hof, hp4.eq_with]; exact hb3.2.2.2.2.2.2.2.2.1)
                    (by unfold kittenAssumpLitsS; rw [hof, hass4]
                        exact hb3.2.2.2.2.2.2.2.2.2.1)
                    (by unfold kittenOrigClausesS kittenCoreClausesS; rw [hof, horig4]
                        exact hb3.2.2.2.2.2.2.2.2.2.2.1)
                    (by unfold kittenOrigClausesS; rw [hof, horig4]
                        exact hb3.2.2.2.2.2.2.2.2.2.2.2.1)
                    (by unfold kittenOrigClausesS; rw [hof, horig4]
                        exact hb3.2.2.2.2.2.2.2.2.2.2.2.2.1)
                    (by rw [hof, show st4.orig_nc = st3.orig_nc by rw [hp4.eq_with]]
                        have haux4 : kittenClauseAux st4 = kittenClauseAux st3 :=
                          funext fun ci => by unfold kittenClauseAux; rw [hp4.eq_with]
                        rw [haux4]; exact hb3.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
                    (by intro ci hci
                        rw [hof, show st4.orig_nc = st3.orig_nc by rw [hp4.eq_with]] at hci
                        rw [hof, show kittenClauseMeta st4 ci = kittenClauseMeta st3 ci by
                          unfold kittenClauseMeta; rw [hp4.eq_with]]
                        exact hb3.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ci hci)
                    (by rw [hof]; intro w hw hsz
                        have hw3 : w < 2 * st3.nc.toNat := by
                          rwa [show st4.nc = st3.nc by rw [hp4.eq_with]] at hw
                        have hsz_eq :
                            kittenClauseSize st4 (w / 2) = kittenClauseSize st3 (w / 2) := by
                          unfold kittenClauseSize kittenClauseMeta; rw [hp4.eq_with]
                        have hlits_eq :
                            kittenClauseLits st4 (w / 2) = kittenClauseLits st3 (w / 2) := by
                          unfold kittenClauseLits kittenClauseOff kittenClauseSize kittenClauseMeta
                          rw [hp4.eq_with]
                        rw [hsz_eq] at hsz
                        rw [hlits_eq]
                        exact hp4.wblit_ok w hw3 hsz)
                    hmJ

end LeanQbe.T.Examples.Kissat.Full
