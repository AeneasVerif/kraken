module

public import LeanQbe.T.Examples.Kissat.FullKittenLemmas
public import LeanQbe.T.Examples.Kissat.FullDefSweepLemmas
public import LeanQbe.T.Examples.Kissat.FullFastBveBudgetsLemmas1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` M2 Cross-Slice Adapters (`FullKitten` <-> `FullDefSweep` <-> `FullFastBveBudgets`)

Bridges the concrete `FullKitten` scratch invariant (`KittenScratchInv`, `KittenCnfPermEquiv`,
`KittenWblitInClause`) to `FullDefSweep.KittenInvLaws` (`fastKInv` / `fastKInv_laws`) and adapts
all cross-slice `Spec` contracts needed to close `FullFastProof` (`196/196`) unconditionally:
1. `fastKInv` + `fastKInv_laws : FullDefSweep.KittenInvLaws fastKInv`
2. `6` Kitten entry adapters (`full_kitten_{init,add_clause,solve,core,shrink,flip}`)
3. `4` non-Kitten extern adapters (`full_cong_try_xor_ite`, `full_cong_hash_step`,
   `full_add_unit`, and `full_bve_gates` `FullDefSweep` -> `FullFastBveBudgets`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullFast

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. Concrete `fastKInv` & `KittenInvLaws` -/

/-- Concrete `Kitten` scratch invariant bridging `FullKitten` (`KittenScratchInv`,
`KittenCnfPermEquiv`, `KittenWblitInClause`) to `FullDefSweep.KittenInvLaws`. -/
def fastKInv (nv : Nat) (cls : List (Nat × List Nat)) (ta : Bool)
    (ph : FullDefSweep.KittenPhase) (scr : List (BitVec 32)) : Prop :=
  let ks := kittenStateOfScratch scr
  KittenScratchInv scr ∧
  1 ≤ nv ∧ nv ≤ 128 ∧ ks.nv = BitVec.ofNat 32 nv ∧
  cls.length ≤ 512 ∧ ks.orig_nc = BitVec.ofNat 32 cls.length ∧
  (∀ (i : Nat) (hi : i < cls.length), (ks.clAux[i]?.getD 0#32).toNat = (cls[i]'hi).1) ∧
  KittenCnfPermEquiv (kittenOrigClauses ks) (cls.map Prod.snd) ∧
  (∀ c ∈ cls, ∀ l ∈ c.2, l < 2 * nv) ∧
  ((ks.ante ≠ 0#32) ↔ ta = true) ∧
  ks.nassump.toNat ≤ 2 ∧
  (ph = .fresh →
    KittenTrailSynced ks ∧ ks.lvl = 0#32 ∧ ks.trl_end = 0#32 ∧
    ks.nc = ks.orig_nc ∧ KittenWblitInClause ks) ∧
  (ph = .unsatReady →
    (ks.incons ≠ 0xFFFFFFFF#32 ∨ ks.failing ≠ 0xFFFFFFFF#32) ∧ ks.nassump = 0#32)

private theorem bv32_ofNat_toNat_le {n : Nat} (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

private theorem ks_getElem_slice (scr : List (BitVec 32)) (off len i : Nat) (hi : i < len) :
    (((scr.drop 256).drop off).take len)[i]? = scr[256 + off + i]? := by
  rw [List.getElem?_take_of_lt hi, List.getElem?_drop, List.getElem?_drop, Nat.add_assoc]

private theorem nodup_flatten_take {α : Type _} (xs : List (List α)) (n : Nat)
    (h : xs.flatten.Nodup) : (xs.take n).flatten.Nodup := by
  rw [← List.take_append_drop n xs, List.flatten_append, List.nodup_append] at h
  exact h.1

private theorem kittenClauseLits_perm_cls {ks : KittenState} {cls : List (Nat × List Nat)}
    (honc : ks.orig_nc = BitVec.ofNat 32 cls.length) (hcl : cls.length ≤ 512)
    (hperm : KittenCnfPermEquiv (kittenOrigClauses ks) (cls.map Prod.snd))
    {cid : Nat} (hcid : cid < cls.length) :
    (kittenClauseLits ks cid).Perm (cls[cid]'hcid).2 := by
  have h1 : ks.orig_nc.toNat = cls.length := by
    rw [honc]; exact bv32_ofNat_toNat_le (by omega)
  have hlen : (kittenOrigClauses ks).length = cls.length := by
    simp [kittenOrigClauses, h1]
  have hp := hperm.2 cid (by omega)
  have hL : (kittenOrigClauses ks)[cid]! = kittenClauseLits ks cid := by
    rw [List.getElem!_eq_getElem?_getD, kittenOrigClauses, List.getElem?_map,
      List.getElem?_range (by omega)]
    rfl
  have hR : (cls.map Prod.snd)[cid]! = (cls[cid]'hcid).2 := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hcid]
    rfl
  rwa [hL, hR] at hp

private theorem kittenState_set_nv_eq {scr : List (BitVec 32)} (hlen : 10240 ≤ scr.length)
    (nv' : Nat) :
    let scr' := (scr.set 256 (BitVec.ofNat 32 nv')).set 262 (BitVec.ofNat 32 nv')
    kittenStateOfScratch scr' =
      { kittenStateOfScratch scr with
        nv := BitVec.ofNat 32 nv'
        unass := BitVec.ofNat 32 nv' } := by
  intro scr'
  have hdrop : ∀ a b, 25 ≤ a →
      ((scr'.drop 256).drop a).take b = ((scr.drop 256).drop a).take b := by
    intro a b ha
    apply List.ext_getElem?; intro k
    by_cases hk : k < b
    · rw [ks_getElem_slice _ _ _ _ hk, ks_getElem_slice _ _ _ _ hk]
      simp only [scr']
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  have harena : (scr'.drop 256).drop 8608 = (scr.drop 256).drop 8608 := by
    apply List.ext_getElem?; intro k
    simp only [List.getElem?_drop, scr']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  have hne : ∀ j, j ≠ 0 → j ≠ 6 →
      (scr'.drop 256)[j]?.getD 0#32 = (scr.drop 256)[j]?.getD 0#32 := by
    intro j h0 h6
    simp only [List.getElem?_drop, scr']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
  have h0 : (scr'.drop 256)[0]?.getD 0#32 = BitVec.ofNat 32 nv' := by
    simp only [List.getElem?_drop, Nat.add_zero, scr']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some]
  have h6 : (scr'.drop 256)[6]?.getD 0#32 = BitVec.ofNat 32 nv' := by
    simp only [List.getElem?_drop, scr']
    rw [List.getElem?_set_self (by simp; omega), Option.getD_some]
  dsimp only [kittenStateOfScratch, KittenState.ofSlab]
  congr 1
  all_goals first
    | rfl
    | exact h0
    | exact h6
    | exact hne _ (by decide) (by decide)
    | exact hdrop _ _ (by decide)
    | exact harena

private theorem kittenState_set_assumps_eq {scr scr' : List (BitVec 32)}
    (hpres : ∀ i, i ≠ 256 + 18 → i ≠ 256 + 1184 → i ≠ 256 + 1185 → scr'[i]? = scr[i]?) :
    kittenStateOfScratch scr' =
      { kittenStateOfScratch scr with
        nassump := scr'[256 + 18]?.getD 0#32
        assump := ((scr'.drop 256).drop 1184).take 128 } := by
  have hslice : ∀ a b, (a + b ≤ 1184 ∨ 1186 ≤ a) → 25 ≤ a →
      ((scr'.drop 256).drop a).take b = ((scr.drop 256).drop a).take b := by
    intro a b hdisj ha
    apply List.ext_getElem?; intro k
    by_cases hk : k < b
    · rw [ks_getElem_slice _ _ _ _ hk, ks_getElem_slice _ _ _ _ hk]
      exact hpres _ (by omega) (by omega) (by omega)
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  have harena : (scr'.drop 256).drop 8608 = (scr.drop 256).drop 8608 := by
    apply List.ext_getElem?; intro k
    simp only [List.getElem?_drop]
    exact hpres _ (by omega) (by omega) (by omega)
  have hne : ∀ j, j ≠ 18 → j < 25 →
      (scr'.drop 256)[j]?.getD 0#32 = (scr.drop 256)[j]?.getD 0#32 := by
    intro j h18 hj
    simp only [List.getElem?_drop]
    rw [hpres _ (by omega) (by omega) (by omega)]
  dsimp only [kittenStateOfScratch, KittenState.ofSlab]
  congr 1
  all_goals first
    | rfl
    | (rw [List.getElem?_drop]; done)
    | exact hne _ (by decide) (by decide)
    | exact hslice _ _ (by omega) (by decide)
    | exact harena

/-- `fastKInv` satisfies every law required by `FullDefSweep.KittenInvLaws`. -/
theorem fastKInv_laws : FullDefSweep.KittenInvLaws fastKInv where
  cap_ok h := ⟨h.1.1, h.2.1, h.2.2.1, h.2.2.2.2.1⟩
  orig_nc_eq {nv cls ta ph scr} h := by
    rcases h with ⟨_, _, _, _, hcl, honc, _⟩
    have h1 : (kittenStateOfScratch scr).orig_nc.toNat = cls.length := by
      rw [honc]; exact bv32_ofNat_toNat_le (by omega)
    simpa [kittenStateOfScratch, KittenState.ofSlab, List.getElem?_drop] using h1
  cl_aux_eq {nv cls ta ph scr} h i hi := by
    rcases h with ⟨_, _, _, _, hcl, _, haux, _⟩
    have h1 := haux i hi
    have hget : (kittenStateOfScratch scr).clAux[i]? = scr[256 + 7712 + i]? :=
      ks_getElem_slice scr 7712 896 i (by omega)
    rwa [hget] at h1
  lits_lt h := h.2.2.2.2.2.2.2.2.1
  nassump_ok {nv cls ta ph scr} h := by
    rcases h with ⟨hscr, _, hnv128, hnv, _, _, _, _, _, _, hna, _, _⟩
    have hna' : (scr[256 + 18]?.getD 0#32).toNat ≤ 2 := by
      simpa [kittenStateOfScratch, KittenState.ofSlab, List.getElem?_drop] using hna
    refine ⟨hna', fun i hi => ?_⟩
    have ha := hscr.2.2.clauses.assump_ok i (by
      simpa [kittenStateOfScratch, KittenState.ofSlab, List.getElem?_drop] using hi)
    have hget : (kittenStateOfScratch scr).assump[i]? = scr[256 + 1184 + i]? :=
      ks_getElem_slice scr 1184 128 i (by omega)
    rw [hget, hnv, bv32_ofNat_toNat_le (by omega)] at ha
    exact ha
  set_nv {nv nv' cls ta scr} h h1 hnv' hna hlt := by
    rcases h with ⟨⟨hlen1, hlen2, hinv⟩, h1_old, hnv128, hnv_eq, hcl512, honc, haux, hperm,
      _, hante, hna_le, hfresh, _⟩
    obtain ⟨hsync, hlvl0, htrl0, hnc_eq, hwblit⟩ := hfresh rfl
    let scr' := (scr.set 256 (BitVec.ofNat 32 nv')).set 262 (BitVec.ofNat 32 nv')
    let ks := kittenStateOfScratch scr
    have hks' : kittenStateOfScratch scr' =
        { ks with nv := BitVec.ofNat 32 nv', unass := BitVec.ofNat 32 nv' } :=
      kittenState_set_nv_eq hlen1 nv'
    have hlen' : scr'.length = scr.length := by simp [scr']
    have hnv'_toNat : (BitVec.ofNat 32 nv').toNat = nv' := bv32_ofNat_toNat_le (by omega)
    have hnv_toNat : (kittenStateOfScratch scr).nv.toNat = nv := by
      rw [hnv_eq]; exact bv32_ofNat_toNat_le (by omega)
    have honc_toNat : (kittenStateOfScratch scr).orig_nc.toNat = cls.length := by
      rw [honc]; exact bv32_ofNat_toNat_le (by omega)
    have hna0 : (kittenStateOfScratch scr).nassump.toNat = 0 := by
      simpa [kittenStateOfScratch, KittenState.ofSlab, List.getElem?_drop] using hna
    have hcl_lt' : ∀ cid < ks.nc.toNat, ∀ l ∈ kittenClauseLits ks cid, l < 2 * nv' := by
      intro cid hcid l hl
      have hcid' : cid < cls.length := by
        change cid < (kittenStateOfScratch scr).nc.toNat at hcid
        rw [hnc_eq, honc_toNat] at hcid; exact hcid
      have hp := kittenClauseLits_perm_cls honc hcl512 hperm hcid'
      exact hlt (cls[cid]'hcid') (List.getElem_mem hcid') l (hp.mem_iff.mp hl)
    have hinv' : (kittenStateOfScratch scr').Inv (scr'.length - 8864) := by
      rw [hks', hlen']
      have hsh_ok : ({ ks with nv := BitVec.ofNat 32 nv', unass := BitVec.ofNat 32 nv' } :
          KittenState).ShapesOk (scr.length - 8864) :=
        { hinv.shapes with }
      have hcl_ok : KittenClausesOk (scr.length - 8864)
          { ks with nv := BitVec.ofNat 32 nv', unass := BitVec.ofNat 32 nv' } :=
        { acap_ge := hinv.clauses.acap_ge
          acap_lt := hinv.clauses.acap_lt
          acap_eq := hinv.clauses.acap_eq
          nv_le := by
            change (BitVec.ofNat 32 nv').toNat ≤ kMaxV; rw [hnv'_toNat]; unfold kMaxV; omega
          nc_le := hinv.clauses.nc_le
          orig_nc_le := hinv.clauses.orig_nc_le
          orig_nc_max := hinv.clauses.orig_nc_max
          alen_le := hinv.clauses.alen_le
          nassump_le := hinv.clauses.nassump_le
          nunits_le := hinv.clauses.nunits_le
          nres_le := hinv.clauses.nres_le
          nkl_le := hinv.clauses.nkl_le
          nana_le := hinv.clauses.nana_le
          cl_wf := fun cid hcid => by
            have hwf := hinv.clauses.cl_wf cid hcid
            exact ⟨hwf.1, hwf.2.1, hwf.2.2.1, fun l hl => by
              change l < 2 * (BitVec.ofNat 32 nv').toNat; rw [hnv'_toNat]
              exact hcl_lt' cid hcid l hl, hwf.2.2.2.2.1, hwf.2.2.2.2.2⟩
          cl_mono := hinv.clauses.cl_mono
          units_ok := hinv.clauses.units_ok
          incons_ok := hinv.clauses.incons_ok
          failing_ok := hinv.clauses.failing_ok
          assump_ok := fun i hi => by
            change i < (kittenStateOfScratch scr).nassump.toNat at hi; omega
          flags_clean := fun v hv => by
            change v < (BitVec.ofNat 32 nv').toNat at hv; rw [hnv'_toNat] at hv
            exact hinv.clauses.flags_clean v (by rw [hnv_toNat]; omega) }
      have hwat_ok : KittenWatchesOk
          { ks with nv := BitVec.ofNat 32 nv', unass := BitVec.ofNat 32 nv' } := by
        obtain ⟨chains, hclen, hnodup, hch, hmem⟩ := hinv.watches
        refine ⟨chains.take (2 * nv'), ?_, nodup_flatten_take chains (2 * nv') hnodup, ?_, ?_⟩
        · change (chains.take (2 * nv')).length = 2 * (BitVec.ofNat 32 nv').toNat
          rw [hnv'_toNat, List.length_take, hclen, hnv_toNat]; omega
        · intro l hl
          change l < 2 * (BitVec.ofNat 32 nv').toNat at hl; rw [hnv'_toNat] at hl
          rw [List.getElem?_take_of_lt hl]
          exact hch l (by rw [hnv_toNat]; omega)
        · intro l hl w hw
          change l < 2 * (BitVec.ofNat 32 nv').toNat at hl; rw [hnv'_toNat] at hl
          rw [List.getElem?_take_of_lt hl] at hw
          obtain ⟨hw_lt, hsz, har, _⟩ := hmem l (by rw [hnv_toNat]; omega) w hw
          refine ⟨hw_lt, hsz, har, ?_⟩
          change w < 2 * ks.nc.toNat at hw_lt
          change (ks.wblit[w]?.getD 0#32).toNat < 2 * (BitVec.ofNat 32 nv').toNat
          rw [hnv'_toNat]
          exact hcl_lt' (w / 2) (by omega) _ (hwblit w hw_lt hsz)
      have htrl_nat : (kittenStateOfScratch scr).trl_end.toNat = 0 := by rw [htrl0]; rfl
      have hba_ok : KittenBaseAssignOk
          { ks with nv := BitVec.ofNat 32 nv', unass := BitVec.ofNat 32 nv' } :=
        { trl_end_le := by
            change (kittenStateOfScratch scr).trl_end.toNat ≤ (BitVec.ofNat 32 nv').toNat
            rw [htrl_nat]; omega
          prop_le := hinv.assign.prop_le
          unass_eq := by
            change (BitVec.ofNat 32 nv').toNat + (kittenStateOfScratch scr).trl_end.toNat =
              (BitVec.ofNat 32 nv').toNat
            rw [htrl_nat]; omega
          vals_dom := fun l hl => by
            change l < 2 * (BitVec.ofNat 32 nv').toNat at hl; rw [hnv'_toNat] at hl
            exact hinv.assign.vals_dom l (by rw [hnv_toNat]; omega)
          vals_neg_iff := fun l hl => by
            change l < 2 * (BitVec.ofNat 32 nv').toNat at hl; rw [hnv'_toNat] at hl
            exact hinv.assign.vals_neg_iff l (by rw [hnv_toNat]; omega)
          vals_nz_iff_trl := fun l hl => by
            change l < 2 * (BitVec.ofNat 32 nv').toNat at hl; rw [hnv'_toNat] at hl
            exact hinv.assign.vals_nz_iff_trl l (by rw [hnv_toNat]; omega)
          trl_nodup := hinv.assign.trl_nodup
          trl_lt := fun l hl => by
            unfold kittenTrailLits at hl
            change l ∈ ((kittenStateOfScratch scr).trl.take
              (kittenStateOfScratch scr).trl_end.toNat).map BitVec.toNat at hl
            rw [htrl_nat] at hl; simp at hl
          trl_lvl_le := fun v hv => by
            change v < (BitVec.ofNat 32 nv').toNat at hv; rw [hnv'_toNat] at hv
            exact hinv.assign.trl_lvl_le v (by rw [hnv_toNat]; omega)
          unass_lvl_zero := fun v hv => by
            change v < (BitVec.ofNat 32 nv').toNat at hv; rw [hnv'_toNat] at hv
            exact hinv.assign.unass_lvl_zero v (by rw [hnv_toNat]; omega)
          trl_lvl_mono := hinv.assign.trl_lvl_mono
          dec_earliest := hinv.assign.dec_earliest
          lvl0_ok := hinv.assign.lvl0_ok }
      exact ⟨hsh_ok, hcl_ok, hwat_ok, hba_ok, hinv.reasons⟩
    refine ⟨⟨hlen'.symm ▸ hlen1, hlen'.symm ▸ hlen2, hinv'⟩, h1, by omega,
      by rw [hks'], hcl512, by rw [hks']; exact honc,
      fun i hi => by rw [hks']; exact haux i hi,
      by rw [hks']; exact hperm, hlt,
      by rw [hks']; exact hante,
      by rw [hks']; exact hna_le,
      fun _ => by rw [hks']; exact ⟨hsync, hlvl0, htrl0, hnc_eq, hwblit⟩,
      fun hc => by cases hc⟩
  set_assumps {nv cls ph scr scr'} h hlen hpres hna hlts := by
    rcases h with ⟨⟨hlen1, hlen2, hinv⟩, h1, hnv128, hnv_eq, hcl512, honc, haux, hperm,
      hlt_cls, hante, _, _, _⟩
    let ks := kittenStateOfScratch scr
    have hks' : kittenStateOfScratch scr' =
        { ks with
          nassump := scr'[256 + 18]?.getD 0#32
          assump := ((scr'.drop 256).drop 1184).take 128 } :=
      kittenState_set_assumps_eq hpres
    have hante0 : (kittenStateOfScratch scr).ante = 0#32 := by
      by_cases hz : (kittenStateOfScratch scr).ante = 0#32
      · exact hz
      · have := hante.mp hz; cases this
    have hnv_toNat : (kittenStateOfScratch scr).nv.toNat = nv := by
      rw [hnv_eq]; exact bv32_ofNat_toNat_le (by omega)
    have hinv' : (kittenStateOfScratch scr').Inv (scr'.length - 8864) := by
      rw [hks', hlen]
      have hsh' : ({ ks with
            nassump := scr'[256 + 18]?.getD 0#32
            assump := ((scr'.drop 256).drop 1184).take 128 } : KittenState).ShapesOk
          (scr.length - 8864) :=
        { hinv.shapes with
          assump_len := by
            rw [List.length_take, List.length_drop, List.length_drop, hlen]
            unfold kMinScratchCap at hlen1; omega }
      have hcl_ok : KittenClausesOk (scr.length - 8864)
          { ks with
            nassump := scr'[256 + 18]?.getD 0#32
            assump := ((scr'.drop 256).drop 1184).take 128 } :=
        { acap_ge := hinv.clauses.acap_ge
          acap_lt := hinv.clauses.acap_lt
          acap_eq := hinv.clauses.acap_eq
          nv_le := hinv.clauses.nv_le
          nc_le := hinv.clauses.nc_le
          orig_nc_le := hinv.clauses.orig_nc_le
          orig_nc_max := hinv.clauses.orig_nc_max
          alen_le := hinv.clauses.alen_le
          nassump_le := by unfold kMaxV; exact Nat.le_trans hna (by decide)
          nunits_le := hinv.clauses.nunits_le
          nres_le := hinv.clauses.nres_le
          nkl_le := hinv.clauses.nkl_le
          nana_le := hinv.clauses.nana_le
          cl_wf := hinv.clauses.cl_wf
          cl_mono := hinv.clauses.cl_mono
          units_ok := hinv.clauses.units_ok
          incons_ok := hinv.clauses.incons_ok
          failing_ok := fun ha _ => absurd hante0 ha
          assump_ok := fun i hi => by
            change i < (scr'[256 + 18]?.getD 0#32).toNat at hi
            change ((((scr'.drop 256).drop 1184).take 128)[i]?.getD 0#32).toNat <
              2 * (kittenStateOfScratch scr).nv.toNat
            rw [ks_getElem_slice _ 1184 128 i (by omega), hnv_toNat]
            exact hlts i hi
          flags_clean := hinv.clauses.flags_clean }
      have hba_ok : KittenBaseAssignOk
          { ks with
            nassump := scr'[256 + 18]?.getD 0#32
            assump := ((scr'.drop 256).drop 1184).take 128 } :=
        { trl_end_le := hinv.assign.trl_end_le
          prop_le := hinv.assign.prop_le
          unass_eq := hinv.assign.unass_eq
          vals_dom := hinv.assign.vals_dom
          vals_neg_iff := hinv.assign.vals_neg_iff
          vals_nz_iff_trl := hinv.assign.vals_nz_iff_trl
          trl_nodup := hinv.assign.trl_nodup
          trl_lt := hinv.assign.trl_lt
          trl_lvl_le := hinv.assign.trl_lvl_le
          unass_lvl_zero := hinv.assign.unass_lvl_zero
          trl_lvl_mono := hinv.assign.trl_lvl_mono
          dec_earliest := hinv.assign.dec_earliest
          lvl0_ok := hinv.assign.lvl0_ok }
      exact ⟨hsh', hcl_ok, hinv.watches, hba_ok, hinv.reasons⟩
    refine ⟨⟨hlen.symm ▸ hlen1, hlen.symm ▸ hlen2, hinv'⟩, h1, hnv128,
      by rw [hks']; exact hnv_eq, hcl512, by rw [hks']; exact honc,
      fun i hi => by rw [hks']; exact haux i hi,
      by rw [hks']; exact hperm, hlt_cls,
      by rw [hks']; exact hante,
      by rw [hks']; exact hna,
      (fun hc => by cases hc), (fun hc => by cases hc)⟩

/-! ## 2. Clause & Assumption Helpers for Kitten Adapters -/

private theorem kittenAssumpClauses_sat_iff (scr : List (BitVec 32))
    (hscr : KittenScratchInv scr) (α : Nat → Bool) :
    (cnfOfClauses (FullDefSweep.kittenAssumpClauses scr)).Sat α ↔
      (unitsCnf (kittenAssumpLitsS scr)).Sat α := by
  have hna_le : (kittenStateOfScratch scr).nassump.toNat ≤ 128 := hscr.2.2.clauses.nassump_le
  have hna_eq : (scr[256 + 18]?.getD 0#32).toNat = (kittenStateOfScratch scr).nassump.toNat := by
    simp [kittenStateOfScratch, KittenState.ofSlab, List.getElem?_drop]
  have hal_len : (kittenStateOfScratch scr).assump.length = 128 := hscr.2.2.shapes.assump_len
  simp only [cnf_sat_cnfOfClauses_iff, sat_unitsCnf_iff, FullDefSweep.kittenAssumpClauses,
    kittenAssumpLitsS, kittenAssumpLits, List.mem_map, List.mem_range]
  constructor
  · rintro h l ⟨x, hx, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hi_na : i < (kittenStateOfScratch scr).nassump.toNat := by
      rw [List.length_take, hal_len] at hi; omega
    have hxi : ((kittenStateOfScratch scr).assump.take
        (kittenStateOfScratch scr).nassump.toNat)[i]'hi = scr[256 + 1184 + i]?.getD 0#32 := by
      rw [List.getElem_take]
      have hget : (kittenStateOfScratch scr).assump[i]? = scr[256 + 1184 + i]? :=
        ks_getElem_slice scr 1184 128 i (by omega)
      rw [← hget, List.getElem?_eq_getElem (by omega), Option.getD_some]
    rw [hxi]
    exact h _ ⟨i, by omega, rfl⟩
  · rintro h c ⟨i, hi, rfl⟩
    have hi_na : i < (kittenStateOfScratch scr).nassump.toNat := by omega
    have hi_tk : i < ((kittenStateOfScratch scr).assump.take
        (kittenStateOfScratch scr).nassump.toNat).length := by
      rw [List.length_take, hal_len]; omega
    have hxi : ((kittenStateOfScratch scr).assump.take
        (kittenStateOfScratch scr).nassump.toNat)[i]'hi_tk = scr[256 + 1184 + i]?.getD 0#32 := by
      rw [List.getElem_take]
      have hget : (kittenStateOfScratch scr).assump[i]? = scr[256 + 1184 + i]? :=
        ks_getElem_slice scr 1184 128 i (by omega)
      rw [← hget, List.getElem?_eq_getElem (by omega), Option.getD_some]
    rw [← hxi]
    exact h _ ⟨_, List.getElem_mem hi_tk, rfl⟩

private theorem kittenCore_perm_equiv {cls : List (Nat × List Nat)} {scr : List (BitVec 32)}
    (hcl : cls.length ≤ 512)
    (honc : (kittenStateOfScratch scr).orig_nc = BitVec.ofNat 32 cls.length)
    (hperm : KittenCnfPermEquiv (kittenOrigClausesS scr) (cls.map Prod.snd)) :
    KittenCnfPermEquiv (kittenCoreClausesS scr)
      ((FullDefSweep.kittenCoreClauses cls scr).map Prod.snd) := by
  let ks := kittenStateOfScratch scr
  have honc_nat : ks.orig_nc.toNat = cls.length := by
    rw [honc]; exact bv32_ofNat_toNat_le (by omega)
  let p : Nat → Bool := fun ci => (scr[256 + 6816 + ci]?.getD 0#32 &&& 0x10000#32) != 0#32
  have hp_eq : ∀ ci < cls.length,
      ((kittenClauseMeta ks ci &&& kmCore) != 0#32) = p ci := by
    intro ci hci
    have hget : ks.clMeta[ci]? = scr[256 + 6816 + ci]? :=
      ks_getElem_slice scr 6816 896 ci (by omega)
    simp only [kittenClauseMeta, kmCore, p, hget]
  have h1 : kittenCoreClausesS scr =
      ((List.range cls.length).filter p).map (kittenClauseLits ks) := by
    unfold kittenCoreClausesS kittenCoreClauses
    rw [honc_nat]
    congr 1
    apply List.filter_congr
    intro ci hci
    exact hp_eq ci (List.mem_range.mp hci)
  have h2 : (FullDefSweep.kittenCoreClauses cls scr).map Prod.snd =
      ((List.range cls.length).filter p).map (fun ci => (cls[ci]?.getD (0, [])).2) := by
    unfold FullDefSweep.kittenCoreClauses
    suffices ∀ L : List Nat, (∀ ci ∈ L, ci < cls.length) →
        (L.filterMap fun ci =>
          if (scr[256 + 6816 + ci]?.getD 0#32 &&& 0x10000#32) ≠ 0#32 then cls[ci]? else none).map
          Prod.snd =
        (L.filter p).map (fun ci => (cls[ci]?.getD (0, [])).2) from
      this (List.range cls.length) (fun _ h => List.mem_range.mp h)
    intro L hL
    induction L with
    | nil => rfl
    | cons ci tl ih =>
      have hci := hL ci List.mem_cons_self
      have htl := ih fun x hx => hL x (List.mem_cons_of_mem _ hx)
      rw [List.filterMap_cons, List.filter_cons, List.getElem?_eq_getElem hci]
      by_cases hcond : (scr[256 + 6816 + ci]?.getD 0#32 &&& 0x10000#32) ≠ 0#32
      · have hp1 : p ci = true := bne_iff_ne.mpr hcond
        rw [ite_eq_left_of_eq_true _ _ (eq_true hcond), hp1]
        simp only [↓reduceIte, List.map_cons, List.getElem?_eq_getElem hci, Option.getD_some, htl]
      · have hp0 : p ci = false := by
          dsimp only [p]; rw [bne_eq_false_iff_eq]; exact Decidable.not_not.mp hcond
        rw [ite_eq_right_of_eq_false _ _ (eq_false hcond), hp0]
        simp only [Bool.false_eq_true, ↓reduceIte, htl]
  rw [h1, h2]
  refine ⟨by simp, fun i hi => ?_⟩
  rw [List.length_map] at hi
  let F := (List.range cls.length).filter p
  have hL : (F.map (kittenClauseLits ks))[i]! = kittenClauseLits ks (F[i]'hi) := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]; rfl
  have hR : (F.map (fun ci => (cls[ci]?.getD (0, [])).2))[i]! =
      (cls[F[i]'hi]?.getD (0, [])).2 := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]; rfl
  rw [hL, hR]
  have hmem := List.mem_filter.mp (List.getElem_mem hi)
  have hci : F[i]'hi < cls.length := List.mem_range.mp hmem.1
  rw [List.getElem?_eq_getElem hci, Option.getD_some]
  exact kittenClauseLits_perm_cls honc hcl hperm hci

private theorem kittenCore_aux_eq {cls : List (Nat × List Nat)} {scr : List (BitVec 32)}
    (hcl : cls.length ≤ 512)
    (honc : (kittenStateOfScratch scr).orig_nc = BitVec.ofNat 32 cls.length)
    (haux : ∀ (i : Nat) (hi : i < cls.length),
      ((kittenStateOfScratch scr).clAux[i]?.getD 0#32).toNat = (cls[i]'hi).1) :
    ((List.range (kittenStateOfScratch scr).orig_nc.toNat).filter fun ci =>
        (kittenClauseMeta (kittenStateOfScratch scr) ci &&& kmCore) != 0#32).map
      (kittenClauseAux (kittenStateOfScratch scr)) =
      (FullDefSweep.kittenCoreClauses cls scr).map Prod.fst := by
  let ks := kittenStateOfScratch scr
  have honc_nat : ks.orig_nc.toNat = cls.length := by
    rw [honc]; exact bv32_ofNat_toNat_le (by omega)
  rw [honc_nat]
  unfold FullDefSweep.kittenCoreClauses
  suffices ∀ L : List Nat, (∀ ci ∈ L, ci < cls.length) →
      (L.filter fun ci => (kittenClauseMeta ks ci &&& kmCore) != 0#32).map (kittenClauseAux ks) =
      (L.filterMap fun ci =>
        if (scr[256 + 6816 + ci]?.getD 0#32 &&& 0x10000#32) ≠ 0#32 then cls[ci]? else none).map
        Prod.fst from
    this (List.range cls.length) (fun _ h => List.mem_range.mp h)
  intro L hL
  induction L with
  | nil => rfl
  | cons ci tl ih =>
    have hci := hL ci List.mem_cons_self
    have htl := ih fun x hx => hL x (List.mem_cons_of_mem _ hx)
    have hmeta : kittenClauseMeta ks ci = scr[256 + 6816 + ci]?.getD 0#32 := by
      unfold kittenClauseMeta
      dsimp only [ks, kittenStateOfScratch, KittenState.ofSlab]
      rw [ks_getElem_slice scr 6816 896 ci (by omega)]
    rw [List.filter_cons, List.filterMap_cons, List.getElem?_eq_getElem hci]
    by_cases hcond : (scr[256 + 6816 + ci]?.getD 0#32 &&& 0x10000#32) ≠ 0#32
    · have hb : ((kittenClauseMeta ks ci &&& kmCore) != 0#32) = true := by
        rw [hmeta]; exact bne_iff_ne.mpr hcond
      rw [hb, ite_eq_left_of_eq_true _ _ (eq_true hcond)]
      simp only [↓reduceIte, List.map_cons, htl]
      congr 1
      exact haux ci hci
    · have hb : ((kittenClauseMeta ks ci &&& kmCore) != 0#32) = false := by
        rw [hmeta, kmCore, bne_eq_false_iff_eq]; exact Decidable.not_not.mp hcond
      rw [hb, ite_eq_right_of_eq_false _ _ (eq_false hcond)]
      simp only [Bool.false_eq_true, ↓reduceIte, htl]

/-! ## 3. Six `FullKitten` -> `FullDefSweep` Entry Adapters -/

theorem fast_kitten_init_adapter {Γ : Env}
    (h : ∀ a m Q X, fullKittenInitSpec a m Q X →
      Γ "full_kitten_init" [i64, i32, i32] [] a m Q X) :
    ∀ a m Q X, FullDefSweep.fullKittenInitSpec fastKInv a m Q X →
      Γ "full_kitten_init" [i64, i32, i32] [] a m Q X := by
  rintro ⟨h_ptr, nv, ta, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcap, h1, h128, hm, hQ⟩
  refine h _ m Q X ⟨c, s, R, rfl, hlen, hm, ?_⟩
  have hcond : ¬ (c.scratch_cap < kMinScratchCap ∨ kMaxV < nv.toNat) := by
    unfold kMinScratchCap kMaxV; omega
  simp only [hcond, ↓reduceIte]
  intro scr' m'
  intro hlen' hpres hscr' hsync hnv hnc honc hlvl _ htrl _ _ _ hante hna _ horig _ hm'
  have hscr_len' : scr'.length = c.scratch_cap := hlen'.scratch_ok.scratch_buf_len
  have hna_get : scr'[256 + 18]? = some 0#32 := by
    have hlt : 256 + 18 < scr'.length := by omega
    have h1 : (scr'.drop 256)[18]?.getD 0#32 = 0#32 := hna
    rw [List.getElem?_drop, List.getElem?_eq_getElem hlt, Option.getD_some] at h1
    rw [List.getElem?_eq_getElem hlt, h1]
  have hkinv : fastKInv nv.toNat [] (decide (ta ≠ 0#32)) .fresh scr' :=
    ⟨hscr', h1, h128, by rw [hnv, BitVec.ofNat_toNat, BitVec.setWidth_eq], Nat.zero_le _, honc,
     (fun _ hi => by cases hi),
     (by change KittenCnfPermEquiv (kittenOrigClausesS scr') []; rw [horig]; exact .refl []),
     (fun _ hc => by cases hc),
     by rw [hante]; exact decide_eq_true_iff.symm,
     by rw [hna]; decide,
     (fun _ => ⟨hsync, hlvl, htrl, by rw [hnc, honc], fun w hw => by rw [hnc] at hw; simp at hw⟩),
     (fun hc => by cases hc)⟩
  exact hQ scr' m' hscr_len' hpres hna_get hkinv hm'

theorem fast_kitten_add_clause_adapter {Γ : Env}
    (h : ∀ a m Q X, fullKittenAddClauseSpec a m Q X →
      Γ "full_kitten_add_clause" [i64, i32, i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, FullDefSweep.fullKittenAddClauseSpec fastKInv a m Q X →
      Γ "full_kitten_add_clause" [i64, i32, i64, i32] [.bool] a m Q X := by
  rintro ⟨h_ptr, eid, lits_ptr, sz, ⟨⟩⟩ m Q X
    ⟨c, s, nv, cls, ta, xs, R, rfl, hlen, hcap, hkinv, hsz1, hsz16, hsz_le, hxs_lt, hm, hQ⟩
  rcases hkinv with ⟨hscr, h1, h128, hnv_eq, hcl512, honc, haux, hperm, hlt_cls,
    hante, hna_le, hfresh, _⟩
  obtain ⟨hsync, hlvl0, htrl0, hnc_eq, hwblit⟩ := hfresh rfl
  have hnv_toNat : (kittenStateOfScratch s.scratch.scratch_buf).nv.toNat = nv := by
    rw [hnv_eq]; exact bv32_ofNat_toNat_le (by omega)
  have honc_toNat : (kittenStateOfScratch s.scratch.scratch_buf).orig_nc.toNat = cls.length := by
    rw [honc]; exact bv32_ofNat_toNat_le (by omega)
  have hnc_toNat : (kittenStateOfScratch s.scratch.scratch_buf).nc.toNat =
      (kittenStateOfScratch s.scratch.scratch_buf).orig_nc.toNat := congrArg BitVec.toNat hnc_eq
  refine h _ m Q X ⟨c, s, s.scratch.scratch_buf, xs, R, rfl, hlen, rfl,
    hscr, hsync, hlvl0, htrl0, hnc_eq, hsz_le, hsz16,
    fun i hi => by rw [hnv_toNat]; exact hxs_lt i hi, hm, ?_⟩
  intro ok scr' m'
  dsimp only
  intro hlen' hpres hscr' hsync' hlvl' htrl' hnv' hnc' hante' hna' _ hfalse htrue hm'
  have hna_get : scr'[256 + 18]? = s.scratch.scratch_buf[256 + 18]? := by
    have hlt1 : 256 + 18 < scr'.length := by omega
    have hlt2 : 256 + 18 < s.scratch.scratch_buf.length := by
      rw [hlen.scratch_ok.scratch_buf_len]; omega
    have h1 : (scr'.drop 256)[18]?.getD 0#32 =
        (s.scratch.scratch_buf.drop 256)[18]?.getD 0#32 := hna'
    rw [List.getElem?_drop, List.getElem?_drop, List.getElem?_eq_getElem hlt1,
      List.getElem?_eq_getElem hlt2, Option.getD_some, Option.getD_some] at h1
    rw [List.getElem?_eq_getElem hlt1, List.getElem?_eq_getElem hlt2, h1]
  refine hQ ok scr' m' hlen' hpres hna_get (fun hok => ?_) (fun hok => ?_) hm'
  · obtain ⟨honc', haux_new, haux_old, hmeta_new, horig', hwblit_old, hwblit_new⟩ := htrue hok
    let newCl : List Nat := (xs.take sz.toNat).map BitVec.toNat
    let cls' := cls ++ [(eid.toNat, newCl)]
    have honc'_toNat : (kittenStateOfScratch scr').orig_nc.toNat = cls.length + 1 := by
      have h32 : (kittenStateOfScratch s.scratch.scratch_buf).orig_nc.toNat + 1 < 2 ^ 32 := by
        omega
      rw [honc', BitVec.toNat_add, show (1#32).toNat = 1 from rfl, Nat.mod_eq_of_lt h32,
        honc_toNat]
    have hcls'_le : cls'.length ≤ 512 := by
      have hmax := hscr'.2.2.clauses.orig_nc_max
      unfold kMaxOrig at hmax
      simp only [cls', List.length_append, List.length_singleton]; omega
    have hperm' : KittenCnfPermEquiv (kittenOrigClauses (kittenStateOfScratch scr'))
        (cls'.map Prod.snd) := by
      change KittenCnfPermEquiv (kittenOrigClausesS scr') (cls'.map Prod.snd)
      rw [horig']
      simp only [cls', List.map_append, List.map_singleton]
      have hperm1 : (kittenOrigClausesS s.scratch.scratch_buf).length = cls.length := by
        simpa [kittenOrigClausesS] using hperm.1
      refine ⟨by simp [hperm1], fun i hi => ?_⟩
      rw [List.length_append, List.length_singleton] at hi
      by_cases hilt : i < (kittenOrigClausesS s.scratch.scratch_buf).length
      · have h1 : (kittenOrigClausesS s.scratch.scratch_buf ++ [newCl])[i]! =
            (kittenOrigClausesS s.scratch.scratch_buf)[i]! := by
          rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
            List.getElem?_append_left hilt]
        have h2 : (cls.map Prod.snd ++ [newCl])[i]! = (cls.map Prod.snd)[i]! := by
          rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
            List.getElem?_append_left (by simp; omega)]
        rw [h1, h2]; exact hperm.2 i hilt
      · have hieq : i = (kittenOrigClausesS s.scratch.scratch_buf).length := by omega
        subst hieq
        have h1 : (kittenOrigClausesS s.scratch.scratch_buf ++ [newCl])[
            (kittenOrigClausesS s.scratch.scratch_buf).length]! = newCl := by
          rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
            Nat.sub_self]; rfl
        have h2 : (cls.map Prod.snd ++ [newCl])[
            (kittenOrigClausesS s.scratch.scratch_buf).length]! = newCl := by
          have hlen_eq : (kittenOrigClausesS s.scratch.scratch_buf).length =
              (cls.map Prod.snd).length := hperm.1
          rw [hlen_eq, List.getElem!_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
            Nat.sub_self]; rfl
        rw [h1, h2]
    have haux' : ∀ (i : Nat) (hi : i < cls'.length),
        ((kittenStateOfScratch scr').clAux[i]?.getD 0#32).toNat = (cls'[i]'hi).1 := by
      intro i hi
      simp only [cls', List.length_append, List.length_singleton] at hi
      by_cases hilt : i < cls.length
      · rw [haux_old i (by omega)]
        have hget : (cls'[i]'(by simp [cls']; omega)) = cls[i]'hilt :=
          List.getElem_append_left hilt
        rw [hget]; exact haux i hilt
      · have hieq : i = cls.length := by omega
        subst hieq
        have hget : (cls'[cls.length]'(by simp [cls'])) = (eid.toNat, newCl) := by
          simp [cls']
        rw [hget, show cls.length = (kittenStateOfScratch s.scratch.scratch_buf).orig_nc.toNat
          from honc_toNat.symm, haux_new]; rfl
    have hlt_cls' : ∀ cl ∈ cls', ∀ l ∈ cl.2, l < 2 * nv := by
      intro cl hcl l hl
      rcases List.mem_append.mp hcl with hmem | hmem
      · exact hlt_cls cl hmem l hl
      · rw [List.mem_singleton] at hmem; subst hmem
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hl
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
        have hk_sz : k < sz.toNat := by rw [List.length_take] at hk; omega
        have hget := hxs_lt k hk_sz
        rw [List.getElem_take]
        rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hget
    have hwblit' : KittenWblitInClause (kittenStateOfScratch scr') := by
      intro w hw hsz2
      have hnc'_nat : (kittenStateOfScratch scr').nc.toNat =
          (kittenStateOfScratch s.scratch.scratch_buf).nc.toNat + 1 := by
        rw [hnc', honc'_toNat, hnc_toNat, honc_toNat]
      by_cases hw_old : w < 2 * (kittenStateOfScratch s.scratch.scratch_buf).nc.toNat
      · have hcid_lt : w / 2 < (kittenStateOfScratch s.scratch.scratch_buf).orig_nc.toNat := by
          omega
        have hlits_eq : kittenClauseLits (kittenStateOfScratch scr') (w / 2) =
            kittenClauseLits (kittenStateOfScratch s.scratch.scratch_buf) (w / 2) := by
          have hidx := congrArg (·[w / 2]?) horig'
          have hlen_o : (kittenOrigClausesS s.scratch.scratch_buf).length =
              (kittenStateOfScratch s.scratch.scratch_buf).orig_nc.toNat := by
            simp [kittenOrigClausesS, kittenOrigClauses]
          rw [List.getElem?_append_left (by omega)] at hidx
          simp only [kittenOrigClausesS, kittenOrigClauses, List.getElem?_map,
            List.getElem?_range (by omega : w / 2 < (kittenStateOfScratch scr').orig_nc.toNat),
            List.getElem?_range hcid_lt] at hidx
          exact Option.some.inj hidx
        have hsz_old :
            2 ≤ kittenClauseSize (kittenStateOfScratch s.scratch.scratch_buf) (w / 2) := by
          have hlen_lits : ∀ (k : KittenState) (cid : Nat),
              cid < k.nc.toNat → k.Inv (s.scratch.scratch_buf.length - 8864) →
              (kittenClauseLits k cid).length = kittenClauseSize k cid := by
            intro k cid hcid hk
            have hwf := hk.clauses.cl_wf cid hcid
            have hsp : kittenClauseSize k cid ≤ kittenClauseSpan k cid := Nat.le_add_right ..
            have hal := hk.clauses.alen_le
            have har := hk.shapes.arena_len
            simp [kittenClauseLits, List.length_take, List.length_drop]; omega
          have hlen_eq : scr'.length = s.scratch.scratch_buf.length := by
            rw [hlen', hlen.scratch_ok.scratch_buf_len]
          have h1 := hlen_lits (kittenStateOfScratch scr') (w / 2) (by omega)
            (hlen_eq ▸ hscr'.2.2)
          have h2 := hlen_lits (kittenStateOfScratch s.scratch.scratch_buf) (w / 2) (by omega)
            hscr.2.2
          rw [hlits_eq] at h1; omega
        rw [hwblit_old w hw_old, hlits_eq]
        exact hwblit w hw_old hsz_old
      · have hcid_eq : w / 2 = (kittenStateOfScratch s.scratch.scratch_buf).orig_nc.toNat := by
          omega
        have hsz_eq : kittenClauseSize (kittenStateOfScratch scr') (w / 2) = sz.toNat := by
          rw [hcid_eq, kittenClauseSize, kittenClauseMeta, hmeta_new]
        have hsz2' : 2 ≤ sz.toNat := by omega
        have hlits_new : kittenClauseLits (kittenStateOfScratch scr') (w / 2) = newCl := by
          have hidx :=
            congrArg (·[(kittenStateOfScratch s.scratch.scratch_buf).orig_nc.toNat]?) horig'
          have hlen_o : (kittenOrigClausesS s.scratch.scratch_buf).length =
              (kittenStateOfScratch s.scratch.scratch_buf).orig_nc.toNat := by
            simp [kittenOrigClausesS, kittenOrigClauses]
          rw [List.getElem?_append_right (by omega), hlen_o, Nat.sub_self] at hidx
          simp only [kittenOrigClausesS, kittenOrigClauses, List.getElem?_map,
            List.getElem?_range (by omega :
              (kittenStateOfScratch s.scratch.scratch_buf).orig_nc.toNat <
                (kittenStateOfScratch scr').orig_nc.toNat)] at hidx
          rw [hcid_eq]; exact Option.some.inj hidx
        obtain ⟨hw0, hw1⟩ := hwblit_new hsz2'
        rw [hlits_new]
        rcases (by omega : w = 2 * (kittenStateOfScratch s.scratch.scratch_buf).nc.toNat ∨
            w = 2 * (kittenStateOfScratch s.scratch.scratch_buf).nc.toNat + 1) with rfl | rfl
        · rw [hw0, List.getElem?_eq_getElem (by omega), Option.getD_some]
          exact List.mem_map_of_mem (by
            have : xs[1]'(by omega) = (xs.take sz.toNat)[1]'(by simp; omega) := by simp
            rw [this]; exact List.getElem_mem _)
        · rw [hw1, List.getElem?_eq_getElem (by omega), Option.getD_some]
          exact List.mem_map_of_mem (by
            have : xs[0]'(by omega) = (xs.take sz.toNat)[0]'(by simp; omega) := by simp
            rw [this]; exact List.getElem_mem _)
    refine ⟨hscr', h1, h128, by rw [hnv', hnv_eq], hcls'_le, ?_, haux', hperm', hlt_cls',
      by rw [hante']; exact hante, by rw [hna']; exact hna_le,
      (fun _ => ⟨hsync', hlvl', htrl', hnc', hwblit'⟩), (fun hc => by cases hc)⟩
    apply BitVec.eq_of_toNat_eq
    rw [honc'_toNat, bv32_ofNat_toNat_le (by simp; omega)]
    simp
  · have heq := hfalse hok
    subst heq
    exact ⟨hscr, h1, h128, hnv_eq, hcl512, honc, haux, hperm, hlt_cls, hante, hna_le,
      (fun _ => ⟨hsync, hlvl0, htrl0, hnc_eq, hwblit⟩), (fun hc => by cases hc)⟩

theorem fast_kitten_solve_adapter {Γ : Env}
    (h : ∀ a m Q X, fullKittenSolveSpec a m Q X →
      Γ "full_kitten_solve" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, FullDefSweep.fullKittenSolveSpec fastKInv a m Q X →
      Γ "full_kitten_solve" [i64, i64] [i64] a m Q X := by
  rintro ⟨h_ptr, tlim, ⟨⟩⟩ m Q X ⟨c, s, nv, cls, ta, ph, R, rfl, hlen, hcap, hkinv, hm, hQ⟩
  rcases hkinv with ⟨hscr, h1, h128, hnv_eq, hcl512, honc, haux, hperm, hlt_cls,
    hante, hna_le, _, _⟩
  have honc_toNat : (kittenStateOfScratch s.scratch.scratch_buf).orig_nc.toNat = cls.length := by
    rw [honc]; exact bv32_ofNat_toNat_le (by omega)
  refine h _ m Q X ⟨c, s, R, rfl, hlen, hscr, hm, ?_⟩
  intro r fuel' scr' m'
  dsimp only
  intro hlen' hfu' hpres hscr' hnv' honc' hante' hna' hass' hperm' haux'
    hcore_pres hdom h20 hm'
  have hscr_len' : scr'.length = c.scratch_cap := hlen'.scratch_ok.scratch_buf_len
  have hna_get : scr'[256 + 18]? = s.scratch.scratch_buf[256 + 18]? := by
    have hlt1 : 256 + 18 < scr'.length := by omega
    have hlt2 : 256 + 18 < s.scratch.scratch_buf.length := by
      rw [hlen.scratch_ok.scratch_buf_len]; omega
    have h1 : (scr'.drop 256)[18]?.getD 0#32 =
        (s.scratch.scratch_buf.drop 256)[18]?.getD 0#32 := hna'
    rw [List.getElem?_drop, List.getElem?_drop, List.getElem?_eq_getElem hlt1,
      List.getElem?_eq_getElem hlt2, Option.getD_some, Option.getD_some] at h1
    rw [List.getElem?_eq_getElem hlt1, List.getElem?_eq_getElem hlt2, h1]
  have hperm_cls : KittenCnfPermEquiv (kittenOrigClauses (kittenStateOfScratch scr'))
      (cls.map Prod.snd) :=
    hperm'.trans hperm
  have hkinv' : fastKInv nv cls ta
      (if decide (r = 20#64) && ta &&
        decide ((s.scratch.scratch_buf[256 + 18]?.getD 0#32).toNat = 0)
        then .unsatReady else .solved) scr' := by
    refine ⟨hscr', h1, h128, by rw [hnv', hnv_eq], hcl512, by rw [honc', honc],
      (fun i hi => by rw [haux' i (by omega)]; exact haux i hi),
      hperm_cls, hlt_cls, by rw [hante']; exact hante, by rw [hna']; exact hna_le,
      (fun hfr => by split at hfr <;> cases hfr),
      (fun hur => ?_)⟩
    split at hur
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      obtain ⟨⟨hr20, _⟩, hna0⟩ := hcond
      refine ⟨(h20 hr20).1, ?_⟩
      apply BitVec.eq_of_toNat_eq
      rw [hna']
      simpa [kittenStateOfScratch, KittenState.ofSlab, List.getElem?_drop] using hna0
    · cases hur
  refine hQ r fuel' scr' m' hscr_len' hfu' hpres hna_get hkinv' hdom (fun hr20 => ?_)
    (fun hrne i hi => ?_) hm'
  · have huns := (h20 hr20).2
    rw [CNF.unsat_iff_not_sat] at huns ⊢
    intro α hα
    rw [cnfOfClauses_append] at hα
    apply huns α
    rw [CNF.sat_append]
    exact ⟨(hperm_cls.sat_iff α).mpr hα.1,
      by rw [hass']; exact (kittenAssumpClauses_sat_iff _ hscr α).mp hα.2⟩
  · have hc := hcore_pres hrne i (by omega)
    have hg1 : (kittenStateOfScratch scr').clMeta[i]? = scr'[256 + 6816 + i]? :=
      ks_getElem_slice scr' 6816 896 i (by omega)
    have hg2 : (kittenStateOfScratch s.scratch.scratch_buf).clMeta[i]? =
        s.scratch.scratch_buf[256 + 6816 + i]? :=
      ks_getElem_slice s.scratch.scratch_buf 6816 896 i (by omega)
    rwa [hg1, hg2] at hc

theorem fast_kitten_core_adapter {Γ : Env}
    (h : ∀ a m Q X, fullKittenCoreSpec a m Q X →
      Γ "full_kitten_core" [i64] [i32] a m Q X) :
    ∀ a m Q X, FullDefSweep.fullKittenCoreSpec fastKInv a m Q X →
      Γ "full_kitten_core" [i64] [i32] a m Q X := by
  rintro ⟨h_ptr, ⟨⟩⟩ m Q X ⟨c, s, nv, cls, R, rfl, hlen, hcap, hkinv, hm, hQ⟩
  rcases hkinv with ⟨hscr, h1, h128, hnv_eq, hcl512, honc, haux, hperm, hlt_cls,
    hante, hna_le, _, hur⟩
  obtain ⟨hinc, hna0⟩ := hur rfl
  have honc_toNat : (kittenStateOfScratch s.scratch.scratch_buf).orig_nc.toNat = cls.length := by
    rw [honc]; exact bv32_ofNat_toNat_le (by omega)
  refine h _ m Q X ⟨c, s, R, rfl, hlen, hscr, hante.mpr rfl, hinc, hm, ?_⟩
  intro csz scr' m'
  dsimp only
  intro hlen' hpres hscr' _ hnv' honc' hante' hna' hinc' hfail' horig' _ haux'
    _ hcore_uns hm'
  have hscr_len' : scr'.length = c.scratch_cap := hlen'.scratch_ok.scratch_buf_len
  have hna_get : scr'[256 + 18]? = s.scratch.scratch_buf[256 + 18]? := by
    have hlt1 : 256 + 18 < scr'.length := by omega
    have hlt2 : 256 + 18 < s.scratch.scratch_buf.length := by
      rw [hlen.scratch_ok.scratch_buf_len]; omega
    have h1 : (scr'.drop 256)[18]?.getD 0#32 =
        (s.scratch.scratch_buf.drop 256)[18]?.getD 0#32 := hna'
    rw [List.getElem?_drop, List.getElem?_drop, List.getElem?_eq_getElem hlt1,
      List.getElem?_eq_getElem hlt2, Option.getD_some, Option.getD_some] at h1
    rw [List.getElem?_eq_getElem hlt1, List.getElem?_eq_getElem hlt2, h1]
  have hperm' : KittenCnfPermEquiv (kittenOrigClausesS scr') (cls.map Prod.snd) := by
    rw [horig']; exact hperm
  have hkinv' : fastKInv nv cls true .unsatReady scr' :=
    ⟨hscr', h1, h128, by rw [hnv', hnv_eq], hcl512, by rw [honc', honc],
     (fun i hi => by rw [haux' i (by omega)]; exact haux i hi),
     hperm', hlt_cls, by rw [hante']; exact hante, by rw [hna']; exact hna_le,
     (fun hc => by cases hc),
     (fun _ => ⟨by rw [hinc', hfail']; exact hinc, by rw [hna', hna0]⟩)⟩
  have hcore_perm := kittenCore_perm_equiv hcl512 (by rw [honc', honc]) hperm'
  have hcore_uns' :
      (cnfOfClauses ((FullDefSweep.kittenCoreClauses cls scr').map Prod.snd)).Unsat := by
    rw [CNF.unsat_iff_not_sat] at hcore_uns ⊢
    intro α hα
    apply hcore_uns α
    rw [CNF.sat_append]
    refine ⟨(hcore_perm.sat_iff α).mpr hα, ?_⟩
    rw [sat_unitsCnf_iff]; intro l hl
    have : kittenAssumpLitsS scr' = [] := by
      unfold kittenAssumpLitsS kittenAssumpLits
      change ((kittenStateOfScratch scr').assump.take
        (kittenStateOfScratch scr').nassump.toNat).map BitVec.toNat = []
      rw [hna', hna0]; rfl
    rw [this] at hl; cases hl
  exact hQ csz scr' m' hscr_len' hpres hna_get hkinv' hcore_uns' hm'

theorem fast_kitten_shrink_adapter {Γ : Env}
    (h : ∀ a m Q X, fullKittenShrinkSpec a m Q X →
      Γ "full_kitten_shrink" [i64] [] a m Q X) :
    ∀ a m Q X, FullDefSweep.fullKittenShrinkSpec fastKInv a m Q X →
      Γ "full_kitten_shrink" [i64] [] a m Q X := by
  rintro ⟨h_ptr, ⟨⟩⟩ m Q X ⟨c, s, nv, cls, ta, ph, R, rfl, hlen, hcap, hkinv, hm, hQ⟩
  rcases hkinv with ⟨hscr, h1, h128, hnv_eq, hcl512, honc, haux, hperm, hlt_cls,
    hante, hna_le, _, _⟩
  refine h _ m Q X ⟨c, s, R, rfl, hlen, hscr, hm, ?_⟩
  intro scr' m'
  dsimp only
  intro hlen' hpres hscr' hsync' hnv' hlvl' htrl' hnc' hante' hna' _ horig' _ _
    haux_map hmeta_clr hwblit' hm'
  let cls' := FullDefSweep.kittenCoreClauses cls s.scratch.scratch_buf
  have hscr_len' : scr'.length = c.scratch_cap := hlen'.scratch_ok.scratch_buf_len
  have hna_get : scr'[256 + 18]? = s.scratch.scratch_buf[256 + 18]? := by
    have hlt1 : 256 + 18 < scr'.length := by omega
    have hlt2 : 256 + 18 < s.scratch.scratch_buf.length := by
      rw [hlen.scratch_ok.scratch_buf_len]; omega
    have h1 : (scr'.drop 256)[18]?.getD 0#32 =
        (s.scratch.scratch_buf.drop 256)[18]?.getD 0#32 := hna'
    rw [List.getElem?_drop, List.getElem?_drop, List.getElem?_eq_getElem hlt1,
      List.getElem?_eq_getElem hlt2, Option.getD_some, Option.getD_some] at h1
    rw [List.getElem?_eq_getElem hlt1, List.getElem?_eq_getElem hlt2, h1]
  have hcore_perm := kittenCore_perm_equiv hcl512 honc hperm
  have hperm' : KittenCnfPermEquiv (kittenOrigClausesS scr') (cls'.map Prod.snd) := by
    rw [horig']; exact hcore_perm
  have honc'_nat : (kittenStateOfScratch scr').orig_nc.toNat = cls'.length := by
    have h1 := hperm'.1
    simp only [kittenOrigClausesS, kittenOrigClauses, List.length_map, List.length_range] at h1
    exact h1
  have hcls'_le : cls'.length ≤ 512 :=
    Nat.le_trans (FullDefSweep.kittenCoreClauses_length_le cls _) hcl512
  have honc' : (kittenStateOfScratch scr').orig_nc = BitVec.ofNat 32 cls'.length := by
    apply BitVec.eq_of_toNat_eq
    rw [honc'_nat, bv32_ofNat_toNat_le (by omega)]
  have haux' : ∀ (i : Nat) (hi : i < cls'.length),
      ((kittenStateOfScratch scr').clAux[i]?.getD 0#32).toNat = (cls'[i]'hi).1 := by
    intro i hi
    have hmap : (List.range (kittenStateOfScratch scr').orig_nc.toNat).map
        (kittenClauseAux (kittenStateOfScratch scr')) = cls'.map Prod.fst :=
      haux_map.trans (kittenCore_aux_eq hcl512 honc haux)
    have hidx := congrArg (·[i]?) hmap
    simp only [List.getElem?_map,
      List.getElem?_range (by omega : i < (kittenStateOfScratch scr').orig_nc.toNat),
      List.getElem?_eq_getElem hi] at hidx
    exact Option.some.inj hidx
  have hkinv' : fastKInv nv cls' ta .fresh scr' :=
    ⟨hscr', h1, h128, by rw [hnv', hnv_eq], hcls'_le, honc', haux', hperm',
     (fun cl hcl => hlt_cls cl (FullDefSweep.kittenCoreClauses_mem hcl)),
     by rw [hante']; exact hante, by rw [hna']; exact hna_le,
     (fun _ => ⟨hsync', hlvl', htrl', hnc', hwblit'⟩),
     (fun hc => by cases hc)⟩
  refine hQ scr' m' hscr_len' hpres hna_get hkinv' (fun i hi => ?_) hm'
  change i < cls'.length at hi
  have hc := hmeta_clr i (by omega)
  have hg : (kittenStateOfScratch scr').clMeta[i]? = scr'[256 + 6816 + i]? :=
    ks_getElem_slice scr' 6816 896 i (by omega)
  rw [kittenClauseMeta, kmCore, hg] at hc
  exact hc

theorem fast_kitten_flip_adapter {Γ : Env}
    (h : ∀ a m Q X, fullKittenFlipSpec a m Q X →
      Γ "full_kitten_flip" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, FullDefSweep.fullKittenFlipSpec fastKInv a m Q X →
      Γ "full_kitten_flip" [i64, i32] [.bool] a m Q X := by
  rintro ⟨h_ptr, lit, ⟨⟩⟩ m Q X ⟨c, s, nv, cls, ta, ph, R, rfl, hlen, hcap, hkinv, hlit, hm, hQ⟩
  rcases hkinv with ⟨hscr, h1, h128, hnv_eq, hcl512, honc, haux, hperm, hlt_cls,
    hante, hna_le, _, _⟩
  have hnv_toNat : (kittenStateOfScratch s.scratch.scratch_buf).nv.toNat = nv := by
    rw [hnv_eq]; exact bv32_ofNat_toNat_le (by omega)
  have honc_toNat : (kittenStateOfScratch s.scratch.scratch_buf).orig_nc.toNat = cls.length := by
    rw [honc]; exact bv32_ofNat_toNat_le (by omega)
  refine h _ m Q X ⟨c, s, R, rfl, hlen, hscr, by rw [hnv_toNat]; exact hlit, hm, ?_⟩
  intro ok scr' m'
  dsimp only
  intro hlen' hpres hscr' hnv' honc' hante' hna' _ hperm' haux' hm'
  have hscr_len' : scr'.length = c.scratch_cap := hlen'.scratch_ok.scratch_buf_len
  have hna_get : scr'[256 + 18]? = s.scratch.scratch_buf[256 + 18]? := by
    have hlt1 : 256 + 18 < scr'.length := by omega
    have hlt2 : 256 + 18 < s.scratch.scratch_buf.length := by
      rw [hlen.scratch_ok.scratch_buf_len]; omega
    have h1 : (scr'.drop 256)[18]?.getD 0#32 =
        (s.scratch.scratch_buf.drop 256)[18]?.getD 0#32 := hna'
    rw [List.getElem?_drop, List.getElem?_drop, List.getElem?_eq_getElem hlt1,
      List.getElem?_eq_getElem hlt2, Option.getD_some, Option.getD_some] at h1
    rw [List.getElem?_eq_getElem hlt1, List.getElem?_eq_getElem hlt2, h1]
  have hkinv' : fastKInv nv cls ta .solved scr' :=
    ⟨hscr', h1, h128, by rw [hnv', hnv_eq], hcl512, by rw [honc', honc],
     (fun i hi => by rw [haux' i (by omega)]; exact haux i hi),
     hperm'.trans hperm, hlt_cls, by rw [hante']; exact hante, by rw [hna']; exact hna_le,
     (fun hc => by cases hc), (fun hc => by cases hc)⟩
  exact hQ ok scr' m' hscr_len' hpres hna_get hkinv' hm'

/-! ## 4. Non-Kitten `FullDefSweep` & `FullFastBveBudgets` Cross-Slice Adapters -/

private theorem gateAt_of_full {F_cur : List (List Nat)} {cur_vars : Nat} {scr : List (BitVec 32)}
    {g_len g : Nat} (hg : FullCongGateAt F_cur cur_vars scr g_len g) :
    FullCongSpecs.GateAt F_cur cur_vars scr g_len g := by
  obtain ⟨lhs, mword, h0, h1, hlhs, hbd, hac, ha8, hrhs, hsem⟩ := hg
  exact ⟨lhs, mword, h0, h1, hlhs, hbd, hac, ha8, hrhs, hsem⟩

private theorem gateSeqOk_of_full {F_cur : List (List Nat)} {cur_vars : Nat}
    {scr : List (BitVec 32)} {g_len g : Nat}
    (hs : FullCongGateSeqOk F_cur cur_vars scr g_len g) :
    FullCongSpecs.GateSeqOk F_cur cur_vars scr g_len g := by
  induction hs with
  | done => exact .done
  | step hg _ ih => exact .step (gateAt_of_full hg) ih

theorem fast_cong_try_xor_ite_adapter {Γ : Env}
    (h : ∀ a m Q X, fullCongTryXorIteSpec a m Q X →
      Γ "full_cong_try_xor_ite" [i64, i32, i32, i32, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, FullCongSpecs.fullCongTryXorIteSpec a m Q X →
      Γ "full_cong_try_xor_ite" [i64, i32, i32, i32, i64, i64] [i64] a m Q X := by
  rintro ⟨h', a, b, cl, gl, gc', ⟨⟩⟩ m' Q' X'
    ⟨c', F0', Fc', s', R', rfl, hl', hw', hnd', hcl0', ha, hb, hcl, hab, hac, hbc, hent, h5,
      hcp, hg', hm', hQ'⟩
  exact h _ m' Q' X' ⟨c', F0', Fc', s', R', rfl, hl', hw', hnd', hcl0', ha, hb, hcl,
    hab, hac, hbc, hent, h5, hcp, FullDefSweep.gateSeqOk_to_full hg', hm',
    fun ret scr' m'' hl'' hlo hhi hp' hg'' hm'' =>
      hQ' ret scr' m'' hl'' hlo hhi hp' (gateSeqOk_of_full hg'') hm''⟩

theorem fast_cong_hash_step_adapter {Γ : Env}
    (h : ∀ a m Q X, fullCongHashStepSpec a m Q X →
      Γ "full_cong_hash_step" [i64, i64, i64, i64] [.bool] a m Q X) :
    ∀ a m Q X, FullCongSpecs.fullCongHashStepSpec a m Q X →
      Γ "full_cong_hash_step" [i64, i64, i64, i64] [.bool] a m Q X := by
  rintro ⟨h', gl, ho, hs, ⟨⟩⟩ m' Q' X'
    ⟨c', F0', Fc', s', R', rfl, hl', hw', hlm', hnd', hext', hcl0', hdm', hrep', hsz', hle',
      hcap', hg', hm', hQ'⟩
  exact h _ m' Q' X' ⟨c', F0', Fc', s', R', rfl, hl', hw', hlm', hnd', hext', hcl0', hdm',
    hrep', hsz', hle', hcap', FullDefSweep.gateSeqOk_to_full hg', hm', hQ'⟩

theorem fast_sweep_add_unit_adapter {Γ : Env}
    (h : ∀ a m Q X, fullAddUnitSpec a m Q X → Γ "full_add_unit" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, FullSweepVarSpecs.fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X := by
  rintro ⟨h', lit, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hent, hm, hQ⟩
  refine h _ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hent, hm,
    fun ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
      ph' ta' ba' pt' pb' hp' ps' hl' qsi' qss' m' hlen' hw' hcl0 hlt hfa hm' =>
      hQ ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
        { s.scratch with
          phases := ph', target_assigned := ta', best_assigned := ba',
          phases_target := pt', phases_best := pb', heap := hp', pos := ps',
          heap_len := hl', q_search_idx := qsi', q_search_stamp := qss' }
        m' hlen' hw' ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hcl0 hlt hfa hm'⟩

/-- Bridges `FullDefSweep.fullBveGatesDefSpec` (strictly stronger) to
`FullFastBveBudgets.fullBveGatesDefFastSpec` for `fast_bve_var_def_wp`. -/
theorem fast_bve_gates_def_adapter {Γ : Env}
    (h : ∀ a m Q X, FullDefSweep.fullBveGatesDefSpec a m Q X →
      Γ "full_bve_gates" [i64, i32, i32, i32] [] a m Q X) :
    ∀ a m Q X, FullFastBveBudgets.fullBveGatesDefFastSpec a m Q X →
      Γ "full_bve_gates" [i64, i32, i32, i32] [] a m Q X := by
  rintro ⟨h', v, np, nn, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hdw, h132, htmk, hv, hnp, hnn,
    hpos, hneg, hm, hQ⟩
  exact h _ m Q X ⟨c, F0, F_cur, s, R, rfl, hdw, h132, htmk, hv, hnp, hnn, hpos, hneg, hm,
    fun s' m' hdw' htmk' hcv' _ har' halen' hfu' hpres hgate hm' =>
      hQ s' m' hdw' htmk' hcv' har' halen' hfu'
        (fun i hi => hpres i (by omega) (Or.inl hi)) hgate hm'⟩

end LeanQbe.T.Examples.Kissat.FullFast
