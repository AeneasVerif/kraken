module

public import LeanQbe.T.Examples.Kissat.FullKittenLemmas2

/-!
# Kissat `D-Full` Scratch `kitten` Solve Loop Proofs (`Part 6`, Pure Helpers & `[15/15]`)

Pure semantic invariants, trail-assignment preservation, and `[15]` (`full_kitten_solve_wp`)
proof support for `FullKitten`:
- `KittenLvlNonempty`, `KittenFreeDecLate`, `SolveFrame`, `SolveLoopInv`.
- `lvl_le_trl_end`, `trl_end_lt_nv_of_unassigned` (pigeonhole on trail vars).
- `kittenAssignStep_preserves_inv`, `inv_set_incons_lvl0`, `decide_step_preserves`,
  `allDecisionsInAssumps_of_late`.
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

/-! ## 1. Solve Loop Invariants & Small Bitvector / List Helpers -/

/-- Every decision level `1 .. ks.lvl` is inhabited by at least one entry on `trl`. -/
def KittenLvlNonempty (ks : KittenState) : Prop :=
  ∀ L, 0 < L → L ≤ ks.lvl.toNat →
    ∃ i < ks.trl_end.toNat,
      (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = L

/-- Any non-assumption decision on `trl` sits strictly after every active assumption literal. -/
def KittenFreeDecLate (ks : KittenState) : Prop :=
  ∀ p < ks.trl_end.toNat,
    ks.rsn[(ks.trl[p]?.getD 0#32).toNat / 2]?.getD 0#32 = 0xFFFFFFFF#32 →
    (ks.trl[p]?.getD 0#32).toNat ∉ kittenAssumpLits ks →
    ∀ a ∈ kittenAssumpLits ks, ∃ q < p, (ks.trl[q]?.getD 0#32).toNat = a

/-- Frame invariants preserved across `full_kitten_solve` relative to entry state `ks0`. -/
structure SolveFrame (ks0 ks : KittenState) : Prop where
  nv : ks.nv = ks0.nv
  orig_nc : ks.orig_nc = ks0.orig_nc
  ante : ks.ante = ks0.ante
  nassump : ks.nassump = ks0.nassump
  assump : ks.assump = ks0.assump
  perm : KittenCnfPermEquiv (kittenOrigClauses ks) (kittenOrigClauses ks0)
  clAux : ∀ ci < ks0.orig_nc.toNat, ks.clAux[ci]? = ks0.clAux[ci]?
  core : ∀ ci < ks0.orig_nc.toNat,
    (ks.clMeta[ci]?.getD 0#32 &&& kmCore) = (ks0.clMeta[ci]?.getD 0#32 &&& kmCore)

theorem SolveFrame.refl (ks : KittenState) : SolveFrame ks ks :=
  ⟨rfl, rfl, rfl, rfl, rfl, KittenCnfPermEquiv.refl _, fun _ _ => rfl, fun _ _ => rfl⟩

theorem SolveFrame.trans {ks0 ks1 ks2 : KittenState}
    (h1 : SolveFrame ks0 ks1) (h2 : SolveFrame ks1 ks2) : SolveFrame ks0 ks2 :=
  ⟨h2.nv.trans h1.nv, h2.orig_nc.trans h1.orig_nc, h2.ante.trans h1.ante,
   h2.nassump.trans h1.nassump, h2.assump.trans h1.assump, h2.perm.trans h1.perm,
   fun ci hci => (h2.clAux ci (h1.orig_nc ▸ hci)).trans (h1.clAux ci hci),
   fun ci hci => (h2.core ci (h1.orig_nc ▸ hci)).trans (h1.core ci hci)⟩

theorem SolveFrame.assumpLits {ks0 ks : KittenState} (h : SolveFrame ks0 ks) :
    kittenAssumpLits ks = kittenAssumpLits ks0 := by
  unfold kittenAssumpLits; rw [h.nassump, h.assump]

/-- Combined CDCL loop invariant for `full_kitten_solve`. -/
structure SolveLoopInv (acap : Nat) (ks0 ks : KittenState) (confl : BitVec 32) : Prop where
  inv : ks.Inv acap
  sync : KittenTrailSynced ks
  incons : ks.incons = 0xFFFFFFFF#32
  failing : ks.failing = 0xFFFFFFFF#32
  frame : SolveFrame ks0 ks
  lvlne : KittenLvlNonempty ks
  late : KittenFreeDecLate ks
  confl_ne : confl ≠ 0xFFFFFFFE#32
  confl_ok : confl ≠ 0xFFFFFFFF#32 →
    confl.toNat < ks.nc.toNat ∧
    ∀ l ∈ kittenClauseLits ks confl.toNat, ks.vals[l]? = some 2#32

private theorem nodup_length_le_of_mem {α : Type} [DecidableEq α] :
    ∀ (xs ys : List α), xs.Nodup → (∀ x ∈ xs, x ∈ ys) → xs.length ≤ ys.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, ys, hnd, hmem => by
    rcases List.nodup_cons.mp hnd with ⟨hx_not, hnd_xs⟩
    have hx_ys : x ∈ ys := hmem x (by simp)
    have hsub : ∀ z ∈ xs, z ∈ ys.erase x := fun z hz =>
      (List.mem_erase_of_ne (fun hzx => hx_not (by rw [← hzx]; exact hz))).mpr
        (hmem z (by simp [hz]))
    have hle := nodup_length_le_of_mem xs (ys.erase x) hnd_xs hsub
    have hlen : (ys.erase x).length + 1 = ys.length := by
      rw [List.length_erase_of_mem hx_ys]
      have hpos : 0 < ys.length := List.length_pos_iff_exists_mem.mpr ⟨x, hx_ys⟩
      omega
    simp only [List.length_cons]
    omega

/-- Every inhabited level `1 .. ks.lvl` pushes `ks.lvl.toNat ≤ ks.trl_end.toNat`. -/
theorem lvl_le_trl_end {acap : Nat} {ks : KittenState}
    (hinv : ks.Inv acap) (hne : KittenLvlNonempty ks) :
    ks.lvl.toNat ≤ ks.trl_end.toNat := by
  have hstep : ∀ L, L ≤ ks.lvl.toNat → 0 < L →
      ∃ i < ks.trl_end.toNat, L - 1 ≤ i ∧
        (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = L := by
    intro L
    induction L with
    | zero => intro _ hz; omega
    | succ L ih =>
      intro hle _
      obtain ⟨i, hi, hiv⟩ := hne (L + 1) (Nat.succ_pos L) hle
      by_cases hL0 : L = 0
      · subst hL0; exact ⟨i, hi, Nat.zero_le _, hiv⟩
      · obtain ⟨j, hj, hj_le, hjv⟩ := ih (by omega) (Nat.pos_of_ne_zero hL0)
        refine ⟨i, hi, ?_, hiv⟩
        by_cases hlt : L ≤ i
        · omega
        · exfalso
          have hij : i ≤ j := by omega
          have hm := hinv.assign.trl_lvl_mono i j hij hj
          rw [hiv, hjv] at hm
          omega
  by_cases hl0 : ks.lvl.toNat = 0
  · rw [hl0]; exact Nat.zero_le _
  · obtain ⟨i, hi, hle, _⟩ := hstep ks.lvl.toNat (Nat.le_refl _) (Nat.pos_of_ne_zero hl0)
    omega

/-- Having at least one unassigned literal implies `ks.trl_end.toNat < ks.nv.toNat`. -/
theorem trl_end_lt_nv_of_unassigned {acap : Nat} {ks : KittenState}
    (hinv : ks.Inv acap) {l : Nat} (hl : l < 2 * ks.nv.toNat)
    (hun : ks.vals[l]?.getD 0#32 = 0#32) :
    ks.trl_end.toNat < ks.nv.toNat := by
  have hnv := hinv.clauses.nv_le
  have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
    rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; unfold kMaxV at hnv; omega
  let vs : List Nat := (ks.trl.take ks.trl_end.toNat).map (fun b => b.toNat / 2)
  have hvs_len : vs.length = ks.trl_end.toNat := by
    simp [vs, List.length_take, htrl_len]
  have hvs_nd : vs.Nodup := by
    simpa [vs, kittenTrailLits, List.map_map, Function.comp_def] using hinv.assign.trl_nodup
  have hnot : l / 2 ∉ vs := by
    intro hmem
    simp only [vs, List.mem_map, List.mem_take_iff_getElem] at hmem
    obtain ⟨b, ⟨i, hi, hget⟩, hbeq⟩ := hmem
    have hi_te : i < ks.trl_end.toNat := by omega
    have hget' : (ks.trl[i]?.getD 0#32).toNat / 2 = l / 2 := by
      rw [List.getElem?_eq_getElem (by omega : i < ks.trl.length), Option.getD_some, hget]
      exact hbeq
    have hnz := (hinv.assign.vals_nz_iff_trl l hl).mpr ⟨i, hi_te, hget'⟩
    exact hnz hun
  have hmem_range : ∀ v ∈ (l / 2 :: vs), v ∈ List.range ks.nv.toNat := by
    intro v hv
    rw [List.mem_range]
    rcases List.mem_cons.mp hv with rfl | hv_vs
    · omega
    · simp only [vs, List.mem_map] at hv_vs
      obtain ⟨b, hb, rfl⟩ := hv_vs
      have hbl := hinv.assign.trl_lt b.toNat (List.mem_map.mpr ⟨b, hb, rfl⟩)
      omega
  have hle := nodup_length_le_of_mem (l / 2 :: vs) (List.range ks.nv.toNat)
    (List.nodup_cons.mpr ⟨hnot, hvs_nd⟩) hmem_range
  simp only [List.length_cons, List.length_range, hvs_len] at hle
  omega

private theorem nat_xor1_xor1 (l : Nat) : (l ^^^ 1) ^^^ 1 = l := by
  rcases nat_xor1_cases l with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
    rcases nat_xor1_cases (l ^^^ 1) with ⟨hc, hd⟩ | ⟨hc, hd⟩ <;> omega

/-- If `vals[l] = 0` under `KittenBaseAssignOk`, then `vals[l ^^^ 1] = 0` too. -/
theorem vals_xor1_eq_zero_of_zero {acap : Nat} {ks : KittenState}
    (hinv : ks.Inv acap) {l : Nat} (hl : l < 2 * ks.nv.toNat)
    (hz : ks.vals[l]?.getD 0#32 = 0#32) :
    ks.vals[l ^^^ 1]?.getD 0#32 = 0#32 := by
  have hnl : (l ^^^ 1) < 2 * ks.nv.toNat := by
    rcases nat_xor1_cases l with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega
  rcases hinv.assign.vals_dom (l ^^^ 1) hnl with h0 | h1 | h2
  · exact h0
  · exfalso
    have hneg := (hinv.assign.vals_neg_iff (l ^^^ 1) hnl).mp h1
    rw [nat_xor1_xor1] at hneg
    rw [hz] at hneg; cases hneg
  · exfalso
    have hneg := (hinv.assign.vals_neg_iff l hl).mpr h2
    rw [hz] at hneg; cases hneg

/-- Both `vals[l]?` and `vals[l ^^^ 1]?` are `some 0#32` when `vals[l]? = some 0#32`. -/
theorem vals_pair_some_zero {acap : Nat} {ks : KittenState}
    (hinv : ks.Inv acap) {l : Nat} (hl : l < 2 * ks.nv.toNat)
    (hz : ks.vals[l]? = some 0#32) :
    ks.vals[l ^^^ 1]? = some 0#32 := by
  have hnv := hinv.clauses.nv_le
  have hnl : (l ^^^ 1) < 2 * ks.nv.toNat := by
    rcases nat_xor1_cases l with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega
  have hlen : (l ^^^ 1) < ks.vals.length := by
    rw [hinv.shapes.vals_len]; unfold kMaxV at hnv; omega
  have h0 := vals_xor1_eq_zero_of_zero hinv hl (by simp [hz])
  rw [List.getElem?_eq_getElem hlen, Option.getD_some] at h0
  rw [List.getElem?_eq_getElem hlen, h0]

/-- If `vals[l]?.getD 0#32 = 0#32`, then `vals[l]? = some 0#32`. -/
theorem vals_some_zero_of_getD {acap : Nat} {ks : KittenState}
    (hinv : ks.Inv acap) {l : Nat} (hl : l < 2 * ks.nv.toNat)
    (hz : ks.vals[l]?.getD 0#32 = 0#32) :
    ks.vals[l]? = some 0#32 := by
  have hnv := hinv.clauses.nv_le
  have hlen : l < ks.vals.length := by rw [hinv.shapes.vals_len]; unfold kMaxV at hnv; omega
  rw [List.getElem?_eq_getElem hlen, Option.getD_some] at hz
  rw [List.getElem?_eq_getElem hlen, hz]

/-- `kittenOrigClauses` is unchanged by `kittenAssignStep`. -/
theorem kittenOrigClauses_assignStep (ks : KittenState) (lit rsn : BitVec 32) :
    kittenOrigClauses (kittenAssignStep ks lit rsn) = kittenOrigClauses ks := rfl

/-- `kittenAssumpLits` is unchanged by `kittenAssignStep`. -/
theorem kittenAssumpLits_assignStep (ks : KittenState) (lit rsn : BitVec 32) :
    kittenAssumpLits (kittenAssignStep ks lit rsn) = kittenAssumpLits ks := rfl

/-- Full invariant + trail-sync preservation for `kittenAssignStep`. -/
theorem kittenAssignStep_preserves_inv {acap : Nat} {ks : KittenState}
    (hinv : ks.Inv acap) (hsync : KittenTrailSynced ks)
    (hinc : ks.incons = 0xFFFFFFFF#32)
    {lit rsn : BitVec 32} (hlit : lit.toNat < 2 * ks.nv.toNat)
    (hun : ks.vals[lit.toNat]? = some 0#32)
    (hlvl0 : ks.lvl = 0#32 →
      rsn ≠ 0xFFFFFFFF#32 ∧
      (cnfOfClauses (kittenOrigClauses ks)).EntailsClause (cnfClause [lit.toNat]) ∧
      (ks.ante ≠ 0#32 →
        rsn.toNat < ks.nc.toNat ∧ kittenClauseLits ks rsn.toNat = [lit.toNat]))
    (hdec : rsn = 0xFFFFFFFF#32 →
      ∀ i < ks.trl_end.toNat, ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 ≠ ks.lvl)
    (hrsn_ok : rsn = 0xFFFFFFFF#32 ∨
      (rsn.toNat < ks.nc.toNat ∧ lit.toNat ∈ kittenClauseLits ks rsn.toNat ∧
       ∀ x ∈ kittenClauseLits ks rsn.toNat, x ≠ lit.toNat →
         ∃ j < ks.trl_end.toNat, (ks.trl[j]?.getD 0#32).toNat = x ^^^ 1)) :
    (kittenAssignStep ks lit rsn).Inv acap ∧
    KittenTrailSynced (kittenAssignStep ks lit rsn) := by
  let ks' := kittenAssignStep ks lit rsn
  have hsh' := kittenAssignStep_preserves_shapes hinv.shapes lit rsn
  have hcl' := kittenAssignStep_preserves_clauses hinv.shapes hinv.clauses hinc (rsn := rsn) hlit
  have hw' := kittenAssignStep_preserves_watches hinv.watches lit rsn
  have hnv := hinv.clauses.nv_le
  have hte_lt : ks.trl_end.toNat < ks.nv.toNat :=
    trl_end_lt_nv_of_unassigned hinv hlit (by simp [hun])
  have hun_pos : 0 < ks.unass.toNat := by have := hinv.assign.unass_eq; omega
  have hte_wrap : ks.trl_end.toNat + 1 < 2 ^ 32 := by unfold kMaxV at hnv; omega
  have e_te : ks'.trl_end.toNat = ks.trl_end.toNat + 1 := by
    dsimp only [ks', kittenAssignStep]; bv_omega
  have e_un : ks'.unass.toNat = ks.unass.toNat - 1 := by
    dsimp only [ks', kittenAssignStep]
    rw [ite_eq_left hun_pos]
    bv_omega
  have hnl_lt : (lit.toNat ^^^ 1) < 2 * ks.nv.toNat := by
    rcases nat_xor1_cases lit.toNat with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega
  have hnl_eq : (lit ^^^ 1#32).toNat = lit.toNat ^^^ 1 := by simp
  have hv_eq : (lit >>> 1).toNat = lit.toNat / 2 := (bv32_lit_div2_bv hlit).1
  have hvals_len : ks.vals.length = 256 := hinv.shapes.vals_len
  have hlvl_len : ks.lvlArr.length = 128 := hinv.shapes.lvlArr_len
  have hrsn_len : ks.rsn.length = 128 := hinv.shapes.rsn_len
  have htrl_len : ks.trl.length = 128 := hinv.shapes.trl_len
  have hlit_256 : lit.toNat < 256 := by unfold kMaxV at hnv; omega
  have hnl_256 : (lit.toNat ^^^ 1) < 256 := by unfold kMaxV at hnv; omega
  have hv_128 : lit.toNat / 2 < 128 := by unfold kMaxV at hnv; omega
  have hte_128 : ks.trl_end.toNat < 128 := by unfold kMaxV at hnv; omega
  have hne_nl : lit.toNat ≠ (lit.toNat ^^^ 1) := by
    rcases nat_xor1_cases lit.toNat with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega
  have hnot_trl : ∀ i < ks.trl_end.toNat,
      (ks.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := by
    intro i hi heq
    have hnz := (hinv.assign.vals_nz_iff_trl lit.toNat hlit).mpr ⟨i, hi, heq⟩
    simp [hun] at hnz
  have hvals_lit : ks'.vals[lit.toNat]? = some 1#32 := by
    dsimp only [ks', kittenAssignStep]
    rw [hnl_eq, List.getElem?_set_ne hne_nl.symm, List.getElem?_set_self (by omega)]
  have hvals_nl : ks'.vals[lit.toNat ^^^ 1]? = some 2#32 := by
    dsimp only [ks', kittenAssignStep]
    rw [hnl_eq, List.getElem?_set_self (by simp; omega)]
  have hvals_other : ∀ x, x / 2 ≠ lit.toNat / 2 → ks'.vals[x]? = ks.vals[x]? := by
    intro x hne
    have hx1 : lit.toNat ≠ x := by
      rcases nat_xor1_cases x with ⟨_, _⟩ | ⟨_, _⟩ <;>
        rcases nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
    have hx2 : lit.toNat ^^^ 1 ≠ x := by
      rcases nat_xor1_cases x with ⟨_, _⟩ | ⟨_, _⟩ <;>
        rcases nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
    dsimp only [ks', kittenAssignStep]
    rw [hnl_eq, List.getElem?_set_ne hx2, List.getElem?_set_ne hx1]
  have htrl_lt_idx : ∀ i < ks.trl_end.toNat, ks'.trl[i]? = ks.trl[i]? := fun i hi => by
    dsimp only [ks', kittenAssignStep]; exact List.getElem?_set_ne (by omega)
  have htrl_end_idx : ks'.trl[ks.trl_end.toNat]? = some lit := by
    dsimp only [ks', kittenAssignStep]; exact List.getElem?_set_self (by omega)
  have hlvl_other : ∀ v, v ≠ lit.toNat / 2 → ks'.lvlArr[v]? = ks.lvlArr[v]? := fun v hne => by
    dsimp only [ks', kittenAssignStep]; rw [hv_eq]; exact List.getElem?_set_ne hne.symm
  have hlvl_v : ks'.lvlArr[lit.toNat / 2]? = some ks.lvl := by
    dsimp only [ks', kittenAssignStep]; rw [hv_eq]; exact List.getElem?_set_self (by omega)
  have hrsn_other : ∀ v, v ≠ lit.toNat / 2 → ks'.rsn[v]? = ks.rsn[v]? := fun v hne => by
    dsimp only [ks', kittenAssignStep]; rw [hv_eq]; exact List.getElem?_set_ne hne.symm
  have hrsn_v : ks'.rsn[lit.toNat / 2]? = some rsn := by
    dsimp only [ks', kittenAssignStep]; rw [hv_eq]; exact List.getElem?_set_self (by omega)
  have hsync' : KittenTrailSynced ks' := by
    intro i hi
    rw [e_te] at hi
    by_cases hie : i = ks.trl_end.toNat
    · subst hie
      change ks'.vals[(ks'.trl[ks.trl_end.toNat]?.getD 0#32).toNat]? = some 1#32 ∧
        ks'.vals[(ks'.trl[ks.trl_end.toNat]?.getD 0#32).toNat ^^^ 1]? = some 2#32
      rw [htrl_end_idx, Option.getD_some]
      exact ⟨hvals_lit, hvals_nl⟩
    · have hi' : i < ks.trl_end.toNat := by omega
      have hsy := hsync i hi'
      let l := (ks.trl[i]?.getD 0#32).toNat
      have hne_v : l / 2 ≠ lit.toNat / 2 := hnot_trl i hi'
      have hne_vx : (l ^^^ 1) / 2 ≠ lit.toNat / 2 := by
        rcases nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
      change ks'.vals[(ks'.trl[i]?.getD 0#32).toNat]? = some 1#32 ∧
        ks'.vals[(ks'.trl[i]?.getD 0#32).toNat ^^^ 1]? = some 2#32
      rw [htrl_lt_idx i hi']
      change ks'.vals[l]? = some 1#32 ∧ ks'.vals[l ^^^ 1]? = some 2#32
      rw [hvals_other l hne_v, hvals_other (l ^^^ 1) hne_vx]
      exact hsy
  have hba' : KittenBaseAssignOk ks' := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e_te]; change (ks.trl_end.toNat + 1) ≤ ks.nv.toNat; omega
    · rw [e_te]; change ks.prop.toNat ≤ ks.trl_end.toNat + 1
      have := hinv.assign.prop_le; omega
    · rw [e_un, e_te]; change (ks.unass.toNat - 1) + (ks.trl_end.toNat + 1) = ks.nv.toNat
      have := hinv.assign.unass_eq; omega
    · intro l hl
      change l < 2 * ks.nv.toNat at hl
      by_cases hv : l / 2 = lit.toNat / 2
      · rcases nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;>
          rcases nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩
        · rw [show l = lit.toNat by omega, hvals_lit]; exact Or.inr (Or.inl rfl)
        · rw [show l = lit.toNat ^^^ 1 by omega, hvals_nl]; exact Or.inr (Or.inr rfl)
        · rw [show l = lit.toNat ^^^ 1 by omega, hvals_nl]; exact Or.inr (Or.inr rfl)
        · rw [show l = lit.toNat by omega, hvals_lit]; exact Or.inr (Or.inl rfl)
      · rw [hvals_other l hv]; exact hinv.assign.vals_dom l hl
    · intro l hl
      change l < 2 * ks.nv.toNat at hl
      by_cases hv : l / 2 = lit.toNat / 2
      · rcases nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;>
          rcases nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩
        · rw [show l = lit.toNat by omega, hvals_lit, hvals_nl]; simp
        · rw [show l = lit.toNat ^^^ 1 by omega, nat_xor1_xor1, hvals_nl, hvals_lit]; simp
        · rw [show l = lit.toNat ^^^ 1 by omega, nat_xor1_xor1, hvals_nl, hvals_lit]; simp
        · rw [show l = lit.toNat by omega, hvals_lit, hvals_nl]; simp
      · have hne_x : (l ^^^ 1) / 2 ≠ lit.toNat / 2 := by
          rcases nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
        rw [hvals_other l hv, hvals_other (l ^^^ 1) hne_x]
        exact hinv.assign.vals_neg_iff l hl
    · intro l hl
      change l < 2 * ks.nv.toNat at hl
      rw [e_te]
      by_cases hv : l / 2 = lit.toNat / 2
      · constructor
        · intro _
          exact ⟨ks.trl_end.toNat, Nat.lt_succ_self _, by
            rw [htrl_end_idx, Option.getD_some]; exact hv.symm⟩
        · intro _
          rcases nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;>
            rcases nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩
          · rw [show l = lit.toNat by omega, hvals_lit]; simp
          · rw [show l = lit.toNat ^^^ 1 by omega, hvals_nl]; simp
          · rw [show l = lit.toNat ^^^ 1 by omega, hvals_nl]; simp
          · rw [show l = lit.toNat by omega, hvals_lit]; simp
      · rw [hvals_other l hv]
        rw [hinv.assign.vals_nz_iff_trl l hl]
        constructor
        · rintro ⟨i, hi, hiv⟩
          exact ⟨i, Nat.lt_succ_of_lt hi, by rw [htrl_lt_idx i hi]; exact hiv⟩
        · rintro ⟨i, hi, hiv⟩
          by_cases hie : i = ks.trl_end.toNat
          · subst hie; rw [htrl_end_idx, Option.getD_some] at hiv; exact absurd hiv.symm hv
          · exact ⟨i, by omega, by rw [htrl_lt_idx i (by omega)] at hiv; exact hiv⟩
    · unfold kittenTrailLits
      rw [e_te]
      dsimp only [ks', kittenAssignStep]
      rw [List.map_map]
      have htk : (ks.trl.set ks.trl_end.toNat lit).take (ks.trl_end.toNat + 1) =
          ks.trl.take ks.trl_end.toNat ++ [lit] := by
        rw [List.take_succ_eq_append_getElem (by rw [List.length_set, htrl_len]; omega),
          List.take_set_of_le (le_refl _),
          List.getElem_set_self (by rw [List.length_set, htrl_len]; omega)]
      rw [htk, List.map_append, List.map_singleton, List.nodup_append]
      refine ⟨?_, by simp, fun x hx y hy heq => ?_⟩
      · simpa [kittenTrailLits, List.map_map] using hinv.assign.trl_nodup
      · simp only [List.mem_singleton] at hy; subst hy
        simp only [List.mem_map, List.mem_take_iff_getElem, Function.comp_def] at hx
        obtain ⟨b, ⟨i, hi, hget⟩, hbeq⟩ := hx
        have hi_te : i < ks.trl_end.toNat := by omega
        have hget' : (ks.trl[i]?.getD 0#32).toNat / 2 = lit.toNat / 2 := by
          rw [List.getElem?_eq_getElem (by omega : i < ks.trl.length), Option.getD_some, hget]
          exact hbeq.trans heq
        exact hnot_trl i hi_te hget'
    · intro l hl
      unfold kittenTrailLits at hl
      rw [e_te] at hl
      dsimp only [ks', kittenAssignStep] at hl
      have htk : (ks.trl.set ks.trl_end.toNat lit).take (ks.trl_end.toNat + 1) =
          ks.trl.take ks.trl_end.toNat ++ [lit] := by
        rw [List.take_succ_eq_append_getElem (by rw [List.length_set, htrl_len]; omega),
          List.take_set_of_le (le_refl _),
          List.getElem_set_self (by rw [List.length_set, htrl_len]; omega)]
      rw [htk, List.map_append, List.map_singleton, List.mem_append, List.mem_singleton] at hl
      rcases hl with hl | rfl
      · exact hinv.assign.trl_lt l hl
      · exact hlit
    · intro v hv
      change v < ks.nv.toNat at hv
      change (ks'.lvlArr[v]?.getD 0#32).toNat ≤ ks.lvl.toNat
      by_cases hvv : v = lit.toNat / 2
      · subst hvv; rw [hlvl_v]; exact le_refl _
      · rw [hlvl_other v hvv]; exact hinv.assign.trl_lvl_le v hv
    · intro v hv hv0
      change v < ks.nv.toNat at hv
      have hne_v : v ≠ lit.toNat / 2 := by
        intro hvv; subst hvv
        have h2 : 2 * (lit.toNat / 2) = lit.toNat ∨ 2 * (lit.toNat / 2) = lit.toNat ^^^ 1 := by
          rcases nat_xor1_cases lit.toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
        rcases h2 with h2 | h2
        · rw [h2, hvals_lit] at hv0; cases hv0
        · rw [h2, hvals_nl] at hv0; cases hv0
      change ks'.lvlArr[v]?.getD 0#32 = 0#32 ∧ ks'.rsn[v]?.getD 0#32 = 0xFFFFFFFF#32
      rw [hlvl_other v hne_v, hrsn_other v hne_v]
      apply hinv.assign.unass_lvl_zero v hv
      rwa [← hvals_other (2 * v) (by omega)]
    · intro i j hij hj
      rw [e_te] at hj
      by_cases hje : j = ks.trl_end.toNat
      · subst hje
        rw [htrl_end_idx, Option.getD_some, hlvl_v, Option.getD_some]
        by_cases hie : i = ks.trl_end.toNat
        · subst hie; rw [htrl_end_idx, Option.getD_some, hlvl_v]; exact le_refl _
        · have hi' : i < ks.trl_end.toNat := by omega
          rw [htrl_lt_idx i hi']
          have hne_v := hnot_trl i hi'
          rw [hlvl_other _ hne_v]
          have hmem := mem_kittenTrailLits_of_lt hi' (by omega : ks.trl_end.toNat ≤ ks.trl.length)
          have hli := hinv.assign.trl_lt _ hmem
          exact hinv.assign.trl_lvl_le _ (by omega)
      · have hj' : j < ks.trl_end.toNat := by omega
        have hi' : i < ks.trl_end.toNat := by omega
        rw [htrl_lt_idx i hi', htrl_lt_idx j hj',
          hlvl_other _ (hnot_trl i hi'), hlvl_other _ (hnot_trl j hj')]
        exact hinv.assign.trl_lvl_mono i j hij hj'
    · intro i j hji hi heq
      rw [e_te] at hi
      by_cases hie : i = ks.trl_end.toNat
      · subst hie
        have hj' : j < ks.trl_end.toNat := by omega
        rw [htrl_end_idx, Option.getD_some, hlvl_v, Option.getD_some,
          htrl_lt_idx j hj', hlvl_other _ (hnot_trl j hj')] at heq
        rw [htrl_end_idx, Option.getD_some, hrsn_v, Option.getD_some]
        intro hrsn_eq
        exact hdec hrsn_eq j hj' heq
      · have hi' : i < ks.trl_end.toNat := by omega
        have hj' : j < ks.trl_end.toNat := by omega
        rw [htrl_lt_idx i hi', htrl_lt_idx j hj',
          hlvl_other _ (hnot_trl i hi'), hlvl_other _ (hnot_trl j hj')] at heq
        rw [htrl_lt_idx i hi', hrsn_other _ (hnot_trl i hi')]
        exact hinv.assign.dec_earliest i j hji hi' heq
    · intro i hi l hlv
      rw [e_te] at hi
      dsimp only [l] at hlv ⊢
      by_cases hie : i = ks.trl_end.toNat
      · subst hie
        rw [htrl_end_idx, Option.getD_some, hlvl_v, Option.getD_some] at hlv
        rw [htrl_end_idx, Option.getD_some, hrsn_v, Option.getD_some]
        obtain ⟨hr_ne, hent, hante⟩ := hlvl0 hlv
        refine ⟨hr_ne, hvals_lit, hvals_nl, hent, fun ha => ?_⟩
        exact hante ha
      · have hi' : i < ks.trl_end.toNat := by omega
        have hne_v := hnot_trl i hi'
        rw [htrl_lt_idx i hi', hlvl_other _ hne_v] at hlv
        rw [htrl_lt_idx i hi', hrsn_other _ hne_v]
        have hne_vx : ((ks.trl[i]?.getD 0#32).toNat ^^^ 1) / 2 ≠ lit.toNat / 2 := by
          rcases nat_xor1_cases (ks.trl[i]?.getD 0#32).toNat with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
        rw [hvals_other _ hne_v, hvals_other _ hne_vx]
        exact hinv.assign.lvl0_ok i hi' hlv
  have hrsn' : ReasonOk ks' := by
    intro i hi
    rw [e_te] at hi
    by_cases hie : i = ks.trl_end.toNat
    · subst hie
      change _ = 0xFFFFFFFF#32 ∨ _
      rw [htrl_end_idx, Option.getD_some, hrsn_v, Option.getD_some]
      rcases hrsn_ok with rfl | ⟨hr_lt, hr_mem, hall⟩
      · exact Or.inl rfl
      · refine Or.inr ⟨hr_lt, hr_mem, fun x hx hxl => ?_⟩
        obtain ⟨j, hj, hjx⟩ := hall x hx hxl
        exact ⟨j, hj, by rw [htrl_lt_idx j hj]; exact hjx⟩
    · have hi' : i < ks.trl_end.toNat := by omega
      have hro := hinv.reasons i hi'
      change _ = 0xFFFFFFFF#32 ∨ _
      rw [htrl_lt_idx i hi', hrsn_other _ (hnot_trl i hi')]
      rcases hro with hdec_i | ⟨hr_lt, hr_mem, hall⟩
      · exact Or.inl hdec_i
      · refine Or.inr ⟨hr_lt, hr_mem, fun x hx hxl => ?_⟩
        obtain ⟨j, hj, hjx⟩ := hall x hx hxl
        exact ⟨j, hj, by rw [htrl_lt_idx j (Nat.lt_trans hj hi')]; exact hjx⟩
  exact ⟨⟨hsh', hcl', hw', hba', hrsn'⟩, hsync'⟩

private theorem baseAssignOk_of_unchanged {ks ks' : KittenState}
    (h : KittenBaseAssignOk ks)
    (e1 : ks'.trl_end = ks.trl_end) (e2 : ks'.prop = ks.prop) (e3 : ks'.unass = ks.unass)
    (e4 : ks'.nv = ks.nv) (e5 : ks'.vals = ks.vals) (e6 : ks'.trl = ks.trl)
    (e7 : ks'.lvlArr = ks.lvlArr) (e8 : ks'.lvl = ks.lvl) (e9 : ks'.rsn = ks.rsn)
    (e10 : ks'.orig_nc = ks.orig_nc) (e11 : ks'.clOff = ks.clOff) (e12 : ks'.clMeta = ks.clMeta)
    (e13 : ks'.arena = ks.arena) (e14 : ks'.ante = ks.ante) (e15 : ks'.nc = ks.nc) :
    KittenBaseAssignOk ks' :=
  let hcl : ∀ c, kittenClauseLits ks' c = kittenClauseLits ks c := fun c => by
    simp [kittenClauseLits, kittenClauseOff, kittenClauseSize, kittenClauseMeta, e11, e12, e13]
  let horig : kittenOrigClauses ks' = kittenOrigClauses ks :=
    kittenOrigClauses_eq_of e10 fun c _ => hcl c
  { trl_end_le := by rw [e1, e4]; exact h.trl_end_le
    prop_le := by rw [e1, e2]; exact h.prop_le
    unass_eq := by rw [e1, e3, e4]; exact h.unass_eq
    vals_dom := by rw [e4, e5]; exact h.vals_dom
    vals_neg_iff := by rw [e4, e5]; exact h.vals_neg_iff
    vals_nz_iff_trl := by rw [e1, e4, e5, e6]; exact h.vals_nz_iff_trl
    trl_nodup := by simpa [kittenTrailLits, e1, e6] using h.trl_nodup
    trl_lt := by simpa [kittenTrailLits, e1, e4, e6] using h.trl_lt
    trl_lvl_le := by rw [e4, e7, e8]; exact h.trl_lvl_le
    unass_lvl_zero := by rw [e4, e5, e7, e9]; exact h.unass_lvl_zero
    trl_lvl_mono := by rw [e1, e6, e7]; exact h.trl_lvl_mono
    dec_earliest := by rw [e1, e6, e7, e9]; exact h.dec_earliest
    lvl0_ok := fun i hi hlv => by
      have hi' : i < ks.trl_end.toNat := by rwa [← e1]
      have hlv' : ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 = 0#32 := by
        simpa [e6, e7] using hlv
      have h0 := h.lvl0_ok i hi' hlv'
      simpa [horig, hcl, e5, e6, e9, e14, e15] using h0 }

private theorem reasonOk_of_unchanged {ks ks' : KittenState} (h : ReasonOk ks)
    (e1 : ks'.trl_end = ks.trl_end) (e2 : ks'.trl = ks.trl) (e3 : ks'.rsn = ks.rsn)
    (e4 : ks'.nc = ks.nc) (e5 : ks'.clOff = ks.clOff) (e6 : ks'.clMeta = ks.clMeta)
    (e7 : ks'.arena = ks.arena) : ReasonOk ks' := by
  simpa [ReasonOk, kittenClauseLits, kittenClauseOff, kittenClauseSize, kittenClauseMeta,
    e1, e2, e3, e4, e5, e6, e7] using h

/-- Setting `incons := cid` at level `0` on a falsified clause `cid` preserves `Inv` & `Synced`. -/
theorem inv_set_incons_lvl0 {acap : Nat} {ks : KittenState}
    (hinv : ks.Inv acap) (hsync : KittenTrailSynced ks)
    (hlvl0 : ks.lvl = 0#32) {cid : BitVec 32} (hcid : cid.toNat < ks.nc.toNat)
    (hfals : ∀ l ∈ kittenClauseLits ks cid.toNat, ks.vals[l]? = some 2#32) :
    (ks.putHdr .incons cid).Inv acap ∧ KittenTrailSynced (ks.putHdr .incons cid) := by
  let ks' := ks.putHdr .incons cid
  have hsh' : ks'.ShapesOk acap := hinv.shapes.putHdr .incons cid
  have hunsat : (cnfOfClauses (kittenOrigClauses ks)).Unsat :=
    kitten_conflict_unsat_lvl0 hinv.shapes hinv.clauses hinv.assign hlvl0 hcid hfals
  have hcl' : KittenClausesOk acap ks' :=
    { hinv.clauses with
      incons_ok := fun _ => by
        refine ⟨hcid, hunsat, fun l hl => ?_⟩
        have hl_lt := (hinv.clauses.cl_wf cid.toNat hcid).2.2.2.1 l hl
        have hlv : ks.lvlArr[l / 2]?.getD 0#32 = 0#32 := by
          have hle := hinv.assign.trl_lvl_le (l / 2) (by omega)
          rw [hlvl0] at hle
          exact BitVec.eq_of_toNat_eq (Nat.eq_zero_of_le_zero hle)
        refine ⟨hfals l hl, hlv, fun ha => ?_⟩
        obtain ⟨i, hi, hieq⟩ :=
          kitten_falsified_to_trail hinv.shapes hinv.clauses.nv_le hinv.assign hsync hl_lt
            (hfals l hl)
        have hlv_trl : ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 = 0#32 := by
          rw [hieq, show litNeg l / 2 = l / 2 from by
            rw [← litNeg_eq_xor1]
            rcases nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;> omega]
          exact hlv
        have h0 := hinv.assign.lvl0_ok i hi hlv_trl
        have h0r := h0.2.2.2.2 ha
        dsimp only at h0r ⊢
        rw [hieq, ← litNeg_eq_xor1] at h0r
        have hdiv : (l ^^^ 1) / 2 = l / 2 := by
          rcases nat_xor1_cases l with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
        rw [hdiv] at h0r
        exact h0r }
  have hba' := baseAssignOk_of_unchanged (ks' := ks') hinv.assign
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hrsn' := reasonOk_of_unchanged (ks' := ks') hinv.reasons rfl rfl rfl rfl rfl rfl rfl
  exact ⟨⟨hsh', hcl', hinv.watches, hba', hrsn'⟩, hsync⟩

/-- Setting `tick_lim` preserves `Inv`. -/
theorem inv_set_tick_lim {acap : Nat} {ks : KittenState}
    (hinv : ks.Inv acap) (v : BitVec 32) :
    (ks.putHdr .tick_lim v).Inv acap :=
  ⟨hinv.shapes.putHdr .tick_lim v, { hinv.clauses with }, hinv.watches,
   baseAssignOk_of_unchanged (ks' := ks.putHdr .tick_lim v)
     hinv.assign rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl,
   reasonOk_of_unchanged (ks' := ks.putHdr .tick_lim v)
     hinv.reasons rfl rfl rfl rfl rfl rfl rfl⟩

/-- Clearing `failing := 0xFFFFFFFF#32` preserves `Inv`. -/
theorem inv_set_failing_none {acap : Nat} {ks : KittenState} (hinv : ks.Inv acap) :
    (ks.putHdr .failing 0xFFFFFFFF#32).Inv acap :=
  ⟨hinv.shapes.putHdr .failing 0xFFFFFFFF#32,
   { hinv.clauses with failing_ok := fun _ hf => absurd rfl hf }, hinv.watches,
   baseAssignOk_of_unchanged (ks' := ks.putHdr .failing 0xFFFFFFFF#32)
     hinv.assign rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl,
   reasonOk_of_unchanged (ks' := ks.putHdr .failing 0xFFFFFFFF#32)
     hinv.reasons rfl rfl rfl rfl rfl rfl rfl⟩

/-- Setting `qsearch` preserves `Inv` (`kittenState_setQueue_preserves_inv`). -/
theorem inv_set_qsearch {acap : Nat} {ks : KittenState} (hinv : ks.Inv acap) (v : BitVec 32) :
    (ks.putHdr .qsearch v).Inv acap := by
  change ({ ks with qsearch := v } : KittenState).Inv acap
  exact kittenState_setQueue_preserves_inv hinv hinv.shapes.qprev_len hinv.shapes.qnext_len
    hinv.shapes.qstampArr_len

/-- Incrementing `lvl` by `1` then calling `kittenAssignStep` for a decision literal preserves
`Inv`, `KittenTrailSynced`, `KittenLvlNonempty`, `KittenFreeDecLate`, and `SolveFrame`. -/
theorem decide_step_preserves {acap : Nat} {ks0 ks : KittenState}
    (hinv : ks.Inv acap) (hsync : KittenTrailSynced ks)
    (hinc : ks.incons = 0xFFFFFFFF#32)
    (hframe : SolveFrame ks0 ks) (hlvlne : KittenLvlNonempty ks) (hlate : KittenFreeDecLate ks)
    {lit : BitVec 32} (hlit : lit.toNat < 2 * ks.nv.toNat)
    (hun : ks.vals[lit.toNat]? = some 0#32)
    (hall_ass : lit.toNat ∉ kittenAssumpLits ks →
      ∀ a ∈ kittenAssumpLits ks, ks.vals[a]? = some 1#32) :
    let ks1 := ks.putHdr .lvl (ks.lvl + 1#32)
    let ks' := kittenAssignStep ks1 lit 0xFFFFFFFF#32
    ks'.Inv acap ∧ KittenTrailSynced ks' ∧ ks'.incons = 0xFFFFFFFF#32 ∧
    SolveFrame ks0 ks' ∧ KittenLvlNonempty ks' ∧ KittenFreeDecLate ks' := by
  intro ks1 ks'
  have hnv := hinv.clauses.nv_le
  have hle_te := lvl_le_trl_end hinv hlvlne
  have hte_le := hinv.assign.trl_end_le
  have hlvl_wrap : ks.lvl.toNat + 1 < 2 ^ 32 := by unfold kMaxV at hnv; omega
  have hlvl1_nat : (ks.lvl + 1#32).toNat = ks.lvl.toNat + 1 := by bv_omega
  have hlvl1_ne0 : ks.lvl + 1#32 ≠ 0#32 := fun h => by
    have := congrArg BitVec.toNat h; rw [hlvl1_nat] at this; simp at this
  have hinv1 : ks1.Inv acap :=
    ⟨hinv.shapes.putHdr .lvl (ks.lvl + 1#32),
     { hinv.clauses with },
     hinv.watches,
     { hinv.assign with
       trl_lvl_le := fun v hv => by
         change (ks.lvlArr[v]?.getD 0#32).toNat ≤ (ks.lvl + 1#32).toNat
         rw [hlvl1_nat]; have := hinv.assign.trl_lvl_le v hv; omega },
     hinv.reasons⟩
  have hsync1 : KittenTrailSynced ks1 := hsync
  have hdec1 : ∀ i < ks1.trl_end.toNat,
      ks1.lvlArr[(ks1.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 ≠ ks1.lvl := by
    intro i hi heq
    have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
      rw [hinv.shapes.trl_len]; unfold kMaxV at hnv; omega
    have hli := hinv.assign.trl_lt _ (mem_kittenTrailLits_of_lt hi htrl_len)
    have hle := hinv.assign.trl_lvl_le ((ks.trl[i]?.getD 0#32).toNat / 2) (by omega)
    have hcon := congrArg BitVec.toNat heq
    change (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
      (ks.lvl + 1#32).toNat at hcon
    rw [hlvl1_nat] at hcon
    omega
  obtain ⟨hinv', hsync'⟩ := kittenAssignStep_preserves_inv hinv1 hsync1 hinc hlit hun
    (fun h => absurd h hlvl1_ne0) (fun _ => hdec1) (Or.inl rfl)
  have hte_lt : ks.trl_end.toNat < ks.nv.toNat :=
    trl_end_lt_nv_of_unassigned hinv hlit (by simp [hun])
  have hte_wrap : ks.trl_end.toNat + 1 < 2 ^ 32 := by unfold kMaxV at hnv; omega
  have e_te : ks'.trl_end.toNat = ks.trl_end.toNat + 1 := by
    dsimp only [ks', kittenAssignStep, ks1, KittenState.putHdr]; bv_omega
  have e_lvl : ks'.lvl = ks.lvl + 1#32 := rfl
  have e_trl_lt : ∀ i < ks.trl_end.toNat, ks'.trl[i]? = ks.trl[i]? := fun i hi => by
    dsimp only [ks', kittenAssignStep, ks1, KittenState.putHdr]
    exact List.getElem?_set_ne (by omega)
  have e_trl_end : ks'.trl[ks.trl_end.toNat]? = some lit := by
    dsimp only [ks', kittenAssignStep, ks1, KittenState.putHdr]
    exact List.getElem?_set_self (by rw [hinv.shapes.trl_len]; unfold kMaxV at hnv; omega)
  have e_lvl_v : ks'.lvlArr[lit.toNat / 2]? = some (ks.lvl + 1#32) := by
    dsimp only [ks', kittenAssignStep, ks1, KittenState.putHdr]
    rw [(bv32_lit_div2_bv hlit).1]
    exact List.getElem?_set_self (by rw [hinv.shapes.lvlArr_len]; unfold kMaxV at hnv; omega)
  have hnot_trl : ∀ i < ks.trl_end.toNat,
      (ks.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := by
    intro i hi heq
    have hnz := (hinv.assign.vals_nz_iff_trl lit.toNat hlit).mpr ⟨i, hi, heq⟩
    simp [hun] at hnz
  have e_lvl_other : ∀ v, v ≠ lit.toNat / 2 → ks'.lvlArr[v]? = ks.lvlArr[v]? := fun v hne => by
    dsimp only [ks', kittenAssignStep, ks1, KittenState.putHdr]
    rw [(bv32_lit_div2_bv hlit).1]
    exact List.getElem?_set_ne hne.symm
  have e_rsn_other : ∀ v, v ≠ lit.toNat / 2 → ks'.rsn[v]? = ks.rsn[v]? := fun v hne => by
    dsimp only [ks', kittenAssignStep, ks1, KittenState.putHdr]
    rw [(bv32_lit_div2_bv hlit).1]
    exact List.getElem?_set_ne hne.symm
  have hlvlne' : KittenLvlNonempty ks' := by
    intro L hL0 hLle
    rw [e_lvl, hlvl1_nat] at hLle
    by_cases htop : L = ks.lvl.toNat + 1
    · subst htop
      refine ⟨ks.trl_end.toNat, by rw [e_te]; omega, ?_⟩
      rw [e_trl_end, Option.getD_some, e_lvl_v, Option.getD_some, hlvl1_nat]
    · obtain ⟨i, hi, hiv⟩ := hlvlne L hL0 (by omega)
      refine ⟨i, by rw [e_te]; omega, ?_⟩
      rw [e_trl_lt i hi, e_lvl_other _ (hnot_trl i hi)]
      exact hiv
  have hlate' : KittenFreeDecLate ks' := by
    intro p hp hrsn hnot a ha
    rw [e_te] at hp
    change a ∈ kittenAssumpLits ks at ha
    by_cases hpe : p = ks.trl_end.toNat
    · subst hpe
      rw [e_trl_end, Option.getD_some] at hnot
      have ha_val := hall_ass hnot a ha
      have ha_lt : a < 2 * ks.nv.toNat := by
        simp only [kittenAssumpLits, List.mem_map] at ha
        obtain ⟨ab, hab, rfl⟩ := ha
        rw [List.mem_take_iff_getElem] at hab
        obtain ⟨ia, hia, rfl⟩ := hab
        have hlen : ks.nassump.toNat ≤ ks.assump.length := by
          rw [hinv.shapes.assump_len]; exact hinv.clauses.nassump_le
        have := hinv.clauses.assump_ok ia (by omega)
        rwa [List.getElem?_eq_getElem (by omega : ia < ks.assump.length), Option.getD_some] at this
      have hnz : ks.vals[a]?.getD 0#32 ≠ 0#32 := by simp [ha_val]
      obtain ⟨q, hq, hqv⟩ := (hinv.assign.vals_nz_iff_trl a ha_lt).mp hnz
      have hsy_q := hsync q hq
      let lq := (ks.trl[q]?.getD 0#32).toNat
      have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
        rw [hinv.shapes.trl_len]; unfold kMaxV at hnv; omega
      have hql_lt : lq < 2 * ks.nv.toNat :=
        hinv.assign.trl_lt lq (mem_kittenTrailLits_of_lt hq htrl_len)
      have ha_eq : lq = a := by
        rcases (litVar_eq_iff lq a).mp (by simpa [litVar] using hqv) with heq | heq
        · exact heq
        · exfalso
          have hx : lq ^^^ 1 = a := by
            rw [heq, ← litNeg_eq_xor1, nat_xor1_xor1]
          dsimp only at hsy_q
          rw [← hx] at ha_val
          dsimp only [lq] at ha_val
          rw [ha_val] at hsy_q
          cases hsy_q.2
      refine ⟨q, hq, ?_⟩
      rw [e_trl_lt q hq]; exact ha_eq
    · have hp' : p < ks.trl_end.toNat := by omega
      rw [e_trl_lt p hp'] at hrsn hnot
      rw [e_rsn_other _ (hnot_trl p hp')] at hrsn
      obtain ⟨q, hqp, hqa⟩ := hlate p hp' hrsn hnot a ha
      exact ⟨q, hqp, by rw [e_trl_lt q (by omega)]; exact hqa⟩
  have hframe' : SolveFrame ks0 ks' := SolveFrame.trans hframe
    ⟨rfl, rfl, rfl, rfl, rfl, KittenCnfPermEquiv.refl _, fun _ _ => rfl, fun _ _ => rfl⟩
  exact ⟨hinv', hsync', hinc, hframe', hlvlne', hlate'⟩

/-- Under `KittenFreeDecLate`, a falsified assumption literal forces all trail decisions to be
assumptions, yielding UNSAT of `kittenOrigClauses ks` + `kittenAssumpLits ks`. -/
theorem allDecisionsInAssumps_of_late {acap : Nat} {ks : KittenState}
    (hinv : ks.Inv acap) (hsync : KittenTrailSynced ks) (hlate : KittenFreeDecLate ks)
    {a : Nat} (ha_mem : a ∈ kittenAssumpLits ks) (hfals : ks.vals[a]? = some 2#32) :
    KittenAllDecisionsInAssumps ks ∧
    (cnfOfClauses (kittenOrigClauses ks) ++ unitsCnf (kittenAssumpLits ks)).Unsat := by
  have hdec : KittenAllDecisionsInAssumps ks := by
    intro d hd
    by_cases hd_mem : d ∈ kittenAssumpLits ks
    · exact hd_mem
    · exfalso
      have hnv := hinv.clauses.nv_le
      have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
        rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; unfold kMaxV at hnv; omega
      obtain ⟨p, hp, rfl, hrsn⟩ := (mem_kittenTrailDecisions_iff htrl_len).mp hd
      obtain ⟨q, hq, hqa⟩ := hlate p hp hrsn hd_mem a ha_mem
      have hsy := hsync q (Nat.lt_trans hq hp)
      dsimp only at hsy
      rw [hqa, hfals] at hsy
      cases hsy.1
  refine ⟨hdec, ?_⟩
  simp only [kittenAssumpLits, List.mem_map, List.mem_take_iff_getElem] at ha_mem
  obtain ⟨ab, ⟨ia, hia, rfl⟩, rfl⟩ := ha_mem
  have hlen : ks.nassump.toNat ≤ ks.assump.length := by
    rw [hinv.shapes.assump_len]; exact hinv.clauses.nassump_le
  have hia_lt : ia < ks.nassump.toNat := by omega
  have hget : (ks.assump[ia]?.getD 0#32).toNat = ks.assump[ia].toNat := by
    rw [List.getElem?_eq_getElem (by omega : ia < ks.assump.length), Option.getD_some]
  rw [← hget] at hfals
  exact kitten_falsified_assump_unsat hinv hsync hdec hia_lt hfals

private theorem trl_idx_eq_of_val {acap : Nat} {ks : KittenState}
    (hinv : ks.Inv acap) {p q : Nat} (hp : p < ks.trl_end.toNat) (hq : q < ks.trl_end.toNat)
    (heq : (ks.trl[p]?.getD 0#32).toNat = (ks.trl[q]?.getD 0#32).toNat) : p = q := by
  by_cases hpq : p = q
  · exact hpq
  · exfalso
    have hnv := hinv.clauses.nv_le
    have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
      rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; unfold kMaxV at hnv; omega
    have hnd := hinv.assign.trl_nodup
    unfold kittenTrailLits at hnd
    rw [List.map_map] at hnd
    have hml : (List.map ((fun x => x / 2) ∘ BitVec.toNat)
        (ks.trl.take ks.trl_end.toNat)).length = ks.trl_end.toNat := by
      simp [List.length_take, htrl_len]
    have hinj := list_nodup_getElem_inj hnd (by rw [hml]; exact hp) (by rw [hml]; exact hq)
      (show (List.map ((fun x => x / 2) ∘ BitVec.toNat)
          (ks.trl.take ks.trl_end.toNat))[p]'(by rw [hml]; exact hp) =
          (List.map ((fun x => x / 2) ∘ BitVec.toNat)
          (ks.trl.take ks.trl_end.toNat))[q]'(by rw [hml]; exact hq) by
        simp only [List.getElem_map, List.getElem_take, Function.comp_def]
        rw [List.getElem?_eq_getElem (by omega : p < ks.trl.length),
          List.getElem?_eq_getElem (by omega : q < ks.trl.length),
          Option.getD_some, Option.getD_some] at heq
        rw [heq])
    exact hpq hinj

/-- Transport `SolveLoopInv` across `full_kitten_propagate` (when `confl ≠ 0xFFFFFFFE#32`). -/
theorem solveLoopInv_of_propagate {acap : Nat} {ks0 ks ks' : KittenState} {confl : BitVec 32}
    (hinv : ks.Inv acap) (hinc : ks.incons = 0xFFFFFFFF#32) (hfail : ks.failing = 0xFFFFFFFF#32)
    (hframe : SolveFrame ks0 ks) (hlvlne : KittenLvlNonempty ks) (hlate : KittenFreeDecLate ks)
    (hinv' : ks'.Inv acap) (hsync' : KittenTrailSynced ks')
    (e_nv : ks'.nv = ks.nv) (e_on : ks'.orig_nc = ks.orig_nc) (e_lvl : ks'.lvl = ks.lvl)
    (e_inc : ks'.incons = ks.incons) (e_fail : ks'.failing = ks.failing)
    (e_ant : ks'.ante = ks.ante) (e_na : ks'.nassump = ks.nassump) (e_ass : ks'.assump = ks.assump)
    (hperm : KittenCnfPermEquiv (kittenOrigClauses ks') (kittenOrigClauses ks))
    (hclAux : ∀ ci < ks.orig_nc.toNat, ks'.clAux[ci]? = ks.clAux[ci]?)
    (hcore : ∀ ci < ks.orig_nc.toNat,
      (ks'.clMeta[ci]?.getD 0#32 &&& kmCore) = (ks.clMeta[ci]?.getD 0#32 &&& kmCore))
    (hdec_eq : kittenTrailDecisions ks' = kittenTrailDecisions ks)
    (hte_le : ks.trl_end.toNat ≤ ks'.trl_end.toNat)
    (htrl_kept : ∀ i < ks.trl_end.toNat, ks'.trl[i]? = ks.trl[i]? ∧
      ks'.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]? =
        ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?)
    (hc_ne : confl ≠ 0xFFFFFFFE#32)
    (hc_ok : confl ≠ 0xFFFFFFFF#32 → confl.toNat < ks'.nc.toNat ∧
      ∀ l ∈ kittenClauseLits ks' confl.toNat, ks'.vals[l]? = some 2#32) :
    SolveLoopInv acap ks0 ks' confl := by
  have hframe' : SolveFrame ks0 ks' :=
    SolveFrame.trans hframe ⟨e_nv, e_on, e_ant, e_na, e_ass, hperm, hclAux, hcore⟩
  have hlvlne' : KittenLvlNonempty ks' := by
    intro L hL0 hLle
    rw [e_lvl] at hLle
    obtain ⟨i, hi, hiv⟩ := hlvlne L hL0 hLle
    refine ⟨i, Nat.lt_of_lt_of_le hi hte_le, ?_⟩
    obtain ⟨ht, hl⟩ := htrl_kept i hi
    rw [ht, hl]
    exact hiv
  have hlate' : KittenFreeDecLate ks' := by
    intro p hp hrsn hnot a ha
    have hass_eq : kittenAssumpLits ks' = kittenAssumpLits ks := by
      unfold kittenAssumpLits; rw [e_na, e_ass]
    rw [hass_eq] at hnot ha
    have hnv' := hinv'.clauses.nv_le
    have htrl_len' : ks'.trl_end.toNat ≤ ks'.trl.length := by
      rw [hinv'.shapes.trl_len]; have := hinv'.assign.trl_end_le; unfold kMaxV at hnv'; omega
    have hnv := hinv.clauses.nv_le
    have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
      rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; unfold kMaxV at hnv; omega
    have hd_mem' : (ks'.trl[p]?.getD 0#32).toNat ∈ kittenTrailDecisions ks' :=
      (mem_kittenTrailDecisions_iff htrl_len').mpr ⟨p, hp, rfl, hrsn⟩
    rw [hdec_eq] at hd_mem'
    obtain ⟨p0, hp0, hp0_eq, hp0_rsn⟩ := (mem_kittenTrailDecisions_iff htrl_len).mp hd_mem'
    have hp0_eq' : (ks'.trl[p0]?.getD 0#32).toNat = (ks'.trl[p]?.getD 0#32).toNat := by
      rw [(htrl_kept p0 hp0).1]; exact hp0_eq
    obtain rfl : p0 = p := trl_idx_eq_of_val hinv' (Nat.lt_of_lt_of_le hp0 hte_le) hp hp0_eq'
    have hnot0 : (ks.trl[p0]?.getD 0#32).toNat ∉ kittenAssumpLits ks := by
      rw [← (htrl_kept p0 hp0).1]; exact hnot
    have hp0_rsn' : ks.rsn[(ks.trl[p0]?.getD 0#32).toNat / 2]?.getD 0#32 = 0xFFFFFFFF#32 := by
      rw [← (htrl_kept p0 hp0).1]; exact hp0_rsn
    obtain ⟨q, hqp, hqa⟩ := hlate p0 hp0 hp0_rsn' hnot0 a ha
    refine ⟨q, hqp, ?_⟩
    rw [(htrl_kept q (Nat.lt_trans hqp hp0)).1]; exact hqa
  exact ⟨hinv', hsync', e_inc.trans hinc, e_fail.trans hfail, hframe', hlvlne', hlate', hc_ne,
    hc_ok⟩

/-- Transport `SolveLoopInv` across `full_kitten_analyze` returning `ok = true` (prior to
calling `full_kitten_propagate`). -/
theorem solveLoopInv_of_analyze {acap : Nat} {ks0 ks ks' : KittenState}
    (hinv : ks.Inv acap) (hinc : ks.incons = 0xFFFFFFFF#32) (hfail : ks.failing = 0xFFFFFFFF#32)
    (hframe : SolveFrame ks0 ks) (hlvlne : KittenLvlNonempty ks) (hlate : KittenFreeDecLate ks)
    (hinv' : ks'.Inv acap) (hsync' : KittenTrailSynced ks')
    (e_nv : ks'.nv = ks.nv) (e_on : ks'.orig_nc = ks.orig_nc) (e_ant : ks'.ante = ks.ante)
    (e_na : ks'.nassump = ks.nassump) (e_ass : ks'.assump = ks.assump)
    (e_inc : ks'.incons = ks.incons) (e_fail : ks'.failing = ks.failing)
    (horig : kittenOrigClauses ks' = kittenOrigClauses ks)
    (hclAux : ∀ ci < ks.orig_nc.toNat, ks'.clAux[ci]? = ks.clAux[ci]?)
    (hcore : ∀ ci < ks.orig_nc.toNat,
      (ks'.clMeta[ci]?.getD 0#32 &&& kmCore) = (ks.clMeta[ci]?.getD 0#32 &&& kmCore))
    (hlvl_lt : ks'.lvl.toNat < ks.lvl.toNat)
    (hdec_sub : ∀ d ∈ kittenTrailDecisions ks', ∃ i < ks.trl_end.toNat,
      (ks.trl[i]?.getD 0#32).toNat = d ∧ d ∈ kittenTrailDecisions ks ∧
      (ks.lvlArr[d / 2]?.getD 0#32).toNat ≤ ks'.lvl.toNat)
    (hkept_below : ∀ i < ks.trl_end.toNat,
      (ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ ks'.lvl.toNat →
      i < ks'.trl_end.toNat ∧ ks'.trl[i]? = ks.trl[i]? ∧
      ks'.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]? =
        ks.lvlArr[(ks.trl[i]?.getD 0#32).toNat / 2]?) :
    SolveLoopInv acap ks0 ks' 0xFFFFFFFF#32 := by
  have hperm : KittenCnfPermEquiv (kittenOrigClauses ks') (kittenOrigClauses ks) := by
    rw [horig]; exact KittenCnfPermEquiv.refl _
  have hframe' : SolveFrame ks0 ks' :=
    SolveFrame.trans hframe ⟨e_nv, e_on, e_ant, e_na, e_ass, hperm, hclAux, hcore⟩
  have hlvlne' : KittenLvlNonempty ks' := by
    intro L hL0 hLle
    obtain ⟨i, hi, hiv⟩ := hlvlne L hL0 (Nat.le_trans hLle (Nat.le_of_lt hlvl_lt))
    obtain ⟨hi', ht, hl⟩ := hkept_below i hi (by rw [hiv]; exact hLle)
    refine ⟨i, hi', ?_⟩
    rw [ht, hl]
    exact hiv
  have hlate' : KittenFreeDecLate ks' := by
    intro p hp hrsn hnot a ha
    have hass_eq : kittenAssumpLits ks' = kittenAssumpLits ks := by
      unfold kittenAssumpLits; rw [e_na, e_ass]
    rw [hass_eq] at hnot ha
    have hnv' := hinv'.clauses.nv_le
    have htrl_len' : ks'.trl_end.toNat ≤ ks'.trl.length := by
      rw [hinv'.shapes.trl_len]; have := hinv'.assign.trl_end_le; unfold kMaxV at hnv'; omega
    have hnv := hinv.clauses.nv_le
    have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
      rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; unfold kMaxV at hnv; omega
    have hd_mem' : (ks'.trl[p]?.getD 0#32).toNat ∈ kittenTrailDecisions ks' :=
      (mem_kittenTrailDecisions_iff htrl_len').mpr ⟨p, hp, rfl, hrsn⟩
    obtain ⟨p0, hp0, hp0_eq, hp0_dec, hp0_lvl⟩ := hdec_sub _ hd_mem'
    have hle0 : (ks.lvlArr[(ks.trl[p0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        ks'.lvl.toNat := by
      rw [hp0_eq]; exact hp0_lvl
    obtain ⟨hp0', hp0_trl, _⟩ := hkept_below p0 hp0 hle0
    have hp0_eq' : (ks'.trl[p0]?.getD 0#32).toNat = (ks'.trl[p]?.getD 0#32).toNat := by
      rw [hp0_trl]; exact hp0_eq
    obtain rfl : p0 = p := trl_idx_eq_of_val hinv' hp0' hp hp0_eq'
    obtain ⟨_, _, _, hrsn0⟩ := (mem_kittenTrailDecisions_iff htrl_len).mp hp0_dec
    have hnot0 : (ks.trl[p0]?.getD 0#32).toNat ∉ kittenAssumpLits ks := by
      rw [← hp0_trl]; exact hnot
    obtain ⟨q, hqp, hqa⟩ := hlate p0 hp0 (by
      have := hp0_eq; rw [← this] at hrsn0; exact hrsn0) hnot0 a ha
    have hq_lvl : (ks.lvlArr[(ks.trl[q]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
        ks'.lvl.toNat :=
      Nat.le_trans (hinv.assign.trl_lvl_mono q p0 (Nat.le_of_lt hqp) hp0) hle0
    obtain ⟨_, hq_trl, _⟩ := hkept_below q (Nat.lt_trans hqp hp0) hq_lvl
    refine ⟨q, hqp, ?_⟩
    rw [hq_trl]; exact hqa
  exact ⟨hinv', hsync', e_inc.trans hinc, e_fail.trans hfail, hframe', hlvlne', hlate',
    by decide, fun h => absurd rfl h⟩

/-! ## 2. Additional `solve` Helpers (`lvl = 0`, `assump`, `pick`, & Exit Packaging) -/

/-- At level `0`, `Inv` + `Synced` automatically give `KittenLvlNonempty` and
`KittenFreeDecLate`. -/
theorem solveLoopInv_of_lvl0 {acap : Nat} {ks0 ks : KittenState}
    (hinv : ks.Inv acap) (hsync : KittenTrailSynced ks)
    (hlvl0 : ks.lvl = 0#32) (hinc : ks.incons = 0xFFFFFFFF#32)
    (hfail : ks.failing = 0xFFFFFFFF#32) (hframe : SolveFrame ks0 ks) :
    SolveLoopInv acap ks0 ks 0xFFFFFFFF#32 :=
  ⟨hinv, hsync, hinc, hfail, hframe,
   fun L hL0 hLle => by rw [hlvl0] at hLle; simp at hLle; omega,
   fun p hp hrsn => by
     exfalso
     have hnv := hinv.clauses.nv_le
     have htrl_len : ks.trl_end.toNat ≤ ks.trl.length := by
       rw [hinv.shapes.trl_len]; have := hinv.assign.trl_end_le; unfold kMaxV at hnv; omega
     have hlp := hinv.assign.trl_lt _ (mem_kittenTrailLits_of_lt hp htrl_len)
     have hle := hinv.assign.trl_lvl_le ((ks.trl[p]?.getD 0#32).toNat / 2) (by omega)
     rw [hlvl0] at hle
     have hl0 : ks.lvlArr[(ks.trl[p]?.getD 0#32).toNat / 2]?.getD 0#32 = 0#32 :=
       BitVec.eq_of_toNat_eq (Nat.eq_zero_of_le_zero hle)
     exact (hinv.assign.lvl0_ok p hp hl0).1 hrsn,
   by decide, fun h => absurd rfl h⟩

private theorem mem_kittenAssumpLits_of_lt {ks : KittenState}
    (hlen : ks.nassump.toNat ≤ ks.assump.length) {i : Nat} (hi : i < ks.nassump.toNat) :
    (ks.assump[i]?.getD 0#32).toNat ∈ kittenAssumpLits ks := by
  unfold kittenAssumpLits
  rw [List.mem_map]
  refine ⟨ks.assump[i]?.getD 0#32, ?_, rfl⟩
  rw [List.mem_take_iff_getElem]
  exact ⟨i, by omega, by simp [List.getElem?_eq_getElem (by omega : i < ks.assump.length)]⟩

private theorem bv32_shl1_or_bit_toNat {pick ph : BitVec 32} {nv : Nat}
    (hp : pick.toNat < nv) (hnv : nv ≤ kMaxV) (hph : ph.toNat < 2) :
    ((pick <<< (1 : Nat)) ||| ph).toNat = 2 * pick.toNat + ph.toNat ∧
    ((pick <<< (1 : Nat)) ||| ph).toNat < 2 * nv := by
  unfold kMaxV at hnv
  have h1 : (pick <<< (1 : Nat)).toNat = 2 * pick.toNat := by
    rw [BitVec.toNat_shiftLeft]; simp; omega
  have h2 : ((pick <<< (1 : Nat)) ||| ph).toNat = 2 * pick.toNat + ph.toNat := by
    rcases (by omega : ph.toNat = 0 ∨ ph.toNat = 1) with hz | ho
    · have : ph = 0#32 := BitVec.eq_of_toNat_eq hz; subst this; simp [h1]
    · have : ph = 1#32 := BitVec.eq_of_toNat_eq ho; subst this
      rw [BitVec.toNat_or, h1]
      have h132 : (1#32).toNat = 1 := by decide
      rw [h132]
      have heq : 2 ^ 1 * pick.toNat + 1 = (2 ^ 1 * pick.toNat) ||| 1 :=
        Nat.two_pow_add_eq_or_of_lt (by decide : 1 < 2 ^ 1) pick.toNat
      rw [show 2 * pick.toNat = 2 ^ 1 * pick.toNat by omega, ← heq]
  exact ⟨h2, by omega⟩

private theorem solve_post_finish {c : FullCfg} {s : FullState} {scr : List (BitVec 32)}
    {ks0 ks' : KittenState} {fuel' r : BitVec 64} {R : Mem 64 → Prop} {m' : Mem 64}
    {Q : Post [i64]}
    (hlen : s.LengthsOk c) (h256 : 256 ≤ scr.length) (hscr_len : scr.length = c.scratch_cap)
    (hscr_ge : kMinScratchCap ≤ scr.length) (hof_ks0 : kittenStateOfScratch scr = ks0)
    (hinv' : ks'.Inv (scr.length - 8864)) (hfuel : fuel'.toNat ≤ s.core.fuel.toNat)
    (e_nv : ks'.nv = ks0.nv) (e_on : ks'.orig_nc = ks0.orig_nc) (e_ant : ks'.ante = ks0.ante)
    (e_na : ks'.nassump = ks0.nassump) (e_ass : ks'.assump = ks0.assump)
    (hperm : KittenCnfPermEquiv (kittenOrigClauses ks') (kittenOrigClauses ks0))
    (hclAux : ∀ ci < ks0.orig_nc.toNat, ks'.clAux[ci]? = ks0.clAux[ci]?)
    (hcore : r ≠ 20#64 → ∀ ci < ks0.orig_nc.toNat,
      (ks'.clMeta[ci]?.getD 0#32 &&& kmCore) = (ks0.clMeta[ci]?.getD 0#32 &&& kmCore))
    (hr : r = 0#64 ∨ r = 10#64 ∨ r = 20#64)
    (hr20 : r = 20#64 →
      (ks'.incons ≠ 0xFFFFFFFF#32 ∨ ks'.failing ≠ 0xFFFFFFFF#32) ∧
      (cnfOfClauses (kittenOrigClauses ks') ++ unitsCnf (kittenAssumpLits ks')).Unsat)
    (hm' : (FullKittenFrame c { s with core := { s.core with fuel := fuel' } } ⋆
      KittenMem (c.pScratchBuf + 1024#64) ks' ⋆ R) m')
    (hQ : ∀ (r fuel' : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState :=
        { s with core := { s.core with fuel := fuel' }
                 scratch := { s.scratch with scratch_buf := scr' } }
      let ks := kittenStateOfScratch s.scratch.scratch_buf
      let ks' := kittenStateOfScratch scr'
      s'.LengthsOk c → fuel'.toNat ≤ s.core.fuel.toNat →
      (∀ i < kBase, scr'[i]? = s.scratch.scratch_buf[i]?) →
      KittenScratchInv scr' →
      ks'.nv = ks.nv → ks'.orig_nc = ks.orig_nc → ks'.ante = ks.ante →
      ks'.nassump = ks.nassump →
      kittenAssumpLitsS scr' = kittenAssumpLitsS s.scratch.scratch_buf →
      KittenCnfPermEquiv (kittenOrigClausesS scr') (kittenOrigClausesS s.scratch.scratch_buf) →
      (∀ ci < ks.orig_nc.toNat, ks'.clAux[ci]? = ks.clAux[ci]?) →
      (r ≠ 20#64 → ∀ ci < ks.orig_nc.toNat,
        (ks'.clMeta[ci]?.getD 0#32 &&& kmCore) = (ks.clMeta[ci]?.getD 0#32 &&& kmCore)) →
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
      (r = 20#64 →
        (ks'.incons ≠ 0xFFFFFFFF#32 ∨ ks'.failing ≠ 0xFFFFFFFF#32) ∧
        (cnfOfClauses (kittenOrigClausesS scr') ++ unitsCnf (kittenAssumpLitsS scr')).Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hscr_eq : s.scratch.scratch_buf = scr) :
    Q (r, ()) m' := by
  let sFuel : FullState := { s with core := { s.core with fuel := fuel' } }
  let scr' := scr.take 256 ++ ks'.toSlab
  have hsh' := hinv'.shapes
  have htk_len : (scr.take 256).length = 256 := List.length_take_of_le h256
  have hscr'_len : scr'.length = c.scratch_cap := by
    simp only [scr', List.length_append, htk_len, KittenState.toSlab_length hsh']
    unfold kMinScratchCap at hscr_ge
    omega
  have hpre : ∀ i < kBase, scr'[i]? = s.scratch.scratch_buf[i]? := by
    intro i hi
    rw [hscr_eq, List.getElem?_append_left (by unfold kBase at hi; omega),
      List.getElem?_take_of_lt (by unfold kBase at hi; omega)]
  have hof' : kittenStateOfScratch scr' = ks' := by
    unfold kittenStateOfScratch
    rw [show scr' = scr.take 256 ++ ks'.toSlab from rfl, slab_drop_exact _ ks'.toSlab htk_len]
    exact KittenState.ofSlab_toSlab hsh'
  have hks_inv' : KittenScratchInv scr' := by
    refine ⟨by rw [hscr'_len, ← hscr_len]; exact hscr_ge,
      by rw [hscr'_len]; exact c.hscr, ?_⟩
    rw [hof', hscr'_len, ← hscr_len]
    exact hinv'
  have hlen_f : sFuel.LengthsOk c :=
    ⟨{ hlen.core_ok with vals_len := hlen.core_ok.vals_len }, hlen.scratch_ok⟩
  have hlen' : FullState.LengthsOk c
      { sFuel with scratch := { s.scratch with scratch_buf := scr' } } :=
    fullState_lengthsOk_scratch hlen_f (by rw [hscr'_len])
  have hm_join := fullMem_join_kitten (c := c) (s := sFuel) (acap := scr.length - 8864)
    (ks' := ks') (R := R)
    (by change 256 ≤ sFuel.scratch.scratch_buf.length; rw [hscr_eq]; exact h256)
    hsh' hm'
  refine hQ r fuel' scr' m' hlen' hfuel hpre hks_inv'
    (by rw [hof', hscr_eq, hof_ks0]; exact e_nv)
    (by rw [hof', hscr_eq, hof_ks0]; exact e_on)
    (by rw [hof', hscr_eq, hof_ks0]; exact e_ant)
    (by rw [hof', hscr_eq, hof_ks0]; exact e_na)
    (by unfold kittenAssumpLitsS kittenAssumpLits
        rw [hof', hscr_eq, hof_ks0, e_na, e_ass])
    (by unfold kittenOrigClausesS; rw [hof', hscr_eq, hof_ks0]; exact hperm)
    (by rw [hof', hscr_eq, hof_ks0]; exact hclAux)
    (fun hne => by rw [hof', hscr_eq, hof_ks0]; exact hcore hne)
    hr
    (fun h20 => by
      unfold kittenOrigClausesS kittenAssumpLitsS
      rw [hof']
      exact hr20 h20)
    (by simpa [sFuel, scr', hscr_eq] using hm_join)

/-! ## 3. Parametric `Func.wp` Proof for `full_kitten_solve` (`[15/15]`) -/

local macro "c0_hcall" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-- Parametric `Func.wp` proof for `full_kitten_solve`. -/
theorem full_kitten_solve_wp (Γ : Env)
    (hBt : ∀ args m Q X, fullKittenBacktrackSpec args m Q X →
      Γ "full_kitten_backtrack" [i64, i32] [] args m Q X)
    (hAsg : ∀ args m Q X, fullKittenAssignSpec args m Q X →
      Γ "full_kitten_assign" [i64, i32, i32] [] args m Q X)
    (hProp : ∀ args m Q X, fullKittenPropagateSpec args m Q X →
      Γ "full_kitten_propagate" [i64] [i32] args m Q X)
    (hAna : ∀ args m Q X, fullKittenAnalyzeSpec args m Q X →
      Γ "full_kitten_analyze" [i64, i32] [.bool] args m Q X)
    (hBf : ∀ args m Q X, fullKittenBuildFailingSpec args m Q X →
      Γ "full_kitten_build_failing" [i64, i32] [] args m Q X) :
    ∀ args m Q X, fullKittenSolveSpec args m Q X →
      Func.wp Γ full_kitten_solve_body args m Q X := by
  rintro ⟨hPtr, tick_lim, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hscr_inv, hm, hQ⟩
  rcases hscr_inv with ⟨hscr_ge, hscr_lt, hinv0⟩
  let scr := s.scratch.scratch_buf
  let acap := scr.length - 8864
  let ks0 := kittenStateOfScratch scr
  have hscr_len : scr.length = c.scratch_cap := hlen.scratch_ok.scratch_buf_len
  have hscr_8864 : 8864 ≤ scr.length := by
    dsimp only [scr]; unfold kMinScratchCap at hscr_ge; omega
  have h256 : 256 ≤ scr.length := by omega
  let kPtr := c.pScratchBuf + BitVec.ofNat 64 256 * 4
  have hkPtr_eq : kPtr = c.pScratchBuf + 1024#64 := kPtr_base_eq c.pScratchBuf
  have hmF0 : (FullKittenFrame c s ⋆ KittenMem kPtr ks0 ⋆ R) m := by
    rw [fullMem_eq_kittenFrame hscr_8864] at hm
    rw [hkPtr_eq]
    exact sep_ac hm
  clear hm
  c0_hsteps_nogrp
  c0_hcall hBt
  · refine ⟨acap, ks0, FullKittenFrame c s ⋆ R, hinv0, fun i hi hle => ?_, ?_, ?_⟩
    · have hl0 : ks0.lvlArr[(ks0.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 = 0#32 :=
        BitVec.eq_of_toNat_eq (Nat.eq_zero_of_le_zero hle)
      have h0 := hinv0.assign.lvl0_ok i hi hl0
      exact ⟨h0.2.1, h0.2.2.1⟩
    · exact sep_ac hmF0
    · intro ks1 m1 hinv1 hsync1 hlvl1 _ _ hbt1 _ _ hm1
      have hframe1 : SolveFrame ks0 ks1 :=
        ⟨hbt1.nv, hbt1.orig_nc, hbt1.ante, hbt1.nassump, hbt1.assump, by
          rw [kittenOrigClauses_eq_of hbt1.orig_nc fun ci _ => by
            simp [kittenClauseLits, kittenClauseOff, kittenClauseSize, kittenClauseMeta,
              hbt1.clOff, hbt1.clMeta, hbt1.arena]]
          exact KittenCnfPermEquiv.refl _,
         fun ci _ => by rw [hbt1.clAux],
         fun ci _ => by rw [hbt1.clMeta]⟩
      have hmA1 : (KittenMemA kPtr acap ks1 ⋆ (FullKittenFrame c s ⋆ R)) m1 :=
        kittenMem_to_amem hinv1.shapes (sep_ac hm1)
      clear hm1
      c0_hsplit
      · have hinc1 : ks1.incons ≠ 0xFFFFFFFF#32 := ‹_›
        c0_hsteps!
        obtain ⟨_, hmFin1⟩ := kittenMemA_to_mem hmA1
        have huns1 := cnfOfClauses_unsat_append_left (unitsCnf (kittenAssumpLits ks1))
          (hinv1.clauses.incons_ok hinc1).2.1
        refine solve_post_finish hlen h256 hscr_len hscr_ge rfl hinv1 (le_refl _)
          hframe1.nv hframe1.orig_nc hframe1.ante hframe1.nassump hframe1.assump
          hframe1.perm hframe1.clAux (fun _ => hframe1.core) (Or.inr (Or.inr rfl))
          (fun _ => ⟨Or.inl hinc1, huns1⟩) ?_ hQ rfl
        rw [← hkPtr_eq]; exact sep_ac hmFin1
      · have hinc1 : ks1.incons = 0xFFFFFFFF#32 := by
          first | exact ‹_› | exact Classical.not_not.mp ‹_›
        c0_hsteps_nogrp
        let ks2 := (ks1.putHdr .tick_lim
          (ks1.ticks + BitVec.setWidth 32 tick_lim)).putHdr .failing 0xFFFFFFFF#32
        have hinv2 : ks2.Inv acap := inv_set_failing_none (inv_set_tick_lim hinv1 _)
        have hsync2 : KittenTrailSynced ks2 := hsync1
        have hframe2 : SolveFrame ks0 ks2 := SolveFrame.trans hframe1
          ⟨rfl, rfl, rfl, rfl, rfl, KittenCnfPermEquiv.refl _, fun _ _ => rfl, fun _ _ => rfl⟩
        refine wp_while_state1 (fun p : BitVec 32 × KittenState => p.1)
          (fun p => p.2.nunits.toNat - p.1.toNat)
          (fun p m' => p.1.toNat ≤ p.2.nunits.toNat ∧ p.2.Inv acap ∧
            KittenTrailSynced p.2 ∧ p.2.lvl = 0#32 ∧ p.2.incons = 0xFFFFFFFF#32 ∧
            p.2.failing = 0xFFFFFFFF#32 ∧ SolveFrame ks0 p.2 ∧
            (KittenMemA kPtr acap p.2 ⋆ (FullKittenFrame c s ⋆ R)) m')
          ?_ ?_
        · intro J hJ
          exact wp_jump_state (proj := fun p : BitVec 32 × KittenState => (p.1, ()))
            (0#32, ks2) rfl
            (hJ _ _ ⟨by simp, hinv2, hsync2, by dsimp only [ks2]; kp_field; exact hlvl1,
              by dsimp only [ks2]; kp_field; exact hinc1, rfl, hframe2, hm⟩)
        · rintro J ⟨ui, ku⟩ m' ⟨hui_le, hinv_u, hsync_u, hlvl_u, hinc_u, hfail_u,
              hframe_u, hm_u⟩ ih_u
          try clear hm
          dsimp only at hui_le hinv_u hsync_u hlvl_u hinc_u hfail_u hframe_u hm_u
          have hnv_u := hinv_u.clauses.nv_le
          have hal_u := hinv_u.clauses.alen_le
          have hnu_le := hinv_u.clauses.nunits_le
          have hacap_lt := hinv_u.clauses.acap_lt
          c0_hsplit
          · have hui_lt : ui.toNat < ku.nunits.toNat := by bv_omega
            have hui_wrap : ui.toNat < 2 ^ 28 := by unfold kMaxL at hnu_le; omega
            have hui_256 : ui.toNat < 256 := by unfold kMaxL at hnu_le; omega
            have hui1_nat : (ui + 1#32).toNat = ui.toNat + 1 := by
              unfold kMaxL at hnu_le; bv_omega
            let ucid := ku.units[ui.toNat]?.getD 0#32
            have hucid_ok := hinv_u.clauses.units_ok ui.toNat hui_lt
            dsimp only at hucid_ok
            have hnc_u := hinv_u.clauses.nc_le
            have hucid_lt : ucid.toNat < ku.nc.toNat := hucid_ok.1
            have hucid_wrap : ucid.toNat < 2 ^ 28 := by unfold kMaxCl at hnc_u; omega
            have hucid_896 : ucid.toNat < 896 := by unfold kMaxCl at hnc_u; omega
            have hucid_wrap' : (ku.units[ui.toNat]?.getD 0#32).toNat < 2 ^ 28 := hucid_wrap
            have hucid_896' : (ku.units[ui.toNat]?.getD 0#32).toNat < 896 := hucid_896
            have hwf_u := hinv_u.clauses.cl_wf ucid.toNat hucid_ok.1
            have hoff_lt : kittenClauseOff ku ucid.toNat < acap := by
              have hsp1 : 1 ≤ kittenClauseSpan ku ucid.toNat := by
                unfold kittenClauseSpan; rw [hucid_ok.2]; omega
              omega
            have hoff_wrap : kittenClauseOff ku ucid.toNat < 2 ^ 28 := by
              unfold dimacsBound at hacap_lt; omega
            have hoff_lt' : (ku.clOff[(ku.units[ui.toNat]?.getD 0#32).toNat]?.getD 0#32).toNat <
                acap := hoff_lt
            have hoff_wrap' : (ku.clOff[(ku.units[ui.toNat]?.getD 0#32).toNat]?.getD 0#32).toNat <
                2 ^ 28 := hoff_wrap
            let ul := ku.arena[kittenClauseOff ku ucid.toNat]?.getD 0#32
            have hlits_u : kittenClauseLits ku ucid.toNat = [ul.toNat] := by
              unfold kittenClauseLits
              rw [hucid_ok.2]
              have hlen_ar : ku.arena.length = acap := hinv_u.shapes.arena_len
              have hdrop : ku.arena.drop (kittenClauseOff ku ucid.toNat) =
                  ku.arena[kittenClauseOff ku ucid.toNat]'(by omega) ::
                    ku.arena.drop (kittenClauseOff ku ucid.toNat + 1) :=
                List.drop_eq_getElem_cons (by omega)
              rw [hdrop, List.take_succ_cons, List.take_zero, List.map_singleton]
              simp [ul, List.getElem?_eq_getElem (by omega : kittenClauseOff ku ucid.toNat <
                ku.arena.length)]
            have hul_lt : ul.toNat < 2 * ku.nv.toNat :=
              hwf_u.2.2.2.1 ul.toNat (by rw [hlits_u]; simp)
            have hul_wrap : ul.toNat < 2 ^ 28 := by unfold kMaxV at hnv_u; omega
            have hul_256 : ul.toNat < 256 := by unfold kMaxV at hnv_u; omega
            have hul_wrap' : (ku.arena[(ku.clOff[(ku.units[ui.toNat]?.getD
                0#32).toNat]?.getD 0#32).toNat]?.getD 0#32).toNat < 2 ^ 28 := hul_wrap
            have hul_256' : (ku.arena[(ku.clOff[(ku.units[ui.toNat]?.getD
                0#32).toNat]?.getD 0#32).toNat]?.getD 0#32).toNat < 256 := hul_256
            c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
            c0_hstep; c0_hstep; c0_hstep; c0_hstep; c0_hstep
            c0_hstep; c0_hstep; c0_hstep; c0_hstep
            refine head_wp_load rfl (KittenMemATactics.load_ka_arena hoff_wrap' hoff_lt' hm_u) ?_
            c0_hsplit
            · have huv2 : ku.vals[ul.toNat]?.getD 0#32 = 2#32 := ‹_›
              have huv2' : ku.vals[ul.toNat]? = some 2#32 := by
                have hl : ul.toNat < ku.vals.length := by rw [hinv_u.shapes.vals_len]; exact hul_256
                rw [List.getElem?_eq_getElem hl, Option.getD_some] at huv2
                rw [List.getElem?_eq_getElem hl, huv2]
              c0_hsteps!
              have hinc_ucid : ucid ≠ 0xFFFFFFFF#32 := by
                intro h; have := congrArg BitVec.toNat h
                change ucid.toNat = 2 ^ 32 - 1 at this; omega
              have hfals_u : ∀ l ∈ kittenClauseLits ku ucid.toNat, ku.vals[l]? = some 2#32 := by
                intro l hl; rw [hlits_u] at hl; simp at hl; subst hl; exact huv2'
              have ⟨hinv_i, _⟩ := inv_set_incons_lvl0 hinv_u hsync_u hlvl_u hucid_ok.1 hfals_u
              have huns_i := cnfOfClauses_unsat_append_left (unitsCnf (kittenAssumpLits (ku.putHdr
                .incons ucid))) (hinv_i.clauses.incons_ok hinc_ucid).2.1
              have hframe_i : SolveFrame ks0 (ku.putHdr .incons ucid) := SolveFrame.trans hframe_u
                ⟨rfl, rfl, rfl, rfl, rfl, KittenCnfPermEquiv.refl _, fun _ _ => rfl,
                 fun _ _ => rfl⟩
              obtain ⟨_, hmFin_i⟩ := kittenMemA_to_mem hm
              refine solve_post_finish hlen h256 hscr_len hscr_ge rfl hinv_i (le_refl _)
                hframe_i.nv hframe_i.orig_nc hframe_i.ante hframe_i.nassump hframe_i.assump
                hframe_i.perm hframe_i.clAux (fun _ => hframe_i.core) (Or.inr (Or.inr rfl))
                (fun _ => ⟨Or.inl hinc_ucid, huns_i⟩) ?_ hQ rfl
              rw [← hkPtr_eq]; exact sep_ac hmFin_i
            · refine wp_join0 (fun m_j => ∃ ku' : KittenState,
                  ku'.nunits = ku.nunits ∧ ku'.Inv acap ∧ KittenTrailSynced ku' ∧
                  ku'.lvl = 0#32 ∧ ku'.incons = 0xFFFFFFFF#32 ∧
                  ku'.failing = 0xFFFFFFFF#32 ∧ SolveFrame ks0 ku' ∧
                  (KittenMemA kPtr acap ku' ⋆ (FullKittenFrame c s ⋆ R)) m_j) ?_ ?_
              · intro Js m_j ⟨ku', hnu', hinv', hsync', hlvl', hinc', hfail', hframe', hm'⟩
                c0_hsteps!
                exact ih_u (ui + 1#32, ku') m_j (by dsimp only; rw [hnu', hui1_nat]; omega)
                  ⟨by dsimp only; rw [hnu', hui1_nat]; exact hui_lt, hinv', hsync', hlvl', hinc',
                   hfail', hframe', hm'⟩
              · intro Js hJs
                c0_hsplit
                · have huv0 : ku.vals[ul.toNat]?.getD 0#32 = 0#32 := ‹_›
                  have hun0 := vals_some_zero_of_getD hinv_u hul_lt huv0
                  have hte_lt := trl_end_lt_nv_of_unassigned hinv_u hul_lt huv0
                  c0_hcall hAsg
                  · obtain ⟨_, hm_asg⟩ := kittenMemA_to_mem hm_u
                    exact ⟨acap, ku, FullKittenFrame c s ⋆ R, hinv_u.shapes, hacap_lt, hnv_u,
                      hul_lt, hte_lt, hm_asg, fun mA hmA => by
                        c0_hsteps!
                        have hucid_ne : ucid ≠ 0xFFFFFFFF#32 := by
                          intro h; have := congrArg BitVec.toNat h
                          change ucid.toNat = 2 ^ 32 - 1 at this; omega
                        have hent_ul : (cnfOfClauses (kittenOrigClauses ku)).EntailsClause
                            (cnfClause [ul.toNat]) := by
                          simpa [hlits_u] using hwf_u.2.2.2.2.1
                        obtain ⟨hinv_a, hsync_a⟩ := kittenAssignStep_preserves_inv hinv_u hsync_u
                          hinc_u hul_lt hun0
                          (fun _ => ⟨hucid_ne, hent_ul, fun _ => ⟨hucid_ok.1, hlits_u⟩⟩)
                          (fun h => absurd h hucid_ne)
                          (Or.inr ⟨hucid_ok.1, by simp [hlits_u], fun x hx hxl => by
                            simp [hlits_u] at hx; exact absurd hx hxl⟩)
                        have hframe_a : SolveFrame ks0 (kittenAssignStep ku ul ucid) :=
                          SolveFrame.trans hframe_u ⟨rfl, rfl, rfl, rfl, rfl,
                            KittenCnfPermEquiv.refl _, fun _ _ => rfl, fun _ _ => rfl⟩
                        exact hJs _ ⟨kittenAssignStep ku ul ucid, rfl, hinv_a, hsync_a, hlvl_u,
                          hinc_u, hfail_u, hframe_a, kittenMem_to_amem hinv_a.shapes hmA⟩⟩
                · c0_hsteps!
                  exact hJs _ ⟨ku, rfl, hinv_u, hsync_u, hlvl_u, hinc_u, hfail_u, hframe_u,
                    hm_u⟩
          · obtain ⟨_, hm_p0⟩ := kittenMemA_to_mem hm_u
            c0_hcall hProp
            · refine ⟨acap, ku, FullKittenFrame c s ⋆ R, hinv_u, hsync_u, hm_p0,
                fun confl_p ks_p m_p hinv_p hsync_p e_nv e_on e_lvl e_inc e_fail e_ant e_na e_ass
                  hperm hclAux hcore hdec hte_le htrl_kept hconfl_ff hconfl_ne hm_p => ?_⟩
              have hm_p' : (KittenMem kPtr ks_p ⋆ (FullKittenFrame c s ⋆ R)) m_p := hm_p
              clear hm_p
              c0_hsplit
              · have hc_fe : confl_p = 0xFFFFFFFE#32 := ‹_›
                c0_hsteps!
                have hframe_p : SolveFrame ks0 ks_p := SolveFrame.trans hframe_u
                  ⟨e_nv, e_on, e_ant, e_na, e_ass, hperm, hclAux, hcore⟩
                refine solve_post_finish hlen h256 hscr_len hscr_ge rfl hinv_p (le_refl _)
                  hframe_p.nv hframe_p.orig_nc hframe_p.ante hframe_p.nassump hframe_p.assump
                  hframe_p.perm hframe_p.clAux (fun _ => hframe_p.core) (Or.inl rfl)
                  (fun h => absurd h (by decide)) ?_ hQ rfl
                rw [← hkPtr_eq]; exact sep_ac hm_p'
              · have hc_ne_fe : confl_p ≠ 0xFFFFFFFE#32 := ‹_›
                c0_hsplit
                · have hc_ne_ff : confl_p ≠ 0xFFFFFFFF#32 := ‹_›
                  have hmA_p : (KittenMemA kPtr acap ks_p ⋆ (FullKittenFrame c s ⋆ R)) m_p :=
                    kittenMem_to_amem hinv_p.shapes hm_p'
                  clear hm_p'
                  c0_hsteps!
                  obtain ⟨hc_lt, hc_fals⟩ := hconfl_ne hc_ne_ff hc_ne_fe
                  have ⟨hinv_i, _⟩ := inv_set_incons_lvl0 hinv_p hsync_p (e_lvl.trans hlvl_u)
                    hc_lt hc_fals
                  have huns_i := cnfOfClauses_unsat_append_left
                    (unitsCnf (kittenAssumpLits (ks_p.putHdr .incons confl_p)))
                    (hinv_i.clauses.incons_ok hc_ne_ff).2.1
                  have hframe_p : SolveFrame ks0 (ks_p.putHdr .incons confl_p) :=
                    SolveFrame.trans hframe_u ⟨e_nv, e_on, e_ant, e_na, e_ass, hperm, hclAux, hcore⟩
                  obtain ⟨_, hmFin_i⟩ := kittenMemA_to_mem hm
                  refine solve_post_finish hlen h256 hscr_len hscr_ge rfl hinv_i (le_refl _)
                    hframe_p.nv hframe_p.orig_nc hframe_p.ante hframe_p.nassump hframe_p.assump
                    hframe_p.perm hframe_p.clAux (fun _ => hframe_p.core) (Or.inr (Or.inr rfl))
                    (fun _ => ⟨Or.inl hc_ne_ff, huns_i⟩) ?_ hQ rfl
                  rw [← hkPtr_eq]; exact sep_ac hmFin_i
                · have hc_ff : confl_p = 0xFFFFFFFF#32 := by
                    first | exact ‹_› | exact Classical.not_not.mp ‹_›
                  have hframe_p : SolveFrame ks0 ks_p := SolveFrame.trans hframe_u
                    ⟨e_nv, e_on, e_ant, e_na, e_ass, hperm, hclAux, hcore⟩
                  have hsi_p : SolveLoopInv acap ks0 ks_p 0xFFFFFFFF#32 :=
                    solveLoopInv_of_lvl0 hinv_p hsync_p (e_lvl.trans hlvl_u)
                      (e_inc.trans hinc_u) (e_fail.trans hfail_u) hframe_p
                  refine wp_while_state1
                    (fun st : BitVec 32 × KittenState × BitVec 64 => st.1)
                    (fun st => st.2.2.toNat)
                    (fun st m_l => st.2.2.toNat ≤ s.core.fuel.toNat ∧
                      SolveLoopInv acap ks0 st.2.1 st.1 ∧
                      (KittenMemA kPtr acap st.2.1 ⋆
                        (FullKittenFrame c { s with core := { s.core with fuel := st.2.2 } } ⋆
                          R)) m_l)
                    ?_ ?_
                  · intro Jm hJm
                    c0_hsteps!
                    rw [hc_ff]
                    exact hJm (0xFFFFFFFF#32, ks_p, s.core.fuel) m_p
                      ⟨le_refl _, hsi_p, kittenMem_to_amem hinv_p.shapes hm_p'⟩
                  · rintro Jm ⟨confl_m, km, fuel_m⟩ m_l ⟨hfuel_m, hsi_m, hm_l⟩ ih_m
                    dsimp only at hfuel_m hsi_m hm_l
                    c0_hsplit
                    · have htk_le : km.ticks.toNat ≤ km.tick_lim.toNat := by bv_omega
                      c0_hsplit
                      · have hfuel_pos : 0 < fuel_m.toNat := by bv_omega
                        have hfuel_sub : (fuel_m - 1#64).toNat = fuel_m.toNat - 1 := by bv_omega
                        let sFuel1 : FullState :=
                          { s with core := { s.core with fuel := fuel_m - 1#64 } }
                        have hfuel_le1 : (fuel_m - 1#64).toNat ≤ s.core.fuel.toNat := by omega
                        c0_hsplit
                        · have hconfl_ne : confl_m ≠ 0xFFFFFFFF#32 := ‹_›
                          have hm_l1 : (KittenMemA kPtr acap km ⋆
                              (FullKittenFrame c sFuel1 ⋆ R)) m := by
                            simpa only [sFuel1] using sep_ac hm
                          clear hm
                          c0_hsplit
                          · have hlvl0_m : km.lvl = 0#32 := ‹_›
                            c0_hsteps!
                            obtain ⟨hc_lt, hc_fals⟩ := hsi_m.confl_ok hconfl_ne
                            have ⟨hinv_i, _⟩ := inv_set_incons_lvl0 hsi_m.inv hsi_m.sync hlvl0_m
                              hc_lt hc_fals
                            have huns_i := cnfOfClauses_unsat_append_left
                              (unitsCnf (kittenAssumpLits (km.putHdr .incons confl_m)))
                              (hinv_i.clauses.incons_ok hconfl_ne).2.1
                            have hframe_i : SolveFrame ks0 (km.putHdr .incons confl_m) :=
                              SolveFrame.trans hsi_m.frame ⟨rfl, rfl, rfl, rfl, rfl,
                                KittenCnfPermEquiv.refl _, fun _ _ => rfl, fun _ _ => rfl⟩
                            obtain ⟨_, hmFin_i⟩ := kittenMemA_to_mem hm
                            refine solve_post_finish hlen h256 hscr_len hscr_ge rfl hinv_i
                              hfuel_le1 hframe_i.nv hframe_i.orig_nc hframe_i.ante hframe_i.nassump
                              hframe_i.assump hframe_i.perm hframe_i.clAux (fun _ => hframe_i.core)
                              (Or.inr (Or.inr rfl)) (fun _ => ⟨Or.inl hconfl_ne, huns_i⟩) ?_ hQ rfl
                            rw [← hkPtr_eq]; exact sep_ac hmFin_i
                          · have hlvl_pos : 0 < km.lvl.toNat := by bv_omega
                            obtain ⟨hc_lt, hc_fals⟩ := hsi_m.confl_ok hconfl_ne
                            obtain ⟨iw, hiw, hiw_lvl⟩ := hsi_m.lvlne km.lvl.toNat hlvl_pos
                              (le_refl _)
                            have hiw_lvl_bv : km.lvlArr[(km.trl[iw]?.getD 0#32).toNat / 2]?.getD
                                0#32 = km.lvl := by
                              apply BitVec.eq_of_toNat_eq; exact hiw_lvl
                            obtain ⟨_, hm_a0⟩ := kittenMemA_to_mem hm_l1
                            c0_hcall hAna
                            · refine ⟨acap, km, FullKittenFrame c sFuel1 ⋆ R, hsi_m.inv, hsi_m.sync,
                                hlvl_pos, ⟨iw, hiw, hiw_lvl_bv⟩, hc_lt, hc_fals, hm_a0,
                                fun ok_a ks_a m_a hinv_a e_nv e_on e_ant e_na e_ass e_inc e_fail
                                  horig_a hclAux_a hcore_a hok_a hm_a => ?_⟩
                              c0_hsplit
                              · have hok_t : ok_a = true := by
                                  cases ok_a <;> simp_all
                                obtain ⟨hsync_a, hlvl_lt, _, hdec_sub, hkept⟩ := hok_a hok_t
                                have hsi_a := solveLoopInv_of_analyze hsi_m.inv hsi_m.incons
                                  hsi_m.failing hsi_m.frame hsi_m.lvlne hsi_m.late hinv_a hsync_a
                                  e_nv e_on e_ant e_na e_ass e_inc e_fail horig_a hclAux_a hcore_a
                                  hlvl_lt hdec_sub hkept
                                c0_hcall hProp
                                · refine ⟨acap, ks_a, FullKittenFrame c sFuel1 ⋆ R, hsi_a.inv,
                                    hsi_a.sync, hm_a,
                                    fun confl_p2 ks_p2 m_p2 hinv_p2 hsync_p2 p_nv p_on p_lvl p_inc
                                      p_fail p_ant p_na p_ass p_perm p_clAux p_core p_te_le p_dec
                                      p_trl p_ff p_ne hm_p2 => ?_⟩
                                  c0_hsplit
                                  · have : confl_p2 = 0xFFFFFFFE#32 := ‹_›
                                    c0_hsteps!
                                    have hframe_p2 : SolveFrame ks0 ks_p2 :=
                                      SolveFrame.trans hsi_a.frame
                                        ⟨p_nv, p_on, p_ant, p_na, p_ass, p_perm, p_clAux, p_core⟩
                                    refine solve_post_finish hlen h256 hscr_len hscr_ge rfl hinv_p2
                                      hfuel_le1 hframe_p2.nv hframe_p2.orig_nc hframe_p2.ante
                                      hframe_p2.nassump hframe_p2.assump hframe_p2.perm
                                      hframe_p2.clAux (fun _ => hframe_p2.core) (Or.inl rfl)
                                      (fun h => absurd h (by decide)) ?_ hQ rfl
                                    rw [← hkPtr_eq]; exact sep_ac hm_p2
                                  · have hc_ne2 : confl_p2 ≠ 0xFFFFFFFE#32 := ‹_›
                                    have hsi_p2 := solveLoopInv_of_propagate hsi_a.inv hsi_a.incons
                                      hsi_a.failing hsi_a.frame hsi_a.lvlne hsi_a.late hinv_p2
                                      hsync_p2 p_nv p_on p_lvl p_inc p_fail p_ant p_na p_ass p_perm
                                      p_clAux p_core p_dec p_te_le p_trl hc_ne2 (p_ne · hc_ne2)
                                    c0_hsteps!
                                    exact ih_m (confl_p2, ks_p2, fuel_m - 1#64) _
                                      (by dsimp only; omega)
                                      ⟨hfuel_le1, hsi_p2, kittenMem_to_amem hinv_p2.shapes hm_p2⟩
                              · have hok_f : ok_a = false := by
                                  cases ok_a <;> simp_all
                                c0_hsteps!
                                have hperm_a : KittenCnfPermEquiv (kittenOrigClauses ks_a)
                                    (kittenOrigClauses km) := by
                                  rw [horig_a]; exact KittenCnfPermEquiv.refl _
                                have hframe_a : SolveFrame ks0 ks_a := SolveFrame.trans hsi_m.frame
                                  ⟨e_nv, e_on, e_ant, e_na, e_ass, hperm_a, hclAux_a, hcore_a⟩
                                refine solve_post_finish hlen h256 hscr_len hscr_ge rfl hinv_a
                                  hfuel_le1 hframe_a.nv hframe_a.orig_nc hframe_a.ante
                                  hframe_a.nassump hframe_a.assump hframe_a.perm hframe_a.clAux
                                  (fun _ => hframe_a.core) (Or.inl rfl)
                                  (fun h => absurd h (by decide)) ?_ hQ rfl
                                rw [← hkPtr_eq]; exact sep_ac hm_a
                        · have hconfl_ff : confl_m = 0xFFFFFFFF#32 := by
                            first | exact ‹_› | exact Classical.not_not.mp ‹_›
                          have hm_l1 : (KittenMemA kPtr acap km ⋆
                              (FullKittenFrame c sFuel1 ⋆ R)) m := by
                            simpa only [sFuel1] using sep_ac hm
                          clear hm
                          c0_hsteps_nogrp
                          refine wp_while_break_state
                            (β := BitVec 32 × BitVec 32 × Bool × KittenState)
                            (fun bst => ((bst.1, bst.2.1, bst.2.2.1, ()) :
                              Tup Val [i32, i32, .bool]))
                            (fun bst m_b =>
                              (bst.2.2.1 = false → bst.1 = 0xFFFFFFFF#32 ∧ bst.2.2.2 = km ∧
                                ∀ j < km.nassump.toNat,
                                  km.vals[(km.assump[j]?.getD 0#32).toNat]? = some 1#32) ∧
                              (bst.2.2.1 = true →
                                bst.2.2.2.Inv acap ∧ SolveFrame ks0 bst.2.2.2 ∧
                                (bst.1 ≠ 0xFFFFFFFE#32 →
                                  SolveLoopInv acap ks0 bst.2.2.2 bst.1)) ∧
                              (KittenMemA kPtr acap bst.2.2.2 ⋆
                                (FullKittenFrame c sFuel1 ⋆ R)) m_b)
                            (α := BitVec 32)
                            (fun st => ((st, ()) : Tup Val [i32]))
                            (fun st => km.nassump.toNat - st.toNat)
                            (fun st m_b =>
                              st.toNat ≤ km.nassump.toNat ∧
                              (∀ j < st.toNat,
                                km.vals[(km.assump[j]?.getD 0#32).toNat]? = some 1#32) ∧
                              (KittenMemA kPtr acap km ⋆ (FullKittenFrame c sFuel1 ⋆ R)) m_b)
                            ?_ ?_ ?_
                          · rintro B ⟨confl_b, ad_b, did_b, ks_b⟩ m_b ⟨hf_b, ht_b, hm_b⟩
                            dsimp only at hf_b ht_b hm_b
                            c0_hsplit
                            · have hfe_b : confl_b = 0xFFFFFFFE#32 := ‹_›
                              c0_hsteps!
                              have hdid_t : did_b = true := by
                                cases did_b
                                · obtain ⟨hc, _⟩ := hf_b rfl; rw [hc] at hfe_b; cases hfe_b
                                · rfl
                              obtain ⟨hinv_b, hframe_b, _⟩ := ht_b hdid_t
                              obtain ⟨_, hmFin_b⟩ := kittenMemA_to_mem hm_b
                              refine solve_post_finish hlen h256 hscr_len hscr_ge rfl hinv_b
                                hfuel_le1 hframe_b.nv hframe_b.orig_nc hframe_b.ante
                                hframe_b.nassump hframe_b.assump hframe_b.perm hframe_b.clAux
                                (fun _ => hframe_b.core) (Or.inl rfl)
                                (fun h => absurd h (by decide)) ?_ hQ rfl
                              rw [← hkPtr_eq]; exact sep_ac hmFin_b
                            · have hne_fe_b : confl_b ≠ 0xFFFFFFFE#32 := ‹_›
                              c0_hsplit
                              · have hdid_t : did_b = true := ‹_›
                                c0_hsteps!
                                obtain ⟨_, _, hsi_b⟩ := ht_b hdid_t
                                exact ih_m (confl_b, ks_b, fuel_m - 1#64) _ (by dsimp only; omega)
                                  ⟨hfuel_le1, hsi_b hne_fe_b, hm_b⟩
                              · have hdid_f : did_b = false := by
                                  cases did_b <;> simp_all
                                obtain ⟨_, hks_b_eq, hall_ass_j⟩ := hf_b hdid_f
                                subst ks_b
                                have hall_ass_mem : ∀ a ∈ kittenAssumpLits km,
                                    km.vals[a]? = some 1#32 := by
                                  intro a ha
                                  simp only [kittenAssumpLits, List.mem_map,
                                    List.mem_take_iff_getElem] at ha
                                  obtain ⟨ab, ⟨ia, hia, rfl⟩, rfl⟩ := ha
                                  have hlen_a : km.nassump.toNat ≤ km.assump.length := by
                                    rw [hsi_m.inv.shapes.assump_len]
                                    exact hsi_m.inv.clauses.nassump_le
                                  have hia_lt : ia < km.nassump.toNat := by omega
                                  have hget := hall_ass_j ia hia_lt
                                  rwa [List.getElem?_eq_getElem (by omega : ia < km.assump.length),
                                    Option.getD_some] at hget
                                c0_hsplit
                                · c0_hsteps!
                                  obtain ⟨_, hmFin_b⟩ := kittenMemA_to_mem hm_b
                                  refine solve_post_finish hlen h256 hscr_len hscr_ge rfl hsi_m.inv
                                    hfuel_le1 hsi_m.frame.nv hsi_m.frame.orig_nc hsi_m.frame.ante
                                    hsi_m.frame.nassump hsi_m.frame.assump hsi_m.frame.perm
                                    hsi_m.frame.clAux (fun _ => hsi_m.frame.core)
                                    (Or.inr (Or.inl rfl)) (fun h => absurd h (by decide))
                                    ?_ hQ rfl
                                  rw [← hkPtr_eq]; exact sep_ac hmFin_b
                                · have hnv_m := hsi_m.inv.clauses.nv_le
                                  c0_hsteps_nogrp
                                  refine wp_while_break_state
                                    (β := BitVec 32 × BitVec 32 × BitVec 32)
                                    (fun bst => (bst.1, bst.2.1, bst.2.2, ()))
                                    (fun bst m_v =>
                                      (bst.2.1 = 0xFFFFFFFF#32 ∨
                                        (bst.2.1.toNat < km.nv.toNat ∧
                                          km.vals[2 * bst.2.1.toNat]?.getD 0#32 = 0#32)) ∧
                                      (KittenMemA kPtr acap km ⋆
                                        (FullKittenFrame c sFuel1 ⋆ R)) m_v)
                                    (α := BitVec 32 × BitVec 32)
                                    (fun st => (st.1, st.2, ()))
                                    (fun st => km.nv.toNat - st.2.toNat)
                                    (fun st m_v =>
                                      st.2.toNat ≤ km.nv.toNat ∧
                                      (KittenMemA kPtr acap km ⋆
                                        (FullKittenFrame c sFuel1 ⋆ R)) m_v)
                                    ?_ ?_ ?_
                                  · rintro B1 ⟨_c1, pick1, _s1⟩ m_v1 ⟨hpick1, hm_v1⟩
                                    dsimp only at hpick1 hm_v1
                                    refine wp_join_state
                                      (proj := fun p : BitVec 32 × BitVec 32 × BitVec 32 =>
                                        (p.1, p.2.1, p.2.2, ()))
                                      (fun p m_v2 =>
                                        (p.2.1 = 0xFFFFFFFF#32 ∨
                                          (p.2.1.toNat < km.nv.toNat ∧
                                            km.vals[2 * p.2.1.toNat]?.getD 0#32 = 0#32)) ∧
                                        (KittenMemA kPtr acap km ⋆
                                          (FullKittenFrame c sFuel1 ⋆ R)) m_v2)
                                      ?_ ?_
                                    · intro J2 ⟨_c2, pick2, _s2⟩ m_v2 ⟨hpick2, hm_v2⟩
                                      dsimp only at hpick2 hm_v2
                                      refine wp_join_state
                                        (proj := fun p : BitVec 32 × BitVec 32 => (p.1, p.2, ()))
                                        (fun p m_v3 =>
                                          (p.2 = 0xFFFFFFFF#32 ∨
                                            (p.2.toNat < km.nv.toNat ∧
                                              km.vals[2 * p.2.toNat]?.getD 0#32 = 0#32)) ∧
                                          (KittenMemA kPtr acap km ⋆
                                            (FullKittenFrame c sFuel1 ⋆ R)) m_v3)
                                        ?_ ?_
                                      · intro J3 ⟨_c3, pick3⟩ m_v3 ⟨hpick3, hm_v3⟩
                                        dsimp only at hpick3 hm_v3
                                        c0_hsplit
                                        · c0_hsteps!
                                          obtain ⟨_, hmFin_v⟩ := kittenMemA_to_mem hm_v3
                                          refine solve_post_finish hlen h256 hscr_len hscr_ge rfl
                                            hsi_m.inv hfuel_le1 hsi_m.frame.nv hsi_m.frame.orig_nc
                                            hsi_m.frame.ante hsi_m.frame.nassump hsi_m.frame.assump
                                            hsi_m.frame.perm hsi_m.frame.clAux
                                            (fun _ => hsi_m.frame.core) (Or.inr (Or.inl rfl))
                                            (fun h => absurd h (by decide)) ?_ hQ rfl
                                          rw [← hkPtr_eq]; exact sep_ac hmFin_v
                                        · have hpk_ne : pick3 ≠ 0xFFFFFFFF#32 := ‹_›
                                          rcases hpick3 with rfl | ⟨hpk_lt, hpk_val⟩
                                          · exact absurd rfl hpk_ne
                                          have hpk_wrap : pick3.toNat < 2 ^ 28 := by
                                            unfold kMaxV at hnv_m; omega
                                          have hpk_128 : pick3.toNat < 128 := by
                                            unfold kMaxV at hnv_m; omega
                                          let ks_q := km.putHdr .qsearch pick3
                                          have hinv_q := inv_set_qsearch hsi_m.inv pick3
                                          have hsync_q : KittenTrailSynced ks_q := hsi_m.sync
                                          have hframe_q : SolveFrame ks0 ks_q :=
                                            SolveFrame.trans hsi_m.frame
                                              ⟨rfl, rfl, rfl, rfl, rfl, KittenCnfPermEquiv.refl _,
                                               fun _ _ => rfl, fun _ _ => rfl⟩
                                          let ph : BitVec 32 :=
                                            (ks_q.flags[pick3.toNat]?.getD 0#32 ^^^ ks_q.phase) &&&
                                              1#32
                                          have hq_nv : ks_q.nv = km.nv := rfl
                                          have hq_lvl : ks_q.lvl = km.lvl := rfl
                                          have hph_lt : ph.toNat < 2 := by
                                            dsimp only [ph]; rw [BitVec.toNat_and]
                                            have h1 : (1#32 : BitVec 32).toNat = 1 := rfl
                                            rw [h1]
                                            exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
                                          let lit_d := (pick3 <<< (1 : Nat)) ||| ph
                                          have hlit_d := bv32_shl1_or_bit_toNat hpk_lt hnv_m hph_lt
                                          have hlit_0 : ks_q.vals[lit_d.toNat]? = some 0#32 := by
                                            have hz0 := vals_some_zero_of_getD hinv_q
                                              (show 2 * pick3.toNat < 2 * ks_q.nv.toNat by
                                                rw [hq_nv]; omega)
                                              hpk_val
                                            rcases (by omega : ph.toNat = 0 ∨ ph.toNat = 1) with
                                              h0 | h1
                                            · rwa [hlit_d.1, h0, Nat.add_zero]
                                            · have hxor : 2 * pick3.toNat + 1 =
                                                  (2 * pick3.toNat) ^^^ 1 := by
                                                rcases nat_xor1_cases (2 * pick3.toNat) with
                                                  ⟨_, _⟩ | ⟨_, _⟩ <;> omega
                                              rw [hlit_d.1, h1, hxor]
                                              exact vals_pair_some_zero hinv_q
                                                (by rw [hq_nv]; omega) hz0
                                          have hle_te := lvl_le_trl_end hinv_q hsi_m.lvlne
                                          have hte_le := hinv_q.assign.trl_end_le
                                          have hlvl_wrap : ks_q.lvl.toNat + 1 < 2 ^ 32 := by
                                            dsimp only [ks_q]
                                            rw [hq_nv] at hte_le; unfold kMaxV at hnv_m; omega
                                          let ks_l := ks_q.putHdr .lvl (ks_q.lvl + 1#32)
                                          have hte_lt := trl_end_lt_nv_of_unassigned hinv_q
                                            (by rw [hq_nv]; exact hlit_d.2) (by rw [hlit_0]; rfl)
                                          c0_hsteps_nogrp
                                          c0_hcall hAsg
                                          · obtain ⟨_, hm_asg⟩ := kittenMemA_to_mem hm
                                            exact ⟨acap, ks_l, FullKittenFrame c sFuel1 ⋆ R,
                                              hinv_q.shapes.putHdr .lvl _, hacap_lt, hnv_m,
                                              hlit_d.2, hte_lt, hm_asg, fun mA hmA => by
                                                obtain ⟨hinv_d, hsync_d, hinc_d, hframe_d,
                                                  hlvlne_d, hlate_d⟩ :=
                                                  decide_step_preserves hinv_q hsync_q hsi_m.incons
                                                    hframe_q hsi_m.lvlne hsi_m.late hlit_d.2 hlit_0
                                                    (fun _ a ha => hall_ass_mem a ha)
                                                c0_hcall hProp
                                                · refine ⟨acap, kittenAssignStep ks_l lit_d
                                                    0xFFFFFFFF#32, FullKittenFrame c sFuel1 ⋆ R,
                                                    hinv_d, hsync_d, hmA,
                                                    fun confl_p2 ks_p2 m_p2 hinv_p2 hsync_p2 p_nv
                                                      p_on p_lvl p_inc p_fail p_ant p_na p_ass
                                                      p_perm p_clAux p_core p_te_le p_dec p_trl
                                                      _ p_ne hm_p2 => ?_⟩
                                                  c0_hsplit
                                                  · have : confl_p2 = 0xFFFFFFFE#32 := ‹_›
                                                    c0_hsteps!
                                                    have hframe_p2 : SolveFrame ks0 ks_p2 :=
                                                      SolveFrame.trans hframe_d
                                                        ⟨p_nv, p_on, p_ant, p_na, p_ass, p_perm,
                                                         p_clAux, p_core⟩
                                                    refine solve_post_finish hlen h256 hscr_len
                                                      hscr_ge rfl hinv_p2 hfuel_le1 hframe_p2.nv
                                                      hframe_p2.orig_nc hframe_p2.ante
                                                      hframe_p2.nassump hframe_p2.assump
                                                      hframe_p2.perm hframe_p2.clAux
                                                      (fun _ => hframe_p2.core) (Or.inl rfl)
                                                      (fun h => absurd h (by decide)) ?_ hQ rfl
                                                    rw [← hkPtr_eq]; exact sep_ac hm_p2
                                                  · have hc_ne2 : confl_p2 ≠ 0xFFFFFFFE#32 := ‹_›
                                                    have hsi_p2 := solveLoopInv_of_propagate hinv_d
                                                      hinc_d hsi_m.failing hframe_d hlvlne_d hlate_d
                                                      hinv_p2 hsync_p2 p_nv p_on p_lvl p_inc p_fail
                                                      p_ant p_na p_ass p_perm p_clAux p_core p_dec
                                                      p_te_le p_trl hc_ne2 (p_ne · hc_ne2)
                                                    c0_hsteps!
                                                    exact ih_m (confl_p2, ks_p2, fuel_m - 1#64) _
                                                      (by dsimp only; omega)
                                                      ⟨hfuel_le1, hsi_p2,
                                                       kittenMem_to_amem hinv_p2.shapes hm_p2⟩⟩
                                      · intro J3 hJ3
                                        c0_hsplit
                                        · have hpk2_ff : pick2 = 0xFFFFFFFF#32 := ‹_›
                                          subst pick2
                                          refine wp_while_break_state
                                            (β := BitVec 32 × BitVec 32)
                                            (fun bst => ((bst.1, bst.2, ()) : Tup Val [i32, i32]))
                                            (fun bst m_v3 =>
                                              (bst.2 = 0xFFFFFFFF#32 ∨
                                                (bst.2.toNat < km.nv.toNat ∧
                                                  km.vals[2 * bst.2.toNat]?.getD 0#32 = 0#32)) ∧
                                              (KittenMemA kPtr acap km ⋆
                                                (FullKittenFrame c sFuel1 ⋆ R)) m_v3)
                                            (α := BitVec 32)
                                            (fun st => ((st, ()) : Tup Val [i32]))
                                            (fun st => km.nv.toNat - st.toNat)
                                            (fun st m_v3 =>
                                              st.toNat ≤ km.nv.toNat ∧
                                              (KittenMemA kPtr acap km ⋆
                                                (FullKittenFrame c sFuel1 ⋆ R)) m_v3)
                                            ?_ ?_ ?_
                                          · rintro B3 ⟨c3, pk3⟩ m_v3 ⟨hpk3, hm_v3⟩
                                            exact hJ3 (c3, pk3) m_v3 ⟨hpk3, hm_v3⟩
                                          · rintro B3 L3 c3 m_v3 hB3 hL3 ⟨hc3_le, hm_v3⟩
                                            c0_hsplit
                                            · have hc3_lt : c3.toNat < km.nv.toNat := by bv_omega
                                              have hc3_2 : 2 * c3.toNat < 256 := by
                                                unfold kMaxV at hnv_m; omega
                                              have hc3_2w : 2 * c3.toNat < 2 ^ 28 := by omega
                                              have hc3_shl : (c3 <<< (1 : Nat)).toNat =
                                                  2 * c3.toNat := by
                                                rw [BitVec.toNat_shiftLeft]; simp; omega
                                              have hc3_shl_w : (c3 <<< (1 : Nat)).toNat < 2 ^ 28 :=
                                                by rw [hc3_shl]; exact hc3_2w
                                              have hc3_shl_256 : (c3 <<< (1 : Nat)).toNat < 256 :=
                                                by rw [hc3_shl]; exact hc3_2
                                              have hc3_1 : (c3 + 1#32).toNat = c3.toNat + 1 := by
                                                unfold kMaxV at hnv_m; bv_omega
                                              c0_hsplit
                                              · have hval0 : km.vals[2 * c3.toNat]?.getD 0#32 =
                                                    0#32 := by
                                                  rwa [← hc3_shl]
                                                c0_hsteps!
                                                exact hB3 (c3, c3) m_v3
                                                  ⟨Or.inr ⟨hc3_lt, hval0⟩, hm_v3⟩
                                              · c0_hsteps!
                                                exact hL3 (c3 + 1#32) m_v3
                                                  (by rw [hc3_1]; omega)
                                                  ⟨by rw [hc3_1]; omega, hm_v3⟩
                                            · exact hB3 (c3, 0xFFFFFFFF#32) m_v3 ⟨Or.inl rfl, hm_v3⟩
                                          · intro B3 L3 hB3 hL3
                                            exact wp_jump_state
                                              (proj := fun st : BitVec 32 => (st, ()))
                                              0#32 rfl (hL3 _ _ ⟨by simp, hm_v2⟩)
                                        · exact wp_jump_state
                                            (proj := fun p : BitVec 32 × BitVec 32 =>
                                              (p.1, p.2, ()))
                                            (_c2, pick2) rfl (hJ3 (_c2, pick2) m_v2 ⟨hpick2, hm_v2⟩)
                                    · intro J2 hJ2
                                      c0_hsplit
                                      · have hpk1_ff : pick1 = 0xFFFFFFFF#32 := ‹_›
                                        subst pick1
                                        c0_hsteps_nogrp
                                        refine wp_while_break_state
                                          (β := BitVec 32 × BitVec 32 × BitVec 32)
                                          (fun bst => (bst.1, bst.2.1, bst.2.2, ()))
                                          (fun bst m_v2 =>
                                            (bst.2.1 = 0xFFFFFFFF#32 ∨
                                              (bst.2.1.toNat < km.nv.toNat ∧
                                                km.vals[2 * bst.2.1.toNat]?.getD 0#32 = 0#32)) ∧
                                            (KittenMemA kPtr acap km ⋆
                                              (FullKittenFrame c sFuel1 ⋆ R)) m_v2)
                                          (α := BitVec 32 × BitVec 32)
                                          (fun st => (st.1, st.2, ()))
                                          (fun st => km.nv.toNat - st.2.toNat)
                                          (fun st m_v2 =>
                                            st.2.toNat ≤ km.nv.toNat ∧
                                            (KittenMemA kPtr acap km ⋆
                                              (FullKittenFrame c sFuel1 ⋆ R)) m_v2)
                                          ?_ ?_ ?_
                                        · rintro B2 ⟨c2, pk2, s2⟩ m_v2 ⟨hpk2, hm_v2⟩
                                          exact hJ2 (c2, pk2, s2) m_v2 ⟨hpk2, hm_v2⟩
                                        · rintro B2 L2 ⟨c2, s2⟩ m_v2 hB2 hL2 ⟨hs2_le, hm_v2⟩
                                          c0_hsplit
                                          · c0_hsplit
                                            · have hc2_lt : c2.toNat < km.nv.toNat := by bv_omega
                                              have hs2_lt : s2.toNat < km.nv.toNat := by bv_omega
                                              have hc2_128 : c2.toNat < 128 := by
                                                unfold kMaxV at hnv_m; omega
                                              have hc2_w : c2.toNat < 2 ^ 28 := by omega
                                              have hc2_2 : 2 * c2.toNat < 256 := by
                                                unfold kMaxV at hnv_m; omega
                                              have hc2_2w : 2 * c2.toNat < 2 ^ 28 := by omega
                                              have hc2_shl : (c2 <<< (1 : Nat)).toNat =
                                                  2 * c2.toNat := by
                                                rw [BitVec.toNat_shiftLeft]; simp; omega
                                              have hc2_shl_w : (c2 <<< (1 : Nat)).toNat < 2 ^ 28 :=
                                                by rw [hc2_shl]; exact hc2_2w
                                              have hc2_shl_256 : (c2 <<< (1 : Nat)).toNat < 256 :=
                                                by rw [hc2_shl]; exact hc2_2
                                              have hs2_1 : (s2 + 1#32).toNat = s2.toNat + 1 := by
                                                unfold kMaxV at hnv_m; bv_omega
                                              c0_hsplit
                                              · have hval0 : km.vals[2 * c2.toNat]?.getD 0#32 =
                                                    0#32 := by
                                                  rwa [← hc2_shl]
                                                c0_hsteps!
                                                exact hB2 (c2, c2, s2) m_v2
                                                  ⟨Or.inr ⟨hc2_lt, hval0⟩, hm_v2⟩
                                              · c0_hsteps!
                                                exact hL2 (km.qprev[c2.toNat]?.getD 0#32, s2 + 1#32)
                                                  m_v2 (by dsimp only; rw [hs2_1]; omega)
                                                  ⟨by dsimp only; rw [hs2_1]; omega, hm_v2⟩
                                            · exact hB2 (c2, 0xFFFFFFFF#32, s2) m_v2
                                                ⟨Or.inl rfl, hm_v2⟩
                                          · exact hB2 (c2, 0xFFFFFFFF#32, s2) m_v2
                                              ⟨Or.inl rfl, hm_v2⟩
                                        · intro B2 L2 hB2 hL2
                                          exact wp_jump_state
                                            (proj := fun st : BitVec 32 × BitVec 32 =>
                                              (st.1, st.2, ()))
                                            (km.qlast, 0#32) rfl
                                            (hL2 _ _ ⟨by simp, hm_v1⟩)
                                      · exact wp_jump_state
                                          (proj := fun p : BitVec 32 × BitVec 32 × BitVec 32 =>
                                            (p.1, p.2.1, p.2.2, ()))
                                          (_c1, pick1, _s1) rfl
                                          (hJ2 (_c1, pick1, _s1) m_v1 ⟨hpick1, hm_v1⟩)
                                  · rintro B1 L1 ⟨c1, s1⟩ m_v1 hB1 hL1 ⟨hs1_le, hm_v1⟩
                                    c0_hsplit
                                    · c0_hsplit
                                      · have hc1_lt : c1.toNat < km.nv.toNat := by bv_omega
                                        have hs1_lt : s1.toNat < km.nv.toNat := by bv_omega
                                        have hc1_128 : c1.toNat < 128 := by
                                          unfold kMaxV at hnv_m; omega
                                        have hc1_w : c1.toNat < 2 ^ 28 := by omega
                                        have hc1_2 : 2 * c1.toNat < 256 := by
                                          unfold kMaxV at hnv_m; omega
                                        have hc1_2w : 2 * c1.toNat < 2 ^ 28 := by omega
                                        have hc1_shl : (c1 <<< (1 : Nat)).toNat = 2 * c1.toNat := by
                                          rw [BitVec.toNat_shiftLeft]; simp; omega
                                        have hc1_shl_w : (c1 <<< (1 : Nat)).toNat < 2 ^ 28 := by
                                          rw [hc1_shl]; exact hc1_2w
                                        have hc1_shl_256 : (c1 <<< (1 : Nat)).toNat < 256 := by
                                          rw [hc1_shl]; exact hc1_2
                                        have hs1_1 : (s1 + 1#32).toNat = s1.toNat + 1 := by
                                          unfold kMaxV at hnv_m; bv_omega
                                        c0_hsplit
                                        · have hval0 : km.vals[2 * c1.toNat]?.getD 0#32 = 0#32 := by
                                            rwa [← hc1_shl]
                                          c0_hsteps!
                                          exact hB1 (c1, c1, s1) m_v1
                                            ⟨Or.inr ⟨hc1_lt, hval0⟩, hm_v1⟩
                                        · c0_hsteps!
                                          exact hL1 (km.qprev[c1.toNat]?.getD 0#32, s1 + 1#32)
                                            m_v1 (by dsimp only; rw [hs1_1]; omega)
                                            ⟨by dsimp only; rw [hs1_1]; omega, hm_v1⟩
                                      · exact hB1 (c1, 0xFFFFFFFF#32, s1) m_v1 ⟨Or.inl rfl, hm_v1⟩
                                    · exact hB1 (c1, 0xFFFFFFFF#32, s1) m_v1 ⟨Or.inl rfl, hm_v1⟩
                                  · intro B1 L1 hB1 hL1
                                    exact wp_jump_state
                                      (proj := fun st : BitVec 32 × BitVec 32 => (st.1, st.2, ()))
                                      (km.qsearch, 0#32) rfl (hL1 _ _ ⟨by simp, hm_b⟩)
                          · rintro B0 L0 ad_a m_a hB0 hL0 ⟨had_le, hall_j, hm_a⟩
                            c0_hsplit
                            · have had_lt : ad_a.toNat < km.nassump.toNat := by bv_omega
                              have hna_le := hsi_m.inv.clauses.nassump_le
                              have hnv_m := hsi_m.inv.clauses.nv_le
                              have had_128 : ad_a.toNat < 128 := by unfold kMaxV at hna_le; omega
                              have had_w : ad_a.toNat < 2 ^ 28 := by omega
                              have had_1 : (ad_a + 1#32).toNat = ad_a.toNat + 1 := by
                                unfold kMaxV at hna_le; bv_omega
                              let alit := km.assump[ad_a.toNat]?.getD 0#32
                              have halit_lt : alit.toNat < 2 * km.nv.toNat :=
                                hsi_m.inv.clauses.assump_ok ad_a.toNat had_lt
                              have halit_256 : alit.toNat < 256 := by unfold kMaxV at hnv_m; omega
                              have halit_w : alit.toNat < 2 ^ 28 := by omega
                              have hlen_a : km.nassump.toNat ≤ km.assump.length := by
                                rw [hsi_m.inv.shapes.assump_len]; exact hna_le
                              have halit_mem : alit.toNat ∈ kittenAssumpLits km :=
                                mem_kittenAssumpLits_of_lt hlen_a had_lt
                              c0_hsplit
                              · have hav2 : km.vals[alit.toNat]?.getD 0#32 = 2#32 := ‹_›
                                have hav2' : km.vals[alit.toNat]? = some 2#32 := by
                                  have hl : alit.toNat < km.vals.length := by
                                    rw [hsi_m.inv.shapes.vals_len]; exact halit_256
                                  rw [List.getElem?_eq_getElem hl, Option.getD_some] at hav2
                                  rw [List.getElem?_eq_getElem hl, hav2]
                                obtain ⟨hdec_in, huns_bf⟩ := allDecisionsInAssumps_of_late
                                  hsi_m.inv hsi_m.sync hsi_m.late halit_mem hav2'
                                obtain ⟨_, hm_bf0⟩ := kittenMemA_to_mem hm_a
                                c0_hcall hBf
                                · refine ⟨acap, km, FullKittenFrame c sFuel1 ⋆ R, hsi_m.inv,
                                    hsi_m.sync, halit_lt, halit_mem, hav2', hdec_in, hm_bf0,
                                    fun ks_bf m_bf hinv_bf _ hfail_bf hpres_bf hm_bf => ?_⟩
                                  c0_hsteps!
                                  have huns_bf' : (cnfOfClauses (kittenOrigClauses ks_bf) ++
                                      unitsCnf (kittenAssumpLits ks_bf)).Unsat := by
                                    unfold kittenAssumpLits
                                    rw [hpres_bf.orig_eq, hpres_bf.nassump, hpres_bf.assump]
                                    exact huns_bf
                                  refine solve_post_finish hlen h256 hscr_len hscr_ge rfl hinv_bf
                                    hfuel_le1 (hpres_bf.nv.trans hsi_m.frame.nv)
                                    (hpres_bf.orig_nc.trans hsi_m.frame.orig_nc)
                                    (hpres_bf.ante.trans hsi_m.frame.ante)
                                    (hpres_bf.nassump.trans hsi_m.frame.nassump)
                                    (hpres_bf.assump.trans hsi_m.frame.assump) ?_ ?_
                                    (fun h => absurd rfl h) (Or.inr (Or.inr rfl))
                                    (fun _ => ⟨Or.inr (by rw [hfail_bf]; decide), huns_bf'⟩)
                                    ?_ hQ rfl
                                  · rw [hpres_bf.orig_eq]; exact hsi_m.frame.perm
                                  · intro ci hci
                                    rw [hpres_bf.clAux_eq ci
                                      (by rw [hsi_m.frame.orig_nc]; exact hci)]
                                    exact hsi_m.frame.clAux ci hci
                                  · rw [← hkPtr_eq]; exact sep_ac hm_bf
                              · c0_hsplit
                                · have hav0 : km.vals[alit.toNat]?.getD 0#32 = 0#32 := ‹_›
                                  have halit_0 := vals_some_zero_of_getD hsi_m.inv halit_lt hav0
                                  have hle_te := lvl_le_trl_end hsi_m.inv hsi_m.lvlne
                                  have hte_le := hsi_m.inv.assign.trl_end_le
                                  have hlvl_wrap : km.lvl.toNat + 1 < 2 ^ 32 := by
                                    unfold kMaxV at hnv_m; omega
                                  let km_l := km.putHdr .lvl (km.lvl + 1#32)
                                  have hte_lt := trl_end_lt_nv_of_unassigned hsi_m.inv halit_lt hav0
                                  c0_hsteps_nogrp
                                  c0_hcall hAsg
                                  · obtain ⟨_, hm_asg⟩ := kittenMemA_to_mem hm
                                    exact ⟨acap, km_l, FullKittenFrame c sFuel1 ⋆ R,
                                      hsi_m.inv.shapes.putHdr .lvl _, hacap_lt, hnv_m, halit_lt,
                                      hte_lt, hm_asg, fun mA hmA => by
                                        obtain ⟨hinv_d, hsync_d, hinc_d, hframe_d, hlvlne_d,
                                          hlate_d⟩ :=
                                          decide_step_preserves hsi_m.inv hsi_m.sync hsi_m.incons
                                            hsi_m.frame hsi_m.lvlne hsi_m.late halit_lt halit_0
                                            (fun hnot => absurd halit_mem hnot)
                                        c0_hcall hProp
                                        · refine ⟨acap, kittenAssignStep km_l alit 0xFFFFFFFF#32,
                                            FullKittenFrame c sFuel1 ⋆ R, hinv_d, hsync_d, hmA,
                                            fun confl_p2 ks_p2 m_p2 hinv_p2 hsync_p2 p_nv p_on
                                              p_lvl p_inc p_fail p_ant p_na p_ass p_perm p_clAux
                                              p_core p_te_le p_dec p_trl _ p_ne hm_p2 => ?_⟩
                                          c0_hsteps!
                                          have hframe_p2 : SolveFrame ks0 ks_p2 :=
                                            SolveFrame.trans hframe_d
                                              ⟨p_nv, p_on, p_ant, p_na, p_ass, p_perm, p_clAux,
                                               p_core⟩
                                          exact hB0 (confl_p2, ad_a, true, ks_p2) m_p2
                                            ⟨(fun h => by dsimp only at h; cases h), fun _ =>
                                              ⟨hinv_p2, hframe_p2, fun hc_ne =>
                                                solveLoopInv_of_propagate hinv_d hinc_d
                                                  hsi_m.failing hframe_d hlvlne_d hlate_d hinv_p2
                                                  hsync_p2 p_nv p_on p_lvl p_inc p_fail p_ant p_na
                                                  p_ass p_perm p_clAux p_core p_dec p_te_le p_trl
                                                  hc_ne (p_ne · hc_ne)⟩,
                                             kittenMem_to_amem hinv_p2.shapes hm_p2⟩⟩
                                · have hne2 : km.vals[alit.toNat]?.getD 0#32 ≠ 2#32 := ‹_›
                                  have hne0 : km.vals[alit.toNat]?.getD 0#32 ≠ 0#32 := ‹_›
                                  have hav1 : km.vals[alit.toNat]?.getD 0#32 = 1#32 := by
                                    rcases hsi_m.inv.assign.vals_dom alit.toNat halit_lt with
                                      h0 | h1 | h2
                                    · exact absurd h0 hne0
                                    · exact h1
                                    · exact absurd h2 hne2
                                  have hav1' : km.vals[alit.toNat]? = some 1#32 := by
                                    have hl : alit.toNat < km.vals.length := by
                                      rw [hsi_m.inv.shapes.vals_len]; exact halit_256
                                    rw [List.getElem?_eq_getElem hl, Option.getD_some] at hav1
                                    rw [List.getElem?_eq_getElem hl, hav1]
                                  c0_hsteps!
                                  refine hL0 (ad_a + 1#32) m_a
                                    (by rw [had_1]; omega)
                                    ⟨by rw [had_1]; exact had_lt,
                                     fun j hj => by
                                       rw [had_1] at hj
                                       by_cases hja : j = ad_a.toNat
                                       · subst hja; exact hav1'
                                       · exact hall_j j (by omega),
                                     hm_a⟩
                            · exact hB0 (confl_m, ad_a, false, km) m_a
                                ⟨fun _ => ⟨hconfl_ff, rfl, fun j hj => by
                                  have heq : ad_a.toNat = km.nassump.toNat := by bv_omega
                                  rw [← heq] at hj
                                  exact hall_j j hj⟩,
                                 (fun h => by dsimp only at h; cases h), hm_a⟩
                          · intro B0 L0 hB0 hL0
                            exact wp_jump_state
                              (proj := fun st : BitVec 32 => (st, ()))
                              0#32 rfl
                              (hL0 _ _ ⟨by simp, fun _ hj => by simp at hj, hm_l1⟩)
                      · c0_hsteps!
                        obtain ⟨_, hmFin_m⟩ := kittenMemA_to_mem hm_l
                        refine solve_post_finish hlen h256 hscr_len hscr_ge rfl hsi_m.inv hfuel_m
                          hsi_m.frame.nv hsi_m.frame.orig_nc hsi_m.frame.ante hsi_m.frame.nassump
                          hsi_m.frame.assump hsi_m.frame.perm hsi_m.frame.clAux
                          (fun _ => hsi_m.frame.core) (Or.inl rfl)
                          (fun h => absurd h (by decide)) ?_ hQ rfl
                        rw [← hkPtr_eq]; exact sep_ac hmFin_m
                    · c0_hsteps!
                      obtain ⟨_, hmFin_m⟩ := kittenMemA_to_mem hm_l
                      refine solve_post_finish hlen h256 hscr_len hscr_ge rfl hsi_m.inv hfuel_m
                        hsi_m.frame.nv hsi_m.frame.orig_nc hsi_m.frame.ante hsi_m.frame.nassump
                        hsi_m.frame.assump hsi_m.frame.perm hsi_m.frame.clAux
                        (fun _ => hsi_m.frame.core) (Or.inl rfl)
                        (fun h => absurd h (by decide)) ?_ hQ rfl
                      rw [← hkPtr_eq]; exact sep_ac hmFin_m

end LeanQbe.T.Examples.Kissat.Full
