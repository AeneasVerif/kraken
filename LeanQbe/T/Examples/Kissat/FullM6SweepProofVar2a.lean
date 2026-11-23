module

public import LeanQbe.T.Examples.Kissat.FullM6SweepProofEls2

/-!
# Kissat `D-Full` M6 — Units & Shared Class-Sweep Helpers (`27/39`)

Parametric `(Γ : Env)` `Func.wp` proof for `1/39` owned function (`full_m6_sweep_units_wp`) plus
shared dynamic `M6Var2PhtMem`, `K6Inv`, and `FullDenseInvW` transition helpers used by
`FullM6SweepProofVar2b`:
- `27/39`: `full_m6_sweep_units_wp` (`m6SweepUnitsSpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6Sweep

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full LeanQbe.T.Examples.Kissat.FullM4Sweep
open Kraken.Bedrock2.Test
open FullArenaTactics K6MemATactics K6PtrTactics M6ElsBv
open scoped FullArenaTactics M6SweepTactics

/-! ## 1. Dynamic PHT-Merged Memory, Alignment, `K6Inv`, & `FullDenseInvW` Helpers -/

namespace M6Var2PhtMem
@[scoped c0_load] theorem load_pht_merged {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < L.maxV) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 ((c.pScratchBuf + BitVec.ofNat 64 (4 * L.phtMerged)) + idx.setWidth 64 * 4) =
      some (s.scratch.scratch_buf[L.phtMerged + idx.toNat]'(by
        have := L.hmaxV; have := L.hacap
        rw [hscr, ← hL]; unfold K6Layout.scrLen K6Layout.k6Base K6Layout.phtMerged; omega)) := by
  have := L.hmaxV
  have hptr : (c.pScratchBuf + BitVec.ofNat 64 (4 * L.phtMerged)) + idx.setWidth 64 * 4 =
      c.pScratchBuf + BitVec.ofNat 64 (4 * (L.phtMerged + idx.toNat)) := by
    rw [show idx.setWidth 64 = BitVec.ofNat 64 idx.toNat from by apply BitVec.eq_of_toNat_eq; simp,
      k6_ptr_nat_mul4 _ idx.toNat (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  rw [hptr]; exact load_full_scratch_buf _ hm

@[scoped c0_load] theorem load_pht_merged_32 {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < L.maxV) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32
        ((c.pScratchBuf + BitVec.setWidth 64 ((1280 : BitVec 32) + L.mv32) * 4) +
          idx.setWidth 64 * 4) =
      some (s.scratch.scratch_buf[L.phtMerged + idx.toNat]'(by
        have := L.hmaxV; have := L.hacap
        rw [hscr, ← hL]; unfold K6Layout.scrLen K6Layout.k6Base K6Layout.phtMerged; omega)) := by
  have := L.hmaxV
  have hptr : c.pScratchBuf + BitVec.setWidth 64 ((1280 : BitVec 32) + L.mv32) * 4 =
      c.pScratchBuf + BitVec.ofNat 64 (4 * L.phtMerged) := by
    congr 1; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_add, k6_mv32_toNat,
      BitVec.toNat_ofNat]
    rw [show (1280 : BitVec 32).toNat = 1280 from rfl,
      show (4 : BitVec 64).toNat = 4 from rfl]
    unfold K6Layout.phtMerged
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  rw [hptr]; exact load_pht_merged hL hscr hi hm

@[scoped c0_load] theorem load_pht_merged_bv32 {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < L.maxV) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32
        ((c.pScratchBuf + BitVec.setWidth 64 (1280#32 + L.mv32) * 4) +
          idx.setWidth 64 * 4) =
      some (s.scratch.scratch_buf[L.phtMerged + idx.toNat]'(by
        have := L.hmaxV; have := L.hacap
        rw [hscr, ← hL]; unfold K6Layout.scrLen K6Layout.k6Base K6Layout.phtMerged; omega)) :=
  load_pht_merged_32 hL hscr hi hm

@[scoped c0_store] theorem store_pht_merged {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < L.maxV) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 ((c.pScratchBuf + BitVec.ofNat 64 (4 * L.phtMerged)) + idx.setWidth 64 * 4) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set (L.phtMerged + idx.toNat) v } } ⋆ R)
        (storeMem m i32
          ((c.pScratchBuf + BitVec.ofNat 64 (4 * L.phtMerged)) + idx.setWidth 64 * 4) v) := by
  have := L.hmaxV
  have hptr : (c.pScratchBuf + BitVec.ofNat 64 (4 * L.phtMerged)) + idx.setWidth 64 * 4 =
      c.pScratchBuf + BitVec.ofNat 64 (4 * (L.phtMerged + idx.toNat)) := by
    rw [show idx.setWidth 64 = BitVec.ofNat 64 idx.toNat from by apply BitVec.eq_of_toNat_eq; simp,
      k6_ptr_nat_mul4 _ idx.toNat (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  rw [hptr]
  exact store_full_scratch_buf v (by
    have := L.hmaxV; have := L.hacap
    rw [hscr, ← hL]; unfold K6Layout.scrLen K6Layout.k6Base K6Layout.phtMerged; omega) hm

@[scoped c0_store] theorem store_pht_merged_32 {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < L.maxV) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32
        ((c.pScratchBuf + BitVec.setWidth 64 ((1280 : BitVec 32) + L.mv32) * 4) +
          idx.setWidth 64 * 4) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set (L.phtMerged + idx.toNat) v } } ⋆ R)
        (storeMem m i32
          ((c.pScratchBuf + BitVec.setWidth 64 ((1280 : BitVec 32) + L.mv32) * 4) +
            idx.setWidth 64 * 4) v) := by
  have := L.hmaxV
  have hptr : c.pScratchBuf + BitVec.setWidth 64 ((1280 : BitVec 32) + L.mv32) * 4 =
      c.pScratchBuf + BitVec.ofNat 64 (4 * L.phtMerged) := by
    congr 1; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_add, k6_mv32_toNat,
      BitVec.toNat_ofNat]
    rw [show (1280 : BitVec 32).toNat = 1280 from rfl,
      show (4 : BitVec 64).toNat = 4 from rfl]
    unfold K6Layout.phtMerged
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  rw [hptr]; exact store_pht_merged v hL hscr hi hm

@[scoped c0_store] theorem store_pht_merged_bv32 {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < L.maxV) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32
        ((c.pScratchBuf + BitVec.setWidth 64 (1280#32 + L.mv32) * 4) + idx.setWidth 64 * 4) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set (L.phtMerged + idx.toNat) v } } ⋆ R)
        (storeMem m i32
          ((c.pScratchBuf + BitVec.setWidth 64 (1280#32 + L.mv32) * 4) +
            idx.setWidth 64 * 4) v) :=
  store_pht_merged_32 v hL hscr hi hm

@[scoped c0_store] theorem store_k6_assump0_ofnat {L : K6Layout} {kPtr : BitVec 64}
    {ks : K6State} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32)
    (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32 ((kPtr + BitVec.ofNat 64 (4 * L.oAssump)) + BitVec.ofNat 64 0 * 4) ∧
      (K6MemA L kPtr (ks.putArr .assump 0 v) ⋆ R)
        (storeMem m i32
          ((kPtr + BitVec.ofNat 64 (4 * L.oAssump)) + BitVec.ofNat 64 0 * 4) v) := by
  simpa using store_k6_assump0 v hm

@[scoped c0_store] theorem store_k6_assump0_dyn {L : K6Layout} {kPtr : BitVec 64} {ks : K6State}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32
        ((kPtr + BitVec.setWidth 64 ((32 : BitVec 32) + (9 : BitVec 32) * L.mv32) * 4) +
          BitVec.ofNat 64 0 * 4) ∧
      (K6MemA L kPtr (ks.putArr .assump 0 v) ⋆ R)
        (storeMem m i32
          ((kPtr + BitVec.setWidth 64 ((32 : BitVec 32) + (9 : BitVec 32) * L.mv32) * 4) +
            BitVec.ofNat 64 0 * 4) v) := by
  rw [k6_ptr_assump L kPtr]; exact store_k6_assump0_ofnat v hm

@[scoped c0_store] theorem store_k6_assump0_dyn_bv {L : K6Layout} {kPtr : BitVec 64}
    {ks : K6State} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32)
    (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32
        ((kPtr + BitVec.setWidth 64 (32#32 + 9#32 * L.mv32) * 4) + BitVec.ofNat 64 0 * 4) ∧
      (K6MemA L kPtr (ks.putArr .assump 0 v) ⋆ R)
        (storeMem m i32
          ((kPtr + BitVec.setWidth 64 (32#32 + 9#32 * L.mv32) * 4) +
            BitVec.ofNat 64 0 * 4) v) :=
  store_k6_assump0_dyn v hm

@[scoped c0_store] theorem store_k6_assump1_ofnat {L : K6Layout} {kPtr : BitVec 64}
    {ks : K6State} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32)
    (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32 ((kPtr + BitVec.ofNat 64 (4 * L.oAssump)) + BitVec.ofNat 64 1 * 4) ∧
      (K6MemA L kPtr (ks.putArr .assump 1 v) ⋆ R)
        (storeMem m i32
          ((kPtr + BitVec.ofNat 64 (4 * L.oAssump)) + BitVec.ofNat 64 1 * 4) v) := by
  have hi : (1#32).toNat < szV L := by unfold szV; have := L.hmaxV; bv_omega
  simpa using store_k6_assump v (i := 1#32) hi hm

@[scoped c0_store] theorem store_k6_assump1_4 {L : K6Layout} {kPtr : BitVec 64}
    {ks : K6State} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32)
    (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32 ((kPtr + BitVec.ofNat 64 (4 * L.oAssump)) + 4) ∧
      (K6MemA L kPtr (ks.putArr .assump 1 v) ⋆ R)
        (storeMem m i32 ((kPtr + BitVec.ofNat 64 (4 * L.oAssump)) + 4) v) := by
  simpa using store_k6_assump1_ofnat v hm

@[scoped c0_store] theorem store_k6_assump1_dyn {L : K6Layout} {kPtr : BitVec 64} {ks : K6State}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32
        ((kPtr + BitVec.setWidth 64 ((32 : BitVec 32) + (9 : BitVec 32) * L.mv32) * 4) +
          BitVec.ofNat 64 1 * 4) ∧
      (K6MemA L kPtr (ks.putArr .assump 1 v) ⋆ R)
        (storeMem m i32
          ((kPtr + BitVec.setWidth 64 ((32 : BitVec 32) + (9 : BitVec 32) * L.mv32) * 4) +
            BitVec.ofNat 64 1 * 4) v) := by
  rw [k6_ptr_assump L kPtr]; exact store_k6_assump1_ofnat v hm

@[scoped c0_store] theorem store_k6_assump1_dyn_4 {L : K6Layout} {kPtr : BitVec 64}
    {ks : K6State} {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32)
    (hm : (K6MemA L kPtr ks ⋆ R) m) :
    storeOk m i32
        ((kPtr + BitVec.setWidth 64 ((32 : BitVec 32) + (9 : BitVec 32) * L.mv32) * 4) + 4) ∧
      (K6MemA L kPtr (ks.putArr .assump 1 v) ⋆ R)
        (storeMem m i32
          ((kPtr + BitVec.setWidth 64 ((32 : BitVec 32) + (9 : BitVec 32) * L.mv32) * 4) + 4)
          v) := by
  rw [k6_ptr_assump L kPtr]; exact store_k6_assump1_4 v hm

@[scoped c0_load] theorem load_pht_next_ofnat {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < L.maxV) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 ((c.pScratchBuf + BitVec.ofNat 64 1280 * 4) + idx.setWidth 64 * 4) =
      some (s.scratch.scratch_buf[k6PhtNext + idx.toNat]'(by
        have := L.hmaxV; have := L.hacap
        rw [hscr, ← hL]; unfold K6Layout.scrLen K6Layout.k6Base k6PhtNext; omega)) := by
  change loadVal m i32 ((c.pScratchBuf + BitVec.ofNat 64 (4 * k6PhtNext)) +
    idx.setWidth 64 * 4) = _
  exact M6PhtMem.load_pht_next hL hscr hi hm

@[scoped c0_store] theorem store_pht_next_ofnat {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < L.maxV) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 ((c.pScratchBuf + BitVec.ofNat 64 1280 * 4) + idx.setWidth 64 * 4) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set (k6PhtNext + idx.toNat) v } } ⋆ R)
        (storeMem m i32
          ((c.pScratchBuf + BitVec.ofNat 64 1280 * 4) + idx.setWidth 64 * 4) v) := by
  change storeOk m i32 ((c.pScratchBuf + BitVec.ofNat 64 (4 * k6PhtNext)) +
    idx.setWidth 64 * 4) ∧ _
  exact M6PhtMem.store_pht_next v hL hscr hi hm

@[scoped c0_load] theorem load_m6_full_kvals_dyn {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < 2 * L.maxV) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32
        ((L.kPtr c.pScratchBuf + BitVec.setWidth 64 ((32 : BitVec 32) +
          (10 : BitVec 32) * L.mv32) * 4) + idx.setWidth 64 * 4) =
      some (s.scratch.scratch_buf[L.k6Base + L.oVals + idx.toNat]'(by
        have := L.hmaxV; have := L.hacap
        rw [hscr, ← hL]; unfold K6Layout.scrLen K6Layout.k6Fixed K6Layout.oVals; omega)) := by
  rw [k6_ptr_vals L (L.kPtr c.pScratchBuf)]
  exact FullK6DynMem.load_m6_full_kvals hL hscr hi hm

@[scoped c0_load] theorem load_m6_full_kvals_dyn_bv {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < 2 * L.maxV) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32
        ((L.kPtr c.pScratchBuf + BitVec.setWidth 64 (32#32 + 10#32 * L.mv32) * 4) +
          idx.setWidth 64 * 4) =
      some (s.scratch.scratch_buf[L.k6Base + L.oVals + idx.toNat]'(by
        have := L.hmaxV; have := L.hacap
        rw [hscr, ← hL]; unfold K6Layout.scrLen K6Layout.k6Fixed K6Layout.oVals; omega)) :=
  load_m6_full_kvals_dyn hL hscr hi hm
end M6Var2PhtMem

theorem m6_ptr_phtMerged (L : K6Layout) (pScr : BitVec 64) :
    pScr + BitVec.setWidth 64 ((1280 : BitVec 32) + L.mv32) * 4 =
      pScr + BitVec.ofNat 64 (4 * L.phtMerged) := by
  have := L.hmaxV
  congr 1; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_add, k6_mv32_toNat,
    BitVec.toNat_ofNat]
  rw [show (1280 : BitVec 32).toNat = 1280 from rfl,
    show (4 : BitVec 64).toNat = 4 from rfl]
  unfold K6Layout.phtMerged
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem bv32_sub1_of_pos {x : BitVec 32} (hx : 0 < x.toNat) :
    (x - 1#32).toNat = x.toNat - 1 := by bv_omega

theorem m6_bv32_shl1_lt {v : BitVec 32} (hv : v.toNat < 2 ^ 31) :
    (v <<< (1 : Nat)).toNat = 2 * v.toNat := by bv_omega

theorem m6_pol_01 (pa pc : BitVec 32) :
    let pol := (pa &&& 1#32) ^^^ (pc &&& 1#32)
    pol = 0#32 ∨ pol = 1#32 := by
  intro pol
  have h1 : ∀ x : BitVec 32, (x &&& 1#32) = 0#32 ∨ (x &&& 1#32) = 1#32 := fun x => by
    have ht : (x &&& 1#32).toNat < 2 := by rw [m6_bv32_and1_toNat]; omega
    rcases (by omega : (x &&& 1#32).toNat = 0 ∨ (x &&& 1#32).toNat = 1) with h0 | h1
    · exact Or.inl (BitVec.eq_of_toNat_eq h0)
    · exact Or.inr (BitVec.eq_of_toNat_eq h1)
  rcases h1 pa with ha | ha <;> rcases h1 pc with hc | hc <;> simp [pol, ha, hc]

theorem m6_fullDenseInvW_with_scratch {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {fuel' : BitVec 64} {scr' : List (BitVec 32)} (hscr : scr'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with fuel := fuel' }
        scratch := { s.scratch with scratch_buf := scr' } } :=
  m6_fullDenseInvW_with_fuel_rng_sig_scr h h.1.scratch_ok.sim_sig_len hscr

theorem m6_fullDenseInvW_with_tmk {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {tmk' : List (BitVec 32)} (ht : tmk'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with tarjan_mark := tmk' } } := by
  have hw := h.2.1
  refine ⟨⟨h.1.core_ok, { h.1.scratch_ok with tarjan_mark_len := ht }⟩,
    { hw with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
    h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem m6_fullDenseInvW_with_sig {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {sig' : List (BitVec 64)} (hsig : sig'.length = c.max_vars) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with sim_sig := sig' } } :=
  m6_fullDenseInvW_with_fuel_rng_sig_scr h hsig h.1.scratch_ok.scratch_buf_len

theorem m6_fullDenseInvW_with_sweep_cnt {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    (sc' : BitVec 64) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with sweep_cnt := sc' } } := by
  have hw := h.2.1
  refine ⟨⟨h.1.core_ok, { h.1.scratch_ok with sim_sig_len := h.1.scratch_ok.sim_sig_len }⟩,
    { hw with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
    h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem m6_fullDenseInvW_with_cls_scratch {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {scr' sstk' mclr' wso' : List (BitVec 32)}
    (hscr : scr'.length = c.scratch_cap) (hsst : sstk'.length = c.max_vars)
    (hmc : mclr'.length = c.max_vars) (hwso : wso'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with min_clr := mclr' }
        scratch :=
          { s.scratch with scratch_buf := scr', shrink_stk := sstk', wsort := wso' } } := by
  have hw := h.2.1
  refine ⟨⟨{ h.1.core_ok with min_clr_len_arr := hmc },
      { h.1.scratch_ok with
        scratch_buf_len := hscr, shrink_stk_len := hst_len_fix sstk' hsst,
        wsort_len := hwso }⟩,
    { hw with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
    h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
where
  hst_len_fix (x : List (BitVec 32)) (hx : x.length = c.max_vars) : x.length = c.max_vars := hx

theorem m6_fullDenseInvW_with_ws2 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {ws2' : List (BitVec 32)} (hws2 : ws2'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with work_stk2 := ws2' } } := by
  have hw := h.2.1
  refine ⟨⟨h.1.core_ok, { h.1.scratch_ok with work_stk2_len := hws2 }⟩,
    { hw with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
    h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem m6_k6Inv_of_prefix_set {L : K6Layout} {P : (Nat → Bool) → Prop}
    {scr : List (BitVec 32)} {idx : Nat} {v : BitVec 32} (hi : idx < L.k6Base)
    (_hK : K6Inv L P (k6StateOfScratch L scr)) :
    k6StateOfScratch L (scr.set idx v) = k6StateOfScratch L scr := by
  unfold k6StateOfScratch; rw [m6_list_drop_set_lt scr v hi]

private theorem k6Inv_set_assump1 {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    {a0 : BitVec 32} (ha0 : a0.toNat < 2 * ks.nv.toNat) (hinv : K6Inv L P ks) :
    let ks' := (ks.putHdr .nassump 1#32).putArr .assump 0 a0
    K6Inv L P ks' ∧ ks'.nv = ks.nv ∧ ks'.nassump = 1#32 ∧ k6AssumpLits ks' = [a0.toNat] ∧
    ks'.neq = ks.neq := by
  intro ks'
  have hmL := L.hmaxV
  have hcl := hinv.clauses
  have hna1 : ks'.nassump.toNat ≤ L.maxV := by
    dsimp only [ks', K6State.putArr, K6State.putHdr]; simp; omega
  have ha0_lt : 0 < ks.assump.length := by rw [hinv.shapes.assump_len]; omega
  refine ⟨⟨(hinv.shapes.putHdr .nassump 1#32).putArr .assump 0 a0,
    { acap_eq := by dsimp only [ks', K6State.putArr, K6State.putHdr]; exact hcl.acap_eq
      max_v_eq := by dsimp only [ks', K6State.putArr, K6State.putHdr]; exact hcl.max_v_eq
      max_orig_eq := by dsimp only [ks', K6State.putArr, K6State.putHdr]; exact hcl.max_orig_eq
      max_cl_eq := by dsimp only [ks', K6State.putArr, K6State.putHdr]; exact hcl.max_cl_eq
      nv_le := by dsimp only [ks', K6State.putArr, K6State.putHdr]; exact hcl.nv_le
      nc_le := by dsimp only [ks', K6State.putArr, K6State.putHdr]; exact hcl.nc_le
      alen_le := by dsimp only [ks', K6State.putArr, K6State.putHdr]; exact hcl.alen_le
      nassump_le := hna1
      nkl_le := by dsimp only [ks', K6State.putArr, K6State.putHdr]; exact hcl.nkl_le
      nana_le := by dsimp only [ks', K6State.putArr, K6State.putHdr]; exact hcl.nana_le
      cl_wf := fun cid hc => by
        dsimp only [ks', k6ClauseSize, k6ClauseOff, k6ClauseLits, K6State.putArr, K6State.putHdr]
          at hc ⊢
        exact hcl.cl_wf cid hc
      cl_mono := fun c1 c2 h12 h2c => by
        dsimp only [ks', k6ClauseSize, k6ClauseOff, K6State.putArr, K6State.putHdr] at h2c ⊢
        exact hcl.cl_mono c1 c2 h12 h2c
      incons_ok := by dsimp only [ks', K6State.putArr, K6State.putHdr]; exact hcl.incons_ok
      assump_ok := fun i hi => by
        dsimp only [ks', K6State.putArr, K6State.putHdr] at hi ⊢
        have hi0 : i = 0 := by simp at hi; omega
        subst hi0; rw [List.getElem?_set_self ha0_lt, Option.getD_some]; exact ha0
      flags_clean := by dsimp only [ks', K6State.putArr, K6State.putHdr]; exact hcl.flags_clean },
    by dsimp only [ks', K6State.putArr, K6State.putHdr]; exact hinv.watches,
    k6BaseAssignOk_cast hinv.assign rfl rfl rfl rfl rfl rfl rfl rfl rfl,
    by dsimp only [ks', K6State.putArr, K6State.putHdr]; exact hinv.reasons⟩,
    by dsimp only [ks', K6State.putArr, K6State.putHdr],
    by dsimp only [ks', K6State.putArr, K6State.putHdr], ?_,
    by dsimp only [ks', K6State.putArr, K6State.putHdr]⟩
  unfold k6AssumpLits; dsimp only [ks', K6State.putArr, K6State.putHdr]
  cases h : ks.assump with
  | nil => simp [h] at ha0_lt
  | cons x xs => simp [List.set, List.take]

theorem k6Inv_set_assump2 {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    {a0 a1 : BitVec 32} (ha0 : a0.toNat < 2 * ks.nv.toNat) (ha1 : a1.toNat < 2 * ks.nv.toNat)
    (hinv : K6Inv L P ks) :
    let ks' := ((ks.putHdr .nassump 2#32).putArr .assump 0 a0).putArr .assump 1 a1
    K6Inv L P ks' ∧ ks'.nv = ks.nv ∧ ks'.nassump = 2#32 ∧
    k6AssumpLits ks' = [a0.toNat, a1.toNat] ∧ ks'.neq = ks.neq := by
  intro ks'
  have hmL := L.hmaxV
  have hcl := hinv.clauses
  have hna2 : ks'.nassump.toNat ≤ L.maxV := by
    dsimp only [ks', K6State.putArr, K6State.putHdr]; simp; omega
  have ha1_lt : 1 < ks.assump.length := by rw [hinv.shapes.assump_len]; omega
  refine ⟨⟨((hinv.shapes.putHdr .nassump 2#32).putArr .assump 0 a0).putArr .assump 1 a1,
    { acap_eq := by dsimp only [ks', K6State.putArr, K6State.putHdr]; exact hcl.acap_eq
      max_v_eq := by dsimp only [ks', K6State.putArr, K6State.putHdr]; exact hcl.max_v_eq
      max_orig_eq := by dsimp only [ks', K6State.putArr, K6State.putHdr]; exact hcl.max_orig_eq
      max_cl_eq := by dsimp only [ks', K6State.putArr, K6State.putHdr]; exact hcl.max_cl_eq
      nv_le := by dsimp only [ks', K6State.putArr, K6State.putHdr]; exact hcl.nv_le
      nc_le := by dsimp only [ks', K6State.putArr, K6State.putHdr]; exact hcl.nc_le
      alen_le := by dsimp only [ks', K6State.putArr, K6State.putHdr]; exact hcl.alen_le
      nassump_le := hna2
      nkl_le := by dsimp only [ks', K6State.putArr, K6State.putHdr]; exact hcl.nkl_le
      nana_le := by dsimp only [ks', K6State.putArr, K6State.putHdr]; exact hcl.nana_le
      cl_wf := fun cid hc => by
        dsimp only [ks', k6ClauseSize, k6ClauseOff, k6ClauseLits, K6State.putArr, K6State.putHdr]
          at hc ⊢
        exact hcl.cl_wf cid hc
      cl_mono := fun c1 c2 h12 h2c => by
        dsimp only [ks', k6ClauseSize, k6ClauseOff, K6State.putArr, K6State.putHdr] at h2c ⊢
        exact hcl.cl_mono c1 c2 h12 h2c
      incons_ok := by dsimp only [ks', K6State.putArr, K6State.putHdr]; exact hcl.incons_ok
      assump_ok := fun i hi => by
        dsimp only [ks', K6State.putArr, K6State.putHdr] at hi ⊢
        have h2 : i < 2 := by simp at hi; exact hi
        rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · rw [List.getElem?_set_ne (by decide), List.getElem?_set_self (by omega),
            Option.getD_some]
          exact ha0
        · rw [List.getElem?_set_self (by simp; exact ha1_lt), Option.getD_some]; exact ha1
      flags_clean := by dsimp only [ks', K6State.putArr, K6State.putHdr]; exact hcl.flags_clean },
    by dsimp only [ks', K6State.putArr, K6State.putHdr]; exact hinv.watches,
    k6BaseAssignOk_cast hinv.assign rfl rfl rfl rfl rfl rfl rfl rfl rfl,
    by dsimp only [ks', K6State.putArr, K6State.putHdr]; exact hinv.reasons⟩,
    by dsimp only [ks', K6State.putArr, K6State.putHdr],
    by dsimp only [ks', K6State.putArr, K6State.putHdr], ?_,
    by dsimp only [ks', K6State.putArr, K6State.putHdr]⟩
  unfold k6AssumpLits; dsimp only [ks', K6State.putArr, K6State.putHdr]
  cases h : ks.assump with
  | nil => simp [h] at ha1_lt
  | cons x0 tl0 =>
    cases tl0 with
    | nil => simp [h] at ha1_lt
    | cons x1 tl1 => simp [List.set, List.take]

theorem k6Inv_set_neq {L : K6Layout} {P : (Nat → Bool) → Prop} {ks : K6State}
    (v : BitVec 32) (hinv : K6Inv L P ks) :
    K6Inv L P (ks.putHdr .neq v) :=
  ⟨hinv.shapes.putHdr .neq v,
   k6ClausesOk_cast hinv.clauses (by k6_field) (by k6_field) (by k6_field) (by k6_field)
     (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field)
     (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field),
   by dsimp only [K6State.putHdr]; exact hinv.watches,
   k6BaseAssignOk_cast hinv.assign (by k6_field) (by k6_field) (by k6_field) (by k6_field)
     (by k6_field) (by k6_field) (by k6_field) (by k6_field) (by k6_field),
   by dsimp only [K6State.putHdr]; exact hinv.reasons⟩

theorem m6_partOk_drop_head {nv ncls : Nat} {scr heads : List (BitVec 32)}
    (hp : M6PartitionOk nv ncls scr heads) : M6PartitionOk nv (ncls - 1) scr heads :=
  ⟨Nat.le_trans (Nat.sub_le _ _) hp.1, hp.2.1, fun ci hci => hp.2.2 ci (by omega)⟩

theorem m6_partOk_unlink {nv ncls : Nat} {scr heads : List (BitVec 32)}
    {a c : BitVec 32} (hnv_lt : nv ≤ 2 ^ 31) (ha : a.toNat < nv)
    (hc_eq : c = scr[k6PhtNext + a.toNat]?.getD 0xFFFFFFFF#32)
    (hc : c.toNat < nv) (hbd_a : k6PhtNext + a.toNat < scr.length)
    (hbd : k6PhtNext + c.toNat < scr.length)
    (hp : M6PartitionOk nv ncls scr heads) :
    let v := scr[k6PhtNext + c.toNat]'hbd
    let scr' := scr.set (k6PhtNext + a.toNat) v
    M6PartitionOk nv ncls scr' heads ∧
    M6PartitionOk nv (ncls - 1) scr' heads := by
  intro v scr'
  have hc_lt_a : c.toNat < a.toNat := by
    have ha' := hp.2.1 a.toNat ha
    rw [← hc_eq] at ha'
    rcases ha' with rfl | hlt
    · exfalso; exact absurd hc (by rw [show (0xFFFFFFFF#32).toNat = 4294967295 from rfl]; omega)
    · exact hlt
  have hv_ok : v = 0xFFFFFFFF#32 ∨ v.toNat < a.toNat := by
    have hc' := hp.2.1 c.toNat hc
    dsimp only [v]; rw [List.getElem?_eq_getElem hbd, Option.getD_some] at hc'
    rcases hc' with hff | hlt
    · exact Or.inl hff
    · exact Or.inr (Nat.lt_trans hlt hc_lt_a)
  have hp' : M6PartitionOk nv ncls scr' heads := by
    refine ⟨hp.1, fun i hi => ?_, hp.2.2⟩
    by_cases hia : i = a.toNat
    · subst hia; dsimp only [scr']
      rw [List.getElem?_set_self hbd_a, Option.getD_some]; exact hv_ok
    · dsimp only [scr']; rw [List.getElem?_set_ne (by omega)]; exact hp.2.1 i hi
  exact ⟨hp', m6_partOk_drop_head hp'⟩

private theorem m6_coneModelSet_unsat_unit {F_cur : List (List Nat)} {ws1 : List (BitVec 32)}
    {nv a : Nat} (_ha : a < 2 * nv)
    (h : ∀ β, ConeModelSet F_cur ws1 nv β → ¬ (unitsCnf [a]).Sat β) :
    SemEntails (ConeModelSet F_cur ws1 nv) [a ^^^ 1] ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [m6ConeLift ws1 (a ^^^ 1)]) := by
  have hsem : SemEntails (ConeModelSet F_cur ws1 nv) [a ^^^ 1] := fun β hβ => by
    rw [show a ^^^ 1 = litNeg a from rfl, sat_cnfClause_litNeg_iff]
    intro hsat
    exact h β hβ ((sat_unitsCnf_iff β [a]).mpr fun l hl => by
      simp only [List.mem_singleton] at hl; subst hl; exact hsat)
  refine ⟨hsem, ?_⟩
  rw [CNF.entails_clause_def]; intro α hα
  have hsat := hsem (fun i => α (ws1[i]?.getD 0#32).toNat) ⟨α, hα, fun _ _ => rfl⟩
  exact (coneLift_sat_iff (α := α) (cone_v := ws1) (l := a ^^^ 1)).mp hsat

theorem m6_coneModelSet_unsat_bin {F_cur : List (List Nat)} {ws1 : List (BitVec 32)}
    {nv a0 a1 : Nat} (_ha0 : a0 < 2 * nv) (_ha1 : a1 < 2 * nv)
    (h : ∀ β, ConeModelSet F_cur ws1 nv β → ¬ (unitsCnf [a0, a1]).Sat β) :
    SemEntails (ConeModelSet F_cur ws1 nv) [a0 ^^^ 1, a1 ^^^ 1] ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause
      [m6ConeLift ws1 (a0 ^^^ 1), m6ConeLift ws1 (a1 ^^^ 1)]) := by
  have hsem : SemEntails (ConeModelSet F_cur ws1 nv) [a0 ^^^ 1, a1 ^^^ 1] := fun β hβ => by
    exact Classical.byContradiction fun hnot => by
      have h0 : (cnfClause [a0]).Sat β := Classical.byContradiction fun hn0 =>
        hnot ((clause_sat_cnfClause_iff β [a0 ^^^ 1, a1 ^^^ 1]).mpr ⟨a0 ^^^ 1,
          List.mem_cons_self .., (sat_cnfClause_singleton β (a0 ^^^ 1)).mp
            ((sat_cnfClause_litNeg_iff β a0).mpr hn0)⟩)
      have h1 : (cnfClause [a1]).Sat β := Classical.byContradiction fun hn1 =>
        hnot ((clause_sat_cnfClause_iff β [a0 ^^^ 1, a1 ^^^ 1]).mpr ⟨a1 ^^^ 1,
          List.mem_cons_of_mem _ (List.mem_cons_self ..),
          (sat_cnfClause_singleton β (a1 ^^^ 1)).mp ((sat_cnfClause_litNeg_iff β a1).mpr hn1)⟩)
      exact h β hβ ((sat_unitsCnf_iff β [a0, a1]).mpr fun l hl => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl <;> assumption)
  refine ⟨hsem, ?_⟩
  rw [CNF.entails_clause_def]; intro α hα
  have hsat := hsem (fun i => α (ws1[i]?.getD 0#32).toNat) ⟨α, hα, fun _ _ => rfl⟩
  have hl := (semEntails_coneModelSet_of_entails (F_cur := F_cur) (ws1 := ws1)
    (nv := nv) (lits := [a0 ^^^ 1, a1 ^^^ 1]))
  obtain ⟨x, hx, hxs⟩ := (clause_sat_cnfClause_iff _ _).mp hsat
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact (clause_sat_cnfClause_iff _ _).mpr ⟨m6ConeLift ws1 (a0 ^^^ 1), List.mem_cons_self ..,
      (sat_cnfClause_singleton α _).mp
        ((coneLift_sat_iff (α := α) (cone_v := ws1) (l := a0 ^^^ 1)).mp
          ((sat_cnfClause_singleton _ _).mpr hxs))⟩
  · exact (clause_sat_cnfClause_iff _ _).mpr ⟨m6ConeLift ws1 (a1 ^^^ 1),
      List.mem_cons_of_mem _ (List.mem_cons_self ..),
      (sat_cnfClause_singleton α _).mp
        ((coneLift_sat_iff (α := α) (cone_v := ws1) (l := a1 ^^^ 1)).mp
          ((sat_cnfClause_singleton _ _).mpr hxs))⟩

theorem m6_nat_xor1_cases (x : Nat) :
    x ^^^ 1 = if x % 2 = 0 then x + 1 else x - 1 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor]
  rcases i with _ | i
  · simp only [Nat.testBit_zero, show (1 : Nat) % 2 = 1 from rfl, decide_true, Bool.xor_true]
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h] <;> omega
  · simp only [Nat.testBit_succ, show (1 : Nat) / 2 = 0 from rfl, Nat.zero_testBit,
      Bool.xor_false]
    split <;> rename_i h
    · rw [show (x + 1) / 2 = x / 2 by omega]
    · rw [show (x - 1) / 2 = x / 2 by omega]

private theorem m6_nat_xor1_even (x : Nat) : (2 * x) ^^^ 1 = 2 * x + 1 := by
  rcases k6_nat_xor1_cases (2 * x) with ⟨_, h⟩ | ⟨h, _⟩
  · have hd : 2 * x / 2 = x := by omega
    rwa [hd] at h
  · exfalso; omega

private theorem m6_nat_xor1_odd (x : Nat) : (2 * x + 1) ^^^ 1 = 2 * x := by
  rcases k6_nat_xor1_cases (2 * x + 1) with ⟨h, _⟩ | ⟨_, h⟩
  · exfalso; omega
  · omega

private theorem m6_unit_lit_align {ws1 : List (BitVec 32)} {i gv wf : BitVec 32}
    (hi : i.toNat < 2 ^ 31) (hgv : gv.toNat < 2 ^ 31)
    (hws : (ws1[i.toNat]?.getD 0#32).toNat = gv.toNat) (hwf : wf = 0#32 ∨ wf = 1#32) :
    let test_lit := (i <<< (1 : Nat)) ||| wf
    let gl := (gv <<< (1 : Nat)) ||| (1#32 - wf)
    test_lit.toNat = 2 * i.toNat + wf.toNat ∧
    gl.toNat = m6ConeLift ws1 (test_lit.toNat ^^^ 1) ∧
    gl.toNat = 2 * gv.toNat + (1 - wf.toNat) := by
  intro test_lit gl
  have hwf_lt : wf.toNat < 2 := by rcases hwf with rfl | rfl <;> decide
  have h1w_lt : (1#32 - wf).toNat < 2 := by rcases hwf with rfl | rfl <;> decide
  have htl : test_lit.toNat = 2 * i.toNat + wf.toNat :=
    m6_bv32_shl1_or_pol i wf hi hwf_lt
  have hgl : gl.toNat = 2 * gv.toNat + (1 - wf.toNat) := by
    rw [m6_bv32_shl1_or_pol gv (1#32 - wf) hgv h1w_lt]
    rcases hwf with rfl | rfl <;> rfl
  have hlift : m6ConeLift ws1 (test_lit.toNat ^^^ 1) = 2 * gv.toNat + (1 - wf.toNat) := by
    have hc := coneLift_of_tmk_pair (cone_v := ws1) (idx := i.toNat) (v := gv.toNat)
      (l := 2 * gv.toNat + (1 - wf.toNat)) hws (by omega)
    rw [htl]
    rcases hwf with rfl | rfl
    · have hx : (2 * i.toNat + (0#32).toNat) ^^^ 1 =
          2 * i.toNat + (2 * gv.toNat + (1 - (0#32).toNat)) % 2 := by
        rw [show (0#32).toNat = 0 from rfl, Nat.add_zero, m6_nat_xor1_even i.toNat]; omega
      rw [hx]; exact hc
    · have hx : (2 * i.toNat + (1#32).toNat) ^^^ 1 =
          2 * i.toNat + (2 * gv.toNat + (1 - (1#32).toNat)) % 2 := by
        rw [show (1#32).toNat = 1 from rfl, m6_nat_xor1_odd i.toNat]; omega
      rw [hx]; exact hc
  exact ⟨htl, hgl.trans hlift.symm, hgl⟩

theorem m6_bin_lits_align {ws1 : List (BitVec 32)} {a c gv_a gv_c pol : BitVec 32}
    (ha : a.toNat < 2 ^ 31) (hc : c.toNat < 2 ^ 31)
    (hgva : gv_a.toNat < 2 ^ 31) (hgvc : gv_c.toNat < 2 ^ 31)
    (hwsa : (ws1[a.toNat]?.getD 0#32).toNat = gv_a.toNat)
    (hwsc : (ws1[c.toNat]?.getD 0#32).toNat = gv_c.toNat)
    (hpol : pol = 0#32 ∨ pol = 1#32) :
    let la := gv_a <<< (1 : Nat)
    let lc := (gv_c <<< (1 : Nat)) ||| pol
    let a0_1 := a <<< (1 : Nat)
    let a1_1 := (c <<< (1 : Nat)) ||| (1#32 ^^^ pol)
    let a0_2 := (a <<< (1 : Nat)) ||| 1#32
    let a1_2 := (c <<< (1 : Nat)) ||| pol
    a0_1.toNat = 2 * a.toNat ∧ a1_1.toNat = 2 * c.toNat + (1#32 ^^^ pol).toNat ∧
    a0_2.toNat = 2 * a.toNat + 1 ∧ a1_2.toNat = 2 * c.toNat + pol.toNat ∧
    la.toNat = 2 * gv_a.toNat ∧ lc.toNat = 2 * gv_c.toNat + pol.toNat ∧
    ((a <<< (1 : Nat)) ^^^ 1#32).toNat = a0_1.toNat ^^^ 1 ∧
    ((c <<< (1 : Nat)) ||| pol).toNat = a1_1.toNat ^^^ 1 ∧
    (a <<< (1 : Nat)).toNat = a0_2.toNat ^^^ 1 ∧
    (((c <<< (1 : Nat)) ||| pol) ^^^ 1#32).toNat = a1_2.toNat ^^^ 1 ∧
    (la ^^^ 1#32).toNat = m6ConeLift ws1 (a0_1.toNat ^^^ 1) ∧
    lc.toNat = m6ConeLift ws1 (a1_1.toNat ^^^ 1) ∧
    la.toNat = m6ConeLift ws1 (a0_2.toNat ^^^ 1) ∧
    (lc ^^^ 1#32).toNat = m6ConeLift ws1 (a1_2.toNat ^^^ 1) := by
  intro la lc a0_1 a1_1 a0_2 a1_2
  have hp_lt : pol.toNat < 2 := by rcases hpol with rfl | rfl <;> decide
  have hxp_lt : (1#32 ^^^ pol).toNat < 2 := by rcases hpol with rfl | rfl <;> decide
  have ha01 : a0_1.toNat = 2 * a.toNat := m6_bv32_shl1_lt ha
  have ha11 : a1_1.toNat = 2 * c.toNat + (1#32 ^^^ pol).toNat :=
    m6_bv32_shl1_or_pol c (1#32 ^^^ pol) hc hxp_lt
  have ha02 : a0_2.toNat = 2 * a.toNat + 1 := m6_bv32_shl1_or_pol a 1#32 ha (by decide)
  have ha12 : a1_2.toNat = 2 * c.toNat + pol.toNat := m6_bv32_shl1_or_pol c pol hc hp_lt
  have hla : la.toNat = 2 * gv_a.toNat := m6_bv32_shl1_lt hgva
  have hlc : lc.toNat = 2 * gv_c.toNat + pol.toNat := m6_bv32_shl1_or_pol gv_c pol hgvc hp_lt
  refine ⟨ha01, ha11, ha02, ha12, hla, hlc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [BitVec.toNat_xor, show (1#32).toNat = 1 from rfl]
  · rw [ha12, ha11]; rcases hpol with rfl | rfl
    · simpa [show (0#32).toNat = 0 from rfl, show (1#32 ^^^ 0#32).toNat = 1 from rfl] using
        (m6_nat_xor1_odd c.toNat).symm
    · simpa [show (1#32).toNat = 1 from rfl, show (1#32 ^^^ 1#32).toNat = 0 from rfl] using
        (m6_nat_xor1_even c.toNat).symm
  · rw [ha01, ha02]; exact (m6_nat_xor1_odd a.toNat).symm
  · rw [BitVec.toNat_xor, show (1#32).toNat = 1 from rfl]
  · have hc1 := coneLift_of_tmk_pair (cone_v := ws1) (idx := a.toNat) (v := gv_a.toNat)
      (l := 2 * gv_a.toNat + 1) hwsa (by omega)
    rw [BitVec.toNat_xor, show (1#32).toNat = 1 from rfl, hla, ha01,
      m6_nat_xor1_even gv_a.toNat, m6_nat_xor1_even a.toNat]
    simpa [show (2 * gv_a.toNat + 1) % 2 = 1 by omega] using hc1.symm
  · rw [hlc, ha11]; rcases hpol with rfl | rfl
    · have hc2 := coneLift_of_tmk_pair (cone_v := ws1) (idx := c.toNat) (v := gv_c.toNat)
        (l := 2 * gv_c.toNat) hwsc (by omega)
      rw [show (0#32).toNat = 0 from rfl, show (1#32 ^^^ 0#32).toNat = 1 from rfl,
        m6_nat_xor1_odd c.toNat]
      simpa [show (2 * gv_c.toNat) % 2 = 0 by omega] using hc2.symm
    · have hc2 := coneLift_of_tmk_pair (cone_v := ws1) (idx := c.toNat) (v := gv_c.toNat)
        (l := 2 * gv_c.toNat + 1) hwsc (by omega)
      rw [show (1#32).toNat = 1 from rfl, show (1#32 ^^^ 1#32).toNat = 0 from rfl,
        show 2 * c.toNat + 0 = 2 * c.toNat by omega, m6_nat_xor1_even c.toNat]
      simpa [show (2 * gv_c.toNat + 1) % 2 = 1 by omega] using hc2.symm
  · have hc3 := coneLift_of_tmk_pair (cone_v := ws1) (idx := a.toNat) (v := gv_a.toNat)
      (l := 2 * gv_a.toNat) hwsa (by omega)
    rw [hla, ha02, m6_nat_xor1_odd a.toNat]
    simpa [show (2 * gv_a.toNat) % 2 = 0 by omega] using hc3.symm
  · rw [BitVec.toNat_xor, show (1#32).toNat = 1 from rfl, hlc, ha12]
    rcases hpol with rfl | rfl
    · have hc4 := coneLift_of_tmk_pair (cone_v := ws1) (idx := c.toNat) (v := gv_c.toNat)
        (l := 2 * gv_c.toNat + 1) hwsc (by omega)
      rw [show (0#32).toNat = 0 from rfl, show 2 * c.toNat + 0 = 2 * c.toNat by omega,
        show 2 * gv_c.toNat + 0 = 2 * gv_c.toNat by omega, m6_nat_xor1_even gv_c.toNat,
        m6_nat_xor1_even c.toNat]
      simpa [show (2 * gv_c.toNat + 1) % 2 = 1 by omega] using hc4.symm
    · have hc4 := coneLift_of_tmk_pair (cone_v := ws1) (idx := c.toNat) (v := gv_c.toNat)
        (l := 2 * gv_c.toNat) hwsc (by omega)
      rw [show (1#32).toNat = 1 from rfl, m6_nat_xor1_odd gv_c.toNat, m6_nat_xor1_odd c.toNat]
      simpa [show (2 * gv_c.toNat) % 2 = 0 by omega] using hc4.symm

theorem m6_eqBufOk_push {F_cur : List (List Nat)} {s : FullState} {neq la lc : BitVec 32}
    (heq : M6EqBufOk F_cur s neq.toNat) (hne : neq.toNat < s.core.cur_vars)
    (hla : la.toNat < 2 * s.core.cur_vars) (hlc : lc.toNat < 2 * s.core.cur_vars)
    (hlv : LitEquiv (cnfOfClauses F_cur) la.toNat lc.toNat)
    (h2lt : 2 * neq.toNat + 1 < s.scratch.work_stk2.length) :
    let ws2' := (s.scratch.work_stk2.set (2 * neq.toNat) la).set (2 * neq.toNat + 1) lc
    let s' := { s with scratch := { s.scratch with work_stk2 := ws2' } }
    M6EqBufOk F_cur s' (neq.toNat + 1) := by
  intro ws2' s'
  refine ⟨by dsimp [s']; omega, fun i hi => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
  · dsimp only [s', ws2']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact heq.2 i hlt
  · dsimp only [s', ws2']
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega), Option.getD_some,
      List.getElem?_set_self (by simp; exact h2lt), Option.getD_some]
    exact ⟨hla, hlc, hlv⟩

theorem m6_eqBufOk_congr {F_cur : List (List Nat)} {s s' : FullState} {neq : Nat}
    (h : M6EqBufOk F_cur s neq) (hcv : s'.core.cur_vars = s.core.cur_vars)
    (hws2 : s'.scratch.work_stk2 = s.scratch.work_stk2) : M6EqBufOk F_cur s' neq := by
  refine ⟨hcv ▸ h.1, fun i hi => ?_⟩
  have h0 := h.2 i hi; dsimp only; rw [hws2, hcv]; exact h0

theorem m6_k6StateOfScratch_incons {L : K6Layout} {scr : List (BitVec 32)}
    (hbd : L.k6Base + 6 < scr.length) :
    (k6StateOfScratch L scr).incons = scr[L.k6Base + 6]'hbd := by
  unfold k6StateOfScratch K6State.ofSlab
  simp only [List.getElem?_drop, List.getElem?_eq_getElem hbd, Option.getD_some]

theorem m6_k6StateOfScratch_neq {L : K6Layout} {scr : List (BitVec 32)}
    (hbd : L.k6Base + 24 < scr.length) :
    (k6StateOfScratch L scr).neq = scr[L.k6Base + 24]'hbd := by
  unfold k6StateOfScratch K6State.ofSlab
  simp only [List.getElem?_drop, List.getElem?_eq_getElem hbd, Option.getD_some]

/-! ## 2. `full_m6_sweep_units_wp` (`27/39`) -/

private structure M6UnitState (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 : FullState) (nv : BitVec 32) (rbit : BitVec 32) (R : Mem 64 → Prop)
    (m : Mem 64) where
  rbit_le : rbit.toNat ≤ 64
  st : FullState
  inv : FullDenseInvW c F0 F_cur st
  cv : st.core.cur_vars = s0.core.cur_vars
  fuel : st.core.fuel.toNat ≤ s0.core.fuel.toNat
  ws : st.scratch.work_stk1 = s0.scratch.work_stk1
  tmk : st.scratch.tarjan_mark = s0.scratch.tarjan_mark
  trh : st.scratch.tarjan_reach = s0.scratch.tarjan_reach
  cone : M6SweepConeOk F_cur st nv.toNat
  mem : (FullMem c st ⋆ R) m

theorem full_m6_sweep_units_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hFlip : M6EnvSpec Γ "full_k6_flip" k6FlipSpec)
    (hRef : M6EnvSpec Γ "full_m6_sweep_refine_sig" m6SweepRefineSigSpec)
    (hSolve : M6EnvSpec Γ "full_m6_sweep_solve" m6SweepSolveSpec)
    (hAddU : M6EnvSpec Γ "full_add_unit" Full.fullAddUnitSpec)
    (hLive : M6EnvSpec Γ "full_k512_add_live_m6" k6AddLiveSpec)
    (hRearm : M6EnvSpec Γ "full_m6_sweep_rearm" m6SweepRearmSpec) :
    ∀ args m Q X, m6SweepUnitsSpec args m Q X →
      Func.wp Γ full_m6_sweep_units_body args m Q X := by
  rintro ⟨h, nv, rbit_in, tick_lim, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv, hcone, hrb_in, hm, hQ⟩
  obtain ⟨hnv1, hnv_mv, hnv_cv, hws_lt, hK_scr, hge_s, hlt_s, hnv_eq⟩ := hcone
  have hlen := hinv.1
  have hcv_le := hlen.core_ok.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hscr_len := hlen.scratch_ok.scratch_buf_len
  have hcap : k6MinScr ≤ c.scratch_cap := hscr_len ▸ hge_s
  have hnv_mx : nv.toNat ≤ 2 * c.max_vars := by omega
  let ws1 := s.scratch.work_stk1
  let tmk := s.scratch.tarjan_mark
  let P := ConeModelSet F_cur ws1 nv.toNat
  obtain ⟨L, hL_def⟩ : ∃ L : K6Layout, L = k6LayoutOfCap c.scratch_cap hcap c.hscr := ⟨_, rfl⟩
  have hL_len : L.scrLen = c.scratch_cap := by
    rw [hL_def]; exact k6LayoutOfCap_scrLen hcap c.hscr
  have hL_mv : L.maxV = k6MaxV c.scratch_cap := by rw [hL_def]; rfl
  have hmL := L.hmaxV; have haL := L.hacap
  have hnv_L : nv.toNat ≤ L.maxV := by rw [hL_mv, ← hscr_len]; exact hnv_mv
  have hK0 : K6Inv L P (k6StateOfScratch L s.scratch.scratch_buf) :=
    k6ScratchInv_to_inv (L := L) (hL_len.trans hscr_len.symm) (by rw [hscr_len]; exact hL_mv) hK_scr
  have hnv_bv : (k6StateOfScratch L s.scratch.scratch_buf).nv = nv := by
    have hL_eq : L = k6LayoutOfCap s.scratch.scratch_buf.length hge_s hlt_s :=
      (k6LayoutOfCap_eq (hL_len.trans hscr_len.symm)
        (by rw [hscr_len]; exact hL_mv) hge_s hlt_s).symm
    rw [hL_eq, hnv_eq]
    exact BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt nv.isLt])
  have hmv64_lt : k6MaxV c.scratch_cap < 2 ^ 32 := by rw [← hL_mv]; omega
  have hmv_eq : BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) = L.mv32 := by
    apply BitVec.eq_of_toNat_eq
    simp only [k6_mv32_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; rw [← hL_mv]; omega
  have hkptr_c0 : c.pScratchBuf + BitVec.setWidth 64
      ((1280 : BitVec 32) + (BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) <<<
        (1 : Nat))) * 4 = L.kPtr c.pScratchBuf := by
    rw [hmv_eq]; exact k6_ptr_base_k6Base L c.pScratchBuf
  have hpm_c0 := m6_ptr_phtMerged L c.pScratchBuf
  have hpm_end : L.phtMerged + L.maxV = L.k6Base := by
    unfold K6Layout.phtMerged K6Layout.k6Base; omega
  have hass_c0 := k6_ptr_assump L (L.kPtr c.pScratchBuf)
  have hmk_cone : ∀ (st : FullState),
      st.scratch.scratch_buf.length = c.scratch_cap → st.core.cur_vars = s.core.cur_vars →
      st.scratch.work_stk1 = ws1 → K6Inv L P (k6StateOfScratch L st.scratch.scratch_buf) →
      (k6StateOfScratch L st.scratch.scratch_buf).nv = nv →
      M6SweepConeOk F_cur st nv.toNat := fun st hsc hcv hws hK hnv => by
    have hge' : k6MinScr ≤ st.scratch.scratch_buf.length := hsc ▸ hcap
    have hlt' : st.scratch.scratch_buf.length < dimacsBound := hsc ▸ c.hscr
    have hL_c : L = k6LayoutOfCap st.scratch.scratch_buf.length hge' hlt' :=
      (k6LayoutOfCap_eq (hL_len.trans hsc.symm) (by rw [hsc]; exact hL_mv) hge' hlt').symm
    refine ⟨hnv1, by rw [hsc, ← hscr_len]; exact hnv_mv, hcv.symm ▸ hnv_cv,
      fun j hj => by rw [hws, hcv]; exact hws_lt j hj,
      K6Inv.to_scratchInv (hsc.trans hL_len.symm) (hsc ▸ hL_mv) hge' hlt' (by
        dsimp only [P] at hK; rw [hws]; exact hK),
      ⟨hge', hlt', by
        rw [← hL_c, hnv]
        exact (BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt nv.isLt])).symm⟩⟩
  clear hL_def
  unfold Func.wp full_m6_sweep_units_body
  m6_steps
  refine m6_call_max_v hMaxV (c := c) rfl ?_
  m6_to_group
  refine wp_join_group (ts := []) (fun () _ => False) (fun _ () _ h => False.elim h) ?_
  intro _ _
  m6_split
  · exfalso; have h0 := congrArg BitVec.toNat hc
    rw [hmv_eq, k6_mv32_toNat] at h0; simp at h0; omega
  m6_split
  · exfalso
    rw [← hL_mv, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc; omega
  m6_to_group
  -- Loop 1: zero `pht_merged[0..nv)`
  refine wp_loop_inv (ts := [i32])
    (fun (i, ()) m1 => i.toNat ≤ nv.toNat ∧ ∃ scr1 : List (BitVec 32),
      scr1.length = c.scratch_cap ∧ K6Inv L P (k6StateOfScratch L scr1) ∧
      (k6StateOfScratch L scr1).nv = nv ∧
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr1 } } ⋆ R) m1)
    (fun (i, ()) _ => nv.toNat - i.toNat)
    (fun _ hJ0 => by
      m6_steps
      exact hJ0 (0#32, ()) m ⟨Nat.zero_le _, s.scratch.scratch_buf, hscr_len, hK0, hnv_bv, hm⟩)
    (fun _ (i, ()) m1 ⟨hi_le, scr1, hsl1, hK1, hnv1_eq, hm1⟩ hJ0 => by
      m6_split
      · have hi_lt : i.toNat < nv.toNat := hc
        have hi_mv : i.toNat < L.maxV := Nat.lt_of_lt_of_le hi_lt hnv_L
        have hi1 : (i + 1#32).toNat = i.toNat + 1 := m6_bv32_add1 (by omega)
        change wp _ _ _ _ _
        c0_hsteps_nogrp; try dsimp only [Prod.fst]; try rw [hmv_eq]; try rw [hpm_c0]
        open scoped M6Var2PhtMem in m6_steps
        have hlt_k6 : L.phtMerged + i.toNat < L.k6Base := by omega
        let scr1' := scr1.set (L.phtMerged + i.toNat) 0#32
        have hm1' : (FullMem c { s with scratch :=
            { s.scratch with scratch_buf := scr1' } } ⋆ R) m := by
          simpa only [scr1', show (0 : BitVec 32) = 0#32 from rfl] using hm
        exact hJ0 (i + 1#32, ()) m (by dsimp only; rw [hi1]; exact Nat.sub_lt_sub_left hi_lt (by
          omega))
          ⟨by omega, scr1', List.length_set.trans hsl1, by
            rw [m6_k6Inv_of_prefix_set hlt_k6 hK1]; exact hK1,
           by rw [m6_k6Inv_of_prefix_set hlt_k6 hK1, hnv1_eq], hm1'⟩
      · let s1 : FullState := { s with scratch := { s.scratch with scratch_buf := scr1 } }
        have hinv1 := m6_fullDenseInvW_with_scratch hinv hsl1 (fuel' := s.core.fuel)
        have hcone1 := hmk_cone s1 hsl1 rfl rfl hK1 hnv1_eq
        m6_to_group
        refine wp_join_group (ts := [i64])
          (fun (_smask0, ()) ms => ms = m1)
          (fun _ (smask0, ()) ms hms => by
            subst ms
            m6_to_group
            refine wp_loop_inv (ts := [i32, i32, i64])
              (fun (i, rbit, _smask, ()) ml => i.toNat ≤ nv.toNat ∧
                ∃ _ : M6UnitState c F0 F_cur s nv rbit R ml, True)
              (fun (i, _, _, ()) _ => nv.toNat - i.toNat)
              (fun _ hJu => by
                m6_steps
                exact hJu (0#32, rbit_in, smask0, ()) m1
                  ⟨Nat.zero_le _, ⟨hrb_in, s1, hinv1, rfl, le_refl _, rfl, rfl, rfl, hcone1, hm1⟩,
                   trivial⟩)
              (fun _ (i, rbit, smask, ()) ml
                  ⟨hi_le, ⟨hrb_le, sL, hinvL, hcvL, hfuelL, hwsL, htmkL, htrhL, hconeL, hml⟩, _⟩
                  hJu => by
                clear hm hm1
                m6_to_group
                refine wp_join_group (ts := [])
                  (fun () m_ex => m_ex = ml)
                  (fun _ () m_ex hm_ex => by
                    subst hm_ex
                    m6_to_group; refine wp_unroll_group fun _ _ => ?_
                    m6_split
                    · have hinc : sL.core.inconsistent ≠ 0#64 := hc
                      have huns : F0.Unsat :=
                        hinvL.2.1.ext_sound.2 (hinvL.2.1.inconsistent_sound hinc)
                      m6_steps
                      exact hQ 0xFFFFFFFFFFFFFFFF#64 sL m_ex hinvL hcvL hfuelL hwsL htmkL htrhL
                        hconeL (fun _ => huns) (fun h => absurd rfl h) hml
                    · m6_steps
                      have hrb64 : (rbit.setWidth 64).toNat ≤ 64 := by
                        rw [bv_c0_zext32_64]; exact hrb_le
                      have hne_ff : rbit.setWidth 64 ≠ 0xFFFFFFFFFFFFFFFF#64 := by
                        intro h; rw [h] at hrb64; revert hrb64; decide
                      exact hQ (rbit.setWidth 64) sL m_ex hinvL hcvL hfuelL hwsL htmkL htrhL
                        hconeL (fun h => absurd h hne_ff) (fun _ => hrb64) hml)
                  (fun _ hJex => by
                    have hlenL := hinvL.1
                    have hscrL_len := hlenL.scratch_ok.scratch_buf_len
                    m6_split; rotate_left; · m6_steps; exact hJex () ml rfl
                    m6_split; rotate_left; · m6_steps; exact hJex () ml rfl
                    m6_split; rotate_left; · m6_steps; exact hJex () ml rfl
                    change wp _ _ _ _ _
                    c0_hsteps_nogrp; try dsimp only [Prod.fst]; try rw [hkptr_c0]; try rw [hmv_eq]
                    open scoped FullK6DynMem in m6_split
                    rotate_left; · m6_steps; exact hJex () ml rfl
                    have hi_lt : i.toNat < nv.toNat := ‹_›
                    have hi_mv : i.toNat < L.maxV := Nat.lt_of_lt_of_le hi_lt hnv_L
                    have hi1 : (i + 1#32).toNat = i.toNat + 1 := m6_bv32_add1 (by omega)
                    have hwsL_len := hlenL.scratch_ok.work_stk1_len
                    have hvalL_len := hlenL.core_ok.vals_len
                    have hsigL_len := hlenL.scratch_ok.sim_sig_len
                    have hKL : K6Inv L P (k6StateOfScratch L sL.scratch.scratch_buf) :=
                      k6ScratchInv_to_inv (L := L) (hL_len.trans hscrL_len.symm)
                        (by rw [hscrL_len]; exact hL_mv) (by
                          dsimp only [P, ws1]; rw [← hwsL]; exact hconeL.2.2.2.2.1)
                    have hnvL : (k6StateOfScratch L sL.scratch.scratch_buf).nv = nv := by
                      have hcan := hconeL.2.2.2.2.2
                      rcases hcan with ⟨hgeL, hltL, heqL⟩
                      rw [← k6LayoutOfCap_eq (hL_len.trans hscrL_len.symm)
                        (by rw [hscrL_len]; exact hL_mv) hgeL hltL]
                      rw [heqL]
                      exact BitVec.eq_of_toNat_eq
                        (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt nv.isLt])
                    have hi_ws : (i.setWidth 64).toNat < sL.scratch.work_stk1.length := by
                      rw [hwsL_len, bv_c0_zext32_64]; omega
                    let gv := sL.scratch.work_stk1[(i.setWidth 64).toNat]'hi_ws
                    have hgv_eq_ws : (ws1[i.toNat]?.getD 0#32).toNat = gv.toNat := by
                      dsimp only [gv, ws1]
                      rw [← hwsL, List.getElem?_eq_getElem (by rw [hwsL_len]; omega),
                        Option.getD_some]
                      exact congrArg BitVec.toNat (m6_list_getElem_congr (bv_c0_zext32_64 i)
                        (by rw [hwsL_len]; omega) (by rw [hwsL_len]; omega)).symm
                    have hgv_lt : gv.toNat < s.core.cur_vars := by
                      rw [← hgv_eq_ws]; exact hws_lt i.toNat hi_lt
                    have hgv_ltL : gv.toNat < sL.core.cur_vars := hcvL ▸ hgv_lt
                    have h2gv_lt :
                        ((gv <<< (1 : Nat)).setWidth 64).toNat < sL.core.vals.length := by
                      rw [hvalL_len, bv_c0_zext32_64, m6_bv32_shl1_lt (by omega)]; omega
                    m6_split
                    · -- `vals[gv << 1] != 0`: mark merged and continue
                      change wp _ _ _ _ _
                      c0_hsteps_nogrp; try dsimp only [Prod.fst]; try rw [hmv_eq]; try rw [hpm_c0]
                      open scoped M6Var2PhtMem in m6_steps
                      have hlt_k6 : L.phtMerged + i.toNat < L.k6Base := by omega
                      let scrM := sL.scratch.scratch_buf.set (L.phtMerged + i.toNat) 1#32
                      let sM : FullState :=
                        { sL with scratch := { sL.scratch with scratch_buf := scrM } }
                      have hslM : scrM.length = c.scratch_cap := List.length_set.trans hscrL_len
                      have hKM : K6Inv L P (k6StateOfScratch L scrM) := by
                        rw [m6_k6Inv_of_prefix_set hlt_k6 hKL]; exact hKL
                      have hnvM : (k6StateOfScratch L scrM).nv = nv := by
                        rw [m6_k6Inv_of_prefix_set hlt_k6 hKL, hnvL]
                      have hinvM := m6_fullDenseInvW_with_scratch hinvL hslM (fuel' := sL.core.fuel)
                      exact hJu (i + 1#32, rbit, smask, ()) _
                        (by dsimp only; rw [hi1]; exact Nat.sub_lt_sub_left hi_lt (by omega))
                        ⟨by omega, ⟨hrb_le, sM, hinvM, hcvL, hfuelL, hwsL, htmkL, htrhL,
                         hmk_cone sM hslM hcvL hwsL hKM hnvM, by assumption⟩, trivial⟩
                    · -- Unassigned `gv`: check signature
                      have hgv_sig : (gv.setWidth 64).toNat < sL.scratch.sim_sig.length := by
                        rw [hsigL_len, bv_c0_zext32_64]; omega
                      m6_to_group
                      refine wp_join_group (ts := [i32, i64])
                        (fun (rbitN, _smaskN, ()) mN =>
                          ∃ _ : M6UnitState c F0 F_cur s nv rbitN R mN, True)
                        (fun _ (rbitN, smaskN, ()) mN ⟨hN, _⟩ => by
                          m6_steps
                          exact hJu (i + 1#32, rbitN, smaskN, ()) mN
                            (by dsimp only; rw [hi1]; exact Nat.sub_lt_sub_left hi_lt (by omega))
                            ⟨by omega, hN, trivial⟩)
                        (fun _ hJif => by
                          refine wp_join_group (ts := [])
                            (fun () mdo => mdo = ml)
                            (fun _ () mdo hmdo => by
                              subst mdo
                              m6_to_group
                              refine wp_join_group (ts := [i32])
                                (fun (wf, ()) mwf => mwf = ml ∧ (wf = 0#32 ∨ wf = 1#32))
                                (fun _ (wf, ()) mwf ⟨hmwf, hwf⟩ => by
                                  subst mwf
                                  let test_lit : BitVec 32 := (i <<< (1 : Nat)) ||| wf
                                  obtain ⟨htl_eq, hgl_lift, hgl_eq⟩ :=
                                    m6_unit_lit_align (by omega) (by omega) hgv_eq_ws hwf
                                  have hwf_lt : wf.toNat < 2 := by
                                    rcases hwf with rfl | rfl <;> decide
                                  have htl_lt : test_lit.toNat < 2 * nv.toNat := by
                                    dsimp only [test_lit]; omega
                                  have htl_x_to :
                                      (test_lit ^^^ 1#32).toNat = test_lit.toNat ^^^ 1 := by
                                    simp
                                  have htl_x_lt : (test_lit ^^^ 1#32).toNat < 2 * nv.toNat := by
                                    rw [htl_x_to, m6_nat_xor1_cases]; split <;> omega
                                  m6_steps
                                  m6_call hFlip
                                  refine ⟨c, sL, P, L, R, rfl, hlenL, hL_len, hL_mv, hKL,
                                    by rw [hnvL]; exact htl_x_lt, hml,
                                    fun okF scrF mF hlenF _ hKF hnvF _ _ _ hmF => ?_⟩
                                  let sF : FullState :=
                                    { sL with scratch := { sL.scratch with scratch_buf := scrF } }
                                  have hscrF_len := hlenF.scratch_ok.scratch_buf_len
                                  have hinvF := m6_fullDenseInvW_with_scratch hinvL hscrF_len
                                    (fuel' := sL.core.fuel)
                                  have hnvF' : (k6StateOfScratch L scrF).nv = nv :=
                                    hnvF.trans hnvL
                                  have hconeF := hmk_cone sF hscrF_len hcvL hwsL hKF hnvF'
                                  m6_split
                                  · m6_to_group; refine wp_unroll_group fun _ _ => ?_
                                    m6_split; rotate_left
                                    · m6_steps
                                      exact hJif (rbit, smask, ()) mF
                                        ⟨⟨hrb_le, sF, hinvF, hcvL, hfuelL, hwsL, htmkL, htrhL,
                                         hconeF, hmF⟩, trivial⟩
                                    have hrb_lt : rbit.toNat < 64 := ‹_›
                                    have hrb1 : (rbit + 1#32).toNat = rbit.toNat + 1 :=
                                      m6_bv32_add1 (by omega)
                                    m6_call hRef
                                    refine ⟨c, sF, R, rfl, hlenF, hcap,
                                      by rw [← hL_mv]; exact hnv_L,
                                      hnv_mx, fun j hj => by rw [hwsL, hcvL]; exact hws_lt j hj,
                                      hmF, fun sigR mR hsigR hmR => ?_⟩
                                    let sR : FullState :=
                                      { sF with scratch := { sF.scratch with sim_sig := sigR } }
                                    m6_steps
                                    exact hJif (rbit + 1#32, _, ()) mR
                                      ⟨⟨by omega, sR, m6_fullDenseInvW_with_sig hinvF hsigR, hcvL,
                                       hfuelL, hwsL, htmkL, htrhL,
                                       hmk_cone sR hscrF_len hcvL hwsL hKF hnvF', hmR⟩, trivial⟩
                                  · -- `flip` failed: set `nassump = 1`, solve
                                    have hsl_F : sF.scratch.scratch_buf.length = L.scrLen :=
                                      hscrF_len.trans hL_len.symm
                                    obtain ⟨Rfr, hRfr⟩ :
                                        ∃ Rfr : Mem 64 → Prop, Rfr = (FullK6Frame c L sF ⋆ R) :=
                                      ⟨_, rfl⟩
                                    have hm_ka : (K6MemA L (L.kPtr c.pScratchBuf)
                                        (k6StateOfScratch L scrF) ⋆ Rfr) mF := by
                                      change (FullMem c sF ⋆ R) mF at hmF
                                      rw [fullMem_eq_k6Frame hsl_F] at hmF; rw [hRfr]
                                      exact k6Mem_to_amem hKF.shapes (sep_ac hmF)
                                    change wp _ _ _ _ _
                                    c0_hsteps
                                    try dsimp only [Prod.fst]
                                    try rw [hkptr_c0]; try rw [hmv_eq]; try rw [hass_c0]
                                    open scoped K6MemATactics K6PtrTactics FullK6DynMem M6Var2PhtMem
                                      in c0_hsteps!
                                    obtain ⟨hKA, hnvA, _, hassA, _⟩ := k6Inv_set_assump1
                                      (by rw [hnvF']; exact htl_lt) hKF
                                    rw [hRfr] at hm
                                    let ksA := ((k6StateOfScratch L scrF).putHdr .nassump
                                      1#32).putArr .assump 0 test_lit
                                    let scrA := scrF.take L.k6Base ++ ksA.toSlab
                                    let sA : FullState :=
                                      { sF with scratch := { sF.scratch with scratch_buf := scrA } }
                                    obtain ⟨hscrA_len, _, hofA, hmA⟩ :=
                                      m6_join_k6_ofSlab (s := sF) hL_len hscrF_len hKA.shapes hm
                                    change scrA.length = c.scratch_cap at hscrA_len
                                    change k6StateOfScratch L scrA = ksA at hofA
                                    change (FullMem c sA ⋆ R) _ at hmA
                                    have hlenA : sA.LengthsOk c :=
                                      ⟨hlenF.core_ok,
                                       { hlenF.scratch_ok with scratch_buf_len := hscrA_len }⟩
                                    have hnvA' : (k6StateOfScratch L scrA).nv = nv := by
                                      rw [hofA]; exact hnvA.trans hnvF'
                                    have hassA' : k6AssumpLitsS L scrA = [test_lit.toNat] := by
                                      unfold k6AssumpLitsS; rw [hofA]; exact hassA
                                    m6_call hSolve
                                    refine ⟨c, sA, P, L, R, rfl, hlenA, hL_len, hL_mv,
                                      hofA ▸ hKA, hnvA', hmA,
                                      fun d fuelS rngS scrS mS hlenS hfuelS _ hKS _ hnvS _
                                        hassS _ _ hunsS hmS => ?_⟩
                                    let sS : FullState :=
                                      { sA with
                                        core := { sA.core with fuel := fuelS }
                                        scratch :=
                                          { sA.scratch with
                                            rng_state := rngS, scratch_buf := scrS } }
                                    have hscrS_len := hlenS.scratch_ok.scratch_buf_len
                                    have hinvS : FullDenseInvW c F0 F_cur sS :=
                                      m6_fullDenseInvW_with_fuel_rng_sig_scr hinvL hsigL_len
                                        hscrS_len
                                    have hfuelS0 : fuelS.toNat ≤ s.core.fuel.toNat :=
                                      Nat.le_trans hfuelS hfuelL
                                    have hnvS' : (k6StateOfScratch L scrS).nv = nv := by
                                      dsimp only [Arg.val] at hnvS; exact hnvS
                                    have hconeS := hmk_cone sS hscrS_len hcvL hwsL hKS hnvS'
                                    m6_to_group; refine wp_unroll_group fun _ _ => ?_
                                    m6_split
                                    · have hd20 : d = 20#64 := by
                                        clear hK_scr hcone1 hconeL hconeF hconeS hmk_cone hQ
                                        bv_omega
                                      have huns_t :
                                          ∀ β, P β → ¬ (unitsCnf [test_lit.toNat]).Sat β :=
                                        fun β hβ => by
                                          have := hunsS hd20 β hβ; rwa [hassS, hassA'] at this
                                      obtain ⟨hsem_u, hent_u⟩ :=
                                        m6_coneModelSet_unsat_unit htl_lt huns_t
                                      let gl : BitVec 32 := (gv <<< (1 : Nat)) ||| (1#32 - wf)
                                      have hgl_lt : gl.toNat < 2 * sS.core.cur_vars := by
                                        change gl.toNat < 2 * sL.core.cur_vars
                                        dsimp only [gl]; omega
                                      m6_steps
                                      m6_call hAddU
                                      refine ⟨c, F0, F_cur, sS, R, rfl, hlenS, hinvS.2.1,
                                        fun _ => by
                                          dsimp only [Arg.val]
                                          change (cnfOfClauses F_cur).EntailsClause
                                            (cnfClause [gl.toNat])
                                          rw [hgl_lift]; exact hent_u,
                                        hmS, ?_⟩
                                      intro okU valsU flagsU lvlU rsnsU trlU tpU teU propU clU
                                        unassU unflU incU phasesU taU baU ptU pbU hpU psU hlU
                                        qsiU qssU mU _ hlenU hwU hclU hokF _ hmU
                                      let sU : FullState :=
                                        { sS with
                                          core := { sS.core with
                                            vals := valsU, flags := flagsU, lvl := lvlU,
                                            rsns := rsnsU, trl := trlU, trail_pos := tpU,
                                            trail_end := teU, propagated := propU,
                                            cur_level := clU, unassigned := unassU,
                                            unflushed := unflU, inconsistent := incU }
                                          scratch := { sS.scratch with
                                            phases := phasesU, target_assigned := taU,
                                            best_assigned := baU, phases_target := ptU,
                                            phases_best := pbU, heap := hpU, pos := psU,
                                            heap_len := hlU, q_search_idx := qsiU,
                                            q_search_stamp := qssU } }
                                      have hinvU := m6_denseInvW_after_addUnit hinvS hlenU hwU hclU
                                      change FullDenseInvW c F0 F_cur sU at hinvU
                                      have hcvU : sU.core.cur_vars = s.core.cur_vars := hcvL
                                      have hfuelU : sU.core.fuel.toNat ≤ s.core.fuel.toNat :=
                                        hfuelS0
                                      have hwsU : sU.scratch.work_stk1 = ws1 := hwsL
                                      have htmkU : sU.scratch.tarjan_mark = tmk := htmkL
                                      have htrhU : sU.scratch.tarjan_reach =
                                          s.scratch.tarjan_reach := htrhL
                                      have hscrU : sU.scratch.scratch_buf = scrS := rfl
                                      have hconeU := hmk_cone sU hscrS_len hcvU hwsU hKS hnvS'
                                      have hmU' : (FullMem c sU ⋆ R) mU := hmU
                                      m6_split; rotate_left
                                      · have hok_f : okU = false := by cases okU <;> simp at hc ⊢
                                        m6_steps
                                        exact hQ 0xFFFFFFFFFFFFFFFF#64 sU mU hinvU hcvU hfuelU
                                          hwsU htmkU htrhU hconeU (fun _ => (hokF hgl_lt hok_f).1)
                                          (fun h => absurd rfl h) hmU'
                                      change wp _ _ _ _ _
                                      c0_hsteps_nogrp; try dsimp only [Prod.fst]
                                      try rw [hmv_eq]; try rw [hpm_c0]
                                      open scoped M6Var2PhtMem in m6_steps
                                      have hlt_k6 : L.phtMerged + i.toNat < L.k6Base := by omega
                                      let scrM2 := sU.scratch.scratch_buf.set
                                        (L.phtMerged + i.toNat) 1#32
                                      let sM2 : FullState :=
                                        { sU with scratch := { sU.scratch with
                                          scratch_buf := scrM2 } }
                                      have hscrM2_len : scrM2.length = c.scratch_cap :=
                                        List.length_set.trans hscrS_len
                                      have hKM2 : K6Inv L P (k6StateOfScratch L scrM2) := by
                                        rw [m6_k6Inv_of_prefix_set hlt_k6 (hscrU.symm ▸ hKS)]
                                        exact hKS
                                      have hnvM2 : (k6StateOfScratch L scrM2).nv = nv := by
                                        rw [m6_k6Inv_of_prefix_set hlt_k6 (hscrU.symm ▸ hKS)]
                                        exact hnvS'
                                      have hinvM2 := m6_fullDenseInvW_with_scratch hinvU hscrM2_len
                                        (fuel' := sU.core.fuel)
                                      have hsem_u' : SemEntails P [(test_lit ^^^ 1#32).toNat] := by
                                        rw [htl_x_to]; exact hsem_u
                                      m6_call hLive
                                      refine ⟨c, sM2, P, L, R, rfl, hinvM2.1, hL_len, hL_mv, hKM2,
                                        by dsimp only [Arg.val]
                                           change (test_lit ^^^ 1#32).toNat <
                                             2 * (k6StateOfScratch L scrM2).nv.toNat
                                           rw [hnvM2]; exact htl_x_lt,
                                        fun _ => by
                                          dsimp only [Arg.val]
                                          change SemEntails P [(test_lit ^^^ 1#32).toNat]
                                          exact hsem_u',
                                        fun h => absurd rfl h, by assumption,
                                        fun scrL2 mL2 hlenL2 _ hKL2 _ hnvL2 _ _ _ hmL2 => ?_⟩
                                      let sL2 : FullState :=
                                        { sM2 with scratch := { sM2.scratch with
                                          scratch_buf := scrL2 } }
                                      have hscrL2_len := hlenL2.scratch_ok.scratch_buf_len
                                      have hinvL2 := m6_fullDenseInvW_with_scratch hinvM2 hscrL2_len
                                        (fuel' := sM2.core.fuel)
                                      have hnvL2' : (k6StateOfScratch L scrL2).nv = nv :=
                                        hnvL2.trans hnvM2
                                      have hconeL2 := hmk_cone sL2 hscrL2_len hcvU hwsU hKL2 hnvL2'
                                      change wp _ _ _ _ _
                                      c0_hsteps_nogrp; try dsimp only [Prod.fst]
                                      try rw [hkptr_c0]; try rw [hmv_eq]
                                      open scoped FullK6DynMem in m6_split
                                      · have hk_inc : (k6StateOfScratch L scrL2).incons ≠ 0#32 := by
                                          rw [m6_k6StateOfScratch_incons (by
                                            rw [hscrL2_len, ← hL_len]
                                            unfold K6Layout.scrLen K6Layout.k6Fixed; omega)]
                                          exact ‹_›
                                        have huns_cur : (cnfOfClauses F_cur).Unsat :=
                                          m6_coneModelSet_unsat_of_empty (ws1 := ws1)
                                            (nv := nv.toNat) (hKL2.clauses.incons_ok hk_inc)
                                        have huns_f0 : F0.Unsat := hinvL2.2.1.ext_sound.2 huns_cur
                                        m6_steps
                                        exact hQ 0xFFFFFFFFFFFFFFFF#64 _ _
                                          (m6_denseInvW_set_inconsistent hinvL2 huns_cur) hcvU
                                          hfuelU hwsU htmkU htrhU hconeL2 (fun _ => huns_f0)
                                          (fun h => absurd rfl h) (by assumption)
                                      m6_call hRearm
                                      refine ⟨c, F0, F_cur, sL2, R, rfl, hinvL2, hmL2,
                                        fun flR mR hflR hinvR hmR => ?_⟩
                                      let sR2 : FullState :=
                                        { sL2 with core := { sL2.core with flags := flR } }
                                      m6_steps
                                      let sC2 : FullState :=
                                        { sR2 with scratch := { sR2.scratch with
                                          sweep_cnt := sR2.scratch.sweep_cnt + 1#64 } }
                                      have hinvC2 := m6_fullDenseInvW_with_sweep_cnt hinvR
                                        (sR2.scratch.sweep_cnt + 1#64)
                                      have hconeC2 := hmk_cone sC2 hscrL2_len hcvU hwsU hKL2 hnvL2'
                                      exact hJif (rbit, smask, ()) _
                                        ⟨⟨hrb_le, sC2, hinvC2, hcvU, hfuelU, hwsU, htmkU, htrhU,
                                         hconeC2, by assumption⟩, trivial⟩
                                    · m6_to_group; refine wp_unroll_group fun _ _ => ?_
                                      m6_split; rotate_left
                                      · m6_steps
                                        exact hJif (rbit, smask, ()) mS
                                          ⟨⟨hrb_le, sS, hinvS, hcvL, hfuelS0, hwsL, htmkL, htrhL,
                                           hconeS, hmS⟩, trivial⟩
                                      m6_split; rotate_left
                                      · m6_steps
                                        exact hJif (rbit, smask, ()) mS
                                          ⟨⟨hrb_le, sS, hinvS, hcvL, hfuelS0, hwsL, htmkL, htrhL,
                                           hconeS, hmS⟩, trivial⟩
                                      have hrb_lt : rbit.toNat < 64 := ‹_›
                                      have hrb1 : (rbit + 1#32).toNat = rbit.toNat + 1 :=
                                        m6_bv32_add1 (by omega)
                                      m6_call hRef
                                      refine ⟨c, sS, R, rfl, hlenS, hcap,
                                        by rw [← hL_mv]; exact hnv_L, hnv_mx,
                                        fun j hj => by rw [hwsL, hcvL]; exact hws_lt j hj,
                                        hmS, fun sigR mR hsigR hmR => ?_⟩
                                      let sR : FullState :=
                                        { sS with scratch := { sS.scratch with sim_sig := sigR } }
                                      m6_steps
                                      exact hJif (rbit + 1#32, _, ()) mR
                                        ⟨⟨by omega, sR, m6_fullDenseInvW_with_sig hinvS hsigR,
                                         hcvL, hfuelS0, hwsL, htmkL, htrhL,
                                         hmk_cone sR hscrS_len hcvL hwsL hKS hnvS', hmR⟩, trivial⟩)
                                (fun _ hJwf => by
                                  m6_split
                                  · m6_steps; exact hJwf (0#32, ()) ml ⟨rfl, Or.inl rfl⟩
                                  · m6_steps; exact hJwf (1#32, ()) ml ⟨rfl, Or.inr rfl⟩))
                            (fun _ hJdo => by
                              m6_split; · m6_steps; exact hJdo () ml rfl
                              m6_split; · m6_steps; exact hJdo () ml rfl
                              m6_steps
                              exact hJif (rbit, smask, ()) ml
                                ⟨⟨hrb_le, sL, hinvL, hcvL, hfuelL, hwsL, htmkL, htrhL, hconeL,
                                 hml⟩, trivial⟩)))))
          (fun _ hJsm => by
            m6_split
            · m6_steps; exact hJsm _ m1 rfl
            · m6_steps; exact hJsm _ m1 rfl))

end LeanQbe.T.Examples.Kissat.FullM6Sweep
