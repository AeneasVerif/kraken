module

public import LeanQbe.T.Examples.Kissat.FullM6SweepProofVar1a

/-!
# Kissat `D-Full` M6 — Rearm, PHT, & Partition Refinement Proofs (`23..26/39`)

Parametric `(Γ : Env)` `Func.wp` proofs for `4/39` owned functions (`26/39` cumulative):
- `23/39`: `full_m6_sweep_rearm_wp`
- `24/39`: `full_m6_sweep_build_pht_wp`
- `25/39`: `full_m6_extract_pht_wp`
- `26/39`: `full_m6_refine_partition_wp`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6Sweep

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full LeanQbe.T.Examples.Kissat.FullM4Sweep
open Kraken.Bedrock2.Test
open FullArenaTactics K6MemATactics K6PtrTactics
open scoped FullArenaTactics M6SweepTactics

/-! ## 1. Shared Watch, PHT, & Dynamic `scratch_buf` Sub-Array Helpers -/

private theorem m6_denseSlice_step_bin {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} {w0 : BitVec 32} (hs : DenseWatchSliceOk F_cur k lit p rem)
    (hpos : 0 < rem) (hp : k.wstk[p]? = some w0)
    (hbin : (w0 &&& 0x80000000#32) ≠ 0#32) :
    w0 ≠ 0xFFFFFFFF#32 ∧ (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
    DenseWatchSliceOk F_cur k lit (p + 1) (rem - 1) := by
  cases hs with
  | empty => omega
  | bin hp' _ hne hlt hent hrest =>
    rw [hp] at hp'; cases Option.some.inj hp'; exact ⟨hne, hlt, hent, hrest⟩
  | occ hp' _ hflag _ _ _ _ =>
    rw [hp] at hp'; cases Option.some.inj hp'; exact absurd hflag hbin

private theorem m6_denseSlice_step_occ {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} {w0 : BitVec 32} (hs : DenseWatchSliceOk F_cur k lit p rem)
    (hpos : 0 < rem) (hp : k.wstk[p]? = some w0)
    (hocc : (w0 &&& 0x80000000#32) = 0#32) :
    2 ≤ rem ∧ 3 ≤ w0.toNat ∧
    ∃ cr, k.wstk[p + 1]? = some cr ∧ cr.toNat < 0x80000000 ∧
      cr.toNat ∈ fullArenaClauseRefsCore k ∧
      DenseWatchSliceOk F_cur k lit (p + 2) (rem - 2) := by
  cases hs with
  | empty => omega
  | bin hp' hflag _ _ _ _ =>
    rw [hp] at hp'; cases Option.some.inj hp'; exact absurd hocc hflag
  | occ hp' hp1 _ h3 hlt href hrest =>
    rw [hp] at hp'; cases Option.some.inj hp'
    exact ⟨by omega, h3, _, hp1, hlt, href, hrest⟩

private theorem m6_hidx_lt_1024 (k : BitVec 64) : ((k &&& 1023#64).setWidth 32).toNat < 1024 := by
  rw [BitVec.toNat_setWidth]
  have h1 : (k &&& 1023#64).toNat < 1024 := by
    rw [BitVec.toNat_and, show (1023#64).toNat = 1023 from rfl]
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  rw [Nat.mod_eq_of_lt (by omega)]; exact h1

namespace M6PhtMem
@[scoped c0_load] theorem load_pht_next {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < L.maxV) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 ((c.pScratchBuf + BitVec.ofNat 64 (4 * k6PhtNext)) + idx.setWidth 64 * 4) =
      some (s.scratch.scratch_buf[k6PhtNext + idx.toNat]'(by
        have := L.hmaxV; have := L.hacap
        rw [hscr, ← hL]; unfold K6Layout.scrLen K6Layout.k6Base k6PhtNext; omega)) := by
  have := L.hmaxV
  have hptr : (c.pScratchBuf + BitVec.ofNat 64 (4 * k6PhtNext)) + idx.setWidth 64 * 4 =
      c.pScratchBuf + BitVec.ofNat 64 (4 * (k6PhtNext + idx.toNat)) := by
    rw [show idx.setWidth 64 = BitVec.ofNat 64 idx.toNat from by apply BitVec.eq_of_toNat_eq; simp,
      k6_ptr_nat_mul4 _ idx.toNat (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  rw [hptr]; exact load_full_scratch_buf _ hm

@[scoped c0_store] theorem store_pht_next {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < L.maxV) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 ((c.pScratchBuf + BitVec.ofNat 64 (4 * k6PhtNext)) + idx.setWidth 64 * 4) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set (k6PhtNext + idx.toNat) v } } ⋆ R)
        (storeMem m i32
          ((c.pScratchBuf + BitVec.ofNat 64 (4 * k6PhtNext)) + idx.setWidth 64 * 4) v) := by
  have := L.hmaxV
  have hptr : (c.pScratchBuf + BitVec.ofNat 64 (4 * k6PhtNext)) + idx.setWidth 64 * 4 =
      c.pScratchBuf + BitVec.ofNat 64 (4 * (k6PhtNext + idx.toNat)) := by
    rw [show idx.setWidth 64 = BitVec.ofNat 64 idx.toNat from by apply BitVec.eq_of_toNat_eq; simp,
      k6_ptr_nat_mul4 _ idx.toNat (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  rw [hptr]
  exact store_full_scratch_buf v (by
    have := L.hmaxV; have := L.hacap
    rw [hscr, ← hL]; unfold K6Layout.scrLen K6Layout.k6Base k6PhtNext; omega) hm

@[scoped c0_load] theorem load_pht_next_32 {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < L.maxV) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32
        ((c.pScratchBuf + BitVec.setWidth 64 (1280 : BitVec 32) * 4) +
          idx.setWidth 64 * 4) =
      some (s.scratch.scratch_buf[k6PhtNext + idx.toNat]'(by
        have := L.hmaxV; have := L.hacap
        rw [hscr, ← hL]; unfold K6Layout.scrLen K6Layout.k6Base k6PhtNext; omega)) := by
  change loadVal m i32 ((c.pScratchBuf + BitVec.ofNat 64 (4 * k6PhtNext)) +
    idx.setWidth 64 * 4) = _
  exact load_pht_next hL hscr hi hm

@[scoped c0_store] theorem store_pht_next_32 {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < L.maxV) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32
        ((c.pScratchBuf + BitVec.setWidth 64 (1280 : BitVec 32) * 4) +
          idx.setWidth 64 * 4) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set (k6PhtNext + idx.toNat) v } } ⋆ R)
        (storeMem m i32
          ((c.pScratchBuf + BitVec.setWidth 64 (1280 : BitVec 32) * 4) +
            idx.setWidth 64 * 4) v) := by
  change storeOk m i32 ((c.pScratchBuf + BitVec.ofNat 64 (4 * k6PhtNext)) +
    idx.setWidth 64 * 4) ∧ _
  exact store_pht_next v hL hscr hi hm

@[scoped c0_load] theorem load_pht_next_bv32 {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < L.maxV) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 ((c.pScratchBuf + BitVec.setWidth 64 1280#32 * 4) + idx.setWidth 64 * 4) =
      some (s.scratch.scratch_buf[k6PhtNext + idx.toNat]'(by
        have := L.hmaxV; have := L.hacap
        rw [hscr, ← hL]; unfold K6Layout.scrLen K6Layout.k6Base k6PhtNext; omega)) := by
  change loadVal m i32 ((c.pScratchBuf + BitVec.ofNat 64 (4 * k6PhtNext)) +
    idx.setWidth 64 * 4) = _
  exact load_pht_next hL hscr hi hm

@[scoped c0_store] theorem store_pht_next_bv32 {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < L.maxV) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 ((c.pScratchBuf + BitVec.setWidth 64 1280#32 * 4) + idx.setWidth 64 * 4) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set (k6PhtNext + idx.toNat) v } } ⋆ R)
        (storeMem m i32
          ((c.pScratchBuf + BitVec.setWidth 64 1280#32 * 4) + idx.setWidth 64 * 4) v) := by
  change storeOk m i32 ((c.pScratchBuf + BitVec.ofNat 64 (4 * k6PhtNext)) +
    idx.setWidth 64 * 4) ∧ _
  exact store_pht_next v hL hscr hi hm

@[scoped c0_load] theorem load_pht_next_64 {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < L.maxV) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 ((c.pScratchBuf + (1280#64 : BitVec 64) * 4) + idx.setWidth 64 * 4) =
      some (s.scratch.scratch_buf[k6PhtNext + idx.toNat]'(by
        have := L.hmaxV; have := L.hacap
        rw [hscr, ← hL]; unfold K6Layout.scrLen K6Layout.k6Base k6PhtNext; omega)) := by
  change loadVal m i32 ((c.pScratchBuf + BitVec.ofNat 64 (4 * k6PhtNext)) +
    idx.setWidth 64 * 4) = _
  exact load_pht_next hL hscr hi hm

@[scoped c0_store] theorem store_pht_next_64 {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < L.maxV) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 ((c.pScratchBuf + (1280#64 : BitVec 64) * 4) + idx.setWidth 64 * 4) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set (k6PhtNext + idx.toNat) v } } ⋆ R)
        (storeMem m i32
          ((c.pScratchBuf + (1280#64 : BitVec 64) * 4) + idx.setWidth 64 * 4) v) := by
  change storeOk m i32 ((c.pScratchBuf + BitVec.ofNat 64 (4 * k6PhtNext)) +
    idx.setWidth 64 * 4) ∧ _
  exact store_pht_next v hL hscr hi hm

@[scoped c0_load] theorem load_pht_next_ofnat {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < L.maxV) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 ((c.pScratchBuf + (1280 : BitVec 64) * 4) + idx.setWidth 64 * 4) =
      some (s.scratch.scratch_buf[k6PhtNext + idx.toNat]'(by
        have := L.hmaxV; have := L.hacap
        rw [hscr, ← hL]; unfold K6Layout.scrLen K6Layout.k6Base k6PhtNext; omega)) := by
  change loadVal m i32 ((c.pScratchBuf + BitVec.ofNat 64 (4 * k6PhtNext)) +
    idx.setWidth 64 * 4) = _
  exact load_pht_next hL hscr hi hm

@[scoped c0_store] theorem store_pht_next_ofnat {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < L.maxV) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 ((c.pScratchBuf + (1280 : BitVec 64) * 4) + idx.setWidth 64 * 4) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set (k6PhtNext + idx.toNat) v } } ⋆ R)
        (storeMem m i32
          ((c.pScratchBuf + (1280 : BitVec 64) * 4) + idx.setWidth 64 * 4) v) := by
  change storeOk m i32 ((c.pScratchBuf + BitVec.ofNat 64 (4 * k6PhtNext)) +
    idx.setWidth 64 * 4) ∧ _
  exact store_pht_next v hL hscr hi hm

@[scoped c0_load] theorem load_pht_merged {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {idx : BitVec 32}
    (hL : L.scrLen = c.scratch_cap) (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hi : idx.toNat < L.maxV) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 ((c.pScratchBuf + BitVec.ofNat 64 (4 * L.phtMerged)) + idx.setWidth 64 * 4) =
      some (s.scratch.scratch_buf[L.phtMerged + idx.toNat]'(by
        have := L.hmaxV; have := L.hacap
        rw [hscr, ← hL]
        unfold K6Layout.scrLen K6Layout.k6Base K6Layout.phtMerged; omega)) := by
  have := L.hmaxV
  have hptr : (c.pScratchBuf + BitVec.ofNat 64 (4 * L.phtMerged)) + idx.setWidth 64 * 4 =
      c.pScratchBuf + BitVec.ofNat 64 (4 * (L.phtMerged + idx.toNat)) := by
    rw [show idx.setWidth 64 = BitVec.ofNat 64 idx.toNat from by apply BitVec.eq_of_toNat_eq; simp,
      k6_ptr_nat_mul4 _ idx.toNat (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  rw [hptr]; exact load_full_scratch_buf _ hm

@[scoped c0_store] theorem store_scratch_buf_after_set {c : FullCfg} {s : FullState}
    {scr : List (BitVec 32)} {k : Nat} {w v : BitVec 32} {i : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : i.toNat < scr.length)
    (hm : (FullMem c { s with scratch := { s.scratch with scratch_buf := scr.set k w } } ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf + i * 4) ∧
      (FullMem c { s with scratch :=
          { s.scratch with scratch_buf := (scr.set k w).set i.toNat v } } ⋆ R)
        (storeMem m i32 (c.pScratchBuf + i * 4) v) := by
  simpa only [List.length_set] using
    c0_store_full_scratch_buf
      (s := { s with scratch := { s.scratch with scratch_buf := scr.set k w } }) v
      (by rw [List.length_set]; exact hi) hm
end M6PhtMem

private theorem m6_ptr_phtMerged (L : K6Layout) (pScr : BitVec 64) :
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

private theorem bv32_sub1_of_pos {x : BitVec 32} (hx : 0 < x.toNat) :
    (x - 1#32).toNat = x.toNat - 1 := by bv_omega

private theorem m6_bv64_zext_lt {v : BitVec 32} {n : Nat} (hv : v.toNat < n) :
    (BitVec.setWidth 64 v).toNat < n := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact hv

private theorem m6_bv64_shl1_zext_lt {v : BitVec 32} {n : Nat} (hv : v.toNat < n)
    (_hn : n < 2 ^ 31) : (BitVec.setWidth 64 v <<< (1 : Nat)).toNat < 2 * n := by
  rw [m6_bv64_shl1]; omega

private theorem m6_bv32_shl1_zext_lt {v : BitVec 32} {n : Nat} (hv : v.toNat < n)
    (_hn : n < 2 ^ 31) : (BitVec.setWidth 64 (v <<< (1 : Nat))).toNat < 2 * n := by
  rw [bv_c0_zext32_64, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one,
    Nat.mod_eq_of_lt (by omega)]
  omega

private theorem m6_phtOk_zero {scr : List (BitVec 32)}
    (hhead : ∀ b < k6PhtSz, scr[k6PhtHead + b]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) :
    M6PhtOk 0 scr :=
  ⟨fun b hb => Or.inl (hhead b hb), fun _ hi => by omega⟩

private theorem m6_phtOk_step_unmerged {L : K6Layout} {scr : List (BitVec 32)} {i hidx : Nat}
    (hi : i < L.maxV) (hh : hidx < k6PhtSz) (hlen : L.scrLen ≤ scr.length) (hp : M6PhtOk i scr) :
    let scr1 := scr.set (k6PhtNext + i) (scr[k6PhtHead + hidx]?.getD 0xFFFFFFFF#32)
    let scr2 := scr1.set (k6PhtHead + hidx) (BitVec.ofNat 32 i)
    M6PhtOk (i + 1) scr2 := by
  intro scr1 scr2
  have hm := L.hmaxV; have ha := L.hacap
  have hsz : 1280 + L.maxV ≤ scr.length := by
    have : k6PhtNext + L.maxV ≤ L.scrLen := by
      unfold K6Layout.scrLen K6Layout.k6Base K6Layout.k6Fixed k6PhtNext; omega
    unfold k6PhtNext at this; omega
  have hh' : hidx < 1024 := hh
  refine ⟨fun b hb => ?_, fun k hk => ?_⟩
  · have hb' : b < 1024 := hb
    by_cases hbh : b = hidx
    · subst hbh; right
      dsimp only [scr2, scr1]; unfold k6PhtHead k6PhtNext
      have hbd : 256 + b < (scr.set (1280 + i) (scr[256 + b]?.getD 0xFFFFFFFF#32)).length := by
        simp; omega
      rw [List.getElem?_set_self hbd, Option.getD_some,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    · dsimp only [scr2, scr1]; unfold k6PhtHead k6PhtNext
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      rcases hp.1 b hb with hff | hlt
      · exact Or.inl hff
      · exact Or.inr (by unfold k6PhtHead at hlt; omega)
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
    · dsimp only [scr2, scr1]; unfold k6PhtHead k6PhtNext
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      exact hp.2 k hlt
    · dsimp only [scr2, scr1]; unfold k6PhtHead k6PhtNext
      have hbd : 1280 + k < scr.length := by omega
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_self hbd, Option.getD_some]
      exact hp.1 hidx hh

private theorem m6_phtOk_step_merged {L : K6Layout} {scr : List (BitVec 32)} {i : Nat}
    (hi : i < L.maxV) (hlen : L.scrLen ≤ scr.length) (hp : M6PhtOk i scr) :
    M6PhtOk (i + 1) (scr.set (k6PhtNext + i) 0xFFFFFFFF#32) := by
  have hm := L.hmaxV; have ha := L.hacap
  have hsz : 1280 + L.maxV ≤ scr.length := by
    have : k6PhtNext + L.maxV ≤ L.scrLen := by
      unfold K6Layout.scrLen K6Layout.k6Base K6Layout.k6Fixed k6PhtNext; omega
    unfold k6PhtNext at this; omega
  refine ⟨fun b hb => ?_, fun k hk => ?_⟩
  · have hb' : b < 1024 := hb
    unfold k6PhtHead k6PhtNext
    rw [List.getElem?_set_ne (by omega)]
    rcases hp.1 b hb with hff | hlt
    · exact Or.inl hff
    · exact Or.inr (by unfold k6PhtHead at hlt; omega)
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
    · unfold k6PhtNext; rw [List.getElem?_set_ne (by omega)]; exact hp.2 k hlt
    · unfold k6PhtNext; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact Or.inl rfl

private theorem m6_phtOk_set_head {scr : List (BitVec 32)} {nv b : Nat} {v : BitVec 32}
    (hb : b < k6PhtSz) (hbd : k6PhtHead + b < scr.length)
    (hv : v = 0xFFFFFFFF#32 ∨ v.toNat < nv) (hp : M6PhtOk nv scr) :
    M6PhtOk nv (scr.set (k6PhtHead + b) v) := by
  refine ⟨fun b' hb' => ?_, fun i hi => ?_⟩
  · by_cases hbe : b' = b
    · subst hbe; rw [List.getElem?_set_self hbd, Option.getD_some]; exact hv
    · rw [List.getElem?_set_ne (by omega)]; exact hp.1 b' hb'
  · unfold k6PhtHead k6PhtNext k6PhtSz at *
    rw [List.getElem?_set_ne (by omega)]; exact hp.2 i hi

private theorem m6_phtNext_set_next {scr : List (BitVec 32)} {nv idx : Nat} {v : BitVec 32}
    (hi : idx < nv) (hbd : k6PhtNext + idx < scr.length) (hv : v = 0xFFFFFFFF#32 ∨ v.toNat < idx)
    (hnx : ∀ i < nv,
      let nx := scr[k6PhtNext + i]?.getD 0xFFFFFFFF#32
      nx = 0xFFFFFFFF#32 ∨ nx.toNat < i) :
    ∀ i < nv,
      let nx := (scr.set (k6PhtNext + idx) v)[k6PhtNext + i]?.getD 0xFFFFFFFF#32
      nx = 0xFFFFFFFF#32 ∨ nx.toNat < i := by
  intro i hi'
  by_cases hie : i = idx
  · subst hie; dsimp only; rw [List.getElem?_set_self hbd, Option.getD_some]; exact hv
  · dsimp only; rw [List.getElem?_set_ne (by omega)]; exact hnx i hi'

private theorem m6_phtOk_set_next {scr : List (BitVec 32)} {nv idx : Nat} {v : BitVec 32}
    (hi : idx < nv) (hbd : k6PhtNext + idx < scr.length) (hv : v = 0xFFFFFFFF#32 ∨ v.toNat < idx)
    (hp : M6PhtOk nv scr) :
    M6PhtOk nv (scr.set (k6PhtNext + idx) v) :=
  ⟨fun b hb => by
    unfold k6PhtHead k6PhtNext k6PhtSz at *
    rw [List.getElem?_set_ne (by omega)]; exact hp.1 b hb,
   m6_phtNext_set_next hi hbd hv hp.2⟩

private theorem m6_partOk_set_head {nv ncls idx : Nat} {scr heads : List (BitVec 32)}
    {v : BitVec 32} (hidx : idx < k6PhtSz) (hp : M6PartitionOk nv ncls scr heads) :
    M6PartitionOk nv ncls (scr.set (k6PhtHead + idx) v) heads :=
  ⟨hp.1,
   fun i hi => by
     unfold k6PhtHead k6PhtNext k6PhtSz at *
     rw [List.getElem?_set_ne (by omega)]; exact hp.2.1 i hi,
   hp.2.2⟩

private theorem m6_partOk_set_next {nv ncls idx : Nat} {scr heads : List (BitVec 32)}
    {v : BitVec 32} (hi : idx < nv) (hbd : k6PhtNext + idx < scr.length)
    (hv : v = 0xFFFFFFFF#32 ∨ v.toNat < idx) (hp : M6PartitionOk nv ncls scr heads) :
    M6PartitionOk nv ncls (scr.set (k6PhtNext + idx) v) heads :=
  ⟨hp.1, m6_phtNext_set_next hi hbd hv hp.2.1, hp.2.2⟩

private theorem m6_partOk_push_head {nv ncls : Nat} {scr heads : List (BitVec 32)} {h0 : BitVec 32}
    (hnl : ncls + 1 ≤ heads.length) (hh0 : h0.toNat < nv) (hp : M6PartitionOk nv ncls scr heads) :
    M6PartitionOk nv (ncls + 1) scr (heads.set ncls h0) :=
  ⟨by simpa using hnl, hp.2.1, fun ci hci => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hci with hlt | rfl
    · rw [List.getElem?_set_ne (by omega)]; exact hp.2.2 ci hlt
    · rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hh0⟩

/-! ## 2. `full_m6_sweep_rearm_wp` (`23/39`) -/

theorem full_m6_sweep_rearm_wp (Γ : Env) :
    ∀ args m Q X, m6SweepRearmSpec args m Q X →
      Func.wp Γ full_m6_sweep_rearm_body args m Q X := by
  rintro ⟨h, v, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hinv, hm, hQ⟩
  have hlen := hinv.1
  have hw := hinv.2.1
  have hdm := hinv.2.2.2.2.2.2
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le := hlen.core_ok.cur_vars_le
  have hfl_len := hlen.core_ok.flags_len
  have hwv_len := hlen.core_ok.wvec_len
  have hws_len := hlen.core_ok.wstk_len_arr
  have har_len := hlen.core_ok.arena_len_arr
  have hal_le := hlen.core_ok.arena_len_le
  have hwcap_lt := c.hwcap; unfold dimacsBound at hwcap_lt
  have hacap_lt := c.harena; unfold dimacsBound at hacap_lt
  have hdense : DenseWatchesInv F_cur s.core := by
    have hmw := hw.watches; unfold ModeWatchesInv at hmw; rwa [ite_eq_right hdm] at hmw
  unfold Func.wp full_m6_sweep_rearm_body
  m6_steps
  m6_split
  · m6_steps; exact hQ s.core.flags m hfl_len hinv hm
  have hv_lt : v.toNat < s.core.cur_vars := by
    have : ¬ s.core.cur_vars % 2 ^ 64 ≤ v.toNat := by bv_omega
    omega
  m6_to_group
  refine wp_loop_inv (ts := [i32])
    (fun (pol, ()) mp => pol.toNat ≤ 2 ∧ ∃ flP : List (BitVec 32), flP.length = c.max_vars ∧
      (FullMem c { s with core := { s.core with flags := flP } } ⋆ R) mp)
    (fun (pol, ()) _ => 2 - pol.toNat)
    (fun _ hJpol => by
      m6_steps; exact hJpol (0#32, ()) m ⟨Nat.zero_le _, s.core.flags, hfl_len, hm⟩)
    (fun _ (pol, ()) mp ⟨hpol_le, flP, hflP_len, hmp⟩ hJpol => by
      m6_split; rotate_left
      · m6_steps; exact hQ flP mp hflP_len (m6_fullDenseInvW_with_flags hinv hflP_len) hmp
      have hpol_lt : pol.toNat < 2 := by bv_omega
      have hpol1 : (pol + 1#32).toNat = pol.toNat + 1 := m6_bv32_add1 (by omega)
      let lit : BitVec 32 := (v <<< (1 : Nat)) ||| pol
      have hlit_eq : lit.toNat = 2 * v.toNat + pol.toNat :=
        m6_bv32_shl1_or_pol v pol (by omega) hpol_lt
      have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by omega
      have hlit_w0 : (BitVec.setWidth 64 (v <<< (1 : Nat) ||| pol) <<< (1 : Nat)).toNat <
          s.core.wvec.length := by
        rw [hwv_len, m6_bv64_shl1]; change 2 * lit.toNat < 4 * c.max_vars; omega
      have hlit_w1 : ((BitVec.setWidth 64 (v <<< (1 : Nat) ||| pol) <<< (1 : Nat)) + 1#64).toNat <
          s.core.wvec.length := by
        rw [hwv_len, m6_bv64_shl1_add1]; change 2 * lit.toNat + 1 < 4 * c.max_vars; omega
      let wOff : BitVec 64 :=
        (s.core.wvec[(BitVec.setWidth 64 (v <<< (1 : Nat) ||| pol) <<<
          (1 : Nat)).toNat]'hlit_w0).setWidth 64
      let wSz : BitVec 64 :=
        (s.core.wvec[((BitVec.setWidth 64 (v <<< (1 : Nat) ||| pol) <<< (1 : Nat)) +
          1#64).toNat]'hlit_w1).setWidth 64
      have hoff_eq : wOff.toNat = fullWatchOffCore s.core lit.toNat := by
        dsimp only [wOff, fullWatchOffCore]
        simp only [bv_c0_zext32_64, m6_bv64_shl1,
          List.getElem?_eq_getElem (by rw [hwv_len]; omega : 2 * lit.toNat < s.core.wvec.length),
          Option.getD_some]; rfl
      have hsz_eq : wSz.toNat = fullWatchSizeCore s.core lit.toNat := by
        dsimp only [wSz, fullWatchSizeCore]
        simp only [bv_c0_zext32_64, m6_bv64_shl1_add1,
          List.getElem?_eq_getElem
            (by rw [hwv_len]; omega : 2 * lit.toNat + 1 < s.core.wvec.length),
          Option.getD_some]; rfl
      have hbd_lit := hdense.layout.bounds lit.toNat hlit_lt
      have hwlen_le := hlen.core_ok.wlen_le
      have hend_eq : (wOff + wSz).toNat = wOff.toNat + wSz.toNat := by
        rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
      have hw0_nat : 2 * (v <<< (1 : Nat) ||| pol).toNat % 2 ^ 64 =
          (BitVec.setWidth 64 (v <<< (1 : Nat) ||| pol) <<< (1 : Nat)).toNat := by
        rw [m6_bv64_shl1, Nat.mod_eq_of_lt (by change 2 * lit.toNat < 2 ^ 64; omega)]
      have hw1_nat : (2 * (v <<< (1 : Nat) ||| pol).toNat + (1#64).toNat) % 2 ^ 64 =
          ((BitVec.setWidth 64 (v <<< (1 : Nat) ||| pol) <<< (1 : Nat)) + 1#64).toNat := by
        rw [m6_bv64_shl1_add1, show (1#64).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (by change 2 * lit.toNat + 1 < 2 ^ 64; omega)]
      have hslice0 : DenseWatchSliceOk F_cur s.core lit.toNat wOff.toNat wSz.toNat := by
        rw [hoff_eq, hsz_eq]; exact hdense.slices lit.toNat hlit_lt
      m6_to_group
      refine wp_join_group (ts := [i64, i64])
        (fun (_pB, _lB, ()) mb => ∃ flB : List (BitVec 32), flB.length = c.max_vars ∧
          (FullMem c { s with core := { s.core with flags := flB } } ⋆ R) mb)
        (fun _ _ mb ⟨flB, hflB_len, hmb⟩ => by
          m6_steps
          exact hJpol (pol + 1#32, ()) mb (by dsimp only; omega) ⟨by omega, flB, hflB_len, hmb⟩)
        (fun _ hJbrk => by
          refine wp_loop_inv (ts := [i64, i64])
            (fun (p, lim, ()) mw => p.toNat ≤ (wOff + wSz).toNat ∧ lim.toNat ≤ 128 ∧
              DenseWatchSliceOk F_cur s.core lit.toNat p.toNat ((wOff + wSz).toNat - p.toNat) ∧
              ∃ flW : List (BitVec 32), flW.length = c.max_vars ∧
                (FullMem c { s with core := { s.core with flags := flW } } ⋆ R) mw)
            (fun (_, lim, ()) _ => 128 - lim.toNat)
            (fun _ hJw => by
              m6_steps
              refine hJw (wOff, 0#64, ()) mp ⟨by omega, by simp, ?_, flP, hflP_len, hmp⟩
              rw [hend_eq, Nat.add_sub_cancel_left]; exact hslice0)
            (fun Jw (p, lim, ()) mw ⟨hp_le, hlim_le, hslice, flW, hflW_len, hmw⟩ hJw => by
              m6_split; rotate_left
              · m6_steps; exact hJbrk (p, lim, ()) mw ⟨flW, hflW_len, hmw⟩
              m6_split; rotate_left
              · m6_steps; exact hJbrk (p, lim, ()) mw ⟨flW, hflW_len, hmw⟩
              have hp_lt : p.toNat < (wOff + wSz).toNat := by
                dsimp only [wOff, wSz]; rw [BitVec.toNat_add, bv_c0_zext32_64, bv_c0_zext32_64]
                simp only [← hw0_nat, ← hw1_nat]; assumption
              have hlim_lt : lim.toNat < 128 := by bv_omega
              have hp_ws : p.toNat < s.core.wstk.length := by omega
              have hp1 : (p + 1#64).toNat = p.toNat + 1 := m6_bv64_add1 (by omega)
              have hlim1 : (lim + 1#64).toNat = lim.toNat + 1 := m6_bv64_add1 (by omega)
              let w0 : BitVec 32 := s.core.wstk[p.toNat]'hp_ws
              have hw0_s : s.core.wstk[p.toNat]? = some w0 := List.getElem?_eq_getElem hp_ws
              m6_split
              · -- binary watch entry
                have hbin : (w0 &&& 0x80000000#32) ≠ 0#32 := by dsimp only [w0]; bv_omega
                have hslice1 := (m6_denseSlice_step_bin hslice (by omega) hw0_s hbin).2.2.2
                m6_to_group
                refine wp_join_group (ts := [])
                  (fun (_ : Tup Val []) m1 => ∃ fl1 : List (BitVec 32), fl1.length = c.max_vars ∧
                    (FullMem c { s with core := { s.core with flags := fl1 } } ⋆ R) m1)
                  (fun _ () m1 ⟨fl1, hfl1_len, hm1⟩ => by
                    m6_steps
                    refine hJw (p + 1#64, lim + 1#64, ()) m1 (by dsimp only; omega)
                      ⟨by omega, by omega, ?_, fl1, hfl1_len, hm1⟩
                    rw [hp1, show (wOff + wSz).toNat - (p.toNat + 1) =
                      (wOff + wSz).toNat - p.toNat - 1 by omega]
                    exact hslice1)
                  (fun _ hJb => by
                    try refine wp_unroll_group fun _ _ => ?_
                    m6_split; rotate_left
                    · m6_steps; exact hJb () mw ⟨flW, hflW_len, hmw⟩
                    have hov_lt : (((w0 &&& 0x7FFFFFFF#32) >>> (1 : Nat)).setWidth 64).toNat <
                        c.max_vars := by
                      have : (((w0 &&& 0x7FFFFFFF#32) >>> (1 : Nat)).setWidth 64).toNat <
                          s.core.cur_vars % 2 ^ 64 := by dsimp only [w0]; bv_omega
                      omega
                    m6_split; rotate_left
                    · m6_steps; exact hJb () mw ⟨flW, hflW_len, hmw⟩
                    m6_split; rotate_left
                    · m6_steps; exact hJb () mw ⟨flW, hflW_len, hmw⟩
                    m6_steps; exact hJb () _ ⟨_, List.length_set.trans hflW_len, by assumption⟩)
              · -- occurrence watch entry
                have hocc : (w0 &&& 0x80000000#32) = 0#32 := by dsimp only [w0]; bv_omega
                obtain ⟨hrem2, _, cr, hcr_s, hcr_lt, hcr_ref, hslice2⟩ :=
                  m6_denseSlice_step_occ hslice (by omega) hw0_s hocc
                m6_split
                · exfalso
                  have hge : (wOff + wSz).toNat ≤ (p + 1#64).toNat := by
                    rw [BitVec.toNat_add, BitVec.toNat_add]
                    dsimp only [wOff, wSz]
                    rw [bv_c0_zext32_64, bv_c0_zext32_64]
                    simp only [← hw0_nat, ← hw1_nat]; assumption
                  omega
                have hp2 : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by
                  rw [m6_bv64_add1 (by rw [hp1]; omega), hp1]
                have hcr_wf := hw.arena.refs_wf cr.toNat hcr_ref
                have hcr_eq : s.core.wstk[(p + 1#64).toNat]'(by omega) = cr := by
                  rw [List.getElem?_eq_getElem (by omega)] at hcr_s
                  simpa [hp1] using Option.some.inj hcr_s
                have hcr2_lt : (cr.setWidth 64 + 2#64).toNat = cr.toNat + 2 := by
                  simp [BitVec.toNat_add]; omega
                have hcr_bd : cr.toNat < s.core.arena.length := by omega
                have hcr2_bd : (cr.setWidth 64 + 2#64).toNat < s.core.arena.length := by omega
                have hcr_bd' : (BitVec.setWidth 64
                    (s.core.wstk[(p + 1#64).toNat]'(by omega))).toNat < s.core.arena.length := by
                  rw [hcr_eq, bv_c0_zext32_64]; exact hcr_bd
                have hcr2_bd' : (BitVec.setWidth 64
                    (s.core.wstk[(p + 1#64).toNat]'(by omega)) + 2#64).toNat <
                    s.core.arena.length := by
                  rw [hcr_eq]; exact hcr2_bd
                let sz : BitVec 32 := s.core.arena[(cr.setWidth 64 + 2#64).toNat]'hcr2_bd
                have hsz_eq_ar : sz.toNat = fullArenaClauseSizeCore s.core cr.toNat := by
                  unfold fullArenaClauseSizeCore; dsimp only [sz]
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                  simp only [hcr2_lt]
                have hsz_eq_hc : s.core.arena[(BitVec.setWidth 64
                    (s.core.wstk[(p + 1#64).toNat]'(by omega)) + 2#64).toNat]'(by
                      rw [hcr_eq]; exact hcr2_bd) = sz := by
                  simp only [hcr_eq, sz]
                have hstep_occ : ∀ flX mX, flX.length = c.max_vars →
                    (FullMem c { s with core := { s.core with flags := flX } } ⋆ R) mX →
                    Jw (p + 1#64 + 1#64, lim + 1#64, ()) mX := fun flX mX hflX hmX =>
                  hJw (p + 1#64 + 1#64, lim + 1#64, ()) mX (by dsimp only; omega)
                    ⟨by omega, by omega, by
                      rw [hp2, show (wOff + wSz).toNat - (p.toNat + 2) =
                        (wOff + wSz).toNat - p.toNat - 2 by omega]
                      exact hslice2, flX, hflX, hmX⟩
                m6_to_group; try refine wp_unroll_group fun _ _ => ?_
                try refine wp_unroll_group fun _ _ => ?_
                m6_split; · m6_steps; exact hstep_occ flW mw hflW_len hmw
                m6_split; · m6_steps; exact hstep_occ flW mw hflW_len hmw
                have hsz_le16 : sz.toNat ≤ 16 := by
                  have h1 : ¬ 16 < (s.core.arena[(BitVec.setWidth 64
                      (s.core.wstk[(p + 1#64).toNat]'(by omega)) + 2#64).toNat]'(by
                        rw [hcr_eq]; exact hcr2_bd)).toNat := ‹_›
                  rw [hsz_eq_hc] at h1; omega
                have hcr3_sz : cr.toNat + 3 + sz.toNat ≤ s.core.arena.length := by
                  have := hcr_wf.2.2; omega
                m6_to_group
                refine wp_loop_inv (ts := [i32])
                  (fun (i, ()) mi => i.toNat ≤ sz.toNat ∧ ∃ flI : List (BitVec 32),
                    flI.length = c.max_vars ∧
                    (FullMem c { s with core := { s.core with flags := flI } } ⋆ R) mi)
                  (fun (i, ()) _ => sz.toNat - i.toNat)
                  (fun _ hJi => by
                    m6_steps; exact hJi (0#32, ()) mw ⟨Nat.zero_le _, flW, hflW_len, hmw⟩)
                  (fun _ (i, ()) mi ⟨hi_le, flI, hflI_len, hmi⟩ hJi => by
                    m6_split; rotate_left
                    · m6_steps; exact hstep_occ flI mi hflI_len hmi
                    have hi_lt : i.toNat < sz.toNat := by
                      have h1 : i.toNat < (s.core.arena[(BitVec.setWidth 64
                          (s.core.wstk[(p + 1#64).toNat]'(by omega)) + 2#64).toNat]'(by
                            rw [hcr_eq]; exact hcr2_bd)).toNat := ‹_›
                      rwa [hsz_eq_hc] at h1
                    have hi1 : (i + 1#32).toNat = i.toNat + 1 := m6_bv32_add1 (by omega)
                    have hidx_ar : (cr.setWidth 64 + 3#64 + i.setWidth 64).toNat <
                        s.core.arena.length := by
                      simp [BitVec.toNat_add]; omega
                    have hidx_ar' : (BitVec.setWidth 64
                        (s.core.wstk[(p + 1#64).toNat]'(by omega)) + 3#64 +
                        i.setWidth 64).toNat < s.core.arena.length := by
                      rw [hcr_eq]; exact hidx_ar
                    m6_to_group
                    refine wp_join_group (ts := [])
                      (fun (_ : Tup Val []) m2 => ∃ fl2 : List (BitVec 32),
                        fl2.length = c.max_vars ∧
                        (FullMem c { s with core := { s.core with flags := fl2 } } ⋆ R) m2)
                      (fun _ () m2 ⟨fl2, hfl2_len, hm2⟩ => by
                        m6_steps
                        exact hJi (i + 1#32, ()) m2 (by dsimp only; omega)
                          ⟨by omega, fl2, hfl2_len, hm2⟩)
                      (fun _ hJif => by
                        try refine wp_unroll_group fun _ _ => ?_
                        m6_split; rotate_left
                        · m6_steps; exact hJif () mi ⟨flI, hflI_len, hmi⟩
                        have hlv_lt : (((s.core.arena[(BitVec.setWidth 64
                            (s.core.wstk[(p + 1#64).toNat]'(by omega)) + 3#64 +
                            i.setWidth 64).toNat]'(by rw [hcr_eq]; exact hidx_ar)) >>>
                            (1 : Nat)).setWidth 64).toNat < c.max_vars := by
                          have : (((s.core.arena[(BitVec.setWidth 64
                              (s.core.wstk[(p + 1#64).toNat]'(by omega)) + 3#64 +
                              i.setWidth 64).toNat]'(by rw [hcr_eq]; exact hidx_ar)) >>>
                              (1 : Nat)).setWidth 64).toNat < s.core.cur_vars % 2 ^ 64 := by
                            simp only [bv_c0]; bv_omega
                          omega
                        m6_split; rotate_left
                        · m6_steps; exact hJif () mi ⟨flI, hflI_len, hmi⟩
                        m6_split; rotate_left
                        · m6_steps; exact hJif () mi ⟨flI, hflI_len, hmi⟩
                        m6_steps
                        exact hJif () _ ⟨_, List.length_set.trans hflI_len, by assumption⟩)))))

/-! ## 3. `full_m6_sweep_build_pht_wp` (`24/39`) -/

theorem full_m6_sweep_build_pht_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec) :
    ∀ args m Q X, m6SweepBuildPhtSpec args m Q X →
      Func.wp Γ full_m6_sweep_build_pht_body args m Q X := by
  rintro ⟨h, nv, smask, ⟨⟩⟩ m Q X
    ⟨c, s, L, R, rfl, hlen, hL_len, hL_mv, hnv_L, hnv_mx, hws_lt, hm, hQ⟩
  have hcv_le := hlen.core_ok.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hscr_len := hlen.scratch_ok.scratch_buf_len
  have hws_len := hlen.scratch_ok.work_stk1_len
  have hsig_len := hlen.scratch_ok.sim_sig_len
  have hval_len := hlen.core_ok.vals_len
  have hmL := L.hmaxV; have haL := L.hacap
  have hmv64_lt : k6MaxV c.scratch_cap < 2 ^ 32 := by rw [← hL_mv]; omega
  have hmv_eq : BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) = L.mv32 := by
    apply BitVec.eq_of_toNat_eq
    simp only [k6_mv32_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [← hL_mv]; omega
  have hpm_c0 := m6_ptr_phtMerged L c.pScratchBuf
  have hpn_c0 : c.pScratchBuf + BitVec.setWidth 64 (1280 : BitVec 32) * 4 =
      c.pScratchBuf + BitVec.ofNat 64 (4 * k6PhtNext) := rfl
  have hpn_c0' : c.pScratchBuf + BitVec.ofNat 64 1280 * 4 =
      c.pScratchBuf + BitVec.ofNat 64 (4 * k6PhtNext) := rfl
  have hpm_end : L.phtMerged + L.maxV ≤ c.scratch_cap := by
    rw [← hL_len]; unfold K6Layout.scrLen K6Layout.k6Base K6Layout.k6Fixed K6Layout.phtMerged
    omega
  unfold Func.wp full_m6_sweep_build_pht_body
  m6_steps
  refine m6_call_max_v hMaxV (c := c) rfl ?_
  m6_split
  · exfalso; have h0 := congrArg BitVec.toNat hc
    rw [hmv_eq, k6_mv32_toNat] at h0; simp at h0; omega
  m6_split
  · exfalso; rw [← hL_mv, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc; omega
  m6_to_group
  refine wp_loop_inv (ts := [i32])
    (fun (b, ()) mb => b.toNat ≤ k6PhtSz ∧ ∃ scr1 : List (BitVec 32),
      scr1.length = c.scratch_cap ∧
      (∀ j < c.scratch_cap, j < k6PhtHead ∨ L.phtMerged ≤ j →
        scr1[j]? = s.scratch.scratch_buf[j]?) ∧
      (∀ k < b.toNat, scr1[k6PhtHead + k]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) ∧
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr1 } } ⋆ R) mb)
    (fun (b, ()) _ => k6PhtSz - b.toNat)
    (fun _ hJb => by
      m6_steps
      exact hJb (0#32, ()) m ⟨Nat.zero_le _, s.scratch.scratch_buf, hscr_len,
        fun _ _ _ => rfl, fun _ hk => by simp at hk, hm⟩)
    (fun _ (b, ()) mb ⟨hb_le, scr1, hsl1, hpre1, hhd1, hmb⟩ hJb => by
      m6_split
      · have hb_lt : b.toNat < k6PhtSz := hc
        have hb1 : (b + 1#32).toNat = b.toNat + 1 :=
          m6_bv32_add1 (by unfold k6PhtSz at hb_lt; omega)
        have hidx_eq : ((256 + b).setWidth 64).toNat = k6PhtHead + b.toNat := by
          simp only [k6PhtHead, k6PhtSz] at hb_lt ⊢; rw [bv_c0_zext32_64]; bv_omega
        have hidx_bd : ((256 + b).setWidth 64).toNat < scr1.length := by
          rw [hsl1, hidx_eq]; unfold k6PhtHead at ⊢; unfold k6PhtSz at hb_lt
          unfold K6Layout.phtMerged at hpm_end; omega
        m6_steps
        refine hJb (b + 1#32, ()) _ (by dsimp only; rw [hb1]; unfold k6PhtSz at hb_lt ⊢; omega)
          ⟨by omega, _, List.length_set.trans hsl1, fun j hj hdom => ?_,
           fun k hk => ?_, by assumption⟩
        · rw [List.getElem?_set_ne (by
            rw [hidx_eq]; unfold k6PhtHead K6Layout.phtMerged at hdom; unfold k6PhtHead
            unfold k6PhtSz at hb_lt; omega)]
          exact hpre1 j hj hdom
        · rw [hb1] at hk
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
          · rw [List.getElem?_set_ne (by rw [hidx_eq]; omega)]; exact hhd1 k hlt
          · rw [hidx_eq, List.getElem?_set_self (by rw [← hidx_eq]; exact hidx_bd),
              Option.getD_some]; rfl
      · have hb_eq : b.toNat = k6PhtSz := by
          unfold k6PhtSz at hb_le ⊢
          rw [show (1024 : BitVec 32).toNat = 1024 from rfl] at hc; omega
        have hp0 : M6PhtOk 0 scr1 := m6_phtOk_zero (hb_eq ▸ hhd1)
        m6_to_group
        refine wp_loop_inv (ts := [i32])
          (fun (i, ()) mi => i.toNat ≤ nv.toNat ∧ ∃ scr2 : List (BitVec 32),
            scr2.length = c.scratch_cap ∧
            (∀ j < c.scratch_cap, j < k6PhtHead ∨ L.phtMerged ≤ j →
              scr2[j]? = s.scratch.scratch_buf[j]?) ∧
            M6PhtOk i.toNat scr2 ∧
            (FullMem c { s with scratch := { s.scratch with scratch_buf := scr2 } } ⋆ R) mi)
          (fun (i, ()) _ => nv.toNat - i.toNat)
          (fun _ hJi => by
            m6_steps; exact hJi (0#32, ()) mb ⟨Nat.zero_le _, scr1, hsl1, hpre1, hp0, hmb⟩)
          (fun _ (i, ()) mi ⟨hi_le, scr2, hsl2, hpre2, hp2, hmi⟩ hJi => by
            clear hm hmb
            m6_split; rotate_left
            · have hi_eq : i.toNat = nv.toNat := by omega
              m6_steps; exact hQ scr2 mi hsl2 hpre2 (hi_eq ▸ hp2) hmi
            have hi_lt : i.toNat < nv.toNat := hc
            have hi_mv : i.toNat < L.maxV := by omega
            have hi1 : (i + 1#32).toNat = i.toNat + 1 := m6_bv32_add1 (by omega)
            have hi_ws : (i.setWidth 64).toNat < s.scratch.work_stk1.length := by
              rw [hws_len, bv_c0_zext32_64]; omega
            have hgv_lt : (s.scratch.work_stk1[(i.setWidth 64).toNat]'hi_ws).toNat <
                c.max_vars := by
              have hg := hws_lt i.toNat hi_lt
              rw [List.getElem?_eq_getElem (by rw [hws_len]; omega), Option.getD_some] at hg
              simp only [bv_c0_zext32_64]; exact Nat.lt_of_lt_of_le hg hcv_le
            have hgv_val : ((BitVec.setWidth 64
                (s.scratch.work_stk1[(i.setWidth 64).toNat]'hi_ws)) <<< (1 : Nat)).toNat <
                s.core.vals.length := by
              rw [hval_len]; exact m6_bv64_shl1_zext_lt hgv_lt (by omega)
            have hgv_sig : (BitVec.setWidth 64
                (s.scratch.work_stk1[(i.setWidth 64).toNat]'hi_ws)).toNat <
                s.scratch.sim_sig.length := by
              rw [hsig_len]; exact m6_bv64_zext_lt hgv_lt
            m6_to_group
            refine wp_join_group (ts := [])
              (fun () mN => ∃ scrN : List (BitVec 32),
                scrN.length = c.scratch_cap ∧
                (∀ j < c.scratch_cap, j < k6PhtHead ∨ L.phtMerged ≤ j →
                  scrN[j]? = s.scratch.scratch_buf[j]?) ∧
                M6PhtOk (i.toNat + 1) scrN ∧
                (FullMem c { s with scratch := { s.scratch with scratch_buf := scrN } } ⋆ R) mN)
              (fun _ () mN ⟨scrN, hslN, hpreN, hpN, hmN⟩ => by
                m6_steps
                exact hJi (i + 1#32, ()) mN (by dsimp only; rw [hi1]; omega)
                  ⟨by omega, scrN, hslN, hpreN, by rw [hi1]; exact hpN, hmN⟩)
              (fun _ hJnxt => by
                m6_to_group
                refine wp_join_group (ts := [])
                  (fun () mE => mE = mi)
                  (fun _ () mE hmE => by
                    subst hmE
                    change wp _ _ _ _ _
                    c0_hsteps_nogrp; try rw [hpn_c0]; try rw [hpn_c0']
                    open scoped M6PhtMem in c0_hsteps!
                    refine hJnxt () _ ⟨_, List.length_set.trans hsl2, fun j hj hdom => ?_,
                      m6_phtOk_step_merged hi_mv (by rw [hsl2, hL_len]; exact le_refl _) hp2,
                      by assumption⟩
                    rw [List.getElem?_set_ne (by
                      unfold k6PhtNext; unfold k6PhtHead K6Layout.phtMerged at hdom; omega)]
                    exact hpre2 j hj hdom)
                  (fun _ hJelse => by
                    change wp _ _ _ _ _
                    c0_hsteps_nogrp; try rw [hmv_eq]; try rw [hpm_c0]
                    try rw [hpn_c0]; try rw [hpn_c0']
                    open scoped M6PhtMem in m6_split; rotate_left
                    · m6_steps; exact hJelse () mi rfl
                    change wp _ _ _ _ _
                    c0_hsteps_nogrp; try rw [hmv_eq]; try rw [hpm_c0]
                    try rw [hpn_c0]; try rw [hpn_c0']
                    open scoped M6PhtMem in m6_split; rotate_left
                    · m6_steps; exact hJelse () mi rfl
                    m6_to_group
                    refine wp_join_group (ts := [i64])
                      (fun (key, ()) mkey => mkey = mi)
                      (fun _ (key, ()) mkey hmkey => by
                        subst hmkey
                        let hidx : BitVec 32 :=
                          ((key ^^^ (key >>> (17 : Nat)) ^^^ (key >>> (34 : Nat)) ^^^
                            (key >>> (51 : Nat))) &&& 1023#64).setWidth 32
                        have hh_lt : hidx.toNat < k6PhtSz := m6_hidx_lt_1024 _
                        have hh_eq : ((256 + hidx).setWidth 64).toNat =
                            k6PhtHead + hidx.toNat := by
                          simp only [k6PhtHead, k6PhtSz] at hh_lt ⊢
                          rw [bv_c0_zext32_64]; bv_omega
                        have hh_bd : ((256 + hidx).setWidth 64).toNat < scr2.length := by
                          rw [hsl2, hh_eq]
                          unfold k6PhtHead at ⊢; unfold k6PhtSz at hh_lt
                          unfold K6Layout.phtMerged at hpm_end; omega
                        change wp _ _ _ _ _
                        c0_hsteps_nogrp; try rw [hmv_eq]; try rw [hpm_c0]
                        try rw [hpn_c0]; try rw [hpn_c0']
                        open scoped M6PhtMem in c0_hsteps!
                        have hstep := m6_phtOk_step_unmerged (L := L) hi_mv hh_lt
                          (by rw [hsl2, hL_len]; exact le_refl _) hp2
                        have hi_ofn : BitVec.ofNat 32 i.toNat = i := by
                          apply BitVec.eq_of_toNat_eq; simp
                        rw [hi_ofn] at hstep
                        have hhd_get : scr2[((256 + hidx).setWidth 64).toNat]'hh_bd =
                            scr2[k6PhtHead + hidx.toNat]?.getD 0xFFFFFFFF#32 := by
                          rw [List.getElem?_eq_getElem (by rw [← hh_eq]; exact hh_bd),
                            Option.getD_some]
                          congr 1
                        have hbuf_eq :
                            ((scr2.set (k6PhtNext + i.toNat)
                                (scr2[((256 + hidx).setWidth 64).toNat]'hh_bd)).set
                              ((256 + hidx).setWidth 64).toNat i) =
                            ((scr2.set (k6PhtNext + i.toNat)
                                (scr2[k6PhtHead + hidx.toNat]?.getD 0xFFFFFFFF#32)).set
                              (k6PhtHead + hidx.toNat) i) := by
                          rw [hhd_get, hh_eq]
                        refine hJnxt () _
                          ⟨(scr2.set (k6PhtNext + i.toNat)
                             (scr2[k6PhtHead + hidx.toNat]?.getD 0xFFFFFFFF#32)).set
                             (k6PhtHead + hidx.toNat) i,
                           by simp [hsl2], fun j hj hdom => ?_, hstep, ?_⟩
                        · rw [List.getElem?_set_ne (by
                              unfold k6PhtHead; unfold k6PhtHead K6Layout.phtMerged at hdom
                              unfold k6PhtSz at hh_lt; omega),
                            List.getElem?_set_ne (by
                              unfold k6PhtNext; unfold k6PhtHead K6Layout.phtMerged at hdom
                              omega)]
                          exact hpre2 j hj hdom
                        · rw [← hbuf_eq]; assumption)
                      (fun _ hJkey => by
                        m6_split <;> (m6_steps; exact hJkey _ mi rfl))))))

/-! ## 4. `full_m6_extract_pht_wp` (`25/39`) -/

theorem full_m6_extract_pht_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec) :
    ∀ args m Q X, m6ExtractPhtSpec args m Q X →
      Func.wp Γ full_m6_extract_pht_body args m Q X := by
  rintro ⟨h, nv, smask, ⟨⟩⟩ m Q X
    ⟨c, s, L, R, rfl, hlen, hL_len, hL_mv, hnv_L, hnv_cv_bd, hws_lt, hpht0, hm, hQ⟩
  have hcv_le := hlen.core_ok.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hscr_len := hlen.scratch_ok.scratch_buf_len
  have hws_len := hlen.scratch_ok.work_stk1_len
  have hsig_len := hlen.scratch_ok.sim_sig_len
  have hss_len := hlen.scratch_ok.shrink_stk_len
  have hmclr_len := hlen.core_ok.min_clr_len_arr
  have hmL := L.hmaxV; have haL := L.hacap
  have hmv64_lt : k6MaxV c.scratch_cap < 2 ^ 32 := by rw [← hL_mv]; omega
  have hmv_eq : BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) = L.mv32 := by
    apply BitVec.eq_of_toNat_eq
    simp only [k6_mv32_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [← hL_mv]; omega
  have hpn_c0 : c.pScratchBuf + BitVec.setWidth 64 (1280 : BitVec 32) * 4 =
      c.pScratchBuf + BitVec.ofNat 64 (4 * k6PhtNext) := rfl
  have hpn_c0' : c.pScratchBuf + BitVec.ofNat 64 1280 * 4 =
      c.pScratchBuf + BitVec.ofNat 64 (4 * k6PhtNext) := rfl
  have hpm_end : L.phtMerged + L.maxV ≤ c.scratch_cap := by
    rw [← hL_len]; unfold K6Layout.scrLen K6Layout.k6Base K6Layout.k6Fixed K6Layout.phtMerged
    omega
  have hpart0 : M6PartitionOk nv.toNat 0 s.scratch.scratch_buf s.scratch.shrink_stk :=
    ⟨Nat.zero_le _, hpht0.2, fun _ h => by omega⟩
  unfold Func.wp full_m6_extract_pht_body
  m6_steps
  refine m6_call_max_v hMaxV (c := c) rfl ?_
  m6_split
  · exfalso; have h0 := congrArg BitVec.toNat hc
    rw [hmv_eq, k6_mv32_toNat] at h0; simp at h0; omega
  m6_split
  · exfalso; rw [← hL_mv, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc; omega
  m6_to_group
  -- Outer loop (`ncls, b`)
  refine wp_loop_inv (ts := [i32, i32])
    (fun (ncls, b, ()) mb => b.toNat ≤ k6PhtSz ∧ ncls.toNat ≤ c.max_vars ∧
      ∃ scrB sstkB mclrB, scrB.length = c.scratch_cap ∧ sstkB.length = c.max_vars ∧
        mclrB.length = c.max_vars ∧
        (∀ j < c.scratch_cap, j < k6PhtHead ∨ L.phtMerged ≤ j →
          scrB[j]? = s.scratch.scratch_buf[j]?) ∧
        M6PhtOk nv.toNat scrB ∧ M6PartitionOk nv.toNat ncls.toNat scrB sstkB ∧
        (FullMem c { s with core := { s.core with min_clr := mclrB }
                            scratch := { s.scratch with scratch_buf := scrB,
                                                        shrink_stk := sstkB } } ⋆ R) mb)
    (fun (_, b, ()) _ => k6PhtSz - b.toNat)
    (fun _ hJb => by
      m6_steps
      exact hJb (0#32, 0#32, ()) m
        ⟨Nat.zero_le _, Nat.zero_le _, s.scratch.scratch_buf, s.scratch.shrink_stk,
         s.core.min_clr, hscr_len, hss_len, hmclr_len, fun _ _ _ => rfl, hpht0, hpart0, hm⟩)
    (fun _ (ncls, b, ()) mb
        ⟨hb_le, hncls_le, scrB, sstkB, mclrB, hslB, hssB, hmcB, hpreB, hphtB, hpartB, hmb⟩ hJb => by
      clear hm
      m6_split; rotate_left
      · m6_steps
        exact hQ ncls scrB sstkB mclrB mb hslB hssB hmcB hpreB hncls_le hpartB hmb
      have hb_lt : b.toNat < k6PhtSz := hc
      have hb1 : (b + 1#32).toNat = b.toNat + 1 :=
        m6_bv32_add1 (by unfold k6PhtSz at hb_lt; omega)
      m6_to_group
      -- `guard` loop (`nclsL, guard`)
      refine wp_loop_inv (ts := [i32, i32])
        (fun (nclsL, guard, ()) ml => guard.toNat ≤ nv.toNat ∧ nclsL.toNat ≤ c.max_vars ∧
          ∃ scrL sstkL mclrL, scrL.length = c.scratch_cap ∧ sstkL.length = c.max_vars ∧
            mclrL.length = c.max_vars ∧
            (∀ j < c.scratch_cap, j < k6PhtHead ∨ L.phtMerged ≤ j →
              scrL[j]? = s.scratch.scratch_buf[j]?) ∧
            M6PhtOk nv.toNat scrL ∧ M6PartitionOk nv.toNat nclsL.toNat scrL sstkL ∧
            (FullMem c { s with core := { s.core with min_clr := mclrL }
                                scratch := { s.scratch with scratch_buf := scrL,
                                                            shrink_stk := sstkL } } ⋆ R) ml)
        (fun (_, guard, ()) _ => guard.toNat)
        (fun _ hJg => by
          m6_steps
          exact hJg (ncls, nv, ()) mb
            ⟨le_refl _, hncls_le, scrB, sstkB, mclrB, hslB, hssB, hmcB, hpreB, hphtB,
             hpartB, hmb⟩)
        (fun _ (nclsL, guard, ()) ml
            ⟨hg_le, hnl_le, scrL, sstkL, mclrL, hslL, hssL, hmcL, hpreL, hphtL, hpartL,
             hml⟩ hJg => by
          clear hmb
          have hbh_eq : ((256 + b).setWidth 64).toNat = k6PhtHead + b.toNat := by
            simp only [k6PhtHead, k6PhtSz] at hb_lt ⊢; rw [bv_c0_zext32_64]; bv_omega
          have hbh_bd : ((256 + b).setWidth 64).toNat < scrL.length := by
            rw [hslL, hbh_eq]
            unfold k6PhtHead at ⊢; unfold k6PhtSz at hb_lt
            unfold K6Layout.phtMerged at hpm_end; omega
          m6_to_group
          refine wp_join_group (ts := [])
            (fun () mG => mG = ml)
            (fun _ () mG hmG => by
              subst hmG
              m6_steps
              exact hJb (nclsL, b + 1#32, ()) mG (by dsimp only; rw [hb1]; omega)
                ⟨by omega, hnl_le, scrL, sstkL, mclrL, hslL, hssL, hmcL, hpreL, hphtL,
                 hpartL, hml⟩)
            (fun _ hJguard => by
              m6_split; rotate_left
              · m6_steps; exact hJguard () ml rfl
              m6_split; rotate_left
              · m6_steps; exact hJguard () ml rfl
              have hg_lt : 0 < guard.toNat := hc
              have hg1 : (guard - 1#32).toNat = guard.toNat - 1 := bv32_sub1_of_pos hg_lt
              let h0 := scrL[((256 + b).setWidth 64).toNat]'hbh_bd
              have hh0_lt : h0.toNat < nv.toNat := ‹_›
              have hh0_mv : h0.toNat < L.maxV := by omega
              have hh0_mc : (h0.setWidth 64).toNat < mclrL.length := by
                rw [hmcL, bv_c0_zext32_64]; omega
              have hh0_ws : (h0.setWidth 64).toNat < s.scratch.work_stk1.length := by
                rw [hws_len, bv_c0_zext32_64]; omega
              have hgv0_sig : (BitVec.setWidth 64
                  (s.scratch.work_stk1[(h0.setWidth 64).toNat]'hh0_ws)).toNat <
                  s.scratch.sim_sig.length := by
                have hg := hws_lt h0.toNat hh0_lt
                rw [List.getElem?_eq_getElem (by rw [hws_len]; omega), Option.getD_some] at hg
                rw [hsig_len, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                exact Nat.lt_of_lt_of_le hg hcv_le
              have hh0_nx_bd : k6PhtNext + h0.toNat < scrL.length := by
                unfold k6PhtNext at ⊢; unfold K6Layout.phtMerged at hpm_end; rw [hslL]; omega
              change wp _ _ _ _ _
              c0_hsteps_nogrp; try rw [hpn_c0]; try rw [hpn_c0']
              open scoped M6PhtMem in m6_to_group
              try dsimp only; try dsimp only at hml; try dsimp only at hm
              let scrL1 := scrL.set ((256 + b).setWidth 64).toNat 0xFFFFFFFF#32
              let mclrL1 := mclrL.set (h0.setWidth 64).toNat 0#32
              have hmcL1 : mclrL1.length = c.max_vars := List.length_set.trans hmcL
              have hslL1 : scrL1.length = c.scratch_cap := List.length_set.trans hslL
              have hpreL1 : ∀ j < c.scratch_cap, j < k6PhtHead ∨ L.phtMerged ≤ j →
                  scrL1[j]? = s.scratch.scratch_buf[j]? := fun j hj hdom => by
                dsimp only [scrL1]
                rw [hbh_eq, List.getElem?_set_ne (by
                  unfold k6PhtHead; unfold k6PhtHead K6Layout.phtMerged at hdom
                  unfold k6PhtSz at hb_lt; omega)]
                exact hpreL j hj hdom
              have hphtL1 : M6PhtOk nv.toNat scrL1 := by
                dsimp only [scrL1]; rw [hbh_eq]
                exact m6_phtOk_set_head hb_lt (by rw [← hbh_eq]; exact hbh_bd) (Or.inl rfl) hphtL
              have hpartL1 : M6PartitionOk nv.toNat nclsL.toNat scrL1 sstkL := by
                dsimp only [scrL1]; rw [hbh_eq]; exact m6_partOk_set_head hb_lt hpartL
              have hh0_nx_bd1 : k6PhtNext + h0.toNat < scrL1.length := by
                rw [hslL1]; unfold k6PhtNext at ⊢; unfold K6Layout.phtMerged at hpm_end; omega
              let y0 := scrL1[k6PhtNext + h0.toNat]'hh0_nx_bd1
              have hy0_lt : y0 = 0xFFFFFFFF#32 ∨ y0.toNat < h0.toNat := by
                have hp2 := hphtL1.2 h0.toNat hh0_lt
                dsimp only [y0]; rwa [List.getElem?_eq_getElem hh0_nx_bd1, Option.getD_some] at hp2
              -- Inner loop: `(keep_tail, cls_tail, csz, y, inner_g)`
              refine wp_loop_inv (ts := [i32, i32, i32, i32, i32])
                (fun (keep_tail, cls_tail, csz, y, inner_g, ()) mIn =>
                  inner_g.toNat ≤ nv.toNat ∧ cls_tail.toNat < nv.toNat ∧
                  (keep_tail = 0xFFFFFFFF#32 ∨ keep_tail.toNat < nv.toNat) ∧
                  (y = 0xFFFFFFFF#32 ∨ (y.toNat < cls_tail.toNat ∧
                    (keep_tail ≠ 0xFFFFFFFF#32 → y.toNat < keep_tail.toNat))) ∧
                  ∃ scrI mclrI, scrI.length = c.scratch_cap ∧ mclrI.length = c.max_vars ∧
                    (∀ j < c.scratch_cap, j < k6PhtHead ∨ L.phtMerged ≤ j →
                      scrI[j]? = s.scratch.scratch_buf[j]?) ∧
                    M6PhtOk nv.toNat scrI ∧ M6PartitionOk nv.toNat nclsL.toNat scrI sstkL ∧
                    (FullMem c { s with core := { s.core with min_clr := mclrI }
                                        scratch := { s.scratch with scratch_buf := scrI,
                                                                    shrink_stk := sstkL } } ⋆ R)
                      mIn)
                (fun (_, _, _, _, inner_g, ()) _ => inner_g.toNat)
                (fun _ hJi => by
                  m6_steps
                  refine hJi (0xFFFFFFFF#32, h0, 1#32, y0, nv, ()) _
                    ⟨le_refl _, hh0_lt, Or.inl rfl, ?_, scrL1, mclrL1, hslL1, hmcL1,
                     hpreL1, hphtL1, hpartL1, ?_⟩
                  · rcases hy0_lt with hyff | hylt
                    · exact Or.inl hyff
                    · exact Or.inr ⟨hylt, fun h => absurd rfl h⟩
                  · dsimp only [scrL1, mclrL1]; assumption)
                (fun _ (keep_tail, cls_tail, csz, y, inner_g, ()) mIn
                    ⟨hig_le, hct_lt, hkt_ok, hy_ok, scrI, mclrI, hslI, hmcI, hpreI, hphtI,
                      hpartI, hmin⟩ hJi => by
                  try clear hml
                  have hct_mv : cls_tail.toNat < L.maxV := by omega
                  have hct_bd : k6PhtNext + cls_tail.toNat < scrI.length := by
                    rw [hslI]; unfold k6PhtNext at ⊢; unfold K6Layout.phtMerged at hpm_end; omega
                  m6_to_group
                  refine wp_join_group (ts := [])
                    (fun () mF => mF = mIn)
                    (fun _ () mF hmF => by
                      subst mF
                      change wp _ _ _ _ _
                      c0_hsteps_nogrp; try rw [hpn_c0]; try rw [hpn_c0']
                      open scoped M6PhtMem in m6_to_group
                      let scrF1 := scrI.set (k6PhtNext + cls_tail.toNat) 0xFFFFFFFF#32
                      have hslF1 : scrF1.length = c.scratch_cap := List.length_set.trans hslI
                      have hpreF1 : ∀ j < c.scratch_cap, j < k6PhtHead ∨ L.phtMerged ≤ j →
                          scrF1[j]? = s.scratch.scratch_buf[j]? := fun j hj hdom => by
                        dsimp only [scrF1]
                        rw [List.getElem?_set_ne (by
                          unfold k6PhtNext; unfold k6PhtHead K6Layout.phtMerged at hdom; omega)]
                        exact hpreI j hj hdom
                      have hphtF1 : M6PhtOk nv.toNat scrF1 :=
                        m6_phtOk_set_next hct_lt hct_bd (Or.inl rfl) hphtI
                      have hpartF1 : M6PartitionOk nv.toNat nclsL.toNat scrF1 sstkL :=
                        m6_partOk_set_next hct_lt hct_bd (Or.inl rfl) hpartI
                      refine wp_join_group (ts := [])
                        (fun () mk => ∃ scrK, scrK.length = c.scratch_cap ∧
                          (∀ j < c.scratch_cap, j < k6PhtHead ∨ L.phtMerged ≤ j →
                            scrK[j]? = s.scratch.scratch_buf[j]?) ∧
                          M6PhtOk nv.toNat scrK ∧ M6PartitionOk nv.toNat nclsL.toNat scrK sstkL ∧
                          (FullMem c { s with core := { s.core with min_clr := mclrI }
                                              scratch := { s.scratch with scratch_buf := scrK,
                                                                          shrink_stk := sstkL } } ⋆
                            R) mk)
                        (fun _ () mk ⟨scrK, hslK, hpreK, hphtK, hpartK, hmK⟩ => by
                          m6_to_group
                          refine wp_join_group (ts := [i32])
                            (fun (nclsK, ()) mk' => nclsK.toNat ≤ c.max_vars ∧
                              ∃ sstkK, sstkK.length = c.max_vars ∧
                                M6PartitionOk nv.toNat nclsK.toNat scrK sstkK ∧
                                (FullMem c { s with
                                  core := { s.core with min_clr := mclrI }
                                  scratch := { s.scratch with scratch_buf := scrK,
                                                              shrink_stk := sstkK } } ⋆ R) mk')
                            (fun _ (nclsK, ()) mk' ⟨hnlK, sstkK, hssK, hpartK', hmK'⟩ => by
                              m6_steps
                              exact hJg (nclsK, guard - 1#32, ()) mk'
                                (by dsimp only; rw [hg1]; omega)
                                ⟨by omega, hnlK, scrK, sstkK, mclrI, hslK, hssK, hmcI, hpreK,
                                 hphtK, hpartK', hmK'⟩)
                            (fun _ hJncls => by
                              try clear hmK_unused
                              clear hphtK hpartI hphtI hpartF1 hphtF1 hphtL1 hpartL1
                              clear hphtL hpartL hphtB hpartB
                              try clear hm; try clear hmin
                              try dsimp only at hmK
                              m6_split
                              · m6_split
                                · have hncls_lt : nclsL.toNat < c.max_vars := by
                                    rw [Nat.mod_eq_of_lt (Nat.lt_trans c.hmaxv
                                      (by unfold dimacsBound; decide))] at hc
                                    exact hc
                                  have hncls_ss : (nclsL.setWidth 64).toNat < sstkL.length := by
                                    rw [hssL, bv_c0_zext32_64]; exact hncls_lt
                                  have hncls_u31 : nclsL.toNat < 2 ^ 31 :=
                                    Nat.lt_trans hncls_lt (Nat.lt_trans hmx (by decide))
                                  have hncls1 : (nclsL + 1#32).toNat = nclsL.toNat + 1 :=
                                    m6_bv32_add1 hncls_u31
                                  m6_steps
                                  exact hJncls (nclsL + 1#32, ()) _
                                    ⟨by rw [hncls1]; exact Nat.succ_le_of_lt hncls_lt,
                                     sstkL.set (nclsL.setWidth 64).toNat h0,
                                     List.length_set.trans hssL,
                                     by simpa only [bv_c0_zext32_64, hncls1] using
                                       m6_partOk_push_head (ncls := nclsL.toNat)
                                         (by rw [hssL]; exact Nat.succ_le_of_lt hncls_lt)
                                         hh0_lt hpartK,
                                     by assumption⟩
                                · m6_steps
                                  exact hJncls (nclsL, ()) mk ⟨hnl_le, sstkL, hssL, hpartK, hmK⟩
                              · m6_steps
                                exact hJncls (nclsL, ()) mk ⟨hnl_le, sstkL, hssL, hpartK, hmK⟩))
                        (fun _ hJkt => by
                          m6_split; rotate_left
                          · m6_steps
                            exact hJkt () _ ⟨scrF1, hslF1, hpreF1, hphtF1, hpartF1, by assumption⟩
                          have hkt_lt : keep_tail.toNat < nv.toNat := hc
                          have hkt_mv : keep_tail.toNat < L.maxV := by omega
                          have hkt_bd : k6PhtNext + keep_tail.toNat < scrF1.length := by
                            rw [hslF1]; unfold k6PhtNext at ⊢
                            unfold K6Layout.phtMerged at hpm_end; omega
                          change wp _ _ _ _ _
                          c0_hsteps_nogrp; try rw [hpn_c0]; try rw [hpn_c0']
                          open scoped M6PhtMem in m6_steps
                          exact hJkt () _ ⟨_, List.length_set.trans hslF1, fun j hj hdom => by
                            rw [List.getElem?_set_ne (by
                              unfold k6PhtNext; unfold k6PhtHead K6Layout.phtMerged at hdom; omega)]
                            exact hpreF1 j hj hdom,
                            m6_phtOk_set_next hkt_lt hkt_bd (Or.inl rfl) hphtF1,
                            m6_partOk_set_next hkt_lt hkt_bd (Or.inl rfl) hpartF1, by assumption⟩))
                    (fun _ hJinn => by
                      clear hpartL hphtL hpartB hphtB hpreL hpreB hmcB hssB hslB
                      try clear hm
                      m6_split; rotate_left
                      · m6_steps; exact hJinn () mIn rfl
                      m6_split; rotate_left
                      · m6_steps; exact hJinn () mIn rfl
                      have hy_lt : y.toNat < nv.toNat := ‹_›
                      have hy_not_ff : y ≠ 0xFFFFFFFF#32 := by
                        intro h; subst h
                        have hff : (0xFFFFFFFF#32 : BitVec 32).toNat = 4294967295 := rfl
                        rw [hff] at hy_lt
                        have := Nat.lt_of_lt_of_le hy_lt hnv_L; have := hmL.2; omega
                      have hig_lt : 0 < inner_g.toNat := hc
                      have hig1 : (inner_g - 1#32).toNat = inner_g.toNat - 1 :=
                        bv32_sub1_of_pos hig_lt
                      have hy_mv : y.toNat < L.maxV := Nat.lt_of_lt_of_le hy_lt hnv_L
                      have hy_mc : (y.setWidth 64).toNat < mclrI.length := by
                        rw [hmcI, bv_c0_zext32_64]; exact Nat.lt_of_lt_of_le hy_lt hnv_cv_bd
                      have hy_ws_nat : y.toNat < s.scratch.work_stk1.length := by
                        rw [hws_len]
                        exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hy_lt hnv_cv_bd)
                          (Nat.le_mul_of_pos_left _ (by decide))
                      have hy_ws : (y.setWidth 64).toNat < s.scratch.work_stk1.length := by
                        rw [bv_c0_zext32_64]; exact hy_ws_nat
                      have hgv_sig : (BitVec.setWidth 64
                          (s.scratch.work_stk1[(y.setWidth 64).toNat]'hy_ws)).toNat <
                          s.scratch.sim_sig.length := by
                        have hg := hws_lt y.toNat hy_lt
                        rw [List.getElem?_eq_getElem hy_ws_nat, Option.getD_some] at hg
                        rw [hsig_len, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                        exact Nat.lt_of_lt_of_le hg hcv_le
                      have hy_clt : y.toNat < cls_tail.toNat := by
                        rcases hy_ok with rfl | hyo
                        · exact absurd rfl hy_not_ff
                        · exact hyo.1
                      have hy_nx_bd : k6PhtNext + y.toNat < scrI.length := by
                        rw [hslI]
                        have hsum : k6PhtNext + y.toNat < L.phtMerged := by
                          unfold k6PhtNext K6Layout.phtMerged
                          exact Nat.add_lt_add_left hy_mv 1280
                        exact Nat.lt_of_lt_of_le hsum
                          (Nat.le_trans (Nat.le_add_right _ _) hpm_end)
                      let ny := scrI[k6PhtNext + y.toNat]'hy_nx_bd
                      have hny_lt : ny = 0xFFFFFFFF#32 ∨ ny.toNat < y.toNat := by
                        have hp2 := hphtI.2 y.toNat hy_lt
                        dsimp only [ny]
                        rwa [List.getElem?_eq_getElem hy_nx_bd, Option.getD_some] at hp2
                      change wp _ _ _ _ _
                      c0_hsteps_nogrp; try rw [hpn_c0]; try rw [hpn_c0']
                      open scoped M6PhtMem in m6_to_group
                      dsimp only
                      refine wp_join_group (ts := [i32, i32, i32])
                        (fun (keep_tail', cls_tail', csz', ()) mY => cls_tail'.toNat < nv.toNat ∧
                          (keep_tail' = 0xFFFFFFFF#32 ∨ keep_tail'.toNat < nv.toNat) ∧
                          (cls_tail' = cls_tail ∨ cls_tail' = y) ∧
                          (keep_tail' = keep_tail ∨ keep_tail' = y) ∧
                          ∃ scrY mclrY, scrY.length = c.scratch_cap ∧ mclrY.length = c.max_vars ∧
                            (∀ j < c.scratch_cap, j < k6PhtHead ∨ L.phtMerged ≤ j →
                              scrY[j]? = s.scratch.scratch_buf[j]?) ∧
                            M6PhtOk nv.toNat scrY ∧ M6PartitionOk nv.toNat nclsL.toNat scrY sstkL ∧
                            (FullMem c { s with core := { s.core with min_clr := mclrY }
                                                scratch := { s.scratch with scratch_buf := scrY,
                                                                            shrink_stk := sstkL } }
                              ⋆ R) mY)
                        (fun _ (keep_tail', cls_tail', csz', ()) mY
                            ⟨hctY, hktY, hct_or, hkt_or, scrY, mclrY, hslY, hmcY, hpreY, hphtY,
                              hpartY, hmY⟩ => by
                          m6_steps
                          refine hJi (keep_tail', cls_tail', csz', ny, inner_g - 1#32, ()) mY
                            (by dsimp only; rw [hig1]; exact Nat.sub_lt hig_lt (by omega))
                            ⟨by omega, hctY, hktY, ?_, scrY, mclrY, hslY, hmcY, hpreY, hphtY,
                             hpartY, hmY⟩
                          rcases hny_lt with hyf | hyn
                          · exact Or.inl hyf
                          · refine Or.inr ⟨?_, ?_⟩
                            · rcases hct_or with rfl | rfl <;> omega
                            · intro hk_ne
                              rcases hkt_or with hke | rfl
                              · have hok : y.toNat < keep_tail'.toNat := by
                                  rcases hy_ok with rfl | h2
                                  · exact absurd rfl hy_not_ff
                                  · rw [hke]; exact h2.2 (by rw [← hke]; exact hk_ne)
                                omega
                              · exact hyn)
                        (fun _ hJbr => by
                          m6_to_group
                          refine wp_join_group (ts := [])
                            (fun () mThen => mThen = mIn)
                            (fun _ () mThen hmThen => by
                              subst mThen
                              m6_to_group
                              refine wp_join_group (ts := [i32])
                                (fun (pv, ()) mpv => mpv = mIn)
                                (fun _ (pv, ()) mpv hmpv => by
                                  subst mpv
                                  change wp _ _ _ _ _
                                  c0_hsteps_nogrp; try rw [hpn_c0]; try rw [hpn_c0']
                                  open scoped M6PhtMem in m6_steps
                                  let scrY := scrI.set (k6PhtNext + cls_tail.toNat) y
                                  exact hJbr (keep_tail, y, csz + 1#32, ()) _
                                    ⟨hy_lt, hkt_ok, Or.inr rfl, Or.inl rfl, scrY, _,
                                     List.length_set.trans hslI, List.length_set.trans hmcI,
                                     fun j hj hdom => by
                                       rw [List.getElem?_set_ne (by
                                         unfold k6PhtNext
                                         unfold k6PhtHead K6Layout.phtMerged at hdom; omega)]
                                       exact hpreI j hj hdom,
                                     m6_phtOk_set_next hct_lt hct_bd (Or.inr hy_clt) hphtI,
                                     m6_partOk_set_next hct_lt hct_bd (Or.inr hy_clt) hpartI,
                                     by dsimp only [scrY]; assumption⟩)
                                (fun _ hJpv => by
                                  m6_split <;> (m6_steps; exact hJpv _ mIn rfl)))
                            (fun _ hJthen => by
                              m6_split
                              · m6_steps; exact hJthen () mIn rfl
                              m6_split
                              · m6_steps; exact hJthen () mIn rfl
                              m6_to_group
                              refine wp_join_group (ts := [])
                                (fun () mK => ∃ scrK, scrK.length = c.scratch_cap ∧
                                  (∀ j < c.scratch_cap, j < k6PhtHead ∨ L.phtMerged ≤ j →
                                    scrK[j]? = s.scratch.scratch_buf[j]?) ∧
                                  M6PhtOk nv.toNat scrK ∧
                                  M6PartitionOk nv.toNat nclsL.toNat scrK sstkL ∧
                                  (FullMem c { s with
                                    core := { s.core with min_clr := mclrI }
                                    scratch := { s.scratch with scratch_buf := scrK,
                                                                shrink_stk := sstkL } } ⋆ R) mK)
                                (fun _ () mK ⟨scrK, hslK, hpreK, hphtK, hpartK, hmK⟩ => by
                                  m6_steps
                                  exact hJbr (y, cls_tail, csz, ()) mK
                                    ⟨hct_lt, Or.inr hy_lt, Or.inl rfl, Or.inr rfl, scrK, mclrI,
                                     hslK, hmcI, hpreK, hphtK, hpartK, hmK⟩)
                                (fun _ hJkeep => by
                                  m6_split
                                  · m6_steps
                                    let scrY := scrI.set (k6PhtHead + b.toNat) y
                                    exact hJkeep () _ ⟨scrY, List.length_set.trans hslI,
                                      fun j hj hdom => by
                                        rw [List.getElem?_set_ne ?_]
                                        · exact hpreI j hj hdom
                                        · unfold k6PhtHead
                                          unfold k6PhtHead K6Layout.phtMerged at hdom
                                          unfold k6PhtSz at hb_lt
                                          rcases hdom with h1 | h2
                                          · exact Nat.ne_of_gt
                                              (Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _))
                                          · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le
                                              (Nat.add_lt_add_left hb_lt 256)
                                              (Nat.le_trans (by
                                                have := hmL.1; omega) h2)),
                                      m6_phtOk_set_head hb_lt
                                        (by rw [hslI, ← hslL, ← hbh_eq]; exact hbh_bd)
                                        (Or.inr hy_lt) hphtI,
                                      m6_partOk_set_head hb_lt hpartI,
                                      by dsimp only [scrY]; rw [← hbh_eq]; assumption⟩
                                  · have hkt_lt : keep_tail.toNat < nv.toNat := by
                                      rcases hkt_ok with hff | hlt
                                      · exfalso; exact hc hff
                                      · exact hlt
                                    have hkt_mv : keep_tail.toNat < L.maxV := by omega
                                    have hkt_bd : k6PhtNext + keep_tail.toNat < scrI.length := by
                                      rw [hslI]; unfold k6PhtNext at ⊢
                                      unfold K6Layout.phtMerged at hpm_end; omega
                                    have hy_klt : y.toNat < keep_tail.toNat := by
                                      rcases hy_ok with rfl | h2
                                      · exact absurd rfl hy_not_ff
                                      · exact h2.2 hc
                                    change wp _ _ _ _ _
                                    c0_hsteps_nogrp; try rw [hpn_c0]; try rw [hpn_c0']
                                    open scoped M6PhtMem in m6_steps
                                    let scrY := scrI.set (k6PhtNext + keep_tail.toNat) y
                                    exact hJkeep () _ ⟨scrY, List.length_set.trans hslI,
                                      fun j hj hdom => by
                                        rw [List.getElem?_set_ne (by
                                          unfold k6PhtNext
                                          unfold k6PhtHead K6Layout.phtMerged at hdom; omega)]
                                        exact hpreI j hj hdom,
                                      m6_phtOk_set_next hkt_lt hkt_bd (Or.inr hy_klt) hphtI,
                                      m6_partOk_set_next hkt_lt hkt_bd (Or.inr hy_klt) hpartI,
                                      by dsimp only [scrY]; assumption⟩))))))))

/-! ## 5. `full_m6_refine_partition_wp` (`26/39`) -/

private def mkRefSt (s : FullState) (scr wso : List (BitVec 32)) : FullState :=
  { s with scratch := { s.scratch with scratch_buf := scr, wsort := wso } }

private theorem mkRefSt_self (s : FullState) :
    mkRefSt s s.scratch.scratch_buf s.scratch.wsort = s := by
  cases s with | mk c sc => cases sc; rfl

private def M6RefListOk (nv h t c : BitVec 32) : Prop :=
  t = 0xFFFFFFFF#32 ∧ c = 0#32 ∨ t.toNat < nv.toNat ∧ h.toNat < nv.toNat

private theorem m6_refList_nil {nv : BitVec 32} :
    M6RefListOk nv 0xFFFFFFFF#32 0xFFFFFFFF#32 0#32 := Or.inl ⟨rfl, rfl⟩

private theorem m6_refList_cons {nv h x c : BitVec 32}
    (hx : x.toNat < nv.toNat) (hh : h.toNat < nv.toNat) : M6RefListOk nv h x c :=
  Or.inr ⟨hx, hh⟩

private theorem m6_refList_head_of_pos {nv h t c : BitVec 32}
    (hr : M6RefListOk nv h t c) (h2 : 2 ≤ c.toNat) : h.toNat < nv.toNat := by
  rcases hr with ⟨_, rfl⟩ | ⟨_, hlt⟩
  · exfalso; exact Nat.not_le_of_gt (by decide : (0#32 : BitVec 32).toNat < 2) h2
  · exact hlt

private theorem m6_refList_of_lt {nv h t c : BitVec 32}
    (hr : M6RefListOk nv h t c) (hlt : t.toNat < nv.toNat) (hnv : nv.toNat < 2 ^ 31) :
    t.toNat < nv.toNat ∧ h.toNat < nv.toNat := by
  rcases hr with ⟨rfl, _⟩ | hpair
  · exfalso; exact Nat.not_lt_of_ge (by decide : 2 ^ 31 ≤ (0xFFFFFFFF#32 : BitVec 32).toNat)
      (Nat.lt_trans hlt hnv)
  · exact hpair

private theorem m6_refList_of_ne {nv h t c : BitVec 32}
    (hr : M6RefListOk nv h t c) (hne : t ≠ 0xFFFFFFFF#32) :
    t.toNat < nv.toNat ∧ h.toNat < nv.toNat := by
  rcases hr with ⟨rfl, _⟩ | hpair
  · exact absurd rfl hne
  · exact hpair

private def M6RefNodeOk (nv x pt nt : BitVec 32) : Prop :=
  x = 0xFFFFFFFF#32 ∨ (x.toNat < nv.toNat ∧
    (pt ≠ 0xFFFFFFFF#32 → x.toNat < pt.toNat) ∧
    (nt ≠ 0xFFFFFFFF#32 → x.toNat < nt.toNat))

private theorem m6_refNode_init {nv x : BitVec 32} (hx : x.toNat < nv.toNat) :
    M6RefNodeOk nv x 0xFFFFFFFF#32 0xFFFFFFFF#32 :=
  Or.inr ⟨hx, fun h => absurd rfl h, fun h => absurd rfl h⟩

private theorem m6_refNode_of_lt {nv x pt nt : BitVec 32}
    (hn : M6RefNodeOk nv x pt nt) (hx31 : x.toNat < 2 ^ 31) :
    (pt ≠ 0xFFFFFFFF#32 → x.toNat < pt.toNat) ∧
    (nt ≠ 0xFFFFFFFF#32 → x.toNat < nt.toNat) := by
  rcases hn with rfl | h2
  · exfalso; exact Nat.ne_of_lt (Nat.lt_trans hx31 (by decide : 2 ^ 31 < 4294967295)) rfl
  · exact h2.2

private theorem m6_refNode_plt {nv x pt nt : BitVec 32}
    (hn : M6RefNodeOk nv x pt nt) (hx31 : x.toNat < 2 ^ 31) (hpt : pt ≠ 0xFFFFFFFF#32) :
    x.toNat < pt.toNat :=
  (m6_refNode_of_lt hn hx31).1 hpt

private theorem m6_refNode_nlt {nv x pt nt : BitVec 32}
    (hn : M6RefNodeOk nv x pt nt) (hx31 : x.toNat < 2 ^ 31) (hnt : nt ≠ 0xFFFFFFFF#32) :
    x.toNat < nt.toNat :=
  (m6_refNode_of_lt hn hx31).2 hnt

private theorem m6_refNode_step {nv nx x pt nt pt' nt' : BitVec 32}
    (hnx : nx = 0xFFFFFFFF#32 ∨ nx.toNat < x.toNat) (hx_lt : x.toNat < nv.toNat)
    (hpt_eq : pt' = pt ∨ pt' = x) (hnt_eq : nt' = nt ∨ nt' = x)
    (hplt : pt ≠ 0xFFFFFFFF#32 → x.toNat < pt.toNat)
    (hnlt : nt ≠ 0xFFFFFFFF#32 → x.toNat < nt.toNat) :
    M6RefNodeOk nv nx pt' nt' := by
  rcases hnx with rfl | hxn
  · exact Or.inl rfl
  · refine Or.inr ⟨Nat.lt_trans hxn hx_lt, fun h => ?_, fun h => ?_⟩
    · rcases hpt_eq with rfl | rfl
      · exact Nat.lt_trans hxn (hplt h)
      · exact hxn
    · rcases hnt_eq with rfl | rfl
      · exact Nat.lt_trans hxn (hnlt h)
      · exact hxn

theorem full_m6_refine_partition_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec) :
    ∀ args m Q X, m6RefinePartitionSpec args m Q X →
      Func.wp Γ full_m6_refine_partition_body args m Q X := by
  rintro ⟨h, nv, ncls, ⟨⟩⟩ m Q X
    ⟨c, s, L, R, rfl, hlen, hL_len, hL_mv, hnv_L, hnv_cv_bd, hncls_cv_bd, hws_lt, hpart0, hm, hQ⟩
  have hcv_le := hlen.core_ok.cur_vars_le
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hscr_len := hlen.scratch_ok.scratch_buf_len
  have hws_len := hlen.scratch_ok.work_stk1_len
  have hval_len := hlen.core_ok.vals_len
  have hss_len := hlen.scratch_ok.shrink_stk_len
  have hmc_len := hlen.core_ok.min_clr_len_arr
  have hwso_len := hlen.scratch_ok.wsort_len
  have hmL := L.hmaxV; have haL := L.hacap
  have hmv64_lt : k6MaxV c.scratch_cap < 2 ^ 32 := by rw [← hL_mv]; omega
  have hmv_eq : BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) = L.mv32 := by
    apply BitVec.eq_of_toNat_eq
    simp only [k6_mv32_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [← hL_mv]; omega
  have hkptr_c0 : c.pScratchBuf + BitVec.setWidth 64
      ((1280 : BitVec 32) + (BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) <<<
        (1 : Nat))) * 4 = L.kPtr c.pScratchBuf := by
    rw [hmv_eq]; exact k6_ptr_base_k6Base L c.pScratchBuf
  have hvals_c0 : L.kPtr c.pScratchBuf + BitVec.setWidth 64
      ((32 : BitVec 32) + (10 : BitVec 32) * L.mv32) * 4 =
      L.kPtr c.pScratchBuf + BitVec.ofNat 64 (4 * L.oVals) :=
    k6_ptr_vals L (L.kPtr c.pScratchBuf)
  have hpm_c0 := m6_ptr_phtMerged L c.pScratchBuf
  have hpn_c0 : c.pScratchBuf + BitVec.setWidth 64 (1280 : BitVec 32) * 4 =
      c.pScratchBuf + BitVec.ofNat 64 (4 * k6PhtNext) := rfl
  have hpn_c0' : c.pScratchBuf + BitVec.ofNat 64 1280 * 4 =
      c.pScratchBuf + BitVec.ofNat 64 (4 * k6PhtNext) := rfl
  have hpm_end : L.phtMerged + L.maxV ≤ c.scratch_cap := by
    rw [← hL_len]; unfold K6Layout.scrLen K6Layout.k6Base K6Layout.k6Fixed K6Layout.phtMerged
    omega
  unfold Func.wp full_m6_refine_partition_body
  m6_steps
  refine m6_call_max_v hMaxV (c := c) rfl ?_
  m6_split
  · exfalso; have h0 := congrArg BitVec.toNat hc
    rw [hmv_eq, k6_mv32_toNat] at h0; simp at h0; omega
  m6_split
  · exfalso; rw [← hL_mv, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc; omega
  m6_to_group
  -- Loop 1: `(new_n, ci)` split each class into `ph`/`nh` lists recorded in `nheads` (`wsort`)
  refine wp_loop_inv (ts := [i32, i32])
    (fun (new_n, ci, ()) m1 => ci.toNat ≤ ncls.toNat ∧ new_n.toNat ≤ c.max_vars ∧
      ∃ scr1 wsort1, scr1.length = c.scratch_cap ∧ wsort1.length = 2 * c.max_vars ∧
        (∀ j < c.scratch_cap, j < k6PhtNext ∨ L.phtMerged ≤ j →
          scr1[j]? = s.scratch.scratch_buf[j]?) ∧
        (∀ i < nv.toNat,
          let nx := scr1[k6PhtNext + i]?.getD 0xFFFFFFFF#32
          nx = 0xFFFFFFFF#32 ∨ nx.toNat < i) ∧
        (∀ k < new_n.toNat, (wsort1[k]?.getD 0xFFFFFFFF#32).toNat < nv.toNat) ∧
        (FullMem c (mkRefSt s scr1 wsort1) ⋆ R) m1)
    (fun (_, ci, ()) _ => ncls.toNat - ci.toNat)
    (fun _ hJci => by
      m6_steps
      exact hJci (0#32, 0#32, ()) m ⟨Nat.zero_le _, Nat.zero_le _, s.scratch.scratch_buf,
        s.scratch.wsort, hscr_len, hwso_len, fun _ _ _ => rfl, hpart0.2.1,
        fun _ hk => by simp at hk, by rw [mkRefSt_self]; exact hm⟩)
    (fun _ (new_n, ci, ()) m1
        ⟨hci_le, hnn_le, scr1, wsort1, hsl1, hws1_len, hpre1, hnx1, hwso_ok, hm1⟩ hJci => by
      clear hm
      m6_split
      · have hci_lt : ci.toNat < ncls.toNat := hc
        have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := m6_bv32_add1 (by omega)
        have hci_ss : (ci.setWidth 64).toNat < s.scratch.shrink_stk.length := by
          rw [hss_len, bv_c0_zext32_64]; omega
        let x0 := s.scratch.shrink_stk[(ci.setWidth 64).toNat]'hci_ss
        have hx0_lt : x0.toNat < nv.toNat := by
          have := hpart0.2.2 ci.toNat hci_lt
          dsimp only [x0]; rw [List.getElem?_eq_getElem (by rw [hss_len]; omega),
            Option.getD_some] at this
          simpa only [bv_c0_zext32_64] using this
        m6_to_group
        -- Inner loop: `(x, ph, pt, pc, nh, nt, nc, g)`
        refine wp_loop_inv (ts := [i32, i32, i32, i32, i32, i32, i32, i32])
          (fun (x, ph, pt, pc, nh, nt, nc, g, ()) mi => g.toNat ≤ nv.toNat ∧
            M6RefListOk nv ph pt pc ∧ M6RefListOk nv nh nt nc ∧
            M6RefNodeOk nv x pt nt ∧
            ∃ scrI, scrI.length = c.scratch_cap ∧
              (∀ j < c.scratch_cap, j < k6PhtNext ∨ L.phtMerged ≤ j →
                scrI[j]? = s.scratch.scratch_buf[j]?) ∧
              (∀ i < nv.toNat,
                let nx := scrI[k6PhtNext + i]?.getD 0xFFFFFFFF#32
                nx = 0xFFFFFFFF#32 ∨ nx.toNat < i) ∧
              (FullMem c (mkRefSt s scrI wsort1) ⋆ R) mi)
          (fun (_, _, _, _, _, _, _, g, ()) _ => g.toNat)
          (fun _ hJx => by
            dsimp only [mkRefSt] at hm1
            m6_steps
            change (FullMem c (mkRefSt s scr1 wsort1) ⋆ R) m1 at hm1
            exact hJx (x0, 0xFFFFFFFF#32, 0xFFFFFFFF#32, 0#32,
                0xFFFFFFFF#32, 0xFFFFFFFF#32, 0#32, nv, ()) m1
              ⟨le_refl _, m6_refList_nil, m6_refList_nil, m6_refNode_init hx0_lt,
               scr1, hsl1, hpre1, hnx1, hm1⟩)
          (fun _ (x, ph, pt, pc, nh, nt, nc, g, ()) mi
              ⟨hg_le, hptph, hntnh, hx, scrI, hslI, hpreI, hnxI, hmi⟩ hJx => by
            try clear hm1; try clear hpre1; try clear hnx1; try clear hpart0
            try clear hx0_lt; try clear hci_ss
            m6_to_group
            refine wp_join_group (ts := [])
              (fun () mE => mE = mi)
              (fun _ () mE hmE => by
                subst hmE
                m6_to_group
                refine wp_join_group (ts := [])
                  (fun () mpt => ∃ scrT, scrT.length = c.scratch_cap ∧
                    (∀ j < c.scratch_cap, j < k6PhtNext ∨ L.phtMerged ≤ j →
                      scrT[j]? = s.scratch.scratch_buf[j]?) ∧
                    (∀ i < nv.toNat,
                      let nx := scrT[k6PhtNext + i]?.getD 0xFFFFFFFF#32
                      nx = 0xFFFFFFFF#32 ∨ nx.toNat < i) ∧
                    (FullMem c (mkRefSt s scrT wsort1) ⋆ R) mpt)
                  (fun _ () mpt ⟨scrT, hslT, hpreT, hnxT, hmT⟩ => by
                    m6_to_group
                    refine wp_join_group (ts := [])
                      (fun () mnt => ∃ scrN, scrN.length = c.scratch_cap ∧
                        (∀ j < c.scratch_cap, j < k6PhtNext ∨ L.phtMerged ≤ j →
                          scrN[j]? = s.scratch.scratch_buf[j]?) ∧
                        (∀ i < nv.toNat,
                          let nx := scrN[k6PhtNext + i]?.getD 0xFFFFFFFF#32
                          nx = 0xFFFFFFFF#32 ∨ nx.toNat < i) ∧
                        (FullMem c (mkRefSt s scrN wsort1) ⋆ R) mnt)
                      (fun _ () mnt ⟨scrN, hslN, hpreN, hnxN, hmN⟩ => by
                        m6_to_group
                        refine wp_join_group (ts := [i32])
                          (fun (new_nP, ()) mP => new_nP.toNat ≤ c.max_vars ∧
                            ∃ wsortP, wsortP.length = 2 * c.max_vars ∧
                              (∀ k < new_nP.toNat,
                                (wsortP[k]?.getD 0xFFFFFFFF#32).toNat < nv.toNat) ∧
                              (FullMem c (mkRefSt s scrN wsortP) ⋆ R) mP)
                          (fun _ (new_nP, ()) mP ⟨hnnP, wsortP, hwsoP_len, hwsoP_ok, hmP⟩ => by
                            m6_to_group
                            refine wp_join_group (ts := [i32])
                              (fun (new_nQ, ()) mQ => new_nQ.toNat ≤ c.max_vars ∧
                                ∃ wsortQ, wsortQ.length = 2 * c.max_vars ∧
                                  (∀ k < new_nQ.toNat,
                                    (wsortQ[k]?.getD 0xFFFFFFFF#32).toNat < nv.toNat) ∧
                                  (FullMem c (mkRefSt s scrN wsortQ) ⋆ R) mQ)
                              (fun _ (new_nQ, ()) mQ ⟨hnnQ, wsortQ, hwsoQ_len, hwsoQ_ok, hmQ⟩ => by
                                m6_steps
                                exact hJci (new_nQ, ci + 1#32, ()) mQ
                                  (by dsimp only; rw [hci1]
                                      exact Nat.sub_lt_sub_left hci_lt (by omega))
                                  ⟨by omega, hnnQ, scrN, wsortQ, hslN, hwsoQ_len, hpreN, hnxN,
                                   hwsoQ_ok, hmQ⟩)
                              (fun _ hJnc => by
                                m6_split
                                · m6_split
                                  · have hnh_lt : nh.toNat < nv.toNat :=
                                      m6_refList_head_of_pos hntnh ‹_›
                                    have hn_lt : new_nP.toNat < c.max_vars := by omega
                                    have hn1 : (new_nP + 1#32).toNat = new_nP.toNat + 1 :=
                                      m6_bv32_add1 (by omega)
                                    dsimp only [mkRefSt] at hmP
                                    m6_steps
                                    refine hJnc (new_nP + 1#32, ()) _
                                      ⟨by omega, _, List.length_set.trans hwsoP_len,
                                       fun k hk => ?_, by dsimp only [mkRefSt]; assumption⟩
                                    rw [hn1] at hk
                                    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
                                    · rw [List.getElem?_set_ne (by rw [bv_c0_zext32_64]; omega)]
                                      exact hwsoP_ok k hlt
                                    · rw [bv_c0_zext32_64, List.getElem?_set_self (by omega),
                                        Option.getD_some]
                                      exact hnh_lt
                                  · m6_steps
                                    exact hJnc (new_nP, ()) mP
                                      ⟨hnnP, wsortP, hwsoP_len, hwsoP_ok, hmP⟩
                                · m6_steps
                                  exact hJnc (new_nP, ()) mP
                                    ⟨hnnP, wsortP, hwsoP_len, hwsoP_ok, hmP⟩))
                          (fun _ hJpc => by
                            m6_split
                            · m6_split
                              · have hph_lt : ph.toNat < nv.toNat :=
                                  m6_refList_head_of_pos hptph ‹_›
                                have hn_lt : new_n.toNat < c.max_vars := by omega
                                have hn1 : (new_n + 1#32).toNat = new_n.toNat + 1 :=
                                  m6_bv32_add1 (by omega)
                                dsimp only [mkRefSt] at hmN
                                m6_steps
                                refine hJpc (new_n + 1#32, ()) _
                                  ⟨by omega, _, List.length_set.trans hws1_len, fun k hk => ?_,
                                   by dsimp only [mkRefSt]; assumption⟩
                                rw [hn1] at hk
                                rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
                                · rw [List.getElem?_set_ne (by rw [bv_c0_zext32_64]; omega)]
                                  exact hwso_ok k hlt
                                · rw [bv_c0_zext32_64, List.getElem?_set_self (by omega),
                                    Option.getD_some]
                                  exact hph_lt
                              · m6_steps
                                exact hJpc (new_n, ()) mnt ⟨hnn_le, wsort1, hws1_len, hwso_ok, hmN⟩
                            · m6_steps
                              exact hJpc (new_n, ()) mnt ⟨hnn_le, wsort1, hws1_len, hwso_ok, hmN⟩))
                      (fun _ hJnt => by
                        m6_split; rotate_left
                        · m6_steps; exact hJnt () mpt ⟨scrT, hslT, hpreT, hnxT, hmT⟩
                        have hnt_lt : nt.toNat < nv.toNat :=
                          (m6_refList_of_lt hntnh hc
                            (Nat.lt_of_le_of_lt hnv_cv_bd (Nat.lt_trans hmx (by decide)))).1
                        have hnt_mv : nt.toNat < L.maxV := by omega
                        have hnt_bd : k6PhtNext + nt.toNat < scrT.length := by
                          rw [hslT]; unfold k6PhtNext at ⊢; unfold K6Layout.phtMerged at hpm_end
                          omega
                        change wp _ _ _ _ _
                        dsimp only [mkRefSt] at hmT
                        c0_hsteps_nogrp; try rw [hpn_c0]; try rw [hpn_c0']
                        open scoped M6PhtMem in m6_steps
                        exact hJnt () _ ⟨_, List.length_set.trans hslT, fun j hj hdom => by
                          rw [List.getElem?_set_ne (by
                            unfold k6PhtNext; unfold k6PhtNext K6Layout.phtMerged at hdom; omega)]
                          exact hpreT j hj hdom,
                          m6_phtNext_set_next hnt_lt hnt_bd (Or.inl rfl) hnxT,
                          by dsimp only [mkRefSt]; assumption⟩))
                  (fun _ hJpt => by
                    m6_split; rotate_left
                    · m6_steps; exact hJpt () mE ⟨scrI, hslI, hpreI, hnxI, hmi⟩
                    have hpt_lt : pt.toNat < nv.toNat :=
                      (m6_refList_of_lt hptph hc
                        (Nat.lt_of_le_of_lt hnv_cv_bd (Nat.lt_trans hmx (by decide)))).1
                    have hpt_mv : pt.toNat < L.maxV := by omega
                    have hpt_bd : k6PhtNext + pt.toNat < scrI.length := by
                      rw [hslI]; unfold k6PhtNext at ⊢; unfold K6Layout.phtMerged at hpm_end; omega
                    change wp _ _ _ _ _
                    dsimp only [mkRefSt] at hmi
                    c0_hsteps_nogrp; try rw [hpn_c0]; try rw [hpn_c0']
                    open scoped M6PhtMem in m6_steps
                    exact hJpt () _ ⟨_, List.length_set.trans hslI, fun j hj hdom => by
                      rw [List.getElem?_set_ne (by
                        unfold k6PhtNext; unfold k6PhtNext K6Layout.phtMerged at hdom; omega)]
                      exact hpreI j hj hdom,
                      m6_phtNext_set_next hpt_lt hpt_bd (Or.inl rfl) hnxI,
                      by dsimp only [mkRefSt]; assumption⟩))
              (fun _ hJinn => by
                m6_split; rotate_left
                · m6_steps; exact hJinn () mi rfl
                m6_split; rotate_left
                · m6_steps; exact hJinn () mi rfl
                have hx_lt : x.toNat < nv.toNat := ‹_›
                have hx_mv : x.toNat < L.maxV := Nat.lt_of_lt_of_le hx_lt hnv_L
                have hx_cv : x.toNat < c.max_vars := Nat.lt_of_lt_of_le hx_lt hnv_cv_bd
                have hx_u31 : x.toNat < 2 ^ 31 :=
                  Nat.lt_trans hx_cv (Nat.lt_trans hmx (by decide))
                have hg_lt : 0 < g.toNat := hc
                have hg1 : (g - 1#32).toNat = g.toNat - 1 := bv32_sub1_of_pos hg_lt
                have hx_ws_nat : x.toNat < s.scratch.work_stk1.length := by
                  rw [hws_len]
                  exact Nat.lt_of_lt_of_le hx_cv (Nat.le_mul_of_pos_left _ (by decide))
                have hx_ws : (x.setWidth 64).toNat < s.scratch.work_stk1.length := by
                  rw [bv_c0_zext32_64]; exact hx_ws_nat
                have hgv_val : (BitVec.setWidth 64
                    (s.scratch.work_stk1[(x.setWidth 64).toNat]'hx_ws <<< (1 : Nat))).toNat <
                    s.core.vals.length := by
                  have hg := hws_lt x.toNat hx_lt
                  rw [List.getElem?_eq_getElem hx_ws_nat, Option.getD_some] at hg
                  rw [hval_len]
                  refine m6_bv32_shl1_zext_lt (Nat.lt_of_lt_of_le ?_ hcv_le)
                    (Nat.lt_trans hmx (by decide))
                  have hidx : (x.setWidth 64).toNat = x.toNat := bv_c0_zext32_64 x
                  simpa only [hidx] using hg
                have hx_mc : (x.setWidth 64).toNat < s.core.min_clr.length := by
                  rw [hmc_len, bv_c0_zext32_64]; exact hx_cv
                have hx_kv : ((x <<< (1 : Nat)) |||
                    (s.core.min_clr[(x.setWidth 64).toNat]'hx_mc &&& 1#32)).toNat <
                    2 * L.maxV := by
                  rw [m6_bv32_shl1_or_and1 _ _ hx_u31]
                  exact Nat.lt_of_lt_of_le
                    (Nat.add_lt_add_left (Nat.mod_lt _ (by decide)) (2 * x.toNat))
                    (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left 2 hx_mv)
                have hx_nx_bd : k6PhtNext + x.toNat < scrI.length := by
                  rw [hslI]
                  have h1 : k6PhtNext + x.toNat < L.phtMerged := by
                    unfold k6PhtNext K6Layout.phtMerged; exact Nat.add_lt_add_left hx_mv 1280
                  exact Nat.lt_of_lt_of_le h1 (Nat.le_trans (Nat.le_add_right _ _) hpm_end)
                change wp _ _ _ _ _
                dsimp only [mkRefSt] at hmi
                c0_hsteps_nogrp
                try rw [hkptr_c0]; try rw [hmv_eq]; try rw [hvals_c0]
                try rw [hpm_c0]; try rw [hpn_c0]; try rw [hpn_c0']
                open scoped M6PhtMem FullK6DynMem in m6_to_group
                change (FullMem c (mkRefSt s scrI wsort1) ⋆ R) mi at hmi
                refine wp_join_group (ts := [i32, i32, i32, i32, i32, i32])
                  (fun (ph', pt', pc', nh', nt', nc', ()) my =>
                    M6RefListOk nv ph' pt' pc' ∧ M6RefListOk nv nh' nt' nc' ∧
                    (pt' = pt ∨ pt' = x) ∧ (nt' = nt ∨ nt' = x) ∧
                    ∃ scrY, scrY.length = c.scratch_cap ∧
                      (∀ j < c.scratch_cap, j < k6PhtNext ∨ L.phtMerged ≤ j →
                        scrY[j]? = s.scratch.scratch_buf[j]?) ∧
                      (∀ i < nv.toNat,
                        let nx' := scrY[k6PhtNext + i]?.getD 0xFFFFFFFF#32
                        nx' = 0xFFFFFFFF#32 ∨ nx'.toNat < i) ∧
                      (FullMem c (mkRefSt s scrY wsort1) ⋆ R) my)
                  (fun _ (ph', pt', pc', nh', nt', nc', ()) my
                      ⟨hptph', hntnh', hpt_eq, hnt_eq, scrY, hslY, hpreY, hnxY, hmy⟩ => by
                    try clear hmi hm
                    let nx := scrI[k6PhtNext + x.toNat]'hx_nx_bd
                    have hnx_lt : nx = 0xFFFFFFFF#32 ∨ nx.toNat < x.toNat := by
                      have hp2 := hnxI x.toNat hx_lt
                      dsimp only [nx]
                      rwa [List.getElem?_eq_getElem hx_nx_bd, Option.getD_some] at hp2
                    m6_steps
                    exact hJx (nx, ph', pt', pc', nh', nt', nc', g - 1#32, ()) my
                      (by dsimp only; rw [hg1]; exact Nat.sub_lt hg_lt (by omega))
                      ⟨by omega, hptph', hntnh',
                       m6_refNode_step hnx_lt hx_lt hpt_eq hnt_eq
                         (m6_refNode_plt hx hx_u31) (m6_refNode_nlt hx hx_u31),
                       scrY, hslY, hpreY, hnxY, hmy⟩)
                  (fun _ hJkv => by
                    try clear hg_lt
                    try clear hg1
                    try clear hg_le
                    try clear hJx
                    try clear hJci
                    try clear hwso_ok
                    try clear hnn_le
                    try clear hci_lt
                    try clear hci1
                    try clear hws1_len
                    try clear scr1
                    try clear hsl1
                    dsimp only [mkRefSt] at hmi
                    change wp _ _ _ _ _
                    c0_hsteps_nogrp; try rw [hpm_c0]
                    open scoped M6PhtMem in m6_split; rotate_left
                    · m6_steps
                      exact hJkv (ph, pt, pc, nh, nt, nc, ()) mi
                        ⟨hptph, hntnh, Or.inl rfl, Or.inl rfl, scrI, hslI, hpreI, hnxI,
                         by dsimp only [mkRefSt]; exact hmi⟩
                    change wp _ _ _ _ _
                    let sI : FullState := mkRefSt s scrI wsort1
                    have hslI_sI : sI.scratch.scratch_buf.length = c.scratch_cap := hslI
                    have hx_wsI : (x.setWidth 64).toNat < sI.scratch.work_stk1.length := hx_ws
                    have hgv_valI : (BitVec.setWidth 64
                        (sI.scratch.work_stk1[(x.setWidth 64).toNat]'hx_wsI <<< (1 : Nat))).toNat <
                        sI.core.vals.length := hgv_val
                    have hx_mcI : (x.setWidth 64).toNat < sI.core.min_clr.length := hx_mc
                    have hx_kvI : ((x <<< (1 : Nat)) |||
                        (sI.core.min_clr[(x.setWidth 64).toNat]'hx_mcI &&& 1#32)).toNat <
                        2 * L.maxV := hx_kv
                    have hmiI : (FullMem c sI ⋆ R) mi := hmi
                    open scoped M6PhtMem FullK6DynMem in c0_hsteps_nogrp
                    open scoped M6PhtMem FullK6DynMem in m6_split; rotate_left
                    · m6_steps
                      exact hJkv (ph, pt, pc, nh, nt, nc, ()) mi
                        ⟨hptph, hntnh, Or.inl rfl, Or.inl rfl, scrI, hslI, hpreI, hnxI,
                         by dsimp only [mkRefSt]; exact hmi⟩
                    change wp _ _ _ _ _
                    c0_hsteps_nogrp
                    try rw [hkptr_c0]; try rw [hmv_eq]; try rw [hvals_c0]
                    try rw [hpm_c0]; try rw [hpn_c0]
                    open scoped M6PhtMem FullK6DynMem in m6_to_group
                    try clear hmiI; try clear hx_kvI; try clear hx_mcI
                    try clear hgv_valI; try clear hx_wsI; try clear hslI_sI
                    refine wp_join_group (ts := [i32, i32, i32, i32, i32, i32])
                      (fun (ph', pt', pc', nh', nt', nc', ()) my =>
                        M6RefListOk nv ph' pt' pc' ∧ M6RefListOk nv nh' nt' nc' ∧
                        (pt' = pt ∨ pt' = x) ∧ (nt' = nt ∨ nt' = x) ∧
                        ∃ scrY, scrY.length = c.scratch_cap ∧
                          (∀ j < c.scratch_cap, j < k6PhtNext ∨ L.phtMerged ≤ j →
                            scrY[j]? = s.scratch.scratch_buf[j]?) ∧
                          (∀ i < nv.toNat,
                            let nx' := scrY[k6PhtNext + i]?.getD 0xFFFFFFFF#32
                            nx' = 0xFFFFFFFF#32 ∨ nx'.toNat < i) ∧
                          (FullMem c (mkRefSt s scrY wsort1) ⋆ R) my)
                      (fun _ (ph', pt', pc', nh', nt', nc', ()) my hmy => by
                        m6_steps; exact hJkv (ph', pt', pc', nh', nt', nc', ()) my hmy)
                      (fun _ hJkv' => by
                        m6_split
                        · -- `kv == 1u`: append `x` to `ph`/`pt`
                          m6_to_group
                          refine wp_join_group (ts := [i32])
                            (fun (ph', ()) mP => ph'.toNat < nv.toNat ∧
                              ∃ scrY, scrY.length = c.scratch_cap ∧
                                (∀ j < c.scratch_cap, j < k6PhtNext ∨ L.phtMerged ≤ j →
                                  scrY[j]? = s.scratch.scratch_buf[j]?) ∧
                                (∀ i < nv.toNat,
                                  let nx' := scrY[k6PhtNext + i]?.getD 0xFFFFFFFF#32
                                  nx' = 0xFFFFFFFF#32 ∨ nx'.toNat < i) ∧
                                (FullMem c (mkRefSt s scrY wsort1) ⋆ R) mP)
                                (fun _ (ph', ()) mP ⟨hph', scrY, hslY, hpreY, hnxY, hmP⟩ => by
                                  try clear hmi
                                  m6_steps
                                  exact hJkv' (ph', x, pc + 1#32, nh, nt, nc, ()) mP
                                    ⟨m6_refList_cons hx_lt hph', hntnh, Or.inr rfl, Or.inl rfl,
                                     scrY, hslY, hpreY, hnxY, hmP⟩)
                            (fun _ hJp => by
                              m6_split
                              · m6_steps
                                exact hJp (x, ()) mi ⟨hx_lt, scrI, hslI, hpreI, hnxI,
                                  by dsimp only [mkRefSt]; exact hmi⟩
                              · obtain ⟨hpt_lt, hph_lt⟩ := m6_refList_of_ne hptph hc
                                have hpt_mv : pt.toNat < L.maxV := Nat.lt_of_lt_of_le hpt_lt hnv_L
                                have hpt_bd : k6PhtNext + pt.toNat < scrI.length := by
                                  rw [hslI]
                                  have h1 : k6PhtNext + pt.toNat < L.phtMerged := by
                                    unfold k6PhtNext K6Layout.phtMerged
                                    exact Nat.add_lt_add_left hpt_mv 1280
                                  exact Nat.lt_of_lt_of_le h1
                                    (Nat.le_trans (Nat.le_add_right _ _) hpm_end)
                                have hx_plt : x.toNat < pt.toNat := m6_refNode_plt hx hx_u31 hc
                                try clear hx
                                change wp _ _ _ _ _
                                c0_hsteps_nogrp; try rw [hpn_c0]
                                open scoped M6PhtMem in m6_steps
                                exact hJp (ph, ()) _ ⟨hph_lt, _, List.length_set.trans hslI,
                                  fun j hj hdom => by
                                    rw [List.getElem?_set_ne (by
                                      unfold k6PhtNext
                                      unfold k6PhtNext K6Layout.phtMerged at hdom; omega)]
                                    exact hpreI j hj hdom,
                                  m6_phtNext_set_next hpt_lt hpt_bd (Or.inr hx_plt) hnxI,
                                  by dsimp only [mkRefSt]; assumption⟩)
                        · m6_to_group
                          refine wp_join_group (ts := [i32, i32, i32])
                            (fun (nh', nt', nc', ()) mN =>
                              M6RefListOk nv nh' nt' nc' ∧
                              (nt' = nt ∨ nt' = x) ∧
                              ∃ scrY, scrY.length = c.scratch_cap ∧
                                (∀ j < c.scratch_cap, j < k6PhtNext ∨ L.phtMerged ≤ j →
                                  scrY[j]? = s.scratch.scratch_buf[j]?) ∧
                                (∀ i < nv.toNat,
                                  let nx' := scrY[k6PhtNext + i]?.getD 0xFFFFFFFF#32
                                  nx' = 0xFFFFFFFF#32 ∨ nx'.toNat < i) ∧
                                (FullMem c (mkRefSt s scrY wsort1) ⋆ R) mN)
                            (fun _ (nh', nt', nc', ()) mN
                                ⟨hntnh', hnt_eq, scrY, hslY, hpreY, hnxY, hmN⟩ => by
                              try clear hmi
                              m6_steps
                              exact hJkv' (ph, pt, pc, nh', nt', nc', ()) mN
                                ⟨hptph, hntnh', Or.inl rfl, hnt_eq,
                                 scrY, hslY, hpreY, hnxY, hmN⟩)
                            (fun _ hJnt3 => by
                              m6_split
                              · -- `kv == 2u`: append `x` to `nh`/`nt`
                                m6_to_group
                                refine wp_join_group (ts := [i32])
                                  (fun (nh', ()) mN => nh'.toNat < nv.toNat ∧
                                    ∃ scrY, scrY.length = c.scratch_cap ∧
                                      (∀ j < c.scratch_cap, j < k6PhtNext ∨ L.phtMerged ≤ j →
                                        scrY[j]? = s.scratch.scratch_buf[j]?) ∧
                                      (∀ i < nv.toNat,
                                        let nx' := scrY[k6PhtNext + i]?.getD 0xFFFFFFFF#32
                                        nx' = 0xFFFFFFFF#32 ∨ nx'.toNat < i) ∧
                                      (FullMem c (mkRefSt s scrY wsort1) ⋆ R) mN)
                                  (fun _ (nh', ()) mN ⟨hnh', scrY, hslY, hpreY, hnxY, hmN⟩ => by
                                    try clear hmi
                                    m6_steps
                                    exact hJnt3 (nh', x, nc + 1#32, ()) mN
                                      ⟨m6_refList_cons hx_lt hnh', Or.inr rfl,
                                       scrY, hslY, hpreY, hnxY, hmN⟩)
                                  (fun _ hJn => by
                                    m6_split
                                    · m6_steps
                                      exact hJn (x, ()) mi ⟨hx_lt, scrI, hslI, hpreI, hnxI,
                                        by dsimp only [mkRefSt]; exact hmi⟩
                                    · obtain ⟨hnt_lt, hnh_lt⟩ := m6_refList_of_ne hntnh hc
                                      have hnt_mv : nt.toNat < L.maxV :=
                                        Nat.lt_of_lt_of_le hnt_lt hnv_L
                                      have hnt_bd : k6PhtNext + nt.toNat < scrI.length := by
                                        rw [hslI]
                                        have h1 : k6PhtNext + nt.toNat < L.phtMerged := by
                                          unfold k6PhtNext K6Layout.phtMerged
                                          exact Nat.add_lt_add_left hnt_mv 1280
                                        exact Nat.lt_of_lt_of_le h1
                                          (Nat.le_trans (Nat.le_add_right _ _) hpm_end)
                                      have hx_nlt : x.toNat < nt.toNat :=
                                        m6_refNode_nlt hx hx_u31 hc
                                      try clear hx
                                      change wp _ _ _ _ _
                                      c0_hsteps_nogrp; try rw [hpn_c0]
                                      open scoped M6PhtMem in m6_steps
                                      exact hJn (nh, ()) _ ⟨hnh_lt, _, List.length_set.trans hslI,
                                        fun j hj hdom => by
                                          rw [List.getElem?_set_ne (by
                                            unfold k6PhtNext
                                            unfold k6PhtNext K6Layout.phtMerged at hdom; omega)]
                                          exact hpreI j hj hdom,
                                        m6_phtNext_set_next hnt_lt hnt_bd (Or.inr hx_nlt) hnxI,
                                        by dsimp only [mkRefSt]; assumption⟩)
                              · m6_steps
                                exact hJnt3 (nh, nt, nc, ()) mi
                                  ⟨hntnh, Or.inl rfl, scrI, hslI, hpreI, hnxI,
                                   by dsimp only [mkRefSt]; exact hmi⟩)))))
      · -- Loop 2: copy `heads[ci] = nheads[ci]` for `ci < new_n`
        m6_to_group
        refine wp_loop_inv (ts := [i32])
          (fun (j, ()) m2 => j.toNat ≤ new_n.toNat ∧ ∃ sstk2 : List (BitVec 32),
            sstk2.length = c.max_vars ∧
            (∀ k < j.toNat, (sstk2[k]?.getD 0xFFFFFFFF#32).toNat < nv.toNat) ∧
            (FullMem c { s with scratch :=
              { s.scratch with scratch_buf := scr1, shrink_stk := sstk2, wsort := wsort1 } } ⋆ R)
              m2)
          (fun (j, ()) _ => new_n.toNat - j.toNat)
          (fun _ hJj => by
            dsimp only [mkRefSt] at hm1
            m6_steps
            exact hJj (0#32, ()) m1 ⟨Nat.zero_le _, s.scratch.shrink_stk, hss_len,
              fun _ hk => by simp at hk, hm1⟩)
          (fun _ (j, ()) m2 ⟨hj_le, sstk2, hss2_len, hok2, hm2⟩ hJj => by
            m6_split
            · have hj_lt : j.toNat < new_n.toNat := hc
              have hj1 : (j + 1#32).toNat = j.toNat + 1 := m6_bv32_add1 (by omega)
              have hj_ws : (j.setWidth 64).toNat < wsort1.length := by
                rw [hws1_len, bv_c0_zext32_64]; omega
              have hj_ss : (j.setWidth 64).toNat < sstk2.length := by
                rw [hss2_len, bv_c0_zext32_64]; omega
              m6_steps
              refine hJj (j + 1#32, ()) _
                (by dsimp only; rw [hj1]; exact Nat.sub_lt_sub_left hj_lt (by omega))
                ⟨by omega, _, List.length_set.trans hss2_len, fun k hk => ?_, by assumption⟩
              rw [hj1] at hk
              rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
              · rw [List.getElem?_set_ne (by rw [bv_c0_zext32_64]; omega)]; exact hok2 k hlt
              · dsimp only
                simp only [bv_c0_zext32_64]
                rw [List.getElem?_set_self (by rw [hss2_len]; omega), Option.getD_some]
                have h1 := hwso_ok j.toNat hj_lt
                rw [List.getElem?_eq_getElem (by rw [hws1_len]; omega), Option.getD_some] at h1
                exact h1
            · have hj_eq : j.toNat = new_n.toNat := by omega
              m6_steps
              exact hQ new_n scr1 sstk2 wsort1 m2 hsl1 hss2_len hws1_len hpre1 hnn_le
                ⟨by rw [hss2_len]; exact hnn_le, hnx1, hj_eq ▸ hok2⟩ hm2))

end LeanQbe.T.Examples.Kissat.FullM6Sweep
