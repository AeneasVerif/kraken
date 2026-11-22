module

public import LeanQbe.T.Examples.Kissat.FullM6CongSubstProof2c
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1

/-!
# Kissat M6 Congruence Closure & 2-Round Substitute Proofs — Part 2d

Builds on `FullM6CongSubstProof2c` to prove parametric `(Γ : Env)` `Func.wp`
contract (`FullM6CongSubst.lean` #22):
22. `full_cong_fwd_subsume` (`full_cong_fwd_subsume_wp`, `m6CongFwdSubsumeSpec`)

All proofs operate strictly within UNSAT-only `FullDenseInvW` / `M6FsScanInv` /
`M6FsKInv` invariants (complete proofs, default heartbeats, `<= 100` c/l).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6CongSubst

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open LeanQbe.T.Examples.Kissat.Full.FullDenseWatchHelpers
open Kraken.Bedrock2.Test
open scoped FullArenaTactics FullCongTactics M6bHeadTactics

/-! ## 1. Pure & Framing Helpers for `full_cong_fwd_subsume` -/

section Helpers

private theorem bv32_ult_lt {a b : BitVec 32} (h : a.ult b = true) : a.toNat < b.toNat := by
  simpa [BitVec.ult] using h

private theorem bv32_ult_not_lt {a b : BitVec 32} (h : a.ult b = false) :
    ¬ a.toNat < b.toNat := by
  simpa [BitVec.ult] using h

private theorem bv64_ult_lt {a b : BitVec 64} (h : a.ult b = true) : a.toNat < b.toNat := by
  simpa [BitVec.ult] using h

private theorem bv64_ult_not_lt {a b : BitVec 64} (h : a.ult b = false) :
    ¬ a.toNat < b.toNat := by
  simpa [BitVec.ult] using h

private theorem bv64_ofNat_toNat_lt {n : Nat} (h : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

private theorem bv64_shl1_toNat (x : BitVec 64) :
    (x <<< 1#64).toNat = (2 * x.toNat) % 2 ^ 64 := by
  rw [show (x <<< 1#64 : BitVec 64) = x <<< (1 : Nat) from rfl,
    BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

private theorem bv_zext32_toNat (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := x.isLt; omega)]

private theorem list_getElem_congr {α : Type _} {xs : List α} {i j : Nat}
    (h : i = j) (hi : i < xs.length) (hj : j < xs.length) : xs[i]'hi = xs[j]'hj := by
  subst h; rfl

private theorem list_eq_getElem_congr {α : Type _} {xs ys : List α} (h : xs = ys) {i : Nat}
    (hx : i < xs.length) (hy : i < ys.length) : xs[i]'hx = ys[i]'hy := by
  subst h; rfl

private theorem m6_bv8_sgt0_iff {v : BitVec 8}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) : (0#8 : BitVec 8).slt v = true ↔ v = 1#8 :=
  bv8_sgt0_iff_eq1 hdom

private theorem m6_bv8_slt0_iff {v : BitVec 8}
    (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) : v.slt 0#8 = true ↔ v = 0xFF#8 := by
  rcases hdom with rfl | rfl | rfl <;> decide

private theorem m6_lit_false_of_vals_slt0 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (_hcl0 : k.cur_level = 0) {l : Nat} (hl : l < 2 * k.cur_vars)
    (hslt : (k.vals[l]?.getD 0#8).slt 0#8 = true) :
    ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α → evalLitVal α l = false := by
  intro α hα
  have hff : k.vals[l]?.getD 0#8 = 0xFF#8 :=
    (m6_bv8_slt0_iff (hw.vals_domain l hl)).mp hslt
  obtain ⟨i, hi, htrl⟩ := (hw.vals_false_iff l hl).mp hff
  have hlv0 : (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
    have := hw.lvl_le i hi; omega
  have hent := hw.level0_sound i hi hlv0
  have hsat := CNF.entails_clause_def.mp hent α hα
  rw [← clauseEvalVal_iff, clauseEvalVal] at hsat
  simp only [List.any_cons, List.any_nil, Bool.or_false, htrl,
    show l ^^^ 1 = litNeg l from rfl, evalLitVal_litNeg] at hsat
  cases h : evalLitVal α l <;> simp_all

private theorem m6_garb_false_of_and_48 {hdr : BitVec 32}
    (h : (hdr &&& 0x00480000#32) = 0#32) : ((hdr &&& 0x00080000#32) != 0#32) = false := by
  have hmask : (0x00480000#32 : BitVec 32) &&& 0x00080000#32 = 0x00080000#32 := by decide
  have hb : (hdr &&& 0x00080000#32) = 0#32 := by
    calc hdr &&& 0x00080000#32 = hdr &&& (0x00480000#32 &&& 0x00080000#32) := by rw [hmask]
      _ = (hdr &&& 0x00480000#32) &&& 0x00080000#32 := by rw [BitVec.and_assoc]
      _ = 0#32 := by rw [h]; decide
  simp [hb]

private theorem m6_dense_slice_step {F_cur : List (List Nat)} {k : FullCoreState}
    {a p rem : Nat} (hs : DenseWatchSliceOk F_cur k a p rem) (hpos : 0 < rem) :
    ∃ w0 : BitVec 32, k.wstk[p]? = some w0 ∧
      (((w0 &&& 0x80000000#32) ≠ 0#32 ∧ DenseWatchSliceOk F_cur k a (p + 1) (rem - 1)) ∨
       ((w0 &&& 0x80000000#32) = 0#32 ∧ 2 ≤ rem ∧
         ∃ cr : BitVec 32, k.wstk[p + 1]? = some cr ∧ cr.toNat ∈ fullArenaClauseRefsCore k ∧
           DenseWatchSliceOk F_cur k a (p + 2) (rem - 2))) := by
  cases hs with
  | empty => omega
  | bin hp hf _ _ _ hrest => exact ⟨_, hp, Or.inl ⟨hf, hrest⟩⟩
  | occ hp hp1 hf _ _ href hrest => exact ⟨_, hp, Or.inr ⟨hf, by omega, _, hp1, href, hrest⟩⟩

private theorem m6_denseWatchSliceOk_with_repr {F_cur : List (List Nat)} {k : FullCoreState}
    {a p rem : Nat} (hs : DenseWatchSliceOk F_cur k a p rem) (r' : List (BitVec 32)) :
    DenseWatchSliceOk F_cur { k with repr := r' } a p rem := by
  induction hs with
  | empty => exact .empty
  | bin hp hf hne hl he _ ih => exact .bin hp hf hne hl he ih
  | occ hp hp1 hf hs hlt href _ ih => exact .occ hp hp1 hf hs hlt href ih

private abbrev m6DwsRepr := @m6_denseWatchSliceOk_with_repr

private theorem m6_denseWatchBounds {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hlk : k.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur k) (hdm : k.dense_mode ≠ 0#64)
    {l : Nat} (hl : l < 2 * k.cur_vars) :
    fullWatchOffCore k l + fullWatchSizeCore k l ≤ k.wstk.length := by
  have hwat := hw.watches
  unfold ModeWatchesInv at hwat; simp only [hdm, ↓reduceIte] at hwat
  have hb := hwat.layout.bounds l hl
  have hwl := hlk.wlen_le; have hwa := hlk.wstk_len_arr
  omega

private theorem m6_denseWatchSlice_of_inv {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState}
    (hw : FullWitnessInv c F0 F_cur k) (hdm : k.dense_mode ≠ 0#64)
    {l : Nat} (hl : l < 2 * k.cur_vars) :
    DenseWatchSliceOk F_cur k l (fullWatchOffCore k l) (fullWatchSizeCore k l) := by
  have hwat := hw.watches
  unfold ModeWatchesInv at hwat; simp only [hdm, ↓reduceIte] at hwat
  exact hwat.slices l hl

private theorem m6_denseInvW_with_mclr {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {mc' : List (BitVec 32)} (hl : mc'.length = c.max_vars) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with min_clr := mc' } } := by
  have hw' : FullWitnessInv c F0 F_cur { s.core with min_clr := mc' } :=
    { hd.2.1 with
      arena := { hd.2.1.arena with len_ok := hd.2.1.arena.len_ok }
      watches := hd.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
  exact ⟨⟨{ hd.1.core_ok with min_clr_len_arr := hl }, hd.1.scratch_ok⟩, hw',
    fullLitMarksClear_of_eq hd.2.2.1 rfl rfl, fullArenaVarsNodup_of_eq hd.2.2.2.1 rfl rfl,
    fullExtScratchOk_of_eq hd.2.2.2.2.1 rfl rfl rfl rfl,
    hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

private theorem m6_denseInvW_with_inc {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    (hu : (cnfOfClauses F_cur).Unsat) (inc' : BitVec 64) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with inconsistent := inc' } } :=
  ⟨⟨{ hd.1.core_ok with }, hd.1.scratch_ok⟩,
   fullWitnessInv_with_inconsistent hd.2.1 inc' (fun _ => hu),
   hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

private theorem m6_fs_markGarb_dense {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) (ag' : BitVec 64) :
    FullDenseInvW c F0 F_cur
      { s with core :=
        { s.core with
          arena := s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
          arena_garbage := ag' } } := by
  have hcl0 := hd.2.2.2.2.2.1
  have hmg := markGarb_preserves_fullWitnessInv hd.1 hd.2.1 href ag' fun idx hidx hne _ => by
    have hr := hd.2.1.level0_rsn_none idx hidx (by have := hd.2.1.lvl_le idx hidx; omega)
    exact absurd hr hne
  exact ⟨hmg.1, hmg.2.2.1, fullLitMarksClear_of_eq hd.2.2.1 rfl rfl, hmg.2.2.2.2 hd.2.2.2.1,
    ⟨fun i hi => (hd.2.2.2.2.1.1 i hi).elim Or.inl fun h => Or.inr (hmg.2.1 ▸ h),
     hd.2.2.2.2.1.2⟩, hcl0, hd.2.2.2.2.2.2⟩

private theorem m6_fs_markGarb_dense' {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) (hcr : cref < s.core.arena.length)
    (ag' : BitVec 64) :
    FullDenseInvW c F0 F_cur
      { s with core :=
        { s.core with
          arena := s.core.arena.set cref ((s.core.arena[cref]'hcr) ||| 0x00080000#32)
          arena_garbage := ag' } } := by
  have hhdr : fullArenaHdr s cref = s.core.arena[cref]'hcr := by
    unfold fullArenaHdr fullArenaHdrCore
    rw [List.getElem?_eq_getElem hcr, Option.getD_some]
  simpa only [hhdr] using m6_fs_markGarb_dense hd href ag'

private theorem m6_fs_markGarb_refs {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) (hcr : cref < s.core.arena.length)
    (ag' : BitVec 64) :
    fullArenaClauseRefs
      { s with core :=
        { s.core with
          arena := s.core.arena.set cref ((s.core.arena[cref]'hcr) ||| 0x00080000#32)
          arena_garbage := ag' } } = fullArenaClauseRefs s := by
  have hcl0 := hd.2.2.2.2.2.1
  have hhdr : fullArenaHdr s cref = s.core.arena[cref]'hcr := by
    unfold fullArenaHdr fullArenaHdrCore
    rw [List.getElem?_eq_getElem hcr, Option.getD_some]
  have hmg := markGarb_preserves_fullWitnessInv hd.1 hd.2.1 href ag' fun idx hidx hne _ => by
    have hr := hd.2.1.level0_rsn_none idx hidx (by have := hd.2.1.lvl_le idx hidx; omega)
    exact absurd hr hne
  simpa only [hhdr] using hmg.2.1

private theorem m6_addUnit_denseInvW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (hd : FullDenseInvW c F0 F_cur s)
    (hl' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hcl' : s'.core.cur_level = 0) (hdm' : s'.core.dense_mode = s.core.dense_mode)
    (hmrk' : s'.core.mrk = s.core.mrk) (hlm' : s'.core.lit_mark = s.core.lit_mark)
    (har' : s'.core.arena = s.core.arena) (hal' : s'.core.arena_len = s.core.arena_len)
    (hll' : s'.scratch.last_learned = s.scratch.last_learned)
    (hext' : s'.scratch.extend_len = s.scratch.extend_len) :
    FullDenseInvW c F0 F_cur s' :=
  ⟨hl', hw', fullLitMarksClear_of_eq hd.2.2.1 hmrk' hlm',
   fullArenaVarsNodup_of_eq hd.2.2.2.1 har' hal',
   fullExtScratchOk_of_eq hd.2.2.2.2.1 har' hal' hll' hext',
   hcl', hdm' ▸ hd.2.2.2.2.2.2⟩

/-- Core `fwd_subsume` invariant with `lit_mark` possibly dirty on indices listed in `tmp`. -/
private def M6FsBaseOk (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (cv0 : Nat) (alen0 : Nat) (fuel0 : BitVec 64) (s : FullState) : Prop :=
  s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
  (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8) ∧
  FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧
  s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64 ∧
  s.core.cur_vars = cv0 ∧ s.core.arena_len = alen0 ∧ s.core.fuel = fuel0 ∧
  FullCongReprInv F_cur (2 * cv0) s.core.repr

private theorem m6FsBaseOk_of_dense {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    (hrepr : FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr) :
    M6FsBaseOk c F0 F_cur s.core.cur_vars s.core.arena_len s.core.fuel s ∧
    (∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8) :=
  ⟨⟨hd.1, hd.2.1, hd.2.2.1.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1,
    hd.2.2.2.2.2.2, rfl, rfl, rfl, hrepr⟩, hd.2.2.1.2⟩

private theorem m6FsBaseOk_to_dense {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 alen0 : Nat} {fuel0 : BitVec 64} {s : FullState}
    (hb : M6FsBaseOk c F0 F_cur cv0 alen0 fuel0 s)
    (hlm : ∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8) :
    FullDenseInvW c F0 F_cur s ∧
    s.core.cur_vars = cv0 ∧ s.core.arena_len = alen0 ∧ s.core.fuel = fuel0 ∧
    FullCongReprInv F_cur (2 * cv0) s.core.repr :=
  ⟨⟨hb.1, hb.2.1, ⟨hb.2.2.1, hlm⟩, hb.2.2.2.1, hb.2.2.2.2.1,
    hb.2.2.2.2.2.1, hb.2.2.2.2.2.2.1⟩,
   hb.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.1,
   hb.2.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.2⟩

private theorem m6FsBaseOk_with_repr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 alen0 : Nat} {fuel0 : BitVec 64} {s : FullState}
    (hb : M6FsBaseOk c F0 F_cur cv0 alen0 fuel0 s) {r' : List (BitVec 32)}
    (hrl : r'.length = 2 * c.max_vars) (hrepr' : FullCongReprInv F_cur (2 * cv0) r') :
    M6FsBaseOk c F0 F_cur cv0 alen0 fuel0 { s with core := { s.core with repr := r' } } :=
  ⟨⟨{ hb.1.core_ok with repr_len := hrl }, hb.1.scratch_ok⟩,
   fullWitnessInv_with_repr hb.2.1 r', hb.2.2.1, hb.2.2.2.1,
   fullExtScratchOk_of_eq hb.2.2.2.2.1 rfl rfl rfl rfl,
   hb.2.2.2.2.2.1, hb.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.1,
   hb.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.1, hrepr'⟩

private theorem m6FsBaseOk_with_lm {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 alen0 : Nat} {fuel0 : BitVec 64} {s : FullState}
    (hb : M6FsBaseOk c F0 F_cur cv0 alen0 fuel0 s) {lm' : List (BitVec 8)}
    (hlml : lm'.length = 2 * c.max_vars) :
    M6FsBaseOk c F0 F_cur cv0 alen0 fuel0 { s with core := { s.core with lit_mark := lm' } } := by
  have hw' : FullWitnessInv c F0 F_cur { s.core with lit_mark := lm' } :=
    { hb.2.1 with
      arena := { hb.2.1.arena with len_ok := hb.2.1.arena.len_ok }
      watches := hb.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
  exact ⟨⟨{ hb.1.core_ok with lit_mark_len := hlml }, hb.1.scratch_ok⟩,
    hw', hb.2.2.1, fullArenaVarsNodup_of_eq hb.2.2.2.1 rfl rfl,
    fullExtScratchOk_of_eq hb.2.2.2.2.1 rfl rfl rfl rfl,
    hb.2.2.2.2.2.1, hb.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.1,
    hb.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.2⟩

private theorem m6FsBaseOk_with_tmp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 alen0 : Nat} {fuel0 : BitVec 64} {s : FullState}
    (hb : M6FsBaseOk c F0 F_cur cv0 alen0 fuel0 s) {tmp' : List (BitVec 32)}
    (htl : tmp'.length = c.max_vars) :
    M6FsBaseOk c F0 F_cur cv0 alen0 fuel0 { s with core := { s.core with tmp := tmp' } } :=
  ⟨⟨{ hb.1.core_ok with tmp_len_arr := htl }, hb.1.scratch_ok⟩,
   fullWitnessInv_with_tmp hb.2.1 tmp', hb.2.2.1,
   fullArenaVarsNodup_of_eq hb.2.2.2.1 rfl rfl,
   fullExtScratchOk_of_eq hb.2.2.2.2.1 rfl rfl rfl rfl,
   hb.2.2.2.2.2.1, hb.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.1,
   hb.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.2⟩

private theorem m6Fs_lm_set_mark {maxv cv msz : Nat} {tmp : List (BitVec 32)}
    {lm : List (BitVec 8)} {r : BitVec 32}
    (htmp_lt : ∀ j < msz, (tmp[j]?.getD 0#32).toNat < 2 * cv)
    (hlm_ok : ∀ l < 2 * maxv, lm[l]?.getD 0#8 = 0#8 ∨
      (∃ j < msz, (tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv))
    (hr_lt : r.toNat < 2 * cv) (hmsz_lt : msz < tmp.length) (_hr_len : r.toNat < lm.length) :
    let tmp' := tmp.set msz r
    let lm' := lm.set r.toNat 1#8
    (∀ j < msz + 1, (tmp'[j]?.getD 0#32).toNat < 2 * cv) ∧
    (∀ l < 2 * maxv, lm'[l]?.getD 0#8 = 0#8 ∨
      (∃ j < msz + 1, (tmp'[j]?.getD 0#32).toNat = l ∧ l < 2 * cv)) := by
  intro tmp' lm'; constructor
  · intro j hj; dsimp only [tmp']
    by_cases hjm : j = msz
    · subst hjm; rw [List.getElem?_set_self hmsz_lt, Option.getD_some]; exact hr_lt
    · rw [List.getElem?_set_ne (Ne.symm hjm)]; exact htmp_lt j (by omega)
  · intro l hl; dsimp only [lm', tmp']
    by_cases hlr : l = r.toNat
    · subst hlr; right
      refine ⟨msz, Nat.lt_succ_self msz, ?_, hr_lt⟩
      rw [List.getElem?_set_self hmsz_lt, Option.getD_some]
    · rw [List.getElem?_set_ne (Ne.symm hlr)]
      rcases hlm_ok l hl with h0 | ⟨j, hj, hjl, hlc⟩
      · exact Or.inl h0
      · right; refine ⟨j, by omega, ?_, hlc⟩
        rw [List.getElem?_set_ne (by omega)]; exact hjl

private theorem m6Fs_lm_set_one {maxv cv msz : Nat} {tmp : List (BitVec 32)}
    {lm : List (BitVec 8)} {k : Nat}
    (htmp_lt : ∀ j < msz, (tmp[j]?.getD 0#32).toNat < 2 * cv)
    (hlm_ok : ∀ l < 2 * maxv, lm[l]?.getD 0#8 = 0#8 ∨
      (∃ j < msz, (tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv))
    (hk : k < msz) (hk_lt : k < tmp.length)
    (_hrk_len : (tmp[k]'hk_lt).toNat < lm.length) :
    ∀ l < 2 * maxv, (lm.set (tmp[k]'hk_lt).toNat 1#8)[l]?.getD 0#8 = 0#8 ∨
      (∃ j < msz, (tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv) := by
  intro l hl
  by_cases hlk : l = (tmp[k]'hk_lt).toNat
  · right; refine ⟨k, hk, ?_, hlk ▸ ?_⟩
    · rw [List.getElem?_eq_getElem hk_lt, Option.getD_some, hlk]
    · have h := htmp_lt k hk; rwa [List.getElem?_eq_getElem hk_lt, Option.getD_some] at h
  · rw [List.getElem?_set_ne (Ne.symm hlk)]; exact hlm_ok l hl

private theorem m6Fs_lm_clear_step {maxv cv msz k : Nat} {tmp : List (BitVec 32)}
    {lm : List (BitVec 8)} (hk : k < msz) (hk_lt : k < tmp.length)
    (htk_len : (tmp[k]'hk_lt).toNat < lm.length)
    (hinv : ∀ l < 2 * maxv, lm[l]?.getD 0#8 = 0#8 ∨
      (∃ j, k ≤ j ∧ j < msz ∧ (tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv)) :
    ∀ l < 2 * maxv, (lm.set (tmp[k]'hk_lt).toNat 0#8)[l]?.getD 0#8 = 0#8 ∨
      (∃ j, k + 1 ≤ j ∧ j < msz ∧ (tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv) := by
  intro l hl
  by_cases hlk : l = (tmp[k]'hk_lt).toNat
  · subst hlk; left; rw [List.getElem?_set_self htk_len, Option.getD_some]
  · rw [List.getElem?_set_ne (Ne.symm hlk)]
    rcases hinv l hl with h0 | ⟨j, hkj, hjm, hjl, hlc⟩
    · exact Or.inl h0
    · right
      have hjk : j ≠ k := by
        intro heq; subst heq
        rw [List.getElem?_eq_getElem hk_lt, Option.getD_some] at hjl
        exact hlk hjl.symm
      exact ⟨j, by omega, hjm, hjl, hlc⟩

private theorem m6Fs_lm_clear_from_zero {maxv cv msz : Nat} {tmp : List (BitVec 32)}
    {lm : List (BitVec 8)}
    (h : ∀ l < 2 * maxv, lm[l]?.getD 0#8 = 0#8 ∨
      (∃ j < msz, (tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv)) :
    ∀ l < 2 * maxv, lm[l]?.getD 0#8 = 0#8 ∨
      (∃ j, 0 ≤ j ∧ j < msz ∧ (tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv) :=
  fun l hl => (h l hl).elim Or.inl fun ⟨j, hj, hjl, hlc⟩ => Or.inr ⟨j, Nat.zero_le _, hj, hjl, hlc⟩

private theorem m6Fs_lm_clear_done {maxv cv msz : Nat} {tmp : List (BitVec 32)}
    {lm : List (BitVec 8)}
    (h : ∀ l < 2 * maxv, lm[l]?.getD 0#8 = 0#8 ∨
      (∃ j, msz ≤ j ∧ j < msz ∧ (tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv)) :
    ∀ l < 2 * maxv, lm[l]?.getD 0#8 = 0#8 := fun l hl =>
  (h l hl).elim id fun ⟨j, hj1, hj2, _⟩ => by omega

private theorem m6Fs_msz0_unsat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {p sz : Nat} (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hp_ref : p ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s p = false)
    (hsz : fullArenaClauseSizeCore s.core p = sz)
    (hsem : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      ∀ j < sz, evalLitVal α (s.core.arena[p + 3 + j]?.getD 0#32).toNat = true → False) :
    (cnfOfClauses F_cur).Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro α hα
  have hwf := hw.arena.refs_wf p hp_ref
  have hbd : p + 3 + sz ≤ s.core.arena.length := by
    have := hlen.core_ok.arena_len_le; have := hlen.core_ok.arena_len_arr; omega
  have hsat := CNF.entails_clause_def.mp (hw.arena.entails p hp_ref hng) α hα
  rw [← clauseEvalVal_iff, clauseEvalVal, List.any_eq_true] at hsat
  obtain ⟨l, hl_mem, hl_true⟩ := hsat
  obtain ⟨j, hj, hget⟩ := (mem_fullArenaClauseLitsCore_iff (hsz ▸ hbd)).mp hl_mem
  have hj' : j < sz := hsz ▸ hj
  have hget' : (s.core.arena[p + 3 + j]?.getD 0#32).toNat = l := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hget]
  exact hsem α hα j hj' (hget' ▸ hl_true)

private theorem m6Fs_msz1_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {p sz : Nat} (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hp_ref : p ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s p = false)
    (hsz : fullArenaClauseSizeCore s.core p = sz) {u : Nat}
    (hsem : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      ∀ j < sz, evalLitVal α (s.core.arena[p + 3 + j]?.getD 0#32).toNat = true →
        evalLitVal α u = true) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [u]) := by
  refine entails_of_eval_mem fun α hα => ⟨u, by simp, ?_⟩
  have hwf := hw.arena.refs_wf p hp_ref
  have hbd : p + 3 + sz ≤ s.core.arena.length := by
    have := hlen.core_ok.arena_len_le; have := hlen.core_ok.arena_len_arr; omega
  have hsat := CNF.entails_clause_def.mp (hw.arena.entails p hp_ref hng) α hα
  rw [← clauseEvalVal_iff, clauseEvalVal, List.any_eq_true] at hsat
  obtain ⟨l, hl_mem, hl_true⟩ := hsat
  obtain ⟨j, hj, hget⟩ := (mem_fullArenaClauseLitsCore_iff (hsz ▸ hbd)).mp hl_mem
  have hj' : j < sz := hsz ▸ hj
  have hget' : (s.core.arena[p + 3 + j]?.getD 0#32).toNat = l := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hget]
  exact hsem α hα j hj' (hget' ▸ hl_true)

private def M6FsScanInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (cv0 alen0 : Nat) (fuel0 : BitVec 64) (sp sk : FullState) (msz : Nat)
    (s : FullState) : Prop :=
  M6FsBaseOk c F0 F_cur cv0 alen0 fuel0 s ∧
  s.core.arena = sp.core.arena ∧ s.core.wvec = sp.core.wvec ∧
  s.core.wstk = sp.core.wstk ∧ s.core.vals = sp.core.vals ∧
  s.core.tmp = sk.core.tmp ∧ s.core.inconsistent = 0#64 ∧
  (∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8 ∨
    (∃ j < msz, (s.core.tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv0))

private theorem m6FsScanInv_with_repr {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cv0 alen0 : Nat} {fuel0 : BitVec 64}
    {sp sk s : FullState} {msz : Nat}
    (h : M6FsScanInv c F0 F_cur cv0 alen0 fuel0 sp sk msz s)
    {r' : List (BitVec 32)} (hrl : r'.length = 2 * c.max_vars)
    (hrepr' : FullCongReprInv F_cur (2 * cv0) r') :
    M6FsScanInv c F0 F_cur cv0 alen0 fuel0 sp sk msz
      { s with core := { s.core with repr := r' } } :=
  ⟨m6FsBaseOk_with_repr h.1 hrl hrepr', h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
   h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

private theorem m6Fs_cr_lit_lt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 alen0 : Nat} {fuel0 : BitVec 64} {sp sk sd : FullState} {msz : Nat}
    (hsc : M6FsScanInv c F0 F_cur cv0 alen0 fuel0 sp sk msz sd)
    (hal_sp : sp.core.arena_len = alen0) {cr dsz dj : BitVec 32}
    (hcr_sp : cr.toNat ∈ fullArenaClauseRefsCore sp.core)
    (hng_sp : fullArenaClauseGarbCore sp.core cr.toNat = false)
    (hdsz_sp : fullArenaClauseSizeCore sp.core cr.toNat = dsz.toNat)
    (hdj : dj.toNat < dsz.toNat) :
    ∃ hbd : (cr.setWidth 64 + 3#64 + dj.setWidth 64).toNat < sd.core.arena.length,
      (sd.core.arena[(cr.setWidth 64 + 3#64 + dj.setWidth 64).toNat]'hbd).toNat < 2 * cv0 := by
  have hac := c.harena; unfold dimacsBound at hac
  rcases hsc with ⟨hb, har, _, _, _, _, _, _⟩
  have hcr_sd : cr.toNat ∈ fullArenaClauseRefsCore sd.core := by
    unfold fullArenaClauseRefsCore at hcr_sp ⊢
    rw [har, hb.2.2.2.2.2.2.2.2.1, ← hal_sp]; exact hcr_sp
  have hng_sd : fullArenaClauseGarbCore sd.core cr.toNat = false := by
    unfold fullArenaClauseGarbCore fullArenaHdrCore at hng_sp ⊢; rwa [har]
  have hdsz_sd : fullArenaClauseSizeCore sd.core cr.toNat = dsz.toNat := by
    unfold fullArenaClauseSizeCore at hdsz_sp ⊢; rwa [har]
  have hwf := hb.2.1.arena.refs_wf cr.toNat hcr_sd
  have hle := hb.1.core_ok.arena_len_le
  have harr := hb.1.core_ok.arena_len_arr
  have hadd : (cr.setWidth 64 + 3#64 + dj.setWidth 64).toNat =
      cr.toNat + 3 + dj.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_add, bv_zext32_toNat, bv_zext32_toNat,
      show (3#64 : BitVec 64).toNat = 3 from rfl,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hbd : (cr.setWidth 64 + 3#64 + dj.setWidth 64).toNat < sd.core.arena.length := by
    rw [hadd]; omega
  refine ⟨hbd, ?_⟩
  let ol := sd.core.arena[(cr.setWidth 64 + 3#64 + dj.setWidth 64).toNat]'hbd
  have hol_mem : ol.toNat ∈ fullArenaClauseLitsCore sd.core cr.toNat := by
    refine (mem_fullArenaClauseLitsCore_iff (by omega)).mpr ⟨dj.toNat, by omega, ?_⟩
    exact congrArg BitVec.toNat (list_getElem_congr hadd.symm _ _)
  have hlt := hb.2.1.arena.lits_lt cr.toNat hcr_sd hng_sd ol.toNat hol_mem
  rwa [hb.2.2.2.2.2.2.2.1] at hlt

private theorem m6Fs_k_lit_lt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 alen0 : Nat} {fuel0 : BitVec 64} {sp sk_in : FullState}
    {p : BitVec 64} {sz k : BitVec 32}
    (hb : M6FsBaseOk c F0 F_cur cv0 alen0 fuel0 sk_in) (har : sk_in.core.arena = sp.core.arena)
    (hal_sp : sp.core.arena_len = alen0) (hp_ref : p.toNat ∈ fullArenaClauseRefsCore sp.core)
    (hng : fullArenaClauseGarbCore sp.core p.toNat = false)
    (hsz : fullArenaClauseSizeCore sp.core p.toNat = sz.toNat)
    (hp_le : p.toNat + 3 + sz.toNat ≤ alen0)
    (hk : k.toNat < sz.toNat) :
    ∃ hbd : (p + 3#64 + k.setWidth 64).toNat < sk_in.core.arena.length,
      (sk_in.core.arena[(p + 3#64 + k.setWidth 64).toNat]'hbd).toNat < 2 * cv0 := by
  have hac := c.harena; unfold dimacsBound at hac
  have hp_sd : p.toNat ∈ fullArenaClauseRefsCore sk_in.core := by
    unfold fullArenaClauseRefsCore at hp_ref ⊢
    rw [har, hb.2.2.2.2.2.2.2.2.1, ← hal_sp]; exact hp_ref
  have hng_sd : fullArenaClauseGarbCore sk_in.core p.toNat = false := by
    unfold fullArenaClauseGarbCore fullArenaHdrCore at hng ⊢; rwa [har]
  have hsz_sd : fullArenaClauseSizeCore sk_in.core p.toNat = sz.toNat := by
    unfold fullArenaClauseSizeCore at hsz ⊢; rwa [har]
  have hal := hb.2.2.2.2.2.2.2.2.1
  have hle := hb.1.core_ok.arena_len_le
  have harr := hb.1.core_ok.arena_len_arr
  have hadd : (p + 3#64 + k.setWidth 64).toNat = p.toNat + 3 + k.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_add, bv_zext32_toNat,
      show (3#64 : BitVec 64).toNat = 3 from rfl,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hbd : (p + 3#64 + k.setWidth 64).toNat < sk_in.core.arena.length := by
    rw [hadd]; omega
  refine ⟨hbd, ?_⟩
  let l := sk_in.core.arena[(p + 3#64 + k.setWidth 64).toNat]'hbd
  have hl_mem : l.toNat ∈ fullArenaClauseLitsCore sk_in.core p.toNat := by
    refine (mem_fullArenaClauseLitsCore_iff (by omega)).mpr ⟨k.toNat, by omega, ?_⟩
    exact congrArg BitVec.toNat (list_getElem_congr hadd.symm _ _)
  have hlt := hb.2.1.arena.lits_lt p.toNat hp_sd hng_sd l.toNat hl_mem
  rwa [hb.2.2.2.2.2.2.2.1] at hlt

private def M6FsKInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (cv0 alen0 : Nat) (fuel0 : BitVec 64) (sp : FullState) (p sz : Nat)
    (msz k : Nat) (min_l : BitVec 32) (s : FullState) : Prop :=
  k ≤ sz ∧
  M6FsBaseOk c F0 F_cur cv0 alen0 fuel0 s ∧
  s.core.arena = sp.core.arena ∧ s.core.wvec = sp.core.wvec ∧
  s.core.wstk = sp.core.wstk ∧ s.core.vals = sp.core.vals ∧
  s.core.min_clr = sp.core.min_clr ∧ s.core.mrk = sp.core.mrk ∧
  s.core.inconsistent = 0#64 ∧
  msz ≤ cv0 ∧ (min_l = 0xFFFFFFFF#32 ∨ min_l.toNat < 2 * cv0) ∧
  (∀ j < msz, (s.core.tmp[j]?.getD 0#32).toNat < 2 * cv0) ∧
  (∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8 ∨
    (∃ j < msz, (s.core.tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv0)) ∧
  (∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
    ∀ j < k, evalLitVal α (s.core.arena[p + 3 + j]?.getD 0#32).toNat = true →
      ∃ q < msz, evalLitVal α (s.core.tmp[q]?.getD 0#32).toNat = true)

private theorem m6Fs_k_sem_false {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 : Nat} {s : FullState} {p k msz : Nat} (hw : FullWitnessInv c F0 F_cur s.core)
    (hcl0 : s.core.cur_level = 0) (hcv : s.core.cur_vars = cv0)
    (hsem : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      ∀ j < k, evalLitVal α (s.core.arena[p + 3 + j]?.getD 0#32).toNat = true →
        ∃ q < msz, evalLitVal α (s.core.tmp[q]?.getD 0#32).toNat = true)
    (hk_arr : p + 3 + k < s.core.arena.length)
    (hl_lt : (s.core.arena[p + 3 + k]'hk_arr).toNat < 2 * cv0)
    (hslt : (s.core.vals[(s.core.arena[p + 3 + k]'hk_arr).toNat]?.getD 0#8).slt 0#8 = true) :
    ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      ∀ j < k + 1, evalLitVal α (s.core.arena[p + 3 + j]?.getD 0#32).toNat = true →
        ∃ q < msz, evalLitVal α (s.core.tmp[q]?.getD 0#32).toNat = true := by
  intro α hα j hj het
  by_cases hjk : j < k
  · exact hsem α hα j hjk het
  · obtain rfl : j = k := (by omega)
    rw [List.getElem?_eq_getElem hk_arr, Option.getD_some] at het
    have hf := m6_lit_false_of_vals_slt0 hw hcl0 (hcv ▸ hl_lt) hslt α hα
    rw [het] at hf; cases hf

private theorem m6_litEquiv_eval {F : CNF Nat} {l1 l2 : Nat}
    (heqv : LitEquiv F l1 l2) {α : Nat → Bool} (hα : F.Sat α) :
    evalLitVal α l1 = evalLitVal α l2 := by
  have h12 := CNF.entails_clause_def.mp heqv.1 α hα
  have h21 := CNF.entails_clause_def.mp heqv.2 α hα
  rw [← clauseEvalVal_iff, clauseEvalVal] at h12 h21
  simp only [List.any_cons, List.any_nil, Bool.or_false, evalLitVal_litNeg] at h12 h21
  cases e1 : evalLitVal α l1 <;> cases e2 : evalLitVal α l2 <;> simp_all

private theorem m6Fs_k_sem_equiv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 : Nat} {s : FullState} {p k msz : Nat} {r : BitVec 32}
    (hw : FullWitnessInv c F0 F_cur s.core) (hcl0 : s.core.cur_level = 0)
    (hcv : s.core.cur_vars = cv0)
    (hsem : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      ∀ j < k, evalLitVal α (s.core.arena[p + 3 + j]?.getD 0#32).toNat = true →
        ∃ q < msz, evalLitVal α (s.core.tmp[q]?.getD 0#32).toNat = true)
    (hk_arr : p + 3 + k < s.core.arena.length) (hr_lt : r.toNat < 2 * cv0)
    (heqv : LitEquiv (cnfOfClauses F_cur) (s.core.arena[p + 3 + k]'hk_arr).toNat r.toNat)
    (hslt : (s.core.vals[r.toNat]?.getD 0#8).slt 0#8 = true) :
    ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      ∀ j < k + 1, evalLitVal α (s.core.arena[p + 3 + j]?.getD 0#32).toNat = true →
        ∃ q < msz, evalLitVal α (s.core.tmp[q]?.getD 0#32).toNat = true := by
  intro α hα j hj het
  by_cases hjk : j < k
  · exact hsem α hα j hjk het
  · obtain rfl : j = k := (by omega)
    rw [List.getElem?_eq_getElem hk_arr, Option.getD_some] at het
    have hev_r : evalLitVal α r.toNat = true := by
      have h := m6_litEquiv_eval heqv hα; rwa [← h]
    have hf := m6_lit_false_of_vals_slt0 hw hcl0 (hcv ▸ hr_lt) hslt α hα
    rw [hev_r] at hf; cases hf

private theorem m6Fs_k_sem_mem {F_cur : List (List Nat)} {maxv cv0 p k msz : Nat}
    {ar : List (BitVec 32)} {tmp : List (BitVec 32)} {lm : List (BitVec 8)} {r : BitVec 32}
    (hsem : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      ∀ j < k, evalLitVal α (ar[p + 3 + j]?.getD 0#32).toNat = true →
        ∃ q < msz, evalLitVal α (tmp[q]?.getD 0#32).toNat = true)
    (hk_arr : p + 3 + k < ar.length) (hr_lt : r.toNat < 2 * cv0) (hcv : cv0 ≤ maxv)
    (hlm_ok : ∀ l < 2 * maxv, lm[l]?.getD 0#8 = 0#8 ∨
      (∃ j < msz, (tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv0))
    (hneq : lm[r.toNat]?.getD 0#8 ≠ 0#8)
    (heqv : LitEquiv (cnfOfClauses F_cur) (ar[p + 3 + k]'hk_arr).toNat r.toNat) :
    ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      ∀ j < k + 1, evalLitVal α (ar[p + 3 + j]?.getD 0#32).toNat = true →
        ∃ q < msz, evalLitVal α (tmp[q]?.getD 0#32).toNat = true := by
  intro α hα j hj het
  by_cases hjk : j < k
  · exact hsem α hα j hjk het
  · obtain rfl : j = k := (by omega)
    rw [List.getElem?_eq_getElem hk_arr, Option.getD_some] at het
    rcases hlm_ok r.toNat (by omega) with h0 | ⟨q, hq, hqr, _⟩
    · exact absurd h0 hneq
    · refine ⟨q, hq, ?_⟩
      rw [hqr, ← m6_litEquiv_eval heqv hα]; exact het

private theorem m6Fs_k_sem_push {F_cur : List (List Nat)} {p k msz : Nat}
    {ar tmp : List (BitVec 32)} {r : BitVec 32}
    (hsem : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      ∀ j < k, evalLitVal α (ar[p + 3 + j]?.getD 0#32).toNat = true →
        ∃ q < msz, evalLitVal α (tmp[q]?.getD 0#32).toNat = true)
    (hk_arr : p + 3 + k < ar.length) (hmsz_lt : msz < tmp.length)
    (heqv : LitEquiv (cnfOfClauses F_cur) (ar[p + 3 + k]'hk_arr).toNat r.toNat) :
    ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      ∀ j < k + 1, evalLitVal α (ar[p + 3 + j]?.getD 0#32).toNat = true →
        ∃ q < msz + 1, evalLitVal α ((tmp.set msz r)[q]?.getD 0#32).toNat = true := by
  intro α hα j hj het
  by_cases hjk : j < k
  · obtain ⟨q, hq, hqt⟩ := hsem α hα j hjk het
    refine ⟨q, by omega, ?_⟩
    rw [List.getElem?_set_ne (by omega)]; exact hqt
  · obtain rfl : j = k := (by omega)
    rw [List.getElem?_eq_getElem hk_arr, Option.getD_some] at het
    refine ⟨msz, Nat.lt_succ_self _, ?_⟩
    rw [List.getElem?_set_self hmsz_lt, Option.getD_some, ← m6_litEquiv_eval heqv hα]
    exact het

private theorem bv8_sext32_slt0_true {x : BitVec 8}
    (h : (x.signExtend 32).slt 0#32 = true) : x.slt 0#8 = true := by
  have hi : (x.signExtend 32).toInt = x.toInt := by
    rw [BitVec.toInt_signExtend, show min 32 8 = 8 from rfl, Int.bmod_def]
    have h1 : -(2 ^ 7 : Int) ≤ x.toInt := BitVec.le_toInt x
    have h2 : x.toInt < 2 ^ 7 := @BitVec.toInt_lt 8 x
    have hpow : ((2 ^ 8 : Nat) : Int) = 256 := rfl
    rw [hpow]; split <;> omega
  simpa [BitVec.slt, hi] using h

private theorem bv8_zext32_beq0_false {x : BitVec 8}
    (h : (x.setWidth 32 == 0#32) = false) : x ≠ 0#8 := by
  intro hx; subst hx; simp at h

private theorem bv64_shl1_ofNat_lt {n : Nat} (h : 2 * n < 2 ^ 64) :
    (BitVec.ofNat 64 n <<< (1 : Nat)).toNat = 2 * n := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat,
    Nat.pow_one, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64), Nat.mul_comm, Nat.mod_eq_of_lt h]

private theorem bv32_and_msb_ne0 {w0 : BitVec 32}
    (h : ((w0 &&& 0x80000000#32 != 0#32, ()).fst) = true) :
    (w0 &&& 0x80000000#32) ≠ 0#32 :=
  bne_iff_ne.mp h

private theorem bv32_and_msb_eq0 {w0 : BitVec 32}
    (h : ((w0 &&& 0x80000000#32 != 0#32, ()).fst) = false) :
    (w0 &&& 0x80000000#32) = 0#32 := by
  cases hb : (w0 &&& 0x80000000#32 == 0#32)
  · have h1 : (w0 &&& 0x80000000#32 != 0#32) = true := by simp [bne, hb]
    change (w0 &&& 0x80000000#32 != 0#32) = false at h
    rw [h1] at h; exact Bool.noConfusion h
  · exact beq_iff_eq.mp hb

private theorem bv32_and_48_eq0 {dhdr : BitVec 32}
    (h : ((dhdr &&& (524288#32 ||| 4194304#32) != 0#32, ()).fst) = false) :
    (dhdr &&& 0x00480000#32) = 0#32 := by
  have hmask : (524288#32 ||| 4194304#32 : BitVec 32) = 0x00480000#32 := by decide
  cases hb : (dhdr &&& 0x00480000#32 == 0#32)
  · have h1 : (dhdr &&& (524288#32 ||| 4194304#32) != 0#32) = true := by
      simp [hmask, bne, hb]
    change (dhdr &&& (524288#32 ||| 4194304#32) != 0#32) = false at h
    rw [h1] at h; exact Bool.noConfusion h
  · exact beq_iff_eq.mp hb

private theorem m6Fs_watch_2_arr {c : FullCfg} {k : FullCoreState} {cv : Nat}
    {l : BitVec 32} (hlk : k.LengthsOk c) (_hcv_eq : k.cur_vars = cv) (hl : l.toNat < 2 * cv) :
    (l.setWidth 64 <<< 1#64).toNat < k.wvec.length ∧
    ((l.setWidth 64 <<< 1#64) + 1#64).toNat < k.wvec.length := by
  have hcm := hlk.cur_vars_le
  have h2_64 : 2 * l.toNat < 2 ^ 64 := by have := l.isLt; omega
  have hz := bv_zext32_toNat l
  have h2 : (l.setWidth 64 <<< 1#64).toNat = 2 * l.toNat := by
    rw [bv64_shl1_toNat, hz, Nat.mod_eq_of_lt h2_64]
  have h21 : ((l.setWidth 64 <<< 1#64) + 1#64).toNat = 2 * l.toNat + 1 := by
    rw [BitVec.toNat_add, h2, show (1#64 : BitVec 64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  have hwl := hlk.wvec_len
  exact ⟨by rw [h2]; omega, by rw [h21]; omega⟩

private theorem m6Fs_watch_off_eq {c : FullCfg} {k : FullCoreState} {cv : Nat}
    {l : BitVec 32} (hlk : k.LengthsOk c) (_hcv_eq : k.cur_vars = cv) (_hl : l.toNat < 2 * cv)
    (h2 : (l.setWidth 64 <<< 1#64).toNat < k.wvec.length)
    (h21 : ((l.setWidth 64 <<< 1#64) + 1#64).toNat < k.wvec.length) :
    let woff := (k.wvec[(l.setWidth 64 <<< 1#64).toNat]'h2).setWidth 64
    let wsz := (k.wvec[((l.setWidth 64 <<< 1#64) + 1#64).toNat]'h21).setWidth 64
    woff.toNat = fullWatchOffCore k l.toNat ∧
    wsz.toNat = fullWatchSizeCore k l.toNat ∧
    (woff + wsz).toNat = woff.toNat + wsz.toNat := by
  have h2_64 : 2 * l.toNat < 2 ^ 64 := by have := l.isLt; omega
  have hz := bv_zext32_toNat l
  have hidx2 : (l.setWidth 64 <<< 1#64).toNat = 2 * l.toNat := by
    rw [bv64_shl1_toNat, hz, Nat.mod_eq_of_lt h2_64]
  have hidx21 : ((l.setWidth 64 <<< 1#64) + 1#64).toNat = 2 * l.toNat + 1 := by
    rw [BitVec.toNat_add, hidx2, show (1#64 : BitVec 64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega)]
  have ho : ((k.wvec[(l.setWidth 64 <<< 1#64).toNat]'h2).setWidth 64).toNat =
      fullWatchOffCore k l.toNat := by
    unfold fullWatchOffCore
    rw [bv_zext32_toNat, list_getElem_congr hidx2 _ (by have := hlk.wvec_len; omega),
      List.getElem?_eq_getElem (by have := hlk.wvec_len; omega), Option.getD_some]
  have hs : ((k.wvec[((l.setWidth 64 <<< 1#64) + 1#64).toNat]'h21).setWidth 64).toNat =
      fullWatchSizeCore k l.toNat := by
    unfold fullWatchSizeCore
    rw [bv_zext32_toNat, list_getElem_congr hidx21 _ (by have := hlk.wvec_len; omega),
      List.getElem?_eq_getElem (by have := hlk.wvec_len; omega), Option.getD_some]
  have hlt1 : ((k.wvec[(l.setWidth 64 <<< 1#64).toNat]'h2).setWidth 64).toNat < 2 ^ 32 := by
    rw [bv_zext32_toNat]; exact BitVec.isLt _
  have hlt2 : ((k.wvec[((l.setWidth 64 <<< 1#64) + 1#64).toNat]'h21).setWidth 64).toNat < 2 ^ 32
    := by rw [bv_zext32_toNat]; exact BitVec.isLt _
  refine ⟨ho, hs, ?_⟩
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]

private theorem m6Fs_scan_cr_ar {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 alen0 : Nat} {fuel0 : BitVec 64} {sp sk s : FullState} {msz : Nat} {cr : BitVec 32}
    (hs : M6FsScanInv c F0 F_cur cv0 alen0 fuel0 sp sk msz s)
    (hwf : cr.toNat + 3 ≤ s.core.arena_len ∧ 3 ≤ fullArenaClauseSizeCore s.core cr.toNat ∧
      cr.toNat + 3 + fullArenaClauseSizeCore s.core cr.toNat ≤
        fullArenaNextOff s.core.arena s.core.arena_len cr.toNat ∧
      fullArenaNextOff s.core.arena s.core.arena_len cr.toNat ≤ s.core.arena_len ∧
      (fullArenaNextOff s.core.arena s.core.arena_len cr.toNat = s.core.arena_len ∨
       fullArenaNextOff s.core.arena s.core.arena_len cr.toNat + 3 ≤ s.core.arena_len)) :
    cr.toNat < s.core.arena.length ∧
    (cr.setWidth 64 + 2#64).toNat < s.core.arena.length ∧
    (cr.setWidth 64 + 2#64).toNat = cr.toNat + 2 := by
  have hac := c.harena; unfold dimacsBound at hac
  have h1 := hs.1.1.core_ok.arena_len_le
  have h2 := hs.1.1.core_ok.arena_len_arr
  have h3 : (cr.setWidth 64 + 2#64).toNat = cr.toNat + 2 := by
    rw [bv64_add_nat_lt 2 (by decide) (by rw [bv_zext32_toNat]; have := cr.isLt; omega),
      bv_zext32_toNat]
  exact ⟨by omega, by rw [h3]; omega, h3⟩

private theorem m6Fs_scan_vals_lt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 alen0 : Nat} {fuel0 : BitVec 64} {sp sk s : FullState} {msz x : Nat}
    (hs : M6FsScanInv c F0 F_cur cv0 alen0 fuel0 sp sk msz s) (hx : x < 2 * cv0) :
    x < s.core.vals.length := by
  have := hs.1.1.core_ok.vals_len; have := hs.1.1.core_ok.cur_vars_le
  have := hs.1.2.2.2.2.2.2.2.1; omega

private theorem m6Fs_scan_lm_lt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 alen0 : Nat} {fuel0 : BitVec 64} {sp sk s : FullState} {msz x : Nat}
    (hs : M6FsScanInv c F0 F_cur cv0 alen0 fuel0 sp sk msz s) (hx : x < 2 * cv0) :
    x < s.core.lit_mark.length := by
  have := hs.1.1.core_ok.lit_mark_len; have := hs.1.1.core_ok.cur_vars_le
  have := hs.1.2.2.2.2.2.2.2.1; omega

private theorem m6Fs_base_vals_lt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 alen0 : Nat} {fuel0 : BitVec 64} {s : FullState} {x : Nat}
    (hb : M6FsBaseOk c F0 F_cur cv0 alen0 fuel0 s) (hx : x < 2 * cv0) :
    x < s.core.vals.length := by
  have := hb.1.core_ok.vals_len; have := hb.1.core_ok.cur_vars_le
  have := hb.2.2.2.2.2.2.2.1; omega

private theorem m6Fs_base_lm_lt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 alen0 : Nat} {fuel0 : BitVec 64} {s : FullState} {x : Nat}
    (hb : M6FsBaseOk c F0 F_cur cv0 alen0 fuel0 s) (hx : x < 2 * cv0) :
    x < s.core.lit_mark.length := by
  have := hb.1.core_ok.lit_mark_len; have := hb.1.core_ok.cur_vars_le
  have := hb.2.2.2.2.2.2.2.1; omega

end Helpers

/-! ## 2. `#22` `full_cong_fwd_subsume_wp` (`m6CongFwdSubsumeSpec`) -/

section FwdSubsumeProof

theorem full_cong_fwd_subsume_wp (Γ : Env)
    (hNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hFind : ∀ a m Q X, fullCongFindSpec a m Q X →
      Γ "full_cong_find" [i64, i32] [i32] a m Q X)
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X) :
    ∀ a m Q X, m6CongFwdSubsumeSpec a m Q X →
      Func.wp Γ full_cong_fwd_subsume_body a m Q X := by
  rintro ⟨h, tick_lim, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s0, R, rfl, hd0, hrepr0, hm0, hQ⟩
  have hmx := c.hmaxv; have hac := c.harena; have hwc := c.hwcap
  unfold dimacsBound at hmx hac hwc
  let cv0 := s0.core.cur_vars; let alen0 := s0.core.arena_len; let fuel0 := s0.core.fuel
  have hcv_le : cv0 ≤ c.max_vars := hd0.1.core_ok.cur_vars_le
  have hmclr_len0 := hd0.1.core_ok.min_clr_len_arr
  unfold Func.wp full_cong_fwd_subsume_body
  m6b_to_group
  refine wp_join_group (ts := [])
    (fun () mj => mj = m0 ∧ (s0.core.inconsistent ≠ 0#64 ∨ s0.scratch.ant_sz ≠ 0#64))
    (fun _ ⟨⟩ mj ⟨hmj, _hcond⟩ => by
      have hmj0 : (FullMem c s0 ⋆ R) mj := hmj ▸ hm0
      m6b_to_group
      refine wp_join_group (ts := [i64])
        (fun (r, ()) mr => mr = mj ∧ (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → F0.Unsat))
        (fun _ ⟨r, ⟨⟩⟩ mr ⟨hmr, hr_dom, huns⟩ => by
          m6b_steps; exact hQ r s0 mr hd0 rfl rfl hrepr0 hr_dom huns (hmr ▸ hmj0))
        (fun Jret hJret => by
          m6b_split
          · m6b_let
            exact hJret (20#64, ()) mj ⟨rfl, Or.inr rfl, fun _ =>
              FullM3CongBva.unsat_of_inconsistent_w hd0.2.1 (bne_iff_ne.mp hc)⟩
          · m6b_let; exact hJret (1#64, ()) mj ⟨rfl, Or.inl rfl, fun h => by cases h⟩))
    ?_
  intro Jearly hJearly
  m6b_split
  · m6b_let; exact hJearly () m0 ⟨rfl, Or.inl (bne_iff_ne.mp hc)⟩
  · clear hc; m6b_split
    · m6b_let; exact hJearly () m0 ⟨rfl, Or.inr (bne_iff_ne.mp hc)⟩
    · clear hc; m6b_steps
      refine wp_loop_inv (ts := [i64])
        (fun (i, ()) mi => ∃ si : FullState,
          i.toNat ≤ cv0 ∧ FullDenseInvW c F0 F_cur si ∧
          si.core.cur_vars = cv0 ∧ si.core.arena_len = alen0 ∧ si.core.fuel = fuel0 ∧
          FullCongReprInv F_cur (2 * cv0) si.core.repr ∧ (FullMem c si ⋆ R) mi)
        (fun (i, ()) _ => cv0 - i.toNat)
        (fun J0 hJ0 => by
          m6b_let
          exact hJ0 (0#64, ()) m0 ⟨s0, Nat.zero_le _, hd0, rfl, rfl, rfl, hrepr0, hm0⟩)
        (fun J0 (i, ()) mi ⟨si, hi_le, hdi, hcvi, hali, hfli, hrepri, hmi⟩ ihi => ?_)
      have hmli := hdi.1.core_ok.min_clr_len_arr
      m6b_split
      · have hi_lt : i.toNat < cv0 := by
          have h := bv64_ult_lt hc; rwa [bv64_ofNat_toNat_lt (by omega)] at h
        have hi1_n : (i + 1#64).toNat = i.toNat + 1 := bv64_add1_lt (by omega)
        have hi_arr : i.toNat < si.core.min_clr.length := by omega
        clear hc; m6b_steps
        let si' : FullState :=
          { si with core := { si.core with min_clr := si.core.min_clr.set i.toNat 0#32 } }
        exact ihi (i + 1#64, ()) m (by dsimp only; omega)
          ⟨si', by rw [hi1_n]; omega, m6_denseInvW_with_mclr hdi (by simp [hmli]),
           hcvi, hali, hfli, hrepri, hm⟩
      · clear hc; m6b_to_group
        refine wp_loop_inv (ts := [i64, .bool])
          (fun (i2, _hmch, ()) mi2 => ∃ si2 : FullState,
            i2.toNat ≤ cv0 ∧ FullDenseInvW c F0 F_cur si2 ∧
            si2.core.cur_vars = cv0 ∧ si2.core.arena_len = alen0 ∧ si2.core.fuel = fuel0 ∧
            FullCongReprInv F_cur (2 * cv0) si2.core.repr ∧ (FullMem c si2 ⋆ R) mi2)
          (fun (i2, _, ()) _ => cv0 - i2.toNat)
          (fun Jm hJm => by
            m6b_steps
            exact hJm (0#64, false, ()) mi
              ⟨si, Nat.zero_le _, hdi, hcvi, hali, hfli, hrepri, hmi⟩)
          (fun Jm (i2, hmch, ()) mi2
              ⟨si2, hi2_le, hdi2, hcvi2, hali2, hfli2, hrepri2, hmi2⟩ ihm => ?_)
        have hfl_len2 := hdi2.1.core_ok.flags_len
        have hmli2 := hdi2.1.core_ok.min_clr_len_arr
        m6b_split
        · have hi2_lt : i2.toNat < cv0 := by
            have h := bv64_ult_lt hc; rwa [bv64_ofNat_toNat_lt (by omega)] at h
          have hi2_1 : (i2 + 1#64).toNat = i2.toNat + 1 := bv64_add1_lt (by omega)
          have hi2_fl : i2.toNat < si2.core.flags.length := by omega
          clear hc; m6b_to_group
          refine wp_join_group (ts := [.bool])
            (fun (hm', ()) mj => ∃ sj : FullState,
              FullDenseInvW c F0 F_cur sj ∧ sj.core.cur_vars = cv0 ∧
              sj.core.arena_len = alen0 ∧ sj.core.fuel = fuel0 ∧
              FullCongReprInv F_cur (2 * cv0) sj.core.repr ∧ (FullMem c sj ⋆ R) mj)
            (fun _ ⟨hm', ⟨⟩⟩ mj ⟨sj, hdj, hcvj, halj, hflj, hreprj, hmj⟩ => by
              m6b_steps
              exact ihm (i2 + 1#64, hm', ()) mj (by dsimp only; omega)
                ⟨sj, by rw [hi2_1]; omega, hdj, hcvj, halj, hflj, hreprj, hmj⟩)
            (fun Jhm hJhm => by
              m6b_split
              · have hlit_n : (BitVec.setWidth 32 (i2 <<< (1 : Nat))).toNat = 2 * i2.toNat := by
                  rw [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
                    Nat.mul_comm, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                clear hc; m6b_steps; m6b_call hFind
                refine ⟨F_cur, 2 * cv0, si2.core.repr, FullReprRest c si2 ⋆ R,
                  hcvi2 ▸ hrepri2, by rw [hlit_n]; omega, focus_full_repr hmi2,
                  fun rr repr_r mr hrl_r hrepr_r _ hrr_lt _ hmr => ?_⟩
                let sr : FullState := { si2 with core := { si2.core with repr := repr_r } }
                have hmr' : (FullMem c sr ⋆ R) mr := unfocus_full_repr hmr
                have hdr := m6_fullDenseInvW_with_repr hdi2 (hrl_r.trans hdi2.1.core_ok.repr_len)
                m6b_to_group
                refine wp_join_group (ts := [.bool])
                  (fun (_hm'', ()) mj => ∃ sj : FullState,
                    FullDenseInvW c F0 F_cur sj ∧ sj.core.cur_vars = cv0 ∧
                    sj.core.arena_len = alen0 ∧ sj.core.fuel = fuel0 ∧
                    FullCongReprInv F_cur (2 * cv0) sj.core.repr ∧ (FullMem c sj ⋆ R) mj)
                  (fun _ ⟨hm'', ⟨⟩⟩ mj ⟨sj, hdj, hcvj, halj, hflj, hreprj, hmj⟩ =>
                    hJhm (hm'', ()) mj ⟨sj, hdj, hcvj, halj, hflj, hreprj, hmj⟩)
                  (fun Jhm2 hJhm2 => by
                    m6b_split
                    · have hri_mc : i2.toNat < sr.core.min_clr.length := by
                        change i2.toNat < si2.core.min_clr.length; omega
                      have hrr1_n : ((rr >>> 1#32).setWidth 64).toNat = rr.toNat / 2 := by
                        rw [bv_zext32_toNat,
                          show (rr >>> 1#32 : BitVec 32) = rr >>> (1 : Nat) from rfl,
                          BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
                      have hrr1_mc : ((rr >>> 1#32).setWidth 64).toNat <
                          (sr.core.min_clr.set i2.toNat 1#32).length := by
                        rw [List.length_set, hrr1_n]
                        change rr.toNat / 2 < si2.core.min_clr.length; omega
                      clear hc; m6b_steps
                      have hsr_mcl : sr.core.min_clr.length = c.max_vars := hmli2
                      exact hJhm2 (true, ()) m ⟨_, m6_denseInvW_with_mclr
                        (m6_denseInvW_with_mclr hdr (by rw [List.length_set]; exact hsr_mcl))
                        (by rw [List.length_set, List.length_set]; exact hsr_mcl),
                        hcvi2, hali2, hfli2, hrepr_r, hm⟩
                    · m6b_let; exact hJhm2 (hmch, ()) mr
                        ⟨sr, hdr, hcvi2, hali2, hfli2, hrepr_r, hmr'⟩)
              · m6b_let; exact hJhm (hmch, ()) mi2
                  ⟨si2, hdi2, hcvi2, hali2, hfli2, hrepri2, hmi2⟩)
        · clear hc; m6b_split
          · m6b_to_group
            refine wp_loop_inv (ts := [i64, i64])
              (fun (p, _ticks, ()) mp => ∃ sp : FullState,
                p.toNat ≤ alen0 ∧ (p.toNat = alen0 ∨ p.toNat ∈ fullArenaClauseRefs sp) ∧
                FullDenseInvW c F0 F_cur sp ∧ sp.core.cur_vars = cv0 ∧
                sp.core.arena_len = alen0 ∧ sp.core.fuel = fuel0 ∧
                FullCongReprInv F_cur (2 * cv0) sp.core.repr ∧ (FullMem c sp ⋆ R) mp)
              (fun (p, _, ()) _ => alen0 - p.toNat)
              (fun Jp hJp => by
                have h0_mem : 0 = alen0 ∨ 0 ∈ fullArenaClauseRefs si2 := by
                  rcases Nat.eq_zero_or_pos alen0 with hz | hpos
                  · exact Or.inl hz.symm
                  · exact Or.inr (fullArenaClauseRefs_zero_mem hdi2.2.1 (by rw [hali2]; exact hpos))
                m6b_steps
                exact hJp (0#64, 0#64, ()) mi2
                  ⟨si2, Nat.zero_le _, h0_mem, hdi2, hcvi2, hali2, hfli2, hrepri2, hmi2⟩)
              (fun Jp (p, ticks, ()) mp
                  ⟨sp, hp_le, hp_mem, hdp, hcvp, halp, hflp, hreprp, hmp⟩ ihp => ?_)
            m6b_to_group
            refine wp_join_group (ts := [])
              (fun () me => ∃ se : FullState,
                FullDenseInvW c F0 F_cur se ∧ se.core.cur_vars = cv0 ∧ se.core.fuel = fuel0 ∧
                FullCongReprInv F_cur (2 * cv0) se.core.repr ∧ (FullMem c se ⋆ R) me)
              (fun _ ⟨⟩ me ⟨se, hde, hcve, hfle, hrepre, hme⟩ => by
                m6b_to_group
                refine wp_join_group (ts := [i64])
                  (fun (r, ()) mr => mr = me ∧ (r = 1#64 ∨ r = 20#64) ∧
                    (r = 20#64 → F0.Unsat))
                  (fun _ ⟨r, ⟨⟩⟩ mr ⟨hmr, hr_dom, huns⟩ => by
                    m6b_steps
                    exact hQ r se mr hde hcve hfle (hcve ▸ hrepre) hr_dom huns (hmr ▸ hme))
                  (fun Jr hJr => by
                    m6b_split
                    · m6b_let
                      exact hJr (20#64, ()) me ⟨rfl, Or.inr rfl, fun _ =>
                        FullM3CongBva.unsat_of_inconsistent_w hde.2.1 (bne_iff_ne.mp hc)⟩
                    · m6b_let; exact hJr (1#64, ()) me ⟨rfl, Or.inl rfl, fun h => by cases h⟩))
              ?_
            intro Jexit hJexit
            clear hd0 hrepr0 hm0 hmclr_len0 Jearly hJearly J0 hi_le hdi hcvi hali hfli hrepri hmi
              hmli ihi Jm hi2_le hdi2 hcvi2 hali2 hfli2 hrepri2 hmi2 hfl_len2 hmli2 ihm
            m6b_split
            · have har_le_p0 := hdp.1.core_ok.arena_len_le
              have har_arr_p0 := hdp.1.core_ok.arena_len_arr
              have hp_lt : p.toNat < alen0 := by
                have h := bv64_ult_lt hc; rwa [halp, bv64_ofNat_toNat_lt (by omega)] at h
              clear hc; m6b_split
              · have htk_lt : ticks.toNat < tick_lim.toNat := bv64_ult_lt hc
                have htk1_n : (ticks + 1#64).toNat = ticks.toNat + 1 := bv64_add1_lt (by omega)
                clear hc; m6b_split
                · have hinc0 : sp.core.inconsistent = 0#64 := by simpa using hc
                  have hp_ref : p.toNat ∈ fullArenaClauseRefs sp := hp_mem.resolve_left (by omega)
                  have hp_wf := hdp.2.1.arena.refs_wf p.toNat hp_ref
                  have har_len_p := hdp.1.core_ok.arena_len_arr
                  have har_le_p := hdp.1.core_ok.arena_len_le
                  have hp_arr0 : p.toNat < sp.core.arena.length := by omega
                  have hp_arr2 : (p + 2#64).toNat < sp.core.arena.length := by
                    rw [bv64_add_nat_lt 2 (by decide) (by omega)]; omega
                  have hp_32n : (p.setWidth 32).toNat = p.toNat := by
                    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                  clear hc; m6b_steps
                  refine LeanQbe.T.wp_call_of_spec _ _ (hNext _ _ _ _ ?_)
                  dsimp only [LeanQbe.T.vals_nil, LeanQbe.T.vals_cons,
                    LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm]
                  refine ⟨c, sp, R, rfl, hdp.1, hmp, ?_⟩
                  let np_nat := fullArenaNextOff sp.core.arena sp.core.arena_len p.toNat
                  have hnp_bds := fullArenaNextOff_bounds (ar := sp.core.arena)
                    (alen := sp.core.arena_len) (cref := p.toNat) hp_wf.1
                  let np := (BitVec.ofNat 32 (fullArenaNextOff sp.core.arena
                    sp.core.arena_len (p.setWidth 32).toNat)).setWidth 64
                  have hnp_n : np.toNat = np_nat := by
                    dsimp only [np, np_nat]
                    rw [hp_32n, bv_zext32_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                  have hnp_mem : np_nat = alen0 ∨ np_nat ∈ fullArenaClauseRefs sp := by
                    simpa only [np_nat, halp] using
                      fullArenaClauseRefs_next_or_end hdp.2.1 hp_ref
                  have hp2_n : (p + 2#64).toNat = p.toNat + 2 :=
                    bv64_add_nat_lt 2 (by decide) (by omega)
                  have hsz_eq : fullArenaClauseSizeCore sp.core p.toNat =
                      (sp.core.arena[(p + 2#64).toNat]'hp_arr2).toNat := by
                    unfold fullArenaClauseSizeCore
                    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                    exact congrArg BitVec.toNat (list_getElem_congr hp2_n.symm _ _)
                  m6b_split
                  · clear hc; m6b_let
                    exact ihp (np, ticks + 1#64, ()) mp
                      (by dsimp only; rw [hnp_n]; omega)
                      ⟨sp, by rw [hnp_n]; omega,
                       by rw [hnp_n]; exact hnp_mem,
                       hdp, hcvp, halp, hflp, hreprp, hmp⟩
                  · have h48_0 : ((sp.core.arena[p.toNat]'hp_arr0) &&& 0x00480000#32) = 0#32 := by
                      simpa using hc
                    clear hc; m6b_split
                    · clear hc; m6b_let
                      exact ihp (np, ticks + 1#64, ()) mp
                        (by dsimp only; rw [hnp_n]; omega)
                        ⟨sp, by rw [hnp_n]; omega,
                         by rw [hnp_n]; exact hnp_mem,
                         hdp, hcvp, halp, hflp, hreprp, hmp⟩
                    · let hdr := sp.core.arena[p.toNat]'hp_arr0
                      let sz := sp.core.arena[(p + 2#64).toNat]'hp_arr2
                      have hsz3 : 3 ≤ sz.toNat := by
                        have h := bv32_ult_not_lt hc
                        rw [show (3 : BitVec 32).toNat = 3 from rfl] at h
                        change ¬ sz.toNat < 3 at h; omega
                      have hng_p : fullArenaClauseGarb sp p.toNat = false := by
                        unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
                        rw [List.getElem?_eq_getElem hp_arr0, Option.getD_some]
                        exact m6_garb_false_of_and_48 h48_0
                      have hsz_cv : sz.toNat ≤ cv0 := by
                        rw [← hcvp, ← hsz_eq]
                        exact fullArenaClauseSize_le_cur_vars hdp.1 hdp.2.1 hdp.2.2.2.1 hp_ref hng_p
                      have hp_bd : p.toNat + 3 + sz.toNat ≤ alen0 := by
                        dsimp only [sz]
                        have h1 := hp_wf.2.2.1; have h2 := hp_wf.2.2.2.1; rw [hsz_eq] at h1; omega
                      have ⟨hb_p, hlm_p⟩ := m6FsBaseOk_of_dense hdp (hcvp ▸ hreprp)
                      have hb_p' : M6FsBaseOk c F0 F_cur cv0 alen0 fuel0 sp :=
                        hcvp ▸ halp ▸ hflp ▸ hb_p
                      clear hc; m6b_to_group
                      refine wp_join_group (ts := [.bool, .bool, .bool, .bool, i32, i32, i32, i32])
                        (fun (sat, taut, _c_mch, ovf, msz, min_l, _min_ld, _k, ()) mk =>
                          ∃ sk : FullState,
                            M6FsBaseOk c F0 F_cur cv0 alen0 fuel0 sk ∧
                            sk.core.arena = sp.core.arena ∧ sk.core.wvec = sp.core.wvec ∧
                            sk.core.wstk = sp.core.wstk ∧ sk.core.vals = sp.core.vals ∧
                            sk.core.min_clr = sp.core.min_clr ∧ sk.core.mrk = sp.core.mrk ∧
                            sk.core.inconsistent = 0#64 ∧
                            msz.toNat ≤ cv0 ∧
                            (min_l = 0xFFFFFFFF#32 ∨ min_l.toNat < 2 * cv0) ∧
                            (∀ j < msz.toNat, (sk.core.tmp[j]?.getD 0#32).toNat < 2 * cv0) ∧
                            (∀ l < 2 * c.max_vars, sk.core.lit_mark[l]?.getD 0#8 = 0#8 ∨
                              (∃ j < msz.toNat,
                                (sk.core.tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv0)) ∧
                            (sat = false → taut = false → ovf = false →
                              ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
                                ∀ j < sz.toNat,
                                  evalLitVal α (sk.core.arena[p.toNat + 3 + j]?.getD 0#32).toNat =
                                    true →
                                  ∃ q < msz.toNat,
                                    evalLitVal α (sk.core.tmp[q]?.getD 0#32).toNat = true) ∧
                            (FullMem c sk ⋆ R) mk)
                        ?_ ?_
                      · rintro _ ⟨sat, taut, c_mch, ovf, msz, min_l, min_ld, _k, ⟨⟩⟩ mk
                          ⟨sk, hbk, hark, hwvk, hwsk, hvlk, hmck, hmrkk, hinck,
                           hmsz_cv, hminl_ok, htmp_lt, hlm_ok, hsem_ok, hmk⟩
                        m6b_to_group
                        refine wp_loop_inv (ts := [i32])
                          (fun (kc, ()) mc => ∃ sc : FullState,
                            kc.toNat ≤ msz.toNat ∧
                            M6FsBaseOk c F0 F_cur cv0 alen0 fuel0 sc ∧
                            sc.core.arena = sp.core.arena ∧ sc.core.wvec = sp.core.wvec ∧
                            sc.core.wstk = sp.core.wstk ∧ sc.core.vals = sp.core.vals ∧
                            sc.core.tmp = sk.core.tmp ∧ sc.core.inconsistent = 0#64 ∧
                            (∀ l < 2 * c.max_vars, sc.core.lit_mark[l]?.getD 0#8 = 0#8 ∨
                              (∃ j, kc.toNat ≤ j ∧ j < msz.toNat ∧
                                (sc.core.tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv0)) ∧
                            (FullMem c sc ⋆ R) mc)
                          (fun (kc, ()) _ => msz.toNat - kc.toNat)
                          (fun Jc hJc => by
                            m6b_steps
                            exact hJc (0#32, ()) mk
                              ⟨sk, Nat.zero_le _, hbk, hark, hwvk, hwsk, hvlk, rfl, hinck,
                               m6Fs_lm_clear_from_zero hlm_ok, hmk⟩)
                          (fun Jc (kc, ()) mc
                              ⟨sc, hkc_le, hbc, harc, hwvc, hwsc, hvlc, htmpc, hincc,
                               hlmc, hmc⟩ ihc => ?_)
                        m6b_split
                        · have hkc_lt : kc.toNat < msz.toNat := bv32_ult_lt hc
                          have hkc1 : (kc + 1#32).toNat = kc.toNat + 1 := bv32_add1_lt_of (by omega)
                          have hkc_arr : kc.toNat < sc.core.tmp.length := by
                            have := hbc.1.core_ok.tmp_len_arr; omega
                          let rk := sc.core.tmp[kc.toNat]'hkc_arr
                          have hrk_lt : rk.toNat < 2 * cv0 := by
                            have h := htmp_lt kc.toNat hkc_lt
                            rw [← htmpc, List.getElem?_eq_getElem hkc_arr, Option.getD_some] at h
                            exact h
                          have hrk_arr : rk.toNat < sc.core.lit_mark.length := by
                            have := hbc.1.core_ok.lit_mark_len; omega
                          have hkc_z : (kc.setWidth 64).toNat = kc.toNat := bv_zext32_toNat kc
                          have hrk_z : ((sc.core.tmp[kc.toNat]'hkc_arr).setWidth 64).toNat =
                              rk.toNat := bv_zext32_toNat _
                          have hlmc' : ∀ l < 2 * c.max_vars,
                              (sc.core.lit_mark.set rk.toNat
                                (BitVec.ofNat 8 0))[l]?.getD 0#8 = 0#8 ∨
                                (∃ j, (kc + 1#32).toNat ≤ j ∧ j < msz.toNat ∧
                                  (sc.core.tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv0) := by
                            rw [hkc1]; intro l hl
                            rcases m6Fs_lm_clear_step hkc_lt hkc_arr hrk_arr hlmc l hl with
                              h0 | ⟨j, hj, hjl, hjt, hcvj⟩
                            · exact Or.inl h0
                            · exact Or.inr ⟨j, hj, hjl, hjt, hcvj⟩
                          have hlm_set_eq : sc.core.lit_mark.set
                              ((sc.core.tmp[(kc.setWidth 64).toNat]'(by
                                rw [hkc_z]; exact hkc_arr)).setWidth 64).toNat
                              (BitVec.ofNat 8 0) =
                              sc.core.lit_mark.set rk.toNat (BitVec.ofNat 8 0) :=
                            congrArg (sc.core.lit_mark.set · _) (by
                              rw [bv_zext32_toNat]
                              exact congrArg BitVec.toNat (list_getElem_congr hkc_z _ _))
                          clear hc; m6b_steps
                          let P_lm (lm : List (BitVec 8)) :=
                            (FullMem c { sc with core := { sc.core with lit_mark := lm } } ⋆ R) m
                          have hm_rk : P_lm (sc.core.lit_mark.set rk.toNat (BitVec.ofNat 8 0)) :=
                            (congrArg P_lm hlm_set_eq).mp hm
                          exact ihc (kc + 1#32, ()) m (by dsimp only; omega)
                            ⟨_, by rw [hkc1]; omega,
                             m6FsBaseOk_with_lm hbc
                               (lm' := sc.core.lit_mark.set rk.toNat (BitVec.ofNat 8 0))
                               (by simp [hbc.1.core_ok.lit_mark_len]),
                             harc, hwvc, hwsc, hvlc, htmpc, hincc, hlmc', hm_rk⟩
                        · have hkc_eq : kc.toNat = msz.toNat := by
                            have := bv32_ult_not_lt hc; omega
                          clear hc
                          have hlm_done : ∀ l < 2 * c.max_vars,
                              sc.core.lit_mark[l]?.getD 0#8 = 0#8 :=
                            m6Fs_lm_clear_done (hkc_eq ▸ hlmc)
                          obtain ⟨hdc, hcvc, halc, hflc, hreprc⟩ :=
                            m6FsBaseOk_to_dense hbc hlm_done
                          have hrefs_eq_sc : fullArenaClauseRefs sc = fullArenaClauseRefs sp := by
                            change fullArenaClauseRefsCore sc.core = fullArenaClauseRefsCore sp.core
                            unfold fullArenaClauseRefsCore; rw [harc, halc, ← halp]
                          have har_sc_sk : sc.core.arena = sk.core.arena := harc.trans hark.symm
                          have hp_ref_c : p.toNat ∈ fullArenaClauseRefs sc :=
                            hrefs_eq_sc ▸ hp_ref
                          have harc_p : p.toNat < sc.core.arena.length := by
                            rw [harc]; exact hp_arr0
                          have hhdr_c : sc.core.arena[p.toNat]'harc_p = hdr := by
                            dsimp only [hdr]; exact list_eq_getElem_congr harc _ _
                          m6b_to_group
                          refine wp_join_group (ts := [])
                            (fun () mm => mm = mc ∧ (sat = true ∨ taut = true))
                            (fun _ ⟨⟩ mm ⟨hmm, _⟩ => by
                              have hmm' : (FullMem c sc ⋆ R) mm := hmm ▸ hmc
                              m6b_steps
                              have hd_mg := m6_fs_markGarb_dense' hdc hp_ref_c harc_p
                                (sc.core.arena_garbage + 3#64 + sz.setWidth 64)
                              have hmg_refs := m6_fs_markGarb_refs hdc hp_ref_c harc_p
                                (sc.core.arena_garbage + 3#64 + sz.setWidth 64)
                              rw [hhdr_c] at hd_mg hmg_refs
                              exact ihp (np, ticks + 1#64, ()) m (by dsimp only; rw [hnp_n]; omega)
                                ⟨_, by rw [hnp_n, ← halp]; exact hnp_bds.2,
                                 (by rw [hnp_n]
                                     exact hnp_mem.elim Or.inl
                                       (fun h => Or.inr (hmg_refs ▸ hrefs_eq_sc ▸ h))),
                                 hd_mg, hcvc, halc, hflc, hreprc, hm⟩)
                            ?_
                          intro Jst hJst
                          m6b_split
                          · m6b_let; exact hJst () mc ⟨rfl, Or.inl hc⟩
                          · have hsat_f : sat = false := hc
                            clear hc; m6b_split
                            · m6b_let; exact hJst () mc ⟨rfl, Or.inr hc⟩
                            · have htaut_f : taut = false := hc
                              clear hc; m6b_split
                              · m6b_let
                                exact ihp (np, ticks + 1#64, ()) mc
                                  (by dsimp only; rw [hnp_n]; omega)
                                  ⟨sc, by rw [hnp_n]; omega,
                                   (by rw [hnp_n]
                                       exact hnp_mem.elim Or.inl
                                         (fun h => Or.inr (hrefs_eq_sc ▸ h))),
                                   hdc, hcvc, halc, hflc, hreprc, hmc⟩
                              · have hovf_f : ovf = false := hc
                                clear hc; m6b_split
                                · have hmsz0 : msz.toNat = 0 := by rw [beq_iff_eq.mp hc]; rfl
                                  have hng_c : fullArenaClauseGarb sc p.toNat = false := by
                                    unfold fullArenaClauseGarb fullArenaClauseGarbCore
                                      fullArenaHdrCore
                                    rw [List.getElem?_eq_getElem harc_p, Option.getD_some,
                                      hhdr_c]
                                    exact m6_garb_false_of_and_48 h48_0
                                  have hsz_c : fullArenaClauseSizeCore sc.core p.toNat =
                                      sz.toNat := by
                                    unfold fullArenaClauseSizeCore; rw [harc]
                                    rw [← hsz_eq]; rfl
                                  have hu_cur : (cnfOfClauses F_cur).Unsat :=
                                    m6Fs_msz0_unsat hdc.1 hdc.2.1 hp_ref_c hng_c hsz_c
                                      fun α hα j hj hl => by
                                        obtain ⟨q, hq, _⟩ :=
                                          hsem_ok hsat_f htaut_f hovf_f α hα j hj
                                            (har_sc_sk ▸ hl)
                                        omega
                                  clear hc; m6b_steps
                                  exact hQ 20#64 _ m
                                    (m6_denseInvW_with_inc hdc hu_cur 1#64)
                                    hcvc hflc (hcvc ▸ hreprc) (Or.inr rfl)
                                    (fun _ => hdc.2.1.ext_sound.2 hu_cur) hm
                                · have hmsz_ne0 : msz.toNat ≠ 0 := fun h =>
                                    (beq_eq_false_iff_ne.mp hc) (BitVec.eq_of_toNat_eq h)
                                  clear hc; m6b_split
                                  · have hmsz1 : msz.toNat = 1 := by rw [beq_iff_eq.mp hc]; rfl
                                    have h0_tmp : 0 < sc.core.tmp.length := by
                                      have := hdc.1.core_ok.tmp_len_arr; omega
                                    have hu0_lt : (sc.core.tmp[0]'h0_tmp).toNat < 2 * cv0 := by
                                      have h := htmp_lt 0 (by omega)
                                      rwa [← htmpc, List.getElem?_eq_getElem h0_tmp,
                                        Option.getD_some] at h
                                    have hng_c : fullArenaClauseGarb sc p.toNat = false := by
                                      unfold fullArenaClauseGarb fullArenaClauseGarbCore
                                        fullArenaHdrCore
                                      rw [List.getElem?_eq_getElem harc_p, Option.getD_some,
                                        hhdr_c]
                                      exact m6_garb_false_of_and_48 h48_0
                                    have hsz_c : fullArenaClauseSizeCore sc.core p.toNat =
                                        sz.toNat := by
                                      unfold fullArenaClauseSizeCore; rw [harc]
                                      rw [← hsz_eq]; rfl
                                    have hent_u : (cnfOfClauses F_cur).EntailsClause
                                        (cnfClause [(sc.core.tmp[0]'h0_tmp).toNat]) :=
                                      m6Fs_msz1_entails hdc.1 hdc.2.1 hp_ref_c hng_c hsz_c
                                        fun α hα j hj hl => by
                                          obtain ⟨q, hq, hqt⟩ :=
                                            hsem_ok hsat_f htaut_f hovf_f α hα j hj
                                              (har_sc_sk ▸ hl)
                                          have hq0 : q = 0 := by omega
                                          subst hq0
                                          rwa [← htmpc, List.getElem?_eq_getElem h0_tmp,
                                            Option.getD_some] at hqt
                                    clear hc; m6b_steps
                                    let sc_mg : FullState :=
                                      { sc with core :=
                                        { sc.core with
                                          arena := sc.core.arena.set p.toNat (hdr ||| 0x00080000#32)
                                          arena_garbage := sc.core.arena_garbage + 3#64 +
                                            sz.setWidth 64 } }
                                    have hd_mg : FullDenseInvW c F0 F_cur sc_mg := by
                                      simpa only [sc_mg, hhdr_c] using m6_fs_markGarb_dense' hdc
                                        hp_ref_c harc_p
                                        (sc.core.arena_garbage + 3#64 + sz.setWidth 64)
                                    m6b_call hAddUnit
                                    refine ⟨c, F0, F_cur, sc_mg, R, rfl, hd_mg.1, hd_mg.2.1,
                                      fun _ => by
                                        rw [list_getElem_congr
                                          (by decide : (BitVec.ofNat 64 0).toNat = 0) _ h0_tmp]
                                        exact hent_u,
                                      hm,
                                      fun ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass'
                                        unfl' inc' phases' ta' ba' pt' pb' hp' ps' hl' qsi' qss'
                                        mu hlu hwu hclu _h_unc h_f hmu => ?_⟩
                                    let su : FullState :=
                                      { sc_mg with
                                        core := { sc_mg.core with
                                          vals := vals', flags := flags', lvl := lvl',
                                          rsns := rsns', trl := trl', trail_pos := tp',
                                          trail_end := te', propagated := prop', cur_level := cl',
                                          unassigned := unass', unflushed := unfl',
                                          inconsistent := inc' }
                                        scratch := { sc_mg.scratch with
                                          phases := phases', target_assigned := ta',
                                          best_assigned := ba', phases_target := pt',
                                          phases_best := pb', heap := hp', pos := ps',
                                          heap_len := hl', q_search_idx := qsi',
                                          q_search_stamp := qss' } }
                                    have hdu := m6_addUnit_denseInvW hd_mg hlu hwu hclu rfl rfl rfl
                                      rfl rfl rfl rfl
                                    m6b_split
                                    · have hmg_refs := m6_fs_markGarb_refs hdc hp_ref_c harc_p
                                        (sc.core.arena_garbage + 3#64 + sz.setWidth 64)
                                      rw [hhdr_c] at hmg_refs
                                      have hnp_mem_u : np_nat = alen0 ∨
                                          np_nat ∈ fullArenaClauseRefs su := by
                                        change np_nat = alen0 ∨
                                          np_nat ∈ fullArenaClauseRefs sc_mg
                                        rw [hmg_refs]
                                        exact hnp_mem.elim Or.inl
                                          fun h => Or.inr (hrefs_eq_sc ▸ h)
                                      m6b_let
                                      exact ihp (np, ticks + 1#64, ()) mu
                                        (by dsimp only; rw [hnp_n]; omega)
                                        ⟨su, by rw [hnp_n, ← halp]; exact hnp_bds.2,
                                         by rw [hnp_n]; exact hnp_mem_u,
                                         hdu, hcvc, halc, hflc, hreprc, hmu⟩
                                    · have hu_f := h_f hc
                                      have hu0_eq : (sc.core.tmp[(BitVec.ofNat 64 0).toNat]'(by
                                          rw [bv64_ofNat_toNat_lt (by decide)]
                                          exact h0_tmp)).toNat =
                                          (sc.core.tmp[0]'h0_tmp).toNat :=
                                        congrArg BitVec.toNat (list_getElem_congr
                                          (by decide : (BitVec.ofNat 64 0).toNat = 0) _ h0_tmp)
                                      have hcv_su : su.core.cur_vars = cv0 := hcvc
                                      have hlt_su : (sc.core.tmp[(BitVec.ofNat 64 0).toNat]'(by
                                          rw [bv64_ofNat_toNat_lt (by decide)]
                                          exact h0_tmp)).toNat < 2 * su.core.cur_vars := by
                                        rw [hu0_eq, show su.core.cur_vars = cv0 from hcvc]
                                        exact hu0_lt
                                      have hu := (hu_f.resolve_left (Nat.not_le_of_lt hlt_su)).1
                                      m6b_steps
                                      exact hQ 20#64 su mu hdu hcvc hflc (hcvc ▸ hreprc)
                                        (Or.inr rfl) (fun _ => hu) hmu
                                  · have hmsz_ne1 : msz.toNat ≠ 1 := fun h =>
                                      (beq_eq_false_iff_ne.mp hc) (BitVec.eq_of_toNat_eq h)
                                    have hmsz_ge2 : 2 ≤ msz.toNat := by omega
                                    clear hc; m6b_split
                                    · have h0_tmp : 0 < sk.core.tmp.length := by
                                        have := hbk.1.core_ok.tmp_len_arr; omega
                                      have h0_tmp_c : 0 < sc.core.tmp.length := by
                                        rw [htmpc]; exact h0_tmp
                                      let min_r0 := sk.core.tmp[0]'h0_tmp
                                      have hmr0_lt : min_r0.toNat < 2 * cv0 := by
                                        have h := htmp_lt 0 (by omega)
                                        rwa [List.getElem?_eq_getElem h0_tmp, Option.getD_some] at h
                                      have hwv_len_c := hdc.1.core_ok.wvec_len
                                      have h0_tmpeq : (sc.core.tmp[(BitVec.ofNat 64 0).toNat]'(by
                                          rw [bv64_ofNat_toNat_lt (by decide)]
                                          exact h0_tmp_c)).toNat = min_r0.toNat := by
                                        rw [congrArg BitVec.toNat (list_getElem_congr
                                          (by decide : (BitVec.ofNat 64 0).toNat = 0) _ h0_tmp_c)]
                                        exact congrArg BitVec.toNat
                                          (list_eq_getElem_congr htmpc h0_tmp_c h0_tmp)
                                      have hmr0_wv_c : ((sc.core.tmp[(BitVec.ofNat 64 0).toNat]'(by
                                          rw [bv64_ofNat_toNat_lt (by decide)]
                                          exact h0_tmp_c)).setWidth 64 <<< 1#64 +
                                          1#64).toNat < sc.core.wvec.length := by
                                        have hz := bv_zext32_toNat
                                          (sc.core.tmp[(BitVec.ofNat 64 0).toNat]'(by
                                            rw [bv64_ofNat_toNat_lt (by decide)]; exact h0_tmp_c))
                                        have h2lt : 2 * min_r0.toNat < 2 ^ 64 := by
                                          have := min_r0.isLt; omega
                                        rw [BitVec.toNat_add, bv64_shl1_toNat, hz, h0_tmpeq,
                                          Nat.mod_eq_of_lt h2lt,
                                          show (1#64 : BitVec 64).toNat = 1 from rfl,
                                          Nat.mod_eq_of_lt (by omega)]
                                        omega
                                      clear hc; m6b_steps
                                      refine wp_loop_inv (ts := [i32, i32, i32])
                                        (fun (km, min_r, _min_rd, ()) mm1 => ∃ sm1 : FullState,
                                          km.toNat ≤ msz.toNat ∧
                                          min_r.toNat < 2 * cv0 ∧
                                          M6FsScanInv c F0 F_cur cv0 alen0 fuel0 sp sk msz.toNat
                                            sm1 ∧
                                          (FullMem c sm1 ⋆ R) mm1)
                                        (fun (km, _, _, ()) _ => msz.toNat - km.toNat)
                                        (fun Jm1 hJm1 => by
                                          m6b_steps
                                          exact hJm1 (0#32, _, _, ()) mc
                                            ⟨sc, Nat.zero_le _, by rw [h0_tmpeq]; exact hmr0_lt,
                                             ⟨hbc, harc, hwvc, hwsc, hvlc, htmpc, hincc,
                                              fun l hl => Or.inl (hlm_done l hl)⟩,
                                             hmc⟩)
                                        (fun Jm1 (km, min_r, min_rd, ()) mm1
                                            ⟨sm1, hkm_le, hmr_lt, hsm1, hmm1⟩ ihm1 => ?_)
                                      m6b_split
                                      · have hkm_lt : km.toNat < msz.toNat := bv32_ult_lt hc
                                        have hkm1 : (km + 1#32).toNat = km.toNat + 1 :=
                                          bv32_add1_lt_of (by omega)
                                        have hkm_arr : km.toNat < sm1.core.tmp.length := by
                                          have := hsm1.1.1.core_ok.tmp_len_arr; omega
                                        let rk := sm1.core.tmp[km.toNat]'hkm_arr
                                        have hrk_lt : rk.toNat < 2 * cv0 := by
                                          have h := htmp_lt km.toNat hkm_lt
                                          rwa [← hsm1.2.2.2.2.2.1,
                                            List.getElem?_eq_getElem hkm_arr,
                                            Option.getD_some] at h
                                        have hrk_lm : rk.toNat < sm1.core.lit_mark.length := by
                                          have := hsm1.1.1.core_ok.lit_mark_len; omega
                                        have hkm_z : (km.setWidth 64).toNat = km.toNat :=
                                          bv_zext32_toNat km
                                        have hkm_arr_bv :
                                            (km.setWidth 64).toNat < sm1.core.tmp.length := by
                                          rw [hkm_z]; exact hkm_arr
                                        have hrk_eq :
                                            sm1.core.tmp[(km.setWidth 64).toNat]'hkm_arr_bv =
                                              rk :=
                                          list_getElem_congr hkm_z hkm_arr_bv hkm_arr
                                        have hrk_z : (rk.setWidth 64).toNat = rk.toNat :=
                                          bv_zext32_toNat rk
                                        have hrk_z_bv :
                                            ((sm1.core.tmp[(km.setWidth 64).toNat]'hkm_arr_bv
                                              ).setWidth 64).toNat = rk.toNat := by
                                          rw [hrk_eq]; exact hrk_z
                                        have hrk_lm_bv :
                                            ((sm1.core.tmp[(km.setWidth 64).toNat]'hkm_arr_bv
                                              ).setWidth 64).toNat <
                                              sm1.core.lit_mark.length := by
                                          rw [hrk_z_bv]; exact hrk_lm
                                        have hrk_wv_bv :
                                            (((sm1.core.tmp[(km.setWidth 64).toNat]'hkm_arr_bv
                                              ).setWidth 64 <<< 1#64) + 1#64).toNat <
                                              sm1.core.wvec.length := by
                                          rw [hrk_eq]
                                          have hz := bv_zext32_toNat rk
                                          have h2rk : 2 * rk.toNat < 2 ^ 64 := by
                                            have := rk.isLt; omega
                                          rw [BitVec.toNat_add, bv64_shl1_toNat, hz,
                                            Nat.mod_eq_of_lt h2rk,
                                            show (1#64 : BitVec 64).toNat = 1 from rfl,
                                            Nat.mod_eq_of_lt (by omega)]
                                          have := hsm1.1.1.core_ok.wvec_len; omega
                                        clear hc; m6b_steps; rw [hrk_z_bv] at hm
                                        let sm2 : FullState :=
                                          { sm1 with core :=
                                            { sm1.core with
                                              lit_mark := sm1.core.lit_mark.set rk.toNat 1#8 } }
                                        have hsm2 : M6FsScanInv c F0 F_cur cv0 alen0 fuel0 sp sk
                                            msz.toNat sm2 :=
                                          ⟨m6FsBaseOk_with_lm hsm1.1
                                             (lm' := sm1.core.lit_mark.set rk.toNat 1#8)
                                             (by simp [hsm1.1.1.core_ok.lit_mark_len]),
                                           hsm1.2.1, hsm1.2.2.1, hsm1.2.2.2.1,
                                           hsm1.2.2.2.2.1, hsm1.2.2.2.2.2.1,
                                           hsm1.2.2.2.2.2.2.1,
                                           by simpa only [← hsm1.2.2.2.2.2.1] using
                                             m6Fs_lm_set_one (hsm1.2.2.2.2.2.1 ▸ htmp_lt)
                                               (hsm1.2.2.2.2.2.1 ▸ hsm1.2.2.2.2.2.2.2)
                                               hkm_lt hkm_arr hrk_lm⟩
                                        m6b_split
                                        · clear hc; m6b_steps; apply_assumption; m6b_steps
                                          exact ihm1 (km + 1#32, _, _, ()) m
                                            (by dsimp only; omega)
                                            ⟨sm2, by rw [hkm1]; omega, hrk_lt, hsm2, hm⟩
                                        · clear hc; m6b_steps; apply_assumption; m6b_steps
                                          exact ihm1 (km + 1#32, min_r, min_rd, ()) m
                                            (by dsimp only; omega)
                                            ⟨sm2, by rw [hkm1]; omega, hmr_lt, hsm2, hm⟩
                                      · clear hc; m6b_steps
                                        refine wp_loop_inv (ts := [i32, .bool])
                                          (fun (kb, subm, ()) mb => ∃ sb : FullState,
                                            kb.toNat ≤ msz.toNat ∧
                                            M6FsScanInv c F0 F_cur cv0 alen0 fuel0 sp sk msz.toNat
                                              sb ∧
                                            (FullMem c sb ⋆ R) mb)
                                          (fun (kb, subm, ()) _ =>
                                            if subm then 0 else msz.toNat - kb.toNat + 1)
                                          (fun Jb hJb => by
                                            m6b_let
                                            exact hJb (0#32, false, ()) mm1
                                              ⟨sm1, Nat.zero_le _, hsm1, hmm1⟩)
                                          (fun Jb (kb, subm, ()) mb
                                              ⟨sb, hkb_le, hsb, hmb⟩ ihb => ?_)
                                        m6b_to_group
                                        refine wp_join_group (ts := [])
                                          (fun () mp_pass => ∃ s_ps : FullState,
                                            M6FsScanInv c F0 F_cur cv0 alen0 fuel0 sp sk msz.toNat
                                              s_ps ∧
                                            (FullMem c s_ps ⋆ R) mp_pass)
                                          (fun _ ⟨⟩ m_ps ⟨s_ps, hsps, hmps⟩ => by
                                            m6b_to_group
                                            refine wp_join_group (ts := [i64, .bool, i32])
                                              (fun (tk_p, sub_p, _pass, ()) mclr_2 =>
                                                ∃ sc2 : FullState,
                                                  tk_p.toNat ≤ tick_lim.toNat + 1 ∧
                                                  M6FsScanInv c F0 F_cur cv0 alen0 fuel0 sp sk
                                                    msz.toNat sc2 ∧
                                                  (FullMem c sc2 ⋆ R) mclr_2)
                                              (fun _ ⟨tk_p, sub_p, _pass, ⟨⟩⟩ mclr_2
                                                  ⟨sc2, htkp_le, hsc2, hmc2⟩ => by
                                                m6b_to_group
                                                refine wp_loop_inv (ts := [i32])
                                                  (fun (k2, ()) mk2 => ∃ sk2 : FullState,
                                                    k2.toNat ≤ msz.toNat ∧
                                                    M6FsBaseOk c F0 F_cur cv0 alen0 fuel0 sk2 ∧
                                                    sk2.core.arena = sp.core.arena ∧
                                                    sk2.core.tmp = sk.core.tmp ∧
                                                    (∀ l < 2 * c.max_vars,
                                                      sk2.core.lit_mark[l]?.getD 0#8 = 0#8 ∨
                                                      (∃ j, k2.toNat ≤ j ∧ j < msz.toNat ∧
                                                        (sk2.core.tmp[j]?.getD 0#32).toNat = l ∧
                                                        l < 2 * cv0)) ∧
                                                    (FullMem c sk2 ⋆ R) mk2)
                                                  (fun (k2, ()) _ => msz.toNat - k2.toNat)
                                                  (fun Jc2 hJc2 => by
                                                    m6b_let
                                                    exact hJc2 (0#32, ()) mclr_2
                                                      ⟨sc2, Nat.zero_le _, hsc2.1, hsc2.2.1,
                                                       hsc2.2.2.2.2.2.1,
                                                       m6Fs_lm_clear_from_zero hsc2.2.2.2.2.2.2.2,
                                                       hmc2⟩)
                                                  (fun Jc2 (k2, ()) mk2
                                                      ⟨sk2, hk2_le, hbk2, hark2, htmpk2,
                                                       hlmk2, hmk2⟩ ihc2 => ?_)
                                                m6b_split
                                                · have hk2_lt : k2.toNat < msz.toNat :=
                                                    bv32_ult_lt hc
                                                  have hk2_1 :
                                                      (k2 + 1#32).toNat = k2.toNat + 1 :=
                                                    bv32_add1_lt_of (by omega)
                                                  have hk2_arr :
                                                      k2.toNat < sk2.core.tmp.length := by
                                                    have := hbk2.1.core_ok.tmp_len_arr; omega
                                                  let rk := sk2.core.tmp[k2.toNat]'hk2_arr
                                                  have hrk_lt : rk.toNat < 2 * cv0 := by
                                                    have h := htmp_lt k2.toNat hk2_lt
                                                    rwa [← htmpk2, List.getElem?_eq_getElem hk2_arr,
                                                      Option.getD_some] at h
                                                  have hrk_lm :
                                                      rk.toNat < sk2.core.lit_mark.length := by
                                                    have := hbk2.1.core_ok.lit_mark_len; omega
                                                  have hk2_z : (k2.setWidth 64).toNat = k2.toNat :=
                                                    bv_zext32_toNat k2
                                                  have hk2_arr_bv :
                                                      (k2.setWidth 64).toNat <
                                                        sk2.core.tmp.length := by
                                                    rw [hk2_z]; exact hk2_arr
                                                  have hrk_eq :
                                                      sk2.core.tmp[(k2.setWidth 64).toNat]'
                                                        hk2_arr_bv = rk :=
                                                    list_getElem_congr hk2_z hk2_arr_bv hk2_arr
                                                  have hrk_z_bv :
                                                      ((sk2.core.tmp[(k2.setWidth 64).toNat]'
                                                        hk2_arr_bv).setWidth 64).toNat =
                                                        rk.toNat := by
                                                    rw [hrk_eq]; exact bv_zext32_toNat rk
                                                  clear hc; m6b_steps; rw [hrk_z_bv] at hm
                                                  exact ihc2 (k2 + 1#32, ()) m
                                                    (by dsimp only; omega)
                                                    ⟨_, by rw [hk2_1]; omega,
                                                     m6FsBaseOk_with_lm hbk2
                                                       (lm' := sk2.core.lit_mark.set rk.toNat 0#8)
                                                       (by simp [hbk2.1.core_ok.lit_mark_len]),
                                                     hark2, htmpk2,
                                                     by rw [hk2_1]
                                                        exact m6Fs_lm_clear_step hk2_lt hk2_arr
                                                          hrk_lm hlmk2,
                                                     hm⟩
                                                · have hk2_eq : k2.toNat = msz.toNat := by
                                                    have := bv32_ult_not_lt hc; omega
                                                  have hlm_fin : ∀ l < 2 * c.max_vars,
                                                      sk2.core.lit_mark[l]?.getD 0#8 = 0#8 :=
                                                    m6Fs_lm_clear_done (hk2_eq ▸ hlmk2)
                                                  obtain ⟨hdk2, hcvk2, halk2, hflk2, hreprk2⟩ :=
                                                    m6FsBaseOk_to_dense hbk2 hlm_fin
                                                  have hrefs_eq_k2 :
                                                      fullArenaClauseRefs sk2 =
                                                        fullArenaClauseRefs sp := by
                                                    change fullArenaClauseRefsCore sk2.core =
                                                      fullArenaClauseRefsCore sp.core
                                                    unfold fullArenaClauseRefsCore
                                                    rw [hark2, halk2, ← halp]
                                                  clear hc; m6b_to_group
                                                  refine wp_join_group (ts := [])
                                                    (fun () m_mg => ∃ s_mg : FullState,
                                                      (np_nat = alen0 ∨
                                                        np_nat ∈ fullArenaClauseRefs s_mg) ∧
                                                      FullDenseInvW c F0 F_cur s_mg ∧
                                                      s_mg.core.cur_vars = cv0 ∧
                                                      s_mg.core.arena_len = alen0 ∧
                                                      s_mg.core.fuel = fuel0 ∧
                                                      FullCongReprInv F_cur (2 * cv0)
                                                        s_mg.core.repr ∧
                                                      (FullMem c s_mg ⋆ R) m_mg)
                                                    (fun _ ⟨⟩ m_mg ⟨s_mg, hmg_mem, hd_mg, hcv_mg,
                                                        hal_mg, hfl_mg, hrepr_mg, hm_mg⟩ => by
                                                      m6b_let
                                                      exact ihp (np, tk_p, ()) m_mg
                                                        (by dsimp only; rw [hnp_n]; omega)
                                                        ⟨s_mg,
                                                         by rw [hnp_n, ← halp]; exact hnp_bds.2,
                                                         by rw [hnp_n]; exact hmg_mem,
                                                         hd_mg, hcv_mg, hal_mg, hfl_mg, hrepr_mg,
                                                         hm_mg⟩)
                                                    ?_
                                                  intro J_mg hJ_mg
                                                  m6b_split
                                                  · have hp_ref2 :
                                                        p.toNat ∈ fullArenaClauseRefs sk2 :=
                                                      hrefs_eq_k2 ▸ hp_ref
                                                    have har_k2p :
                                                        p.toNat < sk2.core.arena.length := by
                                                      rw [hark2]; exact hp_arr0
                                                    have hhdr_k2 :
                                                        sk2.core.arena[p.toNat]'har_k2p = hdr := by
                                                      dsimp only [hdr]
                                                      exact list_eq_getElem_congr hark2 _ _
                                                    clear hc; m6b_steps
                                                    have hd_mg2 := m6_fs_markGarb_dense' hdk2
                                                      hp_ref2 har_k2p
                                                      (sk2.core.arena_garbage + 3#64 +
                                                        sz.setWidth 64)
                                                    have hmg2_refs := m6_fs_markGarb_refs hdk2
                                                      hp_ref2 har_k2p
                                                      (sk2.core.arena_garbage + 3#64 +
                                                        sz.setWidth 64)
                                                    rw [hhdr_k2] at hd_mg2 hmg2_refs
                                                    exact hJ_mg () m
                                                      ⟨_, hnp_mem.elim Or.inl fun h =>
                                                         Or.inr (hmg2_refs ▸ hrefs_eq_k2 ▸ h),
                                                       hd_mg2, hcvk2, halk2, hflk2, hreprk2, hm⟩
                                                  · clear hc; m6b_let
                                                    exact hJ_mg () mk2
                                                      ⟨sk2, hnp_mem.elim Or.inl fun h =>
                                                         Or.inr (hrefs_eq_k2 ▸ h),
                                                       hdk2, hcvk2, halk2, hflk2, hreprk2, hmk2⟩)
                                              ?_
                                            intro Jpx hJpx
                                            m6b_to_group
                                            refine wp_loop_inv (ts := [i64, .bool, i32])
                                              (fun (tk_p, sub_p, pass, ()) mlp => ∃ slp : FullState,
                                                pass.toNat ≤ 2 ∧ tk_p.toNat ≤ tick_lim.toNat + 1 ∧
                                                M6FsScanInv c F0 F_cur cv0 alen0 fuel0 sp sk
                                                  msz.toNat slp ∧
                                                (FullMem c slp ⋆ R) mlp)
                                              (fun (_, sub_p, pass, ()) _ =>
                                                if sub_p then 0 else 2 - pass.toNat + 1)
                                              (fun Jl_p hJl_p => by
                                                m6b_let
                                                exact hJl_p (ticks + 1#64, subm, 0#32, ()) m_ps
                                                  ⟨s_ps, by decide, by rw [htk1_n]; omega,
                                                   hsps, hmps⟩)
                                              (fun Jl_p (tk_p, sub_p, pass, ()) mlp
                                                  ⟨slp, hps_le, htkp_le, hslp, hmlp⟩ ihlp => ?_)
                                            m6b_split
                                            · have hps_lt : pass.toNat < 2 := bv32_ult_lt hc
                                              have hps1 : (pass + 1#32).toNat = pass.toNat + 1 :=
                                                bv32_add1_lt_of (by omega)
                                              clear hc; m6b_split
                                              · m6b_let
                                                exact hJpx (tk_p, sub_p, pass, ()) mlp
                                                  ⟨slp, htkp_le, hslp, hmlp⟩
                                              · have hsubp_f : sub_p = false := hc
                                                clear hc; m6b_to_group
                                                refine wp_join_group (ts := [i32])
                                                  (fun (wl, ()) mwl => mwl = mlp ∧
                                                    (wl = 0xFFFFFFFF#32 ∨ wl.toNat < 2 * cv0))
                                                  ?_
                                                  (fun Jwl_ch hJwl_ch => by
                                                    m6b_split
                                                    · m6b_let; exact hJwl_ch (min_r, ()) mlp
                                                        ⟨rfl, Or.inr hmr_lt⟩
                                                    · m6b_let; exact hJwl_ch (min_l, ()) mlp
                                                        ⟨rfl, hminl_ok⟩)
                                                rintro _ ⟨wl, ⟨⟩⟩ mwl ⟨hmwl, hwl_ok⟩
                                                m6b_to_group
                                                refine wp_join_group (ts := [])
                                                  (fun () mbp => mbp = mlp ∧
                                                    ¬ (pass = 1#32 ∧ min_l = min_r))
                                                  ?_
                                                  (fun Jbp hJbp => by
                                                    m6b_split
                                                    · clear hc; m6b_split
                                                      · m6b_let
                                                        exact hJpx (tk_p, sub_p, pass, ()) mwl
                                                          ⟨slp, htkp_le, hslp, hmwl ▸ hmlp⟩
                                                      · m6b_let; exact hJbp () mwl
                                                          ⟨hmwl, fun h =>
                                                            absurd h.2 (beq_eq_false_iff_ne.mp hc)⟩
                                                    · m6b_let; exact hJbp () mwl
                                                        ⟨hmwl, fun h =>
                                                          absurd h.1 (beq_eq_false_iff_ne.mp hc)⟩)
                                                rintro _ ⟨⟩ mbp ⟨hmbp, _⟩
                                                have hmbp' : (FullMem c slp ⋆ R) mbp := hmbp ▸ hmlp
                                                m6b_to_group
                                                refine wp_join_group (ts := [i64, .bool])
                                                  (fun (tk', sub', ()) mwp => ∃ swp : FullState,
                                                    tk'.toNat ≤ tick_lim.toNat + 1 ∧
                                                    M6FsScanInv c F0 F_cur cv0 alen0 fuel0 sp sk
                                                      msz.toNat swp ∧
                                                    (FullMem c swp ⋆ R) mwp)
                                                  (fun _ ⟨tk', sub', ⟨⟩⟩ mwp
                                                      ⟨swp, htk'_le, hswp, hmw⟩ => by
                                                    m6b_steps
                                                    exact ihlp (tk', sub', pass + 1#32, ()) mwp
                                                      (by dsimp only; rw [hsubp_f, hps1]
                                                          cases sub'
                                                          · rw [ite_eq_right Bool.false_ne_true,
                                                              ite_eq_right Bool.false_ne_true]
                                                            omega
                                                          · rw [ite_eq_left rfl,
                                                              ite_eq_right Bool.false_ne_true]
                                                            omega)
                                                      ⟨swp, by rw [hps1]; omega, htk'_le,
                                                       hswp, hmw⟩)
                                                  ?_
                                                intro Jwl hJwl
                                                m6b_split
                                                · have hwl_lt : wl.toNat < 2 * cv0 := by
                                                    rcases hwl_ok with heq | hlt
                                                    · exact absurd heq (bne_iff_ne.mp hc)
                                                    · exact hlt
                                                  have hcv_slp : slp.core.cur_vars = cv0 :=
                                                    hslp.1.2.2.2.2.2.2.2.1
                                                  have hwa_slp := hslp.1.1.core_ok.wstk_len_arr
                                                  have hwa_sp : sp.core.wstk.length = c.wcap := by
                                                    rw [← hslp.2.2.2.1]; exact hwa_slp
                                                  have hwb := m6_denseWatchBounds hslp.1.1.core_ok
                                                    hslp.1.2.1 hslp.1.2.2.2.2.2.2.1
                                                    (by rw [hcv_slp]; exact hwl_lt)
                                                  obtain ⟨hwl_2_arr, hwl_21_arr⟩ :=
                                                    m6Fs_watch_2_arr hslp.1.1.core_ok hcv_slp
                                                      hwl_lt
                                                  let woff_bv :=
                                                    (slp.core.wvec[(wl.setWidth 64 <<<
                                                      1#64).toNat]'hwl_2_arr).setWidth 64
                                                  let wsz_bv :=
                                                    (slp.core.wvec[((wl.setWidth 64 <<<
                                                      1#64) + 1#64).toNat]'hwl_21_arr).setWidth 64
                                                  let wend_bv := woff_bv + wsz_bv
                                                  obtain ⟨hwoff_eq, hwsz_eq, hwend_n⟩ :=
                                                    m6Fs_watch_off_eq hslp.1.1.core_ok hcv_slp
                                                      hwl_lt hwl_2_arr hwl_21_arr
                                                  change woff_bv.toNat =
                                                    fullWatchOffCore slp.core wl.toNat at hwoff_eq
                                                  change wsz_bv.toNat =
                                                    fullWatchSizeCore slp.core wl.toNat at hwsz_eq
                                                  change wend_bv.toNat =
                                                    woff_bv.toNat + wsz_bv.toNat at hwend_n
                                                  have hsl0 : DenseWatchSliceOk F_cur slp.core
                                                      wl.toNat woff_bv.toNat
                                                      (wend_bv.toNat - woff_bv.toNat) := by
                                                    rw [hwend_n, Nat.add_sub_cancel_left,
                                                      hwoff_eq, hwsz_eq]
                                                    exact m6_denseWatchSlice_of_inv hslp.1.2.1
                                                      hslp.1.2.2.2.2.2.2.1
                                                      (by rw [hcv_slp]; exact hwl_lt)
                                                  clear hc; m6b_to_group
                                                  refine wp_join_group (ts := [i64, .bool, i64])
                                                    (fun (tk', sub', _wp', ()) mwp =>
                                                      ∃ swp : FullState,
                                                        tk'.toNat ≤ tick_lim.toNat + 1 ∧
                                                        M6FsScanInv c F0 F_cur cv0 alen0 fuel0 sp sk
                                                          msz.toNat swp ∧
                                                        (FullMem c swp ⋆ R) mwp)
                                                    (fun _ ⟨tk', sub', _, ⟨⟩⟩ mwp
                                                        ⟨swp, htk'_le, hswp, hmw⟩ => by
                                                      m6b_let
                                                      exact hJwl (tk', sub', ()) mwp
                                                        ⟨swp, htk'_le, hswp, hmw⟩)
                                                    ?_
                                                  intro Jwp_ex hJwp_ex
                                                  refine wp_loop_inv (ts := [i64, i64])
                                                    (fun (tk_w, wp, ()) mwi => ∃ swi : FullState,
                                                      wp.toNat ≤ wend_bv.toNat ∧
                                                      tk_w.toNat ≤ tick_lim.toNat + 1 ∧
                                                      M6FsScanInv c F0 F_cur cv0 alen0 fuel0 sp sk
                                                        msz.toNat swi ∧
                                                      DenseWatchSliceOk F_cur swi.core wl.toNat
                                                        wp.toNat (wend_bv.toNat - wp.toNat) ∧
                                                      (FullMem c swi ⋆ R) mwi)
                                                    (fun (_, wp, ()) _ => wend_bv.toNat - wp.toNat)
                                                    (fun Jw hJw => by
                                                      m6b_let
                                                      exact hJw (tk_p, woff_bv, ()) mbp
                                                        ⟨slp, by omega, htkp_le, hslp, hsl0,
                                                         hmbp'⟩)
                                                    (fun Jw (tk_w, wp, ()) mwi
                                                        ⟨swi, hwp_le, htkw_le, hswi, hslw,
                                                         hmwi⟩ ihw => ?_)
                                                  m6b_split
                                                  · have hwp_lt : wp.toNat < wend_bv.toNat :=
                                                      bv64_ult_lt hc
                                                    clear hc; m6b_split
                                                    · have htkw_lt :
                                                          tk_w.toNat < tick_lim.toNat :=
                                                        bv64_ult_lt hc
                                                      have htkw1 :
                                                          (tk_w + 1#64).toNat = tk_w.toNat + 1 :=
                                                        bv64_add1_lt (by omega)
                                                      obtain ⟨w0, hwp_g, hs_step⟩ :=
                                                        m6_dense_slice_step hslw (by omega)
                                                      have hwp_arr :
                                                          wp.toNat < swi.core.wstk.length := by
                                                        rw [hswi.2.2.2.1, hwa_sp]; omega
                                                      have hw0_eq :
                                                          swi.core.wstk[wp.toNat]'hwp_arr = w0 := by
                                                        rw [List.getElem?_eq_getElem
                                                          hwp_arr] at hwp_g
                                                        exact Option.some.inj hwp_g
                                                      have hwp1_n :
                                                          (wp + 1#64).toNat = wp.toNat + 1 :=
                                                        bv64_add1_lt (by omega)
                                                      clear hc; m6b_split
                                                      · rcases hs_step with
                                                          ⟨hf, hrest⟩ | ⟨hf, _⟩
                                                        · m6b_let
                                                          exact ihw (tk_w, wp + 1#64, ()) mwi
                                                            (by dsimp only; rw [hwp1_n]; omega)
                                                            ⟨swi, by rw [hwp1_n]; omega, htkw_le,
                                                             hswi,
                                                             by rw [hwp1_n,
                                                                  show wend_bv.toNat -
                                                                    (wp.toNat + 1) =
                                                                    wend_bv.toNat - wp.toNat - 1
                                                                    by omega]
                                                                exact hrest,
                                                             hmwi⟩
                                                        · have hne :
                                                              (w0 &&& 0x80000000#32) ≠ 0#32 := by
                                                            change (((swi.core.wstk[wp.toNat]'
                                                              hwp_arr) &&& 0x80000000#32 !=
                                                              0#32, ()).fst) = true at hc
                                                            rw [hw0_eq] at hc
                                                            exact bv32_and_msb_ne0 hc
                                                          exact absurd hf hne
                                                      · rcases hs_step with
                                                          ⟨hf, _⟩ |
                                                          ⟨hf, hrem2, cr, hcr_g, hcr_ref, hrest⟩
                                                        · have heq :
                                                              (w0 &&& 0x80000000#32) = 0#32 := by
                                                            change (((swi.core.wstk[wp.toNat]'
                                                              hwp_arr) &&& 0x80000000#32 !=
                                                              0#32, ()).fst) = false at hc
                                                            rw [hw0_eq] at hc
                                                            exact bv32_and_msb_eq0 hc
                                                          exact absurd heq hf
                                                        · have hwp1_arr :
                                                              (wp + 1#64).toNat <
                                                                swi.core.wstk.length := by
                                                            rw [hswi.2.2.2.1, hwa_sp]; omega
                                                          have hwp1_arr' :
                                                              wp.toNat + 1 <
                                                                swi.core.wstk.length := by
                                                            rw [← hwp1_n]; exact hwp1_arr
                                                          have hcr_eq :
                                                              swi.core.wstk[(wp + 1#64).toNat]'
                                                                hwp1_arr = cr := by
                                                            rw [List.getElem?_eq_getElem
                                                              hwp1_arr'] at hcr_g
                                                            exact (list_getElem_congr hwp1_n
                                                              hwp1_arr hwp1_arr').trans
                                                              (Option.some.inj hcr_g)
                                                          have hcr_rw0 : ∀ h,
                                                              swi.core.wstk[(wp + 1#64).toNat]'h =
                                                                cr := fun _ => hcr_eq
                                                          have hcr_rw1 : ∀ h,
                                                              swi.core.wstk[(wp + 1).toNat]'h =
                                                                cr := fun _ => hcr_eq
                                                          have hwp2_n :
                                                              (wp + 1#64 + 1#64).toNat =
                                                                wp.toNat + 2 := by
                                                            rw [BitVec.toNat_add, hwp1_n,
                                                              show (1#64 : BitVec 64).toNat = 1
                                                                from rfl,
                                                              Nat.mod_eq_of_lt (by omega)]
                                                          clear hc; m6b_split
                                                          · m6b_let
                                                            exact hJwp_ex
                                                              (tk_w, sub_p, wp + 1#64, ())
                                                              mwi ⟨swi, by omega, hswi, hmwi⟩
                                                          · have hcr_wf :=
                                                              hswi.1.2.1.arena.refs_wf cr.toNat
                                                                hcr_ref
                                                            obtain ⟨har_cr, har_cr2, hcr2_n⟩ :=
                                                              m6Fs_scan_cr_ar hswi hcr_wf
                                                            let dhdr :=
                                                              swi.core.arena[cr.toNat]'har_cr
                                                            let dsz :=
                                                              swi.core.arena[(cr.setWidth 64 +
                                                                2#64).toNat]'har_cr2
                                                            have hcr_sp :
                                                                cr.toNat ∈
                                                                  fullArenaClauseRefsCore
                                                                    sp.core := by
                                                              unfold fullArenaClauseRefsCore
                                                              rw [← hswi.2.1, halp,
                                                                ← hswi.1.2.2.2.2.2.2.2.2.1]
                                                              exact hcr_ref
                                                            clear hc
                                                            m6b_split
                                                            · m6b_let
                                                              exact ihw (tk_w + 1#64,
                                                                wp + 1#64 + 1#64, ()) mwi
                                                                (by dsimp only; rw [hwp2_n]; omega)
                                                                ⟨swi, by rw [hwp2_n]; omega,
                                                                 by rw [htkw1]; omega, hswi,
                                                                 by rw [hwp2_n,
                                                                      show wend_bv.toNat -
                                                                        (wp.toNat + 2) =
                                                                        wend_bv.toNat - wp.toNat - 2
                                                                        by omega]
                                                                    exact hrest,
                                                                 hmwi⟩
                                                            · clear hc
                                                              repeat rw [hcr_rw1]
                                                              repeat rw [hcr_rw0]
                                                              m6b_split
                                                              · m6b_let
                                                                exact ihw (tk_w + 1#64,
                                                                  wp + 1#64 + 1#64, ()) mwi
                                                                  (by
                                                                    dsimp only
                                                                    rw [hwp2_n]
                                                                    omega)
                                                                  ⟨swi, by rw [hwp2_n]; omega,
                                                                   by rw [htkw1]; omega, hswi,
                                                                   by rw [hwp2_n,
                                                                        show wend_bv.toNat -
                                                                          (wp.toNat + 2) =
                                                                          wend_bv.toNat - wp.toNat -
                                                                          2 by omega]
                                                                      exact hrest,
                                                                   hmwi⟩
                                                              · have h48d :
                                                                    (dhdr &&& 0x00480000#32) =
                                                                      0#32 := by
                                                                  dsimp only [dhdr]
                                                                  change (((swi.core.arena[
                                                                    cr.toNat]'har_cr) &&&
                                                                    (524288#32 ||| 4194304#32) !=
                                                                    0#32, ()).fst) = false at hc
                                                                  exact bv32_and_48_eq0 hc
                                                                have hng_sp :
                                                                    fullArenaClauseGarbCore
                                                                      sp.core cr.toNat = false := by
                                                                  unfold fullArenaClauseGarbCore
                                                                    fullArenaHdrCore
                                                                  rw [← hswi.2.1,
                                                                    List.getElem?_eq_getElem har_cr,
                                                                    Option.getD_some]
                                                                  exact m6_garb_false_of_and_48 h48d
                                                                have hdsz_sp :
                                                                    fullArenaClauseSizeCore
                                                                      sp.core cr.toNat =
                                                                      dsz.toNat := by
                                                                  unfold fullArenaClauseSizeCore
                                                                  rw [← hswi.2.1]; dsimp only [dsz]
                                                                  have har_cr2' : cr.toNat + 2 <
                                                                      swi.core.arena.length :=
                                                                    hcr2_n ▸ har_cr2
                                                                  rw [List.getElem?_eq_getElem
                                                                    har_cr2', Option.getD_some]
                                                                  exact congrArg BitVec.toNat
                                                                    (list_getElem_congr hcr2_n.symm
                                                                      har_cr2' har_cr2)
                                                                clear hc; m6b_split
                                                                · m6b_let
                                                                  exact ihw (tk_w + 1#64,
                                                                    wp + 1#64 + 1#64, ()) mwi
                                                                    (by dsimp only; rw [hwp2_n]
                                                                        omega)
                                                                    ⟨swi, by rw [hwp2_n]; omega,
                                                                     by rw [htkw1]; omega, hswi,
                                                                     by rw [hwp2_n,
                                                                          show wend_bv.toNat -
                                                                            (wp.toNat + 2) =
                                                                            wend_bv.toNat - wp.toNat
                                                                            - 2 by omega]
                                                                        exact hrest,
                                                                     hmwi⟩
                                                                · clear hc; m6b_to_group
                                                                  refine wp_join_group (ts := [])
                                                                    (fun () m_dok =>
                                                                      ∃ sd : FullState,
                                                                        M6FsScanInv c F0 F_cur cv0
                                                                          alen0 fuel0 sp sk
                                                                          msz.toNat sd ∧
                                                                        DenseWatchSliceOk F_cur
                                                                          sd.core wl.toNat
                                                                          (wp.toNat + 2)
                                                                          (wend_bv.toNat -
                                                                            wp.toNat - 2) ∧
                                                                        (FullMem c sd ⋆ R) m_dok)
                                                                    ?_
                                                                    (fun Jflt hJflt => by
                                                                      m6b_split
                                                                      · clear hc; m6b_split
                                                                        · m6b_let
                                                                          exact ihw (tk_w + 1#64,
                                                                            wp + 1#64 + 1#64, ())
                                                                            mwi
                                                                            (by dsimp only
                                                                                rw [hwp2_n]; omega)
                                                                            ⟨swi,
                                                                             by rw [hwp2_n]; omega,
                                                                             by rw [htkw1]; omega,
                                                                             hswi,
                                                                             by rw [hwp2_n,
                                                                                  show wend_bv.toNat
                                                                                    - (wp.toNat + 2)
                                                                                    = wend_bv.toNat
                                                                                    - wp.toNat - 2
                                                                                    by omega]
                                                                                exact hrest,
                                                                             hmwi⟩
                                                                        · m6b_let
                                                                          exact hJflt () mwi
                                                                            ⟨swi, hswi, hrest,
                                                                             hmwi⟩
                                                                      · m6b_let
                                                                        exact hJflt () mwi
                                                                          ⟨swi, hswi, hrest,
                                                                           hmwi⟩)
                                                                  rintro _ ⟨⟩ m_dok
                                                                    ⟨swd0, hswd0, hsld0, hmdok⟩
                                                                  m6b_to_group
                                                                  refine wp_join_group
                                                                    (ts := [.bool, i32])
                                                                    (fun (dok, _dj, ()) mdj =>
                                                                      ∃ sd : FullState,
                                                                        M6FsScanInv c F0 F_cur cv0
                                                                          alen0 fuel0 sp sk
                                                                          msz.toNat sd ∧
                                                                        DenseWatchSliceOk F_cur
                                                                          sd.core wl.toNat
                                                                          (wp.toNat + 2)
                                                                          (wend_bv.toNat -
                                                                            wp.toNat - 2) ∧
                                                                        (FullMem c sd ⋆ R) mdj)
                                                                    (fun _ ⟨dok, _, ⟨⟩⟩ mdj
                                                                        ⟨sd, hsd, hsld, hmd⟩ => by
                                                                      m6b_split
                                                                      · m6b_steps
                                                                        exact hJwp_ex (tk_w + 1#64,
                                                                          true,
                                                                          wp + 1#64 + 1#64, ())
                                                                          mdj ⟨sd,
                                                                            by rw [htkw1]; omega,
                                                                            hsd, hmd⟩
                                                                      · m6b_let
                                                                        exact ihw (tk_w + 1#64,
                                                                          wp + 1#64 + 1#64, ()) mdj
                                                                          (by dsimp only
                                                                              rw [hwp2_n]; omega)
                                                                          ⟨sd,
                                                                           by rw [hwp2_n]; omega,
                                                                           by rw [htkw1]; omega,
                                                                           hsd,
                                                                           by rw [hwp2_n]
                                                                              exact hsld,
                                                                           hmd⟩)
                                                                    ?_
                                                                  intro Jdj_br hJdj_br
                                                                  refine wp_loop_inv (ts := [i32])
                                                                    (fun (dj, ()) md =>
                                                                      ∃ sd : FullState,
                                                                        dj.toNat ≤ dsz.toNat ∧
                                                                        M6FsScanInv c F0 F_cur cv0
                                                                          alen0 fuel0 sp sk
                                                                          msz.toNat sd ∧
                                                                        DenseWatchSliceOk F_cur
                                                                          sd.core wl.toNat
                                                                          (wp.toNat + 2)
                                                                          (wend_bv.toNat -
                                                                            wp.toNat - 2) ∧
                                                                        (FullMem c sd ⋆ R) md)
                                                                    (fun (dj, ()) _ =>
                                                                      dsz.toNat - dj.toNat)
                                                                    (fun Jd hJd => by
                                                                      m6b_let
                                                                      exact hJd (0#32, ()) m_dok
                                                                        ⟨swd0, Nat.zero_le _, hswd0,
                                                                         hsld0, hmdok⟩)
                                                                    (fun Jd (dj, ()) md
                                                                        ⟨sd, hdj_le, hsd, hsld,
                                                                         hmd⟩ ihd => ?_)
                                                                  m6b_split
                                                                  · have hdj_lt :
                                                                        dj.toNat < dsz.toNat :=
                                                                      bv32_ult_lt hc
                                                                    have hdj1 :
                                                                        (dj + 1#32).toNat =
                                                                          dj.toNat + 1 :=
                                                                      bv32_add1_lt_of (by omega)
                                                                    obtain ⟨hol_arr, hol_lt⟩ :=
                                                                      m6Fs_cr_lit_lt hsd halp
                                                                        hcr_sp hng_sp hdsz_sp hdj_lt
                                                                    let ol :=
                                                                      sd.core.arena[(cr.setWidth 64
                                                                        + 3#64 + dj.setWidth 64
                                                                        ).toNat]'hol_arr
                                                                    have hol_vl :
                                                                        ol.toNat <
                                                                          sd.core.vals.length :=
                                                                      m6Fs_scan_vals_lt hsd hol_lt
                                                                    clear hc; m6b_split
                                                                    · m6b_let
                                                                      exact hJdj_br (false, dj, ())
                                                                        md ⟨sd, hsd, hsld, hmd⟩
                                                                    · clear hc; m6b_to_group
                                                                      refine wp_join_group
                                                                        (ts := [.bool])
                                                                        (fun (_dok', ()) m1 =>
                                                                          ∃ sd1 : FullState,
                                                                            M6FsScanInv c F0 F_cur
                                                                              cv0 alen0 fuel0 sp sk
                                                                              msz.toNat sd1 ∧
                                                                            DenseWatchSliceOk F_cur
                                                                              sd1.core wl.toNat
                                                                              (wp.toNat + 2)
                                                                              (wend_bv.toNat -
                                                                                wp.toNat - 2) ∧
                                                                            (FullMem c sd1 ⋆ R) m1)
                                                                        (fun _ _ m1
                                                                            ⟨sd1, hsd1, hsld1,
                                                                             hm1⟩ => by
                                                                          m6b_steps
                                                                          exact ihd (dj + 1#32, ())
                                                                            m1 (by dsimp only
                                                                                   rw [hdj1]
                                                                                   omega)
                                                                            ⟨sd1,
                                                                             by rw [hdj1]; omega,
                                                                             hsd1, hsld1, hm1⟩)
                                                                        ?_
                                                                      intro Jdok1 hJdok1
                                                                      m6b_split
                                                                      · clear hc; m6b_steps
                                                                        m6b_call hFind
                                                                        refine ⟨F_cur, 2 * cv0,
                                                                          sd.core.repr,
                                                                          FullReprRest c sd ⋆ R,
                                                                          hsd.1.2.2.2.2.2.2.2.2.2.2,
                                                                          hol_lt,
                                                                          focus_full_repr hmd,
                                                                          fun ro repr_o mo hrl_o
                                                                            hrepr_o _ hro_lt _
                                                                            hmo => ?_⟩
                                                                        let sd1 : FullState :=
                                                                          { sd with core :=
                                                                            { sd.core with
                                                                              repr := repr_o } }
                                                                        have hmo' :
                                                                            (FullMem c sd1 ⋆ R) mo
                                                                          := unfocus_full_repr hmo
                                                                        have hrl_sd :=
                                                                          hsd.1.1.core_ok.repr_len
                                                                        have hsd1 :=
                                                                          m6FsScanInv_with_repr hsd
                                                                            (hrl_o.trans hrl_sd)
                                                                            hrepr_o
                                                                        have hsld1 :=
                                                                          m6DwsRepr hsld repr_o
                                                                        have hro_vl :=
                                                                          m6Fs_scan_vals_lt
                                                                            hsd1 hro_lt
                                                                        have hro_lm :=
                                                                          m6Fs_scan_lm_lt
                                                                            hsd1 hro_lt
                                                                        m6b_split
                                                                        · m6b_let
                                                                          exact hJdj_br
                                                                            (false, dj, ()) mo
                                                                            ⟨sd1, hsd1, hsld1,
                                                                             hmo'⟩
                                                                        · clear hc; m6b_split
                                                                          · clear hc; m6b_split
                                                                            · m6b_let
                                                                              exact hJdj_br
                                                                                (false, dj, ()) mo
                                                                                ⟨sd1, hsd1, hsld1,
                                                                                 hmo'⟩
                                                                            · m6b_let
                                                                              exact hJdok1
                                                                                (true, ()) mo
                                                                                ⟨sd1, hsd1, hsld1,
                                                                                 hmo'⟩
                                                                          · m6b_let
                                                                            exact hJdok1 (true, ())
                                                                              mo ⟨sd1, hsd1, hsld1,
                                                                                hmo'⟩
                                                                      · m6b_let
                                                                        exact hJdok1 (true, ()) md
                                                                          ⟨sd, hsd, hsld, hmd⟩
                                                                  · m6b_let
                                                                    exact hJdj_br (true, dj, ()) md
                                                                      ⟨sd, hsd, hsld, hmd⟩
                                                    · m6b_let
                                                      exact hJwp_ex (tk_w, sub_p, wp, ()) mwi
                                                        ⟨swi, htkw_le, hswi, hmwi⟩
                                                  · m6b_let
                                                    exact hJwp_ex (tk_w, sub_p, wp, ()) mwi
                                                      ⟨swi, htkw_le, hswi, hmwi⟩
                                                · m6b_let
                                                  exact hJwl (tk_p, sub_p, ()) mbp
                                                    ⟨slp, htkp_le, hslp, hmbp'⟩
                                            · m6b_let
                                              exact hJpx (tk_p, sub_p, pass, ()) mlp
                                                ⟨slp, htkp_le, hslp, hmlp⟩)
                                          ?_
                                        intro Jb_ex hJb_ex
                                        m6b_split
                                        · have hkb_lt : kb.toNat < msz.toNat := bv32_ult_lt hc
                                          have hkb1 : (kb + 1#32).toNat = kb.toNat + 1 :=
                                            bv32_add1_lt_of (by omega)
                                          clear hc; m6b_split
                                          · m6b_let; exact hJb_ex () mb ⟨sb, hsb, hmb⟩
                                          · have hsubm : subm = false := hc
                                            have hkb_arr : kb.toNat < sb.core.tmp.length := by
                                              have := hsb.1.1.core_ok.tmp_len_arr; omega
                                            let rk := sb.core.tmp[kb.toNat]'hkb_arr
                                            have hrk_lt : rk.toNat < 2 * cv0 := by
                                              have h := htmp_lt kb.toNat hkb_lt
                                              rwa [← hsb.2.2.2.2.2.1,
                                                List.getElem?_eq_getElem hkb_arr,
                                                Option.getD_some] at h
                                            obtain ⟨hrk_wv, hrk_wv1⟩ :=
                                              m6Fs_watch_2_arr hsb.1.1.core_ok
                                                hsb.1.2.2.2.2.2.2.2.1 hrk_lt
                                            have hwb := m6_denseWatchBounds hsb.1.1.core_ok
                                              hsb.1.2.1 hsb.1.2.2.2.2.2.2.1
                                              (by rw [hsb.1.2.2.2.2.2.2.2.1]; exact hrk_lt)
                                            let boff_bv :=
                                              (sb.core.wvec[(rk.setWidth 64 <<<
                                                1#64).toNat]'hrk_wv).setWidth 64
                                            let bsz_bv :=
                                              (sb.core.wvec[((rk.setWidth 64 <<< 1#64) +
                                                1#64).toNat]'hrk_wv1).setWidth 64
                                            let bend_bv := boff_bv + bsz_bv
                                            obtain ⟨hboff_eq, hbsz_eq, hbend_n⟩ :=
                                              m6Fs_watch_off_eq hsb.1.1.core_ok
                                                hsb.1.2.2.2.2.2.2.2.1 hrk_lt hrk_wv hrk_wv1
                                            change boff_bv.toNat =
                                              fullWatchOffCore sb.core rk.toNat at hboff_eq
                                            change bsz_bv.toNat =
                                              fullWatchSizeCore sb.core rk.toNat at hbsz_eq
                                            change bend_bv.toNat =
                                              boff_bv.toNat + bsz_bv.toNat at hbend_n
                                            clear hc; m6b_to_group
                                            refine wp_join_group (ts := [.bool, i64])
                                              (fun (subm', _bp', ()) m1 => ∃ sb1 : FullState,
                                                M6FsScanInv c F0 F_cur cv0 alen0 fuel0 sp sk
                                                  msz.toNat sb1 ∧
                                                (FullMem c sb1 ⋆ R) m1)
                                              (fun _ ⟨subm', _, ⟨⟩⟩ m1 ⟨sb1, hsb1, hm1⟩ => by
                                                m6b_steps
                                                exact ihb (kb + 1#32, subm', ()) m1
                                                  (by dsimp only; rw [hkb1, hsubm]
                                                      cases subm'
                                                      · rw [ite_eq_right Bool.false_ne_true,
                                                          ite_eq_right Bool.false_ne_true]
                                                        omega
                                                      · rw [ite_eq_left rfl,
                                                          ite_eq_right Bool.false_ne_true]
                                                        omega)
                                                  ⟨sb1, by rw [hkb1]; omega, hsb1, hm1⟩)
                                              ?_
                                            intro Jbp_ex hJbp_ex
                                            have hbd_cap : bend_bv.toNat ≤ c.wcap := by
                                              have := hsb.1.1.core_ok.wstk_len_arr
                                              rw [hbend_n, hboff_eq, hbsz_eq]; omega
                                            refine wp_loop_inv (ts := [i64])
                                              (fun (bp, ()) m1 => ∃ sb1 : FullState,
                                                bp.toNat ≤ bend_bv.toNat + 1 ∧
                                                M6FsScanInv c F0 F_cur cv0 alen0 fuel0 sp sk
                                                  msz.toNat sb1 ∧
                                                (FullMem c sb1 ⋆ R) m1)
                                              (fun (bp, ()) _ => bend_bv.toNat + 1 - bp.toNat)
                                              (fun Jbp hJbp => by
                                                m6b_let
                                                exact hJbp (boff_bv, ()) mb
                                                  ⟨sb, by omega, hsb, hmb⟩)
                                              (fun Jbp (bp, ()) m1
                                                  ⟨sb1, hbp_le, hsb1, hm1⟩ ihbp => ?_)
                                            m6b_split
                                            · have hbp_lt : bp.toNat < bend_bv.toNat :=
                                                bv64_ult_lt hc
                                              have hbp_arr : bp.toNat < sb1.core.wstk.length := by
                                                rw [hsb1.2.2.2.1]
                                                change bp.toNat < sp.core.wstk.length
                                                rw [← hsb.2.2.2.1]
                                                have := hsb.1.1.core_ok.wstk_len_arr; omega
                                              have hbp1_n : (bp + 1#64).toNat = bp.toNat + 1 :=
                                                bv64_add1_lt (by omega)
                                              clear hc; m6b_split
                                              · have hbp2_n :
                                                    (bp + 2#64).toNat = bp.toNat + 2 :=
                                                  bv64_add_nat_lt 2 (by decide) (by omega)
                                                m6b_let
                                                exact ihbp (bp + 2#64, ()) m1
                                                  (by dsimp only; rw [hbp2_n]; omega)
                                                  ⟨sb1, by rw [hbp2_n]; omega, hsb1, hm1⟩
                                              · clear hc; m6b_to_group
                                                refine wp_join_group (ts := [.bool])
                                                  (fun (_subm'', ()) m2 => ∃ sb2 : FullState,
                                                    M6FsScanInv c F0 F_cur cv0 alen0 fuel0 sp sk
                                                      msz.toNat sb2 ∧
                                                    (FullMem c sb2 ⋆ R) m2)
                                                  (fun _ _ m2 ⟨sb2, hsb2, hm2⟩ => by
                                                    m6b_let
                                                    exact ihbp (bp + 1#64, ()) m2
                                                      (by dsimp only; rw [hbp1_n]; omega)
                                                      ⟨sb2, by rw [hbp1_n]; omega, hsb2, hm2⟩)
                                                  ?_
                                                intro Jbo hJbo
                                                m6b_split
                                                · have hot_lt :
                                                      (sb1.core.wstk[bp.toNat]'hbp_arr &&&
                                                        0x7FFFFFFF#32).toNat < 2 * cv0 := by
                                                    have h := bv64_ult_lt hc
                                                    rw [bv_zext32_toNat] at h
                                                    change (sb1.core.wstk[bp.toNat]'hbp_arr &&&
                                                      0x7FFFFFFF#32).toNat <
                                                      (BitVec.ofNat 64 cv0 <<< (1 : Nat)).toNat
                                                      at h
                                                    rwa [bv64_shl1_ofNat_lt (by omega)] at h
                                                  have hot_vl :
                                                      (sb1.core.wstk[bp.toNat]'hbp_arr &&&
                                                        0x7FFFFFFF#32).toNat <
                                                        sb1.core.vals.length :=
                                                    m6Fs_scan_vals_lt hsb1 hot_lt
                                                  clear hc; m6b_split
                                                  · clear hc; m6b_steps; m6b_call hFind
                                                    refine ⟨F_cur, 2 * cv0, sb1.core.repr,
                                                      FullReprRest c sb1 ⋆ R,
                                                      hsb1.1.2.2.2.2.2.2.2.2.2.2, hot_lt,
                                                      focus_full_repr hm1,
                                                      fun ro repr_o mo hrl_o hrepr_o _ hro_lt _
                                                        hmo => ?_⟩
                                                    let sb2 : FullState :=
                                                      { sb1 with core :=
                                                        { sb1.core with repr := repr_o } }
                                                    have hmo' : (FullMem c sb2 ⋆ R) mo :=
                                                      unfocus_full_repr hmo
                                                    have hsb2 := m6FsScanInv_with_repr hsb1
                                                      (hrl_o.trans hsb1.1.1.core_ok.repr_len)
                                                      hrepr_o
                                                    have hro_vl : ro.toNat < sb2.core.vals.length
                                                      := m6Fs_scan_vals_lt hsb2 hro_lt
                                                    have hro_lm :
                                                        ro.toNat < sb2.core.lit_mark.length :=
                                                      m6Fs_scan_lm_lt hsb2 hro_lt
                                                    m6b_split
                                                    · clear hc; m6b_split
                                                      · m6b_let
                                                        exact hJbp_ex (true, bp + 1#64, ()) mo
                                                          ⟨sb2, hsb2, hmo'⟩
                                                      · m6b_let; exact hJbo (subm, ()) mo
                                                          ⟨sb2, hsb2, hmo'⟩
                                                    · m6b_let; exact hJbo (subm, ()) mo
                                                        ⟨sb2, hsb2, hmo'⟩
                                                  · m6b_let; exact hJbo (subm, ()) m1
                                                      ⟨sb1, hsb1, hm1⟩
                                                · m6b_let; exact hJbo (subm, ()) m1
                                                    ⟨sb1, hsb1, hm1⟩
                                            · m6b_let; exact hJbp_ex (subm, bp, ()) m1
                                                ⟨sb1, hsb1, hm1⟩
                                        · m6b_let; exact hJb_ex () mb ⟨sb, hsb, hmb⟩
                                    · m6b_let
                                      exact ihp (np, ticks + 1#64, ()) mc
                                        (by dsimp only; rw [hnp_n]; omega)
                                        ⟨sc, by rw [hnp_n, ← halp]; exact hnp_bds.2,
                                         (by rw [hnp_n]
                                             exact hnp_mem.elim Or.inl
                                               (fun h => Or.inr (hrefs_eq_sc ▸ h))),
                                         hdc, hcvc, halc, hflc, hreprc, hmc⟩
                      · intro J63 hJ63
                        m6b_steps
                        refine wp_loop_inv (ts := [.bool, i32, i32, i32, i32])
                          (fun (_c_mch, msz, min_l, _min_ld, k, ()) mk_in => ∃ sk_in : FullState,
                            M6FsKInv c F0 F_cur cv0 alen0 fuel0 sp p.toNat sz.toNat msz.toNat
                              k.toNat min_l sk_in ∧
                            (FullMem c sk_in ⋆ R) mk_in)
                          (fun (_, _, _, _, k, ()) _ => sz.toNat - k.toNat)
                          (fun Jk hJk => by
                            m6b_let
                            exact hJk (false, 0#32, 0xFFFFFFFF#32, 0xFFFFFFFF#32, 0#32, ()) mp
                              ⟨sp, ⟨Nat.zero_le _, hb_p', rfl, rfl, rfl, rfl, rfl, rfl, hinc0,
                               Nat.zero_le _, Or.inl rfl,
                               (fun _ hj => absurd hj (Nat.not_lt_zero _)),
                               fun l hl => Or.inl (hlm_p l hl),
                               fun _ _ _ hj _ => absurd hj (Nat.not_lt_zero _)⟩, hmp⟩)
                          (fun Jk (c_mch, msz, min_l, min_ld, k, ()) mk_in
                              ⟨sk_in, hkin, hmk_in⟩ ihk => ?_)
                        rcases hkin with ⟨hk_le, hb_in, har_in, hwv_in, hws_in, hvl_in, hmc_in,
                          hmrk_in, hinc_in, hmsz_cv, hminl_in, htmp_lt_in, hlm_ok_in, hsem_in⟩
                        m6b_split
                        · have hk_lt : k.toNat < sz.toNat := bv32_ult_lt hc
                          have hk1 : (k + 1#32).toNat = k.toNat + 1 :=
                            bv32_add1_lt_of (by omega)
                          obtain ⟨hl_arr, hl_lt⟩ := m6Fs_k_lit_lt hb_in har_in halp hp_ref
                            hng_p hsz_eq hp_bd hk_lt
                          let l := sk_in.core.arena[(p + 3#64 + k.setWidth 64).toNat]'hl_arr
                          have hl_cv : l.toNat < 2 * cv0 := hl_lt
                          have h2l : 2 * l.toNat < 2 ^ 64 := by have := l.isLt; omega
                          have hpk_n :
                              (p + 3#64 + k.setWidth 64).toNat = p.toNat + 3 + k.toNat := by
                            rw [BitVec.toNat_add, BitVec.toNat_add, bv_zext32_toNat,
                              show (3#64 : BitVec 64).toNat = 3 from rfl,
                              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                          have har_k_pk : p.toNat + 3 + k.toNat < sk_in.core.arena.length := by
                            rw [har_in]; omega
                          have hl_get : sk_in.core.arena[p.toNat + 3 + k.toNat]'har_k_pk = l :=
                            list_getElem_congr hpk_n.symm _ _
                          have hl_vl : l.toNat < sk_in.core.vals.length := by
                            have := hb_in.1.core_ok.vals_len; omega
                          have hl_z : (l.setWidth 64).toNat = l.toNat := bv_zext32_toNat l
                          clear hc; m6b_split
                          · m6b_let
                            exact hJ63 (true, false, c_mch, false, msz, min_l, min_ld, k, ()) mk_in
                              ⟨sk_in, hb_in, har_in, hwv_in, hws_in, hvl_in, hmc_in, hmrk_in,
                               hinc_in, hmsz_cv, hminl_in, htmp_lt_in, hlm_ok_in,
                               (fun h => Bool.noConfusion h), hmk_in⟩
                          · clear hc; m6b_split
                            · have hl_pk_lt :
                                  (sk_in.core.arena[p.toNat + 3 + k.toNat]'har_k_pk).toNat <
                                    2 * cv0 := by
                                rw [hl_get]; exact hl_lt
                              have hlt_v : (sk_in.core.vals[(sk_in.core.arena[p.toNat + 3 +
                                  k.toNat]'har_k_pk).toNat]?.getD 0#8).slt 0#8 = true := by
                                rw [hl_get, List.getElem?_eq_getElem hl_vl, Option.getD_some]
                                refine bv8_sext32_slt0_true ?_
                                rw [list_getElem_congr hl_z.symm hl_vl _]
                                exact hc
                              have hsem' := m6Fs_k_sem_false hb_in.2.1 hb_in.2.2.2.2.2.1
                                hb_in.2.2.2.2.2.2.2.1 hsem_in har_k_pk hl_pk_lt hlt_v
                              m6b_let
                              exact ihk (c_mch, msz, min_l, min_ld, k + 1#32, ()) mk_in
                                (by dsimp only; rw [hk1]; omega)
                                ⟨sk_in, ⟨by rw [hk1]; omega, hb_in, har_in, hwv_in, hws_in,
                                  hvl_in, hmc_in, hmrk_in, hinc_in, hmsz_cv, hminl_in,
                                  htmp_lt_in, hlm_ok_in, by rw [hk1]; exact hsem'⟩, hmk_in⟩
                            · have hl1_mc : ((l >>> 1#32).setWidth 64).toNat <
                                  sk_in.core.min_clr.length := by
                                rw [bv_zext32_toNat,
                                  show (l >>> 1#32 : BitVec 32) = l >>> (1 : Nat) from rfl,
                                  BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
                                have := hb_in.1.core_ok.min_clr_len_arr; omega
                              clear hc; m6b_to_group
                              refine wp_join_group (ts := [.bool]) (fun _ mc1 => mk_in = mc1)
                                ?_
                                (fun Jcm hJcm => by
                                  m6b_split
                                  · m6b_let; exact hJcm (true, ()) mk_in rfl
                                  · m6b_let; exact hJcm (c_mch, ()) mk_in rfl)
                              rintro _ ⟨c_mch', ⟨⟩⟩ mc1 rfl
                              have hl_wv : ((l.setWidth 64 <<< 1#64) + 1#64).toNat <
                                  sk_in.core.wvec.length := by
                                rw [BitVec.toNat_add, bv64_shl1_toNat, hl_z,
                                  Nat.mod_eq_of_lt h2l,
                                  show (1#64 : BitVec 64).toNat = 1 from rfl,
                                  Nat.mod_eq_of_lt (by omega)]
                                have := hb_in.1.core_ok.wvec_len; omega
                              m6b_to_group
                              refine wp_join_group (ts := [i32, i32])
                                (fun (ml', _mld', ()) mm =>
                                  (ml' = 0xFFFFFFFF#32 ∨ ml'.toNat < 2 * cv0) ∧ mk_in = mm)
                                ?_
                                (fun Jml hJml => by
                                  m6b_split
                                  · m6b_let; exact hJml (l, _, ()) mk_in ⟨Or.inr hl_lt, rfl⟩
                                  · m6b_let; exact hJml (min_l, min_ld, ()) mk_in ⟨hminl_in, rfl⟩)
                              rintro _ ⟨min_l', min_ld', ⟨⟩⟩ mm ⟨hminl', rfl⟩
                              m6b_steps; m6b_call hFind
                              refine ⟨F_cur, 2 * cv0, sk_in.core.repr, FullReprRest c sk_in ⋆ R,
                                hb_in.2.2.2.2.2.2.2.2.2.2, hl_lt, focus_full_repr hmk_in,
                                fun r repr_r mr hrl_r hrepr_r _ hr_lt heqv_lr hmr => ?_⟩
                              let sk_r : FullState :=
                                { sk_in with core := { sk_in.core with repr := repr_r } }
                              have hmr' : (FullMem c sk_r ⋆ R) mr := unfocus_full_repr hmr
                              have hb_r := m6FsBaseOk_with_repr hb_in
                                (hrl_r.trans hb_in.1.core_ok.repr_len) hrepr_r
                              have hcv_sk_in : sk_in.core.cur_vars = cv0 := hb_in.2.2.2.2.2.2.2.1
                              have hcv_sk_in_le := hb_in.1.core_ok.cur_vars_le
                              have hr_vl : r.toNat < sk_r.core.vals.length :=
                                m6Fs_base_vals_lt hb_r hr_lt
                              have hr_lm : r.toNat < sk_r.core.lit_mark.length :=
                                m6Fs_base_lm_lt hb_r hr_lt
                              have hr1_lm : (r ^^^ 1#32).toNat < sk_r.core.lit_mark.length := by
                                rw [bv32_xor1_eq_litNeg]
                                exact m6Fs_base_lm_lt hb_r (bv32_xor1_lt_even hr_lt)
                              have hr_z : (r.setWidth 64).toNat = r.toNat := bv_zext32_toNat r
                              have heqv_pk : LitEquiv (cnfOfClauses F_cur)
                                  (sk_r.core.arena[p.toNat + 3 + k.toNat]'har_k_pk).toNat
                                  r.toNat := by
                                change LitEquiv (cnfOfClauses F_cur)
                                  (sk_in.core.arena[p.toNat + 3 + k.toNat]'har_k_pk).toNat r.toNat
                                rw [hl_get]; exact heqv_lr
                              m6b_split
                              · m6b_let
                                exact hJ63 (true, false, c_mch', false, msz, min_l', min_ld', k, ())
                                  mr ⟨sk_r, hb_r, har_in, hwv_in, hws_in, hvl_in, hmc_in, hmrk_in,
                                   hinc_in, hmsz_cv, hminl', htmp_lt_in, hlm_ok_in,
                                   (fun h => Bool.noConfusion h), hmr'⟩
                              · clear hc; m6b_split
                                · have hr_slt :
                                      (sk_r.core.vals[r.toNat]?.getD 0#8).slt 0#8 = true := by
                                    rw [List.getElem?_eq_getElem hr_vl, Option.getD_some]
                                    refine bv8_sext32_slt0_true ?_
                                    rw [list_getElem_congr hr_z.symm hr_vl _]
                                    exact hc
                                  have hsem' := m6Fs_k_sem_equiv hb_r.2.1 hb_r.2.2.2.2.2.1
                                    hb_r.2.2.2.2.2.2.2.1 hsem_in har_k_pk hr_lt heqv_pk hr_slt
                                  m6b_let
                                  exact ihk (c_mch', msz, min_l', min_ld', k + 1#32, ()) mr
                                    (by dsimp only; rw [hk1]; omega)
                                    ⟨sk_r, ⟨by rw [hk1]; omega, hb_r, har_in, hwv_in, hws_in,
                                      hvl_in, hmc_in, hmrk_in, hinc_in, hmsz_cv, hminl',
                                      htmp_lt_in, hlm_ok_in, by rw [hk1]; exact hsem'⟩, hmr'⟩
                                · clear hc; m6b_split
                                  · m6b_let
                                    exact hJ63 (false, true, c_mch', false, msz, min_l', min_ld',
                                      k, ()) mr ⟨sk_r, hb_r, har_in, hwv_in, hws_in, hvl_in,
                                        hmc_in, hmrk_in, hinc_in, hmsz_cv, hminl', htmp_lt_in,
                                        hlm_ok_in, (fun _ h => Bool.noConfusion h), hmr'⟩
                                  · clear hc; m6b_to_group
                                    refine wp_join_group (ts := [.bool, i32])
                                      (fun (ovf', msz', ()) m1 => ∃ sk1 : FullState,
                                        ovf' = false ∧ msz'.toNat ≤ cv0 ∧
                                        M6FsBaseOk c F0 F_cur cv0 alen0 fuel0 sk1 ∧
                                        sk1.core.arena = sp.core.arena ∧
                                        sk1.core.wvec = sp.core.wvec ∧
                                        sk1.core.wstk = sp.core.wstk ∧
                                        sk1.core.vals = sp.core.vals ∧
                                        sk1.core.min_clr = sp.core.min_clr ∧
                                        sk1.core.mrk = sp.core.mrk ∧
                                        sk1.core.inconsistent = 0#64 ∧
                                        (∀ j < msz'.toNat,
                                          (sk1.core.tmp[j]?.getD 0#32).toNat < 2 * cv0) ∧
                                        (∀ l < 2 * c.max_vars,
                                          sk1.core.lit_mark[l]?.getD 0#8 = 0#8 ∨
                                          (∃ j < msz'.toNat,
                                            (sk1.core.tmp[j]?.getD 0#32).toNat = l ∧
                                            l < 2 * cv0)) ∧
                                        (∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
                                          ∀ j < k.toNat + 1,
                                            evalLitVal α (sk1.core.arena[p.toNat + 3 + j]?.getD
                                              0#32).toNat = true →
                                            ∃ q < msz'.toNat, evalLitVal α (sk1.core.tmp[q]?.getD
                                              0#32).toNat = true) ∧
                                        (FullMem c sk1 ⋆ R) m1)
                                      (fun _ ⟨ovf', msz', ⟨⟩⟩ m1
                                          ⟨sk1, _, hmsz', hb1, har1, hwv1, hws1, hvl1, hmc1, hmrk1,
                                           hinc1, htmp1, hlm1, hsem1, hm1⟩ => by
                                        m6b_steps
                                        exact ihk (c_mch', msz', min_l', min_ld', k + 1#32, ()) m1
                                          (by dsimp only; rw [hk1]; omega)
                                          ⟨sk1, ⟨by rw [hk1]; omega, hb1, har1, hwv1, hws1, hvl1,
                                            hmc1, hmrk1, hinc1, hmsz', hminl', htmp1, hlm1,
                                            by rw [hk1]; exact hsem1⟩,
                                           hm1⟩)
                                      ?_
                                    intro Jov hJov
                                    m6b_split
                                    · clear hc; m6b_split
                                      · have hmsz_lt : msz.toNat < cv0 := by
                                          have h := bv64_ult_lt hc
                                          rwa [bv_zext32_toNat, bv64_ofNat_toNat_lt (by omega)] at h
                                        have hmsz1 : (msz + 1#32).toNat = msz.toNat + 1 :=
                                          bv32_add1_lt_of (by omega)
                                        have hmsz_arr : msz.toNat < sk_r.core.tmp.length := by
                                          dsimp only [sk_r]
                                          have := hb_in.1.core_ok.tmp_len_arr; omega
                                        have hmsz_z : (msz.setWidth 64).toNat = msz.toNat :=
                                          bv_zext32_toNat msz
                                        clear hc; m6b_steps; rw [hmsz_z, hr_z] at hm
                                        obtain ⟨htmp', hlm'⟩ := m6Fs_lm_set_mark htmp_lt_in
                                          hlm_ok_in hr_lt hmsz_arr hr_lm
                                        have hsem' := m6Fs_k_sem_push hsem_in har_k_pk hmsz_arr
                                          heqv_pk
                                        exact hJov (false, msz + 1#32, ()) m
                                          ⟨_, rfl, by rw [hmsz1]; omega,
                                           m6FsBaseOk_with_tmp
                                             (m6FsBaseOk_with_lm hb_r
                                               (lm' := sk_r.core.lit_mark.set r.toNat 1#8)
                                               (by rw [List.length_set]
                                                   exact hb_r.1.core_ok.lit_mark_len))
                                             (tmp' := sk_r.core.tmp.set msz.toNat r)
                                             (by rw [List.length_set]
                                                 exact hb_r.1.core_ok.tmp_len_arr),
                                           har_in, hwv_in, hws_in, hvl_in, hmc_in, hmrk_in, hinc_in,
                                           by rw [hmsz1]; exact htmp',
                                           by rw [hmsz1]; exact hlm',
                                           by rw [hmsz1]; exact hsem', hm⟩
                                      · m6b_let
                                        exact hJ63 (false, false, c_mch', true, msz, min_l',
                                          min_ld', k, ()) mr
                                          ⟨sk_r, hb_r, har_in, hwv_in, hws_in, hvl_in, hmc_in,
                                           hmrk_in, hinc_in, hmsz_cv, hminl', htmp_lt_in,
                                           hlm_ok_in, (fun _ _ h => Bool.noConfusion h), hmr'⟩
                                    · have hneq : sk_r.core.lit_mark[r.toNat]?.getD 0#8 ≠ 0#8 := by
                                        rw [List.getElem?_eq_getElem hr_lm, Option.getD_some]
                                        refine bv8_zext32_beq0_false ?_
                                        rw [list_getElem_congr hr_z.symm hr_lm _]
                                        exact hc
                                      have hsem' := m6Fs_k_sem_mem hsem_in har_k_pk hr_lt
                                        hcv_le hlm_ok_in hneq heqv_pk
                                      m6b_let
                                      exact hJov (false, msz, ()) mr
                                        ⟨sk_r, rfl, hmsz_cv, hb_r, har_in, hwv_in, hws_in, hvl_in,
                                         hmc_in, hmrk_in, hinc_in, htmp_lt_in, hlm_ok_in, hsem',
                                         hmr'⟩
                        · have hk_eq : k.toNat = sz.toNat := by
                            have h : ¬ k.toNat < sz.toNat := bv32_ult_not_lt hc; omega
                          m6b_let
                          exact hJ63 (false, false, c_mch, false, msz, min_l, min_ld, k, ()) mk_in
                            ⟨sk_in, hb_in, har_in, hwv_in, hws_in, hvl_in, hmc_in, hmrk_in,
                             hinc_in, hmsz_cv, hminl_in, htmp_lt_in, hlm_ok_in,
                             fun _ _ _ => hk_eq ▸ hsem_in, hmk_in⟩
                · clear hc; m6b_let
                  exact hJexit () mp ⟨sp, hdp, hcvp, hflp, hreprp, hmp⟩
              · clear hc; m6b_let
                exact hJexit () mp ⟨sp, hdp, hcvp, hflp, hreprp, hmp⟩
            · clear hc; m6b_let
              exact hJexit () mp ⟨sp, hdp, hcvp, hflp, hreprp, hmp⟩
          · m6b_steps
            exact hQ 1#64 si2 mi2 hdi2 hcvi2 hfli2 (hcvi2 ▸ hrepri2)
              (Or.inl rfl) (fun h => by cases h) hmi2

end FwdSubsumeProof

end LeanQbe.T.Examples.Kissat.FullM6CongSubst
