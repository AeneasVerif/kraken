/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Congruence.Inv
public import LeanQbe.T.Examples.Kissat.Src.Congruence

/-!
# Congruence Forward Subsumption Helpers & Inner-Loop WP Lemmas (`WpFwdSubsume0`)

Shared pure/invariant/occurrence helpers, match-init WP, and literal-reduction loop WPs
used by `LeanQbe.T.Examples.Kissat.Proof.Congruence.WpFwdSubsume`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Congruence

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Congruence
open LeanQbe.T.Examples.Kissat.Proof.Spec LeanQbe.T.Examples.Kissat.Proof.Congruence.Spec
open Kraken.Bedrock2.Test

open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Congruence.CongTactics

public section

/-! ## 1. Pure, Invariant, Pair & Occurrence-List Helpers -/

theorem list_eq_getElem_congr {α : Type _} {xs ys : List α} (h : xs = ys) {i : Nat}
    (hx : i < xs.length) (hy : i < ys.length) : xs[i]'hx = ys[i]'hy := by subst h; rfl

theorem bv8_slt0_iff {v : BitVec 8} (hdom : v = 0#8 ∨ v = 1#8 ∨ v = 0xFF#8) :
    v.slt 0#8 = true ↔ v = 0xFF#8 := by rcases hdom with rfl | rfl | rfl <;> decide

theorem bv8_sext32_slt0_true {x : BitVec 8}
    (h : (x.signExtend 32).slt 0#32 = true) : x.slt 0#8 = true := by
  have hi : (x.signExtend 32).toInt = x.toInt := by
    rw [BitVec.toInt_signExtend, show min 32 8 = 8 from rfl, Int.bmod_def]
    have h1 := BitVec.le_toInt x; have h2 := @BitVec.toInt_lt 8 x
    rw [show ((2 ^ 8 : Nat) : Int) = 256 from rfl]; split <;> omega
  simpa [BitVec.slt, hi] using h

theorem bv8_zext32_beq0_false {x : BitVec 8}
    (h : (x.setWidth 32 == 0#32) = false) : x ≠ 0#8 := by intro hx; subst hx; simp at h

theorem fid_garb_false_of_and {hdr : BitVec 32}
    (h : (hdr &&& 0x00080000#32) = 0#32) : ((hdr &&& 0x00080000#32) != 0#32) = false := by
  simp [h]

theorem bv64_shl_s1 (x : BitVec 64) (h : 2 * x.toNat < 2 ^ 64) :
    (x <<< BitVec.signExtend 64 1#32).toNat = 2 * x.toNat := by
  rw [show BitVec.signExtend 64 1#32 = 1#64 from rfl]; exact bv64_shl1_lt h

theorem bv64_shr_s2 (x : BitVec 64) :
    (x >>> BitVec.signExtend 64 2#32).toNat = x.toNat / 4 := by
  rw [show BitVec.signExtend 64 2#32 = 2#64 from rfl]; exact bv64_shr2_toNat x

theorem bv32_shr1_z64 (x : BitVec 32) :
    (BitVec.setWidth 64 (x >>> 1#32)).toNat = x.toNat / 2 := by
  rw [bv_zext32_toNat]; simp [Nat.shiftRight_eq_div_pow]

theorem fid_lit_false_of_vals_slt0 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    (_hcl0 : k.cur_level = 0) {l : Nat} (hl : l < 2 * k.cur_vars)
    (hslt : (k.vals[l]?.getD 0#8).slt 0#8 = true) :
    ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α → evalLitVal α l = false := by
  intro α hα
  have hff : k.vals[l]?.getD 0#8 = 0xFF#8 := (bv8_slt0_iff (hw.vals_domain l hl)).mp hslt
  obtain ⟨i, hi, htrl⟩ := (hw.vals_false_iff l hl).mp hff
  have hlv0 : (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
    have := hw.lvl_le i hi; omega
  have hsat := CNF.entails_clause_def.mp (hw.level0_sound i hi hlv0) α hα
  rw [← clauseEvalVal_iff, clauseEvalVal] at hsat
  simp only [List.any_cons, List.any_nil, Bool.or_false, htrl,
    show l ^^^ 1 = litNeg l from rfl, evalLitVal_litNeg] at hsat
  cases h : evalLitVal α l <;> simp_all

theorem fid_litEquiv_eval {F : CNF Nat} {l1 l2 : Nat}
    (heqv : LitEquiv F l1 l2) {α : Nat → Bool} (hα : F.Sat α) :
    evalLitVal α l1 = evalLitVal α l2 := by
  have h12 := CNF.entails_clause_def.mp heqv.1 α hα
  have h21 := CNF.entails_clause_def.mp heqv.2 α hα
  rw [← clauseEvalVal_iff, clauseEvalVal] at h12 h21
  simp only [List.any_cons, List.any_nil, Bool.or_false, evalLitVal_litNeg] at h12 h21
  cases e1 : evalLitVal α l1 <;> cases e2 : evalLitVal α l2 <;> simp_all

theorem fid_denseInvW_with_mclr {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {mc' : List (BitVec 32)} (hl : mc'.length = c.max_vars) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with min_clr := mc' } } :=
  ⟨⟨{ hd.1.core_ok with min_clr_len_arr := hl }, hd.1.scratch_ok⟩,
   { hd.2.1 with
     arena := { hd.2.1.arena with len_ok := hd.2.1.arena.len_ok }
     watches := hd.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   fullLitMarksClear_of_eq hd.2.2.1 rfl rfl, fullArenaVarsNodup_of_eq hd.2.2.2.1 rfl rfl,
   fullExtScratchOk_of_eq hd.2.2.2.2.1 rfl rfl rfl rfl, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

theorem fid_denseInvW_with_ws12 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {w1' w2' : List (BitVec 32)}
    (hl1 : w1'.length = 2 * c.max_vars) (hl2 : w2'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur
      { s with scratch := { s.scratch with work_stk1 := w1', work_stk2 := w2' } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with work_stk1_len := hl1, work_stk2_len := hl2 }⟩,
   hd.2.1, hd.2.2.1, hd.2.2.2.1, fullExtScratchOk_of_eq hd.2.2.2.2.1 rfl rfl rfl rfl,
   hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

theorem fid_denseInvW_with_inc {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    (hu : (cnfOfClauses F_cur).Unsat) (inc' : BitVec 64) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with inconsistent := inc' } } :=
  ⟨⟨{ hd.1.core_ok with }, hd.1.scratch_ok⟩,
   fullWitnessInv_with_inconsistent hd.2.1 inc' (fun _ => hu),
   hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

theorem fid_fs_markGarb_core {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) (ag' : BitVec 64) :
    let s' : FullState :=
      { s with core :=
        { s.core with
          arena := s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
          arena_garbage := ag' } }
    FullDenseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s := by
  intro s'
  have hcl0 : s.core.cur_level = 0 := hd.2.2.2.2.2.1
  have hmg := hd.2.1.arena.markGarb hd.1.core_ok href ag'
  have hlen' : s'.LengthsOk c :=
    ⟨{ hd.1.core_ok with arena_len_arr := by simp [s', hd.1.core_ok.arena_len_arr] },
     hd.1.scratch_ok⟩
  have hnd' := FullArenaVarsNodup.of_markGarb ⟨hd.1, ⟨F_cur, hd.2.1⟩⟩ hd.2.2.2.1 href ag'
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hd.2.1 with
      arena := hmg.2
      watches := hd.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => hmg.1 ▸ hr)
      reason_inv := fun idx hidx hne => by
        dsimp only [s'] at hidx
        exact absurd (hd.2.1.level0_rsn_none idx hidx (by have := hd.2.1.lvl_le idx hidx; omega))
          hne
      reason_lit_mem := fun idx hidx hne _ => by
        dsimp only [s'] at hidx
        exact absurd (hd.2.1.level0_rsn_none idx hidx (by have := hd.2.1.lvl_le idx hidx; omega))
          hne }
  refine ⟨⟨hlen', hw', fullLitMarksClear_of_eq hd.2.2.1 rfl rfl, hnd',
    ⟨fun i hi => (hd.2.2.2.2.1.1 i hi).elim Or.inl fun h =>
      Or.inr (by change _ ∈ fullArenaClauseRefsCore s'.core; rw [hmg.1]; exact h),
     hd.2.2.2.2.1.2⟩, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩, hmg.1⟩

theorem fid_fs_markGarb_dense' {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefs s) (hcr : cref < s.core.arena.length)
    (ag' : BitVec 64) :
    let s' : FullState :=
      { s with core :=
        { s.core with
          arena := s.core.arena.set cref ((s.core.arena[cref]'hcr) ||| 0x00080000#32)
          arena_garbage := ag' } }
    FullDenseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s := by
  have hhdr : fullArenaHdr s cref = s.core.arena[cref]'hcr := by
    unfold fullArenaHdr fullArenaHdrCore; rw [List.getElem?_eq_getElem hcr, Option.getD_some]
  simpa only [hhdr] using fid_fs_markGarb_core hd href ag'

theorem fid_addUnit_denseInvW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (hd : FullDenseInvW c F0 F_cur s)
    (hl' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hcl' : s'.core.cur_level = 0) (hdm' : s'.core.dense_mode = s.core.dense_mode)
    (hmrk' : s'.core.mrk = s.core.mrk) (hlm' : s'.core.lit_mark = s.core.lit_mark)
    (har' : s'.core.arena = s.core.arena) (hal' : s'.core.arena_len = s.core.arena_len)
    (hll' : s'.scratch.last_learned = s.scratch.last_learned)
    (hext' : s'.scratch.extend_len = s.scratch.extend_len) : FullDenseInvW c F0 F_cur s' :=
  let ⟨h1, h2, h3, h4, h5⟩ := fullAddUnitSpec_fullDenseInvW hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2.1
    hd.2.2.2.2.2.2 hcl' hmrk' hlm' har' hal' hll' hext' hdm'
  ⟨hl', hw', h1, h2, h3, h4, h5⟩

theorem congPairsOk_push {P : BitVec 32 → BitVec 32 → Prop} {a : List (BitVec 32)}
    {n : Nat} {key cr : BitVec 32} (hok : CongPairsOk P a n) (hbd : 2 * n + 1 < a.length)
    (hp : P key cr) : CongPairsOk P ((a.set (2 * n) key).set (2 * n + 1) cr) (n + 1) := by
  intro i hi; by_cases hin : i = n
  · subst hin; rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega),
      List.getElem?_set_self (by simp; omega), Option.getD_some, Option.getD_some]; exact hp
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hok i (by omega)

theorem congPairsOk_set_ge {P : BitVec 32 → BitVec 32 → Prop} {a : List (BitVec 32)}
    {n idx : Nat} {v : BitVec 32} (hok : CongPairsOk P a n) (hge : 2 * n ≤ idx) :
    CongPairsOk P (a.set idx v) n := fun i hi => by
  rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hok i hi

abbrev FidFsOccPtrOk (base occ_pos : Nat) (ptr : BitVec 32) : Prop :=
  ptr = 0xFFFFFFFF#32 ∨
    (base ≤ ptr.toNat ∧ ptr.toNat + 1 < occ_pos ∧ (ptr.toNat - base) % 2 = 0)

abbrev FidFsOccOk (refs0 : List Nat) (nlits base occ_pos : Nat)
    (occ_head scr : List (BitVec 32)) : Prop :=
  base ≤ occ_pos ∧ occ_pos ≤ scr.length ∧ (occ_pos - base) % 2 = 0 ∧
  (∀ l < nlits, FidFsOccPtrOk base occ_pos (occ_head[l]?.getD 0xFFFFFFFF#32)) ∧
  (∀ nd, base ≤ nd → nd + 1 < occ_pos → (nd - base) % 2 = 0 →
    (scr[nd]?.getD 0#32).toNat ∈ refs0 ∧
    FidFsOccPtrOk base occ_pos (scr[nd + 1]?.getD 0xFFFFFFFF#32))

theorem fidFsOccOk_init {refs0 : List Nat} {nlits base : Nat}
    {occ_head scr : List (BitVec 32)} (hbd : base ≤ scr.length)
    (hall : ∀ l < nlits, occ_head[l]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) :
    FidFsOccOk refs0 nlits base base occ_head scr :=
  ⟨Nat.le_refl _, hbd, by simp, fun l hl => Or.inl (hall l hl), fun _ _ h2 _ => by omega⟩

theorem fidFsOccOk_push {refs0 : List Nat} {nlits base occ_pos : Nat}
    {occ_head scr : List (BitVec 32)} {cref least_r : BitVec 32}
    (hok : FidFsOccOk refs0 nlits base occ_pos occ_head scr)
    (hcap : occ_pos + 2 ≤ scr.length) (hu32 : occ_pos < 2 ^ 32)
    (hcr : cref.toNat ∈ refs0) (hlr : least_r.toNat < nlits)
    (hlr_len : least_r.toNat < occ_head.length) :
    let head := occ_head[least_r.toNat]'hlr_len
    FidFsOccOk refs0 nlits base (occ_pos + 2)
      (occ_head.set least_r.toNat (BitVec.ofNat 32 occ_pos))
      ((scr.set occ_pos cref).set (occ_pos + 1) head) := by
  intro head; rcases hok with ⟨hbo, hos, hev, hheads, hnodes⟩
  have hup : ∀ p, FidFsOccPtrOk base occ_pos p → FidFsOccPtrOk base (occ_pos + 2) p := fun p hp =>
    hp.elim Or.inl fun ⟨h1, h2, h3⟩ => Or.inr ⟨h1, by omega, h3⟩
  have hhead_ok : FidFsOccPtrOk base occ_pos head := by
    have h :=
      hheads least_r.toNat hlr; rwa [List.getElem?_eq_getElem hlr_len, Option.getD_some] at h
  have hnew_ptr : FidFsOccPtrOk base (occ_pos + 2) (BitVec.ofNat 32 occ_pos) := by
    right; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu32]; exact ⟨hbo, by omega, hev⟩
  refine ⟨by omega, by simp [hcap], by omega, fun l hl => ?_, fun nd h1 h2 h3 => ?_⟩
  · by_cases hle : l = least_r.toNat
    · subst hle; rw [List.getElem?_set_self hlr_len, Option.getD_some]; exact hnew_ptr
    · rw [List.getElem?_set_ne (Ne.symm hle)]; exact hup _ (hheads l hl)
  · by_cases hnd : nd = occ_pos
    · subst hnd; rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega),
        List.getElem?_set_self (by simp; omega), Option.getD_some, Option.getD_some]
      exact ⟨hcr, hup _ hhead_ok⟩
    · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
      obtain ⟨hcr', hnxt'⟩ := hnodes nd h1 (by omega) h3; exact ⟨hcr', hup _ hnxt'⟩

structure FidFsBaseOk (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (cv0 alen0 : Nat) (fuel0 : BitVec 64) (refs0 : List Nat) (s : FullState) : Prop where
  hlen : s.LengthsOk c
  hw : FullWitnessInv c F0 F_cur s.core
  hmrk : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8
  hnd : FullArenaVarsNodup s
  hext : FullExtScratchOk c s
  hcl : s.core.cur_level = 0
  hdm : s.core.dense_mode ≠ 0#64
  hcv : s.core.cur_vars = cv0
  hal : s.core.arena_len = alen0
  hfl : s.core.fuel = fuel0
  hrefs : fullArenaClauseRefs s = refs0
  hrepr : FullCongReprInv F_cur (2 * cv0) s.core.repr

theorem FidFsBaseOk.of_dense {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 alen0 : Nat} {fuel0 : BitVec 64} {refs0 : List Nat} {s : FullState}
    (hd : FullDenseInvW c F0 F_cur s) (hcv : s.core.cur_vars = cv0)
    (hal : s.core.arena_len = alen0) (hfl : s.core.fuel = fuel0)
    (hrefs : fullArenaClauseRefs s = refs0) (hrepr : FullCongReprInv F_cur (2 * cv0) s.core.repr) :
    FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 s ∧
    (∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8) :=
  ⟨⟨hd.1, hd.2.1, hd.2.2.1.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1,
    hd.2.2.2.2.2.2, hcv, hal, hfl, hrefs, hrepr⟩, hd.2.2.1.2⟩

theorem FidFsBaseOk.to_dense {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 alen0 : Nat} {fuel0 : BitVec 64} {refs0 : List Nat} {s : FullState}
    (hb : FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 s)
    (hlm : ∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8) :
    FullDenseInvW c F0 F_cur s ∧ s.core.cur_vars = cv0 ∧ s.core.arena_len = alen0 ∧
    s.core.fuel = fuel0 ∧ fullArenaClauseRefs s = refs0 ∧
    FullCongReprInv F_cur (2 * cv0) s.core.repr :=
  ⟨⟨hb.hlen, hb.hw, ⟨hb.hmrk, hlm⟩, hb.hnd, hb.hext, hb.hcl, hb.hdm⟩,
   hb.hcv, hb.hal, hb.hfl, hb.hrefs, hb.hrepr⟩

theorem FidFsBaseOk.with_repr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 alen0 : Nat} {fuel0 : BitVec 64} {refs0 : List Nat} {s : FullState}
    (hb : FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 s) {r' : List (BitVec 32)}
    (hrl : r'.length = 2 * c.max_vars) (hrepr' : FullCongReprInv F_cur (2 * cv0) r') :
    FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 { s with core := { s.core with repr := r' } } :=
  { hb with
    hlen := ⟨{ hb.hlen.core_ok with repr_len := hrl }, hb.hlen.scratch_ok⟩
    hw := fullWitnessInv_with_repr hb.hw r'
    hext := fullExtScratchOk_of_eq hb.hext rfl rfl rfl rfl
    hrepr := hrepr' }

theorem FidFsBaseOk.with_lm {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 alen0 : Nat} {fuel0 : BitVec 64} {refs0 : List Nat} {s : FullState}
    (hb : FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 s) {lm' : List (BitVec 8)}
    (hlml : lm'.length = 2 * c.max_vars) :
    FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0
      { s with core := { s.core with lit_mark := lm' } } :=
  { hb with
    hlen := ⟨{ hb.hlen.core_ok with lit_mark_len := hlml }, hb.hlen.scratch_ok⟩
    hw := fullWitnessInv_with_tmp_lm hb.hw s.core.tmp lm'
    hnd := fullArenaVarsNodup_of_eq hb.hnd rfl rfl
    hext := fullExtScratchOk_of_eq hb.hext rfl rfl rfl rfl }

theorem FidFsBaseOk.with_tmp_lm {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 alen0 : Nat} {fuel0 : BitVec 64} {refs0 : List Nat} {s : FullState}
    (hb : FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 s)
    {tmp' : List (BitVec 32)} {lm' : List (BitVec 8)}
    (htl : tmp'.length = c.max_vars) (hlml : lm'.length = 2 * c.max_vars) :
    FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0
      { s with core := { s.core with tmp := tmp', lit_mark := lm' } } :=
  { hb with
    hlen := ⟨{ hb.hlen.core_ok with tmp_len_arr := htl, lit_mark_len := hlml }, hb.hlen.scratch_ok⟩
    hw := fullWitnessInv_with_tmp_lm hb.hw tmp' lm'
    hnd := fullArenaVarsNodup_of_eq hb.hnd rfl rfl
    hext := fullExtScratchOk_of_eq hb.hext rfl rfl rfl rfl }

theorem FidFsBaseOk.vals_lt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 alen0 : Nat} {fuel0 : BitVec 64} {refs0 : List Nat} {s : FullState} {x : Nat}
    (hb : FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 s) (hx : x < 2 * cv0) :
    x < s.core.vals.length := by
  have := hb.hlen.core_ok.vals_len; have := hb.hlen.core_ok.cur_vars_le; have := hb.hcv; omega

theorem FidFsBaseOk.lm_lt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 alen0 : Nat} {fuel0 : BitVec 64} {refs0 : List Nat} {s : FullState} {x : Nat}
    (hb : FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 s) (hx : x < 2 * cv0) :
    x < s.core.lit_mark.length := by
  have := hb.hlen.core_ok.lit_mark_len; have := hb.hlen.core_ok.cur_vars_le; have := hb.hcv; omega

theorem FidFsBaseOk.cr_ar {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 alen0 : Nat} {fuel0 : BitVec 64} {refs0 : List Nat} {s : FullState} {cr : BitVec 32}
    (hb : FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 s) (hcr : cr.toNat ∈ refs0) :
    cr.toNat < s.core.arena.length ∧ (cr.setWidth 64 + 2#64).toNat < s.core.arena.length ∧
    (cr.setWidth 64 + 2#64).toNat = cr.toNat + 2 ∧
    cr.toNat + 3 + fullArenaClauseSizeCore s.core cr.toNat ≤ alen0 := by
  have hac := c.harena; unfold dimacsBound at hac
  have hcr_s : cr.toNat ∈ fullArenaClauseRefsCore s.core := by
    change cr.toNat ∈ fullArenaClauseRefs s; rw [hb.hrefs]; exact hcr
  have hwf := hb.hw.arena.refs_wf cr.toNat hcr_s
  have hle := hb.hlen.core_ok.arena_len_le; have harr := hb.hlen.core_ok.arena_len_arr
  have hal := hb.hal; have h3 : (cr.setWidth 64 + 2#64).toNat = cr.toNat + 2 := by bv_omega
  exact ⟨by omega, by rw [h3]; omega, h3, by omega⟩

structure FidFsScanInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (cv0 alen0 : Nat) (fuel0 : BitVec 64) (refs0 : List Nat) (s2 sk : FullState) (msz : Nat)
    (s : FullState) : Prop where
  hb : FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 s
  har : s.core.arena = s2.core.arena
  hvl : s.core.vals = s2.core.vals
  htmp : s.core.tmp = sk.core.tmp
  hlm : s.core.lit_mark = sk.core.lit_mark
  hinc : s.core.inconsistent = 0#64
  hscr : s.scratch = s2.scratch
  hlmok : ∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8 ∨
    (∃ j < msz, (s.core.tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv0)

theorem FidFsScanInv.with_repr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 alen0 : Nat} {fuel0 : BitVec 64} {refs0 : List Nat} {s2 sk s : FullState} {msz : Nat}
    (h : FidFsScanInv c F0 F_cur cv0 alen0 fuel0 refs0 s2 sk msz s)
    {r' : List (BitVec 32)} (hrl : r'.length = 2 * c.max_vars)
    (hrepr' : FullCongReprInv F_cur (2 * cv0) r') :
    FidFsScanInv c F0 F_cur cv0 alen0 fuel0 refs0 s2 sk msz
      { s with core := { s.core with repr := r' } } :=
  { h with hb := h.hb.with_repr hrl hrepr' }

theorem fidFs_lm_set_mark {maxv cv msz : Nat} {tmp : List (BitVec 32)}
    {lm : List (BitVec 8)} {r : BitVec 32} (htmp_lt : ∀ j < msz, (tmp[j]?.getD 0#32).toNat < 2 * cv)
    (hlm_ok : ∀ l < 2 * maxv, lm[l]?.getD 0#8 = 0#8 ∨
      (∃ j < msz, (tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv))
    (hr_lt : r.toNat < 2 * cv) (hmsz_lt : msz < tmp.length) :
    (∀ j < msz + 1, ((tmp.set msz r)[j]?.getD 0#32).toNat < 2 * cv) ∧
    (∀ l < 2 * maxv, (lm.set r.toNat 1#8)[l]?.getD 0#8 = 0#8 ∨
      (∃ j < msz + 1, ((tmp.set msz r)[j]?.getD 0#32).toNat = l ∧ l < 2 * cv)) := by
  refine ⟨fun j hj => ?_, fun l hl => ?_⟩
  · by_cases hjm : j = msz
    · subst hjm; rw [List.getElem?_set_self hmsz_lt, Option.getD_some]; exact hr_lt
    · rw [List.getElem?_set_ne (Ne.symm hjm)]; exact htmp_lt j (by omega)
  · by_cases hlr : l = r.toNat
    · subst hlr; right; refine ⟨msz, Nat.lt_succ_self _, ?_, hr_lt⟩
      rw [List.getElem?_set_self hmsz_lt, Option.getD_some]
    · rw [List.getElem?_set_ne (Ne.symm hlr)]
      rcases hlm_ok l hl with h0 | ⟨j, hj, hjl, hlc⟩
      · exact Or.inl h0
      · right; refine ⟨j, by omega, ?_, hlc⟩; rw [List.getElem?_set_ne (by omega)]; exact hjl

theorem fidFs_lm_clear_step {maxv cv msz k : Nat} {tmp : List (BitVec 32)}
    {lm : List (BitVec 8)} (hk : k < msz) (hk_lt : k < tmp.length)
    (htk_len : (tmp[k]'hk_lt).toNat < lm.length)
    (hinv : ∀ l < 2 * maxv, lm[l]?.getD 0#8 = 0#8 ∨
      (∃ j, k ≤ j ∧ j < msz ∧ (tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv)) :
    ∀ l < 2 * maxv, (lm.set (tmp[k]'hk_lt).toNat 0#8)[l]?.getD 0#8 = 0#8 ∨
      (∃ j, k + 1 ≤ j ∧ j < msz ∧ (tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv) := by
  intro l hl; by_cases hlk : l = (tmp[k]'hk_lt).toNat
  · subst hlk; left; rw [List.getElem?_set_self htk_len, Option.getD_some]
  · rw [List.getElem?_set_ne (Ne.symm hlk)]
    rcases hinv l hl with h0 | ⟨j, hkj, hjm, hjl, hlc⟩
    · exact Or.inl h0
    · right; have hjk : j ≠ k := fun he => by
        subst he; rw [List.getElem?_eq_getElem hk_lt, Option.getD_some] at hjl; exact hlk hjl.symm
      exact ⟨j, by omega, hjm, hjl, hlc⟩

theorem fidFs_lm_clear_from_zero {maxv cv msz : Nat} {tmp : List (BitVec 32)}
    {lm : List (BitVec 8)} (h : ∀ l < 2 * maxv, lm[l]?.getD 0#8 = 0#8 ∨
      (∃ j < msz, (tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv)) :
    ∀ l < 2 * maxv, lm[l]?.getD 0#8 = 0#8 ∨
      (∃ j, 0 ≤ j ∧ j < msz ∧ (tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv) :=
  fun l hl => (h l hl).elim Or.inl fun ⟨j, hj, hjl, hlc⟩ => Or.inr ⟨j, Nat.zero_le _, hj, hjl, hlc⟩

theorem fidFs_lm_clear_done {maxv cv msz : Nat} {tmp : List (BitVec 32)}
    {lm : List (BitVec 8)} (h : ∀ l < 2 * maxv, lm[l]?.getD 0#8 = 0#8 ∨
      (∃ j, msz ≤ j ∧ j < msz ∧ (tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv)) :
    ∀ l < 2 * maxv, lm[l]?.getD 0#8 = 0#8 := fun l hl =>
  (h l hl).elim id fun ⟨_, hj1, hj2, _⟩ => by omega

theorem fidFs_msz0_unsat {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {p sz : Nat} (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hp_ref : p ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s p = false)
    (hsz : fullArenaClauseSizeCore s.core p = sz)
    (hsem : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      ∀ j < sz, evalLitVal α (s.core.arena[p + 3 + j]?.getD 0#32).toNat = true → False) :
    (cnfOfClauses F_cur).Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro α hα; have hwf := hw.arena.refs_wf p hp_ref
  have hbd : p + 3 + sz ≤ s.core.arena.length := by
    have := hlen.core_ok.arena_len_le; have := hlen.core_ok.arena_len_arr; omega
  have hsat := CNF.entails_clause_def.mp (hw.arena.entails p hp_ref hng) α hα
  rw [← clauseEvalVal_iff, clauseEvalVal, List.any_eq_true] at hsat
  obtain ⟨l, hl_mem, hl_true⟩ := hsat
  obtain ⟨j, hj, hget⟩ := (mem_fullArenaClauseLitsCore_iff (hsz ▸ hbd)).mp hl_mem
  have hget' : (s.core.arena[p + 3 + j]?.getD 0#32).toNat = l := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hget]
  exact hsem α hα j (hsz ▸ hj) (hget' ▸ hl_true)

theorem fidFs_msz1_entails {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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
  have hget' : (s.core.arena[p + 3 + j]?.getD 0#32).toNat = l := by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hget]
  exact hsem α hα j (hsz ▸ hj) (hget' ▸ hl_true)

theorem fidFs_k_lit_lt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cv0 alen0 : Nat} {fuel0 : BitVec 64} {refs0 : List Nat} {sp sk_in : FullState}
    {p : BitVec 64} {sz k : BitVec 32} (hb : FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 sk_in)
    (har : sk_in.core.arena = sp.core.arena) (hp_ref : p.toNat ∈ refs0)
    (hng : fullArenaClauseGarbCore sp.core p.toNat = false)
    (hsz : fullArenaClauseSizeCore sp.core p.toNat = sz.toNat)
    (hp_le : p.toNat + 3 + sz.toNat ≤ alen0) (hk : k.toNat < sz.toNat) :
    ∃ hbd : (p + 3#64 + k.setWidth 64).toNat < sk_in.core.arena.length,
      (sk_in.core.arena[(p + 3#64 + k.setWidth 64).toNat]'hbd).toNat < 2 * cv0 := by
  have hac := c.harena; unfold dimacsBound at hac
  have hp_sd : p.toNat ∈ fullArenaClauseRefsCore sk_in.core := by
    change p.toNat ∈ fullArenaClauseRefs sk_in; rw [hb.hrefs]; exact hp_ref
  have hng_sd : fullArenaClauseGarbCore sk_in.core p.toNat = false := by
    unfold fullArenaClauseGarbCore fullArenaHdrCore at hng ⊢; rwa [har]
  have hsz_sd : fullArenaClauseSizeCore sk_in.core p.toNat = sz.toNat := by
    unfold fullArenaClauseSizeCore at hsz ⊢; rwa [har]
  have hal := hb.hal; have hle := hb.hlen.core_ok.arena_len_le
  have harr := hb.hlen.core_ok.arena_len_arr
  have hadd : (p + 3#64 + k.setWidth 64).toNat = p.toNat + 3 + k.toNat := by bv_omega
  have hbd : (p + 3#64 + k.setWidth 64).toNat < sk_in.core.arena.length := by rw [hadd]; omega
  refine ⟨hbd, ?_⟩
  have hl_mem : (sk_in.core.arena[(p + 3#64 + k.setWidth 64).toNat]'hbd).toNat ∈
      fullArenaClauseLitsCore sk_in.core p.toNat :=
    (mem_fullArenaClauseLitsCore_iff (by omega)).mpr ⟨k.toNat, by omega,
      congrArg BitVec.toNat (list_getElem_congr hadd.symm _ _)⟩
  have hlt := hb.hw.arena.lits_lt p.toNat hp_sd hng_sd _ hl_mem
  rwa [hb.hcv] at hlt

theorem fidFs_k_sem_false {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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
  intro α hα j hj het; by_cases hjk : j < k
  · exact hsem α hα j hjk het
  · obtain rfl : j = k := by omega
    rw [List.getElem?_eq_getElem hk_arr, Option.getD_some] at het
    have hf := fid_lit_false_of_vals_slt0 hw hcl0 (hcv ▸ hl_lt) hslt α hα; rw [het] at hf; cases hf

theorem fidFs_k_sem_equiv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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
  intro α hα j hj het; by_cases hjk : j < k
  · exact hsem α hα j hjk het
  · obtain rfl : j = k := by omega
    rw [List.getElem?_eq_getElem hk_arr, Option.getD_some] at het
    have hev_r : evalLitVal α r.toNat = true := by
      have h := fid_litEquiv_eval heqv hα; rwa [← h]
    have hf :=
      fid_lit_false_of_vals_slt0 hw hcl0 (hcv ▸ hr_lt) hslt α hα; rw [hev_r] at hf; cases hf

theorem fidFs_k_sem_mem {F_cur : List (List Nat)} {maxv cv0 p k msz : Nat}
    {ar tmp : List (BitVec 32)} {lm : List (BitVec 8)} {r : BitVec 32}
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
  intro α hα j hj het; by_cases hjk : j < k
  · exact hsem α hα j hjk het
  · obtain rfl : j = k := by omega
    rw [List.getElem?_eq_getElem hk_arr, Option.getD_some] at het
    rcases hlm_ok r.toNat (by omega) with h0 | ⟨q, hq, hqr, _⟩
    · exact absurd h0 hneq
    · refine ⟨q, hq, ?_⟩; rw [hqr, ← fid_litEquiv_eval heqv hα]; exact het

theorem fidFs_k_sem_push {F_cur : List (List Nat)} {p k msz : Nat}
    {ar tmp : List (BitVec 32)} {r : BitVec 32}
    (hsem : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      ∀ j < k, evalLitVal α (ar[p + 3 + j]?.getD 0#32).toNat = true →
        ∃ q < msz, evalLitVal α (tmp[q]?.getD 0#32).toNat = true)
    (hk_arr : p + 3 + k < ar.length) (hmsz_lt : msz < tmp.length)
    (heqv : LitEquiv (cnfOfClauses F_cur) (ar[p + 3 + k]'hk_arr).toNat r.toNat) :
    ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      ∀ j < k + 1, evalLitVal α (ar[p + 3 + j]?.getD 0#32).toNat = true →
        ∃ q < msz + 1, evalLitVal α ((tmp.set msz r)[q]?.getD 0#32).toNat = true := by
  intro α hα j hj het; by_cases hjk : j < k
  · obtain ⟨q, hq, hqt⟩ := hsem α hα j hjk het
    refine ⟨q, by omega, ?_⟩; rw [List.getElem?_set_ne (by omega)]; exact hqt
  · obtain rfl : j = k := by omega
    rw [List.getElem?_eq_getElem hk_arr, Option.getD_some] at het
    refine ⟨msz, Nat.lt_succ_self _, ?_⟩
    rw [List.getElem?_set_self hmsz_lt, Option.getD_some, ← fid_litEquiv_eval heqv hα]; exact het

/-! ## 2. `fidFs_clearLm_wp` & `fidFs_mch_init_wp` -/

@[expose] def fidFs_clearLm_expr {V : Ty → Type} {L : List Ty → Type}
    (pLitMark pTmp : V i64) (msz : V i32) (kExit : Expr V L [i64]) : Expr V L [i64] :=
  .group (sig := [[i32]]) (fun Js => .cons (fun p =>
    .let_ ⟨.cmp .ult i32, (.var p.1, (.var msz, ()))⟩ fun p_cmp =>
    .jnz (.var p_cmp.1)
      (.let_ ⟨.zext 32 64, (.var p.1, ())⟩ fun p1 =>
       .let_ ⟨.mul i64, (.var p1.1, (.imm 4, ()))⟩ fun p2 =>
       .let_ ⟨.add i64, (.var pTmp, (.var p2.1, ()))⟩ fun p3 => .load i32 (.var p3.1) fun ld =>
       .let_ ⟨.zext 32 64, (.var ld, ())⟩ fun p4 =>
       .let_ ⟨.add i64, (.var pLitMark, (.var p4.1, ()))⟩ fun p5 =>
       .let_ ⟨.trunc 32 8, (.imm 0, ())⟩ fun p6 =>
       .store (t := i8) (.var p6.1) (.var p5.1)
         (.let_ ⟨.add i32, (.var p.1, (.imm 1, ()))⟩ fun p7 => .jump Js.1 (.var p7.1, ())))
      kExit) .nil) (fun Js => .jump Js.1 (.imm 0, ()))

theorem fidFs_clearLm_wp (Γ : Env) {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cv0 alen0 : Nat} {fuel0 : BitVec 64} {refs0 : List Nat}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {s2 sk st0 : FullState}
    {pLitMark pTmp : Val i64} {msz : Val i32} {m_in : Mem 64} {kExit : Expr Val Cont [i64]}
    (hLm : pLitMark = c.pLitMark) (hTmp : pTmp = c.pTmp) (hm_in : (FullMem c st0 ⋆ R) m_in)
    (hb0 : FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 st0)
    (har0 : st0.core.arena = s2.core.arena) (htmp0 : st0.core.tmp = sk.core.tmp)
    (hscr0 : st0.scratch = s2.scratch) (hmsz_cv : msz.toNat ≤ cv0)
    (htmp_lt : ∀ j < msz.toNat, (sk.core.tmp[j]?.getD 0#32).toNat < 2 * cv0)
    (hlm0 : ∀ l < 2 * c.max_vars, st0.core.lit_mark[l]?.getD 0#8 = 0#8 ∨
      (∃ j, 0 ≤ j ∧ j < msz.toNat ∧ (st0.core.tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv0))
    (hk : ∀ (sc : FullState) (mc : Mem 64),
      FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 sc → sc.core.arena = s2.core.arena →
      sc.core.tmp = sk.core.tmp → sc.scratch = s2.scratch → FullDenseInvW c F0 F_cur sc →
      sc.core.cur_vars = cv0 → sc.core.arena_len = alen0 → sc.core.fuel = fuel0 →
      fullArenaClauseRefs sc = refs0 → FullCongReprInv F_cur (2 * cv0) sc.core.repr →
      (FullMem c sc ⋆ R) mc → wp Γ Q X kExit mc) :
    wp Γ Q X (fidFs_clearLm_expr pLitMark pTmp msz kExit) m_in := by
  subst hLm hTmp; have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le : cv0 ≤ c.max_vars := by rw [← hb0.hcv]; exact hb0.hlen.core_ok.cur_vars_le
  unfold fidFs_clearLm_expr
  refine wp_loop_inv (ts := [i32])
    (fun (kc, ()) mc => ∃ sc : FullState, kc.toNat ≤ msz.toNat ∧
      FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 sc ∧ sc.core.arena = s2.core.arena ∧
      sc.core.tmp = sk.core.tmp ∧ sc.scratch = s2.scratch ∧
      (∀ l < 2 * c.max_vars, sc.core.lit_mark[l]?.getD 0#8 = 0#8 ∨
        (∃ j, kc.toNat ≤ j ∧ j < msz.toNat ∧
          (sc.core.tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv0)) ∧
      (FullMem c sc ⋆ R) mc)
    (fun (kc, ()) _ => msz.toNat - kc.toNat)
    (fun Jc hJc => by
      c0_hsteps!
      exact hJc (0#32, ()) m_in ⟨st0, Nat.zero_le _, hb0, har0, htmp0, hscr0, hlm0, hm_in⟩)
    (fun Jc (kc, ()) mc ⟨sc, hkc_le, hbc, harc, htmpc, hscrc, hlmc, hmc⟩ ihc => ?_)
  c0_hsplit
  · have hkc_lt : kc.toNat < msz.toNat := hc
    have hkc1 : (kc + 1#32).toNat = kc.toNat + 1 := by bv_omega
    have hkc_arr : kc.toNat < sc.core.tmp.length := by have := hbc.hlen.core_ok.tmp_len_arr; omega
    let rk := sc.core.tmp[kc.toNat]'hkc_arr
    have hrk_lt : rk.toNat < 2 * cv0 := by
      have h := htmp_lt kc.toNat hkc_lt
      rwa [← htmpc, List.getElem?_eq_getElem hkc_arr, Option.getD_some] at h
    have hrk_arr : rk.toNat < sc.core.lit_mark.length := hbc.lm_lt hrk_lt
    have hkc_z : (kc.setWidth 64).toNat = kc.toNat := bv_zext32_toNat kc
    have hkc_z_arr : (kc.setWidth 64).toNat < sc.core.tmp.length := by rw [hkc_z]; exact hkc_arr
    have hrk_z_lm : ((sc.core.tmp[(kc.setWidth 64).toNat]'hkc_z_arr).setWidth 64).toNat <
        sc.core.lit_mark.length := by
      rw [list_getElem_congr hkc_z hkc_z_arr hkc_arr, bv_zext32_toNat]; exact hrk_arr
    have hlmc' := fidFs_lm_clear_step hkc_lt hkc_arr hrk_arr hlmc
    clear hc; c0_hsteps!
    let sc' : FullState :=
      { sc with core := { sc.core with lit_mark := sc.core.lit_mark.set rk.toNat 0#8 } }
    have hlm_eq : sc.core.lit_mark.set
        ((sc.core.tmp[(kc.setWidth 64).toNat]'hkc_z_arr).setWidth 64).toNat 0#8 =
        sc.core.lit_mark.set rk.toNat 0#8 :=
      congrArg (sc.core.lit_mark.set · 0#8)
        (by rw [list_getElem_congr hkc_z hkc_z_arr hkc_arr, bv_zext32_toNat])
    rw [hlm_eq] at hm
    exact ihc (kc + 1#32, ()) _ (by dsimp only; omega)
      ⟨sc', by omega, hbc.with_lm (by simp [hbc.hlen.core_ok.lit_mark_len]),
       harc, htmpc, hscrc, by rw [hkc1]; exact hlmc', hm⟩
  · have hkc_eq : kc.toNat = msz.toNat := by omega
    obtain ⟨hdc, hcvc, halc, hflc, hrefsc, hreprc⟩ :=
      hbc.to_dense (fidFs_lm_clear_done (hkc_eq ▸ hlmc))
    exact hk sc mc hbc harc htmpc hscrc hdc hcvc halc hflc hrefsc hreprc hmc

@[expose] def fidFs_mch_init_expr {V : Ty → Type} {L : List Ty → Type}
    (pMinClr pFlags pRepr cv64 : V i64) (kExit : Tup V [i64, .bool] → Expr V L [i64]) :
    Expr V L [i64] :=
  .group (sig := [[i64]]) (fun Ji => .cons (fun p =>
    .let_ ⟨.cmp .ult i64, (.var p.1, (.var cv64, ()))⟩ fun p_lt =>
    .jnz (.var p_lt.1)
      (.let_ ⟨.mul i64, (.var p.1, (.imm 4, ()))⟩ fun p2 =>
       .let_ ⟨.add i64, (.var pMinClr, (.var p2.1, ()))⟩ fun p3 =>
       .store (t := i32) (.imm 0) (.var p3.1)
         (.let_ ⟨.add i64, (.var p.1, (.imm 1, ()))⟩ fun pi1 => .jump Ji.1 (.var pi1.1, ())))
      (.group (sig := [[i64, .bool]]) (fun Jm => .cons (fun pm =>
         .let_ ⟨.cmp .ult i64, (.var pm.1, (.var cv64, ()))⟩ fun pm_lt =>
         .jnz (.var pm_lt.1)
           (.group (sig := [[.bool]]) (fun Jhm => .cons (fun phm =>
              .let_ ⟨.add i64, (.var pm.1, (.imm 1, ()))⟩ fun pm1 =>
              .jump Jm.1 (.var pm1.1, (.var phm.1, ()))) .nil) fun Jhm =>
            .let_ ⟨.mul i64, (.var pm.1, (.imm 4, ()))⟩ fun pm_off =>
            .let_ ⟨.add i64, (.var pFlags, (.var pm_off.1, ()))⟩ fun pm_ptr =>
            .load i32 (.var pm_ptr.1) fun ldf =>
            .let_ ⟨.and i32, (.var ldf, (.imm 1, ()))⟩ fun pm_and =>
            .let_ ⟨.cmp .ne i32, (.var pm_and.1, (.imm 0, ()))⟩ fun pm_ne =>
            .jnz (.var pm_ne.1)
              (.let_ ⟨.sext 32 64, (.imm 1, ())⟩ fun p_s1 =>
               .let_ ⟨.shl i64, (.var pm.1, (.var p_s1.1, ()))⟩ fun p_sh =>
               .let_ ⟨.trunc 64 32, (.var p_sh.1, ())⟩ fun p_lit =>
               .call "full_cong_find" (as := [i64, i32]) (bs := [i32])
                 (Arg.var pRepr, (Arg.var p_lit.1, ())) fun p_rr =>
               .group (sig := [[.bool]]) (fun Jhm2 => .cons (fun phm2 =>
                  .jump Jhm.1 (.var phm2.1, ())) .nil) fun Jhm2 =>
                .let_ ⟨.cmp .ne i32, (.var p_rr.1, (.var p_lit.1, ()))⟩ fun p_neq =>
                .jnz (.var p_neq.1)
                  (.let_ ⟨.mul i64, (.var pm.1, (.imm 4, ()))⟩ fun q1 =>
                   .let_ ⟨.add i64, (.var pMinClr, (.var q1.1, ()))⟩ fun q2 =>
                   .store (t := i32) (.imm 1) (.var q2.1)
                     (.let_ ⟨.lshr i32, (.var p_rr.1, (.imm 1, ()))⟩ fun q3 =>
                      .let_ ⟨.zext 32 64, (.var q3.1, ())⟩ fun q4 =>
                      .let_ ⟨.mul i64, (.var q4.1, (.imm 4, ()))⟩ fun q5 =>
                      .let_ ⟨.add i64, (.var pMinClr, (.var q5.1, ()))⟩ fun q6 =>
                      .store (t := i32) (.imm 1) (.var q6.1) (.jump Jhm2.1 (.imm true, ()))))
                  (.jump Jhm2.1 (.var pm.2.1, ())))
              (.jump Jhm.1 (.var pm.2.1, ())))
           (kExit pm)) .nil) fun Jm => .jump Jm.1 (.imm 0, (.imm false, ())))) .nil)
  fun Ji => .jump Ji.1 (.imm 0, ())

theorem fidFs_mch_init_wp (Γ : Env) (hFind : Γ.Has "full_cong_find" Spec.fullCongFindSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cv0 alen0 : Nat} {fuel0 : BitVec 64}
    {refs0 : List Nat} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {s0 : FullState}
    {m0 : Mem 64} {pMinClr pFlags pRepr cv64 : Val i64}
    {kExit : Tup Val [i64, .bool] → Expr Val Cont [i64]}
    (hMc : pMinClr = c.pMinClr) (hFl : pFlags = c.pFlags) (hRepr : pRepr = c.pRepr)
    (hcv64 : cv64 = BitVec.ofNat 64 cv0) (hd0 : FullDenseInvW c F0 F_cur s0)
    (hcv0 : s0.core.cur_vars = cv0) (hal0 : s0.core.arena_len = alen0)
    (hfl0 : s0.core.fuel = fuel0) (href0 : fullArenaClauseRefs s0 = refs0)
    (hrepr0 : FullCongReprInv F_cur (2 * cv0) s0.core.repr) (hm0 : (FullMem c s0 ⋆ R) m0)
    (hk : ∀ (i2 : Val i64) (hmch : Bool) (si2 : FullState) (mi2 : Mem 64),
      FullDenseInvW c F0 F_cur si2 → si2.core.cur_vars = cv0 → si2.core.arena_len = alen0 →
      si2.core.fuel = fuel0 → fullArenaClauseRefs si2 = refs0 →
      FullCongReprInv F_cur (2 * cv0) si2.core.repr → (FullMem c si2 ⋆ R) mi2 →
      wp Γ Q X (kExit (i2, hmch, ())) mi2) :
    wp Γ Q X (fidFs_mch_init_expr pMinClr pFlags pRepr cv64 kExit) m0 := by
  subst hMc hFl hRepr hcv64; have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le : cv0 ≤ c.max_vars := by rw [← hcv0]; exact hd0.1.core_ok.cur_vars_le
  unfold fidFs_mch_init_expr
  refine wp_loop_inv (ts := [i64])
    (fun (i, ()) mi => ∃ si : FullState, i.toNat ≤ cv0 ∧ FullDenseInvW c F0 F_cur si ∧
      si.core.cur_vars = cv0 ∧ si.core.arena_len = alen0 ∧ si.core.fuel = fuel0 ∧
      fullArenaClauseRefs si = refs0 ∧ FullCongReprInv F_cur (2 * cv0) si.core.repr ∧
      (FullMem c si ⋆ R) mi)
    (fun (i, ()) _ => cv0 - i.toNat)
    (fun J0 hJ0 => by
      c0_hsteps!
      exact hJ0 (0#64, ()) m0 ⟨s0, Nat.zero_le _, hd0, hcv0, hal0, hfl0, href0, hrepr0, hm0⟩)
    (fun J0 (i, ()) mi ⟨si, hi_le, hdi, hcvi, hali, hfli, hrefsi, hrepri, hmi⟩ ihi => ?_)
  have hmli := hdi.1.core_ok.min_clr_len_arr; c0_hsplit
  · have hi_lt : i.toNat < cv0 := by omega
    have hi_arr : i.toNat < si.core.min_clr.length := by omega
    clear hc; c0_hsteps!
    let si' : FullState :=
      { si with core := { si.core with min_clr := si.core.min_clr.set i.toNat 0#32 } }
    exact ihi (i + 1#64, ()) _ (by dsimp only; bv_omega)
      ⟨si', by bv_omega, fid_denseInvW_with_mclr hdi (by simp [hmli]),
       hcvi, hali, hfli, hrefsi, hrepri, hm⟩
  clear hc J0 hi_le hmli ihi hd0 hrepr0 hm0; c0_hsteps_nogrp
  refine wp_loop_inv (ts := [i64, .bool])
    (fun (i2, _hmch, ()) mi2 => ∃ si2 : FullState, i2.toNat ≤ cv0 ∧
      FullDenseInvW c F0 F_cur si2 ∧ si2.core.cur_vars = cv0 ∧ si2.core.arena_len = alen0 ∧
      si2.core.fuel = fuel0 ∧ fullArenaClauseRefs si2 = refs0 ∧
      FullCongReprInv F_cur (2 * cv0) si2.core.repr ∧ (FullMem c si2 ⋆ R) mi2)
    (fun (i2, _, ()) _ => cv0 - i2.toNat)
    (fun Jm hJm => by
      c0_hsteps!
      exact hJm (0#64, false, ()) mi ⟨si, Nat.zero_le _, hdi, hcvi, hali, hfli, hrefsi, hrepri,
        hmi⟩)
    (fun Jm (i2, hmch, ()) mi2 ⟨si2, hi2_le, hdi2, hcvi2, hali2, hfli2, hrefsi2, hrepri2,
      hmi2⟩ ihm => ?_)
  have hfl_len2 := hdi2.1.core_ok.flags_len; have hmli2 := hdi2.1.core_ok.min_clr_len_arr
  c0_hsplit
  · have hi2_lt : i2.toNat < cv0 := by omega
    have hi2_fl : i2.toNat < si2.core.flags.length := by omega
    clear hc; c0_hsteps_nogrp
    refine wp_join_group (ts := [.bool])
      (fun (_hm', ()) mj => ∃ sj : FullState, FullDenseInvW c F0 F_cur sj ∧
        sj.core.cur_vars = cv0 ∧ sj.core.arena_len = alen0 ∧ sj.core.fuel = fuel0 ∧
        fullArenaClauseRefs sj = refs0 ∧ FullCongReprInv F_cur (2 * cv0) sj.core.repr ∧
        (FullMem c sj ⋆ R) mj)
      (fun _ ⟨hm', ⟨⟩⟩ mj ⟨sj, hdj, hcvj, halj, hflj, hrefsj, hreprj, hmj⟩ => by
        c0_hsteps!; exact ihm (i2 + 1#64, hm', ()) mj (by dsimp only; bv_omega)
          ⟨sj, by bv_omega, hdj, hcvj, halj, hflj, hrefsj, hreprj, hmj⟩)
      (fun Jhm hJhm => by
        c0_hsplit; rotate_left 1
        · c0_hsteps!
          exact hJhm (hmch, ()) mi2 ⟨si2, hdi2, hcvi2, hali2, hfli2, hrefsi2, hrepri2, hmi2⟩
        have hlit_n : (BitVec.setWidth 32 (i2 <<< (1 : Nat))).toNat = 2 * i2.toNat := by
          rw [BitVec.toNat_setWidth, bv64_shl1_toNat, Nat.mod_eq_of_lt (by omega),
            Nat.mod_eq_of_lt (by omega)]
        clear hc; c0_hsteps!; c0_hcall hFind
        refine ⟨F_cur, 2 * cv0, si2.core.repr, ArrayField.repr.rest c si2 ⋆ R,
          hrepri2,
          (by change (BitVec.setWidth 32 (i2 <<< (1 : Nat))).toNat < 2 * cv0; rw [hlit_n]; omega),
          focus_full_repr hmi2,
          fun rr repr_r mr hrl_r hrepr_r _ hrr_lt _ hmr => ?_⟩
        let sr : FullState := { si2 with core := { si2.core with repr := repr_r } }
        have hmr' : (FullMem c sr ⋆ R) mr := unfocus_full_repr hmr
        have hdr := fullDenseInvW_with_repr hdi2 (hrl_r.trans hdi2.1.core_ok.repr_len)
        c0_hsteps_nogrp
        refine wp_join_group (ts := [.bool])
          (fun (_hm'', ()) mj => ∃ sj : FullState, FullDenseInvW c F0 F_cur sj ∧
            sj.core.cur_vars = cv0 ∧ sj.core.arena_len = alen0 ∧ sj.core.fuel = fuel0 ∧
            fullArenaClauseRefs sj = refs0 ∧ FullCongReprInv F_cur (2 * cv0) sj.core.repr ∧
            (FullMem c sj ⋆ R) mj)
          (fun _ ⟨hm'', ⟨⟩⟩ mj ⟨sj, hdj, hcvj, halj, hflj, hrefsj, hreprj, hmj⟩ =>
            hJhm (hm'', ()) mj ⟨sj, hdj, hcvj, halj, hflj, hrefsj, hreprj, hmj⟩)
          (fun Jhm2 hJhm2 => by
            c0_hsplit; rotate_left 1
            · c0_hsteps!
              exact hJhm2 (hmch, ()) mr ⟨sr, hdr, hcvi2, hali2, hfli2, hrefsi2, hrepr_r, hmr'⟩
            have hri_mc : i2.toNat < sr.core.min_clr.length := by
              change i2.toNat < si2.core.min_clr.length; omega
            have hrr1_mc : ((rr >>> 1#32).setWidth 64).toNat <
                (sr.core.min_clr.set i2.toNat 1#32).length := by
              rw [List.length_set, bv32_shr1_z64]; change _ < si2.core.min_clr.length; omega
            clear hc; c0_hsteps!
            let sr' : FullState :=
              { sr with core :=
                { sr.core with
                  min_clr := (sr.core.min_clr.set i2.toNat 1#32).set
                    ((rr >>> 1#32).setWidth 64).toNat 1#32 } }
            exact hJhm2 (true, ()) _ ⟨sr', fid_denseInvW_with_mclr
              (mc' := (sr.core.min_clr.set i2.toNat 1#32).set
                ((rr >>> 1#32).setWidth 64).toNat 1#32)
              hdr (by simpa [List.length_set] using hmli2),
              hcvi2, hali2, hfli2, hrefsi2, hrepr_r, hm⟩))
  · exact hk i2 hmch si2 mi2 hdi2 hcvi2 hali2 hfli2 hrefsi2 hrepri2 hmi2

/-! ## 3. Clause Reduction Loops (`fidFs_reduce_k_wp`, `fidFs_pass1_k_wp`) -/

@[expose] def fidFs_reduce_k_expr {V : Ty → Type} {L : List Ty → Type}
    (pRepr pArena pVals pLitMark pTmp cv64 : V i64) (cref csz : V i32)
    (Jk2_ex : L [.bool, .bool, .bool, i32, i32]) : Expr V L [i64] :=
  .group (sig := [[i32, i32]]) (fun Jk => .cons (fun p =>
    .let_ ⟨.cmp .ult i32, (.var p.2.1, (.var csz, ()))⟩ fun p_lt =>
    .jnz (.var p_lt.1)
      (.let_ ⟨.zext 32 64, (.var cref, ())⟩ fun p2 =>
       .let_ ⟨.add i64, (.var p2.1, (.imm 3, ()))⟩ fun p3 =>
       .let_ ⟨.zext 32 64, (.var p.2.1, ())⟩ fun p4 =>
       .let_ ⟨.add i64, (.var p3.1, (.var p4.1, ()))⟩ fun p5 =>
       .let_ ⟨.mul i64, (.var p5.1, (.imm 4, ()))⟩ fun p6 =>
       .let_ ⟨.add i64, (.var pArena, (.var p6.1, ()))⟩ fun p7 => .load i32 (.var p7.1) fun l =>
       .let_ ⟨.zext 32 64, (.var l, ())⟩ fun p8 =>
       .let_ ⟨.add i64, (.var pVals, (.var p8.1, ()))⟩ fun p9 => .load i8 (.var p9.1) fun lv =>
       .let_ ⟨.trunc 32 8, (.imm 0, ())⟩ fun p10 =>
       .let_ ⟨.sext 8 32, (.var lv, ())⟩ fun p11 =>
       .let_ ⟨.sext 8 32, (.var p10.1, ())⟩ fun p12 =>
       .let_ ⟨.cmp .sgt i32, (.var p11.1, (.var p12.1, ()))⟩ fun p13 =>
       .jnz (.var p13.1)
         (.jump Jk2_ex (.imm true, (.imm false, (.imm false, (.var p.1, (.var p.2.1, ()))))))
         (.let_ ⟨.trunc 32 8, (.imm 0, ())⟩ fun p14 =>
          .let_ ⟨.sext 8 32, (.var lv, ())⟩ fun p15 =>
          .let_ ⟨.sext 8 32, (.var p14.1, ())⟩ fun p16 =>
          .let_ ⟨.cmp .slt i32, (.var p15.1, (.var p16.1, ()))⟩ fun p17 =>
          .jnz (.var p17.1)
            (.let_ ⟨.add i32, (.var p.2.1, (.imm 1, ()))⟩ fun p18 =>
             .jump Jk.1 (.var p.1, (.var p18.1, ())))
            (.call "full_cong_find" (as := [i64, i32]) (bs := [i32])
               (Arg.var pRepr, (Arg.var l, ())) fun rr =>
             .let_ ⟨.zext 32 64, (.var rr.1, ())⟩ fun p19 =>
             .let_ ⟨.add i64, (.var pVals, (.var p19.1, ()))⟩ fun p20 =>
             .load i8 (.var p20.1) fun rv =>
             .let_ ⟨.trunc 32 8, (.imm 0, ())⟩ fun p21 =>
             .let_ ⟨.sext 8 32, (.var rv, ())⟩ fun p22 =>
             .let_ ⟨.sext 8 32, (.var p21.1, ())⟩ fun p23 =>
             .let_ ⟨.cmp .sgt i32, (.var p22.1, (.var p23.1, ()))⟩ fun p24 =>
             .jnz (.var p24.1)
               (.jump Jk2_ex (.imm true, (.imm false, (.imm false, (.var p.1, (.var p.2.1, ()))))))
               (.let_ ⟨.trunc 32 8, (.imm 0, ())⟩ fun p25 =>
                .let_ ⟨.sext 8 32, (.var rv, ())⟩ fun p26 =>
                .let_ ⟨.sext 8 32, (.var p25.1, ())⟩ fun p27 =>
                .let_ ⟨.cmp .slt i32, (.var p26.1, (.var p27.1, ()))⟩ fun p28 =>
                .jnz (.var p28.1)
                  (.let_ ⟨.add i32, (.var p.2.1, (.imm 1, ()))⟩ fun p29 =>
                   .jump Jk.1 (.var p.1, (.var p29.1, ())))
                  (.let_ ⟨.xor i32, (.var rr.1, (.imm 1, ()))⟩ fun p29 =>
                   .let_ ⟨.zext 32 64, (.var p29.1, ())⟩ fun p30 =>
                   .let_ ⟨.add i64, (.var pLitMark, (.var p30.1, ()))⟩ fun p31 =>
                   .load i8 (.var p31.1) fun lm1 =>
                   .let_ ⟨.trunc 32 8, (.imm 0, ())⟩ fun p32 =>
                   .let_ ⟨.zext 8 32, (.var lm1, ())⟩ fun p33 =>
                   .let_ ⟨.zext 8 32, (.var p32.1, ())⟩ fun p34 =>
                   .let_ ⟨.cmp .ne i32, (.var p33.1, (.var p34.1, ()))⟩ fun p35 =>
                   .jnz (.var p35.1)
                     (.jump Jk2_ex
                       (.imm false, (.imm true, (.imm false, (.var p.1, (.var p.2.1, ()))))))
                     (.group (sig := [[.bool, i32]]) (fun Jov => .cons (fun p36 =>
                        .let_ ⟨.add i32, (.var p.2.1, (.imm 1, ()))⟩ fun pk1 =>
                        .jump Jk.1 (.var p36.2.1, (.var pk1.1, ()))) .nil) fun Jov =>
                      .let_ ⟨.zext 32 64, (.var rr.1, ())⟩ fun p36 =>
                      .let_ ⟨.add i64, (.var pLitMark, (.var p36.1, ()))⟩ fun p37 =>
                      .load i8 (.var p37.1) fun lm0 =>
                      .let_ ⟨.trunc 32 8, (.imm 0, ())⟩ fun p38 =>
                      .let_ ⟨.zext 8 32, (.var lm0, ())⟩ fun p39 =>
                      .let_ ⟨.zext 8 32, (.var p38.1, ())⟩ fun p40 =>
                      .let_ ⟨.cmp .eq i32, (.var p39.1, (.var p40.1, ()))⟩ fun p41 =>
                      .jnz (.var p41.1)
                        (.let_ ⟨.zext 32 64, (.var p.1, ())⟩ fun p42 =>
                         .let_ ⟨.cmp .ult i64, (.var p42.1, (.var cv64, ()))⟩ fun p43 =>
                         .jnz (.var p43.1)
                           (.let_ ⟨.zext 32 64, (.var rr.1, ())⟩ fun p44 =>
                            .let_ ⟨.add i64, (.var pLitMark, (.var p44.1, ()))⟩ fun p45 =>
                            .let_ ⟨.trunc 32 8, (.imm 1, ())⟩ fun p46 =>
                            .store (t := i8) (.var p46.1) (.var p45.1)
                              (.let_ ⟨.zext 32 64, (.var p.1, ())⟩ fun p47 =>
                               .let_ ⟨.mul i64, (.var p47.1, (.imm 4, ()))⟩ fun p48 =>
                               .let_ ⟨.add i64, (.var pTmp, (.var p48.1, ()))⟩ fun p49 =>
                               .store (t := i32) (.var rr.1) (.var p49.1)
                                 (.let_ ⟨.add i32, (.var p.1, (.imm 1, ()))⟩ fun pm1 =>
                                  .jump Jov.1 (.imm false, (.var pm1.1, ())))))
                           (.jump Jk2_ex
                             (.imm false, (.imm false, (.imm true, (.var p.1, (.var p.2.1, ())))))))
                        (.jump Jov.1 (.imm false, (.var p.1, ())))))))))
      (.jump Jk2_ex (.imm false, (.imm false, (.imm false, (.var p.1, (.var p.2.1, ()))))))
  ) .nil) (fun Jk => .jump Jk.1 (.imm 0, (.imm 0, ())))

theorem fidFs_reduce_k_wp (Γ : Env) (hFind : Γ.Has "full_cong_find" Spec.fullCongFindSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cv0 alen0 : Nat} {fuel0 : BitVec 64}
    {refs0 : List Nat} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {s2 : FullState}
    {m2 : Mem 64} {pRepr pArena pVals pLitMark pTmp cv64 : Val i64} {cref csz : Val i32}
    {Jk2_ex : Cont [.bool, .bool, .bool, i32, i32]}
    (hRepr : pRepr = c.pRepr) (hAr : pArena = c.pArena) (hVals : pVals = c.pVals)
    (hLm : pLitMark = c.pLitMark) (hTmp : pTmp = c.pTmp) (hcv64 : cv64 = BitVec.ofNat 64 cv0)
    (hb_2 : FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 s2) (hinc2 : s2.core.inconsistent = 0#64)
    (hlm_2 : ∀ l < 2 * c.max_vars, s2.core.lit_mark[l]?.getD 0#8 = 0#8)
    (hcref_ref0 : cref.toNat ∈ refs0) (hng_c2 : fullArenaClauseGarb s2 cref.toNat = false)
    (hcsz_eq : fullArenaClauseSizeCore s2.core cref.toNat = csz.toNat)
    (hcr_bd : cref.toNat + 3 + csz.toNat ≤ alen0) (hm2 : (FullMem c s2 ⋆ R) m2)
    (hJk2_ex : ∀ (sat taut ovf : Bool) (msz k_r : Val i32) (mk : Mem 64),
      (∃ sk : FullState, FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 sk ∧
        sk.core.arena = s2.core.arena ∧ sk.core.vals = s2.core.vals ∧
        sk.core.inconsistent = 0#64 ∧ sk.scratch = s2.scratch ∧ msz.toNat ≤ cv0 ∧
        (∀ j < msz.toNat, (sk.core.tmp[j]?.getD 0#32).toNat < 2 * cv0) ∧
        (∀ l < 2 * c.max_vars, sk.core.lit_mark[l]?.getD 0#8 = 0#8 ∨
          (∃ j < msz.toNat, (sk.core.tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv0)) ∧
        (sat = false → taut = false → ovf = false →
          ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α → ∀ j < csz.toNat,
            evalLitVal α (sk.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat = true →
            ∃ q < msz.toNat, evalLitVal α (sk.core.tmp[q]?.getD 0#32).toNat = true) ∧
        (FullMem c sk ⋆ R) mk) → Jk2_ex (sat, taut, ovf, msz, k_r, ()) mk) :
    wp Γ Q X (fidFs_reduce_k_expr pRepr pArena pVals pLitMark pTmp cv64 cref csz Jk2_ex) m2 := by
  subst hRepr hAr hVals hLm hTmp hcv64; have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le : cv0 ≤ c.max_vars := by rw [← hb_2.hcv]; exact hb_2.hlen.core_ok.cur_vars_le
  have hcr_z : (cref.setWidth 64).toNat = cref.toNat := bv_zext32_toNat cref
  unfold fidFs_reduce_k_expr; c0_hsteps_nogrp
  refine wp_loop_inv (ts := [i32, i32])
    (fun (msz, k, ()) mk_in => ∃ sk_in : FullState, k.toNat ≤ csz.toNat ∧
      FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 sk_in ∧ sk_in.core.arena = s2.core.arena ∧
      sk_in.core.vals = s2.core.vals ∧ sk_in.core.inconsistent = 0#64 ∧
      sk_in.scratch = s2.scratch ∧ msz.toNat ≤ cv0 ∧
      (∀ j < msz.toNat, (sk_in.core.tmp[j]?.getD 0#32).toNat < 2 * cv0) ∧
      (∀ l < 2 * c.max_vars, sk_in.core.lit_mark[l]?.getD 0#8 = 0#8 ∨
        (∃ j < msz.toNat, (sk_in.core.tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv0)) ∧
      (∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α → ∀ j < k.toNat,
        evalLitVal α (sk_in.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat = true →
        ∃ q < msz.toNat, evalLitVal α (sk_in.core.tmp[q]?.getD 0#32).toNat = true) ∧
      (FullMem c sk_in ⋆ R) mk_in)
    (fun (_, k, ()) _ => csz.toNat - k.toNat)
    (fun Jk hJk => by
      c0_hsteps!; exact hJk (0#32, 0#32, ()) m2
        ⟨s2, Nat.zero_le _, hb_2, rfl, rfl, hinc2, rfl, Nat.zero_le _,
         (fun _ hj => absurd hj (Nat.not_lt_zero _)), fun l hl => Or.inl (hlm_2 l hl),
         (fun _ _ _ hj _ => absurd hj (Nat.not_lt_zero _)), hm2⟩)
    (fun Jk (msz, k, ()) mk_in ⟨sk_in, hk_le, hb_in, har_in, hvl_in, hinc_in, hscr_in,
      hmsz_cv, htmp_lt_in, hlm_ok_in, hsem_in, hmk_in⟩ ihk => ?_)
  c0_hsplit; rotate_left 1
  · have hk_eq : k.toNat = csz.toNat := by omega
    c0_hsteps!; exact hJk2_ex false false false msz k mk_in
      ⟨sk_in, hb_in, har_in, hvl_in, hinc_in, hscr_in, hmsz_cv,
       htmp_lt_in, hlm_ok_in, fun _ _ _ => hk_eq ▸ hsem_in, hmk_in⟩
  have hk_lt : k.toNat < csz.toNat := hc; have hk1 : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
  obtain ⟨hl_arr, hl_lt⟩ := fidFs_k_lit_lt (p := cref.setWidth 64) hb_in har_in
    (by rw [hcr_z]; exact hcref_ref0) (by rw [hcr_z]; exact hng_c2)
    (by rw [hcr_z]; exact hcsz_eq) (by rw [hcr_z]; exact hcr_bd) hk_lt
  let l := sk_in.core.arena[(cref.setWidth 64 + 3#64 + k.setWidth 64).toNat]'hl_arr
  have hpk_n : (cref.setWidth 64 + 3#64 + k.setWidth 64).toNat = cref.toNat + 3 + k.toNat := by
    bv_omega
  have har_k_pk : cref.toNat + 3 + k.toNat < sk_in.core.arena.length := by
    rw [har_in, hb_2.hlen.core_ok.arena_len_arr]; have := hb_2.hlen.core_ok.arena_len_le
    have := hb_2.hal; omega
  have hl_get : sk_in.core.arena[cref.toNat + 3 + k.toNat]'har_k_pk = l :=
    list_getElem_congr hpk_n.symm _ _
  have hl_vl : l.toNat < sk_in.core.vals.length := hb_in.vals_lt hl_lt
  have hl_z : (l.setWidth 64).toNat = l.toNat := bv_zext32_toNat l
  have hl_vl_z : (l.setWidth 64).toNat < sk_in.core.vals.length := by rw [hl_z]; exact hl_vl
  clear hc; c0_hsplit
  · c0_hsteps!; exact hJk2_ex true false false msz k mk_in
      ⟨sk_in, hb_in, har_in, hvl_in, hinc_in, hscr_in, hmsz_cv,
       htmp_lt_in, hlm_ok_in, (fun h => Bool.noConfusion h), hmk_in⟩
  clear hc; c0_hsplit
  · have hlt_v : (sk_in.core.vals[(sk_in.core.arena[cref.toNat + 3 +
        k.toNat]'har_k_pk).toNat]?.getD 0#8).slt 0#8 = true := by
      rw [hl_get, List.getElem?_eq_getElem hl_vl, Option.getD_some]
      exact bv8_sext32_slt0_true (by
        have h_idx : (BitVec.toNat cref + BitVec.toNat (3 : BitVec 64) +
            BitVec.toNat k) % 2 ^ 64 =
            (cref.setWidth 64 + 3#64 + k.setWidth 64).toNat := by bv_omega
        simpa only [list_getElem_congr h_idx (h_idx ▸ hl_arr) hl_arr] using hc)
    have hsem' := fidFs_k_sem_false hb_in.hw hb_in.hcl hb_in.hcv
      hsem_in har_k_pk (by rw [hl_get]; exact hl_lt) hlt_v
    c0_hsteps!; exact ihk (msz, k + 1#32, ()) mk_in (by dsimp only; omega)
      ⟨sk_in, by omega, hb_in, har_in, hvl_in, hinc_in, hscr_in, hmsz_cv,
       htmp_lt_in, hlm_ok_in, by rw [hk1]; exact hsem', hmk_in⟩
  clear hc; c0_hsteps!; c0_hcall hFind
  refine ⟨F_cur, 2 * cv0, sk_in.core.repr, ArrayField.repr.rest c sk_in ⋆ R,
    hb_in.hrepr, hl_lt, focus_full_repr hmk_in,
    fun r repr_r mr hrl_r hrepr_r _ hr_lt heqv_lr hmr => ?_⟩
  let sk_r : FullState := { sk_in with core := { sk_in.core with repr := repr_r } }
  have hmr' : (FullMem c sk_r ⋆ R) mr := unfocus_full_repr hmr
  have hb_r := hb_in.with_repr (hrl_r.trans hb_in.hlen.core_ok.repr_len) hrepr_r
  have hr_vl : r.toNat < sk_r.core.vals.length := hb_r.vals_lt hr_lt
  have hr_lm : r.toNat < sk_r.core.lit_mark.length := hb_r.lm_lt hr_lt
  have hr1_lm : (r ^^^ 1#32).toNat < sk_r.core.lit_mark.length := by
    rw [bv32_xor1_eq_litNeg]; exact hb_r.lm_lt (bv32_xor1_lt_even hr_lt)
  have hr_z : (r.setWidth 64).toNat = r.toNat := bv_zext32_toNat r
  have hr_vl_z : (r.setWidth 64).toNat < sk_r.core.vals.length := by rw [hr_z]; exact hr_vl
  have hr_lm_z : (r.setWidth 64).toNat < sk_r.core.lit_mark.length := by rw [hr_z]; exact hr_lm
  have hr1_lm_z : ((r ^^^ 1#32).setWidth 64).toNat < sk_r.core.lit_mark.length := by
    rw [bv_zext32_toNat]; exact hr1_lm
  have heqv_pk : LitEquiv (cnfOfClauses F_cur)
      (sk_r.core.arena[cref.toNat + 3 + k.toNat]'har_k_pk).toNat r.toNat := by
    change LitEquiv (cnfOfClauses F_cur)
      (sk_in.core.arena[cref.toNat + 3 + k.toNat]'har_k_pk).toNat r.toNat
    rw [hl_get]; exact heqv_lr
  c0_hsplit
  · c0_hsteps!; exact hJk2_ex true false false msz k mr
      ⟨sk_r, hb_r, har_in, hvl_in, hinc_in, hscr_in, hmsz_cv,
       htmp_lt_in, hlm_ok_in, (fun h => Bool.noConfusion h), hmr'⟩
  clear hc; c0_hsplit
  · have hr_slt : (sk_r.core.vals[r.toNat]?.getD 0#8).slt 0#8 = true := by
      rw [List.getElem?_eq_getElem hr_vl, Option.getD_some]
      exact bv8_sext32_slt0_true (by simpa only [hr_z] using hc)
    have hsem' := fidFs_k_sem_equiv hb_r.hw hb_r.hcl hb_r.hcv
      hsem_in har_k_pk hr_lt heqv_pk hr_slt
    c0_hsteps!; exact ihk (msz, k + 1#32, ()) mr (by dsimp only; omega)
      ⟨sk_r, by omega, hb_r, har_in, hvl_in, hinc_in, hscr_in, hmsz_cv,
       htmp_lt_in, hlm_ok_in, by rw [hk1]; exact hsem', hmr'⟩
  clear hc; c0_hsplit
  · c0_hsteps!; exact hJk2_ex false true false msz k mr
      ⟨sk_r, hb_r, har_in, hvl_in, hinc_in, hscr_in, hmsz_cv,
       htmp_lt_in, hlm_ok_in, (fun _ h => Bool.noConfusion h), hmr'⟩
  clear hc; c0_hsteps_nogrp
  refine wp_join_group (ts := [.bool, i32])
    (fun (ovf', msz', ()) m1 => ∃ sk1 : FullState, ovf' = false ∧ msz'.toNat ≤ cv0 ∧
      FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 sk1 ∧ sk1.core.arena = s2.core.arena ∧
      sk1.core.vals = s2.core.vals ∧ sk1.core.inconsistent = 0#64 ∧ sk1.scratch = s2.scratch ∧
      (∀ j < msz'.toNat, (sk1.core.tmp[j]?.getD 0#32).toNat < 2 * cv0) ∧
      (∀ l < 2 * c.max_vars, sk1.core.lit_mark[l]?.getD 0#8 = 0#8 ∨
        (∃ j < msz'.toNat, (sk1.core.tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv0)) ∧
      (∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α → ∀ j < k.toNat + 1,
        evalLitVal α (sk1.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat = true →
        ∃ q < msz'.toNat, evalLitVal α (sk1.core.tmp[q]?.getD 0#32).toNat = true) ∧
      (FullMem c sk1 ⋆ R) m1)
    (fun _ ⟨_, msz', ⟨⟩⟩ m1 ⟨sk1, _, hmsz', hb1, har1, hvl1, hinc1, hscr1, htmp1, hlm1, hsem1,
      hm1⟩ => by
      c0_hsteps!; exact ihk (msz', k + 1#32, ()) m1 (by dsimp only; omega)
        ⟨sk1, by omega, hb1, har1, hvl1, hinc1, hscr1, hmsz', htmp1, hlm1,
          by rw [hk1]; exact hsem1, hm1⟩)
    ?_
  intro Jov hJov; c0_hsplit; rotate_left 1
  · have hneq : sk_r.core.lit_mark[r.toNat]?.getD 0#8 ≠ 0#8 := by
      rw [List.getElem?_eq_getElem hr_lm, Option.getD_some]
      exact bv8_zext32_beq0_false (by simp only [beq_eq_false_iff_ne]; exact hc)
    have hsem' := fidFs_k_sem_mem hsem_in har_k_pk hr_lt hcv_le hlm_ok_in hneq heqv_pk
    c0_hsteps!; exact hJov (false, msz, ()) mr
      ⟨sk_r, rfl, hmsz_cv, hb_r, har_in, hvl_in, hinc_in, hscr_in,
       htmp_lt_in, hlm_ok_in, hsem', hmr'⟩
  clear hc; c0_hsplit; rotate_left 1
  · c0_hsteps!; exact hJk2_ex false false true msz k mr
      ⟨sk_r, hb_r, har_in, hvl_in, hinc_in, hscr_in, hmsz_cv,
       htmp_lt_in, hlm_ok_in, (fun _ _ h => Bool.noConfusion h), hmr'⟩
  have hmsz_lt : msz.toNat < cv0 := by omega
  have hmsz1 : (msz + 1#32).toNat = msz.toNat + 1 := by bv_omega
  have hmsz_arr : msz.toNat < sk_r.core.tmp.length := by
    have := hb_r.hlen.core_ok.tmp_len_arr; dsimp only [sk_r] at this ⊢; omega
  have hmsz_z : (msz.setWidth 64).toNat = msz.toNat := bv_zext32_toNat msz
  have hmsz_z_arr : (msz.setWidth 64).toNat < sk_r.core.tmp.length := by rw [hmsz_z]; exact hmsz_arr
  clear hc; c0_hsteps!
  obtain ⟨htmp', hlm'⟩ := fidFs_lm_set_mark htmp_lt_in hlm_ok_in hr_lt hmsz_arr
  have hsem' := fidFs_k_sem_push hsem_in har_k_pk hmsz_arr heqv_pk
  let sk1 : FullState :=
    { sk_r with core :=
      { sk_r.core with tmp :=
        sk_r.core.tmp.set msz.toNat r, lit_mark := sk_r.core.lit_mark.set r.toNat 1#8 } }
  rw [hmsz_z, hr_z] at hm
  exact hJov (false, msz + 1#32, ()) _
    ⟨sk1, rfl, by omega,
     hb_r.with_tmp_lm (by simpa [List.length_set] using hb_r.hlen.core_ok.tmp_len_arr)
       (by simpa [List.length_set] using hb_r.hlen.core_ok.lit_mark_len),
     har_in, hvl_in, hinc_in, hscr_in, by rw [hmsz1]; exact htmp',
     by rw [hmsz1]; exact hlm', by rw [hmsz1]; exact hsem', hm⟩

@[expose] def fidFs_pass1_k_expr {V : Ty → Type} {L : List Ty → Type}
    (pRepr pMinClr pArena pVals pLitMark pTmp p64 cv64 : V i64) (sz : V i32)
    (Jk1_ex : L [.bool, .bool, .bool, .bool, i32, i32]) : Expr V L [i64] :=
  .group (sig := [[.bool, i32, i32]]) (fun Jk => .cons (fun p =>
    .let_ ⟨.cmp .ult i32, (.var p.2.2.1, (.var sz, ()))⟩ fun p_lt =>
    .jnz (.var p_lt.1)
      (.let_ ⟨.add i64, (.var p64, (.imm 3, ()))⟩ fun p2 =>
       .let_ ⟨.zext 32 64, (.var p.2.2.1, ())⟩ fun p3 =>
       .let_ ⟨.add i64, (.var p2.1, (.var p3.1, ()))⟩ fun p4 =>
       .let_ ⟨.mul i64, (.var p4.1, (.imm 4, ()))⟩ fun p5 =>
       .let_ ⟨.add i64, (.var pArena, (.var p5.1, ()))⟩ fun p6 => .load i32 (.var p6.1) fun l =>
       .let_ ⟨.zext 32 64, (.var l, ())⟩ fun p7 =>
       .let_ ⟨.add i64, (.var pVals, (.var p7.1, ()))⟩ fun p8 => .load i8 (.var p8.1) fun lv =>
       .let_ ⟨.trunc 32 8, (.imm 0, ())⟩ fun p9 =>
       .let_ ⟨.sext 8 32, (.var lv, ())⟩ fun p10 =>
       .let_ ⟨.sext 8 32, (.var p9.1, ())⟩ fun p11 =>
       .let_ ⟨.cmp .sgt i32, (.var p10.1, (.var p11.1, ()))⟩ fun p12 =>
       .jnz (.var p12.1)
         (.jump Jk1_ex (.imm true, (.imm false, (.var p.1, (.imm false, (.var p.2.1, (.var p.2.2.1,
           ())))))))
         (.let_ ⟨.trunc 32 8, (.imm 0, ())⟩ fun p13 =>
          .let_ ⟨.sext 8 32, (.var lv, ())⟩ fun p14 =>
          .let_ ⟨.sext 8 32, (.var p13.1, ())⟩ fun p15 =>
          .let_ ⟨.cmp .slt i32, (.var p14.1, (.var p15.1, ()))⟩ fun p16 =>
          .jnz (.var p16.1)
            (.let_ ⟨.add i32, (.var p.2.2.1, (.imm 1, ()))⟩ fun p17 =>
             .jump Jk.1 (.var p.1, (.var p.2.1, (.var p17.1, ()))))
            (.group (sig := [[.bool]]) (fun Jcm => .cons (fun p17 =>
               .call "full_cong_find" (as := [i64, i32]) (bs := [i32])
                 (Arg.var pRepr, (Arg.var l, ())) fun rr =>
               .let_ ⟨.zext 32 64, (.var rr.1, ())⟩ fun p18 =>
               .let_ ⟨.add i64, (.var pVals, (.var p18.1, ()))⟩ fun p19 =>
               .load i8 (.var p19.1) fun rv =>
               .let_ ⟨.trunc 32 8, (.imm 0, ())⟩ fun p20 =>
               .let_ ⟨.sext 8 32, (.var rv, ())⟩ fun p21 =>
               .let_ ⟨.sext 8 32, (.var p20.1, ())⟩ fun p22 =>
               .let_ ⟨.cmp .sgt i32, (.var p21.1, (.var p22.1, ()))⟩ fun p23 =>
               .jnz (.var p23.1)
                 (.jump Jk1_ex (.imm true, (.imm false, (.var p17.1, (.imm false, (.var p.2.1,
                   (.var p.2.2.1, ())))))))
                 (.let_ ⟨.trunc 32 8, (.imm 0, ())⟩ fun p24 =>
                  .let_ ⟨.sext 8 32, (.var rv, ())⟩ fun p25 =>
                  .let_ ⟨.sext 8 32, (.var p24.1, ())⟩ fun p26 =>
                  .let_ ⟨.cmp .slt i32, (.var p25.1, (.var p26.1, ()))⟩ fun p27 =>
                  .jnz (.var p27.1)
                    (.let_ ⟨.add i32, (.var p.2.2.1, (.imm 1, ()))⟩ fun p28 =>
                     .jump Jk.1 (.var p17.1, (.var p.2.1, (.var p28.1, ()))))
                    (.let_ ⟨.xor i32, (.var rr.1, (.imm 1, ()))⟩ fun p28 =>
                     .let_ ⟨.zext 32 64, (.var p28.1, ())⟩ fun p29 =>
                     .let_ ⟨.add i64, (.var pLitMark, (.var p29.1, ()))⟩ fun p30 =>
                     .load i8 (.var p30.1) fun lm1 =>
                     .let_ ⟨.trunc 32 8, (.imm 0, ())⟩ fun p31 =>
                     .let_ ⟨.zext 8 32, (.var lm1, ())⟩ fun p32 =>
                     .let_ ⟨.zext 8 32, (.var p31.1, ())⟩ fun p33 =>
                     .let_ ⟨.cmp .ne i32, (.var p32.1, (.var p33.1, ()))⟩ fun p34 =>
                     .jnz (.var p34.1)
                       (.jump Jk1_ex (.imm false, (.imm true, (.var p17.1, (.imm false,
                         (.var p.2.1, (.var p.2.2.1, ())))))))
                       (.group (sig := [[.bool, i32]]) (fun Jov => .cons (fun p35 =>
                          .let_ ⟨.add i32, (.var p.2.2.1, (.imm 1, ()))⟩ fun pk1 =>
                          .jump Jk.1 (.var p17.1, (.var p35.2.1, (.var pk1.1,
                            ())))) .nil) fun Jov =>
                        .let_ ⟨.zext 32 64, (.var rr.1, ())⟩ fun p35 =>
                        .let_ ⟨.add i64, (.var pLitMark, (.var p35.1, ()))⟩ fun p36 =>
                        .load i8 (.var p36.1) fun lm0 =>
                        .let_ ⟨.trunc 32 8, (.imm 0, ())⟩ fun p37 =>
                        .let_ ⟨.zext 8 32, (.var lm0, ())⟩ fun p38 =>
                        .let_ ⟨.zext 8 32, (.var p37.1, ())⟩ fun p39 =>
                        .let_ ⟨.cmp .eq i32, (.var p38.1, (.var p39.1, ()))⟩ fun p40 =>
                        .jnz (.var p40.1)
                          (.let_ ⟨.zext 32 64, (.var p.2.1, ())⟩ fun p41 =>
                           .let_ ⟨.cmp .ult i64, (.var p41.1, (.var cv64, ()))⟩ fun p42 =>
                           .jnz (.var p42.1)
                             (.let_ ⟨.zext 32 64, (.var rr.1, ())⟩ fun p43 =>
                              .let_ ⟨.add i64, (.var pLitMark, (.var p43.1, ()))⟩ fun p44 =>
                              .let_ ⟨.trunc 32 8, (.imm 1, ())⟩ fun p45 =>
                              .store (t := i8) (.var p45.1) (.var p44.1)
                                (.let_ ⟨.zext 32 64, (.var p.2.1, ())⟩ fun p46 =>
                                 .let_ ⟨.mul i64, (.var p46.1, (.imm 4, ()))⟩ fun p47 =>
                                 .let_ ⟨.add i64, (.var pTmp, (.var p47.1, ()))⟩ fun p48 =>
                                 .store (t := i32) (.var rr.1) (.var p48.1)
                                   (.let_ ⟨.add i32, (.var p.2.1, (.imm 1, ()))⟩ fun pm1 =>
                                    .jump Jov.1 (.imm false, (.var pm1.1, ())))))
                             (.jump Jk1_ex (.imm false, (.imm false, (.var p17.1, (.imm true,
                               (.var p.2.1, (.var p.2.2.1, ()))))))))
                          (.jump Jov.1 (.imm false, (.var p.2.1, ()))))))) .nil)
             fun Jcm =>
             .let_ ⟨.lshr i32, (.var l, (.imm 1, ()))⟩ fun q1 =>
             .let_ ⟨.zext 32 64, (.var q1.1, ())⟩ fun q2 =>
             .let_ ⟨.mul i64, (.var q2.1, (.imm 4, ()))⟩ fun q3 =>
             .let_ ⟨.add i64, (.var pMinClr, (.var q3.1, ()))⟩ fun q4 =>
               .load i32 (.var q4.1) fun lmch =>
             .let_ ⟨.cmp .ne i32, (.var lmch, (.imm 0, ()))⟩ fun q5 =>
             .jnz (.var q5.1) (.jump Jcm.1 (.imm true, ())) (.jump Jcm.1 (.var p.1, ())))))
      (.jump Jk1_ex (.imm false, (.imm false, (.var p.1, (.imm false, (.var p.2.1, (.var p.2.2.1,
        ())))))))
  ) .nil) (fun Jk => .jump Jk.1 (.imm false, (.imm 0, (.imm 0, ()))))

theorem fidFs_pass1_k_wp (Γ : Env) (hFind : Γ.Has "full_cong_find" Spec.fullCongFindSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {cv0 alen0 : Nat} {fuel0 : BitVec 64}
    {refs0 : List Nat} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {sp : FullState}
    {mp : Mem 64} {pRepr pMinClr pArena pVals pLitMark pTmp p64 cv64 : Val i64} {sz : Val i32}
    {Jk1_ex : Cont [.bool, .bool, .bool, .bool, i32, i32]}
    (hRepr : pRepr = c.pRepr) (hMc : pMinClr = c.pMinClr) (hAr : pArena = c.pArena)
    (hVals : pVals = c.pVals) (hLm : pLitMark = c.pLitMark) (hTmp : pTmp = c.pTmp)
    (hcv64 : cv64 = BitVec.ofNat 64 cv0) (hb_p : FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 sp)
    (hinc0 : sp.core.inconsistent = 0#64)
    (hlm_p : ∀ l < 2 * c.max_vars, sp.core.lit_mark[l]?.getD 0#8 = 0#8)
    (hp_ref0 : p64.toNat ∈ refs0) (hng_p : fullArenaClauseGarb sp p64.toNat = false)
    (hsz_eq : fullArenaClauseSizeCore sp.core p64.toNat = sz.toNat)
    (hp_bd : p64.toNat + 3 + sz.toNat ≤ alen0) (hmp : (FullMem c sp ⋆ R) mp)
    (hJk1_ex : ∀ (sat taut c_mch ovf : Bool) (msz k_r : Val i32) (mk : Mem 64),
      (∃ sk : FullState, FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 sk ∧
        sk.core.arena = sp.core.arena ∧ sk.core.vals = sp.core.vals ∧
        sk.core.min_clr = sp.core.min_clr ∧ sk.core.inconsistent = 0#64 ∧
        sk.scratch = sp.scratch ∧ msz.toNat ≤ cv0 ∧
        (∀ j < msz.toNat, (sk.core.tmp[j]?.getD 0#32).toNat < 2 * cv0) ∧
        (∀ l < 2 * c.max_vars, sk.core.lit_mark[l]?.getD 0#8 = 0#8 ∨
          (∃ j < msz.toNat, (sk.core.tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv0)) ∧
        (sat = false → taut = false → ovf = false →
          ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α → ∀ j < sz.toNat,
            evalLitVal α (sk.core.arena[p64.toNat + 3 + j]?.getD 0#32).toNat = true →
            ∃ q < msz.toNat, evalLitVal α (sk.core.tmp[q]?.getD 0#32).toNat = true) ∧
        (FullMem c sk ⋆ R) mk) → Jk1_ex (sat, taut, c_mch, ovf, msz, k_r, ()) mk) :
    wp Γ Q X (fidFs_pass1_k_expr pRepr pMinClr pArena pVals pLitMark pTmp p64 cv64 sz Jk1_ex)
      mp := by
  subst hRepr hMc hAr hVals hLm hTmp hcv64; have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv_le : cv0 ≤ c.max_vars := by rw [← hb_p.hcv]; exact hb_p.hlen.core_ok.cur_vars_le
  unfold fidFs_pass1_k_expr; c0_hsteps_nogrp
  refine wp_loop_inv (ts := [.bool, i32, i32])
    (fun (_c_mch, msz, k, ()) mk_in => ∃ sk_in : FullState, k.toNat ≤ sz.toNat ∧
      FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 sk_in ∧ sk_in.core.arena = sp.core.arena ∧
      sk_in.core.vals = sp.core.vals ∧ sk_in.core.min_clr = sp.core.min_clr ∧
      sk_in.core.inconsistent = 0#64 ∧ sk_in.scratch = sp.scratch ∧ msz.toNat ≤ cv0 ∧
      (∀ j < msz.toNat, (sk_in.core.tmp[j]?.getD 0#32).toNat < 2 * cv0) ∧
      (∀ l < 2 * c.max_vars, sk_in.core.lit_mark[l]?.getD 0#8 = 0#8 ∨
        (∃ j < msz.toNat, (sk_in.core.tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv0)) ∧
      (∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α → ∀ j < k.toNat,
        evalLitVal α (sk_in.core.arena[p64.toNat + 3 + j]?.getD 0#32).toNat = true →
        ∃ q < msz.toNat, evalLitVal α (sk_in.core.tmp[q]?.getD 0#32).toNat = true) ∧
      (FullMem c sk_in ⋆ R) mk_in)
    (fun (_, _, k, ()) _ => sz.toNat - k.toNat)
    (fun Jk hJk => by
      c0_hsteps!; exact hJk (false, 0#32, 0#32, ()) mp
        ⟨sp, Nat.zero_le _, hb_p, rfl, rfl, rfl, hinc0, rfl, Nat.zero_le _,
         (fun _ hj => absurd hj (Nat.not_lt_zero _)), fun l hl => Or.inl (hlm_p l hl),
         (fun _ _ _ hj _ => absurd hj (Nat.not_lt_zero _)), hmp⟩)
    (fun Jk (c_mch, msz, k, ()) mk_in ⟨sk_in, hk_le, hb_in, har_in, hvl_in, hmc_in,
      hinc_in, hscr_in, hmsz_cv, htmp_lt_in, hlm_ok_in, hsem_in, hmk_in⟩ ihk => ?_)
  c0_hsplit; rotate_left 1
  · have hk_eq : k.toNat = sz.toNat := by omega
    c0_hsteps!; exact hJk1_ex false false c_mch false msz k mk_in
      ⟨sk_in, hb_in, har_in, hvl_in, hmc_in, hinc_in, hscr_in, hmsz_cv,
       htmp_lt_in, hlm_ok_in, fun _ _ _ => hk_eq ▸ hsem_in, hmk_in⟩
  have hk_lt : k.toNat < sz.toNat := hc; have hk1 : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
  obtain ⟨hl_arr, hl_lt⟩ := fidFs_k_lit_lt hb_in har_in hp_ref0 hng_p hsz_eq hp_bd hk_lt
  let l := sk_in.core.arena[(p64 + 3#64 + k.setWidth 64).toNat]'hl_arr
  have hac := c.harena; unfold dimacsBound at hac
  have hal_le := hb_in.hlen.core_ok.arena_len_le
  have hal_arr := hb_in.hlen.core_ok.arena_len_arr
  have hal_eq := hb_in.hal
  have hpk_n : (p64 + 3#64 + k.setWidth 64).toNat = p64.toNat + 3 + k.toNat := by bv_omega
  have har_k_pk : p64.toNat + 3 + k.toNat < sk_in.core.arena.length := by
    rw [har_in, hb_p.hlen.core_ok.arena_len_arr]; have := hb_p.hal; omega
  have hl_get : sk_in.core.arena[p64.toNat + 3 + k.toNat]'har_k_pk = l :=
    list_getElem_congr hpk_n.symm _ _
  have hl_vl : l.toNat < sk_in.core.vals.length := hb_in.vals_lt hl_lt
  have hl_z : (l.setWidth 64).toNat = l.toNat := bv_zext32_toNat l
  have hl_vl_z : (l.setWidth 64).toNat < sk_in.core.vals.length := by rw [hl_z]; exact hl_vl
  clear hc; c0_hsplit
  · c0_hsteps!; exact hJk1_ex true false c_mch false msz k mk_in
      ⟨sk_in, hb_in, har_in, hvl_in, hmc_in, hinc_in, hscr_in, hmsz_cv,
       htmp_lt_in, hlm_ok_in, (fun h => Bool.noConfusion h), hmk_in⟩
  clear hc; c0_hsplit
  · have hlt_v : (sk_in.core.vals[(sk_in.core.arena[p64.toNat + 3 +
        k.toNat]'har_k_pk).toNat]?.getD 0#8).slt 0#8 = true := by
      rw [hl_get, List.getElem?_eq_getElem hl_vl, Option.getD_some]
      exact bv8_sext32_slt0_true (by
        have h_idx : (BitVec.toNat p64 + BitVec.toNat (3 : BitVec 64) +
            BitVec.toNat k) % 2 ^ 64 =
            (p64 + 3#64 + k.setWidth 64).toNat := by bv_omega
        simpa only [list_getElem_congr h_idx (h_idx ▸ hl_arr) hl_arr] using hc)
    have hsem' := fidFs_k_sem_false hb_in.hw hb_in.hcl hb_in.hcv
      hsem_in har_k_pk (by rw [hl_get]; exact hl_lt) hlt_v
    c0_hsteps!; exact ihk (c_mch, msz, k + 1#32, ()) mk_in (by dsimp only; omega)
      ⟨sk_in, by omega, hb_in, har_in, hvl_in, hmc_in, hinc_in, hscr_in, hmsz_cv,
       htmp_lt_in, hlm_ok_in, by rw [hk1]; exact hsem', hmk_in⟩
  have hl1_mc : ((l >>> 1#32).setWidth 64).toNat < sk_in.core.min_clr.length := by
    have hl_lt' : l.toNat < 2 * cv0 := hl_lt
    rw [bv32_shr1_z64, hb_in.hlen.core_ok.min_clr_len_arr]; omega
  clear hc; c0_hsteps_nogrp
  refine wp_join_group (ts := [.bool]) (fun _ mc1 => mk_in = mc1) ?_
    (fun Jcm hJcm => by
      c0_hsplit
      · c0_hsteps!; exact hJcm (true, ()) mk_in rfl
      · c0_hsteps!; exact hJcm (c_mch, ()) mk_in rfl)
  rintro _ ⟨c_mch', ⟨⟩⟩ mc1 rfl
  c0_hsteps!; c0_hcall hFind
  refine ⟨F_cur, 2 * cv0, sk_in.core.repr, ArrayField.repr.rest c sk_in ⋆ R,
    hb_in.hrepr, hl_lt, focus_full_repr hmk_in,
    fun r repr_r mr hrl_r hrepr_r _ hr_lt heqv_lr hmr => ?_⟩
  let sk_r : FullState := { sk_in with core := { sk_in.core with repr := repr_r } }
  have hmr' : (FullMem c sk_r ⋆ R) mr := unfocus_full_repr hmr
  have hb_r := hb_in.with_repr (hrl_r.trans hb_in.hlen.core_ok.repr_len) hrepr_r
  have hr_vl : r.toNat < sk_r.core.vals.length := hb_r.vals_lt hr_lt
  have hr_lm : r.toNat < sk_r.core.lit_mark.length := hb_r.lm_lt hr_lt
  have hr1_lm : (r ^^^ 1#32).toNat < sk_r.core.lit_mark.length := by
    rw [bv32_xor1_eq_litNeg]; exact hb_r.lm_lt (bv32_xor1_lt_even hr_lt)
  have hr_z : (r.setWidth 64).toNat = r.toNat := bv_zext32_toNat r
  have hr_vl_z : (r.setWidth 64).toNat < sk_r.core.vals.length := by rw [hr_z]; exact hr_vl
  have hr_lm_z : (r.setWidth 64).toNat < sk_r.core.lit_mark.length := by rw [hr_z]; exact hr_lm
  have hr1_lm_z : ((r ^^^ 1#32).setWidth 64).toNat < sk_r.core.lit_mark.length := by
    rw [bv_zext32_toNat]; exact hr1_lm
  have heqv_pk : LitEquiv (cnfOfClauses F_cur)
      (sk_r.core.arena[p64.toNat + 3 + k.toNat]'har_k_pk).toNat r.toNat := by
    change LitEquiv (cnfOfClauses F_cur)
      (sk_in.core.arena[p64.toNat + 3 + k.toNat]'har_k_pk).toNat r.toNat
    rw [hl_get]; exact heqv_lr
  c0_hsplit
  · c0_hsteps!; exact hJk1_ex true false c_mch' false msz k mr
      ⟨sk_r, hb_r, har_in, hvl_in, hmc_in, hinc_in, hscr_in, hmsz_cv,
       htmp_lt_in, hlm_ok_in, (fun h => Bool.noConfusion h), hmr'⟩
  clear hc; c0_hsplit
  · have hr_slt : (sk_r.core.vals[r.toNat]?.getD 0#8).slt 0#8 = true := by
      rw [List.getElem?_eq_getElem hr_vl, Option.getD_some]
      exact bv8_sext32_slt0_true (by simpa only [hr_z] using hc)
    have hsem' := fidFs_k_sem_equiv hb_r.hw hb_r.hcl hb_r.hcv
      hsem_in har_k_pk hr_lt heqv_pk hr_slt
    c0_hsteps!; exact ihk (c_mch', msz, k + 1#32, ()) mr (by dsimp only; omega)
      ⟨sk_r, by omega, hb_r, har_in, hvl_in, hmc_in, hinc_in, hscr_in, hmsz_cv,
       htmp_lt_in, hlm_ok_in, by rw [hk1]; exact hsem', hmr'⟩
  clear hc; c0_hsplit
  · c0_hsteps!; exact hJk1_ex false true c_mch' false msz k mr
      ⟨sk_r, hb_r, har_in, hvl_in, hmc_in, hinc_in, hscr_in, hmsz_cv,
       htmp_lt_in, hlm_ok_in, (fun _ h => Bool.noConfusion h), hmr'⟩
  clear hc; c0_hsteps_nogrp
  refine wp_join_group (ts := [.bool, i32])
    (fun (ovf', msz', ()) m1 => ∃ sk1 : FullState, ovf' = false ∧ msz'.toNat ≤ cv0 ∧
      FidFsBaseOk c F0 F_cur cv0 alen0 fuel0 refs0 sk1 ∧ sk1.core.arena = sp.core.arena ∧
      sk1.core.vals = sp.core.vals ∧ sk1.core.min_clr = sp.core.min_clr ∧
      sk1.core.inconsistent = 0#64 ∧ sk1.scratch = sp.scratch ∧
      (∀ j < msz'.toNat, (sk1.core.tmp[j]?.getD 0#32).toNat < 2 * cv0) ∧
      (∀ l < 2 * c.max_vars, sk1.core.lit_mark[l]?.getD 0#8 = 0#8 ∨
        (∃ j < msz'.toNat, (sk1.core.tmp[j]?.getD 0#32).toNat = l ∧ l < 2 * cv0)) ∧
      (∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α → ∀ j < k.toNat + 1,
        evalLitVal α (sk1.core.arena[p64.toNat + 3 + j]?.getD 0#32).toNat = true →
        ∃ q < msz'.toNat, evalLitVal α (sk1.core.tmp[q]?.getD 0#32).toNat = true) ∧
      (FullMem c sk1 ⋆ R) m1)
    (fun _ ⟨_, msz', ⟨⟩⟩ m1 ⟨sk1, _, hmsz', hb1, har1, hvl1, hmc1, hinc1, hscr1, htmp1, hlm1,
      hsem1, hm1⟩ => by
      c0_hsteps!; exact ihk (c_mch', msz', k + 1#32, ()) m1 (by dsimp only; omega)
        ⟨sk1, by omega, hb1, har1, hvl1, hmc1, hinc1, hscr1, hmsz', htmp1, hlm1,
          by rw [hk1]; exact hsem1, hm1⟩)
    ?_
  intro Jov hJov; c0_hsplit; rotate_left 1
  · have hneq : sk_r.core.lit_mark[r.toNat]?.getD 0#8 ≠ 0#8 := by
      rw [List.getElem?_eq_getElem hr_lm, Option.getD_some]
      exact bv8_zext32_beq0_false (by simp only [beq_eq_false_iff_ne]; exact hc)
    have hsem' := fidFs_k_sem_mem hsem_in har_k_pk hr_lt hcv_le hlm_ok_in hneq heqv_pk
    c0_hsteps!; exact hJov (false, msz, ()) mr
      ⟨sk_r, rfl, hmsz_cv, hb_r, har_in, hvl_in, hmc_in, hinc_in, hscr_in,
       htmp_lt_in, hlm_ok_in, hsem', hmr'⟩
  clear hc; c0_hsplit; rotate_left 1
  · c0_hsteps!; exact hJk1_ex false false c_mch' true msz k mr
      ⟨sk_r, hb_r, har_in, hvl_in, hmc_in, hinc_in, hscr_in, hmsz_cv,
       htmp_lt_in, hlm_ok_in, (fun _ _ h => Bool.noConfusion h), hmr'⟩
  have hmsz_lt : msz.toNat < cv0 := by omega
  have hmsz1 : (msz + 1#32).toNat = msz.toNat + 1 := by bv_omega
  have hmsz_arr : msz.toNat < sk_r.core.tmp.length := by
    have := hb_r.hlen.core_ok.tmp_len_arr; dsimp only [sk_r] at this ⊢; omega
  have hmsz_z : (msz.setWidth 64).toNat = msz.toNat := bv_zext32_toNat msz
  have hmsz_z_arr : (msz.setWidth 64).toNat < sk_r.core.tmp.length := by rw [hmsz_z]; exact hmsz_arr
  clear hc; c0_hsteps!
  obtain ⟨htmp', hlm'⟩ := fidFs_lm_set_mark htmp_lt_in hlm_ok_in hr_lt hmsz_arr
  have hsem' := fidFs_k_sem_push hsem_in har_k_pk hmsz_arr heqv_pk
  let sk1 : FullState :=
    { sk_r with core :=
      { sk_r.core with tmp :=
        sk_r.core.tmp.set msz.toNat r, lit_mark := sk_r.core.lit_mark.set r.toNat 1#8 } }
  rw [hmsz_z, hr_z] at hm
  exact hJov (false, msz + 1#32, ()) _
    ⟨sk1, rfl, by omega,
     hb_r.with_tmp_lm (by simpa [List.length_set] using hb_r.hlen.core_ok.tmp_len_arr)
       (by simpa [List.length_set] using hb_r.hlen.core_ok.lit_mark_len),
     har_in, hvl_in, hmc_in, hinc_in, hscr_in, by rw [hmsz1]; exact htmp',
     by rw [hmsz1]; exact hlm', by rw [hmsz1]; exact hsem', hm⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Congruence
