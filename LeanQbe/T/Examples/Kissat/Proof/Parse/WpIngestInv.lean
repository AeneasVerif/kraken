/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Parse.WpIngestHelpers

/-!
# Loop Invariants & Step Lemmas for `full_ingest_cl` (`Proof.Parse.WpIngestInv`)

Defines the four loop/join invariants (`IngestReadInv`, `IngestAfterReadInv`,
`IngestFiltInv`, `IngestActInv`) and proves all state-transition and exit-obligation
lemmas for `Proof.Parse.WpIngest`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Parse

open Std.Sat
open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

/-! ## 1. Auxiliary List / Singleton-Clause Helpers -/

theorem kissatLitToDimacsLiteral_inj {l1 l2 : Nat}
    (h : kissatLitToDimacsLiteral l1 = kissatLitToDimacsLiteral l2) : l1 = l2 := by
  simp only [kissatLitToDimacsLiteral, litVar, litSign, Prod.mk.injEq] at h
  have h1 : l1 / 2 = l2 / 2 := by omega
  have h2 : l1 % 2 = l2 % 2 := by
    by_cases a : l1 % 2 = 1 <;> by_cases b : l2 % 2 = 1 <;> simp [a, b] at h <;> omega
  omega

theorem ingest_singleton_acc {acc : List Nat} {l : Nat}
    (h : CNF.Clause.ofLiterals (acc.reverse.map kissatLitToDimacsLiteral) =
      CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l]) :
    acc = [l] := by
  have hl := congrArg CNF.Clause.literals h
  simp only [CNF.Clause.literals_ofLiterals] at hl
  cases hr : acc.reverse with
  | nil => simp [hr] at hl
  | cons a tl =>
    rw [hr] at hl
    cases tl with
    | nil =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hl
      have ha : a = l := kissatLitToDimacsLiteral_inj hl
      subst ha
      have := congrArg List.reverse hr
      simpa using this
    | cons b tl' => simp at hl

theorem list_take_set_append {α : Type} {xs : List α} {n : Nat} {x : α} (hn : n < xs.length) :
    (xs.set n x).take (n + 1) = xs.take n ++ [x] := by
  apply List.ext_getElem
  · simp [List.length_take, List.length_set]; omega
  · intro i hi1 hi2
    simp only [List.getElem_take, List.getElem_append, List.length_take] at hi1 hi2 ⊢
    by_cases hilt : i < n
    · have hmin : min n xs.length = n := Nat.min_eq_left (by omega)
      rw [List.getElem_set_ne (Ne.symm (Nat.ne_of_lt hilt))]
      simp [hmin, hilt]
    · have hieq : i = n := by simp [List.length_set] at hi1; omega
      subst hieq
      have hmin : min i xs.length = i := Nat.min_eq_left (by omega)
      rw [List.getElem_set_self]
      simp [hmin]

theorem list_map_take_nodup_set {tmp : List (BitVec 32)} {cnt : Nat} {ilit : BitVec 32}
    (hcnt : cnt < tmp.length)
    (hnd : ((tmp.take cnt).map fun x => x.toNat / 2).Nodup)
    (hnot : ilit.toNat / 2 ∉ (tmp.take cnt).map fun x => x.toNat / 2) :
    (((tmp.set cnt ilit).take (cnt + 1)).map fun x => x.toNat / 2).Nodup := by
  rw [list_take_set_append hcnt, List.map_append, List.map_singleton, List.nodup_append]
  refine ⟨hnd, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, fun a ha b hb => ?_⟩
  simp only [List.mem_singleton] at hb
  subst hb
  exact fun heq => hnot (heq ▸ ha)

/-! ## 2. `IngestReadInv` & `IngestAfterReadInv` -/

/-- State bundle shared by `IngestReadInv` and the non-error branch of `IngestAfterReadInv`. -/
structure IngestClauseState (c : FullCfg) (accCnf : CNF Nat) (F_cur : List (List Nat))
    (s0 : FullState) (acc : List Nat) (cnt : BitVec 32) (taut : Bool) (s : FullState) : Prop where
  hlen : s.LengthsOk c
  hw : FullWitnessInv c
    (CNF.relabel (tumblePi (decide (c.mv < c.extend_cap)) s0.core.frame_dec) (shiftDownCnf accCnf))
    F_cur s.core
  hlm : ∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8
  hnodup : FullArenaVarsNodup s
  hext : FullExtScratchOk c s
  hdense : s.core.dense_mode = 0#64
  hcv : s.core.cur_vars = c.mv
  hcl0 : s.core.cur_level = 0
  hfuel : s.core.fuel = s0.core.fuel
  hoom : s.core.oom = s0.core.oom
  hprob : s.core.probing = s0.core.probing
  hvals : s.core.vals = s0.core.vals
  hte : s.core.trail_end = s0.core.trail_end
  hprop : s.core.propagated = s0.core.propagated
  htm : TumbleInv (decide (c.mv < c.extend_cap)) c.mv s.scratch.extend_len s.core.frame_dec
  hcov : TumbleCovers (decide (c.mv < c.extend_cap)) s.core.frame_dec (shiftDownCnf accCnf)
  hrel_eq : CNF.relabel (tumblePi (decide (c.mv < c.extend_cap)) s.core.frame_dec)
      (shiftDownCnf accCnf) =
    CNF.relabel (tumblePi (decide (c.mv < c.extend_cap)) s0.core.frame_dec) (shiftDownCnf accCnf)
  hfd_mono : ∀ e < c.mv, s0.core.frame_dec[e]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
    s.core.frame_dec[e]?.getD 0xFFFFFFFF#32 = s0.core.frame_dec[e]?.getD 0xFFFFFFFF#32
  hacc_lt : ∀ l ∈ acc, l < 2 * c.mv
  hacc_map : decide (c.mv < c.extend_cap) = true →
    ∀ l ∈ acc, s.core.frame_dec[l / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32
  hval_rel : ∀ vext, 2 * c.mv ≤ vext.length →
    TumbleValsRel (decide (c.mv < c.extend_cap)) c.mv s0.core.frame_dec vext s0.core.vals →
    TumbleUnusedZero (decide (c.mv < c.extend_cap)) c.mv s0.scratch.extend_len s0.core.vals →
    TumbleValsRel (decide (c.mv < c.extend_cap)) c.mv s.core.frame_dec vext s.core.vals ∧
      TumbleUnusedZero (decide (c.mv < c.extend_cap)) c.mv s.scratch.extend_len s.core.vals
  hcnt_le : cnt.toNat ≤ c.mv
  htmp_wf : ∀ idx < cnt.toNat,
    let tl := (s.core.tmp[idx]?.getD 0#32).toNat
    tl < 2 * c.mv ∧
      s.core.mrk[tl / 2]?.getD 0#8 = (if tl % 2 = 0 then 1#8 else 2#8) ∧
      tl ∈ acc.map (tumbleLit (decide (c.mv < c.extend_cap)) s.core.frame_dec)
  htmp_nd : ((s.core.tmp.take cnt.toNat).map fun x => x.toNat / 2).Nodup
  hmrk_only : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
    ∃ idx < cnt.toNat, (s.core.tmp[idx]?.getD 0#32).toNat / 2 = v
  htmp_cov : taut = false → ∀ l ∈ acc,
    tumbleLit (decide (c.mv < c.extend_cap)) s.core.frame_dec l ∈
      (s.core.tmp.take cnt.toNat).map BitVec.toNat
  htaut_len : taut = true → 2 ≤ acc.length

@[expose] def IngestReadInv (c : FullCfg) (accCnf : CNF Nat) (F_cur : List (List Nat))
    (s0 : FullState) (cnf_ptr : BitVec 64) (cnfBytes : List UInt8) (i0 : Nat)
    (R : Mem 64 → Prop) (n : Nat) (xs : Tup Val [i32, .bool]) (m : Mem 64) : Prop :=
  match xs with
  | (cnt, taut, ()) =>
    ∃ (k : Nat) (acc : List Nat) (s : FullState),
      i0 ≤ k ∧ k ≤ cnfBytes.length ∧ n = cnfBytes.length - k ∧
      s.core.d_cur = cnf_ptr + BitVec.ofNat 64 k ∧
      parseClauseAux (cnfBytes.length - k + 1) c.mv (acc.map kissatLitToDimacsLiteral)
        (cnfBytes.drop k) = parseClause c.mv (cnfBytes.drop i0) ∧
      IngestClauseState c accCnf F_cur s0 acc cnt taut s ∧
      (FullMem c s ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m

@[expose] def IngestAfterReadInv (c : FullCfg) (accCnf : CNF Nat) (F_cur : List (List Nat))
    (s0 : FullState) (cnf_ptr : BitVec 64) (cnfBytes : List UInt8) (i0 : Nat)
    (R : Mem 64 → Prop) (xs : Tup Val [i32, .bool, .bool]) (m : Mem 64) : Prop :=
  match xs with
  | (cnt, taut, err, ()) =>
    if err = true then
      parseClause c.mv (cnfBytes.drop i0) = none ∧
      ∃ s : FullState,
        s.LengthsOk c ∧ s.core.fuel = s0.core.fuel ∧ s.core.oom = s0.core.oom ∧
        s.core.probing = s0.core.probing ∧ cnt.toNat ≤ c.mv ∧
        (FullMem c s ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m
    else
      ∃ (j : Nat) (acc : List Nat) (rest : List UInt8) (s : FullState),
        i0 < j ∧ j ≤ cnfBytes.length ∧ cnfBytes.drop j = rest ∧
        s.core.d_cur = cnf_ptr + BitVec.ofNat 64 j ∧
        parseClause c.mv (cnfBytes.drop i0) =
          some (CNF.Clause.ofLiterals (acc.reverse.map kissatLitToDimacsLiteral), rest) ∧
        IngestClauseState c accCnf F_cur s0 acc cnt taut s ∧
        (FullMem c s ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m

/-! ## 3. Loop 0 Init & Step Lemmas -/

theorem ingest_read_init {c : FullCfg} {accCnf : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {cnf_ptr : BitVec 64} {cnfBytes : List UInt8} {i0 : Nat}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hi0 : i0 ≤ cnfBytes.length) (hcv : s.core.cur_vars = c.mv)
    (hdcur : s.core.d_cur = cnf_ptr + BitVec.ofNat 64 i0) (hcl0 : s.core.cur_level = 0)
    (htm : TumbleInv (decide (c.mv < c.extend_cap)) c.mv s.scratch.extend_len s.core.frame_dec)
    (hcov : TumbleCovers (decide (c.mv < c.extend_cap)) s.core.frame_dec (shiftDownCnf accCnf))
    (hsp : FullSparseInvW c
      (CNF.relabel (tumblePi (decide (c.mv < c.extend_cap)) s.core.frame_dec) (shiftDownCnf accCnf))
      F_cur s)
    (hm : (FullMem c s ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m) :
    IngestReadInv c accCnf F_cur s cnf_ptr cnfBytes i0 R (cnfBytes.length - i0) (0#32, false, ())
      m := by
  refine ⟨i0, [], s, Nat.le_refl _, hi0, rfl, hdcur, ?_, ?_, hm⟩
  · unfold parseClause; simp [List.length_drop]
  · refine
      { hlen := hsp.1, hw := hsp.2.1, hlm := hsp.2.2.1.2, hnodup := hsp.2.2.2.1,
        hext := hsp.2.2.2.2.1, hdense := hsp.2.2.2.2.2, hcv := hcv, hcl0 := hcl0,
        hfuel := rfl, hoom := rfl, hprob := rfl, hvals := rfl, hte := rfl, hprop := rfl,
        htm := htm, hcov := hcov, hrel_eq := rfl,
        hfd_mono := fun _ _ _ => rfl,
        hacc_lt := fun _ h => by simp at h,
        hacc_map := fun _ _ h => by simp at h,
        hval_rel := fun _ _ hr hu => ⟨hr, hu⟩,
        hcnt_le := by simp,
        htmp_wf := fun _ h => by simp at h,
        htmp_nd := by simp,
        hmrk_only := fun v hv hne => absurd (hsp.2.2.1.1 v hv) hne,
        htmp_cov := fun _ _ h => by simp at h,
        htaut_len := fun h => by cases h }

theorem ingest_cs_upd_dcur {c : FullCfg} {accCnf : CNF Nat} {F_cur : List (List Nat)}
    {s0 s : FullState} {acc : List Nat} {cnt : BitVec 32} {taut : Bool}
    (hcs : IngestClauseState c accCnf F_cur s0 acc cnt taut s) (d_cur' d_val' : BitVec 64) :
    IngestClauseState c accCnf F_cur s0 acc cnt taut
      { s with core := { s.core with d_cur := d_cur', d_val := d_val' } } :=
  { hcs with
    hlen := ⟨{ hcs.hlen.core_ok with vals_len := hcs.hlen.core_ok.vals_len }, hcs.hlen.scratch_ok⟩
    hw := ingest_witness_with_fd_dcur_mrk_tmp hcs.hw hcs.hcl0 }

theorem ingest_cs_tumble_map {c : FullCfg} {accCnf : CNF Nat} {F_cur : List (List Nat)}
    {s0 s : FullState} {acc : List Nat} {cnt : BitVec 32} {taut : Bool} {ev : Nat}
    (hcs : IngestClauseState c accCnf F_cur s0 acc cnt taut s)
    (htum : decide (c.mv < c.extend_cap) = true)
    (hev : ev < c.mv)
    (hun : s.core.frame_dec[ev]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) :
    let next := s.scratch.extend_len
    let fd' := s.core.frame_dec.set ev (BitVec.ofNat 32 next)
    let s' : FullState :=
      { core := { s.core with frame_dec := fd' }
        scratch := { s.scratch with extend_len := next + 1 } }
    next < c.mv ∧
      fd'[ev]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 next ∧
      fd'[ev]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 ∧
      IngestClauseState c accCnf F_cur s0 acc cnt taut s' := by
  intro next fd' s'
  have hmv_lt := c.hmv; have hext_lt := c.hext; unfold dimacsBound at hmv_lt hext_lt
  have hmv_ec : c.mv < c.extend_cap := of_decide_eq_true htum
  have hmap0 : TumbleMapInv c.mv next s.core.frame_dec := hcs.htm htum
  have hnext_lt : next < c.mv := tumbleMapInv_next_lt hmap0 hev hun
  have hfd_len : c.mv ≤ s.core.frame_dec.length := by
    rw [hcs.hlen.core_ok.frame_dec_len]
    have := hcs.hlen.core_ok.cur_vars_le; have := hcs.hcv; omega
  have hfd_ev : ev < s.core.frame_dec.length := by omega
  have hget_self : fd'[ev]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 next := by
    simp [fd', List.getElem?_set_self hfd_ev]
  have hne_ff : BitVec.ofNat 32 next ≠ 0xFFFFFFFF#32 := by
    intro h; have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    change next % 2 ^ 32 = 2 ^ 32 - 1 at this; omega
  have htm' : TumbleInv (decide (c.mv < c.extend_cap)) c.mv (next + 1) fd' := fun _ =>
    tumbleMapInv_set hmap0 hev hfd_len (by omega) hun
  have hcov' : TumbleCovers (decide (c.mv < c.extend_cap)) fd' (shiftDownCnf accCnf) :=
    tumbleCovers_set hcs.hcov hun
  have hrel' : CNF.relabel (tumblePi (decide (c.mv < c.extend_cap)) fd') (shiftDownCnf accCnf) =
      CNF.relabel (tumblePi (decide (c.mv < c.extend_cap)) s0.core.frame_dec)
        (shiftDownCnf accCnf) := by
    rw [cnf_relabel_tumble_set hcs.hcov hun, hcs.hrel_eq]
  have hacc_map' : decide (c.mv < c.extend_cap) = true →
      ∀ l ∈ acc, fd'[l / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
    intro ht l hl
    have hprev := hcs.hacc_map ht l hl
    have hne : ev ≠ l / 2 := fun heq => hprev (heq ▸ hun)
    simpa [fd', List.getElem?_set_ne hne] using hprev
  have hmap_eq : acc.map (tumbleLit (decide (c.mv < c.extend_cap)) fd') =
      acc.map (tumbleLit (decide (c.mv < c.extend_cap)) s.core.frame_dec) := by
    apply List.map_congr_left
    intro l hl
    exact tumbleLit_set_eq hun (fun ht => hcs.hacc_map ht l hl)
  refine ⟨hnext_lt, hget_self, by rw [hget_self]; exact hne_ff, ?_⟩
  refine
    { hcs with
      hlen := ⟨{ hcs.hlen.core_ok with
          frame_dec_len := by
            dsimp only [s', fd']; rw [List.length_set]; exact hcs.hlen.core_ok.frame_dec_len },
        { hcs.hlen.scratch_ok with extend_stk_len := hcs.hlen.scratch_ok.extend_stk_len }⟩
      hw := ingest_witness_with_fd_dcur_mrk_tmp hcs.hw hcs.hcl0
      hext := ⟨hcs.hext.1, by dsimp only [s']; omega⟩
      htm := htm', hcov := hcov', hrel_eq := hrel', hacc_map := hacc_map'
      hfd_mono := fun e he hne => by
        have hprev := hcs.hfd_mono e he hne
        have hne_ev : ev ≠ e := fun h => hne (hprev ▸ h ▸ hun)
        dsimp only [s', fd']; rw [List.getElem?_set_ne hne_ev]; exact hprev
      hval_rel := fun vext hvl hr hu => by
        obtain ⟨hr1, hu1⟩ := hcs.hval_rel vext hvl hr hu
        exact ⟨tumbleValsRel_set_unmapped hr1 hu1 hev hfd_len hnext_lt (by omega) hun,
          tumbleUnusedZero_mono hu1 (Nat.le_succ next)⟩
      htmp_wf := fun idx hidx => by
        dsimp only [s']; rw [hmap_eq]; exact hcs.htmp_wf idx hidx
      htmp_cov := fun htf l hl => by
        dsimp only [s']
        rw [tumbleLit_set_eq hun (fun ht => hcs.hacc_map ht l hl)]
        exact hcs.htmp_cov htf l hl }

theorem ingest_cs_mark_new {c : FullCfg} {accCnf : CNF Nat} {F_cur : List (List Nat)}
    {s0 s : FullState} {acc : List Nat} {cnt ilit ivar : BitVec 32} {taut : Bool} {l : Nat}
    (hcs : IngestClauseState c accCnf F_cur s0 acc cnt taut s)
    (hl_lt : l < 2 * c.mv)
    (hl_map : decide (c.mv < c.extend_cap) = true →
      s.core.frame_dec[l / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hilit : ilit.toNat = tumbleLit (decide (c.mv < c.extend_cap)) s.core.frame_dec l)
    (hivar : ivar.toNat = ilit.toNat / 2)
    (hunm : s.core.mrk[ivar.toNat]?.getD 0#8 = 0#8) :
    let sm := BitVec.setWidth 8 ((ilit &&& 1#32) + 1#32)
    let s' : FullState :=
      { s with core := { s.core with
          mrk := s.core.mrk.set ivar.toNat sm,
          tmp := s.core.tmp.set cnt.toNat ilit } }
    cnt.toNat < c.mv ∧
      IngestClauseState c accCnf F_cur s0 (l :: acc) (cnt + 1#32) taut s' := by
  intro sm s'
  have hmv_lt := c.hmv; have hmx_lt := c.hmaxv; unfold dimacsBound at hmv_lt hmx_lt
  have hcv_le := hcs.hlen.core_ok.cur_vars_le
  have hcv := hcs.hcv
  have hcnt_le := hcs.hcnt_le
  have hilit_lt : ilit.toNat < 2 * c.mv := hilit ▸ tumbleLit_lt hcs.htm hl_lt hl_map
  have hivar_lt : ivar.toNat < c.mv := by omega
  have htmp_len : s.core.tmp.length = c.max_vars := hcs.hlen.core_ok.tmp_len_arr
  have hmrk_len : s.core.mrk.length = c.max_vars := hcs.hlen.core_ok.mrk_len
  have hcnt_lt : cnt.toNat < c.mv :=
    ing_cnt_lt_mv_of_unmarked (by omega) hivar_lt hunm hcs.htmp_nd fun i hi => by
      obtain ⟨h1, h2, _⟩ := hcs.htmp_wf i hi
      refine ⟨h1, ?_⟩
      rw [h2]; split <;> decide
  have hcnt1 : (cnt + 1#32).toNat = cnt.toNat + 1 := by
    rw [BitVec.toNat_add, show (1#32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hcnt_tmp : cnt.toNat < s.core.tmp.length := by omega
  have hivar_mrk : ivar.toNat < s.core.mrk.length := by omega
  have hnot_in : ilit.toNat / 2 ∉ (s.core.tmp.take cnt.toNat).map fun x => x.toNat / 2 := by
    intro hmem
    simp only [List.mem_map] at hmem
    obtain ⟨x, hx_t, hdiv⟩ := hmem
    rw [List.mem_iff_getElem] at hx_t
    obtain ⟨i, hi, hget⟩ := hx_t
    have hi_cnt : i < cnt.toNat := by simp [List.length_take] at hi; omega
    have hx_eq : s.core.tmp[i]?.getD 0#32 = x := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      simpa [List.getElem_take] using hget
    have h2 := (hcs.htmp_wf i hi_cnt).2.1
    rw [hx_eq, hdiv, ← hivar, hunm] at h2
    split at h2 <;> cases h2
  refine ⟨hcnt_lt, ?_⟩
  refine
    { hcs with
      hlen := ⟨{ hcs.hlen.core_ok with
          mrk_len := by dsimp only [s']; rw [List.length_set, hmrk_len],
          tmp_len_arr := by dsimp only [s']; rw [List.length_set, htmp_len] },
        hcs.hlen.scratch_ok⟩
      hw := ingest_witness_with_fd_dcur_mrk_tmp hcs.hw hcs.hcl0
      hacc_lt := fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hm; exact hl_lt; exact hcs.hacc_lt x hm
      hacc_map := fun ht x hx => by
        rcases List.mem_cons.mp hx with rfl | hm; exact hl_map ht; exact hcs.hacc_map ht x hm
      hcnt_le := by omega
      htmp_wf := fun idx hidx => by
        rw [hcnt1] at hidx
        dsimp only [s']
        by_cases he : idx = cnt.toNat
        · subst he
          rw [List.getElem?_set_self hcnt_tmp, Option.getD_some, ← hivar,
            List.getElem?_set_self hivar_mrk, Option.getD_some]
          refine ⟨hilit_lt, ing_sign_mark_eq ilit, ?_⟩
          rw [hilit]; exact List.mem_cons_self
        · have hi' : idx < cnt.toNat := by omega
          rw [List.getElem?_set_ne (Ne.symm he)]
          obtain ⟨h1, h2, h3⟩ := hcs.htmp_wf idx hi'
          have hne_v : ivar.toNat ≠ (s.core.tmp[idx]?.getD 0#32).toNat / 2 := by
            intro heq; rw [← heq, hunm] at h2; split at h2 <;> cases h2
          rw [List.getElem?_set_ne hne_v]
          exact ⟨h1, h2, List.mem_cons_of_mem _ h3⟩
      htmp_nd := by
        dsimp only [s']; rw [hcnt1]
        exact list_map_take_nodup_set hcnt_tmp hcs.htmp_nd hnot_in
      hmrk_only := fun v hv hne => by
        dsimp only [s'] at hne ⊢
        by_cases hev : v = ivar.toNat
        · subst hev
          refine ⟨cnt.toNat, by omega, ?_⟩
          rw [List.getElem?_set_self hcnt_tmp, Option.getD_some, hivar]
        · rw [List.getElem?_set_ne (Ne.symm hev)] at hne
          obtain ⟨idx, hidx, hdiv⟩ := hcs.hmrk_only v hv hne
          refine ⟨idx, by omega, ?_⟩
          rw [List.getElem?_set_ne (by omega)]; exact hdiv
      htmp_cov := fun htf x hx => by
        dsimp only [s']; rw [hcnt1, list_take_set_append hcnt_tmp, List.map_append,
          List.map_singleton, List.mem_append, List.mem_singleton]
        rcases List.mem_cons.mp hx with rfl | hm
        · exact Or.inr hilit.symm
        · exact Or.inl (hcs.htmp_cov htf x hm)
      htaut_len := fun htt => by have := hcs.htaut_len htt; simp; omega }

theorem ingest_cs_mark_dup {c : FullCfg} {accCnf : CNF Nat} {F_cur : List (List Nat)}
    {s0 s : FullState} {acc : List Nat} {cnt ilit ivar : BitVec 32} {taut taut' : Bool} {l : Nat}
    (hcs : IngestClauseState c accCnf F_cur s0 acc cnt taut s)
    (hl_lt : l < 2 * c.mv)
    (hl_map : decide (c.mv < c.extend_cap) = true →
      s.core.frame_dec[l / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hilit : ilit.toNat = tumbleLit (decide (c.mv < c.extend_cap)) s.core.frame_dec l)
    (hivar : ivar.toNat = ilit.toNat / 2)
    (hmk : s.core.mrk[ivar.toNat]?.getD 0#8 ≠ 0#8)
    (htaut' : taut' = if s.core.mrk[ivar.toNat]?.getD 0#8 ≠
        BitVec.setWidth 8 ((ilit &&& 1#32) + 1#32) then true else taut) :
    IngestClauseState c accCnf F_cur s0 (l :: acc) cnt taut' s := by
  have hilit_lt : ilit.toNat < 2 * c.mv := hilit ▸ tumbleLit_lt hcs.htm hl_lt hl_map
  have hcv_le := hcs.hlen.core_ok.cur_vars_le
  have hcv := hcs.hcv
  have hcnt_le := hcs.hcnt_le
  have hivar_lt : ivar.toNat < c.max_vars := by omega
  obtain ⟨idx, hidx_lt, hidx_div⟩ := hcs.hmrk_only ivar.toNat hivar_lt hmk
  obtain ⟨htl_lt, htl_mk, htl_mem⟩ := hcs.htmp_wf idx hidx_lt
  have hacc_ne : acc ≠ [] := by
    intro hnil; simp [hnil] at htl_mem
  have hacc_pos : 1 ≤ acc.length := by cases acc with | nil => contradiction | cons _ _ => simp
  refine
    { hlen := hcs.hlen, hw := hcs.hw, hlm := hcs.hlm, hnodup := hcs.hnodup, hext := hcs.hext,
      hdense := hcs.hdense, hcv := hcs.hcv, hcl0 := hcs.hcl0, hfuel := hcs.hfuel, hoom := hcs.hoom,
      hprob := hcs.hprob, hvals := hcs.hvals, hte := hcs.hte, hprop := hcs.hprop, htm := hcs.htm,
      hcov := hcs.hcov, hrel_eq := hcs.hrel_eq, hfd_mono := hcs.hfd_mono,
      hval_rel := hcs.hval_rel, hcnt_le := hcs.hcnt_le,
      htmp_nd := hcs.htmp_nd, hmrk_only := hcs.hmrk_only,
      hacc_lt := fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hm; exact hl_lt; exact hcs.hacc_lt x hm
      hacc_map := fun ht x hx => by
        rcases List.mem_cons.mp hx with rfl | hm; exact hl_map ht; exact hcs.hacc_map ht x hm
      htmp_wf := fun i hi => by
        obtain ⟨h1, h2, h3⟩ := hcs.htmp_wf i hi
        exact ⟨h1, h2, List.mem_cons_of_mem _ h3⟩
      htmp_cov := fun htf x hx => by
        have hsame : s.core.mrk[ivar.toNat]?.getD 0#8 =
            BitVec.setWidth 8 ((ilit &&& 1#32) + 1#32) :=
          Classical.byContradiction fun hne => by
            simp [htaut', hne] at htf
        have htaut_f : taut = false := by
          simpa [htaut', hsame] using htf
        rcases List.mem_cons.mp hx with rfl | hm
        · rw [← hilit]
          rw [hidx_div, hsame, ing_sign_mark_eq] at htl_mk
          have hmod_eq : (s.core.tmp[idx]?.getD 0#32).toNat % 2 = ilit.toNat % 2 := by
            by_cases h1 : (s.core.tmp[idx]?.getD 0#32).toNat % 2 = 0 <;>
              by_cases h2 : ilit.toNat % 2 = 0
            · omega
            · simp [h1, h2] at htl_mk
            · simp [h1, h2] at htl_mk
            · omega
          have heq_l : (s.core.tmp[idx]?.getD 0#32).toNat = ilit.toNat := by omega
          have hidx_tmp : idx < s.core.tmp.length := by
            rw [hcs.hlen.core_ok.tmp_len_arr]; omega
          rw [← heq_l, List.getElem?_eq_getElem hidx_tmp, Option.getD_some]
          refine List.mem_map.mpr ⟨s.core.tmp[idx]'hidx_tmp, ?_, rfl⟩
          rw [List.mem_iff_getElem]
          exact ⟨idx, by simp [List.length_take]; omega, by simp [List.getElem_take]⟩
        · exact hcs.htmp_cov htaut_f x hm
      htaut_len := fun _ => by simp; omega }

/-! ## 4. Loop 1 (`clear mrk`) & Loop 2 (`filter vals`) & Loop 3 (`activate`) Helpers -/

/-- After Loop 1 clears `mrk[tmp[idx] >>> 1]` for all `idx < cnt`, `FullMrkZero` holds
and the `IngestClauseState` yields `FullSparseInvW c F0 F_cur s`. -/
theorem ingest_after_clear_sparse {c : FullCfg} {accCnf : CNF Nat} {F_cur : List (List Nat)}
    {s0 s : FullState} {acc : List Nat} {cnt : BitVec 32} {taut : Bool} {mrk' : List (BitVec 8)}
    (hcs : IngestClauseState c accCnf F_cur s0 acc cnt taut s)
    (hmrkl : mrk'.length = c.max_vars)
    (hclr : ∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8) :
    let s' : FullState := { s with core := { s.core with mrk := mrk' } }
    FullSparseInvW c
      (CNF.relabel (tumblePi (decide (c.mv < c.extend_cap)) s'.core.frame_dec)
        (shiftDownCnf accCnf))
      F_cur s' := by
  intro s'
  have hlen' : s'.LengthsOk c :=
    ⟨{ hcs.hlen.core_ok with mrk_len := hmrkl }, hcs.hlen.scratch_ok⟩
  have hw' : FullWitnessInv c
      (CNF.relabel (tumblePi (decide (c.mv < c.extend_cap)) s'.core.frame_dec)
        (shiftDownCnf accCnf))
      F_cur s'.core := by
    have h1 := ingest_witness_with_fd_dcur_mrk_tmp hcs.hw hcs.hcl0
      (d_cur' := s.core.d_cur) (d_val' := s.core.d_val) (fd' := s.core.frame_dec)
      (mrk' := mrk') (tmp' := s.core.tmp)
    simpa only [s', hcs.hrel_eq] using h1
  exact ⟨hlen', hw', ⟨hclr, hcs.hlm⟩, hcs.hnodup, hcs.hext, hcs.hdense⟩

/-- Filter-loop invariant for Loop 2 (`J_filt (new_cnt, idx, ())`). -/
structure IngestFiltState (c : FullCfg) (s_clr : FullState) (cnt : Nat)
    (new_cnt idx : BitVec 32) (tmp : List (BitVec 32)) : Prop where
  htmp_len : tmp.length = c.max_vars
  hle : new_cnt.toNat ≤ idx.toNat
  hidx_le : idx.toNat ≤ cnt
  hrest : ∀ j, idx.toNat ≤ j → j < cnt → tmp[j]? = s_clr.core.tmp[j]?
  hkept : ∀ k < new_cnt.toNat,
    let tl := (tmp[k]?.getD 0#32).toNat
    tl < 2 * c.mv ∧ s_clr.core.vals[tl]?.getD 0#8 = 0#8 ∧
      tl ∈ (s_clr.core.tmp.take cnt).map BitVec.toNat
  hnd : ((tmp.take new_cnt.toNat).map (fun (x : BitVec 32) => x.toNat / 2) ++
    ((s_clr.core.tmp.drop idx.toNat).take (cnt - idx.toNat)).map
      (fun (x : BitVec 32) => x.toNat / 2)).Nodup
  hseen : ∀ j < idx.toNat,
    let tl := (s_clr.core.tmp[j]?.getD 0#32).toNat
    tl ∈ (tmp.take new_cnt.toNat).map BitVec.toNat ∨ s_clr.core.vals[tl]?.getD 0#8 = 0xFF#8

theorem ingest_filt_init {c : FullCfg} {s_clr : FullState} {cnt : Nat}
    (hlen : s_clr.LengthsOk c)
    (hnd : ((s_clr.core.tmp.take cnt).map fun x => x.toNat / 2).Nodup) :
    IngestFiltState c s_clr cnt 0#32 0#32 s_clr.core.tmp :=
  { htmp_len := hlen.core_ok.tmp_len_arr
    hle := by simp
    hidx_le := by simp
    hrest := fun _ _ _ => rfl
    hkept := fun _ h => by simp at h
    hnd := by simpa using hnd
    hseen := fun _ h => by simp at h }

private theorem take_drop_succ_eq {α : Type} {xs : List α} {i cnt : Nat}
    (hi : i < cnt) (hcnt : cnt ≤ xs.length) :
    (xs.drop i).take (cnt - i) =
      xs[i]'(by omega) :: (xs.drop (i + 1)).take (cnt - (i + 1)) := by
  have hi_len : i < xs.length := by omega
  have hsub : cnt - i = (cnt - (i + 1)) + 1 := by omega
  rw [hsub, List.drop_eq_getElem_cons hi_len, List.take_succ_cons]

theorem ingest_filt_step_keep {c : FullCfg} {s_clr : FullState} {cnt : Nat}
    {new_cnt idx l : BitVec 32} {tmp : List (BitVec 32)}
    (hf : IngestFiltState c s_clr cnt new_cnt idx tmp)
    (hclr_len : s_clr.core.tmp.length = c.max_vars)
    (hcnt_le : cnt ≤ c.mv) (hcv_le : c.mv ≤ c.max_vars) (hmx : c.max_vars < 2 * dimacsBound)
    (hidx_lt : idx.toNat < cnt)
    (hl_eq : s_clr.core.tmp[idx.toNat]? = some l)
    (hl_lt : l.toNat < 2 * c.mv)
    (hval0 : s_clr.core.vals[l.toNat]?.getD 0#8 = 0#8) :
    IngestFiltState c s_clr cnt (new_cnt + 1#32) (idx + 1#32) (tmp.set new_cnt.toNat l) := by
  unfold dimacsBound at hmx
  have hle := hf.hle
  have hnc1 : (new_cnt + 1#32).toNat = new_cnt.toNat + 1 := by
    rw [BitVec.toNat_add, show (1#32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hidx1 : (idx + 1#32).toNat = idx.toNat + 1 := by
    rw [BitVec.toNat_add, show (1#32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hnc_tmp : new_cnt.toNat < tmp.length := by rw [hf.htmp_len]; omega
  have hcnt_clr : cnt ≤ s_clr.core.tmp.length := by omega
  have hl_get : s_clr.core.tmp[idx.toNat]'(by omega) = l := by
    rw [List.getElem?_eq_getElem (by omega)] at hl_eq; exact Option.some.inj hl_eq
  have hl_in_take : l.toNat ∈ (s_clr.core.tmp.take cnt).map BitVec.toNat := by
    refine List.mem_map.mpr ⟨l, ?_, rfl⟩
    rw [List.mem_iff_getElem]
    exact ⟨idx.toNat, by simp [List.length_take]; omega, by simp [List.getElem_take, hl_get]⟩
  refine
    { htmp_len := by rw [List.length_set, hf.htmp_len]
      hle := by have := hf.hle; omega
      hidx_le := by omega
      hrest := fun j hj1 hj2 => by
        have hne : new_cnt.toNat ≠ j := by have := hf.hle; omega
        rw [List.getElem?_set_ne hne]
        exact hf.hrest j (by omega) hj2
      hkept := fun k hk => by
        rw [hnc1] at hk
        by_cases he : k = new_cnt.toNat
        · subst he; rw [List.getElem?_set_self hnc_tmp, Option.getD_some]
          exact ⟨hl_lt, hval0, hl_in_take⟩
        · rw [List.getElem?_set_ne (Ne.symm he)]
          exact hf.hkept k (by omega)
      hnd := by
        rw [hnc1, hidx1, list_take_set_append hnc_tmp, List.map_append, List.map_singleton,
          List.append_assoc, List.singleton_append]
        have htd := take_drop_succ_eq hidx_lt hcnt_clr
        rw [hl_get] at htd
        have hnd0 := hf.hnd
        rw [htd, List.map_cons] at hnd0
        exact hnd0
      hseen := fun j hj => by
        rw [hidx1] at hj
        dsimp only
        rw [hnc1, list_take_set_append hnc_tmp, List.map_append, List.map_singleton,
          List.mem_append, List.mem_singleton]
        by_cases he : j = idx.toNat
        · subst he
          rw [hl_eq, Option.getD_some]
          exact Or.inl (Or.inr rfl)
        · rcases hf.hseen j (by omega) with hm | hf0
          · exact Or.inl (Or.inl hm)
          · exact Or.inr hf0 }

theorem ingest_filt_step_skip {c : FullCfg} {s_clr : FullState} {cnt : Nat}
    {new_cnt idx l : BitVec 32} {tmp : List (BitVec 32)}
    (hf : IngestFiltState c s_clr cnt new_cnt idx tmp)
    (hclr_len : s_clr.core.tmp.length = c.max_vars)
    (hcnt_le : cnt ≤ c.mv) (hcv_le : c.mv ≤ c.max_vars) (hmx : c.max_vars < 2 * dimacsBound)
    (hidx_lt : idx.toNat < cnt)
    (hl_eq : s_clr.core.tmp[idx.toNat]? = some l)
    (hvf : s_clr.core.vals[l.toNat]?.getD 0#8 = 0xFF#8) :
    IngestFiltState c s_clr cnt new_cnt (idx + 1#32) tmp := by
  unfold dimacsBound at hmx
  have hidx1 : (idx + 1#32).toNat = idx.toNat + 1 := by
    rw [BitVec.toNat_add, show (1#32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hcnt_clr : cnt ≤ s_clr.core.tmp.length := by omega
  refine
    { htmp_len := hf.htmp_len
      hle := by have := hf.hle; omega
      hidx_le := by omega
      hrest := fun j hj1 hj2 => hf.hrest j (by omega) hj2
      hkept := hf.hkept
      hnd := by
        rw [hidx1]
        have htd := take_drop_succ_eq hidx_lt hcnt_clr
        have hnd0 := hf.hnd
        rw [htd, List.map_cons] at hnd0
        rw [List.nodup_append] at hnd0 ⊢
        refine ⟨hnd0.1, (List.nodup_cons.mp hnd0.2.1).2, fun a ha b hb =>
          hnd0.2.2 a ha b (List.mem_cons_of_mem _ hb)⟩
      hseen := fun j hj => by
        rw [hidx1] at hj
        by_cases he : j = idx.toNat
        · subst he; rw [hl_eq, Option.getD_some]; exact Or.inr hvf
        · exact hf.hseen j (by omega) }

/-! ## 5. Exit Obligation Helpers for `fullIngestClTumSpec` -/

/-- Common clause-level facts derived from `IngestClauseState` when `err = false`. -/
theorem ingest_clause_common {c : FullCfg} {accCnf : CNF Nat} {F_cur : List (List Nat)}
    {s0 s : FullState} {acc : List Nat} {cnt : BitVec 32} {taut : Bool}
    (hcs : IngestClauseState c accCnf F_cur s0 acc cnt taut s)
    (hvb : CnfVarsLt c.mv (shiftDownCnf accCnf)) :
    let tum := decide (c.mv < c.extend_cap)
    let cl := CNF.Clause.ofLiterals (acc.reverse.map kissatLitToDimacsLiteral)
    let F0' := CNF.relabel (tumblePi tum s.core.frame_dec) (shiftDownCnf (accCnf.add cl))
    (∀ lit ∈ cl.literals, 1 ≤ lit.1) ∧
    TumbleCovers tum s.core.frame_dec (shiftDownCnf (accCnf.add cl)) ∧
    CnfVarsLt c.mv (shiftDownCnf (accCnf.add cl)) ∧
    F0'.Entails (CNF.relabel (tumblePi tum s.core.frame_dec) (shiftDownCnf accCnf)) ∧
    F0'.EntailsClause (cnfClause (acc.reverse.map (tumbleLit tum s.core.frame_dec))) := by
  intro tum cl F0'
  have hpos : ∀ lit ∈ cl.literals, 1 ≤ lit.1 := by
    intro lit hlit
    simp only [cl, CNF.Clause.literals_ofLiterals, List.mem_map] at hlit
    obtain ⟨l, _, rfl⟩ := hlit
    simp [kissatLitToDimacsLiteral]
  have hcov' : TumbleCovers tum s.core.frame_dec (shiftDownCnf (accCnf.add cl)) :=
    tumbleCovers_add_clause hcs.hcov fun ht l hl =>
      hcs.hacc_map ht l (List.mem_reverse.mp hl)
  have hvb' : CnfVarsLt c.mv (shiftDownCnf (accCnf.add cl)) :=
    cnfVarsLt_add_clause hvb fun l hl => hcs.hacc_lt l (List.mem_reverse.mp hl)
  have hF0'_F0 : F0'.Entails (CNF.relabel (tumblePi tum s.core.frame_dec) (shiftDownCnf accCnf)) :=
    cnf_relabel_entails_mono (shiftDownCnf_entails_add accCnf cl)
  have hF0'_cl : F0'.EntailsClause
      (cnfClause (acc.reverse.map (tumbleLit tum s.core.frame_dec))) := by
    have h1 := cnf_relabel_entailsClause_mono (r := tumblePi tum s.core.frame_dec)
      (shiftDownCnf_entails_added accCnf cl)
    have hcl_eq : CNF.Clause.relabel (tumblePi tum s.core.frame_dec) (shiftDownClause cl) =
        cnfClause (acc.reverse.map (tumbleLit tum s.core.frame_dec)) := cnfClause_relabel_eq
    rwa [hcl_eq] at h1
  exact ⟨hpos, hcov', hvb', hF0'_F0, hF0'_cl⟩

/-- For a singleton clause `cl = [l]` with `taut = false`, `cnt = 1` and `tmp[0] = tumbleLit l`. -/
theorem ingest_singleton_tmp0 {c : FullCfg} {accCnf : CNF Nat} {F_cur : List (List Nat)}
    {s0 s : FullState} {acc : List Nat} {cnt : BitVec 32} {taut : Bool} {l : Nat}
    (hcs : IngestClauseState c accCnf F_cur s0 acc cnt taut s)
    (htf : taut = false)
    (hcl : CNF.Clause.ofLiterals (acc.reverse.map kissatLitToDimacsLiteral) =
      CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l]) :
    cnt.toNat = 1 ∧
      (s.core.tmp[0]?.getD 0#32).toNat =
        tumbleLit (decide (c.mv < c.extend_cap)) s.core.frame_dec l := by
  have hacc : acc = [l] := ingest_singleton_acc hcl
  subst hacc
  have hmem := hcs.htmp_cov htf l List.mem_cons_self
  rw [List.mem_map] at hmem
  obtain ⟨x, hx_t, hx_eq⟩ := hmem
  rw [List.mem_iff_getElem] at hx_t
  obtain ⟨i, hi, _⟩ := hx_t
  have hcnt_pos : 0 < cnt.toNat := by simp [List.length_take] at hi; omega
  have h0_wf := hcs.htmp_wf 0 hcnt_pos
  have h0_eq : (s.core.tmp[0]?.getD 0#32).toNat =
      tumbleLit (decide (c.mv < c.extend_cap)) s.core.frame_dec l := by
    simpa using h0_wf.2.2
  have hcnt_le1 : cnt.toNat ≤ 1 := Nat.le_of_not_lt fun h1_lt => by
    have h1_wf := hcs.htmp_wf 1 h1_lt
    have h1_eq : (s.core.tmp[1]?.getD 0#32).toNat =
        tumbleLit (decide (c.mv < c.extend_cap)) s.core.frame_dec l := by
      simpa using h1_wf.2.2
    have htmp_len := hcs.hlen.core_ok.tmp_len_arr
    have hcv_le := hcs.hlen.core_ok.cur_vars_le
    have hcv := hcs.hcv
    have hcnt_tmp : cnt.toNat ≤ s.core.tmp.length := by have := hcs.hcnt_le; omega
    have hnd := hcs.htmp_nd
    cases htmp : s.core.tmp with
    | nil => simp [htmp] at hcnt_tmp; omega
    | cons a tl =>
      cases tl with
      | nil => simp [htmp] at hcnt_tmp; omega
      | cons b tl' =>
        rw [htmp] at h0_eq h1_eq hnd
        have hcnt_eq : cnt.toNat = (cnt.toNat - 2) + 2 := by omega
        rw [hcnt_eq] at hnd
        simp only [List.take_succ_cons, List.map_cons, List.nodup_cons, List.mem_cons,
          not_or] at hnd
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some] at h0_eq h1_eq
        exact hnd.1.1 (by omega)
  exact ⟨by omega, h0_eq⟩

/-- When `taut = false` and Loop 2 ends at `idx = cnt`, `F0'` entails `tmp.take new_cnt`. -/
theorem ingest_filt_done_entails {c : FullCfg} {accCnf : CNF Nat} {F_cur : List (List Nat)}
    {s0 s : FullState} {acc : List Nat} {cnt new_cnt : BitVec 32} {mrk' : List (BitVec 8)}
    {tmp : List (BitVec 32)}
    (hcs : IngestClauseState c accCnf F_cur s0 acc cnt false s)
    (hclr_sp : FullSparseInvW c
      (CNF.relabel (tumblePi (decide (c.mv < c.extend_cap)) s.core.frame_dec)
        (shiftDownCnf accCnf))
      F_cur { s with core := { s.core with mrk := mrk' } })
    (hent : (CNF.relabel (tumblePi (decide (c.mv < c.extend_cap)) s0.core.frame_dec)
        (shiftDownCnf accCnf)).Entails (cnfOfClauses F_cur))
    (hf : IngestFiltState c { s with core := { s.core with mrk := mrk' } }
      cnt.toNat new_cnt cnt tmp) :
    let tum := decide (c.mv < c.extend_cap)
    let cl := CNF.Clause.ofLiterals (acc.reverse.map kissatLitToDimacsLiteral)
    let F0' := CNF.relabel (tumblePi tum s.core.frame_dec) (shiftDownCnf (accCnf.add cl))
    F0'.EntailsClause (cnfClause ((tmp.take new_cnt.toNat).map BitVec.toNat)) := by
  intro tum cl F0'
  have hF0'_F0 : F0'.Entails (CNF.relabel (tumblePi tum s.core.frame_dec)
      (shiftDownCnf accCnf)) :=
    cnf_relabel_entails_mono (shiftDownCnf_entails_add accCnf cl)
  have hF0'_Fcur : F0'.Entails (cnfOfClauses F_cur) :=
    cnf_entails_trans (by rwa [hcs.hrel_eq] at hF0'_F0) hent
  have hF0'_cl : F0'.EntailsClause (cnfClause (acc.reverse.map
      (tumbleLit tum s.core.frame_dec))) := by
    have h1 := cnf_relabel_entailsClause_mono (r := tumblePi tum s.core.frame_dec)
      (shiftDownCnf_entails_added accCnf cl)
    have hcl_eq : CNF.Clause.relabel (tumblePi tum s.core.frame_dec) (shiftDownClause cl) =
        cnfClause (acc.reverse.map (tumbleLit tum s.core.frame_dec)) := cnfClause_relabel_eq
    rwa [hcl_eq] at h1
  refine entails_of_mem_or_false hF0'_cl fun tl htl => ?_
  rw [List.mem_map] at htl
  obtain ⟨l, hl, rfl⟩ := htl
  have hcov_l := hcs.htmp_cov rfl l (List.mem_reverse.mp hl)
  rw [List.mem_map] at hcov_l
  obtain ⟨x, hx_t, hx_eq⟩ := hcov_l
  rw [List.mem_iff_getElem] at hx_t
  obtain ⟨j, hj, hget⟩ := hx_t
  have hj_cnt : j < cnt.toNat := by simp [List.length_take] at hj; omega
  have hj_len : j < s.core.tmp.length := by
    rw [hclr_sp.1.core_ok.tmp_len_arr]
    have := hcs.hcnt_le; have := hcs.hlen.core_ok.cur_vars_le; have := hcs.hcv
    omega
  have hx_get : (s.core.tmp[j]?.getD 0#32).toNat =
      tumbleLit tum s.core.frame_dec l := by
    rw [List.getElem?_eq_getElem hj_len, Option.getD_some]
    simpa [List.getElem_take, hx_eq] using congrArg BitVec.toNat hget
  rcases hf.hseen j hj_cnt with hm | hvf
  · rw [hx_get] at hm; exact Or.inl hm
  · rw [hx_get] at hvf
    have htl_lt : tumbleLit tum s.core.frame_dec l < 2 * s.core.cur_vars := by
      rw [hcs.hcv]
      exact tumbleLit_lt hcs.htm (hcs.hacc_lt l (List.mem_reverse.mp hl))
        (fun ht => hcs.hacc_map ht l (List.mem_reverse.mp hl))
    have hneg := ingest_level0_false_entails_neg hclr_sp.2.1 hcs.hcl0 htl_lt hvf
    exact Or.inr (cnf_entails_clause_of_entails hF0'_Fcur hneg)

/-! ## 6. Fuel Irrelevance, `UnitUnsatTrace` Bridges & Post-Loop Helpers -/

theorem parseClauseAux_fuel_irrel {f1 f2 mv : Nat} {acc : List (Literal Nat)}
    {bs : List UInt8} (h1 : bs.length + 1 ≤ f1) (h2 : bs.length + 1 ≤ f2) :
    parseClauseAux f1 mv acc bs = parseClauseAux f2 mv acc bs := by
  have hgo : ∀ (n : Nat) (f1 f2 : Nat) (acc : List (Literal Nat)) (bs : List UInt8),
      bs.length = n → n + 1 ≤ f1 → n + 1 ≤ f2 →
      parseClauseAux f1 mv acc bs = parseClauseAux f2 mv acc bs := by
    intro n
    refine Nat.strongRecOn n fun n ih f1 f2 acc bs hlen hf1 hf2 => ?_
    obtain ⟨f1', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f1 ≠ 0)
    obtain ⟨f2', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f2 ≠ 0)
    rw [parseClauseAux_eq_nextLitPure, parseClauseAux_eq_nextLitPure]
    cases hn : nextLitPure mv bs with
    | err => rfl
    | endClause rest => rfl
    | lit l rest =>
      have ⟨_, _, hlt⟩ := nextLitPure_lit_bounds hn
      exact ih rest.length (by omega) f1' f2' _ rest rfl (by omega) (by omega)
  exact hgo bs.length f1 f2 acc bs rfl h1 h2

theorem ingest_val_false_of_vext {c : FullCfg} {accCnf : CNF Nat} {F_cur : List (List Nat)}
    {s0 s : FullState} {acc : List Nat} {cnt : BitVec 32} {taut : Bool}
    {vext : List (BitVec 8)} {l : Nat}
    (hcs : IngestClauseState c accCnf F_cur s0 acc cnt taut s)
    (hl : l < 2 * c.mv)
    (hrel : TumbleValsRel (decide (c.mv < c.extend_cap)) c.mv s0.core.frame_dec vext s0.core.vals)
    (hvf : vext[l]?.getD 0#8 = 0xFF#8) :
    s.core.vals[tumbleLit (decide (c.mv < c.extend_cap)) s.core.frame_dec l]?.getD 0#8 =
      0xFF#8 := by
  have h0 := hrel l hl
  rw [hvf] at h0
  cases ht : decide (c.mv < c.extend_cap) with
  | false =>
    simp only [ht, tumbleLit_false] at h0
    rw [hcs.hvals, tumbleLit_false]; exact h0.symm
  | true =>
    rw [ht] at h0
    have hmap0 : s0.core.frame_dec[l / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
      intro hff; simp [hff] at h0
    simp only [hmap0, and_false, ↓reduceIte] at h0
    have hfd_eq := hcs.hfd_mono (l / 2) (by omega) hmap0
    have htl_eq : tumbleLit true s.core.frame_dec l = tumbleLit true s0.core.frame_dec l := by
      unfold tumbleLit tumblePi; simp only [↓reduceIte, hfd_eq]
    rw [htl_eq, hcs.hvals]; exact h0.symm

theorem ingest_val_zero_of_vext {c : FullCfg} {accCnf : CNF Nat} {F_cur : List (List Nat)}
    {s0 s : FullState} {acc : List Nat} {cnt : BitVec 32} {taut : Bool}
    {vext : List (BitVec 8)} {l : Nat}
    (hcs : IngestClauseState c accCnf F_cur s0 acc cnt taut s)
    (hvl : 2 * c.mv ≤ vext.length) (hl : l < 2 * c.mv) (hl_acc : l ∈ acc)
    (hrel : TumbleValsRel (decide (c.mv < c.extend_cap)) c.mv s0.core.frame_dec vext s0.core.vals)
    (hunz : TumbleUnusedZero (decide (c.mv < c.extend_cap)) c.mv s0.scratch.extend_len
      s0.core.vals)
    (hv0 : vext[l]?.getD 0#8 = 0#8) :
    s.core.vals[tumbleLit (decide (c.mv < c.extend_cap)) s.core.frame_dec l]?.getD 0#8 = 0#8 := by
  obtain ⟨hr1, _⟩ := hcs.hval_rel vext hvl hrel hunz
  have h0 := hr1 l hl
  rw [hv0] at h0
  have hnotun : ¬ (decide (c.mv < c.extend_cap) = true ∧
      s.core.frame_dec[l / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) := by
    rintro ⟨ht, hff⟩; exact hcs.hacc_map ht l hl_acc hff
  simp only [hnotun, ↓reduceIte] at h0
  exact h0.symm

theorem ingest_clear_step {c : FullCfg} {tmp : List (BitVec 32)} {mrk : List (BitVec 8)}
    {k cnt : Nat} (hkv_len : (tmp[k]?.getD 0#32).toNat / 2 < mrk.length)
    (hinv : ∀ v < c.max_vars, mrk[v]?.getD 0#8 ≠ 0#8 →
      ∃ idx, k ≤ idx ∧ idx < cnt ∧ (tmp[idx]?.getD 0#32).toNat / 2 = v) :
    ∀ v < c.max_vars, (mrk.set ((tmp[k]?.getD 0#32).toNat / 2) 0#8)[v]?.getD 0#8 ≠ 0#8 →
      ∃ idx, k + 1 ≤ idx ∧ idx < cnt ∧ (tmp[idx]?.getD 0#32).toNat / 2 = v := by
  intro v hv hne
  by_cases he : v = (tmp[k]?.getD 0#32).toNat / 2
  · subst he; rw [List.getElem?_set_self hkv_len] at hne; exact absurd rfl hne
  · rw [List.getElem?_set_ne (Ne.symm he)] at hne
    obtain ⟨idx, h1, h2, h3⟩ := hinv v hv hne
    have hidx_ne : idx ≠ k := fun h => he (h ▸ h3.symm)
    exact ⟨idx, by omega, h2, h3⟩

theorem ingest_with_tmp_sparse {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {tmp' : List (BitVec 32)}
    (hsp : FullSparseInvW c F0 F_cur s) (hcl0 : s.core.cur_level = 0)
    (htl : tmp'.length = c.max_vars) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with tmp := tmp' } } :=
  ⟨⟨{ hsp.1.core_ok with tmp_len_arr := htl }, hsp.1.scratch_ok⟩,
   ingest_witness_with_fd_dcur_mrk_tmp hsp.2.1 hcl0,
   hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

theorem ingest_take_one_eq {tmp : List (BitVec 32)} (hpos : 0 < tmp.length) :
    (tmp.take 1).map BitVec.toNat = [(tmp[0]?.getD 0#32).toNat] := by
  cases tmp with
  | nil => simp at hpos
  | cons a _ => simp

theorem ingest_add_cl_pre {c : FullCfg} {accCnf : CNF Nat} {F_cur : List (List Nat)}
    {s0 s : FullState} {acc : List Nat} {cnt new_cnt : BitVec 32} {mrk' : List (BitVec 8)}
    {tmp : List (BitVec 32)} {flags' : List (BitVec 32)} {unass' : BitVec 64} {sc' : FullScratch}
    (hcs : IngestClauseState c accCnf F_cur s0 acc cnt false s)
    (hclr_sp : FullSparseInvW c
      (CNF.relabel (tumblePi (decide (c.mv < c.extend_cap)) s.core.frame_dec)
        (shiftDownCnf accCnf))
      F_cur { s with core := { s.core with mrk := mrk' } })
    (hent : (CNF.relabel (tumblePi (decide (c.mv < c.extend_cap)) s0.core.frame_dec)
        (shiftDownCnf accCnf)).Entails (cnfOfClauses F_cur))
    (hf : IngestFiltState c { s with core := { s.core with mrk := mrk' } }
      cnt.toNat new_cnt cnt tmp)
    (hact_sp : FullSparseInvW c
      (CNF.relabel (tumblePi (decide (c.mv < c.extend_cap)) s.core.frame_dec)
        (shiftDownCnf accCnf))
      F_cur { core := { s.core with mrk := mrk', tmp := tmp,
                                    flags := flags', unassigned := unass' }
              scratch := sc' }) :
    let tum := decide (c.mv < c.extend_cap)
    let cl := CNF.Clause.ofLiterals (acc.reverse.map kissatLitToDimacsLiteral)
    let F0' := CNF.relabel (tumblePi tum s.core.frame_dec) (shiftDownCnf (accCnf.add cl))
    let keepLits := (tmp.take new_cnt.toNat).map BitVec.toNat
    let F_cur' := keepLits :: F_cur
    let s_act : FullState :=
      { core := { s.core with mrk := mrk', tmp := tmp, flags := flags', unassigned := unass' }
        scratch := sc' }
    FullSparseInvW c F0' F_cur' s_act ∧
    F0'.Entails (cnfOfClauses F_cur') ∧
    (∀ l ∈ keepLits, l < 2 * s_act.core.cur_vars) ∧
    ((tmp.take new_cnt.toNat).map fun x => x.toNat / 2).Nodup ∧
    (cnfOfClauses F_cur').EntailsClause (cnfClause keepLits) := by
  intro tum cl F0' keepLits F_cur' s_act
  have hF0'_F0 : F0'.Entails (CNF.relabel (tumblePi tum s.core.frame_dec) (shiftDownCnf accCnf)) :=
    cnf_relabel_entails_mono (shiftDownCnf_entails_add accCnf cl)
  have hF0'_Fcur : F0'.Entails (cnfOfClauses F_cur) :=
    cnf_entails_trans (by rwa [hcs.hrel_eq] at hF0'_F0) hent
  have hF0'_keep : F0'.EntailsClause (cnfClause keepLits) :=
    ingest_filt_done_entails hcs hclr_sp hent hf
  have hkeep_lt : ∀ l ∈ keepLits, l < 2 * s_act.core.cur_vars := by
    intro l hl
    rw [List.mem_map] at hl
    obtain ⟨x, hx_t, rfl⟩ := hl
    rw [List.mem_iff_getElem] at hx_t
    obtain ⟨k, hk, hget⟩ := hx_t
    have hk_nc : k < new_cnt.toNat := by simp [List.length_take] at hk; omega
    have hk_len : k < tmp.length := by
      rw [hf.htmp_len]; have := hf.hle; have := hcs.hcnt_le
      have := hcs.hlen.core_ok.cur_vars_le; have := hcs.hcv; omega
    have hx_eq : tmp[k]?.getD 0#32 = x := by
      rw [List.getElem?_eq_getElem hk_len, Option.getD_some]
      simpa [List.getElem_take] using hget
    have := (hf.hkept k hk_nc).1
    rw [hx_eq] at this
    change x.toNat < 2 * s.core.cur_vars; rw [hcs.hcv]; exact this
  have hnd : ((tmp.take new_cnt.toNat).map fun x => x.toNat / 2).Nodup := by
    have h1 := hf.hnd
    simp only [Nat.sub_self, List.take_zero, List.map_nil, List.append_nil] at h1
    exact h1
  have hw' : FullWitnessInv c F0' F_cur' s_act.core :=
    ingest_witness_add_clause (ingest_witness_weaken_F0 hact_sp.2.1 hF0'_F0)
      hkeep_lt hF0'_Fcur hF0'_keep
  have hmem_head : (cnfOfClauses F_cur').EntailsClause (cnfClause keepLits) := by
    apply CNF.entails_clause_of_mem
    rw [CNF.Internal.mem_iff]
    simp [F_cur', cnfOfClauses]
  exact ⟨⟨hact_sp.1, hw', hact_sp.2.2.1, hact_sp.2.2.2.1, hact_sp.2.2.2.2.1, hact_sp.2.2.2.2.2⟩,
    cnf_entails_cnfOfClauses_cons hF0'_Fcur hF0'_keep, hkeep_lt, hnd, hmem_head⟩

end LeanQbe.T.Examples.Kissat.Proof.Parse
