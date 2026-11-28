/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Parse.WpIngestInv
public import LeanQbe.T.Examples.Kissat.Src.Parse
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.ControlComb

/-!
# Soundness Proof for `full_ingest_cl` (`Proof.Parse.WpIngest`)

Proves parametric `(Γ : Env)` `Func.wp` theorem `full_ingest_cl_wp` against canonical
`Parse.Spec.fullIngestClTumSpec`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Parse

open Std.Sat
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Src.Parse
open Kraken.Bedrock2.Test
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics

/-! ## 1. Pure Postcondition Discharge Helpers -/

private abbrev IngestClauseCont (c : FullCfg) (accCnf : CNF Nat) (s0 : FullState)
    (cnf_ptr : BitVec 64) (cnfBytes : List UInt8) (i0 : Nat) (R : Mem 64 → Prop)
    (Q : Post [i64]) (cl : CNF.Clause Nat) (rest : List UInt8) : Prop :=
  let tum := decide (c.mv < c.extend_cap)
  ∀ r s' j m',
    (∀ lit ∈ cl.literals, 1 ≤ lit.1) →
    i0 < j → j ≤ cnfBytes.length → cnfBytes.drop j = rest →
    s'.LengthsOk c → s'.core.cur_vars = c.mv →
    s'.core.d_cur = cnf_ptr + BitVec.ofNat 64 j →
    s'.core.cur_level = 0 → s'.core.fuel = s0.core.fuel → s'.core.oom = s0.core.oom →
    s'.core.probing = s0.core.probing →
    TumbleInv tum c.mv s'.scratch.extend_len s'.core.frame_dec →
    TumbleCovers tum s'.core.frame_dec (shiftDownCnf (accCnf.add cl)) →
    CnfVarsLt c.mv (shiftDownCnf (accCnf.add cl)) →
    (r = 1#64 ∨ r = 2#64 ∨ r = 3#64) →
    (r = 1#64 → ∃ F_cur',
      FullSparseInvW c
        (CNF.relabel (tumblePi tum s'.core.frame_dec) (shiftDownCnf (accCnf.add cl)))
        F_cur' s' ∧
      (CNF.relabel (tumblePi tum s'.core.frame_dec) (shiftDownCnf (accCnf.add cl))).Entails
        (cnfOfClauses F_cur')) →
    (r = 2#64 → (shiftDownCnf (accCnf.add cl)).Unsat) →
    (∀ vext l, 2 * c.mv ≤ vext.length → l < 2 * c.mv →
      TumbleValsRel tum c.mv s0.core.frame_dec vext s0.core.vals →
      TumbleUnusedZero tum c.mv s0.scratch.extend_len s0.core.vals →
      cl = CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l] →
      vext[l]?.getD 0#8 = 0#8 →
      r = 1#64 ∧
      TumbleValsRel tum c.mv s'.core.frame_dec
        ((vext.set l 1#8).set (l ^^^ 1) 0xFF#8) s'.core.vals ∧
      TumbleUnusedZero tum c.mv s'.scratch.extend_len s'.core.vals ∧
      s'.core.trail_end = s0.core.trail_end + 1 ∧
      s'.core.propagated = s0.core.propagated) →
    (∀ vext l, 2 * c.mv ≤ vext.length → l < 2 * c.mv →
      TumbleValsRel tum c.mv s0.core.frame_dec vext s0.core.vals →
      cl = CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l] →
      vext[l]?.getD 0#8 = 0xFF#8 → r = 2#64) →
    (bytes cnf_ptr cnfBytes ⋆ FullMem c s' ⋆ R) m' → Q (r, ()) m'

private theorem ingest_taut_unit0 {acc : List Nat} {l : Nat}
    (h2 : 2 ≤ acc.length)
    (hcl : CNF.Clause.ofLiterals (acc.reverse.map kissatLitToDimacsLiteral) =
      CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l]) : False := by
  have := ingest_singleton_acc hcl; subst this; simp at h2

private theorem ingest_exit_keep_Fcur {c : FullCfg} {accCnf : CNF Nat} {F_cur : List (List Nat)}
    {s0 s s' : FullState} {acc : List Nat} {cnt : BitVec 32} {taut : Bool}
    {cnf_ptr : BitVec 64} {cnfBytes rest : List UInt8} {i0 j : Nat}
    {R : Mem 64 → Prop} {Q : Post [i64]} {m' : Mem 64}
    (hcs : IngestClauseState c accCnf F_cur s0 acc cnt taut s)
    (hvb0 : CnfVarsLt c.mv (shiftDownCnf accCnf))
    (hent0 : (CNF.relabel (tumblePi (decide (c.mv < c.extend_cap)) s0.core.frame_dec)
      (shiftDownCnf accCnf)).Entails (cnfOfClauses F_cur))
    (hi0_j : i0 < j) (hj_hi : j ≤ cnfBytes.length) (hdrop : cnfBytes.drop j = rest)
    (hcv' : s'.core.cur_vars = c.mv) (hdcur' : s'.core.d_cur = cnf_ptr + BitVec.ofNat 64 j)
    (hcl0' : s'.core.cur_level = 0) (hfuel' : s'.core.fuel = s0.core.fuel)
    (hoom' : s'.core.oom = s0.core.oom) (hprob' : s'.core.probing = s0.core.probing)
    (hfd' : s'.core.frame_dec = s.core.frame_dec)
    (hext' : s'.scratch.extend_len = s.scratch.extend_len)
    (hsp' : FullSparseInvW c
      (CNF.relabel (tumblePi (decide (c.mv < c.extend_cap)) s.core.frame_dec) (shiftDownCnf accCnf))
      F_cur s')
    (hno_u0 : ∀ vext l, 2 * c.mv ≤ vext.length → l < 2 * c.mv →
      TumbleValsRel (decide (c.mv < c.extend_cap)) c.mv s0.core.frame_dec vext s0.core.vals →
      TumbleUnusedZero (decide (c.mv < c.extend_cap)) c.mv s0.scratch.extend_len s0.core.vals →
      CNF.Clause.ofLiterals (acc.reverse.map kissatLitToDimacsLiteral) =
        CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l] →
      vext[l]?.getD 0#8 = 0#8 → False)
    (hno_uf : ∀ vext l, 2 * c.mv ≤ vext.length → l < 2 * c.mv →
      TumbleValsRel (decide (c.mv < c.extend_cap)) c.mv s0.core.frame_dec vext s0.core.vals →
      CNF.Clause.ofLiterals (acc.reverse.map kissatLitToDimacsLiteral) =
        CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l] →
      vext[l]?.getD 0#8 = 0xFF#8 → False)
    (hm' : (FullMem c s' ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m')
    (hQ : IngestClauseCont c accCnf s0 cnf_ptr cnfBytes i0 R Q
      (CNF.Clause.ofLiterals (acc.reverse.map kissatLitToDimacsLiteral)) rest) :
    Q (1#64, ()) m' := by
  obtain ⟨hpos, hcov', hvb', hF0'_F0, _⟩ := ingest_clause_common hcs hvb0
  refine hQ 1#64 s' j m' hpos hi0_j hj_hi hdrop hsp'.1 hcv' hdcur' hcl0' hfuel' hoom' hprob'
    (hfd' ▸ hext' ▸ hcs.htm) (hfd' ▸ hcov') hvb' (Or.inl rfl)
    (fun _ => ⟨F_cur, ?_, ?_⟩) (fun h => by cases h)
    (fun vext l hvl hl hr hu hcl hv0 => False.elim (hno_u0 vext l hvl hl hr hu hcl hv0))
    (fun vext l hvl hl hr hcl hvf => False.elim (hno_uf vext l hvl hl hr hcl hvf))
    (fullMem_join_bytes hm')
  · rw [hfd']
    exact ⟨hsp'.1, ingest_witness_weaken_F0 hsp'.2.1 hF0'_F0, hsp'.2.2.1,
      hsp'.2.2.2.1, hsp'.2.2.2.2.1, hsp'.2.2.2.2.2⟩
  · rw [hfd']
    exact cnf_entails_trans (by rwa [hcs.hrel_eq] at hF0'_F0) hent0

private theorem ingest_sat_unit_absurd {c : FullCfg} {accCnf : CNF Nat}
    {F_cur : List (List Nat)} {s0 s : FullState} {acc : List Nat} {cnt : BitVec 32}
    {idx l : Nat} {vext : List (BitVec 8)}
    (hcs : IngestClauseState c accCnf F_cur s0 acc cnt false s)
    (hidx : idx < cnt.toNat)
    (hval1 : s.core.vals[(s.core.tmp[idx]?.getD 0#32).toNat]?.getD 0#8 = 1#8)
    (hcl : CNF.Clause.ofLiterals (acc.reverse.map kissatLitToDimacsLiteral) =
      CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l]) :
    ((2 * c.mv ≤ vext.length → l < 2 * c.mv →
      TumbleValsRel (decide (c.mv < c.extend_cap)) c.mv s0.core.frame_dec vext s0.core.vals →
      TumbleUnusedZero (decide (c.mv < c.extend_cap)) c.mv s0.scratch.extend_len s0.core.vals →
      vext[l]?.getD 0#8 = 0#8 → False) ∧
     (l < 2 * c.mv →
      TumbleValsRel (decide (c.mv < c.extend_cap)) c.mv s0.core.frame_dec vext s0.core.vals →
      vext[l]?.getD 0#8 = 0xFF#8 → False)) := by
  have ⟨hcnt1, h0_eq⟩ := ingest_singleton_tmp0 hcs rfl hcl
  have hidx0 : idx = 0 := by omega
  subst hidx0
  rw [h0_eq] at hval1
  have hacc : acc = [l] := ingest_singleton_acc hcl
  refine ⟨fun hvl hl hrel hunz hv0 => ?_, fun hl hrel hvf => ?_⟩
  · have := ingest_val_zero_of_vext hcs hvl hl (by rw [hacc]; exact List.mem_cons_self)
      hrel hunz hv0
    rw [this] at hval1; cases hval1
  · have := ingest_val_false_of_vext hcs hl hrel hvf
    rw [this] at hval1; cases hval1

private theorem ingest_empty_unit0_absurd {c : FullCfg} {accCnf : CNF Nat}
    {F_cur : List (List Nat)} {s0 s : FullState} {acc : List Nat} {cnt : BitVec 32}
    {mrk' : List (BitVec 8)} {tmp : List (BitVec 32)} {vext : List (BitVec 8)} {l : Nat}
    (hcs : IngestClauseState c accCnf F_cur s0 acc cnt false s)
    (hf : IngestFiltState c { s with core := { s.core with mrk := mrk' } }
      cnt.toNat 0#32 cnt tmp)
    (hvl : 2 * c.mv ≤ vext.length) (hl : l < 2 * c.mv)
    (hrel : TumbleValsRel (decide (c.mv < c.extend_cap)) c.mv s0.core.frame_dec vext s0.core.vals)
    (hunz : TumbleUnusedZero (decide (c.mv < c.extend_cap)) c.mv s0.scratch.extend_len
      s0.core.vals)
    (hcl : CNF.Clause.ofLiterals (acc.reverse.map kissatLitToDimacsLiteral) =
      CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l])
    (hv0 : vext[l]?.getD 0#8 = 0#8) : False := by
  have ⟨hcnt1, h0_eq⟩ := ingest_singleton_tmp0 hcs rfl hcl
  have hacc : acc = [l] := ingest_singleton_acc hcl
  have hval0 := ingest_val_zero_of_vext hcs hvl hl (by rw [hacc]; exact List.mem_cons_self)
    hrel hunz hv0
  have hs := hf.hseen 0 (by omega)
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, List.take_zero, List.map_nil,
    List.not_mem_nil, false_or] at hs
  change s.core.vals[(s.core.tmp[0]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8 at hs
  rw [h0_eq, hval0] at hs; cases hs

private theorem ingest_unit_rel_post {c : FullCfg} {accCnf : CNF Nat}
    {F_cur : List (List Nat)} {s0 s : FullState} {acc : List Nat} {cnt : BitVec 32}
    {mrk' : List (BitVec 8)} {tmp : List (BitVec 32)} {l0 : BitVec 32}
    {vext : List (BitVec 8)} {l : Nat}
    (hcs : IngestClauseState c accCnf F_cur s0 acc cnt false s)
    (hf : IngestFiltState c { s with core := { s.core with mrk := mrk' } }
      cnt.toNat 1#32 cnt tmp)
    (hl0 : l0 = tmp[0]?.getD 0#32)
    (hvl : 2 * c.mv ≤ vext.length) (hl : l < 2 * c.mv)
    (hrel : TumbleValsRel (decide (c.mv < c.extend_cap)) c.mv s0.core.frame_dec vext s0.core.vals)
    (hunz : TumbleUnusedZero (decide (c.mv < c.extend_cap)) c.mv s0.scratch.extend_len
      s0.core.vals)
    (hcl : CNF.Clause.ofLiterals (acc.reverse.map kissatLitToDimacsLiteral) =
      CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l]) :
    TumbleValsRel (decide (c.mv < c.extend_cap)) c.mv s.core.frame_dec
      ((vext.set l 1#8).set (l ^^^ 1) 0xFF#8)
      ((s.core.vals.set l0.toNat 1#8).set (l0.toNat ^^^ 1) 0xFF#8) ∧
    TumbleUnusedZero (decide (c.mv < c.extend_cap)) c.mv s.scratch.extend_len
      ((s.core.vals.set l0.toNat 1#8).set (l0.toNat ^^^ 1) 0xFF#8) := by
  have ⟨hcnt1, h0_eq⟩ := ingest_singleton_tmp0 hcs rfl hcl
  have hacc : acc = [l] := ingest_singleton_acc hcl
  have hkept0 := hf.hkept 0 (by simp)
  have htmp_pos : 0 < s.core.tmp.length := by
    rw [hcs.hlen.core_ok.tmp_len_arr]; have := hcs.hlen.core_ok.cur_vars_le
    have := hcs.hcv; omega
  have hmem0 : l0.toNat ∈ [(s.core.tmp[0]?.getD 0#32).toNat] := by
    rw [hl0, ← ingest_take_one_eq htmp_pos, ← hcnt1]; exact hkept0.2.2
  have hl0_eq : l0.toNat = tumbleLit (decide (c.mv < c.extend_cap)) s.core.frame_dec l := by
    simpa [h0_eq] using hmem0
  obtain ⟨hr1, hu1⟩ := hcs.hval_rel vext hvl hrel hunz
  have hvl_int : 2 * c.mv ≤ s.core.vals.length := by
    rw [hcs.hlen.core_ok.vals_len]; have := hcs.hlen.core_ok.cur_vars_le
    have := hcs.hcv; omega
  have hmap_l : decide (c.mv < c.extend_cap) = true →
      s.core.frame_dec[l / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 :=
    fun ht => hcs.hacc_map ht l (by rw [hacc]; exact List.mem_cons_self)
  rw [hl0_eq]
  refine ⟨tumbleValsRel_assign_unit hcs.htm hr1 hvl hvl_int hl hmap_l,
    tumbleUnusedZero_assign hu1 fun ht => ?_⟩
  have htm' := hcs.htm ht
  rcases htm'.2.2.1 (l / 2) (by omega) with hff | hlt
  · exact absurd hff (hmap_l ht)
  · unfold tumbleLit tumblePi; simp only [ht, ↓reduceIte]; omega

private theorem ingest_unit_false_absurd {c : FullCfg} {accCnf : CNF Nat}
    {F_cur : List (List Nat)} {s0 s : FullState} {acc : List Nat} {cnt : BitVec 32}
    {mrk' : List (BitVec 8)} {tmp : List (BitVec 32)} {vext : List (BitVec 8)} {l : Nat}
    (hcs : IngestClauseState c accCnf F_cur s0 acc cnt false s)
    (hf : IngestFiltState c { s with core := { s.core with mrk := mrk' } }
      cnt.toNat 1#32 cnt tmp)
    (hl : l < 2 * c.mv)
    (hrel : TumbleValsRel (decide (c.mv < c.extend_cap)) c.mv s0.core.frame_dec vext s0.core.vals)
    (hcl : CNF.Clause.ofLiterals (acc.reverse.map kissatLitToDimacsLiteral) =
      CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l])
    (hvf : vext[l]?.getD 0#8 = 0xFF#8) : False := by
  have ⟨hcnt1, h0_eq⟩ := ingest_singleton_tmp0 hcs rfl hcl
  have hkept0 := hf.hkept 0 (by simp)
  have htmp_pos : 0 < s.core.tmp.length := by
    rw [hcs.hlen.core_ok.tmp_len_arr]; have := hcs.hlen.core_ok.cur_vars_le
    have := hcs.hcv; omega
  have hmem0 : (tmp[0]?.getD 0#32).toNat ∈ [(s.core.tmp[0]?.getD 0#32).toNat] := by
    rw [← ingest_take_one_eq htmp_pos, ← hcnt1]; exact hkept0.2.2
  have hl0_eq : (tmp[0]?.getD 0#32).toNat =
      tumbleLit (decide (c.mv < c.extend_cap)) s.core.frame_dec l := by
    simpa [h0_eq] using hmem0
  have hv0 : s.core.vals[(tmp[0]?.getD 0#32).toNat]?.getD 0#8 = 0#8 := hkept0.2.1
  rw [hl0_eq, ingest_val_false_of_vext hcs hl hrel hvf] at hv0
  cases hv0

private theorem ingest_exit_ge2 {c : FullCfg} {accCnf : CNF Nat} {F_cur F_cur' : List (List Nat)}
    {s0 s s' : FullState} {acc : List Nat} {cnt new_cnt : BitVec 32} {r_out : BitVec 64}
    {cnf_ptr : BitVec 64} {cnfBytes rest : List UInt8} {i0 j : Nat}
    {R : Mem 64 → Prop} {Q : Post [i64]} {m' : Mem 64}
    (hcs : IngestClauseState c accCnf F_cur s0 acc cnt false s)
    (hvb0 : CnfVarsLt c.mv (shiftDownCnf accCnf))
    (hle : new_cnt.toNat ≤ cnt.toNat) (hge2 : 2 ≤ new_cnt.toNat)
    (hi0_j : i0 < j) (hj_hi : j ≤ cnfBytes.length) (hdrop : cnfBytes.drop j = rest)
    (hcv' : s'.core.cur_vars = c.mv) (hdcur' : s'.core.d_cur = cnf_ptr + BitVec.ofNat 64 j)
    (hcl0' : s'.core.cur_level = 0) (hfuel' : s'.core.fuel = s0.core.fuel)
    (hoom' : s'.core.oom = s0.core.oom) (hprob' : s'.core.probing = s0.core.probing)
    (hfd' : s'.core.frame_dec = s.core.frame_dec)
    (hext' : s'.scratch.extend_len = s.scratch.extend_len)
    (hr : r_out = 1#64 ∨ r_out = 3#64)
    (hsp' : FullSparseInvW c
      (CNF.relabel (tumblePi (decide (c.mv < c.extend_cap)) s.core.frame_dec)
        (shiftDownCnf (accCnf.add
          (CNF.Clause.ofLiterals (acc.reverse.map kissatLitToDimacsLiteral)))))
      F_cur' s')
    (hent' : (CNF.relabel (tumblePi (decide (c.mv < c.extend_cap)) s.core.frame_dec)
      (shiftDownCnf (accCnf.add
        (CNF.Clause.ofLiterals (acc.reverse.map kissatLitToDimacsLiteral))))).Entails
      (cnfOfClauses F_cur'))
    (hm' : (FullMem c s' ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m')
    (hQ : IngestClauseCont c accCnf s0 cnf_ptr cnfBytes i0 R Q
      (CNF.Clause.ofLiterals (acc.reverse.map kissatLitToDimacsLiteral)) rest) :
    Q (r_out, ()) m' := by
  obtain ⟨hpos, hcov', hvb', _, _⟩ := ingest_clause_common hcs hvb0
  have hno : ∀ l, CNF.Clause.ofLiterals (acc.reverse.map kissatLitToDimacsLiteral) =
      CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l] → False := fun l hcl => by
    have ⟨hcnt1, _⟩ := ingest_singleton_tmp0 hcs rfl hcl; omega
  refine hQ r_out s' j m' hpos hi0_j hj_hi hdrop hsp'.1 hcv' hdcur' hcl0' hfuel' hoom' hprob'
    (hfd' ▸ hext' ▸ hcs.htm) (hfd' ▸ hcov') hvb'
    (hr.elim Or.inl (fun h => Or.inr (Or.inr h)))
    (fun _ => ⟨F_cur', hfd' ▸ hsp', hfd' ▸ hent'⟩)
    (fun h2 => by rcases hr with rfl | rfl <;> cases h2)
    (fun _ l _ _ _ _ hcl _ => False.elim (hno l hcl))
    (fun _ l _ _ _ hcl _ => False.elim (hno l hcl))
    (fullMem_join_bytes hm')

private theorem ingest_after_read_unpack {c : FullCfg} {accCnf : CNF Nat}
    {F_cur : List (List Nat)} {s0 : FullState} {cnf_ptr : BitVec 64} {cnfBytes : List UInt8}
    {i0 : Nat} {R : Mem 64 → Prop} {cnt : BitVec 32} {taut err : Bool} {m : Mem 64}
    (h : IngestAfterReadInv c accCnf F_cur s0 cnf_ptr cnfBytes i0 R (cnt, taut, err, ()) m) :
    ∃ s : FullState,
      s.LengthsOk c ∧ s.core.fuel = s0.core.fuel ∧ s.core.oom = s0.core.oom ∧
      s.core.probing = s0.core.probing ∧ cnt.toNat ≤ c.mv ∧
      (FullMem c s ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m ∧
      (err = true → parseClause c.mv (cnfBytes.drop i0) = none) ∧
      (err = false → ∃ j acc rest,
        i0 < j ∧ j ≤ cnfBytes.length ∧ cnfBytes.drop j = rest ∧
        s.core.d_cur = cnf_ptr + BitVec.ofNat 64 j ∧
        parseClause c.mv (cnfBytes.drop i0) =
          some (CNF.Clause.ofLiterals (acc.reverse.map kissatLitToDimacsLiteral), rest) ∧
        IngestClauseState c accCnf F_cur s0 acc cnt taut s) := by
  unfold IngestAfterReadInv at h
  dsimp only at h
  cases err with
  | true =>
    simp only [↓reduceIte] at h
    rcases h with ⟨hnone, s, hlen, hf, ho, hp, hcle, hm⟩
    exact ⟨s, hlen, hf, ho, hp, hcle, hm, fun _ => hnone, (fun h => by cases h)⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    rcases h with ⟨j, acc, rest, s, h1, h2, h3, h4, h5, hcs, hm⟩
    exact ⟨s, hcs.hlen, hcs.hfuel, hcs.hoom, hcs.hprob, hcs.hcnt_le, hm,
      (fun h => by cases h), fun _ => ⟨j, acc, rest, h1, h2, h3, h4, h5, hcs⟩⟩

private theorem ingest_tumble_bv_aux {n l : Nat} (hn : n < 2 ^ 28) (hl : l < 2 * 2 ^ 28) :
    BitVec.setWidth 32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 n ∧
    (BitVec.ofNat 64 n + (1 : BitVec 64)).toNat = n + 1 ∧
    (BitVec.ofNat 32 n).toNat = n ∧
    (BitVec.setWidth 32 (BitVec.ofNat 64 l)).toNat = l ∧
    ((BitVec.setWidth 32 (BitVec.ofNat 64 l)) >>> (1 : Nat)).toNat = l / 2 ∧
    (BitVec.setWidth 64 ((BitVec.setWidth 32 (BitVec.ofNat 64 l)) >>> (1 : Nat))).toNat =
      l / 2 := by
  have h1 : BitVec.setWidth 32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 n := by
    apply BitVec.eq_of_toNat_eq; simp [Nat.mod_eq_of_lt (by omega : n < 2 ^ 32)]
  have h2 : (BitVec.ofNat 64 n + (1 : BitVec 64)).toNat = n + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have h3 : (BitVec.ofNat 32 n).toNat = n := Nat.mod_eq_of_lt (by omega)
  have h4 : (BitVec.setWidth 32 (BitVec.ofNat 64 l)).toNat = l := by
    simp [Nat.mod_eq_of_lt (by omega : l < 2 ^ 32)]
  have h5 : ((BitVec.setWidth 32 (BitVec.ofNat 64 l)) >>> (1 : Nat)).toNat = l / 2 := by
    change ((BitVec.setWidth 32 (BitVec.ofNat 64 l)) >>> 1#32).toNat = l / 2
    rw [ing_bv32_lshr1_toNat, h4]
  have h6 : (BitVec.setWidth 64 ((BitVec.setWidth 32 (BitVec.ofNat 64 l)) >>>
      (1 : Nat))).toNat = l / 2 := by
    rw [BitVec.toNat_setWidth, h5, Nat.mod_eq_of_lt (by omega)]
  exact ⟨h1, h2, h3, h4, h5, h6⟩

private theorem ingest_tumble_mapped_lt {mv next e : Nat} {fd : List (BitVec 32)}
    (hm : TumbleInv true mv next fd) (he : e < mv)
    (hmap : fd[e]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) :
    (fd[e]?.getD 0xFFFFFFFF#32).toNat < mv := by
  have htm := hm rfl
  rcases htm.2.2.1 e he with hff | hlt
  · exact absurd hff hmap
  · exact Nat.lt_of_lt_of_le hlt htm.1

private theorem ingest_mrk_zero_of_done {c : FullCfg} {tmp : List (BitVec 32)}
    {mrk : List (BitVec 8)} {k cnt : Nat} (heq : k = cnt)
    (hinv : ∀ v < c.max_vars, mrk[v]?.getD 0#8 ≠ 0#8 →
      ∃ idx, k ≤ idx ∧ idx < cnt ∧ (tmp[idx]?.getD 0#32).toNat / 2 = v) :
    ∀ v < c.max_vars, mrk[v]?.getD 0#8 = 0#8 := fun v hv =>
  Classical.byContradiction fun hne => by
    obtain ⟨_, h1, h2, _⟩ := hinv v hv hne; omega

private theorem ingest_assign_call_wp (Γ : Env)
    (hAssign : Γ.Has "full_assign_lvl" fullAssignLvlSpec)
    {c : FullCfg} {accCnf : CNF Nat} {F_cur : List (List Nat)} {s0 s : FullState}
    {acc : List Nat} {cnt : BitVec 32} {mrk' : List (BitVec 8)} {tmp1 : List (BitVec 32)}
    {flags1 : List (BitVec 32)} {unass1 : BitVec 64} {sc1 : FullScratch}
    {cnf_ptr : BitVec 64} {cnfBytes rest : List UInt8} {i0 j : Nat}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {m4 : Mem 64}
    (hcs : IngestClauseState c accCnf F_cur s0 acc cnt false s)
    (hvb0 : CnfVarsLt c.mv (shiftDownCnf accCnf))
    (hclr_sp : FullSparseInvW c
      (CNF.relabel (tumblePi (decide (c.mv < c.extend_cap)) s.core.frame_dec) (shiftDownCnf accCnf))
      F_cur { s with core := { s.core with mrk := mrk' } })
    (hent0 : (CNF.relabel (tumblePi (decide (c.mv < c.extend_cap)) s0.core.frame_dec)
      (shiftDownCnf accCnf)).Entails (cnfOfClauses F_cur))
    (hf : IngestFiltState c { s with core := { s.core with mrk := mrk' } }
      cnt.toNat 1#32 cnt tmp1)
    (hi0_j : i0 < j) (hj_hi : j ≤ cnfBytes.length) (hdrop : cnfBytes.drop j = rest)
    (hdcur : s.core.d_cur = cnf_ptr + BitVec.ofNat 64 j)
    (ha_ext : sc1.extend_len = s.scratch.extend_len)
    (ha_sp : FullSparseInvW c
      (CNF.relabel (tumblePi (decide (c.mv < c.extend_cap)) s.core.frame_dec) (shiftDownCnf accCnf))
      F_cur { core := { s.core with mrk := mrk', tmp := tmp1,
                                    flags := flags1, unassigned := unass1 }
              scratch := sc1 })
    (h0_tmp : 0 < tmp1.length)
    (hm4 : (FullMem c { core := { s.core with mrk := mrk', tmp := tmp1,
                                              flags := flags1, unassigned := unass1 }
                        scratch := sc1 } ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m4)
    (hQ : IngestClauseCont c accCnf s0 cnf_ptr cnfBytes i0 R Q
      (CNF.Clause.ofLiterals (acc.reverse.map kissatLitToDimacsLiteral)) rest) :
    wp Γ Q X (Expr.call (V := Val) (L := Cont) (rs := [i64]) "full_assign_lvl"
      (as := [i64, i32, i32, i32]) (bs := [])
      (Arg.var c.hdr, Arg.var (tmp1[0]'h0_tmp), Arg.imm 4294967295#32, Arg.imm 0#32, ())
      fun _ => Expr.ret (Arg.imm 1#64, ())) m4 := by
  let s_a : FullState :=
    { core := { s.core with mrk := mrk', tmp := tmp1, flags := flags1, unassigned := unass1 }
      scratch := sc1 }
  let l0 := tmp1[0]'h0_tmp
  have hl0_eq : l0 = tmp1[0]?.getD 0#32 := by
    rw [List.getElem?_eq_getElem h0_tmp, Option.getD_some]
  have hkept0 := hf.hkept 0 (by simp)
  have hl0_lt : l0.toNat < 2 * s_a.core.cur_vars := by
    change l0.toNat < 2 * s.core.cur_vars; rw [hcs.hcv, hl0_eq]; exact hkept0.1
  have hl0_val0 : s_a.core.vals[l0.toNat]?.getD 0#8 = 0#8 := by rw [hl0_eq]; exact hkept0.2.1
  have hte_lt : s_a.core.trail_end < c.max_vars :=
    Nat.lt_of_lt_of_le (ha_sp.2.1.trail_end_lt_of_unassigned hl0_lt hl0_val0)
      ha_sp.1.core_ok.cur_vars_le
  have hcond_f : ¬ (s_a.core.cur_vars ≤ l0.toNat / 2 ∨ c.max_vars ≤ s_a.core.trail_end ∨
      s_a.core.vals[l0.toNat]?.getD 0#8 ≠ 0#8) := by
    rw [hl0_val0]; exact not_or.mpr ⟨by omega, not_or.mpr ⟨by omega, by simp⟩⟩
  obtain ⟨hpos, hcov', hvb', _, _⟩ := ingest_clause_common hcs hvb0
  obtain ⟨hact_sp', hent', _, _, hmem_head⟩ := ingest_add_cl_pre hcs hclr_sp hent0 hf ha_sp
  refine wp_call_of_spec _ _
    (hAssign _ _ _ _ ⟨c, s_a, bytes cnf_ptr cnfBytes ⋆ R, rfl, ha_sp.1, hm4, ?_⟩)
  dsimp only [Arg.val]
  dsimp only [l0] at hcond_f
  simp only [hcond_f, ↓reduceIte]
  intro flags2 unass2 phases2 m5 hfl2 hph2 hm5
  c0_hfast
  have htk1 : (tmp1.take (1#32).toNat).map BitVec.toNat = [l0.toNat] := by
    have h1 : (1#32).toNat = 1 := rfl
    rw [h1, ingest_take_one_eq h0_tmp, ← hl0_eq]
  have hsp_u := ingest_sparseInvW_assign_level0 (unass' := unass2) hact_sp' hcs.hcl0 hl0_lt hl0_val0
    (by rw [← htk1]; exact hmem_head) hfl2 hph2
  refine hQ 1#64 _ j m5 hpos hi0_j hj_hi hdrop hsp_u.1 hcs.hcv hdcur hcs.hcl0
    hcs.hfuel hcs.hoom hcs.hprob (ha_ext ▸ hcs.htm) hcov' hvb' (Or.inl rfl)
    (fun _ => ⟨_, hsp_u, hent'⟩) (fun h => by cases h)
    (fun vext l hvl hl hr hu hcl _ => by
      have ⟨hr2, hu2⟩ := ingest_unit_rel_post hcs hf hl0_eq hvl hl hr hu hcl
      exact ⟨rfl, hr2, ha_ext ▸ hu2, congrArg (· + 1) hcs.hte, hcs.hprop⟩)
    (fun _ _ _ hl hr hcl hvf => False.elim (ingest_unit_false_absurd hcs hf hl hr hcl hvf))
    (fullMem_join_bytes hm5)

private theorem ingest_add_cl_call_wp (Γ : Env)
    (hAddCl : Γ.Has "full_add_clause" Clause.Spec.fullAddClauseSpec)
    {c : FullCfg} {accCnf : CNF Nat} {F_cur : List (List Nat)} {s0 s : FullState}
    {acc : List Nat} {cnt new_cnt : BitVec 32} {mrk' : List (BitVec 8)} {tmp1 : List (BitVec 32)}
    {flags1 : List (BitVec 32)} {unass1 : BitVec 64} {sc1 : FullScratch}
    {cnf_ptr : BitVec 64} {cnfBytes rest : List UInt8} {i0 j : Nat}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {m4 : Mem 64}
    (hcs : IngestClauseState c accCnf F_cur s0 acc cnt false s)
    (hvb0 : CnfVarsLt c.mv (shiftDownCnf accCnf))
    (hclr_sp : FullSparseInvW c
      (CNF.relabel (tumblePi (decide (c.mv < c.extend_cap)) s.core.frame_dec) (shiftDownCnf accCnf))
      F_cur { s with core := { s.core with mrk := mrk' } })
    (hent0 : (CNF.relabel (tumblePi (decide (c.mv < c.extend_cap)) s0.core.frame_dec)
      (shiftDownCnf accCnf)).Entails (cnfOfClauses F_cur))
    (hf : IngestFiltState c { s with core := { s.core with mrk := mrk' } }
      cnt.toNat new_cnt cnt tmp1)
    (hi0_j : i0 < j) (hj_hi : j ≤ cnfBytes.length) (hdrop : cnfBytes.drop j = rest)
    (hdcur : s.core.d_cur = cnf_ptr + BitVec.ofNat 64 j)
    (hnc_ge2 : 2 ≤ new_cnt.toNat) (hnc_le_mx : new_cnt.toNat ≤ c.max_vars)
    (ha_ext : sc1.extend_len = s.scratch.extend_len)
    (ha_sp : FullSparseInvW c
      (CNF.relabel (tumblePi (decide (c.mv < c.extend_cap)) s.core.frame_dec) (shiftDownCnf accCnf))
      F_cur { core := { s.core with mrk := mrk', tmp := tmp1,
                                    flags := flags1, unassigned := unass1 }
              scratch := sc1 })
    (hm4 : (FullMem c { core := { s.core with mrk := mrk', tmp := tmp1,
                                              flags := flags1, unassigned := unass1 }
                        scratch := sc1 } ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m4)
    (hQ : IngestClauseCont c accCnf s0 cnf_ptr cnfBytes i0 R Q
      (CNF.Clause.ofLiterals (acc.reverse.map kissatLitToDimacsLiteral)) rest) :
    wp Γ Q X (Expr.call (V := Val) (L := Cont) (rs := [i64]) "full_add_clause"
      (as := [i64, i32, i32, .bool]) (bs := [i64])
      (Arg.var c.hdr, Arg.var new_cnt, Arg.imm 0#32, Arg.imm false, ())
      fun p => Expr.let_
        { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
          args := (Arg.var p.fst, Arg.imm 4294967295#64, ()) }
        fun p => Expr.jnz (Arg.var p.fst) (Expr.ret (Arg.imm 3#64, ()))
          (Expr.ret (Arg.imm 1#64, ()))) m4 := by
  let s_a : FullState :=
    { core := { s.core with mrk := mrk', tmp := tmp1, flags := flags1, unassigned := unass1 }
      scratch := sc1 }
  obtain ⟨hact_sp', hent', hkeep_lt, hnd, hmem_head⟩ :=
    ingest_add_cl_pre hcs hclr_sp hent0 hf ha_sp
  refine wp_call_of_spec _ _
    (hAddCl _ _ _ _ ⟨c, _, _, s_a, bytes cnf_ptr cnfBytes ⋆ R, rfl, hact_sp'.1, hact_sp'.2.1,
      hcs.hdense, hnc_le_mx, fun _ => ⟨hkeep_lt, hnd, hmem_head⟩, hm4, ?_⟩)
  dsimp only [Arg.val]
  have hnot_lt2 : ¬ new_cnt.toNat < 2 := by omega
  simp only [hnot_lt2, ↓reduceIte]
  by_cases hnc2 : new_cnt.toNat = 2
  · simp only [hnc2, ↓reduceIte]
    intro r_ac flags2 wvec2 wstk2 wlen2 wu2 nb2 ws2 m5 _ hlen2 hw2 hm5
    let s2 : FullState :=
      { s_a with
        core := { s_a.core with flags := flags2, wvec := wvec2, wstk := wstk2,
                                wlen := wlen2, wusable := wu2, num_binary := nb2 }
        scratch := { s_a.scratch with wsort := ws2 } }
    have hsp2 : FullSparseInvW c _ _ s2 :=
      ⟨hlen2, hw2, hact_sp'.2.2.1, hact_sp'.2.2.2.1,
       ⟨fun i hi => hact_sp'.2.2.2.2.1.1 i hi, hact_sp'.2.2.2.2.1.2⟩, hcs.hdense⟩
    c0_hfast_nogrp
    · exact ingest_exit_ge2 (s' := s2) hcs hvb0 hf.hle hnc_ge2 hi0_j hj_hi hdrop hcs.hcv hdcur
        hcs.hcl0 hcs.hfuel hcs.hoom hcs.hprob rfl ha_ext (Or.inr rfl) hsp2 (hnc2 ▸ hent') hm5 hQ
    · exact ingest_exit_ge2 (s' := s2) hcs hvb0 hf.hle hnc_ge2 hi0_j hj_hi hdrop hcs.hcv hdcur
        hcs.hcl0 hcs.hfuel hcs.hoom hcs.hprob rfl ha_ext (Or.inl rfl) hsp2 (hnc2 ▸ hent') hm5 hQ
  · simp only [hnc2, ↓reduceIte]
    intro r_ac arena2 alen2 wvec2 wstk2 wlen2 wu2 fr2 ni2 nr2 ws2 m5 _ hlen2 hw2 hrefs hnd2 _ hm5
    let s2 : FullState :=
      { s_a with
        core := { s_a.core with arena := arena2, arena_len := alen2, wvec := wvec2,
                                wstk := wstk2, wlen := wlen2, wusable := wu2,
                                first_reducible := fr2, num_irred := ni2, num_redundant := nr2 }
        scratch := { s_a.scratch with wsort := ws2 } }
    have hsp2 : FullSparseInvW c _ _ s2 :=
      ⟨hlen2, hw2, hact_sp'.2.2.1, hnd2 hact_sp'.2.2.2.1,
       ⟨fun i hi => by
          rcases hact_sp'.2.2.2.2.1.1 i hi with h1 | h2
          · exact Or.inl h1
          · exact Or.inr (hrefs _ h2),
        hact_sp'.2.2.2.2.1.2⟩, hcs.hdense⟩
    c0_hfast_nogrp
    · exact ingest_exit_ge2 (s' := s2) hcs hvb0 hf.hle hnc_ge2 hi0_j hj_hi hdrop hcs.hcv hdcur
        hcs.hcl0 hcs.hfuel hcs.hoom hcs.hprob rfl ha_ext (Or.inr rfl) hsp2 hent' hm5 hQ
    · exact ingest_exit_ge2 (s' := s2) hcs hvb0 hf.hle hnc_ge2 hi0_j hj_hi hdrop hcs.hcv hdcur
        hcs.hcl0 hcs.hfuel hcs.hoom hcs.hprob rfl ha_ext (Or.inl rfl) hsp2 hent' hm5 hQ

/-! ## 2. Soundness Proof for `full_ingest_cl` -/

/-- Parametric soundness proof for `full_ingest_cl` against `Parse.Spec.fullIngestClTumSpec`. -/
theorem full_ingest_cl_wp (Γ : Env)
    (hNextLit : Γ.Has "kissat_next_lit" Dimacs.Spec.kissatNextLitSpec)
    (hAct : Γ.Has "full_activate_lit_fid" Spec.fullActivateLitFidSpec)
    (hAssign : Γ.Has "full_assign_lvl" fullAssignLvlSpec)
    (hAddCl : Γ.Has "full_add_clause" Clause.Spec.fullAddClauseSpec) :
    ∀ a m Q X, Spec.fullIngestClTumSpec a m Q X →
      Func.wp Γ full_ingest_cl_body a m Q X := by
  rintro ⟨h, cend, ⟨⟩⟩ m0 Q X
    ⟨c, accCnf, F_cur, s0, cnf_ptr, cnfBytes, i0, R, rfl, rfl, hptr_lt, hi0,
     hcv0, hdcur0, hcl0, htm0, hcov0, hvb0, hsp0, hent0, hm0, hQ⟩
  have hmv_lt := c.hmv; have hmx_lt := c.hmaxv; have hext_lt := c.hext
  unfold dimacsBound at hmv_lt hmx_lt hext_lt
  have hmv_le_mx : c.mv ≤ c.max_vars := hcv0 ▸ hsp0.1.core_ok.cur_vars_le
  have hm0' := fullMem_split_bytes hm0
  unfold Func.wp full_ingest_cl_body
  c0_hfast_nogrp
  refine wp_join_group (ts := [i32, .bool, .bool])
    (IngestAfterReadInv c accCnf F_cur s0 cnf_ptr cnfBytes i0 R) ?_ ?_
  · /- Body of `J_after_read (cnt, taut, err, ())` -/
    rintro _ ⟨cnt, taut, err, ⟨⟩⟩ m1 hAfter
    obtain ⟨s, hlen_s, hfuel_s, hoom_s, hprob_s, hcnt_le, hm1, herr_t, herr_f⟩ :=
      ingest_after_read_unpack hAfter
    have htmp_len := hlen_s.core_ok.tmp_len_arr
    have hmrk_len := hlen_s.core_ok.mrk_len
    /- Loop 1: clear `mrk[tmp[k] >>> 1] := 0#8` for `k < cnt` -/
    refine wp_loop_inv (ts := [i32])
      (fun (k, ()) m2 => k.toNat ≤ cnt.toNat ∧ ∃ mrk1 : List (BitVec 8),
        mrk1.length = c.max_vars ∧
        (FullMem c { s with core := { s.core with mrk := mrk1 } } ⋆
          (bytes cnf_ptr cnfBytes ⋆ R)) m2 ∧
        (err = false → ∀ v < c.max_vars, mrk1[v]?.getD 0#8 ≠ 0#8 →
          ∃ idx, k.toNat ≤ idx ∧ idx < cnt.toNat ∧ (s.core.tmp[idx]?.getD 0#32).toNat / 2 = v))
      (fun (k, ()) _ => cnt.toNat - k.toNat)
      (fun J1 hJ1 => by
        c0_hfast
        refine hJ1 (0#32, ()) m1 ⟨by simp, s.core.mrk, hmrk_len, hm1, fun hef v hv hne => ?_⟩
        obtain ⟨_, _, _, _, _, _, _, _, hcs⟩ := herr_f hef
        obtain ⟨idx, hidx, hdiv⟩ := hcs.hmrk_only v hv hne
        exact ⟨idx, Nat.zero_le _, hidx, hdiv⟩)
      (fun J1 ⟨k, ⟨⟩⟩ m2 ⟨hk_le, mrk1, hmrk1_len, hm2, hinv1⟩ ih1 => ?_)
    c0_hfast_nogrp
    · have hk_lt : k.toNat < cnt.toNat := by c0_bound
      have hk1 : (k + 1#32).toNat = k.toNat + 1 := ing_bv32_ofNat_lt_of_toNat hk_lt
      have hk_tmp : k.toNat < s.core.tmp.length := by rw [htmp_len]; omega
      c0_hfast_nogrp
      refine wp_join0
        (fun m3 => ∃ mrk2 : List (BitVec 8), mrk2.length = c.max_vars ∧
          (FullMem c { s with core := { s.core with mrk := mrk2 } } ⋆
            (bytes cnf_ptr cnfBytes ⋆ R)) m3 ∧
          (err = false → ∀ v < c.max_vars, mrk2[v]?.getD 0#8 ≠ 0#8 →
            ∃ idx, k.toNat + 1 ≤ idx ∧ idx < cnt.toNat ∧
              (s.core.tmp[idx]?.getD 0#32).toNat / 2 = v))
        (fun _ m3 ⟨mrk2, hmrk2_len, hm3, hinv2⟩ => by
          c0_hfast
          exact ih1 (k + 1#32, ()) m3 (by dsimp only; omega)
            ⟨by omega, mrk2, hmrk2_len, hm3, fun hef => by rw [hk1]; exact hinv2 hef⟩)
        (fun Jc hJc => by
          c0_hfast_nogrp
          · have hkv_lt : ((s.core.tmp[k.toNat]'hk_tmp) >>> 1#32).toNat < c.mv := by
              rw [ing_bv32_lshr1_toNat]; omega
            have hkv_div : ((s.core.tmp[k.toNat]'hk_tmp) >>> 1#32).toNat =
                (s.core.tmp[k.toNat]?.getD 0#32).toNat / 2 := by
              rw [ing_bv32_lshr1_toNat, List.getElem?_eq_getElem hk_tmp, Option.getD_some]
            have hkv_mrk : ((s.core.tmp[k.toNat]'hk_tmp) >>> 1#32).toNat < mrk1.length := by
              rw [hmrk1_len]; omega
            c0_hfast_nogrp
            refine hJc _ ⟨mrk1.set ((s.core.tmp[k.toNat]'hk_tmp) >>> 1#32).toNat 0#8,
              by rw [List.length_set, hmrk1_len], by assumption, fun hef => ?_⟩
            rw [hkv_div]; exact ingest_clear_step (hkv_div ▸ hkv_mrk) (hinv1 hef)
          · refine hJc m2 ⟨mrk1, hmrk1_len, hm2, fun hef => ?_⟩
            obtain ⟨_, _, _, _, _, _, _, _, hcs⟩ := herr_f hef
            have hlt := (hcs.htmp_wf k.toNat hk_lt).1
            rw [List.getElem?_eq_getElem hk_tmp, Option.getD_some] at hlt; omega)
    · /- Loop 1 done (`err = true`): `ret 0#64` -/
      have hnone := herr_t (by assumption)
      rw [hnone] at hQ
      exact hQ { s with core := { s.core with mrk := mrk1 } } m2
        ⟨{ hlen_s.core_ok with mrk_len := hmrk1_len }, hlen_s.scratch_ok⟩
        hfuel_s hoom_s hprob_s (fullMem_join_bytes hm2)
    · /- Loop 1 done (`err = false`, `taut = true`): `ret 1#64` -/
      have hef : err = false := by assumption
      obtain ⟨j, acc, rest, hi0_j, hj_hi, hdrop, hdcur, hpc, hcs⟩ := herr_f hef
      rw [hpc] at hQ
      have hclr_sp := ingest_after_clear_sparse hcs hmrk1_len
        (ingest_mrk_zero_of_done (by omega) (hinv1 hef))
      have h2 := hcs.htaut_len (by assumption)
      exact ingest_exit_keep_Fcur (s' := { s with core := { s.core with mrk := mrk1 } })
        hcs hvb0 hent0 hi0_j hj_hi hdrop hcs.hcv hdcur hcs.hcl0
        hcs.hfuel hcs.hoom hcs.hprob rfl rfl hclr_sp
        (fun _ _ _ _ _ _ hcl _ => ingest_taut_unit0 h2 hcl)
        (fun _ _ _ _ _ hcl _ => ingest_taut_unit0 h2 hcl) hm2 hQ
    · /- Loop 1 done (`err = false`, `taut = false`): Loop 2 (`J_filt`) -/
      have hef : err = false := by assumption
      have htf : taut = false := by assumption
      subst htf
      obtain ⟨j, acc, rest, hi0_j, hj_hi, hdrop, hdcur, hpc, hcs⟩ := herr_f hef
      rw [hpc] at hQ
      let s_clr : FullState := { s with core := { s.core with mrk := mrk1 } }
      have hclr_sp := ingest_after_clear_sparse hcs hmrk1_len
        (ingest_mrk_zero_of_done (by omega) (hinv1 hef))
      refine wp_loop_inv (ts := [i32, i32])
        (fun (new_cnt, idx, ()) m3 => ∃ tmp1 : List (BitVec 32),
          IngestFiltState c s_clr cnt.toNat new_cnt idx tmp1 ∧
          (FullMem c { s_clr with core := { s_clr.core with tmp := tmp1 } } ⋆
            (bytes cnf_ptr cnfBytes ⋆ R)) m3)
        (fun (_, idx, ()) _ => cnt.toNat - idx.toNat)
        (fun J2 hJ2 => by
          c0_hfast
          exact hJ2 (0#32, 0#32, ()) m2
            ⟨s.core.tmp, ingest_filt_init hclr_sp.1 hcs.htmp_nd, hm2⟩)
        (fun J2 ⟨new_cnt, idx, ⟨⟩⟩ m3 ⟨tmp1, hf, hm3⟩ ih2 => ?_)
      c0_hfast_nogrp
      · /- Loop 2 body (`idx < cnt`) -/
        have hidx_lt : idx.toNat < cnt.toNat := by omega
        have hidx_tmp : idx.toNat < tmp1.length := by rw [hf.htmp_len]; omega
        have hl_eq : tmp1[idx.toNat]? = s.core.tmp[idx.toNat]? :=
          hf.hrest idx.toNat (Nat.le_refl _) hidx_lt
        have hl_get : tmp1[idx.toNat]'hidx_tmp = s.core.tmp[idx.toNat]?.getD 0#32 := by
          rw [← hl_eq, List.getElem?_eq_getElem hidx_tmp, Option.getD_some]
        have hl_lt : (tmp1[idx.toNat]'hidx_tmp).toNat < 2 * c.mv := by
          rw [hl_get]; exact (hcs.htmp_wf idx.toNat hidx_lt).1
        have hl_vals : (tmp1[idx.toNat]'hidx_tmp).toNat < s.core.vals.length := by
          rw [hclr_sp.1.core_ok.vals_len]; omega
        have hlv_dom := hclr_sp.2.1.vals_domain (tmp1[idx.toNat]'hidx_tmp).toNat
          (by rw [hcs.hcv]; exact hl_lt)
        rw [List.getElem?_eq_getElem hl_vals, Option.getD_some] at hlv_dom
        c0_hfast_nogrp
        · /- `lv > 0` (`lv = 1#8`): early `ret 1#64` -/
          have hlv1 := (ing_bv8_sext32_sgt0_iff hlv_dom).mp (by assumption)
          have hval1 : s.core.vals[(s.core.tmp[idx.toNat]?.getD 0#32).toNat]?.getD 0#8 = 1#8 := by
            rw [← hl_get, List.getElem?_eq_getElem hl_vals, Option.getD_some]; exact hlv1
          exact ingest_exit_keep_Fcur (s' := { s_clr with core := { s_clr.core with tmp := tmp1 } })
            hcs hvb0 hent0 hi0_j hj_hi hdrop hcs.hcv hdcur hcs.hcl0
            hcs.hfuel hcs.hoom hcs.hprob rfl rfl
            (ingest_with_tmp_sparse hclr_sp hcs.hcl0 hf.htmp_len)
            (fun _ _ hvl hl hr hu hcl hv0 =>
              (ingest_sat_unit_absurd hcs hidx_lt hval1 hcl).1 hvl hl hr hu hv0)
            (fun _ _ _ hl hr hcl hvf =>
              (ingest_sat_unit_absurd hcs hidx_lt hval1 hcl).2 hl hr hvf) hm3 hQ
        · /- `lv ≤ 0`: keep if `lv = 0`, skip if `lv = 0xFF` -/
          have hlv_ne1 : s.core.vals[(tmp1[idx.toNat]'hidx_tmp).toNat]'hl_vals ≠ 1#8 :=
            fun h => Bool.false_ne_true ((by assumption : _ = false).symm.trans
              ((ing_bv8_sext32_sgt0_iff hlv_dom).mpr h))
          have hidx1 : (idx + 1#32).toNat = idx.toNat + 1 := ing_bv32_ofNat_lt_of_toNat hidx_lt
          refine wp_join_group (ts := [i32])
            (fun (nc', ()) m4 => ∃ tmp2 : List (BitVec 32),
              IngestFiltState c s_clr cnt.toNat nc' (idx + 1#32) tmp2 ∧
              (FullMem c { s_clr with core := { s_clr.core with tmp := tmp2 } } ⋆
                (bytes cnf_ptr cnfBytes ⋆ R)) m4)
            (fun _ ⟨nc', ⟨⟩⟩ m4 ⟨tmp2, hf2, hm4⟩ => by
              c0_hfast
              exact ih2 (nc', idx + 1#32, ()) m4 (by dsimp only; omega) ⟨tmp2, hf2, hm4⟩)
            (fun Jk hJk => by
              c0_hfast_nogrp
              · have hlv0 := (ing_bv8_sext32_eq0_iff hlv_dom).mp (by assumption)
                have hnc_tmp : new_cnt.toNat < tmp1.length := by
                  rw [hf.htmp_len]; have := hf.hle; omega
                c0_hfast_nogrp
                refine hJk (new_cnt + 1#32, ()) _
                  ⟨tmp1.set new_cnt.toNat (tmp1[idx.toNat]'hidx_tmp), ?_, by assumption⟩
                refine ingest_filt_step_keep hf htmp_len hcnt_le hmv_le_mx hmx_lt hidx_lt
                  (by rw [← hl_eq, List.getElem?_eq_getElem hidx_tmp]) hl_lt ?_
                change s.core.vals[(tmp1[idx.toNat]'hidx_tmp).toNat]?.getD 0#8 = 0#8
                rw [List.getElem?_eq_getElem hl_vals, Option.getD_some]; exact hlv0
              · have hlv_ne0 : s.core.vals[(tmp1[idx.toNat]'hidx_tmp).toNat]'hl_vals ≠ 0#8 :=
                  fun h => (by assumption : _ ≠ _) ((ing_bv8_sext32_eq0_iff hlv_dom).mpr h)
                have hlvf : s.core.vals[(tmp1[idx.toNat]'hidx_tmp).toNat]'hl_vals = 0xFF#8 := by
                  rcases hlv_dom with h | h | h
                  · exact absurd h hlv_ne0
                  · exact absurd h hlv_ne1
                  · exact h
                refine hJk (new_cnt, ()) m3 ⟨tmp1, ?_, hm3⟩
                refine ingest_filt_step_skip hf htmp_len hcnt_le hmv_le_mx hmx_lt hidx_lt
                  (by rw [← hl_eq, List.getElem?_eq_getElem hidx_tmp]) ?_
                change s.core.vals[(tmp1[idx.toNat]'hidx_tmp).toNat]?.getD 0#8 = 0xFF#8
                rw [List.getElem?_eq_getElem hl_vals, Option.getD_some]; exact hlvf)
      · /- Loop 2 done (`idx = cnt`): Loop 3 (`J_act (a, ())`) -/
        have hidx_eq : idx = cnt := BitVec.eq_of_toNat_eq (by have := hf.hidx_le; omega)
        subst hidx_eq
        let s_f : FullState := { s_clr with core := { s_clr.core with tmp := tmp1 } }
        have hf_sp := ingest_with_tmp_sparse hclr_sp hcs.hcl0 hf.htmp_len
        refine wp_loop_inv (ts := [i32])
          (fun (a, ()) m4 => a.toNat ≤ new_cnt.toNat ∧
            ∃ flags1 unass1 sc1,
              let s_a : FullState :=
                { core := { s_f.core with flags := flags1, unassigned := unass1 }, scratch := sc1 }
              FullSparseInvW c
                (CNF.relabel (tumblePi (decide (c.mv < c.extend_cap)) s.core.frame_dec)
                  (shiftDownCnf accCnf))
                F_cur s_a ∧
              FullExtScratchPres s_f s_a ∧
              (FullMem c s_a ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m4)
          (fun (a, ()) _ => new_cnt.toNat - a.toNat)
          (fun J3 hJ3 => by
            c0_hfast
            exact hJ3 (0#32, ()) m3 ⟨by simp, s_f.core.flags, s_f.core.unassigned, s_f.scratch,
              hf_sp, ⟨rfl, rfl⟩, hm3⟩)
          (fun J3 ⟨a, ⟨⟩⟩ m4 ⟨ha_le, flags1, unass1, sc1, ha_sp, ha_pres, hm4⟩ ih3 => ?_)
        let s_a : FullState :=
          { core := { s_f.core with flags := flags1, unassigned := unass1 }, scratch := sc1 }
        c0_hfast_nogrp
        · have ha_lt : a.toNat < new_cnt.toNat := by omega
          have ha1 : (a + 1#32).toNat = a.toNat + 1 := ing_bv32_ofNat_lt_of_toNat ha_lt
          have ha_tmp : a.toNat < tmp1.length := by rw [hf.htmp_len]; have := hf.hle; omega
          c0_hfast_nogrp
          refine wp_call_of_spec _ _
            (hAct _ _ _ _ ⟨c, s_a, bytes cnf_ptr cnfBytes ⋆ R, rfl, ha_sp.1, hm4,
              fun flags2 unass2 sc2 m5 hlen2 hpres2 hm5 => ?_⟩)
          c0_hfast
          exact ih3 (a + 1#32, ()) m5 (by dsimp only; omega)
            ⟨by omega, flags2, unass2, sc2, fullSparseInvW_with_act ha_sp hlen2 hpres2,
              ⟨hpres2.1.trans ha_pres.1, hpres2.2.trans ha_pres.2⟩, hm5⟩
        · /- Loop 3 done, `new_cnt = 0`: `ret 2#64` (UNSAT) -/
          have hnc0 : new_cnt = 0#32 := by assumption
          subst hnc0
          obtain ⟨hpos, hcov', hvb', _, _⟩ := ingest_clause_common hcs hvb0
          have hnil := ingest_filt_done_entails hcs hclr_sp hent0 hf
          simp only [BitVec.toNat_ofNat, Nat.zero_mod, List.take_zero, List.map_nil] at hnil
          exact hQ 2#64 s_a j m4 hpos hi0_j hj_hi hdrop ha_sp.1 hcs.hcv hdcur hcs.hcl0
            hcs.hfuel hcs.hoom hcs.hprob (ha_pres.2 ▸ hcs.htm) hcov' hvb' (Or.inr (Or.inl rfl))
            (fun h => by cases h)
            (fun _ => cnf_unsat_of_relabel_tumble hcs.htm hcov' hvb' (unsat_of_entails_nil hnil))
            (fun _ _ hvl hl hr hu hcl hv0 =>
              False.elim (ingest_empty_unit0_absurd hcs hf hvl hl hr hu hcl hv0))
            (fun _ _ _ _ _ _ _ => rfl) (fullMem_join_bytes hm4)
        · /- Loop 3 done, `new_cnt = 1`: `full_assign_lvl` + `ret 1#64` -/
          have hnc1 : new_cnt = 1#32 := by assumption
          subst hnc1
          have h0_tmp : 0 < tmp1.length := by
            rw [hf.htmp_len]; have := hf.hle; have : (1#32).toNat = 1 := rfl; omega
          c0_hfast_nogrp
          exact ingest_assign_call_wp Γ hAssign hcs hvb0 hclr_sp hent0 hf hi0_j hj_hi hdrop
            hdcur ha_pres.2 ha_sp h0_tmp hm4 hQ
        · /- Loop 3 done, `new_cnt ≥ 2`: `full_add_clause` -/
          have hnc_ne0 : new_cnt ≠ 0#32 := by assumption
          have hnc_ne1 : new_cnt ≠ 1#32 := by assumption
          have hnc_ge2 : 2 ≤ new_cnt.toNat := by
            have h0 : new_cnt.toNat ≠ 0 := fun h => hnc_ne0 (BitVec.eq_of_toNat_eq h)
            have h1 : new_cnt.toNat ≠ 1 := fun h => hnc_ne1 (BitVec.eq_of_toNat_eq h)
            omega
          have hnc_le_mx : new_cnt.toNat ≤ c.max_vars := by
            have := hf.hle; have := hcs.hcnt_le; omega
          exact ingest_add_cl_call_wp Γ hAddCl hcs hvb0 hclr_sp hent0 hf hi0_j hj_hi hdrop
            hdcur hnc_ge2 hnc_le_mx ha_pres.2 ha_sp hm4 hQ
  · /- Entry of outer group = Loop 0 (`J_read (cnt, taut, ())`) -/
    intro J_after hJ_after
    refine wp_loop_group (ts := [i32, .bool])
      (IngestReadInv c accCnf F_cur s0 cnf_ptr cnfBytes i0 R) ?_ ?_
    · rintro J_read n ⟨cnt, taut, ⟨⟩⟩ m1 ih ⟨k, acc, s, hk_lo, hk_hi, rfl, hdcur, hpca, hcs, hm1⟩
      c0_hfast_nogrp
      · have hm1_d := fullMem_split_dimacs (fullMem_join_bytes hm1)
        refine wp_call_of_spec _ _
          (hNextLit _ _ _ _ ⟨cnf_ptr, BitVec.ofNat 64 c.nc, s.core.d_val, c.mv, cnfBytes, k, _,
            rfl, hptr_lt, by omega, hk_hi, hdcur ▸ hm1_d, ?_⟩)
        cases hn : nextLitPure c.mv (cnfBytes.drop k) with
        | err =>
          intro cur' val' m2 hm2
          have hm2' := fullMem_split_bytes (fullMem_join_dimacs hm2)
          have hcs1 := ingest_cs_upd_dcur hcs cur' val'
          c0_hfast_nogrp
          · refine hJ_after (cnt, taut, true, ()) m2 ?_
            simp only [IngestAfterReadInv, ↓reduceIte]
            exact ⟨by rw [← hpca, parseClauseAux_eq_nextLitPure, hn], _, hcs1.hlen, hcs.hfuel,
              hcs.hoom, hcs.hprob, hcs.hcnt_le, hm2'⟩
          all_goals exact absurd rfl (by assumption : ¬ (0#64 : BitVec 64) = 0#64)
        | endClause rest =>
          intro j m2 hkj hj_hi hdrop hm2
          have hm2' := fullMem_split_bytes (fullMem_join_dimacs hm2)
          have hcs1 := ingest_cs_upd_dcur hcs (cnf_ptr + BitVec.ofNat 64 j) 0#64
          c0_hfast_nogrp
          · cases (by assumption : (1#64 : BitVec 64) = 0#64)
          · refine hJ_after (cnt, taut, false, ()) m2 ?_
            simp only [IngestAfterReadInv, Bool.false_eq_true, ↓reduceIte]
            exact ⟨j, acc, rest, _, by omega, hj_hi, hdrop, rfl,
              by rw [← hpca, parseClauseAux_eq_nextLitPure, hn, List.map_reverse], hcs1, hm2'⟩
          all_goals exact absurd rfl (by assumption : ¬ (1#64 : BitVec 64) = 1#64)
        | lit l rest =>
          intro j m2 hl_lt hl_bd hkj hj_hi hdrop hm2
          have hm2' := fullMem_split_bytes (fullMem_join_dimacs hm2)
          let s1 : FullState :=
            { s with core := { s.core with d_cur := cnf_ptr + BitVec.ofNat 64 j,
                                           d_val := BitVec.ofNat 64 l } }
          have hcs1 := ingest_cs_upd_dcur hcs (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 l)
          have hev_lt : l / 2 < c.mv := by omega
          have ⟨_, _, _, hlit32_toNat, hev_toNat, hsw_ev⟩ :=
            ingest_tumble_bv_aux (n := 0) (by omega) hl_bd
          have hpca' : parseClauseAux (cnfBytes.length - j + 1) c.mv
              ((l :: acc).map kissatLitToDimacsLiteral) (cnfBytes.drop j) =
              parseClause c.mv (cnfBytes.drop i0) := by
            rw [← hpca, parseClauseAux_eq_nextLitPure (bs := cnfBytes.drop k), hn, ← hdrop,
              List.map_cons]
            exact parseClauseAux_fuel_irrel (by simp [List.length_drop])
              (by simp [List.length_drop]; omega)
          c0_hfast_nogrp
          · cases (by assumption : 2#64 = 0#64)
          · cases (by assumption : 2#64 = 1#64)
          · omega
          · /- `Js_2 (terr, ilit, ivar, ())` -/
            refine wp_join_group (ts := [.bool, i32, i32])
              (fun (terr, ilit, ivar, ()) m3 => terr = false ∧ ∃ s2 : FullState,
                s2.core.d_cur = cnf_ptr + BitVec.ofNat 64 j ∧
                IngestClauseState c accCnf F_cur s0 acc cnt taut s2 ∧
                (decide (c.mv < c.extend_cap) = true →
                  s2.core.frame_dec[l / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) ∧
                ilit.toNat = tumbleLit (decide (c.mv < c.extend_cap)) s2.core.frame_dec l ∧
                ivar.toNat = ilit.toNat / 2 ∧
                (FullMem c s2 ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m3) ?_ ?_
            · /- Body of `Js_2`: mark/dedup `mrk[ivar]` -/
              rintro _ ⟨terr, ilit, ivar, ⟨⟩⟩ m3 ⟨rfl, s2, hdcur2, hcs2, hl_map, hilit, hivar, hm3⟩
              have hilit_lt : ilit.toNat < 2 * c.mv := hilit ▸ tumbleLit_lt hcs2.htm hl_lt hl_map
              have hivar_mrk : ivar.toNat < s2.core.mrk.length := by
                rw [hcs2.hlen.core_ok.mrk_len]; omega
              c0_hfast_nogrp
              refine wp_join_group (ts := [i32, .bool, .bool])
                (fun (cnt', taut', _, ()) m4 => ∃ s3 : FullState,
                  s3.core.d_cur = cnf_ptr + BitVec.ofNat 64 j ∧
                  IngestClauseState c accCnf F_cur s0 (l :: acc) cnt' taut' s3 ∧
                  (FullMem c s3 ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m4)
                (fun _ ⟨cnt', taut', _, ⟨⟩⟩ m4 ⟨s3, hdcur3, hcs3, hm4⟩ => by
                  c0_hfast
                  exact ih (cnfBytes.length - j) (cnt', taut', ()) m4 (by omega)
                    ⟨j, l :: acc, s3, by omega, hj_hi, rfl, hdcur3, hpca', hcs3, hm4⟩)
                (fun Jm hJm => by
                  c0_hfast_nogrp
                  · have hunm : s2.core.mrk[ivar.toNat]?.getD 0#8 = 0#8 := by
                      rw [List.getElem?_eq_getElem hivar_mrk, Option.getD_some]
                      exact (ing_bv8_zext32_eq_iff _ 0#8).mp (by assumption)
                    have ⟨hcnt_lt, _⟩ := ingest_cs_mark_new hcs2 hl_lt hl_map hilit hivar hunm
                    omega
                  · have hunm : s2.core.mrk[ivar.toNat]?.getD 0#8 = 0#8 := by
                      rw [List.getElem?_eq_getElem hivar_mrk, Option.getD_some]
                      exact (ing_bv8_zext32_eq_iff _ 0#8).mp (by assumption)
                    obtain ⟨hcnt_lt, hcs3⟩ := ingest_cs_mark_new hcs2 hl_lt hl_map hilit hivar hunm
                    have hcnt_tmp : cnt.toNat < s2.core.tmp.length := by
                      rw [hcs2.hlen.core_ok.tmp_len_arr]; omega
                    have hsw_iv : (BitVec.setWidth 64 ivar).toNat = ivar.toNat := by
                      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := ivar.isLt; omega)]
                    have hsw_cnt : (BitVec.setWidth 64 cnt).toNat = cnt.toNat := by
                      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := cnt.isLt; omega)]
                    c0_hfast_nogrp
                    rw [hsw_iv, hsw_cnt] at *
                    let sm := BitVec.setWidth 8 ((ilit &&& 1#32) + 1#32)
                    exact hJm (cnt + 1#32, taut, false, ()) _
                      ⟨{ s2 with core := { s2.core with mrk := s2.core.mrk.set ivar.toNat sm,
                                                        tmp := s2.core.tmp.set cnt.toNat ilit } },
                       hdcur2, hcs3, by assumption⟩
                  · have hmk : s2.core.mrk[ivar.toNat]?.getD 0#8 ≠ 0#8 := by
                      rw [List.getElem?_eq_getElem hivar_mrk, Option.getD_some]
                      intro h
                      exact (by assumption : ¬ _ = _) ((ing_bv8_zext32_eq_iff _ 0#8).mpr h)
                    refine wp_join_group (ts := [.bool])
                      (fun (taut', ()) m4 => m4 = m3 ∧
                        taut' = if s2.core.mrk[ivar.toNat]?.getD 0#8 ≠
                          BitVec.setWidth 8 ((ilit &&& 1#32) + 1#32) then true else taut)
                      (fun _ ⟨taut', ⟨⟩⟩ m4 ⟨rfl, ht'⟩ => by
                        c0_hfast
                        exact hJm (cnt, taut', false, ()) m4
                          ⟨s2, hdcur2, ingest_cs_mark_dup hcs2 hl_lt hl_map hilit hivar hmk ht',
                           hm3⟩)
                      (fun Jt hJt => by
                        c0_hfast_nogrp
                        · have hne : s2.core.mrk[ivar.toNat]?.getD 0#8 ≠
                              BitVec.setWidth 8 ((ilit &&& 1#32) + 1#32) := by
                            rw [List.getElem?_eq_getElem hivar_mrk, Option.getD_some]
                            intro h
                            exact (by assumption : ¬ _ = _) ((ing_bv8_zext32_eq_iff _ _).mpr h)
                          exact hJt (true, ()) m3 ⟨rfl, by simp [hne]⟩
                        · have heq : s2.core.mrk[ivar.toNat]?.getD 0#8 =
                              BitVec.setWidth 8 ((ilit &&& 1#32) + 1#32) := by
                            rw [List.getElem?_eq_getElem hivar_mrk, Option.getD_some]
                            exact (ing_bv8_zext32_eq_iff _ _).mp (by assumption)
                          exact hJt (taut, ()) m3 ⟨rfl, by simp [heq]⟩))
            · /- Entry of `Js_2`: tumble lookup/allocation -/
              intro J2 hJ2
              c0_hfast_nogrp
              · /- `tum = true` -/
                have htum : decide (c.mv < c.extend_cap) = true := decide_eq_true (by omega)
                have hfd_l2 : l / 2 < s.core.frame_dec.length := by
                  rw [hcs1.hlen.core_ok.frame_dec_len]; omega
                have hev_fd : ((BitVec.setWidth 32 (BitVec.ofNat 64 l)) >>> (1 : Nat)).toNat <
                    s1.core.frame_dec.length := by rw [hev_toNat]; exact hfd_l2
                c0_hfast_nogrp
                refine wp_join_group (ts := [.bool, i32])
                  (fun (terr, ivar, ()) m3 => terr = false ∧ ∃ s2 : FullState,
                    s2.core.d_cur = cnf_ptr + BitVec.ofNat 64 j ∧
                    IngestClauseState c accCnf F_cur s0 acc cnt taut s2 ∧
                    s2.core.frame_dec[l / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 ∧
                    ivar = s2.core.frame_dec[l / 2]?.getD 0xFFFFFFFF#32 ∧
                    ivar.toNat < c.mv ∧
                    (FullMem c s2 ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m3)
                  (fun _ ⟨terr, ivar, ⟨⟩⟩ m3
                      ⟨hterr, s2, hdcur2, hcs2, hmap2, hivar_eq, hivar_lt, hm3⟩ => by
                    subst hterr; c0_hfast; dsimp only
                    have hilit_eq : ((ivar <<< (1 : Nat)) |||
                        (BitVec.setWidth 32 (BitVec.ofNat 64 l) &&& (1 : BitVec 32))).toNat =
                        tumbleLit (decide (c.mv < c.extend_cap)) s2.core.frame_dec l := by
                      change ((ivar <<< 1#32) |||
                        (BitVec.setWidth 32 (BitVec.ofNat 64 l) &&& 1#32)).toNat = _
                      rw [ing_bv32_shl1_or_and1 (by omega), hlit32_toNat, hivar_eq]
                      unfold tumbleLit tumblePi; simp [htum]
                    exact hJ2 (false, _, ivar, ()) m3 ⟨rfl, s2, hdcur2, hcs2, (fun _ => hmap2),
                      hilit_eq, (by
                        rw [hilit_eq]; unfold tumbleLit tumblePi; simp [htum, hivar_eq]; omega),
                      hm3⟩)
                  (fun J3 hJ3 => by
                    have hget_l2 : s.core.frame_dec[l / 2]'hfd_l2 =
                        s1.core.frame_dec[l / 2]?.getD 0xFFFFFFFF#32 := by
                      dsimp only [s1]; rw [List.getElem?_eq_getElem hfd_l2, Option.getD_some]
                    c0_hfast_nogrp
                    · have hun : s1.core.frame_dec[l / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 := by
                        rw [← hev_toNat, List.getElem?_eq_getElem hev_fd, Option.getD_some]
                        assumption
                      have ⟨hnext_lt, _⟩ := ingest_cs_tumble_map hcs1 htum hev_lt hun
                      dsimp only [s1] at hnext_lt; omega
                    · have hun : s1.core.frame_dec[l / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 := by
                        rw [← hev_toNat, List.getElem?_eq_getElem hev_fd, Option.getD_some]
                        assumption
                      obtain ⟨hnext_lt, hget_self, hne_ff, hcs2⟩ :=
                        ingest_cs_tumble_map hcs1 htum hev_lt hun
                      dsimp only [s1] at hnext_lt
                      have ⟨hto32, hsucc64, hto_nat, _, _, _⟩ :=
                        ingest_tumble_bv_aux (n := s.scratch.extend_len) (by omega) hl_bd
                      dsimp only [s1] at *
                      simp only [hsw_ev, hto32, hsucc64] at *
                      exact hJ3 (false, _, ()) _ ⟨rfl, _, rfl, hcs2, hne_ff,
                        hget_self.symm, (by rw [hto_nat]; exact hnext_lt), by assumption⟩
                    · have hmap1 : s1.core.frame_dec[l / 2]?.getD 0xFFFFFFFF#32 ≠
                          0xFFFFFFFF#32 := by
                        rw [← hev_toNat, List.getElem?_eq_getElem hev_fd, Option.getD_some]
                        assumption
                      have hlt_iv := ingest_tumble_mapped_lt (htum ▸ hcs1.htm) hev_lt hmap1
                      dsimp only; simp only [hsw_ev]
                      exact hJ3 (false, _, ()) m2 ⟨rfl, s1, rfl, hcs1, hmap1,
                        hget_l2, hget_l2 ▸ hlt_iv, hm2'⟩)
              · /- `tum = false` -/
                have htum : decide (c.mv < c.extend_cap) = false := decide_eq_false (by omega)
                dsimp only
                exact hJ2 (false, _, _, ()) m2
                  ⟨rfl, s1, rfl, hcs1, (fun h => by rw [htum] at h; cases h),
                   (by rw [hlit32_toNat, htum, tumbleLit_false]),
                   (by rw [hev_toNat, hlit32_toNat]), hm2'⟩
      · cases (by assumption : true = false)
    · /- Loop 0 entry (`jump J_read (0, false, ())`) -/
      intro J_read hJ_read
      c0_hfast
      exact hJ_read (cnfBytes.length - i0) (0#32, false, ()) m0
        (ingest_read_init hi0 hcv0 hdcur0 hcl0 htm0 hcov0 hsp0 hm0')

end LeanQbe.T.Examples.Kissat.Proof.Parse
