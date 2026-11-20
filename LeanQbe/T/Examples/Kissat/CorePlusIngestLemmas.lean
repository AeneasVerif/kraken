module

public import LeanQbe.T.Examples.Kissat.CorePlusIngestLemmas1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Soundness Proofs for Kissat `CorePlus` Syntax Skip, Clause Ingestion & Body Parsing (`Stage 2`)

Proves `Func.wp` specifications for:
1. `kissat_skip_clause_syntax` (`corePlusSkipClauseSyntaxSpec`, `kissat_skip_clause_syntax_wp`)
2. `kissat_ingest_clause` (`corePlusIngestClauseSpec`, `kissat_ingest_clause_wp`)
3. `kissat_parse_body` (`corePlusParseBodySpec`, `kissat_parse_body_wp`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.CorePlus

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test
open scoped IngestTactics

/-! ## 1. `kissat_skip_clause_syntax` -/

theorem kissat_skip_clause_syntax_wp (Γ : Env)
    (hLit : ∀ a m Q X, kissatNextLitSpec a m Q X →
      Γ "kissat_next_lit" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, corePlusSkipClauseSyntaxSpec a m Q X →
      Func.wp Γ kissat_skip_clause_syntax_body a m Q X := by
  rintro ⟨cend, d, ⟨⟩⟩ m Q X ⟨cnf_ptr, nc, val0, mv, cnfBytes, i0, R, rfl, hfit, hmv64, hi0, hm, hQ⟩
  unfold Func.wp kissat_skip_clause_syntax_body; wp_unfold
  refine wp_loop_group
    (fun r () ml => ∃ idx val_l revLits,
      i0 ≤ idx ∧ idx ≤ cnfBytes.length ∧ r = cnfBytes.length - idx ∧
      (∀ lit ∈ revLits, 1 ≤ lit.1) ∧
      parseClauseAux ((cnfBytes.drop idx).length + 1) mv revLits (cnfBytes.drop idx) =
        parseClause mv (cnfBytes.drop i0) ∧
      (bytes cnf_ptr cnfBytes ⋆
        dimacsState d (BitVec.ofNat 64 mv) nc (cnf_ptr + BitVec.ofNat 64 idx) val_l ⋆ R) ml)
    ?_ ?_
  · rintro L r ⟨⟩ ml ih ⟨idx, val_l, revLits, hi_le, hidx, rfl, hpos_acc, hpc_inv, hml⟩
    cp_steps
    · c0_call hLit
      refine ⟨cnf_ptr, nc, val_l, mv, cnfBytes, idx, R, rfl, hfit, hmv64, hidx, hml, ?_⟩
      cases hnl : nextLitPure mv (cnfBytes.drop idx) with
      | err =>
        intro cur' val' m' hm'; cp_steps
        · rw [← hpc_inv, parseClauseAux_eq_nextLitPure, hnl] at hQ; exact hQ cur' val' m' hm'
        · exact absurd rfl (by assumption : ¬(0#64 : BitVec 64) = 0)
      | endClause rest =>
        intro j m' hij hj hdrop hm'; cp_steps
        · rw [← hpc_inv, parseClauseAux_eq_nextLitPure, hnl] at hQ
          refine hQ j m' (fun lit hlit => ?_) (by omega) hj hdrop hm'
          simp only [CNF.Clause.literals_ofLiterals, List.mem_reverse] at hlit
          exact hpos_acc lit hlit
        · exact absurd rfl (by assumption : ¬(1#64 : BitVec 64) = 1)
      | lit l rest =>
        intro j m' _ _ hij hj hdrop hm'; cp_steps
        refine ih (cnfBytes.length - j) () m' (by omega)
          ⟨j, BitVec.ofNat 64 l, kissatLitToDimacsLiteral l :: revLits, by omega, hj, rfl,
            fun lit hlit => (List.mem_cons.mp hlit).elim
              (fun h => h ▸ by simp [kissatLitToDimacsLiteral]) (hpos_acc lit), ?_, hm'⟩
        have hstep :
            parseClauseAux ((cnfBytes.drop idx).length + 1) mv revLits (cnfBytes.drop idx) =
            parseClauseAux (cnfBytes.drop idx).length mv (kissatLitToDimacsLiteral l :: revLits)
              (cnfBytes.drop j) := by rw [parseClauseAux_eq_nextLitPure, hnl, ← hdrop]
        rw [← hpc_inv, hstep]; exact parseClauseAux_fuel_irrel (by simp) (by simp; omega)
    · cases (by assumption : true = false)
  · intro L hL; cp_steps
    exact hL (cnfBytes.length - i0) () m
      ⟨i0, val0, [], Nat.le_refl _, hi0, rfl, (fun _ h => by cases h), rfl, hm⟩

/-! ## 2. Pure and `CorePlusInv` Helpers for Clause Ingestion -/

private theorem cp_mem_to_dimacs {c : CorePlusCfg} {s : CorePlusState} {cnf_ptr : BitVec 64}
    {cnfBytes : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c s ⋆ R) m) :
    (bytes cnf_ptr cnfBytes ⋆
      dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.d_cur s.d_val ⋆
      (CorePlusRest c s ⋆ R)) m := by rw [corePlusMem_eq_dimacs_sep] at hm; exact sep_ac hm

private theorem cp_dimacs_to_mem {c : CorePlusCfg} {s : CorePlusState} {cnf_ptr dc' dv' : BitVec 64}
    {cnfBytes : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (bytes cnf_ptr cnfBytes ⋆
      dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) dc' dv' ⋆
      (CorePlusRest c s ⋆ R)) m) :
    (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c { s with d_cur := dc', d_val := dv' } ⋆ R) m := by
  rw [corePlusMem_eq_dimacs_sep, corePlusRest_d_irrel]; exact sep_ac hm

private theorem core_inv_d_mrk_tmp {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    (hcore : CorePlusCoreInv c F0 s) (dc dv : BitVec 64) {mrk' : List (BitVec 8)}
    {tmp' : List (BitVec 32)} (hm : mrk'.length = c.mv) (ht : tmp'.length = c.mv) :
    CorePlusCoreInv c F0 { s with d_cur := dc, d_val := dv, mrk := mrk', tmp := tmp' } :=
  ⟨{ hcore.lengths with mrk_len := hm, tmp_len_arr := ht },
    ⟨hcore.clauses.bounds, hcore.clauses.disjoint, hcore.clauses.lits_lt, hcore.clauses.entails⟩,
    hcore.cur_level_le, hcore.trail_lits_lt, hcore.trail_vars_nodup, hcore.vals_domain,
    hcore.vals_true_iff, hcore.vals_false_iff, hcore.lvl_le, hcore.trail_mono,
    hcore.levels_inhabited, hcore.level0_sound, hcore.reason_inv⟩

private theorem ingest_unit_rev {mv : Nat} {revLits : List Nat} {l : Nat} (_hl : l < 2 * mv)
    (hcleq : CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral) =
      CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l]) : revLits = [l] := by
  have hlits := congrArg CNF.Clause.literals hcleq
  simp only [CNF.Clause.literals_ofLiterals] at hlits
  cases hr : revLits.reverse with
  | nil => rw [hr] at hlits; simp at hlits
  | cons a rest_r =>
    rw [hr] at hlits
    cases rest_r with
    | nil =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hlits
      have ha : a = l := kissatLitToDimacsLiteral_inj hlits
      subst ha; simpa using congrArg List.reverse hr
    | cons _ _ => simp at hlits

private theorem ingest_F1_cl {c : CorePlusCfg} {accCnf : CNF Nat} {cl : CNF.Clause Nat}
    {st : CorePlusState} {tlen : Nat} {revLits : List Nat}
    (htlen_le : tlen ≤ c.mv) (htmpl : st.tmp.length = c.mv)
    (hcov : ∀ l ∈ revLits, ∃ k < tlen, (st.tmp[k]?.getD 0#32).toNat = l)
    (hcl_eq : cl = CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral)) :
    (shiftDownCnf (accCnf.add cl)).EntailsClause
      (cnfClause ((st.tmp.take tlen).map BitVec.toNat)) := by
  subst hcl_eq
  let cls := CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral)
  have h1 := shiftDownCnf_entails_added accCnf cls
  have hcl_ent : (shiftDownCnf (accCnf.add cls)).EntailsClause (cnfClause revLits.reverse) := by
    rwa [shiftDownClause_kissatLits revLits.reverse] at h1
  refine entails_of_mem_or_false hcl_ent fun l hl => Or.inl ?_
  obtain ⟨k, hk, hget⟩ := hcov l (List.mem_reverse.mp hl)
  refine List.mem_map.mpr ⟨st.tmp[k]'(by omega), ?_, ?_⟩
  · rw [List.mem_iff_getElem]; exact ⟨k, by rw [List.length_take]; omega, by rw [List.getElem_take]⟩
  · rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hget

private theorem ingest_F1_keep {c : CorePlusCfg} {accCnf : CNF Nat} {F1 : CNF Nat}
    {s : CorePlusState} {stTmp tmp' : List (BitVec 32)} {tlen keep : Nat} {cl : CNF.Clause Nat}
    (hF1 : F1 = shiftDownCnf (accCnf.add cl)) (hcore : CorePlusCoreInv c (shiftDownCnf accCnf) s)
    (hcl0 : s.cur_level = 0)
    (hk_le : keep ≤ tlen) (hs_tmpl : stTmp.length = c.mv) (ht_tmpl : tmp'.length = c.mv)
    (ht_le : tlen ≤ c.mv)
    (hF1_cl : F1.EntailsClause (cnfClause ((stTmp.take tlen).map BitVec.toNat)))
    (htmp_lt : ∀ k < tlen, (stTmp[k]?.getD 0#32).toNat < 2 * c.mv)
    (hpruned : ∀ k < tlen,
      (∃ j < keep, tmp'[j]? = stTmp[k]?) ∨ s.vals[(stTmp[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) :
    F1.EntailsClause (cnfClause ((tmp'.take keep).map BitVec.toNat)) := by
  refine entails_of_mem_or_false hF1_cl fun l hl => ?_
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hl; obtain ⟨k, hk, hxk⟩ := List.mem_iff_getElem.mp hx
  have hklt : k < tlen := by rw [List.length_take] at hk; omega
  rw [List.getElem_take] at hxk
  rcases hpruned k hklt with ⟨j, hj, hjeq⟩ | hfl
  · have htk : (tmp'.take keep)[j]? = some x := by
      rw [List.getElem?_take_of_lt hj, hjeq, List.getElem?_eq_getElem (by omega), hxk]
    rw [List.getElem?_eq_getElem (by rw [List.length_take]; omega)] at htk
    refine Or.inl (List.mem_map.mpr ⟨x, List.mem_iff_getElem.mpr
      ⟨j, by rw [List.length_take]; omega, Option.some.inj htk⟩, rfl⟩)
  · refine Or.inr ?_
    have hxk_get : (stTmp[k]?.getD 0#32).toNat = x.toNat := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hxk]
    rw [hxk_get] at hfl
    have hx_lt : x.toNat < 2 * c.mv := by have := htmp_lt k hklt; rwa [hxk_get] at this
    obtain ⟨ti, hti, htr_eq⟩ := (hcore.vals_false_iff x.toNat hx_lt).mp hfl
    have hlvl0 : (s.lvl[(s.trl[ti]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
      have := hcore.lvl_le ti hti; omega
    have hent0 := hcore.level0_sound ti hti hlvl0
    have hent_F1 : F1.EntailsClause (cnfClause [(s.trl[ti]?.getD 0#32).toNat]) := by
      rw [hF1]; exact CNF.entails_clause_trans (shiftDownCnf_entails_add accCnf cl) hent0
    rwa [htr_eq] at hent_F1

private structure IngestReadInv (c : CorePlusCfg) (s : CorePlusState) (nbytes i0 idx tlen : Nat)
    (taut : Bool) (revLits : List Nat) (st : CorePlusState) : Prop where
  idx_ge : i0 ≤ idx
  idx_le : idx ≤ nbytes
  tlen_le : tlen ≤ c.mv
  agree : st = { s with d_cur := st.d_cur, d_val := st.d_val, mrk := st.mrk, tmp := st.tmp }
  mrk_len : st.mrk.length = c.mv
  tmp_len : st.tmp.length = c.mv
  tmp_lt : ∀ k < tlen, (st.tmp[k]?.getD 0#32).toNat < 2 * c.mv
  tmp_nd : ∀ k1 k2, k1 < tlen → k2 < tlen →
    (st.tmp[k1]?.getD 0#32).toNat / 2 = (st.tmp[k2]?.getD 0#32).toNat / 2 → k1 = k2
  mrk_zero : ∀ v < c.mv,
    (∀ k < tlen, (st.tmp[k]?.getD 0#32).toNat / 2 ≠ v) → st.mrk[v]?.getD 0#8 = 0#8
  mrk_pos : ∀ k < tlen,
    st.mrk[(st.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#8 =
      BitVec.ofNat 8 ((st.tmp[k]?.getD 0#32).toNat % 2 + 1)
  cov : taut = false → ∀ l ∈ revLits, ∃ k < tlen, (st.tmp[k]?.getD 0#32).toNat = l
  sub_rev : ∀ k < tlen, (st.tmp[k]?.getD 0#32).toNat ∈ revLits
  nil_taut : revLits = [] → taut = false
  unit_r : ∀ l, revLits = [l] → taut = false ∧ tlen = 1 ∧ (st.tmp[0]?.getD 0#32).toNat = l

private theorem ingest_read_new_inv {c : CorePlusCfg} {s st : CorePlusState}
    {nbytes i0 j idx tlen l : Nat} {taut : Bool} {revLits : List Nat}
    (hri : IngestReadInv c s nbytes i0 idx tlen taut revLits st)
    (hij : idx < j) (hj : j ≤ nbytes) (hl_mv : l < 2 * c.mv) (hl32 : l < 2 ^ 32)
    (hmiss_v : ∀ k < tlen, (st.tmp[k]?.getD 0#32).toNat / 2 ≠ l / 2)
    (htlen_lt : tlen < c.mv) (dc' dv' : BitVec 64) :
    IngestReadInv c s nbytes i0 j (tlen + 1) taut (l :: revLits)
      { st with
        d_cur := dc', d_val := dv',
        mrk := st.mrk.set (l / 2) (BitVec.ofNat 8 (l % 2 + 1)),
        tmp := st.tmp.set tlen (BitVec.ofNat 32 l) } := by
  let st' : CorePlusState := { st with
    d_cur := dc', d_val := dv',
    mrk := st.mrk.set (l / 2) (BitVec.ofNat 8 (l % 2 + 1)),
    tmp := st.tmp.set tlen (BitVec.ofNat 32 l) }
  have hmkl := hri.mrk_len; have htmpl := hri.tmp_len
  refine ⟨by have := hri.idx_ge; omega, hj, by omega,
    congrArg (fun x => { x with
      d_cur := dc', d_val := dv', mrk := st'.mrk, tmp := st'.tmp }) hri.agree,
    by simp [hmkl], by simp [htmpl], ?_, ?_, ?_, ?_, ?_, ?_, (fun hc => by cases hc), ?_⟩
  · intro k hk; dsimp only [st']
    by_cases hkt : k = tlen
    · subst k; rw [List.getElem?_set_self (by omega), Option.getD_some, bv32_ofNat_toNat hl32]
      exact hl_mv
    · rw [List.getElem?_set_ne (Ne.symm hkt)]; exact hri.tmp_lt k (by omega)
  · intro k1 k2 h1 h2 heq; dsimp only [st'] at heq
    by_cases hk1 : k1 = tlen <;> by_cases hk2 : k2 = tlen
    · omega
    · subst hk1
      rw [List.getElem?_set_self (by omega), Option.getD_some, bv32_ofNat_toNat hl32,
        List.getElem?_set_ne (Ne.symm hk2)] at heq
      exact absurd heq.symm (hmiss_v k2 (by omega))
    · subst hk2
      rw [List.getElem?_set_self (by omega), Option.getD_some, bv32_ofNat_toNat hl32,
        List.getElem?_set_ne (Ne.symm hk1)] at heq
      exact absurd heq (hmiss_v k1 (by omega))
    · rw [List.getElem?_set_ne (Ne.symm hk1), List.getElem?_set_ne (Ne.symm hk2)] at heq
      exact hri.tmp_nd k1 k2 (by omega) (by omega) heq
  · intro v hv hmiss; dsimp only [st']
    have hne : v ≠ l / 2 := by
      have h := hmiss tlen (by omega); dsimp only [st'] at h
      rw [List.getElem?_set_self (by omega), Option.getD_some, bv32_ofNat_toNat hl32] at h
      exact Ne.symm h
    rw [List.getElem?_set_ne (Ne.symm hne)]
    refine hri.mrk_zero v hv fun k hk => ?_
    have h := hmiss k (by omega); dsimp only [st'] at h; rwa [List.getElem?_set_ne (by omega)] at h
  · intro k hk; dsimp only [st']
    by_cases hkt : k = tlen
    · subst k
      rw [List.getElem?_set_self (by omega), Option.getD_some, bv32_ofNat_toNat hl32,
        List.getElem?_set_self (by omega)]; rfl
    · rw [List.getElem?_set_ne (Ne.symm hkt),
        List.getElem?_set_ne (Ne.symm (hmiss_v k (by omega)))]
      exact hri.mrk_pos k (by omega)
  · intro hnt x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · refine ⟨tlen, by omega, ?_⟩; dsimp only [st']
      rw [List.getElem?_set_self (by omega), Option.getD_some, bv32_ofNat_toNat hl32]
    · obtain ⟨k, hk, hget⟩ := hri.cov hnt x hx'
      refine ⟨k, by omega, ?_⟩; dsimp only [st']; rwa [List.getElem?_set_ne (by omega)]
  · intro k hk; dsimp only [st']
    by_cases hkt : k = tlen
    · subst k; rw [List.getElem?_set_self (by omega), Option.getD_some, bv32_ofNat_toNat hl32]
      exact List.mem_cons_self
    · rw [List.getElem?_set_ne (Ne.symm hkt)]
      exact List.mem_cons_of_mem _ (hri.sub_rev k (by omega))
  · intro l' hl'; rcases List.cons.inj hl' with ⟨rfl, rfl⟩
    have ht0 : tlen = 0 := by
      cases tlen with
      | zero => rfl
      | succ k => exact absurd (hri.sub_rev 0 (by omega)) (by simp)
    subst ht0; refine ⟨hri.nil_taut rfl, rfl, ?_⟩; dsimp only [st']
    rw [List.getElem?_set_self (by omega), Option.getD_some, bv32_ofNat_toNat hl32]

private theorem ingest_read_dup_inv {c : CorePlusCfg} {s st : CorePlusState}
    {nbytes i0 j idx tlen l k0 : Nat} {taut : Bool} {revLits : List Nat}
    (hri : IngestReadInv c s nbytes i0 idx tlen taut revLits st)
    (hij : idx < j) (hj : j ≤ nbytes) (hk0 : k0 < tlen) (hl_mv : l < 2 * c.mv)
    (hk0_v : (st.tmp[k0]?.getD 0#32).toNat / 2 = l / 2) (dc' dv' : BitVec 64) :
    let mv_b := st.mrk[l / 2]'(by rw [hri.mrk_len]; omega)
    let taut' := if mv_b = BitVec.ofNat 8 (l % 2 + 1) then taut else true
    IngestReadInv c s nbytes i0 j tlen taut' (l :: revLits)
      { st with d_cur := dc', d_val := dv' } := by
  intro mv_b taut'
  have hmv_pos := hri.mrk_pos k0 hk0
  rw [hk0_v, List.getElem?_eq_getElem (by rw [hri.mrk_len]; omega), Option.getD_some] at hmv_pos
  refine ⟨by have := hri.idx_ge; omega, hj, hri.tlen_le,
    congrArg (fun x => { x with d_cur := dc', d_val := dv' }) hri.agree,
    hri.mrk_len, hri.tmp_len, hri.tmp_lt, hri.tmp_nd, hri.mrk_zero, hri.mrk_pos, ?_,
    (fun k hk => List.mem_cons_of_mem _ (hri.sub_rev k hk)), (fun hc => by cases hc), ?_⟩
  · intro hnt' x hx
    by_cases hmeq : mv_b = BitVec.ofNat 8 (l % 2 + 1)
    · simp only [taut', hmeq, ↓reduceIte] at hnt'
      rcases List.mem_cons.mp hx with rfl | hx'
      · refine ⟨k0, hk0, ?_⟩
        dsimp only
        have hmeq' : st.mrk[x / 2]'(by rw [hri.mrk_len]; omega) = BitVec.ofNat 8 (x % 2 + 1) :=
          hmeq
        rw [hmv_pos] at hmeq'
        have hmod := congrArg BitVec.toNat hmeq'
        have hlt1 : (st.tmp[k0]?.getD 0#32).toNat % 2 + 1 < 256 := by omega
        have hlt2 : x % 2 + 1 < 256 := by omega
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hmod
        omega
      · exact hri.cov hnt' x hx'
    · simp only [taut', hmeq, ↓reduceIte] at hnt'; cases hnt'
  · intro l' hl'; rcases List.cons.inj hl' with ⟨_, rfl⟩
    exact absurd (hri.sub_rev k0 hk0) (by simp)

private theorem ingest_tlen_lt_of_zero {c : CorePlusCfg} {s st : CorePlusState}
    {nbytes i0 idx tlen l : Nat} {taut : Bool} {revLits : List Nat}
    (hri : IngestReadInv c s nbytes i0 idx tlen taut revLits st) (hl_mv : l < 2 * c.mv)
    (hm0 : st.mrk[l / 2]'(by rw [hri.mrk_len]; omega) = 0#8) :
    (∀ k < tlen, (st.tmp[k]?.getD 0#32).toNat / 2 ≠ l / 2) ∧ tlen < c.mv := by
  have hmiss : ∀ k < tlen, (st.tmp[k]?.getD 0#32).toNat / 2 ≠ l / 2 := by
    intro k hk heq
    have hpos := hri.mrk_pos k hk
    rw [heq, List.getElem?_eq_getElem (by rw [hri.mrk_len]; omega), Option.getD_some, hm0] at hpos
    have h1 := congrArg BitVec.toNat hpos; simp only [BitVec.toNat_ofNat] at h1; omega
  exact ⟨hmiss, inj_lt_of_missing (fun k => (st.tmp[k]?.getD 0#32).toNat / 2) hri.tmp_nd
    (fun k hk => by have := hri.tmp_lt k hk; omega) (by omega) hmiss⟩

private theorem ingest_exists_var_of_nz {c : CorePlusCfg} {s st : CorePlusState}
    {nbytes i0 idx tlen l : Nat} {taut : Bool} {revLits : List Nat}
    (hri : IngestReadInv c s nbytes i0 idx tlen taut revLits st) (hl_mv : l < 2 * c.mv)
    (hmne0 : st.mrk[l / 2]'(by rw [hri.mrk_len]; omega) ≠ 0#8) :
    ∃ k0 < tlen, (st.tmp[k0]?.getD 0#32).toNat / 2 = l / 2 := by
  by_cases h : ∃ k0 < tlen, (st.tmp[k0]?.getD 0#32).toNat / 2 = l / 2
  · exact h
  · exfalso; have h0 := hri.mrk_zero (l / 2) (by omega) fun k hk heq => h ⟨k, hk, heq⟩
    rw [List.getElem?_eq_getElem (by rw [hri.mrk_len]; omega), Option.getD_some] at h0
    exact hmne0 h0

private structure IngestPruneInv (c : CorePlusCfg) (s : CorePlusState)
    (tlen keep i : Nat) (revLits : List Nat) (stTmp tmp' : List (BitVec 32)) : Prop where
  keep_le : keep ≤ i
  i_le : i ≤ tlen
  tmp_len : tmp'.length = c.mv
  tail_eq : ∀ k, i ≤ k → k < tlen → tmp'[k]? = stTmp[k]?
  keep_un : ∀ k < keep, (tmp'[k]?.getD 0#32).toNat < 2 * c.mv ∧
    s.vals[(tmp'[k]?.getD 0#32).toNat]?.getD 0#8 = 0#8
  pruned : ∀ k < i,
    (∃ j < keep, tmp'[j]? = stTmp[k]?) ∨ s.vals[(stTmp[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8
  unit0 : ∀ l < 2 * c.mv, revLits = [l] → s.vals[l]?.getD 0#8 = 0#8 →
    i = 1 → keep = 1 ∧ (tmp'[0]?.getD 0#32).toNat = l
  unit1 : ∀ l < 2 * c.mv, revLits = [l] → s.vals[l]?.getD 0#8 = 0xFF#8 → i = 1 → keep = 0

private theorem ingest_prune_push_inv {c : CorePlusCfg} {s : CorePlusState}
    {tlen keep i : Nat} {revLits : List Nat} {stTmp tmp' : List (BitVec 32)}
    (hp : IngestPruneInv c s tlen keep i revLits stTmp tmp') (hi : i < tlen)
    (ht_le : tlen ≤ c.mv) (hs_tl : stTmp.length = c.mv)
    (hunit_r : ∀ l, revLits = [l] → tlen = 1 ∧ (stTmp[0]?.getD 0#32).toNat = l)
    {li : BitVec 32} (hli_eq : li = stTmp[i]'(by rw [hs_tl]; omega))
    (hli_lt : li.toNat < 2 * c.mv) (hlv0 : s.vals[li.toNat]?.getD 0#8 = 0#8) :
    IngestPruneInv c s tlen (keep + 1) (i + 1) revLits stTmp (tmp'.set keep li) := by
  have hk_lt : keep < tmp'.length := by rw [hp.tmp_len]; have := hp.keep_le; have := hp.i_le; omega
  refine ⟨by have := hp.keep_le; omega, by omega, by simp [hp.tmp_len], ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk1 hk2; rw [List.getElem?_set_ne (by have := hp.keep_le; omega)]
    exact hp.tail_eq k (by omega) hk2
  · intro k hk; by_cases hkk : k = keep
    · subst k; rw [List.getElem?_set_self hk_lt, Option.getD_some]; exact ⟨hli_lt, hlv0⟩
    · rw [List.getElem?_set_ne (Ne.symm hkk)]; exact hp.keep_un k (by omega)
  · intro k hk; by_cases hki : k = i
    · subst k; refine Or.inl ⟨keep, by omega, ?_⟩
      rw [List.getElem?_set_self hk_lt, List.getElem?_eq_getElem (by rw [hs_tl]; omega), hli_eq]
    · rcases hp.pruned k (by omega) with ⟨j, hj, hjeq⟩ | hfl
      · exact Or.inl ⟨j, by omega,
          by rw [List.getElem?_set_ne (by have := hp.keep_le; omega)]; exact hjeq⟩
      · exact Or.inr hfl
  · intro l hl hrev hv0 hi1
    have hi0 : i = 0 := by omega
    have hk0 : keep = 0 := by have := hp.keep_le; omega
    subst hi0 hk0; obtain ⟨_, htmp0⟩ := hunit_r l hrev
    refine ⟨rfl, ?_⟩; rw [List.getElem?_set_self hk_lt, Option.getD_some, hli_eq]
    rwa [List.getElem?_eq_getElem (by rw [hs_tl]; omega), Option.getD_some] at htmp0
  · intro l hl hrev hvf hi1
    have hi0 : i = 0 := by omega
    subst hi0; obtain ⟨_, htmp0⟩ := hunit_r l hrev
    have hli_l : li.toNat = l := by
      rw [hli_eq]; rwa [List.getElem?_eq_getElem (by rw [hs_tl]; omega), Option.getD_some] at htmp0
    rw [hli_l] at hlv0; rw [hlv0] at hvf; cases hvf

private theorem ingest_prune_skip_inv {c : CorePlusCfg} {s : CorePlusState}
    {tlen keep i : Nat} {revLits : List Nat} {stTmp tmp' : List (BitVec 32)}
    (hp : IngestPruneInv c s tlen keep i revLits stTmp tmp') (hi : i < tlen)
    (ht_le : tlen ≤ c.mv) (hs_tl : stTmp.length = c.mv)
    (hunit_r : ∀ l, revLits = [l] → tlen = 1 ∧ (stTmp[0]?.getD 0#32).toNat = l)
    {li : BitVec 32} (hli_eq : li = stTmp[i]'(by rw [hs_tl]; omega))
    (hlv_ff : s.vals[li.toNat]?.getD 0#8 = 0xFF#8) :
    IngestPruneInv c s tlen keep (i + 1) revLits stTmp tmp' := by
  refine ⟨by have := hp.keep_le; omega, by omega, hp.tmp_len,
    fun k hk1 hk2 => hp.tail_eq k (by omega) hk2, hp.keep_un, ?_, ?_, ?_⟩
  · intro k hk; by_cases hki : k = i
    · subst k; refine Or.inr ?_
      have hget : stTmp[i]? = some li := by
        rw [List.getElem?_eq_getElem (by rw [hs_tl]; omega), hli_eq]
      rwa [hget, Option.getD_some]
    · exact hp.pruned k (by omega)
  · intro l hl hrev hv0 hi1
    have hi0 : i = 0 := by omega
    subst hi0; obtain ⟨_, htmp0⟩ := hunit_r l hrev
    have hli_l : li.toNat = l := by
      rw [hli_eq]; rwa [List.getElem?_eq_getElem (by rw [hs_tl]; omega), Option.getD_some] at htmp0
    rw [hli_l] at hlv_ff; rw [hlv_ff] at hv0; cases hv0
  · intro l hl hrev hvf hi1; have := hp.keep_le; omega

private abbrev IngestClausePost (c : CorePlusCfg) (accCnf : CNF Nat) (s : CorePlusState)
    (cnf_ptr : BitVec 64) (cnfBytes : List UInt8) (i0 : Nat) (R : Mem 64 → Prop)
    (Q : Post [i64]) (cl : CNF.Clause Nat) (rest : List UInt8) : Prop :=
  ∀ r s' j m',
    (∀ lit ∈ cl.literals, 1 ≤ lit.1) → i0 < j → j ≤ cnfBytes.length → cnfBytes.drop j = rest →
    s'.LengthsOk c → s'.d_cur = cnf_ptr + BitVec.ofNat 64 j → s'.cur_level = 0 →
    s'.fuel = s.fuel → s'.heur.rel_trigger = s.heur.rel_trigger →
    (r = 1#64 ∨ r = 2#64 ∨ r = 3#64) →
    (r = 1#64 → CorePlusInv c (shiftDownCnf (accCnf.add cl)) s') →
    (r = 2#64 → (shiftDownCnf (accCnf.add cl)).Unsat) →
    (∀ l < 2 * c.mv, cl = CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l] →
      s.vals[l]?.getD 0#8 = 0#8 →
      r = 1#64 ∧ s'.vals = (s.vals.set l 1#8).set (l ^^^ 1) 0xFF#8 ∧
      s'.trail_end = s.trail_end + 1 ∧ s'.propagated = s.propagated ∧
      s'.num_clauses = s.num_clauses ∧ s'.wh = s.wh) →
    (∀ l < 2 * c.mv, cl = CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l] →
      s.vals[l]?.getD 0#8 = 0xFF#8 → r = 2#64) →
    (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c s' ⋆ R) m' → Q (r, ()) m'

private theorem ingest_lv_pos_exit {c : CorePlusCfg} {accCnf : CNF Nat}
    {s st st3 : CorePlusState} {cnf_ptr : BitVec 64} {cnfBytes : List UInt8}
    {i0 idx tlen i : Nat} {revLits : List Nat} {mrk' : List (BitVec 8)} {tmp' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m3 : Mem 64} {Q : Post [i64]}
    (hcore : CorePlusCoreInv c (shiftDownCnf accCnf) s)
    (hmc : MarksClear c { st with mrk := mrk' })
    (hri : IngestReadInv c s cnfBytes.length i0 idx tlen false revLits st)
    (hi0_lt : i0 < idx) (hdcur_st : st.d_cur = cnf_ptr + BitVec.ofNat 64 idx)
    (hcl0 : s.cur_level = 0) (hmkl : mrk'.length = c.mv) (htl : tmp'.length = c.mv)
    (hs3 : st3 = { s with d_cur := st.d_cur, d_val := st.d_val, mrk := mrk', tmp := tmp' })
    (hi_lt : i < tlen) (hli_eq : tmp'[i]'(by rw [htl]; have := hri.tlen_le; omega) =
      st.tmp[i]'(by rw [hri.tmp_len]; have := hri.tlen_le; omega))
    (_hli_lt : (tmp'[i]'(by rw [htl]; have := hri.tlen_le; omega)).toNat < 2 * c.mv)
    (hlv1 : s.vals[(tmp'[i]'(by rw [htl]; have := hri.tlen_le; omega)).toNat]?.getD 0#8 = 1#8)
    (hm3 : (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c st3 ⋆ R) m3)
    (hQ : IngestClausePost c accCnf s cnf_ptr cnfBytes i0 R Q
      (CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral))
      (cnfBytes.drop idx)) : Q (1#64, ()) m3 := by
  have hcl_pos : ∀ lit ∈ (CNF.Clause.ofLiterals
      (revLits.reverse.map kissatLitToDimacsLiteral)).literals, 1 ≤ lit.1 := fun lit hlit => by
    simp only [CNF.Clause.literals_ofLiterals, List.mem_map] at hlit
    rcases hlit with ⟨l, _, rfl⟩; simp [kissatLitToDimacsLiteral]
  have hcore3 : CorePlusCoreInv c (shiftDownCnf accCnf) st3 := by
    rw [hs3]; exact core_inv_d_mrk_tmp hcore st.d_cur st.d_val hmkl htl
  have hmc3 : MarksClear c st3 := fun v hv => by rw [hs3]; simpa using hmc v hv
  have hst_i : (st.tmp[i]'(by rw [hri.tmp_len]; have := hri.tlen_le; omega)).toNat =
      (st.tmp[i]?.getD 0#32).toNat := by
    rw [List.getElem?_eq_getElem (by rw [hri.tmp_len]; have := hri.tlen_le; omega),
      Option.getD_some]
  have hli_l : ∀ l, revLits = [l] →
      (tmp'[i]'(by rw [htl]; have := hri.tlen_le; omega)).toNat = l := fun l hr => by
    obtain ⟨_, ht1, htmp0⟩ := hri.unit_r l hr
    have hi0_e : i = 0 := by omega
    rw [hli_eq, hst_i, hi0_e, htmp0]
  exact hQ 1#64 st3 idx m3 hcl_pos hi0_lt hri.idx_le rfl hcore3.lengths
    (by rw [hs3]; exact hdcur_st) (by rw [hs3]; exact hcl0) (by rw [hs3]) (by rw [hs3])
    (Or.inl rfl) (fun _ => ⟨hcore3.mono (shiftDownCnf_entails_add _ _), hmc3⟩)
    (fun h => by cases h)
    (fun l hl hcleq hv0 => by rw [hli_l l (ingest_unit_rev hl hcleq)] at hlv1; cases hlv1 ▸ hv0)
    (fun l hl hcleq hvf => by rw [hli_l l (ingest_unit_rev hl hcleq)] at hlv1; cases hlv1 ▸ hvf)
    hm3

private theorem ingest_addcl_post {c : CorePlusCfg} {accCnf : CNF Nat} {s st3 : CorePlusState}
    {cnf_ptr : BitVec 64} {cnfBytes : List UInt8} {i0 idx tlen keep : Nat} {revLits : List Nat}
    {lpool' cls' wh' wn' : List (BitVec 32)} {R : Mem 64 → Prop} {m4 : Mem 64} {Q : Post [i64]}
    (hinv3 : CorePlusInv c (shiftDownCnf (accCnf.add
      (CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral)))) st3)
    (hm3_eq : st3.d_cur = cnf_ptr + BitVec.ofNat 64 idx ∧ st3.cur_level = 0 ∧
      st3.fuel = s.fuel ∧ st3.heur.rel_trigger = s.heur.rel_trigger)
    (hkp_ge2 : 2 ≤ keep) (hkp_le : keep ≤ tlen) (ht_le : tlen ≤ c.mv)
    (hkp_un : ∀ k < keep, (st3.tmp[k]?.getD 0#32).toNat < 2 * c.mv)
    (hF1_keep : (shiftDownCnf (accCnf.add
      (CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral)))).EntailsClause
      (cnfClause ((st3.tmp.take keep).map BitVec.toNat)))
    (hunit_r : ∀ l, revLits = [l] → tlen = 1 ∧ (st3.tmp[0]?.getD 0#32).toNat = l)
    (hu0 : ∀ l < 2 * c.mv, revLits = [l] → s.vals[l]?.getD 0#8 = 0#8 →
      tlen = 1 → keep = 1 ∧ (st3.tmp[0]?.getD 0#32).toNat = l)
    (hu1 : ∀ l < 2 * c.mv, revLits = [l] → s.vals[l]?.getD 0#8 = 0xFF#8 → tlen = 1 → keep = 0)
    (hi0_lt : i0 < idx) (hidx_le : idx ≤ cnfBytes.length)
    (hlen_sf : (addClauseState st3 keep lpool' cls' wh' wn').LengthsOk c)
    (hmeta : ∀ cid < st3.num_clauses,
      clauseOff (addClauseState st3 keep lpool' cls' wh' wn') cid = clauseOff st3 cid ∧
      clauseSize (addClauseState st3 keep lpool' cls' wh' wn') cid = clauseSize st3 cid)
    (hlp_pre : ∀ k < st3.lit_len, lpool'[k]? = st3.lpool[k]?)
    (hoff : clauseOff (addClauseState st3 keep lpool' cls' wh' wn') st3.num_clauses = st3.lit_len)
    (hsz : clauseSize (addClauseState st3 keep lpool' cls' wh' wn') st3.num_clauses = keep)
    (hlits : clauseLits (addClauseState st3 keep lpool' cls' wh' wn') st3.num_clauses =
      (st3.tmp.take keep).map BitVec.toNat)
    (hm4 : (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c
      (addClauseState st3 keep lpool' cls' wh' wn') ⋆ R) m4)
    (hQ : IngestClausePost c accCnf s cnf_ptr cnfBytes i0 R Q
      (CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral))
      (cnfBytes.drop idx)) : Q (1#64, ()) m4 := by
  have hcl_pos : ∀ lit ∈ (CNF.Clause.ofLiterals
      (revLits.reverse.map kissatLitToDimacsLiteral)).literals, 1 ≤ lit.1 := fun lit hlit => by
    simp only [CNF.Clause.literals_ofLiterals, List.mem_map] at hlit
    rcases hlit with ⟨l, _, rfl⟩; simp [kissatLitToDimacsLiteral]
  have hlits_lt : ∀ l ∈ (st3.tmp.take keep).map BitVec.toNat, l < 2 * c.mv := by
    intro l hl; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hl
    obtain ⟨k, hk, hxk⟩ := List.mem_iff_getElem.mp hx
    rw [List.length_take] at hk; rw [List.getElem_take] at hxk
    have hlt := hkp_un k (by omega)
    rwa [List.getElem?_eq_getElem (by rw [hinv3.core.lengths.tmp_len_arr]; omega),
      Option.getD_some, hxk] at hlt
  have hsf_core := addClause_preserves_core hinv3.core hlen_sf hkp_ge2 hlits_lt hF1_keep
    hmeta hlp_pre hoff hsz hlits
  exact hQ 1#64 _ idx m4 hcl_pos hi0_lt hidx_le rfl hlen_sf hm3_eq.1 hm3_eq.2.1 hm3_eq.2.2.1
    hm3_eq.2.2.2 (Or.inl rfl) (fun _ => ⟨hsf_core, hinv3.marks⟩) (fun h => by cases h)
    (fun l hl hcleq hv0 => by
      have hr := ingest_unit_rev hl hcleq; have h1 := (hu0 l hl hr hv0 (hunit_r l hr).1).1; omega)
    (fun l hl hcleq hvf => by
      have hr := ingest_unit_rev hl hcleq; have := hu1 l hl hr hvf (hunit_r l hr).1; omega) hm4

private theorem ingest_assign_post {c : CorePlusCfg} {accCnf : CNF Nat} {s st3 : CorePlusState}
    {cnf_ptr : BitVec 64} {cnfBytes : List UInt8} {i0 idx tlen : Nat} {revLits : List Nat}
    {l0 : BitVec 32} {phases' : List (BitVec 8)} {R : Mem 64 → Prop} {m4 : Mem 64} {Q : Post [i64]}
    (hinv3 : CorePlusInv c (shiftDownCnf (accCnf.add
      (CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral)))) st3)
    (hag3 : st3.d_cur = cnf_ptr + BitVec.ofNat 64 idx ∧ st3.cur_level = 0 ∧
      st3.fuel = s.fuel ∧ st3.heur.rel_trigger = s.heur.rel_trigger ∧
      st3.vals = s.vals ∧ st3.trail_end = s.trail_end ∧ st3.propagated = s.propagated ∧
      st3.num_clauses = s.num_clauses ∧ st3.wh = s.wh)
    (hl0_lt : l0.toNat < 2 * c.mv) (hph4 : phases'.length = c.mv)
    (hl0_un : st3.vals[l0.toNat]?.getD 0#8 = 0#8)
    (hl0_ent : (shiftDownCnf (accCnf.add
      (CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral)))).EntailsClause
      (cnfClause [l0.toNat]))
    (hunit_r : ∀ l, revLits = [l] → tlen = 1)
    (hu0 : ∀ l < 2 * c.mv, revLits = [l] → s.vals[l]?.getD 0#8 = 0#8 →
      tlen = 1 → 1 = 1 ∧ l0.toNat = l)
    (hu1 : ∀ l < 2 * c.mv, revLits = [l] → s.vals[l]?.getD 0#8 = 0xFF#8 → tlen = 1 → 1 = 0)
    (hi0_lt : i0 < idx) (hidx_le : idx ≤ cnfBytes.length)
    (hlen4 : ({ st3 with
      vals := (st3.vals.set l0.toNat 1#8).set (l0.toNat ^^^ 1) 0xFF#8,
      lvl := st3.lvl.set (l0.toNat / 2) (BitVec.ofNat 32 st3.cur_level),
      rsns := st3.rsns.set (l0.toNat / 2) 0xFFFFFFFF#32, trl := st3.trl.set st3.trail_end l0,
      trail_end := st3.trail_end + 1, heur := { st3.heur with phases := phases' } } :
      CorePlusState).LengthsOk c)
    (hm4 : (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c { st3 with
      vals := (st3.vals.set l0.toNat 1#8).set (l0.toNat ^^^ 1) 0xFF#8,
      lvl := st3.lvl.set (l0.toNat / 2) (BitVec.ofNat 32 st3.cur_level),
      rsns := st3.rsns.set (l0.toNat / 2) 0xFFFFFFFF#32, trl := st3.trl.set st3.trail_end l0,
      trail_end := st3.trail_end + 1, heur := { st3.heur with phases := phases' } } ⋆ R) m4)
    (hQ : IngestClausePost c accCnf s cnf_ptr cnfBytes i0 R Q
      (CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral))
      (cnfBytes.drop idx)) : Q (1#64, ()) m4 := by
  have hcl_pos : ∀ lit ∈ (CNF.Clause.ofLiterals
      (revLits.reverse.map kissatLitToDimacsLiteral)).literals, 1 ≤ lit.1 := fun lit hlit => by
    simp only [CNF.Clause.literals_ofLiterals, List.mem_map] at hlit
    rcases hlit with ⟨l, _, rfl⟩; simp [kissatLitToDimacsLiteral]
  have hsf_core := assign_preserves_core hinv3.core hl0_lt hph4 hl0_un
    (by rw [hag3.2.1]; omega) (fun _ h1 h2 => by rw [hag3.2.1] at h2; omega)
    (fun _ => hl0_ent) (fun hc => absurd rfl hc)
  exact hQ 1#64 _ idx m4 hcl_pos hi0_lt hidx_le rfl hlen4 hag3.1 hag3.2.1 hag3.2.2.1
    hag3.2.2.2.1 (Or.inl rfl) (fun _ => ⟨hsf_core, hinv3.marks⟩) (fun h => by cases h)
    (fun l hl hcleq hv0 => by
      have hr := ingest_unit_rev hl hcleq; have ⟨_, hl0eq⟩ := hu0 l hl hr hv0 (hunit_r l hr)
      exact ⟨rfl, by rw [hag3.2.2.2.2.1, hl0eq], by rw [hag3.2.2.2.2.2.1],
        hag3.2.2.2.2.2.2.1, hag3.2.2.2.2.2.2.2.1, hag3.2.2.2.2.2.2.2.2⟩)
    (fun l hl hcleq hvf => by
      have hr := ingest_unit_rev hl hcleq; have := hu1 l hl hr hvf (hunit_r l hr); omega) hm4

/-! ## 3. `kissat_ingest_clause_wp` -/

private theorem bv8_setWidth32_eq_iff (a b : BitVec 8) :
    a.setWidth 32 = b.setWidth 32 ↔ a = b := by
  constructor
  · intro h; apply BitVec.eq_of_toNat_eq; have ht := congrArg BitVec.toNat h
    have ha := a.isLt; have hb := b.isLt; simp only [BitVec.toNat_setWidth] at ht; omega
  · rintro rfl; rfl

private def ingestPruneExpr (hdr pTmp pVals : Val i64) (tlen_v : Val i32) :
    Expr Val Cont [i64] :=
  Expr.group (sig := [[i32, i32]]) (fun Js => Blocks.cons (fun p_7 =>
    Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool (by decide),
                args := (Arg.var p_7.snd.fst, Arg.var tlen_v, ()) } fun p_8 =>
    Expr.jnz (Arg.var p_8.fst)
      (Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                   args := (Arg.var p_7.snd.fst, ()) } fun p =>
       Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                   args := (Arg.var p.fst, Arg.imm 4, ()) } fun p =>
       Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                   args := (Arg.var pTmp, Arg.var p.fst, ()) } fun p =>
       Expr.load i32 (Arg.var p.fst) fun ld_3 =>
       Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var ld_3, ()) } fun p =>
       Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                   args := (Arg.var pVals, Arg.var p.fst, ()) } fun p =>
       Expr.load i8 (Arg.var p.fst) fun ld_4 =>
       Expr.let_ { sig := [i32], code := OpCode.trunc 32 8, args := (Arg.imm 0, ()) } fun p =>
       Expr.let_ { sig := [i8], code := OpCode.sext 8 32, args := (Arg.var ld_4, ()) } fun p_9 =>
       Expr.let_ { sig := [i8], code := OpCode.sext 8 32, args := (Arg.var p.fst, ()) } fun p =>
       Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.sgt i32 Ty.bool (by decide),
                   args := (Arg.var p_9.fst, Arg.var p.fst, ()) } fun p =>
       Expr.jnz (Arg.var p.fst) (Expr.ret (Arg.imm 1, ()))
         (Expr.group (sig := [[i32]]) (fun Js_1 => Blocks.cons (fun p =>
           Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                       args := (Arg.var p_7.snd.fst, Arg.imm 1, ()) } fun p_10 =>
           Expr.jump Js.fst (Arg.var p.fst, Arg.var p_10.fst, ())) Blocks.nil) fun Js =>
          Expr.let_ { sig := [i32], code := OpCode.trunc 32 8, args := (Arg.imm 0, ()) } fun p =>
          Expr.let_ { sig := [i8], code := OpCode.sext 8 32,
                      args := (Arg.var ld_4, ()) } fun p_10 =>
          Expr.let_ { sig := [i8], code := OpCode.sext 8 32, args := (Arg.var p.fst, ()) } fun p =>
          Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32 Ty.bool (by decide),
                      args := (Arg.var p_10.fst, Arg.var p.fst, ()) } fun p =>
          Expr.jnz (Arg.var p.fst)
            (Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                         args := (Arg.var p_7.fst, ()) } fun p =>
             Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                         args := (Arg.var p.fst, Arg.imm 4, ()) } fun p =>
             Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                         args := (Arg.var pTmp, Arg.var p.fst, ()) } fun p =>
             Expr.store (Arg.var ld_3) (Arg.var p.fst)
               (Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                            args := (Arg.var p_7.fst, Arg.imm 1, ()) } fun p =>
                Expr.jump Js.fst (Arg.var p.fst, ())))
            (Expr.jump Js.fst (Arg.var p_7.fst, ()))))
      (Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32 Ty.bool (by decide),
                   args := (Arg.var p_7.fst, Arg.imm 0, ()) } fun p_9 =>
       Expr.jnz (Arg.var p_9.fst) (Expr.ret (Arg.imm 2, ()))
         (Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.eq i32 Ty.bool (by decide),
                      args := (Arg.var p_7.fst, Arg.imm 1, ()) } fun p_10 =>
          Expr.jnz (Arg.var p_10.fst)
            (Expr.let_ { sig := [i32], code := OpCode.sext 32 64,
                         args := (Arg.imm 0, ()) } fun p_11 =>
             Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                         args := (Arg.var p_11.fst, Arg.imm 4, ()) } fun p_12 =>
             Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                         args := (Arg.var pTmp, Arg.var p_12.fst, ()) } fun p_13 =>
             Expr.load i32 (Arg.var p_13.fst) fun ld =>
             Expr.call (as := [i64, i32, i32]) (bs := []) "kissat_assign"
               (Arg.var hdr, Arg.var ld, Arg.imm 4294967295, ()) fun _ => Expr.ret (Arg.imm 1, ()))
            (Expr.call (as := [i64, i32]) (bs := [i64]) "kissat_add_clause"
              (Arg.var hdr, Arg.var p_7.fst, ()) fun p =>
             Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool (by decide),
                         args := (Arg.var p.fst, Arg.imm 4294967295, ()) } fun p =>
             Expr.jnz (Arg.var p.fst) (Expr.ret (Arg.imm 3, ())) (Expr.ret (Arg.imm 1, ())))))
  ) Blocks.nil) fun Js => Expr.jump Js.fst (Arg.imm 0, Arg.imm 0, ())

private def ingestClearMrkExpr (hdr pTmp pMark pVals : Val i64)
    (tlen_v : Val i32) (taut_v err_v : Val Ty.bool) : Expr Val Cont [i64] :=
  Expr.group (sig := [[i32]]) (fun Js => Blocks.cons (fun p_5 =>
    Expr.let_ { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool (by decide),
                args := (Arg.var p_5.fst, Arg.var tlen_v, ()) } fun p_6 =>
    Expr.jnz (Arg.var p_6.fst)
      (Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                   args := (Arg.var p_5.fst, ()) } fun p_7 =>
       Expr.let_ { sig := [i64, i64], code := OpCode.mul i64,
                   args := (Arg.var p_7.fst, Arg.imm 4, ()) } fun p_8 =>
       Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                   args := (Arg.var pTmp, Arg.var p_8.fst, ()) } fun p_9 =>
       Expr.load i32 (Arg.var p_9.fst) fun ld =>
       Expr.let_ { sig := [i32, i32], code := OpCode.lshr i32,
                   args := (Arg.var ld, Arg.imm 1, ()) } fun p_10 =>
       Expr.group (sig := [[]]) (fun Js_1 => Blocks.cons (fun _ =>
         Expr.let_ { sig := [i32, i32], code := OpCode.add i32,
                     args := (Arg.var p_5.fst, Arg.imm 1, ()) } fun p =>
         Expr.jump Js.fst (Arg.var p.fst, ())) Blocks.nil) fun Js =>
       Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                   args := (Arg.var p_10.fst, ()) } fun p_11 =>
       Expr.load i64 (Arg.var hdr) fun ld =>
       Expr.let_ { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool (by decide),
                   args := (Arg.var p_11.fst, Arg.var ld, ()) } fun p =>
       Expr.jnz (Arg.var p.fst)
         (Expr.let_ { sig := [i32], code := OpCode.zext 32 64,
                      args := (Arg.var p_10.fst, ()) } fun p =>
          Expr.let_ { sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var pMark, Arg.var p.fst, ()) } fun p =>
          Expr.let_ { sig := [i32], code := OpCode.trunc 32 8, args := (Arg.imm 0, ()) } fun p_12 =>
          Expr.store (Arg.var p_12.fst) (Arg.var p.fst) (Expr.jump Js.fst ()))
         (Expr.jump Js.fst ()))
      (Expr.jnz (Arg.var err_v) (Expr.ret (Arg.imm 0, ()))
        (Expr.jnz (Arg.var taut_v) (Expr.ret (Arg.imm 1, ()))
          (ingestPruneExpr hdr pTmp pVals tlen_v)))) Blocks.nil)
    fun Js => Expr.jump Js.fst (Arg.imm 0, ())

private theorem ingest_addcl_wp {Γ : Env}
    (hAddCl : ∀ a m Q X, corePlusAddClauseSpec a m Q X →
      Γ "kissat_add_clause" [i64, i32] [i64] a m Q X)
    {c : CorePlusCfg} {accCnf : CNF Nat} {s st st3 : CorePlusState} {cnf_ptr : BitVec 64}
    {cnfBytes : List UInt8} {i0 idx tlen : Nat} {revLits : List Nat} {kp_v : Val i32}
    {R : Mem 64 → Prop} {m3 : Mem 64} {Q : Post [i64]} {X : XPost}
    (hinv3 : CorePlusInv c (shiftDownCnf (accCnf.add
      (CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral)))) st3)
    (hkp_ge2 : 2 ≤ kp_v.toNat) (hkle_tlen : kp_v.toNat ≤ tlen) (htlen_le : tlen ≤ c.mv)
    (hkp_un : ∀ k < kp_v.toNat, (st3.tmp[k]?.getD 0#32).toNat < 2 * c.mv)
    (hF1_keep : (shiftDownCnf (accCnf.add
      (CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral)))).EntailsClause
      (cnfClause ((st3.tmp.take kp_v.toNat).map BitVec.toNat)))
    (hri : IngestReadInv c s cnfBytes.length i0 idx tlen false revLits st)
    (hi0_lt : i0 < idx) (hdcur_st : st3.d_cur = cnf_ptr + BitVec.ofNat 64 idx)
    (hs2cl : st3.cur_level = 0) (hs2fu : st3.fuel = s.fuel)
    (hs2rt : st3.heur.rel_trigger = s.heur.rel_trigger)
    (hm3 : (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c st3 ⋆ R) m3)
    (hQ : IngestClausePost c accCnf s cnf_ptr cnfBytes i0 R Q
      (CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral))
      (cnfBytes.drop idx)) :
    wp Γ Q X (Expr.call (as := [i64, i32]) (bs := [i64]) "kissat_add_clause"
      (Arg.var c.hdr, Arg.var kp_v, ()) fun p =>
      Expr.let_
        { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool (by decide),
          args := (Arg.var p.fst, Arg.imm 4294967295, ()) } fun p =>
      Expr.jnz (Arg.var p.fst) (Expr.ret (Arg.imm 3, ())) (Expr.ret (Arg.imm 1, ()))) m3 := by
  have hcl_pos : ∀ lit ∈ (CNF.Clause.ofLiterals
      (revLits.reverse.map kissatLitToDimacsLiteral)).literals, 1 ≤ lit.1 := fun lit hlit => by
    simp only [CNF.Clause.literals_ofLiterals, List.mem_map] at hlit
    rcases hlit with ⟨l, _, rfl⟩; simp [kissatLitToDimacsLiteral]
  have hlen3 := hinv3.core.lengths
  have hnot_unit : ∀ l, revLits = [l] → False := fun l h => by
    have := (hri.unit_r l h).2.1; omega
  c0_call hAddCl
  refine ⟨c, st3, bytes cnf_ptr cnfBytes ⋆ R, rfl, hlen3, by omega, sep_ac hm3, ?_⟩
  by_cases hoom : c.max_c ≤ st3.num_clauses ∨ c.lcap - st3.lit_len < kp_v.toNat
  · simp only [hoom, ↓reduceIte]; cp_steps
    · exact hQ 3#64 st3 idx m3 hcl_pos hi0_lt hri.idx_le rfl hlen3 hdcur_st hs2cl hs2fu
        hs2rt (Or.inr (Or.inr rfl)) (fun h => by cases h) (fun h => by cases h)
        (fun l hl hcleq _ => False.elim (hnot_unit l (ingest_unit_rev hl hcleq)))
        (fun l hl hcleq _ => False.elim (hnot_unit l (ingest_unit_rev hl hcleq))) hm3
    · exact absurd rfl (by assumption : ¬(0xFFFFFFFF#64 : BitVec 64) = 0xFFFFFFFF)
  · simp only [hoom, ↓reduceIte]
    intro lpool' cls' wh' wn' m4 hlen_sf hmeta hlp_pre hoff hsz hlits hm4
    have hmc := c.hmax_c; unfold dimacsBound at hmc
    have hne_ff : BitVec.ofNat 64 st3.num_clauses ≠ (0xFFFFFFFF : BitVec 64) := by
      intro heq; have hnc_le := hlen3.num_clauses_le
      have ht := congrArg BitVec.toNat heq; rw [bv64_ofNat_toNat (by omega)] at ht
      have hff : (0xFFFFFFFF : BitVec 64).toNat = 4294967295 := by decide
      rw [hff] at ht; omega
    cp_steps
    exact ingest_addcl_post hinv3 ⟨hdcur_st, hs2cl, hs2fu, hs2rt⟩ hkp_ge2 hkle_tlen htlen_le
      hkp_un hF1_keep (fun l h => False.elim (hnot_unit l h))
      (fun l _ h => False.elim (hnot_unit l h)) (fun l _ h => False.elim (hnot_unit l h))
      hi0_lt hri.idx_le hlen_sf hmeta hlp_pre hoff hsz hlits (sep_ac hm4) hQ

private theorem ingest_prune_wp {Γ : Env}
    (hAssign : ∀ a m Q X, corePlusAssignSpec a m Q X → Γ "kissat_assign" [i64, i32, i32] [] a m Q X)
    (hAddCl : ∀ a m Q X, corePlusAddClauseSpec a m Q X →
      Γ "kissat_add_clause" [i64, i32] [i64] a m Q X)
    {c : CorePlusCfg} {accCnf : CNF Nat} {s st st2 : CorePlusState} {cnf_ptr : BitVec 64}
    {cnfBytes : List UInt8} {i0 idx tlen : Nat} {revLits : List Nat} {mrk' : List (BitVec 8)}
    {R : Mem 64 → Prop} {m2 : Mem 64} {Q : Post [i64]} {X : XPost}
    (hcore : CorePlusCoreInv c (shiftDownCnf accCnf) s) (hlen : s.LengthsOk c)
    (hcl0 : s.cur_level = 0)
    (hri : IngestReadInv c s cnfBytes.length i0 idx tlen false revLits st) (hi0_lt : i0 < idx)
    (hdcur_st : st.d_cur = cnf_ptr + BitVec.ofNat 64 idx) (hmk'l : mrk'.length = c.mv)
    (hmc2 : MarksClear c { st with mrk := mrk' }) (hst2 : st2 = { st with mrk := mrk' })
    (hag2 : st2 = { s with d_cur := st.d_cur, d_val := st.d_val, mrk := mrk', tmp := st.tmp })
    (hm2 : (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c st2 ⋆ R) m2)
    (hQ : IngestClausePost c accCnf s cnf_ptr cnfBytes i0 R Q
      (CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral))
      (cnfBytes.drop idx)) :
    wp Γ Q X (ingestPruneExpr c.hdr c.pTmp c.pVals (BitVec.ofNat 32 tlen)) m2 := by
  have htlen_le := hri.tlen_le; have htmpl := hri.tmp_len; have hmv := c.hmv
  unfold dimacsBound at hmv
  let cl := CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral)
  have hcl_pos : ∀ lit ∈ cl.literals, 1 ≤ lit.1 := fun lit hlit => by
    simp only [cl, CNF.Clause.literals_ofLiterals, List.mem_map] at hlit
    rcases hlit with ⟨l, _, rfl⟩; simp [kissatLitToDimacsLiteral]
  let F1 := shiftDownCnf (accCnf.add cl)
  have hF1_cl := ingest_F1_cl (accCnf := accCnf) htlen_le htmpl (hri.cov rfl) rfl
  have hst2_vals : st2.vals = s.vals := by rw [hst2, hri.agree]
  have hst2_vlen : st2.vals.length = 2 * c.mv := by rw [hst2_vals, hlen.vals_len]
  unfold ingestPruneExpr
  refine wp_loop_inv (fun (kp_v, iv, ()) m3 => ∃ tmp',
      IngestPruneInv c s tlen kp_v.toNat iv.toNat revLits st.tmp tmp' ∧
      (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c { st2 with tmp := tmp' } ⋆ R) m3)
    (fun (_, iv, ()) _ => tlen - iv.toNat) ?_ ?_
  · intro L3 hL3; cp_steps; exact hL3 (0#32, 0#32, ()) m2 ⟨st.tmp, ⟨Nat.zero_le _, Nat.zero_le _,
      htmpl, (fun _ _ _ => rfl), (fun _ h => by cases h), (fun _ h => by cases h),
      (fun _ _ _ _ h => by cases h), (fun _ _ _ _ h => by cases h)⟩,
      by rwa [show { st2 with tmp := st.tmp } = st2 by rw [hst2]]⟩
  · intro L3 ⟨kp_v, iv, ⟨⟩⟩ m3 ⟨tmp', hp, hm3⟩ hL3
    have hkle3 := hp.keep_le; have hile3 := hp.i_le; have htmpl3 := hp.tmp_len
    let st3 : CorePlusState := { st2 with tmp := tmp' }
    have hag3 : st3 = { s with
        d_cur := st.d_cur, d_val := st.d_val, mrk := mrk', tmp := tmp' } :=
      congrArg (fun x => { x with tmp := tmp' }) hag2
    have hcore3 : CorePlusCoreInv c (shiftDownCnf accCnf) st3 := by
      rw [hag3]; exact core_inv_d_mrk_tmp hcore st.d_cur st.d_val hmk'l htmpl3
    have hlen3 := hcore3.lengths
    have hmc3 : MarksClear c st3 := fun v hv => by dsimp only [st3]; rw [hst2]; exact hmc2 v hv
    have hinv3 : CorePlusInv c F1 st3 := ⟨hcore3.mono (shiftDownCnf_entails_add accCnf cl), hmc3⟩
    have hs2cl : st3.cur_level = 0 := by rw [hag3]; exact hcl0
    have hs2fu : st3.fuel = s.fuel := by rw [hag3]
    have hF1_eq : iv.toNat = tlen → F1.EntailsClause
        (cnfClause ((tmp'.take kp_v.toNat).map BitVec.toNat)) := fun h =>
      ingest_F1_keep rfl hcore hcl0 (by omega) htmpl htmpl3 htlen_le hF1_cl hri.tmp_lt
        (h ▸ hp).pruned
    cp_steps
    · have hilt3 : iv.toNat < tlen := by clear hm3 hm2 hQ; c0_bound
      let li := tmp'[iv.toNat]'(by omega)
      have hli_eq : li = st.tmp[iv.toNat]'(by omega) := by
        have h1 := hp.tail_eq iv.toNat (Nat.le_refl _) hilt3
        rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at h1
        exact Option.some.inj h1
      have hli_lt : li.toNat < 2 * c.mv := by
        have := hri.tmp_lt iv.toNat hilt3
        rwa [List.getElem?_eq_getElem (by omega), Option.getD_some, ← hli_eq] at this
      have hiv64 : (BitVec.setWidth 64 iv).toNat = iv.toNat := by
        clear hm3 hm2 hQ; simp only [bv_c0]
      have hli_st2_lt : (tmp'[(BitVec.setWidth 64 iv).toNat]'(by
          rw [hiv64, htmpl3]; omega)).toNat < st2.vals.length := by
        rw [hst2_vlen]; simpa only [hiv64] using hli_lt
      have hv_eq : ({ st2 with tmp := tmp' }).vals[li.toNat]'(by
            change st2.vals.length > _; rw [hst2_vlen]; exact hli_lt) =
          s.vals[li.toNat]'(by rw [hlen.vals_len]; exact hli_lt) := by
        change st2.vals[li.toNat] = _; simp only [hst2_vals]
      have hlv_dom := hcore.vals_domain li.toNat hli_lt
      have hlv_getD : s.vals[li.toNat]?.getD 0#8 =
          s.vals[li.toNat]'(by rw [hlen.vals_len]; exact hli_lt) := by
        rw [List.getElem?_eq_getElem (by rw [hlen.vals_len]; exact hli_lt), Option.getD_some]
      rw [List.getElem?_eq_getElem (by rw [hlen.vals_len]; exact hli_lt),
        Option.getD_some] at hlv_dom
      cp_steps
      · exact ingest_lv_pos_exit hcore hmc2 hri hi0_lt hdcur_st hcl0 hmk'l htmpl3 hag3 hilt3
          hli_eq hli_lt (by rw [hlv_getD]; exact (i8_vals_sgt0 hlv_dom).mp (by rwa [← hv_eq]))
          hm3 hQ
      · have hlv0 : s.vals[li.toNat]?.getD 0#8 = 0#8 := by
          rw [hlv_getD]; exact (i8_vals_eq0 hlv_dom).mp (by rwa [← hv_eq])
        have hkv64 : (BitVec.setWidth 64 kp_v).toNat = kp_v.toNat := by
          clear hm hQ; simp only [bv_c0]
        have hiv64' : (BitVec.setWidth 64 iv).toNat = iv.toNat := by clear hm hQ; simp only [bv_c0]
        exact hL3 (kp_v + 1#32, iv + 1#32, ()) _ (by clear hm hQ; c0_bound)
          ⟨_, by simpa [show (kp_v + 1#32).toNat = kp_v.toNat + 1 by c0_bound,
              show (iv + 1#32).toNat = iv.toNat + 1 by c0_bound] using
              (ingest_prune_push_inv hp hilt3 htlen_le htmpl
                (fun l h => ⟨(hri.unit_r l h).2.1, (hri.unit_r l h).2.2⟩) hli_eq hli_lt hlv0),
            by simpa only [hkv64, hiv64'] using sep_ac hm⟩
      · have hneg1 : (0#32).slt (BitVec.signExtend 32
            (st2.vals[li.toNat]'(by rw [hst2_vlen]; exact hli_lt))) = false := by assumption
        have hne0 : BitVec.signExtend 32
            (st2.vals[li.toNat]'(by rw [hst2_vlen]; exact hli_lt)) ≠ 0#32 := by assumption
        simp only [hst2_vals] at hneg1 hne0
        have hlv_ff : s.vals[li.toNat]?.getD 0#8 = 0xFF#8 := by
          rw [hlv_getD]; rcases hlv_dom with h | h | h
          · rw [h] at hne0; exact absurd hne0 (by decide)
          · rw [h] at hneg1; exact absurd hneg1 (by decide)
          · exact h
        exact hL3 (kp_v, iv + 1#32, ()) _ (by clear hm3 hQ; c0_bound)
          ⟨_, by simpa [show (iv + 1#32).toNat = iv.toNat + 1 by c0_bound] using
              (ingest_prune_skip_inv hp hilt3 htlen_le htmpl
                (fun l h => ⟨(hri.unit_r l h).2.1, (hri.unit_r l h).2.2⟩) hli_eq hlv_ff), hm3⟩
    · have hieq3 : iv.toNat = tlen := by clear hm3 hm2 hQ; c0_bound
      have hk0 : kp_v.toNat = 0 := by clear hm3 hQ; c0_bound
      have hF1_keep := hF1_eq hieq3; rw [hk0] at hF1_keep; rw [hieq3] at hp
      exact hQ 2#64 st3 idx m3 hcl_pos hi0_lt hri.idx_le rfl hlen3 (by rw [hag3]; exact hdcur_st)
        hs2cl hs2fu (by rw [hag3]) (Or.inr (Or.inl rfl)) (fun h => by cases h)
        (fun _ => unsat_of_entails_nil (by simpa [F1, cl] using hF1_keep))
        (fun l hl hcleq hv0 => by
          have hr := ingest_unit_rev hl hcleq
          have h1 := (hp.unit0 l hl hr hv0 (hri.unit_r l hr).2.1).1; omega)
        (fun _ _ _ _ => rfl) hm3
    · have hieq3 : iv.toNat = tlen := by clear hm3 hm2 hQ; c0_bound
      have hk1 : kp_v.toNat = 1 := by clear hm3 hQ; c0_bound
      have hF1_keep := hF1_eq hieq3; rw [hieq3] at hp
      let l0 := tmp'[0]'(by rw [htmpl3]; omega)
      have ⟨hl0_lt, hl0_un⟩ := hp.keep_un 0 (by omega)
      have htmp0_eq : tmp'[0]? = some l0 := List.getElem?_eq_getElem (by rw [htmpl3]; omega)
      rw [htmp0_eq, Option.getD_some] at hl0_lt hl0_un
      have hl0_ent : F1.EntailsClause (cnfClause [l0.toNat]) := by
        have htk : tmp'.take 1 = [l0] := by
          cases tmp' with | nil => simp at htmpl3; omega | cons _ _ => rfl
        simpa [F1, cl, hk1, htk] using hF1_keep
      have hte_lt : st3.trail_end < c.mv :=
        hinv3.core.trail_end_lt_of_unassigned hl0_lt (by rw [hag3]; exact hl0_un)
      c0_call hAssign
      refine ⟨c, st3, bytes cnf_ptr cnfBytes ⋆ R, rfl, hlen3, sep_ac hm3, ?_⟩
      have hng : ¬ (c.mv ≤ tmp'[0].toNat / 2 ∨ c.mv ≤ st3.trail_end) := by
        change ¬ (c.mv ≤ l0.toNat / 2 ∨ c.mv ≤ st3.trail_end); omega
      simp only [hng, ↓reduceIte]; intro ph4 m4 hph4 hlen4 hm4; cp_steps
      exact ingest_assign_post hinv3 ⟨by rw [hag3]; exact hdcur_st, hs2cl, hs2fu,
        by rw [hag3], by rw [hag3], by rw [hag3], by rw [hag3], by rw [hag3], by rw [hag3]⟩
        hl0_lt hph4 (by rw [hag3]; exact hl0_un) hl0_ent
        (fun l h => (hri.unit_r l h).2.1) (fun l hl hrev hv0 ht1 => by
          have ⟨_, hl0eq⟩ := hp.unit0 l hl hrev hv0 ht1
          rw [htmp0_eq, Option.getD_some] at hl0eq; exact ⟨rfl, hl0eq⟩)
        (hk1 ▸ hp.unit1) hi0_lt hri.idx_le hlen4 (sep_ac hm4) hQ
    · have hieq3 : iv.toNat = tlen := by clear hm3 hm2 hQ; c0_bound
      have hkp_ge2 : 2 ≤ kp_v.toNat := by clear hm3 hQ; c0_bound
      exact ingest_addcl_wp hAddCl hinv3 hkp_ge2 (by omega) htlen_le
        (fun k hk => (hp.keep_un k hk).1) (hF1_eq hieq3) hri hi0_lt (by rw [hag3]; exact hdcur_st)
        hs2cl hs2fu (by rw [hag3]) hm3 hQ

private theorem ingest_clear_mrk_wp {Γ : Env}
    (hAssign : ∀ a m Q X, corePlusAssignSpec a m Q X →
      Γ "kissat_assign" [i64, i32, i32] [] a m Q X)
    (hAddCl : ∀ a m Q X, corePlusAddClauseSpec a m Q X →
      Γ "kissat_add_clause" [i64, i32] [i64] a m Q X)
    {c : CorePlusCfg} {accCnf : CNF Nat} {s st : CorePlusState} {cnf_ptr : BitVec 64}
    {cnfBytes : List UInt8} {i0 idx tlen : Nat} {revLits : List Nat} {taut_v err_v : Bool}
    {R : Mem 64 → Prop} {mb : Mem 64} {Q : Post [i64]} {X : XPost}
    (hcore : CorePlusCoreInv c (shiftDownCnf accCnf) s) (hlen : s.LengthsOk c)
    (hcl0 : s.cur_level = 0)
    (hri : IngestReadInv c s cnfBytes.length i0 idx tlen taut_v revLits st)
    (herr_p : err_v = true → parseClause c.mv (cnfBytes.drop i0) = none)
    (hok_p : err_v = false → i0 < idx ∧ st.d_cur = cnf_ptr + BitVec.ofNat 64 idx ∧
      parseClause c.mv (cnfBytes.drop i0) =
        some (CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral),
          cnfBytes.drop idx))
    (hmb : (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c st ⋆ R) mb)
    (hQ : match parseClause c.mv (cnfBytes.drop i0) with
      | none => ∀ s' m', s'.LengthsOk c → s'.fuel = s.fuel →
          s'.heur.rel_trigger = s.heur.rel_trigger →
          (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c s' ⋆ R) m' → Q (0#64, ()) m'
      | some (cl, rest) => IngestClausePost c accCnf s cnf_ptr cnfBytes i0 R Q cl rest) :
    wp Γ Q X (ingestClearMrkExpr c.hdr c.pTmp c.pMark c.pVals
      (BitVec.ofNat 32 tlen) taut_v err_v) mb := by
  have htlen_le := hri.tlen_le; have htmpl := hri.tmp_len; have hmv := c.hmv
  unfold dimacsBound at hmv
  unfold ingestClearMrkExpr
  refine wp_loop_inv
    (fun (k_v : Tup Val [i32]) m2 => ∃ mrk',
      k_v.1.toNat ≤ tlen ∧ mrk'.length = c.mv ∧
      (∀ v < c.mv,
        (∀ j, k_v.1.toNat ≤ j → j < tlen → (st.tmp[j]?.getD 0#32).toNat / 2 ≠ v) →
        mrk'[v]?.getD 0#8 = 0#8) ∧
      (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c { st with mrk := mrk' } ⋆ R) m2)
    (fun k_v _ => tlen - k_v.1.toNat) ?_ ?_
  · intro L2 hL2; cp_steps; exact hL2 (0#32, ()) mb
      ⟨st.mrk, Nat.zero_le _, hri.mrk_len,
        fun v hv hmiss => hri.mrk_zero v hv fun j hj => hmiss j (Nat.zero_le _) hj, hmb⟩
  · intro L2 ⟨k_v, ⟨⟩⟩ m2 ⟨mrk', hkle, hmk'l, hclr, hm2⟩ hL2
    dsimp only at hkle hclr; cp_steps
    · have hklt : k_v.toNat < tlen := by clear hQ; c0_bound
      have hlitk_lt : (st.tmp[k_v.toNat]'(by omega)).toNat < 2 * c.mv := by
        have := hri.tmp_lt k_v.toNat hklt
        rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
      have hvk_lt : (st.tmp[k_v.toNat]'(by omega)).toNat / 2 < c.mv := by omega
      have hkv64 : (BitVec.setWidth 64 k_v).toNat = k_v.toNat := by clear hQ; simp only [bv_c0]
      have hidx_eq :
          (BitVec.setWidth 64
            (st.tmp[(BitVec.setWidth 64 k_v).toNat]'(by rw [hkv64]; omega) >>> 1)).toNat =
            (st.tmp[k_v.toNat]'(by omega)).toNat / 2 := by clear hQ; simp only [bv_c0]
      refine hL2 (k_v + 1#32, ()) _ (by clear hm hQ; c0_bound)
        ⟨mrk'.set ((st.tmp[k_v.toNat]'(by omega)).toNat / 2) 0#8,
          by clear hm hQ; c0_bound, by simp [hmk'l], fun v hv hmiss => ?_,
          by rw [← hidx_eq]; exact sep_ac hm⟩
      by_cases hveq : v = (st.tmp[k_v.toNat]'(by omega)).toNat / 2
      · rw [hveq, List.getElem?_set_self (by omega)]; rfl
      · rw [List.getElem?_set_ne (Ne.symm hveq)]
        refine hclr v hv fun j hj1 hj2 => ?_
        by_cases hjk : j = k_v.toNat
        · subst j; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact Ne.symm hveq
        · exact hmiss j (by
            dsimp only; have : (k_v + 1#32).toNat = k_v.toNat + 1 := (by c0_bound); omega) hj2
    · exfalso; have hklt : k_v.toNat < tlen := by clear hm2 hQ; c0_bound
      have := hri.tmp_lt k_v.toNat hklt
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at this; omega
    · have hkeq : k_v.toNat = tlen := by clear hm2 hQ; c0_bound
      have herr : err_v = true := by assumption
      subst herr; let st2 : CorePlusState := { st with mrk := mrk' }
      have hag2 : st2 =
          { s with d_cur := st.d_cur, d_val := st.d_val, mrk := mrk', tmp := st.tmp } :=
        congrArg (fun x => { x with mrk := mrk' }) hri.agree
      have hcore2 : CorePlusCoreInv c (shiftDownCnf accCnf) st2 := by
        rw [hag2]; exact core_inv_d_mrk_tmp hcore st.d_cur st.d_val hmk'l htmpl
      rw [herr_p rfl] at hQ; exact hQ st2 m2 hcore2.lengths (by rw [hag2]) (by rw [hag2]) hm2
    · have hkeq : k_v.toNat = tlen := by clear hm2 hQ; c0_bound
      have hne : err_v = false := by assumption
      have htaut : taut_v = true := by assumption
      subst hne htaut; let st2 : CorePlusState := { st with mrk := mrk' }
      have hag2 : st2 =
          { s with d_cur := st.d_cur, d_val := st.d_val, mrk := mrk', tmp := st.tmp } :=
        congrArg (fun x => { x with mrk := mrk' }) hri.agree
      have hcore2 : CorePlusCoreInv c (shiftDownCnf accCnf) st2 := by
        rw [hag2]; exact core_inv_d_mrk_tmp hcore st.d_cur st.d_val hmk'l htmpl
      have hmc2 : MarksClear c st2 := fun v hv => hclr v hv fun j hj1 hj2 => by omega
      obtain ⟨hi0_lt, hdcur_st, hpc_some⟩ := hok_p rfl
      let cl := CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral)
      have hcl_pos : ∀ lit ∈ cl.literals, 1 ≤ lit.1 := fun lit hlit => by
        simp only [cl, CNF.Clause.literals_ofLiterals, List.mem_map] at hlit
        rcases hlit with ⟨l, _, rfl⟩; simp [kissatLitToDimacsLiteral]
      rw [hpc_some] at hQ; exact hQ 1#64 st2 idx m2 hcl_pos hi0_lt hri.idx_le rfl hcore2.lengths
        hdcur_st (by rw [hag2]; exact hcl0) (by rw [hag2]) (by rw [hag2]) (Or.inl rfl)
        (fun _ => ⟨hcore2.mono (shiftDownCnf_entails_add _ _), hmc2⟩) (fun h => by cases h)
        (fun l hl hcleq _ => by have := (hri.unit_r l (ingest_unit_rev hl hcleq)).1; cases this)
        (fun l hl hcleq _ => by have := (hri.unit_r l (ingest_unit_rev hl hcleq)).1; cases this) hm2
    · have hkeq : k_v.toNat = tlen := by clear hm2 hQ; c0_bound
      have hne : err_v = false := by assumption
      have hnt : taut_v = false := by assumption
      subst hne hnt; obtain ⟨hi0_lt, hdcur_st, hpc_some⟩ := hok_p rfl
      rw [hpc_some] at hQ; exact ingest_prune_wp hAssign hAddCl hcore hlen hcl0 hri hi0_lt
        hdcur_st hmk'l (fun v hv => hclr v hv fun j hj1 hj2 => by omega) rfl
        (congrArg (fun x => { x with mrk := mrk' }) hri.agree) hm2 hQ

private theorem ingest_read_inv_with_d {c : CorePlusCfg} {s st : CorePlusState}
    {mLen i0 idx j tlen : Nat} {taut : Bool} {revLits : List Nat}
    {dc dv : BitVec 64}
    (hri : IngestReadInv c s mLen i0 idx tlen taut revLits st)
    (hige : i0 ≤ j) (hj : j ≤ mLen) :
    IngestReadInv c s mLen i0 j tlen taut revLits { st with d_cur := dc, d_val := dv } :=
  ⟨hige, hj, hri.tlen_le, congrArg (fun x => { x with d_cur := dc, d_val := dv }) hri.agree,
    hri.mrk_len, hri.tmp_len, hri.tmp_lt, hri.tmp_nd, hri.mrk_zero, hri.mrk_pos,
    hri.cov, hri.sub_rev, hri.nil_taut, hri.unit_r⟩

private theorem ingest_dup_step {c : CorePlusCfg} {s st : CorePlusState}
    {cnf_ptr : BitVec 64} {cnfBytes : List UInt8} {i0 idx j tlen l : Nat}
    {taut_v taut' : Bool} {revLits : List Nat}
    (hri : IngestReadInv c s cnfBytes.length i0 idx tlen taut_v revLits st)
    (hij : idx < j) (hj : j ≤ cnfBytes.length) (hl_mv : l < 2 * c.mv)
    (hl_idx : l % 2 ^ 64 % 2 ^ 32 / 2 ^ 1 = l / 2)
    (hptag32 :
      ((BitVec.setWidth 32 (BitVec.ofNat 64 l) &&& (1 : BitVec 32)) + 1).setWidth 8 =
      BitVec.ofNat 8 (l % 2 + 1))
    (hm32_ne : BitVec.setWidth 32 (st.mrk[l % 2 ^ 64 % 2 ^ 32 / 2 ^ 1]'(by
      have := hri.mrk_len; omega)) ≠ 0#32)
    (hbranch :
      (taut' = true ∧ BitVec.setWidth 32
        (st.mrk[l % 2 ^ 64 % 2 ^ 32 / 2 ^ 1]'(by have := hri.mrk_len; omega)) ≠
        BitVec.setWidth 32 (BitVec.setWidth 8
          ((BitVec.setWidth 32 (BitVec.ofNat 64 l) &&& (1 : BitVec 32)) + 1))) ∨
      (taut' = taut_v ∧ BitVec.setWidth 32
        (st.mrk[l % 2 ^ 64 % 2 ^ 32 / 2 ^ 1]'(by have := hri.mrk_len; omega)) =
        BitVec.setWidth 32 (BitVec.setWidth 8
          ((BitVec.setWidth 32 (BitVec.ofNat 64 l) &&& (1 : BitVec 32)) + 1)))) :
    IngestReadInv c s cnfBytes.length i0 j tlen taut' (l :: revLits)
      { st with d_cur := cnf_ptr + BitVec.ofNat 64 j, d_val := BitVec.ofNat 64 l } := by
  have hmkl := hri.mrk_len
  have hmne0 : st.mrk[l / 2]'(by omega) ≠ 0#8 := fun h0 =>
    hm32_ne (by simp only [hl_idx, h0]; rfl)
  obtain ⟨k0, hk0, hk0_v⟩ := ingest_exists_var_of_nz hri hl_mv hmne0
  have hdu := ingest_read_dup_inv hri hij hj hk0 hl_mv hk0_v
    (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 l)
  rcases hbranch with ⟨rfl, hne⟩ | ⟨rfl, heq⟩
  · have htag_ne : st.mrk[l / 2]'(by omega) ≠ BitVec.ofNat 8 (l % 2 + 1) := fun h =>
      hne (by simp only [hl_idx, hptag32, h])
    simpa [htag_ne] using hdu
  · have htag_eq : st.mrk[l / 2]'(by omega) = BitVec.ofNat 8 (l % 2 + 1) :=
      (bv8_setWidth32_eq_iff _ _).mp (by simpa only [hl_idx, hptag32] using heq)
    simpa [htag_eq] using hdu

theorem kissat_ingest_clause_wp (Γ : Env)
    (hLit : ∀ a m Q X, kissatNextLitSpec a m Q X →
      Γ "kissat_next_lit" [i64, i64] [i64] a m Q X)
    (hAssign : ∀ a m Q X, corePlusAssignSpec a m Q X →
      Γ "kissat_assign" [i64, i32, i32] [] a m Q X)
    (hAddCl : ∀ a m Q X, corePlusAddClauseSpec a m Q X →
      Γ "kissat_add_clause" [i64, i32] [i64] a m Q X) :
    ∀ a m Q X, corePlusIngestClauseSpec a m Q X →
      Func.wp Γ kissat_ingest_clause_body a m Q X := by
  rintro ⟨h, cend, ⟨⟩⟩ m Q X
    ⟨c, accCnf, s, cnf_ptr, cnfBytes, i0, R, rfl, rfl, hfit, hi0, hdcur, hcl0, hinv, hm, hQ⟩
  have hcore := hinv.core; have hlen := hcore.lengths; have hmv : c.mv < 2 ^ 28 := c.hmv
  cp_steps
  have hBrk : ∀ (tlen_v : BitVec 32) (taut_v err_v : Bool) mb,
      (∃ idx tlen revLits st,
        tlen_v = BitVec.ofNat 32 tlen ∧
        IngestReadInv c s cnfBytes.length i0 idx tlen taut_v revLits st ∧
        (err_v = true → parseClause c.mv (cnfBytes.drop i0) = none) ∧
        (err_v = false → i0 < idx ∧ st.d_cur = cnf_ptr + BitVec.ofNat 64 idx ∧
          parseClause c.mv (cnfBytes.drop i0) =
            some (CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral),
              cnfBytes.drop idx)) ∧
        (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c st ⋆ R) mb) →
      J (tlen_v, taut_v, err_v, ()) mb := by
    rintro tlen_v taut_v err_v mb ⟨idx, tlen, revLits, st, rfl, hri, herr_p, hok_p, hmb⟩
    exact hJ _ _ (ingest_clear_mrk_wp hAssign hAddCl hcore hlen hcl0 hri herr_p hok_p hmb hQ)
  refine wp_loop_group
    (fun r (tlen_v, taut_v, ()) ml => ∃ idx tlen revLits st,
      r = cnfBytes.length - idx ∧ tlen_v = BitVec.ofNat 32 tlen ∧
      st.d_cur = cnf_ptr + BitVec.ofNat 64 idx ∧
      IngestReadInv c s cnfBytes.length i0 idx tlen taut_v revLits st ∧
      parseClauseAux ((cnfBytes.drop idx).length + 1) c.mv
        (revLits.map kissatLitToDimacsLiteral) (cnfBytes.drop idx) =
        parseClause c.mv (cnfBytes.drop i0) ∧
      (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c st ⋆ R) ml) ?_ ?_
  · rintro L1 r ⟨tlen_v, taut_v, ⟨⟩⟩ ml ih1
      ⟨idx, tlen, revLits, st, rfl, rfl, hdcur_st, hri, hpc_inv, hml⟩
    clear hJ; cp_steps
    · c0_call hLit
      refine ⟨cnf_ptr, BitVec.ofNat 64 c.nc, st.d_val, c.mv, cnfBytes, idx,
        CorePlusRest c st ⋆ R, rfl, hfit, by omega, hri.idx_le,
        by rw [← hdcur_st]; exact cp_mem_to_dimacs hml, ?_⟩
      cases hnl : nextLitPure c.mv (cnfBytes.drop idx) with
      | err =>
        intro cur' val' m' hm'; cp_steps
        · exact hBrk (BitVec.ofNat 32 tlen) taut_v true m'
            ⟨idx, tlen, revLits, { st with d_cur := cur', d_val := val' }, rfl,
              ingest_read_inv_with_d hri hri.idx_ge hri.idx_le,
              (fun _ => by rw [← hpc_inv, parseClauseAux_eq_nextLitPure, hnl]),
              (fun hc => by cases hc), cp_dimacs_to_mem hm'⟩
        · exact absurd rfl (by assumption : ¬(0#64 : BitVec 64) = 0)
      | endClause rest =>
        intro j m' hij hj hdrop hm'; cp_steps
        · exact hBrk (BitVec.ofNat 32 tlen) taut_v false m'
            ⟨j, tlen, revLits, { st with d_cur := cnf_ptr + BitVec.ofNat 64 j, d_val := 0#64 },
              rfl, ingest_read_inv_with_d hri (by have := hri.idx_ge; omega) hj,
              (fun hc => by cases hc),
              fun _ => ⟨by have := hri.idx_ge; omega, rfl, by
                rw [← hpc_inv, parseClauseAux_eq_nextLitPure, hnl, List.map_reverse, hdrop]⟩,
              cp_dimacs_to_mem hm'⟩
        · exact absurd rfl (by assumption : ¬(1#64 : BitVec 64) = 1)
      | lit l rest =>
        intro j m' hl_mv hl_bd hij hj hdrop hm'
        let st' : CorePlusState :=
          { st with d_cur := cnf_ptr + BitVec.ofNat 64 j, d_val := BitVec.ofNat 64 l }
        have hm'_mem := cp_dimacs_to_mem hm'
        have hl32 : l < 2 ^ 32 := by omega
        have hl64 : l < 2 ^ 64 := by omega
        have hl_idx : l % 2 ^ 64 % 2 ^ 32 / 2 ^ 1 = l / 2 := by omega
        have hv_lt : l / 2 < c.mv := by omega
        have hpc_next : parseClauseAux ((cnfBytes.drop j).length + 1) c.mv
            ((l :: revLits).map kissatLitToDimacsLiteral) (cnfBytes.drop j) =
            parseClause c.mv (cnfBytes.drop i0) := by
          have hstep :
              parseClauseAux ((cnfBytes.drop idx).length + 1) c.mv
                (revLits.map kissatLitToDimacsLiteral) (cnfBytes.drop idx) =
              parseClauseAux (cnfBytes.drop idx).length c.mv
                ((l :: revLits).map kissatLitToDimacsLiteral) (cnfBytes.drop j) := by
            rw [parseClauseAux_eq_nextLitPure, hnl, ← hdrop]; rfl
          rw [← hpc_inv, hstep]
          exact parseClauseAux_fuel_irrel (by simp only [List.length_drop]; omega)
            (by simp only [List.length_drop]; omega)
        have hmkl := hri.mrk_len; have htmpl := hri.tmp_len
        have hptag32 :
            ((BitVec.setWidth 32 (BitVec.ofNat 64 l) &&& (1 : BitVec 32)) + 1).setWidth 8 =
            BitVec.ofNat 8 (l % 2 + 1) := by
          rw [bv64_setWidth32_ofNat]; apply BitVec.eq_of_toNat_eq
          simp [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_and,
            Nat.and_one_is_mod, Nat.mod_eq_of_lt hl32]
        cp_steps
        · exfalso
          have hm0_w : (st.mrk[l / 2]'(by omega)).setWidth 32 = 0#32 := by
            simpa only [hl_idx] using
              (by assumption : BitVec.setWidth 32 st.mrk[l % 2 ^ 64 % 2 ^ 32 / 2 ^ 1] = 0#32)
          have htlt := (ingest_tlen_lt_of_zero hri hl_mv ((bv8_setWidth32_eq_iff _ 0#8).mp hm0_w)).2
          have htge : c.mv ≤ tlen % 2 ^ 32 := by assumption
          have htmod : tlen % 2 ^ 32 = tlen := Nat.mod_eq_of_lt (by omega)
          omega
        · have hm0_w : (st.mrk[l / 2]'(by omega)).setWidth 32 = 0#32 := by
            simpa only [hl_idx] using
              (by assumption : BitVec.setWidth 32 st.mrk[l % 2 ^ 64 % 2 ^ 32 / 2 ^ 1] = 0#32)
          obtain ⟨hmiss_v, htlen_lt⟩ :=
            ingest_tlen_lt_of_zero hri hl_mv ((bv8_setWidth32_eq_iff _ 0#8).mp hm0_w)
          have htr32 : BitVec.setWidth 32 (BitVec.ofNat 64 l) = BitVec.ofNat 32 l :=
            bv64_setWidth32_ofNat l
          have hr_idx1 : (BitVec.setWidth 64 (BitVec.ofNat 32 l >>> 1)).toNat = l / 2 := by
            clear hm hml hQ; simp only [bv_c0]; omega
          have hr_idx2 : (BitVec.setWidth 64 (BitVec.ofNat 32 tlen)).toNat = tlen := by
            clear hm hml hQ; simp only [bv_c0]; omega
          have htl_inc : BitVec.ofNat 32 tlen + (1 : BitVec 32) = BitVec.ofNat 32 (tlen + 1) := by
            apply BitVec.eq_of_toNat_eq
            change (tlen % 2 ^ 32 + 1) % 2 ^ 32 = (tlen + 1) % 2 ^ 32; omega
          exact ih1 (cnfBytes.length - j) _ _ (by omega)
            ⟨j, tlen + 1, l :: revLits, _, rfl, htl_inc, rfl,
              ingest_read_new_inv hri hij hj hl_mv hl32 hmiss_v htlen_lt
                (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 l), hpc_next, by
              rw [hptag32, htr32, hr_idx1, hr_idx2] at hm; exact sep_ac hm⟩
        · exact ih1 (cnfBytes.length - j) _ _ (by omega)
            ⟨j, tlen, l :: revLits, st', rfl, rfl, rfl,
              ingest_dup_step hri hij hj hl_mv hl_idx hptag32 (by assumption)
                (Or.inl ⟨rfl, by assumption⟩), hpc_next, hm'_mem⟩
        · exact ih1 (cnfBytes.length - j) _ _ (by omega)
            ⟨j, tlen, l :: revLits, st', rfl, rfl, rfl,
              ingest_dup_step hri hij hj hl_mv hl_idx hptag32 (by assumption)
                (Or.inr ⟨rfl, by assumption⟩), hpc_next, hm'_mem⟩
    · cases (by assumption : true = false)
  · intro L1 hL1; cp_steps
    exact hL1 (cnfBytes.length - i0) _ m
      ⟨i0, 0, [], s, rfl, rfl, hdcur,
        ⟨Nat.le_refl _, hi0, Nat.zero_le _, rfl, hlen.mrk_len, hlen.tmp_len_arr,
          (fun _ h => by cases h), (fun _ _ h => by cases h), (fun v hv _ => hinv.marks v hv),
          (fun _ h => by cases h), (fun _ _ h => by cases h), (fun _ h => by cases h),
          (fun _ => rfl), (fun _ h => by cases h)⟩, rfl, hm⟩

/-! ## 4. Helpers and `kissat_parse_body_wp` -/

private structure ParseBodyInv (c : CorePlusCfg) (s : CorePlusState) (cnf_ptr : BitVec 64)
    (cnfBytes : List UInt8) (i0 i idx : Nat) (accCnf : CNF Nat) (unsat oom : Bool)
    (st : CorePlusState) : Prop where
  i_le : i ≤ c.nc
  idx_le : idx ≤ cnfBytes.length
  d_cur_eq : st.d_cur = cnf_ptr + BitVec.ofNat 64 idx
  len_ok : st.LengthsOk c
  cl0 : st.cur_level = 0
  fuel_eq : st.fuel = s.fuel
  rt_eq : st.heur.rel_trigger = s.heur.rel_trigger
  vars_pos : CnfVarsPos accCnf
  pc_eq : parseClauses c.mv (c.nc - i) accCnf (cnfBytes.drop idx) = parseDimacs cnfBytes
  uns_inv : unsat = true → (shiftDownCnf accCnf).Unsat
  ok_inv : unsat = false → oom = false → CorePlusInv c (shiftDownCnf accCnf) st
  sat_tr : ∀ vals' te', UnitSatTrace c.mv s.vals 0 (cnfBytes.drop i0) c.nc vals' te' →
    unsat = false ∧ oom = false ∧ st.propagated = 0 ∧ st.num_clauses = 0 ∧ st.wh = s.wh ∧
    UnitSatTrace c.mv st.vals st.trail_end (cnfBytes.drop idx) (c.nc - i) vals' te'
  uns_tr : UnitUnsatTrace c.mv s.vals (cnfBytes.drop i0) c.nc →
    oom = false ∧
    ((unsat = false ∧ UnitUnsatTrace c.mv st.vals (cnfBytes.drop idx) (c.nc - i)) ∨
     (unsat = true ∧ ∃ cnf, parseClauses c.mv (c.nc - i) CNF.empty (cnfBytes.drop idx) = some cnf))

private theorem parse_body_skip_step {c : CorePlusCfg} {s st st' : CorePlusState}
    {cnf_ptr : BitVec 64} {cnfBytes rest : List UInt8} {i0 i idx j : Nat} {accCnf : CNF Nat}
    {oom : Bool} {cl : CNF.Clause Nat}
    (hp : ParseBodyInv c s cnf_ptr cnfBytes i0 i idx accCnf true oom st)
    (hi : i < c.nc) (hpc1 : parseClause c.mv (cnfBytes.drop idx) = some (cl, rest))
    (hcl_pos : ∀ lit ∈ cl.literals, 1 ≤ lit.1) (hj : j ≤ cnfBytes.length)
    (hdrop : cnfBytes.drop j = rest)
    (hst' : st' = { st with d_cur := cnf_ptr + BitVec.ofNat 64 j, d_val := 0#64 }) :
    ParseBodyInv c s cnf_ptr cnfBytes i0 (i + 1) j (accCnf.add cl) true oom st' := by
  have hsub : c.nc - i = (c.nc - (i + 1)) + 1 := by omega
  refine ⟨by omega, hj, by rw [hst'],
    by rw [hst']; exact { hp.len_ok with vals_len := hp.len_ok.vals_len },
    by rw [hst']; exact hp.cl0, by rw [hst']; exact hp.fuel_eq, by rw [hst']; exact hp.rt_eq,
    cnfVarsPos_add hp.vars_pos hcl_pos,
    by rw [← hp.pc_eq, hsub, parseClauses, hpc1, ← hdrop]; rfl,
    (fun _ => by rw [shiftDownCnf_add]; exact cnf_unsat_add (hp.uns_inv rfl)),
    (fun hc => by cases hc),
    (fun vals' te' hst => by have h1 := (hp.sat_tr vals' te' hst).1; cases h1),
    (fun hut => by
      obtain ⟨hoom, hdisj⟩ := hp.uns_tr hut
      refine ⟨hoom, Or.inr ⟨rfl, ?_⟩⟩
      rcases hdisj with ⟨hf, _⟩ | ⟨_, cnf_r, hr⟩
      · cases hf
      · rw [hsub, parseClauses, hpc1, ← hdrop] at hr; exact parseClauses_some_of_acc hr)⟩

private theorem parse_body_ingest_step {c : CorePlusCfg} {s st st' : CorePlusState}
    {cnf_ptr : BitVec 64} {cnfBytes rest : List UInt8} {i0 i idx j : Nat} {accCnf : CNF Nat}
    {r_in : BitVec 64} {cl : CNF.Clause Nat}
    (hp : ParseBodyInv c s cnf_ptr cnfBytes i0 i idx accCnf false false st)
    (hi : i < c.nc) (hpc1 : parseClause c.mv (cnfBytes.drop idx) = some (cl, rest))
    (hcl_pos : ∀ lit ∈ cl.literals, 1 ≤ lit.1) (hj : j ≤ cnfBytes.length)
    (hdrop : cnfBytes.drop j = rest) (hlen' : st'.LengthsOk c)
    (hd' : st'.d_cur = cnf_ptr + BitVec.ofNat 64 j) (hcl' : st'.cur_level = 0)
    (hfu' : st'.fuel = st.fuel) (hrt' : st'.heur.rel_trigger = st.heur.rel_trigger)
    (hr_dom : r_in = 1#64 ∨ r_in = 2#64 ∨ r_in = 3#64)
    (hok_in : r_in = 1#64 → CorePlusInv c (shiftDownCnf (accCnf.add cl)) st')
    (huns_in : r_in = 2#64 → (shiftDownCnf (accCnf.add cl)).Unsat)
    (hunit_ok : ∀ l < 2 * c.mv, cl = CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l] →
      st.vals[l]?.getD 0#8 = 0#8 → r_in = 1#64 ∧
      st'.vals = (st.vals.set l 1#8).set (l ^^^ 1) 0xFF#8 ∧ st'.trail_end = st.trail_end + 1 ∧
      st'.propagated = st.propagated ∧ st'.num_clauses = st.num_clauses ∧ st'.wh = st.wh)
    (hunit_fl : ∀ l < 2 * c.mv, cl = CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l] →
      st.vals[l]?.getD 0#8 = 0xFF#8 → r_in = 2#64) :
    ParseBodyInv c s cnf_ptr cnfBytes i0 (i + 1) j (accCnf.add cl)
      (decide (r_in = 2#64)) (decide (r_in = 3#64)) st' := by
  have hsub : c.nc - i = (c.nc - (i + 1)) + 1 := by omega
  have hpc_next : parseClauses c.mv (c.nc - (i + 1)) (accCnf.add cl) (cnfBytes.drop j) =
      parseDimacs cnfBytes := by rw [← hp.pc_eq, hsub, parseClauses, hpc1, ← hdrop]; rfl
  rcases hr_dom with rfl | rfl | rfl <;>
    refine ⟨by omega, hj, hd', hlen', hcl', hfu'.trans hp.fuel_eq, hrt'.trans hp.rt_eq,
      cnfVarsPos_add hp.vars_pos hcl_pos, hpc_next, ?_, ?_, ?_, ?_⟩
  · exact fun hc => by cases hc
  · exact fun _ _ => hok_in rfl
  · intro vals' te' hst
    obtain ⟨_, _, hpr_z, hnc_z, hwh_z, htr⟩ := hp.sat_tr vals' te' hst
    rw [hsub] at htr; cases htr with
    | step hl hpc_s hv0 htr_next =>
      rw [hpc1] at hpc_s; rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, hreq⟩
      obtain ⟨_, hvs, htes, hprs, hncs, hwhs⟩ := hunit_ok _ hl hcl_eq hv0
      refine ⟨rfl, rfl, by rw [hprs, hpr_z], by rw [hncs, hnc_z], by rw [hwhs, hwh_z], ?_⟩
      rw [hvs, htes, hdrop, hreq]; exact htr_next
  · intro hut; refine ⟨rfl, Or.inl ⟨rfl, ?_⟩⟩
    rcases (hp.uns_tr hut).2 with ⟨_, htr⟩ | ⟨ht, _⟩
    · rw [hsub] at htr; cases htr with
      | conflict hl hpc_s hvf _ =>
        rw [hpc1] at hpc_s; rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
        have hr2 := hunit_fl _ hl hcl_eq hvf; cases hr2
      | step hl hpc_s hv0 htr_next =>
        rw [hpc1] at hpc_s; rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, hreq⟩
        obtain ⟨_, hvs, _, _, _, _⟩ := hunit_ok _ hl hcl_eq hv0
        rw [hvs, hdrop, hreq]; exact htr_next
    · cases ht
  · exact fun _ => huns_in rfl
  · exact fun hc => by cases hc
  · intro vals' te' hst; have htr := (hp.sat_tr vals' te' hst).2.2.2.2.2; rw [hsub] at htr
    cases htr with | step hl hpc_s hv0 _ =>
      rw [hpc1] at hpc_s; rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
      exact absurd (hunit_ok _ hl hcl_eq hv0).1 (by decide)
  · intro hut; refine ⟨rfl, Or.inr ⟨rfl, ?_⟩⟩
    rcases (hp.uns_tr hut).2 with ⟨_, htr⟩ | ⟨ht, _⟩
    · rw [hsub] at htr; cases htr with
      | conflict _ hpc_s _ hrest =>
        rw [hpc1] at hpc_s; rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨_, hreq⟩
        rwa [hdrop, hreq]
      | step hl hpc_s hv0 _ =>
        rw [hpc1] at hpc_s; rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
        exact absurd (hunit_ok _ hl hcl_eq hv0).1 (by decide)
    · cases ht
  · exact fun hc => by cases hc
  · exact fun _ hc => by cases hc
  · intro vals' te' hst; have htr := (hp.sat_tr vals' te' hst).2.2.2.2.2; rw [hsub] at htr
    cases htr with | step hl hpc_s hv0 _ =>
      rw [hpc1] at hpc_s; rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
      exact absurd (hunit_ok _ hl hcl_eq hv0).1 (by decide)
  · intro hut; rcases (hp.uns_tr hut).2 with ⟨_, htr⟩ | ⟨ht, _⟩
    · rw [hsub] at htr; cases htr with
      | conflict hl hpc_s hvf _ =>
        rw [hpc1] at hpc_s; rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
        exact absurd (hunit_fl _ hl hcl_eq hvf) (by decide)
      | step hl hpc_s hv0 _ =>
        rw [hpc1] at hpc_s; rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
        exact absurd (hunit_ok _ hl hcl_eq hv0).1 (by decide)
    · cases ht

private abbrev ParseBodyPost (c : CorePlusCfg) (s : CorePlusState) (cnf_ptr : BitVec 64)
    (cnfBytes : List UInt8) (i0 : Nat) (R : Mem 64 → Prop) (Q : Post [i64]) : Prop :=
  ∀ r st' m', st'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → st'.fuel = s.fuel →
    st'.heur.rel_trigger = s.heur.rel_trigger →
    (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ CNF.Unsat cnf) →
    (r = 1#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ CorePlusInv c (shiftDownCnf cnf) st' ∧
      st'.cur_level = 0) →
    (∀ vals' te', UnitSatTrace c.mv s.vals 0 (cnfBytes.drop i0) c.nc vals' te' →
      r = 1#64 ∧ st'.vals = vals' ∧ st'.trail_end = te' ∧
      st'.propagated = 0 ∧ st'.num_clauses = 0 ∧ st'.wh = s.wh) →
    (UnitUnsatTrace c.mv s.vals (cnfBytes.drop i0) c.nc → r = 20#64) →
    (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c st' ⋆ R) m' → Q (r, ()) m'

private theorem parse_body_oom_exit {c : CorePlusCfg} {s st : CorePlusState}
    {cnf_ptr : BitVec 64} {cnfBytes : List UInt8} {i0 i idx : Nat} {accCnf : CNF Nat}
    {unsat_v : Bool} {R : Mem 64 → Prop} {ml : Mem 64} {Q : Post [i64]}
    (hp : ParseBodyInv c s cnf_ptr cnfBytes i0 i idx accCnf unsat_v true st)
    (hml : (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c st ⋆ R) ml)
    (hQ : ParseBodyPost c s cnf_ptr cnfBytes i0 R Q) : Q (0#64, ()) ml :=
  hQ 0#64 st ml hp.len_ok (Or.inl rfl) hp.fuel_eq hp.rt_eq (fun h => by cases h)
    (fun h => by cases h) (fun vals' te' hst => by cases (hp.sat_tr vals' te' hst).2.1)
    (fun hut => by cases (hp.uns_tr hut).1) hml

private theorem parse_body_eof_ne {c : CorePlusCfg} {s st : CorePlusState}
    {cnf_ptr : BitVec 64} {cnfBytes : List UInt8} {i0 idx j : Nat} {accCnf : CNF Nat}
    {unsat_v oom_v : Bool} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hp : ParseBodyInv c s cnf_ptr cnfBytes i0 c.nc idx accCnf unsat_v oom_v st)
    (_hidx : idx ≤ cnfBytes.length) (hj : j ≤ cnfBytes.length)
    (hsw : cnfBytes.drop j = skipWsComments (cnfBytes.drop idx))
    (hne : cnf_ptr + BitVec.ofNat 64 j ≠ cnf_ptr + BitVec.ofNat 64 cnfBytes.length)
    (hfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c { st with d_cur := cnf_ptr + BitVec.ofNat 64 j }
      ⋆ R) m')
    (hQ : ParseBodyPost c s cnf_ptr cnfBytes i0 R Q) : Q (0#64, ()) m' := by
  have hj_lt : j < cnfBytes.length := by
    have hj_ne : j ≠ cnfBytes.length := fun heq =>
      hne ((cursor_eq_iff (base := cnf_ptr) (by omega) (by omega)).mpr heq)
    omega
  have hne_emp : (skipWsComments (cnfBytes.drop idx)).isEmpty = false := by
    rw [← hsw, List.drop_eq_getElem_cons hj_lt]; rfl
  exact hQ 0#64 { st with d_cur := cnf_ptr + BitVec.ofNat 64 j } m'
    { hp.len_ok with vals_len := hp.len_ok.vals_len } (Or.inl rfl) hp.fuel_eq hp.rt_eq
    (fun h => by cases h) (fun h => by cases h)
    (fun vals' te' hst => by
      have htr := (hp.sat_tr vals' te' hst).2.2.2.2.2; rw [Nat.sub_self] at htr
      cases htr with | done hemp => rw [hne_emp] at hemp; cases hemp)
    (fun hut => by
      rcases (hp.uns_tr hut).2 with ⟨_, htr⟩ | ⟨_, _, hr⟩
      · rw [Nat.sub_self] at htr; cases htr
      · rw [Nat.sub_self] at hr
        simp only [parseClauses, hne_emp, Bool.false_eq_true, ↓reduceIte] at hr; cases hr) hm

private theorem parse_body_eof_done {c : CorePlusCfg} {s st : CorePlusState}
    {cnf_ptr : BitVec 64} {cnfBytes : List UInt8} {i0 idx j : Nat} {accCnf : CNF Nat}
    {unsat_v oom_v : Bool} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hp : ParseBodyInv c s cnf_ptr cnfBytes i0 c.nc idx accCnf unsat_v oom_v st)
    (_hidx : idx ≤ cnfBytes.length) (hj : j ≤ cnfBytes.length)
    (hsw : cnfBytes.drop j = skipWsComments (cnfBytes.drop idx))
    (heq : cnf_ptr + BitVec.ofNat 64 j = cnf_ptr + BitVec.ofNat 64 cnfBytes.length)
    (hfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c { st with d_cur := cnf_ptr + BitVec.ofNat 64 j }
      ⋆ R) m')
    (hQ : ParseBodyPost c s cnf_ptr cnfBytes i0 R Q)
    (hret : (unsat_v = true ∧ cnf_ptr = cnf_ptr) ∨ (unsat_v = false ∧ oom_v = false)) :
    Q (if unsat_v then 20#64 else 1#64, ()) m' := by
  have hj_len : j = cnfBytes.length := (cursor_eq_iff (by omega) (by omega)).mp heq
  have hemp : (skipWsComments (cnfBytes.drop idx)).isEmpty = true := by
    rw [← hsw, hj_len, List.drop_length]; rfl
  have hpc_eq := hp.pc_eq; simp only [Nat.sub_self, parseClauses] at hpc_eq
  have hpd_some : parseDimacs cnfBytes = some accCnf := by rw [← hpc_eq]; simp [hemp]
  let sf : CorePlusState := { st with d_cur := cnf_ptr + BitVec.ofNat 64 j }
  have hlen_sf : sf.LengthsOk c := { hp.len_ok with vals_len := hp.len_ok.vals_len }
  rcases hret with ⟨hunt, _⟩ | ⟨huf, hnf⟩
  · subst hunt
    exact hQ 20#64 sf m' hlen_sf (Or.inr (Or.inr rfl)) hp.fuel_eq hp.rt_eq
      (fun _ => ⟨accCnf, hpd_some, shiftDownCnf_unsat hp.vars_pos (hp.uns_inv rfl)⟩)
      (fun h => by cases h)
      (fun vals' te' hst => by cases (hp.sat_tr vals' te' hst).1) (fun _ => rfl) hm
  · subst huf hnf
    have hinv_sf := (hp.ok_inv rfl rfl).with_d (cnf_ptr + BitVec.ofNat 64 j) st.d_val
    exact hQ 1#64 sf m' hlen_sf (Or.inr (Or.inl rfl)) hp.fuel_eq hp.rt_eq (fun h => by cases h)
      (fun _ => ⟨accCnf, hpd_some, hinv_sf, hp.cl0⟩)
      (fun vals' te' hst => by
        obtain ⟨_, _, hpr_z, hnc_z, hwh_z, htr⟩ := hp.sat_tr vals' te' hst
        rw [Nat.sub_self] at htr
        cases htr with | done _ => exact ⟨rfl, rfl, rfl, hpr_z, hnc_z, hwh_z⟩)
      (fun hut => by
        rcases (hp.uns_tr hut).2 with ⟨_, htr⟩ | ⟨ht, _⟩
        · rw [Nat.sub_self] at htr; cases htr
        · cases ht) hm

theorem kissat_parse_body_wp (Γ : Env)
    (hSkip : ∀ a m Q X, corePlusSkipClauseSyntaxSpec a m Q X →
      Γ "kissat_skip_clause_syntax" [i64, i64] [.bool] a m Q X)
    (hIngest : ∀ a m Q X, corePlusIngestClauseSpec a m Q X →
      Γ "kissat_ingest_clause" [i64, i64] [i64] a m Q X)
    (hSwc : ∀ a m Q X, kissatSkipWsCommentsSpec a m Q X →
      Γ "kissat_skip_ws_comments" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, corePlusParseBodySpec a m Q X → Func.wp Γ kissat_parse_body_body a m Q X := by
  rintro ⟨h, cend, ⟨⟩⟩ m Q X
    ⟨c, s, cnf_ptr, cnfBytes, i0, R, rfl, rfl, hfit, hi0, hhdr, hdcur, hcl0, hte0, hpr0, hnc0,
      hinv0, hm, hQ⟩
  have hnc_bd := c.hnc; have hmv_bd := c.hmv; unfold dimacsBound at hnc_bd hmv_bd
  have hpd_init : parseClauses c.mv c.nc CNF.empty (cnfBytes.drop i0) = parseDimacs cnfBytes := by
    simp [parseDimacs, hhdr]
  cp_steps
  refine wp_loop_group
    (fun r (unsat_v, oom_v, iv, ()) ml => ∃ i idx accCnf st,
      r = c.nc - i ∧ iv = BitVec.ofNat 64 i ∧ ParseBodyInv c s cnf_ptr cnfBytes i0 i idx accCnf
        unsat_v oom_v st ∧ (bytes cnf_ptr cnfBytes ⋆ CorePlusMem c st ⋆ R) ml) ?_ ?_
  · rintro L r ⟨unsat_v, oom_v, iv, ⟨⟩⟩ ml ih ⟨i, idx, accCnf, st, rfl, rfl, hp, hml⟩
    have hile := hp.i_le; have hidx := hp.idx_le; have hdcur_st := hp.d_cur_eq
    have hlen_st := hp.len_ok; have hcl_st := hp.cl0; have hfu_st := hp.fuel_eq
    have hrt_st := hp.rt_eq
    cp_steps
    · have hilt : i < c.nc := by clear hm hml hQ; c0_bound
      have hunt : unsat_v = true := by assumption
      subst hunt
      have hsub_eq : c.nc - i = (c.nc - (i + 1)) + 1 := by omega
      have hinc : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := by
        apply BitVec.eq_of_toNat_eq; change (i % 2 ^ 64 + 1) % 2 ^ 64 = (i + 1) % 2 ^ 64; omega
      c0_call hSkip
      refine ⟨cnf_ptr, BitVec.ofNat 64 c.nc, st.d_val, c.mv, cnfBytes, idx,
        CorePlusRest c st ⋆ R, rfl, hfit, by omega, hidx,
        by rw [← hdcur_st]; exact cp_mem_to_dimacs hml, ?_⟩
      cases hpc1 : parseClause c.mv (cnfBytes.drop idx) with
      | none =>
        intro cur' val' m' hm'; cp_steps
        · exact False.elim (Bool.false_ne_true (by assumption))
        · exact hQ 0#64 { st with d_cur := cur', d_val := val' } m'
            { hlen_st with vals_len := hlen_st.vals_len } (Or.inl rfl) hfu_st hrt_st
            (fun h => by cases h) (fun h => by cases h)
            (fun vals' te' hst => by cases (hp.sat_tr vals' te' hst).1)
            (fun hut => by
              rcases (hp.uns_tr hut).2 with ⟨hf, _⟩ | ⟨_, cnf_r, hr⟩
              · cases hf
              · rw [hsub_eq, parseClauses, hpc1] at hr; cases hr) (cp_dimacs_to_mem hm')
      | some p =>
        rcases p with ⟨cl, rest⟩; intro j m' hcl_pos _ hj hdrop hm'; cp_steps
        · exact ih (c.nc - (i + 1)) _ _ (by omega)
            ⟨i + 1, j, accCnf.add cl, _, rfl, hinc,
              parse_body_skip_step hp hilt hpc1 hcl_pos hj hdrop rfl, cp_dimacs_to_mem hm'⟩
        · cases (by assumption : true = false)
    · have hoo : oom_v = true := by assumption
      subst hoo; exact parse_body_oom_exit hp hml hQ
    · have hilt : i < c.nc := by clear hm hml hQ; c0_bound
      have huf : unsat_v = false := by assumption
      have hnf : oom_v = false := by assumption
      subst huf hnf
      have hsub_eq : c.nc - i = (c.nc - (i + 1)) + 1 := by omega
      have hinc : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := by
        apply BitVec.eq_of_toNat_eq; change (i % 2 ^ 64 + 1) % 2 ^ 64 = (i + 1) % 2 ^ 64; omega
      c0_call hIngest
      refine ⟨c, accCnf, st, cnf_ptr, cnfBytes, idx, R, rfl, rfl, hfit, hidx, hdcur_st,
        hcl_st, hp.ok_inv rfl rfl, hml, ?_⟩
      cases hpc1 : parseClause c.mv (cnfBytes.drop idx) with
      | none =>
        intro st' m' hlen' hfu' hrt' hm'; cp_steps
        · exact hQ 0#64 st' m' hlen' (Or.inl rfl) (hfu'.trans hfu_st) (hrt'.trans hrt_st)
            (fun h => by cases h) (fun h => by cases h)
            (fun vals' te' hst => by
              have htr := (hp.sat_tr vals' te' hst).2.2.2.2.2; rw [hsub_eq] at htr
              cases htr with | step _ hpc_s _ _ => rw [hpc1] at hpc_s; cases hpc_s)
            (fun hut => by
              rcases (hp.uns_tr hut).2 with ⟨_, htr⟩ | ⟨ht, _⟩
              · rw [hsub_eq] at htr
                cases htr with
                | conflict _ hpc_s _ _ => rw [hpc1] at hpc_s; cases hpc_s
                | step _ hpc_s _ _ => rw [hpc1] at hpc_s; cases hpc_s
              · cases ht) hm'
        · exact absurd rfl (by assumption : ¬(0#64 : BitVec 64) = 0)
      | some p =>
        rcases p with ⟨cl, rest⟩
        intro r_in st' j m' hcl_pos _ hj hdrop hlen' hd' hcl' hfu' hrt' hr_dom
          hok_in huns_in hunit_ok hunit_fl hm'
        rcases hr_dom with rfl | rfl | rfl <;> cp_steps <;>
          first
          | (exact absurd rfl (by assumption : ¬(2#64 : BitVec 64) = 2))
          | (exact absurd rfl (by assumption : ¬(3#64 : BitVec 64) = 3))
          | exact ih (c.nc - (i + 1)) _ _ (by omega)
              ⟨i + 1, j, accCnf.add cl, st', rfl, hinc, by
                simpa using parse_body_ingest_step hp hilt hpc1 hcl_pos hj hdrop hlen'
                  hd' hcl' hfu' hrt' (by simp) hok_in huns_in hunit_ok hunit_fl, hm'⟩
    · have hoo : oom_v = true := by assumption
      subst hoo; exact parse_body_oom_exit hp hml hQ
    · have hieq : i = c.nc := by clear hml hQ; c0_bound
      subst hieq
      c0_call hSwc
      refine ⟨cnf_ptr, cnfBytes, idx, CorePlusMem c st ⋆ R, hdcur_st, rfl, hfit, hidx,
        sep_ac hml, fun j _ hj hsw => ?_⟩
      cp_steps
      · exact parse_body_eof_ne hp hidx hj hsw (by assumption) hfit (sep_ac hm) hQ
      · have hunt : unsat_v = true := by assumption
        simpa [hunt] using parse_body_eof_done hp hidx hj hsw (by assumption) hfit (sep_ac hm) hQ
          (Or.inl ⟨hunt, rfl⟩)
      · have huf : unsat_v = false := by assumption
        have hnf : oom_v = false := by assumption
        simpa [huf] using parse_body_eof_done hp hidx hj hsw (by assumption) hfit (sep_ac hm) hQ
          (Or.inr ⟨huf, hnf⟩)
  · intro L hL; cp_steps
    exact hL c.nc _ m ⟨0, i0, CNF.empty, s, by simp, rfl,
      ⟨Nat.zero_le _, hi0, hdcur, hinv0.core.lengths, hcl0, rfl, rfl, cnfVarsPos_empty,
        by simpa using hpd_init, (fun hc => by cases hc), fun _ _ => hinv0,
        fun vals' te' hst => ⟨rfl, rfl, hpr0, hnc0, rfl, by simpa [hte0] using hst⟩,
        fun hut => ⟨rfl, Or.inl ⟨rfl, by simpa using hut⟩⟩⟩, hm⟩

end LeanQbe.T.Examples.Kissat.CorePlus
