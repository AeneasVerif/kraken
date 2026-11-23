module

public import LeanQbe.T.Examples.Kissat.SolverIngestLemmas1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Soundness Proofs for Kissat `D-Min` C0 Clause Ingestion & Body Parsing (Part 2)

Proves `Func.wp` specifications for:
1. `kissat_ingest_clause` (`kissatIngestClauseSpec`, `kissat_ingest_clause_wp`)
2. `kissat_parse_body` (`kissatParseBodySpec`, `kissat_parse_body_wp`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open Kraken.Bedrock2.Test

/-! ## 4. `kissat_ingest_clause` specification and `Func.wp` proof -/

/-- Specification of `kissat_ingest_clause(h, cnf_end)`. -/
def kissatIngestClauseSpec : Spec [i64, i64] [i64] := fun (h, cend, ()) m Q _ =>
  ∃ (c : ArenaCfg) (accCnf : CNF Nat) (s : ArenaState) (cnf_ptr : BitVec 64)
    (cnfBytes : List UInt8) (i0 : Nat) (R : Mem 64 → Prop),
    h = c.hdr ∧ cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
    i0 ≤ cnfBytes.length ∧
    s.d_cur = cnf_ptr + BitVec.ofNat 64 i0 ∧
    s.cur_level = 0 ∧
    SolverInv c (shiftDownCnf accCnf) s ∧
    (bytes cnf_ptr cnfBytes ⋆ ArenaMem c s ⋆ R) m ∧
    match parseClause c.mv (cnfBytes.drop i0) with
    | none =>
      ∀ s' m', s'.LengthsOk c → s'.fuel = s.fuel →
        (bytes cnf_ptr cnfBytes ⋆ ArenaMem c s' ⋆ R) m' →
        Q (0#64, ()) m'
    | some (cl, rest) =>
      ∀ r s' j m',
        (∀ lit ∈ cl.literals, 1 ≤ lit.1) →
        i0 < j → j ≤ cnfBytes.length → cnfBytes.drop j = rest →
        s'.LengthsOk c → s'.d_cur = cnf_ptr + BitVec.ofNat 64 j →
        s'.cur_level = 0 → s'.fuel = s.fuel →
        (r = 1#64 ∨ r = 2#64 ∨ r = 3#64) →
        (r = 1#64 → SolverInv c (shiftDownCnf (accCnf.add cl)) s') →
        (r = 2#64 → (shiftDownCnf (accCnf.add cl)).Unsat) →
        (∀ l < 2 * c.mv, cl = CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l] →
          s.vals[l]?.getD 0#8 = 0#8 →
          r = 1#64 ∧ s'.vals = (s.vals.set l 1#8).set (l ^^^ 1) 0xFF#8 ∧
          s'.trail_end = s.trail_end + 1 ∧ s'.propagated = s.propagated ∧
          s'.num_clauses = s.num_clauses ∧ s'.wh = s.wh) →
        (∀ l < 2 * c.mv, cl = CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l] →
          s.vals[l]?.getD 0#8 = 0xFF#8 → r = 2#64) →
        (bytes cnf_ptr cnfBytes ⋆ ArenaMem c s' ⋆ R) m' →
        Q (r, ()) m'

theorem kissat_ingest_clause_wp (Γ : Env)
    (hLit : ∀ args m Q X, kissatNextLitSpec args m Q X →
      Γ "kissat_next_lit" [i64, i64] [i64] args m Q X)
    (hAssign : ∀ args m Q X, kissatAssignSpec args m Q X →
      Γ "kissat_assign" [i64, i32, i32] [] args m Q X)
    (hAddCl : ∀ args m Q X, kissatAddClauseSpec args m Q X →
      Γ "kissat_add_clause" [i64, i32] [i64] args m Q X) :
    ∀ args m Q X, kissatIngestClauseSpec args m Q X →
      Func.wp Γ kissat_ingest_clause_body args m Q X := by
  rintro ⟨h, cend, ⟨⟩⟩ m Q X
    ⟨c, accCnf, s, cnf_ptr, cnfBytes, i0, R, rfl, rfl, hfit, hi0, hdcur, hcl0, hinv, hm, hQ⟩
  unfold Func.wp kissat_ingest_clause_body; wp_unfold
  have hcore := hinv.core
  have hlen := hcore.lengths
  have hmv := c.hmv; unfold dimacsBound at hmv
  have hm_a : (ArenaMem c s ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m := sep_ac hm
  refine ⟨_, load_arena_tmp_lits hm_a, _, load_arena_mark hm_a, _, load_arena_values hm_a, ?_⟩
  -- Invariant for Loop 1 (reading literals + dedup + tautology mark)
  let ReadInv (idx tlen : Nat) (taut err : Bool) (revLits : List Nat) (st : ArenaState) : Prop :=
    i0 ≤ idx ∧ idx ≤ cnfBytes.length ∧ tlen ≤ c.mv ∧
    st.lit_len = s.lit_len ∧ st.num_clauses = s.num_clauses ∧
    st.trail_end = s.trail_end ∧ st.propagated = s.propagated ∧
    st.cur_level = 0 ∧ st.fuel = s.fuel ∧ st.confl_cid = s.confl_cid ∧
    st.tmp_cnt = s.tmp_cnt ∧ st.tmp_len = s.tmp_len ∧
    st.vals = s.vals ∧ st.lvl = s.lvl ∧ st.rsns = s.rsns ∧ st.trl = s.trl ∧
    st.wh = s.wh ∧ st.cls = s.cls ∧ st.wn = s.wn ∧ st.lpool = s.lpool ∧
    st.mrk.length = c.mv ∧ st.tmp.length = c.mv ∧
    (∀ k < tlen, (st.tmp[k]?.getD 0#32).toNat < 2 * c.mv) ∧
    (∀ k1 k2, k1 < tlen → k2 < tlen →
      (st.tmp[k1]?.getD 0#32).toNat / 2 = (st.tmp[k2]?.getD 0#32).toNat / 2 → k1 = k2) ∧
    (∀ v < c.mv,
      (∀ k < tlen, (st.tmp[k]?.getD 0#32).toNat / 2 ≠ v) → st.mrk[v]?.getD 0#8 = 0#8) ∧
    (∀ k < tlen,
      st.mrk[(st.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#8 =
        BitVec.ofNat 8 ((st.tmp[k]?.getD 0#32).toNat % 2 + 1)) ∧
    (taut = false → ∀ l ∈ revLits, ∃ k < tlen, (st.tmp[k]?.getD 0#32).toNat = l) ∧
    (∀ k < tlen, (st.tmp[k]?.getD 0#32).toNat ∈ revLits) ∧
    (revLits = [] → taut = false) ∧
    (∀ l, revLits = [l] → taut = false ∧ tlen = 1 ∧ (st.tmp[0]?.getD 0#32).toNat = l)
  refine wp_loop_break_group
    (fun (tlen_v, taut_v, err_v, ()) mb => ∃ idx tlen revLits st,
      tlen_v = BitVec.ofNat 32 tlen ∧ ReadInv idx tlen taut_v err_v revLits st ∧
      (err_v = true → parseClause c.mv (cnfBytes.drop i0) = none) ∧
      (err_v = false → i0 < idx ∧ st.d_cur = cnf_ptr + BitVec.ofNat 64 idx ∧
        parseClause c.mv (cnfBytes.drop i0) =
          some (CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral),
            cnfBytes.drop idx)) ∧
      (bytes cnf_ptr cnfBytes ⋆ ArenaMem c st ⋆ R) mb)
    (fun r (tlen_v, taut_v, ()) ml => ∃ idx tlen revLits st,
      r = cnfBytes.length - idx ∧ tlen_v = BitVec.ofNat 32 tlen ∧
      st.d_cur = cnf_ptr + BitVec.ofNat 64 idx ∧
      ReadInv idx tlen taut_v false revLits st ∧
      parseClauseAux ((cnfBytes.drop idx).length + 1) c.mv
        (revLits.map kissatLitToDimacsLiteral) (cnfBytes.drop idx) =
        parseClause c.mv (cnfBytes.drop i0) ∧
      (bytes cnf_ptr cnfBytes ⋆ ArenaMem c st ⋆ R) ml) ?_ ?_ ?_
  · -- Post-Loop 1: Loop 2 (clear marks), then err/taut check, then Loop 3 (prune), then dispatch
    rintro _ ⟨tlen_v, taut_v, err_v, ⟨⟩⟩ mb ⟨idx, tlen, revLits, st, rfl, hri, herr_p, hok_p, hmb⟩
    obtain ⟨hi_le, hidx, htlen_le, hll, hnc, hte, hpr, hcl_st, hfu, hcf, htc, htl,
      hvals, hlvl, hrsns, htrl, hwh, hcls, hwn, hlpool, hmkl, htmpl,
      htmp_lt, htmp_nd, hmrk_zero, hmrk_pos, hcov, hsub_rev, hnil_taut, hunit_r⟩ := hri
    wp_unfold
    -- Loop 2: clear marks for k = 0 .. tlen - 1
    refine wp_loop_group
      (fun r2 (kv, ()) m2 => ∃ k mrk',
        k ≤ tlen ∧ r2 = tlen - k ∧ kv = BitVec.ofNat 32 k ∧
        mrk'.length = c.mv ∧
        (∀ v < c.mv,
          (∀ j, k ≤ j → j < tlen → (st.tmp[j]?.getD 0#32).toNat / 2 ≠ v) →
          mrk'[v]?.getD 0#8 = 0#8) ∧
        (bytes cnf_ptr cnfBytes ⋆ ArenaMem c { st with mrk := mrk' } ⋆ R) m2) ?_ ?_
    · rintro L2 r2 ⟨kv, ⟨⟩⟩ m2 ih2 ⟨k, mrk', hkle, rfl, rfl, hmk'l, hclr, hm2⟩
      wp_unfold
      rw [bv32_ult_eq (by omega) (by omega)]
      simp only [decide_eq_true_eq, decide_eq_false_iff_not]
      refine ⟨fun hklt => ?_, fun hkge => ?_⟩
      · have hm2a : (ArenaMem c { st with mrk := mrk' } ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m2 :=
          sep_ac hm2
        rw [bv32_mul4_eq, bv32_ofNat_toNat (by omega)]
        have hk_tmp : k < st.tmp.length := by omega
        refine ⟨_, load_arena_tmp (by simp [htmpl]; omega) hm2a, ?_⟩
        let litk := st.tmp[k]'hk_tmp
        have hlitk_lt : litk.toNat < 2 * c.mv := by
          have := htmp_lt k hklt
          rwa [List.getElem?_eq_getElem hk_tmp, Option.getD_some] at this
        have hvk_lt : litk.toNat / 2 < c.mv := by omega
        refine wp_join_group
          (fun () m2' => (bytes cnf_ptr cnfBytes ⋆
            ArenaMem c { st with mrk := mrk'.set (litk.toNat / 2) 0#8 } ⋆ R) m2')
          (fun _ ⟨⟩ m2' hm2' => by
            wp_unfold
            rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
              show BitVec.ofNat 32 k + BitVec.ofNat 32 1 = BitVec.ofNat 32 (k + 1) by grind]
            refine ih2 (tlen - (k + 1)) _ m2' (by omega)
              ⟨k + 1, mrk'.set (litk.toNat / 2) 0#8, by omega, rfl, rfl, by simp [hmk'l],
                fun v hv hmiss => ?_, hm2'⟩
            by_cases hveq : v = litk.toNat / 2
            · subst v
              rw [List.getElem?_set_self (by omega)]; rfl
            · rw [List.getElem?_set_ne (Ne.symm hveq)]
              refine hclr v hv fun j hj1 hj2 => ?_
              by_cases hjk : j = k
              · subst j; rw [List.getElem?_eq_getElem hk_tmp, Option.getD_some]; exact Ne.symm hveq
              · exact hmiss j (by omega) hj2)
          (fun Jc hJc => by
            wp_unfold
            refine ⟨_, load_arena_mv hm2a, ?_⟩
            rw [bv32_zext64_eq, bv32_lshr_1, bv_ult_eq (by omega) (by omega)]
            simp only [decide_eq_true_eq, decide_eq_false_iff_not]
            refine ⟨fun _ => ?_, fun hc => absurd hvk_lt hc⟩
            rw [trunc32_8_zero]
            obtain ⟨okm, hmm⟩ := store_arena_mrk (i := litk.toNat / 2) 0#8
              (by simp [hmk'l]; omega) hm2a
            exact ⟨okm, hJc () _ (sep_ac hmm)⟩)
      · have hkeq : k = tlen := by omega
        subst k
        let st2 : ArenaState := { st with mrk := mrk' }
        have hlen2 : st2.LengthsOk c :=
          ⟨by simp [st2, hvals, hlen.vals_len], hmk'l, by simp [st2, hlvl, hlen.lvl_len],
            by simp [st2, hrsns, hlen.rsns_len], by simp [st2, htrl, hlen.trl_len], htmpl,
            by simp [st2, hwh, hlen.wh_len], by simp [st2, hcls, hlen.cls_len],
            by simp [st2, hwn, hlen.wn_len], by simp [st2, hlpool, hlen.lpool_len],
            by simp [st2, hll, hlen.lit_len_le], by simp [st2, hnc, hlen.num_clauses_le],
            by simp [st2, hte, hlen.trail_end_le], by simp [st2, hte, hpr, hlen.propagated_le],
            by simp [st2, hcl_st], by simp [st2, htc, hlen.tmp_cnt_lt],
            by simp [st2, htl, hlen.tmp_len_lt]⟩
        have hmrk_clr : MarksClear c st2 := fun v hv => hclr v hv (fun j hj1 hj2 => by omega)
        have hcore2 : SolverCoreInv c (shiftDownCnf accCnf) st2 := by
          have hco : ∀ cid, clauseOff st2 cid = clauseOff s cid := fun cid => by
            unfold clauseOff; simp [st2, hcls]
          have hcs : ∀ cid, clauseSize st2 cid = clauseSize s cid := fun cid => by
            unfold clauseSize; simp [st2, hcls]
          have hcl' : ∀ cid, clauseLits st2 cid = clauseLits s cid := fun cid => by
            unfold clauseLits; rw [hco, hcs]; simp [st2, hlpool]
          refine ⟨hlen2,
            ⟨fun cid hcid => by
               rw [hco, hcs]; simp only [st2, hll, hnc] at hcid ⊢
               exact hcore.clauses.bounds cid hcid,
             fun c1 c2 h12 h2 => by
               rw [hco, hcs, hco]; simp only [st2, hnc] at h2
               exact hcore.clauses.disjoint c1 c2 h12 h2,
             fun cid hcid => by
               rw [hcl']; simp only [st2, hnc] at hcid; exact hcore.clauses.lits_lt cid hcid,
             fun cid hcid => by
               rw [hcl']; simp only [st2, hnc] at hcid; exact hcore.clauses.entails cid hcid⟩,
            by simp [st2, hcl_st],
            by simp only [st2, hte, htrl]; exact hcore.trail_lits_lt,
            by simp only [st2, hte, htrl]; exact hcore.trail_vars_nodup,
            by simp only [st2, hvals]; exact hcore.vals_domain,
            by simp only [st2, hvals, hte, htrl]; exact hcore.vals_true_iff,
            by simp only [st2, hvals, hte, htrl]; exact hcore.vals_false_iff,
            fun i hi => by
              simp only [st2, hte, htrl, hlvl] at hi ⊢
              have := hcore.lvl_le i hi; omega,
            by simp only [st2, hte, htrl, hlvl]; exact hcore.trail_mono,
            by simp only [st2, hcl_st]; intro L h1 h2; omega,
            by simp only [st2, hte, htrl, hlvl]; exact hcore.level0_sound,
            fun idx' hidx' => by
              simp only [st2, hte, htrl, hrsns, hnc] at hidx' ⊢
              intro hne; obtain ⟨hrc, hall⟩ := hcore.reason_inv idx' hidx' hne
              refine ⟨hrc, fun q hq => hall q ?_⟩
              simpa [clauseLits, clauseOff, clauseSize, st2, hcls, hlpool] using hq⟩
        have hinv2 : SolverInv c (shiftDownCnf accCnf) st2 := ⟨hcore2, hmrk_clr⟩
        refine ⟨fun herr => ?_, fun hnoerr => ?_⟩
        · have hnone := herr_p herr
          rw [hnone] at hQ
          exact hQ st2 m2 hlen2 hfu hm2
        · obtain ⟨hi0_lt, hdcur_st, hpc_some⟩ := hok_p hnoerr
          let cl := CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral)
          have hcl_pos : ∀ lit ∈ cl.literals, 1 ≤ lit.1 := by
            intro lit hlit
            simp only [cl, CNF.Clause.literals_ofLiterals, List.mem_map] at hlit
            rcases hlit with ⟨l, _, rfl⟩
            simp [kissatLitToDimacsLiteral]
          rw [hpc_some] at hQ
          let F1 := shiftDownCnf (accCnf.add cl)
          have hinv2_F1 : SolverInv c F1 st2 :=
            SolverInv.mono (shiftDownCnf_entails_add accCnf cl) hinv2
          have hunit_rev : ∀ l < 2 * c.mv,
              cl = CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l] → revLits = [l] := by
            intro l _ hcleq
            have hlits_eq := congrArg CNF.Clause.literals hcleq
            simp only [cl, CNF.Clause.literals_ofLiterals] at hlits_eq
            cases hr : revLits.reverse with
            | nil => rw [hr] at hlits_eq; simp at hlits_eq
            | cons a rest_r =>
              rw [hr] at hlits_eq
              cases rest_r with
              | nil =>
                simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hlits_eq
                have ha : a = l := kissatLitToDimacsLiteral_inj hlits_eq
                subst ha
                have := congrArg List.reverse hr
                simpa using this
              | cons _ _ => simp at hlits_eq
          refine ⟨fun htaut => ?_, fun hntaut => ?_⟩
          · exact hQ 1#64 st2 idx m2 hcl_pos hi0_lt hidx rfl hlen2 hdcur_st hcl_st hfu
              (Or.inl rfl) (fun _ => hinv2_F1) (fun h => by cases h)
              (fun l hl hcleq _ => by
                have := (hunit_r l (hunit_rev l hl hcleq)).1; rw [htaut] at this; cases this)
              (fun l hl hcleq _ => by
                have := (hunit_r l (hunit_rev l hl hcleq)).1; rw [htaut] at this; cases this)
              hm2
          · -- Loop 3: prune satisfied/falsified literals in tmp[0..tlen) into tmp'[0..keep)
            have hF1_cl : F1.EntailsClause (cnfClause ((st.tmp.take tlen).map BitVec.toNat)) := by
              have hcl_ent : F1.EntailsClause (cnfClause revLits.reverse) := by
                have h1 := shiftDownCnf_entails_added accCnf cl
                rwa [show shiftDownClause cl = cnfClause revLits.reverse from
                  shiftDownClause_kissatLits revLits.reverse] at h1
              refine entails_of_mem_or_false hcl_ent fun l hl => Or.inl ?_
              obtain ⟨k, hk, hget⟩ := hcov hntaut l (List.mem_reverse.mp hl)
              rw [List.mem_map]
              refine ⟨st.tmp[k]'(by omega), ?_, ?_⟩
              · rw [List.mem_iff_getElem]
                exact ⟨k, by rw [List.length_take]; omega, by rw [List.getElem_take]⟩
              · rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at hget
            refine wp_loop_group
              (fun r3 (kp_v, iv, ()) m3 => ∃ keep i tmp',
                keep ≤ i ∧ i ≤ tlen ∧ r3 = tlen - i ∧
                kp_v = BitVec.ofNat 32 keep ∧ iv = BitVec.ofNat 32 i ∧
                tmp'.length = c.mv ∧
                (∀ k, i ≤ k → k < tlen → tmp'[k]? = st.tmp[k]?) ∧
                (∀ k < keep, (tmp'[k]?.getD 0#32).toNat < 2 * c.mv ∧
                  s.vals[(tmp'[k]?.getD 0#32).toNat]?.getD 0#8 = 0#8) ∧
                (∀ k < i,
                  (∃ j < keep, tmp'[j]? = st.tmp[k]?) ∨
                  s.vals[(st.tmp[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) ∧
                (∀ l < 2 * c.mv, revLits = [l] → s.vals[l]?.getD 0#8 = 0#8 →
                  i = 1 → keep = 1 ∧ (tmp'[0]?.getD 0#32).toNat = l) ∧
                (∀ l < 2 * c.mv, revLits = [l] → s.vals[l]?.getD 0#8 = 0xFF#8 →
                  i = 1 → keep = 0) ∧
                (bytes cnf_ptr cnfBytes ⋆ ArenaMem c { st2 with tmp := tmp' } ⋆ R) m3) ?_ ?_
            · rintro L3 r3 ⟨kp_v, iv, ⟨⟩⟩ m3 ih3
                ⟨keep, i, tmp', hk_le, hi_le3, rfl, rfl, rfl, htmp'l, htail, hkeep_un, hpruned,
                  hu0, hu1, hm3⟩
              wp_unfold
              rw [bv32_ult_eq (by omega) (by omega)]
              simp only [decide_eq_true_eq, decide_eq_false_iff_not]
              refine ⟨fun hilt => ?_, fun hige => ?_⟩
              · have hm3a : (ArenaMem c { st2 with tmp := tmp' } ⋆
                    (bytes cnf_ptr cnfBytes ⋆ R)) m3 := sep_ac hm3
                rw [bv32_mul4_eq, bv32_ofNat_toNat (by omega)]
                refine ⟨_, load_arena_tmp (by simp [htmp'l]; omega) hm3a, ?_⟩
                let li := tmp'[i]'(by omega)
                have hli_eq : li = st.tmp[i]'(by omega) := by
                  have h1 := htail i (Nat.le_refl _) hilt
                  rw [List.getElem?_eq_getElem (by omega),
                    List.getElem?_eq_getElem (by omega)] at h1
                  exact Option.some.inj h1
                have hli_lt : li.toNat < 2 * c.mv := by
                  have := htmp_lt i hilt
                  rwa [List.getElem?_eq_getElem (by omega), Option.getD_some, ← hli_eq] at this
                rw [bv32_zext64_eq]
                refine ⟨_, load_arena_vals (by simp [st2, hvals, hlen.vals_len]; exact hli_lt) hm3a,
                  ?_⟩
                let lv := s.vals[li.toNat]'(by rw [hlen.vals_len]; exact hli_lt)
                have hlv_eq : ({ st2 with tmp := tmp' }).vals[li.toNat]'(by
                    simp [st2, hvals, hlen.vals_len]; exact hli_lt) = lv := by
                  simp [st2, hvals, lv]
                have hlv_dom : lv = 0#8 ∨ lv = 1#8 ∨ lv = 0xFF#8 := by
                  have := hcore.vals_domain li.toNat hli_lt
                  rwa [List.getElem?_eq_getElem (by rw [hlen.vals_len]; exact hli_lt),
                    Option.getD_some] at this
                have hlv_getD : s.vals[li.toNat]?.getD 0#8 = lv := by
                  rw [List.getElem?_eq_getElem (by rw [hlen.vals_len]; exact hli_lt),
                    Option.getD_some]
                rw [hlv_eq, trunc32_8_zero, i8_sext32_zero]
                have hsgt : (0#32).slt (lv.signExtend 32) = true ↔ lv = 1#8 :=
                  i8_vals_sgt0 hlv_dom
                refine ⟨fun hpos => ?_, fun hnpos => ?_⟩
                · have hlv1 : lv = 1#8 := hsgt.mp hpos
                  let st3 : ArenaState := { st2 with tmp := tmp' }
                  have hlen3 : st3.LengthsOk c :=
                    ⟨hlen2.vals_len, hlen2.mrk_len, hlen2.lvl_len, hlen2.rsns_len, hlen2.trl_len,
                      htmp'l, hlen2.wh_len, hlen2.cls_len, hlen2.wn_len, hlen2.lpool_len,
                      hlen2.lit_len_le, hlen2.num_clauses_le, hlen2.trail_end_le,
                      hlen2.propagated_le, hlen2.cur_level_lt, hlen2.tmp_cnt_lt, hlen2.tmp_len_lt⟩
                  have hinv3 : SolverInv c F1 st3 := by
                    refine ⟨⟨hlen3,
                      ⟨hinv2_F1.core.clauses.bounds, hinv2_F1.core.clauses.disjoint,
                        hinv2_F1.core.clauses.lits_lt, hinv2_F1.core.clauses.entails⟩,
                      hinv2_F1.core.cur_level_le, hinv2_F1.core.trail_lits_lt,
                      hinv2_F1.core.trail_vars_nodup, hinv2_F1.core.vals_domain,
                      hinv2_F1.core.vals_true_iff, hinv2_F1.core.vals_false_iff,
                      hinv2_F1.core.lvl_le, hinv2_F1.core.trail_mono,
                      hinv2_F1.core.levels_inhabited, hinv2_F1.core.level0_sound,
                      hinv2_F1.core.reason_inv⟩, hinv2_F1.marks⟩
                  refine hQ 1#64 st3 idx m3 hcl_pos hi0_lt hidx rfl hlen3 hdcur_st hcl_st hfu
                    (Or.inl rfl) (fun _ => hinv3) (fun h => by cases h)
                    (fun l hl hcleq hv0 => by
                      have hrev := hunit_rev l hl hcleq
                      obtain ⟨_, ht1, htmp0⟩ := hunit_r l hrev
                      have hi0_eq : i = 0 := by omega
                      subst hi0_eq
                      have hli_l : li.toNat = l := by
                        rw [hli_eq]
                        rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at htmp0
                      rw [hli_l] at hlv_getD; rw [hlv_getD, hlv1] at hv0; cases hv0)
                    (fun l hl hcleq hvf => by
                      have hrev := hunit_rev l hl hcleq
                      obtain ⟨_, ht1, htmp0⟩ := hunit_r l hrev
                      have hi0_eq : i = 0 := by omega
                      subst hi0_eq
                      have hli_l : li.toNat = l := by
                        rw [hli_eq]
                        rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at htmp0
                      rw [hli_l] at hlv_getD; rw [hlv_getD, hlv1] at hvf; cases hvf)
                    hm3
                · have hlv_ne1 : lv ≠ 1#8 := fun h => by rw [hsgt.mpr h] at hnpos; cases hnpos
                  have heq0 : lv.signExtend 32 = 0#32 ↔ lv = 0#8 := i8_vals_eq0 hlv_dom
                  refine wp_join_group
                    (fun (kp', ()) m3' => ∃ keep' tmp'',
                      keep' ≤ i + 1 ∧ kp' = BitVec.ofNat 32 keep' ∧ tmp''.length = c.mv ∧
                      (∀ k, i + 1 ≤ k → k < tlen → tmp''[k]? = st.tmp[k]?) ∧
                      (∀ k < keep', (tmp''[k]?.getD 0#32).toNat < 2 * c.mv ∧
                        s.vals[(tmp''[k]?.getD 0#32).toNat]?.getD 0#8 = 0#8) ∧
                      (∀ k < i + 1,
                        (∃ j < keep', tmp''[j]? = st.tmp[k]?) ∨
                        s.vals[(st.tmp[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) ∧
                      (∀ l < 2 * c.mv, revLits = [l] → s.vals[l]?.getD 0#8 = 0#8 →
                        i + 1 = 1 → keep' = 1 ∧ (tmp''[0]?.getD 0#32).toNat = l) ∧
                      (∀ l < 2 * c.mv, revLits = [l] → s.vals[l]?.getD 0#8 = 0xFF#8 →
                        i + 1 = 1 → keep' = 0) ∧
                      (bytes cnf_ptr cnfBytes ⋆ ArenaMem c { st2 with tmp := tmp'' } ⋆ R) m3')
                    (fun _ ⟨kp', ⟨⟩⟩ m3' ⟨keep', tmp'', hk'le, hkp', htl', hta', hku', hpr',
                        hu0', hu1', hm3'⟩ => by
                      subst hkp'
                      wp_unfold
                      rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
                        show BitVec.ofNat 32 i + BitVec.ofNat 32 1 =
                          BitVec.ofNat 32 (i + 1) by grind]
                      exact ih3 (tlen - (i + 1)) _ m3' (by omega)
                        ⟨keep', i + 1, tmp'', hk'le, by omega, rfl, rfl, rfl, htl', hta', hku',
                          hpr', hu0', hu1', hm3'⟩)
                    (fun Jp hJp => by
                      wp_unfold
                      rw [trunc32_8_zero, i8_sext32_zero, heq0]
                      refine ⟨fun hlv0 => ?_, fun hlvne0 => ?_⟩
                      · rw [bv32_mul4_eq, bv32_ofNat_toNat (by omega)]
                        obtain ⟨okt, hmt⟩ := store_arena_tmp (i := keep) li
                          (by simp [htmp'l]; omega) hm3a
                        refine ⟨okt, ?_⟩
                        rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
                          show BitVec.ofNat 32 keep + BitVec.ofNat 32 1 =
                            BitVec.ofNat 32 (keep + 1) by grind]
                        refine hJp _ _ ⟨keep + 1, tmp'.set keep li, by omega, rfl,
                          by simp [htmp'l], ?_, ?_, ?_, ?_, ?_, sep_ac hmt⟩
                        · intro k hk1 hk2
                          rw [List.getElem?_set_ne (by omega)]; exact htail k (by omega) hk2
                        · intro k hk
                          by_cases hkk : k = keep
                          · subst k
                            rw [List.getElem?_set_self (by omega), Option.getD_some]
                            exact ⟨hli_lt, by rw [hlv_getD, hlv0]⟩
                          · rw [List.getElem?_set_ne (Ne.symm hkk)]; exact hkeep_un k (by omega)
                        · intro k hk
                          by_cases hki : k = i
                          · subst k
                            refine Or.inl ⟨keep, by omega, ?_⟩
                            rw [List.getElem?_set_self (by omega),
                              List.getElem?_eq_getElem (by omega), hli_eq]
                          · rcases hpruned k (by omega) with ⟨j, hj, hjeq⟩ | hfl
                            · exact Or.inl ⟨j, by omega,
                                by rw [List.getElem?_set_ne (by omega)]; exact hjeq⟩
                            · exact Or.inr hfl
                        · intro l hl hrev hv0 hi1
                          have hi0' : i = 0 := by omega
                          have hk0' : keep = 0 := by omega
                          subst hi0' hk0'
                          obtain ⟨_, _, htmp0⟩ := hunit_r l hrev
                          refine ⟨rfl, ?_⟩
                          rw [List.getElem?_set_self (by omega), Option.getD_some, hli_eq]
                          rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at htmp0
                        · intro l hl hrev hvf hi1
                          have hi0' : i = 0 := by omega
                          subst hi0'
                          obtain ⟨_, _, htmp0⟩ := hunit_r l hrev
                          have hli_l : li.toNat = l := by
                            rw [hli_eq]
                            rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at htmp0
                          rw [hli_l] at hlv_getD; rw [hlv_getD, hlv0] at hvf; cases hvf
                      · have hlv_ff : lv = 0xFF#8 := by
                          rcases hlv_dom with h | h | h
                          · exact absurd h hlvne0
                          · exact absurd h hlv_ne1
                          · exact h
                        refine hJp _ m3 ⟨keep, tmp', by omega, rfl, htmp'l,
                          fun k hk1 hk2 => htail k (by omega) hk2, hkeep_un, ?_, ?_, ?_, hm3⟩
                        · intro k hk
                          by_cases hki : k = i
                          · subst k
                            refine Or.inr ?_
                            rw [List.getElem?_eq_getElem (i := i) (by omega), Option.getD_some,
                              ← hli_eq, hlv_getD, hlv_ff]
                          · exact hpruned k (by omega)
                        · intro l hl hrev hv0 hi1
                          have hi0' : i = 0 := by omega
                          subst hi0'
                          obtain ⟨_, _, htmp0⟩ := hunit_r l hrev
                          have hli_l : li.toNat = l := by
                            rw [hli_eq]
                            rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at htmp0
                          rw [hli_l] at hlv_getD; rw [hlv_getD, hlv_ff] at hv0; cases hv0
                        · intro l hl hrev hvf hi1; omega)
              · -- Loop 3 done: i = tlen
                have hieq : i = tlen := by omega
                subst i
                have hF1_keep :
                    F1.EntailsClause (cnfClause ((tmp'.take keep).map BitVec.toNat)) := by
                  refine entails_of_mem_or_false hF1_cl fun l hl => ?_
                  rw [List.mem_map] at hl
                  obtain ⟨x, hx, rfl⟩ := hl
                  rw [List.mem_iff_getElem] at hx
                  obtain ⟨k, hk, hxk⟩ := hx
                  have hklt : k < tlen := by rw [List.length_take] at hk; omega
                  rw [List.getElem_take] at hxk
                  rcases hpruned k hklt with ⟨j, hj, hjeq⟩ | hfl
                  · refine Or.inl (List.mem_map.mpr ⟨x, ?_, rfl⟩)
                    rw [List.mem_iff_getElem]
                    refine ⟨j, by rw [List.length_take]; omega, ?_⟩
                    rw [List.getElem_take]
                    rw [List.getElem?_eq_getElem (by omega),
                      List.getElem?_eq_getElem (by omega)] at hjeq
                    exact (Option.some.inj hjeq).trans hxk
                  · refine Or.inr ?_
                    have hxk_get : (st.tmp[k]?.getD 0#32).toNat = x.toNat := by
                      rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hxk]
                    rw [hxk_get] at hfl
                    have hx_lt : x.toNat < 2 * c.mv := by
                      have := htmp_lt k hklt; rwa [hxk_get] at this
                    obtain ⟨ti, hti, htr_eq⟩ := (hcore.vals_false_iff x.toNat hx_lt).mp hfl
                    have hlvl0 :
                        (s.lvl[(s.trl[ti]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
                      have := hcore.lvl_le ti hti; omega
                    have hent0 := hcore.level0_sound ti hti hlvl0
                    have hent_F1 : F1.EntailsClause (cnfClause [(s.trl[ti]?.getD 0#32).toNat]) := by
                      rw [CNF.entails_clause_def] at hent0 ⊢
                      have hmono := shiftDownCnf_entails_add accCnf cl
                      rw [CNF.entails_def] at hmono
                      intro α hα; exact hent0 α (hmono α hα)
                    rwa [htr_eq] at hent_F1
                let st3 : ArenaState := { st2 with tmp := tmp' }
                have hlen3 : st3.LengthsOk c :=
                  ⟨hlen2.vals_len, hlen2.mrk_len, hlen2.lvl_len, hlen2.rsns_len, hlen2.trl_len,
                    htmp'l, hlen2.wh_len, hlen2.cls_len, hlen2.wn_len, hlen2.lpool_len,
                    hlen2.lit_len_le, hlen2.num_clauses_le, hlen2.trail_end_le,
                    hlen2.propagated_le, hlen2.cur_level_lt, hlen2.tmp_cnt_lt, hlen2.tmp_len_lt⟩
                have hinv3 : SolverInv c F1 st3 := by
                  refine ⟨⟨hlen3,
                    ⟨hinv2_F1.core.clauses.bounds, hinv2_F1.core.clauses.disjoint,
                      hinv2_F1.core.clauses.lits_lt, hinv2_F1.core.clauses.entails⟩,
                    hinv2_F1.core.cur_level_le, hinv2_F1.core.trail_lits_lt,
                    hinv2_F1.core.trail_vars_nodup, hinv2_F1.core.vals_domain,
                    hinv2_F1.core.vals_true_iff, hinv2_F1.core.vals_false_iff,
                    hinv2_F1.core.lvl_le, hinv2_F1.core.trail_mono,
                    hinv2_F1.core.levels_inhabited, hinv2_F1.core.level0_sound,
                    hinv2_F1.core.reason_inv⟩, hinv2_F1.marks⟩
                have hk0_iff : BitVec.ofNat 32 keep = (0 : BitVec 32) ↔ keep = 0 := by
                  constructor
                  · intro h; have ht := congrArg BitVec.toNat h
                    rw [bv32_ofNat_toNat (by omega)] at ht; exact ht
                  · intro h; subst h; rfl
                rw [hk0_iff]
                refine ⟨fun hk0 => ?_, fun hkn0 => ?_⟩
                · subst hk0
                  have hunsat : F1.Unsat := unsat_of_entails_nil (by simpa using hF1_keep)
                  exact hQ 2#64 st3 idx m3 hcl_pos hi0_lt hidx rfl hlen3 hdcur_st hcl_st hfu
                    (Or.inr (Or.inl rfl)) (fun h => by cases h) (fun _ => hunsat)
                    (fun l hl hcleq hv0 => by
                      have hrev := hunit_rev l hl hcleq
                      have ⟨_, ht1, _⟩ := hunit_r l hrev
                      have ⟨h1, _⟩ := hu0 l hl hrev hv0 ht1; omega)
                    (fun _ _ _ _ => rfl) hm3
                · have hk1_iff : BitVec.ofNat 32 keep = (1 : BitVec 32) ↔ keep = 1 := by
                    constructor
                    · intro h; have ht := congrArg BitVec.toNat h
                      rw [bv32_ofNat_toNat (by omega)] at ht; exact ht
                    · intro h; subst h; rfl
                  rw [hk1_iff]
                  refine ⟨fun hk1 => ?_, fun hkn1 => ?_⟩
                  · subst hk1
                    have hm3a : (ArenaMem c st3 ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m3 := sep_ac hm3
                    rw [show ((0 : BitVec 32).signExtend 64) * (4 : BitVec 64) =
                        BitVec.ofNat 64 (4 * 0) from rfl]
                    have ht0 := load_arena_tmp (s := st3) (i := 0)
                      (by simp [st3, htmp'l]; omega) hm3a
                    refine ⟨_, ht0, ?_⟩
                    let l0 := tmp'[0]'(by omega)
                    have ⟨hl0_lt, hl0_un⟩ := hkeep_un 0 (by decide)
                    rw [List.getElem?_eq_getElem (i := 0) (by omega),
                      Option.getD_some] at hl0_lt hl0_un
                    have hl0_lt' : l0.toNat < 2 * c.mv := hl0_lt
                    have hl0_ent : F1.EntailsClause (cnfClause [l0.toNat]) := by
                      have htk : tmp'.take 1 = [l0] := by
                        cases tmp' with
                        | nil => simp at htmp'l; omega
                        | cons a _ => rfl
                      simpa [htk] using hF1_keep
                    apply wp_call_of_spec; apply hAssign
                    refine ⟨c, st3, bytes cnf_ptr cnfBytes ⋆ R, rfl, hlen3, hm3a, ?_⟩
                    have hte_lt : st3.trail_end < c.mv :=
                      hinv3.core.trail_end_lt_of_unassigned hl0_lt'
                        (by simpa [st3, st2, hvals] using hl0_un)
                    have hnot_guard : ¬ (c.mv ≤ l0.toNat / 2 ∨ c.mv ≤ st3.trail_end) := by omega
                    dsimp only [Arg.val, st3]
                    by_cases hgd : c.mv ≤ tmp'[0].toNat / 2 ∨ c.mv ≤ st2.trail_end
                    · exfalso; exact hnot_guard hgd
                    · simp only [hgd, ↓reduceIte]
                      intro m4 _ hm4
                      wp_unfold
                      let sf : ArenaState :=
                        { st3 with
                          vals := (st3.vals.set l0.toNat 1#8).set (l0.toNat ^^^ 1) 0xFF#8,
                          lvl := st3.lvl.set (l0.toNat / 2) (BitVec.ofNat 32 st3.cur_level),
                          rsns := st3.rsns.set (l0.toNat / 2) 0xFFFFFFFF#32,
                          trl := st3.trl.set st3.trail_end l0,
                          trail_end := st3.trail_end + 1 }
                      have hsf_core : SolverCoreInv c F1 sf :=
                        assign_preserves_core hinv3.core hl0_lt'
                          (by simpa [st3, st2, hvals] using hl0_un)
                          (by simp [st3, st2, hcl_st])
                          (fun L h1 h2 => by simp [st3, st2, hcl_st] at h2; omega)
                          (fun _ => hl0_ent) (fun hc => absurd rfl hc)
                      have hsf_inv : SolverInv c F1 sf := ⟨hsf_core, hinv3.marks⟩
                      exact hQ 1#64 sf idx m4 hcl_pos hi0_lt hidx rfl hsf_core.lengths
                        hdcur_st hcl_st hfu (Or.inl rfl) (fun _ => hsf_inv) (fun h => by cases h)
                        (fun l hl hcleq hv0 => by
                          have hrev := hunit_rev l hl hcleq
                          have ⟨_, ht1, _⟩ := hunit_r l hrev
                          have ⟨_, hl0eq⟩ := hu0 l hl hrev hv0 ht1
                          rw [List.getElem?_eq_getElem (i := 0) (by omega),
                            Option.getD_some] at hl0eq
                          have hl0eq' : l0.toNat = l := hl0eq
                          exact ⟨rfl, by simp [sf, st3, st2, hvals, hl0eq'],
                            by simp [sf, st3, st2, hte], by simp [sf, st3, st2, hpr],
                            by simp [sf, st3, st2, hnc], by simp [sf, st3, st2, hwh]⟩)
                        (fun l hl hcleq hvf => by
                          have hrev := hunit_rev l hl hcleq
                          have ⟨_, ht1, _⟩ := hunit_r l hrev
                          have := hu1 l hl hrev hvf ht1; omega)
                        (sep_ac hm4)
                  · -- keep >= 2: call kissat_add_clause(h, keep)
                    have hkp_ge2 : 2 ≤ keep := by omega
                    have hm3a : (ArenaMem c st3 ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m3 := sep_ac hm3
                    apply wp_call_of_spec; apply hAddCl
                    refine ⟨c, st3, bytes cnf_ptr cnfBytes ⋆ R, rfl, hlen3,
                      by dsimp; rw [bv32_ofNat_toNat (by omega)]; omega, hm3a, ?_⟩
                    have hk32 : (BitVec.ofNat 32 keep).toNat = keep := bv32_ofNat_toNat (by omega)
                    simp only [Arg.val, hk32]
                    split
                    · wp_unfold
                      refine ⟨fun _ => ?_, fun hc => absurd rfl hc⟩
                      exact hQ 3#64 st3 idx m3 hcl_pos hi0_lt hidx rfl hlen3 hdcur_st hcl_st hfu
                        (Or.inr (Or.inr rfl)) (fun h => by cases h) (fun h => by cases h)
                        (fun l hl hcleq hv0 => by
                          have hrev := hunit_rev l hl hcleq
                          have ⟨_, ht1, _⟩ := hunit_r l hrev
                          have ⟨h1, _⟩ := hu0 l hl hrev hv0 ht1; omega)
                        (fun l hl hcleq hvf => by
                          have hrev := hunit_rev l hl hcleq
                          have ⟨_, ht1, _⟩ := hunit_r l hrev
                          have := hu1 l hl hrev hvf ht1; omega) hm3
                    · intro sf m4 hlen_sf hd1 _ hll_sf hnc_sf hte_sf hpr_sf hcl_sf hfu_sf _ _ _
                        hvals_sf hmrk_sf hlvl_sf hrsns_sf htrl_sf _ hmeta hlp_pre hoff hsz hlits hm4
                      wp_unfold
                      have hne_ff : BitVec.ofNat 64 st3.num_clauses ≠ (0xFFFFFFFF : BitVec 64) := by
                        intro heq
                        have hmc := c.hmax_c; unfold dimacsBound at hmc
                        have hnc_le := hlen3.num_clauses_le
                        have ht := congrArg BitVec.toNat heq
                        have hlt64 : st3.num_clauses < 2 ^ 64 := by omega
                        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64,
                          show (0xFFFFFFFF : BitVec 64).toNat = 0xFFFFFFFF from rfl] at ht
                        omega
                      refine ⟨fun hc => absurd hc hne_ff, fun _ => ?_⟩
                      have hlits_lt :
                          ∀ l ∈ (st3.tmp.take keep).map BitVec.toNat, l < 2 * c.mv := by
                        intro l hl
                        rw [List.mem_map] at hl
                        obtain ⟨x, hx, rfl⟩ := hl
                        rw [List.mem_iff_getElem] at hx
                        obtain ⟨k, hk, hxk⟩ := hx
                        rw [List.length_take] at hk
                        rw [List.getElem_take] at hxk
                        have hlt := (hkeep_un k (by omega)).1
                        rwa [List.getElem?_eq_getElem (by omega), Option.getD_some, hxk] at hlt
                      have hsf_core : SolverCoreInv c F1 sf :=
                        addClause_preserves_core hinv3.core hlen_sf hkp_ge2 hlits_lt
                          hF1_keep hll_sf hnc_sf hte_sf hcl_sf
                          hvals_sf hlvl_sf hrsns_sf htrl_sf hmeta hlp_pre hoff hsz hlits
                      have hsf_inv : SolverInv c F1 sf :=
                        ⟨hsf_core, fun v hv => by rw [hmrk_sf]; exact hinv3.marks v hv⟩
                      exact hQ 1#64 sf idx m4 hcl_pos hi0_lt hidx rfl hlen_sf
                        (by rw [hd1]; exact hdcur_st) (by rw [hcl_sf]; exact hcl_st)
                        (by rw [hfu_sf]; exact hfu) (Or.inl rfl) (fun _ => hsf_inv)
                        (fun h => by cases h)
                        (fun l hl hcleq hv0 => by
                          have hrev := hunit_rev l hl hcleq
                          have ⟨_, ht1, _⟩ := hunit_r l hrev
                          have ⟨h1, _⟩ := hu0 l hl hrev hv0 ht1; omega)
                        (fun l hl hcleq hvf => by
                          have hrev := hunit_rev l hl hcleq
                          have ⟨_, ht1, _⟩ := hunit_r l hrev
                          have := hu1 l hl hrev hvf ht1; omega)
                        (sep_ac hm4)
            · intro L3 hL3; wp_unfold
              exact hL3 tlen _ m2
                ⟨0, 0, st.tmp, Nat.le_refl _, Nat.zero_le _, by simp, rfl, rfl, htmpl,
                  fun _ _ _ => rfl, fun _ h => by omega, fun _ h => by omega,
                  fun _ _ _ _ h => by omega, fun _ _ _ _ h => by omega, hm2⟩
    · intro L2 hL2; wp_unfold
      exact hL2 tlen _ mb
        ⟨0, st.mrk, Nat.zero_le _, by simp, rfl, hmkl,
          fun v hv hmiss => hmrk_zero v hv (fun j hj => hmiss j (Nat.zero_le _) hj), hmb⟩
  · -- Loop 1 body: read next literal via kissat_next_lit
    rintro B1 L1 r ⟨tlen_v, taut_v, ⟨⟩⟩ ml hB1 ih1
      ⟨idx, tlen, revLits, st, rfl, rfl, hdcur_st, hri, hpc_inv, hml⟩
    obtain ⟨hi_le, hidx, htlen_le, hll, hnc, hte, hpr, hcl_st, hfu, hcf, htc, htl,
      hvals, hlvl, hrsns, htrl, hwh, hcls, hwn, hlpool, hmkl, htmpl,
      htmp_lt, htmp_nd, hmrk_zero, hmrk_pos, hcov, hsub_rev, hnil_taut, hunit_r⟩ := hri
    wp_unfold
    have hml_d : (bytes cnf_ptr cnfBytes ⋆
        dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
          (cnf_ptr + BitVec.ofNat 64 idx) st.d_val ⋆ (ArenaRest c st ⋆ R)) ml := by
      rw [← hdcur_st]
      have h1 := hml; rw [arenaMem_eq_dimacs_sep] at h1; exact sep_ac h1
    apply wp_call_of_spec; apply hLit
    change kissatNextLitSpec (cnf_ptr + BitVec.ofNat 64 cnfBytes.length, c.hdr, ()) ml _ _
    refine ⟨cnf_ptr, BitVec.ofNat 64 c.nc, st.d_val, c.mv, cnfBytes, idx, ArenaRest c st ⋆ R,
      rfl, hfit, by omega, hidx, hml_d, ?_⟩
    cases hnl : nextLitPure c.mv (cnfBytes.drop idx) with
    | err =>
      intro cur' val' m' hm'
      wp_unfold
      refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
      let st' : ArenaState := { st with d_cur := cur', d_val := val' }
      have hm'_a : (bytes cnf_ptr cnfBytes ⋆ ArenaMem c st' ⋆ R) m' := by
        rw [arenaMem_eq_dimacs_sep, arenaRest_d_irrel]; exact sep_ac hm'
      refine hB1 (BitVec.ofNat 32 tlen, taut_v, true, ()) m'
        ⟨idx, tlen, revLits, st', rfl,
          ⟨hi_le, hidx, htlen_le, hll, hnc, hte, hpr, hcl_st, hfu, hcf, htc, htl,
            hvals, hlvl, hrsns, htrl, hwh, hcls, hwn, hlpool, hmkl, htmpl,
            htmp_lt, htmp_nd, hmrk_zero, hmrk_pos, hcov, hsub_rev, hnil_taut, hunit_r⟩,
          fun _ => by rw [← hpc_inv, parseClauseAux_eq_nextLitPure, hnl],
          (fun hc => by cases hc), hm'_a⟩
    | endClause rest =>
      intro j m' hij hj hdrop hm'
      wp_unfold
      refine ⟨fun h => absurd h (by decide), fun _ => ⟨fun _ => ?_, fun h => absurd rfl h⟩⟩
      let st' : ArenaState := { st with d_cur := cnf_ptr + BitVec.ofNat 64 j, d_val := 0#64 }
      have hm'_a : (bytes cnf_ptr cnfBytes ⋆ ArenaMem c st' ⋆ R) m' := by
        rw [arenaMem_eq_dimacs_sep, arenaRest_d_irrel]; exact sep_ac hm'
      refine hB1 (BitVec.ofNat 32 tlen, taut_v, false, ()) m'
        ⟨j, tlen, revLits, st', rfl,
          ⟨by omega, hj, htlen_le, hll, hnc, hte, hpr, hcl_st, hfu, hcf, htc, htl,
            hvals, hlvl, hrsns, htrl, hwh, hcls, hwn, hlpool, hmkl, htmpl,
            htmp_lt, htmp_nd, hmrk_zero, hmrk_pos, hcov, hsub_rev, hnil_taut, hunit_r⟩,
          (fun hc => by cases hc),
          fun _ => ⟨by omega, rfl, by
            rw [← hpc_inv, parseClauseAux_eq_nextLitPure, hnl, List.map_reverse, hdrop]⟩,
          hm'_a⟩
    | lit l rest =>
      intro j m' hl_mv hl_bd hij hj hdrop hm'
      wp_unfold
      refine ⟨fun h => absurd h (by decide), fun _ =>
        ⟨fun h => absurd h (by decide), fun _ => ?_⟩⟩
      let st' : ArenaState :=
        { st with d_cur := cnf_ptr + BitVec.ofNat 64 j, d_val := BitVec.ofNat 64 l }
      have hm'_a : (ArenaMem c st' ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m' := by
        rw [arenaMem_eq_dimacs_sep, arenaRest_d_irrel]; exact sep_ac hm'
      refine ⟨_, load_arena_val hm'_a, _, load_arena_mv hm'_a, ?_⟩
      have hl32 : l < 2 ^ 32 := by omega
      have hv_lt : l / 2 < c.mv := by omega
      rw [bv64_trunc32_ofNat hl32, bv32_zext64_eq, bv32_lshr_1, bv32_ofNat_toNat hl32,
        bv_ule_eq (by omega) (by omega)]
      simp only [decide_eq_true_eq, decide_eq_false_iff_not]
      refine ⟨fun hge => absurd hv_lt (by omega), fun _ => ?_⟩
      refine ⟨_, load_arena_mrk (by simp [st', hmkl]; exact hv_lt) hm'_a, ?_⟩
      let mv_b := st.mrk[l / 2]'(by omega)
      have hmv_b_eq : st'.mrk[l / 2]'(by simp [st', hmkl]; exact hv_lt) = mv_b := rfl
      rw [hmv_b_eq, bv32_and1_add1, bv32_ofNat_toNat hl32]
      have hpc_next : parseClauseAux ((cnfBytes.drop j).length + 1) c.mv
          ((l :: revLits).map kissatLitToDimacsLiteral) (cnfBytes.drop j) =
          parseClause c.mv (cnfBytes.drop i0) := by
        have hstep : parseClauseAux ((cnfBytes.drop idx).length + 1) c.mv
            (revLits.map kissatLitToDimacsLiteral) (cnfBytes.drop idx) =
            parseClauseAux (cnfBytes.drop idx).length c.mv
              ((l :: revLits).map kissatLitToDimacsLiteral) (cnfBytes.drop j) := by
          rw [parseClauseAux_eq_nextLitPure, hnl, ← hdrop]; rfl
        rw [← hpc_inv, hstep]
        exact parseClauseAux_fuel_irrel (by simp only [List.length_drop]; omega)
          (by simp only [List.length_drop]; omega)
      refine wp_join_group
        (fun (tl', taut', _err', ()) m_s =>
          ∃ tlen' st_n, tl' = BitVec.ofNat 32 tlen' ∧
            st_n.d_cur = cnf_ptr + BitVec.ofNat 64 j ∧
            ReadInv j tlen' taut' false (l :: revLits) st_n ∧
            (bytes cnf_ptr cnfBytes ⋆ ArenaMem c st_n ⋆ R) m_s)
        (fun _ ⟨tl', taut', _err', ⟨⟩⟩ m_s ⟨tlen', st_n, htl', hdcur_n, hinv_n, hm_n⟩ => by
          subst htl'; wp_unfold
          exact ih1 (cnfBytes.length - j) _ m_s (by omega)
            ⟨j, tlen', l :: revLits, st_n, rfl, rfl, hdcur_n, hinv_n, hpc_next, hm_n⟩)
        (fun Js hJs => by
          wp_unfold
          rw [trunc32_8_zero, bv8_zext32_eq]
          refine ⟨fun hm0 => ?_, fun hmne0 => ?_⟩
          · -- m == 0: new variable, so tlen < c.mv by pigeonhole
            have hm0' : st.mrk[l / 2]'(by omega) = 0#8 := hm0
            have hmiss_v : ∀ k < tlen, (st.tmp[k]?.getD 0#32).toNat / 2 ≠ l / 2 := by
              intro k hk heq
              have hpos := hmrk_pos k hk
              rw [heq, List.getElem?_eq_getElem (by omega), Option.getD_some, hm0'] at hpos
              have h1 := congrArg BitVec.toNat hpos
              simp only [BitVec.toNat_ofNat] at h1
              omega
            have htlen_lt : tlen < c.mv :=
              inj_lt_of_missing (fun k => (st.tmp[k]?.getD 0#32).toNat / 2)
                htmp_nd (fun k hk => by have := htmp_lt k hk; omega) hv_lt hmiss_v
            refine ⟨_, load_arena_mv hm'_a, ?_⟩
            rw [bv32_zext64_eq, bv32_ofNat_toNat (by omega), bv_ule_eq (by omega) (by omega)]
            simp only [decide_eq_true_eq, decide_eq_false_iff_not]
            refine ⟨fun hge => absurd htlen_lt (by omega), fun _ => ?_⟩
            rw [bv32_zext64_eq, bv32_lshr_1, bv32_ofNat_toNat hl32]
            obtain ⟨okm, hmm⟩ := store_arena_mrk (i := l / 2) (BitVec.ofNat 8 (l % 2 + 1))
              (by simp [st', hmkl]; exact hv_lt) hm'_a
            refine ⟨okm, ?_⟩
            rw [bv64_mul4_nat]
            obtain ⟨okt, hmt⟩ := store_arena_tmp (i := tlen) (BitVec.ofNat 32 l)
              (by simp [st', htmpl]; exact htlen_lt) hmm
            refine ⟨okt, ?_⟩
            rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
              show BitVec.ofNat 32 tlen + BitVec.ofNat 32 1 = BitVec.ofNat 32 (tlen + 1) by grind]
            let st_n : ArenaState :=
              { st' with
                mrk := st.mrk.set (l / 2) (BitVec.ofNat 8 (l % 2 + 1)),
                tmp := st.tmp.set tlen (BitVec.ofNat 32 l) }
            refine hJs _ _ ⟨tlen + 1, st_n, rfl, rfl,
                ⟨by omega, hj, by omega, hll, hnc, hte, hpr, hcl_st, hfu, hcf, htc, htl,
                  hvals, hlvl, hrsns, htrl, hwh, hcls, hwn, hlpool,
                  by simp [st_n, hmkl], by simp [st_n, htmpl],
                  fun k hk => by
                    dsimp only [st_n]
                    by_cases hkt : k = tlen
                    · subst k; rw [List.getElem?_set_self (by omega), Option.getD_some,
                        bv32_ofNat_toNat hl32]; exact hl_mv
                    · rw [List.getElem?_set_ne (Ne.symm hkt)]; exact htmp_lt k (by omega),
                  fun k1 k2 h1 h2 heq => by
                    dsimp only [st_n] at heq
                    by_cases hk1 : k1 = tlen <;> by_cases hk2 : k2 = tlen
                    · omega
                    · subst hk1
                      rw [List.getElem?_set_self (by omega), Option.getD_some,
                        bv32_ofNat_toNat hl32, List.getElem?_set_ne (Ne.symm hk2)] at heq
                      exact absurd heq.symm (hmiss_v k2 (by omega))
                    · subst hk2
                      rw [List.getElem?_set_self (by omega), Option.getD_some,
                        bv32_ofNat_toNat hl32, List.getElem?_set_ne (Ne.symm hk1)] at heq
                      exact absurd heq (hmiss_v k1 (by omega))
                    · rw [List.getElem?_set_ne (Ne.symm hk1),
                        List.getElem?_set_ne (Ne.symm hk2)] at heq
                      exact htmp_nd k1 k2 (by omega) (by omega) heq,
                  fun v hv hmiss => by
                    dsimp only [st_n]
                    have hne : v ≠ l / 2 := by
                      have h := hmiss tlen (by omega)
                      dsimp only [st_n] at h
                      rw [List.getElem?_set_self (by omega), Option.getD_some,
                        bv32_ofNat_toNat hl32] at h
                      exact Ne.symm h
                    rw [List.getElem?_set_ne (Ne.symm hne)]
                    refine hmrk_zero v hv fun k hk => ?_
                    have h := hmiss k (by omega)
                    dsimp only [st_n] at h
                    rwa [List.getElem?_set_ne (by omega)] at h,
                  fun k hk => by
                    dsimp only [st_n]
                    by_cases hkt : k = tlen
                    · subst k
                      rw [List.getElem?_set_self (by omega), Option.getD_some,
                        bv32_ofNat_toNat hl32, List.getElem?_set_self (by omega)]; rfl
                    · rw [List.getElem?_set_ne (Ne.symm hkt)]
                      have hne := hmiss_v k (by omega)
                      rw [List.getElem?_set_ne (Ne.symm hne)]
                      exact hmrk_pos k (by omega),
                  fun hnt x hx => by
                    rcases List.mem_cons.mp hx with rfl | hx'
                    · refine ⟨tlen, by omega, ?_⟩
                      dsimp only [st_n]
                      rw [List.getElem?_set_self (by omega), Option.getD_some,
                        bv32_ofNat_toNat hl32]
                    · obtain ⟨k, hk, hget⟩ := hcov hnt x hx'
                      refine ⟨k, by omega, ?_⟩
                      dsimp only [st_n]; rwa [List.getElem?_set_ne (by omega)],
                  fun k hk => by
                    dsimp only [st_n]
                    by_cases hkt : k = tlen
                    · subst k; rw [List.getElem?_set_self (by omega), Option.getD_some,
                        bv32_ofNat_toNat hl32]; exact List.mem_cons_self
                    · rw [List.getElem?_set_ne (Ne.symm hkt)]
                      exact List.mem_cons_of_mem _ (hsub_rev k (by omega)),
                  (fun hc => by cases hc),
                  fun l' hl' => by
                    rcases List.cons.inj hl' with ⟨rfl, rfl⟩
                    have ht0 : tlen = 0 := by
                      cases tlen with
                      | zero => rfl
                      | succ k => exact absurd (hsub_rev 0 (by omega)) (by simp)
                    subst ht0
                    refine ⟨hnil_taut rfl, rfl, ?_⟩
                    dsimp only [st_n]
                    rw [List.getElem?_set_self (by omega), Option.getD_some,
                      bv32_ofNat_toNat hl32]⟩,
                by simpa [st_n, st'] using sep_ac hmt⟩
          · -- m != 0: variable l/2 already seen at some k0 < tlen
            have hex : ∃ k0 < tlen, (st.tmp[k0]?.getD 0#32).toNat / 2 = l / 2 := by
              by_cases h : ∃ k0 < tlen, (st.tmp[k0]?.getD 0#32).toNat / 2 = l / 2
              · exact h
              · exfalso
                have h0 := hmrk_zero (l / 2) hv_lt (fun k hk heq => h ⟨k, hk, heq⟩)
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h0
                exact hmne0 h0
            obtain ⟨k0, hk0, hk0_v⟩ := hex
            have hmv_pos := hmrk_pos k0 hk0
            rw [hk0_v, List.getElem?_eq_getElem (by omega), Option.getD_some] at hmv_pos
            refine wp_join_group
              (fun (taut', ()) m_j =>
                (taut' = if mv_b = BitVec.ofNat 8 (l % 2 + 1) then taut_v else true) ∧ m_j = m')
              (fun _ ⟨taut', ⟨⟩⟩ m_j ⟨htaut', hm_j⟩ => by
                subst m_j
                wp_unfold
                refine hJs _ m' ⟨tlen, st', rfl, rfl,
                    ⟨by omega, hj, htlen_le, hll, hnc, hte, hpr, hcl_st, hfu, hcf, htc, htl,
                      hvals, hlvl, hrsns, htrl, hwh, hcls, hwn, hlpool, hmkl, htmpl,
                      htmp_lt, htmp_nd, hmrk_zero, hmrk_pos, ?_, ?_, (fun hc => by cases hc), ?_⟩,
                    sep_ac hm'_a⟩
                · intro hnt' x hx
                  by_cases hmeq : mv_b = BitVec.ofNat 8 (l % 2 + 1)
                  · simp only [hmeq, ↓reduceIte] at htaut'
                    have hnt : taut_v = false := htaut' ▸ hnt'
                    rcases List.mem_cons.mp hx with rfl | hx'
                    · refine ⟨k0, hk0, ?_⟩
                      have hmeq' : st.mrk[x / 2]'(by omega) = BitVec.ofNat 8 (x % 2 + 1) := hmeq
                      rw [hmv_pos] at hmeq'
                      have hmod := congrArg BitVec.toNat hmeq'
                      simp only [BitVec.toNat_ofNat] at hmod
                      dsimp only [st']
                      omega
                    · exact hcov hnt x hx'
                  · simp only [hmeq, ↓reduceIte] at htaut'; rw [htaut'] at hnt'; cases hnt'
                · intro k hk; exact List.mem_cons_of_mem _ (hsub_rev k hk)
                · intro l' hl'
                  rcases List.cons.inj hl' with ⟨_, rfl⟩
                  exact absurd (hsub_rev k0 hk0) (by simp))
              (fun Jt hJt => by
                wp_unfold
                rw [bv8_zext32_eq]
                refine ⟨fun hne => hJt (true, ()) m' ⟨by simp [hne], rfl⟩,
                  fun heq => hJt (taut_v, ()) m' ⟨by simp [heq], rfl⟩⟩))
  · intro B1 L1 _ hL1; wp_unfold
    exact hL1 (cnfBytes.length - i0) _ m
      ⟨i0, 0, [], s, rfl, rfl, hdcur,
        ⟨Nat.le_refl _, hi0, Nat.zero_le _, rfl, rfl, rfl, rfl, hcl0, rfl, rfl, rfl, rfl,
          rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hlen.mrk_len, hlen.tmp_len_arr,
          fun _ h => by omega, fun _ _ h => by omega,
          fun v hv _ => hinv.marks v hv, fun _ h => by omega,
          (fun _ _ h => by cases h), (fun _ h => by omega), (fun _ => rfl),
          (fun _ h => by cases h)⟩,
        rfl, hm⟩

private theorem lengthsOk_d_update {c : ArenaCfg} {s : ArenaState} {cur' val' : BitVec 64}
    (h : s.LengthsOk c) : ({ s with d_cur := cur', d_val := val' }).LengthsOk c :=
  ⟨h.vals_len, h.mrk_len, h.lvl_len, h.rsns_len, h.trl_len, h.tmp_len_arr, h.wh_len, h.cls_len,
    h.wn_len, h.lpool_len, h.lit_len_le, h.num_clauses_le, h.trail_end_le, h.propagated_le,
    h.cur_level_lt, h.tmp_cnt_lt, h.tmp_len_lt⟩

private theorem solverInv_d_update {c : ArenaCfg} {F0 : CNF Nat} {s : ArenaState}
    {cur' val' : BitVec 64} (h : SolverInv c F0 s) :
    SolverInv c F0 { s with d_cur := cur', d_val := val' } :=
  ⟨⟨lengthsOk_d_update h.core.lengths,
    ⟨h.core.clauses.bounds, h.core.clauses.disjoint, h.core.clauses.lits_lt,
      h.core.clauses.entails⟩,
    h.core.cur_level_le, h.core.trail_lits_lt, h.core.trail_vars_nodup, h.core.vals_domain,
    h.core.vals_true_iff, h.core.vals_false_iff, h.core.lvl_le, h.core.trail_mono,
    h.core.levels_inhabited, h.core.level0_sound, h.core.reason_inv⟩, h.marks⟩

/-! ## 5. `kissat_parse_body` specification and `Func.wp` proof -/

/-- Specification of `kissat_parse_body(h, cnf_end)`. -/
def kissatParseBodySpec : Spec [i64, i64] [i64] := fun (h, cend, ()) m Q _ =>
  ∃ (c : ArenaCfg) (s : ArenaState) (cnf_ptr : BitVec 64) (cnfBytes : List UInt8) (i0 : Nat)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
    i0 ≤ cnfBytes.length ∧
    parseHeader cnfBytes = some (c.mv, c.nc, cnfBytes.drop i0) ∧
    s.d_cur = cnf_ptr + BitVec.ofNat 64 i0 ∧
    s.cur_level = 0 ∧ s.trail_end = 0 ∧ s.propagated = 0 ∧ s.num_clauses = 0 ∧
    SolverInv c (shiftDownCnf CNF.empty) s ∧
    (bytes cnf_ptr cnfBytes ⋆ ArenaMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      s'.fuel = s.fuel →
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
      (r = 1#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
        SolverInv c (shiftDownCnf cnf) s' ∧ s'.cur_level = 0) →
      (∀ vals' te', UnitSatTrace c.mv s.vals 0 (cnfBytes.drop i0) c.nc vals' te' →
        r = 1#64 ∧ s'.vals = vals' ∧ s'.trail_end = te' ∧ s'.propagated = 0 ∧
        s'.num_clauses = 0 ∧ s'.wh = s.wh) →
      (UnitUnsatTrace c.mv s.vals (cnfBytes.drop i0) c.nc → r = 20#64) →
      (bytes cnf_ptr cnfBytes ⋆ ArenaMem c s' ⋆ R) m' →
      Q (r, ()) m'

theorem kissat_parse_body_wp (Γ : Env)
    (hSkip : ∀ args m Q X, kissatSkipClauseSyntaxSpec args m Q X →
      Γ "kissat_skip_clause_syntax" [i64, i64] [.bool] args m Q X)
    (hIngest : ∀ args m Q X, kissatIngestClauseSpec args m Q X →
      Γ "kissat_ingest_clause" [i64, i64] [i64] args m Q X)
    (hSwc : ∀ args m Q X, kissatSkipWsCommentsSpec args m Q X →
      Γ "kissat_skip_ws_comments" [i64, i64] [i64] args m Q X) :
    ∀ args m Q X, kissatParseBodySpec args m Q X →
      Func.wp Γ kissat_parse_body_body args m Q X := by
  rintro ⟨h, cend, ⟨⟩⟩ m Q X
    ⟨c, s, cnf_ptr, cnfBytes, i0, R, rfl, rfl, hfit, hi0, hhdr, hdcur, hcl0, hte0, hpr0, hnc0,
      hinv0, hm, hQ⟩
  unfold Func.wp kissat_parse_body_body; wp_unfold
  have hnc_bd := c.hnc; have hmv_bd := c.hmv; unfold dimacsBound at hnc_bd hmv_bd
  have hpd_init : parseClauses c.mv c.nc CNF.empty (cnfBytes.drop i0) = parseDimacs cnfBytes := by
    simp [parseDimacs, hhdr]
  refine wp_loop_group
    (fun r (unsat_v, oom_v, iv, ()) ml => ∃ i idx accCnf st,
      i ≤ c.nc ∧ r = c.nc - i ∧ iv = BitVec.ofNat 64 i ∧
      idx ≤ cnfBytes.length ∧ st.d_cur = cnf_ptr + BitVec.ofNat 64 idx ∧
      st.LengthsOk c ∧ st.cur_level = 0 ∧ st.fuel = s.fuel ∧
      CnfVarsPos accCnf ∧
      parseClauses c.mv (c.nc - i) accCnf (cnfBytes.drop idx) = parseDimacs cnfBytes ∧
      (unsat_v = true → (shiftDownCnf accCnf).Unsat) ∧
      (unsat_v = false → oom_v = false → SolverInv c (shiftDownCnf accCnf) st) ∧
      (∀ vals' te', UnitSatTrace c.mv s.vals 0 (cnfBytes.drop i0) c.nc vals' te' →
        unsat_v = false ∧ oom_v = false ∧ st.propagated = 0 ∧ st.num_clauses = 0 ∧ st.wh = s.wh ∧
        UnitSatTrace c.mv st.vals st.trail_end (cnfBytes.drop idx) (c.nc - i) vals' te') ∧
      (UnitUnsatTrace c.mv s.vals (cnfBytes.drop i0) c.nc →
        oom_v = false ∧
        ((unsat_v = false ∧ UnitUnsatTrace c.mv st.vals (cnfBytes.drop idx) (c.nc - i)) ∨
         (unsat_v = true ∧
           ∃ cnf, parseClauses c.mv (c.nc - i) CNF.empty (cnfBytes.drop idx) = some cnf))) ∧
      (bytes cnf_ptr cnfBytes ⋆ ArenaMem c st ⋆ R) ml) ?_ ?_
  · rintro L r ⟨unsat_v, oom_v, iv, ⟨⟩⟩ ml ih
      ⟨i, idx, accCnf, st, hile, rfl, rfl, hidx, hdcur_st, hlen_st, hcl_st, hfu_st, hpos, hpc_eq,
        huns_inv, hok_inv, hsat_tr, huns_tr, hml⟩
    wp_unfold
    have hml_a : (ArenaMem c st ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) ml := sep_ac hml
    refine ⟨_, load_arena_nc hml_a, ?_⟩
    rw [bv_ult_eq (by omega) (by omega)]
    simp only [decide_eq_true_eq, decide_eq_false_iff_not]
    refine ⟨fun hilt => ?_, fun hige => ?_⟩
    · have hsub_eq : c.nc - i = (c.nc - (i + 1)) + 1 := by omega
      have hjoin_next : ∀ (unsat' oom' : Bool) (idx' : Nat) (accCnf' : CNF Nat)
          (st' : ArenaState) (m' : Mem 64),
          idx' ≤ cnfBytes.length → st'.d_cur = cnf_ptr + BitVec.ofNat 64 idx' →
          st'.LengthsOk c → st'.cur_level = 0 → st'.fuel = s.fuel →
          CnfVarsPos accCnf' →
          parseClauses c.mv (c.nc - (i + 1)) accCnf' (cnfBytes.drop idx') = parseDimacs cnfBytes →
          (unsat' = true → (shiftDownCnf accCnf').Unsat) →
          (unsat' = false → oom' = false → SolverInv c (shiftDownCnf accCnf') st') →
          (∀ vals' te', UnitSatTrace c.mv s.vals 0 (cnfBytes.drop i0) c.nc vals' te' →
            unsat' = false ∧ oom' = false ∧ st'.propagated = 0 ∧ st'.num_clauses = 0 ∧
            st'.wh = s.wh ∧
            UnitSatTrace c.mv st'.vals st'.trail_end (cnfBytes.drop idx')
              (c.nc - (i + 1)) vals' te') →
          (UnitUnsatTrace c.mv s.vals (cnfBytes.drop i0) c.nc →
            oom' = false ∧
            ((unsat' = false ∧ UnitUnsatTrace c.mv st'.vals (cnfBytes.drop idx') (c.nc - (i + 1))) ∨
             (unsat' = true ∧ ∃ cnf,
               parseClauses c.mv (c.nc - (i + 1)) CNF.empty (cnfBytes.drop idx') = some cnf))) →
          (bytes cnf_ptr cnfBytes ⋆ ArenaMem c st' ⋆ R) m' →
          L (unsat', oom', BitVec.ofNat 64 i + 1, ()) m' := by
        intro unsat' oom' idx' accCnf' st' m' hidx' hd' hlen' hcl' hfu' hpos' hpc'
          hu' hok' hst' hut' hm'
        rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv_add_ofNat]
        exact ih (c.nc - (i + 1)) _ m' (by omega)
          ⟨i + 1, idx', accCnf', st', by omega, rfl, rfl, hidx', hd', hlen', hcl', hfu',
            hpos', hpc', hu', hok', hst', hut', hm'⟩
      refine wp_join_group
        (fun (unsat', oom', ()) m' => ∃ idx' accCnf' st',
          idx' ≤ cnfBytes.length ∧ st'.d_cur = cnf_ptr + BitVec.ofNat 64 idx' ∧
          st'.LengthsOk c ∧ st'.cur_level = 0 ∧ st'.fuel = s.fuel ∧
          CnfVarsPos accCnf' ∧
          parseClauses c.mv (c.nc - (i + 1)) accCnf' (cnfBytes.drop idx') = parseDimacs cnfBytes ∧
          (unsat' = true → (shiftDownCnf accCnf').Unsat) ∧
          (unsat' = false → oom' = false → SolverInv c (shiftDownCnf accCnf') st') ∧
          (∀ vals' te', UnitSatTrace c.mv s.vals 0 (cnfBytes.drop i0) c.nc vals' te' →
            unsat' = false ∧ oom' = false ∧ st'.propagated = 0 ∧ st'.num_clauses = 0 ∧
            st'.wh = s.wh ∧
            UnitSatTrace c.mv st'.vals st'.trail_end (cnfBytes.drop idx')
              (c.nc - (i + 1)) vals' te') ∧
          (UnitUnsatTrace c.mv s.vals (cnfBytes.drop i0) c.nc →
            oom' = false ∧
            ((unsat' = false ∧ UnitUnsatTrace c.mv st'.vals (cnfBytes.drop idx') (c.nc - (i + 1))) ∨
             (unsat' = true ∧ ∃ cnf,
               parseClauses c.mv (c.nc - (i + 1)) CNF.empty (cnfBytes.drop idx') = some cnf))) ∧
          (bytes cnf_ptr cnfBytes ⋆ ArenaMem c st' ⋆ R) m')
        (fun _ ⟨unsat', oom', ⟨⟩⟩ m' ⟨idx', accCnf', st', h1, h2, h3, h4, h5, h6, h7, h8, h9,
            h10, h11, h12⟩ => by
          wp_unfold
          exact hjoin_next unsat' oom' idx' accCnf' st' m' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12)
        (fun Jb hJb => ?_)
      wp_unfold
      refine ⟨fun huns_t => ?_, fun huns_f => ?_⟩
      · -- unsat_seen = true: call kissat_skip_clause_syntax(cnf_end, &h->d)
        have hml_d : (bytes cnf_ptr cnfBytes ⋆
            dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
              (cnf_ptr + BitVec.ofNat 64 idx) st.d_val ⋆ (ArenaRest c st ⋆ R)) ml := by
          rw [← hdcur_st]; have h1 := hml; rw [arenaMem_eq_dimacs_sep] at h1; exact sep_ac h1
        apply wp_call_of_spec; apply hSkip
        change kissatSkipClauseSyntaxSpec
          (cnf_ptr + BitVec.ofNat 64 cnfBytes.length, c.hdr, ()) ml _ _
        refine ⟨cnf_ptr, BitVec.ofNat 64 c.nc, st.d_val, c.mv, cnfBytes, idx, ArenaRest c st ⋆ R,
          rfl, hfit, by omega, hidx, hml_d, ?_⟩
        cases hpc1 : parseClause c.mv (cnfBytes.drop idx) with
        | none =>
          intro cur' val' m' hm'
          wp_unfold
          let st' : ArenaState := { st with d_cur := cur', d_val := val' }
          have hm'_a : (bytes cnf_ptr cnfBytes ⋆ ArenaMem c st' ⋆ R) m' := by
            rw [arenaMem_eq_dimacs_sep, arenaRest_d_irrel]; exact sep_ac hm'
          exact hQ 0#64 st' m' (lengthsOk_d_update hlen_st) (Or.inl rfl) hfu_st
            (fun h => by cases h) (fun h => by cases h)
            (fun vals' te' hst => by
              have h1 := (hsat_tr vals' te' hst).1; rw [huns_t] at h1; cases h1)
            (fun hut => by
              rcases (huns_tr hut).2 with ⟨hf, _⟩ | ⟨_, ⟨cnf_r, hr⟩⟩
              · rw [huns_t] at hf; cases hf
              · rw [hsub_eq, parseClauses, hpc1] at hr; cases hr)
            hm'_a
        | some p =>
          rcases p with ⟨cl, rest⟩
          intro j m' hcl_pos _ hj hdrop hm'
          wp_unfold
          let st' : ArenaState := { st with d_cur := cnf_ptr + BitVec.ofNat 64 j, d_val := 0#64 }
          have hm'_a : (bytes cnf_ptr cnfBytes ⋆ ArenaMem c st' ⋆ R) m' := by
            rw [arenaMem_eq_dimacs_sep, arenaRest_d_irrel]; exact sep_ac hm'
          rw [huns_t]
          refine hJb (true, oom_v, ()) m' ⟨j, accCnf.add cl, st', hj, rfl,
            lengthsOk_d_update hlen_st, hcl_st, hfu_st,
            cnfVarsPos_add hpos hcl_pos, ?_, ?_, (fun hc => by cases hc), ?_, ?_, hm'_a⟩
          · rw [← hpc_eq, hsub_eq, parseClauses, hpc1, ← hdrop]; rfl
          · intro _; rw [shiftDownCnf_add]; exact cnf_unsat_add (huns_inv huns_t)
          · intro vals' te' hst
            have h1 := (hsat_tr vals' te' hst).1; rw [huns_t] at h1; cases h1
          · intro hut
            obtain ⟨hoom, hdisj⟩ := huns_tr hut
            refine ⟨hoom, Or.inr ⟨rfl, ?_⟩⟩
            rcases hdisj with ⟨hf, _⟩ | ⟨_, cnf_r, hr⟩
            · rw [huns_t] at hf; cases hf
            · rw [hsub_eq, parseClauses, hpc1, ← hdrop] at hr
              exact parseClauses_some_of_acc hr
      · -- unsat_seen = false: check oom_seen
        refine ⟨fun hoom_t => ?_, fun hoom_f => ?_⟩
        · exact hQ 0#64 st ml hlen_st (Or.inl rfl) hfu_st
            (fun h => by cases h) (fun h => by cases h)
            (fun vals' te' hst => by
              have h2 := (hsat_tr vals' te' hst).2.1; rw [hoom_t] at h2; cases h2)
            (fun hut => by
              have h1 := (huns_tr hut).1; rw [hoom_t] at h1; cases h1)
            hml
        · -- call kissat_ingest_clause(h, cnf_end)
          have hinv_st := hok_inv huns_f hoom_f
          apply wp_call_of_spec; apply hIngest
          refine ⟨c, accCnf, st, cnf_ptr, cnfBytes, idx, R, rfl, rfl, hfit, hidx, hdcur_st,
            hcl_st, hinv_st, hml, ?_⟩
          cases hpc1 : parseClause c.mv (cnfBytes.drop idx) with
          | none =>
            intro st' m' hlen' hfu' hm'
            wp_unfold
            refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
            exact hQ 0#64 st' m' hlen' (Or.inl rfl) (by rw [hfu', hfu_st])
              (fun h => by cases h) (fun h => by cases h)
              (fun vals' te' hst => by
                have htr := (hsat_tr vals' te' hst).2.2.2.2.2
                rw [hsub_eq] at htr
                cases htr with
                | step _ hpc_s _ _ => rw [hpc1] at hpc_s; cases hpc_s)
              (fun hut => by
                rcases (huns_tr hut).2 with ⟨_, htr⟩ | ⟨ht, _⟩
                · rw [hsub_eq] at htr
                  cases htr with
                  | conflict _ hpc_s _ _ => rw [hpc1] at hpc_s; cases hpc_s
                  | step _ hpc_s _ _ => rw [hpc1] at hpc_s; cases hpc_s
                · rw [huns_f] at ht; cases ht)
              hm'
          | some p =>
            rcases p with ⟨cl, rest⟩
            intro r_in st' j m' hcl_pos _ hj hdrop hlen' hdcur' hcl' hfu' hr_dom hok_in huns_in
              hunit_ok hunit_fl hm'
            wp_unfold
            have hne0 : r_in ≠ 0#64 := by rcases hr_dom with rfl | rfl | rfl <;> decide
            refine ⟨fun hc => absurd hc hne0, fun _ => ?_⟩
            have hpc_next : parseClauses c.mv (c.nc - (i + 1)) (accCnf.add cl) (cnfBytes.drop j) =
                parseDimacs cnfBytes := by
              rw [← hpc_eq, hsub_eq, parseClauses, hpc1, ← hdrop]; rfl
            have hpos_next := cnfVarsPos_add hpos hcl_pos
            refine wp_join_group
              (fun (u', o', ()) m_j =>
                u' = decide (r_in = 2#64) ∧ o' = decide (r_in = 3#64) ∧ m_j = m')
              (fun _ ⟨u', o', ⟨⟩⟩ m_j ⟨hu', ho', hm_j⟩ => by
                subst m_j; wp_unfold
                rcases hr_dom with rfl | rfl | rfl
                · -- r_in = 1#64: normal ingest
                  subst hu' ho'
                  refine hJb (false, false, ()) m' ⟨j, accCnf.add cl, st', hj, hdcur', hlen', hcl',
                    by rw [hfu', hfu_st], hpos_next, hpc_next,
                    (fun hc => by cases hc), fun _ _ => hok_in rfl, ?_, ?_, hm'⟩
                  · intro vals' te' hst
                    obtain ⟨_, _, hpr_z, hnc_z, hwh_z, htr⟩ := hsat_tr vals' te' hst
                    rw [hsub_eq] at htr
                    cases htr with
                    | step hl hpc_s hv0 htr_next =>
                      rw [hpc1] at hpc_s
                      rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, hreq⟩
                      obtain ⟨_, hvs, htes, hprs, hncs, hwhs⟩ := hunit_ok _ hl hcl_eq hv0
                      refine ⟨rfl, rfl, by rw [hprs, hpr_z], by rw [hncs, hnc_z],
                        by rw [hwhs, hwh_z], ?_⟩
                      rw [hvs, htes, hdrop, hreq]; exact htr_next
                  · intro hut
                    refine ⟨rfl, Or.inl ⟨rfl, ?_⟩⟩
                    rcases (huns_tr hut).2 with ⟨_, htr⟩ | ⟨ht, _⟩
                    · rw [hsub_eq] at htr
                      cases htr with
                      | conflict hl hpc_s hvf _ =>
                        rw [hpc1] at hpc_s
                        rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
                        have hr2 := hunit_fl _ hl hcl_eq hvf; cases hr2
                      | step hl hpc_s hv0 htr_next =>
                        rw [hpc1] at hpc_s
                        rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, hreq⟩
                        obtain ⟨_, hvs, _, _, _, _⟩ := hunit_ok _ hl hcl_eq hv0
                        rw [hvs, hdrop, hreq]; exact htr_next
                    · rw [huns_f] at ht; cases ht
                · -- r_in = 2#64: unsat_seen := true
                  subst hu' ho'
                  refine hJb (true, false, ()) m' ⟨j, accCnf.add cl, st', hj, hdcur', hlen', hcl',
                    by rw [hfu', hfu_st], hpos_next, hpc_next,
                    fun _ => huns_in rfl, (fun hc => by cases hc), ?_, ?_, hm'⟩
                  · intro vals' te' hst
                    have htr := (hsat_tr vals' te' hst).2.2.2.2.2
                    rw [hsub_eq] at htr
                    cases htr with
                    | step hl hpc_s hv0 _ =>
                      rw [hpc1] at hpc_s
                      rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
                      have hr1 := (hunit_ok _ hl hcl_eq hv0).1; cases hr1
                  · intro hut
                    refine ⟨rfl, Or.inr ⟨rfl, ?_⟩⟩
                    rcases (huns_tr hut).2 with ⟨_, htr⟩ | ⟨ht, _⟩
                    · rw [hsub_eq] at htr
                      cases htr with
                      | conflict _ hpc_s _ hrest =>
                        rw [hpc1] at hpc_s
                        rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨_, hreq⟩
                        rwa [hdrop, hreq]
                      | step hl hpc_s hv0 _ =>
                        rw [hpc1] at hpc_s
                        rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
                        have hr1 := (hunit_ok _ hl hcl_eq hv0).1; cases hr1
                    · rw [huns_f] at ht; cases ht
                · -- r_in = 3#64: oom_seen := true
                  subst hu' ho'
                  refine hJb (false, true, ()) m' ⟨j, accCnf.add cl, st', hj, hdcur', hlen', hcl',
                    by rw [hfu', hfu_st], hpos_next, hpc_next,
                    (fun hc => by cases hc), (fun _ hc => by cases hc), ?_, ?_, hm'⟩
                  · intro vals' te' hst
                    have htr := (hsat_tr vals' te' hst).2.2.2.2.2
                    rw [hsub_eq] at htr
                    cases htr with
                    | step hl hpc_s hv0 _ =>
                      rw [hpc1] at hpc_s
                      rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
                      have hr1 := (hunit_ok _ hl hcl_eq hv0).1; cases hr1
                  · intro hut
                    rcases (huns_tr hut).2 with ⟨_, htr⟩ | ⟨ht, _⟩
                    · rw [hsub_eq] at htr
                      cases htr with
                      | conflict hl hpc_s hvf _ =>
                        rw [hpc1] at hpc_s
                        rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
                        have hr2 := hunit_fl _ hl hcl_eq hvf; cases hr2
                      | step hl hpc_s hv0 _ =>
                        rw [hpc1] at hpc_s
                        rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
                        have hr1 := (hunit_ok _ hl hcl_eq hv0).1; cases hr1
                    · rw [huns_f] at ht; cases ht)
              (fun J1 hJ1 => by
                wp_unfold
                refine ⟨fun hr2 => hJ1 (true, oom_v, ()) m'
                    ⟨by simp [hr2], by rw [hoom_f, hr2]; decide, rfl⟩,
                  fun hrne2 => ?_⟩
                refine wp_join_group
                  (fun (o', ()) m_j => o' = decide (r_in = 3#64) ∧ m_j = m')
                  (fun _ ⟨o', ⟨⟩⟩ m_j ⟨ho', hm_j⟩ => by
                    subst m_j; wp_unfold
                    have hne2' : r_in ≠ 2#64 := hrne2
                    exact hJ1 (unsat_v, o', ()) m' ⟨by simp [huns_f, hne2'], ho', rfl⟩)
                  (fun J2 hJ2 => by
                    wp_unfold
                    exact ⟨fun hr3 => hJ2 (true, ()) m' ⟨by simp [hr3], rfl⟩,
                      fun hrne3 => by
                        have hne3' : r_in ≠ 3#64 := hrne3
                        exact hJ2 (oom_v, ()) m' ⟨by simp [hoom_f, hne3'], rfl⟩⟩))
    · -- Loop done: i = c.nc
      have hieq : i = c.nc := by omega
      subst hieq
      simp only [Nat.sub_self, parseClauses] at hpc_eq
      refine ⟨fun hoom_t => ?_, fun hoom_f => ?_⟩
      · exact hQ 0#64 st ml hlen_st (Or.inl rfl) hfu_st
          (fun h => by cases h) (fun h => by cases h)
          (fun vals' te' hst => by
            have h2 := (hsat_tr vals' te' hst).2.1; rw [hoom_t] at h2; cases h2)
          (fun hut => by
            have h1 := (huns_tr hut).1; rw [hoom_t] at h1; cases h1) hml
      · refine ⟨_, load_arena_cur hml_a, ?_⟩
        apply wp_call_of_spec; apply hSwc
        refine ⟨cnf_ptr, cnfBytes, idx, ArenaMem c st ⋆ R, hdcur_st, rfl, hfit, hidx, sep_ac hml,
          fun j _ hj hsw => ?_⟩
        wp_unfold
        obtain ⟨okc, hmc⟩ := store_arena_cur (cnf_ptr + BitVec.ofNat 64 j) hml_a
        refine ⟨okc, _, load_arena_cur hmc, ?_⟩
        rw [cursor_eq_iff (by omega) (by omega)]
        let sf : ArenaState := { st with d_cur := cnf_ptr + BitVec.ofNat 64 j }
        have hlen_sf : sf.LengthsOk c := lengthsOk_d_update hlen_st
        have hmf : (bytes cnf_ptr cnfBytes ⋆ ArenaMem c sf ⋆ R) _ := sep_ac hmc
        refine ⟨fun hne => ?_, fun heq => ?_⟩
        · have hne_emp : (skipWsComments (cnfBytes.drop idx)).isEmpty = false := by
            rw [← hsw, List.drop_eq_getElem_cons (by omega : j < cnfBytes.length)]; rfl
          exact hQ 0#64 sf _ hlen_sf (Or.inl rfl) hfu_st
            (fun h => by cases h) (fun h => by cases h)
            (fun vals' te' hst => by
              have htr := (hsat_tr vals' te' hst).2.2.2.2.2
              rw [Nat.sub_self] at htr
              cases htr with
              | done hemp => rw [hne_emp] at hemp; cases hemp)
            (fun hut => by
              rcases (huns_tr hut).2 with ⟨_, htr⟩ | ⟨_, cnf_r, hr⟩
              · rw [Nat.sub_self] at htr; cases htr
              · rw [Nat.sub_self] at hr
                simp only [parseClauses, hne_emp, Bool.false_eq_true, ↓reduceIte] at hr; cases hr)
            hmf
        · have hemp : (skipWsComments (cnfBytes.drop idx)).isEmpty = true := by
            rw [← hsw, heq]; simp
          have hpd_some : parseDimacs cnfBytes = some accCnf := by
            rw [← hpc_eq]; simp [hemp]
          refine ⟨fun huns_t => ?_, fun huns_f => ?_⟩
          · exact hQ 20#64 sf _ hlen_sf (Or.inr (Or.inr rfl)) hfu_st
              (fun _ => ⟨accCnf, hpd_some, shiftDownCnf_unsat hpos (huns_inv huns_t)⟩)
              (fun h => by cases h)
              (fun vals' te' hst => by
                have h1 := (hsat_tr vals' te' hst).1; rw [huns_t] at h1; cases h1)
              (fun _ => rfl) hmf
          · have hinv_sf : SolverInv c (shiftDownCnf accCnf) sf :=
              solverInv_d_update (hok_inv huns_f hoom_f)
            exact hQ 1#64 sf _ hlen_sf (Or.inr (Or.inl rfl)) hfu_st
              (fun h => by cases h)
              (fun _ => ⟨accCnf, hpd_some, hinv_sf, hcl_st⟩)
              (fun vals' te' hst => by
                obtain ⟨_, _, hpr_z, hnc_z, hwh_z, htr⟩ := hsat_tr vals' te' hst
                rw [Nat.sub_self] at htr
                cases htr with
                | done _ => exact ⟨rfl, rfl, rfl, hpr_z, hnc_z, hwh_z⟩)
              (fun hut => by
                rcases (huns_tr hut).2 with ⟨_, htr⟩ | ⟨ht, _⟩
                · rw [Nat.sub_self] at htr; cases htr
                · rw [huns_f] at ht; cases ht)
              hmf
  · intro L hL; wp_unfold
    exact hL c.nc _ m
      ⟨0, i0, CNF.empty, s, Nat.zero_le _, by simp, rfl, hi0, hdcur, hinv0.core.lengths,
        hcl0, rfl, cnfVarsPos_empty, by simpa using hpd_init,
        (fun hc => by cases hc), fun _ _ => hinv0,
        fun vals' te' hst => ⟨rfl, rfl, hpr0, hnc0, rfl, by simpa [hte0] using hst⟩,
        fun hut => ⟨rfl, Or.inl ⟨rfl, by simpa using hut⟩⟩, hm⟩

end LeanQbe.T.Examples.Kissat
