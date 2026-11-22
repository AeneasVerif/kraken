module

public import LeanQbe.T.Examples.Kissat.FullM5CongBins
public import LeanQbe.T.Examples.Kissat.FullM3CongBvaLemmas4
public import LeanQbe.T.Examples.Kissat.FullDefSweepLemmas1
public import LeanQbe.T.Examples.Kissat.FullOneLitConflLemmas

/-!
# Kissat `D-Full` M5 Dense Binary Extraction Specs & `Func.wp` Proofs (`FullM5CongBinsLemmas`)

Proves parametric `(Γ : Env)` `Func.wp` contracts for all `3` C0 functions in
`FullM5CongBins.lean`:
1. `full_cong_eb_match` (`full_cong_eb_match_wp` against `m5CongEbMatchSpec`)
2. `full_cong_extract_binaries` (`full_cong_extract_binaries_wp` against
   `m5CongExtractBinariesSpec`, proving binary resolution soundness `(a ∨ b ∨ c)` +
   `(¬a ∨ b)/(¬a ∨ c)` ⇒ `(b ∨ c)` via `Clause.entails`, `FullDenseInv` preservation, and
   `r = 20#64 → F0.Unsat`)
3. `full_congruence_dense` (`m5_congruence_dense_wp` against exact unchanged
   `FullM3CongBva.m3CongruenceDenseSpec` and `m5_defsweep_congruence_dense_wp` against
   `FullDefSweep.fullCongruenceDenseSpec`)
4. Closed `8`-row `m5CongBinsModule` verification (`m5CongBins_moduleOk`) and concrete `Mem 64`
   non-vacuity theorems (`XPost := False`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM5CongBins

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open LeanQbe.T.Examples.Kissat.FullM3CongBva hiding
  full_congruence_dense full_congruence_dense_body full_congruence_dense_wf
open Kraken.Bedrock2.Test

/-! ## 1. `Spec` Contracts & Pure Resolution Soundness Helpers -/

section SpecsAndHelpers

/-- `full_cong_eb_match(h, x, l, k)`: checks whether `(¬x ∨ l)` or `(¬x ∨ k)` is a binary
watch in `h`, returning `true` only when one of the two binary clauses is semantically entailed
by `cnfOfClauses F_cur` and all literals are in `[0 ..< 2 * cur_vars)`. -/
def m5CongEbMatchSpec : Spec [i64, i32, i32, i32] [.bool] := fun (h, x, l, k, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ (FullMem c s ⋆ R) m ∧
    ∀ ok : Bool,
      (ok = true →
        (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg x.toNat, l.toNat]) ∨
        (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg x.toNat, k.toNat])) →
      Q (ok, ()) m

/-- `full_cong_extract_binaries(h)`: scans irredundant unassigned ternary clauses before
`full_cong_extract`, resolving against existing binary watches to add strengthened binaries
while preserving `FullDenseInv`, `cur_vars`, and `fuel`, and returning `1#64` or `20#64`
(`F0.Unsat`). -/
def m5CongExtractBinariesSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInv c F0 s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

theorem entails_resolve_ternary_pair {F : CNF Nat} {x l k : Nat}
    (hTri : F.EntailsClause (cnfClause [x, l, k]))
    (hBin : F.EntailsClause (cnfClause [litNeg x, l]) ∨
      F.EntailsClause (cnfClause [litNeg x, k])) :
    F.EntailsClause (cnfClause [l, k]) := by
  rw [CNF.entails_clause_def]
  intro α hα
  have h3 := (CNF.entails_clause_def.mp hTri) α hα
  rw [← clauseEvalVal_iff, clauseEvalVal] at h3 ⊢
  simp only [List.any_cons, List.any_nil, Bool.or_false] at h3 ⊢
  cases hx : evalLitVal α x
  · simpa [hx] using h3
  · rcases hBin with hl | hk
    · have h2 := (CNF.entails_clause_def.mp hl) α hα
      rw [← clauseEvalVal_iff, clauseEvalVal] at h2
      simp only [List.any_cons, List.any_nil, Bool.or_false, evalLitVal_litNeg, hx,
        Bool.not_true, Bool.false_or] at h2
      simp [h2]
    · have h2 := (CNF.entails_clause_def.mp hk) α hα
      rw [← clauseEvalVal_iff, clauseEvalVal] at h2
      simp only [List.any_cons, List.any_nil, Bool.or_false, evalLitVal_litNeg, hx,
        Bool.not_true, Bool.false_or] at h2
      simp [h2]

theorem entails_ternary_perm01 {F : CNF Nat} {a b c : Nat}
    (h : F.EntailsClause (cnfClause [a, b, c])) :
    F.EntailsClause (cnfClause [b, a, c]) := by
  rw [CNF.entails_clause_def]
  intro α hα
  have h' := (CNF.entails_clause_def.mp h) α hα
  rw [← clauseEvalVal_iff, clauseEvalVal] at h' ⊢
  simp only [List.any_cons, List.any_nil, Bool.or_false] at h' ⊢
  cases ha : evalLitVal α a <;> cases hb : evalLitVal α b <;> cases hc : evalLitVal α c <;>
    simp [ha, hb, hc] at h' ⊢

theorem entails_ternary_perm02 {F : CNF Nat} {a b c : Nat}
    (h : F.EntailsClause (cnfClause [a, b, c])) :
    F.EntailsClause (cnfClause [c, a, b]) := by
  rw [CNF.entails_clause_def]
  intro α hα
  have h' := (CNF.entails_clause_def.mp h) α hα
  rw [← clauseEvalVal_iff, clauseEvalVal] at h' ⊢
  simp only [List.any_cons, List.any_nil, Bool.or_false] at h' ⊢
  cases ha : evalLitVal α a <;> cases hb : evalLitVal α b <;> cases hc : evalLitVal α c <;>
    simp [ha, hb, hc] at h' ⊢

private theorem fullDenseInvW_after_addBin' {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' wvec' wstk' wsort' : List (BitVec 32)}
    {te' wlen' : Nat} {unass' unfl' wu' nb' oom' inc' : BitVec 64} {phases' : List (BitVec 8)}
    (s' : FullState)
    (hs'_def : s' =
      { s with
        core :=
          { s.core with
            vals := vals', flags := flags', lvl := lvl', rsns := rsns',
            trl := trl', trail_pos := tp', trail_end := te', unassigned := unass',
            unflushed := unfl',
            wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
            oom := oom', inconsistent := inc' }
        scratch := { s.scratch with phases := phases', wsort := wsort' } })
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core) :
    FullDenseInvW c F0 F_cur s' := by
  subst hs'_def
  refine ⟨hlen', hw', h.2.2.1, ?_, ?_, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
    exact h.2.2.2.1
  · exact h.2.2.2.2.1.of_pres ⟨rfl, rfl⟩ fun r hr => hr

private theorem fullDenseInvW_with_oom0 {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (h : FullDenseInvW c F0 F_cur s) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with oom := 0#64 } } := by
  refine ⟨⟨{ h.1.core_ok with vals_len := h.1.core_ok.vals_len }, h.1.scratch_ok⟩,
    { h.2.1 with
      arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
      watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
    h.2.2.1, ?_, ?_, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
    exact h.2.2.2.1
  · exact h.2.2.2.2.1.of_pres ⟨rfl, rfl⟩ fun r hr => hr

end SpecsAndHelpers

/-! ## 2. `full_cong_eb_match_wp` -/

section EbMatchProof

open scoped FullArenaTactics FullCongTactics M3HeadTactics

/-- `full_cong_eb_match(h, x, l, k)` returns `true` only when either `(¬x ∨ l)` or `(¬x ∨ k)`
is entailed by `cnfOfClauses F_cur`. -/
theorem full_cong_eb_match_wp (Γ : Env)
    (hHasBin : ∀ a m Q X, fullHasBinSpec a m Q X →
      Γ "full_has_bin" [i64, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, m5CongEbMatchSpec a m Q X → Func.wp Γ full_cong_eb_match_body a m Q X := by
  rintro ⟨h, x, l, k, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hm0, hQ⟩
  unfold Func.wp full_cong_eb_match_body
  m3_to_group
  refine wp_join_group (ts := [.bool])
    (fun (ok, ()) m1 => m1 = m0 ∧
      (ok = true →
        (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg x.toNat, l.toNat]) ∨
        (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg x.toNat, k.toNat])))
    (fun _ (ok, ⟨⟩) m1 ⟨hm1, hok⟩ => by
      subst m1; m3_steps; exact hQ ok hok)
    ?_
  intro J hJ
  m3_steps
  m3_call hHasBin
  refine ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hm0, fun ok1 hok1 => ?_⟩
  m3_split_fast
  · m3_let
    refine hJ (true, ()) m0 ⟨rfl, fun _ => Or.inl ?_⟩
    simpa only [bv32_xor1_litNeg] using (hok1 hc).2.2.2.2
  · clear hc
    m3_steps
    m3_call hHasBin
    refine ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hm0, fun ok2 hok2 => ?_⟩
    m3_split_fast
    · m3_let
      refine hJ (true, ()) m0 ⟨rfl, fun _ => Or.inr ?_⟩
      simpa only [bv32_xor1_litNeg] using (hok2 hc).2.2.2.2
    · m3_let
      exact hJ (false, ()) m0 ⟨rfl, fun h => by cases h⟩

end EbMatchProof

/-! ## 3. `full_cong_extract_binaries_wp` -/

section ExtractBinariesProof

open scoped FullArenaTactics FullCongTactics M3HeadTactics

private theorem arena_clause3_lits_eq {k : FullCoreState} {cr : Nat}
    (hsz : fullArenaClauseSizeCore k cr = 3) (hbd : cr + 6 ≤ k.arena.length) :
    fullArenaClauseLitsCore k cr =
      [(k.arena[cr + 3]'(by omega)).toNat,
       (k.arena[cr + 4]'(by omega)).toNat,
       (k.arena[cr + 5]'(by omega)).toNat] :=
  arena_clause3_lits hsz hbd

/-- `full_cong_extract_binaries(h)`: scans irredundant unassigned ternary clauses in `arena`
before `full_cong_extract`, deducing strengthened binaries via resolution with existing binary
watches and preserving `FullDenseInv`, `cur_vars`, and `fuel`. -/
theorem full_cong_extract_binaries_wp (Γ : Env)
    (hNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hHasBin : ∀ a m Q X, fullHasBinSpec a m Q X →
      Γ "full_has_bin" [i64, i32, i32] [.bool] a m Q X)
    (hEbMatch : ∀ a m Q X, m5CongEbMatchSpec a m Q X →
      Γ "full_cong_eb_match" [i64, i32, i32, i32] [.bool] a m Q X)
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X) :
    ∀ a m Q X, m5CongExtractBinariesSpec a m Q X →
      Func.wp Γ full_cong_extract_binaries_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m0 Q X ⟨c, F0, s0, R, rfl, hden0, hm0, hQ⟩
  have hac := c.harena; have hmx := c.hmaxv; unfold dimacsBound at hac hmx
  obtain ⟨F_cur, hw0⟩ := hden0.1.witness
  have hdenw0 : FullDenseInvW c F0 F_cur s0 :=
    ⟨hden0.1.lengths, hw0, hden0.2.1, hden0.2.2.1, hden0.2.2.2.1, hden0.2.2.2.2.1,
      hden0.2.2.2.2.2⟩
  let cv0 := s0.core.cur_vars
  let fuel0 := s0.core.fuel
  let ar0 := s0.core.arena
  let alen0 := s0.core.arena_len
  unfold Func.wp full_cong_extract_binaries_body
  m3_split_fast
  · have hinc0 : s0.core.inconsistent ≠ 0#64 := bne_iff_ne.mp hc
    m3_steps
    exact hQ 20#64 s0 m0 hden0 rfl rfl (Or.inr rfl)
      (fun _ => unsat_of_inconsistent_w hw0 hinc0) hm0
  · clear hc; m3_to_group
    refine wp_loop_break_group (brkTs := [i64]) (lpTs := [i64])
      (fun _ mb => ∃ sb : FullState,
        FullDenseInvW c F0 F_cur sb ∧ sb.core.cur_vars = cv0 ∧ sb.core.fuel = fuel0 ∧
        (FullMem c sb ⋆ R) mb)
      (fun rem (p, ()) ml => ∃ sl : FullState,
        FullDenseInvW c F0 F_cur sl ∧ sl.core.cur_vars = cv0 ∧ sl.core.fuel = fuel0 ∧
        sl.core.arena = ar0 ∧ sl.core.arena_len = alen0 ∧
        p.toNat ≤ alen0 ∧ rem = alen0 - p.toNat ∧
        (p.toNat = alen0 ∨ p.toNat ∈ fullArenaClauseRefs sl) ∧
        (FullMem c sl ⋆ R) ml)
      ?_ ?_ ?_
    · rintro _ ⟨p_b, ⟨⟩⟩ mb ⟨sb, hdenb, hcvb, hfub, hmb⟩
      m3_to_group
      refine wp_join_group (ts := [i64])
        (fun (r, ()) m' => m' = mb ∧ (r = 20#64 ∧ sb.core.inconsistent ≠ 0#64 ∨ r = 1#64))
        (fun _ (r, ⟨⟩) m' ⟨hm', hr⟩ => by
          subst m'; m3_steps
          rcases hr with ⟨rfl, hincb⟩ | rfl
          · exact hQ 20#64 sb mb hdenb.toDense hcvb hfub (Or.inr rfl)
              (fun _ => unsat_of_inconsistent_w hdenb.2.1 hincb) hmb
          · exact hQ 1#64 sb mb hdenb.toDense hcvb hfub (Or.inl rfl) (fun h => by cases h) hmb)
        ?_
      intro Jret hJret
      m3_split_fast
      · m3_let; exact hJret (20#64, ()) mb ⟨rfl, Or.inl ⟨rfl, bne_iff_ne.mp hc⟩⟩
      · m3_let; exact hJret (1#64, ()) mb ⟨rfl, Or.inr rfl⟩
    · rintro B L rem ⟨p, ⟨⟩⟩ ml hB hL ⟨sl, hdenl, hcvl, hful, harl_eq, hal_eq, hp_le, rfl,
          hp_mem, hml⟩
      have hcv_le := hdenl.1.core_ok.cur_vars_le
      have har_len := hdenl.1.core_ok.arena_len_arr
      have hale := hdenl.1.core_ok.arena_len_le
      m3_split_fast
      · have hp_lt : p.toNat < alen0 := by
          have hlt := bv64_ult_lt hc
          change p.toNat < (BitVec.ofNat 64 alen0).toNat at hlt
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hlt
          exact hlt
        clear hc
        have hp_ref : p.toNat ∈ fullArenaClauseRefs sl := hp_mem.resolve_left (by omega)
        have hp_wf := hdenl.2.1.arena.refs_wf p.toNat hp_ref
        have hp2_n : (p + 2#64).toNat = p.toNat + 2 := by bv_omega
        have hp_arr : p.toNat < sl.core.arena.length := by omega
        have hp2_arr : (p + 2#64).toNat < sl.core.arena.length := by omega
        have hp_tr : (p.setWidth 32).toNat = p.toNat := by
          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
        have hnp_bd := fullArenaNextOff_bounds (ar := sl.core.arena) (alen := sl.core.arena_len)
          (cref := p.toNat) (by omega)
        m3_steps; m3_call hNext
        refine ⟨c, sl, R, rfl, hdenl.1, hml, ?_⟩
        let np_bv := (BitVec.ofNat 32 (fullArenaNextOff sl.core.arena sl.core.arena_len
          (p.setWidth 32).toNat)).setWidth 64
        have hnp_n : np_bv.toNat = fullArenaNextOff sl.core.arena sl.core.arena_len p.toNat := by
          dsimp only [np_bv]; rw [hp_tr, bv_zext32_toNat, bv32_ofNat_toNat (by omega)]
        have hnp_mem : np_bv.toNat = alen0 ∨ np_bv.toNat ∈ fullArenaClauseRefs sl := by
          rw [hnp_n, ← hal_eq]; exact fullArenaClauseRefs_next_or_end hdenl.2.1 hp_ref
        have hnp_gt : p.toNat < np_bv.toNat := by omega
        have hnp_le : np_bv.toNat ≤ alen0 := by omega
        m3_to_group
        refine wp_join_group (ts := [])
          (fun () mn => ∃ sn : FullState,
            FullDenseInvW c F0 F_cur sn ∧ sn.core.cur_vars = cv0 ∧ sn.core.fuel = fuel0 ∧
            sn.core.arena = ar0 ∧ sn.core.arena_len = alen0 ∧
            (np_bv.toNat = alen0 ∨ np_bv.toNat ∈ fullArenaClauseRefs sn) ∧
            (FullMem c sn ⋆ R) mn)
          ?_ ?_
        · rintro _ ⟨⟩ mn ⟨sn, hdenn, hcvn, hfun, harn, haln, hnpm, hmn⟩
          m3_let
          exact hL (alen0 - np_bv.toNat) (np_bv, ()) mn (by omega)
            ⟨sn, hdenn, hcvn, hfun, harn, haln, hnp_le, rfl, hnpm, hmn⟩
        · intro Jnp hJnp
          have hskip : Jnp () ml :=
            hJnp () ml ⟨sl, hdenl, hcvl, hful, harl_eq, hal_eq, hnp_mem, hml⟩
          m3_split_fast
          · have hng_red := beq_iff_eq.mp hc; clear hc
            m3_split_fast
            · have hsz_bv : sl.core.arena[(p + 2#64).toNat]'hp2_arr = 3#32 := by
                simpa using beq_iff_eq.mp hc
              clear hc
              have hng : fullArenaClauseGarb sl p.toNat = false := by
                unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
                rw [List.getElem?_eq_getElem hp_arr, Option.getD_some]
                exact garb_false_of_and_480000 hng_red
              have hsz_bv_p2 : sl.core.arena[(p + 2#64).toNat]'hp2_arr =
                  sl.core.arena[p.toNat + 2]'(by omega) :=
                list_getElem_congr hp2_n hp2_arr (by omega)
              have hsz3_n : fullArenaClauseSizeCore sl.core p.toNat = 3 := by
                unfold fullArenaClauseSizeCore
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some, ← hsz_bv_p2, hsz_bv]
                rfl
              have har_bd : p.toNat + 6 ≤ sl.core.arena.length := by omega
              have hlits3 := arena_clause3_lits_eq hsz3_n har_bd
              have hcl3 := hdenl.2.1.arena.entails p.toNat hp_ref hng
              have hlt3 := hdenl.2.1.arena.lits_lt p.toNat hp_ref hng
              unfold fullArenaClauseLits at hcl3 hlt3; rw [hlits3] at hcl3 hlt3
              have hp3_n : (p + 3#64).toNat = p.toNat + 3 := by bv_omega
              have hp4_n : (p + 4#64).toNat = p.toNat + 4 := by bv_omega
              have hp5_n : (p + 5#64).toNat = p.toNat + 5 := by bv_omega
              let a := sl.core.arena[(p + 3#64).toNat]'(by omega)
              let b := sl.core.arena[(p + 4#64).toNat]'(by omega)
              let c_lit := sl.core.arena[(p + 5#64).toNat]'(by omega)
              have ha_eq : a = sl.core.arena[p.toNat + 3]'(by omega) :=
                list_getElem_congr hp3_n (by omega) (by omega)
              have hb_eq : b = sl.core.arena[p.toNat + 4]'(by omega) :=
                list_getElem_congr hp4_n (by omega) (by omega)
              have hc_eq : c_lit = sl.core.arena[p.toNat + 5]'(by omega) :=
                list_getElem_congr hp5_n (by omega) (by omega)
              have ha_lt : a.toNat < 2 * sl.core.cur_vars := by
                rw [ha_eq]; exact hlt3 _ (by simp)
              have hb_lt : b.toNat < 2 * sl.core.cur_vars := by
                rw [hb_eq]; exact hlt3 _ (by simp)
              have hc_lt : c_lit.toNat < 2 * sl.core.cur_vars := by
                rw [hc_eq]; exact hlt3 _ (by simp)
              have hcl3' : (cnfOfClauses F_cur).EntailsClause
                  (cnfClause [a.toNat, b.toNat, c_lit.toNat]) := by
                rwa [ha_eq, hb_eq, hc_eq]
              have hva_len : (a.setWidth 64).toNat < sl.core.vals.length := by
                rw [bv_zext32_toNat, hdenl.1.core_ok.vals_len]; omega
              have hvb_len : (b.setWidth 64).toNat < sl.core.vals.length := by
                rw [bv_zext32_toNat, hdenl.1.core_ok.vals_len]; omega
              have hvc_len : (c_lit.setWidth 64).toNat < sl.core.vals.length := by
                rw [bv_zext32_toNat, hdenl.1.core_ok.vals_len]; omega
              m3_to_group
              refine wp_join_group (ts := [])
                (fun () mn => ∃ sn : FullState,
                  FullDenseInvW c F0 F_cur sn ∧ sn.core.cur_vars = cv0 ∧
                  sn.core.fuel = fuel0 ∧ sn.core.arena = ar0 ∧ sn.core.arena_len = alen0 ∧
                  (np_bv.toNat = alen0 ∨ np_bv.toNat ∈ fullArenaClauseRefs sn) ∧
                  (FullMem c sn ⋆ R) mn)
                (fun _ ⟨⟩ mn hmn => by m3_let; exact hJnp () mn hmn)
                ?_
              intro Jnp2 hJnp2
              have hskip2 : Jnp2 () ml :=
                hJnp2 () ml ⟨sl, hdenl, hcvl, hful, harl_eq, hal_eq, hnp_mem, hml⟩
              m3_split_fast
              · clear hc; m3_split_fast
                · clear hc; m3_split_fast
                  · clear hc
                    m3_to_group
                    refine wp_join_group (ts := [i32, i32, .bool])
                      (fun (l_m, k_m, found, ()) mm => mm = ml ∧
                        (found = true → l_m.toNat < 2 * cv0 ∧ k_m.toNat < 2 * cv0 ∧
                          (cnfOfClauses F_cur).EntailsClause (cnfClause [l_m.toNat, k_m.toNat])))
                      ?_ ?_
                    · rintro _ ⟨l_m, k_m, found, ⟨⟩⟩ mm ⟨hmm, hfd⟩
                      subst mm
                      m3_to_group
                      refine wp_join_group (ts := [])
                        (fun () mn => ∃ sn : FullState,
                          FullDenseInvW c F0 F_cur sn ∧ sn.core.cur_vars = cv0 ∧
                          sn.core.fuel = fuel0 ∧ sn.core.arena = ar0 ∧
                          sn.core.arena_len = alen0 ∧
                          (np_bv.toNat = alen0 ∨ np_bv.toNat ∈ fullArenaClauseRefs sn) ∧
                          (FullMem c sn ⋆ R) mn)
                        (fun _ ⟨⟩ mn hmn => by m3_let; exact hJnp2 () mn hmn)
                        ?_
                      intro Jnp3 hJnp3
                      have hskip3 : Jnp3 () ml :=
                        hJnp3 () ml ⟨sl, hdenl, hcvl, hful, harl_eq, hal_eq, hnp_mem, hml⟩
                      m3_split_fast
                      · obtain ⟨hl_lt, hk_lt, hent_lk⟩ := hfd hc
                        clear hc; m3_steps; m3_call hHasBin
                        refine ⟨c, F0, F_cur, sl, R, rfl, hdenl.1, hdenl.2.1, hml,
                          fun has_lk _ => ?_⟩
                        m3_split_fast
                        · clear hc; m3_let; exact hskip3
                        · clear hc; m3_steps; m3_call hAddBin
                          refine ⟨c, F0, F_cur, sl, R, rfl, hdenl.1, hdenl.2.1,
                            hdenl.2.2.2.2.2.1, fun _ _ => hent_lk, hml, ?_⟩
                          intro st vals1 flags1 lvl1 rsns1 trl1 tp1 te1 unass1 unfl1 wvec1 wstk1
                            wlen1 wu1 nb1 oom1 inc1 phases1 wsort1 m1 _ hlen1 hw1 _hdom hr_uns
                            _hroom hm1
                          let s1 : FullState :=
                            { sl with
                              core := { sl.core with
                                vals := vals1, flags := flags1, lvl := lvl1, rsns := rsns1,
                                trl := trl1, trail_pos := tp1, trail_end := te1,
                                unassigned := unass1, unflushed := unfl1,
                                wvec := wvec1, wstk := wstk1, wlen := wlen1, wusable := wu1,
                                num_binary := nb1, oom := oom1, inconsistent := inc1 }
                              scratch := { sl.scratch with phases := phases1, wsort := wsort1 } }
                          have hden1 := fullDenseInvW_after_addBin' hdenl s1 rfl hlen1 hw1
                          have hcv1' : s1.core.cur_vars = cv0 := hcvl
                          have hfu1' : s1.core.fuel = fuel0 := hful
                          have har1' : s1.core.arena = ar0 := harl_eq
                          have hal1' : s1.core.arena_len = alen0 := hal_eq
                          have hnpm1 : np_bv.toNat = alen0 ∨
                              np_bv.toNat ∈ fullArenaClauseRefs s1 := by
                            unfold fullArenaClauseRefs fullArenaClauseRefsCore
                            rw [har1', hal1']
                            simpa only [harl_eq, hal_eq, fullArenaClauseRefs,
                              fullArenaClauseRefsCore] using hnp_mem
                          m3_split_fast
                          · have h20 : st = 20#64 := beq_iff_eq.mp hc
                            m3_steps
                            exact hQ 20#64 s1 m1 hden1.toDense hcv1' hfu1' (Or.inr rfl)
                              (fun _ => (hr_uns h20).1) hm1
                          · clear hc; m3_split_fast
                            · clear hc; m3_steps
                              let s1z := { s1 with core := { s1.core with oom := 0#64 } }
                              exact hB (p, ()) m
                                ⟨s1z, fullDenseInvW_with_oom0 hden1, hcv1', hfu1', hm⟩
                            · clear hc; m3_let
                              exact hJnp3 () m1 ⟨s1, hden1, hcv1', hfu1', har1', hal1', hnpm1, hm1⟩
                      · clear hc; m3_let; exact hskip3
                    · intro Jf hJf
                      m3_steps; m3_call hEbMatch
                      refine ⟨c, F0, F_cur, sl, R, rfl, hdenl.1, hdenl.2.1, hml,
                        fun ok1 hok1 => ?_⟩
                      m3_split_fast
                      · have hent_bc := entails_resolve_ternary_pair hcl3' (hok1 hc)
                        m3_steps
                        exact hJf (b, c_lit, true, ()) ml ⟨rfl, fun _ =>
                          ⟨hcvl ▸ hb_lt, hcvl ▸ hc_lt, hent_bc⟩⟩
                      · clear hc
                        m3_to_group
                        refine wp_join_group (ts := [i32, i32, .bool])
                          (fun (l_m, k_m, found, ()) mm => mm = ml ∧
                            (found = true → l_m.toNat < 2 * cv0 ∧ k_m.toNat < 2 * cv0 ∧
                              (cnfOfClauses F_cur).EntailsClause
                                (cnfClause [l_m.toNat, k_m.toNat])))
                          (fun _ x mm h => by m3_let; exact hJf x mm h)
                          ?_
                        intro Jf2 hJf2
                        m3_steps; m3_call hEbMatch
                        refine ⟨c, F0, F_cur, sl, R, rfl, hdenl.1, hdenl.2.1, hml,
                          fun ok2 hok2 => ?_⟩
                        m3_split_fast
                        · have hent_ac := entails_resolve_ternary_pair
                            (entails_ternary_perm01 hcl3') (hok2 hc)
                          m3_steps
                          exact hJf2 (a, c_lit, true, ()) ml ⟨rfl, fun _ =>
                            ⟨hcvl ▸ ha_lt, hcvl ▸ hc_lt, hent_ac⟩⟩
                        · clear hc
                          m3_to_group
                          refine wp_join_group (ts := [i32, i32, .bool])
                            (fun (l_m, k_m, found, ()) mm => mm = ml ∧
                              (found = true → l_m.toNat < 2 * cv0 ∧ k_m.toNat < 2 * cv0 ∧
                                (cnfOfClauses F_cur).EntailsClause
                                  (cnfClause [l_m.toNat, k_m.toNat])))
                            (fun _ x mm h => by m3_let; exact hJf2 x mm h)
                            ?_
                          intro Jf3 hJf3
                          m3_steps; m3_call hEbMatch
                          refine ⟨c, F0, F_cur, sl, R, rfl, hdenl.1, hdenl.2.1, hml,
                            fun ok3 hok3 => ?_⟩
                          m3_split_fast
                          · have hent_ab := entails_resolve_ternary_pair
                              (entails_ternary_perm02 hcl3') (hok3 hc)
                            m3_steps
                            exact hJf3 (a, b, true, ()) ml ⟨rfl, fun _ =>
                              ⟨hcvl ▸ ha_lt, hcvl ▸ hb_lt, hent_ab⟩⟩
                          · clear hc; m3_steps
                            exact hJf3 (0#32, 0#32, false, ()) ml ⟨rfl, fun h => by cases h⟩
                  · clear hc; m3_let; exact hskip2
                · clear hc; m3_let; exact hskip2
              · clear hc; m3_let; exact hskip2
            · clear hc; m3_let; exact hskip
          · clear hc; m3_let; exact hskip
      · clear hc; m3_let; exact hB (p, ()) ml ⟨sl, hdenl, hcvl, hful, hml⟩
    · intro _ Lp _ hLp
      m3_steps
      refine hLp alen0 (0#64, ()) m0 ⟨s0, hdenw0, rfl, rfl, rfl, rfl, Nat.zero_le _, rfl, ?_, hm0⟩
      rcases Nat.eq_zero_or_pos s0.core.arena_len with hz | hpos
      · exact Or.inl hz.symm
      · exact Or.inr (fullArenaClauseRefs_zero_mem hw0 hpos)

end ExtractBinariesProof

/-! ## 4. `m5_congruence_dense_wp` & `FullDefSweep.fullCongruenceDenseSpec` -/

section CongruenceDenseProof

open scoped FullArenaTactics FullCongTactics M3HeadTactics

private theorem bv64_ule_le {a b : BitVec 64} (h : a.ule b = true) : a.toNat ≤ b.toNat := by
  simpa [BitVec.ule] using h

private theorem cd_ht_pow_step {ht_sz : BitVec 64} {k cap : Nat}
    (hk : k ≤ 10) (heq : ht_sz.toNat = 64 * 2 ^ k)
    (hlt : ht_sz.toNat < 65536) (hmul : ht_sz.toNat * 8 ≤ cap) :
    k + 1 ≤ 10 ∧ (ht_sz <<< (1#32 : BitVec 32).signExtend 64).toNat = 64 * 2 ^ (k + 1) ∧
    (ht_sz <<< (1#32 : BitVec 32).signExtend 64).toNat ≤ 65536 ∧
    (ht_sz <<< (1#32 : BitVec 32).signExtend 64).toNat ≤ cap := by
  have hk_lt : k < 10 :=
    Nat.lt_of_le_of_ne hk fun h => by subst h; rw [heq] at hlt; simp at hlt
  have hshl : (ht_sz <<< (1#32 : BitVec 32).signExtend 64).toNat = 2 * ht_sz.toNat := by
    change (ht_sz <<< (1 : Nat)).toNat = 2 * ht_sz.toNat
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]
    exact Nat.mod_eq_of_lt (by omega)
  have h2k : 2 ^ k ≤ 2 ^ 9 := Nat.pow_le_pow_right (by omega) (by omega : k ≤ 9)
  have hpow : 64 * 2 ^ (k + 1) = 2 * (64 * 2 ^ k) := by rw [Nat.pow_succ]; omega
  refine ⟨by omega, by rw [hshl, heq, hpow], by rw [hshl, heq]; omega, by rw [hshl]; omega⟩

private theorem cd_ht_mul8_toNat {ht_sz : BitVec 64} (hle : ht_sz.toNat ≤ 65536) :
    (ht_sz * 8#64).toNat = ht_sz.toNat * 8 := by
  rw [BitVec.toNat_mul, show (8#64 : BitVec 64).toNat = 8 from rfl,
    Nat.mod_eq_of_lt (by omega)]

private theorem cd_repr_init_inv {F_cur : List (List Nat)} {repri : List (BitVec 32)}
    {cv0 maxv : Nat} (hrl : repri.length = 2 * maxv) (hcv : cv0 ≤ maxv)
    (hmax : maxv < 2 * dimacsBound)
    (hinit : ∀ k < 2 * cv0, repri[k]? = some (BitVec.ofNat 32 k)) :
    FullCongReprInv F_cur (2 * cv0) repri := by
  unfold dimacsBound at hmax
  refine ⟨⟨by omega, fun l hl => ?_⟩, fun l hl => ?_⟩
  · rw [hinit l hl, Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact Nat.le_refl _
  · rw [hinit l hl, Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact LitEquiv.refl _ _

/-- Parameterized `WorkStepOk` over an arbitrary congruence hash-table invariant `HtInv`
(allowing both `arity ≤ 8` `CongHtInv` and `arity ≤ 31` `CongHtInv32`). -/
def WorkStepOkGen
    (HtInv : List (List Nat) → Nat → List (BitVec 32) → List (BitVec 32) → Nat → Nat → Nat → Prop)
    (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (fuel0 : BitVec 64) (ar0 : List (BitVec 32)) (alen0 cv0 g_len ht_off ht_sz : Nat)
    (scr0 : List (BitVec 32)) (st : FullState) : Prop :=
  st.LengthsOk c ∧ FullWitnessInv c F0 F_cur st.core ∧
  FullLitMarksClear c st ∧ FullArenaVarsNodup st ∧ FullExtScratchOk c st ∧
  st.core.cur_level = 0 ∧ st.core.dense_mode ≠ 0#64 ∧
  st.core.cur_vars = cv0 ∧ st.core.fuel = fuel0 ∧
  st.core.arena = ar0 ∧ st.core.arena_len = alen0 ∧
  FullCongReprInv F_cur (2 * cv0) st.core.repr ∧
  (∀ idx < g_len, st.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
  HtInv F_cur cv0 scr0 st.scratch.scratch_buf g_len ht_off ht_sz

private theorem cd_workStepOkGen_of_scr
    {HtInv : List (List Nat) → Nat → List (BitVec 32) → List (BitVec 32) → Nat → Nat → Nat → Prop}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)} {alen0 cv0 g_len ht_off ht_sz : Nat}
    {scr0 scri : List (BitVec 32)} {st : FullState}
    (hok : WorkStepOkGen HtInv c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 st)
    (hscrl : scri.length = c.scratch_cap)
    (hpref : ∀ idx < g_len, scri[idx]? = scr0[idx]?)
    (hht : HtInv F_cur cv0 scr0 scri g_len ht_off ht_sz) :
    WorkStepOkGen HtInv c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0
      { st with scratch := { st.scratch with scratch_buf := scri, res_sz := 0#64 } } := by
  have hext' := fullExtScratchOk_of_eq hok.2.2.2.2.1 rfl rfl rfl rfl
  exact ⟨⟨hok.1.core_ok, { hok.1.scratch_ok with scratch_buf_len := hscrl }⟩,
    hok.2.1, hok.2.2.1, hok.2.2.2.1, hext', hok.2.2.2.2.2.1, hok.2.2.2.2.2.2.1,
    hok.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.2.1,
    hok.2.2.2.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.2.2.2.1, hpref, hht⟩

private theorem cd_workStepOkGen_with_tmk
    {HtInv : List (List Nat) → Nat → List (BitVec 32) → List (BitVec 32) → Nat → Nat → Nat → Prop}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)} {alen0 cv0 g_len ht_off ht_sz : Nat}
    {scr0 : List (BitVec 32)} {st : FullState} {tmki : List (BitVec 32)}
    (hok : WorkStepOkGen HtInv c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 st)
    (htl : tmki.length = 2 * c.max_vars) :
    WorkStepOkGen HtInv c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0
      { st with scratch := { st.scratch with tarjan_mark := tmki } } :=
  ⟨⟨hok.1.core_ok, { hok.1.scratch_ok with tarjan_mark_len := htl }⟩,
    hok.2.1, hok.2.2.1, hok.2.2.2.1, fullExtScratchOk_of_eq hok.2.2.2.2.1 rfl rfl rfl rfl,
    hok.2.2.2.2.2.1, hok.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.1,
    hok.2.2.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.2.2.2.1,
    hok.2.2.2.2.2.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

private theorem cd_denseInv_of_workStepOkGen
    {HtInv : List (List Nat) → Nat → List (BitVec 32) → List (BitVec 32) → Nat → Nat → Nat → Prop}
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)} {alen0 cv0 g_len ht_off ht_sz : Nat}
    {scr0 : List (BitVec 32)} {st : FullState}
    (hok : WorkStepOkGen HtInv c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 st) :
    FullDenseInv c F0 st ∧ st.core.cur_vars = cv0 ∧ st.core.fuel = fuel0 :=
  ⟨⟨⟨hok.1, F_cur, hok.2.1⟩, hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2.1,
    hok.2.2.2.2.2.1, hok.2.2.2.2.2.2.1⟩,
   hok.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.1⟩

private theorem cd_denseInv_with_tmk_res0 {c : FullCfg} {F0 : CNF Nat} {st : FullState}
    (hden : FullDenseInv c F0 st) {tmki : List (BitVec 32)} (htl : tmki.length = 2 * c.max_vars) :
    FullDenseInv c F0
      { st with scratch := { st.scratch with tarjan_mark := tmki, res_sz := 0#64 } } :=
  fullDenseInv_with_scratch_keep hden
    { hden.lengths.scratch_ok with tarjan_mark_len := htl } rfl rfl

private theorem cd_ht_set_step {g_len ht_off i : Nat} {scr0 scri : List (BitVec 32)}
    (hg_le : g_len ≤ ht_off) (hinv1 : ∀ idx < g_len, scri[idx]? = scr0[idx]?)
    (hinv2 : ∀ k < i, scri[ht_off + k]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32)
    (hi_len : ht_off + i < scri.length) :
    (∀ idx < g_len, (scri.set (ht_off + i) 0xFFFFFFFF#32)[idx]? = scr0[idx]?) ∧
    (∀ k < i + 1,
      (scri.set (ht_off + i) 0xFFFFFFFF#32)[ht_off + k]?.getD 0xFFFFFFFF#32 =
        0xFFFFFFFF#32) := by
  refine ⟨fun idx hidx => ?_, fun k hk => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hinv1 idx hidx
  · by_cases hki : k = i
    · subst hki; rw [List.getElem?_set_self hi_len, Option.getD_some]
    · rw [List.getElem?_set_ne (by omega)]; exact hinv2 k (by omega)

/-- Generic `full_congruence_dense` proof parameterized over any `GateSeq` / `HtInv` pair
(supporting both `FullM3CongBva` `arity ≤ 8` and `FullM5CongFix` `arity ≤ 31`). -/
theorem m5_congruence_dense_wp_gen
    (GateSeq : List (List Nat) → Nat → List (BitVec 32) → Nat → Nat → Prop)
    (HtInv : List (List Nat) → Nat → List (BitVec 32) → List (BitVec 32) → Nat → Nat → Nat → Prop)
    (hHtEmpty : ∀ F_cur cv scr0 scr g_len ht_off ht_sz,
      (∀ k < ht_sz, scr[ht_off + k]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) →
      HtInv F_cur cv scr0 scr g_len ht_off ht_sz)
    (Γ : Env)
    (hExtractBins : ∀ a m Q X, m5CongExtractBinariesSpec a m Q X →
      Γ "full_cong_extract_binaries" [i64] [i64] a m Q X)
    (hExtract : ∀ a m Q X,
      (fun (h, g_cap, _tick_lim, ()) m Q _ =>
        ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
          (R : Mem 64 → Prop),
          h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
          FullArenaVarsNodup s ∧ s.core.cur_level = 0 ∧ g_cap.toNat ≤ c.scratch_cap ∧
          (FullMem c s ⋆ R) m ∧
          ∀ (ret : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
            let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
            scr'.length = c.scratch_cap → ret.toNat ≤ g_cap.toNat →
            GateSeq F_cur s.core.cur_vars scr' ret.toNat 0 →
            (FullMem c s' ⋆ R) m' → Q (ret, ()) m') a m Q X →
      Γ "full_cong_extract" [i64, i64, i64] [i64] a m Q X)
    (hWork : ∀ a m Q X,
      (fun (h, g_len, ht_off, ht_sz, _cur_ep, ()) m Q _ =>
        ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
          (scr0 : List (BitVec 32)) (R : Mem 64 → Prop),
          h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
          FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧
          s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64 ∧
          FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
          0 < ht_sz.toNat ∧ g_len.toNat ≤ ht_off.toNat ∧
          ht_off.toNat + ht_sz.toNat ≤ c.scratch_cap ∧
          GateSeq F_cur s.core.cur_vars scr0 g_len.toNat 0 ∧
          (∀ idx < g_len.toNat, s.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
          HtInv F_cur s.core.cur_vars scr0 s.scratch.scratch_buf
            g_len.toNat ht_off.toNat ht_sz.toNat ∧
          (FullMem c s ⋆ R) m ∧
          ∀ (r : BitVec 64) s' m',
            s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
            FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
            s'.core.cur_level = 0 → s'.core.dense_mode ≠ 0#64 →
            s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
            s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
            FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
            (∀ idx < g_len.toNat, s'.scratch.scratch_buf[idx]? = scr0[idx]?) →
            HtInv F_cur s'.core.cur_vars scr0 s'.scratch.scratch_buf
              g_len.toNat ht_off.toNat ht_sz.toNat →
            ((r &&& 3#64) = 0#64 ∨ (r &&& 3#64) = 1#64 ∨ (r &&& 3#64) = 2#64) →
            ((r &&& 3#64) = 2#64 → F0.Unsat) →
            (FullMem c s' ⋆ R) m' → Q (r, ()) m') a m Q X →
      Γ "full_cong_work_step" [i64, i64, i64, i64, i32] [i64] a m Q X) :
    ∀ a m Q X, m3CongruenceDenseSpec a m Q X →
      Func.wp Γ full_congruence_dense_body a m Q X := by
  rintro ⟨h, tick_lim, ⟨⟩⟩ m0 Q X ⟨c, F0, s_in, R, rfl, hden_in, hm_in, hQ⟩
  have hsc := c.hscr; have hmx := c.hmaxv; unfold dimacsBound at hsc hmx
  unfold Func.wp full_congruence_dense_body
  m3_split_fast
  · m3_steps; exact hQ 1#64 s_in m0 hden_in rfl rfl (Or.inl rfl) (fun h => by cases h) hm_in
  · have h256 : 256 ≤ c.scratch_cap := by
      have hnot := bv64_ult_not_lt hc
      rw [show (256 : BitVec 64).toNat = 256 from rfl, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)] at hnot
      omega
    clear hc; m3_split_fast
    · m3_steps; exact hQ 1#64 s_in m0 hden_in rfl rfl (Or.inl rfl) (fun h => by cases h) hm_in
    · clear hc; m3_steps; m3_call hExtractBins
      refine ⟨c, F0, s_in, R, rfl, hden_in, hm_in, fun reb s m0 hden0 hcv_in hfu_in hreb_dom
        hreb_uns hm0 => ?_⟩
      m3_split_fast
      · have hreb20 : reb = 20#64 := beq_iff_eq.mp hc
        m3_steps
        exact hQ 20#64 s m0 hden0 hcv_in hfu_in (Or.inr rfl) (fun _ => hreb_uns hreb20) hm0
      · clear hc
        have hcore0 := hden0.1
        have hmk0 := hden0.2.1
        have hnd0 := hden0.2.2.1
        have hext0 := hden0.2.2.2.1
        have hcl0 := hden0.2.2.2.2.1
        have hdm0 := hden0.2.2.2.2.2
        obtain ⟨F_cur, hw0⟩ := hcore0.witness
        have hlen0 := hcore0.lengths
        have hcv_le := hlen0.core_ok.cur_vars_le
        have hrl0 := hlen0.core_ok.repr_len
        have htl0 := hlen0.scratch_ok.tarjan_mark_len
        let cv0 := s.core.cur_vars; let fuel0 := s.core.fuel
        let ar0 := s.core.arena; let alen0 := s.core.arena_len
        have hQ' : ∀ r s' m',
            FullDenseInv c F0 s' → s'.core.cur_vars = cv0 → s'.core.fuel = fuel0 →
            (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
            (FullMem c s' ⋆ R) m' → Q (r, ()) m' := fun r s' m' hd hc hf hr hu hm =>
          hQ r s' m' hd (hc.trans hcv_in) (hf.trans hfu_in) hr hu hm
        m3_steps
        refine wp_loop_inv
          (fun (ht_sz, ()) mht => mht = m0 ∧ ∃ k : Nat,
            k ≤ 10 ∧ ht_sz.toNat = 64 * 2 ^ k ∧ ht_sz.toNat ≤ 65536 ∧
            ht_sz.toNat ≤ c.scratch_cap)
          (fun (ht_sz, ()) _ => 65536 - ht_sz.toNat)
          (fun Jht hJht => by
            m3_steps; exact hJht (64#64, ()) m0 ⟨rfl, 0, Nat.zero_le _, rfl, by decide, by
              change 64 ≤ c.scratch_cap; omega⟩)
          (fun Jht (ht_sz, ()) mht ⟨hmht, k, hk_le, hpow, h65, hsc_le⟩ ih_ht => ?_)
        subst hmht
        have hht_pos : 0 < ht_sz.toNat := by
          rw [hpow]; exact Nat.mul_pos (by decide) (Nat.two_pow_pos _)
        m3_to_group
        refine wp_join_group (ts := []) (fun () me => me = mht) ?_ ?_
        · rintro _ ⟨⟩ me rfl
          have hht_off_n : (BitVec.ofNat 64 c.scratch_cap - ht_sz).toNat =
              c.scratch_cap - ht_sz.toNat := by
            rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hsc_le)),
              BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          let ht_off := BitVec.ofNat 64 c.scratch_cap - ht_sz
          have hht_off_lt : ht_off.toNat + ht_sz.toNat ≤ c.scratch_cap := by
            dsimp only [ht_off]; rw [hht_off_n]; omega
          have hcv0_lt : cv0 < 2 ^ 32 := by dsimp only [cv0]; omega
          have hcv0_64 : cv0 < 2 ^ 64 := Nat.lt_trans hcv0_lt (by decide)
          have h2cv0_64 : 2 * cv0 < 2 ^ 64 := by omega
          have hcv0_le : cv0 ≤ c.max_vars := hcv_le
          m3_steps; m3_call hExtract
          refine ⟨c, F0, F_cur, s, R, rfl, hlen0, hw0, hnd0, hcl0, by omega, hm0,
            fun g_len scr1 m1 hscrl1 hgl_le hseq1 hm1 => ?_⟩
          let s1 : FullState := { s with scratch := { s.scratch with scratch_buf := scr1 } }
          have hden1 : FullDenseInv c F0 s1 :=
            fullDenseInv_with_scratch_keep hden0 { hlen0.scratch_ok with scratch_buf_len := hscrl1 }
              rfl rfl
          m3_split_fast
          · m3_steps; exact hQ' 1#64 s1 m1 hden1 rfl rfl (Or.inl rfl) (fun h => by cases h) hm1
          · have hg_pos : 0 < g_len.toNat := by
              have hne := beq_eq_false_iff_ne.mp hc
              rcases Nat.eq_zero_or_pos g_len.toNat with hz | hp
              · exact absurd (BitVec.eq_of_toNat_eq hz) hne
              · exact hp
            clear hc
            m3_steps
            refine wp_loop_inv
              (fun (i, ()) mi => ∃ repri : List (BitVec 32),
                repri.length = 2 * c.max_vars ∧ i.toNat ≤ 2 * cv0 ∧
                (∀ k' < i.toNat, repri[k']? = some (BitVec.ofNat 32 k')) ∧
                (FullMem c { s1 with core := { s1.core with repr := repri } } ⋆ R) mi)
              (fun (i, ()) _ => 2 * cv0 - i.toNat)
              (fun Ji hJi => by
                m3_steps; exact hJi (0#64, ()) m1 ⟨s1.core.repr, hrl0, Nat.zero_le _,
                  fun _ h => by simp at h, hm1⟩)
              (fun Ji (i, ()) mi ⟨repri, hrli, hi_le, hinit, hmi⟩ ihi => ?_)
            m3_split_fast
            · have hi_lt : i.toNat < 2 * cv0 := by
                have hlt := bv64_ult_lt hc
                change i.toNat < (BitVec.ofNat 64 cv0 <<< (1 : Nat)).toNat at hlt
                rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt hcv0_64, Nat.mod_eq_of_lt h2cv0_64] at hlt
                exact hlt
              have hi1_n : (i + 1#64).toNat = i.toNat + 1 :=
                bv64_add1_toNat (n := 2 * cv0) hi_lt h2cv0_64
              have hi_arr : i.toNat < repri.length := by omega
              have hi_tr : i.setWidth 32 = BitVec.ofNat 32 i.toNat := by
                apply BitVec.eq_of_toNat_eq
                rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
              m3_steps
              exact ihi (i + 1#64, ()) m (by dsimp only; omega)
                ⟨repri.set i.toNat (i.setWidth 32), by simp [hrli], by omega,
                 fun k' hk' => by
                   rw [hi1_n] at hk'
                   by_cases hki : k' = i.toNat
                   · subst hki; rw [List.getElem?_set_self (by omega), hi_tr]
                   · rw [List.getElem?_set_ne (Ne.symm hki)]; exact hinit k' (by omega),
                 hm⟩
            · have hi_eq : i.toNat = 2 * cv0 := by
                have hnot := bv64_ult_not_lt hc
                change ¬ i.toNat < (BitVec.ofNat 64 cv0 <<< (1 : Nat)).toNat at hnot
                rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt hcv0_64, Nat.mod_eq_of_lt h2cv0_64] at hnot
                omega
              rw [hi_eq] at hinit
              have hrepr2 : FullCongReprInv F_cur (2 * cv0) repri :=
                cd_repr_init_inv hrli hcv_le hmx hinit
              let s2 : FullState := { s1 with core := { s1.core with repr := repri } }
              have hlen2 : s2.LengthsOk c := ⟨{ hlen0.core_ok with repr_len := hrli },
                { hlen0.scratch_ok with scratch_buf_len := hscrl1 }⟩
              have hw2 : FullWitnessInv c F0 F_cur s2.core := fullWitnessInv_with_repr hw0 repri
              clear hc; m3_steps
              refine wp_loop_inv
                (fun (i2, ()) mt => ∃ tmki : List (BitVec 32),
                  tmki.length = 2 * c.max_vars ∧ i2.toNat ≤ cv0 ∧
                  (FullMem c { s2 with scratch := { s2.scratch with tarjan_mark := tmki } } ⋆ R) mt)
                (fun (i2, ()) _ => cv0 - i2.toNat)
                (fun Jt hJt => by
                  m3_steps
                  exact hJt (0#64, ()) mi ⟨s2.scratch.tarjan_mark, htl0, Nat.zero_le _, hmi⟩)
                (fun Jt (i2, ()) mt ⟨tmki, htli, hi2_le, hmt⟩ iht => ?_)
              m3_split_fast
              · have hi2_lt : i2.toNat < cv0 := by
                  have hlt := bv64_ult_lt hc
                  rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv0_64] at hlt
                have hi2_arr : i2.toNat < tmki.length := by omega
                have hi2_1 : (i2 + 1#64).toNat = i2.toNat + 1 :=
                  bv64_add1_toNat (n := cv0) hi2_lt hcv0_64
                m3_steps
                exact iht (i2 + 1#64, ()) m (by dsimp only; omega)
                  ⟨tmki.set i2.toNat 1#32, by simp [htli], by omega, hm⟩
              · clear hc
                let s3 : FullState :=
                  { s2 with scratch := { s2.scratch with tarjan_mark := tmki } }
                have hlen3 : s3.LengthsOk c :=
                  ⟨hlen2.core_ok, { hlen2.scratch_ok with tarjan_mark_len := htli }⟩
                m3_steps
                refine wp_loop_inv
                  (fun (i3, ()) ms => ∃ scri : List (BitVec 32),
                    scri.length = c.scratch_cap ∧ i3.toNat ≤ ht_sz.toNat ∧
                    (∀ idx < g_len.toNat, scri[idx]? = scr1[idx]?) ∧
                    (∀ k' < i3.toNat, scri[ht_off.toNat + k']?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) ∧
                    (FullMem c
                      { s3 with scratch := { s3.scratch with scratch_buf := scri } } ⋆ R) ms)
                  (fun (i3, ()) _ => ht_sz.toNat - i3.toNat)
                  (fun Js hJs => by
                    m3_steps; exact hJs (0#64, ()) mt ⟨scr1, hscrl1, Nat.zero_le _,
                      fun _ _ => rfl, fun _ h => by simp at h, hmt⟩)
                  (fun Js (i3, ()) ms ⟨scri, hscrl_i, hi3_le, hpref_i, hinit_i, hms⟩ ihs => ?_)
                m3_split_fast
                · have hi3_lt : i3.toNat < ht_sz.toNat := bv64_ult_lt hc
                  have hi3_1 : (i3 + 1#64).toNat = i3.toNat + 1 :=
                    bv64_add1_toNat (n := ht_sz.toNat) hi3_lt (by omega)
                  have hadd_n : (ht_off + i3).toNat = ht_off.toNat + i3.toNat := by
                    show (ht_off.toNat + i3.toNat) % 2 ^ 64 = ht_off.toNat + i3.toNat
                    exact Nat.mod_eq_of_lt (by omega)
                  have hadd_arr : (ht_off + i3).toNat < scri.length := by rw [hadd_n]; omega
                  m3_steps
                  rw [hadd_n] at hm
                  obtain ⟨hpref_i', hinit_i'⟩ := cd_ht_set_step (g_len := g_len.toNat)
                    (ht_off := ht_off.toNat) (i := i3.toNat) (by omega) hpref_i hinit_i
                    (by omega)
                  exact ihs (i3 + 1#64, ()) m (by dsimp only; omega)
                    ⟨scri.set (ht_off.toNat + i3.toNat) 0xFFFFFFFF#32, by simp [hscrl_i], by omega,
                     hpref_i', hi3_1 ▸ hinit_i', hm⟩
                · have hi3_eq : i3.toNat = ht_sz.toNat := by
                    have := bv64_ult_not_lt hc; omega
                  rw [hi3_eq] at hinit_i; clear hc
                  have hht4 := hHtEmpty F_cur cv0 scr1 scri g_len.toNat ht_off.toNat ht_sz.toNat
                    hinit_i
                  let s4 : FullState :=
                    { s3 with scratch := { s3.scratch with scratch_buf := scri, res_sz := 0#64 } }
                  have hok4 : WorkStepOkGen HtInv c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat
                      ht_off.toNat ht_sz.toNat scr1 s4 :=
                    ⟨⟨hlen3.core_ok, { hlen3.scratch_ok with scratch_buf_len := hscrl_i }⟩,
                     hw2, hmk0, hnd0, fullExtScratchOk_of_eq hext0 rfl rfl rfl rfl,
                     hcl0, hdm0, rfl, rfl, rfl, rfl, hrepr2, hpref_i, hht4⟩
                  m3_to_group
                  refine wp_join_group (ts := [i64])
                    (fun (mp, ()) mmp => mmp = m ∧ mp.toNat ≤ 0x7FFFFFFF)
                    (fun _ ⟨mp, ⟨⟩⟩ mmp hmmp => by
                      obtain ⟨hmmp_eq, hmp_le⟩ := hmmp
                      rw [hmmp_eq]
                      m3_to_group
                      refine wp_loop_break_group
                        (fun _ mb => ∃ sb : FullState,
                          FullDenseInv c F0 sb ∧ sb.core.cur_vars = cv0 ∧
                          sb.core.fuel = fuel0 ∧ sb.scratch.tarjan_mark.length = 2 * c.max_vars ∧
                          (FullMem c sb ⋆ R) mb)
                        (fun rem (_, pass, ticks, rehashes, ()) ml => ∃ sp : FullState,
                          pass.toNat ≤ mp.toNat ∧ rem = mp.toNat - pass.toNat ∧
                          rehashes.toNat ≤ 4 ∧ sp.scratch.tarjan_mark.length = 2 * c.max_vars ∧
                          WorkStepOkGen HtInv c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat
                            ht_off.toNat ht_sz.toNat scr1 sp ∧
                          (FullMem c sp ⋆ R) ml)
                        ?_ ?_ ?_
                      · rintro _ _ mb ⟨sb, hdenb, hcvb, hfub, htlb, hmb⟩
                        m3_steps
                        refine wp_loop_inv
                          (fun (ie, ()) me => ∃ tmke : List (BitVec 32),
                            tmke.length = 2 * c.max_vars ∧ ie.toNat ≤ cv0 ∧
                            (FullMem c { sb with scratch :=
                              { sb.scratch with tarjan_mark := tmke } } ⋆ R) me)
                          (fun (ie, ()) _ => cv0 - ie.toNat)
                          (fun Je hJe => by
                            m3_steps; exact hJe (0#64, ()) mb ⟨sb.scratch.tarjan_mark, htlb,
                              Nat.zero_le _, hmb⟩)
                          (fun Je (ie, ()) me ⟨tmke, htle, hie_le, hme⟩ ihe => ?_)
                        m3_split_fast
                        · have hie_lt : ie.toNat < cv0 := by
                            have hlt := bv64_ult_lt hc
                            change ie.toNat < (BitVec.ofNat 64 cv0).toNat at hlt
                            rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv0_64] at hlt
                          have hie_arr : ie.toNat < tmke.length := by omega
                          have hie1 : (ie + 1#64).toNat = ie.toNat + 1 :=
                            bv64_add1_toNat (n := cv0) hie_lt (by omega)
                          m3_steps
                          exact ihe (ie + 1#64, ()) m (by dsimp only; omega)
                            ⟨tmke.set ie.toNat 0#32, by simp [htle], by omega, hm⟩
                        · clear hc
                          let sf : FullState := { sb with scratch :=
                            { sb.scratch with tarjan_mark := tmke, res_sz := 0#64 } }
                          have hdenf : FullDenseInv c F0 sf := cd_denseInv_with_tmk_res0 hdenb htle
                          m3_steps
                          · have hinc : sf.core.inconsistent ≠ 0#64 := hc
                            obtain ⟨_, hw_f⟩ := hdenf.1.witness
                            exact hJ _ _ (hQ' 20#64 sf m hdenf hcvb hfub (Or.inr rfl)
                              (fun _ => unsat_of_inconsistent_w hw_f hinc) hm)
                          · exact hJ _ _ (hQ' 1#64 sf m hdenf hcvb hfub (Or.inl rfl)
                              (fun h => by cases h) hm)
                      · rintro B L rem ⟨i_lp, pass, ticks, rehashes, ⟨⟩⟩ ml hB hL
                          ⟨sp, hpass_le, rfl, hreh_le, htlp, hokp, hml⟩
                        have hcvp := hokp.2.2.2.2.2.2.2.1
                        have hfup := hokp.2.2.2.2.2.2.2.2.1
                        have hbrk_p : B (i_lp, pass, ticks, rehashes, ()) ml :=
                          hB (i_lp, pass, ticks, rehashes, ()) ml
                            ⟨sp, (cd_denseInv_of_workStepOkGen hokp).1, hcvp, hfup, htlp, hml⟩
                        m3_split_fast
                        · have hpass_lt : pass.toNat < mp.toNat := bv64_ult_lt hc
                          have hpass1 : (pass + 1#64).toNat = pass.toNat + 1 :=
                            bv64_add1_toNat (n := mp.toNat) hpass_lt (by omega)
                          clear hc; m3_split_fast
                          · clear hc; m3_split_fast
                            · clear hc
                              m3_steps; m3_call hWork
                              refine ⟨c, F0, F_cur, sp, scr1, R, rfl, hokp.1, hokp.2.1, hokp.2.2.1,
                                hokp.2.2.2.1, hokp.2.2.2.2.1, hokp.2.2.2.2.2.1, hokp.2.2.2.2.2.2.1,
                                hcvp ▸ hokp.2.2.2.2.2.2.2.2.2.2.2.1, hht_pos, by omega, by omega,
                                hcvp ▸ hseq1, hokp.2.2.2.2.2.2.2.2.2.2.2.2.1,
                                hcvp ▸ hokp.2.2.2.2.2.2.2.2.2.2.2.2.2,
                                hml, fun ret sq mq hlenq hwq hmkq hndq hextq hclq hdmq hcvq hfuq
                                  harq halq hreprq hprefq hhtq hdomq _ hmq => ?_⟩
                              have hcvq0 : sq.core.cur_vars = cv0 := hcvq.trans hcvp
                              have hokq' : WorkStepOkGen HtInv c F0 F_cur fuel0 ar0 alen0 cv0
                                  g_len.toNat ht_off.toNat ht_sz.toNat scr1 sq :=
                                ⟨hlenq, hwq, hmkq, hndq, hextq, hclq, hdmq, hcvq0,
                                 hfuq.trans hfup, harq.trans hokp.2.2.2.2.2.2.2.2.2.1,
                                 halq.trans hokp.2.2.2.2.2.2.2.2.2.2.1,
                                 hcvq0 ▸ hreprq, hprefq, hcvq0 ▸ hhtq⟩
                              have hdenq := (cd_denseInv_of_workStepOkGen hokq').1
                              have hfuq0 := hokq'.2.2.2.2.2.2.2.2.1
                              have htlq := hokq'.1.scratch_ok.tarjan_mark_len
                              m3_split_fast
                              · m3_steps
                                exact hB (i_lp, pass, ticks + (ret >>> 2#64), rehashes, ()) mq
                                  ⟨sq, hdenq, hcvq0, hfuq0, htlq, hmq⟩
                              · clear hc; m3_split_fast
                                · m3_steps
                                  exact hB (i_lp, pass, ticks + (ret >>> 2#64), rehashes, ()) mq
                                    ⟨sq, hdenq, hcvq0, hfuq0, htlq, hmq⟩
                                · clear hc
                                  m3_to_group
                                  refine wp_join_group (ts := [i64, i64])
                                    (fun (_, r', ()) mj => ∃ sj : FullState,
                                      r'.toNat ≤ 4 ∧
                                      sj.scratch.tarjan_mark.length = 2 * c.max_vars ∧
                                      WorkStepOkGen HtInv c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat
                                        ht_off.toNat ht_sz.toNat scr1 sj ∧ (FullMem c sj ⋆ R) mj)
                                    (fun _ (i_j, r', ()) mj ⟨sj, hrj, htlj, hokj, hmj⟩ => by
                                      m3_steps
                                      exact hL (mp.toNat - (pass + 1#64).toNat)
                                        (i_j, pass + 1#64, ticks + (ret >>> 2#64), r', ()) mj
                                        (by omega) ⟨sj, by omega, rfl, hrj, htlj, hokj, hmj⟩)
                                    ?_
                                  intro Jre hJre
                                  m3_split_fast
                                  · m3_split_fast
                                    · have hreh_lt : rehashes.toNat < 4 := bv64_ult_lt hc
                                      have hreh1 : (rehashes + 1#64).toNat = rehashes.toNat + 1 :=
                                        bv64_add1_toNat (n := 4) hreh_lt (by decide)
                                      clear hc; m3_steps
                                      refine wp_loop_inv
                                        (fun (ir, ()) mr => ∃ scrr : List (BitVec 32),
                                          scrr.length = c.scratch_cap ∧ ir.toNat ≤ ht_sz.toNat ∧
                                          (∀ idx < g_len.toNat, scrr[idx]? = scr1[idx]?) ∧
                                          (∀ k' < ir.toNat,
                                            scrr[ht_off.toNat + k']?.getD 0xFFFFFFFF#32 =
                                              0xFFFFFFFF#32) ∧
                                          (FullMem c { sq with scratch :=
                                            { sq.scratch with scratch_buf := scrr } } ⋆ R) mr)
                                        (fun (ir, ()) _ => ht_sz.toNat - ir.toNat)
                                        (fun Jr hJr => by
                                          m3_steps; exact hJr (0#64, ()) mq
                                            ⟨sq.scratch.scratch_buf,
                                             hokq'.1.scratch_ok.scratch_buf_len, Nat.zero_le _,
                                             hprefq, fun _ h => by simp at h, hmq⟩)
                                        (fun Jr (ir, ()) mr
                                            ⟨scrr, hscrr, hir_le, hprefr, hinitr, hmr⟩ ihr => ?_)
                                      m3_split_fast
                                      · have hir_lt : ir.toNat < ht_sz.toNat := bv64_ult_lt hc
                                        have hir1 : (ir + 1#64).toNat = ir.toNat + 1 :=
                                          bv64_add1_toNat (n := ht_sz.toNat) hir_lt (by omega)
                                        have hadd_n : (ht_off + ir).toNat =
                                            ht_off.toNat + ir.toNat := by
                                          show (ht_off.toNat + ir.toNat) % 2 ^ 64 =
                                            ht_off.toNat + ir.toNat
                                          exact Nat.mod_eq_of_lt (by omega)
                                        have hadd_arr : (ht_off + ir).toNat < scrr.length := by
                                          rw [hadd_n]; omega
                                        m3_steps; rw [hadd_n] at hm
                                        obtain ⟨hprefr', hinitr'⟩ := cd_ht_set_step
                                          (g_len := g_len.toNat) (ht_off := ht_off.toNat)
                                          (i := ir.toNat) (by omega) hprefr hinitr (by omega)
                                        exact ihr (ir + 1#64, ()) m (by dsimp only; omega)
                                          ⟨scrr.set (ht_off.toNat + ir.toNat) 0xFFFFFFFF#32,
                                           by simp [hscrr], by omega, hprefr', hir1 ▸ hinitr', hm⟩
                                      · have hir_eq : ir.toNat = ht_sz.toNat := by
                                          have := bv64_ult_not_lt hc; omega
                                        rw [hir_eq] at hinitr; clear hc
                                        have hhtr' := hHtEmpty F_cur cv0 scr1 scrr g_len.toNat
                                          ht_off.toNat ht_sz.toNat hinitr
                                        let sr1 : FullState :=
                                          { sq with scratch := { sq.scratch with
                                            scratch_buf := scrr, res_sz := 0#64 } }
                                        have hokr1 := cd_workStepOkGen_of_scr hokq' hscrr hprefr
                                          hhtr'
                                        m3_steps
                                        refine wp_loop_inv
                                          (fun (it, ()) mtt => ∃ tmkt : List (BitVec 32),
                                            tmkt.length = 2 * c.max_vars ∧ it.toNat ≤ cv0 ∧
                                            (FullMem c { sr1 with scratch :=
                                              { sr1.scratch with tarjan_mark := tmkt } } ⋆ R) mtt)
                                          (fun (it, ()) _ => cv0 - it.toNat)
                                          (fun Jt' hJt' => by
                                            m3_steps; exact hJt' (0#64, ()) m
                                              ⟨sr1.scratch.tarjan_mark, htlq, Nat.zero_le _, hm⟩)
                                          (fun Jt' (it, ()) mtt
                                              ⟨tmkt, htlt, hit_le, hmtt⟩ iht' => ?_)
                                        m3_split_fast
                                        · have hit_lt : it.toNat < cv0 := by
                                            have hlt := bv64_ult_lt hc
                                            change it.toNat < (BitVec.ofNat 64 cv0).toNat at hlt
                                            rwa [BitVec.toNat_ofNat,
                                              Nat.mod_eq_of_lt hcv0_64] at hlt
                                          have hit_arr : it.toNat < tmkt.length := by omega
                                          have hit1 : (it + 1#64).toNat = it.toNat + 1 :=
                                            bv64_add1_toNat (n := cv0) hit_lt (by omega)
                                          m3_steps
                                          exact iht' (it + 1#64, ()) m (by dsimp only; omega)
                                            ⟨tmkt.set it.toNat _, by simp [htlt], by omega, hm⟩
                                        · clear hc; m3_steps
                                          exact hJre (it, rehashes + 1#64, ()) mtt
                                            ⟨_, by omega, htlt,
                                             cd_workStepOkGen_with_tmk hokr1 htlt, hmtt⟩
                                    · clear hc; m3_let
                                      exact hJre (i_lp, rehashes, ()) mq
                                        ⟨sq, hreh_le, htlq, hokq', hmq⟩
                                  · clear hc; m3_let
                                    exact hJre (i_lp, rehashes, ()) mq
                                      ⟨sq, hreh_le, htlq, hokq', hmq⟩
                            · clear hc; m3_steps; exact hbrk_p
                          · clear hc; m3_steps; exact hbrk_p
                        · clear hc; m3_steps; exact hbrk_p
                      · intro _ Lp _ hLp; m3_steps
                        exact hLp mp.toNat (i3, 0#64, 0#64, 0#64, ()) m
                          ⟨s4, Nat.zero_le _, rfl, Nat.zero_le _, htli, hok4, hm⟩)
                    (fun Jmp hJmp => by
                      m3_split_fast
                      · m3_steps; exact hJmp (0x7FFFFFFF#64, ()) m ⟨rfl, by decide⟩
                      · have hle : ((BitVec.ofNat 64 cv0 <<< (1 : Nat)) + 4#64).toNat ≤
                            0x7FFFFFFF := by
                          have hnot := bv64_ult_not_lt hc
                          change ¬ (0x7FFFFFFF : BitVec 64).toNat <
                            ((BitVec.ofNat 64 cv0 <<< (1 : Nat)) + 4#64).toNat at hnot
                          rw [show (0x7FFFFFFF : BitVec 64).toNat = 0x7FFFFFFF from rfl] at hnot
                          omega
                        m3_let; exact hJmp (_, ()) m ⟨rfl, hle⟩)
        · intro Jht_exit hJht_exit
          m3_split_fast
          · have hmul_le : ht_sz.toNat * 8 ≤ c.scratch_cap := by
              have hle := bv64_ule_le hc
              rw [show (8 : BitVec 64) = 8#64 from rfl, cd_ht_mul8_toNat h65,
                BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hle
              exact hle
            clear hc; m3_split_fast
            · have hlt : ht_sz.toNat < 65536 := bv64_ult_lt hc
              obtain ⟨hk1, hpow1, h651, hsc1⟩ := cd_ht_pow_step hk_le hpow hlt hmul_le
              m3_steps; exact ih_ht (ht_sz <<< (1#32 : BitVec 32).signExtend 64, ()) mht
                (by dsimp only; rw [hpow1, hpow]; omega) ⟨rfl, k + 1, hk1, hpow1, h651, hsc1⟩
            · m3_let; exact hJht_exit () mht rfl
          · m3_let; exact hJht_exit () mht rfl

/-- Drop-in replacement `full_congruence_dense` (`FullM5CongBins`) proving unchanged
`FullM3CongBva.m3CongruenceDenseSpec` while calling `full_cong_extract_binaries(h)` before
`full_cong_extract`. -/
theorem m5_congruence_dense_wp (Γ : Env)
    (hExtractBins : ∀ a m Q X, m5CongExtractBinariesSpec a m Q X →
      Γ "full_cong_extract_binaries" [i64] [i64] a m Q X)
    (hExtract : ∀ a m Q X, FullM3CongBva.fullCongExtractTickSpec a m Q X →
      Γ "full_cong_extract" [i64, i64, i64] [i64] a m Q X)
    (hWork : ∀ a m Q X, m3CongWorkStepSpec a m Q X →
      Γ "full_cong_work_step" [i64, i64, i64, i64, i32] [i64] a m Q X) :
    ∀ a m Q X, m3CongruenceDenseSpec a m Q X →
      Func.wp Γ full_congruence_dense_body a m Q X :=
  m5_congruence_dense_wp_gen FullCongSpecs.GateSeqOk FullCongSpecs.CongHtInv
    (fun _ _ _ _ _ _ _ hinit k hk => Or.inl (hinit k hk)) Γ hExtractBins hExtract hWork

/-- Weakening to unchanged `FullDefSweep.fullCongruenceDenseSpec` (`M2b` compatibility). -/
theorem m5_defsweep_congruence_dense_wp (Γ : Env)
    (hExtractBins : ∀ a m Q X, m5CongExtractBinariesSpec a m Q X →
      Γ "full_cong_extract_binaries" [i64] [i64] a m Q X)
    (hExtract : ∀ a m Q X, FullM3CongBva.fullCongExtractTickSpec a m Q X →
      Γ "full_cong_extract" [i64, i64, i64] [i64] a m Q X)
    (hWork : ∀ a m Q X, m3CongWorkStepSpec a m Q X →
      Γ "full_cong_work_step" [i64, i64, i64, i64, i32] [i64] a m Q X) :
    ∀ a m Q X, FullDefSweep.fullCongruenceDenseSpec a m Q X →
      Func.wp Γ full_congruence_dense_body a m Q X := by
  rintro ⟨h, tick_lim, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hden, hm, hQ⟩
  exact m5_congruence_dense_wp Γ hExtractBins hExtract hWork
    (c.hdr, tick_lim, ()) m0 Q X ⟨c, F0, s, R, rfl, hden, hm,
      fun r s' m' hd _ hf hr hu hm' => hQ r s' m' hd hf hr hu hm'⟩

end CongruenceDenseProof

/-! ## 5. Closed `m5CongBinsModule` Soundness & Concrete `Mem 64` Non-Vacuity -/

section ModuleAndNV

/-- Closed `8`-row specification table for `m5CongBinsModule` (`3` fns ++ `5` externs). -/
def m5CongBinsSpecTable : List SpecEntry :=
  [ ⟨"full_cong_eb_match", [i64, i32, i32, i32], [.bool], m5CongEbMatchSpec, true⟩
  , ⟨"full_cong_extract_binaries", [i64], [i64], m5CongExtractBinariesSpec, true⟩
  , ⟨"full_congruence_dense", [i64, i64], [i64], m3CongruenceDenseSpec, true⟩
  , ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  , ⟨"full_has_bin", [i64, i32, i32], [.bool], fullHasBinSpec, true⟩
  , ⟨"full_add_bin", [i64, i32, i32], [i64], fullAddBinSpec, true⟩
  , ⟨"full_cong_extract", [i64, i64, i64], [i64], FullM3CongBva.fullCongExtractTickSpec, true⟩
  , ⟨"full_cong_work_step", [i64, i64, i64, i64, i32], [i64], m3CongWorkStepSpec, true⟩ ]

def m5CongBinsEnv : Env := Env.ofTable m5CongBinsSpecTable

theorem m5CongBinsSpecTable_sigs :
    m5CongBinsSpecTable.map (fun e => (e.name, e.as, e.rs)) = m5CongBinsModule.sigs := by
  t_kernel_rfl

theorem m5CongBinsSpecTable_noExit :
    ∀ e ∈ m5CongBinsSpecTable, e.noExit = true := by
  intro e he
  simp only [m5CongBinsSpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem m5CongBinsSpecTable_nodup :
    (m5CongBinsSpecTable.map SpecEntry.name).Nodup := by
  have hchk := m5CongBins_acyclic
  simp only [m5CongBinsModule, Module.checkAcyclic, Bool.and_eq_true] at hchk
  have hnd := Module.namesNodup_of_checkNamesNodup hchk.1
  have hnames : m5CongBinsSpecTable.map SpecEntry.name = m5CongBinsModule.names := by
    have hm := congrArg (List.map Prod.fst) m5CongBinsSpecTable_sigs
    simpa only [List.map_map, Function.comp_def, Module.sigs, Module.names, Fn.sig, Extern.sig,
      List.map_append] using hm
  rw [hnames]; exact hnd

private theorem m5Env_row (i : Nat) (e : SpecEntry)
    (hi : m5CongBinsSpecTable[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → m5CongBinsEnv e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) m5CongBinsSpecTable_nodup (hno xs m Q X h)

private theorem m5_allFns_of_forall {P : Fn → Prop} :
    ∀ {fs : List Fn}, (∀ f ∈ fs, P f) → AllFns P fs
  | [], _ => trivial
  | _ :: _, h =>
    ⟨h _ List.mem_cons_self, m5_allFns_of_forall fun f hf => h f (List.mem_cons_of_mem _ hf)⟩

theorem m5CongBins_tableImpl :
    TableImpl m5CongBinsEnv m5CongBinsModule.fns m5CongBinsSpecTable := by
  have hExt0 := m5Env_row 0
    ⟨"full_cong_eb_match", [i64, i32, i32, i32], [.bool], m5CongEbMatchSpec, true⟩
  have hExt1 := m5Env_row 1
    ⟨"full_cong_extract_binaries", [i64], [i64], m5CongExtractBinariesSpec, true⟩
  have hExt3 := m5Env_row 3 ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  have hExt4 := m5Env_row 4 ⟨"full_has_bin", [i64, i32, i32], [.bool], fullHasBinSpec, true⟩
  have hExt5 := m5Env_row 5 ⟨"full_add_bin", [i64, i32, i32], [i64], fullAddBinSpec, true⟩
  have hExt6 := m5Env_row 6
    ⟨"full_cong_extract", [i64, i64, i64], [i64], FullM3CongBva.fullCongExtractTickSpec, true⟩
  have hExt7 := m5Env_row 7
    ⟨"full_cong_work_step", [i64, i64, i64, i64, i32], [i64], m3CongWorkStepSpec, true⟩
  exact ⟨
    .of (full_cong_eb_match_wp m5CongBinsEnv hExt4),
    .of (full_cong_extract_binaries_wp m5CongBinsEnv hExt3 hExt4 hExt0 hExt5),
    .of (m5_congruence_dense_wp m5CongBinsEnv hExt1 hExt6 hExt7),
    trivial⟩

theorem m5CongBins_moduleOk : ModuleOk m5CongBinsEnv m5CongBinsModule :=
  Env.ofTable_moduleOk m5CongBins_acyclic (m5_allFns_of_forall m5CongBins_fns_wf)
    m5CongBins_tableImpl

/-- Concrete empty-database dense `FullState` over `nvOneLitCfg` (`F0 = {(x0), (¬x0)}`,
`arena_len = 0`, `cur_level = 0`, `dense_mode = 1`). -/
def nvDenseState : FullState where
  core :=
    { nvOneLitState.core with
      vals := [0#8, 0#8]
      trail_end := 0
      propagated := 0
      dense_mode := 1#64 }
  scratch := nvOneLitState.scratch

/-- Concrete `Mem 64` carrying `FullDenseInv nvOneLitCfg nvOneLitF0 nvDenseState`. -/
def nvDenseMem : Mem 64 :=
  storeMem (storeMem (storeMem (storeMem (storeMem nvOneLitMem
    i8 (nvOneLitCfg.pVals + 0#64) 0#8)
    i8 (nvOneLitCfg.pVals + 1#64) 0#8)
    i64 (nvOneLitCfg.hdr + 144) (BitVec.ofNat 64 0))
    i64 (nvOneLitCfg.hdr + 152) (BitVec.ofNat 64 0))
    i64 (nvOneLitCfg.hdr + 1016) 1#64

theorem nvDense_lengths : nvDenseState.LengthsOk nvOneLitCfg :=
  ⟨{ nvOneLit_lengths.core_ok with
     vals_len := rfl
     trail_end_le := Nat.zero_le _
     propagated_le := Nat.zero_le _ },
   nvOneLit_lengths.scratch_ok⟩

theorem nvDense_witness :
    FullWitnessInv nvOneLitCfg nvOneLitF0 [[0], [1]] nvDenseState.core :=
  fullWitnessInv_empty
    (hext := ⟨(varsBoundedBool_iff 1 [[0], [1]]).mp rfl, id⟩)
    (hinc := rfl) (hal := rfl)
    (hwvec := fun l hl => by
      have hcv : nvDenseState.core.cur_vars = 1 := rfl
      rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> exact ⟨rfl, rfl⟩)
    (hte := rfl) (hcl := rfl) (hft0 := rfl)
    (hvals := fun l hl => by
      have hcv : nvDenseState.core.cur_vars = 1 := rfl
      rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl)

theorem nvDense_inv : FullDenseInv nvOneLitCfg nvOneLitF0 nvDenseState := by
  have hmv : nvOneLitCfg.max_vars = 1 := rfl
  refine ⟨⟨nvDense_lengths, [[0], [1]], nvDense_witness⟩, ?_, ?_, ?_, rfl, by decide⟩
  · refine ⟨fun v hv => ?_, fun l hl => ?_⟩
    · rw [hmv] at hv; obtain rfl : v = 0 := (by omega); rfl
    · rw [hmv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl
  · intro r hr; have : fullArenaClauseRefs nvDenseState = [] := rfl; simp [this] at hr
  · exact ⟨FullLastLearnedWf.of_cleared fun i hi => by
      simp only [nvDenseState, nvOneLitState, nvOneLitScratch, List.getElem?_replicate,
        show i < 16 by omega, ↓reduceIte, Option.getD_some], Nat.le_refl 0⟩

open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics in
theorem nvDenseMem_ok : FullMem nvOneLitCfg nvDenseState nvDenseMem := by
  have h0 : (FullMem nvOneLitCfg nvOneLitState ⋆ emp) nvOneLitMem := by
    rw [sep_emp]; exact nvOneLitMem_ok
  have h1 := (FullArenaTactics.store_full_vals (i := 0) (v := 0#8) (by decide) h0).2
  have h2 := (FullArenaTactics.store_full_vals (i := 1) (v := 0#8) (by decide) h1).2
  have h3 := (FullArenaTactics.store_full_trail_end (v := 0) (by decide) h2).2
  have h4 := (FullArenaTactics.store_full_propagated (v := 0) (by decide) h3).2
  have h5 := (FullArenaTactics.store_full_dense_mode (v := 1#64) h4).2
  rw [sep_emp] at h5
  simpa only [nvDenseState, nvDenseMem, nvOneLitState,
    show (([1#8, 0xFF#8] : List (BitVec 8)).set 0 0#8).set 1 0#8 = [0#8, 0#8] from rfl] using h5

/-- Concrete `Mem 64` non-vacuity (`XPost := False`) for `full_cong_extract_binaries`
under closed `m5CongBinsEnv`. -/
theorem m5_cong_extract_binaries_nv :
    Func.wp m5CongBinsEnv full_cong_extract_binaries_body (nvOneLitCfg.hdr, ()) nvDenseMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvOneLitCfg nvOneLitF0 s' ∧
        s'.core.cur_vars = 1 ∧ s'.core.fuel = 0#64 ∧
        (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → nvOneLitF0.Unsat) ∧
        FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvDenseState ⋆ emp) nvDenseMem := by
    rw [sep_emp]; exact nvDenseMem_ok
  exact full_cong_extract_binaries_wp m5CongBinsEnv
    (m5Env_row 3 ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩)
    (m5Env_row 4 ⟨"full_has_bin", [i64, i32, i32], [.bool], fullHasBinSpec, true⟩)
    (m5Env_row 0 ⟨"full_cong_eb_match", [i64, i32, i32, i32], [.bool],
      m5CongEbMatchSpec, true⟩)
    (m5Env_row 5 ⟨"full_add_bin", [i64, i32, i32], [i64], fullAddBinSpec, true⟩)
    _ nvDenseMem _ _ ⟨nvOneLitCfg, nvOneLitF0, nvDenseState, emp, rfl, nvDense_inv, hm,
      fun r s' m' hd hc hf hr hu hm' => ⟨s', hd, hc, hf, hr, hu, by rwa [sep_emp] at hm'⟩⟩

/-- Concrete `Mem 64` non-vacuity (`XPost := False`) for `full_congruence_dense` under
closed `m5CongBinsEnv`. -/
theorem m5_congruence_dense_nv :
    Func.wp m5CongBinsEnv full_congruence_dense_body (nvOneLitCfg.hdr, 1024#64, ()) nvDenseMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInv nvOneLitCfg nvOneLitF0 s' ∧
        s'.core.cur_vars = 1 ∧ s'.core.fuel = 0#64 ∧
        (r = 1#64 ∨ r = 20#64) ∧ (r = 20#64 → nvOneLitF0.Unsat) ∧
        FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvDenseState ⋆ emp) nvDenseMem := by
    rw [sep_emp]; exact nvDenseMem_ok
  exact m5_congruence_dense_wp m5CongBinsEnv
    (m5Env_row 1 ⟨"full_cong_extract_binaries", [i64], [i64], m5CongExtractBinariesSpec, true⟩)
    (m5Env_row 6 ⟨"full_cong_extract", [i64, i64, i64], [i64],
      FullM3CongBva.fullCongExtractTickSpec, true⟩)
    (m5Env_row 7 ⟨"full_cong_work_step", [i64, i64, i64, i64, i32], [i64],
      m3CongWorkStepSpec, true⟩)
    _ nvDenseMem _ _ ⟨nvOneLitCfg, nvOneLitF0, nvDenseState, emp, rfl, nvDense_inv, hm,
      fun r s' m' hd hc hf hr hu hm' => ⟨s', hd, hc, hf, hr, hu, by rwa [sep_emp] at hm'⟩⟩

end ModuleAndNV

end LeanQbe.T.Examples.Kissat.FullM5CongBins
