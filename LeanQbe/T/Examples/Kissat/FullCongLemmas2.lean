module

public import LeanQbe.T.Examples.Kissat.FullCongLemmas1

/-!
# Kissat `D-Full` Gate Extraction & Congruence Closure — Part 2 (`Stage 4`)

Builds on `FullCongLemmas1` to prove parametric `(Γ : Env)` `Func.wp` contracts for 4 gate
extraction & ternary lookup functions (`Full.lean` #3, #5, #6, #7):
3. `full_has_ternary` (`full_has_ternary_wp`)
5. `full_cong_extract_ite` (`full_cong_extract_ite_wp`)
6. `full_cong_emit_xor` (`full_cong_emit_xor_wp`)
7. `full_cong_try_xor_ite` (`full_cong_try_xor_ite_wp`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test
open FullCongSpecs FullCongHelpers
open scoped FullArenaTactics FullCongTactics

/-! ## 1. Pure gate-extraction, watch-slice & XOR polarity lemmas -/

private theorem slice_pop_step {F_cur : List (List Nat)} {k : FullCoreState} {a p rem : Nat}
    (hslice : if k.dense_mode = 0#64 then WatchSliceOk F_cur k a p rem
      else DenseWatchSliceOk F_cur k a p rem) (hpos : 0 < rem) :
    ∃ w0 : BitVec 32, k.wstk[p]? = some w0 ∧
      ((w0 &&& 0x80000000#32) ≠ 0#32 ∧
        (if k.dense_mode = 0#64 then WatchSliceOk F_cur k a (p + 1) (rem - 1)
         else DenseWatchSliceOk F_cur k a (p + 1) (rem - 1)) ∨
       (w0 &&& 0x80000000#32) = 0#32 ∧ 2 ≤ rem ∧
        ∃ cr : BitVec 32, k.wstk[p + 1]? = some cr ∧ cr.toNat ∈ fullArenaClauseRefsCore k ∧
        (if k.dense_mode = 0#64 then WatchSliceOk F_cur k a (p + 2) (rem - 2)
         else DenseWatchSliceOk F_cur k a (p + 2) (rem - 2))) := by
  by_cases hdm : k.dense_mode = 0#64 <;> simp only [hdm, ↓reduceIte] at hslice ⊢
  · cases hslice with
    | empty => omega
    | bin hp hf _ _ _ hrest => exact ⟨_, hp, Or.inl ⟨hf, hrest⟩⟩
    | large hp hp1 hf _ href hrest => exact ⟨_, hp, Or.inr ⟨hf, by omega, _, hp1, href, hrest⟩⟩
  · cases hslice with
    | empty => omega
    | bin hp hf _ _ _ hrest => exact ⟨_, hp, Or.inl ⟨hf, hrest⟩⟩
    | occ hp hp1 hf _ _ href hrest => exact ⟨_, hp, Or.inr ⟨hf, by omega, _, hp1, href, hrest⟩⟩

namespace FullCongHelpers

theorem garb_false_of_and_480000 {hdr : BitVec 32}
    (h : (hdr &&& 0x00480000#32) = 0#32) :
    ((hdr &&& 0x00080000#32) != 0#32) = false := by
  have hmask : (0x00480000#32 : BitVec 32) &&& 0x00080000#32 = 0x00080000#32 := by decide
  have hb : (hdr &&& 0x00080000#32) = 0#32 := by
    calc hdr &&& 0x00080000#32 = hdr &&& (0x00480000#32 &&& 0x00080000#32) := by rw [hmask]
      _ = (hdr &&& 0x00480000#32) &&& 0x00080000#32 := by rw [BitVec.and_assoc]
      _ = 0#32 := by rw [h]; decide
  simp [hb]

theorem arena_clause3_lits {k : FullCoreState} {cr : Nat}
    (hsz : fullArenaClauseSizeCore k cr = 3) (hbd : cr + 6 ≤ k.arena.length) :
    fullArenaClauseLitsCore k cr =
      [(k.arena[cr + 3]'(by omega)).toNat, (k.arena[cr + 4]'(by omega)).toNat,
       (k.arena[cr + 5]'(by omega)).toNat] := by
  unfold fullArenaClauseLitsCore; rw [hsz]
  apply List.ext_getElem
  · simp [List.length_take, List.length_drop]; omega
  · intro i hi1 _
    simp only [List.length_map, List.length_take, List.length_drop] at hi1
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
    rcases i with _ | _ | _ | i' <;> first | rfl | omega

end FullCongHelpers

private theorem litNeg_div2 (n : Nat) : litNeg n / 2 = n / 2 := litVar_litNeg n

private theorem bv32_ne_of_div2_ne {x y : BitVec 32} (h : x.toNat / 2 ≠ y.toNat / 2) : x ≠ y := by
  intro heq; subst heq; exact h rfl

private theorem div2_ne_of_xor1 {x y : BitVec 32} (h : x.toNat / 2 ≠ y.toNat / 2) :
    x.toNat / 2 ≠ (y ^^^ 1).toNat / 2 := by
  rw [bv32_xor1_litNeg, litNeg_div2]; exact h

private theorem div2_ne_of_xor1_l {x y : BitVec 32} (h : x.toNat / 2 ≠ y.toNat / 2) :
    (x ^^^ 1).toNat / 2 ≠ y.toNat / 2 := by
  rw [bv32_xor1_litNeg, litNeg_div2]; exact h

private theorem div2_ne_of_xor1_both {x y : BitVec 32} (h : x.toNat / 2 ≠ y.toNat / 2) :
    (x ^^^ 1).toNat / 2 ≠ (y ^^^ 1).toNat / 2 := by
  rw [bv32_xor1_litNeg, bv32_xor1_litNeg, litNeg_div2, litNeg_div2]; exact h

private theorem cur_vars_ge3_of_distinct {v0 v1 v2 n : Nat}
    (h0 : v0 < n) (h1 : v1 < n) (h2 : v2 < n)
    (h01 : v0 ≠ v1) (h02 : v0 ≠ v2) (h12 : v1 ≠ v2) : 3 ≤ n := by
  have hle := nodup_lt_length_le (n := n) (xs := [v0, v1, v2])
    (by simp [h01, h02, h12])
    (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption)
  simpa using hle

private theorem ternary_of_unassigned_hits {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hnd : FullArenaVarsNodup s) (hcl0 : s.core.cur_level = 0)
    {cr : Nat} {a b cl : BitVec 32}
    (hcr : cr ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s cr = false)
    (hnosat : ∀ k < fullArenaClauseSizeCore s.core cr,
      s.core.vals[(s.core.arena[cr + 3 + k]?.getD 0#32).toNat]?.getD 0#8 ≠ 1#8)
    (hcnt : ((fullArenaClauseLits s cr).filter (fun l => s.core.vals[l]?.getD 0#8 == 0#8)).length =
      3)
    (ha : a.toNat ∈ (fullArenaClauseLits s cr).filter (fun l => s.core.vals[l]?.getD 0#8 == 0#8))
    (hb : b.toNat ∈ (fullArenaClauseLits s cr).filter (fun l => s.core.vals[l]?.getD 0#8 == 0#8))
    (hc : cl.toNat ∈ (fullArenaClauseLits s cr).filter (fun l => s.core.vals[l]?.getD 0#8 == 0#8))
    (hab : a ≠ b) (hac : a ≠ cl) (hbc : b ≠ cl) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat, cl.toNat]) := by
  have hwf := hw.arena.refs_wf cr hcr
  have hbd : cr + 3 + fullArenaClauseSizeCore s.core cr ≤ s.core.arena.length := by
    have := hlen.core_ok.arena_len_le; have := hlen.core_ok.arena_len_arr; omega
  have hnd_lits : (fullArenaClauseLits s cr).Nodup := nodup_of_map_nodup (hnd cr hcr hng)
  let unass := (fullArenaClauseLits s cr).filter (fun l => s.core.vals[l]?.getD 0#8 == 0#8)
  have hsub := nodup_len3_subset (hnd_lits.filter _) hcnt ha hb hc
    (fun h => hab (BitVec.eq_of_toNat_eq h))
    (fun h => hac (BitVec.eq_of_toNat_eq h))
    (fun h => hbc (BitVec.eq_of_toNat_eq h))
  refine entails_of_eval_mem fun α hα => ?_
  have hsat_cl := CNF.entails_clause_def.mp (hw.arena.entails cr hcr hng) α hα
  rw [← clauseEvalVal_iff, clauseEvalVal, List.any_eq_true] at hsat_cl
  obtain ⟨l, hl_mem, hl_true⟩ := hsat_cl
  have hl_lt : l < 2 * s.core.cur_vars := hw.arena.lits_lt cr hcr hng l hl_mem
  have hv_dom := hw.vals_domain l hl_lt
  obtain ⟨k, hk_lt, hget_k⟩ := (mem_fullArenaClauseLitsCore_iff hbd).mp hl_mem
  have hne1 : s.core.vals[l]?.getD 0#8 ≠ 1#8 := by
    have h := hnosat k hk_lt
    have hget_a : s.core.arena[cr + 3 + k]?.getD 0#32 = s.core.arena[cr + 3 + k]'(by omega) := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    rwa [hget_a, hget_k] at h
  rcases hv_dom with hv0 | hv1 | hvm1
  · have hl_un : l ∈ unass := List.mem_filter.mpr ⟨hl_mem, by simp [hv0]⟩
    rcases hsub l hl_un with rfl | rfl | rfl
    · exact ⟨a.toNat, by simp, hl_true⟩
    · exact ⟨b.toNat, by simp, hl_true⟩
    · exact ⟨cl.toNat, by simp, hl_true⟩
  · exact absurd hv1 hne1
  · exfalso
    obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl_lt).mp hvm1
    have hlvl0 : (s.core.lvl[(s.core.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
      have := hw.lvl_le i hi; omega
    have hunit := hw.level0_sound i hi hlvl0; rw [heq] at hunit
    have hsat_u := CNF.entails_clause_def.mp hunit α hα
    rw [← clauseEvalVal_iff, clauseEvalVal] at hsat_u; have hln : l ^^^ 1 = litNeg l := rfl
    simp only [List.any_cons, List.any_nil, Bool.or_false, hln, evalLitVal_litNeg,
      hl_true] at hsat_u
    cases hsat_u

private theorem testBit_false_of_lt {a b : Nat} (h : a < 2 ^ b) : a.testBit b = false := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt h]; rfl

private theorem bv32_and_not1_toNat (x : BitVec 32) :
    (x &&& ~~~1#32).toNat = 2 * (x.toNat / 2) := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [BitVec.toNat_and, Nat.testBit_and]
  cases i with
  | zero => simp
  | succ k =>
    by_cases hk : k + 1 < 32
    · have hall : ∀ j < 32, 0 < j → (~~~1#32 : BitVec 32).toNat.testBit j = true := by decide
      rw [hall (k + 1) hk (by omega), Bool.and_true, Nat.testBit_succ, Nat.testBit_succ]
      congr 1; omega
    · have hx : x.toNat < 2 ^ (k + 1) :=
        Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) (by omega))
      have h2 : 2 * (x.toNat / 2) < 2 ^ (k + 1) := by omega
      rw [testBit_false_of_lt hx, testBit_false_of_lt h2, Bool.false_and]

private theorem bv32_even_or_bit_toNat (y b : BitVec 32) :
    ((y &&& ~~~1#32) ||| (b &&& 1#32)).toNat = 2 * (y.toNat / 2) + b.toNat % 2 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [BitVec.toNat_or, Nat.testBit_or, bv32_and_not1_toNat, BitVec.toNat_and, Nat.testBit_and]
  cases i with
  | zero =>
    have h1 : (1#32 : BitVec 32).toNat.testBit 0 = true := by decide
    rw [h1, Bool.and_true, Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one b.toNat with hb | hb <;> simp [hb] <;> omega
  | succ k =>
    have h0 : (1#32 : BitVec 32).toNat.testBit (k + 1) = false := by
      rw [show (1#32 : BitVec 32).toNat = 1 from rfl]
      exact testBit_false_of_lt (Nat.lt_of_lt_of_le (by omega)
        (Nat.pow_le_pow_right (by omega) (by omega : 1 ≤ k + 1)))
    rw [h0, Bool.and_false, Bool.or_false, Nat.testBit_succ, Nat.testBit_succ]
    congr 1; omega

private theorem litSign_of_mod2 (n : Nat) : litSign n = decide (n % 2 = 1) := by
  unfold litSign; rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

private theorem xor_emit_sound {f : CNF Nat} {cur_vars : Nat} {x0 x1 x2 : BitVec 32}
    (hx0 : x0.toNat < 2 * cur_vars) (hx1 : x1.toNat < 2 * cur_vars)
    (hx2 : x2.toNat < 2 * cur_vars)
    (hxor : XorGateDef f (litNeg x0.toNat) x1.toNat x2.toNat) :
    let lhs := ((x0 ^^^ 1#32) &&& ~~~1#32) ||| ((((x0 ^^^ 1#32) ^^^ x1) ^^^ x2) &&& 1#32)
    let r0 := x1 &&& ~~~1#32; let r1 := x2 &&& ~~~1#32
    lhs.toNat < 2 * cur_vars ∧ r0.toNat < 2 * cur_vars ∧ r1.toNat < 2 * cur_vars ∧
    XorGateDef f lhs.toNat r0.toNat r1.toNat ∧ XorGateDef f lhs.toNat r1.toNat r0.toNat := by
  intro lhs r0 r1
  have hlhs_n : lhs.toNat =
      2 * ((x0 ^^^ 1#32).toNat / 2) + (((x0 ^^^ 1#32) ^^^ x1) ^^^ x2).toNat % 2 :=
    bv32_even_or_bit_toNat (x0 ^^^ 1#32) (((x0 ^^^ 1#32) ^^^ x1) ^^^ x2)
  have hr0_n : r0.toNat = 2 * (x1.toNat / 2) := bv32_and_not1_toNat x1
  have hr1_n : r1.toNat = 2 * (x2.toNat / 2) := bv32_and_not1_toNat x2
  have hx0n_div : (x0 ^^^ 1#32).toNat / 2 = x0.toNat / 2 := by
    rw [bv32_xor1_eq_litNeg, litNeg_div2]
  have hlt_lhs : lhs.toNat < 2 * cur_vars := by omega
  have hlt_r0 : r0.toNat < 2 * cur_vars := by omega
  have hlt_r1 : r1.toNat < 2 * cur_vars := by omega
  have heval_eq : ∀ α : Nat → Bool, f.Sat α →
      evalLitVal α lhs.toNat = (evalLitVal α r0.toNat != evalLitVal α r1.toNat) := by
    intro α hα
    have hv := xorGateDef_eval hα hxor
    have hx0_eval : evalLitVal α (litNeg x0.toNat) =
        (α (x0.toNat / 2) != litSign (litNeg x0.toNat)) := by
      simp [evalLitVal, litVar, litNeg_div2]
    have hx1_eval : evalLitVal α x1.toNat = (α (x1.toNat / 2) != litSign x1.toNat) := rfl
    have hx2_eval : evalLitVal α x2.toNat = (α (x2.toNat / 2) != litSign x2.toNat) := rfl
    have hr0_eval : evalLitVal α r0.toNat = α (x1.toNat / 2) := by
      simp [evalLitVal, litVar, litSign, hr0_n]
    have hr1_eval : evalLitVal α r1.toNat = α (x2.toNat / 2) := by
      simp [evalLitVal, litVar, litSign, hr1_n]
    have hvar_lhs : litVar lhs.toNat = x0.toNat / 2 := by
      simp only [litVar, hlhs_n, hx0n_div]; omega
    have hmod_xor : (((x0 ^^^ 1#32) ^^^ x1) ^^^ x2).toNat % 2 =
        (((litNeg x0.toNat) % 2 ^^^ x1.toNat % 2) ^^^ x2.toNat % 2) := by
      rw [BitVec.toNat_xor, BitVec.toNat_xor, bv32_xor1_eq_litNeg]
      have h1 := Nat.xor_mod_two_pow (a := (litNeg x0.toNat) ^^^ x1.toNat) (b := x2.toNat) (n := 1)
      have h2 := Nat.xor_mod_two_pow (a := litNeg x0.toNat) (b := x1.toNat) (n := 1)
      simpa using h1.trans (by rw [h2])
    have hsign_lhs : litSign lhs.toNat =
        ((litSign (litNeg x0.toNat) != litSign x1.toNat) != litSign x2.toNat) := by
      rw [litSign_of_mod2, litSign_of_mod2, litSign_of_mod2, litSign_of_mod2, hlhs_n]
      have hlm : (2 * ((x0 ^^^ 1#32).toNat / 2) +
          (((x0 ^^^ 1#32) ^^^ x1) ^^^ x2).toNat % 2) % 2 =
          (((x0 ^^^ 1#32) ^^^ x1) ^^^ x2).toNat % 2 := by omega
      rw [hlm, hmod_xor]
      rcases Nat.mod_two_eq_zero_or_one (litNeg x0.toNat) with h0 | h0 <;>
        rcases Nat.mod_two_eq_zero_or_one x1.toNat with h1 | h1 <;>
        rcases Nat.mod_two_eq_zero_or_one x2.toNat with h2 | h2 <;>
        simp [h0, h1, h2]
    rw [evalLitVal, hvar_lhs, hsign_lhs, hr0_eval, hr1_eval]
    rw [hx0_eval, hx1_eval, hx2_eval] at hv
    cases ha0 : α (x0.toNat / 2) <;> cases ha1 : α (x1.toNat / 2) <;>
      cases ha2 : α (x2.toNat / 2) <;> cases hs0 : litSign (litNeg x0.toNat) <;>
      cases hs1 : litSign x1.toNat <;> cases hs2 : litSign x2.toNat <;> simp_all
  refine ⟨hlt_lhs, hlt_r0, hlt_r1, xorGateDef_of_eval_eq heval_eq,
    xorGateDef_of_eval_eq fun α hα => by
      rw [heval_eq α hα]; cases evalLitVal α r0.toNat <;> cases evalLitVal α r1.toNat <;> rfl⟩

private theorem xorGateDef_of_four {f : CNF Nat} {a b c : Nat}
    (h1 : f.EntailsClause (cnfClause [a, b, c]))
    (h2 : f.EntailsClause (cnfClause [a, litNeg b, litNeg c]))
    (h3 : f.EntailsClause (cnfClause [litNeg a, b, litNeg c]))
    (h4 : f.EntailsClause (cnfClause [litNeg a, litNeg b, c])) :
    XorGateDef f (litNeg a) b c ∧ XorGateDef f (litNeg b) a c ∧ XorGateDef f (litNeg c) a b := by
  have h1' : XorGateDef f (litNeg a) b c :=
    ⟨entails_perm_clause (fun x hx => by
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
       rcases hx with rfl | rfl | rfl <;> simp) h4,
     entails_perm_clause (fun x hx => by
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
       rcases hx with rfl | rfl | rfl <;> simp) h3,
     by simpa [litNeg_litNeg] using h1,
     by simpa [litNeg_litNeg] using h2⟩
  refine ⟨h1', xorGateDef_of_eval_eq fun α hα => ?_, xorGateDef_of_eval_eq fun α hα => ?_⟩
  · have hv := xorGateDef_eval hα h1'; rw [evalLitVal_litNeg] at hv ⊢
    cases ha : evalLitVal α a <;> cases hb : evalLitVal α b <;> cases hc : evalLitVal α c <;>
      simp_all
  · have hv := xorGateDef_eval hα h1'; rw [evalLitVal_litNeg] at hv ⊢
    cases ha : evalLitVal α a <;> cases hb : evalLitVal α b <;> cases hc : evalLitVal α c <;>
      simp_all

/-! ## 2. `Func.wp` Proofs #3, #5, #6, #7 -/

/-- **#3 (`full_has_ternary`)**: scans literal `a`'s watch/occurrence list for an irredundant
non-garbage clause whose exact unassigned literals (at `cur_level = 0`) are `{a, b, cl}`. -/
theorem full_has_ternary_wp (Γ : Env) :
    ∀ args m Q X, fullHasTernarySpec args m Q X →
      Func.wp Γ full_has_ternary_body args m Q X := by
  rintro ⟨h, a, b, cl, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hcl0, ha_lt, hm0, hQ⟩
  have hmx := c.hmaxv; have hwc := c.hwcap; have hac := c.harena
  unfold dimacsBound at hmx hwc hac; have hcl := hlen.core_ok
  have hcv_le := hcl.cur_vars_le; have hwvl := hcl.wvec_len
  have hwsl := hcl.wstk_len_arr; have hwle := hcl.wlen_le
  have harl := hcl.arena_len_arr; have hale := hcl.arena_len_le; have hvl := hcl.vals_len
  have hw_bd := hw.watches.bounds a.toNat ha_lt
  have hshl : (a.setWidth 64 <<< (1 : Nat)).toNat = 2 * a.toNat := by
    rw [bv64_shl1_toNat, bv_zext32_toNat]; omega
  have hshl1 : (a.setWidth 64 <<< (1 : Nat) + 1#64).toNat = 2 * a.toNat + 1 := by
    rw [BitVec.toNat_add, hshl]; show (2 * a.toNat + 1) % 2 ^ 64 = 2 * a.toNat + 1; omega
  have hslice0 : if s.core.dense_mode = 0#64 then
        WatchSliceOk F_cur s.core a.toNat (fullWatchOffCore s.core a.toNat)
          (fullWatchSizeCore s.core a.toNat)
      else DenseWatchSliceOk F_cur s.core a.toNat (fullWatchOffCore s.core a.toNat)
          (fullWatchSizeCore s.core a.toNat) := by
    have hwat := hw.watches; unfold ModeWatchesInv at hwat
    by_cases hdm : s.core.dense_mode = 0#64 <;> simp only [hdm, ↓reduceIte] at hwat ⊢
    · exact hwat.slices a.toNat ha_lt
    · exact hwat.slices a.toNat ha_lt
  fc_to_group
  generalize hoff_v :
    (s.core.wvec[(a.setWidth 64 <<< (1 : Nat)).toNat]'(by omega)).setWidth 64 = off
  generalize hwsz_v :
    (s.core.wvec[(a.setWidth 64 <<< (1 : Nat) + 1#64).toNat]'(by omega)).setWidth 64 = wsz
  have hoff_n : off.toNat = fullWatchOffCore s.core a.toNat := by
    rw [← hoff_v, bv_zext32_toNat]; unfold fullWatchOffCore
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact congrArg BitVec.toNat (list_getElem_congr hshl (by omega) (by omega))
  have hwsz_n : wsz.toNat = fullWatchSizeCore s.core a.toNat := by
    rw [← hwsz_v, bv_zext32_toNat]; unfold fullWatchSizeCore
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact congrArg BitVec.toNat (list_getElem_congr hshl1 (by omega) (by omega))
  have hend_n : (off + wsz).toNat = off.toNat + wsz.toNat := by bv_omega
  refine wp_loop_break_group (brkTs := [i64]) (lpTs := [i64])
    (fun _ mb => mb = m0)
    (fun rem (p, ()) ml =>
      ml = m0 ∧ p.toNat ≤ (off + wsz).toNat ∧ rem = (off + wsz).toNat - p.toNat ∧
      (if s.core.dense_mode = 0#64 then
         WatchSliceOk F_cur s.core a.toNat p.toNat ((off + wsz).toNat - p.toNat)
       else DenseWatchSliceOk F_cur s.core a.toNat p.toNat ((off + wsz).toNat - p.toNat)))
    ?_ ?_ ?_
  · rintro _ ⟨_, ⟨⟩⟩ mb hmb; subst mb
    fc_steps; exact hQ false (fun h => by cases h)
  · rintro B L rem ⟨p, ⟨⟩⟩ ml hB hL ⟨hml, hp_le, rfl, hslice⟩
    subst ml; fc_split
    · have hp_lt : p.toNat < (off + wsz).toNat := by bv_omega
      have hp_w : p.toNat < s.core.wstk.length := by omega
      obtain ⟨w0, hw0_get, hcase⟩ := slice_pop_step hslice (by omega)
      have hw0_eq : s.core.wstk[p.toNat]'hp_w = w0 := by
        rw [List.getElem?_eq_getElem hp_w] at hw0_get; exact Option.some.inj hw0_get
      have hp1_n : (p + 1#64).toNat = p.toNat + 1 := by bv_omega
      fc_split
      · -- binary watch -> continue
        rcases hcase with ⟨_, hrest⟩ | ⟨hf0, _⟩
        · fc_steps; exact hL ((off + wsz).toNat - (p + 1#64).toNat) (p + 1#64, ()) m0 (by omega)
            ⟨rfl, by omega, rfl, by simpa [hp1_n, Nat.sub_sub] using hrest⟩
        · exfalso; rw [hw0_eq] at hc; exact hc hf0
      · -- large watch -> load cr
        rcases hcase with ⟨hf1, _⟩ | ⟨_, hrem2, cr, hcr_get, hcr_ref, hrest2⟩
        · exfalso; rw [hw0_eq] at hc; exact hf1 (by grind)
        · have hp1_n' : (p + 1).toNat = p.toNat + 1 := hp1_n
          have hp1_w : (p + 1).toNat < s.core.wstk.length := by omega
          have hcr_eq : s.core.wstk[(p + 1).toNat]'hp1_w = cr := by
            rw [list_getElem_congr hp1_n' hp1_w (by omega)]
            rw [List.getElem?_eq_getElem (by omega)] at hcr_get
            exact Option.some.inj hcr_get
          have hp1_m : (p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 = p.toNat + 1 :=
            show (p.toNat + 1) % 2 ^ 64 = p.toNat + 1 from Nat.mod_eq_of_lt (by omega)
          have hcr_m : s.core.wstk[(p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'(by omega) = cr := by
            rw [list_getElem_congr hp1_m _ (by omega)]
            rw [List.getElem?_eq_getElem (by omega)] at hcr_get
            exact Option.some.inj hcr_get
          have hcr_wf := hw.arena.refs_wf cr.toNat hcr_ref
          have hp2_n : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by bv_omega
          have hcont2 : L (p + 1 + 1, ()) m0 :=
            hL ((off + wsz).toNat - (p + 1#64 + 1#64).toNat) (p + 1#64 + 1#64, ()) m0
              (by omega) ⟨rfl, by omega, rfl, by simpa [hp2_n, Nat.sub_sub] using hrest2⟩
          have hcr_arr : cr.toNat < s.core.arena.length := by omega
          have hcr2_m : (cr.toNat + (2 : BitVec 64).toNat) % 2 ^ 64 = cr.toNat + 2 :=
            show (cr.toNat + 2) % 2 ^ 64 = cr.toNat + 2 from Nat.mod_eq_of_lt (by omega)
          have hcr_w : ((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64).toNat <
              s.core.arena.length := by rw [hcr_eq, bv_zext32_toNat]; exact hcr_arr
          have hcr2_w : ((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64 + 2).toNat <
              s.core.arena.length := by
            rw [hcr_eq, BitVec.toNat_add, bv_zext32_toNat, hcr2_m]; omega
          fc_split
          · fc_split
            · exact hcont2
            · have hng_red := hc; clear hc; fc_split
              · exact hcont2
              · have hsz_ge3 := hc; clear hc
                simp only [hcr_m, hcr2_m] at hng_red hsz_ge3
                have hng : fullArenaClauseGarb s cr.toNat = false := by
                  unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
                  rw [List.getElem?_eq_getElem hcr_arr, Option.getD_some]
                  exact garb_false_of_and_480000 hng_red
                let sz_bv := s.core.arena[cr.toNat + 2]'(by omega)
                have hsz_eq : sz_bv.toNat = fullArenaClauseSizeCore s.core cr.toNat := by
                  unfold fullArenaClauseSizeCore
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                have hsz3 : 3 ≤ sz_bv.toNat := by
                  change ¬sz_bv.toNat < 3 at hsz_ge3; omega
                have hsz_cv : sz_bv.toNat ≤ s.core.cur_vars := by
                  rw [hsz_eq]; exact fullArenaClauseSize_le_cur_vars hlen hw hnd hcr_ref hng
                have hbd_ar : cr.toNat + 3 + sz_bv.toNat ≤ s.core.arena.length := by omega
                fc_to_group
                refine wp_loop_break_group (brkTs := [i32, .bool, .bool, .bool, .bool, i32])
                  (lpTs := [i32, .bool, .bool, .bool, i32])
                  (fun (nf, ha, hb, hcf, sat, _, ()) mb2 =>
                    mb2 = m0 ∧
                    (sat = false →
                      (∀ k < sz_bv.toNat,
                        s.core.vals[(s.core.arena[cr.toNat + 3 + k]?.getD 0#32).toNat]?.getD 0#8 ≠
                          1#8) ∧
                      nf.toNat = ((fullArenaClauseLits s cr.toNat).filter
                        (fun l => s.core.vals[l]?.getD 0#8 == 0#8)).length ∧
                      (ha = true → a.toNat ∈ (fullArenaClauseLits s cr.toNat).filter
                        (fun l => s.core.vals[l]?.getD 0#8 == 0#8)) ∧
                      (hb = true → b.toNat ∈ (fullArenaClauseLits s cr.toNat).filter
                        (fun l => s.core.vals[l]?.getD 0#8 == 0#8)) ∧
                      (hcf = true → cl.toNat ∈ (fullArenaClauseLits s cr.toNat).filter
                        (fun l => s.core.vals[l]?.getD 0#8 == 0#8))))
                  (fun rem2 (nf, ha, hb, hcf, i, ()) mi =>
                    mi = m0 ∧ i.toNat ≤ sz_bv.toNat ∧ rem2 = sz_bv.toNat - i.toNat ∧
                    (∀ k < i.toNat,
                      s.core.vals[(s.core.arena[cr.toNat + 3 + k]?.getD 0#32).toNat]?.getD 0#8 ≠
                        1#8) ∧
                    nf.toNat = (((fullArenaClauseLits s cr.toNat).take i.toNat).filter
                      (fun l => s.core.vals[l]?.getD 0#8 == 0#8)).length ∧
                    (ha = true → a.toNat ∈ ((fullArenaClauseLits s cr.toNat).take i.toNat).filter
                      (fun l => s.core.vals[l]?.getD 0#8 == 0#8)) ∧
                    (hb = true → b.toNat ∈ ((fullArenaClauseLits s cr.toNat).take i.toNat).filter
                      (fun l => s.core.vals[l]?.getD 0#8 == 0#8)) ∧
                    (hcf = true → cl.toNat ∈ ((fullArenaClauseLits s cr.toNat).take i.toNat).filter
                      (fun l => s.core.vals[l]?.getD 0#8 == 0#8)))
                  ?_ ?_ ?_
                · rintro _ ⟨nf, ha, hb, hcf, sat, _, ⟨⟩⟩ mb2 ⟨hmb2, hpost⟩
                  subst mb2; fc_steps
                  all_goals first
                    | exact hcont2
                    | (obtain ⟨hnosat, hcnt, hha, hhb, hhc⟩ := hpost (by grind)
                       have hnf3 : nf.toNat = 3 := by
                         have h : nf = 3#32 := by grind
                         rw [h]; rfl
                       exact hQ true fun _ hab hac hbc =>
                         ternary_of_unassigned_hits hlen hw hnd hcl0 hcr_ref hng
                           (hsz_eq ▸ hnosat) (hnf3 ▸ hcnt.symm)
                           (hha (by grind)) (hhb (by grind)) (hhc (by grind)) hab hac hbc)
                · rintro B2 L2 rem2 ⟨nf, ha, hb, hcf, i, ⟨⟩⟩ mi hB2 hL2
                    ⟨hmi, hi_le, rfl, hnosat_i, hcnt_i, hha_i, hhb_i, hhc_i⟩
                  subst mi; fc_split
                  · simp only [hcr_m, hcr2_m] at hc; have hi_lt : i.toNat < sz_bv.toNat := hc
                    have hi1_n : (i + 1#32).toNat = i.toNat + 1 :=
                      show (i.toNat + 1) % 2 ^ 32 = i.toNat + 1 from Nat.mod_eq_of_lt (by omega)
                    have hcr3i_m : (cr.toNat + (3 : BitVec 64).toNat + i.toNat) % 2 ^ 64 =
                        cr.toNat + 3 + i.toNat :=
                      show (cr.toNat + 3 + i.toNat) % 2 ^ 64 = cr.toNat + 3 + i.toNat from
                        Nat.mod_eq_of_lt (by omega)
                    let l := s.core.arena[cr.toNat + 3 + i.toNat]'(by omega)
                    have hl_mem : l.toNat ∈ fullArenaClauseLits s cr.toNat := by
                      rw [mem_fullArenaClauseLitsCore_iff (by omega)]
                      exact ⟨i.toNat, by omega, rfl⟩
                    have hl_lt : l.toNat < 2 * s.core.cur_vars :=
                      hw.arena.lits_lt cr.toNat hcr_ref hng l.toNat hl_mem
                    have htake_step :
                        (fullArenaClauseLits s cr.toNat).take (i.toNat + 1) =
                          (fullArenaClauseLits s cr.toNat).take i.toNat ++ [l.toNat] := by
                      have hlen_l : (fullArenaClauseLits s cr.toNat).length = sz_bv.toNat := by
                        unfold fullArenaClauseLits fullArenaClauseLitsCore
                        simp only [List.length_map, List.length_take, List.length_drop]; omega
                      have hget_l : (fullArenaClauseLits s cr.toNat)[i.toNat]'(by omega) =
                          l.toNat := by
                        unfold fullArenaClauseLits fullArenaClauseLitsCore
                        simp [List.getElem_map, List.getElem_take, List.getElem_drop, l]
                      rw [List.take_succ_eq_append_getElem (by omega), hget_l]
                    have hnf_le : nf.toNat ≤ i.toNat := by
                      rw [hcnt_i]; have h1 := List.length_filter_le
                        (l := (fullArenaClauseLits s cr.toNat).take i.toNat)
                        (p := fun l => s.core.vals[l]?.getD 0#8 == 0#8)
                      have h2 : ((fullArenaClauseLits s cr.toNat).take i.toNat).length ≤ i.toNat :=
                        List.length_take_le _ _
                      omega
                    have hnf1_n : (nf + 1#32).toNat = nf.toNat + 1 :=
                      show (nf.toNat + 1) % 2 ^ 32 = nf.toNat + 1 from Nat.mod_eq_of_lt (by omega)
                    have hcr3i_n : ((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64 + 3 +
                        i.setWidth 64).toNat = cr.toNat + 3 + i.toNat := by
                      rw [hcr_eq, BitVec.toNat_add, BitVec.toNat_add, bv_zext32_toNat,
                        bv_zext32_toNat]
                      show ((cr.toNat + 3) % 2 ^ 64 + i.toNat) % 2 ^ 64 = cr.toNat + 3 + i.toNat
                      omega
                    have hcr3i_w : ((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64 + 3 +
                        i.setWidth 64).toNat < s.core.arena.length := by omega
                    have hl_v : ((s.core.arena[((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64 +
                        3 + i.setWidth 64).toNat]'hcr3i_w).setWidth 64).toNat <
                        s.core.vals.length := by
                      rw [list_getElem_congr hcr3i_n hcr3i_w (by omega), bv_zext32_toNat]
                      change l.toNat < s.core.vals.length; omega
                    fc_split
                    · -- vals[l] > 0 -> break with sat = true
                      fc_steps
                      exact hB2 (nf, ha, hb, hcf, true, i, ()) m0 ⟨rfl, fun h => by cases h⟩
                    · -- vals[l] <= 0
                      simp only [hcr_m, hcr3i_m] at hc
                      have hne1_l : s.core.vals[l.toNat]?.getD 0#8 ≠ 1#8 := by
                        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                        intro h1
                        change (0#32).slt (BitVec.signExtend 32 (s.core.vals[l.toNat]'(by omega))) =
                          false at hc
                        rw [h1] at hc; exact absurd hc (by decide)
                      have hnosat_next : ∀ k < (i + 1#32).toNat,
                          s.core.vals[(s.core.arena[cr.toNat + 3 + k]?.getD 0#32).toNat]?.getD 0#8 ≠
                            1#8 := fun k hk => by
                        rw [hi1_n] at hk
                        by_cases hki : k = i.toNat
                        · subst hki
                          have ha_get : s.core.arena[cr.toNat + 3 + i.toNat]?.getD 0#32 = l := by
                            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                          rw [ha_get]; exact hne1_l
                        · exact hnosat_i k (by omega)
                      fc_to_group; refine wp_join_group (ts := [i32, .bool, .bool, .bool])
                        (fun (nf', ha', hb', hcf', ()) m' => m' = m0 ∧
                          nf'.toNat = (((fullArenaClauseLits s cr.toNat).take (i.toNat + 1)).filter
                            (fun x => s.core.vals[x]?.getD 0#8 == 0#8)).length ∧
                          (ha' = true → a.toNat ∈ ((fullArenaClauseLits s cr.toNat).take
                            (i.toNat + 1)).filter (fun x => s.core.vals[x]?.getD 0#8 == 0#8)) ∧
                          (hb' = true → b.toNat ∈ ((fullArenaClauseLits s cr.toNat).take
                            (i.toNat + 1)).filter (fun x => s.core.vals[x]?.getD 0#8 == 0#8)) ∧
                          (hcf' = true → cl.toNat ∈ ((fullArenaClauseLits s cr.toNat).take
                            (i.toNat + 1)).filter (fun x => s.core.vals[x]?.getD 0#8 == 0#8)))
                        ?_ ?_
                      · rintro _ ⟨nf', ha', hb', hcf', ⟨⟩⟩ m' ⟨hm', hcnt', hha', hhb', hhc'⟩
                        subst m'; fc_steps
                        exact hL2 (sz_bv.toNat - (i + 1#32).toNat)
                          (nf', ha', hb', hcf', i + 1#32, ()) m0 (by omega)
                          ⟨rfl, by omega, rfl, hnosat_next,
                           hi1_n ▸ hcnt', hi1_n ▸ hha', hi1_n ▸ hhb', hi1_n ▸ hhc'⟩
                      · intro Js hJs
                        fc_split
                        · -- vals[l] == 0 -> nf++, check l==a, l==b, l==c
                          simp only [hcr_m, hcr3i_m] at hc
                          have hval0 : s.core.vals[l.toNat]?.getD 0#8 = 0#8 := by
                            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                            have hdom := hw.vals_domain l.toNat hl_lt
                            rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hdom
                            rcases hdom with h | h | h
                            · exact h
                            · exfalso; rw [h] at hc; exact absurd hc (by decide)
                            · exfalso; rw [h] at hc; exact absurd hc (by decide)
                          have hfilt_step :
                              ((fullArenaClauseLits s cr.toNat).take (i.toNat + 1)).filter
                                (fun x => s.core.vals[x]?.getD 0#8 == 0#8) =
                              ((fullArenaClauseLits s cr.toNat).take i.toNat).filter
                                (fun x => s.core.vals[x]?.getD 0#8 == 0#8) ++ [l.toNat] := by
                            rw [htake_step, List.filter_append, List.filter_cons, hval0]; simp
                          fc_to_group; refine wp_join_group (ts := [.bool])
                            (fun (ha', ()) m' => m' = m0 ∧ (ha' = true → ha = true ∨ l = a)) ?_ ?_
                          · rintro _ ⟨ha', ⟨⟩⟩ m' ⟨hm', hha'⟩; subst m'
                            fc_to_group; refine wp_join_group (ts := [.bool])
                              (fun (hb', ()) m' => m' = m0 ∧ (hb' = true → hb = true ∨ l = b)) ?_ ?_
                            · rintro _ ⟨hb', ⟨⟩⟩ m' ⟨hm', hhb'⟩; subst m'
                              fc_to_group; refine wp_join_group (ts := [.bool])
                                (fun (hcf', ()) m' => m' = m0 ∧ (hcf' = true → hcf = true ∨ l = cl))
                                ?_ ?_
                              · rintro _ ⟨hcf', ⟨⟩⟩ m' ⟨hm', hhc'⟩; subst m'
                                fc_steps
                                refine hJs (nf + 1#32, ha', hb', hcf', ()) m0 ⟨rfl, ?_, ?_, ?_, ?_⟩
                                · rw [hfilt_step, List.length_append, hnf1_n, hcnt_i]; simp
                                · intro ht; rw [hfilt_step, List.mem_append]
                                  rcases hha' ht with h1 | h2
                                  · exact Or.inl (hha_i h1)
                                  · exact Or.inr (by simp [h2])
                                · intro ht; rw [hfilt_step, List.mem_append]
                                  rcases hhb' ht with h1 | h2
                                  · exact Or.inl (hhb_i h1)
                                  · exact Or.inr (by simp [h2])
                                · intro ht; rw [hfilt_step, List.mem_append]
                                  rcases hhc' ht with h1 | h2
                                  · exact Or.inl (hhc_i h1)
                                  · exact Or.inr (by simp [h2])
                              · intro Jc hJc; fc_steps
                                · simp only [hcr_m, hcr3i_m] at hc
                                  exact hJc (true, ()) m0 ⟨rfl, fun _ => Or.inr hc⟩
                                · exact hJc (hcf, ()) m0 ⟨rfl, fun h => Or.inl h⟩
                            · intro Jb hJb; fc_steps
                              · simp only [hcr_m, hcr3i_m] at hc
                                exact hJb (true, ()) m0 ⟨rfl, fun _ => Or.inr hc⟩
                              · exact hJb (hb, ()) m0 ⟨rfl, fun h => Or.inl h⟩
                          · intro Ja hJa; fc_steps
                            · simp only [hcr_m, hcr3i_m] at hc
                              exact hJa (true, ()) m0 ⟨rfl, fun _ => Or.inr hc⟩
                            · exact hJa (ha, ()) m0 ⟨rfl, fun h => Or.inl h⟩
                        · -- vals[l] != 0
                          simp only [hcr_m, hcr3i_m] at hc
                          have hval_ne0 : (s.core.vals[l.toNat]?.getD 0#8 == 0#8) = false := by
                            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                            refine beq_false_of_ne (fun h0 => hc ?_)
                            change BitVec.signExtend 32 (s.core.vals[l.toNat]'(by omega)) = 0#32
                            rw [h0]; rfl
                          have hfilt_step :
                              ((fullArenaClauseLits s cr.toNat).take (i.toNat + 1)).filter
                                (fun x => s.core.vals[x]?.getD 0#8 == 0#8) =
                              ((fullArenaClauseLits s cr.toNat).take i.toNat).filter
                                (fun x => s.core.vals[x]?.getD 0#8 == 0#8) := by
                            rw [htake_step, List.filter_append, List.filter_cons, hval_ne0]; simp
                          fc_steps; exact hJs (nf, ha, hb, hcf, ()) m0
                            ⟨rfl, by rw [hfilt_step]; exact hcnt_i,
                             by rw [hfilt_step]; exact hha_i,
                             by rw [hfilt_step]; exact hhb_i,
                             by rw [hfilt_step]; exact hhc_i⟩
                  · -- i >= sz -> break with sat = false
                    simp only [hcr_m, hcr2_m] at hc
                    have hi_eq : i.toNat = sz_bv.toNat := by
                      change ¬i.toNat < sz_bv.toNat at hc; omega
                    have htake_all : (fullArenaClauseLits s cr.toNat).take i.toNat =
                        fullArenaClauseLits s cr.toNat := by
                      apply List.take_of_length_le
                      unfold fullArenaClauseLits fullArenaClauseLitsCore
                      simp only [List.length_map, List.length_take, List.length_drop]; omega
                    rw [hi_eq] at hnosat_i; rw [htake_all] at hcnt_i hha_i hhb_i hhc_i
                    fc_steps; exact hB2 (nf, ha, hb, hcf, false, i, ()) m0
                      ⟨rfl, fun _ => ⟨hnosat_i, hcnt_i, hha_i, hhb_i, hhc_i⟩⟩
                · intro _ L2 _ hL2; fc_steps
                  exact hL2 (sz_bv.toNat - 0) (0#32, false, false, false, 0#32, ()) m0
                    ⟨rfl, Nat.zero_le _, rfl, fun _ h => by simp at h, rfl,
                     Bool.noConfusion, Bool.noConfusion, Bool.noConfusion⟩
    · fc_steps; exact hB (p, ()) m0 rfl
  · intro _ L _ hL; fc_steps
    refine hL ((off + wsz).toNat - off.toNat) (off, ()) m0 ⟨rfl, by omega, rfl, ?_⟩
    simpa [hend_n, hoff_n, hwsz_n] using hslice0

private theorem closed_cons_get {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {ts : List Ty} {b : Tup Val ts → Expr Val Cont rs} {Js : Tup Cont [ts]}
    (h : Closed Γ Q X (.cons b .nil) Js) (xs : Tup Val ts) (m : Mem 64)
    (hwp : wp Γ Q X (b xs) m) : Js.1 xs m := h.1 xs m hwp

private theorem bv64_add_n {x y : BitVec 64} (h : x.toNat + y.toNat < 2 ^ 64) :
    (x + y).toNat = x.toNat + y.toNat := Nat.mod_eq_of_lt h

private theorem ite_pick_e_ok {F_cur : List (List Nat)} {cv : Nat}
    {c_lit y l0 l1 l2 la lb lc : BitVec 32}
    (hcl : (cnfOfClauses F_cur).EntailsClause (cnfClause [l0.toNat, l1.toNat, l2.toNat]))
    (hnd : l0.toNat / 2 ≠ l1.toNat / 2 ∧ l0.toNat / 2 ≠ l2.toNat / 2 ∧
      l1.toNat / 2 ≠ l2.toNat / 2)
    (hlt : ∀ x ∈ [l0.toNat, l1.toNat, l2.toNat], x < 2 * cv)
    (h1 : la = c_lit) (h2 : lb = y ^^^ 1)
    (hcase : (la = l0 ∧ lb = l1 ∧ lc = l2) ∨ (la = l0 ∧ lb = l2 ∧ lc = l1) ∨
             (la = l1 ∧ lb = l0 ∧ lc = l2) ∨ (la = l1 ∧ lb = l2 ∧ lc = l0) ∨
             (la = l2 ∧ lb = l0 ∧ lc = l1) ∨ (la = l2 ∧ lb = l1 ∧ lc = l0)) :
    lc.toNat < 2 * cv ∧ lc.toNat / 2 ≠ c_lit.toNat / 2 ∧ lc.toNat / 2 ≠ y.toNat / 2 ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg y.toNat, c_lit.toNat, lc.toNat]) := by
  have hny : (y ^^^ 1 : BitVec 32).toNat = litNeg y.toNat := bv32_xor1_litNeg y
  have hdiv_ny : (y ^^^ 1 : BitVec 32).toNat / 2 = y.toNat / 2 := by rw [hny, litNeg_div2]
  rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    (subst h1 h2; refine ⟨hlt _ (by simp), by omega, by rw [← hdiv_ny]; omega,
      entails_perm_clause (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        rw [← hny]; rcases hx with rfl | rfl | rfl <;> simp) hcl⟩)

private theorem ite_emit_gateSeq {F_cur : List (List Nat)} {cur_vars cap g_len : Nat}
    {scr : List (BitVec 32)} {y2 c1 t2 e2 : BitVec 32}
    (hscrl : scr.length = cap) (hg5_le : g_len + 5 ≤ cap) (hcv3 : 3 ≤ cur_vars)
    (hy2_lt : y2.toNat < 2 * cur_vars) (hc1_lt : c1.toNat < 2 * cur_vars)
    (ht2_lt : t2.toNat < 2 * cur_vars) (he2_lt : e2.toNat < 2 * cur_vars)
    (hite2 : IteGateDef (cnfOfClauses F_cur) y2.toNat c1.toNat t2.toNat e2.toNat)
    (hseq0 : GateSeqOk F_cur cur_vars scr g_len 0) :
    let scr5 := ((((scr.set g_len y2).set (g_len + 1) ((2#32 <<< 28) ||| 3#32)).set
      (g_len + 2) c1).set (g_len + 3) t2).set (g_len + 4) e2
    scr5.length = cap ∧ (∀ idx < g_len, scr5[idx]? = scr[idx]?) ∧
      GateSeqOk F_cur cur_vars scr5 (g_len + 5) 0 := by
  intro scr5
  have hlen5 : scr5.length = cap := by simp [scr5, hscrl]
  have hpref : ∀ idx < g_len, scr5[idx]? = scr[idx]? := fun idx hi => by
    simp only [scr5]; repeat rw [List.getElem?_set_ne (by omega)]
  have h0 : scr5[g_len]? = some y2 := by
    simp only [scr5]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by omega)]
  have h1 : scr5[g_len + 1]? = some ((2#32 <<< 28) ||| 3#32) := by
    simp only [scr5]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp [hscrl]; omega)]
  have h2 : scr5[g_len + 2]? = some c1 := by
    simp only [scr5]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by simp [hscrl]; omega)]
  have h3 : scr5[g_len + 3]? = some t2 := by
    simp only [scr5]; rw [List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by simp [hscrl]; omega)]
  have h4 : scr5[g_len + 4]? = some e2 := by
    simp only [scr5]; rw [List.getElem?_set_self (by simp [hscrl]; omega)]
  have hg_at : GateAt F_cur cur_vars scr5 (g_len + 5) g_len := by
    refine ⟨y2, (2#32 <<< 28) ||| 3#32, h0, h1, hy2_lt, by show g_len + 2 + 3 ≤ g_len + 5; omega,
      hcv3, by decide, fun k hk => ?_,
      Or.inr (Or.inr ⟨rfl, rfl, by rw [h2, h3, h4]; simpa using hite2⟩)⟩
    have hk3 : k < 3 := hk
    match k with
    | 0 => exact ⟨c1, h2, hc1_lt⟩
    | 1 => exact ⟨t2, h3, ht2_lt⟩
    | 2 => exact ⟨e2, h4, he2_lt⟩
    | _ + 3 => omega
  refine ⟨hlen5, hpref, gateSeqOk_append (by omega) hpref (.step hg_at ?_) hseq0⟩
  simpa [h1] using GateSeqOk.done

/-- **#5 (`full_cong_extract_ite`)**: finds a complementary ternary clause pair completing an ITE
gate definition, normalizes polarities, and emits a 5-word `tag=2, arity=3` gate entry. -/
theorem full_cong_extract_ite_wp (Γ : Env)
    (hHasTern : ∀ args m Q X, fullHasTernarySpec args m Q X →
      Γ "full_has_ternary" [i64, i32, i32, i32] [.bool] args m Q X) :
    ∀ args m Q X, fullCongExtractIteSpec args m Q X →
      Func.wp Γ full_cong_extract_ite_body args m Q X := by
  rintro ⟨h, c_lit, y, t, g_len, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hcl0, hc_lt, hy_lt, ht_lt,
     hcy, hct, hyt, hcl1, hcl2, hglen_le, hseq0, hm0, hQ⟩
  have hmx := c.hmaxv; have hwc := c.hwcap; have hac := c.harena; have hsc := c.hscr
  unfold dimacsBound at hmx hwc hac hsc; have hcl := hlen.core_ok; have hsl := hlen.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hwvl := hcl.wvec_len
  have hwsl := hcl.wstk_len_arr; have hwle := hcl.wlen_le
  have harl := hcl.arena_len_arr; have hale := hcl.arena_len_le
  have hscrl := hsl.scratch_buf_len
  have hcv3 : 3 ≤ s.core.cur_vars :=
    cur_vars_ge3_of_distinct (by omega) (by omega) (by omega) hcy hct hyt
  have hw_bd := hw.watches.bounds c_lit.toNat hc_lt
  have hshl : (c_lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * c_lit.toNat := by
    rw [bv64_shl1_toNat, bv_zext32_toNat]; omega
  have hshl1 : (c_lit.setWidth 64 <<< (1 : Nat) + 1#64).toNat = 2 * c_lit.toNat + 1 := by
    rw [BitVec.toNat_add, hshl]; show (2 * c_lit.toNat + 1) % 2 ^ 64 = 2 * c_lit.toNat + 1; omega
  have hslice0 : if s.core.dense_mode = 0#64 then
        WatchSliceOk F_cur s.core c_lit.toNat (fullWatchOffCore s.core c_lit.toNat)
          (fullWatchSizeCore s.core c_lit.toNat)
      else DenseWatchSliceOk F_cur s.core c_lit.toNat (fullWatchOffCore s.core c_lit.toNat)
          (fullWatchSizeCore s.core c_lit.toNat) := by
    have hwat := hw.watches; unfold ModeWatchesInv at hwat
    by_cases hdm : s.core.dense_mode = 0#64 <;> simp only [hdm, ↓reduceIte] at hwat ⊢
    · exact hwat.slices c_lit.toNat hc_lt
    · exact hwat.slices c_lit.toNat hc_lt
  fc_to_group
  generalize hoff_v :
    (s.core.wvec[(c_lit.setWidth 64 <<< (1 : Nat)).toNat]'(by omega)).setWidth 64 = off
  generalize hwsz_v :
    (s.core.wvec[(c_lit.setWidth 64 <<< (1 : Nat) + 1#64).toNat]'(by omega)).setWidth 64 = wsz
  have hoff_n : off.toNat = fullWatchOffCore s.core c_lit.toNat := by
    rw [← hoff_v, bv_zext32_toNat]; unfold fullWatchOffCore
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact congrArg BitVec.toNat (list_getElem_congr hshl (by omega) (by omega))
  have hwsz_n : wsz.toNat = fullWatchSizeCore s.core c_lit.toNat := by
    rw [← hwsz_v, bv_zext32_toNat]; unfold fullWatchSizeCore
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact congrArg BitVec.toNat (list_getElem_congr hshl1 (by omega) (by omega))
  have hend_n : (off + wsz).toNat = off.toNat + wsz.toNat := by bv_omega
  refine wp_loop_break_group (brkTs := [i32, i32, i32, i64]) (lpTs := [i64])
    (fun _ mb => mb = m0)
    (fun rem (p, ()) ml =>
      ml = m0 ∧ p.toNat ≤ (off + wsz).toNat ∧ rem = (off + wsz).toNat - p.toNat ∧
      (if s.core.dense_mode = 0#64 then
         WatchSliceOk F_cur s.core c_lit.toNat p.toNat ((off + wsz).toNat - p.toNat)
       else DenseWatchSliceOk F_cur s.core c_lit.toNat p.toNat ((off + wsz).toNat - p.toNat)))
    ?_ ?_ ?_
  · rintro _ ⟨_, _, _, _, ⟨⟩⟩ mb hmb; subst mb
    fc_steps
    exact hQ g_len s.scratch.scratch_buf m0 hscrl (Or.inl rfl) (fun _ _ => rfl) hseq0 hm0
  · rintro B L rem ⟨p, ⟨⟩⟩ ml hB hL ⟨hml, hp_le, rfl, hslice⟩
    subst ml
    fc_split
    · have hp_lt : p.toNat < (off + wsz).toNat := by bv_omega
      have hp_w : p.toNat < s.core.wstk.length := by omega
      obtain ⟨w0, hw0_get, hcase⟩ := slice_pop_step hslice (by omega)
      have hw0_eq : s.core.wstk[p.toNat]'hp_w = w0 := by
        rw [List.getElem?_eq_getElem hp_w] at hw0_get; exact Option.some.inj hw0_get
      have hp1_n : (p + 1#64).toNat = p.toNat + 1 := by bv_omega
      fc_split
      · rcases hcase with ⟨_, hrest⟩ | ⟨hf0, _⟩
        · exact hL ((off + wsz).toNat - (p + 1#64).toNat) (p + 1#64, ()) m0 (by omega)
            ⟨rfl, by omega, rfl, by simpa [hp1_n, Nat.sub_sub] using hrest⟩
        · exfalso; rw [hw0_eq] at hc; exact hc hf0
      · rcases hcase with ⟨hf1, _⟩ | ⟨_, hrem2, cr, hcr_get, hcr_ref, hrest2⟩
        · exfalso; rw [hw0_eq] at hc; exact hf1 (by grind)
        · have hp1_n' : (p + 1).toNat = p.toNat + 1 := hp1_n
          have hp1_w : (p + 1).toNat < s.core.wstk.length := by omega
          have hcr_eq : s.core.wstk[(p + 1).toNat]'hp1_w = cr := by
            rw [list_getElem_congr hp1_n' hp1_w (by omega)]
            rw [List.getElem?_eq_getElem (by omega)] at hcr_get
            exact Option.some.inj hcr_get
          have hp1_m : (p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 = p.toNat + 1 :=
            show (p.toNat + 1) % 2 ^ 64 = p.toNat + 1 from Nat.mod_eq_of_lt (by omega)
          have hcr_m : s.core.wstk[(p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'(by omega) = cr := by
            rw [list_getElem_congr hp1_m _ (by omega)]
            rw [List.getElem?_eq_getElem (by omega)] at hcr_get
            exact Option.some.inj hcr_get
          have hcr_wf := hw.arena.refs_wf cr.toNat hcr_ref
          have hp2_n : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by bv_omega
          have hcont2 : L (p + 1 + 1, ()) m0 :=
            hL ((off + wsz).toNat - (p + 1#64 + 1#64).toNat) (p + 1#64 + 1#64, ()) m0
              (by omega) ⟨rfl, by omega, rfl, by simpa [hp2_n, Nat.sub_sub] using hrest2⟩
          have hcr_arr : cr.toNat < s.core.arena.length := by omega
          have hcr2_m : (cr.toNat + (2 : BitVec 64).toNat) % 2 ^ 64 = cr.toNat + 2 :=
            show (cr.toNat + 2) % 2 ^ 64 = cr.toNat + 2 from Nat.mod_eq_of_lt (by omega)
          have hcr_w : ((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64).toNat <
              s.core.arena.length := by rw [hcr_eq, bv_zext32_toNat]; exact hcr_arr
          have hcr2_w : ((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64 + 2).toNat <
              s.core.arena.length := by
            rw [hcr_eq, BitVec.toNat_add, bv_zext32_toNat, hcr2_m]; omega
          fc_split
          · fc_split
            · exact hcont2
            · have hng_red := hc; clear hc
              fc_split
              · exact hcont2
              · have hsz3_bv := hc; clear hc
                simp only [hcr_m, hcr2_m] at hng_red hsz3_bv
                have hng : fullArenaClauseGarb s cr.toNat = false := by
                  unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
                  rw [List.getElem?_eq_getElem hcr_arr, Option.getD_some]
                  exact garb_false_of_and_480000 hng_red
                have hsz3 : fullArenaClauseSizeCore s.core cr.toNat = 3 := by
                  unfold fullArenaClauseSizeCore
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                  exact congrArg BitVec.toNat hsz3_bv
                have hbd6 : cr.toNat + 6 ≤ s.core.arena.length := by omega
                have hlits3 := arena_clause3_lits (k := s.core) (cr := cr.toNat) hsz3 hbd6
                have hcl3 := hw.arena.entails cr.toNat hcr_ref hng
                have hnd3 := hnd cr.toNat hcr_ref hng
                have hlt3 := hw.arena.lits_lt cr.toNat hcr_ref hng
                unfold fullArenaClauseLits at hnd3
                rw [hlits3] at hcl3 hnd3 hlt3
                simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
                  List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hnd3
                have hcr3_m : (cr.toNat + (3 : BitVec 64).toNat) % 2 ^ 64 = cr.toNat + 3 :=
                  show (cr.toNat + 3) % 2 ^ 64 = cr.toNat + 3 from Nat.mod_eq_of_lt (by omega)
                have hcr4_m : (cr.toNat + (4 : BitVec 64).toNat) % 2 ^ 64 = cr.toNat + 4 :=
                  show (cr.toNat + 4) % 2 ^ 64 = cr.toNat + 4 from Nat.mod_eq_of_lt (by omega)
                have hcr5_m : (cr.toNat + (5 : BitVec 64).toNat) % 2 ^ 64 = cr.toNat + 5 :=
                  show (cr.toNat + 5) % 2 ^ 64 = cr.toNat + 5 from Nat.mod_eq_of_lt (by omega)
                have hcr3_w : ((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64 + 3).toNat <
                    s.core.arena.length := by
                  rw [hcr_eq, BitVec.toNat_add, bv_zext32_toNat, hcr3_m]; omega
                have hcr4_w : ((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64 + 4).toNat <
                    s.core.arena.length := by
                  rw [hcr_eq, BitVec.toNat_add, bv_zext32_toNat, hcr4_m]; omega
                have hcr5_w : ((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64 + 5).toNat <
                    s.core.arena.length := by
                  rw [hcr_eq, BitVec.toNat_add, bv_zext32_toNat, hcr5_m]; omega
                have hl0_eq : s.core.arena[((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64 +
                    3).toNat]'hcr3_w = s.core.arena[cr.toNat + 3]'(by omega) :=
                  list_getElem_congr (by rw [hcr_eq, BitVec.toNat_add, bv_zext32_toNat, hcr3_m]) _ _
                have hl1_eq : s.core.arena[((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64 +
                    4).toNat]'hcr4_w = s.core.arena[cr.toNat + 4]'(by omega) :=
                  list_getElem_congr (by rw [hcr_eq, BitVec.toNat_add, bv_zext32_toNat, hcr4_m]) _ _
                have hl2_eq : s.core.arena[((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64 +
                    5).toNat]'hcr5_w = s.core.arena[cr.toNat + 5]'(by omega) :=
                  list_getElem_congr (by rw [hcr_eq, BitVec.toNat_add, bv_zext32_toNat, hcr5_m]) _ _
                fc_to_group
                refine wp_join_group (ts := [i32])
                  (fun (e, ()) mj => mj = m0 ∧
                    (e ≠ 0xFFFFFFFF#32 →
                      e.toNat < 2 * s.core.cur_vars ∧
                      e.toNat / 2 ≠ c_lit.toNat / 2 ∧ e.toNat / 2 ≠ y.toNat / 2 ∧
                      (cnfOfClauses F_cur).EntailsClause
                        (cnfClause [litNeg y.toNat, c_lit.toNat, e.toNat])))
                  ?_ ?_
                · rintro _ ⟨e, ⟨⟩⟩ mj ⟨hmj, he_ok⟩
                  subst mj
                  fc_split
                  · have he_ne : e ≠ 0xFFFFFFFF#32 := hc
                    obtain ⟨he_lt, hec, hey, hcl3_ite⟩ := he_ok he_ne
                    fc_steps
                    c0_call hHasTern
                    refine ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hcl0, hc_lt, hm0,
                      fun ok hok => ?_⟩
                    fc_split
                    · -- ok = true -> emit ITE gate!
                      have hne_ce : c_lit ≠ e ^^^ 1 :=
                        bv32_ne_of_div2_ne (div2_ne_of_xor1 (Ne.symm hec))
                      have hne_cy : c_lit ≠ y := bv32_ne_of_div2_ne hcy
                      have hne_ey : e ^^^ 1 ≠ y :=
                        bv32_ne_of_div2_ne (div2_ne_of_xor1_l hey)
                      have hcl4 := hok (by cases ok <;> simp_all) hne_ce hne_cy hne_ey
                      have hcl4' : (cnfOfClauses F_cur).EntailsClause
                          (cnfClause [y.toNat, c_lit.toNat, litNeg e.toNat]) := by
                        rw [bv32_xor1_litNeg] at hcl4
                        exact entails_perm_clause (fun x hx => by
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
                          rcases hx with rfl | rfl | rfl <;> simp) hcl4
                      have hite0 : IteGateDef (cnfOfClauses F_cur)
                          y.toNat c_lit.toNat t.toNat e.toNat :=
                        ⟨hcl1, hcl4', hcl2, hcl3_ite⟩
                      clear hl0_eq hl1_eq hl2_eq hcl1 hcl2 hcl3_ite hcl4 hcl4' hok hne_ce hne_cy
                        hne_ey hec hey he_ne he_ok hcy hct hyt hHasTern hlt3 hnd3 hcl3 hlits3
                        hbd6 hsz3 hng hcr_wf hrest2 hL hslice hB hslice0 hw_bd hcl0 hnd hw hlen
                      fc_to_group
                      refine wp_join_group (ts := [i32, i32, i32])
                        (fun (c1, t1, e1, ()) m1 => m1 = m0 ∧
                          c1.toNat < 2 * s.core.cur_vars ∧ t1.toNat < 2 * s.core.cur_vars ∧
                          e1.toNat < 2 * s.core.cur_vars ∧
                          IteGateDef (cnfOfClauses F_cur) y.toNat c1.toNat t1.toNat e1.toNat)
                        ?_ ?_
                      · rintro _ ⟨c1, t1, e1, ⟨⟩⟩ m1 ⟨hm1, hc1_lt, ht1_lt, he1_lt, hite1⟩
                        subst m1
                        fc_to_group
                        refine wp_join_group (ts := [i32, i32, i32])
                          (fun (y2, t2, e2, ()) m2 => m2 = m0 ∧
                            y2.toNat < 2 * s.core.cur_vars ∧ t2.toNat < 2 * s.core.cur_vars ∧
                            e2.toNat < 2 * s.core.cur_vars ∧
                            IteGateDef (cnfOfClauses F_cur) y2.toNat c1.toNat t2.toNat e2.toNat)
                          ?_ ?_
                        · rintro _ ⟨y2, t2, e2, ⟨⟩⟩ m2 ⟨hm2, hy2_lt, ht2_lt, he2_lt, hite2⟩
                          subst m2
                          have hi32 : i32.bytes = 4 := rfl
                          have hg1 : (g_len + 1).toNat = g_len.toNat + 1 := bv64_add_n (by omega)
                          have hg2 : (g_len + 2).toNat = g_len.toNat + 2 := bv64_add_n (by omega)
                          have hg3 : (g_len + 3).toNat = g_len.toNat + 3 := bv64_add_n (by omega)
                          have hg4 : (g_len + 4).toNat = g_len.toNat + 4 := bv64_add_n (by omega)
                          have hg5 : (g_len + 5).toNat = g_len.toNat + 5 := bv64_add_n (by omega)
                          have hfs := focus_full_scratch_buf hm0; clear hm0
                          generalize hR_scr : FullScrBufRest c s ⋆ R = R_scr at hfs
                          have hsc_len : s.scratch.scratch_buf.length = c.scratch_cap := hscrl
                          have hg0_lt : g_len.toNat < s.scratch.scratch_buf.length := by omega
                          have hg1_lt : (g_len + 1).toNat < s.scratch.scratch_buf.length := by omega
                          have hg2_lt : (g_len + 2).toNat < s.scratch.scratch_buf.length := by omega
                          have hg3_lt : (g_len + 3).toNat < s.scratch.scratch_buf.length := by omega
                          have hg4_lt : (g_len + 4).toNat < s.scratch.scratch_buf.length := by omega
                          fc_steps; subst hR_scr
                          obtain ⟨hlen5, hpref, hseq5⟩ := ite_emit_gateSeq hscrl (by omega) hcv3
                            hy2_lt hc1_lt ht2_lt he2_lt hite2 hseq0
                          rw [hg1, hg2, hg3, hg4] at hm
                          exact hQ (g_len + 5) _ m hlen5 (Or.inr rfl) hpref (hg5 ▸ hseq5)
                            (unfocus_full_scratch_buf hm)
                        · intro Jy hJy; c0_let_simp; refine ⟨fun _ => ?_, fun _ => ?_⟩
                          · c0_let_simp
                            exact hJy (y ^^^ 1#32, t1 ^^^ 1#32, e1 ^^^ 1#32, ()) m0
                              ⟨rfl, by rw [bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even hy_lt,
                               by rw [bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even ht1_lt,
                               by rw [bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even he1_lt,
                               by simp only [bv32_xor1_eq_litNeg]; exact iteGateDef_flip_out hite1⟩
                          · c0_let_simp
                            exact hJy (y, t1, e1, ()) m0 ⟨rfl, hy_lt, ht1_lt, he1_lt, hite1⟩
                      · intro Jc hJc; c0_let_simp; refine ⟨fun _ => ?_, fun _ => ?_⟩
                        · c0_let_simp
                          exact hJc (c_lit ^^^ 1#32, e, t, ()) m0
                            ⟨rfl, by rw [bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even hc_lt,
                             he_lt, ht_lt,
                             by rw [bv32_xor1_eq_litNeg]; exact iteGateDef_flip_cond hite0⟩
                        · c0_let_simp
                          exact hJc (c_lit, t, e, ()) m0 ⟨rfl, hc_lt, ht_lt, he_lt, hite0⟩
                    · exact hcont2
                  · exact hcont2
                · -- 6-way if/else-if for e (pure linear stepping, zero c0_bound)
                  intro Je hJe
                  have hJe' : ∀ (v : Val i32) (m : Mem 64), (m = m0 ∧ (v ≠ 0xFFFFFFFF#32 →
                      v.toNat < 2 * s.core.cur_vars ∧ v.toNat / 2 ≠ c_lit.toNat / 2 ∧
                      v.toNat / 2 ≠ y.toNat / 2 ∧ (cnfOfClauses F_cur).EntailsClause
                        (cnfClause [litNeg y.toNat, c_lit.toNat, v.toNat]))) →
                      Je (v, ()) m := fun v m h => hJe (v, ()) m h
                  clear hJe
                  repeat (
                    intro Js hJs
                    suffices hnext : Js.1 () m0 by
                      c0_let_simp; refine ⟨fun h1 => ?_, fun _ => hnext⟩
                      c0_let_simp; refine ⟨fun h2 => ?_, fun _ => hnext⟩
                      c0_let_simp
                      refine hJe' _ m0 ⟨rfl, fun _ => ite_pick_e_ok hcl3
                        ⟨hnd3.1.1, hnd3.1.2, hnd3.2.1⟩ hlt3
                        (beq_iff_eq.mp h1) (beq_iff_eq.mp h2) ?_⟩
                      rw [hl0_eq, hl1_eq, hl2_eq]; simp
                    refine closed_cons_get hJs () m0 fun Jf hJf => ?_
                    have hJe' := fun v m h => closed_cons_get hJf (v, ()) m (hJe' v m h))
                  c0_let_simp; refine ⟨fun h1 => ?_, fun _ => hJe' 0xFFFFFFFF#32 m0
                    ⟨rfl, fun h => absurd rfl h⟩⟩
                  c0_let_simp; refine ⟨fun h2 => ?_, fun _ => hJe' 0xFFFFFFFF#32 m0
                    ⟨rfl, fun h => absurd rfl h⟩⟩
                  c0_let_simp; refine hJe' _ m0 ⟨rfl, fun _ => ite_pick_e_ok hcl3
                    ⟨hnd3.1.1, hnd3.1.2, hnd3.2.1⟩ hlt3
                    (beq_iff_eq.mp h1) (beq_iff_eq.mp h2) ?_⟩
                  rw [hl0_eq, hl1_eq, hl2_eq]; simp
    · exact hB (c_lit, y, t, p, ()) m0 rfl
  · intro _ L _ hL; c0_let_simp
    refine hL ((off + wsz).toNat - off.toNat) (off, ()) m0 ⟨rfl, by omega, rfl, ?_⟩
    simpa [hend_n, hoff_n, hwsz_n] using hslice0

/-- **#6 (`full_cong_emit_xor`)**: emits one polarity-normalized 4-word `tag=1, arity=2` XOR gate
record into `scr[g_len ..< g_len + 4)`. -/
theorem full_cong_emit_xor_wp (Γ : Env) :
    ∀ args m Q X, fullCongEmitXorSpec args m Q X →
      Func.wp Γ full_cong_emit_xor_body args m Q X := by
  rintro ⟨scr_ptr, g_len, x0, x1, x2, ⟨⟩⟩ m0 Q X
    ⟨F_cur, cur_vars, scr, R, hx0, hx1, hx2, hcv2, hg_le, hscr_lt, hxor, hseq0, hm0, hQ⟩
  have hxs := xor_emit_sound hx0 hx1 hx2 hxor
  have hi32 : i32.bytes = 4 := rfl
  have hg1 : (g_len + 1).toNat = g_len.toNat + 1 := by bv_omega
  have hg2 : (g_len + 2).toNat = g_len.toNat + 2 := by bv_omega
  have hg3 : (g_len + 3).toNat = g_len.toNat + 3 := by bv_omega
  let lhs := ((x0 ^^^ 1#32) &&& ~~~1#32) ||| ((((x0 ^^^ 1#32) ^^^ x1) ^^^ x2) &&& 1#32)
  let r0 := x1 &&& ~~~1#32
  let r1 := x2 &&& ~~~1#32
  have hfinish : ∀ (a0 a1 : BitVec 32) (m : Mem 64),
      ((a0 = r0 ∧ a1 = r1) ∨ (a0 = r1 ∧ a1 = r0)) →
      let scr1 := scr.set g_len.toNat lhs
      let scr2 := scr1.set (g_len.toNat + 1) ((1#32 <<< 28) ||| 2#32)
      let scr3 := scr2.set (g_len.toNat + 2) a0
      let scr4 := scr3.set (g_len.toNat + 3) a1
      (array (t := i32) scr_ptr scr4 ⋆ R) m → Q (g_len + 4#64, ()) m := by
    intro a0 a1 m hpair scr1 scr2 scr3 scr4 hm4
    have hlen4 : scr4.length = scr.length := by simp [scr4, scr3, scr2, scr1]
    have hpref : ∀ idx < g_len.toNat, scr4[idx]? = scr[idx]? := fun idx hi => by
      simp only [scr4, scr3, scr2, scr1]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    have hg_at : GateAt F_cur cur_vars scr4 (g_len.toNat + 4) g_len.toNat := by
      have h0 : scr4[g_len.toNat]? = some lhs := by
        simp only [scr4, scr3, scr2, scr1]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)]
      have h1 : scr4[g_len.toNat + 1]? = some ((1#32 <<< 28) ||| 2#32) := by
        simp only [scr4, scr3, scr2, scr1]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_self (by simp; omega)]
      have h2 : scr4[g_len.toNat + 2]? = some a0 := by
        simp only [scr4, scr3, scr2, scr1]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega)]
      have h3 : scr4[g_len.toNat + 3]? = some a1 := by
        simp only [scr4, scr3, scr2, scr1]
        rw [List.getElem?_set_self (by simp; omega)]
      refine ⟨lhs, (1#32 <<< 28) ||| 2#32, h0, h1, hxs.1,
        by show g_len.toNat + 2 + 2 ≤ g_len.toNat + 4; omega, hcv2, by decide, ?_, ?_⟩
      · intro k hk; have hk2 : k < 2 := hk
        match k with
        | 0 => exact ⟨a0, h2, by
            rcases hpair with ⟨rfl, _⟩ | ⟨rfl, _⟩; exact hxs.2.1; exact hxs.2.2.1⟩
        | 1 => exact ⟨a1, h3, by
            rcases hpair with ⟨_, rfl⟩ | ⟨_, rfl⟩; exact hxs.2.2.1; exact hxs.2.1⟩
        | _ + 2 => omega
      · right; left; refine ⟨rfl, rfl, ?_⟩
        rw [h2, h3]; dsimp only [Option.getD_some]
        rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hxs.2.2.2.1
        · exact hxs.2.2.2.2
    have hseq4 : GateSeqOk F_cur cur_vars scr4 (g_len.toNat + 4) 0 := by
      refine gateSeqOk_append (by omega) hpref ?_ hseq0
      refine .step hg_at ?_
      have h1 : scr4[g_len.toNat + 1]? = some ((1#32 <<< 28) ||| 2#32) := by
        simp only [scr4, scr3, scr2, scr1]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_self (by simp; omega)]
      simpa [h1] using GateSeqOk.done
    exact hQ scr4 m hlen4 hpref hseq4 hm4
  fc_steps
  · exact hfinish r0 r1 m (Or.inl ⟨rfl, rfl⟩) (by rw [hg1, hg2, hg3] at hm; exact hm)
  · exact hfinish r1 r0 m (Or.inr ⟨rfl, rfl⟩) (by rw [hg1, hg2, hg3] at hm; exact hm)

/-- **#7 (`full_cong_try_xor_ite`)**: tests a ternary clause `[a, b, cl]` for full 4-clause XOR
definitions (emitting 3 XOR gates) or 2-clause ITE halves (`full_cong_extract_ite`). -/
theorem full_cong_try_xor_ite_wp (Γ : Env)
    (hHasTern : ∀ args m Q X, fullHasTernarySpec args m Q X →
      Γ "full_has_ternary" [i64, i32, i32, i32] [.bool] args m Q X)
    (hEmitXor : ∀ args m Q X, fullCongEmitXorSpec args m Q X →
      Γ "full_cong_emit_xor" [i64, i64, i32, i32, i32] [i64] args m Q X)
    (hExtIte : ∀ args m Q X, fullCongExtractIteSpec args m Q X →
      Γ "full_cong_extract_ite" [i64, i32, i32, i32, i64] [i64] args m Q X) :
    ∀ args m Q X, fullCongTryXorIteSpec args m Q X →
      Func.wp Γ full_cong_try_xor_ite_body args m Q X := by
  rintro ⟨h, a, b, cl, g_len, g_cap, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hcl0, ha_lt, hb_lt, hc_lt,
     hab_v, hac_v, hbc_v, hcl0_ent, hg_le, hgc_le, hseq0, hm0, hQ⟩
  have hsc := c.hscr; unfold dimacsBound at hsc
  have hscrl := hlen.scratch_ok.scratch_buf_len
  have hcv3 : 3 ≤ s.core.cur_vars :=
    cur_vars_ge3_of_distinct (by omega) (by omega) (by omega) hab_v hac_v hbc_v
  have hna_lt : (a ^^^ 1).toNat < 2 * s.core.cur_vars := by
    rw [bv32_xor1_litNeg]; exact bv32_xor1_lt_even ha_lt
  have hnb_lt : (b ^^^ 1).toNat < 2 * s.core.cur_vars := by
    rw [bv32_xor1_litNeg]; exact bv32_xor1_lt_even hb_lt
  have hnc_lt : (cl ^^^ 1).toNat < 2 * s.core.cur_vars := by
    rw [bv32_xor1_litNeg]; exact bv32_xor1_lt_even hc_lt
  have hdis_lit : ∀ x y : BitVec 32, x.toNat / 2 ≠ y.toNat / 2 → x ≠ y :=
    fun _ _ => bv32_ne_of_div2_ne
  have hperm3 : ∀ {u v w u' v' w' : Nat},
      (u = u' ∨ u = v' ∨ u = w') → (v = u' ∨ v = v' ∨ v = w') → (w = u' ∨ w = v' ∨ w = w') →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [u, v, w]) →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [u', v', w']) :=
    fun hu hv hw_p hcl => entails_perm_clause (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> assumption) hcl
  have hcall_ite : ∀ (x y z : BitVec 32) (s_cur : FullState) (m_cur : Mem 64),
      s_cur = { s with scratch := { s.scratch with scratch_buf := s_cur.scratch.scratch_buf } } →
      s_cur.scratch.scratch_buf.length = c.scratch_cap →
      (∀ idx < g_len.toNat, s_cur.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?) →
      GateSeqOk F_cur s.core.cur_vars s_cur.scratch.scratch_buf g_len.toNat 0 →
      x.toNat < 2 * s.core.cur_vars → y.toNat < 2 * s.core.cur_vars →
      z.toNat < 2 * s.core.cur_vars →
      x.toNat / 2 ≠ y.toNat / 2 → x.toNat / 2 ≠ z.toNat / 2 → y.toNat / 2 ≠ z.toNat / 2 →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [x.toNat, y.toNat, z.toNat]) →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [x.toNat, litNeg y.toNat, litNeg z.toNat]) →
      (FullMem c s_cur ⋆ R) m_cur →
      fullCongExtractIteSpec (c.hdr, x ^^^ 1, y ^^^ 1, z, g_len, ()) m_cur
        (fun (ret, ()) m' => Q (ret, ()) m') X := by
    intro x y z s_cur m_cur hseq hlen_c hpref_c hgate_c hx hy hz hxy hxz hyz he1 he2 hm_c
    have hcore_eq : s_cur.core = s.core := by rw [hseq]
    refine ⟨c, F0, F_cur, s_cur, R, rfl,
      ⟨hcore_eq ▸ hlen.core_ok,
       by rw [hseq]; exact { hlen.scratch_ok with scratch_buf_len := hlen_c }⟩,
      hcore_eq ▸ hw, fullArenaVarsNodup_of_eq hnd (by rw [hcore_eq]) (by rw [hcore_eq]),
      hcore_eq ▸ hcl0,
      by rw [hcore_eq, bv32_xor1_litNeg]; exact bv32_xor1_lt_even hx,
      by rw [hcore_eq, bv32_xor1_litNeg]; exact bv32_xor1_lt_even hy,
      hcore_eq ▸ hz,
      div2_ne_of_xor1_both hxy, div2_ne_of_xor1_l hxz, div2_ne_of_xor1_l hyz,
      by simp only [bv32_xor1_litNeg, litNeg_litNeg]
         exact hperm3 (Or.inr (Or.inl rfl)) (Or.inl rfl) (Or.inr (Or.inr rfl)) he2,
      by simp only [bv32_xor1_litNeg, litNeg_litNeg]
         exact hperm3 (Or.inr (Or.inl rfl)) (Or.inl rfl) (Or.inr (Or.inr rfl)) he1,
      by omega, hcore_eq ▸ hgate_c, hm_c,
      fun ret scr' m' hlen' hret hpref' hgate' hm' => ?_⟩
    have hbounds : g_len.toNat ≤ ret.toNat ∧ ret.toNat ≤ g_cap.toNat := by
      rcases hret with rfl | rfl
      · exact ⟨Nat.le_refl _, by omega⟩
      · have : (g_len + 5#64).toNat = g_len.toNat + 5 := by bv_omega
        omega
    have hm'' : (FullMem c { s with scratch :=
        { s.scratch with scratch_buf := scr' } } ⋆ R) m' := by
      have : { s_cur with scratch := { s_cur.scratch with scratch_buf := scr' } } =
          { s with scratch := { s.scratch with scratch_buf := scr' } } := by
        conv => lhs; rw [hseq]
      rwa [this] at hm'
    exact hQ ret scr' m' hlen' hbounds.1 hbounds.2
      (fun idx hi => (hpref' idx hi).trans (hpref_c idx hi)) (hcore_eq ▸ hgate') hm''
  have hite_first : ∀ (x y z : BitVec 32),
      x.toNat < 2 * s.core.cur_vars → y.toNat < 2 * s.core.cur_vars →
      z.toNat < 2 * s.core.cur_vars →
      x.toNat / 2 ≠ y.toNat / 2 → x.toNat / 2 ≠ z.toNat / 2 → y.toNat / 2 ≠ z.toNat / 2 →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [x.toNat, y.toNat, z.toNat]) →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [x.toNat, litNeg y.toNat, litNeg z.toNat]) →
      ∀ (P : Post [i64]),
      (∀ (ng : BitVec 64) (scr1 : List (BitVec 32)) (m1 : Mem 64),
        scr1.length = c.scratch_cap → (ng = g_len ∨ ng = g_len + 5#64) →
        (∀ idx < g_len.toNat, scr1[idx]? = s.scratch.scratch_buf[idx]?) →
        GateSeqOk F_cur s.core.cur_vars scr1 ng.toNat 0 →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr1 } } ⋆ R) m1 →
        P (ng, ()) m1) →
      fullCongExtractIteSpec (c.hdr, x ^^^ 1, y ^^^ 1, z, g_len, ()) m0 P X := by
    intro x y z hx hy hz hxy hxz hyz he1 he2 P hP
    exact ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hcl0,
      by rw [bv32_xor1_litNeg]; exact bv32_xor1_lt_even hx,
      by rw [bv32_xor1_litNeg]; exact bv32_xor1_lt_even hy, hz,
      div2_ne_of_xor1_both hxy, div2_ne_of_xor1_l hxz, div2_ne_of_xor1_l hyz,
      by simp only [bv32_xor1_litNeg, litNeg_litNeg]
         exact hperm3 (Or.inr (Or.inl rfl)) (Or.inl rfl) (Or.inr (Or.inr rfl)) he2,
      by simp only [bv32_xor1_litNeg, litNeg_litNeg]
         exact hperm3 (Or.inr (Or.inl rfl)) (Or.inl rfl) (Or.inr (Or.inr rfl)) he1,
      by omega, hseq0, hm0, hP⟩
  fc_to_group
  refine wp_join_group (ts := []) (fun () mj => mj = m0) ?_ ?_
  · -- Shared ITE fallback join point (3 permutations of (a, b, cl))
    rintro _ ⟨⟩ mj hmj; subst mj
    c0_call hHasTern
    refine ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hcl0, ha_lt, hm0, fun ok_i1 hok_i1 => ?_⟩
    fc_split
    · have hti1 : (cnfOfClauses F_cur).EntailsClause
          (cnfClause [a.toNat, litNeg b.toNat, litNeg cl.toNat]) := by
        simpa only [bv32_xor1_litNeg] using hok_i1 (by grind)
          (hdis_lit _ _ (div2_ne_of_xor1 hab_v)) (hdis_lit _ _ (div2_ne_of_xor1 hac_v))
          (hdis_lit _ _ (div2_ne_of_xor1_both hbc_v))
      fc_steps
      c0_call hExtIte
      refine hite_first a b cl ha_lt hb_lt hc_lt hab_v hac_v hbc_v hcl0_ent hti1 _
        fun ng scr1 m1 hlen1 hng hpref1 hseq1 hm1 => ?_
      fc_split
      · have hng_le : g_len.toNat ≤ ng.toNat ∧ ng.toNat ≤ g_cap.toNat := by
          rcases hng with rfl | rfl
          · exact ⟨Nat.le_refl _, by omega⟩
          · have : (g_len + 5#64).toNat = g_len.toNat + 5 := by bv_omega
            omega
        fc_steps; exact hQ ng scr1 m1 hlen1 hng_le.1 hng_le.2 hpref1 hseq1 hm1
      · have hng_eq : ng = g_len := by
          rcases hng with rfl | rfl
          · rfl
          · exfalso
            have : (g_len + 5#64).toNat = g_len.toNat + 5 := by bv_omega
            c0_bound
        subst hng_eq; fc_steps; c0_call hExtIte
        exact hcall_ite a cl b { s with scratch := { s.scratch with scratch_buf := scr1 } } m1
          rfl hlen1 hpref1 hseq1 ha_lt hc_lt hb_lt hac_v hab_v (Ne.symm hbc_v)
          (hperm3 (Or.inl rfl) (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) hcl0_ent)
          (hperm3 (Or.inl rfl) (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) hti1) hm1
    · fc_steps
      c0_call hHasTern
      refine ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hcl0, hb_lt, hm0, fun ok_i2 hok_i2 => ?_⟩
      fc_split
      · have hti2 : (cnfOfClauses F_cur).EntailsClause
            (cnfClause [b.toNat, litNeg a.toNat, litNeg cl.toNat]) := by
          simpa only [bv32_xor1_litNeg] using hok_i2 (by grind)
            (hdis_lit _ _ (div2_ne_of_xor1 (Ne.symm hab_v))) (hdis_lit _ _ (div2_ne_of_xor1 hbc_v))
            (hdis_lit _ _ (div2_ne_of_xor1_both hac_v))
        fc_steps
        c0_call hExtIte
        refine hite_first b a cl hb_lt ha_lt hc_lt (Ne.symm hab_v) hbc_v hac_v
          (hperm3 (Or.inr (Or.inl rfl)) (Or.inl rfl) (Or.inr (Or.inr rfl)) hcl0_ent) hti2 _
          fun ng scr1 m1 hlen1 hng hpref1 hseq1 hm1 => ?_
        fc_split
        · have hng_le : g_len.toNat ≤ ng.toNat ∧ ng.toNat ≤ g_cap.toNat := by
            rcases hng with rfl | rfl
            · exact ⟨Nat.le_refl _, by omega⟩
            · have : (g_len + 5#64).toNat = g_len.toNat + 5 := by bv_omega
              omega
          fc_steps; exact hQ ng scr1 m1 hlen1 hng_le.1 hng_le.2 hpref1 hseq1 hm1
        · have hng_eq : ng = g_len := by
            rcases hng with rfl | rfl
            · rfl
            · exfalso
              have : (g_len + 5#64).toNat = g_len.toNat + 5 := by bv_omega
              c0_bound
          subst hng_eq; fc_steps; c0_call hExtIte
          exact hcall_ite b cl a { s with scratch := { s.scratch with scratch_buf := scr1 } } m1
            rfl hlen1 hpref1 hseq1 hb_lt hc_lt ha_lt hbc_v (Ne.symm hab_v) (Ne.symm hac_v)
            (hperm3 (Or.inr (Or.inr rfl)) (Or.inl rfl) (Or.inr (Or.inl rfl)) hcl0_ent)
            (hperm3 (Or.inl rfl) (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) hti2) hm1
      · fc_steps
        c0_call hHasTern
        refine ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hcl0, hc_lt, hm0, fun ok_i3 hok_i3 => ?_⟩
        fc_split
        · have hti3 : (cnfOfClauses F_cur).EntailsClause
              (cnfClause [cl.toNat, litNeg a.toNat, litNeg b.toNat]) := by
            simpa only [bv32_xor1_litNeg] using hok_i3 (by grind)
              (hdis_lit _ _ (div2_ne_of_xor1 (Ne.symm hac_v)))
              (hdis_lit _ _ (div2_ne_of_xor1 (Ne.symm hbc_v)))
              (hdis_lit _ _ (div2_ne_of_xor1_both hab_v))
          fc_steps
          c0_call hExtIte
          refine hite_first cl a b hc_lt ha_lt hb_lt (Ne.symm hac_v) (Ne.symm hbc_v) hab_v
            (hperm3 (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) (Or.inl rfl) hcl0_ent) hti3 _
            fun ng scr1 m1 hlen1 hng hpref1 hseq1 hm1 => ?_
          fc_split
          · have hng_le : g_len.toNat ≤ ng.toNat ∧ ng.toNat ≤ g_cap.toNat := by
              rcases hng with rfl | rfl
              · exact ⟨Nat.le_refl _, by omega⟩
              · have : (g_len + 5#64).toNat = g_len.toNat + 5 := by bv_omega
                omega
            fc_steps; exact hQ ng scr1 m1 hlen1 hng_le.1 hng_le.2 hpref1 hseq1 hm1
          · have hng_eq : ng = g_len := by
              rcases hng with rfl | rfl
              · rfl
              · exfalso
                have : (g_len + 5#64).toNat = g_len.toNat + 5 := by bv_omega
                c0_bound
            subst hng_eq; fc_steps; c0_call hExtIte
            exact hcall_ite cl b a { s with scratch := { s.scratch with scratch_buf := scr1 } } m1
              rfl hlen1 hpref1 hseq1 hc_lt hb_lt ha_lt (Ne.symm hbc_v) (Ne.symm hac_v)
              (Ne.symm hab_v)
              (hperm3 (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) (Or.inl rfl) hcl0_ent)
              (hperm3 (Or.inl rfl) (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) hti3) hm1
        · fc_steps
          exact hQ g_len s.scratch.scratch_buf m0 hscrl (Nat.le_refl _) (by omega)
            (fun _ _ => rfl) hseq0 hm0
  · -- Entry: 3-way && XOR check; false branches jump to ITE join J
    intro J hJ
    fc_steps
    c0_call hHasTern
    refine ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hcl0, ha_lt, hm0, fun ok1 hok1 => ?_⟩
    fc_split
    · have ht1 : (cnfOfClauses F_cur).EntailsClause
          (cnfClause [a.toNat, litNeg b.toNat, litNeg cl.toNat]) := by
        simpa only [bv32_xor1_litNeg] using hok1 (by grind)
          (hdis_lit _ _ (div2_ne_of_xor1 hab_v)) (hdis_lit _ _ (div2_ne_of_xor1 hac_v))
          (hdis_lit _ _ (div2_ne_of_xor1_both hbc_v))
      fc_steps
      c0_call hHasTern
      refine ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hcl0, hna_lt, hm0, fun ok2 hok2 => ?_⟩
      fc_split
      · have ht2 : (cnfOfClauses F_cur).EntailsClause
            (cnfClause [litNeg a.toNat, b.toNat, litNeg cl.toNat]) := by
          simpa only [bv32_xor1_litNeg] using hok2 (by grind)
            (hdis_lit _ _ (div2_ne_of_xor1_l hab_v))
            (hdis_lit _ _ (div2_ne_of_xor1_both hac_v))
            (hdis_lit _ _ (div2_ne_of_xor1 hbc_v))
        fc_steps
        c0_call hHasTern
        refine ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hcl0, hna_lt, hm0, fun ok3 hok3 => ?_⟩
        fc_split
        · have ht3 : (cnfOfClauses F_cur).EntailsClause
              (cnfClause [litNeg a.toNat, litNeg b.toNat, cl.toNat]) := by
            simpa only [bv32_xor1_litNeg] using hok3 (by grind)
              (hdis_lit _ _ (div2_ne_of_xor1_both hab_v))
              (hdis_lit _ _ (div2_ne_of_xor1_l hac_v))
              (hdis_lit _ _ (div2_ne_of_xor1_l hbc_v))
          obtain ⟨hx1, hx2, hx3⟩ := xorGateDef_of_four hcl0_ent ht1 ht2 ht3
          fc_split
          · have h12 : g_len.toNat + 12 ≤ g_cap.toNat := by bv_omega
            have hg4 : (g_len + 4#64).toNat = g_len.toNat + 4 := by bv_omega
            have hg8 : (g_len + 4#64 + 4#64).toNat = g_len.toNat + 8 := by bv_omega
            have hg12 : (g_len + 4#64 + 4#64 + 4#64).toNat = g_len.toNat + 12 := by bv_omega
            fc_steps
            c0_call hEmitXor
            refine ⟨F_cur, s.core.cur_vars, s.scratch.scratch_buf, FullScrBufRest c s ⋆ R,
              ha_lt, hb_lt, hc_lt, by omega, by omega, by omega, hx1, hseq0,
              focus_full_scratch_buf hm0, fun scr1 m1 hlen1 hpref1 hseq1 hm1 => ?_⟩
            fc_steps
            c0_call hEmitXor
            refine ⟨F_cur, s.core.cur_vars, scr1, FullScrBufRest c s ⋆ R,
              hb_lt, ha_lt, hc_lt, by omega, by omega, by omega, hx2, hg4 ▸ hseq1, hm1,
              fun scr2 m2 hlen2 hpref2 hseq2 hm2 => ?_⟩
            fc_steps
            c0_call hEmitXor
            refine ⟨F_cur, s.core.cur_vars, scr2, FullScrBufRest c s ⋆ R,
              hc_lt, ha_lt, hb_lt, by omega, by omega, by omega, hx3,
              by rw [hg8]; simpa [hg4, Nat.add_assoc] using hseq2, hm2,
              fun scr3 m3 hlen3 hpref3 hseq3 hm3 => ?_⟩
            fc_steps
            exact hQ (g_len + 4#64 + 4#64 + 4#64) scr3 m3 (by omega) (by omega) (by omega)
              (fun idx hi =>
                (hpref3 idx (by omega)).trans ((hpref2 idx (by omega)).trans (hpref1 idx hi)))
              (by rw [hg12]; simpa [hg8, Nat.add_assoc] using hseq3) (unfocus_full_scratch_buf hm3)
          · fc_steps
            exact hQ g_len s.scratch.scratch_buf m0 hscrl (Nat.le_refl _) (by omega)
              (fun _ _ => rfl) hseq0 hm0
        · fc_steps; exact hJ () m0 rfl
      · fc_steps; exact hJ () m0 rfl
    · fc_steps; exact hJ () m0 rfl

namespace FullCongHelpers

/-- Emitting an AND gate from an arena clause with verified binary clauses gives `GateAt`. -/
theorem andGate_of_emitted {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hnd : FullArenaVarsNodup s) {p i sz g_len : Nat}
    (hp : p ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s p = false)
    (hsz_eq : fullArenaClauseSizeCore s.core p = sz) (hsz3 : 3 ≤ sz) (hsz8 : sz ≤ 8) (hi : i < sz)
    (hbins : ∀ k < sz, k ≠ i →
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause [litNeg (s.core.arena[p + 3 + i]?.getD 0#32).toNat,
                    litNeg (s.core.arena[p + 3 + k]?.getD 0#32).toNat]))
    {scr : List (BitVec 32)} (hscrl : scr.length = c.scratch_cap)
    (hbd_g : g_len + 2 + (sz - 1) ≤ c.scratch_cap)
    (h0 : scr[g_len]? = some (s.core.arena[p + 3 + i]?.getD 0#32))
    (h1 : scr[g_len + 1]? = some (BitVec.ofNat 32 (sz - 1)))
    (hrhs : ∀ k < sz, k ≠ i →
      scr[g_len + 2 + (if k < i then k else k - 1)]? =
        some ((s.core.arena[p + 3 + k]?.getD 0#32) ^^^ 1#32)) :
    GateAt F_cur s.core.cur_vars scr (g_len + 2 + (sz - 1)) g_len := by
  have hwf := hw.arena.refs_wf p hp
  have har_bd : p + 3 + sz ≤ s.core.arena.length := by
    have := hlen.core_ok.arena_len_le; have := hlen.core_ok.arena_len_arr; omega
  have hsz_cv : sz ≤ s.core.cur_vars :=
    hsz_eq ▸ fullArenaClauseSize_le_cur_vars hlen hw hnd hp hng
  have hlit_lt : ∀ k < sz, (s.core.arena[p + 3 + k]?.getD 0#32).toNat < 2 * s.core.cur_vars :=
    fun k hk => hw.arena.lits_lt p hp hng _ <| (mem_fullArenaClauseLitsCore_iff (by omega)).mpr
      ⟨k, by omega, by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]⟩
  have hmword_tag : ((BitVec.ofNat 32 (sz - 1) >>> 28)).toNat = 0 := by
    rw [BitVec.toNat_ushiftRight, bv32_ofNat_toNat (by omega), Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt (by omega)
  have hmword_ar : ((BitVec.ofNat 32 (sz - 1) &&& 0xFF#32)).toNat = sz - 1 := by
    rw [BitVec.toNat_and, bv32_ofNat_toNat (by omega),
      show (0xFF#32 : BitVec 32).toNat = 255 from rfl]
    simpa [Nat.mod_eq_of_lt (show sz - 1 < 256 by omega)] using
      Nat.and_two_pow_sub_one_eq_mod (sz - 1) 8
  have hrhs_at : ∀ r < sz - 1,
      ∃ v : BitVec 32, scr[g_len + 2 + r]? = some v ∧ v.toNat < 2 * s.core.cur_vars ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause [litNeg (s.core.arena[p + 3 + i]?.getD 0#32).toNat, v.toNat]) := by
    intro r hr
    let k := if r < i then r else r + 1
    have hk_lt : k < sz := by dsimp only [k]; split <;> omega
    have hk_ne : k ≠ i := by dsimp only [k]; split <;> omega
    have hk_eq : (if k < i then k else k - 1) = r := by
      dsimp only [k]; split <;> (try split) <;> omega
    have hget := hrhs k hk_lt hk_ne; rw [hk_eq] at hget
    exact ⟨_, hget, by rw [bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even (hlit_lt k hk_lt),
      by rw [bv32_xor1_eq_litNeg]; exact hbins k hk_lt hk_ne⟩
  refine ⟨s.core.arena[p + 3 + i]?.getD 0#32, BitVec.ofNat 32 (sz - 1), h0, h1, hlit_lt i hi,
    by omega, by omega, by omega,
    fun r hr => let ⟨v, hv, hlt, _⟩ := hrhs_at r (by omega); ⟨v, hv, hlt⟩, Or.inl ⟨hmword_tag,
    by omega, ?_, ?_⟩⟩
  · refine entails_perm_clause (fun x hx => ?_) (hw.arena.entails p hp hng)
    obtain ⟨k, hk, hget⟩ := (mem_fullArenaClauseLitsCore_iff (by omega)).mp hx
    rw [hsz_eq] at hk; rw [List.mem_cons]
    by_cases hki : k = i
    · subst hki; left; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hget.symm
    · right; rw [List.mem_map]
      let r := if k < i then k else k - 1
      have hr_lt : r < sz - 1 := by dsimp only [r]; split <;> omega
      have hscr_r := hrhs k hk hki; have hr_scr : g_len + 2 + r < scr.length := by omega
      have hval_r : scr[g_len + 2 + r]'hr_scr = (s.core.arena[p + 3 + k]?.getD 0#32) ^^^ 1#32 := by
        rw [List.getElem?_eq_getElem hr_scr] at hscr_r; exact Option.some.inj hscr_r
      refine ⟨(scr[g_len + 2 + r]'hr_scr).toNat, List.mem_map.mpr ⟨_, ?_, rfl⟩, ?_⟩
      · have hlt_t : r < ((scr.drop (g_len + 2)).take
            ((BitVec.ofNat 32 (sz - 1) &&& 0xFF#32).toNat)).length := by
          rw [List.length_take, List.length_drop, hmword_ar]; omega
        simpa [List.getElem_take, List.getElem_drop] using List.getElem_mem hlt_t
      · rw [hval_r, bv32_xor1_eq_litNeg, litNeg_litNeg,
          List.getElem?_eq_getElem (by omega), Option.getD_some, hget]
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx; obtain ⟨r, hr, hget⟩ := List.mem_iff_getElem.mp hv
    rw [List.length_take, List.length_drop, hmword_ar] at hr; rw [List.getElem_take,
      List.getElem_drop] at hget
    obtain ⟨v', hv', _, hent⟩ := hrhs_at r (by omega)
    rw [List.getElem?_eq_getElem (by omega)] at hv'
    rwa [(Option.some.inj hv').symm.trans hget] at hent

end FullCongHelpers

end LeanQbe.T.Examples.Kissat.Full
