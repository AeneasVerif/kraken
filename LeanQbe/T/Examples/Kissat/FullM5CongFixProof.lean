module

public import LeanQbe.T.Examples.Kissat.FullM5CongFixProof1
public import LeanQbe.T.Examples.Kissat.FullDefSweepLemmas

/-!
# Kissat `D-Full` M5 Congruence Closure Fix Proofs — Part 2 (`work_step`, `ModuleOk`, UNSAT NV)

Builds on `FullM5CongFixProof1` to prove:
7. `full_cong_work_step` (`m5_cong_work_step_wp` against `m5CongWorkStepSpec`):
   - `cur == (lhs ^ 1u)` clash detection in AND dedup (`andFold_neg_lhs_entails`)
   - `need_hash = false` when `vals[lhs] > 0` in AND
   - `vals[lhs] != 0` folding (`xor_lhs_const_equiv`) & RHS sign-stripping (`xor_sign_strip_sound`)
     in XOR
   - `then_lit` sign normalization (`iteGateDef_flip_out`) in ITE
   - self-match skip `ent == (u32)g` (`seen_self`) and matching `match_lhs` sign normalization in
     HT lookup.
8. Closed `15`-row `m5CongFixSpecTable`, `m5CongFixEnv`, and `m5CongFix_moduleOk`.
9. Direct composition `m5_congruence_dense_fix_wp` proving `FullM5CongBins.full_congruence_dense`
   with `FullM5CongFix`'s `full_cong_extract` + `full_cong_work_step` satisfies exact canonical
   `FullM3CongBva.m3CongruenceDenseSpec` and `FullDefSweep.fullCongruenceDenseSpec`.
10. Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`, zero SAT/model proofs).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM5CongFix

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open LeanQbe.T.Examples.Kissat.FullM3CongBva hiding
  full_cong_and_match full_cong_and_match_body full_cong_and_match_wf
  full_cong_work_step full_cong_work_step_body full_cong_work_step_wf
open LeanQbe.T.Examples.Kissat.FullM5CongBins
open Kraken.Bedrock2.Test

/-! ## 1. Local `tmp` Framing & After-Fold Tactic for `WorkStepOk32` -/

section WorkStepProof

open scoped FullArenaTactics FullCongTactics M3HeadTactics

private theorem c0_load_full_tmp0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) (h0 : 0 < s.core.tmp.length) :
    loadVal m i32 (c.pTmp + 0#64) = some (s.core.tmp[0]'h0) := by
  simpa using FullArenaTactics.c0_load_full_tmp (i := 0#64) (by simpa using h0) hm

private theorem c0_load_full_tmp1 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) (h1 : 1 < s.core.tmp.length) :
    loadVal m i32 (c.pTmp + 4#64) = some (s.core.tmp[1]'h1) := by
  simpa using FullArenaTactics.c0_load_full_tmp (i := 1#64) (by simpa using h1) hm

private theorem c0_load_full_tmp2 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (FullMem c s ⋆ R) m) (h2 : 2 < s.core.tmp.length) :
    loadVal m i32 (c.pTmp + 8#64) = some (s.core.tmp[2]'h2) := by
  simpa using FullArenaTactics.c0_load_full_tmp (i := 2#64) (by simpa using h2) hm

private theorem c0_store_full_tmp0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (v : BitVec 32) (h0 : 0 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 0#64) ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 0 v } } ⋆ R)
        (storeMem m i32 (c.pTmp + 0#64) v) := by
  simpa using FullArenaTactics.c0_store_full_tmp (i := 0#64) v (by simpa using h0) hm

private theorem c0_store_full_tmp1 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (v : BitVec 32) (h1 : 1 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 4#64) ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 1 v } } ⋆ R)
        (storeMem m i32 (c.pTmp + 4#64) v) := by
  simpa using FullArenaTactics.c0_store_full_tmp (i := 1#64) v (by simpa using h1) hm

private theorem c0_store_full_tmp2 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    (v : BitVec 32) (h2 : 2 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 8#64) ∧
      (FullMem c { s with core := { s.core with tmp := s.core.tmp.set 2 v } } ⋆ R)
        (storeMem m i32 (c.pTmp + 8#64) v) := by
  simpa using FullArenaTactics.c0_store_full_tmp (i := 2#64) v (by simpa using h2) hm

attribute [local c0_load] c0_load_full_tmp0 c0_load_full_tmp1 c0_load_full_tmp2
attribute [local c0_store] c0_store_full_tmp0 c0_store_full_tmp1 c0_store_full_tmp2

private theorem c0_store_array32_set_0 {p : BitVec 64} {xs : List (BitVec 32)}
    {k0 : Nat} {v0 v1 : BitVec 32} {R : Mem 64 → Prop} {m : Mem 64} (h1 : 1 < xs.length)
    (hm : (array (t := i32) p (xs.set k0 v0) ⋆ R) m) :
    storeOk m i32 (p + 4#64) ∧
      (array (t := i32) p ((xs.set k0 v0).set 1 v1) ⋆ R) (storeMem m i32 (p + 4#64) v1) := by
  simpa [Ty.bytes, Ty.size, i32] using
    store_array (t := i32) (i := 1) v1 (by decide) (by simpa using h1) hm

private theorem c0_store_array32_set_0_mul {p : BitVec 64}
    {xs : List (BitVec 32)} {k0 : Nat} {v0 v1 : BitVec 32} {R : Mem 64 → Prop} {m : Mem 64}
    (h1 : 1 < xs.length) (hm : (array (t := i32) p (xs.set k0 v0) ⋆ R) m) :
    storeOk m i32 (p + 1#64 * 4) ∧
      (array (t := i32) p ((xs.set k0 v0).set 1 v1) ⋆ R)
        (storeMem m i32 (p + 1#64 * 4) v1) := by
  simpa [Ty.bytes, Ty.size, i32, show (1#64 : BitVec 64) * 4 = 4#64 from rfl] using
    c0_store_array32_set_0 (p := p) (xs := xs) (k0 := k0) (v0 := v0) (v1 := v1) h1 hm

private theorem c0_store_array32_set_01 {p : BitVec 64}
    {xs : List (BitVec 32)} {k0 k1 : Nat} {v0 v1 v2 : BitVec 32}
    {R : Mem 64 → Prop} {m : Mem 64} (h2 : 2 < xs.length)
    (hm : (array (t := i32) p ((xs.set k0 v0).set k1 v1) ⋆ R) m) :
    storeOk m i32 (p + 8#64) ∧
      (array (t := i32) p (((xs.set k0 v0).set k1 v1).set 2 v2) ⋆ R)
        (storeMem m i32 (p + 8#64) v2) := by
  simpa [Ty.bytes, Ty.size, i32] using
    store_array (t := i32) (i := 2) v2 (by decide) (by simpa using h2) hm

private theorem c0_store_array32_set_01_mul {p : BitVec 64}
    {xs : List (BitVec 32)} {k0 k1 : Nat} {v0 v1 v2 : BitVec 32}
    {R : Mem 64 → Prop} {m : Mem 64} (h2 : 2 < xs.length)
    (hm : (array (t := i32) p ((xs.set k0 v0).set k1 v1) ⋆ R) m) :
    storeOk m i32 (p + 2#64 * 4) ∧
      (array (t := i32) p (((xs.set k0 v0).set k1 v1).set 2 v2) ⋆ R)
        (storeMem m i32 (p + 2#64 * 4) v2) := by
  simpa [Ty.bytes, Ty.size, i32, show (2#64 : BitVec 64) * 4 = 8#64 from rfl] using
    c0_store_array32_set_01 (p := p) (xs := xs) (k0 := k0) (k1 := k1) (v0 := v0) (v1 := v1)
      (v2 := v2) h2 hm

attribute [local c0_store] c0_store_array32_set_0 c0_store_array32_set_0_mul
  c0_store_array32_set_01 c0_store_array32_set_01_mul

private theorem ws_tag0_il_push_inv' {hf : Bool} {vals : List (BitVec 8)}
    {tmpl raw : List (BitVec 32)} {il_n na_n ar_n maxv : Nat} (htl : tmpl.length = maxv)
    (hna : na_n ≤ il_n) (hil : il_n < ar_n) (har_le : ar_n ≤ maxv)
    (hraw_len : raw.length = ar_n) (htail : ∀ j, il_n ≤ j → j < ar_n → tmpl[j]? = raw[j]?)
    (hsub : ∀ j < na_n, ∃ k < ar_n, tmpl[j]? = raw[k]?)
    (hnohf : hf = false → ∀ k < il_n,
      vals[(raw[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8 ∨
        ∃ j < na_n, tmpl[j]? = raw[k]?) :
    let tmpl' := tmpl.set na_n (raw[il_n]'(by omega))
    tmpl'.length = maxv ∧ na_n + 1 ≤ il_n + 1 ∧ il_n + 1 ≤ ar_n ∧
    (∀ j, il_n + 1 ≤ j → j < ar_n → tmpl'[j]? = raw[j]?) ∧
    (∀ j < na_n + 1, ∃ k < ar_n, tmpl'[j]? = raw[k]?) ∧
    (hf = false → ∀ k < il_n + 1,
      vals[(raw[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8 ∨
        ∃ j < na_n + 1, tmpl'[j]? = raw[k]?) := by
  refine ⟨by rw [List.length_set]; exact htl, by omega, by omega, ?_, ?_, ?_⟩
  · intro j hj1 hj2; rw [List.getElem?_set_ne (by omega)]; exact htail j (by omega) hj2
  · intro j hj; by_cases hjn : j = na_n
    · subst hjn; refine ⟨il_n, hil, ?_⟩
      rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem (by omega)]
    · rw [List.getElem?_set_ne (Ne.symm hjn)]; exact hsub j (by omega)
  · intro hhf k hk; by_cases hki : k = il_n
    · subst hki; right; refine ⟨na_n, by omega, ?_⟩
      rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem (by omega)]
    · obtain h1 | ⟨j, hj, hget⟩ := hnohf hhf k (by omega)
      · exact Or.inl h1
      · right; refine ⟨j, by omega, ?_⟩
        rw [List.getElem?_set_ne (by omega)]; exact hget

local elab "m5_after_fold " hq:ident hres:ident ch0:ident wk:ident hc_ok:ident
    mm:ident hmem:ident chVar:ident " => " k:tacticSeq : tactic => do
  let hcId := Lean.mkIdent `hc
  Lean.Elab.Tactic.evalTactic <| ← `(tactic| (
    m3_split_fast
    · m3_let; exact ws32_ret2_q $hq rfl rfl rfl rfl $hc_ok ($hres (beq_iff_eq.mp $hcId))
        $hmem ($wk + 4#64)
    · m3_to_group; refine wp_join_group (ts := [.bool]) (fun _ m_af => m_af = $mm)
        (fun _ ⟨$chVar, ⟨⟩⟩ m_af hm_af => by rw [hm_af]; m3_let; ($k:tacticSeq)) ?_
      intro Jef hJef; m3_split_fast
      · m3_let; exact hJef (true, ()) $mm rfl
      · m3_let; exact hJef ($ch0, ()) $mm rfl))

private def WsPost (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (fuel0 : BitVec 64) (ar0 : List (BitVec 32)) (alen0 cv0 g_len ht_off ht_sz : Nat)
    (scr0 : List (BitVec 32)) (R : Mem 64 → Prop)
    (tag lhs' har' : BitVec 32) (nh' : Bool) (mj : Mem 64) : Prop :=
  ∃ stj : FullState,
    WorkStepOk32 c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 stj ∧
    (nh' = true → HashGateOk32 F_cur cv0 lhs' stj.core.tmp tag har') ∧
    (FullMem c stj ⋆ R) mj

private theorem wsPost_false {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)} {alen0 cv0 g_len ht_off ht_sz : Nat}
    {scr0 : List (BitVec 32)} {R : Mem 64 → Prop} {tag lhs' har' : BitVec 32}
    {stj : FullState} {mj : Mem 64}
    (hok : WorkStepOk32 c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 stj)
    (hm : (FullMem c stj ⋆ R) mj) :
    WsPost c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 R tag lhs' har' false mj :=
  ⟨stj, hok, (fun h => by cases h), hm⟩

private theorem ws_ite_norm_post {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)} {alen0 cv0 g_len ht_off ht_sz : Nat}
    {scr0 : List (BitVec 32)} {R : Mem 64 → Prop} {st : FullState}
    {repri tmpi : List (BitVec 32)} {tag arity lhs1 c1 t2 e2 : BitVec 32} {m : Mem 64}
    (hok_t : WorkStepOk32 c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 st)
    (hrli : repri.length = 2 * c.max_vars) (htli : tmpi.length = c.max_vars)
    (hrepri : FullCongReprInv F_cur (2 * cv0) repri)
    (ht2 : 2 < tmpi.length) (hlhs1_lt : lhs1.toNat < 2 * cv0) (har_cv : arity.toNat ≤ cv0)
    (htag2 : tag = 2#32) (har3 : arity = 3#32)
    (hite2 : IteGateDef (cnfOfClauses F_cur) lhs1.toNat c1.toNat t2.toNat e2.toNat)
    (hm : (array (t := i32) c.pTmp
        (((tmpi.set (0#64 : BitVec 64).toNat c1).set (1#64 : BitVec 64).toNat t2).set
          (2#64 : BitVec 64).toNat e2) ⋆
      (FullTmpRest c (wsState st repri tmpi) ⋆ R)) m) :
    WsPost c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 R tag lhs1 arity true m := by
  let tmps := ((tmpi.set 0 c1).set 1 t2).set 2 e2
  have htmps_len : tmps.length = c.max_vars := by simp [tmps, htli]
  have hm' : (array (t := i32) c.pTmp tmps ⋆ (FullTmpRest c (wsState st repri tmpi) ⋆ R)) m := by
    simpa only [tmps, show (0#64 : BitVec 64).toNat = 0 from rfl,
      show (1#64 : BitVec 64).toNat = 1 from rfl,
      show (2#64 : BitVec 64).toNat = 2 from rfl] using hm
  have htmps_mem : (FullMem c (wsState st repri tmps) ⋆ R) m := ws_unfocus_tmp hm'
  refine ⟨wsState st repri tmps, workStepOk32_wsState hok_t hrli htmps_len hrepri,
    fun _ => ⟨hlhs1_lt, har_cv,
      fun h => absurd (htag2.symm.trans h) (by decide),
      fun h => absurd (htag2.symm.trans h) (by decide),
      fun _ => ⟨har3, ?_⟩⟩, htmps_mem⟩
  have h0_c : tmps[0]?.getD 0#32 = c1 := by
    dsimp only [tmps]
    rw [List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide),
      List.getElem?_set_self (by omega), Option.getD_some]
  have h1_c : tmps[1]?.getD 0#32 = t2 := by
    dsimp only [tmps]
    rw [List.getElem?_set_ne (by decide), List.getElem?_set_self (by simp; omega), Option.getD_some]
  have h2_c : tmps[2]?.getD 0#32 = e2 := by
    dsimp only [tmps]
    rw [List.getElem?_set_self (by simp; omega), Option.getD_some]
  dsimp only [wsState]; rw [h0_c, h1_c, h2_c]; exact hite2

private theorem ws_xor_strip_post {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)} {alen0 cv0 g_len ht_off ht_sz : Nat}
    {scr0 : List (BitVec 32)} {R : Mem 64 → Prop} {st : FullState}
    {repri tmpi : List (BitVec 32)} {tag arity lhs1 a0 a1 : BitVec 32} {m : Mem 64}
    (hok_t : WorkStepOk32 c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 st)
    (hrli : repri.length = 2 * c.max_vars) (htli : tmpi.length = c.max_vars)
    (hrepri : FullCongReprInv F_cur (2 * cv0) repri)
    (ht1 : 1 < tmpi.length) (hlhs1_lt : lhs1.toNat < 2 * cv0) (har_cv : arity.toNat ≤ cv0)
    (htag1 : tag = 1#32) (har2 : arity = 2#32)
    (hxor_s : XorGateDef (cnfOfClauses F_cur) lhs1.toNat a0.toNat a1.toNat)
    (hm : (array (t := i32) c.pTmp
        ((tmpi.set (0#64 : BitVec 64).toNat a0).set (1#64 : BitVec 64).toNat a1) ⋆
      (FullTmpRest c (wsState st repri tmpi) ⋆ R)) m) :
    WsPost c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 R tag lhs1 arity true m := by
  let tmps := (tmpi.set 0 a0).set 1 a1
  have htmps_len : tmps.length = c.max_vars := by simp [tmps, htli]
  have hm' : (array (t := i32) c.pTmp tmps ⋆ (FullTmpRest c (wsState st repri tmpi) ⋆ R)) m := by
    simpa only [tmps, show (0#64 : BitVec 64).toNat = 0 from rfl,
      show (1#64 : BitVec 64).toNat = 1 from rfl] using hm
  have htmps_mem : (FullMem c (wsState st repri tmps) ⋆ R) m := ws_unfocus_tmp hm'
  refine ⟨wsState st repri tmps, workStepOk32_wsState hok_t hrli htmps_len hrepri,
    fun _ => ⟨hlhs1_lt, har_cv,
      fun h => absurd (htag1.symm.trans h) (by decide),
      fun _ => ⟨har2, ?_⟩,
      fun h => absurd (htag1.symm.trans h) (by decide)⟩, htmps_mem⟩
  have h0_c : tmps[0]?.getD 0#32 = a0 := by
    dsimp only [tmps]
    rw [List.getElem?_set_ne (by decide), List.getElem?_set_self (by omega), Option.getD_some]
  have h1_c : tmps[1]?.getD 0#32 = a1 := by
    dsimp only [tmps]
    rw [List.getElem?_set_self (by simp; omega), Option.getD_some]
  dsimp only [wsState]; rw [h0_c, h1_c]; exact hxor_s

private theorem ws_tag0_nlhs_clash_entails {F_cur : List (List Nat)} {rhs : List Nat}
    {tmps raw : List (BitVec 32)} {lhs0 lhs : BitVec 32} {si na ar : Nat}
    (hand0 : AndGateDef (cnfOfClauses F_cur) lhs0.toNat rhs)
    (hlhs_eqv0 : LitEquiv (cnfOfClauses F_cur) lhs0.toNat lhs.toNat)
    (hsi_lt : si < na) (hsi_ts : si < tmps.length) (hraw_len : raw.length = ar)
    (hsub_s : ∀ j < na, ∃ k < ar, tmps[j]? = raw[k]?)
    (hrhs_of_raw : ∀ k < ar, ∃ x ∈ rhs,
      LitEquiv (cnfOfClauses F_cur) x (raw[k]?.getD 0#32).toNat)
    (hcur_nlhs : tmps[si]'hsi_ts = lhs ^^^ 1#32) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg lhs.toNat]) := by
  obtain ⟨k, hk, hgetk⟩ := hsub_s si hsi_lt
  obtain ⟨x, hx, heqvx⟩ := hrhs_of_raw k hk
  have hk_raw : k < raw.length := by rw [hraw_len]; exact hk
  refine andFold_neg_lhs_entails hand0 hlhs_eqv0 ⟨x, hx, ?_⟩
  rw [List.getElem?_eq_getElem hsi_ts, List.getElem?_eq_getElem hk_raw] at hgetk
  rw [List.getElem?_eq_getElem hk_raw, Option.getD_some, ← Option.some.inj hgetk] at heqvx
  change LitEquiv (cnfOfClauses F_cur) x (tmps[si]'hsi_ts).toNat at heqvx
  rwa [hcur_nlhs, bv32_xor1_eq_litNeg] at heqvx

/-- **#7 (`full_cong_work_step`)**: widened (`arity ≤ 31`) epoch-filtered congruence pass with
`cur == lhs ^ 1`, AND `need_hash = false` on `vals[lhs] > 0`, XOR `vals[lhs] != 0` & RHS sign
stripping, ITE `then_lit` sign normalization, and self-match skip `ent == (u32)g`. -/
theorem m5_cong_work_step_wp (Γ : Env)
    (hFind : ∀ a m Q X, fullCongFindSpec a m Q X →
      Γ "full_cong_find" [i64, i32] [i32] a m Q X)
    (hSort : ∀ a m Q X, fullSortU32Spec a m Q X →
      Γ "full_sort_u32" [i64, i32] [] a m Q X)
    (hUnit : ∀ a m Q X, m3CongUnitFoldSpec a m Q X →
      Γ "full_cong_unit_fold" [i64, i32, i32] [i64] a m Q X)
    (hEquiv : ∀ a m Q X, m3CongEquivFoldSpec a m Q X →
      Γ "full_cong_equiv_fold" [i64, i32, i32, i32] [i64] a m Q X)
    (hMatch : ∀ a m Q X, m5CongAndMatchSpec a m Q X →
      Γ "full_cong_and_match" [i64, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, m5CongWorkStepSpec a m Q X →
      Func.wp Γ full_cong_work_step_body a m Q X := by
  rintro ⟨h, g_len, ht_off, ht_sz, cur_ep, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s0, scr0, R, rfl, hlen0, hw0, hmk0, hnd0, hext0, hcl0, hdm0, hrepr0,
     hht_pos, hg_le_ht, hht_le, hseq0, hpref0, hht0, hm0, hQ⟩
  have hsc := c.hscr; have hmx := c.hmaxv; unfold dimacsBound at hsc hmx
  let cv0 := s0.core.cur_vars; let fuel0 := s0.core.fuel
  let ar0 := s0.core.arena; let alen0 := s0.core.arena_len
  m3_steps
  refine wp_loop_inv (ts := [.bool, i64, i64])
    (fun (changed, _work, g, ()) mg => ∃ st : FullState,
      g.toNat ≤ g_len.toNat ∧
      WorkStepOk32 c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat ht_off.toNat ht_sz.toNat scr0 st ∧
      GateSeqOk32 F_cur cv0 scr0 g_len.toNat g.toNat ∧
      (FullMem c st ⋆ R) mg)
    (fun (_changed, _work, g, ()) _ => g_len.toNat - g.toNat)
    (fun Jg hJg => by
      m3_steps; exact hJg (false, 0#64, 0#64, ()) m0
        ⟨s0, Nat.zero_le _,
         ⟨hlen0, hw0, hmk0, hnd0, hext0, hcl0, hdm0, rfl, rfl, rfl, rfl, hrepr0, hpref0, hht0⟩,
         hseq0, hm0⟩)
    (fun Jg (changed, work, g, ()) mg ⟨st, hg_le, hok_t, hseq_t, hmg⟩ ihg => ?_)
  have ⟨hlen_t, hw_t, hmk_t, hnd_t, hext_t, hcl_t, hdm_t, hcv_t, hfl_t, har_t, hal_t,
    hrepr_t, hpref_t, hht_t⟩ := hok_t
  have hscrl_t := hlen_t.scratch_ok.scratch_buf_len
  have hcv_le := hlen_t.core_ok.cur_vars_le
  have hcv0_le : cv0 ≤ c.max_vars := hcv_t ▸ hcv_le
  have htmpl_t := hlen_t.core_ok.tmp_len_arr
  have hrl_t := hlen_t.core_ok.repr_len
  have htmkl_t := hlen_t.scratch_ok.tarjan_mark_len
  have hvlen_t := hlen_t.core_ok.vals_len
  m3_to_group
  refine wp_join0
    (fun m_ex => ∃ ste : FullState,
      WorkStepOk32 c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat ht_off.toNat ht_sz.toNat scr0 ste ∧
      (FullMem c ste ⋆ R) m_ex)
    (fun _ m_ex ⟨ste, hoke, hme⟩ => by
      m3_to_group
      refine wp_join_group (ts := [i64])
        (fun (st_v, ()) m_st =>
          st_v = (if ste.core.inconsistent ≠ 0#64 then 2#64 else if changed then 1#64 else 0#64) ∧
          m_st = m_ex)
        (fun _ ⟨st_v, ⟨⟩⟩ m_st ⟨hst_v, rfl⟩ => by
          m3_steps
          have hgoal := ws32_exit_q hQ rfl rfl rfl rfl hoke hme changed work
          dsimp only at hst_v hgoal; rw [hst_v]
          simpa only [BitVec.reduceSignExtend, BitVec.reduceToNat] using hgoal)
        (fun Jst hJst => by
          m3_split_fast
          · have hne : ste.core.inconsistent ≠ 0#64 := bne_iff_ne.mp hc
            m3_let; exact hJst (2#64, ()) m_ex ⟨by rw [ite_eq_left hne], rfl⟩
          · have heq0 : ¬ ste.core.inconsistent ≠ 0#64 := by simpa using hc
            m3_to_group
            refine wp_join_group (ts := [i64])
              (fun (vc, ()) mc => vc = (if changed then 1#64 else 0#64) ∧ mc = m_ex)
              (fun _ ⟨vc, ⟨⟩⟩ mc ⟨hvc, hmc⟩ => by
                m3_let; exact hJst (vc, ()) mc ⟨by rw [ite_eq_right heq0]; exact hvc, hmc⟩)
              (fun Jch hJch => by
                m3_split_fast
                · m3_let; exact hJch (1#64, ()) m_ex ⟨by rw [ite_eq_left hc], rfl⟩
                · have hnch : ¬ changed = true := by intro h; rw [h] at hc; cases hc
                  m3_let; exact hJch (0#64, ()) m_ex ⟨by rw [ite_eq_right hnch], rfl⟩)))
    ?_
  intro Jex hJex
  m3_split_fast
  · have hg_lt : g.toNat < g_len.toNat := bv64_ult_lt hc
    clear hc
    m3_split_fast
    · clear hc
      obtain ⟨hgat, hseq_next⟩ := gateSeqOk32_inv_lt hseq_t hg_lt
      have ⟨lhs0, mword, hscr0_g, hscr0_g1, hlhs0_lt, hbd_g, har_cv, har_31, hrhs0, hsem0⟩ := hgat
      have hg_arr : g.toNat < st.scratch.scratch_buf.length := by omega
      have hg1_n : (g + 1).toNat = g.toNat + 1 := by bv_omega
      have hg1_arr : (g + 1).toNat < st.scratch.scratch_buf.length := by omega
      have hst_g : st.scratch.scratch_buf[g.toNat]'hg_arr = lhs0 :=
        list_getElem_eq_of_eqD hg_arr ((hpref_t g.toNat hg_lt).trans hscr0_g)
      have hst_g1 : st.scratch.scratch_buf[(g + 1).toNat]'hg1_arr = mword :=
        list_getElem_eq_of_eqD hg1_arr
          (by rw [hg1_n]; exact (hpref_t (g.toNat + 1) (by omega)).trans hscr0_g1)
      let tag := mword >>> 28; let arity := mword &&& 0xFF#32
      have har_cv' : arity.toNat ≤ cv0 := har_cv
      have hbd_g' : g.toNat + 2 + arity.toNat ≤ g_len.toNat := hbd_g
      have hnext_g : (g + 2#64 + arity.setWidth 64).toNat = g.toNat + 2 + arity.toNat :=
        bv64_add_zext32 (k := 2) (by omega)
      have hseq_next' : GateSeqOk32 F_cur cv0 scr0 g_len.toNat
          (g + 2#64 + arity.setWidth 64).toNat := by
        rw [hnext_g]; simpa [hscr0_g1, arity] using hseq_next
      m3_steps; m3_call hFind
      refine ⟨F_cur, 2 * cv0, st.core.repr, FullReprRest c st ⋆ R, hrepr_t,
        by rw [hst_g]; exact hlhs0_lt, focus_full_repr hmg,
        fun lhs repr1 m1 hrl1 hrepr1 _ hlhs_lt hlhs_eqv hm1 => ?_⟩
      have hm1' : (FullMem c (wsState st repr1 st.core.tmp) ⋆ R) m1 := unfocus_full_repr hm1
      clear hm1
      have hlhs_eqv0 : LitEquiv (cnfOfClauses F_cur) lhs0.toNat lhs.toNat := by
        rwa [hst_g] at hlhs_eqv
      have hlhs0_v_lt : ((lhs0 >>> 1).setWidth 64).toNat < st.scratch.tarjan_mark.length := by
        rw [bv_zext32_toNat]; have := bv32_div2_lt_of_lt2 hlhs0_lt; omega
      have hstg_v_lt :
          ((st.scratch.scratch_buf[g.toNat]'hg_arr >>> 1).setWidth 64).toNat <
            st.scratch.tarjan_mark.length := by
        rw [hst_g]; exact hlhs0_v_lt
      have hlhs_v_lt : ((lhs >>> 1).setWidth 64).toNat < st.scratch.tarjan_mark.length := by
        rw [bv_zext32_toNat]; have := bv32_div2_lt_of_lt2 hlhs_lt; omega
      m3_to_group
      refine wp_join_group (ts := [.bool])
        (fun (_, ()) md => md = m1)
        (fun _ ⟨dty0, ⟨⟩⟩ md hmd => ?_)
        (fun Jd hJd => by
          m3_split_fast
          · m3_let; exact hJd (true, ()) m1 rfl
          · m3_split_fast <;> (m3_let; exact hJd (_, ()) m1 rfl))
      subst md; m3_to_group
      refine wp_loop_inv
        (fun (_dty, i, ()) mi => ∃ (repri tmpi : List (BitVec 32)),
          repri.length = 2 * c.max_vars ∧ tmpi.length = c.max_vars ∧
          i.toNat ≤ arity.toNat ∧ FullCongReprInv F_cur (2 * cv0) repri ∧
          (∀ k' < i.toNat,
            (tmpi[k']?.getD 0#32).toNat < 2 * cv0 ∧
            LitEquiv (cnfOfClauses F_cur) (scr0[g.toNat + 2 + k']?.getD 0#32).toNat
              (tmpi[k']?.getD 0#32).toNat) ∧
          (FullMem c (wsState st repri tmpi) ⋆ R) mi)
        (fun (_, i, ()) _ => arity.toNat - i.toNat)
        (fun Ji hJi => by
          m3_steps; exact hJi (dty0, 0#32, ()) m1 ⟨repr1, st.core.tmp, hrl1.trans hrl_t, htmpl_t,
            Nat.zero_le _, hrepr1, fun _ h => by simp at h, hm1'⟩)
        (fun Ji (dty, i, ()) mi ⟨repri, tmpi, hrli, htli, hi_le, hrepri, htmp_i, hmi⟩ ihi => ?_)
      have hoki : WorkStepOk32 c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat ht_off.toNat ht_sz.toNat
          scr0 (wsState st repri tmpi) := workStepOk32_wsState hok_t hrli htli hrepri
      m3_split_fast
      · have hi_lt : i.toNat < arity.toNat := bv32_ult_lt (by rw [hst_g1] at hc; exact hc)
        obtain ⟨ri, hri_get, hri_lt⟩ := hrhs0 i.toNat hi_lt
        have hg2i_n : (g + 2 + i.setWidth 64).toNat = g.toNat + 2 + i.toNat :=
          bv64_add_zext32 (k := 2) (by omega)
        have hg2i_arr : (g + 2 + i.setWidth 64).toNat < st.scratch.scratch_buf.length := by
          rw [hg2i_n]; omega
        have hst_g2i : st.scratch.scratch_buf[(g + 2 + i.setWidth 64).toNat]'hg2i_arr = ri :=
          scr_g2i_get hpref_t hri_get (by omega) hg2i_n hg2i_arr
        m3_steps; m3_call hFind
        refine ⟨F_cur, 2 * cv0, repri, FullReprRest c (wsState st repri tmpi) ⋆ R, hrepri,
          by dsimp only [wsState]; rw [hst_g2i]; exact hri_lt, focus_full_repr hmi,
          fun rval repri' mi' hrl_i' hrepr_i' _ hrval_lt hrval_eqv hmi' => ?_⟩
        have hmi'' : (FullMem c (wsState st repri' tmpi) ⋆ R) mi' := ws_unfocus_repr hmi'
        clear hmi'
        have hri_tmk : ((ri >>> 1).setWidth 64).toNat < st.scratch.tarjan_mark.length := by
          rw [bv_zext32_toNat]; have := bv32_div2_lt_of_lt2 hri_lt; omega
        have hstg2i_tmk :
            ((st.scratch.scratch_buf[(g + 2 + i.setWidth 64).toNat]'hg2i_arr >>> 1).setWidth
              64).toNat < st.scratch.tarjan_mark.length := by
          rw [hst_g2i]; exact hri_tmk
        have hrval_tmk : ((rval >>> 1).setWidth 64).toNat < st.scratch.tarjan_mark.length := by
          rw [bv_zext32_toNat]; have := bv32_div2_lt_of_lt2 hrval_lt; omega
        have hi_tmp : i.toNat < tmpi.length := by omega
        have hi1_n : (i + 1#32).toNat = i.toNat + 1 := bv32_add1_toNat (by omega) (by omega)
        m3_to_group; refine wp_join_group (ts := [.bool])
          (fun (_dty', ()) m_d => m_d = mi' ∧ (FullMem c (wsState st repri' tmpi) ⋆ R) m_d) ?_ ?_
        · rintro _ ⟨dty', ⟨⟩⟩ m_d ⟨hmd_eq, hmd⟩; subst m_d
          have hfs_tmp := focus_full_tmp hmd; clear hmd
          generalize hR_tmp : FullTmpRest c (wsState st repri' tmpi) ⋆ R = R_tmp at hfs_tmp
          have hi32 : i32.bytes = 4 := rfl; m3_steps; subst hR_tmp
          rw [bv_zext32_toNat] at hm
          exact ihi (dty', i + 1#32, ()) m (by dsimp only; omega)
            ⟨repri', tmpi.set i.toNat rval, hrl_i'.trans hrli,
             by rw [List.length_set]; exact htli, by omega, hrepr_i',
             fun k' hk' => ws_find_tmp_step htmp_i htli (by omega) hri_get hrval_lt
               (by dsimp only [wsState] at hrval_eqv; rwa [hst_g2i] at hrval_eqv)
               k' (hi1_n ▸ hk'),
             ws_unfocus_tmp hm⟩
        · intro Jd hJd; m3_split_fast
          · m3_steps; exact hJd (true, ()) mi' ⟨rfl, hmi''⟩
          · m3_split_fast
            · m3_steps; exact hJd (true, ()) mi' ⟨rfl, hmi''⟩
            · m3_let; exact hJd (dty, ()) mi' ⟨rfl, hmi''⟩
      · have hi_eq : i.toNat = arity.toNat := by
          have hnot : ¬ i.toNat < arity.toNat := by
            rw [hst_g1] at hc; simpa [arity] using bv32_ult_not_lt hc
          omega
        have htmp_i_len : arity.toNat ≤ tmpi.length := by omega
        have htmp_i' : ∀ (k' : Nat) (hk' : k' < arity.toNat),
            (tmpi[k']'(by omega)).toNat < 2 * cv0 ∧
            LitEquiv (cnfOfClauses F_cur) (scr0[g.toNat + 2 + k']?.getD 0#32).toNat
              (tmpi[k']'(by omega)).toNat := fun k' hk' => by
          have h := htmp_i k' (by omega)
          rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at h
        clear hc; m3_split_fast
        rotate_left
        · m3_steps; rw [hst_g1]
          exact ihg (changed, work + 1#64, g + 2#64 + arity.setWidth 64, ()) mi
            (by dsimp only; rw [hnext_g]; omega)
            ⟨wsState st repri tmpi, by rw [hnext_g]; exact hbd_g', hoki, hseq_next', hmi⟩
        · clear hc; m3_to_group
          let WsP := WsPost c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat ht_off.toNat ht_sz.toNat
            scr0 R tag
          refine wp_join_group (ts := [.bool, i32, i32, i32, .bool])
            (fun (_changed', lhs_n, _iw, harity, need_hash, ()) mj =>
              WsP lhs_n harity need_hash mj)
            ?_ ?_
          · rintro _ ⟨changed', lhs_n, _iw, harity, need_hash, ⟨⟩⟩ mj ⟨stj, hokj, hgatej, hmj⟩
            m3_split_fast
            rotate_left
            · m3_steps; rw [hst_g1]
              exact ihg (changed', work + 4#64, g + 2#64 + arity.setWidth 64, ()) mj
                (by dsimp only; rw [hnext_g]; omega)
                ⟨stj, by rw [hnext_g]; exact hbd_g', hokj, hseq_next', hmj⟩
            · obtain ⟨hlhs_n_lt, hhar_cv, hgat0, hgat1, hgat2⟩ := hgatej hc
              have hhar_tmp : harity.toNat ≤ stj.core.tmp.length := by
                rw [hokj.1.core_ok.tmp_len_arr]; exact Nat.le_trans hhar_cv hcv0_le
              m3_to_group
              refine wp_loop_inv
                (fun (ih_v, _hv, ()) mhv => mhv = mj ∧ ih_v.toNat ≤ harity.toNat)
                (fun (ih_v, _, ()) _ => harity.toNat - ih_v.toNat)
                (fun Jhv hJhv => by m3_steps; exact hJhv (0#32, _, ()) mj ⟨rfl, Nat.zero_le _⟩)
                (fun Jhv (ih_v, _hv, ()) mhv ⟨hmhv, hih_le⟩ ih_hv => ?_)
              subst mhv; m3_split_fast
              · have hih_lt : ih_v.toNat < harity.toNat := bv32_ult_lt hc
                have hih_arr : (ih_v.setWidth 64).toNat < stj.core.tmp.length := by
                  rw [bv_zext32_toNat]; omega
                have hih1 : (ih_v + 1#32).toNat = ih_v.toNat + 1 :=
                  bv32_add1_toNat (by omega) (by omega)
                m3_steps; exact ih_hv (ih_v + 1#32, _, ()) mj (by dsimp only; omega) ⟨rfl, by omega⟩
              · clear hc
                let StOkP := WorkStepOk32 c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat
                  ht_off.toNat ht_sz.toNat scr0
                m3_to_group
                refine wp_loop_break_group (brkTs := [.bool, i64, i64, .bool])
                  (lpTs := [i64, i64, .bool])
                  (fun (ch_p, _, _, _, ()) mp => ∃ stp : FullState,
                    StOkP stp ∧ (FullMem c stp ⋆ R) mp)
                  (fun remp (slot, probes, _seen_self, ()) mp => ∃ stp : FullState,
                    slot.toNat < ht_sz.toNat ∧ probes.toNat ≤ 64 ∧ remp = 64 - probes.toNat ∧
                    stp.core.tmp = stj.core.tmp ∧ StOkP stp ∧ (FullMem c stp ⋆ R) mp)
                  ?_ ?_ ?_
                · rintro _ ⟨ch_p, _, _, _, ⟨⟩⟩ mp ⟨stp, hokp, hmp⟩
                  m3_let; rw [hst_g1]
                  exact ihg (ch_p, work + 4#64, g + 2#64 + arity.setWidth 64, ()) mp
                    (by dsimp only; rw [hnext_g]; omega)
                    ⟨stp, by rw [hnext_g]; exact hbd_g', hokp, hseq_next', hmp⟩
                · rintro Bp Lp remp ⟨slot, probes, seen_self, ⟨⟩⟩ mp hBp hLp
                    ⟨stp, hslot_lt, hpr_le, rfl, htmp_p, hokp, hmp⟩
                  have hscrl_p := hokp.1.scratch_ok.scratch_buf_len
                  have hrl_p := hokp.1.core_ok.repr_len
                  have hrepr_p := hokp.2.2.2.2.2.2.2.2.2.2.2.1
                  have hpref_p := hokp.2.2.2.2.2.2.2.2.2.2.2.2.1
                  have hht_p := hokp.2.2.2.2.2.2.2.2.2.2.2.2.2
                  m3_split_fast
                  · have hpr_lt : probes.toNat < 64 := bv64_ult_lt hc
                    have hhts_n : (ht_off + slot).toNat = ht_off.toNat + slot.toNat := by
                      show (ht_off.toNat + slot.toNat) % 2 ^ 64 = ht_off.toNat + slot.toNat
                      exact Nat.mod_eq_of_lt (by omega)
                    have hhts_arr : (ht_off + slot).toNat < stp.scratch.scratch_buf.length := by
                      omega
                    let ent := stp.scratch.scratch_buf[(ht_off + slot).toNat]'hhts_arr
                    have hent_slot : stp.scratch.scratch_buf[ht_off.toNat + slot.toNat]?.getD
                        0xFFFFFFFF#32 = ent := by
                      rw [← hhts_n, List.getElem?_eq_getElem hhts_arr, Option.getD_some]
                    have hslot_next_lt : ((slot + 1#64) &&& (ht_sz - 1#64)).toNat <
                        ht_sz.toNat := bv64_and_sub1_lt hht_pos
                    have hpr1 : (probes + 1#64).toNat = probes.toNat + 1 :=
                      bv64_add1_toNat (n := 64) (by omega) (by decide)
                    clear hc; m3_split_fast
                    · -- `ent == 0xFFFFFFFFu`: insert if `!seen_self && h->res_sz < ht_lim`, break
                      m3_to_group; refine wp_join_group (ts := [])
                        (fun () mins => ∃ stins : FullState,
                          StOkP stins ∧ (FullMem c stins ⋆ R) mins)
                        (fun _ ⟨⟩ mins ⟨stins, hokins, hmins⟩ => by
                          m3_let
                          exact hBp (changed', slot, probes, seen_self, ()) mins
                            ⟨stins, hokins, hmins⟩)
                        ?_
                      intro Jins hJins; m3_split_fast
                      · m3_let; exact hJins () mp ⟨stp, hokp, hmp⟩
                      · m3_split_fast
                        · have hi32 : i32.bytes = 4 := rfl; m3_steps
                          have hm_ins : (FullMem c { stp with scratch := { stp.scratch with
                              scratch_buf := stp.scratch.scratch_buf.set (ht_off.toNat + slot.toNat)
                                (g.setWidth 32)
                              res_sz := stp.scratch.res_sz + 1#64 } } ⋆ R) m := by
                            rw [hhts_n] at hm; exact hm
                          exact hJins () m ⟨_, ws32_probe_insert_ok hokp hg_lt hg_le_ht hht_le
                            hslot_lt hgat, hm_ins⟩
                        · m3_let; exact hJins () mp ⟨stp, hokp, hmp⟩
                    · -- `ent != 0xFFFFFFFFu`: check self-match `ent == (u32)g` first!
                      have hent_ne : ent ≠ 0xFFFFFFFF#32 := beq_eq_false_iff_ne.mp hc
                      clear hc; m3_split_fast
                      · -- `ent == (u32)g` -> `seen_self = true; continue;`
                        m3_steps
                        exact hLp (64 - (probes + 1#64).toNat)
                          ((slot + 1#64) &&& (ht_sz - 1#64), probes + 1#64, true, ()) mp
                          (by omega) ⟨stp, hslot_next_lt, by omega, rfl, htmp_p, hokp, hmp⟩
                      · have hent_gate : GateAt32 F_cur cv0 scr0 g_len.toNat ent.toNat := by
                          rcases hht_p slot.toNat hslot_lt with he | hg_e
                          · rw [hent_slot] at he; exact absurd he hent_ne
                          · rwa [hent_slot] at hg_e
                        have ⟨elhs, emword, he0, he1, helhs_lt, hbd_e, _, _, herhs, hsem_e⟩ :=
                          hent_gate
                        have he0_arr : ent.toNat < stp.scratch.scratch_buf.length := by omega
                        have he1_n : (ent.setWidth 64 + 1).toNat = ent.toNat + 1 := by
                          rw [BitVec.toNat_add, bv_zext32_toNat]
                          show (ent.toNat + 1) % 2 ^ 64 = ent.toNat + 1; omega
                        have he1_arr : (ent.setWidth 64 + 1).toNat <
                            stp.scratch.scratch_buf.length := by omega
                        have hst_e0 : stp.scratch.scratch_buf[(ent.setWidth 64).toNat]'
                            (by rw [bv_zext32_toNat]; exact he0_arr) = elhs := by
                          have h := (hpref_p ent.toNat (by omega)).trans he0
                          rw [list_getElem_congr (bv_zext32_toNat ent) _ he0_arr]
                          rw [List.getElem?_eq_getElem he0_arr] at h; exact Option.some.inj h
                        have hst_e1 : stp.scratch.scratch_buf[(ent.setWidth 64 + 1).toNat]'he1_arr =
                            emword := by
                          have h := (hpref_p (ent.toNat + 1) (by omega)).trans he1
                          rw [← he1_n, List.getElem?_eq_getElem he1_arr] at h
                          exact Option.some.inj h
                        clear hc; m3_to_group; refine wp_join_group (ts := [.bool])
                          (fun _ mnxt => ∃ stn : FullState,
                            stn.core.tmp = stj.core.tmp ∧ StOkP stn ∧
                            (FullMem c stn ⋆ R) mnxt) ?_ ?_
                        · rintro _ ⟨_, ⟨⟩⟩ mnxt ⟨stn, htmp_n, hokn, hmn⟩
                          m3_let; exact hLp (64 - (probes + 1#64).toNat)
                            ((slot + 1#64) &&& (ht_sz - 1#64), probes + 1#64, seen_self, ()) mnxt
                            (by omega) ⟨stn, hslot_next_lt, by omega, rfl, htmp_n, hokn, hmn⟩
                        · intro Jnxt hJnxt
                          have hjnxt_keep : ∀ b : Val .bool, Jnxt (b, ()) mp := fun b =>
                            hJnxt (b, ()) mp ⟨stp, htmp_p, hokp, hmp⟩
                          m3_split_fast
                          · have hetag_eq : emword >>> 28 = tag := by
                              have hc1 : (stp.scratch.scratch_buf[
                                  (ent.setWidth 64 + 1).toNat]'he1_arr >>> 28 ==
                                st.scratch.scratch_buf[(g + 1).toNat]'hg1_arr >>> 28) = true := hc
                              have hc2 := beq_iff_eq.mp hc1
                              rwa [hst_e1, hst_g1] at hc2
                            clear hc; m3_to_group
                            refine wp_join_group (ts := [.bool, i32])
                              (fun (matched, match_lhs, ()) mmatch => ∃ repr_m : List (BitVec 32),
                                repr_m.length = 2 * c.max_vars ∧
                                FullCongReprInv F_cur (2 * cv0) repr_m ∧
                                (matched = true →
                                  match_lhs.toNat < 2 * cv0 ∧
                                  LitEquiv (cnfOfClauses F_cur) lhs_n.toNat match_lhs.toNat) ∧
                                (FullMem c { stp with core :=
                                  { stp.core with repr := repr_m } } ⋆ R) mmatch)
                              ?_ ?_
                            · rintro _ ⟨matched, match_lhs, ⟨⟩⟩ mmatch
                                ⟨repr_m, hrl_m, hrepr_m, heqv_m, hmm⟩
                              let stm : FullState :=
                                { stp with core := { stp.core with repr := repr_m } }
                              have hokm : StOkP stm := workStepOk32_with_repr hokp hrl_m hrepr_m
                              m3_split_fast
                              · obtain ⟨hml_lt, hlhs_ent⟩ := heqv_m hc
                                m3_steps; m3_call hEquiv
                                refine ws32_equiv_call hokm hlhs_n_lt hml_lt hlhs_ent hmm
                                  fun ef se me hoke _ hef2 me_mem => ?_
                                m5_after_fold hQ hef2 changed' work hoke me me_mem ch_ef =>
                                  exact hBp (ch_ef, slot, probes, seen_self, ()) me
                                    ⟨se, hoke, me_mem⟩
                              · m3_steps; exact hJnxt (_, ()) mmatch ⟨stm, htmp_p, hokm, hmm⟩
                            · intro Jm hJm; m3_split_fast
                              · have htag0_eq : tag = 0#32 := ws_tag_eq hst_g1 hc
                                obtain ⟨_, _, hand_eq⟩ := hgat0 htag0_eq
                                m3_steps; m3_call hMatch
                                refine ⟨c, F0, F_cur, stp, scr0, g_len.toNat, R, rfl, hokp.1,
                                  hokp.2.1, hokp.2.2.2.2.2.1, hokp.2.2.2.2.2.2.2.1 ▸ hrepr_p,
                                  by omega, hpref_p,
                                  by rw [hokp.2.2.2.2.2.2.2.1]; exact hent_gate,
                                  by rw [he1, Option.getD_some, hetag_eq, htag0_eq],
                                  by rw [hokp.2.2.2.2.2.2.2.1]; exact hhar_cv, hmp, ?_⟩
                                intro ok_m repr_m mm _ hrl_m hrepr_m hok_and hmm
                                m3_steps
                                exact hJm (ok_m, _, ()) mm
                                  ⟨repr_m, hrl_m, hokp.2.2.2.2.2.2.2.1 ▸ hrepr_m,
                                   fun hokt => ⟨by rw [hst_e0]; exact helhs_lt,
                                     by rw [hst_e0]
                                        exact ws_match_and_equiv (htmp_p ▸ hand_eq) he0
                                          (hok_and hokt).2.2⟩,
                                   hmm⟩
                              · clear hc; m3_to_group
                                refine wp_unroll_group (ts := [.bool, i32]) fun Jmb hJmb => ?_
                                have hJmb_q : ∀ (m_ok : Bool) (mlhs : BitVec 32)
                                    (repr_m : List (BitVec 32)) (mf : Mem 64),
                                    repr_m.length = 2 * c.max_vars →
                                    FullCongReprInv F_cur (2 * cv0) repr_m →
                                    (m_ok = true → mlhs.toNat < 2 * cv0 ∧
                                      LitEquiv (cnfOfClauses F_cur) lhs_n.toNat mlhs.toNat) →
                                    (FullMem c { stp with core :=
                                      { stp.core with repr := repr_m } } ⋆ R) mf →
                                    Jmb (m_ok, mlhs, ()) mf :=
                                  fun m_ok mlhs repr_m mf hrl hrepr hmok hmf =>
                                    hJmb (m_ok, mlhs, ()) mf (by
                                      m3_let
                                      exact hJm (m_ok, mlhs, ()) mf ⟨repr_m, hrl, hrepr, hmok, hmf⟩)
                                m3_to_group; refine wp_join_group (ts := []) (fun () mf => mf = mp)
                                  ?_ ?_
                                · rintro _ ⟨⟩ mf rfl; m3_to_group
                                  refine wp_unroll_group (ts := [.bool, i32]) fun Jm2 hJm2 => ?_
                                  have hJm2_q : ∀ (m_ok : Bool) (mlhs : BitVec 32)
                                      (repr_m : List (BitVec 32)) (mf' : Mem 64),
                                      repr_m.length = 2 * c.max_vars →
                                      FullCongReprInv F_cur (2 * cv0) repr_m →
                                      (m_ok = true → mlhs.toNat < 2 * cv0 ∧
                                        LitEquiv (cnfOfClauses F_cur) lhs_n.toNat mlhs.toNat) →
                                      (FullMem c { stp with core :=
                                        { stp.core with repr := repr_m } } ⋆ R) mf' →
                                      Jm2 (m_ok, mlhs, ()) mf' :=
                                    fun m_ok mlhs repr_m mf' hrl hrepr hmok hmf =>
                                      hJm2 (m_ok, mlhs, ()) mf' (by
                                        m3_let
                                        exact hJmb_q m_ok mlhs repr_m mf' hrl hrepr hmok hmf)
                                  m3_split_fast
                                  · have he_tag2 : tag = 2#32 := ws_tag_eq hst_g1 hc
                                    clear hc; m3_split_fast
                                    rotate_left
                                    · m3_let; exact hJm2_q false _ stp.core.repr mf hrl_p hrepr_p
                                        (fun h => (by cases h)) hmp
                                    obtain ⟨har_ite, hite_s⟩ := hgat2 he_tag2
                                    have hite_e := ws_tag2_ite_def (by rw [hetag_eq, he_tag2])
                                      hsem_e
                                    have ha_e : (emword &&& 0xFF#32).toNat = 3 := by
                                      have ht2 : (emword >>> 28).toNat = 2 := by
                                        rw [hetag_eq, he_tag2]; decide
                                      rcases hsem_e with ⟨ht, _⟩ | ⟨ht, _⟩ | ⟨_, h, _⟩
                                      · omega
                                      · omega
                                      · exact h
                                    obtain ⟨er0, her0_get, her0_lt⟩ := herhs 0 (by omega)
                                    obtain ⟨er1, her1_get, her1_lt⟩ := herhs 1 (by omega)
                                    obtain ⟨er2, her2_get, her2_lt⟩ := herhs 2 (by omega)
                                    have he2_arr := scr_e_lt (scr := stp.scratch.scratch_buf)
                                      (g_len := g_len.toNat) (ent := ent) 2 (by omega) (by omega)
                                      (by omega)
                                    have he3_arr := scr_e_lt (scr := stp.scratch.scratch_buf)
                                      (g_len := g_len.toNat) (ent := ent) 3 (by omega) (by omega)
                                      (by omega)
                                    have he4_arr := scr_e_lt (scr := stp.scratch.scratch_buf)
                                      (g_len := g_len.toNat) (ent := ent) 4 (by omega) (by omega)
                                      (by omega)
                                    have hst_e2 := scr_e_get (g_len := g_len.toNat) 2 (by omega)
                                      hpref_p her0_get he2_arr (by omega)
                                    have hst_e3 := scr_e_get (g_len := g_len.toNat) 3 (by omega)
                                      hpref_p her1_get he3_arr (by omega)
                                    have hst_e4 := scr_e_get (g_len := g_len.toNat) 4 (by omega)
                                      hpref_p her2_get he4_arr (by omega)
                                    m3_steps; m3_call hFind
                                    refine ⟨F_cur, 2 * cv0, stp.core.repr, FullReprRest c stp ⋆ R,
                                      hrepr_p, hst_e2 ▸ her0_lt, focus_full_repr hmp,
                                      fun ec repra ma hrla hrepra _ _ hec_eqv hma => ?_⟩
                                    have hma' := unfocus_full_repr hma; clear hma
                                    m3_steps; m3_call hFind
                                    refine ⟨F_cur, 2 * cv0, repra,
                                      FullReprRest c { stp with core :=
                                        { stp.core with repr := repra } } ⋆ R,
                                      hrepra, hst_e3 ▸ her1_lt, focus_full_repr hma',
                                      fun et reprb mb hrlb hreprb _ _ het_eqv hmb => ?_⟩
                                    have hmb' := unfocus_full_repr hmb; clear hmb
                                    m3_steps; m3_call hFind
                                    refine ⟨F_cur, 2 * cv0, reprb,
                                      FullReprRest c { stp with core :=
                                        { stp.core with repr := reprb } } ⋆ R,
                                      hreprb, hst_e4 ▸ her2_lt, focus_full_repr hmb',
                                      fun ee reprc mc hrlc hreprc _ _ hee_eqv hmc => ?_⟩
                                    let stpc : FullState :=
                                      { stp with core := { stp.core with repr := reprc } }
                                    have hmc' : (FullMem c stpc ⋆ R) mc := by
                                      simpa [stpc] using unfocus_full_repr hmc
                                    clear hmc
                                    have hite_e' : IteGateDef (cnfOfClauses F_cur) elhs.toNat
                                        ec.toNat et.toNat ee.toNat :=
                                      ite_eval_congr hite_e (LitEquiv.refl _ _)
                                        (by rw [her0_get, Option.getD_some, ← hst_e2]
                                            exact hec_eqv)
                                        (by rw [her1_get, Option.getD_some, ← hst_e3]
                                            exact het_eqv)
                                        (by rw [her2_get, Option.getD_some, ← hst_e4]
                                            exact hee_eqv)
                                    have h3 : harity.toNat = 3 := by rw [har_ite]; decide
                                    have hstp_tl : stp.core.tmp.length = c.max_vars :=
                                      hokp.1.core_ok.tmp_len_arr
                                    have htmp_ge3 : 3 ≤ stpc.core.tmp.length := by
                                      change 3 ≤ stp.core.tmp.length; omega
                                    have h0_c :
                                        (0#64 : BitVec 64).toNat < stpc.core.tmp.length := by
                                      change 0 < stp.core.tmp.length; omega
                                    have h1_c :
                                        (1#64 : BitVec 64).toNat < stpc.core.tmp.length := by
                                      change 1 < stp.core.tmp.length; omega
                                    have h2_c :
                                        (2#64 : BitVec 64).toNat < stpc.core.tmp.length := by
                                      change 2 < stp.core.tmp.length; omega
                                    have ht0_eq := tmp_st_get (k := 0) htmp_p (by omega)
                                    have ht1_eq := tmp_st_get (k := 1) htmp_p (by omega)
                                    have ht2_eq := tmp_st_get (k := 2) htmp_p (by omega)
                                    m3_to_group; refine wp_join_group (ts := [i32, i32, i32])
                                      (fun (ec', et', ee', ()) mfin => mfin = mc ∧
                                        IteGateDef (cnfOfClauses F_cur) elhs.toNat
                                          ec'.toNat et'.toNat ee'.toNat)
                                      (fun _ ⟨ec', et', ee', ⟨⟩⟩ mfin ⟨hmfin, hite_f1⟩ => by
                                        subst mfin; m3_to_group
                                        refine wp_join_group (ts := [i32, i32, i32])
                                          (fun (mlhs', et2, ee2, ()) mfin2 => mfin2 = mc ∧
                                            mlhs'.toNat < 2 * cv0 ∧
                                            IteGateDef (cnfOfClauses F_cur) mlhs'.toNat
                                              ec'.toNat et2.toNat ee2.toNat)
                                          (fun _ ⟨mlhs', et2, ee2, ⟨⟩⟩ mfin2
                                            ⟨hmfin2, hml_lt, hite_f⟩ => by
                                            subst mfin2; m3_to_group
                                            refine wp_unroll_group (ts := [.bool])
                                              fun Jmi hJmi => ?_
                                            have hJm_ok : ∀ b : Bool,
                                                (b = true → mlhs'.toNat < 2 * cv0 ∧
                                                  LitEquiv (cnfOfClauses F_cur)
                                                    lhs_n.toNat mlhs'.toNat) →
                                                Jmi (b, ()) mc := fun b hm =>
                                              hJmi (b, ()) mc (by
                                                m3_let
                                                exact hJm2_q b mlhs' reprc mc (by omega) hreprc hm
                                                  hmc')
                                            m3_split_fast
                                            · have hc0 : ec' = stj.core.tmp[0]'(by omega) := by
                                                have h : ec' = stpc.core.tmp[0] := beq_iff_eq.mp hc
                                                rw [h, ht0_eq, List.getElem?_eq_getElem (by omega),
                                                  Option.getD_some]
                                              clear hc; m3_split_fast
                                              · have hc1 : et2 = stj.core.tmp[1]'(by omega) := by
                                                  have h : et2 = stpc.core.tmp[1] :=
                                                    beq_iff_eq.mp hc
                                                  rw [h, ht1_eq,
                                                    List.getElem?_eq_getElem (by omega),
                                                    Option.getD_some]
                                                clear hc; m3_split_fast
                                                · have hc2 : ee2 = stj.core.tmp[2]'(by omega) := by
                                                    have h : ee2 = stpc.core.tmp[2] :=
                                                      beq_iff_eq.mp hc
                                                    rw [h, ht2_eq,
                                                      List.getElem?_eq_getElem (by omega),
                                                      Option.getD_some]
                                                  m3_steps
                                                  exact hJm_ok true fun _ => ⟨hml_lt,
                                                    ws_hash_ite_equiv (by omega) hite_s hite_f hc0
                                                      hc1 hc2⟩
                                                · m3_let; exact hJm_ok false (fun h => by cases h)
                                              · m3_let; exact hJm_ok false (fun h => by cases h)
                                            · m3_let; exact hJm_ok false (fun h => by cases h))
                                          ?_
                                        intro Jf2 hJf2; m3_split_fast
                                        · m3_steps
                                          refine hJf2 (_, et' ^^^ 1#32, ee' ^^^ 1#32, ()) mc
                                            ⟨rfl, by rw [hst_e0, bv32_xor1_litNeg]
                                                     exact bv32_xor1_lt_even helhs_lt, ?_⟩
                                          rw [hst_e0]
                                          simp only [bv32_xor1_litNeg, bv32_xor1_eq_litNeg]
                                          exact iteGateDef_flip_out hite_f1
                                        · m3_let; exact hJf2 (_, et', ee', ()) mc
                                            ⟨rfl, by rw [hst_e0]; exact helhs_lt,
                                             by rw [hst_e0]; exact hite_f1⟩)
                                      ?_
                                    intro Jf hJf; m3_split_fast
                                    · m3_steps; refine hJf (ec ^^^ 1#32, ee, et, ()) mc ⟨rfl, ?_⟩
                                      rw [bv32_xor1_eq_litNeg]; exact iteGateDef_flip_cond hite_e'
                                    · m3_let; exact hJf (ec, et, ee, ()) mc ⟨rfl, hite_e'⟩
                                  · m3_let; exact hJm2_q false _ stp.core.repr mf hrl_p hrepr_p
                                      (fun h => (by cases h)) hmp
                                · intro Jt2 hJt2; m3_split_fast
                                  · have he_tag1 : tag = 1#32 := ws_tag_eq hst_g1 hc
                                    clear hc; m3_split_fast
                                    rotate_left
                                    · m3_let; exact hJt2 () mp rfl
                                    · obtain ⟨har_xor, hxor_s⟩ := hgat1 he_tag1
                                      have hxor_e := ws_tag1_xor_def (by rw [hetag_eq, he_tag1])
                                        hsem_e
                                      have ha_e : (emword &&& 0xFF#32).toNat = 2 := by
                                        have ht1 : (emword >>> 28).toNat = 1 := by
                                          rw [hetag_eq, he_tag1]; decide
                                        rcases hsem_e with ⟨ht, _⟩ | ⟨_, h, _⟩ | ⟨ht, _⟩
                                        · omega
                                        · exact h
                                        · omega
                                      obtain ⟨er0, her0_get, her0_lt⟩ := herhs 0 (by omega)
                                      obtain ⟨er1, her1_get, her1_lt⟩ := herhs 1 (by omega)
                                      have he2_arr := scr_e_lt (scr := stp.scratch.scratch_buf)
                                        (g_len := g_len.toNat) (ent := ent) 2 (by omega) (by omega)
                                        (by omega)
                                      have he3_arr := scr_e_lt (scr := stp.scratch.scratch_buf)
                                        (g_len := g_len.toNat) (ent := ent) 3 (by omega) (by omega)
                                        (by omega)
                                      have hst_e2 := scr_e_get (g_len := g_len.toNat) 2 (by omega)
                                        hpref_p her0_get he2_arr (by omega)
                                      have hst_e3 := scr_e_get (g_len := g_len.toNat) 3 (by omega)
                                        hpref_p her1_get he3_arr (by omega)
                                      m3_steps; m3_call hFind
                                      refine ⟨F_cur, 2 * cv0, stp.core.repr, FullReprRest c stp ⋆ R,
                                        hrepr_p, hst_e2 ▸ her0_lt, focus_full_repr hmp,
                                        fun e0 repra ma hrla hrepra _ he0_lt he0_eqv hma => ?_⟩
                                      have hma' := unfocus_full_repr hma; clear hma
                                      m3_steps; m3_call hFind
                                      refine ⟨F_cur, 2 * cv0, repra,
                                        FullReprRest c { stp with core :=
                                          { stp.core with repr := repra } } ⋆ R,
                                        hrepra, hst_e3 ▸ her1_lt, focus_full_repr hma',
                                        fun e1 reprb mb hrlb hreprb _ he1_lt he1_eqv hmb => ?_⟩
                                      let stpb : FullState :=
                                        { stp with core := { stp.core with repr := reprb } }
                                      have hmb' : (FullMem c stpb ⋆ R) mb := by
                                        simpa [stpb] using unfocus_full_repr hmb
                                      clear hmb
                                      have h2 : harity.toNat = 2 := by rw [har_xor]; decide
                                      have hstp_tl : stp.core.tmp.length = c.max_vars :=
                                        hokp.1.core_ok.tmp_len_arr
                                      have htmp_ge2 : 2 ≤ stpb.core.tmp.length := by
                                        change 2 ≤ stp.core.tmp.length; omega
                                      have h0_b :
                                          (0#64 : BitVec 64).toNat < stpb.core.tmp.length := by
                                        change 0 < stp.core.tmp.length; omega
                                      have h1_b :
                                          (1#64 : BitVec 64).toNat < stpb.core.tmp.length := by
                                        change 1 < stp.core.tmp.length; omega
                                      have ht0_eq := tmp_st_get (k := 0) htmp_p (by omega)
                                      have ht1_eq := tmp_st_get (k := 1) htmp_p (by omega)
                                      have hxor_e' : XorGateDef (cnfOfClauses F_cur) elhs.toNat
                                          e0.toNat e1.toNat :=
                                        xor_eval_congr hxor_e (LitEquiv.refl _ _)
                                          (by rw [her0_get, Option.getD_some, ← hst_e2]
                                              exact he0_eqv)
                                          (by rw [her1_get, Option.getD_some, ← hst_e3]
                                              exact he1_eqv)
                                      have hstrip_e :=
                                        xor_sign_strip_sound helhs_lt he0_lt he1_lt hxor_e'
                                      let mlhs_e := elhs ^^^ ((e0 ^^^ e1) &&& 1#32)
                                      let e0p := e0 &&& ~~~1#32
                                      let e1p := e1 &&& ~~~1#32
                                      m3_to_group
                                      refine wp_unroll_group (ts := [.bool]) fun Jx0 hJx0 => ?_
                                      have hJxor : ∀ b : Bool,
                                          (b = true → LitEquiv (cnfOfClauses F_cur)
                                            lhs_n.toNat mlhs_e.toNat) →
                                          Jx0 (b, ()) mb := fun b hm =>
                                        hJx0 (b, ()) mb (by
                                          m3_steps
                                          refine hJmb_q b _ reprb mb (by omega) hreprb
                                            (fun ht => ?_) hmb'
                                          rw [hst_e0]
                                          exact ⟨hstrip_e.1, hm ht⟩)
                                      m3_to_group
                                      refine wp_join_group (ts := []) (fun _ mf => mf = mb) ?_ ?_
                                      · rintro _ ⟨⟩ _ rfl; m3_split_fast
                                        · have hc0 : e0p = stj.core.tmp[1]'(by omega) := by
                                            have h : e0p = stpb.core.tmp[1] := beq_iff_eq.mp hc
                                            rw [h, ht1_eq, List.getElem?_eq_getElem (by omega),
                                              Option.getD_some]
                                          clear hc; m3_split_fast
                                          · have hc1 : e1p = stj.core.tmp[0]'(by omega) := by
                                              have h : e1p = stpb.core.tmp[0] := beq_iff_eq.mp hc
                                              rw [h, ht0_eq, List.getElem?_eq_getElem (by omega),
                                                Option.getD_some]
                                            m3_let; exact hJxor true fun _ =>
                                              ws_hash_xor_equiv (by omega) hxor_s hstrip_e.2.2.2.2
                                                hc1 hc0
                                          · m3_let; exact hJxor false (fun h => by cases h)
                                        · m3_let; exact hJxor false (fun h => by cases h)
                                      · intro Jfb hJfb; m3_split_fast
                                        · have hc0 : e0p = stj.core.tmp[0]'(by omega) := by
                                            have h : e0p = stpb.core.tmp[0] := beq_iff_eq.mp hc
                                            rw [h, ht0_eq, List.getElem?_eq_getElem (by omega),
                                              Option.getD_some]
                                          clear hc; m3_split_fast
                                          · have hc1 : e1p = stj.core.tmp[1]'(by omega) := by
                                              have h : e1p = stpb.core.tmp[1] := beq_iff_eq.mp hc
                                              rw [h, ht1_eq, List.getElem?_eq_getElem (by omega),
                                                Option.getD_some]
                                            m3_let; exact hJxor true fun _ =>
                                              ws_hash_xor_equiv (by omega) hxor_s hstrip_e.2.2.2.1
                                                hc0 hc1
                                          · m3_let; exact hJfb () mb rfl
                                        · m3_let; exact hJfb () mb rfl
                                  · m3_let; exact hJt2 () mp rfl
                          · m3_let; exact hjnxt_keep _
                  · m3_steps
                    exact hBp (changed', slot, probes, seen_self, ()) mp ⟨stp, hokp, hmp⟩
                · intro _ Lp _ hLp; m3_steps
                  exact hLp 64 (_ &&& (ht_sz - 1#64), 0#64, false, ()) mj
                    ⟨stj, bv64_and_sub1_lt hht_pos, by decide, rfl, rfl, hokj, hmj⟩
          · intro Jgfin hJgfin
            let raw := tmpi.take arity.toNat
            have hraw_len : raw.length = arity.toNat := by simp [raw]; omega
            have hraw_lt : ∀ k < arity.toNat, (raw[k]?.getD 0#32).toNat < 2 * cv0 := fun k hk => by
              have hget : raw[k]?.getD 0#32 = tmpi[k]'(by omega) := by
                simp only [raw, List.getElem?_take, ite_eq_left hk]
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
              rw [hget]; exact (htmp_i' k hk).1
            have hraw_eqv : ∀ k < arity.toNat,
                LitEquiv (cnfOfClauses F_cur) (scr0[g.toNat + 2 + k]?.getD 0#32).toNat
                  (raw[k]?.getD 0#32).toNat := fun k hk => by
              have hget : raw[k]?.getD 0#32 = tmpi[k]'(by omega) := by
                simp only [raw, List.getElem?_take, ite_eq_left hk]
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
              rw [hget]; exact (htmp_i' k hk).2
            m3_split_fast
            · -- Branch `tag == 0u` (AND)
              have htag0 : tag = 0#32 := ws_tag_eq hst_g1 hc
              have hand0 := ws_tag0_and_def htag0 hsem0
              let rhs : List Nat := ((scr0.drop (g.toNat + 2)).take arity.toNat).map BitVec.toNat
              have hscr_ge : g.toNat + 2 + arity.toNat ≤ scr0.length := by
                dsimp only [arity]
                rcases Nat.eq_zero_or_pos (mword &&& 0xFF#32).toNat with hz | hpos
                · have := (List.getElem?_eq_some_iff.mp hscr0_g1).1; omega
                · obtain ⟨_, hr, _⟩ := hrhs0 ((mword &&& 0xFF#32).toNat - 1) (by omega)
                  have := (List.getElem?_eq_some_iff.mp hr).1; omega
              obtain ⟨hraw_of_rhs, hrhs_of_raw⟩ :=
                ws_tag0_raw_of_rhs htmp_i_len hscr_ge hraw_eqv
              clear hc; m3_to_group
              refine wp_loop_inv
                (fun (il, has_false, na, ()) ml => ∃ tmpl : List (BitVec 32),
                  tmpl.length = c.max_vars ∧ na.toNat ≤ il.toNat ∧ il.toNat ≤ arity.toNat ∧
                  (∀ j, il.toNat ≤ j → j < arity.toNat → tmpl[j]? = raw[j]?) ∧
                  (∀ j < na.toNat, ∃ k < arity.toNat, tmpl[j]? = raw[k]?) ∧
                  (has_false = true → ∃ k < arity.toNat,
                    st.core.vals[(raw[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) ∧
                  (has_false = false → ∀ k < il.toNat,
                    st.core.vals[(raw[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8 ∨
                    ∃ j < na.toNat, tmpl[j]? = raw[k]?) ∧
                  (FullMem c (wsState st repri tmpl) ⋆ R) ml)
                (fun (il, _, _, ()) _ => arity.toNat - il.toNat)
                (fun Jl hJl => by
                  m3_steps
                  exact hJl (0#32, false, 0#32, ()) mi ⟨tmpi, htli, Nat.zero_le _, Nat.zero_le _,
                    fun j _ hj => (by simp [raw, hj]),
                    fun _ h => (by simp at h), fun h => (by cases h),
                    fun _ _ h => (by simp at h), hmi⟩)
                (fun Jl (il, has_false, na, ()) ml ⟨tmpl, htl_l, hna_le, hil_le, htail_l,
                  hsub_l, hhf_l, hnohf_l, hml⟩ ihl => ?_)
              have hokl := workStepOk32_wsState hok_t hrli htl_l hrepri
              m3_split_fast
              · have hil_lt : il.toNat < arity.toNat :=
                  bv32_ult_lt (by rw [hst_g1] at hc; exact hc)
                have hil_tmp : (il.setWidth 64).toNat < tmpl.length := by
                  rw [bv_zext32_toNat]; omega
                have hil_tl : il.toNat < tmpl.length := by omega
                have hil_raw : il.toNat < raw.length := by rw [hraw_len]; exact hil_lt
                have hr_eq : tmpl[(il.setWidth 64).toNat]'hil_tmp = raw[il.toNat]'hil_raw :=
                  (list_getElem_zext32_eq rfl hil_tmp hil_tl).trans
                    (list_getElem_eq_of_eqD hil_tl
                      ((htail_l il.toNat (Nat.le_refl _) hil_lt).trans
                        (List.getElem?_eq_getElem hil_raw)))
                have hr_lt : (raw[il.toNat]'hil_raw).toNat < 2 * cv0 := by
                  have h := hraw_lt il.toNat hil_lt
                  rwa [List.getElem?_eq_getElem hil_raw, Option.getD_some] at h
                have hr_vals' : (raw[il.toNat]'hil_raw).toNat < st.core.vals.length := by omega
                have hr_vals : ((tmpl[(il.setWidth 64).toNat]'hil_tmp).setWidth 64).toNat <
                    st.core.vals.length := by
                  rw [hr_eq, bv_zext32_toNat]; exact hr_vals'
                have hil1 : (il + 1#32).toNat = il.toNat + 1 :=
                  bv32_add1_toNat (n := arity.toNat) (by omega) (by omega)
                have hna1 : (na + 1#32).toNat = na.toNat + 1 :=
                  bv32_add1_toNat (n := arity.toNat) (by omega) (by omega)
                have hna_tmp : (na.setWidth 64).toNat < tmpl.length := by
                  rw [bv_zext32_toNat]; omega
                have hrv_dom := hokl.2.1.vals_domain (raw[il.toNat]'hil_raw).toNat
                  (by change _ < 2 * st.core.cur_vars; rw [hcv_t]; exact hr_lt)
                have hrv_get : st.core.vals[
                    ((tmpl[(il.setWidth 64).toNat]'hil_tmp).setWidth 64).toNat]'hr_vals =
                    st.core.vals[(raw[il.toNat]'hil_raw).toNat]'hr_vals' := by
                  have h1 : ((tmpl[(il.setWidth 64).toNat]'hil_tmp).setWidth 64).toNat =
                      (raw[il.toNat]'hil_raw).toNat := by
                    rw [hr_eq, bv_zext32_toNat]
                  exact list_getElem_congr h1 hr_vals hr_vals'
                m3_to_group
                refine wp_unroll_group (ts := [.bool, i32]) fun Jil hJil => ?_
                have hJil_step : ∀ (hf' : Bool) (na' : BitVec 32) (ml' : Mem 64),
                    (∃ tmpl' : List (BitVec 32),
                      tmpl'.length = c.max_vars ∧ na'.toNat ≤ (il + 1#32).toNat ∧
                      (il + 1#32).toNat ≤ arity.toNat ∧
                      (∀ j, (il + 1#32).toNat ≤ j → j < arity.toNat → tmpl'[j]? = raw[j]?) ∧
                      (∀ j < na'.toNat, ∃ k < arity.toNat, tmpl'[j]? = raw[k]?) ∧
                      (hf' = true → ∃ k < arity.toNat,
                        st.core.vals[(raw[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) ∧
                      (hf' = false → ∀ k < (il + 1#32).toNat,
                        st.core.vals[(raw[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8 ∨
                        ∃ j < na'.toNat, tmpl'[j]? = raw[k]?) ∧
                      (FullMem c (wsState st repri tmpl') ⋆ R) ml') →
                    Jil (hf', na', ()) ml' := fun hf' na' ml' h =>
                  hJil (hf', na', ()) ml'
                    (by m3_let; exact ihl (il + 1#32, hf', na', ()) ml' (by dsimp only; omega) h)
                m3_split_fast
                · have hr_gd : raw[il.toNat]?.getD 0#32 = raw[il.toNat]'hil_raw := by
                    rw [List.getElem?_eq_getElem hil_raw, Option.getD_some]
                  have hff : st.core.vals[(raw[il.toNat]?.getD 0#32).toNat]?.getD 0#8 =
                      0xFF#8 := by
                    rw [hr_gd]
                    exact vals_slt0_eqff hr_vals' _ hrv_dom (hrv_get ▸ hc)
                  m3_steps; exact hJil_step true na ml ⟨tmpl, htl_l, by omega, by omega,
                    fun j hj1 hj2 => htail_l j (by omega) hj2, hsub_l,
                    fun _ => ⟨il.toNat, hil_lt, hff⟩, (fun h => by cases h), hml⟩
                · have hnslt_se : ((st.core.vals[
                      ((tmpl[(il.setWidth 64).toNat]'hil_tmp).setWidth 64).toNat]'
                        hr_vals).signExtend 32).slt 0#32 = false := hc
                  m3_to_group; refine wp_unroll_group (ts := [i32]) fun Jna hJna => ?_
                  have hJna_step : ∀ (na' : BitVec 32) (ml' : Mem 64),
                      (∃ tmpl' : List (BitVec 32),
                        tmpl'.length = c.max_vars ∧ na'.toNat ≤ (il + 1#32).toNat ∧
                        (il + 1#32).toNat ≤ arity.toNat ∧
                        (∀ j, (il + 1#32).toNat ≤ j → j < arity.toNat → tmpl'[j]? = raw[j]?) ∧
                        (∀ j < na'.toNat, ∃ k < arity.toNat, tmpl'[j]? = raw[k]?) ∧
                        (has_false = true → ∃ k < arity.toNat,
                          st.core.vals[(raw[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) ∧
                        (has_false = false → ∀ k < (il + 1#32).toNat,
                          st.core.vals[(raw[k]?.getD 0#32).toNat]?.getD 0#8 = 1#8 ∨
                          ∃ j < na'.toNat, tmpl'[j]? = raw[k]?) ∧
                        (FullMem c (wsState st repri tmpl') ⋆ R) ml') →
                      Jna (na', ()) ml' := fun na' ml' h =>
                    hJna (na', ()) ml' (by m3_let; exact hJil_step has_false na' ml' h)
                  clear hc; m3_split_fast
                  · have hfs_tmp := focus_full_tmp hml; clear hml
                    generalize hR_tmp : FullTmpRest c (wsState st repri tmpl) ⋆ R = R_tmp at hfs_tmp
                    have hi32 : i32.bytes = 4 := rfl; m3_steps; subst hR_tmp
                    dsimp only [wsState] at hm; rw [bv_zext32_toNat, hr_eq] at hm
                    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ws_tag0_il_push_inv' htl_l hna_le hil_lt
                      (Nat.le_trans har_cv hcv0_le) hraw_len htail_l hsub_l hnohf_l
                    exact hJna_step (na + 1#32) m
                      ⟨tmpl.set na.toNat (raw[il.toNat]'(by rw [hraw_len]; exact hil_lt)),
                       h1, hna1 ▸ hil1 ▸ h2, hil1 ▸ h3, hil1 ▸ h4, hna1 ▸ h5, hhf_l,
                       hil1 ▸ hna1 ▸ h6, ws_unfocus_tmp hm⟩
                  · have hr_gd : raw[il.toNat]?.getD 0#32 = raw[il.toNat]'hil_raw := by
                      rw [List.getElem?_eq_getElem hil_raw, Option.getD_some]
                    have h1_val : st.core.vals[(raw[il.toNat]?.getD 0#32).toNat]?.getD 0#8 =
                        1#8 := by
                      rw [hr_gd]
                      exact vals_nslt0_ne0_eq1 hr_vals' _ hrv_dom (hrv_get ▸ hnslt_se)
                        (hrv_get ▸ hc)
                    m3_steps; exact hJna_step na ml
                      ⟨tmpl, htl_l, by omega, by omega,
                       fun j hj1 hj2 => htail_l j (by omega) hj2, hsub_l, hhf_l,
                       hil1 ▸ ws_tag0_il_true_inv h1_val hnohf_l, hml⟩
              · have hil_eq : il.toNat = arity.toNat := by
                  have hnot : ¬ il.toNat < arity.toNat := by
                    rw [hst_g1] at hc; simpa [arity] using bv32_ult_not_lt hc
                  omega
                rw [hil_eq] at hna_le htail_l hnohf_l; clear hc
                m3_to_group; refine wp_unroll_group fun Jt0 hJt0 => ?_
                have hJg0 : ∀ ch' har' nh' mj, WsP lhs har' nh' mj →
                    Jt0 (ch', har', nh', ()) mj := fun ch' har' nh' mj h =>
                  hJt0 (ch', har', nh', ()) mj
                    (by m3_let; exact hJgfin (ch', lhs, _, har', nh', ()) mj h)
                m3_split_fast
                · obtain ⟨k, hk, hff⟩ := hhf_l hc
                  obtain ⟨x, hx_mem, hx_eqv⟩ := hrhs_of_raw k hk
                  have hun_ent := andFold_has_false_entails hokl.2.1 hcl_t hand0 hlhs_eqv0
                    ⟨x, hx_mem, (raw[k]?.getD 0#32).toNat,
                     by change _ < 2 * st.core.cur_vars; rw [hcv_t]; exact hraw_lt k hk,
                     hx_eqv, hff⟩
                  m3_steps; m3_call hUnit
                  refine ws32_unit_xor1 hokl hlhs_lt hun_ent hml
                    fun uf su mu hoku _ hu2 hmu => ?_
                  m5_after_fold hQ hu2 changed work hoku mu hmu ch' =>
                    rw [hst_g1]; exact hJg0 ch' _ false mu (wsPost_false hoku hmu)
                · m3_to_group
                  refine wp_unroll_group (ts := [.bool, i32, .bool]) fun Jt0b hJt0b => ?_
                  have hJg0b : ∀ ch' har' nh' mj, WsP lhs har' nh' mj →
                      Jt0b (ch', har', nh', ()) mj := fun ch' har' nh' mj h =>
                    hJt0b (ch', har', nh', ()) mj (by m3_let; exact hJg0 ch' har' nh' mj h)
                  m3_split_fast
                  · have hna0 : na.toNat = 0 := by rw [beq_iff_eq.mp hc]; rfl
                    have hun_ent := ws_tag0_all_true_entails hokl.2.1 hcl_t hand0 hlhs_eqv0
                      (fun m hm => hokl.2.2.2.2.2.2.2.1 ▸ hraw_lt m hm) hraw_of_rhs
                      (hna0 ▸ hnohf_l (by assumption))
                    m3_steps; m3_call hUnit
                    refine ws32_unit_call hokl hlhs_lt hun_ent hml fun uf su mu hoku _ hu2 hmu => ?_
                    m5_after_fold hQ hu2 changed work hoku mu hmu ch' =>
                      rw [hst_g1]; exact hJg0b ch' _ false mu (wsPost_false hoku hmu)
                  · have hhf_f : has_false = false := by assumption
                    have hna_pos : 0 < na.toNat := by
                      have hne : na ≠ 0#32 := beq_eq_false_iff_ne.mp hc
                      rcases Nat.eq_zero_or_pos na.toNat with hz | hp
                      · exact absurd (BitVec.eq_of_toNat_eq hz) hne
                      · exact hp
                    have hfwd_l := ws_tag0_hf_false_fwd F_cur hraw_lt hraw_of_rhs (hnohf_l hhf_f)
                    m3_to_group
                    refine wp_join_group (ts := [])
                      (fun () ms => ∃ tmps : List (BitVec 32),
                        tmps.length = c.max_vars ∧
                        (∀ j < na.toNat, ∃ k < arity.toNat, tmps[j]? = raw[k]?) ∧
                        (∀ x ∈ rhs, ∃ r < 2 * cv0, LitEquiv (cnfOfClauses F_cur) x r ∧
                          (st.core.vals[r]?.getD 0#8 = 1#8 ∨
                            ∃ j < na.toNat, (tmps[j]?.getD 0#32).toNat = r)) ∧
                        (FullMem c (wsState st repri tmps) ⋆ R) ms)
                      ?_ ?_
                    · rintro _ ⟨⟩ ms ⟨tmps, htl_s, hsub_s, hfwd_s, hms⟩
                      m3_to_group
                      refine wp_loop_break_group (brkTs := [.bool, i32, i32])
                        (lpTs := [i32, i32])
                        (fun (clash, ua, _si, ()) md => ∃ tmpd : List (BitVec 32),
                          tmpd.length = c.max_vars ∧ ua.toNat ≤ na.toNat ∧
                          (∀ j < ua.toNat, ∃ k < na.toNat, tmpd[j]? = tmps[k]?) ∧
                          (clash = true →
                            (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg lhs.toNat])) ∧
                          (clash = false → 0 < ua.toNat ∧
                            ∀ j < na.toNat, ∃ q < ua.toNat,
                              (tmpd[q]?.getD 0#32) = tmps[j]?.getD 0#32) ∧
                          (FullMem c (wsState st repri tmpd) ⋆ R) md)
                        (fun remd (ua, si, ()) md => ∃ tmpd : List (BitVec 32),
                          tmpd.length = c.max_vars ∧ ua.toNat ≤ si.toNat ∧ si.toNat ≤ na.toNat ∧
                          remd = na.toNat - si.toNat ∧
                          (0 < si.toNat → 0 < ua.toNat) ∧
                          (∀ j, si.toNat ≤ j → j < na.toNat → tmpd[j]? = tmps[j]?) ∧
                          (∀ j < ua.toNat, ∃ k < na.toNat, tmpd[j]? = tmps[k]?) ∧
                          (∀ j < si.toNat, ∃ q < ua.toNat,
                            (tmpd[q]?.getD 0#32) = tmps[j]?.getD 0#32) ∧
                          (FullMem c (wsState st repri tmpd) ⋆ R) md)
                        ?_ ?_ ?_
                      · rintro _ ⟨clash, ua, _si, ⟨⟩⟩ md
                          ⟨tmpd, htl_d, hua_le, hsub_tmps, hcl_d, huf_d, hmd⟩
                        have hokd := workStepOk32_wsState hok_t hrli htl_d hrepri
                        obtain ⟨hsub_d, hsub_raw_d⟩ := ws_tag0_sub_raw_d hsub_tmps hsub_s
                          hrhs_of_raw (by omega) hraw_len
                        m3_to_group
                        refine wp_unroll_group (ts := [.bool, i32, .bool]) fun Jt0c hJt0c => ?_
                        have hJg0c : ∀ ch' har' nh' mj, WsP lhs har' nh' mj →
                            Jt0c (ch', har', nh', ()) mj := fun ch' har' nh' mj h =>
                          hJt0c (ch', har', nh', ()) mj (by m3_let; exact hJg0b ch' har' nh' mj h)
                        m3_split_fast
                        · have hun_ent := hcl_d hc
                          m3_steps; m3_call hUnit
                          refine ws32_unit_xor1 hokd hlhs_lt hun_ent hmd
                            fun uf su mu hoku _ hu2 hmu => ?_
                          m5_after_fold hQ hu2 changed work hoku mu hmu ch' =>
                            rw [hst_g1]; exact hJg0c ch' _ false mu (wsPost_false hoku hmu)
                        · obtain ⟨hua_pos, hcov_d⟩ := huf_d hc; clear hc; m3_to_group
                          refine wp_unroll_group (ts := [.bool, i32, .bool]) fun Jt0d hJt0d => ?_
                          have hJg0d : ∀ ch' har' nh' mj, WsP lhs har' nh' mj →
                              Jt0d (ch', har', nh', ()) mj := fun ch' har' nh' mj h =>
                            hJt0d (ch', har', nh', ()) mj (by m3_let; exact hJg0c ch' har' nh' mj h)
                          m3_split_fast
                          · have hua0 : ua.toNat = 0 := by rw [beq_iff_eq.mp hc]; rfl
                            omega
                          · have hev_d := ws_tag0_dedup_eval hokd.2.1 hcl_t hcv_t (by omega) hand0
                              hlhs_eqv0 hfwd_s hcov_d hsub_raw_d
                            m3_to_group
                            refine wp_unroll_group (ts := [.bool, i32, .bool]) fun Jt0e hJt0e => ?_
                            have hJg0e : ∀ ch' har' nh' mj, WsP lhs har' nh' mj →
                                Jt0e (ch', har', nh', ()) mj := fun ch' har' nh' mj h =>
                              hJt0e (ch', har', nh', ()) mj
                                (by m3_let; exact hJg0d ch' har' nh' mj h)
                            m3_split_fast
                            · have hua1 : ua.toNat = 1 := by rw [beq_iff_eq.mp hc]; rfl
                              obtain ⟨ht0_lt, ht0_eqv⟩ := ws_tag0_ua1_equiv (by omega) hraw_len
                                (hsub_d 0 (by omega)) hraw_lt (hua1 ▸ hev_d)
                              have h0_tmp : (0#64 : BitVec 64).toNat < tmpd.length := by
                                change 0 < tmpd.length; omega
                              m3_steps; m3_call hEquiv
                              refine ws32_equiv_call hokd hlhs_lt ht0_lt ht0_eqv hmd
                                fun ef se me hoke _ hef2 hme => ?_
                              m5_after_fold hQ hef2 changed work hoke me hme ch' =>
                                exact hJg0e ch' _ false me (wsPost_false hoke hme)
                            · have hua_ge2 : 2 ≤ ua.toNat := by
                                have hne := beq_eq_false_iff_ne.mp hc
                                have : ua.toNat ≠ 1 := fun h => hne (BitVec.eq_of_toNat_eq h); omega
                              have hlhs_vals : (lhs.setWidth 64).toNat < st.core.vals.length := by
                                rw [bv_zext32_toNat, hvlen_t]; omega
                              have hua_cv : ua.toNat ≤ cv0 := by omega
                              have hua_31 : ua.toNat ≤ 31 := by
                                change arity.toNat ≤ 31 at har_31; omega
                              m3_to_group
                              refine wp_unroll_group (ts := [.bool, i32, .bool])
                                fun Jt0f hJt0f => ?_
                              have hJg0f : ∀ ch' har' nh' mj, WsP lhs har' nh' mj →
                                  Jt0f (ch', har', nh', ()) mj := fun ch' har' nh' mj h =>
                                hJt0f (ch', har', nh', ()) mj
                                  (by m3_let; exact hJg0e ch' har' nh' mj h)
                              m3_split_fast
                              · -- `vals[lhs] > 0`: propagate all `tmp[k]`, set `need_hash = false`
                                have hv1 : st.core.vals[lhs.toNat]?.getD 0#8 = 1#8 :=
                                  vals_sgt0_eq1 (by rw [hvlen_t]; omega) hlhs_vals
                                    (hokd.2.1.vals_domain lhs.toNat
                                      (hokd.2.2.2.2.2.2.2.1 ▸ hlhs_lt))
                                    hc
                                have hents := ws_tag0_lhs_true_ents hokd.2.1 hokd.2.2.2.2.2.1
                                  (hokd.2.2.2.2.2.2.2.1 ▸ hlhs_lt) hv1 hev_d
                                m3_to_group; refine wp_loop_inv
                                  (fun (ch_k, k, ()) mk => ∃ stk : FullState,
                                    k.toNat ≤ ua.toNat ∧
                                    WorkStepOk32 c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat
                                      ht_off.toNat ht_sz.toNat scr0 stk ∧
                                    stk.core.tmp = tmpd ∧ (FullMem c stk ⋆ R) mk)
                                  (fun (_, k, ()) _ => ua.toNat - k.toNat)
                                  (fun Jk hJk => by
                                    m3_steps; exact hJk (changed, 0#32, ()) md
                                      ⟨wsState st repri tmpd, Nat.zero_le _, hokd, rfl, hmd⟩)
                                  (fun Jk (ch_k, k, ()) mk
                                    ⟨stk, hk_le, hokk, htmp_k, hmk⟩ ihk => ?_)
                                m3_split_fast
                                · have hk_lt : k.toNat < ua.toNat := bv32_ult_lt hc
                                  have hk_tmp : (k.setWidth 64).toNat < stk.core.tmp.length := by
                                    rw [bv_zext32_toNat, htmp_k]; omega
                                  have hk1 : (k + 1#32).toNat = k.toNat + 1 :=
                                    bv32_add1_toNat (n := ua.toNat) (by omega) (by omega)
                                  obtain ⟨htk_lt, htk_ent⟩ := ws_tag0_unit_k_args htmp_k hk_lt
                                    hraw_len (by omega) hsub_d hraw_lt hents hk_tmp
                                  m3_steps; m3_call hUnit
                                  refine ws32_unit_call hokk htk_lt htk_ent hmk
                                    fun uf su mu hoku htmpu hu2 hmu => ?_
                                  m5_after_fold hQ hu2 ch_k work hoku mu hmu ch_u =>
                                    exact ihk (ch_u, k + 1#32, ()) mu (by dsimp only; omega)
                                      ⟨su, by omega, hoku, htmpu.trans htmp_k, hmu⟩
                                · m3_steps; exact hJg0f ch_k _ false mk (wsPost_false hokk hmk)
                              · -- `vals[lhs] <= 0`: set `harity = ua`, keep `need_hash = true`
                                m3_steps
                                exact hJg0f changed ua true md ⟨wsState st repri tmpd, hokd,
                                  fun _ => ⟨hlhs_lt, hua_cv,
                                    fun _ => ⟨hua_ge2, hua_31, fun α hα => hev_d α hα⟩,
                                    fun h => (by rw [htag0] at h; cases h),
                                    fun h => (by rw [htag0] at h; cases h)⟩, hmd⟩
                      · rintro Bd Ld remd ⟨ua, si, ⟨⟩⟩ md hBd hLd
                          ⟨tmpd, htl_d, hua_le, hsi_le, rfl, hua_pos_if, htail_d,
                           hsub_tmps, hcov_d, hmd⟩
                        m3_split_fast
                        · have hsi_lt : si.toNat < na.toNat := bv32_ult_lt hc
                          have hna_max : na.toNat ≤ c.max_vars :=
                            Nat.le_trans hna_le (Nat.le_trans har_cv hcv0_le)
                          have hsi_tmp : (si.setWidth 64).toNat < tmpd.length := by
                            rw [bv_zext32_toNat]; omega
                          have hsi_tl : si.toNat < tmpd.length := by omega
                          have hsi_ts : si.toNat < tmps.length := by omega
                          let cur := tmps[si.toNat]'hsi_ts
                          have hcur_eq : tmpd[(si.setWidth 64).toNat]'hsi_tmp = cur :=
                            (list_getElem_zext32_eq rfl hsi_tmp hsi_tl).trans
                              (list_getElem_eq_of_eqD hsi_tl
                                ((htail_d si.toNat (Nat.le_refl _) hsi_lt).trans
                                  (List.getElem?_eq_getElem hsi_ts)))
                          have hsi1 : (si + 1#32).toNat = si.toNat + 1 :=
                            bv32_add1_toNat (by omega) (by omega)
                          have hua1 : (ua + 1#32).toNat = ua.toNat + 1 :=
                            bv32_add1_toNat (n := na.toNat) (by omega) (by omega)
                          clear hc; m3_split_fast
                          · -- NEW: `cur == (lhs ^ 1u)` -> `clash = true; break;`
                            have hcur_nlhs : cur = lhs ^^^ 1#32 := hcur_eq ▸ beq_iff_eq.mp hc
                            have hcl_nlhs := ws_tag0_nlhs_clash_entails hand0 hlhs_eqv0 hsi_lt
                              hsi_ts hraw_len hsub_s hrhs_of_raw hcur_nlhs
                            m3_steps
                            exact hBd (true, ua, si + 1#32, ()) md
                              ⟨tmpd, htl_d, by omega, hsub_tmps, fun _ => hcl_nlhs,
                               (fun h => by cases h), hmd⟩
                          · clear hc; m3_to_group
                            refine wp_unroll_group (ts := [.bool, i32]) fun Jua hJua => ?_
                            have hJua_step : ∀ (b' : Bool) (ua' : BitVec 32) (md' : Mem 64),
                                (∃ tmpd' : List (BitVec 32),
                                  tmpd'.length = c.max_vars ∧
                                  ua'.toNat ≤ (si + 1#32).toNat ∧ (si + 1#32).toNat ≤ na.toNat ∧
                                  (0 < (si + 1#32).toNat → 0 < ua'.toNat) ∧
                                  (∀ j, (si + 1#32).toNat ≤ j → j < na.toNat →
                                    tmpd'[j]? = tmps[j]?) ∧
                                  (∀ j < ua'.toNat, ∃ k < na.toNat, tmpd'[j]? = tmps[k]?) ∧
                                  (∀ j < (si + 1#32).toNat, ∃ q < ua'.toNat,
                                    (tmpd'[q]?.getD 0#32) = tmps[j]?.getD 0#32) ∧
                                  (FullMem c (wsState st repri tmpd') ⋆ R) md') →
                                Jua (b', ua', ()) md' :=
                              fun b' ua' md' ⟨t', ht', hu', hs', hp', htl', hs_t', hc', hm'⟩ =>
                                hJua (b', ua', ()) md' (by
                                  m3_let; exact hLd (na.toNat - (si + 1#32).toNat)
                                    (ua', si + 1#32, ()) md' (by omega)
                                    ⟨t', ht', hu', hs', rfl, hp', htl', hs_t', hc', hm'⟩)
                            m3_split_fast
                            · have hua0 : ua.toNat = 0 := by rw [beq_iff_eq.mp hc]; rfl
                              have hsi0 : si.toNat = 0 :=
                                Nat.eq_zero_of_not_pos fun h => by have := hua_pos_if h; omega
                              have h0_tmp : (0#64 : BitVec 64).toNat < tmpd.length := by
                                change 0 < tmpd.length; omega
                              have hfs_tmp := focus_full_tmp hmd; clear hmd
                              generalize hR_tmp : FullTmpRest c (wsState st repri tmpd) ⋆ R =
                                R_tmp at hfs_tmp
                              have hi32 : i32.bytes = 4 := rfl; m3_steps; subst hR_tmp
                              dsimp only [wsState] at hm; rw [hcur_eq] at hm
                              obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ws_tag0_dedup_first_inv hsi0
                                htl_d hsi_lt (by omega) htail_d (by omega)
                              exact hJua_step _ 1#32 m ⟨tmpd.set 0 cur, h1,
                                (by rw [hsi1]; have h1 : (1#32).toNat = 1 := rfl; omega),
                                hsi1 ▸ h3, hsi1 ▸ h4,
                                hsi1 ▸ h5, h6, hsi1 ▸ h7, ws_unfocus_tmp hm⟩
                            · have hua_pos : 0 < ua.toNat := by
                                have hne : ua ≠ 0#32 := beq_eq_false_iff_ne.mp hc
                                rcases Nat.eq_zero_or_pos ua.toNat with hz | hp
                                · exact absurd (BitVec.eq_of_toNat_eq hz) hne
                                · exact hp
                              have hum1_n : ((ua - 1#32).setWidth 64).toNat = ua.toNat - 1 := by
                                rw [bv_zext32_toNat, bv32_sub1_toNat hua_pos]
                              have hum1_tmp : ((ua - 1#32).setWidth 64).toNat < tmpd.length := by
                                rw [hum1_n]; omega
                              let prev := tmpd[((ua - 1#32).setWidth 64).toNat]'hum1_tmp
                              have hprev_eq : prev = tmpd[ua.toNat - 1]'(by omega) :=
                                list_getElem_congr hum1_n hum1_tmp (by omega)
                              m3_split_fast
                              · have hcur_prev : cur = tmpd[ua.toNat - 1]'(by omega) :=
                                  (hcur_eq ▸ beq_iff_eq.mp hc).trans hprev_eq
                                obtain ⟨h1, h2, h3, h4, h5⟩ := ws_tag0_dedup_dup_inv' (by omega)
                                  (by omega) hua_pos hua_le hsi_lt hcur_prev htail_d hcov_d
                                m3_steps; exact hLd (na.toNat - (si + 1#32).toNat)
                                  (ua, si + 1#32, ()) md (by omega)
                                  ⟨tmpd, htl_d, hsi1 ▸ h1, hsi1 ▸ h2, rfl, hsi1 ▸ h3, hsi1 ▸ h4,
                                   hsub_tmps, hsi1 ▸ h5, hmd⟩
                              · m3_split_fast
                                · have hcur_xor : cur = prev ^^^ 1#32 := hcur_eq ▸ beq_iff_eq.mp hc
                                  have hcl := ws_tag0_dedup_clash (by omega) (by omega) hua_pos
                                    hua_le hsi_lt hprev_eq hsub_tmps hcur_xor
                                  have hun_cl := ws_tag0_clash_entails hand0 hlhs_eqv0 hsub_s
                                    hrhs_of_raw hraw_len (by omega) hcl
                                  m3_steps; exact hBd (true, ua, si + 1#32, ()) md
                                    ⟨tmpd, htl_d, (by omega), hsub_tmps, fun _ => hun_cl,
                                     (fun h => by cases h), hmd⟩
                                · have hua_tmp : (ua.setWidth 64).toNat < tmpd.length := by
                                    rw [bv_zext32_toNat]; omega
                                  have hfs_tmp := focus_full_tmp hmd; clear hmd
                                  generalize hR_tmp : FullTmpRest c (wsState st repri tmpd) ⋆ R =
                                    R_tmp at hfs_tmp
                                  have hi32 : i32.bytes = 4 := rfl; m3_steps; subst hR_tmp
                                  dsimp only [wsState] at hm; rw [bv_zext32_toNat, hcur_eq] at hm
                                  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
                                    ws_tag0_dedup_push_inv htl_d
                                    (by omega) (by omega) hua_le hsi_lt htail_d hsub_tmps hcov_d
                                  exact hJua_step _ (ua + 1#32) m ⟨tmpd.set ua.toNat cur, h1,
                                    hua1 ▸ hsi1 ▸ h2, hsi1 ▸ h3, hua1 ▸ hsi1 ▸ h4, hsi1 ▸ h5,
                                    hua1 ▸ h6, hua1 ▸ hsi1 ▸ h7, ws_unfocus_tmp hm⟩
                        · have hsi_eq : si.toNat = na.toNat := by
                            have := bv32_ult_not_lt hc; omega
                          rw [hsi_eq] at hua_pos_if hcov_d
                          m3_steps; exact hBd (false, ua, si, ()) md
                            ⟨tmpd, htl_d, hsi_eq ▸ hua_le, hsub_tmps, (fun h => by cases h),
                             fun _ => ⟨hua_pos_if hna_pos, hcov_d⟩, hmd⟩
                      · intro _ Ld _ hLd; m3_steps
                        exact hLd na.toNat (0#32, 0#32, ()) ms
                          ⟨tmps, htl_s, Nat.zero_le _, Nat.zero_le _, rfl,
                           fun h => by simp at h, fun _ _ _ => rfl,
                           fun _ h => by simp at h, fun _ h => by simp at h, hms⟩
                    · intro Js hJs; m3_split_fast
                      · m3_steps; m3_call hSort
                        refine ⟨tmpl, FullTmpRest c (wsState st repri tmpl) ⋆ R, by omega,
                          focus_full_tmp hml, fun tmps ms htl_s hperm_s _ hms => ?_⟩
                        have hms' : (FullMem c (wsState st repri tmps) ⋆ R) ms :=
                          ws_unfocus_tmp hms
                        clear hms; m3_steps
                        obtain ⟨hsub_s, hfwd_s⟩ := ws_tag0_post_sort (htl_s.trans htl_l) htl_l
                          hna_le (Nat.le_trans har_cv hcv0_le) hperm_s hsub_l hfwd_l
                        exact hJs () ms ⟨tmps, htl_s.trans htl_l, hsub_s, hfwd_s, hms'⟩
                      · m3_steps; exact hJs () ml ⟨tmpl, htl_l, hsub_l, hfwd_l, hml⟩
            · -- Not `tag == 0u`: check `tag == 1u && arity == 2u`, else `tag == 2u && arity == 3u`
              have htag_ne0 : tag ≠ 0#32 := ws_tag_ne hst_g1 hc
              clear hc; m3_to_group
              refine wp_unroll_group (ts := [.bool, i32, .bool]) fun Jt1 hJt1 => ?_
              have hJg1 : ∀ ch' lhs' nh' mj, WsP lhs' arity nh' mj →
                  Jt1 (ch', lhs', nh', ()) mj := fun ch' lhs' nh' mj h =>
                hJt1 (ch', lhs', nh', ()) mj
                  (by m3_let; rw [hst_g1]; exact hJgfin (ch', lhs', _, arity, nh', ()) mj h)
              m3_to_group
              refine wp_join_group (ts := []) (fun () mj => tag ≠ 1#32 ∧ mj = mi) ?_ ?_
              · rintro _ ⟨⟩ mj ⟨htag_ne1, rfl⟩
                m3_to_group
                refine wp_unroll_group (ts := [.bool, i32, .bool]) fun Jt2b hJt2b => ?_
                have hJg2b : ∀ ch' lhs' nh' mj, WsP lhs' arity nh' mj →
                    Jt2b (ch', lhs', nh', ()) mj := fun ch' lhs' nh' mj h =>
                  hJt2b (ch', lhs', nh', ()) mj (by m3_let; exact hJg1 ch' lhs' nh' mj h)
                m3_split_fast
                · have htag2 : tag = 2#32 := ws_tag_eq hst_g1 hc
                  m3_split_fast
                  · have har3 : arity = 3#32 := ws_har_eq hst_g1 hc
                    have har3_n : arity.toNat = 3 := by rw [har3]; decide
                    have hite0 := ws_tag2_ite_def htag2 hsem0
                    have ht_ge3 : 3 ≤ tmpi.length := by omega
                    have h0_tmp : (0#64 : BitVec 64).toNat <
                        (wsState st repri tmpi).core.tmp.length := by
                      change 0 < tmpi.length; omega
                    have h1_tmp : (1#64 : BitVec 64).toNat <
                        (wsState st repri tmpi).core.tmp.length := by
                      change 1 < tmpi.length; omega
                    have h2_tmp : (2#64 : BitVec 64).toNat <
                        (wsState st repri tmpi).core.tmp.length := by
                      change 2 < tmpi.length; omega
                    let cl := tmpi[0]'(by omega); let tl := tmpi[1]'(by omega)
                    let el := tmpi[2]'(by omega)
                    have hcl_lt : cl.toNat < 2 * cv0 := (htmp_i' 0 (by omega)).1
                    have htl_lt : tl.toNat < 2 * cv0 := (htmp_i' 1 (by omega)).1
                    have hel_lt : el.toNat < 2 * cv0 := (htmp_i' 2 (by omega)).1
                    have hcl_vl : cl.toNat < st.core.vals.length := by
                      rw [hvlen_t]; exact Nat.lt_of_lt_of_le hcl_lt (Nat.mul_le_mul_left 2 hcv0_le)
                    have htl_vl : tl.toNat < st.core.vals.length := by
                      rw [hvlen_t]; exact Nat.lt_of_lt_of_le htl_lt (Nat.mul_le_mul_left 2 hcv0_le)
                    have hel_vl : el.toNat < st.core.vals.length := by
                      rw [hvlen_t]; exact Nat.lt_of_lt_of_le hel_lt (Nat.mul_le_mul_left 2 hcv0_le)
                    have hcl_vals : (cl.setWidth 64).toNat < st.core.vals.length := by
                      rw [bv_zext32_toNat]; exact hcl_vl
                    have htl_vals : (tl.setWidth 64).toNat < st.core.vals.length := by
                      rw [bv_zext32_toNat]; exact htl_vl
                    have hel_vals : (el.setWidth 64).toNat < st.core.vals.length := by
                      rw [bv_zext32_toNat]; exact hel_vl
                    have hvc_dom := hoki.2.1.vals_domain cl.toNat
                      (hoki.2.2.2.2.2.2.2.1 ▸ hcl_lt)
                    have hvt_dom := hoki.2.1.vals_domain tl.toNat
                      (hoki.2.2.2.2.2.2.2.1 ▸ htl_lt)
                    have hve_dom := hoki.2.1.vals_domain el.toNat
                      (hoki.2.2.2.2.2.2.2.1 ▸ hel_lt)
                    have hite_t : IteGateDef (cnfOfClauses F_cur) lhs.toNat
                        cl.toNat tl.toNat el.toNat :=
                      ite_eval_congr hite0 hlhs_eqv0 (htmp_i' 0 (by omega)).2
                        (htmp_i' 1 (by omega)).2 (htmp_i' 2 (by omega)).2
                    clear hFind hSort hMatch
                    clear hc; m3_to_group
                    refine wp_unroll_group (ts := [.bool, i32, .bool, i32, i32, i32])
                      fun Jt2c hJt2c => ?_
                    have hJg2c : ∀ ch' lhs' nh' c' t' e' mj, WsP lhs' arity nh' mj →
                        Jt2c (ch', lhs', nh', c', t', e', ()) mj :=
                      fun ch' lhs' nh' c' t' e' mj h =>
                        hJt2c (ch', lhs', nh', c', t', e', ()) mj
                          (by m3_let; exact hJg2b ch' lhs' nh' mj h)
                    m3_split_fast
                    · have hvc_ne := vals_ne0_1_or_ff hcl_vl hcl_vals hvc_dom hc
                      have heqc := ite_cond_const_equiv hoki.2.1 hoki.2.2.2.2.2.1 hite_t
                        (hoki.2.2.2.2.2.2.2.1 ▸ hcl_lt) hvc_ne
                      dsimp only [wsState] at heqc
                      m3_to_group; refine wp_join_group (ts := [i32])
                        (fun (br, ()) mbr => mbr = mj ∧ br.toNat < 2 * cv0 ∧
                          LitEquiv (cnfOfClauses F_cur) lhs.toNat br.toNat)
                        (fun _ ⟨br, ⟨⟩⟩ mbr ⟨hmbr, hbr_lt, heqv_br⟩ => by
                          subst mbr; m3_steps; m3_call hEquiv
                          refine ws32_equiv_call hoki hlhs_lt hbr_lt heqv_br hmi
                            fun ef se me hoke _ hef2 hme => ?_
                          m5_after_fold hQ hef2 changed work hoke me hme ch' =>
                            exact hJg2c ch' lhs false _ _ _ me (wsPost_false hoke hme))
                        ?_
                      intro Jbr hJbr; m3_split_fast
                      · have hvc1 := vals_sgt0_eq1 hcl_vl hcl_vals hvc_dom hc
                        m3_let; exact hJbr (tl, ()) mj
                          ⟨rfl, htl_lt, by simpa [hvc1, bv_zext32_toNat] using heqc⟩
                      · have hvcff := vals_ne0_nsgt0_eqff hcl_vl hcl_vals hvc_dom hvc_ne hc
                        m3_let; exact hJbr (el, ()) mj
                          ⟨rfl, hel_lt, by simpa [hvcff, bv_zext32_toNat] using heqc⟩
                    · clear hc; m3_to_group
                      refine wp_unroll_group (ts := [.bool, i32, .bool, i32, i32, i32])
                        fun Jt2d hJt2d => ?_
                      have hJg2d : ∀ ch' lhs' nh' c' t' e' mj', WsP lhs' arity nh' mj' →
                          Jt2d (ch', lhs', nh', c', t', e', ()) mj' :=
                        fun ch' lhs' nh' c' t' e' mj' h =>
                          hJt2d (ch', lhs', nh', c', t', e', ()) mj'
                            (by m3_let; exact hJg2c ch' lhs' nh' c' t' e' mj' h)
                      m3_split_fast
                      · have hte : tl = el := beq_iff_eq.mp hc
                        have heqt : LitEquiv (cnfOfClauses F_cur) lhs.toNat tl.toNat :=
                          ite_equal_branches_equiv hite_t (LitEquiv.refl _ _)
                            (LitEquiv.refl _ _) (by rw [hte]; exact LitEquiv.refl _ _)
                        m3_steps; m3_call hEquiv
                        refine ws32_equiv_call hoki hlhs_lt htl_lt heqt hmi
                          fun ef se me hoke _ hef2 hme => ?_
                        m5_after_fold hQ hef2 changed work hoke me hme ch' =>
                          exact hJg2d ch' lhs false _ _ _ me (wsPost_false hoke hme)
                      · clear hc; m3_to_group
                        refine wp_unroll_group (ts := [.bool, i32, .bool, i32, i32, i32])
                          fun Jt2e hJt2e => ?_
                        have hJg2e : ∀ ch' lhs' nh' c' t' e' mj', WsP lhs' arity nh' mj' →
                            Jt2e (ch', lhs', nh', c', t', e', ()) mj' :=
                          fun ch' lhs' nh' c' t' e' mj' h =>
                            hJt2e (ch', lhs', nh', c', t', e', ()) mj'
                              (by m3_let; exact hJg2d ch' lhs' nh' c' t' e' mj' h)
                        m3_to_group; refine wp_join_group (ts := []) (fun _ mf => mf = mj) ?_ ?_
                        · rintro _ ⟨⟩ mf hmf; subst mf; m3_to_group
                          refine wp_unroll_group (ts := [.bool, i32, .bool, i32, i32, i32])
                            fun Jt2f hJt2f => ?_
                          have hJg2f : ∀ ch' lhs' nh' c' t' e' mj', WsP lhs' arity nh' mj' →
                              Jt2f (ch', lhs', nh', c', t', e', ()) mj' :=
                            fun ch' lhs' nh' c' t' e' mj' h =>
                              hJt2f (ch', lhs', nh', c', t', e', ()) mj'
                                (by m3_let; exact hJg2e ch' lhs' nh' c' t' e' mj' h)
                          m3_to_group; refine wp_join_group (ts := []) (fun _ mf => mf = mj)
                            ?_ ?_
                          · rintro _ ⟨⟩ mf hmf; subst mf; m3_to_group
                            refine wp_unroll_group (ts := [.bool, i32, .bool, i32, i32, i32])
                              fun Jt2g hJt2g => ?_
                            have hJg2g : ∀ ch' lhs' nh' c' t' e' mj', WsP lhs' arity nh' mj' →
                                Jt2g (ch', lhs', nh', c', t', e', ()) mj' :=
                              fun ch' lhs' nh' c' t' e' mj' h =>
                                hJt2g (ch', lhs', nh', c', t', e', ()) mj'
                                  (by m3_let; exact hJg2f ch' lhs' nh' c' t' e' mj' h)
                            m3_to_group; refine wp_join_group (ts := []) (fun _ mf => mf = mj)
                              ?_ ?_
                            · rintro _ ⟨⟩ mf hmf; subst mf; m3_to_group
                              refine wp_unroll_group (ts := [.bool, i32, .bool, i32, i32, i32])
                                fun Jt2h hJt2h => ?_
                              have hJg2h : ∀ ch' lhs' nh' c' t' e' mj', WsP lhs' arity nh' mj' →
                                  Jt2h (ch', lhs', nh', c', t', e', ()) mj' :=
                                fun ch' lhs' nh' c' t' e' mj' h =>
                                  hJt2h (ch', lhs', nh', c', t', e', ()) mj'
                                    (by m3_let; exact hJg2g ch' lhs' nh' c' t' e' mj' h)
                              m3_to_group; refine wp_join_group (ts := []) (fun _ mf => mf = mj)
                                ?_ ?_
                              · -- NEW: ITE sign normalization (`c & 1` and `t & 1`) + store `tmp`
                                rintro _ ⟨⟩ mf hmf; subst mf; m3_to_group
                                refine wp_join_group (ts := [i32, i32, i32])
                                  (fun (c1, t1, e1, ()) m1 => m1 = mj ∧
                                    IteGateDef (cnfOfClauses F_cur) lhs.toNat
                                      c1.toNat t1.toNat e1.toNat)
                                  ?_ ?_
                                · rintro _ ⟨c1, t1, e1, ⟨⟩⟩ m1 ⟨hm1, hite1⟩; subst m1
                                  m3_to_group
                                  refine wp_join_group (ts := [i32, i32, i32])
                                    (fun (lhs1, t2, e2, ()) m2 => m2 = mj ∧
                                      lhs1.toNat < 2 * cv0 ∧
                                      IteGateDef (cnfOfClauses F_cur) lhs1.toNat
                                        c1.toNat t2.toNat e2.toNat)
                                    ?_ ?_
                                  · rintro _ ⟨lhs1, t2, e2, ⟨⟩⟩ m2 ⟨hm2, hlhs1_lt, hite2⟩; subst m2
                                    have hfs_tmp := focus_full_tmp hmi; clear hmi
                                    dsimp only [wsState] at hfs_tmp
                                    generalize hR_tmp : FullTmpRest c (wsState st repri tmpi) ⋆ R =
                                      R_tmp at hfs_tmp
                                    have ht1_len : 1 < tmpi.length := by omega
                                    have ht2_len : 2 < tmpi.length := by omega
                                    have hi32 : i32.bytes = 4 := rfl; m3_steps; subst hR_tmp
                                    exact hJg2h changed lhs1 true _ _ _ m
                                      (ws_ite_norm_post hok_t hrli htli hrepri ht2_len hlhs1_lt
                                        har_cv' htag2 har3 hite2 hm)
                                  · intro Jf2 hJf2; m3_split_fast
                                    · m3_steps
                                      refine hJf2 (lhs ^^^ 1#32, t1 ^^^ 1#32, e1 ^^^ 1#32, ()) mj
                                        ⟨rfl, by rw [bv32_xor1_eq_litNeg]
                                                 exact bv32_xor1_lt_even hlhs_lt, ?_⟩
                                      simp only [bv32_xor1_eq_litNeg]
                                      exact iteGateDef_flip_out hite1
                                    · m3_let
                                      exact hJf2 (lhs, t1, e1, ()) mj ⟨rfl, hlhs_lt, hite1⟩
                                · intro Jf1 hJf1; m3_split_fast
                                  · m3_steps
                                    refine hJf1 (cl ^^^ 1#32, el, tl, ()) mj ⟨rfl, ?_⟩
                                    rw [bv32_xor1_eq_litNeg]; exact iteGateDef_flip_cond hite_t
                                  · m3_let; exact hJf1 (cl, tl, el, ()) mj ⟨rfl, hite_t⟩
                              · intro J4 hJ4; m3_split_fast
                                · have htff := vals_slt0_eqff htl_vl htl_vals hvt_dom hc
                                  clear hc; m3_split_fast
                                  · have hun := ite_branches_both_false_entails hoki.2.1
                                      hoki.2.2.2.2.2.1 hite_t (hoki.2.2.2.2.2.2.2.1 ▸ htl_lt)
                                      (hoki.2.2.2.2.2.2.2.1 ▸ hel_lt)
                                      (by simpa [wsState] using htff)
                                      (vals_slt0_eqff hel_vl hel_vals hve_dom hc)
                                    m3_steps; m3_call hUnit
                                    refine ws32_unit_xor1 hoki hlhs_lt hun hmi
                                      fun uf su mu hoku _ hu2 hmu => ?_
                                    m5_after_fold hQ hu2 changed work hoku mu hmu ch' =>
                                      exact hJg2h ch' lhs false _ _ _ mu (wsPost_false hoku hmu)
                                  · m3_let; exact hJ4 () mj rfl
                                · m3_let; exact hJ4 () mj rfl
                            · intro J3 hJ3; m3_split_fast
                              · have ht1 := vals_sgt0_eq1 htl_vl htl_vals hvt_dom hc
                                clear hc; m3_split_fast
                                · have hun := ite_branches_both_true_entails hoki.2.1
                                    hoki.2.2.2.2.2.1 hite_t (hoki.2.2.2.2.2.2.2.1 ▸ htl_lt)
                                    (hoki.2.2.2.2.2.2.2.1 ▸ hel_lt) (by simpa [wsState] using ht1)
                                    (vals_sgt0_eq1 hel_vl hel_vals hve_dom hc)
                                  m3_steps; m3_call hUnit
                                  refine ws32_unit_call hoki hlhs_lt hun hmi
                                    fun uf su mu hoku _ hu2 hmu => ?_
                                  m5_after_fold hQ hu2 changed work hoku mu hmu ch' =>
                                    exact hJg2g ch' lhs false _ _ _ mu (wsPost_false hoku hmu)
                                · m3_let; exact hJ3 () mj rfl
                              · m3_let; exact hJ3 () mj rfl
                          · intro J2 hJ2; m3_split_fast
                            · have htff := vals_slt0_eqff htl_vl htl_vals hvt_dom hc
                              clear hc; m3_split_fast
                              · have heqc := ite_branches_false_true_equiv hoki.2.1
                                  hoki.2.2.2.2.2.1 hite_t (hoki.2.2.2.2.2.2.2.1 ▸ htl_lt)
                                  (hoki.2.2.2.2.2.2.2.1 ▸ hel_lt) (by simpa [wsState] using htff)
                                  (vals_sgt0_eq1 hel_vl hel_vals hve_dom hc)
                                m3_steps; m3_call hEquiv
                                refine ws32_equiv_call hoki hlhs_lt
                                  (by change (cl ^^^ 1#32).toNat < 2 * cv0
                                      rw [bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even hcl_lt)
                                  (by change LitEquiv (cnfOfClauses F_cur) lhs.toNat
                                        (cl ^^^ 1#32).toNat
                                      rw [bv32_xor1_eq_litNeg]; exact heqc) hmi
                                  fun ef se me hoke _ hef2 hme => ?_
                                m5_after_fold hQ hef2 changed work hoke me hme ch' =>
                                  exact hJg2f ch' lhs false _ _ _ me (wsPost_false hoke hme)
                              · m3_let; exact hJ2 () mj rfl
                            · m3_let; exact hJ2 () mj rfl
                        · intro J1 hJ1; m3_split_fast
                          · have ht1 := vals_sgt0_eq1 htl_vl htl_vals hvt_dom hc
                            clear hc; m3_split_fast
                            · have heqc := ite_branches_true_false_equiv hoki.2.1
                                hoki.2.2.2.2.2.1 hite_t (hoki.2.2.2.2.2.2.2.1 ▸ htl_lt)
                                (hoki.2.2.2.2.2.2.2.1 ▸ hel_lt) (by simpa [wsState] using ht1)
                                (vals_slt0_eqff hel_vl hel_vals hve_dom hc)
                              m3_steps; m3_call hEquiv
                              refine ws32_equiv_call hoki hlhs_lt hcl_lt heqc hmi
                                fun ef se me hoke _ hef2 hme => ?_
                              m5_after_fold hQ hef2 changed work hoke me hme ch' =>
                                exact hJg2e ch' lhs false _ _ _ me (wsPost_false hoke hme)
                            · m3_let; exact hJ1 () mj rfl
                          · m3_let; exact hJ1 () mj rfl
                  · have hc_n : arity ≠ 3#32 := ws_har_ne hst_g1 hc
                    exfalso; rcases hsem0 with ⟨ht, _⟩ | ⟨ht, _⟩ | ⟨_, ha3, _⟩
                    · have : (mword >>> 28).toNat = 2 := by change tag.toNat = 2; rw [htag2]; decide
                      omega
                    · have : (mword >>> 28).toNat = 2 := by change tag.toNat = 2; rw [htag2]; decide
                      omega
                    · exact hc_n (BitVec.eq_of_toNat_eq ha3)
                · have htag_ne2 : tag ≠ 2#32 := ws_tag_ne hst_g1 hc
                  exfalso; rcases hsem0 with ⟨ht, _⟩ | ⟨ht, _⟩ | ⟨ht, _⟩
                  · apply htag_ne0; apply BitVec.eq_of_toNat_eq; simpa [tag] using ht
                  · apply htag_ne1; apply BitVec.eq_of_toNat_eq; simpa [tag] using ht
                  · apply htag_ne2; apply BitVec.eq_of_toNat_eq; simpa [tag] using ht
              · intro Jt1_2 hJt1_2
                m3_split_fast
                · have htag1 : tag = 1#32 := ws_tag_eq hst_g1 hc
                  m3_split_fast
                  · have har2 : arity = 2#32 := ws_har_eq hst_g1 hc
                    have har2_n : arity.toNat = 2 := by rw [har2]; decide
                    have hxor0 := ws_tag1_xor_def htag1 hsem0
                    have ht_ge2 : 2 ≤ tmpi.length := by omega
                    have h0_tmp : (0#64 : BitVec 64).toNat <
                        (wsState st repri tmpi).core.tmp.length := by
                      change 0 < tmpi.length; omega
                    have h1_tmp : (1#64 : BitVec 64).toNat <
                        (wsState st repri tmpi).core.tmp.length := by
                      change 1 < tmpi.length; omega
                    let t0 := tmpi[0]'(by omega); let t1 := tmpi[1]'(by omega)
                    have ht0_lt : t0.toNat < 2 * cv0 := (htmp_i' 0 (by omega)).1
                    have ht1_lt : t1.toNat < 2 * cv0 := (htmp_i' 1 (by omega)).1
                    have ht0_vl : t0.toNat < st.core.vals.length := by
                      rw [hvlen_t]; exact Nat.lt_of_lt_of_le ht0_lt (Nat.mul_le_mul_left 2 hcv0_le)
                    have ht1_vl : t1.toNat < st.core.vals.length := by
                      rw [hvlen_t]; exact Nat.lt_of_lt_of_le ht1_lt (Nat.mul_le_mul_left 2 hcv0_le)
                    have hlhs_vl : lhs.toNat < st.core.vals.length := by
                      rw [hvlen_t]; exact Nat.lt_of_lt_of_le hlhs_lt (Nat.mul_le_mul_left 2 hcv0_le)
                    have ht0_vals : (t0.setWidth 64).toNat < st.core.vals.length := by
                      rw [bv_zext32_toNat]; exact ht0_vl
                    have ht1_vals : (t1.setWidth 64).toNat < st.core.vals.length := by
                      rw [bv_zext32_toNat]; exact ht1_vl
                    have hlhs_vals : (lhs.setWidth 64).toNat < st.core.vals.length := by
                      rw [bv_zext32_toNat]; exact hlhs_vl
                    have hv0_dom := hoki.2.1.vals_domain t0.toNat
                      (hoki.2.2.2.2.2.2.2.1 ▸ ht0_lt)
                    have hv1_dom := hoki.2.1.vals_domain t1.toNat
                      (hoki.2.2.2.2.2.2.2.1 ▸ ht1_lt)
                    have hvl_dom := hoki.2.1.vals_domain lhs.toNat
                      (hoki.2.2.2.2.2.2.2.1 ▸ hlhs_lt)
                    have ht0_eqv := (htmp_i' 0 (by omega)).2
                    have ht1_eqv := (htmp_i' 1 (by omega)).2
                    have hxor_t : XorGateDef (cnfOfClauses F_cur) lhs.toNat t0.toNat t1.toNat :=
                      xor_eval_congr hxor0 hlhs_eqv0 ht0_eqv ht1_eqv
                    clear hFind hSort hMatch
                    clear hc; m3_to_group
                    refine wp_unroll_group (ts := [.bool, i32, .bool, i32, i32])
                      fun Jt1c hJt1c => ?_
                    have hJg1c : ∀ ch' lhs' nh' t0' t1' mj, WsP lhs' arity nh' mj →
                        Jt1c (ch', lhs', nh', t0', t1', ()) mj :=
                      fun ch' lhs' nh' t0' t1' mj h =>
                        hJt1c (ch', lhs', nh', t0', t1', ()) mj
                          (by m3_let; exact hJg1 ch' lhs' nh' mj h)
                    m3_split_fast
                    · have hv0_ne := vals_ne0_1_or_ff ht0_vl ht0_vals hv0_dom hc
                      m3_to_group; refine wp_join_group (ts := [i32])
                        (fun (eq, ()) meq => meq = mi ∧ eq.toNat < 2 * cv0 ∧
                          LitEquiv (cnfOfClauses F_cur) lhs.toNat eq.toNat)
                        ?_ ?_
                      · rintro _ ⟨eq, ⟨⟩⟩ meq ⟨hmeq, heq_lt, heqv_eq⟩; subst meq
                        m3_steps; m3_call hEquiv
                        refine ws32_equiv_call hoki hlhs_lt heq_lt heqv_eq hmi
                          fun ef se me hoke _ hef2 hme => ?_
                        m5_after_fold hQ hef2 changed work hoke me hme ch' =>
                          exact hJg1c ch' lhs false _ _ me (wsPost_false hoke hme)
                      · intro Jeq hJeq
                        have heqc := xor_const_equiv hoki.2.1 hoki.2.2.2.2.2.1 hxor_t
                          (hoki.2.2.2.2.2.2.2.1 ▸ ht0_lt) hv0_ne
                        dsimp only [wsState] at heqc
                        m3_split_fast
                        · have hv0_1 := vals_sgt0_eq1 ht0_vl ht0_vals hv0_dom hc
                          m3_let; refine hJeq (t1 ^^^ 1#32, ()) mi ⟨rfl,
                            by change (t1 ^^^ 1#32).toNat < 2 * cv0; rw [bv32_xor1_eq_litNeg]
                               exact bv32_xor1_lt_even ht1_lt,
                            by change LitEquiv (cnfOfClauses F_cur) lhs.toNat (t1 ^^^ 1#32).toNat
                               rw [bv32_xor1_eq_litNeg]
                               simpa [hv0_1, bv_zext32_toNat] using heqc⟩
                        · have hv0_ff := vals_ne0_nsgt0_eqff ht0_vl ht0_vals hv0_dom hv0_ne hc
                          m3_let; refine hJeq (t1, ()) mi
                            ⟨rfl, ht1_lt, by simpa [hv0_ff, bv_zext32_toNat] using heqc⟩
                    · clear hc; m3_to_group
                      refine wp_unroll_group (ts := [.bool, i32, .bool, i32, i32])
                        fun Jt1d hJt1d => ?_
                      have hJg1d : ∀ ch' lhs' nh' t0' t1' mj, WsP lhs' arity nh' mj →
                          Jt1d (ch', lhs', nh', t0', t1', ()) mj :=
                        fun ch' lhs' nh' t0' t1' mj h =>
                          hJt1d (ch', lhs', nh', t0', t1', ()) mj
                            (by m3_let; exact hJg1c ch' lhs' nh' t0' t1' mj h)
                      m3_split_fast
                      · have hv1_ne := vals_ne0_1_or_ff ht1_vl ht1_vals hv1_dom hc
                        m3_to_group; refine wp_join_group (ts := [i32])
                          (fun (eq, ()) meq => meq = mi ∧ eq.toNat < 2 * cv0 ∧
                            LitEquiv (cnfOfClauses F_cur) lhs.toNat eq.toNat)
                          ?_ ?_
                        · rintro _ ⟨eq, ⟨⟩⟩ meq ⟨hmeq, heq_lt, heqv_eq⟩; subst meq
                          m3_steps; m3_call hEquiv
                          refine ws32_equiv_call hoki hlhs_lt heq_lt heqv_eq hmi
                            fun ef se me hoke _ hef2 hme => ?_
                          m5_after_fold hQ hef2 changed work hoke me hme ch' =>
                            exact hJg1d ch' lhs false _ _ me (wsPost_false hoke hme)
                        · intro Jeq hJeq
                          have heqc := xor_const_equiv hoki.2.1 hoki.2.2.2.2.2.1
                            (xorGateDef_comm hxor_t) (hoki.2.2.2.2.2.2.2.1 ▸ ht1_lt) hv1_ne
                          dsimp only [wsState] at heqc
                          m3_split_fast
                          · have hv1_1 := vals_sgt0_eq1 ht1_vl ht1_vals hv1_dom hc
                            m3_let; refine hJeq (t0 ^^^ 1#32, ()) mi ⟨rfl,
                              by change (t0 ^^^ 1#32).toNat < 2 * cv0; rw [bv32_xor1_eq_litNeg]
                                 exact bv32_xor1_lt_even ht0_lt,
                              by change LitEquiv (cnfOfClauses F_cur) lhs.toNat (t0 ^^^ 1#32).toNat
                                 rw [bv32_xor1_eq_litNeg]
                                 simpa [hv1_1, bv_zext32_toNat] using heqc⟩
                          · have hv1_ff := vals_ne0_nsgt0_eqff ht1_vl ht1_vals hv1_dom hv1_ne hc
                            m3_let; refine hJeq (t0, ()) mi
                              ⟨rfl, ht0_lt, by simpa [hv1_ff, bv_zext32_toNat] using heqc⟩
                      · clear hc; m3_to_group
                        refine wp_unroll_group (ts := [.bool, i32, .bool, i32, i32])
                          fun Jt1e hJt1e => ?_
                        have hJg1e : ∀ ch' lhs' nh' t0' t1' mj, WsP lhs' arity nh' mj →
                            Jt1e (ch', lhs', nh', t0', t1', ()) mj :=
                          fun ch' lhs' nh' t0' t1' mj h =>
                            hJt1e (ch', lhs', nh', t0', t1', ()) mj
                              (by m3_let; exact hJg1d ch' lhs' nh' t0' t1' mj h)
                        m3_split_fast
                        · obtain ⟨hul_lt, hul_ent⟩ := ws_tag1_same_var_unit_args hxor0 hlhs_eqv0
                            ht0_eqv ht1_eqv hlhs_lt (bv32_shr1_eq_div2 hc)
                          clear hc; m3_to_group; refine wp_join_group (ts := [i32])
                            (fun (ul, ()) mu => mu = mi ∧ ul.toNat < 2 * cv0 ∧
                              (cnfOfClauses F_cur).EntailsClause (cnfClause [ul.toNat]))
                            ?_ ?_
                          · rintro _ ⟨ul, ⟨⟩⟩ mu ⟨hmu, hul_lt', hul_ent'⟩; subst mu
                            m3_steps; m3_call hUnit
                            refine ws32_unit_call hoki hul_lt' hul_ent' hmi
                              fun uf su mu hoku _ hu2 hmu => ?_
                            m5_after_fold hQ hu2 changed work hoku mu hmu ch' =>
                              exact hJg1e ch' lhs false _ _ mu (wsPost_false hoku hmu)
                          · intro Jul hJul; m3_split_fast
                            · have hc' : tmpi[0]'(by omega) = tmpi[1]'(by omega) :=
                                beq_iff_eq.mp hc
                              rw [ite_eq_left hc'] at hul_lt hul_ent
                              m3_let; exact hJul (lhs ^^^ 1#32, ()) mi ⟨rfl, hul_lt, hul_ent⟩
                            · have hc' : tmpi[0]'(by omega) ≠ tmpi[1]'(by omega) :=
                                beq_eq_false_iff_ne.mp hc
                              rw [ite_eq_right hc'] at hul_lt hul_ent
                              m3_let; exact hJul (lhs, ()) mi ⟨rfl, hul_lt, hul_ent⟩
                        · clear hc; m3_to_group
                          refine wp_unroll_group (ts := [.bool, i32, .bool, i32, i32])
                            fun Jt1f hJt1f => ?_
                          have hJg1f : ∀ ch' lhs' nh' t0' t1' mj, WsP lhs' arity nh' mj →
                              Jt1f (ch', lhs', nh', t0', t1', ()) mj :=
                            fun ch' lhs' nh' t0' t1' mj h =>
                              hJt1f (ch', lhs', nh', t0', t1', ()) mj
                                (by m3_let; exact hJg1e ch' lhs' nh' t0' t1' mj h)
                          m3_split_fast
                          · -- NEW: `vals[lhs] != 0` -> `equiv_fold(eq0, t1)`, `need_hash = false`
                            have hvl_ne := vals_ne0_1_or_ff hlhs_vl hlhs_vals hvl_dom hc
                            m3_to_group; refine wp_join_group (ts := [i32])
                              (fun (eq0, ()) meq => meq = mi ∧ eq0.toNat < 2 * cv0 ∧
                                LitEquiv (cnfOfClauses F_cur) eq0.toNat t1.toNat)
                              ?_ ?_
                            · rintro _ ⟨eq0, ⟨⟩⟩ meq ⟨hmeq, heq_lt, heqv_eq⟩; subst meq
                              m3_steps; m3_call hEquiv
                              refine ws32_equiv_call hoki heq_lt ht1_lt heqv_eq hmi
                                fun ef se me hoke _ hef2 hme => ?_
                              m5_after_fold hQ hef2 changed work hoke me hme ch' =>
                                exact hJg1f ch' lhs false _ _ me (wsPost_false hoke hme)
                            · intro Jeq hJeq
                              have heqc := xor_lhs_const_equiv hoki.2.1 hoki.2.2.2.2.2.1 hxor_t
                                (hoki.2.2.2.2.2.2.2.1 ▸ hlhs_lt) hvl_ne
                              dsimp only [wsState] at heqc
                              m3_split_fast
                              · have hvl1 := vals_sgt0_eq1 hlhs_vl hlhs_vals hvl_dom hc
                                m3_let; refine hJeq (t0 ^^^ 1#32, ()) mi ⟨rfl,
                                  by change (t0 ^^^ 1#32).toNat < 2 * cv0; rw [bv32_xor1_eq_litNeg]
                                     exact bv32_xor1_lt_even ht0_lt,
                                  by change LitEquiv (cnfOfClauses F_cur) (t0 ^^^ 1#32).toNat
                                       t1.toNat
                                     rw [bv32_xor1_eq_litNeg]
                                     simpa [hvl1, bv_zext32_toNat] using heqc⟩
                              · have hvlff := vals_ne0_nsgt0_eqff hlhs_vl hlhs_vals hvl_dom
                                  hvl_ne hc
                                m3_let; refine hJeq (t0, ()) mi
                                  ⟨rfl, ht0_lt, by simpa [hvlff, bv_zext32_toNat] using heqc⟩
                          · -- NEW: strip RHS signs onto `lhs`, sort `t0, t1`, store `tmp[0..1]`
                            clear hc
                            have hstrip := xor_sign_strip_sound hlhs_lt ht0_lt ht1_lt hxor_t
                            let lhs1 := lhs ^^^ ((t0 ^^^ t1) &&& 1#32)
                            let r0 := t0 &&& ~~~1#32
                            let r1 := t1 &&& ~~~1#32
                            m3_to_group
                            refine wp_join_group (ts := [i32, i32])
                              (fun (a0, a1, ()) msw => msw = mi ∧
                                XorGateDef (cnfOfClauses F_cur) lhs1.toNat a0.toNat a1.toNat)
                              ?_ ?_
                            · rintro _ ⟨a0, a1, ⟨⟩⟩ msw ⟨hmsw, hxor_s⟩; subst msw
                              have hfs_tmp := focus_full_tmp hmi; clear hmi
                              dsimp only [wsState] at hfs_tmp
                              generalize hR_tmp : FullTmpRest c (wsState st repri tmpi) ⋆ R =
                                R_tmp at hfs_tmp
                              have ht1_len : 1 < tmpi.length := by omega
                              have hi32 : i32.bytes = 4 := rfl; m3_steps; subst hR_tmp
                              exact hJg1f changed lhs1 true _ _ m
                                (ws_xor_strip_post hok_t hrli htli hrepri ht1_len hstrip.1
                                  har_cv' htag1 har2 hxor_s hm)
                            · intro Jsw hJsw; m3_split_fast
                              · m3_steps; exact hJsw (r1, r0, ()) mi ⟨rfl, hstrip.2.2.2.2⟩
                              · m3_let; exact hJsw (r0, r1, ()) mi ⟨rfl, hstrip.2.2.2.1⟩
                  · have hc_n : arity ≠ 2#32 := ws_har_ne hst_g1 hc
                    exfalso; rcases hsem0 with ⟨ht, _⟩ | ⟨_, ha2, _⟩ | ⟨ht, _⟩
                    · have : (mword >>> 28).toNat = 1 := by change tag.toNat = 1; rw [htag1]; decide
                      omega
                    · exact hc_n (BitVec.eq_of_toNat_eq ha2)
                    · have : (mword >>> 28).toNat = 1 := by change tag.toNat = 1; rw [htag1]; decide
                      omega
                · have htag_ne1 : tag ≠ 1#32 := ws_tag_ne hst_g1 hc
                  m3_let; exact hJt1_2 () mi ⟨htag_ne1, rfl⟩
    · m3_steps
      exact hJex mg ⟨st, ⟨hlen_t, hw_t, hmk_t, hnd_t, hext_t, hcl_t, hdm_t,
        hcv_t, hfl_t, har_t, hal_t, hrepr_t, hpref_t, hht_t⟩, hmg⟩
  · m3_steps
    exact hJex mg ⟨st, ⟨hlen_t, hw_t, hmk_t, hnd_t, hext_t, hcl_t, hdm_t,
      hcv_t, hfl_t, har_t, hal_t, hrepr_t, hpref_t, hht_t⟩, hmg⟩

end WorkStepProof

/-! ## 2. Closed `15`-Row `m5CongFixModule` Soundness, Dense Composition & Concrete `Mem 64` NV -/

section ModuleAndNV

/-- Closed `15`-row specification table for `m5CongFixModule` (`7` fns ++ `8` externs). -/
def m5CongFixSpecTable : List SpecEntry :=
  [ ⟨"full_cong_merge", [i64, i32, i32], [.bool], fullCongMergeSpec, true⟩
  , ⟨"full_cong_extract_ite", [i64, i32, i32, i32, i64], [i64], m5CongExtractIteSpec, true⟩
  , ⟨"full_cong_emit_xor", [i64, i64, i32, i32, i32], [i64], m5CongEmitXorSpec, true⟩
  , ⟨"full_cong_try_xor_ite", [i64, i32, i32, i32, i64, i64], [i64], m5CongTryXorIteSpec, true⟩
  , ⟨"full_cong_extract", [i64, i64, i64], [i64], m5CongExtractSpec, true⟩
  , ⟨"full_cong_and_match", [i64, i32, i32], [.bool], m5CongAndMatchSpec, true⟩
  , ⟨"full_cong_work_step", [i64, i64, i64, i64, i32], [i64], m5CongWorkStepSpec, true⟩
  , ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  , ⟨"full_has_bin", [i64, i32, i32], [.bool], fullHasBinSpec, true⟩
  , ⟨"full_add_bin", [i64, i32, i32], [i64], FullCongSpecs.fullAddBinSpec, true⟩
  , ⟨"full_has_ternary", [i64, i32, i32, i32], [.bool], fullHasTernarySpec, true⟩
  , ⟨"full_sort_u32", [i64, i32], [], fullSortU32Spec, true⟩
  , ⟨"full_cong_find", [i64, i32], [i32], fullCongFindSpec, true⟩
  , ⟨"full_cong_unit_fold", [i64, i32, i32], [i64], m3CongUnitFoldSpec, true⟩
  , ⟨"full_cong_equiv_fold", [i64, i32, i32, i32], [i64], m3CongEquivFoldSpec, true⟩ ]

def m5CongFixEnv : Env := Env.ofTable m5CongFixSpecTable

theorem m5CongFixSpecTable_sigs :
    m5CongFixSpecTable.map (fun e => (e.name, e.as, e.rs)) = m5CongFixModule.sigs := by
  t_kernel_rfl

theorem m5CongFixSpecTable_noExit :
    ∀ e ∈ m5CongFixSpecTable, e.noExit = true := by
  intro e he
  simp only [m5CongFixSpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> rfl

theorem m5CongFixSpecTable_nodup :
    (m5CongFixSpecTable.map SpecEntry.name).Nodup := by
  have hchk := m5CongFix_acyclic
  simp only [m5CongFixModule, Module.checkAcyclic, Bool.and_eq_true] at hchk
  have hnd := Module.namesNodup_of_checkNamesNodup hchk.1
  have hnames : m5CongFixSpecTable.map SpecEntry.name = m5CongFixModule.names := by
    have hm := congrArg (List.map Prod.fst) m5CongFixSpecTable_sigs
    simpa only [List.map_map, Function.comp_def, Module.sigs, Module.names, Fn.sig, Extern.sig,
      List.map_append] using hm
  rw [hnames]; exact hnd

private theorem m5FixEnv_row (i : Nat) (e : SpecEntry)
    (hi : m5CongFixSpecTable[i]? = some e := by rfl)
    (hno : ∀ xs m Q X, e.spec xs m Q X → e.eff xs m Q X := by intro _ _ _ _ h; exact h) :
    ∀ xs m Q X, e.spec xs m Q X → m5CongFixEnv e.name e.as e.rs xs m Q X :=
  fun xs m Q X h =>
    Env.ofTable_of_mem (List.mem_of_getElem? hi) m5CongFixSpecTable_nodup (hno xs m Q X h)

private theorem m5Fix_allFns_of_forall {P : Fn → Prop} :
    ∀ {fs : List Fn}, (∀ f ∈ fs, P f) → AllFns P fs
  | [], _ => trivial
  | _ :: _, h =>
    ⟨h _ List.mem_cons_self, m5Fix_allFns_of_forall fun f hf => h f (List.mem_cons_of_mem _ hf)⟩

theorem m5CongFix_tableImpl :
    TableImpl m5CongFixEnv m5CongFixModule.fns m5CongFixSpecTable := by
  have r1 := m5FixEnv_row 1
    ⟨"full_cong_extract_ite", [i64, i32, i32, i32, i64], [i64], m5CongExtractIteSpec, true⟩
  have r2 := m5FixEnv_row 2
    ⟨"full_cong_emit_xor", [i64, i64, i32, i32, i32], [i64], m5CongEmitXorSpec, true⟩
  have r3 := m5FixEnv_row 3
    ⟨"full_cong_try_xor_ite", [i64, i32, i32, i32, i64, i64], [i64], m5CongTryXorIteSpec, true⟩
  have r5 := m5FixEnv_row 5
    ⟨"full_cong_and_match", [i64, i32, i32], [.bool], m5CongAndMatchSpec, true⟩
  have r7 := m5FixEnv_row 7 ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩
  have r8 := m5FixEnv_row 8 ⟨"full_has_bin", [i64, i32, i32], [.bool], fullHasBinSpec, true⟩
  have r9 := m5FixEnv_row 9
    ⟨"full_add_bin", [i64, i32, i32], [i64], FullCongSpecs.fullAddBinSpec, true⟩
  have r10 := m5FixEnv_row 10
    ⟨"full_has_ternary", [i64, i32, i32, i32], [.bool], fullHasTernarySpec, true⟩
  have r11 := m5FixEnv_row 11 ⟨"full_sort_u32", [i64, i32], [], fullSortU32Spec, true⟩
  have r12 := m5FixEnv_row 12 ⟨"full_cong_find", [i64, i32], [i32], fullCongFindSpec, true⟩
  have r13 := m5FixEnv_row 13
    ⟨"full_cong_unit_fold", [i64, i32, i32], [i64], m3CongUnitFoldSpec, true⟩
  have r14 := m5FixEnv_row 14
    ⟨"full_cong_equiv_fold", [i64, i32, i32, i32], [i64], m3CongEquivFoldSpec, true⟩
  exact ⟨
    .of (m5_cong_merge_wp m5CongFixEnv r12 r9),
    .of (m5_cong_extract_ite_wp m5CongFixEnv r10),
    .of (m5_cong_emit_xor_wp m5CongFixEnv),
    .of (m5_cong_try_xor_ite_wp m5CongFixEnv r10 r2 r1),
    .of (m5_cong_extract_wp m5CongFixEnv r7 r8 r3),
    .of (m5_cong_and_match_wp m5CongFixEnv r12),
    .of (m5_cong_work_step_wp m5CongFixEnv r12 r11 r13 r14 r5),
    trivial⟩

theorem m5CongFix_moduleOk : ModuleOk m5CongFixEnv m5CongFixModule :=
  Env.ofTable_moduleOk m5CongFix_acyclic (m5Fix_allFns_of_forall m5CongFix_fns_wf)
    m5CongFix_tableImpl

/-- Direct composition (`PR-W1E` ready): `FullM5CongBins.full_congruence_dense` calling
`FullM5CongFix`'s widened `full_cong_extract` + `full_cong_work_step` satisfies exact canonical
`FullM3CongBva.m3CongruenceDenseSpec`. -/
theorem m5_congruence_dense_fix_wp (Γ : Env)
    (hExtractBins : ∀ a m Q X, m5CongExtractBinariesSpec a m Q X →
      Γ "full_cong_extract_binaries" [i64] [i64] a m Q X)
    (hExtract : ∀ a m Q X, m5CongExtractSpec a m Q X →
      Γ "full_cong_extract" [i64, i64, i64] [i64] a m Q X)
    (hWork : ∀ a m Q X, m5CongWorkStepSpec a m Q X →
      Γ "full_cong_work_step" [i64, i64, i64, i64, i32] [i64] a m Q X) :
    ∀ a m Q X, m3CongruenceDenseSpec a m Q X →
      Func.wp Γ FullM5CongBins.full_congruence_dense_body a m Q X :=
  FullM5CongBins.m5_congruence_dense_wp_gen GateSeqOk32 CongHtInv32
    (fun _ _ _ _ _ _ _ hinit k hk => Or.inl (hinit k hk)) Γ hExtractBins hExtract hWork

/-- Weakening of `m5_congruence_dense_fix_wp` to `FullDefSweep.fullCongruenceDenseSpec`. -/
theorem m5_defsweep_congruence_dense_fix_wp (Γ : Env)
    (hExtractBins : ∀ a m Q X, m5CongExtractBinariesSpec a m Q X →
      Γ "full_cong_extract_binaries" [i64] [i64] a m Q X)
    (hExtract : ∀ a m Q X, m5CongExtractSpec a m Q X →
      Γ "full_cong_extract" [i64, i64, i64] [i64] a m Q X)
    (hWork : ∀ a m Q X, m5CongWorkStepSpec a m Q X →
      Γ "full_cong_work_step" [i64, i64, i64, i64, i32] [i64] a m Q X) :
    ∀ a m Q X, FullDefSweep.fullCongruenceDenseSpec a m Q X →
      Func.wp Γ FullM5CongBins.full_congruence_dense_body a m Q X := by
  rintro ⟨h, tick_lim, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hden, hm, hQ⟩
  exact m5_congruence_dense_fix_wp Γ hExtractBins hExtract hWork
    (c.hdr, tick_lim, ()) m0 Q X ⟨c, F0, s, R, rfl, hden, hm,
      fun r s' m' hd _ hf hr hu hm' => hQ r s' m' hd hf hr hu hm'⟩

/-- Concrete `FullState` derived from `FullDefSweep.nvDefSweepState` with HT slot `0` cleared to
`0xFFFFFFFF#32` (`CongHtInv32` empty sentinel). -/
def nvCongFixState : FullState :=
  { FullDefSweep.nvDefSweepState with scratch :=
    { FullDefSweep.nvDefSweepState.scratch with
      scratch_buf := FullDefSweep.nvDefSweepScratchBuf.set 0 0xFFFFFFFF#32 } }

/-- Concrete `Mem 64` carrying `FullMem FullDefSweep.nvDefSweepCfg nvCongFixState`. -/
def nvCongFixMem : Mem 64 :=
  storeMem FullDefSweep.nvDefSweepMem i32
    (FullDefSweep.nvDefSweepCfg.pScratchBuf + 0#64) 0xFFFFFFFF#32

theorem nvCongFix_lengths : nvCongFixState.LengthsOk FullDefSweep.nvDefSweepCfg :=
  ⟨FullDefSweep.nvDefSweepState_lengths.core_ok,
   { FullDefSweep.nvDefSweepState_lengths.scratch_ok with
     scratch_buf_len := by
       show (FullDefSweep.nvDefSweepScratchBuf.set 0 0xFFFFFFFF#32).length = 10240
       rw [List.length_set, FullDefSweep.nvDefSweepScratchBuf_length] }⟩

open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics in
theorem nvCongFixMem_ok : FullMem FullDefSweep.nvDefSweepCfg nvCongFixState nvCongFixMem := by
  have h0 : (FullMem FullDefSweep.nvDefSweepCfg FullDefSweep.nvDefSweepState ⋆ emp)
      FullDefSweep.nvDefSweepMem := by
    rw [sep_emp]; exact FullDefSweep.nvDefSweepMem_ok
  have h1 := (FullArenaTactics.store_full_scratch_buf (i := 0) (v := 0xFFFFFFFF#32)
    (by show 0 < FullDefSweep.nvDefSweepScratchBuf.length
        rw [FullDefSweep.nvDefSweepScratchBuf_length]; omega) h0).2
  rw [sep_emp] at h1; exact h1

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_cong_extract` under closed
`m5CongFixEnv` (`FullDefSweep.nvDefSweepCfg`, `nvDefSweepState`, `nvDefSweepMem`). -/
theorem m5_cong_extract_nv :
    Func.wp m5CongFixEnv full_cong_extract_body
      (FullDefSweep.nvDefSweepCfg.hdr, 128#64, 1024#64, ()) FullDefSweep.nvDefSweepMem
      (fun (ret, ()) m' => ∃ scr' : List (BitVec 32),
        scr'.length = FullDefSweep.nvDefSweepCfg.scratch_cap ∧ ret.toNat ≤ 128 ∧
        GateSeqOk32 [[0], [1]] 1 scr' ret.toNat 0 ∧
        FullMem FullDefSweep.nvDefSweepCfg { FullDefSweep.nvDefSweepState with scratch :=
          { FullDefSweep.nvDefSweepState.scratch with scratch_buf := scr' } } m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem FullDefSweep.nvDefSweepCfg FullDefSweep.nvDefSweepState ⋆ emp)
      FullDefSweep.nvDefSweepMem := by
    rw [sep_emp]; exact FullDefSweep.nvDefSweepMem_ok
  exact m5_cong_extract_wp m5CongFixEnv
    (m5FixEnv_row 7 ⟨"full_arena_next", [i64, i32], [i32], fullArenaNextSpec, true⟩)
    (m5FixEnv_row 8 ⟨"full_has_bin", [i64, i32, i32], [.bool], fullHasBinSpec, true⟩)
    (m5FixEnv_row 3
      ⟨"full_cong_try_xor_ite", [i64, i32, i32, i32, i64, i64], [i64], m5CongTryXorIteSpec, true⟩)
    _ FullDefSweep.nvDefSweepMem _ _ ⟨FullDefSweep.nvDefSweepCfg, nvOneLitF0, [[0], [1]],
      FullDefSweep.nvDefSweepState, emp, rfl, FullDefSweep.nvDefSweepState_lengths,
      FullDefSweep.nvDefSweep_invW.2.1, FullDefSweep.nvDefSweep_invW.2.2.2.1, rfl,
      by decide, hm, fun ret scr' m' hlen hle hseq hm' =>
        ⟨scr', hlen, hle, hseq, by rwa [sep_emp] at hm'⟩⟩

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) for `full_cong_work_step` under closed
`m5CongFixEnv` (`FullDefSweep.nvDefSweepCfg`, `nvCongFixState`, `nvCongFixMem`). -/
theorem m5_cong_work_step_nv :
    Func.wp m5CongFixEnv full_cong_work_step_body
      (FullDefSweep.nvDefSweepCfg.hdr, 0#64, 0#64, 1#64, 1#32, ()) nvCongFixMem
      (fun (r, ()) m' => ∃ s' : FullState,
        FullDenseInv FullDefSweep.nvDefSweepCfg nvOneLitF0 s' ∧
        s'.core.cur_vars = 1 ∧ s'.core.fuel = 1#64 ∧
        ((r &&& 3#64) = 0#64 ∨ (r &&& 3#64) = 1#64 ∨ (r &&& 3#64) = 2#64) ∧
        ((r &&& 3#64) = 2#64 → nvOneLitF0.Unsat) ∧
        FullMem FullDefSweep.nvDefSweepCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem FullDefSweep.nvDefSweepCfg nvCongFixState ⋆ emp) nvCongFixMem := by
    rw [sep_emp]; exact nvCongFixMem_ok
  have hrepr : FullCongReprInv [[0], [1]] (2 * nvCongFixState.core.cur_vars)
      nvCongFixState.core.repr := by
    refine ⟨⟨by decide, fun l hl => ?_⟩, fun l _ => ?_⟩
    · have hcv : nvCongFixState.core.cur_vars = 1 := rfl
      rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> decide
    · exact litEquiv_of_eval_eq fun α hα =>
        False.elim (CNF.unsat_iff_not_sat.mp FullDefSweep.nvDefSweepF0_unsat α hα)
  have hht : CongHtInv32 [[0], [1]] nvCongFixState.core.cur_vars
      nvCongFixState.scratch.scratch_buf nvCongFixState.scratch.scratch_buf 0 0 1 := by
    intro k hk; obtain rfl : k = 0 := by omega
    left
    show (FullDefSweep.nvDefSweepScratchBuf.set 0 0xFFFFFFFF#32)[0]?.getD 0xFFFFFFFF#32 =
      0xFFFFFFFF#32
    rw [List.getElem?_set_self (by rw [FullDefSweep.nvDefSweepScratchBuf_length]; omega),
      Option.getD_some]
  exact m5_cong_work_step_wp m5CongFixEnv
    (m5FixEnv_row 12 ⟨"full_cong_find", [i64, i32], [i32], fullCongFindSpec, true⟩)
    (m5FixEnv_row 11 ⟨"full_sort_u32", [i64, i32], [], fullSortU32Spec, true⟩)
    (m5FixEnv_row 13 ⟨"full_cong_unit_fold", [i64, i32, i32], [i64], m3CongUnitFoldSpec, true⟩)
    (m5FixEnv_row 14
      ⟨"full_cong_equiv_fold", [i64, i32, i32, i32], [i64], m3CongEquivFoldSpec, true⟩)
    (m5FixEnv_row 5 ⟨"full_cong_and_match", [i64, i32, i32], [.bool], m5CongAndMatchSpec, true⟩)
    _ nvCongFixMem _ _ ⟨FullDefSweep.nvDefSweepCfg, nvOneLitF0, [[0], [1]], nvCongFixState,
      nvCongFixState.scratch.scratch_buf, emp, rfl, nvCongFix_lengths,
      FullDefSweep.nvDefSweep_invW.2.1, FullDefSweep.nvDefSweep_invW.2.2.1,
      FullDefSweep.nvDefSweep_invW.2.2.2.1, FullDefSweep.nvDefSweep_invW.2.2.2.2.1, rfl,
      by decide, hrepr, by decide, by decide, by decide, .done, fun _ _ => rfl, hht, hm,
      fun r s' m' hlen' hw' hmk' hnd' hext' hcl' hdm' hcv' hfu' _ _ _ _ _ hdom huns hm' =>
        ⟨s', ⟨⟨hlen', [[0], [1]], hw'⟩, hmk', hnd', hext', hcl', hdm'⟩, hcv', hfu', hdom, huns,
         by rwa [sep_emp] at hm'⟩⟩

end ModuleAndNV

end LeanQbe.T.Examples.Kissat.FullM5CongFix
