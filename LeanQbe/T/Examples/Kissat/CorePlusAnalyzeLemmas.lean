module

public import LeanQbe.T.Examples.Kissat.CorePlusAnalyzeLemmas1
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Core+` 1UIP Conflict Analysis `Func.wp` Proof (`Stage 2`, Part 2)

Builds on `CorePlusAnalyzeLemmas1` to verify `kissat_analyze` against `corePlusAnalyzeSpec`
(parameterized over `Γ` contracts for `kissat_analyze_clause`, `kissat_clear_marks`,
`kissat_bump_var`, `kissat_bump_decay`, `kissat_minimize_clause`, `kissat_tick_reluctant`,
`kissat_backtrack`, `kissat_add_clause`, and `kissat_assign`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.CorePlus

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Local `C0Step` helpers for `kissat_analyze` -/

attribute [local bv_c0] bv32_lshr_1

private theorem bv8_sext32_eq_zero (b : BitVec 8) : b.signExtend 32 = 0#32 ↔ b = 0#8 :=
  ⟨fun h => BitVec.eq_of_toInt_eq (by
      have h1 := congrArg BitVec.toInt h
      rw [BitVec.toInt_signExtend, BitVec.toInt_zero] at h1
      have h2 := b.le_toInt; have h3 := b.toInt_lt
      simp only [BitVec.toInt_zero, show min 32 8 = 8 from rfl, Int.bmod] at h1 ⊢
      split at h1 <;> omega),
   fun h => by subst h; rfl⟩

attribute [local bv_c0] Bool.true_eq_false Bool.false_eq_true

private theorem ofNat64_pos {n : Nat} (h : ¬ BitVec.ofNat 64 n = 0#64) : 0 < n := by
  cases n with
  | zero => exact absurd rfl h
  | succ _ => omega

private theorem ofNat64_eq_zero {n : Nat} (hn : n < 2 ^ 64)
    (h : BitVec.ofNat 64 n = 0#64) : n = 0 := by
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] using congrArg BitVec.toNat h

private theorem ofNat64_eq_one {n : Nat} (hn : n < 2 ^ 64)
    (h : BitVec.ofNat 64 n = 1#64) : n = 1 := by
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] using congrArg BitVec.toNat h

private theorem lt_of_lt_mod64 {a b : Nat} (hb : b < 2 ^ 64) (h : a < b % 2 ^ 64) : a < b := by
  rwa [Nat.mod_eq_of_lt hb] at h

private theorem bv64_sub_one_toNat {n : Nat} (h1 : 0 < n) (h2 : n < 2 ^ 64) :
    (BitVec.ofNat 64 n - 1#64).toNat = n - 1 := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simp only [Nat.mod_eq_of_lt h2]; omega

private theorem bv64_sub1_raw {n : Nat} (h1 : 0 < n) (h2 : n < 2 ^ 64) :
    (2 ^ 64 - BitVec.toNat (1 : BitVec 64) + n) % 2 ^ 64 = n - 1 := by
  have : BitVec.toNat (1 : BitVec 64) = 1 := rfl; omega

private theorem lt64_of_le_mv {n mv : Nat} (h1 : n ≤ mv) (h2 : mv < 2 ^ 28) : n < 2 ^ 64 :=
  Nat.lt_of_le_of_lt h1 (Nat.lt_trans h2 (by decide))

private theorem lt32_of_le_mv {n mv : Nat} (h1 : n ≤ mv) (h2 : mv < 2 ^ 28) : n < 2 ^ 32 :=
  Nat.lt_of_le_of_lt h1 (Nat.lt_trans h2 (by decide))

private theorem lt64_of_bv32 (x : BitVec 32) : x.toNat < 2 ^ 64 :=
  Nat.lt_trans x.isLt (by decide)

private theorem bv64_add_one_toNat {x : BitVec 64} (h : x.toNat + 1 < 2 ^ 64) :
    (x + 1).toNat = x.toNat + 1 := by
  simp [BitVec.toNat_add, Nat.mod_eq_of_lt h]

private theorem bv64_setWidth32_toNat {n : Nat} (h : n < 2 ^ 32) :
    ((BitVec.ofNat 64 n).setWidth 32).toNat = n := by
  simp [Nat.mod_eq_of_lt h]

attribute [local bv_c0] bv8_zext32_eq0_prop

@[local bv_c0] private theorem bv8_sext32_eq0_prop (b : BitVec 8) :
    (b.signExtend 32 = 0#32) = (b = 0#8) :=
  propext (bv8_sext32_eq_zero b)

@[local c0_store] private theorem c0_store_tmp_0 {c : CorePlusCfg} {s : CorePlusState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.tmp.length)
    (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 0#64) ∧
      (CorePlusMem c { s with tmp := s.tmp.set 0 v } ⋆ R) (storeMem m i32 (c.pTmp + 0#64) v) :=
  store_arena_tmp (i := 0) v hi hm

@[local c0_load] private theorem c0_load_tmp_1 {c : CorePlusCfg} {s : CorePlusState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 1 < s.tmp.length) (hm : (CorePlusMem c s ⋆ R) m) :
    loadVal m i32 (c.pTmp + 4#64) = some (s.tmp[1]'hi) :=
  load_arena_tmp (i := 1) hi hm

@[local c0_store] private theorem c0_store_tmp_1 {c : CorePlusCfg} {s : CorePlusState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 1 < s.tmp.length)
    (hm : (CorePlusMem c s ⋆ R) m) :
    storeOk m i32 (c.pTmp + 4#64) ∧
      (CorePlusMem c { s with tmp := s.tmp.set 1 v } ⋆ R) (storeMem m i32 (c.pTmp + 4#64) v) :=
  store_arena_tmp (i := 1) v hi hm

private theorem take1_map_eq_singleton {xs : List (BitVec 32)} {x : BitVec 32}
    (h0 : xs[0]? = some x) : (xs.take 1).map BitVec.toNat = [x.toNat] := by
  cases xs with
  | nil => simp at h0
  | cons y ys => simp only [List.getElem?_cons_zero, Option.some.injEq] at h0; subst h0; rfl

/-- Fast variant of `cp_steps` that skips `c0_bound` refutation on live `jnz` branches. -/
local syntax "fast_steps" : tactic
local macro_rules
  | `(tactic| fast_steps) => do
    let hc := Lean.mkIdent `hc
    `(tactic| (
      try (first | refine strip_fwp ?_ | refine strip_wp ?_)
      repeat (any_goals (first
        | refine strip_le_wp (by decide) ?_
        | ((refine wp_jnz_of (fun $hc:ident => ?_) (fun $hc:ident => ?_)) <;> (
             try simp only [Arg.val_var, Arg.val_imm] at $hc:ident
             c0_cond $hc
             try (first | exact ($hc).elim | exact absurd rfl $hc | exact $hc rfl
                        | exact absurd trivial $hc)))
        | c0_step))))

/-! ## 2. Factored semantic & exit helpers for `kissat_analyze` -/

private theorem analyze_ret_ok {c : CorePlusCfg} {F0 : CNF Nat} {s s' : CorePlusState}
    {R : Mem 64 → Prop} {Q : Post [i64]} {m' : Mem 64}
    (hQ : ∀ (r : Val i64) vals' lvl' rsns' trl' te' prop' cl' tc' tl' mrk' tmp'
        wh' cls' wn' lpool' ll' nc' mstk' mclr' mcl' mcf' heur' m'',
      let st : CorePlusState :=
        { s with
          vals := vals', lvl := lvl', rsns := rsns', trl := trl',
          trail_end := te', propagated := prop', cur_level := cl',
          tmp_cnt := tc', tmp_len := tl', mrk := mrk', tmp := tmp',
          wh := wh', cls := cls', wn := wn', lpool := lpool', lit_len := ll',
          num_clauses := nc', min_stk := mstk', min_clr := mclr',
          min_clr_len := mcl', min_clr_full := mcf', heur := heur' }
      st.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) → (r = 1#64 → CorePlusInv c F0 st) →
      (CorePlusMem c st ⋆ R) m'' → Q (r, ()) m'')
    (r : Val i64) (hl : s'.LengthsOk c) (hr : r = 0#64 ∨ r = 1#64 ∨ r = 20#64)
    (hu : r = 20#64 → F0.Unsat) (hi : r = 1#64 → CorePlusInv c F0 s')
    (hm' : (CorePlusMem c s' ⋆ R) m')
    (h1 : s'.d_cur = s.d_cur) (h2 : s'.d_val = s.d_val)
    (h3 : s'.fuel = s.fuel) (h4 : s'.confl_cid = s.confl_cid) :
    Q (r, ()) m' := by
  have heq : s' = { s with
      vals := s'.vals, lvl := s'.lvl, rsns := s'.rsns, trl := s'.trl,
      trail_end := s'.trail_end, propagated := s'.propagated, cur_level := s'.cur_level,
      tmp_cnt := s'.tmp_cnt, tmp_len := s'.tmp_len, mrk := s'.mrk, tmp := s'.tmp,
      wh := s'.wh, cls := s'.cls, wn := s'.wn, lpool := s'.lpool, lit_len := s'.lit_len,
      num_clauses := s'.num_clauses, min_stk := s'.min_stk, min_clr := s'.min_clr,
      min_clr_len := s'.min_clr_len, min_clr_full := s'.min_clr_full, heur := s'.heur } := by
    cases s'; cases s; simp only at h1 h2 h3 h4; subst h1 h2 h3 h4; rfl
  exact hQ r _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m'
    (heq ▸ hl) hr hu (fun h => heq ▸ hi h) (heq ▸ hm')

private theorem analyze_fail_cm {Γ : Env} {c : CorePlusCfg} {F0 : CNF Nat}
    {s st : CorePlusState} {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost} {ml : Mem 64}
    (hCm : ∀ args m Q X, corePlusClearMarksSpec args m Q X →
      Γ "kissat_clear_marks" [i64, i64] [] args m Q X)
    (hQ : ∀ (r : Val i64) vals' lvl' rsns' trl' te' prop' cl' tc' tl' mrk' tmp'
        wh' cls' wn' lpool' ll' nc' mstk' mclr' mcl' mcf' heur' m'',
      let st : CorePlusState :=
        { s with
          vals := vals', lvl := lvl', rsns := rsns', trl := trl',
          trail_end := te', propagated := prop', cur_level := cl',
          tmp_cnt := tc', tmp_len := tl', mrk := mrk', tmp := tmp',
          wh := wh', cls := cls', wn := wn', lpool := lpool', lit_len := ll',
          num_clauses := nc', min_stk := mstk', min_clr := mclr',
          min_clr_len := mcl', min_clr_full := mcf', heur := heur' }
      st.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) → (r = 1#64 → CorePlusInv c F0 st) →
      (CorePlusMem c st ⋆ R) m'' → Q (r, ()) m'')
    (hstl : st.LengthsOk c) (htl_mv : st.tmp_len ≤ c.mv) (hml : (CorePlusMem c st ⋆ R) ml)
    (h1 : st.d_cur = s.d_cur) (h2 : st.d_val = s.d_val)
    (h3 : st.fuel = s.fuel) (h4 : st.confl_cid = s.confl_cid) :
    wp Γ Q X
      (Expr.call (rs := [i64]) (as := [i64, i64]) (bs := []) "kissat_clear_marks"
        (Arg.var c.hdr, Arg.imm 0#64, ())
        fun _ => Expr.ret (rs := [i64]) (Arg.imm 0#64, ())) ml := by
  c0_call hCm
  refine ⟨c, st, R, rfl, hstl, htl_mv, hml, fun mrk' m' hml' _ _ _ hm' => ?_⟩
  fast_steps
  exact analyze_ret_ok hQ 0#64 (s' := { st with mrk := mrk' }) { hstl with mrk_len := hml' }
    (Or.inl rfl) (fun h => by cases h) (fun h => by cases h) hm' h1 h2 h3 h4

private theorem analyze_init_sem {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    {confl_cid : BitVec 64} {mrk1 : List (BitVec 8)} {tmp1 : List (BitVec 32)} {tc1 tl1 : Nat}
    (hinv : CorePlusInv c F0 s) (hcid : confl_cid.toNat < s.num_clauses)
    (hfals : ∀ l ∈ clauseLits s confl_cid.toNat, s.vals[l]?.getD 0#8 = 0xFF#8)
    (ht1_len : tmp1.length = c.mv) (htl1_ge : 1 ≤ tl1) (htl1_le : tl1 ≤ c.mv)
    (hmp1 : ∀ v < c.mv, s.mrk[v]?.getD 0#8 ≠ 0#8 → mrk1[v]?.getD 0#8 = s.mrk[v]?.getD 0#8)
    (htp1 : ∀ k < 1, tmp1[k]? = s.tmp[k]?)
    (hnm1 : ∀ v < c.mv, s.mrk[v]?.getD 0#8 = 0#8 → mrk1[v]?.getD 0#8 ≠ 0#8 →
      ∃ l ∈ clauseLits s (confl_cid.setWidth 32).toNat, l / 2 = v ∧
        v ≠ (0xFFFFFFFF#32).toNat ∧
        0 < (s.lvl[v]?.getD 0#32).toNat ∧ (s.lvl[v]?.getD 0#32).toNat ≤ s.cur_level)
    (hnt1 : ∀ j, 1 ≤ j → j < tl1 →
      let l := (tmp1[j]?.getD 0#32).toNat
      l ∈ clauseLits s (confl_cid.setWidth 32).toNat ∧ l < 2 * c.mv ∧
      l / 2 ≠ (0xFFFFFFFF#32).toNat ∧
      0 < (s.lvl[l / 2]?.getD 0#32).toNat ∧ (s.lvl[l / 2]?.getD 0#32).toNat < s.cur_level ∧
      mrk1[l / 2]?.getD 0#8 ≠ 0#8)
    (hcnt1 : tc1 - 0 = ((List.range c.mv).filter fun v =>
      decide (s.mrk[v]?.getD 0#8 = 0#8) && decide (mrk1[v]?.getD 0#8 ≠ 0#8) &&
      decide ((s.lvl[v]?.getD 0#32).toNat = s.cur_level)).length)
    (hall1 : ∀ l ∈ clauseLits s (confl_cid.setWidth 32).toNat,
      l / 2 < c.mv ∧
      (l / 2 ≠ (0xFFFFFFFF#32).toNat →
        (0 < (s.lvl[l / 2]?.getD 0#32).toNat → mrk1[l / 2]?.getD 0#8 ≠ 0#8) ∧
        (s.mrk[l / 2]?.getD 0#8 = 0#8 →
          (s.lvl[l / 2]?.getD 0#32).toNat ≤ s.cur_level ∧
          (0 < (s.lvl[l / 2]?.getD 0#32).toNat →
            (s.lvl[l / 2]?.getD 0#32).toNat < s.cur_level →
            ∃ j, 1 ≤ j ∧ j < tl1 ∧ (tmp1[j]?.getD 0#32).toNat / 2 = l / 2)))) :
    tc1 = (curTrailIdxs s mrk1 s.trail_end).length ∧
    LowerInv c s tmp1 mrk1 tl1 ∧ MarksCov c s tmp1 mrk1 tl1 ∧
    F0.EntailsClause (cnfClause (activeResolvent s tmp1 mrk1 tl1 s.trail_end)) ∧
    tc1 ≤ c.mv := by
  have hmv := c.hmv; have hmc := c.hmax_c
  unfold dimacsBound at hmv hmc
  have hcore := hinv.core; have hlen := hcore.lengths
  have hnc_le := hlen.num_clauses_le; have hte_le := hlen.trail_end_le
  have hcid32 : (confl_cid.setWidth 32).toNat = confl_cid.toNat := by
    simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : confl_cid.toNat < 2 ^ 32)]
  have hct0 : (curTrailIdxs s s.mrk s.trail_end).length = 0 := by
    unfold curTrailIdxs; rw [filter_length_eq_zero_of_false]; intro j hj
    have hvlt : (s.trl[j]?.getD 0#32).toNat / 2 < c.mv := by
      have := hcore.trail_lits_lt j (List.mem_range.mp hj); omega
    simp [hinv.marks _ hvlt]
  have hcl_confl : ∀ q ∈ clauseLits s confl_cid.toNat,
      q / 2 = (0xFFFFFFFF#32).toNat ∨ ∃ k < s.trail_end, (s.trl[k]?.getD 0#32).toNat = q ^^^ 1 :=
    fun q hq =>
      Or.inr ((hcore.vals_false_iff q (hcore.clauses.lits_lt _ hcid q hq)).mp (hfals q hq))
  obtain ⟨htc1_eq, hlow1, hcov1, _, _, hq1⟩ :=
    analyzeClause_preserves hcore (Nat.le_refl _) (Nat.le_refl _) htl1_ge htl1_le
      hlen.tmp_len_arr ht1_len hct0.symm (Nat.zero_le _) (fun _ h1 h2 => by omega)
      (fun v hv hnz => absurd (hinv.marks v hv) hnz) hcid hcl_confl
      hmp1 htp1 (hcid32 ▸ hnm1) (hcid32 ▸ hnt1) hcnt1 (hcid32 ▸ hall1)
  have hent1 : F0.EntailsClause (cnfClause (activeResolvent s tmp1 mrk1 tl1 s.trail_end)) := by
    refine entails_of_mem_or_false (hcore.clauses.entails confl_cid.toNat hcid) fun q hq => ?_
    rcases hq1 q hq with hskip | hmem | hf
    · have := hcore.clauses.lits_lt confl_cid.toNat hcid q hq
      have : (0xFFFFFFFF#32).toNat = 2 ^ 32 - 1 := rfl; omega
    · exact Or.inl hmem
    · exact Or.inr hf
  have htc1_le_mv : tc1 ≤ c.mv := by
    rw [htc1_eq]; exact Nat.le_trans (List.length_filter_le _ _) (by simp; omega)
  exact ⟨htc1_eq, hlow1, hcov1, hent1, htc1_le_mv⟩

private theorem analyze_nonunit_finish_sem {c : CorePlusCfg} {F0 : CNF Nat}
    {s s_bt2 : CorePlusState} {tmp_m tmp_sw lpool' cls' wh' wn' : List (BitVec 32)}
    {ph' : List (BitVec 8)} {p_bv : BitVec 32} {tl_m mlvl : Nat}
    (hcore : CorePlusCoreInv c F0 s) (hbt_core : CorePlusCoreInv c F0 s_bt2)
    (hs_tmp : s_bt2.tmp = tmp_sw) (hs_nc : s_bt2.num_clauses = s.num_clauses)
    (hs_cl : s_bt2.cur_level = mlvl) (hml_pos : 0 < mlvl) (htl_ge2 : 2 ≤ tl_m)
    (htl_mv : tl_m ≤ c.mv) (huip_lt : (p_bv ^^^ 1#32).toNat < 2 * c.mv)
    (hlow_m : ∀ j, 1 ≤ j → j < tl_m →
      let l := (tmp_m[j]?.getD 0#32).toNat
      l < 2 * c.mv ∧ s.vals[l]?.getD 0#8 = 0xFF#8 ∧
      0 < (s.lvl[l / 2]?.getD 0#32).toNat ∧ (s.lvl[l / 2]?.getD 0#32).toNat < s.cur_level)
    (hall_ml : ∀ j, 1 ≤ j → j < tl_m →
      (s.lvl[(tmp_m[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ mlvl)
    (hsw_mem : ∀ l ∈ (tmp_sw.take tl_m).map BitVec.toNat,
      l = (p_bv ^^^ 1#32).toNat ∨ ∃ j, 1 ≤ j ∧ j < tl_m ∧ (tmp_m[j]?.getD 0#32).toNat = l)
    (hent_sw : F0.EntailsClause (cnfClause ((tmp_sw.take tl_m).map BitVec.toNat)))
    (hbt_keep : ∀ i < s.trail_end,
      (s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ mlvl → i < s_bt2.trail_end)
    (hac_len : (addClauseState s_bt2 ((BitVec.ofNat 64 tl_m).setWidth 32).toNat
        lpool' cls' wh' wn').LengthsOk c)
    (hac_meta : ∀ cid < s_bt2.num_clauses,
      clauseOff (addClauseState s_bt2 ((BitVec.ofNat 64 tl_m).setWidth 32).toNat
        lpool' cls' wh' wn') cid = clauseOff s_bt2 cid ∧
      clauseSize (addClauseState s_bt2 ((BitVec.ofNat 64 tl_m).setWidth 32).toNat
        lpool' cls' wh' wn') cid = clauseSize s_bt2 cid)
    (hac_lp : ∀ k < s_bt2.lit_len, lpool'[k]? = s_bt2.lpool[k]?)
    (hac_off : clauseOff (addClauseState s_bt2 ((BitVec.ofNat 64 tl_m).setWidth 32).toNat
      lpool' cls' wh' wn') s_bt2.num_clauses = s_bt2.lit_len)
    (hac_sz : clauseSize (addClauseState s_bt2 ((BitVec.ofNat 64 tl_m).setWidth 32).toNat
      lpool' cls' wh' wn') s_bt2.num_clauses = ((BitVec.ofNat 64 tl_m).setWidth 32).toNat)
    (hac_lits : clauseLits (addClauseState s_bt2 ((BitVec.ofNat 64 tl_m).setWidth 32).toNat
      lpool' cls' wh' wn') s_bt2.num_clauses =
        (s_bt2.tmp.take ((BitVec.ofNat 64 tl_m).setWidth 32).toNat).map BitVec.toNat)
    (hs_trl : s_bt2.trl = s.trl)
    (hz_get : s_bt2.vals[(p_bv ^^^ 1#32).toNat]?.getD 0#8 = 0#8)
    (hph' : ph'.length = c.mv) :
    let s_ac := addClauseState s_bt2 ((BitVec.ofNat 64 tl_m).setWidth 32).toNat
      lpool' cls' wh' wn'
    let lit := p_bv ^^^ 1#32
    let v := lit.toNat / 2
    s_bt2.trail_end < c.mv ∧
    CorePlusCoreInv c F0
      { s_ac with
        vals := (s_ac.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
        lvl := s_ac.lvl.set v (BitVec.ofNat 32 s_ac.cur_level)
        rsns := s_ac.rsns.set v ((BitVec.ofNat 64 s.num_clauses).setWidth 32)
        trl := s_ac.trl.set s_ac.trail_end lit
        trail_end := s_ac.trail_end + 1
        heur := { s_ac.heur with phases := ph' } } := by
  have hmv := c.hmv; have hmc := c.hmax_c
  unfold dimacsBound at hmv hmc
  have hnc_le := hcore.lengths.num_clauses_le
  have htl32 : ((BitVec.ofNat 64 tl_m).setWidth 32).toNat = tl_m :=
    bv64_setWidth32_toNat (by omega)
  have hlits_lt : ∀ l ∈ (tmp_sw.take tl_m).map BitVec.toNat, l < 2 * c.mv := by
    intro l hl
    rcases hsw_mem l hl with rfl | ⟨j, hj1, hj2, hjeq⟩
    · exact huip_lt
    · rw [← hjeq]; exact (hlow_m j hj1 hj2).1
  have hac_core := addClause_preserves_core hbt_core hac_len (by rw [htl32]; exact htl_ge2)
    (by rw [hs_tmp, htl32]; exact hlits_lt) (by rw [hs_tmp, htl32]; exact hent_sw)
    hac_meta hac_lp hac_off hac_sz hac_lits
  have hac_te_lt : s_bt2.trail_end < c.mv :=
    hac_core.trail_end_lt_of_unassigned huip_lt hz_get
  refine ⟨hac_te_lt, assign_preserves_core hac_core (lit := p_bv ^^^ 1#32)
    (rsn := (BitVec.ofNat 64 s.num_clauses).setWidth 32)
    huip_lt hph' hz_get (by have := hac_core.cur_level_le; omega)
    (fun L h1 h2 => Or.inr (hac_core.levels_inhabited L h1 h2))
    (fun h0 => by dsimp [addClauseState] at h0; omega) (fun _ => ?_)⟩
  have hnc32 : ((BitVec.ofNat 64 s.num_clauses).setWidth 32).toNat = s.num_clauses :=
    bv64_setWidth32_toNat (by omega)
  rw [hnc32]
  refine ⟨by dsimp [addClauseState]; omega, fun q hq => ?_⟩
  rw [← hs_nc, hac_lits, hs_tmp, htl32] at hq
  rcases hsw_mem q hq with rfl | ⟨j, hj1, hj2, hjeq⟩
  · exact Or.inl rfl
  · right
    obtain ⟨hq_lt, hq_fals, _, _⟩ := hlow_m j hj1 hj2
    rw [hjeq] at hq_lt hq_fals
    obtain ⟨ik, hik, hkeq⟩ := (hcore.vals_false_iff q hq_lt).mp hq_fals
    have hklvl : (s.lvl[(s.trl[ik]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ mlvl := by
      have hvar : (s.trl[ik]?.getD 0#32).toNat / 2 = q / 2 := by rw [hkeq]; exact litVar_litNeg q
      rw [hvar, ← hjeq]; exact hall_ml j hj1 hj2
    exact ⟨ik, hbt_keep ik hik hklvl, by dsimp [addClauseState]; rwa [hs_trl]⟩

private theorem analyze_uip_entails {F0 : CNF Nat} {s : CorePlusState}
    {mrk_l : List (BitVec 8)} {tmp_l : List (BitVec 32)} {p_bv : BitVec 32} {idx tl_l : Nat}
    (hent_l : F0.EntailsClause (cnfClause (activeResolvent s tmp_l mrk_l tl_l idx)))
    (hcl_succ : curLits s mrk_l idx = curLits s mrk_l (idx - 1) ++ [p_bv.toNat ^^^ 1])
    (hct_zero : (curTrailIdxs s mrk_l (idx - 1)).length = 0) :
    F0.EntailsClause (cnfClause ((p_bv ^^^ 1#32).toNat :: lowerLits tmp_l tl_l)) := by
  have hct_nil : curTrailIdxs s mrk_l (idx - 1) = [] := List.eq_nil_of_length_eq_zero hct_zero
  have hcl_nil : curLits s mrk_l (idx - 1) = [] := by unfold curLits; simp [hct_nil]
  unfold activeResolvent at hent_l
  rw [hcl_succ, hcl_nil, List.nil_append] at hent_l
  refine entails_of_mem_or_false hent_l fun l hl => Or.inl ?_
  rcases List.mem_append.mp hl with h1 | h2
  · exact List.mem_cons_of_mem _ h1
  · simp only [List.mem_singleton] at h2; rw [h2, ← bv32_xor_1]; exact List.mem_cons_self

private theorem analyze_resolve_sem {c : CorePlusCfg} {F0 : CNF Nat} {s : CorePlusState}
    {mrk_l mrk2 : List (BitVec 8)} {tmp_l tmp2 : List (BitVec 32)}
    {p_bv rcid_bv : BitVec 32} {idx tc_l tc2 tl_l tl2 : Nat}
    (hcore : CorePlusCoreInv c F0 s) (hidx_pos : 0 < idx) (hidx_le : idx ≤ s.trail_end)
    (htl1 : 1 ≤ tl_l) (htl2_ge : tl_l ≤ tl2) (htl2_le : tl2 ≤ c.mv)
    (htl_len : tmp_l.length = c.mv) (ht2_len : tmp2.length = c.mv)
    (htc_sub : tc_l - 1 = (curTrailIdxs s mrk_l (idx - 1)).length)
    (hsub_tc : (BitVec.ofNat 64 tc_l - (1 : BitVec 64)).toNat = tc_l - 1)
    (htc2_ge : (BitVec.ofNat 64 tc_l - (1 : BitVec 64)).toNat ≤ tc2)
    (hlow_l : LowerInv c s tmp_l mrk_l tl_l) (hcov_l : MarksCov c s tmp_l mrk_l tl_l)
    (hent_l : F0.EntailsClause (cnfClause (activeResolvent s tmp_l mrk_l tl_l idx)))
    (hp_get : (s.trl[idx - 1]?.getD 0#32).toNat = p_bv.toNat)
    (hcl_succ : curLits s mrk_l idx = curLits s mrk_l (idx - 1) ++ [p_bv.toNat ^^^ 1])
    (hrc_lt : rcid_bv.toNat < s.num_clauses)
    (hrc_inv : ∀ q ∈ clauseLits s rcid_bv.toNat,
      q = p_bv.toNat ∨ ∃ k < idx - 1, (s.trl[k]?.getD 0#32).toNat = q ^^^ 1)
    (hmp2 : ∀ v < c.mv, mrk_l[v]?.getD 0#8 ≠ 0#8 → mrk2[v]?.getD 0#8 = mrk_l[v]?.getD 0#8)
    (htp2 : ∀ k < tl_l, tmp2[k]? = tmp_l[k]?)
    (hnm2 : ∀ v < c.mv, mrk_l[v]?.getD 0#8 = 0#8 → mrk2[v]?.getD 0#8 ≠ 0#8 →
      ∃ l ∈ clauseLits s rcid_bv.toNat, l / 2 = v ∧ v ≠ (p_bv >>> 1).toNat ∧
        0 < (s.lvl[v]?.getD 0#32).toNat ∧ (s.lvl[v]?.getD 0#32).toNat ≤ s.cur_level)
    (hnt2 : ∀ j, tl_l ≤ j → j < tl2 →
      let l := (tmp2[j]?.getD 0#32).toNat
      l ∈ clauseLits s rcid_bv.toNat ∧ l < 2 * c.mv ∧ l / 2 ≠ (p_bv >>> 1).toNat ∧
      0 < (s.lvl[l / 2]?.getD 0#32).toNat ∧ (s.lvl[l / 2]?.getD 0#32).toNat < s.cur_level ∧
      mrk2[l / 2]?.getD 0#8 ≠ 0#8)
    (hcnt2 : tc2 - (BitVec.ofNat 64 tc_l - (1 : BitVec 64)).toNat =
      ((List.range c.mv).filter fun v =>
        decide (mrk_l[v]?.getD 0#8 = 0#8) && decide (mrk2[v]?.getD 0#8 ≠ 0#8) &&
        decide ((s.lvl[v]?.getD 0#32).toNat = s.cur_level)).length)
    (hall2 : ∀ l ∈ clauseLits s rcid_bv.toNat,
      l / 2 < c.mv ∧
      (l / 2 ≠ (p_bv >>> 1).toNat →
        (0 < (s.lvl[l / 2]?.getD 0#32).toNat → mrk2[l / 2]?.getD 0#8 ≠ 0#8) ∧
        (mrk_l[l / 2]?.getD 0#8 = 0#8 →
          (s.lvl[l / 2]?.getD 0#32).toNat ≤ s.cur_level ∧
          (0 < (s.lvl[l / 2]?.getD 0#32).toNat →
            (s.lvl[l / 2]?.getD 0#32).toNat < s.cur_level →
            ∃ j, tl_l ≤ j ∧ j < tl2 ∧ (tmp2[j]?.getD 0#32).toNat / 2 = l / 2)))) :
    tc2 = (curTrailIdxs s mrk2 (idx - 1)).length ∧
    LowerInv c s tmp2 mrk2 tl2 ∧ MarksCov c s tmp2 mrk2 tl2 ∧
    F0.EntailsClause (cnfClause (activeResolvent s tmp2 mrk2 tl2 (idx - 1))) := by
  have hpv_tr : (p_bv >>> 1).toNat = p_bv.toNat / 2 := bv32_lshr_1 p_bv
  have hclause_r : ∀ q ∈ clauseLits s rcid_bv.toNat,
      q / 2 = p_bv.toNat / 2 ∨ ∃ k < idx - 1, (s.trl[k]?.getD 0#32).toNat = q ^^^ 1 :=
    fun q hq => (hrc_inv q hq).elim (fun he => Or.inl (by rw [he])) Or.inr
  obtain ⟨htc2_eq, hlow2, hcov2, hlow_sub, hcur_sub, hq2⟩ :=
    analyzeClause_preserves hcore (by omega) htl1 htl2_ge htl2_le
      htl_len ht2_len (by rw [hsub_tc]; exact htc_sub) htc2_ge
      hlow_l hcov_l hrc_lt hclause_r hmp2 htp2 (hpv_tr ▸ hnm2) (hpv_tr ▸ hnt2)
      (by simpa [hsub_tc] using hcnt2) (hpv_tr ▸ hall2)
  refine ⟨htc2_eq, hlow2, hcov2, entails_resolve_to (p := p_bv.toNat)
    (hcore.clauses.entails rcid_bv.toNat hrc_lt) hent_l (fun q hq => ?_) (fun l hl => ?_)⟩
  · rcases hq2 q hq with hv_eq | hmem | hf
    · rcases hrc_inv q hq with rfl | ⟨k, hk, hkeq⟩
      · exact Or.inl rfl
      · exfalso
        have := hcore.trail_vars_nodup k (idx - 1) (by omega) (by omega)
          (by rw [hkeq, hp_get]; exact (litVar_litNeg q).trans hv_eq)
        omega
    · exact Or.inr (Or.inl hmem)
    · exact Or.inr (Or.inr hf)
  · unfold activeResolvent at hl
    rcases List.mem_append.mp hl with hl1 | hl2
    · exact Or.inr (Or.inl (List.mem_append_left _ (hlow_sub l hl1)))
    · rw [hcl_succ] at hl2
      rcases List.mem_append.mp hl2 with hl2a | hl2b
      · exact Or.inr (Or.inl (List.mem_append_right _ (hcur_sub l hl2a)))
      · simp only [List.mem_singleton] at hl2b; exact Or.inl hl2b

/-! ## 3. `kissat_analyze` `Func.wp` proof -/

theorem kissat_analyze_wp (Γ : Env)
    (hAc : ∀ args m Q X, corePlusAnalyzeClauseSpec args m Q X →
      Γ "kissat_analyze_clause" [i64, i32, i32] [.bool] args m Q X)
    (hCm : ∀ args m Q X, corePlusClearMarksSpec args m Q X →
      Γ "kissat_clear_marks" [i64, i64] [] args m Q X)
    (hBump : ∀ args m Q X, corePlusBumpVarSpec args m Q X →
      Γ "kissat_bump_var" [i64, i32] [] args m Q X)
    (hDecay : ∀ args m Q X, corePlusBumpDecaySpec args m Q X →
      Γ "kissat_bump_decay" [i64] [] args m Q X)
    (hMin : ∀ args m Q X, corePlusMinimizeClauseSpec args m Q X →
      Γ "kissat_minimize_clause" [i64] [] args m Q X)
    (hRel : ∀ args m Q X, corePlusTickReluctantSpec args m Q X →
      Γ "kissat_tick_reluctant" [i64] [] args m Q X)
    (hBt : ∀ args m Q X, corePlusBacktrackSpec args m Q X →
      Γ "kissat_backtrack" [i64, i64] [] args m Q X)
    (hAddCl : ∀ args m Q X, corePlusAddClauseSpec args m Q X →
      Γ "kissat_add_clause" [i64, i32] [i64] args m Q X)
    (hAssign : ∀ args m Q X, corePlusAssignSpec args m Q X →
      Γ "kissat_assign" [i64, i32, i32] [] args m Q X) :
    ∀ args m Q X, corePlusAnalyzeSpec args m Q X →
      Func.wp Γ kissat_analyze_body args m Q X := by
  rintro ⟨h, confl_cid, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hcid, hfals, hm, hQ⟩
  have hmv := c.hmv; have hmc := c.hmax_c; have hlc := c.hlcap
  unfold dimacsBound at hmv hmc hlc
  have hcore := hinv.core; have hlen := hcore.lengths
  have hcl_lt := hlen.cur_level_lt; have hnc_le := hlen.num_clauses_le
  have hte_le := hlen.trail_end_le; have htrl_len := hlen.trl_len
  have hlvl_len := hlen.lvl_len; have hrsns_len := hlen.rsns_len
  -- Step 1-3: check `cur_level == 0`, set `tmp_cnt := 0, tmp_len := 1`, call `analyze_clause`
  fast_steps
  · have hcl0 : s.cur_level = 0 := ofNat64_eq_zero (by omega) (by assumption)
    exact analyze_ret_ok hQ 20#64 hlen (Or.inr (Or.inr rfl))
      (fun _ => hcore.level0_unsat_of_conflict hcl0 hcid hfals) (fun h => by cases h) hm
      rfl rfl rfl rfl
  have hcur_pos : 0 < s.cur_level := ofNat64_pos (by assumption)
  have hmv_pos : 1 ≤ c.mv := by have := hcore.cur_level_le; omega
  c0_call hAc
  let s1 : CorePlusState := { s with tmp_cnt := 0, tmp_len := 1 }
  have hs1_len : s1.LengthsOk c :=
    hlen.with_ac hlen.mrk_len hlen.tmp_len_arr (by decide) (by decide)
  refine ⟨c, s1, R, rfl, hs1_len, hmv_pos, by dsimp only [s1]; omega, by assumption, ?_⟩
  intro ok1 mrk1 tmp1 tc1 tl1 m3
  dsimp only [s1]
  intro hs2_len htl1_ge htl1_le htc1_ge hmp1 htp1 hnm1 hnt1 hcnt1 hall1 hm3
  cases ok1 with
  | false =>
    fast_steps
    exact analyze_fail_cm hCm hQ hs2_len htl1_le hm3 rfl rfl rfl rfl
  | true =>
    obtain ⟨htc1_eq, hlow1, hcov1, hent1, htc1_le_mv⟩ :=
      analyze_init_sem hinv hcid hfals hs2_len.tmp_len_arr htl1_ge htl1_le
        hmp1 htp1 hnm1 hnt1 hcnt1 (hall1 rfl).2.2
    clear hmp1 htp1 hnm1 hnt1 hcnt1 hall1 htc1_ge hs1_len s1
    fast_steps
    -- Step 4: if `tmp_cnt == 0ULL`
    · have htc_is0 : tc1 = 0 := ofNat64_eq_zero (by omega) (by assumption)
      c0_call hCm
      refine ⟨c, _, R, rfl, hs2_len, htl1_le, hm3, fun mrk_z m_z hmlz _ _ _ hm_z => ?_⟩
      have hz_len :
          ({ s with mrk := mrk_z, tmp := tmp1, tmp_cnt := tc1, tmp_len := tl1 } :
            CorePlusState).LengthsOk c := { hs2_len with mrk_len := hmlz }
      fast_steps
      · refine analyze_ret_ok hQ 20#64 hz_len (Or.inr (Or.inr rfl)) (fun _ => ?_)
          (fun h => by cases h) hm_z rfl rfl rfl rfl
        have htl_is1 : tl1 = 1 := ofNat64_eq_one (by omega) (by assumption)
        have hct_nil : curTrailIdxs s mrk1 s.trail_end = [] :=
          List.eq_nil_of_length_eq_zero (by omega)
        have hres_nil : activeResolvent s tmp1 mrk1 tl1 s.trail_end = [] := by
          unfold activeResolvent lowerLits curLits; simp [htl_is1, hct_nil]
        exact unsat_of_entails_nil (hres_nil ▸ hent1)
      · exact analyze_ret_ok hQ 0#64 hz_len (Or.inl rfl)
          (fun h => by cases h) (fun h => by cases h) hm_z rfl rfl rfl rfl
    -- Step 5: post-1UIP continuation (`J`) + 1UIP loop (`wp_loop_inv`)
    · have htc1_pos : 0 < tc1 := ofNat64_pos (by assumption)
      have hJ_post : ∀ idx mrk_b tmp_b tl_b heur_b p_bv mb,
          idx < s.trail_end → s.trl[idx]? = some p_bv →
          (s.lvl[p_bv.toNat / 2]?.getD 0#32).toNat = s.cur_level →
          mrk_b.length = c.mv → tmp_b.length = c.mv → 1 ≤ tl_b → tl_b ≤ c.mv →
          heur_b.LengthsOk c → (curTrailIdxs s mrk_b idx).length = 0 →
          LowerInv c s tmp_b mrk_b tl_b → MarksCov c s tmp_b mrk_b tl_b →
          F0.EntailsClause (cnfClause ((p_bv ^^^ 1#32).toNat :: lowerLits tmp_b tl_b)) →
          (CorePlusMem c
            { s with
              mrk := mrk_b, tmp := tmp_b, tmp_cnt := 0, tmp_len := tl_b
              heur := heur_b } ⋆ R) mb →
          J (BitVec.ofNat 64 idx, p_bv ^^^ 1#32, ()) mb := by
        intro idx mrk_b tmp_b tl_b heur_b p_bv mb hidx_lt hp_def hp_cl
          hmb_len htb_len htlb1 htlb_mv hhb_ok hct_b0 hlow_b hcov_b hent_b hmb
        clear hlow1 hcov1 hent1 hm3 hs2_len htc1_eq htc1_pos htc1_le_mv htl1_ge htl1_le hAc hm
        apply hJ
        have hp_lt : p_bv.toNat < 2 * c.mv := by
          have := hcore.trail_lits_lt idx hidx_lt; rwa [hp_def, Option.getD_some] at this
        have huip_nat : (p_bv ^^^ 1#32).toNat = p_bv.toNat ^^^ 1 := bv32_xor_1 p_bv
        have huip_lt : (p_bv ^^^ 1#32).toNat < 2 * c.mv := by
          rw [huip_nat]; exact litNeg_lt_two_mul hp_lt
        have huip_fals : s.vals[(p_bv ^^^ 1#32).toNat]?.getD 0#8 = 0xFF#8 :=
          (hcore.vals_false_iff (p_bv ^^^ 1#32).toNat huip_lt).mpr
            ⟨idx, hidx_lt, by rw [hp_def, Option.getD_some, huip_nat]; exact (litNeg_litNeg _).symm⟩
        have h0_tmpb : 0 < tmp_b.length := by omega
        fast_steps
        · exfalso
          change ((p_bv ^^^ 1#32) == 0xFFFFFFFF#32) = true at hc
          rw [beq_iff_eq] at hc
          have h1 := congrArg BitVec.toNat hc
          change (p_bv ^^^ 1#32).toNat = 2 ^ 32 - 1 at h1; omega
        let tmp0 := tmp_b.set 0 (p_bv ^^^ 1#32)
        have htmp0_len : tmp0.length = c.mv := by simp [tmp0, htb_len]
        have htmp0_0 : tmp0[0]? = some (p_bv ^^^ 1#32) := List.getElem?_set_self (by omega)
        have htmp0_gt0 : ∀ j, 1 ≤ j → tmp0[j]? = tmp_b[j]? := fun j hj =>
          List.getElem?_set_ne (by omega)
        have hlow0 : LowerInv c s tmp0 mrk_b tl_b := fun j hj1 hj2 => by
          rw [htmp0_gt0 j hj1]; exact hlow_b j hj1 hj2
        have hcov0 : MarksCov c s tmp0 mrk_b tl_b := fun v hv hnz =>
          (hcov_b v hv hnz).elim
            (fun ⟨j, hj1, hj2, hjeq⟩ => Or.inl ⟨j, hj1, hj2, by rw [htmp0_gt0 j hj1]; exact hjeq⟩)
            Or.inr
        have hlowLits0 : lowerLits tmp0 tl_b = lowerLits tmp_b tl_b := by
          unfold lowerLits; cases tmp_b <;> rfl
        have hent0 : F0.EntailsClause (cnfClause ((tmp0.take tl_b).map BitVec.toNat)) := by
          rw [tmp_take_eq_cons_lowerLits htlb1 (by omega) htmp0_0, hlowLits0]; exact hent_b
        let st0 : CorePlusState :=
          { s with mrk := mrk_b, tmp := tmp0, tmp_cnt := 0, tmp_len := tl_b, heur := heur_b }
        have hst0_len : st0.LengthsOk c :=
          (hlen.with_ac hmb_len htmp0_len (by decide) (by omega)).with_heur hhb_ok
        c0_call hCm
        refine ⟨c, st0, R, rfl, hst0_len, htlb_mv, by assumption,
          fun mrk_c m_c hmc_len hmc_pres hmc_clrt hmc_clrr hm_c => ?_⟩
        have hidx_nat : (BitVec.ofNat 64 idx).toNat = idx := bv64_ofNat_toNat (by omega)
        let sc : CorePlusState :=
          { s with mrk := mrk_c, tmp := tmp0, tmp_cnt := 0, tmp_len := tl_b, heur := heur_b }
        have hsc_inv : CorePlusInv c F0 sc :=
          ⟨(hcore.with_ac hmc_len htmp0_len (by decide) (by omega)).with_heur hhb_ok,
            clear_marks_restores_marksClear hcov0 hct_b0 hmc_pres hmc_clrt (hidx_nat ▸ hmc_clrr)⟩
        clear hCm hJ
        fast_steps
        -- Bump loop: `while (bi < h->tmp_len) { kissat_bump_var(h, tmp[bi] >> 1); bi++; }`
        refine wp_loop_inv
          (fun (bi_v, ()) ml => ∃ heur_i,
            1 ≤ bi_v.toNat ∧ bi_v.toNat ≤ tl_b ∧ heur_i.LengthsOk c ∧
            (CorePlusMem c { sc with heur := heur_i } ⋆ R) ml)
          (fun (bi_v, ()) _ => tl_b - bi_v.toNat) (fun J hJ => ?_)
          (fun J ⟨bi_v, ⟨⟩⟩ ml ⟨heur_i, hbi1, hbile, hhi_ok, hml⟩ ih => ?_)
        · fast_steps; exact hJ (1#64, ()) m_c ⟨heur_b, by decide, htlb1, hhb_ok, hm_c⟩
        · dsimp only [sc] at hml
          refine strip_wp ?_; c0_step; c0_step
          refine wp_jnz_of (fun hc => ?_) (fun _ => ?_)
          · clear hDecay hMin hRel hBt hAddCl hAssign hQ hcov0 hlow0 hent0 hcov_b hlow_b
              hent_b hm_c hmc_pres hmc_clrt hmc_clrr
            simp only [Arg.val_var] at hc; c0_cond hc
            have hbi_lt : bi_v.toNat < tl_b := lt_of_lt_mod64 (by omega) hc
            have hbi_tmp : bi_v.toNat < tmp0.length := by omega
            fast_steps
            c0_call hBump
            refine ⟨c,
              { s with
                mrk := mrk_c, tmp := tmp0, tmp_cnt := 0, tmp_len := tl_b
                heur := heur_i }, R, rfl, (hsc_inv.with_heur hhi_ok).core.lengths,
              hml, fun heur_i' m_i' hhi'_ok hm_i' => ?_⟩
            fast_steps
            have hbi1' : (bi_v + 1).toNat = bi_v.toNat + 1 := bv64_add_one_toNat (by omega)
            exact ih _ _ (by dsimp only; omega)
              ⟨heur_i', by omega, by omega, hhi'_ok, hm_i'⟩
          · -- After bump loop: `bump_decay`, `minimize_clause`, `tick_reluctant`
            fast_steps
            c0_call hDecay
            refine ⟨c,
              { s with
                mrk := mrk_c, tmp := tmp0, tmp_cnt := 0, tmp_len := tl_b
                heur := heur_i }, R, rfl, (hsc_inv.with_heur hhi_ok).core.lengths,
              hml, fun heur2 m2 hh2_ok hm2 => ?_⟩
            fast_steps; c0_call hMin
            let sc2 : CorePlusState :=
              { s with mrk := mrk_c, tmp := tmp0, tmp_cnt := 0, tmp_len := tl_b, heur := heur2 }
            refine ⟨c, F0, sc2, R, rfl, hsc_inv.with_heur hh2_ok,
              htlb1, htlb_mv, hent0, fun k hk => ?_, hm2,
              fun tmp_m tl_m mrk_m mstk_m mclr_m mcl_m mcf_m heur_m mm
                hsmin_inv htl_m1 htl_m_le htmp_m0 htmp_m_sub hent_m hm_m => ?_⟩
            · cases k with
              | zero =>
                change (tmp0[0]?.getD 0#32).toNat < 2 * c.mv ∧
                  s.vals[(tmp0[0]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8
                rw [htmp0_0, Option.getD_some]; exact ⟨huip_lt, huip_fals⟩
              | succ k' =>
                have h := hlow0 (k' + 1) (by omega) hk
                exact ⟨h.1, h.2.1⟩
            · dsimp only [sc2] at hsmin_inv htl_m_le htmp_m0 htmp_m_sub hm_m
              have htmp_m0' : tmp_m[0]? = some (p_bv ^^^ 1#32) := htmp_m0.trans htmp0_0
              have hlow_m : ∀ j, 1 ≤ j → j < tl_m →
                  let l := (tmp_m[j]?.getD 0#32).toNat
                  l < 2 * c.mv ∧ s.vals[l]?.getD 0#8 = 0xFF#8 ∧
                  0 < (s.lvl[l / 2]?.getD 0#32).toNat ∧
                  (s.lvl[l / 2]?.getD 0#32).toNat < s.cur_level := by
                intro j hj1 hjlt
                obtain ⟨i, hi1, hilt, hjeq⟩ := htmp_m_sub j hj1 hjlt
                have h := hlow0 i hi1 hilt
                rw [← hjeq] at h; exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
              let s_min : CorePlusState :=
                { s with
                  tmp := tmp_m, tmp_len := tl_m, mrk := mrk_m, tmp_cnt := 0
                  min_stk := mstk_m, min_clr := mclr_m, min_clr_len := mcl_m
                  min_clr_full := mcf_m, heur := heur_m }
              change CorePlusInv c F0 s_min at hsmin_inv
              change (CorePlusMem c s_min ⋆ R) mm at hm_m
              fast_steps; c0_call hRel
              refine ⟨c, s_min, R, rfl, hsmin_inv.core.lengths, hm_m,
                fun heur3 m3 hh3_ok hm3' => ?_⟩
              let s_tr : CorePlusState :=
                { s with
                  tmp := tmp_m, tmp_len := tl_m, mrk := mrk_m, tmp_cnt := 0
                  min_stk := mstk_m, min_clr := mclr_m, min_clr_len := mcl_m
                  min_clr_full := mcf_m, heur := heur3 }
              have hs_tr_inv : CorePlusInv c F0 s_tr := hsmin_inv.with_heur hh3_ok
              change (CorePlusMem c s_tr ⋆ R) m3 at hm3'
              have htm_len : tmp_m.length = c.mv := hs_tr_inv.core.lengths.tmp_len_arr
              clear hlow0 hcov0 hent0 hlow_b hcov_b hent_b hm_c hm2 hm_m hml hmc_pres hmc_clrt
                hmc_clrr htmp_m_sub htmp_m0 hsmin_inv hsc_inv hst0_len s_min sc2 st0
              dsimp only [s_tr] at hm3'
              fast_steps
              · -- Unit learned clause branch (`tl_m = 1`)
                clear hBump hDecay hMin hRel hAddCl hlow_m
                have htl_mv : tl_m ≤ c.mv := Nat.le_trans htl_m_le htlb_mv
                have htl_is1 : tl_m = 1 := ofNat64_eq_one (lt64_of_le_mv htl_mv hmv) hc
                have hent_unit : F0.EntailsClause (cnfClause [(p_bv ^^^ 1#32).toNat]) := by
                  rw [htl_is1, take1_map_eq_singleton htmp_m0'] at hent_m; exact hent_m
                c0_call hBt
                refine ⟨c, F0, s_tr, R, rfl, hs_tr_inv, Nat.zero_le _, hm3',
                  fun vals_b lvl_b rsns_b te_b prop_b heur_bt mbt hbt_inv hbt1 hbt2 hmbt => ?_⟩
                let s_bt : CorePlusState :=
                  { s with
                    tmp := tmp_m, tmp_len := tl_m, mrk := mrk_m, tmp_cnt := 0
                    min_stk := mstk_m, min_clr := mclr_m, min_clr_len := mcl_m
                    min_clr_full := mcf_m, vals := vals_b, lvl := lvl_b, rsns := rsns_b
                    trail_end := te_b, propagated := prop_b, cur_level := 0, heur := heur_bt }
                change CorePlusInv c F0 s_bt at hbt_inv
                change (CorePlusMem c s_bt ⋆ R) mbt at hmbt
                dsimp only [s_bt] at hmbt
                clear hbt1 hbt2 hs_tr_inv hm3' s_tr hBt htmp_m0' hent_m
                have hvals_blen : vals_b.length = 2 * c.mv := hbt_inv.core.lengths.vals_len
                have huip_vb : (p_bv ^^^ 1#32).toNat < vals_b.length := hvals_blen ▸ huip_lt
                have huip_vals : ((p_bv ^^^ 1#32).setWidth 64).toNat < vals_b.length := by
                  rw [bv_c0_zext32_64]; exact huip_vb
                have huip_mod : (p_bv ^^^ 1#32).toNat % 2 ^ 64 = (p_bv ^^^ 1#32).toNat :=
                  Nat.mod_eq_of_lt (lt64_of_bv32 _)
                fast_steps
                · exact analyze_ret_ok hQ 0#64 hbt_inv.core.lengths (Or.inl rfl)
                    (fun h => by cases h) (fun h => by cases h) hmbt rfl rfl rfl rfl
                · have hz_bv : vals_b[(p_bv ^^^ 1#32).toNat]'huip_vb = 0#8 := by
                    simp only [huip_mod] at hc; exact hc
                  have hz_get : vals_b[(p_bv ^^^ 1#32).toNat]?.getD 0#8 = 0#8 := by
                    rw [List.getElem?_eq_getElem huip_vb, Option.getD_some]; exact hz_bv
                  have hte_lt : te_b < c.mv :=
                    hbt_inv.core.trail_end_lt_of_unassigned huip_lt hz_get
                  c0_call hAssign
                  refine ⟨c, s_bt, R, rfl, hbt_inv.core.lengths, hmbt, ?_⟩
                  have huip_div : (p_bv ^^^ 1#32).toNat / 2 < c.mv :=
                    Nat.div_lt_of_lt_mul (Nat.mul_comm 2 c.mv ▸ huip_lt)
                  have hnot_oob : ¬ (c.mv ≤ (p_bv ^^^ 1#32).toNat / 2 ∨ c.mv ≤ te_b) :=
                    not_or.mpr ⟨Nat.not_le_of_gt huip_div, Nat.not_le_of_gt hte_lt⟩
                  simp only [s_bt, hnot_oob, ↓reduceIte]
                  intro ph' mf hph' hflen hmf
                  fast_steps
                  have hfin_core := assign_preserves_core hbt_inv.core (lit := p_bv ^^^ 1#32)
                    (rsn := 0xFFFFFFFF#32) huip_lt hph' hz_get (Nat.zero_le _)
                    (fun L h1 h2 => False.elim (Nat.not_lt_of_ge h2 h1)) (fun _ => hent_unit)
                    (fun hne => absurd rfl hne)
                  exact analyze_ret_ok hQ 1#64 hflen (Or.inr (Or.inl rfl))
                    (fun h => by cases h) (fun _ => ⟨hfin_core, hbt_inv.marks⟩) hmf
                    rfl rfl rfl rfl
              · -- Non-unit learned clause branch (`2 ≤ tl_m`)
                have htl_mv : tl_m ≤ c.mv := Nat.le_trans htl_m_le htlb_mv
                have htl_64 : tl_m < 2 ^ 64 := lt64_of_le_mv htl_mv hmv
                have htl_ge2 : 2 ≤ tl_m := by
                  have hne1 : ¬ BitVec.ofNat 64 tl_m = 1#64 := by assumption
                  by_cases h1 : tl_m = 1
                  · exact absurd (by rw [h1]) hne1
                  · omega
                have hlow_m1 := hlow_m 1 (Nat.le_refl _) (Nat.lt_of_lt_of_le (by decide) htl_ge2)
                have htm1_lt : 1 < tmp_m.length :=
                  htm_len ▸ Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (by decide) htl_ge2) htl_mv
                have htm1_eq : (tmp_m[1]'htm1_lt).toNat = (tmp_m[1]?.getD 0#32).toNat := by
                  rw [List.getElem?_eq_getElem htm1_lt, Option.getD_some]
                have hv1_lt : (tmp_m[1]'htm1_lt).toNat / 2 < c.mv :=
                  Nat.div_lt_of_lt_mul (htm1_eq.symm ▸ (Nat.mul_comm 2 c.mv ▸ hlow_m1.1))
                have hv1_lvl : ((tmp_m[1]'htm1_lt >>> 1).setWidth 64).toNat < s.lvl.length := by
                  rw [hlvl_len, bv_c0_zext32_64, bv32_lshr_1]; exact hv1_lt
                fast_steps
                obtain ⟨ml1_bv, hml1_def⟩ :
                    ∃ x, s.lvl[((tmp_m[1]'htm1_lt >>> 1).setWidth 64).toNat]'hv1_lvl = x := ⟨_, rfl⟩
                have hml1_eq : ml1_bv.toNat =
                    (s.lvl[(tmp_m[1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
                  rw [← hml1_def,
                    List.getElem?_eq_getElem (by rw [hlvl_len, ← htm1_eq]; exact hv1_lt),
                    Option.getD_some]
                  congr 2; rw [bv_c0_zext32_64, bv32_lshr_1, htm1_eq]
                simp only [hml1_def]
                -- Max-level scan loop: `while (k < h->tmp_len)`
                refine wp_loop_inv
                  (fun (midx_v, mlvl_v, k_v, ()) mk =>
                    2 ≤ k_v.toNat ∧ k_v.toNat ≤ tl_m ∧
                    1 ≤ midx_v.toNat ∧ midx_v.toNat < k_v.toNat ∧
                    0 < mlvl_v.toNat ∧ mlvl_v.toNat < s.cur_level ∧
                    (∀ j, 1 ≤ j → j < k_v.toNat →
                      (s.lvl[(tmp_m[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ mlvl_v.toNat) ∧
                    (CorePlusMem c s_tr ⋆ R) mk)
                  (fun (_, _, k_v, ()) _ => tl_m - k_v.toNat) (fun J hJ => ?_)
                  (fun J ⟨midx_v, mlvl_v, k_v, ⟨⟩⟩ mk
                    ⟨hk2, hkle, hmi1, hmik, hml_pos, hml_lt, hall_ml, hmk⟩ ih => ?_)
                · fast_steps
                  refine hJ (1#64, ml1_bv.setWidth 64, 2#64, ()) m3
                    ⟨by decide, htl_ge2, by decide, by decide,
                      by rw [bv_c0_zext32_64, hml1_eq]; exact hlow_m1.2.2.1,
                      by rw [bv_c0_zext32_64, hml1_eq]; exact hlow_m1.2.2.2,
                      fun j hj1 hj2 => by
                        have hjeq : j = 1 :=
                          Nat.le_antisymm (Nat.le_of_lt_succ hj2) hj1
                        subst hjeq; rw [bv_c0_zext32_64, hml1_eq]; exact Nat.le_refl _, hm3'⟩
                · dsimp only [s_tr] at hmk
                  refine strip_wp ?_; c0_step; c0_step; c0_step
                  · -- `k < tl_m`: load `tmp[k]` and `lvl[tmp[k] >> 1]`
                    clear hBump hDecay hMin hRel hBt hAddCl hAssign hQ hcore hinv hlen hm3'
                      hent_m htmp_m0' huip_nat huip_lt huip_fals hml1_def hml1_eq htm1_lt htm1_eq
                      hv1_lt hv1_lvl hlow_m1 hs_tr_inv
                    have hklt : k_v.toNat < tl_m := lt_of_lt_mod64 htl_64 hc
                    have hk1 : 1 ≤ k_v.toNat := Nat.le_trans (by decide) hk2
                    have hlow_k := hlow_m k_v.toNat hk1 hklt
                    have htmk_lt : k_v.toNat < tmp_m.length :=
                      htm_len ▸ Nat.lt_of_lt_of_le hklt htl_mv
                    have htmk_eq : (tmp_m[k_v.toNat]'htmk_lt).toNat =
                        (tmp_m[k_v.toNat]?.getD 0#32).toNat := by
                      rw [List.getElem?_eq_getElem htmk_lt, Option.getD_some]
                    have hkl_idx_lt : (tmp_m[k_v.toNat]?.getD 0#32).toNat / 2 < s.lvl.length :=
                      hlvl_len ▸ Nat.div_lt_of_lt_mul (Nat.mul_comm 2 c.mv ▸ hlow_k.1)
                    have hkl_lvl :
                        ((tmp_m[k_v.toNat]'htmk_lt >>> 1).setWidth 64).toNat < s.lvl.length := by
                      rw [bv_c0_zext32_64, bv32_lshr_1, htmk_eq]; exact hkl_idx_lt
                    have hkl_get : (s.lvl[((tmp_m[k_v.toNat]'htmk_lt >>> 1).setWidth 64).toNat]'
                        hkl_lvl).toNat =
                          (s.lvl[(tmp_m[k_v.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
                      rw [List.getElem?_eq_getElem hkl_idx_lt, Option.getD_some]
                      congr 2; rw [bv_c0_zext32_64, bv32_lshr_1, htmk_eq]
                    have hkl_get_div :
                        (s.lvl[(tmp_m[k_v.toNat]'htmk_lt).toNat / 2]'(by
                          rw [htmk_eq]; exact hkl_idx_lt)).toNat =
                          (s.lvl[(tmp_m[k_v.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
                      rw [List.getElem?_eq_getElem hkl_idx_lt, Option.getD_some]
                      congr 2; exact congrArg (· / 2) htmk_eq
                    have hkl_mod : (tmp_m[k_v.toNat]'htmk_lt).toNat / 2 % 2 ^ 64 =
                        (tmp_m[k_v.toNat]'htmk_lt).toNat / 2 :=
                      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (lt64_of_bv32 _))
                    have hkl_lt64 : (s.lvl[(tmp_m[k_v.toNat]'htmk_lt).toNat / 2]'(by
                        rw [htmk_eq]; exact hkl_idx_lt)).toNat < 2 ^ 64 := lt64_of_bv32 _
                    have hkv1 : (k_v + (1 : BitVec 64)).toNat = k_v.toNat + 1 :=
                      bv64_add_one_toNat (Nat.lt_of_le_of_lt hklt htl_64)
                    have hmeas : tl_m - (k_v + (1 : BitVec 64)).toNat < tl_m - k_v.toNat := by
                      rw [hkv1]; exact Nat.sub_succ_lt_self tl_m k_v.toNat hklt
                    fast_steps
                    · -- `klvl > max_lvl`: update `max_lvl, max_idx`
                      have hkl_gt : mlvl_v.toNat <
                          (s.lvl[(tmp_m[k_v.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
                        rw [← hkl_get_div]; simp only [hkl_mod] at hc
                        exact lt_of_lt_mod64 hkl_lt64 hc
                      refine ih _ _ hmeas
                        ⟨hkv1 ▸ Nat.le_succ_of_le hk2, hkv1 ▸ hklt, hk1,
                          hkv1 ▸ Nat.lt_succ_self _,
                          by rw [bv_c0_zext32_64, hkl_get]; exact hlow_k.2.2.1,
                          by rw [bv_c0_zext32_64, hkl_get]; exact hlow_k.2.2.2,
                          fun j hj1 hjk => ?_, hmk⟩
                      rw [bv_c0_zext32_64, hkl_get]
                      rw [hkv1] at hjk
                      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hjk) with hlt | rfl
                      · exact Nat.le_trans (hall_ml j hj1 hlt) (Nat.le_of_lt hkl_gt)
                      · exact Nat.le_refl _
                    · -- `klvl ≤ max_lvl`: keep `max_lvl, max_idx`
                      have hkl_le :
                          (s.lvl[(tmp_m[k_v.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
                            mlvl_v.toNat := by
                        rw [← hkl_get_div]; simp only [hkl_mod] at hc
                        rw [Nat.mod_eq_of_lt hkl_lt64] at hc
                        exact Nat.le_of_not_lt hc
                      refine ih _ _ hmeas
                        ⟨hkv1 ▸ Nat.le_succ_of_le hk2, hkv1 ▸ hklt, hmi1,
                          hkv1 ▸ Nat.lt_succ_of_lt hmik, hml_pos, hml_lt,
                          fun j hj1 hjk => ?_, hmk⟩
                      rw [hkv1] at hjk
                      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hjk) with hlt | rfl
                      · exact hall_ml j hj1 hlt
                      · exact hkl_le
                  · -- Exit max-level loop (`k = tl_m`): swap, backtrack, add, assign
                    clear hBump hDecay hMin hRel
                    have hkeq : k_v.toNat = tl_m := by
                      rw [Nat.mod_eq_of_lt htl_64] at hc
                      exact Nat.le_antisymm hkle (Nat.le_of_not_lt hc)
                    have hmi_lt : midx_v.toNat < tl_m := hkeq ▸ hmik
                    have hmidx_lt : midx_v.toNat < tmp_m.length :=
                      htm_len ▸ Nat.lt_of_lt_of_le hmi_lt htl_mv
                    have hmidx_lt' :
                        midx_v.toNat < (tmp_m.set 1 (tmp_m[midx_v.toNat]'hmidx_lt)).length := by
                      rw [List.length_set]; exact hmidx_lt
                    refine strip_wp ?_; c0_step
                    refine wp_jnz_of (fun hc => ?_) (fun _ => ?_)
                    · simp only [Arg.val_var] at hc; c0_cond hc; exfalso
                      have hcl_64 : s.cur_level < 2 ^ 64 := Nat.lt_trans hcl_lt (by decide)
                      rw [Nat.mod_eq_of_lt hcl_64, Nat.mod_eq_of_lt hcl_lt,
                        Nat.mod_eq_of_lt hcl_64] at hc
                      exact Nat.not_le_of_gt hml_lt hc
                    fast_steps
                    let tmp_sw := (tmp_m.set 1 (tmp_m[midx_v.toNat]'hmidx_lt)).set
                      midx_v.toNat (tmp_m[1]'htm1_lt)
                    have hsw_len : tmp_sw.length = c.mv := by
                      simp only [tmp_sw, List.length_set, htm_len]
                    obtain ⟨hsw_iff, hsw_mem⟩ := swap_tmp_props htl_ge2 (htm_len ▸ htl_mv)
                      hmi1 hmi_lt htmp_m0'
                    have hent_sw :
                        F0.EntailsClause (cnfClause ((tmp_sw.take tl_m).map BitVec.toNat)) :=
                      entails_of_mem_or_false hent_m fun l hl => Or.inl ((hsw_iff l).mpr hl)
                    let s_sw : CorePlusState :=
                      { s with
                        tmp := tmp_sw, tmp_len := tl_m, mrk := mrk_m, tmp_cnt := 0
                        min_stk := mstk_m, min_clr := mclr_m, min_clr_len := mcl_m
                        min_clr_full := mcf_m, heur := heur3 }
                    have hsw_inv : CorePlusInv c F0 s_sw :=
                      ⟨{ hs_tr_inv.core with
                          lengths := { hs_tr_inv.core.lengths with tmp_len_arr := hsw_len }
                          clauses := { hs_tr_inv.core.clauses with
                            bounds := hs_tr_inv.core.clauses.bounds } },
                        hs_tr_inv.marks⟩
                    c0_call hBt
                    refine ⟨c, F0, s_sw, R, rfl, hsw_inv, Nat.le_of_lt hml_lt,
                      by assumption,
                      fun vals_b lvl_b rsns_b te_b prop_b heur_bt mbt hbt_inv hbt1 hbt_keep
                        hmbt => ?_⟩
                    let s_bt2 : CorePlusState :=
                      { s with
                        tmp := tmp_sw, tmp_len := tl_m, mrk := mrk_m, tmp_cnt := 0
                        min_stk := mstk_m, min_clr := mclr_m, min_clr_len := mcl_m
                        min_clr_full := mcf_m, vals := vals_b, lvl := lvl_b, rsns := rsns_b
                        trail_end := te_b, propagated := prop_b, cur_level := mlvl_v.toNat
                        heur := heur_bt }
                    change CorePlusInv c F0 s_bt2 at hbt_inv
                    change (CorePlusMem c s_bt2 ⋆ R) mbt at hmbt
                    dsimp only [s_bt2] at hmbt
                    dsimp only [s_sw] at hbt_keep
                    clear hbt1 hsw_inv s_sw hBt ih hmidx_lt' hml1_def hml1_eq htm1_eq hv1_lt
                      hv1_lvl hlow_m1 hs_tr_inv hm3' hsw_iff htmp_m0' hent_m
                    fast_steps
                    have htl32 : ((BitVec.ofNat 64 tl_m).setWidth 32).toNat = tl_m :=
                      bv64_setWidth32_toNat (lt32_of_le_mv htl_mv hmv)
                    c0_call hAddCl
                    refine ⟨c, s_bt2, R, rfl, hbt_inv.core.lengths, htl32.symm ▸ htl_mv, hmbt, ?_⟩
                    by_cases hoom : c.max_c ≤ s.num_clauses ∨ c.lcap - s.lit_len <
                        ((BitVec.ofNat 64 tl_m).setWidth 32).toNat
                    · simp only [s_bt2, hoom, ↓reduceIte]
                      fast_steps
                      exact analyze_ret_ok hQ 0#64 hbt_inv.core.lengths (Or.inl rfl)
                        (fun h => by cases h) (fun h => by cases h) hmbt rfl rfl rfl rfl
                    · simp only [s_bt2, hoom, ↓reduceIte]
                      intro lpool' cls' wh' wn' mac hac_len hac_meta hac_lp hac_off hac_sz hac_lits
                        hmac
                      let s_ac : CorePlusState :=
                        { s with
                          tmp := tmp_sw, tmp_len := tl_m, mrk := mrk_m, tmp_cnt := 0
                          min_stk := mstk_m, min_clr := mclr_m, min_clr_len := mcl_m
                          min_clr_full := mcf_m, vals := vals_b, lvl := lvl_b, rsns := rsns_b
                          trail_end := te_b, propagated := prop_b, cur_level := mlvl_v.toNat
                          heur := heur_bt, lpool := lpool', cls := cls', wh := wh', wn := wn'
                          lit_len := s.lit_len + ((BitVec.ofNat 64 tl_m).setWidth 32).toNat
                          num_clauses := s.num_clauses + 1 }
                      have hvals_blen : vals_b.length = 2 * c.mv := hac_len.vals_len
                      have huip_vb : (p_bv ^^^ 1#32).toNat < vals_b.length := hvals_blen ▸ huip_lt
                      have huip_vals : ((p_bv ^^^ 1#32).setWidth 64).toNat < vals_b.length := by
                        rw [bv_c0_zext32_64]; exact huip_vb
                      have huip_mod : (p_bv ^^^ 1#32).toNat % 2 ^ 64 = (p_bv ^^^ 1#32).toNat :=
                        Nat.mod_eq_of_lt (lt64_of_bv32 _)
                      change (CorePlusMem c s_ac ⋆ R) mac at hmac
                      dsimp only [s_ac] at hmac
                      fast_steps
                      · exfalso
                        have h1 := congrArg BitVec.toNat hc
                        rw [bv64_ofNat_toNat (lt64_of_le_mv hnc_le hmc)] at h1
                        have hnc_lt32 : s.num_clauses < 0xFFFFFFFF :=
                          Nat.lt_of_le_of_lt hnc_le (Nat.lt_trans hmc (by decide))
                        exact Nat.ne_of_lt hnc_lt32 h1
                      · exact analyze_ret_ok hQ 0#64 hac_len (Or.inl rfl)
                          (fun h => by cases h) (fun h => by cases h) hmac rfl rfl rfl rfl
                      · have hz_bv : vals_b[(p_bv ^^^ 1#32).toNat]'huip_vb = 0#8 := by
                          simp only [huip_mod] at hc; exact hc
                        have hz_get : vals_b[(p_bv ^^^ 1#32).toNat]?.getD 0#8 = 0#8 := by
                          rw [List.getElem?_eq_getElem huip_vb, Option.getD_some]; exact hz_bv
                        have hfin_sem := fun (ph' : List (BitVec 8)) (hph' : ph'.length = c.mv) =>
                          analyze_nonunit_finish_sem hcore hbt_inv.core rfl rfl rfl hml_pos
                            htl_ge2 htl_mv huip_lt hlow_m (by rwa [hkeq] at hall_ml) hsw_mem
                            hent_sw hbt_keep hac_len hac_meta hac_lp hac_off hac_sz hac_lits
                            rfl hz_get hph'
                        have hac_te_lt : te_b < c.mv :=
                          (hfin_sem (List.replicate c.mv 0#8) (List.length_replicate)).1
                        c0_call hAssign
                        refine ⟨c, s_ac, R, rfl, hac_len, hmac, ?_⟩
                        have huip_div : (p_bv ^^^ 1#32).toNat / 2 < c.mv :=
                          Nat.div_lt_of_lt_mul (Nat.mul_comm 2 c.mv ▸ huip_lt)
                        have hnot_oob :
                            ¬ (c.mv ≤ (p_bv ^^^ 1#32).toNat / 2 ∨ c.mv ≤ te_b) :=
                          not_or.mpr ⟨Nat.not_le_of_gt huip_div, Nat.not_le_of_gt hac_te_lt⟩
                        simp only [s_ac, hnot_oob, ↓reduceIte]
                        intro ph' mf hph' hflen hmf
                        fast_steps
                        exact analyze_ret_ok hQ 1#64 hflen (Or.inr (Or.inl rfl))
                          (fun h => by cases h) (fun _ => ⟨(hfin_sem ph' hph').2, hbt_inv.marks⟩)
                          hmf rfl rfl rfl rfl
      clear hJ
      refine wp_loop_inv
        (fun (idx_v, ()) ml => ∃ idx mrk_l tmp_l tc_l tl_l heur_l,
          idx ≤ s.trail_end ∧ idx_v = BitVec.ofNat 64 idx ∧
          mrk_l.length = c.mv ∧ tmp_l.length = c.mv ∧ 1 ≤ tl_l ∧ tl_l ≤ c.mv ∧
          heur_l.LengthsOk c ∧ 0 < tc_l ∧ tc_l = (curTrailIdxs s mrk_l idx).length ∧
          LowerInv c s tmp_l mrk_l tl_l ∧ MarksCov c s tmp_l mrk_l tl_l ∧
          F0.EntailsClause (cnfClause (activeResolvent s tmp_l mrk_l tl_l idx)) ∧
          (CorePlusMem c
            { s with
              mrk := mrk_l, tmp := tmp_l, tmp_cnt := tc_l, tmp_len := tl_l
              heur := heur_l } ⋆ R) ml)
        (fun (idx_v, ()) _ => idx_v.toNat) (fun L hL => ?_) (fun L ⟨idx_v, ⟨⟩⟩ ml hinv ih => ?_)
      · -- Entry into 1UIP loop
        fast_steps
        exact hL _ m3 ⟨s.trail_end, mrk1, tmp1, tc1, tl1, s.heur, Nat.le_refl _, rfl,
          hs2_len.mrk_len, hs2_len.tmp_len_arr, htl1_ge, htl1_le, hlen.heur_ok,
          htc1_pos, htc1_eq, hlow1, hcov1, hent1, hm3⟩
      · -- 1UIP loop body (lines 952-977)
        clear hlow1 hcov1 hent1 hm3 hs2_len htc1_eq htc1_pos htc1_le_mv htl1_ge htl1_le
          hDecay hMin hRel hBt hAddCl hAssign hm
        obtain ⟨idx, mrk_l, tmp_l, tc_l, tl_l, heur_l, hidx_le, rfl, hml_len, htl_len, htl1,
          htl_mv, hhl_ok, htc_pos, htc_eq, hlow_l, hcov_l, hent_l, hml⟩ := hinv
        have htc_le_mv : tc_l ≤ c.mv := by
          rw [htc_eq]; exact Nat.le_trans (List.length_filter_le _ _) (by simp; omega)
        have htc_64 : tc_l < 2 ^ 64 := lt64_of_le_mv htc_le_mv hmv
        have htl_64 : tl_l < 2 ^ 64 := lt64_of_le_mv htl_mv hmv
        have hidx_64 : idx < 2 ^ 64 := lt64_of_le_mv (Nat.le_trans hidx_le hte_le) hmv
        let sl : CorePlusState :=
          { s with mrk := mrk_l, tmp := tmp_l, tmp_cnt := tc_l, tmp_len := tl_l, heur := heur_l }
        have hsl_len : sl.LengthsOk c :=
          (hlen.with_ac hml_len htl_len htc_64 htl_64).with_heur hhl_ok
        have hskip : ∀ (_hidx_pos : 0 < idx),
            ¬ (mrk_l[(s.trl[idx - 1]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 ∧
               (s.lvl[(s.trl[idx - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s.cur_level) →
            L (BitVec.ofNat 64 idx - 1#64, ()) ml := fun hidx_pos hnot => by
          have hsub_nat : (BitVec.ofNat 64 idx - 1#64).toNat = idx - 1 :=
            bv64_sub_one_toNat hidx_pos hidx_64
          have hidx_eq : idx - 1 + 1 = idx := Nat.sub_add_cancel hidx_pos
          have hct_same : curTrailIdxs s mrk_l idx = curTrailIdxs s mrk_l (idx - 1) := by
            rw [← hidx_eq]; exact curTrailIdxs_succ_false hnot
          have hcl_same : curLits s mrk_l idx = curLits s mrk_l (idx - 1) := by
            rw [← hidx_eq]; exact curLits_succ_false hnot
          refine ih _ _
            (by dsimp only; rw [hsub_nat, bv64_ofNat_toNat hidx_64]
                exact Nat.sub_lt hidx_pos Nat.one_pos)
            ⟨idx - 1, mrk_l, tmp_l, tc_l, tl_l, heur_l, Nat.le_trans (Nat.sub_le _ _) hidx_le,
              by rw [← bv_ofNat_toNat_eq (BitVec.ofNat 64 idx - 1#64), hsub_nat], hml_len,
              htl_len, htl1, htl_mv, hhl_ok, htc_pos, by rw [← hct_same]; exact htc_eq,
              hlow_l, hcov_l, ?_, hml⟩
          unfold activeResolvent at hent_l ⊢; rwa [hcl_same] at hent_l
        refine strip_wp ?_; c0_step; c0_step
        refine wp_jnz_of (fun _ => ?_) (fun hc => by
          simp only [Arg.val_var] at hc; c0_cond hc; exfalso
          rw [Nat.mod_eq_of_lt htc_64] at hc
          exact hc htc_pos)
        c0_let_simp
        refine wp_jnz_of
          (fun _ => by fast_steps; exact analyze_fail_cm hCm hQ hsl_len htl_mv hml rfl rfl rfl rfl)
          (fun hidx_ne0 => ?_)
        simp only [Arg.val_var] at hidx_ne0; c0_cond hidx_ne0
        have hidx_pos : 0 < idx := ofNat64_pos hidx_ne0
        have hidx_lt : idx - 1 < s.trail_end :=
          Nat.lt_of_lt_of_le (Nat.sub_lt hidx_pos Nat.one_pos) hidx_le
        have hsub_nat : (BitVec.ofNat 64 idx - (1 : BitVec 64)).toNat = idx - 1 :=
          bv64_sub_one_toNat hidx_pos hidx_64
        have hi_trl : idx - 1 < s.trl.length := htrl_len ▸ Nat.lt_of_lt_of_le hidx_lt hte_le
        have hi_trl_bv : (BitVec.ofNat 64 idx - (1 : BitVec 64)).toNat < s.trl.length :=
          hsub_nat ▸ hi_trl
        refine strip_wp ?_; c0_step; c0_step
        obtain ⟨p_bv, hp_bv_def⟩ :
            ∃ x, s.trl[(BitVec.ofNat 64 idx - (1 : BitVec 64)).toNat]'hi_trl_bv = x := ⟨_, rfl⟩
        have hp_get : (s.trl[idx - 1]?.getD 0#32).toNat = p_bv.toNat := by
          rw [← hp_bv_def, List.getElem?_eq_getElem hi_trl, Option.getD_some]
          congr 2; exact hsub_nat.symm
        have hp_lt_all : p_bv.toNat < 2 * c.mv := by
          have := hcore.trail_lits_lt (idx - 1) hidx_lt; rwa [hp_get] at this
        have hpv_lt_all : p_bv.toNat / 2 < c.mv :=
          Nat.div_lt_of_lt_mul (Nat.mul_comm 2 c.mv ▸ hp_lt_all)
        have hpv_64 : p_bv.toNat / 2 < 2 ^ 64 := lt64_of_le_mv (Nat.le_of_lt hpv_lt_all) hmv
        have hpv_mod : p_bv.toNat / 2 % 2 ^ 64 = p_bv.toNat / 2 := Nat.mod_eq_of_lt hpv_64
        have hpv_mrk_raw : p_bv.toNat / 2 < mrk_l.length := hml_len ▸ hpv_lt_all
        have hpv_lvl_raw : p_bv.toNat / 2 < s.lvl.length := hlvl_len ▸ hpv_lt_all
        have hpv_rsn_raw : p_bv.toNat / 2 < s.rsns.length := hrsns_len ▸ hpv_lt_all
        have hpv_mrk : ((p_bv >>> 1).setWidth 64).toNat < mrk_l.length := by
          rw [bv_c0_zext32_64, bv32_lshr_1]; exact hpv_mrk_raw
        have hpv_lvl : ((p_bv >>> 1).setWidth 64).toNat < s.lvl.length := by
          rw [bv_c0_zext32_64, bv32_lshr_1]; exact hpv_lvl_raw
        have hpv_rsn : ((p_bv >>> 1).setWidth 64).toNat < s.rsns.length := by
          rw [bv_c0_zext32_64, bv32_lshr_1]; exact hpv_rsn_raw
        simp only [hp_bv_def]
        refine strip_wp ?_; c0_step
        refine wp_jnz_of (fun hc => by
          simp only [Arg.val_var] at hc; c0_cond hc; exfalso
          rw [Nat.mod_eq_of_lt (lt64_of_le_mv (Nat.le_refl _) hmv), hpv_mod] at hc
          exact Nat.not_le_of_gt hpv_lt_all hc)
          (fun _ => ?_)
        fast_steps
        · -- `mrk[pv] ≠ 0 ∧ lvl[pv] == cur_lvl`: call `kissat_bump_var(h, pv)`
          clear hskip
          have hmnz_bv : ¬ mrk_l[p_bv.toNat / 2]'hpv_mrk_raw = 0#8 := by
            have h0 : ¬ mrk_l[p_bv.toNat / 2 % 2 ^ 64]'(hpv_mod.symm ▸ hpv_mrk_raw) = 0#8 := by
              assumption
            simpa only [hpv_mod] using h0
          have hmnz : mrk_l[p_bv.toNat / 2]?.getD 0#8 ≠ 0#8 := by
            rw [List.getElem?_eq_getElem hpv_mrk_raw, Option.getD_some]; exact hmnz_bv
          have hpl_bv : s.lvl[p_bv.toNat / 2]'hpv_lvl_raw =
              (BitVec.ofNat 64 s.cur_level).setWidth 32 := by
            simp only [hpv_mod] at hc; exact hc
          have hpl_cl : (s.lvl[p_bv.toNat / 2]?.getD 0#32).toNat = s.cur_level := by
            rw [List.getElem?_eq_getElem hpv_lvl_raw, Option.getD_some, hpl_bv]
            simp [bv_c0, Nat.mod_eq_of_lt hcl_lt]
          have hidx_eq : idx - 1 + 1 = idx := Nat.sub_add_cancel hidx_pos
          have hct_succ : curTrailIdxs s mrk_l idx =
              curTrailIdxs s mrk_l (idx - 1) ++ [idx - 1] := by
            rw [← hidx_eq]; exact curTrailIdxs_succ_true (by rwa [hp_get]) (by rwa [hp_get])
          have hcl_succ : curLits s mrk_l idx =
              curLits s mrk_l (idx - 1) ++ [p_bv.toNat ^^^ 1] := by
            rw [← hidx_eq, ← hp_get]
            exact curLits_succ_true (by rwa [hp_get]) (by rwa [hp_get])
          have htc_sub : tc_l - 1 = (curTrailIdxs s mrk_l (idx - 1)).length := by
            rw [htc_eq, hct_succ, List.length_append, List.length_singleton, Nat.add_sub_cancel]
          c0_call hBump
          refine ⟨c, sl, R, rfl, hsl_len, hml, fun heur_l' mb' hhl'_ok hmb' => ?_⟩
          dsimp only [sl] at hmb'
          clear hml hsl_len sl hmnz_bv hpl_bv
          have hsub_tc : (BitVec.ofNat 64 tc_l - (1 : BitVec 64)).toNat = tc_l - 1 :=
            bv64_sub_one_toNat htc_pos htc_64
          have htc_raw : (2 ^ 64 - BitVec.toNat (1 : BitVec 64) + tc_l) % 2 ^ 64 = tc_l - 1 :=
            bv64_sub1_raw htc_pos htc_64
          fast_steps
          · -- `tmp_cnt - 1 == 0`: found 1UIP, break!
            clear ih hAc hCm hBump hQ hcore hinv hlen
            have htc_is1 : tc_l - 1 = 0 := by
              rw [htc_raw] at hc
              exact ofNat64_eq_zero (Nat.lt_of_le_of_lt (Nat.sub_le _ _) htc_64) hc
            have hent_uip :
                F0.EntailsClause (cnfClause ((p_bv ^^^ 1#32).toNat :: lowerLits tmp_l tl_l)) :=
              analyze_uip_entails hent_l hcl_succ (htc_sub ▸ htc_is1)
            have hidx_bv : BitVec.ofNat 64 idx - (1 : BitVec 64) = BitVec.ofNat 64 (idx - 1) := by
              rw [← bv_ofNat_toNat_eq (BitVec.ofNat 64 idx - (1 : BitVec 64)), hsub_nat]
            rw [hidx_bv]
            refine hJ_post (idx - 1) mrk_l tmp_l tl_l heur_l' p_bv _ hidx_lt
              (by rw [List.getElem?_eq_getElem hi_trl, ← hp_bv_def]; congr 2; exact hsub_nat.symm)
              hpl_cl hml_len htl_len htl1 htl_mv hhl'_ok (htc_sub ▸ htc_is1)
              hlow_l hcov_l hent_uip ?_
            rw [← htc_is1, ← hsub_tc]; assumption
          · -- `rcid == 0xFFFFFFFFu`: clear marks and return 0
            exact analyze_fail_cm hCm hQ
              ((hlen.with_ac (tc' := (BitVec.ofNat 64 tc_l - (1 : BitVec 64)).toNat)
                hml_len htl_len (BitVec.isLt _) htl_64).with_heur hhl'_ok)
              htl_mv (by assumption) rfl rfl rfl rfl
          · -- `rcid ≠ 0xFFFFFFFFu`: call `kissat_analyze_clause(h, rcid, pv)`
            clear hJ_post hBump
            have htc_sub_pos : 0 < tc_l - 1 := by
              have hne0 : ¬ BitVec.ofNat 64
                  ((2 ^ 64 - BitVec.toNat (1 : BitVec 64) + tc_l) % 2 ^ 64) = 0#64 := by
                assumption
              rw [htc_raw] at hne0; exact ofNat64_pos hne0
            have hrc_ne : ¬ s.rsns[p_bv.toNat / 2]'hpv_rsn_raw = 0xFFFFFFFF#32 := by
              simp only [hpv_mod] at hc; exact hc
            let rcid_bv := s.rsns[((p_bv >>> 1).setWidth 64).toNat]'hpv_rsn
            have hrc_idx : ((p_bv >>> 1).setWidth 64).toNat = p_bv.toNat / 2 := by
              rw [bv_c0_zext32_64, bv32_lshr_1]
            have hrc_eq_raw : rcid_bv = s.rsns[p_bv.toNat / 2]'hpv_rsn_raw := by
              dsimp [rcid_bv]; congr 1
            have hrc_get : s.rsns[(s.trl[idx - 1]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
                rcid_bv := by
              rw [hp_get, List.getElem?_eq_getElem hpv_rsn_raw, Option.getD_some, hrc_eq_raw]
            obtain ⟨hrc_lt, hrc_inv⟩ :=
              hcore.reason_inv (idx - 1) hidx_lt (by rw [hrc_get, hrc_eq_raw]; exact hrc_ne)
            rw [hrc_get] at hrc_lt hrc_inv
            rw [hp_get] at hrc_inv
            c0_call hAc
            refine ⟨c,
              { s with
                mrk := mrk_l, tmp := tmp_l
                tmp_cnt := (BitVec.ofNat 64 tc_l - (1 : BitVec 64)).toNat
                tmp_len := tl_l, heur := heur_l' }, R, rfl,
              ((hlen.with_ac (tc' := (BitVec.ofNat 64 tc_l - (1 : BitVec 64)).toNat)
                hml_len htl_len (BitVec.isLt _) htl_64).with_heur hhl'_ok),
              htl_mv, by dsimp only; rw [hsub_tc]; omega, by assumption, ?_⟩
            intro ok2 mrk2 tmp2 tc2 tl2 m2; dsimp only
            intro hs3_len htl2_ge htl2_le htc2_ge hmp2 htp2 hnm2 hnt2 hcnt2 hall2 hm2
            cases ok2 with
            | false =>
              fast_steps
              exact analyze_fail_cm hCm hQ hs3_len htl2_le hm2 rfl rfl rfl rfl
            | true =>
              fast_steps
              obtain ⟨htc2_eq, hlow2, hcov2, hent2⟩ :=
                analyze_resolve_sem hcore hidx_pos hidx_le htl1 htl2_ge htl2_le
                  htl_len hs3_len.tmp_len_arr htc_sub hsub_tc htc2_ge hlow_l hcov_l hent_l
                  hp_get hcl_succ hrc_lt hrc_inv hmp2 htp2 hnm2 hnt2 hcnt2 (hall2 rfl).2.2
              exact ih _ _
                (by dsimp only; rw [hsub_nat, bv64_ofNat_toNat hidx_64]
                    exact Nat.sub_lt hidx_pos Nat.one_pos)
                ⟨idx - 1, mrk2, tmp2, tc2, tl2, heur_l', Nat.le_trans (Nat.sub_le _ _) hidx_le,
                by rw [← bv_ofNat_toNat_eq (BitVec.ofNat 64 idx - (1 : BitVec 64)), hsub_nat],
                hs3_len.mrk_len, hs3_len.tmp_len_arr, Nat.le_trans htl1 htl2_ge, htl2_le, hhl'_ok,
                Nat.lt_of_lt_of_le (hsub_tc ▸ htc_sub_pos) htc2_ge,
                htc2_eq, hlow2, hcov2, hent2, hm2⟩
        · -- `lvl[pv] ≠ cur_lvl`: skip
          clear hJ_post hBump hAc hCm hQ
          have hpl_ne : ¬ s.lvl[p_bv.toNat / 2]'hpv_lvl_raw =
              (BitVec.ofNat 64 s.cur_level).setWidth 32 := by
            simp only [hpv_mod] at hc; exact hc
          refine hskip hidx_pos fun h => hpl_ne (by
            apply BitVec.eq_of_toNat_eq
            have h1 := h.2
            rw [hp_get, List.getElem?_eq_getElem hpv_lvl_raw, Option.getD_some] at h1
            simp [bv_c0, Nat.mod_eq_of_lt hcl_lt, h1])
        · -- `mrk[pv] == 0`: skip
          clear hJ_post hBump hAc hCm hQ
          simp only [hpv_mod] at hc
          refine hskip hidx_pos fun h => h.1 (by
            rw [hp_get, List.getElem?_eq_getElem hpv_mrk_raw, Option.getD_some]; exact hc)

end LeanQbe.T.Examples.Kissat.CorePlus
