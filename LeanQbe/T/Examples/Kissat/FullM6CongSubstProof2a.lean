module

public import LeanQbe.T.Examples.Kissat.FullM6CongSubstProof1b
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# Kissat M6 Congruence Closure & 2-Round Substitute Proofs — Part 2a

Proves parametric `(Γ : Env)` `Func.wp` contracts for congruence pattern matchers and queue
enqueuer, plus shared `M6EvalGateOk` / `M6HashGateOk` support (`FullM6CongSubst.lean` fns 16–18):
1. `full_cong_and_match` (`full_cong_and_match_wp`, `m6CongAndMatchSpec`)
2. `full_cong_xor_match` (`full_cong_xor_match_wp`, `m6CongXorMatchSpec`)
3. `full_cong_enq_var` (`full_cong_enq_var_wp`, `m6CongEnqVarSpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6CongSubst

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open Kraken.Bedrock2.Test
open scoped FullArenaTactics Full.FullCongTactics

namespace M6HeadTactics
open Lean Meta Elab Tactic

/-- Strict `O(1)` head-step loop unrolling `Expr.group` & join hyps and stopping before `jnz`. -/
scoped elab "m6_steps" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps
    { unrollGroup := true, splitJnz := false, strictMem := true } 10000

/-- Non-strict `O(1)` head-step loop stopping before `Expr.group`, `jnz`, and join hyps. -/
scoped elab "m6_to_group" : tactic =>
  FullM3CongBva.M3HeadTactics.m3HeadLoop
    { unrollGroup := false, splitJnz := false, strictMem := false } 10000

/-- Step only `let_`/`jump`/`ret`/`exit` and `Func.wp`/variant goals (`O(1)` without chasing
`J*` continuation hyps). -/
scoped elab "m6_let" : tactic => do
  focus do
    FullM3CongBva.M3HeadTactics.m3LetLoop 200
    FullM3CongBva.M3HeadTactics.m3NormWpHead

/-- Fast `O(1)` head splitter that unrolls `Expr.group` join wrappers, then splits `Expr.jnz`
without `c0_bound`. -/
scoped elab "m6_split_fast" : tactic => do
  focus do
    LeanQbe.T.C0HeadStep.headSteps
      { unrollGroup := true, splitJnz := false, strictMem := false } 2000
    let g ← getMainGoal
    let ty ← instantiateMVars (← g.getType)
    if ty.isAppOfArity ``LeanQbe.T.wp 6 then
      let e := (ty.getArg! 4).consumeMData
      if e.isAppOfArity ``LeanQbe.T.Expr.jnz 6 then
        let c0 := (e.getArg! 3).consumeMData
        if c0.isAppOf ``LeanQbe.T.Arg.var && c0.getAppNumArgs ≥ 2 then
          let inner0 := c0.appArg!
          let inner := FullM3CongBva.M3HeadTactics.m3PeelBlocks inner0
          if inner != inner0 then
            let cArg := Lean.mkAppN c0.getAppFn
              (c0.getAppArgs.set! (c0.getAppNumArgs - 1) inner)
            let e' := Lean.mkAppN e.getAppFn (e.getAppArgs.set! 3 cArg)
            let g' ← g.change (Lean.mkAppN ty.getAppFn (ty.getAppArgs.set! 4 e'))
              (checkDefEq := false)
            setGoals [g']
        else
          let cArg ← whnf c0
          let e' := Lean.mkAppN e.getAppFn (e.getAppArgs.set! 3 cArg)
          let g' ← g.change (Lean.mkAppN ty.getAppFn (ty.getAppArgs.set! 4 e'))
            (checkDefEq := false)
          setGoals [g']
    let hcId := Lean.mkIdent `hc
    let tac1 ← `(tactic| refine Full.FullCongTactics.wp_jnz_var (fun $hcId => ?_)
      (fun $hcId => ?_))
    let tac2 ← `(tactic| refine C0HeadStep.head_wp_jnz rfl (fun $hcId => ?_)
      (fun $hcId => ?_))
    evalTactic tac1 <|> evalTactic tac2

/-- Fast call discharge skipping full `c0_let_simp` (reduces only `vals`/`Arg.val` args). -/
scoped macro "m6_call " h:ident : tactic =>
  `(tactic| (
    refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_)
    try simp only [LeanQbe.T.vals_nil, LeanQbe.T.vals_cons,
      LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm]))

end M6HeadTactics

open scoped M6HeadTactics

/-! ## 1. Bitmask-31, XOR-Match, Queue-Frame & Gate-Evaluator Helpers (`Proof2a`) -/

section Helpers

private theorem bv32_add1_lt_of {x : BitVec 32} (h : x.toNat + 1 < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

private theorem bv32_add2_lt_of {x : BitVec 32} (h : x.toNat + 2 < 2 ^ 32) :
    (x + 2#32).toNat = x.toNat + 2 := by
  rw [BitVec.toNat_add, show (2#32 : BitVec 32).toNat = 2 from rfl, Nat.mod_eq_of_lt h]

private theorem bv64_addk_lt_of {x : BitVec 64} {k : Nat} (hk : k < 2 ^ 64)
    (h : x.toNat + k < 2 ^ 64) : (x + BitVec.ofNat 64 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt h]

private theorem list_getElem?_eq_some_of_getD {α : Type _} [Inhabited α] {l : List α}
    {i : Nat} {d v : α} (hi : i < l.length) (hd : l[i]?.getD d = v) : l[i]? = some v := by
  rw [List.getElem?_eq_getElem hi, Option.getD_some] at hd
  rw [List.getElem?_eq_getElem hi, hd]

private theorem list_getElem_of_getD {α : Type _} [Inhabited α] {xs : List α} {i : Nat}
    {d x : α} (hi : i < xs.length) (h : xs[i]?.getD d = x) : xs[i]'hi = x := by
  rwa [List.getElem?_eq_getElem hi, Option.getD_some] at h

private theorem list_drop_take_succ {α : Type _} (l : List α) {i k : Nat} (hi : i < l.length) :
    (l.drop i).take (k + 1) = l[i]'hi :: (l.drop (i + 1)).take k := by
  induction l generalizing i k with
  | nil => simp at hi
  | cons a t ih =>
    cases i with
    | zero => simp
    | succ i' =>
      simp only [List.drop_succ_cons, List.getElem_cons_succ]
      exact ih (by simp at hi; omega)

private theorem two_pow_sub_one_testBit :
    ∀ u k : Nat, k < u → (2 ^ u - 1).testBit k = true := by
  intro u; induction u with
  | zero => intro k hk; omega
  | succ u ih =>
    intro k hk
    have hpow : 1 ≤ 2 ^ u := Nat.one_le_two_pow
    have hsplit : 2 ^ (u + 1) - 1 = 2 * (2 ^ u - 1) + 1 := by
      rw [Nat.pow_succ]; omega
    rw [hsplit]
    cases k with
    | zero => simp [Nat.testBit_zero]
    | succ k' =>
      rw [Nat.testBit_succ]
      have hdiv : (2 * (2 ^ u - 1) + 1) / 2 = 2 ^ u - 1 := by omega
      rw [hdiv]; exact ih k' (by omega)

theorem testBit_full_mask_iff31 {ua : BitVec 32} (hlo : 2 ≤ ua.toNat) (hhi : ua.toNat ≤ 31)
    {k : Nat} (hk : k < ua.toNat) :
    (((1#32 <<< ua) - 1#32).toNat.testBit k) = true := by
  have hlt : 2 ^ ua.toNat < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) (by omega)
  have h1 : (1#32 <<< ua : BitVec 32).toNat = 2 ^ ua.toNat := by
    have hshl : (1#32 <<< ua : BitVec 32) = 1#32 <<< ua.toNat := rfl
    rw [hshl, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change 1 * 2 ^ ua.toNat % 2 ^ 32 = 2 ^ ua.toNat
    rw [Nat.one_mul, Nat.mod_eq_of_lt hlt]
  have hsub : ((1#32 <<< ua) - 1#32 : BitVec 32).toNat = 2 ^ ua.toNat - 1 := by
    have hle : (1#32 : BitVec 32).toNat ≤ (1#32 <<< ua : BitVec 32).toNat := by
      rw [h1]; exact Nat.one_le_two_pow
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle), h1]; rfl
  rw [hsub]; exact two_pow_sub_one_testBit ua.toNat k hk

theorem testBit_or_shl_eq31 {mask : BitVec 32} {k : BitVec 32} (hk : k.toNat < 31)
    {b : Nat} (_hb : b < 32) :
    ((mask ||| (1#32 <<< k)).toNat.testBit b) =
      (mask.toNat.testBit b || decide (b = k.toNat)) := by
  rw [BitVec.toNat_or, Nat.testBit_or]
  have hget : ((1#32 <<< k : BitVec 32).toNat.testBit b) = decide (b = k.toNat) := by
    have h1 : (1#32 <<< k : BitVec 32).toNat = 2 ^ k.toNat := by
      have hshl : (1#32 <<< k : BitVec 32) = 1#32 <<< k.toNat := rfl
      rw [hshl, BitVec.toNat_shiftLeft, show (1#32 : BitVec 32).toNat = 1 from rfl,
        Nat.shiftLeft_eq, Nat.one_mul,
        Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))]
    rw [h1, Nat.testBit_two_pow]; simp [eq_comm]
  rw [hget]

private def FullMinClrRest (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  (array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
   array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
   array (t := i32) c.pTrailPos s.core.trail_pos ⋆ array (t := i32) c.pTmp s.core.tmp) ⋆
  (FullCoreByteArrs c s.core ⋆ FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆
   fullCoreOuter c s)

private theorem focus_full_min_clr {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (FullMem c s ⋆ R) m) :
    (array (t := i32) c.pMinClr s.core.min_clr ⋆ (FullMinClrRest c s ⋆ R)) m := by
  rw [fullMem_eq_coreU32A] at hm; unfold FullCoreU32A at hm; unfold FullMinClrRest; ecancel

private theorem unfocus_full_min_clr {c : FullCfg} {s : FullState} {mclr' : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hm : (array (t := i32) c.pMinClr mclr' ⋆ (FullMinClrRest c s ⋆ R)) m) :
    (FullMem c { s with core := { s.core with min_clr := mclr' } } ⋆ R) m := by
  rw [fullMem_eq_coreU32A]; unfold FullCoreU32A; unfold FullMinClrRest at hm
  change ((array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
    array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
    array (t := i32) c.pTrailPos s.core.trail_pos ⋆ array (t := i32) c.pTmp s.core.tmp ⋆
    array (t := i32) c.pMinClr mclr') ⋆
    (FullCoreByteArrs c s.core ⋆ FullCoreU32B c s.core ⋆ FullCoreDynArrs c s.core ⋆
     fullCoreOuter c s) ⋆ R) m
  ecancel

private theorem evalLitVal_eq_xor1_eval {α : Nat → Bool} {er : BitVec 32} :
    evalLitVal α er.toNat =
      (evalLitVal α (er &&& ~~~1#32).toNat != ((er &&& 1#32) == 1#32)) := by
  rw [m6_bv32_and_not1_toNat]
  simp only [evalLitVal, litVar, litSign]
  rw [show (2 * (er.toNat / 2)) / 2 = er.toNat / 2 by omega,
    show (2 * (er.toNat / 2)) % 2 = 0 by omega]
  have hband : (er &&& 1#32).toNat = er.toNat % 2 := by
    rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one er.toNat with hm | hm
  · have hb : (er &&& 1#32) = 0#32 := BitVec.eq_of_toNat_eq (by rw [hband, hm]; rfl)
    rw [hb, hm]; simp
  · have hb : (er &&& 1#32) = 1#32 := BitVec.eq_of_toNat_eq (by rw [hband, hm]; rfl)
    rw [hb, hm]; simp

private theorem xor1_bit01_eval {α : Nat → Bool} {l b : BitVec 32}
    (hb : b = 0#32 ∨ b = 1#32) :
    evalLitVal α (l ^^^ b).toNat = ((b == 1#32) != evalLitVal α l.toNat) := by
  rcases hb with rfl | rfl
  · simp
  · rw [bv32_xor1_eq_litNeg, evalLitVal_litNeg]; cases evalLitVal α l.toNat <;> rfl

private theorem xor1_bit01_lt {l b : BitVec 32} {n : Nat} (hl : l.toNat < 2 * n)
    (hb : b = 0#32 ∨ b = 1#32) : (l ^^^ b).toNat < 2 * n := by
  rcases hb with rfl | rfl
  · simpa using hl
  · rw [bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even hl

private theorem xor_dedup_adj_step {α : Nat → Bool} {prefixL rest : List Nat} {x : Nat} :
    (xorEvalList α prefixL != xorEvalList α (x :: x :: rest)) =
      (xorEvalList α prefixL != xorEvalList α rest) := by
  rw [xorEvalList_dedup_adj]

private theorem xor_dedup_push_step {α : Nat → Bool} {prefixL rest : List Nat} {x : Nat} :
    (xorEvalList α (prefixL ++ [x]) != xorEvalList α rest) =
      (xorEvalList α prefixL != xorEvalList α (x :: rest)) := by
  rw [xorEvalList_append, xorEvalList_cons, xorEvalList_nil, xorEvalList_cons]
  cases xorEvalList α prefixL <;> cases evalLitVal α x <;> cases xorEvalList α rest <;> rfl

private theorem m6QueueCtx_set_ht {c : FullCfg} {scr : List (BitVec 32)}
    {g_len ctrl_off ht_off ht_sz : Nat}
    (hq : M6QueueCtx c scr g_len ctrl_off ht_off ht_sz) {slot : Nat} (_hslot : slot < ht_sz)
    (v : BitVec 32) :
    M6QueueCtx c (scr.set (ht_off + slot) v) g_len ctrl_off ht_off ht_sz := by
  rcases hq with rfl | ⟨occ_bkt, bkt_off, inq_off, q_off, hlay⟩
  · exact Or.inl rfl
  · right; refine ⟨occ_bkt, bkt_off, inq_off, q_off, ?_⟩
    rcases hlay with ⟨h1, h2, h3, h4, s0, s1, s2, s3, s6, s7,
      h5, h6, hpow, h7, h8, h9, h10, h11, h12, hqh, hql, hqok⟩
    refine ⟨h1, h2, h3, h4, ?_, ?_, ?_, ?_, ?_, ?_, h5, h6, hpow, h7, h8, h9, h10, h11, h12,
      ?_, ?_, ?_⟩
    · rw [List.getElem?_set_ne (by omega)]; exact s0
    · rw [List.getElem?_set_ne (by omega)]; exact s1
    · rw [List.getElem?_set_ne (by omega)]; exact s2
    · rw [List.getElem?_set_ne (by omega)]; exact s3
    · rw [List.getElem?_set_ne (by omega)]; exact s6
    · rw [List.getElem?_set_ne (by omega)]; exact s7
    · rw [List.getElem?_set_ne (by omega)]; exact hqh
    · rw [List.getElem?_set_ne (by omega)]; exact hql
    · intro k hk
      have h4 : (scr.set (ht_off + slot) v)[ctrl_off + 4]? = scr[ctrl_off + 4]? :=
        List.getElem?_set_ne (by omega)
      have h5' : (scr.set (ht_off + slot) v)[ctrl_off + 5]? = scr[ctrl_off + 5]? :=
        List.getElem?_set_ne (by omega)
      rw [h5'] at hk; rw [h4]
      have hne : ht_off + slot ≠
          q_off + ((scr[ctrl_off + 4]?.getD 0#32).toNat + k) % occ_bkt := by
        have := Nat.mod_lt ((scr[ctrl_off + 4]?.getD 0#32).toNat + k) h5; omega
      rw [List.getElem?_set_ne hne]; exact hqok k hk

@[expose] def M6ScrFrame (c : FullCfg) (g_len ctrl_off ht_off ht_sz : Nat)
    (scr0 scr : List (BitVec 32)) : Prop :=
  scr.length = c.scratch_cap ∧
  ∀ idx < c.scratch_cap, idx < ht_off →
    (ctrl_off = c.scratch_cap → scr[idx]? = scr0[idx]?) ∧
    (∀ occ_bkt bkt_off inq_off q_off,
      M6CtrlLayout c scr0 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz →
      idx ≠ ctrl_off + 5 →
      ¬ (q_off ≤ idx ∧ idx < q_off + occ_bkt) →
      ¬ (inq_off ≤ idx ∧ idx < inq_off + occ_bkt) →
      scr[idx]? = scr0[idx]?)

private theorem m6ScrFrame_refl {c : FullCfg} {g_len ctrl_off ht_off ht_sz : Nat}
    {scr0 : List (BitVec 32)} (hlen : scr0.length = c.scratch_cap) :
    M6ScrFrame c g_len ctrl_off ht_off ht_sz scr0 scr0 :=
  ⟨hlen, fun _ _ _ => ⟨fun _ => rfl, fun _ _ _ _ _ _ _ _ => rfl⟩⟩

private theorem m6ScrFrame_ht_set {c : FullCfg} {g_len ctrl_off ht_off ht_sz : Nat}
    {scr0 scr : List (BitVec 32)} (hfr : M6ScrFrame c g_len ctrl_off ht_off ht_sz scr0 scr)
    (slot : Nat) (v : BitVec 32) :
    M6ScrFrame c g_len ctrl_off ht_off ht_sz scr0 (scr.set (ht_off + slot) v) := by
  refine ⟨by rw [List.length_set]; exact hfr.1, fun idx h1 h2 => ?_⟩
  rw [List.getElem?_set_ne (by omega)]
  exact hfr.2 idx h1 h2

private theorem m6ScrFrame_pref {c : FullCfg} {g_len ctrl_off ht_off ht_sz : Nat}
    {scr0 scr scr_init : List (BitVec 32)} (hle : g_len ≤ ht_off)
    (hht : ht_off + ht_sz ≤ c.scratch_cap)
    (hpref0 : ∀ idx < g_len, scr0[idx]? = scr_init[idx]?)
    (hq0 : M6QueueCtx c scr0 g_len ctrl_off ht_off ht_sz)
    (hfr : M6ScrFrame c g_len ctrl_off ht_off ht_sz scr0 scr) :
    ∀ idx < g_len, scr[idx]? = scr_init[idx]? := by
  intro idx hidx
  have hlt_cap : idx < c.scratch_cap := by omega
  have hlt_ht : idx < ht_off := by omega
  rcases hq0 with rfl | ⟨occ_bkt, bkt_off, inq_off, q_off, hlay⟩
  · rw [(hfr.2 idx hlt_cap hlt_ht).1 rfl, hpref0 idx hidx]
  · have hlay_dup := hlay
    rcases hlay with ⟨_, _, hg_co, _, _, _, _, _, _, _, _, _, _, _, hcq, hqi, hib, hbh, _⟩
    rw [(hfr.2 idx hlt_cap hlt_ht).2 occ_bkt bkt_off inq_off q_off hlay_dup (by omega)
        (by omega) (by omega),
      hpref0 idx hidx]

private theorem m6ScrFrame_enq {c : FullCfg} {g_len ctrl_off ht_off ht_sz : Nat}
    {scr0 scr1 scr2 : List (BitVec 32)}
    (_hq0 : M6QueueCtx c scr0 g_len ctrl_off ht_off ht_sz)
    (hfr1 : M6ScrFrame c g_len ctrl_off ht_off ht_sz scr0 scr1)
    (hq1 : M6QueueCtx c scr1 g_len ctrl_off ht_off ht_sz)
    (hlen2 : scr2.length = c.scratch_cap)
    (hcap_eq : ctrl_off = c.scratch_cap → scr2 = scr1)
    (hlay2 : ∀ occ_bkt bkt_off inq_off q_off,
      M6CtrlLayout c scr1 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz →
      scr2[ctrl_off]? = some (BitVec.ofNat 32 occ_bkt) ∧
      scr2[ctrl_off + 1]? = some (BitVec.ofNat 32 bkt_off) ∧
      scr2[ctrl_off + 2]? = some (BitVec.ofNat 32 inq_off) ∧
      scr2[ctrl_off + 3]? = some (BitVec.ofNat 32 q_off) ∧
      scr2[ctrl_off + 4]? = scr1[ctrl_off + 4]? ∧
      scr2[ctrl_off + 6]? = some (BitVec.ofNat 32 ht_off) ∧
      scr2[ctrl_off + 7]? = some (BitVec.ofNat 32 ht_sz) ∧
      (∀ idx, idx ≠ ctrl_off + 5 →
        ¬ (q_off ≤ idx ∧ idx < q_off + occ_bkt) →
        ¬ (inq_off ≤ idx ∧ idx < inq_off + occ_bkt) →
        scr2[idx]? = scr1[idx]?)) :
    M6ScrFrame c g_len ctrl_off ht_off ht_sz scr0 scr2 := by
  refine ⟨hlen2, fun idx h1 h2 => ?_⟩
  refine ⟨fun hcap => ?_, fun occ_bkt bkt_off inq_off q_off hlay0 hne5 hnq hni => ?_⟩
  · rw [hcap_eq hcap]; exact (hfr1.2 idx h1 h2).1 hcap
  · rcases hq1 with hcap | ⟨o1, b1, i1, q1, hlay1⟩
    · have := hlay0.1; omega
    · have hsc := c.hscr; unfold dimacsBound at hsc
      have hlay0' := hlay0
      rcases hlay0 with ⟨_, hco8_0, _, _, s0_0, _, s0_2, s0_3, _, _, _, ho0_le, _, _,
        hcq_0, hqi_0, hib_0, hbh_0, hhc_0, _⟩
      have hlay1' := hlay1
      rcases hlay1 with ⟨_, _, _, _, s1_0, _, s1_2, s1_3, _, _, _, ho1_le, _, _,
        _, hqi_1, hib_1, hbh_1, hhc_1, _⟩
      have h_eq01 : ∀ k < 4, scr1[ctrl_off + k]? = scr0[ctrl_off + k]? := fun k hk =>
        (hfr1.2 (ctrl_off + k) (by omega) (by omega)).2 occ_bkt bkt_off inq_off q_off hlay0'
          (by omega) (by omega) (by omega)
      have heqc : ∀ {a b : Nat}, a < 2 ^ 32 → b < 2 ^ 32 →
          BitVec.ofNat 32 a = BitVec.ofNat 32 b → a = b := fun ha hb hv => by
        have h := congrArg BitVec.toNat hv
        rwa [bv32_ofNat_toNat ha, bv32_ofNat_toNat hb] at h
      have e0 := h_eq01 0 (by decide); rw [Nat.add_zero] at e0
      have ho : o1 = occ_bkt := heqc (by omega) (by omega) (by rw [← s1_0, e0, s0_0])
      have hi : i1 = inq_off :=
        heqc (by omega) (by omega) (by rw [← s1_2, h_eq01 2 (by decide), s0_2])
      have hq_eq : q1 = q_off :=
        heqc (by omega) (by omega) (by rw [← s1_3, h_eq01 3 (by decide), s0_3])
      have h2' := (hlay2 o1 b1 i1 q1 hlay1').2.2.2.2.2.2.2 idx hne5
        (by rwa [hq_eq, ho]) (by rwa [hi, ho])
      rw [h2']
      exact (hfr1.2 idx h1 h2).2 occ_bkt bkt_off inq_off q_off hlay0' hne5 hnq hni

private theorem m6CongHtInv_enq {c : FullCfg} {F_cur : List (List Nat)}
    {cv g_len ctrl_off ht_off ht_sz : Nat} {scr_init scr1 scr2 : List (BitVec 32)}
    (hht : M6CongHtInv F_cur cv scr_init scr1 g_len ht_off ht_sz)
    (hq1 : M6QueueCtx c scr1 g_len ctrl_off ht_off ht_sz)
    (hcap_eq : ctrl_off = c.scratch_cap → scr2 = scr1)
    (hlay2 : ∀ occ_bkt bkt_off inq_off q_off,
      M6CtrlLayout c scr1 g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz →
      scr2[ctrl_off]? = some (BitVec.ofNat 32 occ_bkt) ∧
      scr2[ctrl_off + 1]? = some (BitVec.ofNat 32 bkt_off) ∧
      scr2[ctrl_off + 2]? = some (BitVec.ofNat 32 inq_off) ∧
      scr2[ctrl_off + 3]? = some (BitVec.ofNat 32 q_off) ∧
      scr2[ctrl_off + 4]? = scr1[ctrl_off + 4]? ∧
      scr2[ctrl_off + 6]? = some (BitVec.ofNat 32 ht_off) ∧
      scr2[ctrl_off + 7]? = some (BitVec.ofNat 32 ht_sz) ∧
      (∀ idx, idx ≠ ctrl_off + 5 →
        ¬ (q_off ≤ idx ∧ idx < q_off + occ_bkt) →
        ¬ (inq_off ≤ idx ∧ idx < inq_off + occ_bkt) →
        scr2[idx]? = scr1[idx]?)) :
    M6CongHtInv F_cur cv scr_init scr2 g_len ht_off ht_sz := by
  intro k hk
  rcases hq1 with hcap | ⟨occ_bkt, bkt_off, inq_off, q_off, hlay⟩
  · rw [hcap_eq hcap]; exact hht k hk
  · have hlay' := hlay
    rcases hlay with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h_co, h_qi, h_ib, h_bh, _⟩
    have heq := (hlay2 occ_bkt bkt_off inq_off q_off hlay').2.2.2.2.2.2.2 (ht_off + k)
      (by omega) (by omega) (by omega)
    rw [heq]; exact hht k hk

private theorem m6CtrlLayout_frame_refl {c : FullCfg} {scr : List (BitVec 32)}
    {g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz : Nat}
    (hscrl : scr.length = c.scratch_cap)
    (hlay : M6CtrlLayout c scr g_len ctrl_off occ_bkt bkt_off inq_off q_off ht_off ht_sz) :
    scr[ctrl_off]? = some (BitVec.ofNat 32 occ_bkt) ∧
    scr[ctrl_off + 1]? = some (BitVec.ofNat 32 bkt_off) ∧
    scr[ctrl_off + 2]? = some (BitVec.ofNat 32 inq_off) ∧
    scr[ctrl_off + 3]? = some (BitVec.ofNat 32 q_off) ∧
    scr[ctrl_off + 4]? = scr[ctrl_off + 4]? ∧
    scr[ctrl_off + 6]? = some (BitVec.ofNat 32 ht_off) ∧
    scr[ctrl_off + 7]? = some (BitVec.ofNat 32 ht_sz) ∧
    (∀ idx, idx ≠ ctrl_off + 5 →
      ¬ (q_off ≤ idx ∧ idx < q_off + occ_bkt) →
      ¬ (inq_off ≤ idx ∧ idx < inq_off + occ_bkt) →
      scr[idx]? = scr[idx]?) := by
  rcases hlay with ⟨_, hco8, _, _, s0, s1, s2, s3, s6, s7, _⟩
  exact ⟨list_getElem?_eq_some_of_getD (by omega) s0,
    list_getElem?_eq_some_of_getD (by omega) s1,
    list_getElem?_eq_some_of_getD (by omega) s2,
    list_getElem?_eq_some_of_getD (by omega) s3, rfl,
    list_getElem?_eq_some_of_getD (by omega) s6,
    list_getElem?_eq_some_of_getD (by omega) s7, fun _ _ _ _ => rfl⟩

private theorem m6DenseInvW_with_scr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hd : FullDenseInvW c F0 F_cur s)
    {scr' : List (BitVec 32)} (hl : scr'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with scratch_buf := scr' } } :=
  ⟨⟨hd.1.core_ok, { hd.1.scratch_ok with scratch_buf_len := hl }⟩,
   hd.2.1, hd.2.2.1, hd.2.2.2.1,
   fullExtScratchOk_of_eq hd.2.2.2.2.1 rfl rfl rfl rfl,
   hd.2.2.2.2.2.1, hd.2.2.2.2.2.2⟩

end Helpers


/-! ## 2. `full_cong_and_match_wp` & `full_cong_xor_match_wp` & `full_cong_enq_var_wp` -/

section MatchersAndQueue

theorem full_cong_and_match_wp (Γ : Env)
    (hFind : ∀ a m Q X, fullCongFindSpec a m Q X →
      Γ "full_cong_find" [i64, i32] [i32] a m Q X) :
    ∀ a m Q X, m6CongAndMatchSpec a m Q X →
      Func.wp Γ full_cong_and_match_body a m Q X := by
  rintro ⟨h, ent, ua, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, scr0, g_len, R, rfl, hlen, hw, hcl0, hrepr0, hg_cap, hpref,
     hgat, htag0, hua_cv, hm0, hQ⟩
  have hsc := c.hscr; have hmx := c.hmaxv; unfold dimacsBound at hsc hmx
  have hcv_le := hlen.core_ok.cur_vars_le
  have hrl0 := hlen.core_ok.repr_len
  have htmpl0 := hlen.core_ok.tmp_len_arr
  have hscrl0 := hlen.scratch_ok.scratch_buf_len
  obtain ⟨lhs_ent, mword, he0, he1, _, hbd_e, _, _, hrhs_e, hsem_e⟩ := hgat
  have htag0' : (mword >>> 28).toNat = 0 := by
    rw [he1, Option.getD_some] at htag0; simpa using congrArg BitVec.toNat htag0
  obtain ⟨_, ha2_e, hand_e⟩ | ⟨ht_ne, _⟩ | ⟨ht_ne, _⟩ := hsem_e <;> (try omega)
  let ea := mword &&& 0xFF#32
  have ha_eq : ea.toNat = (mword &&& 0xFF#32).toNat := rfl
  let rhs := ((scr0.drop (ent.toNat + 2)).take ea.toNat).map BitVec.toNat
  have hrl_rhs : rhs.length = ea.toNat := by
    simp only [rhs, List.length_map, List.length_take, List.length_drop]
    rcases Nat.eq_zero_or_pos ea.toNat with hz | hpos
    · exact Nat.min_eq_left (by omega)
    · obtain ⟨_, hr, _⟩ := hrhs_e (ea.toNat - 1) (by rw [ha_eq] at *; omega)
      have := (List.getElem?_eq_some_iff.mp hr).1; omega
  have he1_n : (ent.setWidth 64 + 1).toNat = ent.toNat + 1 := by
    rw [BitVec.toNat_add, bv_zext32_toNat]
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [h1]; exact Nat.mod_eq_of_lt (by omega)
  have he1_arr : (ent.setWidth 64 + 1).toNat < s.scratch.scratch_buf.length := by omega
  have hst_e1 : s.scratch.scratch_buf[(ent.setWidth 64 + 1).toNat]'he1_arr = mword := by
    have h := (hpref (ent.toNat + 1) (by omega)).trans he1
    rw [← he1_n, List.getElem?_eq_getElem he1_arr] at h; exact Option.some.inj h
  m6_split_fast
  · m6_steps; exact hQ false s.core.repr m0 hrl0 hrepr0 (fun h => by cases h) hm0
  · have h2_le_ua : 2 ≤ ua.toNat := by
      have h2_val : ((2 : BitVec 32).toNat) = 2 := rfl
      simp only [BitVec.ult, h2_val, decide_eq_false_iff_not] at hc; omega
    m6_split_fast
    · m6_steps; exact hQ false s.core.repr m0 hrl0 hrepr0 (fun h => by cases h) hm0
    · have hua_le_31 : ua.toNat ≤ 31 := by
        have h31_val : ((31 : BitVec 32).toNat) = 31 := rfl
        simp only [BitVec.ult, h31_val, decide_eq_false_iff_not] at hc; omega
      m6_steps
      refine wp_loop_inv
        (fun (mask, j, ()) mj => ∃ reprj : List (BitVec 32),
          reprj.length = 2 * c.max_vars ∧ j.toNat ≤ ea.toNat ∧
          FullCongReprInv F_cur (2 * s.core.cur_vars) reprj ∧
          (∀ p (hp : p < j.toNat), ∃ er < 2 * s.core.cur_vars,
            LitEquiv (cnfOfClauses F_cur) (rhs[p]?.getD 0) er ∧
            (s.core.vals[er]?.getD 0#8 = 1#8 ∨
              ∃ k < ua.toNat, er = (s.core.tmp[k]?.getD 0#32).toNat)) ∧
          (∀ b < 32, mask.toNat.testBit b = true → b < ua.toNat ∧
            ∃ p < j.toNat, LitEquiv (cnfOfClauses F_cur)
              (rhs[p]?.getD 0) (s.core.tmp[b]?.getD 0#32).toNat) ∧
          (FullMem c { s with core := { s.core with repr := reprj } } ⋆ R) mj)
        (fun (_, j, ()) _ => ea.toNat - j.toNat)
        (fun J hJ => by
          m6_let
          exact hJ (0#32, 0#32, ()) m0 ⟨s.core.repr, hrl0, Nat.zero_le _, hrepr0,
            fun _ h => absurd h (by simp), fun _ _ h => by simp at h, hm0⟩)
        (fun J (mask, j, ()) mj ⟨reprj, hrlj, hj_le, hreprj, hfwdj, hbwdj, hmj⟩ ihj => ?_)
      let stj : FullState := { s with core := { s.core with repr := reprj } }
      have hlenj : stj.LengthsOk c := ⟨{ hlen.core_ok with repr_len := hrlj }, hlen.scratch_ok⟩
      have hwj : FullWitnessInv c F0 F_cur stj.core := fullWitnessInv_with_repr hw reprj
      m6_split_fast
      · have hj_lt : j.toNat < ea.toNat := by
          simp only [BitVec.ult, decide_eq_true_eq] at hc; rw [hst_e1] at hc; exact hc
        obtain ⟨rv, hrv_get, hrv_lt⟩ := hrhs_e j.toNat hj_lt
        have hrhs_j : rhs[j.toNat]?.getD 0 = rv.toNat := by
          simp only [rhs, List.getElem?_map, List.getElem?_take,
            ite_eq_left (by omega : j.toNat < ea.toNat), List.getElem?_drop, hrv_get]
          rfl
        have he2j_lt : ent.toNat + 2 + j.toNat < c.scratch_cap := by rw [ha_eq] at *; omega
        have he2j_n : (ent.setWidth 64 + 2 + j.setWidth 64).toNat = ent.toNat + 2 + j.toNat :=
          bv64_add_zext32 (k := 2) (by rw [bv_zext32_toNat]; omega)
        have he2j_arr : (ent.setWidth 64 + 2 + j.setWidth 64).toNat <
            stj.scratch.scratch_buf.length := by
          rw [he2j_n]; dsimp [stj]; exact Nat.lt_of_lt_of_le he2j_lt (Nat.le_of_eq hscrl0.symm)
        have hst_e2j : stj.scratch.scratch_buf[(ent.setWidth 64 + 2 + j.setWidth 64).toNat]'
            he2j_arr = rv := by
          have h := (hpref (ent.toNat + 2 + j.toNat) (by omega)).trans hrv_get
          rw [← he2j_n, List.getElem?_eq_getElem he2j_arr] at h; exact Option.some.inj h
        have hj1_n : (j + 1#32).toNat = j.toNat + 1 := bv32_add1_lt_of (by omega)
        m6_steps; m6_call hFind
        refine ⟨F_cur, 2 * s.core.cur_vars, reprj, FullReprRest c stj ⋆ R, hreprj,
          by rw [hst_e2j]; exact hrv_lt, focus_full_repr hmj,
          fun er repr_e me hrl_e hrepr_e _ her_lt her_eqv hme => ?_⟩
        let ste : FullState := { stj with core := { stj.core with repr := repr_e } }
        have hme' : (FullMem c ste ⋆ R) me := unfocus_full_repr hme; clear hme
        have hw_e : FullWitnessInv c F0 F_cur ste.core := fullWitnessInv_with_repr hwj repr_e
        have her_vals : (er.setWidth 64).toNat < ste.core.vals.length := by
          rw [bv_zext32_toNat]; dsimp [ste, stj]; rw [hlen.core_ok.vals_len]; omega
        have her_vals' : er.toNat < ste.core.vals.length := by
          rw [bv_zext32_toNat] at her_vals; exact her_vals
        have hrv_er_eqv : LitEquiv (cnfOfClauses F_cur) (rhs[j.toNat]?.getD 0) er.toNat := by
          rw [hrhs_j]; rwa [hst_e2j] at her_eqv
        have hev_dom : ste.core.vals[er.toNat]'her_vals' = 0#8 ∨
            ste.core.vals[er.toNat]'her_vals' = 1#8 ∨
            ste.core.vals[er.toNat]'her_vals' = 0xFF#8 := by
          have hd := hw_e.vals_domain er.toNat her_lt
          rwa [List.getElem?_eq_getElem her_vals', Option.getD_some] at hd
        m6_split_fast
        · m6_steps
          exact hQ false repr_e me (by omega) hrepr_e (fun h => by cases h) hme'
        · have hev_nslt : ¬ (ste.core.vals[er.toNat]'her_vals').slt 0#8 = true :=
            bv8_not_slt0_of_signExtend32_nslt0 hev_dom (by
              rw [list_getElem_congr (bv_zext32_toNat er) her_vals her_vals'] at hc; exact hc)
          m6_split_fast
          · have hev_eq0 : s.core.vals[er.toNat]?.getD 0#8 = 0#8 := by
              have hv0 : ste.core.vals[er.toNat]'her_vals' = 0#8 :=
                bv8_eq0_of_signExtend32 hev_dom (by
                  have hc' := beq_iff_eq.mp hc
                  rw [list_getElem_congr (bv_zext32_toNat er) her_vals her_vals'] at hc'; exact hc')
              rw [List.getElem?_eq_getElem (by rw [hlen.core_ok.vals_len]; omega),
                Option.getD_some]
              exact hv0
            m6_to_group
            refine wp_loop_break_group (brkTs := [i32, .bool, i32]) (lpTs := [i32])
              (fun (mask_b, found, _, ()) mb => mb = me ∧
                (found = true → ∃ k < ua.toNat, er = (s.core.tmp[k]?.getD 0#32) ∧
                  ∀ b < 32, mask_b.toNat.testBit b = true → b < ua.toNat ∧
                    (b = k ∨ ∃ p < j.toNat, LitEquiv (cnfOfClauses F_cur)
                      (rhs[p]?.getD 0) (s.core.tmp[b]?.getD 0#32).toNat)))
              (fun rem (k, ()) mk => mk = me ∧ k.toNat ≤ ua.toNat ∧ rem = ua.toNat - k.toNat)
              ?_ ?_ ?_
            · rintro _ ⟨mask_b, found, _, ⟨⟩⟩ mb ⟨hmb_eq, hfb⟩
              subst mb
              m6_split_fast
              · obtain ⟨k, hk_lt, htmp_k, hmask_b⟩ := hfb hc
                m6_steps
                refine ihj (mask_b, j + 1#32, ()) me (by dsimp only; omega)
                  ⟨repr_e, by omega, by omega, hrepr_e, ?_, ?_, hme'⟩
                · intro p hp
                  rw [hj1_n] at hp
                  by_cases hpj : p = j.toNat
                  · subst hpj
                    refine ⟨er.toNat, her_lt, hrv_er_eqv, Or.inr ⟨k, hk_lt, ?_⟩⟩
                    rw [htmp_k]
                  · exact hfwdj p (by omega)
                · intro b hb htb
                  obtain ⟨hb_ua, hbk | ⟨p, hp, heq⟩⟩ := hmask_b b hb htb
                  · refine ⟨hb_ua, j.toNat, by omega, ?_⟩
                    subst hbk; rwa [← htmp_k]
                  · exact ⟨hb_ua, p, by omega, heq⟩
              · m6_steps
                exact hQ false repr_e me (by omega) hrepr_e (fun h => by cases h) hme'
            · rintro Bk Lk rem ⟨k, ⟨⟩⟩ mk hBk hLk ⟨hmk_eq, hk_le, rfl⟩
              subst mk
              m6_split_fast
              · have hk_lt : k.toNat < ua.toNat := by
                  simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                have hk_tmp : (k.setWidth 64).toNat < ste.core.tmp.length := by
                  rw [bv_zext32_toNat]; dsimp [ste, stj]; omega
                have hk_tmp' : k.toNat < ste.core.tmp.length := by
                  rw [bv_zext32_toNat] at hk_tmp; exact hk_tmp
                have hk1_n : (k + 1#32).toNat = k.toNat + 1 := bv32_add1_lt_of (by omega)
                m6_split_fast
                · have htmp_eq : s.core.tmp[k.toNat]?.getD 0#32 = er := by
                    have h1 : ste.core.tmp[k.toNat]'hk_tmp' = er := by
                      have hc' := beq_iff_eq.mp hc
                      rw [list_getElem_congr (bv_zext32_toNat k) hk_tmp hk_tmp'] at hc'
                      exact hc'
                    change s.core.tmp[k.toNat]'_ = er at h1
                    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact h1
                  have hk_31 : k.toNat < 31 := by omega
                  m6_steps
                  have hkm : ((1 : BitVec 32) <<< (k.toNat % 32)) = 1#32 <<< k := by
                    rw [Nat.mod_eq_of_lt (by omega)]; rfl
                  rw [hkm]
                  refine hBk (mask ||| (1#32 <<< k), true, k, ()) me ⟨rfl, fun _ =>
                    ⟨k.toNat, hk_lt, htmp_eq.symm, fun b hb htb => ?_⟩⟩
                  rw [testBit_or_shl_eq31 hk_31 hb, Bool.or_eq_true, decide_eq_true_eq] at htb
                  rcases htb with htb | rfl
                  · obtain ⟨hb_ua, p, hp, heq⟩ := hbwdj b hb htb
                    exact ⟨hb_ua, Or.inr ⟨p, hp, heq⟩⟩
                  · exact ⟨hk_lt, Or.inl rfl⟩
                · m6_steps
                  exact hLk (ua.toNat - (k + 1#32).toNat) (k + 1#32, ()) me (by omega)
                    ⟨rfl, by omega, rfl⟩
              · m6_steps; exact hBk (mask, false, k, ()) me ⟨rfl, fun h => by cases h⟩
            · intro _ Lk _ hLk; m6_let; exact hLk ua.toNat (0#32, ()) me ⟨rfl, Nat.zero_le _, rfl⟩
          · have hev_eq1 : s.core.vals[er.toNat]?.getD 0#8 = 1#8 := by
              have hne0 : (ste.core.vals[er.toNat]'her_vals').signExtend 32 ≠ 0#32 := by
                have hc' := beq_eq_false_iff_ne.mp hc
                rw [list_getElem_congr (bv_zext32_toNat er) her_vals her_vals'] at hc'; exact hc'
              have h1 := bv8_eq1_of_signExtend32_ne0_nslt0 hev_dom hne0 hev_nslt
              rw [List.getElem?_eq_getElem (by rw [hlen.core_ok.vals_len]; omega),
                Option.getD_some]
              exact h1
            m6_steps
            refine ihj (mask, j + 1#32, ()) me (by dsimp only; omega)
              ⟨repr_e, by omega, by omega, hrepr_e, ?_, ?_, hme'⟩
            · intro p hp
              rw [hj1_n] at hp
              by_cases hpj : p = j.toNat
              · subst hpj; exact ⟨er.toNat, her_lt, hrv_er_eqv, Or.inl hev_eq1⟩
              · exact hfwdj p (by omega)
            · intro b hb htb
              obtain ⟨hb_ua, p, hp, heq⟩ := hbwdj b hb htb
              exact ⟨hb_ua, p, by omega, heq⟩
      · have hj_eq : j.toNat = ea.toNat := by
          simp only [BitVec.ult, decide_eq_false_iff_not] at hc; rw [hst_e1] at hc
          change ¬ j.toNat < ea.toNat at hc; omega
        rw [hj_eq] at hfwdj hbwdj
        m6_steps
        have hm_mod : ((1 : BitVec 32) <<< (ua.toNat % 32)) = 1#32 <<< ua := by
          rw [Nat.mod_eq_of_lt (by omega)]; rfl
        rw [hm_mod]
        refine hQ (mask == (1#32 <<< ua) - 1#32) reprj mj hrlj hreprj ?_ hmj
        intro htrue
        have hm_eq : mask = (1#32 <<< ua) - 1#32 := beq_iff_eq.mp htrue
        refine ⟨h2_le_ua, hua_le_31, ?_⟩
        rw [he0, Option.getD_some]
        refine andMatch_sound_equiv hwj hcl0 hand_e ?_ ?_
        · intro p hp
          have hp' : p < ea.toNat := by rw [← hrl_rhs]; exact hp
          have h1 := hfwdj p hp'
          dsimp only [rhs] at h1
          rw [List.getElem?_eq_getElem hp, Option.getD_some] at h1
          exact h1
        · intro k hk
          have htb : mask.toNat.testBit k = true := by
            rw [hm_eq]; exact testBit_full_mask_iff31 h2_le_ua hua_le_31 hk
          have ⟨_, p, hp, heq⟩ := hbwdj k (by omega) htb
          rw [← hrl_rhs] at hp
          exact ⟨p, hp, heq⟩

theorem full_cong_xor_match_wp (Γ : Env)
    (hFind : ∀ a m Q X, fullCongFindSpec a m Q X →
      Γ "full_cong_find" [i64, i32] [i32] a m Q X)
    (hSort : ∀ a m Q X, fullSortU32Spec a m Q X →
      Γ "full_sort_u32" [i64, i32] [] a m Q X) :
    ∀ a m Q X, m6CongXorMatchSpec a m Q X →
      Func.wp Γ full_cong_xor_match_body a m Q X := by
  rintro ⟨h, ent, ua, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, scr0, g_len, R, rfl, hlen, hw, hcl0, hrepr0, hcv2, hg_cap, hpref,
     hgat, htag1, hua_cv, htmp_lt, hm0, hQ⟩
  have hsc := c.hscr; have hmx := c.hmaxv; unfold dimacsBound at hsc hmx
  have hcv_le := hlen.core_ok.cur_vars_le
  have hrl0 := hlen.core_ok.repr_len
  have hml0 := hlen.core_ok.min_clr_len_arr
  have htmpl0 := hlen.core_ok.tmp_len_arr
  have hscrl0 := hlen.scratch_ok.scratch_buf_len
  obtain ⟨lhs_ent, mword, he0, he1, hlhs_lt, hbd_e, _, _, hrhs_e, hsem_e⟩ := hgat
  have htag1' : (mword >>> 28).toNat = 1 := by
    rw [he1, Option.getD_some] at htag1; simpa using congrArg BitVec.toNat htag1
  obtain ⟨ht_ne, _⟩ | ⟨_, ha2_e, ha4_e, hxor_e⟩ | ⟨ht_ne, _⟩ := hsem_e <;> (try omega)
  let ea := mword &&& 0xFF#32
  have ha_eq : ea.toNat = (mword &&& 0xFF#32).toNat := rfl
  let erhs := ((scr0.drop (ent.toNat + 2)).take ea.toNat).map BitVec.toNat
  have hrl_erhs : erhs.length = ea.toNat := by
    simp only [erhs, List.length_map, List.length_take, List.length_drop]
    obtain ⟨_, hr, _⟩ := hrhs_e (ea.toNat - 1) (by rw [ha_eq]; omega)
    have := (List.getElem?_eq_some_iff.mp hr).1; omega
  have he0_n : (ent.setWidth 64).toNat = ent.toNat := bv_zext32_toNat ent
  have he0_arr : (ent.setWidth 64).toNat < s.scratch.scratch_buf.length := by omega
  have hst_e0 : s.scratch.scratch_buf[(ent.setWidth 64).toNat]'he0_arr = lhs_ent := by
    have h := (hpref ent.toNat (by omega)).trans he0
    rw [← he0_n, List.getElem?_eq_getElem he0_arr] at h; exact Option.some.inj h
  have he1_n : (ent.setWidth 64 + 1).toNat = ent.toNat + 1 := by
    rw [BitVec.toNat_add, bv_zext32_toNat]
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [h1]; exact Nat.mod_eq_of_lt (by omega)
  have he1_arr : (ent.setWidth 64 + 1).toNat < s.scratch.scratch_buf.length := by omega
  have hst_e1 : s.scratch.scratch_buf[(ent.setWidth 64 + 1).toNat]'he1_arr = mword := by
    have h := (hpref (ent.toNat + 1) (by omega)).trans he1
    rw [← he1_n, List.getElem?_eq_getElem he1_arr] at h; exact Option.some.inj h
  have hmiss0 : ∀ (reprx mclrx : List (BitVec 32)) mx,
      reprx.length = 2 * c.max_vars → mclrx.length = c.max_vars →
      FullCongReprInv F_cur (2 * s.core.cur_vars) reprx →
      (FullMem c { s with core := { s.core with repr := reprx, min_clr := mclrx } } ⋆ R) mx →
      Q (0xFFFFFFFF#32, ()) mx := fun reprx mclrx mx hr hx hinv hm =>
    hQ 0xFFFFFFFF#32 reprx mclrx mx hr hx hinv (fun h => absurd rfl h) hm
  m6_split_fast
  · m6_steps; exact hmiss0 s.core.repr s.core.min_clr m0 hrl0 hml0 hrepr0 hm0
  · have h2_ua : 2 ≤ ua.toNat := by
      have h2_v : ((2 : BitVec 32).toNat) = 2 := rfl
      simp only [BitVec.ult, h2_v, decide_eq_false_iff_not] at hc; omega
    m6_split_fast
    · m6_steps; exact hmiss0 s.core.repr s.core.min_clr m0 hrl0 hml0 hrepr0 hm0
    · have hua_4 : ua.toNat ≤ 4 := by
        have h4_v : ((4 : BitVec 32).toNat) = 4 := rfl
        simp only [BitVec.ult, h4_v, decide_eq_false_iff_not] at hc; omega
      m6_split_fast
      · m6_steps; exact hmiss0 s.core.repr s.core.min_clr m0 hrl0 hml0 hrepr0 hm0
      · clear hc; m6_split_fast
        · m6_steps; exact hmiss0 s.core.repr s.core.min_clr m0 hrl0 hml0 hrepr0 hm0
        · clear hc; m6_split_fast
          · m6_steps; exact hmiss0 s.core.repr s.core.min_clr m0 hrl0 hml0 hrepr0 hm0
          · clear hc; m6_split_fast
            · m6_steps; exact hmiss0 s.core.repr s.core.min_clr m0 hrl0 hml0 hrepr0 hm0
            · clear hc; m6_split_fast
              · m6_steps; exact hmiss0 s.core.repr s.core.min_clr m0 hrl0 hml0 hrepr0 hm0
              · have hea_cv : ea.toNat ≤ s.core.cur_vars := by
                  rw [hst_e1] at hc
                  simp only [BitVec.ult, decide_eq_false_iff_not, BitVec.toNat_setWidth,
                    BitVec.toNat_ofNat] at hc
                  change ¬ s.core.cur_vars % 2 ^ 64 < ea.toNat % 2 ^ 64 at hc
                  have h1 : s.core.cur_vars % 2 ^ 64 = s.core.cur_vars :=
                    Nat.mod_eq_of_lt (by omega)
                  have h2 : ea.toNat % 2 ^ 64 = ea.toNat :=
                    Nat.mod_eq_of_lt (by rw [ha_eq]; omega)
                  rw [h1, h2] at hc; omega
                clear hc; m6_steps
                refine wp_loop_inv (ts := [i32, i32, i32])
                  (fun (eflip, ena, j, ()) mj => ∃ (reprj mclrj : List (BitVec 32)),
                    reprj.length = 2 * c.max_vars ∧ mclrj.length = c.max_vars ∧
                    j.toNat ≤ ea.toNat ∧ ena.toNat ≤ j.toNat ∧
                    (eflip = 0#32 ∨ eflip = 1#32) ∧
                    FullCongReprInv F_cur (2 * s.core.cur_vars) reprj ∧
                    (∀ q < ena.toNat, (mclrj[q]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
                    (∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
                      xorEvalList α (erhs.take j.toNat) =
                        ((eflip == 1#32) !=
                          xorEvalList α ((mclrj.take ena.toNat).map BitVec.toNat))) ∧
                    (FullMem c { s with core :=
                      { s.core with repr := reprj, min_clr := mclrj } } ⋆ R) mj)
                  (fun (_, _, j, ()) _ => ea.toNat - j.toNat)
                  (fun J hJ => by
                    m6_let
                    exact hJ (0#32, 0#32, 0#32, ()) m0
                      ⟨s.core.repr, s.core.min_clr, hrl0, hml0, Nat.zero_le _, Nat.zero_le _,
                       Or.inl rfl, hrepr0, (fun _ h => by cases h),
                       (fun _ _ => by
                         simp only [show (0#32 : BitVec 32).toNat = 0 from rfl,
                           List.take_zero, List.map_nil, xorEvalList_nil,
                           show ((0#32 : BitVec 32) == 1#32) = false from rfl,
                           Bool.false_bne]), hm0⟩)
                  (fun J (eflip, ena, j, ()) mj
                    ⟨reprj, mclrj, hrlj, hmlj, hj_le, hena_le, hfl_bv, hreprj, hmclr_lt,
                     hxor_j, hmj⟩ ihj => ?_)
                next =>
                  let stj : FullState :=
                    { s with core := { s.core with repr := reprj, min_clr := mclrj } }
                  m6_split_fast
                  · have hj_lt : j.toNat < ea.toNat := by
                      simp only [BitVec.ult, decide_eq_true_eq] at hc
                      rw [hst_e1] at hc; exact hc
                    have hj_lt_m : j.toNat < (mword &&& 0xFF#32).toNat := by
                      rw [← ha_eq]; exact hj_lt
                    obtain ⟨rv, hrv_get, hrv_lt⟩ := hrhs_e j.toNat hj_lt
                    have herhs_j : erhs[j.toNat]?.getD 0 = rv.toNat := by
                      simp only [erhs, List.getElem?_map, List.getElem?_take,
                        ite_eq_left (by omega : j.toNat < ea.toNat), List.getElem?_drop, hrv_get]
                      rfl
                    have he2j_n :
                        (ent.setWidth 64 + 2 + j.setWidth 64).toNat = ent.toNat + 2 + j.toNat :=
                      bv64_add_zext32 (k := 2) (by rw [bv_zext32_toNat]; omega)
                    have he2j_arr : (ent.setWidth 64 + 2 + j.setWidth 64).toNat <
                        stj.scratch.scratch_buf.length := by
                      rw [he2j_n]; dsimp [stj]; omega
                    have hst_e2j : stj.scratch.scratch_buf[
                        (ent.setWidth 64 + 2 + j.setWidth 64).toNat]'he2j_arr = rv := by
                      have h := (hpref (ent.toNat + 2 + j.toNat) (by omega)).trans hrv_get
                      rw [← he2j_n, List.getElem?_eq_getElem he2j_arr] at h; exact Option.some.inj h
                    have hj1_n : (j + 1#32).toNat = j.toNat + 1 :=
                      bv32_add1_lt_of (by rw [ha_eq] at *; omega)
                    have hena1_n : (ena + 1#32).toNat = ena.toNat + 1 :=
                      bv32_add1_lt_of (by rw [ha_eq] at *; omega)
                    have hena_arr : (ena.setWidth 64).toNat < stj.core.min_clr.length := by
                      rw [bv_zext32_toNat]; dsimp [stj]; omega
                    m6_steps; m6_call hFind
                    refine ⟨F_cur, 2 * s.core.cur_vars, reprj, FullReprRest c stj ⋆ R, hreprj,
                      by rw [hst_e2j]; exact hrv_lt, focus_full_repr hmj,
                      fun er repr_e me hrl_e hrepr_e _ her_lt her_eqv hme => ?_⟩
                    let ste : FullState :=
                      { s with core := { s.core with repr := repr_e, min_clr := mclrj } }
                    have hme' : (FullMem c ste ⋆ R) me := by
                      simpa [ste, stj] using unfocus_full_repr hme
                    clear hme
                    have hw_e : FullWitnessInv c F0 F_cur ste.core :=
                      fullWitnessInv_with_min_clr (fullWitnessInv_with_repr hw repr_e) mclrj
                    have her_vals : (er.setWidth 64).toNat < ste.core.vals.length := by
                      rw [bv_zext32_toNat]; dsimp [ste]; rw [hlen.core_ok.vals_len]; omega
                    have her_vals' : er.toNat < ste.core.vals.length := by
                      rw [bv_zext32_toNat] at her_vals; exact her_vals
                    have hrv_er_eqv :
                        LitEquiv (cnfOfClauses F_cur) (erhs[j.toNat]?.getD 0) er.toNat := by
                      rw [herhs_j]; rwa [hst_e2j] at her_eqv
                    have hev_dom : ste.core.vals[er.toNat]'her_vals' = 0#8 ∨
                        ste.core.vals[er.toNat]'her_vals' = 1#8 ∨
                        ste.core.vals[er.toNat]'her_vals' = 0xFF#8 := by
                      have hd := hw_e.vals_domain er.toNat her_lt
                      rwa [List.getElem?_eq_getElem her_vals', Option.getD_some] at hd
                    have htake_succ : erhs.take (j.toNat + 1) =
                        erhs.take j.toNat ++ [rv.toNat] := by
                      have hj_erhs : j.toNat < erhs.length := by omega
                      have hget : erhs[j.toNat]'hj_erhs = rv.toNat := by
                        rwa [List.getElem?_eq_getElem hj_erhs, Option.getD_some] at herhs_j
                      rw [List.take_succ_eq_append_getElem hj_erhs, hget]
                    m6_to_group
                    refine wp_join_group (ts := [i32, i32])
                      (fun (eflip', ena', ()) mf => ∃ mclrf : List (BitVec 32),
                        mclrf.length = c.max_vars ∧ ena'.toNat ≤ j.toNat + 1 ∧
                        (eflip' = 0#32 ∨ eflip' = 1#32) ∧
                        (∀ q < ena'.toNat, (mclrf[q]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
                        (∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
                          xorEvalList α (erhs.take (j.toNat + 1)) =
                            ((eflip' == 1#32) !=
                              xorEvalList α ((mclrf.take ena'.toNat).map BitVec.toNat))) ∧
                        (FullMem c { s with core :=
                          { s.core with repr := repr_e, min_clr := mclrf } } ⋆ R) mf)
                      (fun _ ⟨eflip', ena', ⟨⟩⟩ mf
                        ⟨mclrf, hmlf, henaf, hflf, hmclrf_lt, hxorf, hmf⟩ => by
                        m6_let; exact ihj (eflip', ena', j + 1#32, ()) mf
                          (by dsimp only; omega)
                          ⟨repr_e, mclrf, hrl_e.trans hrlj, hmlf, by omega, hj1_n ▸ henaf, hflf,
                           hrepr_e, hmclrf_lt, fun α hα => hj1_n ▸ hxorf α hα, hmf⟩)
                      ?_
                    intro Jstep hJstep; m6_split_fast
                    · have hev_ne : ste.core.vals[er.toNat]?.getD 0#8 ≠ 0#8 := by
                        rw [List.getElem?_eq_getElem her_vals', Option.getD_some]
                        exact bv8_ne0_of_signExtend32 hev_dom (by
                          rw [list_getElem_congr (bv_zext32_toNat er) her_vals her_vals'] at hc
                          exact bne_iff_ne.mp hc)
                      m6_to_group
                      refine wp_join_group (ts := [i32])
                        (fun (eflip', ()) mf => mf = me ∧ (eflip' = 0#32 ∨ eflip' = 1#32) ∧
                          ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
                            xorEvalList α (erhs.take (j.toNat + 1)) =
                              ((eflip' == 1#32) !=
                                xorEvalList α ((mclrj.take ena.toNat).map BitVec.toNat)))
                        (fun _ ⟨eflip', ⟨⟩⟩ mf ⟨rfl, hfl', hxor'⟩ => by
                          m6_let
                          exact hJstep (eflip', ena, ()) mf
                            ⟨mclrj, hmlj, by omega, hfl', hmclr_lt, hxor', hme'⟩)
                        ?_
                      intro Jt hJt; m6_split_fast
                      · have hev_1 : s.core.vals[er.toNat]?.getD 0#8 = 1#8 :=
                          vals_sgt0_eq1 (by rw [hlen.core_ok.vals_len]; omega) her_vals
                            (hw_e.vals_domain er.toNat her_lt) hc
                        m6_let
                        refine hJt (eflip ^^^ 1#32, ()) me ⟨rfl, ?_, fun α hα => ?_⟩
                        · rcases hfl_bv with rfl | rfl <;> simp
                        · have hev_tr : evalLitVal α rv.toNat = true := by
                            rw [← herhs_j, litEquiv_eval hα hrv_er_eqv]
                            exact entails_eval_true (vals1_entails hw_e hcl0 her_lt hev_1) hα
                          rw [htake_succ, xorEvalList_append, hxor_j α hα]
                          change (((eflip == 1#32) != _) != (evalLitVal α rv.toNat != false)) =
                            ((eflip ^^^ 1#32 == 1#32) != _)
                          rw [hev_tr]; rcases hfl_bv with rfl | rfl <;>
                            cases xorEvalList α ((mclrj.take ena.toNat).map BitVec.toNat) <;> rfl
                      · have hev_ff : s.core.vals[er.toNat]?.getD 0#8 = 0xFF#8 :=
                          vals_ne0_nsgt0_eqff (by rw [hlen.core_ok.vals_len]; omega) her_vals
                            (hw_e.vals_domain er.toNat her_lt)
                            (by rcases hev_dom with h0 | h1 | hff
                                · rw [List.getElem?_eq_getElem her_vals',
                                    Option.getD_some] at hev_ne
                                  exact absurd h0 hev_ne
                                · rw [List.getElem?_eq_getElem her_vals', Option.getD_some]
                                  exact Or.inl h1
                                · rw [List.getElem?_eq_getElem her_vals', Option.getD_some]
                                  exact Or.inr hff)
                            hc
                        m6_let
                        refine hJt (eflip, ()) me ⟨rfl, hfl_bv, fun α hα => ?_⟩
                        have hev_fl : evalLitVal α rv.toNat = false := by
                          rw [← herhs_j, litEquiv_eval hα hrv_er_eqv]
                          exact entails_neg_eval_false
                            (valsff_entails_neg hw_e hcl0 her_lt hev_ff) hα
                        rw [htake_succ, xorEvalList_append, hxor_j α hα]
                        change (((eflip == 1#32) != _) != (evalLitVal α rv.toNat != false)) =
                          ((eflip == 1#32) != _)
                        rw [hev_fl]; simp
                    · clear hc; m6_let
                      let e0 := er &&& ~~~1#32
                      let mclrf := mclrj.set ena.toNat e0
                      have he0_lt : e0.toNat < 2 * s.core.cur_vars := by
                        dsimp only [e0]; rw [m6_bv32_and_not1_toNat]; omega
                      have hena_ste : (ena.setWidth 64).toNat < ste.core.min_clr.length := hena_arr
                      refine wp_store_sep
                        (FullArenaTactics.c0_store_full_min_clr e0 hena_ste hme') ?_
                      intro mf hmf
                      have hmf' : (FullMem c { s with core :=
                          { s.core with repr := repr_e, min_clr := mclrf } } ⋆ R) mf := by
                        simpa only [ste, mclrf, bv_zext32_toNat] using hmf
                      m6_let
                      refine hJstep (eflip ^^^ (er &&& 1#32), ena + 1#32, ()) mf
                        ⟨mclrf, by simp [mclrf, hmlj], by omega, ?_, fun q hq => ?_,
                         fun α hα => ?_, hmf'⟩
                      · have h0n : (0#32 : BitVec 32).toNat = 0 := rfl
                        have h1n : (1#32 : BitVec 32).toNat = 1 := rfl
                        have hbit : (er &&& 1#32) = 0#32 ∨ (er &&& 1#32) = 1#32 := by
                          have h1 : (er &&& 1#32).toNat < 2 := by
                            rw [BitVec.toNat_and, h1n, Nat.and_one_is_mod]
                            exact Nat.mod_lt _ (by decide)
                          rcases Nat.mod_two_eq_zero_or_one (er &&& 1#32).toNat with hm | hm
                          · left; exact BitVec.eq_of_toNat_eq (by rw [h0n]; omega)
                          · right; exact BitVec.eq_of_toNat_eq (by rw [h1n]; omega)
                        rcases hfl_bv with rfl | rfl <;> rcases hbit with h0 | h1 <;>
                          first | (rw [h0]; decide) | (rw [h1]; decide)
                      · dsimp only [mclrf]; rw [hena1_n] at hq
                        by_cases hqe : q = ena.toNat
                        · subst hqe; rw [List.getElem?_set_self (by omega), Option.getD_some]
                          exact he0_lt
                        · rw [List.getElem?_set_ne (Ne.symm hqe)]; exact hmclr_lt q (by omega)
                      · rw [htake_succ, xorEvalList_append, hxor_j α hα, hena1_n]
                        have htk_m : (mclrf.take (ena.toNat + 1)).map BitVec.toNat =
                            (mclrj.take ena.toNat).map BitVec.toNat ++ [e0.toNat] := by
                          dsimp only [mclrf]
                          have hl1 : ena.toNat + 1 ≤ (mclrj.set ena.toNat e0).length := by
                            rw [List.length_set]; omega
                          rw [List.take_succ_eq_append_getElem (by rw [List.length_set]; omega),
                            List.getElem_set_self (by omega), List.take_set_of_le (Nat.le_refl _),
                            List.map_append]
                          rfl
                        rw [htk_m, xorEvalList_append]
                        have hev_rv : evalLitVal α rv.toNat = evalLitVal α er.toNat := by
                          rw [← herhs_j]; exact litEquiv_eval hα hrv_er_eqv
                        change (((eflip == 1#32) != _) != (evalLitVal α rv.toNat != false)) =
                          ((eflip ^^^ (er &&& 1#32) == 1#32) !=
                            (_ != (evalLitVal α e0.toNat != false)))
                        rw [hev_rv, evalLitVal_eq_xor1_eval (er := er)]
                        have h0n : (0#32 : BitVec 32).toNat = 0 := rfl
                        have h1n : (1#32 : BitVec 32).toNat = 1 := rfl
                        have hbit : (er &&& 1#32) = 0#32 ∨ (er &&& 1#32) = 1#32 := by
                          have h1 : (er &&& 1#32).toNat < 2 := by
                            rw [BitVec.toNat_and, h1n, Nat.and_one_is_mod]
                            exact Nat.mod_lt _ (by decide)
                          rcases Nat.mod_two_eq_zero_or_one (er &&& 1#32).toNat with hm | hm
                          · left; exact BitVec.eq_of_toNat_eq (by rw [h0n]; omega)
                          · right; exact BitVec.eq_of_toNat_eq (by rw [h1n]; omega)
                        rcases hfl_bv with rfl | rfl <;> rcases hbit with hb | hb <;>
                          simp only [hb] <;>
                          cases xorEvalList α ((mclrj.take ena.toNat).map BitVec.toNat) <;>
                          cases evalLitVal α (er &&& ~~~1#32).toNat <;> rfl
                  · have hj_eq : j.toNat = ea.toNat := by
                      simp only [BitVec.ult, decide_eq_false_iff_not] at hc
                      rw [hst_e1] at hc; change ¬ j.toNat < ea.toNat at hc; omega
                    rw [hj_eq] at hxor_j
                    have htake_all : erhs.take ea.toNat = erhs :=
                      List.take_of_length_le (by omega)
                    rw [htake_all] at hxor_j
                    clear hc; m6_split_fast
                    · m6_steps; exact hmiss0 reprj mclrj mj hrlj hmlj hreprj hmj
                    · have hua_ena : ua.toNat ≤ ena.toNat := by
                        simp only [BitVec.ult, decide_eq_false_iff_not] at hc; omega
                      have hena_cv : ena.toNat ≤ s.core.cur_vars := by omega
                      clear hc; m6_to_group
                      refine wp_join_group (ts := [])
                        (fun () ms => ∃ mclrs : List (BitVec 32),
                          mclrs.length = c.max_vars ∧
                          (∀ q < ena.toNat, (mclrs[q]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
                          (∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
                            xorEvalList α erhs = ((eflip == 1#32) !=
                              xorEvalList α ((mclrs.take ena.toNat).map BitVec.toNat))) ∧
                          (FullMem c { s with core :=
                            { s.core with repr := reprj, min_clr := mclrs } } ⋆ R) ms)
                        ?_ ?_
                      · rintro _ ⟨⟩ ms ⟨mclrs, hmls, hmclrs_lt, hxors, hms⟩
                        let P_d : Tup Val [i32, i32] → Mem 64 → Prop :=
                          fun (jd', eua', ()) md' => ∃ mclrd' : List (BitVec 32),
                            mclrd'.length = c.max_vars ∧ eua'.toNat ≤ jd'.toNat ∧
                            jd'.toNat ≤ ena.toNat ∧
                            (∀ q, jd'.toNat ≤ q → q < ena.toNat → mclrd'[q]? = mclrs[q]?) ∧
                            (∀ q < eua'.toNat,
                              (mclrd'[q]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
                            (∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
                              xorEvalList α erhs = ((eflip == 1#32) !=
                                (xorEvalList α ((mclrd'.take eua'.toNat).map BitVec.toNat) !=
                                 xorEvalList α
                                   (((mclrs.drop jd'.toNat).take (ena.toNat - jd'.toNat)).map
                                     BitVec.toNat)))) ∧
                            (FullMem c { s with core :=
                              { s.core with repr := reprj, min_clr := mclrd' } } ⋆ R) md'
                        m6_let; refine wp_loop_inv (ts := [i32, i32]) P_d
                          (fun (jd, _, ()) _ => ena.toNat - jd.toNat)
                          (fun Jd hJd => by
                            m6_let
                            refine hJd (0#32, 0#32, ()) ms ⟨mclrs, hmls, Nat.zero_le _,
                              Nat.zero_le _, (fun _ _ _ => rfl), (fun _ h => by cases h),
                              fun α hα => ?_, hms⟩
                            rw [hxors α hα]
                            simp only [show (0#32 : BitVec 32).toNat = 0 from rfl,
                              List.take_zero, List.map_nil, xorEvalList_nil,
                              Nat.sub_zero, List.drop_zero, Bool.false_bne])
                          (fun Jd (jd, eua, ()) md ⟨mclrd, hmld, heua_le, hjd_le, htail_d,
                            hmclrd_lt, hxord, hmd⟩ ihd => ?_)
                        m6_split_fast
                        · have hjd_lt : jd.toNat < ena.toNat := by
                            dsimp only at hc; exact bv32_ult_lt hc
                          clear hc
                          have hjd1_n : (jd + 1#32).toNat = jd.toNat + 1 :=
                            bv32_add1_lt_of (by omega)
                          let std : FullState :=
                            { s with core := { s.core with repr := reprj, min_clr := mclrd } }
                          m6_to_group
                          refine wp_join_group (ts := [i32, i32])
                            (fun x mp =>
                              (ena.toNat - x.1.toNat < ena.toNat - jd.toNat) ∧ P_d x mp)
                            (fun _ ⟨jd', eua', ⟨⟩⟩ mp ⟨hdec, hP⟩ => by
                              m6_let; exact ihd (jd', eua', ()) mp hdec hP)
                            ?_
                          intro Js hJs; m6_to_group
                          refine wp_join_group (ts := []) (fun () mp => mp = md) ?_ ?_
                          · rintro _ ⟨⟩ mp rfl
                            have hjd_arr : (jd.setWidth 64).toNat < std.core.min_clr.length := by
                              rw [bv_zext32_toNat]; dsimp [std]; omega
                            have heua_arr :
                                (eua.setWidth 64).toNat < std.core.min_clr.length := by
                              rw [bv_zext32_toNat]; dsimp [std]; omega
                            have heua1_n : (eua + 1#32).toNat = eua.toNat + 1 :=
                              bv32_add1_lt_of (by omega)
                            let vjd := mclrd[(jd.setWidth 64).toNat]'hjd_arr
                            have hvjd_eq : vjd = mclrs[jd.toNat]?.getD 0#32 := by
                              have hjd_m : jd.toNat < mclrd.length := by omega
                              have hv0 : vjd = mclrd[jd.toNat]'hjd_m :=
                                list_getElem_congr (bv_zext32_toNat jd) hjd_arr hjd_m
                              have hg := htail_d jd.toNat (Nat.le_refl _) hjd_lt
                              rw [List.getElem?_eq_getElem (by omega)] at hg
                              rw [hv0, ← hg, Option.getD_some]
                            let mclrd' := mclrd.set eua.toNat vjd
                            m6_let; refine wp_load_of (FullArenaTactics.c0_load_full_min_clr
                              hjd_arr hmd) ?_
                            m6_let; refine wp_store_sep (FullArenaTactics.c0_store_full_min_clr
                              vjd heua_arr hmd) ?_
                            intro md' hmd'
                            have hmd'' : (FullMem c { s with core :=
                                { s.core with repr := reprj, min_clr := mclrd' } } ⋆ R) md' := by
                              simpa only [std, mclrd', vjd, bv_zext32_toNat] using hmd'
                            m6_let; refine hJs (jd + 1#32, eua + 1#32, ()) md'
                              ⟨by dsimp only; rw [hjd1_n]; omega,
                               ⟨mclrd', by simp [mclrd', hmld],
                                by rw [heua1_n, hjd1_n]; omega,
                                by rw [hjd1_n]; omega,
                                fun q hq1 hq2 => by
                                  dsimp only [mclrd']; rw [hjd1_n] at hq1
                                  rw [List.getElem?_set_ne (by omega)]
                                  exact htail_d q (by omega) hq2,
                                fun q hq => by
                                  dsimp only [mclrd']; rw [heua1_n] at hq
                                  by_cases hqe : q = eua.toNat
                                  · subst hqe; rw [List.getElem?_set_self (by omega),
                                      Option.getD_some, hvjd_eq]
                                    exact hmclrs_lt jd.toNat hjd_lt
                                  · rw [List.getElem?_set_ne (Ne.symm hqe)]
                                    exact hmclrd_lt q (by omega),
                                fun α hα => ?_, hmd''⟩⟩
                            rw [hxord α hα, heua1_n, hjd1_n]
                            have htk_new : (mclrd'.take (eua.toNat + 1)).map BitVec.toNat =
                                (mclrd.take eua.toNat).map BitVec.toNat ++ [vjd.toNat] := by
                              dsimp only [mclrd']
                              rw [List.take_succ_eq_append_getElem
                                  (by rw [List.length_set]; omega),
                                List.getElem_set_self (by rw [List.length_set]; omega),
                                List.take_set_of_le (Nat.le_refl _), List.map_append]; rfl
                            have hdp_old :
                                ((mclrs.drop jd.toNat).take (ena.toNat - jd.toNat)).map
                                  BitVec.toNat =
                                vjd.toNat :: (((mclrs.drop (jd.toNat + 1)).take
                                  (ena.toNat - (jd.toNat + 1))).map BitVec.toNat) := by
                              have h_0 : vjd = mclrs[jd.toNat]'(by omega) := by
                                rw [hvjd_eq, List.getElem?_eq_getElem (by omega),
                                  Option.getD_some]
                              rw [h_0, ← List.map_cons]; congr 1
                              have hsub1 : ena.toNat - jd.toNat =
                                  (ena.toNat - (jd.toNat + 1)) + 1 := by omega
                              rw [hsub1, list_drop_take_succ mclrs (by omega)]
                            rw [htk_new, hdp_old, xor_dedup_push_step]
                          · intro Jp hJp; m6_split_fast
                            · have hjd1_lt : jd.toNat + 1 < ena.toNat := by
                                dsimp only at hc; rw [← hjd1_n]; exact bv32_ult_lt hc
                              have hjd_arr : (jd.setWidth 64).toNat < std.core.min_clr.length := by
                                rw [bv_zext32_toNat]; dsimp [std]; omega
                              have hjd1_arr : ((jd + 1#32).setWidth 64).toNat <
                                  std.core.min_clr.length := by
                                rw [bv_zext32_toNat]; dsimp [std]; omega
                              m6_steps; m6_split_fast
                              · have heq_d : mclrd[(jd.setWidth 64).toNat]'hjd_arr =
                                    mclrd[((jd + 1#32).setWidth 64).toNat]'hjd1_arr := by
                                  dsimp only at hc; exact beq_iff_eq.mp hc
                                have hsame :
                                    mclrs[jd.toNat]?.getD 0#32 =
                                      mclrs[jd.toNat + 1]?.getD 0#32 := by
                                  have hjd_m : jd.toNat < mclrd.length := by omega
                                  have hjd1_m : jd.toNat + 1 < mclrd.length := by omega
                                  have hl : mclrd[(jd.setWidth 64).toNat]'hjd_arr =
                                      mclrd[jd.toNat]'hjd_m :=
                                    list_getElem_congr (bv_zext32_toNat jd) hjd_arr hjd_m
                                  have hr :
                                      mclrd[((jd + 1#32).setWidth 64).toNat]'hjd1_arr =
                                        mclrd[jd.toNat + 1]'hjd1_m :=
                                    list_getElem_congr (by rw [bv_zext32_toNat, hjd1_n])
                                      hjd1_arr hjd1_m
                                  have heq_d' : mclrd[jd.toNat]'hjd_m =
                                      mclrd[jd.toNat + 1]'hjd1_m :=
                                    hl.symm.trans (heq_d.trans hr)
                                  rw [← htail_d jd.toNat (Nat.le_refl _) hjd_lt,
                                    ← htail_d (jd.toNat + 1) (by omega) hjd1_lt,
                                    List.getElem?_eq_getElem (by omega),
                                    List.getElem?_eq_getElem (by omega), Option.getD_some,
                                    Option.getD_some, heq_d']
                                have hjd2_n : (jd + 2#32).toNat = jd.toNat + 2 :=
                                  bv32_add2_lt_of (by omega)
                                m6_let; refine hJs (jd + 2#32, eua, ()) md
                                  ⟨by dsimp only; rw [hjd2_n]; omega,
                                   ⟨mclrd, hmld, by omega, by rw [hjd2_n]; omega,
                                    fun q hq1 hq2 => by
                                      rw [hjd2_n] at hq1; exact htail_d q (by omega) hq2,
                                    hmclrd_lt, fun α hα => ?_, hmd⟩⟩
                                rw [hxord α hα]
                                have hslice :
                                    ((mclrs.drop jd.toNat).take (ena.toNat - jd.toNat)).map
                                      BitVec.toNat =
                                    (mclrs[jd.toNat]?.getD 0#32).toNat ::
                                      (mclrs[jd.toNat + 1]?.getD 0#32).toNat ::
                                      (((mclrs.drop (jd.toNat + 2)).take
                                        (ena.toNat - (jd.toNat + 2))).map BitVec.toNat) := by
                                  have h_0 : mclrs[jd.toNat]?.getD 0#32 =
                                      mclrs[jd.toNat]'(by omega) := by
                                    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                                  have h_1 : mclrs[jd.toNat + 1]?.getD 0#32 =
                                      mclrs[jd.toNat + 1]'(by omega) := by
                                    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                                  have hsub1 : ena.toNat - jd.toNat =
                                      (ena.toNat - (jd.toNat + 1)) + 1 := by omega
                                  have hsub2 : ena.toNat - (jd.toNat + 1) =
                                      (ena.toNat - (jd.toNat + 2)) + 1 := by omega
                                  rw [h_0, h_1, ← List.map_cons, ← List.map_cons]; congr 1
                                  rw [hsub1, list_drop_take_succ mclrs (by omega),
                                    hsub2, list_drop_take_succ mclrs (by omega)]
                                rw [hjd2_n, hslice, hsame, xor_dedup_adj_step]
                              · m6_let; exact hJp () md rfl
                            · m6_let; exact hJp () md rfl
                        · have hjd_eq : jd.toNat = ena.toNat := by
                            dsimp only at hc; have := bv32_ult_not_lt hc; omega
                          rw [hjd_eq, Nat.sub_self, List.take_zero, List.map_nil] at hxord
                          clear hc; m6_split_fast
                          · m6_steps; exact hmiss0 reprj mclrd md hrlj hmld hreprj hmd
                          · have heua_eq : eua = ua := by
                              dsimp only at hc
                              have hnot : (eua != ua) = false := hc
                              by_cases heq : eua = ua
                              · exact heq
                              · exfalso; rw [bne_iff_ne.mpr heq] at hnot; cases hnot
                            subst heua_eq; clear hc; m6_steps
                            refine wp_loop_inv (ts := [i32])
                              (fun (jk, ()) mk => mk = md ∧ jk.toNat ≤ eua.toNat ∧
                                ∀ q < jk.toNat, mclrd[q]? = s.core.tmp[q]?)
                              (fun (jk, ()) _ => eua.toNat - jk.toNat)
                              (fun Jk hJk => by
                                m6_let; exact hJk (0#32, ()) md ⟨rfl, Nat.zero_le _,
                                  fun _ h => by cases h⟩)
                              (fun Jk (jk, ()) mk ⟨hmk_eq, hjk_le, hjk_eq⟩ ihk => ?_)
                            subst mk; m6_split_fast
                            · have hjk_lt : jk.toNat < eua.toNat := bv32_ult_lt hc
                              have hjk_mclr : (jk.setWidth 64).toNat < mclrd.length := by
                                rw [bv_zext32_toNat]; omega
                              have hjk_tmp : (jk.setWidth 64).toNat < s.core.tmp.length := by
                                rw [bv_zext32_toNat]; omega
                              have hjk1 : (jk + 1#32).toNat = jk.toNat + 1 :=
                                bv32_add1_lt_of (by omega)
                              m6_steps; m6_split_fast
                              · m6_steps; exact hmiss0 reprj mclrd md hrlj hmld hreprj hmd
                              · have heq_q : mclrd[jk.toNat]? = s.core.tmp[jk.toNat]? := by
                                  have hnot : (mclrd[(jk.setWidth 64).toNat]'hjk_mclr !=
                                      s.core.tmp[(jk.setWidth 64).toNat]'hjk_tmp) = false := hc
                                  have heq : mclrd[(jk.setWidth 64).toNat]'hjk_mclr =
                                      s.core.tmp[(jk.setWidth 64).toNat]'hjk_tmp := by
                                    by_cases hne :
                                        mclrd[(jk.setWidth 64).toNat]'hjk_mclr =
                                          s.core.tmp[(jk.setWidth 64).toNat]'hjk_tmp
                                    · exact hne
                                    · exfalso
                                      have : (mclrd[(jk.setWidth 64).toNat]'hjk_mclr !=
                                          s.core.tmp[(jk.setWidth 64).toNat]'hjk_tmp) = true :=
                                        bne_iff_ne.mpr hne
                                      rw [this] at hnot; cases hnot
                                  have heq1 : mclrd[jk.toNat]'(by omega) =
                                      s.core.tmp[jk.toNat]'(by omega) := by
                                    rw [← list_getElem_congr (bv_zext32_toNat jk) hjk_mclr
                                        (by omega),
                                      ← list_getElem_congr (bv_zext32_toNat jk) hjk_tmp (by omega)]
                                    exact heq
                                  rw [List.getElem?_eq_getElem (by omega),
                                    List.getElem?_eq_getElem (by omega), heq1]
                                m6_let; refine ihk (jk + 1#32, ()) md (by dsimp only; omega)
                                  ⟨rfl, by omega, fun q hq => by
                                    rw [hjk1] at hq
                                    by_cases hqq : q = jk.toNat
                                    · subst hqq; exact heq_q
                                    · exact hjk_eq q (by omega)⟩
                            · have hjk_eq_e : jk.toNat = eua.toNat := by
                                have := bv32_ult_not_lt hc; omega
                              rw [hjk_eq_e] at hjk_eq; clear hc
                              let std : FullState :=
                                { s with core := { s.core with repr := reprj, min_clr := mclrd } }
                              m6_steps; m6_call hFind
                              refine ⟨F_cur, 2 * s.core.cur_vars, reprj,
                                FullReprRest c std ⋆ R, hreprj, by rw [hst_e0]; exact hlhs_lt,
                                focus_full_repr hmd,
                                fun rl repr_f mf hrl_f hrepr_f _ hrl_lt hrl_eqv hmf => ?_⟩
                              have hmf' : (FullMem c { s with core :=
                                  { s.core with repr := repr_f, min_clr := mclrd } } ⋆ R) mf := by
                                simpa [std] using unfocus_full_repr hmf
                              clear hmf; m6_steps
                              refine hQ (rl ^^^ eflip) repr_f mclrd mf (hrl_f.trans hrlj) hmld
                                hrepr_f (fun _ => ⟨h2_ua, hua_4, xor1_bit01_lt hrl_lt hfl_bv,
                                  fun α hα => ?_⟩) hmf'
                              rw [xor1_bit01_eval hfl_bv]
                              have hlhs_rl :
                                  evalLitVal α rl.toNat = evalLitVal α lhs_ent.toNat := by
                                rw [hst_e0] at hrl_eqv; exact (litEquiv_eval hα hrl_eqv).symm
                              rw [hlhs_rl, hxor_e α hα, List.map_take]
                              have hx_d := hxord α hα
                              change xorEvalList α erhs = ((eflip == 1#32) !=
                                (xorEvalList α ((mclrd.take eua.toNat).map BitVec.toNat) !=
                                  xorEvalList α [])) at hx_d
                              rw [show xorEvalList α [] = false from rfl, Bool.bne_false] at hx_d
                              have htk_eq : mclrd.take eua.toNat = s.core.tmp.take eua.toNat := by
                                apply List.ext_getElem
                                · simp [hmld, htmpl0]
                                · intro q hq _; simp only [List.length_take, hmld] at hq
                                  have hq_u : q < eua.toNat := by omega
                                  have he := hjk_eq q hq_u
                                  rw [List.getElem?_eq_getElem (by omega),
                                    List.getElem?_eq_getElem (by omega)] at he
                                  simpa [List.getElem_take] using Option.some.inj he
                              dsimp only [erhs] at hx_d
                              rw [List.map_take, ha_eq] at hx_d
                              rw [hx_d, htk_eq, List.map_take]
                              cases (eflip == 1#32) <;>
                                cases xorEvalList α
                                  (List.take eua.toNat (List.map BitVec.toNat s.core.tmp)) <;>
                                rfl
                      · intro Js hJs; m6_split_fast
                        · m6_steps; m6_call hSort
                          refine ⟨mclrj, FullMinClrRest c { s with core :=
                              { s.core with repr := reprj, min_clr := mclrj } } ⋆ R,
                            by omega, focus_full_min_clr hmj,
                            fun mclrs ms hmls hperm _ hms => ?_⟩
                          have hms' : (FullMem c { s with core :=
                              { s.core with repr := reprj, min_clr := mclrs } } ⋆ R) ms :=
                            unfocus_full_min_clr hms
                          m6_let; refine hJs () ms ⟨mclrs, hmls.trans hmlj, fun q hq => ?_,
                            fun α hα => ?_, hms'⟩
                          · have hmem : mclrs[q]'(by omega) ∈ mclrj.take ena.toNat :=
                              hperm.mem_iff.mp (mem_take_of_lt hq (by omega))
                            obtain ⟨q0, hq0, hget0⟩ := lt_take_of_mem hmem
                            have hq0_lt : q0 < mclrj.length := by omega
                            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                            rw [List.getElem?_eq_getElem hq0_lt, Option.getD_some] at hget0
                            have h1 := hmclr_lt q0 (by omega)
                            rw [List.getElem?_eq_getElem hq0_lt, Option.getD_some] at h1
                            rwa [hget0] at h1
                          · rw [hxor_j α hα, xorEvalList_perm α (List.Perm.map _ hperm)]
                        · m6_let; exact hJs () mj ⟨mclrj, hmlj, hmclr_lt, hxor_j, hmj⟩

theorem full_cong_enq_var_wp (_Γ : Env) :
    ∀ a m Q X, m6CongEnqVarSpec a m Q X → Func.wp _Γ full_cong_enq_var_body a m Q X := by
  rintro ⟨h, ctrl_off, v, ⟨⟩⟩ m0 Q X ⟨c, s, g_len, ht_off, ht_sz, R, rfl, hlen, hq0, hm0, hQ⟩
  have hsc := c.hscr; have hmx := c.hmaxv; unfold dimacsBound at hsc hmx
  have hscrl0 := hlen.scratch_ok.scratch_buf_len
  m6_split_fast
  · m6_steps
    refine hQ s.scratch.scratch_buf m0 hscrl0 hq0 (fun _ => rfl)
      (fun o b i q hlay => m6CtrlLayout_frame_refl hscrl0 hlay) hm0
  · have hco_lt : ctrl_off.toNat < c.scratch_cap := by
      first
      | (simp only [BitVec.ule, decide_eq_false_iff_not, BitVec.toNat_ofNat,
           Nat.mod_eq_of_lt (by omega : c.scratch_cap < 2 ^ 64)] at hc; omega)
      | (simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat,
           Nat.mod_eq_of_lt (by omega : c.scratch_cap < 2 ^ 64)] at hc; exact hc)
    m6_split_fast
    · m6_steps
      refine hQ s.scratch.scratch_buf m0 hscrl0 hq0 (fun hcap => absurd hcap (by omega))
        (fun o b i q hlay => m6CtrlLayout_frame_refl hscrl0 hlay) hm0
    · obtain ⟨occ_bkt, bkt_off, inq_off, q_off, hlay⟩ := hq0.elim
        (fun hcap => absurd hcap (by omega)) id
      have hlay_dup := hlay
      rcases hlay with ⟨h_co_cap, h_co8, hg_co, hg24, h_occ, h_bkt, h_inq, h_q, h_ht_o, h_ht_s,
        h_opos, h_ole, hpow, h_hpos, h_oq, h_qi, h_ib, h_bh, h_hc, h_qh, h_ql, h_qok⟩
      have hco_n : ctrl_off.toNat < s.scratch.scratch_buf.length := by omega
      have hco2_n : (ctrl_off + 2#64).toNat = ctrl_off.toNat + 2 :=
        bv64_addk_lt_of (by decide) (by omega)
      have hco3_n : (ctrl_off + 3#64).toNat = ctrl_off.toNat + 3 :=
        bv64_addk_lt_of (by decide) (by omega)
      have hco4_n : (ctrl_off + 4#64).toNat = ctrl_off.toNat + 4 :=
        bv64_addk_lt_of (by decide) (by omega)
      have hco5_n : (ctrl_off + 5#64).toNat = ctrl_off.toNat + 5 :=
        bv64_addk_lt_of (by decide) (by omega)
      have hco2_arr : (ctrl_off + 2#64).toNat < s.scratch.scratch_buf.length := by omega
      have hco3_arr : (ctrl_off + 3#64).toNat < s.scratch.scratch_buf.length := by omega
      have hco4_arr : (ctrl_off + 4#64).toNat < s.scratch.scratch_buf.length := by omega
      have hco5_arr : (ctrl_off + 5#64).toNat < s.scratch.scratch_buf.length := by omega
      have hs0 : s.scratch.scratch_buf[ctrl_off.toNat]'hco_n = BitVec.ofNat 32 occ_bkt :=
        list_getElem_of_getD hco_n h_occ
      have hs2 : s.scratch.scratch_buf[(ctrl_off + 2#64).toNat]'hco2_arr =
          BitVec.ofNat 32 inq_off :=
        list_getElem_of_getD hco2_arr (by rw [hco2_n]; exact h_inq)
      have hs3 : s.scratch.scratch_buf[(ctrl_off + 3#64).toNat]'hco3_arr = BitVec.ofNat 32 q_off :=
        list_getElem_of_getD hco3_arr (by rw [hco3_n]; exact h_q)
      have hocc_eq : (s.scratch.scratch_buf[ctrl_off.toNat]'hco_n).toNat = occ_bkt := by
        rw [hs0, bv32_ofNat_toNat (by omega)]
      let b := v &&& (s.scratch.scratch_buf[ctrl_off.toNat]'hco_n - 1#32)
      have hb_lt : b.toNat < occ_bkt := by
        have := m6_bv32_and_sub1_lt (x := v) (n := s.scratch.scratch_buf[ctrl_off.toNat]'hco_n)
          (by rw [hocc_eq]; exact h_opos)
        rwa [hocc_eq] at this
      have hinqb_n :
          ((s.scratch.scratch_buf[(ctrl_off + 2#64).toNat]'hco2_arr).setWidth 64 +
            b.setWidth 64).toNat = inq_off + b.toNat := by
        rw [hs2, BitVec.toNat_add, bv_zext32_toNat, bv_zext32_toNat, bv32_ofNat_toNat (by omega)]
        exact Nat.mod_eq_of_lt (by omega)
      have hinqb_arr : ((s.scratch.scratch_buf[(ctrl_off + 2#64).toNat]'hco2_arr).setWidth 64 +
          b.setWidth 64).toNat < s.scratch.scratch_buf.length := by
        rw [hinqb_n]; omega
      m6_split_fast
      · clear hc; m6_split_fast
        · have hql_lt :
              (s.scratch.scratch_buf[(ctrl_off + 5#64).toNat]'hco5_arr).toNat < occ_bkt := by
            simp only [BitVec.ult, decide_eq_true_eq] at hc
            rwa [hocc_eq] at hc
          let q_head := s.scratch.scratch_buf[(ctrl_off + 4#64).toNat]'hco4_arr
          let q_len := s.scratch.scratch_buf[(ctrl_off + 5#64).toNat]'hco5_arr
          have hql_v : q_len.toNat < occ_bkt := hql_lt
          let tail := (q_head + q_len) &&& (s.scratch.scratch_buf[ctrl_off.toNat]'hco_n - 1#32)
          have htail_lt : tail.toNat < occ_bkt := by
            have := m6_bv32_and_sub1_lt (x := q_head + q_len)
              (n := s.scratch.scratch_buf[ctrl_off.toNat]'hco_n) (by rw [hocc_eq]; exact h_opos)
            rwa [hocc_eq] at this
          have hqh_v : q_head.toNat < occ_bkt := by
            dsimp only [q_head]; rw [← Option.getD_some (a := _[ _ ]) (b := 0#32),
              ← List.getElem?_eq_getElem hco4_arr, hco4_n]; exact h_qh
          have htail_mod : tail.toNat = (q_head.toNat + q_len.toNat) % occ_bkt := by
            dsimp only [tail]; rw [hs0, m6_and_sub1_u32_eq_mod hpow]
            have hsum : (q_head + q_len).toNat = q_head.toNat + q_len.toNat := by
              rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
            rw [hsum]
          have hqt_n : ((s.scratch.scratch_buf[(ctrl_off + 3#64).toNat]'hco3_arr).setWidth 64 +
              tail.setWidth 64).toNat = q_off + tail.toNat := by
            rw [hs3, BitVec.toNat_add, bv_zext32_toNat, bv_zext32_toNat,
              bv32_ofNat_toNat (by omega)]
            exact Nat.mod_eq_of_lt (by omega)
          have hqt_arr : ((s.scratch.scratch_buf[(ctrl_off + 3#64).toNat]'hco3_arr).setWidth 64 +
              tail.setWidth 64).toNat < s.scratch.scratch_buf.length := by
            rw [hqt_n]; omega
          have hql1 : (q_len + 1#32).toNat = q_len.toNat + 1 := bv32_add1_lt_of (by omega)
          let scr1 := s.scratch.scratch_buf.set (inq_off + b.toNat) 1#32
          let scr2 := scr1.set (q_off + tail.toNat) b
          let scr3 := scr2.set (ctrl_off.toNat + 5) (q_len + 1#32)
          have hscrl3 : scr3.length = c.scratch_cap := by simp [scr3, scr2, scr1, hscrl0]
          have hql_n : q_len.toNat =
              (s.scratch.scratch_buf[ctrl_off.toNat + 5]?.getD 0#32).toNat := by
            dsimp only [q_len]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
            exact congrArg BitVec.toNat (list_getElem_congr hco5_n hco5_arr (by omega))
          have hqh_n : q_head.toNat =
              (s.scratch.scratch_buf[ctrl_off.toNat + 4]?.getD 0#32).toNat := by
            dsimp only [q_head]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
            exact congrArg BitVec.toNat (list_getElem_congr hco4_n hco4_arr (by omega))
          have hsame_idx : ∀ i < 8, i ≠ 5 → scr3[ctrl_off.toNat + i]? =
              s.scratch.scratch_buf[ctrl_off.toNat + i]? := fun i hi hne5 => by
            dsimp only [scr3, scr2, scr1]
            rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
              List.getElem?_set_ne (by omega)]
          have h5_set : scr3[ctrl_off.toNat + 5]?.getD 0#32 = q_len + 1#32 := by
            dsimp only [scr3]; rw [List.getElem?_set_self (by simp [scr2, scr1, hscrl0]; omega),
              Option.getD_some]
          have hlay3 : M6CtrlLayout c scr3 g_len ctrl_off.toNat occ_bkt bkt_off inq_off q_off
              ht_off ht_sz := by
            refine m6CtrlLayout_same_tail hlay_dup (hscrl3.trans hscrl0.symm) ?_ hsame_idx ?_
            · rw [h5_set, hql1]; omega
            · intro k hk; rw [h5_set, hql1] at hk
              have he4 := hsame_idx 4 (by decide) (by decide)
              rw [he4]
              have hq_idx_lt : q_off + (q_head.toNat + k) % occ_bkt < inq_off + b.toNat := by
                have := Nat.mod_lt (q_head.toNat + k) h_opos; omega
              dsimp only [scr3, scr2, scr1]
              rw [← hqh_n]
              rw [List.getElem?_set_ne (by omega)]
              by_cases hkt : (q_head.toNat + k) % occ_bkt = tail.toNat
              · rw [hkt, List.getElem?_set_self (by simp [hscrl0]; omega), Option.getD_some]
                exact hb_lt
              · have hk_ne : k ≠ q_len.toNat := fun he => hkt (by rw [he, htail_mod])
                rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega), hqh_n]
                exact h_qok k (by rw [← hql_n]; omega)
          clear hc
          have hinqb_idx :
              (BitVec.setWidth 64 s.scratch.scratch_buf[(ctrl_off + 2).toNat] +
                BitVec.setWidth 64
                  (v &&& s.scratch.scratch_buf[BitVec.toNat ctrl_off] - 1)).toNat =
                inq_off + b.toNat := hinqb_n
          m6_let; refine wp_store_sep (FullArenaTactics.c0_store_full_scratch_buf 1#32
            (by change (BitVec.setWidth 64 s.scratch.scratch_buf[(ctrl_off + 2).toNat] +
                    BitVec.setWidth 64
                      (v &&& s.scratch.scratch_buf[BitVec.toNat ctrl_off] - 1)).toNat <
                  s.scratch.scratch_buf.length
                rw [hinqb_idx]; omega) hm0) ?_
          intro m1 hm1
          have hqt_arr1 : (q_off + tail.toNat) < scr1.length := by simp [scr1, hscrl0]; omega
          have hco5_arr2 : (ctrl_off.toNat + 5) < scr2.length := by simp [scr2, scr1]; omega
          have hhm1 : (FullMem c { s with scratch := { s.scratch with scratch_buf := scr1 } } ⋆ R)
              m1 := by dsimp only [scr1]; rw [← hinqb_idx]; exact hm1
          have hqt_idx :
              (BitVec.setWidth 64 s.scratch.scratch_buf[(ctrl_off + 3).toNat] +
                BitVec.setWidth 64
                  (q_head + q_len &&& s.scratch.scratch_buf[BitVec.toNat ctrl_off] - 1)).toNat =
                q_off + tail.toNat := hqt_n
          m6_let; refine wp_store_sep (FullArenaTactics.c0_store_full_scratch_buf b
            (by change (BitVec.setWidth 64 s.scratch.scratch_buf[(ctrl_off + 3).toNat] +
                    BitVec.setWidth 64
                      (q_head + q_len &&& s.scratch.scratch_buf[BitVec.toNat ctrl_off] -
                        1)).toNat < scr1.length
                rw [hqt_idx]; exact hqt_arr1) hhm1) ?_
          intro m2 hm2
          have hhm2 : (FullMem c { s with scratch := { s.scratch with scratch_buf := scr2 } } ⋆ R)
              m2 := by dsimp only [scr2]; rw [← hqt_idx]; exact hm2
          have hco5_idx : (ctrl_off + 5).toNat = ctrl_off.toNat + 5 := hco5_n
          m6_let; refine wp_store_sep (FullArenaTactics.c0_store_full_scratch_buf (q_len + 1#32)
            (by rw [hco5_idx]; exact hco5_arr2) hhm2) ?_
          intro m3 hm3
          have hhm3 : (FullMem c { s with scratch := { s.scratch with scratch_buf := scr3 } } ⋆ R)
              m3 := by dsimp only [scr3]; rw [← hco5_idx]; exact hm3
          m6_steps
          refine hQ scr3 m3 hscrl3 (Or.inr ⟨occ_bkt, bkt_off, inq_off, q_off, hlay3⟩)
            (fun hcap => absurd hcap (by omega)) (fun o1 b1 i1 q1 hlay1 => ?_) hhm3
          obtain ⟨rfl, rfl, rfl, rfl, _, _⟩ := m6CtrlLayout_unique hlay_dup hlay1
          refine ⟨(hsame_idx 0 (by decide) (by decide)).trans
              (list_getElem?_eq_some_of_getD (by omega) h_occ),
            (hsame_idx 1 (by decide) (by decide)).trans
              (list_getElem?_eq_some_of_getD (by omega) h_bkt),
            (hsame_idx 2 (by decide) (by decide)).trans
              (list_getElem?_eq_some_of_getD (by omega) h_inq),
            (hsame_idx 3 (by decide) (by decide)).trans
              (list_getElem?_eq_some_of_getD (by omega) h_q),
            hsame_idx 4 (by decide) (by decide),
            (hsame_idx 6 (by decide) (by decide)).trans
              (list_getElem?_eq_some_of_getD (by omega) h_ht_o),
            (hsame_idx 7 (by decide) (by decide)).trans
              (list_getElem?_eq_some_of_getD (by omega) h_ht_s),
            fun idx hne5 hnq hni => ?_⟩
          dsimp only [scr3, scr2, scr1]
          have hne_q : q_off + tail.toNat ≠ idx := fun h => hnq (h ▸ ⟨by omega, by omega⟩)
          have hne_i : inq_off + b.toNat ≠ idx := fun h => hni (h ▸ ⟨by omega, by omega⟩)
          rw [List.getElem?_set_ne hne5.symm, List.getElem?_set_ne hne_q,
            List.getElem?_set_ne hne_i]
        · m6_steps
          refine hQ s.scratch.scratch_buf m0 hscrl0 (Or.inr ⟨occ_bkt, bkt_off, inq_off, q_off,
            hlay_dup⟩) (fun hcap => absurd hcap (by omega))
            (fun o1 b1 i1 q1 hl => ?_) hm0
          obtain ⟨rfl, rfl, rfl, rfl, _, _⟩ := m6CtrlLayout_unique hlay_dup hl
          exact m6CtrlLayout_frame_refl hscrl0 hl
      · m6_steps
        refine hQ s.scratch.scratch_buf m0 hscrl0 (Or.inr ⟨occ_bkt, bkt_off, inq_off, q_off,
          hlay_dup⟩) (fun hcap => absurd hcap (by omega))
          (fun o1 b1 i1 q1 hl => ?_) hm0
        obtain ⟨rfl, rfl, rfl, rfl, _, _⟩ := m6CtrlLayout_unique hlay_dup hl
        exact m6CtrlLayout_frame_refl hscrl0 hl

end MatchersAndQueue

/-! ## 3. Shared `EvalGate` State Invariants, Enqueue/Fold Framing & Fast Macros -/

section EvalGateSupport

@[expose] def M6EvalGateOk (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (fuel0 : BitVec 64) (ar0 : List (BitVec 32)) (alen0 cv0 g_len ht_off ht_sz
      ctrl_off : Nat) (scr0 scr_init : List (BitVec 32)) (st : FullState) : Prop :=
  FullDenseInvW c F0 F_cur st ∧
  st.core.cur_vars = cv0 ∧ st.core.fuel = fuel0 ∧
  st.core.arena = ar0 ∧ st.core.arena_len = alen0 ∧
  FullCongReprInv F_cur (2 * cv0) st.core.repr ∧
  M6CongHtInv F_cur cv0 scr0 st.scratch.scratch_buf g_len ht_off ht_sz ∧
  M6QueueCtx c st.scratch.scratch_buf g_len ctrl_off ht_off ht_sz ∧
  M6ScrFrame c g_len ctrl_off ht_off ht_sz scr_init st.scratch.scratch_buf

@[expose] def M6HashGateOk (F_cur : List (List Nat)) (cv0 : Nat) (lhs : BitVec 32)
    (tmps : List (BitVec 32)) (htag harity : BitVec 32) : Prop :=
  harity.toNat ≤ cv0 ∧
  (htag = 0#32 → 2 ≤ harity.toNat ∧ harity.toNat ≤ 31 ∧
    ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      evalLitVal α lhs.toNat =
        (List.range harity.toNat).all (fun k => evalLitVal α (tmps[k]?.getD 0#32).toNat)) ∧
  (htag = 1#32 → 2 ≤ harity.toNat ∧ harity.toNat ≤ 4 ∧
    (∀ k < harity.toNat, (tmps[k]?.getD 0#32).toNat < 2 * cv0) ∧
    XorListGateDef (cnfOfClauses F_cur) lhs.toNat
      ((tmps.take harity.toNat).map BitVec.toNat)) ∧
  (htag = 2#32 → harity = 3#32 ∧
    IteGateDef (cnfOfClauses F_cur) lhs.toNat
      (tmps[0]?.getD 0#32).toNat (tmps[1]?.getD 0#32).toNat (tmps[2]?.getD 0#32).toNat)

theorem m6EvalGateOk_of_fold {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)}
    {alen0 cv0 g_len ht_off ht_sz ctrl_off : Nat} {scr0 scr_init : List (BitVec 32)}
    {st s' : FullState}
    (hok : M6EvalGateOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz ctrl_off
      scr0 scr_init st)
    (hl' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hmk' : FullLitMarksClear c s') (hnd' : FullArenaVarsNodup s')
    (hext' : FullExtScratchOk c s') (hcl' : s'.core.cur_level = 0)
    (hdm' : s'.core.dense_mode ≠ 0#64) (hcv' : s'.core.cur_vars = st.core.cur_vars)
    (hfl' : s'.core.fuel = st.core.fuel) (har' : s'.core.arena = st.core.arena)
    (hal' : s'.core.arena_len = st.core.arena_len)
    (hscr' : s'.scratch.scratch_buf = st.scratch.scratch_buf)
    (hrepr' : FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr) :
    M6EvalGateOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz ctrl_off
      scr0 scr_init s' :=
  ⟨⟨hl', hw', hmk', hnd', hext', hcl', hdm'⟩, hcv'.trans hok.2.1, hfl'.trans hok.2.2.1,
   har'.trans hok.2.2.2.1, hal'.trans hok.2.2.2.2.1,
   by rw [hcv'.trans hok.2.1] at hrepr'; exact hrepr',
   by rw [hscr']; exact hok.2.2.2.2.2.2.1,
   by rw [hscr']; exact hok.2.2.2.2.2.2.2.1,
   by unfold M6ScrFrame; rw [hscr']; exact hok.2.2.2.2.2.2.2.2⟩

theorem m6EvalGateOk_wsState {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)}
    {alen0 cv0 g_len ht_off ht_sz ctrl_off : Nat} {scr0 scr_init : List (BitVec 32)}
    {st : FullState}
    (hok : M6EvalGateOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz ctrl_off
      scr0 scr_init st)
    {repr' tmp' : List (BitVec 32)}
    (hrl' : repr'.length = 2 * c.max_vars) (htl' : tmp'.length = c.max_vars)
    (hrepr' : FullCongReprInv F_cur (2 * cv0) repr') :
    M6EvalGateOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz ctrl_off
      scr0 scr_init (wsState st repr' tmp') :=
  ⟨⟨⟨{ hok.1.1.core_ok with repr_len := hrl', tmp_len_arr := htl' }, hok.1.1.scratch_ok⟩,
    fullWitnessInv_with_tmp (fullWitnessInv_with_repr hok.1.2.1 repr') tmp',
    hok.1.2.2.1, hok.1.2.2.2.1, hok.1.2.2.2.2.1, hok.1.2.2.2.2.2.1, hok.1.2.2.2.2.2.2⟩,
   hok.2.1, hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2.1, hrepr', hok.2.2.2.2.2.2.1,
   hok.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2⟩

theorem m6EvalGateOk_with_repr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)}
    {alen0 cv0 g_len ht_off ht_sz ctrl_off : Nat} {scr0 scr_init : List (BitVec 32)}
    {st : FullState}
    (hok : M6EvalGateOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz ctrl_off
      scr0 scr_init st)
    {repr' : List (BitVec 32)} (hrl' : repr'.length = 2 * c.max_vars)
    (hrepr' : FullCongReprInv F_cur (2 * cv0) repr') :
    M6EvalGateOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz ctrl_off
      scr0 scr_init { st with core := { st.core with repr := repr' } } :=
  ⟨⟨⟨{ hok.1.1.core_ok with repr_len := hrl' }, hok.1.1.scratch_ok⟩,
    fullWitnessInv_with_repr hok.1.2.1 repr', hok.1.2.2.1, hok.1.2.2.2.1,
    hok.1.2.2.2.2.1, hok.1.2.2.2.2.2.1, hok.1.2.2.2.2.2.2⟩,
   hok.2.1, hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2.1, hrepr', hok.2.2.2.2.2.2.1,
   hok.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2⟩

theorem m6EvalGateOk_with_repr_mclr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)}
    {alen0 cv0 g_len ht_off ht_sz ctrl_off : Nat} {scr0 scr_init : List (BitVec 32)}
    {st : FullState}
    (hok : M6EvalGateOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz ctrl_off
      scr0 scr_init st)
    {repr' mclr' : List (BitVec 32)} (hrl' : repr'.length = 2 * c.max_vars)
    (hml' : mclr'.length = c.max_vars)
    (hrepr' : FullCongReprInv F_cur (2 * cv0) repr') :
    M6EvalGateOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz ctrl_off
      scr0 scr_init { st with core := { st.core with repr := repr', min_clr := mclr' } } :=
  ⟨⟨⟨{ hok.1.1.core_ok with repr_len := hrl', min_clr_len_arr := hml' }, hok.1.1.scratch_ok⟩,
    fullWitnessInv_with_min_clr (fullWitnessInv_with_repr hok.1.2.1 repr') mclr',
    hok.1.2.2.1, hok.1.2.2.2.1, hok.1.2.2.2.2.1, hok.1.2.2.2.2.2.1, hok.1.2.2.2.2.2.2⟩,
   hok.2.1, hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2.1, hrepr', hok.2.2.2.2.2.2.1,
   hok.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2⟩

theorem m6EvalGateOk_enq {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)}
    {alen0 cv0 g_len ht_off ht_sz ctrl_off : Nat} {scr0 scr_init scr' : List (BitVec 32)}
    {st : FullState}
    (hok : M6EvalGateOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz ctrl_off
      scr0 scr_init st)
    (hq_init : M6QueueCtx c scr_init g_len ctrl_off ht_off ht_sz)
    (hscrl' : scr'.length = c.scratch_cap)
    (hq' : M6QueueCtx c scr' g_len ctrl_off ht_off ht_sz)
    (hcap_eq : ctrl_off = c.scratch_cap → scr' = st.scratch.scratch_buf)
    (hlay' : ∀ occ_bkt bkt_off inq_off q_off,
      M6CtrlLayout c st.scratch.scratch_buf g_len ctrl_off occ_bkt bkt_off inq_off
        q_off ht_off ht_sz →
      scr'[ctrl_off]? = some (BitVec.ofNat 32 occ_bkt) ∧
      scr'[ctrl_off + 1]? = some (BitVec.ofNat 32 bkt_off) ∧
      scr'[ctrl_off + 2]? = some (BitVec.ofNat 32 inq_off) ∧
      scr'[ctrl_off + 3]? = some (BitVec.ofNat 32 q_off) ∧
      scr'[ctrl_off + 4]? = st.scratch.scratch_buf[ctrl_off + 4]? ∧
      scr'[ctrl_off + 6]? = some (BitVec.ofNat 32 ht_off) ∧
      scr'[ctrl_off + 7]? = some (BitVec.ofNat 32 ht_sz) ∧
      (∀ idx, idx ≠ ctrl_off + 5 →
        ¬ (q_off ≤ idx ∧ idx < q_off + occ_bkt) →
        ¬ (inq_off ≤ idx ∧ idx < inq_off + occ_bkt) →
        scr'[idx]? = st.scratch.scratch_buf[idx]?)) :
    M6EvalGateOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz ctrl_off
      scr0 scr_init { st with scratch := { st.scratch with scratch_buf := scr' } } := by
  have hdw := m6DenseInvW_with_scr hok.1 hscrl'
  refine ⟨hdw, hok.2.1, hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2.1, hok.2.2.2.2.2.1,
    m6CongHtInv_enq hok.2.2.2.2.2.2.1 hok.2.2.2.2.2.2.2.1 hcap_eq hlay',
    hq', m6ScrFrame_enq hq_init hok.2.2.2.2.2.2.2.2 hok.2.2.2.2.2.2.2.1 hscrl' hcap_eq hlay'⟩

theorem ev_ht_insert_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)}
    {alen0 cv0 : Nat} {g_len ht_off ht_sz ctrl_off g : BitVec 64}
    {scr0 scr_init : List (BitVec 32)} {stp : FullState} {slot : BitVec 64}
    (hok : M6EvalGateOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat ht_off.toNat ht_sz.toNat
      ctrl_off.toNat scr0 scr_init stp)
    (hg_lt : g.toNat < g_len.toNat) (hg_le_ht : g_len.toNat ≤ ht_off.toNat)
    (hht_le : ht_off.toNat + ht_sz.toNat ≤ c.scratch_cap)
    (hslot_lt : slot.toNat < ht_sz.toNat)
    (hgat : M6GateAt F_cur cv0 scr0 g_len.toNat g.toNat) :
    let scr_ins := stp.scratch.scratch_buf.set (ht_off.toNat + slot.toNat) (g.setWidth 32)
    let stp' : FullState :=
      { stp with scratch := { stp.scratch with
        scratch_buf := scr_ins, res_sz := stp.scratch.res_sz + 1#64 } }
    M6EvalGateOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat ht_off.toNat ht_sz.toNat
      ctrl_off.toNat scr0 scr_init stp' := by
  intro scr_ins stp'
  have hscrl_p := hok.1.1.scratch_ok.scratch_buf_len
  have hlen_p' : stp'.LengthsOk c :=
    ⟨hok.1.1.core_ok,
     { hok.1.1.scratch_ok with scratch_buf_len := by rw [List.length_set]; exact hscrl_p }⟩
  have hdw' : FullDenseInvW c F0 F_cur stp' :=
    ⟨hlen_p', hok.1.2.1, hok.1.2.2.1, hok.1.2.2.2.1,
     fullExtScratchOk_of_eq hok.1.2.2.2.2.1 rfl rfl rfl rfl,
     hok.1.2.2.2.2.2.1, hok.1.2.2.2.2.2.2⟩
  have hg_tr : (g.setWidth 32).toNat = g.toNat := by
    have hsc := c.hscr; unfold dimacsBound at hsc
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  have hht_p' : M6CongHtInv F_cur cv0 scr0 scr_ins g_len.toNat ht_off.toNat ht_sz.toNat :=
    fun k' hk' => by
      by_cases hks : k' = slot.toNat
      · subst hks; right; rw [List.getElem?_set_self (by omega), Option.getD_some, hg_tr]
        exact hgat
      · rw [List.getElem?_set_ne (by omega)]; exact hok.2.2.2.2.2.2.1 k' hk'
  exact ⟨hdw', hok.2.1, hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2.1, hok.2.2.2.2.2.1, hht_p',
    m6QueueCtx_set_ht hok.2.2.2.2.2.2.2.1 hslot_lt _,
    m6ScrFrame_ht_set hok.2.2.2.2.2.2.2.2 slot.toNat _⟩

theorem ev_ret2_q {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)}
    {alen0 cv0 g_len ht_off ht_sz ctrl_off : Nat}
    {scr0 scr_init : List (BitVec 32)} {su s0 : FullState} {R : Mem 64 → Prop} {mu : Mem 64}
    {Q : Post [i64]}
    (hQ : ∀ (r : BitVec 64) s' m',
      FullDenseInvW c F0 F_cur s' →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.fuel = s0.core.fuel →
      s'.core.arena = s0.core.arena → s'.core.arena_len = s0.core.arena_len →
      FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
      (∀ idx < g_len, s'.scratch.scratch_buf[idx]? = scr0[idx]?) →
      M6CongHtInv F_cur s'.core.cur_vars scr0 s'.scratch.scratch_buf g_len ht_off ht_sz →
      M6QueueCtx c s'.scratch.scratch_buf g_len ctrl_off ht_off ht_sz →
      ((r &&& 2#64) = 0#64 →
        (∀ idx < c.scratch_cap, idx < ht_off →
          (ctrl_off = c.scratch_cap →
            s'.scratch.scratch_buf[idx]? = s0.scratch.scratch_buf[idx]?) ∧
          (∀ occ_bkt bkt_off inq_off q_off,
            M6CtrlLayout c s0.scratch.scratch_buf g_len ctrl_off occ_bkt bkt_off inq_off
              q_off ht_off ht_sz →
            idx ≠ ctrl_off + 5 →
            ¬ (q_off ≤ idx ∧ idx < q_off + occ_bkt) →
            ¬ (inq_off ≤ idx ∧ idx < inq_off + occ_bkt) →
            s'.scratch.scratch_buf[idx]? = s0.scratch.scratch_buf[idx]?))) →
      ((r &&& 2#64) ≠ 0#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hcv0 : cv0 = s0.core.cur_vars) (hf0 : fuel0 = s0.core.fuel)
    (ha0 : ar0 = s0.core.arena) (hal0 : alen0 = s0.core.arena_len)
    (_hs0 : scr_init = s0.scratch.scratch_buf)
    (hle : g_len ≤ ht_off) (hht : ht_off + ht_sz ≤ c.scratch_cap)
    (hpref0 : ∀ idx < g_len, scr_init[idx]? = scr0[idx]?)
    (hq0 : M6QueueCtx c scr_init g_len ctrl_off ht_off ht_sz)
    (hoku : M6EvalGateOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz ctrl_off
      scr0 scr_init su)
    (huns : F0.Unsat) (hmu : (FullMem c su ⋆ R) mu) :
    Q (2#64, ()) mu :=
  hQ 2#64 su mu hoku.1 (hoku.2.1.trans hcv0) (hoku.2.2.1.trans hf0)
    (hoku.2.2.2.1.trans ha0) (hoku.2.2.2.2.1.trans hal0)
    (by rw [hoku.2.1]; exact hoku.2.2.2.2.2.1)
    (m6ScrFrame_pref hle hht hpref0 hq0 hoku.2.2.2.2.2.2.2.2)
    (by rw [hoku.2.1]; exact hoku.2.2.2.2.2.2.1)
    hoku.2.2.2.2.2.2.2.1
    (fun h => absurd h (by decide)) (fun _ => huns) hmu

theorem ev_exit_q {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)}
    {alen0 cv0 g_len ht_off ht_sz ctrl_off : Nat}
    {scr0 scr_init : List (BitVec 32)} {su s0 : FullState} {R : Mem 64 → Prop} {mu : Mem 64}
    {Q : Post [i64]}
    (hQ : ∀ (r : BitVec 64) s' m',
      FullDenseInvW c F0 F_cur s' →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.fuel = s0.core.fuel →
      s'.core.arena = s0.core.arena → s'.core.arena_len = s0.core.arena_len →
      FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
      (∀ idx < g_len, s'.scratch.scratch_buf[idx]? = scr0[idx]?) →
      M6CongHtInv F_cur s'.core.cur_vars scr0 s'.scratch.scratch_buf g_len ht_off ht_sz →
      M6QueueCtx c s'.scratch.scratch_buf g_len ctrl_off ht_off ht_sz →
      ((r &&& 2#64) = 0#64 →
        (∀ idx < c.scratch_cap, idx < ht_off →
          (ctrl_off = c.scratch_cap →
            s'.scratch.scratch_buf[idx]? = s0.scratch.scratch_buf[idx]?) ∧
          (∀ occ_bkt bkt_off inq_off q_off,
            M6CtrlLayout c s0.scratch.scratch_buf g_len ctrl_off occ_bkt bkt_off inq_off
              q_off ht_off ht_sz →
            idx ≠ ctrl_off + 5 →
            ¬ (q_off ≤ idx ∧ idx < q_off + occ_bkt) →
            ¬ (inq_off ≤ idx ∧ idx < inq_off + occ_bkt) →
            s'.scratch.scratch_buf[idx]? = s0.scratch.scratch_buf[idx]?))) →
      ((r &&& 2#64) ≠ 0#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hcv0 : cv0 = s0.core.cur_vars) (hf0 : fuel0 = s0.core.fuel)
    (ha0 : ar0 = s0.core.arena) (hal0 : alen0 = s0.core.arena_len)
    (hs0 : scr_init = s0.scratch.scratch_buf)
    (hle : g_len ≤ ht_off) (hht : ht_off + ht_sz ≤ c.scratch_cap)
    (hpref0 : ∀ idx < g_len, scr_init[idx]? = scr0[idx]?)
    (hq0 : M6QueueCtx c scr_init g_len ctrl_off ht_off ht_sz)
    (hoku : M6EvalGateOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz ctrl_off
      scr0 scr_init su)
    (hmu : (FullMem c su ⋆ R) mu) (ch keep : Bool) :
    let rv : BitVec 64 := (if ch then 1#64 else 0#64) ||| (if keep then 4#64 else 0#64)
    Q (rv, ()) mu := by
  intro rv
  have hand0 : (rv &&& 2#64) = 0#64 := by
    dsimp only [rv]; cases ch <;> cases keep <;> decide
  refine hQ rv su mu hoku.1 (hoku.2.1.trans hcv0) (hoku.2.2.1.trans hf0)
    (hoku.2.2.2.1.trans ha0) (hoku.2.2.2.2.1.trans hal0)
    (by rw [hoku.2.1]; exact hoku.2.2.2.2.2.1)
    (m6ScrFrame_pref hle hht hpref0 hq0 hoku.2.2.2.2.2.2.2.2)
    (by rw [hoku.2.1]; exact hoku.2.2.2.2.2.2.1)
    hoku.2.2.2.2.2.2.2.1
    (fun _ idx h1 h2 => hs0 ▸ hoku.2.2.2.2.2.2.2.2.2 idx h1 h2)
    (fun h => absurd hand0 h) hmu

theorem ev_unit_call {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)}
    {alen0 cv0 g_len ht_off ht_sz ctrl_off : Nat} {scr0 scr_init : List (BitVec 32)}
    {st : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} {lit next_ep : BitVec 32}
    (hok : M6EvalGateOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz ctrl_off
      scr0 scr_init st)
    (hl : lit.toNat < 2 * cv0) (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]))
    (hm : (FullMem c st ⋆ R) m)
    (k : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      M6EvalGateOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz ctrl_off
        scr0 scr_init s' →
      s'.core.tmp = st.core.tmp → (r = 2#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    m3CongUnitFoldSpec (c.hdr, lit, next_ep, ()) m Q X :=
  ⟨c, F0, F_cur, st, R, rfl, hok.1.1, hok.1.2.1, hok.1.2.2.1, hok.1.2.2.2.1,
   hok.1.2.2.2.2.1, hok.1.2.2.2.2.2.1, hok.1.2.2.2.2.2.2,
   hok.2.1 ▸ hok.2.2.2.2.2.1, hok.2.1 ▸ hl, hent, hm,
   fun r s' m' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 htmp h12 h13 _ h2u hm' =>
     k r s' m' (m6EvalGateOk_of_fold hok h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13)
       htmp (fun h => (h2u h).2) hm'⟩

theorem ev_unit_xor1 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)}
    {alen0 cv0 g_len ht_off ht_sz ctrl_off : Nat} {scr0 scr_init : List (BitVec 32)}
    {st : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} {lit next_ep : BitVec 32}
    (hok : M6EvalGateOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz ctrl_off
      scr0 scr_init st)
    (hl : lit.toNat < 2 * cv0)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg lit.toNat]))
    (hm : (FullMem c st ⋆ R) m)
    (k : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      M6EvalGateOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz ctrl_off
        scr0 scr_init s' →
      s'.core.tmp = st.core.tmp → (r = 2#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    m3CongUnitFoldSpec (c.hdr, lit ^^^ 1#32, next_ep, ()) m Q X :=
  ev_unit_call hok (by rw [bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even hl)
    (by rw [bv32_xor1_eq_litNeg]; exact hent) hm k

theorem ev_equiv_call {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)}
    {alen0 cv0 g_len ht_off ht_sz ctrl_off : Nat} {scr0 scr_init : List (BitVec 32)}
    {st : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} {a b next_ep : BitVec 32}
    (hok : M6EvalGateOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz ctrl_off
      scr0 scr_init st)
    (ha : a.toNat < 2 * cv0) (hb : b.toNat < 2 * cv0)
    (heqv : LitEquiv (cnfOfClauses F_cur) a.toNat b.toNat) (hm : (FullMem c st ⋆ R) m)
    (k : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      M6EvalGateOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz ctrl_off
        scr0 scr_init s' →
      s'.core.tmp = st.core.tmp → (r = 2#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    m3CongEquivFoldSpec (c.hdr, a, b, next_ep, ()) m Q X :=
  ⟨c, F0, F_cur, st, R, rfl, hok.1.1, hok.1.2.1, hok.1.2.2.1, hok.1.2.2.2.1,
   hok.1.2.2.2.2.1, hok.1.2.2.2.2.2.1, hok.1.2.2.2.2.2.2,
   hok.2.1 ▸ hok.2.2.2.2.2.1, hok.2.1 ▸ ha, hok.2.1 ▸ hb, heqv, hm,
   fun r s' m' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 htmp h12 h13 _ h2u hm' =>
     k r s' m' (m6EvalGateOk_of_fold hok h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13)
       htmp h2u hm'⟩

theorem ev_enq_call {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)}
    {alen0 cv0 g_len ht_off ht_sz ctrl_off : Nat} {scr0 scr_init : List (BitVec 32)}
    {st : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post []} {X : XPost} {v : BitVec 32}
    (hok : M6EvalGateOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz ctrl_off
      scr0 scr_init st)
    (hq_init : M6QueueCtx c scr_init g_len ctrl_off ht_off ht_sz)
    (hm : (FullMem c st ⋆ R) m)
    (k : ∀ s' m',
      M6EvalGateOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz ctrl_off
        scr0 scr_init s' →
      s'.core.tmp = st.core.tmp → (FullMem c s' ⋆ R) m' → Q () m') :
    m6CongEnqVarSpec (c.hdr, BitVec.ofNat 64 ctrl_off, v, ()) m Q X := by
  have hsc := c.hscr; unfold dimacsBound at hsc
  have hco_n : (BitVec.ofNat 64 ctrl_off).toNat = ctrl_off := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      rcases hq_init with rfl | ⟨_, _, _, _, hlay⟩
      · omega
      · have := hlay.1; omega)]
  refine ⟨c, st, g_len, ht_off, ht_sz, R, rfl, hok.1.1, by rw [hco_n]; exact hok.2.2.2.2.2.2.2.1,
    hm, fun scr' m' hscrl' hq' hcap_eq hlay' hm' => ?_⟩
  rw [hco_n] at hq' hcap_eq hlay'
  exact k { st with scratch := { st.scratch with scratch_buf := scr' } } m'
    (m6EvalGateOk_enq hok hq_init hscrl' hq' hcap_eq hlay') rfl hm'

end EvalGateSupport

end LeanQbe.T.Examples.Kissat.FullM6CongSubst
