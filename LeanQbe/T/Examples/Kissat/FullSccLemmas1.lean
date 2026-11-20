module

public import LeanQbe.T.Examples.Kissat.FullArena
public import LeanQbe.T.Examples.Kissat.FullInv2
public import LeanQbe.T.Examples.Kissat.Full3
public import LeanQbe.T.Logic.C0Agrees
public import LeanQbe.T.Logic.C0Step
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Tarjan SCC — Part 1 (`Stage 4`)

Defines:
1. Canonical shared Stage-4 invariants and local `Spec` contracts (`FullSccSpecs`) for
   `full_tarjan_pop_scc` and `full_tarjan_scc` (`Full3.lean` #24–25, with `fullTarjanSccSpec`
   definitionally identical to `FullSpec3.fullTarjanSccSpec`).
2. Strictly scoped tactic & index-0 memory shortcuts (`FullSccTactics`).
3. Pure BIG implication-graph (`BinReach` / `LitEquiv`) and `WatchSliceOk` binary-scan lemmas.
4. `full_tarjan_pop_scc_wp` (`Full3.lean` #24).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Canonical Stage-4 Invariants & Local `Spec` Contracts (`FullSccSpecs`) -/

namespace FullSccSpecs

def FullMrkZero (c : FullCfg) (s : FullState) : Prop :=
  ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8
def FullLitMarksClear (c : FullCfg) (s : FullState) : Prop :=
  FullMrkZero c s ∧ (∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8)
def FullArenaVarsNodup (s : FullState) : Prop :=
  ∀ r ∈ fullArenaClauseRefs s, fullArenaClauseGarb s r = false →
    ((fullArenaClauseLits s r).map (· / 2)).Nodup
def FullLastLearnedWf (s : FullState) : Prop :=
  ∀ i < 8,
    let cr := s.scratch.last_learned[i]?.getD 0xFFFFFFFF#32
    cr = 0xFFFFFFFF#32 ∨ cr.toNat ∈ fullArenaClauseRefs s
def FullExtScratchOk (c : FullCfg) (s : FullState) : Prop :=
  FullLastLearnedWf s ∧ s.scratch.extend_len ≤ c.extend_cap
def FullSparseInv (c : FullCfg) (F0 : CNF Nat) (s : FullState) : Prop :=
  FullCoreInv c F0 s ∧ FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧
  FullExtScratchOk c s ∧ s.core.dense_mode = 0#64
def FullSparseInvW (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) : Prop :=
  s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullLitMarksClear c s ∧
  FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.dense_mode = 0#64
def FullReprEquiv (F_cur : List (List Nat)) (s : FullState) : Prop :=
  ∀ l < 2 * s.core.cur_vars,
    let r := (s.core.repr[l]?.getD 0#32).toNat
    r < 2 * s.core.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l, r ^^^ 1]) ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [l ^^^ 1, r])
def PartialReprInv (F_cur : List (List Nat)) (k : FullCoreState) : Prop :=
  ∀ l < 2 * k.cur_vars, let rv := k.repr[l]?.getD 0xFFFFFFFF#32
    rv ≠ 0xFFFFFFFF#32 → rv.toNat < 2 * k.cur_vars ∧ LitEquiv (cnfOfClauses F_cur) l rv.toNat
def UnitsSoundInv (F_cur : List (List Nat)) (s : FullState) (n : Nat) : Prop :=
  ∀ i < n, let u := (s.scratch.shrink_stk[i]?.getD 0#32).toNat
    u < 2 * s.core.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [u])

/-! ### Owned function specifications (`Full3.lean` #24–25) -/

def popSccMask (s : FullState) : FullState :=
  { s with
    core := { s.core with repr := [], tmp_cnt := 0, inconsistent := 0#64 }
    scratch := { s.scratch with tarjan_reach := [], shrink_stk := [], res_sz := 0#64 } }

def fullTarjanPopSccSpec : Spec [i64, i32, i32, i32] [.bool] :=
  fun (h, root_lit, lit, mark_root, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (k0 : Nat) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ s.core.inconsistent = 0#64 ∧
      root_lit.toNat < 2 * s.core.cur_vars ∧ lit.toNat < 2 * s.core.cur_vars ∧
      s.core.tmp_cnt ≤ 2 * s.core.cur_vars ∧ s.scratch.res_sz.toNat ≤ c.max_vars ∧
      k0 < s.core.tmp_cnt ∧ s.scratch.work_stk1[k0]?.getD 0#32 = lit ∧
      (∀ j, k0 < j → j < s.core.tmp_cnt → s.scratch.work_stk1[j]?.getD 0#32 ≠ lit) ∧
      (∀ j < s.core.tmp_cnt, (s.scratch.work_stk1[j]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
      (∀ j, k0 ≤ j → j < s.core.tmp_cnt →
        LitEquiv (cnfOfClauses F_cur) (s.scratch.work_stk1[j]?.getD 0#32).toNat lit.toNat) ∧
      PartialReprInv F_cur s.core ∧ UnitsSoundInv F_cur s s.scratch.res_sz.toNat ∧
      (mark_root ≠ 0xFFFFFFFF#32 →
        (∀ j, k0 ≤ j → j < s.core.tmp_cnt →
          BinReach (cnfOfClauses F_cur) root_lit.toNat (s.scratch.work_stk1[j]?.getD 0#32).toNat) ∧
        (∀ l < 2 * s.core.cur_vars,
          mark_root.toNat ≤ (s.scratch.tarjan_mark[l]?.getD 0#32).toNat →
          BinReach (cnfOfClauses F_cur) root_lit.toNat l)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (failed' : Bool) (s' : FullState) m',
        AgreesExcept popSccMask s s' → s'.core.tmp_cnt = k0 →
        s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → s'.scratch.res_sz.toNat ≤ c.max_vars →
        PartialReprInv F_cur s'.core → UnitsSoundInv F_cur s' s'.scratch.res_sz.toNat →
        (s'.core.inconsistent = 0#64 ∨ s'.core.inconsistent = 1#64) →
        (s'.core.inconsistent ≠ 0#64 → (cnfOfClauses F_cur).Unsat) →
        (s'.core.inconsistent = 0#64 →
          (∀ j, k0 ≤ j → j < s.core.tmp_cnt →
            let x := (s.scratch.work_stk1[j]?.getD 0#32).toNat
            s'.core.repr[x]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 ∧
            s'.scratch.tarjan_reach[x]?.getD 0#32 = 0xFFFFFFFF#32) ∧
          (∀ l < 2 * s.core.cur_vars,
            (∀ j, k0 ≤ j → j < s.core.tmp_cnt → (s.scratch.work_stk1[j]?.getD 0#32).toNat ≠ l) →
            s'.core.repr[l]? = s.core.repr[l]? ∧
            s'.scratch.tarjan_reach[l]? = s.scratch.tarjan_reach[l]?)) →
        (FullMem c s' ⋆ R) m' → Q (failed', ()) m'

def fullTarjanSccSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ s.core.cur_level = 0 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r repr' tc' inc' tmk' trc' ws1' ws2' wsort' sstk' rsz' m',
      let s' : FullState :=
        { s with
          core := { s.core with repr := repr', tmp_cnt := tc', inconsistent := inc' }
          scratch := { s.scratch with tarjan_mark := tmk', tarjan_reach := trc',
                                      work_stk1 := ws1', work_stk2 := ws2', wsort := wsort',
                                      shrink_stk := sstk', res_sz := rsz' } }
      FullSparseInvW c F0 F_cur s' → r.toNat ≤ c.max_vars →
      (∀ k < r.toNat,
        (sstk'[k]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause [(sstk'[k]?.getD 0#32).toNat])) →
      (inc' = 0#64 → FullReprEquiv F_cur s') →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

end FullSccSpecs

open FullSccSpecs
/-! ## 2. Strictly Scoped Tactic & Index-0 Memory Helpers (`FullSccTactics`) -/
namespace FullSccTactics
open FullArenaTactics
open scoped FullArenaTactics
@[scoped c0_load] theorem load_full_work_stk1_0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.scratch.work_stk1.length)
    (hm : (FullMem c s ⋆ R) m) : loadVal m i32 c.pWorkStk1 = some s.scratch.work_stk1[0] := by
  simpa using load_full_work_stk1 (i := 0) hi hm
@[scoped c0_store] theorem store_full_work_stk1_0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.work_stk1.length)
    (hm : (FullMem c s ⋆ R) m) : storeOk m i32 c.pWorkStk1 ∧ (FullMem c { s with scratch :=
      { s.scratch with work_stk1 := s.scratch.work_stk1.set 0 v } } ⋆ R)
      (storeMem m i32 c.pWorkStk1 v) := by simpa using store_full_work_stk1 (i := 0) v hi hm
@[scoped c0_load] theorem load_full_work_stk2_0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.scratch.work_stk2.length)
    (hm : (FullMem c s ⋆ R) m) : loadVal m i32 c.pWorkStk2 = some s.scratch.work_stk2[0] := by
  simpa using load_full_work_stk2 (i := 0) hi hm
@[scoped c0_store] theorem store_full_work_stk2_0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.work_stk2.length)
    (hm : (FullMem c s ⋆ R) m) : storeOk m i32 c.pWorkStk2 ∧ (FullMem c { s with scratch :=
      { s.scratch with work_stk2 := s.scratch.work_stk2.set 0 v } } ⋆ R)
      (storeMem m i32 c.pWorkStk2 v) := by simpa using store_full_work_stk2 (i := 0) v hi hm
@[scoped c0_store] theorem store_full_wsort_0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.wsort.length)
    (hm : (FullMem c s ⋆ R) m) : storeOk m i32 c.pWsort ∧ (FullMem c { s with scratch :=
      { s.scratch with wsort := s.scratch.wsort.set 0 v } } ⋆ R)
      (storeMem m i32 c.pWsort v) := by simpa using store_full_wsort (i := 0) v hi hm

theorem strip_le_32_64 {P : Prop} (h : P) : 32 ≤ 64 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_32 {P : Prop} (h : P) : 8 ≤ 32 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_64 {P : Prop} (h : P) : 8 ≤ 64 ∧ P := ⟨by decide, h⟩

@[scoped bv_c0] theorem bv64_sext1 : BitVec.signExtend 64 (1 : BitVec 32) = 1#64 := rfl
@[scoped bv_c0] theorem bv64_shl_1bv (x : BitVec 64) :
    (x <<< (1#64 : BitVec 64)).toNat = (2 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]
@[scoped bv_c0] theorem bv64_ushr1_nat (x : BitVec 64) :
    (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
@[scoped bv_c0] theorem bv32_ushr1_nat (x : BitVec 32) :
    (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
@[scoped bv_c0] theorem bv64_ushr_1bv (x : BitVec 64) :
    (x >>> (1#64 : BitVec 64)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
@[scoped bv_c0] theorem bv32_ushr_1bv (x : BitVec 32) :
    (x >>> (1#32 : BitVec 32)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem wp_let_head {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {op : Op Val ts} {k : Tup Val ts → Expr Val Cont rs} {v : Tup Val ts}
    (he : ∀ post : Tup Val ts → Prop, post v → op.code.wp (vals op.args) post)
    (hk : wp Γ Q X (k v) m) : wp Γ Q X (.let_ op k) m := he _ hk
theorem wp_bget_here {Γ : Env} {rs ts : List Ty} {sig : List (List Ty)} {Q : Post rs} {X : XPost}
    {m : Mem 64} {b : Tup Val ts → Expr Val Cont rs} {bs : Blocks Val Cont rs sig}
    {xs : Tup Val ts} (h : wp Γ Q X (b xs) m) :
    wp Γ Q X (Blocks.get (Blocks.cons b bs) .here xs) m := h
theorem wp_jump_head {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {J : Cont ts} {args : Tup (Arg Val) ts} {v : Tup Val ts}
    (hv : vals args = v) (h : J v m) : wp Γ Q X (.jump J args) m := by rw [wp, hv]; exact h
theorem wp_ret_head {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {args : Tup (Arg Val) rs} {v : Tup Val rs}
    (hv : vals args = v) (h : Q v m) : wp Γ Q X (.ret args) m := by rw [wp, hv]; exact h
theorem wp_call_head {Γ : Env} {rs as bs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {f : Sym} {args : Tup (Arg Val) as} {k : Tup Val bs → Expr Val Cont rs} {v : Tup Val as}
    (hv : vals args = v) (h : Γ f as bs v m (fun r m' => wp Γ Q X (k r) m') X) :
    wp Γ Q X (.call f args k) m := by
  rw [wp, hv]; exact ⟨_, _, h, fun _ _ p => p, fun _ _ _ _ e => e⟩
theorem wp_jnz_head {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : Arg Val .bool} {e₁ e₂ : Expr Val Cont rs} {m : Mem 64} {b : Bool} (hb : c.val = b)
    (h₁ : b = true → wp Γ Q X e₁ m) (h₂ : b = false → wp Γ Q X e₂ m) :
    wp Γ Q X (.jnz c e₁ e₂) m := ⟨fun h => h₁ (hb ▸ h), fun h => h₂ (hb ▸ h)⟩

scoped macro "scc_strip" : tactic =>
  `(tactic| first | apply strip_le_32_64 | apply strip_le_8_32 | apply strip_le_8_64)
scoped macro "scc_unmdata" : tactic =>
  `(tactic| first | change LeanQbe.T.Func.wp _ _ _ _ _ _ | change LeanQbe.T.wp _ _ _ _ _ | skip)
scoped macro "scc_call" h:term : tactic =>
  `(tactic| refine wp_call_head (by simp only [LeanQbe.T.vals, LeanQbe.T.Arg.val,
      LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm, Prod.fst, Prod.snd]; rfl) ($h _ _ _ _ ?_))

section HeadStep
open Lean Meta Elab Tactic

private meta def isJoinLam (e : Lean.Expr) : Bool :=
  match e with | .lam _ _ b _ => !b.hasLooseBVars | _ => false

private meta def clearOldMem (m0 : Lean.Expr) : TacticM Unit := withMainContext do
  let .fvar mId := m0 | return
  for d in (← getLCtx).decls.toArray.reverse do
    let some d := d | continue
    let t ← instantiateMVars d.type
    if t.isAppOf ``Std.ExtHashMap.sep && t.appArg! == m0 then
      try liftMetaTactic1 fun g => some <$> g.clear d.fvarId catch _ => pure ()
  try liftMetaTactic1 fun g => some <$> g.clear mId catch _ => pure ()

private meta def findJoinFVar (J : FVarId) : TacticM (Option Lean.Expr) := withMainContext do
  for d in (← getLCtx).decls.toArray.reverse do
    let some d := d | continue
    let ok ← forallTelescopeReducing d.type fun xs concl => do
      if xs.size < 1 then return false
      return concl.getAppFn.isFVarOf J && (← inferType xs[xs.size - 1]!).isAppOf ``LeanQbe.T.wp
    if ok then return some d.toExpr
  return none

/-- Head-only C0 step (never runs `simp` over continuations; avoids deep recursion on ASTs). -/
meta def sccStepOnce (unrollJoin : Bool) : TacticM Bool := withMainContext do
  let g ← getMainGoal; let ty := (← instantiateMVars (← g.getType)).consumeMData.headBeta
  if ty.isAppOf ``LeanQbe.T.Func.wp && ty.getAppNumArgs ≥ 4 then
    let some c := (ty.getArg! 3).getAppFn.constName? | return false
    evalTactic (← `(tactic| unfold LeanQbe.T.Func.wp $(mkIdent c):ident)); return true
  if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 then
    let e := (ty.getArg! 4).headBeta.consumeMData
    match e.getAppFn.constName? with
    | some ``LeanQbe.T.Blocks.get =>
      setGoals (← g.apply (← mkConstWithFreshMVarLevels ``wp_bget_here)); return true
    | some ``LeanQbe.T.Expr.let_ =>
      let s ← saveState
      try
        let [he, hk] := (← g.apply (← mkConstWithFreshMVarLevels ``wp_let_head)).take 2
          | s.restore; return false
        setGoals [he]
        evalTactic (← `(tactic| intro post hpost))
        evalTactic (← `(tactic| dsimp only [LeanQbe.T.OpCode.wp, LeanQbe.T.vals, LeanQbe.T.Arg.val,
          LeanQbe.T.i64, LeanQbe.T.i32, LeanQbe.T.i16, LeanQbe.T.i8, LeanQbe.T.Ty.hasFloat,
          LeanQbe.T.lift1, LeanQbe.T.lift2, LeanQbe.T.liftCmp, LeanQbe.T.CmpOp.evalBits,
          LeanQbe.T.CmpOp.evalBool, Prod.fst, Prod.snd]))
        evalTactic (← `(tactic| try simp only [Bool.false_eq_true, ↓reduceIte,
          BitVec.reduceSignExtend, BitVec.reduceSetWidth, BitVec.reduceAdd, BitVec.reduceMul,
          BitVec.add_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceDiv, Nat.reduceMod]))
        evalTactic (← `(tactic| (try (repeat scc_strip); exact hpost)))
        if !(← getUnsolvedGoals).isEmpty then s.restore; return false
        setGoals [hk]; return true
      catch _ => s.restore; return false
    | some ``LeanQbe.T.Expr.load =>
      let s ← saveState
      try
        let [hl, hk] := (← g.apply (← mkConstWithFreshMVarLevels ``LeanQbe.T.wp_load_of)).take 2
          | s.restore; return false
        setGoals [hl]
        evalTactic (← `(tactic| try simp only [LeanQbe.T.Arg.val, LeanQbe.T.Arg.val_var,
          LeanQbe.T.Arg.val_imm, Prod.fst, Prod.snd]))
        LeanQbe.T.C0Step.memSolve true (← getMainGoal); setGoals [hk]; return true
      catch _ => s.restore; return false
    | some ``LeanQbe.T.Expr.store =>
      let s ← saveState; let m0 := ty.getArg! 5
      try
        let [hs, hk] := (← g.apply (← mkConstWithFreshMVarLevels ``LeanQbe.T.wp_store_sep)).take 2
          | s.restore; return false
        setGoals [hs]
        evalTactic (← `(tactic| try simp only [LeanQbe.T.Arg.val, LeanQbe.T.Arg.val_var,
          LeanQbe.T.Arg.val_imm, Prod.fst, Prod.snd]))
        LeanQbe.T.C0Step.memSolve false (← getMainGoal); setGoals [hk]
        let mId := mkIdent `m; let hmId := mkIdent `hm
        evalTactic (← `(tactic| (intro $mId:ident $hmId:ident; try simp only [LeanQbe.T.Arg.val,
          LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm, Prod.fst, Prod.snd,
          Std.ExtHashMap.sep_emp] at $hmId:ident)))
        clearOldMem m0; return true
      catch _ => s.restore; return false
    | some ``LeanQbe.T.Expr.jnz =>
      let hc := mkIdent `hc
      evalTactic (← `(tactic| refine wp_jnz_head (by simp only [LeanQbe.T.Arg.val,
        LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm, Prod.fst, Prod.snd]; rfl)
        (fun $hc:ident => ?_) (fun $hc:ident => ?_)))
      evalTactic (← `(tactic| all_goals
        (try simp only [_root_.decide_eq_true_eq, _root_.decide_eq_false_iff_not,
          _root_.Bool.not_eq_true, _root_.Bool.not_eq_false, _root_.beq_iff_eq,
          _root_.bne_iff_ne, _root_.ne_eq] at $hc:ident)
        try (exfalso; (try simp only [bv_c0, BitVec.reduceToNat] at $hc:ident); omega)))
      return true
    | some ``LeanQbe.T.Expr.jump =>
      evalTactic (← `(tactic| refine wp_jump_head (by simp only [LeanQbe.T.vals, LeanQbe.T.Arg.val,
        LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm, Prod.fst, Prod.snd]; rfl) ?_))
      evalTactic (← `(tactic| try simp only [Prod.fst, Prod.snd]))
      return true
    | some ``LeanQbe.T.Expr.ret =>
      evalTactic (← `(tactic| refine wp_ret_head (by simp only [LeanQbe.T.vals, LeanQbe.T.Arg.val,
        LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm, Prod.fst, Prod.snd]; rfl) ?_))
      return true
    | some ``LeanQbe.T.Expr.group =>
      if unrollJoin && e.getAppNumArgs == 6 && isJoinLam (e.getArg! 4) then
        let J := mkIdent `J; let hJ := mkIdent `hJ
        evalTactic (← `(tactic| refine LeanQbe.T.wp_unroll_group fun $J:ident $hJ:ident => ?_))
        return true
      return false
    | _ => return false
  if let .fvar J := ty.getAppFn then
    if let some h ← findJoinFVar J then setGoals (← g.apply h); return true
  return false

private meta partial def sccStepsLoop (unrollJoin : Bool) (fuel : Nat) : TacticM Unit := do
  if fuel = 0 then return
  let mut out : Array MVarId := #[]
  for g in ← getUnsolvedGoals do
    if ← g.isAssigned then continue
    setGoals [g]
    if ← sccStepOnce unrollJoin then
      sccStepsLoop unrollJoin (fuel - 1); out := out ++ (← getUnsolvedGoals)
    else out := out.push g
  setGoals out.toList

scoped elab "scc_step" : tactic => do
  evalTactic (← `(tactic| scc_unmdata)); unless ← sccStepOnce true do throwError "scc_step: stuck"
scoped elab "scc_steps" : tactic => do
  evalTactic (← `(tactic| scc_unmdata)); sccStepsLoop true 500
scoped elab "scc_to_group" : tactic => do
  evalTactic (← `(tactic| scc_unmdata)); sccStepsLoop false 500
scoped elab "scc_split" : tactic => do
  evalTactic (← `(tactic| scc_unmdata))
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let ty := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).headBeta.consumeMData).isAppOf ``LeanQbe.T.Expr.jnz then
      let _ ← sccStepOnce false; return
    if ← sccStepOnce false then go (fuel - 1)
  go 100

end HeadStep

end FullSccTactics

open scoped FullArenaTactics FullSccTactics

/-! ## 3. Pure BIG Implication-Graph & Substitution Semantic Lemmas (`FullSccHelpers`) -/

namespace FullSccHelpers

theorem litNeg_eq_xor1 (l : Nat) : litNeg l = l ^^^ 1 := rfl

theorem bv32_xor1_toNat (x : BitVec 32) : (x ^^^ 1#32).toNat = x.toNat ^^^ 1 := by
  simp [BitVec.toNat_xor]

theorem binReach_failed_of_pair {f : CNF Nat} {r x : Nat}
    (h1 : BinReach f r x) (h2 : BinReach f r (litNeg x)) :
    f.EntailsClause (cnfClause [litNeg r]) := by
  have e1 := binReach_sound h1; have e2 := binReach_sound h2
  rw [CNF.entails_clause_def] at e1 e2 ⊢; intro α hα
  have s1 := (clauseEvalVal_iff α _).mpr (e1 α hα)
  have s2 := (clauseEvalVal_iff α _).mpr (e2 α hα); rw [← clauseEvalVal_iff]
  simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false, evalLitVal_litNeg]
    at s1 s2 ⊢
  cases hr : evalLitVal α r <;> cases hx : evalLitVal α x <;> simp_all

theorem litEquiv_contra_unsat {f : CNF Nat} {a b : Nat}
    (h1 : LitEquiv f a b) (h2 : LitEquiv f (litNeg a) b) : f.Unsat := by
  rw [CNF.unsat_iff_not_sat]; intro α hα
  have e1 := litEquiv_eval hα h1; have e2 := litEquiv_eval hα h2
  rw [evalLitVal_litNeg] at e2; cases ha : evalLitVal α a <;> simp_all

/-! ## 4. Watch-Slice Binary Scanning Helpers (`sliceBinsFrom`) -/

/-- Extract all binary-watch target literals from a `WatchSliceOk` watch slice. -/
def sliceBinsFrom (wstk : List (BitVec 32)) : Nat → Nat → List Nat
  | _, 0 => []
  | p, rem + 1 =>
    let w0 := wstk[p]?.getD 0#32
    if (w0 &&& 0x80000000#32) ≠ 0#32 then
      (w0 &&& 0x7FFFFFFF#32).toNat :: sliceBinsFrom wstk (p + 1) rem
    else match rem with
      | 0 => []
      | rem' + 1 => sliceBinsFrom wstk (p + 2) rem'

theorem watchSlice_step_nonbin {F_cur : List (List Nat)} {k : FullCoreState} {nl p rem : Nat}
    (h : WatchSliceOk F_cur k nl p rem) (hpos : 0 < rem)
    (hflag : (k.wstk[p]?.getD 0#32 &&& 0x80000000#32) = 0#32) :
    ∃ w0 cref, 2 ≤ rem ∧ k.wstk[p]? = some w0 ∧ k.wstk[p + 1]? = some cref ∧
      (w0 &&& 0x80000000#32) = 0#32 ∧ cref.toNat < 0x80000000 ∧
      cref.toNat ∈ fullArenaClauseRefsCore k ∧ WatchSliceOk F_cur k nl (p + 2) (rem - 2) ∧
      sliceBinsFrom k.wstk p rem = sliceBinsFrom k.wstk (p + 2) (rem - 2) := by
  cases h with
  | empty => omega
  | @bin _ r w0 hp hf => rw [hp, Option.getD_some] at hflag; exact absurd hflag hf
  | @large _ r w0 cref hp hp1 hf hlt href hrest =>
    refine ⟨w0, cref, by omega, hp, hp1, hf, hlt, href, by simpa using hrest, ?_⟩
    change sliceBinsFrom k.wstk p (r + 1 + 1) = sliceBinsFrom k.wstk (p + 2) (r + 2 - 2)
    conv => lhs; unfold sliceBinsFrom
    simp [hp, hf]

theorem watchSlice_step_bin {F_cur : List (List Nat)} {k : FullCoreState} {nl p rem : Nat}
    (h : WatchSliceOk F_cur k nl p rem) (hpos : 0 < rem)
    (hflag : (k.wstk[p]?.getD 0#32 &&& 0x80000000#32) ≠ 0#32) :
    ∃ w0, k.wstk[p]? = some w0 ∧ (w0 &&& 0x80000000#32) ≠ 0#32 ∧ w0 ≠ 0xFFFFFFFF#32 ∧
      (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [nl, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
      WatchSliceOk F_cur k nl (p + 1) (rem - 1) ∧
      sliceBinsFrom k.wstk p rem =
        (w0 &&& 0x7FFFFFFF#32).toNat :: sliceBinsFrom k.wstk (p + 1) (rem - 1) := by
  cases h with
  | empty => omega
  | @bin _ r w0 hp hf hne hlt hent hrest =>
    refine ⟨w0, hp, hf, hne, hlt, hent, by simpa using hrest, ?_⟩
    conv => lhs; unfold sliceBinsFrom
    simp [hp, hf]
  | @large _ _ w0 _ hp _ hf => rw [hp, Option.getD_some] at hflag; exact absurd hf hflag

theorem watchSlice_mem_sliceBinsFrom {F_cur : List (List Nat)} {k : FullCoreState}
    {nl p rem : Nat} (h : WatchSliceOk F_cur k nl p rem) :
    ∀ ot ∈ sliceBinsFrom k.wstk p rem,
      ot < 2 * k.cur_vars ∧ BinEdge (cnfOfClauses F_cur) (nl ^^^ 1) ot := by
  induction h with
  | empty => intro _ hm; simp [sliceBinsFrom] at hm
  | @bin p r w0 hp hf _ hlt hent _ ih =>
    intro ot hm
    have heq : sliceBinsFrom k.wstk p (r + 1) =
        (w0 &&& 0x7FFFFFFF#32).toNat :: sliceBinsFrom k.wstk (p + 1) r := by
      conv => lhs; unfold sliceBinsFrom
      simp [hp, hf]
    rw [heq, List.mem_cons] at hm; rcases hm with rfl | hm'
    · refine ⟨hlt, ?_⟩; unfold BinEdge; have hnn : litNeg (nl ^^^ 1) = nl := litNeg_litNeg nl
      rwa [hnn]
    · exact ih ot hm'
  | @large p r w0 _ hp _ hf _ _ _ ih =>
    intro ot hm
    have heq : sliceBinsFrom k.wstk p (r + 2) = sliceBinsFrom k.wstk (p + 2) r := by
      change sliceBinsFrom k.wstk p (r + 1 + 1) = _; conv => lhs; unfold sliceBinsFrom
      simp [hp, hf]
    rw [heq] at hm; exact ih ot hm

end FullSccHelpers

open FullSccHelpers

/-! ## 5. `full_tarjan_pop_scc` `Func.wp` Proof (`Full3.lean` #24) -/

theorem full_tarjan_pop_scc_wp (Γ : Env) :
    ∀ args m Q X, fullTarjanPopSccSpec args m Q X →
      Func.wp Γ full_tarjan_pop_scc_body args m Q X := by
  rintro ⟨h, root_lit, lit, mark_root, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, k0, R, rfl, hlen, hw, hinc0, hroot_lt, hlit_lt, htc_le, hrsz_le,
     hk0_lt, hk0_eq, hk0_last, hscc_lt, hscc_eq, hrepr_inv, hunits_inv, hreach, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl := hlen.core_ok; have hsl := hlen.scratch_ok
  have hcv_le := hcl.cur_vars_le
  have hscc_len := hsl.work_stk1_len; have hrepr_len := hcl.repr_len
  have htrc_len := hsl.tarjan_reach_len; have htmk_len := hsl.tarjan_mark_len
  have hunits_len := hsl.shrink_stk_len
  scc_to_group
  refine wp_loop_break_group (brkTs := [i64, i32]) (lpTs := [i64, i32])
    (fun (k, min_l, ()) mb => mb = m ∧ k.toNat = k0 ∧
      min_l.toNat < 2 * s.core.cur_vars ∧
      LitEquiv (cnfOfClauses F_cur) min_l.toNat lit.toNat)
    (fun rem (k, min_l, ()) ml => rem = k.toNat ∧ ml = m ∧
      k0 < k.toNat ∧ k.toNat ≤ s.core.tmp_cnt ∧
      min_l.toNat < 2 * s.core.cur_vars ∧
      LitEquiv (cnfOfClauses F_cur) min_l.toNat lit.toNat)
    ?_ ?_ ?_
  · rintro _ ⟨k, min_l, ⟨⟩⟩ mb ⟨rfl, hk_eq, hmin_lt, hmin_eq⟩
    -- Loop 2: pop `scc[k0 .. scc_top)` and update `repr`, `trc`, `units`, `inconsistent`
    have hfail_init :
        (mark_root == 0xFFFFFFFF#32) = false → mark_root ≠ 0xFFFFFFFF#32 := by
      simp
    have hmin_ne_ff : min_l ≠ 0xFFFFFFFF#32 := fun heq => by
      rw [heq] at hmin_lt; revert hmin_lt; simp; omega
    scc_to_group
    refine wp_loop_break_group (brkTs := [.bool, i64]) (lpTs := [.bool, i64])
      (fun (failed_b, _j, ()) mb =>
        ∃ sb : FullState,
          AgreesExcept popSccMask s sb ∧
          sb.LengthsOk c ∧ FullWitnessInv c F0 F_cur sb.core ∧
          sb.scratch.res_sz.toNat ≤ c.max_vars ∧
          PartialReprInv F_cur sb.core ∧ UnitsSoundInv F_cur sb sb.scratch.res_sz.toNat ∧
          (sb.core.inconsistent = 0#64 ∨ sb.core.inconsistent = 1#64) ∧
          (sb.core.inconsistent ≠ 0#64 → (cnfOfClauses F_cur).Unsat) ∧
          (sb.core.inconsistent = 0#64 →
            (∀ i, k0 ≤ i → i < s.core.tmp_cnt →
              let x := (s.scratch.work_stk1[i]?.getD 0#32).toNat
              sb.core.repr[x]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 ∧
              sb.scratch.tarjan_reach[x]?.getD 0#32 = 0xFFFFFFFF#32) ∧
            (∀ l < 2 * s.core.cur_vars,
              (∀ i, k0 ≤ i → i < s.core.tmp_cnt →
                (s.scratch.work_stk1[i]?.getD 0#32).toNat ≠ l) →
              sb.core.repr[l]? = s.core.repr[l]? ∧
              sb.scratch.tarjan_reach[l]? = s.scratch.tarjan_reach[l]?)) ∧
          (FullMem c sb ⋆ R) mb)
      (fun rem (failed_b, j, ()) ml =>
        ∃ st : FullState,
          AgreesExcept popSccMask s st ∧
          st.core.inconsistent = 0#64 ∧
          rem = s.core.tmp_cnt - j.toNat ∧
          k0 ≤ j.toNat ∧ j.toNat ≤ s.core.tmp_cnt ∧
          st.LengthsOk c ∧ FullWitnessInv c F0 F_cur st.core ∧
          st.scratch.res_sz.toNat ≤ c.max_vars ∧
          PartialReprInv F_cur st.core ∧ UnitsSoundInv F_cur st st.scratch.res_sz.toNat ∧
          (failed_b = false → mark_root ≠ 0xFFFFFFFF#32) ∧
          (∀ i, k0 ≤ i → i < j.toNat →
            let x := (s.scratch.work_stk1[i]?.getD 0#32).toNat
            st.core.repr[x]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 ∧
            st.scratch.tarjan_reach[x]?.getD 0#32 = 0xFFFFFFFF#32) ∧
          (∀ l < 2 * s.core.cur_vars,
            (∀ i, k0 ≤ i → i < j.toNat →
              (s.scratch.work_stk1[i]?.getD 0#32).toNat ≠ l) →
            st.core.repr[l]? = s.core.repr[l]? ∧
            st.scratch.tarjan_reach[l]? = s.scratch.tarjan_reach[l]?) ∧
          (FullMem c st ⋆ R) ml)
      ?_ ?_ ?_
    · rintro _ ⟨failed_b, _j, ⟨⟩⟩ mb
        ⟨sb, hag, hlen', hw', hrsz', hpr', hus', hinc_d, hinc_u, hinc_eff, hmb⟩
      scc_steps
      exact hQ failed_b { sb with core := { sb.core with tmp_cnt := k.toNat } } _
        (hag.update _) hk_eq
        ⟨{ hlen'.core_ok with vals_len := hlen'.core_ok.vals_len }, hlen'.scratch_ok⟩
        { hw' with
          arena := { hw'.arena with len_ok := hw'.arena.len_ok }
          watches := hw'.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
        hrsz' hpr' hus' hinc_d hinc_u hinc_eff hm
    · rintro B L _ ⟨failed_b, j, ⟨⟩⟩ ml hB hL
        ⟨st, hag, hst_inc0, rfl, hj_ge, hj_le, hst_len, hst_w, hrsz', hpr', hus',
         hfb_mr, hdone, hkeep, hml⟩
      have hst_cv : st.core.cur_vars = s.core.cur_vars := hag.get (·.core.cur_vars)
      have hst_scc : st.scratch.work_stk1 = s.scratch.work_stk1 := hag.get (·.scratch.work_stk1)
      have hst_tmk : st.scratch.tarjan_mark = s.scratch.tarjan_mark :=
        hag.get (·.scratch.tarjan_mark)
      have hst_cl := hst_len.core_ok; have hst_sl := hst_len.scratch_ok
      have hrp_l : st.core.repr.length = 2 * c.max_vars := hst_cl.repr_len
      have htr_l : st.scratch.tarjan_reach.length = 2 * c.max_vars := hst_sl.tarjan_reach_len
      have hun_l : st.scratch.shrink_stk.length = c.max_vars := hst_sl.shrink_stk_len
      have hscc_l : st.scratch.work_stk1.length = 2 * c.max_vars := hst_sl.work_stk1_len
      have htmk_l : st.scratch.tarjan_mark.length = 2 * c.max_vars := hst_sl.tarjan_mark_len
      scc_split
      · have hj_lt : j.toNat < s.core.tmp_cnt := by c0_bound
        let other := st.scratch.work_stk1[j.toNat]'(by omega)
        have hoth_get : other = s.scratch.work_stk1[j.toNat]?.getD 0#32 := by
          have hj_s : j.toNat < s.scratch.work_stk1.length := by omega
          simp [other, hst_scc, List.getElem?_eq_getElem hj_s]
        have hoth_lt : other.toNat < 2 * s.core.cur_vars := by
          rw [hoth_get]; exact hscc_lt j.toNat hj_lt
        have hoth_lt' : (st.scratch.work_stk1[j.toNat]'(by omega)).toNat < 2 * s.core.cur_vars :=
          hoth_lt
        have hnoth_lt : (other ^^^ 1#32).toNat < 2 * s.core.cur_vars := by
          rw [bv32_xor1_toNat]; exact litNeg_lt_two_mul hoth_lt
        have hnoth_lt' :
            (st.scratch.work_stk1[j.toNat]'(by omega)).toNat ^^^ 1 < 2 * s.core.cur_vars := by
          rw [← bv32_xor1_toNat]; exact hnoth_lt
        have hoth_eq_lit : LitEquiv (cnfOfClauses F_cur) other.toNat lit.toNat := by
          rw [hoth_get]; exact hscc_eq j.toNat hj_ge hj_lt
        have hoth_eq_min : LitEquiv (cnfOfClauses F_cur) other.toNat min_l.toNat :=
          hoth_eq_lit.trans hmin_eq.symm
        let st1 : FullState :=
          { st with
            core := { st.core with repr := st.core.repr.set other.toNat min_l }
            scratch := { st.scratch with
              tarjan_reach := st.scratch.tarjan_reach.set other.toNat 0xFFFFFFFF#32 } }
        have hag1 : AgreesExcept popSccMask s st1 := hag.update _
        have hlen1 : st1.LengthsOk c :=
          ⟨{ hst_cl with repr_len := by simp [st1, hrp_l] },
           { hst_sl with tarjan_reach_len := by simp [st1, htr_l] }⟩
        have hw1 : FullWitnessInv c F0 F_cur st1.core :=
          { hst_w with
            arena := { hst_w.arena with len_ok := hst_w.arena.len_ok }
            watches := hst_w.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
        have hpr1 : PartialReprInv F_cur st1.core := by
          intro l hl; dsimp only [st1] at hl ⊢; rw [hst_cv] at hl; intro hne
          by_cases hlo : l = other.toNat
          · subst hlo; rw [List.getElem?_set_self (by omega), Option.getD_some]
            exact ⟨by omega, hoth_eq_min⟩
          · rw [List.getElem?_set_ne (Ne.symm hlo)] at hne ⊢
            exact hpr' l (by omega) hne
        have hdone1 : ∀ i, k0 ≤ i → i < j.toNat + 1 →
            let x := (s.scratch.work_stk1[i]?.getD 0#32).toNat
            st1.core.repr[x]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 ∧
            st1.scratch.tarjan_reach[x]?.getD 0#32 = 0xFFFFFFFF#32 := by
          intro i hi1 hi2; dsimp only [st1]
          by_cases hij : i = j.toNat
          · have hx : (s.scratch.work_stk1[i]?.getD 0#32).toNat = other.toNat := by
              rw [hij, ← hoth_get]
            rw [hx, List.getElem?_set_self (by omega), List.getElem?_set_self (by omega),
              Option.getD_some, Option.getD_some]
            exact ⟨hmin_ne_ff, rfl⟩
          · have hx_lt := hscc_lt i (by omega)
            by_cases hxo : (s.scratch.work_stk1[i]?.getD 0#32).toNat = other.toNat
            · rw [hxo, List.getElem?_set_self (by omega), List.getElem?_set_self (by omega),
                Option.getD_some, Option.getD_some]
              exact ⟨hmin_ne_ff, rfl⟩
            · rw [List.getElem?_set_ne (Ne.symm hxo), List.getElem?_set_ne (Ne.symm hxo)]
              exact hdone i hi1 (by omega)
        have hkeep1 : ∀ l < 2 * s.core.cur_vars,
            (∀ i, k0 ≤ i → i < j.toNat + 1 →
              (s.scratch.work_stk1[i]?.getD 0#32).toNat ≠ l) →
            st1.core.repr[l]? = s.core.repr[l]? ∧
            st1.scratch.tarjan_reach[l]? = s.scratch.tarjan_reach[l]? := by
          intro l hl hall
          have hne_o : other.toNat ≠ l := by
            have := hall j.toNat hj_ge (by omega); rwa [← hoth_get] at this
          dsimp only [st1]
          rw [List.getElem?_set_ne hne_o, List.getElem?_set_ne hne_o]
          exact hkeep l hl fun i hi1 hi2 => hall i hi1 (by omega)
        have hus1_keep : UnitsSoundInv F_cur st1 st1.scratch.res_sz.toNat := hus'
        have hz_other : (BitVec.setWidth 64 other).toNat = other.toNat :=
          zext_toNat other (by decide)
        have htmk1_l : st1.scratch.tarjan_mark.length = 2 * c.max_vars :=
          hlen1.scratch_ok.tarjan_mark_len
        have hun1_l : st1.scratch.shrink_stk.length = c.max_vars := hlen1.scratch_ok.shrink_stk_len
        -- Step up to `ro == min_lit` branch
        scc_split
        · -- `ro == min_lit`: contradiction -> UNSAT
          have hro_eq : st1.core.repr[(other ^^^ 1#32).toNat]'(by
              simp only [st1, List.length_set, hrp_l]; omega) = min_l := by
            have h1 : (BitVec.setWidth 64 (st.scratch.work_stk1[j.toNat]'(by omega) ^^^
                (1 : BitVec 32))).toNat = other.toNat ^^^ 1 := by
              rw [zext_toNat _ (by decide), show (1 : BitVec 32) = 1#32 from rfl, bv32_xor1_toNat]
            dsimp only [other] at hz_other
            simpa only [st1, other, hz_other, h1, bv32_xor1_toNat] using hc
          have hunsat : (cnfOfClauses F_cur).Unsat := by
            have hro_get : st1.core.repr[(other ^^^ 1#32).toNat]?.getD 0xFFFFFFFF#32 = min_l := by
              rw [List.getElem?_eq_getElem (by simp only [st1, List.length_set, hrp_l]; omega),
                Option.getD_some]
              exact hro_eq
            have hno_eq :=
              (hpr1 (other ^^^ 1#32).toNat (by simp [st1, hst_cv]; exact hnoth_lt)
                (by rw [hro_get]; exact hmin_ne_ff)).2
            rw [hro_get, bv32_xor1_toNat] at hno_eq
            exact litEquiv_contra_unsat hoth_eq_min hno_eq
          have hm_st1 : (FullMem c st1 ⋆ R) m := hm
          clear hm
          scc_steps
          · have hrsz_lt : st1.scratch.res_sz.toNat < c.max_vars := by c0_bound
            have hrsz_inc : (st1.scratch.res_sz + 1#64).toNat = st1.scratch.res_sz.toNat + 1 := by
              c0_bound
            dsimp only [st1] at hrsz_lt hrsz_inc
            let st2 : FullState :=
              { st1 with
                core := { st1.core with inconsistent := 1#64 }
                scratch := { st1.scratch with
                  shrink_stk := st1.scratch.shrink_stk.set st1.scratch.res_sz.toNat min_l
                  res_sz := st1.scratch.res_sz + 1#64 } }
            have hus2 : UnitsSoundInv F_cur st2 st2.scratch.res_sz.toNat := by
              intro i hi; dsimp only [st2, st1] at hi ⊢
              by_cases hir : i = st.scratch.res_sz.toNat
              · subst hir; rw [List.getElem?_set_self (by omega), Option.getD_some]
                exact ⟨by omega, CNF.entails_clause_def.mpr fun α hα =>
                  absurd hα (CNF.unsat_iff_not_sat.mp hunsat α)⟩
              · rw [List.getElem?_set_ne (Ne.symm hir)]; exact hus' i (by omega)
            exact hB (failed_b, j, ()) _
              ⟨st2, hag1.update _,
               ⟨{ hlen1.core_ok with vals_len := hlen1.core_ok.vals_len },
                { hlen1.scratch_ok with shrink_stk_len := by simp [st2, st1, hun_l] }⟩,
               { hw1 with
                 inconsistent_sound := fun _ => hunsat
                 arena := { hw1.arena with len_ok := hw1.arena.len_ok }
                 watches := hw1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
               by dsimp only [st2, st1]; omega, hpr1, hus2, Or.inr rfl,
               fun _ => hunsat, (fun h => by cases h), hm⟩
          · let st2 : FullState := { st1 with core := { st1.core with inconsistent := 1#64 } }
            exact hB (failed_b, j, ()) _
              ⟨st2, hag1.update _,
               ⟨{ hlen1.core_ok with vals_len := hlen1.core_ok.vals_len }, hlen1.scratch_ok⟩,
               { hw1 with
                 inconsistent_sound := fun _ => hunsat
                 arena := { hw1.arena with len_ok := hw1.arena.len_ok }
                 watches := hw1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
               hrsz', hpr1, hus1_keep, Or.inr rfl, fun _ => hunsat, (fun h => by cases h), hm⟩
        · -- `ro ≠ min_lit`
          have hm_st1 : (FullMem c st1 ⋆ R) m := hm
          clear hm
          have hj1 : (j + 1#64).toNat = j.toNat + 1 := by c0_bound
          scc_steps
          · -- already `failed = true`
            exact hL (s.core.tmp_cnt - (j.toNat + 1)) (failed_b, j + 1#64, ()) _ (by omega)
              ⟨st1, hag1, hst_inc0, by omega, by omega, by omega, hlen1, hw1, hrsz',
               hpr1, hus1_keep, hfb_mr,
               fun i hi1 hi2 => hdone1 i hi1 (by omega),
               fun l hl hall => hkeep1 l hl fun i hi1 hi2 => hall i hi1 (by omega), hm_st1⟩
          · -- failed-lit detected, `res_sz < max_vars`
            have hfb_f : failed_b = false := by assumption
            have hmr_ne : mark_root ≠ 0xFFFFFFFF#32 := hfb_mr hfb_f
            have hmr_le : mark_root.toNat ≤
                (s.scratch.tarjan_mark[(other ^^^ 1#32).toNat]?.getD 0#32).toNat := by
              rw [← hst_tmk, List.getElem?_eq_getElem (by omega), Option.getD_some]
              have hle : mark_root.toNat ≤
                  (st1.scratch.tarjan_mark[other.toNat ^^^ 1]'(by
                    rw [← bv32_xor1_toNat]; omega)).toNat := by
                dsimp only [other]; c0_bound
              simpa only [st1, ← bv32_xor1_toNat] using hle
            have hbr1 : BinReach (cnfOfClauses F_cur) root_lit.toNat other.toNat := by
              have := (hreach hmr_ne).1 j.toNat hj_ge hj_lt; rwa [← hoth_get] at this
            have hbr2 : BinReach (cnfOfClauses F_cur) root_lit.toNat (litNeg other.toNat) := by
              have := (hreach hmr_ne).2 (other ^^^ 1#32).toNat hnoth_lt hmr_le
              rwa [bv32_xor1_toNat] at this
            have hent_rf :
                (cnfOfClauses F_cur).EntailsClause (cnfClause [(root_lit ^^^ 1#32).toNat]) := by
              rw [bv32_xor1_toNat]; exact binReach_failed_of_pair hbr1 hbr2
            have hrsz_lt : st1.scratch.res_sz.toNat < c.max_vars := by c0_bound
            have hrsz_inc : (st1.scratch.res_sz + 1#64).toNat = st1.scratch.res_sz.toNat + 1 := by
              c0_bound
            dsimp only [st1] at hrsz_lt hrsz_inc
            let st2 : FullState :=
              { st1 with
                scratch := { st1.scratch with
                  shrink_stk :=
                    st1.scratch.shrink_stk.set st1.scratch.res_sz.toNat (root_lit ^^^ 1#32)
                  res_sz := st1.scratch.res_sz + 1#64 } }
            have hus2 : UnitsSoundInv F_cur st2 st2.scratch.res_sz.toNat := by
              intro i hi; dsimp only [st2, st1] at hi ⊢
              by_cases hir : i = st.scratch.res_sz.toNat
              · subst hir; rw [List.getElem?_set_self (by omega), Option.getD_some]
                exact ⟨by rw [hst_cv, bv32_xor1_toNat]; exact litNeg_lt_two_mul hroot_lt, hent_rf⟩
              · rw [List.getElem?_set_ne (Ne.symm hir)]; exact hus' i (by omega)
            exact hL (s.core.tmp_cnt - (j.toNat + 1)) (true, j + 1#64, ()) _ (by omega)
              ⟨st2, hag1.update _, hst_inc0, by omega, by omega, by omega,
               ⟨hlen1.core_ok,
                { hlen1.scratch_ok with shrink_stk_len := by simp [st2, st1, hun_l] }⟩,
               hw1, by dsimp only [st2, st1]; omega, hpr1, hus2, (fun h => by cases h),
               fun i hi1 hi2 => hdone1 i hi1 (by omega),
               fun l hl hall => hkeep1 l hl fun i hi1 hi2 => hall i hi1 (by omega), hm⟩
          · -- failed-lit detected, `res_sz ≥ max_vars`
            exact hL (s.core.tmp_cnt - (j.toNat + 1)) (true, j + 1#64, ()) _ (by omega)
              ⟨st1, hag1, hst_inc0, by omega, by omega, by omega, hlen1, hw1, hrsz',
               hpr1, hus1_keep, (fun h => by cases h),
               fun i hi1 hi2 => hdone1 i hi1 (by omega),
               fun l hl hall => hkeep1 l hl fun i hi1 hi2 => hall i hi1 (by omega), hm_st1⟩
          · -- not failed-lit (`tmk < mark_root`)
            exact hL (s.core.tmp_cnt - (j.toNat + 1)) (failed_b, j + 1#64, ()) _ (by omega)
              ⟨st1, hag1, hst_inc0, by omega, by omega, by omega, hlen1, hw1, hrsz',
               hpr1, hus1_keep, hfb_mr,
               fun i hi1 hi2 => hdone1 i hi1 (by omega),
               fun l hl hall => hkeep1 l hl fun i hi1 hi2 => hall i hi1 (by omega), hm_st1⟩
          · -- `ro == 0xFFFFFFFFu`
            exact hL (s.core.tmp_cnt - (j.toNat + 1)) (failed_b, j + 1#64, ()) _ (by omega)
              ⟨st1, hag1, hst_inc0, by omega, by omega, by omega, hlen1, hw1, hrsz',
               hpr1, hus1_keep, hfb_mr,
               fun i hi1 hi2 => hdone1 i hi1 (by omega),
               fun l hl hall => hkeep1 l hl fun i hi1 hi2 => hall i hi1 (by omega), hm_st1⟩
      · -- `j ≥ scc_top`: normal exit
        have hj_eq : j.toNat = s.core.tmp_cnt := by c0_bound
        scc_steps
        exact hB (failed_b, j, ()) ml
          ⟨st, hag, hst_len, hst_w, hrsz', hpr', hus', Or.inl hst_inc0,
           fun h => absurd hst_inc0 h,
           fun _ => ⟨fun i hi1 hi2 => hdone i hi1 (by omega),
                     fun l hl hall => hkeep l hl fun i hi1 hi2 => hall i hi1 (by omega)⟩, hml⟩
    · intro B L _ hL
      scc_steps
      exact hL (s.core.tmp_cnt - k0) (mark_root == 0xFFFFFFFF#32, k, ()) mb
        ⟨s, AgreesExcept.refl _ _, hinc0, by omega, by omega, by omega, hlen, hw, hrsz_le,
         hrepr_inv, hunits_inv, hfail_init, fun _ _ _ => by omega,
         fun _ _ _ => ⟨rfl, rfl⟩, hm⟩
  · rintro B L _ ⟨k, min_l, ⟨⟩⟩ ml hB hL ⟨rfl, rfl, hk_gt, hk_le, hmin_lt, hmin_eq⟩
    -- Loop 1 body
    have hk_sub : (k - 1#64).toNat = k.toNat - 1 := by c0_bound
    have hx_get : s.scratch.work_stk1[(k - 1#64).toNat]'(by omega) =
        s.scratch.work_stk1[k.toNat - 1]?.getD 0#32 := by
      have hk1_s : k.toNat - 1 < s.scratch.work_stk1.length := by omega
      simp [hk_sub, List.getElem?_eq_getElem hk1_s]
    have hx_lt : (s.scratch.work_stk1[(k - 1#64).toNat]'(by omega)).toNat < 2 * s.core.cur_vars :=
      by rw [hx_get]; exact hscc_lt (k.toNat - 1) (by omega)
    have hx_eq : LitEquiv (cnfOfClauses F_cur)
        (s.scratch.work_stk1[(k - 1#64).toNat]'(by omega)).toNat lit.toNat := by
      rw [hx_get]; exact hscc_eq (k.toNat - 1) (by omega) (by omega)
    have hk_eq_or_gt : (s.scratch.work_stk1[(k - 1#64).toNat]'(by omega) = lit →
        (k - 1#64).toNat = k0) ∧
        (s.scratch.work_stk1[(k - 1#64).toNat]'(by omega) ≠ lit → k0 < (k - 1#64).toNat) := by
      refine ⟨fun heq => Classical.byContradiction fun hne0 => ?_,
              fun hne => Classical.byContradiction fun hle0 => ?_⟩
      · have hgt0 : k0 < k.toNat - 1 := by omega
        exact hk0_last (k.toNat - 1) hgt0 (by omega) (by rw [← hx_get]; exact heq)
      · have heq0 : k.toNat - 1 = k0 := by omega
        exact hne (by rw [hx_get, heq0]; exact hk0_eq)
    scc_steps
    · exact hB (k - 1#64, s.scratch.work_stk1[(k - 1#64).toNat]'(by omega), ()) ml
        ⟨rfl, hk_eq_or_gt.1 (by assumption), hx_lt, hx_eq⟩
    · exact hL (k - 1#64).toNat
        (k - 1#64, s.scratch.work_stk1[(k - 1#64).toNat]'(by omega), ()) ml
        (by omega) ⟨rfl, rfl, hk_eq_or_gt.2 (by assumption), by omega, hx_lt, hx_eq⟩
    · exact hB (k - 1#64, min_l, ()) ml
        ⟨rfl, hk_eq_or_gt.1 (by assumption), hmin_lt, hmin_eq⟩
    · exact hL (k - 1#64).toNat (k - 1#64, min_l, ()) ml
        (by omega) ⟨rfl, rfl, hk_eq_or_gt.2 (by assumption), by omega, hmin_lt, hmin_eq⟩
  · intro B L _ hL
    scc_steps
    exact hL s.core.tmp_cnt (BitVec.ofNat 64 s.core.tmp_cnt, lit, ()) m
      ⟨by c0_bound, rfl, by c0_bound, by c0_bound, hlit_lt, LitEquiv.refl _ _⟩

/-! ## 6. Tarjan SCC State Mask, Witness Preservation & `TarjanDfsInv` (`FullSccHelpers`) -/

namespace FullSccHelpers

theorem bv32_trunc_toNat {x : BitVec 64} (h : x.toNat < 2 ^ 32) :
    (BitVec.setWidth 32 x).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h]

theorem binReach_trans {f : CNF Nat} {a b c : Nat} (h1 : BinReach f a b) (h2 : BinReach f b c) :
    BinReach f a c := by
  induction h1 with
  | refl => exact h2
  | step e _ ih => exact .step e (ih h2)

theorem arenaVarsNodup_of_arena_eq {s s' : FullState}
    (ha : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    (h : FullArenaVarsNodup s) : FullArenaVarsNodup s' := fun r hr hng => by
  unfold fullArenaClauseRefs fullArenaClauseRefsCore at hr
  unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hng
  unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore
  rw [ha, hal] at hr; rw [ha] at hng ⊢; exact h r hr hng

/-- State mask covering all fields mutated by `full_tarjan_scc`. -/
def tarjanSccMask (s : FullState) : FullState :=
  { s with
    core := { s.core with repr := [], tmp_cnt := 0, inconsistent := 0#64 }
    scratch := { s.scratch with
      tarjan_mark := [], tarjan_reach := [], work_stk1 := [], work_stk2 := [],
      wsort := [], shrink_stk := [], res_sz := 0#64 } }

theorem agrees_popScc_to_tarjan {s st st' : FullState}
    (h1 : AgreesExcept tarjanSccMask s st) (h2 : AgreesExcept popSccMask st st') :
    AgreesExcept tarjanSccMask s st' := by
  unfold AgreesExcept at h1 h2 ⊢
  have heq : ∀ t, tarjanSccMask (popSccMask t) = tarjanSccMask t := fun _ => rfl
  rw [← heq st', h2, heq st, h1]

theorem agrees_tarjanSccMask_eq {s0 st : FullState}
    (hag : AgreesExcept tarjanSccMask s0 st) :
    ({ s0 with
        core := { s0.core with
          repr := st.core.repr, tmp_cnt := st.core.tmp_cnt
          inconsistent := st.core.inconsistent }
        scratch := { s0.scratch with
          tarjan_mark := st.scratch.tarjan_mark, tarjan_reach := st.scratch.tarjan_reach
          work_stk1 := st.scratch.work_stk1, work_stk2 := st.scratch.work_stk2
          wsort := st.scratch.wsort, shrink_stk := st.scratch.shrink_stk
          res_sz := st.scratch.res_sz } } : FullState) = st := by
  rcases s0 with ⟨c0, sc0⟩; rcases st with ⟨c1, sc1⟩
  cases c0; cases c1; cases sc0; cases sc1
  simp only [AgreesExcept, tarjanSccMask] at hag
  injection hag with hc hsc; cases hc; cases hsc; rfl

theorem tarjanScc_preserves_witness {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hag : AgreesExcept tarjanSccMask s0 st)
    (hinc : st.core.inconsistent ≠ 0#64 → (cnfOfClauses F_cur).Unsat) :
    FullWitnessInv c F0 F_cur st.core := by
  have hcv := hag.get (·.core.cur_vars); have hal := hag.get (·.core.arena_len)
  have har := hag.get (·.core.arena); have hwv := hag.get (·.core.wvec)
  have hws := hag.get (·.core.wstk); have hwl := hag.get (·.core.wlen)
  have hdm := hag.get (·.core.dense_mode); have hvl := hag.get (·.core.vals)
  have hlv := hag.get (·.core.lvl); have hrs := hag.get (·.core.rsns)
  have htr := hag.get (·.core.trl); have htp := hag.get (·.core.trail_pos)
  have hte := hag.get (·.core.trail_end); have hcl := hag.get (·.core.cur_level)
  have hft := hag.get (·.core.frame_trail); have hfd := hag.get (·.core.frame_dec)
  have hrefs : fullArenaClauseRefsCore st.core = fullArenaClauseRefsCore s0.core := by
    unfold fullArenaClauseRefsCore; rw [har, hal]
  have hgarb : ∀ r, fullArenaClauseGarbCore st.core r = fullArenaClauseGarbCore s0.core r :=
    fun r => by unfold fullArenaClauseGarbCore fullArenaHdrCore; rw [har]
  have hlits : ∀ r, fullArenaClauseLitsCore st.core r = fullArenaClauseLitsCore s0.core r :=
    fun r => by unfold fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [har]
  have hsz : ∀ r, fullArenaClauseSizeCore st.core r = fullArenaClauseSizeCore s0.core r :=
    fun r => by unfold fullArenaClauseSizeCore; rw [har]
  exact
    { ext_sound := by rw [hcv]; exact hw0.ext_sound, inconsistent_sound := hinc
      arena :=
        { len_ok := by rw [hal]; exact hw0.arena.len_ok
          refs_wf := fun r hr => by
            rw [hrefs] at hr; rw [hal, har, hsz]; exact hw0.arena.refs_wf r hr
          shrk_term := fun r hr hsh => by
            rw [hrefs] at hr; unfold fullArenaHdrCore at hsh; rw [har] at hsh
            rw [hsz, hal, har]; exact hw0.arena.shrk_term r hr hsh
          lits_lt := fun r hr hg l hl => by
            rw [hrefs] at hr; rw [hgarb] at hg; rw [hlits] at hl; rw [hcv]
            exact hw0.arena.lits_lt r hr hg l hl
          entails := fun r hr hg => by
            rw [hrefs] at hr; rw [hgarb] at hg; rw [hlits]; exact hw0.arena.entails r hr hg }
      watches := hw0.watches.with_wstk hdm hcv hwv hws hwl (fun r hr => by rw [hrefs]; exact hr)
      cur_level_le := by rw [hcl, hte]; exact hw0.cur_level_le
      trail_lits_lt := fun i hi => by rw [htr, hcv]; exact hw0.trail_lits_lt i (hte ▸ hi)
      trail_vars_nodup := fun i j hi hj h => by
        rw [htr] at h; exact hw0.trail_vars_nodup i j (hte ▸ hi) (hte ▸ hj) h
      vals_domain := fun l hl => by rw [hvl]; exact hw0.vals_domain l (hcv ▸ hl)
      vals_true_iff := fun l hl => by rw [hvl, hte, htr]; exact hw0.vals_true_iff l (hcv ▸ hl)
      vals_false_iff := fun l hl => by rw [hvl, hte, htr]; exact hw0.vals_false_iff l (hcv ▸ hl)
      lvl_le := fun i hi => by rw [hlv, htr, hcl]; exact hw0.lvl_le i (hte ▸ hi)
      dec_earliest := fun i j hi hj h1 h2 => by
        rw [hlv, htr] at h1; rw [hlv, hrs, htr] at h2
        exact hw0.dec_earliest i j (hte ▸ hi) (hte ▸ hj) h1 h2
      levels_inhabited := fun L h1 h2 => by
        rw [hte, hlv, htr]; exact hw0.levels_inhabited L h1 (hcl ▸ h2)
      level0_sound := fun i hi hl0 => by
        rw [hlv, htr] at hl0; rw [htr]; exact hw0.level0_sound i (hte ▸ hi) hl0
      trail_pos_inv := fun i hi => by rw [htp, htr]; exact hw0.trail_pos_inv i (hte ▸ hi)
      level0_rsn_none := fun i hi hl0 => by
        rw [hlv, htr] at hl0; rw [hrs, htr]; exact hw0.level0_rsn_none i (hte ▸ hi) hl0
      frame_trail_lt := fun L hL => by rw [hft, hte]; exact hw0.frame_trail_lt L (hcl ▸ hL)
      frame_trail_mono := fun L1 L2 h1 h2 => by
        rw [hft]; exact hw0.frame_trail_mono L1 L2 h1 (hcl ▸ h2)
      frame_trail_before_lt := fun L h1 h2 i hi => by
        rw [hft] at hi; rw [hlv, htr]; exact hw0.frame_trail_before_lt L h1 (hcl ▸ h2) i hi
      frame_dec_lt := fun L h1 h2 => by rw [hfd, hcv]; exact hw0.frame_dec_lt L h1 (hcl ▸ h2)
      reason_inv := fun i hi hne => by
        rw [hrs, htr] at hne ⊢; rw [hlv, hcv, hrefs]
        have hr := hw0.reason_inv i (hte ▸ hi) hne
        by_cases hb : (s0.core.rsns[(s0.core.trl[i]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
        · rw [ite_eq_left hb] at hr ⊢; exact hr
        · rw [ite_eq_right hb] at hr ⊢; rw [hgarb, hlits]; exact hr
      reason_lit_mem := fun i hi hne hlg => by
        rw [hrs, htr] at hne hlg ⊢; rw [hlits]; exact hw0.reason_lit_mem i (hte ▸ hi) hne hlg }

theorem tarjanScc_preserves_sparse {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} (hsp0 : FullSparseInvW c F0 F_cur s0)
    (hag : AgreesExcept tarjanSccMask s0 st) (hlen : st.LengthsOk c)
    (hinc : st.core.inconsistent ≠ 0#64 → (cnfOfClauses F_cur).Unsat) :
    FullSparseInvW c F0 F_cur st :=
  ⟨hlen, tarjanScc_preserves_witness hsp0.2.1 hag hinc,
   ⟨fun v hv => by rw [hag.get (·.core.mrk)]; exact hsp0.2.2.1.1 v hv,
    fun l hl => by rw [hag.get (·.core.lit_mark)]; exact hsp0.2.2.1.2 l hl⟩,
   arenaVarsNodup_of_arena_eq (hag.get (·.core.arena)) (hag.get (·.core.arena_len))
     hsp0.2.2.2.1,
   ⟨fun i hi => by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore
      rw [hag.get (·.core.arena), hag.get (·.core.arena_len), hag.get (·.scratch.last_learned)]
      exact hsp0.2.2.2.2.1.1 i hi,
    by rw [hag.get (·.scratch.extend_len)]; exact hsp0.2.2.2.2.1.2⟩,
   by rw [hag.get (·.core.dense_mode)]; exact hsp0.2.2.2.2.2⟩

/-- Common base invariants carried across all `full_tarjan_scc` loops and joins. -/
def TarjanLoopBase (c : FullCfg) (F_cur : List (List Nat)) (s0 st : FullState) : Prop :=
  AgreesExcept tarjanSccMask s0 st ∧ st.LengthsOk c ∧ st.scratch.res_sz.toNat ≤ c.max_vars ∧
  PartialReprInv F_cur st.core ∧ UnitsSoundInv F_cur st st.scratch.res_sz.toNat ∧
  (st.core.inconsistent ≠ 0#64 → (cnfOfClauses F_cur).Unsat)

def activeLit (s0 : FullState) (l : Nat) : Prop :=
  l < 2 * s0.core.cur_vars ∧ (s0.core.flags[l / 2]?.getD 0#32 &&& 1#32) ≠ 0#32

def activeEdge (s0 : FullState) (u v : Nat) : Prop :=
  activeLit s0 u ∧ activeLit s0 v ∧
  v ∈ sliceBinsFrom s0.core.wstk (fullWatchOffCore s0.core (u ^^^ 1))
    (fullWatchSizeCore s0.core (u ^^^ 1))

theorem activeEdge_binEdge {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} (hw0 : FullWitnessInv c F0 F_cur s0.core) (hdm : s0.core.dense_mode = 0#64)
    {u v : Nat} (he : activeEdge s0 u v) : BinEdge (cnfOfClauses F_cur) u v := by
  have hwat : WatchesInv F_cur s0.core := by
    have hm := hw0.watches; unfold ModeWatchesInv at hm; rwa [ite_eq_left hdm] at hm
  have hbe :=
    watchSlice_mem_sliceBinsFrom (hwat.slices (u ^^^ 1) (litNeg_lt_two_mul he.1.1)) v he.2.2
  simpa only [← litNeg_eq_xor1, litNeg_litNeg] using hbe.2

def onScc (st : FullState) (l : Nat) : Prop :=
  ∃ j < st.core.tmp_cnt, (st.scratch.work_stk1[j]?.getD 0#32).toNat = l

def onDv (st : FullState) (dsp l : Nat) : Prop :=
  ∃ i < dsp, (st.scratch.work_stk2[i]?.getD 0#32).toNat = l

def dvWorkSum (s0 st : FullState) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    let lit := (st.scratch.work_stk2[k]?.getD 0#32).toNat
    let sz := fullWatchSizeCore s0.core (lit ^^^ 1)
    let pos := (st.scratch.wsort[k]?.getD 0#32).toNat
    dvWorkSum s0 st k + (sz - pos + 1)

theorem dvWorkSum_congr {s0 st1 st2 : FullState} :
    ∀ k, (∀ i < k, st1.scratch.work_stk2[i]? = st2.scratch.work_stk2[i]? ∧
      st1.scratch.wsort[i]? = st2.scratch.wsort[i]?) →
      dvWorkSum s0 st1 k = dvWorkSum s0 st2 k
  | 0, _ => rfl
  | k + 1, h => by
    unfold dvWorkSum
    rw [dvWorkSum_congr k (fun i hi => h i (by omega)), (h k (by omega)).1, (h k (by omega)).2]

/-- Complete Tarjan SCC invariant across outer (`dsp = 0`, `tmp_cnt = 0`) and inner DFS loops. -/
structure TarjanDfsInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 : FullState) (root mroot reached dsp : Nat) (st : FullState) : Prop where
  agrees : AgreesExcept tarjanSccMask s0 st
  len_ok : st.LengthsOk c
  inc0 : st.core.inconsistent = 0#64
  rsz_le : st.scratch.res_sz.toNat ≤ c.max_vars
  partial_repr : PartialReprInv F_cur st.core
  units_ok : UnitsSoundInv F_cur st st.scratch.res_sz.toNat
  reached_le : reached ≤ 2 * s0.core.cur_vars
  tmk_le : ∀ l < 2 * s0.core.cur_vars, (st.scratch.tarjan_mark[l]?.getD 0#32).toNat ≤ reached
  tmk_inj : ∀ a b, a < 2 * s0.core.cur_vars → b < 2 * s0.core.cur_vars →
    1 ≤ (st.scratch.tarjan_mark[a]?.getD 0#32).toNat →
    (st.scratch.tarjan_mark[a]?.getD 0#32).toNat = (st.scratch.tarjan_mark[b]?.getD 0#32).toNat →
    a = b
  tmk_surj : ∀ t, 1 ≤ t → t ≤ reached →
    ∃ l < 2 * s0.core.cur_vars, (st.scratch.tarjan_mark[l]?.getD 0#32).toNat = t
  tmk_active : ∀ l < 2 * s0.core.cur_vars,
    1 ≤ (st.scratch.tarjan_mark[l]?.getD 0#32).toNat → activeLit s0 l
  top_le : st.core.tmp_cnt ≤ reached
  scc_lt : ∀ i < st.core.tmp_cnt, (st.scratch.work_stk1[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars
  scc_tmk_ge : ∀ i < st.core.tmp_cnt,
    1 ≤ mroot ∧ mroot ≤ (st.scratch.tarjan_mark[(st.scratch.work_stk1[i]?.getD 0#32).toNat]?.getD
      0#32).toNat
  scc_tmk_mono : ∀ i j, i < j → j < st.core.tmp_cnt →
    (st.scratch.tarjan_mark[(st.scratch.work_stk1[i]?.getD 0#32).toNat]?.getD 0#32).toNat <
    (st.scratch.tarjan_mark[(st.scratch.work_stk1[j]?.getD 0#32).toNat]?.getD 0#32).toNat
  scc_iff_trc : ∀ l < 2 * s0.core.cur_vars,
    onScc st l ↔
      (1 ≤ (st.scratch.tarjan_mark[l]?.getD 0#32).toNat ∧
       st.scratch.tarjan_reach[l]?.getD 0#32 ≠ 0xFFFFFFFF#32)
  trc_range : ∀ i < st.core.tmp_cnt,
    let x := (st.scratch.work_stk1[i]?.getD 0#32).toNat
    mroot ≤ (st.scratch.tarjan_reach[x]?.getD 0#32).toNat ∧
    (st.scratch.tarjan_reach[x]?.getD 0#32).toNat ≤ (st.scratch.tarjan_mark[x]?.getD 0#32).toNat
  trc_witness : ∀ i < st.core.tmp_cnt,
    let x := (st.scratch.work_stk1[i]?.getD 0#32).toNat
    ∃ w < 2 * s0.core.cur_vars, onScc st w ∧
      (st.scratch.tarjan_mark[w]?.getD 0#32).toNat = (st.scratch.tarjan_reach[x]?.getD 0#32).toNat ∧
      BinReach (cnfOfClauses F_cur) x w
  dsp_le : dsp ≤ st.core.tmp_cnt
  dv_on_scc : ∀ i < dsp, onScc st (st.scratch.work_stk2[i]?.getD 0#32).toNat
  dv_tmk_mono : ∀ i j, i < j → j < dsp →
    (st.scratch.tarjan_mark[(st.scratch.work_stk2[i]?.getD 0#32).toNat]?.getD 0#32).toNat <
    (st.scratch.tarjan_mark[(st.scratch.work_stk2[j]?.getD 0#32).toNat]?.getD 0#32).toNat
  dv0_root : 0 < dsp →
    (st.scratch.work_stk2[0]?.getD 0#32).toNat = root ∧
    (st.scratch.work_stk1[0]?.getD 0#32).toNat = root ∧
    (st.scratch.tarjan_mark[root]?.getD 0#32).toNat = mroot ∧ activeLit s0 root
  dv_trc_eq : ∀ i < dsp,
    let x := (st.scratch.work_stk2[i]?.getD 0#32).toNat
    (st.scratch.tarjan_reach[x]?.getD 0#32).toNat = (st.scratch.tarjan_mark[x]?.getD 0#32).toNat
  dpos_slice : ∀ i < dsp,
    let lit := (st.scratch.work_stk2[i]?.getD 0#32).toNat
    let nl := lit ^^^ 1
    let off := fullWatchOffCore s0.core nl
    let sz := fullWatchSizeCore s0.core nl
    let pos := (st.scratch.wsort[i]?.getD 0#32).toNat
    pos ≤ sz ∧ WatchSliceOk F_cur s0.core nl (off + pos) (sz - pos) ∧
    ∃ scanned, sliceBinsFrom s0.core.wstk off sz =
        scanned ++ sliceBinsFrom s0.core.wstk (off + pos) (sz - pos) ∧
      ∀ ot ∈ scanned, activeLit s0 ot → 1 ≤ (st.scratch.tarjan_mark[ot]?.getD 0#32).toNat
  pop_trc_lt : ∀ u, onScc st u → ¬ onDv st dsp u →
    (st.scratch.tarjan_reach[u]?.getD 0#32).toNat < (st.scratch.tarjan_mark[u]?.getD 0#32).toNat
  pop_edges_vis : ∀ u v, onScc st u → ¬ onDv st dsp u → activeEdge s0 u v →
    1 ≤ (st.scratch.tarjan_mark[v]?.getD 0#32).toNat
  pop_trc_fwd : ∀ u v, onScc st u → ¬ onDv st dsp u → activeEdge s0 u v → onScc st v →
    (st.scratch.tarjan_mark[u]?.getD 0#32).toNat < (st.scratch.tarjan_mark[v]?.getD 0#32).toNat →
    (st.scratch.tarjan_reach[u]?.getD 0#32).toNat ≤ (st.scratch.tarjan_reach[v]?.getD 0#32).toNat
  pop_dv_order : ∀ u i, onScc st u → ¬ onDv st dsp u → i < dsp →
    activeEdge s0 u (st.scratch.work_stk2[i]?.getD 0#32).toNat →
    (st.scratch.tarjan_mark[(st.scratch.work_stk2[i]?.getD 0#32).toNat]?.getD 0#32).toNat <
    (st.scratch.tarjan_mark[u]?.getD 0#32).toNat
  scc_parent_ge : ∀ j < st.core.tmp_cnt, ∀ d < dsp,
    (st.scratch.tarjan_mark[(st.scratch.work_stk2[d]?.getD 0#32).toNat]?.getD 0#32).toNat <
    (st.scratch.tarjan_mark[(st.scratch.work_stk1[j]?.getD 0#32).toNat]?.getD 0#32).toNat →
    ∃ i < j,
      (st.scratch.tarjan_mark[(st.scratch.work_stk2[d]?.getD 0#32).toNat]?.getD 0#32).toNat ≤
        (st.scratch.tarjan_mark[(st.scratch.work_stk1[i]?.getD 0#32).toNat]?.getD 0#32).toNat ∧
      activeEdge s0 (st.scratch.work_stk1[i]?.getD 0#32).toNat
        (st.scratch.work_stk1[j]?.getD 0#32).toNat
  mroot_reach : 0 < dsp →
    ∀ l < 2 * s0.core.cur_vars,
      mroot ≤ (st.scratch.tarjan_mark[l]?.getD 0#32).toNat → BinReach (cnfOfClauses F_cur) root l

namespace TarjanDfsInv

variable {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
  {s0 st : FullState} {root mroot reached dsp : Nat}

theorem toBase (h : TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st) :
    TarjanLoopBase c F_cur s0 st :=
  ⟨h.agrees, h.len_ok, h.rsz_le, h.partial_repr, h.units_ok, fun hc => absurd h.inc0 hc⟩

theorem onScc_lt (h : TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st)
    {u : Nat} (hu : onScc st u) : u < 2 * s0.core.cur_vars :=
  let ⟨j, hj, hje⟩ := hu; hje ▸ h.scc_lt j hj

theorem dv_lt (h : TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st)
    {i : Nat} (hi : i < dsp) : (st.scratch.work_stk2[i]?.getD 0#32).toNat < 2 * s0.core.cur_vars :=
  h.onScc_lt (h.dv_on_scc i hi)

theorem reached_lt_of_unvisited (h : TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st)
    {l : Nat} (hl : l < 2 * s0.core.cur_vars)
    (h0 : (st.scratch.tarjan_mark[l]?.getD 0#32).toNat = 0) : reached < 2 * s0.core.cur_vars := by
  let f : Nat → Nat := fun k =>
    if hk : k < reached then (h.tmk_surj (k + 1) (by omega) (by omega)).choose else 0
  have hf : ∀ k (hk : k < reached),
      f k < 2 * s0.core.cur_vars ∧ (st.scratch.tarjan_mark[f k]?.getD 0#32).toNat = k + 1 :=
    fun k hk => by
      simp only [f, hk, ↓reduceDIte]
      exact (h.tmk_surj (k + 1) (by omega) (by omega)).choose_spec
  refine inj_lt_of_missing (v := l) f (fun i j hi hj heq => ?_) (fun i hi => (hf i hi).1) hl
    (fun i hi heq => ?_)
  · have h1 := (hf i hi).2; have h2 := (hf j hj).2; rw [heq] at h1; omega
  · have h1 := (hf i hi).2; rw [heq, h0] at h1; omega

def measure (c : FullCfg) (s0 st : FullState) (reached dsp : Nat) : Nat :=
  (2 * s0.core.cur_vars - reached) * (c.wcap + 2) + dvWorkSum s0 st dsp

theorem measure_pos (hdsp : 0 < dsp) : 0 < measure c s0 st reached dsp := by
  cases dsp with
  | zero => omega
  | succ k => unfold measure dvWorkSum; dsimp only; omega

theorem reset_empty (h : TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st)
    (htc0 : st.core.tmp_cnt = 0) : TarjanDfsInv c F0 F_cur s0 0 1 reached 0 st :=
  { h with
    top_le := by omega, scc_lt := by omega, scc_tmk_ge := by omega, scc_tmk_mono := by omega
    trc_range := by omega, trc_witness := by omega, dsp_le := by omega, dv_on_scc := by omega
    dv_tmk_mono := by omega, dv0_root := by omega, dv_trc_eq := by omega, dpos_slice := by omega
    pop_trc_lt := fun _ ⟨_, h, _⟩ => by omega, pop_edges_vis := fun _ _ ⟨_, h, _⟩ => by omega
    pop_trc_fwd := fun _ _ ⟨_, h, _⟩ => by omega, pop_dv_order := fun _ _ ⟨_, h, _⟩ => by omega
    scc_parent_ge := by omega, mroot_reach := by omega }

/-- When `lit = dv[dsp - 1]` finishes with `rlit = tmk[lit]`, `scc[k0 .. top)` is `LitEquiv`. -/
theorem scc_pop_equiv (h : TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st)
    (hw0 : FullWitnessInv c F0 F_cur s0.core) (hdm : s0.core.dense_mode = 0#64) (hdsp : 0 < dsp)
    (hscan : ∀ v, activeEdge s0 (st.scratch.work_stk2[dsp - 1]?.getD 0#32).toNat v → onScc st v →
      (st.scratch.tarjan_mark[(st.scratch.work_stk2[dsp - 1]?.getD 0#32).toNat]?.getD 0#32).toNat ≤
        (st.scratch.tarjan_reach[v]?.getD 0#32).toNat) :
    ∃ k0 < st.core.tmp_cnt,
      st.scratch.work_stk1[k0]?.getD 0#32 = st.scratch.work_stk2[dsp - 1]?.getD 0#32 ∧
      (∀ j, k0 < j → j < st.core.tmp_cnt →
        st.scratch.work_stk1[j]?.getD 0#32 ≠ st.scratch.work_stk2[dsp - 1]?.getD 0#32) ∧
      (dsp = 1 → k0 = 0) ∧
      (∀ j, k0 ≤ j → j < st.core.tmp_cnt →
        LitEquiv (cnfOfClauses F_cur) (st.scratch.work_stk1[j]?.getD 0#32).toNat
          (st.scratch.work_stk2[dsp - 1]?.getD 0#32).toNat) := by
  let lit := (st.scratch.work_stk2[dsp - 1]?.getD 0#32).toNat
  obtain ⟨k0, hk0_lt, hk0_eq⟩ := h.dv_on_scc (dsp - 1) (by omega)
  have hk0_bv : st.scratch.work_stk1[k0]?.getD 0#32 = st.scratch.work_stk2[dsp - 1]?.getD 0#32 :=
    BitVec.eq_of_toNat_eq hk0_eq
  have hk0_uniq : ∀ j, k0 < j → j < st.core.tmp_cnt →
      st.scratch.work_stk1[j]?.getD 0#32 ≠ st.scratch.work_stk2[dsp - 1]?.getD 0#32 :=
    fun j hj1 hj2 heq => by have := h.scc_tmk_mono k0 j hj1 hj2; rw [heq, hk0_bv] at this; omega
  have hk0_zero : dsp = 1 → k0 = 0 := fun h1 => Classical.byContradiction fun hz => by
    have h0 := h.dv0_root hdsp; have hmt := h.scc_tmk_mono 0 k0 (by omega) hk0_lt
    have hk0_rt : (st.scratch.work_stk1[k0]?.getD 0#32).toNat = root := by
      rw [hk0_eq, h1]; exact h0.1
    rw [h0.2.1, hk0_rt] at hmt; omega
  have hnot_dv : ∀ j, k0 < j → j < st.core.tmp_cnt →
      ¬ onDv st dsp (st.scratch.work_stk1[j]?.getD 0#32).toNat := fun j hj1 hj2 ⟨d, hd, hdeq⟩ => by
    have hlt1 := h.scc_tmk_mono k0 j hj1 hj2; rw [hk0_eq, ← hdeq] at hlt1
    by_cases hde : d = dsp - 1
    · subst hde; omega
    · have := h.dv_tmk_mono d (dsp - 1) (by omega) (by omega); omega
  have hge_of_tmk : ∀ i < st.core.tmp_cnt,
      (st.scratch.tarjan_mark[lit]?.getD 0#32).toNat ≤
        (st.scratch.tarjan_mark[(st.scratch.work_stk1[i]?.getD 0#32).toNat]?.getD 0#32).toNat →
      k0 ≤ i := fun i hi hle => Classical.byContradiction fun hlt => by
    have hmt := h.scc_tmk_mono i k0 (by omega) hk0_lt; rw [hk0_eq] at hmt; dsimp only [lit] at hle
    omega
  have htrc_ge : ∀ j, k0 ≤ j → j < st.core.tmp_cnt →
      (st.scratch.tarjan_mark[lit]?.getD 0#32).toNat ≤
        (st.scratch.tarjan_reach[(st.scratch.work_stk1[j]?.getD 0#32).toNat]?.getD 0#32).toNat := by
    intro j; induction j using Nat.strongRecOn with
    | ind j ih =>
      intro hj1 hj2; rcases Nat.eq_or_lt_of_le hj1 with rfl | hgt
      · rw [hk0_eq]; exact Nat.le_of_eq (h.dv_trc_eq (dsp - 1) (by omega)).symm
      · have hlt := h.scc_tmk_mono k0 j hgt hj2; rw [hk0_eq] at hlt
        obtain ⟨i, hij, hi_tmk, hedge⟩ := h.scc_parent_ge j hj2 (dsp - 1) (by omega) hlt
        have hi_ge := hge_of_tmk i (by omega) hi_tmk
        rcases Nat.eq_or_lt_of_le hi_ge with rfl | higt
        · rw [hk0_eq] at hedge; exact hscan _ hedge ⟨j, hj2, rfl⟩
        · exact Nat.le_trans (ih i hij hi_ge (by omega))
            (h.pop_trc_fwd _ _ ⟨i, by omega, rfl⟩ (hnot_dv i higt (by omega)) hedge
              ⟨j, hj2, rfl⟩ (h.scc_tmk_mono i j hij hj2))
  have hdown : ∀ j, k0 ≤ j → j < st.core.tmp_cnt →
      BinReach (cnfOfClauses F_cur) lit (st.scratch.work_stk1[j]?.getD 0#32).toNat := by
    intro j; induction j using Nat.strongRecOn with
    | ind j ih =>
      intro hj1 hj2; rcases Nat.eq_or_lt_of_le hj1 with rfl | hgt
      · dsimp only [lit]; rw [hk0_eq]; exact BinReach.refl _
      · have hlt := h.scc_tmk_mono k0 j hgt hj2; rw [hk0_eq] at hlt
        obtain ⟨i, hij, hi_tmk, hedge⟩ := h.scc_parent_ge j hj2 (dsp - 1) (by omega) hlt
        exact binReach_trans (ih i hij (hge_of_tmk i (by omega) hi_tmk) (by omega))
          (BinReach.step (activeEdge_binEdge hw0 hdm hedge) (BinReach.refl _))
  have hup : ∀ j, k0 ≤ j → j < st.core.tmp_cnt →
      BinReach (cnfOfClauses F_cur) (st.scratch.work_stk1[j]?.getD 0#32).toNat lit := by
    intro j; induction j using Nat.strongRecOn with
    | ind j ih =>
      intro hj1 hj2; rcases Nat.eq_or_lt_of_le hj1 with rfl | hgt
      · dsimp only [lit]; rw [hk0_eq]; exact BinReach.refl _
      · have hlt_trc := h.pop_trc_lt _ ⟨j, hj2, rfl⟩ (hnot_dv j hgt hj2)
        have hge_trc := htrc_ge j hj1 hj2
        obtain ⟨_, _, ⟨i, hi_lt, rfl⟩, htmk_w, hreach_w⟩ := h.trc_witness j hj2
        have hij : i < j := Classical.byContradiction fun hle => by
          rcases Nat.eq_or_lt_of_le (Nat.le_of_not_gt hle) with rfl | hji
          · omega
          · have := h.scc_tmk_mono j i hji hi_lt; omega
        exact binReach_trans hreach_w (ih i hij (hge_of_tmk i hi_lt (by omega)) hi_lt)
  refine ⟨k0, hk0_lt, hk0_bv, hk0_uniq, hk0_zero, fun j hj1 hj2 =>
    ⟨binReach_sound (hup j hj1 hj2), ?_⟩⟩
  have hd := binReach_sound (hdown j hj1 hj2)
  rw [CNF.entails_clause_def] at hd ⊢; intro α hα
  have h1 := (clauseEvalVal_iff α _).mpr (hd α hα); rw [← clauseEvalVal_iff]
  simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false] at h1 ⊢
  simpa [Bool.or_comm] using h1

end TarjanDfsInv

section TarjanInitAdv

attribute [local grind =] List.getElem?_set_self List.getElem?_set_ne Option.getD_some

theorem dvWorkSum_split {s0 st : FullState} {dsp : Nat} (hdsp : 0 < dsp) :
    dvWorkSum s0 st dsp = dvWorkSum s0 st (dsp - 1) +
      (fullWatchSizeCore s0.core ((st.scratch.work_stk2[dsp - 1]?.getD 0#32).toNat ^^^ 1) -
        (st.scratch.wsort[dsp - 1]?.getD 0#32).toNat + 1) := by
  cases dsp with | zero => omega | succ _ => rfl

theorem tarjan_init_root {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {root mroot reached : Nat}
    (hw0 : FullWitnessInv c F0 F_cur s0.core) (hdm : s0.core.dense_mode = 0#64)
    (h : TarjanDfsInv c F0 F_cur s0 0 mroot reached 0 st) (htop0 : st.core.tmp_cnt = 0)
    (hact : activeLit s0 root) (h0 : (st.scratch.tarjan_mark[root]?.getD 0#32).toNat = 0) :
    let reached' := reached + 1
    let r32 := BitVec.ofNat 32 reached'; let rt32 := BitVec.ofNat 32 root
    let st' : FullState :=
      { st with
        core := { st.core with tmp_cnt := 1 }
        scratch :=
          { st.scratch with
            work_stk2 := st.scratch.work_stk2.set 0 rt32, wsort := st.scratch.wsort.set 0 0#32
            tarjan_mark := st.scratch.tarjan_mark.set root r32
            tarjan_reach := st.scratch.tarjan_reach.set root r32
            work_stk1 := st.scratch.work_stk1.set 0 rt32 } }
    reached' ≤ 2 * s0.core.cur_vars ∧ TarjanDfsInv c F0 F_cur s0 root reached' reached' 1 st' := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcl := h.len_ok.core_ok; have hsl := h.len_ok.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hcv_eq := h.agrees.get (·.core.cur_vars)
  have hreach_lt := h.reached_lt_of_unvisited hact.1 h0
  have hwat : WatchesInv F_cur s0.core := by
    have hm := hw0.watches; unfold ModeWatchesInv at hm; rwa [ite_eq_left hdm] at hm
  have hr32 : (BitVec.ofNat 32 (reached + 1)).toNat = reached + 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hrt32 : (BitVec.ofNat 32 root).toNat = root := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hact.1; omega)]
  have hscc_l := hsl.work_stk1_len; have hdv_l := hsl.work_stk2_len; have hdp_l := hsl.wsort_len
  have htmk_l := hsl.tarjan_mark_len; have htrc_l := hsl.tarjan_reach_len
  have hrt_lt : root < 2 * c.max_vars := by have := hact.1; omega
  have h0_lt : 0 < 2 * c.max_vars := by omega
  intro reached' r32 rt32 st'
  have hscc_onDv : ∀ u, onScc st' u → onDv st' 1 u := by
    rintro u ⟨j, hj, hjeq⟩; dsimp only [st'] at hj hjeq; obtain rfl : j = 0 := by omega
    exact ⟨0, by omega, by dsimp only [st']; grind⟩
  refine ⟨by omega, {
      agrees := h.agrees.update _, inc0 := h.inc0, rsz_le := h.rsz_le, reached_le := by omega
      partial_repr := h.partial_repr, units_ok := h.units_ok
      len_ok := ⟨{ hcl with vals_len := hcl.vals_len },
        { hsl with work_stk1_len := by simp [st', hscc_l], work_stk2_len := by simp [st', hdv_l],
                   wsort_len := by simp [st', hdp_l], tarjan_mark_len := by simp [st', htmk_l],
                   tarjan_reach_len := by simp [st', htrc_l] }⟩
      tmk_le := fun l hl => by
        dsimp only [st']; by_cases hlr : l = root; · subst hlr; grind
        · have := h.tmk_le l hl; grind
      tmk_inj := fun a b ha hb hpos heq => by
        dsimp only [st'] at hpos heq; by_cases har : a = root <;> by_cases hbr : b = root
        · omega
        · subst har; have := h.tmk_le b hb; grind
        · subst hbr; have := h.tmk_le a ha; grind
        · rw [List.getElem?_set_ne (Ne.symm har)] at hpos heq
          rw [List.getElem?_set_ne (Ne.symm hbr)] at heq; exact h.tmk_inj a b ha hb hpos heq
      tmk_surj := fun t ht1 ht2 => by
        dsimp only [st']; by_cases htr : t = reached + 1
        · subst htr; exact ⟨root, hact.1, by grind⟩
        · obtain ⟨l, hl, hlt⟩ := h.tmk_surj t ht1 (by omega)
          exact ⟨l, hl, by rw [List.getElem?_set_ne (fun he => by subst he; omega)]; exact hlt⟩
      tmk_active := fun l hl hpos => by
        dsimp only [st'] at hpos; by_cases hlr : l = root; · subst hlr; exact hact
        · rw [List.getElem?_set_ne (Ne.symm hlr)] at hpos; exact h.tmk_active l hl hpos
      top_le := by dsimp only [st']; omega
      scc_lt := fun i hi => by
        dsimp only [st'] at hi ⊢; obtain rfl : i = 0 := by omega
        have := hact.1; grind
      scc_tmk_ge := fun i hi => by
        dsimp only [st'] at hi ⊢; obtain rfl : i = 0 := by omega
        grind
      scc_tmk_mono := fun _ _ _ h => by dsimp only [st'] at h; omega
      scc_iff_trc := fun l hl => by
        dsimp only [onScc, st']; constructor
        · rintro ⟨j, hj, hjeq⟩; obtain rfl : j = 0 := by omega
          have hlr : root = l := by grind
          subst hlr; refine ⟨by grind, fun heq => ?_⟩
          rw [List.getElem?_set_self (by omega), Option.getD_some] at heq
          have := congrArg BitVec.toNat heq; rw [hr32] at this; revert this; simp; omega
        · rintro ⟨hpos, hne⟩; by_cases hlr : l = root; · subst hlr; exact ⟨0, by omega, by grind⟩
          · rw [List.getElem?_set_ne (Ne.symm hlr)] at hpos hne
            obtain ⟨_, hj, _⟩ := (h.scc_iff_trc l hl).mpr ⟨hpos, hne⟩; omega
      trc_range := fun i hi => by
        dsimp only [st'] at hi ⊢; obtain rfl : i = 0 := by omega
        grind
      trc_witness := fun i hi => by
        dsimp only [st'] at hi ⊢; obtain rfl : i = 0 := by omega
        refine ⟨root, hact.1, ⟨0, by dsimp only [st']; omega, by dsimp only [st']; grind⟩,
          by grind, ?_⟩
        rw [List.getElem?_set_self (by omega), Option.getD_some, hrt32]; exact BinReach.refl _
      dsp_le := by dsimp only [st']; omega
      dv_on_scc := fun i hi => by
        obtain rfl : i = 0 := by omega
        exact ⟨0, by dsimp only [st']; omega, by dsimp only [st']; grind⟩
      dv_tmk_mono := by omega
      dv0_root := fun _ =>
        ⟨by dsimp only [st']; grind, by dsimp only [st']; grind, by dsimp only [st']; grind, hact⟩
      dv_trc_eq := fun i hi => by
        obtain rfl : i = 0 := by omega
        dsimp only [st']; grind
      dpos_slice := fun i hi => by
        obtain rfl : i = 0 := by omega
        dsimp only [st']
        rw [List.getElem?_set_self (by omega), List.getElem?_set_self (by omega),
          Option.getD_some, Option.getD_some, hrt32]
        simp only [show (0#32 : BitVec 32).toNat = 0 from rfl, Nat.add_zero, Nat.sub_zero]
        exact ⟨Nat.zero_le _, hwat.slices _ (litNeg_lt_two_mul hact.1), [], by simp,
          fun _ hm => nomatch hm⟩
      pop_trc_lt := fun u hu hndv => absurd (hscc_onDv u hu) hndv
      pop_edges_vis := fun u _ hu hndv => absurd (hscc_onDv u hu) hndv
      pop_trc_fwd := fun u _ hu hndv => absurd (hscc_onDv u hu) hndv
      pop_dv_order := fun u _ hu hndv => absurd (hscc_onDv u hu) hndv
      scc_parent_ge := fun j hj d hd hlt => by
        dsimp only [st'] at hj hlt; obtain rfl : j = 0 := by omega
        obtain rfl : d = 0 := by omega
        grind
      mroot_reach := fun _ l hl hge => by
        dsimp only [st'] at hge; by_cases hlr : l = root; · subst hlr; exact BinReach.refl _
        · have := h.tmk_le l hl; grind }⟩

theorem tarjan_advance_dpos {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} {root mroot reached dsp : Nat}
    (h : TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st)
    (hdsp : 0 < dsp) {pos' : BitVec 32}
    (hpos_gt : (st.scratch.wsort[dsp - 1]?.getD 0#32).toNat < pos'.toNat)
    (hslice' : let lit := (st.scratch.work_stk2[dsp - 1]?.getD 0#32).toNat; let nl := lit ^^^ 1
      let off := fullWatchOffCore s0.core nl; let sz := fullWatchSizeCore s0.core nl
      pos'.toNat ≤ sz ∧ WatchSliceOk F_cur s0.core nl (off + pos'.toNat) (sz - pos'.toNat) ∧
      ∃ scanned, sliceBinsFrom s0.core.wstk off sz =
          scanned ++ sliceBinsFrom s0.core.wstk (off + pos'.toNat) (sz - pos'.toNat) ∧
        ∀ ot ∈ scanned, activeLit s0 ot → 1 ≤ (st.scratch.tarjan_mark[ot]?.getD 0#32).toNat) :
    let st' : FullState :=
      { st with scratch := { st.scratch with wsort := st.scratch.wsort.set (dsp - 1) pos' } }
    TarjanDfsInv c F0 F_cur s0 root mroot reached dsp st' ∧
    TarjanDfsInv.measure c s0 st' reached dsp < TarjanDfsInv.measure c s0 st reached dsp := by
  intro st'; have hdp_l := h.len_ok.scratch_ok.wsort_len
  have hcv_le := h.len_ok.core_ok.cur_vars_le; have hcv_eq := h.agrees.get (·.core.cur_vars)
  have hdsp_lt : dsp - 1 < st.scratch.wsort.length := by
    have := h.dsp_le; have := h.top_le; have := h.reached_le; omega
  refine ⟨{ h with
      agrees := h.agrees.update _
      len_ok := ⟨h.len_ok.core_ok, { h.len_ok.scratch_ok with wsort_len := by simp [st', hdp_l] }⟩
      dpos_slice := fun i hi => by
        dsimp only [st']; by_cases hid : i = dsp - 1
        · subst hid; rw [List.getElem?_set_self hdsp_lt, Option.getD_some]; exact hslice'
        · rw [List.getElem?_set_ne (Ne.symm hid)]; exact h.dpos_slice i hi }, ?_⟩
  have hcongr : dvWorkSum s0 st' (dsp - 1) = dvWorkSum s0 st (dsp - 1) :=
    dvWorkSum_congr (dsp - 1) fun i hi => ⟨rfl, List.getElem?_set_ne (by omega)⟩
  have hsz_ge := hslice'.1; unfold TarjanDfsInv.measure
  rw [dvWorkSum_split (st := st') hdsp, dvWorkSum_split (st := st) hdsp, hcongr]
  dsimp only [st']; rw [List.getElem?_set_self hdsp_lt, Option.getD_some]; omega

end TarjanInitAdv

end FullSccHelpers

end LeanQbe.T.Examples.Kissat.Full
