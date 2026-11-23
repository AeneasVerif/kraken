module

public import LeanQbe.T.Examples.Kissat.PlainReduceLemmas1

/-!
# Kissat `D-Plain` Compaction GC & Reduction Helpers — Part 2

Provides scoped branch/base-wrapper tactics (`PlainReduceTactics`), trail-value,
arena-prefix, reason-relocation, clause-rewatch, and literal-rank call lemmas
shared by `plain_sweep` and `plain_reduce`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Plain

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.C0Step
open Kraken.Bedrock2.Test

/-! ## 1. Scoped branch tactics & base `c0_load` / `c0_store` wrappers -/

namespace PlainReduceTactics

section
open Lean Meta Elab Tactic

private meta def mkPrBranchSimp : TacticM (Simp.Context × Simp.Methods) := do
  let stx ← `(tactic| simp only [
    LeanQbe.T.op1_eq_mk, LeanQbe.T.op2_eq_mk, LeanQbe.T.op3_eq_mk,
    LeanQbe.T.wp_let_copy_eq, LeanQbe.T.wp_let_add_eq, LeanQbe.T.wp_let_sub_eq,
    LeanQbe.T.wp_let_mul_eq, LeanQbe.T.wp_let_and_eq, LeanQbe.T.wp_let_or_eq,
    LeanQbe.T.wp_let_xor_eq, LeanQbe.T.wp_let_not_eq, LeanQbe.T.wp_let_shl_eq,
    LeanQbe.T.wp_let_lshr_eq, LeanQbe.T.wp_let_ashr_eq, LeanQbe.T.wp_let_cmp_eq,
    LeanQbe.T.wp_let_select_eq, LeanQbe.T.wp_let_zext_eq, LeanQbe.T.wp_let_sext_eq,
    LeanQbe.T.wp_let_trunc_eq, LeanQbe.T.wp_let_ofBool_eq, LeanQbe.T.vals_nil,
    LeanQbe.T.vals_cons, LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm,
    LeanQbe.T.Blocks.get_here, LeanQbe.T.Blocks.get_there, LeanQbe.T.Ty.hasFloat_vec,
    LeanQbe.T.Ty.hasFloat, LeanQbe.T.Ty.isFloatTree, ite_self, ite_true, ite_false,
    Bool.false_eq_true, Bool.true_eq_false, LeanQbe.T.OpCode.eq, LeanQbe.T.OpCode.ne,
    LeanQbe.T.OpCode.ult, LeanQbe.T.OpCode.ule, LeanQbe.T.OpCode.ugt, LeanQbe.T.OpCode.uge,
    LeanQbe.T.OpCode.slt, LeanQbe.T.OpCode.sle, LeanQbe.T.OpCode.sgt, LeanQbe.T.OpCode.sge,
    LeanQbe.T.evalBits_eq_beq, LeanQbe.T.evalBits_ne_bne, LeanQbe.T.evalBits_ult_eq,
    LeanQbe.T.evalBits_ule_eq, LeanQbe.T.evalBits_ugt_eq, LeanQbe.T.evalBits_uge_eq,
    LeanQbe.T.evalBits_slt_eq, LeanQbe.T.evalBits_sle_eq, LeanQbe.T.evalBits_sgt_eq,
    LeanQbe.T.evalBits_sge_eq, LeanQbe.T.evalBool_eq_beq, LeanQbe.T.evalBool_ne_bne,
    LeanQbe.T.lift1, LeanQbe.T.lift2, LeanQbe.T.liftCmp, LeanQbe.T.shl_three, cast_eq,
    BitVec.add_zero, BitVec.zero_add, Nat.reduceLeDiff, true_and, and_true])
  let { ctx, simprocs, .. } ← mkSimpContext stx (eraseLocal := false)
  let m0 := Simp.mkDefaultMethodsCore simprocs
  let methods : Simp.Methods := { m0 with
    pre := fun sub => do
      if sub.isAppOf ``LeanQbe.T.Expr.group || sub.isAppOf ``LeanQbe.T.Expr.load ||
         sub.isAppOf ``LeanQbe.T.Expr.store || sub.isAppOf ``LeanQbe.T.Expr.jnz ||
         sub.isAppOf ``LeanQbe.T.Expr.call then
        return .done { expr := sub }
      m0.pre sub }
  return (ctx, methods)

private meta def prBranchStepWith (ctx : Simp.Context) (methods : Simp.Methods) :
    TacticM Unit := do
  try
    withMainContext do
      let g ← getMainGoal
      let r := (← Simp.main (← instantiateMVars (← g.getType)) ctx (methods := methods)).1
      replaceMainGoal [← g.replaceTargetEq r.expr (← r.getProof)]
  catch _ => pure ()

/-- Step a single `Expr.jnz`, normalizing branch hypotheses with `bv_c0`. -/
scoped elab "pr_jnz" : tactic => do
  let (ctx, methods) ← mkPrBranchSimp
  evalTactic (← `(tactic| c0_unmdata))
  prBranchStepWith ctx methods
  let hc := mkIdent `hc
  evalTactic (← `(tactic| refine LeanQbe.T.wp_jnz_of (fun $hc:ident => ?_) (fun $hc:ident => ?_)))
  let mut out : Array MVarId := #[]
  for g in ← getUnsolvedGoals do
    if ← g.isAssigned then continue
    setGoals [g]
    evalTactic (← `(tactic| try simp only [
      LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm, LeanQbe.T.evalBits_eq_beq,
      LeanQbe.T.evalBits_ne_bne, LeanQbe.T.evalBits_ult_eq, LeanQbe.T.evalBits_ule_eq,
      LeanQbe.T.evalBits_ugt_eq, LeanQbe.T.evalBits_uge_eq, LeanQbe.T.evalBits_slt_eq,
      LeanQbe.T.evalBits_sle_eq, LeanQbe.T.evalBits_sgt_eq, LeanQbe.T.evalBits_sge_eq,
      LeanQbe.T.evalBool_eq_beq, LeanQbe.T.evalBool_ne_bne,
      LeanQbe.T.lift1, LeanQbe.T.lift2, LeanQbe.T.liftCmp, cast_eq,
      Nat.reduceMod, BitVec.reduceToNat, Nat.reducePow] at $hc:ident))
    evalTactic (← `(tactic| c0_cond $hc))
    prBranchStepWith ctx methods
    out := out ++ (← getUnsolvedGoals)
  setGoals out.toList

/-- Simplify pure `let_` bindings and `Blocks.get` in a `wp` goal without crossing `group`/`jnz`. -/
scoped elab "pr_let" : tactic => do
  let (ctx, methods) ← mkPrBranchSimp
  evalTactic (← `(tactic| c0_unmdata))
  prBranchStepWith ctx methods
end

section BaseWrappers
@[scoped c0_load] theorem load_vals_base {c : PlainCfg} {s : PlainState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 0 < s.vals.length) (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i8 c.pVals = some s.vals[0] := by simpa using load_arena_vals (i := 0) hi hm
@[scoped c0_load] theorem load_lvl_base {c : PlainCfg} {s : PlainState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 0 < s.lvl.length) (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 c.pLevel = some s.lvl[0] := by simpa using load_arena_lvl (i := 0) hi hm
@[scoped c0_load] theorem load_rsns_base {c : PlainCfg} {s : PlainState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 0 < s.rsns.length) (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 c.pReason = some s.rsns[0] := by simpa using load_arena_rsns (i := 0) hi hm
@[scoped c0_store] theorem store_rsns_base {c : PlainCfg} {s : PlainState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.rsns.length)
    (hm : (PlainMem c s ⋆ R) m) : storeOk m i32 c.pReason ∧
      (PlainMem c { s with rsns := s.rsns.set 0 v } ⋆ R) (storeMem m i32 c.pReason v) := by
  simpa using store_arena_rsns (i := 0) v hi hm
@[scoped c0_load] theorem load_wvec_base {c : PlainCfg} {s : PlainState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 0 < s.wvec.length) (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 c.pWvec = some s.wvec[0] := by simpa using load_arena_wvec (i := 0) hi hm
@[scoped c0_store] theorem store_wvec_base {c : PlainCfg} {s : PlainState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.wvec.length)
    (hm : (PlainMem c s ⋆ R) m) : storeOk m i32 c.pWvec ∧
      (PlainMem c { s with wvec := s.wvec.set 0 v } ⋆ R) (storeMem m i32 c.pWvec v) := by
  simpa using store_arena_wvec (i := 0) v hi hm
@[scoped c0_load] theorem load_arena_base {c : PlainCfg} {s : PlainState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 0 < s.arena.length) (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 c.pArena = some s.arena[0] := by simpa using load_arena_arena (i := 0) hi hm
@[scoped c0_store] theorem store_arena_base {c : PlainCfg} {s : PlainState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.arena.length)
    (hm : (PlainMem c s ⋆ R) m) : storeOk m i32 c.pArena ∧
      (PlainMem c { s with arena := s.arena.set 0 v } ⋆ R) (storeMem m i32 c.pArena v) := by
  simpa using store_arena_arena (i := 0) v hi hm
@[scoped c0_load] theorem load_wstk_base {c : PlainCfg} {s : PlainState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 0 < s.wstk.length) (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 c.pWstk = some s.wstk[0] := by simpa using load_arena_wstk (i := 0) hi hm
@[scoped c0_store] theorem store_wstk_base {c : PlainCfg} {s : PlainState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.wstk.length)
    (hm : (PlainMem c s ⋆ R) m) : storeOk m i32 c.pWstk ∧
      (PlainMem c { s with wstk := s.wstk.set 0 v } ⋆ R) (storeMem m i32 c.pWstk v) := by
  simpa using store_arena_wstk (i := 0) v hi hm
end BaseWrappers

end PlainReduceTactics

section
open scoped PlainReduceTactics

namespace PlainReduceHelpers

/-! ## 2. Sweep Phase 2: `TrailValsInv`, `ArenaPrefixOk`, `RsnRelocInv`, at-root lemmas -/

/-- Trail and value invariants decoupled from `ArenaClausesInv` / `WatchesInv` / `reason_inv`. -/
structure TrailValsInv (c : PlainCfg) (F0 : CNF Nat) (s : PlainState) : Prop where
  cur_level_le : s.cur_level ≤ s.trail_end
  trail_lits_lt : ∀ i < s.trail_end, (s.trl[i]?.getD 0#32).toNat < 2 * c.mv
  trail_vars_nodup : ∀ i j, i < s.trail_end → j < s.trail_end →
    (s.trl[i]?.getD 0#32).toNat / 2 = (s.trl[j]?.getD 0#32).toNat / 2 → i = j
  vals_domain : ∀ l < 2 * c.mv,
    s.vals[l]?.getD 0#8 = 0#8 ∨ s.vals[l]?.getD 0#8 = 1#8 ∨ s.vals[l]?.getD 0#8 = 0xFF#8
  vals_true_iff : ∀ l < 2 * c.mv,
    s.vals[l]?.getD 0#8 = 1#8 ↔ ∃ i < s.trail_end, (s.trl[i]?.getD 0#32).toNat = l
  vals_false_iff : ∀ l < 2 * c.mv,
    s.vals[l]?.getD 0#8 = 0xFF#8 ↔ ∃ i < s.trail_end, (s.trl[i]?.getD 0#32).toNat = l ^^^ 1
  lvl_le : ∀ i < s.trail_end,
    (s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ s.cur_level
  trail_mono : ∀ i j, i ≤ j → j < s.trail_end →
    (s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
      (s.lvl[(s.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
  levels_inhabited : ∀ L, 1 ≤ L → L ≤ s.cur_level →
    ∃ i < s.trail_end, (s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = L
  level0_sound : ∀ i < s.trail_end,
    (s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 →
    F0.EntailsClause (cnfClause [(s.trl[i]?.getD 0#32).toNat])
  trail_pos_inv : ∀ i < s.trail_end,
    (s.trail_pos[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = i
  level0_rsn_none : ∀ idx < s.trail_end,
    (s.lvl[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 →
    s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32

theorem trailValsInv_of_core {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (h : PlainCoreInv c F0 s) : TrailValsInv c F0 s :=
  ⟨h.cur_level_le, h.trail_lits_lt, h.trail_vars_nodup, h.vals_domain, h.vals_true_iff,
    h.vals_false_iff, h.lvl_le, h.trail_mono, h.levels_inhabited, h.level0_sound,
    h.trail_pos_inv, h.level0_rsn_none⟩

theorem trailValsInv_te_lt {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (htv : TrailValsInv c F0 s) {l : Nat} (hl : l < 2 * c.mv)
    (hun : s.vals[l]?.getD 0#8 = 0#8) : s.trail_end < c.mv := by
  have hmiss : ∀ i < s.trail_end, (s.trl[i]?.getD 0#32).toNat / 2 ≠ l / 2 := fun i hi hv => by
    rcases (litVar_eq_iff _ l).mp hv with h1 | h2
    · have := (htv.vals_true_iff l hl).mpr ⟨i, hi, h1⟩; rw [hun] at this; cases this
    · have := (htv.vals_false_iff l hl).mpr ⟨i, hi, h2⟩; rw [hun] at this; cases this
  exact inj_lt_of_missing (fun i => (s.trl[i]?.getD 0#32).toNat / 2)
    htv.trail_vars_nodup (fun i hi => by have := htv.trail_lits_lt i hi; omega)
    (by omega : l / 2 < c.mv) hmiss

theorem trailValsInv_with_l0_assign {c : PlainCfg} {F0 : CNF Nat} {s0 s : PlainState}
    (hinv0 : PlainCoreInv c F0 s0) (hlen : s.LengthsOk c) (htv : TrailValsInv c F0 s)
    (hb : BinWatchesOnly c F0 s (2 * c.mv)) (hcl0 : s.cur_level = 0)
    {lit : BitVec 32} {phases' : List (BitVec 8)} {unfl' : BitVec 64}
    (hlit : lit.toNat < 2 * c.mv) (hun : s.vals[lit.toNat]?.getD 0#8 = 0#8)
    (hph : phases'.length = c.mv) (hl0 : F0.EntailsClause (cnfClause [lit.toNat])) :
    let v := lit.toNat / 2
    TrailValsInv c F0
      { s with
        vals := (s.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
        lvl := s.lvl.set v (BitVec.ofNat 32 s.cur_level)
        rsns := s.rsns.set v 0xFFFFFFFF#32
        trl := s.trl.set s.trail_end lit
        trail_pos := s.trail_pos.set v (BitVec.ofNat 32 s.trail_end)
        trail_end := s.trail_end + 1
        unflushed := unfl'
        heur := { s.heur with phases := phases' } } := by
  let sd : PlainState := { s with arena := s0.arena, arena_len := s0.arena_len }
  have hsd_len : sd.LengthsOk c :=
    { hlen with arena_len_arr := hinv0.lengths.arena_len_arr
                arena_len_le := hinv0.lengths.arena_len_le }
  have hsd_wat : WatchesInv c F0 sd := (binWatchesOnly_with_arena hb s0.arena s0.arena_len).1
  have hsd_rsn : ∀ idx < sd.trail_end,
      let p := (sd.trl[idx]?.getD 0#32).toNat
      let rsn := sd.rsns[p / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 → False := fun idx hi hne => by
    have hle := htv.lvl_le idx hi; rw [hcl0] at hle
    exact absurd (htv.level0_rsn_none idx hi (by omega)) hne
  have hsd_core : PlainCoreInv c F0 sd :=
    ⟨hsd_len, { hinv0.arena with len_ok := hinv0.arena.len_ok }, hsd_wat,
      htv.cur_level_le, htv.trail_lits_lt, htv.trail_vars_nodup, htv.vals_domain,
      htv.vals_true_iff, htv.vals_false_iff, htv.lvl_le, htv.trail_mono, htv.levels_inhabited,
      htv.level0_sound, htv.trail_pos_inv, htv.level0_rsn_none,
      fun idx hi hne => absurd (hsd_rsn idx hi hne) False.elim,
      fun idx hi hne _ => absurd (hsd_rsn idx hi hne) False.elim⟩
  have hpost := assign_preserves_core hsd_core (rsn := 0xFFFFFFFF#32) (unflushed' := unfl')
    hlit hph hun (by dsimp [sd]; omega) (fun L h1 h2 => by dsimp [sd] at h2; omega)
    (fun _ => hl0) (fun h => absurd hcl0 h)
  have htv' := trailValsInv_of_core hpost
  refine ⟨htv'.cur_level_le, htv'.trail_lits_lt, htv'.trail_vars_nodup, htv'.vals_domain,
    htv'.vals_true_iff, htv'.vals_false_iff, ?_, ?_, ?_, ?_, htv'.trail_pos_inv, ?_⟩
  · intro i hi; simpa [sd] using htv'.lvl_le i hi
  · intro i j hij hj; simpa [sd] using htv'.trail_mono i j hij hj
  · intro L h1 h2; simpa [sd, hcl0] using htv'.levels_inhabited L h1 h2
  · intro i hi hl0'; simpa [sd] using htv'.level0_sound i hi hl0'
  · intro idx hidx hli; simpa [sd, hcl0] using htv'.level0_rsn_none idx hidx hli

/-- Arena prefix compaction invariant maintained across `plain_sweep` Phase 2. -/
structure ArenaPrefixOk (c : PlainCfg) (F0 : CNF Nat) (s0 s : PlainState)
    (src dst : Nat) : Prop where
  ar_len : s.arena.length = c.arena_cap
  dst_le_src : dst ≤ src
  src_le_alen : src ≤ s0.arena_len
  src_ref : src = s0.arena_len ∨ src ∈ arenaClauseRefs s0
  suffix_eq : ∀ k, src ≤ k → k < s0.arena_len → s.arena[k]? = s0.arena[k]?
  comp_arena : ArenaClausesInv c F0 { s with arena_len := dst }
  no_garb : ∀ r ∈ arenaClauseRefs { s with arena_len := dst },
    arenaClauseGarb { s with arena_len := dst } r = false

theorem arenaPrefix_init {c : PlainCfg} {F0 : CNF Nat} {s0 : PlainState}
    (hinv : PlainCoreInv c F0 s0) : ArenaPrefixOk c F0 s0 s0 0 0 :=
  ⟨hinv.lengths.arena_len_arr, Nat.zero_le _, Nat.zero_le _,
    (arenaScan_zero hinv.arena.len_ok).imp Eq.symm id, fun _ _ _ => rfl,
    ⟨Or.inl rfl, fun r hr => by simp [arenaClauseRefs, arenaScanRefs] at hr,
      fun r hr => by simp [arenaClauseRefs, arenaScanRefs] at hr,
      fun r hr => by simp [arenaClauseRefs, arenaScanRefs] at hr,
      fun r hr => by simp [arenaClauseRefs, arenaScanRefs] at hr⟩,
    fun r hr => by simp [arenaClauseRefs, arenaScanRefs] at hr⟩

theorem arenaPrefix_skip {c : PlainCfg} {F0 : CNF Nat} {s0 s : PlainState}
    {src dst : Nat} (hinv0 : PlainCoreInv c F0 s0) (hp : ArenaPrefixOk c F0 s0 s src dst)
    (hsrc_lt : src < s0.arena_len) :
    ArenaPrefixOk c F0 s0 s (arenaNextOff s0.arena s0.arena_len src) dst := by
  rcases hp.src_ref with heq | href
  · omega
  · have hwf := hinv0.arena.refs_wf src href
    have hnb := arenaNextOff_bounds (ar := s0.arena) (alen := s0.arena_len) (cref := src) hwf.1
    have hds := hp.dst_le_src
    refine ⟨hp.ar_len, by omega, hnb.2,
      arenaScan_step (fun r hr => (hinv0.arena.refs_wf r hr).2.2.2.2) href,
      fun k hk1 hk2 => hp.suffix_eq k (by omega) hk2, hp.comp_arena, hp.no_garb⟩

private theorem arenaClausesInv_prefix_congr {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    {dst : Nat} {arena' : List (BitVec 32)}
    (hsc : ArenaClausesInv c F0 { s with arena_len := dst })
    (hlen_s : s.arena.length = c.arena_cap) (hlen' : arena'.length = c.arena_cap)
    (hpre : ∀ k < dst, arena'[k]? = s.arena[k]?)
    (hal_le : dst ≤ c.arena_cap) :
    let sc : PlainState := { s with arena_len := dst }
    let sc' : PlainState := { s with arena := arena', arena_len := dst }
    arenaClauseRefs sc' = arenaClauseRefs sc ∧
    (∀ r ∈ arenaClauseRefs sc, arenaClauseGarb sc' r = arenaClauseGarb sc r ∧
      arenaClauseSize sc' r = arenaClauseSize sc r ∧
      arenaClauseLits sc' r = arenaClauseLits sc r) ∧
    ArenaClausesInv c F0 sc' := by
  intro sc sc'
  have hnxt := hsc.arenaNextOff_extend (alen' := dst) (Nat.le_refl dst) hpre
  have hrefs : arenaClauseRefs sc' = arenaClauseRefs sc := arenaClauseRefs_congr rfl hnxt
  have hprops : ∀ r ∈ arenaClauseRefs sc, arenaClauseGarb sc' r = arenaClauseGarb sc r ∧
      arenaClauseSize sc' r = arenaClauseSize sc r ∧
      arenaClauseLits sc' r = arenaClauseLits sc r := fun r hr => by
    have hwf := hsc.refs_wf r hr
    have hwf3 : r + 3 + arenaClauseSize { s with arena_len := dst } r ≤ dst := by
      have h1 := hwf.2.2.1; have h2 := hwf.2.2.2.1; dsimp only at h1 h2; omega
    have hgb : arenaClauseGarb sc' r = arenaClauseGarb sc r := by
      unfold arenaClauseGarb arenaHdr; dsimp only [sc, sc'] at *; rw [hpre r (by omega)]
    have hsz : arenaClauseSize sc' r = arenaClauseSize sc r := by
      unfold arenaClauseSize; dsimp only [sc, sc'] at *; rw [hpre (r + 2) (by omega)]
    have hbd1 : r + 3 + arenaClauseSize sc r ≤ s.arena.length := by
      rw [hlen_s]; dsimp only [sc] at *; omega
    have hbd2 : r + 3 + arenaClauseSize sc r ≤ arena'.length := by
      rw [hlen']; dsimp only [sc] at *; omega
    refine ⟨hgb, hsz, ?_⟩
    unfold arenaClauseLits; rw [hsz]; apply List.ext_getElem
    · simp only [List.length_map, List.length_take, List.length_drop, sc', sc]
      rw [Nat.min_eq_left (by dsimp only [sc] at hbd2; omega),
        Nat.min_eq_left (by dsimp only [sc] at hbd1; omega)]
    · intro k hk1 _
      simp only [List.length_map, List.length_take, List.length_drop, sc'] at hk1
      have hks : k < arenaClauseSize sc r := by
        dsimp only [sc] at hbd2 ⊢
        exact Nat.lt_of_lt_of_le hk1 (Nat.min_le_left _ _)
      simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
      have hk_eq := hpre (r + 3 + k) (by dsimp only [sc] at hks hwf3; omega)
      dsimp only [sc, sc']
      rw [List.getElem?_eq_getElem (by dsimp only [sc] at hks hbd2; omega),
        List.getElem?_eq_getElem (by dsimp only [sc] at hks hbd1; omega)] at hk_eq
      exact congrArg BitVec.toNat (Option.some.inj hk_eq)
  refine ⟨hrefs, hprops, ⟨hsc.len_ok, fun r hr => ?_, fun r hr => ?_, fun r hr hng l hl => ?_,
      fun r hr hng => ?_⟩⟩
  · rw [hrefs] at hr; have hwf := hsc.refs_wf r hr
    dsimp only [sc', sc] at hwf ⊢; rw [hnxt r hr, (hprops r hr).2.1]; exact hwf
  · rw [hrefs] at hr; have hr3 := (hsc.refs_wf r hr).1
    unfold arenaHdr; dsimp only [sc', sc] at hr3 ⊢; rw [hpre r (by omega)]; exact hsc.no_shrk r hr
  · rw [hrefs] at hr; rw [(hprops r hr).1] at hng
    exact hsc.lits_lt r hr hng l ((hprops r hr).2.2.symm ▸ hl)
  · rw [hrefs] at hr; rw [(hprops r hr).1] at hng; rw [(hprops r hr).2.2]
    exact hsc.entails r hr hng

theorem arenaPrefix_skip_mut {c : PlainCfg} {F0 : CNF Nat} {s0 s : PlainState}
    {src dst : Nat} {arena' : List (BitVec 32)} (hinv0 : PlainCoreInv c F0 s0)
    (hp : ArenaPrefixOk c F0 s0 s src dst) (hsrc_lt : src < s0.arena_len)
    (hlen' : arena'.length = c.arena_cap) (hpre : ∀ k < dst, arena'[k]? = s.arena[k]?)
    (hsuf : ∀ k, src + 3 + arenaClauseSize s0 src ≤ k → k < s0.arena_len →
      arena'[k]? = s.arena[k]?) :
    ArenaPrefixOk c F0 s0 { s with arena := arena' }
      (arenaNextOff s0.arena s0.arena_len src) dst := by
  rcases hp.src_ref with heq | href
  · omega
  · have hwf := hinv0.arena.refs_wf src href
    have hnb := arenaNextOff_bounds (ar := s0.arena) (alen := s0.arena_len) (cref := src) hwf.1
    have hds := hp.dst_le_src; have := hinv0.lengths.arena_len_le
    have hc := arenaClausesInv_prefix_congr hp.comp_arena hp.ar_len hlen' hpre (by omega)
    refine ⟨hlen', by omega, hnb.2,
      arenaScan_step (fun r hr => (hinv0.arena.refs_wf r hr).2.2.2.2) href,
      fun k hk1 hk2 => (hsuf k (by have := hwf.2.2.1; omega) hk2).trans
        (hp.suffix_eq k (by omega) hk2),
      hc.2.2, fun r hr => ?_⟩
    rw [hc.1] at hr; rw [(hc.2.1 r hr).1]; exact hp.no_garb r hr

theorem arenaPrefix_suffix_congr {c : PlainCfg} {F0 : CNF Nat} {s0 s : PlainState}
    {src dst : Nat} (hinv0 : PlainCoreInv c F0 s0) (hp : ArenaPrefixOk c F0 s0 s src dst)
    (hsrc_lt : src < s0.arena_len) :
    src ∈ arenaClauseRefs s0 ∧ src + 3 + arenaClauseSize s0 src ≤ s0.arena_len ∧
    s.arena[src]? = s0.arena[src]? ∧ s.arena[src + 2]? = s0.arena[src + 2]? ∧
    arenaNextOff s.arena s0.arena_len src = arenaNextOff s0.arena s0.arena_len src := by
  rcases hp.src_ref with heq | href
  · omega
  · have hwf := hinv0.arena.refs_wf src href
    have hs0 := hp.suffix_eq src (Nat.le_refl _) (by omega)
    have hs2 := hp.suffix_eq (src + 2) (by omega) (by omega)
    exact ⟨href, by omega, hs0, hs2, arenaNextOff_congr_block hs0 hs2 fun k hk1 hk2 =>
      hp.suffix_eq k (by omega) (Nat.lt_of_lt_of_le hk2 hwf.2.2.2.1)⟩

theorem arenaPrefix_append_props {c : PlainCfg} {F0 : CNF Nat} {s0 s : PlainState}
    {src dst new_sz : Nat} {arena' : List (BitVec 32)}
    (hinv0 : PlainCoreInv c F0 s0) (hp : ArenaPrefixOk c F0 s0 s src dst)
    (hsrc_lt : src < s0.arena_len) (hge3 : 3 ≤ new_sz)
    (hle_old : new_sz ≤ arenaClauseSize s0 src) (hlen' : arena'.length = c.arena_cap)
    (hhold_pre : ∀ k < dst, arena'[k]? = s.arena[k]?)
    (hhold_suf : ∀ k, src + 3 + arenaClauseSize s0 src ≤ k → k < s0.arena_len →
      arena'[k]? = s.arena[k]?)
    (hshrk : (arena'[dst]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hng : (arena'[dst]?.getD 0#32 &&& 0x00080000#32) = 0#32)
    (hsz : (arena'[dst + 2]?.getD 0#32).toNat = new_sz)
    (hlits_lt : ∀ k < new_sz, (arena'[dst + 3 + k]?.getD 0#32).toNat < 2 * c.mv)
    (hent : F0.EntailsClause (cnfClause (arenaClauseLits { s with arena := arena' } dst))) :
    let sc : PlainState := { s with arena_len := dst }
    let sc' : PlainState := { s with arena := arena', arena_len := dst + 3 + new_sz }
    let nsrc := arenaNextOff s0.arena s0.arena_len src
    ArenaPrefixOk c F0 s0 { s with arena := arena' } nsrc (dst + 3 + new_sz) ∧
    arenaClauseRefs sc' = arenaClauseRefs sc ++ [dst] ∧
    (∀ r ∈ arenaClauseRefs sc, arenaClauseGarb sc' r = arenaClauseGarb sc r ∧
      arenaClauseLits sc' r = arenaClauseLits sc r) := by
  intro sc sc' nsrc
  rcases hp.src_ref with heq | href
  · omega
  · have hwf0 := hinv0.arena.refs_wf src href
    have hbd0 : src + 3 + arenaClauseSize s0 src ≤ s0.arena_len := by omega
    have hdst_le_nsrc : dst + 3 + new_sz ≤ nsrc := by
      dsimp only [nsrc]; rw [hinv0.arena.arenaNextOff_eq href]; have := hp.dst_le_src; omega
    have hcomp_s := hp.comp_arena; have hal_cap := hinv0.lengths.arena_len_le
    let sd : PlainState := { s with arena := arena', arena_len := dst }
    obtain ⟨hrefs_d, hprops_d, hcomp_d⟩ := arenaClausesInv_prefix_congr
      hcomp_s hp.ar_len hlen' hhold_pre (by have := hp.dst_le_src; omega)
    have hhold_sd : ∀ k < dst, sc'.arena[k]? = sd.arena[k]? := fun _ _ => rfl
    have hrefs_sd : arenaClauseRefs sc' = arenaClauseRefs sd ++ [dst] :=
      arenaClauseRefs_append hcomp_d hge3 rfl hhold_sd hshrk hsz
    have hrefs : arenaClauseRefs sc' = arenaClauseRefs sc ++ [dst] := by rw [hrefs_sd, hrefs_d]
    have hnxt_d := hcomp_d.arenaNextOff_extend (alen' := dst + 3 + new_sz)
      (by dsimp only [sd]; omega) hhold_sd
    have h_garb : ∀ r ∈ arenaClauseRefs sd,
        arenaClauseGarb sc' r = arenaClauseGarb sd r := fun r hr => by
      have hr3 := (hcomp_d.refs_wf r hr).1; unfold arenaClauseGarb arenaHdr; rfl
    have h_sz : ∀ r ∈ arenaClauseRefs sd,
        arenaClauseSize sc' r = arenaClauseSize sd r := fun r hr => by
      have hr3 := (hcomp_d.refs_wf r hr).1; unfold arenaClauseSize; rfl
    have h_lits : ∀ r ∈ arenaClauseRefs sd,
        arenaClauseLits sc' r = arenaClauseLits sd r := fun r hr => by
      have _ := hcomp_d.refs_wf r hr; unfold arenaClauseLits; rw [h_sz r hr]
    have hcomp' : ArenaClausesInv c F0 sc' := by
      refine ⟨Or.inr (by dsimp [sc']; omega), ?_, ?_, ?_, ?_⟩
      · intro r hr; rw [hrefs_sd, List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | hdst
        · have hwf := hcomp_d.refs_wf r hr
          have hwf1 : r + 3 ≤ dst := hwf.1
          have hwf3 : r + 3 + arenaClauseSize sd r ≤ arenaNextOff arena' dst r := hwf.2.2.1
          have hwf4 : arenaNextOff arena' dst r ≤ dst := hwf.2.2.2.1
          have hwf5 := hwf.2.2.2.2
          have hnx_sd := hnxt_d r hr; have hsz_sd := h_sz r hr
          dsimp only [sd] at hnx_sd hsz_sd hwf1 hwf3 hwf4 hwf5
          dsimp only [sc']; rw [hnx_sd, hsz_sd]
          refine ⟨by omega, hwf.2.1, hwf3, by omega, ?_⟩
          rcases hwf5 with he | h3 <;> right <;> omega
        · rw [hdst]
          have hnxt_new : arenaNextOff sc'.arena sc'.arena_len dst = dst + 3 + new_sz := by
            unfold arenaNextOff; dsimp only [sc']
            have h1 : ¬ (dst + 3 > dst + 3 + new_sz) := by omega
            have h2 : ¬ (dst + 3 + (arena'[dst + 2]?.getD 0#32).toNat > dst + 3 + new_sz) := by
              rw [hsz]; omega
            simp only [h1, h2, hshrk, ↓reduceIte, ne_eq, not_true_eq_false]
            exact congrArg (dst + 3 + ·) hsz
          rw [hnxt_new]; dsimp only [arenaClauseSize, sc']; rw [hsz]
          exact ⟨by omega, hge3, by omega, by omega, Or.inl rfl⟩
      · intro r hr; rw [hrefs_sd, List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | hdst
        · exact hcomp_d.no_shrk r hr
        · rw [hdst]; exact hshrk
      · intro r hr hng' l hl; rw [hrefs_sd, List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | hdst
        · rw [h_garb r hr] at hng'
          exact hcomp_d.lits_lt r hr hng' l ((h_lits r hr).symm ▸ hl)
        · rw [hdst] at hl
          have hbd_d : dst + 3 + arenaClauseSize sc' dst ≤ sc'.arena.length := by
            dsimp only [sc', arenaClauseSize]; rw [hlen', hsz]; omega
          rw [mem_arenaClauseLits_iff hbd_d] at hl; obtain ⟨k, hk, hget⟩ := hl
          have hkn : k < new_sz := by
            dsimp only [arenaClauseSize, sc'] at hk; rw [hsz] at hk; exact hk
          have hlt_k := hlits_lt k hkn
          rw [List.getElem?_eq_getElem (by rw [hlen']; omega), Option.getD_some] at hlt_k
          dsimp only [sc'] at hget; omega
      · intro r hr hng'; rw [hrefs_sd, List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | hdst
        · rw [h_garb r hr] at hng'; rw [h_lits r hr]; exact hcomp_d.entails r hr hng'
        · rw [hdst]; simpa only [arenaClauseLits, arenaClauseSize, sc'] using hent
    have hng_dst : arenaClauseGarb sc' dst = false := by
      unfold arenaClauseGarb arenaHdr sc'; simp [hng]
    have hno_garb' : ∀ r ∈ arenaClauseRefs sc', arenaClauseGarb sc' r = false := fun r hr => by
      rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · have hr' : r ∈ arenaClauseRefs sd := hrefs_d ▸ hr
        rw [h_garb r hr', (hprops_d r hr).1]; exact hp.no_garb r hr
      · exact hng_dst
    refine ⟨⟨hlen', hdst_le_nsrc, hwf0.2.2.2.1,
      arenaScan_step (fun r hr => (hinv0.arena.refs_wf r hr).2.2.2.2) href,
      fun k hk1 hk2 => (hhold_suf k (by omega) hk2).trans (hp.suffix_eq k (by omega) hk2),
      hcomp', hno_garb'⟩, hrefs, fun r hr => ?_⟩
    obtain ⟨h1, _, h3⟩ := hprops_d r hr
    have hr' : r ∈ arenaClauseRefs sd := hrefs_d ▸ hr
    exact ⟨(h_garb r hr').trans h1, (h_lits r hr').trans h3⟩

/-- Reason-relocation invariant maintained across `plain_sweep` Phase 2. -/
@[expose] def RsnRelocInv (s0 s : PlainState) (src dst : Nat) : Prop :=
  s.rsns.length = s0.rsns.length ∧
  (0 < s0.cur_level → ∀ v, (∃ idx < s0.trail_end, (s0.trl[idx]?.getD 0#32).toNat / 2 = v ∧
    let r0 := s0.rsns[v]?.getD 0xFFFFFFFF#32
    r0 ≠ 0xFFFFFFFF#32 ∧ (r0 &&& 0x80000000#32) = 0#32 ∧ r0.toNat < src) ∨
    s.rsns[v]? = s0.rsns[v]?) ∧
  (0 < s0.cur_level → ∀ idx < s0.trail_end,
    let p := (s0.trl[idx]?.getD 0#32).toNat
    let r0 := s0.rsns[p / 2]?.getD 0xFFFFFFFF#32
    let r := s.rsns[p / 2]?.getD 0xFFFFFFFF#32
    r0 ≠ 0xFFFFFFFF#32 → (r0 &&& 0x80000000#32) = 0#32 →
    if r0.toNat < src then
      r.toNat < dst ∧ r ≠ 0xFFFFFFFF#32 ∧ (r &&& 0x80000000#32) = 0#32 ∧
      r.toNat ∈ arenaClauseRefs { s with arena_len := dst } ∧
      arenaClauseGarb { s with arena_len := dst } r.toNat = false ∧
      p ∈ arenaClauseLits { s with arena_len := dst } r.toNat ∧
      arenaClauseLits { s with arena_len := dst } r.toNat = arenaClauseLits s0 r0.toNat
    else r = r0)

theorem rsnReloc_init (s0 : PlainState) : RsnRelocInv s0 s0 0 0 :=
  ⟨rfl, fun _ _ => Or.inr rfl, fun _ _ _ _ _ => by simp⟩

theorem rsnReloc_l0 {s0 s : PlainState} {src dst : Nat} (hcl : s0.cur_level = 0)
    (hrlen : s.rsns.length = s0.rsns.length) : RsnRelocInv s0 s src dst :=
  ⟨hrlen, fun h => absurd h (by omega), fun h => absurd h (by omega)⟩

private theorem rsnReloc_not_in {c : PlainCfg} {F0 : CNF Nat} {s0 : PlainState} {src idx : Nat}
    (hinv0 : PlainCoreInv c F0 s0) (hsrc_ref : src ∈ arenaClauseRefs s0) (hidx : idx < s0.trail_end)
    (hno : (s0.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat ≠ src)
    (hne : s0.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hmsb : (s0.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) =
      0#32) :
    (s0.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat <
        arenaNextOff s0.arena s0.arena_len src ↔
      (s0.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat < src := by
  have hrs := hinv0.reason_inv idx hidx hne
  split at hrs
  · rename_i h1; exact absurd hmsb h1
  · by_cases hlt : (s0.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat < src
    · have := arenaNextOff_bounds (ar := s0.arena) (alen := s0.arena_len) (cref := src)
        (hinv0.arena.refs_wf src hsrc_ref).1
      omega
    · have hdisj := arenaScanRefs_disjoint hsrc_ref hrs.1 (by omega)
      constructor <;> intro h <;> omega

theorem rsnReloc_preserve {c : PlainCfg} {F0 : CNF Nat} {s0 s : PlainState}
    {src dst dst' : Nat} {arena' : List (BitVec 32)}
    (hinv0 : PlainCoreInv c F0 s0) (hrr : RsnRelocInv s0 s src dst)
    (hsrc_ref : src ∈ arenaClauseRefs s0) (hno : ∀ idx < s0.trail_end,
      (s0.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat ≠ src)
    (hrel : ∀ r ∈ arenaClauseRefs { s with arena_len := dst },
      r ∈ arenaClauseRefs { s with arena := arena', arena_len := dst' } ∧
      arenaClauseGarb { s with arena := arena', arena_len := dst' } r =
        arenaClauseGarb { s with arena_len := dst } r ∧
      arenaClauseLits { s with arena := arena', arena_len := dst' } r =
        arenaClauseLits { s with arena_len := dst } r)
    (hdst_le : dst ≤ dst') :
    let nsrc := arenaNextOff s0.arena s0.arena_len src
    RsnRelocInv s0 { s with arena := arena' } nsrc dst' := by
  intro nsrc
  refine ⟨hrr.1, fun hpos v => ?_, fun hpos idx hidx hne hmsb => ?_⟩
  · rcases hrr.2.1 hpos v with ⟨idx, hi, hv, hne, hmsb, hlt⟩ | heq
    · have hnb := (arenaNextOff_bounds (ar := s0.arena) (alen := s0.arena_len) (cref := src)
        (hinv0.arena.refs_wf src hsrc_ref).1).1
      exact Or.inl ⟨idx, hi, hv, hne, hmsb, by omega⟩
    · exact Or.inr heq
  · have hstep := hrr.2.2 hpos idx hidx hne hmsb
    have hnot_in := rsnReloc_not_in hinv0 hsrc_ref hidx (hno idx hidx) hne hmsb
    dsimp only at *
    by_cases hlt : (s0.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat < src
    · have hlt' : (s0.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat < nsrc :=
        hnot_in.mpr hlt
      simp only [hlt, ↓reduceIte] at hstep; simp only [hlt', ↓reduceIte]
      obtain ⟨hlt1, hr1, hr2, href, hng, hmem, hlits⟩ := hstep
      obtain ⟨href', hng', hlits'⟩ := hrel _ href
      exact ⟨by omega, hr1, hr2, href', hng'.trans hng, hlits' ▸ hmem, hlits'.trans hlits⟩
    · have hlt' : ¬ (s0.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat <
          nsrc := fun h => hlt (hnot_in.mp h)
      simp only [hlt, ↓reduceIte] at hstep; simp only [hlt', ↓reduceIte]; exact hstep

theorem rsnReloc_skip {c : PlainCfg} {F0 : CNF Nat} {s0 s : PlainState}
    {src dst : Nat} (hinv0 : PlainCoreInv c F0 s0) (hrr : RsnRelocInv s0 s src dst)
    (hsrc_ref : src ∈ arenaClauseRefs s0)
    (hbad : (s0.arena[src]?.getD 0#32 &&& 0x00080000#32) ≠ 0#32 ∨ s0.cur_level = 0) :
    RsnRelocInv s0 s (arenaNextOff s0.arena s0.arena_len src) dst := by
  have hno : ∀ idx < s0.trail_end,
      (s0.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat ≠ src := by
    intro idx hidx heq
    have hbd_s : src < s0.arena_len := (hinv0.arena.refs_wf src hsrc_ref).1 |> fun h => by omega
    have har := c.harena; unfold dimacsBound at har
    have hlen_a := hinv0.lengths.arena_len_le
    have hne : s0.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
      intro h; rw [h] at heq; simp at heq; omega
    have hrs := hinv0.reason_inv idx hidx hne
    have hmsb0 : (s0.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
        0x80000000#32) = 0#32 := by
      have hlt : (s0.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat <
          0x80000000 := by omega
      exact PlainReduceTactics.bv32_and_msb_zero_of_ult hlt
    split at hrs
    · rename_i h1; exact absurd hmsb0 h1
    · rcases hbad with hgb | hcl0
      · have hg := hrs.2.1; unfold arenaClauseGarb arenaHdr at hg; rw [heq] at hg
        simp [hgb] at hg
      · have hle := hinv0.lvl_le idx hidx; rw [hcl0] at hle
        exact absurd (hinv0.level0_rsn_none idx hidx (by omega)) hne
  exact rsnReloc_preserve hinv0 hrr hsrc_ref hno
    (fun r hr => ⟨hr, rfl, rfl⟩) (Nat.le_refl dst)

theorem rsnReloc_step_nohit {c : PlainCfg} {F0 : CNF Nat} {s0 s : PlainState}
    {src dst new_sz : Nat} {arena' : List (BitVec 32)}
    (hinv0 : PlainCoreInv c F0 s0) (hrm0 : 0 < s0.cur_level → ReasonsMarked s0)
    (hrr : RsnRelocInv s0 s src dst) (hsrc_ref : src ∈ arenaClauseRefs s0)
    (hsz_eq : (arena'[dst + 2]?.getD 0#32).toNat = new_sz)
    (har_len : arena'.length = c.arena_cap) (hdst_bd : dst + 3 + new_sz ≤ c.arena_cap)
    (hlits_eq : arenaClauseLits { s with arena := arena', arena_len := dst + 3 + new_sz } dst =
      arenaClauseLits s0 src)
    (hrel : ∀ r ∈ arenaClauseRefs { s with arena_len := dst },
      r ∈ arenaClauseRefs { s with arena := arena', arena_len := dst + 3 + new_sz } ∧
      arenaClauseGarb { s with arena := arena', arena_len := dst + 3 + new_sz } r =
        arenaClauseGarb { s with arena_len := dst } r ∧
      arenaClauseLits { s with arena := arena', arena_len := dst + 3 + new_sz } r =
        arenaClauseLits { s with arena_len := dst } r)
    (hnohit : s0.cur_level = 0 ∨ (s0.arena[src]?.getD 0#32 &&& 0x00200000#32) = 0#32 ∨
      ∀ k < new_sz,
        let lit := arena'[dst + 3 + k]?.getD 0#32
        ¬ (lit.toNat / 2 < c.mv ∧ (0#8).slt (s0.vals[lit.toNat]?.getD 0#8) = true ∧
          s.rsns[lit.toNat / 2]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 src)) :
    let nsrc := arenaNextOff s0.arena s0.arena_len src
    RsnRelocInv s0 { s with arena := arena' } nsrc (dst + 3 + new_sz) := by
  have har := c.harena; unfold dimacsBound at har; have hlen_a := hinv0.lengths.arena_len_le
  have hsrc_lt : src < s0.arena_len := by have := (hinv0.arena.refs_wf src hsrc_ref).1; omega
  have hno : ∀ idx < s0.trail_end,
      (s0.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat ≠ src := by
    intro idx hidx heq
    have hne : s0.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 :=
      fun h => by rw [h] at heq; simp at heq; omega
    have hmsb0 : (s0.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
        0x80000000#32) = 0#32 := PlainReduceTactics.bv32_and_msb_zero_of_ult (by omega)
    rcases hnohit with hcl0 | hnrsn | hall
    · have hle := hinv0.lvl_le idx hidx; rw [hcl0] at hle
      exact absurd (hinv0.level0_rsn_none idx hidx (by omega)) hne
    · have hcur : 0 < s0.cur_level := Nat.pos_of_ne_zero fun hc => by
        have hle := hinv0.lvl_le idx hidx; rw [hc] at hle
        exact absurd (hinv0.level0_rsn_none idx hidx (by omega)) hne
      have hpos : 0 < (s0.lvl[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat :=
        Nat.pos_of_ne_zero fun hz => absurd (hinv0.level0_rsn_none idx hidx hz) hne
      have hm := hrm0 hcur idx hidx hpos hmsb0
      unfold arenaHdr at hm; rw [heq] at hm; exact absurd hnrsn hm
    · have hmem : (s0.trl[idx]?.getD 0#32).toNat ∈ arenaClauseLits s0 src := by
        simpa [heq] using hinv0.reason_lit_mem idx hidx hne hmsb0
      rw [← hlits_eq] at hmem
      have hbd : dst + 3 +
          arenaClauseSize { s with arena := arena', arena_len := dst + 3 + new_sz } dst ≤
          arena'.length := by unfold arenaClauseSize; simp [hsz_eq, har_len]; omega
      rw [mem_arenaClauseLits_iff hbd] at hmem; obtain ⟨k, hk, hget⟩ := hmem
      have hkn : k < new_sz := by unfold arenaClauseSize at hk; simpa [hsz_eq] using hk
      have hilt := hinv0.trail_lits_lt idx hidx
      have hval1 : s0.vals[(s0.trl[idx]?.getD 0#32).toNat]?.getD 0#8 = 1#8 :=
        (hinv0.vals_true_iff _ hilt).mpr ⟨idx, hidx, rfl⟩
      have hgt0 : (0#8).slt (s0.vals[(s0.trl[idx]?.getD 0#32).toNat]?.getD 0#8) = true := by
        rw [hval1]; decide
      have hrsn_eq : s.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
          s0.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 := by
        have hcur : 0 < s0.cur_level := Nat.pos_of_ne_zero fun hc => by
          have hle := hinv0.lvl_le idx hidx; rw [hc] at hle
          exact absurd (hinv0.level0_rsn_none idx hidx (by omega)) hne
        have hstep := hrr.2.2 hcur idx hidx hne hmsb0
        have hnotlt : ¬ (s0.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32).toNat < src := by omega
        simpa [hnotlt] using hstep
      have hlit_eq : (arena'[dst + 3 + k]?.getD 0#32).toNat = (s0.trl[idx]?.getD 0#32).toNat := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hget
      have hsrc32 : BitVec.ofNat 32 src =
          s0.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 := by
        apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), heq]
      refine hall k hkn ⟨by simp [hlit_eq]; omega, by simp [hlit_eq, hgt0], ?_⟩
      simp only [hlit_eq, hrsn_eq, hsrc32]
  exact rsnReloc_preserve hinv0 hrr hsrc_ref hno hrel (by omega)

theorem rsnReloc_step_hit {c : PlainCfg} {F0 : CNF Nat} {s0 s : PlainState}
    {src dst new_sz k : Nat} {arena' : List (BitVec 32)} {lit : BitVec 32}
    (hinv0 : PlainCoreInv c F0 s0) (hrr : RsnRelocInv s0 s src dst)
    (hcur_pos : 0 < s0.cur_level) (hsrc_ref : src ∈ arenaClauseRefs s0)
    (hdst_le_src : dst ≤ src) (hk : k < new_sz)
    (hsz_eq : (arena'[dst + 2]?.getD 0#32).toNat = new_sz)
    (har_len : arena'.length = c.arena_cap) (hdst_bd : dst + 3 + new_sz ≤ c.arena_cap)
    (hlit : arena'[dst + 3 + k]? = some lit)
    (hlits_eq : arenaClauseLits { s with arena := arena', arena_len := dst + 3 + new_sz } dst =
      arenaClauseLits s0 src)
    (hdst_in : dst ∈ arenaClauseRefs { s with arena := arena', arena_len := dst + 3 + new_sz })
    (hdst_ng :
      arenaClauseGarb { s with arena := arena', arena_len := dst + 3 + new_sz } dst = false)
    (hrel : ∀ r ∈ arenaClauseRefs { s with arena_len := dst },
      r ∈ arenaClauseRefs { s with arena := arena', arena_len := dst + 3 + new_sz } ∧
      arenaClauseGarb { s with arena := arena', arena_len := dst + 3 + new_sz } r =
        arenaClauseGarb { s with arena_len := dst } r ∧
      arenaClauseLits { s with arena := arena', arena_len := dst + 3 + new_sz } r =
        arenaClauseLits { s with arena_len := dst } r)
    (hv_lt : lit.toNat / 2 < c.mv) (hvals_pos : (0#8).slt (s0.vals[lit.toNat]?.getD 0#8) = true)
    (hrsn_src : s.rsns[lit.toNat / 2]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 src) :
    let v := lit.toNat / 2
    let nsrc := arenaNextOff s0.arena s0.arena_len src
    RsnRelocInv s0 { s with arena := arena', rsns := s.rsns.set v (BitVec.ofNat 32 dst) }
      nsrc (dst + 3 + new_sz) := by
  intro v nsrc
  have har := c.harena; unfold dimacsBound at har; have hlen_a := hinv0.lengths.arena_len_le
  have hsrc_lt : src < s0.arena_len := by have := (hinv0.arena.refs_wf src hsrc_ref).1; omega
  have hnb := arenaNextOff_bounds (ar := s0.arena) (alen := s0.arena_len) (cref := src)
    (hinv0.arena.refs_wf src hsrc_ref).1
  have hlit_lt : lit.toNat < 2 * c.mv := by omega
  have hval1 : s0.vals[lit.toNat]?.getD 0#8 = 1#8 :=
    (bv8_zero_slt_iff (hinv0.vals_domain _ hlit_lt)).mp hvals_pos
  obtain ⟨idx0, hidx0, hp0⟩ := (hinv0.vals_true_iff _ hlit_lt).mp hval1
  have huniq : ∀ idx < s0.trail_end, (s0.trl[idx]?.getD 0#32).toNat / 2 = v → idx = idx0 :=
    fun idx hi hv => hinv0.trail_vars_nodup idx idx0 hi hidx0 (by rw [hv, hp0])
  have hr0_src : s0.rsns[v]?.getD 0xFFFFFFFF#32 = BitVec.ofNat 32 src := by
    rcases hrr.2.1 hcur_pos v with ⟨idx', hi', hv', hne', hmsb', hlt'⟩ | heq
    · have hid := huniq idx' hi' hv'; subst idx'
      have hstep := hrr.2.2 hcur_pos idx0 hidx0
        (by simpa [hp0] using hne') (by simpa [hp0] using hmsb')
      have hlt_p : (s0.rsns[(s0.trl[idx0]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32).toNat < src := by simpa [hp0] using hlt'
      simp only [hlt_p, ↓reduceIte] at hstep
      have h2 := congrArg BitVec.toNat hrsn_src
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h2
      have h3 : (s.rsns[lit.toNat / 2]?.getD 0xFFFFFFFF#32).toNat < dst := by
        simpa [hp0] using hstep.1
      omega
    · rw [← heq, hrsn_src]
  have hv_rsn : v < s.rsns.length := by rw [hrr.1, hinv0.lengths.rsns_len]; exact hv_lt
  have hmem_s0 : lit.toNat ∈ arenaClauseLits s0 src := by
    rw [← hlits_eq]
    have hbd : dst + 3 + arenaClauseSize { s with arena := arena', arena_len := dst + 3 + new_sz }
        dst ≤ arena'.length := by unfold arenaClauseSize; simp [hsz_eq, har_len]; omega
    rw [mem_arenaClauseLits_iff hbd]
    refine ⟨k, by unfold arenaClauseSize; simpa [hsz_eq], ?_⟩
    rw [List.getElem?_eq_getElem (by omega)] at hlit
    exact congrArg BitVec.toNat (Option.some.inj hlit)
  have hno_other : ∀ idx < s0.trail_end, idx ≠ idx0 →
      (s0.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat ≠ src := by
    intro idx hidx hne_i heq
    have hne : s0.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 :=
      fun h => by rw [h] at heq; simp at heq; omega
    have hmsb0 : (s0.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
        0x80000000#32) = 0#32 := PlainReduceTactics.bv32_and_msb_zero_of_ult (by omega)
    have hrs := hinv0.reason_inv idx hidx hne
    split at hrs
    · rename_i h1; exact absurd hmsb0 h1
    · rcases hrs.2.2 lit.toNat (by simpa [heq] using hmem_s0) with hlp | ⟨j, hj, hjneg⟩
      · exact hne_i (huniq idx hidx (by rw [← hlp]))
      · have hvalf := (hinv0.vals_false_iff lit.toNat hlit_lt).mpr ⟨j, by omega, hjneg⟩
        rw [hval1] at hvalf; cases hvalf
  refine ⟨by simp [hrr.1], fun hpos w => ?_, fun hpos idx hidx hne hmsb => ?_⟩
  · by_cases hwv : w = v
    · subst w; refine Or.inl ⟨idx0, hidx0, by rw [hp0], ?_, ?_, ?_⟩
      · rw [hr0_src]; exact PlainReduceTactics.bv32_ne_allOnes_of_ult
          (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
      · rw [hr0_src]; exact PlainReduceTactics.bv32_and_msb_zero_of_ult
          (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
      · rw [hr0_src, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hnb.1
    · rw [List.getElem?_set_ne (Ne.symm hwv)]
      rcases hrr.2.1 hpos w with ⟨idx, hi, hv, hne', hmsb', hlt⟩ | heq
      · exact Or.inl ⟨idx, hi, hv, hne', hmsb', by omega⟩
      · exact Or.inr heq
  · by_cases hi0 : idx = idx0
    · subst idx; dsimp only at *; rw [hp0]
      simp only [show (s0.rsns[lit.toNat / 2]?.getD 0xFFFFFFFF#32).toNat < nsrc by
        rw [show lit.toNat / 2 = v from rfl, hr0_src, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega)]; exact hnb.1, ↓reduceIte]
      change (let r := (s.rsns.set v (BitVec.ofNat 32 dst))[v]?.getD 0xFFFFFFFF#32; _)
      rw [List.getElem?_set_self hv_rsn, Option.getD_some]
      have hdst_lt : (BitVec.ofNat 32 dst).toNat = dst :=
        by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hlits_rsn : arenaClauseLits
          ({ s with
            arena := arena', arena_len := dst + 3 + new_sz,
            rsns := s.rsns.set v (BitVec.ofNat 32 dst) } : PlainState) dst =
          arenaClauseLits s0 src := hlits_eq
      refine ⟨by rw [hdst_lt]; omega,
        PlainReduceTactics.bv32_ne_allOnes_of_ult (by rw [hdst_lt]; omega),
        PlainReduceTactics.bv32_and_msb_zero_of_ult (by rw [hdst_lt]; omega),
        by rwa [hdst_lt], by rwa [hdst_lt],
        by rw [hdst_lt, hlits_rsn]; exact hmem_s0,
        by rw [hdst_lt, hlits_rsn, hr0_src, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]⟩
    · have hnv : (s0.trl[idx]?.getD 0#32).toNat / 2 ≠ v := fun h => hi0 (huniq idx hidx h)
      have hset_ne : (s.rsns.set v (BitVec.ofNat 32 dst))[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 = s.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 :=
        congrArg (Option.getD · 0xFFFFFFFF#32) (List.getElem?_set_ne (Ne.symm hnv))
      have hnot_in := rsnReloc_not_in hinv0 hsrc_ref hidx (hno_other idx hidx hi0) hne hmsb
      have hstep := hrr.2.2 hpos idx hidx hne hmsb
      dsimp only at *; rw [hset_ne]
      by_cases hlt : (s0.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat < src
      · have hlt' : (s0.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat <
            nsrc := hnot_in.mpr hlt
        simp only [hlt, ↓reduceIte] at hstep; simp only [hlt', ↓reduceIte]
        obtain ⟨hlt1, hr1, hr2, href, hng, hmem, hlits⟩ := hstep
        obtain ⟨href', hng', hlits'⟩ := hrel _ href
        exact ⟨by omega, hr1, hr2, href', hng'.trans hng, hlits' ▸ hmem, hlits'.trans hlits⟩
      · have hlt' : ¬ (s0.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32).toNat < nsrc := fun h => hlt (hnot_in.mp h)
        simp only [hlt, ↓reduceIte] at hstep; simp only [hlt', ↓reduceIte]; exact hstep

private theorem rsnReloc_step_info {c : PlainCfg} {F0 : CNF Nat} {s0 s : PlainState} {dst : Nat}
    (hinv0 : PlainCoreInv c F0 s0)
    (hkeep : 0 < s0.cur_level → s.trl = s0.trl ∧ s.trail_end = s0.trail_end)
    (hrr : RsnRelocInv s0 s s0.arena_len dst) (hsc_eq : { s with arena_len := dst } = s)
    (hpos : 0 < s0.cur_level) {idx : Nat} (hidx : idx < s.trail_end)
    (hne : s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hmsb0 : (s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) =
      0#32) :
    let p := (s.trl[idx]?.getD 0#32).toNat
    let rsn := s.rsns[p / 2]?.getD 0xFFFFFFFF#32
    rsn.toNat ∈ arenaClauseRefs s ∧ arenaClauseGarb s rsn.toNat = false ∧
      p ∈ arenaClauseLits s rsn.toNat ∧
      (∀ q ∈ arenaClauseLits s rsn.toNat,
        q = p ∨ ∃ k < idx, (s.trl[k]?.getD 0#32).toNat = q ^^^ 1) := by
  obtain ⟨htrl, hte⟩ := hkeep hpos; have hidx0 : idx < s0.trail_end := hte ▸ hidx
  have hp_eq : (s.trl[idx]?.getD 0#32).toNat = (s0.trl[idx]?.getD 0#32).toNat := by rw [htrl]
  have ⟨hne0, hmsb', hlt0⟩ : ∃ (hn : s0.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD
      0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32),
      (s0.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&& 0x80000000#32) = 0#32 ∧
      (s0.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat < s0.arena_len := by
    rcases hrr.2.1 hpos ((s0.trl[idx]?.getD 0#32).toNat / 2) with
        ⟨idx', hi', hv', hne', hm', hl'⟩ | heq
    · have := hinv0.trail_vars_nodup _ _ hi' hidx0 hv'; subst idx'; exact ⟨hne', hm', hl'⟩
    · have hne0 : s0.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠
          0xFFFFFFFF#32 := by simpa [hp_eq, heq] using hne
      have hm0 : (s0.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
          0x80000000#32) = 0#32 := by simpa [hp_eq, heq] using hmsb0
      have hrs0 := hinv0.reason_inv idx hidx0 hne0
      dsimp only at hrs0; simp only [hm0, ne_eq, not_true_eq_false, ↓reduceIte] at hrs0
      have := (hinv0.arena.refs_wf _ hrs0.1).1; have := (hinv0.arena.refs_wf _ hrs0.1).2.1
      exact ⟨hne0, hm0, by omega⟩
  have hstep := hrr.2.2 hpos idx hidx0 hne0 hmsb'
  simp only [hlt0, ↓reduceIte, hsc_eq] at hstep
  have hrs0 := hinv0.reason_inv idx hidx0 hne0
  dsimp only at hrs0; simp only [hmsb', ne_eq, not_true_eq_false, ↓reduceIte] at hrs0
  refine ⟨by simpa [hp_eq] using hstep.2.2.2.1, by simpa [hp_eq] using hstep.2.2.2.2.1,
    by simpa [hp_eq] using hstep.2.2.2.2.2.1, fun q hq => ?_⟩
  have hq0 : q ∈ arenaClauseLits s0
      (s0.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat := by
    simpa [hp_eq, hstep.2.2.2.2.2.2] using hq
  rcases hrs0.2.2 q hq0 with rfl | ⟨k, hk, hkeq⟩
  · exact Or.inl hp_eq.symm
  · exact Or.inr ⟨k, hk, by rw [htrl]; exact hkeq⟩

theorem phase2_to_core {c : PlainCfg} {F0 : CNF Nat} {s0 s : PlainState} {dst : Nat}
    (hinv0 : PlainCoreInv c F0 s0) (hlen : s.LengthsOk c) (htv : TrailValsInv c F0 s)
    (hb : BinWatchesOnly c F0 s (2 * c.mv)) (hp : ArenaPrefixOk c F0 s0 s s0.arena_len dst)
    (hrr : RsnRelocInv s0 s s0.arena_len dst) (hal : s.arena_len = dst)
    (hscl : s.cur_level = s0.cur_level)
    (hkeep : 0 < s0.cur_level → s.trl = s0.trl ∧ s.trail_end = s0.trail_end) :
    PlainCoreInv c F0 s := by
  have hsc_eq : { s with arena_len := dst } = s := by cases s; cases hal; rfl
  have hcomp : ArenaClausesInv c F0 s := by have := hp.comp_arena; rwa [hsc_eq] at this
  refine ⟨hlen, hcomp, hb.1, htv.cur_level_le, htv.trail_lits_lt, htv.trail_vars_nodup,
    htv.vals_domain, htv.vals_true_iff, htv.vals_false_iff, htv.lvl_le, htv.trail_mono,
    htv.levels_inhabited, htv.level0_sound, htv.trail_pos_inv, htv.level0_rsn_none, ?_, ?_⟩
  · intro idx hidx; dsimp only; intro hne
    by_cases hcl0 : s0.cur_level = 0
    · have hle := htv.lvl_le idx hidx; rw [hscl, hcl0] at hle
      exact absurd (htv.level0_rsn_none idx hidx (by omega)) hne
    · have hpos : 0 < s0.cur_level := Nat.pos_of_ne_zero hcl0
      split
      · rename_i hbin
        obtain ⟨htrl, hte⟩ := hkeep hpos; have hidx0 := hte ▸ hidx
        have hp_eq : (s.trl[idx]?.getD 0#32).toNat = (s0.trl[idx]?.getD 0#32).toNat := by rw [htrl]
        rcases hrr.2.1 hpos ((s0.trl[idx]?.getD 0#32).toNat / 2) with
            ⟨idx', hi', hv', hne', hm', hl'⟩ | heq
        · have := hinv0.trail_vars_nodup _ _ hi' hidx0 hv'; subst idx'
          have hstep := hrr.2.2 hpos idx hidx0 hne' hm'
          simp only [hl', ↓reduceIte, hsc_eq] at hstep
          exact absurd (by simpa [hp_eq] using hstep.2.2.1) hbin
        · have hrs0 := hinv0.reason_inv idx hidx0 (by simpa [hp_eq, heq] using hne)
          have hbin0 : (s0.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
              0x80000000#32) ≠ 0#32 := by simpa [hp_eq, heq] using hbin
          split at hrs0
          · simpa [htrl, heq] using hrs0
          · rename_i hnb; exact absurd hbin0 hnb
      · rename_i hnbin
        have hi := rsnReloc_step_info hinv0 hkeep hrr hsc_eq hpos hidx hne
          (Classical.not_not.mp hnbin)
        exact ⟨hi.1, hi.2.1, hi.2.2.2⟩
  · intro idx hidx; dsimp only; intro hne hmsb
    by_cases hcl0 : s0.cur_level = 0
    · have hle := htv.lvl_le idx hidx; rw [hscl, hcl0] at hle
      exact absurd (htv.level0_rsn_none idx hidx (by omega)) hne
    · exact (rsnReloc_step_info hinv0 hkeep hrr hsc_eq (Nat.pos_of_ne_zero hcl0) hidx hne
        hmsb).2.2.1

theorem arenaClauseLits_take_set_append {ar : List (BitVec 32)} {dst n : Nat}
    {lit : BitVec 32} (hlt : dst + 3 + n < ar.length) :
    ((((ar.set (dst + 3 + n) lit).drop (dst + 3)).take (n + 1)).map BitVec.toNat) =
      (((ar.drop (dst + 3)).take n).map BitVec.toNat) ++ [lit.toNat] := by
  have hlen1 : (((ar.set (dst + 3 + n) lit).drop (dst + 3)).take (n + 1)).length = n + 1 := by
    rw [List.length_take, List.length_drop, List.length_set]; omega
  have hlen2 : ((ar.drop (dst + 3)).take n).length = n := by
    rw [List.length_take, List.length_drop]; omega
  apply List.ext_getElem
  · rw [List.length_map, hlen1, List.length_append, List.length_map, hlen2, List.length_singleton]
  · intro k hk1 _; have hk' : k < n + 1 := by rw [List.length_map, hlen1] at hk1; exact hk1
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
    by_cases hkn : k = n
    · subst k; rw [List.getElem_append_right (by rw [List.length_map, hlen2]; exact Nat.le_refl _)]
      simp only [List.length_map, hlen2, Nat.sub_self, List.getElem_singleton,
        List.getElem_set_self]
    · have hklt : k < n := by omega
      rw [List.getElem_append_left (by rw [List.length_map, hlen2]; exact hklt), List.getElem_map,
        List.getElem_take, List.getElem_drop, List.getElem_set_ne (by omega)]

theorem entails_append_drop_cons {F0 : CNF Nat} {kept rest : List Nat} {x : Nat}
    (hent : F0.EntailsClause (cnfClause (kept ++ x :: rest))) :
    F0.EntailsClause (cnfClause ((kept ++ [x]) ++ rest)) :=
  entails_of_mem_or_false hent fun _ hl => Or.inl (by simp_all)

theorem entails_drop_falsified_cons {F0 : CNF Nat} {kept rest : List Nat} {x : Nat}
    (hent : F0.EntailsClause (cnfClause (kept ++ x :: rest)))
    (hfals : F0.EntailsClause (cnfClause [x ^^^ 1])) :
    F0.EntailsClause (cnfClause (kept ++ rest)) :=
  entails_of_mem_or_false hent fun _ hl => by
    simp only [List.mem_append, List.mem_cons] at hl ⊢
    rcases hl with h | rfl | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr hfals
    · exact Or.inl (Or.inr h)

theorem atRoot_unsat_of_nil {F0 : CNF Nat}
    (h : F0.EntailsClause (cnfClause [])) : F0.Unsat := unsat_of_entails_nil h

theorem level0_entails_neg_of_fals {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (htv : TrailValsInv c F0 s) (hcl : s.cur_level = 0) {u : Nat} (hu : u < 2 * c.mv)
    (hfals : s.vals[u]?.getD 0#8 = 0xFF#8) :
    F0.EntailsClause (cnfClause [u ^^^ 1]) := by
  obtain ⟨i, hi, heq⟩ := (htv.vals_false_iff u hu).mp hfals
  have hli : (s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
    have := htv.lvl_le i hi; omega
  have hneg := htv.level0_sound i hi hli
  rwa [← heq]

theorem atRoot_unsat_of_unit_neg {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (htv : TrailValsInv c F0 s) (hcl : s.cur_level = 0) {u : Nat} (hu : u < 2 * c.mv)
    (hent : F0.EntailsClause (cnfClause [u])) (hfals : s.vals[u]?.getD 0#8 = 0xFF#8) :
    F0.Unsat :=
  unsat_of_entails_nil
    (entails_drop_falsified_cons (kept := []) (rest := []) hent
      (level0_entails_neg_of_fals htv hcl hu hfals))

theorem drop_head_eq {α : Type} {xs : List α} {i : Nat} (hi : i < xs.length) :
    xs.drop i = xs[i] :: xs.drop (i + 1) := List.drop_eq_getElem_cons hi

theorem entails_clause_swap2 {F0 : CNF Nat} {a b : Nat}
    (h : F0.EntailsClause (cnfClause [a, b])) : F0.EntailsClause (cnfClause [b, a]) :=
  entails_of_mem_or_false h fun _ hl =>
    Or.inl (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hl ⊢; exact hl.symm)

theorem binWatchOk_pair {c : PlainCfg} {F0 : CNF Nat} {l0 l1 : BitVec 32}
    (h0 : l0.toNat < 2 * c.mv) (h1 : l1.toNat < 2 * c.mv)
    (hent : F0.EntailsClause (cnfClause [l0.toNat, l1.toNat])) :
    let b0 := (l1 &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    let b1 := (l0 &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    BinWatchOk c F0 l0.toNat b0 ∧ BinWatchOk c F0 l1.toNat b1 ∧
      b0 ≠ 0xFFFFFFFF#32 ∧ b1 ≠ 0xFFFFFFFF#32 := by
  have hmv := c.hmv; unfold dimacsBound at hmv
  obtain ⟨_, h0m, h0l, h0ne⟩ := bv32_lit_bin_flag (lit := l0) (by omega)
  obtain ⟨_, h1m, h1l, h1ne⟩ := bv32_lit_bin_flag (lit := l1) (by omega)
  exact ⟨⟨h1m, by rw [h1l]; exact h1, by rwa [h1l]⟩,
    ⟨h0m, by rw [h0l]; exact h0, by rw [h0l]; exact entails_clause_swap2 hent⟩, h1ne, h0ne⟩

theorem bv32_hdr_clear_shrk_rsn {hdr : BitVec 32} (hng : (hdr &&& 0x00080000#32) = 0#32) :
    let hdr' := hdr &&& ~~~(0x00800000#32 ||| 0x00200000#32)
    (hdr' &&& 0x00800000#32) = 0#32 ∧ (hdr' &&& 0x00080000#32) = 0#32 := by
  have hs : ((~~~(0x00800000#32 ||| 0x00200000#32) : BitVec 32) &&& 0x00800000#32) = 0#32 := by
    decide
  have hg : ((~~~(0x00800000#32 ||| 0x00200000#32) : BitVec 32) &&& 0x00080000#32) =
      0x00080000#32 := by decide
  refine ⟨?_, ?_⟩
  · rw [BitVec.and_assoc, hs, BitVec.and_zero]
  · rw [BitVec.and_assoc, hg]; exact hng

/-! ## 3. Sweep Phase 3: Max-rank swaps, search-hint update, and rewatching -/

private theorem arenaNextOff_no_shrk {ar : List (BitVec 32)} {alen r : Nat}
    (hle : r + 3 + (ar[r + 2]?.getD 0#32).toNat ≤ alen)
    (hns : (ar[r]?.getD 0#32 &&& 0x00800000#32) = 0#32) :
    arenaNextOff ar alen r = r + 3 + (ar[r + 2]?.getD 0#32).toNat := by
  unfold arenaNextOff
  simp [show ¬ (r + 3 > alen) by omega,
    show ¬ (r + 3 + (ar[r + 2]?.getD 0#32).toNat > alen) by omega, hns]

private theorem arenaScanRefs_set_inside {ar : List (BitVec 32)} {alen cref k : Nat} {v : BitVec 32}
    (hcref : cref ∈ arenaScanRefs ar alen 0 alen)
    (hns : ∀ r ∈ arenaScanRefs ar alen 0 alen, (ar[r]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hle_ar : ∀ r ∈ arenaScanRefs ar alen 0 alen, r + 3 + (ar[r + 2]?.getD 0#32).toNat ≤ alen)
    (hk1 : cref + 1 ≤ k) (hk2 : k < cref + 3 + (ar[cref + 2]?.getD 0#32).toNat)
    (hne2 : k ≠ cref + 2) :
    arenaScanRefs (ar.set k v) alen 0 alen = arenaScanRefs ar alen 0 alen ∧
    (∀ r ∈ arenaScanRefs (ar.set k v) alen 0 alen,
      ((ar.set k v)[r]?.getD 0#32 &&& 0x00800000#32) = 0#32) ∧
    (∀ r ∈ arenaScanRefs (ar.set k v) alen 0 alen,
      r + 3 + ((ar.set k v)[r + 2]?.getD 0#32).toNat ≤ alen) ∧
    (∀ r ∈ arenaScanRefs ar alen 0 alen, r ≠ k) := by
  have hk_ne_ref : ∀ r ∈ arenaScanRefs ar alen 0 alen, r ≠ k ∧ r + 2 ≠ k := fun r hr => by
    by_cases hrc : r = cref
    · subst hrc; omega
    · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
      · have hd := arenaScanRefs_disjoint hr hcref hlt
        rw [arenaNextOff_no_shrk (hle_ar r hr) (hns r hr)] at hd; omega
      · have hd := arenaScanRefs_disjoint hcref hr hgt
        rw [arenaNextOff_no_shrk (hle_ar cref hcref) (hns cref hcref)] at hd; omega
  have hrefs : arenaScanRefs (ar.set k v) alen 0 alen = arenaScanRefs ar alen 0 alen := by
    refine arenaScanRefs_congr fun r hr => ?_
    obtain ⟨hne0, hne2'⟩ := hk_ne_ref r hr
    have h1 := arenaNextOff_no_shrk (hle_ar r hr) (hns r hr)
    have h2 : arenaNextOff (ar.set k v) alen r = r + 3 + ((ar.set k v)[r + 2]?.getD 0#32).toNat :=
      arenaNextOff_no_shrk (by rw [List.getElem?_set_ne (Ne.symm hne2')]; exact hle_ar r hr)
        (by rw [List.getElem?_set_ne (Ne.symm hne0)]; exact hns r hr)
    rw [h1, h2, List.getElem?_set_ne (Ne.symm hne2')]
  refine ⟨hrefs, fun r hr => ?_, fun r hr => ?_, fun r hr => (hk_ne_ref r hr).1⟩
  · rw [hrefs] at hr; rw [List.getElem?_set_ne (Ne.symm (hk_ne_ref r hr).1)]; exact hns r hr
  · rw [hrefs] at hr; rw [List.getElem?_set_ne (Ne.symm (hk_ne_ref r hr).2)]; exact hle_ar r hr

theorem swapCl_lits_core {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hinv : PlainCoreInv c F0 s) {cref k1 k2 : Nat}
    (hcref : cref ∈ arenaClauseRefs s) (hk1 : k1 < arenaClauseSize s cref)
    (hk2 : k2 < arenaClauseSize s cref) :
    let hlen := hinv.lengths
    have hbd : cref + 3 + arenaClauseSize s cref ≤ s.arena.length := by
      have := (hinv.arena.refs_wf cref hcref).2.2.1; have := (hinv.arena.refs_wf cref hcref).2.2.2.1
      have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
    let l1 := s.arena[cref + 3 + k1]'(by omega)
    let l2 := s.arena[cref + 3 + k2]'(by omega)
    let arena' := (s.arena.set (cref + 3 + k1) l2).set (cref + 3 + k2) l1
    PlainCoreInv c F0 { s with arena := arena' } ∧
      arenaClauseRefs { s with arena := arena' } = arenaClauseRefs s ∧
      (∀ r ∈ arenaClauseRefs s,
        arenaClauseGarb { s with arena := arena' } r = arenaClauseGarb s r) := by
  intro hlen hbd l1 l2 arena'
  have h1_lt : cref + 1 < s.arena.length := by omega
  have har_self : s.arena.set (cref + 1) (s.arena[cref + 1]'h1_lt) = s.arena := by
    apply List.ext_getElem (by simp) fun i hi _ => by
      by_cases hie : i = cref + 1
      · subst i; simp
      · exact List.getElem_set_ne (Ne.symm hie) _
  have hns0 : ∀ r ∈ arenaScanRefs s.arena s.arena_len 0 s.arena_len,
      (s.arena[r]?.getD 0#32 &&& 0x00800000#32) = 0#32 := fun r hr => hinv.arena.no_shrk r hr
  have hle0 : ∀ r ∈ arenaScanRefs s.arena s.arena_len 0 s.arena_len,
      r + 3 + (s.arena[r + 2]?.getD 0#32).toNat ≤ s.arena_len := fun r hr => by
    have := (hinv.arena.refs_wf r hr).2.2.1; have := (hinv.arena.refs_wf r hr).2.2.2.1
    unfold arenaClauseSize at *; omega
  have hs1 := arenaScanRefs_set_inside hcref hns0 hle0 (k := cref + 3 + k1) (v := l2)
    (by omega) (by change _ < _ + _ + arenaClauseSize s cref; omega) (by omega)
  have hcref1 : cref ∈ arenaScanRefs (s.arena.set (cref + 3 + k1) l2) s.arena_len 0 s.arena_len :=
    hs1.1.symm ▸ hcref
  have hs2 := arenaScanRefs_set_inside hcref1 hs1.2.1 hs1.2.2.1 (k := cref + 3 + k2) (v := l1)
    (by omega) (by
      rw [List.getElem?_set_ne (by omega)]
      change _ < _ + _ + arenaClauseSize s cref; omega)
    (by omega)
  have hwat : WatchesInv c F0 { s with arena := arena' } :=
    hinv.watches.with_wstk rfl rfl rfl (hs2.1.trans hs1.1)
  have hcore := swapCl_preserves_core hinv hcref hk1 hk2 hlen.wvec_len hlen.wstk_len_arr
    hlen.heur_ok.wsort_len hlen.wlen_le (srch := s.arena[cref + 1]'h1_lt) (wusable' := s.wusable)
  dsimp only at hcore; rw [har_self] at hcore
  refine ⟨hcore hwat, hs2.1.trans hs1.1, fun r hr => ?_⟩
  unfold arenaClauseGarb arenaHdr arena'; dsimp only
  rw [List.getElem?_set_ne (Ne.symm (hs2.2.2.2 r (hs1.1.symm ▸ hr))),
    List.getElem?_set_ne (Ne.symm (hs1.2.2.2 r hr))]

theorem setSrch2_core {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hinv : PlainCoreInv c F0 s) {cref : Nat} (hcref : cref ∈ arenaClauseRefs s) :
    PlainCoreInv c F0 { s with arena := s.arena.set (cref + 1) 2#32 } ∧
      arenaClauseRefs { s with arena := s.arena.set (cref + 1) 2#32 } = arenaClauseRefs s ∧
      (∀ r ∈ arenaClauseRefs s,
        arenaClauseGarb { s with arena := s.arena.set (cref + 1) 2#32 } r =
          arenaClauseGarb s r) := by
  have hlen := hinv.lengths
  have hsz3 : 3 ≤ arenaClauseSize s cref := (hinv.arena.refs_wf cref hcref).2.1
  have hbd : cref + 3 + arenaClauseSize s cref ≤ s.arena.length := by
    have := (hinv.arena.refs_wf cref hcref).2.2.1; have := (hinv.arena.refs_wf cref hcref).2.2.2.1
    have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
  have hns0 : ∀ r ∈ arenaScanRefs s.arena s.arena_len 0 s.arena_len,
      (s.arena[r]?.getD 0#32 &&& 0x00800000#32) = 0#32 := fun r hr => hinv.arena.no_shrk r hr
  have hle0 : ∀ r ∈ arenaScanRefs s.arena s.arena_len 0 s.arena_len,
      r + 3 + (s.arena[r + 2]?.getD 0#32).toNat ≤ s.arena_len := fun r hr => by
    have := (hinv.arena.refs_wf r hr).2.2.1; have := (hinv.arena.refs_wf r hr).2.2.2.1
    unfold arenaClauseSize at *; omega
  have hs := arenaScanRefs_set_inside hcref hns0 hle0 (k := cref + 1) (v := 2#32)
    (Nat.le_refl _) (by change _ < _ + _ + arenaClauseSize s cref; omega) (by omega)
  have hwat : WatchesInv c F0 { s with arena := s.arena.set (cref + 1) 2#32 } :=
    hinv.watches.with_wstk rfl rfl rfl hs.1
  have hcore := swapCl_preserves_core hinv hcref (k1 := 0) (k2 := 0) (by omega) (by omega)
    hlen.wvec_len hlen.wstk_len_arr hlen.heur_ok.wsort_len hlen.wlen_le (srch := 2#32)
    (wusable' := s.wusable)
  let ar0 := ((s.arena.set (cref + 1) 2#32).set (cref + 3) (s.arena[cref + 3]'(by omega))).set
    (cref + 3) (s.arena[cref + 3]'(by omega))
  have har_eq : ar0 = s.arena.set (cref + 1) 2#32 :=
    List.ext_getElem (by simp [ar0]) fun i hi _ => by
      by_cases hi3 : i = cref + 3
      · subst i; simp only [ar0, List.getElem_set_self]; rw [List.getElem_set_ne (by omega)]
      · simp only [ar0]; rw [List.getElem_set_ne (Ne.symm hi3), List.getElem_set_ne (Ne.symm hi3)]
  have hs_eq :
      ({ s with arena := ar0, wvec := s.wvec, wstk := s.wstk, wlen := s.wlen,
                wusable := s.wusable, heur := { s.heur with wsort := s.heur.wsort } } :
        PlainState) = { s with arena := s.arena.set (cref + 1) 2#32 } := by rw [har_eq]
  dsimp only [Nat.add_zero] at hcore
  change WatchesInv c F0
    ({ s with arena := ar0, wvec := s.wvec, wstk := s.wstk, wlen := s.wlen,
              wusable := s.wusable, heur := { s.heur with wsort := s.heur.wsort } } :
      PlainState) →
    PlainCoreInv c F0
      ({ s with arena := ar0, wvec := s.wvec, wstk := s.wstk, wlen := s.wlen,
                wusable := s.wusable, heur := { s.heur with wsort := s.heur.wsort } } :
        PlainState) at hcore
  rw [hs_eq] at hcore
  refine ⟨hcore hwat, hs.1, fun r hr => ?_⟩
  unfold arenaClauseGarb arenaHdr; dsimp only; rw [List.getElem?_set_ne (Ne.symm (hs.2.2.2 r hr))]

@[expose] def pushWatchState (s : PlainState) (wvec' wstk' wsort' : List (BitVec 32))
    (wlen' : Nat) (wusable' : BitVec 64) : PlainState :=
  { s with wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable',
           heur := { s.heur with wsort := wsort' } }

theorem pushClWatches_step_core {c : PlainCfg} {F0 : CNF Nat}
    {s : PlainState} {lit w0 cref : BitVec 32}
    {wvec' wstk' wsort' : List (BitVec 32)} {wlen' : Nat} {wusable' : BitVec 64}
    (hinv : PlainCoreInv c F0 s)
    (hlay : WatchStackLayout c (pushWatchState s wvec' wstk' wsort' wlen' wusable'))
    (hlen' : (pushWatchState s wvec' wstk' wsort' wlen' wusable').LengthsOk c)
    (h0_eq : (w0 &&& 0x80000000#32) = 0#32) (hcref_lt : cref.toNat < 0x80000000)
    (href : cref.toNat ∈ arenaClauseRefs s)
    (hother : ∀ l < 2 * c.mv, l ≠ lit.toNat →
      watchSize (pushWatchState s wvec' wstk' wsort' wlen' wusable') l = watchSize s l ∧
      ∀ k < watchSize s l,
        wstk'[watchOff (pushWatchState s wvec' wstk' wsort' wlen' wusable') l + k]? =
          s.wstk[watchOff s l + k]?)
    (hlit : lit.toNat < 2 * c.mv)
    (hsz : watchSize (pushWatchState s wvec' wstk' wsort' wlen' wusable') lit.toNat =
      watchSize s lit.toNat + 2)
    (hpre : ∀ k < watchSize s lit.toNat,
      wstk'[watchOff (pushWatchState s wvec' wstk' wsort' wlen' wusable') lit.toNat + k]? =
        s.wstk[watchOff s lit.toNat + k]?)
    (hw0 : wstk'[watchOff (pushWatchState s wvec' wstk' wsort' wlen' wusable') lit.toNat +
      watchSize s lit.toNat]? = some w0)
    (hw1 : wstk'[watchOff (pushWatchState s wvec' wstk' wsort' wlen' wusable') lit.toNat +
      watchSize s lit.toNat + 1]? = some cref) :
    PlainCoreInv c F0 (pushWatchState s wvec' wstk' wsort' wlen' wusable') := by
  have hwat := plainWatchPush_preserves_watchesInv hinv.watches hlay (cnt := 2#32) (ok := true)
    (fun _ hr => hr) (fun h => by simp at h) (fun _ => ⟨h0_eq, hcref_lt, href⟩) hother
    (fun _ => ⟨hlit, Or.inr rfl, hsz, hpre, hw0, fun _ => hw1⟩) (fun h => by cases h)
  exact { hinv with
    lengths := hlen', arena := { hinv.arena with len_ok := hinv.arena.len_ok }, watches := hwat }

theorem phase3_push_prep {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    {p : Nat} (hinv : PlainCoreInv c F0 s) (hp : p ∈ arenaClauseRefs s)
    (hng : arenaClauseGarb s p = false) :
    let hwf := hinv.arena.refs_wf p hp
    have hbd : p + 3 + arenaClauseSize s p ≤ s.arena.length := by
      have := hinv.lengths.arena_len_le; have := hinv.lengths.arena_len_arr; omega
    let l0 := s.arena[p + 3]'(by omega)
    let l1 := s.arena[p + 4]'(by omega)
    l0.toNat < 2 * c.mv ∧ l1.toNat < 2 * c.mv ∧
    (l1 &&& 0x7FFFFFFF#32) = l1 ∧ (l0 &&& 0x7FFFFFFF#32) = l0 ∧
    l1 ≠ 0xFFFFFFFF#32 ∧ l0 ≠ 0xFFFFFFFF#32 ∧
    (l1 &&& 0x80000000#32) = 0#32 ∧ (l0 &&& 0x80000000#32) = 0#32 ∧
    p < 0x80000000 := by
  intro hwf hbd l0 l1
  have hmv := c.hmv; have har := c.harena; unfold dimacsBound at hmv har
  have hlen_a := hinv.lengths.arena_len_le
  have hl0_lt : l0.toNat < 2 * c.mv := by
    refine hinv.arena.lits_lt p hp hng _ ?_
    rw [mem_arenaClauseLits_iff hbd]; exact ⟨0, by omega, rfl⟩
  have hl1_lt : l1.toNat < 2 * c.mv := by
    refine hinv.arena.lits_lt p hp hng _ ?_
    rw [mem_arenaClauseLits_iff hbd]; exact ⟨1, by omega, rfl⟩
  have mask_eq : ∀ x : BitVec 32, x.toNat < 2 * c.mv →
      (x &&& 0x7FFFFFFF#32) = x ∧ x ≠ 0xFFFFFFFF#32 ∧ (x &&& 0x80000000#32) = 0#32 := by
    intro x hx
    refine ⟨?_, PlainReduceTactics.bv32_ne_allOnes_of_ult (by omega),
      PlainReduceTactics.bv32_and_msb_zero_of_ult (by omega)⟩
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨hl0m, hl0ne, hl0z⟩ := mask_eq l0 hl0_lt
  obtain ⟨hl1m, hl1ne, hl1z⟩ := mask_eq l1 hl1_lt
  exact ⟨hl0_lt, hl1_lt, hl1m, hl0m, hl1ne, hl0ne, hl1z, hl0z, by omega⟩

private def plainValsLvlRest (c : PlainCfg) (s : PlainState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.d_cur s.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆
  (array (t := i8) c.pMark s.mrk ⋆ array (t := i32) c.pReason s.rsns ⋆
   array (t := i32) c.pTrail s.trl ⋆ array (t := i32) c.pTrailPos s.trail_pos ⋆
   array (t := i32) c.pTmp s.tmp ⋆ array (t := i32) c.pWvec s.wvec ⋆
   array (t := i32) c.pArena s.arena ⋆ array (t := i32) c.pWstk s.wstk ⋆
   array (t := i32) c.pMinStk s.min_stk ⋆ array (t := i32) c.pMinClr s.min_clr) ⋆
  PlainHeurArrays c s.heur ⋆ c.pad

private theorem plainMem_swap_vals_lvl (c : PlainCfg) (s : PlainState) :
    PlainMem c s = (array (t := i8) c.pVals s.vals ⋆ array (t := i32) c.pLevel s.lvl ⋆
      plainValsLvlRest c s) := by
  unfold PlainMem PlainCoreArrays plainValsLvlRest; ac_rfl

theorem sweep_call_lr {Γ : Env}
    (hLR : ∀ args m Q X, plainLitRankSpec args m Q X →
      Γ "plain_lit_rank" [i64, i64, i32] [i64] args m Q X)
    {c : PlainCfg} {s : PlainState} {R : Mem 64 → Prop} {m : Mem 64} {l : BitVec 32}
    (hlen : s.LengthsOk c) (hl : l.toNat < 2 * c.mv) (hm : (PlainMem c s ⋆ R) m)
    {rs : List Ty} {Q : Post rs} {X : XPost} {k : Tup Val [i64] → Expr Val Cont rs}
    (hk : ∀ r : BitVec 64, wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (.call (rs := rs) (as := [i64, i64, i32]) (bs := [i64])
      "plain_lit_rank" (Arg.var c.pVals, Arg.var c.pLevel, Arg.var l, ()) k) m := by
  rw [plainMem_swap_vals_lvl] at hm
  have hm' : (array (t := i8) c.pVals s.vals ⋆ array (t := i32) c.pLevel s.lvl ⋆
      (plainValsLvlRest c s ⋆ R)) m := sep_ac hm
  exact wp_call_of_spec _ _ (hLR (c.pVals, c.pLevel, l, ()) m _ X
    ⟨s.vals, s.lvl, _, by rw [hlen.vals_len]; exact hl,
      by rw [hlen.lvl_len]; omega, hm', hk⟩)

/-! ## 4. Shared state helpers for `plain_reduce` and `plain_sweep` -/

theorem level0_confl_unsat {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hinv : PlainCoreInv c F0 s) (hcl : s.cur_level = 0)
    {ctype cref c0 c1 : BitVec 64}
    (hc : (ctype = 1#64 ∧ c0.toNat < 2 * c.mv ∧ c1.toNat < 2 * c.mv ∧
      F0.EntailsClause (cnfClause [c0.toNat, c1.toNat]) ∧
      s.vals[c0.toNat]?.getD 0#8 = 0xFF#8 ∧ s.vals[c1.toNat]?.getD 0#8 = 0xFF#8) ∨
      (ctype = 2#64 ∧ cref.toNat ∈ arenaClauseRefs s ∧
        arenaClauseGarb s cref.toNat = false ∧
        ∀ l ∈ arenaClauseLits s cref.toNat, s.vals[l]?.getD 0#8 = 0xFF#8)) :
    F0.Unsat := by
  have htv := trailValsInv_of_core hinv
  refine unsat_of_entails_nil ?_
  rcases hc with ⟨_, h0, h1, hent, hf0, hf1⟩ | ⟨_, href, hng, hfal⟩
  · refine entails_of_mem_or_false hent fun l hl => Or.inr ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact level0_entails_neg_of_fals htv hcl h0 hf0
    · exact level0_entails_neg_of_fals htv hcl h1 hf1
  · refine entails_of_mem_or_false (hinv.arena.entails cref.toNat href hng) fun l hl => Or.inr ?_
    exact level0_entails_neg_of_fals htv hcl (hinv.arena.lits_lt cref.toNat href hng l hl)
      (hfal l hl)

theorem binWatchesOnly_skip_zero {c : PlainCfg} {F0 : CNF Nat} {s : PlainState} {l : Nat}
    (hb : BinWatchesOnly c F0 s l) (h0 : watchSize s l = 0) :
    BinWatchesOnly c F0 s (l + 1) :=
  ⟨hb.1, fun l' hl' hl'_mv k hk => by
    by_cases hll : l' = l
    · subst hll; omega
    · exact hb.2 l' (by omega) hl'_mv k hk⟩

theorem pr_with_unflushed {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (h : PlainCoreInv c F0 s) (u : BitVec 64) : PlainCoreInv c F0 { s with unflushed := u } :=
  { h with
    lengths := { h.lengths with vals_len := h.lengths.vals_len }
    arena := { h.arena with len_ok := h.arena.len_ok }
    watches := h.watches.with_wstk rfl rfl rfl rfl }

theorem pr_with_ag {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (h : PlainCoreInv c F0 s) (ag : BitVec 64) :
    PlainCoreInv c F0 { s with arena_garbage := ag } :=
  { h with
    lengths := { h.lengths with vals_len := h.lengths.vals_len }
    arena := { h.arena with len_ok := h.arena.len_ok }
    watches := h.watches.with_wstk rfl rfl rfl rfl }

theorem pr_with_reduce {c : PlainCfg} {h : PlainHeur}
    (hok : h.LengthsOk c) (r rl : BitVec 64) :
    ({ h with reductions := r, reduce_limit := rl } : PlainHeur).LengthsOk c :=
  { hok with }

theorem bv32_mask_sub_eq {mask sub x y : BitVec 32} (hm : (mask &&& sub) = sub)
    (h : (x &&& mask) = (y &&& mask)) : (x &&& sub) = (y &&& sub) := by
  calc x &&& sub = (x &&& mask) &&& sub := by rw [BitVec.and_assoc, hm]
    _ = (y &&& mask) &&& sub := by rw [h]
    _ = y &&& sub := by rw [BitVec.and_assoc, hm]

/-! ## 5. Sweep phase invariants and transition lemmas -/

@[expose] def SameSwPre (s0 s : PlainState) : Prop :=
  s.d_cur = s0.d_cur ∧ s.d_val = s0.d_val ∧ s.propagated = s0.propagated ∧
  s.cur_level = s0.cur_level ∧ s.fuel = s0.fuel ∧ s.probing = s0.probing ∧
  s.confl_type = s0.confl_type ∧ s.confl_ref = s0.confl_ref ∧
  s.confl_lit0 = s0.confl_lit0 ∧ s.confl_lit1 = s0.confl_lit1 ∧
  s.tmp_cnt = s0.tmp_cnt ∧ s.tmp_len = s0.tmp_len ∧
  s.min_clr_len = s0.min_clr_len ∧ s.min_clr_full = s0.min_clr_full ∧
  s.mrk = s0.mrk ∧ s.tmp = s0.tmp ∧ s.min_stk = s0.min_stk ∧ s.min_clr = s0.min_clr

theorem SameSwPre.eq {s0 s : PlainState} (h : SameSwPre s0 s) (hag : s.arena_garbage = 0#64) :
    { s0 with
      vals := s.vals, lvl := s.lvl, rsns := s.rsns, trl := s.trl,
      trail_pos := s.trail_pos, trail_end := s.trail_end, unflushed := s.unflushed,
      wvec := s.wvec, wstk := s.wstk, arena := s.arena, arena_len := s.arena_len,
      wlen := s.wlen, wusable := s.wusable, arena_garbage := 0#64,
      first_reducible := s.first_reducible, num_irred := s.num_irred,
      num_redundant := s.num_redundant, num_binary := s.num_binary,
      oom := s.oom, heur := s.heur } = s := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩
  cases s0; cases s; simp only at *
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 hag; rfl

@[expose] def SwP1Inv (c : PlainCfg) (F0 : CNF Nat) (s0 : PlainState) (l : Nat)
    (s : PlainState) : Prop :=
  l ≤ 2 * c.mv ∧ s.LengthsOk c ∧ SameSwPre s0 s ∧
  s.vals = s0.vals ∧ s.lvl = s0.lvl ∧ s.rsns = s0.rsns ∧ s.trl = s0.trl ∧
  s.trail_pos = s0.trail_pos ∧ s.trail_end = s0.trail_end ∧ s.unflushed = s0.unflushed ∧
  s.arena = s0.arena ∧ s.arena_len = s0.arena_len ∧ s.wlen = s0.wlen ∧ s.oom = s0.oom ∧
  s.heur.rel_trigger = s0.heur.rel_trigger ∧ BinWatchesOnly c F0 s l

@[expose] def SwP2Inv (c : PlainCfg) (F0 : CNF Nat) (s0 : PlainState)
    (src dst : Nat) (new_unit : Bool) (s : PlainState) : Prop :=
  s.LengthsOk c ∧ SameSwPre s0 s ∧ s.heur.rel_trigger = s0.heur.rel_trigger ∧
  s.arena_len = s0.arena_len ∧ s.arena_garbage = s0.arena_garbage ∧ s.oom = s0.oom ∧
  TrailValsInv c F0 s ∧ BinWatchesOnly c F0 s (2 * c.mv) ∧
  ArenaPrefixOk c F0 s0 s src dst ∧ RsnRelocInv s0 s src dst ∧
  s.cur_level = s0.cur_level ∧ s0.trail_end ≤ s.trail_end ∧
  (new_unit = true → s0.cur_level = 0 ∧ s0.trail_end < s.trail_end) ∧
  (0 < s0.cur_level →
    s.vals = s0.vals ∧ s.lvl = s0.lvl ∧ s.trl = s0.trl ∧
    s.trail_pos = s0.trail_pos ∧ s.trail_end = s0.trail_end)

@[expose] def SwP2ExitInv (c : PlainCfg) (F0 : CNF Nat) (s0 : PlainState)
    (dst : Nat) (unsat new_unit : Bool) (s : PlainState) : Prop :=
  s.LengthsOk c ∧ SameSwPre s0 s ∧ s.heur.rel_trigger = s0.heur.rel_trigger ∧
  dst ≤ s0.arena_len ∧ (∀ i < s.trail_end, (s.trl[i]?.getD 0#32).toNat < 2 * c.mv) ∧
  (unsat = true → s0.cur_level = 0 ∧ F0.Unsat) ∧
  (unsat = false → s.oom = 0#64 →
    TrailValsInv c F0 s ∧ BinWatchesOnly c F0 s (2 * c.mv) ∧
    ArenaPrefixOk c F0 s0 s s0.arena_len dst ∧ RsnRelocInv s0 s s0.arena_len dst ∧
    s.cur_level = s0.cur_level ∧
    (new_unit = true → s0.cur_level = 0 ∧ s0.trail_end < s.trail_end) ∧
    (0 < s0.cur_level →
      s.vals = s0.vals ∧ s.lvl = s0.lvl ∧ s.trl = s0.trl ∧
      s.trail_pos = s0.trail_pos ∧ s.trail_end = s0.trail_end))

private theorem arenaClausesInv_congr_arena {c : PlainCfg} {F0 : CNF Nat} {s1 s2 : PlainState}
    (hc : ArenaClausesInv c F0 s1) (ha : s2.arena = s1.arena) (hl : s2.arena_len = s1.arena_len) :
    ArenaClausesInv c F0 s2 := by
  refine ⟨hl ▸ hc.len_ok, ?_, ?_, ?_, ?_⟩
  · intro r hr
    simp only [arenaClauseRefs, arenaClauseSize, arenaNextOff, ha, hl] at hr ⊢
    exact hc.refs_wf r hr
  · intro r hr
    simp only [arenaClauseRefs, arenaHdr, ha, hl] at hr ⊢
    exact hc.no_shrk r hr
  · intro r hr hng l hl0
    simp only [arenaClauseRefs, arenaClauseGarb, arenaHdr, arenaClauseLits,
      arenaClauseSize, ha, hl] at hr hng hl0 ⊢
    exact hc.lits_lt r hr hng l hl0
  · intro r hr hng
    simp only [arenaClauseRefs, arenaClauseGarb, arenaHdr, arenaClauseLits,
      arenaClauseSize, ha, hl] at hr hng ⊢
    exact hc.entails r hr hng

theorem arenaPrefix_init_eq {c : PlainCfg} {F0 : CNF Nat} {s0 s : PlainState}
    (hinv0 : PlainCoreInv c F0 s0) (ha : s.arena = s0.arena) :
    ArenaPrefixOk c F0 s0 s 0 0 := by
  have h := arenaPrefix_init hinv0
  refine ⟨by rw [ha]; exact h.ar_len, h.dst_le_src, h.src_le_alen, h.src_ref,
    fun _ _ _ => by rw [ha], arenaClausesInv_congr_arena h.comp_arena ha rfl, fun r hr => ?_⟩
  unfold arenaClauseGarb arenaHdr; dsimp only; rw [ha]
  apply h.no_garb r
  unfold arenaClauseRefs; dsimp only; rw [← ha]; exact hr

theorem binWatchesOnly_repack {c : PlainCfg} {F0 : CNF Nat} {s s' : PlainState}
    (hb : BinWatchesOnly c F0 s (2 * c.mv)) (hwv : s'.wvec = s.wvec) (hws : s'.wstk = s.wstk)
    (hwl : s'.wlen = s.wlen) :
    BinWatchesOnly c F0 s' (2 * c.mv) :=
  binWatchesOnly_of_all_bin (hb.1.layout.with_wstk hwv hws hwl) fun l hl k hk => by
    unfold watchOff watchSize at *; rw [hwv, hws] at *; exact hb.2 l hl hl k hk

theorem arenaPrefix_congr_arena {c : PlainCfg} {F0 : CNF Nat} {s0 s s' : PlainState}
    {src dst : Nat} (hp : ArenaPrefixOk c F0 s0 s src dst) (ha : s'.arena = s.arena) :
    ArenaPrefixOk c F0 s0 s' src dst := by
  refine ⟨by rw [ha]; exact hp.ar_len, hp.dst_le_src, hp.src_le_alen, hp.src_ref,
    fun k hk1 hk2 => by rw [ha]; exact hp.suffix_eq k hk1 hk2,
    arenaClausesInv_congr_arena hp.comp_arena ha rfl, fun r hr => ?_⟩
  unfold arenaClauseGarb arenaHdr; dsimp only; rw [ha]
  apply hp.no_garb r
  unfold arenaClauseRefs; dsimp only; rw [← ha]; exact hr

theorem rsnReloc_congr_state {s0 s s' : PlainState} {src dst : Nat}
    (hrr : RsnRelocInv s0 s src dst) (ha : s'.arena = s.arena) (hr : s'.rsns = s.rsns) :
    RsnRelocInv s0 s' src dst := by
  refine ⟨hr ▸ hrr.1, fun hp v => hr ▸ hrr.2.1 hp v, fun hp idx hidx hne hmsb => ?_⟩
  have h := hrr.2.2 hp idx hidx hne hmsb
  have ha' : ({ s' with arena_len := dst } : PlainState).arena =
      ({ s with arena_len := dst } : PlainState).arena := ha
  try dsimp only at h ⊢
  rw [hr]
  by_cases hlt : (s0.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat < src
  · simp only [hlt, ↓reduceIte] at h ⊢
    refine ⟨h.1, h.2.1, h.2.2.1, ?_, ?_, ?_, ?_⟩
    · unfold arenaClauseRefs; dsimp only; rw [ha']; exact h.2.2.2.1
    · unfold arenaClauseGarb arenaHdr; dsimp only; rw [ha']; exact h.2.2.2.2.1
    · unfold arenaClauseLits arenaClauseSize; dsimp only; rw [ha']; exact h.2.2.2.2.2.1
    · unfold arenaClauseLits arenaClauseSize; dsimp only; rw [ha']; exact h.2.2.2.2.2.2
  · simp only [hlt, ↓reduceIte] at h ⊢; exact h

theorem swP2_body4_emit {c : PlainCfg} {F0 : CNF Nat} {s0 s : PlainState}
    {src dst new_sz : Nat} {ar_out : List (BitVec 32)} {hdr : BitVec 32}
    (hinv0 : PlainCoreInv c F0 s0) (hp : ArenaPrefixOk c F0 s0 s src dst)
    (hsrc_lt : src < s0.arena_len) (hge3 : 3 ≤ new_sz)
    (hle_old : new_sz ≤ arenaClauseSize s0 src) (har_len : ar_out.length = c.arena_cap)
    (hpre : ∀ k < dst, ar_out[k]? = s.arena[k]?)
    (hsuf : ∀ k, src + 3 + arenaClauseSize s0 src ≤ k → k < s0.arena_len →
      ar_out[k]? = s.arena[k]?)
    (hlits_lt : ∀ k < new_sz, (ar_out[dst + 3 + k]?.getD 0#32).toNat < 2 * c.mv)
    (hent : F0.EntailsClause (cnfClause (((ar_out.drop (dst + 3)).take new_sz).map BitVec.toNat)))
    (hng0 : (hdr &&& 0x00080000#32) = 0#32) :
    let hdr' := hdr &&& ~~~0x00A00000#32
    let ar1 := ((ar_out.set dst hdr').set (dst + 1) 2#32).set (dst + 2) (BitVec.ofNat 32 new_sz)
    let sc : PlainState := { s with arena_len := dst }
    let sc' : PlainState := { s with arena := ar1, arena_len := dst + 3 + new_sz }
    let nsrc := arenaNextOff s0.arena s0.arena_len src
    ar1.length = c.arena_cap ∧
    ArenaPrefixOk c F0 s0 { s with arena := ar1 } nsrc (dst + 3 + new_sz) ∧
    (ar1[dst + 2]?.getD 0#32).toNat = new_sz ∧
    (∀ k < new_sz, ar1[dst + 3 + k]? = ar_out[dst + 3 + k]?) ∧
    (∀ r ∈ arenaClauseRefs sc, r ∈ arenaClauseRefs sc' ∧
      arenaClauseGarb sc' r = arenaClauseGarb sc r ∧
      arenaClauseLits sc' r = arenaClauseLits sc r) ∧
    arenaClauseLits sc' dst = ((ar_out.drop (dst + 3)).take new_sz).map BitVec.toNat ∧
    dst ∈ arenaClauseRefs sc' ∧ arenaClauseGarb sc' dst = false := by
  intro hdr' ar1 sc sc' nsrc
  have hsrc_ref : src ∈ arenaClauseRefs s0 := hp.src_ref.resolve_left (by omega)
  have hwf0 := hinv0.arena.refs_wf src hsrc_ref
  have har := c.harena; unfold dimacsBound at har; have hlen_a := hinv0.lengths.arena_len_le
  have hds := hp.dst_le_src
  have hbd_dst : dst + 3 + new_sz ≤ c.arena_cap := by omega
  have h1_lt : dst < ar_out.length := by rw [har_len]; omega
  have h3_lt : dst + 2 < ((ar_out.set dst hdr').set (dst + 1) 2#32).length := by
    simp [har_len]; omega
  have har1_len : ar1.length = c.arena_cap := by simp [ar1, har_len]
  have har1_pre : ∀ k < dst, ar1[k]? = s.arena[k]? := fun k hk => by
    simp only [ar1]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]; exact hpre k hk
  have har1_suf : ∀ k, src + 3 + arenaClauseSize s0 src ≤ k → k < s0.arena_len →
      ar1[k]? = s.arena[k]? := fun k hk1 hk2 => by
    simp only [ar1]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]; exact hsuf k hk1 hk2
  have har1_0 : ar1[dst]? = some hdr' := by
    simp only [ar1]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self h1_lt]
  have har1_2 : ar1[dst + 2]? = some (BitVec.ofNat 32 new_sz) := by
    simp only [ar1]; rw [List.getElem?_set_self h3_lt]
  have har1_sz : (ar1[dst + 2]?.getD 0#32).toNat = new_sz := by
    rw [har1_2, Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcl := bv32_shrk_rsn_clear_props hdr
  have har1_shrk : (ar1[dst]?.getD 0#32 &&& 0x00800000#32) = 0#32 := by
    rw [har1_0, Option.getD_some]; exact hcl.1
  have har1_ng : (ar1[dst]?.getD 0#32 &&& 0x00080000#32) = 0#32 := by
    rw [har1_0, Option.getD_some, hcl.2.2]; exact hng0
  have har1_lits : ∀ k < new_sz, ar1[dst + 3 + k]? = ar_out[dst + 3 + k]? := fun k hk => by
    simp only [ar1]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
  have har1_lits_lt : ∀ k < new_sz, (ar1[dst + 3 + k]?.getD 0#32).toNat < 2 * c.mv := fun k hk => by
    rw [har1_lits k hk]; exact hlits_lt k hk
  have hlits_eq_pre : arenaClauseLits sc' dst =
      ((ar_out.drop (dst + 3)).take new_sz).map BitVec.toNat := by
    have hsz1 : arenaClauseSize sc' dst = new_sz := by unfold arenaClauseSize sc'; exact har1_sz
    unfold arenaClauseLits; rw [hsz1]; dsimp only [sc']
    apply congrArg (List.map BitVec.toNat)
    apply List.ext_getElem
    · simp [Nat.min_eq_left (show new_sz ≤ ar1.length - (dst + 3) by omega),
        Nat.min_eq_left (show new_sz ≤ ar_out.length - (dst + 3) by omega)]
    · intro k hk1 hk2
      simp only [List.length_take, List.length_drop, Nat.lt_min] at hk1 hk2
      simp only [List.getElem_take, List.getElem_drop]
      have hke := har1_lits k hk1.1
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hke
      exact Option.some.inj hke
  have hent' : F0.EntailsClause (cnfClause (arenaClauseLits { s with arena := ar1 } dst)) := by
    have heq : arenaClauseLits { s with arena := ar1 } dst = arenaClauseLits sc' dst := rfl
    rw [heq, hlits_eq_pre]; exact hent
  obtain ⟨hp', hrefs, hrel⟩ := arenaPrefix_append_props hinv0 hp hsrc_lt hge3 hle_old har1_len
    har1_pre har1_suf har1_shrk har1_ng har1_sz har1_lits_lt hent'
  have hdst_in : dst ∈ arenaClauseRefs sc' := by rw [hrefs]; simp
  refine ⟨har1_len, hp', har1_sz, har1_lits, fun r hr => ?_, hlits_eq_pre, hdst_in,
    hp'.no_garb dst hdst_in⟩
  exact ⟨by rw [hrefs]; exact List.mem_append_left _ hr, hrel r hr⟩

end PlainReduceHelpers

end

end LeanQbe.T.Examples.Kissat.Plain
