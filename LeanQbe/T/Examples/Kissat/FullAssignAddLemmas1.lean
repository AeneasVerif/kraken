module

public import LeanQbe.T.Examples.Kissat.Full1
public import LeanQbe.T.Examples.Kissat.FullInv1
public import LeanQbe.T.Examples.Kissat.FullInv2
public import LeanQbe.T.Examples.Kissat.FullArena
public import LeanQbe.T.Logic.C0Step
public meta import Lean.Elab.Tactic
public meta import LeanQbe.T.Logic.C0Step
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Watch-Push, Assign & Add-Clause Proofs — Part 1 (`Stage 4`)

Provides:
1. Strictly scoped `FullAssignAddTactics` (extra `FullMem` load/store & `bv_c0` lemmas + join/split
   automation, zero global attributes).
2. Local `namespace FullAssignAddSpecs` matching `FullSpec1`/`FullSpec2` 1:1 for the 4 functions
   (`full_watch_push`, `full_assign_lvl`, `full_assign`, `full_add_clause`) and their callees
   (`full_wstack_defrag`, `full_alloc_cl`), plus witness/watch/garbage preservation helpers.
3. Parametric `(Γ : Env)` `Func.wp` proofs for `full_assign_lvl` and `full_assign`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Strictly Scoped `FullAssignAddTactics` -/

namespace FullAssignAddTactics

theorem bv32_lshr1 (x : BitVec 32) : (x >>> (1 : Nat)).toNat = x.toNat / 2 := bv32_lshr_1 x

theorem bv64_add_no_ovf {a b : BitVec 64} (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt h

theorem bv64_add1_no_ovf {a : BitVec 64} (h : a.toNat + 1 < 2 ^ 64) :
    (a + 1).toNat = a.toNat + 1 := bv64_add_no_ovf (by simpa using h)

theorem bv64_add1_toNat {n : Nat} (h : n + 1 < 2 ^ 64) :
    (BitVec.ofNat 64 n + 1).toNat = n + 1 := by
  rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add, bv64_ofNat_toNat h]

theorem bv64_sub_ofNat {a b : Nat} (hle : b ≤ a) (ha : a < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b).toNat = a - b := by
  have h1 := bv64_ofNat_toNat (n := a) ha
  have h2 := bv64_ofNat_toNat (n := b) (by omega)
  bv_omega

theorem bv64_setWidth32_ofNat (x : Nat) :
    BitVec.setWidth 32 (BitVec.ofNat 64 x) = BitVec.ofNat 32 x :=
  BitVec.eq_of_toNat_eq (by
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    exact Nat.mod_mod_of_dvd _ (by decide))

theorem bv32_trunc_ofNat {n : Nat} (h : n < 2 ^ 32) :
    ((BitVec.ofNat 64 n).setWidth 32).toNat = n := by
  rw [BitVec.toNat_setWidth, bv64_ofNat_toNat (by omega)]; exact Nat.mod_eq_of_lt h

theorem bv32_trunc_add {a : BitVec 64} {b : Val i32} (h : a.toNat + b.toNat < 2 ^ 32) :
    ((a + b.setWidth 64).setWidth 32).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_add, zext_toNat _ (by decide),
    Nat.mod_eq_of_lt (by omega : a.toNat + b.toNat < 2 ^ 64), Nat.mod_eq_of_lt h]

theorem bv64_eq_zero_of_not_pos {x : BitVec 64} (h : ¬ (0 < x.toNat)) : x = 0#64 :=
  BitVec.eq_of_toNat_eq (by simp; omega)

theorem bv64_fit_of_not_ugt {wcap wlen : Nat} {x : BitVec 64}
    (hle : wlen ≤ wcap) (hcap : wcap < 2 ^ 64)
    (h : ¬ ((BitVec.ofNat 64 wcap - BitVec.ofNat 64 wlen).toNat < x.toNat)) :
    x.toNat ≤ wcap - wlen := by
  have := bv64_sub_ofNat hle hcap; omega

theorem bv32_eq_nat {x : Val i32} (n : Nat) (hn : n < 2 ^ 32)
    (h : x = BitVec.ofNat 32 n) : x.toNat = n := by
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at this; exact this

theorem bv32_ne_nat {x : Val i32} (n : Nat) (hn : n < 2 ^ 32)
    (h : x ≠ BitVec.ofNat 32 n) : x.toNat ≠ n := fun heq =>
  h (BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]; exact heq))

theorem bv32_beq_nat_eq {n : Nat} {x : BitVec 32} (hn : n < 2 ^ 32) :
    (x == BitVec.ofNat 32 n) = decide (x.toNat = n) := by
  by_cases h : x.toNat = n
  · have hx : x = BitVec.ofNat 32 n :=
      BitVec.eq_of_toNat_eq (by rw [bv32_ofNat_toNat hn]; exact h)
    simp [hx, bv32_ofNat_toNat hn]
  · have hx : x ≠ BitVec.ofNat 32 n := fun he =>
      h (by simpa [bv32_ofNat_toNat hn] using congrArg BitVec.toNat he)
    simp [h, hx]

theorem bv64_lit2 {lit : Val i32} :
    (lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * lit.toNat := by
  rw [BitVec.toNat_shiftLeft, zext_toNat _ (by decide)]; simp [Nat.shiftLeft_eq]; omega

theorem bv64_lit2p1 {lit : Val i32} :
    ((lit.setWidth 64 <<< (1 : Nat)) + 1).toNat = 2 * lit.toNat + 1 := by
  rw [BitVec.toNat_add, bv64_lit2]; simp; omega

theorem bv32_tag_bin_flag (x : BitVec 32) :
    (((x &&& 0x7FFFFFFF#32) ||| 0x80000000#32) &&& 0x80000000#32) ≠ 0#32 := by
  intro he; have h31 := congrArg (fun v : BitVec 32 => v.getLsbD 31) he; simp at h31

theorem bv32_tag_bin_mask {x : BitVec 32} (hx : x.toNat < 2 ^ 30) :
    (((x &&& 0x7FFFFFFF#32) ||| 0x80000000#32) &&& 0x7FFFFFFF#32) = x := by
  have hm : (x &&& 0x7FFFFFFF#32) = x := BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_and, show (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)])
  rw [← hm]; apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or]
  have h1 : !((0x80000000#32).getLsbD i && (0x7FFFFFFF#32).getLsbD i) := by
    revert i hi; decide
  cases h8 : (0x80000000#32).getLsbD i <;> simp_all

theorem bv32_tag_bin_ne_sent {x : BitVec 32} (hx : x.toNat < 2 ^ 30) :
    ((x &&& 0x7FFFFFFF#32) ||| 0x80000000#32) ≠ 0xFFFFFFFF#32 := by
  intro he; have h30 := congrArg (fun v : BitVec 32 => v.getLsbD 30) he
  have hx30 : x.getLsbD 30 = false := by
    rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat]
    exact Nat.testBit_lt_two_pow hx
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, hx30, Bool.false_and] at h30
  revert h30; decide

theorem bv32_mask_flag0 (x : BitVec 32) :
    ((x &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32 := by
  rw [BitVec.and_assoc, show (0x7FFFFFFF#32 &&& 0x80000000#32) = 0#32 by decide, BitVec.and_zero]

theorem bv32_mask_ne_sent (x : BitVec 32) : (x &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32 := by
  intro he; have h31 := congrArg (fun v : BitVec 32 => v.getLsbD 31) he; simp at h31

theorem bv32_or_garb_noshrk {x : BitVec 32} (hx : (x &&& 0x00800000#32) = 0#32) :
    ((x ||| 0x00080000#32) &&& 0x00800000#32) = 0#32 := by
  rw [← hx]; apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or]
  have h1 : !((0x00080000#32).getLsbD i && (0x00800000#32).getLsbD i) := by
    revert i hi; decide
  cases h8 : (0x00080000#32).getLsbD i <;> simp_all

theorem bv32_or_garb_nz (x : BitVec 32) :
    ((x ||| 0x00080000#32) &&& 0x00080000#32) ≠ 0#32 := by
  intro he; have h19 := congrArg (fun v : BitVec 32 => v.getLsbD 19) he; simp at h19

theorem p_strip_wp {Γ rs Q X e m} (h : wp (rs := rs) Γ Q X e m) : wp Γ Q X e m := h
theorem p_strip_fwp {as rs Γ f args m Q X}
    (h : Func.wp (as := as) (rs := rs) Γ f args m Q X) : Func.wp Γ f args m Q X := h
theorem p_strip_le_wp {a b : Nat} {P : Prop} (h : a ≤ b) (hp : P) : a ≤ b ∧ P := ⟨h, hp⟩

scoped macro "faa_lets" : tactic => `(tactic| (
  (try (first | refine p_strip_fwp ?_ | refine p_strip_wp ?_))
  (try c0_let_simp); repeat (refine p_strip_le_wp (by decide) ?_; try c0_let_simp)))

theorem wp_head_jnz_iff {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {c : Arg Val .bool} {b : Bool} {t e : Expr Val Cont rs} (hc : c.val = b)
    (h : (b = true → wp Γ Q X t m) ∧ (b = false → wp Γ Q X e m)) :
    wp Γ Q X (.jnz c t e) m := by subst hc; rw [wp_jnz]; exact h

section BvC0Extras
@[scoped bv_c0] theorem bv32_toNat_0 : (0 : BitVec 32).toNat = 0 := rfl
@[scoped bv_c0] theorem bv32_toNat_1 : (1 : BitVec 32).toNat = 1 := rfl
@[scoped bv_c0] theorem bv64_toNat_0 : (0 : BitVec 64).toNat = 0 := rfl
@[scoped bv_c0] theorem bv64_toNat_1 : (1 : BitVec 64).toNat = 1 := rfl
@[scoped bv_c0] theorem bv_c0_xor1 (n : Nat) : n ^^^ 1 = n + 1 - 2 * (n % 2) := by
  have h := litNeg_eq n; unfold litNeg at h; rw [h]; split <;> omega
@[scoped bv_c0] theorem fcfg_maxv_mod (c : FullCfg) : c.max_vars % 2 ^ 64 = c.max_vars := by
  have := c.hmaxv; unfold dimacsBound at this; exact Nat.mod_eq_of_lt (by omega)
@[scoped bv_c0] theorem fcfg_arena_cap_mod (c : FullCfg) :
    c.arena_cap % 2 ^ 64 = c.arena_cap := by
  have := c.harena; unfold dimacsBound at this; exact Nat.mod_eq_of_lt (by omega)
@[scoped bv_c0] theorem fcfg_wcap_mod (c : FullCfg) : c.wcap % 2 ^ 64 = c.wcap := by
  have := c.hwcap; unfold dimacsBound at this; exact Nat.mod_eq_of_lt (by omega)
@[scoped bv_c0] theorem bv32_toNat_mod64 (x : BitVec 32) : x.toNat % 2 ^ 64 = x.toNat :=
  Nat.mod_eq_of_lt (by have := x.isLt; omega)
@[scoped bv_c0] theorem bv32_div2_mod64 (x : BitVec 32) : (x.toNat / 2) % 2 ^ 64 = x.toNat / 2 :=
  Nat.mod_eq_of_lt (by have := x.isLt; omega)
@[scoped bv_c0] theorem bv64_toNat_mod64 (x : BitVec 64) : x.toNat % 2 ^ 64 = x.toNat :=
  Nat.mod_eq_of_lt x.isLt
attribute [scoped bv_c0] BitVec.toNat_ushiftRight BitVec.toNat_shiftLeft BitVec.toNat_xor
  BitVec.toNat_and Nat.shiftLeft_eq Nat.shiftRight_eq_div_pow List.length_set
  List.length_replicate
attribute [scoped bv_c0 high] LeanQbe.T.bv_c0_zext32_64 LeanQbe.T.bv_c0_zext8_64
  LeanQbe.T.bv_c0_zext8_32
@[scoped c0_load] theorem c0_load_full_tmp0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 0 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pTmp + 0#64) = some s.core.tmp[0] :=
  FullArenaTactics.load_full_tmp (i := 0) hi hm
@[scoped c0_load] theorem c0_load_full_tmp1 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 1 < s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pTmp + 4#64) = some s.core.tmp[1] :=
  FullArenaTactics.load_full_tmp (i := 1) hi hm
@[scoped c0_load] theorem c0_load_full_arena0 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop}
    {m : Mem 64} (hi : 0 < s.core.arena.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 c.pArena = some s.core.arena[0] := by
  simpa using FullArenaTactics.load_full_arena (i := 0) hi hm
@[scoped c0_store] theorem c0_store_full_wstk_zero {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.core.wstk.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pWstk + 0#64) ∧
      (FullMem c { s with core := { s.core with wstk := s.core.wstk.set 0 v } } ⋆ R)
        (storeMem m i32 (c.pWstk + 0#64) v) :=
  FullArenaTactics.store_full_wstk (i := 0) v hi hm
end BvC0Extras

open Lean Elab Tactic in
/-- Unwrap `MData` wrappers so `C0Step.stepOnce` recognizes `wp`/`Func.wp`. -/
private meta def unwrapWpMData (g : MVarId) : MetaM MVarId := do
  let ty0 ← instantiateMVars (← g.getType)
  let ty1 := ty0.consumeMData
  let ty2 :=
    if ty1.isAppOf ``LeanQbe.T.wp && ty1.getAppNumArgs == 6 then
      let e := ty1.getArg! 4
      let e' := e.consumeMData.headBeta
      if e' != e then mkAppN ty1.getAppFn (ty1.getAppArgs.set! 4 e') else ty1
    else if ty1.isAppOf ``LeanQbe.T.Func.wp && ty1.getAppNumArgs ≥ 4 then
      let f := ty1.getArg! 3
      let f' := f.consumeMData.headBeta
      if f' != f then mkAppN ty1.getAppFn (ty1.getAppArgs.set! 3 f') else ty1
    else ty1
  if ty2 != ty0 then g.replaceTargetDefEq ty2 else return g

open Lean Elab Tactic in
/-- Step all goals like `c0_steps`, unwrapping `MData` and halting on `Expr.group`. -/
scoped elab "c0_to_group" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let mut out : Array MVarId := #[]
    for g in ← getUnsolvedGoals do
      if ← g.isAssigned then continue
      let g ← unwrapWpMData g
      setGoals [g]
      let ty ← instantiateMVars (← g.getType)
      if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
          ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Expr.group then
        out := out.push g
      else if ← LeanQbe.T.C0Step.stepOnce then
        go (fuel - 1); out := out ++ (← getUnsolvedGoals)
      else out := out.push g
    setGoals out.toList
  go 500

open Lean Elab Tactic in
/-- Step straight-line ops on the main goal until the next `Expr.jnz`, then split it once. -/
scoped elab "c0_split" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let gs ← getUnsolvedGoals
    let some g0 := gs.head? | return
    let g ← unwrapWpMData g0
    setGoals (g :: gs.tail!)
    let ty ← instantiateMVars (← g.getType)
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Expr.jnz then
      let _ ← LeanQbe.T.C0Step.stepOnce; return
    if ← LeanQbe.T.C0Step.stepOnce then go (fuel - 1)
  go 100

open Lean Elab Tactic in
/-- Step all goals like `c0_steps`, unwrapping `MData` wrappers before each step. -/
scoped elab "c0_usteps" : tactic => do
  let rec go (fuel : Nat) : TacticM Unit := do
    if fuel = 0 then return
    let mut out : Array MVarId := #[]
    for g in ← getUnsolvedGoals do
      if ← g.isAssigned then continue
      let g ← unwrapWpMData g
      setGoals [g]
      if ← LeanQbe.T.C0Step.stepOnce then
        go (fuel - 1); out := out ++ (← getUnsolvedGoals)
      else out := out.push g
    setGoals out.toList
  go 500

open Lean Elab Tactic in
scoped elab "faa_unmdata" : tactic => do
  let mut out : Array MVarId := #[]
  for g in ← getUnsolvedGoals do
    if ← g.isAssigned then continue
    out := out.push (← unwrapWpMData g)
  setGoals out.toList

scoped elab "faa_head_steps" : tactic => do
  let isBranchHead (ty : Lean.Expr) : Bool :=
    let ty := ty.consumeMData.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 then
      let e := (ty.getArg! 4).consumeMData.headBeta
      e.isAppOf ``LeanQbe.T.Expr.jnz || e.isAppOf ``LeanQbe.T.Expr.group
    else false
  for _ in [:450] do
    let gs ← Lean.Elab.Tactic.getUnsolvedGoals
    let some g := gs.head? | break
    let g ← unwrapWpMData g
    if isBranchHead (← Lean.instantiateMVars (← g.getType)) then
      Lean.Elab.Tactic.setGoals (g :: gs.tail!); break
    Lean.Elab.Tactic.setGoals [g]
    let s ← Lean.Elab.Tactic.saveState
    let ok ← try stepOnce catch _ => s.restore; pure false
    Lean.Elab.Tactic.setGoals ((← Lean.Elab.Tactic.getUnsolvedGoals) ++ gs.tail!)
    if !ok then break

scoped macro "faa_clean" : tactic => `(tactic| simp only [Nat.reduceLeDiff, Nat.le_refl, true_and,
  and_true, Bool.false_or, Bool.or_false, Bool.true_and, Bool.and_true, Bool.not_true,
  Bool.not_false, decide_eq_true_eq, decide_eq_false_iff_not])

scoped macro "faa_steps" : tactic => `(tactic| (
  all_goals try faa_unmdata; c0_usteps
  repeat (any_goals faa_clean; all_goals try faa_unmdata; c0_usteps)))

end FullAssignAddTactics

/-! ## 2. Exact Target `FullSpec1`/`FullSpec2` Contracts & Witness Helpers (`FullAssignAddSpecs`) -/

namespace FullAssignAddSpecs

def FullArenaVarsNodup (s : FullState) : Prop :=
  ∀ r ∈ fullArenaClauseRefs s, fullArenaClauseGarb s r = false →
    ((fullArenaClauseLits s r).map (· / 2)).Nodup

theorem watchSlice_relocate {F F' : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} (hF : (cnfOfClauses F').Entails (cnfOfClauses F))
    (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : WatchSliceOk F k lit p rem) : WatchSliceOk F' k' lit p' rem := by
  induction h generalizing p' with
  | empty => exact .empty
  | @bin p rem w0 hp hflag hne hlt hent _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hflag hne (by omega)
      (CNF.entails_clause_trans hF hent)
      (ih (p' := p' + 1) fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 1) (by omega))
  | @large p rem w0 cref hp hp1 hflag hlt href _ ih =>
    refine .large (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hflag hlt (hsub _ href)
      (ih (p' := p' + 2) fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 2) (by omega))

theorem denseWatchSlice_relocate {F F' : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} (hF : (cnfOfClauses F').Entails (cnfOfClauses F))
    (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : DenseWatchSliceOk F k lit p rem) : DenseWatchSliceOk F' k' lit p' rem := by
  induction h generalizing p' with
  | empty => exact .empty
  | @bin p rem w0 hp hflag hne hlt hent _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hflag hne (by omega)
      (CNF.entails_clause_trans hF hent)
      (ih (p' := p' + 1) fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 1) (by omega))
  | @occ p rem w0 cref hp hp1 hflag hsz hlt href _ ih =>
    refine .occ (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hflag hsz hlt (hsub _ href)
      (ih (p' := p' + 2) fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 2) (by omega))

theorem watchSlice_append_bin {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} {w0 : BitVec 32} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : WatchSliceOk F_cur k lit p rem)
    (hw0 : k'.wstk[p' + rem]? = some w0)
    (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) (hne : w0 ≠ 0xFFFFFFFF#32)
    (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k'.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat])) :
    WatchSliceOk F_cur k' lit p' (rem + 1) := by
  induction h generalizing p' with
  | empty => exact .bin (by simpa using hw0) hflag hne hlt hent .empty
  | @bin p rem w hp hf hn hl he _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn (by omega) he ?_
    exact ih (p' := p' + 1)
      (fun idx hi => by simpa [show p' + 1 + idx = p' + (idx + 1) by omega,
        show p + 1 + idx = p + (idx + 1) by omega] using hwstk (idx + 1) (by omega))
      (by simpa [show p' + 1 + rem = p' + (rem + 1) by omega] using hw0)
  | @large p rem w cref hp hp1 hf hl href _ ih =>
    refine .large (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hf hl (hsub _ href) ?_
    exact ih (p' := p' + 2)
      (fun idx hi => by simpa [show p' + 2 + idx = p' + (idx + 2) by omega,
        show p + 2 + idx = p + (idx + 2) by omega] using hwstk (idx + 2) (by omega))
      (by simpa [show p' + 2 + rem = p' + (rem + 2) by omega] using hw0)

theorem watchSlice_append_large {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} {w0 cref : BitVec 32} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : WatchSliceOk F_cur k lit p rem)
    (hw0 : k'.wstk[p' + rem]? = some w0) (hw1 : k'.wstk[p' + rem + 1]? = some cref)
    (hflag : (w0 &&& 0x80000000#32) = 0#32) (hlt : cref.toNat < 0x80000000)
    (href : cref.toNat ∈ fullArenaClauseRefsCore k') :
    WatchSliceOk F_cur k' lit p' (rem + 2) := by
  induction h generalizing p' with
  | empty => exact .large (by simpa using hw0) (by simpa using hw1) hflag hlt href .empty
  | @bin p rem w hp hf hn hl he _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn (by omega) he ?_
    exact ih (p' := p' + 1)
      (fun idx hi => by simpa [show p' + 1 + idx = p' + (idx + 1) by omega,
        show p + 1 + idx = p + (idx + 1) by omega] using hwstk (idx + 1) (by omega))
      (by simpa [show p' + 1 + rem = p' + (rem + 1) by omega] using hw0)
      (by simpa [show p' + 1 + rem + 1 = p' + (rem + 1) + 1 by omega] using hw1)
  | @large p rem w cr hp hp1 hf hl hr _ ih =>
    refine .large (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hf hl (hsub _ hr) ?_
    exact ih (p' := p' + 2)
      (fun idx hi => by simpa [show p' + 2 + idx = p' + (idx + 2) by omega,
        show p + 2 + idx = p + (idx + 2) by omega] using hwstk (idx + 2) (by omega))
      (by simpa [show p' + 2 + rem = p' + (rem + 2) by omega] using hw0)
      (by simpa [show p' + 2 + rem + 1 = p' + (rem + 2) + 1 by omega] using hw1)

theorem denseWatchSlice_append_bin {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} {w0 : BitVec 32} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : DenseWatchSliceOk F_cur k lit p rem)
    (hw0 : k'.wstk[p' + rem]? = some w0)
    (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) (hne : w0 ≠ 0xFFFFFFFF#32)
    (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k'.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat])) :
    DenseWatchSliceOk F_cur k' lit p' (rem + 1) := by
  induction h generalizing p' with
  | empty => exact .bin (by simpa using hw0) hflag hne hlt hent .empty
  | @bin p rem w hp hf hn hl he _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn (by omega) he ?_
    exact ih (p' := p' + 1)
      (fun idx hi => by simpa [show p' + 1 + idx = p' + (idx + 1) by omega,
        show p + 1 + idx = p + (idx + 1) by omega] using hwstk (idx + 1) (by omega))
      (by simpa [show p' + 1 + rem = p' + (rem + 1) by omega] using hw0)
  | @occ p rem w cref hp hp1 hf hsz hl href _ ih =>
    refine .occ (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hf hsz hl (hsub _ href) ?_
    exact ih (p' := p' + 2)
      (fun idx hi => by simpa [show p' + 2 + idx = p' + (idx + 2) by omega,
        show p + 2 + idx = p + (idx + 2) by omega] using hwstk (idx + 2) (by omega))
      (by simpa [show p' + 2 + rem = p' + (rem + 2) by omega] using hw0)

theorem denseWatchSlice_append_occ {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} {w0 cref : BitVec 32} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : DenseWatchSliceOk F_cur k lit p rem)
    (hw0 : k'.wstk[p' + rem]? = some w0) (hw1 : k'.wstk[p' + rem + 1]? = some cref)
    (hflag : (w0 &&& 0x80000000#32) = 0#32) (hsz : 3 ≤ w0.toNat) (hlt : cref.toNat < 0x80000000)
    (href : cref.toNat ∈ fullArenaClauseRefsCore k') :
    DenseWatchSliceOk F_cur k' lit p' (rem + 2) := by
  induction h generalizing p' with
  | empty => exact .occ (by simpa using hw0) (by simpa using hw1) hflag hsz hlt href .empty
  | @bin p rem w hp hf hn hl he _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn (by omega) he ?_
    exact ih (p' := p' + 1)
      (fun idx hi => by simpa [show p' + 1 + idx = p' + (idx + 1) by omega,
        show p + 1 + idx = p + (idx + 1) by omega] using hwstk (idx + 1) (by omega))
      (by simpa [show p' + 1 + rem = p' + (rem + 1) by omega] using hw0)
      (by simpa [show p' + 1 + rem + 1 = p' + (rem + 1) + 1 by omega] using hw1)
  | @occ p rem w cr hp hp1 hf hsz0 hl hr _ ih =>
    refine .occ (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hf hsz0 hl (hsub _ hr) ?_
    exact ih (p' := p' + 2)
      (fun idx hi => by simpa [show p' + 2 + idx = p' + (idx + 2) by omega,
        show p + 2 + idx = p + (idx + 2) by omega] using hwstk (idx + 2) (by omega))
      (by simpa [show p' + 2 + rem = p' + (rem + 2) by omega] using hw0)
      (by simpa [show p' + 2 + rem + 1 = p' + (rem + 2) + 1 by omega] using hw1)

theorem fullWatchPush_preserves_modeWatchesInv {F_cur : List (List Nat)}
    {k k' : FullCoreState} {lit w0 w1 cnt : BitVec 32} {ok : Bool}
    (hw : ModeWatchesInv F_cur k) (hlay : WatchStackLayout k')
    (hvars : k'.cur_vars = k.cur_vars) (hdm : k'.dense_mode = k.dense_mode)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hbin : cnt.toNat = 1 →
      (w0 &&& 0x80000000#32) ≠ 0#32 ∧ w0 ≠ 0xFFFFFFFF#32 ∧
      (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k'.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat, (w0 &&& 0x7FFFFFFF#32).toNat]))
    (hlarge : cnt.toNat = 2 →
      (w0 &&& 0x80000000#32) = 0#32 ∧ (k.dense_mode ≠ 0#64 → 3 ≤ w0.toNat) ∧
      w1.toNat < 0x80000000 ∧ w1.toNat ∈ fullArenaClauseRefsCore k')
    (hother : ∀ l < 2 * k.cur_vars, l ≠ lit.toNat →
      fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ idx < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k' l + idx]? = k.wstk[fullWatchOffCore k l + idx]?)
    (hok_true : ok = true →
      lit.toNat < 2 * k.cur_vars ∧ (cnt.toNat = 1 ∨ cnt.toNat = 2) ∧
      fullWatchSizeCore k' lit.toNat = fullWatchSizeCore k lit.toNat + cnt.toNat ∧
      (∀ idx < fullWatchSizeCore k lit.toNat,
        k'.wstk[fullWatchOffCore k' lit.toNat + idx]? =
          k.wstk[fullWatchOffCore k lit.toNat + idx]?) ∧
      k'.wstk[fullWatchOffCore k' lit.toNat + fullWatchSizeCore k lit.toNat]? = some w0 ∧
      (cnt.toNat = 2 →
        k'.wstk[fullWatchOffCore k' lit.toNat + fullWatchSizeCore k lit.toNat + 1]? = some w1))
    (hok_false : ok = false → lit.toNat < 2 * k.cur_vars →
      fullWatchSizeCore k' lit.toNat = fullWatchSizeCore k lit.toNat ∧
      ∀ idx < fullWatchSizeCore k lit.toNat,
        k'.wstk[fullWatchOffCore k' lit.toNat + idx]? =
          k.wstk[fullWatchOffCore k lit.toNat + idx]?) :
    ModeWatchesInv F_cur k' := by
  have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ h => h
  unfold ModeWatchesInv at hw ⊢; rw [hdm]
  by_cases hc : k.dense_mode = 0#64 <;> simp only [hc, ↓reduceIte] at hw ⊢
  · refine ⟨hlay, fun l hl => ?_⟩
    by_cases hle : l = lit.toNat
    · subst hle; cases ok with
      | false =>
        obtain ⟨hsz, hslice⟩ := hok_false rfl (hvars ▸ hl); rw [hsz]
        exact watchSlice_relocate hrefl (by omega) hsub hslice (hw.slices _ (hvars ▸ hl))
      | true =>
        obtain ⟨_, hcnt, hsz, hpre, hw0, hw1⟩ := hok_true rfl; rw [hsz]
        rcases hcnt with hc1 | hc2
        · rw [hc1]; obtain ⟨hf, hn, hlt, hent⟩ := hbin hc1
          exact watchSlice_append_bin (by omega) hsub hpre (hw.slices _ (hvars ▸ hl))
            hw0 hf hn hlt hent
        · rw [hc2]; obtain ⟨hf, _, hlt, href⟩ := hlarge hc2
          exact watchSlice_append_large (by omega) hsub hpre (hw.slices _ (hvars ▸ hl))
            hw0 (hw1 hc2) hf hlt href
    · obtain ⟨hsz, hslice⟩ := hother l (hvars ▸ hl) hle; rw [hsz]
      exact watchSlice_relocate hrefl (by omega) hsub hslice (hw.slices l (hvars ▸ hl))
  · refine ⟨hlay, fun l hl => ?_⟩
    by_cases hle : l = lit.toNat
    · subst hle; cases ok with
      | false =>
        obtain ⟨hsz, hslice⟩ := hok_false rfl (hvars ▸ hl); rw [hsz]
        exact denseWatchSlice_relocate hrefl (by omega) hsub hslice (hw.slices _ (hvars ▸ hl))
      | true =>
        obtain ⟨_, hcnt, hsz, hpre, hw0, hw1⟩ := hok_true rfl; rw [hsz]
        rcases hcnt with hc1 | hc2
        · rw [hc1]; obtain ⟨hf, hn, hlt, hent⟩ := hbin hc1
          exact denseWatchSlice_append_bin (by omega) hsub hpre (hw.slices _ (hvars ▸ hl))
            hw0 hf hn hlt hent
        · rw [hc2]; obtain ⟨hf, h3, hlt, href⟩ := hlarge hc2
          exact denseWatchSlice_append_occ (by omega) hsub hpre (hw.slices _ (hvars ▸ hl))
            hw0 (hw1 hc2) hf (h3 hc) hlt href
    · obtain ⟨hsz, hslice⟩ := hother l (hvars ▸ hl) hle; rw [hsz]
      exact denseWatchSlice_relocate hrefl (by omega) hsub hslice (hw.slices l (hvars ▸ hl))

theorem watchUpdate_preserves_witness {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    {wvec' wstk' : List (BitVec 32)} {wlen' : Nat} {wusable' nb' oom' : BitVec 64}
    (hwat : ModeWatchesInv F_cur
      { k with wvec := wvec', wstk := wstk', wlen := wlen',
               wusable := wusable', num_binary := nb', oom := oom' }) :
    FullWitnessInv c F0 F_cur
      { k with wvec := wvec', wstk := wstk', wlen := wlen',
               wusable := wusable', num_binary := nb', oom := oom' } :=
  { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }, watches := hwat }

theorem addEntailedClause_preserves_witness {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState}
    (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core) {len : Nat}
    {arena' wvec' wstk' : List (BitVec 32)} {wlen' : Nat}
    {wusable' fred' ni' nr' : BitVec 64} {scratch' : FullScratch}
    (hlen' : ({ s with
      core := { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len,
                            wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable',
                            first_reducible := fred', num_irred := ni', num_redundant := nr' }
      scratch := scratch' } : FullState).LengthsOk c)
    (hge3 : 3 ≤ len)
    (hlits_lt : ∀ l ∈ (s.core.tmp.take len).map BitVec.toNat, l < 2 * s.core.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause ((s.core.tmp.take len).map BitVec.toNat)))
    (hhold_arena : ∀ k < s.core.arena_len, arena'[k]? = s.core.arena[k]?)
    (hnew_noshrk : (arena'[s.core.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hnew_sz : (arena'[s.core.arena_len + 2]?.getD 0#32).toNat = len)
    (hnew_lits : fullArenaClauseLitsCore
      { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len } s.core.arena_len =
      (s.core.tmp.take len).map BitVec.toNat)
    (hwat : ModeWatchesInv F_cur
      { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len,
                    wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable',
                    first_reducible := fred', num_irred := ni', num_redundant := nr' }) :
    let k' : FullCoreState :=
      { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len,
                    wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable',
                    first_reducible := fred', num_irred := ni', num_redundant := nr' }
    FullWitnessInv c F0 F_cur k' ∧
    fullArenaClauseRefsCore k' = fullArenaClauseRefsCore s.core ++ [s.core.arena_len] ∧
    (∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore s.core r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore s.core r) := by
  intro k'
  have hnxt_hold := hw.arena.arenaNextOff_extend (alen' := s.core.arena_len + 3 + len)
    (by omega) hhold_arena
  have hrefs : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore s.core ++ [s.core.arena_len] :=
    fullArenaClauseRefsCore_append hw.arena hge3 rfl hhold_arena hnew_noshrk hnew_sz
  have hold_garb : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore s.core r := fun r hr => by
    have := (hw.arena.refs_wf r hr).1
    unfold fullArenaClauseGarbCore fullArenaHdrCore k'; simp [hhold_arena r (by omega)]
  have hold_sz : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore s.core r := fun r hr => by
    have := (hw.arena.refs_wf r hr).1
    unfold fullArenaClauseSizeCore k'; simp [hhold_arena (r + 2) (by omega)]
  have hold_lits : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore s.core r := fun r hr => by
    have hwf := hw.arena.refs_wf r hr
    have h1l := hlen.core_ok.arena_len_arr; have h1e := hlen.core_ok.arena_len_le
    have h2l : arena'.length = c.arena_cap := hlen'.core_ok.arena_len_arr
    have h2e : s.core.arena_len + 3 + len ≤ c.arena_cap := hlen'.core_ok.arena_len_le
    have hbd_ar : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena_len := by omega
    exact fullArenaClauseLitsCore_eq_of_hold (by omega) (by dsimp only [k']; omega)
      (hold_sz r hr) fun j hj => hhold_arena (r + 3 + j) (by omega)
  have harena' : FullArenaClausesInv c F_cur k' := by
    refine ⟨Or.inr (by dsimp [k']; omega), ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · have hwf := hw.arena.refs_wf r hr
        rw [hnxt_hold r hr, hold_sz r hr]
        refine ⟨by dsimp [k']; omega, hwf.2.1, hwf.2.2.1, by dsimp [k']; omega, ?_⟩
        rcases hwf.2.2.2.2 with he | h3 <;> right <;> dsimp [k'] <;> omega
      · have hnxt_new : fullArenaNextOff k'.arena k'.arena_len s.core.arena_len =
            s.core.arena_len + 3 + len := by unfold fullArenaNextOff k'; simp [hnew_sz, hnew_noshrk]
        rw [hnxt_new, show fullArenaClauseSizeCore k' s.core.arena_len = len from hnew_sz]
        refine ⟨by dsimp [k']; omega, hge3, by omega, by dsimp [k']; omega, Or.inl (by dsimp [k'])⟩
    · intro r hr hsh; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · have hr3 := (hw.arena.refs_wf r hr).1
        have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
          unfold fullArenaHdrCore at hsh ⊢; dsimp only [k'] at hsh
          rwa [hhold_arena r (by omega)] at hsh
        obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
        exact ⟨t, by rw [hold_sz r hr]; exact ht1, by dsimp only [k']; omega,
          by dsimp only [k']; rw [hhold_arena t ht2]; exact hsent⟩
      · unfold fullArenaHdrCore at hsh; dsimp only [k'] at hsh; exact absurd hnew_noshrk hsh
    · intro r hr hng; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · rw [hold_garb r hr] at hng; rw [hold_lits r hr]; exact hw.arena.lits_lt r hr hng
      · exact hnew_lits ▸ hlits_lt
    · intro r hr hng; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · rw [hold_garb r hr] at hng; rw [hold_lits r hr]; exact hw.arena.entails r hr hng
      · exact hnew_lits ▸ hent
  refine ⟨{ hw with
    arena := harena', watches := hwat
    reason_inv := fun idx hidx hne => by
      have hne0 : s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠
          0xFFFFFFFF#32 := hne
      have hrs := hw.reason_inv idx hidx hne0
      rw [show k'.trl = s.core.trl from rfl, show k'.rsns = s.core.rsns from rfl,
        show k'.cur_vars = s.core.cur_vars from rfl, show k'.lvl = s.core.lvl from rfl]
      by_cases hb : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
      · rw [ite_eq_left hb] at hrs ⊢; exact hrs
      · rw [ite_eq_right hb] at hrs ⊢
        exact ⟨hrefs ▸ List.mem_append_left _ hrs.1, (hold_garb _ hrs.1).trans hrs.2.1,
          fun q hq => hrs.2.2 q (hold_lits _ hrs.1 ▸ hq)⟩
    reason_lit_mem := fun idx hidx hne hlg => by
      have hne0 : s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠
          0xFFFFFFFF#32 := hne
      have hlg0 : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) = 0#32 := hlg
      have hrs := hw.reason_inv idx hidx hne0
      have hb : ¬ (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := fun h => absurd hlg0 h
      rw [ite_eq_right hb] at hrs
      rw [show k'.trl = s.core.trl from rfl, show k'.rsns = s.core.rsns from rfl]
      exact hold_lits _ hrs.1 ▸ hw.reason_lit_mem idx hidx hne0 hlg0 }, hrefs,
    fun r hr => ⟨hold_garb r hr, hold_lits r hr⟩⟩

theorem addGarbageClause_preserves_witness {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState}
    (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core) {len : Nat}
    {arena' wvec' wstk' : List (BitVec 32)} {wlen' : Nat}
    {wusable' ag' oom' : BitVec 64} {scratch' : FullScratch}
    (hlen' : ({ s with
      core := { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len,
                            wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable',
                            arena_garbage := ag', oom := oom' }
      scratch := scratch' } : FullState).LengthsOk c)
    (hge3 : 3 ≤ len)
    (hhold_arena : ∀ i < s.core.arena_len, arena'[i]? = s.core.arena[i]?)
    (hnew_noshrk : (arena'[s.core.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hnew_garb : (arena'[s.core.arena_len]?.getD 0#32 &&& 0x00080000#32) ≠ 0#32)
    (hnew_sz : (arena'[s.core.arena_len + 2]?.getD 0#32).toNat = len)
    (hwat : ModeWatchesInv F_cur
      { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len,
                    wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable',
                    arena_garbage := ag', oom := oom' }) :
    let s' : FullState :=
      { s with
        core := { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len,
                              wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable',
                              arena_garbage := ag', oom := oom' }
        scratch := scratch' }
    FullWitnessInv c F0 F_cur s'.core ∧
    fullArenaClauseRefs s' = fullArenaClauseRefs s ++ [s.core.arena_len] ∧
    (FullArenaVarsNodup s → FullArenaVarsNodup s') := by
  intro s'
  have hnxt_hold := hw.arena.arenaNextOff_extend (alen' := s.core.arena_len + 3 + len)
    (by omega) hhold_arena
  have hrefs :
      fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core ++ [s.core.arena_len] :=
    fullArenaClauseRefsCore_append hw.arena hge3 rfl hhold_arena hnew_noshrk hnew_sz
  have hold_garb : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := fun r hr => by
    have := (hw.arena.refs_wf r hr).1
    unfold fullArenaClauseGarbCore fullArenaHdrCore s'; simp [hhold_arena r (by omega)]
  have hold_sz : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := fun r hr => by
    have := (hw.arena.refs_wf r hr).1
    unfold fullArenaClauseSizeCore s'; simp [hhold_arena (r + 2) (by omega)]
  have hold_lits : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := fun r hr => by
    have hwf := hw.arena.refs_wf r hr
    have h1l := hlen.core_ok.arena_len_arr; have h1e := hlen.core_ok.arena_len_le
    have h2l : arena'.length = c.arena_cap := hlen'.core_ok.arena_len_arr
    have h2e : s.core.arena_len + 3 + len ≤ c.arena_cap := hlen'.core_ok.arena_len_le
    have hbd_ar : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena_len := by omega
    exact fullArenaClauseLitsCore_eq_of_hold (by omega) (by dsimp only [s']; omega)
      (hold_sz r hr) fun j hj => hhold_arena (r + 3 + j) (by omega)
  have hnew_garb_s' : fullArenaClauseGarbCore s'.core s.core.arena_len = true := by
    unfold fullArenaClauseGarbCore fullArenaHdrCore s'; simp [hnew_garb]
  have harena' : FullArenaClausesInv c F_cur s'.core := by
    refine ⟨Or.inr (by dsimp [s']; omega), ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · have hwf := hw.arena.refs_wf r hr
        rw [hnxt_hold r hr, hold_sz r hr]
        refine ⟨by dsimp [s']; omega, hwf.2.1, hwf.2.2.1, by dsimp [s']; omega, ?_⟩
        rcases hwf.2.2.2.2 with he | h3 <;> right <;> dsimp [s'] <;> omega
      · have hnxt_new : fullArenaNextOff s'.core.arena s'.core.arena_len s.core.arena_len =
            s.core.arena_len + 3 + len := by unfold fullArenaNextOff s'; simp [hnew_sz, hnew_noshrk]
        rw [hnxt_new, show fullArenaClauseSizeCore s'.core s.core.arena_len = len from hnew_sz]
        refine ⟨by dsimp [s']; omega, hge3, by omega, by dsimp [s']; omega, Or.inl (by dsimp [s'])⟩
    · intro r hr hsh; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · have hr3 := (hw.arena.refs_wf r hr).1
        have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
          unfold fullArenaHdrCore at hsh ⊢; dsimp only [s'] at hsh
          rwa [hhold_arena r (by omega)] at hsh
        obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
        exact ⟨t, by rw [hold_sz r hr]; exact ht1, by dsimp only [s']; omega,
          by dsimp only [s']; rw [hhold_arena t ht2]; exact hsent⟩
      · unfold fullArenaHdrCore at hsh; dsimp only [s'] at hsh; exact absurd hnew_noshrk hsh
    · intro r hr hng; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · rw [hold_garb r hr] at hng; rw [hold_lits r hr]; exact hw.arena.lits_lt r hr hng
      · rw [hnew_garb_s'] at hng; cases hng
    · intro r hr hng; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · rw [hold_garb r hr] at hng; rw [hold_lits r hr]; exact hw.arena.entails r hr hng
      · rw [hnew_garb_s'] at hng; cases hng
  refine ⟨{ hw with
    arena := harena', watches := hwat
    reason_inv := fun idx hidx hne => by
      have hne0 : s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠
          0xFFFFFFFF#32 := hne
      have hrs := hw.reason_inv idx hidx hne0
      rw [show s'.core.trl = s.core.trl from rfl, show s'.core.rsns = s.core.rsns from rfl,
        show s'.core.cur_vars = s.core.cur_vars from rfl, show s'.core.lvl = s.core.lvl from rfl]
      by_cases hb : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
      · rw [ite_eq_left hb] at hrs ⊢; exact hrs
      · rw [ite_eq_right hb] at hrs ⊢
        exact ⟨hrefs ▸ List.mem_append_left _ hrs.1, (hold_garb _ hrs.1).trans hrs.2.1,
          fun q hq => hrs.2.2 q (hold_lits _ hrs.1 ▸ hq)⟩
    reason_lit_mem := fun idx hidx hne hlg => by
      have hne0 : s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠
          0xFFFFFFFF#32 := hne
      have hlg0 : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) = 0#32 := hlg
      have hrs := hw.reason_inv idx hidx hne0
      have hb : ¬ (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
          0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := fun h => absurd hlg0 h
      rw [ite_eq_right hb] at hrs
      rw [show s'.core.trl = s.core.trl from rfl, show s'.core.rsns = s.core.rsns from rfl]
      exact hold_lits _ hrs.1 ▸ hw.reason_lit_mem idx hidx hne0 hlg0 }, hrefs,
    fun hnd r hr hng => ?_⟩
  change r ∈ fullArenaClauseRefsCore s'.core at hr
  rw [hrefs, List.mem_append, List.mem_singleton] at hr
  rcases hr with hr | rfl
  · change fullArenaClauseGarbCore s'.core r = false at hng
    rw [hold_garb r hr] at hng
    unfold fullArenaClauseLits; rw [hold_lits r hr]; exact hnd r hr hng
  · change fullArenaClauseGarbCore s'.core s.core.arena_len = false at hng
    rw [hnew_garb_s'] at hng; cases hng

def fullAllocClSpec : Spec [i64, i32, i32, .bool] [i64] := fun (h, sz, _glue, red, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    if c.arena_cap - s.core.arena_len < 3 + sz.toNat then
      Q (0xFFFFFFFF#64, ()) m
    else
      ∀ arena' m',
        let alen' := s.core.arena_len + 3 + sz.toNat
        let s' : FullState :=
          { s with core := { s.core with arena_len := alen', arena := arena' } }
        s'.LengthsOk c →
        (∀ i < s.core.arena_len, arena'[i]? = s.core.arena[i]?) →
        (arena'[s.core.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32 →
        (arena'[s.core.arena_len]?.getD 0#32 &&& 0x00080000#32) = 0#32 →
        ((arena'[s.core.arena_len]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ↔ red = true) →
        (arena'[s.core.arena_len + 2]?.getD 0#32).toNat = sz.toNat →
        (FullMem c s' ⋆ R) m' →
        Q (BitVec.ofNat 64 s.core.arena_len, ()) m'

def fullWstackDefragSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧ (FullMem c s ⋆ R) m ∧
    ∀ wvec' wstk' wlen' wsort' m',
      let s' : FullState :=
        { s with
          core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
          scratch := { s.scratch with wsort := wsort' } }
      s'.LengthsOk c → WatchStackLayout s'.core → (1 ≤ s.core.wlen → 1 ≤ wlen') →
      (∀ l < 2 * s.core.cur_vars, fullWatchSize s' l = fullWatchSize s l ∧
        ∀ k < fullWatchSize s l,
          s'.core.wstk[fullWatchOff s' l + k]? = s.core.wstk[fullWatchOff s l + k]?) →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullWatchPushSpec : Spec [i64, i32, i32, i32, i32] [.bool] :=
  fun (h, lit, w0, w1, cnt, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧
      (cnt.toNat = 1 → w0 ≠ 0xFFFFFFFF#32) ∧
      (cnt.toNat = 2 → w0 ≠ 0xFFFFFFFF#32 ∧ w1 ≠ 0xFFFFFFFF#32) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) wvec' wstk' wlen' wusable' wsort' m',
        let s' : FullState :=
          { s with
            core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen',
                                  wusable := wusable' }
            scratch := { s.scratch with wsort := wsort' } }
        s'.LengthsOk c → WatchStackLayout s'.core →
        (∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat →
          fullWatchSize s' l = fullWatchSize s l ∧
          ∀ k < fullWatchSize s l,
            s'.core.wstk[fullWatchOff s' l + k]? = s.core.wstk[fullWatchOff s l + k]?) →
        (ok = true →
          lit.toNat < 2 * s.core.cur_vars ∧ (cnt.toNat = 1 ∨ cnt.toNat = 2) ∧
          fullWatchSize s' lit.toNat = fullWatchSize s lit.toNat + cnt.toNat ∧
          (∀ k < fullWatchSize s lit.toNat,
            s'.core.wstk[fullWatchOff s' lit.toNat + k]? =
              s.core.wstk[fullWatchOff s lit.toNat + k]?) ∧
          s'.core.wstk[fullWatchOff s' lit.toNat + fullWatchSize s lit.toNat]? = some w0 ∧
          (cnt.toNat = 2 →
            s'.core.wstk[fullWatchOff s' lit.toNat + fullWatchSize s lit.toNat + 1]? = some w1)) →
        (ok = false →
          (lit.toNat < 2 * s.core.cur_vars →
            fullWatchSize s' lit.toNat = fullWatchSize s lit.toNat ∧
            ∀ k < fullWatchSize s lit.toNat,
              s'.core.wstk[fullWatchOff s' lit.toNat + k]? =
                s.core.wstk[fullWatchOff s lit.toNat + k]?) ∧
          (2 * s.core.cur_vars ≤ lit.toNat ∨ (cnt.toNat ≠ 1 ∧ cnt.toNat ≠ 2) ∨
            s' = s ∨ wusable' = 0#64)) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullAssignLvlSpec : Spec [i64, i32, i32, i32] [] :=
  fun (h, lit, rsn, alvl, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      if s.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ s.core.trail_end ∨
          s.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8 then
        Q () m
      else
        let v := lit.toNat / 2
        let rsn' := if alvl = 0#32 then 0xFFFFFFFF#32 else rsn
        let unfl' := if alvl = 0#32 then s.core.unflushed + 1#64 else s.core.unflushed
        ∀ flags' unass' phases' m',
          flags'.length = c.max_vars → phases'.length = c.max_vars →
          let s' : FullState :=
            { s with
              core :=
                { s.core with
                  vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
                  flags := flags', lvl := s.core.lvl.set v alvl, rsns := s.core.rsns.set v rsn'
                  trl := s.core.trl.set s.core.trail_end lit
                  trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
                  trail_end := s.core.trail_end + 1
                  unassigned := unass', unflushed := unfl' }
              scratch := { s.scratch with phases := phases' } }
          (FullMem c s' ⋆ R) m' → Q () m'

def fullAssignSpec : Spec [i64, i32, i32] [] := fun (h, lit, rsn, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ s.core.cur_level < 2 ^ 32 ∧ (FullMem c s ⋆ R) m ∧
    if s.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ s.core.trail_end ∨
        s.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8 then
      Q () m
    else
      let v := lit.toNat / 2
      let rsn' := if s.core.cur_level = 0 then 0xFFFFFFFF#32 else rsn
      let unfl' := if s.core.cur_level = 0 then s.core.unflushed + 1#64 else s.core.unflushed
      ∀ flags' unass' phases' m',
        flags'.length = c.max_vars → phases'.length = c.max_vars →
        let s' : FullState :=
          { s with
            core :=
              { s.core with
                vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
                flags := flags', lvl := s.core.lvl.set v (BitVec.ofNat 32 s.core.cur_level)
                rsns := s.core.rsns.set v rsn', trl := s.core.trl.set s.core.trail_end lit
                trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
                trail_end := s.core.trail_end + 1
                unassigned := unass', unflushed := unfl' }
            scratch := { s.scratch with phases := phases' } }
        (FullMem c s' ⋆ R) m' → Q () m'

def fullAddClauseSpec : Spec [i64, i32, i32, .bool] [i64] :=
  fun (h, len, _glue, _red, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ s.core.dense_mode = 0#64 ∧
      len.toNat ≤ c.max_vars ∧
      (2 ≤ len.toNat →
        (∀ l ∈ (s.core.tmp.take len.toNat).map BitVec.toNat, l < 2 * s.core.cur_vars) ∧
        ((s.core.tmp.take len.toNat).map fun x => x.toNat / 2).Nodup ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.core.tmp.take len.toNat).map BitVec.toNat))) ∧
      (FullMem c s ⋆ R) m ∧
      if len.toNat < 2 then
        Q (0xFFFFFFFF#64, ()) m
      else if len.toNat = 2 then
        ∀ r wvec' wstk' wlen' wusable' nb' wsort' m',
          let s' : FullState :=
            { s with
              core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen',
                                    wusable := wusable', num_binary := nb' }
              scratch := { s.scratch with wsort := wsort' } }
          (r = 0xFFFFFFFF#64 ∨ r = 0xFFFFFFFE#64) →
          s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → (FullMem c s' ⋆ R) m' → Q (r, ()) m'
      else
        ∀ r arena' alen' wvec' wstk' wlen' wusable' fred' ni' nr' wsort' m',
          let s' : FullState :=
            { s with
              core := { s.core with arena := arena', arena_len := alen', wvec := wvec',
                                    wstk := wstk', wlen := wlen', wusable := wusable',
                                    first_reducible := fred', num_irred := ni',
                                    num_redundant := nr' }
              scratch := { s.scratch with wsort := wsort' } }
          (r = 0xFFFFFFFF#64 ∨ r = BitVec.ofNat 64 s.core.arena_len) →
          s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
          (∀ ref ∈ fullArenaClauseRefs s, ref ∈ fullArenaClauseRefs s') →
          (FullArenaVarsNodup s → FullArenaVarsNodup s') →
          (r = BitVec.ofNat 64 s.core.arena_len →
            alen' = s.core.arena_len + 3 + len.toNat ∧
            s.core.arena_len ∈ fullArenaClauseRefs s' ∧
            fullArenaClauseGarb s' s.core.arena_len = false ∧
            fullArenaClauseLits s' s.core.arena_len =
              (s.core.tmp.take len.toNat).map BitVec.toNat) →
          (FullMem c s' ⋆ R) m' → Q (r, ()) m'

end FullAssignAddSpecs

/-! ## 3. `full_assign_lvl` and `full_assign` `Func.wp` Proofs -/

open scoped FullArenaTactics FullAssignAddTactics
open FullAssignAddTactics FullAssignAddSpecs

private abbrev asg0 (s : FullState) (lit : BitVec 32) : FullState :=
  { s with core :=
    { s.core with vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8 } }

private abbrev asg1 (s : FullState) (lit : BitVec 32) (unass' : BitVec 64) : FullState :=
  { s with core :=
    { s.core with vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
                  unassigned := unass' } }

private abbrev asg2 (s : FullState) (lit : BitVec 32) (unass' : BitVec 64)
    (ph' : List (BitVec 8)) : FullState :=
  { s with
    core :=
      { s.core with vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
                    unassigned := unass' }
    scratch := { s.scratch with phases := ph' } }

private abbrev asg3 (s : FullState) (lit : BitVec 32) (unass' : BitVec 64)
    (ph' : List (BitVec 8)) (alvl : BitVec 32) : FullState :=
  { s with
    core :=
      { s.core with vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
                    unassigned := unass', lvl := s.core.lvl.set (lit.toNat / 2) alvl }
    scratch := { s.scratch with phases := ph' } }

private abbrev asg4 (s : FullState) (lit rsn' alvl : BitVec 32) (flags' : List (BitVec 32))
    (unass' unfl' : BitVec 64) (ph' : List (BitVec 8)) : FullState :=
  { s with
    core :=
      { s.core with vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
                    flags := flags', lvl := s.core.lvl.set (lit.toNat / 2) alvl
                    rsns := s.core.rsns.set (lit.toNat / 2) rsn'
                    unassigned := unass', unflushed := unfl' }
    scratch := { s.scratch with phases := ph' } }

private abbrev asgFin (s : FullState) (lit rsn' alvl : BitVec 32) (flags' : List (BitVec 32))
    (unass' unfl' : BitVec 64) (ph' : List (BitVec 8)) : FullState :=
  { s with
    core :=
      { s.core with vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
                    flags := flags', lvl := s.core.lvl.set (lit.toNat / 2) alvl
                    rsns := s.core.rsns.set (lit.toNat / 2) rsn'
                    trl := s.core.trl.set s.core.trail_end lit
                    trail_pos := s.core.trail_pos.set (lit.toNat / 2)
                      (BitVec.ofNat 32 s.core.trail_end)
                    trail_end := s.core.trail_end + 1
                    unassigned := unass', unflushed := unfl' }
    scratch := { s.scratch with phases := ph' } }

theorem full_assign_lvl_wp (Γ : Env) :
    ∀ args m Q X, fullAssignLvlSpec args m Q X →
      Func.wp Γ full_assign_lvl_body args m Q X := by
  rintro ⟨h, lit, rsn, alvl, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hco := hlen.core_ok
  have hte_lt64 : s.core.trail_end + 1 < 2 ^ 64 := by
    have := hco.trail_end_le; have := hco.cur_vars_le; omega
  have hte_lt32 : s.core.trail_end < 2 ^ 32 := by
    have := hco.trail_end_le; have := hco.cur_vars_le; omega
  have hcv64 : s.core.cur_vars < 2 ^ 64 := by have := hco.cur_vars_le; omega
  faa_head_steps
  c0_step
  · have hge : s.core.cur_vars ≤ lit.toNat / 2 := by
      clear hm hQ; omega
    clear hc
    simp only [show s.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ s.core.trail_end ∨
        s.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8 from Or.inl hge, ↓reduceIte] at hQ
    faa_head_steps; exact hQ
  · have hvar : lit.toNat / 2 < s.core.cur_vars := by
      clear hm hQ; omega
    clear hc
    faa_head_steps
    c0_step
    · have hte_ge : c.max_vars ≤ s.core.trail_end := by
        clear hm hQ; omega
      clear hc
      simp only [show s.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ s.core.trail_end ∨
          s.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8 from Or.inr (Or.inl hte_ge), ↓reduceIte] at hQ
      faa_head_steps; exact hQ
    · have hte : s.core.trail_end < c.max_vars := by
        clear hm hQ; omega
      clear hc
      have hvl : s.core.vals.length = 2 * c.max_vars := hco.vals_len
      have hfll : s.core.flags.length = c.max_vars := hco.flags_len
      have hphl : s.scratch.phases.length = c.max_vars := hlen.scratch_ok.phases_len
      have hll : s.core.lvl.length = c.max_vars := hco.lvl_len
      have hrsl : s.core.rsns.length = c.max_vars := hco.rsns_len
      have htpl : s.core.trail_pos.length = c.max_vars := hco.trail_pos_len
      have htrl : s.core.trl.length = c.max_vars := hco.trl_len
      have hlit_lt : lit.toNat < 2 * c.max_vars := by have := hco.cur_vars_le; omega
      have hnlit_lt : (lit.toNat ^^^ 1) < 2 * c.max_vars := litNeg_lt_two_mul hlit_lt
      have hv_lt : lit.toNat / 2 < c.max_vars := by have := hco.cur_vars_le; omega
      faa_head_steps
      c0_step
      · have hnz : s.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8 := by
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          intro hz
          rw [hz] at hc
          exact hc rfl
        clear hc
        faa_head_steps
        simp only [show s.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ s.core.trail_end ∨
            s.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8 from Or.inr (Or.inr hnz), ↓reduceIte] at hQ
        exact hQ
      · have hz : s.core.vals[lit.toNat]?.getD 0#8 = 0#8 := by
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          exact BitVec.eq_of_getLsbD_eq fun i hi => by
            have hbit := congrArg (fun v : BitVec 32 => v.getLsbD i) hc
            simp only [BitVec.getLsbD_signExtend, show i < 32 by omega, decide_true,
              Bool.true_and, show i < 8 from hi, ↓reduceIte] at hbit
            simpa using hbit
        clear hc
        simp only [show ¬ (s.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ s.core.trail_end ∨
            s.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8) by simp [hz]; omega, ↓reduceIte] at hQ
        faa_head_steps
        have hm0 : (FullMem c (asg0 s lit) ⋆ R) m := by
          simp only [bv_c0_zext32_64, BitVec.toNat_xor,
            show BitVec.toNat (1 : BitVec 32) = 1 from rfl,
            show BitVec.setWidth 8 (-1 : BitVec 32) = 0xFF#8 by decide] at hm
          exact hm
        clear hm
        refine wp_join_group (fun () m1 => ∃ unass' : BitVec 64,
          (FullMem c (asg1 s lit unass') ⋆ R) m1) ?_ ?_
        · rintro _ ⟨⟩ m1 ⟨unass', hm1⟩
          faa_head_steps
          refine wp_join_group (fun () m2 => ∃ ph' : List (BitVec 8),
            ph'.length = c.max_vars ∧ (FullMem c (asg2 s lit unass' ph') ⋆ R) m2) ?_ ?_
          · rintro _ ⟨⟩ m2 ⟨ph', hph', hm2⟩
            faa_head_steps
            have hm3 : (FullMem c (asg3 s lit unass' ph' alvl) ⋆ R) m := by
              simp only [bv_c0_zext32_64, bv32_lshr1] at hm
              exact hm
            refine wp_join_group (fun () m3 => ∃ flags' : List (BitVec 32),
              flags'.length = c.max_vars ∧
              (FullMem c (asg4 s lit (if alvl = 0#32 then 0xFFFFFFFF#32 else rsn) alvl
                flags' unass' (if alvl = 0#32 then s.core.unflushed + 1#64 else s.core.unflushed)
                ph') ⋆ R) m3) ?_ ?_
            · rintro _ ⟨⟩ m3 ⟨flags', hfl', hm3'⟩
              c0_steps
              have hfin : (FullMem c
                  (asgFin s lit (if alvl = 0#32 then 0xFFFFFFFF#32 else rsn) alvl flags' unass'
                    (if alvl = 0#32 then s.core.unflushed + 1#64 else s.core.unflushed) ph') ⋆
                  R) m := by
                simp only [bv_c0_zext32_64, bv32_lshr1, bv64_setWidth32_ofNat,
                  bv64_ofNat_toNat (by omega : s.core.trail_end < 2 ^ 64),
                  bv64_add1_toNat hte_lt64] at hm
                exact hm
              exact hQ flags' unass' ph' m hfl' hph' hfin
            · intro J3 hJ3; clear hQ
              c0_steps
              · simp only [bv_c0_zext32_64, bv32_lshr1] at hm
                refine hJ3 () m ⟨s.core.flags.set (lit.toNat / 2)
                  (s.core.flags[lit.toNat / 2]'(by omega) &&& ~~~1#32), by simp [hfll], ?_⟩
                simp only [show (alvl = 0#32) = True from eq_true (hc : alvl = 0#32), ↓reduceIte]
                exact hm
              · simp only [bv_c0_zext32_64, bv32_lshr1] at hm
                refine hJ3 () m ⟨s.core.flags, hco.flags_len, ?_⟩
                simp only [show (alvl = 0#32) = False from eq_false (hc : alvl ≠ 0#32), ↓reduceIte]
                exact hm
          · intro J2 hJ2; clear hQ
            c0_steps
            · simp only [bv_c0_zext32_64, bv32_lshr1] at hm
              exact hJ2 () m ⟨s.scratch.phases.set (lit.toNat / 2) 0xFF#8, by simp [hphl], hm⟩
            · simp only [bv_c0_zext32_64, bv32_lshr1] at hm
              exact hJ2 () m ⟨s.scratch.phases.set (lit.toNat / 2) 1#8, by simp [hphl], hm⟩
            · exact hJ2 () m1 ⟨s.scratch.phases, hlen.scratch_ok.phases_len, hm1⟩
        · intro J1 hJ1; clear hQ
          c0_steps
          · exact hJ1 () m ⟨s.core.unassigned - 1#64, hm⟩
          · exact hJ1 () m ⟨s.core.unassigned, hm0⟩
          · exact hJ1 () m ⟨s.core.unassigned, hm0⟩

theorem full_assign_wp (Γ : Env)
    (hAssignLvl : ∀ args m Q X, fullAssignLvlSpec args m Q X →
      Γ "full_assign_lvl" [i64, i32, i32, i32] [] args m Q X) :
    ∀ args m Q X, fullAssignSpec args m Q X → Func.wp Γ full_assign_body args m Q X := by
  rintro ⟨h, lit, rsn, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcl32, hm, hQ⟩
  have halvl_eq : (BitVec.ofNat 64 s.core.cur_level).setWidth 32 =
      BitVec.ofNat 32 s.core.cur_level := bv64_setWidth32_ofNat s.core.cur_level
  have halvl0 : BitVec.ofNat 32 s.core.cur_level = 0#32 ↔ s.core.cur_level = 0 := by
    constructor
    · intro heq
      have h1 := congrArg BitVec.toNat heq
      rwa [bv32_ofNat_toNat hcl32, show (0#32 : BitVec 32).toNat = 0 from rfl] at h1
    · intro h0; rw [h0]
  faa_head_steps
  c0_call hAssignLvl
  refine ⟨c, s, R, rfl, hlen, hm, ?_⟩
  rw [halvl_eq]; split
  · next hc_t => simp only [hc_t, ↓reduceIte] at hQ; exact hQ
  · next hc_f =>
    simp only [hc_f, ↓reduceIte] at hQ
    dsimp only at hQ ⊢
    intro flags' unass' phases' m' hfl' hph' hm'
    c0_steps
    simp only [halvl0] at hm'
    exact hQ flags' unass' phases' m' hfl' hph' hm'

end LeanQbe.T.Examples.Kissat.Full
