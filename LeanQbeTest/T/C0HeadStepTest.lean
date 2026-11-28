module

import LeanQbe.T.Frontend.C0
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Examples.Kissat.PlainPropLemmas1
import LeanQbe.T.Examples.Kissat.PlainReduceLemmas1
import LeanQbe.T.Examples.LratBytesDimacsLemmas
meta import LeanQbe.T.Frontend.C0
meta import LeanQbe.T.Logic.C0StepAttr

/-!
# Verification Suite for `C0HeadStep` and Two-Level `(footprintHead, AddrKey)` Indexing

Tests:
1. Two-level `(footprintHead, AddrKey)` indexing in `C0StepAttr`:
   - `extractAddrKey` classification across constant header offsets, dynamic array offsets,
     nested sub-buffer offsets, and variable-base addresses.
   - `O(1)` bucket narrowing on `PlainMem` (`1–2` candidates vs `200+` total lemmas) while
     preserving 100% backward-compatible `c0MemLemmas`.
2. Direct `Op.mk`, `op1`, `op2`, and `op3` stepping (zero `MVarId.change` on straight-line `let_`):
   - Arithmetic, bitwise, Bool, `select`, `ofBool`, `zext`/`sext`/`trunc` literal folding,
     `shl`/`lshr`/`ashr` with `sext`-promoted shifts, all `CmpOp`s, `udiv`/`urem`/`sdiv`/`srem`,
     `addc`/`subb`/`umulw`, `head_strip_le`, `c0_hstep`, `c0_hsteps`, `c0_hsteps!`,
     `c0_hsteps_nogrp`, and `c0_hsplit`.
3. End-to-end `c0_decl_and_layout!` struct/array loop + strict unmatched-memory diagnostics.
4. Synthetic asymptotic scaling chains (`N = 20, 40, 80` on `Op.mk` and `op2`, up to `240` ops).
5. Real `LratBytes` (`isWsByte`) and real Kissat `D-Plain` C0 functions (`plain_find_repl_body`,
   `plain_red_less_body`, `plain_lit_rank_body`) with no shard-local stepper macros.
6. `#print axioms` strictly `⊆ [propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.C0HeadStepTest

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Frontend.C0 LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Plain
open Kraken.Bedrock2.Test

/-! ## 1. Two-Level `(footprintHead, AddrKey)` Indexing Verification -/

section AddrKeyTests
open scoped PlainPropTactics PlainReduceTactics

/-- Programmatic MetaM check that `C0StepAttr` classifies `PlainMem` addresses into `O(1)` buckets
while preserving the complete backward-compatible `c0MemLemmas` list. -/
theorem addrKey_plainMem_dispatch_check : True := by
  run_tac do
    let env ← Lean.getEnv
    let totalLoads := C0Step.c0MemLemmas env true ``PlainMem
    let totalStores := C0Step.c0MemLemmas env false ``PlainMem
    unless totalLoads.size ≥ 140 do
      throwError "expected ≥ 140 PlainMem load lemmas in c0MemLemmas, got {totalLoads.size}"
    unless totalStores.size ≥ 120 do
      throwError "expected ≥ 120 PlainMem store lemmas in c0MemLemmas, got {totalStores.size}"
    let bv64 := Lean.mkApp (Lean.mkConst ``BitVec) (Lean.mkNatLit 64)
    Lean.Meta.withLocalDeclD `c (Lean.mkConst ``PlainCfg) fun cE =>
    Lean.Meta.withLocalDeclD `i bv64 fun iE =>
    Lean.Meta.withLocalDeclD `p bv64 fun pE => do
      let addInst := Lean.mkApp2 (Lean.mkConst ``instHAdd [Lean.Level.zero]) bv64
        (Lean.mkApp (Lean.mkConst ``BitVec.instAdd) (Lean.mkNatLit 64))
      let mkAdd (a b : Lean.Expr) :=
        Lean.mkApp6 (Lean.mkConst ``HAdd.hAdd [Lean.Level.zero, Lean.Level.zero, Lean.Level.zero])
          bv64 bv64 bv64 addInst a b
      let mkBv (n : Nat) := Lean.mkApp2 (Lean.mkConst ``BitVec.ofNat) (Lean.mkNatLit 64)
        (Lean.mkNatLit n)
      -- 1. `c.hdr` -> `constOff PlainCfg.hdr 0`
      let hdrE := Lean.mkApp (Lean.mkConst ``PlainCfg.hdr) cE
      let kHdr0 := C0Step.extractAddrKey hdrE (some env)
      unless kHdr0 == .constOff ``PlainCfg.hdr 0 do
        throwError "unexpected AddrKey for c.hdr: {repr kHdr0}"
      let bHdr0 := C0Step.c0MemLemmasForAddr env true ``PlainMem hdrE
      unless bHdr0.contains ``Plain.load_arena_mv && bHdr0.size ≤ 4 do
        throwError "unexpected bucket for c.hdr: {bHdr0}"
      -- 2. `c.hdr + 48#64` -> `constOff PlainCfg.hdr 48` (hits `load_arena_len` in O(1))
      let hdr48 := mkAdd hdrE (mkBv 48)
      let kHdr48 := C0Step.extractAddrKey hdr48 (some env)
      unless kHdr48 == .constOff ``PlainCfg.hdr 48 do
        throwError "unexpected AddrKey for c.hdr + 48: {repr kHdr48}"
      let bHdr48 := C0Step.c0MemLemmasForAddr env true ``PlainMem hdr48
      unless bHdr48.contains ``Plain.load_arena_len && bHdr48.size ≤ 4 do
        throwError "unexpected bucket for c.hdr + 48: {bHdr48}"
      -- 3. `c.pArena + i` -> `baseOnly PlainCfg.pArena` (only pArena lemmas, not all 140+)
      let pArenaE := Lean.mkApp (Lean.mkConst ``PlainCfg.pArena) cE
      let arenaDyn := mkAdd pArenaE iE
      let kArena := C0Step.extractAddrKey arenaDyn (some env)
      unless kArena == .baseOnly ``PlainCfg.pArena do
        throwError "unexpected AddrKey for c.pArena + i: {repr kArena}"
      let bArena := C0Step.c0MemLemmasForAddr env true ``PlainMem arenaDyn
      unless bArena.contains ``Plain.c0_load_arena_arena && bArena.size ≤ 8 do
        throwError "unexpected bucket for c.pArena + i: {bArena}"
      -- 4. Nested sub-buffer `(c.pWstk + 4096#64) + i` -> `baseOnly PlainCfg.pWstk`
      let pWstkE := Lean.mkApp (Lean.mkConst ``PlainCfg.pWstk) cE
      let wstkNested := mkAdd (mkAdd pWstkE (mkBv 4096)) iE
      let kWstk := C0Step.extractAddrKey wstkNested (some env)
      unless kWstk == .baseOnly ``PlainCfg.pWstk do
        throwError "unexpected AddrKey for nested wstk addr: {repr kWstk}"
      -- 5. Variable base `p` and `p + 8#64` -> `.any`
      unless C0Step.extractAddrKey pE (some env) == .any do
        throwError "expected .any for variable base p"
      unless C0Step.extractAddrKey (mkAdd pE (mkBv 8)) (some env) == .any do
        throwError "expected .any for variable base p + 8"
      -- 6. Direct `reduceHeadExpr` check on `mdata`-wrapped `ret`
      let retE := Lean.mkApp4 (Lean.mkConst ``LeanQbe.T.Expr.ret)
        (Lean.mkConst ``LeanQbe.T.Val) (Lean.mkConst ``LeanQbe.T.Cont)
        (Lean.mkApp (Lean.mkConst ``List.nil [Lean.Level.zero]) (Lean.mkConst ``LeanQbe.T.Ty))
        (Lean.mkConst ``Unit.unit)
      let wrapped := Lean.Expr.mdata {} retE
      unless C0HeadStep.reduceHeadExpr wrapped == retE do
        throwError "reduceHeadExpr failed to strip mdata on Expr.ret"
  trivial

end AddrKeyTests

/-! ## 2. Direct `op1`/`op2`/`op3`, Promoted Shifts, `head_strip_le`, `c0_hstep`, `c0_hsplit` -/

/-- Exercise direct `op1`, `op2`, `op3`, `sext`-promoted shift constants (`sext 32 64 1#32`),
both `sext`-folded and pre-wrapped `BitVec.signExtend` shifts, `select`, `ofBool`, `cmp`, and
Bool bitwise ops in one straight-line program. -/
def directOpProg (x y : BitVec 64) (z : BitVec 32) (b : Bool) : Expr Val Cont [i64] :=
  .let_ (op1 (.sext 32 64) (.imm 1#32)) fun (one64, ()) =>
  .let_ (op2 (.shl i64) (.var x) (.var one64)) fun (s1, ()) =>
  .let_ (op2 (.lshr i64) (.var s1) (.var (BitVec.signExtend 64 2#32))) fun (s2, ()) =>
  .let_ (op2 (.ashr i64) (.var s2) (.imm 1#64)) fun (s3, ()) =>
  .let_ (op1 (.zext 32 64) (.var z)) fun (z64, ()) =>
  .let_ (op2 (.add i64) (.var s3) (.var z64)) fun (a1, ()) =>
  .let_ (op2 (.sub i64) (.var a1) (.var y)) fun (a2, ()) =>
  .let_ (op2 (.xor i64) (.var a2) (.imm 7#64)) fun (a3, ()) =>
  .let_ (op2 (.ult i64) (.var a3) (.var y)) fun (c1, ()) =>
  .let_ (op2 (.and .bool) (.var c1) (.var b)) fun (c2, ()) =>
  .let_ (op1 (.not .bool) (.var c2)) fun (c3, ()) =>
  .let_ (op1 (.ofBool 64) (.var c3)) fun (ob, ()) =>
  .let_ (op3 (.select i64) (.var c3) (.var a3) (.var ob)) fun (res, ()) =>
  .ret (.var res, ())

theorem directOpProg_wp (Γ : Env) (Q : Post [i64]) (X : XPost) (m : Mem 64)
    (x y : BitVec 64) (z : BitVec 32) (b : Bool)
    (hQ :
      let a3 := (((x <<< 1) >>> 2).sshiftRight 1 + z.setWidth 64 - y) ^^^ 7#64
      let c3 := !(a3.ult y && b)
      Q (if c3 then a3 else BitVec.ofNat 64 c3.toNat, ()) m) :
    wp Γ Q X (directOpProg x y z b) m := by
  unfold directOpProg
  c0_hsteps
  exact hQ

/-- Exercise `c0_hstep` single-stepping and automatic `head_strip_le` (`w ≤ 64 ∧ P`). -/
theorem hstep_and_strip_le_test (Γ : Env) (Q : Post [i64]) (X : XPost) (m : Mem 64)
    (x : BitVec 64) (hQ : Q (x + 1#64, ()) m) :
    32 ≤ 64 ∧ (8 ≤ 32 ∧ wp Γ Q X
      (.let_ (op2 (.add i64) (.var x) (.imm 1#64)) fun (r, ()) => .ret (.var r, ())) m) := by
  c0_hstep
  c0_hstep
  c0_hstep
  c0_hstep
  exact hQ

/-- Exercise `c0_hsplit`: steps straight-line code up to `jnz`, then splits ONE `jnz` without
running `c0_bound` on live branches, leaving both arms cleanly ready. -/
def splitProg (x y : BitVec 64) : Expr Val Cont [i64] :=
  .let_ (op2 (.ult i64) (.var x) (.var y)) fun (c, ()) =>
  .jnz (.var c)
    (.let_ (op2 (.add i64) (.var x) (.imm 1#64)) fun (r, ()) => .ret (.var r, ()))
    (.let_ (op2 (.sub i64) (.var x) (.imm 1#64)) fun (r, ()) => .ret (.var r, ()))

theorem splitProg_wp (Γ : Env) (Q : Post [i64]) (X : XPost) (m : Mem 64) (x y : BitVec 64)
    (h1 : x.toNat < y.toNat → Q (x + 1#64, ()) m)
    (h2 : ¬x.toNat < y.toNat → Q (x - 1#64, ()) m) :
    wp Γ Q X (splitProg x y) m := by
  unfold splitProg
  c0_hsplit
  · c0_hsteps; exact h1 hc
  · c0_hsteps; exact h2 hc

/- Exercise `c0_decl_and_layout!`, `c0_hsteps_nogrp`, `c0_hsteps!`, `sdiv`/`srem`, `addc`/`subb`/
`umulw`, and strict diagnostic reporting on an untagged footprint. -/
c0_decl_and_layout! hs "
typedef struct { u64 len; u64 acc; u64 tag; } HsBox;
u64 hs_step_box(HsBox *b, u64 *arr, u64 idx) {
  u64 v = arr[idx];
  b->acc = b->acc + (v << 1);
  b->len = b->len + 1ULL;
  return b->acc;
}
i64 hs_div_arith(i64 a, i64 b, bool cin) {
  if (b <= 0LL) { return 0LL; }
  u64 s = 0ULL; bool co = false;
  C0_TIE2(s, co, c0_addc64((u64)a, (u64)b, cin));
  u64 lo = 0ULL; u64 hi = 0ULL;
  C0_TIE2(lo, hi, c0_umul128(s, (u64)b));
  return (a / b) + (a % b) + (i64)(lo ^ hi ^ (u64)co);
}
u64 hs_unmatched(u64 p) { return *(u64 *)p; }
"

theorem hs_step_box_wp (Γ : Env) (bp ap idx : BitVec 64) (b : HsBox) (xs : List (BitVec 64))
    (R : Mem 64 → Prop) (m : Mem 64) (Q : Post [i64]) (X : XPost)
    (hi : idx.toNat < xs.length) (hm : (HsBox.At bp b ⋆ array (t := i64) ap xs ⋆ R) m)
    (hQ : ∀ m',
      (HsBox.At bp { b with acc := b.acc + (xs[idx.toNat]'hi <<< 1), len := b.len + 1#64 } ⋆
        array (t := i64) ap xs ⋆ R) m' →
      Q (b.acc + (xs[idx.toNat]'hi <<< 1), ()) m') :
    Func.wp Γ hs_step_box_body (bp, ap, idx, ()) m Q X := by
  c0_hsteps!
  dsimp only at hm
  exact hQ _ (by simpa [Std.ExtHashMap.sep_emp, Std.ExtHashMap.sep_assoc] using hm)

theorem hs_div_arith_wp (Γ : Env) (a b : BitVec 64) (cin : Bool) (m : Mem 64)
    (Q : Post [i64]) (X : XPost)
    (h0 : b.sle 0#64 = true → Q (0#64, ()) m)
    (hpos : b.sle 0#64 = false →
      let s := a + b + BitVec.ofNat 64 cin.toNat
      let co := decide (2 ^ 64 ≤ a.toNat + b.toNat + cin.toNat)
      let lo := s * b
      let hi := BitVec.ofNat 64 (s.toNat * b.toNat / 2 ^ 64)
      Q (a.sdiv b + a.srem b + (lo ^^^ hi ^^^ BitVec.ofNat 64 co.toNat), ()) m) :
    Func.wp Γ hs_div_arith_body (a, b, cin, ()) m Q X := by
  c0_hsteps!
  · exact h0 hc
  · exact hpos hc

def HsUntagged (p v : BitVec 64) : Mem 64 → Prop := cell (t := i64) p v

theorem hs_unmatched_diag_test (Γ : Env) (p v : BitVec 64) (R : Mem 64 → Prop) (m : Mem 64)
    (Q : Post [i64]) (X : XPost) (hm : (HsUntagged p v ⋆ R) m) (hQ : Q (v, ()) m) :
    Func.wp Γ hs_unmatched_body (p, ()) m Q X := by
  run_tac do
    let s ← Lean.Elab.Tactic.saveState
    try
      Lean.Elab.Tactic.evalTactic (← `(tactic| c0_hsteps!))
      s.restore
      throwError "expected c0_hsteps! to fail on untagged footprint"
    catch e =>
      let msg ← e.toMessageData.toString
      s.restore
      for needle in ["c0_hstep", "c0_load", "HsUntagged"] do
        unless (msg.splitOn needle).length > 1 do
          throwError "diagnostic missing '{needle}':\n{msg}"
  unfold HsUntagged at hm
  c0_hsteps!
  exact hQ

/-! ## 3. Synthetic Scaling Chains (`N = 20, 40, 80` on `Op.mk` and `op2`) -/

def mkChainCont : Nat → BitVec 64 → Val i64 → (Val i64 → Expr Val Cont [i64]) →
    Expr Val Cont [i64]
  | 0, _, x, k => k x
  | k + 1, p, x, cont =>
    .load i64 (.var p) fun v =>
    .let_ (Op.mk (.add i64) (.var x, .var v, ())) fun (y, ()) =>
    .let_ (Op.mk (.xor i64) (.var y, .imm 1#64, ())) fun (z, ()) =>
    mkChainCont k p z cont

def mkChain (n : Nat) (p : BitVec 64) (x : Val i64) : Expr Val Cont [i64] :=
  mkChainCont n p x fun z => .ret (.var z, ())

def mkChain80 (p : BitVec 64) (x : Val i64) : Expr Val Cont [i64] :=
  .group (sig := [[i64]])
    (fun _ => Blocks.cons (fun (y, ()) => mkChain 40 p y) Blocks.nil)
    fun (J, ()) => mkChainCont 40 p x fun z => .jump J (.var z, ())

def mkChainOp2 : Nat → BitVec 64 → Val i64 → Expr Val Cont [i64]
  | 0, _, x => .ret (.var x, ())
  | k + 1, p, x =>
    .load i64 (.var p) fun v =>
    .let_ (op2 (.add i64) (.var x) (.var v)) fun (y, ()) =>
    .let_ (op2 (.xor i64) (.var y) (.imm 1#64)) fun (z, ()) =>
    mkChainOp2 k p z

def chainSpec : Nat → BitVec 64 → BitVec 64 → BitVec 64
  | 0, _, x => x
  | k + 1, v, x => chainSpec k v ((x + v) ^^^ 1#64)

theorem chain20_hsteps (Γ : Env) (Q : Post [i64]) (X : XPost) (p v x : BitVec 64)
    (R : Mem 64 → Prop) (m : Mem 64) (hm : (cell (t := i64) p v ⋆ R) m)
    (hQ : Q (chainSpec 20 v x, ()) m) : wp Γ Q X (mkChain 20 p x) m := by
  dsimp only [mkChain, mkChainCont, chainSpec]; c0_hsteps; exact hQ

theorem chain40_hsteps (Γ : Env) (Q : Post [i64]) (X : XPost) (p v x : BitVec 64)
    (R : Mem 64 → Prop) (m : Mem 64) (hm : (cell (t := i64) p v ⋆ R) m)
    (hQ : Q (chainSpec 40 v x, ()) m) : wp Γ Q X (mkChain 40 p x) m := by
  dsimp only [mkChain, mkChainCont, chainSpec]; c0_hsteps; exact hQ

theorem chain80_hsteps (Γ : Env) (Q : Post [i64]) (X : XPost) (p v x : BitVec 64)
    (R : Mem 64 → Prop) (m : Mem 64) (hm : (cell (t := i64) p v ⋆ R) m)
    (hQ : Q (chainSpec 40 v (chainSpec 40 v x), ()) m) : wp Γ Q X (mkChain80 p x) m := by
  dsimp only [mkChain80, mkChain, mkChainCont, chainSpec]; c0_hsteps; exact hQ

theorem chain40_op2_hsteps (Γ : Env) (Q : Post [i64]) (X : XPost) (p v x : BitVec 64)
    (R : Mem 64 → Prop) (m : Mem 64) (hm : (cell (t := i64) p v ⋆ R) m)
    (hQ : Q (chainSpec 40 v x, ()) m) : wp Γ Q X (mkChainOp2 40 p x) m := by
  dsimp only [mkChainOp2, chainSpec]; c0_hsteps; exact hQ

/-! ## 4. Real `LratBytes` Function (`isWsByte`) via `c0_hsteps` -/

theorem lrat_isWsByte_hsteps {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {b : UInt8}
    {k : Bool → Expr Val Cont rs} {m : Mem 64}
    (hk : wp Γ Q X (k (((BitVec.ofNat 64 b.toNat == 32) ||
      (BitVec.ofNat 64 b.toNat - 9).ult 5))) m) :
    wp Γ Q X (isWsByte (BitVec.ofNat 64 b.toNat) k) m := by
  unfold isWsByte
  c0_hsteps
  exact hk

/-! ## 5. Real Kissat `D-Plain` (`plain_find_repl_body`, `plain_red_less_body`, `plain_lit_rank_body`) -/

section KissatRealBench
open scoped PlainPropTactics PlainReduceTactics

private theorem bv32_sle0_to_slt_false (y : BitVec 32) (h : (0#32).sle y = true) :
    y.slt 0#32 = false := by
  simp only [BitVec.sle, BitVec.slt, BitVec.toInt_zero, decide_eq_true_eq,
    decide_eq_false_iff_not] at h ⊢
  omega

private theorem bv32_sle0_false_to_slt (y : BitVec 32) (h : (0#32).sle y = false) :
    y.slt 0#32 = true := by
  simp only [BitVec.sle, BitVec.slt, BitVec.toInt_zero, decide_eq_false_iff_not,
    decide_eq_true_eq] at h ⊢
  omega

private theorem find_repl_ok_aux {c : PlainCfg} {s : PlainState} {cref r idx : Nat}
    {hi_lt : idx < s.arena.length}
    {hj_lt : (s.arena[idx]'hi_lt).toNat < s.vals.length}
    (hidx : idx = cref + 3 + r) (hcv : (s.arena[idx]'hi_lt).toNat < 2 * c.mv)
    (hsle : (0#32).sle ((s.vals[(s.arena[idx]'hi_lt).toNat]'hj_lt).signExtend 32) = true) :
    let cand := (s.arena[cref + 3 + r]?.getD 0#32).toNat
    cand < 2 * c.mv ∧ ((s.vals[cand]?.getD 0#8).signExtend 32).slt 0#32 = false := by
  subst hidx; dsimp only
  rw [List.getElem?_eq_getElem hi_lt, Option.getD_some,
    List.getElem?_eq_getElem hj_lt, Option.getD_some]
  exact ⟨hcv, bv32_sle0_to_slt_false _ hsle⟩

private theorem find_repl_bad_slt_aux {c : PlainCfg} {s : PlainState} {cref r idx : Nat}
    {hi_lt : idx < s.arena.length}
    {hj_lt : (s.arena[idx]'hi_lt).toNat < s.vals.length} (hidx : idx = cref + 3 + r)
    (h : (0#32).sle ((s.vals[(s.arena[idx]'hi_lt).toNat]'hj_lt).signExtend 32) = false) :
    plainFindReplBad c s cref r := by
  subst hidx; unfold plainFindReplBad; refine Or.inr ?_
  rw [List.getElem?_eq_getElem hi_lt, Option.getD_some,
    List.getElem?_eq_getElem hj_lt, Option.getD_some]
  exact bv32_sle0_false_to_slt _ h

private theorem find_repl_bad_oob_aux {c : PlainCfg} {s : PlainState} {cref r idx nlits : Nat}
    {hi_lt : idx < s.arena.length} (hidx : idx = cref + 3 + r)
    (hnl : nlits = 2 * c.mv) (h : ¬ (s.arena[idx]'hi_lt).toNat < nlits) :
    plainFindReplBad c s cref r := by
  subst hidx; unfold plainFindReplBad; refine Or.inl ?_
  rw [List.getElem?_eq_getElem hi_lt, Option.getD_some]; omega

/-- Kissat `D-Plain` `plain_find_repl_body` proved using only `c0_hsteps_nogrp` / `c0_hsteps`
(`O(1)` head stepping + two-level `AddrKey` dispatch). -/
theorem plain_find_repl_hsteps (Γ : Env) :
    ∀ args m Q X, plainFindReplSpec args m Q X → Func.wp Γ plain_find_repl_body args m Q X := by
  rintro ⟨h, cref, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hc3, hsz3, hfit, hm, hNone, hSome⟩
  have hmv := c.hmv; have har := c.harena; unfold dimacsBound at hmv har
  have hal := hlen.arena_len_arr; have hale := hlen.arena_len_le; have hvl := hlen.vals_len
  have hc1 : (cref + 1).toNat = cref.toNat + 1 := by bv_omega
  have hc2 : (cref + 2).toNat = cref.toNat + 2 := by bv_omega
  have hc2_lt : (cref + 2).toNat < s.arena.length := by omega
  have hc1_lt : (cref + 1).toNat < s.arena.length := by omega
  have hsz_eq : (s.arena[(cref + 2).toNat]'hc2_lt).toNat = arenaClauseSize s cref.toNat := by
    unfold arenaClauseSize
    rw [List.getElem?_eq_getElem (show cref.toNat + 2 < s.arena.length by omega), Option.getD_some]
    exact congrArg BitVec.toNat (by congr 1)
  c0_hsteps_nogrp
  generalize hsz_v : s.arena[(cref + 2).toNat]'hc2_lt = sz
  generalize hsr0_v : s.arena[(cref + 1).toNat]'hc1_lt = sr0
  have hsz_nat : sz.toNat = arenaClauseSize s cref.toNat := by rw [← hsz_v]; exact hsz_eq
  refine wp_join_group
    (fun (srch, ()) mj => 2 ≤ srch.toNat ∧ srch.toNat < sz.toNat ∧ mj = m) ?_ ?_
  · rintro _ ⟨srch, ⟨⟩⟩ mj ⟨hsrch2, hsrch_lt, rfl⟩
    c0_hsteps
    refine wp_loop_inv
      (fun (r, ()) ml => srch.toNat ≤ r.toNat ∧ r.toNat ≤ sz.toNat ∧ ml = mj ∧
        ∀ k, srch.toNat ≤ k → k < r.toNat → plainFindReplBad c s cref.toNat k)
      (fun (r, ()) _ => sz.toNat - r.toNat)
      (fun J hJ => by
        c0_hsteps; exact hJ _ _ ⟨Nat.le_refl _, by omega, rfl, fun _ _ _ => by omega⟩)
      (fun J (r, ()) ml ⟨hr_ge, hr_le, rfl, hseen1⟩ ih => ?_)
    c0_hsteps
    · have hok := find_repl_ok_aux (c := c) (cref := cref.toNat) (r := r.toNat)
        (by c0_bound) (by c0_bound) hc
      have hset : { s with arena := s.arena.set (cref + 1).toNat r } =
          { s with arena := s.arena.set (cref.toNat + 1) (BitVec.ofNat 32 r.toNat) } := by
        rw [hc1, bv_ofNat_toNat_eq]
      rw [hset] at hm; rw [bv32_zext64_eq]
      exact hSome r.toNat _ (by omega) (by omega) hok hm
    · refine ih _ _ (by c0_bound) ⟨by c0_bound, by c0_bound, rfl, fun k hk1 hk2 =>
        if hkr : k = r.toNat then
          hkr ▸ find_repl_bad_slt_aux (c := c) (cref := cref.toNat) (r := r.toNat) (by c0_bound) hc
        else hseen1 k hk1 (by c0_bound)⟩
    · refine ih _ _ (by c0_bound) ⟨by c0_bound, by c0_bound, rfl, fun k hk1 hk2 =>
        if hkr : k = r.toNat then
          hkr ▸ find_repl_bad_oob_aux (c := c) (cref := cref.toNat) (r := r.toNat)
            (by c0_bound) (by c0_bound) hc
        else hseen1 k hk1 (by c0_bound)⟩
    · refine wp_loop_inv
        (fun (r2, ()) ml2 => 2 ≤ r2.toNat ∧ r2.toNat ≤ srch.toNat ∧ ml2 = ml ∧
          ∀ k, 2 ≤ k → k < r2.toNat → plainFindReplBad c s cref.toNat k)
        (fun (r2, ()) _ => srch.toNat - r2.toNat)
        (fun J2 hJ2 => by
          c0_hsteps; exact hJ2 _ _ ⟨by decide, by c0_bound, rfl, fun _ _ _ => by c0_bound⟩)
        (fun J2 (r2, ()) ml2 ⟨hr2_ge, hr2_le, rfl, hseen2⟩ ih2 => ?_)
      c0_hsteps
      · have hok := find_repl_ok_aux (c := c) (cref := cref.toNat) (r := r2.toNat)
          (by c0_bound) (by c0_bound) hc
        have hset : { s with arena := s.arena.set (cref + 1).toNat r2 } =
            { s with arena := s.arena.set (cref.toNat + 1) (BitVec.ofNat 32 r2.toNat) } := by
          rw [hc1, bv_ofNat_toNat_eq]
        rw [hset] at hm; rw [bv32_zext64_eq]
        exact hSome r2.toNat _ hr2_ge (by omega) hok hm
      · refine ih2 _ _ (by c0_bound) ⟨by c0_bound, by c0_bound, rfl, fun k hk1 hk2 =>
          if hkr : k = r2.toNat then
            hkr ▸ find_repl_bad_slt_aux (c := c) (cref := cref.toNat) (r := r2.toNat)
              (by c0_bound) hc
          else hseen2 k hk1 (by c0_bound)⟩
      · refine ih2 _ _ (by c0_bound) ⟨by c0_bound, by c0_bound, rfl, fun k hk1 hk2 =>
          if hkr : k = r2.toNat then
            hkr ▸ find_repl_bad_oob_aux (c := c) (cref := cref.toNat) (r := r2.toNat)
              (by c0_bound) (by c0_bound) hc
          else hseen2 k hk1 (by c0_bound)⟩
      · refine hNone fun k hk2 hksz =>
          if hks : k < srch.toNat then hseen2 k hk2 (by omega) else hseen1 k (by omega) (by omega)
  · intro J hJ; c0_hsteps
    · exact hJ (2#32, ()) m ⟨by decide, by c0_bound, rfl⟩
    · exact hJ (2#32, ()) m ⟨by decide, by c0_bound, rfl⟩
    · exact hJ (sr0, ()) m ⟨by c0_bound, by c0_bound, rfl⟩

/-- Kissat `D-Plain` `plain_red_less_body` proved using `c0_hsteps`. -/
theorem plain_red_less_hsteps (Γ : Env) :
    ∀ args m Q X, plainRedLessSpec args m Q X → Func.wp Γ plain_red_less_body args m Q X := by
  rintro ⟨ar_ptr, a, b, ⟨⟩⟩ m Q X ⟨ar, R, ha, hb, hm, hQ⟩
  c0_hsteps; all_goals exact hQ _

/-- Kissat `D-Plain` `plain_lit_rank_body` proved using `c0_hsteps`. -/
theorem plain_lit_rank_hsteps (Γ : Env) :
    ∀ args m Q X, plainLitRankSpec args m Q X → Func.wp Γ plain_lit_rank_body args m Q X := by
  rintro ⟨vals_ptr, lvl_ptr, l, ⟨⟩⟩ m Q X ⟨vals, lvl, R, hvl, hll, hm, hQ⟩
  c0_hsteps; all_goals exact hQ _

end KissatRealBench

section C0HeadStepHelpers

private meta def wrapGoalMData : Lean.Elab.Tactic.TacticM Unit := do
  let g ← Lean.Elab.Tactic.getMainGoal
  let ty ← Lean.instantiateMVars (← g.getType)
  let g' ← g.change (Lean.mkMData {} ty) (checkDefEq := false)
  Lean.Elab.Tactic.replaceMainGoal [g']

theorem c0_hfast_jnz_wp {Γ : Env} {Q : Post [i32]} {X : XPost}
    {p : BitVec 64} {a : List (Val i32)} {R : Mem 64 → Prop} {m : Mem 64}
    (ha : 0 < a.length) (hm : (array (t := i32) p a ⋆ R) m) (c : Val .bool)
    (ht : c = true → ∀ m', (array (t := i32) p (a.set 0 (a[0]'ha + 1#32)) ⋆ R) m' →
      Q (1#32, ()) m')
    (hf : c = false → ∀ m', (array (t := i32) p (a.set 0 (a[0]'ha + 1#32)) ⋆ R) m' →
      Q (0#32, ()) m') :
    wp Γ Q X
      (.load i32 (Arg.imm (p + 0#64)) fun x =>
        .let_ (op2 (.add i32) (Arg.var x) (Arg.imm 1#32)) fun (y, _) =>
          .store (Arg.var y) (Arg.imm (p + 0#64))
            (.jnz (Arg.var c) (.ret (Arg.imm 1#32, ())) (.ret (Arg.imm 0#32, ())))) m := by
  c0_hfast
  · exact ht hc _ hm
  · exact hf hc _ hm

theorem c0_split_jnz_wp {Γ : Env} {Q : Post [i32]} {X : XPost}
    {m : Mem 64} (x : Val i32) (c : Val .bool)
    (ht : c = true → Q (x + 1#32, ()) m)
    (hf : c = false → Q (x + 2#32, ()) m) :
    wp Γ Q X
      (.let_ (op2 (.add i32) (Arg.var x) (Arg.imm 1#32)) fun (y, _) =>
        .jnz (Arg.var c) (.ret (Arg.var y, ()))
          (.let_ (op2 (.add i32) (Arg.var x) (Arg.imm 2#32)) fun (z, _) =>
            .ret (Arg.var z, ()))) m := by
  c0_split
  · exact ht hc
  · c0_hfast
    exact hf hc

theorem c0_split_mdata_wp {Γ : Env} {Q : Post [i32]} {X : XPost}
    {m : Mem 64} (x : Val i32) (c : Val .bool)
    (ht : c = true → Q (x + 1#32, ()) m)
    (hf : c = false → Q (0#32, ()) m) :
    wp Γ Q X
      (.let_ (op2 (.add i32) (Arg.var x) (Arg.imm 1#32)) fun (y, _) =>
        .jnz (Arg.var c) (.ret (Arg.var y, ())) (.ret (Arg.imm 0#32, ()))) m := by
  run_tac wrapGoalMData
  c0_split
  · exact ht hc
  · exact hf hc

theorem c0_to_group_mdata_wp {Γ : Env} {Q : Post [i32]} {X : XPost}
    {m : Mem 64} (x : Val i32)
    (hL : ∀ m', wp Γ Q X
      (.group (sig := [[i32]])
        (fun L => Blocks.cons (fun p => .jump L.1 (Arg.var p.1, ())) .nil)
        (fun L => .jump L.1 (Arg.var (x + 1#32), ()))) m') :
    wp Γ Q X
      (.let_ (op2 (.add i32) (Arg.var x) (Arg.imm 1#32)) fun (y, _) =>
        .group (sig := [[i32]])
          (fun L => Blocks.cons (fun p => .jump L.1 (Arg.var p.1, ())) .nil)
          (fun L => .jump L.1 (Arg.var y, ()))) m := by
  run_tac wrapGoalMData
  c0_to_group
  exact hL m

end C0HeadStepHelpers

/-! ## 6. Axiom Cleanliness Checks -/

#print axioms addrKey_plainMem_dispatch_check
#print axioms directOpProg_wp
#print axioms hstep_and_strip_le_test
#print axioms splitProg_wp
#print axioms hs_step_box_wp
#print axioms hs_div_arith_wp
#print axioms hs_unmatched_diag_test
#print axioms chain20_hsteps
#print axioms chain40_hsteps
#print axioms chain80_hsteps
#print axioms chain40_op2_hsteps
#print axioms lrat_isWsByte_hsteps
#print axioms plain_find_repl_hsteps
#print axioms plain_red_less_hsteps
#print axioms plain_lit_rank_hsteps
#print axioms c0_hfast_jnz_wp
#print axioms c0_split_jnz_wp
#print axioms c0_split_mdata_wp
#print axioms c0_to_group_mdata_wp

end LeanQbeTest.T.C0HeadStepTest
