module

public import LeanQbe.T.OptLemmas
public import LeanQbe.T.WPLemmas
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Logic.Rules
public import LeanQbe.T.Examples.UnionFind
public import LeanQbe.T.Examples.UnionFindLemmas

/-!
# Tests of `LeanQbe.T.Opt` (`T6`)

Ports E1's `OptTest` and exercises full-pipeline `Fold → Copy → Gvn → Fold → Dce` synergy:
- E1 `prog`: constant fold + CSE (`opt_prog_out`, `prog_opt_wf`, `prog_opt_spec`),
- Multi-pass synergy (`synergyProg`): constant fold → `mkpair`/`unpair` projection forwarding →
  GVN deduplication → second-pass self-subtraction fold (`sub x1 x2 → 0`) → dead code cleanup
  collapsing an entire chain down to `ret 0`,
- Combined vector (`v4i32`), multi-result (`addc`), `load`/`store` effect preservation, and
  `group` loop optimization (`fullOptProg`),
- Kernel evaluation (`t_kernel_rfl`), well-formedness (`t_wf_reify`, `Func.opt_wf`), and WP
  refinement (`Func.opt_spec`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.OptTest

open LeanQbe.T

/-! ## 1. E1 `OptTest.prog` ported -/

/-- `x = add 1 2; y = add a x; z = add a 3; ret [y, z]`: folding exposes the common subexpression,
and DCE removes the unused `x`. -/
def prog : Func [i64] [i64, i64] := fun _ _ p =>
  let a := p.1
  .let_ (op2 (.add i64) (.imm 1) (.imm 2)) fun x =>
  .let_ (op2 (.add i64) (.var a) (.var x.1)) fun y =>
  .let_ (op2 (.add i64) (.var a) (.imm 3)) fun z =>
  .ret (.var y.1, .var z.1, ())

theorem opt_prog_out : Func.opt prog = fun _ _ p =>
    .let_ (op2 (.add i64) (.var p.1) (.imm 3)) fun y =>
    .ret (.var y.1, .var y.1, ()) := by
  t_kernel_rfl

theorem prog_wf : prog.Wf := by t_wf_reify

theorem opt_prog_wf : (Func.opt prog).Wf := Func.opt_wf prog_wf

theorem prog_opt_spec (Γ : Env) (a : BitVec 64) (m : Mem 64) :
    Func.spec Γ (Func.opt prog) (a, ()) m
      (fun (r0, r1, ()) m' => r0 = a + 3#64 ∧ r1 = a + 3#64 ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.opt_spec prog_wf
  dsimp only [Func.spec, Func.wp, prog]
  wp_unfold
  simp

/-! ## 2. Five-pass synergy (`Fold → Copy → Gvn → Fold → Dce`) -/

/-- `c = add 10 20` (`30`) → `p = mkpair a c` → `u, v = unpair p` (`Copy`: `a, 30`) →
`x1 = add u v; x2 = add a 30` (`Gvn`: share `x1`) → `d = sub x1 x2` (`Fold #2`: `0`) →
`Dce`: drops unused `p`, `x1`, collapsing the entire function to `ret 0`! -/
def synergyProg : Func [i64] [i64] := fun _ _ p =>
  let a := p.1
  .let_ (op2 (.add i64) (.imm 10) (.imm 20)) fun c =>
  .let_ (op2 (.mkpair i64 i64) (.var a) (.var c.1)) fun pr =>
  .let_ (op1 (.unpair i64 i64) (.var pr.1)) fun uv =>
  .let_ (op2 (.add i64) (.var uv.1) (.var uv.2.1)) fun x1 =>
  .let_ (op2 (.add i64) (.var a) (.imm 30)) fun x2 =>
  .let_ (op2 (.sub i64) (.var x1.1) (.var x2.1)) fun d =>
  .ret (.var d.1, ())

theorem opt_synergyProg_out : Func.opt synergyProg = fun _ _ _ =>
    .ret (.imm 0, ()) := by
  t_kernel_rfl

theorem synergyProg_wf : synergyProg.Wf := by t_wf_reify

theorem opt_synergyProg_wf : (Func.opt synergyProg).Wf := Func.opt_wf synergyProg_wf

theorem synergyProg_opt_spec (Γ : Env) (a : BitVec 64) (m : Mem 64) :
    Func.spec Γ (Func.opt synergyProg) (a, ()) m
      (fun (r, ()) m' => r = 0#64 ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.opt_spec synergyProg_wf
  dsimp only [Func.spec, Func.wp, synergyProg]
  wp_unfold
  simp [BitVec.sub_self]

/-! ## 3. End-to-end vector, multi-result, memory, and `group` pipeline test -/

def fullOptProg : Func [i64, i64, v4i32] [i64, v4i32] := fun _ _ p =>
  let a := p.1
  let ptr := p.2.1
  let v := p.2.2.1
  .let_ (op2 (.xor v4i32) (.var v) (.imm ((0#32, 0#32), (0#32, 0#32)))) fun v0 =>
  .let_ (op1 (.copy v4i32) (.var v0.1)) fun v1 =>
  .let_ (op2 (.add v4i32) (.var v1.1) (.imm ((1#32, 1#32), (1#32, 1#32)))) fun _va =>
  .let_ (op2 (.add v4i32) (.var v) (.imm ((1#32, 1#32), (1#32, 1#32)))) fun vb =>
  .let_ (op3 (.addc 64) (.var a) (.imm 0) (.imm false)) fun ac =>
  .group (sig := [[i64]])
    (fun (_blk, ()) =>
      .cons (fun x =>
        .load i64 (.var ptr) fun mval =>
        .let_ (op2 (.mul i64) (.var ac.1) (.imm 8)) fun scaled =>
        .let_ (op2 (.add i64) (.var x.1) (.var scaled.1)) fun sum =>
        .let_ (op2 (.add i64) (.var sum.1) (.var mval)) fun res =>
        .let_ (op2 (.sub i64) (.var x.1) (.imm 99)) fun _dead =>
        .ret (.var res.1, .var vb.1, ()))
      .nil)
    (fun (blk, ()) =>
      .store (.var a) (.var ptr)
        (.jump blk (.var a, ())))

theorem opt_fullOptProg_out : Func.opt fullOptProg = fun _ _ p =>
    let a := p.1
    let ptr := p.2.1
    let v := p.2.2.1
    .let_ (op2 (.add v4i32) (.var v) (.imm ((1#32, 1#32), (1#32, 1#32)))) fun va =>
    .group (sig := [[i64]])
      (fun (_blk, ()) =>
        .cons (fun x =>
          .load i64 (.var ptr) fun mval =>
          .let_ (op2 (.shl i64) (.var a) (.imm 3)) fun scaled =>
          .let_ (op2 (.add i64) (.var x.1) (.var scaled.1)) fun sum =>
          .let_ (op2 (.add i64) (.var sum.1) (.var mval)) fun res =>
          .ret (.var res.1, .var va.1, ()))
        .nil)
      (fun (blk, ()) =>
        .store (.var a) (.var ptr)
          (.jump blk (.var a, ()))) := by
  t_kernel_rfl

theorem fullOptProg_wf : fullOptProg.Wf := by t_wf_reify

theorem opt_fullOptProg_wf : (Func.opt fullOptProg).Wf := Func.opt_wf fullOptProg_wf

/-! ## 4. Post-GVN `Copy` synergy (`Gvn` merges `unpair`s, second `Copy` eliminates `mkpair`) -/

def gvnCopyPairProg : Func [i64.pair i64, i64.pair i64] [i64.pair i64] := fun _ _ p =>
  let a := p.1
  let b := p.2.1
  .let_ (op2 (.add (i64.pair i64)) (.var a) (.var b)) fun p1 =>
  .let_ (op2 (.add (i64.pair i64)) (.var a) (.var b)) fun p2 =>
  .let_ (op1 (.unpair i64 i64) (.var p1.1)) fun xy1 =>
  .let_ (op1 (.unpair i64 i64) (.var p2.1)) fun xy2 =>
  .let_ (op2 (.mkpair i64 i64) (.var xy1.1) (.var xy2.2.1)) fun q =>
  .ret (.var q.1, ())

theorem opt_gvnCopyPairProg_out : Func.opt gvnCopyPairProg = fun _ _ p =>
    .let_ (op2 (.add (i64.pair i64)) (.var p.1) (.var p.2.1)) fun p1 =>
    .ret (.var p1.1, ()) := by
  t_kernel_rfl

theorem gvnCopyPairProg_wf : gvnCopyPairProg.Wf := by t_wf_reify

theorem opt_gvnCopyPairProg_wf : (Func.opt gvnCopyPairProg).Wf := Func.opt_wf gvnCopyPairProg_wf

theorem gvnCopyPairProg_opt_spec (Γ : Env) (a b : BitVec 64 × BitVec 64) (m : Mem 64) :
    Func.spec Γ (Func.opt gvnCopyPairProg) (a, b, ()) m
      (fun (r, ()) m' => r = (a.1 + b.1, a.2 + b.2) ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.opt_spec gvnCopyPairProg_wf
  dsimp only [Func.spec, Func.wp, gvnCopyPairProg]
  wp_unfold

/-! ## 5. Real `tqbe` program (`UnionFind`) & 250-instruction full-pipeline scaling -/

theorem uf_find_opt_checkTFlat :
    (Func.opt LeanQbe.T.Examples.UnionFind.find).checkTFlat = true := by
  t_kernel_rfl

theorem uf_unionInline_opt_checkTFlat :
    (Func.opt LeanQbe.T.Examples.UnionFind.unionInline).checkTFlat = true := by
  t_kernel_rfl

theorem uf_find_opt_wf :
    (Func.opt LeanQbe.T.Examples.UnionFind.find).Wf :=
  Func.opt_wf LeanQbe.T.Examples.UnionFind.find_wf

def liveChainGo {V : Ty → Type} {L : List Ty → Type} : Nat → Arg V i64 → Expr V L [i64]
  | 0, acc => .ret (acc, ())
  | n + 1, acc => .let_ (op2 (.add i64) acc (.imm (BitVec.ofNat 64 (n + 1)))) fun y =>
      liveChainGo n (.var y.1)

def scaleLive250 : Func [i64] [i64] := fun _ _ p => liveChainGo 250 (.var p.1)

theorem scaleLive250_opt_out : Func.opt scaleLive250 = scaleLive250 := by
  t_kernel_rfl

theorem scaleLive250_opt_wf : (Func.opt scaleLive250).Wf :=
  Func.opt_wf (by t_wf_reify)

/-! ## 6. Staged `O-M2` pipelines (`Func.earlyOpt`, `Func.lateOpt`, `simplifyGroupFast`) -/

/-- Diamond join (`if x <s y then a + 10 else a - 10`) collapses under `lateOpt` via
`ifOptBits → simplifyGroupFast`. -/
def stagedDiamond : Func [i64, i64, i64] [i64] := fun _ _ (x, y, a, ()) =>
  .let_ (op2 (.cmp .slt i64) (.var x) (.var y)) fun (c, ()) =>
  .group (sig := [[i64]])
    (fun _ => .cons (fun (r, ()) => .ret (.var r, ())) .nil)
    (fun (J, ()) =>
      .jnz (.var c)
        (.let_ (op2 (.add i64) (.var a) (.imm 10)) fun (t, ()) => .jump J (.var t, ()))
        (.let_ (op2 (.sub i64) (.var a) (.imm 10)) fun (e, ()) => .jump J (.var e, ())))

theorem stagedDiamond_earlyOpt_out : Func.earlyOpt stagedDiamond = fun _ _ (x, y, a, ()) =>
    .let_ (op2 (.cmp .slt i64) (.var x) (.var y)) fun (c, ()) =>
    .group (sig := [[i64]])
      (fun _ => .cons (fun (r, ()) => .ret (.var r, ())) .nil)
      (fun (J, ()) =>
        .jnz (.var c)
          (.let_ (op2 (.add i64) (.var a) (.imm 10)) fun (t, ()) => .jump J (.var t, ()))
          (.let_ (op2 (.sub i64) (.var a) (.imm 10)) fun (e, ()) => .jump J (.var e, ()))) := by
  t_kernel_rfl

theorem stagedDiamond_lateOpt_out :
    Func.lateOpt (Func.earlyOpt stagedDiamond) = fun _ _ (x, y, a, ()) =>
      .let_ (op2 (.cmp .slt i64) (.var x) (.var y)) fun (c, ()) =>
      .let_ (op2 (.add i64) (.var a) (.imm 10)) fun (t, ()) =>
      .let_ (op2 (.sub i64) (.var a) (.imm 10)) fun (e, ()) =>
      .let_ (op3 (.select i64) (.var c) (.var t) (.var e)) fun (s, ()) =>
      .ret (.var s, ()) := by
  t_kernel_rfl

theorem stagedDiamond_wf : stagedDiamond.Wf := by t_wf_reify

theorem stagedDiamond_earlyOpt_wf : (Func.earlyOpt stagedDiamond).Wf :=
  Func.earlyOpt_wf stagedDiamond_wf

theorem stagedDiamond_lateOpt_wf : (Func.lateOpt (Func.earlyOpt stagedDiamond)).Wf :=
  Func.lateOpt_wf stagedDiamond_earlyOpt_wf

theorem stagedDiamond_earlyLate_spec (Γ : Env) (x y a : BitVec 64) (m : Mem 64) :
    Func.spec Γ (Func.lateOpt (Func.earlyOpt stagedDiamond)) (x, y, a, ()) m
      (fun (r, ()) m' =>
        r = (if BitVec.slt x y then a + 10#64 else a - 10#64) ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.lateOpt_spec stagedDiamond_earlyOpt_wf
  apply Func.earlyOpt_spec stagedDiamond_wf
  dsimp only [Func.spec, Func.wp, stagedDiamond]
  simp only [wp, Op.wp, OpCode.wp, op2, vals, Arg.val, liftCmp, CmpOp.evalBits, i64, Closed]
  intro ⟨J, ⟨⟩⟩ hJ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact hJ.1 (a + 10#64, ()) m ⟨by simp [h], rfl⟩
  · exact hJ.1 (a - 10#64, ()) m ⟨by simp [h], rfl⟩

/-- Post-`Legal` synergy across `divConst` (`x /u 2` -> `lshr 1`), `memLoad` (store-to-load
forwarding), `deadLoadElim` (unused load), and `assumeElim` (`.jnz c _ .hlt`). -/
def lateSynergyProg : Func [i64, i64, .bool] [i64] := fun _ _ (x, ptr, cond, ()) =>
  .store (.var x) (.var ptr)
    (.load i64 (.var ptr) fun v =>
      .load i64 (.var ptr) fun _unused =>
        .let_ (op2 (.udiv 64) (.var v) (.imm 2)) fun (q, ()) =>
          .jnz (.var cond) (.ret (.var q, ())) .hlt)

theorem lateSynergyProg_lateOpt_out : Func.lateOpt lateSynergyProg = fun _ _ (x, ptr, _c, ()) =>
    .store (.var x) (.var ptr)
      (.let_ (op2 (.lshr i64) (.var x) (.imm 1)) fun (q, ()) =>
        .ret (.var q, ())) := by
  t_kernel_rfl

theorem lateSynergyProg_wf : lateSynergyProg.Wf := by t_wf_reify

theorem lateSynergyProg_lateOpt_wf : (Func.lateOpt lateSynergyProg).Wf :=
  Func.lateOpt_wf lateSynergyProg_wf

theorem lateSynergyProg_lateOpt_spec (Γ : Env) (x ptr o : BitVec 64) (cond : Bool)
    (hcond : cond = true) (R : Mem 64 → Prop) (m : Mem 64) (hm : (cell64 ptr o ⋆ R) m) :
    Func.spec Γ (Func.lateOpt lateSynergyProg) (x, ptr, cond, ()) m
      (fun (r, ()) m' => r = x / 2#64 ∧ (cell64 ptr x ⋆ R) m')
      (fun _ _ _ _ => False) := by
  subst hcond
  apply Func.lateOpt_spec lateSynergyProg_wf
  dsimp only [Func.spec, Func.wp, lateSynergyProg]
  wp_unfold
  obtain ⟨hst, hm1⟩ := store_cell64 x hm
  refine ⟨hst, ?_⟩
  have hl : loadVal _ i64 ptr = some x := loadVal_cell64 hm1
  refine ⟨x, hl, x, hl, by decide, ?_⟩
  exact ⟨fun _ => ⟨rfl, hm1⟩, fun h => by cases h⟩

#print axioms LeanQbe.T.Func.renorm_spec
#print axioms LeanQbe.T.Func.simplifyGroupFast_spec
#print axioms LeanQbe.T.Func.earlyOpt_wf
#print axioms LeanQbe.T.Func.earlyOpt_spec
#print axioms LeanQbe.T.Func.lateOpt_wf
#print axioms LeanQbe.T.Func.lateOpt_spec
#print axioms stagedDiamond_earlyLate_spec
#print axioms lateSynergyProg_lateOpt_spec

end LeanQbe.T.OptTest
