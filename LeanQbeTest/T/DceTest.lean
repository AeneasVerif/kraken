module

public import LeanQbe.T.DceLemmas
public import LeanQbe.T.WPLemmas
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Logic.Rules

/-!
# Tests of `LeanQbe.T.Dce`

Covers:
- Cascading dead pure `let_` elimination in a single bottom-up pass,
- Multi-result partial-use retention (`addc` when only carry is used) vs dead `umulw` removal,
- Non-elimination of side effects (`load`, `store`, `call`, `exit`) even when results are unused,
- Sound dropping of dead float operations with NaN operands (exercising `OpCode.wp_exists`'s
  canonical quiet NaN witness) and dead guarded `udiv` under semantic non-zero preconditions,
- `group` block body liveness (outer variable used only inside block body is retained while dead
  outer bindings are dropped),
- Kernel `O(log N)` trie scaling (`t_kernel_rfl`) over a 30-instruction chain,
- Well-formedness (`t_wf_reify`, `Func.dce_wf`) and WP refinement (`Func.dce_spec`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.DceTest

open LeanQbe.T

/-! ## 1. Cascading dead pure chain elimination -/

def deadChainProg : Func [i64] [i64] := fun _ _ p =>
  let a := p.1
  .let_ (op2 (.add i64) (.var a) (.imm 1)) fun x =>
  .let_ (op2 (.mul i64) (.var x.1) (.imm 2)) fun y =>
  .let_ (op2 (.sub i64) (.var y.1) (.var a)) fun _z =>
  .ret (.var a, ())

theorem deadChainProg_dce_out : Func.dce deadChainProg = fun _ _ p =>
    .ret (.var p.1, ()) := by
  t_kernel_rfl

theorem deadChainProg_wf : deadChainProg.Wf := by t_wf_reify

theorem dce_deadChainProg_wf : (Func.dce deadChainProg).Wf := Func.dce_wf deadChainProg_wf

theorem deadChainProg_dce_spec (Γ : Env) (a : BitVec 64) (m : Mem 64) :
    Func.spec Γ (Func.dce deadChainProg) (a, ()) m
      (fun (r, ()) m' => r = a ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.dce_spec deadChainProg_wf
  dsimp only [Func.spec, Func.wp, deadChainProg]
  wp_unfold

/-! ## 2. Multi-result partial use vs completely dead multi-result -/

def multiResPartialProg : Func [i64, i64] [.bool] := fun _ _ p =>
  let a := p.1
  let b := p.2.1
  .let_ (op3 (.addc 64) (.var a) (.var b) (.imm false)) fun sc =>
  .let_ (op2 (.umulw 64) (.var a) (.var b)) fun _unused =>
  .ret (.var sc.2.1, ())

/-- `addc` is retained because its carry output is returned, whereas unused `umulw` is removed. -/
theorem multiResPartialProg_dce_out : Func.dce multiResPartialProg = fun _ _ p =>
    let a := p.1
    let b := p.2.1
    .let_ (op3 (.addc 64) (.var a) (.var b) (.imm false)) fun sc =>
    .ret (.var sc.2.1, ()) := by
  t_kernel_rfl

theorem multiResPartialProg_wf : multiResPartialProg.Wf := by t_wf_reify

theorem dce_multiResPartialProg_wf : (Func.dce multiResPartialProg).Wf :=
  Func.dce_wf multiResPartialProg_wf

theorem multiResPartialProg_dce_spec (Γ : Env) (a b : BitVec 64) (m : Mem 64) :
    Func.spec Γ (Func.dce multiResPartialProg) (a, b, ()) m
      (fun (c, ()) m' => c = decide (2 ^ 64 ≤ a.toNat + b.toNat) ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.dce_spec multiResPartialProg_wf
  dsimp only [Func.spec, Func.wp, multiResPartialProg]
  wp_unfold_all
  rfl

/-! ## 3. Side effects & control (`load`, `store`, `call`, `exit`) are never dropped -/

def effectsProg : Func [i64, i64, .bool] [i64] := fun _ _ p =>
  let a := p.1
  let ptr := p.2.1
  let c := p.2.2.1
  .let_ (op2 (.mul i64) (.var a) (.imm 9)) fun _deadPure =>
  .load i64 (.var ptr) fun _unusedLoad =>
  .store (.var a) (.var ptr)
    (.call "touch" (as := [i64]) (bs := []) (Arg.var a, ()) fun _unusedCall =>
     .jnz (.var c)
       (.ret (.var a, ()))
       (.exit "die" (as := [i64]) (Arg.var a, ())))

theorem effectsProg_dce_out : Func.dce effectsProg = fun _ _ p =>
    let a := p.1
    let ptr := p.2.1
    let c := p.2.2.1
    .load i64 (.var ptr) fun _ =>
    .store (.var a) (.var ptr)
      (.call "touch" (as := [i64]) (bs := []) (Arg.var a, ()) fun _ =>
       .jnz (.var c)
         (.ret (.var a, ()))
         (.exit "die" (as := [i64]) (Arg.var a, ()))) := by
  t_kernel_rfl

theorem effectsProg_wf : effectsProg.Wf := by t_wf_reify

theorem dce_effectsProg_wf : (Func.dce effectsProg).Wf := Func.dce_wf effectsProg_wf

/-! ## 4. Dead float NaN ops and guarded `udiv` (`OpCode.wp_exists`) -/

def qnan32 : BitVec 32 := 0x7fc00001#32

def floatUbProg : Func [i64, i64] [i64] := fun _ _ p =>
  let a := p.1
  let b := p.2.1
  .let_ (op2 (.fadd f32) (.imm qnan32) (.imm 0x3f800000#32)) fun _deadNaN =>
  .let_ (op2 (.udiv 64) (.var a) (.var b)) fun _deadDiv =>
  .ret (.var a, ())

/-- Both the dead quiet-NaN float addition and the dead `udiv` are eliminated. -/
theorem floatUbProg_dce_out : Func.dce floatUbProg = fun _ _ p =>
    .ret (.var p.1, ()) := by
  t_kernel_rfl

theorem floatUbProg_wf : floatUbProg.Wf := by t_wf_reify

theorem floatUbProg_dce_spec (Γ : Env) (a b : BitVec 64) (hb : b ≠ 0#64) (m : Mem 64) :
    Func.spec Γ (Func.dce floatUbProg) (a, b, ()) m
      (fun (r, ()) m' => r = a ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.dce_spec floatUbProg_wf
  dsimp only [Func.spec, Func.wp, floatUbProg]
  wp_unfold_all
  simp only [liftFloatRel2, floatResultWp]
  have hnan : (Float.Model.UnpackedFloat.add Fmt.s.format (unpackFloat .s qnan32)
      (unpackFloat .s 0x3f800000#32)).isNaN = true := by
    decide
  simp only [hnan, ↓reduceIte]
  exact fun _ _ => hb

/-! ## 5. `group` loop liveness: block body usage keeps outer binding alive -/

def groupLiveProg : Func [i64] [i64] := fun _ _ p =>
  let a := p.1
  .let_ (op2 (.add i64) (.var a) (.imm 10)) fun usedInBlk =>
  .let_ (op2 (.mul i64) (.var a) (.imm 99)) fun _deadOuter =>
  .group (sig := [[i64]])
    (fun (_blk, ()) =>
      .cons (fun x =>
        .let_ (op2 (.add i64) (.var x.1) (.var usedInBlk.1)) fun sum =>
        .let_ (op2 (.xor i64) (.var x.1) (.imm 7)) fun _deadInBlk =>
        .ret (.var sum.1, ()))
      .nil)
    (fun (blk, ()) => .jump blk (.var a, ()))

theorem groupLiveProg_dce_out : Func.dce groupLiveProg = fun _ _ p =>
    let a := p.1
    .let_ (op2 (.add i64) (.var a) (.imm 10)) fun usedInBlk =>
    .group (sig := [[i64]])
      (fun (_blk, ()) =>
        .cons (fun x =>
          .let_ (op2 (.add i64) (.var x.1) (.var usedInBlk.1)) fun sum =>
          .ret (.var sum.1, ()))
        .nil)
      (fun (blk, ()) => .jump blk (.var a, ())) := by
  t_kernel_rfl

theorem groupLiveProg_wf : groupLiveProg.Wf := by t_wf_reify

theorem dce_groupLiveProg_wf : (Func.dce groupLiveProg).Wf := Func.dce_wf groupLiveProg_wf

/-! ## 6. `NatSet` scaling: cascading dead chain of length 25 under `t_kernel_rfl` -/

def scaleChainGo {V : Ty → Type} {L : List Ty → Type} (retV : Arg V i64) :
    Nat → Arg V i64 → Expr V L [i64]
  | 0, _ => .ret (retV, ())
  | n + 1, v => .let_ (op2 (.add i64) v (.imm 1)) fun next => scaleChainGo retV n (.var next.1)

def scaleChain25 : Func [i64] [i64] := fun _ _ p =>
  scaleChainGo (.var p.1) 25 (.var p.1)

theorem scaleChain25_dce_out : Func.dce scaleChain25 = fun _ _ p =>
    .ret (.var p.1, ()) := by
  t_kernel_rfl

theorem scaleChain25_wf : scaleChain25.Wf := by t_wf_reify

theorem dce_scaleChain25_wf : (Func.dce scaleChain25).Wf := Func.dce_wf scaleChain25_wf

/-! ## 7. `jnz` sibling depth precision & 250-instruction dead-chain scaling -/

def jnzDepthProg : Func [.bool, i64] [i64] := fun _ _ p =>
  let c := p.1
  let a := p.2.1
  .jnz (.var c)
    (.let_ (op2 (.add i64) (.var a) (.imm 1)) fun t1 =>
     .ret (.var t1.1, ()))
    (.let_ (op2 (.add i64) (.var a) (.imm 2)) fun _e1 =>
     .ret (.var a, ()))

theorem jnzDepthProg_dce_out : Func.dce jnzDepthProg = fun _ _ p =>
    .jnz (.var p.1)
      (.let_ (op2 (.add i64) (.var p.2.1) (.imm 1)) fun t1 =>
       .ret (.var t1.1, ()))
      (.ret (.var p.2.1, ())) := by
  t_kernel_rfl

def scaleChain250 : Func [i64] [i64] := fun _ _ p =>
  scaleChainGo (.var p.1) 250 (.var p.1)

theorem scaleChain250_dce_out : Func.dce scaleChain250 = fun _ _ p =>
    .ret (.var p.1, ()) := by
  t_kernel_rfl

theorem scaleChain250_wf : scaleChain250.Wf := by t_wf_reify

theorem dce_scaleChain250_wf : (Func.dce scaleChain250).Wf := Func.dce_wf scaleChain250_wf

end LeanQbe.T.DceTest
