module

public import LeanQbe.T.CopyLemmas
public import LeanQbe.T.WPLemmas
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Logic.Rules

/-!
# Tests of `LeanQbe.T.Copy` (`T6`)

Covers:
- Multi-hop `OpCode.copy` propagation chains (`y = copy a; z = copy y; ret (add z 1)`),
- Tuple copy propagation (`mkpair` + `unpair` elimination forwarding `fst`/`snd` directly),
- Nested immediate pair decomposition (`unpair` on immediate pairs and constants produced from `mkpair`),
- Identity pair elimination (`x, y = unpair p; q = mkpair x y` → `q` resolves to `p`),
- Cross-`jnz` and `group` block copy propagation,
- Kernel reduction (`t_kernel_rfl`), well-formedness (`t_wf_reify`, `Func.copy_wf`), and WP
  refinement (`Func.copy_spec`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.CopyTest

open LeanQbe.T

/-! ## 1. Chained `copy` elimination -/

def copyChainProg : Func [i64] [i64] := fun _ _ p =>
  .let_ (op1 (.copy i64) (.var p.1)) fun y =>
  .let_ (op1 (.copy i64) (.var y.1)) fun z =>
  .let_ (op2 (.add i64) (.var z.1) (.imm 7)) fun w =>
  .let_ (op1 (.copy i64) (.var w.1)) fun out =>
  .ret (.var out.1, ())

theorem copyChainProg_out : Func.copy copyChainProg = fun _ _ p =>
    .let_ (op2 (.add i64) (.var p.1) (.imm 7)) fun w =>
    .ret (.var w.1, ()) := by
  t_kernel_rfl

theorem copyChainProg_wf : copyChainProg.Wf := by t_wf_reify

theorem copy_copyChainProg_wf : (Func.copy copyChainProg).Wf := Func.copy_wf copyChainProg_wf

theorem copyChainProg_spec (Γ : Env) (a : BitVec 64) (m : Mem 64) :
    Func.spec Γ (Func.copy copyChainProg) (a, ()) m
      (fun (r, ()) m' => r = a + 7#64 ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.copy_spec copyChainProg_wf
  dsimp only [Func.spec, Func.wp, copyChainProg]
  wp_unfold
  simp

/-! ## 2. `mkpair` / `unpair` projection forwarding -/

def pairProjProg : Func [i64, i64] [i64] := fun _ _ p =>
  let a := p.1
  let b := p.2.1
  .let_ (op2 (.mkpair i64 i64) (.var a) (.var b)) fun pr =>
  .let_ (op1 (.copy (i64.pair i64)) (.var pr.1)) fun prCopy =>
  .let_ (op1 (.unpair i64 i64) (.var prCopy.1)) fun xy =>
  .let_ (op2 (.add i64) (.var xy.1) (.var xy.2.1)) fun s =>
  .ret (.var s.1, ())

/-- Both `copy` and `unpair` disappear, forwarding `a` and `b` directly into `add`. -/
theorem pairProjProg_out : Func.copy pairProjProg = fun _ _ p =>
    let a := p.1
    let b := p.2.1
    .let_ (op2 (.mkpair i64 i64) (.var a) (.var b)) fun _ =>
    .let_ (op2 (.add i64) (.var a) (.var b)) fun s =>
    .ret (.var s.1, ()) := by
  t_kernel_rfl

theorem pairProjProg_wf : pairProjProg.Wf := by t_wf_reify

theorem copy_pairProjProg_wf : (Func.copy pairProjProg).Wf := Func.copy_wf pairProjProg_wf

theorem pairProjProg_spec (Γ : Env) (a b : BitVec 64) (m : Mem 64) :
    Func.spec Γ (Func.copy pairProjProg) (a, b, ()) m
      (fun (r, ()) m' => r = a + b ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.copy_spec pairProjProg_wf
  dsimp only [Func.spec, Func.wp, pairProjProg]
  wp_unfold

/-! ## 3. Nested immediate pair unpacking & `mkpair (fst p) (snd p) → p` identity -/

def pairIdentityProg : Func [i64.pair i64] [i64.pair i64, i64, i64] := fun _ _ p =>
  let pr := p.1
  .let_ (op1 (.unpair i64 i64) (.var pr)) fun xy =>
  .let_ (op2 (.mkpair i64 i64) (.var xy.1) (.var xy.2.1)) fun q =>
  .let_ (op1 (.unpair ((i64.pair i64)) i64) (.imm ((10#64, 20#64), 30#64))) fun nest =>
  .let_ (op1 (.unpair i64 i64) (.var nest.1)) fun ab =>
  .ret (.var q.1, .var ab.1, .var nest.2.1, ())

/-- `mkpair x y` folds away to `pr`, and nested immediate `unpair`s resolve directly to constants. -/
theorem pairIdentityProg_out : Func.copy pairIdentityProg = fun _ _ p =>
    let pr := p.1
    .let_ (op1 (.unpair i64 i64) (.var pr)) fun _ =>
    .ret (.var pr, .imm 10, .imm 30, ()) := by
  t_kernel_rfl

theorem pairIdentityProg_wf : pairIdentityProg.Wf := by t_wf_reify

theorem copy_pairIdentityProg_wf : (Func.copy pairIdentityProg).Wf := Func.copy_wf pairIdentityProg_wf

theorem pairIdentityProg_spec (Γ : Env) (a b : BitVec 64) (m : Mem 64) :
    Func.spec Γ (Func.copy pairIdentityProg) ((a, b), ()) m
      (fun (r0, r1, r2, ()) m' => r0 = (a, b) ∧ r1 = 10#64 ∧ r2 = 30#64 ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.copy_spec pairIdentityProg_wf
  dsimp only [Func.spec, Func.wp, pairIdentityProg]
  wp_unfold

/-! ## 4. `jnz` and `group` copy forwarding -/

def groupCopyProg : Func [.bool, i64, i64] [i64] := fun _ _ p =>
  let c := p.1
  let a := p.2.1
  let b := p.2.2.1
  .let_ (op2 (.mkpair i64 i64) (.var a) (.var b)) fun pr =>
  .group (sig := [[i64]])
    (fun (_blk, ()) =>
      .cons (fun arg =>
        .let_ (op1 (.copy i64) (.var arg.1)) fun acopy =>
        .let_ (op1 (.unpair i64 i64) (.var pr.1)) fun xy =>
        .let_ (op2 (.add i64) (.var acopy.1) (.var xy.2.1)) fun sum =>
        .ret (.var sum.1, ()))
      .nil)
    (fun (blk, ()) =>
      .jnz (.var c)
        (.let_ (op1 (.unpair i64 i64) (.var pr.1)) fun xy1 =>
         .jump blk (.var xy1.1, ()))
        (.let_ (op1 (.copy i64) (.var b)) fun bcopy =>
         .jump blk (.var bcopy.1, ())))

theorem groupCopyProg_out : Func.copy groupCopyProg = fun _ _ p =>
    let c := p.1
    let a := p.2.1
    let b := p.2.2.1
    .let_ (op2 (.mkpair i64 i64) (.var a) (.var b)) fun _ =>
    .group (sig := [[i64]])
      (fun (_blk, ()) =>
        .cons (fun arg =>
          .let_ (op2 (.add i64) (.var arg.1) (.var b)) fun sum =>
          .ret (.var sum.1, ()))
        .nil)
      (fun (blk, ()) =>
        .jnz (.var c)
          (.jump blk (.var a, ()))
          (.jump blk (.var b, ()))) := by
  t_kernel_rfl

theorem groupCopyProg_wf : groupCopyProg.Wf := by t_wf_reify

theorem copy_groupCopyProg_wf : (Func.copy groupCopyProg).Wf := Func.copy_wf groupCopyProg_wf

/-! ## 5. Multi-level nested pair identity, mixed-imm `mkpair`/`unpair`, & distinct-pair guard -/

def nestedPairGuardProg :
    Func [(i64.pair i64).pair i64, i64.pair i64]
         [(i64.pair i64).pair i64, i64, i64, i64.pair i64] := fun _ _ p =>
  let outer := p.1
  let other := p.2.1
  .let_ (op1 (.unpair (i64.pair i64) i64) (.var outer)) fun pz =>
  .let_ (op1 (.unpair i64 i64) (.var pz.1)) fun ab =>
  .let_ (op2 (.mkpair i64 i64) (.var ab.1) (.var ab.2.1)) fun q =>
  .let_ (op2 (.mkpair (i64.pair i64) i64) (.var q.1) (.var pz.2.1)) fun outer2 =>
  .let_ (op2 (.mkpair i64 i64) (.imm 42) (.var pz.2.1)) fun mixed =>
  .let_ (op1 (.unpair i64 i64) (.var mixed.1)) fun uv =>
  .let_ (op1 (.unpair i64 i64) (.var other)) fun cd =>
  .let_ (op2 (.mkpair i64 i64) (.var ab.1) (.var cd.2.1)) fun mismatch =>
  .ret (.var outer2.1, .var uv.1, .var uv.2.1, .var mismatch.1, ())

theorem nestedPairGuardProg_out : Func.copy nestedPairGuardProg = fun _ _ p =>
    let outer := p.1
    let other := p.2.1
    .let_ (op1 (.unpair (i64.pair i64) i64) (.var outer)) fun pz =>
    .let_ (op1 (.unpair i64 i64) (.var pz.1)) fun ab =>
    .let_ (op2 (.mkpair i64 i64) (.imm 42) (.var pz.2.1)) fun _ =>
    .let_ (op1 (.unpair i64 i64) (.var other)) fun cd =>
    .let_ (op2 (.mkpair i64 i64) (.var ab.1) (.var cd.2.1)) fun mismatch =>
    .ret (.var outer, .imm 42, .var pz.2.1, .var mismatch.1, ()) := by
  t_kernel_rfl

theorem nestedPairGuardProg_wf : nestedPairGuardProg.Wf := by t_wf_reify

theorem copy_nestedPairGuardProg_wf : (Func.copy nestedPairGuardProg).Wf :=
  Func.copy_wf nestedPairGuardProg_wf

theorem nestedPairGuardProg_spec (Γ : Env) (a b z c d : BitVec 64) (m : Mem 64) :
    Func.spec Γ (Func.copy nestedPairGuardProg) (((a, b), z), (c, d), ()) m
      (fun (r0, r1, r2, r3, ()) m' =>
        r0 = ((a, b), z) ∧ r1 = 42#64 ∧ r2 = z ∧ r3 = (a, d) ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.copy_spec nestedPairGuardProg_wf
  dsimp only [Func.spec, Func.wp, nestedPairGuardProg]
  wp_unfold
  rfl

end LeanQbe.T.CopyTest
