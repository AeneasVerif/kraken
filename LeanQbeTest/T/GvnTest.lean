module

public import LeanQbe.T.GvnLemmas
public import LeanQbe.T.WPLemmas
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Logic.Rules

/-!
# Tests of `LeanQbe.T.Gvn` (`T6`)

Ports E1's `GvnTest` to the typed IR `LeanQbe.T` and adds coverage for:
- Non-deduplication of effectful/control instructions (`load`, `store`, `call`, `exit`),
- Multi-result (`addc`) and vector (`v4i32`) CSE,
- Lexical sibling non-sharing across independent `jnz` branches,
- Lexical dominance across `group` entry and block bodies (parent scope dominates blocks,
  sibling blocks do not leak into each other),
- Kernel reduction (`t_kernel_rfl`), well-formedness (`t_wf_reify`, `Func.gvn_wf`), and WP
  refinement (`Func.gvn_spec`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.GvnTest

open LeanQbe.T

/-! ## 1. E1 `prog` ported: CSE across `jnz` while keeping repeated `load`s -/

/-- `x = add a b; y = add a b; jnz c, (u = add a b; z = mul y u; ret [z, x]), (load p; load p; ret [v, y])` -/
def prog : Func [i64, i64, .bool, i64] [i64, i64] := fun _ _ p =>
  let a := p.1
  let b := p.2.1
  let c := p.2.2.1
  let ptr := p.2.2.2.1
  .let_ (op2 (.add i64) (.var a) (.var b)) fun x =>
  .let_ (op2 (.add i64) (.var a) (.var b)) fun y =>
  .jnz (.var c)
    (.let_ (op2 (.add i64) (.var a) (.var b)) fun u =>
     .let_ (op2 (.mul i64) (.var y.1) (.var u.1)) fun z =>
     .ret (.var z.1, .var x.1, ()))
    (.load i64 (.var ptr) fun _ =>
     .load i64 (.var ptr) fun v =>
     .ret (.var v, .var y.1, ()))

/-- Both repeated `add`s (including inside the `then` branch) are replaced by `x`; both `load`s stay. -/
theorem prog_gvn_out : Func.gvn prog = fun _ _ p =>
    let a := p.1
    let b := p.2.1
    let c := p.2.2.1
    let ptr := p.2.2.2.1
    .let_ (op2 (.add i64) (.var a) (.var b)) fun x =>
    .jnz (.var c)
      (.let_ (op2 (.mul i64) (.var x.1) (.var x.1)) fun z =>
       .ret (.var z.1, .var x.1, ()))
      (.load i64 (.var ptr) fun _ =>
       .load i64 (.var ptr) fun v =>
       .ret (.var v, .var x.1, ())) := by
  t_kernel_rfl

theorem prog_wf : prog.Wf := by t_wf_reify

theorem gvn_prog_wf : (Func.gvn prog).Wf := Func.gvn_wf prog_wf

theorem prog_gvn_spec (Γ : Env) (a b : BitVec 64) (c : Bool) (ptr : BitVec 64) (m : Mem 64)
    (hp : ∃ v, loadVal m i64 ptr = some v) :
    Func.spec Γ (Func.gvn prog) (a, b, c, ptr, ()) m
      (fun (r0, r1, ()) m' => ((r0 = (a + b) * (a + b)) ∨ r1 = a + b) ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.gvn_spec prog_wf
  obtain ⟨v, hv⟩ := hp
  dsimp only [Func.spec, Func.wp, prog]
  wp_unfold
  simp [hv]

/-! ## 2. Effectful and control constructs are NEVER deduplicated -/

def effectsProg : Func [i64, i64, .bool, i64] [i64] := fun _ _ p =>
  let a := p.1
  let b := p.2.1
  let c := p.2.2.1
  let ptr := p.2.2.2.1
  .jnz (.var c)
    (.load i64 (.var ptr) fun _ =>
     .store (.var a) (.var ptr)
       (.load i64 (.var ptr) fun v2 =>
        .call "sideEffect" (as := [i64]) (bs := [i64]) (Arg.var a, ()) fun c1 =>
        .call "sideEffect" (as := [i64]) (bs := [i64]) (Arg.var a, ()) fun c2 =>
        .let_ (op2 (.add i64) (.var b) (.var c1.1)) fun _s1 =>
        .let_ (op2 (.add i64) (.var b) (.var c1.1)) fun s2 =>
        .let_ (op2 (.add i64) (.var s2.1) (.var c2.1)) fun res =>
        .let_ (op2 (.add i64) (.var res.1) (.var v2)) fun out =>
        .ret (.var out.1, ())))
    (.exit "abort" (as := [i64]) (Arg.var a, ()))

/-- `load`, `store`, `call`, and `exit` are never deduplicated, while the duplicate `s2 = add b c1`
becomes `s1`. -/
theorem effectsProg_gvn_out : Func.gvn effectsProg = fun _ _ p =>
    let a := p.1
    let b := p.2.1
    let c := p.2.2.1
    let ptr := p.2.2.2.1
    .jnz (.var c)
      (.load i64 (.var ptr) fun _ =>
       .store (.var a) (.var ptr)
         (.load i64 (.var ptr) fun v2 =>
          .call "sideEffect" (as := [i64]) (bs := [i64]) (Arg.var a, ()) fun c1 =>
          .call "sideEffect" (as := [i64]) (bs := [i64]) (Arg.var a, ()) fun c2 =>
          .let_ (op2 (.add i64) (.var b) (.var c1.1)) fun s1 =>
          .let_ (op2 (.add i64) (.var s1.1) (.var c2.1)) fun res =>
          .let_ (op2 (.add i64) (.var res.1) (.var v2)) fun out =>
          .ret (.var out.1, ())))
      (.exit "abort" (as := [i64]) (Arg.var a, ())) := by
  t_kernel_rfl

theorem effectsProg_wf : effectsProg.Wf := by t_wf_reify

theorem gvn_effectsProg_wf : (Func.gvn effectsProg).Wf := Func.gvn_wf effectsProg_wf

/-! ## 3. Multi-result (`addc`), vector (`v4i32`), and sibling branch non-leakage -/

def multiVecSiblingProg : Func [i64, i64, .bool, v4i32, v4i32] [i64, .bool, v4i32, i64] :=
  fun _ _ p =>
  let a := p.1
  let b := p.2.1
  let c := p.2.2.1
  let v1 := p.2.2.2.1
  let v2 := p.2.2.2.2.1
  .let_ (op3 (.addc 64) (.var a) (.var b) (.imm false)) fun r1 =>
  .let_ (op3 (.addc 64) (.var a) (.var b) (.imm false)) fun r2 =>
  .let_ (op2 (.and v4i32) (.var v1) (.var v2)) fun va =>
  .let_ (op2 (.and v4i32) (.var v1) (.var v2)) fun vb =>
  .jnz (.var c)
    (.let_ (op2 (.sub i64) (.var r2.1) (.imm 1)) fun t1 =>
     .ret (.var r2.1, .var r1.2.1, .var vb.1, .var t1.1, ()))
    (.let_ (op2 (.sub i64) (.var r1.1) (.imm 1)) fun e1 =>
     .ret (.var r1.1, .var r2.2.1, .var va.1, .var e1.1, ()))

/-- Duplicate `addc` and vector `and` are deduplicated, while the two independent `jnz` sibling
branches keep their own `sub` instructions. -/
theorem multiVecSiblingProg_gvn_out : Func.gvn multiVecSiblingProg = fun _ _ p =>
    let a := p.1
    let b := p.2.1
    let c := p.2.2.1
    let v1 := p.2.2.2.1
    let v2 := p.2.2.2.2.1
    .let_ (op3 (.addc 64) (.var a) (.var b) (.imm false)) fun r1 =>
    .let_ (op2 (.and v4i32) (.var v1) (.var v2)) fun va =>
    .jnz (.var c)
      (.let_ (op2 (.sub i64) (.var r1.1) (.imm 1)) fun t1 =>
       .ret (.var r1.1, .var r1.2.1, .var va.1, .var t1.1, ()))
      (.let_ (op2 (.sub i64) (.var r1.1) (.imm 1)) fun e1 =>
       .ret (.var r1.1, .var r1.2.1, .var va.1, .var e1.1, ())) := by
  t_kernel_rfl

theorem multiVecSiblingProg_wf : multiVecSiblingProg.Wf := by t_wf_reify

theorem gvn_multiVecSiblingProg_wf : (Func.gvn multiVecSiblingProg).Wf :=
  Func.gvn_wf multiVecSiblingProg_wf

theorem multiVecSiblingProg_gvn_spec (Γ : Env) (a b : BitVec 64) (c : Bool)
    (v1 v2 : Val v4i32) (m : Mem 64) :
    Func.spec Γ (Func.gvn multiVecSiblingProg) (a, b, c, v1, v2, ()) m
      (fun (s, _, _, d, ()) m' => s = a + b ∧ d = (a + b) - 1#64 ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.gvn_spec multiVecSiblingProg_wf
  dsimp only [Func.spec, Func.wp, multiVecSiblingProg]
  wp_unfold_all
  simp

/-! ## 4. `group` lexical scoping: outer CSE dominates blocks, siblings stay separate -/

def groupProg : Func [i64, .bool] [i64] := fun _ _ p =>
  let a := p.1
  let c := p.2.1
  .let_ (op2 (.add i64) (.var a) (.imm 5)) fun k =>
  .group (sig := [[i64], [i64]])
    (fun (_b0, _b1, ()) =>
      .cons (fun x =>
        .let_ (op2 (.add i64) (.var a) (.imm 5)) fun k0 =>
        .let_ (op2 (.mul i64) (.var x.1) (.imm 3)) fun _m1 =>
        .let_ (op2 (.mul i64) (.var x.1) (.imm 3)) fun m2 =>
        .let_ (op2 (.add i64) (.var m2.1) (.var k0.1)) fun sum =>
        .ret (.var sum.1, ()))
      (.cons (fun y =>
        .let_ (op2 (.mul i64) (.var y.1) (.imm 3)) fun n1 =>
        .let_ (op2 (.add i64) (.var n1.1) (.var k.1)) fun sum =>
        .ret (.var sum.1, ()))
      .nil))
    (fun (b0, b1, ()) =>
      .jnz (.var c) (.jump b0 (.var k.1, ())) (.jump b1 (.var a, ())))

theorem groupProg_gvn_out : Func.gvn groupProg = fun _ _ p =>
    let a := p.1
    let c := p.2.1
    .let_ (op2 (.add i64) (.var a) (.imm 5)) fun k =>
    .group (sig := [[i64], [i64]])
      (fun (_b0, _b1, ()) =>
        .cons (fun x =>
          .let_ (op2 (.mul i64) (.var x.1) (.imm 3)) fun m1 =>
          .let_ (op2 (.add i64) (.var m1.1) (.var k.1)) fun sum =>
          .ret (.var sum.1, ()))
        (.cons (fun y =>
          .let_ (op2 (.mul i64) (.var y.1) (.imm 3)) fun n1 =>
          .let_ (op2 (.add i64) (.var n1.1) (.var k.1)) fun sum =>
          .ret (.var sum.1, ()))
        .nil))
      (fun (b0, b1, ()) =>
        .jnz (.var c) (.jump b0 (.var k.1, ())) (.jump b1 (.var a, ()))) := by
  t_kernel_rfl

theorem groupProg_wf : groupProg.Wf := by t_wf_reify

theorem gvn_groupProg_wf : (Func.gvn groupProg).Wf := Func.gvn_wf groupProg_wf

/-! ## 5. Float NaN (`OpCode.wp_self`) and proof-indexed `OpCode` (`cmp`/`blend`/`bitcast`/`fcmp`) CSE -/

def qnan32 : BitVec 32 := 0x7fc00001#32

def floatProofProg : Func [v4i32, v4i32, v4f32, v4f32] [f32, f32, Ty.mask v4i32, v4i32, i64, Ty.mask v4f32] :=
  fun _ _ p =>
  let a := p.1
  let b := p.2.1
  let fa := p.2.2.1
  let fb := p.2.2.2.1
  .let_ (op2 (.fadd f32) (.imm qnan32) (.imm 0x3f800000#32)) fun n1 =>
  .let_ (op2 (.fadd f32) (.imm qnan32) (.imm 0x3f800000#32)) fun n2 =>
  .let_ (op2 (.eq v4i32) (.var a) (.var b)) fun m1 =>
  .let_ (op2 (.eq v4i32) (.var a) (.var b)) fun m2 =>
  .let_ (op3 (.blend v4i32) (.var m1.1) (.var a) (.var b)) fun bl1 =>
  .let_ (op3 (.blend v4i32) (.var m2.1) (.var a) (.var b)) fun bl2 =>
  .let_ (op1 (.bitcast (i32.pair i32) i64 rfl) (.imm (3#32, 4#32))) fun bc1 =>
  .let_ (op1 (.bitcast (i32.pair i32) i64 rfl) (.imm (3#32, 4#32))) fun bc2 =>
  .let_ (op2 (.fcmp .ord v4f32) (.var fa) (.var fb)) fun fm1 =>
  .let_ (op2 (.fcmp .ord v4f32) (.var fa) (.var fb)) fun fm2 =>
  .let_ (op2 (.add i64) (.var bc1.1) (.var bc2.1)) fun bsum =>
  .let_ (op2 (.and (Ty.mask v4f32)) (.var fm1.1) (.var fm2.1)) fun fmand =>
  .ret (.var n1.1, .var n2.1, .var m2.1, .var bl2.1, .var bsum.1, .var fmand.1, ())

theorem floatProofProg_gvn_out : Func.gvn floatProofProg = fun _ _ p =>
    let a := p.1
    let b := p.2.1
    let fa := p.2.2.1
    let fb := p.2.2.2.1
    .let_ (op2 (.fadd f32) (.imm qnan32) (.imm 0x3f800000#32)) fun n1 =>
    .let_ (op2 (.eq v4i32) (.var a) (.var b)) fun m1 =>
    .let_ (op3 (.blend v4i32) (.var m1.1) (.var a) (.var b)) fun bl1 =>
    .let_ (op1 (.bitcast (i32.pair i32) i64 rfl) (.imm (3#32, 4#32))) fun bc1 =>
    .let_ (op2 (.fcmp .ord v4f32) (.var fa) (.var fb)) fun fm1 =>
    .let_ (op2 (.add i64) (.var bc1.1) (.var bc1.1)) fun bsum =>
    .let_ (op2 (.and (Ty.mask v4f32)) (.var fm1.1) (.var fm1.1)) fun fmand =>
    .ret (.var n1.1, .var n1.1, .var m1.1, .var bl1.1, .var bsum.1, .var fmand.1, ()) := by
  t_kernel_rfl

theorem floatProofProg_wf : floatProofProg.Wf := by t_wf_reify

theorem floatProofProg_gvn_spec (Γ : Env) (a b : Val v4i32) (fa fb : Val v4f32) (m : Mem 64) :
    Func.spec Γ (Func.gvn floatProofProg) (a, b, fa, fb, ()) m
      (fun (r0, r1, _, _, bsum, _, ()) m' =>
        isFloatNaN .s r0 = true ∧ isFloatNaN .s r1 = true ∧ bsum = 0x0000000800000006#64 ∧ m' = m)
      (fun _ _ _ _ => False) := by
  apply Func.gvn_spec floatProofProg_wf
  dsimp only [Func.spec, Func.wp, floatProofProg]
  wp_unfold_all
  simp only [liftFloatRel2, floatResultWp]
  have hnan : (Float.Model.UnpackedFloat.add Fmt.s.format (unpackFloat .s qnan32)
      (unpackFloat .s 0x3f800000#32)).isNaN = true := by
    decide
  simp only [hnan, ↓reduceIte]
  intro r1 hr1 r2 hr2
  refine ⟨hr1, hr2, ?_⟩
  decide

/-! ## 6. `GvnTrie` kernel-cost scaling at 250 distinct instructions -/

def liveChainGo {V : Ty → Type} {L : List Ty → Type} : Nat → Arg V i64 → Expr V L [i64]
  | 0, acc => .ret (acc, ())
  | n + 1, acc => .let_ (op2 (.add i64) acc (.imm (BitVec.ofNat 64 (n + 1)))) fun y =>
      liveChainGo n (.var y.1)

def scaleLive250 : Func [i64] [i64] := fun _ _ p => liveChainGo 250 (.var p.1)

theorem scaleLive250_gvn_out : Func.gvn scaleLive250 = scaleLive250 := by
  t_kernel_rfl

theorem scaleLive250_wf : scaleLive250.Wf := by t_wf_reify

theorem gvn_scaleLive250_wf : (Func.gvn scaleLive250).Wf := Func.gvn_wf scaleLive250_wf

end LeanQbe.T.GvnTest
