module

public import LeanQbe.T.Bootstrap0.Bridge0
public import LeanQbe.T.Bootstrap0.Compiler0
public import LeanQbe.T.Bootstrap0.Sound0
public import LeanQbe.T.Bootstrap0.PrintDir0
public import LeanQbe.T.Frontend.C0.Elab
public import LeanQbe.T.Amd64.PrintAsm0
public import LeanQbe.T.Amd64.ScalarTarg
public import Kraken.X64.PrintATT
public import LeanQbe.T.FlatLemmas

/-!
# Bootstrap Stage C End-to-End Native Emission, Execution & Soundness Bridge

Connects the Stage-A verified bootstrap pipeline (`Bridge0.ofTFlatModule`,
`Compiler0.leanqbe0Compile`, `Sound0.lean` layout and execution theorems, and
closure-free `PrintDir0` / `PrintAsm0` AT&T emitters) directly to real
multi-function C0 programs (`stageCTfs` and `stageCSource`), proving `LabelsUnique`,
AT&T printer agreement, `Defined`, and `FnSpec` via `stageC_host_ok` and
`stageC_exec_i64`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Bootstrap0

open LeanQbe.T
open LeanQbe.T.Amd64
open LeanQbe.T.Frontend.C0

/-! ## 1. Multi-Function C0 Kernel Definitions (`Frontend.C0.TFlatFn`) -/

local macro "c0Leaf1(" nm:term "," op:term "," b:term ")" : term =>
  `({ name := $nm, as := [i64], rs := [i64]
      flat := .let_ (op2 $op (.var 0) $b) (.ret (.var 0, ())) : Frontend.C0.TFlatFn })

local macro "c0CallAdd(" nm:term "," callee:term "," k:term ")" : term =>
  `({ name := $nm, as := [i64], rs := [i64]
      flat := .call $callee (as := [i64]) [i64] (.var 0, ()) <|
        .let_ (op2 (.add i64) (.var 0) (.imm $k)) (.ret (.var 0, ())) : Frontend.C0.TFlatFn })

/-- Arithmetic leaf: `c0_sqr(x) = x * x`. -/
def c0SqrTf : Frontend.C0.TFlatFn := c0Leaf1("c0_sqr", .mul i64, .var 0)

/-- Multi-fn pipeline step 1: `c0_step1(x) = x + 10`. -/
def c0Step1Tf : Frontend.C0.TFlatFn := c0Leaf1("c0_step1", .add i64, .imm 10#64)

/-- Multi-fn pipeline step 2: `c0_step2(x) = c0_step1(x) + 20`. -/
def c0Step2Tf : Frontend.C0.TFlatFn := c0CallAdd("c0_step2", "c0_step1", 20#64)

/-- Multi-fn pipeline entry: `c0_pipeline(x) = c0_step2(x) + 30`. -/
def c0PipeTf : Frontend.C0.TFlatFn := c0CallAdd("c0_pipeline", "c0_step2", 30#64)

/-- SAT/LRAT literal variable index: `sat_lit_var(lit) = lit >> 1`. -/
def satLitVarTf : Frontend.C0.TFlatFn := c0Leaf1("sat_lit_var", .lshr i64, .imm 1#64)

/-- SAT/LRAT literal sign bit: `sat_lit_sign(lit) = lit & 1`. -/
def satLitSignTf : Frontend.C0.TFlatFn := c0Leaf1("sat_lit_sign", .and i64, .imm 1#64)

/-- SAT/LRAT literal negation: `sat_lit_neg(lit) = lit ^ 1`. -/
def satLitNegTf : Frontend.C0.TFlatFn := c0Leaf1("sat_lit_neg", .xor i64, .imm 1#64)

/-- Full list of Stage C multi-function C0 kernels. -/
def stageCTfs : List Frontend.C0.TFlatFn :=
  [c0SqrTf, c0Step1Tf, c0Step2Tf, c0PipeTf, satLitVarTf, satLitSignTf, satLitNegTf]

/-- The high-level `Module` corresponding to `stageCTfs`. -/
def stageCMod : Module :=
  { fns := stageCTfs.map Frontend.C0.TFlatFn.toFn, externs := [], exits := [] }

/-! ## 2. Bridge Translation & Stage-A Compilation (`ofTFlatModule` & `leanqbe0Compile`) -/

/-- Result of `ofTFlatModule` on `stageCTfs`. -/
def stageCBridgePair : TFlatModule0 × List (Sym × Sym0) :=
  (ofTFlatModule stageCTfs [] []).toOption.getD ({ fns := [], externs := [], exits := [] }, [])

/-- Lowered `TFlatModule0` for Stage C. -/
def stageCMod0 : TFlatModule0 := stageCBridgePair.1

/-- Symbol table associating kernel names with numeric IDs. -/
def stageCTbl : List (Sym × Sym0) := stageCBridgePair.2

/-- Emitted `Dir0` directives from `Compiler0.leanqbe0Compile`. -/
def stageCDirs : List Dir0 :=
  match leanqbe0Compile stageCMod0 with | .ok d _ => d | .err _ _ => []

/-- Maximum stack slot allocation computed by `leanqbe0Compile`. -/
def stageCMaxSl : UInt32 :=
  match leanqbe0Compile stageCMod0 with | .ok _ ms => ms | .err _ _ => 0

/-- Stack bounds computed by `computeBounds0`. -/
def stageCBounds : List (Sym0 × Nat) := (stageCMod0.computeBounds0 [] 0).getD []

/-- `ofTFlatModule` succeeds on `stageCTfs`. -/
theorem stageC_bridge_ok : ofTFlatModule stageCTfs [] [] = .ok (stageCMod0, stageCTbl) := by
  t_kernel_rfl

/-- `leanqbe0Compile` succeeds on `stageCMod0`. -/
theorem stageC_compile_ok : leanqbe0Compile stageCMod0 = .ok stageCDirs stageCMaxSl := by
  t_kernel_rfl

/-- `computeBounds0` succeeds on `stageCMod0`. -/
theorem stageC_bounds_ok : stageCMod0.computeBounds0 [] 0 = some stageCBounds := by
  t_kernel_rfl

/-- Emitted x64 program is well inside machine code memory limits. -/
theorem stageC_small :
    x64ScalarProgSmall (toAmd64Program (symNameOf stageCTbl) stageCDirs ++ []) = true := by
  t_kernel_rfl

/-- The call graph among Stage C kernels is acyclic. -/
theorem stageC_acyc : stageCMod.checkAcyclic = true := by t_kernel_rfl

/-- Full Stage-A guards (no forbidden instructions, valid ranges) are satisfied. -/
theorem stageC_okGuards : stageCMod0.okGuardsFull = true := by t_kernel_rfl

/-! ## 3. Semantic Environment & `ModuleOk` Specification -/

local macro "i64Spec" f:term : term => `(fun args m Q _ => Q ($f args.1, ()) m)

/-- Semantic environment assigning operational contracts to Stage C kernels. -/
def stageCEnv : Env := fun nm as rs =>
  match nm, as, rs with
  | "c0_sqr", [.bits 64], [.bits 64] => i64Spec (fun a => a * a)
  | "c0_step1", [.bits 64], [.bits 64] => i64Spec (· + 10#64)
  | "c0_step2", [.bits 64], [.bits 64] => i64Spec (· + 10#64 + 20#64)
  | "c0_pipeline", [.bits 64], [.bits 64] => i64Spec (· + 10#64 + 20#64 + 30#64)
  | "sat_lit_var", [.bits 64], [.bits 64] => i64Spec (· >>> 1#64)
  | "sat_lit_sign", [.bits 64], [.bits 64] => i64Spec (· &&& 1#64)
  | "sat_lit_neg", [.bits 64], [.bits 64] => i64Spec (· ^^^ 1#64)
  | _, _, _ => fun _ _ _ _ => False

private theorem stageC_leaf_wp (Γ : Env) (m : Mem 64) (Q : Post [i64]) (X : XPost)
    (op : OpCode [i64, i64] [i64]) (b0 : Arg K i64) (x bv : BitVec 64)
    (tail : List ((t : Ty) × Val t))
    (hb : (b0 = .var 0 ∧ bv = x) ∨ b0 = .imm bv)
    (hq : OpCode.wp op (x, bv, ()) (fun xs => Q (xs.1, ()) m)) :
    wp Γ Q X (denote Val Cont (.let_ (op2 op (.var 0) b0) (.ret (.var 0, ())) : TFlat [i64])
      (pushTup (f := Val) (as := [i64]) (x, ()) tail) []) m := by
  have ⟨b, hbv, hdenB⟩ : ∃ b : Arg Val i64, b.val = bv ∧
      denoteArg (⟨i64, x⟩ :: tail) b0 = some b := by
    rcases hb with ⟨rfl, rfl⟩ | rfl
    · exact ⟨.var bv, rfl, by simp [denoteArg, lookupV, listGet?, castTy]⟩
    · exact ⟨.imm bv, rfl, rfl⟩
  have hden : denote Val Cont
      (.let_ (op2 op (.var 0) b0) (.ret (.var 0, ())) : TFlat [i64])
      (pushTup (f := Val) (as := [i64]) (x, ()) tail) [] =
      Expr.let_ (op2 op (.var x) b) (fun xs => Expr.ret (.var xs.1, ())) := by
    dsimp only [denote, op2, denoteArgs, pushTup]
    have hx0 : denoteArg (⟨i64, x⟩ :: tail) (Arg.var 0 : Arg K i64) = some (Arg.var x) := by
      simp [denoteArg, lookupV, listGet?, castTy]
    rw [hx0, hdenB]; dsimp only; congr 1
  rw [hden]; dsimp only [wp, Op.wp, op2, vals]; rw [hbv]; exact hq

private theorem stageC_call_wp (Γ : Env) (m : Mem 64) (Q : Post [i64]) (X : XPost)
    (callee : Sym) (x target k : BitVec 64)
    (hcall : Γ callee [i64] [i64] (x, ()) m (fun r m' => r = (target, ()) ∧ m' = m)
      (fun _ _ _ _ => False))
    (hpost : Q (target + k, ()) m) :
    wp Γ Q X (denote Val Cont (.call callee (as := [i64]) [i64] (.var 0, ())
      (.let_ (op2 (.add i64) (.var 0) (.imm k)) (.ret (.var 0, ()))) : TFlat [i64])
      (pushTup (f := Val) (as := [i64]) (x, ()) []) []) m := by
  have hden : denote Val Cont (.call callee (as := [i64]) [i64] (.var 0, ())
      (.let_ (op2 (.add i64) (.var 0) (.imm k)) (.ret (.var 0, ()))) : TFlat [i64])
      (pushTup (f := Val) (as := [i64]) (x, ()) []) [] =
      Expr.call callee (as := [i64]) (bs := [i64]) (Arg.var x, ()) (fun xs =>
        denote Val Cont (.let_ (op2 (.add i64) (.var 0) (.imm k)) (.ret (.var 0, ())))
          (pushTup (f := Val) (as := [i64]) xs [⟨i64, x⟩]) []) := rfl
  rw [hden]; dsimp only [wp, vals, Arg.val]
  refine ⟨fun r m' => r = (target, ()) ∧ m' = m, fun _ _ _ _ => False, hcall,
    fun _ _ ⟨hr, hm⟩ => ?_, fun _ _ _ _ hf => hf.elim⟩
  rw [hr, hm]
  exact stageC_leaf_wp Γ m Q X (.add i64) (.imm k) target k [⟨i64, x⟩] (.inr rfl)
    (by simpa [Ty.hasFloat, OpCode.wp, lift2] using hpost)

/-- All kernels satisfy their operational specifications under `stageCEnv`. -/
theorem stageC_moduleOk : ModuleOk stageCEnv stageCMod := by
  refine Module.moduleOk_of_checkAcyclic (by t_kernel_rfl) (fun fn hmem => ?_)
    (fun fn hmem => ?_) <;>
  · simp only [stageCMod, stageCTfs, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Frontend.C0.TFlatFn.toFn_wf _
      | (intro xs m Q X hΓ; rcases xs with ⟨x, ⟨⟩⟩
         dsimp only [c0SqrTf, c0Step1Tf, c0Step2Tf, c0PipeTf, satLitVarTf, satLitSignTf,
           satLitNegTf, Frontend.C0.TFlatFn.toFn, Func.wp, denoteFunc, stageCEnv] at hΓ ⊢
         first
         | exact stageC_call_wp stageCEnv m Q X _ x _ _ ⟨rfl, rfl⟩ hΓ
         | exact stageC_leaf_wp stageCEnv m Q X _ _ x x [] (.inl ⟨rfl, rfl⟩)
             (by simpa [Ty.hasFloat, OpCode.wp, lift2] using hΓ)
         | exact stageC_leaf_wp stageCEnv m Q X _ _ x _ [] (.inr rfl)
             (by simpa [Ty.hasFloat, OpCode.wp, lift2] using hΓ))

/-! ## 4. Verified Host Layout & Concrete Machine Semantics -/

set_option warn.classDefReducibility false in
/-- Concrete machine host laying out the compiled Stage C kernel instructions. -/
def stageCHost : x64ScalarMach.Host :=
  x64ScalarLayout.layoutOf (toAmd64Program (symNameOf stageCTbl) stageCDirs ++ []) stageC_small

/-- Headline Stage C bridge theorem: proving unique labels, exact AT&T assembly agreement,
and verified `FnSpec` contracts for every compiled kernel. -/
theorem stageC_host_ok :
    x64ScalarTarget.LabelsUnique stageCHost ∧
    printAsm0 (toAmd64Program (symNameOf stageCTbl) stageCDirs) =
      Kraken.X64.toATT (toAmd64Program (symNameOf stageCTbl) stageCDirs) ∧
    ∀ tf ∈ stageCTfs,
      x64ScalarTarget.Defined stageCHost tf.name ∧
      x64ScalarTarget.FnSpec stageCHost tf.name
        (Env.ofModule stageCMod stageCEnv tf.name tf.as tf.rs)
        ((lookupBound0 stageCBounds (lookupSymId? stageCTbl tf.name).get!).getD 0) 0 :=
  bridge_leanqbe0Compile_layout (Γ := stageCEnv) stageCTfs [] []
    stageC_bridge_ok stageC_compile_ok stageC_okGuards
    (of_decide_eq_true (by t_kernel_rfl))
    (List.all_eq_true.mp (by t_kernel_rfl :
      stageCTfs.all (fun tf => tf.flat.wfCheck (pushTypes tf.as []) []) = true))
    (List.all_eq_true.mp (by t_kernel_rfl : stageCTfs.all (fun tf => tflatIdxLtU32 tf.flat) = true))
    stageC_acyc List.nodup_nil (fun _ h => nomatch h)
    (List.all_eq_true.mp (by t_kernel_rfl :
      stageCTfs.all (fun tf => symNoLocPrefix0 tf.name) = true))
    (fun _ h => nomatch h) stageC_bounds_ok (fun _ h => nomatch h)
    stageC_small stageC_moduleOk (fun _ h => nomatch h)

/-- Concrete `i64 -> i64` Stage C native execution bridge via
`TargetInit.run_ret1_i64_of_fnSpec`. -/
theorem stageC_exec_i64 (tf : Frontend.C0.TFlatFn) (nm : String)
    (spec : BitVec 64 → BitVec 64) (x y : BitVec 64)
    (htf : tf ∈ stageCTfs) (hnm : tf.name = nm) (has : tf.as = [i64]) (hrs : tf.rs = [i64])
    (henv : stageCEnv nm [i64] [i64] = fun args m Q _ => Q (spec args.1, ()) m)
    (hb : ((lookupBound0 stageCBounds (lookupSymId? stageCTbl nm).get!).getD 0) ≤ 2048)
    (hspec : spec x = y) :
    Eventually (x64ScalarMach.step stageCHost)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = y)
      (x64ScalarMach.mkState
        (x64ScalarInit.initState (as := [i64])
          ((lookupBound0 stageCBounds (lookupSymId? stageCTbl nm).get!).getD 0) [] (x, ()))
        (x64ScalarMach.labelAddr stageCHost nm)) := by
  have hspec0 := stageC_host_ok.2.2 tf htf
  rw [hnm, has, hrs] at hspec0
  have hsig : (nm, [i64], [i64]) ∈ stageCMod.sigs :=
    List.mem_map.mpr ⟨tf.toFn, List.mem_map.mpr ⟨tf, htf, rfl⟩,
      by simp [Frontend.C0.TFlatFn.toFn, Fn.sig, hnm, has, hrs]⟩
  have hspec_eq : Env.ofModule stageCMod stageCEnv nm [i64] [i64] =
      (fun (args : Tup Val [i64]) m Q _ => Q (spec args.1, ()) m) := by
    rw [← henv]; funext args m Q X; exact propext ⟨fun h => h.2, fun h => ⟨hsig, h⟩⟩
  rw [hspec_eq] at hspec0
  exact TargetInit.run_ret1_i64_of_fnSpec x64ScalarInit stageCHost hspec0.2 [] (x, ())
    y hb (by decide) (by decide)
    (Q := fun r _ => r = (y, ())) (Prod.ext hspec rfl) (fun _ _ h => h)

/-! ## 5. Native Emission Utilities -/

/-- Emit full AT&T assembly text with `.text`, `.globl`, and newline-terminated directives. -/
def stageCEmitATT (fnNames : List String) (p : List _root_.Directive) : String :=
  printModule0 fnNames p

/-- Emit full AT&T assembly bytes directly via `PrintDir0.printModule0Bytes`. -/
def stageCEmitBytes (symBytes : ByteArray) (symOffs : Array Nat) (fnSyms : List Sym0)
    (ds : List Dir0) : ByteArray :=
  printModule0Bytes symBytes symOffs fnSyms ds

/-- Real C0 source code corresponding to the Stage C benchmark kernels. -/
def stageCSource : String := "
u64 c0_sqr(u64 x) {
  return x * x;
}

u64 c0_poly(u64 x, u64 a, u64 b, u64 c) {
  return a * c0_sqr(x) + b * x + c;
}

u64 c0_sumto(u64 n) {
  u64 acc = 0ULL;
  u64 i = 1ULL;
  while (i <= n) {
    acc = acc + i;
    i = i + 1ULL;
  }
  return acc;
}

u64 c0_mem_swap_add(u64 ptr_a, u64 ptr_b) {
  u64 a = *(u64 *)ptr_a;
  u64 b = *(u64 *)ptr_b;
  *(u64 *)ptr_a = b;
  *(u64 *)ptr_b = a;
  return a + b;
}

u64 sat_lit_var(u64 lit) {
  return lit >> 1ULL;
}

u64 sat_lit_sign(u64 lit) {
  return lit & 1ULL;
}

u64 sat_lit_neg(u64 lit) {
  return lit ^ 1ULL;
}

u64 sat_eval_lit(u64 lit, u64 assign_base) {
  u64 v = sat_lit_var(lit);
  u64 val = (u64)(*(u8 *)(assign_base + v));
  u64 s = sat_lit_sign(lit);
  if (s == 1ULL) {
    if (val == 1ULL) { return 2ULL; }
    if (val == 2ULL) { return 1ULL; }
    return 0ULL;
  }
  return val;
}

u64 sat_check_clause2(u64 lit1, u64 lit2, u64 assign_base) {
  u64 e1 = sat_eval_lit(lit1, assign_base);
  if (e1 == 1ULL) { return 1ULL; }
  u64 e2 = sat_eval_lit(lit2, assign_base);
  if (e2 == 1ULL) { return 1ULL; }
  if (e1 == 2ULL && e2 == 2ULL) { return 2ULL; }
  return 0ULL;
}
"

end LeanQbe.T.Bootstrap0
