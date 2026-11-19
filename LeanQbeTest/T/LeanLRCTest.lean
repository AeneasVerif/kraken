module

public import LeanQbe.T.LeanLRC.ToT
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
meta import LeanQbe.T.LeanLRC.ToT
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe

/-!
# Verification, Axiom Audit, and Differential Code Generator for `LeanQbe.T.LeanLRC` (`X3-R0`)

* Kernel `Func.Wf` theorems via `t_wf_reify` for every Tier-0a C0 runtime helper (`rtBase_fns`).
* `Func.checkTFlat`, `LrcModule.sccs`, `LrcModule.closureTargets`, `PrintCpp`, and `PrintQbe`
  checks across all 4 benchmark modules (`sumToMod`, `mapAddMod`, `tree2Mod`, `foldMapMod`),
  real spliced Lean IR (`realLeanIrMod`), and an exhaustive `scalarStructMod` covering
  `sproj`/`sset`/`uproj`/`uset`/`box`/`unbox`/`set`/`setTag`/`isShared`/`scalar` ops.
* Single-line `#print axioms` checks (`[propext, Classical.choice, Quot.sound]`).
* `main` generator emitting standalone C++20 test TUs and QBE `.ssa` for `test/lrc/run.sh`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.LeanLRCTest

open LeanQbe.T
open LeanQbe.T.LeanLRC
open LeanQbe.T.Frontend.C0 (TFlatFn)
open LeanQbe.T.PrintCpp

/-! ## 1. Exhaustive Scalar/Struct Coverage Module -/

/-- Synthetic `LrcModule` exercising `sproj`/`sset`/`uproj`/`uset`/`box`/`unbox`/`set`/`setTag`/
`del`/`isShared` and every `LrcScalarOp`. -/
def scalarStructMod : LrcModule :=
  let scCtor : LrcCtorInfo :=
    { name := "PairU32U8.mk", cidx := 0, size := 1, usize := 1, ssize := 5 }
  let scAlt : LrcCtorInfo :=
    { name := "PairU32U8.alt", cidx := 1, size := 1, usize := 1, ssize := 5 }
  let arithFn : LrcFn :=
    { name := "lrc_scalar_arith"
      params := [{ id := 1, ty := .uint64 }, { id := 2, ty := .uint64 }]
      retTy := .uint64
      body :=
        .vdecl 3 .uint64 (.scalar .add [.var 1, .var 2]) <|
        .vdecl 4 .uint64 (.scalar .sub [.var 3, .var 2]) <|
        .vdecl 5 .uint64 (.scalar .mul [.var 3, .var 1]) <|
        .vdecl 6 .uint64 (.scalar .xor [.var 5, .var 4]) <|
        .vdecl 7 .uint64 (.scalar .and [.var 6, .var 1]) <|
        .vdecl 8 .uint64 (.scalar .or [.var 7, .var 2]) <|
        .vdecl 9 .uint64 (.scalar .shl [.var 8, .val (.num 2)]) <|
        .vdecl 10 .uint64 (.scalar .lshr [.var 9, .val (.num 1)]) <|
        .vdecl 11 .uint64 (.scalar .ashr [.var 10, .val (.num 1)]) <|
        .vdecl 12 .uint64 (.scalar .udiv [.var 11, .val (.num 3)]) <|
        .vdecl 13 .uint64 (.scalar .urem [.var 11, .val (.num 3)]) <|
        .vdecl 14 .uint64 (.scalar .not [.var 13]) <|
        .vdecl 15 .uint64 (.scalar .neg [.var 14]) <|
        .vdecl 16 .uint8 (.scalar .ult [.var 12, .var 15]) <|
        .vdecl 17 .uint8 (.scalar .ule [.var 12, .var 15]) <|
        .vdecl 18 .uint8 (.scalar .slt [.var 1, .var 2]) <|
        .vdecl 19 .uint8 (.scalar .sle [.var 1, .var 2]) <|
        .vdecl 20 .uint8 (.scalar .ne [.var 1, .var 2]) <|
        .vdecl 21 .uint64 (.scalar .add [.var 12, .var 13]) <|
        .case "Flag" 16 .uint8
          [ (.ctor { name := "F", cidx := 0, size := 0, usize := 0, ssize := 0 },
              .ret (.var 21))
          , (.default,
              .vdecl 22 .uint8 (.scalar .eq [.var 17, .var 20]) <|
              .case "Eq" 22 .uint8
                [ (.default,
                    .vdecl 23 .uint8 (.scalar .and [.var 18, .var 19]) <|
                    .vdecl 24 .uint64 (.box .uint8 23) <|
                    .vdecl 25 .uint8 (.unbox 24) <|
                    .vdecl 26 .tobject (.box .uint64 21) <|
                    .vdecl 27 .uint64 (.unbox 26) <| .ret (.var 27)) ]) ] }
  let structFn : LrcFn :=
    { name := "lrc_struct_roundtrip"
      params :=
        [{ id := 1, ty := .tobject }, { id := 2, ty := .uint32 }, { id := 3, ty := .uint8 }]
      retTy := .uint64
      body :=
        .vdecl 4 .uint64 (.lit (.num 42)) <|
        .vdecl 5 .object (.ctor scCtor [.var 1]) <|
        .uset 5 1 4 <|
        .sset 5 2 0 2 .uint32 <|
        .sset 5 2 4 3 .uint8 <|
        .setTag 5 scAlt.cidx <|
        .set 5 0 (.val (.num 7)) <|
        .vdecl 6 .uint8 (.isShared 5) <|
        .vdecl 7 .tobject (.proj 0 5) <|
        .vdecl 8 .usize (.uproj 1 5) <|
        .vdecl 9 .uint32 (.sproj 2 0 5) <|
        .vdecl 10 .uint8 (.sproj 2 4 5) <|
        .del 5 <|
        .case "Shared" 6 .uint8
          [ (.default,
              .vdecl 11 .uint64 (.fap "lean_unbox" [.var 7]) <|
              .vdecl 12 .uint64 (.scalar .add [.var 8, .var 11]) <|
              .vdecl 13 .uint64 (.copy (.var 9)) <|
              .vdecl 14 .uint64 (.copy (.var 10)) <|
              .vdecl 15 .uint64 (.scalar .add [.var 12, .var 13]) <|
              .vdecl 16 .uint64 (.scalar .add [.var 15, .var 14]) <| .ret (.var 16)) ] }
  { name := "scalarStruct", fns := [arithFn, structFn] }

/-! ## 2. Kernel `Func.Wf` Proofs for Static C0 Runtime & Lowered `λRC` Functions -/

theorem wf_is_scalar : Func.Wf lean_is_scalar_body := by t_wf_reify
theorem wf_box : Func.Wf lean_box_body := by t_wf_reify
theorem wf_unbox : Func.Wf lean_unbox_body := by t_wf_reify
theorem wf_obj_tag : Func.Wf lean_obj_tag_body := by t_wf_reify
theorem wf_rt_enter : Func.Wf lean_rt_enter_body := by t_wf_reify
theorem wf_rt_tick : Func.Wf lean_rt_tick_body := by t_wf_reify
theorem wf_rt_leave : Func.Wf lean_rt_leave_body := by t_wf_reify
theorem wf_alloc_small : Func.Wf lean_alloc_small_body := by t_wf_reify
theorem wf_alloc_ctor : Func.Wf lean_alloc_ctor_body := by t_wf_reify
theorem wf_ctor_get : Func.Wf lean_ctor_get_body := by t_wf_reify
theorem wf_ctor_set : Func.Wf lean_ctor_set_body := by t_wf_reify
theorem wf_ctor_set_tag : Func.Wf lean_ctor_set_tag_body := by t_wf_reify
theorem wf_inc : Func.Wf lean_inc_body := by t_wf_reify
theorem wf_dec : Func.Wf lean_dec_body := by t_wf_reify
theorem wf_is_shared : Func.Wf lean_is_shared_body := by t_wf_reify
theorem wf_alloc_clo : Func.Wf lean_alloc_closure_body := by t_wf_reify
theorem wf_clo_get : Func.Wf lean_closure_get_body := by t_wf_reify
theorem wf_clo_set : Func.Wf lean_closure_set_body := by t_wf_reify
theorem wf_box_u64 : Func.Wf lean_box_u64_body := by t_wf_reify
theorem wf_unbox_u64 : Func.Wf lean_unbox_u64_body := by t_wf_reify
theorem wf_nat_add : Func.Wf lean_nat_add_body := by t_wf_reify
theorem wf_nat_sub : Func.Wf lean_nat_sub_body := by t_wf_reify
theorem wf_nat_mul : Func.Wf lean_nat_mul_body := by t_wf_reify
theorem wf_nat_div : Func.Wf lean_nat_div_body := by t_wf_reify
theorem wf_nat_mod : Func.Wf lean_nat_mod_body := by t_wf_reify
theorem wf_nat_eq : Func.Wf lean_nat_dec_eq_body := by t_wf_reify
theorem wf_nat_le : Func.Wf lean_nat_dec_le_body := by t_wf_reify
theorem wf_nat_lt : Func.Wf lean_nat_dec_lt_body := by t_wf_reify

/-- All 28 static Tier-0a C0 runtime functions satisfy `Fn.Wf`. -/
theorem wf_rt : ∀ f ∈ rtBase_fns, f.Wf := by
  intro f hf
  simp only [rtBase_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact wf_is_scalar
  · exact wf_box
  · exact wf_unbox
  · exact wf_obj_tag
  · exact wf_rt_enter
  · exact wf_rt_tick
  · exact wf_rt_leave
  · exact wf_alloc_small
  · exact wf_alloc_ctor
  · exact wf_ctor_get
  · exact wf_ctor_set
  · exact wf_ctor_set_tag
  · exact wf_inc
  · exact wf_dec
  · exact wf_is_shared
  · exact wf_alloc_clo
  · exact wf_clo_get
  · exact wf_clo_set
  · exact wf_box_u64
  · exact wf_unbox_u64
  · exact wf_nat_add
  · exact wf_nat_sub
  · exact wf_nat_mul
  · exact wf_nat_div
  · exact wf_nat_mod
  · exact wf_nat_eq
  · exact wf_nat_le
  · exact wf_nat_lt

/-- Every function in `rtBase_fns ++ tflatFnsToFns tfs` satisfies `Fn.Wf`. -/
theorem wf_lrc (tfs : List TFlatFn) :
    ∀ f ∈ (toLeanModuleWithRuntime tfs).fns, f.Wf := by
  intro f hf
  simp only [toLeanModuleWithRuntime, List.mem_append] at hf
  rcases hf with hrt | hprog
  · exact wf_rt f hrt
  · exact tflatFnsToFns_wf tfs f hprog

/-! ## 3. Reification, SCC, Codegen & Diagnostics `#guard`s -/

private def checkProgramAllWf (tfs : List TFlatFn) : Bool :=
  (tflatFnsToFns tfs).all fun fn => Func.checkTFlat fn.body

private def checkModWf (m : LrcModule) : Bool :=
  (lowerLrcProgram m).toOption.map checkProgramAllWf == some true

#guard rtBase_fns.all fun fn => Func.checkTFlat fn.body
#guard checkModWf sumToMod
#guard checkModWf mapAddMod
#guard checkModWf tree2Mod
#guard checkModWf foldMapMod
#guard checkModWf realLeanIrMod
#guard checkModWf allBenchLrcMod
#guard checkModWf scalarStructMod

#guard sumToMod.sccs == [["lrc_sumTo"], ["lrc_sumToAcc"]]
#guard mapAddMod.sccs.length == 5
#guard (foldMapMod.closureTargets.toOption.map (·.length)) == some 3
#guard foldMapMod.maxApArity == 2
#guard realLeanIrMod.maxApArity == 2

#guard match lowerLrcProgram allBenchLrcMod with
  | .ok tfs =>
    let m := toLeanModuleWithRuntime tfs
    m.fns.length == 61 && (PrintCpp.ppTModule m).isOk && (PrintQbe.module m).isOk
  | .error _ => false

#guard match lowerLrcProgram scalarStructMod with
  | .ok tfs =>
    let m := toLeanModuleWithRuntime tfs
    (PrintCpp.ppTModule m).isOk && (PrintQbe.module m).isOk
  | .error _ => false

private def diagStr : String :=
  match lowerLrcProgram allBenchLrcMod with
  | .error e => s!"ERROR: {e}"
  | .ok tfs =>
    let ms := collectMetrics tfs
    let rtOps := rtBase_fns.map fun f =>
      s!"{f.name}:ops={tflatOpCount (toTFlat (f.body K KL (Tup.levels f.as 0)) f.as.length 0)}"
    let fnLines := ms.map fun x => s!"{x.name}(ops={x.ops},jnz={x.jnzes},calls={x.calls})"
    s!"rt=[{", ".intercalate rtOps}]\n" ++
    s!"lrc=[{", ".intercalate fnLines}]\n" ++
    s!"realLeanSCCs={repr realLeanIrMod.sccs}\n" ++
    s!"foldMapSCCs={repr foldMapMod.sccs}"

#eval IO.println diagStr

/-! ## 4. Single-Line `#print axioms` Audit -/

#print axioms wf_rt
#print axioms wf_lrc
#print axioms wf_rt_enter
#print axioms wf_alloc_ctor
#print axioms wf_nat_add

/-! ## 5. C++20 Differential & QBE Generator (`main`) -/

def mkBenchDriverCpp : String :=
  String.intercalate "\n"
    [ "#include <cstdint>"
    , "#include <cstdio>"
    , "#include <cstdlib>"
    , "#include <string>"
    , "#include \"lrc_gen.hpp\""
    , ""
    , "struct RtGuard {"
    , "  ::tqbe::Mem mem;"
    , "  uint64_t rt = 0x10000ULL;"
    , "  uint64_t heap = 0x20000ULL;"
    , "  explicit RtGuard(uint64_t cap = 1ULL << 20, uint64_t fuel = 1000000ULL,"
    , "                   uint64_t depth = 1024ULL) {"
    , "    mem.alloc(rt, 64, 0);"
    , "    if (cap > 0) mem.alloc(heap, cap, 0);"
    , "    ::tqbe::store<::tqbe::bits<64>>(mem, ::tqbe::bits<64>(rt + 0), ::tqbe::bits<64>(heap));"
    , "    ::tqbe::store<::tqbe::bits<64>>(mem, ::tqbe::bits<64>(rt + 8), ::tqbe::bits<64>(heap));"
    , "    ::tqbe::store<::tqbe::bits<64>>(mem, ::tqbe::bits<64>(rt + 16),"
    , "      ::tqbe::bits<64>(heap + cap));"
    , "    ::tqbe::store<::tqbe::bits<64>>(mem, ::tqbe::bits<64>(rt + 24), ::tqbe::bits<64>(fuel));"
    , "    ::tqbe::store<::tqbe::bits<64>>(mem,"
    , "      ::tqbe::bits<64>(rt + 32), ::tqbe::bits<64>(depth));"
    , "    ::tqbe::store<::tqbe::bits<64>>(mem, ::tqbe::bits<64>(rt + 40), ::tqbe::bits<64>(0));"
    , "  }"
    , "  ::tqbe::bits<64> rtArg() const { return ::tqbe::bits<64>(rt); }"
    , "};"
    , ""
    , "static ::tqbe::bits<64> bx(uint64_t n) { return ::tqbe::bits<64>((n << 1) | 1ULL); }"
    , "static uint64_t ub(::tqbe::bits<64> x) { return x.word(0) >> 1; }"
    , "static void chk(const char* tag, uint64_t got, uint64_t exp) {"
    , "  if (got != exp) {"
    , "    std::fprintf(stderr, \"FAIL %s: got=%llu exp=%llu\\n\", tag,"
    , "      (unsigned long long)got, (unsigned long long)exp);"
    , "    std::exit(1);"
    , "  }"
    , "}"
    , ""
    , "template <typename Fn>"
    , "static void expectExit(const char* tag, const char* expTarget, uint64_t cap,"
    , "                       uint64_t fuel, uint64_t depth, Fn fn) {"
    , "  RtGuard g(cap, fuel, depth);"
    , "  try {"
    , "    (void)fn(g);"
    , "    std::fprintf(stderr, \"FAIL %s: expected exit %s\\n\", tag, expTarget);"
    , "    std::exit(1);"
    , "  } catch (const ::tqbe::ExitException& ex) {"
    , "    if (ex.target != expTarget) {"
    , "      std::fprintf(stderr, \"FAIL %s: got exit %s exp %s\\n\","
    , "        tag, ex.target.c_str(), expTarget);"
    , "      std::exit(1);"
    , "    }"
    , "  }"
    , "}"
    , ""
    , "int main() {"
    , "  uint64_t ns[5] = {0, 1, 5, 10, 12};"
    , "  for (uint64_t n : ns) {"
    , "    RtGuard g;"
    , "    uint64_t s1 = ub(lrc_sumTo(g.mem, g.rtArg(), bx(n)));"
    , "    uint64_t s2 = ub(LeanQbe_T_LeanLRC_leanSumTo(g.mem, g.rtArg(), bx(n)));"
    , "    uint64_t m1 = ub(lrc_mapAdd(g.mem, g.rtArg(), bx(n), bx(3)));"
    , "    uint64_t m2 = ub(LeanQbe_T_LeanLRC_leanMapAddSum(g.mem, g.rtArg(), bx(n), bx(3)));"
    , "    uint64_t f1 = ub(lrc_foldMap(g.mem, g.rtArg(), bx(n), bx(4)));"
    , "    uint64_t f2 = ub(LeanQbe_T_LeanLRC_leanFoldMap(g.mem, g.rtArg(), bx(n), bx(4)));"
    , "    chk(\"sumTo\", s1, s2);"
    , "    chk(\"mapAdd\", m1, m2);"
    , "    chk(\"foldMap\", f1, f2);"
    , "    std::printf(\"CASE n=%llu sumTo=%llu mapAdd=%llu foldMap=%llu\\n\","
    , "      (unsigned long long)n, (unsigned long long)s1,"
    , "      (unsigned long long)m1, (unsigned long long)f1);"
    , "  }"
    , "  for (uint64_t d = 0; d <= 6; ++d) {"
    , "    RtGuard g;"
    , "    uint64_t t1 = ub(lrc_tree2(g.mem, g.rtArg(), bx(d)));"
    , "    uint64_t t2 = ub(LeanQbe_T_LeanLRC_leanTree2(g.mem, g.rtArg(), bx(d)));"
    , "    chk(\"tree2\", t1, t2);"
    , "    std::printf(\"TREE d=%llu tree2=%llu\\n\","
    , "      (unsigned long long)d, (unsigned long long)t1);"
    , "  }"
    , "  { RtGuard g(1ULL << 20, 100000ULL, 1024ULL);"
    , "    uint64_t big = ub(lrc_sumTo(g.mem, g.rtArg(), bx(500)));"
    , "    chk(\"tailSum500\", big, 125250ULL);"
    , "    uint64_t depthNow ="
    , "      ::tqbe::load<::tqbe::bits<64>>(g.mem, ::tqbe::bits<64>(g.rt + 32)).word(0);"
    , "    chk(\"depthBalanced\", depthNow, 1024ULL);"
    , "  }"
    , "  expectExit(\"fuel\", \"lean_out_of_fuel\", 1ULL << 16, 4ULL, 128ULL, [](RtGuard& g) {"
    , "    return lrc_sumTo(g.mem, g.rtArg(), bx(20));"
    , "  });"
    , "  expectExit(\"stack\", \"lean_stack_overflow\","
    , "      1ULL << 16, 10000ULL, 3ULL, [](RtGuard& g) {"
    , "    return lrc_tree2(g.mem, g.rtArg(), bx(4));"
    , "  });"
    , "  expectExit(\"oom\", \"lean_oom\", 16ULL, 10000ULL, 128ULL, [](RtGuard& g) {"
    , "    return lrc_tree2(g.mem, g.rtArg(), bx(3));"
    , "  });"
    , "  return 0;"
    , "}"
    ]

def mkScalarDriverCpp : String :=
  String.intercalate "\n"
    [ "#include <cstdint>"
    , "#include <cstdio>"
    , "#include <cstdlib>"
    , "#include \"lrc_scalar.hpp\""
    , ""
    , "int main() {"
    , "  ::tqbe::Mem mem;"
    , "  uint64_t rt = 0x10000ULL, heap = 0x20000ULL, cap = 4096ULL;"
    , "  mem.alloc(rt, 64, 0); mem.alloc(heap, cap, 0);"
    , "  ::tqbe::store<::tqbe::bits<64>>(mem, ::tqbe::bits<64>(rt + 0), ::tqbe::bits<64>(heap));"
    , "  ::tqbe::store<::tqbe::bits<64>>(mem, ::tqbe::bits<64>(rt + 8), ::tqbe::bits<64>(heap));"
    , "  ::tqbe::store<::tqbe::bits<64>>(mem,"
    , "    ::tqbe::bits<64>(rt + 16), ::tqbe::bits<64>(heap + cap));"
    , "  ::tqbe::store<::tqbe::bits<64>>(mem,"
    , "    ::tqbe::bits<64>(rt + 24), ::tqbe::bits<64>(1000ULL));"
    , "  ::tqbe::store<::tqbe::bits<64>>(mem, ::tqbe::bits<64>(rt + 32), ::tqbe::bits<64>(64ULL));"
    , "  uint64_t a = lrc_scalar_arith(mem, ::tqbe::bits<64>(rt),"
    , "    ::tqbe::bits<64>(99), ::tqbe::bits<64>(25)).word(0);"
    , "  uint64_t s = lrc_struct_roundtrip(mem, ::tqbe::bits<64>(rt),"
    , "    ::tqbe::bits<64>(3), ::tqbe::bits<32>(1000), ::tqbe::bits<8>(9)).word(0);"
    , "  if (s != 1058ULL) {"
    , "    std::fprintf(stderr,"
    , "      \"FAIL scalarStruct: s=%llu (exp 1058)\\n\", (unsigned long long)s);"
    , "    return 1;"
    , "  }"
    , "  std::printf(\"SCALAR_OK arith=%llu struct=%llu\\n\","
    , "    (unsigned long long)a, (unsigned long long)s);"
    , "  return 0;"
    , "}"
    ]

/-- Generate standalone C++20 and QBE `.ssa` artifacts into `outDir`. -/
def generateArtifacts (outDir : System.FilePath) : IO Unit := do
  IO.FS.createDirAll outDir
  let benchTfs ← match lowerLrcProgram allBenchLrcMod with
    | .ok x => pure x | .error e => throw (IO.userError e)
  let scalarTfs ← match lowerLrcProgram scalarStructMod with
    | .ok x => pure x | .error e => throw (IO.userError e)
  let benchMod := toLeanModuleWithRuntime benchTfs
  let scalarMod := toLeanModuleWithRuntime scalarTfs
  let benchCpp ← match PrintCpp.ppTModule benchMod with
    | .ok x => pure x | .error e => throw (IO.userError e)
  let scalarCpp ← match PrintCpp.ppTModule scalarMod with
    | .ok x => pure x | .error e => throw (IO.userError e)
  let benchQbe ← match PrintQbe.module benchMod with
    | .ok x => pure x | .error e => throw (IO.userError e)
  IO.FS.writeFile (outDir / "lrc_gen.hpp") benchCpp
  IO.FS.writeFile (outDir / "lrc_scalar.hpp") scalarCpp
  IO.FS.writeFile (outDir / "lrc_driver.cpp") mkBenchDriverCpp
  IO.FS.writeFile (outDir / "lrc_scalar_driver.cpp") mkScalarDriverCpp
  IO.FS.writeFile (outDir / "lrc.ssa") benchQbe

end LeanQbeTest.T.LeanLRCTest

public def main (args : List String) : IO Unit := do
  let outDir : System.FilePath := match args with
    | dir :: _ => dir
    | [] => "/tmp/leanqbe-lrc"
  LeanQbeTest.T.LeanLRCTest.generateArtifacts outDir
