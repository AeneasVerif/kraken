module

public import LeanQbe.T.Frontend.C0
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Logic.Rules
meta import LeanQbe.T.Frontend.C0
meta import LeanQbe.T.PrintCpp

/-!
# Verification & Differential Test Suite for C0 Frontend (`X0-core`)

Covers:
* `(V1)` Layout parity on Kissat `watch`, `clause`, `assigned`, `lean_object`, `mixed_bf`
* `(V2)` Kissat `search_propagate_literal` (`test/c0/proplit.c`) + `Func.Wf` via `t_wf_reify`
* `(V3)` Lean Tier-0 runtime RC + forward `goto DONE` + multi-return + short-circuit (`test/c0/lean_rc.c`)
  + `Func.Wf` + `ModuleOk`
* `(V4)` `T4` total-correctness `wp` smoke test (`sum_pos64`) using `wp_loop_group` / `wp_join_group`
* C++20 code generation (`PrintCpp`) for D2 differential testing in `test/c0/run.sh`
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.C0Test

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open Std.ExtHashMap

/-! ## (V1) Layout Parity & Bitfield Packing -/

section V1Layout

c0_file! layout "test/c0/test_layout.c"

private def v1LayoutCheck : Except String Bool := do
  let src := "#include \"c0.h\"
typedef union { struct { u32 lit:31; u32 binary:1; } b; u32 raw; } watch;
struct clause {
  u32 glue:19; bool garbage:1; bool quotient:1; bool reason:1; bool redundant:1;
  bool shrunken:1; bool subsume:1; bool swept:1; bool vivify:1; u32 used:5;
  u32 searched; u32 size; u32 lits[];
};
struct assigned {
  u32 level; u32 analyzed:2; bool poison:1; bool reason_flag:1; bool redundant:1; bool shrinkable:1;
  u32 trail; u32 reason;
};
struct lean_object { i32 m_rc; u16 m_cs_sz; u8 m_other; u8 m_tag; };
struct mixed_bf { u8 tag; bool flag:1; u32 val:20; u64 wide:40; };"
  let tu ← parseC0 src
  let env ← buildLayoutEnv tu
  let (wSz, wAl) ← typeSizeAlign env (.typedefRef "watch")
  let (cSz, cAl) ← typeSizeAlign env (.structRef "clause")
  let cSearched ← offsetOfField env (.structRef "clause") "searched"
  let cSize ← offsetOfField env (.structRef "clause") "size"
  let cLits ← offsetOfField env (.structRef "clause") "lits"
  let cGarbage ← lookupField env (.structRef "clause") "garbage"
  let cUsed ← lookupField env (.structRef "clause") "used"
  let (aSz, aAl) ← typeSizeAlign env (.structRef "assigned")
  let aReason ← offsetOfField env (.structRef "assigned") "reason"
  let (lSz, lAl) ← typeSizeAlign env (.structRef "lean_object")
  let lOther ← offsetOfField env (.structRef "lean_object") "m_other"
  let lTag ← offsetOfField env (.structRef "lean_object") "m_tag"
  let (mSz, mAl) ← typeSizeAlign env (.structRef "mixed_bf")
  let mWide ← lookupField env (.structRef "mixed_bf") "wide"
  pure (wSz == 4 && wAl == 4 &&
        cSz == 12 && cAl == 4 && cSearched == 4 && cSize == 8 && cLits == 12 &&
        cGarbage == .bitfield 2 1 3 1 .bool &&
        cUsed == .bitfield 0 4 27 5 .u32 &&
        aSz == 16 && aAl == 4 && aReason == 12 &&
        lSz == 8 && lAl == 4 && lOther == 6 && lTag == 7 &&
        mSz == 16 && mAl == 8 && mWide == .bitfield 8 8 0 40 .u64)

#guard v1LayoutCheck.toOption == some true

theorem pack_watch_bin_wf : Func.Wf pack_watch_bin_body := by t_wf_reify
theorem set_clause_bits_wf : Func.Wf set_clause_bits_body := by t_wf_reify
theorem read_clause_header_word_wf : Func.Wf read_clause_header_word_body := by t_wf_reify
theorem read_lean_header_word_wf : Func.Wf read_lean_header_word_body := by t_wf_reify

end V1Layout

/-! ## (V2) Kissat Watch-List Propagation (`test/c0/proplit.c`) -/

section V2Proplit

c0_file! proplit "test/c0/proplit.c"

#c0_shape search_propagate_literal

theorem search_propagate_literal_wf : Func.Wf search_propagate_literal_body := by t_wf_reify

#guard (PrintCpp.ppModule proplit_fns).isOk

end V2Proplit

/-! ## (V3) Lean Tier-0 Runtime RC + Goto + Multi-Return + Short-Circuit (`test/c0/lean_rc.c`) -/

section V3LeanRc

c0_file! leanrc "test/c0/lean_rc.c"

#c0_shape lean_dec_ref_cold
#c0_shape analyze_goto_demo
#c0_shape divmod_u32
#c0_shape find_guarded

theorem lean_is_scalar_impl_wf : Func.Wf lean_is_scalar_impl_body := by t_wf_reify
theorem lean_is_scalar_wf : Func.Wf lean_is_scalar_body := by t_wf_reify
theorem lean_box_wf : Func.Wf lean_box_body := by t_wf_reify
theorem lean_unbox_wf : Func.Wf lean_unbox_body := by t_wf_reify
theorem lean_inc_wf : Func.Wf lean_inc_body := by t_wf_reify
theorem lean_dec_ref_cold_wf : Func.Wf lean_dec_ref_cold_body := by t_wf_reify
theorem lean_dec_wf : Func.Wf lean_dec_body := by t_wf_reify
theorem analyze_goto_demo_wf : Func.Wf analyze_goto_demo_body := by t_wf_reify
theorem divmod_u32_wf : Func.Wf divmod_u32_body := by t_wf_reify
theorem sum_divmod_u32_wf : Func.Wf sum_divmod_u32_body := by t_wf_reify
theorem find_guarded_wf : Func.Wf find_guarded_body := by t_wf_reify

private theorem leanrc_nodup : leanrc_module.namesNodup := by
  simp only [Module.namesNodup, Module.names, leanrc_module, leanrc_fns,
    lean_is_scalar_impl, lean_is_scalar, lean_box, lean_unbox, lean_inc, lean_dec_ref_cold,
    lean_dec, analyze_goto_demo, divmod_u32, sum_divmod_u32, find_guarded,
    List.map]
  decide

theorem leanrc_moduleOk : ModuleOk (fun _ _ _ _ _ _ _ => False) leanrc_module := by
  refine ⟨leanrc_nodup, ?_⟩
  intro pre fn post hsplit
  have hmem : fn ∈ leanrc_module.fns := by
    rw [hsplit]; exact List.mem_append_right _ List.mem_cons_self
  simp only [leanrc_module, leanrc_fns, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨lean_is_scalar_impl_wf, ?_, fun _ _ _ _ h => h.elim⟩
    simp [Fn.callsOk, lean_is_scalar_impl, lean_is_scalar_impl_body, Expr.callsOk]
  · refine ⟨lean_is_scalar_wf, ?_, fun _ _ _ _ h => h.elim⟩
    simp [Fn.callsOk, lean_is_scalar, lean_is_scalar_body, Expr.callsOk]
  · refine ⟨lean_box_wf, ?_, fun _ _ _ _ h => h.elim⟩
    simp [Fn.callsOk, lean_box, lean_box_body, Expr.callsOk]
  · refine ⟨lean_unbox_wf, ?_, fun _ _ _ _ h => h.elim⟩
    simp [Fn.callsOk, lean_unbox, lean_unbox_body, Expr.callsOk]
  · refine ⟨lean_inc_wf, ?_, fun _ _ _ _ h => h.elim⟩
    simp [Fn.callsOk, lean_inc, lean_inc_body, Expr.callsOk, Blocks.callsOk]
  · refine ⟨lean_dec_ref_cold_wf, ?_, fun _ _ _ _ h => h.elim⟩
    simp [Fn.callsOk, lean_dec_ref_cold, lean_dec_ref_cold_body, leanrc_module, Extern.sig,
      Expr.callsOk, Blocks.callsOk]
  · refine ⟨lean_dec_wf, ?_, fun _ _ _ _ h => h.elim⟩
    have hmem_cold : lean_dec_ref_cold ∈ pre := by
      have hsplit' := hsplit
      simp only [leanrc_module, leanrc_fns] at hsplit'
      have hn := congrArg (List.map Fn.name) hsplit'
      simp only [List.map_cons, List.map_nil, List.map_append,
        lean_is_scalar_impl, lean_is_scalar, lean_box, lean_unbox, lean_inc, lean_dec_ref_cold,
        lean_dec, analyze_goto_demo, divmod_u32, sum_divmod_u32, find_guarded] at hn
      rcases pre with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | rest⟩⟩⟩⟩⟩⟩ <;>
        simp_all
    simp only [Fn.callsOk, lean_dec, lean_dec_body, Expr.callsOk, Blocks.callsOk, true_and, and_true]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨lean_dec_ref_cold, hmem_cold, rfl⟩)
  · refine ⟨analyze_goto_demo_wf, ?_, fun _ _ _ _ h => h.elim⟩
    simp [Fn.callsOk, analyze_goto_demo, analyze_goto_demo_body, Expr.callsOk, Blocks.callsOk]
  · refine ⟨divmod_u32_wf, ?_, fun _ _ _ _ h => h.elim⟩
    simp [Fn.callsOk, divmod_u32, divmod_u32_body, leanrc_module, Expr.callsOk]
  · refine ⟨sum_divmod_u32_wf, ?_, fun _ _ _ _ h => h.elim⟩
    have hmem_dm : divmod_u32 ∈ pre := by
      have hsplit' := hsplit
      simp only [leanrc_module, leanrc_fns] at hsplit'
      have hn := congrArg (List.map Fn.name) hsplit'
      simp only [List.map_cons, List.map_nil, List.map_append,
        lean_is_scalar_impl, lean_is_scalar, lean_box, lean_unbox, lean_inc, lean_dec_ref_cold,
        lean_dec, analyze_goto_demo, divmod_u32, sum_divmod_u32, find_guarded] at hn
      rcases pre with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8, _ | rest⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
        simp_all
    simp only [Fn.callsOk, sum_divmod_u32, sum_divmod_u32_body, Expr.callsOk, and_true]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨divmod_u32, hmem_dm, rfl⟩)
  · refine ⟨find_guarded_wf, ?_, fun _ _ _ _ h => h.elim⟩
    simp [Fn.callsOk, find_guarded, find_guarded_body, Expr.callsOk, Blocks.callsOk]

#guard (PrintCpp.ppModule leanrc_fns).isOk
#guard (PrintCpp.ppTModule leanrc_module).isOk

end V3LeanRc

/-! ## (V4) `T4` `wp` Proof Ergonomics Smoke Test (`sum_pos64`) -/

section V4WpSmoke

c0_file! v4 "test/c0/v4_sum_pos64.c"

#c0_shape sum_pos64

theorem sum_pos64_wf : Func.Wf sum_pos64_body := by t_wf_reify

def sumPosList (xs : List (BitVec 64)) : BitVec 64 :=
  xs.foldl (fun acc v => if (0#64).slt v then acc + v else acc) 0#64

theorem sumPosList_take_succ {xs : List (BitVec 64)} {k : Nat} (hk : k < xs.length) :
    sumPosList (xs.take (k + 1)) =
      let cur := sumPosList (xs.take k)
      if (0#64).slt xs[k] then cur + xs[k] else cur := by
  simp only [sumPosList, List.take_succ_eq_append_getElem hk, List.foldl_append, List.foldl_cons,
    List.foldl_nil]

def sumPos64Spec : Spec [i64, i64] [i64] := fun (arr, n, ()) m Q _ =>
  ∃ xs R, (array64 arr xs ⋆ R) m ∧ xs.length = n.toNat ∧
    ∀ m', (array64 arr xs ⋆ R) m' → Q (sumPosList xs, ()) m'

theorem sum_pos64_correct :
    ∀ (Γ : Env) (args : Tup Val [i64, i64]) (m : Mem 64) (Q : Post [i64]) (X : XPost),
      sumPos64Spec args m Q X → Func.spec Γ sum_pos64_body args m Q X := by
  rintro Γ ⟨arr, n, ⟨⟩⟩ m Q X ⟨xs, R, hm, hlen, hQ⟩
  dsimp only [Func.spec, Func.wp, sum_pos64_body]
  refine wp_loop_group
    (fun rem (i, acc, ()) m' =>
      i.toNat ≤ n.toNat ∧ rem = n.toNat - i.toNat ∧
        acc = sumPosList (xs.take i.toNat) ∧ (array64 arr xs ⋆ R) m')
    ?_ (fun J hJ => ?_)
  · intro J rem ⟨i, acc, ⟨⟩⟩ m' hlt ⟨hile, hrem, hacc, hm'⟩
    dsimp only [Blocks.get_here]
    wp_unfold
    refine ⟨fun hult => ?_, fun hnult => ?_⟩
    · have hiNat : i.toNat < n.toNat := by simpa [BitVec.ult] using hult
      have hiLen : i.toNat < xs.length := hlen ▸ hiNat
      have haddr : (Arg.var (arr + i * 8#64) : Arg Val i64).val =
          arr + BitVec.ofNat 64 (8 * i.toNat) := by
        dsimp only [Arg.val]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_mul, Nat.mul_comm]
      refine wp_load_array64 haddr hiLen hm' ?_
      refine wp_join_group
        (fun (acc', ()) m'' =>
          acc' = (if (0#64).slt xs[i.toNat] then acc + xs[i.toNat] else acc) ∧ m'' = m')
        ?_ (fun Jif hJif => ?_)
      · intro Jif ⟨acc', ⟨⟩⟩ m'' ⟨hacc', hm''⟩
        rw [hm'']
        dsimp only [Blocks.get_here]
        wp_unfold
        have hstep : (i + 1#64).toNat = i.toNat + 1 := by
          have hbound : n.toNat < 2 ^ 64 := n.isLt
          simp [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega : i.toNat + 1 < 2 ^ 64)]
        refine hlt (n.toNat - (i + 1#64).toNat) (i + 1#64, acc', ()) m' (by omega) ?_
        refine ⟨by omega, rfl, ?_, hm'⟩
        rw [hstep, sumPosList_take_succ hiLen, ← hacc, hacc']
      · wp_unfold
        refine ⟨fun hgt => ?_, fun hngt => ?_⟩
        · have hgt' : (0#64).slt xs[i.toNat] = true := by simpa using hgt
          exact hJif (acc + xs[i.toNat], ()) m' ⟨by simp [hgt'], rfl⟩
        · have hngt' : (0#64).slt xs[i.toNat] = false := by simpa using hngt
          exact hJif (acc, ()) m' ⟨by simp [hngt'], rfl⟩
    · have hnot : ¬ (i.toNat < n.toNat) := by simpa [BitVec.ult] using hnult
      have hieq : i.toNat = n.toNat := by omega
      have htake : xs.take i.toNat = xs := by rw [hieq, ← hlen, List.take_length]
      rw [hacc, htake]
      exact hQ m' hm'
  · wp_unfold
    exact hJ n.toNat (0#64, 0#64, ()) m ⟨Nat.zero_le _, by simp, by simp [sumPosList], hm⟩

#print axioms sum_pos64_correct

end V4WpSmoke

/-! ## Extra Intrinsic & Control-Flow Differential Suite (`intrinsics_cf`) -/

section ExtraCF

c0_file! extra "test/c0/extra_cf.c"

theorem test_intrinsics_wf : Func.Wf test_intrinsics_body := by t_wf_reify
theorem test_switch_loops_wf : Func.Wf test_switch_loops_body := by t_wf_reify

end ExtraCF

/-! ## C++20 Codegen Entrypoint for `test/c0/run.sh` -/

def emitNamespace (ns : String) (fns : List Fn) : Except String String := do
  let symMap ← PrintCpp.buildSymMap fns
  let decls := String.join (fns.map (PrintCpp.ppFnDecl symMap))
  let defs := String.intercalate "\n" (fns.map (PrintCpp.ppFn symMap))
  pure (s!"namespace {ns} " ++ "{\n" ++ decls ++ "\n" ++ defs ++ "\n} // namespace " ++ ns ++ "\n")

def runGenerate (outDir : String) : IO UInt32 := do
  let groups : List (String × List Fn) :=
    [ ("c0_layout", layout_fns)
    , ("c0_proplit", proplit_fns)
    , ("c0_leanrc", leanrc_fns)
    , ("c0_v4", v4_fns)
    , ("c0_extra", extra_fns)
    ]
  for (ns, fns) in groups do
    match emitNamespace ns fns with
    | .ok body =>
      let hdr :=
        if ns == "c0_leanrc" then
          "#pragma once\n#include \"tqbe_rt.hpp\"\n\nvoid c0_free_obj(::tqbe::Mem& mem, ::tqbe::bits<64> o);\n\n"
        else
          "#pragma once\n#include \"tqbe_rt.hpp\"\n\n"
      IO.FS.writeFile s!"{outDir}/{ns}.hpp" (hdr ++ body)
    | .error e => throw (IO.userError s!"emitNamespace {ns}: {e}")
  IO.println s!"Generated C0 differential C++ headers in {outDir}."
  pure 0

end LeanQbeTest.T.C0Test

def main (args : List String) : IO UInt32 :=
  LeanQbeTest.T.C0Test.runGenerate (args.headD "/tmp/leanqbe-c0")
