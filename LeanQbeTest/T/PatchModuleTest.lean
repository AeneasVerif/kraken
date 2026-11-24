module

public import LeanQbe.T.Frontend.C0
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.ProofKit
public import LeanQbe.T.Examples.Kissat.PatchModule
public import LeanQbe.T.Examples.Kissat.FullM7CongHash
meta import LeanQbe.T.Frontend.C0
meta import LeanQbe.T.Logic.ProofKit
meta import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Examples.Kissat.FullM7CongHash

/-!
# PatchModuleTest: End-to-End Verification of `PatchModule`

Tests:
1. Standalone 4-fn base module (`Base.toyBase_module`) spliced with a 2-fn replacement delta
   (`Delta.toyRepls`) + 1 inserted helper (`Delta.toyBefores`) + `rewiredRows`:
   * Proves full `ModuleOk (patchEnv b) b.patchedMod` via `PatchBundle` + `patchBundle_moduleOk_isolated`
   * Exercises `splice_module!` (auto slot indices, single batched `Eq.refl` `_slotSigs`,
     `_replSigs_ok`, `_names_nodup`, `_wf`, `_acyclic`)
   * Exercises `derive_reuse_bridge!` (including index shifts from `befores` insertion).
2. Spec-preserving bugfix delta via `patchBundle_moduleOk_sameSpecs`.
3. Real Kissat subset splice onto `FullM7CongHash.m7CongHashModule`: 2-fn delta via
   `splice_module!` (`baseAcyclic := m7CongHash_acyclic`, `baseWf := m7CongHashFns_wf`)
   + `derive_reuse_bridge!` verifying identical untouched suffix runs.
4. `#print axioms` verification ensuring `[propext, Classical.choice, Quot.sound]` only.
-/

set_option autoImplicit false

namespace LeanQbeTest.T.PatchModuleTest

open LeanQbe.T
open LeanQbe.T.ProofKit
open LeanQbe.T.Examples.Kissat.PatchModule
open LeanQbe.T.Examples.Kissat.FullM7CongHash

/-! ## 1. Toy 4-fn Base Module + 2-fn Delta + `befores` Helper + `rewiredRows` -/

namespace Base

c0_decl! toyBase "
u64 toy_leaf(u64 x) {
  return x + 1ULL;
}

u64 toy_mul(u64 x) {
  return x * 2ULL;
}

u64 toy_mid(u64 x) {
  u64 y = toy_leaf(x);
  return y + 3ULL;
}

u64 toy_caller(u64 x) {
  u64 a = toy_mul(x);
  return a + 5ULL;
}
"

def toyLeafSpec : Spec [i64] [i64] :=
  fun (x, ()) m Q _ => ∀ r, r = x + 1#64 → Q (r, ()) m

def toyMulSpec : Spec [i64] [i64] :=
  fun (x, ()) m Q _ => ∀ r, r = x * 2#64 → Q (r, ()) m

def toyMidSpec : Spec [i64] [i64] :=
  fun (x, ()) m Q _ => ∀ r, r = x + 4#64 → Q (r, ()) m

def toyCallerSpec : Spec [i64] [i64] :=
  fun (x, ()) m Q _ => ∀ r, r = x * 2#64 + 5#64 → Q (r, ()) m

def toyBaseTable : List SpecEntry :=
  [ ⟨"toy_leaf", [i64], [i64], toyLeafSpec, true⟩
  , ⟨"toy_mul", [i64], [i64], toyMulSpec, true⟩
  , ⟨"toy_mid", [i64], [i64], toyMidSpec, true⟩
  , ⟨"toy_caller", [i64], [i64], toyCallerSpec, true⟩ ]

theorem toy_leaf_wp (Γ : Env) :
    ∀ xs m Q X, toyLeafSpec xs m Q X → Func.wp Γ toy_leaf.body xs m Q X := by
  intro (x, ()) m Q X hQ
  dsimp only [toy_leaf, toy_leaf_body, Func.wp]
  c0_hsteps
  exact hQ (x + 1#64) rfl

theorem toy_mul_wp (Γ : Env) :
    ∀ xs m Q X, toyMulSpec xs m Q X → Func.wp Γ toy_mul.body xs m Q X := by
  intro (x, ()) m Q X hQ
  dsimp only [toy_mul, toy_mul_body, Func.wp]
  c0_hsteps
  exact hQ (x * 2#64) rfl

theorem toy_mid_wp :
    ∀ xs m Q X, toyMidSpec xs m Q X → Func.wp (Env.ofTable toyBaseTable) toy_mid.body xs m Q X := by
  intro (x, ()) m Q X hQ
  dsimp only [toy_mid, toy_mid_body, Func.wp]
  c0_hsteps
  · dsimp only [wp, toyBaseTable]
    refine ⟨fun r m' => r = (x + 1#64, ()) ∧ m' = m, X, ?_, ?_, fun _ _ _ _ h => h⟩
    · rw [Env.ofTable_cons_self]
      intro r hr
      exact ⟨congrArg (·, ()) hr, rfl⟩
    · rintro r m' ⟨rfl, rfl⟩
      c0_hsteps
      refine hQ _ ?_
      dsimp only [lift2, Arg.val]
      apply BitVec.eq_of_toNat_eq
      c0_bv_omega

theorem toy_caller_wp :
    ∀ xs m Q X, toyCallerSpec xs m Q X →
      Func.wp (Env.ofTable toyBaseTable) toy_caller.body xs m Q X := by
  intro (x, ()) m Q X hQ
  dsimp only [toy_caller, toy_caller_body, Func.wp]
  c0_hsteps
  · dsimp only [wp, toyBaseTable]
    refine ⟨fun r m' => r = (x * 2#64, ()) ∧ m' = m, X, ?_, ?_, fun _ _ _ _ h => h⟩
    · rw [Env.ofTable_cons_ne (by decide)]
      rw [Env.ofTable_cons_self]
      intro r hr
      exact ⟨congrArg (·, ()) hr, rfl⟩
    · rintro r m' ⟨rfl, rfl⟩
      c0_hsteps
      exact hQ _ rfl

theorem toyBase_acyclic : toyBase_module.checkAcyclic = true := by t_kernel_rfl

theorem toyBase_moduleOk :
    LeanQbe.T.ModuleOk (Env.ofTable toyBaseTable) toyBase_module := by
  refine Module.moduleOk_of_checkAcyclic toyBase_acyclic ?_ ?_
  · intro fn hmem
    simp only [toyBase_module, toyBase_fns, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl <;> t_wf_reify
  · intro fn hmem xs m Q X hlookup
    simp only [toyBase_module, toyBase_fns, List.mem_cons, List.not_mem_nil, or_false] at hmem
    dsimp only [toyBaseTable] at hlookup
    rcases hmem with rfl | rfl | rfl | rfl
    · dsimp only [Fn.name, Fn.as, Fn.rs, toy_leaf] at xs Q hlookup
      rw [Env.ofTable_cons_self] at hlookup
      exact toy_leaf_wp _ xs m Q X hlookup
    · dsimp only [Fn.name, Fn.as, Fn.rs, toy_mul] at xs Q hlookup
      rw [Env.ofTable_cons_ne (by decide)] at hlookup
      rw [Env.ofTable_cons_self] at hlookup
      exact toy_mul_wp _ xs m Q X hlookup
    · exact toy_mid_wp xs m Q X (by
        dsimp only [Fn.name, Fn.as, Fn.rs, toy_mid] at xs Q hlookup
        iterate 2 rw [Env.ofTable_cons_ne (by decide)] at hlookup
        rw [Env.ofTable_cons_self] at hlookup
        exact hlookup)
    · exact toy_caller_wp xs m Q X (by
        dsimp only [Fn.name, Fn.as, Fn.rs, toy_caller] at xs Q hlookup
        iterate 3 rw [Env.ofTable_cons_ne (by decide)] at hlookup
        rw [Env.ofTable_cons_self] at hlookup
        exact hlookup)

end Base

namespace Delta

c0_decl! toyDelta "
u64 toy_helper(u64 x) {
  return x + 10ULL;
}

u64 toy_leaf(u64 x) {
  return x + 2ULL;
}

u64 toy_mid(u64 x) {
  u64 h = toy_helper(x);
  u64 y = toy_leaf(h);
  return y + 3ULL;
}
"

def toyRepls : List Fn := [toy_leaf, toy_mid]
def toyBefores : List (Sym × List Fn) := [("toy_mid", [toy_helper])]

-- Exercise `splice_module!` with `befores` insertion!
splice_module! toyPatched Base.toyBase_module toyRepls (befores := toyBefores)

def toyHelperSpec : Spec [i64] [i64] :=
  fun (x, ()) m Q _ => ∀ r, r = x + 10#64 → Q (r, ()) m

def toyLeafV2Spec : Spec [i64] [i64] :=
  fun (x, ()) m Q _ => ∀ r, r = x + 2#64 → Q (r, ()) m

def toyMidV2Spec : Spec [i64] [i64] :=
  fun (x, ()) m Q _ => ∀ r, r = x + 15#64 → Q (r, ()) m

-- Tighten `toy_caller`'s spec in `rewiredRows` (same untouched IR, tightened row semantics)
def toyCallerRewiredSpec : Spec [i64] [i64] :=
  fun (x, ()) m Q _ => ∀ r, r = (x <<< 1) + 5#64 → Q (r, ()) m

def toyReplRows : List SpecEntry :=
  [ ⟨"toy_leaf", [i64], [i64], toyLeafV2Spec, true⟩
  , ⟨"toy_mid", [i64], [i64], toyMidV2Spec, true⟩ ]

def toyBeforeRows : List SpecEntry :=
  [ ⟨"toy_helper", [i64], [i64], toyHelperSpec, true⟩ ]

def toyRewiredRows : List SpecEntry :=
  [ ⟨"toy_caller", [i64], [i64], toyCallerRewiredSpec, true⟩ ]

def toyBundle : PatchBundle where
  baseMod := Base.toyBase_module
  baseTable := Base.toyBaseTable
  baseOk := Base.toyBase_moduleOk
  repls := toyRepls
  replRows := toyReplRows
  befores := toyBefores
  beforeRows := toyBeforeRows
  rewiredRows := toyRewiredRows

theorem toyBundle_moduleOk : LeanQbe.T.ModuleOk (patchEnv toyBundle) toyBundle.patchedMod := by
  have hModEq : toyBundle.patchedMod = toyPatched := rfl
  rw [hModEq]
  refine patchBundle_moduleOk_isolated toyBundle
    toyPatched_names_nodup
    toyPatched_replSigs_ok
    (fun fn h => by
      simp only [toyBundle, toyRepls, toyBefores, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with (rfl | rfl) | rfl <;> t_wf_reify)
    toyPatched_patchCallsOk
    (fun fn h => by
      simp only [toyBundle, toyRepls, toyBefores, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with (rfl | rfl) | rfl <;> decide)
    ?_
    (by t_kernel_rfl)
  intro fn e hfn_mem hfind
  dsimp only [toyBundle, PatchBundle.frontTable, toyRewiredRows, toyReplRows, toyBeforeRows] at hfind
  simp only [List.cons_append, List.nil_append] at hfind
  change fn ∈ [toy_leaf, Base.toy_mul, toy_helper, toy_mid, Base.toy_caller] at hfn_mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn_mem
  rcases hfn_mem with rfl | rfl | rfl | rfl | rfl
  · -- `toy_leaf`
    change some ⟨"toy_leaf", [i64], [i64], toyLeafV2Spec, true⟩ = some e at hfind
    cases hfind
    refine ⟨⟨rfl, rfl, rfl⟩, fun (x, ()) m Q X hspec => ?_⟩
    dsimp only [SpecEntry.cast, SpecEntry.eff, toyLeafV2Spec] at hspec
    dsimp only [toy_leaf, toy_leaf_body, Func.wp]
    c0_hsteps
    exact hspec _ rfl
  · -- `Base.toy_mul` (not in `frontTable`)
    change none = some e at hfind
    cases hfind
  · -- `toy_helper`
    change some ⟨"toy_helper", [i64], [i64], toyHelperSpec, true⟩ = some e at hfind
    cases hfind
    refine ⟨⟨rfl, rfl, rfl⟩, fun (x, ()) m Q X hspec => ?_⟩
    dsimp only [SpecEntry.cast, SpecEntry.eff, toyHelperSpec] at hspec
    dsimp only [toy_helper, toy_helper_body, Func.wp]
    c0_hsteps
    exact hspec _ rfl
  · -- `toy_mid`
    change some ⟨"toy_mid", [i64], [i64], toyMidV2Spec, true⟩ = some e at hfind
    cases hfind
    refine ⟨⟨rfl, rfl, rfl⟩, fun (x, ()) m Q X hspec => ?_⟩
    dsimp only [Fn.as, Fn.rs, toy_mid] at x Q hspec
    dsimp only [SpecEntry.cast, SpecEntry.eff, toyMidV2Spec] at hspec
    dsimp only [toy_mid, toy_mid_body, Func.wp]
    c0_hsteps
    · -- calls `toy_helper`: `toyRewiredRows ++ toyReplRows ++ toyBeforeRows ++ toyBaseTable`
      dsimp only [wp, patchEnv, toyBundle, PatchBundle.frontTable, toyRewiredRows, toyReplRows,
        toyBeforeRows]
      simp only [List.cons_append, List.nil_append]
      refine ⟨fun r m' => r = (x + 10#64, ()) ∧ m' = m, X, ?_, ?_, fun _ _ _ _ h => h⟩
      · iterate 3 rw [Env.ofTable_cons_ne (by decide)]
        rw [Env.ofTable_cons_self]
        intro r hr
        exact ⟨congrArg (·, ()) hr, rfl⟩
      · rintro r m'' ⟨rfl, hmeq⟩
        subst hmeq
        c0_hsteps
        · -- calls `toy_leaf`
          dsimp only [wp]
          refine ⟨fun r m' => r = ((x + 10#64) + 2#64, ()) ∧ m' = m'', X, ?_, ?_, fun _ _ _ _ h => h⟩
          · rw [Env.ofTable_cons_ne (by decide)]
            rw [Env.ofTable_cons_self]
            intro r2 hr2
            exact ⟨congrArg (·, ()) hr2, rfl⟩
          · rintro r2 m''' ⟨rfl, hm3⟩
            subst hm3
            c0_hsteps
            refine hspec _ ?_
            dsimp only [lift2, Arg.val]
            apply BitVec.eq_of_toNat_eq
            c0_bv_omega
  · -- `Base.toy_caller` (`rewiredRows`)
    change some ⟨"toy_caller", [i64], [i64], toyCallerRewiredSpec, true⟩ = some e at hfind
    cases hfind
    refine ⟨⟨rfl, rfl, rfl⟩, fun (x, ()) m Q X hspec => ?_⟩
    dsimp only [Fn.as, Fn.rs, Base.toy_caller] at x Q hspec
    dsimp only [SpecEntry.cast, SpecEntry.eff, toyCallerRewiredSpec] at hspec
    dsimp only [Base.toy_caller, Base.toy_caller_body, Func.wp]
    c0_hsteps
    · dsimp only [wp, patchEnv, toyBundle, PatchBundle.frontTable, toyRewiredRows, toyReplRows,
        toyBeforeRows, Base.toyBaseTable]
      simp only [List.cons_append, List.nil_append]
      refine ⟨fun r m' => r = (x * 2#64, ()) ∧ m' = m, X, ?_, ?_, fun _ _ _ _ h => h⟩
      · iterate 5 rw [Env.ofTable_cons_ne (by decide)]
        rw [Env.ofTable_cons_self]
        intro r hr
        exact ⟨congrArg (·, ()) hr, rfl⟩
      · rintro r m' ⟨rfl, rfl⟩
        c0_hsteps
        refine hspec _ ?_
        dsimp only [lift2, Arg.val]
        apply BitVec.eq_of_toNat_eq
        c0_bv_omega

/-! ## 2. `derive_reuse_bridge!` + Shifted Slices + Spec-Preserving `sameSpecs` -/

derive_reuse_bridge! toyBridge Base.toyBase_module toyPatched

theorem toyBridge_preserves_mul :
    (Base.toyBase_module.fns.drop 1).take 1 = (toyPatched.fns.drop 1).take 1 :=
  toyBridge_slice_0

theorem toyBridge_preserves_caller_shifted :
    (Base.toyBase_module.fns.drop 3).take 1 = (toyPatched.fns.drop 4).take 1 :=
  toyBridge_slice_1

theorem toyBridge_caller_fn_eq :
    Base.toyBase_module.fns[3]? = toyPatched.fns[4]? :=
  fn_eq_of_slice_eq toyBridge_preserves_caller_shifted (j := 0) (by decide)

end Delta

/-! ## 3. Spec-Preserving Replacement (`patchBundle_moduleOk_sameSpecs`) -/

namespace SameSpec

c0_decl! leafFast "
u64 toy_leaf(u64 x) {
  return 1ULL + x;
}
"

def fastRepls : List Fn := [toy_leaf]

splice_module! fastPatched Base.toyBase_module fastRepls

def fastReplRows : List SpecEntry :=
  [ ⟨"toy_leaf", [i64], [i64], Base.toyLeafSpec, true⟩ ]

def fastBundle : PatchBundle where
  baseMod := Base.toyBase_module
  baseTable := Base.toyBaseTable
  baseOk := Base.toyBase_moduleOk
  repls := fastRepls
  replRows := fastReplRows

theorem fastBundle_moduleOk : LeanQbe.T.ModuleOk (patchEnv fastBundle) fastBundle.patchedMod := by
  have hModEq : fastBundle.patchedMod = fastPatched := rfl
  rw [hModEq]
  refine patchBundle_moduleOk_sameSpecs fastBundle
    fastPatched_names_nodup
    fastPatched_replSigs_ok
    (fun fn h => by
      simp only [fastBundle, fastRepls, List.flatMap_nil, List.mem_cons, List.not_mem_nil,
        or_false] at h
      subst h
      t_wf_reify)
    fastPatched_patchCallsOk
    (fun fn h => by
      simp only [fastBundle, fastRepls, List.flatMap_nil, List.mem_cons, List.not_mem_nil,
        or_false] at h
      subst h
      decide)
    ?_
    ?_
  · intro fn e hmem hfind
    dsimp only [fastBundle, PatchBundle.frontTable, fastReplRows] at hfind
    change fn ∈ [toy_leaf, Base.toy_mul, Base.toy_mid, Base.toy_caller] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · change some ⟨"toy_leaf", [i64], [i64], Base.toyLeafSpec, true⟩ = some e at hfind
      cases hfind
      refine ⟨⟨rfl, rfl, rfl⟩, fun (x, ()) m Q X hspec => ?_⟩
      dsimp only [SpecEntry.cast, SpecEntry.eff, Base.toyLeafSpec] at hspec
      dsimp only [toy_leaf, toy_leaf_body, Func.wp]
      c0_hsteps
      refine hspec _ ?_
      apply BitVec.eq_of_toNat_eq
      c0_bv_omega
    · change none = some e at hfind; cases hfind
    · change none = some e at hfind; cases hfind
    · change none = some e at hfind; cases hfind
  · intro s hs xs m P E hbase
    simp only [fastBundle, Base.toyBase_module, Module.sigs, Base.toyBase_fns, List.map_cons,
      List.map_nil, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hs
    dsimp only [patchEnv, fastBundle, PatchBundle.frontTable, fastReplRows, Base.toyBaseTable] at hbase ⊢
    simp only [List.nil_append, List.cons_append, List.append_nil] at ⊢
    rcases hs with rfl | rfl | rfl | rfl
    · dsimp only [Fn.sig, Base.toy_leaf] at xs P hbase ⊢
      rw [Env.ofTable_cons_self] at hbase ⊢; exact hbase
    · dsimp only [Fn.sig, Base.toy_mul] at xs P hbase ⊢
      rw [Env.ofTable_cons_ne (by decide)]
      rw [Env.ofTable_cons_ne (by decide)] at hbase ⊢
      exact hbase
    · dsimp only [Fn.sig, Base.toy_mid] at xs P hbase ⊢
      rw [Env.ofTable_cons_ne (by decide)]
      rw [Env.ofTable_cons_ne (by decide)] at hbase ⊢
      exact hbase
    · dsimp only [Fn.sig, Base.toy_caller] at xs P hbase ⊢
      rw [Env.ofTable_cons_ne (by decide)]
      rw [Env.ofTable_cons_ne (by decide)] at hbase ⊢
      exact hbase

end SameSpec

/-! ## 4. Kissat `FullM7CongHash` 2-fn Splice + `derive_reuse_bridge!` -/

namespace KissatSubset

def m7ChRepl0 : Fn :=
  ⟨"full_cong_ht_hash_ent_m7", m7CongHtHashEntFn.as, m7CongHtHashEntFn.rs,
    fun V L xs => m7CongHtHashEntFn.body V L xs⟩

def m7ChRepl1 : Fn :=
  ⟨"full_cong_ht_init_m7", m7CongHtInitFn.as, m7CongHtInitFn.rs,
    fun V L xs => m7CongHtInitFn.body V L xs⟩

def m7ChRepls : List Fn := [m7ChRepl0, m7ChRepl1]

splice_module! m7ChSpliced m7CongHashModule m7ChRepls
  (baseAcyclic := m7CongHash_acyclic) (baseWf := m7CongHashFns_wf)

derive_reuse_bridge! m7ChBridge m7CongHashModule m7ChSpliced

theorem m7Ch_slot0_check :
    (m7CongHashModule.fns)[0]?.map Fn.sig = some m7CongHtHashEntFn.sig :=
  slotSig_at m7ChSpliced_slotSigs 0

theorem m7Ch_slot1_check :
    (m7CongHashModule.fns)[1]?.map Fn.sig = some m7CongHtInitFn.sig :=
  slotSig_at m7ChSpliced_slotSigs 1

theorem m7Ch_all_reused :
    (m7CongHashModule.fns.drop 0).take 6 = (m7ChSpliced.fns.drop 0).take 6 :=
  m7ChBridge_slice_0

end KissatSubset

#print axioms Delta.toyPatched_slotSigs
#print axioms Delta.toyPatched_wf
#print axioms KissatSubset.m7ChSpliced_slotSigs
#print axioms KissatSubset.m7ChSpliced_wf
check_std_axioms! Base.toyBase_moduleOk Delta.toyBundle_moduleOk
  Delta.toyPatched_slotSigs Delta.toyPatched_wf
  Delta.toyBridge_preserves_mul Delta.toyBridge_caller_fn_eq
  SameSpec.fastBundle_moduleOk KissatSubset.m7Ch_slot0_check KissatSubset.m7Ch_all_reused

end LeanQbeTest.T.PatchModuleTest
