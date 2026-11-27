module

public import LeanQbe.T.LeanLCNF.Sem.H
public import LeanQbe.T.LeanLCNF.Sem.SpecNorm
public import LeanQbe.T.LeanLCNF.LcnfC0Demo
public import LeanQbe.T.LeanLCNF.LcnfC0BigNumProof

namespace LeanQbeTest.T.LcnfSemHTest

open LeanQbe.T
open LeanQbe.T.LeanLCNF
open LeanQbe.T.LeanLCNF.Sem

public section

@[expose] public def addNatDecl : LcDecl :=
  { name := "LeanQbe.T.LeanLCNF.DemoNatStr.addNat",
    params :=
      [ { id := 1, ty := LcTy.tobject, borrow := true },
        { id := 2, ty := LcTy.tobject, borrow := true } ],
    retTy := LcTy.tobject,
    body := LcCode.let_ 3 LcTy.tobject
      (LcVal.fap "Nat.add" [LcArg.var 1, LcArg.var 2])
      (LcCode.ret (LcArg.var 3)) }

public theorem demoNatStrLcMod_head_eq :
    demoNatStrLcMod.decls.head? = some addNatDecl := by
  rfl

public theorem addNatDecl_mem_demoNatStrLcMod :
    addNatDecl ∈ demoNatStrLcMod.decls := by
  have h := demoNatStrLcMod_head_eq
  cases hds : demoNatStrLcMod.decls with
  | nil => simp [hds] at h
  | cons d ds =>
    simp [hds] at h
    simp [h]

/-- General Tier-H specification for `DemoNatStr.addNat` at runtime base `rt`,
covering both tagged scalar fast addition and BigNum slow-path addition. -/
@[expose] public def addNatHSpec (rt : BitVec 64) : HSpec :=
  fun args σ Q X =>
    ∃ a b : BitVec 64,
      args = [Word.i64 a, Word.i64 b] ∧
      HNatPrimWp rt "add" [Word.i64 a, Word.i64 b] Q X σ

/-- Runtime-parametric Tier-H spec for module-level `HModuleOk`. -/
@[expose] public def addNatHSpecEnv : HSpec :=
  fun args σ Q X =>
    ∀ rt : BitVec 64, HInv rt σ → addNatHSpec rt args σ Q X

public theorem addNatHSpec_mono (rt : BitVec 64) : (addNatHSpec rt).Mono := by
  intro args σ Q₁ Q₂ X₁ X₂ hQ hX ⟨a, b, heq, hwp⟩
  refine ⟨a, b, heq, ?_⟩
  have hwp' : HPrim.wp rt "Nat.add" [Word.i64 a, Word.i64 b] Q₁ X₁ σ := hwp
  exact HPrim.wp_mono hQ hX hwp'

private theorem hNatPrimWp_add_i64 (rt a b : BitVec 64) (σ : HState)
    (Q : HPost) (X : HXPost)
    (h : HNatPrimWp rt "add" [Word.i64 a, Word.i64 b] Q X σ) :
    HNatPrimWp rt "add" [Word.i64 a, Word.i64 b]
      (fun r σ' => r.fst = LcTy.tobject.toTTy ∧ Q r σ') X σ := by
  simp only [HNatPrimWp, natBinSlowInfo?, Word.toBV64?, Word.i64] at h ⊢
  cases hfb : natBinFast? "add" a b with
  | some w =>
    rw [hfb] at h
    simp only [natBinFast?] at hfb
    split at hfb
    · cases hfb
    · split at hfb
      · simp only [Option.some.injEq] at hfb
        subst hfb
        exact ⟨rfl, h⟩
      · cases hfb
  | none =>
    rw [hfb] at h
    rcases h with ⟨aVal, bVal, ha, hb, hok, hk⟩
    exact ⟨aVal, bVal, ha, hb, hok, fun res st' scrLimbs' objs' hm hr hwf hp =>
      ⟨rfl, hk res st' scrLimbs' objs' hm hr hwf hp⟩⟩

public theorem demoNatStr_addNat_hwp (Δ : HEnv) (rt : BitVec 64)
    (as : List Word) (σ : HState) (Q : HPost) (X : HXPost)
    (hspec : addNatHSpec rt as σ Q X) :
    HWp Δ rt addNatDecl.retTy HJEnv.empty
      (HValEnv.empty.bindAll addNatDecl.params as)
      Q X addNatDecl.body σ := by
  rcases hspec with ⟨a, b, rfl, hnat⟩
  have hi64 := hNatPrimWp_add_i64 rt a b σ Q X hnat
  have hprim : HPrim.wp rt "Nat.add" [Word.i64 a, Word.i64 b]
      (fun r σ' => r.fst = LcTy.tobject.toTTy ∧ Q r σ') X σ := hi64
  have hwp : HPrim.wp rt "Nat.add" [Word.i64 a, Word.i64 b]
      (fun r σ' => HWp Δ rt addNatDecl.retTy HJEnv.empty
        ((HValEnv.empty.bindAll addNatDecl.params [Word.i64 a, Word.i64 b]).set
          3 LcTy.tobject r)
        Q X (LcCode.ret (LcArg.var 3)) σ')
      X σ := by
    refine HPrim.wp_mono (fun w σ' ⟨hty, hw⟩ => ?_) (fun _ _ h => h) hprim
    simp only [HWp, HValEnv.evalArgAt, HValEnv.set, ↓reduceIte, hty]
    exact hw
  have hev : (HValEnv.empty.bindAll addNatDecl.params [Word.i64 a, Word.i64 b]).evalArgsOwn
      [LcArg.var 1, LcArg.var 2] = some [Word.i64 a, Word.i64 b] := rfl
  have his : isPrimName "Nat.add" = true := rfl
  change HWp Δ rt addNatDecl.retTy HJEnv.empty
    (HValEnv.empty.bindAll addNatDecl.params [Word.i64 a, Word.i64 b])
    Q X (LcCode.let_ 3 LcTy.tobject
      (LcVal.fap "Nat.add" [LcArg.var 1, LcArg.var 2])
      (LcCode.ret (LcArg.var 3))) σ
  simp only [HWp, HVal.wp, hev, his, ↓reduceIte]
  exact hwp

-- =========================================================================
-- NV 1: Scalar fast-path execution of DemoNatStr.addNat (13 + 29 = 42)
-- =========================================================================

@[expose] public def scalarRtBase : BitVec 64 := 0x10000#64

@[expose] public def scalarInitState : HState :=
  { st := initRtC0State scalarRtBase 8 256 (by decide) (by decide),
    objs := [],
    scr := 0x10000#64 + 64,
    scrLimbs := List.replicate 32 0#64 }

public theorem scalarInitState_inv : HInv scalarRtBase scalarInitState := by
  refine ⟨?_, by decide, by decide, by decide, by decide, by decide⟩
  unfold RtC0State.Bounded48
  decide

public theorem demoNatStr_addNat_scalar_hwp :
    HWp HEnv.bot scalarRtBase addNatDecl.retTy HJEnv.empty
      (HValEnv.empty.bindAll addNatDecl.params
        [Word.i64 (boxNat 13), Word.i64 (boxNat 29)])
      (fun w σ' => w = Word.i64 (boxNat 42) ∧ σ' = scalarInitState)
      (fun _ _ => False)
      addNatDecl.body scalarInitState := by
  apply demoNatStr_addNat_hwp
  refine ⟨boxNat 13, boxNat 29, rfl, ?_⟩
  apply HNatPrimWp_add_fast (by decide) (by decide) (by decide)
  have hsum : boxNat 13 - 1#64 + boxNat 29 = boxNat 42 := by decide
  rw [hsum]
  exact ⟨rfl, rfl⟩

public theorem demoNatStr_addNat_scalar_liftEnv (m₀ : Mem 64)
    (hm₀ : scalarInitState.mem scalarRtBase m₀) :
    liftEnv demoNatStrLcMod
      (fun name =>
        if name = addNatDecl.name then addNatHSpec scalarRtBase
        else HEnv.bot name)
      (mangleLc addNatDecl.name)
      (i64 :: List.take regArgs (List.map (fun x => x.ty.toTTy) addNatDecl.params))
      [addNatDecl.retTy.toTTy]
      (scalarRtBase, boxNat 13, boxNat 29, ())
      m₀
      (fun r m' => r = (boxNat 42, ()) ∧ scalarInitState.mem scalarRtBase m')
      (fun _ _ _ _ => False) := by
  apply liftEnv_of_mem addNatDecl_mem_demoNatStrLcMod
  rw [liftDeclSpec_iff_liftSpec_of_le _ _ _ (by decide)]
  refine ⟨scalarInitState, Std.ExtHashMap.emp, scalarInitState_inv, ?_, ?_⟩
  · rw [Std.ExtHashMap.sep_emp]
    exact hm₀
  · simp only [addNatDecl]
    refine ⟨boxNat 13, boxNat 29, rfl, ?_⟩
    apply HNatPrimWp_add_fast (by decide) (by decide) (by decide)
    have hsum : boxNat 13 - 1#64 + boxNat 29 = boxNat 42 := by decide
    rw [hsum]
    refine ⟨rfl, ?_⟩
    intro m' _ hm'
    rw [Std.ExtHashMap.sep_emp] at hm'
    exact ⟨rfl, hm'⟩

-- =========================================================================
-- NV 2: BigNum slow-path execution on concrete nvBnMem
-- =========================================================================

@[expose] public def nvHState : HState :=
  { st := nvBnRtState,
    objs := nvBnObjs,
    scr := nvBnScr,
    scrLimbs := nvBnScrLimbs }

public theorem nvHState_mem : nvHState.mem nvBnRtBase nvBnMem := by
  unfold HState.mem nvHState
  exact nvBnMem_ok

public theorem nvHState_inv : HInv nvBnRtBase nvHState := by
  refine ⟨?_, by decide, by decide, by decide, by decide, by decide⟩
  unfold RtC0State.Bounded48
  decide

private theorem nvBnNatA_rep :
    natRep nvBnAddrNatA nvValNatA nvHState.objs := by
  unfold natRep
  by_cases hlt : nvValNatA < 2 ^ 63
  · exact absurd hlt (by decide)
  · simp only [hlt, ↓reduceIte]
    refine ⟨by decide, nvBnNatA, by simp [nvHState, nvBnObjs], ?_⟩
    refine ⟨by decide, ?_, by decide, by decide, by decide,
      by decide, by decide, by decide, ?_, by decide⟩
    · refine ⟨by decide, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide, by decide, ?_⟩
      simp [nvBnNatA, closureTag, arrayTag, sarrayTag, stringTag, mpzTag]
    · simp [nvBnNatA]
      decide

private theorem nvBnNatB_rep :
    natRep nvBnAddrNatB nvValNatB nvHState.objs := by
  unfold natRep
  by_cases hlt : nvValNatB < 2 ^ 63
  · exact absurd hlt (by decide)
  · simp only [hlt, ↓reduceIte]
    refine ⟨by decide, nvBnNatB, by simp [nvHState, nvBnObjs], ?_⟩
    refine ⟨by decide, ?_, by decide, by decide, by decide,
      by decide, by decide, by decide, ?_, by decide⟩
    · refine ⟨by decide, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide, by decide, ?_⟩
      simp [nvBnNatB, closureTag, arrayTag, sarrayTag, stringTag, mpzTag]
    · simp [nvBnNatB]
      decide

private theorem nvBnNatAdd_ok :
    natArithOk 1 nvValNatA nvValNatB nvHState.scrLimbs.length nvHState.st := by
  simp only [natArithOk, canAllocBytes, RtC0State.hasFree]
  decide

public theorem demoNatStr_addNat_bignum_hwp :
    HWp HEnv.bot nvBnRtBase addNatDecl.retTy HJEnv.empty
      (HValEnv.empty.bindAll addNatDecl.params
        [Word.i64 nvBnAddrNatA, Word.i64 nvBnAddrNatB])
      (fun w σ' =>
        ∃ res : BitVec 64,
          w = Word.i64 res ∧
          natRep res (nvValNatA + nvValNatB) σ'.objs ∧
          (∀ o ∈ nvHState.objs, o ∈ σ'.objs))
      (fun _ _ => False)
      addNatDecl.body nvHState := by
  apply demoNatStr_addNat_hwp
  refine ⟨nvBnAddrNatA, nvBnAddrNatB, rfl, ?_⟩
  simp only [HNatPrimWp, natBinSlowInfo?, Word.toBV64?, Word.i64]
  have hfast : natBinFast? "add" nvBnAddrNatA nvBnAddrNatB = none := by decide
  rw [hfast]
  refine ⟨nvValNatA, nvValNatB, nvBnNatA_rep, Or.inr nvBnNatB_rep, nvBnNatAdd_ok, ?_⟩
  intro res st' scrLimbs' objs' _ _ _ hpost
  rcases hpost with ⟨hrep, hmem⟩
  exact ⟨res, by simp, hrep, hmem⟩

public theorem demoNatStr_addNat_bignum_liftEnv :
    liftEnv demoNatStrLcMod
      (fun name =>
        if name = addNatDecl.name then addNatHSpec nvBnRtBase
        else HEnv.bot name)
      (mangleLc addNatDecl.name)
      (i64 :: List.take regArgs (List.map (fun x => x.ty.toTTy) addNatDecl.params))
      [addNatDecl.retTy.toTTy]
      (nvBnRtBase, nvBnAddrNatA, nvBnAddrNatB, ())
      nvBnMem
      (fun r m' =>
        ∃ σ' : HState,
          HInv nvBnRtBase σ' ∧
          σ'.mem nvBnRtBase m' ∧
          natRep r.1 (nvValNatA + nvValNatB) σ'.objs ∧
          (∀ o ∈ nvHState.objs, o ∈ σ'.objs))
      (fun _ _ _ _ => False) := by
  apply liftEnv_of_mem addNatDecl_mem_demoNatStrLcMod
  rw [liftDeclSpec_iff_liftSpec_of_le _ _ _ (by decide)]
  refine ⟨nvHState, Std.ExtHashMap.emp, nvHState_inv, ?_, ?_⟩
  · rw [Std.ExtHashMap.sep_emp]
    exact nvHState_mem
  · simp only [addNatDecl]
    refine ⟨nvBnAddrNatA, nvBnAddrNatB, rfl, ?_⟩
    simp only [HNatPrimWp, natBinSlowInfo?, Word.toBV64?, Word.i64]
    have hfast : natBinFast? "add" nvBnAddrNatA nvBnAddrNatB = none := by decide
    rw [hfast]
    refine ⟨nvValNatA, nvValNatB, nvBnNatA_rep, Or.inr nvBnNatB_rep, nvBnNatAdd_ok, ?_⟩
    intro res st' scrLimbs' objs' _ _ _ hpost
    rcases hpost with ⟨hrep, hmem⟩
    have hsw : res.setWidth 64 = res := BitVec.setWidth_eq res
    rw [hsw]
    refine ⟨rfl, ?_⟩
    intro m' hinv' hm'
    rw [Std.ExtHashMap.sep_emp] at hm'
    exact ⟨{ st := st', objs := objs', scr := nvHState.scr, scrLimbs := scrLimbs' },
      hinv', hm', hrep, hmem⟩

-- =========================================================================
-- NV 3: HModuleOk, Frame, Join-Loop, and SpecNorm checks
-- =========================================================================

@[expose] public def addNatOnlyMod : LcModule :=
  { name := "addNatOnly",
    decls := [addNatDecl],
    externs := [],
    roots := [],
    snaps := [] }

public theorem addNatOnlyMod_hmoduleOk :
    HModuleOk
      (fun name => if name = addNatDecl.name then addNatHSpecEnv else HEnv.bot name)
      addNatOnlyMod := by
  intro d hd rt as σ Q X hinv _ hspec
  simp only [addNatOnlyMod, List.mem_singleton] at hd
  subst hd
  simp only [↓reduceIte] at hspec
  exact demoNatStr_addNat_hwp _ rt _ σ Q X (hspec rt hinv)

@[expose] public def jpLoopCode : LcCode :=
  LcCode.jp 10 [{ id := 20, ty := LcTy.tobject, borrow := true }]
    (LcCode.ret (LcArg.var 20))
    (LcCode.jmp 10 [LcArg.var 1])

public theorem jpLoop_and_frame_smoke :
    HWp HEnv.bot scalarRtBase LcTy.tobject HJEnv.empty
      (HValEnv.empty.set 1 LcTy.tobject (Word.i64 (boxNat 42)))
      (fun r σ' => (nvValNatA > 0) ∧ (r = Word.i64 (boxNat 42) ∧ σ' = scalarInitState))
      (fun _ _ => (nvValNatA > 0) ∧ False)
      jpLoopCode scalarInitState := by
  apply HWp_frame_pure (by decide)
  apply HWp_jp_loop
    (fun n as σ' => n = 0 ∧ as = [Word.i64 (boxNat 42)] ∧ σ' = scalarInitState)
  · intro n as σ' ⟨_, has, _⟩
    subst has
    exact ⟨rfl, trivial⟩
  · intro Jj n as σ' _ ⟨_, has, hσ⟩
    subst has
    subst hσ
    change match some (Word.i64 (boxNat 42)) with
      | some w => w = Word.i64 (boxNat 42) ∧ scalarInitState = scalarInitState
      | none => False
    exact ⟨rfl, rfl⟩
  · intro Jj hJj
    have hev : (HValEnv.empty.set 1 LcTy.tobject (Word.i64 (boxNat 42))).evalArgsOwn
        [LcArg.var 1] = some [Word.i64 (boxNat 42)] := rfl
    change match (HValEnv.empty.set 1 LcTy.tobject (Word.i64 (boxNat 42))).evalArgsOwn
        [LcArg.var 1] with
      | some ws => Jj ws scalarInitState
      | none => False
    rw [hev]
    exact hJj 0 [Word.i64 (boxNat 42)] scalarInitState ⟨rfl, rfl, rfl⟩

public theorem liftSpec_frame_scalar_smoke (m₀ : Mem 64)
    (hm₀ : scalarInitState.mem scalarRtBase m₀) :
    liftSpec (addNatHSpec scalarRtBase)
      [LcTy.tobject.toTTy, LcTy.tobject.toTTy] LcTy.tobject.toTTy
      (scalarRtBase, boxNat 13, boxNat 29, ())
      m₀
      (fun r m' => r = (boxNat 42, ()) ∧ scalarInitState.mem scalarRtBase m')
      (fun _ _ _ _ => False) := by
  apply liftSpec_frame (addNatHSpec scalarRtBase) (addNatHSpec_mono scalarRtBase)
  rw [Std.ExtHashMap.sep_emp]
  refine ⟨scalarInitState, Std.ExtHashMap.emp, scalarInitState_inv, ?_, ?_⟩
  · rw [Std.ExtHashMap.sep_emp]
    exact hm₀
  · simp only [wordsOfTup]
    refine ⟨boxNat 13, boxNat 29, rfl, ?_⟩
    apply HNatPrimWp_add_fast (by decide) (by decide) (by decide)
    have hsum : boxNat 13 - 1#64 + boxNat 29 = boxNat 42 := by decide
    rw [hsum]
    refine ⟨rfl, ?_⟩
    intro m₁ _ hm₁ m' hm''
    rw [Std.ExtHashMap.sep_emp] at hm₁ hm''
    exact ⟨rfl, hm'' ▸ hm₁⟩

public theorem specNorm_rtC0CoreEnv_check :
    (∀ xs m Q X, lcnfNatSlowSpec xs m Q X → rtC0CoreEnv "lcnf_nat_slow" _ _ xs m Q X) ∧
    (∀ xs m Q X, lcnfIntOpSpec xs m Q X → rtC0CoreEnv "lcnf_int_op" _ _ xs m Q X) ∧
    (∀ xs m Q X, lcnfNatBitsSpec xs m Q X → rtC0CoreEnv "lcnf_nat_bits" _ _ xs m Q X) ∧
    (∀ xs m Q X, bnNatPowSpec xs m Q X → rtC0CoreEnv "bn_nat_pow" _ _ xs m Q X) ∧
    (∀ xs m Q X, bnNatGcdSpec xs m Q X → rtC0CoreEnv "bn_nat_gcd" _ _ xs m Q X) ∧
    (∀ xs m Q X, bnDecNatSpec xs m Q X → rtC0CoreEnv "bn_dec_nat" _ _ xs m Q X) ∧
    (∀ xs m Q X, lcnfIntMulDivSpec xs m Q X → rtC0CoreEnv "lcnf_int_muldiv" _ _ xs m Q X) ∧
    (∀ xs m Q X, lcnfIntAddSubCmpSpec xs m Q X →
      rtC0CoreEnv "lcnf_int_addsub_cmp" _ _ xs m Q X) ∧
    (∀ xs m Q X, lcnfNatAllocSpec xs m Q X → rtC0CoreEnv "lcnf_nat_alloc" _ _ xs m Q X) ∧
    (∀ xs m Q X, lcnfIntConvSpec xs m Q X → rtC0CoreEnv "lcnf_int_conv" _ _ xs m Q X) ∧
    (∀ xs m Q X, lcnfNatArithSpec xs m Q X → rtC0CoreEnv "lcnf_nat_arith" _ _ xs m Q X) ∧
    (∀ obj n, natRep obj n [] → NatInHeap obj n []) ∧
    (∀ obj n, obj &&& 1#64 ≠ 0#64 → NatInHeap obj n [] → natRep obj n []) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun _ _ _ _ h => lcnfNatSlowSpec_le_rtC0CoreEnv h
  · exact fun _ _ _ _ h => lcnfIntOpSpec_le_rtC0CoreEnv h
  · exact fun _ _ _ _ h => lcnfNatBitsSpec_le_rtC0CoreEnv h
  · exact fun _ _ _ _ h => bnNatPowSpec_le_rtC0CoreEnv h
  · exact fun _ _ _ _ h => bnNatGcdSpec_le_rtC0CoreEnv h
  · exact fun _ _ _ _ h => bnDecNatSpec_le_rtC0CoreEnv h
  · exact fun _ _ _ _ h => lcnfIntMulDivSpec_le_rtC0CoreEnv h
  · exact fun _ _ _ _ h => lcnfIntAddSubCmpSpec_le_rtC0CoreEnv h
  · exact fun _ _ _ _ h => lcnfNatAllocSpec_le_rtC0CoreEnv h
  · exact fun _ _ _ _ h => lcnfIntConvSpec_le_rtC0CoreEnv h
  · exact fun _ _ _ _ h => lcnfNatArithSpec_le_rtC0CoreEnv h
  · exact fun _ _ h => natRep_to_natInHeap h (fun _ ho => by cases ho)
  · exact fun _ _ htag h => natInHeap_to_natRep_small htag h

end

end LeanQbeTest.T.LcnfSemHTest
