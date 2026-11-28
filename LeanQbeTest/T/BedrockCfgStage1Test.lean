module

import LeanQbe.T.Unified.CfgRecovery
import LeanQbe.T.Unified.CfgContifyProof
meta import LeanQbe.T.Unified.CfgContify
import LeanQbe.T.FlatLemmas
import LeanQbe.T.OpsLemmas

/-!
# End-to-End Tests for Stage-1 `Unified.CfgContify`
(`Unified.CfgContify`, `CfgContifyLemmas`, `CfgContifyProofPrefix`, `CfgContifyProof`)

Exercises:
1. Nested Bourdoncle `.loop`-in-`.loop` calling a `.contified false` `retM` helper (`Ex 6`) ->
   `Fn.mid` (`liftContifyRegion_mid_wf` & `checkAndLiftContify_cm_wp_to_mid`, `std3`).
2. Dual-return `rp + 8` contification (`Ex 2b`) with a promoted private stack slot live across
   a `memFree` dual-return `.contCall` -> `Fn.mid` (`std3`).
3. Private stack-slot promotion (`nSlots = 2`) eliminating all `.load`/`.store` ops inside loop
   bodies (`PrivFrameOk` -> `Fn.mid`, `std3`).
4. Negative escaped-pointer / aliasing bailout:
   (a) static rejection (`dynAliasGuard = false` -> `check = false`, `.error`);
   (b) runtime disjointness check + `flushFrame` + `lowerUnpromotedTail` hybrid soundness
       (`dynAliasGuard = true`, `checkAndLiftContify_hybrid_sound`, `std3`).
5. `#print axioms` checks confirming all Stage-1 theorems depend ONLY on
   `⊆ [propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.BedrockCfgStage1Test

open LeanQbe.T
open LeanQbe.T.BedrockWord
open LeanQbe.T.Unified

@[local simp] private theorem allPcs_leaf (pc : BitVec 64) :
    GroupTree.allPcs (.leaf pc) = [pc] := GroupTree.allPcs.eq_1 pc

@[local simp] private theorem allPcs_loop (h : BitVec 64) (ns : List GroupTree) :
    GroupTree.allPcs (.loop h ns) = ns.flatMap GroupTree.allPcs := GroupTree.allPcs.eq_2 h ns

def mkEntry (nm : Sym) (addr : BitVec 64) (b : BlockP) : CodeEntry :=
  ⟨nm, addr, reifyBlock b⟩

def haltSpec (code : BitVec 64) : XPost := fun s ts xs _ =>
  match s, ts with
  | "bw_halt", [.bits 64] => xs.1 = code
  | _, _ => False

def haltPredX (P : BitVec 64 → Prop) : XPost := fun s ts xs _ =>
  match s, ts with
  | "bw_halt", [.bits 64] => P xs.1
  | _, _ => False

def contWitCount (o : Option ContifyWitness) : Nat :=
  match o with
  | some w => w.regions.length
  | none => 0

def contLiftCount (cm : CodeMap) (wit : ContifyWitness) : Nat :=
  match checkAndLiftContify cm wit with
  | .ok (fns, _) => fns.length
  | .error _ => 0

def contCheckBool (cm : CodeMap) (callees : List ContCalleeMeta) (cr : ContifyRegion)
    (allPcs : List (BitVec 64)) : Bool :=
  let nSlots := cr.privFrame.numSlots
  let entries := cr.tree.map GroupTree.entryPc
  let pcs := pushLabelPcs entries []
  let tf := liftContifyTFlat cm cr
  fnNameOk cr.name && (nSlots ≤ 64) && (nSlots == 0 || cr.abi == .retEnvelope) &&
  (!cr.tree.isEmpty) && (cm.lookupAddr cr.entryPc).isSome && entries.contains cr.entryPc &&
  listNodup allPcs && checkContGroupNodes cm cr callees pcs cr.tree &&
  tf.wfCheck regCtx [] && tf.noHlt

private theorem check_one_cont_eq (cm : CodeMap) (r : ContifyRegion) (a : List (BitVec 64))
    (ha : r.allPcs = a) (b : Bool)
    (h : (listNodup [r.name] && listNodup a && (contCheckBool cm [] r a && true)) = b) :
    ContifyWitness.check cm ⟨[r]⟩ = b := by
  dsimp only [ContifyWitness.check, ContifyWitness.checkAux, ContifyRegion.check,
    contCheckBool] at h ⊢
  have hf : List.flatMap ContifyRegion.allPcs [r] = a := by simp [ha]
  rw [hf, ha]; exact h

private theorem check_two_cont_true (cm : CodeMap) (r₁ r₂ : ContifyRegion)
    (a₁ a₂ aTot : List (BitVec 64)) (c₁ : ContCalleeMeta)
    (ha₁ : r₁.allPcs = a₁) (ha₂ : r₂.allPcs = a₂)
    (hat : ([r₁, r₂].flatMap ContifyRegion.allPcs) = aTot)
    (hc₁ : r₁.toCalleeMeta? cm [] = some c₁)
    (h : (listNodup ([r₁, r₂].map (·.name)) && listNodup aTot &&
      (contCheckBool cm [] r₁ a₁ && (contCheckBool cm [c₁] r₂ a₂ && true))) = true) :
    ContifyWitness.check cm ⟨[r₁, r₂]⟩ = true := by
  dsimp only [ContifyWitness.check, ContifyWitness.checkAux, ContifyRegion.check,
    contCheckBool] at h ⊢
  rw [hat, ha₁, ha₂, hc₁]; exact h

def hasMemOps : {rs : List Ty} → TFlat rs → Bool
  | _, .let_ _ k => hasMemOps k
  | _, .load _ _ _ => true
  | _, .store _ _ _ => true
  | _, .call _ _ _ k => hasMemOps k
  | _, .jnz _ t e => hasMemOps t || hasMemOps e
  | _, .group _ k => hasMemOps k
  | _, .jump _ _ | _, .ret _ | _, .exit _ _ | _, .hlt => false

/-- Inspect lifted blocks inside `Fn.body` (excluding outer `loadEntryFrameAux` prelude) for any
residual `.load`/`.store`. Helper is `meta` only for `#eval` sanity testing. -/
def fnGroupBodyHasMem (cm : CodeMap) (cr : ContifyRegion) (pc : BitVec 64) : Bool :=
  let nSlots := cr.privFrame.numSlots
  let pcs := pushLabelPcs (cr.tree.map GroupTree.entryPc) []
  match cm.lookupAddr pc with
  | some b =>
      hasMemOps (liftContifyBlock cm cr.abi cr.privFrame cr.toRegionWitness pcs pc b []
        ContSymState.init (if nSlots = 0 then 6 else 7 + nSlots) initEnvMap
        (initSlotsLvls nSlots))
  | none => true

/-! ## 1. Nested Bourdoncle `.loop`-in-`.loop` Calling `retM` Helper (`Ex 6`) -> `Fn.mid` -/

def bNestedOutHdr : BlockP := fun _ r =>
  .letOp2 (.cmp .ult i64) (.imm 0#64) (.var r.r1) fun c =>
  .jnz (.var c) (.ijmp (.imm 16#64) r.keep) (.ijmp (.imm 40#64) r.keep)

theorem bNestedOutHdr_wf : bNestedOutHdr.Wf := by
  intro V₁ V₂ r₁ r₂
  refine .let_ (.mk _ (.cons (.imm _) (.cons (.var (by simp [Tup.zip, RegsV.toTup])) .nil)))
    fun _ _ => .jnz (.var (by simp [Tup.zip])) ?_ ?_
  · exact .ijmp (.imm _)
      ⟨.var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
       .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
       .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup])⟩
  · exact .ijmp (.imm _)
      ⟨.var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
       .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
       .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup])⟩

def cmNested : CodeMap :=
  [ mkEntry "ret_step" 0#64 (fun _ r =>
      .letOp2 (.sub i64) (.var r.r2) (.imm 1#64) fun r2' =>
      .letOp2 (.add i64) (.var r.rv) (.imm 1#64) fun rv' =>
      .ijmp (.var r.rp) { r.keep with r2 := .var r2', rv := .var rv' }),
    mkEntry "out_hdr" 8#64 bNestedOutHdr,
    mkEntry "in_hdr" 16#64 (fun _ r =>
      .letOp2 (.cmp .ult i64) (.imm 0#64) (.var r.r2) fun c =>
      .jnz (.var c) (.ijmp (.imm 24#64) r.keep) (.ijmp (.imm 32#64) r.keep)),
    mkEntry "in_body" 24#64 (fun _ r =>
      .codeAddr "in_hdr" fun retPc =>
      .jmpSym "ret_step" { r.keep with rp := .var retPc }),
    mkEntry "out_step" 32#64 (fun _ r =>
      .letOp2 (.sub i64) (.var r.r1) (.imm 1#64) fun r1' =>
      .ijmp (.imm 8#64) { r.keep with r1 := .var r1', r2 := .imm 2#64 }),
    mkEntry "done" 40#64 (fun _ r => .halt (.var r.rv)) ]

def nestedHelperCr : ContifyRegion :=
  { name := "ret_step"
    entryPc := 0#64
    abi := .contified false
    tree := [.leaf 0#64]
    edges := [⟨0#64, [], .contRet false⟩]
    retainFallbacks := true }

def nestedMainCr : ContifyRegion :=
  { name := "out_hdr_reg"
    entryPc := 8#64
    abi := .retEnvelope
    tree :=
      [ .loop 8#64
          [ .leaf 8#64,
            .loop 16#64 [.leaf 16#64, .leaf 24#64],
            .leaf 32#64 ],
        .leaf 40#64 ]
    edges :=
      [ ⟨8#64, [true], .direct 16#64⟩,
        ⟨8#64, [false], .direct 40#64⟩,
        ⟨16#64, [true], .direct 24#64⟩,
        ⟨16#64, [false], .direct 32#64⟩,
        ⟨24#64, [], .contCall "ret_step" 0#64 false 16#64 none⟩,
        ⟨32#64, [], .direct 8#64⟩ ]
    retainFallbacks := true }

def nestedWit : ContifyWitness := ⟨[nestedHelperCr, nestedMainCr]⟩

#eval show IO Unit from do
  if contWitCount (analyzeContify cmNested) != 2 then
    throw (IO.userError "nested analyzeContify mismatch")

theorem nested_check : nestedWit.check cmNested = true := by
  refine check_two_cont_true cmNested nestedHelperCr nestedMainCr
    [0#64] [8#64, 16#64, 24#64, 32#64, 40#64] [0#64, 8#64, 16#64, 24#64, 32#64, 40#64]
    ⟨"ret_step", 0#64, false, regionMemFree cmNested [] nestedHelperCr⟩
    (by simp [nestedHelperCr, ContifyRegion.allPcs])
    (by simp [nestedMainCr, ContifyRegion.allPcs])
    (by simp [nestedHelperCr, nestedMainCr, ContifyRegion.allPcs])
    (by simp [ContifyRegion.toCalleeMeta?, nestedHelperCr]) ?_
  t_kernel_rfl

theorem nested_lift_eq :
    checkAndLiftContify cmNested nestedWit =
      .ok ([liftContifyRegion cmNested nestedHelperCr, liftContifyRegion cmNested nestedMainCr],
        residualContifyCodeMap cmNested nestedWit) := by
  dsimp only [checkAndLiftContify]; rw [nested_check]; rfl

theorem nested_lift_count : contLiftCount cmNested nestedWit = 2 := by
  simp [contLiftCount, nested_lift_eq]

theorem nested_helper_supports_scalar64 :
    ((liftContifyRegion cmNested nestedHelperCr).earlyOpt).body.supportsSource .scalar64 =
      true := by t_kernel_rfl

theorem nested_main_supports_scalar64 :
    ((liftContifyRegion cmNested nestedMainCr).earlyOpt).body.supportsSource .scalar64 =
      true := by t_kernel_rfl

theorem nested_main_supports_x64 :
    ((liftContifyRegion cmNested nestedMainCr).earlyOpt).body.supportsSource .x64 =
      true := by t_kernel_rfl

theorem nested_main_mid_wf : ((liftContifyRegion cmNested nestedMainCr).mid .scalar64).Wf :=
  liftContifyRegion_mid_wf cmNested nestedMainCr .scalar64 nested_main_supports_scalar64

theorem nested_cm_wp_n0 (r₀ : Regs) (m : Mem 64) (h0 : r₀.r1 = 0#64) :
    cmNested.wp (fun c _ => c = r₀.rv) 8#64 ⟨r₀, m⟩ := by
  intro Ψ hClosed
  have h40 : cmNested.lookupAddr 40#64 = some (reifyBlock fun _ r => .halt (.var r.rv)) := by
    t_kernel_rfl
  have hDone : Ψ 40#64 ⟨r₀, m⟩ := hClosed 40#64 _ h40 ⟨r₀, m⟩ rfl
  refine hClosed.applyP (by t_kernel_rfl : cmNested.lookupAddr 8#64 =
      some (reifyBlock bNestedOutHdr)) bNestedOutHdr_wf ?_
  dsimp only [bNestedOutHdr, BlockP.wp, BlockB.wp, op2, Op.wp, OpCode.wp, evalOpCode, Arg.val,
    Regs.toRegsV, RegsV.keep, RegsExpr.eval, vals]
  rw [h0]
  refine ⟨fun hT => ?_, fun _ => ?_⟩
  · have hF : liftCmp (fun {n} => CmpOp.ult.evalBits) CmpOp.ult.evalBool i64 0#64
        ((rfl : i64 = i64) ▸ 0#64) = false := by decide
    rw [hF] at hT; cases hT
  · have hReg : ({ r₀ with r1 := 0#64 } : Regs) = r₀ := by
      cases r₀; simp at h0; subst h0; rfl
    rw [hReg]; exact hDone

theorem nested_main_mid_spec (r₀ : Regs) (m : Mem 64) (h0 : r₀.r1 = 0#64) :
    Func.spec (legalEnv .scalar64 (witContifyEnv cmNested nestedWit))
      ((liftContifyRegion cmNested nestedMainCr).mid .scalar64).body
      (encodeTup .scalar64 regSig r₀.toRegsV.toTup) m
      (legalPost .scalar64 (regionRetPost .retEnvelope
        (cmNested.wp (fun c _ => c = r₀.rv)) r₀.rp))
      (legalXPost .scalar64 (haltSpec r₀.rv)) :=
  checkAndLiftContify_cm_wp_to_mid cmNested nestedWit (fun c _ => c = r₀.rv)
    (haltSpec r₀.rv) .scalar64 nested_lift_eq (fun _ _ hc => hc) (by simp [nestedWit])
    nested_main_supports_scalar64 r₀ m (fun h => by cases h) (nested_cm_wp_n0 r₀ m h0)

/-! ## 2. Dual-Return `rp + 8` Contification (`Ex 2b`) + Promoted Slot Live Across `contCall` -/

def bCheckedSub : BlockP := fun _ r =>
  .letOp2 (.cmp .ult i64) (.var r.r1) (.var r.r2) fun underflow =>
  .jnz (.var underflow)
    (.letOp2 (.add i64) (.var r.rp) (.imm 8#64) fun rp8 =>
     .ijmp (.var rp8) { r.keep with rv := .imm 0#64 })
    (.letOp2 (.sub i64) (.var r.r1) (.var r.r2) fun diff =>
     .ijmp (.var r.rp) { r.keep with rv := .var diff })

theorem bCheckedSub_wf : bCheckedSub.Wf := by
  intro V₁ V₂ r₁ r₂
  refine .let_ (.mk _ (.cons (.var (by simp [Tup.zip, RegsV.toTup]))
      (.cons (.var (by simp [Tup.zip, RegsV.toTup])) .nil))) fun _ _ => ?_
  refine .jnz (.var (by simp [Tup.zip])) ?_ ?_
  · refine .let_ (.mk _ (.cons (.var (by simp [Tup.zip, RegsV.toTup]))
        (.cons (.imm _) .nil))) fun _ _ => ?_
    exact .ijmp (.var (by simp [Tup.zip]))
      ⟨.var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
       .imm _, .var (by simp [Tup.zip, RegsV.toTup]),
       .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup])⟩
  · refine .let_ (.mk _ (.cons (.var (by simp [Tup.zip, RegsV.toTup]))
        (.cons (.var (by simp [Tup.zip, RegsV.toTup])) .nil))) fun _ _ => ?_
    exact .ijmp (.var (by simp [Tup.zip, RegsV.toTup]))
      ⟨.var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
       .var (by simp [Tup.zip]), .var (by simp [Tup.zip, RegsV.toTup]),
       .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup])⟩

def bDualSlotCaller : BlockP := fun _ r =>
  .letOp2 (.sub i64) (.var r.sp) (.imm 8#64) fun a0 =>
  .store (t := i64) (.var r.r3) (.var a0)
  (.codeAddr "ok_cont" fun k0 =>
   .jmpSym "checked_sub" { r.keep with rp := .var k0 })

theorem bDualSlotCaller_wf : bDualSlotCaller.Wf := by
  intro V₁ V₂ r₁ r₂
  refine .let_ (.mk _ (.cons (.var (by simp [Tup.zip, RegsV.toTup]))
      (.cons (.imm _) .nil))) fun _ _ => ?_
  refine .store (.var (by simp [Tup.zip, RegsV.toTup])) (.var (by simp [Tup.zip])) ?_
  refine .codeAddr _ fun _ _ => .codeAddr _ fun _ _ => .ijmp (.var (by simp))
    ⟨.var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
     .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
     .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup])⟩

def bOkCont : BlockP := fun _ r =>
  .letOp2 (.sub i64) (.var r.sp) (.imm 8#64) fun a0 =>
  .load i64 (.var a0) fun saved =>
  .letOp2 (.add i64) (.var r.rv) (.var saved) fun ans =>
  .halt (.var ans)

theorem bOkCont_wf : bOkCont.Wf := by
  intro V₁ V₂ r₁ r₂
  refine .let_ (.mk _ (.cons (.var (by simp [Tup.zip, RegsV.toTup]))
      (.cons (.imm _) .nil))) fun _ _ => ?_
  refine .load i64 (.var (by simp [Tup.zip])) fun _ _ => ?_
  refine .let_ (.mk _ (.cons (.var (by simp [Tup.zip, RegsV.toTup]))
      (.cons (.var (by simp)) .nil))) fun _ _ => ?_
  exact .halt (.var (by simp [Tup.zip]))

def cmDualSlot : CodeMap :=
  [ mkEntry "checked_sub" 0#64 bCheckedSub,
    mkEntry "caller" 8#64 bDualSlotCaller,
    mkEntry "ok_cont" 16#64 bOkCont,
    mkEntry "err_cont" 24#64 (fun _ _ => .halt (.imm 999#64)) ]

def dualCalleeCr : ContifyRegion :=
  { name := "checked_sub"
    entryPc := 0#64
    abi := .contified true
    tree := [.leaf 0#64]
    edges := [⟨0#64, [true], .contRet true⟩, ⟨0#64, [false], .contRet false⟩]
    retainFallbacks := true }

def dualCallerCr : ContifyRegion :=
  { name := "caller_reg"
    entryPc := 8#64
    abi := .retEnvelope
    privFrame := ⟨1, false⟩
    tree := [.leaf 8#64, .leaf 16#64, .leaf 24#64]
    edges := [⟨8#64, [], .contCall "checked_sub" 0#64 true 16#64 (some 24#64)⟩]
    retainFallbacks := true }

def dualWit : ContifyWitness := ⟨[dualCalleeCr, dualCallerCr]⟩

#eval show IO Unit from do
  if contWitCount (analyzeContify cmDualSlot) != 2 then
    throw (IO.userError "dual_slot analyzeContify mismatch")

theorem dual_slot_check : dualWit.check cmDualSlot = true := by
  have hMf : regionMemFree cmDualSlot [] dualCalleeCr = true := by
    dsimp only [regionMemFree, ContifyRegion.allPcs]
    have h0 : dualCalleeCr.tree.flatMap GroupTree.allPcs = [0#64] := by
      simp [dualCalleeCr]
    rw [h0]
    exact Eq.refl true
  refine check_two_cont_true cmDualSlot dualCalleeCr dualCallerCr
    [0#64] [8#64, 16#64, 24#64] [0#64, 8#64, 16#64, 24#64]
    (ContCalleeMeta.mk "checked_sub" 0#64 true true)
    (by simp [dualCalleeCr, ContifyRegion.allPcs])
    (by simp [dualCallerCr, ContifyRegion.allPcs])
    (by simp [dualCalleeCr, dualCallerCr, ContifyRegion.allPcs])
    (by dsimp only [ContifyRegion.toCalleeMeta?]; rw [hMf]; rfl) ?_
  t_kernel_rfl

theorem dual_slot_lift_eq :
    checkAndLiftContify cmDualSlot dualWit =
      .ok ([liftContifyRegion cmDualSlot dualCalleeCr, liftContifyRegion cmDualSlot dualCallerCr],
        residualContifyCodeMap cmDualSlot dualWit) := by
  dsimp only [checkAndLiftContify]; rw [dual_slot_check]; rfl

theorem dual_callee_supports_x64 :
    ((liftContifyRegion cmDualSlot dualCalleeCr).earlyOpt).body.supportsSource .x64 =
      true := by t_kernel_rfl

theorem dual_caller_supports_x64 :
    ((liftContifyRegion cmDualSlot dualCallerCr).earlyOpt).body.supportsSource .x64 =
      true := by t_kernel_rfl

theorem dual_caller_mid_wf : ((liftContifyRegion cmDualSlot dualCallerCr).mid .x64).Wf :=
  liftContifyRegion_mid_wf cmDualSlot dualCallerCr .x64 dual_caller_supports_x64

theorem dual_cm_wp_ok (r₀ : Regs) (m : Mem 64)
    (hPriv : PrivFrameOk 1 r₀.sp m) (h1 : r₀.r1 = 10#64) (h2 : r₀.r2 = 3#64) :
    cmDualSlot.wp (fun c _ => c = 7#64 + r₀.r3) 8#64 ⟨r₀, m⟩ := by
  intro Ψ hClosed
  let rCall : Regs := { r₀ with rp := 16#64 }
  let rOk : Regs := { r₀ with rp := 16#64, rv := 7#64 }
  let m' := storeMem m i64 (r₀.sp - 8#64) r₀.r3
  have hSto : storeOk m i64 (r₀.sp - 8#64) := (hPriv (by omega)).2 0 (by omega)
  have h16 : cmDualSlot.lookupAddr 16#64 = some (reifyBlock bOkCont) := by t_kernel_rfl
  have hOk : Ψ 16#64 ⟨rOk, m'⟩ := by
    refine hClosed.applyP h16 bOkCont_wf ?_
    dsimp only [bOkCont, BlockP.wp, BlockB.wp, op2, Op.wp, OpCode.wp, evalOpCode, Arg.val,
      Regs.toRegsV, RegsExpr.eval, vals, lift2, Ty.hasFloat]
    have hLv : loadVal m' i64 (r₀.sp - 8#64) = some r₀.r3 :=
      loadVal_storeMem m i64 (r₀.sp - 8#64) r₀.r3 (by decide)
    exact ⟨r₀.r3, by simpa [m'] using hLv, rfl⟩
  have hSub : Ψ 0#64 ⟨rCall, m'⟩ := by
    refine hClosed.applyP (by t_kernel_rfl : cmDualSlot.lookupAddr 0#64 =
        some (reifyBlock bCheckedSub)) bCheckedSub_wf ?_
    dsimp only [bCheckedSub, BlockP.wp, BlockB.wp, op2, Op.wp, OpCode.wp, evalOpCode, Arg.val,
      Regs.toRegsV, RegsV.keep, RegsExpr.eval, vals, rCall]
    rw [h1, h2]
    have hCmp : liftCmp (fun {n} => CmpOp.ult.evalBits) CmpOp.ult.evalBool i64 10#64
        ((rfl : i64 = i64) ▸ 3#64) = false := by decide
    rw [hCmp]
    refine ⟨(fun h => by cases h), (fun _ => ?_)⟩
    have hDiff : lift2 (fun {n} x1 x2 => x1 - x2) (fun x1 x2 => x1 ^^ x2) i64 10#64 3#64 =
        7#64 := by decide
    have hFl : i64.hasFloat = false := rfl
    simp only [hFl, Bool.false_eq_true, ↓reduceIte]
    rw [hDiff]
    have hRegEq : ({ r₀ with rp := 16#64, rv := 7#64, r1 := 10#64, r2 := 3#64 } : Regs) = rOk := by
      cases r₀; simp at h1 h2; subst h1 h2; rfl
    rw [hRegEq]; exact hOk
  refine hClosed.applyP (by t_kernel_rfl : cmDualSlot.lookupAddr 8#64 =
      some (reifyBlock bDualSlotCaller)) bDualSlotCaller_wf ?_
  dsimp only [bDualSlotCaller, BlockP.wp, BlockB.wp, op2, Op.wp, OpCode.wp, evalOpCode, Arg.val,
    CodeMap.symEnv, Regs.toRegsV, RegsV.keep, RegsExpr.eval, vals, lift2, Ty.hasFloat]
  exact ⟨hSto, 16#64, by t_kernel_rfl, 0#64, by t_kernel_rfl, hSub⟩

theorem dual_caller_mid_spec (r₀ : Regs) (m : Mem 64)
    (hPriv : PrivFrameOk 1 r₀.sp m) (h1 : r₀.r1 = 10#64) (h2 : r₀.r2 = 3#64) :
    Func.spec (legalEnv .x64 (witContifyEnv cmDualSlot dualWit))
      ((liftContifyRegion cmDualSlot dualCallerCr).mid .x64).body
      (encodeTup .x64 regSig r₀.toRegsV.toTup) m
      (legalPost .x64 (regionRetPost .retEnvelope
        (cmDualSlot.wp (fun c _ => c = 7#64 + r₀.r3)) r₀.rp))
      (legalXPost .x64 (haltSpec (7#64 + r₀.r3))) :=
  checkAndLiftContify_cm_wp_to_mid cmDualSlot dualWit (fun c _ => c = 7#64 + r₀.r3)
    (haltSpec (7#64 + r₀.r3)) .x64 dual_slot_lift_eq (fun _ _ hc => hc) (by simp [dualWit])
    dual_caller_supports_x64 r₀ m hPriv (dual_cm_wp_ok r₀ m hPriv h1 h2)

/-! ## 3. Private Stack-Slot Promotion (`nSlots = 2`, 0 Mem Ops Inside Loop Body) -> `Fn.mid` -/

def bPrivHdr : BlockP := fun _ r =>
  .letOp2 (.cmp .ult i64) (.imm 0#64) (.var r.r1) fun c =>
  .jnz (.var c) (.ijmp (.imm 8#64) r.keep) (.ijmp (.imm 16#64) r.keep)

theorem bPrivHdr_wf : bPrivHdr.Wf := by
  intro V₁ V₂ r₁ r₂
  refine .let_ (.mk _ (.cons (.imm _) (.cons (.var (by simp [Tup.zip, RegsV.toTup])) .nil)))
    fun _ _ => .jnz (.var (by simp [Tup.zip])) ?_ ?_
  · exact .ijmp (.imm _)
      ⟨.var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
       .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
       .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup])⟩
  · exact .ijmp (.imm _)
      ⟨.var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
       .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
       .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup])⟩

def bPrivExit : BlockP := fun _ r =>
  .letOp2 (.sub i64) (.var r.sp) (.imm 8#64) fun a0 =>
  .load i64 (.var a0) fun v0 =>
  .halt (.var v0)

theorem bPrivExit_wf : bPrivExit.Wf := by
  intro V₁ V₂ r₁ r₂
  refine .let_ (.mk _ (.cons (.var (by simp [Tup.zip, RegsV.toTup]))
      (.cons (.imm _) .nil))) fun _ _ => ?_
  refine .load i64 (.var (by simp [Tup.zip])) fun _ _ => .halt (.var (by simp [Tup.zip]))

def cmPrivLoop : CodeMap :=
  [ mkEntry "priv_hdr" 0#64 bPrivHdr,
    mkEntry "priv_body" 8#64 (fun _ r =>
      .letOp2 (.sub i64) (.var r.sp) (.imm 8#64) fun a0 =>
      .load i64 (.var a0) fun s0 =>
      .letOp2 (.sub i64) (.var r.sp) (.imm 16#64) fun a1 =>
      .load i64 (.var a1) fun s1 =>
      .letOp2 (.add i64) (.var s0) (.var s1) fun sum =>
      .store (t := i64) (.var sum) (.var a0)
      (.letOp2 (.sub i64) (.var r.r1) (.imm 1#64) fun r1' =>
       .ijmp (.imm 0#64) { r.keep with r1 := .var r1' })),
    mkEntry "priv_exit" 16#64 bPrivExit ]

def privLoopCr : ContifyRegion :=
  { name := "priv_hdr_reg"
    entryPc := 0#64
    abi := .retEnvelope
    privFrame := ⟨2, false⟩
    tree := [.loop 0#64 [.leaf 0#64, .leaf 8#64], .leaf 16#64]
    edges :=
      [ ⟨0#64, [true], .direct 8#64⟩,
        ⟨0#64, [false], .direct 16#64⟩,
        ⟨8#64, [], .direct 0#64⟩ ]
    retainFallbacks := true }

def privLoopWit : ContifyWitness := ⟨[privLoopCr]⟩

#eval show IO Unit from do
  match analyzeContify cmPrivLoop with
  | some w =>
      match w.regions with
      | [cr] =>
          if cr.privFrame != ⟨2, false⟩ then
            throw (IO.userError "privLoop analyzeContify privFrame mismatch")
      | _ => throw (IO.userError "privLoop analyzeContify count mismatch")
  | none => throw (IO.userError "privLoop analyzeContify returned none")
  if fnGroupBodyHasMem cmPrivLoop privLoopCr 0#64 ||
     fnGroupBodyHasMem cmPrivLoop privLoopCr 8#64 then
    throw (IO.userError "privLoop loop blocks unexpectedly retained memory ops")

theorem privLoop_check : privLoopWit.check cmPrivLoop = true := by
  refine check_one_cont_eq cmPrivLoop privLoopCr [0#64, 8#64, 16#64]
    (by simp [privLoopCr, ContifyRegion.allPcs]) true ?_
  t_kernel_rfl

theorem privLoop_lift_eq :
    checkAndLiftContify cmPrivLoop privLoopWit =
      .ok ([liftContifyRegion cmPrivLoop privLoopCr],
        residualContifyCodeMap cmPrivLoop privLoopWit) := by
  dsimp only [checkAndLiftContify]; rw [privLoop_check]; rfl

theorem privLoop_supports_scalar64 :
    ((liftContifyRegion cmPrivLoop privLoopCr).earlyOpt).body.supportsSource .scalar64 =
      true := by t_kernel_rfl

theorem privLoop_mid_wf : ((liftContifyRegion cmPrivLoop privLoopCr).mid .scalar64).Wf :=
  liftContifyRegion_mid_wf cmPrivLoop privLoopCr .scalar64 privLoop_supports_scalar64

theorem privLoop_cm_wp_n0 (r₀ : Regs) (m : Mem 64) (v0 : BitVec 64)
    (h0 : r₀.r1 = 0#64) (hLd : loadVal m i64 (r₀.sp - 8#64) = some v0) :
    cmPrivLoop.wp (fun c _ => c = v0) 0#64 ⟨r₀, m⟩ := by
  intro Ψ hClosed
  have h16 : cmPrivLoop.lookupAddr 16#64 = some (reifyBlock bPrivExit) := by t_kernel_rfl
  have hExit : Ψ 16#64 ⟨r₀, m⟩ := by
    refine hClosed.applyP h16 bPrivExit_wf ?_
    dsimp only [bPrivExit, BlockP.wp, BlockB.wp, op2, Op.wp, OpCode.wp, evalOpCode, Arg.val,
      Regs.toRegsV, RegsExpr.eval, vals]
    have hFl : i64.hasFloat = false := rfl
    simp only [hFl, Bool.false_eq_true, ↓reduceIte, lift2]
    exact ⟨v0, hLd, rfl⟩
  refine hClosed.applyP (by t_kernel_rfl : cmPrivLoop.lookupAddr 0#64 =
      some (reifyBlock bPrivHdr)) bPrivHdr_wf ?_
  dsimp only [bPrivHdr, BlockP.wp, BlockB.wp, op2, Op.wp, OpCode.wp, evalOpCode, Arg.val,
    Regs.toRegsV, RegsV.keep, RegsExpr.eval, vals]
  rw [h0]
  refine ⟨fun hT => ?_, fun _ => ?_⟩
  · have hF : liftCmp (fun {n} => CmpOp.ult.evalBits) CmpOp.ult.evalBool i64 0#64
        ((rfl : i64 = i64) ▸ 0#64) = false := by decide
    rw [hF] at hT; cases hT
  · have hReg : ({ r₀ with r1 := 0#64 } : Regs) = r₀ := by
      cases r₀; simp at h0; subst h0; rfl
    rw [hReg]; exact hExit

theorem privLoop_mid_spec (r₀ : Regs) (m : Mem 64) (v0 : BitVec 64)
    (hPriv : PrivFrameOk 2 r₀.sp m) (h0 : r₀.r1 = 0#64)
    (hLd : loadVal m i64 (r₀.sp - 8#64) = some v0) :
    Func.spec (legalEnv .scalar64 (witContifyEnv cmPrivLoop privLoopWit))
      ((liftContifyRegion cmPrivLoop privLoopCr).mid .scalar64).body
      (encodeTup .scalar64 regSig r₀.toRegsV.toTup) m
      (legalPost .scalar64 (regionRetPost .retEnvelope
        (cmPrivLoop.wp (fun c _ => c = v0)) r₀.rp))
      (legalXPost .scalar64 (haltSpec v0)) :=
  checkAndLiftContify_cm_wp_to_mid cmPrivLoop privLoopWit (fun c _ => c = v0)
    (haltSpec v0) .scalar64 privLoop_lift_eq (fun _ _ hc => hc) (by simp [privLoopWit])
    privLoop_supports_scalar64 r₀ m hPriv (privLoop_cm_wp_n0 r₀ m v0 h0 hLd)

/-! ## 4. Negative Escaped-Pointer Rejection & Dynamic Alias-Guard Hybrid Soundness -/

def cmAlias : CodeMap :=
  [ mkEntry "alias_entry" 0#64 (fun _ r =>
      .letOp2 (.sub i64) (.var r.sp) (.imm 8#64) fun a0 =>
      .store (t := i64) (.imm 42#64) (.var a0)
      (.load i64 (.var r.r1) fun _ =>
       .ijmp (.var r.r2) r.keep)),
    mkEntry "fast_exit" 8#64 (fun _ r => .halt (.var r.r3)),
    mkEntry "cold_fallback" 40#64 (fun _ r => .halt (.var r.r3)) ]

def aliasStaticCr : ContifyRegion :=
  { name := "alias_reg"
    entryPc := 0#64
    abi := .retEnvelope
    privFrame := ⟨1, false⟩
    tree := [.leaf 0#64, .leaf 8#64]
    edges := [⟨0#64, [], .guarded [8#64]⟩]
    retainFallbacks := false }

def aliasDynCr : ContifyRegion :=
  { aliasStaticCr with privFrame := ⟨1, true⟩ }

def aliasStaticWit : ContifyWitness := ⟨[aliasStaticCr]⟩
def aliasDynWit : ContifyWitness := ⟨[aliasDynCr]⟩

/-- (4a) Escaped/unknown pointer `r.r1` is statically rejected when `dynAliasGuard = false`. -/
theorem alias_static_rejected : aliasStaticWit.check cmAlias = false := by
  refine check_one_cont_eq cmAlias aliasStaticCr [0#64, 8#64]
    (by simp [aliasStaticCr, ContifyRegion.allPcs]) false ?_
  t_kernel_rfl

theorem alias_static_lift_err :
    checkAndLiftContify cmAlias aliasStaticWit =
      .error "CfgContify: witness check failed" := by
  dsimp only [checkAndLiftContify]; rw [alias_static_rejected]; rfl

/-- (4b) Same escaped pointer with `dynAliasGuard = true` emits runtime disjointness guard +
`flushFrame` + unpromoted tail, passing verification and `hybrid_sound`. -/
theorem alias_dyn_check : aliasDynWit.check cmAlias = true := by
  refine check_one_cont_eq cmAlias aliasDynCr [0#64, 8#64]
    (by simp [aliasDynCr, aliasStaticCr, ContifyRegion.allPcs]) true ?_
  t_kernel_rfl

theorem alias_dyn_res_eq :
    residualContifyCodeMap cmAlias aliasDynWit =
      [mkEntry "cold_fallback" 40#64 (fun _ r => .halt (.var r.r3))] := by
  have h1 : aliasDynCr.allPcs = [0#64, 8#64] := by
    simp [ContifyRegion.allPcs, aliasDynCr, aliasStaticCr]
  have h2 : List.flatMap ContifyRegion.allPcs
      (List.filter (fun r => !r.retainFallbacks) aliasDynWit.regions) = [0#64, 8#64] := by
    simp [aliasDynWit, aliasDynCr, aliasStaticCr, ContifyRegion.allPcs]
  dsimp only [residualContifyCodeMap]; rw [h2]
  simp [aliasDynWit, aliasDynCr, aliasStaticCr, cmAlias, mkEntry]

theorem alias_dyn_lift_eq :
    checkAndLiftContify cmAlias aliasDynWit =
      .ok ([liftContifyRegion cmAlias aliasDynCr],
        [mkEntry "cold_fallback" 40#64 (fun _ r => .halt (.var r.r3))]) := by
  dsimp only [checkAndLiftContify]; rw [alias_dyn_check, alias_dyn_res_eq]; rfl

theorem alias_dyn_supports_x64 :
    ((liftContifyRegion cmAlias aliasDynCr).earlyOpt).body.supportsSource .x64 =
      true := by t_kernel_rfl

theorem alias_dyn_mid_wf : ((liftContifyRegion cmAlias aliasDynCr).mid .x64).Wf :=
  liftContifyRegion_mid_wf cmAlias aliasDynCr .x64 alias_dyn_supports_x64

def psiColdAt40 : CodeSpec := fun pc st => pc = 40#64 → st.regs.r3 = 7#64
def haltR3Eq7 : HaltPost := fun c _ => c = 7#64

private theorem alias_entry_privOk {m : Mem 64} {r : Regs}
    {Ψ : BitVec 64 × State → Prop}
    (hStep : ContifyRegionStep cmAlias aliasDynWit psiColdAt40 haltR3Eq7 Ψ (0#64, ⟨r, m⟩)) :
    PrivFrameOk 1 r.sp m := fun _ => by
  rcases hStep with ⟨b, hlu, hbp⟩
  have h0 : cmAlias.lookupAddr 0#64 = some (reifyBlock fun _ r =>
      .letOp2 (.sub i64) (.var r.sp) (.imm 8#64) fun a0 =>
      .store (t := i64) (.imm 42#64) (.var a0)
      (.load i64 (.var r.r1) fun _ => .ijmp (.var r.r2) r.keep)) := by t_kernel_rfl
  rw [h0] at hlu; cases hlu
  dsimp only [BlockFlat.wp, denoteArgs, denoteArg, lookupV, listGet?, Op.wp, OpCode.wp,
    evalOpCode, vals, pushTup, Arg.val, lift2, Ty.hasFloat, Regs.toRegsV, pushRegsV,
    RegsV.toTup] at hbp
  refine ⟨by omega, fun k hk => ?_⟩
  have hk0 : k = 0 := by omega
  subst hk0
  dsimp only [slotAddr, BitVec.ofNat] at *
  exact hbp.1

theorem alias_dyn_hybrid_sound :
    SpecsClosed cmAlias cmAlias.symEnv (PsiContHyb cmAlias aliasDynWit psiColdAt40 haltR3Eq7)
      haltR3Eq7 ∧
      ∀ pc₀ st₀, cmAlias.wp haltR3Eq7 pc₀ st₀ → psiColdAt40 pc₀ st₀ := by
  refine checkAndLiftContify_hybrid_sound cmAlias aliasDynWit psiColdAt40 haltR3Eq7
    (haltSpec 7#64) .x64 alias_dyn_lift_eq (fun _ _ hc => hc)
    (by simp [aliasDynWit, alias_dyn_supports_x64]) ?_ ?_ ?_ ?_
  · intro cr hCr r₀ m₀ hReg
    simp only [aliasDynWit, List.mem_singleton] at hCr
    subst hCr
    have hUnfold := Xcap.Lfp.lfp_post
      (contifyRegionStep_mono cmAlias aliasDynWit psiColdAt40 haltR3Eq7) (0#64, ⟨r₀, m₀⟩) hReg
    exact alias_entry_privOk hUnfold
  · intro pc b hlu st hbp
    dsimp only [CodeMap.lookupAddr] at hlu
    split at hlu
    · cases hlu
      intro _
      dsimp only [BlockFlat.wp, denoteArg, pushRegsV, Regs.toRegsV, RegsV.toTup, pushTup] at hbp
      exact hbp
    · cases hlu
  · intro cr hCr _ _ _
    simp only [aliasDynWit, List.mem_singleton] at hCr
    subst hCr
    intro h40; cases h40
  · intro cr hCr _ pc hPc hNe _ _
    simp only [aliasDynWit, List.mem_singleton] at hCr
    subst hCr
    simp [aliasDynCr, aliasStaticCr, ContifyRegion.allPcs] at hPc
    rcases hPc with rfl | rfl
    · exact absurd rfl hNe
    · intro h40; cases h40

end LeanQbeTest.T.BedrockCfgStage1Test

#print axioms LeanQbe.T.Unified.checkAndLiftContify_cm_wp_to_mid
#print axioms LeanQbe.T.Unified.checkAndLiftContify_hybrid_sound
#print axioms LeanQbe.T.Unified.contify_psiReg_to_mid_spec
#print axioms LeanQbe.T.Unified.contify_psiReg_to_func_spec
#print axioms LeanQbe.T.Unified.liftContifyRegion_mid_wf
#print axioms LeanQbe.T.Unified.liftContifyRegion_wf
#print axioms LeanQbeTest.T.BedrockCfgStage1Test.nested_main_mid_spec
#print axioms LeanQbeTest.T.BedrockCfgStage1Test.dual_caller_mid_spec
#print axioms LeanQbeTest.T.BedrockCfgStage1Test.privLoop_mid_spec
#print axioms LeanQbeTest.T.BedrockCfgStage1Test.alias_static_lift_err
#print axioms LeanQbeTest.T.BedrockCfgStage1Test.alias_dyn_hybrid_sound
