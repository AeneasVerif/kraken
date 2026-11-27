module

public import LeanQbe.T.Unified.CfgRecoveryProof
public meta import LeanQbe.T.Unified.CfgRecovery
import LeanQbe.T.FlatLemmas
import LeanQbe.T.Unified.CfgRecoveryLemmas

/-!
# End-to-End Tests for `BedrockWord` L0 & Stage-0 `Unified.CfgRecovery`

Exercises:
1. Computed stride jump tables (`unguarded` with `ult` bound & `guarded` variant) -> `Fn.mid`
   (`LegalTarget.x64`, `.aarch64`, `.scalar64`), `liftRegion_mid_wf`, and
   `checkAndLiftWitness_cm_wp_to_mid`.
2. Bourdoncle structured `GroupTree.loop` (`whileM` calling a `retM` helper) -> `Fn.mid`.
3. Dual-return `rp + 8` contification (`RegionAbi.contified true`) -> `Fn.mid`.
4. Flagless `OpCode.select` + 3-bit tag/untag (`(codeAddr s ||| 1) &&& ~~~7`) +
   speculative `EdgeKind.guarded` bailout + nontrivial `checkAndLiftWitness_hybrid_sound`.
5. `#print axioms` checks confirming all top-level soundness & pipeline theorems depend ONLY on
   `⊆ [propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.BedrockCfgRecoveryTest

open LeanQbe.T
open LeanQbe.T.BedrockWord
open LeanQbe.T.Unified

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

def witCount (o : Option CfgWitness) : Nat :=
  match o with
  | some w => w.regions.length
  | none => 0

def liftCount (cm : CodeMap) (wit : CfgWitness) : Nat :=
  match checkAndLiftWitness cm wit with
  | .ok (fns, _) => fns.length
  | .error _ => 0

def resAddrs (cm : CodeMap) (wit : CfgWitness) : List (BitVec 64) :=
  match checkAndLiftWitness cm wit with
  | .ok (_, wRes) => wRes.map (·.addr)
  | .error _ => []

/-! ## 1. Computed Stride Jump Tables (Unguarded & Guarded) -> Real `Fn.mid` -/

def bDispatch : BlockP := fun _ r =>
  .letOp2 (.cmp .ult i64) (.var r.r1) (.imm 3#64) fun c =>
  .jnz (.var c)
    (.letOp2 (.shl i64) (.var r.r1) (.imm 3#64) fun off =>
     .codeAddr "pad0" fun base =>
     .letOp2 (.add i64) (.var base) (.var off) fun tgt =>
     .ijmp (.var tgt) r.keep)
    (.halt (.imm 99#64))

theorem bDispatch_wf : bDispatch.Wf := by
  intro V₁ V₂ r₁ r₂
  refine .let_ (.mk _ (.cons (.var (by simp [Tup.zip, RegsV.toTup]))
      (.cons (.imm _) .nil))) fun _ _ => ?_
  refine .jnz (.var (by simp [Tup.zip])) ?_ (.halt (.imm _))
  refine .let_ (.mk _ (.cons (.var (by simp [Tup.zip, RegsV.toTup]))
      (.cons (.imm _) .nil))) fun _ _ => ?_
  refine .codeAddr _ fun _ _ => ?_
  refine .let_ (.mk _ (.cons (.var (by simp)) (.cons (.var (by simp [Tup.zip])) .nil)))
    fun _ _ => ?_
  exact .ijmp (.var (by simp [Tup.zip]))
    ⟨.var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
     .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
     .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup])⟩

def cmStrideUnguarded : CodeMap :=
  [ mkEntry "dispatch" 0#64 bDispatch,
    mkEntry "pad0" 8#64 (fun _ _ => .halt (.imm 10#64)),
    mkEntry "pad1" 16#64 (fun _ _ => .halt (.imm 20#64)),
    mkEntry "pad2" 24#64 (fun _ _ => .halt (.imm 30#64)) ]

def strideUnRw : RegionWitness :=
  { name := "dispatch_reg"
    entryPc := 0#64
    abi := .retEnvelope
    tree := [.leaf 0#64, .leaf 8#64, .leaf 16#64, .leaf 24#64]
    edges := [⟨0#64, [true], .strideTable 8#64 [8#64, 16#64, 24#64] false⟩]
    retainFallbacks := true }

def strideUnWit : CfgWitness := ⟨[strideUnRw]⟩

#eval show IO Unit from do
  if witCount (analyzeCfg cmStrideUnguarded) != 1 then
    throw (IO.userError "stride_un analyzeCfg mismatch")

theorem stride_un_check : strideUnWit.check cmStrideUnguarded = true := by
  dsimp only [strideUnWit, CfgWitness.check, CfgWitness.checkAux, RegionWitness.check,
    RegionWitness.allPcs]
  have h1 : strideUnRw.tree.flatMap GroupTree.allPcs = [0#64, 8#64, 16#64, 24#64] := by
    simp [strideUnRw, GroupTree.allPcs]
  have h2 : List.flatMap RegionWitness.allPcs [strideUnRw] = [0#64, 8#64, 16#64, 24#64] := by
    simp [RegionWitness.allPcs, h1]
  rw [h1, h2]
  exact Eq.refl true

theorem stride_un_lift_eq :
    checkAndLiftWitness cmStrideUnguarded strideUnWit =
      .ok ([liftRegion cmStrideUnguarded strideUnRw],
        residualCodeMap cmStrideUnguarded strideUnWit) := by
  dsimp only [checkAndLiftWitness]
  rw [stride_un_check]
  rfl

theorem stride_un_lift : liftCount cmStrideUnguarded strideUnWit = 1 := by
  dsimp only [liftCount]
  rw [stride_un_lift_eq]
  rfl

theorem stride_un_supports_x64 :
    ((liftRegion cmStrideUnguarded strideUnRw).earlyOpt).body.supportsSource .x64 = true := by
  t_kernel_rfl

theorem stride_un_supports_arm64 :
    ((liftRegion cmStrideUnguarded strideUnRw).earlyOpt).body.supportsSource .aarch64 =
      true := by
  t_kernel_rfl

theorem stride_un_supports_scalar64 :
    ((liftRegion cmStrideUnguarded strideUnRw).earlyOpt).body.supportsSource .scalar64 =
      true := by
  t_kernel_rfl

theorem stride_un_mid_wf_x64 :
    ((liftRegion cmStrideUnguarded strideUnRw).mid .x64).Wf :=
  liftRegion_mid_wf cmStrideUnguarded strideUnRw .x64 stride_un_supports_x64

theorem stride_un_mid_wf_arm64 :
    ((liftRegion cmStrideUnguarded strideUnRw).mid .aarch64).Wf :=
  liftRegion_mid_wf cmStrideUnguarded strideUnRw .aarch64 stride_un_supports_arm64

theorem stride_un_cm_wp_idx1 (r₀ : Regs) (m : Mem 64) (h1 : r₀.r1 = 1#64) :
    cmStrideUnguarded.wp (fun c _ => c = 20#64) 0#64 ⟨r₀, m⟩ := by
  intro Ψ hClosed
  have h16 : Ψ 16#64 ⟨r₀, m⟩ :=
    hClosed 16#64 (reifyBlock fun _ _ => .halt (.imm 20#64)) (by t_kernel_rfl) ⟨r₀, m⟩ rfl
  refine hClosed.applyP (by t_kernel_rfl : cmStrideUnguarded.lookupAddr 0#64 =
      some (reifyBlock bDispatch)) bDispatch_wf ?_
  dsimp only [bDispatch, BlockP.wp, BlockB.wp, op2, Op.wp, OpCode.wp, evalOpCode, Arg.val,
    CodeMap.symEnv, Regs.toRegsV, RegsV.keep, RegsExpr.eval, vals]
  rw [h1]
  refine ⟨fun _ => ⟨8#64, by t_kernel_rfl, ?_⟩, fun hF => by revert hF; decide⟩
  have hAdd : (lift2 (fun {n} x1 x2 => x1 + x2) (fun x1 x2 => x1 ^^ x2) i64 8#64
      (lift2 (fun {n} x y => x <<< (y.toNat % n)) (fun x _ => x) i64
        ((rfl : i64 = i64) ▸ 1#64) 3#64)) = 16#64 := by decide
  rw [hAdd]
  have hFl : i64.hasFloat = false := rfl
  simp only [hFl, Bool.false_eq_true, ↓reduceIte]
  have hReg : ({ r₀ with r1 := 1#64 } : Regs) = r₀ := by
    cases r₀; simp at h1; subst h1; rfl
  rw [hReg]
  exact h16

theorem stride_un_mid_spec_x64 (r₀ : Regs) (m : Mem 64) (h1 : r₀.r1 = 1#64) :
    Func.spec (legalEnv .x64 (witEnv cmStrideUnguarded strideUnWit))
      ((liftRegion cmStrideUnguarded strideUnRw).mid .x64).body
      (encodeTup .x64 regSig r₀.toRegsV.toTup) m
      (legalPost .x64 (regionRetPost .retEnvelope
        (cmStrideUnguarded.wp (fun c _ => c = 20#64)) r₀.rp))
      (legalXPost .x64 (haltSpec 20#64)) :=
  checkAndLiftWitness_cm_wp_to_mid cmStrideUnguarded strideUnWit
    (fun c _ => c = 20#64) (haltSpec 20#64) .x64 stride_un_lift_eq
    (fun _ _ hc => hc) (List.mem_cons_self) stride_un_supports_x64 r₀ m
    (stride_un_cm_wp_idx1 r₀ m h1)

def regCheckBool (cm : CodeMap) (callees : List CalleeMeta)
    (rw : RegionWitness) (allPcs : List (BitVec 64)) : Bool :=
  let entries := rw.tree.map GroupTree.entryPc
  let pcs := pushLabelPcs entries []
  let tf := liftRegionTFlat cm rw
  fnNameOk rw.name &&
  (!rw.tree.isEmpty) &&
  (cm.lookupAddr rw.entryPc).isSome &&
  entries.contains rw.entryPc &&
  listNodup allPcs &&
  checkGroupNodes cm rw callees pcs rw.tree &&
  tf.wfCheck regCtx [] &&
  tf.noHlt

private theorem check_two_regions_true (cm : CodeMap) (r₁ r₂ : RegionWitness)
    (a₁ a₂ aTot : List (BitVec 64))
    (ha₁ : r₁.allPcs = a₁) (ha₂ : r₂.allPcs = a₂)
    (hat : ([r₁, r₂].flatMap RegionWitness.allPcs) = aTot)
    (h : (listNodup ([r₁, r₂].map (·.name)) && listNodup aTot &&
      (regCheckBool cm [] r₁ a₁ &&
       (regCheckBool cm (match r₁.toCalleeMeta? with | some c => [c] | none => []) r₂ a₂ &&
        true))) = true) :
    CfgWitness.check cm ⟨[r₁, r₂]⟩ = true := by
  dsimp only [CfgWitness.check, CfgWitness.checkAux, RegionWitness.check, regCheckBool] at h ⊢
  rw [hat, ha₁, ha₂]
  exact h

def cmStrideGuarded : CodeMap :=
  [ mkEntry "gdispatch" 0#64 (fun _ r =>
      .letOp2 (.mul i64) (.var r.r1) (.imm 8#64) fun off =>
      .codeAddr "gpad0" fun base =>
      .letOp2 (.add i64) (.var base) (.var off) fun tgt =>
      .ijmp (.var tgt) r.keep),
    mkEntry "gpad0" 8#64 (fun _ _ => .halt (.imm 11#64)),
    mkEntry "gpad1" 16#64 (fun _ _ => .halt (.imm 22#64)) ]

def strideGuRw : RegionWitness :=
  { name := "gdispatch_reg"
    entryPc := 0#64
    abi := .retEnvelope
    tree := [.leaf 0#64, .leaf 8#64, .leaf 16#64]
    edges := [⟨0#64, [], .strideTable 8#64 [8#64, 16#64] true⟩]
    retainFallbacks := true }

def strideGuWit : CfgWitness := ⟨[strideGuRw]⟩

#eval show IO Unit from do
  if witCount (analyzeCfg cmStrideGuarded) != 1 then
    throw (IO.userError "stride_gu analyzeCfg mismatch")

theorem stride_gu_check : strideGuWit.check cmStrideGuarded = true := by
  dsimp only [strideGuWit, CfgWitness.check, CfgWitness.checkAux, RegionWitness.check,
    RegionWitness.allPcs]
  have h1 : strideGuRw.tree.flatMap GroupTree.allPcs = [0#64, 8#64, 16#64] := by
    simp [strideGuRw, GroupTree.allPcs]
  have h2 : List.flatMap RegionWitness.allPcs [strideGuRw] = [0#64, 8#64, 16#64] := by
    simp [RegionWitness.allPcs, h1]
  rw [h1, h2]
  exact Eq.refl true

theorem stride_gu_lift : liftCount cmStrideGuarded strideGuWit = 1 := by
  dsimp only [liftCount, checkAndLiftWitness]
  rw [stride_gu_check]
  rfl

theorem stride_gu_supports_x64 :
    ((liftRegion cmStrideGuarded strideGuRw).earlyOpt).body.supportsSource .x64 = true := by
  t_kernel_rfl

theorem stride_gu_mid_wf_x64 :
    ((liftRegion cmStrideGuarded strideGuRw).mid .x64).Wf :=
  liftRegion_mid_wf cmStrideGuarded strideGuRw .x64 stride_gu_supports_x64

/-! ## 2. Bourdoncle `GroupTree.loop` (`whileM` calling `retM` Helper) -> `Fn.mid` -/

def loopCallHelperMac : Macro :=
  { size := 1
    emit := fun pfx base _ =>
      [⟨pfx ++ "_call", base, fun _ r =>
        .codeAddr "lp_hdr" fun retPc =>
        .jmpSym "step_ret" { r.keep with rp := .var retPc }⟩] }

def loopBodyMac : Macro :=
  whileM (fun _ r k => .letOp2 (.cmp .ult i64) (.imm 0#64) (.var r.r1) k) loopCallHelperMac

def bLoopHdr : BlockP := fun _ r =>
  .letOp2 (.cmp .ult i64) (.imm 0#64) (.var r.r1) fun b =>
  .jnz (.var b) (.ijmp (.imm 16#64) r.keep) (.ijmp (.imm 24#64) r.keep)

theorem bLoopHdr_wf : bLoopHdr.Wf := by
  intro V₁ V₂ r₁ r₂
  refine .let_ (.mk _ (.cons (.imm _) (.cons (.var (by simp [Tup.zip, RegsV.toTup])) .nil)))
    fun _ _ => ?_
  refine .jnz (.var (by simp [Tup.zip])) ?_ ?_
  · exact .ijmp (.imm _)
      ⟨.var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
       .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
       .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup])⟩
  · exact .ijmp (.imm _)
      ⟨.var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
       .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
       .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup])⟩

def cmLoopWhile : CodeMap :=
  [ mkEntry "step_ret" 0#64 (fun _ r =>
      .letOp2 (.sub i64) (.var r.r1) (.imm 1#64) fun r1' =>
      .letOp2 (.add i64) (.var r.rv) (.imm 1#64) fun rv' =>
      .ijmp (.var r.rp) { r.keep with r1 := .var r1', rv := .var rv' }) ] ++
  compileEntries (loopBodyMac.emit "lp" 8#64 24#64 ++ haltM.emit "done" 24#64 24#64)

def loopHelperRw : RegionWitness :=
  { name := "step_ret"
    entryPc := 0#64
    abi := .contified false
    tree := [.leaf 0#64]
    edges := [⟨0#64, [], .contRet false⟩]
    retainFallbacks := true }

def loopMainRw : RegionWitness :=
  { name := "lp_hdr_reg"
    entryPc := 8#64
    abi := .retEnvelope
    tree := [.loop 8#64 [.leaf 8#64, .leaf 16#64], .leaf 24#64]
    edges := [ ⟨8#64, [true], .direct 16#64⟩,
               ⟨8#64, [false], .direct 24#64⟩,
               ⟨16#64, [], .contCall "step_ret" 0#64 false 8#64 none⟩ ]
    retainFallbacks := true }

def loopWit : CfgWitness := ⟨[loopHelperRw, loopMainRw]⟩

#eval show IO Unit from do
  if witCount (analyzeCfg cmLoopWhile) != 2 then
    throw (IO.userError "loop_while analyzeCfg mismatch")

theorem loop_while_check : loopWit.check cmLoopWhile = true := by
  refine check_two_regions_true cmLoopWhile loopHelperRw loopMainRw
    [0#64] [8#64, 16#64, 24#64] [0#64, 8#64, 16#64, 24#64]
    (by simp [loopHelperRw, RegionWitness.allPcs, GroupTree.allPcs])
    (by simp [loopMainRw, RegionWitness.allPcs, GroupTree.allPcs])
    (by simp [RegionWitness.allPcs, loopHelperRw, loopMainRw, GroupTree.allPcs]) ?_
  t_kernel_rfl

theorem loop_while_lift_eq :
    checkAndLiftWitness cmLoopWhile loopWit =
      .ok ([liftRegion cmLoopWhile loopHelperRw, liftRegion cmLoopWhile loopMainRw],
        residualCodeMap cmLoopWhile loopWit) := by
  dsimp only [checkAndLiftWitness]
  rw [loop_while_check]
  rfl

theorem loop_while_lift : liftCount cmLoopWhile loopWit = 2 := by
  dsimp only [liftCount]
  rw [loop_while_lift_eq]
  rfl

theorem loop_helper_supports_arm64 :
    ((liftRegion cmLoopWhile loopHelperRw).earlyOpt).body.supportsSource .aarch64 =
      true := by
  t_kernel_rfl

theorem loop_main_supports_arm64 :
    ((liftRegion cmLoopWhile loopMainRw).earlyOpt).body.supportsSource .aarch64 = true := by
  t_kernel_rfl

theorem loop_helper_mid_wf : ((liftRegion cmLoopWhile loopHelperRw).mid .aarch64).Wf :=
  liftRegion_mid_wf cmLoopWhile loopHelperRw .aarch64 loop_helper_supports_arm64

theorem loop_main_mid_wf : ((liftRegion cmLoopWhile loopMainRw).mid .aarch64).Wf :=
  liftRegion_mid_wf cmLoopWhile loopMainRw .aarch64 loop_main_supports_arm64

theorem loop_cm_wp_n0 (r₀ : Regs) (m : Mem 64) (h0 : r₀.r1 = 0#64) :
    cmLoopWhile.wp (fun c _ => c = r₀.rv) 8#64 ⟨r₀, m⟩ := by
  intro Ψ hClosed
  have h24 : cmLoopWhile.lookupAddr 24#64 = some (reifyBlock fun _ r => .halt (.var r.rv)) := by
    t_kernel_rfl
  have hDone : Ψ 24#64 ⟨r₀, m⟩ := hClosed 24#64 _ h24 ⟨r₀, m⟩ rfl
  refine hClosed.applyP (by t_kernel_rfl : cmLoopWhile.lookupAddr 8#64 =
      some (reifyBlock bLoopHdr)) bLoopHdr_wf ?_
  dsimp only [bLoopHdr, BlockP.wp, BlockB.wp, op2, Op.wp, OpCode.wp, evalOpCode, Arg.val,
    Regs.toRegsV, RegsV.keep, RegsExpr.eval, vals]
  rw [h0]
  refine ⟨fun hT => ?_, fun _ => ?_⟩
  · have hF : liftCmp (fun {n} => CmpOp.ult.evalBits) CmpOp.ult.evalBool i64 0#64
        ((rfl : i64 = i64) ▸ 0#64) = false := by decide
    rw [hF] at hT
    cases hT
  · have hReg : ({ r₀ with r1 := 0#64 } : Regs) = r₀ := by
      cases r₀; simp at h0; subst h0; rfl
    rw [hReg]
    exact hDone

theorem loop_main_mid_spec (r₀ : Regs) (m : Mem 64) (h0 : r₀.r1 = 0#64) :
    Func.spec (legalEnv .aarch64 (witEnv cmLoopWhile loopWit))
      ((liftRegion cmLoopWhile loopMainRw).mid .aarch64).body
      (encodeTup .aarch64 regSig r₀.toRegsV.toTup) m
      (legalPost .aarch64 (regionRetPost .retEnvelope
        (cmLoopWhile.wp (fun c _ => c = r₀.rv)) r₀.rp))
      (legalXPost .aarch64 (haltSpec r₀.rv)) :=
  checkAndLiftWitness_cm_wp_to_mid cmLoopWhile loopWit
    (fun c _ => c = r₀.rv) (haltSpec r₀.rv) .aarch64 loop_while_lift_eq
    (fun _ _ hc => hc) (by simp [loopWit]) loop_main_supports_arm64 r₀ m
    (loop_cm_wp_n0 r₀ m h0)

/-! ## 3. Dual-Return `rp + 8` Contification -> `Fn.mid` -/

def bProbe : BlockP := fun _ r =>
  .letOp2 (.cmp .eq i64) (.var r.r1) (.imm 0#64) fun c =>
  .jnz (.var c)
    (.ijmp (.var r.rp) { r.keep with rv := .imm 10#64 })
    (.letOp2 (.add i64) (.var r.rp) (.imm 8#64) fun rp8 =>
     .ijmp (.var rp8) { r.keep with rv := .imm 20#64 })

theorem bProbe_wf : bProbe.Wf := by
  intro V₁ V₂ r₁ r₂
  refine .let_ (.mk _ (.cons (.var (by simp [Tup.zip, RegsV.toTup]))
      (.cons (.imm _) .nil))) fun _ _ => ?_
  refine .jnz (.var (by simp [Tup.zip])) ?_ ?_
  · exact .ijmp (.var (by simp [Tup.zip, RegsV.toTup]))
      ⟨.var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
       .imm _, .var (by simp [Tup.zip, RegsV.toTup]),
       .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup])⟩
  · refine .let_ (.mk _ (.cons (.var (by simp [Tup.zip, RegsV.toTup]))
        (.cons (.imm _) .nil))) fun _ _ => ?_
    exact .ijmp (.var (by simp [Tup.zip]))
      ⟨.var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
       .imm _, .var (by simp [Tup.zip, RegsV.toTup]),
       .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup])⟩

def bCaller : BlockP := fun _ r =>
  .codeAddr "ok_cont" fun k0 =>
  .jmpSym "probe" { r.keep with rp := .var k0 }

theorem bCaller_wf : bCaller.Wf := by
  intro V₁ V₂ r₁ r₂
  refine .codeAddr _ fun _ _ => .codeAddr _ fun _ _ => .ijmp (.var (by simp))
    ⟨.var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
     .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup]),
     .var (by simp [Tup.zip, RegsV.toTup]), .var (by simp [Tup.zip, RegsV.toTup])⟩

def cmDualRet : CodeMap :=
  [ mkEntry "probe" 0#64 bProbe,
    mkEntry "caller" 8#64 bCaller,
    mkEntry "ok_cont" 16#64 (fun _ r => .halt (.var r.rv)),
    mkEntry "err_cont" 24#64 (fun _ _ => .halt (.imm 999#64)) ]

def dualCalleeRw : RegionWitness :=
  { name := "probe"
    entryPc := 0#64
    abi := .contified true
    tree := [.leaf 0#64]
    edges := [⟨0#64, [true], .contRet false⟩, ⟨0#64, [false], .contRet true⟩]
    retainFallbacks := true }

def dualCallerRw : RegionWitness :=
  { name := "caller_reg"
    entryPc := 8#64
    abi := .retEnvelope
    tree := [.leaf 8#64, .leaf 16#64, .leaf 24#64]
    edges := [⟨8#64, [], .contCall "probe" 0#64 true 16#64 (some 24#64)⟩]
    retainFallbacks := true }

def dualWit : CfgWitness := ⟨[dualCalleeRw, dualCallerRw]⟩

#eval show IO Unit from do
  if witCount (analyzeCfg cmDualRet) != 2 then
    throw (IO.userError "dual_ret analyzeCfg mismatch")

theorem dual_ret_check : dualWit.check cmDualRet = true := by
  refine check_two_regions_true cmDualRet dualCalleeRw dualCallerRw
    [0#64] [8#64, 16#64, 24#64] [0#64, 8#64, 16#64, 24#64]
    (by simp [dualCalleeRw, RegionWitness.allPcs, GroupTree.allPcs])
    (by simp [dualCallerRw, RegionWitness.allPcs, GroupTree.allPcs])
    (by simp [RegionWitness.allPcs, dualCalleeRw, dualCallerRw, GroupTree.allPcs]) ?_
  t_kernel_rfl

theorem dual_ret_lift_eq :
    checkAndLiftWitness cmDualRet dualWit =
      .ok ([liftRegion cmDualRet dualCalleeRw, liftRegion cmDualRet dualCallerRw],
        residualCodeMap cmDualRet dualWit) := by
  dsimp only [checkAndLiftWitness]
  rw [dual_ret_check]
  rfl

theorem dual_ret_lift : liftCount cmDualRet dualWit = 2 := by
  dsimp only [liftCount]
  rw [dual_ret_lift_eq]
  rfl

theorem dual_callee_supports_scalar64 :
    ((liftRegion cmDualRet dualCalleeRw).earlyOpt).body.supportsSource .scalar64 =
      true := by
  t_kernel_rfl

theorem dual_caller_supports_scalar64 :
    ((liftRegion cmDualRet dualCallerRw).earlyOpt).body.supportsSource .scalar64 =
      true := by
  t_kernel_rfl

theorem dual_callee_mid_wf : ((liftRegion cmDualRet dualCalleeRw).mid .scalar64).Wf :=
  liftRegion_mid_wf cmDualRet dualCalleeRw .scalar64 dual_callee_supports_scalar64

theorem dual_caller_mid_wf : ((liftRegion cmDualRet dualCallerRw).mid .scalar64).Wf :=
  liftRegion_mid_wf cmDualRet dualCallerRw .scalar64 dual_caller_supports_scalar64

theorem dual_cm_wp (r₀ : Regs) (m : Mem 64) :
    cmDualRet.wp (fun c _ => c = 10#64 ∨ c = 999#64) 8#64 ⟨r₀, m⟩ := by
  intro Ψ hClosed
  let rOk : Regs := { r₀ with rp := 16#64, rv := 10#64 }
  let rErr : Regs := { r₀ with rp := 16#64, rv := 20#64 }
  have h16 : cmDualRet.lookupAddr 16#64 = some (reifyBlock fun _ r => .halt (.var r.rv)) := by
    t_kernel_rfl
  have h24 : cmDualRet.lookupAddr 24#64 = some (reifyBlock fun _ _ => .halt (.imm 999#64)) := by
    t_kernel_rfl
  have hOk : Ψ 16#64 ⟨rOk, m⟩ := hClosed 16#64 _ h16 ⟨rOk, m⟩ (Or.inl rfl)
  have hErr : Ψ 24#64 ⟨rErr, m⟩ := hClosed 24#64 _ h24 ⟨rErr, m⟩ (Or.inr rfl)
  have hProbe : Ψ 0#64 ⟨{ r₀ with rp := 16#64 }, m⟩ := by
    refine hClosed.applyP (by t_kernel_rfl : cmDualRet.lookupAddr 0#64 = some (reifyBlock bProbe))
      bProbe_wf ?_
    dsimp only [bProbe, BlockP.wp, BlockB.wp, op2, Op.wp, OpCode.wp, evalOpCode, Arg.val,
      Regs.toRegsV, RegsV.keep, RegsExpr.eval, vals]
    refine ⟨fun _ => hOk, fun _ => ?_⟩
    have hAdd : lift2 (fun {n} x1 x2 => x1 + x2) (fun x1 x2 => x1 ^^ x2) i64 16#64 8#64 =
        24#64 := by decide
    rw [hAdd]
    exact hErr
  refine hClosed.applyP (by t_kernel_rfl : cmDualRet.lookupAddr 8#64 = some (reifyBlock bCaller))
    bCaller_wf ?_
  dsimp only [bCaller, BlockP.wp, BlockB.wp, CodeMap.symEnv, Arg.val,
    Regs.toRegsV, RegsV.keep, RegsExpr.eval]
  exact ⟨16#64, by t_kernel_rfl, 0#64, by t_kernel_rfl, hProbe⟩

theorem dual_caller_mid_spec (r₀ : Regs) (m : Mem 64) :
    Func.spec (legalEnv .scalar64 (witEnv cmDualRet dualWit))
      ((liftRegion cmDualRet dualCallerRw).mid .scalar64).body
      (encodeTup .scalar64 regSig r₀.toRegsV.toTup) m
      (legalPost .scalar64 (regionRetPost .retEnvelope
        (cmDualRet.wp (fun c _ => c = 10#64 ∨ c = 999#64)) r₀.rp))
      (legalXPost .scalar64 (haltPredX fun c => c = 10#64 ∨ c = 999#64)) :=
  checkAndLiftWitness_cm_wp_to_mid cmDualRet dualWit
    (fun c _ => c = 10#64 ∨ c = 999#64) (haltPredX fun c => c = 10#64 ∨ c = 999#64) .scalar64
    dual_ret_lift_eq (fun _ _ hc => hc) (by simp [dualWit]) dual_caller_supports_scalar64
    r₀ m (dual_cm_wp r₀ m)

/-! ## 4. Flagless `select`, 3-bit Tag/Untag, Speculative `guarded` Bailout & Hybrid Soundness -/

def cmHybrid : CodeMap :=
  [ mkEntry "entry" 0#64 (fun _ r =>
      .letOp2 (.cmp .eq i64) (.var r.r1) (.imm 0#64) fun c =>
      .codeAddr "hot_a" fun pa =>
      .codeAddr "hot_b" fun pb =>
      .letOp3 (.select i64) (.var c) (.var pa) (.var pb) fun tgt =>
      .ijmp (.var tgt) r.keep),
    mkEntry "hot_a" 8#64 (fun _ r =>
      .codeAddr "join_guard" fun pj =>
      .letOp2 (.or i64) (.var pj) (.imm 1#64) fun tagged =>
      .letOp2 (.and i64) (.var tagged) (.imm (~~~7#64)) fun untagged =>
      .ijmp (.var untagged) r.keep),
    mkEntry "hot_b" 16#64 (fun _ r => .halt (.var r.r3)),
    mkEntry "join_guard" 24#64 (fun _ r => .ijmp (.var r.r2) r.keep),
    mkEntry "fast_exit" 32#64 (fun _ r => .halt (.var r.r3)),
    mkEntry "cold_fallback" 40#64 (fun _ r => .halt (.var r.r3)) ]

def hybridRw : RegionWitness :=
  { name := "spec_main"
    entryPc := 0#64
    abi := .retEnvelope
    tree := [.leaf 0#64, .leaf 8#64, .leaf 16#64, .leaf 24#64, .leaf 32#64]
    edges := [ ⟨0#64, [], .select 8#64 16#64⟩,
               ⟨8#64, [], .direct 24#64⟩,
               ⟨24#64, [], .guarded [32#64]⟩ ]
    retainFallbacks := false }

def hybridWit : CfgWitness := ⟨[hybridRw]⟩

theorem hybrid_check : hybridWit.check cmHybrid = true := by
  dsimp only [hybridWit, CfgWitness.check, CfgWitness.checkAux, RegionWitness.check,
    RegionWitness.allPcs]
  have h1 : hybridRw.tree.flatMap GroupTree.allPcs = [0#64, 8#64, 16#64, 24#64, 32#64] := by
    simp [hybridRw, GroupTree.allPcs]
  have h2 : List.flatMap RegionWitness.allPcs [hybridRw] = [0#64, 8#64, 16#64, 24#64, 32#64] := by
    simp [RegionWitness.allPcs, h1]
  rw [h1, h2]
  exact Eq.refl true

theorem hybrid_res_eq :
    residualCodeMap cmHybrid hybridWit =
      [mkEntry "cold_fallback" 40#64 (fun _ r => .halt (.var r.r3))] := by
  have h1 : hybridRw.allPcs = [0#64, 8#64, 16#64, 24#64, 32#64] := by
    simp [RegionWitness.allPcs, hybridRw, GroupTree.allPcs]
  have h2 : List.flatMap RegionWitness.allPcs
      (List.filter (fun r => !r.retainFallbacks) hybridWit.regions) =
      [0#64, 8#64, 16#64, 24#64, 32#64] := by
    simp [hybridWit, hybridRw, RegionWitness.allPcs, GroupTree.allPcs]
  dsimp only [residualCodeMap]
  rw [h2]
  simp [hybridWit, hybridRw, cmHybrid, mkEntry]

theorem hybrid_lift_eq :
    checkAndLiftWitness cmHybrid hybridWit =
      .ok ([liftRegion cmHybrid hybridRw],
        [mkEntry "cold_fallback" 40#64 (fun _ r => .halt (.var r.r3))]) := by
  dsimp only [checkAndLiftWitness]
  rw [hybrid_check, hybrid_res_eq]
  rfl

theorem hybrid_lift_count : liftCount cmHybrid hybridWit = 1 := by
  simp [liftCount, hybrid_lift_eq]

theorem hybrid_res_addrs : resAddrs cmHybrid hybridWit = [40#64] := by
  simp [resAddrs, hybrid_lift_eq]; rfl

theorem hybrid_supports_x64 :
    ((liftRegion cmHybrid hybridRw).earlyOpt).body.supportsSource .x64 = true := by
  t_kernel_rfl

theorem hybrid_mid_wf_x64 : ((liftRegion cmHybrid hybridRw).mid .x64).Wf :=
  liftRegion_mid_wf cmHybrid hybridRw .x64 hybrid_supports_x64

def psiColdAt40 : CodeSpec := fun pc st => pc = 40#64 → st.regs.r3 = 7#64
def haltR3Eq7 : HaltPost := fun c _ => c = 7#64

theorem hybrid_sound_holds :
    SpecsClosed cmHybrid cmHybrid.symEnv (PsiHyb cmHybrid hybridWit psiColdAt40 haltR3Eq7)
      haltR3Eq7 ∧
      ∀ pc₀ st₀, cmHybrid.wp haltR3Eq7 pc₀ st₀ → psiColdAt40 pc₀ st₀ := by
  refine checkAndLiftWitness_hybrid_sound cmHybrid hybridWit psiColdAt40 haltR3Eq7
    (haltSpec 7#64) .x64 hybrid_lift_eq (fun _ _ hc => hc)
    (by simp [hybridWit, hybrid_supports_x64]) ?_ ?_ ?_
  · intro pc b hlu st hbp
    dsimp only [CodeMap.lookupAddr] at hlu
    split at hlu
    · cases hlu
      intro _
      dsimp only [BlockFlat.wp, denoteArg, pushRegsV, Regs.toRegsV, RegsV.toTup,
        pushTup] at hbp
      exact hbp
    · cases hlu
  · intro rw hRw _ _ _
    simp only [hybridWit, List.mem_singleton] at hRw
    subst hRw
    intro h40
    cases h40
  · intro rw hRw _ pc hPc hNe _ _
    simp only [hybridWit, List.mem_singleton] at hRw
    subst hRw
    simp [hybridRw, RegionWitness.allPcs, GroupTree.allPcs] at hPc
    rcases hPc with rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hNe
    · intro h40; cases h40
    · intro h40; cases h40
    · intro h40; cases h40
    · intro h40; cases h40

end LeanQbeTest.T.BedrockCfgRecoveryTest

#print axioms LeanQbe.T.Unified.checkAndLiftWitness_cm_wp_to_mid
#print axioms LeanQbe.T.Unified.checkAndLiftWitness_hybrid_sound
#print axioms LeanQbe.T.Unified.psiReg_to_mid_spec
#print axioms LeanQbe.T.Unified.psiReg_to_func_spec
#print axioms LeanQbe.T.Unified.liftRegion_wf
#print axioms LeanQbe.T.Unified.liftRegion_mid_wf
#print axioms LeanQbe.T.BedrockWord.CodeMap.adequacy
#print axioms LeanQbeTest.T.BedrockCfgRecoveryTest.stride_un_mid_spec_x64
#print axioms LeanQbeTest.T.BedrockCfgRecoveryTest.loop_main_mid_spec
#print axioms LeanQbeTest.T.BedrockCfgRecoveryTest.dual_caller_mid_spec
#print axioms LeanQbeTest.T.BedrockCfgRecoveryTest.hybrid_mid_wf_x64
#print axioms LeanQbeTest.T.BedrockCfgRecoveryTest.hybrid_sound_holds
