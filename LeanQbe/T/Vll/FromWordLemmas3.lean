module

public import LeanQbe.T.Vll.FromWord
import LeanQbe.T.Vll.FromWordLemmas0
import LeanQbe.T.Vll.FromWordLemmas1
import LeanQbe.T.Vll.FromWordLemmas2
import LeanQbe.T.Unified.CfgContifyLemmas
import LeanQbe.T.BedrockWord.Ops
import LeanQbe.T.AbiLemmas
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.OpsLemmas
import LeanQbe.T.TargetLemmas

/-!
# Stage-1 Contification & Private-Frame Block Simulation (`Vll.FromWordLemmas3`)

Arch-free intermediate simulation layer behind the private proof firewall for
`LeanQbe.T.Vll.FromWord.fromWordContify`:
* §1. Local helpers, `regionExitSuffix_bodyWp`, `lowerStrideCascade_body_bwp`, and
      `lowerGuardedTargets_body_bwp`.
* §2. Full Stage-1 `lowerContEdge_body_bwp`, `lowerContBlock_body_bwp`, and `lowerContBlock_bwp`
      handling promoted `[sp₀ - 8*(k+1)]` slots, static outside-frame ops, dynamic alias
      guards + flush fallback, `.contCall` / `.contRet` (including `dualRet` `b.altRet`),
      `.strideTable`, `.guarded`, and `.bailout`.

Zero `@[expose]`, zero `Arm64`/`Amd64`/`Kraken.X64`/`Kraken.AArch64` imports, zero `*Lemmas*`
public imports.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Vll

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.BedrockWord
open LeanQbe.T.Unified

/-! ## §1. Local Helpers, Exit Suffix & Cascades -/

private theorem contSymVal_asConst_of_match {bvs : List ((t : Ty) × Val t)} {sp₀ rp₀ : BitVec 64}
    {sv : ContSymVal} {x pc : BitVec 64} (hm : ContSymValMatch bvs sp₀ rp₀ sv i64 x)
    (hc : sv.toSymVal.asConst? = some pc) : x = pc := by
  cases sv <;> dsimp only [ContSymVal.toSymVal, SymVal.asConst?] at hc <;> cases hc
  · exact hm rfl
  · exact (hm rfl).1

private theorem contSymState_asConst_val {bvs : List ((t : Ty) × Val t)} {sp₀ rp₀ : BitVec 64}
    {st : ContSymState} (hst : ContSymStateOk bvs sp₀ rp₀ st)
    {a : Arg K i64} {a' : Arg Val i64} (ha : denoteArg bvs a = some a')
    {pc : BitVec 64} (hc : st.toSymState.resolveConst a = some pc) : a'.val = pc := by
  dsimp only [SymState.resolveConst] at hc; rw [contSymState_toSymVal_eval a] at hc
  exact contSymVal_asConst_of_match (evalContArg_symValMatch hst ha) hc

private theorem denoteRegsExpr_sp_rp {vs : List ((t : Ty) × Val t)} {nxt : RegsExpr K}
    {nxt' : RegsExpr Val} (hn : denoteRegsExpr vs nxt = some nxt') :
    denoteArg vs nxt.sp = some nxt'.sp ∧ denoteArg vs nxt.rp = some nxt'.rp := by
  dsimp only [denoteRegsExpr] at hn
  cases h0 : denoteArg vs nxt.sp <;> rw [h0] at hn; · cases hn
  cases h1 : denoteArg vs nxt.rp <;> rw [h1] at hn; · cases hn
  cases h2 : denoteArg vs nxt.rv <;> rw [h2] at hn; · cases hn
  cases h3 : denoteArg vs nxt.r1 <;> rw [h3] at hn; · cases hn
  cases h4 : denoteArg vs nxt.r2 <;> rw [h4] at hn; · cases hn
  cases h5 : denoteArg vs nxt.r3 <;> rw [h5] at hn; · cases hn
  cases hn; exact ⟨rfl, rfl⟩

private theorem spZero_contNxtSp {bvs : List ((t : Ty) × Val t)} {sp₀ rp₀ : BitVec 64}
    {st : ContSymState} (hst : ContSymStateOk bvs sp₀ rp₀ st) {nxt : RegsExpr K}
    {nxt' : RegsExpr Val} (hn : denoteRegsExpr bvs nxt = some nxt')
    (hEq : (st.evalArg nxt.sp == .spOffset 0#64) = true) : nxt'.eval.sp = sp₀ := by
  have hm := evalContArg_symValMatch hst (denoteRegsExpr_sp_rp hn).1
  rw [beq_iff_eq.mp hEq] at hm
  have hsp : nxt'.sp.val = sp₀ + 0#64 := hm rfl
  dsimp only [denoteRegsExpr] at hn
  cases h0 : denoteArg bvs nxt.sp <;> rw [h0] at hn; · cases hn
  cases h1 : denoteArg bvs nxt.rp <;> rw [h1] at hn; · cases hn
  cases h2 : denoteArg bvs nxt.rv <;> rw [h2] at hn; · cases hn
  cases h3 : denoteArg bvs nxt.r1 <;> rw [h3] at hn; · cases hn
  cases h4 : denoteArg bvs nxt.r2 <;> rw [h4] at hn; · cases hn
  cases h5 : denoteArg bvs nxt.r3 <;> rw [h5] at hn; · cases hn
  cases hn; simpa [RegsExpr.eval] using hsp

private theorem resolveConst_nxt_rp {bvs : List ((t : Ty) × Val t)} {sp₀ rp₀ : BitVec 64}
    {st : ContSymState} (hst : ContSymStateOk bvs sp₀ rp₀ st) {nxt : RegsExpr K}
    {nxt' : RegsExpr Val} (hn : denoteRegsExpr bvs nxt = some nxt')
    {pc : BitVec 64} (hc : st.toSymState.resolveConst nxt.rp = some pc) :
    nxt'.eval.rp = pc := by
  have hv := contSymState_asConst_val hst (denoteRegsExpr_sp_rp hn).2 hc
  dsimp only [denoteRegsExpr] at hn
  cases h0 : denoteArg bvs nxt.sp <;> rw [h0] at hn; · cases hn
  cases h1 : denoteArg bvs nxt.rp <;> rw [h1] at hn; · cases hn
  cases h2 : denoteArg bvs nxt.rv <;> rw [h2] at hn; · cases hn
  cases h3 : denoteArg bvs nxt.r1 <;> rw [h3] at hn; · cases hn
  cases h4 : denoteArg bvs nxt.r2 <;> rw [h4] at hn; · cases hn
  cases h5 : denoteArg bvs nxt.r3 <;> rw [h5] at hn; · cases hn
  cases hn; simpa [RegsExpr.eval] using hv

/-- Local public write-slots helper mirroring `Unified.writeSlots` without exposing private
`CfgContifyLemmas` definitions. -/
def stage1WriteSlots (m : Mem 64) (sp0 : BitVec 64) : Nat → List (BitVec 64) → Mem 64
  | _, [] => m
  | k, v :: vs => stage1WriteSlots (storeMem m i64 (slotAddr sp0 k) v) sp0 (k + 1) vs

/-- Local public private-frame relation mirroring `PrivSlotsRel` without exposing private
`*Lemmas*` definitions in public theorem types. -/
def Stage1PrivSlots (nPriv : Nat) (sp0 : BitVec 64) (slots : List (BitVec 64))
    (mConc mPub : Mem 64) : Prop :=
  if nPriv = 0 then mConc = mPub
  else
    slots.length ≥ nPriv + 1 ∧ nPriv ≤ 64 ∧ slots[nPriv]? = some sp0 ∧
    (slots.take nPriv).length = nPriv ∧
    (∀ k < nPriv, storeOk mPub i64 (slotAddr sp0 k)) ∧
    mConc = stage1WriteSlots mPub sp0 0 (slots.take nPriv)

private theorem stage1WriteSlots_eq_foldl (sp0 : BitVec 64) :
    ∀ (k : Nat) (vs : List (BitVec 64)) (m : Mem 64),
      stage1WriteSlots m sp0 k vs =
        (vs.foldl (fun (p : Nat × Mem 64) v =>
          (p.1 + 1, storeMem p.2 i64 (slotAddr sp0 p.1) v)) (k, m)).2
  | _, [], _ => rfl
  | k, v :: vs, m => by
    dsimp only [stage1WriteSlots]
    exact stage1WriteSlots_eq_foldl sp0 (k + 1) vs _

private theorem stage1PrivSlots_iff {nPriv : Nat} {sp0 : BitVec 64} {slots : List (BitVec 64)}
    {mConc mPub : Mem 64} :
    Stage1PrivSlots nPriv sp0 slots mConc mPub ↔ PrivSlotsRel nPriv sp0 slots mConc mPub := by
  rw [privSlotsRel_foldl_iff]
  by_cases hn : nPriv = 0
  · subst hn; simp [Stage1PrivSlots]
  · simp only [Stage1PrivSlots, hn, ↓reduceIte, stage1WriteSlots_eq_foldl]

theorem stage1PrivSlots_zero_eq {nPriv : Nat} {sp0 : BitVec 64} {slots : List (BitVec 64)}
    {m1 m2 : Mem 64} (hn : nPriv = 0) :
    Stage1PrivSlots nPriv sp0 slots m1 m2 ↔ m1 = m2 := by
  subst hn; simp [Stage1PrivSlots]

theorem emitPrivFrameInit_stage1_bodyWp {A : Arch} (hawf : A.Wf) {b : WordRegBind A}
    (hwf : b.Wf) {symAddr : Sym → BitVec 64} {nPriv : Nat} {sp0 : BitVec 64} {rw : Regs}
    {slots : List (BitVec 64)} {mL0 : Mem 64} {G : Mem 64 → Prop} {s : MachSt A}
    {Kpost : MachSt A → Prop} {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)}
    (hsp : rw.sp = sp0) (hr : WordRegsRel b rw s)
    (hpriv : nPriv > 0 → nPriv ≤ 64 ∧ ∀ k < nPriv, storeOk mL0 i64 (slotAddr sp0 k))
    (hlen : nPriv > 0 → nPriv + 1 ≤ slots.length)
    (hm : (array64 (s.gpr A.abi.sp) slots ⋆ (Eq mL0 ⋆ G)) s.mem)
    (hk : ∀ s' (slots' : List (BitVec 64)),
      slots'.length = slots.length →
      Stage1PrivSlots nPriv sp0 slots' mL0 mL0 →
      WordRegsRel b rw s' → s'.gpr A.abi.sp = s.gpr A.abi.sp →
      (∀ q, q ≠ b.w0 → s'.gpr q = s.gpr q) →
      (∀ j, nPriv + 1 ≤ j → slots'[j]? = slots[j]?) →
      (array64 (s'.gpr A.abi.sp) slots' ⋆ (Eq mL0 ⋆ G)) s'.mem →
      Kpost s') :
    bodyWp A symAddr (emitPrivFrameInit b nPriv) Kpost Ψ H s :=
  emitPrivFrameInit_bodyWp hawf hwf hsp hr hpriv hlen hm fun s' sl' hl hp hr' hs' hq' hj' hm' =>
    hk s' sl' hl (stage1PrivSlots_iff.mpr hp) hr' hs' hq' hj' hm'

private theorem listGet_of_cLevelVal_bool {bvs : List ((t : Ty) × Val t)} {d lvl : Nat}
    {v : Val .bool} (hb : bvs.length = d) (h : cLevelVal (t := .bool) bvs lvl = some v) :
    lvl < d ∧ listGet? bvs (d - 1 - lvl) = some ⟨.bool, v⟩ := by
  have hlt : lvl < d := by rw [← hb]; exact cLevelVal_lt_len h
  dsimp only [cLevelVal] at h; rw [hb, ite_eq_left hlt] at h
  dsimp only [lookupV] at h
  cases hg : listGet? bvs (d - 1 - lvl) with
  | none => rw [hg] at h; cases h
  | some p =>
    rcases p with ⟨t', v'⟩; rw [hg] at h; dsimp only at h
    cases t' with
    | bool => cases h; exact ⟨hlt, rfl⟩
    | bits _ | float _ | pair _ _ => cases h

private theorem listGet_of_cLevelVal_i64 {bvs : List ((t : Ty) × Val t)} {d lvl : Nat}
    {v : Val i64} (hb : bvs.length = d) (h : cLevelVal (t := i64) bvs lvl = some v) :
    lvl < d ∧ listGet? bvs (d - 1 - lvl) = some ⟨i64, v⟩ := by
  have hlt : lvl < d := by rw [← hb]; exact cLevelVal_lt_len h
  dsimp only [cLevelVal] at h; rw [hb, ite_eq_left hlt] at h
  dsimp only [lookupV] at h
  cases hg : listGet? bvs (d - 1 - lvl) with
  | none => rw [hg] at h; cases h
  | some p =>
    rcases p with ⟨t', v'⟩; rw [hg] at h; dsimp only at h
    cases t' with
    | bits m =>
      dsimp only [castTy] at h; split at h
      · rename_i heq; cases heq; cases h; exact ⟨hlt, rfl⟩
      · cases h
    | bool | float _ | pair _ _ => cases h

private theorem bodyWp_imp_raReg_cont {A : Arch} {b : WordRegBind A} (hwf : b.Wf)
    {symAddr : Sym → BitVec 64} {P : Prop} {ra₀ : BitVec 64} {is : List (Instr A)}
    {Kpost : MachSt A → Prop} {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)}
    {s : MachSt A} (hno : ∀ i ∈ is, IsNoRaInstr b i) (hra : P → (vllFramePreds A).raReg s ra₀)
    (hwp : bodyWp A symAddr is (fun s' => (P → (vllFramePreds A).raReg s' ra₀) → Kpost s') Ψ H s) :
    bodyWp A symAddr is Kpost Ψ H s :=
  bodyWp_mono (fun _ ⟨hk, hra'⟩ => hk hra') (bodyWp_imp_raReg hwf hno hra hwp)

private theorem bodyWp_imp_raReg_mono {A : Arch} {b : WordRegBind A} (hwf : b.Wf)
    {symAddr : Sym → BitVec 64} {P : Prop} {ra₀ : BitVec 64} {is : List (Instr A)}
    {K₁ K₂ : MachSt A → Prop} {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)}
    {s : MachSt A} (hno : ∀ i ∈ is, IsNoRaInstr b i) (hra : P → (vllFramePreds A).raReg s ra₀)
    (hwp : bodyWp A symAddr is K₁ Ψ H s)
    (hmono : ∀ s', K₁ s' → (P → (vllFramePreds A).raReg s' ra₀) → K₂ s') :
    bodyWp A symAddr is K₂ Ψ H s :=
  bodyWp_mono (fun s' ⟨hk, hra'⟩ => hmono s' hk hra') (bodyWp_imp_raReg hwf hno hra hwp)

private theorem regionExitSuffix_bodyWp {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {vcm : VllCodeMap A} {nPriv ns ns_ : Nat} {needFrame : Bool}
    {sp0 hwSp ra₀ tgtVal : BitVec 64} {nxtR : Regs} {slots : List (BitVec 64)}
    {mConc mPub : Mem 64} {G : Mem 64 → Prop} {s : MachSt A}
    {K : MachSt A → Prop} {Ψ_L1 : Xcap.CodeSpec (MachSt A)} {H_L1 : Xcap.Halt (MachSt A)}
    (_hsb_le : nPriv > 0 → nPriv + 1 ≤ ns_) (_hlen : slots.length = ns_)
    (hw0 : s.gpr b.w0 = tgtVal) (hr : WordRegsRel b nxtR s)
    (hra : needFrame = false → (vllFramePreds A).raReg s ra₀)
    (hsp : s.gpr A.abi.sp = hwSp) (hpriv : PrivSlotsRel nPriv sp0 slots mConc mPub)
    (hm : (array64 hwSp slots ⋆ (Eq mPub ⋆ G)) s.mem)
    (hEp : ∀ s_fin,
      s_fin.gpr b.w0 = tgtVal → WordRegsRel b nxtR s_fin →
      (needFrame = false → (vllFramePreds A).raReg s_fin ra₀) →
      s_fin.gpr A.abi.sp = hwSp →
      (array64 hwSp slots ⋆ (Eq mConc ⋆ G)) s_fin.mem →
      bodyWp A vcm.symAddr (if needFrame then [.epilogue ns] else []) K Ψ_L1 H_L1 s_fin) :
    bodyWp A vcm.symAddr (regionExitSuffix b nPriv ns needFrame) K Ψ_L1 H_L1 s := by
  dsimp only [regionExitSuffix]
  refine bodyWp_append (emitPrivFlush b nPriv) _ s ?_
  have he0 : EnvRel b (if nPriv > 0 then nPriv + 1 else 0) 6 (pushRegsV nxtR.toRegsV) s :=
    envRel_pushRegsV _ hr
  have hsb_if : nPriv > 0 → nPriv + 1 ≤ (if nPriv > 0 then nPriv + 1 else 0) := fun hp => by
    simp [hp]
  have hslots6 : ∀ lvl < 6, ∀ j,
      locOf b (if nPriv > 0 then nPriv + 1 else 0) lvl = .slot j → j < slots.length := by
    intro lvl hl j hj
    dsimp only [locOf] at hj; rw [ite_eq_left hl] at hj; cases hj
  have hm' : (array64 (s.gpr A.abi.sp) slots ⋆ (Eq mPub ⋆ G)) s.mem := by simpa [hsp] using hm
  refine bodyWp_imp_raReg_mono hwf (isNoRa_emitPrivFlush b nPriv) hra
    (emitPrivFlush_bodyWp hawf hwf hsb_if hslots6 he0 hr hpriv hm'
      fun s' hw0' hr' _ hsp' hm'' =>
        And.intro (hw0'.trans hw0)
          (And.intro hr' (And.intro (hsp'.trans hsp) (by simpa [hsp'.trans hsp] using hm''))))
    fun s' ⟨hw0', hr', hsp', hm''⟩ hra' => hEp s' hw0' hr' hra' hsp' hm''

private theorem lowerStrideCascade_head_shape {A : Arch} (b : WordRegBind A) (cr : ContifyRegion)
    (nPriv ns : Nat) (needFrame needGuard : Bool) (ccEq : A.Cond) :
    ∀ (targets : List (BitVec 64)) (curLbl : Sym) (acc : List (Instr A)) (idx : Nat)
      {s0 s1 : Nat} {bs : List (Block A)},
      (lowerStrideCascade b cr nPriv ns needFrame needGuard ccEq curLbl acc idx targets).run s0 =
        .ok (bs, s1) →
      ∃ blk0 rest bodyTail, bs = blk0 :: rest ∧ blk0.label = curLbl ∧ blk0.pad? = none ∧
        blk0.body = acc ++ bodyTail
  | [], l, acc, _, _, _, _, h => by
    dsimp only [lowerStrideCascade] at h
    dsimp only [Pure.pure, StateT.pure] at h; cases h
    exact ⟨_, _, _, rfl, rfl, rfl, rfl⟩
  | [_], l, acc, _, _, _, _, h => by
    dsimp only [lowerStrideCascade] at h; split at h
    · dsimp only [Pure.pure, StateT.pure] at h; cases h
      exact ⟨_, _, [], rfl, rfl, rfl, (List.append_nil acc).symm⟩
    · obtain ⟨_, _, _, h2⟩ := lowerM_bind_ok' h
      dsimp only [Pure.pure, StateT.pure] at h2; cases h2
      exact ⟨_, _, _, rfl, rfl, rfl, rfl⟩
  | _ :: _ :: _, l, acc, _, _, _, _, h => by
    dsimp only [lowerStrideCascade] at h
    obtain ⟨_, _, _, h2⟩ := lowerM_bind_ok' h
    obtain ⟨_, _, _, h3⟩ := lowerM_bind_ok' h2
    dsimp only [Pure.pure, StateT.pure] at h3; cases h3
    exact ⟨_, _, _, rfl, rfl, rfl, rfl⟩

private theorem lowerStrideCascade_body_bwp {A : Arch} (hawf : A.Wf) {b : WordRegBind A}
    (hwf : b.Wf) {vcm : VllCodeMap A} (hvwf : vcm.Wf)
    {cr : ContifyRegion} {nPriv ns ns_ : Nat} {needFrame needGuard : Bool}
    {ccEq : A.Cond} {basePc sp0 rp0 hwSp ra₀ : BitVec 64} {pcs : List (BitVec 64)}
    {G : Mem 64 → Prop} {Ψ_L0 : BedrockWord.CodeSpec}
    {Ψ_L1 : Xcap.CodeSpec (MachSt A)} {H_L1 : Xcap.Halt (MachSt A)}
    (hcl : Xcap.Closed (vllXcapMach A vcm.symAddr) vcm.toXcapCode Ψ_L1 H_L1)
    (hcc : b.condOfCmp? .eq = some ccEq)
    (hsb_le : nPriv > 0 → nPriv + 1 ≤ ns_)
    (hInner : ∀ (p : BitVec 64) (nxtR : Regs) (mConc mPub : Mem 64) (slots : List (BitVec 64))
      (s_t : MachSt A),
      (findLabelIdx pcs p).isSome = true → slots.length = ns_ →
      WordRegsRel b nxtR s_t → (nPriv > 0 → nxtR.sp = sp0) →
      (cr.abi.isContified = true → nxtR.rp = rp0) →
      (needFrame = false → (vllFramePreds A).raReg s_t ra₀) →
      s_t.gpr A.abi.sp = hwSp → PrivSlotsRel nPriv sp0 slots mConc mPub →
      (array64 hwSp slots ⋆ (Eq mPub ⋆ G)) s_t.mem →
      Ψ_L0 p ⟨nxtR, mConc⟩ → Ψ_L1 (vcm.symAddr (innerLabel cr p)) s_t)
    (hEndIjmp : needGuard = true → ∀ s_fin (tgtVal : BitVec 64) (nxt' : Regs) (m' : Mem 64)
      (slots' : List (BitVec 64)),
      slots'.length = ns_ → s_fin.gpr b.w0 = tgtVal → WordRegsRel b nxt' s_fin →
      (needFrame = false → (vllFramePreds A).raReg s_fin ra₀) →
      s_fin.gpr A.abi.sp = hwSp → (array64 hwSp slots' ⋆ (Eq m' ⋆ G)) s_fin.mem →
      Ψ_L0 tgtVal ⟨nxt', m'⟩ →
      bodyWp A vcm.symAddr (if needFrame then [.epilogue ns] else [])
        (fun s' => Ψ_L1 (s'.gpr b.w0) s') Ψ_L1 H_L1 s_fin) :
    ∀ (targets : List (BitVec 64)) (curLbl : Sym) (acc bodyTail : List (Instr A)) (idx : Nat)
      (x : BitVec 64) (nxtR : Regs) (mConc mPub : Mem 64) (slots : List (BitVec 64))
      {s0 s1 : Nat} {blk0 : Block A} {rest : List (Block A)} (s : MachSt A),
      (lowerStrideCascade b cr nPriv ns needFrame needGuard ccEq curLbl acc idx targets).run s0 =
        .ok (blk0 :: rest, s1) →
      blk0.body = acc ++ bodyTail →
      (∀ blk ∈ blk0 :: rest, blk ∈ vcm.blocks) →
      checkStrideTargets pcs basePc idx targets = true →
      idx ≤ x.toNat → (needGuard = false → x.toNat < idx + targets.length) →
      slots.length = ns_ → s.gpr b.w2 = x →
      (needGuard = true → s.gpr b.w0 = basePc + BitVec.ofNat 64 (8 * x.toNat)) →
      WordRegsRel b nxtR s → (nPriv > 0 → nxtR.sp = sp0) →
      (cr.abi.isContified = true → nxtR.rp = rp0) →
      (needFrame = false → (vllFramePreds A).raReg s ra₀) →
      s.gpr A.abi.sp = hwSp → PrivSlotsRel nPriv sp0 slots mConc mPub →
      (array64 hwSp slots ⋆ (Eq mPub ⋆ G)) s.mem →
      Ψ_L0 (basePc + BitVec.ofNat 64 (8 * x.toNat)) ⟨nxtR, mConc⟩ →
      bodyWp A vcm.symAddr bodyTail (termWp A vcm.symAddr blk0.term Ψ_L1 H_L1) Ψ_L1 H_L1 s
  | [], l, acc, bodyTail, idx, x, nxtR, mConc, mPub, slots, s0, s1, blk0, rest, s,
      hlo, hbody, _, _, hloIdx, hbd, hlen, _, hw0, hr, _, _, hra, hsp, hpriv, hm, hbp => by
    have hng : needGuard = true := by
      cases needGuard
      · have hlt := hbd rfl; simp at hlt; omega
      · rfl
    dsimp only [lowerStrideCascade] at hlo
    dsimp only [Pure.pure, StateT.pure] at hlo; cases hlo
    have hTailEq : bodyTail = regionExitSuffix b nPriv ns needFrame := by
      dsimp only at hbody; exact List.append_cancel_left hbody.symm
    rw [hTailEq]
    refine bodyWp_mono (fun s' h => termWp_ijmp h) ?_
    exact regionExitSuffix_bodyWp hawf hwf hsb_le hlen (hw0 hng) hr hra hsp hpriv hm
      fun s_fin hw0' hr' hra' hsp' hm' =>
        hEndIjmp hng s_fin _ nxtR mConc slots hlen hw0' hr' hra' hsp' hm' hbp
  | [lastPc], l, acc, bodyTail, idx, x, nxtR, mConc, mPub, slots, s0, s1, blk0, rest, s,
      hlo, hbody, hsub, hchk, hloIdx, hbd, hlen, hw2, hw0, hr, hnSp, hnRp, hra,
      hsp, hpriv, hm, hbp => by
    obtain ⟨tPc, ht, hPcEq, hPcIn⟩ := checkStrideTargets_spec hchk 0 (by simp)
    cases ht; rw [Nat.add_zero] at hPcEq
    cases hng : needGuard with
    | false =>
      rw [hng] at hlo
      dsimp only [lowerStrideCascade, Bool.not_false, ↓reduceIte] at hlo
      dsimp only [Pure.pure, StateT.pure] at hlo; cases hlo
      have hTailEq : bodyTail = [] := by
        dsimp only at hbody
        conv at hbody => lhs; rw [← List.append_nil acc]
        exact List.append_cancel_left hbody.symm
      subst hTailEq
      have hxEq : x.toNat = idx := by have := hbd hng; simp at this; omega
      rw [hxEq, ← hPcEq] at hbp
      exact termWp_jmp (hInner lastPc nxtR mConc mPub slots s hPcIn hlen hr
        hnSp hnRp hra hsp hpriv hm hbp)
    | true =>
      rw [hng] at hlo
      dsimp only [lowerStrideCascade, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hlo
      obtain ⟨bailLbl, _, _, h2⟩ := lowerM_bind_ok' hlo
      dsimp only [Pure.pure, StateT.pure] at h2; cases h2
      dsimp only at hbody
      have hTailEq : bodyTail = [.cmp .w64 b.w2 (.imm (BitVec.ofNat 64 idx))] :=
        List.append_cancel_left hbody.symm
      subst hTailEq
      refine instrWp_cmp ?_
      let s1 := s.setFlags (A.cmpFlags .w64 ((s.gpr b.w2).setWidth 64)
        (Src.evalW .w64 s.gpr (.imm (BitVec.ofNat 64 idx))) s.flags)
      have hev : A.evalCond s1.flags ccEq = CmpOp.evalBits .eq x (BitVec.ofNat 64 idx) := by
        have hsd := hwf.cond_sound .eq ccEq .w64 ((s.gpr b.w2).setWidth 64)
          (Src.evalW .w64 s.gpr (.imm (BitVec.ofNat 64 idx))) s.flags hcc
        simpa [s1, Src.evalW, Src.eval, BitVec.setWidth_eq, hw2] using hsd
      have hidx64 : idx < 2 ^ 64 := Nat.lt_of_le_of_lt hloIdx x.isLt
      refine termWp_jcc (fun htr => ?_) (fun hfl => ?_)
      · rw [hev] at htr
        have hxBv : x = BitVec.ofNat 64 idx := of_decide_eq_true htr
        have hxNat : x.toNat = idx := by rw [hxBv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hidx64]
        rw [hxNat, ← hPcEq] at hbp
        exact hInner lastPc nxtR mConc mPub slots s1 hPcIn hlen
          ((wordRegsRel_setFlags _ _ _ _).mpr hr) hnSp hnRp
          (fun h => (raReg_setFlags A _ _ _).mpr (hra h)) hsp hpriv hm hbp
      · refine closed_bwp hvwf hcl (hsub _ (List.mem_cons_of_mem _ List.mem_cons_self)) ?_
        refine bodyWp_mono (fun s' h => termWp_ijmp h) ?_
        exact regionExitSuffix_bodyWp hawf hwf hsb_le hlen (hw0 hng)
          ((wordRegsRel_setFlags _ _ _ _).mpr hr)
          (fun h => (raReg_setFlags A _ _ _).mpr (hra h)) hsp hpriv hm
          fun s_fin hw0' hr' hra' hsp' hm' =>
            hEndIjmp hng s_fin _ nxtR mConc slots hlen hw0' hr' hra' hsp' hm' hbp
  | tPc :: r0 :: rs', l, acc, bodyTail, idx, x, nxtR, mConc, mPub, slots, s0, s1, blk0, rest, s,
      hlo, hbody, hsub, hchk, hloIdx, hbd, hlen, hw2, hw0, hr, hnSp, hnRp, hra,
      hsp, hpriv, hm, hbp => by
    obtain ⟨tPc', ht, hPcEq, hPcIn⟩ := checkStrideTargets_spec hchk 0 (by simp)
    cases ht; rw [Nat.add_zero] at hPcEq
    dsimp only [lowerStrideCascade] at hlo
    obtain ⟨nextLbl, _, _, h2⟩ := lowerM_bind_ok' hlo
    obtain ⟨tailBs, _, htail, h3⟩ := lowerM_bind_ok' h2
    dsimp only [Pure.pure, StateT.pure] at h3; cases h3
    dsimp only at hbody
    have hTailEq : bodyTail = [.cmp .w64 b.w2 (.imm (BitVec.ofNat 64 idx))] :=
      List.append_cancel_left hbody.symm
    subst hTailEq
    refine instrWp_cmp ?_
    let s1 := s.setFlags (A.cmpFlags .w64 ((s.gpr b.w2).setWidth 64)
      (Src.evalW .w64 s.gpr (.imm (BitVec.ofNat 64 idx))) s.flags)
    have hev : A.evalCond s1.flags ccEq = CmpOp.evalBits .eq x (BitVec.ofNat 64 idx) := by
      have hsd := hwf.cond_sound .eq ccEq .w64 ((s.gpr b.w2).setWidth 64)
        (Src.evalW .w64 s.gpr (.imm (BitVec.ofNat 64 idx))) s.flags hcc
      simpa [s1, Src.evalW, Src.eval, BitVec.setWidth_eq, hw2] using hsd
    have hidx64 : idx < 2 ^ 64 := Nat.lt_of_le_of_lt hloIdx x.isLt
    refine termWp_jcc (fun htr => ?_) (fun hfl => ?_)
    · rw [hev] at htr
      have hxBv : x = BitVec.ofNat 64 idx := of_decide_eq_true htr
      have hxNat : x.toNat = idx := by rw [hxBv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hidx64]
      rw [hxNat, ← hPcEq] at hbp
      exact hInner tPc nxtR mConc mPub slots s1 hPcIn hlen
        ((wordRegsRel_setFlags _ _ _ _).mpr hr) hnSp hnRp
        (fun h => (raReg_setFlags A _ _ _).mpr (hra h)) hsp hpriv hm hbp
    · rw [hev] at hfl
      have hne : x ≠ BitVec.ofNat 64 idx := fun e => by simp [CmpOp.evalBits, e] at hfl
      have hneNat : x.toNat ≠ idx := fun e => hne <| BitVec.eq_of_toNat_eq <| by
        rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hidx64]
      dsimp only [checkStrideTargets] at hchk
      have hchkR := (Bool.and_eq_true_iff.mp hchk).2
      have hsubT : ∀ blk ∈ rest, blk ∈ vcm.blocks := fun blk hb =>
        hsub blk (List.mem_cons_of_mem _ hb)
      obtain ⟨blkN, restN, tailN, hEqN, hlblN, _, hbodyN⟩ :=
        lowerStrideCascade_head_shape b cr nPriv
          ns needFrame needGuard ccEq (r0 :: rs') nextLbl [] (idx + 1) htail
      cases hEqN
      have hbwN := lowerStrideCascade_body_bwp hawf hwf hvwf hcl hcc hsb_le hInner hEndIjmp
        (r0 :: rs') nextLbl [] tailN (idx + 1) x nxtR mConc mPub slots s1 htail hbodyN hsubT
        hchkR (by omega)
        (fun hg => by have := hbd hg; simp only [List.length_cons] at this ⊢; omega)
        hlen hw2 hw0 ((wordRegsRel_setFlags _ _ _ _).mpr hr) hnSp hnRp
        (fun h => (raReg_setFlags A _ _ _).mpr (hra h)) hsp hpriv hm hbp
      exact hlblN ▸ closed_bwp hvwf hcl (hsubT blkN List.mem_cons_self)
        ((List.nil_append tailN ▸ hbodyN) ▸ hbwN)

private theorem lowerGuardedTargets_head_shape {A : Arch} (b : WordRegBind A)
    (cr : ContifyRegion) (nPriv ns : Nat) (needFrame : Bool) (ccEq : A.Cond) :
    ∀ (targets : List (BitVec 64)) (curLbl : Sym) (acc : List (Instr A))
      {s0 s1 : Nat} {bs : List (Block A)},
      (lowerGuardedTargets b cr nPriv ns needFrame ccEq curLbl acc targets).run s0 =
        .ok (bs, s1) →
      ∃ blk0 rest bodyTail, bs = blk0 :: rest ∧ blk0.label = curLbl ∧ blk0.pad? = none ∧
        blk0.body = acc ++ bodyTail
  | [], l, acc, _, _, _, h => by
    dsimp only [lowerGuardedTargets] at h
    dsimp only [Pure.pure, StateT.pure] at h; cases h
    exact ⟨_, _, _, rfl, rfl, rfl, rfl⟩
  | _ :: _, l, acc, _, _, _, h => by
    dsimp only [lowerGuardedTargets] at h
    obtain ⟨_, _, _, h2⟩ := lowerM_bind_ok' h
    obtain ⟨_, _, _, h3⟩ := lowerM_bind_ok' h2
    dsimp only [Pure.pure, StateT.pure] at h3; cases h3
    exact ⟨_, _, _, rfl, rfl, rfl, rfl⟩

private theorem lowerGuardedTargets_body_bwp {A : Arch} (hawf : A.Wf) {b : WordRegBind A}
    (hwf : b.Wf) {vcm : VllCodeMap A} (hvwf : vcm.Wf)
    {cr : ContifyRegion} {nPriv ns ns_ : Nat} {needFrame : Bool}
    {ccEq : A.Cond} {tgtVal sp0 rp0 hwSp ra₀ : BitVec 64} {pcs : List (BitVec 64)}
    {G : Mem 64 → Prop} {Ψ_L0 : BedrockWord.CodeSpec}
    {Ψ_L1 : Xcap.CodeSpec (MachSt A)} {H_L1 : Xcap.Halt (MachSt A)}
    (hcl : Xcap.Closed (vllXcapMach A vcm.symAddr) vcm.toXcapCode Ψ_L1 H_L1)
    (hcc : b.condOfCmp? .eq = some ccEq)
    (hsb_le : nPriv > 0 → nPriv + 1 ≤ ns_)
    (hInner : ∀ (p : BitVec 64) (nxtR : Regs) (mConc mPub : Mem 64) (slots : List (BitVec 64))
      (s_t : MachSt A),
      (findLabelIdx pcs p).isSome = true → slots.length = ns_ →
      WordRegsRel b nxtR s_t → (nPriv > 0 → nxtR.sp = sp0) →
      (cr.abi.isContified = true → nxtR.rp = rp0) →
      (needFrame = false → (vllFramePreds A).raReg s_t ra₀) →
      s_t.gpr A.abi.sp = hwSp → PrivSlotsRel nPriv sp0 slots mConc mPub →
      (array64 hwSp slots ⋆ (Eq mPub ⋆ G)) s_t.mem →
      Ψ_L0 p ⟨nxtR, mConc⟩ → Ψ_L1 (vcm.symAddr (innerLabel cr p)) s_t)
    (hEndIjmp : ∀ s_fin (tgtVal : BitVec 64) (nxt' : Regs) (m' : Mem 64)
      (slots' : List (BitVec 64)),
      slots'.length = ns_ → s_fin.gpr b.w0 = tgtVal → WordRegsRel b nxt' s_fin →
      (needFrame = false → (vllFramePreds A).raReg s_fin ra₀) →
      s_fin.gpr A.abi.sp = hwSp → (array64 hwSp slots' ⋆ (Eq m' ⋆ G)) s_fin.mem →
      Ψ_L0 tgtVal ⟨nxt', m'⟩ →
      bodyWp A vcm.symAddr (if needFrame then [.epilogue ns] else [])
        (fun s' => Ψ_L1 (s'.gpr b.w0) s') Ψ_L1 H_L1 s_fin) :
    ∀ (targets : List (BitVec 64)) (curLbl : Sym) (acc bodyTail : List (Instr A))
      (nxtR : Regs) (mConc mPub : Mem 64) (slots : List (BitVec 64))
      {s0 s1 : Nat} {blk0 : Block A} {rest : List (Block A)} (s : MachSt A),
      (lowerGuardedTargets b cr nPriv ns needFrame ccEq curLbl acc targets).run s0 =
        .ok (blk0 :: rest, s1) →
      blk0.body = acc ++ bodyTail →
      (∀ blk ∈ blk0 :: rest, blk ∈ vcm.blocks) →
      targets.all (fun p => (findLabelIdx pcs p).isSome) = true →
      slots.length = ns_ → s.gpr b.w0 = tgtVal →
      WordRegsRel b nxtR s → (nPriv > 0 → nxtR.sp = sp0) →
      (cr.abi.isContified = true → nxtR.rp = rp0) →
      (needFrame = false → (vllFramePreds A).raReg s ra₀) →
      s.gpr A.abi.sp = hwSp → PrivSlotsRel nPriv sp0 slots mConc mPub →
      (array64 hwSp slots ⋆ (Eq mPub ⋆ G)) s.mem →
      Ψ_L0 tgtVal ⟨nxtR, mConc⟩ →
      bodyWp A vcm.symAddr bodyTail (termWp A vcm.symAddr blk0.term Ψ_L1 H_L1) Ψ_L1 H_L1 s
  | [], l, acc, bodyTail, nxtR, mConc, mPub, slots, s0, s1, blk0, rest, s,
      hlo, hbody, _, _, hlen, hw0, hr, _, _, hra, hsp, hpriv, hm, hbp => by
    dsimp only [lowerGuardedTargets] at hlo
    dsimp only [Pure.pure, StateT.pure] at hlo; cases hlo
    have hTailEq : bodyTail = regionExitSuffix b nPriv ns needFrame := by
      dsimp only at hbody; exact List.append_cancel_left hbody.symm
    rw [hTailEq]
    refine bodyWp_mono (fun s' h => termWp_ijmp h) ?_
    exact regionExitSuffix_bodyWp hawf hwf hsb_le hlen hw0 hr hra hsp hpriv hm
      fun s_fin hw0' hr' hra' hsp' hm' =>
        hEndIjmp s_fin tgtVal nxtR mConc slots hlen hw0' hr' hra' hsp' hm' hbp
  | hPc :: ts, l, acc, bodyTail, nxtR, mConc, mPub, slots, s0, s1, blk0, rest, s,
      hlo, hbody, hsub, hchk, hlen, hw0, hr, hnSp, hnRp, hra, hsp, hpriv, hm, hbp => by
    simp only [List.all_cons, Bool.and_eq_true] at hchk
    dsimp only [lowerGuardedTargets] at hlo
    obtain ⟨nextLbl, _, _, h2⟩ := lowerM_bind_ok' hlo
    obtain ⟨tailBs, _, htail, h3⟩ := lowerM_bind_ok' h2
    dsimp only [Pure.pure, StateT.pure] at h3; cases h3
    dsimp only at hbody
    have hTailEq : bodyTail = [.cmp .w64 b.w0 (.imm hPc)] := List.append_cancel_left hbody.symm
    subst hTailEq
    refine instrWp_cmp ?_
    let s1 := s.setFlags (A.cmpFlags .w64 ((s.gpr b.w0).setWidth 64)
      (Src.evalW .w64 s.gpr (.imm hPc)) s.flags)
    have hev : A.evalCond s1.flags ccEq = CmpOp.evalBits .eq tgtVal hPc := by
      have hsd := hwf.cond_sound .eq ccEq .w64 ((s.gpr b.w0).setWidth 64)
        (Src.evalW .w64 s.gpr (.imm hPc)) s.flags hcc
      simpa [s1, Src.evalW, Src.eval, BitVec.setWidth_eq, hw0] using hsd
    refine termWp_jcc (fun htr => ?_) (fun _ => ?_)
    · rw [hev] at htr
      have heq : tgtVal = hPc := of_decide_eq_true htr
      subst heq
      exact hInner tgtVal nxtR mConc mPub slots s1 hchk.1 hlen
        ((wordRegsRel_setFlags _ _ _ _).mpr hr) hnSp hnRp
        (fun h => (raReg_setFlags A _ _ _).mpr (hra h)) hsp hpriv hm hbp
    · have hsubT : ∀ blk ∈ rest, blk ∈ vcm.blocks := fun blk hb =>
        hsub blk (List.mem_cons_of_mem _ hb)
      obtain ⟨blkN, restN, tailN, rfl, hlblN, _, hbodyN⟩ :=
        lowerGuardedTargets_head_shape b cr nPriv ns needFrame ccEq ts nextLbl [] htail
      have hbwN := lowerGuardedTargets_body_bwp hawf hwf hvwf hcl hcc hsb_le hInner hEndIjmp
        ts nextLbl [] tailN nxtR mConc mPub slots s1 htail hbodyN hsubT hchk.2 hlen hw0
        ((wordRegsRel_setFlags _ _ _ _).mpr hr) hnSp hnRp
        (fun h => (raReg_setFlags A _ _ _).mpr (hra h)) hsp hpriv hm hbp
      exact hlblN ▸ closed_bwp hvwf hcl (hsubT blkN List.mem_cons_self)
        ((List.nil_append tailN ▸ hbodyN) ▸ hbwN)

/-! ## §2. Stage-1 `lowerContEdge`, `lowerContBlock` & `lowerContBlock_bwp` -/

private theorem lowerContEdge_head_shape {A : Arch} (b : WordRegBind A) (cr : ContifyRegion)
    (spillBase ns : Nat) (needFrame : Bool) (st : ContSymState) (d : Nat)
    (curLbl : Sym) (acc : List (Instr A)) (tgt : Arg K i64) (nxt : RegsExpr K)
    (kind : EdgeKind) {s0 s1 : Nat} {bs : List (Block A)}
    (h : (lowerContEdge b cr spillBase ns needFrame st d curLbl acc tgt nxt kind).run s0 =
      .ok (bs, s1)) :
    ∃ blk0 rest bodyTail, bs = blk0 :: rest ∧ blk0.label = curLbl ∧ blk0.pad? = none ∧
      blk0.body = acc ++ bodyTail := by
  dsimp only [lowerContEdge] at h
  cases kind with
  | direct _ =>
    dsimp only at h; obtain ⟨cnxt, _, _, h2⟩ := lowerM_bind_ok' h
    dsimp only [Pure.pure, StateT.pure] at h2; cases h2
    exact ⟨_, _, cnxt, rfl, rfl, rfl, rfl⟩
  | select _ _ =>
    dsimp only at h; split at h
    · rename_i cLvl _ _ _
      let cc := loadLevelInto b spillBase b.w0 cLvl
      obtain ⟨cnxt, _, _, h2⟩ := lowerM_bind_ok' h
      dsimp only [Pure.pure, StateT.pure] at h2; cases h2
      exact ⟨_, _, cc ++ cnxt, rfl, rfl, rfl, by simp only [List.append_assoc]; rfl⟩
    · dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at h; cases h
  | strideTable _ targets needGuard =>
    dsimp only at h
    cases hev : st.evalArg tgt with
    | stride _ idxLvl =>
      rw [hev] at h; dsimp only at h
      let cidx := loadLevelInto b spillBase b.w2 idxLvl
      cases hcc : b.condOfCmp? .eq with
      | none =>
        rw [hcc] at h; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at h; cases h
      | some cc =>
        rw [hcc] at h; try dsimp only at h
        cases hng : needGuard <;> rw [hng] at h <;> try dsimp only at h
        · obtain ⟨ctgt, _, _, h2⟩ := lowerM_bind_ok' h
          obtain ⟨cnxt, _, _, h3⟩ := lowerM_bind_ok' h2
          obtain ⟨blk0, rest, tail, rfl, hlbl, hpad, hbody⟩ := lowerStrideCascade_head_shape b cr
            cr.privFrame.numSlots ns needFrame false cc targets curLbl _ 0 h3
          exact ⟨blk0, rest, cidx ++ ctgt ++ cnxt ++ tail, rfl, hlbl, hpad,
            by simpa [List.append_assoc] using hbody⟩
        · obtain ⟨ctgt, _, _, h2⟩ := lowerM_bind_ok' h
          obtain ⟨cnxt, _, _, h3⟩ := lowerM_bind_ok' h2
          obtain ⟨blk0, rest, tail, rfl, hlbl, hpad, hbody⟩ := lowerStrideCascade_head_shape b cr
            cr.privFrame.numSlots ns needFrame true cc targets curLbl _ 0 h3
          exact ⟨blk0, rest, cidx ++ ctgt ++ cnxt ++ tail, rfl, hlbl, hpad,
            by simpa [List.append_assoc] using hbody⟩
    | _ =>
      rw [hev] at h; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at h; cases h
  | contCall _ _ dualRet _ altRetPc? =>
    cases habi : cr.abi <;> rw [habi] at h <;> dsimp only at h
    · obtain ⟨cnxt, _, _, h2⟩ := lowerM_bind_ok' h
      cases dualRet
      · simp only [Bool.false_eq_true, ↓reduceIte] at h2
        dsimp only [Pure.pure, StateT.pure] at h2; cases h2
        exact ⟨_, _, cnxt, rfl, rfl, rfl, rfl⟩
      · simp only [↓reduceIte] at h2
        cases halt : altRetPc? with
        | none =>
          rw [halt] at h2; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at h2; cases h2
        | some _ =>
          rw [halt] at h2; dsimp only at h2
          obtain ⟨_, _, _, h3⟩ := lowerM_bind_ok' h2
          dsimp only [Pure.pure, StateT.pure] at h3; cases h3
          exact ⟨_, _, cnxt, rfl, rfl, rfl, rfl⟩
    · dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at h; cases h
  | contRet isAlt =>
    cases habi : cr.abi <;> rw [habi] at h
    · cases isAlt <;>
        (dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at h; cases h)
    · rename_i dualRet; cases dualRet <;> cases isAlt
      · dsimp only at h; obtain ⟨cnxt, _, _, h2⟩ := lowerM_bind_ok' h
        cases hnf : needFrame with
        | false =>
          rw [hnf] at h2; dsimp only [Pure.pure, StateT.pure] at h2; cases h2
          exact ⟨_, _, cnxt, rfl, rfl, rfl, by simp⟩
        | true =>
          rw [hnf] at h2; dsimp only [Pure.pure, StateT.pure] at h2; cases h2
          exact ⟨_, _, cnxt ++ [.epilogue ns], rfl, rfl, rfl, by simp [List.append_assoc]⟩
      · dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at h; cases h
      · dsimp only at h; obtain ⟨cnxt, _, _, h2⟩ := lowerM_bind_ok' h
        let fl : Instr A := .movi b.altRet 0#64
        cases hnf : needFrame with
        | false =>
          rw [hnf] at h2
          simp only [Bool.false_eq_true, ↓reduceIte, Pure.pure] at h2; cases h2
          exact ⟨_, _, cnxt ++ [fl], rfl, rfl, rfl, by simp [fl, List.append_assoc]⟩
        | true =>
          rw [hnf] at h2
          simp only [Bool.false_eq_true, ↓reduceIte, Pure.pure] at h2; cases h2
          exact ⟨_, _, cnxt ++ [fl] ++ [.epilogue ns], rfl, rfl, rfl,
            by simp [fl, List.append_assoc]⟩
      · dsimp only at h; obtain ⟨cnxt, _, _, h2⟩ := lowerM_bind_ok' h
        let fl : Instr A := .movi b.altRet 1#64
        cases hnf : needFrame with
        | false =>
          rw [hnf] at h2
          simp only [↓reduceIte, Pure.pure] at h2; cases h2
          exact ⟨_, _, cnxt ++ [fl], rfl, rfl, rfl, by simp [fl, List.append_assoc]⟩
        | true =>
          rw [hnf] at h2
          simp only [↓reduceIte, Pure.pure] at h2; cases h2
          exact ⟨_, _, cnxt ++ [fl] ++ [.epilogue ns], rfl, rfl, rfl,
            by simp [fl, List.append_assoc]⟩
  | guarded hotTargets =>
    cases habi : cr.abi <;> rw [habi] at h <;> dsimp only at h
    · cases hcc : b.condOfCmp? .eq with
      | none =>
        rw [hcc] at h; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at h; cases h
      | some cc =>
        rw [hcc] at h; dsimp only at h
        obtain ⟨ctgt, _, _, h2⟩ := lowerM_bind_ok' h
        obtain ⟨cnxt, _, _, h3⟩ := lowerM_bind_ok' h2
        obtain ⟨blk0, rest, tail, rfl, hlbl, hpad, hbody⟩ := lowerGuardedTargets_head_shape b cr
          cr.privFrame.numSlots ns needFrame cc hotTargets curLbl _ h3
        exact ⟨blk0, rest, ctgt ++ cnxt ++ tail, rfl, hlbl, hpad,
          by simpa [List.append_assoc] using hbody⟩
    · dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at h; cases h
  | bailout =>
    cases habi : cr.abi <;> rw [habi] at h <;> dsimp only at h
    · obtain ⟨ctgt, _, _, h2⟩ := lowerM_bind_ok' h
      obtain ⟨cnxt, _, _, h3⟩ := lowerM_bind_ok' h2
      cases hnf : needFrame with
      | false =>
        rw [hnf] at h3; dsimp only [Pure.pure, StateT.pure] at h3; cases h3
        exact ⟨_, _, ctgt ++ cnxt ++ emitPrivFlush b cr.privFrame.numSlots, rfl, rfl, rfl,
          by simp [regionExitSuffix, List.append_assoc]⟩
      | true =>
        rw [hnf] at h3; dsimp only [Pure.pure, StateT.pure] at h3; cases h3
        exact ⟨_, _, ctgt ++ cnxt ++ (emitPrivFlush b cr.privFrame.numSlots ++ [.epilogue ns]),
          rfl, rfl, rfl, by simp [regionExitSuffix, List.append_assoc]⟩
    · dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at h; cases h
  | memTableRo _ | memTableGuarded _ _ =>
    cases habi : cr.abi <;> rw [habi] at h <;>
      dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at h <;> cases h

private theorem lowerContBlock_head_shape {A : Arch} (b : WordRegBind A) (cm : CodeMap)
    (cr : ContifyRegion) (pc : BitVec 64) (spillBase ns : Nat) (needFrame : Bool) :
    ∀ (blk : BlockFlat) (curLbl : Sym) (acc : List (Instr A)) (d : Nat) (path : BranchPath)
      (st : ContSymState) {s0 s1 : Nat} {bs : List (Block A)},
      (lowerContBlock b cm cr pc spillBase ns needFrame curLbl acc d path st blk).run s0 =
        .ok (bs, s1) →
      ∃ blk0 rest bodyTail, bs = blk0 :: rest ∧ blk0.label = curLbl ∧ blk0.pad? = none ∧
        blk0.body = acc ++ bodyTail
  | .let_ _ k, l, acc, d, path, st, _, _, _, h => by
    dsimp only [lowerContBlock] at h
    obtain ⟨p', _, _, hk⟩ := lowerM_bind_ok' h
    obtain ⟨blk0, rest, tail, rfl, hlbl, hpad, hbody⟩ :=
      lowerContBlock_head_shape b cm cr pc spillBase ns needFrame k l _ _ _ _ hk
    exact ⟨blk0, rest, p'.1 ++ tail, rfl, hlbl, hpad, by simpa [List.append_assoc] using hbody⟩
  | .load t a k, l, acc, d, path, st, _, _, _, h => by
    dsimp only [lowerContBlock] at h
    cases hslot : (if cr.privFrame.numSlots > 0 && t == i64 then spSlotOf? cr.privFrame.numSlots
        (st.evalArg a) else none) with
    | some slotIdx =>
      rw [hslot] at h
      let is := emitToLoc b.w0 (locOf b spillBase d) fun rd => [.slotLd rd slotIdx]
      obtain ⟨blk0, rest, tail, rfl, hlbl, hpad, hbody⟩ :=
        lowerContBlock_head_shape b cm cr pc spillBase ns needFrame k l (acc ++ is) (d + 1) path
          _ h
      exact ⟨blk0, rest, is ++ tail, rfl, hlbl, hpad, by simpa [List.append_assoc] using hbody⟩
    | none =>
      rw [hslot] at h; dsimp only at h
      split at h
      · obtain ⟨is, _, _, hk⟩ := lowerM_bind_ok' h
        obtain ⟨blk0, rest, tail, rfl, hlbl, hpad, hbody⟩ :=
          lowerContBlock_head_shape b cm cr pc spillBase ns needFrame k l _ _ _ _ hk
        exact ⟨blk0, rest, is ++ tail, rfl, hlbl, hpad, by simpa [List.append_assoc] using hbody⟩
      · obtain ⟨cg, _, _, h2⟩ := lowerM_bind_ok' h
        obtain ⟨_, _, _, h3⟩ := lowerM_bind_ok' h2
        obtain ⟨_, _, _, h4⟩ := lowerM_bind_ok' h3
        obtain ⟨_, _, _, h5⟩ := lowerM_bind_ok' h4
        obtain ⟨_, _, _, h6⟩ := lowerM_bind_ok' h5
        obtain ⟨_, _, _, h7⟩ := lowerM_bind_ok' h6
        dsimp only [Pure.pure, StateT.pure] at h7; cases h7
        exact ⟨_, _, cg, rfl, rfl, rfl, rfl⟩
  | .store v a k, l, acc, d, path, st, _, _, _, h => by
    dsimp only [lowerContBlock] at h
    cases hslot : (if cr.privFrame.numSlots > 0 && _ == i64 then spSlotOf? cr.privFrame.numSlots
        (st.evalArg a) else none) with
    | some slotIdx =>
      rw [hslot] at h
      obtain ⟨p', _, _, hk⟩ := lowerM_bind_ok' h
      obtain ⟨blk0, rest, tail, rfl, hlbl, hpad, hbody⟩ :=
        lowerContBlock_head_shape b cm cr pc spillBase ns needFrame k l _ _ _ _ hk
      exact ⟨blk0, rest, p'.1 ++ [.slotSt slotIdx p'.2] ++ tail, rfl, hlbl, hpad,
        by simpa [List.append_assoc] using hbody⟩
    | none =>
      rw [hslot] at h; dsimp only at h
      split at h
      · obtain ⟨is, _, _, hk⟩ := lowerM_bind_ok' h
        obtain ⟨blk0, rest, tail, rfl, hlbl, hpad, hbody⟩ :=
          lowerContBlock_head_shape b cm cr pc spillBase ns needFrame k l _ _ _ _ hk
        exact ⟨blk0, rest, is ++ tail, rfl, hlbl, hpad, by simpa [List.append_assoc] using hbody⟩
      · obtain ⟨cg, _, _, h2⟩ := lowerM_bind_ok' h
        obtain ⟨_, _, _, h3⟩ := lowerM_bind_ok' h2
        obtain ⟨_, _, _, h4⟩ := lowerM_bind_ok' h3
        obtain ⟨_, _, _, h5⟩ := lowerM_bind_ok' h4
        obtain ⟨_, _, _, h6⟩ := lowerM_bind_ok' h5
        obtain ⟨_, _, _, h7⟩ := lowerM_bind_ok' h6
        dsimp only [Pure.pure, StateT.pure] at h7; cases h7
        exact ⟨_, _, cg, rfl, rfl, rfl, rfl⟩
  | .codeAddr sym k, l, acc, d, path, st, _, _, _, h => by
    dsimp only [lowerContBlock] at h
    cases hca : cm.addrOf? sym with
    | none => rw [hca] at h; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at h; cases h
    | some _ =>
      rw [hca] at h
      let is := emitToLoc b.w0 (locOf b spillBase d) fun rd => [.symAddr sym rd]
      obtain ⟨blk0, rest, tail, rfl, hlbl, hpad, hbody⟩ :=
        lowerContBlock_head_shape b cm cr pc spillBase ns needFrame k l (acc ++ is) (d + 1) path
          _ h
      exact ⟨blk0, rest, is ++ tail, rfl, hlbl, hpad, by simpa [List.append_assoc] using hbody⟩
  | .jnz _ _ _, l, acc, d, path, st, _, _, _, h => by
    dsimp only [lowerContBlock] at h
    obtain ⟨p1, _, _, h2⟩ := lowerM_bind_ok' h
    obtain ⟨_, _, _, h3⟩ := lowerM_bind_ok' h2
    obtain ⟨_, _, _, h4⟩ := lowerM_bind_ok' h3
    obtain ⟨_, _, _, h5⟩ := lowerM_bind_ok' h4
    obtain ⟨_, _, _, h6⟩ := lowerM_bind_ok' h5
    dsimp only [Pure.pure, StateT.pure] at h6; cases h6
    exact ⟨_, _, p1.1, rfl, rfl, rfl, rfl⟩
  | .ijmp tgt nxt, l, acc, d, path, st, _, _, _, h => by
    dsimp only [lowerContBlock] at h
    cases hfe : cr.toRegionWitness.findEdge pc path with
    | none => rw [hfe] at h; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at h; cases h
    | some _ =>
      rw [hfe] at h
      exact lowerContEdge_head_shape b cr spillBase ns needFrame st d l acc tgt nxt _ h
  | .halt _, l, acc, d, _, _, _, _, _, h => by
    dsimp only [lowerContBlock] at h
    obtain ⟨ccode, _, _, h2⟩ := lowerM_bind_ok' h
    cases hnf : needFrame with
    | false =>
      rw [hnf] at h2; dsimp only [Pure.pure, StateT.pure] at h2; cases h2
      exact ⟨_, _, ccode ++ emitPrivFlush b cr.privFrame.numSlots, rfl, rfl, rfl,
        by simp [regionExitSuffix, List.append_assoc]⟩
    | true =>
      rw [hnf] at h2; dsimp only [Pure.pure, StateT.pure] at h2; cases h2
      exact ⟨_, _, ccode ++ (emitPrivFlush b cr.privFrame.numSlots ++ [.epilogue ns]),
        rfl, rfl, rfl, by simp [regionExitSuffix, List.append_assoc]⟩
  | .hlt, _, _, _, _, _, _, _, _, h => by
    dsimp only [lowerContBlock, liftEx, StateT.lift, StateT.run, Except.map] at h; cases h

private def isContCallKind : EdgeKind → Bool
  | .contCall _ _ _ _ _ => true
  | _ => false

private theorem lowerContEdge_body_bwp {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {cm : CodeMap} {vcm : VllCodeMap A} (hvwf : vcm.Wf)
    {cr : ContifyRegion} {callees : List ContCalleeMeta} {pcs : List (BitVec 64)}
    {spillBase ns ns_ : Nat} {needFrame : Bool}
    {sp0 rp0 hwSp ra₀ : BitVec 64} {G : Mem 64 → Prop} {Ψ_L0 : BedrockWord.CodeSpec}
    {Ψ_L1 : Xcap.CodeSpec (MachSt A)} {H_L1 : Xcap.Halt (MachSt A)}
    (hcl : Xcap.Closed (vllXcapMach A vcm.symAddr) vcm.toXcapCode Ψ_L1 H_L1)
    (hPrivEnv : cr.privFrame.numSlots > 0 → cr.abi = .retEnvelope)
    (hsb_le : cr.privFrame.numSlots > 0 → cr.privFrame.numSlots + 1 ≤ spillBase)
    (hspill_ns : spillBase ≤ ns_)
    (hInner : ∀ (p : BitVec 64) (nxtR : Regs) (mConc mPub : Mem 64) (slots : List (BitVec 64))
      (s_t : MachSt A),
      (findLabelIdx pcs p).isSome = true → slots.length = ns_ →
      WordRegsRel b nxtR s_t → (cr.privFrame.numSlots > 0 → nxtR.sp = sp0) →
      (cr.abi.isContified = true → nxtR.rp = rp0) →
      (needFrame = false → (vllFramePreds A).raReg s_t ra₀) →
      s_t.gpr A.abi.sp = hwSp → PrivSlotsRel cr.privFrame.numSlots sp0 slots mConc mPub →
      (array64 hwSp slots ⋆ (Eq mPub ⋆ G)) s_t.mem →
      Ψ_L0 p ⟨nxtR, mConc⟩ → Ψ_L1 (vcm.symAddr (innerLabel cr p)) s_t)
    (hEndIjmp : cr.abi = .retEnvelope ∧ ((cr.privFrame.dynAliasGuard = true ∧
          cr.privFrame.numSlots > 0) ∨ ∃ ew ∈ cr.edges, match ew.kind with
        | .bailout | .guarded _ | .strideTable _ _ true => True | _ => False) →
      ∀ s_fin (tgtVal : BitVec 64) (nxt' : Regs) (m' : Mem 64)
      (slots' : List (BitVec 64)),
      slots'.length = ns_ → s_fin.gpr b.w0 = tgtVal → WordRegsRel b nxt' s_fin →
      (needFrame = false → (vllFramePreds A).raReg s_fin ra₀) →
      s_fin.gpr A.abi.sp = hwSp → (array64 hwSp slots' ⋆ (Eq m' ⋆ G)) s_fin.mem →
      Ψ_L0 tgtVal ⟨nxt', m'⟩ →
      bodyWp A vcm.symAddr (if needFrame then [.epilogue ns] else [])
        (fun s' => Ψ_L1 (s'.gpr b.w0) s') Ψ_L1 H_L1 s_fin)
    (hEndRet : ∀ dualRet (isAlt : Bool) s_fin (tgtVal : BitVec 64) (nxt' : Regs) (m' : Mem 64)
      (slots' : List (BitVec 64)),
      cr.abi = .contified dualRet → (isAlt = true → dualRet = true) →
      tgtVal = rp0 + (if isAlt then 8#64 else 0#64) → slots'.length = ns_ →
      WordRegsRel b nxt' s_fin →
      (dualRet = true → ValHolds64 .bool isAlt (s_fin.gpr b.altRet)) →
      (needFrame = false → (vllFramePreds A).raReg s_fin ra₀) →
      s_fin.gpr A.abi.sp = hwSp → (array64 hwSp slots' ⋆ (Eq m' ⋆ G)) s_fin.mem →
      Ψ_L0 tgtVal ⟨nxt', m'⟩ →
      bodyWp A vcm.symAddr (if needFrame then [.epilogue ns] else [])
        (fun s' => termWp A vcm.symAddr .ret Ψ_L1 H_L1 s') Ψ_L1 H_L1 s_fin)
    (hCall : ∀ {callee calleePc dualRet retPc altRetPc? tgtLbl}
      {nxt' : Regs} {slots' : List (BitVec 64)} {mConc' mPub' : Mem 64} {s_call : MachSt A},
      cr.abi = .retEnvelope → needFrame = true →
      (∃ ew ∈ cr.edges, ew.kind = .contCall callee calleePc dualRet retPc altRetPc?) →
      callees.any (fun c => (c.name == callee) && (c.entryPc == calleePc) &&
        (c.dualRet == dualRet)) = true →
      (cr.privFrame.numSlots > 0 → callees.any (fun c => (c.name == callee) &&
        (c.entryPc == calleePc) && c.memFree) = true) →
      cm.addrOf? callee = some calleePc → nxt'.rp = retPc →
      (if dualRet then altRetPc? = some (retPc + 8#64) else altRetPc?.isNone) →
      (findLabelIdx pcs retPc).isSome = true →
      (if dualRet then (findLabelIdx pcs (retPc + 8#64)).isSome = true else True) →
      (cr.privFrame.numSlots > 0 → nxt'.sp = sp0) →
      slots'.length = ns_ → PrivSlotsRel cr.privFrame.numSlots sp0 slots' mConc' mPub' →
      WordRegsRel b nxt' s_call → s_call.gpr A.abi.sp = hwSp →
      (array64 hwSp slots' ⋆ (Eq mPub' ⋆ G)) s_call.mem →
      Ψ_L0 calleePc ⟨nxt', mConc'⟩ →
      Xcap.cptr Ψ_L1 (vcm.symAddr tgtLbl) (fun s_ret =>
        ∃ (isAlt : Bool) (r_ret : Regs) (mConc'' mPub'' : Mem 64),
          (dualRet = false → isAlt = false) ∧
          (dualRet = true → ValHolds64 .bool isAlt (s_ret.gpr b.altRet)) ∧
          WordRegsRel b r_ret s_ret ∧
          PrivSlotsRel cr.privFrame.numSlots sp0 slots' mConc'' mPub'' ∧
          (cr.privFrame.numSlots > 0 → r_ret.sp = sp0) ∧
          (needFrame = false → (vllFramePreds A).raReg s_ret ra₀) ∧
          s_ret.gpr A.abi.sp = hwSp ∧ (array64 hwSp slots' ⋆ (Eq mPub'' ⋆ G)) s_ret.mem ∧
          Ψ_L0 (if isAlt then retPc + 8#64 else retPc) ⟨r_ret, mConc''⟩) →
      termWp A vcm.symAddr (.call callee tgtLbl) Ψ_L1 H_L1 s_call)
    (st : ContSymState) (d : Nat) (bvs : List ((t : Ty) × Val t))
    (mConc mPub : Mem 64) (slots : List (BitVec 64))
    (curLbl : Sym) (acc bodyTail : List (Instr A))
    (tgt : Arg K i64) (nxt : RegsExpr K) (tgt' : Arg Val i64) (nxt' : RegsExpr Val)
    (path : BranchPath) (kind : EdgeKind)
    {s0 s1 : Nat} {blk0 : Block A} {rest : List (Block A)} (s : MachSt A)
    (hst : ContSymStateOk bvs sp0 rp0 st)
    (he : EnvRel b spillBase d bvs s) (hlen : slots.length = ns_)
    (hslots : ∀ lvl < d, ∀ j, locOf b spillBase lvl = .slot j → j < slots.length)
    (hpriv : PrivSlotsRel cr.privFrame.numSlots sp0 slots mConc mPub)
    (hra : needFrame = false → (vllFramePreds A).raReg s ra₀)
    (hsp : s.gpr A.abi.sp = hwSp) (hm : (array64 hwSp slots ⋆ (Eq mPub ⋆ G)) s.mem)
    (htgtD : denoteArg bvs tgt = some tgt') (hnxtD : denoteRegsExpr bvs nxt = some nxt')
    (hbp : Ψ_L0 tgt'.val ⟨nxt'.eval, mConc⟩)
    (hEdge : checkContEdgeLeaf cm cr.abi cr.privFrame callees pcs ⟨path, st, tgt, nxt⟩ kind = true)
    (hEwMem_ : ∃ ew ∈ cr.edges, ew.kind = kind)
    (hKindNF : isContCallKind kind = true → needFrame = true)
    (hlo : (lowerContEdge b cr spillBase ns needFrame st d curLbl acc tgt nxt kind).run s0 =
      .ok (blk0 :: rest, s1))
    (hbody : blk0.body = acc ++ bodyTail) (hsub : ∀ blk ∈ blk0 :: rest, blk ∈ vcm.blocks) :
    bodyWp A vcm.symAddr bodyTail (termWp A vcm.symAddr blk0.term Ψ_L1 H_L1) Ψ_L1 H_L1 s := by
  have hwk := w_mem_workRegs b; have hwne := wordRegBind_work_ne hwf
  have hwsp := work_not_sp hwf; have hwnot := wordRegs_not_sp_ra hwf
  have hm' : (array64 (s.gpr A.abi.sp) slots ⋆ (Eq mPub ⋆ G)) s.mem := by simpa [hsp] using hm
  have hsb_ns : cr.privFrame.numSlots > 0 → cr.privFrame.numSlots + 1 ≤ ns_ := fun hp =>
    Nat.le_trans (hsb_le hp) hspill_ns
  have hEdgeOrig := hEdge
  dsimp only [checkContEdgeLeaf] at hEdge
  cases hs0 : checkEdgeLeaf cm cr.abi (callees.map fun c => ⟨c.name, c.entryPc, c.dualRet⟩)
      pcs ⟨path, st.toSymState, tgt, nxt⟩ kind with
  | false => cases kind <;> simp [hs0] at hEdge
  | true =>
    have hsp0_nxt : cr.privFrame.numSlots > 0 → kind ≠ .bailout → nxt'.eval.sp = sp0 := by
      intro hpos hnb
      have hpos' : (cr.privFrame.numSlots == 0) = false := beq_false_of_ne (Nat.ne_of_gt hpos)
      simp only [hs0, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hpos'] at hEdge
      have hspOk : (st.evalArg nxt.sp == .spOffset 0#64) = true := by
        cases kind with
        | direct _ | select _ _ | strideTable _ _ _ | guarded _ | contCall _ _ _ _ _ =>
          cases hchk : (st.evalArg nxt.sp == .spOffset 0#64) <;> simp [hchk] at hEdge; rfl
        | contRet _ => rw [hPrivEnv hpos] at hs0; cases hs0
        | bailout => exact absurd rfl hnb
        | memTableGuarded _ _ | memTableRo _ _ _ => cases hEdge
      exact spZero_contNxtSp hst hnxtD hspOk
    cases kind with
    | memTableGuarded _ _ | memTableRo _ _ _ => cases hEdge
    | direct targetPc =>
      dsimp only [checkEdgeLeaf] at hs0
      simp only [Bool.and_eq_true, beq_iff_eq] at hs0
      have htgtEq := contSymState_asConst_val hst htgtD hs0.1.2
      dsimp only [lowerContEdge] at hlo
      obtain ⟨cnxt, _, hN, h2⟩ := lowerM_bind_ok' hlo
      cases hN' : emitNextRegs b spillBase d nxt with
      | error _ =>
        rw [hN'] at hN; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hN; cases hN
      | ok cnxt_ =>
        rw [hN'] at hN; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hN; cases hN
        dsimp only [Pure.pure, StateT.pure] at h2; cases h2
        dsimp only at hbody
        have hTailEq : bodyTail = cnxt := List.append_cancel_left hbody.symm
        rw [hTailEq]
        refine bodyWp_imp_raReg_mono hwf (isNoRa_emitNextRegs b hN') hra
          (emitNextRegs_bodyWp hawf hwf he hnxtD hm' hslots hN' fun s1 hr1 hs1_ne hm1 =>
            And.intro hr1 (And.intro hs1_ne hm1))
          fun s1 ⟨hr1, hs1_ne, hm1⟩ hra1 => ?_
        have hsp1 : s1.gpr A.abi.sp = hwSp :=
          (hs1_ne A.abi.sp (fun hm_ => (hwnot.1 _ hm_).1 rfl) hwsp.2.2.1.symm).trans hsp
        exact termWp_jmp (hInner targetPc nxt'.eval mConc mPub slots s1 hs0.2 hlen hr1
          (fun hpos => hsp0_nxt hpos (by intro h; cases h))
          (fun hc => rpZero_contNxtRp hst hnxtD hs0.1.1 hc) hra1 hsp1 hpriv
          (by simpa [hm1, hsp] using hm) (htgtEq ▸ hbp))
    | select tPc ePc =>
      dsimp only [lowerContEdge] at hlo; dsimp only [checkEdgeLeaf] at hs0
      rw [contSymState_toSymVal_eval tgt] at hs0
      cases hevT : st.evalArg tgt <;> rw [hevT] at hs0 hlo <;>
        try (first
          | (simp at hs0; done)
          | (dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hlo; cases hlo))
      rename_i cLvl tSym eSym
      dsimp only [ContSymVal.toSymVal] at hs0
      simp only [Bool.and_eq_true, beq_iff_eq] at hs0
      have hm_ite := evalContArg_symValMatch hst htgtD; rw [hevT] at hm_ite
      obtain ⟨cVal, hcVal, hTval, hEval⟩ := hm_ite rfl
      obtain ⟨hcLt, hcGet⟩ := listGet_of_cLevelVal_bool he.1 hcVal
      obtain ⟨cnxt, _, hN, h2⟩ := lowerM_bind_ok' hlo
      cases hN' : emitNextRegs b spillBase d nxt with
      | error _ =>
        rw [hN'] at hN; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hN; cases hN
      | ok cnxt_ =>
        rw [hN'] at hN; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hN; cases hN
        dsimp only [Pure.pure, StateT.pure] at h2; cases h2
        let cc := loadLevelInto b spillBase b.w0 cLvl
        dsimp only at hbody; rw [List.append_assoc] at hbody
        have hTailEq : bodyTail = cc ++ cnxt := List.append_cancel_left hbody.symm
        rw [hTailEq]
        refine bodyWp_append cc cnxt s (bodyWp_imp_raReg_mono hwf
          (isNoRa_loadLevelInto b spillBase cLvl (work_mem_allRegs b).2.1) hra
          (loadLevelInto_bodyWp hawf hwf hwk.1 hcLt hcGet he hm'
            fun s1 hs1_ne hv1 hm1 he1 =>
              And.intro hs1_ne (And.intro hv1 (And.intro hm1 he1)))
          fun s1 ⟨hs1_ne, hv1, hm1, he1⟩ hra1 => ?_)
        have hsp1 : s1.gpr A.abi.sp = hwSp := (hs1_ne A.abi.sp hwsp.2.1.symm).trans hsp
        have hm1' : (array64 (s1.gpr A.abi.sp) slots ⋆ (Eq mPub ⋆ G)) s1.mem := by
          simpa [hsp1, hm1] using hm
        refine bodyWp_imp_raReg_mono hwf (isNoRa_emitNextRegs b hN') hra1
          (emitNextRegs_bodyWp hawf hwf he1 hnxtD hm1' hslots hN'
            fun s2 hr2 hs2_ne hm2 => And.intro hr2 (And.intro hs2_ne hm2))
          fun s2 ⟨hr2, hs2_ne, hm2⟩ hra2 => ?_
        have hsp2 : s2.gpr A.abi.sp = hwSp :=
          (hs2_ne A.abi.sp (fun hm_ => (hwnot.1 _ hm_).1 rfl) hwsp.2.2.1.symm).trans hsp1
        have hv2 : ValHolds64 .bool cVal (s2.gpr b.w0) := by
          have hw0_eq := hs2_ne b.w0 (fun hm_ => (hwnot.2 _ hm_).2.1 rfl) hwne.2.2.2.1
          simpa [hw0_eq] using hv1
        have hnz : ((s2.gpr b.w0).setWidth 8 != 0#8) = cVal := valHolds64_bool_nonzero hv2
        have hm2' : (array64 hwSp slots ⋆ (Eq mPub ⋆ G))
            (s2.setFlags (A.jnzGprFlags (s2.gpr b.w0) s2.flags)).mem := by
          simpa [hm2, hm1, hsp] using hm
        refine termWp_jnzGpr (fun htr => ?_) (fun hfl => ?_)
        · have htPc := contSymVal_asConst_of_match (hTval (hnz ▸ htr)) hs0.2.1.2
          exact hInner tPc nxt'.eval mConc mPub slots (s2.setFlags _) hs0.1.1.2 hlen
            ((wordRegsRel_setFlags _ _ _ _).mpr hr2)
            (fun hpos => hsp0_nxt hpos (by intro h; cases h))
            (fun hc => rpZero_contNxtRp hst hnxtD hs0.1.1.1 hc)
            (fun h => (raReg_setFlags A _ _ _).mpr (hra2 h)) hsp2 hpriv hm2' (htPc ▸ hbp)
        · have hePc := contSymVal_asConst_of_match (hEval (hnz ▸ hfl)) hs0.2.2
          exact hInner ePc nxt'.eval mConc mPub slots (s2.setFlags _) hs0.1.2 hlen
            ((wordRegsRel_setFlags _ _ _ _).mpr hr2)
            (fun hpos => hsp0_nxt hpos (by intro h; cases h))
            (fun hc => rpZero_contNxtRp hst hnxtD hs0.1.1.1 hc)
            (fun h => (raReg_setFlags A _ _ _).mpr (hra2 h)) hsp2 hpriv hm2' (hePc ▸ hbp)
    | strideTable basePc targets needGuard =>
      dsimp only [lowerContEdge] at hlo; dsimp only [checkEdgeLeaf] at hs0
      rw [contSymState_toSymVal_eval tgt] at hs0
      cases hevT : st.evalArg tgt <;> rw [hevT] at hs0 hlo <;>
        try (first
          | (simp at hs0; done)
          | (dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hlo; cases hlo))
      rename_i b_s idxLvl
      dsimp only [ContSymVal.toSymVal] at hs0
      simp only [Bool.and_eq_true, beq_iff_eq] at hs0
      rcases hs0 with ⟨⟨⟨hrpOk, hneEmpty⟩, hchkStride⟩, ⟨hBaseEq, _⟩, hGuardChk⟩
      subst hBaseEq
      cases hcc : b.condOfCmp? .eq with
      | none =>
        rw [hcc] at hlo; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hlo; cases hlo
      | some ccEq =>
        rw [hcc] at hlo
        have hlo' : (do
            let ctgt ← (if needGuard then liftEx (loadArgInto b spillBase d b.w0 tgt) else pure [])
            let cnxt ← liftEx (emitNextRegs b spillBase d nxt)
            lowerStrideCascade b cr cr.privFrame.numSlots ns needFrame needGuard ccEq curLbl
              (acc ++ loadLevelInto b spillBase b.w2 idxLvl ++ ctgt ++ cnxt) 0 targets).run s0 =
            .ok (blk0 :: rest, s1) := by
          cases needGuard <;> exact hlo
        obtain ⟨ctgt, s1', hT, h2⟩ := lowerM_bind_ok' hlo'
        obtain ⟨cnxt, _, hN, h3⟩ := lowerM_bind_ok' h2
        cases hN' : emitNextRegs b spillBase d nxt with
        | error _ =>
          rw [hN'] at hN; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hN; cases hN
        | ok cnxt_ =>
          rw [hN'] at hN; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hN; cases hN
          obtain ⟨_, _, tailC, hEqC, _, _, hbodyC⟩ := lowerStrideCascade_head_shape b cr
            cr.privFrame.numSlots ns needFrame needGuard ccEq targets curLbl _ 0 h3
          cases hEqC
          let cidx := loadLevelInto b spillBase b.w2 idxLvl
          simp only [List.append_assoc] at hbody hbodyC
          have hTailEq : bodyTail = cidx ++ (ctgt ++ (cnxt ++ tailC)) :=
            List.append_cancel_left (hbody.symm.trans hbodyC)
          have hm_stride := evalContArg_symValMatch hst htgtD; rw [hevT] at hm_stride
          obtain ⟨x, hxVal, hTgtStride⟩ := hm_stride rfl
          simp only [cast_eq] at hTgtStride
          obtain ⟨hxLt, hxGet⟩ := listGet_of_cLevelVal_i64 he.1 hxVal
          rw [hTailEq]
          refine bodyWp_append cidx (ctgt ++ (cnxt ++ tailC)) s
            (bodyWp_imp_raReg_mono hwf (isNoRa_loadLevelInto b spillBase idxLvl
              (work_mem_allRegs b).2.2.2) hra
              (loadLevelInto_bodyWp hawf hwf hwk.2.2 hxLt hxGet he hm'
                fun s1 hs1_ne hv1 hm1 he1 =>
                  And.intro hs1_ne (And.intro hv1 (And.intro hm1 he1)))
              fun s1 ⟨hs1_ne, hv1, hm1, he1⟩ hra1 => ?_)
          have hsp1 : s1.gpr A.abi.sp = hwSp := (hs1_ne A.abi.sp hwsp.2.2.2.symm).trans hsp
          have hx1 : s1.gpr b.w2 = x := by
            dsimp only [ValHolds64] at hv1; simpa [BitVec.setWidth_eq] using hv1.2
          have hctgt : bodyWp A vcm.symAddr ctgt (fun s2 =>
              s2.gpr b.w2 = x ∧ (needGuard = true → s2.gpr b.w0 = tgt'.val) ∧
              EnvRel b spillBase d bvs s2 ∧
              (needFrame = false → (vllFramePreds A).raReg s2 ra₀) ∧
              s2.gpr A.abi.sp = hwSp ∧
              (array64 hwSp slots ⋆ (Eq mPub ⋆ G)) s2.mem) Ψ_L1 H_L1 s1 := by
            cases ng : needGuard with
            | false =>
              rw [ng] at hT
              simp only [Bool.false_eq_true, ↓reduceIte, Pure.pure] at hT
              cases hT
              exact ⟨hx1, fun h => False.elim (Bool.false_ne_true (ng ▸ h)),
                he1, hra1, hsp1, by simpa [hsp1, hm1] using hm⟩
            | true =>
              rw [ng] at hT; simp only [↓reduceIte] at hT
              cases hT' : loadArgInto b spillBase d b.w0 tgt with
              | error _ =>
                rw [hT'] at hT; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hT
                cases hT
              | ok ctgt_ =>
                rw [hT'] at hT; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hT
                cases hT
                refine bodyWp_imp_raReg_mono hwf
                  (isNoRa_loadArgInto b (work_mem_allRegs b).2.1 hT') hra1
                  (loadArgInto_bodyWp hawf hwf hwk.1 he1 htgtD
                    (by simpa [hsp1, hm1] using hm) hT'
                    fun s2 hs2_ne hvw0 hm2 he2 =>
                      And.intro hs2_ne (And.intro hvw0 (And.intro hm2 he2)))
                  fun s2 ⟨hs2_ne, hvw0, hm2, he2⟩ hra2 => ?_
                have hsp2 : s2.gpr A.abi.sp = hwSp := (hs2_ne A.abi.sp hwsp.2.1.symm).trans hsp1
                have hw0_2 : s2.gpr b.w0 = tgt'.val := by
                  dsimp only [ValHolds64] at hvw0; simpa [BitVec.setWidth_eq] using hvw0.2
                exact ⟨(hs2_ne b.w2 hwne.2.2.2.2.1.symm).trans hx1, fun _ => hw0_2, he2, hra2,
                  hsp2, by simpa [hm2, hm1] using hm⟩
          refine bodyWp_append ctgt (cnxt ++ tailC) s1
            (bodyWp_mono (fun s2 ⟨hx2, hw0_2, he2, hra2, hsp2, hm2⟩ => ?_) hctgt)
          have hm2' : (array64 (s2.gpr A.abi.sp) slots ⋆ (Eq mPub ⋆ G)) s2.mem := by
            simpa [hsp2] using hm2
          refine bodyWp_append cnxt tailC s2
            (bodyWp_imp_raReg_mono hwf (isNoRa_emitNextRegs b hN') hra2
              (emitNextRegs_bodyWp hawf hwf he2 hnxtD hm2' hslots hN'
                fun s3 hr3 hs3_ne hm3 => And.intro hr3 (And.intro hs3_ne hm3))
              fun s3 ⟨hr3, hs3_ne, hm3⟩ hra3 => ?_)
          have hsp3 : s3.gpr A.abi.sp = hwSp :=
            (hs3_ne A.abi.sp (fun hm_ => (hwnot.1 _ hm_).1 rfl) hwsp.2.2.1.symm).trans hsp2
          have hx3 : s3.gpr b.w2 = x :=
            (hs3_ne b.w2 (fun hm_ => (hwnot.2 _ hm_).2.2.2 rfl) hwne.2.2.2.2.2.symm).trans hx2
          have hw0_3 : needGuard = true → s3.gpr b.w0 = tgt'.val := fun hng =>
            (hs3_ne b.w0 (fun hm_ => (hwnot.2 _ hm_).2.1 rfl) hwne.2.2.2.1).trans (hw0_2 hng)
          have hbdLt : needGuard = false → x.toNat < 0 + targets.length := fun hng => by
            rw [hng] at hGuardChk; simp only [Bool.false_eq_true, ↓reduceIte] at hGuardChk
            obtain ⟨x0, hx0, hult⟩ := contSymState_hasUltBound hst hGuardChk
            rw [hxVal] at hx0; cases hx0; omega
          have hbodyC' : blk0.body = (acc ++ loadLevelInto b spillBase b.w2 idxLvl ++ ctgt ++ cnxt)
              ++ tailC := by simpa [List.append_assoc] using hbodyC
          exact lowerStrideCascade_body_bwp hawf hwf hvwf hcl hcc hsb_ns hInner
            (fun hng =>
              have hEnv : cr.abi = .retEnvelope := by
                cases habi : cr.abi <;> simp_all [RegionAbi.isContified]
              hEndIjmp ⟨hEnv, Or.inr (let ⟨ew, hew, hk⟩ := hEwMem_; ⟨ew, hew, by simp [hk, hng]⟩)⟩)
            targets curLbl _ tailC 0 x nxt'.eval mConc mPub slots s3 h3 hbodyC' hsub hchkStride
            (Nat.zero_le _) hbdLt hlen hx3 (fun hng => (hw0_3 hng).trans hTgtStride) hr3
            (fun hpos => hsp0_nxt hpos (by intro h; cases h))
            (fun hc => rpZero_contNxtRp hst hnxtD hrpOk hc) hra3 hsp3 hpriv
            (by simpa [hm3] using hm2) (hTgtStride ▸ hbp)
    | contCall callee calleePc dualRet retPc altRetPc? =>
      dsimp only [lowerContEdge] at hlo
      cases habi : cr.abi <;> rw [habi] at hs0 hlo <;> dsimp only at hs0 hlo
      · have hs0Orig := hs0
        dsimp only [checkEdgeLeaf] at hs0
        simp only [Bool.and_eq_true, beq_iff_eq] at hs0
        rcases hs0 with ⟨⟨⟨⟨⟨⟨_, haddr⟩, htc⟩, hrpc⟩, hRetIn⟩, hCal⟩, hAltChk⟩
        have hCal' : callees.any (fun c => (c.name == callee) && (c.entryPc == calleePc) &&
            (c.dualRet == dualRet)) = true := by
          simpa [List.any_map] using hCal
        have hMfC : cr.privFrame.numSlots > 0 → callees.any (fun c => (c.name == callee) &&
            (c.entryPc == calleePc) && c.memFree) = true := fun hpos => by
          have hpos' : (cr.privFrame.numSlots == 0) = false := beq_false_of_ne (Nat.ne_of_gt hpos)
          dsimp only [checkContEdgeLeaf] at hEdgeOrig
          rw [habi, hs0Orig, hpos'] at hEdgeOrig
          cases hsp' : (st.evalArg nxt.sp == .spOffset 0#64) <;>
            simp only [hsp', Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
              at hEdgeOrig
          exact hEdgeOrig
        have htgtEq := contSymState_asConst_val hst htgtD htc
        have hrpEq := resolveConst_nxt_rp hst hnxtD hrpc
        have hNF : needFrame = true := hKindNF rfl
        have hEwMem : ∃ ew ∈ cr.edges,
            ew.kind = .contCall callee calleePc dualRet retPc altRetPc? := hEwMem_
        have hAltC : if dualRet then altRetPc? = some (retPc + 8#64) else altRetPc?.isNone := by
          cases dualRet
          · exact hAltChk
          · exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp hAltChk).1
        have hAltIn :
            if dualRet then (findLabelIdx pcs (retPc + 8#64)).isSome = true else True := by
          cases dualRet
          · trivial
          · exact (Bool.and_eq_true_iff.mp hAltChk).2
        obtain ⟨cnxt, _, hN, h2⟩ := lowerM_bind_ok' hlo
        cases hN' : emitNextRegs b spillBase d nxt with
        | error _ =>
          rw [hN'] at hN; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hN; cases hN
        | ok cnxt_ =>
          rw [hN'] at hN; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hN; cases hN
          cases hdual : dualRet
          · simp only [hdual, Bool.false_eq_true, ↓reduceIte] at h2
            dsimp only [Pure.pure, StateT.pure] at h2; cases h2
            dsimp only at hbody
            have hTailEq : bodyTail = cnxt := List.append_cancel_left hbody.symm
            rw [hTailEq]
            refine bodyWp_imp_raReg_mono hwf (isNoRa_emitNextRegs b hN') hra
              (emitNextRegs_bodyWp hawf hwf he hnxtD hm' hslots hN'
                fun s1 hr1 hs1_ne hm1 => And.intro hr1 (And.intro hs1_ne hm1))
              fun s1 ⟨hr1, hs1_ne, hm1⟩ _ => ?_
            have hsp1 : s1.gpr A.abi.sp = hwSp :=
              (hs1_ne A.abi.sp (fun hm_ => (hwnot.1 _ hm_).1 rfl) hwsp.2.2.1.symm).trans hsp
            refine hCall habi hNF hEwMem hCal' hMfC haddr hrpEq hAltC hRetIn hAltIn
              (fun hpos => hsp0_nxt hpos (by intro h; cases h)) hlen hpriv hr1 hsp1
              (by simpa [hm1, hsp] using hm) (htgtEq ▸ hbp) ?_
            rintro s_ret ⟨isAlt, r_ret, mConc'', mPub'', hAltF, _, hr_r, hpriv_r, hnSp_r,
              hra_r, hsp_r, hm_r, hbp_r⟩
            have hisF : isAlt = false := hAltF hdual
            rw [hisF] at hbp_r; simp only [Bool.false_eq_true, ↓reduceIte] at hbp_r
            exact hInner retPc r_ret mConc'' mPub'' slots s_ret hRetIn hlen hr_r hnSp_r
              (fun hc => by rw [habi] at hc; cases hc) hra_r hsp_r hpriv_r hm_r hbp_r
          · simp only [hdual, ↓reduceIte] at h2
            cases halt : altRetPc? with
            | none =>
              rw [halt] at h2; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at h2
              cases h2
            | some altPc =>
              rw [halt] at h2; dsimp only at h2
              obtain ⟨dispLbl, _, _, h3⟩ := lowerM_bind_ok' h2
              dsimp only [Pure.pure, StateT.pure] at h3; cases h3
              have haltEq : altPc = retPc + 8#64 := by simpa [hdual, halt] using hAltC
              subst haltEq
              have hAltIn' : (findLabelIdx pcs (retPc + 8#64)).isSome = true := by
                simpa [hdual] using hAltIn
              dsimp only at hbody
              have hTailEq : bodyTail = cnxt := List.append_cancel_left hbody.symm
              rw [hTailEq]
              refine bodyWp_imp_raReg_mono hwf (isNoRa_emitNextRegs b hN') hra
                (emitNextRegs_bodyWp hawf hwf he hnxtD hm' hslots hN'
                  fun s1 hr1 hs1_ne hm1 => And.intro hr1 (And.intro hs1_ne hm1))
                fun s1 ⟨hr1, hs1_ne, hm1⟩ _ => ?_
              have hsp1 : s1.gpr A.abi.sp = hwSp :=
                (hs1_ne A.abi.sp (fun hm_ => (hwnot.1 _ hm_).1 rfl) hwsp.2.2.1.symm).trans hsp
              refine hCall habi hNF hEwMem hCal' hMfC haddr hrpEq hAltC hRetIn hAltIn
                (fun hpos => hsp0_nxt hpos (by intro h; cases h)) hlen hpriv hr1 hsp1
                (by simpa [hm1, hsp] using hm) (htgtEq ▸ hbp) ?_
              rintro s_ret ⟨isAlt, r_ret, mConc'', mPub'', _, hAltV, hr_r, hpriv_r, hnSp_r,
                hra_r, hsp_r, hm_r, hbp_r⟩
              refine closed_bwp hvwf hcl (hsub _ (List.mem_cons_of_mem _ List.mem_cons_self)) ?_
              have hnz : ((s_ret.gpr b.altRet).setWidth 8 != 0#8) = isAlt :=
                valHolds64_bool_nonzero (hAltV hdual)
              refine termWp_jnzGpr (fun htr => ?_) (fun hfl => ?_)
              · have hisT : isAlt = true := hnz.symm.trans htr
                rw [hisT] at hbp_r; simp only [↓reduceIte] at hbp_r
                exact hInner (retPc + 8#64) r_ret mConc'' mPub'' slots (s_ret.setFlags _)
                  hAltIn' hlen ((wordRegsRel_setFlags _ _ _ _).mpr hr_r) hnSp_r
                  (fun hc => by rw [habi] at hc; cases hc)
                  (fun h => (raReg_setFlags A _ _ _).mpr (hra_r h)) hsp_r hpriv_r hm_r hbp_r
              · have hisF : isAlt = false := hnz.symm.trans hfl
                rw [hisF] at hbp_r; simp only [Bool.false_eq_true, ↓reduceIte] at hbp_r
                exact hInner retPc r_ret mConc'' mPub'' slots (s_ret.setFlags _)
                  hRetIn hlen ((wordRegsRel_setFlags _ _ _ _).mpr hr_r) hnSp_r
                  (fun hc => by rw [habi] at hc; cases hc)
                  (fun h => (raReg_setFlags A _ _ _).mpr (hra_r h)) hsp_r hpriv_r hm_r hbp_r
      · dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hlo; cases hlo
    | contRet isAlt =>
      dsimp only [lowerContEdge] at hlo
      cases habi : cr.abi <;> rw [habi] at hs0 hlo
      · cases hs0
      · rename_i dualRet
        have hnPriv0 : cr.privFrame.numSlots = 0 :=
          Decidable.byContradiction fun hne => by
            have := hPrivEnv (Nat.pos_of_ne_zero hne); rw [habi] at this; cases this
        have hPriv0 : PrivSlotsRel 0 sp0 slots mConc mPub := by simpa [hnPriv0] using hpriv
        have hmEq : mConc = mPub := privSlotsRel_zero hPriv0
        dsimp only [checkEdgeLeaf] at hs0
        simp only [Bool.and_eq_true, beq_iff_eq] at hs0
        have hisOk : isAlt = true → dualRet = true := by
          intro h; subst h
          cases dualRet
          · simp at hs0
          · rfl
        have hevEq : st.evalArg tgt = .rpOffset (if isAlt then 8#64 else 0#64) := by
          have hbe := hs0.2; rw [contSymState_toSymVal_eval tgt] at hbe
          cases hev : st.evalArg tgt <;> simp [hev, ContSymVal.toSymVal] at hbe
          cases hbe; rfl
        have hm_rp := evalContArg_symValMatch hst htgtD; rw [hevEq] at hm_rp
        have hrpTgt : tgt'.val = rp0 + (if isAlt then 8#64 else 0#64) := hm_rp rfl
        cases dualRet <;> cases isAlt
        · dsimp only at hlo
          obtain ⟨cnxt, _, hN, h2⟩ := lowerM_bind_ok' hlo
          cases hN' : emitNextRegs b spillBase d nxt with
          | error _ =>
            rw [hN'] at hN; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hN; cases hN
          | ok cnxt_ =>
            rw [hN'] at hN; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hN; cases hN
            dsimp only [Pure.pure, StateT.pure] at h2; cases h2
            dsimp only at hbody; rw [List.append_assoc] at hbody
            have hTailEq : bodyTail = cnxt ++ (if needFrame then [.epilogue ns] else []) :=
              List.append_cancel_left hbody.symm
            rw [hTailEq]
            refine bodyWp_append cnxt _ s (bodyWp_imp_raReg_mono hwf
              (isNoRa_emitNextRegs b hN') hra
              (emitNextRegs_bodyWp hawf hwf he hnxtD hm' hslots hN'
                fun s1 hr1 hs1_ne hm1 => And.intro hr1 (And.intro hs1_ne hm1))
              fun s1 ⟨hr1, hs1_ne, hm1⟩ hra1 => ?_)
            have hsp1 : s1.gpr A.abi.sp = hwSp :=
              (hs1_ne A.abi.sp (fun hm_ => (hwnot.1 _ hm_).1 rfl) hwsp.2.2.1.symm).trans hsp
            exact hEndRet false false s1 tgt'.val nxt'.eval mConc slots habi hisOk hrpTgt hlen
              hr1 (fun h => by cases h) hra1 hsp1 (by simpa [hmEq, hm1, hsp] using hm) hbp
        · dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hlo; cases hlo
        · dsimp only at hlo
          obtain ⟨cnxt, _, hN, h2⟩ := lowerM_bind_ok' hlo
          cases hN' : emitNextRegs b spillBase d nxt with
          | error _ =>
            rw [hN'] at hN; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hN; cases hN
          | ok cnxt_ =>
            rw [hN'] at hN; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hN; cases hN
            dsimp only [Pure.pure, StateT.pure] at h2; cases h2
            dsimp only at hbody; simp only [List.append_assoc] at hbody
            have hTailEq : bodyTail =
                cnxt ++ [.movi b.altRet 0#64] ++ (if needFrame then [.epilogue ns] else []) := by
              simpa [List.append_assoc] using List.append_cancel_left hbody.symm
            rw [hTailEq]; simp only [List.append_assoc]
            refine bodyWp_append cnxt _ s (bodyWp_imp_raReg_mono hwf
              (isNoRa_emitNextRegs b hN') hra
              (emitNextRegs_bodyWp hawf hwf he hnxtD hm' hslots hN'
                fun s1 hr1 hs1_ne hm1 => And.intro hr1 (And.intro hs1_ne hm1))
              fun s1 ⟨hr1, hs1_ne, hm1⟩ hra1 => ?_)
            have hsp1 : s1.gpr A.abi.sp = hwSp :=
              (hs1_ne A.abi.sp (fun hm_ => (hwnot.1 _ hm_).1 rfl) hwsp.2.2.1.symm).trans hsp
            refine instrWp_movi ?_
            let s2 := s1.setGpr b.altRet 0#64
            have hr2 : WordRegsRel b nxt'.eval s2 := wordRegsRel_updWork hwf hr1 b.altRet
              (by simp [WordRegBind.workRegs]) (fun _ hq => MachSt.gpr_setGpr_ne _ _ hq)
            have hval2 : ValHolds64 .bool false (s2.gpr b.altRet) := by
              simp [s2, ValHolds64, MachSt.gpr_setGpr_same]
            have hra2 : needFrame = false → (vllFramePreds A).raReg s2 ra₀ := fun hnf => by
              cases hk : A.abi.raKind with
              | stack => simp [vllFramePreds, hk]
              | linkReg lr =>
                have hne_lr : lr ≠ b.altRet := fun he => work_not_ra hwf |>.1 (he ▸ by
                  simp [Abi.raRegs, hk, RaKind.raRegs])
                have h0 := hra1 hnf; simp only [vllFramePreds, hk] at h0 ⊢
                exact (MachSt.gpr_setGpr_ne _ _ hne_lr).trans h0
            have hsp2 : s2.gpr A.abi.sp = hwSp :=
              (MachSt.gpr_setGpr_ne _ _ hwsp.1.symm).trans hsp1
            exact hEndRet true false s2 tgt'.val nxt'.eval mConc slots habi hisOk hrpTgt hlen hr2
              (fun _ => hval2) hra2 hsp2 (by simpa [s2, hmEq, hm1, hsp] using hm) hbp
        · dsimp only at hlo
          obtain ⟨cnxt, _, hN, h2⟩ := lowerM_bind_ok' hlo
          cases hN' : emitNextRegs b spillBase d nxt with
          | error _ =>
            rw [hN'] at hN; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hN; cases hN
          | ok cnxt_ =>
            rw [hN'] at hN; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hN; cases hN
            dsimp only [Pure.pure, StateT.pure] at h2; cases h2
            dsimp only at hbody; simp only [List.append_assoc] at hbody
            have hTailEq : bodyTail =
                cnxt ++ [.movi b.altRet 1#64] ++ (if needFrame then [.epilogue ns] else []) := by
              simpa [List.append_assoc] using List.append_cancel_left hbody.symm
            rw [hTailEq]; simp only [List.append_assoc]
            refine bodyWp_append cnxt _ s (bodyWp_imp_raReg_mono hwf
              (isNoRa_emitNextRegs b hN') hra
              (emitNextRegs_bodyWp hawf hwf he hnxtD hm' hslots hN'
                fun s1 hr1 hs1_ne hm1 => And.intro hr1 (And.intro hs1_ne hm1))
              fun s1 ⟨hr1, hs1_ne, hm1⟩ hra1 => ?_)
            have hsp1 : s1.gpr A.abi.sp = hwSp :=
              (hs1_ne A.abi.sp (fun hm_ => (hwnot.1 _ hm_).1 rfl) hwsp.2.2.1.symm).trans hsp
            refine instrWp_movi ?_
            let s2 := s1.setGpr b.altRet 1#64
            have hr2 : WordRegsRel b nxt'.eval s2 := wordRegsRel_updWork hwf hr1 b.altRet
              (by simp [WordRegBind.workRegs]) (fun _ hq => MachSt.gpr_setGpr_ne _ _ hq)
            have hval2 : ValHolds64 .bool true (s2.gpr b.altRet) := by
              simp [s2, ValHolds64, MachSt.gpr_setGpr_same]
            have hra2 : needFrame = false → (vllFramePreds A).raReg s2 ra₀ := fun hnf => by
              cases hk : A.abi.raKind with
              | stack => simp [vllFramePreds, hk]
              | linkReg lr =>
                have hne_lr : lr ≠ b.altRet := fun he => work_not_ra hwf |>.1 (he ▸ by
                  simp [Abi.raRegs, hk, RaKind.raRegs])
                have h0 := hra1 hnf; simp only [vllFramePreds, hk] at h0 ⊢
                exact (MachSt.gpr_setGpr_ne _ _ hne_lr).trans h0
            have hsp2 : s2.gpr A.abi.sp = hwSp :=
              (MachSt.gpr_setGpr_ne _ _ hwsp.1.symm).trans hsp1
            exact hEndRet true true s2 tgt'.val nxt'.eval mConc slots habi hisOk hrpTgt hlen hr2
              (fun _ => hval2) hra2 hsp2 (by simpa [s2, hmEq, hm1, hsp] using hm) hbp
    | guarded hotTargets =>
      dsimp only [lowerContEdge] at hlo
      cases habi : cr.abi <;> rw [habi] at hs0 hlo <;> dsimp only at hs0 hlo
      · dsimp only [checkEdgeLeaf] at hs0
        simp only [Bool.and_eq_true] at hs0
        have hHot : hotTargets.all (fun p => (findLabelIdx pcs p).isSome) = true := hs0.2
        cases hcc : b.condOfCmp? .eq with
        | none =>
          rw [hcc] at hlo
          dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hlo; cases hlo
        | some ccEq =>
          rw [hcc] at hlo; dsimp only at hlo
          obtain ⟨ctgt, _, hT, h2⟩ := lowerM_bind_ok' hlo
          cases hT' : loadArgInto b spillBase d b.w0 tgt with
          | error _ =>
            rw [hT'] at hT; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hT; cases hT
          | ok ctgt_ =>
            rw [hT'] at hT; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hT; cases hT
            obtain ⟨cnxt, _, hN, h3⟩ := lowerM_bind_ok' h2
            cases hN' : emitNextRegs b spillBase d nxt with
            | error _ =>
              rw [hN'] at hN; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hN
              cases hN
            | ok cnxt_ =>
              rw [hN'] at hN; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hN
              cases hN
              obtain ⟨_, _, tailG, hEqG, _, _, hbodyG⟩ := lowerGuardedTargets_head_shape b cr
                cr.privFrame.numSlots ns needFrame ccEq hotTargets curLbl _ h3
              cases hEqG
              simp only [List.append_assoc] at hbody hbodyG
              have hTailEq : bodyTail = ctgt ++ (cnxt ++ tailG) :=
                List.append_cancel_left (hbody.symm.trans hbodyG)
              rw [hTailEq]
              refine bodyWp_append ctgt (cnxt ++ tailG) s
                (bodyWp_imp_raReg_mono hwf
                  (isNoRa_loadArgInto b (work_mem_allRegs b).2.1 hT') hra
                  (loadArgInto_bodyWp hawf hwf hwk.1 he htgtD hm' hT'
                    fun s1 hs1_ne hv1 hm1 he1 =>
                      And.intro hs1_ne (And.intro hv1 (And.intro hm1 he1)))
                  fun s1 ⟨hs1_ne, hv1, hm1, he1⟩ hra1 => ?_)
              have hsp1 : s1.gpr A.abi.sp = hwSp := (hs1_ne A.abi.sp hwsp.2.1.symm).trans hsp
              have hm1' : (array64 (s1.gpr A.abi.sp) slots ⋆ (Eq mPub ⋆ G)) s1.mem := by
                simpa [hsp1, hm1] using hm
              refine bodyWp_append cnxt tailG s1
                (bodyWp_imp_raReg_mono hwf (isNoRa_emitNextRegs b hN') hra1
                  (emitNextRegs_bodyWp hawf hwf he1 hnxtD hm1' hslots hN'
                    fun s2 hr2 hs2_ne hm2 => And.intro hr2 (And.intro hs2_ne hm2))
                  fun s2 ⟨hr2, hs2_ne, hm2⟩ hra2 => ?_)
              have hsp2 : s2.gpr A.abi.sp = hwSp :=
                (hs2_ne A.abi.sp (fun hm_ => (hwnot.1 _ hm_).1 rfl) hwsp.2.2.1.symm).trans hsp1
              have hw0_2 : s2.gpr b.w0 = tgt'.val := by
                have hw0_eq := hs2_ne b.w0 (fun hm_ => (hwnot.2 _ hm_).2.1 rfl) hwne.2.2.2.1
                dsimp only [ValHolds64] at hv1
                exact hw0_eq.trans (by simpa [BitVec.setWidth_eq] using hv1.2)
              have hbodyG' : blk0.body = (acc ++ ctgt ++ cnxt) ++ tailG := by
                simpa [List.append_assoc] using hbodyG
              exact lowerGuardedTargets_body_bwp hawf hwf hvwf hcl hcc hsb_ns hInner
                  (hEndIjmp ⟨habi, Or.inr (let ⟨ew, hew, hk⟩ := hEwMem_; ⟨ew, hew, by simp [hk]⟩)⟩)
                hotTargets curLbl _ tailG nxt'.eval mConc mPub slots s2 h3 hbodyG' hsub hHot hlen
                hw0_2 hr2 (fun hpos => hsp0_nxt hpos (by intro h; cases h))
                (fun hc => by rw [habi] at hc; cases hc) hra2 hsp2 hpriv
                (by simpa [hm2, hm1, hsp] using hm) hbp
      · dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hlo; cases hlo
    | bailout =>
      dsimp only [lowerContEdge] at hlo
      cases habi : cr.abi <;> rw [habi] at hs0 hlo <;> dsimp only at hs0 hlo
      · obtain ⟨ctgt, _, hT, h2⟩ := lowerM_bind_ok' hlo
        cases hT' : loadArgInto b spillBase d b.w0 tgt with
        | error _ =>
          rw [hT'] at hT; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hT; cases hT
        | ok ctgt_ =>
          rw [hT'] at hT; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hT; cases hT
          obtain ⟨cnxt, _, hN, h3⟩ := lowerM_bind_ok' h2
          cases hN' : emitNextRegs b spillBase d nxt with
          | error _ =>
            rw [hN'] at hN; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hN; cases hN
          | ok cnxt_ =>
            rw [hN'] at hN; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hN; cases hN
            dsimp only [Pure.pure, StateT.pure] at h3; cases h3
            dsimp only at hbody
            have hTailEq : bodyTail =
                ctgt ++ cnxt ++ regionExitSuffix b cr.privFrame.numSlots ns needFrame := by
              have h := hbody.symm; simp only [List.append_assoc] at h ⊢
              exact List.append_cancel_left h
            rw [hTailEq]; simp only [List.append_assoc]
            refine bodyWp_append ctgt (cnxt ++ _) s
              (bodyWp_imp_raReg_mono hwf
                (isNoRa_loadArgInto b (work_mem_allRegs b).2.1 hT') hra
                (loadArgInto_bodyWp hawf hwf hwk.1 he htgtD hm' hT'
                  fun s1 hs1_ne hv1 hm1 he1 =>
                    And.intro hs1_ne (And.intro hv1 (And.intro hm1 he1)))
                fun s1 ⟨hs1_ne, hv1, hm1, he1⟩ hra1 => ?_)
            have hsp1 : s1.gpr A.abi.sp = hwSp := (hs1_ne A.abi.sp hwsp.2.1.symm).trans hsp
            have hm1' : (array64 (s1.gpr A.abi.sp) slots ⋆ (Eq mPub ⋆ G)) s1.mem := by
              simpa [hsp1, hm1] using hm
            refine bodyWp_append cnxt _ s1
              (bodyWp_imp_raReg_mono hwf (isNoRa_emitNextRegs b hN') hra1
                (emitNextRegs_bodyWp hawf hwf he1 hnxtD hm1' hslots hN'
                  fun s2 hr2 hs2_ne hm2 => And.intro hr2 (And.intro hs2_ne hm2))
                fun s2 ⟨hr2, hs2_ne, hm2⟩ hra2 => ?_)
            have hsp2 : s2.gpr A.abi.sp = hwSp :=
              (hs2_ne A.abi.sp (fun hm_ => (hwnot.1 _ hm_).1 rfl) hwsp.2.2.1.symm).trans hsp1
            have hw0_2 : s2.gpr b.w0 = tgt'.val := by
              have hw0_eq := hs2_ne b.w0 (fun hm_ => (hwnot.2 _ hm_).2.1 rfl) hwne.2.2.2.1
              dsimp only [ValHolds64] at hv1
              exact hw0_eq.trans (by simpa [BitVec.setWidth_eq] using hv1.2)
            refine bodyWp_mono (fun s' h => termWp_ijmp h) ?_
            exact regionExitSuffix_bodyWp hawf hwf hsb_ns hlen hw0_2 hr2 hra2 hsp2 hpriv
              (by simpa [hm2, hm1, hsp] using hm)
              fun s_fin hw0' hr' hra' hsp' hm' =>
                hEndIjmp ⟨habi, Or.inr (let ⟨ew, hew, hk⟩ := hEwMem_; ⟨ew, hew, by simp [hk]⟩)⟩
                  s_fin tgt'.val nxt'.eval mConc slots hlen hw0' hr' hra' hsp' hm' hbp
      · dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hlo; cases hlo

private theorem lowerContBlock_body_bwp {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {cm : CodeMap} {vcm : VllCodeMap A} (hvwf : vcm.Wf)
    {cr : ContifyRegion} {callees : List ContCalleeMeta} {pcs : List (BitVec 64)}
    (pc : BitVec 64) {spillBase ns ns_ dMax : Nat} {needFrame : Bool}
    {sp0 rp0 hwSp ra₀ : BitVec 64} {G : Mem 64 → Prop} {Ψ_L0 : BedrockWord.CodeSpec}
    {H_L0 : HaltPost} {Ψ_L1 : Xcap.CodeSpec (MachSt A)} {H_L1 : Xcap.Halt (MachSt A)}
    (hcl : Xcap.Closed (vllXcapMach A vcm.symAddr) vcm.toXcapCode Ψ_L1 H_L1)
    (hcmAddr : ∀ sym a, cm.addrOf? sym = some a → vcm.symAddr sym = a)
    (hPriv64 : cr.privFrame.numSlots ≤ 64)
    (hPrivEnv : cr.privFrame.numSlots > 0 → cr.abi = .retEnvelope)
    (hNeedCall : regionHasCalls cr = true → needFrame = true)
    (hsb_le : cr.privFrame.numSlots > 0 → cr.privFrame.numSlots + 1 ≤ spillBase)
    (hspills : spillBase + tempSpillCount b dMax ≤ ns_)
    (hInner : ∀ (p : BitVec 64) (nxtR : Regs) (mConc mPub : Mem 64) (slots : List (BitVec 64))
      (s_t : MachSt A),
      (findLabelIdx pcs p).isSome = true → slots.length = ns_ →
      WordRegsRel b nxtR s_t → (cr.privFrame.numSlots > 0 → nxtR.sp = sp0) →
      (cr.abi.isContified = true → nxtR.rp = rp0) →
      (needFrame = false → (vllFramePreds A).raReg s_t ra₀) →
      s_t.gpr A.abi.sp = hwSp → PrivSlotsRel cr.privFrame.numSlots sp0 slots mConc mPub →
      (array64 hwSp slots ⋆ (Eq mPub ⋆ G)) s_t.mem →
      Ψ_L0 p ⟨nxtR, mConc⟩ → Ψ_L1 (vcm.symAddr (innerLabel cr p)) s_t)
    (hEndIjmp : cr.abi = .retEnvelope ∧ ((cr.privFrame.dynAliasGuard = true ∧
          cr.privFrame.numSlots > 0) ∨ ∃ ew ∈ cr.edges, match ew.kind with
        | .bailout | .guarded _ | .strideTable _ _ true => True | _ => False) →
      ∀ s_fin (tgtVal : BitVec 64) (nxt' : Regs) (m' : Mem 64)
      (slots' : List (BitVec 64)),
      slots'.length = ns_ → s_fin.gpr b.w0 = tgtVal → WordRegsRel b nxt' s_fin →
      (needFrame = false → (vllFramePreds A).raReg s_fin ra₀) →
      s_fin.gpr A.abi.sp = hwSp → (array64 hwSp slots' ⋆ (Eq m' ⋆ G)) s_fin.mem →
      Ψ_L0 tgtVal ⟨nxt', m'⟩ →
      bodyWp A vcm.symAddr (if needFrame then [.epilogue ns] else [])
        (fun s' => Ψ_L1 (s'.gpr b.w0) s') Ψ_L1 H_L1 s_fin)
    (hEndHalt : ∀ s_fin (cVal : BitVec 64) (m' : Mem 64) (slots' : List (BitVec 64)),
      slots'.length = ns_ → s_fin.gpr b.w0 = cVal → s_fin.gpr A.abi.sp = hwSp →
      (array64 hwSp slots' ⋆ (Eq m' ⋆ G)) s_fin.mem → H_L0 cVal m' →
      bodyWp A vcm.symAddr (if needFrame then [.epilogue ns] else [])
        (fun s' => H_L1 (s'.gpr b.w0) s') Ψ_L1 H_L1 s_fin)
    (hEndRet : ∀ dualRet (isAlt : Bool) s_fin (tgtVal : BitVec 64) (nxt' : Regs) (m' : Mem 64)
      (slots' : List (BitVec 64)),
      cr.abi = .contified dualRet → (isAlt = true → dualRet = true) →
      tgtVal = rp0 + (if isAlt then 8#64 else 0#64) → slots'.length = ns_ →
      WordRegsRel b nxt' s_fin →
      (dualRet = true → ValHolds64 .bool isAlt (s_fin.gpr b.altRet)) →
      (needFrame = false → (vllFramePreds A).raReg s_fin ra₀) →
      s_fin.gpr A.abi.sp = hwSp → (array64 hwSp slots' ⋆ (Eq m' ⋆ G)) s_fin.mem →
      Ψ_L0 tgtVal ⟨nxt', m'⟩ →
      bodyWp A vcm.symAddr (if needFrame then [.epilogue ns] else [])
        (fun s' => termWp A vcm.symAddr .ret Ψ_L1 H_L1 s') Ψ_L1 H_L1 s_fin)
    (hCall : ∀ {callee calleePc dualRet retPc altRetPc? tgtLbl}
      {nxt' : Regs} {slots' : List (BitVec 64)} {mConc' mPub' : Mem 64} {s_call : MachSt A},
      cr.abi = .retEnvelope → needFrame = true →
      (∃ ew ∈ cr.edges, ew.kind = .contCall callee calleePc dualRet retPc altRetPc?) →
      callees.any (fun c => (c.name == callee) && (c.entryPc == calleePc) &&
        (c.dualRet == dualRet)) = true →
      (cr.privFrame.numSlots > 0 → callees.any (fun c => (c.name == callee) &&
        (c.entryPc == calleePc) && c.memFree) = true) →
      cm.addrOf? callee = some calleePc → nxt'.rp = retPc →
      (if dualRet then altRetPc? = some (retPc + 8#64) else altRetPc?.isNone) →
      (findLabelIdx pcs retPc).isSome = true →
      (if dualRet then (findLabelIdx pcs (retPc + 8#64)).isSome = true else True) →
      (cr.privFrame.numSlots > 0 → nxt'.sp = sp0) →
      slots'.length = ns_ → PrivSlotsRel cr.privFrame.numSlots sp0 slots' mConc' mPub' →
      WordRegsRel b nxt' s_call → s_call.gpr A.abi.sp = hwSp →
      (array64 hwSp slots' ⋆ (Eq mPub' ⋆ G)) s_call.mem →
      Ψ_L0 calleePc ⟨nxt', mConc'⟩ →
      Xcap.cptr Ψ_L1 (vcm.symAddr tgtLbl) (fun s_ret =>
        ∃ (isAlt : Bool) (r_ret : Regs) (mConc'' mPub'' : Mem 64),
          (dualRet = false → isAlt = false) ∧
          (dualRet = true → ValHolds64 .bool isAlt (s_ret.gpr b.altRet)) ∧
          WordRegsRel b r_ret s_ret ∧
          PrivSlotsRel cr.privFrame.numSlots sp0 slots' mConc'' mPub'' ∧
          (cr.privFrame.numSlots > 0 → r_ret.sp = sp0) ∧
          (needFrame = false → (vllFramePreds A).raReg s_ret ra₀) ∧
          s_ret.gpr A.abi.sp = hwSp ∧ (array64 hwSp slots' ⋆ (Eq mPub'' ⋆ G)) s_ret.mem ∧
          Ψ_L0 (if isAlt then retPc + 8#64 else retPc) ⟨r_ret, mConc''⟩) →
      termWp A vcm.symAddr (.call callee tgtLbl) Ψ_L1 H_L1 s_call) :
    ∀ (blk : BlockFlat) (curLbl : Sym) (acc bodyTail : List (Instr A)) (d : Nat)
      (path : BranchPath) (st : ContSymState)
      (bvs : List ((t : Ty) × Val t)) (rw : Regs) (mConc mPub : Mem 64)
      {s0 s1 : Nat} {blk0 : Block A} {rest : List (Block A)},
      6 ≤ d → maxBlockDepth blk d ≤ dMax →
      ContSymStateOk bvs sp0 rp0 st →
      (symEvalContBlock cm cr.privFrame blk path st).isSome = true →
      (∀ lf ∈ (symEvalContBlock cm cr.privFrame blk path st).getD [],
        ∃ ew, cr.toRegionWitness.findEdge pc lf.path = some ew ∧
          checkContEdgeLeaf cm cr.abi cr.privFrame callees pcs lf ew.kind = true) →
      (lowerContBlock b cm cr pc spillBase ns needFrame curLbl acc d path st blk).run s0 =
        .ok (blk0 :: rest, s1) →
      blk0.body = acc ++ bodyTail →
      (∀ x ∈ blk0 :: rest, x ∈ vcm.blocks) →
      blk.wp cm.symEnv Ψ_L0 H_L0 bvs mConc →
      ∀ (s : MachSt A) (slots : List (BitVec 64)),
        slots.length = ns_ → EnvRel b spillBase d bvs s → WordRegsRel b rw s →
        PrivSlotsRel cr.privFrame.numSlots sp0 slots mConc mPub →
        (needFrame = false → (vllFramePreds A).raReg s ra₀) →
        s.gpr A.abi.sp = hwSp → (array64 hwSp slots ⋆ (Eq mPub ⋆ G)) s.mem →
        bodyWp A vcm.symAddr bodyTail (termWp A vcm.symAddr blk0.term Ψ_L1 H_L1) Ψ_L1 H_L1 s
  | .let_ (ts := ts) op k, l, acc, bodyTail, d, path, st, bvs, rw, mConc, mPub,
      s0, s1, blk0, rest, h6, hdMax, hst, hSym, hLeaves, hlo, hbody, hsub, hbp,
      s, slots, hlen, he, hr, hpriv, hra, hsp, hm => by
    dsimp only [lowerContBlock] at hlo
    obtain ⟨pOp, sMid, hOp, hRest⟩ := lowerM_bind_ok' hlo
    cases hOp' : lowerOp b spillBase d op with
    | error _ =>
      rw [hOp'] at hOp; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hOp; cases hOp
    | ok pair =>
      rcases pair with ⟨is, d'⟩
      rw [hOp'] at hOp; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hOp; cases hOp
      have hdEq := lowerOp_d_eq hOp'; subst hdEq
      obtain ⟨_, _, tail', hEqC, _, _, hbody'⟩ := lowerContBlock_head_shape b cm cr pc
        spillBase ns needFrame k l (acc ++ is) (d + ts.length) path _ hRest
      cases hEqC
      have hTailEq : bodyTail = is ++ tail' :=
        List.append_cancel_left (hbody.symm.trans (by simpa [List.append_assoc] using hbody'))
      subst hTailEq
      dsimp only [BlockFlat.wp] at hbp
      cases hden : denoteArgs bvs op.args with
      | none => rw [hden] at hbp; exact False.elim hbp
      | some args' =>
        rw [hden] at hbp
        have hbp' := evalContOp_wp_mono op hst hden (fun r hk hst' => And.intro hk hst') hbp
        have hdMax' : maxBlockDepth k (d + ts.length) ≤ dMax := by simpa [maxBlockDepth] using hdMax
        have hdLt : d < dMax := by
          have hle := maxBlockDepth_le k (d + ts.length)
          have hts := lowerOp_ts_length hOp'; omega
        have hNo : ∀ i ∈ is, IsNoRaInstr b i := isNoRa_lowerOp b hOp'
        refine bodyWp_append is tail' s (bodyWp_imp_raReg_cont hwf hNo hra ?_)
        have hm' : (array64 (s.gpr A.abi.sp) slots ⋆ (Eq mPub ⋆ G)) s.mem := by simpa [hsp] using hm
        exact lowerOp_bodyWp hawf hwf hdLt h6 (by omega) he hr hm' hden hbp' hOp'
          (fun rvs s' slots' ⟨hkRes, hst'⟩ _ hlen' hsb' he' hr' hsp' hm'' => fun hra' =>
            lowerContBlock_body_bwp hawf hwf hvwf pc hcl hcmAddr hPriv64 hPrivEnv hNeedCall
              hsb_le hspills hInner hEndIjmp hEndHalt hEndRet hCall
              k l (acc ++ is) tail' (d + ts.length) path _ (pushTup rvs bvs) rw mConc mPub
              (by omega) hdMax' hst' hSym hLeaves hRest hbody' hsub hkRes s' slots'
              (hlen'.trans hlen) he' hr' (privSlotsRel_take_eq hsb_le hlen' hsb' hpriv)
              hra' (hsp'.trans hsp) (by simpa [hsp'.trans hsp] using hm''))
  | .load t a k, l, acc, bodyTail, d, path, st, bvs, rw, mConc, mPub,
      s0, s1, blk0, rest, h6, hdMax, hst, hSym, hLeaves, hlo, hbody, hsub, hbp,
      s, slots, hlen, he, hr, hpriv, hra, hsp, hm => by
    have hbpOrig := hbp
    dsimp only [BlockFlat.wp] at hbp
    cases hda : denoteArg bvs a with
    | none => rw [hda] at hbp; exact False.elim hbp
    | some aa =>
      rw [hda] at hbp; rcases hbp with ⟨v, hv, hk⟩
      have hdMax' : maxBlockDepth k (d + 1) ≤ dMax := by simpa [maxBlockDepth] using hdMax
      have hdLt : d < dMax := Nat.lt_of_lt_of_le (Nat.lt_succ_self d)
        (Nat.le_trans (maxBlockDepth_le k (d + 1)) hdMax')
      have hst' : ContSymStateOk (⟨t, v⟩ :: bvs) sp0 rp0
          { env := .top :: st.env, ctx := t :: st.ctx, facts := st.facts } :=
        contSymStateOk_cons v .top hst trivial
      have hm' : (array64 (s.gpr A.abi.sp) slots ⋆ (Eq mPub ⋆ G)) s.mem := by simpa [hsp] using hm
      dsimp only [lowerContBlock] at hlo
      cases hslot : (if cr.privFrame.numSlots > 0 && t == i64 then
          spSlotOf? cr.privFrame.numSlots (st.evalArg a) else none) with
      | some slotIdx =>
        rw [hslot] at hlo; dsimp only at hlo
        have ht64 : t = i64 := by
          by_cases h : (t == i64) = true
          · exact beq_iff_eq.mp h
          · simp [h] at hslot
        subst ht64
        have hpos : 0 < cr.privFrame.numSlots := by
          by_cases hp : cr.privFrame.numSlots > 0
          · exact hp
          · simp [hp] at hslot
        have hcond : (cr.privFrame.numSlots > 0 && i64 == i64) = true := by simp [hpos]
        rw [ite_eq_left hcond] at hslot
        obtain ⟨hslLt, hslSv⟩ := spSlotOf?_sound cr.privFrame.numSlots (st.evalArg a) slotIdx hslot
        have hokSym :
            (if (cr.privFrame.numSlots == 0) then true
             else if (i64 == i64 && (spSlotOf? cr.privFrame.numSlots (st.evalArg a)).isSome)
               then true
             else if isStaticOutsideFrame cr.privFrame.numSlots i64.bytes (st.evalArg a)
               then true
             else cr.privFrame.dynAliasGuard && decide (i64.bytes ≤ 16)) = true := by
          simp [Nat.ne_of_gt hpos, hslot]
        have hSym' : (symEvalContBlock cm cr.privFrame k path
            { env := .top :: st.env, ctx := i64 :: st.ctx, facts := st.facts }).isSome = true := by
          dsimp only [symEvalContBlock] at hSym
          rw [ite_eq_left hokSym] at hSym; exact hSym
        have hLeaves' : ∀ lf ∈ (symEvalContBlock cm cr.privFrame k path
            { env := .top :: st.env, ctx := i64 :: st.ctx, facts := st.facts }).getD [],
            ∃ ew, cr.toRegionWitness.findEdge pc lf.path = some ew ∧
              checkContEdgeLeaf cm cr.abi cr.privFrame callees pcs lf ew.kind = true := by
          dsimp only [symEvalContBlock] at hLeaves
          rw [ite_eq_left hokSym] at hLeaves; exact hLeaves
        let is := emitToLoc b.w0 (locOf b spillBase d) fun rd => [.slotLd rd slotIdx]
        obtain ⟨_, _, tail', hEqC, _, _, hbody'⟩ := lowerContBlock_head_shape b cm cr pc
          spillBase ns needFrame k l (acc ++ is) (d + 1) path _ hlo
        cases hEqC
        have hTailEq : bodyTail = is ++ tail' :=
          List.append_cancel_left (hbody.symm.trans (by simpa [List.append_assoc] using hbody'))
        rw [hTailEq]
        have haa : aa.val = slotAddr sp0 slotIdx := by
          have hm_sp := evalContArg_symValMatch hst hda; rw [hslSv] at hm_sp
          have h0 := hm_sp rfl; simp only [cast_eq] at h0
          rw [h0]; dsimp only [slotAddr]
          rw [BitVec.sub_eq_add_neg, BitVec.zero_add, ← BitVec.sub_eq_add_neg]
        have hNo : ∀ i ∈ is, IsNoRaInstr b i := isNoRa_emitToLoc b _ fun rd hrd i hi => by
          simp only [List.mem_singleton] at hi; subst hi
          rcases hrd with rfl | hl
          · exact isNoRa_slotLd b slotIdx (work_mem_allRegs b).2.1
          · exact isNoRa_slotLd b slotIdx (locOf_gpr_mem_allRegs b spillBase d hl)
        refine bodyWp_append is tail' s (bodyWp_imp_raReg_cont hwf hNo hra ?_)
        exact lowerMemLoad_priv_slot_bodyWp hwf hpos (hsb_le hpos) hdLt h6 (by omega) hslLt haa
          he hr hpriv hm' hda hv fun s' slots' hlen' hsb' hpriv' he' hr' hsp' hm'' => fun hra' =>
            lowerContBlock_body_bwp hawf hwf hvwf pc hcl hcmAddr hPriv64 hPrivEnv hNeedCall
              hsb_le hspills hInner hEndIjmp hEndHalt hEndRet hCall k l (acc ++ is) tail'
              (d + 1) path _ (⟨i64, v⟩ :: bvs) rw mConc mPub (by omega) hdMax' hst' hSym' hLeaves'
              hlo hbody' hsub hk s' slots' (hlen'.trans hlen) he' hr' hpriv' hra' (hsp'.trans hsp)
              (by simpa [hsp'.trans hsp] using hm'')
      | none =>
        rw [hslot] at hlo; dsimp only at hlo
        by_cases hStat : (cr.privFrame.numSlots == 0 ||
            isStaticOutsideFrame cr.privFrame.numSlots t.bytes (st.evalArg a)) = true
        · rw [ite_eq_left hStat] at hlo
          obtain ⟨is, sMid, hLd, hRest⟩ := lowerM_bind_ok' hlo
          cases hLd' : lowerMemLoad b spillBase d t a with
          | error _ =>
            rw [hLd'] at hLd; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hLd
            cases hLd
          | ok is_ =>
            rw [hLd'] at hLd; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hLd
            cases hLd
            have hdisj : cr.privFrame.numSlots = 0 ∨ ∀ k i j, k < cr.privFrame.numSlots →
                i < 8 → j < t.bytes → aa.val + BitVec.ofNat 64 j ≠ slotAddr sp0 k +
                BitVec.ofNat 64 i := by
              rcases Bool.or_eq_true_iff.mp hStat with h0 | hso
              · exact Or.inl (beq_iff_eq.mp h0)
              · exact Or.inr (isStaticOutsideFrame_disjoint hso (evalContArg_symValMatch hst hda))
            have hokSym : (if cr.privFrame.numSlots == 0 then true
                else if t == i64 && (spSlotOf? cr.privFrame.numSlots (st.evalArg a)).isSome
                  then true
                else if isStaticOutsideFrame cr.privFrame.numSlots t.bytes (st.evalArg a)
                  then true
                else cr.privFrame.dynAliasGuard && decide (t.bytes ≤ 16)) = true := by
              rcases Bool.or_eq_true_iff.mp hStat with h0 | hso
              · rw [ite_eq_left h0]
              · simp [hso]
            have hSym' : (symEvalContBlock cm cr.privFrame k path
                { env := .top :: st.env, ctx := t :: st.ctx, facts := st.facts }).isSome =
                true := by
              dsimp only [symEvalContBlock] at hSym
              rw [ite_eq_left hokSym] at hSym; exact hSym
            have hLeaves' : ∀ lf ∈ (symEvalContBlock cm cr.privFrame k path
                { env := .top :: st.env, ctx := t :: st.ctx, facts := st.facts }).getD [],
                ∃ ew, cr.toRegionWitness.findEdge pc lf.path = some ew ∧
                  checkContEdgeLeaf cm cr.abi cr.privFrame callees pcs lf ew.kind = true := by
              dsimp only [symEvalContBlock] at hLeaves
              rw [ite_eq_left hokSym] at hLeaves; exact hLeaves
            obtain ⟨_, _, tail', hEqC, _, _, hbody'⟩ := lowerContBlock_head_shape b cm cr pc
              spillBase ns needFrame k l (acc ++ is) (d + 1) path _ hRest
            cases hEqC
            have hTailEq : bodyTail = is ++ tail' :=
              List.append_cancel_left (hbody.symm.trans (by simpa [List.append_assoc] using hbody'))
            subst hTailEq
            have hNo : ∀ i ∈ is, IsNoRaInstr b i := isNoRa_lowerMemLoad b hLd'
            refine bodyWp_append is tail' s (bodyWp_imp_raReg_cont hwf hNo hra ?_)
            exact lowerMemLoad_priv_direct_bodyWp hwf hsb_le hdLt h6 (by omega) hdisj he hr hpriv
              hm' hda hv hLd' fun s' slots' hlen' _ hpriv' he' hr' hsp' hm'' => fun hra' =>
                lowerContBlock_body_bwp hawf hwf hvwf pc hcl hcmAddr hPriv64 hPrivEnv hNeedCall
                  hsb_le hspills hInner hEndIjmp hEndHalt hEndRet hCall k l (acc ++ is) tail'
                  (d + 1) path _ (⟨t, v⟩ :: bvs) rw mConc mPub (by omega) hdMax' hst' hSym'
                  hLeaves' hRest hbody' hsub hk s' slots' (hlen'.trans hlen) he' hr' hpriv' hra'
                  (hsp'.trans hsp) (by simpa [hsp'.trans hsp] using hm'')
        · have hStatF : (cr.privFrame.numSlots == 0 ||
              isStaticOutsideFrame cr.privFrame.numSlots t.bytes (st.evalArg a)) = false :=
            Bool.eq_false_iff.mpr hStat
          rw [ite_eq_right hStat] at hlo
          have hn0 : (cr.privFrame.numSlots == 0) = false := (Bool.or_eq_false_iff.mp hStatF).1
          have hsoF : isStaticOutsideFrame cr.privFrame.numSlots t.bytes (st.evalArg a) = false :=
            (Bool.or_eq_false_iff.mp hStatF).2
          have hpos : 0 < cr.privFrame.numSlots := Nat.pos_of_ne_zero (by simpa using hn0)
          have hSlotNone : (t == i64 && (spSlotOf? cr.privFrame.numSlots (st.evalArg a)).isSome) =
              false := by
            cases ht : t == i64
            · rfl
            · have hcond : (cr.privFrame.numSlots > 0 && t == i64) = true := by simp [hpos, ht]
              rw [ite_eq_left hcond] at hslot; simp [hslot]
          have hSymDyn : (cr.privFrame.dynAliasGuard && decide (t.bytes ≤ 16)) = true ∧
              (symEvalContBlock cm cr.privFrame k path
                { env := .top :: st.env, ctx := t :: st.ctx, facts := st.facts }).isSome =
                true := by
            dsimp only [symEvalContBlock] at hSym
            simp only [hn0, hSlotNone, hsoF, Bool.false_eq_true, ↓reduceIte] at hSym
            cases hd : cr.privFrame.dynAliasGuard && decide (t.bytes ≤ 16)
            · simp [hd] at hSym
            · simp only [hd, ↓reduceIte] at hSym; exact ⟨rfl, hSym⟩
          have hbytes16 : t.bytes ≤ 16 := of_decide_eq_true (Bool.and_eq_true_iff.mp hSymDyn.1).2
          have hLeaves' : ∀ lf ∈ (symEvalContBlock cm cr.privFrame k path
              { env := .top :: st.env, ctx := t :: st.ctx, facts := st.facts }).getD [],
              ∃ ew, cr.toRegionWitness.findEdge pc lf.path = some ew ∧
                checkContEdgeLeaf cm cr.abi cr.privFrame callees pcs lf ew.kind = true := by
            dsimp only [symEvalContBlock] at hLeaves
            simp only [hn0, hSlotNone, hsoF, Bool.false_eq_true, ↓reduceIte, hSymDyn.1] at hLeaves
            exact hLeaves
          obtain ⟨cg, _, hCg, h2⟩ := lowerM_bind_ok' hlo
          cases hCg' : emitDynAliasGuard b spillBase d cr.privFrame.numSlots t.bytes a with
          | error _ =>
            rw [hCg'] at hCg; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hCg
            cases hCg
          | ok cg_ =>
            rw [hCg'] at hCg; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hCg
            cases hCg
            obtain ⟨safeLbl, _, _, h3⟩ := lowerM_bind_ok' h2
            obtain ⟨aliasLbl, _, _, h4⟩ := lowerM_bind_ok' h3
            obtain ⟨ldSafe, _, hLdS, h5⟩ := lowerM_bind_ok' h4
            cases hLdS' : lowerMemLoad b spillBase d t a with
            | error _ =>
              rw [hLdS'] at hLdS; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hLdS
              cases hLdS
            | ok ldSafe_ =>
              rw [hLdS'] at hLdS; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hLdS
              cases hLdS
              obtain ⟨bsSafe, _, hbsSafe, h6'⟩ := lowerM_bind_ok' h5
              obtain ⟨bsAlias, _, hbsAlias, h7⟩ := lowerM_bind_ok' h6'
              dsimp only [Pure.pure, StateT.pure] at h7; cases h7
              dsimp only at hbody
              have hTailEq : bodyTail = cg := List.append_cancel_left hbody.symm
              rw [hTailEq]
              obtain ⟨_, hlenS, hsp0S⟩ := privSlotsRel_slot_sp0 hpos hpriv
              have hlenS' : cr.privFrame.numSlots + 1 ≤ slots.length := by omega
              have hNoG : ∀ i ∈ cg, IsNoRaInstr b i := isNoRa_emitDynAliasGuard b hCg'
              refine bodyWp_imp_raReg_mono hwf hNoG hra
                (emitDynAliasGuard_bodyWp hawf hwf hpos hPriv64 hbytes16 hlenS' hsp0S he hr hm'
                  hda hCg' fun ok s1 hvw0 hdisj he1 hr1 hsp1 hm1 =>
                    @Exists.intro Bool (fun b0 => ValHolds64 .bool b0 (s1.gpr b.w0) ∧
                      (b0 = true → ∀ k i j, k < cr.privFrame.numSlots → i < 8 → j < t.bytes →
                        aa.val + BitVec.ofNat 64 j ≠ slotAddr sp0 k + BitVec.ofNat 64 i) ∧
                      EnvRel b spillBase d bvs s1 ∧ WordRegsRel b rw s1 ∧
                      s1.gpr A.abi.sp = s.gpr A.abi.sp ∧ s1.mem = s.mem)
                      ok (And.intro hvw0 (And.intro hdisj
                        (And.intro he1 (And.intro hr1 (And.intro hsp1 hm1))))))
                fun s1 ⟨ok, hvw0, hdisj, he1, hr1, hsp1, hm1⟩ hra1 => ?_
              have hsp1' : s1.gpr A.abi.sp = hwSp := hsp1.trans hsp
              have hm1' : (array64 hwSp slots ⋆ (Eq mPub ⋆ G))
                  (s1.setFlags (A.jnzGprFlags (s1.gpr b.w0) s1.flags)).mem := by
                simpa [hm1, hsp] using hm'
              have hnz : ((s1.gpr b.w0).setWidth 8 != 0#8) = ok := valHolds64_bool_nonzero hvw0
              have hsubS : ∀ x ∈ bsSafe, x ∈ vcm.blocks := fun x hx =>
                hsub x (List.mem_cons_of_mem _ (List.mem_append_left _ hx))
              have hsubA : ∀ x ∈ bsAlias, x ∈ vcm.blocks := fun x hx =>
                hsub x (List.mem_cons_of_mem _ (List.mem_append_right _ hx))
              refine termWp_jnzGpr (fun htr => ?_) (fun hfl => ?_)
              · obtain ⟨blkS, restS, tailS, rfl, hlblS, _, hbodyS⟩ :=
                  lowerContBlock_head_shape b cm cr pc spillBase ns needFrame k safeLbl ldSafe
                    (d + 1) path _ hbsSafe
                refine hlblS ▸ closed_bwp hvwf hcl (hsubS blkS List.mem_cons_self) ?_
                rw [hbodyS]
                have hNoL : ∀ i ∈ ldSafe, IsNoRaInstr b i := isNoRa_lowerMemLoad b hLdS'
                refine bodyWp_append ldSafe tailS (s1.setFlags _)
                  (bodyWp_imp_raReg_cont hwf hNoL
                    (fun h => (raReg_setFlags A _ _ _).mpr (hra1 h)) ?_)
                exact lowerMemLoad_priv_direct_bodyWp hwf hsb_le hdLt h6 (by omega)
                  (Or.inr (hdisj (hnz ▸ htr))) ((envRel_setFlags _ _ _ _ _ _).mpr he1)
                  ((wordRegsRel_setFlags _ _ _ _).mpr hr1) hpriv (by simpa [hsp1'] using hm1')
                  hda hv hLdS' fun s' slots' hlen' _ hpriv' he' hr' hsp' hm'' => fun hra' =>
                    lowerContBlock_body_bwp hawf hwf hvwf pc hcl hcmAddr hPriv64 hPrivEnv hNeedCall
                      hsb_le hspills hInner hEndIjmp hEndHalt hEndRet hCall k safeLbl ldSafe tailS
                      (d + 1) path _ (⟨t, v⟩ :: bvs) rw mConc mPub (by omega) hdMax' hst'
                      hSymDyn.2 hLeaves' hbsSafe hbodyS hsubS hk s' slots'
                      (hlen'.trans hlen) he' hr' hpriv' hra' (hsp'.trans hsp1')
                      (by simpa [hsp'.trans hsp1'] using hm'')
              · refine lowerContUnpromoted_bwp hawf hwf hvwf hcl hcmAddr hspills
                  (fun s_fin tgtVal nxt' m' sl' hlen' hw0' hr' hra' hsp' hm' hpsi =>
                    hEndIjmp ⟨hPrivEnv hpos, Or.inl ⟨(Bool.and_eq_true_iff.mp hSymDyn.1).1, hpos⟩⟩
                      s_fin tgtVal nxt' m' sl' hlen' hw0' hr' hra' hsp' hm' hpsi) hEndHalt
                  (.load t a k) aliasLbl (emitPrivFlush b cr.privFrame.numSlots) d bvs rw mConc
                  (s1.setFlags _) h6 hdMax hbsAlias hsubA hbpOrig ?_
                have hNoF : ∀ i ∈ emitPrivFlush b cr.privFrame.numSlots, IsNoRaInstr b i :=
                  isNoRa_emitPrivFlush b cr.privFrame.numSlots
                refine bodyWp_imp_raReg_cont hwf hNoF
                  (fun h => (raReg_setFlags A _ _ _).mpr (hra1 h)) ?_
                exact emitPrivFlush_bodyWp hawf hwf hsb_le (fun lvl hl j hj =>
                    envRel_slots_bound b (Nat.le_of_lt hdLt) (by simpa [hlen] using hspills) lvl
                      hl j hj)
                  ((envRel_setFlags _ _ _ _ _ _).mpr he1) ((wordRegsRel_setFlags _ _ _ _).mpr hr1)
                  hpriv (by simpa [hsp1'] using hm1')
                  fun s' _ hr' he' hsp' hm'' => fun hra' =>
                    ⟨slots, hlen, he', hr', hra', hsp'.trans hsp1',
                      by simpa [hsp'.trans hsp1'] using hm''⟩
  | .store (t := t) v a k, l, acc, bodyTail, d, path, st, bvs, rw, mConc, mPub,
      s0, s1, blk0, rest, h6, hdMax, hst, hSym, hLeaves, hlo, hbody, hsub, hbp,
      s, slots, hlen, he, hr, hpriv, hra, hsp, hm => by
    have hbpOrig := hbp
    dsimp only [BlockFlat.wp] at hbp
    cases hdv : denoteArg bvs v <;> rw [hdv] at hbp; · exact False.elim hbp
    cases hda : denoteArg bvs a <;> rw [hda] at hbp; · exact False.elim hbp
    rename_i va aa; rcases hbp with ⟨hstOk, hk⟩
    have hdMax' : maxBlockDepth k d ≤ dMax := by simpa [maxBlockDepth] using hdMax
    have hdLe : d ≤ dMax := Nat.le_trans (maxBlockDepth_le k d) hdMax'
    have hm' : (array64 (s.gpr A.abi.sp) slots ⋆ (Eq mPub ⋆ G)) s.mem := by simpa [hsp] using hm
    dsimp only [lowerContBlock] at hlo
    cases hslot : (if cr.privFrame.numSlots > 0 && t == i64 then
        spSlotOf? cr.privFrame.numSlots (st.evalArg a) else none) with
    | some slotIdx =>
      rw [hslot] at hlo; dsimp only at hlo
      have ht64 : t = i64 := by
        by_cases h : (t == i64) = true
        · exact beq_iff_eq.mp h
        · simp [h] at hslot
      subst ht64
      have hpos : 0 < cr.privFrame.numSlots := by
        by_cases hp : cr.privFrame.numSlots > 0
        · exact hp
        · simp [hp] at hslot
      have hcond : (cr.privFrame.numSlots > 0 && i64 == i64) = true := by simp [hpos]
      rw [ite_eq_left hcond] at hslot
      obtain ⟨hslLt, hslSv⟩ := spSlotOf?_sound cr.privFrame.numSlots (st.evalArg a) slotIdx hslot
      have hokSym :
          (if (cr.privFrame.numSlots == 0) then true
           else if (i64 == i64 && (spSlotOf? cr.privFrame.numSlots (st.evalArg a)).isSome)
             then true
           else if isStaticOutsideFrame cr.privFrame.numSlots i64.bytes (st.evalArg a)
             then true
           else cr.privFrame.dynAliasGuard && decide (i64.bytes ≤ 16)) = true := by
        simp [Nat.ne_of_gt hpos, hslot]
      have hSym' : (symEvalContBlock cm cr.privFrame k path st).isSome = true := by
        dsimp only [symEvalContBlock] at hSym
        rw [ite_eq_left hokSym] at hSym; exact hSym
      have hLeaves' : ∀ lf ∈ (symEvalContBlock cm cr.privFrame k path st).getD [],
          ∃ ew, cr.toRegionWitness.findEdge pc lf.path = some ew ∧
            checkContEdgeLeaf cm cr.abi cr.privFrame callees pcs lf ew.kind = true := by
        dsimp only [symEvalContBlock] at hLeaves
        rw [ite_eq_left hokSym] at hLeaves; exact hLeaves
      obtain ⟨pLv, _, hLv, hRest⟩ := lowerM_bind_ok' hlo
      cases hLv' : loadArgToGpr b spillBase d b.w1 v with
      | error _ =>
        rw [hLv'] at hLv; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hLv; cases hLv
      | ok pair =>
        rcases pair with ⟨cv, rv⟩
        rw [hLv'] at hLv; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hLv; cases hLv
        obtain ⟨_, _, tail', hEqC, _, _, hbody'⟩ := lowerContBlock_head_shape b cm cr pc
          spillBase ns needFrame k l _ d path _ hRest
        cases hEqC
        have hTailEq : bodyTail = (cv ++ [.slotSt slotIdx rv]) ++ tail' :=
          List.append_cancel_left (hbody.symm.trans (by simpa [List.append_assoc] using hbody'))
        rw [hTailEq]
        have haa : aa.val = slotAddr sp0 slotIdx := by
          have hm_sp := evalContArg_symValMatch hst hda; rw [hslSv] at hm_sp
          have h0 := hm_sp rfl; simp only [cast_eq] at h0
          rw [h0]; dsimp only [slotAddr]
          rw [BitVec.sub_eq_add_neg, BitVec.zero_add, ← BitVec.sub_eq_add_neg]
        have hNo : ∀ i ∈ cv ++ [.slotSt slotIdx rv], IsNoRaInstr b i := by
          refine isNoRa_mem_append (isNoRa_loadArgToGpr b (work_mem_allRegs b).2.2.1 hLv') ?_
          intro i hi
          simp only [List.mem_singleton] at hi; subst hi; exact isNoRa_slotSt b slotIdx rv
        refine bodyWp_append (cv ++ [.slotSt slotIdx rv]) tail' s
          (bodyWp_imp_raReg_cont hwf hNo hra ?_)
        exact lowerMemStore_priv_slot_bodyWp hwf hpos (hsb_le hpos) hdLe
          (by simpa [hlen] using hspills) hslLt haa he hr hpriv hm' hdv hda hLv'
          fun s' slots' hlen' _ hpriv' he' hr' hsp' hm'' => fun hra' =>
            lowerContBlock_body_bwp hawf hwf hvwf pc hcl hcmAddr hPriv64 hPrivEnv hNeedCall
              hsb_le hspills hInner hEndIjmp hEndHalt hEndRet hCall k l _ tail' d path st bvs rw
              _ mPub h6 hdMax' hst hSym' hLeaves' hRest hbody' hsub hk s' slots' (hlen'.trans hlen)
              he' hr' hpriv' hra' (hsp'.trans hsp) (by simpa [hsp'.trans hsp] using hm'')
    | none =>
      rw [hslot] at hlo; dsimp only at hlo
      by_cases hStat : (cr.privFrame.numSlots == 0 ||
          isStaticOutsideFrame cr.privFrame.numSlots t.bytes (st.evalArg a)) = true
      · rw [ite_eq_left hStat] at hlo
        obtain ⟨is, sMid, hSt, hRest⟩ := lowerM_bind_ok' hlo
        cases hSt' : lowerMemStore b spillBase d v a with
        | error _ =>
          rw [hSt'] at hSt; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hSt
          cases hSt
        | ok is_ =>
          rw [hSt'] at hSt; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hSt
          cases hSt
          have hdisj : cr.privFrame.numSlots = 0 ∨ ∀ k i j, k < cr.privFrame.numSlots →
              i < 8 → j < t.bytes → aa.val + BitVec.ofNat 64 j ≠ slotAddr sp0 k +
              BitVec.ofNat 64 i := by
            rcases Bool.or_eq_true_iff.mp hStat with h0 | hso
            · exact Or.inl (beq_iff_eq.mp h0)
            · exact Or.inr (isStaticOutsideFrame_disjoint hso (evalContArg_symValMatch hst hda))
          have hokSym : (if cr.privFrame.numSlots == 0 then true
              else if t == i64 && (spSlotOf? cr.privFrame.numSlots (st.evalArg a)).isSome
                then true
              else if isStaticOutsideFrame cr.privFrame.numSlots t.bytes (st.evalArg a) then true
              else cr.privFrame.dynAliasGuard && decide (t.bytes ≤ 16)) = true := by
            rcases Bool.or_eq_true_iff.mp hStat with h0 | hso
            · rw [ite_eq_left h0]
            · simp [hso]
          have hSym' : (symEvalContBlock cm cr.privFrame k path st).isSome = true := by
            dsimp only [symEvalContBlock] at hSym
            rw [ite_eq_left hokSym] at hSym; exact hSym
          have hLeaves' : ∀ lf ∈ (symEvalContBlock cm cr.privFrame k path st).getD [],
              ∃ ew, cr.toRegionWitness.findEdge pc lf.path = some ew ∧
                checkContEdgeLeaf cm cr.abi cr.privFrame callees pcs lf ew.kind = true := by
            dsimp only [symEvalContBlock] at hLeaves
            rw [ite_eq_left hokSym] at hLeaves; exact hLeaves
          obtain ⟨_, _, tail', hEqC, _, _, hbody'⟩ := lowerContBlock_head_shape b cm cr pc
            spillBase ns needFrame k l (acc ++ is) d path st hRest
          cases hEqC
          have hTailEq : bodyTail = is ++ tail' :=
            List.append_cancel_left (hbody.symm.trans (by simpa [List.append_assoc] using hbody'))
          subst hTailEq
          have hNo : ∀ i ∈ is, IsNoRaInstr b i := isNoRa_lowerMemStore b hSt'
          refine bodyWp_append is tail' s (bodyWp_imp_raReg_cont hwf hNo hra ?_)
          exact lowerMemStore_priv_direct_bodyWp hwf hdLe
            (by simpa [hlen] using hspills) hdisj he hr
            hpriv hm' hdv hda hstOk hSt' fun s' hpriv' he' hr' hsp' hm'' => fun hra' =>
              lowerContBlock_body_bwp hawf hwf hvwf pc hcl hcmAddr hPriv64 hPrivEnv hNeedCall
                hsb_le hspills hInner hEndIjmp hEndHalt hEndRet hCall k l (acc ++ is) tail' d path
                st bvs rw _ _ h6 hdMax' hst hSym' hLeaves' hRest hbody' hsub hk
                s' slots hlen he' hr'
                hpriv' hra' (hsp'.trans hsp) (by simpa [hsp'.trans hsp] using hm'')
      · have hStatF : (cr.privFrame.numSlots == 0 ||
            isStaticOutsideFrame cr.privFrame.numSlots t.bytes (st.evalArg a)) = false :=
          Bool.eq_false_iff.mpr hStat
        rw [ite_eq_right hStat] at hlo
        have hn0 : (cr.privFrame.numSlots == 0) = false := (Bool.or_eq_false_iff.mp hStatF).1
        have hsoF : isStaticOutsideFrame cr.privFrame.numSlots t.bytes (st.evalArg a) = false :=
          (Bool.or_eq_false_iff.mp hStatF).2
        have hpos : 0 < cr.privFrame.numSlots := Nat.pos_of_ne_zero (by simpa using hn0)
        have hSlotNone : (t == i64 && (spSlotOf? cr.privFrame.numSlots (st.evalArg a)).isSome) =
            false := by
          cases ht : t == i64
          · rfl
          · have hcond : (cr.privFrame.numSlots > 0 && t == i64) = true := by simp [hpos, ht]
            rw [ite_eq_left hcond] at hslot; simp [hslot]
        have hSymDyn : (cr.privFrame.dynAliasGuard && decide (t.bytes ≤ 16)) = true ∧
            (symEvalContBlock cm cr.privFrame k path st).isSome = true := by
          dsimp only [symEvalContBlock] at hSym
          simp only [hn0, hSlotNone, hsoF, Bool.false_eq_true, ↓reduceIte] at hSym
          cases hd : cr.privFrame.dynAliasGuard && decide (t.bytes ≤ 16)
          · simp [hd] at hSym
          · simp only [hd, ↓reduceIte] at hSym; exact ⟨rfl, hSym⟩
        have hbytes16 : t.bytes ≤ 16 := of_decide_eq_true (Bool.and_eq_true_iff.mp hSymDyn.1).2
        have hLeaves' : ∀ lf ∈ (symEvalContBlock cm cr.privFrame k path st).getD [],
            ∃ ew, cr.toRegionWitness.findEdge pc lf.path = some ew ∧
              checkContEdgeLeaf cm cr.abi cr.privFrame callees pcs lf ew.kind = true := by
          dsimp only [symEvalContBlock] at hLeaves
          simp only [hn0, hSlotNone, hsoF, Bool.false_eq_true, ↓reduceIte, hSymDyn.1] at hLeaves
          exact hLeaves
        obtain ⟨cg, _, hCg, h2⟩ := lowerM_bind_ok' hlo
        cases hCg' : emitDynAliasGuard b spillBase d cr.privFrame.numSlots t.bytes a with
        | error _ =>
          rw [hCg'] at hCg; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hCg
          cases hCg
        | ok cg_ =>
          rw [hCg'] at hCg; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hCg
          cases hCg
          obtain ⟨safeLbl, _, _, h3⟩ := lowerM_bind_ok' h2
          obtain ⟨aliasLbl, _, _, h4⟩ := lowerM_bind_ok' h3
          obtain ⟨stSafe, _, hStS, h5⟩ := lowerM_bind_ok' h4
          cases hStS' : lowerMemStore b spillBase d v a with
          | error _ =>
            rw [hStS'] at hStS; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hStS
            cases hStS
          | ok stSafe_ =>
            rw [hStS'] at hStS; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hStS
            cases hStS
            obtain ⟨bsSafe, _, hbsSafe, h6'⟩ := lowerM_bind_ok' h5
            obtain ⟨bsAlias, _, hbsAlias, h7⟩ := lowerM_bind_ok' h6'
            dsimp only [Pure.pure, StateT.pure] at h7; cases h7
            dsimp only at hbody
            have hTailEq : bodyTail = cg := List.append_cancel_left hbody.symm
            rw [hTailEq]
            obtain ⟨_, hlenS, hsp0S⟩ := privSlotsRel_slot_sp0 hpos hpriv
            have hlenS' : cr.privFrame.numSlots + 1 ≤ slots.length := by omega
            have hNoG : ∀ i ∈ cg, IsNoRaInstr b i := isNoRa_emitDynAliasGuard b hCg'
            refine bodyWp_imp_raReg_mono hwf hNoG hra
              (emitDynAliasGuard_bodyWp hawf hwf hpos hPriv64 hbytes16 hlenS' hsp0S he hr hm' hda
                hCg' fun ok s1 hvw0 hdisj he1 hr1 hsp1 hm1 =>
                  @Exists.intro Bool (fun b0 => ValHolds64 .bool b0 (s1.gpr b.w0) ∧
                    (b0 = true → ∀ k i j, k < cr.privFrame.numSlots → i < 8 → j < t.bytes →
                      aa.val + BitVec.ofNat 64 j ≠ slotAddr sp0 k + BitVec.ofNat 64 i) ∧
                    EnvRel b spillBase d bvs s1 ∧ WordRegsRel b rw s1 ∧
                    s1.gpr A.abi.sp = s.gpr A.abi.sp ∧ s1.mem = s.mem)
                    ok (And.intro hvw0 (And.intro hdisj
                      (And.intro he1 (And.intro hr1 (And.intro hsp1 hm1))))))
              fun s1 ⟨ok, hvw0, hdisj, he1, hr1, hsp1, hm1⟩ hra1 => ?_
            have hsp1' : s1.gpr A.abi.sp = hwSp := hsp1.trans hsp
            have hm1' : (array64 hwSp slots ⋆ (Eq mPub ⋆ G))
                (s1.setFlags (A.jnzGprFlags (s1.gpr b.w0) s1.flags)).mem := by
              simpa [hm1, hsp] using hm'
            have hnz : ((s1.gpr b.w0).setWidth 8 != 0#8) = ok := valHolds64_bool_nonzero hvw0
            have hsubS : ∀ x ∈ bsSafe, x ∈ vcm.blocks := fun x hx =>
              hsub x (List.mem_cons_of_mem _ (List.mem_append_left _ hx))
            have hsubA : ∀ x ∈ bsAlias, x ∈ vcm.blocks := fun x hx =>
              hsub x (List.mem_cons_of_mem _ (List.mem_append_right _ hx))
            refine termWp_jnzGpr (fun htr => ?_) (fun hfl => ?_)
            · obtain ⟨blkS, restS, tailS, rfl, hlblS, _, hbodyS⟩ :=
                lowerContBlock_head_shape b cm cr pc spillBase ns needFrame k safeLbl stSafe d
                  path st hbsSafe
              refine hlblS ▸ closed_bwp hvwf hcl (hsubS blkS List.mem_cons_self) ?_
              rw [hbodyS]
              have hNoS : ∀ i ∈ stSafe, IsNoRaInstr b i := isNoRa_lowerMemStore b hStS'
              refine bodyWp_append stSafe tailS (s1.setFlags _)
                (bodyWp_imp_raReg_cont hwf hNoS
                  (fun h => (raReg_setFlags A _ _ _).mpr (hra1 h)) ?_)
              exact lowerMemStore_priv_direct_bodyWp hwf hdLe (by simpa [hlen] using hspills)
                (Or.inr (hdisj (hnz ▸ htr))) ((envRel_setFlags _ _ _ _ _ _).mpr he1)
                ((wordRegsRel_setFlags _ _ _ _).mpr hr1) hpriv (by simpa [hsp1'] using hm1')
                hdv hda hstOk hStS' fun s' hpriv' he' hr' hsp' hm'' => fun hra' =>
                  lowerContBlock_body_bwp hawf hwf hvwf pc hcl hcmAddr hPriv64 hPrivEnv hNeedCall
                    hsb_le hspills hInner hEndIjmp hEndHalt hEndRet hCall k safeLbl stSafe tailS
                    d path st bvs rw _ _ h6 hdMax' hst hSymDyn.2 hLeaves' hbsSafe hbodyS hsubS
                    hk s' slots hlen he' hr' hpriv' hra' (hsp'.trans hsp1')
                    (by simpa [hsp'.trans hsp1'] using hm'')
            · refine lowerContUnpromoted_bwp hawf hwf hvwf hcl hcmAddr hspills
                (fun s_fin tgtVal nxt' m' sl' hlen' hw0' hr' hra' hsp' hm' hpsi =>
                  hEndIjmp ⟨hPrivEnv hpos, Or.inl ⟨(Bool.and_eq_true_iff.mp hSymDyn.1).1, hpos⟩⟩
                    s_fin tgtVal nxt' m' sl' hlen' hw0' hr' hra' hsp' hm' hpsi) hEndHalt
                (.store v a k) aliasLbl (emitPrivFlush b cr.privFrame.numSlots) d bvs rw mConc
                (s1.setFlags _) h6 hdMax hbsAlias hsubA hbpOrig ?_
              have hNoF : ∀ i ∈ emitPrivFlush b cr.privFrame.numSlots, IsNoRaInstr b i :=
                isNoRa_emitPrivFlush b cr.privFrame.numSlots
              refine bodyWp_imp_raReg_cont hwf hNoF
                (fun h => (raReg_setFlags A _ _ _).mpr (hra1 h)) ?_
              exact emitPrivFlush_bodyWp hawf hwf hsb_le (fun lvl hl j hj =>
                  envRel_slots_bound b hdLe (by simpa [hlen] using hspills) lvl hl j hj)
                ((envRel_setFlags _ _ _ _ _ _).mpr he1) ((wordRegsRel_setFlags _ _ _ _).mpr hr1)
                hpriv (by simpa [hsp1'] using hm1')
                fun s' _ hr' he' hsp' hm'' => fun hra' =>
                  ⟨slots, hlen, he', hr', hra', hsp'.trans hsp1',
                    by simpa [hsp'.trans hsp1'] using hm''⟩
  | .codeAddr sym k, l, acc, bodyTail, d, path, st, bvs, rw, mConc, mPub,
      s0, s1, blk0, rest, h6, hdMax, hst, hSym, hLeaves, hlo, hbody, hsub, hbp,
      s, slots, hlen, he, hr, hpriv, hra, hsp, hm => by
    dsimp only [lowerContBlock] at hlo
    dsimp only [BlockFlat.wp] at hbp; rcases hbp with ⟨a, ha, hk⟩
    have ha' : cm.addrOf? sym = some a := ha
    rw [ha'] at hlo; dsimp only at hlo
    let sv := if (a &&& 7#64) == 0#64 then ContSymVal.alignedConst a else .const a
    have hsvOk : ContSymValMatch (⟨i64, a⟩ :: bvs) sp0 rp0 sv i64 a := by
      dsimp only [sv]; split
      · rename_i h0; exact fun _ => ⟨rfl, beq_iff_eq.mp h0⟩
      · exact fun _ => rfl
    have hst' := contSymStateOk_cons (t := i64) a sv hst hsvOk
    have hSym' : (symEvalContBlock cm cr.privFrame k path
        { env := sv :: st.env, ctx := i64 :: st.ctx, facts := st.facts }).isSome = true := by
      simpa [symEvalContBlock, ha', sv] using hSym
    have hLeaves' : ∀ lf ∈ (symEvalContBlock cm cr.privFrame k path
        { env := sv :: st.env, ctx := i64 :: st.ctx, facts := st.facts }).getD [],
        ∃ ew, cr.toRegionWitness.findEdge pc lf.path = some ew ∧
          checkContEdgeLeaf cm cr.abi cr.privFrame callees pcs lf ew.kind = true := by
      simpa [symEvalContBlock, ha', sv] using hLeaves
    let is := emitToLoc b.w0 (locOf b spillBase d) fun rd => [.symAddr sym rd]
    obtain ⟨_, _, tail', hEqC, _, _, hbody'⟩ := lowerContBlock_head_shape b cm cr pc
      spillBase ns needFrame k l (acc ++ is) (d + 1) path _ hlo
    cases hEqC
    have hTailEq : bodyTail = is ++ tail' :=
      List.append_cancel_left (hbody.symm.trans (by simpa [List.append_assoc] using hbody'))
    rw [hTailEq]
    have hdMax' : maxBlockDepth k (d + 1) ≤ dMax := by simpa [maxBlockDepth] using hdMax
    have hdLt : d < dMax := Nat.lt_of_lt_of_le (Nat.lt_succ_self d)
      (Nat.le_trans (maxBlockDepth_le k (d + 1)) hdMax')
    refine bodyWp_append is tail' s ?_
    have hm' : (array64 (s.gpr A.abi.sp) slots ⋆ (Eq mPub ⋆ G)) s.mem := by simpa [hsp] using hm
    exact lowerCodeAddr_bodyWp hwf hdLt h6 (by simpa [hlen] using hspills) (hcmAddr sym a ha')
      he hr hra hm' fun s' slots' hlen' hsb' he' hr' hra' hsp' hm'' =>
        lowerContBlock_body_bwp hawf hwf hvwf pc hcl hcmAddr hPriv64 hPrivEnv hNeedCall
          hsb_le hspills hInner hEndIjmp hEndHalt hEndRet hCall k l (acc ++ is) tail' (d + 1) path _
          (⟨i64, a⟩ :: bvs) rw mConc mPub (by omega) hdMax' hst' hSym' hLeaves' hlo hbody' hsub
          hk s' slots' (hlen'.trans hlen) he' hr' (privSlotsRel_take_eq hsb_le hlen' hsb' hpriv)
          hra' (hsp'.trans hsp) (by simpa [hsp'.trans hsp] using hm'')
  | .jnz c t e, l, acc, bodyTail, d, path, st, bvs, rw, mConc, mPub,
      s0, s1, blk0, rest, h6, hdMax, hst, hSym, hLeaves, hlo, hbody, hsub, hbp,
      s, slots, hlen, he, hr, hpriv, hra, hsp, hm => by
    dsimp only [lowerContBlock] at hlo
    obtain ⟨pC, _, hC, h2⟩ := lowerM_bind_ok' hlo
    cases hC' : loadArgToGpr b spillBase d b.w0 c with
    | error _ =>
      rw [hC'] at hC; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hC; cases hC
    | ok pair =>
      rcases pair with ⟨cc, rc⟩
      rw [hC'] at hC; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hC; cases hC
      obtain ⟨lT, _, _, h3⟩ := lowerM_bind_ok' h2
      obtain ⟨lF, _, _, h4⟩ := lowerM_bind_ok' h3
      obtain ⟨bsT, _, hbsT, h5⟩ := lowerM_bind_ok' h4
      obtain ⟨bsF, _, hbsF, h6'⟩ := lowerM_bind_ok' h5
      dsimp only [Pure.pure, StateT.pure] at h6'; cases h6'
      dsimp only at hbody
      have hTailEq : bodyTail = cc := List.append_cancel_left hbody.symm
      rw [hTailEq]
      dsimp only [BlockFlat.wp] at hbp
      cases hdc : denoteArg bvs c <;> rw [hdc] at hbp; · exact False.elim hbp
      rename_i c'; rcases hbp with ⟨hbt, hbf⟩
      dsimp only [symEvalContBlock, Bind.bind, Option.bind] at hSym hLeaves
      cases hST : symEvalContBlock cm cr.privFrame t (path ++ [true]) (st.pushCondFact c true) with
      | none => rw [hST] at hSym; cases hSym
      | some lts =>
        rw [hST] at hSym hLeaves
        cases hSF : symEvalContBlock cm cr.privFrame e (path ++ [false])
            (st.pushCondFact c false) with
        | none => rw [hSF] at hSym; cases hSym
        | some les =>
          rw [hSF] at hSym hLeaves; dsimp only [Option.getD] at hLeaves
          have hNo : ∀ i ∈ cc, IsNoRaInstr b i := isNoRa_loadArgToGpr b (work_mem_allRegs b).2.1 hC'
          have hdMaxT : maxBlockDepth t d ≤ dMax :=
            Nat.le_trans (Nat.le_max_left _ _) (by simpa [maxBlockDepth] using hdMax)
          have hdMaxF : maxBlockDepth e d ≤ dMax :=
            Nat.le_trans (Nat.le_max_right _ _) (by simpa [maxBlockDepth] using hdMax)
          have hsubT : ∀ x ∈ bsT, x ∈ vcm.blocks := fun x hx =>
            hsub x (List.mem_cons_of_mem _ (List.mem_append_left _ hx))
          have hsubF : ∀ x ∈ bsF, x ∈ vcm.blocks := fun x hx =>
            hsub x (List.mem_cons_of_mem _ (List.mem_append_right _ hx))
          have hm' : (array64 (s.gpr A.abi.sp) slots ⋆ (Eq mPub ⋆ G)) s.mem := by
            simpa [hsp] using hm
          refine bodyWp_imp_raReg_mono hwf hNo hra
            (loadArgToGpr_bodyWp hwf (w_mem_workRegs b).1 he hdc hm' hC'
              fun s1 hs1_ne hv1 hm1 he1 =>
                And.intro hs1_ne (And.intro hv1 (And.intro hm1 he1)))
            fun s1 ⟨hs1_ne, hv1, hm1, he1⟩ hra1 => ?_
          have hwsp := work_not_sp hwf
          have hsp1 : s1.gpr A.abi.sp = hwSp := (hs1_ne A.abi.sp hwsp.2.1.symm).trans hsp
          have hr1 := wordRegsRel_updWork hwf hr b.w0 (w_mem_workRegs b).1 hs1_ne
          have hnz : ((s1.gpr rc).setWidth 8 != 0#8) = c'.val := valHolds64_bool_nonzero hv1
          refine termWp_jnzGpr (fun htr => ?_) (fun hfl => ?_)
          · obtain ⟨blkT, restT, tailT, rfl, hlblT, _, hbodyT⟩ :=
              lowerContBlock_head_shape b cm cr pc spillBase ns needFrame t lT [] d
                (path ++ [true]) _ hbsT
            have hbwT := lowerContBlock_body_bwp hawf hwf hvwf pc hcl hcmAddr hPriv64 hPrivEnv
              hNeedCall hsb_le hspills hInner hEndIjmp hEndHalt hEndRet hCall t lT [] tailT d
              (path ++ [true]) _ bvs rw mConc mPub h6 hdMaxT
              (pushContCondFact_sound hst hdc true (hnz ▸ htr)) (by simp [hST])
              (fun lf hf => hLeaves lf (List.mem_append_left _ (by simpa [hST] using hf)))
              hbsT hbodyT hsubT (hbt (hnz ▸ htr))
              (s1.setFlags (A.jnzGprFlags (s1.gpr rc) s1.flags)) slots hlen
              ((envRel_setFlags _ _ _ _ _ _).mpr he1) ((wordRegsRel_setFlags _ _ _ _).mpr hr1) hpriv
              (fun h => (raReg_setFlags A _ _ _).mpr (hra1 h)) hsp1
              (by simpa [hsp1, hm1] using hm)
            exact hlblT ▸ closed_bwp hvwf hcl (hsubT blkT List.mem_cons_self)
              ((List.nil_append tailT ▸ hbodyT) ▸ hbwT)
          · obtain ⟨blkF, restF, tailF, rfl, hlblF, _, hbodyF⟩ :=
              lowerContBlock_head_shape b cm cr pc spillBase ns needFrame e lF [] d
                (path ++ [false]) _ hbsF
            have hbwF := lowerContBlock_body_bwp hawf hwf hvwf pc hcl hcmAddr hPriv64 hPrivEnv
              hNeedCall hsb_le hspills hInner hEndIjmp hEndHalt hEndRet hCall e lF [] tailF d
              (path ++ [false]) _ bvs rw mConc mPub h6 hdMaxF
              (pushContCondFact_sound hst hdc false (hnz ▸ hfl)) (by simp [hSF])
              (fun lf hf => hLeaves lf (List.mem_append_right _ (by simpa [hSF] using hf)))
              hbsF hbodyF hsubF (hbf (hnz ▸ hfl))
              (s1.setFlags (A.jnzGprFlags (s1.gpr rc) s1.flags)) slots hlen
              ((envRel_setFlags _ _ _ _ _ _).mpr he1) ((wordRegsRel_setFlags _ _ _ _).mpr hr1) hpriv
              (fun h => (raReg_setFlags A _ _ _).mpr (hra1 h)) hsp1
              (by simpa [hsp1, hm1] using hm)
            exact hlblF ▸ closed_bwp hvwf hcl (hsubF blkF List.mem_cons_self)
              ((List.nil_append tailF ▸ hbodyF) ▸ hbwF)
  | .ijmp tgt nxt, l, acc, bodyTail, d, path, st, bvs, rw, mConc, mPub,
      s0, s1, blk0, rest, _, hdMax, hst, _, hLeaves, hlo, hbody, hsub, hbp,
      s, slots, hlen, he, _, hpriv, hra, hsp, hm => by
    dsimp only [symEvalContBlock, Option.getD] at hLeaves
    obtain ⟨ew, hfe, hEdge⟩ := hLeaves ⟨path, st, tgt, nxt⟩ List.mem_cons_self
    dsimp only [lowerContBlock] at hlo; rw [hfe] at hlo; dsimp only at hlo
    dsimp only [BlockFlat.wp] at hbp
    cases hdt : denoteArg bvs tgt <;> rw [hdt] at hbp; · exact False.elim hbp
    cases hdn : denoteRegsExpr bvs nxt <;> rw [hdn] at hbp; · exact False.elim hbp
    rename_i tgt' nxt'
    have hEwMem_ : ∃ ew' ∈ cr.edges, ew'.kind = ew.kind :=
      ⟨ew, List.mem_of_find?_eq_some hfe, rfl⟩
    have hKindNF : isContCallKind ew.kind = true → needFrame = true := fun hm =>
      hNeedCall (List.any_eq_true.mpr ⟨ew, List.mem_of_find?_eq_some hfe, hm⟩)
    exact lowerContEdge_body_bwp hawf hwf hvwf hcl hPrivEnv hsb_le
      (Nat.le_trans (Nat.le_add_right spillBase _) hspills) hInner hEndIjmp hEndRet hCall
      st d bvs mConc mPub slots l acc bodyTail tgt nxt tgt' nxt' path ew.kind s hst he hlen
      (envRel_slots_bound b (by simpa [maxBlockDepth] using hdMax) (by simpa [hlen] using hspills))
      hpriv hra hsp hm hdt hdn hbp hEdge hEwMem_ hKindNF hlo hbody hsub
  | .halt code, l, acc, bodyTail, d, path, st, bvs, rw, mConc, mPub,
      s0, s1, blk0, rest, _, _, _, _, _, hlo, hbody, _, hbp,
      s, slots, hlen, he, hr, hpriv, hra, hsp, hm => by
    dsimp only [lowerContBlock] at hlo
    obtain ⟨ccode, _, hC, h2⟩ := lowerM_bind_ok' hlo
    cases hC' : loadArgInto b spillBase d b.w0 code with
    | error _ =>
      rw [hC'] at hC; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hC; cases hC
    | ok ccode_ =>
      rw [hC'] at hC; dsimp only [liftEx, StateT.lift, StateT.run, Except.map] at hC; cases hC
      dsimp only [Pure.pure, StateT.pure] at h2; cases h2
      dsimp only at hbody
      have hTailEq : bodyTail =
          ccode ++ regionExitSuffix b cr.privFrame.numSlots ns needFrame := by
        have h := hbody.symm; simp only [List.append_assoc] at h
        exact List.append_cancel_left h
      rw [hTailEq]
      dsimp only [BlockFlat.wp] at hbp
      cases hdc : denoteArg bvs code <;> rw [hdc] at hbp; · exact False.elim hbp
      rename_i c'
      have hNo : ∀ i ∈ ccode, IsNoRaInstr b i := isNoRa_loadArgInto b (work_mem_allRegs b).2.1 hC'
      have hm' : (array64 (s.gpr A.abi.sp) slots ⋆ (Eq mPub ⋆ G)) s.mem := by simpa [hsp] using hm
      refine bodyWp_append ccode _ s (bodyWp_imp_raReg_mono hwf hNo hra
        (loadArgInto_bodyWp hawf hwf (w_mem_workRegs b).1 he hdc hm' hC'
          fun s1 hs1_ne hv1 hm1 _ => And.intro hs1_ne (And.intro hv1 hm1))
        fun s1 ⟨hs1_ne, hv1, hm1⟩ hra1 => ?_)
      have hwsp := work_not_sp hwf
      have hsp1 : s1.gpr A.abi.sp = hwSp := (hs1_ne A.abi.sp hwsp.2.1.symm).trans hsp
      have hw0_1 : s1.gpr b.w0 = c'.val := by
        dsimp only [ValHolds64] at hv1; simpa [BitVec.setWidth_eq] using hv1.2
      have hr1 := wordRegsRel_updWork hwf hr b.w0 (w_mem_workRegs b).1 hs1_ne
      refine bodyWp_mono (fun s' h => termWp_halt h) ?_
      exact regionExitSuffix_bodyWp hawf hwf
        (fun hpos => Nat.le_trans (hsb_le hpos)
          (Nat.le_trans (Nat.le_add_right _ _) (by simpa [hlen] using hspills)))
        hlen hw0_1 hr1 hra1 hsp1 hpriv (by simpa [hm1, hsp] using hm)
        fun s_fin _ _ _ hsp' hm'' => hEndHalt s_fin c'.val mConc slots hlen ‹_› hsp' hm'' hbp
  | .hlt, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      hlo, _, _, _, _, _, _, _, _, _, _, _, _ => by
    dsimp only [lowerContBlock, liftEx, StateT.lift, StateT.run, Except.map] at hlo; cases hlo

theorem lowerContBlock_bwp {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {cm : CodeMap} {vcm : VllCodeMap A} (hvwf : vcm.Wf)
    {cr : ContifyRegion} {callees : List ContCalleeMeta} {pcs : List (BitVec 64)}
    (pc : BitVec 64) {spillBase ns ns_ dMax : Nat} {needFrame : Bool}
    {sp0 rp0 hwSp ra₀ : BitVec 64} {G : Mem 64 → Prop} {Ψ_L0 : BedrockWord.CodeSpec}
    {H_L0 : HaltPost} {Ψ_L1 : Xcap.CodeSpec (MachSt A)} {H_L1 : Xcap.Halt (MachSt A)}
    (hcl : Xcap.Closed (vllXcapMach A vcm.symAddr) vcm.toXcapCode Ψ_L1 H_L1)
    (hcmAddr : ∀ sym a, cm.addrOf? sym = some a → vcm.symAddr sym = a)
    (hPriv64 : cr.privFrame.numSlots ≤ 64)
    (hPrivEnv : cr.privFrame.numSlots > 0 → cr.abi = .retEnvelope)
    (hNeedCall : regionHasCalls cr = true → needFrame = true)
    (hsb_le : cr.privFrame.numSlots > 0 → cr.privFrame.numSlots + 1 ≤ spillBase)
    (hspills : spillBase + tempSpillCount b dMax ≤ ns_)
    (hInner : ∀ (p : BitVec 64) (nxtR : Regs) (mConc mPub : Mem 64) (slots : List (BitVec 64))
      (s_t : MachSt A),
      (findLabelIdx pcs p).isSome = true → slots.length = ns_ →
      WordRegsRel b nxtR s_t → (cr.privFrame.numSlots > 0 → nxtR.sp = sp0) →
      (cr.abi.isContified = true → nxtR.rp = rp0) →
      (needFrame = false → (vllFramePreds A).raReg s_t ra₀) →
      s_t.gpr A.abi.sp = hwSp → Stage1PrivSlots cr.privFrame.numSlots sp0 slots mConc mPub →
      (array64 hwSp slots ⋆ (Eq mPub ⋆ G)) s_t.mem →
      Ψ_L0 p ⟨nxtR, mConc⟩ → Ψ_L1 (vcm.symAddr (innerLabel cr p)) s_t)
    (hEndIjmp : cr.abi = .retEnvelope ∧ ((cr.privFrame.dynAliasGuard = true ∧
          cr.privFrame.numSlots > 0) ∨ ∃ ew ∈ cr.edges, match ew.kind with
        | .bailout | .guarded _ | .strideTable _ _ true => True | _ => False) →
      ∀ s_fin (tgtVal : BitVec 64) (nxt' : Regs) (m' : Mem 64)
      (slots' : List (BitVec 64)),
      slots'.length = ns_ → s_fin.gpr b.w0 = tgtVal → WordRegsRel b nxt' s_fin →
      (needFrame = false → (vllFramePreds A).raReg s_fin ra₀) →
      s_fin.gpr A.abi.sp = hwSp → (array64 hwSp slots' ⋆ (Eq m' ⋆ G)) s_fin.mem →
      Ψ_L0 tgtVal ⟨nxt', m'⟩ →
      bodyWp A vcm.symAddr (if needFrame then [.epilogue ns] else [])
        (fun s' => Ψ_L1 (s'.gpr b.w0) s') Ψ_L1 H_L1 s_fin)
    (hEndHalt : ∀ s_fin (cVal : BitVec 64) (m' : Mem 64) (slots' : List (BitVec 64)),
      slots'.length = ns_ → s_fin.gpr b.w0 = cVal → s_fin.gpr A.abi.sp = hwSp →
      (array64 hwSp slots' ⋆ (Eq m' ⋆ G)) s_fin.mem → H_L0 cVal m' →
      bodyWp A vcm.symAddr (if needFrame then [.epilogue ns] else [])
        (fun s' => H_L1 (s'.gpr b.w0) s') Ψ_L1 H_L1 s_fin)
    (hEndRet : ∀ dualRet (isAlt : Bool) s_fin (tgtVal : BitVec 64) (nxt' : Regs) (m' : Mem 64)
      (slots' : List (BitVec 64)),
      cr.abi = .contified dualRet → (isAlt = true → dualRet = true) →
      tgtVal = rp0 + (if isAlt then 8#64 else 0#64) → slots'.length = ns_ →
      WordRegsRel b nxt' s_fin →
      (dualRet = true → ValHolds64 .bool isAlt (s_fin.gpr b.altRet)) →
      (needFrame = false → (vllFramePreds A).raReg s_fin ra₀) →
      s_fin.gpr A.abi.sp = hwSp → (array64 hwSp slots' ⋆ (Eq m' ⋆ G)) s_fin.mem →
      Ψ_L0 tgtVal ⟨nxt', m'⟩ →
      bodyWp A vcm.symAddr (if needFrame then [.epilogue ns] else [])
        (fun s' => termWp A vcm.symAddr .ret Ψ_L1 H_L1 s') Ψ_L1 H_L1 s_fin)
    (hCall : ∀ {callee calleePc dualRet retPc altRetPc? tgtLbl}
      {nxt' : Regs} {slots' : List (BitVec 64)} {mConc' mPub' : Mem 64} {s_call : MachSt A},
      cr.abi = .retEnvelope → needFrame = true →
      (∃ ew ∈ cr.edges, ew.kind = .contCall callee calleePc dualRet retPc altRetPc?) →
      callees.any (fun c => (c.name == callee) && (c.entryPc == calleePc) &&
        (c.dualRet == dualRet)) = true →
      (cr.privFrame.numSlots > 0 → callees.any (fun c => (c.name == callee) &&
        (c.entryPc == calleePc) && c.memFree) = true) →
      cm.addrOf? callee = some calleePc → nxt'.rp = retPc →
      (if dualRet then altRetPc? = some (retPc + 8#64) else altRetPc?.isNone) →
      (findLabelIdx pcs retPc).isSome = true →
      (if dualRet then (findLabelIdx pcs (retPc + 8#64)).isSome = true else True) →
      (cr.privFrame.numSlots > 0 → nxt'.sp = sp0) →
      slots'.length = ns_ → Stage1PrivSlots cr.privFrame.numSlots sp0 slots' mConc' mPub' →
      WordRegsRel b nxt' s_call → s_call.gpr A.abi.sp = hwSp →
      (array64 hwSp slots' ⋆ (Eq mPub' ⋆ G)) s_call.mem →
      Ψ_L0 calleePc ⟨nxt', mConc'⟩ →
      Xcap.cptr Ψ_L1 (vcm.symAddr tgtLbl) (fun s_ret =>
        ∃ (isAlt : Bool) (r_ret : Regs) (mConc'' mPub'' : Mem 64),
          (dualRet = false → isAlt = false) ∧
          (dualRet = true → ValHolds64 .bool isAlt (s_ret.gpr b.altRet)) ∧
          WordRegsRel b r_ret s_ret ∧
          Stage1PrivSlots cr.privFrame.numSlots sp0 slots' mConc'' mPub'' ∧
          (cr.privFrame.numSlots > 0 → r_ret.sp = sp0) ∧
          (needFrame = false → (vllFramePreds A).raReg s_ret ra₀) ∧
          s_ret.gpr A.abi.sp = hwSp ∧ (array64 hwSp slots' ⋆ (Eq mPub'' ⋆ G)) s_ret.mem ∧
          Ψ_L0 (if isAlt then retPc + 8#64 else retPc) ⟨r_ret, mConc''⟩) →
      termWp A vcm.symAddr (.call callee tgtLbl) Ψ_L1 H_L1 s_call)
    (blk : BlockFlat) (curLbl : Sym) (acc : List (Instr A))
    (rw : Regs) (mConc mPub : Mem 64)
    {s0 s1 : Nat} {bs : List (Block A)} (s_entry : MachSt A)
    (hdMax : maxBlockDepth blk 6 ≤ dMax)
    (hsp0 : cr.privFrame.numSlots > 0 → rw.sp = sp0)
    (hrp0 : cr.abi.isContified = true → rw.rp = rp0)
    (hSym : (symEvalContBlock cm cr.privFrame blk [] ContSymState.init).isSome = true)
    (hLeaves : ∀ lf ∈ (symEvalContBlock cm cr.privFrame blk [] ContSymState.init).getD [],
      ∃ ew, cr.toRegionWitness.findEdge pc lf.path = some ew ∧
        checkContEdgeLeaf cm cr.abi cr.privFrame callees pcs lf ew.kind = true)
    (hlo : (lowerContBlock b cm cr pc spillBase ns needFrame curLbl acc 6 []
      ContSymState.init blk).run s0 = .ok (bs, s1))
    (hsub : ∀ x ∈ bs, x ∈ vcm.blocks)
    (hbp : blk.wp cm.symEnv Ψ_L0 H_L0 (pushRegsV rw.toRegsV) mConc)
    (hacc : bodyWp A vcm.symAddr acc (fun s => ∃ slots : List (BitVec 64),
      slots.length = ns_ ∧ EnvRel b spillBase 6 (pushRegsV rw.toRegsV) s ∧ WordRegsRel b rw s ∧
      Stage1PrivSlots cr.privFrame.numSlots sp0 slots mConc mPub ∧
      (needFrame = false → (vllFramePreds A).raReg s ra₀) ∧
      s.gpr A.abi.sp = hwSp ∧ (array64 hwSp slots ⋆ (Eq mPub ⋆ G)) s.mem) Ψ_L1 H_L1 s_entry) :
    Ψ_L1 (vcm.symAddr curLbl) s_entry := by
  let sp0' : BitVec 64 := if cr.privFrame.numSlots > 0 then sp0 else rw.sp
  let rp0' : BitVec 64 := if cr.abi.isContified then rp0 else rw.rp
  have hsp0' : rw.sp = sp0' := by
    by_cases hp : cr.privFrame.numSlots > 0
    · simp [sp0', hp, hsp0 hp]
    · simp [sp0', hp]
  have hrp0' : rw.rp = rp0' := by
    by_cases hc : cr.abi.isContified = true
    · simp [rp0', hc, hrp0 hc]
    · simp [rp0', hc]
  have hpriv_if : ∀ slots m1 m2,
      PrivSlotsRel cr.privFrame.numSlots sp0' slots m1 m2 ↔
      Stage1PrivSlots cr.privFrame.numSlots sp0 slots m1 m2 := fun slots m1 m2 => by
    by_cases hp : 0 < cr.privFrame.numSlots
    · have hspEq : sp0' = sp0 := ite_eq_left hp
      rw [hspEq, stage1PrivSlots_iff]
    · have h0 : cr.privFrame.numSlots = 0 := Nat.eq_zero_of_not_pos hp
      rw [h0, ← stage1PrivSlots_iff]; simp [Stage1PrivSlots]
  obtain ⟨blk0, rest, bodyTail, rfl, hlbl, _, hbody⟩ :=
    lowerContBlock_head_shape b cm cr pc spillBase ns needFrame blk curLbl acc 6 []
      ContSymState.init hlo
  refine hlbl ▸ closed_bwp hvwf hcl (hsub blk0 List.mem_cons_self) ?_
  rw [hbody]
  refine bodyWp_append acc bodyTail s_entry (bodyWp_mono (fun s hs => ?_) hacc)
  rcases hs with ⟨slots, hlen, he, hr, hpriv, hra, hsp, hm⟩
  have hst : ContSymStateOk (pushRegsV rw.toRegsV) sp0' rp0' ContSymState.init := by
    rw [← hsp0', ← hrp0']; exact contSymStateOk_init rw
  have hsp0'Eq : cr.privFrame.numSlots > 0 → sp0' = sp0 := fun hp => by
    dsimp only [sp0']; exact ite_eq_left hp
  have hrp0'Eq : cr.abi.isContified = true → rp0' = rp0 := fun hc => by
    dsimp only [rp0']; exact ite_eq_left hc
  exact lowerContBlock_body_bwp hawf hwf hvwf pc hcl hcmAddr (sp0 := sp0') (rp0 := rp0')
    hPriv64 hPrivEnv hNeedCall hsb_le hspills
    (fun p nxtR mC mP sl s_t hp hl hr' hns hnr hra' hsp' hpr hm' hbp' =>
      hInner p nxtR mC mP sl s_t hp hl hr' (fun h => (hns h).trans (hsp0'Eq h))
        (fun h => (hnr h).trans (hrp0'Eq h)) hra' hsp' ((hpriv_if sl mC mP).mp hpr) hm' hbp')
    hEndIjmp hEndHalt
    (fun dual isAlt s_f tgtV nxt' m' sl' habi haok htgt hl hr' halt hra' hsp' hm' hbp' =>
      have hrpEq : rp0' = rp0 := by
        dsimp only [rp0']; rw [habi]; simp [RegionAbi.isContified]
      hEndRet dual isAlt s_f tgtV nxt' m' sl' habi haok (hrpEq ▸ htgt) hl hr' halt hra' hsp'
        hm' hbp')
    (fun hEnv hNF hEw hCal hMf hAd hRp hAlt hRI hAI hSp hl hPr hr' hsp' hm' hbp' hCont =>
      hCall hEnv hNF hEw hCal hMf hAd hRp hAlt hRI hAI (fun h => (hSp h).trans (hsp0'Eq h))
        hl ((hpriv_if _ _ _).mp hPr) hr' hsp' hm' hbp' (fun s_ret h => by
          rcases h with ⟨iA, rR, mC'', mP'', h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
          exact hCont s_ret ⟨iA, rR, mC'', mP'', h1, h2, h3, (hpriv_if _ _ _).mpr h4,
            fun hp => (h5 hp).trans (hsp0'Eq hp).symm, h6, h7, h8, h9⟩))
    blk curLbl acc bodyTail 6 [] ContSymState.init (pushRegsV rw.toRegsV) rw mConc mPub
    (Nat.le_refl 6) hdMax hst hSym hLeaves hlo hbody hsub hbp s slots hlen he hr
    ((hpriv_if slots mConc mPub).mpr hpriv) hra hsp hm

end LeanQbe.T.Vll
