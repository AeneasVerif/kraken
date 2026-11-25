module

public import LeanQbe.T.Unified.CfgContifyProofPrefix
public import LeanQbe.T.Unified.CfgContify
public import LeanQbe.T.Unified.CfgContifyLemmas
public import LeanQbe.T.Unified.CfgRecoveryLemmas
public import LeanQbe.T.BedrockWord.Exec
public import LeanQbe.T.Unified.DriverLemmas
import LeanQbe.T.WPLemmas
import LeanQbe.T.MainLemmas
import LeanQbe.T.GroupLfpLemmas
import LeanQbe.T.FlatLemmas
import LeanQbe.T.OpsLemmas

/-!
# Soundness Proofs for Stage-1 CFG Recovery, Contification & Private Frame Promotion
(`Unified.CfgContifyProof`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Unified

open LeanQbe.T
open LeanQbe.T.BedrockWord

/-! ## §3. Stage-1 Edge & Block WP Soundness (`liftContEdgeMapped_wp`, `liftContifyBlock_wp`) -/

private theorem lookupV_append_left {bvs vsTail : List ((t : Ty) × Val t)} {t : Ty} {i : Nat}
    (hi : i < bvs.length) : lookupV (bvs ++ vsTail) t i = lookupV bvs t i := by
  dsimp only [lookupV]; rw [listGet?_append_left bvs vsTail hi]

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
  rw [beq_iff_eq.1 hEq] at hm; have hs := hm rfl
  dsimp only [denoteRegsExpr] at hn
  cases h0 : denoteArg bvs nxt.sp <;> rw [h0] at hn; · cases hn
  cases h1 : denoteArg bvs nxt.rp <;> rw [h1] at hn; · cases hn
  cases h2 : denoteArg bvs nxt.rv <;> rw [h2] at hn; · cases hn
  cases h3 : denoteArg bvs nxt.r1 <;> rw [h3] at hn; · cases hn
  cases h4 : denoteArg bvs nxt.r2 <;> rw [h4] at hn; · cases hn
  cases h5 : denoteArg bvs nxt.r3 <;> rw [h5] at hn; · cases hn
  cases hn; simpa [RegsExpr.eval] using hs

private theorem denoteRegsExpr_rp {vs : List ((t : Ty) × Val t)} {nxt : RegsExpr K}
    {nxt' : RegsExpr Val} (hn : denoteRegsExpr vs nxt = some nxt') :
    denoteArg vs nxt.rp = some nxt'.rp := (denoteRegsExpr_sp_rp hn).2

private theorem denoteRegsExpr_toTup' {vs : List ((t : Ty) × Val t)} {nxt : RegsExpr K}
    {nxt' : RegsExpr Val} (hn : denoteRegsExpr vs nxt = some nxt') :
    ∃ args', denoteArgs vs nxt.toTup = some args' ∧ vals args' = nxt'.eval.toRegsV.toTup := by
  dsimp only [denoteRegsExpr] at hn
  cases h0 : denoteArg vs nxt.sp <;> rw [h0] at hn; · cases hn
  cases h1 : denoteArg vs nxt.rp <;> rw [h1] at hn; · cases hn
  cases h2 : denoteArg vs nxt.rv <;> rw [h2] at hn; · cases hn
  cases h3 : denoteArg vs nxt.r1 <;> rw [h3] at hn; · cases hn
  cases h4 : denoteArg vs nxt.r2 <;> rw [h4] at hn; · cases hn
  cases h5 : denoteArg vs nxt.r3 <;> rw [h5] at hn; · cases hn
  cases hn; exact ⟨(_, _, _, _, _, _, ()),
    by dsimp only [RegsExpr.toTup, denoteArgs]; rw [h0, h1, h2, h3, h4, h5], rfl⟩

private theorem shiftArg_denote {t : Ty} (extra vs : List ((t' : Ty) × Val t')) (a : Arg K t) :
    denoteArg (extra ++ vs) (shiftArg extra.length a) = denoteArg vs a := by
  cases a with | imm _ => rfl | var i =>
    dsimp only [shiftArg, denoteArg, lookupV]; rw [Nat.add_comm i _, listGet?_append_skip]

private theorem shiftRegsExpr_denote (extra vs : List ((t : Ty) × Val t)) (e : RegsExpr K) :
    denoteRegsExpr (extra ++ vs) (shiftRegsExpr extra.length e) = denoteRegsExpr vs e := by
  dsimp only [shiftRegsExpr, denoteRegsExpr]; simp only [shiftArg_denote]

private theorem denoteArg_var_prefix {V : Ty → Type} {bvs vsTail : List ((t : Ty) × V t)}
    {t : Ty} {i : Nat} (hi : i < bvs.length) :
    denoteArg (bvs ++ vsTail) (@Arg.var K t i) = denoteArg bvs (.var i) := by
  dsimp only [denoteArg, lookupV]; rw [listGet?_append_left bvs vsTail hi]

private theorem pushBvs_sp6 {bvsTflat : List ((t : Ty) × Val t)} {d nSlots : Nat} {sp₀ : BitVec 64}
    (hsp : nSlots > 0 → 6 < d ∧ cLevelVal (t := i64) bvsTflat 6 = some sp₀)
    (extra : List ((t : Ty) × Val t)) :
    nSlots > 0 → 6 < d + extra.length ∧ cLevelVal (t := i64) (extra ++ bvsTflat) 6 = some sp₀ :=
  fun hPos => let ⟨hlt, hs⟩ := hsp hPos; ⟨by omega, cLevelVal_prepend extra bvsTflat hs⟩

private theorem pushBvs_slots {bvsTflat : List ((t : Ty) × Val t)} {d nSlots : Nat}
    {sLvls : List Nat} {slots : List (BitVec 64)}
    (hs : nSlots > 0 → SlotsLvlsOk bvsTflat d sLvls slots ∧ slots.length = nSlots)
    (extra : List ((t : Ty) × Val t)) : nSlots > 0 →
    SlotsLvlsOk (extra ++ bvsTflat) (d + extra.length) sLvls slots ∧ slots.length = nSlots :=
  fun hPos => let ⟨hsOk, hsLen⟩ := hs hPos; ⟨slotsLvlsOk_ext extra hsOk, hsLen⟩

private theorem pushTup_sp6 {bvsTflat : List ((t : Ty) × Val t)} {d nSlots : Nat} {sp₀ : BitVec 64}
    (hsp : nSlots > 0 → 6 < d ∧ cLevelVal (t := i64) bvsTflat 6 = some sp₀)
    {ts : List Ty} (xs : Tup Val ts) :
    nSlots > 0 → 6 < d + ts.length ∧ cLevelVal (t := i64) (pushTup xs bvsTflat) 6 = some sp₀ :=
  fun hPos => by
    rw [show pushTup xs bvsTflat = pushTup xs [] ++ bvsTflat from pushTup_append xs [] bvsTflat]
    simpa [pushTup_length xs []] using pushBvs_sp6 hsp (pushTup xs []) hPos

private theorem pushTup_slots {bvsTflat : List ((t : Ty) × Val t)} {d nSlots : Nat}
    {sLvls : List Nat} {slots : List (BitVec 64)}
    (hs : nSlots > 0 → SlotsLvlsOk bvsTflat d sLvls slots ∧ slots.length = nSlots)
    {ts : List Ty} (xs : Tup Val ts) : nSlots > 0 →
    SlotsLvlsOk (pushTup xs bvsTflat) (d + ts.length) sLvls slots ∧ slots.length = nSlots :=
  fun hPos => by
    rw [show pushTup xs bvsTflat = pushTup xs [] ++ bvsTflat from pushTup_append xs [] bvsTflat]
    simpa [pushTup_length xs []] using pushBvs_slots hs (pushTup xs []) hPos

private theorem denoteRegsExpr_prefix_sub {bvs vsTail : List ((t : Ty) × Val t)}
    {i0 i1 i2 i3 i4 i5 : Nat} (h0 : i0 < bvs.length) (h1 : i1 < bvs.length)
    (h2 : i2 < bvs.length) (h3 : i3 < bvs.length) (h4 : i4 < bvs.length) (h5 : i5 < bvs.length) :
    denoteRegsExpr (bvs ++ vsTail) ⟨.var i0, .var i1, .var i2, .var i3, .var i4, .var i5⟩ =
    denoteRegsExpr bvs ⟨.var i0, .var i1, .var i2, .var i3, .var i4, .var i5⟩ := by
  dsimp only [denoteRegsExpr]
  rw [denoteArg_var_prefix h0, denoteArg_var_prefix h1, denoteArg_var_prefix h2,
      denoteArg_var_prefix h3, denoteArg_var_prefix h4, denoteArg_var_prefix h5]

private theorem unpromotedTail_bail_wp {pf : PrivFrameCfg} {Γ : Env} {X : XPost}
    {Ψ_bail Ψ_step : CodeSpec} {H : HaltPost} {cm : CodeMap} {stCtx : List Ty}
    {bvsConc bvsTflat vsTail : List ((t' : Ty) × Val t')} {ls : List ((ts : List Ty) × Cont ts)}
    {d : Nat} {em sLvls : List Nat} {sp₀ : BitVec 64} {slots : List (BitVec 64)}
    {mConc mPub : Mem 64} {bRaw : BlockFlat} (hPos : pf.numSlots > 0)
    (hem : EnvMapOk bvsConc bvsTflat stCtx d em)
    (hsp : 6 < d ∧ cLevelVal (t := i64) bvsTflat 6 = some sp₀)
    (hs : SlotsLvlsOk bvsTflat d sLvls slots ∧ slots.length = pf.numSlots)
    (hfr : FrameRel pf.numSlots sp₀ slots mConc mPub) (hWf : bRaw.wfCheck stCtx = true)
    (hNo : bRaw.noHlt = true) (hH : ∀ c m', H c m' → X haltSym [i64] (c, ()) m')
    (hStepBail : ∀ pc s, Ψ_step pc s → Ψ_bail pc s)
    (hBp : bRaw.wp cm.symEnv Ψ_step H bvsConc mConc)
    (extra : List ((t' : Ty) × Val t')) (hex : extra.length = 5) :
    wp Γ (regionRetPost .retEnvelope Ψ_bail 0#64) X
      (denote Val Cont (flushFrame 6 sLvls (d + 5) fun d' => lowerUnpromotedTail cm bRaw d' em)
        ((extra ++ bvsTflat) ++ vsTail) ls) mPub := by
  refine flushFrame_wp (bvs := extra ++ bvsTflat)
    (by rw [List.length_append, hem.1, hex, Nat.add_comm]) hfr
    (fun _ => ⟨by omega, cLevelVal_prepend extra bvsTflat hsp.2⟩)
    (fun _ => ⟨by simpa [hex] using slotsLvlsOk_ext extra hs.1, hs.2⟩)
    (fun h0 => absurd h0 (Nat.ne_of_gt hPos)) ?_
  intro extraF hexF
  have hdEq : d + 5 + sLvls.length = d + (extraF ++ extra).length := by simp [hexF, hex]; omega
  have hemF : EnvMapOk bvsConc ((extraF ++ extra) ++ bvsTflat) stCtx (d + 5 + sLvls.length) em := by
    rw [hdEq]; exact envMapOk_ext (extraF ++ extra) hem
  have hSub := lowerUnpromotedTail_wp (cm := cm) (Γ := Γ) (Ψ := Ψ_step) (H := H)
    bRaw (vsTail := vsTail) (ls := ls) hemF hWf hNo hBp
  have hSub' : wp Γ (retEnvQ Ψ_step) (haltXPost H) (denote Val Cont
      (lowerUnpromotedTail cm bRaw (d + 5 + sLvls.length) em)
      ((extraF ++ (extra ++ bvsTflat)) ++ vsTail) ls) mConc := by
    simpa [List.append_assoc] using hSub
  exact wp_mono (fun _ _ hq => hStepBail _ _ hq)
    (fun _ _ _ _ h => by rcases h with ⟨rfl, rfl, hh⟩; exact hH _ _ hh) _ _ hSub'

private theorem contRet_true_wp {X : XPost} {Γ : Env} {Ψ : CodeSpec} {rp₀ : BitVec 64}
    (isAlt : Bool) {args' : Tup (Arg Val) regSig} {r : Regs} {m : Mem 64}
    (hvals : vals args' = r.toRegsV.toTup)
    (hbail : Ψ (rp₀ + (if isAlt then 8#64 else 0#64)) ⟨r, m⟩) :
    wp Γ (regionRetPost (.contified true) Ψ rp₀) X
      (Expr.ret ((@Arg.imm Val .bool isAlt, args') :
        Tup (Arg Val) (RegionAbi.contified true).retSig)) m := by
  dsimp only [wp, regionRetPost, RegionAbi.retSig]
  have hEq : @vals (.bool :: regSig) (@Arg.imm Val .bool isAlt, args') =
      ((isAlt, r.toRegsV.toTup) : Tup Val (.bool :: regSig)) := by
    change ((isAlt, vals args') : Tup Val (.bool :: regSig)) = _; rw [hvals]
  rw [hEq]; dsimp only [retContPost]; cases isAlt <;> simpa [RegsV.toTup, Regs.toRegsV] using hbail

@[expose] def contRetSp : ∀ (d : Bool), Tup Val (RegionAbi.contified d).retSig → BitVec 64
  | false, r => r.1
  | true, r => r.2.1

private theorem checkContEdgeLeaf_spOk {cm : CodeMap} {abi : RegionAbi} {nSlots : Nat} {dg : Bool}
    {callees : List ContCalleeMeta} {pcs : List (BitVec 64)} {leaf : ContSymLeaf}
    {kind : EdgeKind}
    (hEdge : checkContEdgeLeaf cm abi ⟨nSlots, dg⟩ callees pcs leaf kind = true)
    (hPos : nSlots > 0) (hAbi : abi = .retEnvelope) (hnb : kind ≠ .bailout) :
    (leaf.st.evalArg leaf.nextRegs.sp == .spOffset 0#64) = true := by
  dsimp only [checkContEdgeLeaf] at hEdge
  have hne : (nSlots == 0) = false := beq_false_of_ne (Nat.ne_of_gt hPos)
  cases hs : checkEdgeLeaf cm abi (callees.map fun c => ⟨c.name, c.entryPc, c.dualRet⟩)
      pcs ⟨leaf.path, leaf.st.toSymState, leaf.target, leaf.nextRegs⟩ kind
  · cases kind <;> simp [hs] at hEdge
  · simp only [hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hne] at hEdge
    cases kind with
    | direct _ | select _ _ | strideTable _ _ _ | guarded _ | contCall _ _ _ _ _ =>
        by_cases hb : (leaf.st.evalArg leaf.nextRegs.sp == .spOffset 0#64) = true
        · exact hb
        · have hf := Bool.eq_false_iff.2 hb; simp [hf] at hEdge
    | contRet _ => subst hAbi; simp [checkEdgeLeaf] at hs
    | memTableGuarded _ _ | memTableRo _ _ _ => simp at hEdge
    | bailout => exact absurd rfl hnb

private theorem checkContEdgeLeaf_callMemFree {cm : CodeMap} {abi : RegionAbi} {nSlots : Nat}
    {dg : Bool} {callees : List ContCalleeMeta} {pcs : List (BitVec 64)} {leaf : ContSymLeaf}
    {callee : Sym} {calleePc retPc : BitVec 64} {dualRet : Bool} {altRetPc? : Option (BitVec 64)}
    (hEdge : checkContEdgeLeaf cm abi ⟨nSlots, dg⟩ callees pcs leaf
      (.contCall callee calleePc dualRet retPc altRetPc?) = true) (hPos : nSlots > 0) :
    callees.any (fun c => (c.name == callee) && (c.entryPc == calleePc) && c.memFree) = true := by
  dsimp only [checkContEdgeLeaf] at hEdge
  have hne : (nSlots == 0) = false := beq_false_of_ne (Nat.ne_of_gt hPos)
  cases hs : checkEdgeLeaf cm abi (callees.map fun c => ⟨c.name, c.entryPc, c.dualRet⟩)
      pcs ⟨leaf.path, leaf.st.toSymState, leaf.target, leaf.nextRegs⟩
      (.contCall callee calleePc dualRet retPc altRetPc?)
  · simp [hs] at hEdge
  · simp only [hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hne] at hEdge
    by_cases hb : (leaf.st.evalArg leaf.nextRegs.sp == .spOffset 0#64) = true
    · simp only [hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hEdge; exact hEdge
    · have hf := Bool.eq_false_iff.2 hb; simp [hf] at hEdge

theorem liftContEdgeMapped_wp {abi : RegionAbi} {nSlots : Nat} {Γ : Env} {X : XPost}
    {Ψ_bail Pred Ψ_step : CodeSpec} {cm : CodeMap} {callees : List ContCalleeMeta}
    {pcs : List (BitVec 64)} {ls : List ((ts : List Ty) × Cont ts)}
    (hls : ContLsMatch nSlots pcs ls Pred) {bvsConc bvsTflat vsTail : List ((t : Ty) × Val t)}
    {d : Nat} {em sLvls : List Nat} {sp₀ rp₀ : BitVec 64} {st : ContSymState}
    {slots : List (BitVec 64)} {mConc mPub : Mem 64} (hem : EnvMapOk bvsConc bvsTflat st.ctx d em)
    (hst : ContSymStateOk bvsConc sp₀ rp₀ st)
    (hsp : nSlots > 0 → 6 < d ∧ cLevelVal (t := i64) bvsTflat 6 = some sp₀)
    (hs : nSlots > 0 → SlotsLvlsOk bvsTflat d sLvls slots ∧ slots.length = nSlots)
    (hz : nSlots = 0 → sLvls = []) (hAbiZero : nSlots > 0 → abi = .retEnvelope)
    (hfr : FrameRel nSlots sp₀ slots mConc mPub) {tgt : Arg K i64} {tgt' : Arg Val i64}
    (htgtB : denoteArg bvsConc tgt = some tgt') (hchkT : checkArg st.ctx i64 tgt = true)
    {nxt : RegsExpr K} {nxt' : RegsExpr Val}
    (hnxtB : denoteRegsExpr bvsConc nxt = some nxt') (hchkN : checkRegsExpr st.ctx nxt = true)
    {path : BranchPath} {kind : EdgeKind} {dg : Bool} (reqSp : Bool)
    (hReqSp : reqSp = true → nSlots > 0 ∨ (st.evalArg nxt.sp == .spOffset 0#64) = true)
    (hEdge : checkContEdgeLeaf cm abi ⟨nSlots, dg⟩ callees pcs ⟨path, st, tgt, nxt⟩ kind = true)
    (hStep : Ψ_step tgt'.val ⟨nxt'.eval, mConc⟩)
    (hStepPred : ∀ pc s, (findLabelIdx pcs pc).isSome = true →
      (abi.isContified = true → s.regs.rp = rp₀) →
      (reqSp = true → s.regs.sp = sp₀) → Ψ_step pc s → Pred pc s)
    (hStepBail : ∀ pc s, (abi.isContified = true → reqSp = true → s.regs.sp = sp₀) →
      Ψ_step pc s → Ψ_bail pc s)
    (hStepCall : ∀ callee calleePc dualRet retPc altRetPc?, abi.isContified = false →
      callees.any (fun c => (c.name == callee) && (c.entryPc == calleePc) &&
        (c.dualRet == dualRet)) = true →
      (nSlots > 0 → callees.any (fun c => (c.name == callee) && (c.entryPc == calleePc) &&
        c.memFree) = true) →
      cm.addrOf? callee = some calleePc → tgt'.val = calleePc → nxt'.rp.val = retPc →
      (if dualRet then altRetPc? = some (retPc + 8#64) else altRetPc?.isNone) →
      (findLabelIdx pcs retPc).isSome = true →
      (if dualRet then (findLabelIdx pcs (retPc + 8#64)).isSome = true else True) →
      (nSlots > 0 → nxt'.eval.sp = sp₀) →
      ∃ P E, Γ callee regSig (RegionAbi.contified dualRet).retSig nxt'.eval.toRegsV.toTup mPub P E ∧
      (∀ r m'', P r m'' → ∃ mConc'', (nSlots > 0 → contRetSp dualRet r = sp₀) ∧
        FrameRel nSlots sp₀ slots mConc'' m'' ∧ retContPost dualRet Pred retPc r mConc'') ∧
      (∀ g cs xs m'', E g cs xs m'' → X g cs xs m'')) :
    wp Γ (regionRetPost abi Ψ_bail rp₀) X (denote Val Cont
      (liftContEdgeMapped abi nSlots 6 sLvls pcs st d em tgt nxt kind)
      (bvsTflat ++ vsTail) ls) mPub := by
  have hb := hem.1
  have htgtT : denoteArg (bvsTflat ++ vsTail) (remapArg d em tgt) = some tgt' := by
    rw [denoteArg_remap hem hchkT, htgtB]
  have hnxtT : denoteRegsExpr (bvsTflat ++ vsTail) (remapRegsExpr d em nxt) = some nxt' := by
    rw [denoteRegsExpr_remap hem hchkN, hnxtB]
  have hmt := evalContArg_symValMatch hst htgtB; have hEdgeOrig := hEdge
  have hSpEdge : (kind ≠ .bailout) → (nSlots > 0 ∨ reqSp = true) → nxt'.eval.sp = sp₀ := by
    intro hnb hOr; refine spZero_contNxtSp hst hnxtB ?_
    rcases hOr with hPos | hReq
    · exact checkContEdgeLeaf_spOk hEdgeOrig hPos (hAbiZero hPos) hnb
    · rcases hReqSp hReq with hPos | hEq
      · exact checkContEdgeLeaf_spOk hEdgeOrig hPos (hAbiZero hPos) hnb
      · exact hEq
  have hnSp : nSlots > 0 → kind ≠ .bailout → nxt'.eval.sp = sp₀ := fun hPos hnb =>
    hSpEdge hnb (.inl hPos)
  have hReqPred : reqSp = true → kind ≠ .bailout → nxt'.eval.sp = sp₀ := fun hR hnb =>
    hSpEdge hnb (.inr hR)
  dsimp only [checkContEdgeLeaf] at hEdge
  cases hs0 : checkEdgeLeaf cm abi (callees.map fun c => ⟨c.name, c.entryPc, c.dualRet⟩)
      pcs ⟨path, st.toSymState, tgt, nxt⟩ kind with
  | false =>
      cases kind <;> simp [hs0] at hEdge
  | true =>
      dsimp only [checkEdgeLeaf, SymState.getSym] at hs0; cases kind with
      | memTableGuarded _ _ | memTableRo _ _ _ => simp at hEdge
      | direct targetPc =>
          simp only [Bool.and_eq_true] at hs0
          have hrc := contSymState_asConst_val hst htgtB (beq_iff_eq.1 hs0.1.2)
          rcases Option.isSome_iff_exists.1 hs0.2 with ⟨j, hj⟩
          dsimp only [liftContEdgeMapped]; rw [hrc] at hStep
          exact lowerContJumpTo_wp hls hb hj hnxtT hsp hs (fun hPos => hnSp hPos (by simp)) hfr
            (hStepPred targetPc _ hs0.2 (rpZero_contNxtRp hst hnxtB hs0.1.1)
              (fun hR => hReqPred hR (by simp)) hStep)
      | select tPc ePc =>
          simp only [Bool.and_eq_true] at hs0
          rcases Option.isSome_iff_exists.1 hs0.1.1.2 with ⟨jt, hjt⟩
          rcases Option.isSome_iff_exists.1 hs0.1.2 with ⟨je, hje⟩
          dsimp only [liftContEdgeMapped]; rw [contSymState_toSymVal_eval tgt] at hs0
          cases hev : st.evalArg tgt <;> rw [hev] at hs0 hmt <;>
            try (rcases hs0 with ⟨_, hbad⟩; dsimp only [ContSymVal.toSymVal] at hbad; cases hbad)
          rename_i cLvl tSym eSym
          dsimp only [ContSymVal.toSymVal] at hs0; simp only [Bool.and_eq_true] at hs0
          obtain ⟨b, hcLv, htB, heB⟩ := hmt rfl
          obtain ⟨_, tl, htlLt, hget, hlook⟩ := cLevelVal_of_envMap hem hst hcLv
          have hdenB : denoteArg (bvsTflat ++ vsTail) (.var (d - 1 - tl)) = some (.var b) := by
            dsimp only [denoteArg]
            rw [lookupV_append_left (by rw [hb]; omega), cLevelVal_lookupV_tflat hb htlLt, hlook]
          dsimp only [denote]; rw [hget, hdenB]; dsimp only [denoteArg, wp]; constructor
          · intro htr
            have htc := contSymVal_asConst_of_match (by simpa using htB htr)
              (beq_iff_eq.1 hs0.2.1.2)
            rw [htc] at hStep
            exact lowerContJumpTo_wp hls hb hjt hnxtT hsp hs (fun hPos => hnSp hPos (by simp)) hfr
              (hStepPred tPc _ hs0.1.1.2 (rpZero_contNxtRp hst hnxtB hs0.1.1.1)
                (fun hR => hReqPred hR (by simp)) hStep)
          · intro hfl
            have hec := contSymVal_asConst_of_match (by simpa using heB hfl)
              (beq_iff_eq.1 hs0.2.2)
            rw [hec] at hStep
            exact lowerContJumpTo_wp hls hb hje hnxtT hsp hs (fun hPos => hnSp hPos (by simp)) hfr
              (hStepPred ePc _ hs0.1.2 (rpZero_contNxtRp hst hnxtB hs0.1.1.1)
                (fun hR => hReqPred hR (by simp)) hStep)
      | strideTable basePc targets needGuard =>
          simp only [Bool.and_eq_true] at hs0
          have hne : targets ≠ [] := fun he => by simp [he] at hs0
          rw [contSymState_toSymVal_eval tgt] at hs0
          cases hev : st.evalArg tgt <;> rw [hev] at hs0 hmt <;>
            try (rcases hs0 with ⟨_, hbad⟩; dsimp only [ContSymVal.toSymVal] at hbad; cases hbad)
          rename_i b lvl
          dsimp only [ContSymVal.toSymVal] at hs0; simp only [Bool.and_eq_true] at hs0
          have hbeq : b = basePc := beq_iff_eq.1 hs0.2.1.1; subst hbeq
          obtain ⟨x, hx, hxtgt⟩ := hmt rfl; simp only [cast_eq] at hxtgt
          obtain ⟨_, tl, htlLt, hget, hlook⟩ := cLevelVal_of_envMap hem hst hx
          have hlookT : lookupV bvsTflat i64 (d - 1 - tl) = some x := by
            rw [cLevelVal_lookupV_tflat hb htlLt]; exact hlook
          cases needGuard
          · dsimp only [liftContEdgeMapped]; rw [hev]; dsimp only; rw [hget]
            obtain ⟨x', hx', hlt⟩ := contSymState_hasUltBound hst hs0.2.2
            rw [hx] at hx'; cases hx'; rw [← hb] at htlLt
            simpa using lowerContStride_wp hls hb hlookT (by omega) hnxtT hsp hs
              (fun hPos => hnSp hPos (by simp)) hfr 0 [] targets hne hs0.1.2 (Nat.zero_le _)
              (by omega : x.toNat < 0 + targets.length)
              (hStepPred _ _ (checkStrideTargets_mem_isSome' 0 targets x.toNat hs0.1.2
                (Nat.zero_le _) (by omega)) (rpZero_contNxtRp hst hnxtB hs0.1.1.1)
                (fun hR => hReqPred hR (by simp)) (hxtgt ▸ hStep))
          · cases abi with
            | contified _ => simp [RegionAbi.isContified] at hs0
            | retEnvelope =>
                dsimp only [liftContEdgeMapped]; rw [hev]; dsimp only; rw [hget]
                have hdenX : denoteArg (bvsTflat ++ vsTail) (.var (d - 1 - tl)) =
                    some (@Arg.var Val i64 x) := by
                  dsimp only [denoteArg]; rw [lookupV_append_left (by rw [hb]; omega), hlookT]
                have himm : denoteArg (bvsTflat ++ vsTail)
                    (@Arg.imm K i64 (BitVec.ofNat 64 targets.length)) = some (.imm _) := rfl
                dsimp only [denote, op2, denoteArgs]; rw [hdenX, himm]
                dsimp only [denoteArg, wp, Op.wp, OpCode.wp, vals, liftCmp, CmpOp.evalBits,
                  Ty.hasFloat, pushTup, Arg.val]
                let cBool := BitVec.ult x (BitVec.ofNat 64 targets.length)
                let bvs1 : List ((t : Ty) × Val t) := ⟨.bool, cBool⟩ :: bvsTflat
                constructor
                · intro htr
                  have hult := of_decide_eq_true htr; rw [BitVec.toNat_ofNat] at hult
                  have hlt := Nat.lt_of_lt_of_le hult (Nat.mod_le _ _)
                  have hnxt1 : denoteRegsExpr (bvs1 ++ vsTail) (remapRegsExpr (d + 1) em nxt) =
                      some nxt' := by
                    let cb : (t : Ty) × Val t := ⟨.bool, cBool⟩
                    have hc1 : denoteRegsExpr (([cb] ++ bvsTflat) ++ vsTail)
                        (remapRegsExpr (d + [cb].length) em nxt) = some nxt' := by
                      rw [denoteRegsExpr_remap (envMapOk_ext [cb] hem) hchkN, hnxtB]
                    exact hc1
                  have hlook1 : lookupV bvs1 i64 (d - 1 - tl + 1) = some x := hlookT
                  simpa [bvs1] using lowerContStride_wp hls (bvsTflat := bvs1) (d := d + 1)
                    (by simp [bvs1, hb]) hlook1 (by simp [bvs1, hb]; omega) hnxt1
                    (pushBvs_sp6 hsp [⟨Ty.bool, cBool⟩]) (pushBvs_slots hs [⟨Ty.bool, cBool⟩])
                    (fun hPos => hnSp hPos (by simp)) hfr 0 [] targets hne hs0.1.2 (Nat.zero_le _)
                    (by omega : x.toNat < 0 + targets.length)
                    (hStepPred _ _ (checkStrideTargets_mem_isSome' 0 targets x.toNat hs0.1.2
                      (Nat.zero_le _) (by omega)) (fun h => by cases h)
                      (fun hR => hReqPred hR (by simp)) (hxtgt ▸ hStep))
                · intro _
                  apply flushFrame_wp (bvs := bvs1) (by simp [bvs1, hb]) hfr
                    (pushBvs_sp6 hsp [⟨Ty.bool, cBool⟩]) (pushBvs_slots hs [⟨Ty.bool, cBool⟩]) hz
                  intro extraF hexF
                  let cb : (t : Ty) × Val t := ⟨.bool, cBool⟩
                  have hlen : (extraF ++ [cb]).length = 1 + sLvls.length := by
                    simp [hexF, Nat.add_comm]
                  have hApp : (extraF ++ bvs1) ++ vsTail =
                      (extraF ++ [cb]) ++ (bvsTflat ++ vsTail) := by
                    simp [bvs1, cb, List.append_assoc]
                  have hT : denoteArg ((extraF ++ bvs1) ++ vsTail)
                      (shiftArg (1 + sLvls.length) (remapArg d em tgt)) = some tgt' := by
                    rw [hApp, ← hlen, shiftArg_denote]; exact htgtT
                  have hN : denoteRegsExpr ((extraF ++ bvs1) ++ vsTail)
                      (shiftRegsExpr (1 + sLvls.length) (remapRegsExpr d em nxt)) = some nxt' := by
                    rw [hApp, ← hlen, shiftRegsExpr_denote]; exact hnxtT
                  exact mkRetEnvelope_wp hT hN (hStepBail _ _ (fun h => by cases h) hStep)
      | contCall callee calleePc dualRet retPc altRetPc? =>
          cases abi with
          | contified _ => simp [RegionAbi.isContified] at hs0
          | retEnvelope =>
              simp only [RegionAbi.isContified, Bool.not_false, Bool.true_and,
                Bool.and_eq_true] at hs0
              have haddr : cm.addrOf? callee = some calleePc := beq_iff_eq.1 hs0.1.1.1.1.1
              have htc := contSymState_asConst_val hst htgtB (beq_iff_eq.1 hs0.1.1.1.1.2)
              have hrpc := contSymState_asConst_val hst (denoteRegsExpr_rp hnxtB)
                (beq_iff_eq.1 hs0.1.1.1.2)
              have hCal0 : callees.any (fun c => (c.name == callee) &&
                  (c.entryPc == calleePc) && (c.dualRet == dualRet)) = true := by
                simpa [List.any_map] using hs0.1.2
              have hMfC : nSlots > 0 → callees.any (fun c => (c.name == callee) &&
                  (c.entryPc == calleePc) && c.memFree) = true := fun hPos =>
                checkContEdgeLeaf_callMemFree hEdgeOrig hPos
              have hAltC : if dualRet then altRetPc? = some (retPc + 8#64) else altRetPc?.isNone :=
                by cases dualRet <;> simp_all
              have hAltIn : if dualRet then (findLabelIdx pcs (retPc + 8#64)).isSome = true
                  else True := by cases dualRet <;> simp_all
              obtain ⟨args', hargs', hvals⟩ := denoteRegsExpr_toTup' hnxtT
              obtain ⟨P, E, hΓc, hP, hE⟩ := hStepCall callee calleePc dualRet retPc altRetPc? rfl
                hCal0 hMfC haddr htc hrpc hAltC hs0.1.1.2 hAltIn (fun hPos => hnSp hPos (by simp))
              dsimp only [liftContEdgeMapped]; cases dualRet
              · simp only [Bool.false_eq_true, ↓reduceIte]; dsimp only [denote]; rw [hargs']
                refine ⟨P, E, hvals ▸ hΓc, ?_, hE⟩
                intro r m'' hr; obtain ⟨mConc', hSpR, hFr', hPr⟩ := hP r m'' hr
                rcases Option.isSome_iff_exists.1 hs0.1.1.2 with ⟨jr, hjr⟩
                obtain ⟨nxtR', hNxtR', hNxtVals⟩ := contCall_retNxt_false r bvsTflat hb
                have hLenR : (pushTup r bvsTflat).length = d + 6 := by
                  rw [pushTup_length, hb, Nat.add_comm]; rfl
                have hNxtR : denoteRegsExpr ((pushTup r bvsTflat) ++ vsTail)
                    ⟨.var (d + 6 - 1 - d), .var (d + 6 - 1 - (d + 1)),
                     .var (d + 6 - 1 - (d + 2)), .var (d + 6 - 1 - (d + 3)),
                     .var (d + 6 - 1 - (d + 4)), .var (d + 6 - 1 - (d + 5))⟩ = some nxtR' := by
                  rw [denoteRegsExpr_prefix_sub (by omega) (by omega) (by omega) (by omega)
                    (by omega) (by omega)]; exact hNxtR'
                have hP' : Pred retPc ⟨nxtR'.eval, mConc'⟩ := by
                  rcases r with ⟨sp, rp, rv, r1, r2, r3, ⟨⟩⟩
                  rcases hEv : nxtR'.eval with ⟨_, _, _, _, _, _⟩
                  rw [hEv] at hNxtVals; cases hNxtVals; exact hPr
                have hnSpR : nSlots > 0 → nxtR'.eval.sp = sp₀ := fun hPos => by
                  rcases r with ⟨sp, rp, rv, r1, r2, r3, ⟨⟩⟩
                  dsimp only [contRetSp] at hSpR
                  rcases hEv : nxtR'.eval with ⟨_, _, _, _, _, _⟩
                  rw [hEv] at hNxtVals; cases hNxtVals; exact hSpR hPos
                dsimp only; rw [pushTup_append r bvsTflat vsTail]
                exact lowerContJumpTo_wp hls hLenR hjr hNxtR (pushTup_sp6 hsp r)
                  (pushTup_slots hs r) hnSpR hFr' hP'
              · cases hAlt : altRetPc? with
                | none => simp [hAlt] at hAltC
                | some altPc =>
                    have haltEq : altPc = retPc + 8#64 := by simpa [hAlt] using hAltC
                    subst haltEq; simp only [↓reduceIte]; dsimp only [denote]; rw [hargs']
                    refine ⟨P, E, hvals ▸ hΓc, ?_, hE⟩
                    intro r m'' hr; obtain ⟨mConc', hSpR, hFr', hPr⟩ := hP r m'' hr
                    obtain ⟨c', nxtR', hc', hcVal, hNxtR', hNxtVals⟩ :=
                      contCall_retNxt_true r bvsTflat hb
                    have hLenR : (pushTup r bvsTflat).length = d + 7 := by
                      rw [pushTup_length, hb, Nat.add_comm]; rfl
                    have hcS : denoteArg ((pushTup r bvsTflat) ++ vsTail) (.var 6) = some c' := by
                      rw [denoteArg_var_prefix (by omega)]; exact hc'
                    have hNxtR : denoteRegsExpr ((pushTup r bvsTflat) ++ vsTail)
                        ⟨.var (d + 7 - 1 - (d + 1)), .var (d + 7 - 1 - (d + 2)),
                         .var (d + 7 - 1 - (d + 3)), .var (d + 7 - 1 - (d + 4)),
                         .var (d + 7 - 1 - (d + 5)), .var (d + 7 - 1 - (d + 6))⟩ = some nxtR' := by
                      rw [denoteRegsExpr_prefix_sub (by omega) (by omega) (by omega) (by omega)
                        (by omega) (by omega)]; exact hNxtR'
                    have hnSpR : nSlots > 0 → nxtR'.eval.sp = sp₀ := fun hPos => by
                      rcases r with ⟨isAlt, sp, rp, rv, r1, r2, r3, ⟨⟩⟩
                      dsimp only [contRetSp] at hSpR
                      rcases hEv : nxtR'.eval with ⟨_, _, _, _, _, _⟩
                      rw [hEv] at hNxtVals; cases hNxtVals; exact hSpR hPos
                    dsimp only; rw [pushTup_append r bvsTflat vsTail, hcS]; dsimp only [wp]
                    have mkPred : ∀ (isAltB : Bool), r.1 = isAltB →
                        Pred (if isAltB then retPc + 8#64 else retPc) ⟨nxtR'.eval, mConc'⟩ := by
                      intro isAltB his; rcases r with ⟨isAlt, sp, rp, rv, r1, r2, r3, ⟨⟩⟩
                      dsimp only at his hNxtVals; rcases hEv : nxtR'.eval with ⟨_, _, _, _, _, _⟩
                      rw [hEv] at hNxtVals; cases hNxtVals
                      simpa [retContPost, his, Regs.toRegsV] using hPr
                    constructor
                    · intro htr; rcases Option.isSome_iff_exists.1 hAltIn with ⟨ja, hja⟩
                      exact lowerContJumpTo_wp hls hLenR hja hNxtR (pushTup_sp6 hsp r)
                        (pushTup_slots hs r) hnSpR hFr' (mkPred true (by rw [← hcVal, htr]))
                    · intro hfl; rcases Option.isSome_iff_exists.1 hs0.1.1.2 with ⟨jr, hjr⟩
                      exact lowerContJumpTo_wp hls hLenR hjr hNxtR (pushTup_sp6 hsp r)
                        (pushTup_slots hs r) hnSpR hFr' (mkPred false (by rw [← hcVal, hfl]))
      | contRet isAlt =>
          cases abi with
          | retEnvelope => simp at hs0
          | contified dualRet =>
              have heqM : mConc = mPub := by
                by_cases hn0 : nSlots = 0
                · subst hn0; exact frameRel_zero hfr
                · cases hAbiZero (Nat.pos_of_ne_zero hn0)
              subst heqM; have hbe := Bool.and_eq_true_iff.1 hs0
              have hisOk : (if isAlt then dualRet = true else True) := by
                cases isAlt
                · trivial
                · exact of_decide_eq_true hbe.1
              have hevEq : st.evalArg tgt = .rpOffset (if isAlt then 8#64 else 0#64) := by
                rw [contSymState_toSymVal_eval tgt] at hbe
                cases hev : st.evalArg tgt <;>
                  simp only [hev, ContSymVal.toSymVal, beq_iff_eq] at hbe
                all_goals try cases hbe.2
                cases hbe.2; rfl
              rw [hevEq] at hmt
              have hrpTgt : tgt'.val = rp₀ + (if isAlt then 8#64 else 0#64) := hmt rfl
              have hSpRet : (RegionAbi.contified dualRet).isContified = true → reqSp = true →
                  nxt'.eval.sp = sp₀ := fun _ hR => hReqPred hR (by simp)
              have hbail := hStepBail _ _ hSpRet hStep; rw [hrpTgt] at hbail
              obtain ⟨args', hargs', hvals⟩ := denoteRegsExpr_toTup' hnxtT
              rcases hEv : nxt'.eval with ⟨_, _, _, _, _, _⟩; rw [hEv] at hbail hvals
              cases dualRet
              · cases isAlt
                · dsimp only [liftContEdgeMapped, denote]
                  rw [show (denoteArgs (ts := (RegionAbi.contified false).retSig) _ _) = some args'
                    from hargs']
                  dsimp only [wp, regionRetPost, RegionAbi.retSig, retContPost] at *
                  rw [hvals]; simpa [RegsV.toTup, Regs.toRegsV] using hbail
                · simp at hisOk
              · have hargs2 : denoteArgs (ts := (RegionAbi.contified true).retSig)
                    (bvsTflat ++ vsTail)
                    (@Arg.imm K .bool isAlt, (remapRegsExpr d em nxt).toTup) =
                    some ((@Arg.imm Val .bool isAlt, args') :
                      Tup (Arg Val) (RegionAbi.contified true).retSig) := by
                  dsimp only [RegionAbi.retSig]; rw [denoteArgs.eq_2, hargs']; rfl
                dsimp only [liftContEdgeMapped]; cases isAlt
                · dsimp only [denote]; rw [hargs2]; exact contRet_true_wp false hvals hbail
                · dsimp only [denote]; rw [hargs2]; exact contRet_true_wp true hvals hbail
      | guarded hotTargets =>
          cases abi with
          | contified _ => simp [RegionAbi.isContified] at hs0
          | retEnvelope =>
              simp only [RegionAbi.isContified, Bool.not_false, Bool.true_and,
                List.all_eq_true] at hs0
              dsimp only [liftContEdgeMapped]
              exact lowerContGuarded_wp hls hb htgtT hnxtT hsp hs hz
                (fun hPos => hnSp hPos (by simp))
                hfr [] hotTargets (by simpa [List.all_eq_true] using hs0)
                (fun p hp heq => hStepPred p _ (hs0 p hp) (fun h => by cases h)
                  (fun hR => hReqPred hR (by simp)) (heq ▸ hStep))
                (hStepBail _ _ (fun h => by cases h) hStep)
      | bailout =>
          cases abi with
          | contified _ => simp [RegionAbi.isContified] at hs0
          | retEnvelope =>
              dsimp only [liftContEdgeMapped]
              apply flushFrame_wp (bvs := bvsTflat) hb hfr hsp hs hz; intro extraF hexF
              have htgtS : denoteArg (extraF ++ bvsTflat ++ vsTail)
                  (shiftArg sLvls.length (remapArg d em tgt)) = some tgt' := by
                rw [List.append_assoc, ← hexF, shiftArg_denote]; exact htgtT
              have hnxtS : denoteRegsExpr (extraF ++ bvsTflat ++ vsTail)
                  (shiftRegsExpr sLvls.length (remapRegsExpr d em nxt)) = some nxt' := by
                rw [List.append_assoc, ← hexF, shiftRegsExpr_denote]; exact hnxtT
              exact mkRetEnvelope_wp htgtS hnxtS (hStepBail _ _ (fun h => by cases h) hStep)

private theorem disj_zero_off {nSlots nBytes : Nat} {a sp₀ : BitVec 64} {slots : List (BitVec 64)}
    (hlen : slots.length = nSlots)
    (hDisj : ∀ k i j, k < nSlots → i < 8 → j < nBytes →
      a + BitVec.ofNat 64 j ≠ slotAddr sp₀ k + BitVec.ofNat 64 i) :
    ∀ k i j, 0 ≤ k → k < 0 + slots.length → i < 8 → j < nBytes →
      a + BitVec.ofNat 64 j ≠ slotAddr sp₀ k + BitVec.ofNat 64 i :=
  fun k i j _ hk => hDisj k i j (by omega)

private theorem liftNonSlotLoad_wp {abi : RegionAbi} {pf : PrivFrameCfg}
    {Γ : Env} {X : XPost} {Ψ_bail Ψ_step : CodeSpec} {H : HaltPost} {cm : CodeMap}
    {t : Ty} {a : Arg K i64} {a' : Arg Val i64} {st : ContSymState}
    {bvsConc bvsTflat vsTail : List ((t' : Ty) × Val t')} {ls : List ((ts : List Ty) × Cont ts)}
    {d : Nat} {em sLvls : List Nat} {sp₀ rp₀ : BitVec 64} {slots : List (BitVec 64)}
    {mConc mPub : Mem 64} {kRaw : BlockFlat} {kCont : Nat → List Nat → TFlat abi.retSig}
    (hPos : pf.numSlots > 0) (hAbi : abi = .retEnvelope)
    (hem : EnvMapOk bvsConc bvsTflat st.ctx d em) (hst : ContSymStateOk bvsConc sp₀ rp₀ st)
    (hsp : 6 < d ∧ cLevelVal (t := i64) bvsTflat 6 = some sp₀)
    (hs : SlotsLvlsOk bvsTflat d sLvls slots ∧ slots.length = pf.numSlots)
    (hfr : FrameRel pf.numSlots sp₀ slots mConc mPub) (haB : denoteArg bvsConc a = some a')
    (haChk : checkArg st.ctx i64 a = true) (hkRawWf : kRaw.wfCheck (t :: st.ctx) = true)
    (hkRawNoHlt : kRaw.noHlt = true)
    (hDyn : isStaticOutsideFrame pf.numSlots t.bytes (st.evalArg a) = false →
      pf.dynAliasGuard = true ∧ t.bytes ≤ 16)
    (hH : ∀ c m', H c m' → X haltSym [i64] (c, ()) m')
    (hStepBail : ∀ pc s, Ψ_step pc s → Ψ_bail pc s)
    (hBp : (BlockFlat.load t a kRaw).wp cm.symEnv Ψ_step H bvsConc mConc)
    (hkWp : ∀ {d' em'} {bvsT' : List ((t' : Ty) × Val t')} {v : Val t},
      loadVal mConc t a'.val = some v → EnvMapOk (⟨t, v⟩ :: bvsConc) bvsT' (t :: st.ctx) d' em' →
      (6 < d' ∧ cLevelVal (t := i64) bvsT' 6 = some sp₀) →
      (SlotsLvlsOk bvsT' d' sLvls slots ∧ slots.length = pf.numSlots) →
      kRaw.wp cm.symEnv Ψ_step H (⟨t, v⟩ :: bvsConc) mConc → wp Γ (regionRetPost abi Ψ_bail rp₀) X
        (denote Val Cont (kCont d' em') (bvsT' ++ vsTail) ls) mPub) :
    wp Γ (regionRetPost abi Ψ_bail rp₀) X (denote Val Cont
      (lowerNonSlotLoad cm abi pf t a st d em sLvls kRaw kCont) (bvsTflat ++ vsTail) ls) mPub := by
  have hma := evalContArg_symValMatch hst haB
  have haT : denoteArg (bvsTflat ++ vsTail) (remapArg d em a) = some a' := by
    rw [denoteArg_remap hem haChk, haB]
  have hfr' := hfr; dsimp only [FrameRel] at hfr'; rw [ite_eq_right (Nat.ne_of_gt hPos)] at hfr'
  rcases hfr' with ⟨hsLen, hnLe, _, hMcEq⟩
  dsimp only [BlockFlat.wp] at hBp; rw [haB] at hBp; rcases hBp with ⟨v, hvConc, hkBp⟩
  dsimp only [lowerNonSlotLoad]; cases hSt : isStaticOutsideFrame pf.numSlots t.bytes (st.evalArg a)
  · simp only [Bool.false_eq_true, ↓reduceIte]; obtain ⟨hdyn, hbyt⟩ := hDyn hSt; subst hAbi
    simp only [hdyn, hbyt, decide_true, Bool.and_self, ↓reduceIte]
    refine emitAliasGuard_wp hem.1 hsp.1 hsp.2 haT hnLe hbyt ?_ ?_
    · intro extra hex hDisj
      have hvPub : loadVal mPub t a'.val = some v := by
        rw [hMcEq, loadVal_writeSlots_disjoint mPub sp₀ t a'.val 0 slots
          (disj_zero_off hsLen hDisj)] at hvConc
        exact hvConc
      have haS : denoteArg ((extra ++ bvsTflat) ++ vsTail) (shiftArg 5 (remapArg d em a)) =
          some a' := by rw [List.append_assoc, ← hex, shiftArg_denote, haT]
      dsimp only [denote]; rw [haS]; dsimp only [wp]
      exact ⟨v, hvPub, hkWp hvConc (envMapOk_cons v (by simpa [hex] using envMapOk_ext extra hem))
        ⟨by omega, cLevelVal_prepend (⟨t, v⟩ :: extra) bvsTflat hsp.2⟩
        ⟨by simpa [hex] using slotsLvlsOk_ext (⟨t, v⟩ :: extra) hs.1, hs.2⟩ hkBp⟩
    · intro extra hex
      exact unpromotedTail_bail_wp (bRaw := .load t a kRaw) hPos hem hsp hs hfr (bAnd haChk hkRawWf)
        hkRawNoHlt hH hStepBail (by dsimp only [BlockFlat.wp]; rw [haB]; exact ⟨v, hvConc, hkBp⟩)
        extra hex
  · simp only [↓reduceIte]; have hDisj := isStaticOutsideFrame_disjoint hSt hma
    have hvPub : loadVal mPub t a'.val = some v := by
      rw [hMcEq, loadVal_writeSlots_disjoint mPub sp₀ t a'.val 0 slots
        (disj_zero_off hsLen hDisj)] at hvConc
      exact hvConc
    dsimp only [denote]; rw [haT]; dsimp only [wp]
    exact ⟨v, hvPub, hkWp hvConc (envMapOk_cons v hem)
      ⟨by omega, cLevelVal_prepend [⟨t, v⟩] bvsTflat hsp.2⟩
      ⟨slotsLvlsOk_ext [⟨t, v⟩] hs.1, hs.2⟩ hkBp⟩

private theorem liftNonSlotStore_wp {abi : RegionAbi} {pf : PrivFrameCfg}
    {Γ : Env} {X : XPost} {Ψ_bail Ψ_step : CodeSpec} {H : HaltPost} {cm : CodeMap}
    {t : Ty} {v : Arg K t} {v' : Arg Val t} {a : Arg K i64} {a' : Arg Val i64}
    {st : ContSymState} {bvsConc bvsTflat vsTail : List ((t' : Ty) × Val t')}
    {ls : List ((ts : List Ty) × Cont ts)} {d : Nat} {em sLvls : List Nat} {sp₀ rp₀ : BitVec 64}
    {slots : List (BitVec 64)} {mConc mPub : Mem 64} {kRaw : BlockFlat}
    {kCont : Nat → TFlat abi.retSig} (hPos : pf.numSlots > 0) (hAbi : abi = .retEnvelope)
    (hem : EnvMapOk bvsConc bvsTflat st.ctx d em) (hst : ContSymStateOk bvsConc sp₀ rp₀ st)
    (hsp : 6 < d ∧ cLevelVal (t := i64) bvsTflat 6 = some sp₀)
    (hs : SlotsLvlsOk bvsTflat d sLvls slots ∧ slots.length = pf.numSlots)
    (hfr : FrameRel pf.numSlots sp₀ slots mConc mPub) (hvB : denoteArg bvsConc v = some v')
    (hvChk : checkArg st.ctx t v = true) (haB : denoteArg bvsConc a = some a')
    (haChk : checkArg st.ctx i64 a = true) (hkRawWf : kRaw.wfCheck st.ctx = true)
    (hkRawNoHlt : kRaw.noHlt = true)
    (hDyn : isStaticOutsideFrame pf.numSlots t.bytes (st.evalArg a) = false →
      pf.dynAliasGuard = true ∧ t.bytes ≤ 16)
    (hH : ∀ c m', H c m' → X haltSym [i64] (c, ()) m')
    (hStepBail : ∀ pc s, Ψ_step pc s → Ψ_bail pc s)
    (hBp : (BlockFlat.store v a kRaw).wp cm.symEnv Ψ_step H bvsConc mConc)
    (hkWp : ∀ {d'} {bvsT' : List ((t' : Ty) × Val t')}, EnvMapOk bvsConc bvsT' st.ctx d' em →
      (6 < d' ∧ cLevelVal (t := i64) bvsT' 6 = some sp₀) →
      (SlotsLvlsOk bvsT' d' sLvls slots ∧ slots.length = pf.numSlots) →
      FrameRel pf.numSlots sp₀ slots (storeMem mConc t a'.val v'.val)
        (storeMem mPub t a'.val v'.val) →
      kRaw.wp cm.symEnv Ψ_step H bvsConc (storeMem mConc t a'.val v'.val) →
      wp Γ (regionRetPost abi Ψ_bail rp₀) X (denote Val Cont (kCont d') (bvsT' ++ vsTail) ls)
        (storeMem mPub t a'.val v'.val)) :
    wp Γ (regionRetPost abi Ψ_bail rp₀) X (denote Val Cont
      (lowerNonSlotStore cm abi pf v a st d em sLvls kRaw kCont) (bvsTflat ++ vsTail) ls) mPub := by
  have hma := evalContArg_symValMatch hst haB
  have hvT : denoteArg (bvsTflat ++ vsTail) (remapArg d em v) = some v' := by
    rw [denoteArg_remap hem hvChk, hvB]
  have haT : denoteArg (bvsTflat ++ vsTail) (remapArg d em a) = some a' := by
    rw [denoteArg_remap hem haChk, haB]
  have hfr0 := hfr; dsimp only [FrameRel] at hfr0; rw [ite_eq_right (Nat.ne_of_gt hPos)] at hfr0
  rcases hfr0 with ⟨hsLen, hnLe, _, hMcEq⟩
  dsimp only [BlockFlat.wp] at hBp; rw [hvB, haB] at hBp; rcases hBp with ⟨hokConc, hkBp⟩
  dsimp only [lowerNonSlotStore]
  cases hSt : isStaticOutsideFrame pf.numSlots t.bytes (st.evalArg a)
  · simp only [Bool.false_eq_true, ↓reduceIte]; obtain ⟨hdyn, hbyt⟩ := hDyn hSt; subst hAbi
    simp only [hdyn, hbyt, decide_true, Bool.and_self, ↓reduceIte]
    refine emitAliasGuard_wp hem.1 hsp.1 hsp.2 haT hnLe hbyt ?_ ?_
    · intro extra hex hDisj
      have hokPub : storeOk mPub t a'.val := by
        rw [hMcEq] at hokConc
        exact (storeOk_writeSlots_disjoint mPub sp₀ t a'.val 0 slots
          (disj_zero_off hsLen hDisj)).1 hokConc
      have hvS : denoteArg ((extra ++ bvsTflat) ++ vsTail) (shiftArg 5 (remapArg d em v)) =
          some v' := by rw [List.append_assoc, ← hex, shiftArg_denote, hvT]
      have haS : denoteArg ((extra ++ bvsTflat) ++ vsTail) (shiftArg 5 (remapArg d em a)) =
          some a' := by rw [List.append_assoc, ← hex, shiftArg_denote, haT]
      dsimp only [denote]; rw [hvS, haS]; dsimp only [wp]
      exact ⟨hokPub, hkWp (by simpa [hex] using envMapOk_ext extra hem)
        ⟨by omega, cLevelVal_prepend extra bvsTflat hsp.2⟩
        ⟨by simpa [hex] using slotsLvlsOk_ext extra hs.1, hs.2⟩
        (frameRel_store_disjoint hfr t a'.val v'.val hDisj) hkBp⟩
    · intro extra hex
      exact unpromotedTail_bail_wp (bRaw := .store v a kRaw) hPos hem hsp hs hfr
        (bAnd (bAnd hvChk haChk) hkRawWf) hkRawNoHlt hH hStepBail
        (by dsimp only [BlockFlat.wp]; rw [hvB, haB]; exact ⟨hokConc, hkBp⟩) extra hex
  · simp only [↓reduceIte]; have hDisj := isStaticOutsideFrame_disjoint hSt hma
    have hokPub : storeOk mPub t a'.val := by
      rw [hMcEq] at hokConc
      exact (storeOk_writeSlots_disjoint mPub sp₀ t a'.val 0 slots
        (disj_zero_off hsLen hDisj)).1 hokConc
    dsimp only [denote]; rw [hvT, haT]; dsimp only [wp]
    exact ⟨hokPub, hkWp hem hsp hs (frameRel_store_disjoint hfr t a'.val v'.val hDisj) hkBp⟩

private theorem nonSlot_sym_guard {α : Type} {x : α} (pf : PrivFrameCfg) (sv : ContSymVal)
    (bytes : Nat) {cond : Bool} {next : Option α} (hc : cond = false)
    (h : (if (if cond = true then true else if isStaticOutsideFrame pf.numSlots bytes sv = true
        then true else pf.dynAliasGuard && decide (bytes ≤ 16)) = true then next else none) =
        some x) :
    (isStaticOutsideFrame pf.numSlots bytes sv = false → pf.dynAliasGuard = true ∧ bytes ≤ 16) ∧
      next = some x := by
  rw [hc] at h; cases hb : isStaticOutsideFrame pf.numSlots bytes sv
  · cases hdg : (pf.dynAliasGuard && decide (bytes ≤ 16))
    · simp [hb, hdg] at h
    · simp [hb, hdg] at h
      have ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 hdg
      exact ⟨fun _ => ⟨h1, of_decide_eq_true h2⟩, h⟩
  · simp [hb] at h; exact ⟨fun h1 => absurd h1.symm Bool.false_ne_true, h⟩

theorem liftContifyBlock_wp {abi : RegionAbi} {pf : PrivFrameCfg}
    {Γ : Env} {X : XPost} {Ψ_bail Pred Ψ_step : CodeSpec} {H : HaltPost}
    {cm : CodeMap} {callees : List ContCalleeMeta} {rw : RegionWitness}
    {pcs : List (BitVec 64)} {ls : List ((ts : List Ty) × Cont ts)}
    (hls : ContLsMatch pf.numSlots pcs ls Pred) (pc : BitVec 64) (sp₀ rp₀ : BitVec 64)
    (hAbiZero : pf.numSlots > 0 → abi = .retEnvelope)
    (hH : ∀ c m', H c m' → X haltSym [i64] (c, ()) m') (reqSp : Bool)
    (hStepPred : ∀ pc' s', (findLabelIdx pcs pc').isSome = true →
      (abi.isContified = true → s'.regs.rp = rp₀) →
      (reqSp = true → s'.regs.sp = sp₀) → Ψ_step pc' s' → Pred pc' s')
    (hStepBail : ∀ pc' s', (abi.isContified = true → reqSp = true → s'.regs.sp = sp₀) →
      Ψ_step pc' s' → Ψ_bail pc' s')
    (hStepCall : ∀ callee calleePc dualRet (nxtR : Regs) mConc' mPub' retPc altRetPc?,
      abi.isContified = false → callees.any (fun c => (c.name == callee) &&
        (c.entryPc == calleePc) && (c.dualRet == dualRet)) = true →
      (pf.numSlots > 0 → callees.any (fun c => (c.name == callee) &&
        (c.entryPc == calleePc) && c.memFree) = true) →
      cm.addrOf? callee = some calleePc → nxtR.rp = retPc →
      (if dualRet then altRetPc? = some (retPc + 8#64) else altRetPc?.isNone) →
      (findLabelIdx pcs retPc).isSome = true →
      (if dualRet then (findLabelIdx pcs (retPc + 8#64)).isSome = true else True) →
      (pf.numSlots > 0 → nxtR.sp = sp₀) →
      Ψ_step calleePc ⟨nxtR, mConc'⟩ → ∀ slots, FrameRel pf.numSlots sp₀ slots mConc' mPub' →
      ∃ P E, Γ callee regSig (RegionAbi.contified dualRet).retSig nxtR.toRegsV.toTup mPub' P E ∧
        (∀ r m'', P r m'' → ∃ mConc'', (pf.numSlots > 0 → contRetSp dualRet r = sp₀) ∧
          FrameRel pf.numSlots sp₀ slots mConc'' m'' ∧ retContPost dualRet Pred retPc r mConc'') ∧
        (∀ g cs xs m'', E g cs xs m'' → X g cs xs m'')) :
    ∀ (b : BlockFlat) (path : BranchPath) (st : ContSymState)
      (bvsConc bvsTflat vsTail : List ((t : Ty) × Val t)) (d : Nat) (em sLvls : List Nat)
      (leaves : List ContSymLeaf) (slots : List (BitVec 64)) (mConc mPub : Mem 64),
      EnvMapOk bvsConc bvsTflat st.ctx d em → ContSymStateOk bvsConc sp₀ rp₀ st →
      (pf.numSlots > 0 → 6 < d ∧ cLevelVal (t := i64) bvsTflat 6 = some sp₀) →
      (pf.numSlots > 0 → SlotsLvlsOk bvsTflat d sLvls slots ∧ slots.length = pf.numSlots) →
      (pf.numSlots = 0 → sLvls = []) → FrameRel pf.numSlots sp₀ slots mConc mPub →
      b.wfCheck st.ctx = true → b.noHlt = true → symEvalContBlock cm pf b path st = some leaves →
      (reqSp = true → pf.numSlots > 0 ∨
        ∀ lf ∈ leaves, (lf.st.evalArg lf.nextRegs.sp == .spOffset 0#64) = true) →
      (∀ lf ∈ leaves, ∃ ew, rw.findEdge pc lf.path = some ew ∧
        checkContEdgeLeaf cm abi pf callees pcs lf ew.kind = true) →
      b.wp cm.symEnv Ψ_step H bvsConc mConc → wp Γ (regionRetPost abi Ψ_bail rp₀) X
        (denote Val Cont (liftContifyBlock cm abi pf rw pcs pc b path st d em sLvls)
          (bvsTflat ++ vsTail) ls) mPub
  | .let_ (ts := ts) op k, path, st, bvsConc, bvsTflat, vsTail, d, em, sLvls, leaves, slots,
      mConc, mPub, hem, hst, hsp, hs, hz, hfr, hwf, hno, hlv, hreq, hleaves, hbp => by
      dsimp only [BlockFlat.wfCheck] at hwf; rcases Bool.and_eq_true_iff.1 hwf with ⟨hwfA, hwfK⟩
      dsimp only [BlockFlat.noHlt] at hno; dsimp only [symEvalContBlock] at hlv
      dsimp only [BlockFlat.wp] at hbp
      cases hda : denoteArgs bvsConc op.args <;> rw [hda] at hbp; · cases hbp
      rename_i a'
      have hdaT : denoteArgs (bvsTflat ++ vsTail) (remapArgs d em op.args) = some a' := by
        rw [denoteArgs_remap hem hwfA, hda]
      dsimp only [liftContifyBlock, denote]; rw [hdaT]; dsimp only [wp]
      exact evalContOp_wp_mono op hst hda (fun r hkr hst' => by
        rw [pushTup_append]
        exact liftContifyBlock_wp hls pc sp₀ rp₀ hAbiZero hH reqSp hStepPred hStepBail hStepCall
          k path _ (pushTup r bvsConc) (pushTup r bvsTflat) vsTail (d + ts.length)
          (pushEnvMap ts d em) sLvls leaves slots mConc mPub (envMapOk_push r hem) hst'
          (pushTup_sp6 hsp r) (pushTup_slots hs r) hz hfr hwfK hno hlv hreq hleaves hkr) hbp
  | .load t a k, path, st, bvsConc, bvsTflat, vsTail, d, em, sLvls, leaves, slots,
      mConc, mPub, hem, hst, hsp, hs, hz, hfr, hwf, hno, hlv, hreq, hleaves, hbp => by
      dsimp only [BlockFlat.wfCheck] at hwf; rcases Bool.and_eq_true_iff.1 hwf with ⟨hwfA, hwfK⟩
      dsimp only [BlockFlat.noHlt] at hno; dsimp only [symEvalContBlock] at hlv
      dsimp only [liftContifyBlock]; by_cases hn0 : pf.numSlots = 0
      · simp only [hn0, beq_self_eq_true, ↓reduceIte] at hlv ⊢; dsimp only [BlockFlat.wp] at hbp
        cases hda : denoteArg bvsConc a <;> rw [hda] at hbp; · cases hbp
        rename_i a'; rcases hbp with ⟨v, hvConc, hkv⟩
        have heq0 := frameRel_zero (hn0 ▸ hfr); subst heq0
        have hdaT : denoteArg (bvsTflat ++ vsTail) (remapArg d em a) = some a' := by
          rw [denoteArg_remap hem hwfA, hda]
        dsimp only [denote]; rw [hdaT]; dsimp only [wp]
        exact ⟨v, hvConc, liftContifyBlock_wp hls pc sp₀ rp₀ hAbiZero hH reqSp hStepPred hStepBail
          hStepCall k path _ (⟨t, v⟩ :: bvsConc) (⟨t, v⟩ :: bvsTflat) vsTail (d + 1) (d :: em)
          sLvls leaves slots mConc mConc (envMapOk_cons v hem)
          (contSymStateOk_cons v .top hst trivial)
          (fun h => absurd hn0 (Nat.ne_of_gt h)) (fun h => absurd hn0 (Nat.ne_of_gt h))
          hz hfr hwfK hno hlv hreq hleaves hkv⟩
      · have hPos : pf.numSlots > 0 := Nat.pos_of_ne_zero hn0
        have hbn : (pf.numSlots == 0) = false := beq_false_of_ne hn0
        simp only [hbn, Bool.false_eq_true, ↓reduceIte] at hlv ⊢; dsimp only [BlockFlat.wp] at hbp
        cases hda : denoteArg bvsConc a <;> rw [hda] at hbp; · cases hbp
        rename_i a'; have hma := evalContArg_symValMatch hst hda
        have hkCont : ∀ {d' em'} {bvsT' : List ((t' : Ty) × Val t')} {v : Val t},
            loadVal mConc t a'.val = some v →
            EnvMapOk (⟨t, v⟩ :: bvsConc) bvsT' (t :: st.ctx) d' em' →
            (6 < d' ∧ cLevelVal (t := i64) bvsT' 6 = some sp₀) →
            (SlotsLvlsOk bvsT' d' sLvls slots ∧ slots.length = pf.numSlots) →
            k.wp cm.symEnv Ψ_step H (⟨t, v⟩ :: bvsConc) mConc →
            symEvalContBlock cm pf k path { st with env := .top :: st.env, ctx := t :: st.ctx } =
              some leaves →
            wp Γ (regionRetPost abi Ψ_bail rp₀) X (denote Val Cont
              (liftContifyBlock cm abi pf rw pcs pc k path
                { st with env := .top :: st.env, ctx := t :: st.ctx } d' em' sLvls)
              (bvsT' ++ vsTail) ls) mPub := fun _ hEm' hSp' hS' hkB hlvK =>
          liftContifyBlock_wp hls pc sp₀ rp₀ hAbiZero hH reqSp hStepPred hStepBail hStepCall
            k path _ (⟨t, _⟩ :: bvsConc) _ vsTail _ _ sLvls leaves slots mConc mPub hEm'
            (contSymStateOk_cons _ .top hst trivial) (fun _ => hSp') (fun _ => hS')
            hz hfr hwfK hno hlvK hreq hleaves hkB
        have hNs : t ≠ i64 ∨ spSlotOf? pf.numSlots (st.evalArg a) = none →
            wp Γ (regionRetPost abi Ψ_bail rp₀) X (denote Val Cont
              (lowerNonSlotLoad cm abi pf t a st d em sLvls k fun d' em' =>
                liftContifyBlock cm abi pf rw pcs pc k path
                  { st with env := .top :: st.env, ctx := t :: st.ctx } d' em' sLvls)
              (bvsTflat ++ vsTail) ls) mPub := fun hMiss => by
          have hCond : (t == i64 && (spSlotOf? pf.numSlots (st.evalArg a)).isSome) = false := by
            rcases hMiss with hnt | hspN
            · rw [beq_false_of_ne hnt]; rfl
            · simp [hspN]
          obtain ⟨hDyn, hlvK⟩ := nonSlot_sym_guard pf (st.evalArg a) t.bytes hCond hlv
          refine liftNonSlotLoad_wp hPos (hAbiZero hPos) hem hst (hsp hPos) (hs hPos) hfr
            hda hwfA hwfK hno hDyn hH (fun _ _ hs => hStepBail _ _ (fun h => by
              rw [hAbiZero hPos] at h; cases h) hs)
            (by dsimp only [BlockFlat.wp]; rw [hda]; exact hbp)
            fun hvC hEm' hSp' hS' hkBp => hkCont hvC hEm' hSp' hS' hkBp hlvK
        cases t with
        | bits n =>
            by_cases h64 : n = 64
            · subst h64
              cases hSlot : spSlotOf? pf.numSlots (st.evalArg a) with
              | none => exact hNs (Or.inr hSlot)
              | some slotIdx =>
                  rw [hSlot] at hlv; simp only [beq_self_eq_true, Option.isSome_some, Bool.and_self,
                    ↓reduceIte] at hlv
                  obtain ⟨hkLt, hspEq⟩ := spSlotOf?_sound pf.numSlots _ _ hSlot; rw [hspEq] at hma
                  have haAddr : a'.val = slotAddr sp₀ slotIdx := by
                    have := hma rfl; simpa [slotAddr, BitVec.sub_eq_add_neg] using this
                  obtain ⟨hsOk, hsLen⟩ := hs hPos; have hd6 := (hsp hPos).1
                  obtain ⟨sl, hslLt, hgetSl, hcvSl⟩ := hsOk.2.2 slotIdx (by omega)
                  have hfr' := hfr; dsimp only [FrameRel] at hfr'
                  rw [ite_eq_right hn0] at hfr'; rcases hfr' with ⟨_, _, _, rfl⟩
                  obtain ⟨vSlot, hvSlotGet, hloadSlot⟩ := loadVal_writeSlots_slot sp₀ 0 slots mPub
                    slotIdx (Nat.zero_le _) (by omega) (by omega)
                  rw [Nat.sub_zero] at hvSlotGet
                  rcases hbp with ⟨vConc, hvConc, hkBp⟩
                  rw [haAddr, hloadSlot] at hvConc; cases hvConc
                  change wp Γ (regionRetPost abi Ψ_bail rp₀) X (denote Val Cont
                    (match listGet? sLvls slotIdx with
                    | some sLvl => .let_ (op1 (.copy i64) (.var (d - 1 - sLvl)))
                        (liftContifyBlock cm abi pf rw pcs pc k path
                          { st with env := .top :: st.env, ctx := i64 :: st.ctx } (d + 1) (d :: em)
                          sLvls)
                    | none => .hlt) (bvsTflat ++ vsTail) ls) mPub
                  rw [hgetSl]; dsimp only
                  have hArgSl : denoteArg (bvsTflat ++ vsTail) (.var (d - 1 - sl)) =
                      some (@Arg.var Val i64 vSlot) := by
                    dsimp only [denoteArg]
                    rw [lookupV_append_left (by rw [hem.1]; omega),
                        cLevelVal_lookupV_tflat hem.1 hslLt, hcvSl vSlot hvSlotGet]
                  dsimp only [denote, op1, denoteArgs]; rw [hArgSl]
                  dsimp only [denoteArg, wp, Op.wp, OpCode.wp, vals, pushTup, Arg.val]
                  exact hkCont (bvsT' := ⟨i64, vSlot⟩ :: bvsTflat) (v := vSlot)
                    (haAddr ▸ hloadSlot) (envMapOk_cons (t := i64) vSlot hem)
                    ⟨by omega, cLevelVal_prepend [⟨i64, vSlot⟩] bvsTflat (hsp hPos).2⟩
                    ⟨slotsLvlsOk_ext [⟨i64, vSlot⟩] hsOk, hsLen⟩ hkBp hlv
            · cases n with
              | zero => exact hNs (Or.inl fun h => by cases h)
              | succ m =>
                  split
                  · rename_i heq; exact absurd (by cases heq; rfl : m + 1 = 64) h64
                  · exact hNs (Or.inl fun h => h64 (by cases h; rfl))
        | bool | float _ | pair _ _ => exact hNs (Or.inl fun h => by cases h)
  | .store (t := t) v a k, path, st, bvsConc, bvsTflat, vsTail, d, em, sLvls, leaves, slots,
      mConc, mPub, hem, hst, hsp, hs, hz, hfr, hwf, hno, hlv, hreq, hleaves, hbp => by
      dsimp only [BlockFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      rcases hwf with ⟨⟨hwfV, hwfA⟩, hwfK⟩; dsimp only [BlockFlat.noHlt] at hno
      dsimp only [symEvalContBlock] at hlv; dsimp only [liftContifyBlock]
      by_cases hn0 : pf.numSlots = 0
      · simp only [hn0, beq_self_eq_true, ↓reduceIte] at hlv ⊢; dsimp only [BlockFlat.wp] at hbp
        cases hdv : denoteArg bvsConc v <;> rw [hdv] at hbp; · cases hbp
        cases hda : denoteArg bvsConc a <;> rw [hda] at hbp; · cases hbp
        rename_i v' a'; rcases hbp with ⟨hok, hkBp⟩
        have heq0 := frameRel_zero (hn0 ▸ hfr); subst heq0
        have hvT : denoteArg (bvsTflat ++ vsTail) (remapArg d em v) = some v' := by
          rw [denoteArg_remap hem hwfV, hdv]
        have haT : denoteArg (bvsTflat ++ vsTail) (remapArg d em a) = some a' := by
          rw [denoteArg_remap hem hwfA, hda]
        dsimp only [denote]; rw [hvT, haT]; dsimp only [wp]
        refine ⟨hok, liftContifyBlock_wp hls pc sp₀ rp₀ hAbiZero hH reqSp hStepPred hStepBail
          hStepCall k path st bvsConc bvsTflat vsTail d em sLvls leaves slots _ _ hem hst hsp hs hz
          ?_ hwfK hno hlv hreq hleaves hkBp⟩
        rw [hn0]; dsimp only [FrameRel]; simp only [↓reduceIte]
      · have hPos : pf.numSlots > 0 := Nat.pos_of_ne_zero hn0
        have hbn : (pf.numSlots == 0) = false := beq_false_of_ne hn0
        simp only [hbn, Bool.false_eq_true, ↓reduceIte] at hlv ⊢; dsimp only [BlockFlat.wp] at hbp
        cases hdv : denoteArg bvsConc v <;> rw [hdv] at hbp; · cases hbp
        cases hda : denoteArg bvsConc a <;> rw [hda] at hbp; · cases hbp
        rename_i v' a'; have hma := evalContArg_symValMatch hst hda
        have hNs : t ≠ i64 ∨ spSlotOf? pf.numSlots (st.evalArg a) = none →
            wp Γ (regionRetPost abi Ψ_bail rp₀) X (denote Val Cont
              (lowerNonSlotStore cm abi pf v a st d em sLvls k fun d' =>
                liftContifyBlock cm abi pf rw pcs pc k path st d' em sLvls)
              (bvsTflat ++ vsTail) ls) mPub := fun hMiss => by
          have hCond : (t == i64 && (spSlotOf? pf.numSlots (st.evalArg a)).isSome) = false := by
            rcases hMiss with hnt | hspN
            · rw [beq_false_of_ne hnt]; rfl
            · simp [hspN]
          obtain ⟨hDyn, hlvK⟩ := nonSlot_sym_guard pf (st.evalArg a) t.bytes hCond hlv
          refine liftNonSlotStore_wp hPos (hAbiZero hPos) hem hst (hsp hPos) (hs hPos) hfr
            hdv hwfV hda hwfA hwfK hno hDyn hH (fun _ _ hs => hStepBail _ _ (fun h => by
              rw [hAbiZero hPos] at h; cases h) hs)
            (by dsimp only [BlockFlat.wp]; rw [hdv, hda]; exact hbp) ?_
          intro d' bvsT' hEm' hSp' hS' hFr' hkBp
          exact liftContifyBlock_wp hls pc sp₀ rp₀ hAbiZero hH reqSp hStepPred hStepBail hStepCall
            k path st bvsConc bvsT' vsTail d' em sLvls leaves slots _ _ hEm' hst
            (fun _ => hSp') (fun _ => hS') hz hFr' hwfK hno hlvK hreq hleaves hkBp
        by_cases ht : t = i64
        · subst ht; simp only [beq_self_eq_true, ↓reduceIte] at hlv ⊢
          cases hSlot : spSlotOf? pf.numSlots (st.evalArg a) with
          | none => exact hNs (Or.inr hSlot)
          | some slotIdx =>
              rw [hSlot] at hlv; simp only [Option.isSome_some, Bool.and_self, ↓reduceIte] at hlv
              obtain ⟨hkLt, hspEq⟩ := spSlotOf?_sound pf.numSlots _ _ hSlot; rw [hspEq] at hma
              have haAddr : a'.val = slotAddr sp₀ slotIdx := by
                have := hma rfl; simpa [slotAddr, BitVec.sub_eq_add_neg] using this
              rcases hbp with ⟨_, hkBp⟩; rw [haAddr] at hkBp
              obtain ⟨hsOk, hsLen⟩ := hs hPos; have hFr' := frameRel_set_slot hn0 hfr hkLt v'.val
              cases hrv : remapArg d em v with
              | var vi =>
                  have hrem : ∃ idx tl, v = .var idx ∧ tl < d ∧ listGet? em idx = some tl ∧
                      vi = d - 1 - tl ∧ cLevelVal (t := i64) bvsTflat tl = some v'.val := by
                    cases v with | imm _ => simp [remapArg] at hrv | var idx =>
                      have hl : st.ctx.length = bvsConc.length := by rw [← hem.2.1, List.length_map]
                      have hi : idx < bvsConc.length :=
                        Nat.lt_of_lt_of_eq (checkArg_idx_lt hwfV) hl
                      obtain ⟨tl, htlLt, hgetEm, hlookEq⟩ := hem.2.2.2 idx hi
                      dsimp only [remapArg] at hrv; rw [hgetEm] at hrv; cases hrv
                      refine ⟨idx, tl, rfl, htlLt, hgetEm, rfl, ?_⟩
                      rw [← cLevelVal_lookupV_tflat hem.1 htlLt, ← hlookEq i64]
                      dsimp only [denoteArg] at hdv
                      cases hl' : lookupV bvsConc i64 idx <;> rw [hl'] at hdv; · cases hdv
                      cases hdv; rfl
                  rcases hrem with ⟨_, tl, _, htlLt, _, hviEq, hcv⟩
                  have hDtl : d - 1 - vi = tl := by rw [hviEq]; omega
                  have hsNew : SlotsLvlsOk bvsTflat d (sLvls.set slotIdx (d - 1 - vi))
                      (slots.set slotIdx v'.val) :=
                    hDtl ▸ slotsLvlsOk_set hsOk (by rw [hsLen]; exact hkLt) htlLt v'.val hcv
                  exact liftContifyBlock_wp hls pc sp₀ rp₀ hAbiZero hH reqSp hStepPred hStepBail
                    hStepCall k path st bvsConc bvsTflat vsTail d em
                    (sLvls.set slotIdx (d - 1 - vi))
                    leaves (slots.set slotIdx v'.val) _ mPub hem hst hsp
                    (fun _ => ⟨hsNew, by simpa [List.length_set] using hsLen⟩)
                    (fun h => absurd (h ▸ hPos) (Nat.lt_irrefl 0)) hFr' hwfK hno hlv
                    hreq hleaves hkBp
              | imm c =>
                  have hcEq : c = v'.val := by
                    cases v with
                    | imm _ => cases hrv; cases hdv; rfl
                    | var idx =>
                        dsimp only [remapArg] at hrv
                        cases hg : listGet? em idx <;> simp [hg] at hrv
                  rw [hcEq]
                  dsimp only [denote, op1, denoteArgs, denoteArg, wp, Op.wp, OpCode.wp, vals]
                  have hltD : d < (⟨i64, v'.val⟩ :: bvsTflat).length := by simp [hem.1]
                  have hsNew : SlotsLvlsOk (⟨i64, v'.val⟩ :: bvsTflat) (d + 1)
                      (sLvls.set slotIdx d) (slots.set slotIdx v'.val) :=
                    slotsLvlsOk_set (slotsLvlsOk_ext [⟨i64, v'.val⟩] hsOk)
                      (by rw [hsLen]; exact hkLt) (Nat.lt_succ_self d) v'.val (by
                        dsimp only [cLevelVal]; simp [hem.1]; rfl)
                  exact liftContifyBlock_wp hls pc sp₀ rp₀ hAbiZero hH reqSp hStepPred hStepBail
                    hStepCall k path st bvsConc (⟨i64, v'.val⟩ :: bvsTflat) vsTail (d + 1) em
                    (sLvls.set slotIdx d) leaves (slots.set slotIdx v'.val) _ mPub
                    (envMapOk_ext [⟨i64, v'.val⟩] hem) hst (pushBvs_sp6 hsp [⟨i64, v'.val⟩])
                    (fun _ => ⟨hsNew, by simpa [List.length_set] using hsLen⟩)
                    (fun h => absurd (h ▸ hPos) (Nat.lt_irrefl 0)) hFr' hwfK hno hlv
                    hreq hleaves hkBp
        · simp only [beq_false_of_ne ht, Bool.false_eq_true, ↓reduceIte]; exact hNs (Or.inl ht)
  | .codeAddr sym k, path, st, bvsConc, bvsTflat, vsTail, d, em, sLvls, leaves, slots,
      mConc, mPub, hem, hst, hsp, hs, hz, hfr, hwf, hno, hlv, hreq, hleaves, hbp => by
      dsimp only [BlockFlat.wfCheck] at hwf; dsimp only [BlockFlat.noHlt] at hno
      dsimp only [symEvalContBlock] at hlv; dsimp only [BlockFlat.wp, CodeMap.symEnv] at hbp
      rcases hbp with ⟨a, had, hkBp⟩; rw [had] at hlv; dsimp only [liftContifyBlock]; rw [had]
      dsimp only [denote, op1, denoteArgs, denoteArg, wp, Op.wp, OpCode.wp, vals]
      let sv := if (a &&& 7#64) == 0#64 then ContSymVal.alignedConst a else ContSymVal.const a
      have hVal : ContSymValMatch (⟨i64, a⟩ :: bvsConc) sp₀ rp₀ sv i64 a := by
        dsimp only [sv]; by_cases hal : ((a &&& 7#64) == 0#64) = true
        · rw [ite_eq_left hal]; intro _; exact ⟨rfl, beq_iff_eq.1 hal⟩
        · rw [ite_eq_right hal]; intro _; rfl
      exact liftContifyBlock_wp hls pc sp₀ rp₀ hAbiZero hH reqSp hStepPred hStepBail hStepCall
        k path _ (⟨i64, a⟩ :: bvsConc) (⟨i64, a⟩ :: bvsTflat) vsTail (d + 1) (d :: em) sLvls
        leaves slots mConc mPub (envMapOk_cons (t := i64) a hem)
        (contSymStateOk_cons (t := i64) a
          (if (a &&& 7#64) == 0#64 then .alignedConst a else .const a) hst hVal)
        (pushBvs_sp6 hsp [⟨i64, a⟩]) (pushBvs_slots hs [⟨i64, a⟩]) hz hfr hwf hno hlv
        hreq hleaves hkBp
  | .jnz c t e, path, st, bvsConc, bvsTflat, vsTail, d, em, sLvls, leaves, slots,
      mConc, mPub, hem, hst, hsp, hs, hz, hfr, hwf, hno, hlv, hreq, hleaves, hbp => by
      dsimp only [BlockFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      rcases hwf with ⟨⟨hwfC, hwfT⟩, hwfE⟩
      dsimp only [BlockFlat.noHlt] at hno; rcases Bool.and_eq_true_iff.1 hno with ⟨hnoT, hnoE⟩
      dsimp only [symEvalContBlock] at hlv
      cases hlt : symEvalContBlock cm pf t (path ++ [true]) (st.pushCondFact c true) with
      | none => simp [hlt] at hlv
      | some lt =>
          cases hle : symEvalContBlock cm pf e (path ++ [false]) (st.pushCondFact c false) with
          | none => simp [hlt, hle] at hlv
          | some le =>
              simp only [hlt, hle] at hlv; cases hlv; dsimp only [BlockFlat.wp] at hbp
              cases hdc : denoteArg bvsConc c <;> rw [hdc] at hbp; · cases hbp
              rename_i c'; rcases hbp with ⟨hbt, hbe⟩
              have hcT : denoteArg (bvsTflat ++ vsTail) (remapArg d em c) = some c' := by
                rw [denoteArg_remap hem hwfC, hdc]
              dsimp only [liftContifyBlock, denote]; rw [hcT]; dsimp only [wp]
              exact ⟨fun htr => liftContifyBlock_wp hls pc sp₀ rp₀ hAbiZero hH reqSp hStepPred
                  hStepBail hStepCall t (path ++ [true]) (st.pushCondFact c true) bvsConc bvsTflat
                  vsTail d em sLvls lt slots mConc mPub (by rw [pushContCondFact_ctx]; exact hem)
                  (pushContCondFact_sound hst hdc true htr) hsp hs hz hfr
                  (by rw [pushContCondFact_ctx]; exact hwfT) hnoT hlt
                  (fun hR => (hreq hR).elim .inl fun h =>
                    .inr fun lf hm => h lf (List.mem_append_left le hm))
                  (fun lf hm => hleaves lf (List.mem_append_left le hm)) (hbt htr),
                fun hfl => liftContifyBlock_wp hls pc sp₀ rp₀ hAbiZero hH reqSp hStepPred hStepBail
                  hStepCall e (path ++ [false]) (st.pushCondFact c false) bvsConc bvsTflat vsTail d
                  em sLvls le slots mConc mPub (by rw [pushContCondFact_ctx]; exact hem)
                  (pushContCondFact_sound hst hdc false hfl) hsp hs hz hfr
                  (by rw [pushContCondFact_ctx]; exact hwfE) hnoE hle
                  (fun hR => (hreq hR).elim .inl fun h =>
                    .inr fun lf hm => h lf (List.mem_append_right lt hm))
                  (fun lf hm => hleaves lf (List.mem_append_right lt hm)) (hbe hfl)⟩
  | .ijmp tgt nxt, path, st, bvsConc, bvsTflat, vsTail, d, em, sLvls, _, slots,
      mConc, mPub, hem, hst, hsp, hs, hz, hfr, hwf, _, hlv, hreq, hleaves, hbp => by
      dsimp only [BlockFlat.wfCheck] at hwf; rcases Bool.and_eq_true_iff.1 hwf with ⟨hwfT, hwfN⟩
      dsimp only [symEvalContBlock] at hlv; cases hlv
      obtain ⟨ew, hfind, hchk⟩ := hleaves ⟨path, st, tgt, nxt⟩ (List.Mem.head _)
      dsimp only [BlockFlat.wp] at hbp
      cases hdt : denoteArg bvsConc tgt <;> rw [hdt] at hbp; · cases hbp
      cases hdn : denoteRegsExpr bvsConc nxt <;> rw [hdn] at hbp; · cases hbp
      dsimp only [liftContifyBlock]; rw [hfind]
      exact liftContEdgeMapped_wp hls hem hst hsp hs hz hAbiZero hfr hdt hwfT hdn hwfN reqSp
        (fun hR => (hreq hR).elim .inl fun h => .inr (h _ (List.Mem.head _)))
        hchk hbp hStepPred hStepBail fun callee calleePc dualRet retPc altRetPc? hAbiF hCal hMf hAd
          hT hR hAlt hIn hAIn hnSp =>
        hStepCall callee calleePc dualRet _ mConc mPub retPc altRetPc? hAbiF hCal hMf hAd hR
          hAlt hIn hAIn hnSp (hT ▸ hbp) slots hfr
  | .halt c, _, st, bvsConc, bvsTflat, vsTail, d, em, sLvls, _, slots,
      mConc, mPub, hem, _, hsp, hs, hz, hfr, hwf, _, _, _, _, hbp => by
      dsimp only [BlockFlat.wfCheck] at hwf; dsimp only [BlockFlat.wp] at hbp
      cases hdc : denoteArg bvsConc c <;> rw [hdc] at hbp; · cases hbp
      rename_i c'
      dsimp only [liftContifyBlock]; refine flushFrame_wp (bvs := bvsTflat) hem.1 hfr hsp hs hz ?_
      intro extraF hexF
      have hcS : denoteArg ((extraF ++ bvsTflat) ++ vsTail) (remapArg (d + sLvls.length) em c) =
          some c' := by
        have hem' : EnvMapOk bvsConc (extraF ++ bvsTflat) st.ctx (d + sLvls.length) em := by
          simpa [hexF] using envMapOk_ext extraF hem
        rw [denoteArg_remap hem' hwf, hdc]
      dsimp only [denote, denoteArgs, wp, vals]; rw [hcS]; dsimp only [vals] at *
      exact hH _ mConc hbp
  | .hlt, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hno, _, _, _, _ => by
      dsimp only [BlockFlat.noHlt] at hno; cases hno

private theorem cLevelVal_pushTup_packSlotTup : ∀ (n : Nat) (slots : List (BitVec 64))
    (base : List ((t : Ty) × Val t)), slots.length = n →
    (pushTup (packSlotTup n slots) base).length = base.length + n ∧
    (∀ lvl (v : BitVec 64), lvl < base.length → cLevelVal (t := i64) base lvl = some v →
      cLevelVal (t := i64) (pushTup (packSlotTup n slots) base) lvl = some v) ∧
    (∀ j < n, ∃ v, slots[j]? = some v ∧
      cLevelVal (t := i64) (pushTup (packSlotTup n slots) base) (base.length + j) = some v)
  | 0, [], _, _ => ⟨rfl, fun _ _ _ h => h, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | 0, _ :: _, _, h | _ + 1, [], _, h => by simp at h
  | n + 1, v :: vs, base, hlen => by
      have ih := cLevelVal_pushTup_packSlotTup n vs (⟨i64, v⟩ :: base) (by simp at hlen; omega)
      have hpt : pushTup (packSlotTup (n + 1) (v :: vs)) base =
          pushTup (packSlotTup n vs) (⟨i64, v⟩ :: base) := rfl
      refine ⟨by rw [hpt, ih.1, List.length_cons]; omega, fun lvl w hlt hc => by
        rw [hpt]; exact ih.2.1 lvl w (Nat.lt_succ_of_lt hlt) (cLevelVal_prepend [⟨i64, v⟩] base hc),
        fun j hj => by rw [hpt]; cases j with
        | zero =>
            refine ⟨v, rfl, ih.2.1 base.length v (Nat.lt_succ_self _) ?_⟩
            dsimp only [cLevelVal, lookupV, listGet?]
            rw [List.length_cons, ite_eq_left (Nat.lt_succ_self _),
              Nat.add_sub_cancel, Nat.sub_self]; rfl
        | succ k =>
            obtain ⟨u, hu, hcv⟩ := ih.2.2 k (Nat.lt_of_succ_lt_succ hj); refine ⟨u, hu, ?_⟩
            rw [List.length_cons, show base.length + 1 + k = base.length + (k + 1) by omega] at hcv
            exact hcv⟩

private theorem pushTup_tupAppend {V : Ty → Type} : ∀ {as bs : List Ty} (xs : Tup V as)
    (ys : Tup V bs) (base : List ((t : Ty) × V t)),
    pushTup (tupAppend xs ys) base = pushTup ys (pushTup xs base)
  | [], _, (), _, _ => rfl | _ :: _, _, (_, xs), ys, base => pushTup_tupAppend xs ys (_ :: base)

private theorem pushTup_packContTup_succ (k : Nat) (r : Regs) (sp₀ : BitVec 64)
    (slots : List (BitVec 64)) : pushTup (packContTup (k + 1) r sp₀ slots) [] =
      pushTup (packSlotTup (k + 1) slots) (⟨i64, sp₀⟩ :: pushRegsV r.toRegsV) := by
  have hcast : ∀ {as bs : List Ty} (h : as = bs) (xs : Tup Val as) (ys : Tup Val bs),
      (h ▸ xs) = ys → pushTup xs [] = pushTup ys [] := by rintro _ _ rfl _ _ rfl; rfl
  have hsig : contSig (k + 1) = regSig ++ (i64 :: List.replicate (k + 1) i64) :=
    ite_eq_right (Nat.succ_ne_zero k)
  let ys : Tup Val (i64 :: List.replicate (k + 1) i64) := (sp₀, packSlotTup (k + 1) slots)
  rw [hcast hsig (packContTup (k + 1) r sp₀ slots) (tupAppend r.toRegsV.toTup ys) rfl]
  exact pushTup_tupAppend r.toRegsV.toTup ys []

private theorem listGet?_initEnvMap (idx : Nat) (hi : idx < 6) :
    listGet? initEnvMap idx = some (5 - idx) := by
  rcases (by omega : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem envMapOk_init (r₀ : Regs) (sp₀ : BitVec 64) (slots : List (BitVec 64))
    (nSlots : Nat) (hSLen : nSlots > 0 → slots.length = nSlots) :
    EnvMapOk (pushRegsV r₀.toRegsV) (pushTup (packContTup nSlots r₀ sp₀ slots) []) regCtx
      (if nSlots = 0 then 6 else 7 + nSlots) initEnvMap := by
  have h6 : (pushRegsV r₀.toRegsV).length = 6 := by rcases r₀ with ⟨_, _, _, _, _, _⟩; rfl
  have hLen : (pushTup (packContTup nSlots r₀ sp₀ slots) []).length =
      if nSlots = 0 then 6 else 7 + nSlots := by
    cases nSlots with | zero => exact h6 | succ k =>
      rw [ite_eq_right (Nat.succ_ne_zero k), pushTup_packContTup_succ,
        (cLevelVal_pushTup_packSlotTup (k + 1) slots (⟨i64, sp₀⟩ :: pushRegsV r₀.toRegsV)
          (hSLen (Nat.zero_lt_succ k))).1, List.length_cons, h6]
  refine ⟨hLen, by rcases r₀ with ⟨_, _, _, _, _, _⟩; rfl, rfl, fun idx hi => ?_⟩; rw [h6] at hi
  refine ⟨5 - idx, by cases nSlots <;> simp <;> omega, listGet?_initEnvMap idx hi, fun t' => ?_⟩
  rw [show (if nSlots = 0 then 6 else 7 + nSlots) - 1 - (5 - idx) =
      (if nSlots = 0 then 0 else nSlots + 1) + idx by cases nSlots <;> simp <;> omega]
  cases nSlots with
  | zero => simp only [↓reduceIte, Nat.zero_add, packContTup]; rfl
  | succ k =>
      rw [ite_eq_right (Nat.succ_ne_zero k), pushTup_packContTup_succ]
      have hlen2 : (pushTup (packSlotTup (k + 1) slots) [⟨i64, sp₀⟩]).length = (k + 1) + 1 := by
        rw [pushTup_length, List.length_replicate, List.length_cons, List.length_nil]
      rw [show (⟨i64, sp₀⟩ :: pushRegsV r₀.toRegsV) = [⟨i64, sp₀⟩] ++ pushRegsV r₀.toRegsV from rfl,
        pushTup_append (packSlotTup (k + 1) slots) [⟨i64, sp₀⟩] (pushRegsV r₀.toRegsV)]
      dsimp only [lookupV]
      rw [show pushRegsV r₀.toRegsV = pushTup r₀.toRegsV.toTup [] from rfl, ← hlen2,
        listGet?_append_skip]

private theorem listGet?_range_add7 : ∀ (m idx : Nat), idx < m →
    listGet? ((List.range m).map (· + 7)) idx = some (idx + 7)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | m + 1, idx, h => by
      rw [List.range_succ, List.map_append]; by_cases he : idx = m
      · subst he; have h0 := listGet?_append_skip ((List.range idx).map (· + 7)) [idx + 7] 0
        rw [List.length_map, List.length_range] at h0; exact h0
      · rw [listGet?_append_left _ _ (by simp; omega)]; exact listGet?_range_add7 m idx (by omega)

private theorem packContTup_frame_ok (nSlots : Nat) (r : Regs) (sp₀ : BitVec 64)
    (slots : List (BitVec 64)) (hsLen : nSlots > 0 → slots.length = nSlots) :
    (nSlots > 0 → 6 < (if nSlots = 0 then 6 else 7 + nSlots) ∧
      cLevelVal (t := i64) (pushTup (packContTup nSlots r sp₀ slots) []) 6 = some sp₀) ∧
    (nSlots > 0 → SlotsLvlsOk (pushTup (packContTup nSlots r sp₀ slots) [])
      (if nSlots = 0 then 6 else 7 + nSlots) (initSlotsLvls nSlots) slots ∧
      slots.length = nSlots) :=
  let h6 : (pushRegsV r.toRegsV).length = 6 := by rcases r with ⟨_, _, _, _, _, _⟩; rfl
  ⟨fun hPos => by cases nSlots with | zero => exact absurd rfl (Nat.ne_of_gt hPos) | succ k =>
    refine ⟨by simp only [ite_eq_right (Nat.succ_ne_zero k)]; omega, ?_⟩
    rw [pushTup_packContTup_succ]
    exact (cLevelVal_pushTup_packSlotTup (k + 1) slots (⟨i64, sp₀⟩ :: pushRegsV r.toRegsV)
      (hsLen hPos)).2.1 6 sp₀ (by simp [h6]) (by
        dsimp only [cLevelVal, lookupV, listGet?]
        rw [ite_eq_left (by simp [h6]), List.length_cons, h6]; rfl),
   fun hPos => by
    have hLen' : slots.length = nSlots := hsLen hPos
    have hBase := (envMapOk_init r sp₀ slots nSlots (fun _ => hLen')).1
    refine ⟨⟨hBase, by simp [initSlotsLvls, hLen'], fun j hj => ?_⟩, hLen'⟩
    cases nSlots with | zero => exact absurd rfl (Nat.ne_of_gt hPos) | succ k =>
      simp only [ite_eq_right (Nat.succ_ne_zero k)]
      obtain ⟨v, hv, hcv⟩ := (cLevelVal_pushTup_packSlotTup (k + 1) slots
        (⟨i64, sp₀⟩ :: pushRegsV r.toRegsV) hLen').2.2 j (by omega)
      refine ⟨j + 7, by omega,
        by dsimp only [initSlotsLvls]; exact listGet?_range_add7 (k + 1) j (by omega),
        fun w hw => by
          rw [hv] at hw; cases hw; rw [pushTup_packContTup_succ]
          simpa [pushTup, h6, Nat.add_comm 7 j] using hcv⟩⟩

theorem liftContifyBlock_wp_init {abi : RegionAbi} {pf : PrivFrameCfg}
    {Γ : Env} {X : XPost} {Ψ_bail Pred Ψ_step : CodeSpec} {H : HaltPost}
    {cm : CodeMap} {callees : List ContCalleeMeta} {rw : RegionWitness}
    {pcs : List (BitVec 64)} {ls : List ((ts : List Ty) × Cont ts)}
    (hls : ContLsMatch pf.numSlots pcs ls Pred) (pc : BitVec 64) (r : Regs)
    (slots : List (BitVec 64)) (hAbiZero : pf.numSlots > 0 → abi = .retEnvelope)
    (hH : ∀ c m', H c m' → X haltSym [i64] (c, ()) m') (reqSp : Bool)
    (hStepPred : ∀ pc' s', (findLabelIdx pcs pc').isSome = true →
      (abi.isContified = true → s'.regs.rp = r.rp) →
      (reqSp = true → s'.regs.sp = r.sp) → Ψ_step pc' s' → Pred pc' s')
    (hStepBail : ∀ pc' s', (abi.isContified = true → reqSp = true → s'.regs.sp = r.sp) →
      Ψ_step pc' s' → Ψ_bail pc' s')
    (hStepCall : ∀ callee calleePc dualRet (nxtR : Regs) mConc' mPub' retPc altRetPc?,
      abi.isContified = false → callees.any (fun c => (c.name == callee) &&
        (c.entryPc == calleePc) && (c.dualRet == dualRet)) = true →
      (pf.numSlots > 0 → callees.any (fun c => (c.name == callee) &&
        (c.entryPc == calleePc) && c.memFree) = true) →
      cm.addrOf? callee = some calleePc → nxtR.rp = retPc →
      (if dualRet then altRetPc? = some (retPc + 8#64) else altRetPc?.isNone) →
      (findLabelIdx pcs retPc).isSome = true →
      (if dualRet then (findLabelIdx pcs (retPc + 8#64)).isSome = true else True) →
      (pf.numSlots > 0 → nxtR.sp = r.sp) →
      Ψ_step calleePc ⟨nxtR, mConc'⟩ → ∀ slots', FrameRel pf.numSlots r.sp slots' mConc' mPub' →
      ∃ P E, Γ callee regSig (RegionAbi.contified dualRet).retSig nxtR.toRegsV.toTup mPub' P E ∧
        (∀ r' m'', P r' m'' → ∃ mConc'',
          (pf.numSlots > 0 → contRetSp dualRet r' = r.sp) ∧
          FrameRel pf.numSlots r.sp slots' mConc'' m'' ∧
          retContPost dualRet Pred retPc r' mConc'') ∧
        (∀ g cs xs m'', E g cs xs m'' → X g cs xs m''))
    (b : BlockFlat) (leaves : List ContSymLeaf) (mConc mPub : Mem 64)
    (hfr : FrameRel pf.numSlots r.sp slots mConc mPub) (hwf : b.wfCheck regCtx = true)
    (hno : b.noHlt = true) (hsym : symEvalContBlock cm pf b [] ContSymState.init = some leaves)
    (hreq : reqSp = true → pf.numSlots > 0 ∨
      ∀ lf ∈ leaves, (lf.st.evalArg lf.nextRegs.sp == .spOffset 0#64) = true)
    (hleaves : ∀ lf ∈ leaves, ∃ ew, rw.findEdge pc lf.path = some ew ∧
      checkContEdgeLeaf cm abi pf callees pcs lf ew.kind = true)
    (hbp : b.wp cm.symEnv Ψ_step H (pushRegsV r.toRegsV) mConc) :
    wp Γ (regionRetPost abi Ψ_bail r.rp) X (denote Val Cont (liftContifyBlock cm abi pf rw pcs pc
      b [] ContSymState.init (if pf.numSlots = 0 then 6 else 7 + pf.numSlots) initEnvMap
      (initSlotsLvls pf.numSlots)) (pushTup (packContTup pf.numSlots r r.sp slots) []) ls)
      mPub := by
  have hsLen : pf.numSlots > 0 → slots.length = pf.numSlots := fun hPos => by
    have hf := hfr; dsimp only [FrameRel] at hf
    rw [ite_eq_right (Nat.ne_of_gt hPos)] at hf; exact hf.1
  have hpf := packContTup_frame_ok pf.numSlots r r.sp slots hsLen
  simpa using liftContifyBlock_wp hls pc r.sp r.rp hAbiZero hH reqSp hStepPred hStepBail hStepCall
    b [] ContSymState.init (pushRegsV r.toRegsV) (pushTup (packContTup pf.numSlots r r.sp slots) [])
    [] (if pf.numSlots = 0 then 6 else 7 + pf.numSlots) initEnvMap (initSlotsLvls pf.numSlots)
    leaves slots mConc mPub (envMapOk_init r r.sp slots pf.numSlots hsLen) (contSymStateOk_init r)
    hpf.1 hpf.2 (fun h0 => by simp [h0, initSlotsLvls]) hfr hwf hno hsym hreq hleaves hbp

/-! ## §4. Park's Induction, Canonical Nested `GroupTree` GFP & Mem-Relocation Step -/

private def diagCtxOfV : List ((t : Ty) × Val t) → Ctx Val Val :=
  List.map fun ⟨t, v⟩ => ⟨t, v, v⟩
private def diagCtxOfL : List ((ts : List Ty) × Cont ts) → Ctx Cont Cont :=
  List.map fun ⟨ts, l⟩ => ⟨ts, l, l⟩

private theorem ctxRel_diagV : (vs : List ((t : Ty) × Val t)) → CtxRel (diagCtxOfV vs) vs vs
  | [] => .nil
  | _ :: vs => .cons (.head _) ((ctxRel_diagV vs).mono fun _ hp => .tail _ hp)

private theorem diagV_diagCtx : (vs : List ((t : Ty) × Val t)) → DiagV (diagCtxOfV vs)
  | [], _, h => nomatch h
  | _ :: vs, p, hp => by cases hp with | head => rfl | tail _ hp => exact diagV_diagCtx vs p hp

private theorem ctxRel_diagL : (ls : List ((ts : List Ty) × Cont ts)) → CtxRel (diagCtxOfL ls) ls ls
  | [] => .nil
  | _ :: ls => .cons (.head _) ((ctxRel_diagL ls).mono fun _ hp => .tail _ hp)

private theorem monoD_diagL : (ls : List ((ts : List Ty) × Cont ts)) → MonoD (diagCtxOfL ls)
  | [], _, h => nomatch h
  | _ :: ls, p, hp => by
      cases hp with | head => exact fun _ _ h => h | tail _ hp => exact monoD_diagL ls p hp

private theorem park_induction {α : Type} {F : Xcap.Lfp.Pred α → Xcap.Lfp.Pred α}
    (hMono : Xcap.Lfp.mono F) {P : Xcap.Lfp.Pred α}
    (hStep : ∀ a, F (fun x => Xcap.Lfp.lfp F x ∧ P x) a → P a) : ∀ a, Xcap.Lfp.lfp F a → P a := by
  intro a ha
  have hClosed : Xcap.Lfp.Closed F (fun x => Xcap.Lfp.lfp F x ∧ P x) := fun x hx =>
    ⟨Xcap.Lfp.lfp_closed hMono x (hMono (fun _ h => h.1) x hx), hStep x hx⟩
  exact (Xcap.Lfp.lfp_le hClosed a ha).2

mutual
private def treeSize : GroupTree → Nat | .leaf _ => 1 | .loop _ ns => 1 + treeListSize ns
private def treeListSize : List GroupTree → Nat
  | [] => 1 | g :: gs => 1 + treeSize g + treeListSize gs
end

private theorem treeListSize_mem (g : GroupTree) :
    ∀ gs, g ∈ gs → treeSize g < treeListSize gs
  | [], h => by cases h
  | x :: gs, h => by
      rcases List.mem_cons.1 h with rfl | h'
      · simp only [treeListSize]; omega
      · have ih := treeListSize_mem g gs h'; simp only [treeListSize]; omega

mutual
private def canonContifyNodePred (cm : CodeMap) (cr : ContifyRegion) (Γ : Env)
    (Q : Post cr.abi.retSig) (X : XPost) (pcs' : List (BitVec 64))
    (ls' : List ((ts : List Ty) × Cont ts)) :
    GroupTree → Cont (contSig cr.privFrame.numSlots) → CodeSpec
  | .leaf pc₀, J, pc, st => pc = pc₀ → ∀ sp₀ slots mPub,
      (cr.privFrame.numSlots > 0 → st.regs.sp = sp₀) →
      FrameRel cr.privFrame.numSlots sp₀ slots st.mem mPub →
      J (packContTup cr.privFrame.numSlots st.regs sp₀ slots) mPub
  | .loop header nodes, J, pc, st =>
      (pc = header → ∀ sp₀ slots mPub, (cr.privFrame.numSlots > 0 → st.regs.sp = sp₀) →
        FrameRel cr.privFrame.numSlots sp₀ slots st.mem mPub →
        J (packContTup cr.privFrame.numSlots st.regs sp₀ slots) mPub) ∧
      let pcs'' := pushLabelPcs (nodes.map GroupTree.entryPc) pcs'
      let Js := lfp Γ Q X (fun Jv =>
        denoteB Val Cont (liftContifyGroupNodes cm cr pcs'' nodes) [] (pushTup Jv ls'))
      canonContifyTupPred cm cr Γ Q X pcs'' (pushTup Js ls') nodes Js pc st

private def canonContifyTupPred (cm : CodeMap) (cr : ContifyRegion) (Γ : Env)
    (Q : Post cr.abi.retSig) (X : XPost) (pcs' : List (BitVec 64))
    (ls' : List ((ts : List Ty) × Cont ts)) :
    (gs : List GroupTree) → Tup Cont (gs.map fun _ => contSig cr.privFrame.numSlots) → CodeSpec
  | [], (), _, _ => True
  | g :: gs, (J, Js), pc, st =>
      canonContifyNodePred cm cr Γ Q X pcs' ls' g J pc st ∧
      canonContifyTupPred cm cr Γ Q X pcs' ls' gs Js pc st
end

private def canonContifyNodesPred (cm : CodeMap) (cr : ContifyRegion) (Γ : Env)
    (Q : Post cr.abi.retSig) (X : XPost) (gs : List GroupTree) (pcsOuter : List (BitVec 64))
    (lsOuter : List ((ts : List Ty) × Cont ts)) : CodeSpec :=
  let pcs' := pushLabelPcs (gs.map GroupTree.entryPc) pcsOuter
  let Js := lfp Γ Q X (fun Jv =>
    denoteB Val Cont (liftContifyGroupNodes cm cr pcs' gs) [] (pushTup Jv lsOuter))
  canonContifyTupPred cm cr Γ Q X pcs' (pushTup Js lsOuter) gs Js

private def contMemberOfPrefix (nSlots : Nat) : (gsPre : List GroupTree) → (g : GroupTree) →
    (gsPost : List GroupTree) → Member (contSig nSlots) ((gsPre ++ g :: gsPost).map fun _ =>
      contSig nSlots)
  | [], _, _ => .here | _ :: gsPre, g, gsPost => .there (contMemberOfPrefix nSlots gsPre g gsPost)

private theorem denoteB_get_contMemberOfPrefix {V : Ty → Type} {L : List Ty → Type} (cm : CodeMap)
    (cr : ContifyRegion) (pcs : List (BitVec 64)) (vs : List ((t : Ty) × V t))
    (ls : List ((ts : List Ty) × L ts)) (xs : Tup V (contSig cr.privFrame.numSlots)) :
    ∀ (gsPre : List GroupTree) (g : GroupTree) (gsPost : List GroupTree),
      (denoteB V L (liftContifyGroupNodes cm cr pcs (gsPre ++ g :: gsPost)) vs ls).get
        (contMemberOfPrefix cr.privFrame.numSlots gsPre g gsPost) xs =
      denote V L (liftContifyGroupNode cm cr pcs g) (pushTup xs vs) ls
  | [], _, _ => rfl
  | _ :: gsPre, g, gsPost => denoteB_get_contMemberOfPrefix cm cr pcs vs ls xs gsPre g gsPost

private theorem canonContifyTupPred_get {cm : CodeMap} {cr : ContifyRegion} {Γ : Env}
    {Q : Post cr.abi.retSig} {X : XPost} {pcs' : List (BitVec 64)}
    {ls' : List ((ts : List Ty) × Cont ts)} :
    ∀ (gsPre : List GroupTree) (g : GroupTree) (gsPost : List GroupTree)
      (Js : Tup Cont ((gsPre ++ g :: gsPost).map fun _ => contSig cr.privFrame.numSlots)) {pc st},
      canonContifyTupPred cm cr Γ Q X pcs' ls' (gsPre ++ g :: gsPost) Js pc st →
      canonContifyNodePred cm cr Γ Q X pcs' ls' g
        (Js.get (contMemberOfPrefix cr.privFrame.numSlots gsPre g gsPost)) pc st
  | [], _, _, (_, _), _, _, h => h.1
  | _ :: gsPre, g, gsPost, (_, Js), _, _, h => canonContifyTupPred_get gsPre g gsPost Js h.2

private theorem contTupGet_cons_eq {nSlots : Nat} {g : GroupTree} {gs gsPre : List GroupTree}
    {g' : GroupTree} {gsPost : List GroupTree} (heq : gs = gsPre ++ g' :: gsPost)
    (heq' : g :: gs = (g :: gsPre) ++ g' :: gsPost) (J : Cont (contSig nSlots))
    (Js : Tup Cont (gs.map fun _ => contSig nSlots)) :
    Tup.get (a := contSig nSlots) (as := (g :: gs).map fun _ => contSig nSlots) (J, Js)
      (heq' ▸ contMemberOfPrefix nSlots (g :: gsPre) g' gsPost) =
    Js.get (heq ▸ contMemberOfPrefix nSlots gsPre g' gsPost) := by subst heq; rfl

private theorem canonContifyTupPred_get_eq {cm : CodeMap} {cr : ContifyRegion} {Γ : Env}
    {Q : Post cr.abi.retSig} {X : XPost} {pcs' : List (BitVec 64)}
    {ls' : List ((ts : List Ty) × Cont ts)} {gs : List GroupTree}
    (gsPre : List GroupTree) (g : GroupTree) (gsPost : List GroupTree)
    (heq : gs = gsPre ++ g :: gsPost)
    (Js : Tup Cont (gs.map fun _ => contSig cr.privFrame.numSlots)) {pc st}
    (h : canonContifyTupPred cm cr Γ Q X pcs' ls' gs Js pc st) :
    canonContifyNodePred cm cr Γ Q X pcs' ls' g
      (Js.get (heq ▸ contMemberOfPrefix cr.privFrame.numSlots gsPre g gsPost)) pc st := by
  subst heq; exact canonContifyTupPred_get gsPre g gsPost Js h

private theorem canonContifyTupPred_of_forall {cm : CodeMap} {cr : ContifyRegion} {Γ : Env}
    {Q : Post cr.abi.retSig} {X : XPost} {pcs' : List (BitVec 64)}
    {ls' : List ((ts : List Ty) × Cont ts)} {pc st} :
    ∀ (gs : List GroupTree) (Js : Tup Cont (gs.map fun _ => contSig cr.privFrame.numSlots)),
      (∀ gsPre g gsPost (h : gs = gsPre ++ g :: gsPost),
        canonContifyNodePred cm cr Γ Q X pcs' ls' g
          (Js.get (h ▸ contMemberOfPrefix cr.privFrame.numSlots gsPre g gsPost)) pc st) →
      canonContifyTupPred cm cr Γ Q X pcs' ls' gs Js pc st
  | [], (), _ => trivial
  | g :: gs, (J, Js), h =>
      ⟨h [] g gs rfl, canonContifyTupPred_of_forall gs Js fun gsPre g' gsPost heq => by
        have h0 := h (g :: gsPre) g' gsPost (by rw [heq]; rfl)
        rwa [contTupGet_cons_eq heq (by rw [heq]; rfl) J Js] at h0⟩

private theorem canonContifyTupPred_tupMemPred {cm : CodeMap} {cr : ContifyRegion} {Γ : Env}
    {Q : Post cr.abi.retSig} {X : XPost} {pcs' : List (BitVec 64)}
    {ls' : List ((ts : List Ty) × Cont ts)} {Pred : CodeSpec} :
    ∀ (gs : List GroupTree) (Js : Tup Cont (gs.map fun _ => contSig cr.privFrame.numSlots)),
      (∀ g ∈ gs, ∀ r m, Pred g.entryPc ⟨r, m⟩ →
        canonContifyTupPred cm cr Γ Q X pcs' ls' gs Js g.entryPc ⟨r, m⟩) →
      ContTupMemPred cr.privFrame.numSlots gs Js Pred
  | [], (), _ => trivial
  | .leaf pc₀ :: gs, (_, Js), h =>
      ⟨fun r sp₀ slots mConc mPub hSp hfr hP =>
          (h (.leaf pc₀) (.head _) r mConc hP).1 rfl sp₀ slots mPub hSp hfr,
       canonContifyTupPred_tupMemPred gs Js fun g hg r m hP => (h g (.tail _ hg) r m hP).2⟩
  | .loop hd ns :: gs, (_, Js), h =>
      ⟨fun r sp₀ slots mConc mPub hSp hfr hP =>
          (h (.loop hd ns) (.head _) r mConc hP).1.1 rfl sp₀ slots mPub hSp hfr,
       canonContifyTupPred_tupMemPred gs Js fun g hg r m hP => (h g (.tail _ hg) r m hP).2⟩

private theorem castListTy_self' (ts : List Ty) (l : Cont ts) : castListTy ts ts l = some l := by
  dsimp only [castListTy]; cases h : listTyDecEq ts ts with
  | isFalse hne => exact absurd rfl hne | isTrue heq => have h' : heq = rfl := rfl; rw [h']

private theorem findContLabel_pushTup {nSlots : Nat} :
    ∀ (gs : List GroupTree) (Js : Tup Cont (gs.map fun _ => contSig nSlots))
      (pcs : List (BitVec 64)) (ls : List ((ts : List Ty) × Cont ts))
      (Pred : CodeSpec) (r : Regs) (sp₀ : BitVec 64) (slots : List (BitVec 64))
      (mConc mPub : Mem 64) (p : BitVec 64),
      ContTupMemPred nSlots gs Js Pred → (nSlots > 0 → r.sp = sp₀) →
      FrameRel nSlots sp₀ slots mConc mPub → (p ∈ gs.map GroupTree.entryPc → Pred p ⟨r, mConc⟩) →
      (p ∈ gs.map GroupTree.entryPc ∨ ∃ idx, findLabelIdx pcs p = some idx ∧
        ∃ J, lookupL ls (contSig nSlots) idx = some J ∧ J (packContTup nSlots r sp₀ slots) mPub) →
      ∃ idx J, findLabelIdx (pushLabelPcs (gs.map GroupTree.entryPc) pcs) p = some idx ∧
        lookupL (pushTup Js ls) (contSig nSlots) idx = some J ∧
        J (packContTup nSlots r sp₀ slots) mPub
  | [], (), _, _, _, _, _, _, _, _, _, _, _, _, _, .inl hp => by cases hp
  | [], (), _, _, _, _, _, _, _, _, _, _, _, _, _, .inr h => by
      simpa [List.map, pushLabelPcs, pushTup] using h
  | g :: gs, (J, Js), pcs, ls, Pred, r, sp₀, slots, mConc, mPub, p, ⟨hJ, hR⟩, hSp, hfr, hP,
      hIn => by
      apply findContLabel_pushTup gs Js (g.entryPc :: pcs) (⟨contSig nSlots, J⟩ :: ls) Pred
        r sp₀ slots mConc mPub p hR hSp hfr (fun hm => hP (.tail _ hm))
      by_cases heq : g.entryPc = p
      · subst heq
        refine .inr ⟨0, by simp [findLabelIdx], J, ?_,
          hJ r sp₀ slots mConc mPub hSp hfr (hP (.head _))⟩
        dsimp only [lookupL, listGet?]; exact castListTy_self' (contSig nSlots) J
      · rcases hIn with hp | ⟨idx, hidx, J₀, hL₀, hJ₀⟩
        · exact (List.mem_cons.1 hp).elim (fun h' => absurd h'.symm heq) .inl
        · refine .inr ⟨idx + 1, ?_, J₀, hL₀, hJ₀⟩
          dsimp only [findLabelIdx]; simp [beq_false_of_ne heq, hidx]

private theorem denote_lowerContJumpTo_base {rs : List Ty} {Γ : Env} {Q : Post rs} {X : XPost}
    {nSlots : Nat} (gs : List GroupTree) (Js : Tup Cont (gs.map fun _ => contSig nSlots))
    (pcs : List (BitVec 64)) (ls : List ((ts : List Ty) × Cont ts)) (Pred : CodeSpec)
    (r : Regs) (sp₀ : BitVec 64) (slots : List (BitVec 64)) (mConc mPub : Mem 64)
    (p : BitVec 64) (hMem : ContTupMemPred nSlots gs Js Pred) (hpIn : p ∈ gs.map GroupTree.entryPc)
    (hSp : nSlots > 0 → r.sp = sp₀) (hfr : FrameRel nSlots sp₀ slots mConc mPub)
    (hP : Pred p ⟨r, mConc⟩) :
    wp Γ Q X (denote Val Cont (lowerContJumpTo (rs := rs) nSlots
        (pushLabelPcs (gs.map GroupTree.entryPc) pcs) p (baseContArgs nSlots))
      (pushTup (packContTup nSlots r sp₀ slots) []) (pushTup Js ls)) mPub := by
  have hsLen : nSlots > 0 → slots.length = nSlots := fun hPos => by
    have hf := hfr; dsimp only [FrameRel] at hf; rw [ite_eq_right (Nat.ne_of_gt hPos)] at hf
    exact hf.1
  obtain ⟨j, J, hj, hL, hJ⟩ := findContLabel_pushTup gs Js pcs ls Pred r sp₀ slots mConc mPub p
    hMem hSp hfr (fun _ => hP) (.inl hpIn)
  have hpf := packContTup_frame_ok nSlots r sp₀ slots hsLen
  let d0 := if nSlots = 0 then 6 else 7 + nSlots
  let rBase : RegsExpr K := ⟨.var (d0 - 1 - 0), .var (d0 - 1 - 1), .var (d0 - 1 - 2),
    .var (d0 - 1 - 3), .var (d0 - 1 - 4), .var (d0 - 1 - 5)⟩
  have hNxt : denoteRegsExpr (pushTup (packContTup nSlots r sp₀ slots) [] ++ []) rBase =
      some ⟨.var r.sp, .var r.rp, .var r.rv, .var r.r1, .var r.r2, .var r.r3⟩ := by
    let e0 : RegsExpr K := ⟨.var 5, .var 4, .var 3, .var 2, .var 1, .var 0⟩
    have hB : denoteRegsExpr (pushRegsV r.toRegsV) e0 =
        some ⟨.var r.sp, .var r.rp, .var r.rv, .var r.r1, .var r.r2, .var r.r3⟩ := by
      rcases r with ⟨_, _, _, _, _, _⟩; rfl
    have hChk : checkRegsExpr regCtx e0 = true := rfl
    have hRm := denoteRegsExpr_remap (vsTail := []) (envMapOk_init r sp₀ slots nSlots hsLen) hChk
    simpa [d0, rBase, e0, remapRegsExpr, remapArg, initEnvMap, listGet?] using hRm.trans hB
  obtain ⟨args', hargs', hvals⟩ := denote_mkJumpTuple
    (envMapOk_init r sp₀ slots nSlots hsLen).1 hNxt hpf.1 hpf.2
  have hev : (⟨.var r.sp, .var r.rp, .var r.rv, .var r.r1, .var r.r2, .var r.r3⟩ :
      RegsExpr Val).eval = r := by rcases r with ⟨_, _, _, _, _, _⟩; rfl
  dsimp only [lowerContJumpTo]; rw [hj]; dsimp only [denote]; rw [hL]
  have hA' : denoteArgs (pushTup (packContTup nSlots r sp₀ slots) []) (baseContArgs nSlots) =
      some args' := by simpa [baseContArgs, d0, rBase] using hargs'
  rw [hA']; dsimp only [wp]; rw [hvals, hev]; exact hJ

private theorem contify_lfp_q_ls_mono {cm : CodeMap} {cr : ContifyRegion} {Γ : Env}
    {Q₁ Q₂ : Post cr.abi.retSig} {X : XPost} (hQ : ∀ vs m, Q₁ vs m → Q₂ vs m)
    {pcs : List (BitVec 64)} (gs : List GroupTree)
    {ls₁ ls₂ : List ((ts : List Ty) × Cont ts)} {D : Ctx Cont Cont}
    (hD : MonoD D) (hRel : CtxRel D ls₁ ls₂) :
    ∀ {ts} (i : Member ts (gs.map fun _ => contSig cr.privFrame.numSlots)) xs m,
      (lfp Γ Q₁ X (fun Jv => denoteB Val Cont (liftContifyGroupNodes cm cr pcs gs) []
        (pushTup Jv ls₁))).get i xs m →
      (lfp Γ Q₂ X (fun Jv => denoteB Val Cont (liftContifyGroupNodes cm cr pcs gs) []
        (pushTup Jv ls₂))).get i xs m := by
  intro ts i xs m h; rw [lfp_get] at h ⊢; intro Js hcl; apply h Js
  rw [closed_iff] at hcl ⊢; intro ts' j ys m' hb; apply hcl j ys m'
  have hwf := (denoteB_wf (liftContifyGroupNodes cm cr pcs gs) (G := ([] : Ctx Val Val))
    (@CtxRel.nil Ty Val Val []) (ctxRel_pushTup Js Js hRel)).get j ys ys
  exact wp_mono hQ (fun _ _ _ _ h => h) _ m'
    (wp_label_mono hwf (DiagV.append DiagV.nil ys) ((mono_zip_self Js).append hD) m' hb)

mutual
private theorem canonContifyNodePred_mono {cm : CodeMap} {cr : ContifyRegion} {Γ : Env}
    {Q₁ Q₂ : Post cr.abi.retSig} {X : XPost} (hQ : ∀ vs m, Q₁ vs m → Q₂ vs m)
    {pcs' : List (BitVec 64)} {ls₁ ls₂ : List ((ts : List Ty) × Cont ts)}
    {D : Ctx Cont Cont} (hD : MonoD D) (hRel : CtxRel D ls₁ ls₂) :
    ∀ (g : GroupTree) {J₁ J₂ : Cont (contSig cr.privFrame.numSlots)},
      (∀ xs m, J₁ xs m → J₂ xs m) → ∀ pc st, canonContifyNodePred cm cr Γ Q₁ X pcs' ls₁ g J₁ pc st →
        canonContifyNodePred cm cr Γ Q₂ X pcs' ls₂ g J₂ pc st
  | .leaf _, _, _, hJ, _, _, h => fun heq sp₀ slots mPub hSp hfr =>
      hJ _ _ (h heq sp₀ slots mPub hSp hfr)
  | .loop _ nodes, _, _, hJ, _, _, ⟨hHd, hSub⟩ =>
      let pcs'' := pushLabelPcs (nodes.map GroupTree.entryPc) pcs'
      have hJs : ∀ {ts} (i : Member ts (nodes.map fun _ => contSig cr.privFrame.numSlots)) xs m,
          (lfp Γ Q₁ X (fun Jv => denoteB Val Cont (liftContifyGroupNodes cm cr pcs'' nodes) []
            (pushTup Jv ls₁))).get i xs m →
          (lfp Γ Q₂ X (fun Jv => denoteB Val Cont (liftContifyGroupNodes cm cr pcs'' nodes) []
            (pushTup Jv ls₂))).get i xs m := contify_lfp_q_ls_mono hQ nodes hD hRel
      ⟨fun heq sp₀ slots mPub hSp hfr => hJ _ _ (hHd heq sp₀ slots mPub hSp hfr),
       canonContifyTupPred_mono hQ ((mono_zip _ _ hJs).append hD)
         (ctxRel_pushTup _ _ hRel) nodes hJs _ _ hSub⟩

private theorem canonContifyTupPred_mono {cm : CodeMap} {cr : ContifyRegion} {Γ : Env}
    {Q₁ Q₂ : Post cr.abi.retSig} {X : XPost} (hQ : ∀ vs m, Q₁ vs m → Q₂ vs m)
    {pcs' : List (BitVec 64)} {ls₁ ls₂ : List ((ts : List Ty) × Cont ts)}
    {D : Ctx Cont Cont} (hD : MonoD D) (hRel : CtxRel D ls₁ ls₂) :
    ∀ (gs : List GroupTree) {Js₁ Js₂ : Tup Cont (gs.map fun _ => contSig cr.privFrame.numSlots)},
      (∀ {ts} (i : Member ts (gs.map fun _ => contSig cr.privFrame.numSlots)) xs m,
        Js₁.get i xs m → Js₂.get i xs m) →
      ∀ pc st, canonContifyTupPred cm cr Γ Q₁ X pcs' ls₁ gs Js₁ pc st →
        canonContifyTupPred cm cr Γ Q₂ X pcs' ls₂ gs Js₂ pc st
  | [], (), (), _, _, _, _ => trivial
  | g :: gs, (_, _), (_, _), hJs, _, _, ⟨hg, hgs⟩ =>
      ⟨canonContifyNodePred_mono hQ hD hRel g (hJs .here) _ _ hg,
       canonContifyTupPred_mono hQ hD hRel gs (fun i => hJs (.there i)) _ _ hgs⟩
end

private theorem canonContifyNodesPred_mono {cm : CodeMap} {cr : ContifyRegion} {Γ : Env}
    {Q₁ Q₂ : Post cr.abi.retSig} {X : XPost} (hQ : ∀ vs m, Q₁ vs m → Q₂ vs m)
    {pcsOuter : List (BitVec 64)} {ls₁ ls₂ : List ((ts : List Ty) × Cont ts)}
    {D : Ctx Cont Cont} (hD : MonoD D) (hRel : CtxRel D ls₁ ls₂) (gs : List GroupTree) {pc st}
    (h : canonContifyNodesPred cm cr Γ Q₁ X gs pcsOuter ls₁ pc st) :
    canonContifyNodesPred cm cr Γ Q₂ X gs pcsOuter ls₂ pc st := by
  dsimp only [canonContifyNodesPred] at h ⊢
  let pcs' := pushLabelPcs (gs.map GroupTree.entryPc) pcsOuter
  have hJs : ∀ {ts} (i : Member ts (gs.map fun _ => contSig cr.privFrame.numSlots)) xs m,
      (lfp Γ Q₁ X (fun Jv => denoteB Val Cont (liftContifyGroupNodes cm cr pcs' gs) []
        (pushTup Jv ls₁))).get i xs m →
      (lfp Γ Q₂ X (fun Jv => denoteB Val Cont (liftContifyGroupNodes cm cr pcs' gs) []
        (pushTup Jv ls₂))).get i xs m := contify_lfp_q_ls_mono hQ gs hD hRel
  exact canonContifyTupPred_mono hQ ((mono_zip _ _ hJs).append hD)
    (ctxRel_pushTup _ _ hRel) gs hJs pc st h

private def contifyRegionBailPost (cm : CodeMap) (wit : ContifyWitness) (Ψ_cold : CodeSpec)
    (H : HaltPost) (P : CodeSpec) (needSp : Bool) (sp₀ : BitVec 64) : RegionAbi → CodeSpec
  | .retEnvelope => PsiContHyb cm wit Ψ_cold H
  | .contified _ => fun pc' s' =>
      P pc' s' ∧ PsiContHyb cm wit Ψ_cold H pc' s' ∧ (needSp = true → s'.regs.sp = sp₀)

private def contifyRegionQ (cm : CodeMap) (wit : ContifyWitness) (Ψ_cold : CodeSpec)
    (H : HaltPost) (P : CodeSpec) (pre : List ContifyRegion) (cr : ContifyRegion)
    (r₀ : Regs) : Post cr.abi.retSig :=
  regionRetPost cr.abi (contifyRegionBailPost cm wit Ψ_cold H P
    (cr.abi.isContified && regionMemFree cm (contCalleesFold cm [] pre) cr) r₀.sp cr.abi) r₀.rp

private theorem contifyRegionQ_mono (cm : CodeMap) (wit : ContifyWitness) (Ψ_cold : CodeSpec)
    (H : HaltPost) {P₁ P₂ : CodeSpec} (hP : ∀ pc st, P₁ pc st → P₂ pc st)
    (pre : List ContifyRegion) (cr : ContifyRegion) (r₀ : Regs) :
    ∀ vs m, contifyRegionQ cm wit Ψ_cold H P₁ pre cr r₀ vs m →
      contifyRegionQ cm wit Ψ_cold H P₂ pre cr r₀ vs m := by
  have hg : ∀ (abi : RegionAbi) (needSp : Bool) (vs : Tup Val abi.retSig) (m : Mem 64),
      regionRetPost abi (contifyRegionBailPost cm wit Ψ_cold H P₁ needSp r₀.sp abi) r₀.rp vs m →
      regionRetPost abi (contifyRegionBailPost cm wit Ψ_cold H P₂ needSp r₀.sp abi) r₀.rp vs m :=
    fun abi needSp vs m h => by
      cases abi with
      | retEnvelope => exact h
      | contified d => cases d <;> exact ⟨hP _ _ h.1, h.2⟩
  exact fun vs m h => hg cr.abi _ vs m h

private def witContStepTrans (cm : CodeMap) (wit : ContifyWitness) (Ψ_cold : CodeSpec)
    (H : HaltPost) (X : XPost) (P : CodeSpec) : CodeSpec := fun pc st =>
  ∀ (pre : List ContifyRegion) (cr : ContifyRegion) (post : List ContifyRegion),
    wit.regions = pre ++ cr :: post → pc ∈ cr.allPcs →
    canonContifyNodesPred cm cr (witContifyEnvAux cm (fun _ _ _ _ _ _ _ => False) pre)
      (contifyRegionQ cm wit Ψ_cold H P pre cr st.regs) X cr.tree [] [] pc st

private theorem witContStepTrans_mono (cm : CodeMap) (wit : ContifyWitness) (Ψ_cold : CodeSpec)
    (H : HaltPost) (X : XPost) {P₁ P₂ : CodeSpec} (hP : ∀ pc st, P₁ pc st → P₂ pc st) :
    ∀ pc st, witContStepTrans cm wit Ψ_cold H X P₁ pc st →
      witContStepTrans cm wit Ψ_cold H X P₂ pc st :=
  fun _ st h pre cr post hEq hMem =>
    canonContifyNodesPred_mono (contifyRegionQ_mono cm wit Ψ_cold H hP pre cr st.regs)
      MonoD.nil .nil cr.tree (h pre cr post hEq hMem)

private def WitContGfp (cm : CodeMap) (wit : ContifyWitness) (Ψ_cold : CodeSpec) (H : HaltPost)
    (X : XPost) : CodeSpec := fun pc st => ∃ P : CodeSpec,
  (∀ pc' st', P pc' st' → witContStepTrans cm wit Ψ_cold H X P pc' st') ∧ P pc st

private theorem witContGfp_post (cm : CodeMap) (wit : ContifyWitness) (Ψ_cold : CodeSpec)
    (H : HaltPost) (X : XPost) {pc st} (h : WitContGfp cm wit Ψ_cold H X pc st) :
    witContStepTrans cm wit Ψ_cold H X (WitContGfp cm wit Ψ_cold H X) pc st :=
  let ⟨P, hP, hpc⟩ := h
  witContStepTrans_mono cm wit Ψ_cold H X (fun _ _ h' => ⟨P, hP, h'⟩) pc st (hP pc st hpc)

private theorem witContGfp_pre (cm : CodeMap) (wit : ContifyWitness) (Ψ_cold : CodeSpec)
    (H : HaltPost) (X : XPost) {pc st}
    (h : witContStepTrans cm wit Ψ_cold H X (WitContGfp cm wit Ψ_cold H X) pc st) :
    WitContGfp cm wit Ψ_cold H X pc st :=
  ⟨fun pc' st' => WitContGfp cm wit Ψ_cold H X pc' st' ∨
      witContStepTrans cm wit Ψ_cold H X (WitContGfp cm wit Ψ_cold H X) pc' st',
   fun _ _ hq => witContStepTrans_mono cm wit Ψ_cold H X (fun _ _ h' => .inl h') _ _
      (hq.elim (witContGfp_post cm wit Ψ_cold H X) id), .inr h⟩

private theorem witContGfp_outside (cm : CodeMap) (wit : ContifyWitness) (Ψ_cold : CodeSpec)
    (H : HaltPost) (X : XPost) {pc st}
    (hOut : ¬ (wit.regions.flatMap ContifyRegion.allPcs).contains pc = true) :
    WitContGfp cm wit Ψ_cold H X pc st :=
  witContGfp_pre cm wit Ψ_cold H X fun pre cr post hEq hMem =>
    absurd (List.contains_iff_mem.2 (List.mem_flatMap.2 ⟨cr, by rw [hEq]; simp, hMem⟩)) hOut

private theorem contify_mem_allPcs_of_split {wit : ContifyWitness} {pre : List ContifyRegion}
    {cr : ContifyRegion} {post : List ContifyRegion} (hEq : wit.regions = pre ++ cr :: post)
    {pc : BitVec 64} (h : pc ∈ cr.allPcs) :
    (wit.regions.flatMap ContifyRegion.allPcs).contains pc = true :=
  List.contains_iff_mem.2 (List.mem_flatMap.2 ⟨cr, by rw [hEq]; simp, h⟩)

private theorem contifyRegionAllPcs_mem_of_tree {cr : ContifyRegion} {g : GroupTree}
    (hg : g ∈ cr.tree) {pc : BitVec 64} (hpc : pc ∈ g.allPcs) : pc ∈ cr.allPcs :=
  List.mem_flatMap.2 ⟨g, hg, hpc⟩

private theorem canonContifyNodesPred_of_outside_all {cm : CodeMap} {cr : ContifyRegion} {Γ : Env}
    {Q : Post cr.abi.retSig} {X : XPost} {callees : List ContCalleeMeta} {pc : BitVec 64}
    {st : State} :
    ∀ (gs : List GroupTree) (pcsOuter : List (BitVec 64))
      (lsOuter : List ((ts : List Ty) × Cont ts)),
      checkContGroupNodes cm cr callees (pushLabelPcs (gs.map GroupTree.entryPc) pcsOuter) gs =
        true →
      pc ∉ gs.flatMap GroupTree.allPcs → canonContifyNodesPred cm cr Γ Q X gs pcsOuter lsOuter pc st
  | gs, pcsOuter, lsOuter, hchk, hNot => by
      dsimp only [canonContifyNodesPred]
      apply canonContifyTupPred_of_forall; intro gsPre g gsPost heq
      have hgMem : g ∈ gs := by rw [heq]; simp
      have hgChk := checkContGroupNodes_forall cm cr callees _ gs hchk g hgMem
      have hgNot : pc ∉ g.allPcs := fun hp => hNot (List.mem_flatMap.2 ⟨g, hgMem, hp⟩)
      have hEntMem := checkContGroupNode_entryPc_mem cm cr callees _ g hgChk
      cases g with
      | leaf pc₁ => intro hEq _ _ _ _ _; rw [hEq] at hgNot; exact absurd hEntMem hgNot
      | loop header nodes =>
          dsimp only [canonContifyNodePred]
          refine ⟨fun hEq _ _ _ _ _ => absurd (hEq ▸ hEntMem) hgNot, ?_⟩
          dsimp only [checkContGroupNode] at hgChk; simp only [Bool.and_eq_true] at hgChk
          exact canonContifyNodesPred_of_outside_all nodes _ _ hgChk.2
            (by simpa [GroupTree.allPcs] using hgNot)
termination_by gs _ _ => treeListSize gs
decreasing_by
  have h := treeListSize_mem (.loop header nodes) gs hgMem
  simp only [treeSize] at h; omega

private theorem contifyRegionSpec_from_canonNodes {cm : CodeMap} {cr : ContifyRegion} {Γ : Env}
    {Q : Post cr.abi.retSig} {X : XPost} {callees : List ContCalleeMeta}
    (hn : cr.privFrame.numSlots ≤ 64)
    (hChk : checkContGroupNodes cm cr callees (pushLabelPcs (cr.tree.map GroupTree.entryPc) [])
      cr.tree = true)
    (hEnt : cr.entryPc ∈ cr.tree.map GroupTree.entryPc) (r₀ : Regs) (m : Mem 64)
    (hPriv : PrivFrameOk cr.privFrame.numSlots r₀.sp m)
    (hCan : canonContifyNodesPred cm cr Γ Q X cr.tree [] [] cr.entryPc ⟨r₀, m⟩) :
    Func.spec Γ (liftContifyRegion cm cr).body r₀.toRegsV.toTup m Q X := by
  dsimp only [Func.spec, Func.wp, liftContifyRegion, denoteFunc, liftContifyTFlat]
  refine loadEntryFrameAux_wp hn r₀ m hPriv fun slots bvsFinal _ hFr ⟨args', hArgs', hVals⟩ => ?_
  dsimp only [denote]
  have hPref : ∀ Jv : Tup Cont (cr.tree.map fun _ => contSig cr.privFrame.numSlots),
      denoteB Val Cont (liftContifyGroupNodes cm cr
        (pushLabelPcs (cr.tree.map GroupTree.entryPc) []) cr.tree) bvsFinal (pushTup Jv []) =
      denoteB Val Cont (liftContifyGroupNodes cm cr
        (pushLabelPcs (cr.tree.map GroupTree.entryPc) []) cr.tree) [] (pushTup Jv []) := fun Jv =>
    denote_liftContifyGroupNodes_prefix _ cr.tree hChk _ _
  simp only [hPref]
  have hWfB : ∀ J₁ J₂ : Tup Cont (cr.tree.map fun _ => contSig cr.privFrame.numSlots),
      WfB (diagCtxOfV bvsFinal) (Tup.zip J₁ J₂ ++ [])
        (denoteB Val Cont (liftContifyGroupNodes cm cr
          (pushLabelPcs (cr.tree.map GroupTree.entryPc) []) cr.tree) [] (pushTup J₁ []))
        (denoteB Val Cont (liftContifyGroupNodes cm cr
          (pushLabelPcs (cr.tree.map GroupTree.entryPc) []) cr.tree) [] (pushTup J₂ [])) :=
    fun J₁ J₂ => denoteB_wf _ CtxRel.nil (ctxRel_pushTup J₁ J₂ .nil)
  have hWfK : ∀ J₁ J₂ : Tup Cont (cr.tree.map fun _ => contSig cr.privFrame.numSlots),
      Wf (rs := cr.abi.retSig) (diagCtxOfV bvsFinal) (Tup.zip J₁ J₂ ++ [])
        (denote Val Cont (lowerContJumpTo (rs := cr.abi.retSig) cr.privFrame.numSlots
          (pushLabelPcs (cr.tree.map GroupTree.entryPc) []) cr.entryPc
          (mkEntryFrameArgs cr.privFrame.numSlots)) bvsFinal (pushTup J₁ []))
        (denote Val Cont (lowerContJumpTo (rs := cr.abi.retSig) cr.privFrame.numSlots
          (pushLabelPcs (cr.tree.map GroupTree.entryPc) []) cr.entryPc
          (mkEntryFrameArgs cr.privFrame.numSlots)) bvsFinal (pushTup J₂ [])) :=
    fun J₁ J₂ => denote_wf _ (ctxRel_diagV bvsFinal) (ctxRel_pushTup J₁ J₂ .nil)
  rw [wp_group_iff (diagV_diagCtx bvsFinal) (monoD_diagL []) hWfB hWfK m]
  have hMem : ContTupMemPred cr.privFrame.numSlots cr.tree
      (lfp Γ Q X (fun Jv => denoteB Val Cont (liftContifyGroupNodes cm cr
        (pushLabelPcs (cr.tree.map GroupTree.entryPc) []) cr.tree) [] (pushTup Jv [])))
      (canonContifyNodesPred cm cr Γ Q X cr.tree [] []) :=
    canonContifyTupPred_tupMemPred cr.tree _ fun _ _ _ _ h => h
  obtain ⟨j, J, hj, hL, hJ⟩ := findContLabel_pushTup cr.tree _ [] [] _ r₀ r₀.sp slots m m
    cr.entryPc hMem (fun _ => rfl) hFr (fun _ => hCan) (.inl hEnt)
  dsimp only [lowerContJumpTo]; rw [hj]; dsimp only [denote]; rw [hL, hArgs']
  dsimp only [wp]; rw [hVals]; exact hJ

private theorem listNodup_append_left {α} [BEq α] [LawfulBEq α] :
    ∀ {l₁ l₂ : List α}, listNodup (l₁ ++ l₂) = true → listNodup l₁ = true
  | [], _, _ => rfl
  | a :: l₁, l₂, h => by
      dsimp only [List.cons_append, listNodup] at h ⊢
      rcases Bool.and_eq_true_iff.1 h with ⟨hc, ht⟩
      refine Bool.and_eq_true_iff.2 ⟨?_, listNodup_append_left ht⟩
      cases h1 : l₁.contains a
      · rfl
      · have hCt := List.contains_iff_mem.2 (List.mem_append_left l₂ (List.contains_iff_mem.1 h1))
        rw [hCt] at hc; cases hc

private theorem listNodup_name_split :
    ∀ {p1 p2 q1 q2 : List ContifyRegion} {r1 r2 : ContifyRegion},
      listNodup ((p1 ++ r1 :: q1).map (·.name)) = true →
      p1 ++ r1 :: q1 = p2 ++ r2 :: q2 → r1.name = r2.name → r1 = r2 ∧ p1 = p2
  | [], [], _, _, _, _, _, hEq, _ => ⟨(List.cons.inj hEq).1, rfl⟩
  | [], _ :: p2, _, q2, r1, r2, hNd, hEq, hnm => by
      dsimp only [List.nil_append, List.map_cons, listNodup] at hNd
      have hc := (Bool.and_eq_true_iff.1 hNd).1
      rw [(List.cons.inj hEq).2] at hc
      change (!(List.map (·.name) (p2 ++ r2 :: q2)).contains r1.name) = true at hc
      have hC : (List.map (·.name) (p2 ++ r2 :: q2)).contains r1.name = true :=
        List.contains_iff_mem.2 (List.mem_map.2 ⟨r2, by simp, hnm.symm⟩)
      rw [hC] at hc; cases hc
  | _ :: p1, [], q1, _, r1, r2, hNd, hEq, hnm => by
      dsimp only [List.cons_append, List.map_cons, listNodup] at hNd
      have hc := (Bool.and_eq_true_iff.1 hNd).1
      rw [(List.cons.inj hEq).1] at hc
      change (!(List.map (·.name) (p1 ++ r1 :: q1)).contains r2.name) = true at hc
      have hC : (List.map (·.name) (p1 ++ r1 :: q1)).contains r2.name = true :=
        List.contains_iff_mem.2 (List.mem_map.2 ⟨r1, by simp, hnm⟩)
      rw [hC] at hc; cases hc
  | a :: p1, _ :: p2, _, _, r1, r2, hNd, hEq, hnm => by
      cases List.cons.inj hEq with | intro hab htl =>
        have ⟨hr, hp⟩ := listNodup_name_split (Bool.and_eq_true_iff.1 hNd).2 htl hnm
        exact ⟨hr, hab ▸ congrArg (a :: ·) hp⟩

private theorem retContPost_mono {P₁ P₂ : CodeSpec} (hP : ∀ pc s, P₁ pc s → P₂ pc s) :
    ∀ (d : Bool) (retPc : BitVec 64) (r : Tup Val (RegionAbi.contified d).retSig)
      (m : Mem 64), retContPost d P₁ retPc r m → retContPost d P₂ retPc r m
  | false, _, _, _, h => hP _ _ h | true, _, _, _, h => hP _ _ h

private theorem contRet_sp_of_post {Ψ : CodeSpec} {rp₀ sp₀ : BitVec 64}
    (hΨ : ∀ pc s, Ψ pc s → s.regs.sp = sp₀) :
    ∀ (dualRet : Bool) (r : Tup Val (RegionAbi.contified dualRet).retSig) (m : Mem 64),
      retContPost dualRet Ψ rp₀ r m → contRetSp dualRet r = sp₀
  | false, (_, _, _, _, _, _, ()), _, h => hΨ _ _ h
  | true, (_, _, _, _, _, _, _, ()), _, h => hΨ _ _ h

private theorem contifyCall_post_cast (cm : CodeMap) (wit : ContifyWitness) (Ψ_cold : CodeSpec)
    (H : HaltPost) (X : XPost) (cr : ContifyRegion) (st₀ nxtR : Regs) (retPc : BitVec 64)
    (hAbiF : cr.abi.isContified = false) (hrp : nxtR.rp = retPc) :
    ∀ (abi : RegionAbi) (d : Bool) (hEq : abi = .contified d) (needS : Bool)
      (r' : Tup Val abi.retSig) (m'' : Mem 64),
      regionRetPost abi (contifyRegionBailPost cm wit Ψ_cold H
        (WitContGfp cm wit Ψ_cold H X) needS nxtR.sp abi) nxtR.rp r' m'' →
      retContPost d (fun pc' s' => (cr.abi.isContified = true → s'.regs.rp = st₀.rp) ∧
        (needS = true → s'.regs.sp = nxtR.sp) ∧ WitContGfp cm wit Ψ_cold H X pc' s')
        retPc (congrArg RegionAbi.retSig hEq ▸ r') m''
  | .contified d, _, rfl, needS, r', m'', h' => by
      cases d <;> dsimp only [regionRetPost, contifyRegionBailPost, retContPost] at h' ⊢
      · rw [hrp] at h'; exact ⟨fun hCont => by simp [hAbiF] at hCont, h'.2.2, h'.1⟩
      · rcases r' with ⟨_, _, _, _, _, _, _, ⟨⟩⟩; dsimp only at h' ⊢; rw [hrp] at h'
        exact ⟨fun hCont => by simp [hAbiF] at hCont, h'.2.2, h'.1⟩

private theorem witCont_region_check_at {cm : CodeMap} {wit : ContifyWitness}
    (hChk : wit.check cm = true) {pre : List ContifyRegion} {cr : ContifyRegion}
    {post : List ContifyRegion} (hSplit : wit.regions = pre ++ cr :: post) :
    cr.privFrame.numSlots ≤ 64 ∧ (cr.privFrame.numSlots == 0 || cr.abi == .retEnvelope) = true ∧
    cr.entryPc ∈ cr.tree.map GroupTree.entryPc ∧
    checkContGroupNodes cm cr (contCalleesFold cm [] pre)
      (pushLabelPcs (cr.tree.map GroupTree.entryPc) []) cr.tree = true := by
  dsimp only [ContifyWitness.check] at hChk
  have hAux := contCheckAux_append cm pre (cr :: post) []
    (by simpa [hSplit] using (Bool.and_eq_true_iff.1 hChk).2)
  dsimp only [ContifyWitness.checkAux] at hAux
  have hCrChk := (Bool.and_eq_true_iff.1 hAux).1
  dsimp only [ContifyRegion.check] at hCrChk; simp only [Bool.and_eq_true] at hCrChk
  exact ⟨of_decide_eq_true hCrChk.1.1.1.1.1.1.1.1.2, hCrChk.1.1.1.1.1.1.1.2,
    by simpa using hCrChk.1.1.1.1.2, hCrChk.1.1.2⟩

private theorem canonContifyNodes_step_aux (cm : CodeMap) (wit : ContifyWitness)
    (Ψ_cold : CodeSpec) (H : HaltPost) (X : XPost)
    (hH : ∀ c m', H c m' → X haltSym [i64] (c, ()) m')
    (hChk : wit.check cm = true) {pc₀ : BitVec 64} {st₀ : State} {b : BlockFlat}
    (hlu : cm.lookupAddr pc₀ = some b)
    (hbp : b.wp cm.symEnv (fun pc' s' =>
      if (wit.regions.flatMap ContifyRegion.allPcs).contains pc' then
        (PsiContReg cm wit Ψ_cold H pc' s' ∧ WitContGfp cm wit Ψ_cold H X pc' s') ∧
          Ψ_cold pc' s'
      else Ψ_cold pc' s') H (pushRegsV st₀.regs.toRegsV) st₀.mem)
    {pre : List ContifyRegion} {cr : ContifyRegion} {post : List ContifyRegion}
    (hSplit : wit.regions = pre ++ cr :: post) (gs : List GroupTree)
    (pcsOuter : List (BitVec 64)) (lsOuter : List ((ts : List Ty) × Cont ts)) :
    (∀ pc ∈ gs.flatMap GroupTree.allPcs, pc ∈ cr.allPcs) →
    checkContGroupNodes cm cr (contCalleesFold cm [] pre)
      (pushLabelPcs (gs.map GroupTree.entryPc) pcsOuter) gs = true →
    ContLsMatch cr.privFrame.numSlots pcsOuter lsOuter
      (fun pc' s' => (cr.abi.isContified = true → s'.regs.rp = st₀.regs.rp) ∧
        (((cr.privFrame.numSlots > 0) ||
          (cr.abi.isContified && regionMemFree cm (contCalleesFold cm [] pre) cr)) = true →
          s'.regs.sp = st₀.regs.sp) ∧
        WitContGfp cm wit Ψ_cold H X pc' s') →
    (∀ pc' s', (cr.abi.isContified = true → s'.regs.rp = st₀.regs.rp) →
      (((cr.privFrame.numSlots > 0) ||
        (cr.abi.isContified && regionMemFree cm (contCalleesFold cm [] pre) cr)) = true →
        s'.regs.sp = st₀.regs.sp) →
      WitContGfp cm wit Ψ_cold H X pc' s' →
      canonContifyNodesPred cm cr (witContifyEnvAux cm (fun _ _ _ _ _ _ _ => False) pre)
        (contifyRegionQ cm wit Ψ_cold H (WitContGfp cm wit Ψ_cold H X) pre cr st₀.regs) X
        gs pcsOuter lsOuter pc' s') →
    pc₀ ∈ gs.flatMap GroupTree.allPcs →
    canonContifyNodesPred cm cr (witContifyEnvAux cm (fun _ _ _ _ _ _ _ => False) pre)
      (contifyRegionQ cm wit Ψ_cold H (WitContGfp cm wit Ψ_cold H X) pre cr st₀.regs) X
      gs pcsOuter lsOuter pc₀ st₀ := by
  intro hSubPcs hgsChk hlsOuter hEx hpcInGs
  simp only [canonContifyNodesPred]
  let pcs' := pushLabelPcs (gs.map GroupTree.entryPc) pcsOuter
  let callees := contCalleesFold cm [] pre
  let Γ := witContifyEnvAux cm (fun _ _ _ _ _ _ _ => False) pre
  let Q := contifyRegionQ cm wit Ψ_cold H (WitContGfp cm wit Ψ_cold H X) pre cr st₀.regs
  let reqSp : Bool := (cr.privFrame.numSlots > 0) ||
    (cr.abi.isContified && regionMemFree cm callees cr)
  let needMfSp : Bool := cr.abi.isContified && regionMemFree cm callees cr
  let bodies := fun (Jv : Tup Cont (gs.map fun _ => contSig cr.privFrame.numSlots)) =>
    denoteB Val Cont (liftContifyGroupNodes cm cr pcs' gs) [] (pushTup Jv lsOuter)
  let Js := lfp Γ Q X bodies
  let Pred : CodeSpec := fun pc' s' =>
    (cr.abi.isContified = true → s'.regs.rp = st₀.regs.rp) ∧
    (reqSp = true → s'.regs.sp = st₀.regs.sp) ∧
    WitContGfp cm wit Ψ_cold H X pc' s'
  have hMemTup : ContTupMemPred cr.privFrame.numSlots gs Js Pred :=
    canonContifyTupPred_tupMemPred gs Js fun g _ r m ⟨hRp, hSp, hPg⟩ =>
      hEx g.entryPc ⟨r, m⟩ hRp hSp hPg
  have hls' : ContLsMatch cr.privFrame.numSlots pcs' (pushTup Js lsOuter) Pred :=
    contLsMatch_pushTup_group cr.privFrame.numSlots gs Js pcsOuter lsOuter Pred hMemTup hlsOuter
  have hwfB : ∀ J₁ J₂, WfB [] (Tup.zip J₁ J₂ ++ diagCtxOfL lsOuter) (bodies J₁) (bodies J₂) :=
    fun J₁ J₂ => denoteB_wf (liftContifyGroupNodes cm cr pcs' gs) .nil
      (ctxRel_pushTup J₁ J₂ (ctxRel_diagL lsOuter))
  have hClosed := lfp_closed DiagV.nil (monoD_diagL lsOuter) hwfB (Γ := Γ) (Q := Q) (X := X)
  have hStepPred : ∀ pc' s', (findLabelIdx pcs' pc').isSome = true →
      (cr.abi.isContified = true → s'.regs.rp = st₀.regs.rp) →
      (reqSp = true → s'.regs.sp = st₀.regs.sp) →
      (if (wit.regions.flatMap ContifyRegion.allPcs).contains pc' then
        (PsiContReg cm wit Ψ_cold H pc' s' ∧ WitContGfp cm wit Ψ_cold H X pc' s') ∧
          Ψ_cold pc' s'
       else Ψ_cold pc' s') → Pred pc' s' := fun pc' s' _ hRp hSp hS => by
    refine ⟨hRp, hSp, ?_⟩
    by_cases hc : (wit.regions.flatMap ContifyRegion.allPcs).contains pc' = true
    · simp only [hc, ↓reduceIte] at hS; exact hS.1.2
    · exact witContGfp_outside cm wit Ψ_cold H X hc
  have hStepBail : ∀ pc' s', (cr.abi.isContified = true → reqSp = true → s'.regs.sp = st₀.regs.sp) →
      (if (wit.regions.flatMap ContifyRegion.allPcs).contains pc' then
        (PsiContReg cm wit Ψ_cold H pc' s' ∧ WitContGfp cm wit Ψ_cold H X pc' s') ∧
          Ψ_cold pc' s'
       else Ψ_cold pc' s') →
      contifyRegionBailPost cm wit Ψ_cold H (WitContGfp cm wit Ψ_cold H X)
        needMfSp st₀.regs.sp cr.abi pc' s' := by
    intro pc' s' hSpB hS
    have hHyb : PsiContHyb cm wit Ψ_cold H pc' s' := by
      dsimp only [PsiContHyb]
      by_cases hc : (wit.regions.flatMap ContifyRegion.allPcs).contains pc' = true
      · simp only [hc, ↓reduceIte] at hS ⊢; exact ⟨hS.1.1, hS.2⟩
      · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hS ⊢; exact hS
    have hWit : WitContGfp cm wit Ψ_cold H X pc' s' := by
      by_cases hc : (wit.regions.flatMap ContifyRegion.allPcs).contains pc' = true
      · simp only [hc, ↓reduceIte] at hS; exact hS.1.2
      · exact witContGfp_outside cm wit Ψ_cold H X hc
    cases hAb : cr.abi with
    | retEnvelope => exact hHyb
    | contified _ =>
        refine ⟨hWit, hHyb, fun hMf => hSpB (by simp [hAb]; rfl) (by
          dsimp only [reqSp, needMfSp] at hMf ⊢; rw [hAb] at hMf ⊢
          exact Bool.or_eq_true_iff.2 (.inr hMf))⟩
  have hStepCall : ∀ callee calleePc dualRet (nxtR : Regs) mConc' mPub' retPc altRetPc?,
      cr.abi.isContified = false →
      callees.any (fun c => (c.name == callee) && (c.entryPc == calleePc) &&
        (c.dualRet == dualRet)) = true →
      (cr.privFrame.numSlots > 0 → callees.any (fun c => (c.name == callee) &&
        (c.entryPc == calleePc) && c.memFree) = true) →
      cm.addrOf? callee = some calleePc → nxtR.rp = retPc →
      (if dualRet then altRetPc? = some (retPc + 8#64) else altRetPc?.isNone) →
      (findLabelIdx pcs' retPc).isSome = true →
      (if dualRet then (findLabelIdx pcs' (retPc + 8#64)).isSome = true else True) →
      (cr.privFrame.numSlots > 0 → nxtR.sp = st₀.regs.sp) →
      (if (wit.regions.flatMap ContifyRegion.allPcs).contains calleePc then
        (PsiContReg cm wit Ψ_cold H calleePc ⟨nxtR, mConc'⟩ ∧
          WitContGfp cm wit Ψ_cold H X calleePc ⟨nxtR, mConc'⟩) ∧ Ψ_cold calleePc ⟨nxtR, mConc'⟩
       else Ψ_cold calleePc ⟨nxtR, mConc'⟩) →
      ∀ slots', FrameRel cr.privFrame.numSlots st₀.regs.sp slots' mConc' mPub' →
      ∃ P E, Γ callee regSig (RegionAbi.contified dualRet).retSig nxtR.toRegsV.toTup mPub' P E ∧
        (∀ r' m'', P r' m'' → ∃ mConc'',
          (cr.privFrame.numSlots > 0 → contRetSp dualRet r' = st₀.regs.sp) ∧
          FrameRel cr.privFrame.numSlots st₀.regs.sp slots' mConc'' m'' ∧
          retContPost dualRet Pred retPc r' mConc'') ∧
        (∀ g cs xs m'', E g cs xs m'' → X g cs xs m'') := by
    intro callee calleePc dualRet nxtR mConc' mPub' retPc _ hAbiF hcal hMf _ hrp _ _ _ hnSp
      hS slots' hFr'
    rw [List.any_eq_true] at hcal; obtain ⟨c, hcMem, hcEq⟩ := hcal
    simp only [Bool.and_eq_true, beq_iff_eq] at hcEq; rcases hcEq with ⟨⟨rfl, rfl⟩, rfl⟩
    rcases mem_contCalleesFold cm pre [] c hcMem with hEmpty | ⟨pre_c, post_c, cr_c, hPreEq, hToM⟩
    · cases hEmpty
    cases hAbi_c : cr_c.abi with
    | retEnvelope => simp [ContifyRegion.toCalleeMeta?, hAbi_c] at hToM
    | contified dualRet' =>
        simp only [ContifyRegion.toCalleeMeta?, hAbi_c, Option.some.injEq] at hToM
        have hName : cr_c.name = c.name := congrArg ContCalleeMeta.name hToM
        have hEntEq : cr_c.entryPc = c.entryPc := congrArg ContCalleeMeta.entryPc hToM
        have hDualEq : dualRet' = c.dualRet := congrArg ContCalleeMeta.dualRet hToM
        subst hDualEq
        have hSplit_c : wit.regions = pre_c ++ cr_c :: (post_c ++ cr :: post) := by
          rw [hSplit, hPreEq, List.append_assoc]; rfl
        have ⟨hN64_c, hSlotAbi_c, hEntMap, hGrp_c⟩ := witCont_region_check_at hChk hSplit_c
        have hSlot0_c : cr_c.privFrame.numSlots = 0 := by
          rw [hAbi_c] at hSlotAbi_c; cases hn : cr_c.privFrame.numSlots <;> simp_all
        have hEntAll : cr_c.entryPc ∈ cr_c.allPcs := by
          rw [List.mem_map] at hEntMap; rcases hEntMap with ⟨g_c, hg_cMem, hg_cEq⟩
          have hm := checkContGroupNode_entryPc_mem cm cr_c (contCalleesFold cm [] pre_c) _ g_c
            (checkContGroupNodes_forall cm cr_c _ _ cr_c.tree hGrp_c g_c hg_cMem)
          rw [hg_cEq] at hm; exact contifyRegionAllPcs_mem_of_tree hg_cMem hm
        have hcInAll : (wit.regions.flatMap ContifyRegion.allPcs).contains cr_c.entryPc = true :=
          contify_mem_allPcs_of_split hSplit_c hEntAll
        rw [← hEntEq] at hS; simp only [hcInAll, ↓reduceIte] at hS
        have hPg_c := witContGfp_post cm wit Ψ_cold H X hS.1.2 pre_c cr_c (post_c ++ cr :: post)
          hSplit_c hEntAll
        let Γ_c := witContifyEnvAux cm (fun _ _ _ _ _ _ _ => False) pre_c
        have hSpec_c := contifyRegionSpec_from_canonNodes hN64_c hGrp_c hEntMap nxtR mConc'
          (fun h => absurd h (by rw [hSlot0_c]; omega)) hPg_c
        have hRetEq : cr_c.abi.retSig = (RegionAbi.contified c.dualRet).retSig :=
          congrArg RegionAbi.retSig hAbi_c
        let Q₀ := contifyRegionQ cm wit Ψ_cold H (WitContGfp cm wit Ψ_cold H X) pre_c cr_c nxtR
        have hMemW : Γ cr_c.name regSig cr_c.abi.retSig nxtR.toRegsV.toTup mConc' Q₀ X := by
          dsimp only [Γ]; rw [hPreEq]
          exact witContifyEnvAux_mem_prefix cm _ pre_c cr_c post_c c.dualRet hAbi_c hSpec_c
        have hCast : ∀ {sig'} (he : cr_c.abi.retSig = sig') (Q' : Post cr_c.abi.retSig)
            (m'' : Mem 64), Γ c.name regSig cr_c.abi.retSig nxtR.toRegsV.toTup m'' Q' X →
            Γ c.name regSig sig' nxtR.toRegsV.toTup m'' (he ▸ Q') X := by
          rintro _ rfl Q' m'' h; exact h
        have hCast2 : ∀ {sig'} (he : cr_c.abi.retSig = sig') (Q' : Post cr_c.abi.retSig)
            (r' : Tup Val sig') (m'' : Mem 64), (he ▸ Q') r' m'' → Q' (he.symm ▸ r') m'' := by
          rintro _ rfl Q' r' m'' h; exact h
        have hSymInv : ∀ {sig'} (he : cr_c.abi.retSig = sig') (x : Tup Val sig'),
            (he ▸ (he.symm ▸ x)) = x := by rintro _ rfl x; rfl
        by_cases hn0 : cr.privFrame.numSlots = 0
        · have hmEq := frameRel_zero (hn0 ▸ hFr'); subst hmEq
          refine ⟨hRetEq ▸ Q₀, X, hCast hRetEq Q₀ mConc' (hName ▸ hMemW), ?_, fun _ _ _ _ h => h⟩
          intro r' m'' hr
          refine ⟨m'', fun hPos => absurd hn0 (Nat.ne_of_gt hPos), hn0.symm ▸ rfl, ?_⟩
          have res := contifyCall_post_cast cm wit Ψ_cold H X cr st₀.regs nxtR retPc hAbiF hrp
            cr_c.abi c.dualRet hAbi_c _ (hRetEq.symm ▸ r') m'' (hCast2 hRetEq Q₀ r' m'' hr)
          rw [hSymInv hRetEq r'] at res
          refine retContPost_mono (fun _ _ h =>
            ⟨h.1, fun hR => by dsimp only [reqSp] at hR; simp [hn0, hAbiF] at hR, h.2.2⟩)
            c.dualRet retPc r' m'' res
        · have hPos : cr.privFrame.numSlots > 0 := Nat.pos_of_ne_zero hn0
          have hMf2 := hMf hPos; rw [List.any_eq_true] at hMf2
          obtain ⟨cmf, hmfMem, hmfEq⟩ := hMf2
          simp only [Bool.and_eq_true, beq_iff_eq] at hmfEq
          rcases mem_contCalleesFold cm pre [] cmf hmfMem with
            hEmp | ⟨p2, q2, cr2, hPreEq2, hToM2⟩
          · cases hEmp
          have hName2 : cr2.name = c.name := by
            cases ha2 : cr2.abi <;> simp [ContifyRegion.toCalleeMeta?, ha2] at hToM2
            exact (congrArg ContCalleeMeta.name hToM2).trans hmfEq.1.1
          have hWitChk := hChk; dsimp only [ContifyWitness.check] at hWitChk
          have hNdPre : listNodup (pre.map (·.name)) = true := by
            have hNdAll := (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 hWitChk).1).1
            rw [hSplit, List.map_append] at hNdAll
            exact listNodup_append_left hNdAll
          obtain ⟨hCrEq, hPrePEq⟩ := listNodup_name_split (hPreEq ▸ hNdPre)
            (hPreEq.symm.trans hPreEq2) (hName.trans hName2.symm)
          subst hCrEq hPrePEq
          have hMfReg : regionMemFree cm (contCalleesFold cm [] pre_c) cr_c = true := by
            cases ha2 : cr_c.abi <;> simp [ContifyRegion.toCalleeMeta?, ha2] at hToM2
            exact (congrArg ContCalleeMeta.memFree hToM2).trans hmfEq.2
          have hAux2 := contCheckAux_append cm pre_c (cr_c :: (post_c ++ cr :: post)) []
            (hSplit_c ▸ (Bool.and_eq_true_iff.1 hWitChk).2)
          dsimp only [ContifyWitness.checkAux] at hAux2
          have hPure := liftContifyTFlat_isPureMemFree cm cr_c (contCalleesFold cm [] pre_c)
            c.dualRet hAbi_c (Bool.and_eq_true_iff.1 hAux2).1 hMfReg
          have hPushEq : pushTup nxtR.toRegsV.toTup [] = pushRegsV nxtR.toRegsV := by
            rcases nxtR with ⟨_, _, _, _, _, _⟩; rfl
          have hSpecWp : wp Γ_c Q₀ X
              (denote Val Cont (liftContifyTFlat cm cr_c) (pushRegsV nxtR.toRegsV) []) mConc' := by
            dsimp only [Func.spec, Func.wp, liftContifyRegion, denoteFunc] at hSpec_c
            rw [← hPushEq]; exact hSpec_c
          have hReloc := wp_pureMemFree_relocate Γ_c X mConc' mPub' (liftContifyTFlat cm cr_c) hPure
            Q₀ (pushRegsV nxtR.toRegsV) [] [] (fun _ _ _ h => by cases h) hSpecWp
          have hSpecReloc : Func.spec Γ_c (liftContifyRegion cm cr_c).body nxtR.toRegsV.toTup
              mPub' (fun r' m'' => m'' = mPub' ∧ Q₀ r' mConc') X := by
            dsimp only [Func.spec, Func.wp, liftContifyRegion, denoteFunc]
            rw [hPushEq]; exact hReloc
          have hMemReloc : Γ c.name regSig cr_c.abi.retSig nxtR.toRegsV.toTup mPub'
              (fun r' m'' => m'' = mPub' ∧ Q₀ r' mConc') X := by
            rw [← hName]; dsimp only [Γ]; rw [hPreEq]
            exact witContifyEnvAux_mem_prefix cm _ pre_c cr_c post_c c.dualRet hAbi_c hSpecReloc
          refine ⟨hRetEq ▸ (fun r' m'' => m'' = mPub' ∧ Q₀ r' mConc'), X,
            hCast hRetEq (fun r' m'' => m'' = mPub' ∧ Q₀ r' mConc') mPub' hMemReloc, ?_,
            fun _ _ _ _ h => h⟩
          intro r' m'' hr
          rcases hCast2 hRetEq (fun r' m'' => m'' = mPub' ∧ Q₀ r' mConc') r' m'' hr with
            ⟨rfl, hq0⟩
          have res := contifyCall_post_cast cm wit Ψ_cold H X cr st₀.regs nxtR retPc hAbiF hrp
            cr_c.abi c.dualRet hAbi_c _ (hRetEq.symm ▸ r') mConc' hq0
          rw [hSymInv hRetEq r'] at res
          have hNeedT : (cr_c.abi.isContified &&
              regionMemFree cm (contCalleesFold cm [] pre_c) cr_c) = true := by
            simp [hAbi_c, hMfReg, RegionAbi.isContified]
          have hSpNxt := contRet_sp_of_post (fun _ _ h => h.2.1 hNeedT) c.dualRet r' mConc' res
          refine ⟨mConc', fun _ => hSpNxt.trans (hnSp hPos), hFr', ?_⟩
          refine retContPost_mono ?_ c.dualRet retPc r' mConc' res
          intro _ _ h; exact ⟨h.1, fun _ => (h.2.1 hNeedT).trans (hnSp hPos), h.2.2⟩
  apply canonContifyTupPred_of_forall; intro gsPre g gsPost heq
  have hgMem : g ∈ gs := by rw [heq]; simp
  have hgChk := checkContGroupNodes_forall cm cr callees pcs' gs hgsChk g hgMem
  cases g with
  | leaf pc₁ =>
      intro hpcEq sp₀ slots mPub hSp hFr; subst hpcEq
      apply (closed_iff Γ Q X _ Js).1 hClosed
        (heq ▸ contMemberOfPrefix cr.privFrame.numSlots gsPre (.leaf pc₀) gsPost)
        (packContTup cr.privFrame.numSlots st₀.regs sp₀ slots) mPub
      have hNodeEq : (bodies Js).get
          (heq ▸ contMemberOfPrefix cr.privFrame.numSlots gsPre (.leaf pc₀) gsPost)
          (packContTup cr.privFrame.numSlots st₀.regs sp₀ slots) =
        denote Val Cont (liftContifyGroupNode cm cr pcs' (.leaf pc₀))
          (pushTup (packContTup cr.privFrame.numSlots st₀.regs sp₀ slots) [])
          (pushTup Js lsOuter) := by
        subst heq; exact denoteB_get_contMemberOfPrefix cm cr pcs' [] (pushTup Js lsOuter) _ _ _ _
      rw [hNodeEq]
      dsimp only [checkContGroupNode, checkContBlockLeaves] at hgChk
      dsimp only [liftContifyGroupNode]; rw [hlu] at hgChk ⊢
      simp only [Bool.and_eq_true] at hgChk
      cases hsym : symEvalContBlock cm cr.privFrame b [] ContSymState.init with
      | none => rw [hsym] at hgChk; cases hgChk.2
      | some leaves =>
          rw [hsym] at hgChk
          have hleaves : ∀ lf ∈ leaves, ∃ ew, cr.toRegionWitness.findEdge pc₀ lf.path = some ew ∧
              checkContEdgeLeaf cm cr.abi cr.privFrame callees pcs' lf ew.kind = true := by
            intro lf hm; have ha := List.all_eq_true.1 hgChk.2 lf hm
            cases hf : cr.toRegionWitness.findEdge pc₀ lf.path with
            | none => rw [hf] at ha; cases ha | some ew => rw [hf] at ha; exact ⟨ew, rfl, ha⟩
          by_cases hn0 : cr.privFrame.numSlots = 0
          · have hmEq := frameRel_zero (hn0 ▸ hFr)
            have hFr0 : FrameRel cr.privFrame.numSlots st₀.regs.sp [] st₀.mem mPub := by
              rw [hn0]; dsimp only [FrameRel]; simp [hmEq]
            have hPack0 : packContTup cr.privFrame.numSlots st₀.regs sp₀ slots =
                packContTup cr.privFrame.numSlots st₀.regs st₀.regs.sp [] := by
              cases hns : cr.privFrame.numSlots with
              | zero => rfl | succ _ => exact Nat.noConfusion (hn0.symm.trans hns)
            rw [hPack0]
            exact liftContifyBlock_wp_init hls' pc₀ st₀.regs []
              (fun hPos => absurd hn0 (Nat.ne_of_gt hPos)) hH reqSp hStepPred hStepBail
              hStepCall b leaves st₀.mem mPub hFr0 hgChk.1.1 hgChk.1.2 hsym
              (fun hR => .inr fun lf hm => by
                dsimp only [reqSp] at hR
                simp only [hn0, Nat.lt_irrefl, decide_false, Bool.false_or] at hR
                have hMfAll := List.all_eq_true.1 (Bool.and_eq_true_iff.1 hR).2 pc₀
                  (hSubPcs pc₀ hpcInGs)
                rw [hlu] at hMfAll; dsimp only at hMfAll; rw [hsym] at hMfAll
                exact (Bool.and_eq_true_iff.1 (List.all_eq_true.1
                  (Bool.and_eq_true_iff.1 hMfAll).2 lf hm)).1)
              hleaves hbp
          · have hSpEq := hSp (Nat.pos_of_ne_zero hn0); subst hSpEq
            exact liftContifyBlock_wp_init hls' pc₀ st₀.regs slots
              (fun hPos => by
                have ⟨_, hSA, _, _⟩ := witCont_region_check_at hChk hSplit
                cases ha : cr.abi <;> simp [ha, beq_false_of_ne (Nat.ne_of_gt hPos)] at hSA; rfl)
              hH reqSp hStepPred hStepBail hStepCall b leaves st₀.mem mPub hFr hgChk.1.1 hgChk.1.2
              hsym (fun _ => .inl (Nat.pos_of_ne_zero hn0)) hleaves hbp
  | loop header nodes =>
      simp only [canonContifyNodePred]
      dsimp only [checkContGroupNode] at hgChk; simp only [Bool.and_eq_true] at hgChk
      by_cases hin : pc₀ ∈ nodes.flatMap GroupTree.allPcs
      · have hExSub : ∀ pc' s', (cr.abi.isContified = true → s'.regs.rp = st₀.regs.rp) →
            (reqSp = true → s'.regs.sp = st₀.regs.sp) →
            WitContGfp cm wit Ψ_cold H X pc' s' →
            canonContifyNodesPred cm cr Γ Q X nodes pcs' (pushTup Js lsOuter) pc' s' :=
          fun pc' s' hRp hSp hPg =>
            (canonContifyTupPred_get_eq gsPre (.loop header nodes) gsPost heq
            Js (hEx pc' s' hRp hSp hPg)).2
        have hSub := canonContifyNodes_step_aux cm wit Ψ_cold H X hH hChk hlu hbp hSplit
          nodes pcs' (pushTup Js lsOuter)
          (fun p hp => hSubPcs p (List.mem_flatMap.2
            ⟨.loop header nodes, hgMem, by simpa [GroupTree.allPcs] using hp⟩))
          hgChk.2 hls' hExSub hin
        refine ⟨fun hEq sp₀ slots mPub hSp hFr => ?_, hSub⟩
        subst hEq
        apply (closed_iff Γ Q X _ Js).1 hClosed
          (heq ▸ contMemberOfPrefix cr.privFrame.numSlots gsPre (.loop pc₀ nodes) gsPost)
          (packContTup cr.privFrame.numSlots st₀.regs sp₀ slots) mPub
        have hNodeEq : (bodies Js).get
            (heq ▸ contMemberOfPrefix cr.privFrame.numSlots gsPre (.loop pc₀ nodes) gsPost)
            (packContTup cr.privFrame.numSlots st₀.regs sp₀ slots) =
          denote Val Cont (liftContifyGroupNode cm cr pcs' (.loop pc₀ nodes))
            (pushTup (packContTup cr.privFrame.numSlots st₀.regs sp₀ slots) [])
            (pushTup Js lsOuter) := by
          subst heq; exact denoteB_get_contMemberOfPrefix cm cr pcs' [] (pushTup Js lsOuter) _ _ _ _
        rw [hNodeEq]; dsimp only [liftContifyGroupNode, denote]
        have hSubPref : ∀ Jv : Tup Cont (nodes.map fun _ => contSig cr.privFrame.numSlots),
            denoteB Val Cont (liftContifyGroupNodes cm cr
              (pushLabelPcs (nodes.map GroupTree.entryPc) pcs') nodes)
              (pushTup (packContTup cr.privFrame.numSlots st₀.regs sp₀ slots) [])
              (pushTup Jv (pushTup Js lsOuter)) =
            denoteB Val Cont (liftContifyGroupNodes cm cr
              (pushLabelPcs (nodes.map GroupTree.entryPc) pcs') nodes) []
              (pushTup Jv (pushTup Js lsOuter)) := fun Jv =>
          denote_liftContifyGroupNodes_prefix _ nodes hgChk.2 _ _
        simp only [hSubPref]
        have hWfSubB : ∀ J₁ J₂ : Tup Cont (nodes.map fun _ => contSig cr.privFrame.numSlots),
            WfB (diagCtxOfV (pushTup (packContTup cr.privFrame.numSlots st₀.regs sp₀ slots) []))
              (Tup.zip J₁ J₂ ++ diagCtxOfL (pushTup Js lsOuter))
              (denoteB Val Cont (liftContifyGroupNodes cm cr
                (pushLabelPcs (nodes.map GroupTree.entryPc) pcs') nodes) []
                (pushTup J₁ (pushTup Js lsOuter)))
              (denoteB Val Cont (liftContifyGroupNodes cm cr
                (pushLabelPcs (nodes.map GroupTree.entryPc) pcs') nodes) []
                (pushTup J₂ (pushTup Js lsOuter))) :=
          fun J₁ J₂ => denoteB_wf _ CtxRel.nil (ctxRel_pushTup J₁ J₂ (ctxRel_diagL _))
        have hWfSubK : ∀ J₁ J₂ : Tup Cont (nodes.map fun _ => contSig cr.privFrame.numSlots),
            Wf (rs := cr.abi.retSig)
              (diagCtxOfV (pushTup (packContTup cr.privFrame.numSlots st₀.regs sp₀ slots) []))
              (Tup.zip J₁ J₂ ++ diagCtxOfL (pushTup Js lsOuter))
              (denote Val Cont (lowerContJumpTo (rs := cr.abi.retSig) cr.privFrame.numSlots
                (pushLabelPcs (nodes.map GroupTree.entryPc) pcs') pc₀
                (baseContArgs cr.privFrame.numSlots))
                (pushTup (packContTup cr.privFrame.numSlots st₀.regs sp₀ slots) [])
                (pushTup J₁ (pushTup Js lsOuter)))
              (denote Val Cont (lowerContJumpTo (rs := cr.abi.retSig) cr.privFrame.numSlots
                (pushLabelPcs (nodes.map GroupTree.entryPc) pcs') pc₀
                (baseContArgs cr.privFrame.numSlots))
                (pushTup (packContTup cr.privFrame.numSlots st₀.regs sp₀ slots) [])
                (pushTup J₂ (pushTup Js lsOuter))) :=
          fun J₁ J₂ => denote_wf _ (ctxRel_diagV _) (ctxRel_pushTup J₁ J₂ (ctxRel_diagL _))
        rw [wp_group_iff (diagV_diagCtx _) (monoD_diagL _) hWfSubB hWfSubK mPub]
        have hMemSub : ContTupMemPred cr.privFrame.numSlots nodes
            (lfp Γ Q X (fun Jv => denoteB Val Cont (liftContifyGroupNodes cm cr
              (pushLabelPcs (nodes.map GroupTree.entryPc) pcs') nodes) []
              (pushTup Jv (pushTup Js lsOuter))))
            (canonContifyNodesPred cm cr Γ Q X nodes pcs' (pushTup Js lsOuter)) :=
          canonContifyTupPred_tupMemPred nodes _ fun _ _ _ _ h => h
        exact denote_lowerContJumpTo_base nodes _ pcs' (pushTup Js lsOuter) _ st₀.regs sp₀ slots
          st₀.mem mPub pc₀ hMemSub (List.contains_iff_mem.1 hgChk.1.2) hSp hFr hSub
      · refine ⟨fun hEq _ _ _ _ _ => ?_, ?_⟩
        · have hEnt := checkContGroupNode_entryPc_mem cm cr callees pcs' (.loop header nodes)
            (by dsimp only [checkContGroupNode]; rw [hgChk.1.1, hgChk.1.2, hgChk.2]; rfl)
          rw [hEq] at hin
          exact absurd (by simpa [GroupTree.entryPc, GroupTree.allPcs] using hEnt) hin
        · exact canonContifyNodesPred_of_outside_all nodes pcs' (pushTup Js lsOuter) hgChk.2 hin
termination_by treeListSize gs
decreasing_by
  have h := treeListSize_mem (.loop header nodes) gs hgMem
  simp only [treeSize] at h; omega

private theorem contifyRegionQ_congr (cm : CodeMap) (wit : ContifyWitness) (Ψ_cold : CodeSpec)
    (H : HaltPost) (P : CodeSpec) (pre : List ContifyRegion) (cr : ContifyRegion)
    {r₁ r₂ : Regs} (hRp : cr.abi.isContified = true → r₁.rp = r₂.rp)
    (hSp : ((cr.privFrame.numSlots > 0) ||
      (cr.abi.isContified && regionMemFree cm (contCalleesFold cm [] pre) cr)) = true →
      r₁.sp = r₂.sp) :
    contifyRegionQ cm wit Ψ_cold H P pre cr r₁ = contifyRegionQ cm wit Ψ_cold H P pre cr r₂ := by
  have hg : ∀ (abi : RegionAbi) (mf : Bool) (hAbi : cr.abi = abi),
      (abi.isContified = true → r₁.rp = r₂.rp) →
      (abi.isContified = true → mf = true → r₁.sp = r₂.sp) →
      ∀ (vs : Tup Val abi.retSig) (m : Mem 64),
        regionRetPost abi (contifyRegionBailPost cm wit Ψ_cold H P
          (abi.isContified && mf) r₁.sp abi) r₁.rp vs m =
        regionRetPost abi (contifyRegionBailPost cm wit Ψ_cold H P
          (abi.isContified && mf) r₂.sp abi) r₂.rp vs m := by
    intro abi mf _ hr hs vs m; cases abi with
    | retEnvelope => rfl
    | contified d =>
        have hr' := hr rfl; simp only [hr']
        by_cases hm : mf = true
        · have hs' := hs rfl hm; simp only [hs']
        · have hmf : mf = false := Bool.eq_false_iff.2 hm
          dsimp only [regionRetPost, contifyRegionBailPost]
          cases d <;> simp [hmf]
  funext vs m
  exact hg cr.abi (regionMemFree cm (contCalleesFold cm [] pre) cr) rfl hRp
    (fun hC hMf => hSp (by simp [hC, hMf])) vs m

private theorem contify_psiReg_implies_witGfp (cm : CodeMap) (wit : ContifyWitness)
    (Ψ_cold : CodeSpec) (H : HaltPost) (X : XPost)
    (hH : ∀ c m', H c m' → X haltSym [i64] (c, ()) m') (hChk : wit.check cm = true) :
    ∀ pc st, PsiContReg cm wit Ψ_cold H pc st → WitContGfp cm wit Ψ_cold H X pc st := by
  intro pc st hReg
  refine park_induction (P := fun p => WitContGfp cm wit Ψ_cold H X p.1 p.2)
    (contifyRegionStep_mono cm wit Ψ_cold H) ?_ (pc, st) hReg
  rintro ⟨pc₀, st₀⟩ ⟨b, hlu, hbp⟩; dsimp only at *; apply witContGfp_pre
  intro pre cr post hSplit hpcMem
  have ⟨_, _, _, hGrp⟩ := witCont_region_check_at hChk hSplit
  exact canonContifyNodes_step_aux cm wit Ψ_cold H X hH hChk hlu hbp hSplit cr.tree [] []
    (fun p hp => hp) hGrp (contLsMatch_nil _ _) (fun pc' s' hRp hSp hPg => by
      by_cases hc : pc' ∈ cr.allPcs
      · have hPost := witContGfp_post cm wit Ψ_cold H X hPg pre cr post hSplit hc
        rw [← contifyRegionQ_congr cm wit Ψ_cold H (WitContGfp cm wit Ψ_cold H X) pre cr hRp hSp]
        exact hPost
      · exact canonContifyNodesPred_of_outside_all cr.tree [] [] hGrp hc) hpcMem

private theorem contifyRegion_entryPc_mem_allPcs (cm : CodeMap) (wit : ContifyWitness)
    (hChk : wit.check cm = true) {cr : ContifyRegion} (hMem : cr ∈ wit.regions) :
    cr.entryPc ∈ cr.allPcs := by
  rcases List.mem_iff_append.1 hMem with ⟨pre, post, hSplit⟩
  have ⟨_, _, hEntMap, hGrp⟩ := witCont_region_check_at hChk hSplit
  rw [List.mem_map] at hEntMap; rcases hEntMap with ⟨g, hgMem, hgEq⟩
  have hm := checkContGroupNode_entryPc_mem cm cr _ _ g
    (checkContGroupNodes_forall cm cr _ _ cr.tree hGrp g hgMem)
  rw [hgEq] at hm; exact contifyRegionAllPcs_mem_of_tree hgMem hm

private theorem contifyFlatMap_nodup_disjoint_split (pre : List ContifyRegion) (a : ContifyRegion)
    (mid : List ContifyRegion) (b : ContifyRegion) (post : List ContifyRegion)
    (hNd : listNodup ((pre ++ a :: mid ++ b :: post).flatMap ContifyRegion.allPcs) = true) :
    ∀ pc, pc ∈ a.allPcs → pc ∉ b.allPcs := by
  intro pc ha hb
  have hApp : (pre ++ a :: mid ++ b :: post).flatMap ContifyRegion.allPcs =
      (pre.flatMap ContifyRegion.allPcs ++ a.allPcs) ++
      (mid.flatMap ContifyRegion.allPcs ++ b.allPcs ++ post.flatMap ContifyRegion.allPcs) := by
    simp [List.flatMap_append, List.append_assoc]
  rw [hApp] at hNd
  exact listNodup_false_append hNd pc (List.mem_append_right _ ha) pc
    (List.mem_append_left _ (List.mem_append_right _ hb)) rfl

private theorem contifyRegionAllPcs_disjoint_of_ne (cm : CodeMap) (wit : ContifyWitness)
    (hChk : wit.check cm = true) {cr₁ cr₂ : ContifyRegion}
    (h1 : cr₁ ∈ wit.regions) (h2 : cr₂ ∈ wit.regions) (hne : cr₁ ≠ cr₂) :
    ∀ pc, pc ∈ cr₁.allPcs → pc ∉ cr₂.allPcs := by
  dsimp only [ContifyWitness.check] at hChk; simp only [Bool.and_eq_true] at hChk
  have hNd := hChk.1.2
  rcases List.mem_iff_append.1 h1 with ⟨pre₁, post₁, hEq₁⟩
  rcases List.mem_append.1 (hEq₁ ▸ h2) with hInPre | hInTail
  · rcases List.mem_iff_append.1 hInPre with ⟨pre₂, mid₂, hPre₁Eq⟩
    rw [show wit.regions = pre₂ ++ cr₂ :: mid₂ ++ cr₁ :: post₁ by
      rw [hEq₁, hPre₁Eq, List.append_assoc]] at hNd
    exact fun pc h1p h2p =>
      contifyFlatMap_nodup_disjoint_split pre₂ cr₂ mid₂ cr₁ post₁ hNd pc h2p h1p
  · rcases List.mem_cons.1 hInTail with hSame | hInPost
    · exact absurd hSame.symm hne
    · rcases List.mem_iff_append.1 hInPost with ⟨mid₂, post₂, hPost₁Eq⟩
      rw [show wit.regions = pre₁ ++ cr₁ :: mid₂ ++ cr₂ :: post₂ by
        rw [hEq₁, hPost₁Eq]; simp [List.cons_append]] at hNd
      exact contifyFlatMap_nodup_disjoint_split pre₁ cr₁ mid₂ cr₂ post₂ hNd

/-! ## §5. Stage-1 `Fn.mid` Lifting & Hybrid `Ψ_hyb = Ψ_reg ∧ Ψ_cold` Soundness Theorems -/

private theorem contifyRegionQ_to_retPost (cm : CodeMap) (wit : ContifyWitness)
    (Ψ_cold : CodeSpec) (H : HaltPost) (X : XPost) (r₀ : Regs) (m' : Mem 64) :
    ∀ (abi : RegionAbi) (needSp : Bool) (vs' : Tup Val abi.retSig),
      regionRetPost abi (contifyRegionBailPost cm wit Ψ_cold H
        (WitContGfp cm wit Ψ_cold H X) needSp r₀.sp abi) r₀.rp vs' m' →
      regionRetPost abi (PsiContHyb cm wit Ψ_cold H) r₀.rp vs' m'
  | .retEnvelope, _, _, h => h
  | .contified dualRet, _, _, h => by cases dualRet <;> exact h.2.1

/-- Lift `PsiContReg` at Stage-1 region entry to `Func.spec` of `(liftContifyRegion cm cr).body`
over `witContifyEnv`. -/
theorem contify_psiReg_to_func_spec (cm : CodeMap) (wit : ContifyWitness) (Ψ_cold : CodeSpec)
    (H : HaltPost) (X : XPost) (hH : ∀ c m', H c m' → X haltSym [i64] (c, ()) m')
    (hChk : wit.check cm = true) {cr : ContifyRegion} (hMem : cr ∈ wit.regions)
    (r₀ : Regs) (m : Mem 64) (hPriv : PrivFrameOk cr.privFrame.numSlots r₀.sp m)
    (hReg : PsiContReg cm wit Ψ_cold H cr.entryPc ⟨r₀, m⟩) :
    Func.spec (witContifyEnv cm wit) (liftContifyRegion cm cr).body r₀.toRegsV.toTup m
      (regionRetPost cr.abi (PsiContHyb cm wit Ψ_cold H) r₀.rp) X := by
  rcases List.mem_iff_append.1 hMem with ⟨pre, post, hSplit⟩
  have ⟨hN64, _, hEntMap, hGrp⟩ := witCont_region_check_at hChk hSplit
  have hEntAll := contifyRegion_entryPc_mem_allPcs cm wit hChk hMem
  have hPg := witContGfp_post cm wit Ψ_cold H X
    (contify_psiReg_implies_witGfp cm wit Ψ_cold H X hH hChk _ _ hReg) pre cr post hSplit hEntAll
  have hSpecPre := contifyRegionSpec_from_canonNodes hN64 hGrp hEntMap r₀ m hPriv hPg
  have hSpecEnv : Func.spec (witContifyEnv cm wit) (liftContifyRegion cm cr).body r₀.toRegsV.toTup m
      (contifyRegionQ cm wit Ψ_cold H (WitContGfp cm wit Ψ_cold H X) pre cr r₀) X := by
    refine Func.spec_env_mono (fun f as bs xs m' P' E' hf => ?_) hSpecPre
    dsimp only [witContifyEnv]; rw [hSplit, witContifyEnvAux_append]
    exact witContifyEnvAux_mono_right cm _ (cr :: post) f as bs xs m' P' E' hf
  exact Func.spec_mono (witContifyEnv cm wit) (liftContifyRegion cm cr).body _ m _ _ _ _
    (fun vs m' hq => contifyRegionQ_to_retPost cm wit Ψ_cold H X r₀ m' cr.abi _ vs hq)
    (fun _ _ _ _ h => h) hSpecEnv

/-- Lift `PsiContReg` through `Unified.Ssa.midEnd` (`Fn.mid`, `fn_mid_spec`). -/
theorem contify_psiReg_to_mid_spec (cm : CodeMap) (wit : ContifyWitness) (Ψ_cold : CodeSpec)
    (H : HaltPost) (X : XPost) (lt : LegalTarget)
    (hH : ∀ c m', H c m' → X haltSym [i64] (c, ()) m') (hChk : wit.check cm = true)
    {cr : ContifyRegion} (hMem : cr ∈ wit.regions)
    (hSupp : ((liftContifyRegion cm cr).earlyOpt).body.supportsSource lt = true)
    (r₀ : Regs) (m : Mem 64) (hPriv : PrivFrameOk cr.privFrame.numSlots r₀.sp m)
    (hReg : PsiContReg cm wit Ψ_cold H cr.entryPc ⟨r₀, m⟩) :
    Func.spec (legalEnv lt (witContifyEnv cm wit)) ((liftContifyRegion cm cr).mid lt).body
      (encodeTup lt regSig r₀.toRegsV.toTup) m
      (legalPost lt (regionRetPost cr.abi (PsiContHyb cm wit Ψ_cold H) r₀.rp))
      (legalXPost lt X) := by
  let s : SSpec := {
    Γ := witContifyEnv cm wit
    C := fun as rs xs m' Q' X' => ∃ (h₁ : as = regSig) (h₂ : rs = cr.abi.retSig),
      Func.spec (witContifyEnv cm wit) (liftContifyRegion cm cr).body
        (cast (congrArg (Tup Val) h₁) xs) m' (cast (congrArg Post h₂) Q') X'
  }
  have hSat : ssa.Sat (liftContifyRegion cm cr) s := fun xs m' Q' X' ⟨h₁, h₂, hSp⟩ => by
    cases h₁; cases h₂; exact hSp
  exact midEnd_sound lt (liftContifyRegion cm cr) ((liftContifyRegion cm cr).mid lt) s
    (liftContifyRegion_wf cm cr) (by simp [hSupp]) hSat (encodeTup lt regSig r₀.toRegsV.toTup) m _ _
    ⟨rfl, rfl, r₀.toRegsV.toTup, regionRetPost cr.abi (PsiContHyb cm wit Ψ_cold H) r₀.rp, X,
      ⟨rfl, rfl, contify_psiReg_to_func_spec cm wit Ψ_cold H X hH hChk hMem r₀ m hPriv hReg⟩,
      rfl, rfl, rfl⟩

private theorem contify_cm_wp_closed (cm : CodeMap) (H : HaltPost) :
    SpecsClosed cm cm.symEnv (cm.wp H) H := fun pc b hlu st hbp Ψ hClosed =>
  hClosed pc b hlu st (blockFlat_wp_mono (fun _ _ h => h Ψ hClosed) b _ _ hbp)

/-- End-to-end verified bridge from whole-`CodeMap` `cm.wp H` to legalized `Fn.mid lt` for every
Stage-1 region in `checkAndLiftContify cm wit = .ok (fns, wRes)`. -/
theorem checkAndLiftContify_cm_wp_to_mid (cm : CodeMap) (wit : ContifyWitness)
    (H : HaltPost) (X : XPost) (lt : LegalTarget) {fns : List Fn} {wRes : CodeMap}
    (hLift : checkAndLiftContify cm wit = .ok (fns, wRes))
    (hH : ∀ c m', H c m' → X haltSym [i64] (c, ()) m')
    {cr : ContifyRegion} (hMem : cr ∈ wit.regions)
    (hSupp : ((liftContifyRegion cm cr).earlyOpt).body.supportsSource lt = true)
    (r₀ : Regs) (m : Mem 64) (hPriv : PrivFrameOk cr.privFrame.numSlots r₀.sp m)
    (hWp : cm.wp H cr.entryPc ⟨r₀, m⟩) :
    Func.spec (legalEnv lt (witContifyEnv cm wit)) ((liftContifyRegion cm cr).mid lt).body
      (encodeTup lt regSig r₀.toRegsV.toTup) m
      (legalPost lt (regionRetPost cr.abi (cm.wp H) r₀.rp)) (legalXPost lt X) := by
  dsimp only [checkAndLiftContify] at hLift; split at hLift
  · rename_i hChk
    have hClosedHyb : SpecsClosed cm cm.symEnv (PsiContHyb cm wit (cm.wp H) H) H := by
      intro pc b hlu st hbp
      have hCold : cm.wp H pc st := contify_cm_wp_closed cm H pc b hlu st
        (blockFlat_wp_mono (fun pc' st' h => by
          dsimp only [PsiContHyb] at h
          by_cases hc : (wit.regions.flatMap ContifyRegion.allPcs).contains pc' = true
          · simp only [hc, ↓reduceIte] at h; exact h.2
          · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h; exact h) b _ _ hbp)
      by_cases hc : (wit.regions.flatMap ContifyRegion.allPcs).contains pc = true
      · dsimp only [PsiContHyb]; simp only [hc, ↓reduceIte]
        exact ⟨Xcap.Lfp.lfp_closed (contifyRegionStep_mono cm wit (cm.wp H) H) (pc, st)
          ⟨b, hlu, blockFlat_wp_mono (fun _ _ h => h) b _ _ hbp⟩, hCold⟩
      · dsimp only [PsiContHyb]; simp only [hc, Bool.false_eq_true, ↓reduceIte]; exact hCold
    have hReg : PsiContReg cm wit (cm.wp H) H cr.entryPc ⟨r₀, m⟩ := by
      have hHyb := hWp (PsiContHyb cm wit (cm.wp H) H) hClosedHyb
      dsimp only [PsiContHyb] at hHyb
      rcases List.mem_iff_append.1 hMem with ⟨pre, post, hSplit⟩
      have hc := contify_mem_allPcs_of_split hSplit
        (contifyRegion_entryPc_mem_allPcs cm wit hChk hMem)
      simp only [hc, ↓reduceIte] at hHyb; exact hHyb.1
    have hSpec := contify_psiReg_to_mid_spec cm wit (cm.wp H) H X lt hH hChk hMem hSupp
      r₀ m hPriv hReg
    refine Func.spec_mono (legalEnv lt (witContifyEnv cm wit))
      ((liftContifyRegion cm cr).mid lt).body _ m _ _ _ _ (fun vs m' hPost => ?_)
      (fun _ _ _ _ h => h) hSpec
    rcases hPost with ⟨xs, rfl, hRet⟩; refine ⟨xs, rfl, ?_⟩
    have hHybCold : ∀ pc' s', PsiContHyb cm wit (cm.wp H) H pc' s' → cm.wp H pc' s' := by
      intro pc' s' h; dsimp only [PsiContHyb] at h; split at h <;> first | exact h.2 | exact h
    have hgen : ∀ (abi : RegionAbi) (xs' : Tup Val abi.retSig),
        regionRetPost abi (PsiContHyb cm wit (cm.wp H) H) r₀.rp xs' m' →
        regionRetPost abi (cm.wp H) r₀.rp xs' m' := fun abi xs' h' => by
      cases abi with
      | retEnvelope => exact hHybCold _ _ h'
      | contified dualRet => cases dualRet <;> exact hHybCold _ _ h'
    exact hgen cr.abi xs hRet
  · cases hLift

private theorem contify_lookupAddr_filter_of_addr (cm : CodeMap) (p : BitVec 64 → Bool)
    (pc : BitVec 64) (hp : p pc = true) :
    CodeMap.lookupAddr (cm.filter fun e => p e.addr) pc = CodeMap.lookupAddr cm pc := by
  induction cm with
  | nil => rfl
  | cons e es ih =>
      dsimp only [List.filter, CodeMap.lookupAddr]
      by_cases heq : e.addr = pc
      · subst heq; simp [hp, CodeMap.lookupAddr]
      · cases hpe : p e.addr <;> simp [beq_false_of_ne heq, CodeMap.lookupAddr, ih]

/-- Hybrid Stage-1 soundness (`Ψ_hyb = Ψ_reg ∧ Ψ_cold`) with `PrivFrameOk` entry precondition. -/
theorem checkAndLiftContify_hybrid_sound (cm : CodeMap) (wit : ContifyWitness)
    (Ψ_cold : CodeSpec) (H : HaltPost) (X : XPost) (lt : LegalTarget)
    {fns : List Fn} {wRes : CodeMap} (hLift : checkAndLiftContify cm wit = .ok (fns, wRes))
    (hH : ∀ c m', H c m' → X haltSym [i64] (c, ()) m')
    (hSupp : ∀ cr ∈ wit.regions, ((liftContifyRegion cm cr).earlyOpt).body.supportsSource lt = true)
    (hPriv : ∀ cr ∈ wit.regions, ∀ r₀ m₀,
      PsiContReg cm wit Ψ_cold H cr.entryPc ⟨r₀, m₀⟩ → PrivFrameOk cr.privFrame.numSlots r₀.sp m₀)
    (hRes : SpecsClosed wRes cm.symEnv Ψ_cold H)
    (hEntry : ∀ cr ∈ wit.regions, ∀ r₀ m₀,
      Func.spec (legalEnv lt (witContifyEnv cm wit)) ((liftContifyRegion cm cr).mid lt).body
        (encodeTup lt regSig r₀.toRegsV.toTup) m₀
        (legalPost lt (regionRetPost cr.abi (PsiContHyb cm wit Ψ_cold H) r₀.rp))
        (legalXPost lt X) → Ψ_cold cr.entryPc ⟨r₀, m₀⟩)
    (hDrop : ∀ cr ∈ wit.regions, cr.retainFallbacks = false →
      ∀ pc ∈ cr.allPcs, pc ≠ cr.entryPc → ∀ st,
        PsiContReg cm wit Ψ_cold H pc st → Ψ_cold pc st) :
    SpecsClosed cm cm.symEnv (PsiContHyb cm wit Ψ_cold H) H ∧
      ∀ pc₀ st₀, cm.wp H pc₀ st₀ → Ψ_cold pc₀ st₀ := by
  dsimp only [checkAndLiftContify] at hLift; split at hLift
  · rename_i hChk; cases hLift
    have hClosed : SpecsClosed cm cm.symEnv (PsiContHyb cm wit Ψ_cold H) H := by
      intro pc b hlu st hbp
      have hRegPc : PsiContReg cm wit Ψ_cold H pc st :=
        Xcap.Lfp.lfp_closed (contifyRegionStep_mono cm wit Ψ_cold H) (pc, st)
          ⟨b, hlu, blockFlat_wp_mono (fun _ _ h => h) b _ _ hbp⟩
      have hColdBp : b.wp cm.symEnv Ψ_cold H (pushRegsV st.regs.toRegsV) st.mem :=
        blockFlat_wp_mono (fun _ _ h => by
          dsimp only [PsiContHyb] at h; split at h <;> first | exact h.2 | exact h) b _ _ hbp
      have hResAt : (pc ∉ wit.regions.map (·.entryPc)) →
          (pc ∉ ((wit.regions.filter (fun r => !r.retainFallbacks)).flatMap
            ContifyRegion.allPcs)) → Ψ_cold pc st := fun hNotEnt hNotDrop => by
        have hFilt : CodeMap.lookupAddr (residualContifyCodeMap cm wit) pc =
            CodeMap.lookupAddr cm pc := by
          dsimp only [residualContifyCodeMap]
          apply contify_lookupAddr_filter_of_addr cm
            (fun a => (!(wit.regions.map (·.entryPc)).contains a) &&
              (!((wit.regions.filter (fun r => !r.retainFallbacks)).flatMap
                ContifyRegion.allPcs).contains a)) pc
          simp [hNotEnt, hNotDrop]
        exact hRes pc b (by rw [hFilt]; exact hlu) st hColdBp
      by_cases hc : (wit.regions.flatMap ContifyRegion.allPcs).contains pc = true
      · dsimp only [PsiContHyb]; simp only [hc, ↓reduceIte]; refine ⟨hRegPc, ?_⟩
        rw [List.contains_iff_mem, List.mem_flatMap] at hc; rcases hc with ⟨cr, hCrMem, hPcCr⟩
        by_cases hEqEnt : pc = cr.entryPc
        · subst hEqEnt
          exact hEntry cr hCrMem st.regs st.mem
            (contify_psiReg_to_mid_spec cm wit Ψ_cold H X lt hH hChk hCrMem (hSupp cr hCrMem)
              st.regs st.mem (hPriv cr hCrMem st.regs st.mem hRegPc) hRegPc)
        · by_cases hRet : cr.retainFallbacks = true
          · exact hResAt (fun hInEnt => by
              rw [List.mem_map] at hInEnt; rcases hInEnt with ⟨cr', hCr'Mem, hCr'Eq⟩
              by_cases hSame : cr' = cr
              · subst hSame; exact hEqEnt hCr'Eq.symm
              · exact contifyRegionAllPcs_disjoint_of_ne cm wit hChk hCrMem hCr'Mem (Ne.symm hSame)
                  pc hPcCr (hCr'Eq ▸ contifyRegion_entryPc_mem_allPcs cm wit hChk hCr'Mem))
              (fun hInDrop => by
              rw [List.mem_flatMap] at hInDrop; rcases hInDrop with ⟨cr', hCr'Filt, hPcCr'⟩
              rw [List.mem_filter] at hCr'Filt
              by_cases hSame : cr' = cr
              · subst hSame; simp [hRet] at hCr'Filt
              · exact contifyRegionAllPcs_disjoint_of_ne cm wit hChk hCrMem hCr'Filt.1
                  (Ne.symm hSame) pc hPcCr hPcCr')
          · have hRetF : cr.retainFallbacks = false := by
              cases hrf : cr.retainFallbacks <;> simp_all
            exact hDrop cr hCrMem hRetF pc hPcCr hEqEnt st hRegPc
      · dsimp only [PsiContHyb]; simp only [hc, Bool.false_eq_true, ↓reduceIte]
        exact hResAt (fun hInEnt => by
          rw [List.mem_map] at hInEnt; rcases hInEnt with ⟨cr', hCr'Mem, hCr'Eq⟩
          exact hc (List.contains_iff_mem.2 (List.mem_flatMap.2
            ⟨cr', hCr'Mem, hCr'Eq ▸ contifyRegion_entryPc_mem_allPcs cm wit hChk hCr'Mem⟩)))
          (fun hInDrop => by
          rw [List.mem_flatMap] at hInDrop; rcases hInDrop with ⟨cr', hCr'Filt, hPcCr'⟩
          rw [List.mem_filter] at hCr'Filt
          exact hc (List.contains_iff_mem.2 (List.mem_flatMap.2 ⟨cr', hCr'Filt.1, hPcCr'⟩)))
    refine ⟨hClosed, fun pc₀ st₀ hWp => ?_⟩
    have hHyb := hWp (PsiContHyb cm wit Ψ_cold H) hClosed
    dsimp only [PsiContHyb] at hHyb; split at hHyb <;> first | exact hHyb.2 | exact hHyb
  · cases hLift

end LeanQbe.T.Unified
