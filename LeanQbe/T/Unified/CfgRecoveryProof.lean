module

public import LeanQbe.T.Unified.CfgRecovery
public import LeanQbe.T.Unified.CfgRecoveryLemmas
public import LeanQbe.T.BedrockWord.Exec
public import LeanQbe.T.Unified.DriverLemmas
import LeanQbe.T.WPLemmas
import LeanQbe.T.MainLemmas
import LeanQbe.T.GroupLfpLemmas
import LeanQbe.T.FlatLemmas

/-!
# Soundness Proofs for Verified CFG Recovery (`Unified.CfgRecoveryProof`)

Top-level XCAP fixed-point and hybrid soundness theorems (`witEnv`,
`checkAndLiftWitness_cm_wp_to_mid`, `checkAndLiftWitness_hybrid_sound`) built over
`LeanQbe.T.Unified.CfgRecoveryLemmas`, with `0` `@[expose]` and all `*Lemmas*` imports private.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Unified

open LeanQbe.T
open LeanQbe.T.BedrockWord

private theorem ctxTypes_length {α : Type} {f : α → Type} :
    {Γ : List α} → {bvs : List ((a : α) × f a)} → CtxTypes Γ bvs → Γ.length = bvs.length
  | _, _, .nil => rfl
  | _, _, .cons h => congrArg Nat.succ (ctxTypes_length h)

private theorem checkArg_idx_lt {Γ : List Ty} {t : Ty} {i : Nat}
    (hchk : checkArg Γ t (.var i) = true) : i < Γ.length := by
  apply listGet?_isSome_lt Γ
  dsimp only [checkArg] at hchk
  cases hg : listGet? Γ i with
  | none => rw [hg] at hchk; cases hchk
  | some _ => rfl

private theorem lookupV_prefix {V : Ty → Type} {Γ : List Ty}
    {bvs : List ((t : Ty) × V t)} (vsTail : List ((t : Ty) × V t))
    (hctx : CtxTypes Γ bvs) {t : Ty} {i : Nat} (hchk : checkArg Γ t (.var i) = true) :
    lookupV (bvs ++ vsTail) t i = lookupV bvs t i := by
  have hlt : i < bvs.length := by rw [← ctxTypes_length hctx]; exact checkArg_idx_lt hchk
  dsimp only [lookupV]
  rw [listGet?_append_left bvs vsTail hlt]

private theorem denoteArg_prefix {V : Ty → Type} {Γ : List Ty}
    {bvs : List ((t : Ty) × V t)} (vsTail : List ((t : Ty) × V t))
    (hctx : CtxTypes Γ bvs) {t : Ty} {a : Arg K t} (hchk : checkArg Γ t a = true) :
    denoteArg (bvs ++ vsTail) a = denoteArg bvs a := by
  cases a with
  | imm _ => rfl
  | var _ => dsimp only [denoteArg]; rw [lookupV_prefix vsTail hctx hchk]

private theorem denoteArgs_prefix {V : Ty → Type} {Γ : List Ty}
    {bvs : List ((t : Ty) × V t)} (vsTail : List ((t : Ty) × V t))
    (hctx : CtxTypes Γ bvs) :
    {ts : List Ty} → {as : Tup (Arg K) ts} → checkArgs Γ as = true →
    denoteArgs (bvs ++ vsTail) as = denoteArgs bvs as
  | [], (), _ => rfl
  | _ :: _, (_, _), hchk => by
      dsimp only [checkArgs] at hchk; simp only [Bool.and_eq_true] at hchk
      dsimp only [denoteArgs]
      rw [denoteArg_prefix vsTail hctx hchk.1, denoteArgs_prefix vsTail hctx hchk.2]

private theorem denoteRegsExpr_prefix {V : Ty → Type} {Γ : List Ty}
    {bvs : List ((t : Ty) × V t)} (vsTail : List ((t : Ty) × V t))
    (hctx : CtxTypes Γ bvs) {e : RegsExpr K} (hchk : checkRegsExpr Γ e = true) :
    denoteRegsExpr (bvs ++ vsTail) e = denoteRegsExpr bvs e := by
  dsimp only [checkRegsExpr] at hchk; simp only [Bool.and_eq_true] at hchk
  dsimp only [denoteRegsExpr]
  rw [denoteArg_prefix vsTail hctx hchk.1.1.1.1.1,
      denoteArg_prefix vsTail hctx hchk.1.1.1.1.2,
      denoteArg_prefix vsTail hctx hchk.1.1.1.2,
      denoteArg_prefix vsTail hctx hchk.1.1.2,
      denoteArg_prefix vsTail hctx hchk.1.2,
      denoteArg_prefix vsTail hctx hchk.2]

private def diagCtxOfV : List ((t : Ty) × Val t) → Ctx Val Val :=
  List.map (fun ⟨t, v⟩ => ⟨t, v, v⟩)

private def diagCtxOfL : List ((ts : List Ty) × Cont ts) → Ctx Cont Cont :=
  List.map (fun ⟨ts, l⟩ => ⟨ts, l, l⟩)

private theorem ctxRel_diagV : (vs : List ((t : Ty) × Val t)) → CtxRel (diagCtxOfV vs) vs vs
  | [] => .nil
  | _ :: vs => .cons List.mem_cons_self
      ((ctxRel_diagV vs).mono fun _ hp => List.mem_cons_of_mem _ hp)

private theorem diagV_diagCtx : (vs : List ((t : Ty) × Val t)) → DiagV (diagCtxOfV vs)
  | [], _, h => nomatch h
  | _ :: vs, p, hp => by cases hp with | head => rfl | tail _ hp => exact diagV_diagCtx vs p hp

private theorem ctxRel_diagL : (ls : List ((ts : List Ty) × Cont ts)) →
    CtxRel (diagCtxOfL ls) ls ls
  | [] => .nil
  | _ :: ls => .cons List.mem_cons_self
      ((ctxRel_diagL ls).mono fun _ hp => List.mem_cons_of_mem _ hp)

private theorem monoD_diagL : (ls : List ((ts : List Ty) × Cont ts)) → MonoD (diagCtxOfL ls)
  | [], _, h => nomatch h
  | _ :: ls, p, hp => by
      cases hp with | head => exact fun _ _ h => h | tail _ hp => exact monoD_diagL ls p hp

/-! ## §4b. Direct Prefix Independence for `liftGroupNodes` and Acyclic Callee Env -/

private theorem symEvalOp_len (st : SymState) {ts : List Ty} (op : Op K ts) :
    (symEvalOp st op).length = ts.length := by
  rcases op with ⟨code, args⟩
  cases code <;> dsimp only [symEvalOp, symEvalOpCode]
  all_goals try (simp; done)
  all_goals try cases ‹CmpOp›
  all_goals try cases ‹Ty›
  all_goals try (simp; done)
  all_goals
    first
    | (rcases args with ⟨a, ⟨⟩⟩; simp only [List.length_cons, List.length_nil];
       repeat (first | rfl | split))
    | (rcases args with ⟨a, b, ⟨⟩⟩; simp only [List.length_cons, List.length_nil];
       repeat (first | rfl | split))
    | (rcases args with ⟨c, t, e, ⟨⟩⟩; simp only [List.length_cons, List.length_nil];
       try cases c
       repeat (first | rfl | split))

private theorem checkArg_idx_var {Γ : List Ty} {t : Ty} {idx : Nat}
    (hg : listGet? Γ idx = some t) :
    checkArg Γ t (.var idx) = true := by
  dsimp only [checkArg]; rw [hg]; dsimp only
  cases tyDecEq t t with
  | isTrue _ => simp
  | isFalse hne => exact absurd rfl hne

private theorem checkArg_levelHasTy {st : SymState} {lvl : Nat} {t : Ty}
    (hlen : st.env.length = st.ctx.length) (h : st.levelHasTy lvl t = true) :
    checkArg st.ctx t (.var (st.env.length - 1 - lvl)) = true := by
  dsimp only [SymState.levelHasTy] at h
  split at h
  · rw [hlen]
    cases hg : listGet? st.ctx (st.ctx.length - 1 - lvl) with
    | none => rw [hg] at h; cases h
    | some t' =>
        rw [hg] at h; dsimp only at h
        split at h
        · subst ‹t' = t›; exact checkArg_idx_var hg
        · cases h
  · cases h

private theorem checkArg_shiftArg {t : Ty} (extra Γ : List Ty) (a : Arg K t)
    (h : checkArg Γ t a = true) : checkArg (extra ++ Γ) t (shiftArg extra.length a) = true := by
  cases a with
  | imm _ => rfl
  | var i =>
      dsimp only [shiftArg, checkArg] at h ⊢
      rw [Nat.add_comm i extra.length, listGet?_append_skip extra Γ i]; exact h

private theorem checkRegsExpr_shiftRegsExpr (extra Γ : List Ty) (e : RegsExpr K)
    (h : checkRegsExpr Γ e = true) :
    checkRegsExpr (extra ++ Γ) (shiftRegsExpr extra.length e) = true := by
  dsimp only [checkRegsExpr, shiftRegsExpr] at h ⊢; simp only [Bool.and_eq_true] at h ⊢
  exact ⟨⟨⟨⟨⟨checkArg_shiftArg extra Γ _ h.1.1.1.1.1, checkArg_shiftArg extra Γ _ h.1.1.1.1.2⟩,
    checkArg_shiftArg extra Γ _ h.1.1.1.2⟩, checkArg_shiftArg extra Γ _ h.1.1.2⟩,
    checkArg_shiftArg extra Γ _ h.1.2⟩, checkArg_shiftArg extra Γ _ h.2⟩

private theorem checkRegsExpr_toTup {Γ : List Ty} {e : RegsExpr K}
    (h : checkRegsExpr Γ e = true) : checkArgs Γ e.toTup = true := by
  dsimp only [checkRegsExpr] at h; simp only [Bool.and_eq_true] at h
  dsimp only [RegsExpr.toTup, checkArgs]
  simp only [h, Bool.and_true]

private theorem checkArgs_cons {Γ : List Ty} {t : Ty} {ts : List Ty}
    {a : Arg K t} {as : Tup (Arg K) ts}
    (ha : checkArg Γ t a = true) (has : checkArgs Γ as = true) :
    checkArgs Γ (ts := t :: ts) (a, as) = true := by
  change (checkArg Γ t a && checkArgs Γ as) = true
  rw [ha, has]; rfl

private theorem ctxTypes_append {V : Ty → Type} :
    {Γ₁ Γ₂ : List Ty} → {vs₁ vs₂ : List ((t : Ty) × V t)} →
    CtxTypes Γ₁ vs₁ → CtxTypes Γ₂ vs₂ → CtxTypes (Γ₁ ++ Γ₂) (vs₁ ++ vs₂)
  | _, _, _, _, .nil, h₂ => h₂
  | _, _, _, _, .cons h₁, h₂ => .cons (ctxTypes_append h₁ h₂)

private theorem denote_lowerJumpTo_prefix {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (pcs : List (BitVec 64)) (tPc : BitVec 64) (nxt : RegsExpr K)
    {Γ : List Ty} {bvs vsTail : List ((t : Ty) × V t)} {ls : List ((ts : List Ty) × L ts)}
    (hΓ : CtxTypes Γ bvs) (hN : checkRegsExpr Γ nxt = true) :
    denote V L (lowerJumpTo (rs := rs) pcs tPc nxt) (bvs ++ vsTail) ls =
      denote V L (lowerJumpTo (rs := rs) pcs tPc nxt) bvs ls := by
  dsimp only [lowerJumpTo]
  cases findLabelIdx pcs tPc with
  | none => rfl
  | some j => dsimp only [denote]; rw [denoteArgs_prefix vsTail hΓ (checkRegsExpr_toTup hN)]

private theorem denote_lowerStrideCascade_prefix {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (pcs : List (BitVec 64)) (idxVar : Nat) (nxt : RegsExpr K) {Γ : List Ty}
    (hIdx : checkArg Γ i64 (.var idxVar) = true) (hN : checkRegsExpr Γ nxt = true)
    (vsTail : List ((t : Ty) × V t)) (ls : List ((ts : List Ty) × L ts)) :
    ∀ (targets : List (BitVec 64)) (k curShift : Nat) (extraTy : List Ty)
      (extra bvs : List ((t : Ty) × V t)),
      extra.length = curShift → CtxTypes extraTy extra → CtxTypes Γ bvs →
      denote V L (lowerStrideCascade (rs := rs) pcs idxVar nxt k curShift targets)
        (extra ++ (bvs ++ vsTail)) ls =
      denote V L (lowerStrideCascade (rs := rs) pcs idxVar nxt k curShift targets)
        (extra ++ bvs) ls
  | [], _, _, _, _, _, _, _, _ => rfl
  | [tPc], _, curShift, extraTy, extra, bvs, hlen, hEx, hBv => by
      dsimp only [lowerStrideCascade]
      have hC := ctxTypes_append hEx hBv
      have hlen' : extraTy.length = curShift := by rw [ctxTypes_length hEx, hlen]
      have hN' : checkRegsExpr (extraTy ++ Γ) (shiftRegsExpr curShift nxt) = true := by
        rw [← hlen']; exact checkRegsExpr_shiftRegsExpr extraTy Γ nxt hN
      rw [← List.append_assoc]
      exact denote_lowerJumpTo_prefix pcs tPc (shiftRegsExpr curShift nxt) hC hN'
  | tPc :: a :: rest, k, curShift, extraTy, extra, bvs, hlen, hEx, hBv => by
      have hC := ctxTypes_append hEx hBv
      have hlen' : extraTy.length = curShift := by rw [ctxTypes_length hEx, hlen]
      have hA' : checkArg (extraTy ++ Γ) i64 (.var (idxVar + curShift)) = true := by
        rw [← hlen']; exact checkArg_shiftArg extraTy Γ (.var idxVar) hIdx
      dsimp only [lowerStrideCascade, denote, op2, denoteArgs]
      rw [← List.append_assoc, denoteArg_prefix vsTail hC hA', List.append_assoc]
      cases denoteArg (extra ++ bvs) (.var (idxVar + curShift)) with
      | none => rfl
      | some _ =>
          dsimp only [denoteArg]
          congr 1; funext xs
          rcases xs with ⟨b, ⟨⟩⟩
          dsimp only [pushTup]
          have hb0 : lookupV (⟨.bool, b⟩ :: (extra ++ (bvs ++ vsTail))) .bool 0 =
              lookupV (⟨.bool, b⟩ :: (extra ++ bvs)) .bool 0 := rfl
          rw [hb0]
          cases lookupV (⟨.bool, b⟩ :: (extra ++ bvs)) .bool 0 with
          | none => rfl
          | some _ =>
              have hN1 : checkRegsExpr ((.bool :: extraTy) ++ Γ)
                  (shiftRegsExpr (curShift + 1) nxt) = true := by
                have hlen1 : (.bool :: extraTy).length = curShift + 1 := by simp [hlen']
                rw [← hlen1]; exact checkRegsExpr_shiftRegsExpr (.bool :: extraTy) Γ nxt hN
              have ht := denote_lowerJumpTo_prefix (rs := rs) pcs tPc
                (shiftRegsExpr (curShift + 1) nxt) (.cons (v := b) hC) hN1
                (vsTail := vsTail) (ls := ls)
              have he := denote_lowerStrideCascade_prefix (rs := rs) pcs idxVar nxt hIdx hN
                vsTail ls (a :: rest) (k + 1) (curShift + 1) (.bool :: extraTy)
                (⟨.bool, b⟩ :: extra) bvs (by simp [hlen]) (.cons hEx) hBv
              dsimp only [List.cons_append] at ht he
              rw [List.append_assoc] at ht
              rw [ht, he]

private theorem denote_lowerGuardedCascade_prefix {V : Ty → Type} {L : List Ty → Type}
    (pcs : List (BitVec 64)) (tgt : Arg K i64) (nxt : RegsExpr K) {Γ : List Ty}
    (hT : checkArg Γ i64 tgt = true) (hN : checkRegsExpr Γ nxt = true)
    (vsTail : List ((t : Ty) × V t)) (ls : List ((ts : List Ty) × L ts)) :
    ∀ (targets : List (BitVec 64)) (curShift : Nat) (extraTy : List Ty)
      (extra bvs : List ((t : Ty) × V t)),
      extra.length = curShift → CtxTypes extraTy extra → CtxTypes Γ bvs →
      denote V L (lowerGuardedCascade pcs tgt nxt curShift targets)
        (extra ++ (bvs ++ vsTail)) ls =
      denote V L (lowerGuardedCascade pcs tgt nxt curShift targets)
        (extra ++ bvs) ls
  | [], curShift, extraTy, extra, bvs, hlen, hEx, hBv => by
      have hC := ctxTypes_append hEx hBv
      have hlen' : extraTy.length = curShift := by rw [ctxTypes_length hEx, hlen]
      have hT' : checkArg (extraTy ++ Γ) i64 (shiftArg curShift tgt) = true := by
        rw [← hlen']; exact checkArg_shiftArg extraTy Γ tgt hT
      have hN' : checkRegsExpr (extraTy ++ Γ) (shiftRegsExpr curShift nxt) = true := by
        rw [← hlen']; exact checkRegsExpr_shiftRegsExpr extraTy Γ nxt hN
      have hRetChk := checkArgs_cons hT' (checkRegsExpr_toTup hN')
      dsimp only [RegsExpr.toTup] at hRetChk
      dsimp only [lowerGuardedCascade, mkRetEnvelope, denote, RegionAbi.retSig]
      rw [← List.append_assoc, denoteArgs_prefix (ts := i64 :: regSig) vsTail hC hRetChk]
  | hPc :: rest, curShift, extraTy, extra, bvs, hlen, hEx, hBv => by
      have hC := ctxTypes_append hEx hBv
      have hlen' : extraTy.length = curShift := by rw [ctxTypes_length hEx, hlen]
      have hT' : checkArg (extraTy ++ Γ) i64 (shiftArg curShift tgt) = true := by
        rw [← hlen']; exact checkArg_shiftArg extraTy Γ tgt hT
      dsimp only [lowerGuardedCascade, denote, op2, denoteArgs]
      rw [← List.append_assoc, denoteArg_prefix vsTail hC hT', List.append_assoc]
      cases denoteArg (extra ++ bvs) (shiftArg curShift tgt) with
      | none => rfl
      | some _ =>
          dsimp only [denoteArg]
          congr 1; funext xs
          rcases xs with ⟨b, ⟨⟩⟩
          dsimp only [pushTup]
          have hb0 : lookupV (⟨.bool, b⟩ :: (extra ++ (bvs ++ vsTail))) .bool 0 =
              lookupV (⟨.bool, b⟩ :: (extra ++ bvs)) .bool 0 := rfl
          rw [hb0]
          cases lookupV (⟨.bool, b⟩ :: (extra ++ bvs)) .bool 0 with
          | none => rfl
          | some _ =>
              have hN1 : checkRegsExpr ((.bool :: extraTy) ++ Γ)
                  (shiftRegsExpr (curShift + 1) nxt) = true := by
                have hlen1 : (.bool :: extraTy).length = curShift + 1 := by simp [hlen']
                rw [← hlen1]; exact checkRegsExpr_shiftRegsExpr (.bool :: extraTy) Γ nxt hN
              have ht := denote_lowerJumpTo_prefix (rs := RegionAbi.retEnvelope.retSig) pcs hPc
                (shiftRegsExpr (curShift + 1) nxt) (.cons (v := b) hC) hN1
                (vsTail := vsTail) (ls := ls)
              have he := denote_lowerGuardedCascade_prefix pcs tgt nxt hT hN vsTail ls
                rest (curShift + 1) (.bool :: extraTy) (⟨.bool, b⟩ :: extra) bvs
                (by simp [hlen]) (.cons hEx) hBv
              dsimp only [List.cons_append] at ht he
              rw [List.append_assoc] at ht
              rw [ht, he]

private theorem denote_liftEdge_prefix {V : Ty → Type} {L : List Ty → Type}
    {cm : CodeMap} {abi : RegionAbi} {callees : List CalleeMeta} {pcs : List (BitVec 64)}
    {st : SymState} {tgt : Arg K i64} {nxt : RegsExpr K} {path : BranchPath} {kind : EdgeKind}
    {bvs vsTail : List ((t : Ty) × V t)} {ls : List ((ts : List Ty) × L ts)}
    (hlen : st.env.length = st.ctx.length) (hctx : CtxTypes st.ctx bvs)
    (hT : checkArg st.ctx i64 tgt = true) (hN : checkRegsExpr st.ctx nxt = true)
    (hEdge : checkEdgeLeaf cm abi callees pcs ⟨path, st, tgt, nxt⟩ kind = true) :
    denote V L (liftEdge abi pcs st tgt nxt kind) (bvs ++ vsTail) ls =
      denote V L (liftEdge abi pcs st tgt nxt kind) bvs ls := by
  dsimp only [checkEdgeLeaf] at hEdge
  cases kind with
  | direct targetPc => exact denote_lowerJumpTo_prefix pcs targetPc nxt hctx hN
  | select tPc ePc =>
      simp only [Bool.and_eq_true] at hEdge
      dsimp only [liftEdge]
      cases hev : st.evalArg tgt <;> rw [hev] at hEdge <;> try (cases hEdge.2)
      rename_i cLvl tSym eSym
      dsimp only at hEdge; simp only [Bool.and_eq_true] at hEdge
      have hc : checkArg st.ctx .bool (.var (st.env.length - 1 - cLvl)) = true :=
        checkArg_levelHasTy hlen hEdge.2.1.1
      dsimp only [denote]
      rw [denoteArg_prefix vsTail hctx hc]
      cases denoteArg bvs (.var (st.env.length - 1 - cLvl)) with
      | none => rfl
      | some _ =>
          rw [denote_lowerJumpTo_prefix pcs tPc nxt hctx hN,
              denote_lowerJumpTo_prefix pcs ePc nxt hctx hN]
  | strideTable basePc targets needGuard =>
      simp only [Bool.and_eq_true] at hEdge
      dsimp only [liftEdge]
      cases hev : st.evalArg tgt <;> rw [hev] at hEdge <;> try (cases hEdge.2)
      rename_i b lvl
      dsimp only at hEdge; simp only [Bool.and_eq_true] at hEdge
      have hidx : checkArg st.ctx i64 (.var (st.env.length - 1 - lvl)) = true :=
        checkArg_levelHasTy hlen hEdge.2.1.2
      cases needGuard
      · exact denote_lowerStrideCascade_prefix pcs _ nxt hidx hN vsTail ls targets 0 0 [] [] bvs
          rfl .nil hctx
      · cases abi
        · dsimp only [denote, op2, denoteArgs]
          rw [denoteArg_prefix vsTail hctx hidx]
          cases denoteArg bvs (.var (st.env.length - 1 - lvl)) with
          | none => rfl
          | some _ =>
              dsimp only [denoteArg]
              congr 1; funext xs
              rcases xs with ⟨u, ⟨⟩⟩
              dsimp only [pushTup]
              have hu0 : lookupV (⟨.bool, u⟩ :: (bvs ++ vsTail)) .bool 0 =
                  lookupV (⟨.bool, u⟩ :: bvs) .bool 0 := rfl
              rw [hu0]
              cases lookupV (⟨.bool, u⟩ :: bvs) .bool 0 with
              | none => rfl
              | some _ =>
                  have hs := denote_lowerStrideCascade_prefix (rs := i64 :: regSig) pcs _ nxt
                    hidx hN vsTail ls targets 0 1 [.bool] [⟨.bool, u⟩] bvs rfl (.cons .nil) hctx
                  have hT1 : checkArg (.bool :: st.ctx) i64 (shiftArg 1 tgt) = true :=
                    checkArg_shiftArg [.bool] st.ctx tgt hT
                  have hN1 : checkRegsExpr (.bool :: st.ctx) (shiftRegsExpr 1 nxt) = true :=
                    checkRegsExpr_shiftRegsExpr [.bool] st.ctx nxt hN
                  have hRetChk := checkArgs_cons hT1 (checkRegsExpr_toTup hN1)
                  dsimp only [RegsExpr.toTup] at hRetChk
                  dsimp only [List.cons_append, List.nil_append] at hs
                  dsimp only [mkRetEnvelope, denote, RegionAbi.retSig]
                  rw [hs, ← List.cons_append,
                    denoteArgs_prefix (ts := i64 :: regSig) vsTail
                      (CtxTypes.cons (v := u) hctx) hRetChk]
        · simp [RegionAbi.isContified] at hEdge
  | contCall callee calleePc dualRet retPc altRetPc? =>
      cases abi
      · simp only [RegionAbi.isContified, Bool.not_false, Bool.true_and, Bool.and_eq_true] at hEdge
        dsimp only [liftEdge]
        cases dualRet
        · simp only [Bool.false_eq_true, ↓reduceIte, RegionAbi.retSig]
          dsimp only [denote]
          rw [denoteArgs_prefix vsTail hctx (checkRegsExpr_toTup hN)]
          cases denoteArgs bvs nxt.toTup with
          | none => rfl
          | some _ =>
              dsimp only; congr 1; funext xs
              rcases xs with ⟨sp, rp, rv, r1, r2, r3, ⟨⟩⟩
              rw [pushTup_append]
              exact denote_lowerJumpTo_prefix pcs retPc _ (CtxTypes.push _ hctx) (by rfl)
        · cases altRetPc? with
          | none => simp at hEdge
          | some altPc =>
              simp only [↓reduceIte, RegionAbi.retSig]
              dsimp only [denote]
              rw [denoteArgs_prefix vsTail hctx (checkRegsExpr_toTup hN)]
              cases denoteArgs bvs nxt.toTup with
              | none => rfl
              | some _ =>
                  dsimp only; congr 1; funext xs
                  rcases xs with ⟨b, sp, rp, rv, r1, r2, r3, ⟨⟩⟩
                  have hctx' : CtxTypes (pushTypes (.bool :: regSig) st.ctx)
                      (pushTup (b, sp, rp, rv, r1, r2, r3, ()) bvs) := CtxTypes.push _ hctx
                  rw [pushTup_append]
                  have hb6 : denoteArg
                      (pushTup (as := .bool :: regSig) (b, sp, rp, rv, r1, r2, r3, ()) bvs ++
                        vsTail) (t := .bool) (.var 6) =
                      denoteArg
                        (pushTup (as := .bool :: regSig) (b, sp, rp, rv, r1, r2, r3, ()) bvs)
                        (t := .bool) (.var 6) := rfl
                  rw [hb6]
                  cases denoteArg
                      (pushTup (as := .bool :: regSig) (b, sp, rp, rv, r1, r2, r3, ()) bvs)
                      (t := .bool) (.var 6) with
                  | none => rfl
                  | some _ =>
                      rw [denote_lowerJumpTo_prefix pcs altPc _ hctx' (by rfl),
                          denote_lowerJumpTo_prefix pcs retPc _ hctx' (by rfl)]
      · simp [RegionAbi.isContified] at hEdge
  | contRet isAlt =>
      cases abi with
      | retEnvelope => simp at hEdge
      | contified dualRet =>
          cases dualRet <;> cases isAlt
          · dsimp only [liftEdge, denote, RegionAbi.retSig]
            rw [denoteArgs_prefix vsTail hctx (checkRegsExpr_toTup hN)]
          · simp at hEdge
          · have hA : checkArgs st.ctx (ts := .bool :: regSig) (.imm false, nxt.toTup) = true :=
              checkRegsExpr_toTup hN
            dsimp only [liftEdge, denote, RegionAbi.retSig]
            rw [denoteArgs_prefix vsTail hctx hA]
          · have hA : checkArgs st.ctx (ts := .bool :: regSig) (.imm true, nxt.toTup) = true :=
              checkRegsExpr_toTup hN
            dsimp only [liftEdge, denote, RegionAbi.retSig]
            rw [denoteArgs_prefix vsTail hctx hA]
  | guarded hotTargets =>
      cases abi
      · exact denote_lowerGuardedCascade_prefix pcs tgt nxt hT hN vsTail ls hotTargets 0 [] [] bvs
          rfl .nil hctx
      · simp [RegionAbi.isContified] at hEdge
  | bailout =>
      cases abi
      · have hB := checkArgs_cons hT (checkRegsExpr_toTup hN)
        dsimp only [RegsExpr.toTup] at hB
        dsimp only [liftEdge, mkRetEnvelope, denote, RegionAbi.retSig]
        rw [denoteArgs_prefix (ts := i64 :: regSig) vsTail hctx hB]
      · simp [RegionAbi.isContified] at hEdge

private theorem pushTypes_len {α : Type} :
    (ts acc : List α) → (pushTypes ts acc).length = ts.length + acc.length
  | [], acc => (Nat.zero_add acc.length).symm
  | a :: ts, acc => by
      dsimp only [pushTypes, List.length_cons]
      rw [pushTypes_len ts (a :: acc), List.length_cons]
      omega

private theorem pushCondFact_env (st : SymState) (c : Arg K .bool) (b : Bool) :
    (st.pushCondFact c b).env = st.env := by
  dsimp only [SymState.pushCondFact]
  split
  · cases c with
    | imm _ => rfl
    | var _ => dsimp only; split <;> rfl
  · rfl

private theorem denote_liftBlock_prefix {V : Ty → Type} {L : List Ty → Type}
    {cm : CodeMap} {rw : RegionWitness} {callees : List CalleeMeta}
    {pcs : List (BitVec 64)} {pc : BitVec 64} {ls : List ((ts : List Ty) × L ts)} :
    ∀ (b : BlockFlat) (path : BranchPath) (st : SymState)
      (bvs vsTail : List ((t : Ty) × V t)) (leaves : List SymLeaf),
      st.env.length = st.ctx.length → CtxTypes st.ctx bvs → b.wfCheck st.ctx = true →
      symEvalBlock cm b path st = some leaves →
      (∀ lf ∈ leaves, ∃ ew, rw.findEdge pc lf.path = some ew ∧
        checkEdgeLeaf cm rw.abi callees pcs lf ew.kind = true) →
      denote V L (liftBlock cm rw pcs pc b path st) (bvs ++ vsTail) ls =
        denote V L (liftBlock cm rw pcs pc b path st) bvs ls
  | .let_ (ts := ts) op k, path, st, bvs, vsTail, leaves, hlen, hctx, hwf, hlv, hleaves => by
      dsimp only [BlockFlat.wfCheck] at hwf; rcases Bool.and_eq_true_iff.1 hwf with ⟨hwfA, hwfK⟩
      dsimp only [symEvalBlock] at hlv
      dsimp only [liftBlock, denote]
      rw [denoteArgs_prefix vsTail hctx hwfA]
      cases denoteArgs bvs op.args with
      | none => rfl
      | some _ =>
          dsimp only; congr 1; funext xs
          rw [pushTup_append]
          have hlen' : (st.pushRes ts (symEvalOp st op)).env.length =
              (st.pushRes ts (symEvalOp st op)).ctx.length := by
            dsimp only [SymState.pushRes]
            rw [List.length_append, pushTypes_len, symEvalOp_len, hlen, Nat.add_comm]
          exact denote_liftBlock_prefix k path _ (pushTup xs bvs) vsTail leaves hlen'
            (CtxTypes.push xs hctx) hwfK hlv hleaves
  | .load t a k, path, st, bvs, vsTail, leaves, hlen, hctx, hwf, hlv, hleaves => by
      dsimp only [BlockFlat.wfCheck] at hwf; rcases Bool.and_eq_true_iff.1 hwf with ⟨hwfA, hwfK⟩
      dsimp only [liftBlock, denote]
      rw [denoteArg_prefix vsTail hctx hwfA]
      cases denoteArg bvs a with
      | none => rfl
      | some _ =>
          dsimp only; congr 1; funext v
          exact denote_liftBlock_prefix k path _ (⟨t, v⟩ :: bvs) vsTail leaves
            (by simp [hlen]) (.cons hctx) hwfK hlv hleaves
  | .store v a k, path, st, bvs, vsTail, leaves, hlen, hctx, hwf, hlv, hleaves => by
      dsimp only [BlockFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      dsimp only [liftBlock, denote]
      rw [denoteArg_prefix vsTail hctx hwf.1.1, denoteArg_prefix vsTail hctx hwf.1.2]
      cases denoteArg bvs v <;> cases denoteArg bvs a <;> try rfl
      exact congrArg _
        (denote_liftBlock_prefix k path st bvs vsTail leaves hlen hctx hwf.2 hlv hleaves)
  | .codeAddr sym k, path, st, bvs, vsTail, leaves, hlen, hctx, hwf, hlv, hleaves => by
      dsimp only [symEvalBlock] at hlv
      dsimp only [liftBlock]
      cases haddr : cm.addrOf? sym with
      | none => rw [haddr] at hlv; cases hlv
      | some a =>
          rw [haddr] at hlv
          dsimp only [denote, op1, denoteArgs, denoteArg]
          congr 1; funext xs
          rcases xs with ⟨v, ⟨⟩⟩
          exact denote_liftBlock_prefix k path _ (⟨i64, v⟩ :: bvs) vsTail leaves
            (by simp [hlen]) (.cons hctx) hwf hlv hleaves
  | .jnz c t e, path, st, bvs, vsTail, leaves, hlen, hctx, hwf, hlv, hleaves => by
      dsimp only [BlockFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      dsimp only [symEvalBlock] at hlv
      cases hlt : symEvalBlock cm t (path ++ [true]) (st.pushCondFact c true) with
      | none => simp [hlt] at hlv
      | some lt =>
          cases hle : symEvalBlock cm e (path ++ [false]) (st.pushCondFact c false) with
          | none => simp [hlt, hle] at hlv
          | some le =>
              simp only [hlt, hle] at hlv; cases hlv
              dsimp only [liftBlock, denote]
              rw [denoteArg_prefix vsTail hctx hwf.1.1]
              cases denoteArg bvs c with
              | none => rfl
              | some _ =>
                  have hltP := denote_liftBlock_prefix (ls := ls) t (path ++ [true])
                    (st.pushCondFact c true) bvs vsTail lt
                    (by rw [pushCondFact_env, pushCondFact_ctx]; exact hlen)
                    (by rw [pushCondFact_ctx]; exact hctx)
                    (by rw [pushCondFact_ctx]; exact hwf.1.2) hlt
                    (fun lf hm => hleaves lf (List.mem_append_left le hm))
                  have hleP := denote_liftBlock_prefix (ls := ls) e (path ++ [false])
                    (st.pushCondFact c false) bvs vsTail le
                    (by rw [pushCondFact_env, pushCondFact_ctx]; exact hlen)
                    (by rw [pushCondFact_ctx]; exact hctx)
                    (by rw [pushCondFact_ctx]; exact hwf.2) hle
                    (fun lf hm => hleaves lf (List.mem_append_right lt hm))
                  rw [hltP, hleP]
  | .ijmp tgt nxt, path, st, bvs, vsTail, leaves, hlen, hctx, hwf, hlv, hleaves => by
      dsimp only [BlockFlat.wfCheck] at hwf; rcases Bool.and_eq_true_iff.1 hwf with ⟨hwfT, hwfN⟩
      dsimp only [symEvalBlock] at hlv; cases hlv
      obtain ⟨ew, hfind, hchk⟩ := hleaves ⟨path, st, tgt, nxt⟩ List.mem_cons_self
      dsimp only [liftBlock]; rw [hfind]
      exact denote_liftEdge_prefix hlen hctx hwfT hwfN hchk
  | .halt c, _, _, bvs, vsTail, _, _, hctx, hwf, _, _ => by
      dsimp only [BlockFlat.wfCheck] at hwf
      dsimp only [liftBlock, denote, denoteArgs]
      rw [denoteArg_prefix vsTail hctx hwf]
  | .hlt, _, _, _, _, _, _, _, _, _, _ => rfl

mutual
private theorem denote_liftGroupNode_prefix {V : Ty → Type} {L : List Ty → Type}
    {cm : CodeMap} {rw : RegionWitness} {callees : List CalleeMeta} :
    (pcs : List (BitVec 64)) → (g : GroupTree) →
    checkGroupNode cm rw callees pcs g = true →
    ∀ (bvs vsTail : List ((t : Ty) × V t)) (ls : List ((ts : List Ty) × L ts)),
      CtxTypes regCtx bvs →
      denote V L (liftGroupNode cm rw pcs g) (bvs ++ vsTail) ls =
        denote V L (liftGroupNode cm rw pcs g) bvs ls
  | pcs, .leaf pc, hchk, bvs, vsTail, ls, hctx => by
      dsimp only [checkGroupNode, checkBlockLeaves] at hchk
      dsimp only [liftGroupNode]
      cases hlu : cm.lookupAddr pc with
      | none => rw [hlu] at hchk; cases hchk
      | some b =>
          rw [hlu] at hchk; simp only [Bool.and_eq_true] at hchk
          cases hsym : symEvalBlock cm b [] SymState.init with
          | none => rw [hsym] at hchk; simp at hchk
          | some leaves =>
              rw [hsym] at hchk
              have hleaves : ∀ lf ∈ leaves, ∃ ew, rw.findEdge pc lf.path = some ew ∧
                  checkEdgeLeaf cm rw.abi callees pcs lf ew.kind = true := by
                intro lf hm
                have ha := List.all_eq_true.1 hchk.2 lf hm
                cases hf : rw.findEdge pc lf.path with
                | none => rw [hf] at ha; cases ha
                | some ew => rw [hf] at ha; exact ⟨ew, rfl, ha⟩
              exact denote_liftBlock_prefix b [] SymState.init bvs vsTail leaves rfl hctx
                hchk.1.1 hsym hleaves
  | pcs, .loop header nodes, hchk, bvs, vsTail, ls, hctx => by
      dsimp only [checkGroupNode] at hchk; simp only [Bool.and_eq_true] at hchk
      dsimp only [liftGroupNode, denote]
      congr 1
      · funext Jv
        rw [denote_liftGroupNodes_prefix _ nodes hchk.2 (bvs ++ vsTail) (pushTup Jv ls),
            denote_liftGroupNodes_prefix _ nodes hchk.2 bvs (pushTup Jv ls)]
      · funext Jv
        exact denote_lowerJumpTo_prefix _ header _ hctx (by rfl)

private theorem denote_liftGroupNodes_prefix {V : Ty → Type} {L : List Ty → Type}
    {cm : CodeMap} {rw : RegionWitness} {callees : List CalleeMeta} :
    (pcs : List (BitVec 64)) → (gs : List GroupTree) →
    checkGroupNodes cm rw callees pcs gs = true →
    ∀ (vs : List ((t : Ty) × V t)) (ls : List ((ts : List Ty) × L ts)),
      denoteB V L (liftGroupNodes cm rw pcs gs) vs ls =
        denoteB V L (liftGroupNodes cm rw pcs gs) [] ls
  | _, [], _, _, _ => rfl
  | pcs, g :: gs, hchk, vs, ls => by
      dsimp only [checkGroupNodes] at hchk; rcases Bool.and_eq_true_iff.1 hchk with ⟨hg, hgs⟩
      dsimp only [liftGroupNodes, denoteB]
      congr 1
      · funext xs
        exact denote_liftGroupNode_prefix pcs g hg (pushTup xs []) vs ls (CtxTypes.push xs .nil)
      · exact denote_liftGroupNodes_prefix pcs gs hgs vs ls
end

/-! ## §4c. Park's Induction, Acyclic Callee Environment, and Canonical `GroupTree` GFP -/

private theorem park_induction {α : Type} {F : Xcap.Lfp.Pred α → Xcap.Lfp.Pred α}
    (hMono : Xcap.Lfp.mono F) {P : Xcap.Lfp.Pred α}
    (hStep : ∀ a, F (fun x => Xcap.Lfp.lfp F x ∧ P x) a → P a) :
    ∀ a, Xcap.Lfp.lfp F a → P a := by
  intro a ha
  have hClosed : Xcap.Lfp.Closed F (fun x => Xcap.Lfp.lfp F x ∧ P x) := fun x hx =>
    ⟨Xcap.Lfp.lfp_closed hMono x (hMono (fun _ h => h.1) x hx), hStep x hx⟩
  exact (Xcap.Lfp.lfp_le hClosed a ha).2

/-- Callee environment extending `Γ` over an acyclic list of regions in callee-first order. -/
@[expose] def witEnvAux (cm : CodeMap) (Γ : Env) : List RegionWitness → Env
  | [] => Γ
  | rw :: rws =>
      let Γ' : Env := fun f as bs xs m P E =>
        ((∃ dualRet, rw.abi = .contified dualRet) ∧ f = rw.name ∧
          ∃ (h₁ : as = (liftRegion cm rw).as) (h₂ : bs = (liftRegion cm rw).rs),
            Func.spec Γ (liftRegion cm rw).body (h₁ ▸ xs) m (h₂ ▸ P) E) ∨
        Γ f as bs xs m P E
      witEnvAux cm Γ' rws

/-- Global callee environment associated with `wit`. -/
@[expose] def witEnv (cm : CodeMap) (wit : CfgWitness) : Env :=
  witEnvAux cm (fun _ _ _ _ _ _ _ => False) wit.regions

private theorem witEnvAux_base_mono (cm : CodeMap) {Γ₁ Γ₂ : Env}
    (hΓ : ∀ f as bs xs m P E, Γ₁ f as bs xs m P E → Γ₂ f as bs xs m P E) :
    ∀ rws f as bs xs m P E, witEnvAux cm Γ₁ rws f as bs xs m P E →
      witEnvAux cm Γ₂ rws f as bs xs m P E
  | [], _, _, _, _, _, _, _, h => hΓ _ _ _ _ _ _ _ h
  | rw :: rws, f, as, bs, xs, m, P, E, h => by
      apply witEnvAux_base_mono cm (Γ₁ := _) (Γ₂ := _) (fun g cs ds ys m' P' E' hg => by
        rcases hg with ⟨hd, rfl, rfl, rfl, hSp⟩ | hg
        · exact Or.inl ⟨hd, rfl, rfl, rfl, Func.spec_env_mono hΓ hSp⟩
        · exact Or.inr (hΓ _ _ _ _ _ _ _ hg)) rws f as bs xs m P E h

private theorem witEnvAux_mono_right (cm : CodeMap) (Γ : Env) :
    ∀ rws f as bs xs m P E, Γ f as bs xs m P E → witEnvAux cm Γ rws f as bs xs m P E
  | [], _, _, _, _, _, _, _, h => h
  | _ :: rws, f, as, bs, xs, m, P, E, h =>
      witEnvAux_mono_right cm _ rws f as bs xs m P E (Or.inr h)

private theorem witEnvAux_append (cm : CodeMap) (Γ : Env) (pre post : List RegionWitness) :
    witEnvAux cm Γ (pre ++ post) = witEnvAux cm (witEnvAux cm Γ pre) post := by
  induction pre generalizing Γ with
  | nil => rfl
  | cons _ _ ih => exact ih _

private theorem witEnvAux_mem_prefix (cm : CodeMap) (Γ : Env) (pre : List RegionWitness)
    (rw : RegionWitness) (post : List RegionWitness) (dualRet : Bool)
    (habi : rw.abi = .contified dualRet) {xs m P E}
    (hSpec : Func.spec (witEnvAux cm Γ pre) (liftRegion cm rw).body xs m P E) :
    witEnvAux cm Γ (pre ++ rw :: post) rw.name regSig rw.abi.retSig xs m P E := by
  rw [witEnvAux_append]
  dsimp only [witEnvAux]
  refine witEnvAux_mono_right cm _ post _ _ _ _ _ _ _ ?_
  exact Or.inl ⟨⟨dualRet, habi⟩, rfl, rfl, rfl, hSpec⟩

private def calleesStep (rw : RegionWitness) (cs : List CalleeMeta) : List CalleeMeta :=
  match rw.toCalleeMeta? with | some c => c :: cs | none => cs

private def calleesFold (cs : List CalleeMeta) : List RegionWitness → List CalleeMeta
  | [] => cs
  | rw :: rws => calleesFold (calleesStep rw cs) rws

private theorem checkAux_append (cm : CodeMap) :
    ∀ (pre post : List RegionWitness) (cs : List CalleeMeta),
      CfgWitness.checkAux cm cs (pre ++ post) = true →
      CfgWitness.checkAux cm (calleesFold cs pre) post = true
  | [], _, _, h => h
  | rw :: pre, post, cs, h => by
      dsimp only [List.cons_append, CfgWitness.checkAux] at h
      simp only [Bool.and_eq_true] at h
      exact checkAux_append cm pre post (calleesStep rw cs) h.2

private theorem mem_calleesFold :
    ∀ (pre : List RegionWitness) (cs : List CalleeMeta) (c : CalleeMeta),
      c ∈ calleesFold cs pre → c ∈ cs ∨ ∃ rw ∈ pre, rw.toCalleeMeta? = some c
  | [], _, _, hc => Or.inl hc
  | rw :: pre, cs, c, hc => by
      rcases mem_calleesFold pre (calleesStep rw cs) c hc with hc' | ⟨rw', hmem, hto⟩
      · cases h : rw.toCalleeMeta? with
        | none => simp only [calleesStep, h] at hc'; exact Or.inl hc'
        | some m =>
            simp only [calleesStep, h] at hc'
            rcases List.mem_cons.1 hc' with rfl | hc''
            · exact Or.inr ⟨rw, List.mem_cons_self, h⟩
            · exact Or.inl hc''
      · exact Or.inr ⟨rw', List.mem_cons_of_mem _ hmem, hto⟩

mutual
private def treeSize : GroupTree → Nat
  | .leaf _ => 1
  | .loop _ nodes => 1 + treeListSize nodes

private def treeListSize : List GroupTree → Nat
  | [] => 1
  | g :: gs => 1 + treeSize g + treeListSize gs
end

private theorem treeListSize_mem (g : GroupTree) :
    ∀ gs, g ∈ gs → treeSize g < treeListSize gs
  | [], h => by cases h
  | x :: gs, h => by
      rcases List.mem_cons.1 h with rfl | h'
      · simp only [treeListSize]; omega
      · have ih := treeListSize_mem g gs h'
        simp only [treeListSize]; omega

mutual
private def canonNodePred (cm : CodeMap) (rw : RegionWitness) (Γ : Env)
    (Q : Post rw.abi.retSig) (X : XPost)
    (pcs' : List (BitVec 64)) (ls' : List ((ts : List Ty) × Cont ts)) :
    GroupTree → Cont regSig → CodeSpec
  | .leaf pc₀, J, pc, st => pc = pc₀ → J st.regs.toRegsV.toTup st.mem
  | .loop header nodes, J, pc, st =>
      (pc = header → J st.regs.toRegsV.toTup st.mem) ∧
      let pcs'' := pushLabelPcs (nodes.map GroupTree.entryPc) pcs'
      let Js := lfp Γ Q X
        (fun Jv => denoteB Val Cont (liftGroupNodes cm rw pcs'' nodes) [] (pushTup Jv ls'))
      canonTupPred cm rw Γ Q X pcs'' (pushTup Js ls') nodes Js pc st

private def canonTupPred (cm : CodeMap) (rw : RegionWitness) (Γ : Env)
    (Q : Post rw.abi.retSig) (X : XPost)
    (pcs' : List (BitVec 64)) (ls' : List ((ts : List Ty) × Cont ts)) :
    (gs : List GroupTree) → Tup Cont (gs.map fun _ => regSig) → CodeSpec
  | [], (), _, _ => True
  | g :: gs, (J, Js), pc, st =>
      canonNodePred cm rw Γ Q X pcs' ls' g J pc st ∧
      canonTupPred cm rw Γ Q X pcs' ls' gs Js pc st
end

private def canonNodesPred (cm : CodeMap) (rw : RegionWitness) (Γ : Env)
    (Q : Post rw.abi.retSig) (X : XPost)
    (gs : List GroupTree) (pcsOuter : List (BitVec 64))
    (lsOuter : List ((ts : List Ty) × Cont ts)) : CodeSpec :=
  let pcs' := pushLabelPcs (gs.map GroupTree.entryPc) pcsOuter
  let Js := lfp Γ Q X
    (fun Jv => denoteB Val Cont (liftGroupNodes cm rw pcs' gs) [] (pushTup Jv lsOuter))
  canonTupPred cm rw Γ Q X pcs' (pushTup Js lsOuter) gs Js

private def memberOfPrefix :
    (gsPre : List GroupTree) → (g : GroupTree) → (gsPost : List GroupTree) →
    Member regSig ((gsPre ++ g :: gsPost).map fun _ => regSig)
  | [], _, _ => .here
  | _ :: gsPre, g, gsPost => .there (memberOfPrefix gsPre g gsPost)

private theorem denoteB_get_memberOfPrefix {V : Ty → Type} {L : List Ty → Type}
    (cm : CodeMap) (rw : RegionWitness) (pcs : List (BitVec 64))
    (vs : List ((t : Ty) × V t)) (ls : List ((ts : List Ty) × L ts))
    (xs : Tup V regSig) :
    ∀ (gsPre : List GroupTree) (g : GroupTree) (gsPost : List GroupTree),
      (denoteB V L (liftGroupNodes cm rw pcs (gsPre ++ g :: gsPost)) vs ls).get
        (memberOfPrefix gsPre g gsPost) xs =
      denote V L (liftGroupNode cm rw pcs g) (pushTup xs vs) ls
  | [], _, _ => rfl
  | _ :: gsPre, g, gsPost => denoteB_get_memberOfPrefix cm rw pcs vs ls xs gsPre g gsPost

private theorem canonTupPred_get {cm : CodeMap} {rw : RegionWitness} {Γ : Env}
    {Q : Post rw.abi.retSig} {X : XPost}
    {pcs' : List (BitVec 64)} {ls' : List ((ts : List Ty) × Cont ts)} :
    ∀ (gsPre : List GroupTree) (g : GroupTree) (gsPost : List GroupTree)
      (Js : Tup Cont ((gsPre ++ g :: gsPost).map fun _ => regSig)) {pc st},
      canonTupPred cm rw Γ Q X pcs' ls' (gsPre ++ g :: gsPost) Js pc st →
      canonNodePred cm rw Γ Q X pcs' ls' g (Js.get (memberOfPrefix gsPre g gsPost)) pc st
  | [], _, _, (_, _), _, _, h => h.1
  | _ :: gsPre, g, gsPost, (_, Js), _, _, h => canonTupPred_get gsPre g gsPost Js h.2

private theorem tupGet_cons_eq {g : GroupTree} {gs gsPre : List GroupTree} {g' : GroupTree}
    {gsPost : List GroupTree} (heq : gs = gsPre ++ g' :: gsPost)
    (heq' : g :: gs = (g :: gsPre) ++ g' :: gsPost)
    (J : Cont regSig) (Js : Tup Cont (gs.map fun _ => regSig)) :
    Tup.get (a := regSig) (as := (g :: gs).map fun _ => regSig) (J, Js)
      (heq' ▸ memberOfPrefix (g :: gsPre) g' gsPost) =
    Js.get (heq ▸ memberOfPrefix gsPre g' gsPost) := by
  subst heq; rfl

private theorem canonTupPred_get_eq {cm : CodeMap} {rw : RegionWitness} {Γ : Env}
    {Q : Post rw.abi.retSig} {X : XPost} {pcs' : List (BitVec 64)}
    {ls' : List ((ts : List Ty) × Cont ts)} {gs : List GroupTree}
    (gsPre : List GroupTree) (g : GroupTree) (gsPost : List GroupTree)
    (heq : gs = gsPre ++ g :: gsPost)
    (Js : Tup Cont (gs.map fun _ => regSig)) {pc st}
    (h : canonTupPred cm rw Γ Q X pcs' ls' gs Js pc st) :
    canonNodePred cm rw Γ Q X pcs' ls' g (Js.get (heq ▸ memberOfPrefix gsPre g gsPost)) pc st := by
  subst heq; exact canonTupPred_get gsPre g gsPost Js h

private theorem canonTupPred_of_forall {cm : CodeMap} {rw : RegionWitness} {Γ : Env}
    {Q : Post rw.abi.retSig} {X : XPost}
    {pcs' : List (BitVec 64)} {ls' : List ((ts : List Ty) × Cont ts)} {pc st} :
    ∀ (gs : List GroupTree) (Js : Tup Cont (gs.map fun _ => regSig)),
      (∀ gsPre g gsPost (h : gs = gsPre ++ g :: gsPost),
        canonNodePred cm rw Γ Q X pcs' ls' g
          (Js.get (h ▸ memberOfPrefix gsPre g gsPost)) pc st) →
      canonTupPred cm rw Γ Q X pcs' ls' gs Js pc st
  | [], (), _ => trivial
  | g :: gs, (J, Js), h =>
      ⟨h [] g gs rfl,
       canonTupPred_of_forall gs Js fun gsPre g' gsPost heq => by
         have h0 := h (g :: gsPre) g' gsPost (by rw [heq]; rfl)
         rwa [tupGet_cons_eq heq (by rw [heq]; rfl) J Js] at h0⟩

private theorem canonTupPred_tupMemPred {cm : CodeMap} {rw : RegionWitness} {Γ : Env}
    {Q : Post rw.abi.retSig} {X : XPost}
    {pcs' : List (BitVec 64)} {ls' : List ((ts : List Ty) × Cont ts)} {Pred : CodeSpec} :
    ∀ (gs : List GroupTree) (Js : Tup Cont (gs.map fun _ => regSig)),
      (∀ g ∈ gs, ∀ r m, Pred g.entryPc ⟨r, m⟩ →
        canonTupPred cm rw Γ Q X pcs' ls' gs Js g.entryPc ⟨r, m⟩) →
      TupMemPred gs Js Pred
  | [], (), _ => trivial
  | .leaf pc₀ :: gs, (_J, Js), h =>
      ⟨fun r m hP => (h (.leaf pc₀) List.mem_cons_self r m hP).1 rfl,
       canonTupPred_tupMemPred gs Js fun g hg r m hP =>
         (h g (List.mem_cons_of_mem _ hg) r m hP).2⟩
  | .loop hd ns :: gs, (_J, Js), h =>
      ⟨fun r m hP => (h (.loop hd ns) List.mem_cons_self r m hP).1.1 rfl,
       canonTupPred_tupMemPred gs Js fun g hg r m hP =>
         (h g (List.mem_cons_of_mem _ hg) r m hP).2⟩

private theorem castListTy_self_proof (ts : List Ty) (l : Cont ts) :
    castListTy ts ts l = some l := by
  dsimp only [castListTy]
  cases h : listTyDecEq ts ts with
  | isFalse hne => exact absurd rfl hne
  | isTrue heq => have h' : heq = rfl := rfl; rw [h']

private theorem lookupL_pushTup_entry :
    ∀ (gs : List GroupTree) (Js : Tup Cont (gs.map fun _ => regSig))
      (pcs : List (BitVec 64)) (ls : List ((ts : List Ty) × Cont ts))
      (Pred : CodeSpec) (r : Regs) (m : Mem 64) (p : BitVec 64),
      TupMemPred gs Js Pred →
      (p ∈ gs.map GroupTree.entryPc → Pred p ⟨r, m⟩) →
      (p ∈ gs.map GroupTree.entryPc ∨ ∃ idx, findLabelIdx pcs p = some idx ∧
        ∃ J, lookupL ls regSig idx = some J ∧ J r.toRegsV.toTup m) →
      ∃ idx J, findLabelIdx (pushLabelPcs (gs.map GroupTree.entryPc) pcs) p = some idx ∧
        lookupL (pushTup Js ls) regSig idx = some J ∧ J r.toRegsV.toTup m
  | [], (), _, _, _, _, _, _, _, _, Or.inl hp => by cases hp
  | [], (), _, _, _, _, _, _, _, _, Or.inr ⟨idx, hidx, J, hL, hJ⟩ =>
      ⟨idx, J, hidx, hL, hJ⟩
  | g :: gs, (J, Js), pcs, ls, Pred, r, m, p, ⟨hJ, hRest⟩, hP, hIn => by
      dsimp only [List.map_cons, pushLabelPcs, pushTup]
      apply lookupL_pushTup_entry gs Js (g.entryPc :: pcs) (⟨regSig, J⟩ :: ls) Pred r m p hRest
        (fun hm => hP (List.mem_cons_of_mem _ hm))
      by_cases heq : g.entryPc = p
      · subst heq
        refine Or.inr ⟨0, by simp [findLabelIdx], J, ?_, hJ r m (hP List.mem_cons_self)⟩
        dsimp only [lookupL, listGet?]; exact castListTy_self_proof regSig J
      · rcases hIn with hp | ⟨idx, hidx, J₀, hL₀, hJ₀⟩
        · rcases List.mem_cons.1 hp with h' | h'
          · exact absurd h'.symm heq
          · exact Or.inl h'
        · refine Or.inr ⟨idx + 1, ?_, J₀, hL₀, hJ₀⟩
          dsimp only [findLabelIdx]
          simp [beq_false_of_ne heq, hidx]

private theorem denote_lowerJumpTo_of_mem {rs : List Ty} {Γ : Env} {Q : Post rs} {X : XPost}
    (gs : List GroupTree) (Js : Tup Cont (gs.map fun _ => regSig))
    (pcs : List (BitVec 64)) (ls : List ((ts : List Ty) × Cont ts)) (Pred : CodeSpec)
    (r : Regs) (m : Mem 64) (p : BitVec 64)
    (hMem : TupMemPred gs Js Pred) (hpIn : p ∈ gs.map GroupTree.entryPc) (hP : Pred p ⟨r, m⟩) :
    wp Γ Q X (denote Val Cont (lowerJumpTo (pushLabelPcs (gs.map GroupTree.entryPc) pcs) p
      ⟨.var 5, .var 4, .var 3, .var 2, .var 1, .var 0⟩) (pushTup r.toRegsV.toTup [])
      (pushTup Js ls)) m := by
  obtain ⟨j, J, hj, hL, hJ⟩ := lookupL_pushTup_entry gs Js pcs ls Pred r m p hMem (fun _ => hP)
    (Or.inl hpIn)
  dsimp only [lowerJumpTo]
  rw [hj]
  rcases r with ⟨sp, rp, rv, r1, r2, r3⟩
  have hArgs : denoteArgs (pushTup (as := regSig) (sp, rp, rv, r1, r2, r3, ()) [])
      (⟨.var 5, .var 4, .var 3, .var 2, .var 1, .var 0⟩ : RegsExpr K).toTup =
      some ((.var sp, .var rp, .var rv, .var r1, .var r2, .var r3, ()) : Tup (Arg Val) regSig) := by
    dsimp only [pushTup, RegsExpr.toTup, denoteArgs, denoteArg, lookupV, listGet?, castTy]
    simp only [↓reduceDIte]
  dsimp only [denote, Regs.toRegsV, RegsV.toTup]
  rw [hL, hArgs]
  exact hJ

private theorem lfp_q_ls_mono {cm : CodeMap} {rw : RegionWitness} {Γ : Env}
    {Q₁ Q₂ : Post rw.abi.retSig} {X : XPost} (hQ : ∀ vs m, Q₁ vs m → Q₂ vs m)
    {pcs : List (BitVec 64)} (gs : List GroupTree)
    {ls₁ ls₂ : List ((ts : List Ty) × Cont ts)} {D : Ctx Cont Cont}
    (hD : MonoD D) (hRel : CtxRel D ls₁ ls₂) :
    ∀ {ts} (i : Member ts (gs.map fun _ => regSig)) xs m,
      (lfp Γ Q₁ X (fun Jv => denoteB Val Cont (liftGroupNodes cm rw pcs gs) []
        (pushTup Jv ls₁))).get i xs m →
      (lfp Γ Q₂ X (fun Jv => denoteB Val Cont (liftGroupNodes cm rw pcs gs) []
        (pushTup Jv ls₂))).get i xs m := by
  intro ts i xs m h
  rw [lfp_get] at h ⊢
  intro Js hcl
  apply h Js
  rw [closed_iff] at hcl ⊢
  intro ts' j ys m' hb
  apply hcl j ys m'
  have hwf := (denoteB_wf (liftGroupNodes cm rw pcs gs) (G := ([] : Ctx Val Val))
    (@CtxRel.nil Ty Val Val []) (ctxRel_pushTup Js Js hRel)).get j ys ys
  exact wp_mono hQ (fun _ _ _ _ h => h) _ m'
    (wp_label_mono hwf (DiagV.append DiagV.nil ys)
      ((mono_zip_self Js).append hD) m' hb)

mutual
private theorem canonNodePred_mono {cm : CodeMap} {rw : RegionWitness} {Γ : Env}
    {Q₁ Q₂ : Post rw.abi.retSig} {X : XPost} (hQ : ∀ vs m, Q₁ vs m → Q₂ vs m)
    {pcs' : List (BitVec 64)} {ls₁ ls₂ : List ((ts : List Ty) × Cont ts)}
    {D : Ctx Cont Cont} (hD : MonoD D) (hRel : CtxRel D ls₁ ls₂) :
    ∀ (g : GroupTree) {J₁ J₂ : Cont regSig},
      (∀ xs m, J₁ xs m → J₂ xs m) →
      ∀ pc st, canonNodePred cm rw Γ Q₁ X pcs' ls₁ g J₁ pc st →
        canonNodePred cm rw Γ Q₂ X pcs' ls₂ g J₂ pc st
  | .leaf _, _, _, hJ, _, _, h => fun heq => hJ _ _ (h heq)
  | .loop _ nodes, _, _, hJ, _, _, ⟨hHd, hSub⟩ =>
      let pcs'' := pushLabelPcs (nodes.map GroupTree.entryPc) pcs'
      have hJs : ∀ {ts} (i : Member ts (nodes.map fun _ => regSig)) xs m,
          (lfp Γ Q₁ X (fun Jv => denoteB Val Cont (liftGroupNodes cm rw pcs'' nodes) []
            (pushTup Jv ls₁))).get i xs m →
          (lfp Γ Q₂ X (fun Jv => denoteB Val Cont (liftGroupNodes cm rw pcs'' nodes) []
            (pushTup Jv ls₂))).get i xs m := lfp_q_ls_mono hQ nodes hD hRel
      ⟨fun heq => hJ _ _ (hHd heq),
       canonTupPred_mono hQ ((mono_zip _ _ hJs).append hD)
         (ctxRel_pushTup _ _ hRel) nodes hJs _ _ hSub⟩

private theorem canonTupPred_mono {cm : CodeMap} {rw : RegionWitness} {Γ : Env}
    {Q₁ Q₂ : Post rw.abi.retSig} {X : XPost} (hQ : ∀ vs m, Q₁ vs m → Q₂ vs m)
    {pcs' : List (BitVec 64)} {ls₁ ls₂ : List ((ts : List Ty) × Cont ts)}
    {D : Ctx Cont Cont} (hD : MonoD D) (hRel : CtxRel D ls₁ ls₂) :
    ∀ (gs : List GroupTree) {Js₁ Js₂ : Tup Cont (gs.map fun _ => regSig)},
      (∀ {ts} (i : Member ts (gs.map fun _ => regSig)) xs m, Js₁.get i xs m → Js₂.get i xs m) →
      ∀ pc st, canonTupPred cm rw Γ Q₁ X pcs' ls₁ gs Js₁ pc st →
        canonTupPred cm rw Γ Q₂ X pcs' ls₂ gs Js₂ pc st
  | [], (), (), _, _, _, _ => trivial
  | g :: gs, (_, _), (_, _), hJs, _, _, ⟨hg, hgs⟩ =>
      ⟨canonNodePred_mono hQ hD hRel g (hJs .here) _ _ hg,
       canonTupPred_mono hQ hD hRel gs (fun i => hJs (.there i)) _ _ hgs⟩
end

private theorem canonNodesPred_mono {cm : CodeMap} {rw : RegionWitness} {Γ : Env}
    {Q₁ Q₂ : Post rw.abi.retSig} {X : XPost} (hQ : ∀ vs m, Q₁ vs m → Q₂ vs m)
    {pcsOuter : List (BitVec 64)} {ls₁ ls₂ : List ((ts : List Ty) × Cont ts)}
    {D : Ctx Cont Cont} (hD : MonoD D) (hRel : CtxRel D ls₁ ls₂)
    (gs : List GroupTree) {pc st}
    (h : canonNodesPred cm rw Γ Q₁ X gs pcsOuter ls₁ pc st) :
    canonNodesPred cm rw Γ Q₂ X gs pcsOuter ls₂ pc st := by
  dsimp only [canonNodesPred] at h ⊢
  let pcs' := pushLabelPcs (gs.map GroupTree.entryPc) pcsOuter
  have hJs : ∀ {ts} (i : Member ts (gs.map fun _ => regSig)) xs m,
      (lfp Γ Q₁ X (fun Jv => denoteB Val Cont (liftGroupNodes cm rw pcs' gs) []
        (pushTup Jv ls₁))).get i xs m →
      (lfp Γ Q₂ X (fun Jv => denoteB Val Cont (liftGroupNodes cm rw pcs' gs) []
        (pushTup Jv ls₂))).get i xs m := lfp_q_ls_mono hQ gs hD hRel
  exact canonTupPred_mono hQ ((mono_zip _ _ hJs).append hD)
    (ctxRel_pushTup _ _ hRel) gs hJs pc st h

private def regionBailPost (cm : CodeMap) (wit : CfgWitness) (Ψ_cold : CodeSpec)
    (H : HaltPost) (P : CodeSpec) : RegionAbi → CodeSpec
  | .retEnvelope => PsiHyb cm wit Ψ_cold H
  | .contified _ => fun pc' s' => P pc' s' ∧ PsiHyb cm wit Ψ_cold H pc' s'

private def regionQ (cm : CodeMap) (wit : CfgWitness) (Ψ_cold : CodeSpec) (H : HaltPost)
    (P : CodeSpec) (rw : RegionWitness) (rp₀ : BitVec 64) : Post rw.abi.retSig :=
  regionRetPost rw.abi (regionBailPost cm wit Ψ_cold H P rw.abi) rp₀

private theorem regionQ_mono_aux (cm : CodeMap) (wit : CfgWitness) (Ψ_cold : CodeSpec)
    (H : HaltPost) {P₁ P₂ : CodeSpec} (hP : ∀ pc st, P₁ pc st → P₂ pc st) (rp₀ : BitVec 64)
    (m : Mem 64) :
    ∀ (abi : RegionAbi) (vs : Tup Val abi.retSig),
      regionRetPost abi (regionBailPost cm wit Ψ_cold H P₁ abi) rp₀ vs m →
      regionRetPost abi (regionBailPost cm wit Ψ_cold H P₂ abi) rp₀ vs m
  | .retEnvelope, _, h => h
  | .contified dualRet, _, h => by
      cases dualRet <;> exact ⟨hP _ _ h.1, h.2⟩

private theorem regionQ_mono (cm : CodeMap) (wit : CfgWitness) (Ψ_cold : CodeSpec) (H : HaltPost)
    {P₁ P₂ : CodeSpec} (hP : ∀ pc st, P₁ pc st → P₂ pc st) (rw : RegionWitness) (rp₀ : BitVec 64) :
    ∀ vs m, regionQ cm wit Ψ_cold H P₁ rw rp₀ vs m → regionQ cm wit Ψ_cold H P₂ rw rp₀ vs m :=
  fun vs m h => regionQ_mono_aux cm wit Ψ_cold H hP rp₀ m rw.abi vs h

private def witStepTrans (cm : CodeMap) (wit : CfgWitness) (Ψ_cold : CodeSpec) (H : HaltPost)
    (X : XPost) (P : CodeSpec) : CodeSpec :=
  fun pc st =>
    ∀ (pre : List RegionWitness) (rw : RegionWitness) (post : List RegionWitness),
      wit.regions = pre ++ rw :: post → pc ∈ rw.allPcs →
      canonNodesPred cm rw (witEnvAux cm (fun _ _ _ _ _ _ _ => False) pre)
        (regionQ cm wit Ψ_cold H P rw st.regs.rp) X rw.tree [] [] pc st

private theorem witStepTrans_mono (cm : CodeMap) (wit : CfgWitness) (Ψ_cold : CodeSpec)
    (H : HaltPost) (X : XPost) {P₁ P₂ : CodeSpec} (hP : ∀ pc st, P₁ pc st → P₂ pc st) :
    ∀ pc st, witStepTrans cm wit Ψ_cold H X P₁ pc st →
      witStepTrans cm wit Ψ_cold H X P₂ pc st := by
  intro pc st h pre rw post hEq hMem
  exact canonNodesPred_mono (regionQ_mono cm wit Ψ_cold H hP rw st.regs.rp)
    MonoD.nil .nil rw.tree (h pre rw post hEq hMem)

private def WitGfp (cm : CodeMap) (wit : CfgWitness) (Ψ_cold : CodeSpec) (H : HaltPost)
    (X : XPost) : CodeSpec :=
  fun pc st => ∃ P : CodeSpec,
    (∀ pc' st', P pc' st' → witStepTrans cm wit Ψ_cold H X P pc' st') ∧ P pc st

private theorem witGfp_post (cm : CodeMap) (wit : CfgWitness) (Ψ_cold : CodeSpec)
    (H : HaltPost) (X : XPost) {pc st} :
    WitGfp cm wit Ψ_cold H X pc st →
    witStepTrans cm wit Ψ_cold H X (WitGfp cm wit Ψ_cold H X) pc st := by
  rintro ⟨P, hP, hpc⟩
  exact witStepTrans_mono cm wit Ψ_cold H X (fun _ _ h => ⟨P, hP, h⟩) pc st (hP pc st hpc)

private theorem witGfp_pre (cm : CodeMap) (wit : CfgWitness) (Ψ_cold : CodeSpec)
    (H : HaltPost) (X : XPost) {pc st} :
    witStepTrans cm wit Ψ_cold H X (WitGfp cm wit Ψ_cold H X) pc st →
    WitGfp cm wit Ψ_cold H X pc st := by
  intro h
  refine ⟨fun pc' st' => WitGfp cm wit Ψ_cold H X pc' st' ∨
      witStepTrans cm wit Ψ_cold H X (WitGfp cm wit Ψ_cold H X) pc' st', ?_, Or.inr h⟩
  intro pc' st' hq
  apply witStepTrans_mono cm wit Ψ_cold H X (fun _ _ h' => Or.inl h')
  rcases hq with hq | hq
  · exact witGfp_post cm wit Ψ_cold H X hq
  · exact hq

private theorem witGfp_outside (cm : CodeMap) (wit : CfgWitness) (Ψ_cold : CodeSpec)
    (H : HaltPost) (X : XPost) {pc st}
    (hOut : ¬ (wit.regions.flatMap RegionWitness.allPcs).contains pc = true) :
    WitGfp cm wit Ψ_cold H X pc st := by
  apply witGfp_pre
  intro pre rw post hEq hMem
  have hIn : (wit.regions.flatMap RegionWitness.allPcs).contains pc = true := by
    rw [List.contains_iff_mem, List.mem_flatMap]
    exact ⟨rw, by rw [hEq]; simp, hMem⟩
  exact absurd hIn hOut

private theorem mem_allPcs_of_split {wit : CfgWitness} {pre : List RegionWitness}
    {rw : RegionWitness} {post : List RegionWitness}
    (hEq : wit.regions = pre ++ rw :: post) {pc : BitVec 64} (h : pc ∈ rw.allPcs) :
    (wit.regions.flatMap RegionWitness.allPcs).contains pc = true := by
  rw [List.contains_iff_mem, List.mem_flatMap]
  exact ⟨rw, by rw [hEq]; simp, h⟩

private theorem regionAllPcs_mem_of_tree {rw : RegionWitness} {g : GroupTree}
    (hg : g ∈ rw.tree) {pc : BitVec 64} (hpc : pc ∈ g.allPcs) : pc ∈ rw.allPcs :=
  List.mem_flatMap.2 ⟨g, hg, hpc⟩

private theorem canonNodesPred_of_outside_all {cm : CodeMap} {rw : RegionWitness} {Γ : Env}
    {Q : Post rw.abi.retSig} {X : XPost} {callees : List CalleeMeta} {pc : BitVec 64} {st : State} :
    ∀ (gs : List GroupTree) (pcsOuter : List (BitVec 64))
      (lsOuter : List ((ts : List Ty) × Cont ts)),
      checkGroupNodes cm rw callees (pushLabelPcs (gs.map GroupTree.entryPc) pcsOuter) gs = true →
      pc ∉ gs.flatMap GroupTree.allPcs →
      canonNodesPred cm rw Γ Q X gs pcsOuter lsOuter pc st
  | gs, pcsOuter, lsOuter, hchk, hNot => by
      dsimp only [canonNodesPred]
      apply canonTupPred_of_forall
      intro gsPre g gsPost heq
      have hgMem : g ∈ gs := by rw [heq]; simp
      have hgChk := checkGroupNodes_forall cm rw callees _ gs hchk g hgMem
      have hgNot : pc ∉ g.allPcs := fun hp => hNot (List.mem_flatMap.2 ⟨g, hgMem, hp⟩)
      have hEntMem := checkGroupNode_entryPc_mem cm rw callees _ g hgChk
      cases g with
      | leaf pc₁ =>
          intro hEq
          rw [hEq] at hgNot
          exact absurd hEntMem hgNot
      | loop header nodes =>
          dsimp only [canonNodePred]
          refine ⟨fun hEq => absurd (hEq ▸ hEntMem) hgNot, ?_⟩
          dsimp only [checkGroupNode] at hgChk; simp only [Bool.and_eq_true] at hgChk
          have hLt : treeListSize nodes < treeListSize gs := by
            have := treeListSize_mem (.loop header nodes) gs hgMem
            simp only [treeSize] at this; omega
          exact canonNodesPred_of_outside_all nodes _ _ hgChk.2
            (by simpa [GroupTree.allPcs] using hgNot)
termination_by gs _ _ => treeListSize gs
decreasing_by exact hLt

private theorem regionSpec_from_canonNodes {cm : CodeMap} {rw : RegionWitness} {Γ : Env}
    {Q : Post rw.abi.retSig} {X : XPost} {callees : List CalleeMeta}
    (hChk : checkGroupNodes cm rw callees (pushLabelPcs (rw.tree.map GroupTree.entryPc) [])
      rw.tree = true)
    (hEnt : rw.entryPc ∈ rw.tree.map GroupTree.entryPc)
    (r₀ : Regs) (m : Mem 64)
    (hCan : canonNodesPred cm rw Γ Q X rw.tree [] [] rw.entryPc ⟨r₀, m⟩) :
    Func.spec Γ (liftRegion cm rw).body r₀.toRegsV.toTup m Q X := by
  dsimp only [Func.spec, Func.wp, liftRegion, denoteFunc, liftRegionTFlat, denote]
  have hPref : ∀ Jv : Tup Cont (rw.tree.map fun _ => regSig), denoteB Val Cont
      (liftGroupNodes cm rw (pushLabelPcs (rw.tree.map GroupTree.entryPc) []) rw.tree)
      (pushTup r₀.toRegsV.toTup []) (pushTup Jv []) =
    denoteB Val Cont
      (liftGroupNodes cm rw (pushLabelPcs (rw.tree.map GroupTree.entryPc) []) rw.tree)
      [] (pushTup Jv []) := fun Jv =>
    denote_liftGroupNodes_prefix _ rw.tree hChk _ _
  simp only [hPref]
  have hWfB : ∀ J₁ J₂ : Tup Cont (rw.tree.map fun _ => regSig),
      WfB (diagCtxOfV (pushTup r₀.toRegsV.toTup [])) (Tup.zip J₁ J₂ ++ [])
        (denoteB Val Cont (liftGroupNodes cm rw
          (pushLabelPcs (rw.tree.map GroupTree.entryPc) []) rw.tree) [] (pushTup J₁ []))
        (denoteB Val Cont (liftGroupNodes cm rw
          (pushLabelPcs (rw.tree.map GroupTree.entryPc) []) rw.tree) [] (pushTup J₂ [])) :=
    fun J₁ J₂ => denoteB_wf _ CtxRel.nil (ctxRel_pushTup J₁ J₂ .nil)
  have hWfK : ∀ J₁ J₂ : Tup Cont (rw.tree.map fun _ => regSig),
      Wf (rs := rw.abi.retSig) (diagCtxOfV (pushTup r₀.toRegsV.toTup [])) (Tup.zip J₁ J₂ ++ [])
        (denote Val Cont (lowerJumpTo (rs := rw.abi.retSig)
          (pushLabelPcs (rw.tree.map GroupTree.entryPc) [])
          rw.entryPc ⟨.var 5, .var 4, .var 3, .var 2, .var 1, .var 0⟩)
          (pushTup r₀.toRegsV.toTup []) (pushTup J₁ []))
        (denote Val Cont (lowerJumpTo (rs := rw.abi.retSig)
          (pushLabelPcs (rw.tree.map GroupTree.entryPc) [])
          rw.entryPc ⟨.var 5, .var 4, .var 3, .var 2, .var 1, .var 0⟩)
          (pushTup r₀.toRegsV.toTup []) (pushTup J₂ [])) :=
    fun J₁ J₂ => denote_wf _ (ctxRel_diagV (pushTup r₀.toRegsV.toTup []))
      (ctxRel_pushTup J₁ J₂ .nil)
  rw [wp_group_iff (diagV_diagCtx (pushTup r₀.toRegsV.toTup [])) (monoD_diagL []) hWfB hWfK m]
  have hMem : TupMemPred rw.tree
      (lfp Γ Q X (fun Jv =>
        denoteB Val Cont (liftGroupNodes cm rw (pushLabelPcs (rw.tree.map GroupTree.entryPc) [])
          rw.tree) [] (pushTup Jv [])))
      (canonNodesPred cm rw Γ Q X rw.tree [] []) :=
    canonTupPred_tupMemPred rw.tree _ fun g _ r m' h => h
  exact denote_lowerJumpTo_of_mem rw.tree _ [] [] _ r₀ m rw.entryPc hMem hEnt hCan

private theorem canonNodes_step_aux (cm : CodeMap) (wit : CfgWitness) (Ψ_cold : CodeSpec)
    (H : HaltPost) (X : XPost) (hH : ∀ c m', H c m' → X haltSym [i64] (c, ()) m')
    (hChk : wit.check cm = true) {pc₀ : BitVec 64} {st₀ : State} {b : BlockFlat}
    (hlu : cm.lookupAddr pc₀ = some b)
    (hbp : b.wp cm.symEnv (fun pc' s' =>
      if (wit.regions.flatMap RegionWitness.allPcs).contains pc' then
        (PsiReg cm wit Ψ_cold H pc' s' ∧ WitGfp cm wit Ψ_cold H X pc' s') ∧ Ψ_cold pc' s'
      else Ψ_cold pc' s') H (pushRegsV st₀.regs.toRegsV) st₀.mem)
    {pre : List RegionWitness} {rw : RegionWitness} {post : List RegionWitness}
    (hSplit : wit.regions = pre ++ rw :: post)
    (gs : List GroupTree) (pcsOuter : List (BitVec 64))
    (lsOuter : List ((ts : List Ty) × Cont ts)) :
    checkGroupNodes cm rw (calleesFold [] pre)
      (pushLabelPcs (gs.map GroupTree.entryPc) pcsOuter) gs = true →
    LsMatch pcsOuter lsOuter
      (fun pc' s' => (rw.abi.isContified = true → s'.regs.rp = st₀.regs.rp) ∧
        WitGfp cm wit Ψ_cold H X pc' s') →
    (∀ pc' s', (rw.abi.isContified = true → s'.regs.rp = st₀.regs.rp) →
      WitGfp cm wit Ψ_cold H X pc' s' →
      canonNodesPred cm rw (witEnvAux cm (fun _ _ _ _ _ _ _ => False) pre)
        (regionQ cm wit Ψ_cold H (WitGfp cm wit Ψ_cold H X) rw st₀.regs.rp) X
        gs pcsOuter lsOuter pc' s') →
    pc₀ ∈ gs.flatMap GroupTree.allPcs →
    canonNodesPred cm rw (witEnvAux cm (fun _ _ _ _ _ _ _ => False) pre)
      (regionQ cm wit Ψ_cold H (WitGfp cm wit Ψ_cold H X) rw st₀.regs.rp) X
      gs pcsOuter lsOuter pc₀ st₀ := by
  intro hgsChk hlsOuter hEx _
  simp only [canonNodesPred]
  let pcs' := pushLabelPcs (gs.map GroupTree.entryPc) pcsOuter
  let callees := calleesFold [] pre
  let Γ := witEnvAux cm (fun _ _ _ _ _ _ _ => False) pre
  let Q := regionQ cm wit Ψ_cold H (WitGfp cm wit Ψ_cold H X) rw st₀.regs.rp
  let bodies := fun (Jv : Tup Cont (gs.map fun _ => regSig)) =>
    denoteB Val Cont (liftGroupNodes cm rw pcs' gs) [] (pushTup Jv lsOuter)
  let Js := lfp Γ Q X bodies
  let Pred : CodeSpec := fun pc' s' =>
    (rw.abi.isContified = true → s'.regs.rp = st₀.regs.rp) ∧
    WitGfp cm wit Ψ_cold H X pc' s'
  have hMemTup : TupMemPred gs Js Pred :=
    canonTupPred_tupMemPred gs Js fun g _ r m ⟨hRp, hPg⟩ => hEx g.entryPc ⟨r, m⟩ hRp hPg
  have hls' : LsMatch pcs' (pushTup Js lsOuter) Pred :=
    lsMatch_pushTup_group gs Js pcsOuter lsOuter Pred hMemTup hlsOuter
  have hwfB : ∀ J₁ J₂, WfB [] (Tup.zip J₁ J₂ ++ diagCtxOfL lsOuter)
      (bodies J₁) (bodies J₂) := fun J₁ J₂ =>
    denoteB_wf (liftGroupNodes cm rw pcs' gs) .nil (ctxRel_pushTup J₁ J₂ (ctxRel_diagL lsOuter))
  have hClosed := lfp_closed DiagV.nil (monoD_diagL lsOuter) hwfB
    (Γ := Γ) (Q := Q) (X := X)
  have hStepPred : ∀ pc' s', (findLabelIdx pcs' pc').isSome = true →
      (rw.abi.isContified = true → s'.regs.rp = st₀.regs.rp) →
      (if (wit.regions.flatMap RegionWitness.allPcs).contains pc' then
        (PsiReg cm wit Ψ_cold H pc' s' ∧ WitGfp cm wit Ψ_cold H X pc' s') ∧ Ψ_cold pc' s'
       else Ψ_cold pc' s') →
      Pred pc' s' := by
    intro pc' s' _ hRp hS
    refine ⟨hRp, ?_⟩
    by_cases hc : (wit.regions.flatMap RegionWitness.allPcs).contains pc' = true
    · simp only [hc, ↓reduceIte] at hS; exact hS.1.2
    · exact witGfp_outside cm wit Ψ_cold H X hc
  have hStepBail : ∀ pc' s',
      (if (wit.regions.flatMap RegionWitness.allPcs).contains pc' then
        (PsiReg cm wit Ψ_cold H pc' s' ∧ WitGfp cm wit Ψ_cold H X pc' s') ∧ Ψ_cold pc' s'
       else Ψ_cold pc' s') →
      regionBailPost cm wit Ψ_cold H (WitGfp cm wit Ψ_cold H X) rw.abi pc' s' := by
    intro pc' s' hS
    have hHyb : PsiHyb cm wit Ψ_cold H pc' s' := by
      dsimp only [PsiHyb]
      by_cases hc : (wit.regions.flatMap RegionWitness.allPcs).contains pc' = true
      · simp only [hc, ↓reduceIte] at hS ⊢; exact ⟨hS.1.1, hS.2⟩
      · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hS ⊢; exact hS
    have hWit : WitGfp cm wit Ψ_cold H X pc' s' := by
      by_cases hc : (wit.regions.flatMap RegionWitness.allPcs).contains pc' = true
      · simp only [hc, ↓reduceIte] at hS; exact hS.1.2
      · exact witGfp_outside cm wit Ψ_cold H X hc
    cases rw.abi with
    | retEnvelope => exact hHyb
    | contified _ => exact ⟨hWit, hHyb⟩
  have hStepCall : ∀ callee calleePc dualRet (nxtR : Regs) m' retPc altRetPc?,
      rw.abi.isContified = false →
      callees.any (fun c => (c.name == callee) && (c.entryPc == calleePc) &&
        (c.dualRet == dualRet)) = true →
      cm.addrOf? callee = some calleePc →
      nxtR.rp = retPc →
      (if dualRet then altRetPc? = some (retPc + 8#64) else altRetPc?.isNone) →
      (findLabelIdx pcs' retPc).isSome = true →
      (if dualRet then (findLabelIdx pcs' (retPc + 8#64)).isSome = true else True) →
      (if (wit.regions.flatMap RegionWitness.allPcs).contains calleePc then
        (PsiReg cm wit Ψ_cold H calleePc ⟨nxtR, m'⟩ ∧
          WitGfp cm wit Ψ_cold H X calleePc ⟨nxtR, m'⟩) ∧ Ψ_cold calleePc ⟨nxtR, m'⟩
       else Ψ_cold calleePc ⟨nxtR, m'⟩) →
      ∃ P E, Γ callee regSig (RegionAbi.contified dualRet).retSig
          nxtR.toRegsV.toTup m' P E ∧
        (∀ r m'', P r m'' → retContPost dualRet Pred retPc r m'') ∧
        (∀ g cs xs m'', E g cs xs m'' → X g cs xs m'') := by
    intro callee calleePc dualRet nxtR m' retPc _ hAbiF hcal _ hrp _ _ _ hS
    rw [List.any_eq_true] at hcal
    obtain ⟨c, hcMem, hcEq⟩ := hcal
    simp only [Bool.and_eq_true, beq_iff_eq] at hcEq
    rcases hcEq with ⟨⟨rfl, rfl⟩, rfl⟩
    rcases mem_calleesFold pre [] c hcMem with hEmpty | ⟨rw_c, hRwcMem, hToMeta⟩
    · cases hEmpty
    rcases List.mem_iff_append.1 hRwcMem with ⟨pre_c, post_c, hPreEq⟩
    cases hAbi_c : rw_c.abi with
    | retEnvelope => simp [RegionWitness.toCalleeMeta?, hAbi_c] at hToMeta
    | contified dualRet =>
        simp only [RegionWitness.toCalleeMeta?, hAbi_c, Option.some.injEq] at hToMeta
        subst hToMeta
        have hAuxAll : CfgWitness.checkAux cm [] wit.regions = true := by
          dsimp only [CfgWitness.check] at hChk
          simp only [Bool.and_eq_true] at hChk; exact hChk.2
        have hSplit_c : wit.regions = pre_c ++ rw_c :: (post_c ++ rw :: post) := by
          rw [hSplit, hPreEq, List.append_assoc]; rfl
        have hAux_c := checkAux_append cm pre_c (rw_c :: (post_c ++ rw :: post)) []
          (hSplit_c ▸ hAuxAll)
        dsimp only [CfgWitness.checkAux] at hAux_c
        simp only [Bool.and_eq_true] at hAux_c
        have hRwcChk := hAux_c.1
        dsimp only [RegionWitness.check] at hRwcChk
        simp only [Bool.and_eq_true] at hRwcChk
        have hEntMap : rw_c.entryPc ∈ rw_c.tree.map GroupTree.entryPc := by
          simpa using hRwcChk.1.1.1.1.2
        have hEntAll : rw_c.entryPc ∈ rw_c.allPcs := by
          rw [List.mem_map] at hEntMap
          rcases hEntMap with ⟨g_c, hg_cMem, hg_cEq⟩
          have hm := checkGroupNode_entryPc_mem cm rw_c (calleesFold [] pre_c) _ g_c
            (checkGroupNodes_forall cm rw_c _ _ rw_c.tree hRwcChk.1.1.2 g_c hg_cMem)
          rw [hg_cEq] at hm
          exact regionAllPcs_mem_of_tree hg_cMem hm
        have hcInAll : (wit.regions.flatMap RegionWitness.allPcs).contains rw_c.entryPc =
            true := mem_allPcs_of_split hSplit_c hEntAll
        simp only [hcInAll, ↓reduceIte] at hS
        have hPg_c := witGfp_post cm wit Ψ_cold H X hS.1.2 pre_c rw_c (post_c ++ rw :: post)
          hSplit_c hEntAll
        have hSpec_c := regionSpec_from_canonNodes hRwcChk.1.1.2 hEntMap nxtR m' hPg_c
        have hRetEq : rw_c.abi.retSig = (RegionAbi.contified dualRet).retSig :=
          congrArg RegionAbi.retSig hAbi_c
        let Q₀ := regionQ cm wit Ψ_cold H (WitGfp cm wit Ψ_cold H X) rw_c nxtR.rp
        refine ⟨hRetEq ▸ Q₀, X, ?_, ?_, fun _ _ _ _ h => h⟩
        · dsimp only [Γ]
          rw [hPreEq]
          have hMemW := witEnvAux_mem_prefix cm (fun _ _ _ _ _ _ _ => False) pre_c rw_c
            post_c dualRet hAbi_c hSpec_c
          have hCast : ∀ {sig'} (he : rw_c.abi.retSig = sig') (Q' : Post rw_c.abi.retSig),
              witEnvAux cm (fun _ _ _ _ _ _ _ => False) (pre_c ++ rw_c :: post_c)
                rw_c.name regSig rw_c.abi.retSig nxtR.toRegsV.toTup m' Q' X →
              witEnvAux cm (fun _ _ _ _ _ _ _ => False) (pre_c ++ rw_c :: post_c)
                rw_c.name regSig sig' nxtR.toRegsV.toTup m' (he ▸ Q') X := by
            rintro _ rfl Q' h; exact h
          exact hCast hRetEq Q₀ hMemW
        · intro r m'' hr
          have hCast2 : ∀ {sig'} (he : rw_c.abi.retSig = sig') (Q' : Post rw_c.abi.retSig)
              (r' : Tup Val sig'), (he ▸ Q') r' m'' → Q' (he.symm ▸ r') m'' := by
            rintro _ rfl Q' r' h; exact h
          have hPostCast : ∀ (abi : RegionAbi) (hEq : abi = .contified dualRet)
              (r' : Tup Val abi.retSig),
              regionRetPost abi (regionBailPost cm wit Ψ_cold H
                (WitGfp cm wit Ψ_cold H X) abi) nxtR.rp r' m'' →
              retContPost dualRet Pred retPc (congrArg RegionAbi.retSig hEq ▸ r') m'' := by
            rintro _ rfl r' h'
            cases dualRet <;> dsimp only [regionRetPost, regionBailPost, retContPost] at h' ⊢
            · rw [hrp] at h'; exact ⟨fun hCont => by simp [hAbiF] at hCont, h'.1⟩
            · rcases r' with ⟨isAlt, sp, rp, rv, r1, r2, r3, ⟨⟩⟩
              dsimp only at h' ⊢; rw [hrp] at h'
              exact ⟨fun hCont => by simp [hAbiF] at hCont, h'.1⟩
          have hSymInv : ∀ {sig'} (he : rw_c.abi.retSig = sig') (x : Tup Val sig'),
              (he ▸ (he.symm ▸ x)) = x := by rintro _ rfl x; rfl
          have res := hPostCast rw_c.abi hAbi_c (hRetEq.symm ▸ r) (hCast2 hRetEq Q₀ r hr)
          rwa [hSymInv hRetEq r] at res
  apply canonTupPred_of_forall
  intro gsPre g gsPost heq
  have hgMem : g ∈ gs := by rw [heq]; simp
  have hgChk := checkGroupNodes_forall cm rw callees pcs' gs hgsChk g hgMem
  cases g with
  | leaf pc₁ =>
      intro hpcEq
      subst hpcEq
      apply (closed_iff Γ Q X _ Js).1 hClosed (heq ▸ memberOfPrefix gsPre (.leaf pc₀) gsPost)
        st₀.regs.toRegsV.toTup st₀.mem
      have hNodeEq : (bodies Js).get (heq ▸ memberOfPrefix gsPre (.leaf pc₀) gsPost)
          st₀.regs.toRegsV.toTup =
        denote Val Cont (liftGroupNode cm rw pcs' (.leaf pc₀))
          (pushRegsV st₀.regs.toRegsV) (pushTup Js lsOuter) := by
        subst heq; exact denoteB_get_memberOfPrefix cm rw pcs' [] (pushTup Js lsOuter) _ _ _ _
      rw [hNodeEq]
      dsimp only [checkGroupNode, checkBlockLeaves] at hgChk
      dsimp only [liftGroupNode]
      rw [hlu] at hgChk ⊢
      simp only [Bool.and_eq_true] at hgChk
      cases hsym : symEvalBlock cm b [] SymState.init with
      | none => rw [hsym] at hgChk; cases hgChk.2
      | some leaves =>
          rw [hsym] at hgChk
          have hleaves : ∀ lf ∈ leaves, ∃ ew, rw.findEdge pc₀ lf.path = some ew ∧
              checkEdgeLeaf cm rw.abi callees pcs' lf ew.kind = true := by
            intro lf hm
            have ha := List.all_eq_true.1 hgChk.2 lf hm
            cases hf : rw.findEdge pc₀ lf.path with
            | none => rw [hf] at ha; cases ha
            | some ew => rw [hf] at ha; exact ⟨ew, rfl, ha⟩
          exact liftBlock_wp_init hls' pc₀ st₀.regs hH hStepPred hStepBail hStepCall b leaves
            st₀.mem hgChk.1.1 hgChk.1.2 hsym hleaves hbp
  | loop header nodes =>
      simp only [canonNodePred]
      dsimp only [checkGroupNode] at hgChk; simp only [Bool.and_eq_true] at hgChk
      by_cases hin : pc₀ ∈ nodes.flatMap GroupTree.allPcs
      · have hExSub : ∀ pc' s', (rw.abi.isContified = true → s'.regs.rp = st₀.regs.rp) →
            WitGfp cm wit Ψ_cold H X pc' s' →
            canonNodesPred cm rw Γ Q X nodes pcs' (pushTup Js lsOuter) pc' s' :=
          fun pc' s' hRp hPg => by
            have hG := hEx pc' s' hRp hPg
            dsimp only [canonNodesPred] at hG
            exact (canonTupPred_get_eq gsPre (.loop header nodes) gsPost heq Js hG).2
        have hSub := canonNodes_step_aux cm wit Ψ_cold H X hH hChk hlu hbp hSplit
          nodes pcs' (pushTup Js lsOuter) hgChk.2 hls' hExSub hin
        refine ⟨fun hEq => ?_, hSub⟩
        subst hEq
        apply (closed_iff Γ Q X _ Js).1 hClosed
          (heq ▸ memberOfPrefix gsPre (.loop pc₀ nodes) gsPost)
          st₀.regs.toRegsV.toTup st₀.mem
        have hNodeEq : (bodies Js).get
            (heq ▸ memberOfPrefix gsPre (.loop pc₀ nodes) gsPost) st₀.regs.toRegsV.toTup =
          denote Val Cont (liftGroupNode cm rw pcs' (.loop pc₀ nodes))
            (pushRegsV st₀.regs.toRegsV) (pushTup Js lsOuter) := by
          subst heq; exact denoteB_get_memberOfPrefix cm rw pcs' [] (pushTup Js lsOuter) _ _ _ _
        rw [hNodeEq]
        dsimp only [liftGroupNode, denote, pushRegsV]
        have hSubPref : ∀ Jv : Tup Cont (nodes.map fun _ => regSig),
            denoteB Val Cont (liftGroupNodes cm rw
              (pushLabelPcs (nodes.map GroupTree.entryPc) pcs') nodes)
            (pushTup st₀.regs.toRegsV.toTup []) (pushTup Jv (pushTup Js lsOuter)) =
          denoteB Val Cont (liftGroupNodes cm rw
              (pushLabelPcs (nodes.map GroupTree.entryPc) pcs') nodes) []
            (pushTup Jv (pushTup Js lsOuter)) := fun Jv =>
          denote_liftGroupNodes_prefix _ nodes hgChk.2 _ _
        simp only [hSubPref]
        have hWfSubB : ∀ J₁ J₂ : Tup Cont (nodes.map fun _ => regSig),
            WfB (diagCtxOfV (pushTup st₀.regs.toRegsV.toTup []))
              (Tup.zip J₁ J₂ ++ diagCtxOfL (pushTup Js lsOuter))
              (denoteB Val Cont (liftGroupNodes cm rw
                (pushLabelPcs (nodes.map GroupTree.entryPc) pcs') nodes) []
                (pushTup J₁ (pushTup Js lsOuter)))
              (denoteB Val Cont (liftGroupNodes cm rw
                (pushLabelPcs (nodes.map GroupTree.entryPc) pcs') nodes) []
                (pushTup J₂ (pushTup Js lsOuter))) :=
          fun J₁ J₂ => denoteB_wf _ CtxRel.nil (ctxRel_pushTup J₁ J₂ (ctxRel_diagL _))
        have hWfSubK : ∀ J₁ J₂ : Tup Cont (nodes.map fun _ => regSig),
            Wf (rs := rw.abi.retSig) (diagCtxOfV (pushTup st₀.regs.toRegsV.toTup []))
              (Tup.zip J₁ J₂ ++ diagCtxOfL (pushTup Js lsOuter))
              (denote Val Cont (lowerJumpTo (rs := rw.abi.retSig)
                (pushLabelPcs (nodes.map GroupTree.entryPc) pcs')
                pc₀ ⟨.var 5, .var 4, .var 3, .var 2, .var 1, .var 0⟩)
                (pushTup st₀.regs.toRegsV.toTup []) (pushTup J₁ (pushTup Js lsOuter)))
              (denote Val Cont (lowerJumpTo (rs := rw.abi.retSig)
                (pushLabelPcs (nodes.map GroupTree.entryPc) pcs')
                pc₀ ⟨.var 5, .var 4, .var 3, .var 2, .var 1, .var 0⟩)
                (pushTup st₀.regs.toRegsV.toTup []) (pushTup J₂ (pushTup Js lsOuter))) :=
          fun J₁ J₂ => denote_wf _ (ctxRel_diagV (pushTup st₀.regs.toRegsV.toTup []))
            (ctxRel_pushTup J₁ J₂ (ctxRel_diagL _))
        rw [wp_group_iff (diagV_diagCtx (pushTup st₀.regs.toRegsV.toTup []))
          (monoD_diagL (pushTup Js lsOuter)) hWfSubB hWfSubK st₀.mem]
        have hMemSub : TupMemPred nodes
            (lfp Γ Q X (fun Jv => denoteB Val Cont (liftGroupNodes cm rw
              (pushLabelPcs (nodes.map GroupTree.entryPc) pcs') nodes) []
              (pushTup Jv (pushTup Js lsOuter))))
            (canonNodesPred cm rw Γ Q X nodes pcs' (pushTup Js lsOuter)) :=
          canonTupPred_tupMemPred nodes _ fun _ _ _ _ h => h
        have hEntIn : pc₀ ∈ nodes.map GroupTree.entryPc :=
          List.contains_iff_mem.1 hgChk.1.2
        exact denote_lowerJumpTo_of_mem nodes _ pcs' (pushTup Js lsOuter) _ st₀.regs st₀.mem
          pc₀ hMemSub hEntIn hSub
      · refine ⟨fun hEq => ?_, ?_⟩
        · have hEnt := checkGroupNode_entryPc_mem cm rw callees pcs' (.loop header nodes)
            (by dsimp only [checkGroupNode]; rw [hgChk.1.1, hgChk.1.2, hgChk.2]; rfl)
          rw [hEq] at hin
          exact absurd (by simpa [GroupTree.entryPc, GroupTree.allPcs] using hEnt) hin
        · exact canonNodesPred_of_outside_all nodes pcs' (pushTup Js lsOuter) hgChk.2 hin
termination_by treeListSize gs
decreasing_by
  have hLt := treeListSize_mem (.loop header nodes) gs hgMem
  simp only [treeSize] at hLt
  omega

private theorem regionQ_retEnvelope_rp (cm : CodeMap) (wit : CfgWitness) (Ψ_cold : CodeSpec)
    (H : HaltPost) (P : CodeSpec) (rw : RegionWitness) (hEnv : rw.abi = .retEnvelope)
    (rp₁ rp₂ : BitVec 64) :
    regionQ cm wit Ψ_cold H P rw rp₁ = regionQ cm wit Ψ_cold H P rw rp₂ := by
  have hgen : ∀ (abi : RegionAbi), abi = .retEnvelope → ∀ (vs : Tup Val abi.retSig) (m : Mem 64),
      regionRetPost abi (regionBailPost cm wit Ψ_cold H P abi) rp₁ vs m =
      regionRetPost abi (regionBailPost cm wit Ψ_cold H P abi) rp₂ vs m := by
    rintro _ rfl _ _; rfl
  funext vs m; exact hgen rw.abi hEnv vs m

private theorem psiReg_implies_witGfp (cm : CodeMap) (wit : CfgWitness) (Ψ_cold : CodeSpec)
    (H : HaltPost) (X : XPost) (hH : ∀ c m', H c m' → X haltSym [i64] (c, ()) m')
    (hChk : wit.check cm = true) :
    ∀ pc st, PsiReg cm wit Ψ_cold H pc st → WitGfp cm wit Ψ_cold H X pc st := by
  intro pc st hReg
  refine park_induction (P := fun p => WitGfp cm wit Ψ_cold H X p.1 p.2)
    (regionStep_mono cm wit Ψ_cold H) ?_ (pc, st) hReg
  rintro ⟨pc₀, st₀⟩ ⟨b, hlu, hbp⟩
  apply witGfp_pre
  intro pre rw post hSplit hpcMem
  have hAuxAll : CfgWitness.checkAux cm [] wit.regions = true := by
    dsimp only [CfgWitness.check] at hChk; simp only [Bool.and_eq_true] at hChk; exact hChk.2
  have hAux := checkAux_append cm pre (rw :: post) [] (by simpa [hSplit] using hAuxAll)
  dsimp only [CfgWitness.checkAux] at hAux; simp only [Bool.and_eq_true] at hAux
  have hRwChk := hAux.1
  dsimp only [RegionWitness.check] at hRwChk; simp only [Bool.and_eq_true] at hRwChk
  exact canonNodes_step_aux cm wit Ψ_cold H X hH hChk hlu hbp hSplit rw.tree [] []
    hRwChk.1.1.2 (lsMatch_nil _) (fun pc' s' hRp hPg => by
      by_cases hc : pc' ∈ rw.allPcs
      · have hPost := witGfp_post cm wit Ψ_cold H X hPg pre rw post hSplit hc
        cases hAbi : rw.abi with
        | retEnvelope =>
            rwa [regionQ_retEnvelope_rp cm wit Ψ_cold H (WitGfp cm wit Ψ_cold H X) rw hAbi
              st₀.regs.rp s'.regs.rp]
        | contified _ =>
            rw [hRp (by simp [RegionAbi.isContified, hAbi])] at hPost
            exact hPost
      · exact canonNodesPred_of_outside_all rw.tree [] [] hRwChk.1.1.2 hc) hpcMem

private theorem region_entryPc_mem_allPcs (cm : CodeMap) (wit : CfgWitness)
    (hChk : wit.check cm = true) {rw : RegionWitness} (hMem : rw ∈ wit.regions) :
    rw.entryPc ∈ rw.allPcs := by
  rcases List.mem_iff_append.1 hMem with ⟨pre, post, hSplit⟩
  dsimp only [CfgWitness.check] at hChk; simp only [Bool.and_eq_true] at hChk
  have hAux := checkAux_append cm pre (rw :: post) [] (by simpa [hSplit] using hChk.2)
  dsimp only [CfgWitness.checkAux] at hAux; simp only [Bool.and_eq_true] at hAux
  have hRwChk := hAux.1
  dsimp only [RegionWitness.check] at hRwChk; simp only [Bool.and_eq_true] at hRwChk
  have hEntMap : rw.entryPc ∈ rw.tree.map GroupTree.entryPc := by
    simpa using hRwChk.1.1.1.1.2
  rw [List.mem_map] at hEntMap
  rcases hEntMap with ⟨g, hgMem, hgEq⟩
  have hm := checkGroupNode_entryPc_mem cm rw _ _ g
    (checkGroupNodes_forall cm rw _ _ rw.tree hRwChk.1.1.2 g hgMem)
  rw [hgEq] at hm
  exact regionAllPcs_mem_of_tree hgMem hm

private theorem flatMap_nodup_disjoint_split (pre : List RegionWitness) (a : RegionWitness)
    (mid : List RegionWitness) (b : RegionWitness) (post : List RegionWitness)
    (hNd : listNodup ((pre ++ a :: mid ++ b :: post).flatMap RegionWitness.allPcs) = true) :
    ∀ pc, pc ∈ a.allPcs → pc ∉ b.allPcs := by
  intro pc ha hb
  have hApp : (pre ++ a :: mid ++ b :: post).flatMap RegionWitness.allPcs =
      (pre.flatMap RegionWitness.allPcs ++ a.allPcs) ++
      (mid.flatMap RegionWitness.allPcs ++ b.allPcs ++ post.flatMap RegionWitness.allPcs) := by
    simp [List.flatMap_append, List.append_assoc]
  rw [hApp] at hNd
  exact listNodup_false_append hNd pc (List.mem_append_right _ ha) pc
    (List.mem_append_left _ (List.mem_append_right _ hb)) rfl

private theorem regionAllPcs_disjoint_of_ne (cm : CodeMap) (wit : CfgWitness)
    (hChk : wit.check cm = true) {rw₁ rw₂ : RegionWitness}
    (h1 : rw₁ ∈ wit.regions) (h2 : rw₂ ∈ wit.regions) (hne : rw₁ ≠ rw₂) :
    ∀ pc, pc ∈ rw₁.allPcs → pc ∉ rw₂.allPcs := by
  dsimp only [CfgWitness.check] at hChk; simp only [Bool.and_eq_true] at hChk
  have hNd := hChk.1.2
  rcases List.mem_iff_append.1 h1 with ⟨pre₁, post₁, hEq₁⟩
  have h2' : rw₂ ∈ pre₁ ++ rw₁ :: post₁ := hEq₁ ▸ h2
  rcases List.mem_append.1 h2' with hInPre | hInTail
  · rcases List.mem_iff_append.1 hInPre with ⟨pre₂, mid₂, hPre₁Eq⟩
    have hFull : wit.regions = pre₂ ++ rw₂ :: mid₂ ++ rw₁ :: post₁ := by
      rw [hEq₁, hPre₁Eq, List.append_assoc]
    rw [hFull] at hNd
    intro pc h1p h2p
    exact flatMap_nodup_disjoint_split pre₂ rw₂ mid₂ rw₁ post₁ hNd pc h2p h1p
  · rcases List.mem_cons.1 hInTail with hSame | hInPost
    · exact absurd hSame.symm hne
    · rcases List.mem_iff_append.1 hInPost with ⟨mid₂, post₂, hPost₁Eq⟩
      have hFull : wit.regions = pre₁ ++ rw₁ :: mid₂ ++ rw₂ :: post₂ := by
        rw [hEq₁, hPost₁Eq]; simp [List.cons_append]
      rw [hFull] at hNd
      exact flatMap_nodup_disjoint_split pre₁ rw₁ mid₂ rw₂ post₂ hNd

/-! ## §5. Top-Level `Fn.mid` Lifting & `Ψ_hyb = Ψ_reg ∧ Ψ_cold` Soundness Theorems -/

private theorem regionQ_to_retPost (cm : CodeMap) (wit : CfgWitness) (Ψ_cold : CodeSpec)
    (H : HaltPost) (X : XPost) (rp₀ : BitVec 64) (m' : Mem 64) :
    ∀ (abi : RegionAbi) (vs' : Tup Val abi.retSig),
      regionRetPost abi (regionBailPost cm wit Ψ_cold H
        (WitGfp cm wit Ψ_cold H X) abi) rp₀ vs' m' →
      regionRetPost abi (PsiHyb cm wit Ψ_cold H) rp₀ vs' m'
  | .retEnvelope, _, h => h
  | .contified dualRet, _, h => by cases dualRet <;> exact h.2

/-- Lift `PsiReg` at region entry to `Func.spec` of `(liftRegion cm rw).body` over `witEnv`. -/
theorem psiReg_to_func_spec (cm : CodeMap) (wit : CfgWitness) (Ψ_cold : CodeSpec) (H : HaltPost)
    (X : XPost) (hH : ∀ c m', H c m' → X haltSym [i64] (c, ()) m')
    (hChk : wit.check cm = true) {rw : RegionWitness} (hMem : rw ∈ wit.regions)
    (r₀ : Regs) (m : Mem 64) (hReg : PsiReg cm wit Ψ_cold H rw.entryPc ⟨r₀, m⟩) :
    Func.spec (witEnv cm wit) (liftRegion cm rw).body r₀.toRegsV.toTup m
      (regionRetPost rw.abi (PsiHyb cm wit Ψ_cold H) r₀.rp) X := by
  rcases List.mem_iff_append.1 hMem with ⟨pre, post, hSplit⟩
  have hAuxAll : CfgWitness.checkAux cm [] wit.regions = true := by
    dsimp only [CfgWitness.check] at hChk; simp only [Bool.and_eq_true] at hChk; exact hChk.2
  have hAux := checkAux_append cm pre (rw :: post) [] (by simpa [hSplit] using hAuxAll)
  dsimp only [CfgWitness.checkAux] at hAux; simp only [Bool.and_eq_true] at hAux
  have hRwChk := hAux.1
  dsimp only [RegionWitness.check] at hRwChk; simp only [Bool.and_eq_true] at hRwChk
  have hEntMap : rw.entryPc ∈ rw.tree.map GroupTree.entryPc := by
    simpa using hRwChk.1.1.1.1.2
  have hEntAll := region_entryPc_mem_allPcs cm wit hChk hMem
  have hPg := witGfp_post cm wit Ψ_cold H X
    (psiReg_implies_witGfp cm wit Ψ_cold H X hH hChk _ _ hReg) pre rw post hSplit hEntAll
  have hSpecPre := regionSpec_from_canonNodes hRwChk.1.1.2 hEntMap r₀ m hPg
  have hQMono : ∀ vs m', regionQ cm wit Ψ_cold H (WitGfp cm wit Ψ_cold H X) rw r₀.rp vs m' →
      regionRetPost rw.abi (PsiHyb cm wit Ψ_cold H) r₀.rp vs m' :=
    fun vs m' hq => regionQ_to_retPost cm wit Ψ_cold H X r₀.rp m' rw.abi vs hq
  have hSpecEnv : Func.spec (witEnv cm wit) (liftRegion cm rw).body r₀.toRegsV.toTup m
      (regionQ cm wit Ψ_cold H (WitGfp cm wit Ψ_cold H X) rw r₀.rp) X := by
    refine Func.spec_env_mono ?_ hSpecPre
    intro f as bs xs m' P' E' hf
    dsimp only [witEnv]
    rw [hSplit, witEnvAux_append]
    exact witEnvAux_mono_right cm _ (rw :: post) f as bs xs m' P' E' hf
  exact Func.spec_mono (witEnv cm wit) (liftRegion cm rw).body _ m _ _ _ _ hQMono
    (fun _ _ _ _ h => h) hSpecEnv

/-- Lift `PsiReg` through `Unified.Ssa.midEnd` (`Fn.mid`, `fn_mid_spec`). -/
theorem psiReg_to_mid_spec (cm : CodeMap) (wit : CfgWitness) (Ψ_cold : CodeSpec) (H : HaltPost)
    (X : XPost) (lt : LegalTarget) (hH : ∀ c m', H c m' → X haltSym [i64] (c, ()) m')
    (hChk : wit.check cm = true) {rw : RegionWitness} (hMem : rw ∈ wit.regions)
    (hSupp : ((liftRegion cm rw).earlyOpt).body.supportsSource lt = true)
    (r₀ : Regs) (m : Mem 64) (hReg : PsiReg cm wit Ψ_cold H rw.entryPc ⟨r₀, m⟩) :
    Func.spec (legalEnv lt (witEnv cm wit)) ((liftRegion cm rw).mid lt).body
      (encodeTup lt regSig r₀.toRegsV.toTup) m
      (legalPost lt (regionRetPost rw.abi (PsiHyb cm wit Ψ_cold H) r₀.rp))
      (legalXPost lt X) := by
  let s : SSpec := {
    Γ := witEnv cm wit
    C := fun as rs xs m' Q' X' =>
      ∃ (h₁ : as = regSig) (h₂ : rs = rw.abi.retSig),
        Func.spec (witEnv cm wit) (liftRegion cm rw).body
          (cast (congrArg (Tup Val) h₁) xs) m' (cast (congrArg Post h₂) Q') X'
  }
  have hSat : ssa.Sat (liftRegion cm rw) s := by
    intro xs m' Q' X' ⟨h₁, h₂, hSp⟩
    cases h₁; cases h₂; exact hSp
  have hMid := midEnd_sound lt (liftRegion cm rw) ((liftRegion cm rw).mid lt) s
    (liftRegion_wf cm rw) (by simp [hSupp]) hSat
  exact hMid (encodeTup lt regSig r₀.toRegsV.toTup) m _ _
    ⟨rfl, rfl, r₀.toRegsV.toTup, regionRetPost rw.abi (PsiHyb cm wit Ψ_cold H) r₀.rp, X,
      ⟨rfl, rfl, psiReg_to_func_spec cm wit Ψ_cold H X hH hChk hMem r₀ m hReg⟩,
      rfl, rfl, rfl⟩

private theorem cm_wp_closed (cm : CodeMap) (H : HaltPost) :
    SpecsClosed cm cm.symEnv (cm.wp H) H := by
  intro pc b hlu st hbp Ψ hClosed
  exact hClosed pc b hlu st (blockFlat_wp_mono (fun pc' st' h => h Ψ hClosed) b _ _ hbp)

/-- End-to-end verified bridge from whole-`CodeMap` `cm.wp H` to legalized `Fn.mid lt`
for every recovered region in `checkAndLiftWitness cm wit = .ok (fns, wRes)`. -/
theorem checkAndLiftWitness_cm_wp_to_mid (cm : CodeMap) (wit : CfgWitness)
    (H : HaltPost) (X : XPost) (lt : LegalTarget)
    {fns : List Fn} {wRes : CodeMap}
    (hLift : checkAndLiftWitness cm wit = .ok (fns, wRes))
    (hH : ∀ c m', H c m' → X haltSym [i64] (c, ()) m')
    {rw : RegionWitness} (hMem : rw ∈ wit.regions)
    (hSupp : ((liftRegion cm rw).earlyOpt).body.supportsSource lt = true)
    (r₀ : Regs) (m : Mem 64) (hWp : cm.wp H rw.entryPc ⟨r₀, m⟩) :
    Func.spec (legalEnv lt (witEnv cm wit)) ((liftRegion cm rw).mid lt).body
      (encodeTup lt regSig r₀.toRegsV.toTup) m
      (legalPost lt (regionRetPost rw.abi (cm.wp H) r₀.rp)) (legalXPost lt X) := by
  dsimp only [checkAndLiftWitness] at hLift
  split at hLift
  · rename_i hChk
    have hClosedHyb : SpecsClosed cm cm.symEnv (PsiHyb cm wit (cm.wp H) H) H := by
      intro pc b hlu st hbp
      have hCold : cm.wp H pc st :=
        cm_wp_closed cm H pc b hlu st
          (blockFlat_wp_mono (fun pc' st' h => by
            dsimp only [PsiHyb] at h
            by_cases hc : (wit.regions.flatMap RegionWitness.allPcs).contains pc' = true
            · simp only [hc, ↓reduceIte] at h; exact h.2
            · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h; exact h) b _ _ hbp)
      by_cases hc : (wit.regions.flatMap RegionWitness.allPcs).contains pc = true
      · dsimp only [PsiHyb]; simp only [hc, ↓reduceIte]
        refine ⟨Xcap.Lfp.lfp_closed (regionStep_mono cm wit (cm.wp H) H) (pc, st)
          ⟨b, hlu, ?_⟩, hCold⟩
        exact blockFlat_wp_mono (fun pc' st' h => by
          dsimp only [PsiHyb] at h; exact h) b _ _ hbp
      · dsimp only [PsiHyb]; simp only [hc, Bool.false_eq_true, ↓reduceIte]; exact hCold
    have hReg : PsiReg cm wit (cm.wp H) H rw.entryPc ⟨r₀, m⟩ := by
      have hHyb := hWp (PsiHyb cm wit (cm.wp H) H) hClosedHyb
      dsimp only [PsiHyb] at hHyb
      rcases List.mem_iff_append.1 hMem with ⟨pre, post, hSplit⟩
      have hEntAll := region_entryPc_mem_allPcs cm wit hChk hMem
      have hc := mem_allPcs_of_split hSplit hEntAll
      simp only [hc, ↓reduceIte] at hHyb
      exact hHyb.1
    have hSpec := psiReg_to_mid_spec cm wit (cm.wp H) H X lt hH hChk hMem hSupp r₀ m hReg
    refine Func.spec_mono (legalEnv lt (witEnv cm wit)) ((liftRegion cm rw).mid lt).body _ m _ _ _ _
      (fun vs m' hPost => ?_) (fun _ _ _ _ h => h) hSpec
    rcases hPost with ⟨xs, rfl, hRet⟩
    refine ⟨xs, rfl, ?_⟩
    have hHybCold : ∀ pc' s', PsiHyb cm wit (cm.wp H) H pc' s' → cm.wp H pc' s' := by
      intro pc' s' h
      dsimp only [PsiHyb] at h
      split at h
      · exact h.2
      · exact h
    have hgen : ∀ (abi : RegionAbi) (xs' : Tup Val abi.retSig),
        regionRetPost abi (PsiHyb cm wit (cm.wp H) H) r₀.rp xs' m' →
        regionRetPost abi (cm.wp H) r₀.rp xs' m' := by
      intro abi xs' h'
      cases abi with
      | retEnvelope => exact hHybCold _ _ h'
      | contified dualRet => cases dualRet <;> exact hHybCold _ _ h'
    exact hgen rw.abi xs hRet
  · cases hLift

private theorem lookupAddr_filter_of_addr (cm : CodeMap) (p : BitVec 64 → Bool) (pc : BitVec 64)
    (hp : p pc = true) :
    CodeMap.lookupAddr (cm.filter fun e => p e.addr) pc = CodeMap.lookupAddr cm pc := by
  induction cm with
  | nil => rfl
  | cons e es ih =>
      dsimp only [List.filter, CodeMap.lookupAddr]
      by_cases heq : e.addr = pc
      · subst heq; simp [hp, CodeMap.lookupAddr]
      · cases hpe : p e.addr <;> simp [beq_false_of_ne heq, CodeMap.lookupAddr, ih]

/-- Hybrid soundness theorem (`Ψ_hyb = Ψ_reg ∧ Ψ_cold`): if `W_res` blocks satisfy `Ψ_cold`,
lifted `(fn.mid lt)` specs satisfy `Ψ_cold` at region entries, and any dropped non-entry PCs
preserve `Ψ_cold`, then `SpecsClosed cm cm.symEnv (PsiHyb cm wit Ψ_cold H) H` holds and
`cm.wp H pc₀ st₀` implies `Ψ_cold pc₀ st₀`. -/
theorem checkAndLiftWitness_hybrid_sound (cm : CodeMap) (wit : CfgWitness)
    (Ψ_cold : CodeSpec) (H : HaltPost) (X : XPost) (lt : LegalTarget)
    {fns : List Fn} {wRes : CodeMap}
    (hLift : checkAndLiftWitness cm wit = .ok (fns, wRes))
    (hH : ∀ c m', H c m' → X haltSym [i64] (c, ()) m')
    (hSupp : ∀ rw ∈ wit.regions, ((liftRegion cm rw).earlyOpt).body.supportsSource lt = true)
    (hRes : SpecsClosed wRes cm.symEnv Ψ_cold H)
    (hEntry : ∀ rw ∈ wit.regions, ∀ r₀ m₀,
      Func.spec (legalEnv lt (witEnv cm wit)) ((liftRegion cm rw).mid lt).body
        (encodeTup lt regSig r₀.toRegsV.toTup) m₀
        (legalPost lt (regionRetPost rw.abi (PsiHyb cm wit Ψ_cold H) r₀.rp))
        (legalXPost lt X) →
      Ψ_cold rw.entryPc ⟨r₀, m₀⟩)
    (hDrop : ∀ rw ∈ wit.regions, rw.retainFallbacks = false →
      ∀ pc ∈ rw.allPcs, pc ≠ rw.entryPc → ∀ st,
        PsiReg cm wit Ψ_cold H pc st → Ψ_cold pc st) :
    SpecsClosed cm cm.symEnv (PsiHyb cm wit Ψ_cold H) H ∧
      ∀ pc₀ st₀, cm.wp H pc₀ st₀ → Ψ_cold pc₀ st₀ := by
  dsimp only [checkAndLiftWitness] at hLift
  split at hLift
  · rename_i hChk
    cases hLift
    have hClosed : SpecsClosed cm cm.symEnv (PsiHyb cm wit Ψ_cold H) H := by
      intro pc b hlu st hbp
      have hStepReg : RegionStep cm wit Ψ_cold H
          (fun p => PsiReg cm wit Ψ_cold H p.1 p.2) (pc, st) :=
        ⟨b, hlu, blockFlat_wp_mono (fun pc' st' h => h) b _ _ hbp⟩
      have hRegPc : PsiReg cm wit Ψ_cold H pc st :=
        Xcap.Lfp.lfp_closed (regionStep_mono cm wit Ψ_cold H) (pc, st) hStepReg
      have hColdBp : b.wp cm.symEnv Ψ_cold H (pushRegsV st.regs.toRegsV) st.mem :=
        blockFlat_wp_mono (fun pc' st' h => by
          dsimp only [PsiHyb] at h
          split at h
          · exact h.2
          · exact h) b _ _ hbp
      have hResAt : ∀ (hNotEnt : pc ∉ wit.regions.map (·.entryPc))
          (hNotDrop : pc ∉ ((wit.regions.filter (fun r => !r.retainFallbacks)).flatMap
            RegionWitness.allPcs)), Ψ_cold pc st := by
        intro hNotEnt hNotDrop
        have hFilt : CodeMap.lookupAddr (residualCodeMap cm wit) pc = CodeMap.lookupAddr cm pc := by
          dsimp only [residualCodeMap]
          apply lookupAddr_filter_of_addr cm
            (fun a => (!(wit.regions.map (·.entryPc)).contains a) &&
              (!((wit.regions.filter (fun r => !r.retainFallbacks)).flatMap
                RegionWitness.allPcs).contains a)) pc
          simp [hNotEnt, hNotDrop]
        exact hRes pc b (by rw [hFilt]; exact hlu) st hColdBp
      by_cases hc : (wit.regions.flatMap RegionWitness.allPcs).contains pc = true
      · dsimp only [PsiHyb]; simp only [hc, ↓reduceIte]
        refine ⟨hRegPc, ?_⟩
        rw [List.contains_iff_mem, List.mem_flatMap] at hc
        rcases hc with ⟨rw, hRwMem, hPcRw⟩
        by_cases hEqEnt : pc = rw.entryPc
        · subst hEqEnt
          exact hEntry rw hRwMem st.regs st.mem
            (psiReg_to_mid_spec cm wit Ψ_cold H X lt hH hChk hRwMem (hSupp rw hRwMem)
              st.regs st.mem hRegPc)
        · by_cases hRet : rw.retainFallbacks = true
          · exact hResAt (fun hInEnt => by
              rw [List.mem_map] at hInEnt
              rcases hInEnt with ⟨rw', hRw'Mem, hRw'Eq⟩
              by_cases hSame : rw' = rw
              · subst hSame; exact hEqEnt hRw'Eq.symm
              · exact regionAllPcs_disjoint_of_ne cm wit hChk hRwMem hRw'Mem (Ne.symm hSame)
                  pc hPcRw (hRw'Eq ▸ region_entryPc_mem_allPcs cm wit hChk hRw'Mem))
              (fun hInDrop => by
              rw [List.mem_flatMap] at hInDrop
              rcases hInDrop with ⟨rw', hRw'Filt, hPcRw'⟩
              rw [List.mem_filter] at hRw'Filt
              by_cases hSame : rw' = rw
              · subst hSame; simp [hRet] at hRw'Filt
              · exact regionAllPcs_disjoint_of_ne cm wit hChk hRwMem hRw'Filt.1 (Ne.symm hSame) pc
                  hPcRw hPcRw')
          · have hRetF : rw.retainFallbacks = false := by
              cases hrf : rw.retainFallbacks <;> simp_all
            exact hDrop rw hRwMem hRetF pc hPcRw hEqEnt st hRegPc
      · dsimp only [PsiHyb]; simp only [hc, Bool.false_eq_true, ↓reduceIte]
        exact hResAt (fun hInEnt => by
          rw [List.mem_map] at hInEnt
          rcases hInEnt with ⟨rw', hRw'Mem, hRw'Eq⟩
          exact hc (List.contains_iff_mem.2 (List.mem_flatMap.2
            ⟨rw', hRw'Mem, hRw'Eq ▸ region_entryPc_mem_allPcs cm wit hChk hRw'Mem⟩)))
          (fun hInDrop => by
          rw [List.mem_flatMap] at hInDrop
          rcases hInDrop with ⟨rw', hRw'Filt, hPcRw'⟩
          rw [List.mem_filter] at hRw'Filt
          exact hc (List.contains_iff_mem.2 (List.mem_flatMap.2 ⟨rw', hRw'Filt.1, hPcRw'⟩)))
    refine ⟨hClosed, fun pc₀ st₀ hWp => ?_⟩
    have hHyb := hWp (PsiHyb cm wit Ψ_cold H) hClosed
    dsimp only [PsiHyb] at hHyb
    split at hHyb
    · exact hHyb.2
    · exact hHyb
  · cases hLift

end LeanQbe.T.Unified
