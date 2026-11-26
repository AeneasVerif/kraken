module

public import LeanQbe.T.Unified.CfgRecovery
public import LeanQbe.T.BedrockWord.Exec
import LeanQbe.T.FlatLemmas
import LeanQbe.T.WPLemmas
import LeanQbe.T.OpsLemmas
import LeanQbe.T.MainLemmas
import LeanQbe.T.GroupLfpLemmas

/-!
# Block-Level Soundness Lemmas for Verified CFG Recovery (`Unified.CfgRecoveryLemmas`)

Proof companion to `LeanQbe.T.Unified.CfgRecovery` behind the module-system proof firewall
(`*Lemmas*` imports stay private, `0` `@[expose]`):

* Prefix / shift / `diagCtx` helpers for `BlockFlat` and `TFlat`.
* `symEvalOp_wp_mono`, `liftEdge_wp`, `liftBlock_wp`, `liftBlock_wp_init`: block-level soundness
  linking `BlockFlat.wp` to `denote` of `liftBlock`.
* `liftRegion_wf`, `liftRegion_mid_wf`: `Fn.Wf` via `Func.wf_of_denote` and `Unified.Ssa.midEnd`.
* `RegionStep`, `blockFlat_wp_mono`, `regionStep_mono`, `PsiReg`, `PsiHyb`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Unified

open LeanQbe.T
open LeanQbe.T.BedrockWord

/-! ## §1. De Bruijn Prefix, Shifting, and Diagonal Context Helpers -/

theorem listGet?_isSome_lt {α : Type} :
    (xs : List α) → {i : Nat} → (listGet? xs i).isSome = true → i < xs.length
  | [], _, h => by cases h
  | _ :: _, 0, _ => Nat.zero_lt_succ _
  | _ :: xs, _ + 1, h => Nat.succ_lt_succ (listGet?_isSome_lt xs h)

theorem listGet?_append_left {α : Type} :
    (xs ys : List α) → {i : Nat} → i < xs.length →
    listGet? (xs ++ ys) i = listGet? xs i
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => rfl
  | _ :: xs, ys, _ + 1, h => listGet?_append_left xs ys (Nat.lt_of_succ_lt_succ h)

theorem listGet?_append_skip {α : Type} :
    (extra xs : List α) → (k : Nat) →
    listGet? (extra ++ xs) (extra.length + k) = listGet? xs k
  | [], _, _ => by simp
  | _ :: es, xs, k => by
      simp only [List.length_cons, List.cons_append]
      rw [show es.length + 1 + k = (es.length + k) + 1 by omega]
      exact listGet?_append_skip es xs k

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
  | var _ =>
      dsimp only [denoteArg]
      rw [lookupV_prefix vsTail hctx hchk]

private theorem denoteArgs_prefix {V : Ty → Type} {Γ : List Ty}
    {bvs : List ((t : Ty) × V t)} (vsTail : List ((t : Ty) × V t))
    (hctx : CtxTypes Γ bvs) :
    {ts : List Ty} → {as : Tup (Arg K) ts} → checkArgs Γ as = true →
    denoteArgs (bvs ++ vsTail) as = denoteArgs bvs as
  | [], (), _ => rfl
  | _ :: _, (_, _), hchk => by
      dsimp only [checkArgs] at hchk
      simp only [Bool.and_eq_true] at hchk
      dsimp only [denoteArgs]
      rw [denoteArg_prefix vsTail hctx hchk.1, denoteArgs_prefix vsTail hctx hchk.2]

private theorem denoteRegsExpr_prefix {V : Ty → Type} {Γ : List Ty}
    {bvs : List ((t : Ty) × V t)} (vsTail : List ((t : Ty) × V t))
    (hctx : CtxTypes Γ bvs) {e : RegsExpr K} (hchk : checkRegsExpr Γ e = true) :
    denoteRegsExpr (bvs ++ vsTail) e = denoteRegsExpr bvs e := by
  dsimp only [checkRegsExpr] at hchk
  simp only [Bool.and_eq_true] at hchk
  dsimp only [denoteRegsExpr]
  rw [denoteArg_prefix vsTail hctx hchk.1.1.1.1.1,
      denoteArg_prefix vsTail hctx hchk.1.1.1.1.2,
      denoteArg_prefix vsTail hctx hchk.1.1.1.2,
      denoteArg_prefix vsTail hctx hchk.1.1.2,
      denoteArg_prefix vsTail hctx hchk.1.2,
      denoteArg_prefix vsTail hctx hchk.2]

theorem pushTup_append {α : Type} {f : α → Type} :
    {ts : List α} → (xs : Tup f ts) → (bvs vsTail : List ((a : α) × f a)) →
    pushTup xs (bvs ++ vsTail) = pushTup xs bvs ++ vsTail
  | [], (), _, _ => rfl
  | _ :: _, (_, xs), bvs, vsTail => pushTup_append xs (_ :: bvs) vsTail

theorem pushTup_length {α : Type} {f : α → Type} :
    {ts : List α} → (xs : Tup f ts) → (vs : List ((a : α) × f a)) →
    (pushTup xs vs).length = ts.length + vs.length
  | [], (), vs => (Nat.zero_add vs.length).symm
  | _ :: _, (_, xs), vs => by
      dsimp only [pushTup, List.length_cons]
      rw [pushTup_length xs (_ :: vs), List.length_cons]
      omega

private theorem denoteArg_shift {V : Ty → Type} (extra vs : List ((t : Ty) × V t))
    {t : Ty} (a : Arg K t) :
    denoteArg (extra ++ vs) (shiftArg extra.length a) = denoteArg vs a := by
  cases a with
  | imm _ => rfl
  | var i =>
      dsimp only [shiftArg, denoteArg, lookupV]
      rw [Nat.add_comm i extra.length, listGet?_append_skip]

private theorem denoteRegsExpr_shift {V : Ty → Type} (extra vs : List ((t : Ty) × V t))
    (e : RegsExpr K) :
    denoteRegsExpr (extra ++ vs) (shiftRegsExpr extra.length e) = denoteRegsExpr vs e := by
  dsimp only [denoteRegsExpr, shiftRegsExpr]
  rw [denoteArg_shift, denoteArg_shift, denoteArg_shift,
      denoteArg_shift, denoteArg_shift, denoteArg_shift]

private theorem denoteArg_shift1 {V : Ty → Type} {t' : Ty} (v : V t')
    (vs : List ((t : Ty) × V t)) {t : Ty} (a : Arg K t) :
    denoteArg (⟨t', v⟩ :: vs) (shiftArg 1 a) = denoteArg vs a :=
  denoteArg_shift [⟨t', v⟩] vs a

private theorem denoteRegsExpr_shift1 {V : Ty → Type} {t' : Ty} (v : V t')
    (vs : List ((t : Ty) × V t)) (e : RegsExpr K) :
    denoteRegsExpr (⟨t', v⟩ :: vs) (shiftRegsExpr 1 e) = denoteRegsExpr vs e :=
  denoteRegsExpr_shift [⟨t', v⟩] vs e

private theorem denoteRegsExpr_toTup {e : RegsExpr K} {vs : List ((t : Ty) × Val t)}
    {nxt' : RegsExpr Val} (h : denoteRegsExpr vs e = some nxt') :
    ∃ args', denoteArgs vs e.toTup = some args' ∧ vals args' = nxt'.eval.toRegsV.toTup := by
  dsimp only [denoteRegsExpr] at h
  cases hs : denoteArg vs e.sp <;> rw [hs] at h; · cases h
  cases hrp : denoteArg vs e.rp <;> rw [hrp] at h; · cases h
  cases hrv : denoteArg vs e.rv <;> rw [hrv] at h; · cases h
  cases hr1 : denoteArg vs e.r1 <;> rw [hr1] at h; · cases h
  cases hr2 : denoteArg vs e.r2 <;> rw [hr2] at h; · cases h
  cases hr3 : denoteArg vs e.r3 <;> rw [hr3] at h; · cases h
  cases h
  refine ⟨(_, _, _, _, _, _, ()), ?_, rfl⟩
  dsimp only [RegsExpr.toTup, denoteArgs]
  rw [hs, hrp, hrv, hr1, hr2, hr3]

private theorem denoteArgs_baseRegs (xs : Tup Val regSig)
    (vsTail : List ((t : Ty) × Val t)) :
    ∃ args', denoteArgs (pushTup xs vsTail)
      (⟨.var 5, .var 4, .var 3, .var 2, .var 1, .var 0⟩ : RegsExpr K).toTup = some args' ∧
      vals args' = xs := by
  rcases xs with ⟨sp, rp, rv, r1, r2, r3, ⟨⟩⟩
  refine ⟨(.var sp, .var rp, .var rv, .var r1, .var r2, .var r3, ()), ?_, rfl⟩
  dsimp only [pushTup, RegsExpr.toTup, denoteArgs, denoteArg, lookupV, listGet?, castTy]
  simp only [↓reduceDIte]

private theorem denoteArgs_retRegArgs (isAlt : Val .bool) (xs : Tup Val regSig)
    (vsTail : List ((t : Ty) × Val t)) :
    ∃ args', ∃ c' : Arg Val .bool,
      denoteArg (pushTup (as := .bool :: regSig) (isAlt, xs) vsTail) (.var 6) = some c' ∧
      c'.val = isAlt ∧
      denoteArgs (pushTup (as := .bool :: regSig) (isAlt, xs) vsTail)
        (⟨.var 5, .var 4, .var 3, .var 2, .var 1, .var 0⟩ : RegsExpr K).toTup = some args' ∧
      vals args' = xs := by
  rcases xs with ⟨sp, rp, rv, r1, r2, r3, ⟨⟩⟩
  refine ⟨(.var sp, .var rp, .var rv, .var r1, .var r2, .var r3, ()), .var isAlt, ?_, rfl, ?_, rfl⟩
  · rfl
  · dsimp only [pushTup, RegsExpr.toTup, denoteArgs, denoteArg, lookupV, listGet?, castTy]
    simp only [↓reduceDIte]

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
  | _ :: vs, p, hp => by
      cases hp with
      | head => rfl
      | tail _ hp => exact diagV_diagCtx vs p hp

private theorem ctxRel_diagL : (ls : List ((ts : List Ty) × Cont ts)) →
    CtxRel (diagCtxOfL ls) ls ls
  | [] => .nil
  | _ :: ls => .cons List.mem_cons_self
      ((ctxRel_diagL ls).mono fun _ hp => List.mem_cons_of_mem _ hp)

private theorem monoD_diagL : (ls : List ((ts : List Ty) × Cont ts)) → MonoD (diagCtxOfL ls)
  | [], _, h => nomatch h
  | _ :: ls, p, hp => by
      cases hp with
      | head => exact fun _ _ h => h
      | tail _ hp => exact monoD_diagL ls p hp

/-! ## §2. Symbolic Evaluation Invariant and Soundness -/

private def levelVal {t : Ty} (bvs : List ((t' : Ty) × Val t')) (lvl : Nat) : Option (Val t) :=
  if lvl < bvs.length then lookupV bvs t (bvs.length - 1 - lvl) else none

private def SymValMatch (bvs : List ((t : Ty) × Val t)) (rp₀ : BitVec 64) :
    SymVal → (t : Ty) → Val t → Prop
  | .rpOffset off, t, v => ∀ h : t = i64, cast (congrArg Val h) v = rp₀ + off
  | .const w, t, v => ∀ h : t = i64, cast (congrArg Val h) v = w
  | .alignedConst w, t, v => ∀ h : t = i64, cast (congrArg Val h) v = w ∧ AlignedAddr w
  | .taggedAligned w tag, t, v =>
      ∀ h : t = i64, cast (congrArg Val h) v = w ||| tag ∧ AlignedAddr w ∧ tag.toNat < 8
  | .shl3 lvl, t, v => ∀ h : t = i64,
      ∃ x : Val i64, levelVal bvs lvl = some x ∧
        cast (congrArg Val h) v = BitVec.ofNat 64 (8 * x.toNat)
  | .stride base lvl, t, v => ∀ h : t = i64,
      ∃ x : Val i64, levelVal bvs lvl = some x ∧
        cast (congrArg Val h) v = base + BitVec.ofNat 64 (8 * x.toNat)
  | .ite cLvl tSym eSym, t, v => ∀ h : t = i64,
      ∃ b : Val .bool, levelVal bvs cLvl = some b ∧
        ((b = true → SymValMatch bvs rp₀ tSym i64 (cast (congrArg Val h) v)) ∧
         (b = false → SymValMatch bvs rp₀ eSym i64 (cast (congrArg Val h) v)))
  | .boolConst c, t, v => ∀ h : t = .bool, cast (congrArg Val h) v = c
  | .cmpUlt lvl bound, t, v => ∀ h : t = .bool,
      ∃ x : Val i64, levelVal bvs lvl = some x ∧
        cast (congrArg Val h) v = BitVec.ult x bound
  | .top, _, _ => True

private def SymFactsOk (bvs : List ((t : Ty) × Val t)) (facts : List SymFact) : Prop :=
  ∀ f ∈ facts, match f with
    | .ultBound lvl bound => ∃ x : Val i64, levelVal bvs lvl = some x ∧ x.toNat < bound.toNat

private structure SymStateOk (bvs : List ((t : Ty) × Val t)) (rp₀ : BitVec 64)
    (st : SymState) : Prop where
  lenEq   : st.env.length = bvs.length
  ctxOk   : CtxTypes st.ctx bvs
  valsOk  : ∀ idx, idx < bvs.length →
    match listGet? st.env idx, listGet? bvs idx with
    | some sv, some ⟨t, v⟩ => SymValMatch bvs rp₀ sv t v
    | _, _ => True
  factsOk : SymFactsOk bvs st.facts

private theorem levelVal_prepend {t : Ty} (extra bvs : List ((t' : Ty) × Val t'))
    {lvl : Nat} {x : Val t} (h : levelVal bvs lvl = some x) :
    levelVal (extra ++ bvs) lvl = some x := by
  dsimp only [levelVal] at h ⊢
  split at h
  · rename_i hlt
    have hlt' : lvl < (extra ++ bvs).length := by rw [List.length_append]; omega
    rw [ite_eq_left hlt']
    dsimp only [lookupV] at h ⊢
    rw [show (extra ++ bvs).length - 1 - lvl = extra.length + (bvs.length - 1 - lvl) by
      rw [List.length_append]; omega]
    rw [listGet?_append_skip]
    exact h
  · cases h

private theorem symValMatch_prepend (extra bvs : List ((t' : Ty) × Val t'))
    (rp₀ : BitVec 64) :
    (sv : SymVal) → (t : Ty) → (v : Val t) →
    SymValMatch bvs rp₀ sv t v → SymValMatch (extra ++ bvs) rp₀ sv t v
  | .rpOffset _, _, _, h => h
  | .const _, _, _, h => h
  | .alignedConst _, _, _, h => h
  | .taggedAligned _ _, _, _, h => h
  | .shl3 _, _, _, h => fun heq =>
      let ⟨x, hx, hval⟩ := h heq
      ⟨x, levelVal_prepend extra bvs hx, hval⟩
  | .stride _ _, _, _, h => fun heq =>
      let ⟨x, hx, hval⟩ := h heq
      ⟨x, levelVal_prepend extra bvs hx, hval⟩
  | .ite _ tS eS, _, _, h => fun heq =>
      let ⟨b, hb, ht, he⟩ := h heq
      ⟨b, levelVal_prepend extra bvs hb,
       fun hc => symValMatch_prepend extra bvs rp₀ tS i64 _ (ht hc),
       fun hc => symValMatch_prepend extra bvs rp₀ eS i64 _ (he hc)⟩
  | .boolConst _, _, _, h => h
  | .cmpUlt _ _, _, _, h => fun heq =>
      let ⟨x, hx, hval⟩ := h heq
      ⟨x, levelVal_prepend extra bvs hx, hval⟩
  | .top, _, _, _ => trivial

private theorem symFactsOk_prepend (extra bvs : List ((t' : Ty) × Val t'))
    {facts : List SymFact} (h : SymFactsOk bvs facts) :
    SymFactsOk (extra ++ bvs) facts := by
  intro f hf
  cases f with
  | ultBound lvl bound =>
      obtain ⟨x, hx, hlt⟩ := h _ hf
      exact ⟨x, levelVal_prepend extra bvs hx, hlt⟩

private theorem castTy_same_eq {V : Ty → Type} {t' t : Ty} {v' : V t'} {v : V t}
    (h : castTy t' t v' = some v) : ∃ heq : t' = t, heq ▸ v' = v := by
  cases t' with
  | bool => cases t with
      | bool => cases h; exact ⟨rfl, rfl⟩
      | _ => cases h
  | bits m => cases t with
      | bits n =>
          dsimp only [castTy] at h
          split at h
          · rename_i heq; subst heq; cases h; exact ⟨rfl, rfl⟩
          · cases h
      | _ => cases h
  | float f => cases t with
      | float g =>
          dsimp only [castTy] at h
          split at h
          · rename_i heq; subst heq; cases h; exact ⟨rfl, rfl⟩
          · cases h
      | _ => cases h
  | pair a1 b1 => cases t with
      | pair a2 b2 =>
          dsimp only [castTy] at h
          cases h1 : tyDecEq a1 a2 <;> rw [h1] at h; · cases h
          cases h2 : tyDecEq b1 b2 <;> rw [h2] at h; · cases h
          rename_i e1 e2; subst e1 e2; cases h; exact ⟨rfl, rfl⟩
      | _ => cases h

private theorem evalArg_symValMatch {bvs : List ((t : Ty) × Val t)} {rp₀ : BitVec 64}
    {st : SymState} (hst : SymStateOk bvs rp₀ st) {t : Ty} {a : Arg K t} {a' : Arg Val t}
    (ha : denoteArg bvs a = some a') :
    SymValMatch bvs rp₀ (st.evalArg a) t a'.val := by
  cases a with
  | imm _ =>
      cases ha
      dsimp only [SymState.evalArg, Arg.val]
      cases t with
      | bool => exact fun _ => rfl
      | bits n =>
          by_cases h64 : n = 64
          · subst h64; exact fun _ => rfl
          · have hne : Ty.bits n ≠ Ty.bits 64 := fun he => h64 (by cases he; rfl)
            split
            · contradiction
            · exact absurd ‹_› hne
            · exact trivial
      | float _ => trivial
      | pair _ _ => trivial
  | var idx =>
      dsimp only [denoteArg, lookupV] at ha
      cases hg : listGet? bvs idx with
      | none => rw [hg] at ha; cases ha
      | some p =>
          rcases p with ⟨t', v'⟩
          rw [hg] at ha
          dsimp only at ha
          cases hc : castTy t' t v' with
          | none => rw [hc] at ha; cases ha
          | some _ =>
              rw [hc] at ha; cases ha
              obtain ⟨heq, hv⟩ := castTy_same_eq hc
              subst heq; cases hv
              have hlt : idx < bvs.length :=
                listGet?_isSome_lt bvs (by rw [hg]; rfl)
              have hval := hst.valsOk idx hlt
              rw [hg] at hval
              dsimp only [SymState.evalArg, SymState.getSym]
              cases he : listGet? st.env idx with
              | none => exact trivial
              | some _ => rw [he] at hval; exact hval

private theorem symStateOk_init (r : Regs) :
    SymStateOk (pushRegsV r.toRegsV) r.rp SymState.init := by
  refine ⟨rfl, CtxTypes.push r.toRegsV.toTup .nil, ?_, fun _ h => nomatch h⟩
  intro idx hlt
  match idx with
  | 0 | 1 | 2 | 3 | 5 => exact trivial
  | 4 => exact fun _ => by simp only [cast_eq, Regs.toRegsV]; exact (BitVec.add_zero r.rp).symm
  | _ + 6 => exact absurd hlt (by simp [pushRegsV, RegsV.toTup, pushTup])

private theorem listGet?_replicate_top :
    ∀ (ts : List Ty) (idx : Nat), idx < ts.length →
      listGet? (List.replicate ts.length SymVal.top) idx = some .top
  | [], _, hi => absurd hi (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: ts, idx + 1, hi => listGet?_replicate_top ts idx (Nat.lt_of_succ_lt_succ hi)

private theorem symStateOk_pushTop (extra : List ((t : Ty) × Val t)) (ts : List Ty)
    {bvs : List ((t : Ty) × Val t)} {rp₀ : BitVec 64} {st : SymState}
    (hst : SymStateOk bvs rp₀ st) (heq : extra.length = ts.length)
    (hctx : CtxTypes (pushTypes ts st.ctx) (extra ++ bvs)) :
    SymStateOk (extra ++ bvs) rp₀ (st.pushRes ts (List.replicate ts.length .top)) := by
  refine ⟨by simp [SymState.pushRes, heq, hst.lenEq], hctx, ?_,
    symFactsOk_prepend extra bvs hst.factsOk⟩
  intro idx hlt
  dsimp only [SymState.pushRes]
  by_cases hi : idx < extra.length
  · have hltRep : idx < (List.replicate ts.length SymVal.top).length := by
      simpa [heq] using hi
    rw [listGet?_append_left (List.replicate ts.length .top) st.env hltRep]
    rw [listGet?_append_left extra bvs hi]
    rw [listGet?_replicate_top ts idx (by omega)]
    cases listGet? extra idx <;> trivial
  · have hk : ∃ k, idx = extra.length + k ∧ k < bvs.length := by
      refine ⟨idx - extra.length, by omega, ?_⟩
      rw [List.length_append] at hlt; omega
    rcases hk with ⟨k, rfl, hk⟩
    have hrep : (List.replicate ts.length SymVal.top).length = extra.length := by simp [heq]
    have hskip : listGet? (List.replicate ts.length SymVal.top ++ st.env) (extra.length + k) =
        listGet? st.env k := by rw [← hrep, listGet?_append_skip]
    rw [hskip, listGet?_append_skip extra bvs k]
    have h0 := hst.valsOk k hk
    cases h1 : listGet? st.env k <;> cases h2 : listGet? bvs k
    · exact trivial
    · exact trivial
    · exact trivial
    · rw [h1, h2] at h0; exact symValMatch_prepend extra bvs rp₀ _ _ _ h0

private theorem symStateOk_cons {t : Ty} (v : Val t) (sv : SymVal)
    {bvs : List ((t' : Ty) × Val t')} {rp₀ : BitVec 64} {st : SymState}
    (hst : SymStateOk bvs rp₀ st)
    (hsv : SymValMatch (⟨t, v⟩ :: bvs) rp₀ sv t v) :
    SymStateOk (⟨t, v⟩ :: bvs) rp₀
      { st with env := sv :: st.env, ctx := t :: st.ctx } := by
  refine ⟨by simp [hst.lenEq], .cons hst.ctxOk, ?_, symFactsOk_prepend [⟨t, v⟩] bvs hst.factsOk⟩
  intro idx hlt
  cases idx with
  | zero => exact hsv
  | succ k =>
      have hk : k < bvs.length := Nat.lt_of_succ_lt_succ hlt
      have h0 := hst.valsOk k hk
      dsimp only [listGet?]
      cases h1 : listGet? st.env k <;> cases h2 : listGet? bvs k
      · exact trivial
      · exact trivial
      · exact trivial
      · rw [h1, h2] at h0; exact symValMatch_prepend [⟨t, v⟩] bvs rp₀ _ _ _ h0

private theorem symStateOk_store {bvs : List ((t : Ty) × Val t)} {rp₀ : BitVec 64}
    {st : SymState} (hst : SymStateOk bvs rp₀ st) :
    SymStateOk bvs rp₀ { st with hasStored := true } :=
  ⟨hst.lenEq, hst.ctxOk, hst.valsOk, hst.factsOk⟩

private theorem symStateOk_stepLoad {t : Ty} (v : Val t)
    {bvs : List ((t' : Ty) × Val t')} {rp₀ : BitVec 64} {st : SymState}
    (hst : SymStateOk bvs rp₀ st) (a : Arg K i64) :
    SymStateOk (⟨t, v⟩ :: bvs) rp₀ (st.stepLoad t a) := by
  have h := symStateOk_cons v .top hst trivial
  exact ⟨h.lenEq, h.ctxOk, h.valsOk, h.factsOk⟩

private def SymMemOk (m₀ mCur : Mem 64) (bvs : List ((t : Ty) × Val t)) (st : SymState) : Prop :=
  (st.hasStored = false → mCur = m₀) ∧
  ∀ e ∈ st.memLoads, e.clean = true →
    ∃ (x v : Val i64),
      levelVal bvs e.idxLvl = some x ∧
      levelVal bvs e.valLvl = some v ∧
      loadVal m₀ i64 (e.tblBase + BitVec.ofNat 64 (8 * x.toNat)) = some v

private theorem symMemOk_init (r : Regs) (m : Mem 64) :
    SymMemOk m m (pushRegsV r.toRegsV) SymState.init :=
  ⟨fun _ => rfl, fun _ h => nomatch h⟩

private theorem symMemOk_prepend {m₀ mCur : Mem 64} (extra bvs : List ((t : Ty) × Val t))
    {st : SymState} (hm : SymMemOk m₀ mCur bvs st) :
    ∀ env' ctx', SymMemOk m₀ mCur (extra ++ bvs) { st with env := env', ctx := ctx' } := by
  intro env' ctx'
  refine ⟨hm.1, fun e he hcl => ?_⟩
  obtain ⟨x, v, hx, hv, hld⟩ := hm.2 e he hcl
  exact ⟨x, v, levelVal_prepend extra bvs hx, levelVal_prepend extra bvs hv, hld⟩

private theorem symMemOk_pushCondFact {m₀ mCur : Mem 64} {bvs : List ((t : Ty) × Val t)}
    {st : SymState} (hm : SymMemOk m₀ mCur bvs st) (c : Arg K .bool) (taken : Bool) :
    SymMemOk m₀ mCur bvs (st.pushCondFact c taken) := by
  dsimp only [SymState.pushCondFact]
  cases taken
  · exact hm
  · cases c with
    | imm _ => exact hm
    | var idx =>
        simp only [↓reduceIte]
        cases st.getSym idx <;> exact hm

private theorem symMemOk_store {m₀ mCur mNext : Mem 64} {bvs : List ((t : Ty) × Val t)}
    {st : SymState} (hm : SymMemOk m₀ mCur bvs st) :
    SymMemOk m₀ mNext bvs { st with hasStored := true } :=
  ⟨(fun h => by cases h), hm.2⟩

private theorem castTy_self {V : Ty → Type} {t : Ty} (v : V t) : castTy t t v = some v := by
  cases t with
  | bool => rfl
  | bits _ => simp [castTy]
  | float _ => simp [castTy]
  | pair a b =>
      dsimp only [castTy]
      cases h1 : tyDecEq a a with
      | isFalse h => exact absurd rfl h
      | isTrue e1 =>
          cases h2 : tyDecEq b b with
          | isFalse h => exact absurd rfl h
          | isTrue e2 => rfl

private theorem levelVal_cons_end {t : Ty} (v : Val t) (bvs : List ((t' : Ty) × Val t')) :
    levelVal (⟨t, v⟩ :: bvs) bvs.length = some v := by
  dsimp only [levelVal, List.length_cons]
  rw [ite_eq_left (Nat.lt_succ_self _), Nat.add_sub_cancel, Nat.sub_self]
  dsimp only [lookupV, listGet?]
  exact castTy_self v

private theorem symMemOk_stepLoad {m₀ mCur : Mem 64} {bvs : List ((t' : Ty) × Val t')}
    {rp₀ : BitVec 64} {st : SymState} (hst : SymStateOk bvs rp₀ st)
    (hm : SymMemOk m₀ mCur bvs st) (t : Ty) (a : Arg K i64) {a' : Arg Val i64}
    (ha : denoteArg bvs a = some a') (v : Val t) (hload : loadVal mCur t a'.val = some v) :
    SymMemOk m₀ mCur (⟨t, v⟩ :: bvs) (st.stepLoad t a) := by
  dsimp only [SymState.stepLoad]
  refine ⟨hm.1, fun e he hcl => ?_⟩
  have hOld : ∀ e' ∈ st.memLoads, e'.clean = true →
      ∃ (x w : Val i64), levelVal (⟨t, v⟩ :: bvs) e'.idxLvl = some x ∧
        levelVal (⟨t, v⟩ :: bvs) e'.valLvl = some w ∧
        loadVal m₀ i64 (e'.tblBase + BitVec.ofNat 64 (8 * x.toNat)) = some w := by
    intro e' he' hcl'
    obtain ⟨x, w, hx, hw, hld⟩ := hm.2 e' he' hcl'
    exact ⟨x, w, levelVal_prepend [⟨t, v⟩] bvs hx, levelVal_prepend [⟨t, v⟩] bvs hw, hld⟩
  cases t with
  | bool | float _ | pair _ _ => exact hOld e he hcl
  | bits n =>
      by_cases h64 : n = 64
      · subst h64
        dsimp only at he
        cases hev : st.evalArg a with
        | stride tblBase idxLvl =>
            rw [hev] at he
            rcases List.mem_cons.1 he with rfl | he'
            · simp only at hcl
              have hSto : st.hasStored = false := by cases hhs : st.hasStored <;> simp_all
              have hmt := evalArg_symValMatch hst ha; rw [hev] at hmt
              obtain ⟨x, hx, haVal⟩ := hmt rfl
              simp only [cast_eq] at haVal
              refine ⟨x, v, levelVal_prepend [⟨i64, v⟩] bvs hx, ?_, ?_⟩
              · rw [hst.lenEq]; exact levelVal_cons_end v bvs
              · rw [← haVal, ← hm.1 hSto]; exact hload
            · exact hOld e he' hcl
        | _ => rw [hev] at he; exact hOld e he hcl
      · dsimp only at he
        split at he
        · rename_i heq; cases heq; exact absurd rfl h64
        · exact hOld e he hcl

private theorem ctxTypes_lookupV {V : Ty → Type} :
    ∀ {Γ : List Ty} {bvs : List ((t : Ty) × V t)} (_ : CtxTypes Γ bvs)
      {i : Nat} {t : Ty}, listGet? Γ i = some t → ∃ v : V t, lookupV bvs t i = some v
  | [], _, .nil, _, _, hg => by cases hg
  | _ :: _, ⟨_, x⟩ :: _, .cons _, 0, _, rfl => ⟨x, castTy_self x⟩
  | _ :: _, _ :: _, .cons h, _ + 1, t, hg => ctxTypes_lookupV h hg

private theorem levelHasTy_lookupV {bvs : List ((t : Ty) × Val t)} {rp₀ : BitVec 64}
    {st : SymState} (hst : SymStateOk bvs rp₀ st) {lvl : Nat} {t : Ty}
    (hty : st.levelHasTy lvl t = true) :
    ∃ x : Val t, lookupV bvs t (bvs.length - 1 - lvl) = some x ∧ lvl < bvs.length ∧
      levelVal bvs lvl = some x := by
  dsimp only [SymState.levelHasTy] at hty
  split at hty <;> rename_i hlt
  · have hlenCtx : st.ctx.length = bvs.length := ctxTypes_length hst.ctxOk
    have hltB : lvl < bvs.length := hlenCtx ▸ hlt
    rw [hlenCtx] at hty
    cases hg : listGet? st.ctx (bvs.length - 1 - lvl) with
    | none => rw [hg] at hty; cases hty
    | some t' =>
        rw [hg] at hty; dsimp only at hty
        cases hdec : tyDecEq t' t with
        | isFalse _ => rw [hdec] at hty; cases hty
        | isTrue heq =>
            subst heq
            obtain ⟨x, hx⟩ := ctxTypes_lookupV hst.ctxOk hg
            refine ⟨x, hx, hltB, ?_⟩
            dsimp only [levelVal]; rw [ite_eq_left hltB]; exact hx
  · cases hty

private theorem symState_findMemLoad_spec {st : SymState} {tgt : Arg K i64}
    {tblBase : BitVec 64} {reqClean : Bool} {lvl : Nat}
    (h : st.memLoadIdx? tgt tblBase reqClean = some lvl) :
    ∃ (idx vLvl : Nat) (e : MemLoadEntry),
      tgt = .var idx ∧ st.toLevel? idx = some vLvl ∧
      st.findMemLoad? vLvl tblBase reqClean = some e ∧ e ∈ st.memLoads ∧
      e.idxLvl = lvl ∧ e.valLvl = vLvl ∧ e.tblBase = tblBase ∧
      (reqClean = true → e.clean = true) ∧ st.levelHasTy e.idxLvl i64 = true := by
  dsimp only [SymState.memLoadIdx?] at h
  cases tgt with
  | imm _ => cases h
  | var idx =>
      dsimp only at h
      cases htl : st.toLevel? idx with
      | none => rw [htl] at h; cases h
      | some vLvl =>
          rw [htl] at h; dsimp only at h
          cases hfl : st.findMemLoad? vLvl tblBase reqClean with
          | none => rw [hfl] at h; cases h
          | some e =>
              rw [hfl] at h; cases h
              have hm := List.mem_of_find?_eq_some hfl
              have hp := List.find?_some (by simpa [SymState.findMemLoad?] using hfl)
              simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hp
              refine ⟨idx, vLvl, e, rfl, htl, hfl, hm, rfl, hp.1.1.1, hp.1.1.2, ?_, hp.2⟩
              intro hr; rcases hp.1.2 with hnc | hc
              · simp [hr] at hnc
              · exact hc

private theorem var_levelVal {bvs : List ((t : Ty) × Val t)} {rp₀ : BitVec 64}
    {st : SymState} (hst : SymStateOk bvs rp₀ st) {t : Ty} {idx lvl : Nat}
    {a' : Arg Val t} (hlvl : st.toLevel? idx = some lvl)
    (hden : denoteArg bvs (.var idx) = some a') :
    levelVal bvs lvl = some a'.val := by
  dsimp only [SymState.toLevel?] at hlvl
  split at hlvl <;> rename_i hlt
  · cases hlvl
    have hb : idx < bvs.length := by rwa [← hst.lenEq]
    have hltL : bvs.length - 1 - idx < bvs.length := by omega
    rw [hst.lenEq]
    dsimp only [levelVal]
    rw [ite_eq_left hltL, show bvs.length - 1 - (bvs.length - 1 - idx) = idx by omega]
    dsimp only [denoteArg] at hden
    cases hl : lookupV bvs t idx with
    | none => rw [hl] at hden; cases hden
    | some _ => rw [hl] at hden; cases hden; rfl
  · cases hlvl

private theorem asConst_eq {bvs : List ((t : Ty) × Val t)} {rp₀ : BitVec 64}
    {sv : SymVal} {v : Val i64} (hm : SymValMatch bvs rp₀ sv i64 v)
    {w : BitVec 64} (hc : sv.asConst? = some w) : v = w := by
  cases sv with
  | const _ => cases hc; simpa using hm rfl
  | alignedConst _ => cases hc; simpa using (hm rfl).1
  | rpOffset _ | taggedAligned _ _ | shl3 _ | stride _ _ | ite _ _ _
  | boolConst _ | cmpUlt _ _ | top => cases hc

private theorem mkAdd_sound {bvs : List ((t : Ty) × Val t)} {rp₀ : BitVec 64}
    {sx sy : SymVal} {vx vy : Val i64}
    (hx : SymValMatch bvs rp₀ sx i64 vx) (hy : SymValMatch bvs rp₀ sy i64 vy) :
    SymValMatch (⟨i64, vx + vy⟩ :: bvs) rp₀ (mkAdd sx sy) i64 (vx + vy) := by
  have hx' := symValMatch_prepend [⟨i64, vx + vy⟩] bvs rp₀ sx i64 vx hx
  have hy' := symValMatch_prepend [⟨i64, vx + vy⟩] bvs rp₀ sy i64 vy hy
  dsimp only [mkAdd]
  split
  · intro _; have h1 := hx rfl; have h2 := hy rfl
    simp only [cast_eq] at h1 h2 ⊢; rw [h1, h2, BitVec.add_assoc]
  · intro _; have h1 := hx rfl; have h2 := hy rfl
    simp only [cast_eq] at h1 h2 ⊢; rw [h1, h2, BitVec.add_comm, BitVec.add_assoc]
  · intro _; obtain ⟨idx, hidx, hvy⟩ := hy' rfl
    have h1 := (hx rfl).1; simp only [cast_eq] at h1 hvy ⊢
    exact ⟨idx, hidx, by rw [h1, hvy]⟩
  · intro _; obtain ⟨idx, hidx, hvy⟩ := hy' rfl
    have h1 := hx rfl; simp only [cast_eq] at h1 hvy ⊢
    exact ⟨idx, hidx, by rw [h1, hvy]⟩
  · intro _; obtain ⟨idx, hidx, hvx⟩ := hx' rfl
    have h2 := (hy rfl).1; simp only [cast_eq] at h2 hvx ⊢
    exact ⟨idx, hidx, by rw [hvx, h2, BitVec.add_comm]⟩
  · intro _; obtain ⟨idx, hidx, hvx⟩ := hx' rfl
    have h2 := hy rfl; simp only [cast_eq] at h2 hvx ⊢
    exact ⟨idx, hidx, by rw [hvx, h2, BitVec.add_comm]⟩
  · cases hax : sx.asConst? <;> cases hay : sy.asConst?
    · exact trivial
    · exact trivial
    · exact trivial
    · intro _; simp only [cast_eq]; rw [asConst_eq hx hax, asConst_eq hy hay]

private theorem mkOrTag_sound {bvs : List ((t : Ty) × Val t)} {rp₀ : BitVec 64}
    {sx sy : SymVal} {vx vy : Val i64}
    (hx : SymValMatch bvs rp₀ sx i64 vx) (hy : SymValMatch bvs rp₀ sy i64 vy) :
    SymValMatch (⟨i64, vx ||| vy⟩ :: bvs) rp₀ (mkOrTag sx sy) i64 (vx ||| vy) := by
  dsimp only [mkOrTag]
  split
  · rename_i w tag
    by_cases hu : BitVec.ult tag 8#64 = true
    · rw [ite_eq_left hu]; intro _
      obtain ⟨hvx, hal⟩ := hx rfl
      have hvy := hy rfl
      simp only [cast_eq] at hvx hvy ⊢
      exact ⟨by rw [hvx, hvy], hal, of_decide_eq_true hu⟩
    · rw [ite_eq_right (by simpa using hu)]; intro _
      obtain ⟨hvx, _⟩ := hx rfl
      have hvy := hy rfl
      simp only [cast_eq] at hvx hvy ⊢
      rw [hvx, hvy]
  · rename_i tag w
    by_cases hu : BitVec.ult tag 8#64 = true
    · rw [ite_eq_left hu]; intro _
      obtain ⟨hvy, hal⟩ := hy rfl
      have hvx := hx rfl
      simp only [cast_eq] at hvx hvy ⊢
      exact ⟨by rw [hvx, hvy, BitVec.or_comm], hal, of_decide_eq_true hu⟩
    · rw [ite_eq_right (by simpa using hu)]; intro _
      obtain ⟨hvy, _⟩ := hy rfl
      have hvx := hx rfl
      simp only [cast_eq] at hvx hvy ⊢
      rw [hvx, hvy]
  · intro _; have h1 := hx rfl; have h2 := hy rfl; simp only [cast_eq] at h1 h2 ⊢; rw [h1, h2]
  · exact trivial

private theorem mkUntag_sound {bvs : List ((t : Ty) × Val t)} {rp₀ : BitVec 64}
    {sx sy : SymVal} {vx vy : Val i64}
    (hx : SymValMatch bvs rp₀ sx i64 vx) (hy : SymValMatch bvs rp₀ sy i64 vy) :
    SymValMatch (⟨i64, vx &&& vy⟩ :: bvs) rp₀ (mkUntag sx sy) i64 (vx &&& vy) := by
  dsimp only [mkUntag]
  split
  · rename_i w tag m
    by_cases hm : m = ~~~7#64
    · subst hm; simp only [beq_self_eq_true, ↓reduceIte]; intro _
      obtain ⟨hvx, hal, ht⟩ := hx rfl
      have hvy := hy rfl
      simp only [cast_eq] at hvx hvy ⊢
      rw [hvx, hvy, bv64_untag_aligned hal ht]
      exact ⟨rfl, hal⟩
    · simp only [beq_false_of_ne hm, Bool.false_eq_true, ↓reduceIte]; exact trivial
  · rename_i m w tag
    by_cases hm : m = ~~~7#64
    · subst hm; simp only [beq_self_eq_true, ↓reduceIte]; intro _
      obtain ⟨hvy, hal, ht⟩ := hy rfl
      have hvx := hx rfl
      simp only [cast_eq] at hvx hvy ⊢
      rw [hvx, hvy, BitVec.and_comm, bv64_untag_aligned hal ht]
      exact ⟨rfl, hal⟩
    · simp only [beq_false_of_ne hm, Bool.false_eq_true, ↓reduceIte]; exact trivial
  · intro _; have h1 := hx rfl; have h2 := hy rfl; simp only [cast_eq] at h1 h2 ⊢; rw [h1, h2]
  · intro _; have h1 := (hx rfl).1; have h2 := hy rfl
    simp only [cast_eq] at h1 h2 ⊢; rw [h1, h2]
  · intro _; have h1 := hx rfl; have h2 := (hy rfl).1
    simp only [cast_eq] at h1 h2 ⊢; rw [h1, h2]
  · exact trivial

private theorem symEvalOp_top_step {ts : List Ty} (op : Op K ts) {st : SymState}
    {bvs : List ((t : Ty) × Val t)} {rp₀ : BitVec 64}
    {args' : Tup (Arg Val) op.sig}
    (hst : SymStateOk bvs rp₀ st)
    (htop : symEvalOp st op = List.replicate ts.length .top)
    {P₁ P₂ : Tup Val ts → Prop}
    (hstep : ∀ r, P₁ r → SymStateOk (pushTup r bvs) rp₀ (st.pushRes ts (symEvalOp st op)) → P₂ r)
    (hop : (⟨op.code, args'⟩ : Op Val ts).wp P₁) :
    (⟨op.code, args'⟩ : Op Val ts).wp P₂ := by
  apply Op.wp_mono (fun r hr => ?_) hop
  have hok := symStateOk_pushTop (pushTup r []) ts hst (pushTup_length r [])
    (by rw [← pushTup_append r [] bvs]; exact CtxTypes.push r hst.ctxOk)
  rw [← pushTup_append r [] bvs, ← htop] at hok
  exact hstep r hr hok

private theorem symEvalOp_wp_mono {ts : List Ty} (op : Op K ts) {st : SymState}
    {bvs : List ((t : Ty) × Val t)} {rp₀ : BitVec 64}
    {args' : Tup (Arg Val) op.sig}
    (hst : SymStateOk bvs rp₀ st)
    (hargs : denoteArgs bvs op.args = some args')
    {P₁ P₂ : Tup Val ts → Prop}
    (hstep : ∀ r, P₁ r → SymStateOk (pushTup r bvs) rp₀ (st.pushRes ts (symEvalOp st op)) → P₂ r)
    (hop : (⟨op.code, args'⟩ : Op Val ts).wp P₁) :
    (⟨op.code, args'⟩ : Op Val ts).wp P₂ := by
  rcases op with ⟨code, args⟩
  cases code with
  | copy t =>
      cases t with
      | bits n =>
          by_cases h64 : n = 64
          · subst h64
            rcases args with ⟨a, ⟨⟩⟩; rcases args' with ⟨a', ⟨⟩⟩
            dsimp only [denoteArgs] at hargs
            cases ha : denoteArg bvs a <;> rw [ha] at hargs; · cases hargs
            cases hargs
            dsimp only [Op.wp, OpCode.wp, vals] at hop ⊢
            apply hstep (a'.val, ()) hop
            dsimp only [symEvalOp, symEvalOpCode]; simp only [beq_self_eq_true, ↓reduceIte]
            exact symStateOk_cons (t := i64) a'.val _ hst
              (symValMatch_prepend [⟨i64, a'.val⟩] bvs rp₀ _ _ _ (evalArg_symValMatch hst ha))
          · exact symEvalOp_top_step ⟨.copy (.bits n), args⟩ hst
              (by rcases args with ⟨_, ⟨⟩⟩; dsimp only [symEvalOp, symEvalOpCode]; simp [h64])
              hstep hop
      | bool =>
          rcases args with ⟨a, ⟨⟩⟩; rcases args' with ⟨a', ⟨⟩⟩
          dsimp only [denoteArgs] at hargs
          cases ha : denoteArg bvs a <;> rw [ha] at hargs; · cases hargs
          cases hargs
          dsimp only [Op.wp, OpCode.wp, vals] at hop ⊢
          apply hstep (a'.val, ()) hop
          exact symStateOk_cons (t := .bool) a'.val _ hst
            (symValMatch_prepend [⟨.bool, a'.val⟩] bvs rp₀ _ _ _ (evalArg_symValMatch hst ha))
      | float _ | pair _ _ =>
          exact symEvalOp_top_step ⟨.copy _, args⟩ hst rfl hstep hop
  | not t =>
      cases t with
      | bits n =>
          by_cases h64 : n = 64
          · subst h64
            rcases args with ⟨a, ⟨⟩⟩; rcases args' with ⟨a', ⟨⟩⟩
            dsimp only [denoteArgs] at hargs
            cases ha : denoteArg bvs a <;> rw [ha] at hargs; · cases hargs
            cases hargs
            dsimp only [Op.wp, OpCode.wp, vals, lift1] at hop ⊢
            apply hstep _ hop
            have hma := evalArg_symValMatch hst ha
            dsimp only [symEvalOp, symEvalOpCode]; simp only [beq_self_eq_true, ↓reduceIte]
            cases hc : (st.evalArg a).asConst? with
            | none => exact symStateOk_cons (t := i64) _ _ hst trivial
            | some _ => exact symStateOk_cons (t := i64) _ _ hst (fun _ => by
                simp only [cast_eq]; rw [asConst_eq hma hc])
          · exact symEvalOp_top_step ⟨.not (.bits n), args⟩ hst
              (by rcases args with ⟨_, ⟨⟩⟩; dsimp only [symEvalOp, symEvalOpCode]; simp [h64])
              hstep hop
      | _ => exact symEvalOp_top_step ⟨.not _, args⟩ hst rfl hstep hop
  | add t =>
      cases t with
      | bits n =>
          by_cases h64 : n = 64
          · subst h64
            rcases args with ⟨a, b, ⟨⟩⟩; rcases args' with ⟨a', b', ⟨⟩⟩
            dsimp only [denoteArgs] at hargs
            cases ha : denoteArg bvs a <;> rw [ha] at hargs; · cases hargs
            cases hb : denoteArg bvs b <;> rw [hb] at hargs; · cases hargs
            cases hargs
            dsimp only [Op.wp, OpCode.wp, vals, lift2, Ty.hasFloat] at hop ⊢
            apply hstep _ hop
            dsimp only [symEvalOp, symEvalOpCode]; simp only [beq_self_eq_true, ↓reduceIte]
            exact symStateOk_cons (t := i64) _ _ hst
              (mkAdd_sound (evalArg_symValMatch hst ha) (evalArg_symValMatch hst hb))
          · exact symEvalOp_top_step ⟨.add (.bits n), args⟩ hst
              (by rcases args with ⟨_, _, ⟨⟩⟩; dsimp only [symEvalOp, symEvalOpCode]; simp [h64])
              hstep hop
      | _ => exact symEvalOp_top_step ⟨.add _, args⟩ hst rfl hstep hop
  | sub t =>
      cases t with
      | bits n =>
          by_cases h64 : n = 64
          · subst h64
            rcases args with ⟨a, b, ⟨⟩⟩; rcases args' with ⟨a', b', ⟨⟩⟩
            dsimp only [denoteArgs] at hargs
            cases ha : denoteArg bvs a <;> rw [ha] at hargs; · cases hargs
            cases hb : denoteArg bvs b <;> rw [hb] at hargs; · cases hargs
            cases hargs
            dsimp only [Op.wp, OpCode.wp, vals, lift2, Ty.hasFloat] at hop ⊢
            apply hstep _ hop
            have hma := evalArg_symValMatch hst ha
            have hmb := evalArg_symValMatch hst hb
            dsimp only [symEvalOp, symEvalOpCode]; simp only [beq_self_eq_true, ↓reduceIte]
            cases hca : (st.evalArg a).asConst? <;> cases hcb : (st.evalArg b).asConst?
            · exact symStateOk_cons (t := i64) _ _ hst trivial
            · exact symStateOk_cons (t := i64) _ _ hst trivial
            · exact symStateOk_cons (t := i64) _ _ hst trivial
            · exact symStateOk_cons (t := i64) _ _ hst (fun _ => by
                simp only [cast_eq]; rw [asConst_eq hma hca, asConst_eq hmb hcb])
          · exact symEvalOp_top_step ⟨.sub (.bits n), args⟩ hst
              (by rcases args with ⟨_, _, ⟨⟩⟩; dsimp only [symEvalOp, symEvalOpCode]; simp [h64])
              hstep hop
      | _ => exact symEvalOp_top_step ⟨.sub _, args⟩ hst rfl hstep hop
  | or t =>
      cases t with
      | bits n =>
          by_cases h64 : n = 64
          · subst h64
            rcases args with ⟨a, b, ⟨⟩⟩; rcases args' with ⟨a', b', ⟨⟩⟩
            dsimp only [denoteArgs] at hargs
            cases ha : denoteArg bvs a <;> rw [ha] at hargs; · cases hargs
            cases hb : denoteArg bvs b <;> rw [hb] at hargs; · cases hargs
            cases hargs
            dsimp only [Op.wp, OpCode.wp, vals, lift2] at hop ⊢
            apply hstep _ hop
            dsimp only [symEvalOp, symEvalOpCode]; simp only [beq_self_eq_true, ↓reduceIte]
            exact symStateOk_cons (t := i64) _ _ hst
              (mkOrTag_sound (evalArg_symValMatch hst ha) (evalArg_symValMatch hst hb))
          · exact symEvalOp_top_step ⟨.or (.bits n), args⟩ hst
              (by rcases args with ⟨_, _, ⟨⟩⟩; dsimp only [symEvalOp, symEvalOpCode]; simp [h64])
              hstep hop
      | _ => exact symEvalOp_top_step ⟨.or _, args⟩ hst rfl hstep hop
  | and t =>
      cases t with
      | bits n =>
          by_cases h64 : n = 64
          · subst h64
            rcases args with ⟨a, b, ⟨⟩⟩; rcases args' with ⟨a', b', ⟨⟩⟩
            dsimp only [denoteArgs] at hargs
            cases ha : denoteArg bvs a <;> rw [ha] at hargs; · cases hargs
            cases hb : denoteArg bvs b <;> rw [hb] at hargs; · cases hargs
            cases hargs
            dsimp only [Op.wp, OpCode.wp, vals, lift2] at hop ⊢
            apply hstep _ hop
            dsimp only [symEvalOp, symEvalOpCode]; simp only [beq_self_eq_true, ↓reduceIte]
            exact symStateOk_cons (t := i64) _ _ hst
              (mkUntag_sound (evalArg_symValMatch hst ha) (evalArg_symValMatch hst hb))
          · exact symEvalOp_top_step ⟨.and (.bits n), args⟩ hst
              (by rcases args with ⟨_, _, ⟨⟩⟩; dsimp only [symEvalOp, symEvalOpCode]; simp [h64])
              hstep hop
      | _ => exact symEvalOp_top_step ⟨.and _, args⟩ hst rfl hstep hop
  | shl t =>
      cases t with
      | bits n =>
          by_cases h64 : n = 64
          · subst h64
            rcases args with ⟨a, b, ⟨⟩⟩; rcases args' with ⟨a', b', ⟨⟩⟩
            dsimp only [denoteArgs] at hargs
            cases ha : denoteArg bvs a <;> rw [ha] at hargs; · cases hargs
            cases hb : denoteArg bvs b <;> rw [hb] at hargs; · cases hargs
            cases hargs
            dsimp only [Op.wp, OpCode.wp, vals, lift2, Ty.hasFloat] at hop ⊢
            apply hstep _ hop
            have hmb := evalArg_symValMatch hst hb
            dsimp only [symEvalOp, symEvalOpCode]; simp only [beq_self_eq_true, ↓reduceIte]
            split
            · rename_i idx heq
              cases hl : st.toLevel? idx with
              | none => exact symStateOk_cons (t := i64) _ _ hst trivial
              | some lvl =>
                  by_cases hty : st.levelHasTy lvl i64 = true
                  · simp only [hty, ↓reduceIte]
                    apply symStateOk_cons (t := i64) _ _ hst
                    intro _; simp only [cast_eq]
                    refine ⟨a'.val, levelVal_prepend [⟨i64, _⟩] bvs (var_levelVal hst hl ha), ?_⟩
                    rw [asConst_eq hmb heq, bv64_shl3_eq_mul8]
                  · simp only [hty, Bool.false_eq_true, ↓reduceIte]
                    exact symStateOk_cons (t := i64) _ _ hst trivial
            · exact symStateOk_cons (t := i64) _ _ hst trivial
          · exact symEvalOp_top_step ⟨.shl (.bits n), args⟩ hst
              (by rcases args with ⟨_, _, ⟨⟩⟩; dsimp only [symEvalOp, symEvalOpCode]; simp [h64])
              hstep hop
      | _ => exact symEvalOp_top_step ⟨.shl _, args⟩ hst rfl hstep hop
  | mul t =>
      cases t with
      | bits n =>
          by_cases h64 : n = 64
          · subst h64
            rcases args with ⟨a, b, ⟨⟩⟩; rcases args' with ⟨a', b', ⟨⟩⟩
            dsimp only [denoteArgs] at hargs
            cases ha : denoteArg bvs a <;> rw [ha] at hargs; · cases hargs
            cases hb : denoteArg bvs b <;> rw [hb] at hargs; · cases hargs
            cases hargs
            dsimp only [Op.wp, OpCode.wp, vals, lift2, Ty.hasFloat] at hop ⊢
            apply hstep _ hop
            have hma := evalArg_symValMatch hst ha
            have hmb := evalArg_symValMatch hst hb
            dsimp only [symEvalOp, symEvalOpCode]; simp only [beq_self_eq_true, ↓reduceIte]
            split
            · rename_i idx heqB
              cases hl : st.toLevel? idx with
              | none => exact symStateOk_cons (t := i64) _ _ hst trivial
              | some lvl =>
                  by_cases hty : st.levelHasTy lvl i64 = true
                  · simp only [hty, ↓reduceIte]
                    apply symStateOk_cons (t := i64) _ _ hst
                    intro _; simp only [cast_eq]
                    refine ⟨a'.val, levelVal_prepend [⟨i64, _⟩] bvs (var_levelVal hst hl ha), ?_⟩
                    rw [asConst_eq hmb heqB, bv64_mul8_eq_ofNat]
                  · simp only [hty, Bool.false_eq_true, ↓reduceIte]
                    exact symStateOk_cons (t := i64) _ _ hst trivial
            · rename_i idx heqA hnot1
              cases hl : st.toLevel? idx with
              | none => exact symStateOk_cons (t := i64) _ _ hst trivial
              | some lvl =>
                  by_cases hty : st.levelHasTy lvl i64 = true
                  · simp only [hty, ↓reduceIte]
                    apply symStateOk_cons (t := i64) _ _ hst
                    intro _; simp only [cast_eq]
                    refine ⟨b'.val, levelVal_prepend [⟨i64, _⟩] bvs (var_levelVal hst hl hb), ?_⟩
                    rw [asConst_eq hma heqA, BitVec.mul_comm, bv64_mul8_eq_ofNat]
                  · simp only [hty, Bool.false_eq_true, ↓reduceIte]
                    exact symStateOk_cons (t := i64) _ _ hst trivial
            · rename_i x y heqA heqB
              refine symStateOk_cons (t := i64) _ _ hst (fun _ => ?_)
              simp only [cast_eq]; rw [asConst_eq hma heqA, asConst_eq hmb heqB, BitVec.mul_comm]
            · exact symStateOk_cons (t := i64) _ _ hst trivial
          · exact symEvalOp_top_step ⟨.mul (.bits n), args⟩ hst
              (by rcases args with ⟨_, _, ⟨⟩⟩; dsimp only [symEvalOp, symEvalOpCode]; simp [h64])
              hstep hop
      | _ => exact symEvalOp_top_step ⟨.mul _, args⟩ hst rfl hstep hop
  | select t =>
      cases t with
      | bits n =>
          by_cases h64 : n = 64
          · subst h64
            rcases args with ⟨c, tA, eA, ⟨⟩⟩; rcases args' with ⟨c', tA', eA', ⟨⟩⟩
            dsimp only [denoteArgs] at hargs
            cases hc : denoteArg bvs c <;> rw [hc] at hargs; · cases hargs
            cases ht : denoteArg bvs tA <;> rw [ht] at hargs; · cases hargs
            cases he : denoteArg bvs eA <;> rw [he] at hargs; · cases hargs
            cases hargs
            dsimp only [Op.wp, OpCode.wp, vals] at hop ⊢
            apply hstep _ hop
            have hmt := symValMatch_prepend [⟨i64, if c'.val then tA'.val else eA'.val⟩]
              bvs rp₀ _ _ _ (evalArg_symValMatch hst ht)
            have hme := symValMatch_prepend [⟨i64, if c'.val then tA'.val else eA'.val⟩]
              bvs rp₀ _ _ _ (evalArg_symValMatch hst he)
            dsimp only [symEvalOp, symEvalOpCode]; simp only [beq_self_eq_true, ↓reduceIte]
            cases c with
            | imm cb =>
                cases hc
                cases cb
                · exact symStateOk_cons (t := i64) _ _ hst hme
                · exact symStateOk_cons (t := i64) _ _ hst hmt
            | var idx =>
                dsimp only
                cases hl : st.toLevel? idx with
                | none => exact symStateOk_cons (t := i64) _ _ hst trivial
                | some lvl =>
                    by_cases hty : st.levelHasTy lvl .bool = true
                    · simp only [hty, ↓reduceIte]
                      apply symStateOk_cons (t := i64) _ _ hst
                      intro _; simp only [cast_eq]
                      refine ⟨c'.val, levelVal_prepend [⟨i64, _⟩] bvs (var_levelVal hst hl hc), ?_⟩
                      constructor
                      · intro htr; simpa [htr] using hmt
                      · intro hfl; simpa [hfl] using hme
                    · simp only [hty, Bool.false_eq_true, ↓reduceIte]
                      exact symStateOk_cons (t := i64) _ _ hst trivial
          · exact symEvalOp_top_step ⟨.select (.bits n), args⟩ hst
              (by rcases args with ⟨_, _, _, ⟨⟩⟩; dsimp only [symEvalOp, symEvalOpCode]; simp [h64])
              hstep hop
      | _ => exact symEvalOp_top_step ⟨.select _, args⟩ hst rfl hstep hop
  | cmp cmpOp t _ h =>
      subst h
      cases cmpOp with
      | ult =>
          cases t with
          | bits n =>
              by_cases h64 : n = 64
              · subst h64
                rcases args with ⟨a, b, ⟨⟩⟩; rcases args' with ⟨a', b', ⟨⟩⟩
                dsimp only [denoteArgs] at hargs
                cases ha : denoteArg bvs a <;> rw [ha] at hargs; · cases hargs
                cases hb : denoteArg bvs b <;> rw [hb] at hargs; · cases hargs
                cases hargs
                dsimp only [Op.wp, OpCode.wp, vals, liftCmp, CmpOp.evalBits, Ty.hasFloat] at hop ⊢
                apply hstep _ hop
                have hmb := evalArg_symValMatch hst hb
                dsimp only [symEvalOp, symEvalOpCode]; simp only [beq_self_eq_true, ↓reduceIte]
                split
                · rename_i idx bound heq
                  cases hl : st.toLevel? idx with
                  | none => exact symStateOk_cons (t := .bool) _ _ hst trivial
                  | some lvl =>
                      by_cases hty : st.levelHasTy lvl i64 = true
                      · simp only [hty, ↓reduceIte]
                        apply symStateOk_cons (t := .bool) _ _ hst
                        intro _; simp only [cast_eq]
                        refine ⟨a'.val,
                          levelVal_prepend [⟨.bool, _⟩] bvs (var_levelVal hst hl ha), ?_⟩
                        rw [asConst_eq hmb heq]
                      · simp only [hty, Bool.false_eq_true, ↓reduceIte]
                        exact symStateOk_cons (t := .bool) _ _ hst trivial
                · exact symStateOk_cons (t := .bool) _ _ hst trivial
              · exact symEvalOp_top_step ⟨.cmp .ult (.bits n), args⟩ hst
                  (by rcases args with ⟨_, _, ⟨⟩⟩
                      dsimp only [symEvalOp, symEvalOpCode]; simp [h64])
                  hstep hop
          | _ => exact symEvalOp_top_step ⟨.cmp .ult _, args⟩ hst rfl hstep hop
      | _ =>
          exact symEvalOp_top_step ⟨.cmp _ _, args⟩ hst
            (by cases t <;> rfl) hstep hop
  | _ =>
      exact symEvalOp_top_step ⟨_, args⟩ hst rfl hstep hop

private theorem pushCondFact_sound {bvs : List ((t : Ty) × Val t)} {rp₀ : BitVec 64}
    {st : SymState} (hst : SymStateOk bvs rp₀ st) {c : Arg K .bool} {c' : Arg Val .bool}
    (hc : denoteArg bvs c = some c') (taken : Bool) (hval : c'.val = taken) :
    SymStateOk bvs rp₀ (st.pushCondFact c taken) := by
  dsimp only [SymState.pushCondFact]
  cases taken
  · exact hst
  · cases c with
    | imm _ => exact hst
    | var idx =>
        simp only [↓reduceIte]
        have hmv := evalArg_symValMatch hst hc
        dsimp only [SymState.evalArg] at hmv
        cases hgs : st.getSym idx with
        | cmpUlt lvl bound =>
            refine ⟨hst.lenEq, hst.ctxOk, hst.valsOk, ?_⟩
            intro f hf
            rcases List.mem_cons.1 hf with rfl | hf
            · rw [hgs] at hmv
              obtain ⟨x, hx, hult⟩ := hmv rfl
              rw [hval] at hult
              exact ⟨x, hx, of_decide_eq_true hult.symm⟩
            · exact hst.factsOk f hf
        | _ => exact hst

/-! ## §3. Edge & Block Soundness (`liftEdge_wp`, `liftBlock_wp`) -/

@[expose] def retEnvQ (Ψ : CodeSpec) : Post RegionAbi.retEnvelope.retSig :=
  fun (nextPc, sp, rp, rv, r1, r2, r3, ()) m =>
    Ψ nextPc ⟨⟨sp, rp, rv, r1, r2, r3⟩, m⟩

@[expose] def retContPost (dualRet : Bool) (Ψ : CodeSpec) (rp₀ : BitVec 64) :
    Post (RegionAbi.contified dualRet).retSig :=
  match dualRet with
  | true => fun (isAlt, sp, rp, rv, r1, r2, r3, ()) m =>
      Ψ (if isAlt then rp₀ + 8#64 else rp₀) ⟨⟨sp, rp, rv, r1, r2, r3⟩, m⟩
  | false => fun (sp, rp, rv, r1, r2, r3, ()) m =>
      Ψ rp₀ ⟨⟨sp, rp, rv, r1, r2, r3⟩, m⟩

@[expose] def haltXPost (H : HaltPost) : XPost :=
  fun sym cs xs m =>
    sym = haltSym ∧ ∃ (heq : cs = [i64]), H (heq ▸ xs).1 m

@[expose] def regionRetPost (abi : RegionAbi) (Ψ_ret : CodeSpec) (rp₀ : BitVec 64) :
    Post abi.retSig :=
  match abi with
  | .retEnvelope => retEnvQ Ψ_ret
  | .contified dualRet => retContPost dualRet Ψ_ret rp₀

@[expose] def LsMatch (pcs : List (BitVec 64)) (ls : List ((ts : List Ty) × Cont ts))
    (Pred : CodeSpec) : Prop :=
  ∀ pc idx, findLabelIdx pcs pc = some idx →
    ∃ J, lookupL ls regSig idx = some J ∧
      ∀ r : Regs, ∀ m : Mem 64, Pred pc ⟨r, m⟩ → J r.toRegsV.toTup m

theorem lsMatch_nil (Pred : CodeSpec) : LsMatch [] [] Pred :=
  fun _ _ h => by cases h

private theorem castListTy_self_local (ts : List Ty) (l : Cont ts) :
    castListTy ts ts l = some l := by
  dsimp only [castListTy]
  cases h : listTyDecEq ts ts with
  | isFalse hne => exact absurd rfl hne
  | isTrue heq =>
      have h' : heq = rfl := rfl
      rw [h']

theorem lsMatch_cons {pc : BitVec 64} {J : Cont regSig}
    {pcs : List (BitVec 64)} {ls : List ((ts : List Ty) × Cont ts)} {Pred : CodeSpec}
    (hJ : ∀ r : Regs, ∀ m : Mem 64, Pred pc ⟨r, m⟩ → J r.toRegsV.toTup m)
    (hls : LsMatch pcs ls Pred) :
    LsMatch (pc :: pcs) (⟨regSig, J⟩ :: ls) Pred := by
  intro tgt idx hf
  dsimp only [findLabelIdx] at hf
  by_cases heq : pc = tgt
  · subst heq
    simp only [beq_self_eq_true, ↓reduceIte] at hf
    cases hf
    refine ⟨J, ?_, hJ⟩
    dsimp only [lookupL, listGet?]
    exact castListTy_self_local regSig J
  · simp only [beq_false_of_ne heq, Bool.false_eq_true, ↓reduceIte] at hf
    cases hf' : findLabelIdx pcs tgt with
    | none => rw [hf'] at hf; cases hf
    | some idx' =>
        rw [hf'] at hf; cases hf
        exact hls tgt idx' hf'

theorem lowerJumpTo_wp {rs : List Ty} {Γ : Env} {Q : Post rs} {X : XPost}
    {pcs : List (BitVec 64)} {ls : List ((ts : List Ty) × Cont ts)} {Pred : CodeSpec}
    (hls : LsMatch pcs ls Pred)
    {vs : List ((t : Ty) × Val t)} {targetPc : BitVec 64} {j : Nat}
    (hj : findLabelIdx pcs targetPc = some j)
    {nxt : RegsExpr K} {nxt' : RegsExpr Val} (hnxt : denoteRegsExpr vs nxt = some nxt')
    {m : Mem 64} (hP : Pred targetPc ⟨nxt'.eval, m⟩) :
    wp Γ Q X (denote Val Cont (lowerJumpTo pcs targetPc nxt) vs ls) m := by
  dsimp only [lowerJumpTo]
  rw [hj]
  obtain ⟨args', hargs', hvals⟩ := denoteRegsExpr_toTup hnxt
  obtain ⟨J, hJ, hJP⟩ := hls targetPc j hj
  dsimp only [denote]
  rw [hJ, hargs']
  dsimp only [wp]
  rw [hvals]
  exact hJP nxt'.eval m hP

theorem lowerJumpTo_base_wp {rs : List Ty} {Γ : Env} {Q : Post rs} {X : XPost}
    {pcs : List (BitVec 64)} {ls : List ((ts : List Ty) × Cont ts)} {Pred : CodeSpec}
    (hls : LsMatch pcs ls Pred) (targetPc : BitVec 64)
    (hIs : (findLabelIdx pcs targetPc).isSome = true) (r : Regs) (m : Mem 64)
    (hP : Pred targetPc ⟨r, m⟩) :
    wp Γ Q X (denote Val Cont
      (lowerJumpTo pcs targetPc ⟨.var 5, .var 4, .var 3, .var 2, .var 1, .var 0⟩)
      (pushTup r.toRegsV.toTup []) ls) m := by
  rcases Option.isSome_iff_exists.1 hIs with ⟨j, hj⟩
  dsimp only [lowerJumpTo]; rw [hj]
  obtain ⟨args', hargs', hvals⟩ := denoteArgs_baseRegs r.toRegsV.toTup []
  obtain ⟨J, hJ, hJP⟩ := hls targetPc j hj
  dsimp only [denote]; rw [hJ, hargs']; dsimp only [wp]; rw [hvals]
  exact hJP r m hP

private theorem levelVal_lookupV {bvs vsTail : List ((t : Ty) × Val t)} {rp₀ : BitVec 64}
    {st : SymState} (hst : SymStateOk bvs rp₀ st) {t : Ty} {lvl : Nat} {x : Val t}
    (hl : levelVal bvs lvl = some x) :
    lookupV (bvs ++ vsTail) t (st.env.length - 1 - lvl) = some x := by
  dsimp only [levelVal] at hl
  split at hl <;> rename_i hlt
  · rw [hst.lenEq]
    dsimp only [lookupV] at hl ⊢
    rw [listGet?_append_left bvs vsTail (by omega)]
    exact hl
  · cases hl

private theorem levelVal_lt_len {bvs : List ((t : Ty) × Val t)} {t : Ty} {lvl : Nat} {x : Val t}
    (hl : levelVal bvs lvl = some x) : lvl < bvs.length := by
  dsimp only [levelVal] at hl
  split at hl <;> rename_i hlt
  · exact hlt
  · cases hl

private theorem lookupV_extra_shift {V : Ty → Type} (extra bvs vsTail : List ((t : Ty) × V t))
    {t : Ty} {i : Nat} {v : V t} (hlt : i < bvs.length)
    (hl : lookupV bvs t i = some v) :
    lookupV (extra ++ bvs ++ vsTail) t (i + extra.length) = some v := by
  rw [List.append_assoc, lookupV]
  rw [Nat.add_comm i extra.length, listGet?_append_skip, listGet?_append_left bvs vsTail hlt]
  exact hl

private theorem checkStrideTargets_mem_isSome {pcs : List (BitVec 64)} {base : BitVec 64} :
    ∀ (k : Nat) (targets : List (BitVec 64)) (i : Nat),
      checkStrideTargets pcs base k targets = true →
      k ≤ i → i < k + targets.length →
      (findLabelIdx pcs (base + BitVec.ofNat 64 (8 * i))).isSome = true
  | _, [], _, _, hlo, hhi => by simp at hhi; omega
  | k, t :: ts, i, hchk, hlo, hhi => by
      dsimp only [checkStrideTargets] at hchk
      simp only [Bool.and_eq_true] at hchk
      by_cases hi : i = k
      · subst hi
        have ht : t = base + BitVec.ofNat 64 (8 * i) := of_decide_eq_true hchk.1.1
        rw [← ht]; exact hchk.1.2
      · exact checkStrideTargets_mem_isSome (k + 1) ts i hchk.2 (by omega)
          (by simp [List.length_cons] at hhi ⊢; omega)

private theorem checkStrideTargets_all_isSome (pcs : List (BitVec 64)) (base : BitVec 64) :
    ∀ (k : Nat) (targets : List (BitVec 64)),
      checkStrideTargets pcs base k targets = true →
      targets.all (fun p => (findLabelIdx pcs p).isSome) = true
  | _, [], _ => rfl
  | k, _ :: ts, hchk => by
      dsimp only [checkStrideTargets] at hchk
      simp only [Bool.and_eq_true] at hchk
      simp only [List.all_cons, Bool.and_eq_true]
      exact ⟨hchk.1.2, checkStrideTargets_all_isSome pcs base (k + 1) ts hchk.2⟩

private theorem checkStrideTargets_getElem (pcs : List (BitVec 64)) (base : BitVec 64) :
    ∀ (k : Nat) (targets : List (BitVec 64)) (i : Nat) (hi : i < targets.length),
      checkStrideTargets pcs base k targets = true →
      targets[i]'hi = base + BitVec.ofNat 64 (8 * (k + i))
  | _, [], _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | k, t :: ts, 0, _, hchk => by
      dsimp only [checkStrideTargets] at hchk
      simp only [Bool.and_eq_true] at hchk
      simpa using of_decide_eq_true hchk.1.1
  | k, _ :: ts, i + 1, hi, hchk => by
      dsimp only [checkStrideTargets] at hchk
      simp only [Bool.and_eq_true] at hchk
      have ih := checkStrideTargets_getElem pcs base (k + 1) ts i
        (Nat.lt_of_succ_lt_succ hi) hchk.2
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using ih

private theorem lowerTableCascade_wp {rs : List Ty} {Γ : Env} {Q : Post rs} {X : XPost}
    {pcs : List (BitVec 64)} {ls : List ((ts : List Ty) × Cont ts)} {Pred : CodeSpec}
    (hls : LsMatch pcs ls Pred)
    {bvs vsTail : List ((t : Ty) × Val t)}
    {idxVar : Nat} {x : Val i64}
    (hlook : lookupV bvs i64 idxVar = some x)
    (hltIdx : idxVar < bvs.length)
    {nxt : RegsExpr K} {nxt' : RegsExpr Val}
    (hnxt : denoteRegsExpr (bvs ++ vsTail) nxt = some nxt')
    {m : Mem 64} :
    ∀ (k : Nat) (extra : List ((t : Ty) × Val t)) (targets : List (BitVec 64)),
      targets ≠ [] →
      targets.all (fun p => (findLabelIdx pcs p).isSome) = true →
      k ≤ x.toNat →
      (hkLt : x.toNat - k < targets.length) →
      Pred (targets[x.toNat - k]'hkLt) ⟨nxt'.eval, m⟩ →
      wp Γ Q X (denote Val Cont (lowerStrideCascade pcs idxVar nxt k extra.length targets)
        (extra ++ bvs ++ vsTail) ls) m
  | _, _, [], hne, _, _, _, _ => absurd rfl hne
  | k, extra, [lastPc], _, hchk, hlo, hkLt, hP => by
      have hsub : x.toNat - k = 0 := by simp at hkLt; omega
      simp only [List.all_cons, List.all_nil, Bool.and_true] at hchk
      rcases Option.isSome_iff_exists.1 hchk with ⟨j, hj⟩
      have hLastEq : ([lastPc][x.toNat - k]'hkLt) = lastPc := by simp [hsub]
      rw [hLastEq] at hP
      dsimp only [lowerStrideCascade]
      have hnxtS : denoteRegsExpr (extra ++ bvs ++ vsTail) (shiftRegsExpr extra.length nxt) =
          some nxt' := by
        rw [List.append_assoc, denoteRegsExpr_shift, hnxt]
      exact lowerJumpTo_wp hls hj hnxtS hP
  | k, extra, tPc :: r0 :: rest, _, hchk, hlo, hkLt, hP => by
      dsimp only [List.all_cons] at hchk
      rcases Bool.and_eq_true_iff.1 hchk with ⟨hchk1, hchk2⟩
      rcases Option.isSome_iff_exists.1 hchk1 with ⟨j, hj⟩
      dsimp only [lowerStrideCascade]
      have hdenV : denoteArg (extra ++ bvs ++ vsTail) (.var (idxVar + extra.length)) =
          some (.var x) := by
        dsimp only [denoteArg]
        rw [lookupV_extra_shift extra bvs vsTail hltIdx hlook]
      dsimp only [denote, op2, denoteArgs]
      rw [hdenV]
      dsimp only [denoteArg, wp, Op.wp, OpCode.wp, vals, liftCmp, CmpOp.evalBits, Ty.hasFloat]
      have hk64 : k < 2 ^ 64 := Nat.lt_of_le_of_lt hlo x.isLt
      constructor
      · intro htr
        have hxEq : x = BitVec.ofNat 64 k := beq_iff_eq.1 htr
        have hnat : x.toNat = k := by rw [hxEq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64]
        rw [show ((tPc :: r0 :: rest)[x.toNat - k]'hkLt) = tPc by simp [hnat]] at hP
        have hnxtS : denoteRegsExpr (⟨.bool, (x == BitVec.ofNat 64 k)⟩ :: (extra ++ bvs ++ vsTail))
            (shiftRegsExpr (extra.length + 1) nxt) = some nxt' := by
          have hlen : (([⟨.bool, (x == BitVec.ofNat 64 k)⟩] :
              List ((t : Ty) × Val t)) ++ extra).length = extra.length + 1 := by simp
          rw [show (⟨.bool, (x == BitVec.ofNat 64 k)⟩ :: (extra ++ bvs ++ vsTail) :
            List ((t : Ty) × Val t)) = ([⟨.bool, (x == BitVec.ofNat 64 k)⟩] ++ extra) ++
              (bvs ++ vsTail) by simp [List.append_assoc], ← hlen, denoteRegsExpr_shift, hnxt]
        exact lowerJumpTo_wp hls hj hnxtS hP
      · intro hfl
        have hne : x ≠ BitVec.ofNat 64 k := fun he => by simp [he] at hfl
        have hnatNe : x.toNat ≠ k := fun he => hne (BitVec.eq_of_toNat_eq
          (by rw [he, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64]))
        have hkLt' : x.toNat - (k + 1) < (r0 :: rest).length := by
          simp [List.length_cons] at hkLt ⊢; omega
        have hRestEq : ((tPc :: r0 :: rest)[x.toNat - k]'hkLt) =
            ((r0 :: rest)[x.toNat - (k + 1)]'hkLt') := by
          have hpos : x.toNat - k ≠ 0 := by omega
          have hsub : x.toNat - k - 1 = x.toNat - (k + 1) := by omega
          simp [List.getElem_cons, hpos, hsub]
        have ih := lowerTableCascade_wp (rs := rs) (Γ := Γ) (Q := Q) (X := X)
          hls hlook hltIdx hnxt (k + 1) (⟨.bool, (x == BitVec.ofNat 64 k)⟩ :: extra)
          (r0 :: rest) (by simp) hchk2 (by omega) hkLt' (hRestEq ▸ hP)
        dsimp only [pushTup, List.length_cons] at ih ⊢; exact ih

private theorem lowerStrideCascade_wp {rs : List Ty} {Γ : Env} {Q : Post rs} {X : XPost}
    {pcs : List (BitVec 64)} {ls : List ((ts : List Ty) × Cont ts)} {Pred : CodeSpec}
    (hls : LsMatch pcs ls Pred)
    {bvs vsTail : List ((t : Ty) × Val t)}
    {idxVar : Nat} {x : Val i64}
    (hlook : lookupV bvs i64 idxVar = some x)
    (hltIdx : idxVar < bvs.length)
    {nxt : RegsExpr K} {nxt' : RegsExpr Val}
    (hnxt : denoteRegsExpr (bvs ++ vsTail) nxt = some nxt')
    {base : BitVec 64} {m : Mem 64}
    (k : Nat) (extra : List ((t : Ty) × Val t)) (targets : List (BitVec 64))
    (hne : targets ≠ [])
    (hchk : checkStrideTargets pcs base k targets = true)
    (hlo : k ≤ x.toNat) (hhi : x.toNat < k + targets.length)
    (hP : Pred (base + BitVec.ofNat 64 (8 * x.toNat)) ⟨nxt'.eval, m⟩) :
    wp Γ Q X (denote Val Cont (lowerStrideCascade pcs idxVar nxt k extra.length targets)
      (extra ++ bvs ++ vsTail) ls) m := by
  have hkLt : x.toNat - k < targets.length := by omega
  have hget := checkStrideTargets_getElem pcs base k targets (x.toNat - k) hkLt hchk
  rw [show k + (x.toNat - k) = x.toNat by omega] at hget
  exact lowerTableCascade_wp hls hlook hltIdx hnxt k extra targets hne
    (checkStrideTargets_all_isSome pcs base k targets hchk) hlo hkLt (hget ▸ hP)

private theorem vals_regsExpr_toTup (e : RegsExpr Val) :
    vals e.toTup = e.eval.toRegsV.toTup := rfl

private theorem denoteArgs_cons_pair {vs : List ((t : Ty) × Val t)} {t : Ty} {ts : List Ty}
    {a : Arg K t} {as : Tup (Arg K) ts} {a' : Arg Val t} {as' : Tup (Arg Val) ts}
    (ha : denoteArg vs a = some a') (has : denoteArgs vs as = some as') :
    denoteArgs (ts := t :: ts) vs (a, as) = some (a', as') := by
  dsimp only [denoteArgs]; rw [ha, has]

private theorem denoteArgs_retEnv {vs : List ((t : Ty) × Val t)} {tgt : Arg K i64}
    {tgt' : Arg Val i64} {nxt : RegsExpr K} {args' : Tup (Arg Val) regSig}
    (ht : denoteArg vs tgt = some tgt') (hn : denoteArgs vs nxt.toTup = some args') :
    denoteArgs (ts := RegionAbi.retEnvelope.retSig) vs
        (tgt, nxt.sp, nxt.rp, nxt.rv, nxt.r1, nxt.r2, nxt.r3, ()) =
      some ((tgt', args') : Tup (Arg Val) RegionAbi.retEnvelope.retSig) := by
  dsimp only [RegionAbi.retSig]
  exact denoteArgs_cons_pair ht hn

private theorem denoteArgs_contRetTrue {vs : List ((t : Ty) × Val t)} (isAlt : Bool)
    {nxt : RegsExpr K} {args' : Tup (Arg Val) regSig}
    (hn : denoteArgs vs nxt.toTup = some args') :
    denoteArgs (ts := (RegionAbi.contified true).retSig) vs (Arg.imm isAlt, nxt.toTup) =
      some ((Arg.imm isAlt, args') : Tup (Arg Val) (RegionAbi.contified true).retSig) := by
  dsimp only [RegionAbi.retSig]
  exact denoteArgs_cons_pair (t := .bool) (a := Arg.imm isAlt) (a' := Arg.imm isAlt) rfl hn

private theorem denoteArgs_baseRegs_false (r : Tup Val (RegionAbi.contified false).retSig)
    (tail : List ((t : Ty) × Val t)) :
    ∃ args', denoteArgs (pushTup r tail)
        (⟨.var 5, .var 4, .var 3, .var 2, .var 1, .var 0⟩ : RegsExpr K).toTup = some args' ∧
      vals args' = (r : Tup Val regSig) :=
  denoteArgs_baseRegs r tail

private theorem denoteArgs_retRegArgs_true (r : Tup Val (RegionAbi.contified true).retSig)
    (tail : List ((t : Ty) × Val t)) :
    ∃ args', ∃ c' : Arg Val .bool,
      denoteArg (pushTup r tail) (.var 6) = some c' ∧
      c'.val = r.1 ∧
      denoteArgs (pushTup r tail)
        (⟨.var 5, .var 4, .var 3, .var 2, .var 1, .var 0⟩ : RegsExpr K).toTup = some args' ∧
      vals args' = r.2 := by
  dsimp only [RegionAbi.retSig] at r
  rcases r with ⟨isAlt, sp, rp, rv, r1, r2, r3, ⟨⟩⟩
  exact denoteArgs_retRegArgs isAlt (sp, rp, rv, r1, r2, r3, ()) tail

private theorem denoteArgs_contRetFalse {vs : List ((t : Ty) × Val t)}
    {nxt : RegsExpr K} {args' : Tup (Arg Val) regSig}
    (hn : denoteArgs vs nxt.toTup = some args') :
    denoteArgs (ts := (RegionAbi.contified false).retSig) vs nxt.toTup =
      some (args' : Tup (Arg Val) (RegionAbi.contified false).retSig) :=
  hn

private theorem retEnvQ_of_eq {Ψ : CodeSpec} {tgt' : Arg Val i64} {args' : Tup (Arg Val) regSig}
    {nxt' : RegsExpr Val} {m : Mem 64}
    (hv : vals args' = nxt'.eval.toRegsV.toTup)
    (h : Ψ tgt'.val ⟨nxt'.eval, m⟩) :
    retEnvQ Ψ (vals ((tgt', args') : Tup (Arg Val) RegionAbi.retEnvelope.retSig)) m := by
  dsimp only [RegionAbi.retSig, vals] at *
  rw [hv]
  exact h

private theorem retContPost_false_of_eq {Ψ : CodeSpec} {rp₀ : BitVec 64}
    {args' : Tup (Arg Val) regSig} {nxt' : RegsExpr Val} {m : Mem 64}
    (hv : vals args' = nxt'.eval.toRegsV.toTup)
    (h : Ψ rp₀ ⟨nxt'.eval, m⟩) :
    retContPost false Ψ rp₀
      (vals (args' : Tup (Arg Val) (RegionAbi.contified false).retSig)) m := by
  dsimp only [RegionAbi.retSig]
  rw [hv]
  exact h

private theorem retContPost_true_of_eq {Ψ : CodeSpec} {rp₀ : BitVec 64} (isAlt : Bool)
    {args' : Tup (Arg Val) regSig} {nxt' : RegsExpr Val} {m : Mem 64}
    (hv : vals args' = nxt'.eval.toRegsV.toTup)
    (h : Ψ (if isAlt then rp₀ + 8#64 else rp₀) ⟨nxt'.eval, m⟩) :
    retContPost true Ψ rp₀
      (vals ((Arg.imm isAlt, args') : Tup (Arg Val) (RegionAbi.contified true).retSig)) m := by
  dsimp only [RegionAbi.retSig, vals] at *
  rw [hv]
  exact h

private theorem lowerGuardedCascade_wp {Γ : Env} {X : XPost} {Ψ_cold Pred : CodeSpec}
    {pcs : List (BitVec 64)} {ls : List ((ts : List Ty) × Cont ts)}
    (hls : LsMatch pcs ls Pred)
    {bvs vsTail : List ((t : Ty) × Val t)}
    {tgt : Arg K i64} {tgt' : Arg Val i64}
    (htgt : denoteArg (bvs ++ vsTail) tgt = some tgt')
    {nxt : RegsExpr K} {nxt' : RegsExpr Val}
    (hnxt : denoteRegsExpr (bvs ++ vsTail) nxt = some nxt')
    {m : Mem 64} :
    ∀ (extra : List ((t : Ty) × Val t)) (hotTargets : List (BitVec 64)),
      hotTargets.all (fun p => (findLabelIdx pcs p).isSome) = true →
      (∀ p ∈ hotTargets, tgt'.val = p → Pred p ⟨nxt'.eval, m⟩) →
      Ψ_cold tgt'.val ⟨nxt'.eval, m⟩ →
      wp Γ (retEnvQ Ψ_cold) X
        (denote Val Cont (lowerGuardedCascade pcs tgt nxt extra.length hotTargets)
          (extra ++ bvs ++ vsTail) ls) m
  | extra, [], _, _, hCold => by
      dsimp only [lowerGuardedCascade, mkRetEnvelope, denote]
      have htgtS : denoteArg (extra ++ bvs ++ vsTail) (shiftArg extra.length tgt) = some tgt' := by
        rw [List.append_assoc, denoteArg_shift, htgt]
      have hnxtS : denoteRegsExpr (extra ++ bvs ++ vsTail) (shiftRegsExpr extra.length nxt) =
          some nxt' := by
        rw [List.append_assoc, denoteRegsExpr_shift, hnxt]
      obtain ⟨args', hargs', hvals⟩ := denoteRegsExpr_toTup hnxtS
      rw [denoteArgs_retEnv htgtS hargs']
      dsimp only [wp]
      exact retEnvQ_of_eq hvals hCold
  | extra, hPc :: rest, hchk, hPred, hCold => by
      simp only [List.all_cons, Bool.and_eq_true] at hchk
      rcases Option.isSome_iff_exists.1 hchk.1 with ⟨j, hj⟩
      have htgtS : denoteArg (extra ++ bvs ++ vsTail) (shiftArg extra.length tgt) = some tgt' := by
        rw [List.append_assoc, denoteArg_shift, htgt]
      dsimp only [lowerGuardedCascade, denote, op2, denoteArgs]
      rw [htgtS]
      dsimp only [denoteArg, wp, Op.wp, OpCode.wp, vals, liftCmp, CmpOp.evalBits, Ty.hasFloat]
      constructor
      · intro htr
        have heq : tgt'.val = hPc := beq_iff_eq.1 htr
        have hP := hPred hPc List.mem_cons_self heq
        have hnxtS : denoteRegsExpr (⟨.bool, (tgt'.val == hPc)⟩ :: (extra ++ bvs ++ vsTail))
            (shiftRegsExpr (extra.length + 1) nxt) = some nxt' := by
          have hcons : (⟨.bool, (tgt'.val == hPc)⟩ :: (extra ++ bvs ++ vsTail) :
              List ((t : Ty) × Val t)) =
              ([⟨.bool, (tgt'.val == hPc)⟩] ++ extra) ++ (bvs ++ vsTail) := by
            simp [List.append_assoc]
          rw [hcons]
          have hlen : (([Sigma.mk Ty.bool (tgt'.val == hPc)] :
              List ((t : Ty) × Val t)) ++ extra).length = extra.length + 1 := by
            simp
          rw [← hlen, denoteRegsExpr_shift, hnxt]
        exact lowerJumpTo_wp hls hj hnxtS hP
      · intro _
        have ih := lowerGuardedCascade_wp (Γ := Γ) (X := X) hls htgt hnxt
          (⟨.bool, (tgt'.val == hPc)⟩ :: extra) rest hchk.2
          (fun p hp => hPred p (List.mem_cons_of_mem _ hp)) hCold
        dsimp only [pushTup, List.length_cons] at ih ⊢
        exact ih

private theorem lowerStrideOrRo_wp {Γ : Env} {X : XPost} {Ψ_bail Pred : CodeSpec}
    {pcs : List (BitVec 64)} {ls : List ((ts : List Ty) × Cont ts)}
    (hls : LsMatch pcs ls Pred) {bvs vsTail : List ((t : Ty) × Val t)}
    {rp₀ : BitVec 64} {st : SymState} (hst : SymStateOk bvs rp₀ st)
    {lvl : Nat} {x : Val i64} (hlvX : levelVal bvs lvl = some x)
    (hlook : lookupV bvs i64 (bvs.length - 1 - lvl) = some x) (hltB : lvl < bvs.length)
    {tgt : Arg K i64} {tgt' : Arg Val i64} (htgt : denoteArg (bvs ++ vsTail) tgt = some tgt')
    {nxt : RegsExpr K} {nxt' : RegsExpr Val}
    (hnxt : denoteRegsExpr (bvs ++ vsTail) nxt = some nxt')
    {m : Mem 64} (targets : List (BitVec 64)) (hne : targets ≠ [])
    (hchk : targets.all (fun p => (findLabelIdx pcs p).isSome) = true)
    (hHit : ∀ (hlt : x.toNat < targets.length), Pred (targets[x.toNat]'hlt) ⟨nxt'.eval, m⟩)
    (hBail : Ψ_bail tgt'.val ⟨nxt'.eval, m⟩) :
    wp Γ (regionRetPost RegionAbi.retEnvelope Ψ_bail rp₀) X
      (denote Val Cont (lowerStrideOrRo pcs (st.env.length - 1 - lvl) tgt nxt targets true)
        (bvs ++ vsTail) ls) m := by
  have hdenX : denoteArg (bvs ++ vsTail) (.var (st.env.length - 1 - lvl)) = some (.var x) := by
    dsimp only [denoteArg]; rw [levelVal_lookupV hst hlvX]
  dsimp only [lowerStrideOrRo]
  simp only [↓reduceIte]
  dsimp only [denote, op2, denoteArgs]
  rw [hdenX]
  dsimp only [denoteArg, wp, Op.wp, OpCode.wp, vals, liftCmp, CmpOp.evalBits, Ty.hasFloat]
  constructor
  · intro htr
    have hult : x.toNat < (BitVec.ofNat 64 targets.length).toNat := of_decide_eq_true htr
    have hlt : x.toNat < targets.length := by
      rw [BitVec.toNat_ofNat] at hult
      have hmod : targets.length % 2 ^ 64 ≤ targets.length := Nat.mod_le _ _
      omega
    have hres := lowerTableCascade_wp (rs := RegionAbi.retEnvelope.retSig) (Γ := Γ)
      (Q := regionRetPost RegionAbi.retEnvelope Ψ_bail rp₀) (X := X)
      (extra := [⟨.bool, BitVec.ult x (BitVec.ofNat 64 targets.length)⟩])
      hls hlook (by omega) hnxt 0 targets hne hchk (Nat.zero_le _) hlt (hHit hlt)
    dsimp only [pushTup]
    simpa [hst.lenEq, List.length_singleton] using hres
  · intro _
    dsimp only [mkRetEnvelope]
    have htgtS : denoteArg (⟨.bool, BitVec.ult x (BitVec.ofNat 64 targets.length)⟩ ::
        (bvs ++ vsTail)) (shiftArg 1 tgt) = some tgt' := by
      rw [denoteArg_shift1]; exact htgt
    have hnxtS : denoteRegsExpr (⟨.bool, BitVec.ult x (BitVec.ofNat 64 targets.length)⟩ ::
        (bvs ++ vsTail)) (shiftRegsExpr 1 nxt) = some nxt' := by
      rw [denoteRegsExpr_shift1]; exact hnxt
    obtain ⟨args', hargs', hvals⟩ := denoteRegsExpr_toTup hnxtS
    dsimp only [denote, pushTup, Arg.val]
    rw [denoteArgs_retEnv htgtS hargs']
    dsimp only [wp, regionRetPost]
    exact retEnvQ_of_eq hvals hBail

private theorem rpZero_nxtRp {bvs : List ((t : Ty) × Val t)} {rp₀ : BitVec 64} {st : SymState}
    (hst : SymStateOk bvs rp₀ st) {nxt : RegsExpr K} {nxt' : RegsExpr Val}
    (hnxtB : denoteRegsExpr bvs nxt = some nxt') {abi : RegionAbi}
    (hrpOk : (!abi.isContified || st.isRpZero nxt.rp) = true)
    (hCont : abi.isContified = true) :
    nxt'.eval.rp = rp₀ := by
  have hz : st.isRpZero nxt.rp = true := by
    rw [hCont] at hrpOk; simpa using hrpOk
  dsimp only [SymState.isRpZero] at hz
  have hrp : ∃ v, denoteArg bvs nxt.rp = some v := by
    dsimp only [denoteRegsExpr] at hnxtB
    cases h0 : denoteArg bvs nxt.sp <;> rw [h0] at hnxtB; · cases hnxtB
    cases h1 : denoteArg bvs nxt.rp <;> rw [h1] at hnxtB; · cases hnxtB
    exact ⟨_, rfl⟩
  obtain ⟨v, hv⟩ := hrp
  have hm := evalArg_symValMatch hst hv
  cases hev : st.evalArg nxt.rp with
  | rpOffset off =>
      rw [hev] at hz
      by_cases h0 : off = 0#64
      · subst h0
        rw [hev] at hm
        have hvEq : v.val = rp₀ + 0#64 := hm rfl
        dsimp only [denoteRegsExpr] at hnxtB
        cases h0' : denoteArg bvs nxt.sp <;> rw [h0'] at hnxtB; · cases hnxtB
        rw [hv] at hnxtB
        cases h2 : denoteArg bvs nxt.rv <;> rw [h2] at hnxtB; · cases hnxtB
        cases h3 : denoteArg bvs nxt.r1 <;> rw [h3] at hnxtB; · cases hnxtB
        cases h4 : denoteArg bvs nxt.r2 <;> rw [h4] at hnxtB; · cases hnxtB
        cases h5 : denoteArg bvs nxt.r3 <;> rw [h5] at hnxtB; · cases hnxtB
        cases hnxtB
        simpa [RegsExpr.eval] using hvEq
      · exfalso
        have hfalse : (match SymVal.rpOffset off with | .rpOffset 0#64 => true | _ => false) =
            false := by
          split <;> rename_i heq
          · cases heq; exact absurd rfl h0
          · rfl
        cases hz.symm.trans hfalse
  | const _ | alignedConst _ | taggedAligned _ _ | shl3 _ | stride _ _ | ite _ _ _
  | boolConst _ | cmpUlt _ _ | top =>
      rw [hev] at hz; cases hz

private def edgeRoOk (m : Mem 64) : EdgeKind → Prop
  | .memTableRo b ts _ => RoTableOk m b ts
  | _ => True

private theorem liftEdge_wp {abi : RegionAbi} {Γ : Env} {X : XPost}
    {Ψ_bail Pred : CodeSpec}
    {cm : CodeMap} {callees : List CalleeMeta}
    {pcs : List (BitVec 64)} {ls : List ((ts : List Ty) × Cont ts)}
    (hls : LsMatch pcs ls Pred)
    {bvs vsTail : List ((t : Ty) × Val t)} {rp₀ : BitVec 64} {st : SymState}
    (hst : SymStateOk bvs rp₀ st)
    {tgt : Arg K i64} {tgt' : Arg Val i64}
    (htgtB : denoteArg bvs tgt = some tgt') (hchkT : checkArg st.ctx i64 tgt = true)
    {nxt : RegsExpr K} {nxt' : RegsExpr Val}
    (hnxtB : denoteRegsExpr bvs nxt = some nxt') (hchkN : checkRegsExpr st.ctx nxt = true)
    {path : BranchPath} {kind : EdgeKind}
    (hEdge : checkEdgeLeaf cm abi callees pcs ⟨path, st, tgt, nxt⟩ kind = true)
    {Ψ_step : CodeSpec} {m₀ m : Mem 64}
    (hMemOk : SymMemOk m₀ m bvs st)
    (hRo : edgeRoOk m₀ kind)
    (hStep : Ψ_step tgt'.val ⟨nxt'.eval, m⟩)
    (hStepPred : ∀ pc s, (findLabelIdx pcs pc).isSome = true →
      (abi.isContified = true → s.regs.rp = rp₀) → Ψ_step pc s → Pred pc s)
    (hStepBail : ∀ pc s, Ψ_step pc s → Ψ_bail pc s)
    (hStepCall : ∀ callee calleePc dualRet retPc altRetPc?,
      abi.isContified = false →
      callees.any (fun c => (c.name == callee) && (c.entryPc == calleePc) &&
        (c.dualRet == dualRet)) = true →
      cm.addrOf? callee = some calleePc →
      tgt'.val = calleePc →
      nxt'.rp.val = retPc →
      (if dualRet then altRetPc? = some (retPc + 8#64) else altRetPc?.isNone) →
      (findLabelIdx pcs retPc).isSome = true →
      (if dualRet then (findLabelIdx pcs (retPc + 8#64)).isSome = true else True) →
      (match kind with | .contCall _ _ _ _ _ => True | _ => False) →
      ∃ P E, Γ callee regSig (RegionAbi.contified dualRet).retSig
          (vals nxt'.toTup) m P E ∧
        (∀ r m', P r m' → retContPost dualRet Pred retPc r m') ∧
        (∀ g cs xs m', E g cs xs m' → X g cs xs m')) :
    wp Γ (regionRetPost abi Ψ_bail rp₀) X
      (denote Val Cont (liftEdge abi pcs st tgt nxt kind) (bvs ++ vsTail) ls) m := by
  have htgt : denoteArg (bvs ++ vsTail) tgt = some tgt' := by
    rw [denoteArg_prefix vsTail hst.ctxOk hchkT]; exact htgtB
  have hnxt : denoteRegsExpr (bvs ++ vsTail) nxt = some nxt' := by
    rw [denoteRegsExpr_prefix vsTail hst.ctxOk hchkN]; exact hnxtB
  have hmt := evalArg_symValMatch hst htgtB
  dsimp only [checkEdgeLeaf, SymState.resolveConst] at hEdge
  cases kind with
  | direct targetPc =>
      simp only [Bool.and_eq_true] at hEdge
      have hrc : tgt'.val = targetPc := asConst_eq hmt (beq_iff_eq.1 hEdge.1.2)
      rcases Option.isSome_iff_exists.1 hEdge.2 with ⟨j, hj⟩
      dsimp only [liftEdge]
      rw [hrc] at hStep
      exact lowerJumpTo_wp hls hj hnxt
        (hStepPred targetPc _ hEdge.2 (rpZero_nxtRp hst hnxtB hEdge.1.1) hStep)
  | select tPc ePc =>
      simp only [Bool.and_eq_true] at hEdge
      rcases Option.isSome_iff_exists.1 hEdge.1.1.2 with ⟨jt, hjt⟩
      rcases Option.isSome_iff_exists.1 hEdge.1.2 with ⟨je, hje⟩
      dsimp only [liftEdge]
      cases hev : st.evalArg tgt
      <;> (try (rw [hev] at hEdge; dsimp only at hEdge; rcases hEdge with ⟨_, hbad⟩; cases hbad))
      · rename_i cLvl tSym eSym
        rw [hev] at hEdge hmt
        dsimp only at hEdge
        simp only [Bool.and_eq_true] at hEdge
        obtain ⟨b, hb, htB, heB⟩ := hmt rfl
        have hcIdx : lookupV (bvs ++ vsTail) .bool (st.env.length - 1 - cLvl) = some b :=
          levelVal_lookupV hst hb
        dsimp only [denote, denoteArg]
        rw [hcIdx]
        dsimp only [wp]
        constructor
        · intro htr
          have htc := asConst_eq (htB htr) (beq_iff_eq.1 hEdge.2.1.2)
          simp only [cast_eq] at htc
          rw [htc] at hStep
          exact lowerJumpTo_wp hls hjt hnxt
            (hStepPred tPc _ hEdge.1.1.2 (rpZero_nxtRp hst hnxtB hEdge.1.1.1) hStep)
        · intro hfl
          have hec := asConst_eq (heB hfl) (beq_iff_eq.1 hEdge.2.2)
          simp only [cast_eq] at hec
          rw [hec] at hStep
          exact lowerJumpTo_wp hls hje hnxt
            (hStepPred ePc _ hEdge.1.2 (rpZero_nxtRp hst hnxtB hEdge.1.1.1) hStep)
  | strideTable basePc targets needGuard =>
      simp only [Bool.and_eq_true] at hEdge
      have hne : targets ≠ [] := by
        intro he; simp [he] at hEdge
      cases hev : st.evalArg tgt
      <;> (try (rw [hev] at hEdge; dsimp only at hEdge; rcases hEdge with ⟨_, hbad⟩; cases hbad))
      · rename_i b lvl
        rw [hev] at hEdge hmt
        dsimp only at hEdge
        simp only [Bool.and_eq_true] at hEdge
        have hbeq : b = basePc := beq_iff_eq.1 hEdge.2.1.1
        subst b
        obtain ⟨x, hx, hxtgt⟩ := hmt rfl
        have hlvlLt : lvl < bvs.length := levelVal_lt_len hx
        have hlook : lookupV bvs i64 (bvs.length - 1 - lvl) = some x := by
          dsimp only [levelVal] at hx; rw [ite_eq_left hlvlLt] at hx; exact hx
        dsimp only [liftEdge]
        rw [hev]
        simp only [cast_eq] at hxtgt
        cases needGuard
        · have hult : st.hasUltBound lvl targets.length = true := hEdge.2.2
          dsimp only [SymState.hasUltBound] at hult
          rw [List.any_eq_true] at hult
          obtain ⟨⟨l, bound⟩, hfMem, hfOk⟩ := hult
          have hF := hst.factsOk (.ultBound l bound) hfMem
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfOk
          rcases hfOk with ⟨rfl, hle⟩
          obtain ⟨x', hx', hltB⟩ := hF
          rw [hx] at hx'; cases hx'
          rw [hst.lenEq]
          have hlt : x.toNat < 0 + targets.length := by omega
          have hres := lowerStrideCascade_wp
            (rs := abi.retSig) (Γ := Γ) (Q := regionRetPost abi Ψ_bail rp₀) (X := X)
            (extra := []) hls hlook (by omega) hnxt 0 targets
            hne hEdge.1.2 (Nat.zero_le _) hlt
            (hStepPred _ _ (checkStrideTargets_mem_isSome 0 targets x.toNat hEdge.1.2
              (Nat.zero_le _) hlt) (rpZero_nxtRp hst hnxtB hEdge.1.1.1) (hxtgt ▸ hStep))
          simpa [hst.lenEq] using hres
        · cases abi
          · dsimp only
            exact lowerStrideOrRo_wp hls hst hx hlook hlvlLt htgt hnxt targets hne
              (checkStrideTargets_all_isSome pcs basePc 0 targets hEdge.1.2)
              (fun hlt => by
                have hget := checkStrideTargets_getElem pcs basePc 0 targets x.toNat hlt hEdge.1.2
                simp only [Nat.zero_add] at hget
                rw [hget]
                exact hStepPred _ _ (checkStrideTargets_mem_isSome 0 targets x.toNat hEdge.1.2
                  (Nat.zero_le _) (by simpa using hlt)) (fun h => by cases h) (hxtgt ▸ hStep))
              (hStepBail _ _ hStep)
          · simp [RegionAbi.isContified] at hEdge
  | memTableGuarded _ targets =>
      cases abi
      · simp only [RegionAbi.isContified, Bool.not_false, Bool.true_and,
          Bool.and_eq_true, List.all_eq_true] at hEdge
        dsimp only [liftEdge]
        exact lowerGuardedCascade_wp hls htgt hnxt [] targets
          (by simpa [List.all_eq_true] using hEdge.1.2)
          (fun p hp heq => hStepPred p _ (hEdge.1.2 p hp) (fun h => by cases h) (heq ▸ hStep))
          (hStepBail _ _ hStep)
      · simp [RegionAbi.isContified] at hEdge
  | memTableRo tblBase targets needGuard =>
      cases abi
      · simp only [RegionAbi.isContified, Bool.not_false, Bool.true_and,
          Bool.and_eq_true] at hEdge
        have hne : targets ≠ [] := by intro he; simp [he] at hEdge
        cases hml : st.memLoadIdx? tgt tblBase true with
        | none => rw [hml] at hEdge; simp at hEdge
        | some lvl =>
            rw [hml] at hEdge; dsimp only at hEdge
            obtain ⟨_, _, e, rfl, htl, _, heMem, rfl, rfl, rfl, hcl, hty⟩ :=
              symState_findMemLoad_spec hml
            obtain ⟨x, hx, hltB, hlvX⟩ := levelHasTy_lookupV hst hty
            obtain ⟨x₀, v₀, hx₀, hv₀, hload₀⟩ := hMemOk.2 e heMem (hcl rfl)
            rw [hlvX] at hx₀; cases hx₀
            have hvTgt : levelVal bvs e.valLvl = some tgt'.val := var_levelVal hst htl htgtB
            rw [hv₀] at hvTgt; cases hvTgt
            have hHit : ∀ (hlt : x.toNat < targets.length),
                Pred (targets[x.toNat]'hlt) ⟨nxt'.eval, m⟩ := fun hlt => by
              have hldT := hRo x.toNat hlt; rw [hload₀, Option.some.injEq] at hldT
              refine hStepPred _ _ (List.all_eq_true.1 hEdge.1.2 _ (List.getElem_mem hlt))
                (fun h => by cases h) ?_
              rw [← hldT]; exact hStep
            dsimp only [liftEdge]; rw [hml]
            cases needGuard
            · have hult : st.hasUltBound e.idxLvl targets.length = true := hEdge.2
              dsimp only [SymState.hasUltBound] at hult
              rw [List.any_eq_true] at hult
              obtain ⟨⟨l, bound⟩, hfMem, hfOk⟩ := hult
              have hF := hst.factsOk (.ultBound l bound) hfMem
              simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfOk
              rcases hfOk with ⟨rfl, hle⟩
              obtain ⟨x', hx', hltBnd⟩ := hF
              rw [hlvX] at hx'; cases hx'
              have hlt : x.toNat < targets.length := by omega
              dsimp only [lowerStrideOrRo, Bool.false_eq_true, ↓reduceIte]
              simpa [hst.lenEq] using lowerTableCascade_wp
                (rs := RegionAbi.retEnvelope.retSig) (Γ := Γ)
                (Q := regionRetPost RegionAbi.retEnvelope Ψ_bail rp₀) (X := X)
                hls hx (by omega) hnxt 0 [] targets hne hEdge.1.2 (Nat.zero_le _) hlt (hHit hlt)
            · exact lowerStrideOrRo_wp hls hst hlvX hx hltB htgt hnxt targets hne
                hEdge.1.2 hHit (hStepBail _ _ hStep)
      · simp [RegionAbi.isContified] at hEdge
  | contCall callee calleePc dualRet retPc altRetPc? =>
      cases abi
      · simp only [RegionAbi.isContified, Bool.not_false, Bool.true_and, Bool.and_eq_true] at hEdge
        have haddr : cm.addrOf? callee = some calleePc := beq_iff_eq.1 hEdge.1.1.1.1.1
        have htc : tgt'.val = calleePc := asConst_eq hmt (beq_iff_eq.1 hEdge.1.1.1.1.2)
        have hmrp : SymValMatch bvs rp₀ (st.evalArg nxt.rp) i64 nxt'.rp.val := by
          dsimp only [denoteRegsExpr] at hnxtB
          cases hs : denoteArg bvs nxt.sp <;> rw [hs] at hnxtB; · cases hnxtB
          cases hrp : denoteArg bvs nxt.rp <;> rw [hrp] at hnxtB; · cases hnxtB
          cases hrv : denoteArg bvs nxt.rv <;> rw [hrv] at hnxtB; · cases hnxtB
          cases hr1 : denoteArg bvs nxt.r1 <;> rw [hr1] at hnxtB; · cases hnxtB
          cases hr2 : denoteArg bvs nxt.r2 <;> rw [hr2] at hnxtB; · cases hnxtB
          cases hr3 : denoteArg bvs nxt.r3 <;> rw [hr3] at hnxtB; · cases hnxtB
          cases hnxtB
          exact evalArg_symValMatch hst hrp
        have hrpc : nxt'.rp.val = retPc := asConst_eq hmrp (beq_iff_eq.1 hEdge.1.1.1.2)
        obtain ⟨args', hargs', hvals⟩ := denoteRegsExpr_toTup hnxt
        have hAltCond : if dualRet then altRetPc? = some (retPc + 8#64) else altRetPc?.isNone := by
          cases dualRet
          · exact hEdge.2
          · simp only [↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hEdge
            exact hEdge.2.1
        have hAltIn :
            if dualRet then (findLabelIdx pcs (retPc + 8#64)).isSome = true else True := by
          cases dualRet
          · trivial
          · simp only [↓reduceIte, Bool.and_eq_true] at hEdge
            exact hEdge.2.2
        obtain ⟨P, E, hΓc, hP, hE⟩ :=
          hStepCall callee calleePc dualRet retPc altRetPc? rfl
            hEdge.1.2 haddr htc hrpc hAltCond hEdge.1.1.2 hAltIn trivial
        dsimp only [liftEdge]
        cases dualRet
        · simp only [Bool.false_eq_true, ↓reduceIte]; dsimp only [denote]
          rw [hargs']
          refine ⟨P, E, ?_, ?_, hE⟩
          · rw [hvals, ← vals_regsExpr_toTup]; exact hΓc
          · intro r m' hr
            rcases Option.isSome_iff_exists.1 hEdge.1.1.2 with ⟨jr, hjr⟩
            have hPr := hP r m' hr
            dsimp only [retContPost] at hPr
            obtain ⟨argsR, hargsR, hvalsR⟩ := denoteArgs_baseRegs_false r (bvs ++ vsTail)
            dsimp only [lowerJumpTo]
            rw [hjr]
            obtain ⟨Jr, hJr, hJrP⟩ := hls retPc jr hjr
            dsimp only [denote]
            rw [hJr, hargsR]
            dsimp only [wp]
            rw [hvalsR]
            rcases r with ⟨sp, rp, rv, r1, r2, r3, ⟨⟩⟩
            exact hJrP ⟨sp, rp, rv, r1, r2, r3⟩ m' hPr
        · cases altRetPc? with
          | none => simp at hAltCond
          | some altPc =>
              have haltEq : altPc = retPc + 8#64 := by simpa using hAltCond
              subst haltEq
              simp only [↓reduceIte]; dsimp only [denote]
              rw [hargs']
              refine ⟨P, E, ?_, ?_, hE⟩
              · rw [hvals, ← vals_regsExpr_toTup]; exact hΓc
              · intro r m' hr
                have hPr := hP r m' hr
                dsimp only [retContPost] at hPr
                obtain ⟨argsR, cR, hcR, hcVal, hargsR, hvalsR⟩ :=
                  denoteArgs_retRegArgs_true r (bvs ++ vsTail)
                dsimp only [denote]
                rw [hcR]
                dsimp only [wp]
                constructor
                · intro htr
                  have his : r.1 = true := by rw [← hcVal, htr]
                  rcases Option.isSome_iff_exists.1 hAltIn with ⟨ja, hja⟩
                  dsimp only [lowerJumpTo]; rw [hja]
                  obtain ⟨Ja, hJa, hJaP⟩ := hls (retPc + 8#64) ja hja
                  dsimp only [denote]; rw [hJa, hargsR]
                  dsimp only [wp]; rw [hvalsR]
                  rcases r with ⟨isAlt, sp, rp, rv, r1, r2, r3, ⟨⟩⟩
                  dsimp only at his
                  exact hJaP ⟨sp, rp, rv, r1, r2, r3⟩ m' (by simpa [his] using hPr)
                · intro hfl
                  have his : r.1 = false := by rw [← hcVal, hfl]
                  rcases Option.isSome_iff_exists.1 hEdge.1.1.2 with ⟨jr, hjr⟩
                  dsimp only [lowerJumpTo]; rw [hjr]
                  obtain ⟨Jr, hJr, hJrP⟩ := hls retPc jr hjr
                  dsimp only [denote]; rw [hJr, hargsR]
                  dsimp only [wp]; rw [hvalsR]
                  rcases r with ⟨isAlt, sp, rp, rv, r1, r2, r3, ⟨⟩⟩
                  dsimp only at his
                  exact hJrP ⟨sp, rp, rv, r1, r2, r3⟩ m' (by simpa [his] using hPr)
      · dsimp only at hEdge; simp [RegionAbi.isContified] at hEdge
  | contRet isAlt =>
      cases abi
      · simp at hEdge
      · rename_i dualRet
        simp only [Bool.and_eq_true] at hEdge
        have hisOk : (if isAlt then dualRet = true else True) := by
          cases isAlt
          · trivial
          · exact of_decide_eq_true (by simpa using hEdge.1)
        have hevEq : st.evalArg tgt = .rpOffset (if isAlt then 8#64 else 0#64) :=
          of_decide_eq_true hEdge.2
        rw [hevEq] at hmt
        have hrpTgt : tgt'.val = rp₀ + (if isAlt then 8#64 else 0#64) := hmt rfl
        have hbail := hStepBail _ _ hStep
        rw [hrpTgt] at hbail
        obtain ⟨args', hargs', hvals⟩ := denoteRegsExpr_toTup hnxt
        cases dualRet
        · cases isAlt
          · dsimp only [liftEdge, denote]
            rw [denoteArgs_contRetFalse hargs']
            dsimp only [wp, regionRetPost]
            exact retContPost_false_of_eq hvals (by simpa using hbail)
          · simp at hisOk
        · cases isAlt
          · dsimp only [liftEdge, denote]
            rw [denoteArgs_contRetTrue false hargs']
            dsimp only [wp, regionRetPost]
            exact retContPost_true_of_eq false hvals (by simpa using hbail)
          · dsimp only [liftEdge, denote]
            rw [denoteArgs_contRetTrue true hargs']
            dsimp only [wp, regionRetPost]
            exact retContPost_true_of_eq true hvals (by simpa using hbail)
  | guarded hotTargets =>
      cases abi
      · simp only [RegionAbi.isContified, Bool.not_false, Bool.true_and,
          List.all_eq_true] at hEdge
        dsimp only [liftEdge]
        exact lowerGuardedCascade_wp hls htgt hnxt [] hotTargets
          (by simpa [List.all_eq_true] using hEdge)
          (fun p hp heq => hStepPred p _ (hEdge p hp) (fun h => by cases h) (heq ▸ hStep))
          (hStepBail _ _ hStep)
      · dsimp only at hEdge; simp [RegionAbi.isContified] at hEdge
  | bailout =>
      cases abi
      · obtain ⟨args', hargs', hvals⟩ := denoteRegsExpr_toTup hnxt
        dsimp only [liftEdge, mkRetEnvelope, denote]
        rw [denoteArgs_retEnv htgt hargs']
        dsimp only [wp, regionRetPost]
        exact retEnvQ_of_eq hvals (hStepBail _ _ hStep)
      · dsimp only at hEdge; simp [RegionAbi.isContified] at hEdge

theorem pushCondFact_ctx (st : SymState) (c : Arg K .bool) (taken : Bool) :
    (st.pushCondFact c taken).ctx = st.ctx := by
  dsimp only [SymState.pushCondFact]
  cases taken
  · rfl
  · cases c with
    | imm _ => rfl
    | var idx => simp only [↓reduceIte]; cases st.getSym idx <;> rfl

private theorem liftBlock_wp {rw : RegionWitness} {Γ : Env} {X : XPost}
    {Ψ_bail Pred Ψ_step : CodeSpec} {H : HaltPost}
    {cm : CodeMap} {callees : List CalleeMeta}
    {pcs : List (BitVec 64)} {ls : List ((ts : List Ty) × Cont ts)}
    (hls : LsMatch pcs ls Pred) (pc rp₀ : BitVec 64)
    (hH : ∀ c m', H c m' → X haltSym [i64] (c, ()) m')
    (hStepPred : ∀ pc' s', (findLabelIdx pcs pc').isSome = true →
      (rw.abi.isContified = true → s'.regs.rp = rp₀) → Ψ_step pc' s' → Pred pc' s')
    (hStepBail : ∀ pc' s', Ψ_step pc' s' → Ψ_bail pc' s')
    (hStepCall : ∀ callee calleePc dualRet (nxtR : Regs) m' retPc altRetPc?,
      rw.abi.isContified = false →
      callees.any (fun c => (c.name == callee) && (c.entryPc == calleePc) &&
        (c.dualRet == dualRet)) = true →
      cm.addrOf? callee = some calleePc →
      nxtR.rp = retPc →
      (if dualRet then altRetPc? = some (retPc + 8#64) else altRetPc?.isNone) →
      (findLabelIdx pcs retPc).isSome = true →
      (if dualRet then (findLabelIdx pcs (retPc + 8#64)).isSome = true else True) →
      (rw.edges.any (fun ew => match ew.kind with | .contCall _ _ _ _ _ => true | _ => false) =
        true) →
      Ψ_step calleePc ⟨nxtR, m'⟩ →
      ∃ P E, Γ callee regSig (RegionAbi.contified dualRet).retSig
          nxtR.toRegsV.toTup m' P E ∧
        (∀ r m'', P r m'' → retContPost dualRet Pred retPc r m'') ∧
        (∀ g cs xs m'', E g cs xs m'' → X g cs xs m''))
    (m₀ : Mem 64) (hRo : RegionRoOk rw m₀) :
    ∀ (b : BlockFlat) (path : BranchPath) (st : SymState)
      (bvs vsTail : List ((t : Ty) × Val t)) (leaves : List SymLeaf) (m : Mem 64),
      SymStateOk bvs rp₀ st →
      SymMemOk m₀ m bvs st →
      b.wfCheck st.ctx = true →
      b.noHlt = true →
      symEvalBlock cm b path st = some leaves →
      (∀ leaf ∈ leaves, ∃ ew, rw.findEdge pc leaf.path = some ew ∧
        checkEdgeLeaf cm rw.abi callees pcs leaf ew.kind = true) →
      b.wp cm.symEnv Ψ_step H bvs m →
      wp Γ (regionRetPost rw.abi Ψ_bail rp₀) X
        (denote Val Cont (liftBlock cm rw pcs pc b path st) (bvs ++ vsTail) ls) m
  | .let_ (ts := ts) op k, path, st, bvs, vsTail, leaves, m, hst, hmOk, hwf, hno, hlv,
      hleaves, hbp => by
      dsimp only [BlockFlat.wfCheck] at hwf
      rcases Bool.and_eq_true_iff.1 hwf with ⟨hwfA, hwfK⟩
      dsimp only [BlockFlat.noHlt] at hno
      dsimp only [symEvalBlock] at hlv
      dsimp only [BlockFlat.wp] at hbp
      cases hda : denoteArgs bvs op.args with
      | none => rw [hda] at hbp; exact False.elim hbp
      | some args' =>
          rw [hda] at hbp
          have hda' : denoteArgs (bvs ++ vsTail) op.args = some args' := by
            rw [denoteArgs_prefix vsTail hst.ctxOk hwfA, hda]
          dsimp only [liftBlock, denote]
          rw [hda']
          dsimp only [wp]
          exact symEvalOp_wp_mono op hst hda (fun r hkr hst' => by
            rw [pushTup_append]
            have hmOk' : SymMemOk m₀ m (pushTup r bvs) (st.pushRes ts (symEvalOp st op)) := by
              rw [← List.nil_append bvs, pushTup_append r [] bvs]
              exact symMemOk_prepend (pushTup r []) bvs hmOk _ _
            exact liftBlock_wp hls pc rp₀ hH hStepPred hStepBail hStepCall m₀ hRo k path
              (st.pushRes ts (symEvalOp st op)) (pushTup r bvs) vsTail leaves m hst' hmOk' hwfK
              hno hlv hleaves hkr) hbp
  | .load t a k, path, st, bvs, vsTail, leaves, m, hst, hmOk, hwf, hno, hlv, hleaves, hbp => by
      dsimp only [BlockFlat.wfCheck] at hwf
      rcases Bool.and_eq_true_iff.1 hwf with ⟨hwfA, hwfK⟩
      dsimp only [BlockFlat.noHlt] at hno
      dsimp only [symEvalBlock] at hlv
      dsimp only [BlockFlat.wp] at hbp
      cases hda : denoteArg bvs a with
      | none => rw [hda] at hbp; exact False.elim hbp
      | some a' =>
          rw [hda] at hbp
          rcases hbp with ⟨v, hv, hkv⟩
          have hda' : denoteArg (bvs ++ vsTail) a = some a' := by
            rw [denoteArg_prefix vsTail hst.ctxOk hwfA, hda]
          dsimp only [liftBlock, denote]
          rw [hda']
          dsimp only [wp]
          refine ⟨v, hv, ?_⟩
          have hst' := symStateOk_stepLoad v hst a
          have hmOk' := symMemOk_stepLoad hst hmOk t a hda v hv
          exact liftBlock_wp hls pc rp₀ hH hStepPred hStepBail hStepCall m₀ hRo k path
            (st.stepLoad t a) (⟨t, v⟩ :: bvs) vsTail leaves m hst' hmOk' hwfK hno hlv
            hleaves hkv
  | .store (t := t) v a k, path, st, bvs, vsTail, leaves, m, hst, hmOk, hwf, hno, hlv,
      hleaves, hbp => by
      dsimp only [BlockFlat.wfCheck] at hwf
      rcases Bool.and_eq_true_iff.1 hwf with ⟨hwfVA, hwfK⟩
      rcases Bool.and_eq_true_iff.1 hwfVA with ⟨hwfV, hwfA⟩
      dsimp only [BlockFlat.noHlt] at hno
      dsimp only [symEvalBlock] at hlv
      dsimp only [BlockFlat.wp] at hbp
      cases hdv : denoteArg bvs v with
      | none => rw [hdv] at hbp; exact False.elim hbp
      | some v' =>
          cases hda : denoteArg bvs a with
          | none => rw [hdv, hda] at hbp; exact False.elim hbp
          | some a' =>
              rw [hdv, hda] at hbp
              rcases hbp with ⟨hok, hk⟩
              have hdv' : denoteArg (bvs ++ vsTail) v = some v' := by
                rw [denoteArg_prefix vsTail hst.ctxOk hwfV, hdv]
              have hda' : denoteArg (bvs ++ vsTail) a = some a' := by
                rw [denoteArg_prefix vsTail hst.ctxOk hwfA, hda]
              dsimp only [liftBlock, denote]
              rw [hdv', hda']
              exact ⟨hok, liftBlock_wp hls pc rp₀ hH hStepPred hStepBail hStepCall m₀ hRo k path
                { st with hasStored := true } bvs vsTail leaves _ (symStateOk_store hst)
                (symMemOk_store hmOk) hwfK hno hlv hleaves hk⟩
  | .codeAddr sym k, path, st, bvs, vsTail, leaves, m, hst, hmOk, hwf, hno, hlv,
      hleaves, hbp => by
      dsimp only [BlockFlat.wfCheck] at hwf
      dsimp only [BlockFlat.noHlt] at hno
      dsimp only [symEvalBlock] at hlv
      dsimp only [BlockFlat.wp] at hbp
      rcases hbp with ⟨a', hsym, hk⟩
      cases haddr : cm.addrOf? sym with
      | none => rw [haddr] at hlv; cases hlv
      | some a =>
          rw [haddr] at hlv
          have haeq : a' = a := Option.some.inj (hsym.symm.trans haddr)
          subst haeq
          dsimp only [liftBlock]
          rw [haddr]
          dsimp only [denote, op1, denoteArgs, denoteArg, wp, Op.wp, OpCode.wp, vals]
          have hm : SymValMatch (⟨i64, a'⟩ :: bvs) rp₀
              (if (a' &&& 7#64) == 0#64 then .alignedConst a' else .const a') i64 a' := by
            by_cases ha : (a' &&& 7#64) == 0#64
            · simp only [ha, ↓reduceIte]; exact fun _ => ⟨rfl, beq_iff_eq.1 ha⟩
            · simp only [ha, Bool.false_eq_true, ↓reduceIte]; exact fun _ => rfl
          have hst' := symStateOk_cons (t := i64) a' _ hst hm
          have hmOk' := symMemOk_prepend [⟨i64, a'⟩] bvs hmOk
            ((if (a' &&& 7#64) == 0#64 then .alignedConst a' else .const a') :: st.env)
            (i64 :: st.ctx)
          exact liftBlock_wp hls pc rp₀ hH hStepPred hStepBail hStepCall m₀ hRo k path
            { st with
              env := (if (a' &&& 7#64) == 0#64 then .alignedConst a' else .const a') :: st.env,
              ctx := i64 :: st.ctx }
            (⟨i64, a'⟩ :: bvs) vsTail leaves m hst' hmOk' hwf hno hlv hleaves hk
  | .jnz c t e, path, st, bvs, vsTail, leaves, m, hst, hmOk, hwf, hno, hlv, hleaves, hbp => by
      dsimp only [BlockFlat.wfCheck] at hwf
      rcases Bool.and_eq_true_iff.1 hwf with ⟨hwfCT, hwfE⟩
      rcases Bool.and_eq_true_iff.1 hwfCT with ⟨hwfC, hwfT⟩
      dsimp only [BlockFlat.noHlt] at hno
      rcases Bool.and_eq_true_iff.1 hno with ⟨hnoT, hnoE⟩
      dsimp only [symEvalBlock] at hlv
      cases hlt' : symEvalBlock cm t (path ++ [true]) (st.pushCondFact c true) with
      | none => simp [hlt'] at hlv
      | some lt =>
          cases hle' : symEvalBlock cm e (path ++ [false]) (st.pushCondFact c false) with
          | none => simp [hlt', hle'] at hlv
          | some le =>
              simp only [hlt', hle'] at hlv
              cases hlv
              dsimp only [BlockFlat.wp] at hbp
              cases hdc : denoteArg bvs c with
              | none => rw [hdc] at hbp; exact False.elim hbp
              | some c' =>
                  rw [hdc] at hbp
                  rcases hbp with ⟨hbt, hbe⟩
                  have hdc' : denoteArg (bvs ++ vsTail) c = some c' := by
                    rw [denoteArg_prefix vsTail hst.ctxOk hwfC, hdc]
                  dsimp only [liftBlock, denote]
                  rw [hdc']
                  dsimp only [wp]
                  constructor
                  · intro htr
                    have hstT := pushCondFact_sound hst hdc true htr
                    have hwfT' : t.wfCheck (st.pushCondFact c true).ctx = true := by
                      rw [pushCondFact_ctx]; exact hwfT
                    exact liftBlock_wp hls pc rp₀ hH hStepPred hStepBail hStepCall m₀ hRo t
                      (path ++ [true]) (st.pushCondFact c true) bvs vsTail lt m hstT
                      (symMemOk_pushCondFact hmOk c true) hwfT' hnoT hlt'
                      (fun lf hmem => hleaves lf (List.mem_append_left le hmem)) (hbt htr)
                  · intro hfl
                    have hstE := pushCondFact_sound hst hdc false hfl
                    have hwfE' : e.wfCheck (st.pushCondFact c false).ctx = true := by
                      rw [pushCondFact_ctx]; exact hwfE
                    exact liftBlock_wp hls pc rp₀ hH hStepPred hStepBail hStepCall m₀ hRo e
                      (path ++ [false]) (st.pushCondFact c false) bvs vsTail le m hstE
                      (symMemOk_pushCondFact hmOk c false) hwfE' hnoE hle'
                      (fun lf hmem => hleaves lf (List.mem_append_right lt hmem)) (hbe hfl)
  | .ijmp tgt nxt, path, st, bvs, vsTail, leaves, m, hst, hmOk, hwf, _, hlv, hleaves, hbp => by
      dsimp only [BlockFlat.wfCheck] at hwf
      rcases Bool.and_eq_true_iff.1 hwf with ⟨hwfT, hwfN⟩
      dsimp only [symEvalBlock] at hlv
      cases hlv
      obtain ⟨ew, hfind, hchk⟩ := hleaves ⟨path, st, tgt, nxt⟩ List.mem_cons_self
      have hewMem : ew ∈ rw.edges := by
        dsimp only [RegionWitness.findEdge] at hfind
        exact List.mem_of_find?_eq_some hfind
      have hRoEdge : edgeRoOk m₀ ew.kind := by
        have h' := hRo ew hewMem
        dsimp only [edgeRoOk]; exact h'
      dsimp only [BlockFlat.wp] at hbp
      cases hdt : denoteArg bvs tgt with
      | none => rw [hdt] at hbp; exact False.elim hbp
      | some tgt' =>
          cases hdn : denoteRegsExpr bvs nxt with
          | none => rw [hdt, hdn] at hbp; exact False.elim hbp
          | some nxt' =>
              rw [hdt, hdn] at hbp
              dsimp only at hbp
              dsimp only [liftBlock]
              rw [hfind]
              refine liftEdge_wp hls hst hdt hwfT hdn hwfN hchk hmOk hRoEdge hbp hStepPred
                hStepBail ?_
              intro callee calleePc dualRet retPc altRetPc?
                hAb hcal haddr htc hrpc hAltC hRetIn hAltIn hIsCont
              rw [htc] at hbp
              have hCont : rw.edges.any (fun ew =>
                  match ew.kind with | .contCall _ _ _ _ _ => true | _ => false) = true :=
                List.any_eq_true.2 ⟨ew, hewMem, by
                  cases hkw : ew.kind <;> rw [hkw] at hIsCont <;>
                    first | rfl | exact False.elim hIsCont⟩
              exact hStepCall callee calleePc dualRet _ m retPc altRetPc? hAb hcal haddr hrpc
                hAltC hRetIn hAltIn hCont hbp
  | .halt c, _, st, bvs, vsTail, _, m, hst, _, hwf, _, _, _, hbp => by
      dsimp only [BlockFlat.wfCheck] at hwf
      dsimp only [BlockFlat.wp] at hbp
      cases hdc : denoteArg bvs c with
      | none => rw [hdc] at hbp; exact False.elim hbp
      | some c' =>
          rw [hdc] at hbp
          have hdc' : denoteArg (bvs ++ vsTail) c = some c' := by
            rw [denoteArg_prefix vsTail hst.ctxOk hwf, hdc]
          dsimp only [liftBlock, denote, denoteArgs]
          rw [hdc']
          dsimp only [denoteArgs, wp, vals]
          exact hH c'.val m hbp
  | .hlt, _, _, _, _, _, _, _, _, _, hno, _, _, _ => by
      dsimp only [BlockFlat.noHlt] at hno; cases hno

theorem liftBlock_wp_init {rw : RegionWitness} {Γ : Env} {X : XPost}
    {Ψ_bail Pred Ψ_step : CodeSpec} {H : HaltPost}
    {cm : CodeMap} {callees : List CalleeMeta}
    {pcs : List (BitVec 64)} {ls : List ((ts : List Ty) × Cont ts)}
    (hls : LsMatch pcs ls Pred) (pc : BitVec 64) (r₀ : Regs)
    (hH : ∀ c m', H c m' → X haltSym [i64] (c, ()) m')
    (hStepPred : ∀ pc' s', (findLabelIdx pcs pc').isSome = true →
      (rw.abi.isContified = true → s'.regs.rp = r₀.rp) → Ψ_step pc' s' → Pred pc' s')
    (hStepBail : ∀ pc' s', Ψ_step pc' s' → Ψ_bail pc' s')
    (hStepCall : ∀ callee calleePc dualRet (nxtR : Regs) m' retPc altRetPc?,
      rw.abi.isContified = false →
      callees.any (fun c => (c.name == callee) && (c.entryPc == calleePc) &&
        (c.dualRet == dualRet)) = true →
      cm.addrOf? callee = some calleePc →
      nxtR.rp = retPc →
      (if dualRet then altRetPc? = some (retPc + 8#64) else altRetPc?.isNone) →
      (findLabelIdx pcs retPc).isSome = true →
      (if dualRet then (findLabelIdx pcs (retPc + 8#64)).isSome = true else True) →
      (rw.edges.any (fun ew => match ew.kind with | .contCall _ _ _ _ _ => true | _ => false) =
        true) →
      Ψ_step calleePc ⟨nxtR, m'⟩ →
      ∃ P E, Γ callee regSig (RegionAbi.contified dualRet).retSig
          nxtR.toRegsV.toTup m' P E ∧
        (∀ r m'', P r m'' → retContPost dualRet Pred retPc r m'') ∧
        (∀ g cs xs m'', E g cs xs m'' → X g cs xs m''))
    (b : BlockFlat) (leaves : List SymLeaf) (m : Mem 64)
    (hRo : RegionRoOk rw m)
    (hwf : b.wfCheck regCtx = true) (hno : b.noHlt = true)
    (hlv : symEvalBlock cm b [] SymState.init = some leaves)
    (hleaves : ∀ lf ∈ leaves, ∃ ew, rw.findEdge pc lf.path = some ew ∧
      checkEdgeLeaf cm rw.abi callees pcs lf ew.kind = true)
    (hbp : b.wp cm.symEnv Ψ_step H (pushRegsV r₀.toRegsV) m) :
    wp Γ (regionRetPost rw.abi Ψ_bail r₀.rp) X
      (denote Val Cont (liftBlock cm rw pcs pc b [] SymState.init)
        (pushRegsV r₀.toRegsV) ls) m :=
  liftBlock_wp hls pc r₀.rp hH hStepPred hStepBail hStepCall m hRo b [] SymState.init
    (pushRegsV r₀.toRegsV) [] leaves m (symStateOk_init r₀) (symMemOk_init r₀ m)
    hwf hno hlv hleaves hbp

/-! ## §4. Canonical `GroupTree` Helpers, `RegionStep`, `PsiReg`, and `PsiHyb` -/


theorem liftRegion_wf (cm : CodeMap) (rw : RegionWitness) :
    (liftRegion cm rw).Wf :=
  Func.wf_of_denote (liftRegionTFlat cm rw) rfl

theorem liftRegion_mid_wf (cm : CodeMap) (rw : RegionWitness) (t : LegalTarget)
    (hs : ((liftRegion cm rw).earlyOpt).body.supportsSource t = true) :
    ((liftRegion cm rw).mid t).Wf :=
  midEnd_ok t (liftRegion cm rw) ((liftRegion cm rw).mid t)
    (liftRegion_wf cm rw) (by simp [hs])

theorem checkGroupNodes_forall (cm : CodeMap) (rw : RegionWitness)
    (callees : List CalleeMeta) (pcs : List (BitVec 64)) :
    ∀ gs, checkGroupNodes cm rw callees pcs gs = true →
      ∀ g ∈ gs, checkGroupNode cm rw callees pcs g = true
  | [], _, _, h => by cases h
  | g :: gs, hchk, x, hx => by
      dsimp only [checkGroupNodes] at hchk
      rcases Bool.and_eq_true_iff.1 hchk with ⟨hg, hgs⟩
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact hg
      · exact checkGroupNodes_forall cm rw callees pcs gs hgs x hx'

theorem checkGroupNode_entryPc_mem :
    ∀ (cm : CodeMap) (rw : RegionWitness) (callees : List CalleeMeta)
      (pcs : List (BitVec 64)) (g : GroupTree),
      checkGroupNode cm rw callees pcs g = true → g.entryPc ∈ g.allPcs
  | _, _, _, _, .leaf pc, _ => by
      simp only [GroupTree.entryPc, GroupTree.allPcs]
      exact List.mem_cons_self
  | cm, rw, callees, pcs, .loop header nodes, hchk => by
      dsimp only [checkGroupNode] at hchk
      simp only [Bool.and_eq_true] at hchk
      have hin : header ∈ nodes.map GroupTree.entryPc := by
        simpa using hchk.1.2
      rw [List.mem_map] at hin
      rcases hin with ⟨c, hcMem, hcEq⟩
      have hsub := checkGroupNode_entryPc_mem cm rw callees
        (pushLabelPcs (nodes.map GroupTree.entryPc) pcs) c
        (checkGroupNodes_forall cm rw callees _ nodes hchk.2 c hcMem)
      rw [hcEq] at hsub
      simp only [GroupTree.entryPc, GroupTree.allPcs]
      exact List.mem_flatMap.2 ⟨c, hcMem, hsub⟩

theorem listNodup_false_append {xs ys : List (BitVec 64)} :
    listNodup (xs ++ ys) = true → ∀ x ∈ xs, ∀ y ∈ ys, x ≠ y := by
  induction xs with
  | nil => intro _ _ h; cases h
  | cons a xs ih =>
      intro hnd x hx y hy hxy
      dsimp only [listNodup, List.cons_append] at hnd
      simp only [Bool.and_eq_true] at hnd
      rcases List.mem_cons.1 hx with rfl | hx'
      · simp only [Bool.not_eq_true'] at hnd
        have hc : (xs ++ ys).contains x = true :=
          List.contains_iff_mem.2 (List.mem_append_right xs (hxy ▸ hy))
        rw [hnd.1] at hc; cases hc
      · exact ih hnd.2 x hx' y hy hxy

@[expose] def TupMemPred : (gs : List GroupTree) →
    Tup Cont (gs.map fun _ => regSig) → CodeSpec → Prop
  | [], (), _ => True
  | g :: gs, (J, Js), Pred =>
      (∀ r m, Pred g.entryPc ⟨r, m⟩ → J r.toRegsV.toTup m) ∧ TupMemPred gs Js Pred

theorem lsMatch_pushTup_group :
    ∀ (gs : List GroupTree) (Js : Tup Cont (gs.map fun _ => regSig))
      (pcs : List (BitVec 64)) (ls : List ((ts : List Ty) × Cont ts)) (Pred : CodeSpec),
      TupMemPred gs Js Pred → LsMatch pcs ls Pred →
      LsMatch (pushLabelPcs (gs.map GroupTree.entryPc) pcs) (pushTup Js ls) Pred
  | [], (), _, _, _, _, hls => hls
  | g :: gs, (J, Js), pcs, ls, Pred, ⟨hJ, hrest⟩, hls =>
      lsMatch_pushTup_group gs Js (g.entryPc :: pcs) (⟨regSig, J⟩ :: ls) Pred hrest
        (lsMatch_cons hJ hls)

/-- True iff `pc` belongs to a region in `wit` that uses `.memTableRo`. -/
@[expose] def isRoPc (wit : CfgWitness) (pc : BitVec 64) : Bool :=
  ((wit.regions.filter RegionWitness.hasMemTableRo).flatMap RegionWitness.allPcs).contains pc

/-- Conditional `WitRoOk` wrapper parameterized by `(useRo, wit, pc)`. -/
@[expose] def RoPred (useRo : Bool) (wit : CfgWitness) (pc : BitVec 64) (m : Mem 64) : Prop :=
  if useRo && isRoPc wit pc then WitRoOk wit m else True

@[expose] def RegionStepG (useRo : Bool) (cm : CodeMap) (wit : CfgWitness) (Ψ_cold : CodeSpec)
    (H : HaltPost) (Ψ : Xcap.Lfp.Pred (BitVec 64 × State)) : Xcap.Lfp.Pred (BitVec 64 × State) :=
  fun p => ∃ b, cm.lookupAddr p.1 = some b ∧
    (RoPred useRo wit p.1 p.2.mem →
      b.wp cm.symEnv (fun pc' st' =>
        if (wit.regions.flatMap RegionWitness.allPcs).contains pc' then
          (RoPred useRo wit pc' st'.mem → Ψ (pc', st')) ∧ Ψ_cold pc' st'
        else Ψ_cold pc' st') H (pushRegsV p.2.regs.toRegsV) p.2.mem)

@[expose] def RegionStep (cm : CodeMap) (wit : CfgWitness) (Ψ_cold : CodeSpec) (H : HaltPost)
    (Ψ : Xcap.Lfp.Pred (BitVec 64 × State)) : Xcap.Lfp.Pred (BitVec 64 × State) :=
  RegionStepG false cm wit Ψ_cold H Ψ

theorem blockFlat_wp_mono {ρ : SymEnv} {Ψ₁ Ψ₂ : CodeSpec} {H : HaltPost}
    (hΨ : ∀ pc st, Ψ₁ pc st → Ψ₂ pc st) :
    ∀ (b : BlockFlat) (vs : List ((t : Ty) × Val t)) (m : Mem 64),
      b.wp ρ Ψ₁ H vs m → b.wp ρ Ψ₂ H vs m
  | .let_ op k, vs, m, h => by
      dsimp only [BlockFlat.wp] at h ⊢
      cases hda : denoteArgs vs op.args with
      | none => rw [hda] at h; exact h
      | some args' =>
          rw [hda] at h
          exact Op.wp_mono (fun r hr => blockFlat_wp_mono hΨ k (pushTup r vs) m hr) h
  | .load t a k, vs, m, h => by
      dsimp only [BlockFlat.wp] at h ⊢
      cases hda : denoteArg vs a with
      | none => rw [hda] at h; exact h
      | some a' =>
          rw [hda] at h
          rcases h with ⟨v, hv, hk⟩
          exact ⟨v, hv, blockFlat_wp_mono hΨ k (⟨t, v⟩ :: vs) m hk⟩
  | .store v a k, vs, m, h => by
      dsimp only [BlockFlat.wp] at h ⊢
      cases hdv : denoteArg vs v <;> rw [hdv] at h; · exact h
      cases hda : denoteArg vs a <;> rw [hda] at h; · exact h
      exact ⟨h.1, blockFlat_wp_mono hΨ k vs _ h.2⟩
  | .codeAddr sym k, vs, m, ⟨a, ha, hk⟩ => ⟨a, ha, blockFlat_wp_mono hΨ k (⟨i64, a⟩ :: vs) m hk⟩
  | .jnz c t e, vs, m, h => by
      dsimp only [BlockFlat.wp] at h ⊢
      cases hdc : denoteArg vs c with
      | none => rw [hdc] at h; exact h
      | some c' =>
          rw [hdc] at h
          exact ⟨fun ht => blockFlat_wp_mono hΨ t vs m (h.1 ht),
                 fun hf => blockFlat_wp_mono hΨ e vs m (h.2 hf)⟩
  | .ijmp tgt nxt, vs, m, h => by
      dsimp only [BlockFlat.wp] at h ⊢
      cases h1 : denoteArg vs tgt with
      | none => rw [h1] at h; exact h
      | some tgt' =>
          cases h2 : denoteRegsExpr vs nxt with
          | none => rw [h1, h2] at h; exact h
          | some nxt' =>
              rw [h1, h2] at h
              dsimp only at h ⊢
              exact hΨ _ _ h
  | .halt _, _, _, h => h
  | .hlt, _, _, h => h

theorem regionStepG_mono (useRo : Bool) (cm : CodeMap) (wit : CfgWitness)
    (Ψ_cold : CodeSpec) (H : HaltPost) :
    Xcap.Lfp.mono (RegionStepG useRo cm wit Ψ_cold H) := by
  rintro Ψ₁ Ψ₂ hle ⟨pc, st⟩ ⟨b, hlu, hbp⟩
  refine ⟨b, hlu, fun hRo => blockFlat_wp_mono ?_ b _ _ (hbp hRo)⟩
  intro pc' st' h
  by_cases hc : (wit.regions.flatMap RegionWitness.allPcs).contains pc' = true
  · simp only [hc, ↓reduceIte] at h ⊢
    exact ⟨fun hRo' => hle (pc', st') (h.1 hRo'), h.2⟩
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact h

theorem regionStep_mono (cm : CodeMap) (wit : CfgWitness)
    (Ψ_cold : CodeSpec) (H : HaltPost) :
    Xcap.Lfp.mono (RegionStep cm wit Ψ_cold H) :=
  regionStepG_mono false cm wit Ψ_cold H

/-- Generalized least Knaster–Tarski code specification covering `wit.regions`. -/
@[expose] def PsiRegG (useRo : Bool) (cm : CodeMap) (wit : CfgWitness) (Ψ_cold : CodeSpec)
    (H : HaltPost) : CodeSpec :=
  fun pc st => Xcap.Lfp.lfp (RegionStepG useRo cm wit Ψ_cold H) (pc, st)

/-- Least Knaster–Tarski code specification covering all blocks inside `wit.regions`. -/
@[expose] def PsiReg (cm : CodeMap) (wit : CfgWitness) (Ψ_cold : CodeSpec)
    (H : HaltPost) : CodeSpec :=
  PsiRegG false cm wit Ψ_cold H

/-- Generalized hybrid code specification over `wit.regions` + `Ψ_cold`. -/
@[expose] def PsiHybG (useRo : Bool) (cm : CodeMap) (wit : CfgWitness) (Ψ_cold : CodeSpec)
    (H : HaltPost) : CodeSpec :=
  fun pc st =>
    if (wit.regions.flatMap RegionWitness.allPcs).contains pc then
      (RoPred useRo wit pc st.mem → PsiRegG useRo cm wit Ψ_cold H pc st) ∧ Ψ_cold pc st
    else Ψ_cold pc st

/-- Hybrid code specification combining verified Tier-S lifted regions (`PsiReg`) inside
`wit.allPcs` with cold/residual invariant `Ψ_cold`. -/
@[expose] def PsiHyb (cm : CodeMap) (wit : CfgWitness) (Ψ_cold : CodeSpec)
    (H : HaltPost) : CodeSpec :=
  fun pc st =>
    if (wit.regions.flatMap RegionWitness.allPcs).contains pc then
      PsiReg cm wit Ψ_cold H pc st ∧ Ψ_cold pc st
    else Ψ_cold pc st

theorem psiHybG_false_eq (cm : CodeMap) (wit : CfgWitness) (Ψ_cold : CodeSpec) (H : HaltPost) :
    PsiHybG false cm wit Ψ_cold H = PsiHyb cm wit Ψ_cold H := by
  funext pc st
  dsimp only [PsiHybG, PsiHyb, PsiReg, RoPred]
  by_cases hc : (wit.regions.flatMap RegionWitness.allPcs).contains pc = true
  · simp
  · simp


end LeanQbe.T.Unified
