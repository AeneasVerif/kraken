module

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

Top-level XCAP fixed-point, `TFlat.isMemFree` callee memory relocation, nested `GroupTree`
canonical induction, `Fn.mid` lifting, and hybrid soundness theorems (`witContifyEnv`,
`contify_psiReg_to_func_spec`, `contify_psiReg_to_mid_spec`, `checkAndLiftContify_cm_wp_to_mid`,
`checkAndLiftContify_hybrid_sound`), with `0` `@[expose]` on theorems and all `*Lemmas*`
imports private.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Unified

open LeanQbe.T
open LeanQbe.T.BedrockWord

/-! ## §1. Direct Prefix Independence for `liftContifyGroupNodes` -/

private def argVarsLt (d : Nat) {t : Ty} : Arg K t → Bool
  | .imm _ => true | .var i => decide (i < d)

private def argsVarsLt (d : Nat) : {ts : List Ty} → Tup (Arg K) ts → Bool
  | [], () => true | _ :: _, (a, as) => argVarsLt d a && argsVarsLt d as

private def regsVarsLt (d : Nat) (e : RegsExpr K) : Bool :=
  argVarsLt d e.sp && argVarsLt d e.rp && argVarsLt d e.rv &&
  argVarsLt d e.r1 && argVarsLt d e.r2 && argVarsLt d e.r3

private theorem argLt_of {d i : Nat} (h : decide (i < d) = true) : i < d := of_decide_eq_true h
private theorem of_argLt {d i : Nat} (h : i < d) : decide (i < d) = true := decide_eq_true h
theorem bAnd {a b : Bool} (h1 : a = true) (h2 : b = true) : (a && b) = true :=
  Bool.and_eq_true_iff.2 ⟨h1, h2⟩
private theorem bAnd6 {b1 b2 b3 b4 b5 b6 : Bool} (h1 : b1 = true) (h2 : b2 = true)
    (h3 : b3 = true) (h4 : b4 = true) (h5 : b5 = true) (h6 : b6 = true) :
    (b1 && b2 && b3 && b4 && b5 && b6) = true :=
  bAnd (bAnd (bAnd (bAnd (bAnd h1 h2) h3) h4) h5) h6

mutual
private def tfVarsLt (d : Nat) {rs : List Ty} : TFlat rs → Bool
  | .let_ (ts := ts) op k => argsVarsLt d op.args && tfVarsLt (d + ts.length) k
  | .load _ a k => argVarsLt d a && tfVarsLt (d + 1) k
  | .store v a k => argVarsLt d v && argVarsLt d a && tfVarsLt d k
  | .call _ bs args k => argsVarsLt d args && tfVarsLt (d + bs.length) k
  | .jnz c t e => argVarsLt d c && tfVarsLt d t && tfVarsLt d e
  | .jump _ args | .ret args | .exit _ args => argsVarsLt d args
  | .hlt => true | .group bodies k => tbVarsLt d bodies && tfVarsLt d k

private def tbVarsLt (d : Nat) {rs : List Ty} : {sig : List (List Ty)} → TBlocks rs sig → Bool
  | _, .nil => true | _, .cons (ts := ts) b bs => tfVarsLt (d + ts.length) b && tbVarsLt d bs
end

private theorem argVarsLt_mono {d d' : Nat} (hle : d ≤ d') {t : Ty} :
    (a : Arg K t) → argVarsLt d a = true → argVarsLt d' a = true
  | .imm _, _ => rfl | .var _, h => of_argLt (Nat.lt_of_lt_of_le (argLt_of h) hle)

private theorem argsVarsLt_mono {d d' : Nat} (hle : d ≤ d') :
    {ts : List Ty} → (as : Tup (Arg K) ts) → argsVarsLt d as = true → argsVarsLt d' as = true
  | [], (), _ => rfl
  | _ :: _, (a, as), h => let ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h
      bAnd (argVarsLt_mono hle a h1) (argsVarsLt_mono hle as h2)

mutual
private theorem tfVarsLt_mono {d d' : Nat} (hle : d ≤ d') {rs : List Ty} :
    (tf : TFlat rs) → tfVarsLt d tf = true → tfVarsLt d' tf = true
  | .let_ (ts := ts) op k, h => let ⟨ha, hk⟩ := Bool.and_eq_true_iff.1 h
      bAnd (argsVarsLt_mono hle op.args ha)
        (tfVarsLt_mono (Nat.add_le_add_right hle ts.length) k hk)
  | .load _ a k, h => let ⟨ha, hk⟩ := Bool.and_eq_true_iff.1 h
      bAnd (argVarsLt_mono hle a ha) (tfVarsLt_mono (Nat.add_le_add_right hle 1) k hk)
  | .store v a k, h => by
      dsimp only [tfVarsLt] at h ⊢; simp only [Bool.and_eq_true] at h
      exact bAnd (bAnd (argVarsLt_mono hle v h.1.1) (argVarsLt_mono hle a h.1.2))
        (tfVarsLt_mono hle k h.2)
  | .call _ bs args k, h => let ⟨ha, hk⟩ := Bool.and_eq_true_iff.1 h
      bAnd (argsVarsLt_mono hle args ha)
        (tfVarsLt_mono (Nat.add_le_add_right hle bs.length) k hk)
  | .jnz c t e, h => by
      dsimp only [tfVarsLt] at h ⊢; simp only [Bool.and_eq_true] at h
      exact bAnd (bAnd (argVarsLt_mono hle c h.1.1) (tfVarsLt_mono hle t h.1.2))
        (tfVarsLt_mono hle e h.2)
  | .jump _ args, h | .ret args, h | .exit _ args, h => argsVarsLt_mono hle args h
  | .hlt, _ => rfl
  | .group bodies k, h => let ⟨hb, hk⟩ := Bool.and_eq_true_iff.1 h
      bAnd (tbVarsLt_mono hle bodies hb) (tfVarsLt_mono hle k hk)

private theorem tbVarsLt_mono {d d' : Nat} (hle : d ≤ d') {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) → tbVarsLt d tb = true → tbVarsLt d' tb = true
  | _, .nil, _ => rfl
  | _, .cons (ts := ts) b bs, h => let ⟨hb, hbs⟩ := Bool.and_eq_true_iff.1 h
      bAnd (tfVarsLt_mono (Nat.add_le_add_right hle ts.length) b hb) (tbVarsLt_mono hle bs hbs)
end

private theorem denoteArg_prefix_lt {V : Ty → Type} {bvs vsTail : List ((t : Ty) × V t)}
    {t : Ty} {a : Arg K t} (h : argVarsLt bvs.length a = true) :
    denoteArg (bvs ++ vsTail) a = denoteArg bvs a := by
  cases a with | imm _ => rfl | var _ =>
    dsimp only [denoteArg, lookupV]; rw [listGet?_append_left bvs vsTail (argLt_of h)]

private theorem denoteArgs_prefix_lt {V : Ty → Type} {bvs vsTail : List ((t : Ty) × V t)} :
    {ts : List Ty} → {as : Tup (Arg K) ts} → argsVarsLt bvs.length as = true →
    denoteArgs (bvs ++ vsTail) as = denoteArgs bvs as
  | [], (), _ => rfl
  | _ :: _, (_, _), h => by
      rcases Bool.and_eq_true_iff.1 h with ⟨h1, h2⟩
      dsimp only [denoteArgs]; rw [denoteArg_prefix_lt h1, denoteArgs_prefix_lt h2]

mutual
private theorem denote_tfVarsLt_prefix {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (tf : TFlat rs) → ∀ (bvs vsTail : List ((t : Ty) × V t)) (ls : List ((ts : List Ty) × L ts))
      {d : Nat}, bvs.length = d → tfVarsLt d tf = true →
      denote V L tf (bvs ++ vsTail) ls = denote V L tf bvs ls
  | .let_ op k, bvs, vsTail, ls, d, hL, h => by
      rcases Bool.and_eq_true_iff.1 h with ⟨ha, hk⟩; dsimp only [denote]
      rw [denoteArgs_prefix_lt (hL.symm ▸ ha)]
      cases denoteArgs bvs op.args with | none => rfl | some _ =>
        dsimp only; congr 1; funext xs; rw [pushTup_append]
        exact denote_tfVarsLt_prefix k (pushTup xs bvs) vsTail ls
          (by rw [pushTup_length, hL, Nat.add_comm]) hk
  | .load t a k, bvs, vsTail, ls, d, hL, h => by
      rcases Bool.and_eq_true_iff.1 h with ⟨ha, hk⟩; dsimp only [denote]
      rw [denoteArg_prefix_lt (hL.symm ▸ ha)]
      cases denoteArg bvs a with | none => rfl | some _ =>
        dsimp only; congr 1; funext v
        exact denote_tfVarsLt_prefix k (⟨t, v⟩ :: bvs) vsTail ls (by simp [hL]) hk
  | .store v a k, bvs, vsTail, ls, d, hL, h => by
      dsimp only [tfVarsLt] at h; simp only [Bool.and_eq_true] at h; dsimp only [denote]
      rw [denoteArg_prefix_lt (hL.symm ▸ h.1.1), denoteArg_prefix_lt (hL.symm ▸ h.1.2)]
      cases denoteArg bvs v <;> cases denoteArg bvs a <;> try rfl
      exact congrArg _ (denote_tfVarsLt_prefix k bvs vsTail ls hL h.2)
  | .call _ _ args k, bvs, vsTail, ls, d, hL, h => by
      rcases Bool.and_eq_true_iff.1 h with ⟨ha, hk⟩; dsimp only [denote]
      rw [denoteArgs_prefix_lt (hL.symm ▸ ha)]
      cases denoteArgs bvs args with | none => rfl | some _ =>
        dsimp only; congr 1; funext xs; rw [pushTup_append]
        exact denote_tfVarsLt_prefix k (pushTup xs bvs) vsTail ls
          (by rw [pushTup_length, hL, Nat.add_comm]) hk
  | .jnz c t e, bvs, vsTail, ls, d, hL, h => by
      dsimp only [tfVarsLt] at h; simp only [Bool.and_eq_true] at h; dsimp only [denote]
      rw [denoteArg_prefix_lt (hL.symm ▸ h.1.1)]
      cases denoteArg bvs c with | none => rfl | some _ =>
        rw [denote_tfVarsLt_prefix t bvs vsTail ls hL h.1.2,
            denote_tfVarsLt_prefix e bvs vsTail ls hL h.2]
  | .jump _ _, bvs, vsTail, _, _, hL, h | .ret _, bvs, vsTail, _, _, hL, h |
    .exit _ _, bvs, vsTail, _, _, hL, h => by
      dsimp only [tfVarsLt] at h; dsimp only [denote]; rw [denoteArgs_prefix_lt (hL.symm ▸ h)]
  | .hlt, _, _, _, _, _, _ => rfl
  | .group bodies k, bvs, vsTail, ls, d, hL, h => by
      rcases Bool.and_eq_true_iff.1 h with ⟨hb, hk⟩; dsimp only [denote]; congr 1
      · funext Js; exact denoteB_tbVarsLt_prefix bodies bvs vsTail (pushTup Js ls) hL hb
      · funext Js; exact denote_tfVarsLt_prefix k bvs vsTail (pushTup Js ls) hL hk

private theorem denoteB_tbVarsLt_prefix {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    ∀ (bvs vsTail : List ((t : Ty) × V t)) (ls : List ((ts : List Ty) × L ts)) {d : Nat},
      bvs.length = d → tbVarsLt d tb = true →
      denoteB V L tb (bvs ++ vsTail) ls = denoteB V L tb bvs ls
  | _, .nil, _, _, _, _, _, _ => rfl
  | _, .cons _ _, bvs, vsTail, ls, d, hL, h => by
      rcases Bool.and_eq_true_iff.1 h with ⟨hb, hbs⟩; dsimp only [denoteB]; congr 1
      · funext xs; rw [pushTup_append]
        exact denote_tfVarsLt_prefix _ (pushTup xs bvs) vsTail ls
          (by rw [pushTup_length, hL, Nat.add_comm]) hb
      · exact denoteB_tbVarsLt_prefix _ bvs vsTail ls hL hbs
end

private theorem regsVarsLt_toTup {d : Nat} {e : RegsExpr K} (h : regsVarsLt d e = true) :
    argsVarsLt d e.toTup = true := by
  dsimp only [regsVarsLt] at h; simp only [Bool.and_eq_true] at h
  exact bAnd h.1.1.1.1.1 (bAnd h.1.1.1.1.2 (bAnd h.1.1.1.2 (bAnd h.1.1.2
    (bAnd h.1.2 (bAnd h.2 rfl)))))

private theorem argsVarsLt_append {d : Nat} : {as bs : List Ty} → {xs : Tup (Arg K) as} →
    {ys : Tup (Arg K) bs} → argsVarsLt d xs = true → argsVarsLt d ys = true →
    argsVarsLt d (tupAppend xs ys) = true
  | [], _, (), _, _, hy => hy
  | _ :: _, _, (_, _), _, hx, hy =>
      let ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 hx; bAnd h1 (argsVarsLt_append h2 hy)

private theorem argVarsLt_shift (k d : Nat) {t : Ty} :
    (a : Arg K t) → argVarsLt d a = true → argVarsLt (k + d) (shiftArg k a) = true
  | .imm _, _ => rfl | .var _, h => of_argLt (by have := argLt_of h; omega)

private theorem regsVarsLt_shift (k d : Nat) (e : RegsExpr K) (h : regsVarsLt d e = true) :
    regsVarsLt (k + d) (shiftRegsExpr k e) = true := by
  dsimp only [regsVarsLt] at h; simp only [Bool.and_eq_true] at h
  exact bAnd6 (argVarsLt_shift k d _ h.1.1.1.1.1) (argVarsLt_shift k d _ h.1.1.1.1.2)
    (argVarsLt_shift k d _ h.1.1.1.2) (argVarsLt_shift k d _ h.1.1.2)
    (argVarsLt_shift k d _ h.1.2) (argVarsLt_shift k d _ h.2)

theorem checkArg_idx_lt {Γ : List Ty} {t : Ty} {i : Nat}
    (h : checkArg Γ t (.var i) = true) : i < Γ.length := by
  apply listGet?_isSome_lt Γ; dsimp only [checkArg] at h; cases hg : listGet? Γ i <;> simp_all

private theorem listGet?_lt_ne_none {α : Type} :
    ∀ (xs : List α) (i : Nat), i < xs.length → listGet? xs i ≠ none
  | [], _, h => absurd h (Nat.not_lt_zero _) | _ :: _, 0, _ => by simp [listGet?]
  | _ :: xs, _ + 1, h => listGet?_lt_ne_none xs _ (Nat.lt_of_succ_lt_succ h)

private theorem argVarsLt_remap (Γ : List Ty) (d : Nat) (em : List Nat) (hd : 0 < d)
    (heLen : em.length = Γ.length) {t : Ty} (a : Arg K t) (ha : checkArg Γ t a = true) :
    argVarsLt d (remapArg d em a) = true := by
  cases a with | imm _ => rfl | var idx =>
    have hi := checkArg_idx_lt ha; dsimp only [remapArg]; cases hg : listGet? em idx with
    | none => exact absurd hg (listGet?_lt_ne_none em idx (by rw [heLen]; exact hi))
    | some _ => exact of_argLt (by omega)

private theorem argsVarsLt_remap (Γ : List Ty) (d : Nat) (em : List Nat) (hd : 0 < d)
    (heLen : em.length = Γ.length) : {ts : List Ty} → (as : Tup (Arg K) ts) →
    checkArgs Γ as = true → argsVarsLt d (remapArgs d em as) = true
  | [], (), _ => rfl
  | _ :: _, (a, as), h => let ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h
      bAnd (argVarsLt_remap Γ d em hd heLen a h1) (argsVarsLt_remap Γ d em hd heLen as h2)

private theorem regsVarsLt_remap (Γ : List Ty) (d : Nat) (em : List Nat) (hd : 0 < d)
    (heLen : em.length = Γ.length) (e : RegsExpr K) (he : checkRegsExpr Γ e = true) :
    regsVarsLt d (remapRegsExpr d em e) = true := by
  dsimp only [checkRegsExpr] at he; simp only [Bool.and_eq_true] at he
  exact bAnd6 (argVarsLt_remap Γ d em hd heLen _ he.1.1.1.1.1)
    (argVarsLt_remap Γ d em hd heLen _ he.1.1.1.1.2) (argVarsLt_remap Γ d em hd heLen _ he.1.1.1.2)
    (argVarsLt_remap Γ d em hd heLen _ he.1.1.2) (argVarsLt_remap Γ d em hd heLen _ he.1.2)
    (argVarsLt_remap Γ d em hd heLen _ he.2)

private theorem pushEnvMap_ctx_len : ∀ (ts : List Ty) (d : Nat) (em : List Nat) (Γ : List Ty),
    em.length = Γ.length → (pushEnvMap ts d em).length = (pushTypes ts Γ).length
  | [], _, _, _, he => he
  | a :: ts, d, em, Γ, he => pushEnvMap_ctx_len ts (d + 1) (d :: em) (a :: Γ) (by simp [he])

private theorem argsVarsLt_mkSlotArgs (d : Nat) (hd : 0 < d) :
    ∀ (n : Nat) (sLvls : List Nat), argsVarsLt d (mkSlotArgs d n sLvls) = true
  | 0, _ => rfl | _ + 1, [] => bAnd rfl (argsVarsLt_mkSlotArgs d hd _ [])
  | _ + 1, _ :: ls => bAnd (of_argLt (by omega)) (argsVarsLt_mkSlotArgs d hd _ ls)

private theorem argsVarsLt_mkJumpTuple (d sp0Lvl nSlots : Nat) (nxt : RegsExpr K)
    (sLvls : List Nat) (hd : 0 < d) (hN : regsVarsLt d nxt = true) :
    argsVarsLt d (mkJumpTuple d sp0Lvl nxt nSlots sLvls) = true := by
  cases nSlots with | zero => exact regsVarsLt_toTup hN | succ k =>
    exact argsVarsLt_append (regsVarsLt_toTup hN)
      (bAnd (of_argLt (by omega)) (argsVarsLt_mkSlotArgs d hd (k + 1) sLvls))

private theorem argsVarsLt_shift (k d : Nat) : {ts : List Ty} → (as : Tup (Arg K) ts) →
    argsVarsLt d as = true → argsVarsLt (k + d) (shiftArgTup k as) = true
  | [], (), _ => rfl | _ :: _, (a, as), h => let ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h
      bAnd (argVarsLt_shift k d a h1) (argsVarsLt_shift k d as h2)

private theorem tfVarsLt_lowerContJumpTo {rs : List Ty} (d nSlots : Nat) (pcs : List (BitVec 64))
    (tPc : BitVec 64) (args : Tup (Arg K) (contSig nSlots)) (h : argsVarsLt d args = true) :
    tfVarsLt d (lowerContJumpTo (rs := rs) nSlots pcs tPc args) = true := by
  dsimp only [lowerContJumpTo]; cases findLabelIdx pcs tPc <;> simp [tfVarsLt, h]

private theorem tfVarsLt_lowerContStride {rs : List Ty} (d nSlots : Nat) (pcs : List (BitVec 64))
    (iv : Nat) (args : Tup (Arg K) (contSig nSlots)) (hIdx : iv < d)
    (hA : argsVarsLt d args = true) :
    ∀ (targets : List (BitVec 64)) (k cs : Nat),
      tfVarsLt (d + cs) (lowerContStride (rs := rs) nSlots pcs iv args k cs targets) = true
  | [], _, _ => rfl
  | [tPc], _, cs => tfVarsLt_lowerContJumpTo (d + cs) nSlots pcs tPc _
      (by rw [Nat.add_comm d cs]; exact argsVarsLt_shift cs d args hA)
  | tPc :: a :: rest, k, cs => by
      have hj := tfVarsLt_lowerContJumpTo (rs := rs) (d + (cs + 1)) nSlots pcs tPc _
        (by rw [Nat.add_comm d (cs + 1)]; exact argsVarsLt_shift (cs + 1) d args hA)
      have hs := tfVarsLt_lowerContStride (rs := rs) d nSlots pcs iv args hIdx hA
        (a :: rest) (k + 1) (cs + 1)
      dsimp only [lowerContStride, tfVarsLt, op2, argsVarsLt, List.length_cons, List.length_nil]
      rw [show d + cs + 1 = d + (cs + 1) by omega]
      exact bAnd (bAnd (of_argLt (by omega)) (bAnd rfl rfl))
        (bAnd (bAnd (of_argLt (by omega)) hj) hs)

private theorem tfVarsLt_flushFrameAux {rs : List Ty} (sp0Lvl : Nat) (kCont : TFlat rs)
    (sCount dBase : Nat) (hkP : tfVarsLt (dBase + sCount) kCont = true) :
    ∀ (k : Nat) (sLvls : List Nat) (d : Nat), 0 < d → d + sLvls.length = dBase + sCount →
      tfVarsLt d (flushFrameAux sp0Lvl k sLvls d kCont) = true
  | _, [], d, _, hex => by dsimp only [flushFrameAux]; simp at hex; rw [hex]; exact hkP
  | k, _ :: rest, d, hd, hex => by
      have hr := tfVarsLt_flushFrameAux sp0Lvl kCont sCount dBase hkP (k + 1) rest (d + 1)
        (by omega) (by simp at hex; omega)
      dsimp only [flushFrameAux, tfVarsLt, op2, argsVarsLt, List.length_cons, List.length_nil]
      exact bAnd (bAnd (of_argLt (by omega)) (bAnd rfl rfl))
        (bAnd (bAnd (of_argLt (by omega)) (of_argLt (by omega))) hr)

private theorem tfVarsLt_flushFrame {rs : List Ty} (sp0Lvl : Nat) (sLvls : List Nat) (d : Nat)
    (kCont : Nat → TFlat rs) (hd : 0 < d)
    (hkP : tfVarsLt (d + sLvls.length) (kCont (d + sLvls.length)) = true) :
    tfVarsLt d (flushFrame sp0Lvl sLvls d kCont) = true :=
  tfVarsLt_flushFrameAux sp0Lvl _ sLvls.length d hkP 0 sLvls d hd rfl

private theorem tfVarsLt_lowerUnpromotedTail (cm : CodeMap) :
    ∀ (b : BlockFlat) (Γ : List Ty) (d : Nat) (em : List Nat),
      0 < d → em.length = Γ.length → b.wfCheck Γ = true →
      tfVarsLt d (lowerUnpromotedTail cm b d em) = true
  | .let_ (ts := ts) op k, Γ, d, em, hd, heLen, hwf => let ⟨ha, hk⟩ := Bool.and_eq_true_iff.1 hwf
      bAnd (argsVarsLt_remap Γ d em hd heLen op.args ha) (tfVarsLt_lowerUnpromotedTail cm k
        (pushTypes ts Γ) (d + ts.length) (pushEnvMap ts d em) (by omega)
        (pushEnvMap_ctx_len ts d em Γ heLen) hk)
  | .load t a k, Γ, d, em, hd, heLen, hwf => let ⟨ha, hk⟩ := Bool.and_eq_true_iff.1 hwf
      bAnd (argVarsLt_remap Γ d em hd heLen a ha) (tfVarsLt_lowerUnpromotedTail cm k (t :: Γ)
        (d + 1) (d :: em) (by omega) (by simp [heLen]) hk)
  | .store v a k, Γ, d, em, hd, heLen, hwf => by
      dsimp only [BlockFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      exact bAnd (bAnd (argVarsLt_remap Γ d em hd heLen v hwf.1.1)
        (argVarsLt_remap Γ d em hd heLen a hwf.1.2))
        (tfVarsLt_lowerUnpromotedTail cm k Γ d em hd heLen hwf.2)
  | .codeAddr sym k, Γ, d, em, hd, heLen, hwf => by
      dsimp only [lowerUnpromotedTail]; cases cm.addrOf? sym with | none => rfl | some _ =>
        exact bAnd (bAnd rfl rfl) (tfVarsLt_lowerUnpromotedTail cm k (i64 :: Γ) (d + 1) (d :: em)
          (by omega) (by simp [heLen]) hwf)
  | .jnz c t e, Γ, d, em, hd, heLen, hwf => by
      dsimp only [BlockFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      exact bAnd (bAnd (argVarsLt_remap Γ d em hd heLen c hwf.1.1)
        (tfVarsLt_lowerUnpromotedTail cm t Γ d em hd heLen hwf.1.2))
        (tfVarsLt_lowerUnpromotedTail cm e Γ d em hd heLen hwf.2)
  | .ijmp tgt nxt, Γ, d, em, hd, heLen, hwf => let ⟨ht, hn⟩ := Bool.and_eq_true_iff.1 hwf
      bAnd (argVarsLt_remap Γ d em hd heLen tgt ht)
        (regsVarsLt_toTup (regsVarsLt_remap Γ d em hd heLen nxt hn))
  | .halt c, Γ, d, em, hd, heLen, hwf => bAnd (argVarsLt_remap Γ d em hd heLen c hwf) rfl
  | .hlt, _, _, _, _, _, _ => rfl

private theorem tfVarsLt_emitAliasGuard {rs : List Ty} (sp0Lvl nSlots d bytes : Nat)
    (aT : Arg K i64) (tB fB : TFlat rs) (hd : 0 < d) (ha : argVarsLt d aT = true)
    (ht : tfVarsLt (d + 5) tB = true) (hf : tfVarsLt (d + 5) fB = true) :
    tfVarsLt d (emitAliasGuard sp0Lvl nSlots d aT bytes tB fB) = true := by
  have ha1 := argVarsLt_shift 1 d aT ha; rw [Nat.add_comm 1 d] at ha1
  dsimp only [emitAliasGuard, tfVarsLt, op2, argsVarsLt, List.length_cons, List.length_nil]
  refine bAnd (bAnd (of_argLt (by omega)) (bAnd rfl rfl))
    (bAnd (bAnd ha1 (bAnd (of_argLt (by omega)) rfl))
    (bAnd (bAnd rfl (bAnd (of_argLt (by omega)) rfl))
    (bAnd (bAnd (of_argLt (by omega)) (bAnd rfl rfl))
    (bAnd (bAnd (of_argLt (by omega)) (bAnd (of_argLt (by omega)) rfl))
      (bAnd (bAnd (of_argLt (by omega)) (by simpa [Nat.add_assoc] using ht))
        (by simpa [Nat.add_assoc] using hf))))))

private theorem tfVarsLt_lowerContGuarded (nSlots sp0Lvl : Nat) (sLvls : List Nat)
    (pcs : List (BitVec 64)) (tgt : Arg K i64) (nxt : RegsExpr K) (d : Nat) (hd : 0 < d)
    (htgt : argVarsLt d tgt = true) (hnxt : regsVarsLt d nxt = true) :
    ∀ (targets : List (BitVec 64)) (cs : Nat),
      tfVarsLt (d + cs) (lowerContGuarded nSlots sp0Lvl sLvls pcs tgt nxt d cs targets) = true
  | [], cs => tfVarsLt_flushFrame sp0Lvl sLvls (d + cs) _ (by omega) (by
      have h1 := argVarsLt_shift (cs + sLvls.length) d tgt htgt
      have h2 := regsVarsLt_toTup (regsVarsLt_shift (cs + sLvls.length) d nxt hnxt)
      rw [show cs + sLvls.length + d = d + cs + sLvls.length by omega] at h1 h2; exact bAnd h1 h2)
  | hPc :: rest, cs => by
      have htC := argVarsLt_shift cs d tgt htgt; rw [Nat.add_comm cs d] at htC
      have hnC := regsVarsLt_shift (cs + 1) d nxt hnxt
      rw [show cs + 1 + d = d + cs + 1 by omega] at hnC
      have hj := tfVarsLt_lowerContJumpTo (rs := RegionAbi.retEnvelope.retSig) (d + cs + 1)
        nSlots pcs hPc _ (argsVarsLt_mkJumpTuple (d + cs + 1) sp0Lvl nSlots _ sLvls (by omega) hnC)
      have hr := tfVarsLt_lowerContGuarded nSlots sp0Lvl sLvls pcs tgt nxt d hd htgt hnxt
        rest (cs + 1)
      rw [show d + (cs + 1) = d + cs + 1 by omega] at hr
      dsimp only [lowerContGuarded, tfVarsLt, op2, argsVarsLt, List.length_cons, List.length_nil]
      exact bAnd (bAnd htC (bAnd rfl rfl)) (bAnd (bAnd (of_argLt (by omega)) hj) hr)

private theorem regsVarsLt_call_ret (d len k : Nat) (hk : k + 5 < len) :
    regsVarsLt (d + len) ⟨.var (d + len - 1 - (d + k)), .var (d + len - 1 - (d + (k + 1))),
      .var (d + len - 1 - (d + (k + 2))), .var (d + len - 1 - (d + (k + 3))),
      .var (d + len - 1 - (d + (k + 4))), .var (d + len - 1 - (d + (k + 5)))⟩ = true :=
  bAnd6 (of_argLt (by omega)) (of_argLt (by omega)) (of_argLt (by omega))
    (of_argLt (by omega)) (of_argLt (by omega)) (of_argLt (by omega))

private theorem tfVarsLt_liftContEdgeMapped (abi : RegionAbi) (nSlots sp0Lvl : Nat)
    (sLvls : List Nat) (pcs : List (BitVec 64)) (st : ContSymState) (d : Nat) (em : List Nat)
    (tgtRaw : Arg K i64) (nxtRaw : RegsExpr K) (kind : EdgeKind) (hd : 0 < d)
    (heLen : em.length = st.ctx.length)
    (htgt : checkArg st.ctx i64 tgtRaw = true) (hnxt : checkRegsExpr st.ctx nxtRaw = true) :
    tfVarsLt d (liftContEdgeMapped abi nSlots sp0Lvl sLvls pcs st d em tgtRaw nxtRaw kind) =
      true := by
  have htgtR := argVarsLt_remap st.ctx d em hd heLen tgtRaw htgt
  have hnxtR := regsVarsLt_remap st.ctx d em hd heLen nxtRaw hnxt
  have hjArgs := argsVarsLt_mkJumpTuple d sp0Lvl nSlots _ sLvls hd hnxtR
  have hIdx : ∀ lvl : Nat, (let bIdx := st.env.length - 1 - lvl; match listGet? em bIdx with
      | some tl => d - 1 - tl | none => 0) < d := fun lvl => by
    dsimp only; split
    · exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.sub_lt hd Nat.zero_lt_one)
    · exact hd
  dsimp only [liftContEdgeMapped]; cases kind with
  | direct tPc => exact tfVarsLt_lowerContJumpTo d nSlots pcs tPc _ hjArgs
  | select tPc ePc =>
      cases st.evalArg tgtRaw <;> try rfl
      exact bAnd (bAnd (of_argLt (hIdx _)) (tfVarsLt_lowerContJumpTo d nSlots pcs tPc _ hjArgs))
        (tfVarsLt_lowerContJumpTo d nSlots pcs ePc _ hjArgs)
  | strideTable _ targets needGuard =>
      cases needGuard with
      | false =>
          cases st.evalArg tgtRaw <;> try rfl
          exact tfVarsLt_lowerContStride d nSlots pcs _ _ (hIdx _) hjArgs targets 0 0
      | true =>
          cases abi with
          | contified _ => rfl
          | retEnvelope =>
              cases st.evalArg tgtRaw <;> try rfl
              rename_i _ lvl
              let iv := let bIdx := st.env.length - 1 - lvl; match listGet? em bIdx with
                | some tl => d - 1 - tl | none => 0
              have hnxt1 := regsVarsLt_remap st.ctx (d + 1) em (by omega) heLen nxtRaw hnxt
              have hStr := tfVarsLt_lowerContStride (rs := RegionAbi.retEnvelope.retSig)
                (d + 1) nSlots pcs (iv + 1) (mkJumpTuple (d + 1) sp0Lvl
                  (remapRegsExpr (d + 1) em nxtRaw) nSlots sLvls) (Nat.succ_lt_succ (hIdx lvl))
                (argsVarsLt_mkJumpTuple (d + 1) sp0Lvl nSlots _ sLvls (by omega) hnxt1)
                targets 0 0
              rw [Nat.add_zero] at hStr
              have hFl := tfVarsLt_flushFrame sp0Lvl sLvls (d + 1) (fun _ => mkRetEnvelope
                (shiftArg (1 + sLvls.length) (remapArg d em tgtRaw))
                (shiftRegsExpr (1 + sLvls.length) (remapRegsExpr d em nxtRaw))) (by omega) (by
                have h1 := argVarsLt_shift (1 + sLvls.length) d _ htgtR
                have h2 := regsVarsLt_toTup (regsVarsLt_shift (1 + sLvls.length) d _ hnxtR)
                rw [show 1 + sLvls.length + d = d + 1 + sLvls.length by omega] at h1 h2
                exact bAnd h1 h2)
              dsimp only [tfVarsLt, op2, argsVarsLt, List.length_cons, List.length_nil]
              exact bAnd (bAnd (of_argLt (hIdx lvl)) (bAnd rfl rfl))
                (bAnd (bAnd (of_argLt (by omega)) hStr) hFl)
  | memTableGuarded _ _ | memTableRo _ _ _ => exact bAnd rfl rfl
  | contCall _ _ dualRet retPc altRetPc? =>
      cases abi with
      | contified _ => rfl
      | retEnvelope =>
          cases dualRet with
          | false =>
              simp only [Bool.false_eq_true, ↓reduceIte, tfVarsLt, RegionAbi.retSig, regSig,
                List.length_cons, List.length_nil]
              exact bAnd (regsVarsLt_toTup hnxtR) (tfVarsLt_lowerContJumpTo (d + 6) nSlots pcs
                retPc _ (argsVarsLt_mkJumpTuple (d + 6) sp0Lvl nSlots _ sLvls (by omega)
                  (regsVarsLt_call_ret d 6 0 (by omega))))
          | true =>
              cases altRetPc? with | none => rfl | some altPc =>
                have hS7 : (RegionAbi.contified true).retSig.length = 7 := rfl
                dsimp only [tfVarsLt]; simp only [hS7, ↓reduceIte]
                have hR7 := regsVarsLt_call_ret d 7 1 (by omega)
                exact bAnd (regsVarsLt_toTup hnxtR) (bAnd (bAnd (of_argLt (by omega))
                  (tfVarsLt_lowerContJumpTo (d + 7) nSlots pcs altPc _
                    (argsVarsLt_mkJumpTuple (d + 7) sp0Lvl nSlots _ sLvls (by omega) hR7)))
                  (tfVarsLt_lowerContJumpTo (d + 7) nSlots pcs retPc _
                    (argsVarsLt_mkJumpTuple (d + 7) sp0Lvl nSlots _ sLvls (by omega) hR7)))
  | contRet isAlt =>
      cases abi with
      | retEnvelope => cases isAlt <;> rfl
      | contified dualRet =>
          cases dualRet <;> cases isAlt
          · exact regsVarsLt_toTup hnxtR
          · rfl
          · dsimp only [tfVarsLt, RegionAbi.retSig, argsVarsLt, argVarsLt]
            exact bAnd rfl (regsVarsLt_toTup hnxtR)
          · dsimp only [tfVarsLt, RegionAbi.retSig, argsVarsLt, argVarsLt]
            exact bAnd rfl (regsVarsLt_toTup hnxtR)
  | guarded hotTargets =>
      cases abi with
      | retEnvelope =>
          exact tfVarsLt_lowerContGuarded nSlots sp0Lvl sLvls pcs _ _ d hd htgtR
            hnxtR hotTargets 0
      | contified _ => rfl
  | bailout =>
      cases abi with
      | retEnvelope => exact tfVarsLt_flushFrame sp0Lvl sLvls d _ hd (by
          have h1 := argVarsLt_shift sLvls.length d _ htgtR
          have h2 := regsVarsLt_toTup (regsVarsLt_shift sLvls.length d _ hnxtR)
          rw [Nat.add_comm sLvls.length d] at h1 h2; exact bAnd h1 h2)
      | contified _ => rfl

private theorem tfVarsLt_liftContifyBlock (cm : CodeMap) (abi : RegionAbi) (pf : PrivFrameCfg)
    (rw : RegionWitness) (pcs : List (BitVec 64)) (pc : BitVec 64) :
    ∀ (b : BlockFlat) (path : BranchPath) (st : ContSymState) (d : Nat) (em sLvls : List Nat),
      0 < d → em.length = st.ctx.length → b.wfCheck st.ctx = true →
      tfVarsLt d (liftContifyBlock cm abi pf rw pcs pc b path st d em sLvls) = true
  | .let_ (ts := ts) op k, path, st, d, em, sLvls, hd, heLen, hwf =>
      let ⟨ha, hk⟩ := Bool.and_eq_true_iff.1 hwf
      bAnd (argsVarsLt_remap st.ctx d em hd heLen op.args ha)
        (tfVarsLt_liftContifyBlock cm abi pf rw pcs pc k path _ (d + ts.length)
          (pushEnvMap ts d em) sLvls (by omega) (pushEnvMap_ctx_len ts d em st.ctx heLen) hk)
  | .load t a k, path, st, d, em, sLvls, hd, heLen, hwf => by
      rcases Bool.and_eq_true_iff.1 hwf with ⟨ha, hk⟩
      have haR := argVarsLt_remap st.ctx d em hd heLen a ha
      have hCont : ∀ {d' em'}, 0 < d' → em'.length = (t :: st.ctx).length →
          tfVarsLt d' (liftContifyBlock cm abi pf rw pcs pc k path
            { st with env := .top :: st.env, ctx := t :: st.ctx } d' em' sLvls) = true :=
        fun hd' he' => tfVarsLt_liftContifyBlock cm abi pf rw pcs pc k path _ _ _ sLvls hd' he' hk
      have hNs : tfVarsLt d (lowerNonSlotLoad cm abi pf t a st d em sLvls k fun d' em' =>
          liftContifyBlock cm abi pf rw pcs pc k path
            { st with env := .top :: st.env, ctx := t :: st.ctx } d' em' sLvls) = true := by
        dsimp only [lowerNonSlotLoad]; split
        · exact bAnd haR (hCont (by omega) (by simp [heLen]))
        · cases abi with
          | contified _ => rfl
          | retEnvelope =>
              split
              · refine tfVarsLt_emitAliasGuard 6 pf.numSlots d t.bytes _ _ _ hd haR ?_ ?_
                · have ha5 := argVarsLt_shift 5 d _ haR; rw [Nat.add_comm 5 d] at ha5
                  have hc := hCont (d' := d + 6) (em' := (d + 5) :: em) (by omega) (by simp [heLen])
                  rw [show d + 5 + 1 = d + 6 by omega]; exact bAnd ha5 hc
                · exact tfVarsLt_flushFrame 6 sLvls (d + 5) _ (by omega)
                    (tfVarsLt_lowerUnpromotedTail cm (.load t a k) st.ctx (d + 5 + sLvls.length)
                      em (by omega) heLen (bAnd ha hk))
              · rfl
      dsimp only [liftContifyBlock]; by_cases hn0 : pf.numSlots = 0
      · simp only [hn0, beq_self_eq_true, ↓reduceIte]
        exact bAnd haR (hCont (by omega) (by simp [heLen]))
      · simp only [beq_false_of_ne hn0, Bool.false_eq_true, ↓reduceIte]
        cases t with
        | bits n =>
            by_cases h64 : n = 64
            · subst h64
              cases hSlot : spSlotOf? pf.numSlots (st.evalArg a) with
              | none => exact hNs
              | some sIdx =>
                  cases hGl : listGet? sLvls sIdx with
                  | none =>
                      change tfVarsLt d (match listGet? sLvls sIdx with
                        | some _ => _ | none => .hlt) = true
                      rw [hGl]; rfl
                  | some sLvl =>
                      change tfVarsLt d (match listGet? sLvls sIdx with
                        | some sLvl => .let_ (op1 (.copy i64) (.var (d - 1 - sLvl)))
                            (liftContifyBlock cm abi pf rw pcs pc k path
                              { st with env := .top :: st.env, ctx := i64 :: st.ctx }
                              (d + 1) (d :: em) sLvls)
                        | none => .hlt) = true
                      rw [hGl]; dsimp only [tfVarsLt, op1, argsVarsLt, List.length_cons,
                        List.length_nil]
                      exact bAnd (bAnd (of_argLt (by omega)) rfl)
                        (hCont (d' := d + 1) (em' := d :: em) (by omega) (by simp [heLen]))
            · cases n with
              | zero => exact hNs
              | succ m =>
                  split
                  · rename_i heq; exact absurd (by cases heq; rfl : m + 1 = 64) h64
                  · exact hNs
        | bool | float _ | pair _ _ => exact hNs
  | .store (t := t) v a k, path, st, d, em, sLvls, hd, heLen, hwf => by
      dsimp only [BlockFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      rcases hwf with ⟨⟨hv, ha⟩, hk⟩
      have hvR := argVarsLt_remap st.ctx d em hd heLen v hv
      have haR := argVarsLt_remap st.ctx d em hd heLen a ha
      have hCont : ∀ {d' sL'}, 0 < d' →
          tfVarsLt d' (liftContifyBlock cm abi pf rw pcs pc k path st d' em sL') = true :=
        fun hd' => tfVarsLt_liftContifyBlock cm abi pf rw pcs pc k path st _ em _ hd' heLen hk
      have hNs : tfVarsLt d (lowerNonSlotStore cm abi pf v a st d em sLvls k fun d' =>
          liftContifyBlock cm abi pf rw pcs pc k path st d' em sLvls) = true := by
        dsimp only [lowerNonSlotStore]; split
        · exact bAnd (bAnd hvR haR) (hCont hd)
        · cases abi with
          | contified _ => rfl
          | retEnvelope =>
              split
              · refine tfVarsLt_emitAliasGuard 6 pf.numSlots d t.bytes _ _ _ hd haR ?_ ?_
                · have hv5 := argVarsLt_shift 5 d _ hvR; rw [Nat.add_comm 5 d] at hv5
                  have ha5 := argVarsLt_shift 5 d _ haR; rw [Nat.add_comm 5 d] at ha5
                  exact bAnd (bAnd hv5 ha5) (hCont (by omega))
                · exact tfVarsLt_flushFrame 6 sLvls (d + 5) _ (by omega)
                    (tfVarsLt_lowerUnpromotedTail cm (.store v a k) st.ctx (d + 5 + sLvls.length)
                      em (by omega) heLen (bAnd (bAnd hv ha) hk))
              · rfl
      dsimp only [liftContifyBlock]; by_cases hn0 : pf.numSlots = 0
      · simp only [hn0, beq_self_eq_true, ↓reduceIte]; exact bAnd (bAnd hvR haR) (hCont hd)
      · simp only [beq_false_of_ne hn0, Bool.false_eq_true, ↓reduceIte]; by_cases ht : t = i64
        · subst ht; simp only [beq_self_eq_true, ↓reduceIte]
          cases spSlotOf? pf.numSlots (st.evalArg a) with | none => exact hNs | some _ =>
            cases remapArg d em v with
            | var _ => exact hCont hd
            | imm _ =>
                dsimp only [tfVarsLt, op1, argsVarsLt, List.length_cons, List.length_nil]
                exact bAnd (bAnd rfl rfl) (hCont (by omega))
        · simp only [beq_false_of_ne ht, Bool.false_eq_true, ↓reduceIte]; exact hNs
  | .codeAddr sym k, path, st, d, em, sLvls, hd, heLen, hwf => by
      dsimp only [liftContifyBlock]; cases cm.addrOf? sym with | none => rfl | some _ =>
        dsimp only [tfVarsLt, op1, argsVarsLt, List.length_cons, List.length_nil]
        exact bAnd (bAnd rfl rfl) (tfVarsLt_liftContifyBlock cm abi pf rw pcs pc k path _ (d + 1)
          (d :: em) sLvls (by omega) (by simp [heLen]) hwf)
  | .jnz c t e, path, st, d, em, sLvls, hd, heLen, hwf => by
      dsimp only [BlockFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      exact bAnd (bAnd (argVarsLt_remap st.ctx d em hd heLen c hwf.1.1)
        (tfVarsLt_liftContifyBlock cm abi pf rw pcs pc t (path ++ [true]) (st.pushCondFact c true)
          d em sLvls hd (by rw [pushContCondFact_ctx]; exact heLen)
          (by rw [pushContCondFact_ctx]; exact hwf.1.2)))
        (tfVarsLt_liftContifyBlock cm abi pf rw pcs pc e (path ++ [false]) (st.pushCondFact c false)
          d em sLvls hd (by rw [pushContCondFact_ctx]; exact heLen)
          (by rw [pushContCondFact_ctx]; exact hwf.2))
  | .ijmp tgt nxt, path, st, d, em, sLvls, hd, heLen, hwf => by
      rcases Bool.and_eq_true_iff.1 hwf with ⟨ht, hn⟩
      dsimp only [liftContifyBlock]; cases rw.findEdge pc path with | none => rfl | some ew =>
        exact tfVarsLt_liftContEdgeMapped abi pf.numSlots 6 sLvls pcs st d em tgt nxt ew.kind
          hd heLen ht hn
  | .halt c, _, st, d, em, sLvls, hd, heLen, hwf =>
      tfVarsLt_flushFrame 6 sLvls d _ hd
        (bAnd (argVarsLt_remap st.ctx (d + sLvls.length) em (by omega) heLen c hwf) rfl)
  | .hlt, _, _, _, _, _, _, _, _ => rfl

mutual
private theorem tfVarsLt_liftContifyGroupNode (cm : CodeMap) (cr : ContifyRegion)
    (callees : List ContCalleeMeta) : (pcs : List (BitVec 64)) → (g : GroupTree) →
    checkContGroupNode cm cr callees pcs g = true →
    tfVarsLt (if cr.privFrame.numSlots = 0 then 6 else 7 + cr.privFrame.numSlots)
      (liftContifyGroupNode cm cr pcs g) = true
  | pcs, .leaf pc, hchk => by
      dsimp only [checkContGroupNode, checkContBlockLeaves] at hchk
      dsimp only [liftContifyGroupNode]; cases hlu : cm.lookupAddr pc with
      | none => rw [hlu] at hchk; cases hchk
      | some b =>
          rw [hlu] at hchk; simp only [Bool.and_eq_true] at hchk
          exact tfVarsLt_liftContifyBlock cm cr.abi cr.privFrame cr.toRegionWitness pcs pc b []
            ContSymState.init _ initEnvMap (initSlotsLvls cr.privFrame.numSlots)
            (by cases cr.privFrame.numSlots <;> simp <;> omega) rfl hchk.1.1
  | pcs, .loop header nodes, hchk => by
      dsimp only [checkContGroupNode] at hchk; simp only [Bool.and_eq_true] at hchk
      dsimp only [liftContifyGroupNode, tfVarsLt]
      have hb := tbVarsLt_liftContifyGroupNodes cm cr callees _ nodes hchk.2
      let d0 := if cr.privFrame.numSlots = 0 then 6 else 7 + cr.privFrame.numSlots
      have hd0 : 0 < d0 := by dsimp only [d0]; cases cr.privFrame.numSlots <;> simp <;> omega
      have hlt : ∀ k, k ≤ 5 → d0 - 1 - k < d0 := fun k hk => by
        dsimp only [d0]; cases cr.privFrame.numSlots <;> simp <;> omega
      have hR : regsVarsLt d0 ⟨.var (d0 - 1 - 0), .var (d0 - 1 - 1), .var (d0 - 1 - 2),
          .var (d0 - 1 - 3), .var (d0 - 1 - 4), .var (d0 - 1 - 5)⟩ = true :=
        bAnd6 (of_argLt (hlt 0 (by omega))) (of_argLt (hlt 1 (by omega)))
          (of_argLt (hlt 2 (by omega))) (of_argLt (hlt 3 (by omega)))
          (of_argLt (hlt 4 (by omega))) (of_argLt (hlt 5 (by omega)))
      exact bAnd (tbVarsLt_mono (Nat.zero_le d0) _ hb)
        (tfVarsLt_lowerContJumpTo (rs := cr.abi.retSig) d0 cr.privFrame.numSlots
          (pushLabelPcs (nodes.map GroupTree.entryPc) pcs) header
          (baseContArgs cr.privFrame.numSlots)
          (argsVarsLt_mkJumpTuple d0 6 cr.privFrame.numSlots _ _ hd0 hR))

private theorem tbVarsLt_liftContifyGroupNodes (cm : CodeMap) (cr : ContifyRegion)
    (callees : List ContCalleeMeta) : (pcs : List (BitVec 64)) → (gs : List GroupTree) →
    checkContGroupNodes cm cr callees pcs gs = true →
    tbVarsLt 0 (liftContifyGroupNodes cm cr pcs gs) = true
  | _, [], _ => rfl
  | pcs, g :: gs, hchk => by
      rcases Bool.and_eq_true_iff.1 hchk with ⟨hg, hgs⟩
      dsimp only [liftContifyGroupNodes, tbVarsLt]
      have hlen : (contSig cr.privFrame.numSlots).length =
          if cr.privFrame.numSlots = 0 then 6 else 7 + cr.privFrame.numSlots := by
        cases h : cr.privFrame.numSlots with
        | zero => rfl | succ k => simp [contSig, regSig]; omega
      rw [Nat.zero_add, hlen]
      exact bAnd (tfVarsLt_liftContifyGroupNode cm cr callees pcs g hg)
        (tbVarsLt_liftContifyGroupNodes cm cr callees pcs gs hgs)
end

theorem denote_liftContifyGroupNodes_prefix {V : Ty → Type} {L : List Ty → Type}
    {cm : CodeMap} {cr : ContifyRegion} {callees : List ContCalleeMeta}
    (pcs : List (BitVec 64)) (gs : List GroupTree)
    (hchk : checkContGroupNodes cm cr callees pcs gs = true)
    (vs : List ((t : Ty) × V t)) (ls : List ((ts : List Ty) × L ts)) :
    denoteB V L (liftContifyGroupNodes cm cr pcs gs) vs ls =
      denoteB V L (liftContifyGroupNodes cm cr pcs gs) [] ls :=
  denoteB_tbVarsLt_prefix _ [] vs ls rfl (tbVarsLt_liftContifyGroupNodes cm cr callees pcs gs hchk)

/-! ## §2. `witContifyEnv`, `TFlat.isMemFree` Relocation & Acyclic Callee Metadata -/

/-- Callee environment extending `Γ` over an acyclic list of Stage-1 regions. -/
@[expose] def witContifyEnvAux (cm : CodeMap) (Γ : Env) : List ContifyRegion → Env
  | [] => Γ
  | cr :: crs =>
      let Γ' : Env := fun f as bs xs m P E =>
        ((∃ dualRet, cr.abi = .contified dualRet) ∧ f = cr.name ∧
          ∃ (h₁ : as = (liftContifyRegion cm cr).as) (h₂ : bs = (liftContifyRegion cm cr).rs),
            Func.spec Γ (liftContifyRegion cm cr).body (h₁ ▸ xs) m (h₂ ▸ P) E) ∨
        Γ f as bs xs m P E
      witContifyEnvAux cm Γ' crs

/-- Global callee environment associated with Stage-1 witness `wit`. -/
@[expose] def witContifyEnv (cm : CodeMap) (wit : ContifyWitness) : Env :=
  witContifyEnvAux cm (fun _ _ _ _ _ _ _ => False) wit.regions

private theorem witContifyEnvAux_base_mono (cm : CodeMap) {Γ₁ Γ₂ : Env}
    (hΓ : ∀ f as bs xs m P E, Γ₁ f as bs xs m P E → Γ₂ f as bs xs m P E) :
    ∀ crs f as bs xs m P E, witContifyEnvAux cm Γ₁ crs f as bs xs m P E →
      witContifyEnvAux cm Γ₂ crs f as bs xs m P E
  | [], _, _, _, _, _, _, _, h => hΓ _ _ _ _ _ _ _ h
  | _ :: crs, f, as, bs, xs, m, P, E, h =>
      witContifyEnvAux_base_mono cm (fun _ _ _ _ _ _ _ hg => by
        rcases hg with ⟨hd, rfl, rfl, rfl, hSp⟩ | hg
        · exact Or.inl ⟨hd, rfl, rfl, rfl, Func.spec_env_mono hΓ hSp⟩
        · exact Or.inr (hΓ _ _ _ _ _ _ _ hg)) crs f as bs xs m P E h

theorem witContifyEnvAux_mono_right (cm : CodeMap) (Γ : Env) :
    ∀ crs f as bs xs m P E, Γ f as bs xs m P E → witContifyEnvAux cm Γ crs f as bs xs m P E
  | [], _, _, _, _, _, _, _, h => h
  | _ :: crs, f, as, bs, xs, m, P, E, h =>
      witContifyEnvAux_mono_right cm _ crs f as bs xs m P E (.inr h)

theorem witContifyEnvAux_append (cm : CodeMap) (Γ : Env) (pre post : List ContifyRegion) :
    witContifyEnvAux cm Γ (pre ++ post) = witContifyEnvAux cm (witContifyEnvAux cm Γ pre) post := by
  induction pre generalizing Γ with | nil => rfl | cons _ _ ih => exact ih _

theorem witContifyEnvAux_mem_prefix (cm : CodeMap) (Γ : Env) (pre : List ContifyRegion)
    (cr : ContifyRegion) (post : List ContifyRegion) (dualRet : Bool)
    (habi : cr.abi = .contified dualRet) {xs m P E}
    (hSpec : Func.spec (witContifyEnvAux cm Γ pre) (liftContifyRegion cm cr).body xs m P E) :
    witContifyEnvAux cm Γ (pre ++ cr :: post) cr.name regSig cr.abi.retSig xs m P E := by
  rw [witContifyEnvAux_append]; dsimp only [witContifyEnvAux]
  exact witContifyEnvAux_mono_right cm _ post _ _ _ _ _ _ _
    (.inl ⟨⟨dualRet, habi⟩, rfl, rfl, rfl, hSpec⟩)

@[expose] def contCalleesStep (cm : CodeMap) (cr : ContifyRegion) (cs : List ContCalleeMeta) :
    List ContCalleeMeta :=
  match cr.toCalleeMeta? cm cs with | some c => c :: cs | none => cs

@[expose] def contCalleesFold (cm : CodeMap) (cs : List ContCalleeMeta) :
    List ContifyRegion → List ContCalleeMeta
  | [] => cs | cr :: crs => contCalleesFold cm (contCalleesStep cm cr cs) crs

theorem contCheckAux_append (cm : CodeMap) :
    ∀ (pre post : List ContifyRegion) (cs : List ContCalleeMeta),
      ContifyWitness.checkAux cm cs (pre ++ post) = true →
      ContifyWitness.checkAux cm (contCalleesFold cm cs pre) post = true
  | [], _, _, h => h
  | cr :: pre, post, cs, h =>
      contCheckAux_append cm pre post (contCalleesStep cm cr cs) (Bool.and_eq_true_iff.1 h).2

theorem mem_contCalleesFold (cm : CodeMap) :
    ∀ (pre : List ContifyRegion) (cs : List ContCalleeMeta) (c : ContCalleeMeta),
      c ∈ contCalleesFold cm cs pre → c ∈ cs ∨ ∃ (pre0 post0 : List ContifyRegion)
        (cr : ContifyRegion), pre = pre0 ++ cr :: post0 ∧
        cr.toCalleeMeta? cm (contCalleesFold cm cs pre0) = some c
  | [], _, _, hc => Or.inl hc
  | cr :: pre, cs, c, hc => by
      rcases mem_contCalleesFold cm pre (contCalleesStep cm cr cs) c hc with
        hc' | ⟨p0, q0, cr', hEq, hto⟩
      · cases h : cr.toCalleeMeta? cm cs with
        | none => simp only [contCalleesStep, h] at hc'; exact Or.inl hc'
        | some m =>
            simp only [contCalleesStep, h] at hc'
            rcases List.mem_cons.1 hc' with rfl | hc''
            · exact Or.inr ⟨[], pre, cr, rfl, h⟩
            · exact Or.inl hc''
      · exact Or.inr ⟨cr :: p0, q0, cr', by rw [hEq]; rfl, hto⟩

mutual
@[expose] def isPureMemFreeF {rs : List Ty} : TFlat rs → Bool
  | .let_ _ k => isPureMemFreeF k
  | .load _ _ _ | .store _ _ _ | .call _ _ _ _ | .exit _ _ => false
  | .jnz _ t e => isPureMemFreeF t && isPureMemFreeF e
  | .jump _ _ | .ret _ | .hlt => true
  | .group bodies k => isPureMemFreeB bodies && isPureMemFreeF k

@[expose] def isPureMemFreeB {rs : List Ty} : {sig : List (List Ty)} → TBlocks rs sig → Bool
  | _, .nil => true | _, .cons b bs => isPureMemFreeF b && isPureMemFreeB bs
end

@[expose] def ContLsReloc (m₁ m₀ : Mem 64) (ls₁ ls₀ : List ((ts : List Ty) × Cont ts)) : Prop :=
  ∀ ts idx J₁, lookupL ls₁ ts idx = some J₁ →
    ∃ J₀, lookupL ls₀ ts idx = some J₀ ∧ ∀ vs, J₁ vs m₁ → J₀ vs m₀

private theorem contLsReloc_pushTup (m₁ m₀ : Mem 64) :
    ∀ {sig : List (List Ty)} (Js₁ Js₀ : Tup Cont sig) {ls₁ ls₀ : List ((ts : List Ty) × Cont ts)},
      (∀ {ts} (i : Member ts sig) vs, Js₁.get i vs m₁ → Js₀.get i vs m₀) →
      ContLsReloc m₁ m₀ ls₁ ls₀ → ContLsReloc m₁ m₀ (pushTup Js₁ ls₁) (pushTup Js₀ ls₀)
  | [], (), (), _, _, _, hls => hls
  | ts :: _, (J₁, Js₁), (J₀, Js₀), ls₁, ls₀, hJs, hls => by
      dsimp only [pushTup]; apply contLsReloc_pushTup m₁ m₀ Js₁ Js₀ (fun i => hJs (.there i))
      intro ts' idx K₁ hK; cases idx with
      | succ k => exact hls ts' k K₁ hK
      | zero =>
          dsimp only [lookupL, listGet?] at hK ⊢
          cases hCast : castListTy ts ts' J₁ with
          | none => rw [hCast] at hK; cases hK
          | some _ =>
              rw [hCast] at hK; cases hK; dsimp only [castListTy] at hCast
              cases hDec : listTyDecEq ts ts' with
              | isFalse _ => rw [hDec] at hCast; cases hCast
              | isTrue hEq =>
                  rw [hDec] at hCast; cases hEq; cases hCast
                  refine ⟨J₀, ?_, fun vs h => hJs .here vs h⟩; dsimp only [castListTy]
                  cases listTyDecEq ts ts with | isFalse hn => exact absurd rfl hn | isTrue _ => rfl

mutual
theorem wp_pureMemFree_relocate (Γ : Env) (X : XPost) (m₁ m₀ : Mem 64) {rs : List Ty} :
    (tf : TFlat rs) → isPureMemFreeF tf = true →
    ∀ (Q : Post rs) (bvs : List ((t : Ty) × Val t))
      (ls₁ ls₀ : List ((ts : List Ty) × Cont ts)), ContLsReloc m₁ m₀ ls₁ ls₀ →
      wp Γ Q X (denote Val Cont tf bvs ls₁) m₁ →
      wp Γ (fun r m' => m' = m₀ ∧ Q r m₁) X (denote Val Cont tf bvs ls₀) m₀
  | .let_ op k, hmf, Q, bvs, ls₁, ls₀, hls, hwp => by
      dsimp only [denote] at hwp ⊢; cases ha : denoteArgs bvs op.args with
      | none => rw [ha] at hwp; exact hwp
      | some _ =>
          rw [ha] at hwp; dsimp only [wp] at hwp ⊢
          exact Op.wp_mono (fun xs h =>
            wp_pureMemFree_relocate Γ X m₁ m₀ k hmf Q (pushTup xs bvs) ls₁ ls₀ hls h) hwp
  | .load _ _ _, hmf, _, _, _, _, _, _ | .store _ _ _, hmf, _, _, _, _, _, _ |
    .call _ _ _ _, hmf, _, _, _, _, _, _ | .exit _ _, hmf, _, _, _, _, _, _ => by cases hmf
  | .jnz c t e, hmf, Q, bvs, ls₁, ls₀, hls, hwp => by
      rcases Bool.and_eq_true_iff.1 hmf with ⟨ht, he⟩; dsimp only [denote] at hwp ⊢
      cases hc : denoteArg bvs c with | none => rw [hc] at hwp; exact hwp | some _ =>
        rw [hc] at hwp; dsimp only [wp] at hwp ⊢
        exact ⟨fun h => wp_pureMemFree_relocate Γ X m₁ m₀ t ht Q bvs ls₁ ls₀ hls (hwp.1 h),
          fun h => wp_pureMemFree_relocate Γ X m₁ m₀ e he Q bvs ls₁ ls₀ hls (hwp.2 h)⟩
  | .jump (ts := ts) j args, _, _, bvs, ls₁, ls₀, hls, hwp => by
      dsimp only [denote] at hwp ⊢; cases hj₁ : lookupL ls₁ ts j with
      | none => rw [hj₁] at hwp; cases hwp
      | some J₁ =>
          rw [hj₁] at hwp; cases ha : denoteArgs bvs args with
          | none => rw [ha] at hwp; cases hwp
          | some _ =>
              rw [ha] at hwp; obtain ⟨J₀, hj₀, hrel⟩ := hls ts j J₁ hj₁
              rw [hj₀]; exact hrel _ hwp
  | .ret vs, _, _, bvs, _, _, _, hwp => by
      dsimp only [denote] at hwp ⊢; cases ha : denoteArgs bvs vs with
      | none => rw [ha] at hwp; cases hwp | some _ => rw [ha] at hwp; exact ⟨rfl, hwp⟩
  | .hlt, _, _, _, _, _, _, hwp => hwp
  | .group bodies k, hmf, Q, bvs, ls₁, ls₀, hls, hwp => by
      rcases Bool.and_eq_true_iff.1 hmf with ⟨hb, hk⟩; dsimp only [denote, wp] at hwp ⊢
      intro Js₀ hCl₀
      let Js₁ : Tup Cont _ := Tup.ofMember _ fun i xs m => m = m₁ → Js₀.get i xs m₀
      have hJsRel : ∀ {ts} (i : Member ts _) vs, Js₁.get i vs m₁ → Js₀.get i vs m₀ := by
        intro ts i vs h; rw [Tup.get_ofMember] at h; exact h rfl
      have hCl₁ : Closed Γ Q X (denoteB Val Cont bodies bvs (pushTup Js₁ ls₁)) Js₁ := by
        rw [closed_iff]; intro ts i xs m hbm; rw [Tup.get_ofMember]; intro hmEq; subst m
        exact (closed_iff Γ (fun r m' => m' = m₀ ∧ Q r m₁) X _ Js₀).1 hCl₀ i xs m₀
          (wp_pureMemFree_relocate_blocks Γ X m₁ m₀ bodies hb Q bvs (pushTup Js₁ ls₁)
            (pushTup Js₀ ls₀) (contLsReloc_pushTup m₁ m₀ Js₁ Js₀ hJsRel hls) i xs hbm)
      exact wp_pureMemFree_relocate Γ X m₁ m₀ k hk Q bvs (pushTup Js₁ ls₁) (pushTup Js₀ ls₀)
        (contLsReloc_pushTup m₁ m₀ Js₁ Js₀ hJsRel hls) (hwp Js₁ hCl₁)

private theorem wp_pureMemFree_relocate_blocks (Γ : Env) (X : XPost) (m₁ m₀ : Mem 64)
    {rs : List Ty} : {sig : List (List Ty)} → (bs : TBlocks rs sig) → isPureMemFreeB bs = true →
    ∀ (Q : Post rs) (bvs : List ((t : Ty) × Val t)) (ls₁ ls₀ : List ((ts : List Ty) × Cont ts)),
      ContLsReloc m₁ m₀ ls₁ ls₀ → ∀ {ts} (i : Member ts sig) (xs : Tup Val ts),
      wp Γ Q X ((denoteB Val Cont bs bvs ls₁).get i xs) m₁ →
      wp Γ (fun r m' => m' = m₀ ∧ Q r m₁) X ((denoteB Val Cont bs bvs ls₀).get i xs) m₀
  | _ :: _, .cons b _, hmf, Q, bvs, ls₁, ls₀, hls, _, .here, xs, hwp =>
      wp_pureMemFree_relocate Γ X m₁ m₀ b (Bool.and_eq_true_iff.1 hmf).1 Q
        (pushTup xs bvs) ls₁ ls₀ hls hwp
  | _ :: _, .cons _ bs, hmf, Q, bvs, ls₁, ls₀, hls, _, .there i, xs, hwp =>
      wp_pureMemFree_relocate_blocks Γ X m₁ m₀ bs (Bool.and_eq_true_iff.1 hmf).2 Q
        bvs ls₁ ls₀ hls i xs hwp
end

private theorem isPureMemFreeF_lowerContJumpTo {rs : List Ty} (n : Nat) (pcs : List (BitVec 64))
    (tPc : BitVec 64) (args : Tup (Arg K) (contSig n)) :
    isPureMemFreeF (lowerContJumpTo (rs := rs) n pcs tPc args) = true := by
  dsimp only [lowerContJumpTo]; cases findLabelIdx pcs tPc <;> rfl

private theorem isPureMemFreeF_lowerContStride {rs : List Ty} (pcs : List (BitVec 64))
    (iv : Nat) (args : Tup (Arg K) (contSig 0)) :
    ∀ (targets : List (BitVec 64)) (k cs : Nat),
      isPureMemFreeF (lowerContStride (rs := rs) 0 pcs iv args k cs targets) = true
  | [], _, _ => rfl | [t], _, _ => isPureMemFreeF_lowerContJumpTo 0 pcs t _
  | t :: a :: rest, k, cs => bAnd (isPureMemFreeF_lowerContJumpTo 0 pcs t _)
      (isPureMemFreeF_lowerContStride pcs iv args (a :: rest) (k + 1) (cs + 1))

private theorem contify_isPureMemFree_edge (pcs : List (BitVec 64)) (dualRet : Bool)
    (pf : PrivFrameCfg) (st : ContSymState) (d : Nat) (em : List Nat) (tgt : Arg K i64)
    (nxt : RegsExpr K) (kind : EdgeKind) (leaf : ContSymLeaf) (cm : CodeMap)
    (callees : List ContCalleeMeta)
    (hEdge : checkContEdgeLeaf cm (.contified dualRet) pf callees pcs leaf kind = true) :
    isPureMemFreeF (liftContEdgeMapped (.contified dualRet) 0 6 [] pcs st d em tgt nxt kind) =
      true := by
  dsimp only [checkContEdgeLeaf] at hEdge
  cases kind with
  | memTableGuarded _ _ | memTableRo _ _ _ => simp at hEdge
  | direct tPc =>
      cases h0 : checkEdgeLeaf cm (.contified dualRet)
          (callees.map fun c => ⟨c.name, c.entryPc, c.dualRet⟩) pcs
          ⟨leaf.path, leaf.st.toSymState, leaf.target, leaf.nextRegs⟩ (.direct tPc)
      · rw [h0] at hEdge; cases hEdge
      · exact isPureMemFreeF_lowerContJumpTo 0 pcs tPc _
  | select tPc ePc =>
      cases h0 : checkEdgeLeaf cm (.contified dualRet)
          (callees.map fun c => ⟨c.name, c.entryPc, c.dualRet⟩) pcs
          ⟨leaf.path, leaf.st.toSymState, leaf.target, leaf.nextRegs⟩ (.select tPc ePc)
      · rw [h0] at hEdge; cases hEdge
      · dsimp only [liftContEdgeMapped]; cases st.evalArg tgt <;> try rfl
        exact bAnd (isPureMemFreeF_lowerContJumpTo 0 pcs tPc _)
          (isPureMemFreeF_lowerContJumpTo 0 pcs ePc _)
  | strideTable basePc targets needGuard =>
      cases h0 : checkEdgeLeaf cm (.contified dualRet)
          (callees.map fun c => ⟨c.name, c.entryPc, c.dualRet⟩) pcs
          ⟨leaf.path, leaf.st.toSymState, leaf.target, leaf.nextRegs⟩
          (.strideTable basePc targets needGuard)
      · rw [h0] at hEdge; cases hEdge
      · dsimp only [liftContEdgeMapped]
        cases needGuard with
        | false =>
            cases st.evalArg tgt <;> try rfl
            exact isPureMemFreeF_lowerContStride pcs _ _ targets 0 0
        | true =>
            simp only [checkEdgeLeaf, RegionAbi.isContified, Bool.not_true, ↓reduceIte,
              Bool.and_eq_true] at h0
            have hm := h0.2
            cases hev : leaf.st.toSymState.evalArg leaf.target <;> simp [hev] at hm
  | contCall _ _ _ _ _ | guarded _ | bailout =>
      cases h0 : checkEdgeLeaf cm (.contified dualRet)
          (callees.map fun c => ⟨c.name, c.entryPc, c.dualRet⟩) pcs
          ⟨leaf.path, leaf.st.toSymState, leaf.target, leaf.nextRegs⟩ _
      · rw [h0] at hEdge; cases hEdge
      · dsimp only [checkEdgeLeaf] at h0; simp [RegionAbi.isContified] at h0
  | contRet isAlt =>
      cases dualRet <;> cases isAlt <;> rfl

private theorem contify_isPureMemFree_block (cm : CodeMap) (rw : RegionWitness)
    (pcs : List (BitVec 64)) (pc : BitVec 64) (dualRet : Bool) (pf : PrivFrameCfg)
    (hZero : pf.numSlots = 0) (callees : List ContCalleeMeta) :
    ∀ (b : BlockFlat) (path : BranchPath) (st : ContSymState) (d : Nat) (em : List Nat)
      (leaves : List ContSymLeaf), blockNoMem b = true →
      symEvalContBlock cm pf b path st = some leaves →
      (∀ lf ∈ leaves, ∃ ew, rw.findEdge pc lf.path = some ew ∧
        checkContEdgeLeaf cm (.contified dualRet) pf callees pcs lf ew.kind = true) →
      isPureMemFreeF (liftContifyBlock cm (.contified dualRet) pf rw pcs pc b path st d em []) =
        true
  | .let_ _ k, _, _, _, _, _, hnm, hsym, hlvs =>
      contify_isPureMemFree_block cm rw pcs pc dualRet pf hZero callees k _ _ _ _ _ hnm hsym hlvs
  | .load _ _ _, _, _, _, _, _, hnm, _, _ | .store _ _ _, _, _, _, _, _, hnm, _, _ |
    .halt _, _, _, _, _, _, hnm, _, _ => by cases hnm
  | .hlt, _, _, _, _, _, _, _, _ => rfl
  | .codeAddr sym k, _, _, _, _, _, hnm, hsym, hlvs => by
      dsimp only [symEvalContBlock] at hsym; dsimp only [liftContifyBlock]
      cases ha : cm.addrOf? sym with | none => rfl | some _ =>
        rw [ha] at hsym
        exact contify_isPureMemFree_block cm rw pcs pc dualRet pf hZero callees k _ _ _ _ _
          hnm hsym hlvs
  | .jnz c t e, path, st, d, em, _, hnm, hsym, hlvs => by
      rcases Bool.and_eq_true_iff.1 hnm with ⟨ht, he⟩; dsimp only [symEvalContBlock] at hsym
      cases hlt : symEvalContBlock cm pf t (path ++ [true]) (st.pushCondFact c true) with
      | none => simp [hlt] at hsym
      | some lt =>
          cases hle : symEvalContBlock cm pf e (path ++ [false]) (st.pushCondFact c false) with
          | none => simp [hlt, hle] at hsym
          | some le =>
              simp only [hlt, hle] at hsym; cases hsym
              dsimp only [liftContifyBlock, isPureMemFreeF]
              exact bAnd (contify_isPureMemFree_block cm rw pcs pc dualRet pf hZero callees t _ _
                  d em lt ht hlt (fun lf hm => hlvs lf (List.mem_append_left le hm)))
                (contify_isPureMemFree_block cm rw pcs pc dualRet pf hZero callees e _ _ d em le
                  he hle (fun lf hm => hlvs lf (List.mem_append_right lt hm)))
  | .ijmp tgt nxt, path, st, d, em, _, _, hsym, hlvs => by
      dsimp only [symEvalContBlock] at hsym; cases hsym
      obtain ⟨ew, hfind, hchk⟩ := hlvs ⟨path, st, tgt, nxt⟩ List.mem_cons_self
      dsimp only [liftContifyBlock]; rw [hfind, hZero]
      exact contify_isPureMemFree_edge pcs dualRet pf st d em tgt nxt ew.kind _ cm callees hchk

mutual
private theorem contify_isPureMemFree_node (cm : CodeMap) (cr : ContifyRegion)
    (callees : List ContCalleeMeta) (dualRet : Bool) (hAbi : cr.abi = .contified dualRet)
    (hZero : cr.privFrame.numSlots = 0) :
    (pcs : List (BitVec 64)) → (g : GroupTree) → checkContGroupNode cm cr callees pcs g = true →
    (∀ pc ∈ g.allPcs, ∃ b, cm.lookupAddr pc = some b ∧ blockNoMem b = true) →
    isPureMemFreeF (liftContifyGroupNode cm cr pcs g) = true
  | pcs, .leaf pc, hchk, hnm => by
      dsimp only [checkContGroupNode, checkContBlockLeaves] at hchk
      dsimp only [liftContifyGroupNode]
      obtain ⟨b, hlu, hbn⟩ := hnm pc (by simp [GroupTree.allPcs])
      rw [hlu] at hchk ⊢; simp only [Bool.and_eq_true] at hchk
      cases hsym : symEvalContBlock cm cr.privFrame b [] ContSymState.init with
      | none => rw [hsym] at hchk; cases hchk.2
      | some leaves =>
          rw [hsym] at hchk
          have hlvs : ∀ lf ∈ leaves, ∃ ew, cr.toRegionWitness.findEdge pc lf.path = some ew ∧
              checkContEdgeLeaf cm (.contified dualRet) cr.privFrame callees pcs lf ew.kind =
                true := fun lf hm => by
            have ha := List.all_eq_true.1 hchk.2 lf hm
            cases hf : cr.toRegionWitness.findEdge pc lf.path with
            | none => rw [hf] at ha; cases ha
            | some ew => rw [hf] at ha; rw [← hAbi]; exact ⟨ew, rfl, ha⟩
          rw [hAbi, hZero]
          simpa [hZero, initSlotsLvls] using contify_isPureMemFree_block cm cr.toRegionWitness
            pcs pc dualRet cr.privFrame hZero callees b [] ContSymState.init _ initEnvMap leaves
            hbn hsym hlvs
  | pcs, .loop header nodes, hchk, hnm => by
      dsimp only [checkContGroupNode] at hchk; simp only [Bool.and_eq_true] at hchk
      dsimp only [liftContifyGroupNode, isPureMemFreeF]
      exact bAnd (contify_isPureMemFree_nodes cm cr callees dualRet hAbi hZero _ nodes hchk.2
        (fun pc hpc => hnm pc (by simpa [GroupTree.allPcs] using hpc)))
        (isPureMemFreeF_lowerContJumpTo _ _ _ _)

private theorem contify_isPureMemFree_nodes (cm : CodeMap) (cr : ContifyRegion)
    (callees : List ContCalleeMeta) (dualRet : Bool) (hAbi : cr.abi = .contified dualRet)
    (hZero : cr.privFrame.numSlots = 0) : (pcs : List (BitVec 64)) → (gs : List GroupTree) →
    checkContGroupNodes cm cr callees pcs gs = true →
    (∀ pc ∈ gs.flatMap GroupTree.allPcs, ∃ b, cm.lookupAddr pc = some b ∧ blockNoMem b = true) →
    isPureMemFreeB (liftContifyGroupNodes cm cr pcs gs) = true
  | _, [], _, _ => rfl
  | pcs, g :: gs, hchk, hnm =>
      let ⟨hg, hgs⟩ := Bool.and_eq_true_iff.1 hchk
      bAnd (contify_isPureMemFree_node cm cr callees dualRet hAbi hZero pcs g hg
          (fun pc hpc => hnm pc (List.mem_flatMap.2 ⟨g, .head _, hpc⟩)))
        (contify_isPureMemFree_nodes cm cr callees dualRet hAbi hZero pcs gs hgs
          (fun pc hpc => let ⟨g', hm, hp⟩ := List.mem_flatMap.1 hpc
            hnm pc (List.mem_flatMap.2 ⟨g', .tail _ hm, hp⟩)))
end

theorem liftContifyTFlat_isPureMemFree (cm : CodeMap) (cr : ContifyRegion)
    (callees : List ContCalleeMeta) (dualRet : Bool) (hAbi : cr.abi = .contified dualRet)
    (hChk : cr.check cm callees = true) (hMf : regionMemFree cm callees cr = true) :
    isPureMemFreeF (liftContifyTFlat cm cr) = true := by
  dsimp only [ContifyRegion.check] at hChk; simp only [Bool.and_eq_true] at hChk
  have hn0 : cr.privFrame.numSlots = 0 := by
    have ho := hChk.1.1.1.1.1.1.1.2; rw [hAbi] at ho; cases hn : cr.privFrame.numSlots <;> simp_all
  have hnm : ∀ pc ∈ cr.tree.flatMap GroupTree.allPcs,
      ∃ b, cm.lookupAddr pc = some b ∧ blockNoMem b = true := fun pc hpc => by
    have hall := List.all_eq_true.1 hMf pc hpc
    cases hlu : cm.lookupAddr pc with
    | none => rw [hlu] at hall; cases hall
    | some b => rw [hlu] at hall; exact ⟨b, rfl, (Bool.and_eq_true_iff.1 hall).1⟩
  have hNs := contify_isPureMemFree_nodes cm cr callees dualRet hAbi hn0
    (pushLabelPcs (cr.tree.map GroupTree.entryPc) []) cr.tree hChk.1.1.2 hnm
  have hGen : ∀ (n : Nat), n = 0 → isPureMemFreeF (loadEntryFrameAux 0 n n (.group
      (liftContifyGroupNodes cm cr (pushLabelPcs (cr.tree.map GroupTree.entryPc) []) cr.tree)
      (lowerContJumpTo n (pushLabelPcs (cr.tree.map GroupTree.entryPc) []) cr.entryPc
        (mkEntryFrameArgs n)))) = true := fun _ h => by
    subst h; exact bAnd hNs (isPureMemFreeF_lowerContJumpTo _ _ _ _)
  exact hGen cr.privFrame.numSlots hn0


end LeanQbe.T.Unified
