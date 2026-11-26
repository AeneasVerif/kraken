module

public import LeanQbe.T.CondThreadOptLemmas0
import LeanQbe.T.OptUtilLemmas
import LeanQbe.T.OpsLemmas
import LeanQbe.T.WPLemmas
import LeanQbe.T.WfLemmas
import LeanQbe.T.FoldLemmas

/-!
# Soundness Proofs for `CondThreadOpt` — Part 1 (`pathCondOpt_wf` & `rewriteCTAux_wf`)

Completes `pcStep_rel`, `pathCondOpt_wf`, `pathCondOpt_callsOk`, `Func.pathCondOpt_*`, and
relational well-formedness for `condThreadPass` through `rewriteCTAux_wf`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

open CondThreadOpt

namespace CondThreadOptImpl

section
variable {V₁ V₂ : Ty → Type}

theorem pcStep_rel {G' : Ctx V₁ V₂} {G : Ctx (PVal V₁) (PVal V₂)} (hG : PRelG G' G)
    (F : List BoolFact) (next : Nat) {sig ts : List Ty} (code : OpCode sig ts)
    {args₁ : Tup (Arg (PVal V₁)) sig} {args₂ : Tup (Arg (PVal V₂)) sig}
    (hargs : TRel (ArgRel G) args₁ args₂) :
    PStepRel G' (pcStepAux code args₁ F next) (pcStepAux code args₂ F next) := by
  cases code with
  | copy _ =>
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [pcStepAux]
    cases ha with
    | var h => exact .elim (.cons (hG _ h) .nil)
    | imm c => exact .elim (.cons ⟨.imm c, rfl⟩ .nil)
  | not t =>
    cases t with
    | bool =>
      rcases hargs with _ | ⟨ha, _⟩
      obtain ⟨ho, hi⟩ := argRel_resolveBoolArg hG F ha
      dsimp only [pcStepAux]
      rw [hi]
      rcases argRel_cases ho with ⟨_, _, h1, h2, hm⟩ | ⟨c, h1, h2⟩ <;> simp [h1, h2]
      · exact .emit (.mk _ (.cons (.var hm) .nil)) fun xs₁ xs₂ => wrapBool_rel _ _ _ xs₁ xs₂
      · exact .elim (.cons (pRelVal_imm (!c)) .nil)
    | bits _ | float _ | pair _ _ =>
      exact .emit (.mk _ (trel_pOut_rel hG hargs)) fun xs₁ xs₂ => trel_freshPVals_rel xs₁ xs₂ next
  | and t =>
    cases t with
    | bool =>
      rcases args₁ with ⟨a₁, b₁, _⟩; rcases args₂ with ⟨a₂, b₂, _⟩
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
      obtain ⟨hoa, hia⟩ := argRel_resolveBoolArg hG F ha
      obtain ⟨hob, hib⟩ := argRel_resolveBoolArg hG F hb
      have hva := argRel_resolveBoolArg_rel hG F ha
      have hvb := argRel_resolveBoolArg_rel hG F hb
      dsimp only [pcStepAux]
      rcases argRel_cases hoa with ⟨_, _, ha1, ha2, hma⟩ | ⟨ca, ha1, ha2⟩ <;>
        rcases argRel_cases hob with ⟨_, _, hb1, hb2, hmb⟩ | ⟨cb, hb1, hb2⟩ <;>
        simp only [ha1, ha2, hb1, hb2]
      · rw [hia, hib]
        by_cases heq : ((pInfo (resolveBoolArg F a₂)).id == (pInfo (resolveBoolArg F b₂)).id &&
            (pInfo (resolveBoolArg F a₂)).id.isSome) = true
        · simp only [heq, ↓reduceIte]; exact .elim (.cons hva .nil)
        · simp only [heq, Bool.false_eq_true, ↓reduceIte]
          exact .emit (.mk _ (.cons (.var hma) (.cons (.var hmb) .nil)))
            fun xs₁ xs₂ => wrapBool_rel _ _ _ xs₁ xs₂
      · cases cb
        · exact .elim (.cons (pRelVal_imm false) .nil)
        · exact .elim (.cons hva .nil)
      · cases ca
        · exact .elim (.cons (pRelVal_imm false) .nil)
        · exact .elim (.cons hvb .nil)
      · cases ca <;> cases cb
        · exact .elim (.cons (pRelVal_imm false) .nil)
        · exact .elim (.cons (pRelVal_imm false) .nil)
        · exact .elim (.cons (pRelVal_imm false) .nil)
        · exact .elim (.cons hvb .nil)
    | bits _ | float _ | pair _ _ =>
      exact .emit (.mk _ (trel_pOut_rel hG hargs)) fun xs₁ xs₂ => trel_freshPVals_rel xs₁ xs₂ next
  | or t =>
    cases t with
    | bool =>
      rcases args₁ with ⟨a₁, b₁, _⟩; rcases args₂ with ⟨a₂, b₂, _⟩
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
      obtain ⟨hoa, hia⟩ := argRel_resolveBoolArg hG F ha
      obtain ⟨hob, hib⟩ := argRel_resolveBoolArg hG F hb
      have hva := argRel_resolveBoolArg_rel hG F ha
      have hvb := argRel_resolveBoolArg_rel hG F hb
      dsimp only [pcStepAux]
      rcases argRel_cases hoa with ⟨_, _, ha1, ha2, hma⟩ | ⟨ca, ha1, ha2⟩ <;>
        rcases argRel_cases hob with ⟨_, _, hb1, hb2, hmb⟩ | ⟨cb, hb1, hb2⟩ <;>
        simp only [ha1, ha2, hb1, hb2]
      · rw [hia, hib]
        by_cases heq : ((pInfo (resolveBoolArg F a₂)).id == (pInfo (resolveBoolArg F b₂)).id &&
            (pInfo (resolveBoolArg F a₂)).id.isSome) = true
        · simp only [heq, ↓reduceIte]; exact .elim (.cons hva .nil)
        · simp only [heq, Bool.false_eq_true, ↓reduceIte]
          exact .emit (.mk _ (.cons (.var hma) (.cons (.var hmb) .nil)))
            fun xs₁ xs₂ => wrapBool_rel _ _ _ xs₁ xs₂
      · cases cb
        · exact .elim (.cons hva .nil)
        · exact .elim (.cons (pRelVal_imm true) .nil)
      · cases ca
        · exact .elim (.cons hvb .nil)
        · exact .elim (.cons (pRelVal_imm true) .nil)
      · cases ca <;> cases cb
        · exact .elim (.cons hvb .nil)
        · exact .elim (.cons (pRelVal_imm true) .nil)
        · exact .elim (.cons (pRelVal_imm true) .nil)
        · exact .elim (.cons (pRelVal_imm true) .nil)
    | bits _ | float _ | pair _ _ =>
      exact .emit (.mk _ (trel_pOut_rel hG hargs)) fun xs₁ xs₂ => trel_freshPVals_rel xs₁ xs₂ next
  | xor t =>
    cases t with
    | bool =>
      rcases args₁ with ⟨a₁, b₁, _⟩; rcases args₂ with ⟨a₂, b₂, _⟩
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
      obtain ⟨hoa, hia⟩ := argRel_resolveBoolArg hG F ha
      obtain ⟨hob, hib⟩ := argRel_resolveBoolArg hG F hb
      have hva := argRel_resolveBoolArg_rel hG F ha
      have hvb := argRel_resolveBoolArg_rel hG F hb
      dsimp only [pcStepAux]
      rcases argRel_cases hoa with ⟨_, _, ha1, ha2, hma⟩ | ⟨ca, ha1, ha2⟩ <;>
        rcases argRel_cases hob with ⟨_, _, hb1, hb2, hmb⟩ | ⟨cb, hb1, hb2⟩ <;>
        simp only [ha1, ha2, hb1, hb2]
      · rw [hia, hib]
        by_cases heq : ((pInfo (resolveBoolArg F a₂)).id == (pInfo (resolveBoolArg F b₂)).id &&
            (pInfo (resolveBoolArg F a₂)).id.isSome) = true
        · simp only [heq, ↓reduceIte]; exact .elim (.cons (pRelVal_imm false) .nil)
        · simp only [heq, Bool.false_eq_true, ↓reduceIte]
          exact .emit (.mk _ (.cons (.var hma) (.cons (.var hmb) .nil)))
            fun xs₁ xs₂ => trel_freshPVals_rel xs₁ xs₂ next
      · cases cb
        · exact .elim (.cons hva .nil)
        · rw [hia]
          exact .emit (.mk _ (.cons (.var hma) (.cons (ArgRel.imm (t := .bool) true) .nil)))
            fun xs₁ xs₂ => wrapBool_rel _ _ _ xs₁ xs₂
      · cases ca
        · exact .elim (.cons hvb .nil)
        · rw [hib]
          exact .emit (.mk _ (.cons (ArgRel.imm (t := .bool) true) (.cons (.var hmb) .nil)))
            fun xs₁ xs₂ => wrapBool_rel _ _ _ xs₁ xs₂
      · cases ca <;> cases cb <;> exact .elim (.cons (pRelVal_imm _) .nil)
    | bits _ | float _ | pair _ _ =>
      exact .emit (.mk _ (trel_pOut_rel hG hargs)) fun xs₁ xs₂ => trel_freshPVals_rel xs₁ xs₂ next
  | select t =>
    rcases hargs with _ | ⟨hc, _ | ⟨hx, _ | ⟨hy, _⟩⟩⟩
    obtain ⟨hoc, _⟩ := argRel_resolveBoolArg hG F hc
    dsimp only [pcStepAux]
    rcases argRel_cases hoc with ⟨_, _, h1, h2, hm⟩ | ⟨cb, h1, h2⟩ <;> simp [h1, h2]
    · exact .emit (.mk _ (.cons (.var hm)
          (.cons (argRel_pRel hG hx).1 (.cons (argRel_pRel hG hy).1 .nil))))
        fun xs₁ xs₂ => trel_freshPVals_rel xs₁ xs₂ next
    · cases cb
      · exact .elim (.cons (argRel_toPVal_rel hG hy) .nil)
      · exact .elim (.cons (argRel_toPVal_rel hG hx) .nil)
  | zext m n =>
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [pcStepAux]
    rw [pRelArg_pFKey_eq hG ha]
    by_cases hm : m ≤ n
    · simp only [hm, ↓reduceDIte]
      cases pFKey _ with
      | some sk =>
        exact .emit (.mk _ (.cons (argRel_pRel hG ha).1 .nil))
          fun xs₁ xs₂ => wrapExt_rel next .zext m n hm sk xs₁ xs₂
      | none =>
        exact .emit (.mk _ (.cons (argRel_pRel hG ha).1 .nil))
          fun xs₁ xs₂ => trel_freshPVals_rel xs₁ xs₂ next
    · simp only [hm, ↓reduceDIte]
      exact .emit (.mk _ (.cons (argRel_pRel hG ha).1 .nil))
        fun xs₁ xs₂ => trel_freshPVals_rel xs₁ xs₂ next
  | sext m n =>
    rcases hargs with _ | ⟨ha, _⟩
    dsimp only [pcStepAux]
    rw [pRelArg_pFKey_eq hG ha]
    by_cases hm : m ≤ n
    · simp only [hm, ↓reduceDIte]
      cases pFKey _ with
      | some sk =>
        exact .emit (.mk _ (.cons (argRel_pRel hG ha).1 .nil))
          fun xs₁ xs₂ => wrapExt_rel next .sext m n hm sk xs₁ xs₂
      | none =>
        exact .emit (.mk _ (.cons (argRel_pRel hG ha).1 .nil))
          fun xs₁ xs₂ => trel_freshPVals_rel xs₁ xs₂ next
    · simp only [hm, ↓reduceDIte]
      exact .emit (.mk _ (.cons (argRel_pRel hG ha).1 .nil))
        fun xs₁ xs₂ => trel_freshPVals_rel xs₁ xs₂ next
  | cmp o t m h =>
    subst h
    cases t with
    | bits w =>
      rcases args₁ with ⟨a₁, b₁, _⟩; rcases args₂ with ⟨a₂, b₂, _⟩
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
      obtain ⟨hoa, _⟩ := argRel_pRel hG ha
      obtain ⟨hob, _⟩ := argRel_pRel hG hb
      have hiea := pRelArg_imm?_eq hoa
      have hieb := pRelArg_imm?_eq hob
      cases h2a : (pOut a₂).imm? <;> cases h2b : (pOut b₂).imm?
      · have h1a : (pOut a₁).imm? = none := hiea.trans h2a
        rw [pcStepAux_cmpBits_n_ F next o h1a, pcStepAux_cmpBits_n_ F next o h2a]
        exact pcCmpBitsSym_rel hG F next o o ha hb ha hb
      · have h1a : (pOut a₁).imm? = none := hiea.trans h2a
        rw [pcStepAux_cmpBits_n_ F next o h1a, pcStepAux_cmpBits_n_ F next o h2a]
        exact pcCmpBitsSym_rel hG F next o o ha hb ha hb
      · rename_i ca
        have h1a : (pOut a₁).imm? = some ca := hiea.trans h2a
        have h1b : (pOut b₁).imm? = none := hieb.trans h2b
        rw [pcStepAux_cmpBits_sn F next o h1a h1b, pcStepAux_cmpBits_sn F next o h2a h2b]
        exact pcCmpBitsSym_rel hG F next o o.swap ha hb hb ha
      · rename_i ca cb
        have h1a : (pOut a₁).imm? = some ca := hiea.trans h2a
        have h1b : (pOut b₁).imm? = some cb := hieb.trans h2b
        rw [pcStepAux_cmpBits_ss F next o h1a h1b, pcStepAux_cmpBits_ss F next o h2a h2b]
        exact .elim (.cons (pRelVal_imm _) .nil)
    | bool =>
      rcases args₁ with ⟨a₁, b₁, _⟩; rcases args₂ with ⟨a₂, b₂, _⟩
      rcases hargs with _ | ⟨ha, _ | ⟨hb, _⟩⟩
      obtain ⟨hoa, hia⟩ := argRel_resolveBoolArg hG F ha
      obtain ⟨hob, hib⟩ := argRel_resolveBoolArg hG F hb
      have hva := argRel_resolveBoolArg_rel hG F ha
      have hvb := argRel_resolveBoolArg_rel hG F hb
      have hn1 : ((none : Option Bool) == some true) = false := rfl
      have hn2 : ((none : Option Bool) == some false) = false := rfl
      dsimp only [pcStepAux]
      have hiea := pRelArg_imm?_eq hoa
      have hieb := pRelArg_imm?_eq hob
      have hfka : pFKey (resolveBoolArg F a₁) = pFKey (resolveBoolArg F a₂) := by
        dsimp only [pFKey]; rw [hia]
        rcases argRel_cases hoa with ⟨_, _, h1, h2, _⟩ | ⟨_, h1, h2⟩ <;> simp [h1, h2]
      have hfkb : pFKey (resolveBoolArg F b₁) = pFKey (resolveBoolArg F b₂) := by
        dsimp only [pFKey]; rw [hib]
        rcases argRel_cases hob with ⟨_, _, h1, h2, _⟩ | ⟨_, h1, h2⟩ <;> simp [h1, h2]
      rw [hiea, hieb, hfka, hfkb, hia, hib]
      cases (pOut (resolveBoolArg F a₂)).imm? <;>
        cases (pOut (resolveBoolArg F b₂)).imm? <;>
        dsimp only
      · simp only [hn1, hn2, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        cases pFKey (resolveBoolArg F a₂) <;> cases pFKey (resolveBoolArg F b₂) <;> dsimp only
        case some.some ka kb =>
          by_cases hbeq : fKeyBeq ka kb = true
          · simp only [hbeq, ↓reduceIte]; exact .elim (.cons (pRelVal_imm _) .nil)
          · simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
            cases queryCmpBool F o ka kb with
            | some _ => exact .elim (.cons (pRelVal_imm _) .nil)
            | none =>
              exact .emit (.mk _ (.cons hoa (.cons hob .nil)))
                fun xs₁ xs₂ => wrapBool_rel _ _ _ xs₁ xs₂
        all_goals
          exact .emit (.mk _ (.cons hoa (.cons hob .nil))) fun xs₁ xs₂ =>
            trel_freshPVals_rel xs₁ xs₂ next
      · rename_i cb
        simp only [hn1, hn2, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        by_cases h1 : (o == .eq && some cb == some true) = true
        · simp only [h1, ↓reduceIte]; exact .elim (.cons hva .nil)
        · simp only [h1, Bool.false_eq_true, ↓reduceIte]
          by_cases h3 : (o == .ne && some cb == some false) = true
          · simp only [h3, ↓reduceIte]; exact .elim (.cons hva .nil)
          · simp only [h3, Bool.false_eq_true, ↓reduceIte]
            cases pFKey (resolveBoolArg F a₂) <;> cases pFKey (resolveBoolArg F b₂) <;> dsimp only
            case some.some ka kb =>
              by_cases hbeq : fKeyBeq ka kb = true
              · simp only [hbeq, ↓reduceIte]; exact .elim (.cons (pRelVal_imm _) .nil)
              · simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
                cases queryCmpBool F o ka kb with
                | some _ => exact .elim (.cons (pRelVal_imm _) .nil)
                | none =>
                  exact .emit (.mk _ (.cons hoa (.cons hob .nil)))
                    fun xs₁ xs₂ => wrapBool_rel _ _ _ xs₁ xs₂
            all_goals
              exact .emit (.mk _ (.cons hoa (.cons hob .nil)))
                fun xs₁ xs₂ => trel_freshPVals_rel xs₁ xs₂ next
      · rename_i ca
        simp only [hn1, hn2, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        by_cases h2 : (o == .eq && some ca == some true) = true
        · simp only [h2, ↓reduceIte]; exact .elim (.cons hvb .nil)
        · simp only [h2, Bool.false_eq_true, ↓reduceIte]
          by_cases h4 : (o == .ne && some ca == some false) = true
          · simp only [h4, ↓reduceIte]; exact .elim (.cons hvb .nil)
          · simp only [h4, Bool.false_eq_true, ↓reduceIte]
            cases pFKey (resolveBoolArg F a₂) <;> cases pFKey (resolveBoolArg F b₂) <;> dsimp only
            case some.some ka kb =>
              by_cases hbeq : fKeyBeq ka kb = true
              · simp only [hbeq, ↓reduceIte]; exact .elim (.cons (pRelVal_imm _) .nil)
              · simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
                cases queryCmpBool F o ka kb with
                | some _ => exact .elim (.cons (pRelVal_imm _) .nil)
                | none =>
                  exact .emit (.mk _ (.cons hoa (.cons hob .nil)))
                    fun xs₁ xs₂ => wrapBool_rel _ _ _ xs₁ xs₂
            all_goals
              exact .emit (.mk _ (.cons hoa (.cons hob .nil)))
                fun xs₁ xs₂ => trel_freshPVals_rel xs₁ xs₂ next
      · exact .elim (.cons (pRelVal_imm _) .nil)
    | float _ | pair _ _ =>
      exact .emit (.mk _ (trel_pOut_rel hG hargs)) fun xs₁ xs₂ => trel_freshPVals_rel xs₁ xs₂ next
  | _ =>
    exact .emit (.mk _ (trel_pOut_rel hG hargs)) fun xs₁ xs₂ => trel_freshPVals_rel xs₁ xs₂ next

end

theorem pathCondOpt_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx (PVal V₁) (PVal V₂)} {D : Ctx L₁ L₂}
    {e₁ : Expr (PVal V₁) L₁ rs} {e₂ : Expr (PVal V₂) L₂ rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ {G' : Ctx V₁ V₂}, PRelG G' G → ∀ b F, Wf G' D (pathCondOpt b F e₁) (pathCondOpt b F e₂) := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop _ ih =>
    intro G' hG b F
    cases hop with
    | @mk sig _ code args₁ args₂ hargs =>
      have hrel := pcStep_rel hG F b code hargs
      unfold pathCondOpt
      dsimp only [pcStep]
      generalize pcStepAux code args₁ F b = st₁ at hrel ⊢
      generalize pcStepAux code args₂ F b = st₂ at hrel ⊢
      cases hrel with
      | elim hr => exact ih _ _ (hG.append_tup hr) b F
      | emit hop' hw =>
        refine .let_ hop' fun xs₁ xs₂ => ?_
        have hG' : PRelG (Tup.zip xs₁ xs₂ ++ G') G :=
          hG.weaken fun _ hq => List.mem_append_right _ hq
        exact ih _ _ (hG'.append_tup (hw xs₁ xs₂)) (b + ts.length) F
  | load t ha _ ih =>
    intro G' hG b F
    exact .load t (argRel_pRel hG ha).1 fun v₁ v₂ => ih _ _ (hG.freshOne v₁ v₂ b) (b + 1) F
  | store hv ha _ ih =>
    intro G' hG b F
    exact .store (argRel_pRel hG hv).1 (argRel_pRel hG ha).1 (ih hG b F)
  | call f hargs _ ih =>
    intro G' hG b F
    exact .call f (trel_pOut_rel hG hargs) fun xs₁ xs₂ =>
      ih _ _ (hG.freshPVals xs₁ xs₂ b) (b + _) F
  | jnz hc _ _ iht ihe =>
    intro G' hG b F
    obtain ⟨ho, hi⟩ := argRel_pRel hG hc
    dsimp only [pathCondOpt]
    rw [pRelArg_resolveBool?_eq hG F hc]
    cases resolveBool? F _ with
    | some bv => cases bv with | false => exact ihe hG b F | true => exact iht hG b F
    | none => rw [hi]; exact .jnz ho (iht hG b _) (ihe hG b _)
  | jump hj hargs =>
    intro G' hG _ F
    exact .jump hj (trel_resolveBoolArgs_rel hG F hargs)
  | ret hvs =>
    intro G' hG _ F
    exact .ret (trel_resolveBoolArgs_rel hG F hvs)
  | exit f hargs =>
    intro G' hG _ F
    exact .exit f (trel_resolveBoolArgs_rel hG F hargs)
  | hlt => intro _ _ _ _; exact .hlt
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro G' hG b F
    refine .group (fun Js₁ Js₂ => WfB.of_get fun i xs₁ xs₂ => ?_)
      (fun Js₁ Js₂ => ihk Js₁ Js₂ hG b F)
    rw [pathCondOptB_get, pathCondOptB_get]
    exact ihb Js₁ Js₂ i _ _ (hG.freshPVals xs₁ xs₂ b) (b + _) F

private theorem pathCondOptB_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    (b : Nat) (F : List BoolFact) :
    {sig : List (List Ty)} → (bs₁ : Blocks (PVal (fun _ => Unit)) (fun _ => Unit) rs sig) →
    (bs₂ : Blocks (fun _ => Unit) (fun _ => Unit) rs sig) →
    (∀ {ts} (i : Member ts sig), (bs₂.get i (Tup.units ts)).callsOk allowed exits →
      (pathCondOpt (b + ts.length) F (bs₁.get i (freshPVals ts (Tup.units ts) b))).callsOk
        allowed exits) →
    bs₂.callsOk allowed exits → (pathCondOptB b F bs₁).callsOk allowed exits
  | _, .nil, .nil, _, _ => trivial
  | _, .cons _ _, .cons _ _, h, hc =>
    ⟨h .here hc.1, pathCondOptB_callsOk b F _ _ (fun i => h (.there i)) hc.2⟩

theorem pathCondOpt_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {G : Ctx (PVal (fun _ => Unit)) (fun _ => Unit)} {D : Ctx (fun _ => Unit) (fun _ => Unit)}
    {e₁ : Expr (PVal (fun _ => Unit)) (fun _ => Unit) rs}
    {e₂ : Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ b F, e₂.callsOk allowed exits → (pathCondOpt b F e₁).callsOk allowed exits := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ _ _ ih =>
    intro b F hc
    unfold pathCondOpt
    dsimp only [pcStep]
    cases pcStepAux op₁.code op₁.args F b with
    | elim res => exact ih res (Tup.units ts) b F hc
    | emit op' wrap => exact ih (wrap (Tup.units ts)) (Tup.units ts) (b + ts.length) F hc
  | load _ _ _ ih => intro b F hc; exact ih _ () (b + 1) F hc
  | store _ _ _ ih => intro b F hc; exact ih b F hc
  | call _ _ _ ih => intro b F hc; exact ⟨hc.1, ih _ (Tup.units _) (b + _) F hc.2⟩
  | jnz _ _ _ iht ihe =>
    intro b F ⟨ht, he⟩
    dsimp only [pathCondOpt]
    cases resolveBool? F _ with
    | some bv => cases bv with | false => exact ihe b F he | true => exact iht b F ht
    | none => exact ⟨iht b _ ht, ihe b _ he⟩
  | jump _ _ | ret _ | hlt => intro _ _ _; trivial
  | exit _ _ => intro _ _ hc; exact hc
  | @group _ _ sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro b F hc
    exact ⟨pathCondOptB_callsOk b F _ _
      (fun i hci => ihb (Tup.units sig) (Tup.units sig) i _ (Tup.units _) _ F hci) hc.1,
      ihk (Tup.units sig) (Tup.units sig) b F hc.2⟩

end CondThreadOptImpl

theorem Func.pathCondOpt_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    (Func.pathCondOpt f).Wf := by
  intro V₁ V₂ L₁ L₂ xs₁ xs₂
  have hwf := hf (PVal V₁) (PVal V₂) L₁ L₂ (freshPVals as xs₁ 0) (freshPVals as xs₂ 0)
  have hrel : CondThreadOptImpl.PRelG (Tup.zip xs₁ xs₂)
      (Tup.zip (freshPVals as xs₁ 0) (freshPVals as xs₂ 0)) := by
    simpa using CondThreadOptImpl.PRelG.freshPVals (G := []) (G' := [])
      (fun _ hp => nomatch hp) xs₁ xs₂ 0
  exact CondThreadOptImpl.pathCondOpt_wf hwf hrel as.length []

theorem Func.pathCondOpt_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.pathCondOpt f) xs m Q X := by
  have hwf := hf (PVal Val) Val Cont Cont (freshPVals as xs 0) xs
  have hgood : CondThreadOptImpl.PGoodCtx (CondThreadOptImpl.PEnv.updTup (fun _ => none) 0 xs)
      as.length (Tup.zip (freshPVals as xs 0) xs) := by
    simpa using CondThreadOptImpl.PGoodCtx.freshPVals (ρ := fun _ => none) (b := 0) (G := [])
      (fun _ hp => nomatch hp) xs
  exact CondThreadOptImpl.pathCondOpt_wp hwf (fun _ hp => nomatch hp) as.length _ [] hgood
    CondThreadOptImpl.FactsOk.nil m h

theorem Func.pathCondOpt_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.pathCondOpt f) (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk
      allowed exits :=
  CondThreadOptImpl.pathCondOpt_callsOk
    (hf (PVal (fun _ => Unit)) (fun _ => Unit) (fun _ => Unit) (fun _ => Unit)
      (freshPVals as (Tup.units as) 0) (Tup.units as)) as.length [] hc

/-! ## Part 2: Soundness of `condThreadPass` -/

namespace CondThreadOptImpl

/-! ### `Member` tuple operations (`getTupMem`, `dropTupMem`, `insertTupMem`) -/

theorem getTupMem_insertTupMem {f : Ty → Type} {u : Ty} :
    {ts : List Ty} → (m : Member u ts) → (v : f u) → (xs : Tup f (eraseMem m)) →
    getTupMem m (insertTupMem m v xs) = v
  | _ :: _, .here, _, _ => rfl
  | _ :: _, .there m, v, xs => getTupMem_insertTupMem m v xs.2

theorem dropTupMem_insertTupMem {f : Ty → Type} {u : Ty} :
    {ts : List Ty} → (m : Member u ts) → (v : f u) → (xs : Tup f (eraseMem m)) →
    dropTupMem m (insertTupMem m v xs) = xs
  | _ :: _, .here, _, _ => rfl
  | _ :: _, .there m, v, xs => Prod.ext rfl (dropTupMem_insertTupMem m v xs.2)

theorem insertTupMem_get_drop {f : Ty → Type} {u : Ty} :
    {ts : List Ty} → (m : Member u ts) → (xs : Tup f ts) →
    insertTupMem m (getTupMem m xs) (dropTupMem m xs) = xs
  | _ :: _, .here, (_, _) => rfl
  | _ :: _, .there m, (_, xs) => Prod.ext rfl (insertTupMem_get_drop m xs)

theorem getTupMem_vals {u : Ty} :
    {ts : List Ty} → (m : Member u ts) → (args : Tup (Arg Val) ts) →
    (getTupMem m args).val = getTupMem m (vals args)
  | _ :: _, .here, (_, _) => rfl
  | _ :: _, .there m, (_, args) => getTupMem_vals m args

theorem dropTupMem_vals {u : Ty} :
    {ts : List Ty} → (m : Member u ts) → (args : Tup (Arg Val) ts) →
    vals (dropTupMem m args) = dropTupMem m (vals args)
  | _ :: _, .here, (_, _) => rfl
  | _ :: _, .there m, (_, args) => Prod.ext rfl (dropTupMem_vals m args)

theorem getTupMem_toArgTup {V : Ty → Type} {u : Ty} :
    {ts : List Ty} → (m : Member u ts) → (xs : Tup V ts) →
    getTupMem m (toArgTup xs) = .var (getTupMem m xs)
  | _ :: _, .here, (_, _) => rfl
  | _ :: _, .there m, (_, xs) => getTupMem_toArgTup m xs

theorem dropTupMem_toArgTup {V : Ty → Type} {u : Ty} :
    {ts : List Ty} → (m : Member u ts) → (xs : Tup V ts) →
    dropTupMem m (toArgTup xs) = toArgTup (dropTupMem m xs)
  | _ :: _, .here, (_, _) => rfl
  | _ :: _, .there m, (_, xs) => Prod.ext rfl (dropTupMem_toArgTup m xs)

theorem trel_getTupMem {f g : Ty → Type} {R : ∀ t, f t → g t → Prop} {u : Ty} :
    {ts : List Ty} → (m : Member u ts) → {xs : Tup f ts} → {ys : Tup g ts} →
    TRel R xs ys → R u (getTupMem m xs) (getTupMem m ys)
  | _ :: _, .here, (_, _), (_, _), .cons h _ => h
  | _ :: _, .there m, (_, _), (_, _), .cons _ hs => trel_getTupMem m hs

theorem trel_dropTupMem {f g : Ty → Type} {R : ∀ t, f t → g t → Prop} {u : Ty} :
    {ts : List Ty} → (m : Member u ts) → {xs : Tup f ts} → {ys : Tup g ts} →
    TRel R xs ys → TRel R (dropTupMem m xs) (dropTupMem m ys)
  | _ :: _, .here, (_, _), (_, _), .cons _ hs => hs
  | _ :: _, .there m, (_, _), (_, _), .cons h hs => .cons h (trel_dropTupMem m hs)

theorem trel_insertTupMem {f g : Ty → Type} {R : ∀ t, f t → g t → Prop} {u : Ty} :
    {ts : List Ty} → (m : Member u ts) → {v₁ : f u} → {v₂ : g u} →
    R u v₁ v₂ → {xs : Tup f (eraseMem m)} → {ys : Tup g (eraseMem m)} →
    TRel R xs ys → TRel R (insertTupMem m v₁ xs) (insertTupMem m v₂ ys)
  | _ :: _, .here, _, _, hv, _, _, hxs => .cons hv hxs
  | _ :: _ :: _, .there m, _, _, hv, _, _, hxs => by
    cases hxs with
    | cons hx hxs' => exact .cons hx (trel_insertTupMem m hv hxs')

/-! ### `immsTup` and `evalThreadLet?` lemmas -/

private theorem tupImms?_vals :
    {ts : List Ty} → {a : Tup (Arg Val) ts} → {cs : Tup Val ts} →
    tupImms? a = some cs → vals a = cs
  | [], (), (), _ => rfl
  | _ :: _, (.imm _, _), (_, _), h => by
    dsimp only [tupImms?, Arg.imm?, Option.bind] at h
    cases hc : tupImms? _ with
    | none => rw [hc] at h; cases h
    | some cs' =>
      rw [hc] at h; simp only [Option.pure_def] at h
      cases h; exact Prod.ext rfl (tupImms?_vals hc)
  | _ :: _, (.var _, _), (_, _), h => by dsimp only [tupImms?, Arg.imm?] at h; cases h

theorem immsTup_vals : {ts : List Ty} → (cs : Tup Val ts) → vals (immsTup cs) = cs
  | [], () => rfl
  | _ :: _, (_, cs) => Prod.ext rfl (immsTup_vals cs)

theorem trel_immsTup {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} :
    {ts : List Ty} → (cs : Tup Val ts) → TRel (ArgRel G) (immsTup cs) (immsTup cs)
  | [], () => .nil
  | _ :: _, (c, cs) => .cons (.imm c) (trel_immsTup cs)

theorem trel_immsTup_shape {V₁ V₂ : Ty → Type} :
    {ts : List Ty} → (cs : Tup Val ts) →
    TRel (fun _ a₁ a₂ => @Arg.imm? V₁ _ a₁ = @Arg.imm? V₂ _ a₂) (immsTup cs) (immsTup cs)
  | [], () => .nil
  | _ :: _, (_, cs) => .cons rfl (trel_immsTup_shape cs)

theorem tupImms?_shape_eq {V₁ V₂ : Ty → Type} :
    {ts : List Ty} → {a₁ : Tup (Arg V₁) ts} → {a₂ : Tup (Arg V₂) ts} →
    TRel (fun _ x₁ x₂ => x₁.imm? = x₂.imm?) a₁ a₂ →
    tupImms? a₁ = tupImms? a₂
  | [], (), (), .nil => rfl
  | _ :: _, (x₁, xs₁), (x₂, xs₂), .cons hx hxs => by
    dsimp only [tupImms?]
    rw [hx, tupImms?_shape_eq hxs]

theorem evalThreadLet?_wp {sig dts : List Ty} (code : OpCode sig dts)
    {args₁ : Tup (Arg Val) sig} {args₂ : Tup (Arg Val) sig} (hargs : vals args₁ = vals args₂)
    {out : Tup (Arg Val) dts} (heval : evalThreadLet? code args₁ = some out)
    {post : Tup Val dts → Prop} (hw : code.wp (vals args₂) post) :
    post (vals out) := by
  rw [← hargs] at hw
  cases code with
  | copy _ =>
    rcases args₁ with ⟨a, _⟩
    dsimp only [evalThreadLet?] at heval; cases heval
    exact hw
  | _ =>
    all_goals
      dsimp only [evalThreadLet?] at heval
      split at heval
      · simp only [Option.map_eq_some_iff, Option.bind_eq_some_iff] at heval
        rcases heval with ⟨cs, hcs, rfl⟩
        rw [immsTup_vals]
        rcases hcs with ⟨vts, hv, hev⟩
        have hvv := tupImms?_vals hv
        rw [hvv] at hw
        exact OpCode.eval?_sound _ vts post hev hw
      · cases heval

theorem evalThreadLet?_rel {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂} {sig dts : List Ty}
    (code : OpCode sig dts) {a₁ : Tup (Arg V₁) sig} {a₂ : Tup (Arg V₂) sig}
    (ha : TRel (ArgRel G') a₁ a₂) :
    (evalThreadLet? code a₁ = none ∧ evalThreadLet? code a₂ = none) ∨
    ∃ o₁ o₂, evalThreadLet? code a₁ = some o₁ ∧ evalThreadLet? code a₂ = some o₂ ∧
      TRel (ArgRel G') o₁ o₂ := by
  have hsh : TRel (fun _ x₁ x₂ => x₁.imm? = x₂.imm?) a₁ a₂ :=
    TRel.mono (fun _ _ _ h => by cases h <;> rfl) ha
  cases code with
  | copy _ =>
    rcases a₁ with ⟨x₁, _⟩; rcases a₂ with ⟨x₂, _⟩
    rcases ha with _ | ⟨hx, _⟩
    exact Or.inr ⟨(x₁, ()), (x₂, ()), rfl, rfl, .cons hx .nil⟩
  | _ =>
    all_goals
      dsimp only [evalThreadLet?]
      split
      · rw [tupImms?_shape_eq hsh]
        cases (tupImms? a₂).bind _ with
        | none => exact Or.inl ⟨rfl, rfl⟩
        | some cs => exact Or.inr ⟨immsTup cs, immsTup cs, rfl, rfl, trel_immsTup cs⟩
      · exact Or.inl ⟨rfl, rfl⟩

theorem evalThreadLet?_shape {V₁ V₂ : Ty → Type} {sig dts : List Ty}
    (code : OpCode sig dts) {a₁ : Tup (Arg V₁) sig} {a₂ : Tup (Arg V₂) sig}
    (hsh : TRel (fun _ x₁ x₂ => x₁.imm? = x₂.imm?) a₁ a₂) :
    (evalThreadLet? code a₁ = none ∧ evalThreadLet? code a₂ = none) ∨
    ∃ o₁ o₂, evalThreadLet? code a₁ = some o₁ ∧ evalThreadLet? code a₂ = some o₂ ∧
      TRel (fun _ x₁ x₂ => x₁.imm? = x₂.imm?) o₁ o₂ := by
  cases code with
  | copy _ =>
    rcases a₁ with ⟨x₁, _⟩; rcases a₂ with ⟨x₂, _⟩
    rcases hsh with _ | ⟨hx, _⟩
    exact Or.inr ⟨(x₁, ()), (x₂, ()), rfl, rfl, .cons hx .nil⟩
  | _ =>
    all_goals
      dsimp only [evalThreadLet?]
      split
      · rw [tupImms?_shape_eq hsh]
        cases (tupImms? a₂).bind _ with
        | none => exact Or.inl ⟨rfl, rfl⟩
        | some cs => exact Or.inr ⟨immsTup cs, immsTup cs, rfl, rfl, trel_immsTup_shape cs⟩
      · exact Or.inl ⟨rfl, rfl⟩

/-! ### Relational invariants for `CTOptV`, `rewriteCTAux`, and `validateCTPlan` -/

/-- Shape compatibility between `Arg V₁` and `Arg V₂` (identical immediate/variable tag and constant). -/
@[expose] def ArgShapeEq {V₁ V₂ : Ty → Type} {t : Ty} (a₁ : Arg V₁ t) (a₂ : Arg V₂ t) : Prop :=
  a₁.imm? = a₂.imm?

theorem ArgShapeEq.flattenArg {V₁ V₂ : Ty → Type} {G : Ctx (Arg V₁) (Arg V₂)}
    (hG : ∀ p ∈ G, ArgShapeEq p.2.1 p.2.2) {t : Ty} {a₁ : Arg (Arg V₁) t} {a₂ : Arg (Arg V₂) t} :
    ArgRel G t a₁ a₂ → ArgShapeEq (LeanQbe.T.flattenArg a₁) (LeanQbe.T.flattenArg a₂)
  | .var hm => hG _ hm
  | .imm _ => rfl

theorem trel_flattenArgs_shape {V₁ V₂ : Ty → Type} {G : Ctx (Arg V₁) (Arg V₂)}
    (hG : ∀ p ∈ G, ArgShapeEq p.2.1 p.2.2) {ts : List Ty} {a₁ : Tup (Arg (Arg V₁)) ts}
    {a₂ : Tup (Arg (Arg V₂)) ts} (ha : TRel (ArgRel G) a₁ a₂) :
    TRel (fun _ => ArgShapeEq) (flattenArgs a₁) (flattenArgs a₂) :=
  TRel.tupMapArg_rel (fun _ => flattenArg) (fun _ => flattenArg)
    (fun h => ArgShapeEq.flattenArg hG h) ha

theorem toOptArgTup_shape_zip {V₁ V₂ : Ty → Type} :
    {ts : List Ty} → (xs₁ : Tup V₁ ts) → (xs₂ : Tup V₂ ts) →
    ∀ p ∈ Tup.zip (toOptArgTup xs₁) (toOptArgTup xs₂), ArgShapeEq p.2.1 p.2.2
  | [], (), (), _, hp => nomatch hp
  | _ :: _, (_, _), (_, _), _, hp => by
    cases hp with
    | head => rfl
    | tail _ hp => exact toOptArgTup_shape_zip _ _ _ hp

theorem none_toOptArgTup_shape_zip {V₁ V₂ : Ty → Type} :
    {ts : List Ty} → (xs₂ : Tup V₂ ts) →
    ∀ p ∈ Tup.zip (noneArgTup (V := V₁) ts) (toOptArgTup xs₂), ArgShapeEq p.2.1 p.2.2
  | [], (), _, hp => nomatch hp
  | _ :: _, (_, _), _, hp => by
    cases hp with
    | head => rfl
    | tail _ hp => exact none_toOptArgTup_shape_zip _ _ hp

theorem ArgShapeEq.mem_zip {V₁ V₂ : Ty → Type} :
    {ts : List Ty} → {a₁ : Tup (Arg V₁) ts} → {a₂ : Tup (Arg V₂) ts} →
    TRel (fun _ => ArgShapeEq) a₁ a₂ → ∀ p ∈ Tup.zip a₁ a₂, ArgShapeEq p.2.1 p.2.2
  | [], (), (), .nil, _, hp => nomatch hp
  | _ :: _, (_, _), (_, _), .cons h hs, _, hp => by
    cases hp with
    | head => exact h
    | tail _ hp => exact ArgShapeEq.mem_zip hs _ hp

/-- Optionalized operand relation disallowing `.var none`. -/
inductive OptArgRel {V₁ V₂ : Ty → Type} (G' : Ctx V₁ V₂) :
    (t : Ty) → Arg (CTOptV V₁) t → Arg (CTOptV V₂) t → Prop
  | var {t : Ty} {v₁ : V₁ t} {v₂ : V₂ t} : ⟨t, v₁, v₂⟩ ∈ G' →
      OptArgRel G' t (.var (some v₁)) (.var (some v₂))
  | imm {t : Ty} (c : Val t) : OptArgRel G' t (.imm c) (.imm c)

theorem OptArgRel.weaken {V₁ V₂ : Ty → Type} {G₁ G₂ : Ctx V₁ V₂}
    (hG : ∀ p ∈ G₁, p ∈ G₂) {t : Ty} {a₁ : Arg (CTOptV V₁) t} {a₂ : Arg (CTOptV V₂) t} :
    OptArgRel G₁ t a₁ a₂ → OptArgRel G₂ t a₁ a₂
  | .var hm => .var (hG _ hm)
  | .imm c => .imm c

theorem OptArgRel.shape {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂} {t : Ty}
    {a₁ : Arg (CTOptV V₁) t} {a₂ : Arg (CTOptV V₂) t} :
    OptArgRel G' t a₁ a₂ → ArgShapeEq a₁ a₂
  | .var _ => rfl
  | .imm _ => rfl

theorem OptArgRel.toRealArg? {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂} {t : Ty}
    {a₁ : Arg (CTOptV V₁) t} {a₂ : Arg (CTOptV V₂) t} :
    OptArgRel G' t a₁ a₂ →
    ∃ r₁ r₂, LeanQbe.T.CondThreadOpt.toRealArg? a₁ = some r₁ ∧
      LeanQbe.T.CondThreadOpt.toRealArg? a₂ = some r₂ ∧ ArgRel G' t r₁ r₂
  | .var hm => ⟨.var _, .var _, rfl, rfl, .var hm⟩
  | .imm c => ⟨.imm c, .imm c, rfl, rfl, .imm c⟩

theorem trel_toRealArgs?_rel {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂} :
    {ts : List Ty} → {a₁ : Tup (Arg (CTOptV V₁)) ts} → {a₂ : Tup (Arg (CTOptV V₂)) ts} →
    TRel (OptArgRel G') a₁ a₂ →
    ∃ r₁ r₂, LeanQbe.T.CondThreadOpt.toRealArgs? a₁ = some r₁ ∧
      LeanQbe.T.CondThreadOpt.toRealArgs? a₂ = some r₂ ∧ TRel (ArgRel G') r₁ r₂
  | [], (), (), .nil => ⟨(), (), rfl, rfl, .nil⟩
  | _ :: _, (_, _), (_, _), .cons ha has => by
    obtain ⟨r₁, r₂, hr₁, hr₂, hra⟩ := ha.toRealArg?
    obtain ⟨rs₁, rs₂, hrs₁, hrs₂, hras⟩ := trel_toRealArgs?_rel has
    refine ⟨(r₁, rs₁), (r₂, rs₂), ?_, ?_, .cons hra hras⟩
    · dsimp only [LeanQbe.T.CondThreadOpt.toRealArgs?]; rw [hr₁, hrs₁]; rfl
    · dsimp only [LeanQbe.T.CondThreadOpt.toRealArgs?]; rw [hr₂, hrs₂]; rfl

theorem OptArgRel.flattenArg {V₁ V₂ : Ty → Type} {G : Ctx (Arg (CTOptV V₁)) (Arg (CTOptV V₂))}
    {G' : Ctx V₁ V₂} (hG : ∀ p ∈ G, OptArgRel G' p.1 p.2.1 p.2.2) {t : Ty}
    {a₁ : Arg (Arg (CTOptV V₁)) t} {a₂ : Arg (Arg (CTOptV V₂)) t} :
    ArgRel G t a₁ a₂ → OptArgRel G' t (LeanQbe.T.flattenArg a₁) (LeanQbe.T.flattenArg a₂)
  | .var hm => hG _ hm
  | .imm c => .imm c

theorem trel_flattenArgs_opt {V₁ V₂ : Ty → Type} {G : Ctx (Arg (CTOptV V₁)) (Arg (CTOptV V₂))}
    {G' : Ctx V₁ V₂} (hG : ∀ p ∈ G, OptArgRel G' p.1 p.2.1 p.2.2) {ts : List Ty}
    {a₁ : Tup (Arg (Arg (CTOptV V₁))) ts} {a₂ : Tup (Arg (Arg (CTOptV V₂))) ts}
    (ha : TRel (ArgRel G) a₁ a₂) :
    TRel (OptArgRel G') (flattenArgs a₁) (flattenArgs a₂) :=
  TRel.tupMapArg_rel (fun _ => flattenArg) (fun _ => flattenArg)
    (fun h => OptArgRel.flattenArg hG h) ha

theorem toOptArgTup_trel {V₁ V₂ : Ty → Type} :
    {ts : List Ty} → (xs₁ : Tup V₁ ts) → (xs₂ : Tup V₂ ts) →
    TRel (OptArgRel (Tup.zip xs₁ xs₂)) (toOptArgTup xs₁) (toOptArgTup xs₂)
  | [], (), () => .nil
  | _ :: _, (_x₁, xs₁), (_x₂, xs₂) =>
    .cons (.var List.mem_cons_self)
      (TRel.mono (fun _ _ _ h => h.weaken (fun _ hp => List.mem_cons_of_mem _ hp))
        (toOptArgTup_trel xs₁ xs₂))

theorem mem_zip_optArgRel {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂} :
    {ts : List Ty} → {a₁ : Tup (Arg (CTOptV V₁)) ts} → {a₂ : Tup (Arg (CTOptV V₂)) ts} →
    TRel (OptArgRel G') a₁ a₂ → ∀ p ∈ Tup.zip a₁ a₂, OptArgRel G' p.1 p.2.1 p.2.2
  | [], (), (), .nil, _, hp => nomatch hp
  | _ :: _, (_, _), (_, _), .cons h hs, _, hp => by
    cases hp with
    | head => exact h
    | tail _ hp => exact mem_zip_optArgRel hs _ hp

theorem ctx_optArgRel_append {V₁ V₂ : Ty → Type} {G : Ctx (Arg (CTOptV V₁)) (Arg (CTOptV V₂))}
    {G' : Ctx V₁ V₂} {H' : Ctx V₁ V₂}
    {H : Ctx (Arg (CTOptV V₁)) (Arg (CTOptV V₂))}
    (hH : ∀ p ∈ H, OptArgRel H' p.1 p.2.1 p.2.2)
    (hG : ∀ p ∈ G, OptArgRel G' p.1 p.2.1 p.2.2) :
    ∀ p ∈ H ++ G, OptArgRel (H' ++ G') p.1 p.2.1 p.2.2 := fun p hp =>
  (List.mem_append.1 hp).elim
    (fun hm => (hH p hm).weaken (fun _ h => List.mem_append_left _ h))
    (fun hm => (hG p hm).weaken (fun _ h => List.mem_append_right _ h))

theorem ctx_optArgRel_append_same {V₁ V₂ : Ty → Type} {G : Ctx (Arg (CTOptV V₁)) (Arg (CTOptV V₂))}
    {G' : Ctx V₁ V₂} {H : Ctx (Arg (CTOptV V₁)) (Arg (CTOptV V₂))}
    (hH : ∀ p ∈ H, OptArgRel G' p.1 p.2.1 p.2.2)
    (hG : ∀ p ∈ G, OptArgRel G' p.1 p.2.1 p.2.2) :
    ∀ p ∈ H ++ G, OptArgRel G' p.1 p.2.1 p.2.2 := fun p hp =>
  (List.mem_append.1 hp).elim (hH p) (hG p)

theorem ctx_optArgRel_cons_var {V₁ V₂ : Ty → Type} {G : Ctx (Arg (CTOptV V₁)) (Arg (CTOptV V₂))}
    {G' : Ctx V₁ V₂} (hG : ∀ p ∈ G, OptArgRel G' p.1 p.2.1 p.2.2) {t : Ty} (v₁ : V₁ t) (v₂ : V₂ t) :
    ∀ p ∈ (⟨t, .var (some v₁), .var (some v₂)⟩ :: G),
      OptArgRel (⟨t, v₁, v₂⟩ :: G') p.1 p.2.1 p.2.2 := fun p hp => by
  cases hp with
  | head => exact .var List.mem_cons_self
  | tail _ hm => exact (hG p hm).weaken (fun _ h => List.mem_cons_of_mem _ h)

theorem mem_zip_toOptArgTup {V₁ V₂ : Ty → Type} {ts : List Ty} (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts) :
    ∀ p ∈ Tup.zip (toOptArgTup xs₁) (toOptArgTup xs₂), OptArgRel
        (Tup.zip xs₁ xs₂) p.1 p.2.1 p.2.2 :=
  mem_zip_optArgRel (toOptArgTup_trel xs₁ xs₂)

theorem trel_immsTup_opt {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂} :
    {ts : List Ty} → (cs : Tup Val ts) →
    TRel (OptArgRel G') (immsTup cs) (immsTup cs)
  | [], () => .nil
  | _ :: _, (c, cs) => .cons (.imm c) (trel_immsTup_opt cs)

theorem evalThreadLet?_opt_rel {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂} {sig dts : List Ty}
    (code : OpCode sig dts) {a₁ : Tup (Arg (CTOptV V₁)) sig} {a₂ : Tup (Arg (CTOptV V₂)) sig}
    (ha : TRel (OptArgRel G') a₁ a₂) :
    (evalThreadLet? code a₁ = none ∧ evalThreadLet? code a₂ = none) ∨
    ∃ o₁ o₂, evalThreadLet? code a₁ = some o₁ ∧ evalThreadLet? code a₂ = some o₂ ∧
      TRel (OptArgRel G') o₁ o₂ := by
  have hsh : TRel (fun _ => ArgShapeEq) a₁ a₂ := TRel.mono (fun _ _ _ h => h.shape) ha
  cases code with
  | copy _ =>
    rcases a₁ with ⟨x₁, _⟩; rcases a₂ with ⟨x₂, _⟩
    rcases ha with _ | ⟨hx, _⟩
    exact Or.inr ⟨(x₁, ()), (x₂, ()), rfl, rfl, .cons hx .nil⟩
  | _ =>
    all_goals
      dsimp only [evalThreadLet?]
      split
      · rw [tupImms?_shape_eq hsh]
        cases (tupImms? a₂).bind _ with
        | none => exact Or.inl ⟨rfl, rfl⟩
        | some cs => exact Or.inr ⟨immsTup cs, immsTup cs, rfl, rfl, trel_immsTup_opt cs⟩
      · exact Or.inl ⟨rfl, rfl⟩

/-- Structural shape equivalence between two `CTTarget`s (agreeing on `.canEmit`). -/
@[expose] def CTTargetShape {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} :
    {ts : List Ty} → CTTarget V₁ L₁ ts → CTTarget V₂ L₂ ts → Prop
  | _, .keep _, .keep _ => True
  | _, .dead, .dead => True
  | _, .split m₁ lT1? lF1? lD1?, .split m₂ lT2? lF2? lD2? =>
      HEq m₁ m₂ ∧ (lT1?.isSome = lT2?.isSome) ∧ (lF1?.isSome = lF2?.isSome) ∧
        (lD1?.isSome = lD2?.isSome)
  | _, _, _ => False

theorem CTTargetShape.canEmit_eq {W₁ W₂ V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {ts : List Ty} {t₁ : CTTarget V₁ L₁ ts} {t₂ : CTTarget V₂ L₂ ts}
    (ht : CTTargetShape t₁ t₂) {a₁ : Tup (Arg W₁) ts} {a₂ : Tup (Arg W₂) ts}
    (ha : TRel (fun _ => ArgShapeEq) a₁ a₂) : t₁.canEmit a₁ = t₂.canEmit a₂ := by
  cases t₁ <;> cases t₂ <;> dsimp only [CTTargetShape] at ht <;> try contradiction
  · rfl
  · rfl
  · rcases ht with ⟨hm, hT, hF, hD⟩
    cases hm
    have hmem := trel_getTupMem ‹Member .bool ts› ha
    dsimp only [CTTarget.canEmit]
    cases e₁ : getTupMem _ a₁ <;> cases e₂ : getTupMem _ a₂ <;> rw [e₁, e₂] at hmem
    · simp only [hD, hT, hF]
    · dsimp only [ArgShapeEq, Arg.imm?] at hmem; cases hmem
    · dsimp only [ArgShapeEq, Arg.imm?] at hmem; cases hmem
    · rename_i b₁ b₂
      dsimp only [ArgShapeEq, Arg.imm?] at hmem; cases hmem
      first | (cases b₁ <;> simp only [hT, hF]) | (cases b₂ <;> simp only [hT, hF])

/-- Full relational invariant on `CTTarget` for `Wf` proofs (`rewriteCTAux_wf`). -/
@[expose] def CTTargetRel {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    (D' : Ctx L₁ L₂) : {ts : List Ty} → CTTarget V₁ L₁ ts → CTTarget V₂ L₂ ts → Prop
  | ts, .keep l₁, .keep l₂ => ⟨ts, l₁, l₂⟩ ∈ D'
  | _, .dead, .dead => True
  | ts, .split m₁ lT1? lF1? lD1?, .split m₂ lT2? lF2? lD2? =>
      ∃ hm : m₁ = m₂,
        ORel (fun l₁ l₂ => ⟨eraseMem m₁, l₁, l₂⟩ ∈ D') lT1? (hm ▸ lT2?) ∧
        ORel (fun l₁ l₂ => ⟨eraseMem m₁, l₁, l₂⟩ ∈ D') lF1? (hm ▸ lF2?) ∧
        ORel (fun l₁ l₂ => ⟨ts, l₁, l₂⟩ ∈ D') lD1? lD2?
  | _, _, _ => False

theorem CTTargetRel.weaken {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {D₁ D₂ : Ctx L₁ L₂} (hD : ∀ p ∈ D₁, p ∈ D₂) {ts : List Ty}
    {t₁ : CTTarget V₁ L₁ ts} {t₂ : CTTarget V₂ L₂ ts} :
    CTTargetRel D₁ t₁ t₂ → CTTargetRel D₂ t₁ t₂ := by
  cases t₁ with
  | keep _ =>
    cases t₂ <;> dsimp only [CTTargetRel] <;> try exact fun h => h
    exact fun h => hD _ h
  | dead => cases t₂ <;> dsimp only [CTTargetRel] <;> exact fun h => h
  | split m₁ lT1? lF1? lD1? =>
    cases t₂ with
    | keep _ | dead => dsimp only [CTTargetRel]; exact fun h => h
    | split m₂ lT2? lF2? lD2? =>
      dsimp only [CTTargetRel]
      rintro ⟨rfl, hT, hF, hDi⟩
      refine ⟨rfl, ?_, ?_, ?_⟩
      · cases lT1? <;> cases lT2? <;> simp_all [ORel]
      · cases lF1? <;> cases lF2? <;> simp_all [ORel]
      · cases lD1? <;> cases lD2? <;> simp_all [ORel]

theorem CTTargetRel.shape {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {D' : Ctx L₁ L₂} {ts : List Ty} {t₁ : CTTarget V₁ L₁ ts} {t₂ : CTTarget V₂ L₂ ts} :
    CTTargetRel D' t₁ t₂ → CTTargetShape t₁ t₂ := by
  cases t₁ with
  | keep _ | dead =>
    cases t₂ <;> dsimp only [CTTargetRel, CTTargetShape] <;>
      first | exact fun h => h | exact fun _ => trivial
  | split m₁ lT1? lF1? lD1? =>
    cases t₂ with
    | keep _ | dead => dsimp only [CTTargetRel, CTTargetShape]; exact fun h => h
    | split m₂ lT2? lF2? lD2? =>
      dsimp only [CTTargetRel, CTTargetShape]
      rintro ⟨rfl, hT, hF, hD⟩
      refine ⟨HEq.rfl, ?_, ?_, ?_⟩
      · cases lT1? <;> cases lT2? <;> simp_all [ORel]
      · cases lF1? <;> cases lF2? <;> simp_all [ORel]
      · cases lD1? <;> cases lD2? <;> simp_all [ORel]

theorem CTTargetRel.emit_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} {rs ts : List Ty}
    {t₁ : CTTarget V₁ L₁ ts} {t₂ : CTTarget V₂ L₂ ts} (ht : CTTargetRel D' t₁ t₂)
    {a₁ : Tup (Arg (CTOptV V₁)) ts} {a₂ : Tup (Arg (CTOptV V₂)) ts}
    (ha : TRel (OptArgRel G') a₁ a₂) :
    Wf G' D' (t₁.emit (rs := rs) a₁) (t₂.emit (rs := rs) a₂) := by
  obtain ⟨r₁, r₂, hr₁, hr₂, hr⟩ := trel_toRealArgs?_rel ha
  cases t₁ with
  | keep _ =>
    cases t₂ <;> dsimp only [CTTargetRel] at ht <;> try contradiction
    dsimp only [CTTarget.emit]; rw [hr₁, hr₂]; exact .jump ht hr
  | dead =>
    cases t₂ <;> dsimp only [CTTargetRel] at ht <;> try contradiction
    exact .hlt
  | split m lT1? lF1? lD1? =>
    cases t₂ with
    | keep _ => dsimp only [CTTargetRel] at ht; try exact False.elim ht
    | dead => dsimp only [CTTargetRel] at ht; try exact False.elim ht
    | split m₂ lT2? lF2? lD2? =>
      dsimp only [CTTargetRel] at ht
      rcases ht with ⟨rfl, hT, hF, hD⟩
      have hmem := trel_getTupMem m ha
      obtain ⟨dr₁, dr₂, hdr₁, hdr₂, hdr⟩ := trel_toRealArgs?_rel (trel_dropTupMem m ha)
      dsimp only [CTTarget.emit]
      cases e₁ : getTupMem m a₁ <;> cases e₂ : getTupMem m a₂ <;> rw [e₁, e₂] at hmem
      · cases hmem
        · rename_i v₁ v₂ hm
          dsimp only
          cases lD1? <;> cases lD2? <;> dsimp only [ORel] at hD <;> try contradiction
          · rw [hdr₁, hdr₂]
            cases lT1? <;> cases lT2? <;> dsimp only [ORel] at hT <;> try contradiction
            · exact .hlt
            · cases lF1? <;> cases lF2? <;> dsimp only [ORel] at hF <;> try contradiction
              · exact .hlt
              · exact .jnz (.var hm) (.jump hT hdr) (.jump hF hdr)
          · rw [hr₁, hr₂]; exact .jump hD hr
      · cases hmem
      · cases hmem
      · cases hmem; next b =>
        cases b
        · rw [hdr₁, hdr₂]
          cases lF1? <;> cases lF2? <;> dsimp only [ORel] at hF <;> try contradiction
          · exact .hlt
          · exact .jump hF hdr
        · rw [hdr₁, hdr₂]
          cases lT1? <;> cases lT2? <;> dsimp only [ORel] at hT <;> try contradiction
          · exact .hlt
          · exact .jump hT hdr

/-- `CTLabelRel` pairs two `CTLabel`s for both `Wf` proofs and `validateInline` simulation. -/
@[expose] def CTLabelRel {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (G' : Ctx V₁ V₂) (D' : Ctx L₁ L₂) {ts : List Ty}
    (l₁ : CTLabel V₁ L₁ rs ts) (l₂ : CTLabel V₂ L₂ rs ts) : Prop :=
  CTTargetRel D' l₁.target l₂.target ∧
    (∀ {G'' D''}, (∀ p ∈ G', p ∈ G'') → (∀ p ∈ D', p ∈ D'') →
      ∀ (a₁ : Tup (Arg (CTOptV V₁)) ts) (a₂ : Tup (Arg (CTOptV V₂)) ts),
        TRel (OptArgRel G'') a₁ a₂ → ORel (Wf G'' D'') (l₁.inline? a₁) (l₂.inline? a₂)) ∧
    (∀ (a₁ : Tup (Arg (CTOptV V₁)) ts) (a₂ : Tup (Arg (CTOptV V₂)) ts),
      TRel (fun _ => ArgShapeEq) a₁ a₂ → (l₁.inline? a₁).isSome = (l₂.inline? a₂).isSome)

theorem CTLabelRel.weaken {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G₁ G₂ : Ctx V₁ V₂} {D₁ D₂ : Ctx L₁ L₂}
    (hG : ∀ p ∈ G₁, p ∈ G₂) (hD : ∀ p ∈ D₁, p ∈ D₂) {ts : List Ty}
    {l₁ : CTLabel V₁ L₁ rs ts} {l₂ : CTLabel V₂ L₂ rs ts}
    (h : CTLabelRel G₁ D₁ l₁ l₂) : CTLabelRel G₂ D₂ l₁ l₂ :=
  ⟨h.1.weaken hD,
   fun hG' hD' => h.2.1 (fun _ hp => hG' _ (hG _ hp)) (fun _ hp => hD' _ (hD _ hp)),
   h.2.2⟩

@[expose] def CTDRel {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (G' : Ctx V₁ V₂) (D' : Ctx L₁ L₂)
    (D : Ctx (CTLabel V₁ L₁ rs) (CTLabel V₂ L₂ rs)) : Prop :=
  ∀ p ∈ D, CTLabelRel G' D' p.2.1 p.2.2

theorem CTDRel.weaken {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G₁ G₂ : Ctx V₁ V₂} {D₁ D₂ : Ctx L₁ L₂} {D : Ctx (CTLabel V₁ L₁ rs) (CTLabel V₂ L₂ rs)}
    (hG : ∀ p ∈ G₁, p ∈ G₂) (hD : ∀ p ∈ D₁, p ∈ D₂) (h : CTDRel G₁ D₁ D) : CTDRel G₂ D₂ D :=
  fun p hp => (h p hp).weaken hG hD

theorem CTDRel.append {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} {H D : Ctx (CTLabel V₁ L₁ rs) (CTLabel V₂ L₂ rs)}
    (hH : CTDRel G' D' H) (hD : CTDRel G' D' D) : CTDRel G' D' (H ++ D) := fun p hp =>
  (List.mem_append.1 hp).elim (hH p) (hD p)

/-- Inline-safety coherence for `CTLabel`: matching `canEmit` and `inline?.isSome` under shape eq. -/
@[expose] def CTLabelSim {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} {ts : List Ty}
    (l₁ : CTLabel V₁ L₁ rs ts) (l₂ : CTLabel V₂ L₂ rs ts) : Prop :=
  CTTargetShape l₁.target l₂.target ∧
    ∀ (a₁ : Tup (Arg (CTOptV V₁)) ts) (a₂ : Tup (Arg (CTOptV V₂)) ts),
      TRel (fun _ => ArgShapeEq) a₁ a₂ → (l₁.inline? a₁).isSome = (l₂.inline? a₂).isSome

@[expose] def CTDSim {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (D : Ctx (CTLabel V₁ L₁ rs) (CTLabel V₂ L₂ rs)) : Prop :=
  ∀ p ∈ D, CTLabelSim p.2.1 p.2.2

theorem CTDSim.append {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {H D : Ctx (CTLabel V₁ L₁ rs) (CTLabel V₂ L₂ rs)}
    (hH : CTDSim H) (hD : CTDSim D) : CTDSim (H ++ D) := fun p hp =>
  (List.mem_append.1 hp).elim (hH p) (hD p)

theorem CTLabelRel.toSim {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} {ts : List Ty}
    {l₁ : CTLabel V₁ L₁ rs ts} {l₂ : CTLabel V₂ L₂ rs ts}
    (h : CTLabelRel G' D' l₁ l₂) : CTLabelSim l₁ l₂ :=
  ⟨h.1.shape, h.2.2⟩

theorem CTDRel.toSim {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂}
    {D : Ctx (CTLabel V₁ L₁ rs) (CTLabel V₂ L₂ rs)} (h : CTDRel G' D' D) : CTDSim D :=
  fun p hp => (h p hp).toSim

theorem CTLabel.emitJump_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs ts : List Ty}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} (tryInl : Bool)
    {l₁ : CTLabel V₁ L₁ rs ts} {l₂ : CTLabel V₂ L₂ rs ts} (hl : CTLabelRel G' D' l₁ l₂)
    {a₁ : Tup (Arg (CTOptV V₁)) ts} {a₂ : Tup (Arg (CTOptV V₂)) ts}
    (ha : TRel (OptArgRel G') a₁ a₂) :
    Wf G' D' (l₁.emitJump tryInl a₁) (l₂.emitJump tryInl a₂) := by
  dsimp only [CTLabel.emitJump]
  cases tryInl
  · exact hl.1.emit_wf ha
  · have hor := hl.2.1 (fun _ h => h) (fun _ h => h) a₁ a₂ ha
    cases e₁ : l₁.inline? a₁ <;> cases e₂ : l₂.inline? a₂ <;> rw [e₁, e₂] at hor <;>
      dsimp only [ORel] at hor
    · exact hl.1.emit_wf ha
    · exact hor

/-! ### Inline peeling, inline validation, and `rewriteCTInline` relational soundness -/

theorem peelThreadHead_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    (fuel : Nat) → (res : Bool) → (p : CTPlan) →
    {G : Ctx (Arg (CTOptV V₁)) (Arg (CTOptV V₂))} →
    {D : Ctx (CTLabel V₁ L₁ rs) (CTLabel V₂ L₂ rs)} →
    {e₁ : Expr (Arg (CTOptV V₁)) (CTLabel V₁ L₁ rs) rs} →
    {e₂ : Expr (Arg (CTOptV V₂)) (CTLabel V₂ L₂ rs) rs} →
    Wf G D e₁ e₂ → {G' : Ctx V₁ V₂} →
    (∀ p ∈ G, OptArgRel G' p.1 p.2.1 p.2.2) →
    let r₁ := peelThreadHead fuel res p e₁
    let r₂ := peelThreadHead fuel res p e₂
    r₁.1 = r₂.1 ∧ r₁.2.1 = r₂.2.1 ∧
      ∃ G₁, (∀ p ∈ G₁, OptArgRel G' p.1 p.2.1 p.2.2) ∧ Wf G₁ D r₁.2.2 r₂.2.2
  | 0, _, _, G, _, _, _, hwf, _, hG => ⟨rfl, rfl, G, hG, hwf⟩
  | fuel + 1, res, p, G, D, _, _, hwf, G', hG => by
    cases p with
    | node1 pk =>
      have hwf0 := hwf
      cases hwf
      case let_ hop hk =>
        clear hwf0
        rcases hop with ⟨code, hargs⟩
        have hel := evalThreadLet?_opt_rel code (trel_flattenArgs_opt hG hargs)
        dsimp only [peelThreadHead]
        rcases hel with ⟨he₁, he₂⟩ | ⟨o₁, o₂, he₁, he₂, ho⟩
        · rw [he₁, he₂]; exact ⟨rfl, rfl, G, hG, .let_ (.mk code hargs) hk⟩
        · rw [he₁, he₂]
          exact peelThreadHead_wf fuel res pk (hk o₁ o₂)
            (ctx_optArgRel_append_same (mem_zip_optArgRel ho) hG)
      all_goals exact ⟨rfl, rfl, G, hG, hwf0⟩
    | node2 pt pe =>
      have hwf0 := hwf
      cases hwf
      case jnz hc ht he =>
        clear hwf0
        have hfl := OptArgRel.flattenArg hG hc
        dsimp only [peelThreadHead]
        cases e₁ : flattenArg _ <;> cases e₂ : flattenArg _ <;> rw [e₁, e₂] at hfl
        · exact ⟨rfl, rfl, G, hG, .jnz hc ht he⟩
        · cases hfl
        · cases hfl
        · cases hfl; next c => cases c with
          | false => exact peelThreadHead_wf fuel true pe he hG
          | true => exact peelThreadHead_wf fuel true pt ht hG
      all_goals exact ⟨rfl, rfl, G, hG, hwf0⟩
    | _ => exact ⟨rfl, rfl, G, hG, hwf⟩

theorem peelThreadHead_sim {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    (fuel : Nat) → (res : Bool) → (p : CTPlan) →
    {G : Ctx (Arg (CTOptV V₁)) (Arg (CTOptV V₂))} →
    {D : Ctx (CTLabel V₁ L₁ rs) (CTLabel V₂ L₂ rs)} →
    {e₁ : Expr (Arg (CTOptV V₁)) (CTLabel V₁ L₁ rs) rs} →
    {e₂ : Expr (Arg (CTOptV V₂)) (CTLabel V₂ L₂ rs) rs} →
    Wf G D e₁ e₂ → (∀ p ∈ G, ArgShapeEq p.2.1 p.2.2) →
    let r₁ := peelThreadHead fuel res p e₁
    let r₂ := peelThreadHead fuel res p e₂
    r₁.1 = r₂.1 ∧ r₁.2.1 = r₂.2.1 ∧
      ∃ G₁, (∀ p ∈ G₁, ArgShapeEq p.2.1 p.2.2) ∧ Wf G₁ D r₁.2.2 r₂.2.2
  | 0, _, _, G, _, _, _, hwf, hG => ⟨rfl, rfl, G, hG, hwf⟩
  | fuel + 1, res, p, G, D, _, _, hwf, hG => by
    cases p with
    | node1 pk =>
      have hwf0 := hwf
      cases hwf
      case let_ hop hk =>
        clear hwf0
        rcases hop with ⟨code, hargs⟩
        have hel := evalThreadLet?_shape code (trel_flattenArgs_shape hG hargs)
        dsimp only [peelThreadHead]
        rcases hel with ⟨he₁, he₂⟩ | ⟨o₁, o₂, he₁, he₂, ho⟩
        · rw [he₁, he₂]; exact ⟨rfl, rfl, G, hG, .let_ (.mk code hargs) hk⟩
        · rw [he₁, he₂]
          exact peelThreadHead_sim fuel res pk (hk o₁ o₂) fun p hp =>
            (List.mem_append.1 hp).elim (ArgShapeEq.mem_zip ho p) (hG p)
      all_goals exact ⟨rfl, rfl, G, hG, hwf0⟩
    | node2 pt pe =>
      have hwf0 := hwf
      cases hwf
      case jnz hc ht he =>
        clear hwf0
        have hsh := ArgShapeEq.flattenArg hG hc
        dsimp only [peelThreadHead]
        cases e₁ : flattenArg _ <;> cases e₂ : flattenArg _ <;> rw [e₁, e₂] at hsh
        · exact ⟨rfl, rfl, G, hG, .jnz hc ht he⟩
        · cases hsh
        · cases hsh
        · rename_i b₁ b₂
          dsimp only [ArgShapeEq, Arg.imm?] at hsh; cases hsh
          first
          | (cases b₁ <;> first
            | exact peelThreadHead_sim fuel true pe he hG
            | exact peelThreadHead_sim fuel true pt ht hG)
          | (cases b₂ <;> first
            | exact peelThreadHead_sim fuel true pe he hG
            | exact peelThreadHead_sim fuel true pt ht hG)
      all_goals exact ⟨rfl, rfl, G, hG, hwf0⟩
    | _ => exact ⟨rfl, rfl, G, hG, hwf⟩

private theorem mem_zip_noneArgTup_shape {V₁ V₂ : Ty → Type} :
    {ts : List Ty} → ∀ p ∈ Tup.zip (noneArgTup (V := V₁) ts) (noneArgTup (V := V₂) ts),
      ArgShapeEq p.2.1 p.2.2
  | [], _, hp => nomatch hp
  | _ :: _, _, hp => by
    cases hp with
    | head => rfl
    | tail _ hp => exact mem_zip_noneArgTup_shape _ hp

theorem validateInline_sim {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    (budget : Nat) → (p : CTPlan) →
    {G : Ctx (Arg (CTOptV V₁)) (Arg (CTOptV V₂))} →
    {D : Ctx (CTLabel V₁ L₁ rs) (CTLabel V₂ L₂ rs)} →
    {e₁ : Expr (Arg (CTOptV V₁)) (CTLabel V₁ L₁ rs) rs} →
    {e₂ : Expr (Arg (CTOptV V₂)) (CTLabel V₂ L₂ rs) rs} →
    Wf G D e₁ e₂ → (∀ p ∈ G, ArgShapeEq p.2.1 p.2.2) → CTDSim D →
    validateInline budget p e₁ = validateInline budget p e₂
  | 0, _, _, _, _, _, _, _, _ => by simp only [validateInline]
  | b + 1, p, G, D, _, _, hwf, hG, hD => by
    cases p with
    | node1 pk =>
      cases hwf with
      | let_ hop hk =>
        rcases hop with ⟨code, hargs⟩
        have hel := evalThreadLet?_shape code (trel_flattenArgs_shape hG hargs)
        dsimp only [validateInline]
        rcases hel with ⟨he₁, he₂⟩ | ⟨o₁, o₂, he₁, he₂, ho⟩
        · rw [he₁, he₂]
          exact congrArg (Option.map (· + 1)) (validateInline_sim b pk (hk _ _)
            (fun p hp => (List.mem_append.1 hp).elim
              (mem_zip_noneArgTup_shape p) (hG p)) hD)
        · rw [he₁, he₂]
          exact validateInline_sim (b + 1) pk (hk o₁ o₂)
            (fun p hp => (List.mem_append.1 hp).elim (ArgShapeEq.mem_zip ho p) (hG p)) hD
      | load _ _ hk =>
        dsimp only [validateInline]
        exact congrArg (Option.map (· + 1)) (validateInline_sim b pk (hk _ _)
          (fun p hp => by cases hp with | head => rfl | tail _ hp' => exact hG p hp') hD)
      | store _ _ hk =>
        dsimp only [validateInline]
        exact congrArg (Option.map (· + 1)) (validateInline_sim b pk hk hG hD)
      | call _ _ hk =>
        dsimp only [validateInline]
        exact congrArg (Option.map (· + 1)) (validateInline_sim b pk (hk _ _)
          (fun p hp => (List.mem_append.1 hp).elim (mem_zip_noneArgTup_shape p) (hG p)) hD)
      | _ => rfl
    | node2 pt pe =>
      cases hwf with
      | jnz hc ht he =>
        have hsh := ArgShapeEq.flattenArg hG hc
        dsimp only [validateInline]
        cases e₁ : flattenArg _ <;> cases e₂ : flattenArg _ <;> rw [e₁, e₂] at hsh
        · rw [validateInline_sim b pt ht hG hD]
          dsimp only [Bind.bind, Option.bind]
          cases validateInline b pt _ with
          | none => rfl
          | some st => dsimp only; rw [validateInline_sim (b - st) pe he hG hD]
        · cases hsh
        · cases hsh
        · rename_i b₁ b₂
          dsimp only [ArgShapeEq, Arg.imm?] at hsh; cases hsh
          first
          | cases b₁ with
            | false => exact validateInline_sim (b + 1) pe he hG hD
            | true => exact validateInline_sim (b + 1) pt ht hG hD
          | cases b₂ with
            | false => exact validateInline_sim (b + 1) pe he hG hD
            | true => exact validateInline_sim (b + 1) pt ht hG hD
      | _ => rfl
    | jump _ =>
      cases hwf with
      | jump hj hargs =>
        obtain ⟨hts, hsinl⟩ := hD _ hj
        have hfa := trel_flattenArgs_shape hG hargs
        dsimp only [validateInline]
        rw [hts.canEmit_eq hfa, hsinl _ _ hfa]
      | _ => rfl
    | leaf => cases hwf <;> rfl
    | group _ _ _ => cases hwf <;> rfl

theorem rewriteCTInline_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx (Arg (CTOptV V₁)) (Arg (CTOptV V₂))}
    {D : Ctx (CTLabel V₁ L₁ rs) (CTLabel V₂ L₂ rs)}
    {e₁ : Expr (Arg (CTOptV V₁)) (CTLabel V₁ L₁ rs) rs}
    {e₂ : Expr (Arg (CTOptV V₂)) (CTLabel V₂ L₂ rs) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ (p : CTPlan) {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂},
      (∀ p ∈ G, OptArgRel G' p.1 p.2.1 p.2.2) → CTDRel G' D' D →
      Wf G' D' (rewriteCTInline p e₁) (rewriteCTInline p e₂) := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
    intro p G' D' hG hD
    cases p with
    | node1 pk =>
      cases hop with
      | mk code hargs =>
        have hfa := trel_flattenArgs_opt hG hargs
        have hel := evalThreadLet?_opt_rel code hfa
        dsimp only [rewriteCTInline]
        rcases hel with ⟨he₁, he₂⟩ | ⟨o₁, o₂, he₁, he₂, ho⟩
        · rw [he₁, he₂]
          obtain ⟨r₁, r₂, hr₁, hr₂, hr⟩ := trel_toRealArgs?_rel hfa
          rw [hr₁, hr₂]
          exact .let_ (.mk code hr) fun xs₁ xs₂ =>
            ih (toOptArgTup xs₁) (toOptArgTup xs₂) pk
              (ctx_optArgRel_append (mem_zip_toOptArgTup xs₁ xs₂) hG)
              (hD.weaken (fun _ h => List.mem_append_right _ h) (fun _ h => h))
        · rw [he₁, he₂]
          exact ih o₁ o₂ pk (ctx_optArgRel_append_same (mem_zip_optArgRel ho) hG) hD
    | _ => exact .hlt
  | load t ha _ ih =>
    intro p G' D' hG hD
    cases p with
    | node1 pk =>
      obtain ⟨r₁, r₂, hr₁, hr₂, hr⟩ := (OptArgRel.flattenArg hG ha).toRealArg?
      dsimp only [rewriteCTInline]
      rw [hr₁, hr₂]
      exact .load t hr fun v₁ v₂ =>
        ih (.var (some v₁)) (.var (some v₂)) pk (ctx_optArgRel_cons_var hG v₁ v₂)
          (hD.weaken (fun _ h => List.mem_cons_of_mem _ h) (fun _ h => h))
    | _ => exact .hlt
  | store hv ha _ ih =>
    intro p G' D' hG hD
    cases p with
    | node1 pk =>
      obtain ⟨rv₁, rv₂, hrv₁, hrv₂, hrv⟩ := (OptArgRel.flattenArg hG hv).toRealArg?
      obtain ⟨ra₁, ra₂, hra₁, hra₂, hra⟩ := (OptArgRel.flattenArg hG ha).toRealArg?
      dsimp only [rewriteCTInline]
      rw [hrv₁, hrv₂, hra₁, hra₂]
      exact .store hrv hra (ih pk hG hD)
    | _ => exact .hlt
  | call f hargs _ ih =>
    intro p G' D' hG hD
    cases p with
    | node1 pk =>
      obtain ⟨r₁, r₂, hr₁, hr₂, hr⟩ := trel_toRealArgs?_rel (trel_flattenArgs_opt hG hargs)
      dsimp only [rewriteCTInline]
      rw [hr₁, hr₂]
      exact .call f hr fun xs₁ xs₂ =>
        ih (toOptArgTup xs₁) (toOptArgTup xs₂) pk
          (ctx_optArgRel_append (mem_zip_toOptArgTup xs₁ xs₂) hG)
          (hD.weaken (fun _ h => List.mem_append_right _ h) (fun _ h => h))
    | _ => exact .hlt
  | jnz hc _ _ iht ihe =>
    intro p G' D' hG hD
    cases p with
    | node2 pt pe =>
      have hfl := OptArgRel.flattenArg hG hc
      dsimp only [rewriteCTInline]
      cases e₁ : flattenArg _ <;> cases e₂ : flattenArg _ <;> rw [e₁, e₂] at hfl
      · cases hfl; exact .jnz (.var ‹_›) (iht pt hG hD) (ihe pe hG hD)
      · cases hfl
      · cases hfl
      · cases hfl; next c => cases c with | false => exact ihe pe hG hD | true => exact iht pt hG hD
    | _ => exact .hlt
  | jump hj hargs =>
    intro p G' D' hG hD
    cases p with
    | jump _ =>
      have hhl := hD _ hj
      have hfa := trel_flattenArgs_opt hG hargs
      have hsh : TRel (fun _ => ArgShapeEq) (flattenArgs _) (flattenArgs _) :=
        TRel.mono (fun _ _ _ h => h.shape) hfa
      dsimp only [rewriteCTInline]
      rw [hhl.1.shape.canEmit_eq hsh]
      split
      · exact hhl.1.emit_wf hfa
      · have hor := hhl.2.1 (fun _ h => h) (fun _ h => h) _ _ hfa
        cases e₁ : CTLabel.inline? _ (flattenArgs _) <;>
          cases e₂ : CTLabel.inline? _ (flattenArgs _) <;>
          rw [e₁, e₂] at hor <;> dsimp only [ORel] at hor
        · exact .hlt
        · exact hor
    | _ => exact .hlt
  | ret hvs =>
    intro p G' _ hG _
    cases p with
    | leaf =>
      obtain ⟨r₁, r₂, hr₁, hr₂, hr⟩ := trel_toRealArgs?_rel (trel_flattenArgs_opt hG hvs)
      dsimp only [rewriteCTInline]; rw [hr₁, hr₂]; exact .ret hr
    | _ => exact .hlt
  | exit f hargs =>
    intro p G' _ hG _
    cases p with
    | leaf =>
      obtain ⟨r₁, r₂, hr₁, hr₂, hr⟩ := trel_toRealArgs?_rel (trel_flattenArgs_opt hG hargs)
      dsimp only [rewriteCTInline]; rw [hr₁, hr₂]; exact .exit f hr
    | _ => exact .hlt
  | hlt => intro p _ _ _ _; cases p <;> exact .hlt
  | group _ _ _ _ => intro p _ _ _ _; cases p <;> exact .hlt

/-! ### `splitLabelTup`, `buildTargets`, `attachInlines`, `rewriteCTBlocks`, and `rewriteCTAux_wf` -/

theorem splitLabelTup_rel {L₁ L₂ : List Ty → Type} {D' : Ctx L₁ L₂} :
    (as bs : List (List Ty)) → (js₁ : Tup L₁ (as ++ bs)) → (js₂ : Tup L₂ (as ++ bs)) →
    (∀ p ∈ Tup.zip js₁ js₂, p ∈ D') →
    (∀ p ∈ Tup.zip (splitLabelTup as bs js₁).1 (splitLabelTup as bs js₂).1, p ∈ D') ∧
      (∀ p ∈ Tup.zip (splitLabelTup as bs js₁).2 (splitLabelTup as bs js₂).2, p ∈ D')
  | [], _, js₁, js₂, h => ⟨fun _ hp => (nomatch hp), h⟩
  | _ :: as, bs, (j₁, js₁), (j₂, js₂), h => by
    have ih := splitLabelTup_rel as bs js₁ js₂ fun _ hp => h _ (List.mem_cons_of_mem _ hp)
    dsimp only [splitLabelTup]
    refine ⟨fun p hp => ?_, ih.2⟩
    cases hp with
    | head => exact h _ List.mem_cons_self
    | tail _ hp' => exact ih.1 _ hp'

theorem splitOptLabel_rel {L₁ L₂ : List Ty → Type} {D' : Ctx L₁ L₂} {ts : List Ty} :
    (b : Bool) → {rest : List (List Ty)} →
    (js₁ : Tup L₁ ((if b then [ts] else []) ++ rest)) →
    (js₂ : Tup L₂ ((if b then [ts] else []) ++ rest)) →
    (∀ p ∈ Tup.zip js₁ js₂, p ∈ D') →
    ORel (fun l₁ l₂ => ⟨ts, l₁, l₂⟩ ∈ D')
      (splitOptLabel b js₁).1 (splitOptLabel b js₂).1 ∧
    (∀ p ∈ Tup.zip (splitOptLabel b js₁).2 (splitOptLabel b js₂).2, p ∈ D')
  | false, _, _, _, h => ⟨trivial, h⟩
  | true, _, (_, _), (_, _), h =>
    ⟨h _ List.mem_cons_self, fun _ hp => h _ (List.mem_cons_of_mem _ hp)⟩

theorem mkActTarget_rel {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {D' : Ctx L₁ L₂}
    (ts : List Ty) (act : BlockAct)
    (js₁ : Tup L₁ (actSig ts act)) (js₂ : Tup L₂ (actSig ts act))
    (h : ∀ p ∈ Tup.zip js₁ js₂, p ∈ D') :
    CTTargetRel (V₁ := V₁) (V₂ := V₂) D' (mkActTarget ts act js₁) (mkActTarget ts act js₂) := by
  cases act with
  | keep kb _ =>
    cases kb with
    | true => exact h _ List.mem_cons_self
    | false => exact trivial
  | splitBool p keepT keepF keepDisp _ _ =>
    dsimp only [actSig] at js₁ js₂ h
    dsimp only [mkActTarget]
    revert js₁ js₂ h
    generalize splitMember? p ts = sp
    cases sp with
    | none => intro js₁ js₂ h; exact h _ List.mem_cons_self
    | some _ =>
      intro js₁ js₂ h
      have hD := splitOptLabel_rel keepDisp _ _ h
      have hT := splitOptLabel_rel keepT _ _ hD.2
      have hF := splitOptLabel_rel keepF _ _ hT.2
      exact ⟨rfl, hT.1, hF.1, hD.1⟩

theorem buildTargets_rel {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} :
    (acts : List BlockAct) → (sig : List (List Ty)) →
    (js₁ : Tup L₁ (threadSig acts sig)) → (js₂ : Tup L₂ (threadSig acts sig)) →
    (∀ p ∈ Tup.zip js₁ js₂, p ∈ D') →
    CTDRel G' D' (Tup.zip (buildTargets (V := V₁) (rs := rs) acts sig js₁)
      (buildTargets (V := V₂) (rs := rs) acts sig js₂))
  | _, [], (), (), _, _, hp => nomatch hp
  | [], ts :: sig, (j₁, js₁), (j₂, js₂), h, _, hp => by
    dsimp only [buildTargets, Tup.zip] at hp
    cases hp with
    | head => exact ⟨h _ List.mem_cons_self, fun _ _ _ _ _ => trivial, fun _ _ _ => rfl⟩
    | tail _ hp' =>
      exact buildTargets_rel [] sig js₁ js₂ (fun _ hq => h _ (List.mem_cons_of_mem _ hq)) _ hp'
  | a :: acts, ts :: sig, js₁, js₂, h, p, hp => by
    dsimp only [buildTargets, Tup.zip] at hp
    have hsp := splitLabelTup_rel (actSig ts a) (threadSig acts sig) js₁ js₂ h
    cases hp with
    | head => exact ⟨mkActTarget_rel ts a _ _ hsp.1, fun _ _ _ _ _ => trivial, fun _ _ _ => rfl⟩
    | tail _ hp' => exact buildTargets_rel acts sig _ _ hsp.2 p hp'

theorem tryMakeInlineLabel_rel {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs ts : List Ty}
    {G : Ctx (Arg (CTOptV V₁)) (Arg (CTOptV V₂))}
    {D : Ctx (CTLabel V₁ L₁ rs) (CTLabel V₂ L₂ rs)}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂}
    (hG : ∀ p ∈ G, OptArgRel G' p.1 p.2.1 p.2.2) (hD : CTDRel G' D' D)
    {b₁ : Tup (Arg (CTOptV V₁)) ts → Expr (Arg (CTOptV V₁)) (CTLabel V₁ L₁ rs) rs}
    {b₂ : Tup (Arg (CTOptV V₂)) ts → Expr (Arg (CTOptV V₂)) (CTLabel V₂ L₂ rs) rs}
    (hb : ∀ a₁ a₂, Wf (Tup.zip a₁ a₂ ++ G) D (b₁ a₁) (b₂ a₂))
    (a : BlockAct) (pb : CTPlan) {l₁ : CTLabel V₁ L₁ rs ts} {l₂ : CTLabel V₂ L₂ rs ts}
    (hl : CTLabelRel G' D' l₁ l₂) :
    CTLabelRel G' D' (tryMakeInlineLabel a pb b₁ l₁) (tryMakeInlineLabel a pb b₂ l₂) := by
  have hGsh : ∀ p ∈ G, ArgShapeEq p.2.1 p.2.2 := fun p hp => (hG p hp).shape
  have hsim : ∀ a₁ a₂, TRel (fun _ => ArgShapeEq) a₁ a₂ →
      ∀ (budget : Nat),
      (let (res₁, p₁', e₁') := peelThreadHead 4 false pb (b₁ a₁)
       let (res₂, p₂', e₂') := peelThreadHead 4 false pb (b₂ a₂)
       res₁ = res₂ ∧ p₁' = p₂' ∧
         (validateInline budget p₁' e₁').isSome = (validateInline budget p₂' e₂').isSome ∧
         (res₁ → (validateInline 8 p₁' e₁').isSome = (validateInline 8 p₂' e₂').isSome)) := by
    intro a₁ a₂ ha budget
    obtain ⟨hres, hp', G₁, hG₁, hwf₁⟩ := peelThreadHead_sim 4 false pb (hb a₁ a₂) fun p hp =>
      (List.mem_append.1 hp).elim (ArgShapeEq.mem_zip ha p) (hGsh p)
    refine ⟨hres, hp', ?_, fun _ => ?_⟩
    · rw [hp', validateInline_sim budget _ hwf₁ hG₁ hD.toSim]
    · rw [hp', validateInline_sim 8 _ hwf₁ hG₁ hD.toSim]
  cases a with
  | keep _ allow =>
    cases allow
    · exact hl
    · refine ⟨hl.1, ?_, ?_⟩
      · intro G'' D'' hG'' hD'' a₁ a₂ ha
        have hG' : ∀ p ∈ G, OptArgRel G'' p.1 p.2.1 p.2.2 := fun p hp => (hG p hp).weaken hG''
        obtain ⟨hres, hp', G₁, hG₁, hwf₁⟩ := peelThreadHead_wf 4 false pb (hb a₁ a₂)
          (ctx_optArgRel_append_same (mem_zip_optArgRel ha) hG')
        obtain ⟨_, _, hval, _⟩ := hsim a₁ a₂ (TRel.mono (fun _ _ _ h => h.shape) ha)
          (if (peelThreadHead 4 false pb (b₂ a₂)).1 then 8 else 3)
        dsimp only [tryMakeInlineLabel]
        simp only [hp'] at hval
        simp only [hres, hp']
        rw [hval]
        by_cases hc : (validateInline (if (peelThreadHead 4 false pb (b₂ a₂)).1 then 8 else 3)
            (peelThreadHead 4 false pb (b₂ a₂)).2.1
            (peelThreadHead 4 false pb (b₂ a₂)).2.2).isSome = true
        · simp only [hc, ↓reduceIte, ORel]
          rw [← hp']
          exact rewriteCTInline_wf hwf₁ _ hG₁ (hD.weaken hG'' hD'')
        · simp only [hc, Bool.false_eq_true, ↓reduceIte, ORel]
      · intro a₁ a₂ ha
        obtain ⟨hres, hp', hval, _⟩ := hsim a₁ a₂ ha
          (if (peelThreadHead 4 false pb (b₂ a₂)).1 then 8 else 3)
        dsimp only [tryMakeInlineLabel]
        simp only [hp'] at hval
        simp only [hres, hp']
        rw [hval]
        by_cases hc : (validateInline (if (peelThreadHead 4 false pb (b₂ a₂)).1 then 8 else 3)
            (peelThreadHead 4 false pb (b₂ a₂)).2.1
            (peelThreadHead 4 false pb (b₂ a₂)).2.2).isSome = true <;>
          simp only [hc, ↓reduceIte, Bool.false_eq_true, Option.isSome_some, Option.isSome_none]
  | splitBool _ _ _ _ inlT inlF =>
    dsimp only [tryMakeInlineLabel]
    by_cases hinl : (inlT || inlF) = true
    · simp only [hinl, ↓reduceIte]
      refine ⟨hl.1, ?_, ?_⟩
      · intro G'' D'' hG'' hD'' a₁ a₂ ha
        have hG' : ∀ p ∈ G, OptArgRel G'' p.1 p.2.1 p.2.2 := fun p hp => (hG p hp).weaken hG''
        obtain ⟨hres, hp', G₁, hG₁, hwf₁⟩ := peelThreadHead_wf 4 false pb (hb a₁ a₂)
          (ctx_optArgRel_append_same (mem_zip_optArgRel ha) hG')
        obtain ⟨_, _, _, hval8⟩ := hsim a₁ a₂ (TRel.mono (fun _ _ _ h => h.shape) ha) 8
        by_cases hres₂ : (peelThreadHead 4 false pb (b₂ a₂)).1 = true
        · have hvi := hval8 (hres.trans hres₂)
          simp only [hp'] at hvi
          simp only [hres, hres₂, hp', Bool.true_and]
          rw [hvi]
          by_cases hc : (validateInline 8 (peelThreadHead 4 false pb (b₂ a₂)).2.1
              (peelThreadHead 4 false pb (b₂ a₂)).2.2).isSome = true
          · simp only [hc, ↓reduceIte, ORel]
            rw [← hp']
            exact rewriteCTInline_wf hwf₁ _ hG₁ (hD.weaken hG'' hD'')
          · simp only [hc, Bool.false_eq_true, ↓reduceIte, ORel]
        · have hfalse : (peelThreadHead 4 false pb (b₂ a₂)).1 = false :=
            Bool.eq_false_iff.2 hres₂
          simp only [hres, hfalse, Bool.false_and, Bool.false_eq_true, ↓reduceIte, ORel]
      · intro a₁ a₂ ha
        obtain ⟨hres, hp', _, hval8⟩ := hsim a₁ a₂ ha 8
        by_cases hres₂ : (peelThreadHead 4 false pb (b₂ a₂)).1 = true
        · have hvi := hval8 (hres.trans hres₂)
          simp only [hp'] at hvi
          simp only [hres, hres₂, hp', Bool.true_and]
          rw [hvi]
          by_cases hc : (validateInline 8 (peelThreadHead 4 false pb (b₂ a₂)).2.1
              (peelThreadHead 4 false pb (b₂ a₂)).2.2).isSome = true <;>
            simp only [hc, ↓reduceIte, Bool.false_eq_true, Option.isSome_some, Option.isSome_none]
        · have hfalse : (peelThreadHead 4 false pb (b₂ a₂)).1 = false :=
            Bool.eq_false_iff.2 hres₂
          simp only [hres, hfalse, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
            Option.isSome_none]
    · simp only [hinl, Bool.false_eq_true, ↓reduceIte]
      exact hl

theorem attachInlines_rel {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx (Arg (CTOptV V₁)) (Arg (CTOptV V₂))}
    {D : Ctx (CTLabel V₁ L₁ rs) (CTLabel V₂ L₂ rs)}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂}
    (hG : ∀ p ∈ G, OptArgRel G' p.1 p.2.1 p.2.2) (hD : CTDRel G' D' D) :
    (acts : List BlockAct) → (pbs : CTPlanB) → {sig : List (List Ty)} →
    (bs₁ : Blocks (Arg (CTOptV V₁)) (CTLabel V₁ L₁ rs) rs sig) →
    (bs₂ : Blocks (Arg (CTOptV V₂)) (CTLabel V₂ L₂ rs) rs sig) →
    WfB G D bs₁ bs₂ →
    (ls₁ : Tup (CTLabel V₁ L₁ rs) sig) → (ls₂ : Tup (CTLabel V₂ L₂ rs) sig) →
    CTDRel G' D' (Tup.zip ls₁ ls₂) →
    CTDRel G' D' (Tup.zip (attachInlines acts pbs bs₁ ls₁) (attachInlines acts pbs bs₂ ls₂))
  | _, _, [], .nil, .nil, _, (), (), _, _, hp => nomatch hp
  | a :: acts, .cons pb pbs, _ :: _, .cons _ bs₁, .cons _ bs₂, .cons hb hbs,
      (l₁, ls₁), (l₂, ls₂), hls, p, hp => by
    dsimp only [attachInlines, Tup.zip] at hp
    cases hp with
    | head =>
      exact tryMakeInlineLabel_rel hG hD hb a pb (hls _ List.mem_cons_self)
    | tail _ hp' =>
      exact attachInlines_rel hG hD acts pbs bs₁ bs₂ hbs ls₁ ls₂
        (fun _ hq => hls _ (List.mem_cons_of_mem _ hq)) p hp'
  | [], _, _ :: _, .cons _ bs₁, .cons _ bs₂, .cons _ hbs,
      (l₁, ls₁), (l₂, ls₂), hls, p, hp => by
    dsimp only [attachInlines, Tup.zip] at hp
    cases hp with
    | head => exact hls _ List.mem_cons_self
    | tail _ hp' =>
      exact attachInlines_rel hG hD [] .nil bs₁ bs₂ hbs ls₁ ls₂
        (fun _ hq => hls _ (List.mem_cons_of_mem _ hq)) p hp'
  | _ :: _, .nil, _ :: _, .cons _ bs₁, .cons _ bs₂, .cons _ hbs,
      (l₁, ls₁), (l₂, ls₂), hls, p, hp => by
    dsimp only [attachInlines, Tup.zip] at hp
    cases hp with
    | head => exact hls _ List.mem_cons_self
    | tail _ hp' =>
      exact attachInlines_rel hG hD [] .nil bs₁ bs₂ hbs ls₁ ls₂
        (fun _ hq => hls _ (List.mem_cons_of_mem _ hq)) p hp'

theorem tryMakeInlineLabel_sim {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs ts : List Ty}
    {G : Ctx (Arg (CTOptV V₁)) (Arg (CTOptV V₂))}
    {D : Ctx (CTLabel V₁ L₁ rs) (CTLabel V₂ L₂ rs)}
    (hG : ∀ p ∈ G, ArgShapeEq p.2.1 p.2.2) (hD : CTDSim D)
    {b₁ : Tup (Arg (CTOptV V₁)) ts → Expr (Arg (CTOptV V₁)) (CTLabel V₁ L₁ rs) rs}
    {b₂ : Tup (Arg (CTOptV V₂)) ts → Expr (Arg (CTOptV V₂)) (CTLabel V₂ L₂ rs) rs}
    (hb : ∀ a₁ a₂, Wf (Tup.zip a₁ a₂ ++ G) D (b₁ a₁) (b₂ a₂))
    (a : BlockAct) (pb : CTPlan) {l₁ : CTLabel V₁ L₁ rs ts} {l₂ : CTLabel V₂ L₂ rs ts}
    (hl : CTLabelSim l₁ l₂) :
    CTLabelSim (tryMakeInlineLabel a pb b₁ l₁) (tryMakeInlineLabel a pb b₂ l₂) := by
  have hcheck : ∀ a₁ a₂, TRel (fun _ => ArgShapeEq) a₁ a₂ → ∀ (budget : Nat),
      (let (res₁, p₁', e₁') := peelThreadHead 4 false pb (b₁ a₁)
       let (res₂, p₂', e₂') := peelThreadHead 4 false pb (b₂ a₂)
       res₁ = res₂ ∧ p₁' = p₂' ∧
         (validateInline budget p₁' e₁').isSome = (validateInline budget p₂' e₂').isSome ∧
         (validateInline 8 p₁' e₁').isSome = (validateInline 8 p₂' e₂').isSome) := by
    intro a₁ a₂ ha budget
    have hsh : ∀ p ∈ Tup.zip a₁ a₂ ++ G, ArgShapeEq p.2.1 p.2.2 := fun p hp =>
      (List.mem_append.1 hp).elim (ArgShapeEq.mem_zip ha p) (hG p)
    obtain ⟨hres, hp', G₁, hG₁, hwf₁⟩ := peelThreadHead_sim 4 false pb (hb a₁ a₂) hsh
    refine ⟨hres, hp', ?_, ?_⟩
    · rw [hp', validateInline_sim budget _ hwf₁ hG₁ hD]
    · rw [hp', validateInline_sim 8 _ hwf₁ hG₁ hD]
  cases a with
  | keep _ allow =>
    cases allow
    · exact hl
    · refine ⟨hl.1, fun a₁ a₂ ha => ?_⟩
      obtain ⟨hres, hp', hval, _⟩ :=
          hcheck a₁ a₂ ha (if (peelThreadHead 4 false pb (b₂ a₂)).1 then 8 else 3)
      dsimp only [tryMakeInlineLabel]
      simp only [hp'] at hval
      simp only [hres, hp']
      rw [hval]
      by_cases hc : (validateInline (if (peelThreadHead 4 false pb (b₂ a₂)).1 then 8 else 3)
          (peelThreadHead 4 false pb (b₂ a₂)).2.1
          (peelThreadHead 4 false pb (b₂ a₂)).2.2).isSome = true <;>
        simp only [hc, ↓reduceIte, Bool.false_eq_true, Option.isSome_some, Option.isSome_none]
  | splitBool _ _ _ _ inlT inlF =>
    dsimp only [tryMakeInlineLabel]
    by_cases hinl : (inlT || inlF) = true
    · simp only [hinl, ↓reduceIte]
      refine ⟨hl.1, fun a₁ a₂ ha => ?_⟩
      obtain ⟨hres, hp', _, hval8⟩ := hcheck a₁ a₂ ha 8
      simp only [hp'] at hval8
      by_cases hres₂ : (peelThreadHead 4 false pb (b₂ a₂)).1 = true
      · simp only [hres, hres₂, hp', Bool.true_and]
        rw [hval8]
        by_cases hc : (validateInline 8 (peelThreadHead 4 false pb (b₂ a₂)).2.1
            (peelThreadHead 4 false pb (b₂ a₂)).2.2).isSome = true <;>
          simp only [hc, ↓reduceIte, Bool.false_eq_true, Option.isSome_some, Option.isSome_none]
      · have hfalse : (peelThreadHead 4 false pb (b₂ a₂)).1 = false :=
          Bool.eq_false_iff.2 hres₂
        simp only [hres, hfalse, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Option.isSome_none]
    · simp only [hinl, Bool.false_eq_true, ↓reduceIte]
      exact hl

theorem attachInlines_sim {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx (Arg (CTOptV V₁)) (Arg (CTOptV V₂))}
    {D : Ctx (CTLabel V₁ L₁ rs) (CTLabel V₂ L₂ rs)}
    (hG : ∀ p ∈ G, ArgShapeEq p.2.1 p.2.2) (hD : CTDSim D) :
    (acts : List BlockAct) → (pbs : CTPlanB) → {sig : List (List Ty)} →
    (bs₁ : Blocks (Arg (CTOptV V₁)) (CTLabel V₁ L₁ rs) rs sig) →
    (bs₂ : Blocks (Arg (CTOptV V₂)) (CTLabel V₂ L₂ rs) rs sig) →
    WfB G D bs₁ bs₂ →
    (ls₁ : Tup (CTLabel V₁ L₁ rs) sig) → (ls₂ : Tup (CTLabel V₂ L₂ rs) sig) →
    CTDSim (Tup.zip ls₁ ls₂) →
    CTDSim (Tup.zip (attachInlines acts pbs bs₁ ls₁) (attachInlines acts pbs bs₂ ls₂))
  | _, _, [], .nil, .nil, _, (), (), _, _, hp => nomatch hp
  | a :: acts, .cons pb pbs, _ :: _, .cons _ bs₁, .cons _ bs₂, .cons hb hbs,
      (l₁, ls₁), (l₂, ls₂), hls, p, hp => by
    dsimp only [attachInlines, Tup.zip] at hp
    cases hp with
    | head => exact tryMakeInlineLabel_sim hG hD hb a pb (hls _ List.mem_cons_self)
    | tail _ hp' =>
      exact attachInlines_sim hG hD acts pbs bs₁ bs₂ hbs ls₁ ls₂
        (fun _ hq => hls _ (List.mem_cons_of_mem _ hq)) p hp'
  | [], _, _ :: _, .cons _ bs₁, .cons _ bs₂, .cons _ hbs,
      (l₁, ls₁), (l₂, ls₂), hls, p, hp => by
    dsimp only [attachInlines, Tup.zip] at hp
    cases hp with
    | head => exact hls _ List.mem_cons_self
    | tail _ hp' =>
      exact attachInlines_sim hG hD [] .nil bs₁ bs₂ hbs ls₁ ls₂
        (fun _ hq => hls _ (List.mem_cons_of_mem _ hq)) p hp'
  | _ :: _, .nil, _ :: _, .cons _ bs₁, .cons _ bs₂, .cons _ hbs,
      (l₁, ls₁), (l₂, ls₂), hls, p, hp => by
    dsimp only [attachInlines, Tup.zip] at hp
    cases hp with
    | head => exact hls _ List.mem_cons_self
    | tail _ hp' =>
      exact attachInlines_sim hG hD [] .nil bs₁ bs₂ hbs ls₁ ls₂
        (fun _ hq => hls _ (List.mem_cons_of_mem _ hq)) p hp'

theorem validTargets_buildTargets_sim {V₂ : Ty → Type} {L₂ : List Ty → Type} {rs : List Ty} :
    (acts : List BlockAct) → (sig : List (List Ty)) → (Js₂ : Tup L₂ (threadSig acts sig)) →
    CTDSim (Tup.zip (validTargets (rs := rs) acts sig) (buildTargets (V := V₂) (rs :=
        rs) acts sig Js₂))
  | _, [], (), _, hp => nomatch hp
  | [], _ :: sig, (_, js₂), p, hp => by
    dsimp only [validTargets, buildTargets, Tup.zip] at hp
    cases hp with
    | head => exact ⟨trivial, fun _ _ _ => rfl⟩
    | tail _ hp' => exact validTargets_buildTargets_sim [] sig js₂ p hp'
  | a :: acts, ts :: sig, js₂, p, hp => by
    dsimp only [validTargets, buildTargets, Tup.zip] at hp
    cases hp with
    | head =>
      refine ⟨?_, fun _ _ _ => rfl⟩
      cases a with
      | keep kb _ => cases kb <;> trivial
      | splitBool p keepT keepF keepDisp _ _ =>
        dsimp only [threadSig, actSig] at js₂ ⊢
        dsimp only [mkActTarget]
        revert js₂
        generalize splitMember? p ts = sp
        cases sp with
        | none => intro _; trivial
        | some _ =>
          intro _
          dsimp only [CTTargetShape]
          refine ⟨HEq.rfl, ?_, ?_, ?_⟩
          · cases keepT <;> cases keepDisp <;> rfl
          · cases keepT <;> cases keepF <;> cases keepDisp <;> rfl
          · cases keepDisp <;> rfl
    | tail _ hp' =>
      exact validTargets_buildTargets_sim acts sig _ p hp'

theorem buildTargets_self_sim {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (acts : List BlockAct) → (sig : List (List Ty)) → (Js : Tup L (threadSig acts sig)) →
    CTDSim (Tup.zip (buildTargets (V := V) (rs := rs) acts sig Js)
      (buildTargets (V := V) (rs := rs) acts sig Js))
  | _, [], (), _, hp => nomatch hp
  | [], _ :: sig, (_, js), p, hp => by
    dsimp only [buildTargets, Tup.zip] at hp
    cases hp with
    | head => exact ⟨trivial, fun _ _ _ => rfl⟩
    | tail _ hp' => exact buildTargets_self_sim [] sig js p hp'
  | a :: acts, ts :: sig, js, p, hp => by
    dsimp only [buildTargets, Tup.zip] at hp
    cases hp with
    | head =>
      refine ⟨?_, fun _ _ _ => rfl⟩
      cases a with
      | keep kb _ => cases kb <;> trivial
      | splitBool p keepT keepF keepDisp _ _ =>
        dsimp only [threadSig, actSig] at js ⊢
        dsimp only [mkActTarget]
        revert js
        generalize splitMember? p ts = sp
        cases sp with
        | none => intro _; trivial
        | some _ => intro _; exact ⟨HEq.rfl, rfl, rfl, rfl⟩
    | tail _ hp' => exact buildTargets_self_sim acts sig _ p hp'

theorem blocksAppend_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} :
    {s₁ s₂ : List (List Ty)} →
    {bs₁ : Blocks V₁ L₁ rs s₁} → {bs₁' : Blocks V₂ L₂ rs s₁} →
    {bs₂ : Blocks V₁ L₁ rs s₂} → {bs₂' : Blocks V₂ L₂ rs s₂} →
    WfB G D bs₁ bs₁' → WfB G D bs₂ bs₂' →
    WfB G D (blocksAppend bs₁ bs₂) (blocksAppend bs₁' bs₂')
  | [], _, .nil, .nil, _, _, .nil, hbs₂ => hbs₂
  | _ :: _, _, .cons _ _, .cons _ _, _, _, .cons hb₁ ht₁, hbs₂ =>
    .cons hb₁ (blocksAppend_wf ht₁ hbs₂)

theorem condConsBlock_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs ts : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (b : Bool)
    {blk₁ : Unit → Tup V₁ ts → Expr V₁ L₁ rs} {blk₂ : Unit → Tup V₂ ts → Expr V₂ L₂ rs}
    {rest : List (List Ty)} {tl₁ : Blocks V₁ L₁ rs rest} {tl₂ : Blocks V₂ L₂ rs rest}
    (hblk : b = true → ∀ xs₁ xs₂, Wf (Tup.zip xs₁ xs₂ ++ G) D (blk₁ () xs₁) (blk₂ () xs₂))
    (htl : WfB G D tl₁ tl₂) :
    WfB G D (condConsBlock b blk₁ tl₁) (condConsBlock b blk₂ tl₂) := by
  cases b
  · exact htl
  · exact .cons (hblk rfl) htl

theorem mkHltBlocks_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} :
    (sig : List (List Ty)) → WfB G D (mkHltBlocks (V := V₁) (rs := rs) sig)
      (mkHltBlocks (V := V₂) (rs := rs) sig)
  | [] => .nil
  | _ :: sig => .cons (fun _ _ => .hlt) (mkHltBlocks_wf sig)

private theorem eq_cast_wfb {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {s₁ s₂ : List (List Ty)} (h : s₁ = s₂)
    {b₁ : Blocks V₁ L₁ rs s₁} {b₂ : Blocks V₂ L₂ rs s₁} (hb : WfB G D b₁ b₂) :
    WfB G D (h ▸ b₁) (h ▸ b₂) := by
  subst h; exact hb

theorem mkSplitBlocks_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs ts : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} (m : Member .bool ts)
    (keepDisp keepT keepF : Bool)
    {l₁ : CTLabel V₁ L₁ rs ts} {l₂ : CTLabel V₂ L₂ rs ts}
    (hl : CTTargetRel D l₁.target l₂.target)
    {rwT₁ rwF₁ : Tup V₁ (eraseMem m) → Expr V₁ L₁ rs}
    {rwT₂ rwF₂ : Tup V₂ (eraseMem m) → Expr V₂ L₂ rs}
    (hT : ∀ xs₁ xs₂, Wf (Tup.zip xs₁ xs₂ ++ G) D (rwT₁ xs₁) (rwT₂ xs₂))
    (hF : ∀ xs₁ xs₂, Wf (Tup.zip xs₁ xs₂ ++ G) D (rwF₁ xs₁) (rwF₂ xs₂)) :
    WfB G D (mkSplitBlocks m keepDisp keepT keepF l₁ rwT₁ rwF₁)
      (mkSplitBlocks m keepDisp keepT keepF l₂ rwT₂ rwF₂) := by
  refine condConsBlock_wf keepDisp (fun _ xs₁ xs₂ => ?_)
    (condConsBlock_wf keepT (fun _ => hT) (condConsBlock_wf keepF (fun _ => hF) .nil))
  revert hl
  cases l₁.target <;> cases l₂.target <;> intro hl
  · exact .hlt
  · exact .hlt
  · dsimp only [CTTargetRel] at hl
  · exact .hlt
  · exact .hlt
  · dsimp only [CTTargetRel] at hl
  · dsimp only [CTTargetRel] at hl
  · dsimp only [CTTargetRel] at hl
  · rename_i m₁ lT1? lF1? _ m₂ lT2? lF2? _
    dsimp only [CTTargetRel] at hl
    rcases hl with ⟨rfl, hlt, hlf, _⟩
    cases lT1? <;> cases lT2? <;> dsimp only [ORel] at hlt <;> try exact .hlt
    cases lF1? <;> cases lF2? <;> dsimp only [ORel] at hlf <;> try exact .hlt
    have hvar : ArgRel (Tup.zip xs₁ xs₂ ++ G) .bool
        (.var (getTupMem m₁ xs₁)) (.var (getTupMem m₁ xs₂)) := by
      have hm := trel_getTupMem m₁ (toArgTup_trel xs₁ xs₂)
      rw [getTupMem_toArgTup, getTupMem_toArgTup] at hm
      exact hm.weaken (fun _ hp => List.mem_append_left _ hp)
    have hdrop : TRel (ArgRel (Tup.zip xs₁ xs₂ ++ G))
        (dropTupMem m₁ (toArgTup xs₁)) (dropTupMem m₁ (toArgTup xs₂)) :=
      TRel.argRel_weaken (fun _ hp => List.mem_append_left _ hp)
        (trel_dropTupMem m₁ (toArgTup_trel xs₁ xs₂))
    exact .jnz hvar (.jump hlt hdrop) (.jump hlf hdrop)

theorem rewriteCTBlocks_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} :
    (acts : List BlockAct) → (pbs : CTPlanB) → {sig : List (List Ty)} →
    (bs₁ : Blocks (Arg (CTOptV V₁)) (CTLabel V₁ L₁ rs) rs sig) →
    (bs₂ : Blocks (Arg (CTOptV V₂)) (CTLabel V₂ L₂ rs) rs sig) →
    (ls₁ : Tup (CTLabel V₁ L₁ rs) sig) → (ls₂ : Tup (CTLabel V₂ L₂ rs) sig) →
    CTDRel G' D' (Tup.zip ls₁ ls₂) →
    (∀ {ts} (i : Member ts sig) pb (a₁ : Tup (Arg (CTOptV V₁)) ts) (a₂ : Tup (Arg (CTOptV V₂)) ts)
        {H'}, (∀ p ∈ Tup.zip a₁ a₂, OptArgRel H' p.1 p.2.1 p.2.2) →
        Wf (H' ++ G') D' (rewriteCTAux pb (bs₁.get i a₁)) (rewriteCTAux pb (bs₂.get i a₂))) →
    WfB G' D' (rewriteCTBlocks acts pbs bs₁ ls₁) (rewriteCTBlocks acts pbs bs₂ ls₂)
  | acts, _, [], .nil, .nil, (), (), _, _ => by simp only [rewriteCTBlocks]; exact mkHltBlocks_wf _
  | [], _, _ :: _, .cons _ _, .cons _ _, _, _, _, _ => by
    simp only [rewriteCTBlocks]; exact mkHltBlocks_wf _
  | _ :: _, .nil, _ :: _, .cons _ _, .cons _ _, _, _, _, _ => by
    simp only [rewriteCTBlocks]; exact mkHltBlocks_wf _
  | a :: acts, .cons pb pbs, ts :: _, .cons _ tl₁, .cons _ tl₂, (l₁, tls₁), (l₂, tls₂), hls, h => by
    have htl := rewriteCTBlocks_wf acts pbs tl₁ tl₂ tls₁ tls₂
      (fun _ hp => hls _ (List.mem_cons_of_mem _ hp)) (fun i => h (.there i))
    unfold rewriteCTBlocks
    refine blocksAppend_wf ?_ htl
    cases a with
    | keep kb _ =>
      cases kb with
      | true =>
        exact .cons (fun xs₁ xs₂ => h .here pb _ _ (mem_zip_toOptArgTup xs₁ xs₂)) .nil
      | false => exact .nil
    | splitBool p keepT keepF keepDisp _ _ =>
      dsimp only [actSig]
      generalize splitMember? p ts = sp
      cases sp with
      | none =>
        exact .cons (fun xs₁ xs₂ => h .here pb _ _ (mem_zip_toOptArgTup xs₁ xs₂)) .nil
      | some m =>
        exact mkSplitBlocks_wf m keepDisp keepT keepF (hls _ List.mem_cons_self).1
          (fun xs₁ xs₂ => h .here pb _ _ (mem_zip_optArgRel
            (trel_insertTupMem m (OptArgRel.imm (t := .bool) true) (toOptArgTup_trel xs₁ xs₂))))
          (fun xs₁ xs₂ => h .here pb _ _ (mem_zip_optArgRel
            (trel_insertTupMem m (OptArgRel.imm (t := .bool) false) (toOptArgTup_trel xs₁ xs₂))))

theorem rewriteCTAux_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx (Arg (CTOptV V₁)) (Arg (CTOptV V₂))}
    {D : Ctx (CTLabel V₁ L₁ rs) (CTLabel V₂ L₂ rs)}
    {e₁ : Expr (Arg (CTOptV V₁)) (CTLabel V₁ L₁ rs) rs}
    {e₂ : Expr (Arg (CTOptV V₂)) (CTLabel V₂ L₂ rs) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ (p : CTPlan) {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂},
      (∀ p ∈ G, OptArgRel G' p.1 p.2.1 p.2.2) → CTDRel G' D' D →
      Wf G' D' (rewriteCTAux p e₁) (rewriteCTAux p e₂) := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
    intro p G' D' hG hD
    cases p with
    | node1 pk =>
      cases hop with
      | mk code hargs =>
        have hfa := trel_flattenArgs_opt hG hargs
        have hel := evalThreadLet?_opt_rel code hfa
        dsimp only [rewriteCTAux]
        rcases hel with ⟨he₁, he₂⟩ | ⟨o₁, o₂, he₁, he₂, ho⟩
        · rw [he₁, he₂]
          obtain ⟨r₁, r₂, hr₁, hr₂, hr⟩ := trel_toRealArgs?_rel hfa
          rw [hr₁, hr₂]
          exact .let_ (.mk code hr) fun xs₁ xs₂ =>
            ih (toOptArgTup xs₁) (toOptArgTup xs₂) pk
              (ctx_optArgRel_append (mem_zip_toOptArgTup xs₁ xs₂) hG)
              (hD.weaken (fun _ h => List.mem_append_right _ h) (fun _ h => h))
        · rw [he₁, he₂]
          exact ih o₁ o₂ pk (ctx_optArgRel_append_same (mem_zip_optArgRel ho) hG) hD
    | _ => exact .hlt
  | load t ha _ ih =>
    intro p G' D' hG hD
    cases p with
    | node1 pk =>
      obtain ⟨r₁, r₂, hr₁, hr₂, hr⟩ := (OptArgRel.flattenArg hG ha).toRealArg?
      dsimp only [rewriteCTAux]
      rw [hr₁, hr₂]
      exact .load t hr fun v₁ v₂ =>
        ih (.var (some v₁)) (.var (some v₂)) pk (ctx_optArgRel_cons_var hG v₁ v₂)
          (hD.weaken (fun _ h => List.mem_cons_of_mem _ h) (fun _ h => h))
    | _ => exact .hlt
  | store hv ha _ ih =>
    intro p G' D' hG hD
    cases p with
    | node1 pk =>
      obtain ⟨rv₁, rv₂, hrv₁, hrv₂, hrv⟩ := (OptArgRel.flattenArg hG hv).toRealArg?
      obtain ⟨ra₁, ra₂, hra₁, hra₂, hra⟩ := (OptArgRel.flattenArg hG ha).toRealArg?
      dsimp only [rewriteCTAux]
      rw [hrv₁, hrv₂, hra₁, hra₂]
      exact .store hrv hra (ih pk hG hD)
    | _ => exact .hlt
  | call f hargs _ ih =>
    intro p G' D' hG hD
    cases p with
    | node1 pk =>
      obtain ⟨r₁, r₂, hr₁, hr₂, hr⟩ := trel_toRealArgs?_rel (trel_flattenArgs_opt hG hargs)
      dsimp only [rewriteCTAux]
      rw [hr₁, hr₂]
      exact .call f hr fun xs₁ xs₂ =>
        ih (toOptArgTup xs₁) (toOptArgTup xs₂) pk
          (ctx_optArgRel_append (mem_zip_toOptArgTup xs₁ xs₂) hG)
          (hD.weaken (fun _ h => List.mem_append_right _ h) (fun _ h => h))
    | _ => exact .hlt
  | jnz hc _ _ iht ihe =>
    intro p G' D' hG hD
    cases p with
    | node2 pt pe =>
      have hfl := OptArgRel.flattenArg hG hc
      dsimp only [rewriteCTAux]
      cases e₁ : flattenArg _ <;> cases e₂ : flattenArg _ <;> rw [e₁, e₂] at hfl
      · cases hfl; exact .jnz (.var ‹_›) (iht pt hG hD) (ihe pe hG hD)
      · cases hfl
      · cases hfl
      · cases hfl; next c => cases c with | false => exact ihe pe hG hD | true => exact iht pt hG hD
    | _ => exact .hlt
  | jump hj hargs =>
    intro p G' D' hG hD
    cases p with
    | jump tryInl =>
      exact CTLabel.emitJump_wf tryInl (hD _ hj) (trel_flattenArgs_opt hG hargs)
    | _ => exact .hlt
  | ret hvs =>
    intro p G' _ hG _
    cases p with
    | leaf =>
      obtain ⟨r₁, r₂, hr₁, hr₂, hr⟩ := trel_toRealArgs?_rel (trel_flattenArgs_opt hG hvs)
      dsimp only [rewriteCTAux]; rw [hr₁, hr₂]; exact .ret hr
    | _ => exact .hlt
  | exit f hargs =>
    intro p G' _ hG _
    cases p with
    | leaf =>
      obtain ⟨r₁, r₂, hr₁, hr₂, hr⟩ := trel_toRealArgs?_rel (trel_flattenArgs_opt hG hargs)
      dsimp only [rewriteCTAux]; rw [hr₁, hr₂]; exact .exit f hr
    | _ => exact .hlt
  | hlt => intro p _ _ _ _; cases p <;> exact .hlt
  | @group _ Dc sig b₁ b₂ k₁ k₂ hb _ ihb ihk =>
    intro p G' D' hG hD
    cases p with
    | group acts pbs pk =>
      refine .group (sig := threadSig acts sig) (fun Js₁ Js₂ => ?_) (fun Js₁ Js₂ => ?_)
      · let lsNo₁ := buildTargets (V := V₁) (rs := rs) acts sig Js₁
        let lsNo₂ := buildTargets (V := V₂) (rs := rs) acts sig Js₂
        let D'_new := Tup.zip Js₁ Js₂ ++ D'
        have hNo : CTDRel G' D'_new (Tup.zip lsNo₁ lsNo₂) :=
          buildTargets_rel acts sig Js₁ Js₂ fun _ hp => List.mem_append_left _ hp
        have hD_no : CTDRel G' D'_new (Tup.zip lsNo₁ lsNo₂ ++ Dc) :=
          hNo.append (hD.weaken (fun _ h => h) (fun _ h => List.mem_append_right _ h))
        let lsBody₁ := attachInlines acts pbs (b₁ lsNo₁) lsNo₁
        let lsBody₂ := attachInlines acts pbs (b₂ lsNo₂) lsNo₂
        have hBody : CTDRel G' D'_new (Tup.zip lsBody₁ lsBody₂) :=
          attachInlines_rel hG hD_no acts pbs (b₁ lsNo₁) (b₂ lsNo₂)
            (hb lsNo₁ lsNo₂) lsNo₁ lsNo₂ hNo
        have hD_body : CTDRel G' D'_new (Tup.zip lsBody₁ lsBody₂ ++ Dc) :=
          hBody.append (hD.weaken (fun _ h => h) (fun _ h => List.mem_append_right _ h))
        exact rewriteCTBlocks_wf acts pbs (b₁ lsBody₁) (b₂ lsBody₂) lsNo₁ lsNo₂ hNo
          fun {ts} i pb a₁ a₂ {H'} ha =>
            ihb lsBody₁ lsBody₂ i a₁ a₂ pb (ctx_optArgRel_append ha hG)
              (hD_body.weaken (fun _ h => List.mem_append_right _ h) (fun _ h => h))
      · let lsNo₁ := buildTargets (V := V₁) (rs := rs) acts sig Js₁
        let lsNo₂ := buildTargets (V := V₂) (rs := rs) acts sig Js₂
        let D'_new := Tup.zip Js₁ Js₂ ++ D'
        have hNo : CTDRel G' D'_new (Tup.zip lsNo₁ lsNo₂) :=
          buildTargets_rel acts sig Js₁ Js₂ fun _ hp => List.mem_append_left _ hp
        have hD_no : CTDRel G' D'_new (Tup.zip lsNo₁ lsNo₂ ++ Dc) :=
          hNo.append (hD.weaken (fun _ h => h) (fun _ h => List.mem_append_right _ h))
        let lsBody₁ := attachInlines acts pbs (b₁ lsNo₁) lsNo₁
        let lsBody₂ := attachInlines acts pbs (b₂ lsNo₂) lsNo₂
        have hBody : CTDRel G' D'_new (Tup.zip lsBody₁ lsBody₂) :=
          attachInlines_rel hG hD_no acts pbs (b₁ lsNo₁) (b₂ lsNo₂)
            (hb lsNo₁ lsNo₂) lsNo₁ lsNo₂ hNo
        have hD_body : CTDRel G' D'_new (Tup.zip lsBody₁ lsBody₂ ++ Dc) :=
          hBody.append (hD.weaken (fun _ h => h) (fun _ h => List.mem_append_right _ h))
        exact ihk lsBody₁ lsBody₂ pk hG hD_body
    | _ => exact .hlt

end CondThreadOptImpl

end LeanQbe.T
