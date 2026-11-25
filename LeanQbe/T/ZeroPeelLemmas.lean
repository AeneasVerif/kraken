module

public import LeanQbe.T.ZeroPeel
public import LeanQbe.T.Module
import all LeanQbe.T.ZeroPeel
import LeanQbe.T.ZeroPeelLemmas1
import LeanQbe.T.FlatLemmas
import LeanQbe.T.OptUtilLemmas
import LeanQbe.T.OpsLemmas
import LeanQbe.T.GroupLfpLemmas
import LeanQbe.T.WPLemmas
import LeanQbe.T.PassFlatKit
import all Kraken.Mem

/-!
# Soundness & Well-Formedness of `LeanQbe.T.ZeroPeel`

Proves syntactic well-scopedness preservation (`TFlat.wfCheck_zeroPeelWith`), relational
PHOAS well-formedness (`Func.zeroPeelWith_wf`, `Func.zeroPeel_wf`, `Fn.zeroPeel_wf`), weakest
precondition semantic refinement (`Func.zeroPeelWith_spec`, `Func.zeroPeel_spec`,
`Fn.zeroPeel_spec`), and static call-closure + module safety (`Func.zeroPeelWith_callsOk`,
`Func.zeroPeel_callsOk`, `Fn.zeroPeel_callsOk`, `Module.zeroPeel_ok`).
-/

set_option autoImplicit false

namespace LeanQbe.T

open Std Std.ExtHashMap

namespace ZeroPeel

/-! ## Section 4A: Symbolic Fill Matcher WF (`matchFillBody_wf`, `wfCheck_widenFillSingle`) -/

private def SymOuterOk (GOuter : List Ty) : Sym64 → Prop
  | .loopI => True
  | .outer idx0 => checkArg GOuter i64 (.var idx0) = true
  | .const _ => True
  | .add a b => SymOuterOk GOuter a ∧ SymOuterOk GOuter b
  | .shlConst a _ => SymOuterOk GOuter a
  | .cmpU _ bnd => checkArg GOuter i64 bnd = true
  | .other => True

private def SymEnvWf (GOuter GLocal : List Ty) (env : Array Sym64) : Prop :=
  env.size = GLocal.length ∧ ∀ s ∈ env.toList, SymOuterOk GOuter s

private theorem symToOuterArg64_wf {GOuter : List Ty} {s : Sym64} {a : Arg K i64}
    (hs : SymOuterOk GOuter s) (hm : symToOuterArg64 s = some a) :
    checkArg GOuter i64 a = true := by
  cases s with
  | outer _ => dsimp only [symToOuterArg64] at hm; cases hm; exact hs
  | const _ => dsimp only [symToOuterArg64] at hm; cases hm; rfl
  | _ => dsimp only [symToOuterArg64] at hm; cases hm

private theorem matchOffLoop_wf {GOuter : List Ty} {s : Sym64} {off? : Option (Arg K i64)}
    (hs : SymOuterOk GOuter s) (hm : matchOffLoop s = some off?) :
    off?.all (checkArg GOuter i64) = true := by
  cases s with
  | loopI => dsimp only [matchOffLoop] at hm; cases hm; rfl
  | add a b =>
    dsimp only [SymOuterOk] at hs; dsimp only [matchOffLoop] at hm
    cases a <;> cases b <;> dsimp only at hm <;>
      first
      | (cases hm; done)
      | (rcases Option.map_eq_some_iff.mp hm with ⟨arg, harg, rfl⟩
         rw [Option.all_some]
         first | exact symToOuterArg64_wf hs.1 harg | exact symToOuterArg64_wf hs.2 harg)
  | _ => dsimp only [matchOffLoop] at hm; cases hm

private theorem matchAddr_wf {GOuter : List Ty} {s : Sym64} {sh : Nat}
    {res : Arg K i64 × Option (Arg K i64)}
    (hs : SymOuterOk GOuter s) (hm : matchAddr sh s = some res) :
    checkArg GOuter i64 res.1 = true ∧ res.2.all (checkArg GOuter i64) = true := by
  cases s with
  | add x y =>
    dsimp only [SymOuterOk] at hs
    dsimp only [matchAddr] at hm
    let chk (p idx : Sym64) : Option (Arg K i64 × Option (Arg K i64)) :=
      match symToOuterArg64 p with
      | some base =>
        if (sh == 0) = true then Option.map (fun x => (base, x)) (matchOffLoop idx)
        else
          match idx with
          | .shlConst inner s =>
            if (s == sh) = true then Option.map (fun x => (base, x)) (matchOffLoop inner)
            else none
          | _ => none
      | none => none
    have check_wf : ∀ p idx : Sym64, SymOuterOk GOuter p → SymOuterOk GOuter idx →
        chk p idx = some res →
        checkArg GOuter i64 res.1 = true ∧ res.2.all (checkArg GOuter i64) = true := by
      intro p idx hp hidx hc
      dsimp only [chk] at hc
      cases hso : symToOuterArg64 p with
      | none => simp [hso] at hc
      | some base =>
        rw [hso] at hc; dsimp only at hc; have hb := symToOuterArg64_wf hp hso
        by_cases hsh : (sh == 0) = true
        · rw [ite_eq_left hsh] at hc
          rcases Option.map_eq_some_iff.mp hc with ⟨off?, hoff, rfl⟩
          exact ⟨hb, matchOffLoop_wf hidx hoff⟩
        · rw [ite_eq_right hsh] at hc
          cases idx with
          | shlConst inner s =>
            dsimp only at hc; by_cases hsEq : (s == sh) = true
            · rw [ite_eq_left hsEq] at hc
              rcases Option.map_eq_some_iff.mp hc with ⟨off?, hoff, rfl⟩
              exact ⟨hb, matchOffLoop_wf (s := inner) hidx hoff⟩
            · rw [ite_eq_right hsEq] at hc; cases hc
          | _ => cases hc
    change (match chk x y with | some r => some r | none => chk y x) = some res at hm
    cases hc1 : chk x y with
    | some r => rw [hc1] at hm; cases hm; exact check_wf x y hs.1 hs.2 hc1
    | none => rw [hc1] at hm; exact check_wf y x hs.2 hs.1 hm
  | _ => dsimp only [matchAddr] at hm; cases hm

private theorem argToSym64_var (env : Array Sym64) {t : Ty} (idx : K t) :
    argToSym64 env (.var idx) =
      if idx < env.size then env[env.size - 1 - idx]!
      else if t == i64 then
        if idx == env.size then .loopI else .outer (idx - (env.size + 1))
      else .other := by
  dsimp only [argToSym64]; split <;> try (next h => cases h)
  next h => cases h; rfl

private theorem argToSym64_wf {GOuter GLocal : List Ty} {env : Array Sym64}
    (hwf : SymEnvWf GOuter GLocal env) {t : Ty} {a : Arg K t}
    (ha : checkArg (GLocal ++ i64 :: GOuter) t a = true) :
    SymOuterOk GOuter (argToSym64 env a) := by
  cases a with
  | imm _ => dsimp only [argToSym64]; split <;> trivial
  | var idx =>
    rw [argToSym64_var]; split
    · next hlt =>
      dsimp only [K] at hlt idx
      have hidx : env.size - 1 - idx < env.size := by omega
      rw [getElem!_pos env (env.size - 1 - idx) hidx]
      exact hwf.2 _ (Array.getElem_mem_toList hidx)
    · next hge =>
      dsimp only [K] at hge idx; split
      · next ht =>
        rw [beq_iff_eq] at ht; subst ht; split
        · exact trivial
        · next hne =>
          have hlen := hwf.1; dsimp only [K] at *; simp only [beq_iff_eq] at hne
          have hge' : GLocal.length ≤ idx := by omega
          simp only [checkArg, listGet?_append_drop GLocal (i64 :: GOuter) idx hge'] at ha
          rw [show idx - GLocal.length = (idx - (GLocal.length + 1)) + 1 by omega] at ha
          rw [show idx - (env.size + 1) = idx - (GLocal.length + 1) by omega]; exact ha
      · exact trivial

private theorem symEnvWf_push {GOuter GLocal : List Ty} {env : Array Sym64}
    (hwf : SymEnvWf GOuter GLocal env) (ts : List Ty) (sy : List Sym64)
    (hlen : sy.length = ts.length) (hok : ∀ s ∈ sy, SymOuterOk GOuter s) :
    SymEnvWf GOuter (pushTypes ts GLocal) (env ++ sy.toArray) := by
  refine ⟨by rw [Array.size_append, hwf.1, List.size_toArray, hlen, pushTypes_length,
    Nat.add_comm], fun s hs => ?_⟩
  rw [Array.toList_append, List.toList_toArray, List.mem_append] at hs
  exact hs.elim (hwf.2 s) (hok s)

private theorem symOuterOk_cmpU {GOuter : List Ty} (isLt : Bool) {s : Sym64}
    (hs : SymOuterOk GOuter s) :
    SymOuterOk GOuter ((Option.map (Sym64.cmpU isLt) (symToOuterArg64 s)).getD .other) := by
  cases hso : symToOuterArg64 s with
  | none => exact trivial
  | some _ => exact symToOuterArg64_wf hs hso

private theorem evalSymOp_wf {GOuter GLocal : List Ty} {env : Array Sym64}
    (hwf : SymEnvWf GOuter GLocal env) {ts : List Ty} (op : Op K ts)
    (hargs : checkArgs (GLocal ++ i64 :: GOuter) op.args = true) :
    SymEnvWf GOuter (pushTypes ts GLocal) (env ++ (evalSymOp env op).toArray) := by
  refine symEnvWf_push hwf ts (evalSymOp env op) (evalSymOp_len env op) ?_
  have hOth : ∀ {ts' : List Ty} {op' : Op K ts'},
      evalSymOp1 env op' = none → ∀ s ∈ evalSymOp env op', SymOuterOk GOuter s := by
    intro ts' op' h1 s hs
    dsimp only [evalSymOp] at hs; rw [h1] at hs
    have hs' : s ∈ ts'.map fun _ => Sym64.other := by
      cases ts' with | nil => exact hs | cons _ tl => cases tl <;> exact hs
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hs'; exact trivial
  cases op with
  | mk code args =>
    cases code with
    | copy t =>
      by_cases ht : t = i64
      · subst ht
        dsimp only [evalSymOp, evalSymOp1]; rw [dite_eq_left rfl]
        intro s hs; cases hs with
        | head =>
          dsimp only [checkArgs] at hargs; rw [Bool.and_true] at hargs
          exact argToSym64_wf hwf hargs
        | tail _ h => cases h
      · exact hOth (by dsimp only [evalSymOp1]; rw [dite_eq_right ht])
    | add t =>
      by_cases ht : t = i64
      · subst ht; rcases args with ⟨a, b, ⟨⟩⟩
        dsimp only [evalSymOp, evalSymOp1]; rw [dite_eq_left rfl]
        intro s hs; cases hs with
        | head =>
          rw [checkArgs_pair_eq, Bool.and_eq_true] at hargs
          exact ⟨argToSym64_wf hwf hargs.1, argToSym64_wf hwf hargs.2⟩
        | tail _ h => cases h
      · exact hOth (by dsimp only [evalSymOp1]; rw [dite_eq_right ht])
    | shl t =>
      by_cases ht : t = i64
      · subst ht; rcases args with ⟨a, b, ⟨⟩⟩
        rw [checkArgs_pair_eq, Bool.and_eq_true] at hargs
        dsimp only [evalSymOp, evalSymOp1]; rw [dite_eq_left rfl]
        cases argToSym64 env b <;> intro s hs <;> cases hs with
        | head => first | exact trivial | exact argToSym64_wf hwf hargs.1
        | tail _ h => cases h
      · exact hOth (by dsimp only [evalSymOp1]; rw [dite_eq_right ht])
    | cmp o t _ _ =>
      by_cases ht : t = i64
      · subst ht; rcases args with ⟨a, b, ⟨⟩⟩
        rw [checkArgs_pair_eq, Bool.and_eq_true] at hargs
        have hsa := argToSym64_wf hwf hargs.1
        have hsb := argToSym64_wf hwf hargs.2
        dsimp only [evalSymOp, evalSymOp1]; rw [dite_eq_left rfl]
        intro s hs; cases hs with
        | head =>
          cases o <;>
            first
            | exact trivial
            | (cases argToSym64 env a <;>
                first | exact trivial | exact symOuterOk_cmpU _ hsb)
            | (cases argToSym64 env b <;>
                first | exact trivial | exact symOuterOk_cmpU _ hsa)
        | tail _ h => cases h
      · exact hOth (by dsimp only [evalSymOp1]; rw [dite_eq_right ht])
    | _ => exact hOth rfl

private theorem matchBodyTail_wf {rs : List Ty} {GOuter : List Ty} {D : List (List Ty)}
    {isLt : Bool} {bnd : Arg K i64} {spec : FillSpec} :
    (tf : TFlat rs) → {GLocal : List Ty} → {env : Array Sym64} →
    SymEnvWf GOuter GLocal env →
    tf.wfCheck (GLocal ++ i64 :: GOuter) D = true →
    matchBodyTail env isLt bnd tf = some spec →
    checkArg GOuter i64 spec.base = true ∧ spec.off?.all (checkArg GOuter i64) = true ∧
      spec.shift ≤ 3 ∧ spec.bound = bnd ∧ spec.isLt = isLt
  | .let_ op k, GLocal, env, hwf, htf, hm => by
    rw [wfCheck_let_eq, Bool.and_eq_true] at htf
    dsimp only [matchBodyTail] at hm
    by_cases hp : isTotalPureOp op.code = true
    · rw [ite_eq_left hp] at hm
      have hk := htf.2
      rw [pushTypes_append] at hk
      exact matchBodyTail_wf k (evalSymOp_wf hwf op htf.1) hk hm
    · rw [ite_eq_right hp] at hm; cases hm
  | .store valArg addrArg cont, GLocal, env, hwf, htf, hm => by
    rw [wfCheck_store_eq, Bool.and_eq_true, Bool.and_eq_true] at htf
    dsimp only [matchBodyTail] at hm
    cases valArg with
    | imm v =>
      dsimp only at hm
      cases hsp : splatVal64 v with
      | none => rw [hsp] at hm; cases hm
      | some p =>
        rcases p with ⟨shift, fill64⟩
        rw [hsp] at hm; dsimp only at hm
        cases hma : matchAddr shift (argToSym64 env addrArg) with
        | none => rw [hma] at hm; cases hm
        | some bp =>
          rcases bp with ⟨base, off?⟩
          rw [hma] at hm; dsimp only at hm
          by_cases hchk : checkJump0Inc1 env cont = true
          · rw [ite_eq_left hchk] at hm; cases hm
            have hwfA := matchAddr_wf (argToSym64_wf hwf htf.1.2) hma
            have hsp' := splatVal64_spec v hsp
            exact ⟨hwfA.1, hwfA.2, hsp'.1, rfl, rfl⟩
          · rw [ite_eq_right hchk] at hm; cases hm
    | var _ => cases hm
  | .load _ _ _, _, _, _, _, hm | .call _ _ _ _, _, _, _, _, hm
  | .jnz _ _ _, _, _, _, _, hm | .jump _ _, _, _, _, _, hm
  | .ret _, _, _, _, _, hm | .exit _ _, _, _, _, _, hm
  | .hlt, _, _, _, _, hm | .group _ _, _, _, _, _, hm => by
    dsimp only [matchBodyTail] at hm; cases hm

private theorem matchFillBody_wf {rs : List Ty} {GOuter : List Ty} {D : List (List Ty)}
    {spec : FillSpec} :
    (tf : TFlat rs) → {GLocal : List Ty} → {env : Array Sym64} →
    SymEnvWf GOuter GLocal env →
    tf.wfCheck (GLocal ++ i64 :: GOuter) D = true →
    matchFillBody env tf = some spec →
    checkArg GOuter i64 spec.bound = true ∧
      checkArg GOuter i64 spec.base = true ∧
      spec.off?.all (checkArg GOuter i64) = true ∧ spec.shift ≤ 3
  | .let_ op k, GLocal, env, hwf, htf, hm => by
    rw [wfCheck_let_eq, Bool.and_eq_true] at htf
    dsimp only [matchFillBody] at hm
    by_cases hp : isTotalPureOp op.code = true
    · rw [ite_eq_left hp] at hm
      have hk := htf.2
      rw [pushTypes_append] at hk
      exact matchFillBody_wf k (evalSymOp_wf hwf op htf.1) hk hm
    · rw [ite_eq_right hp] at hm; cases hm
  | .jnz c t e, GLocal, env, hwf, htf, hm => by
    rw [wfCheck_jnz_eq, Bool.and_eq_true, Bool.and_eq_true] at htf
    dsimp only [matchFillBody] at hm
    cases hc : argToSym64 env c with
    | cmpU isLt bnd =>
      rw [hc] at hm; dsimp only at hm
      have hcb : SymOuterOk GOuter (argToSym64 env c) := argToSym64_wf hwf htf.1.1
      rw [hc] at hcb
      have ht := matchBodyTail_wf t hwf htf.1.2 hm
      rcases ht with ⟨hb, ho, hsh, hbeq, _⟩
      exact ⟨hbeq ▸ hcb, hb, ho, hsh⟩
    | loopI | outer _ | const _ | add _ _ | shlConst _ _ | other =>
      rw [hc] at hm; cases hm
  | .load _ _ _, _, _, _, _, hm | .store _ _ _, _, _, _, _, hm
  | .call _ _ _ _, _, _, _, _, hm | .jump _ _, _, _, _, _, hm
  | .ret _, _, _, _, _, hm | .exit _ _, _, _, _, _, hm
  | .hlt, _, _, _, _, hm | .group _ _, _, _, _, _, hm => by
    dsimp only [matchFillBody] at hm; cases hm


private theorem widenFillSingle_eq_some {rs : List Ty} {unrollN : Nat} {ts0 : List Ty}
    {body k res : TFlat rs} (hw : widenFillSingle unrollN ts0 body k = some res) :
    1 ≤ unrollN ∧ unrollN ≤ 64 ∧ ts0 = [i64] ∧
    ∃ (initArg : Arg K i64) (spec : FillSpec),
      k = @TFlat.jump rs [i64] 0 (initArg, ()) ∧ matchFillBody #[] body = some spec ∧
      res = .group (@TBlocks.cons rs [i64] [] body .nil) (mkWideWrapper spec unrollN initArg) := by
  dsimp only [widenFillSingle] at hw
  split at hw
  · cases hw
  · next hNotBad =>
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] at hNotBad
    split at hw
    · next initArg =>
      split at hw
      · next spec hm =>
        cases hw
        exact ⟨by omega, by omega, rfl, initArg, spec, rfl, hm, rfl⟩
      · cases hw
    · cases hw

private theorem wfCheck_widenFillSingle {rs : List Ty} {GOuter : List Ty} {DOuter : List (List Ty)}
    {unrollN : Nat} {ts0 : List Ty} {body k res : TFlat rs}
    (hwfG : (TFlat.group (sig := [ts0]) (.cons body .nil) k).wfCheck GOuter DOuter = true)
    (hw : widenFillSingle unrollN ts0 body k = some res) :
    res.wfCheck GOuter DOuter = true := by
  obtain ⟨hunroll1, _, rfl, initArg, spec, rfl, hm, rfl⟩ := widenFillSingle_eq_some hw
  have hunroll : 0 < unrollN := Nat.lt_of_lt_of_le (by omega) hunroll1
  rw [wfCheck_group_eq, wfCheckB_cons_eq, wfCheckB_nil_eq,
    Bool.and_true, Bool.and_eq_true] at hwfG
  rcases hwfG with ⟨hBodyWf, hJumpWf⟩
  have hInit : checkArg GOuter i64 initArg = true := by
    rw [wfCheck_jump_eq, Bool.and_eq_true] at hJumpWf
    have hj := hJumpWf.2
    dsimp only [pushTypes, checkArgs] at hj
    rw [Bool.and_true] at hj; exact hj
  have hEmpty : SymEnvWf GOuter [] #[] := ⟨rfl, fun _ hs => by cases hs⟩
  have hSpec := matchFillBody_wf body hEmpty hBodyWf hm
  rw [wfCheck_group_eq, wfCheckB_cons_eq, wfCheckB_nil_eq,
    Bool.and_true, Bool.and_eq_true]
  exact ⟨hBodyWf,
    wfCheck_mkWideWrapper hunroll hInit hSpec.1 hSpec.2.1 hSpec.2.2.1⟩

/-! ## Section 4B: Semantics of Wide-Zero Idiom (`widenFillSingle_wp`) -/

private def SymRel (vsOuter : List ((t : Ty) × Val t)) (iVal : Val i64) :
    Sym64 → (t : Ty) × Val t → Prop
  | .loopI, tv => tv = ⟨i64, iVal⟩
  | .outer idx0, tv =>
    ∃ (a : Arg Val i64), denoteArg vsOuter (.var idx0) = some a ∧ tv = ⟨i64, a.val⟩
  | .const c, tv => tv = ⟨i64, c⟩
  | .add a b, tv =>
    ∃ (va vb : BitVec 64),
      SymRel vsOuter iVal a ⟨i64, va⟩ ∧ SymRel vsOuter iVal b ⟨i64, vb⟩ ∧ tv = ⟨i64, va + vb⟩
  | .shlConst a s, tv =>
    ∃ (va : BitVec 64), SymRel vsOuter iVal a ⟨i64, va⟩ ∧ tv = ⟨i64, va <<< s⟩
  | .cmpU isLt bnd, tv =>
    ∃ (bndA : Arg Val i64),
      denoteArg vsOuter bnd = some bndA ∧
      tv = ⟨Ty.bool, if isLt then decide (iVal < bndA.val) else decide (iVal ≤ bndA.val)⟩
  | .other, _ => True

private def offVal (vsOuter : List ((t : Ty) × Val t)) :
    Option (Arg K i64) → Option (BitVec 64)
  | none => some 0#64
  | some off => Option.map Arg.val (denoteArg vsOuter off)

private def SymEnvMatch (vsOuter : List ((t : Ty) × Val t)) (iVal : Val i64)
    (vsLocal : List ((t : Ty) × Val t)) (env : Array Sym64) : Prop :=
  env.size = vsLocal.length ∧
  ∀ (k : Nat) (hk : k < vsLocal.length),
    SymRel vsOuter iVal env[env.size - 1 - k]! vsLocal[k]

private theorem symEnvMatch_empty {vsOuter : List ((t : Ty) × Val t)} {iVal : Val i64} :
    SymEnvMatch vsOuter iVal [] #[] :=
  ⟨rfl, fun _ hk => by simp at hk⟩

private theorem symEnvMatch_push1 {vsOuter : List ((t : Ty) × Val t)} {iVal : Val i64}
    {vsLocal : List ((t : Ty) × Val t)} {env : Array Sym64} {s : Sym64} {tv : (t : Ty) × Val t}
    (hm : SymEnvMatch vsOuter iVal vsLocal env) (hs : SymRel vsOuter iVal s tv) :
    SymEnvMatch vsOuter iVal (tv :: vsLocal) (env ++ #[s]) := by
  have hLen := hm.1
  refine ⟨by simp [hLen], fun k hk => ?_⟩
  cases k with
  | zero =>
    have hIdx : (env ++ #[s]).size - 1 - 0 = env.size := by simp
    rw [hIdx, array_getElem!_push_last]
    exact hs
  | succ k' =>
    have hk' : k' < vsLocal.length := Nat.lt_of_succ_lt_succ hk
    have hLt : env.size - 1 - k' < env.size := by omega
    have hIdx : (env ++ #[s]).size - 1 - (k' + 1) = env.size - 1 - k' := by simp; omega
    rw [hIdx, array_getElem!_append_left _ _ _ hLt]
    exact hm.2 k' hk'

private theorem pushTup_singleton {t : Ty} (x : Val t) (acc : List ((t : Ty) × Val t)) :
    pushTup (as := [t]) (x, ()) acc = ⟨t, x⟩ :: acc := rfl

private theorem symEnvMatch_push_other {vsOuter : List ((t : Ty) × Val t)} {iVal : Val i64} :
    ∀ {ts : List Ty} {vsLocal : List ((t : Ty) × Val t)} {env : Array Sym64},
      SymEnvMatch vsOuter iVal vsLocal env →
      ∀ (res : Tup Val ts) (sy : List Sym64),
        sy.length = ts.length → (∀ s ∈ sy, s = .other) →
        SymEnvMatch vsOuter iVal (pushTup res vsLocal) (env ++ sy.toArray)
  | [], _, env, hm, ⟨⟩, [], _, _ => by
    rw [pushTup_nil_eq]
    have hEq : env ++ ([] : List Sym64).toArray = env := by
      apply Array.toList_inj.mp; rw [Array.toList_append]; exact List.append_nil env.toList
    rw [hEq]; exact hm
  | _ :: _, _, env, hm, (r, res), s :: sy, hlen, hoth => by
    have hs : SymRel vsOuter iVal s ⟨_, r⟩ := by rw [hoth s (List.Mem.head _)]; trivial
    have hApp : env ++ (s :: sy).toArray = (env ++ #[s]) ++ sy.toArray := by
      apply Array.toList_inj.mp
      rw [Array.toList_append, Array.toList_append, Array.toList_append]
      exact (List.append_assoc env.toList [s] sy).symm
    rw [pushTup_cons_eq, hApp]
    exact symEnvMatch_push_other (symEnvMatch_push1 hm hs) res sy
      (Nat.succ.inj hlen) (fun x hx => hoth x (List.Mem.tail _ hx))

private theorem argToSym64_correct {vsOuter : List ((t : Ty) × Val t)} {iVal : Val i64}
    {vsLocal : List ((t : Ty) × Val t)} {env : Array Sym64}
    (hm : SymEnvMatch vsOuter iVal vsLocal env) {t : Ty} (a : Arg K t) {valA : Arg Val t}
    (hd : denoteArg (vsLocal ++ ⟨i64, iVal⟩ :: vsOuter) a = some valA) :
    SymRel vsOuter iVal (argToSym64 env a) ⟨t, valA.val⟩ := by
  cases a with
  | imm c =>
    dsimp only [denoteArg] at hd; cases hd
    cases t with
    | bool | float _ | pair _ _ => exact trivial
    | bits n =>
      cases n with
      | zero => exact trivial
      | succ n' =>
        by_cases hn : n' = 63
        · subst hn; exact rfl
        · cases n' <;> simp_all [argToSym64, SymRel]
  | var idx =>
    rw [argToSym64_var]
    by_cases hLt : idx < env.size
    · rw [ite_eq_left hLt]
      have hk : idx < vsLocal.length := hm.1 ▸ hLt
      have hGet : listGet? (vsLocal ++ ⟨i64, iVal⟩ :: vsOuter) idx = some vsLocal[idx] := by
        rw [listGet?_eq_getElem?, List.getElem?_append_left hk, List.getElem?_eq_getElem hk]
      dsimp only [denoteArg, lookupV] at hd; rw [hGet] at hd; dsimp only at hd
      cases hCast : castTy vsLocal[idx].1 t vsLocal[idx].2 with
      | none => rw [hCast] at hd; cases hd
      | some v =>
        rw [hCast] at hd; cases hd
        have hTv : (⟨t, (Arg.var v).val⟩ : (t : Ty) × Val t) = vsLocal[idx] :=
          (castTy_some_eq hCast).symm
        rw [hTv]
        exact hm.2 idx hk
    · rw [ite_eq_right hLt]
      have hGe : vsLocal.length ≤ idx := hm.1 ▸ Nat.le_of_not_lt hLt
      have hDrop : listGet? (vsLocal ++ ⟨i64, iVal⟩ :: vsOuter) idx =
          listGet? (⟨i64, iVal⟩ :: vsOuter) (idx - env.size) := by
        rw [listGet?_eq_getElem?, listGet?_eq_getElem?, List.getElem?_append_right hGe, hm.1]
      dsimp only [denoteArg, lookupV] at hd; rw [hDrop] at hd
      by_cases hEq : idx = env.size
      · subst hEq
        rw [Nat.sub_self, listGet?_cons_zero_eq] at hd; dsimp only at hd
        cases hCast : castTy i64 t iVal with
        | none => rw [hCast] at hd; cases hd
        | some v =>
          rw [hCast] at hd; cases hd
          have hTy := castTy_some_eq hCast
          have ht : t = i64 := (congrArg Sigma.fst hTy).symm
          subst ht
          dsimp only [castTy] at hCast; rw [dite_eq_left rfl] at hCast; cases hCast
          rw [ite_eq_left (beq_self_eq_true i64), ite_eq_left (beq_self_eq_true env.size)]
          rfl
      · have hGt : env.size < idx := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hLt) (Ne.symm hEq)
        obtain ⟨m, hmSub⟩ := Nat.exists_eq_add_of_lt hGt
        have hSub1 : idx - env.size = m + 1 := by
          have : idx = env.size + (m + 1) := by dsimp [K] at *; omega
          rw [this, Nat.add_sub_cancel_left]
        have hSub2 : idx - (env.size + 1) = m := by
          have : idx = (env.size + 1) + m := by dsimp [K] at *; omega
          rw [this, Nat.add_sub_cancel_left]
        rw [hSub1, listGet?_cons_succ_eq] at hd
        rw [hSub2]
        by_cases ht : t = i64
        · subst ht
          rw [ite_eq_left (beq_self_eq_true i64),
            ite_eq_right (beq_false_of_ne hEq ▸ Bool.false_ne_true)]
          dsimp only [SymRel]
          cases hCast : listGet? vsOuter m with
          | none => rw [hCast] at hd; cases hd
          | some tv =>
            rw [hCast] at hd; dsimp only at hd
            cases hC : castTy tv.1 i64 tv.2 with
            | none => rw [hC] at hd; cases hd
            | some v =>
              rw [hC] at hd; cases hd
              refine ⟨.var v, ?_, rfl⟩
              dsimp only [denoteArg, lookupV]; rw [hCast]; dsimp only; rw [hC]
        · rw [ite_eq_right (beq_false_of_ne ht ▸ Bool.false_ne_true)]; exact trivial

private theorem symToOuterArg64_correct {vsOuter : List ((t : Ty) × Val t)} {iVal : Val i64}
    {s : Sym64} {tv : (t : Ty) × Val t} {a : Arg K i64}
    (hrel : SymRel vsOuter iVal s tv) (hsym : symToOuterArg64 s = some a) :
    ∃ aVal : Arg Val i64, denoteArg vsOuter a = some aVal ∧ tv = ⟨i64, aVal.val⟩ := by
  cases s with
  | outer _ => dsimp only [symToOuterArg64] at hsym; cases hsym; exact hrel
  | const c => dsimp only [symToOuterArg64] at hsym; cases hsym; exact ⟨.imm c, rfl, hrel⟩
  | loopI | add _ _ | shlConst _ _ | cmpU _ _ | other =>
    dsimp only [symToOuterArg64] at hsym; cases hsym

private theorem matchOffLoop_add_arm {vsOuter : List ((t : Ty) × Val t)} {iVal va vb : Val i64}
    {s : Sym64} {off? : Option (Arg K i64)} (ha : va = iVal)
    (hb : SymRel vsOuter iVal s ⟨i64, vb⟩)
    (hm : Option.map some (symToOuterArg64 s) = some off?) :
    ∃ oVal : BitVec 64, offVal vsOuter off? = some oVal ∧ iVal + oVal = va + vb := by
  rcases Option.map_eq_some_iff.mp hm with ⟨off, hoff, rfl⟩
  obtain ⟨offA, hd, hEq⟩ := symToOuterArg64_correct hb hoff
  have hvb : vb = offA.val := sigma_val_eq hEq
  subst ha; subst hvb
  exact ⟨offA.val, by dsimp only [offVal]; rw [hd]; rfl, rfl⟩

private theorem matchOffLoop_correct {vsOuter : List ((t : Ty) × Val t)} {iVal : Val i64}
    {s : Sym64} {tv : (t : Ty) × Val t} {off? : Option (Arg K i64)}
    (hrel : SymRel vsOuter iVal s tv) (hm : matchOffLoop s = some off?) :
    ∃ oVal : BitVec 64, offVal vsOuter off? = some oVal ∧ tv = ⟨i64, iVal + oVal⟩ := by
  cases s with
  | loopI =>
    dsimp only [matchOffLoop] at hm; cases hm
    have hv : tv = ⟨i64, iVal⟩ := hrel
    exact ⟨0#64, rfl, by rw [BitVec.add_zero]; exact hv⟩
  | add a b =>
    rcases hrel with ⟨va, vb, ha, hb, rfl⟩
    cases a with
    | loopI =>
      have hva : va = iVal := sigma_val_eq ha
      dsimp only [matchOffLoop] at hm
      obtain ⟨oVal, hO, hSum⟩ := matchOffLoop_add_arm hva hb hm
      exact ⟨oVal, hO, by rw [hSum]⟩
    | outer _ | const _ | add _ _ | shlConst _ _ | cmpU _ _ | other =>
      cases b with
      | loopI =>
        have hvb : vb = iVal := sigma_val_eq hb
        dsimp only [matchOffLoop] at hm
        obtain ⟨oVal, hO, hSum⟩ := matchOffLoop_add_arm hvb ha hm
        exact ⟨oVal, hO, by rw [hSum, BitVec.add_comm]⟩
      | outer _ | const _ | add _ _ | shlConst _ _ | cmpU _ _ | other =>
        dsimp only [matchOffLoop] at hm; cases hm
  | outer _ | const _ | shlConst _ _ | cmpU _ _ | other =>
    dsimp only [matchOffLoop] at hm; cases hm

private theorem matchAddrCheck_correct {vsOuter : List ((t : Ty) × Val t)} {iVal : Val i64}
    (sExpected : Nat) (sp sidx : Sym64) {vp vidx : BitVec 64}
    {base : Arg K i64} {off? : Option (Arg K i64)}
    (hc : (match symToOuterArg64 sp with
      | some base =>
        if sExpected == 0 then Option.map (base, ·) (matchOffLoop sidx)
        else match sidx with
          | .shlConst inner s =>
            if s == sExpected then Option.map (base, ·) (matchOffLoop inner) else none
          | _ => none
      | none => none) = some (base, off?))
    (hp : SymRel vsOuter iVal sp ⟨i64, vp⟩) (hidx : SymRel vsOuter iVal sidx ⟨i64, vidx⟩) :
    ∃ (baseVal : Arg Val i64) (oVal : BitVec 64),
      denoteArg vsOuter base = some baseVal ∧ offVal vsOuter off? = some oVal ∧
      vp + vidx = baseVal.val + ((iVal + oVal) <<< sExpected) := by
  cases hOuter : symToOuterArg64 sp with
  | none => rw [hOuter] at hc; cases hc
  | some base' =>
    rw [hOuter] at hc; dsimp only at hc
    obtain ⟨baseVal, hdBase, hBaseEq⟩ := symToOuterArg64_correct hp hOuter
    have hvp : vp = baseVal.val := sigma_val_eq hBaseEq
    subst hvp
    by_cases hZero : sExpected = 0
    · subst hZero
      rw [ite_eq_left (beq_self_eq_true 0)] at hc
      rcases Option.map_eq_some_iff.mp hc with ⟨off'', hmOff, hPair⟩
      rcases hPair with ⟨rfl, rfl⟩
      obtain ⟨oVal, hOffVal, hIdxEq⟩ := matchOffLoop_correct hidx hmOff
      have hvidx : vidx = iVal + oVal := sigma_val_eq hIdxEq
      subst hvidx
      exact ⟨baseVal, oVal, hdBase, hOffVal, by rw [BitVec.shiftLeft_zero]⟩
    · rw [ite_eq_right (beq_false_of_ne hZero ▸ Bool.false_ne_true)] at hc
      cases sidx with
      | shlConst inner s =>
        dsimp only at hc
        by_cases hs : s = sExpected
        · subst hs
          rw [ite_eq_left (beq_self_eq_true s)] at hc
          rcases Option.map_eq_some_iff.mp hc with ⟨off'', hmOff, hPair⟩
          rcases hPair with ⟨rfl, rfl⟩
          rcases hidx with ⟨va, hInner, hIdxEq⟩
          obtain ⟨oVal, hOffVal, hVaEq⟩ := matchOffLoop_correct hInner hmOff
          have hva : va = iVal + oVal := sigma_val_eq hVaEq
          have hvidx : vidx = va <<< s := sigma_val_eq hIdxEq
          subst hva; subst hvidx
          exact ⟨baseVal, oVal, hdBase, hOffVal, rfl⟩
        · rw [ite_eq_right (beq_false_of_ne hs ▸ Bool.false_ne_true)] at hc; cases hc
      | loopI | outer _ | const _ | add _ _ | cmpU _ _ | other => cases hc

private theorem matchAddr_correct {vsOuter : List ((t : Ty) × Val t)} {iVal : Val i64}
    {sExpected : Nat} {s : Sym64} {tv : (t : Ty) × Val t}
    {base : Arg K i64} {off? : Option (Arg K i64)}
    (hrel : SymRel vsOuter iVal s tv) (hm : matchAddr sExpected s = some (base, off?)) :
    ∃ (baseVal : Arg Val i64) (oVal : BitVec 64),
      denoteArg vsOuter base = some baseVal ∧ offVal vsOuter off? = some oVal ∧
      tv = ⟨i64, baseVal.val + ((iVal + oVal) <<< sExpected)⟩ := by
  cases s with
  | add x y =>
    rcases hrel with ⟨vx, vy, hx, hy, htv⟩
    let check := fun (sp sidx : Sym64) =>
      match symToOuterArg64 sp with
      | some base =>
        if sExpected == 0 then Option.map (base, ·) (matchOffLoop sidx)
        else match sidx with
          | .shlConst inner s =>
            if s == sExpected then Option.map (base, ·) (matchOffLoop inner) else none
          | _ => none
      | none => none
    change (match check x y with | some r => some r | none => check y x) = some (base, off?) at hm
    cases hc1 : check x y with
    | some r =>
      rw [hc1] at hm; cases hm
      dsimp only [check] at hc1
      obtain ⟨baseVal, oVal, hd, ho, hAdd⟩ := matchAddrCheck_correct sExpected x y hc1 hx hy
      rw [hAdd] at htv; exact ⟨baseVal, oVal, hd, ho, htv⟩
    | none =>
      rw [hc1] at hm; dsimp only [check] at hm
      obtain ⟨baseVal, oVal, hd, ho, hAdd⟩ := matchAddrCheck_correct sExpected y x hm hy hx
      rw [BitVec.add_comm vx vy, hAdd] at htv; exact ⟨baseVal, oVal, hd, ho, htv⟩
  | loopI | outer _ | const _ | shlConst _ _ | cmpU _ _ | other =>
    dsimp only [matchAddr] at hm; cases hm

private theorem matchInc1_correct {vsOuter : List ((t : Ty) × Val t)} {iVal : Val i64}
    {s : Sym64} {tv : (t : Ty) × Val t}
    (hrel : SymRel vsOuter iVal s tv) (hm : matchInc1 s = true) :
    tv = ⟨i64, iVal + 1#64⟩ := by
  cases s with
  | add a b =>
    rcases hrel with ⟨va, vb, ha, hb, htv⟩
    dsimp only [matchInc1] at hm
    split at hm
    · rename_i heq; cases heq; rw [sigma_val_eq ha, sigma_val_eq hb] at htv; exact htv
    · rename_i heq; cases heq
      rw [sigma_val_eq ha, sigma_val_eq hb, BitVec.add_comm] at htv; exact htv
    · cases hm
  | loopI | outer _ | const _ | shlConst _ _ | cmpU _ _ | other =>
    dsimp only [matchInc1] at hm; cases hm

private theorem evalSymOp_push_other {vsOuter : List ((t : Ty) × Val t)} {iVal : Val i64}
    {vsLocal : List ((t : Ty) × Val t)} {env : Array Sym64}
    (hm : SymEnvMatch vsOuter iVal vsLocal env) {ts : List Ty} (op : Op K ts)
    {valArgs : Tup (Arg Val) op.sig} {P : Tup Val ts → Prop}
    (hwp : op.code.wp (vals valArgs) P)
    (hOth : evalSymOp env op = ts.map (fun _ => Sym64.other)) :
    ∃ res : Tup Val ts, P res ∧
      SymEnvMatch vsOuter iVal (pushTup res vsLocal) (env ++ (evalSymOp env op).toArray) := by
  obtain ⟨res, hRes⟩ := OpCode.wp_exists _ _ hwp
  refine ⟨res, hRes, hOth ▸ symEnvMatch_push_other hm res _ (List.length_map ..) ?_⟩
  intro s hs; obtain ⟨_, _, rfl⟩ := List.mem_map.mp hs; rfl

private theorem evalSymCmp_left {vsOuter : List ((t : Ty) × Val t)} {iVal : Val i64}
    (isLt : Bool) {sb : Sym64} {vb : BitVec 64}
    (hb : SymRel vsOuter iVal sb ⟨i64, vb⟩) :
    SymRel vsOuter iVal
      ((Option.map (Sym64.cmpU isLt) (symToOuterArg64 sb)).getD .other)
      ⟨Ty.bool, if isLt then CmpOp.ult.evalBits iVal vb else CmpOp.ule.evalBits iVal vb⟩ := by
  cases hs : symToOuterArg64 sb with
  | none => exact trivial
  | some bnd =>
    obtain ⟨bndA, hdb, hEq⟩ := symToOuterArg64_correct hb hs
    have hvb : vb = bndA.val := sigma_val_eq hEq
    subst hvb
    refine ⟨bndA, hdb, ?_⟩
    cases isLt <;> rfl

private theorem evalSymCmp_correct {vsOuter : List ((t : Ty) × Val t)} {iVal : Val i64}
    (o : CmpOp) {sa sb : Sym64} {va vb : BitVec 64}
    (ha : SymRel vsOuter iVal sa ⟨i64, va⟩) (hb : SymRel vsOuter iVal sb ⟨i64, vb⟩) :
    SymRel vsOuter iVal
      ((match o, sa, sb with
        | .ult, .loopI, _ => Option.map (Sym64.cmpU true) (symToOuterArg64 sb)
        | .ule, .loopI, _ => Option.map (Sym64.cmpU false) (symToOuterArg64 sb)
        | .ugt, _, .loopI => Option.map (Sym64.cmpU true) (symToOuterArg64 sa)
        | .uge, _, .loopI => Option.map (Sym64.cmpU false) (symToOuterArg64 sa)
        | _, _, _ => none).getD .other)
      ⟨Ty.bool, o.evalBits va vb⟩ := by
  cases o with
  | ult =>
    cases sa <;> first
    | exact trivial
    | (have hva : va = iVal := sigma_val_eq ha; subst hva; exact evalSymCmp_left true hb)
  | ule =>
    cases sa <;> first
    | exact trivial
    | (have hva : va = iVal := sigma_val_eq ha; subst hva; exact evalSymCmp_left false hb)
  | ugt =>
    cases sb <;> first
    | exact trivial
    | (have hvb : vb = iVal := sigma_val_eq hb; subst hvb; exact evalSymCmp_left true ha)
  | uge =>
    cases sb <;> first
    | exact trivial
    | (have hvb : vb = iVal := sigma_val_eq hb; subst hvb; exact evalSymCmp_left false ha)
  | eq | ne | slt | sle | sgt | sge => exact trivial

private theorem denoteArgs_singleton_some {V : Ty → Type}
    {vs : List ((t : Ty) × V t)} {t : Ty} {a : Arg K t} {va : Arg V t}
    (h : denoteArgs vs (ts := [t]) (a, ()) = some (va, ())) : denoteArg vs a = some va := by
  rw [denoteArgs_singleton_eq] at h
  cases hd : denoteArg vs a <;> simp_all

private theorem denoteArgs_pair_some {V : Ty → Type}
    {vs : List ((t : Ty) × V t)} {t₁ t₂ : Ty} {a : Arg K t₁} {b : Arg K t₂}
    {va : Arg V t₁} {vb : Arg V t₂}
    (h : denoteArgs vs (ts := [t₁, t₂]) (a, b, ()) = some (va, vb, ())) :
    denoteArg vs a = some va ∧ denoteArg vs b = some vb := by
  rw [denoteArgs_pair_eq] at h
  cases hda : denoteArg vs a <;> cases hdb : denoteArg vs b <;> simp_all

private theorem evalSymOp_wp {vsOuter : List ((t : Ty) × Val t)} {iVal : Val i64}
    {vsLocal : List ((t : Ty) × Val t)} {env : Array Sym64}
    (hm : SymEnvMatch vsOuter iVal vsLocal env)
    {ts : List Ty} (op : Op K ts) {valArgs : Tup (Arg Val) op.sig}
    (hargs : denoteArgs (vsLocal ++ ⟨i64, iVal⟩ :: vsOuter) op.args = some valArgs)
    {P : Tup Val ts → Prop} (hwp : op.code.wp (vals valArgs) P) :
    ∃ res : Tup Val ts, P res ∧
      SymEnvMatch vsOuter iVal (pushTup res vsLocal) (env ++ (evalSymOp env op).toArray) := by
  have hNone {ts' : List Ty} {op' : Op K ts'} {va' : Tup (Arg Val) op'.sig}
      {P' : Tup Val ts' → Prop} (hw' : op'.code.wp (vals va') P')
      (h1 : evalSymOp1 env op' = none) :
      ∃ res : Tup Val ts', P' res ∧
        SymEnvMatch vsOuter iVal (pushTup res vsLocal) (env ++ (evalSymOp env op').toArray) :=
    evalSymOp_push_other hm op' hw' (by
      dsimp only [evalSymOp]; rw [h1]; cases ts' with | nil => rfl | cons _ tl => cases tl <;> rfl)
  rcases op with ⟨code, args⟩; dsimp only at valArgs hargs hwp
  cases code with
  | copy t =>
    rcases args with ⟨a, ⟨⟩⟩; rcases valArgs with ⟨va, ⟨⟩⟩
    have hda := denoteArgs_singleton_some hargs
    by_cases ht : t = i64
    · subst ht; rw [OpCode.wp_copy] at hwp; dsimp only [vals, Arg.val] at hwp
      refine ⟨(va.val, ()), hwp, ?_⟩
      dsimp only [evalSymOp, evalSymOp1]; rw [dite_eq_left rfl, pushTup_singleton]
      exact symEnvMatch_push1 hm (argToSym64_correct hm a hda)
    · exact hNone hwp (by dsimp only [evalSymOp1]; rw [dite_eq_right ht])
  | add t =>
    rcases args with ⟨a, b, ⟨⟩⟩; rcases valArgs with ⟨va, vb, ⟨⟩⟩
    obtain ⟨hda, hdb⟩ := denoteArgs_pair_some hargs
    by_cases ht : t = i64
    · subst ht; rw [OpCode.wp_add] at hwp
      dsimp only [lift2, vals, Arg.val, i64, Ty.hasFloat] at hwp
      refine ⟨(va.val + vb.val, ()), hwp, ?_⟩
      dsimp only [evalSymOp, evalSymOp1]; rw [dite_eq_left rfl, pushTup_singleton]
      exact symEnvMatch_push1 hm
        ⟨va.val, vb.val, argToSym64_correct hm a hda, argToSym64_correct hm b hdb, rfl⟩
    · exact hNone hwp (by dsimp only [evalSymOp1]; rw [dite_eq_right ht])
  | shl t =>
    rcases args with ⟨a, b, ⟨⟩⟩; rcases valArgs with ⟨va, vb, ⟨⟩⟩
    obtain ⟨hda, hdb⟩ := denoteArgs_pair_some hargs
    by_cases ht : t = i64
    · subst ht
      cases hsb : argToSym64 env b with
      | const c =>
        rw [OpCode.wp_shl] at hwp; dsimp only [lift2, vals, Arg.val, i64, Ty.hasFloat] at hwp
        have hrelB := argToSym64_correct hm b hdb; rw [hsb] at hrelB
        refine ⟨(va.val <<< (vb.val.toNat % 64), ()), hwp, ?_⟩
        dsimp only [evalSymOp, evalSymOp1]; rw [dite_eq_left rfl, hsb, pushTup_singleton (t := i64)]
        exact symEnvMatch_push1 hm ⟨va.val, argToSym64_correct hm a hda, by rw [sigma_val_eq hrelB]⟩
      | loopI | outer _ | add _ _ | shlConst _ _ | cmpU _ _ | other =>
        exact evalSymOp_push_other hm _ hwp
          (by dsimp only [evalSymOp, evalSymOp1]; rw [dite_eq_left rfl, hsb]; rfl)
    · exact hNone hwp (by dsimp only [evalSymOp1]; rw [dite_eq_right ht])
  | cmp o t m h =>
    subst h; rcases args with ⟨a, b, ⟨⟩⟩; rcases valArgs with ⟨va, vb, ⟨⟩⟩
    obtain ⟨hda, hdb⟩ := denoteArgs_pair_some hargs
    by_cases ht : t = i64
    · subst ht; rw [OpCode.wp_cmp _ _ rfl] at hwp
      dsimp only [liftCmp, vals, Arg.val, i64, Ty.hasFloat] at hwp
      refine ⟨(o.evalBits va.val vb.val, ()), hwp, ?_⟩
      dsimp only [evalSymOp, evalSymOp1]; rw [dite_eq_left rfl, pushTup_singleton (t := i64.mask)]
      exact symEnvMatch_push1 hm
        (evalSymCmp_correct o (argToSym64_correct hm a hda) (argToSym64_correct hm b hdb))
    · exact hNone hwp (by dsimp only [evalSymOp1]; rw [dite_eq_right ht])
  | _ => exact hNone hwp rfl

private theorem checkJump0Inc1_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {vsOuter : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    {JLoop : Cont [i64]} (cont : TFlat rs) :
    ∀ {vsLocal : List ((t : Ty) × Val t)} {env : Array Sym64} {iVal : BitVec 64} {m : Mem 64},
      checkJump0Inc1 env cont = true →
      SymEnvMatch vsOuter iVal vsLocal env →
      wp Γ Q X
        (denote Val Cont cont (vsLocal ++ ⟨i64, iVal⟩ :: vsOuter) (⟨[i64], JLoop⟩ :: ls)) m →
      JLoop (iVal + 1#64, ()) m := by
  cases cont with
  | let_ op k =>
    intro vsLocal env iVal m hChk hm hwp
    dsimp only [checkJump0Inc1] at hChk
    rw [Bool.and_eq_true] at hChk
    rw [denote_let_eq] at hwp
    cases hda : denoteArgs (vsLocal ++ ⟨i64, iVal⟩ :: vsOuter) op.args with
    | none => rw [hda] at hwp; dsimp only at hwp; exact False.elim (wp_hlt_false hwp)
    | some valArgs =>
      rw [hda] at hwp; dsimp only [Op.wp] at hwp; rw [wp_let] at hwp
      obtain ⟨res, hP, hm'⟩ := evalSymOp_wp hm op hda hwp
      rw [pushTup_append_assoc] at hP
      exact checkJump0Inc1_wp k hChk.2 hm' hP
  | jump j args =>
    intro vsLocal env iVal m hChk hm hwp
    unfold checkJump0Inc1 at hChk
    split at hChk
    · rename_i heq; cases heq
    · rename_i nextArg heq
      cases heq
      rw [denote_jump_eq, denoteArgs_singleton_eq] at hwp
      have hL : lookupL (⟨[i64], JLoop⟩ :: ls) [i64] 0 = some JLoop := by
        dsimp only [lookupL]; rw [listGet?_cons_zero_eq]; dsimp only; rw [castListTy_self]
      cases hda : denoteArg (vsLocal ++ ⟨i64, iVal⟩ :: vsOuter) nextArg with
      | none => rw [hL, hda] at hwp; dsimp only at hwp; exact False.elim (wp_hlt_false hwp)
      | some nextA =>
        rw [hL, hda] at hwp; dsimp only at hwp; rw [wp_jump] at hwp
        dsimp only [vals] at hwp
        have hNext := matchInc1_correct (argToSym64_correct hm nextArg hda) hChk
        have hv : nextA.val = iVal + 1#64 := sigma_val_eq hNext
        rw [hv] at hwp; exact hwp
    · cases hChk
  | load _ _ _ | store _ _ _ | call _ _ _ _ | jnz _ _ _ | ret _ | exit _ _ | hlt | group _ _ =>
    intro _ _ _ _ hChk _ _; cases hChk

private theorem matchBodyTail_bound_eq {rs : List Ty} {isLt : Bool} {bound : Arg K i64} :
    ∀ (cont : TFlat rs) {env : Array Sym64} {spec : FillSpec},
      matchBodyTail env isLt bound cont = some spec → spec.isLt = isLt ∧ spec.bound = bound
  | .let_ op k, env, spec, hm => by
    dsimp only [matchBodyTail] at hm
    by_cases hp : isTotalPureOp op.code = true
    · rw [ite_eq_left hp] at hm; exact matchBodyTail_bound_eq k hm
    · rw [ite_eq_right hp] at hm; cases hm
  | .store valArg addrArg cont, env, spec, hm => by
    dsimp only [matchBodyTail] at hm
    cases valArg with
    | var _ => cases hm
    | imm v =>
      cases hSp : splatVal64 v with
      | none => simp [hSp] at hm
      | some sf =>
        cases hA : matchAddr sf.1 (argToSym64 env addrArg) with
        | none => simp [hSp, hA] at hm
        | some bo =>
          simp only [hSp, hA] at hm; split at hm
          · cases hm; exact ⟨rfl, rfl⟩
          · cases hm
  | .load _ _ _, _, _, hm | .call _ _ _ _, _, _, hm | .jnz _ _ _, _, _, hm |
    .jump _ _, _, _, hm | .ret _, _, _, hm | .exit _ _, _, _, hm | .hlt, _, _, hm |
    .group _ _, _, _, hm => by dsimp only [matchBodyTail] at hm; cases hm

private theorem matchBodyTail_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {vsOuter : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    {JLoop : Cont [i64]} {isLt : Bool} {bound : Arg K i64} :
    ∀ (cont : TFlat rs) {env : Array Sym64} {spec : FillSpec},
      matchBodyTail env isLt bound cont = some spec →
      ∃ (t_atom : Ty) (fillAtom : Val t_atom),
        splatVal64 fillAtom = some (spec.shift, spec.fill64) ∧
        ∀ (vsLocal : List ((t : Ty) × Val t)) (iVal : BitVec 64) (m : Mem 64),
          SymEnvMatch vsOuter iVal vsLocal env →
          wp Γ Q X
            (denote Val Cont cont (vsLocal ++ ⟨i64, iVal⟩ :: vsOuter) (⟨[i64], JLoop⟩ :: ls))
            m →
          ∀ (baseA : Arg Val i64) (oVal : BitVec 64),
            denoteArg vsOuter spec.base = some baseA →
            offVal vsOuter spec.off? = some oVal →
            storeOk m t_atom (baseA.val + ((iVal + oVal) <<< spec.shift)) ∧
            JLoop (iVal + 1#64, ())
              (storeMem m t_atom (baseA.val + ((iVal + oVal) <<< spec.shift)) fillAtom)
  | .let_ op k, env, spec, hm => by
    dsimp only [matchBodyTail] at hm
    by_cases hPure : isTotalPureOp op.code = true
    · rw [ite_eq_left hPure] at hm
      obtain ⟨t_atom, fillAtom, hSplat, hk⟩ := matchBodyTail_spec k hm
      refine ⟨t_atom, fillAtom, hSplat, fun vsLocal iVal m hEnv hwp baseA oVal hdB hdO => ?_⟩
      rw [denote_let_eq] at hwp
      cases hda : denoteArgs (vsLocal ++ ⟨i64, iVal⟩ :: vsOuter) op.args with
      | none => rw [hda] at hwp; dsimp only at hwp; exact False.elim (wp_hlt_false hwp)
      | some valArgs =>
        rw [hda] at hwp; dsimp only [Op.wp] at hwp; rw [wp_let] at hwp
        obtain ⟨res, hP, hm'⟩ := evalSymOp_wp hEnv op hda hwp
        rw [pushTup_append_assoc] at hP
        exact hk (pushTup res vsLocal) iVal m hm' hP baseA oVal hdB hdO
    · rw [ite_eq_right hPure] at hm; cases hm
  | .store (t := t_atom) valArg addrArg cont, env, spec, hm => by
    dsimp only [matchBodyTail] at hm
    cases valArg with
    | var _ => cases hm
    | imm fillAtom =>
      dsimp only at hm
      cases hSp : splatVal64 fillAtom with
      | none => simp [hSp] at hm
      | some sf =>
        rcases sf with ⟨sh, f64⟩
        cases hAddr : matchAddr sh (argToSym64 env addrArg) with
        | none => simp [hSp, hAddr] at hm
        | some bo =>
          rcases bo with ⟨base, off?⟩; simp only [hSp, hAddr] at hm
          by_cases hChk : checkJump0Inc1 env cont = true
          · rw [ite_eq_left hChk] at hm; cases hm
            refine ⟨t_atom, fillAtom, hSp, fun vsLocal iVal m hEnv hwp baseA oVal hdB hdO => ?_⟩
            rw [denote_store_eq] at hwp
            have hdv : denoteArg (vsLocal ++ ⟨i64, iVal⟩ :: vsOuter) (.imm fillAtom) =
                some (.imm fillAtom) := rfl
            cases hda : denoteArg (vsLocal ++ ⟨i64, iVal⟩ :: vsOuter) addrArg with
            | none => exact absurd (by rw [hdv, hda] at hwp; exact hwp) wp_hlt_false
            | some addrA =>
              rw [hdv, hda] at hwp; dsimp only at hwp; rw [wp_store] at hwp
              obtain ⟨baseA', oVal', hdB', hdO', hEqAddr⟩ :=
                matchAddr_correct (argToSym64_correct hEnv addrArg hda) hAddr
              rw [hdB] at hdB'; rw [hdO] at hdO'; cases hdB'; cases hdO'
              have hAddrVal := sigma_val_eq hEqAddr
              exact ⟨hAddrVal ▸ hwp.1, checkJump0Inc1_wp cont hChk hEnv (hAddrVal ▸ hwp.2)⟩
          · rw [ite_eq_right hChk] at hm; cases hm
  | .load _ _ _, _, _, hm | .call _ _ _ _, _, _, hm | .jnz _ _ _, _, _, hm |
    .jump _ _, _, _, hm | .ret _, _, _, hm | .exit _ _, _, _, hm | .hlt, _, _, hm |
    .group _ _, _, _, hm => by dsimp only [matchBodyTail] at hm; cases hm

private theorem matchFillBody_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {vsOuter : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    {JLoop : Cont [i64]} :
    ∀ (body : TFlat rs) {env : Array Sym64} {spec : FillSpec},
      matchFillBody env body = some spec →
      ∃ (t_atom : Ty) (fillAtom : Val t_atom),
        splatVal64 fillAtom = some (spec.shift, spec.fill64) ∧
        ∀ (vsLocal : List ((t : Ty) × Val t)) (iVal : BitVec 64) (m : Mem 64),
          SymEnvMatch vsOuter iVal vsLocal env →
          wp Γ Q X (denote Val Cont body (vsLocal ++ ⟨i64, iVal⟩ :: vsOuter)
            (⟨[i64], JLoop⟩ :: ls)) m →
          ∀ (bndA baseA : Arg Val i64) (oVal : BitVec 64),
            denoteArg vsOuter spec.bound = some bndA → denoteArg vsOuter spec.base = some baseA →
            offVal vsOuter spec.off? = some oVal →
            (if spec.isLt then decide (iVal < bndA.val) else decide (iVal ≤ bndA.val)) = true →
            storeOk m t_atom (baseA.val + ((iVal + oVal) <<< spec.shift)) ∧
            JLoop (iVal + 1#64, ())
              (storeMem m t_atom (baseA.val + ((iVal + oVal) <<< spec.shift)) fillAtom)
  | .let_ op k, env, spec, hm => by
    dsimp only [matchFillBody] at hm
    by_cases hPure : isTotalPureOp op.code = true
    · rw [ite_eq_left hPure] at hm
      obtain ⟨t_atom, fillAtom, hSplat, hk⟩ := matchFillBody_spec k hm
      refine ⟨t_atom, fillAtom, hSplat,
        fun vsLocal iVal m hEnv hwp bndA baseA oVal hBnd hBs hO hC => ?_⟩
      rw [denote_let_eq] at hwp
      cases hda : denoteArgs (vsLocal ++ ⟨i64, iVal⟩ :: vsOuter) op.args with
      | none => exact absurd (by rw [hda] at hwp; exact hwp) wp_hlt_false
      | some valArgs =>
        rw [hda] at hwp; dsimp only [Op.wp] at hwp; rw [wp_let] at hwp
        obtain ⟨res, hP, hm'⟩ := evalSymOp_wp hEnv op hda hwp
        rw [pushTup_append_assoc] at hP
        exact hk (pushTup res vsLocal) iVal m hm' hP bndA baseA oVal hBnd hBs hO hC
    · rw [ite_eq_right hPure] at hm; cases hm
  | .jnz c t e, env, spec, hm => by
    dsimp only [matchFillBody] at hm
    cases hc : argToSym64 env c with
    | cmpU isLt bnd =>
      rw [hc] at hm; dsimp only at hm
      obtain ⟨hLtEq, hBndEq⟩ := matchBodyTail_bound_eq t hm
      obtain ⟨t_atom, fillAtom, hSplat, ht⟩ := matchBodyTail_spec (Γ := Γ) (Q := Q) (X := X) t hm
      refine ⟨t_atom, fillAtom, hSplat,
        fun vsLocal iVal m hEnv hwp bndA baseA oVal hBnd hBs hO hC => ?_⟩
      rw [denote_jnz_eq] at hwp
      cases hdc : denoteArg (vsLocal ++ ⟨i64, iVal⟩ :: vsOuter) c with
      | none => exact absurd (by rw [hdc] at hwp; exact hwp) wp_hlt_false
      | some cA =>
        rw [hdc] at hwp; dsimp only at hwp; rw [wp_jnz] at hwp
        have hRel := argToSym64_correct hEnv c hdc; rw [hc] at hRel
        rcases hRel with ⟨bndA', hBnd', hCEq⟩
        rw [hBndEq] at hBnd; rw [hBnd] at hBnd'; cases hBnd'
        exact ht vsLocal iVal m hEnv
          (hwp.1 (by rw [sigma_val_eq hCEq, ← hLtEq]; exact hC)) baseA oVal hBs hO
    | loopI | outer _ | const _ | add _ _ | shlConst _ _ | other => rw [hc] at hm; cases hm
  | .load _ _ _, _, _, hm | .store _ _ _, _, _, hm | .call _ _ _ _, _, _, hm |
    .jump _ _, _, _, hm | .ret _, _, _, hm | .exit _ _, _, _, hm | .hlt, _, _, hm |
    .group _ _, _, _, hm => by dsimp only [matchFillBody] at hm; cases hm

private theorem liftOp_cmp_wp {o : CmpOp} {a b : Arg Val i64} {K : Tup Val [.bool] → Prop}
    (hK : K (o.evalBits a.val b.val, ())) :
    OpCode.wp (OpCode.cmp o i64 .bool rfl) (vals (a, b, ())) K := by
  rw [OpCode.wp_cmp _ _ rfl]
  dsimp only [liftCmp, vals, Arg.val, Ty.hasFloat]
  cases a <;> cases b <;> exact hK

private theorem liftOp_sub_wp {a : Arg Val i64} {y : BitVec 64} {K : Tup Val [i64] → Prop}
    (hK : K (a.val - y, ())) :
    OpCode.wp (OpCode.sub i64) (vals (a, (.var y : Arg Val i64), ())) K := by
  rw [OpCode.wp_sub]; dsimp only [lift2, vals, Arg.val, i64, Ty.hasFloat]; cases a <;> exact hK
private theorem liftOp_add_wp {x : BitVec 64} {b : Arg Val i64} {K : Tup Val [i64] → Prop}
    (hK : K (x + b.val, ())) :
    OpCode.wp (OpCode.add i64) (vals ((.var x : Arg Val i64), b, ())) K := by
  rw [OpCode.wp_add]; dsimp only [lift2, vals, Arg.val, i64, Ty.hasFloat]; cases b <;> exact hK
private theorem liftOp_shl_wp {a : Arg Val i64} {s : BitVec 64} {K : Tup Val [i64] → Prop}
    (hK : K (a.val <<< (s.toNat % 64), ())) :
    OpCode.wp (OpCode.shl i64) (vals (a, (.imm s : Arg Val i64), ())) K := by
  rw [OpCode.wp_shl]; dsimp only [lift2, vals, Arg.val, i64, Ty.hasFloat]; cases a <;> exact hK
private theorem denoteArg_var0 {V : Ty → Type} {t : Ty} (v : V t) (vs : List ((t' : Ty) × V t')) :
    denoteArg (⟨t, v⟩ :: vs) (.var 0 : Arg K t) = some (.var v) := by
  dsimp only [denoteArg, lookupV]; rw [listGet?_cons_zero_eq]; dsimp only
  rw [PassFlatKit.castTy_self]
private theorem lookupL_0 {L : List Ty → Type} {ts : List Ty} (l : L ts)
    (ls : List ((ts' : List Ty) × L ts')) : lookupL (⟨ts, l⟩ :: ls) ts 0 = some l := by
  dsimp only [lookupL]; rw [listGet?_cons_zero_eq]; dsimp only; exact castListTy_self ts l
private theorem lookupL_1 {L : List Ty → Type} {ts ts0 : List Ty} (l0 : L ts0) (l : L ts)
    (ls : List ((ts' : List Ty) × L ts')) :
    lookupL (⟨ts0, l0⟩ :: ⟨ts, l⟩ :: ls) ts 1 = some l := by
  dsimp only [lookupL, listGet?]; exact castListTy_self ts l

private theorem widenFillSingle_wp {Γ : Env} {rs ts0 : List Ty} {Q : Post rs} {X : XPost}
    {GOuter : List Ty} {DOuter : List (List Ty)}
    {vs : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    (hCtxV : CtxTypes GOuter vs) (_hCtxL : CtxTypes DOuter ls)
    {unrollN : Nat} {body k res : TFlat rs} {m : Mem 64}
    (hwf : TFlat.wfCheck GOuter DOuter (.group (@TBlocks.cons rs ts0 [] body .nil) k) = true)
    (hw : widenFillSingle unrollN ts0 body k = some res)
    (hwp : wp Γ Q X (denote Val Cont (.group (@TBlocks.cons rs ts0 [] body .nil) k) vs ls) m) :
    wp Γ Q X (denote Val Cont res vs ls) m := by
  obtain ⟨hunroll1, hunroll64, rfl, initArg, spec, rfl, hmFill, rfl⟩ :=
    widenFillSingle_eq_some hw
  rw [wfCheck_group_eq, wfCheckB_cons_eq, wfCheckB_nil_eq, Bool.and_true, Bool.and_eq_true,
    wfCheck_jump_eq, Bool.and_eq_true] at hwf
  have hBodyWf : TFlat.wfCheck ([] ++ i64 :: GOuter) ([i64] :: DOuter) body = true := hwf.1
  have hSpec := matchFillBody_wf body ⟨rfl, fun _ hs => by cases hs⟩ hBodyWf hmFill
  obtain ⟨initA, hdInit⟩ := Option.isSome_iff_exists.mp (denoteArg_isSome_of_checkArg hCtxV
    (by simpa [pushTypes, checkArgs] using hwf.2.2 : checkArg GOuter i64 initArg = true))
  obtain ⟨bndA, hdBnd⟩ := Option.isSome_iff_exists.mp (denoteArg_isSome_of_checkArg hCtxV hSpec.1)
  obtain ⟨baseA, hdBase⟩ :=
    Option.isSome_iff_exists.mp (denoteArg_isSome_of_checkArg hCtxV hSpec.2.1)
  obtain ⟨oVal, hdOff⟩ : ∃ oVal : BitVec 64, offVal vs spec.off? = some oVal := by
    cases hOff : spec.off? with
    | none => exact ⟨0#64, rfl⟩
    | some off =>
      have hOffWf := hSpec.2.2.1; rw [hOff, Option.all_some] at hOffWf
      obtain ⟨offA, hdOffA⟩ :=
        Option.isSome_iff_exists.mp (denoteArg_isSome_of_checkArg hCtxV hOffWf)
      exact ⟨offA.val, by simp [offVal, hdOffA]⟩
  have hG := ctx_diagV_of_vs (vs := vs); have hD := ctx_monoD_of_ls (ls := ls)
  have hRelV := ctxRel_refl_vs (vs := vs); have hRelL := ctxRel_refl_ls (ls := ls)
  let bodies : Tup Cont [[i64]] → Blocks Val Cont rs [[i64]] := fun Js =>
    denoteB Val Cont (.cons (ts := [i64]) body .nil) vs (pushTup Js ls)
  have hWfB (Js₁ Js₂ : Tup Cont [[i64]]) :
      WfB (List.map (fun ⟨t, v⟩ => ⟨t, (v, v)⟩) vs)
        (Js₁.zip Js₂ ++ List.map (fun ⟨ts, l⟩ => ⟨ts, (l, l)⟩) ls) (bodies Js₁) (bodies Js₂) :=
    denoteB_wf (.cons (ts := [i64]) body .nil) hRelV (ctxRel_pushTup Js₁ Js₂ hRelL)
  rw [denote_group_eq] at hwp ⊢
  rw [wp_group_iff hG hD hWfB (fun Js₁ Js₂ =>
    denote_wf (.jump (ts := [i64]) 0 (initArg, ())) hRelV (ctxRel_pushTup Js₁ Js₂ hRelL))] at hwp
  rw [wp_group_iff hG hD hWfB (fun Js₁ Js₂ =>
    denote_wf (mkWideWrapper spec unrollN initArg) hRelV (ctxRel_pushTup Js₁ Js₂ hRelL))]
  let JLoop : Cont [i64] := (lfp Γ Q X bodies).fst
  have hPushJs : pushTup (lfp Γ Q X bodies) ls = ⟨[i64], JLoop⟩ :: ls := by
    cases hEq : lfp Γ Q X bodies with
    | mk jl u => cases u; dsimp only [JLoop]; rw [hEq]; rfl
  have hJInit : JLoop (initA.val, ()) m := by
    rw [hPushJs, denote_jump_eq, denoteArgs_singleton_eq, lookupL_0, hdInit] at hwp
    simpa [wp_jump, vals, Arg.val] using hwp
  have hBodyStep (i' : BitVec 64) (m' : Mem 64) (hJi : JLoop (i', ()) m') :
      wp Γ Q X (denote Val Cont body (⟨i64, i'⟩ :: vs) (⟨[i64], JLoop⟩ :: ls)) m' := by
    have hUnr := lfp_unroll_single hG hD hWfB (i', ()) m' hJi
    change wp Γ Q X ((denoteB Val Cont (.cons (ts := [i64]) body .nil) vs
      (pushTup (lfp Γ Q X bodies) ls)).get Member.here (i', ())) m' at hUnr
    rwa [hPushJs, denoteB_cons_eq] at hUnr
  obtain ⟨t_atom, fillAtom, hSplat, hBodyMatched⟩ := matchFillBody_spec (Γ := Γ) (Q := Q) (X := X)
    (vsOuter := vs) (ls := ls) (JLoop := JLoop) body hmFill
  obtain ⟨hShLe, hBytesEq, hK64Mul, hWideBytesEq⟩ := splatVal64_spec fillAtom hSplat
  have hBytesPos : 0 < t_atom.bytes := by rw [hBytesEq]; exact Nat.pow_pos (by omega)
  have hScalarStep (i' : BitVec 64) (m' : Mem 64) (hiLt : i'.toNat < bndA.val.toNat)
      (hJi : JLoop (i', ()) m') :
      storeOk m' t_atom (baseA.val + ((i' + oVal) <<< spec.shift)) ∧
      JLoop (i' + 1#64, ())
        (storeMem m' t_atom (baseA.val + ((i' + oVal) <<< spec.shift)) fillAtom) := by
    have hLe : i'.toNat ≤ bndA.val.toNat := Nat.le_of_lt hiLt
    have hCmpT : (if spec.isLt then decide (i' < bndA.val) else decide (i' ≤ bndA.val)) = true := by
      cases spec.isLt <;> simp [BitVec.lt_def, BitVec.le_def, hiLt, hLe]
    exact hBodyMatched [] i' m' symEnvMatch_empty (hBodyStep i' m' hJi) bndA baseA oVal
      hdBnd hdBase hdOff hCmpT
  rw [hPushJs]; dsimp only [mkWideWrapper]; rw [denote_group_eq]
  let wb := mkWideBody (rs := rs) spec unrollN
  let k64 := 8 >>> spec.shift; let stepK := unrollN * k64
  let cmpOp := if spec.isLt = true then CmpOp.ult else CmpOp.ule
  let kCheck : TFlat rs := TFlat.let_ (op2 (OpCode.cmp cmpOp (Ty.bits 64) Ty.bool rfl) initArg
    spec.bound) (TFlat.jnz (.var 0) (.jump (ts := [i64]) 0 (tArgShift 1 initArg, ()))
      (.jump (ts := [i64]) 1 (tArgShift 1 initArg, ())))
  have hEqGroup :
      Expr.group (sig := [[i64]]) (fun Js => denoteB Val Cont (.cons (ts := [i64]) wb .nil) vs
          (pushTup Js (⟨[i64], JLoop⟩ :: ls)))
        (fun Js => denote Val Cont kCheck vs (pushTup Js (⟨[i64], JLoop⟩ :: ls))) =
      Expr.group (sig := [[i64]])
        (fun Js : Tup Cont [[i64]] => Blocks.cons
          (fun xs => denote Val Cont wb (pushTup xs vs) (⟨[i64], Js.fst⟩ :: ⟨[i64], JLoop⟩ :: ls))
          Blocks.nil)
        (fun Js => denote Val Cont kCheck vs (⟨[i64], Js.fst⟩ :: ⟨[i64], JLoop⟩ :: ls)) := by
    congr 1 <;> funext Js <;> rcases Js with ⟨jw, ⟨⟩⟩ <;>
      · dsimp only [pushTup]; try rw [denoteB_cons_eq, denoteB_nil_eq]; rfl
  rw [hEqGroup]
  let Inv : Nat → Tup Val [i64] → Mem 64 → Prop := fun n xs m' =>
    xs.fst.toNat ≤ bndA.val.toNat ∧ n = bndA.val.toNat - xs.fst.toNat ∧ JLoop xs m'
  refine wp_loop
    (fun JWide xs =>
      denote Val Cont wb (pushTup xs vs) (⟨[i64], JWide⟩ :: ⟨[i64], JLoop⟩ :: ls))
    (fun JWide => denote Val Cont kCheck vs (⟨[i64], JWide⟩ :: ⟨[i64], JLoop⟩ :: ls))
    Inv ?_ ?_
  · intro JWide n xs m' ih ⟨hLe, hn, hJL⟩
    rcases xs with ⟨i', ⟨⟩⟩
    dsimp only at hLe hn hJL
    subst hn
    dsimp only [wb, mkWideBody, op2]
    rw [denote_let_eq, denoteArgs_pair_eq, pushTup_singleton]
    have hBnd1 : denoteArg (⟨i64, i'⟩ :: vs) (tArgShift 1 spec.bound) = some bndA := by
      have hSh := denoteArg_shiftArgAbove (vsPre := []) [⟨i64, i'⟩] vs spec.bound
      simpa [tArgShift] using hSh.trans hdBnd
    rw [hBnd1, denoteArg_var0]
    dsimp only
    rw [wp_let]; dsimp only [Op.wp]
    refine liftOp_sub_wp (a := bndA) (y := i') ?_
    let rem := bndA.val - i'
    rw [denote_let_eq, denoteArgs_pair_eq, pushTup_singleton (t := i64), denoteArg_var0]
    change wp Γ Q X (Expr.let_ (op2 (OpCode.cmp .uge (Ty.bits 64) .bool rfl)
      (.var rem) (.imm (BitVec.ofNat 64 stepK))) _) m'
    rw [wp_let]; dsimp only [Op.wp]
    refine liftOp_cmp_wp (o := .uge) (a := (Arg.var rem : Arg Val i64))
      (b := (Arg.imm (BitVec.ofNat 64 stepK) : Arg Val i64)) ?_
    rw [pushTup_singleton (t := Ty.bool)]
    let cStep := CmpOp.uge.evalBits rem (BitVec.ofNat 64 stepK)
    rw [show CmpOp.uge.evalBits (Arg.var rem : Arg Val i64).val
        (Arg.imm (BitVec.ofNat 64 stepK) : Arg Val i64).val = cStep from rfl,
      show bndA.val - i' = rem from rfl, denote_jnz_eq, denoteArg_var0]
    dsimp only; rw [wp_jnz, show (Arg.var cStep : Arg Val Ty.bool).val = cStep from rfl]
    constructor
    · intro hcTrue
      have hK64Bnd : 1 ≤ k64 ∧ k64 ≤ 8 := by
        dsimp only [k64]
        have : spec.shift = 0 ∨ spec.shift = 1 ∨ spec.shift = 2 ∨ spec.shift = 3 := by omega
        rcases this with h | h | h | h <;> simp [h]
      have hStepPos : 1 ≤ stepK :=
        Nat.le_trans hunroll1 (Nat.le_mul_of_pos_right unrollN hK64Bnd.1)
      have hStep512 : stepK ≤ 512 := Nat.mul_le_mul hunroll64 hK64Bnd.2
      have hStep64 : stepK < 2 ^ 64 := by omega
      have hRemGe : stepK ≤ bndA.val.toNat - i'.toNat := by
        have hc' : (BitVec.ofNat 64 stepK).toNat ≤ rem.toNat := by
          dsimp only [cStep, CmpOp.evalBits] at hcTrue
          exact of_decide_eq_true (by unfold BitVec.ule at hcTrue; exact hcTrue)
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hStep64,
          BitVec.toNat_sub_of_le (BitVec.le_def.mpr hLe)] at hc'
      have hMulLe64 : stepK * t_atom.bytes ≤ 2 ^ 64 := by
        have : stepK * t_atom.bytes = unrollN * (k64 * t_atom.bytes) := Nat.mul_assoc _ _ _
        rw [this, hK64Mul]; omega
      obtain ⟨hOkSc, hJPostSc⟩ := runScalarMem_step hShLe hBytesEq hBytesPos hScalarStep
        i' hLe m' hJL stepK hRemGe hMulLe64
      let ptr0 := baseA.val + ((i' + oVal) <<< spec.shift)
      have hOkWide := storeOk_split_8 m' t_atom ptr0 unrollN k64 hK64Mul hBytesPos hOkSc
      have hWidePost : JWide (i' + BitVec.ofNat 64 stepK, ())
          (m'.storeBytes ptr0
            (List.replicate unrollN (Int.toBytes 8 spec.fill64.toInt)).flatten) := by
        rw [show (List.replicate unrollN (Int.toBytes 8 spec.fill64.toInt)).flatten =
          (List.replicate stepK (Int.toBytes t_atom.bytes
            (BitVec.setWidth (8 * t_atom.bytes) (toBits t_atom fillAtom)).toInt)).flatten by
          rw [hWideBytesEq, flatten_replicate_flatten]]
        have hSumLe : i'.toNat + stepK ≤ bndA.val.toNat := by omega
        have hAddNat : (i' + BitVec.ofNat 64 stepK).toNat = i'.toNat + stepK := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hStep64,
            Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hSumLe bndA.val.isLt)]
        exact ih (bndA.val.toNat - (i'.toNat + stepK))
          (i' + BitVec.ofNat 64 stepK, ()) _ (by omega)
          ⟨by dsimp only; rw [hAddNat]; exact hSumLe, by dsimp only; rw [hAddNat], hJPostSc⟩
      have runWithShift (vsL : List ((t : Ty) × Val t)) (idxVar : Arg K i64) (idxA : Arg Val i64)
          (hL1 : vsL.length ≥ 1) (hDIdx : denoteArg (vsL ++ vs) idxVar = some idxA)
          (hDIdxVal : idxA.val = i' + oVal)
          (hIL : lookupV (vsL ++ vs) i64 (vsL.length - 1) = some i') :
          wp Γ Q X (denote Val Cont
            (if (spec.shift == 0) = true then
              TFlat.let_ (op2 (OpCode.add i64) (tArgShift vsL.length spec.base) idxVar)
                (mkStoreChain spec.fill64 stepK unrollN vsL.length)
             else
              TFlat.let_ (op2 (OpCode.shl i64) idxVar (.imm (BitVec.ofNat 64 spec.shift)))
                (TFlat.let_ (op2 (OpCode.add i64) (tArgShift (vsL.length + 1) spec.base) (.var 0))
                  (mkStoreChain spec.fill64 stepK unrollN (vsL.length + 1))))
            (vsL ++ vs) (⟨[i64], JWide⟩ :: ⟨[i64], JLoop⟩ :: ls)) m' := by
        by_cases hS0 : spec.shift = 0
        · rw [ite_eq_left (by simp [hS0])]
          exact wideBody_withBase_wp (ls := ⟨[i64], JLoop⟩ :: ls) hunroll1 hunroll64 hL1 hdBase
            hDIdx (by rw [hS0, BitVec.shiftLeft_zero, hDIdxVal]) hIL hOkWide hWidePost
        · rw [ite_eq_right (beq_false_of_ne hS0 ▸ Bool.false_ne_true)]
          dsimp only [op2]; rw [denote_let_eq, denoteArgs_pair_eq, hDIdx]
          change wp Γ Q X (Expr.let_ (op2 (OpCode.shl i64) idxA
            (.imm (BitVec.ofNat 64 spec.shift))) _) m'
          rw [wp_let]; dsimp only [Op.wp]
          refine liftOp_shl_wp (a := idxA) (s := BitVec.ofNat 64 spec.shift) ?_
          rw [pushTup_singleton (t := i64)]
          have hMod : (BitVec.ofNat 64 spec.shift).toNat % 64 = spec.shift := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          let vsL' := ⟨i64, idxA.val <<< ((BitVec.ofNat 64 spec.shift).toNat % 64)⟩ :: vsL
          have hD0 : denoteArg (vsL' ++ vs) (.var 0 : Arg K i64) =
              some (.var (idxA.val <<< ((BitVec.ofNat 64 spec.shift).toNat % 64))) := by
            dsimp only [vsL']; rw [List.cons_append]; exact denoteArg_var0 _ _
          have hI' : lookupV (vsL' ++ vs) i64 (vsL'.length - 1) = some i' := by
            have hSub : vsL.length = (vsL.length - 1) + 1 := by omega
            change lookupV (⟨i64, _⟩ :: (vsL ++ vs)) i64 vsL.length = some i'
            rw [hSub]; exact hIL
          exact wideBody_withBase_wp (ls := ⟨[i64], JLoop⟩ :: ls) (vsLocal := vsL')
            (idxA := .var (idxA.val <<< ((BitVec.ofNat 64 spec.shift).toNat % 64)))
            hunroll1 hunroll64 (Nat.succ_pos _) hdBase hD0
            (by dsimp only [Arg.val] at hDIdxVal ⊢; rw [hDIdxVal, hMod]) hI' hOkWide hWidePost
      let vsL0 : List ((t : Ty) × Val t) := [⟨Ty.bool, cStep⟩, ⟨i64, rem⟩, ⟨i64, i'⟩]
      cases hOff : spec.off? with
      | none =>
        have hOVar : oVal = 0#64 := by
          dsimp only [offVal] at hdOff; rw [hOff] at hdOff; cases hdOff; rfl
        exact runWithShift vsL0 (.var 2) (.var i') (Nat.succ_pos _) rfl
          (by dsimp only [Arg.val]; rw [hOVar, BitVec.add_zero]) rfl
      | some off =>
        have hOffArg : ∃ aOff, denoteArg vs off = some aOff ∧ aOff.val = oVal := by
          dsimp only [offVal] at hdOff; rw [hOff] at hdOff; exact Option.map_eq_some_iff.mp hdOff
        obtain ⟨aOff, hdOffA, haOffVal⟩ := hOffArg
        rw [denote_let_eq, denoteArgs_pair_eq]
        have hOffSh : denoteArg (vsL0 ++ vs) (tArgShift 3 off) = some aOff := by
          simpa [vsL0, tArgShift] using
            (denoteArg_shiftArgAbove (vsPre := []) vsL0 vs off).trans hdOffA
        have hV2 : denoteArg (vsL0 ++ vs) (.var 2 : Arg K i64) = some (.var i') := rfl
        rw [show (⟨Ty.bool, cStep⟩ :: ⟨i64, rem⟩ :: ⟨i64, i'⟩ :: vs) = vsL0 ++ vs from rfl,
          hV2, hOffSh]; dsimp only
        rw [wp_let]; dsimp only [Op.wp]
        refine liftOp_add_wp (x := i') (b := aOff) ?_
        rw [pushTup_singleton (t := i64), haOffVal]
        exact runWithShift (⟨i64, i' + oVal⟩ :: vsL0) (.var 0) (.var (i' + oVal))
          (Nat.succ_pos _) rfl rfl rfl
    · intro _
      have hV2 : denoteArg (⟨Ty.bool, cStep⟩ :: ⟨i64, rem⟩ :: ⟨i64, i'⟩ :: vs)
          (.var 2 : Arg K i64) = some (.var i') := rfl
      rw [denote_jump_eq, denoteArgs_singleton_eq, lookupL_1, hV2]
      dsimp only; rw [wp_jump]; exact hJL
  · intro JWide hInv
    dsimp only [kCheck, op2]; rw [denote_let_eq, denoteArgs_pair_eq, hdInit, hdBnd]
    dsimp only; rw [wp_let]; dsimp only [Op.wp]
    refine liftOp_cmp_wp (o := cmpOp) (a := initA) (b := bndA) ?_
    rw [pushTup_singleton (t := Ty.bool)]
    let cInit := cmpOp.evalBits initA.val bndA.val
    rw [denote_jnz_eq, denoteArg_var0]; dsimp only
    rw [wp_jnz, show (Arg.var cInit : Arg Val Ty.bool).val = cInit from rfl]
    have hInitSh : denoteArg (⟨Ty.bool, cInit⟩ :: vs) (tArgShift 1 initArg) = some initA := by
      simpa [tArgShift] using
        (denoteArg_shiftArgAbove (vsPre := []) [⟨Ty.bool, cInit⟩] vs initArg).trans hdInit
    have hVals1 : @vals [i64] (initA, ()) = (initA.val, ()) := by cases initA <;> rfl
    constructor
    · intro hcTrue
      rw [denote_jump_eq, denoteArgs_singleton_eq, lookupL_0, hInitSh]; dsimp only
      rw [wp_jump, hVals1]
      have hLe : initA.val.toNat ≤ bndA.val.toNat := by
        dsimp only [cInit, cmpOp] at hcTrue
        cases hIs : spec.isLt <;> rw [hIs] at hcTrue <;> dsimp only [CmpOp.evalBits] at hcTrue
        · exact of_decide_eq_true (by unfold BitVec.ule at hcTrue; exact hcTrue)
        · exact Nat.le_of_lt (of_decide_eq_true (by unfold BitVec.ult at hcTrue; exact hcTrue))
      exact hInv (bndA.val.toNat - initA.val.toNat) (initA.val, ()) m ⟨hLe, rfl, hJInit⟩
    · intro _
      rw [denote_jump_eq, denoteArgs_singleton_eq, lookupL_1, hInitSh]; dsimp only
      rw [wp_jump, hVals1]; exact hJInit

/-! ## Section 5: Full-Function WF, WP, CallsOk & Module Correctness -/

private theorem zpeelTF_let (cfg : ZeroPeelConfig) {rs ts : List Ty} (op : Op K ts) (k : TFlat rs) :
    zpeelTF cfg (.let_ op k) = .let_ op (zpeelTF cfg k) := rfl
private theorem zpeelTF_load (cfg : ZeroPeelConfig) {rs : List Ty} (t : Ty) (a : Arg K i64)
    (k : TFlat rs) : zpeelTF cfg (.load t a k) = .load t a (zpeelTF cfg k) := rfl
private theorem zpeelTF_store (cfg : ZeroPeelConfig) {rs : List Ty} {t : Ty} (v : Arg K t)
    (a : Arg K i64) (k : TFlat rs) : zpeelTF cfg (.store v a k) = .store v a (zpeelTF cfg k) := rfl
private theorem zpeelTF_call (cfg : ZeroPeelConfig) {rs : List Ty} (f : Sym) {as : List Ty}
    (bs : List Ty) (args : Tup (Arg K) as) (k : TFlat rs) :
    zpeelTF cfg (.call f bs args k) = .call f bs args (zpeelTF cfg k) := rfl
private theorem zpeelTF_jnz (cfg : ZeroPeelConfig) {rs : List Ty} (c : Arg K Ty.bool)
    (t e : TFlat rs) : zpeelTF cfg (.jnz c t e) = .jnz c (zpeelTF cfg t) (zpeelTF cfg e) := rfl
private theorem zpeelTF_jump (cfg : ZeroPeelConfig) {rs ts : List Ty} (j : Nat)
    (args : Tup (Arg K) ts) : zpeelTF cfg (.jump j args : TFlat rs) = .jump j args := rfl
private theorem zpeelTF_ret (cfg : ZeroPeelConfig) {rs : List Ty} (vs : Tup (Arg K) rs) :
    zpeelTF cfg (.ret vs) = .ret vs := rfl
private theorem zpeelTF_exit (cfg : ZeroPeelConfig) {rs : List Ty} (f : Sym) {as : List Ty}
    (args : Tup (Arg K) as) : zpeelTF cfg (.exit f args : TFlat rs) = .exit f args := rfl
private theorem zpeelTF_hlt (cfg : ZeroPeelConfig) {rs : List Ty} :
    zpeelTF cfg (.hlt : TFlat rs) = .hlt := rfl
private theorem zpeelBs_nil (cfg : ZeroPeelConfig) {rs : List Ty} :
    zpeelBs cfg (.nil : TBlocks rs []) = .nil := rfl
private theorem zpeelBs_cons (cfg : ZeroPeelConfig) {rs ts : List Ty} {sig : List (List Ty)}
    (b : TFlat rs) (bs : TBlocks rs sig) :
    zpeelBs cfg (.cons (ts := ts) b bs) = .cons (zpeelTF cfg b) (zpeelBs cfg bs) := rfl

private def zpeelGroupWrap (cfg : ZeroPeelConfig) {rs : List Ty}
    {sig : List (List Ty)} (bs' : TBlocks rs sig) (k' : TFlat rs) : TFlat rs :=
  match sig, bs' with
  | [ts0], .cons body .nil =>
    match widenFillSingle cfg.unrollN ts0 body k' with
    | some g => g
    | none =>
      match peelSingle cfg ts0 body k' with
      | some g => g
      | none => .group (sig := [ts0]) (.cons body .nil) k'
  | _, _ => .group bs' k'
private theorem zpeelGroupWrap_nil (cfg : ZeroPeelConfig) {rs : List Ty} (k' : TFlat rs) :
    zpeelGroupWrap cfg .nil k' = .group .nil k' := rfl
private theorem zpeelGroupWrap_cons2 (cfg : ZeroPeelConfig) {rs : List Ty} {ts0 ts1 : List Ty}
    {sig : List (List Ty)} (b0 b1 : TFlat rs) (bs : TBlocks rs sig) (k' : TFlat rs) :
    zpeelGroupWrap cfg (.cons (ts := ts0) b0 (.cons (ts := ts1) b1 bs)) k' =
      .group (sig := ts0 :: ts1 :: sig) (.cons b0 (.cons b1 bs)) k' := rfl
private theorem zpeelGroupWrap_cons_nil (cfg : ZeroPeelConfig) {rs : List Ty}
    (ts0 : List Ty) (body k' : TFlat rs) :
    zpeelGroupWrap cfg (.cons (ts := ts0) body .nil) k' =
      (match widenFillSingle cfg.unrollN ts0 body k' with
      | some g => g | none => match peelSingle cfg ts0 body k' with
        | some g => g | none => .group (sig := [ts0]) (.cons body .nil) k') := rfl

private theorem zpeelTF_group (cfg : ZeroPeelConfig) {rs : List Ty}
    {sig : List (List Ty)} (bs : TBlocks rs sig) (k : TFlat rs) :
    zpeelTF cfg (.group bs k) = zpeelGroupWrap cfg (zpeelBs cfg bs) (zpeelTF cfg k) := by
  cases bs with | nil => rfl | cons _ bs1 => cases bs1 <;> rfl

private theorem zpeelGroupWrap_wf {rs : List Ty} (cfg : ZeroPeelConfig)
    {G : List Ty} {D : List (List Ty)} {sig : List (List Ty)}
    (bs' : TBlocks rs sig) (k' : TFlat rs)
    (hwf : TFlat.wfCheck G D (.group bs' k') = true) :
    TFlat.wfCheck G D (zpeelGroupWrap cfg bs' k') = true := by
  cases bs' with
  | nil => rw [zpeelGroupWrap_nil]; exact hwf
  | @cons ts0 _ body bsNil =>
    cases bsNil with
    | nil =>
      rw [zpeelGroupWrap_cons_nil]
      cases hw : widenFillSingle cfg.unrollN ts0 body k' with
      | some g => exact wfCheck_widenFillSingle hwf hw
      | none =>
        cases hp : peelSingle cfg ts0 body k' with
        | some g =>
          rw [wfCheck_group_eq, wfCheckB_cons_eq, wfCheckB_nil_eq, Bool.and_true,
            Bool.and_eq_true] at hwf
          exact wfCheck_peelSingle hwf.1 hwf.2 hp
        | none => exact hwf
    | cons _ _ => exact hwf

mutual
private theorem wfCheck_zpeelTF (cfg : ZeroPeelConfig) {rs : List Ty} :
    (tf : TFlat rs) → (G : List Ty) → (D : List (List Ty)) →
    tf.wfCheck G D = true → (zpeelTF cfg tf).wfCheck G D = true
  | .let_ _ k, G, D, h => by
    rw [wfCheck_let_eq, Bool.and_eq_true] at h; rw [zpeelTF_let, wfCheck_let_eq, Bool.and_eq_true]
    exact ⟨h.1, wfCheck_zpeelTF cfg k _ D h.2⟩
  | .load t _ k, G, D, h => by
    rw [wfCheck_load_eq, Bool.and_eq_true] at h
    rw [zpeelTF_load, wfCheck_load_eq, Bool.and_eq_true]
    exact ⟨h.1, wfCheck_zpeelTF cfg k (t :: G) D h.2⟩
  | .store _ _ k, G, D, h => by
    rw [wfCheck_store_eq, Bool.and_eq_true] at h
    rw [zpeelTF_store, wfCheck_store_eq, Bool.and_eq_true]
    exact ⟨h.1, wfCheck_zpeelTF cfg k G D h.2⟩
  | .call _ bs _ k, G, D, h => by
    rw [wfCheck_call_eq, Bool.and_eq_true] at h
    rw [zpeelTF_call, wfCheck_call_eq, Bool.and_eq_true]
    exact ⟨h.1, wfCheck_zpeelTF cfg k (pushTypes bs G) D h.2⟩
  | .jnz _ t e, G, D, h => by
    rw [wfCheck_jnz_eq, Bool.and_eq_true, Bool.and_eq_true] at h
    rw [zpeelTF_jnz, wfCheck_jnz_eq, Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨h.1.1, wfCheck_zpeelTF cfg t G D h.1.2⟩, wfCheck_zpeelTF cfg e G D h.2⟩
  | .jump _ _, _, _, h => by rw [zpeelTF_jump]; exact h
  | .ret _, _, _, h => by rw [zpeelTF_ret]; exact h
  | .exit _ _, _, _, h => by rw [zpeelTF_exit]; exact h
  | .hlt, _, _, h => by rw [zpeelTF_hlt]; exact h
  | .group (sig := sig) bs k, G, D, h => by
    rw [wfCheck_group_eq, Bool.and_eq_true] at h; rw [zpeelTF_group]
    refine zpeelGroupWrap_wf cfg _ _ ?_
    rw [wfCheck_group_eq, Bool.and_eq_true]
    exact ⟨wfCheck_zpeelBs cfg bs G _ h.1, wfCheck_zpeelTF cfg k G _ h.2⟩
private theorem wfCheck_zpeelBs (cfg : ZeroPeelConfig) {rs : List Ty} :
    {sig : List (List Ty)} → (bs : TBlocks rs sig) → (G : List Ty) → (D : List (List Ty)) →
    bs.wfCheck G D = true → (zpeelBs cfg bs).wfCheck G D = true
  | _, .nil, _, _, h => by rw [zpeelBs_nil]; exact h
  | ts :: _, .cons b bs, G, D, h => by
    rw [wfCheckB_cons_eq, Bool.and_eq_true] at h
    rw [zpeelBs_cons, wfCheckB_cons_eq, Bool.and_eq_true]
    exact ⟨wfCheck_zpeelTF cfg b (pushTypes ts G) D h.1, wfCheck_zpeelBs cfg bs G D h.2⟩
end

private theorem CtxTypes_pushTup {α : Type} {f : α → Type} :
    ∀ {ts : List α} (xs : Tup f ts) {G : List α} {vs : List ((a : α) × f a)},
      CtxTypes G vs → CtxTypes (pushTypes ts G) (pushTup xs vs)
  | [], _, _, _, h => h
  | _ :: _, (_, xs), _, _, h => CtxTypes_pushTup xs (.cons h)

private def LabelLe :
    List ((ts : List Ty) × Cont ts) → List ((ts : List Ty) × Cont ts) → Prop
  | [], [] => True
  | ⟨ts₁, l₁⟩ :: xs₁, ⟨ts₂, l₂⟩ :: xs₂ =>
    ∃ (h : ts₁ = ts₂), (∀ args m, l₁ args m → l₂ (h ▸ args) m) ∧ LabelLe xs₁ xs₂
  | _, _ => False

private theorem labelLe_refl : ∀ (ls : List ((ts : List Ty) × Cont ts)), LabelLe ls ls
  | [] => trivial
  | ⟨_, _⟩ :: ls => ⟨rfl, fun _ _ h => h, labelLe_refl ls⟩

private theorem labelLe_pushTup :
    ∀ {sig : List (List Ty)} (Js : Tup Cont sig)
      {ls₁ ls₂ : List ((ts : List Ty) × Cont ts)},
      LabelLe ls₁ ls₂ → LabelLe (pushTup Js ls₁) (pushTup Js ls₂)
  | [], _, _, _, h => h
  | _ :: _, (_, Js), _, _, h => labelLe_pushTup Js ⟨rfl, fun _ _ hx => hx, h⟩

private theorem labelLe_pushTup2 :
    ∀ {sig : List (List Ty)} {Js₁ Js₂ : Tup Cont sig}
      {ls₁ ls₂ : List ((ts : List Ty) × Cont ts)},
      (∀ {ts : List Ty} (i : Member ts sig) xs m, Js₁.get i xs m → Js₂.get i xs m) →
      LabelLe ls₁ ls₂ → LabelLe (pushTup Js₁ ls₁) (pushTup Js₂ ls₂)
  | [], _, _, _, _, _, hLs => hLs
  | _ :: _, (_, Js₁), (_, Js₂), _, _, hJs, hLs => by
    dsimp only [pushTup]
    exact labelLe_pushTup2 (fun {ts'} i xs m hy => hJs (Member.there i) xs m hy)
      ⟨rfl, fun args m hx => hJs Member.here args m hx, hLs⟩

private theorem lookupL_cons_succ {L : List Ty → Type} (e : (ts : List Ty) × L ts)
    (xs : List ((ts : List Ty) × L ts)) (ts : List Ty) (idx : Nat) :
    lookupL (e :: xs) ts (idx + 1) = lookupL xs ts idx := by
  simp only [lookupL, listGet?_eq_getElem?, List.getElem?_cons_succ]

private theorem labelLe_lookupL :
    ∀ {ls₁ ls₂ : List ((ts : List Ty) × Cont ts)} {ts : List Ty} {idx : Nat} {l₁ : Cont ts},
      LabelLe ls₁ ls₂ → lookupL ls₁ ts idx = some l₁ →
      ∃ l₂, lookupL ls₂ ts idx = some l₂ ∧ ∀ args m, l₁ args m → l₂ args m
  | [], _, _, _, _, _, h => by simp [lookupL, listGet?.eq_1] at h
  | ⟨_, _⟩ :: _, [], _, _, _, hRel, _ => nomatch hRel
  | ⟨ts₁, l₁'⟩ :: _, ⟨_, l₂'⟩ :: _, ts, 0, l₁, hRel, hLk => by
    obtain ⟨hEq, hImp, _⟩ := hRel
    subst hEq
    simp only [lookupL, listGet?.eq_2] at hLk ⊢
    cases hTy : listTyDecEq ts₁ ts with
    | isFalse hne =>
      have : castListTy ts₁ ts l₁' = none := by simp [castListTy, hTy]
      simp [this] at hLk
    | isTrue heq =>
      subst heq
      rw [castListTy_self] at hLk ⊢
      simp only [Option.some.injEq] at hLk
      subst hLk
      exact ⟨l₂', rfl, hImp⟩
  | ⟨_, _⟩ :: xs₁, ⟨_, _⟩ :: xs₂, ts, idx + 1, l₁, hRel, hLk => by
    obtain ⟨_, _, hTail⟩ := hRel
    have hLk' : lookupL xs₁ ts idx = some l₁ := by simpa [lookupL, listGet?_eq_getElem?] using hLk
    obtain ⟨l₂, hLk₂, hImp⟩ := labelLe_lookupL hTail hLk'
    exact ⟨l₂, by simpa [lookupL, listGet?_eq_getElem?] using hLk₂, hImp⟩

private theorem zpeelGroupWrap_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : List Ty} {D : List (List Ty)}
    {vs : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    (hG : CtxTypes G vs) (hD : CtxTypes D ls) (cfg : ZeroPeelConfig)
    {sig : List (List Ty)} (bs' : TBlocks rs sig) (k' : TFlat rs)
    (hwf : TFlat.wfCheck G D (.group bs' k') = true) {m : Mem 64}
    (hwp : wp Γ Q X (denote Val Cont (.group bs' k') vs ls) m) :
    wp Γ Q X (denote Val Cont (zpeelGroupWrap cfg bs' k') vs ls) m := by
  cases bs' with
  | nil => rw [zpeelGroupWrap_nil]; exact hwp
  | @cons ts0 _ body bsNil =>
    cases bsNil with
    | nil =>
      rw [zpeelGroupWrap_cons_nil]
      cases hw : widenFillSingle cfg.unrollN ts0 body k' with
      | some g => exact widenFillSingle_wp hG hD hwf hw hwp
      | none =>
        cases hp : peelSingle cfg ts0 body k' with
        | some g =>
          rw [wfCheck_group_eq, Bool.and_eq_true] at hwf
          exact peelSingle_wp hG hD hwf.2 hp hwp
        | none => exact hwp
    | cons _ _ => rw [zpeelGroupWrap_cons2]; exact hwp

mutual
private theorem zpeelTF_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (cfg : ZeroPeelConfig) : (tf : TFlat rs) → (G : List Ty) → (D : List (List Ty)) →
    tf.wfCheck G D = true →
    ∀ (vs : List ((t : Ty) × Val t)) (ls₁ ls₂ : List ((ts : List Ty) × Cont ts)),
      CtxTypes G vs → CtxTypes D ls₁ → CtxTypes D ls₂ → LabelLe ls₁ ls₂ → ∀ {m : Mem 64},
        wp Γ Q X (denote Val Cont tf vs ls₁) m →
        wp Γ Q X (denote Val Cont (zpeelTF cfg tf) vs ls₂) m
  | .let_ op k, G, D, hwf, vs, ls₁, ls₂, hG, hD₁, hD₂, hLs, m, hwp => by
    rw [wfCheck_let_eq, Bool.and_eq_true] at hwf
    rw [zpeelTF_let, denote_let_eq]; rw [denote_let_eq] at hwp
    cases hda : denoteArgs vs op.args with
    | none => exact absurd (by rw [hda] at hwp; exact hwp) wp_hlt_false
    | some _ =>
      rw [hda] at hwp; dsimp only at hwp ⊢; rw [wp_let] at hwp ⊢
      exact Op.wp_mono (fun r hr => zpeelTF_wp cfg k _ D hwf.2 (pushTup r vs)
        ls₁ ls₂ (CtxTypes_pushTup r hG) hD₁ hD₂ hLs hr) hwp
  | .load t a k, G, D, hwf, vs, ls₁, ls₂, hG, hD₁, hD₂, hLs, m, hwp => by
    rw [wfCheck_load_eq, Bool.and_eq_true] at hwf
    rw [zpeelTF_load, denote_load_eq]; rw [denote_load_eq] at hwp
    cases hda : denoteArg vs a with
    | none => exact absurd (by rw [hda] at hwp; exact hwp) wp_hlt_false
    | some _ =>
      rw [hda] at hwp; dsimp only at hwp ⊢; rw [wp_load] at hwp ⊢
      obtain ⟨v, hv, hk⟩ := hwp
      exact ⟨v, hv, zpeelTF_wp cfg k (t :: G) D hwf.2 (⟨t, v⟩ :: vs)
        ls₁ ls₂ (.cons hG) hD₁ hD₂ hLs hk⟩
  | .store v a k, G, D, hwf, vs, ls₁, ls₂, hG, hD₁, hD₂, hLs, m, hwp => by
    rw [wfCheck_store_eq, Bool.and_eq_true] at hwf
    rw [zpeelTF_store, denote_store_eq]; rw [denote_store_eq] at hwp
    cases hdv : denoteArg vs v with
    | none => exact absurd (by rw [hdv] at hwp; exact hwp) wp_hlt_false
    | some _ =>
      cases hda : denoteArg vs a with
      | none => exact absurd (by rw [hdv, hda] at hwp; exact hwp) wp_hlt_false
      | some _ =>
        rw [hdv, hda] at hwp; dsimp only at hwp ⊢; rw [wp_store] at hwp ⊢
        exact ⟨hwp.1, zpeelTF_wp cfg k G D hwf.2 vs ls₁ ls₂ hG hD₁ hD₂ hLs hwp.2⟩
  | .call f bs args k, G, D, hwf, vs, ls₁, ls₂, hG, hD₁, hD₂, hLs, m, hwp => by
    rw [wfCheck_call_eq, Bool.and_eq_true] at hwf
    rw [zpeelTF_call, denote_call_eq]; rw [denote_call_eq] at hwp
    cases hda : denoteArgs vs args with
    | none => exact absurd (by rw [hda] at hwp; exact hwp) wp_hlt_false
    | some _ =>
      rw [hda] at hwp; dsimp only at hwp ⊢; rw [wp_call_eq] at hwp ⊢
      obtain ⟨P, E, hPre, hPost, hEx⟩ := hwp
      exact ⟨P, E, hPre, fun r m' hp => zpeelTF_wp cfg k (pushTypes bs G) D hwf.2
        (pushTup r vs) ls₁ ls₂ (CtxTypes_pushTup r hG) hD₁ hD₂ hLs (hPost r m' hp), hEx⟩
  | .jnz c t e, G, D, hwf, vs, ls₁, ls₂, hG, hD₁, hD₂, hLs, m, hwp => by
    rw [wfCheck_jnz_eq, Bool.and_eq_true, Bool.and_eq_true] at hwf
    rw [zpeelTF_jnz, denote_jnz_eq]; rw [denote_jnz_eq] at hwp
    cases hdc : denoteArg vs c with
    | none => exact absurd (by rw [hdc] at hwp; exact hwp) wp_hlt_false
    | some _ =>
      rw [hdc] at hwp; dsimp only at hwp ⊢; rw [wp_jnz] at hwp ⊢
      exact ⟨fun ht => zpeelTF_wp cfg t G D hwf.1.2 vs ls₁ ls₂ hG hD₁ hD₂ hLs (hwp.1 ht),
        fun hf => zpeelTF_wp cfg e G D hwf.2 vs ls₁ ls₂ hG hD₁ hD₂ hLs (hwp.2 hf)⟩
  | .jump (ts := ts) j args, _, _, _, vs, ls₁, ls₂, _, _, _, hLs, m, hwp => by
    rw [zpeelTF_jump]; rw [denote_jump_eq] at hwp ⊢
    cases hLk : lookupL ls₁ ts j with
    | none => exact absurd (by rw [hLk] at hwp; exact hwp) wp_hlt_false
    | some l₁ =>
      cases hda : denoteArgs vs args with
      | none => exact absurd (by rw [hLk, hda] at hwp; exact hwp) wp_hlt_false
      | some _ =>
        obtain ⟨l₂, hLk₂, hImp⟩ := labelLe_lookupL hLs hLk
        rw [hLk, hda] at hwp; dsimp only at hwp; rw [wp_jump] at hwp
        rw [hLk₂]; dsimp only; rw [wp_jump]; exact hImp _ m hwp
  | .ret _, _, _, _, _, _, _, _, _, _, _, _, hwp => by rw [zpeelTF_ret]; exact hwp
  | .exit _ _, _, _, _, _, _, _, _, _, _, _, _, hwp => by rw [zpeelTF_exit]; exact hwp
  | .hlt, _, _, _, _, _, _, _, _, _, _, _, hwp => by rw [zpeelTF_hlt]; exact hwp
  | .group (sig := sig) bs k, G, D, hwf, vs, ls₁, ls₂, hG, hD₁, hD₂, hLs, m, hwp => by
    rw [wfCheck_group_eq, Bool.and_eq_true] at hwf
    let bs' := zpeelBs cfg bs; let k' := zpeelTF cfg k
    have hwf' : TFlat.wfCheck G D (.group bs' k') = true := by
      rw [wfCheck_group_eq, Bool.and_eq_true]
      exact ⟨wfCheck_zpeelBs cfg bs G _ hwf.1, wfCheck_zpeelTF cfg k G _ hwf.2⟩
    let bodies₁ : Tup Cont sig → Blocks Val Cont rs sig :=
      fun Js => denoteB Val Cont bs vs (pushTup Js ls₁)
    let k₁ : Tup Cont sig → Expr Val Cont rs := fun Js => denote Val Cont k vs (pushTup Js ls₁)
    let bodies₂ : Tup Cont sig → Blocks Val Cont rs sig :=
      fun Js => denoteB Val Cont bs' vs (pushTup Js ls₂)
    let k₂ : Tup Cont sig → Expr Val Cont rs := fun Js => denote Val Cont k' vs (pushTup Js ls₂)
    have hDiag := ctx_diagV_of_vs (vs := vs)
    have hMono1 := ctx_monoD_of_ls (ls := ls₁); have hMono2 := ctx_monoD_of_ls (ls := ls₂)
    have hRelV := ctxRel_refl_vs (vs := vs)
    have hRelL1 := ctxRel_refl_ls (ls := ls₁); have hRelL2 := ctxRel_refl_ls (ls := ls₂)
    have hwfB2 : ∀ Js₁ Js₂ : Tup Cont sig, WfB _
        (Js₁.zip Js₂ ++ List.map (fun ⟨ts, l⟩ => ⟨ts, (l, l)⟩) ls₂) (bodies₂ Js₁) (bodies₂ Js₂) :=
      fun Js₁ Js₂ => denoteB_wf bs' hRelV (ctxRel_pushTup Js₁ Js₂ hRelL2)
    rw [denote_group_eq] at hwp
    change wp Γ Q X (.group bodies₁ k₁) m at hwp
    rw [wp_group_iff hDiag hMono1
      (fun Js₁ Js₂ => denoteB_wf bs hRelV (ctxRel_pushTup Js₁ Js₂ hRelL1))
      (fun Js₁ Js₂ => denote_wf k hRelV (ctxRel_pushTup Js₁ Js₂ hRelL1))] at hwp
    let Js₁ := lfp Γ Q X bodies₁; let Js₂ := lfp Γ Q X bodies₂
    have hCl₁ : Closed Γ Q X (bodies₁ Js₂) Js₂ := by
      rw [closed_iff]; intro ts i xs m' hbi
      exact (closed_iff Γ Q X (bodies₂ Js₂) Js₂).mp (lfp_closed hDiag hMono2 hwfB2) i xs m'
        (zpeelBs_wp cfg bs G (pushTypes sig D) hwf.1 vs (pushTup Js₂ ls₁) (pushTup Js₂ ls₂)
          hG (CtxTypes_pushTup Js₂ hD₁) (CtxTypes_pushTup Js₂ hD₂) (labelLe_pushTup Js₂ hLs)
          i xs m' hbi)
    have hwpK2 : wp Γ Q X (k₂ Js₂) m := zpeelTF_wp cfg k G (pushTypes sig D) hwf.2 vs
      (pushTup Js₁ ls₁) (pushTup Js₂ ls₂) hG (CtxTypes_pushTup Js₁ hD₁) (CtxTypes_pushTup Js₂ hD₂)
      (labelLe_pushTup2 (fun i xs m' h => lfp_le hCl₁ i xs m' h) hLs) hwp
    rw [zpeelTF_group]
    exact zpeelGroupWrap_wp hG hD₂ cfg bs' k' hwf' (by
      rw [denote_group_eq]; change wp Γ Q X (.group bodies₂ k₂) m
      rw [wp_group_iff hDiag hMono2 hwfB2
        (fun Js₁ Js₂ => denote_wf k' hRelV (ctxRel_pushTup Js₁ Js₂ hRelL2))]; exact hwpK2)

private theorem zpeelBs_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (cfg : ZeroPeelConfig) : {sig : List (List Ty)} → (bs : TBlocks rs sig) →
    (G : List Ty) → (D : List (List Ty)) → bs.wfCheck G D = true →
    ∀ (vs : List ((t : Ty) × Val t)) (ls₁ ls₂ : List ((ts : List Ty) × Cont ts)),
      CtxTypes G vs → CtxTypes D ls₁ → CtxTypes D ls₂ → LabelLe ls₁ ls₂ →
      ∀ {ts : List Ty} (i : Member ts sig) (xs : Tup Val ts) (m : Mem 64),
        wp Γ Q X ((denoteB Val Cont bs vs ls₁).get i xs) m →
        wp Γ Q X ((denoteB Val Cont (zpeelBs cfg bs) vs ls₂).get i xs) m
  | _, .nil, _, _, _, _, _, _, _, _, _, _, _, i, _, _, _ => nomatch i
  | ts :: _, .cons b bs, G, D, hwf, vs, ls₁, ls₂, hG, hD₁, hD₂, hLs, _, .here, xs, m, hwp => by
    rw [wfCheckB_cons_eq, Bool.and_eq_true] at hwf
    rw [zpeelBs_cons, denoteB_cons_eq]; rw [denoteB_cons_eq] at hwp
    exact zpeelTF_wp cfg b (pushTypes ts G) D hwf.1 (pushTup xs vs) ls₁ ls₂
      (CtxTypes_pushTup xs hG) hD₁ hD₂ hLs hwp
  | _ :: _, .cons b bs, G, D, hwf, vs, ls₁, ls₂, hG, hD₁, hD₂, hLs, _, .there i, xs, m, hwp => by
    rw [wfCheckB_cons_eq, Bool.and_eq_true] at hwf
    rw [zpeelBs_cons, denoteB_cons_eq]; rw [denoteB_cons_eq] at hwp
    exact zpeelBs_wp cfg bs G D hwf.2 vs ls₁ ls₂ hG hD₁ hD₂ hLs i xs m hwp
end

/-! ## Section 5B: Syntactic `CallsOk` Preservation & Module Safety -/

section
open PassFlatKit (callsOkTF callsOkBs)

mutual
private theorem shiftTFlat_callsOk {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} :
    (tf : TFlat rs) → (d n : Nat) →
    callsOkTF allowed exits tf → callsOkTF allowed exits (shiftTFlat d n tf)
  | .let_ _ k, _, n, h => by
    unfold shiftTFlat; simp only [PassFlatKit.callsOkTF_let] at h ⊢
    exact shiftTFlat_callsOk k _ n h
  | .load _ _ k, _, n, h => by
    unfold shiftTFlat; simp only [PassFlatKit.callsOkTF_load] at h ⊢
    exact shiftTFlat_callsOk k _ n h
  | .store _ _ k, _, n, h => by
    unfold shiftTFlat; simp only [PassFlatKit.callsOkTF_store] at h ⊢
    exact shiftTFlat_callsOk k _ n h
  | .call _ _ _ k, _, n, h => by
    unfold shiftTFlat; simp only [PassFlatKit.callsOkTF_call] at h ⊢
    exact ⟨h.1, shiftTFlat_callsOk k _ n h.2⟩
  | .jnz _ t e, d, n, h => by
    unfold shiftTFlat; simp only [PassFlatKit.callsOkTF_jnz] at h ⊢
    exact ⟨shiftTFlat_callsOk t d n h.1, shiftTFlat_callsOk e d n h.2⟩
  | .jump _ _, _, _, _ | .ret _, _, _, _ | .hlt, _, _, _ => by unfold shiftTFlat; simp
  | .exit _ _, _, _, h => by unfold shiftTFlat; simpa using h
  | .group bs k, d, n, h => by
    unfold shiftTFlat; simp only [PassFlatKit.callsOkTF_group] at h ⊢
    exact ⟨shiftTBlocks_callsOk bs d n h.1, shiftTFlat_callsOk k d n h.2⟩

private theorem shiftTBlocks_callsOk {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} :
    {sig : List (List Ty)} → (bs : TBlocks rs sig) → (d n : Nat) →
    callsOkBs allowed exits bs → callsOkBs allowed exits (shiftTBlocks d n bs)
  | _, .nil, _, _, _ => by unfold shiftTBlocks; simp
  | ts :: _, .cons b bs, d, n, h => by
    unfold shiftTBlocks; simp only [PassFlatKit.callsOkBs_cons] at h ⊢
    exact ⟨shiftTFlat_callsOk b (d + ts.length) n h.1, shiftTBlocks_callsOk bs d n h.2⟩
end

private theorem letBindTup_callsOk {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} :
    {ts : List Ty} → (args : Tup (Arg K) ts) → (d : Nat) → {body : TFlat rs} →
    callsOkTF allowed exits body → callsOkTF allowed exits (letBindTup args d body)
  | [], _, _, _, h => h
  | _ :: _, (_, as), d, _, h => by
    simp only [letBindTup, PassFlatKit.callsOkTF_let]
    exact letBindTup_callsOk as (d + 1) h

private theorem inlineJump0_callsOk {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} (body : TFlat rs) (ts0 : List Ty) (hb : callsOkTF allowed exits body) :
    ∀ (d : Nat) (k : TFlat rs),
      callsOkTF allowed exits k → callsOkTF allowed exits (inlineJump0 body ts0 d k)
  | _, .let_ _ k, hk | _, .load _ _ k, hk | _, .store _ _ k, hk => by
    simp [inlineJump0] at hk ⊢
    exact inlineJump0_callsOk body ts0 hb _ k hk
  | _, .call _ _ _ k, hk => by
    simp [inlineJump0] at hk ⊢
    exact ⟨hk.1, inlineJump0_callsOk body ts0 hb _ k hk.2⟩
  | d, .jnz _ t e, hk => by
    simp [inlineJump0] at hk ⊢
    exact ⟨inlineJump0_callsOk body ts0 hb d t hk.1, inlineJump0_callsOk body ts0 hb d e hk.2⟩
  | d, .jump _ _, _ => by
    dsimp only [inlineJump0]; split
    · split; exact letBindTup_callsOk _ 0 (shiftTFlat_callsOk body ts0.length d hb)
      simp
    · simp
  | _, .ret _, _ | _, .hlt, _ => by simp [inlineJump0]
  | _, .exit _ _, hk | _, .group _ _, hk => hk

private theorem mkStoreChainGoRest_callsOk {allowed : List SigEntry}
    {exits : List Sym} {rs : List Ty} (fill64 : BitVec 64) (stepK : Nat) :
    ∀ (m remStores curIDepth : Nat),
      callsOkTF allowed exits (mkStoreChainGoRest (rs := rs) fill64 stepK m remStores curIDepth)
  | _, 0, _ => by simp [mkStoreChainGoRest]
  | m, r + 1, curIDepth => by
    simpa [mkStoreChainGoRest] using
      mkStoreChainGoRest_callsOk fill64 stepK (m + 1) r (curIDepth + 1)

private theorem mkStoreChain_callsOk {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} (fill64 : BitVec 64) (stepK : Nat) :
    ∀ (unrollN iDepth : Nat),
      callsOkTF allowed exits (mkStoreChain (rs := rs) fill64 stepK unrollN iDepth)
  | 0, _ | 1, _ => by simp [mkStoreChain]
  | n + 2, iDepth => by
    simpa [mkStoreChain] using mkStoreChainGoRest_callsOk fill64 stepK 1 (n + 1) iDepth

private theorem mkWideWrapper_callsOk {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} (spec : FillSpec) (unrollN : Nat) (initArg : Arg K i64) :
    callsOkTF allowed exits (mkWideWrapper (rs := rs) spec unrollN initArg) := by
  have hWithShift : ∀ d idx, callsOkTF allowed exits
      (if spec.shift == 0 then
        TFlat.let_ (op2 (OpCode.add i64) (tArgShift d spec.base) idx)
          (mkStoreChain (rs := rs) spec.fill64 (unrollN * (8 >>> spec.shift)) unrollN d)
      else
        TFlat.let_ (op2 (OpCode.shl i64) idx (Arg.imm (BitVec.ofNat 64 spec.shift)))
          (TFlat.let_ (op2 (OpCode.add i64) (tArgShift (d + 1) spec.base) (.var 0))
            (mkStoreChain (rs := rs) spec.fill64
              (unrollN * (8 >>> spec.shift)) unrollN (d + 1)))) := by
    intro d _; split <;> simp [mkStoreChain_callsOk]
  dsimp only [mkWideWrapper, mkWideBody]
  simp only [PassFlatKit.callsOkTF_group, PassFlatKit.callsOkBs_cons, PassFlatKit.callsOkBs_nil,
    PassFlatKit.callsOkTF_let, PassFlatKit.callsOkTF_jnz, PassFlatKit.callsOkTF_jump, and_true]
  cases spec.off? with
  | none => exact hWithShift 3 (.var 2)
  | some _ => simp only [PassFlatKit.callsOkTF_let]; exact hWithShift 4 (.var 0)

private theorem zpeelGroupWrap_callsOk {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} (cfg : ZeroPeelConfig) {sig : List (List Ty)}
    (bs' : TBlocks rs sig) (k' : TFlat rs)
    (hbs : callsOkBs allowed exits bs') (hk : callsOkTF allowed exits k') :
    callsOkTF allowed exits (zpeelGroupWrap cfg bs' k') := by
  cases bs' with
  | nil => rw [zpeelGroupWrap_nil]; simp [hbs, hk]
  | @cons ts0 _ body bsNil =>
    cases bsNil with
    | nil =>
      rw [zpeelGroupWrap_cons_nil]
      cases hw : widenFillSingle cfg.unrollN ts0 body k' with
      | some g =>
        obtain ⟨_, _, rfl, initArg, spec, _, _, rfl⟩ := widenFillSingle_eq_some hw
        simp only [PassFlatKit.callsOkBs_cons, PassFlatKit.callsOkBs_nil] at hbs
        simp [hbs.1, mkWideWrapper_callsOk spec cfg.unrollN initArg]
      | none =>
        cases hp : peelSingle cfg ts0 body k' with
        | some g =>
          dsimp only [peelSingle] at hp; split at hp
          · simp only [Option.some.injEq] at hp; subst hp
            simp only [PassFlatKit.callsOkBs_cons] at hbs
            simp [hbs, inlineJump0_callsOk body ts0 hbs.1 0 k' hk]
          · cases hp
        | none => simp [hbs, hk]
    | cons _ _ => rw [zpeelGroupWrap_cons2]; simp [hbs, hk]

mutual
private theorem zpeelTF_callsOk {allowed : List SigEntry} {exits : List Sym}
    (cfg : ZeroPeelConfig) {rs : List Ty} :
    (tf : TFlat rs) → callsOkTF allowed exits tf → callsOkTF allowed exits (zpeelTF cfg tf)
  | .let_ _ k, h => by
    rw [zpeelTF_let]; simp only [PassFlatKit.callsOkTF_let] at h ⊢
    exact zpeelTF_callsOk cfg k h
  | .load _ _ k, h => by
    rw [zpeelTF_load]; simp only [PassFlatKit.callsOkTF_load] at h ⊢
    exact zpeelTF_callsOk cfg k h
  | .store _ _ k, h => by
    rw [zpeelTF_store]; simp only [PassFlatKit.callsOkTF_store] at h ⊢
    exact zpeelTF_callsOk cfg k h
  | .call _ _ _ k, h => by
    rw [zpeelTF_call]; simp only [PassFlatKit.callsOkTF_call] at h ⊢
    exact ⟨h.1, zpeelTF_callsOk cfg k h.2⟩
  | .jnz _ t e, h => by
    rw [zpeelTF_jnz]; simp only [PassFlatKit.callsOkTF_jnz] at h ⊢
    exact ⟨zpeelTF_callsOk cfg t h.1, zpeelTF_callsOk cfg e h.2⟩
  | .jump _ _, _ => by rw [zpeelTF_jump]; simp
  | .ret _, _ => by rw [zpeelTF_ret]; simp
  | .hlt, _ => by rw [zpeelTF_hlt]; simp
  | .exit _ _, h => by rw [zpeelTF_exit]; exact h
  | .group bs k, h => by
    rw [zpeelTF_group]; simp only [PassFlatKit.callsOkTF_group] at h
    exact zpeelGroupWrap_callsOk cfg (zpeelBs cfg bs) (zpeelTF cfg k)
      (zpeelBs_callsOk cfg bs h.1) (zpeelTF_callsOk cfg k h.2)

private theorem zpeelBs_callsOk {allowed : List SigEntry} {exits : List Sym}
    (cfg : ZeroPeelConfig) {rs : List Ty} :
    {sig : List (List Ty)} → (bs : TBlocks rs sig) →
    callsOkBs allowed exits bs → callsOkBs allowed exits (zpeelBs cfg bs)
  | _, .nil, _ => by rw [zpeelBs_nil]; simp
  | _ :: _, .cons b bs, h => by
    rw [zpeelBs_cons]; simp only [PassFlatKit.callsOkBs_cons] at h ⊢
    exact ⟨zpeelTF_callsOk cfg b h.1, zpeelBs_callsOk cfg bs h.2⟩
end

end

end ZeroPeel

public section

/-- Syntactic well-scopedness preservation for `TFlat.zeroPeelWith`. -/
theorem TFlat.wfCheck_zeroPeelWith (cfg : ZeroPeelConfig := {}) {rs : List Ty}
    {G : List Ty} {D : List (List Ty)} {tf : TFlat rs}
    (h : tf.wfCheck G D = true) : (tf.zeroPeelWith cfg).wfCheck G D = true := by
  dsimp only [TFlat.zeroPeelWith]
  split
  · exact ZeroPeel.wfCheck_zpeelTF cfg tf G D h
  · exact h

/-- Relational PHOAS well-formedness preservation for `Func.zeroPeelWith`. -/
theorem Func.zeroPeelWith_wf (cfg : ZeroPeelConfig := {}) {as rs : List Ty}
    {f : Func as rs} (hf : f.Wf) : (f.zeroPeelWith cfg).Wf := by
  dsimp only [Func.zeroPeelWith]
  split
  · exact Func.wf_of_denote (ZeroPeel.zpeelTF cfg (reifyFunc f)) rfl
  · exact hf

/-- Weakest-precondition semantic refinement for `Func.zeroPeelWith`. -/
theorem Func.zeroPeelWith_spec (cfg : ZeroPeelConfig := {}) {as rs : List Ty}
    {f : Func as rs} (hf : f.Wf) {Γ : Env} {xs : Tup Val as} {m : Mem 64}
    {Q : Post rs} {X : XPost} (h : Func.spec Γ f xs m Q X) :
    Func.spec Γ (f.zeroPeelWith cfg) xs m Q X := by
  dsimp only [Func.zeroPeelWith]
  split
  · rename_i hcond
    rw [Bool.and_eq_true] at hcond
    have hRen := Func.renorm_spec hf h
    exact ZeroPeel.zpeelTF_wp cfg (reifyFunc f) (pushTypes as []) [] hcond.1
      (pushTup xs []) [] [] (ZeroPeel.CtxTypes_pushTup xs .nil) .nil .nil trivial hRen
  · exact h

/-- Call-closure preservation for `Func.zeroPeelWith`. -/
theorem Func.zeroPeelWith_callsOk (cfg : ZeroPeelConfig := {})
    {allowed : List SigEntry} {exits : List Sym} {as rs : List Ty}
    {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((f.zeroPeelWith cfg) (fun _ => Unit) (fun _ => Unit)
      (Tup.units as)).callsOk allowed exits := by
  dsimp only [Func.zeroPeelWith]
  split
  · have hSyn := (PassFlatKit.callsOkTF_reify_iff (allowed := allowed) (exits := exits) hf).2 hc
    exact PassFlatKit.callsOkTF_denote (ZeroPeel.zpeelTF cfg (reifyFunc f))
      (ZeroPeel.zpeelTF_callsOk cfg (reifyFunc f) hSyn) _ _
  · exact hc

/-- Closed-function relational well-formedness preservation for `Func.zeroPeel`. -/
theorem Func.zeroPeel_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (cfg : ZeroPeelConfig := {}) : (f.zeroPeel cfg).Wf :=
  Func.zeroPeelWith_wf cfg hf

/-- Closed-function WP semantic refinement for `Func.zeroPeel`. -/
theorem Func.zeroPeel_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (cfg : ZeroPeelConfig := {}) {Γ : Env} {xs : Tup Val as} {m : Mem 64}
    {Q : Post rs} {X : XPost} (h : Func.spec Γ f xs m Q X) :
    Func.spec Γ (f.zeroPeel cfg) xs m Q X :=
  Func.zeroPeelWith_spec cfg hf h

/-- Closed-function call-closure preservation for `Func.zeroPeel`. -/
theorem Func.zeroPeel_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits)
    (cfg : ZeroPeelConfig := {}) :
    ((f.zeroPeel cfg) (fun _ => Unit) (fun _ => Unit)
      (Tup.units as)).callsOk allowed exits :=
  Func.zeroPeelWith_callsOk cfg hf hc

/-- Named-function well-formedness preservation for `Fn.zeroPeel`. -/
theorem Fn.zeroPeel_wf {fn : Fn} (hfn : fn.Wf) (cfg : ZeroPeelConfig := {}) :
    (fn.zeroPeel cfg).Wf := Func.zeroPeel_wf hfn cfg

/-- Named-function WP semantic refinement for `Fn.zeroPeel`. -/
theorem Fn.zeroPeel_spec (fn : Fn) (hfn : fn.Wf) (cfg : ZeroPeelConfig := {})
    {Γ : Env} {xs : Tup Val fn.as} {m : Mem 64} {Q : Post fn.rs} {X : XPost}
    (h : Func.spec Γ fn.body xs m Q X) :
    Func.spec Γ (fn.zeroPeel cfg).body xs m Q X := Func.zeroPeel_spec hfn cfg h

/-- Named-function call-closure preservation for `Fn.zeroPeel`. -/
theorem Fn.zeroPeel_callsOk {allowed : List SigEntry} {exits : List Sym}
    {fn : Fn} (hfn : fn.Wf) (hc : fn.callsOk allowed exits) (cfg : ZeroPeelConfig := {}) :
    (fn.zeroPeel cfg).callsOk allowed exits := Func.zeroPeel_callsOk hfn hc cfg

/-- Whole-module soundness preservation under `Fn.zeroPeel`. -/
theorem Module.zeroPeel_ok {Γ : Env} {M : Module} (hM : ModuleOk Γ M)
    (cfg : ZeroPeelConfig := {}) :
    ModuleOk Γ { M with fns := M.fns.map (Fn.zeroPeel · cfg) } := by
  refine ⟨?_, ?_⟩
  · have hNames : (M.fns.map (Fn.zeroPeel · cfg)).map Fn.name = M.fns.map Fn.name := by
      rw [List.map_map]; exact List.map_congr_left fun _ _ => rfl
    dsimp only [Module.namesNodup, Module.names] at *; rw [hNames]; exact hM.nodup
  · intro pre fn' post hsplit; dsimp only at hsplit
    obtain ⟨pre₀, l₂, hMsplit, rfl, hl₂⟩ :=
      PassFlatKit.map_eq_append_split (Fn.zeroPeel · cfg) hsplit
    cases l₂ with
    | nil => cases hl₂
    | cons fn post₀ =>
      simp only [List.map_cons, List.cons.injEq] at hl₂; obtain ⟨rfl, rfl⟩ := hl₂
      obtain ⟨hWf, hCalls, hSpec⟩ := hM.fnsOk pre₀ fn post₀ hMsplit
      have hSigPre : (pre₀.map (Fn.zeroPeel · cfg)).map Fn.sig = pre₀.map Fn.sig := by
        rw [List.map_map]; exact List.map_congr_left fun _ _ => rfl
      exact ⟨Fn.zeroPeel_wf hWf cfg, hSigPre ▸ Fn.zeroPeel_callsOk hWf hCalls cfg,
        fun xs m Q X hPre => Fn.zeroPeel_spec fn hWf cfg (hSpec xs m Q X hPre)⟩
end
end LeanQbe.T
