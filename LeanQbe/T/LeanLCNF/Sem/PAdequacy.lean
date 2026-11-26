module

public import LeanQbe.T.LeanLCNF.Sem.PLemmas

/-!
# Tier-P Adequacy (`PWp ⇔ PEval` on `.isShared`-free Code) (`PAdequacy`)

Bridges `PWp` and the executable fuel-indexed oracle `PEval`:
1. `PEvalInf`: fuel-unbounded `PEval`-induced `PEnv`.
2. `PWp_terminates_PEval`: any `PWp (PEvalInf ...)` judgment terminates in `PEval` with a
   satisfying outcome (holds for ALL `LcCode`s including `.isShared`).
3. `PEval_complete_PWp`, `PModuleOk_PEvalInf`, and `PWp_iff_PEval`: full bidirectional
   adequacy `PWp ⇔ PEval` on `.isShared`-free code (`noIsSharedCode`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF

/-! ## 1. `PEvalInf` & `PWp` → `∃ fuel, PEval` Termination -/

/-- Fuel-unbounded `PEval`-induced `PEnv`: holds when `PEval` terminates at some fuel and
satisfies `(Q, X)`. -/
@[expose] def PEvalInf (m : LcModule) (shared : Bool) : PEnv :=
  fun fn args Q X => ∃ fuel out, PEval fuel m fn args shared = some out ∧ OutcomeOk Q X out

private theorem PEvalApply_of_PApply {m : LcModule} {shared : Bool} {K : PPost} {X : PXPost}
    (fn : PVal) (args : List PVal) (h : PApply (PEvalInf m shared) fn args K X) :
    ∃ f out, PEvalApply (PEvalCallAt m shared f) fn args = some out ∧ OutcomeOk K X out := by
  cases fn with
  | clo g arity fixed =>
    unfold PApply at h
    by_cases hemp : args.isEmpty = true
    · rw [ite_eq_left hemp] at h
      refine ⟨0, .ret (.clo g arity fixed), ?_, h⟩
      unfold PEvalApply; rw [ite_eq_left hemp]
    · rw [ite_eq_right hemp] at h
      by_cases hrem : arity - fixed.length = 0
      · rw [dite_eq_left hrem] at h
        refine ⟨0, .panic panicBadClosure, ?_, h⟩
        unfold PEvalApply; rw [ite_eq_right hemp, dite_eq_left hrem]
      · rw [dite_eq_right hrem] at h
        by_cases hlt : args.length < arity - fixed.length
        · rw [dite_eq_left hlt] at h
          refine ⟨0, .ret (.clo g arity (fixed ++ args)), ?_, h⟩
          unfold PEvalApply; rw [ite_eq_right hemp, dite_eq_right hrem, dite_eq_left hlt]
        · rw [dite_eq_right hlt] at h
          by_cases heq : args.length = arity - fixed.length
          · rw [dite_eq_left heq] at h
            rcases h with ⟨P, E, ⟨f, out, hev, hok⟩, hP, hE⟩
            refine ⟨f, out, ?_, OutcomeOk_mono hP hE hok⟩
            unfold PEvalApply
            rw [ite_eq_right hemp, dite_eq_right hrem, dite_eq_right hlt, dite_eq_left heq]
            exact hev
          · rw [dite_eq_right heq] at h
            rcases h with ⟨P, E, ⟨f1, out1, hev1, hok1⟩, hP, hE⟩
            cases out1 with
            | panic c =>
              refine ⟨f1, .panic c, ?_, hE c hok1⟩
              unfold PEvalApply
              rw [ite_eq_right hemp, dite_eq_right hrem, dite_eq_right hlt, dite_eq_right heq]
              rw [PEvalCallAt_eq_PEval, hev1]
            | ret r =>
              obtain ⟨f2, out2, hev2, hok2⟩ :=
                PEvalApply_of_PApply r (args.drop (arity - fixed.length)) (hP r hok1)
              let fm := Nat.max f1 f2
              refine ⟨fm, out2, ?_, hok2⟩
              unfold PEvalApply
              rw [ite_eq_right hemp, dite_eq_right hrem, dite_eq_right hlt, dite_eq_right heq]
              have h1' : PEvalCallAt m shared fm g (fixed ++ args.take (arity - fixed.length)) =
                  some (.ret r) := by
                rw [PEvalCallAt_eq_PEval]
                exact PEval_fuel_mono (Nat.le_max_left f1 f2) hev1
              rw [h1']
              exact PEvalApply_mono (fun fn' args' out' hcall =>
                PEvalCallAt_mono (Nat.le_max_right f1 f2) fn' args' hcall)
                r (args.drop (arity - fixed.length)) hev2
  | erased | bits _ _ | nat _ | int _ | ctor _ _ _ | str _ | arr _ | barr _ =>
    unfold PApply at h
    exact ⟨0, .panic panicBadClosure, by unfold PEvalApply; rfl, h⟩
termination_by args.length
decreasing_by
  simp only [List.length_drop]
  omega

/-- Join-point termination invariant for `PWp (PEvalInf ...)` → `∃ fuel, PEval ...`. -/
@[expose] def JPEvalTerm (m : LcModule) (shared : Bool) (Q : PPost) (X : PXPost)
    (J : PJEnv) (jps : List PJEntry) : Prop :=
  ∀ j vs, J j vs →
    ∃ ps body ρ0 outer,
      jps.dropWhile (fun e => e.1 != j) = (j, ps, body, ρ0) :: outer ∧
      vs.length = ps.length ∧
      ∃ f out,
        PEvalCode f m shared ((j, ps, body, ρ0) :: outer) (ρ0.bindAll ps vs) body = some out ∧
        OutcomeOk Q X out

mutual
private theorem PWp_terminates_go (m : LcModule) (shared : Bool) :
    ∀ (c : LcCode) (jps : List PJEntry) (J : PJEnv) (ρ : PValEnv) (Q : PPost) (X : PXPost),
      JPEvalTerm m shared Q X J jps →
      PWp (modArityOf m) (PEvalInf m shared) J ρ Q X c →
      ∃ f out, PEvalCode (f + 1) m shared jps ρ c = some out ∧ OutcomeOk Q X out
  | .let_ x ty v kcode, jps, J, ρ, Q, X, hJ, hwp => by
    dsimp only [PWp] at hwp
    cases v with
    | lit l =>
      cases l with
      | nat n =>
        obtain ⟨f, out, hev, hok⟩ := PWp_terminates_go m shared kcode jps J (ρ.set x (.nat n))
          Q X hJ hwp
        exact ⟨f, out, hev, hok⟩
      | str s =>
        obtain ⟨f, out, hev, hok⟩ := PWp_terminates_go m shared kcode jps J (ρ.set x (.str s))
          Q X hJ hwp
        exact ⟨f, out, hev, hok⟩
      | scalar n =>
        obtain ⟨f, out, hev, hok⟩ := PWp_terminates_go m shared kcode jps J
          (ρ.set x (.bits ty.width (BitVec.ofNat ty.width n))) Q X hJ hwp
        exact ⟨f, out, hev, hok⟩
    | erased =>
      obtain ⟨f, out, hev, hok⟩ := PWp_terminates_go m shared kcode jps J (ρ.set x .erased)
        Q X hJ hwp
      exact ⟨f, out, hev, hok⟩
    | ap f as =>
      dsimp only [PVal.wp] at hwp
      cases hf : ρ f <;> cases has : ρ.evalArgs as <;> simp [hf, has] at hwp
      rename_i fn vs
      obtain ⟨f1, o1, hap, hok1⟩ := PEvalApply_of_PApply fn vs hwp
      cases o1 with
      | panic c =>
        refine ⟨f1, .panic c, ?_, hok1⟩
        rw [PEvalCode_succ_eq]; dsimp only [PEvalStep, PEvalVal]
        rw [hf, has]; dsimp only; rw [hap]
      | ret r =>
        obtain ⟨f2, out2, hev2, hok2⟩ := PWp_terminates_go m shared kcode jps J (ρ.set x r)
          Q X hJ hok1
        let fm := Nat.max f1 f2
        refine ⟨fm, out2, ?_, hok2⟩
        rw [PEvalCode_succ_eq]; dsimp only [PEvalStep, PEvalVal]
        rw [hf, has]; dsimp only
        have hap' : PEvalApply (PEvalCallAt m shared fm) fn vs = some (.ret r) :=
          PEvalApply_mono (fun fn' args' out' hcall =>
            PEvalCallAt_mono (Nat.le_max_left f1 f2) fn' args' hcall) fn vs hap
        rw [hap']
        exact PEvalCode_fuel_mono (Nat.succ_le_succ (Nat.le_max_right f1 f2)) hev2
    | ctor ci as =>
      dsimp only [PVal.wp] at hwp
      cases has : ρ.evalArgs as with
      | none => simp [has] at hwp
      | some vs =>
        simp only [has] at hwp
        cases hmk : PVal.mkCtor ty ci vs with
        | none => simp [hmk] at hwp
        | some r =>
          simp only [hmk] at hwp
          obtain ⟨f, out, hev, hok⟩ := PWp_terminates_go m shared kcode jps J (ρ.set x r)
            Q X hJ hwp
          refine ⟨f, out, ?_, hok⟩
          rw [PEvalCode_succ_eq]; dsimp only [PEvalStep, PEvalVal]; simp [has, hmk]; exact hev
    | oproj i y =>
      dsimp only [PVal.wp] at hwp
      cases hp : (ρ y).bind (·.getObj? i) with
      | none => simp [hp] at hwp
      | some r =>
        simp only [hp] at hwp
        obtain ⟨f, out, hev, hok⟩ := PWp_terminates_go m shared kcode jps J (ρ.set x r) Q X hJ hwp
        refine ⟨f, out, ?_, hok⟩
        rw [PEvalCode_succ_eq]; dsimp only [PEvalStep, PEvalVal]; simp [hp]; exact hev
    | uproj i y =>
      dsimp only [PVal.wp] at hwp
      cases hp : (ρ y).bind (·.getUsize? i) with
      | none => simp [hp] at hwp
      | some r =>
        simp only [hp] at hwp
        obtain ⟨f, out, hev, hok⟩ := PWp_terminates_go m shared kcode jps J (ρ.set x r) Q X hJ hwp
        refine ⟨f, out, ?_, hok⟩
        rw [PEvalCode_succ_eq]; dsimp only [PEvalStep, PEvalVal]; simp [hp]; exact hev
    | sproj n off y =>
      dsimp only [PVal.wp] at hwp
      cases hp : (ρ y).bind (·.getScalar? n off ty) with
      | none => simp [hp] at hwp
      | some r =>
        simp only [hp] at hwp
        obtain ⟨f, out, hev, hok⟩ := PWp_terminates_go m shared kcode jps J (ρ.set x r) Q X hJ hwp
        refine ⟨f, out, ?_, hok⟩
        rw [PEvalCode_succ_eq]; dsimp only [PEvalStep, PEvalVal]; simp [hp]; exact hev
    | fap f as =>
      dsimp only [PVal.wp] at hwp
      cases has : ρ.evalArgs as with
      | none => simp [has] at hwp
      | some vs =>
        simp only [has] at hwp
        by_cases hoob : (f == "outOfBounds._redArg") = true
        · rw [ite_eq_left hoob] at hwp
          by_cases hlen : (vs.length == 1) = true
          · rw [ite_eq_left hlen] at hwp
            refine ⟨0, .panic panicOob, ?_, hwp⟩
            rw [PEvalCode_succ_eq]; dsimp only [PEvalStep, PEvalVal]
            simp [has, hoob, beq_iff_eq.mp hlen]
          · rw [ite_eq_right hlen] at hwp; exact False.elim hwp
        · rw [ite_eq_right hoob] at hwp
          by_cases hp : pIsPrimName f = true
          · rw [ite_eq_left hp] at hwp
            cases hpr : primP f vs with
            | none => simp [hpr] at hwp
            | some r =>
              simp only [hpr] at hwp
              obtain ⟨f1, out, hev, hok⟩ := PWp_terminates_go m shared kcode jps J (ρ.set x r)
                Q X hJ hwp
              refine ⟨f1, out, ?_, hok⟩
              rw [PEvalCode_succ_eq]; dsimp only [PEvalStep, PEvalVal]
              simp [has, hoob, hp, hpr]; exact hev
          · rw [ite_eq_right hp] at hwp
            rcases hwp with ⟨P, E, ⟨f1, o1, hev1, hok1⟩, hP, hE⟩
            cases o1 with
            | panic c =>
              refine ⟨f1, .panic c, ?_, hE c hok1⟩
              rw [PEvalCode_succ_eq]; dsimp only [PEvalStep, PEvalVal]
              simp only [has, Option.bind_some, ite_eq_right hoob, ite_eq_right hp]
              rw [PEvalCallAt_eq_PEval, hev1]
            | ret r =>
              obtain ⟨f2, out2, hev2, hok2⟩ := PWp_terminates_go m shared kcode jps J (ρ.set x r)
                Q X hJ (hP r hok1)
              let fm := Nat.max f1 f2
              refine ⟨fm, out2, ?_, hok2⟩
              rw [PEvalCode_succ_eq]; dsimp only [PEvalStep, PEvalVal]
              simp only [has, Option.bind_some, ite_eq_right hoob, ite_eq_right hp]
              have h1' : PEvalCallAt m shared fm f vs = some (.ret r) := by
                rw [PEvalCallAt_eq_PEval]; exact PEval_fuel_mono (Nat.le_max_left f1 f2) hev1
              rw [h1']
              exact PEvalCode_fuel_mono (Nat.succ_le_succ (Nat.le_max_right f1 f2)) hev2
    | pap f as =>
      dsimp only [PVal.wp] at hwp
      cases ha : modArityOf m f <;> cases has : ρ.evalArgs as <;> simp [ha, has] at hwp
      rename_i a vs
      obtain ⟨f1, out, hev, hok⟩ := PWp_terminates_go m shared kcode jps J
        (ρ.set x (.clo f a vs)) Q X hJ hwp.2
      refine ⟨f1, out, ?_, hok⟩
      rw [PEvalCode_succ_eq]; dsimp only [PEvalStep, PEvalVal]; simp [ha, has, hwp.1]; exact hev
    | reset _ y =>
      dsimp only [PVal.wp] at hwp
      cases hy : ρ y with
      | none => simp [hy] at hwp
      | some _ =>
        simp only [hy] at hwp
        obtain ⟨f1, out, hev, hok⟩ := PWp_terminates_go m shared kcode jps J (ρ.set x .erased)
          Q X hJ hwp
        refine ⟨f1, out, ?_, hok⟩
        rw [PEvalCode_succ_eq]; dsimp only [PEvalStep, PEvalVal]; simp [hy]; exact hev
    | reuse y ci _ as =>
      dsimp only [PVal.wp] at hwp
      cases hy : ρ y <;> cases has : ρ.evalArgs as <;> simp [hy, has] at hwp
      rename_i vs
      cases hmk : PVal.mkCtor ty ci vs with
      | none => simp [hmk] at hwp
      | some r =>
        simp only [hmk] at hwp
        obtain ⟨f1, out, hev, hok⟩ := PWp_terminates_go m shared kcode jps J (ρ.set x r)
          Q X hJ hwp
        refine ⟨f1, out, ?_, hok⟩
        rw [PEvalCode_succ_eq]; dsimp only [PEvalStep, PEvalVal]; simp [hy, has, hmk]; exact hev
    | box t y =>
      dsimp only [PVal.wp] at hwp
      cases hb : (ρ y).bind (PVal.box t) with
      | none => simp [hb] at hwp
      | some r =>
        simp only [hb] at hwp
        obtain ⟨f1, out, hev, hok⟩ := PWp_terminates_go m shared kcode jps J (ρ.set x r)
          Q X hJ hwp
        refine ⟨f1, out, ?_, hok⟩
        rw [PEvalCode_succ_eq]; dsimp only [PEvalStep, PEvalVal]; simp [hb]; exact hev
    | unbox y =>
      dsimp only [PVal.wp] at hwp
      cases hu : (ρ y).bind (PVal.unbox ty) with
      | none => simp [hu] at hwp
      | some r =>
        simp only [hu] at hwp
        obtain ⟨f1, out, hev, hok⟩ := PWp_terminates_go m shared kcode jps J (ρ.set x r)
          Q X hJ hwp
        refine ⟨f1, out, ?_, hok⟩
        rw [PEvalCode_succ_eq]; dsimp only [PEvalStep, PEvalVal]; simp [hu]; exact hev
    | isShared y =>
      dsimp only [PVal.wp] at hwp
      cases hy : ρ y with
      | none => simp [hy] at hwp
      | some _ =>
        obtain ⟨f1, out, hev, hok⟩ := PWp_terminates_go m shared kcode jps J
          (ρ.set x (PVal.bool shared)) Q X hJ (hwp.2 shared)
        refine ⟨f1, out, ?_, hok⟩
        rw [PEvalCode_succ_eq]; dsimp only [PEvalStep, PEvalVal]; simp [hy]; exact hev
  | .jp j ps body kcode, jps, J, ρ, Q, X, hJ, hwp => by
    dsimp only [PWp] at hwp
    let Jj : List PVal → Prop := fun vs =>
      vs.length = ps.length ∧
      ∃ f out,
        PEvalCode f m shared ((j, ps, body, ρ) :: jps) (ρ.bindAll ps vs) body = some out ∧
        OutcomeOk Q X out
    have hJ' : JPEvalTerm m shared Q X (J.set j Jj) ((j, ps, body, ρ) :: jps) := by
      intro j' vs hmem
      by_cases heq : j' = j
      · subst heq
        simp only [PJEnv.set, ↓reduceIte] at hmem
        refine ⟨ps, body, ρ, jps, ?_, hmem.1, hmem.2⟩
        simp
      · simp only [PJEnv.set] at hmem
        rw [ite_eq_right heq] at hmem
        obtain ⟨ps', body', ρ0', outer, hdw, hlen, hf⟩ := hJ j' vs hmem
        have hne : (j, ps, body, ρ).1 ≠ j' := fun h => heq h.symm
        rw [← dropWhile_ne_cons (·.1) (j, ps, body, ρ) hne jps] at hdw
        exact ⟨ps', body', ρ0', outer, hdw, hlen, hf⟩
    have hcl : ∀ as, as.length = ps.length →
        PWp (modArityOf m) (PEvalInf m shared) (J.set j Jj) (ρ.bindAll ps as) Q X body →
        Jj as := by
      intro as has hbody
      obtain ⟨f, out, hev, hok⟩ :=
        PWp_terminates_go m shared body ((j, ps, body, ρ) :: jps) (J.set j Jj)
          (ρ.bindAll ps as) Q X hJ' hbody
      exact ⟨has, f + 1, out, hev, hok⟩
    obtain ⟨f, out, hev, hok⟩ := PWp_terminates_go m shared kcode ((j, ps, body, ρ) :: jps)
      (J.set j Jj) ρ Q X hJ' (hwp Jj hcl)
    exact ⟨f, out, hev, hok⟩
  | .jmp j as, jps, J, ρ, Q, X, hJ, hwp => by
    dsimp only [PWp] at hwp
    cases has : ρ.evalArgs as with
    | none => simp [has] at hwp
    | some vs =>
      simp only [has] at hwp
      obtain ⟨ps, body, ρ0, outer, hdw, hlen, f, out, hev, hok⟩ := hJ j vs hwp
      refine ⟨f, out, ?_, hok⟩
      rw [PEvalCode_succ_eq]; dsimp only [PEvalStep]
      simp [hdw, has, hlen]
      exact hev
  | .cases x alts, jps, J, ρ, Q, X, hJ, hwp => by
    dsimp only [PWp] at hwp
    cases ht : (ρ x).bind PVal.tag? with
    | none => simp [ht] at hwp
    | some tag =>
      simp only [ht] at hwp
      obtain ⟨f, out, hev, hok⟩ := PWpCtorAlts_terminates_go m shared tag alts jps J ρ Q X
        (fun f' => PEvalDfltAlts m shared (PEvalCallAt m shared f') (PEvalCode f' m shared)
          jps ρ alts)
        hJ (fun hd => PWpDfltAlts_terminates_go m shared alts jps J ρ Q X hJ hd) hwp
      refine ⟨f, out, ?_, hok⟩
      rw [PEvalCode_succ_eq]; dsimp only [PEvalStep]; rw [ht]; exact hev
  | .ret a, jps, J, ρ, Q, X, _, hwp => by
    dsimp only [PWp] at hwp
    cases ha : ρ.evalArg a with
    | none => simp [ha] at hwp
    | some v =>
      simp only [ha] at hwp
      refine ⟨0, .ret v, ?_, hwp⟩
      rw [PEvalCode_succ_eq]; dsimp only [PEvalStep]; simp [ha]
  | .unreach, _, _, _, _, _, _, hwp =>
    ⟨0, .panic panicUnreachable, rfl, hwp⟩
  | .oset x i y kcode, jps, J, ρ, Q, X, hJ, hwp => by
    dsimp only [PWp] at hwp
    cases hx : ρ x <;> cases hy : ρ.evalArg y <;> simp [hx, hy] at hwp
    rename_i xv yv
    cases hs : xv.setObj i yv with
    | none => simp [hs] at hwp
    | some xv' =>
      simp only [hs] at hwp
      obtain ⟨f, out, hev, hok⟩ :=
        PWp_terminates_go m shared kcode jps J (ρ.set x xv') Q X hJ hwp
      refine ⟨f, out, ?_, hok⟩
      rw [PEvalCode_succ_eq]; dsimp only [PEvalStep]; simp [hx, hy, hs]; exact hev
  | .uset x i y kcode, jps, J, ρ, Q, X, hJ, hwp => by
    dsimp only [PWp] at hwp
    cases hx : ρ x <;> cases hy : ρ y <;> simp [hx, hy] at hwp
    rename_i xv yv
    cases hs : xv.setUsize i yv with
    | none => simp [hs] at hwp
    | some xv' =>
      simp only [hs] at hwp
      obtain ⟨f, out, hev, hok⟩ :=
        PWp_terminates_go m shared kcode jps J (ρ.set x xv') Q X hJ hwp
      refine ⟨f, out, ?_, hok⟩
      rw [PEvalCode_succ_eq]; dsimp only [PEvalStep]; simp [hx, hy, hs]; exact hev
  | .sset x n off y ty kcode, jps, J, ρ, Q, X, hJ, hwp => by
    dsimp only [PWp] at hwp
    cases hx : ρ x <;> cases hy : ρ y <;> simp [hx, hy] at hwp
    rename_i xv yv
    cases hs : xv.setScalar n off ty yv with
    | none => simp [hs] at hwp
    | some xv' =>
      simp only [hs] at hwp
      obtain ⟨f, out, hev, hok⟩ :=
        PWp_terminates_go m shared kcode jps J (ρ.set x xv') Q X hJ hwp
      refine ⟨f, out, ?_, hok⟩
      rw [PEvalCode_succ_eq]; dsimp only [PEvalStep]; simp [hx, hy, hs]; exact hev
  | .setTag x cidx kcode, jps, J, ρ, Q, X, hJ, hwp => by
    dsimp only [PWp] at hwp
    cases hs : (ρ x).bind (·.setTag cidx) with
    | none => simp [hs] at hwp
    | some xv' =>
      simp only [hs] at hwp
      obtain ⟨f, out, hev, hok⟩ :=
        PWp_terminates_go m shared kcode jps J (ρ.set x xv') Q X hJ hwp
      refine ⟨f, out, ?_, hok⟩
      rw [PEvalCode_succ_eq]; dsimp only [PEvalStep]; simp [hs]; exact hev
  | .inc _ _ _ kcode, jps, J, ρ, Q, X, hJ, hwp =>
    PWp_terminates_go m shared kcode jps J ρ Q X hJ hwp
  | .dec _ _ _ kcode, jps, J, ρ, Q, X, hJ, hwp =>
    PWp_terminates_go m shared kcode jps J ρ Q X hJ hwp
  | .del _ kcode, jps, J, ρ, Q, X, hJ, hwp =>
    PWp_terminates_go m shared kcode jps J ρ Q X hJ hwp

private theorem PWpCtorAlts_terminates_go (m : LcModule) (shared : Bool) (tag : Nat) :
    ∀ (alts : List (LcPat × LcCode)) (jps : List PJEntry) (J : PJEnv) (ρ : PValEnv)
      (Q : PPost) (X : PXPost) {kDW : Prop} (dfltAt : Nat → Option POutcome),
      JPEvalTerm m shared Q X J jps →
      (kDW → ∃ f out, (∀ f', f ≤ f' → dfltAt f' = some out) ∧ OutcomeOk Q X out) →
      PWpCtorAlts (modArityOf m) (PEvalInf m shared) J ρ Q X tag alts kDW →
      ∃ f out,
        PEvalCtorAlts m shared (PEvalCallAt m shared f) (PEvalCode f m shared)
          jps ρ tag alts (dfltAt f) = some out ∧ OutcomeOk Q X out
  | [], _, _, _, _, _, _, _, _, hd, hwp => by
    obtain ⟨f, out, hdf, hok⟩ := hd hwp
    exact ⟨f, out, hdf f (Nat.le_refl f), hok⟩
  | (.ctor ci _, b) :: rest, jps, J, ρ, Q, X, _, dfltAt, hJ, hd, hwp => by
    dsimp only [PWpCtorAlts] at hwp
    by_cases hci : ci = tag
    · rw [ite_eq_left hci] at hwp
      obtain ⟨f, out, hev, hok⟩ := PWp_terminates_go m shared b jps J ρ Q X hJ hwp
      refine ⟨f, out, ?_, hok⟩
      dsimp only [PEvalCtorAlts]
      rw [ite_eq_left (beq_iff_eq.mpr hci)]
      exact hev
    · rw [ite_eq_right hci] at hwp
      obtain ⟨f, out, hev, hok⟩ :=
        PWpCtorAlts_terminates_go m shared tag rest jps J ρ Q X dfltAt hJ hd hwp
      refine ⟨f, out, ?_, hok⟩
      dsimp only [PEvalCtorAlts]
      rw [ite_eq_right (mt beq_iff_eq.mp hci)]
      exact hev
  | (.dflt, _) :: rest, jps, J, ρ, Q, X, _, dfltAt, hJ, hd, hwp =>
    PWpCtorAlts_terminates_go m shared tag rest jps J ρ Q X dfltAt hJ hd hwp

private theorem PWpDfltAlts_terminates_go (m : LcModule) (shared : Bool) :
    ∀ (alts : List (LcPat × LcCode)) (jps : List PJEntry) (J : PJEnv) (ρ : PValEnv)
      (Q : PPost) (X : PXPost),
      JPEvalTerm m shared Q X J jps →
      PWpDfltAlts (modArityOf m) (PEvalInf m shared) J ρ Q X alts →
      ∃ f out, (∀ f', f ≤ f' →
        PEvalDfltAlts m shared (PEvalCallAt m shared f') (PEvalCode f' m shared)
          jps ρ alts = some out) ∧ OutcomeOk Q X out
  | [], _, _, _, _, _, _, hwp => False.elim hwp
  | (.dflt, b) :: _, jps, J, ρ, Q, X, hJ, hwp => by
    obtain ⟨f, out, hev, hok⟩ := PWp_terminates_go m shared b jps J ρ Q X hJ hwp
    refine ⟨f, out, fun f' hle => ?_, hok⟩
    exact PEvalStep_mono (fun fn args out' hc => PEvalCallAt_mono hle fn args hc)
      (fun jps' ρ' b' out' hj => PEvalCode_fuel_mono hle hj) b jps ρ hev
  | (.ctor _ _, _) :: rest, jps, J, ρ, Q, X, hJ, hwp =>
    PWpDfltAlts_terminates_go m shared rest jps J ρ Q X hJ hwp
end

/-- Termination + soundness of `PWp` under `PEvalInf`: any body satisfying `PWp` under
`PEvalInf` terminates in `PEval` with a satisfying outcome (valid for ALL `LcCode`s). -/
theorem PWp_terminates_PEval {m : LcModule} {d : LcDecl} (hd : d ∈ m.decls)
    {args : List PVal} (hlen : args.length = d.params.length)
    {Q : PPost} {X : PXPost} {shared : Bool}
    (hfind : m.decls.find? (·.name == d.name) = some d)
    (hwp : PWp (modArityOf m) (PEvalInf m shared) PJEnv.empty
      (PValEnv.empty.bindAll d.params args) Q X d.body) :
    ∃ fuel out, PEval fuel m d.name args shared = some out ∧ OutcomeOk Q X out := by
  have _ := hd
  obtain ⟨f, out, hev, hok⟩ := PWp_terminates_go m shared d.body [] PJEnv.empty
    (PValEnv.empty.bindAll d.params args) Q X (fun _ _ hf => False.elim hf) hwp
  refine ⟨f + 1, out, ?_, hok⟩
  dsimp only [PEval]
  simp [hfind, hlen]
  exact hev

/-! ## 2. Completeness of `PEval` wrt `PWp` (`noIsShared` Fragment) and `PWp ⇔ PEval` -/

/-- Whether an `LcVal` avoids demonic `.isShared`. -/
@[expose] def noIsSharedVal : LcVal → Bool
  | .isShared _ => false
  | _ => true

mutual
/-- Whether an `LcCode` tree avoids demonic `.isShared`. -/
@[expose] def noIsSharedCode : LcCode → Bool
  | .let_ _ _ v k => noIsSharedVal v && noIsSharedCode k
  | .jp _ _ body k => noIsSharedCode body && noIsSharedCode k
  | .cases _ alts => noIsSharedAlts alts
  | .oset _ _ _ k | .uset _ _ _ k | .sset _ _ _ _ _ k | .setTag _ _ k
  | .inc _ _ _ k | .dec _ _ _ k | .del _ k => noIsSharedCode k
  | .jmp _ _ | .ret _ | .unreach => true

/-- `noIsSharedCode` over `cases` alternatives. -/
@[expose] def noIsSharedAlts : List (LcPat × LcCode) → Bool
  | [] => true
  | (_, b) :: rest => noIsSharedCode b && noIsSharedAlts rest
end

/-- Whether all declarations in `m` avoid demonic `.isShared`. -/
@[expose] def noIsSharedMod (m : LcModule) : Bool :=
  m.decls.all (fun d => noIsSharedCode d.body)

/-- Join-point completeness invariant up to fuel `k`. -/
@[expose] def JPEvalCompl (m : LcModule) (shared : Bool) (Q : PPost) (X : PXPost)
    (J : PJEnv) (jps : List PJEntry) (k : Nat) : Prop :=
  ∀ j vs ps body ρ0 outer,
    jps.dropWhile (fun e => e.1 != j) = (j, ps, body, ρ0) :: outer →
    vs.length = ps.length →
    (∃ f ≤ k, ∃ out,
      PEvalCode f m shared ((j, ps, body, ρ0) :: outer) (ρ0.bindAll ps vs) body = some out ∧
      OutcomeOk Q X out) →
    J j vs

private theorem PApply_of_PEvalApply {m : LcModule} {shared : Bool} {f : Nat}
    {K : PPost} {X : PXPost} (fn : PVal) (args : List PVal) {out : POutcome}
    (hev : PEvalApply (PEvalCallAt m shared f) fn args = some out) (hok : OutcomeOk K X out) :
    PApply (PEvalInf m shared) fn args K X := by
  cases fn with
  | clo g arity fixed =>
    unfold PEvalApply at hev
    unfold PApply
    by_cases hemp : args.isEmpty = true
    · rw [ite_eq_left hemp] at hev ⊢; cases hev; exact hok
    · rw [ite_eq_right hemp] at hev ⊢
      by_cases hrem : arity - fixed.length = 0
      · rw [dite_eq_left hrem] at hev ⊢; cases hev; exact hok
      · rw [dite_eq_right hrem] at hev ⊢
        by_cases hlt : args.length < arity - fixed.length
        · rw [dite_eq_left hlt] at hev ⊢; cases hev; exact hok
        · rw [dite_eq_right hlt] at hev ⊢
          by_cases heq : args.length = arity - fixed.length
          · rw [dite_eq_left heq] at hev ⊢
            cases out with
            | ret r =>
              refine ⟨fun y => y = r, fun _ => False,
                ⟨f, .ret r, ?_, rfl⟩, fun y hy => by subst hy; exact hok, fun _ hf => False.elim hf⟩
              rw [← PEvalCallAt_eq_PEval]; exact hev
            | panic c =>
              refine ⟨fun _ => False, fun z => z = c, ⟨f, .panic c, ?_, rfl⟩,
                fun _ hf => False.elim hf, fun z hz => by subst hz; exact hok⟩
              rw [← PEvalCallAt_eq_PEval]; exact hev
          · rw [dite_eq_right heq] at hev ⊢
            cases hres : PEvalCallAt m shared f g (fixed ++ args.take (arity - fixed.length)) with
            | none => simp [hres] at hev
            | some o1 =>
              rw [hres] at hev
              rw [PEvalCallAt_eq_PEval] at hres
              cases o1 with
              | panic c =>
                cases hev
                exact ⟨fun _ => False, fun z => z = c, ⟨f, .panic c, hres, rfl⟩,
                  fun _ hf => False.elim hf, fun _ hz => by subst hz; exact hok⟩
              | ret r =>
                exact ⟨fun y => y = r, fun _ => False, ⟨f, .ret r, hres, rfl⟩,
                  fun y hy => by rw [hy]; exact PApply_of_PEvalApply r _ hev hok,
                  fun _ hf => False.elim hf⟩
  | erased | bits _ _ | nat _ | int _ | ctor _ _ _ | str _ | arr _ | barr _ =>
    unfold PEvalApply at hev; unfold PApply; cases hev; exact hok
termination_by args.length
decreasing_by
  simp only [List.length_drop]
  omega

mutual
private theorem PEval_complete_go {m : LcModule} {shared : Bool} {k : Nat}
    (ihJmp : ∀ f < k, ∀ jps J ρ c Q X,
      noIsSharedCode c = true → JPEvalCompl m shared Q X J jps f →
      ∀ out, PEvalCode (f + 1) m shared jps ρ c = some out → OutcomeOk Q X out →
      PWp (modArityOf m) (PEvalInf m shared) J ρ Q X c) :
    ∀ (c : LcCode) (jps : List PJEntry) (J : PJEnv) (ρ : PValEnv) (Q : PPost) (X : PXPost),
      noIsSharedCode c = true → JPEvalCompl m shared Q X J jps k →
      ∀ out, PEvalCode (k + 1) m shared jps ρ c = some out → OutcomeOk Q X out →
      PWp (modArityOf m) (PEvalInf m shared) J ρ Q X c
  | .let_ x ty v kcode, jps, J, ρ, Q, X, hno, hJ, out, hev, hok => by
    simp only [noIsSharedCode, Bool.and_eq_true] at hno
    rcases hno with ⟨hnv, hnk⟩
    rw [PEvalCode_succ_eq] at hev
    dsimp only [PEvalStep] at hev
    dsimp only [PWp]
    cases v with
    | lit l =>
      cases l <;>
        exact PEval_complete_go ihJmp kcode jps J (ρ.set x _) Q X hnk hJ out hev hok
    | erased =>
      exact PEval_complete_go ihJmp kcode jps J (ρ.set x .erased) Q X hnk hJ out hev hok
    | ap f as =>
      dsimp only [PEvalVal] at hev
      dsimp only [PVal.wp]
      cases hf : ρ f <;> cases has : ρ.evalArgs as <;> simp [hf, has] at hev
      rename_i fn vs
      cases hap : PEvalApply (PEvalCallAt m shared k) fn vs with
      | none => simp [hap] at hev
      | some o1 =>
        rw [hap] at hev
        refine PApply_of_PEvalApply fn vs hap ?_
        cases o1 with
        | ret r =>
          exact PEval_complete_go ihJmp kcode jps J (ρ.set x r) Q X hnk hJ out hev hok
        | panic c => cases hev; exact hok
    | ctor ci as =>
      dsimp only [PEvalVal] at hev
      dsimp only [PVal.wp]
      cases has : ρ.evalArgs as with
      | none => simp [has] at hev
      | some vs =>
        simp only [has, Option.bind_some] at hev
        dsimp only
        cases hmk : PVal.mkCtor ty ci vs with
        | none => simp [hmk] at hev
        | some r =>
          simp only [hmk, Option.map_some] at hev
          dsimp only
          exact PEval_complete_go ihJmp kcode jps J (ρ.set x r) Q X hnk hJ out hev hok
    | oproj i y =>
      dsimp only [PEvalVal] at hev
      dsimp only [PVal.wp]
      cases hp : (ρ y).bind (·.getObj? i) with
      | none => simp [hp] at hev
      | some r =>
        simp only [hp, Option.map_some] at hev
        exact PEval_complete_go ihJmp kcode jps J (ρ.set x r) Q X hnk hJ out hev hok
    | uproj i y =>
      dsimp only [PEvalVal] at hev
      dsimp only [PVal.wp]
      cases hp : (ρ y).bind (·.getUsize? i) with
      | none => simp [hp] at hev
      | some r =>
        simp only [hp, Option.map_some] at hev
        exact PEval_complete_go ihJmp kcode jps J (ρ.set x r) Q X hnk hJ out hev hok
    | sproj n off y =>
      dsimp only [PEvalVal] at hev
      dsimp only [PVal.wp]
      cases hp : (ρ y).bind (·.getScalar? n off ty) with
      | none => simp [hp] at hev
      | some r =>
        simp only [hp, Option.map_some] at hev
        exact PEval_complete_go ihJmp kcode jps J (ρ.set x r) Q X hnk hJ out hev hok
    | fap f as =>
      dsimp only [PEvalVal] at hev
      dsimp only [PVal.wp]
      cases has : ρ.evalArgs as with
      | none => simp [has] at hev
      | some vs =>
        simp only [has, Option.bind_some] at hev
        dsimp only
        by_cases hoob : (f == "outOfBounds._redArg") = true
        · rw [ite_eq_left hoob] at hev ⊢
          by_cases hlen : (vs.length == 1) = true
          · rw [ite_eq_left hlen] at hev ⊢; cases hev; exact hok
          · rw [ite_eq_right hlen] at hev; simp at hev
        · rw [ite_eq_right hoob] at hev ⊢
          by_cases hp : pIsPrimName f = true
          · rw [ite_eq_left hp] at hev ⊢
            cases hpr : primP f vs with
            | none => simp [hpr] at hev
            | some r =>
              simp only [hpr, Option.map_some] at hev
              exact PEval_complete_go ihJmp kcode jps J (ρ.set x r) Q X hnk hJ out hev hok
          · rw [ite_eq_right hp] at hev ⊢
            cases hres : PEvalCallAt m shared k f vs with
            | none => simp [hres] at hev
            | some o1 =>
              rw [hres] at hev
              rw [PEvalCallAt_eq_PEval] at hres
              cases o1 with
              | ret r =>
                refine ⟨fun y => y = r, fun _ => False, ⟨k, .ret r, hres, rfl⟩,
                  fun y hy => ?_, fun _ hf => False.elim hf⟩
                rw [hy]
                exact PEval_complete_go ihJmp kcode jps J (ρ.set x r) Q X hnk hJ out hev hok
              | panic c =>
                cases hev
                exact ⟨fun _ => False, fun z => z = c, ⟨k, .panic c, hres, rfl⟩,
                  fun _ hf => False.elim hf, fun _ hz => by subst hz; exact hok⟩
    | pap f as =>
      dsimp only [PEvalVal] at hev
      dsimp only [PVal.wp]
      cases ha : modArityOf m f <;> cases has : ρ.evalArgs as <;> simp [ha, has] at hev
      rename_i a vs
      dsimp only
      by_cases hlt : vs.length < a
      · rw [ite_eq_left hlt] at hev ⊢
        exact PEval_complete_go ihJmp kcode jps J (ρ.set x (.clo f a vs)) Q X hnk hJ out hev hok
      · rw [ite_eq_right hlt] at hev; simp at hev
    | reset _ y =>
      dsimp only [PEvalVal] at hev
      dsimp only [PVal.wp]
      cases hy : ρ y with
      | none => simp [hy] at hev
      | some _ =>
        simp only [hy, Option.map_some] at hev
        exact PEval_complete_go ihJmp kcode jps J (ρ.set x .erased) Q X hnk hJ out hev hok
    | reuse y ci _ as =>
      dsimp only [PEvalVal] at hev
      dsimp only [PVal.wp]
      cases hy : ρ y <;> cases has : ρ.evalArgs as <;> simp [hy, has] at hev
      rename_i vs
      dsimp only
      cases hmk : PVal.mkCtor ty ci vs with
      | none => simp [hmk] at hev
      | some r =>
        simp only [hmk, Option.map_some] at hev
        dsimp only
        exact PEval_complete_go ihJmp kcode jps J (ρ.set x r) Q X hnk hJ out hev hok
    | box t y =>
      dsimp only [PEvalVal] at hev
      dsimp only [PVal.wp]
      cases hb : (ρ y).bind (PVal.box t) with
      | none => simp [hb] at hev
      | some r =>
        simp only [hb, Option.map_some] at hev
        exact PEval_complete_go ihJmp kcode jps J (ρ.set x r) Q X hnk hJ out hev hok
    | unbox y =>
      dsimp only [PEvalVal] at hev
      dsimp only [PVal.wp]
      cases hu : (ρ y).bind (PVal.unbox ty) with
      | none => simp [hu] at hev
      | some r =>
        simp only [hu, Option.map_some] at hev
        exact PEval_complete_go ihJmp kcode jps J (ρ.set x r) Q X hnk hJ out hev hok
    | isShared _ => simp [noIsSharedVal] at hnv
  | .jp j ps body kcode, jps, J, ρ, Q, X, hno, hJ, out, hev, hok => by
    simp only [noIsSharedCode, Bool.and_eq_true] at hno
    rcases hno with ⟨hnb, hnk⟩
    rw [PEvalCode_succ_eq] at hev
    dsimp only [PEvalStep] at hev
    dsimp only [PWp]
    intro Jj hcl
    have hJall : ∀ f ≤ k, JPEvalCompl m shared Q X (J.set j Jj) ((j, ps, body, ρ) :: jps) f := by
      intro f
      induction f using Nat.strongRecOn with
      | _ f ihf =>
        intro hf j' vs ps' body' ρ0' outer hdw hlen ⟨g, hg, out', hev', hok'⟩
        by_cases heq : j' = j
        · rw [heq] at hdw hev'
          simp only [List.dropWhile_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
            List.cons.injEq, Prod.mk.injEq] at hdw
          rcases hdw with ⟨⟨_, hps, hbody, hρ⟩, houter⟩
          subst hps hbody hρ houter
          simp only [PJEnv.set, heq, ↓reduceIte]
          cases g with
          | zero => simp [PEvalCode] at hev'
          | succ g' =>
            have hgf : g' < f := by omega
            have hgk : g' < k := by omega
            exact hcl vs hlen (ihJmp g' hgk ((j, ps, body, ρ) :: jps) (J.set j Jj)
              (ρ.bindAll ps vs) body Q X hnb (ihf g' hgf (by omega)) out' hev' hok')
        · have hne : (j, ps, body, ρ).1 ≠ j' := fun h => heq h.symm
          rw [dropWhile_ne_cons (·.1) (j, ps, body, ρ) hne jps] at hdw
          simp only [PJEnv.set]
          rw [ite_eq_right heq]
          exact hJ j' vs ps' body' ρ0' outer hdw hlen ⟨g, by omega, out', hev', hok'⟩
    exact PEval_complete_go ihJmp kcode ((j, ps, body, ρ) :: jps) (J.set j Jj) ρ Q X hnk
      (hJall k (Nat.le_refl k)) out hev hok
  | .jmp j as, jps, J, ρ, Q, X, _, hJ, out, hev, hok => by
    rw [PEvalCode_succ_eq] at hev
    dsimp only [PEvalStep] at hev
    dsimp only [PWp]
    cases hdw : jps.dropWhile (fun e => e.1 != j) with
    | nil => simp [hdw] at hev
    | cons hd outer =>
      rcases hd with ⟨j1, ps, body, ρ0⟩
      cases has : ρ.evalArgs as with
      | none => simp [hdw, has] at hev
      | some vs =>
        simp only [hdw, has] at hev ⊢
        have hj1 : j1 = j := dropWhile_head_fst (·.1) j jps hdw
        subst hj1
        by_cases hlen : (vs.length == ps.length) = true
        · rw [ite_eq_left hlen] at hev
          exact hJ j1 vs ps body ρ0 outer hdw (beq_iff_eq.mp hlen)
            ⟨k, Nat.le_refl k, out, hev, hok⟩
        · rw [ite_eq_right hlen] at hev; simp at hev
  | .cases x alts, jps, J, ρ, Q, X, hno, hJ, out, hev, hok => by
    dsimp only [noIsSharedCode] at hno
    rw [PEvalCode_succ_eq] at hev
    dsimp only [PEvalStep] at hev
    dsimp only [PWp]
    cases ht : (ρ x).bind PVal.tag? with
    | none => simp [ht] at hev
    | some tag =>
      simp only [ht] at hev
      exact PEvalCtorAlts_complete_go ihJmp tag alts jps J ρ Q X hno hJ
        (fun hevd hokd => PEvalDfltAlts_complete_go ihJmp alts jps J ρ Q X hno hJ hevd hokd)
        out hev hok
  | .ret a, _, _, ρ, _, _, _, _, out, hev, hok => by
    rw [PEvalCode_succ_eq] at hev
    dsimp only [PEvalStep] at hev
    dsimp only [PWp]
    cases ha : ρ.evalArg a with
    | none => simp [ha] at hev
    | some v => simp only [ha, Option.map_some] at hev; cases hev; exact hok
  | .unreach, _, _, _, _, _, _, _, out, hev, hok => by
    rw [PEvalCode_succ_eq] at hev
    dsimp only [PEvalStep] at hev; cases hev; exact hok
  | .oset x i y kcode, jps, J, ρ, Q, X, hno, hJ, out, hev, hok => by
    dsimp only [noIsSharedCode] at hno
    rw [PEvalCode_succ_eq] at hev
    dsimp only [PEvalStep] at hev
    dsimp only [PWp]
    cases hx : ρ x <;> cases hy : ρ.evalArg y <;> simp [hx, hy] at hev
    rename_i xv yv
    cases hs : xv.setObj i yv with
    | none => simp [hs] at hev
    | some xv' =>
      simp only [hs] at hev
      dsimp only
      simp only [hs]
      exact PEval_complete_go ihJmp kcode jps J (ρ.set x xv') Q X hno hJ out hev hok
  | .uset x i y kcode, jps, J, ρ, Q, X, hno, hJ, out, hev, hok => by
    dsimp only [noIsSharedCode] at hno
    rw [PEvalCode_succ_eq] at hev
    dsimp only [PEvalStep] at hev
    dsimp only [PWp]
    cases hx : ρ x <;> cases hy : ρ y <;> simp [hx, hy] at hev
    rename_i xv yv
    cases hs : xv.setUsize i yv with
    | none => simp [hs] at hev
    | some xv' =>
      simp only [hs] at hev
      dsimp only
      simp only [hs]
      exact PEval_complete_go ihJmp kcode jps J (ρ.set x xv') Q X hno hJ out hev hok
  | .sset x n off y ty kcode, jps, J, ρ, Q, X, hno, hJ, out, hev, hok => by
    dsimp only [noIsSharedCode] at hno
    rw [PEvalCode_succ_eq] at hev
    dsimp only [PEvalStep] at hev
    dsimp only [PWp]
    cases hx : ρ x <;> cases hy : ρ y <;> simp [hx, hy] at hev
    rename_i xv yv
    cases hs : xv.setScalar n off ty yv with
    | none => simp [hs] at hev
    | some xv' =>
      simp only [hs] at hev
      dsimp only
      simp only [hs]
      exact PEval_complete_go ihJmp kcode jps J (ρ.set x xv') Q X hno hJ out hev hok
  | .setTag x cidx kcode, jps, J, ρ, Q, X, hno, hJ, out, hev, hok => by
    dsimp only [noIsSharedCode] at hno
    rw [PEvalCode_succ_eq] at hev
    dsimp only [PEvalStep] at hev
    dsimp only [PWp]
    cases hs : (ρ x).bind (·.setTag cidx) with
    | none => simp [hs] at hev
    | some xv' =>
      simp only [hs] at hev
      exact PEval_complete_go ihJmp kcode jps J (ρ.set x xv') Q X hno hJ out hev hok
  | .inc _ _ _ kcode, jps, J, ρ, Q, X, hno, hJ, out, hev, hok =>
    PEval_complete_go ihJmp kcode jps J ρ Q X hno hJ out hev hok
  | .dec _ _ _ kcode, jps, J, ρ, Q, X, hno, hJ, out, hev, hok =>
    PEval_complete_go ihJmp kcode jps J ρ Q X hno hJ out hev hok
  | .del _ kcode, jps, J, ρ, Q, X, hno, hJ, out, hev, hok =>
    PEval_complete_go ihJmp kcode jps J ρ Q X hno hJ out hev hok

private theorem PEvalCtorAlts_complete_go {m : LcModule} {shared : Bool} {k : Nat}
    (ihJmp : ∀ f < k, ∀ jps J ρ c Q X,
      noIsSharedCode c = true → JPEvalCompl m shared Q X J jps f →
      ∀ out, PEvalCode (f + 1) m shared jps ρ c = some out → OutcomeOk Q X out →
      PWp (modArityOf m) (PEvalInf m shared) J ρ Q X c)
    (tag : Nat) :
    ∀ (alts : List (LcPat × LcCode)) (jps : List PJEntry) (J : PJEnv) (ρ : PValEnv)
      (Q : PPost) (X : PXPost) {kDW : Prop} {kDE : Option POutcome},
      noIsSharedAlts alts = true → JPEvalCompl m shared Q X J jps k →
      (∀ {out}, kDE = some out → OutcomeOk Q X out → kDW) →
      ∀ out, PEvalCtorAlts m shared (PEvalCallAt m shared k) (PEvalCode k m shared)
        jps ρ tag alts kDE = some out → OutcomeOk Q X out →
      PWpCtorAlts (modArityOf m) (PEvalInf m shared) J ρ Q X tag alts kDW
  | [], _, _, _, _, _, _, _, _, _, hd, _, hev, hok => hd hev hok
  | (.ctor ci _, b) :: rest, jps, J, ρ, Q, X, _, _, hno, hJ, hd, out, hev, hok => by
    simp only [noIsSharedAlts, Bool.and_eq_true] at hno
    dsimp only [PEvalCtorAlts] at hev
    dsimp only [PWpCtorAlts]
    by_cases hci : ci = tag
    · rw [ite_eq_left (beq_iff_eq.mpr hci)] at hev
      rw [ite_eq_left hci]
      exact PEval_complete_go ihJmp b jps J ρ Q X hno.1 hJ out hev hok
    · rw [ite_eq_right (mt beq_iff_eq.mp hci)] at hev
      rw [ite_eq_right hci]
      exact PEvalCtorAlts_complete_go ihJmp tag rest jps J ρ Q X hno.2 hJ hd out hev hok
  | (.dflt, _) :: rest, jps, J, ρ, Q, X, _, _, hno, hJ, hd, out, hev, hok => by
    simp only [noIsSharedAlts, Bool.and_eq_true] at hno
    exact PEvalCtorAlts_complete_go ihJmp tag rest jps J ρ Q X hno.2 hJ hd out hev hok

private theorem PEvalDfltAlts_complete_go {m : LcModule} {shared : Bool} {k : Nat}
    (ihJmp : ∀ f < k, ∀ jps J ρ c Q X,
      noIsSharedCode c = true → JPEvalCompl m shared Q X J jps f →
      ∀ out, PEvalCode (f + 1) m shared jps ρ c = some out → OutcomeOk Q X out →
      PWp (modArityOf m) (PEvalInf m shared) J ρ Q X c) :
    ∀ (alts : List (LcPat × LcCode)) (jps : List PJEntry) (J : PJEnv) (ρ : PValEnv)
      (Q : PPost) (X : PXPost),
      noIsSharedAlts alts = true → JPEvalCompl m shared Q X J jps k →
      ∀ {out}, PEvalDfltAlts m shared (PEvalCallAt m shared k) (PEvalCode k m shared)
        jps ρ alts = some out → OutcomeOk Q X out →
      PWpDfltAlts (modArityOf m) (PEvalInf m shared) J ρ Q X alts
  | [], _, _, _, _, _, _, _, _, hev, _ => by simp [PEvalDfltAlts] at hev
  | (.dflt, b) :: _, jps, J, ρ, Q, X, hno, hJ, out, hev, hok => by
    simp only [noIsSharedAlts, Bool.and_eq_true] at hno
    exact PEval_complete_go ihJmp b jps J ρ Q X hno.1 hJ out hev hok
  | (.ctor _ _, _) :: rest, jps, J, ρ, Q, X, hno, hJ, out, hev, hok => by
    simp only [noIsSharedAlts, Bool.and_eq_true] at hno
    exact PEvalDfltAlts_complete_go ihJmp rest jps J ρ Q X hno.2 hJ hev hok
end

private theorem PEvalCode_complete_PWp {m : LcModule} {shared : Bool} :
    ∀ k jps J ρ c Q X,
      noIsSharedCode c = true →
      JPEvalCompl m shared Q X J jps k →
      ∀ out, PEvalCode (k + 1) m shared jps ρ c = some out → OutcomeOk Q X out →
      PWp (modArityOf m) (PEvalInf m shared) J ρ Q X c := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro jps J ρ c Q X hno hJ out hev hok
    exact PEval_complete_go
      (fun f hf jps' J' ρ' c' Q' X' hno' hJ' out' hev' hok' =>
        ih f hf jps' J' ρ' c' Q' X' hno' hJ' out' hev' hok')
      c jps J ρ Q X hno hJ out hev hok

/-- Completeness of `PEval` wrt `PWp` on `.isShared`-free code: if `PEval` succeeds with a
satisfying outcome, then `PWp` holds under `PEvalInf`. -/
theorem PEval_complete_PWp {m : LcModule} {d : LcDecl} (hno : noIsSharedCode d.body = true)
    {fuel : Nat} {args : List PVal} {Q : PPost} {X : PXPost}
    {shared : Bool} {out : POutcome}
    (hfind : m.decls.find? (·.name == d.name) = some d)
    (hlen : args.length = d.params.length)
    (hev : PEval fuel m d.name args shared = some out) (hok : OutcomeOk Q X out) :
    PWp (modArityOf m) (PEvalInf m shared) PJEnv.empty
      (PValEnv.empty.bindAll d.params args) Q X d.body := by
  dsimp only [PEval] at hev
  rw [hfind] at hev
  simp only [hlen, beq_self_eq_true, ↓reduceIte] at hev
  cases fuel with
  | zero => simp [PEvalCode] at hev
  | succ f =>
    refine PEvalCode_complete_PWp f [] PJEnv.empty (PValEnv.empty.bindAll d.params args)
      d.body Q X hno ?_ out hev hok
    intro j vs ps body ρ0 outer hdw _ _
    simp at hdw

/-- Every `.isShared`-free module satisfies `PModuleOk (PEvalInf m shared) m` whenever `m.decls`
has distinct names (i.e. `m.decls.find? (·.name == d.name) = some d` for all `d ∈ m.decls`). -/
theorem PModuleOk_PEvalInf {m : LcModule} (hno : noIsSharedMod m = true)
    (hnodup : ∀ d ∈ m.decls, m.decls.find? (·.name == d.name) = some d) (shared : Bool) :
    PModuleOk (PEvalInf m shared) m := by
  intro d hd as Q X hlen ⟨fuel, out, hev, hok⟩
  have hdb : noIsSharedCode d.body = true := (List.all_eq_true.mp hno) d hd
  exact PEval_complete_PWp hdb (hnodup d hd) hlen hev hok

/-- Full adequacy (`PWp ⇔ PEval`) on the `.isShared`-free fragment. -/
theorem PWp_iff_PEval {m : LcModule} {d : LcDecl} (hd : d ∈ m.decls)
    (hno : noIsSharedCode d.body = true)
    (hfind : m.decls.find? (·.name == d.name) = some d)
    {args : List PVal} (hlen : args.length = d.params.length)
    {Q : PPost} {X : PXPost} {shared : Bool} :
    PWp (modArityOf m) (PEvalInf m shared) PJEnv.empty
      (PValEnv.empty.bindAll d.params args) Q X d.body ↔
    ∃ fuel out, PEval fuel m d.name args shared = some out ∧ OutcomeOk Q X out :=
  ⟨PWp_terminates_PEval hd hlen hfind, fun ⟨_, _, hev, hok⟩ =>
    PEval_complete_PWp hno hfind hlen hev hok⟩

end LeanQbe.T.LeanLCNF.Sem
