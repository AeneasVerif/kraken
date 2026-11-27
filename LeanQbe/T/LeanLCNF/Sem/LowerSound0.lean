module

public import LeanQbe.T.LeanLCNF.LExprSem
public import LeanQbe.T.LeanLCNF.Sem.H
public import LeanQbe.T.LeanLCNF.Sem.SpecNormProof
public import LeanQbe.T.LeanLCNF.LcnfC0LinkKit

/-!
# Generic `H → T` Lowering Simulation Foundation (`LowerSound0`)

Canonical specification and invariant layer bridging `Lower1` (`LM` named-SSA builder),
`LExprSem` (`L1`, `LExpr.wp`), and Tier-H heap semantics (`L2`, `HWp`, `liftDeclSpec`,
`liftSpec`, `liftEnv`):

1. **Phase-1 First-Order Fragment (`LcModule.inFirstOrderFragment : Bool`)**:
   Decidable, kernel-reducible fragment mirroring `Lower1` + `Sem.H` Phase-1 constructs:
   `ctor`, `oproj`, `uproj`, `sproj`, `box`, `unbox`, first-order `fap` + supported primitives,
   `inc`/`dec`, `cases`, `jp`/`jmp`, `ret`, `unreach`, and self-tail loops.
2. **`LM` Fresh-Counter & Scope Infrastructure**:
   `argIdsBelow`, `ctxIdsBelow`, non-interference for `VEnv.set`/`VEnv.bind`/`JEnv.set`, and
   exact characterization of `ts.mapM freshVar` (`mkFreshVars`, `mapM_freshVar_run`,
   `evalArgs_bind_mkFreshVars`).
3. **Env-Parametric Call-Environment Assumption (`HCallEnvOk`)**:
   `envJoin`, `rtCoreCallSigs`, `rtCoreCallEnv`, `HCallEnvOk m Δ Γ` (`Γ ≥ liftEnv m Δ ⊔
   rtCoreCallEnv`), `HSpec.RetTyped`, `HEnv.RetTyped`, and direct bridges for both acyclic
   `LinkedCert` (`linkRtC0Env`) and recursive `LinkedCertScc` (`BudgetEnv.semScc`).
4. **Canonical `H ↔ LExpr` Simulation Invariant (`HSimInv`)**:
   `LEnvOk`, `VarRel`, `HPostRel`, `HXPostRel`, `JpRel`, `LoopRel`, `HSimInv`, and their
   monotonicity, freshness-preservation, and argument-evaluation lemmas.

See `LowerSound0Bridge.lean` for the `lowerModule` structural lemmas and exact compositional
declaration bridge theorems (`finishFn_wp_of_lExpr`, `loadExtras_wp`, `lowerDecl_of_body_sim`,
`lowerDecl_loop_of_body_sim`).
-/

set_option autoImplicit false

public section

/-! ## 1. Phase-1 First-Order Fragment Predicate (`LcModule.inFirstOrderFragment`) -/

namespace LeanQbe.T.LeanLCNF

open LeanQbe.T
open LeanQbe.T.LeanLCNF.Sem

/-- Supported Phase-1 `Nat.*` primitives (matching `Lower.natPrim` and `Sem.HNatPrimWp`). -/
@[expose] def isPhase1NatPrim (op : String) (arity : Nat) (retTy : LcTy) : Bool :=
  match op, arity with
  | "add", 2 | "sub", 2 | "mul", 2 | "div", 2 | "mod", 2
  | "shiftRight", 2 | "land", 2 | "lor", 2 | "xor", 2 | "shiftLeft", 2
  | "pow", 2 | "gcd", 2 | "pred", 1 | "log2", 1 | "reprFast", 1 => retTy.width == 64
  | "decEq", 2 | "beq", 2 | "decLt", 2 | "blt", 2 | "decLe", 2 | "ble", 2 => retTy.width == 8
  | _, _ => false

/-- Supported Phase-1 `UIntN.*` / `USize.*` primitives (`Lower.uintPrim` / `Sem.HUintPrimWp`). -/
@[expose] def isPhase1UintPrim (w : Nat) (op : String) (arity : Nat) (retTy : LcTy) : Bool :=
  match op, arity with
  | "add", 2 | "sub", 2 | "mul", 2 | "land", 2 | "lor", 2 | "xor", 2
  | "shiftLeft", 2 | "shiftRight", 2 | "div", 2 | "mod", 2
  | "complement", 1 | "neg", 1
  | "ofNat", 1 | "ofNatLT", 1 | "ofNatLT", 2 | "ofBitVec", 1 => retTy.width == w
  | "decEq", 2 | "beq", 2 | "decLt", 2 | "blt", 2 | "decLe", 2 | "ble", 2
  | "toUInt8", 1 => retTy.width == 8
  | "toUInt16", 1 => retTy.width == 16
  | "toUInt32", 1 => retTy.width == 32
  | "toUInt64", 1 | "toUSize", 1 | "toNat", 1 | "toBitVec", 1 => retTy.width == 64
  | _, _ => false

/-- Supported Phase-1 `String.*` primitives (`Lower.stringPrim` / `Sem.HStringPrimWp`). -/
@[expose] def isPhase1StringPrim (parts : List String) (arity : Nat) (retTy : LcTy) : Bool :=
  match parts, arity with
  | ["length"], 1 | ["Internal", "length"], 1 | ["utf8ByteSize"], 1
  | ["propagateMark"], 2 | ["append"], 2 | ["Internal", "append"], 2 => retTy.width == 64
  | ["decEq"], 2 | ["decidableLT"], 2 => retTy.width == 8
  | _, _ => false

/-- Supported Phase-1 `Array.*` primitives (`Lower.arrayPrim` / `Sem.HArrayPrimWp`). -/
@[expose] def isPhase1ArrayPrim (op : String) (arity : Nat) (retTy : LcTy) : Bool :=
  match op, arity with
  | "empty", 1 | "size", 2 | "usize", 2 | "mkEmpty", 2 | "emptyWithCapacity", 2
  | "push", 3 | "get!Internal", 4 | "get!InternalBorrowed", 4
  | "propagateMark", 4 | "set!", 4 | "set", 5 => retTy.width == 64
  | _, _ => false

/-- Supported Phase-1 `ByteArray.*` primitives (`Lower.byteArrayPrim` / `Sem.HByteArrayPrimWp`). -/
@[expose] def isPhase1ByteArrayPrim (op : String) (arity : Nat) (retTy : LcTy) : Bool :=
  match op, arity with
  | "size", 1 | "usize", 1 | "propagateMark", 2 | "push", 2 => retTy.width == 64
  | "get!", 2 | "get", 3 => retTy.width == 8
  | _, _ => false

/-- Decidable classifier for built-in primitives supported by Phase-1 `H → T` simulation. -/
@[expose] def isPhase1Prim (name : String) (arity : Nat) (retTy : LcTy) : Bool :=
  match splitDot name with
  | ["Nat", op] => isPhase1NatPrim op arity retTy
  | ["Array", op] => isPhase1ArrayPrim op arity retTy
  | "String" :: rest => isPhase1StringPrim rest arity retTy
  | ["ByteArray", op] => isPhase1ByteArrayPrim op arity retTy
  | ["System", "Platform", "getNumBits"] => retTy.width == 64
  | ["getObjTagNat"] => (arity == 1 || arity == 2) && retTy.width == 64
  | [ty, op] =>
    match uintWidth? ty with
    | some w => isPhase1UintPrim w op arity retTy
    | none => false
  | _ => false

/-- Arguments match parameter types in length and never pass `.erased` to a scalar slot (so
`Lower1.argAt` agrees with `HValEnv.evalArgOwn` on `.erased` → `1#64`). -/
@[expose] def argsOkForTys : List LcArg → List LcTy → Bool
  | [], [] => true
  | .erased :: as, t :: ts => !t.isScalar && argsOkForTys as ts
  | .var _ :: as, _ :: ts => argsOkForTys as ts
  | _, _ => false

/-- Phase-1 fragment check for a single `LcVal` bound at type `ty`. -/
@[expose] def LcVal.inFirstOrder (decls : List LcDecl) (ty : LcTy) : LcVal → Bool
  | .lit (.nat n) => decide (n < 2 ^ 63) && ty.width == 64
  | .lit (.scalar _) => true
  | .lit (.str _) => false
  | .erased => true
  | .ap _ _ => false
  | .ctor ci as =>
    if ci.isScalar then true
    else ty.width == 64 && as.length == ci.size
  | .oproj _ _ | .uproj _ _ => ty.width == 64
  | .sproj _ _ _ => true
  | .fap f as =>
    match decls.find? (·.name == f) with
    | some d =>
      !isPrimName f && decide (d.params.length ≤ regArgs) &&
        argsOkForTys as (d.params.map (·.ty))
    | none => isPhase1Prim f as.length ty
  | .pap _ _ => false
  | .reset _ _ | .reuse _ _ _ _ | .isShared _ => false
  | .box t _ =>
    match t with
    | .uint8 | .uint16 | .uint32 | .uint64 | .usize | .float => ty.width == 64
    | _ => ty.width == t.width
  | .unbox _ => true

mutual
/-- Phase-1 fragment check for impure `LcCode` under module declarations `decls` and in-scope join
points `jps`. -/
@[expose] def LcCode.inFirstOrder (decls : List LcDecl)
    (jps : List (Nat × List LcTy)) : LcCode → Bool
  | .let_ _ ty v k => v.inFirstOrder decls ty && k.inFirstOrder decls jps
  | .jp j ps body k =>
    let jps' := (j, ps.map (·.ty)) :: jps
    body.inFirstOrder decls jps' && k.inFirstOrder decls jps'
  | .jmp j as =>
    match jps.lookup j with
    | some ts => argsOkForTys as ts
    | none => false
  | .cases _ alts => LcAlts.inFirstOrder decls jps alts
  | .ret _ | .unreach => true
  | .inc _ _ _ k | .dec _ _ _ k => k.inFirstOrder decls jps
  | .oset _ _ _ _ | .uset _ _ _ _ | .sset _ _ _ _ _ _ | .setTag _ _ _ | .del _ _ => false

/-- Phase-1 fragment check for `cases` alternatives (all constructor tags `< 256`). -/
@[expose] def LcAlts.inFirstOrder (decls : List LcDecl)
    (jps : List (Nat × List LcTy)) : List (LcPat × LcCode) → Bool
  | [] => true
  | (p, b) :: rest =>
    let patOk := match p with | .ctor ci _ => decide (ci < 256) | .dflt => true
    patOk && b.inFirstOrder decls jps && LcAlts.inFirstOrder decls jps rest
end

/-- Phase-1 fragment check for one declaration in `decls`. -/
@[expose] def LcDecl.inFirstOrder (decls : List LcDecl) (d : LcDecl) : Bool :=
  !isPrimName d.name &&
  !(d.params.isEmpty && !d.retTy.isScalar) &&
  decide (d.params.length ≤ regArgs + rtExtraSlots) &&
  d.body.inFirstOrder decls []

/-- Exact Phase-1 first-order fragment predicate for a whole `LcModule`:
no closures (`pap`/`ap`), no closed non-scalar constants or once-cell literals, distinct
declaration and mangled symbol names disjoint from primitives, parameter count within ABI spill
slots, and every declaration body in the supported Phase-1 construct subset. -/
@[expose] def LcModule.inFirstOrderFragment (m : LcModule) : Bool :=
  symsNodup (m.decls.map (·.name)) &&
  symsNodup (m.decls.map fun d => mangleLc d.name) &&
  m.decls.all (LcDecl.inFirstOrder m.decls)

end LeanQbe.T.LeanLCNF

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF
open LeanQbe.T.Frontend.C0
open Std.ExtHashMap

/-! ## 2. `VEnv` / `JEnv` & `LM` Fresh-Counter Invariants -/

private theorem castTy_self' {V : Ty → Type} : (t : Ty) → (v : V t) → castTy t t v = some v
  | .bool, _ => rfl
  | .bits _, _ => by dsimp only [castTy]; simp
  | .float _, _ => by dsimp only [castTy]; simp
  | .pair a b, _ => by
    dsimp only [castTy]
    cases ha : tyDecEq a a with
    | isFalse hne => exact absurd rfl hne
    | isTrue ea =>
      cases hb : tyDecEq b b with
      | isFalse hne => exact absurd rfl hne
      | isTrue eb =>
        have ha' : ea = rfl := rfl
        have hb' : eb = rfl := rfl
        rw [ha', hb']

private theorem castListTy_self' {L : List Ty → Type} (ts : List Ty) (l : L ts) :
    castListTy ts ts l = some l := by
  dsimp only [castListTy]
  cases h : listTyDecEq ts ts with
  | isFalse hne => exact absurd rfl hne
  | isTrue heq =>
    have h' : heq = rfl := rfl
    rw [h']

/-- All variable IDs mentioned by an `LArg` are strictly below counter `n`. -/
@[expose] def argIdsBelow (a : LArg) (n : Nat) : Prop :=
  match a with
  | .var id _ => id < n
  | .imm _ _ => True

/-- Every variable and label ID stored in `LCtx` is strictly below counter `n`. -/
@[expose] def ctxIdsBelow (c : LCtx) (n : Nat) : Prop :=
  argIdsBelow c.rt n ∧
  (∀ entry ∈ c.vars, argIdsBelow entry.2.1 n) ∧
  (∀ entry ∈ c.jps, entry.2.1 < n) ∧
  (∀ lbl, c.loop? = some lbl → lbl < n)

theorem argIdsBelow_mono {a : LArg} {n m : Nat} (hle : n ≤ m) (h : argIdsBelow a n) :
    argIdsBelow a m := by
  cases a with
  | var _ _ => exact Nat.lt_of_lt_of_le h hle
  | imm _ _ => trivial

theorem argIdsBelow_imm (t : Ty) (v : Val t) (n : Nat) : argIdsBelow (.imm t v) n :=
  trivial

theorem argIdsBelow_vArg {v : Frontend.C0.LVar} {n : Nat} (h : v.id < n) : argIdsBelow (vArg v) n :=
  h

theorem ctxIdsBelow_mono {c : LCtx} {n m : Nat} (hle : n ≤ m) (h : ctxIdsBelow c n) :
    ctxIdsBelow c m :=
  ⟨argIdsBelow_mono hle h.1,
   fun e he => argIdsBelow_mono hle (h.2.1 e he),
   fun e he => Nat.lt_of_lt_of_le (h.2.2.1 e he) hle,
   fun lbl hlbl => Nat.lt_of_lt_of_le (h.2.2.2 lbl hlbl) hle⟩

theorem ctxIdsBelow_bind {c : LCtx} {x : Nat} {a : LArg} {ty : LcTy} {n : Nat}
    (hc : ctxIdsBelow c n) (ha : argIdsBelow a n) : ctxIdsBelow (c.bind x a ty) n := by
  refine ⟨hc.1, ?_, hc.2.2.1, hc.2.2.2⟩
  intro e he
  rcases List.mem_cons.mp he with rfl | he'
  · exact ha
  · exact hc.2.1 e he'

theorem ctxIdsBelow_bindAll {ps : List LcParam} {as : List LArg} {c : LCtx} {n : Nat}
    (hc : ctxIdsBelow c n) (has : ∀ a ∈ as, argIdsBelow a n) :
    ctxIdsBelow (c.bindAll ps as) n := by
  induction ps generalizing as c with
  | nil => simpa [LCtx.bindAll] using hc
  | cons p ps ih =>
    cases as with
    | nil => simpa [LCtx.bindAll] using hc
    | cons a as =>
      simp only [LCtx.bindAll, List.zip_cons_cons, List.foldl_cons]
      exact ih (ctxIdsBelow_bind hc (has a (List.mem_cons_self ..)))
        (fun a' ha' => has a' (List.mem_cons_of_mem _ ha'))

theorem ctxIdsBelow_pushJp {c : LCtx} {j lbl : Nat} {ts : List LcTy} {n : Nat}
    (hc : ctxIdsBelow c n) (hlbl : lbl < n) :
    ctxIdsBelow { c with jps := (j, lbl, ts) :: c.jps } n := by
  refine ⟨hc.1, hc.2.1, ?_, hc.2.2.2⟩
  intro e he
  rcases List.mem_cons.mp he with rfl | he'
  · exact hlbl
  · exact hc.2.2.1 e he'

theorem ctxIdsBelow_setLoop {c : LCtx} {lbl n : Nat}
    (hc : ctxIdsBelow c n) (hlbl : lbl < n) :
    ctxIdsBelow { c with loop? := some lbl } n :=
  ⟨hc.1, hc.2.1, hc.2.2.1, fun _ h => by cases h; exact hlbl⟩

private theorem mem_of_lookup_eq_some {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {xs : List (α × β)} {k : α} {v : β}, xs.lookup k = some v → (k, v) ∈ xs
  | [], _, _, h => by cases h
  | (k', v') :: rest, k, v, h => by
    dsimp only [List.lookup] at h
    cases hk : (k == k') with
    | true =>
      simp only [hk, Option.some.injEq] at h
      have heq : k = k' := eq_of_beq hk
      subst heq; subst h
      exact List.mem_cons_self ..
    | false =>
      simp only [hk] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup_eq_some h)

theorem ctxIdsBelow_lookup_var {c : LCtx} {n x : Nat} {a : LArg} {ty : LcTy}
    (hc : ctxIdsBelow c n) (hlu : c.vars.lookup x = some (a, ty)) : argIdsBelow a n :=
  hc.2.1 (x, a, ty) (mem_of_lookup_eq_some hlu)

theorem ctxIdsBelow_lookup_jp {c : LCtx} {n j lbl : Nat} {ts : List LcTy}
    (hc : ctxIdsBelow c n) (hlu : c.jps.lookup j = some (lbl, ts)) : lbl < n :=
  hc.2.2.1 (j, lbl, ts) (mem_of_lookup_eq_some hlu)

theorem c0VEnv_get_set_self (ρ : Frontend.C0.VEnv) (id : Nat) (t : Ty) (v : Val t) :
    (ρ.set id t v).get id t = some v := by
  simp only [Frontend.C0.VEnv.get, Frontend.C0.VEnv.set, ↓reduceIte]
  exact castTy_self' t v

theorem c0VEnv_get_set_ne (ρ : Frontend.C0.VEnv) {id id' : Nat} (hne : id ≠ id')
    (t u : Ty) (v : Val t) :
    (ρ.set id' t v).get id u = ρ.get id u := by
  simp only [Frontend.C0.VEnv.get, Frontend.C0.VEnv.set, hne, ↓reduceIte]

theorem LArg.eval_vArg_set_self (ρ : Frontend.C0.VEnv) (v : Frontend.C0.LVar) (val : Val v.ty) :
    LArg.eval (ρ.set v.id v.ty val) v.ty (vArg v) = some val := by
  simp only [LArg.eval, vArg, ↓reduceIte]
  exact c0VEnv_get_set_self ρ v.id v.ty val

theorem LArg.eval_imm_self (ρ : Frontend.C0.VEnv) (t : Ty) (v : Val t) :
    LArg.eval ρ t (.imm t v) = some v := by
  simp only [LArg.eval, ↓reduceDIte]

theorem LArg.eval_set_of_ltBound {ρ : Frontend.C0.VEnv} {a : LArg} {n id : Nat}
    {t u : Ty} {v : Val t}
    (ha : argIdsBelow a n) (hle : n ≤ id) :
    LArg.eval (ρ.set id t v) u a = LArg.eval ρ u a := by
  cases a with
  | imm _ _ => rfl
  | var vid vt =>
    have hne : vid ≠ id := Nat.ne_of_lt (Nat.lt_of_lt_of_le ha hle)
    simp only [LArg.eval, c0VEnv_get_set_ne ρ hne]

theorem LArg.eval_bind_of_ltBound {ρ : Frontend.C0.VEnv} {a : LArg} {n : Nat} {u : Ty}
    (ha : argIdsBelow a n) :
    ∀ {bs : List Frontend.C0.LVar} {ts : List Ty} (xs : Tup Val ts),
      (∀ b ∈ bs, n ≤ b.id) → LArg.eval (ρ.bind bs ts xs) u a = LArg.eval ρ u a
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | b :: bs, t :: ts, (x, xs), hge => by
    dsimp only [Frontend.C0.VEnv.bind]
    rw [LArg.eval_bind_of_ltBound ha xs (fun b' hb' => hge b' (List.mem_cons_of_mem _ hb'))]
    exact LArg.eval_set_of_ltBound ha (hge b (List.mem_cons_self ..))

theorem evalArgs_set_of_ltBound {ρ : Frontend.C0.VEnv} {n id : Nat} {t : Ty} {v : Val t}
    (hle : n ≤ id) :
    ∀ {ts : List Ty} {as : List LArg},
      (∀ a ∈ as, argIdsBelow a n) → evalArgs (ρ.set id t v) ts as = evalArgs ρ ts as
  | [], [], _ => rfl
  | [], _ :: _, _ => rfl
  | _ :: _, [], _ => rfl
  | u :: ts, a :: as, has => by
    dsimp only [evalArgs]
    rw [LArg.eval_set_of_ltBound (has a (List.mem_cons_self ..)) hle,
      evalArgs_set_of_ltBound hle (fun a' ha' => has a' (List.mem_cons_of_mem _ ha'))]

theorem evalArgs_bind_of_ltBound {ρ : Frontend.C0.VEnv} {n : Nat} :
    ∀ {ts : List Ty} {as : List LArg} {bs : List Frontend.C0.LVar} {us : List Ty} (xs : Tup Val us),
      (∀ a ∈ as, argIdsBelow a n) → (∀ b ∈ bs, n ≤ b.id) →
      evalArgs (ρ.bind bs us xs) ts as = evalArgs ρ ts as
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, _, _, _, _, _ => rfl
  | _ :: _, [], _, _, _, _, _ => rfl
  | u :: ts, a :: as, bs, us, xs, has, hge => by
    dsimp only [evalArgs]
    rw [LArg.eval_bind_of_ltBound (has a (List.mem_cons_self ..)) xs hge,
      evalArgs_bind_of_ltBound xs (fun a' ha' => has a' (List.mem_cons_of_mem _ ha')) hge]

theorem JEnv.get_set_self (J : JEnv) (lid : Nat) (ts : List Ty) (k : Cont ts) :
    (J.set lid ts k).get lid ts = some k := by
  simp only [JEnv.get, JEnv.set, ↓reduceIte]
  exact castListTy_self' ts k

theorem JEnv.get_set_ne (J : JEnv) {lid lid' : Nat} (hne : lid ≠ lid')
    (ts us : List Ty) (k : Cont ts) :
    (J.set lid' ts k).get lid us = J.get lid us := by
  simp only [JEnv.get, JEnv.set, hne, ↓reduceIte]

theorem JEnv.get_set_of_lt (J : JEnv) {lid lid' n : Nat} (hlt : lid < n) (hle : n ≤ lid')
    (ts us : List Ty) (k : Cont ts) :
    (J.set lid' ts k).get lid us = J.get lid us :=
  JEnv.get_set_ne J (Nat.ne_of_lt (Nat.lt_of_lt_of_le hlt hle)) ts us k

/-! ### Exact Characterization of `fresh`, `freshVar`, and `ts.mapM freshVar` -/

theorem fresh_run (n : Nat) : fresh.run n = .ok (n, n + 1) :=
  rfl

theorem freshVar_run (t : Ty) (n : Nat) :
    (freshVar t).run n = .ok ({ id := n, name := "", ty := t }, n + 1) :=
  rfl

/-- Canonical list of fresh binders allocated by `ts.mapM freshVar` starting from counter `n`. -/
@[expose] def mkFreshVars : List Ty → Nat → List Frontend.C0.LVar
  | [], _ => []
  | t :: ts, n => { id := n, name := "", ty := t } :: mkFreshVars ts (n + 1)

theorem mapM_freshVar_run : ∀ (ts : List Ty) (n : Nat),
    (ts.mapM freshVar).run n = .ok (mkFreshVars ts n, n + ts.length)
  | [], n => by
    simp only [List.mapM_nil, Pure.pure, StateT.pure, Except.pure, StateT.run,
      mkFreshVars, List.length_nil, Nat.add_zero]
  | t :: ts, n => by
    have ih := mapM_freshVar_run ts (n + 1)
    simp only [StateT.run] at ih
    simp only [List.mapM_cons, mkFreshVars, List.length_cons, StateT.run, Bind.bind,
      StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure, freshVar, fresh,
      modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, ih]
    congr 2; omega

theorem mkFreshVars_map_ty : ∀ (ts : List Ty) (n : Nat),
    (mkFreshVars ts n).map (·.ty) = ts
  | [], _ => rfl
  | _ :: ts, n => by simp [mkFreshVars, mkFreshVars_map_ty ts (n + 1)]

theorem mkFreshVars_length (ts : List Ty) (n : Nat) :
    (mkFreshVars ts n).length = ts.length := by
  have := congrArg List.length (mkFreshVars_map_ty ts n)
  simpa using this

theorem mkFreshVars_id_bounds : ∀ (ts : List Ty) (n : Nat) (v : Frontend.C0.LVar),
    v ∈ mkFreshVars ts n → n ≤ v.id ∧ v.id < n + ts.length
  | [], _, _, h => by cases h
  | _ :: ts, n, v, h => by
    rcases List.mem_cons.mp h with rfl | h'
    · exact ⟨Nat.le_refl _, by simp⟩
    · obtain ⟨hge, hlt⟩ := mkFreshVars_id_bounds ts (n + 1) v h'
      exact ⟨by omega, by simp; omega⟩

theorem mkFreshVars_vArg_ltBound {ts : List Ty} {n : Nat} :
    ∀ a ∈ (mkFreshVars ts n).map vArg, argIdsBelow a (n + ts.length) := by
  intro a ha
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
  exact (mkFreshVars_id_bounds ts n v hv).2

theorem evalArgs_bind_mkFreshVars :
    ∀ (ts : List Ty) (n : Nat) (ρ : Frontend.C0.VEnv) (xs : Tup Val ts),
    evalArgs (ρ.bind (mkFreshVars ts n) ts xs) ts ((mkFreshVars ts n).map vArg) = some xs
  | [], _, _, () => rfl
  | t :: ts, n, ρ, (x, xs) => by
    simp only [mkFreshVars, List.map_cons, Frontend.C0.VEnv.bind, evalArgs]
    have hfirst :
        LArg.eval ((ρ.set n t x).bind (mkFreshVars ts (n + 1)) ts xs) t
          (vArg { id := n, name := "", ty := t }) = some x := by
      rw [LArg.eval_bind_of_ltBound (a := vArg { id := n, name := "", ty := t }) (n := n + 1)
        (Nat.lt_succ_self n) xs (fun b hb => (mkFreshVars_id_bounds ts (n + 1) b hb).1)]
      exact LArg.eval_vArg_set_self ρ { id := n, name := "", ty := t } x
    rw [hfirst, evalArgs_bind_mkFreshVars ts (n + 1) (ρ.set n t x) xs]

theorem LArg.eval_bind_mkFreshVars_lt {ts : List Ty} {n : Nat} {ρ : Frontend.C0.VEnv}
    {a : LArg} {u : Ty}
    (ha : argIdsBelow a n) (xs : Tup Val ts) :
    LArg.eval (ρ.bind (mkFreshVars ts n) ts xs) u a = LArg.eval ρ u a :=
  LArg.eval_bind_of_ltBound ha xs (fun b hb => (mkFreshVars_id_bounds ts n b hb).1)

/-! ## 3. Environment Join, Runtime Call Env, and `HCallEnvOk` -/

/-- Pointwise join (`Γ₁ ⊔ Γ₂`) of two `LeanQbe.T.Env`s. -/
@[expose] def envJoin (Γ₁ Γ₂ : Env) : Env :=
  fun f as bs xs m Q X => Γ₁ f as bs xs m Q X ∨ Γ₂ f as bs xs m Q X

/-- Signatures of `Lower.rtCalls` implemented inside `rtC0CoreMod` (all 35 non-float calls). -/
@[expose] def rtCoreCallSigs : List SigEntry :=
  rtCalls.filter fun s => rtCoreFnNames.contains s.1

/-- `rtC0CoreEnv` restricted to the runtime entry points in `rtCoreCallSigs`. -/
@[expose] def rtCoreCallEnv : Env :=
  fun f as bs xs m Q X => (f, as, bs) ∈ rtCoreCallSigs ∧ rtC0CoreEnv f as bs xs m Q X

/-- Env-parametric call-environment assumption for generic `H → T` simulation:
`Γ` supplies every module callee contract in `liftEnv m Δ` and every Phase-1 runtime entry point
in `rtCoreCallEnv`. Arbitrary `Γ` composes directly with both `linkRtC0Env` (acyclic `LinkedCert`)
and `BudgetEnv.sccStep` (`LinkedCertScc`). -/
@[expose] def HCallEnvOk (m : LcModule) (Δ : HEnv) (Γ : Env) : Prop :=
  Env.le (liftEnv m Δ) Γ ∧ Env.le rtCoreCallEnv Γ

/-- Return-typed monotonicity of a Tier-H function contract: `S` only invokes its normal
postcondition on words of type `retTy.toTTy` and is monotone in `(Q, X)`. -/
@[expose] def HSpec.RetTyped (retTy : LcTy) (S : HSpec) : Prop :=
  ∀ as σ (Q₁ Q₂ : HPost) (X₁ X₂ : HXPost),
    (∀ r σ', r.1 = retTy.toTTy → Q₁ r σ' → Q₂ r σ') →
    (∀ c σ', X₁ c σ' → X₂ c σ') →
    S as σ Q₁ X₁ → S as σ Q₂ X₂

/-- Every declaration contract in `Δ` for module `m` is return-typed at `d.retTy`. -/
@[expose] def HEnv.RetTyped (m : LcModule) (Δ : HEnv) : Prop :=
  ∀ d ∈ m.decls, (Δ d.name).RetTyped d.retTy

theorem HSpec.RetTyped.mono {retTy : LcTy} {S : HSpec} (h : S.RetTyped retTy) : S.Mono :=
  fun as σ Q₁ Q₂ X₁ X₂ hQ hX hs => h as σ Q₁ Q₂ X₁ X₂ (fun r σ' _ => hQ r σ') hX hs

theorem HSpec.RetTyped_bot (retTy : LcTy) : HSpec.RetTyped retTy (HEnv.bot "") :=
  fun _ _ _ _ _ _ _ _ h => False.elim h

theorem HEnv.RetTyped_bot (m : LcModule) : HEnv.RetTyped m HEnv.bot :=
  fun _ _ _ _ _ _ _ _ _ _ h => False.elim h

theorem rtCoreCallEnv_le_rtC0CoreEnv : Env.le rtCoreCallEnv rtC0CoreEnv :=
  fun _ _ _ _ _ _ _ h => h.2

theorem rtCoreCallSigs_mem_rtCalls {s : SigEntry} (h : s ∈ rtCoreCallSigs) : s ∈ rtCalls :=
  (List.mem_filter.mp h).1

theorem rtCoreCallSigs_mem_rtCoreFnNames {s : SigEntry} (h : s ∈ rtCoreCallSigs) :
    s.1 ∈ rtCoreFnNames :=
  List.contains_iff_mem.mp (List.mem_filter.mp h).2

theorem rtCoreCallEnv_le_linkRtC0Env (progEnv : Env) :
    Env.le rtCoreCallEnv (linkRtC0Env progEnv) := by
  intro f as bs xs m Q X h
  exact linkRtC0Env_of_rt (rtCoreCallSigs_mem_rtCoreFnNames h.1) h.2

theorem HCallEnvOk_mono {m : LcModule} {Δ : HEnv} {Γ₁ Γ₂ : Env}
    (h : HCallEnvOk m Δ Γ₁) (hle : Env.le Γ₁ Γ₂) : HCallEnvOk m Δ Γ₂ :=
  ⟨Env.le_trans h.1 hle, Env.le_trans h.2 hle⟩

theorem HCallEnvOk_env_mono {m : LcModule} {Δ₁ Δ₂ : HEnv} {Γ : Env}
    (hΔ : HEnv.le Δ₁ Δ₂) (h : HCallEnvOk m Δ₂ Γ) : HCallEnvOk m Δ₁ Γ :=
  ⟨Env.le_trans (liftEnv_mono m hΔ) h.1, h.2⟩

theorem HCallEnvOk_of_rtC0CoreEnv {m : LcModule} {Δ : HEnv} {Γ : Env}
    (hprog : Env.le (liftEnv m Δ) Γ) (hrt : Env.le rtC0CoreEnv Γ) :
    HCallEnvOk m Δ Γ :=
  ⟨hprog, Env.le_trans rtCoreCallEnv_le_rtC0CoreEnv hrt⟩

theorem HCallEnvOk_of_envJoin {m : LcModule} {Δ : HEnv} {Γ : Env}
    (h : Env.le (envJoin (liftEnv m Δ) rtC0CoreEnv) Γ) :
    HCallEnvOk m Δ Γ :=
  HCallEnvOk_of_rtC0CoreEnv
    (fun f as bs xs mem Q X hp => h f as bs xs mem Q X (Or.inl hp))
    (fun f as bs xs mem Q X hr => h f as bs xs mem Q X (Or.inr hr))

theorem HCallEnvOk_linkRtC0Env {m : LcModule} {Δ : HEnv}
    (hdisj : ∀ d ∈ m.decls, mangleLc d.name ∉ rtCoreFnNames) :
    HCallEnvOk m Δ (linkRtC0Env (liftEnv m Δ)) := by
  refine ⟨?_, rtCoreCallEnv_le_linkRtC0Env (liftEnv m Δ)⟩
  rintro sym as rs xs mem Q X ⟨d, hd, hsym, ha, hr, hspec⟩
  subst hsym
  exact (linkRtC0Env_prog (liftEnv m Δ) (hdisj d hd)).mpr ⟨d, hd, rfl, ha, hr, hspec⟩

theorem HCallEnvOk_bot {m : LcModule} {Γ : Env} (hrt : Env.le rtCoreCallEnv Γ) :
    HCallEnvOk m HEnv.bot Γ := by
  refine ⟨?_, hrt⟩
  rintro sym as rs xs mem Q X ⟨d, _, _, ha, hr, hspec⟩
  rcases hspec with ⟨_, _, _, _, _, hbot⟩
  exact False.elim hbot

theorem HCallEnvOk.rt {m : LcModule} {Δ : HEnv} {Γ : Env} (h : HCallEnvOk m Δ Γ)
    {f : Sym} {as bs : List Ty} (hsig : (f, as, bs) ∈ rtCoreCallSigs)
    {xs : Tup Val as} {mem : Mem 64} {Q : Post bs} {X : XPost}
    (hspec : rtC0CoreEnv f as bs xs mem Q X) :
    Γ f as bs xs mem Q X :=
  h.2 f as bs xs mem Q X ⟨hsig, hspec⟩

theorem HCallEnvOk.decl {m : LcModule} {Δ : HEnv} {Γ : Env} (h : HCallEnvOk m Δ Γ)
    {d : LcDecl} (hd : d ∈ m.decls)
    {xs : Tup Val (i64 :: (d.params.map (·.ty.toTTy)).take regArgs)}
    {mem : Mem 64} {Q : Post [d.retTy.toTTy]} {X : XPost}
    (hspec : liftDeclSpec (Δ d.name) d.params d.retTy xs mem Q X) :
    Γ (mangleLc d.name) (i64 :: (d.params.map (·.ty.toTTy)).take regArgs) [d.retTy.toTTy]
      xs mem Q X :=
  h.1 _ _ _ xs mem Q X (liftEnv_of_mem hd hspec)

/-! ## 4. Canonical `H ↔ LExpr` Simulation Invariant (`HSimInv`) -/

/-- Static lowering environment `env` matches module `m`'s declaration table. -/
@[expose] def LEnvOk (m : LcModule) (env : LEnv) : Prop :=
  ∀ f d, env.decls.lookup f = some d ↔ d ∈ m.decls ∧ d.name = f

/-- Local variable simulation relation: every Tier-H binding `x ↦ (ty, w)` has a matching
lowering binding `x ↦ (a, ty)` in `c.vars` whose `LExpr` value in `ρL` equals `w`. -/
@[expose] def VarRel (c : LCtx) (ρH : HValEnv) (ρL : Frontend.C0.VEnv) : Prop :=
  ∀ x ty w, ρH x = some (ty, w) →
    ∃ (a : LArg) (h : w.1 = ty.toTTy),
      c.vars.lookup x = some (a, ty) ∧
      LArg.eval ρL ty.toTTy a = some (h ▸ w.2)

/-- Normal return postcondition relation between Tier-H `QH` and `T` postcondition `QT`
(parameterized by runtime pointer `rt`, return type `retTy`, and separation frame `R`). -/
@[expose] def HPostRel (rt : BitVec 64) (retTy : LcTy) (R : Mem 64 → Prop)
    (QH : HPost) (QT : Post [retTy.toTTy]) : Prop :=
  ∀ r σ', QH r σ' → (h : r.1 = retTy.toTTy) →
    ∀ m', HInv rt σ' → (σ'.mem rt ⋆ R) m' → QT (h ▸ r.2, ()) m'

/-- Panic exit postcondition relation routing Tier-H `XH` to `XT "lcnf_panic" [i64, i64]`. -/
@[expose] def HXPostRel (rt : BitVec 64) (R : Mem 64 → Prop)
    (XH : HXPost) (XT : XPost) : Prop :=
  ∀ code σ', XH code σ' →
    ∀ m', (σ'.mem rt ⋆ R) m' → XT "lcnf_panic" [i64, i64] (rt, code, ()) m'

/-- Join-point simulation relation between `c.jps`, Tier-H `JH`, and `LExpr` label env `JL`. -/
@[expose] def JpRel (rt : BitVec 64) (R : Mem 64 → Prop)
    (c : LCtx) (JH : HJEnv) (JL : JEnv) : Prop :=
  ∀ j lbl ts, c.jps.lookup j = some (lbl, ts) →
    ∃ k : Cont (ts.map LcTy.toTTy),
      JL.get lbl (ts.map LcTy.toTTy) = some k ∧
      ∀ ws σ, JH j ws σ → HInv rt σ →
        ∀ (xs : Tup Val (ts.map LcTy.toTTy)), wordsOfTup xs = ws →
          ∀ m, (σ.mem rt ⋆ R) m → k xs m

/-- Self-tail loop-header simulation relation: when `c.loop? = some lbl`, calling `Δ c.fn` in
tail position (`let x := f ys; ret x`) discharges `.jump lbl` into `JL.get lbl`. -/
@[expose] def LoopRel (Δ : HEnv) (rt : BitVec 64) (R : Mem 64 → Prop)
    (c : LCtx) (QH : HPost) (XH : HXPost) (JL : JEnv) : Prop :=
  ∀ lbl, c.loop? = some lbl →
    ∃ k : Cont (c.params.map LcTy.toTTy),
      JL.get lbl (c.params.map LcTy.toTTy) = some k ∧
      ∀ ws σ (P : HPost) (E : HXPost),
        Δ c.fn ws σ P E → HInv rt σ →
        (∀ r σ', P r σ' → ∃ r', r.toWidth c.retTy.width = some r' ∧ QH r' σ') →
        (∀ code σ', E code σ' → XH code σ') →
        ∀ (xs : Tup Val (c.params.map LcTy.toTTy)), wordsOfTup xs = ws →
          ∀ m, (σ.mem rt ⋆ R) m → k xs m

/-- Packaged canonical `H ↔ LExpr` simulation invariant for `lowerCode` at fresh-counter `n`. -/
structure HSimInv (Δ : HEnv) (rt : BitVec 64) (R : Mem 64 → Prop)
    (c : LCtx) (n : Nat) (QH : HPost) (XH : HXPost)
    (QT : Post [c.retTy.toTTy]) (XT : XPost)
    (JH : HJEnv) (ρH : HValEnv) (ρL : Frontend.C0.VEnv) (JL : JEnv) : Prop where
  idsOk : ctxIdsBelow c n
  rtOk : LArg.eval ρL i64 c.rt = some rt
  varRel : VarRel c ρH ρL
  jpRel : JpRel rt R c JH JL
  loopRel : LoopRel Δ rt R c QH XH JL
  postRel : HPostRel rt c.retTy R QH QT
  xpostRel : HXPostRel rt R XH XT

/-! ### Invariant Preservation & Extraction Helpers -/

theorem VarRel.empty (c : LCtx) (ρL : Frontend.C0.VEnv) : VarRel c HValEnv.empty ρL :=
  fun _ _ _ h => by cases h

theorem VarRel.set_fresh {c : LCtx} {ρH : HValEnv} {ρL : Frontend.C0.VEnv}
    {n id : Nat} {t : Ty} {v : Val t}
    (hc : ctxIdsBelow c n) (hvr : VarRel c ρH ρL) (hle : n ≤ id) :
    VarRel c ρH (ρL.set id t v) := by
  intro x ty w hρ
  obtain ⟨a, hty, hlu, hev⟩ := hvr x ty w hρ
  refine ⟨a, hty, hlu, ?_⟩
  rw [LArg.eval_set_of_ltBound (ctxIdsBelow_lookup_var hc hlu) hle]
  exact hev

theorem VarRel.bind_fresh {c : LCtx} {ρH : HValEnv} {ρL : Frontend.C0.VEnv} {n : Nat}
    {bs : List Frontend.C0.LVar} {ts : List Ty} (xs : Tup Val ts)
    (hc : ctxIdsBelow c n) (hvr : VarRel c ρH ρL) (hge : ∀ b ∈ bs, n ≤ b.id) :
    VarRel c ρH (ρL.bind bs ts xs) := by
  intro x ty w hρ
  obtain ⟨a, hty, hlu, hev⟩ := hvr x ty w hρ
  refine ⟨a, hty, hlu, ?_⟩
  rw [LArg.eval_bind_of_ltBound (ctxIdsBelow_lookup_var hc hlu) xs hge]
  exact hev

theorem VarRel.bind_lcVar {c : LCtx} {ρH : HValEnv} {ρL : Frontend.C0.VEnv}
    {x : Nat} {a : LArg} {ty : LcTy} {w : Word}
    (hvr : VarRel c ρH ρL) (hw : w.1 = ty.toTTy)
    (hev : LArg.eval ρL ty.toTTy a = some (hw ▸ w.2)) :
    VarRel (c.bind x a ty) (ρH.set x ty w) ρL := by
  intro x' ty' w' hρ
  dsimp only [HValEnv.set] at hρ
  by_cases hx : x' = x
  · subst hx
    simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hρ
    rcases hρ with ⟨rfl, rfl⟩
    refine ⟨a, hw, ?_, hev⟩
    simp [LCtx.bind]
  · simp only [hx, ↓reduceIte] at hρ
    obtain ⟨a', hty', hlu', hev'⟩ := hvr x' ty' w' hρ
    refine ⟨a', hty', ?_, hev'⟩
    have hne : (x' == x) = false := beq_false_of_ne hx
    simp [LCtx.bind, List.lookup, hne, hlu']

theorem VarRel.bindAll {ps : List LcParam} {as : List LArg} {ws : List Word}
    {c : LCtx} {ρH : HValEnv} {ρL : Frontend.C0.VEnv}
    (hvr : VarRel c ρH ρL) (hlen : as.length = ps.length) (hpm : paramsMatch ps ws)
    (hev : ∀ (i : Nat) (hi : i < ps.length) (hia : i < as.length) (hiw : i < ws.length),
      ∃ h : (ws[i]'hiw).1 = (ps[i]'hi).ty.toTTy,
        LArg.eval ρL (ps[i]'hi).ty.toTTy (as[i]'hia) = some (h ▸ (ws[i]'hiw).2)) :
    VarRel (c.bindAll ps as) (ρH.bindAll ps ws) ρL := by
  induction ps generalizing as ws c ρH with
  | nil =>
    cases as with
    | nil => cases ws with
      | nil => simpa [LCtx.bindAll, HValEnv.bindAll] using hvr
      | cons _ _ => exact False.elim hpm
    | cons _ _ => simp at hlen
  | cons p ps ih =>
    cases as with
    | nil => simp at hlen
    | cons a as =>
      cases ws with
      | nil => exact False.elim hpm
      | cons w ws =>
        simp only [LCtx.bindAll, List.zip_cons_cons, List.foldl_cons, HValEnv.bindAll]
        obtain ⟨hw, hev0⟩ := hev 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
        refine ih (hvr.bind_lcVar hw hev0) (Nat.succ.inj hlen) hpm.2 ?_
        intro i hi hia hiw
        exact hev (i + 1) (Nat.succ_lt_succ hi) (Nat.succ_lt_succ hia) (Nat.succ_lt_succ hiw)

private theorem eval_cast_ty {ρ : Frontend.C0.VEnv} {t u : Ty} (h : t = u) {a : LArg} {v : Val t}
    (he : LArg.eval ρ t a = some v) : LArg.eval ρ u a = some (h ▸ v) := by
  cases h; exact he

private theorem eqRec_trans_val {t u v : Ty} (h1 : t = u) (h2 : u = v) (x : Val t) :
    h2 ▸ (h1 ▸ x) = (h1.trans h2) ▸ x := by
  cases h1; cases h2; rfl

private theorem eqRec_symm_val {t u : Ty} (h : t = u) (x : Val t) :
    h.symm ▸ (h ▸ x) = x := by
  cases h; rfl

theorem VarRel.evalArgAt {c : LCtx} {ρH : HValEnv} {ρL : Frontend.C0.VEnv}
    (hvr : VarRel c ρH ρL) {a : LcArg} {t : LcTy} {w : Word}
    (heval : ρH.evalArgAt a t = some w) :
    ∃ (la : LArg) (h : w.1 = t.toTTy),
      (∀ n, (argAt c a t).run n = .ok (la, n)) ∧
      LArg.eval ρL t.toTTy la = some (h ▸ w.2) := by
  cases a with
  | erased =>
    dsimp only [HValEnv.evalArgAt] at heval
    cases heval
    refine ⟨imm t.width (if t.isScalar then 0 else 1), rfl, fun _ => rfl, ?_⟩
    exact LArg.eval_imm_self ρL t.toTTy _
  | var x =>
    dsimp only [HValEnv.evalArgAt] at heval
    cases hρ : ρH x with
    | none => simp [hρ] at heval
    | some p =>
      rcases p with ⟨ty, w0⟩
      simp only [hρ] at heval
      by_cases hty : w0.1 = t.toTTy
      · simp only [hty, ↓reduceIte, Option.some.injEq] at heval
        subst heval
        obtain ⟨la, hw, hlu, hev⟩ := hvr x ty w0 hρ
        have hteq : ty.toTTy = t.toTTy := hw.symm.trans hty
        have hweq : ty.width = t.width := Ty.bits.inj hteq
        refine ⟨la, hty, fun n => ?_, ?_⟩
        · simp [argAt, LCtx.var, hlu, hweq, Bind.bind, StateT.bind, Except.bind,
            Pure.pure, StateT.pure, Except.pure, StateT.run]
        · have hev' := eval_cast_ty hteq hev
          rw [eqRec_trans_val] at hev'
          exact hev'
      · simp [hty] at heval

theorem VarRel.evalArgOwn {c : LCtx} {ρH : HValEnv} {ρL : Frontend.C0.VEnv}
    (hvr : VarRel c ρH ρL) {a : LcArg} {w : Word}
    (heval : ρH.evalArgOwn a = some w) :
    ∃ la : LArg,
      (∀ n, (argOwn c a).run n = .ok (la, n)) ∧
      LArg.eval ρL w.1 la = some w.2 := by
  cases a with
  | erased =>
    dsimp only [HValEnv.evalArgOwn] at heval
    cases heval
    exact ⟨imm64 1, fun _ => rfl, LArg.eval_imm_self ρL i64 1#64⟩
  | var x =>
    dsimp only [HValEnv.evalArgOwn] at heval
    cases hρ : ρH x with
    | none => simp [hρ] at heval
    | some p =>
      rcases p with ⟨ty, w0⟩
      simp only [hρ, Option.map_some, Option.some.injEq] at heval
      subst heval
      obtain ⟨la, hw, hlu, hev⟩ := hvr x ty w0 hρ
      refine ⟨la, fun n => ?_, ?_⟩
      · simp [argOwn, LCtx.var, hlu, Bind.bind, StateT.bind, Except.bind,
          Pure.pure, StateT.pure, Except.pure, StateT.run]
      · rcases w0 with ⟨wt, wv⟩
        dsimp only at hw hev ⊢
        subst hw
        exact hev

theorem VarRel.evalArgAt_of_evalArgOwn {c : LCtx} {ρH : HValEnv} {ρL : Frontend.C0.VEnv}
    (hvr : VarRel c ρH ρL) {a : LcArg} {t : LcTy} {w : Word}
    (heval : ρH.evalArgOwn a = some w) (ht : a = .erased → !t.isScalar)
    (hw : w.1 = t.toTTy) :
    ∃ la : LArg,
      (∀ n, (argAt c a t).run n = .ok (la, n)) ∧
      LArg.eval ρL t.toTTy la = some (hw ▸ w.2) := by
  cases a with
  | erased =>
    dsimp only [HValEnv.evalArgOwn] at heval
    cases heval
    have hns : t.isScalar = false := by simpa using ht rfl
    refine ⟨imm t.width (if t.isScalar then 0 else 1), fun _ => rfl, ?_⟩
    cases t <;> first
      | exact absurd hns (by decide)
      | exact LArg.eval_imm_self ρL i64 1#64
  | var x =>
    dsimp only [HValEnv.evalArgOwn] at heval
    cases hρ : ρH x with
    | none => simp [hρ] at heval
    | some p =>
      rcases p with ⟨ty, w0⟩
      simp only [hρ, Option.map_some, Option.some.injEq] at heval
      subst heval
      have hat : ρH.evalArgAt (.var x) t = some w0 := by
        simp [HValEnv.evalArgAt, hρ, hw]
      obtain ⟨la, _, hrun, hev⟩ := hvr.evalArgAt hat
      exact ⟨la, hrun, hev⟩

theorem VarRel.getBV64? {c : LCtx} {ρH : HValEnv} {ρL : Frontend.C0.VEnv}
    (hvr : VarRel c ρH ρL) {x : Nat} {v : BitVec 64}
    (h : ρH.getBV64? x = some v) :
    ∃ (la : LArg) (ty : LcTy),
      c.vars.lookup x = some (la, ty) ∧ ty.width = 64 ∧ LArg.eval ρL i64 la = some v := by
  dsimp only [HValEnv.getBV64?, HValEnv.evalArgOwn] at h
  cases hρ : ρH x with
  | none => simp [hρ] at h
  | some p =>
    rcases p with ⟨ty, w⟩
    simp only [hρ, Option.map_some, Option.bind_some] at h
    unfold Word.toBV64? at h
    split at h
    · cases h
      obtain ⟨la, hty, hlu, hev⟩ := hvr x ty ⟨i64, v⟩ hρ
      have hweq : ty.width = 64 := (Ty.bits.inj hty).symm
      have hev' := eval_cast_ty hty.symm hev
      rw [eqRec_symm_val] at hev'
      exact ⟨la, ty, hlu, hweq, hev'⟩
    · cases h

theorem VarRel.getTypedBV64? {c : LCtx} {ρH : HValEnv} {ρL : Frontend.C0.VEnv}
    (hvr : VarRel c ρH ρL) {x : Nat} {ty : LcTy} {v : BitVec 64}
    (h : ρH.getTypedBV64? x = some (ty, v)) :
    ∃ la : LArg,
      c.vars.lookup x = some (la, ty) ∧ ty.width = 64 ∧ LArg.eval ρL i64 la = some v := by
  dsimp only [HValEnv.getTypedBV64?] at h
  cases hρ : ρH x with
  | none => simp [hρ] at h
  | some p =>
    rcases p with ⟨ty', w⟩
    simp only [hρ] at h
    cases hbv : w.toBV64? with
    | none => simp [hbv] at h
    | some v' =>
      simp only [hbv, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨h1, h2⟩
      subst h1; subst h2
      have hget : ρH.getBV64? x = some v' := by
        simp [HValEnv.getBV64?, HValEnv.evalArgOwn, hρ, hbv]
      obtain ⟨la, _, hlu, hw, hev⟩ := hvr.getBV64? hget
      obtain ⟨la', _, hlu', _⟩ := hvr x ty' w hρ
      rw [hlu'] at hlu
      cases hlu
      exact ⟨la, hlu', hw, hev⟩

theorem JpRel.empty (rt : BitVec 64) (R : Mem 64 → Prop) (c : LCtx) (hc : c.jps = [])
    (JH : HJEnv) (JL : JEnv) : JpRel rt R c JH JL := by
  intro j lbl ts hlu
  simp [hc] at hlu

theorem JpRel.set_fresh {rt : BitVec 64} {R : Mem 64 → Prop} {c : LCtx} {JH : HJEnv} {JL : JEnv}
    {n lid : Nat} {ts : List Ty} {k : Cont ts}
    (hc : ctxIdsBelow c n) (hjp : JpRel rt R c JH JL) (hle : n ≤ lid) :
    JpRel rt R c JH (JL.set lid ts k) := by
  intro j lbl jts hlu
  obtain ⟨kj, hget, hcont⟩ := hjp j lbl jts hlu
  refine ⟨kj, ?_, hcont⟩
  rw [JEnv.get_set_of_lt JL (ctxIdsBelow_lookup_jp hc hlu) hle]
  exact hget

theorem JpRel.bind_var {rt : BitVec 64} {R : Mem 64 → Prop} {c : LCtx} {JH : HJEnv} {JL : JEnv}
    {x : Nat} {a : LArg} {ty : LcTy} (hjp : JpRel rt R c JH JL) :
    JpRel rt R (c.bind x a ty) JH JL :=
  hjp

theorem JpRel.push_jp {rt : BitVec 64} {R : Mem 64 → Prop} {c : LCtx} {JH : HJEnv} {JL : JEnv}
    {n j lbl : Nat} {ps : List LcParam} {k : Cont ((ps.map (·.ty)).map LcTy.toTTy)}
    (hc : ctxIdsBelow c n) (hjp : JpRel rt R c JH JL) (hle : n ≤ lbl) :
    let Jj : List Word → HState → Prop := fun ws σ =>
      HInv rt σ → ∀ (xs : Tup Val ((ps.map (·.ty)).map LcTy.toTTy)), wordsOfTup xs = ws →
        ∀ m, (σ.mem rt ⋆ R) m → k xs m
    JpRel rt R { c with jps := (j, lbl, ps.map (·.ty)) :: c.jps }
      (JH.set j Jj) (JL.set lbl ((ps.map (·.ty)).map LcTy.toTTy) k) := by
  intro Jj j' lbl' ts' hlu
  dsimp only [List.lookup] at hlu
  cases hj : (j' == j) with
  | true =>
    simp only [hj, Option.some.injEq, Prod.mk.injEq] at hlu
    have heq : j' = j := eq_of_beq hj
    subst heq
    rcases hlu with ⟨rfl, rfl⟩
    refine ⟨k, JEnv.get_set_self JL lbl _ k, ?_⟩
    intro ws σ hJ hinv xs hws m hm
    dsimp only [HJEnv.set] at hJ
    simp only [↓reduceIte] at hJ
    exact hJ hinv xs hws m hm
  | false =>
    simp only [hj] at hlu
    have hne : j' ≠ j := by intro he; subst he; simp at hj
    obtain ⟨k', hget, hcont⟩ := hjp j' lbl' ts' hlu
    refine ⟨k', ?_, ?_⟩
    · rw [JEnv.get_set_of_lt JL (ctxIdsBelow_lookup_jp hc hlu) hle]
      exact hget
    · intro ws σ hJ hinv xs hws m hm
      dsimp only [HJEnv.set] at hJ
      simp only [hne, ↓reduceIte] at hJ
      exact hcont ws σ hJ hinv xs hws m hm

theorem LoopRel.none (Δ : HEnv) (rt : BitVec 64) (R : Mem 64 → Prop) (c : LCtx)
    (hc : c.loop? = none) (QH : HPost) (XH : HXPost) (JL : JEnv) :
    LoopRel Δ rt R c QH XH JL := by
  intro lbl h; rw [hc] at h; cases h

theorem LoopRel.set_fresh {Δ : HEnv} {rt : BitVec 64} {R : Mem 64 → Prop} {c : LCtx}
    {QH : HPost} {XH : HXPost} {JL : JEnv} {n lid : Nat} {ts : List Ty} {k : Cont ts}
    (hc : ctxIdsBelow c n) (hl : LoopRel Δ rt R c QH XH JL) (hle : n ≤ lid) :
    LoopRel Δ rt R c QH XH (JL.set lid ts k) := by
  intro lbl hlbl
  obtain ⟨kl, hget, hcont⟩ := hl lbl hlbl
  refine ⟨kl, ?_, hcont⟩
  rw [JEnv.get_set_of_lt JL (hc.2.2.2 lbl hlbl) hle]
  exact hget

theorem LoopRel.bind_var {Δ : HEnv} {rt : BitVec 64} {R : Mem 64 → Prop} {c : LCtx}
    {QH : HPost} {XH : HXPost} {JL : JEnv} {x : Nat} {a : LArg} {ty : LcTy}
    (hl : LoopRel Δ rt R c QH XH JL) :
    LoopRel Δ rt R (c.bind x a ty) QH XH JL :=
  hl

theorem LoopRel.push_jp {Δ : HEnv} {rt : BitVec 64} {R : Mem 64 → Prop} {c : LCtx}
    {QH : HPost} {XH : HXPost} {JL : JEnv} {n j lid : Nat} {jts : List LcTy}
    {ts : List Ty} {k : Cont ts}
    (hc : ctxIdsBelow c n) (hl : LoopRel Δ rt R c QH XH JL) (hle : n ≤ lid) :
    LoopRel Δ rt R { c with jps := (j, lid, jts) :: c.jps } QH XH (JL.set lid ts k) :=
  fun lbl hlbl => hl.set_fresh hc hle lbl hlbl

theorem HSimInv.mono_n {Δ : HEnv} {rt : BitVec 64} {R : Mem 64 → Prop} {c : LCtx}
    {n m : Nat} {QH : HPost} {XH : HXPost} {QT : Post [c.retTy.toTTy]} {XT : XPost}
    {JH : HJEnv} {ρH : HValEnv} {ρL : Frontend.C0.VEnv} {JL : JEnv}
    (hle : n ≤ m) (h : HSimInv Δ rt R c n QH XH QT XT JH ρH ρL JL) :
    HSimInv Δ rt R c m QH XH QT XT JH ρH ρL JL :=
  { h with idsOk := ctxIdsBelow_mono hle h.idsOk }

theorem HSimInv.set_fresh_var {Δ : HEnv} {rt : BitVec 64} {R : Mem 64 → Prop} {c : LCtx}
    {n m id : Nat} {t : Ty} {v : Val t} {QH : HPost} {XH : HXPost}
    {QT : Post [c.retTy.toTTy]} {XT : XPost}
    {JH : HJEnv} {ρH : HValEnv} {ρL : Frontend.C0.VEnv} {JL : JEnv}
    (h : HSimInv Δ rt R c n QH XH QT XT JH ρH ρL JL) (hid : n ≤ id) (hm : n ≤ m) :
    HSimInv Δ rt R c m QH XH QT XT JH ρH (ρL.set id t v) JL :=
  { idsOk := ctxIdsBelow_mono hm h.idsOk
    rtOk := by rw [LArg.eval_set_of_ltBound h.idsOk.1 hid]; exact h.rtOk
    varRel := h.varRel.set_fresh h.idsOk hid
    jpRel := h.jpRel
    loopRel := h.loopRel
    postRel := h.postRel
    xpostRel := h.xpostRel }

theorem HSimInv.bind_fresh_vars {Δ : HEnv} {rt : BitVec 64} {R : Mem 64 → Prop} {c : LCtx}
    {n m : Nat} {bs : List Frontend.C0.LVar} {ts : List Ty} (xs : Tup Val ts)
    {QH : HPost} {XH : HXPost} {QT : Post [c.retTy.toTTy]} {XT : XPost}
    {JH : HJEnv} {ρH : HValEnv} {ρL : Frontend.C0.VEnv} {JL : JEnv}
    (h : HSimInv Δ rt R c n QH XH QT XT JH ρH ρL JL)
    (hge : ∀ b ∈ bs, n ≤ b.id) (hm : n ≤ m) :
    HSimInv Δ rt R c m QH XH QT XT JH ρH (ρL.bind bs ts xs) JL :=
  { idsOk := ctxIdsBelow_mono hm h.idsOk
    rtOk := by rw [LArg.eval_bind_of_ltBound h.idsOk.1 xs hge]; exact h.rtOk
    varRel := h.varRel.bind_fresh xs h.idsOk hge
    jpRel := h.jpRel
    loopRel := h.loopRel
    postRel := h.postRel
    xpostRel := h.xpostRel }

theorem HSimInv.set_fresh_lbl {Δ : HEnv} {rt : BitVec 64} {R : Mem 64 → Prop} {c : LCtx}
    {n m lid : Nat} {ts : List Ty} {k : Cont ts} {QH : HPost} {XH : HXPost}
    {QT : Post [c.retTy.toTTy]} {XT : XPost}
    {JH : HJEnv} {ρH : HValEnv} {ρL : Frontend.C0.VEnv} {JL : JEnv}
    (h : HSimInv Δ rt R c n QH XH QT XT JH ρH ρL JL) (hlid : n ≤ lid) (hm : n ≤ m) :
    HSimInv Δ rt R c m QH XH QT XT JH ρH ρL (JL.set lid ts k) :=
  { idsOk := ctxIdsBelow_mono hm h.idsOk
    rtOk := h.rtOk
    varRel := h.varRel
    jpRel := h.jpRel.set_fresh h.idsOk hlid
    loopRel := h.loopRel.set_fresh h.idsOk hlid
    postRel := h.postRel
    xpostRel := h.xpostRel }

theorem HSimInv.bind_lcVar {Δ : HEnv} {rt : BitVec 64} {R : Mem 64 → Prop} {c : LCtx}
    {n x : Nat} {a : LArg} {ty : LcTy} {w : Word}
    {QH : HPost} {XH : HXPost} {QT : Post [c.retTy.toTTy]} {XT : XPost}
    {JH : HJEnv} {ρH : HValEnv} {ρL : Frontend.C0.VEnv} {JL : JEnv}
    (h : HSimInv Δ rt R c n QH XH QT XT JH ρH ρL JL)
    (ha : argIdsBelow a n) (hw : w.1 = ty.toTTy)
    (hev : LArg.eval ρL ty.toTTy a = some (hw ▸ w.2)) :
    HSimInv Δ rt R (c.bind x a ty) n QH XH QT XT JH (ρH.set x ty w) ρL JL :=
  { idsOk := ctxIdsBelow_bind h.idsOk ha
    rtOk := h.rtOk
    varRel := h.varRel.bind_lcVar hw hev
    jpRel := h.jpRel.bind_var
    loopRel := h.loopRel.bind_var
    postRel := h.postRel
    xpostRel := h.xpostRel }

end LeanQbe.T.LeanLCNF.Sem
