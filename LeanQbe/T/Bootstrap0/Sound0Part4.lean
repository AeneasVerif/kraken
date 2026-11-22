module

public import LeanQbe.T.Bootstrap0.Sound0Part3

/-!
# Bootstrap Stage B (`Sound0Part4`): Guards, Bounds, Worklist Decomposition, & `PrePass0`

Establishes structural and pass-level invariants for `LeanQbe.T.Bootstrap0.Compiler0` without
modifying `Compiler0.lean` (Option a), adding:
* **Bug C guard (`TFlat0.noGroupAfterJnz`)**: checks DFS worklist order matching `regaWorkLoop0`
  so no `.group` executes after any `.jnz` has incremented `ctrl.nextLbl` without growing
  `ctrl.lblSlots`.
* **AST bounds (`TFlatFn0.boundsFitU32`)** and full guard bundle (`TFlatFn0.okGuardsFull`,
  `TFlatModule0.okGuardsFull`).
* **Worklist decomposition (`preRunAux0` / `regaRunAux0`)**: exact fuel-independence, append
  splitting, `revDirs` prepend decomposition, and `patchEpilogues0` equations.
* **`PrePass0` invariants & exact spine accounting (`preNoteNode0_spec`, `preRunAux0_inv`,
  `compileFnPre0_inv`)**: exact `uses`/`escaped`/`defScope` accounting and `UInt32` safety bounds.
  Lockstep `Rega0` and label uniqueness continue in `Sound0Part5`
  (x64-only `Compiler0` verification targeting `LeanQbe.T.Amd64.ScalarTarg` via `Sound0Part1`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Bootstrap0

open LeanQbe.T
open LeanQbe.T.Amd64

/-! ## 1. Bug C Guard (`noGroupAfterJnz`), AST Bounds, & `okGuardsFull` -/

theorem nodeCount0_pos (n : TFlat0) : 0 < nodeCount0 n := by
  cases n <;> dsimp only [nodeCount0] <;> omega

/-- Total AST node count over a worklist of `TFlat0` nodes. -/
@[expose] def workNodeCount0 : List TFlat0 → Nat
  | [] => 0
  | n :: rest => nodeCount0 n + workNodeCount0 rest

theorem workNodeCount0_append (xs ys : List TFlat0) :
    workNodeCount0 (xs ++ ys) = workNodeCount0 xs + workNodeCount0 ys := by
  induction xs with
  | nil => dsimp only [List.nil_append, workNodeCount0]; omega
  | cons x xs ih => dsimp only [List.cons_append, workNodeCount0]; rw [ih]; omega

theorem workNodeCount0_map_snd (bs : List (List Ty0 × TFlat0)) :
    workNodeCount0 (bs.map Prod.snd) = blocksNodeCount0 bs := by
  induction bs with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨_, b⟩
    rw [List.map_cons]
    dsimp only [workNodeCount0, blocksNodeCount0]
    rw [ih]

/-- Nat-fueled structural version of `jnzGroupSafeWork0` (avoids WF `.eq_def` bloat). -/
@[expose] def jnzGroupSafeWorkNat0 (seenJnz : Bool) : Nat → List TFlat0 → Bool
  | _, [] => true
  | 0, _ :: _ => false
  | m + 1, .let1 _ _ k :: rest | m + 1, .let2Umulw64 _ _ k :: rest
  | m + 1, .load _ _ k :: rest | m + 1, .store _ _ _ k :: rest
  | m + 1, .call _ _ _ _ k :: rest =>
    jnzGroupSafeWorkNat0 seenJnz m (k :: rest)
  | m + 1, .jnz _ t e :: rest =>
    jnzGroupSafeWorkNat0 true m (e :: t :: rest)
  | m + 1, .group bodies k :: rest =>
    !seenJnz && jnzGroupSafeWorkNat0 seenJnz m (k :: (bodies.map Prod.snd ++ rest))
  | m + 1, .tailCall _ _ _ :: rest | m + 1, .jump _ _ :: rest | m + 1, .ret _ :: rest
  | m + 1, .exit _ _ _ :: rest | m + 1, .hlt :: rest =>
    jnzGroupSafeWorkNat0 seenJnz m rest

/-- Worklist-DFS checker tracking whether any `.jnz` precedes `.group` (Bug C guard). -/
@[expose] def jnzGroupSafeWork0 (seenJnz : Bool) (work : List TFlat0) : Bool :=
  jnzGroupSafeWorkNat0 seenJnz (workNodeCount0 work) work

theorem jnzGroupSafeWorkNat0_fuel_indep :
    ∀ (m₁ m₂ : Nat) (seenJnz : Bool) (work : List TFlat0),
      workNodeCount0 work ≤ m₁ → workNodeCount0 work ≤ m₂ →
      jnzGroupSafeWorkNat0 seenJnz m₁ work = jnzGroupSafeWorkNat0 seenJnz m₂ work
  | 0, 0, _, [], _, _ | 0, _ + 1, _, [], _, _ | _ + 1, 0, _, [], _, _
  | _ + 1, _ + 1, _, [], _, _ => rfl
  | m₁ + 1, m₂ + 1, seenJnz, nd :: rest, h1, h2 => by
    cases nd with
    | let1 _ _ k | let2Umulw64 _ _ k | load _ _ k | store _ _ _ k | call _ _ _ _ k =>
      dsimp only [workNodeCount0, nodeCount0] at h1 h2
      dsimp only [jnzGroupSafeWorkNat0]
      exact jnzGroupSafeWorkNat0_fuel_indep m₁ m₂ seenJnz (k :: rest)
        (by dsimp only [workNodeCount0]; omega) (by dsimp only [workNodeCount0]; omega)
    | jnz _ t e =>
      dsimp only [workNodeCount0, nodeCount0] at h1 h2
      dsimp only [jnzGroupSafeWorkNat0]
      exact jnzGroupSafeWorkNat0_fuel_indep m₁ m₂ true (e :: t :: rest)
        (by dsimp only [workNodeCount0]; omega) (by dsimp only [workNodeCount0]; omega)
    | group bodies k =>
      dsimp only [workNodeCount0, nodeCount0] at h1 h2
      dsimp only [jnzGroupSafeWorkNat0]
      have hc : workNodeCount0 (k :: (bodies.map Prod.snd ++ rest)) ≤ m₁ ∧
          workNodeCount0 (k :: (bodies.map Prod.snd ++ rest)) ≤ m₂ := by
        dsimp only [workNodeCount0]
        rw [workNodeCount0_append, workNodeCount0_map_snd]
        omega
      rw [jnzGroupSafeWorkNat0_fuel_indep m₁ m₂ seenJnz _ hc.1 hc.2]
    | tailCall _ _ _ | jump _ _ | ret _ | exit _ _ _ | hlt =>
      dsimp only [workNodeCount0, nodeCount0] at h1 h2
      dsimp only [jnzGroupSafeWorkNat0]
      exact jnzGroupSafeWorkNat0_fuel_indep m₁ m₂ seenJnz rest (by omega) (by omega)
  | 0, _, _, nd :: _, h1, _ => by
    dsimp only [workNodeCount0] at h1; have := nodeCount0_pos nd; omega
  | _ + 1, 0, _, nd :: _, _, h2 => by
    dsimp only [workNodeCount0] at h2; have := nodeCount0_pos nd; omega

/-- True iff no `.group` is processed after any `.jnz` in `Compiler0` worklist DFS order. -/
@[expose] def TFlat0.noGroupAfterJnz (n : TFlat0) : Bool :=
  jnzGroupSafeWork0 false [n]

mutual
/-- Total variable binders introduced inside a `TFlat0` AST. -/
@[expose] def binderCount0 : TFlat0 → Nat
  | .let1 _ _ k => 1 + binderCount0 k
  | .let2Umulw64 _ _ k => 2 + binderCount0 k
  | .load _ _ k => 1 + binderCount0 k
  | .store _ _ _ k => binderCount0 k
  | .call _ _ bs _ k => bs.length + binderCount0 k
  | .jnz _ t e => binderCount0 t + binderCount0 e
  | .group bodies k => blocksBinderCount0 bodies + binderCount0 k
  | _ => 0

/-- Total variable binders across a list of `.group` blocks. -/
@[expose] def blocksBinderCount0 : List (List Ty0 × TFlat0) → Nat
  | [] => 0
  | (pts, b) :: rest => pts.length + binderCount0 b + blocksBinderCount0 rest
end

mutual
/-- Maximum argument list length at any `.jump` inside `n`. -/
@[expose] def maxJumpArity0 : TFlat0 → Nat
  | .let1 _ _ k | .let2Umulw64 _ _ k | .load _ _ k | .store _ _ _ k | .call _ _ _ _ k =>
    maxJumpArity0 k
  | .jnz _ t e => max (maxJumpArity0 t) (maxJumpArity0 e)
  | .jump _ args => args.length
  | .group bodies k => max (blocksMaxJumpArity0 bodies) (maxJumpArity0 k)
  | _ => 0

/-- Maximum `.jump` argument list length across `.group` blocks. -/
@[expose] def blocksMaxJumpArity0 : List (List Ty0 × TFlat0) → Nat
  | [] => 0
  | (_, b) :: rest => max (maxJumpArity0 b) (blocksMaxJumpArity0 rest)
end

mutual
/-- Total AST operand occurrences inside a `TFlat0` AST. -/
@[expose] def argCount0 : TFlat0 → Nat
  | .let1 _ args k => args.length + argCount0 k
  | .let2Umulw64 _ _ k => 2 + argCount0 k
  | .load _ _ k => 1 + argCount0 k
  | .store _ _ _ k => 2 + argCount0 k
  | .call _ _ _ args k => args.length + argCount0 k
  | .tailCall _ _ args => args.length
  | .jump _ args => args.length
  | .ret vs => vs.length
  | .exit _ _ args => args.length
  | .jnz _ t e => 1 + argCount0 t + argCount0 e
  | .group bodies k => blocksArgCount0 bodies + argCount0 k
  | .hlt => 0

/-- Total AST operand occurrences across `.group` blocks. -/
@[expose] def blocksArgCount0 : List (List Ty0 × TFlat0) → Nat
  | [] => 0
  | (_, b) :: rest => argCount0 b + blocksArgCount0 rest
end

/-- Total binder count across a `TFlat0` worklist. -/
@[expose] def workBinderCount0 : List TFlat0 → Nat
  | [] => 0
  | n :: rest => binderCount0 n + workBinderCount0 rest

/-- Maximum `.jump` arity across a `TFlat0` worklist. -/
@[expose] def workMaxJumpArity0 : List TFlat0 → Nat
  | [] => 0
  | n :: rest => max (maxJumpArity0 n) (workMaxJumpArity0 rest)

/-- Total operand occurrence count across a `TFlat0` worklist. -/
@[expose] def workArgCount0 : List TFlat0 → Nat
  | [] => 0
  | n :: rest => argCount0 n + workArgCount0 rest

theorem workBinderCount0_append (xs ys : List TFlat0) :
    workBinderCount0 (xs ++ ys) = workBinderCount0 xs + workBinderCount0 ys := by
  induction xs with
  | nil => dsimp only [List.nil_append, workBinderCount0]; omega
  | cons x xs ih => dsimp only [List.cons_append, workBinderCount0]; rw [ih]; omega

theorem workBinderCount0_map_snd (bs : List (List Ty0 × TFlat0)) :
    workBinderCount0 (bs.map Prod.snd) ≤ blocksBinderCount0 bs := by
  induction bs with
  | nil => rw [List.map_nil]; dsimp only [workBinderCount0, blocksBinderCount0]; omega
  | cons p rest ih =>
    rcases p with ⟨pts, b⟩
    rw [List.map_cons]
    dsimp only [workBinderCount0, blocksBinderCount0]
    omega

theorem workMaxJumpArity0_append (xs ys : List TFlat0) :
    workMaxJumpArity0 (xs ++ ys) = max (workMaxJumpArity0 xs) (workMaxJumpArity0 ys) := by
  induction xs with
  | nil => dsimp only [List.nil_append, workMaxJumpArity0]; simp only [Nat.zero_max]
  | cons x xs ih =>
    dsimp only [List.cons_append, workMaxJumpArity0]
    rw [ih, Nat.max_assoc]

theorem workMaxJumpArity0_map_snd (bs : List (List Ty0 × TFlat0)) :
    workMaxJumpArity0 (bs.map Prod.snd) = blocksMaxJumpArity0 bs := by
  induction bs with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨_, b⟩
    rw [List.map_cons]
    dsimp only [workMaxJumpArity0, blocksMaxJumpArity0]
    rw [ih]

theorem workArgCount0_append (xs ys : List TFlat0) :
    workArgCount0 (xs ++ ys) = workArgCount0 xs + workArgCount0 ys := by
  induction xs with
  | nil => dsimp only [List.nil_append, workArgCount0]; omega
  | cons x xs ih => dsimp only [List.cons_append, workArgCount0]; rw [ih]; omega

theorem workArgCount0_map_snd (bs : List (List Ty0 × TFlat0)) :
    workArgCount0 (bs.map Prod.snd) = blocksArgCount0 bs := by
  induction bs with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨_, b⟩
    rw [List.map_cons]
    dsimp only [workArgCount0, blocksArgCount0]
    rw [ih]

/-- Decidable `UInt32` overflow-safety bounds for variables, slots, scopes, labels, and uses. -/
@[expose] def TFlatFn0.boundsFitU32 (fn : TFlatFn0) : Bool :=
  decide (fn.as.length + binderCount0 fn.body + maxJumpArity0 fn.body + 1 < 2 ^ 31) &&
  decide (nodeCount0 fn.body < 2 ^ 30) &&
  decide (argCount0 fn.body < 2 ^ 31)

/-- Full decidable precondition bundle on one `TFlatFn0` (Bugs A/B/C + `UInt32` bounds). -/
@[expose] def TFlatFn0.okGuardsFull (fn : TFlatFn0) : Bool :=
  fn.okGuards && fn.body.noGroupAfterJnz && fn.sigLensFitU32 && fn.boundsFitU32

/-- Full decidable precondition bundle on a `TFlatModule0`. -/
@[expose] def TFlatModule0.okGuardsFull (mod : TFlatModule0) : Bool :=
  decide (mod.fns.length < 2 ^ 32) &&
  mod.fns.all TFlatFn0.okGuardsFull &&
  mod.externs.all (fun ex => listLenFitsU32 ex.as && listLenFitsU32 ex.rs)

theorem TFlatFn0.okGuardsFull_okGuards {fn : TFlatFn0} (h : fn.okGuardsFull = true) :
    fn.okGuards = true := by
  simp only [TFlatFn0.okGuardsFull, Bool.and_eq_true] at h; exact h.1.1.1

theorem TFlatFn0.okGuardsFull_singleBlock {fn : TFlatFn0} (h : fn.okGuardsFull = true) :
    fn.body.singleBlockGroups = true := by
  have hg := fn.okGuardsFull_okGuards h
  simp only [TFlatFn0.okGuards, Bool.and_eq_true] at hg; exact hg.1

theorem TFlatFn0.okGuardsFull_noNegBool {fn : TFlatFn0} (h : fn.okGuardsFull = true) :
    fn.body.noNegBool = true := by
  have hg := fn.okGuardsFull_okGuards h
  simp only [TFlatFn0.okGuards, Bool.and_eq_true] at hg; exact hg.2

theorem TFlatFn0.okGuardsFull_noGroupAfterJnz {fn : TFlatFn0} (h : fn.okGuardsFull = true) :
    fn.body.noGroupAfterJnz = true := by
  simp only [TFlatFn0.okGuardsFull, Bool.and_eq_true] at h; exact h.1.1.2

theorem TFlatFn0.okGuardsFull_sigLensFitU32 {fn : TFlatFn0} (h : fn.okGuardsFull = true) :
    fn.sigLensFitU32 = true := by
  simp only [TFlatFn0.okGuardsFull, Bool.and_eq_true] at h; exact h.1.2

theorem TFlatFn0.okGuardsFull_boundsFitU32 {fn : TFlatFn0} (h : fn.okGuardsFull = true) :
    fn.boundsFitU32 = true := by
  simp only [TFlatFn0.okGuardsFull, Bool.and_eq_true] at h; exact h.2

theorem TFlatModule0.okGuardsFull_sigLensFitU32 {mod : TFlatModule0}
    (h : mod.okGuardsFull = true) : mod.sigLensFitU32 = true := by
  simp only [TFlatModule0.okGuardsFull, TFlatModule0.sigLensFitU32, Bool.and_eq_true,
    List.all_eq_true] at h ⊢
  exact ⟨fun fn hf => TFlatFn0.okGuardsFull_sigLensFitU32 (h.1.2 fn hf), h.2⟩

theorem TFlatModule0.okGuardsFull_fns_length {mod : TFlatModule0}
    (h : mod.okGuardsFull = true) : mod.fns.length < 2 ^ 32 := by
  simp only [TFlatModule0.okGuardsFull, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

private theorem u32_ext_toNat {a b : UInt32} (h : a.toNat = b.toNat) : a = b :=
  UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)

private theorem u32_toNat_ofNat (n : Nat) : (UInt32.ofNat n).toNat = n % 2 ^ 32 := by
  rw [← UInt32.toNat_toBitVec]
  exact BitVec.toNat_ofNat n 32

private theorem u32_sub1_toNat {x : UInt32} (hx : 0 < x.toNat) :
    (x - 1).toNat = x.toNat - 1 := by
  refine UInt32.toNat_sub_of_le x 1 ?_
  exact UInt32.le_iff_toNat_le.mpr (by rw [UInt32.toNat_one]; exact hx)

private theorem u32_add1_toNat {x : UInt32} (hx : x.toNat + 1 < 2 ^ 32) :
    (x + 1).toNat = x.toNat + 1 := by
  rw [UInt32.toNat_add, UInt32.toNat_one, Nat.mod_eq_of_lt hx]

private theorem u32_add_assoc (a b c : UInt32) : (a + b) + c = a + (b + c) := by
  apply u32_ext_toNat
  rw [UInt32.toNat_add, UInt32.toNat_add, UInt32.toNat_add, UInt32.toNat_add,
    Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]

private theorem u32_add_zero (a : UInt32) : a + UInt32.ofNat 0 = a := by
  apply u32_ext_toNat
  rw [UInt32.toNat_add, u32_toNat_ofNat]
  simp [Nat.mod_eq_of_lt (UInt32.toNat_lt a)]

private theorem u32_succ_add_ofNat (nxt : UInt32) (k : Nat) :
    (nxt + 1) + UInt32.ofNat k = nxt + UInt32.ofNat (k + 1) := by
  apply u32_ext_toNat
  rw [UInt32.toNat_add, UInt32.toNat_add, UInt32.toNat_add, UInt32.toNat_one,
    u32_toNat_ofNat, u32_toNat_ofNat, Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc,
    Nat.add_comm 1 k, Nat.add_mod_mod]

private theorem u32_eq_add_of_toNat {a b : UInt32} {m : Nat} (h : b.toNat = a.toNat + m)
    (hlt : a.toNat + m < 2 ^ 32) : b = a + UInt32.ofNat m := by
  apply u32_ext_toNat
  rw [h, UInt32.toNat_add, u32_toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hlt), Nat.mod_eq_of_lt hlt]

theorem argLenU0_eq_of_lt {xs : List Arg0} (hlt : xs.length < 2 ^ 32) :
    (argLenU0 xs 0).toNat = xs.length := by
  have aux : ∀ (ys : List Arg0) (acc : UInt32),
      (argLenU0 ys acc).toNat = (acc.toNat + ys.length) % 2 ^ 32 := by
    intro ys
    induction ys with
    | nil =>
      intro acc
      dsimp only [argLenU0, List.length_nil]
      rw [Nat.add_zero, Nat.mod_eq_of_lt (UInt32.toNat_lt acc)]
    | cons _ rest ih =>
      intro acc; dsimp only [argLenU0, List.length_cons]
      rw [ih, UInt32.toNat_add, UInt32.toNat_one]; simp [Nat.add_assoc, Nat.add_comm 1]
  rw [aux xs 0, UInt32.toNat_zero, Nat.zero_add, Nat.mod_eq_of_lt hlt]

theorem listGetU32_eq_listGetD : ∀ (xs : List UInt32) (i : UInt32),
    listGetU32 xs i = xs.getD i.toNat 0
  | [], _ => rfl
  | x :: rest, i => by
    dsimp only [listGetU32]
    by_cases hi : i = 0
    · subst hi; simp [List.getD]
    · have hnz : i.toNat ≠ 0 := fun hz => hi (by
        calc i = UInt32.ofNat i.toNat := UInt32.ofNat_toNat.symm
          _ = UInt32.ofNat 0 := by rw [hz]
          _ = 0 := rfl)
      have hpos : 0 < i.toNat := Nat.pos_of_ne_zero hnz
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hnz
      simp only [hi, ↓reduceIte, hm, List.getD_cons_succ]
      rw [listGetU32_eq_listGetD rest (i - 1), u32_sub1_toNat hpos, hm, Nat.succ_sub_one]

private theorem u32_ofNat_succ_add (x : UInt32) (k : Nat) :
    UInt32.ofNat ((x + 1).toNat + k) = UInt32.ofNat (x.toNat + (k + 1)) := by
  apply u32_ext_toNat
  rw [u32_toNat_ofNat, u32_toNat_ofNat, UInt32.toNat_add, UInt32.toNat_one,
    Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc, Nat.add_comm 1 k]

/-! ## 2. Worklist Splitting & Directive Prepend Decomposition -/

/-- Nat-fueled structural version of `preRunAux0` (avoids WF `.eq_def` bloat). -/
@[expose] def preRunAuxNat0 : Nat → UInt32 → PreSt0 → List PreItem0 → UInt32 × PreSt0
  | 0, nextSc, st, _ => (nextSc, st)
  | _, nextSc, st, [] => (nextSc, st)
  | m + 1, nextSc, st, cur :: rest =>
    let st1 := preNoteNode0 cur.scope cur.venv cur.node st
    let out := preStepPush0 cur st1 nextSc rest
    preRunAuxNat0 m out.nextScope out.st out.work

/-- Auxiliary `PrePass0` worklist runner also returning final `nextScope`. -/
@[expose] def preRunAux0 (fuel nextSc : UInt32) (st : PreSt0)
    (work : List PreItem0) : UInt32 × PreSt0 :=
  preRunAuxNat0 fuel.toNat nextSc st work

/-- Nat-fueled structural version of `regaRunAux0` (avoids WF `.eq_def` bloat). -/
@[expose] def regaRunAuxNat0 : Nat → Array Nat → RegaSt0 → CtrlSt0 → List RegaTask0 →
    RegaSt0 × CtrlSt0
  | 0, _, st, ctrl, _ => (st, ctrl)
  | _, _, st, ctrl, [] => (st, ctrl)
  | m + 1, esc, st, ctrl, cur :: rest =>
    let st0 := regaPrependLbl0 cur st ctrl
    let ls := regaStep0 esc cur st0 ctrl rest
    regaRunAuxNat0 m esc ls.st ls.ctrl ls.work

/-- Auxiliary `Rega0` worklist runner also returning final `CtrlSt0`. -/
@[expose] def regaRunAux0 (fuel : UInt32) (esc : Array Nat) (st : RegaSt0) (ctrl : CtrlSt0)
    (work : List RegaTask0) : RegaSt0 × CtrlSt0 :=
  regaRunAuxNat0 fuel.toNat esc st ctrl work

theorem preRunAux0_zero (nextSc : UInt32) (st : PreSt0) (work : List PreItem0) :
    preRunAux0 0 nextSc st work = (nextSc, st) := rfl

theorem regaRunAux0_zero (esc : Array Nat) (st : RegaSt0) (ctrl : CtrlSt0)
    (work : List RegaTask0) :
    regaRunAux0 0 esc st ctrl work = (st, ctrl) := rfl

theorem preRunAux0_nil (fuel nextSc : UInt32) (st : PreSt0) :
    preRunAux0 fuel nextSc st [] = (nextSc, st) := by
  dsimp only [preRunAux0]; cases fuel.toNat <;> rfl

theorem regaRunAux0_nil (fuel : UInt32) (esc : Array Nat) (st : RegaSt0) (ctrl : CtrlSt0) :
    regaRunAux0 fuel esc st ctrl [] = (st, ctrl) := by
  dsimp only [regaRunAux0]; cases fuel.toNat <;> rfl

theorem preRunAux0_succ {fuel : UInt32} (hf : fuel ≠ 0) (nextSc : UInt32) (st : PreSt0)
    (cur : PreItem0) (rest : List PreItem0) :
    preRunAux0 fuel nextSc st (cur :: rest) =
      preRunAux0 (fuel - 1)
        (preStepPush0 cur (preNoteNode0 cur.scope cur.venv cur.node st) nextSc rest).nextScope
        (preStepPush0 cur (preNoteNode0 cur.scope cur.venv cur.node st) nextSc rest).st
        (preStepPush0 cur (preNoteNode0 cur.scope cur.venv cur.node st) nextSc rest).work := by
  have hpos : 0 < fuel.toNat := by
    rcases Nat.eq_zero_or_pos fuel.toNat with hz | hp
    · exact absurd (u32_ext_toNat hz) hf
    · exact hp
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  have hsub : (fuel - 1).toNat = m := by rw [u32_sub1_toNat hpos, hm]; omega
  dsimp only [preRunAux0]; rw [hm, hsub]; rfl

theorem regaRunAux0_succ {fuel : UInt32} (hf : fuel ≠ 0) (esc : Array Nat) (st : RegaSt0)
    (ctrl : CtrlSt0) (cur : RegaTask0) (rest : List RegaTask0) :
    regaRunAux0 fuel esc st ctrl (cur :: rest) =
      regaRunAux0 (fuel - 1) esc
        (regaStep0 esc cur (regaPrependLbl0 cur st ctrl) ctrl rest).st
        (regaStep0 esc cur (regaPrependLbl0 cur st ctrl) ctrl rest).ctrl
        (regaStep0 esc cur (regaPrependLbl0 cur st ctrl) ctrl rest).work := by
  have hpos : 0 < fuel.toNat := by
    rcases Nat.eq_zero_or_pos fuel.toNat with hz | hp
    · exact absurd (u32_ext_toNat hz) hf
    · exact hp
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  have hsub : (fuel - 1).toNat = m := by rw [u32_sub1_toNat hpos, hm]; omega
  dsimp only [regaRunAux0]; rw [hm, hsub]; rfl

theorem preRunAux0_snd_eq_preWorkLoop0 (fuel nextSc : UInt32) (st : PreSt0)
    (work : List PreItem0) :
    (preRunAux0 fuel nextSc st work).2 = preWorkLoop0 fuel nextSc st work := by
  suffices h : ∀ (m : Nat) (fuel nextSc : UInt32) (st : PreSt0) (work : List PreItem0),
      fuel.toNat = m → (preRunAux0 fuel nextSc st work).2 = preWorkLoop0 fuel nextSc st work from
    h fuel.toNat fuel nextSc st work rfl
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro fuel nextSc st work hfuel
    rw [preWorkLoop0.eq_def]
    split
    · subst_vars; rfl
    · rename_i hne
      cases work with
      | nil => rw [preRunAux0_nil]
      | cons cur rest =>
        rw [preRunAux0_succ hne]
        dsimp only
        have hlt : (fuel - 1).toNat < m := hfuel ▸ u32Sub1Lt0 fuel hne
        exact ih (fuel - 1).toNat hlt (fuel - 1) _ _ _ rfl

theorem regaRunAux0_fst_eq_regaWorkLoop0 (fuel : UInt32) (esc : Array Nat) (st : RegaSt0)
    (ctrl : CtrlSt0) (work : List RegaTask0) :
    (regaRunAux0 fuel esc st ctrl work).1 = regaWorkLoop0 fuel esc st ctrl work := by
  suffices h : ∀ (m : Nat) (fuel : UInt32) (st : RegaSt0) (ctrl : CtrlSt0)
      (work : List RegaTask0),
      fuel.toNat = m → (regaRunAux0 fuel esc st ctrl work).1 = regaWorkLoop0 fuel esc st ctrl work
    from h fuel.toNat fuel st ctrl work rfl
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro fuel st ctrl work hfuel
    rw [regaWorkLoop0.eq_def]
    split
    · subst_vars; rfl
    · rename_i hne
      cases work with
      | nil => rw [regaRunAux0_nil]
      | cons cur rest =>
        rw [regaRunAux0_succ hne]
        dsimp only
        have hlt : (fuel - 1).toNat < m := hfuel ▸ u32Sub1Lt0 fuel hne
        exact ih (fuel - 1).toNat hlt (fuel - 1) _ _ _ rfl

theorem preWorkNodeCount0_children (cur : PreItem0) (st1 : PreSt0) (nextSc : UInt32)
    (rest : List PreItem0) :
    let out := preStepPush0 cur st1 nextSc rest
    workNodeCount0 (out.work.map PreItem0.node) + 1 =
      workNodeCount0 ((cur :: rest).map PreItem0.node) := by
  have hgrp_cnt : ∀ bs venv (st : PreSt0) (s : UInt32) (w : List PreItem0),
      workNodeCount0 ((prePushGroup0 bs venv (PreOut0.mk st s w)).work.map PreItem0.node) =
        blocksNodeCount0 bs + workNodeCount0 (w.map PreItem0.node) := by
    intro bs
    induction bs with
    | nil =>
      intro _ _ _ _
      dsimp only [prePushGroup0, blocksNodeCount0]
      exact (Nat.zero_add _).symm
    | cons p bs ih =>
      intro venv st s w
      rcases p with ⟨pts, b⟩
      dsimp only [prePushGroup0, prePushOne0]
      rw [ih, List.map_cons]
      dsimp only [workNodeCount0, blocksNodeCount0]
      omega
  have henq_cnt : ∀ (staged w : List PreItem0),
      workNodeCount0 ((preEnqueueGroup0 staged w).map PreItem0.node) =
        workNodeCount0 (staged.map PreItem0.node) + workNodeCount0 (w.map PreItem0.node) := by
    intro staged
    induction staged with
    | nil =>
      intro w
      rw [List.map_nil]
      dsimp only [preEnqueueGroup0, workNodeCount0]
      exact (Nat.zero_add _).symm
    | cons item restS ih =>
      intro w
      dsimp only [preEnqueueGroup0]
      rw [ih, List.map_cons, List.map_cons]
      dsimp only [workNodeCount0]
      omega
  rcases cur with ⟨nd, venv, scope⟩
  dsimp only [preStepPush0]
  cases nd with
  | tailCall _ _ _ | jump _ _ | ret _ | exit _ _ _ | hlt =>
    dsimp only [isTerm0]
    simp only [↓reduceIte]
    rw [List.map_cons]
    dsimp only [workNodeCount0, nodeCount0]; omega
  | jnz _ t e =>
    dsimp only [isTerm0]
    simp only [Bool.false_eq_true, ↓reduceIte]
    dsimp only [preStepJnz0]
    rw [List.map_cons, List.map_cons, List.map_cons]
    dsimp only [workNodeCount0, nodeCount0]; omega
  | group bodies k =>
    dsimp only [isTerm0]
    simp only [Bool.false_eq_true, ↓reduceIte]
    dsimp only [preStepGroup0]
    rw [List.map_cons, List.map_cons]
    dsimp only [workNodeCount0, nodeCount0]
    rw [henq_cnt, hgrp_cnt, List.map_nil]
    dsimp only [workNodeCount0]
    omega
  | let1 _ _ k | let2Umulw64 _ _ k | load _ _ k | store _ _ _ k | call _ _ _ _ k =>
    dsimp only [isTerm0]
    simp only [Bool.false_eq_true, ↓reduceIte]
    dsimp only [preStepLin0, preLinFinish0, linK0]
    rw [List.map_cons, List.map_cons]
    dsimp only [workNodeCount0, nodeCount0]
    omega

private theorem preStepPush0_append (cur : PreItem0) (st1 : PreSt0) (nextSc : UInt32)
    (w₁ w₂ : List PreItem0) :
    preStepPush0 cur st1 nextSc (w₁ ++ w₂) =
      let out := preStepPush0 cur st1 nextSc w₁
      PreOut0.mk out.st out.nextScope (out.work ++ w₂) := by
  have henq : ∀ (staged w₁ w₂ : List PreItem0),
      preEnqueueGroup0 staged (w₁ ++ w₂) = preEnqueueGroup0 staged w₁ ++ w₂ := by
    intro staged
    induction staged with
    | nil => intro _ _; rfl
    | cons item restS ih =>
      intro w₁ w₂
      dsimp only [preEnqueueGroup0]
      rw [← List.cons_append]
      exact ih (item :: w₁) w₂
  dsimp only [preStepPush0]
  cases cur.node with
  | tailCall _ _ _ | jump _ _ | ret _ | exit _ _ _ | hlt =>
    dsimp only [isTerm0]; simp only [↓reduceIte]
  | jnz _ t e =>
    dsimp only [isTerm0]
    simp only [Bool.false_eq_true, ↓reduceIte]
    dsimp only [preStepJnz0]; rfl
  | group bodies k =>
    dsimp only [isTerm0]
    simp only [Bool.false_eq_true, ↓reduceIte]
    dsimp only [preStepGroup0]
    rw [henq]
    rfl
  | let1 _ _ k | let2Umulw64 _ _ k | load _ _ k | store _ _ _ k | call _ _ _ _ k =>
    dsimp only [isTerm0]
    simp only [Bool.false_eq_true, ↓reduceIte]
    dsimp only [preStepLin0, preLinFinish0]; rfl

theorem preRunAux0_split_and_fuel :
    ∀ (N : Nat) (fuel fuel₁ nextSc : UInt32) (st : PreSt0) (w₁ w₂ : List PreItem0),
      workNodeCount0 (w₁.map PreItem0.node) = N →
      N ≤ fuel.toNat → N ≤ fuel₁.toNat →
      preRunAux0 fuel nextSc st (w₁ ++ w₂) =
        let r1 := preRunAux0 fuel₁ nextSc st w₁
        preRunAux0 (UInt32.ofNat (fuel.toNat - N)) r1.1 r1.2 w₂ := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro fuel fuel₁ nextSc st w₁ w₂ hN hle hle₁
    cases w₁ with
    | nil =>
      subst hN
      rw [List.map_nil]
      dsimp only [workNodeCount0]
      rw [Nat.sub_zero, List.nil_append, preRunAux0_nil, UInt32.ofNat_toNat]
    | cons cur rest =>
      have hpos_N : 0 < N := by
        rw [← hN, List.map_cons]; dsimp only [workNodeCount0]
        have := nodeCount0_pos cur.node; omega
      have hf_ne : fuel ≠ 0 := fun hz => by
        have := congrArg UInt32.toNat hz; simp only [UInt32.toNat_zero] at this; omega
      have hf₁_ne : fuel₁ ≠ 0 := fun hz => by
        have := congrArg UInt32.toNat hz; simp only [UInt32.toNat_zero] at this; omega
      have hsub : (fuel - 1).toNat = fuel.toNat - 1 := u32_sub1_toNat (by omega)
      have hsub₁ : (fuel₁ - 1).toNat = fuel₁.toNat - 1 := u32_sub1_toNat (by omega)
      let st1 := preNoteNode0 cur.scope cur.venv cur.node st
      let out := preStepPush0 cur st1 nextSc rest
      have hcnt : workNodeCount0 (out.work.map PreItem0.node) + 1 = N := by
        rw [← hN]
        simpa only [out, List.map_cons] using preWorkNodeCount0_children cur st1 nextSc rest
      have hlt : workNodeCount0 (out.work.map PreItem0.node) < N := by omega
      have h_ih := ih (workNodeCount0 (out.work.map PreItem0.node)) hlt (fuel - 1) (fuel₁ - 1)
        out.nextScope out.st out.work w₂ rfl (by omega) (by omega)
      have h1 : preRunAux0 fuel nextSc st ((cur :: rest) ++ w₂) =
          preRunAux0 (fuel - 1) out.nextScope out.st (out.work ++ w₂) := by
        rw [List.cons_append, preRunAux0_succ hf_ne, preStepPush0_append cur st1 nextSc rest w₂]
      have h2 : preRunAux0 fuel₁ nextSc st (cur :: rest) =
          preRunAux0 (fuel₁ - 1) out.nextScope out.st out.work :=
        preRunAux0_succ hf₁_ne nextSc st cur rest
      rw [h1, h_ih, ← h2]
      congr 1
      have hmeq : (fuel - 1).toNat - workNodeCount0 (out.work.map PreItem0.node) =
          fuel.toNat - N := by omega
      rw [hmeq]

theorem preRunAux0_fuel_indep {f₁ f₂ nextSc : UInt32} {st : PreSt0} {w : List PreItem0}
    (hf₁ : workNodeCount0 (w.map PreItem0.node) ≤ f₁.toNat)
    (hf₂ : workNodeCount0 (w.map PreItem0.node) ≤ f₂.toNat) :
    preRunAux0 f₁ nextSc st w = preRunAux0 f₂ nextSc st w := by
  have h1 := preRunAux0_split_and_fuel (workNodeCount0 (w.map PreItem0.node)) f₁ f₂ nextSc st w []
    rfl hf₁ hf₂
  rw [List.append_nil] at h1
  rw [h1, preRunAux0_nil]

private theorem regaEnqueueGroup0_append (metas : List GroupMeta0) (lenv' free : List UInt32)
    (nxt : UInt32) (w₁ w₂ : List RegaTask0) :
    regaEnqueueGroup0 metas lenv' free nxt (w₁ ++ w₂) =
      regaEnqueueGroup0 metas lenv' free nxt w₁ ++ w₂ := by
  induction metas generalizing w₁ with
  | nil => rfl
  | cons gm rest ih =>
    dsimp only [regaEnqueueGroup0]
    have h := ih (RegaTask0.mk gm.lbl gm.body gm.venv lenv' free nxt :: w₁)
    simpa only [List.cons_append] using h

private theorem regaStep0_append (esc : Array Nat) (cur : RegaTask0) (st0 : RegaSt0)
    (ctrl : CtrlSt0) (w₁ w₂ : List RegaTask0) :
    regaStep0 esc cur st0 ctrl (w₁ ++ w₂) =
      let ls := regaStep0 esc cur st0 ctrl w₁
      LoopStep0.mk ls.st ls.ctrl (ls.work ++ w₂) := by
  rcases cur with ⟨lbl, nd, venv, lenv, free, nextSlot⟩
  dsimp only [regaStep0]
  cases nd with
  | jnz c t e => rfl
  | group bodies k =>
    dsimp only [stepGroupFinish0, groupEnqCont0]
    rw [regaEnqueueGroup0_append]
    rfl
  | let1 _ _ _ | let2Umulw64 _ _ _ | load _ _ _ | store _ _ _ _ | call _ _ _ _ _ => rfl
  | tailCall _ _ _ | jump _ _ | ret _ | exit _ _ _ | hlt =>
    simp [regaStepCtrl0]

theorem regaWorkNodeCount0_children (esc : Array Nat) (cur : RegaTask0) (st0 : RegaSt0)
    (ctrl : CtrlSt0) (rest : List RegaTask0) :
    let ls := regaStep0 esc cur st0 ctrl rest
    workNodeCount0 (ls.work.map RegaTask0.node) + 1 =
      workNodeCount0 ((cur :: rest).map RegaTask0.node) := by
  have hprep : ∀ bodies venv gp,
      workNodeCount0 ((regaPrepGroup0 bodies venv gp).metas.map GroupMeta0.body) =
        blocksNodeCount0 bodies + workNodeCount0 (gp.metas.map GroupMeta0.body) := by
    intro bodies
    induction bodies with
    | nil =>
      intro _ _; dsimp only [regaPrepGroup0, blocksNodeCount0]; exact (Nat.zero_add _).symm
    | cons p restB ih =>
      intro venv gp; rcases p with ⟨pts, b⟩
      dsimp only [regaPrepGroup0, prepOneBlock0, prepFinishBlock0]
      rw [ih, List.map_cons]
      dsimp only [workNodeCount0, blocksNodeCount0]; omega
  have heq : ∀ metas lenv' free nxt w,
      workNodeCount0 ((regaEnqueueGroup0 metas lenv' free nxt w).map RegaTask0.node) =
        workNodeCount0 (metas.map GroupMeta0.body) + workNodeCount0 (w.map RegaTask0.node) := by
    intro metas
    induction metas with
    | nil =>
      intro _ _ _ _
      rw [List.map_nil]
      dsimp only [regaEnqueueGroup0, workNodeCount0]
      exact (Nat.zero_add _).symm
    | cons gm restM ih =>
      intro lenv' free nxt w
      dsimp only [regaEnqueueGroup0]
      rw [ih, List.map_cons, List.map_cons]
      dsimp only [workNodeCount0]; omega
  rcases cur with ⟨lbl, nd, venv, lenv, free, nextSlot⟩
  dsimp only [regaStep0]
  cases nd with
  | jnz c t e =>
    dsimp only [stepJnzPush0]
    rw [List.map_cons, List.map_cons, List.map_cons]
    dsimp only [workNodeCount0, nodeCount0]; omega
  | group bodies k =>
    dsimp only [stepGroupFinish0, groupEnqCont0, stepGroupPrep0]
    rw [List.map_cons, List.map_cons]
    dsimp only [workNodeCount0, nodeCount0]
    rw [heq, hprep, List.map_nil]
    dsimp only [workNodeCount0, Nat.add_zero]
    omega
  | let1 _ _ k | let2Umulw64 _ _ k | load _ _ k | store _ _ _ k | call _ _ _ _ k =>
    dsimp only [stepLinear0, stepLinBindPush0, linBindPush0, linK0]
    rw [List.map_cons, List.map_cons]
    dsimp only [workNodeCount0, nodeCount0]; omega
  | tailCall _ _ _ | jump _ _ | ret _ | exit _ _ _ | hlt =>
    dsimp only [regaStepCtrl0]
    rw [List.map_cons]
    dsimp only [workNodeCount0, nodeCount0]; omega

theorem regaRunAux0_split_and_fuel :
    ∀ (N : Nat) (fuel fuel₁ : UInt32) (esc : Array Nat) (st : RegaSt0) (ctrl : CtrlSt0)
      (w₁ w₂ : List RegaTask0),
      workNodeCount0 (w₁.map RegaTask0.node) = N →
      N ≤ fuel.toNat → N ≤ fuel₁.toNat →
      regaRunAux0 fuel esc st ctrl (w₁ ++ w₂) =
        let r1 := regaRunAux0 fuel₁ esc st ctrl w₁
        regaRunAux0 (UInt32.ofNat (fuel.toNat - N)) esc r1.1 r1.2 w₂ := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro fuel fuel₁ esc st ctrl w₁ w₂ hN hle hle₁
    cases w₁ with
    | nil =>
      subst hN
      rw [List.map_nil]
      dsimp only [workNodeCount0]
      rw [Nat.sub_zero, List.nil_append, regaRunAux0_nil, UInt32.ofNat_toNat]
    | cons cur rest =>
      have hpos_N : 0 < N := by
        rw [← hN, List.map_cons]; dsimp only [workNodeCount0]
        have := nodeCount0_pos cur.node; omega
      have hf_ne : fuel ≠ 0 := fun hz => by
        have := congrArg UInt32.toNat hz; simp only [UInt32.toNat_zero] at this; omega
      have hf₁_ne : fuel₁ ≠ 0 := fun hz => by
        have := congrArg UInt32.toNat hz; simp only [UInt32.toNat_zero] at this; omega
      have hsub : (fuel - 1).toNat = fuel.toNat - 1 := u32_sub1_toNat (by omega)
      have hsub₁ : (fuel₁ - 1).toNat = fuel₁.toNat - 1 := u32_sub1_toNat (by omega)
      let st0 := regaPrependLbl0 cur st ctrl
      let ls := regaStep0 esc cur st0 ctrl rest
      have hcnt : workNodeCount0 (ls.work.map RegaTask0.node) + 1 = N := by
        rw [← hN]
        simpa only [ls, List.map_cons] using regaWorkNodeCount0_children esc cur st0 ctrl rest
      have hlt : workNodeCount0 (ls.work.map RegaTask0.node) < N := by omega
      have h_ih := ih (workNodeCount0 (ls.work.map RegaTask0.node)) hlt (fuel - 1) (fuel₁ - 1)
        esc ls.st ls.ctrl ls.work w₂ rfl (by omega) (by omega)
      have h1 : regaRunAux0 fuel esc st ctrl ((cur :: rest) ++ w₂) =
          regaRunAux0 (fuel - 1) esc ls.st ls.ctrl (ls.work ++ w₂) := by
        rw [List.cons_append, regaRunAux0_succ hf_ne, regaStep0_append esc cur st0 ctrl rest w₂]
      have h2 : regaRunAux0 fuel₁ esc st ctrl (cur :: rest) =
          regaRunAux0 (fuel₁ - 1) esc ls.st ls.ctrl ls.work :=
        regaRunAux0_succ hf₁_ne esc st ctrl cur rest
      rw [h1, h_ih, ← h2]
      congr 1
      have hmeq : (fuel - 1).toNat - workNodeCount0 (ls.work.map RegaTask0.node) =
          fuel.toNat - N := by omega
      rw [hmeq]

theorem regaRunAux0_fuel_indep {f₁ f₂ : UInt32} {esc : Array Nat} {st : RegaSt0} {ctrl : CtrlSt0}
    {w : List RegaTask0}
    (hf₁ : workNodeCount0 (w.map RegaTask0.node) ≤ f₁.toNat)
    (hf₂ : workNodeCount0 (w.map RegaTask0.node) ≤ f₂.toNat) :
    regaRunAux0 f₁ esc st ctrl w = regaRunAux0 f₂ esc st ctrl w := by
  have h1 := regaRunAux0_split_and_fuel (workNodeCount0 (w.map RegaTask0.node)) f₁ f₂ esc st ctrl
    w [] rfl hf₁ hf₂
  rw [List.append_nil] at h1
  rw [h1, regaRunAux0_nil]

theorem bindOneSlot0_revDirs (esc : Array Nat) (reg : Reg64) (st : RegaSt0)
    (free : List UInt32) (nxt : UInt32) :
    let bo := bindOneSlot0 esc reg st free nxt
    bo.st = { (bindOneSlot0 esc reg { st with revDirs := [] } free nxt).st with
      revDirs := (bindOneSlot0 esc reg { st with revDirs := [] } free nxt).st.revDirs ++
        st.revDirs } ∧
    ListNoSpZero0 (bindOneSlot0 esc reg { st with revDirs := [] } free nxt).st.revDirs ∧
    bo.free = (bindOneSlot0 esc reg { st with revDirs := [] } free nxt).free ∧
    bo.nxt = (bindOneSlot0 esc reg { st with revDirs := [] } free nxt).nxt ∧
    bo.vid = st.nextVid := by
  dsimp only [bindOneSlot0]
  by_cases hn : (decide (0 < arrGetU0 st.remUses st.nextVid) ||
      decide (0 < arrGetU0 esc st.nextVid)) = true
  · simp only [hn, ↓reduceIte]
    obtain ⟨h1, h2⟩ := emitSlotMem0_acc false reg (allocSlot0 free nxt st.maxSlots).slot st.revDirs
    exact ⟨by simp [h1], h2, trivial, trivial, trivial⟩
  · simp only [hn, Bool.false_eq_true, ↓reduceIte]
    exact ⟨by simp, listNoSpZero0_nil, trivial, trivial, trivial⟩

private theorem bindRetsN0_zero (esc : Array Nat) (idx : UInt32) (bl : BindListOut0) :
    bindRetsN0 esc 0 idx bl = bl := by
  rw [bindRetsN0.eq_def]; simp

private theorem bindRetsN0_succ (esc : Array Nat) {rem idx : UInt32} (hr : rem ≠ 0)
    (bl : BindListOut0) :
    bindRetsN0 esc rem idx bl =
      let bo := bindOneSlot0 esc (abiRegAt0 true idx) bl.st bl.free bl.nxt
      bindRetsN0 esc (rem - 1) (idx + 1) ⟨bo.vid :: bl.venv, bo.st, bo.free, bo.nxt⟩ := by
  have h := bindRetsN0.eq_def esc rem idx bl
  simp only [hr, ↓reduceDIte] at h
  exact h

theorem bindRetsN0_revDirs (esc : Array Nat) :
    ∀ (n : Nat) (rem idx : UInt32) (bl : BindListOut0),
      rem.toNat = n →
      let b0 := bindRetsN0 esc rem idx { bl with st := { bl.st with revDirs := [] } }
      let b := bindRetsN0 esc rem idx bl
      b.venv = b0.venv ∧ b.free = b0.free ∧ b.nxt = b0.nxt ∧
      b.st = { b0.st with revDirs := b0.st.revDirs ++ bl.st.revDirs } ∧
      ListNoSpZero0 b0.st.revDirs := by
  intro n
  induction n with
  | zero =>
    intro rem idx bl hrem
    have hr0 : rem = 0 := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hrem)
    subst hr0
    dsimp only
    rw [bindRetsN0_zero, bindRetsN0_zero]
    refine ⟨rfl, rfl, rfl, ?_, listNoSpZero0_nil⟩
    cases bl.st; simp
  | succ m ih =>
    intro rem idx bl hrem
    have hpos : 0 < rem.toNat := by omega
    have hrne : rem ≠ 0 := fun hz => by simp [hz] at hpos
    have hsub : (rem - 1).toNat = m := by rw [u32_sub1_toNat hpos, hrem]; omega
    dsimp only
    rw [bindRetsN0_succ esc hrne bl, bindRetsN0_succ esc hrne]
    let bo := bindOneSlot0 esc (abiRegAt0 true idx) bl.st bl.free bl.nxt
    let bo0 := bindOneSlot0 esc (abiRegAt0 true idx) { bl.st with revDirs := [] } bl.free bl.nxt
    have h1 := bindOneSlot0_revDirs esc (abiRegAt0 true idx) bl.st bl.free bl.nxt
    dsimp only at h1
    have h0 := bindOneSlot0_revDirs esc (abiRegAt0 true idx)
      { bl.st with revDirs := [] } bl.free bl.nxt
    dsimp only at h0
    have hvid_eq : bo.vid = bo0.vid := h1.2.2.2.2.trans h0.2.2.2.2.symm
    let bl1 : BindListOut0 := ⟨bo.vid :: bl.venv, bo.st, bo.free, bo.nxt⟩
    let bl0' : BindListOut0 := ⟨bo0.vid :: bl.venv, bo0.st, bo0.free, bo0.nxt⟩
    have ih1 := ih (rem - 1) (idx + 1) bl1 hsub
    have ih0 := ih (rem - 1) (idx + 1) bl0' hsub
    dsimp only at ih1 ih0
    have hbl_eq : { bl1 with st := { bl1.st with revDirs := [] } } =
        { bl0' with st := { bl0'.st with revDirs := [] } } := by
      have hst_z : { bl1.st with revDirs := [] } = { bl0'.st with revDirs := [] } := by
        dsimp only [bl1, bl0']; rw [h1.1]
      dsimp only [bl1, bl0']
      rw [hvid_eq, h1.2.2.1, h1.2.2.2.1, hst_z]
    rw [hbl_eq] at ih1
    let bz := bindRetsN0 esc (rem - 1) (idx + 1)
      { bl0' with st := { bl0'.st with revDirs := [] } }
    change (bindRetsN0 esc (rem - 1) (idx + 1) bl1).venv =
        (bindRetsN0 esc (rem - 1) (idx + 1) bl0').venv ∧
      (bindRetsN0 esc (rem - 1) (idx + 1) bl1).free =
        (bindRetsN0 esc (rem - 1) (idx + 1) bl0').free ∧
      (bindRetsN0 esc (rem - 1) (idx + 1) bl1).nxt =
        (bindRetsN0 esc (rem - 1) (idx + 1) bl0').nxt ∧
      (bindRetsN0 esc (rem - 1) (idx + 1) bl1).st =
        { (bindRetsN0 esc (rem - 1) (idx + 1) bl0').st with
          revDirs := (bindRetsN0 esc (rem - 1) (idx + 1) bl0').st.revDirs ++ bl.st.revDirs } ∧
      ListNoSpZero0 (bindRetsN0 esc (rem - 1) (idx + 1) bl0').st.revDirs
    refine ⟨ih1.1.trans ih0.1.symm, ih1.2.1.trans ih0.2.1.symm,
      ih1.2.2.1.trans ih0.2.2.1.symm, ?_, ?_⟩
    · have hsr : bl1.st.revDirs = bo0.st.revDirs ++ bl.st.revDirs := by
        dsimp only [bl1]; rw [h1.1]
      rw [ih1.2.2.2.1, ih0.2.2.2.1, hsr]
      change { bz.st with revDirs := bz.st.revDirs ++ (bo0.st.revDirs ++ bl.st.revDirs) } =
        { ({ bz.st with revDirs := bz.st.revDirs ++ bo0.st.revDirs } : RegaSt0) with
          revDirs := (bz.st.revDirs ++ bo0.st.revDirs) ++ bl.st.revDirs }
      cases bz.st; simp [List.append_assoc]
    · rw [ih0.2.2.2.1]
      exact listNoSpZero0_append ih0.2.2.2.2 h0.2.1

theorem emitJump0_revDirs (j : UInt32) (args : List Arg0) (task : RegaTask0) (st : RegaSt0)
    (ctrl : CtrlSt0) :
    let st' := emitJump0 j args task st ctrl
    let st0 := emitJump0 j args task { st with revDirs := [] } ctrl
    st' = { st0 with revDirs := st0.revDirs ++ st.revDirs } ∧ ListNoSpZero0 st0.revDirs := by
  dsimp only [emitJump0]
  cases args with
  | nil =>
    exact ⟨rfl, listNoSpZero0_cons (by intro h; cases h) listNoSpZero0_nil⟩
  | cons a rest =>
    cases rest with
    | nil =>
      dsimp only [emitJumpOne0]
      obtain ⟨h1, h2⟩ := emitJumpOneDir0_acc (arrGetLL0 ctrl.lblSlots (listGetU32 task.lenv j))
        a task.venv st.vslot st.revDirs
      exact ⟨by simp [h1], listNoSpZero0_cons (by intro h; cases h) h2⟩
    | cons head tail =>
      dsimp only [emitJumpMulti0]
      obtain ⟨hs1, hs2⟩ := jumpStageLoop0_acc (a :: head :: tail) task.nextSlot task.venv
        st.vslot st.revDirs
      obtain ⟨hc1, hc2⟩ := jumpCopyLoop0_acc (arrGetLL0 ctrl.lblSlots (listGetU32 task.lenv j))
        task.nextSlot (jumpStageLoop0 (a :: head :: tail) task.nextSlot task.venv st.vslot
          st.revDirs)
      obtain ⟨hc0, _⟩ := jumpCopyLoop0_acc (arrGetLL0 ctrl.lblSlots (listGetU32 task.lenv j))
        task.nextSlot (jumpStageLoop0 (a :: head :: tail) task.nextSlot task.venv st.vslot [])
      have hcomb : jumpCopyLoop0 (arrGetLL0 ctrl.lblSlots (listGetU32 task.lenv j)) task.nextSlot
          (jumpStageLoop0 (a :: head :: tail) task.nextSlot task.venv st.vslot st.revDirs) =
          jumpCopyLoop0 (arrGetLL0 ctrl.lblSlots (listGetU32 task.lenv j)) task.nextSlot
            (jumpStageLoop0 (a :: head :: tail) task.nextSlot task.venv st.vslot []) ++
            st.revDirs := by
        rw [hc1, hs1, hc0, List.append_assoc]
      refine ⟨by rw [hcomb]; rfl,
        listNoSpZero0_cons (by intro h; cases h) (by rw [hc0]; exact listNoSpZero0_append hc2 hs2)⟩

private theorem stepLinear0_revDirs_append (esc : Array Nat) (task : RegaTask0) (p0 : RegaSt0)
    (d : List Dir0) (ctrl : CtrlSt0) (rest : List RegaTask0) :
    let ls0 := stepLinear0 esc task p0 ctrl rest
    let ls := stepLinear0 esc task { p0 with revDirs := p0.revDirs ++ d } ctrl rest
    ls.work = ls0.work ∧ ls.ctrl = ls0.ctrl ∧
    ls.st = { ls0.st with revDirs := ls0.st.revDirs ++ d } := by
  dsimp only [stepLinear0, stepLinBindPush0, linBindPush0]
  obtain ⟨hl1, _⟩ := emitLinNode0_acc task { p0 with revDirs := p0.revDirs ++ d }
  obtain ⟨hl0, _⟩ := emitLinNode0_acc task p0
  have hl : emitLinNode0 task { p0 with revDirs := p0.revDirs ++ d } =
      emitLinNode0 task p0 ++ d := by
    rw [hl1, hl0]
    change emitLinNode0 task { p0 with revDirs := [] } ++ (p0.revDirs ++ d) =
      (emitLinNode0 task { p0 with revDirs := [] } ++ p0.revDirs) ++ d
    simp only [List.append_assoc]
  let rr := relNodeArgs0 esc p0.vslot task.venv task.node
    (RelRes0.mk p0.remUses task.freeSlots)
  have hbr := bindRetsN0_revDirs esc (linCnt0 task.node).toNat (linCnt0 task.node) 0
    ⟨task.venv, { p0 with remUses := rr.remUses, revDirs := emitLinNode0 task p0 },
      rr.free, task.nextSlot⟩ rfl
  have hbr_s := bindRetsN0_revDirs esc (linCnt0 task.node).toNat (linCnt0 task.node) 0
    ⟨task.venv, { p0 with remUses := rr.remUses, revDirs := emitLinNode0 task p0 ++ d },
      rr.free, task.nextSlot⟩ rfl
  dsimp only [relAndUpdateSt0] at *
  rw [hl]
  let bz := { p0 with remUses := rr.remUses, revDirs := [] }
  let stA : RegaSt0 := { p0 with remUses := rr.remUses, revDirs := emitLinNode0 task p0 ++ d }
  let stB : RegaSt0 := { p0 with remUses := rr.remUses, revDirs := emitLinNode0 task p0 }
  refine ⟨?_, rfl, ?_⟩
  · have hbz_eq : { stA with revDirs := [] } = bz := rfl
    have hbz_eq0 : { stB with revDirs := [] } = bz := rfl
    rw [hbr_s.1, hbr_s.2.1, hbr_s.2.2.1, hbz_eq, ← hbz_eq0, ← hbr.1, ← hbr.2.1, ← hbr.2.2.1]
  · have hbz_eq : { stA with revDirs := [] } = bz := rfl
    rw [hbr_s.2.2.2.1, hbr.2.2.2.1, hbz_eq]
    dsimp only
    simp only [List.append_assoc]

private theorem regaStep0_revDirs_append (esc : Array Nat) (cur : RegaTask0) (st : RegaSt0)
    (ctrl : CtrlSt0) (rest : List RegaTask0) :
    let st0 := regaPrependLbl0 cur { st with revDirs := [] } ctrl
    let ls0 := regaStep0 esc cur st0 ctrl rest
    let ls := regaStep0 esc cur (regaPrependLbl0 cur st ctrl) ctrl rest
    ls.work = ls0.work ∧ ls.ctrl = ls0.ctrl ∧
    ls.st = { ls0.st with revDirs := ls0.st.revDirs ++ st.revDirs } := by
  have hpre : ∀ s : RegaSt0,
      regaPrependLbl0 cur s ctrl =
        { (regaPrependLbl0 cur { s with revDirs := [] } ctrl) with
          revDirs :=
            (regaPrependLbl0 cur { s with revDirs := [] } ctrl).revDirs ++ s.revDirs } := by
    intro s; dsimp only [regaPrependLbl0]
    split <;> simp
  rw [hpre st]
  let p0 := regaPrependLbl0 cur { st with revDirs := [] } ctrl
  rcases cur with ⟨lbl, nd, venv, lenv, free, nextSlot⟩
  dsimp only [regaStep0]
  cases nd with
  | jnz c t e =>
    dsimp only [stepJnzPush0, jnzBuildSt0, jnzWrapRes0]
    obtain ⟨hj1, _⟩ := jnzPrep0_revDirs esc c ⟨lbl, .jnz c t e, venv, lenv, free, nextSlot⟩
      { p0 with revDirs := p0.revDirs ++ st.revDirs } ctrl
    obtain ⟨hj0, _⟩ := jnzPrep0_revDirs esc c ⟨lbl, .jnz c t e, venv, lenv, free, nextSlot⟩
      p0 ctrl
    have hj : (jnzPrep0 esc c ⟨lbl, .jnz c t e, venv, lenv, free, nextSlot⟩
        { p0 with revDirs := p0.revDirs ++ st.revDirs } ctrl).2 =
        (jnzPrep0 esc c ⟨lbl, .jnz c t e, venv, lenv, free, nextSlot⟩ p0 ctrl).2 ++ st.revDirs := by
      rw [hj1, hj0]
      change (jnzPrep0 esc c ⟨lbl, .jnz c t e, venv, lenv, free, nextSlot⟩
          { p0 with revDirs := [] } ctrl).2 ++ (p0.revDirs ++ st.revDirs) = _
      simp only [List.append_assoc]
    rw [hj]
    exact ⟨rfl, rfl, rfl⟩
  | group bodies k =>
    have hp : ∀ bs venv' (gp : GroupPrepOut0) d,
        regaPrepGroup0 bs venv' { gp with st := { gp.st with revDirs := gp.st.revDirs ++ d } } =
        let r := regaPrepGroup0 bs venv' gp
        { r with st := { r.st with revDirs := r.st.revDirs ++ d } } := by
      intro bs
      induction bs with
      | nil => intro _ _ _; rfl
      | cons p bs ih =>
        intro venv' gp d; rcases p with ⟨pts, b⟩
        have hbb : ∀ ts v (s0 : RegaSt0) f n d',
            bindBlockParams0 ts v { s0 with revDirs := s0.revDirs ++ d' } f n =
              let bb := bindBlockParams0 ts v s0 f n
              { bb with st := { bb.st with revDirs := bb.st.revDirs ++ d' } } := by
          intro ts
          induction ts with
          | nil => intro _ _ _ _ _; rfl
          | cons _ _ ihb =>
            intro v s0 f n d'
            dsimp only [bindBlockParams0, bindOneBlockSlot0]
            let s1 : RegaSt0 :=
              { s0 with
                nextVid := s0.nextVid + 1
                maxSlots := (allocSlot0 f n s0.maxSlots).maxSlots
                vslot := s0.vslot.push (allocSlot0 f n s0.maxSlots).slot.toNat }
            exact ihb (s0.nextVid :: v) s1
              (allocSlot0 f n s0.maxSlots).free (allocSlot0 f n s0.maxSlots).nxt d'
        dsimp only [regaPrepGroup0, prepOneBlock0, prepOneBind0, prepFinishBlock0, prepUpdCtrl0]
        rw [hbb]
        let bb := bindBlockParams0 pts venv' gp.st gp.free gp.nxt
        let slots := slotsOfVids0 (tyLenU0 pts 0) bb.venv bb.st.vslot []
        let ctrl1 : CtrlSt0 :=
          CtrlSt0.mk gp.ctrl.fnIdx (gp.ctrl.nextLbl + 1) (gp.ctrl.lblSlots.push slots)
        let gm1 : GroupMeta0 := GroupMeta0.mk gp.ctrl.nextLbl b bb.venv
        let gp1 : GroupPrepOut0 :=
          GroupPrepOut0.mk (gp.ctrl.nextLbl :: gp.lenv) bb.st ctrl1 bb.free bb.nxt
            (gm1 :: gp.metas)
        exact ih venv' gp1 d
    dsimp only [stepGroupFinish0, stepGroupPrep0, groupEnqCont0]
    have hp' := hp bodies venv ⟨lenv, p0, ctrl, free, nextSlot, []⟩ st.revDirs
    dsimp only at hp'
    rw [hp']
    exact ⟨rfl, rfl, rfl⟩
  | let1 op args k =>
    exact stepLinear0_revDirs_append esc
      ⟨lbl, .let1 op args k, venv, lenv, free, nextSlot⟩ p0 st.revDirs ctrl rest
  | let2Umulw64 a b k =>
    exact stepLinear0_revDirs_append esc
      ⟨lbl, .let2Umulw64 a b k, venv, lenv, free, nextSlot⟩ p0 st.revDirs ctrl rest
  | load t addr k =>
    exact stepLinear0_revDirs_append esc
      ⟨lbl, .load t addr k, venv, lenv, free, nextSlot⟩ p0 st.revDirs ctrl rest
  | store t val addr k =>
    exact stepLinear0_revDirs_append esc
      ⟨lbl, .store t val addr k, venv, lenv, free, nextSlot⟩ p0 st.revDirs ctrl rest
  | call fn as rs args k =>
    exact stepLinear0_revDirs_append esc
      ⟨lbl, .call fn as rs args k, venv, lenv, free, nextSlot⟩ p0 st.revDirs ctrl rest
  | tailCall fnSym as args =>
    dsimp only [regaStepCtrl0, stepTail0]
    obtain ⟨hla1, _⟩ := loadRegArgs0_acc ⟨false, true, venv, p0.vslot⟩ as args 0
      (p0.revDirs ++ st.revDirs)
    obtain ⟨hla0, _⟩ := loadRegArgs0_acc ⟨false, true, venv, p0.vslot⟩ as args 0 p0.revDirs
    have hla : loadRegArgs0 ⟨false, true, venv, p0.vslot⟩ as args 0
        (p0.revDirs ++ st.revDirs) =
        loadRegArgs0 ⟨false, true, venv, p0.vslot⟩ as args 0 p0.revDirs ++ st.revDirs := by
      rw [hla1, hla0, List.append_assoc]
    rw [hla]; exact ⟨rfl, rfl, rfl⟩
  | exit fnSym as args =>
    dsimp only [regaStepCtrl0, stepTail0]
    obtain ⟨hla1, _⟩ := loadRegArgs0_acc ⟨false, true, venv, p0.vslot⟩ as args 0
      (p0.revDirs ++ st.revDirs)
    obtain ⟨hla0, _⟩ := loadRegArgs0_acc ⟨false, true, venv, p0.vslot⟩ as args 0 p0.revDirs
    have hla : loadRegArgs0 ⟨false, true, venv, p0.vslot⟩ as args 0
        (p0.revDirs ++ st.revDirs) =
        loadRegArgs0 ⟨false, true, venv, p0.vslot⟩ as args 0 p0.revDirs ++ st.revDirs := by
      rw [hla1, hla0, List.append_assoc]
    rw [hla]; exact ⟨rfl, rfl, rfl⟩
  | jump j args =>
    dsimp only [regaStepCtrl0]
    obtain ⟨hj1, _⟩ := emitJump0_revDirs j args ⟨lbl, .jump j args, venv, lenv, free, nextSlot⟩
      { p0 with revDirs := p0.revDirs ++ st.revDirs } ctrl
    obtain ⟨hj0, _⟩ := emitJump0_revDirs j args ⟨lbl, .jump j args, venv, lenv, free, nextSlot⟩
      p0 ctrl
    have hj : emitJump0 j args ⟨lbl, .jump j args, venv, lenv, free, nextSlot⟩
          { p0 with revDirs := p0.revDirs ++ st.revDirs } ctrl =
        { emitJump0 j args ⟨lbl, .jump j args, venv, lenv, free, nextSlot⟩ p0 ctrl with
          revDirs := (emitJump0 j args ⟨lbl, .jump j args, venv, lenv, free, nextSlot⟩ p0
            ctrl).revDirs ++ st.revDirs } := by
      rw [hj1, hj0]
      cases emitJump0 j args ⟨lbl, .jump j args, venv, lenv, free, nextSlot⟩
        { p0 with revDirs := [] } ctrl
      simp only [List.append_assoc]
    rw [hj]; exact ⟨rfl, rfl, rfl⟩
  | ret vs =>
    dsimp only [regaStepCtrl0, stepRet0]
    obtain ⟨hla1, _⟩ := loadRegArgs0_acc ⟨true, false, venv, p0.vslot⟩ [] vs 0
      (p0.revDirs ++ st.revDirs)
    obtain ⟨hla0, _⟩ := loadRegArgs0_acc ⟨true, false, venv, p0.vslot⟩ [] vs 0 p0.revDirs
    have hla : loadRegArgs0 ⟨true, false, venv, p0.vslot⟩ [] vs 0
        (p0.revDirs ++ st.revDirs) =
        loadRegArgs0 ⟨true, false, venv, p0.vslot⟩ [] vs 0 p0.revDirs ++ st.revDirs := by
      rw [hla1, hla0, List.append_assoc]
    rw [hla]; exact ⟨rfl, rfl, rfl⟩
  | hlt => dsimp only [regaStepCtrl0]; exact ⟨rfl, rfl, rfl⟩

theorem regaRunAux0_revDirs_append (fuel : UInt32) (esc : Array Nat) (st : RegaSt0)
    (ctrl : CtrlSt0) (work : List RegaTask0) :
    let r0 := regaRunAux0 fuel esc { st with revDirs := [] } ctrl work
    regaRunAux0 fuel esc st ctrl work =
      ({ r0.1 with revDirs := r0.1.revDirs ++ st.revDirs }, r0.2) := by
  suffices h : ∀ (m : Nat) (fuel : UInt32) (st : RegaSt0) (ctrl : CtrlSt0)
      (work : List RegaTask0),
      fuel.toNat = m →
      let r0 := regaRunAux0 fuel esc { st with revDirs := [] } ctrl work
      regaRunAux0 fuel esc st ctrl work =
        ({ r0.1 with revDirs := r0.1.revDirs ++ st.revDirs }, r0.2) from
    h fuel.toNat fuel st ctrl work rfl
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro fuel st ctrl work hfuel
    by_cases hf0 : fuel = 0
    · subst hf0; cases st; simp only [regaRunAux0_zero, List.nil_append]
    · have hlt : (fuel - 1).toNat < m := hfuel ▸ u32Sub1Lt0 fuel hf0
      cases work with
      | nil => cases st; simp only [regaRunAux0_nil, List.nil_append]
      | cons cur rest =>
        have hdef1 := regaRunAux0_succ hf0 esc st ctrl cur rest
        have hdef0 := regaRunAux0_succ hf0 esc { st with revDirs := [] } ctrl cur rest
        have hstep := regaStep0_revDirs_append esc cur st ctrl rest
        dsimp only at hstep
        let st0 := regaPrependLbl0 cur { st with revDirs := [] } ctrl
        let ls0 := regaStep0 esc cur st0 ctrl rest
        have ih1 := ih (fuel - 1).toNat hlt (fuel - 1) ls0.st ls0.ctrl ls0.work rfl
        have ih2 := ih (fuel - 1).toNat hlt (fuel - 1)
          { ls0.st with revDirs := ls0.st.revDirs ++ st.revDirs } ls0.ctrl ls0.work rfl
        have hz : { RegaSt0.mk ls0.st.nextVid ls0.st.maxSlots ls0.st.vslot ls0.st.remUses
            (ls0.st.revDirs ++ st.revDirs) with revDirs := [] } =
            { ls0.st with revDirs := [] } := rfl
        dsimp only at ih1 ih2
        rw [hz] at ih2
        dsimp only
        rw [hdef1, hdef0, hstep.1, hstep.2.1, hstep.2.2, ih2, ih1]
        simp only [List.append_assoc]

theorem bindOneEntryArg0_acc (i : UInt32) (t : Ty0) (st : RegaSt0) :
    let st' := bindOneEntryArg0 i t st
    let st0 := bindOneEntryArg0 i t { st with revDirs := [] }
    st' = { st0 with revDirs := st0.revDirs ++ st.revDirs } ∧ ListNoSpZero0 st0.revDirs ∧
    st'.nextVid = st.nextVid + 1 ∧ st'.maxSlots = u32Max0 st.maxSlots (i + 1) ∧
    st'.vslot = st.vslot.push i.toNat ∧ st'.remUses = st.remUses := by
  dsimp only [bindOneEntryArg0]
  obtain ⟨hc1, hc2⟩ := emitCanon0_acc (tyWidth0 t) (abiRegAt0 false i) st.revDirs
  obtain ⟨hs1, hs2⟩ := emitSlotMem0_acc false (abiRegAt0 false i) i
    (emitCanon0 (tyWidth0 t) (abiRegAt0 false i) st.revDirs)
  obtain ⟨hs0, _⟩ := emitSlotMem0_acc false (abiRegAt0 false i) i
    (emitCanon0 (tyWidth0 t) (abiRegAt0 false i) [])
  have hrev : emitSlotMem0 false (abiRegAt0 false i) i
      (emitCanon0 (tyWidth0 t) (abiRegAt0 false i) st.revDirs) =
      emitSlotMem0 false (abiRegAt0 false i) i
        (emitCanon0 (tyWidth0 t) (abiRegAt0 false i) []) ++ st.revDirs := by
    rw [hs1, hc1, hs0, List.append_assoc]
  exact ⟨by simp [hrev], hs0 ▸ listNoSpZero0_append hs2 hc2, rfl, rfl, rfl, rfl⟩

theorem bindEntryArgs0_acc :
    ∀ (ts : List Ty0) (i : UInt32) (venv : List UInt32) (st : RegaSt0),
      let bl := bindEntryArgs0 ts i venv st
      let bl0 := bindEntryArgs0 ts i venv { st with revDirs := [] }
      bl.venv = bl0.venv ∧ bl.free = [] ∧ bl0.free = [] ∧
      bl.nxt = UInt32.ofNat (i.toNat + ts.length) ∧
      bl.st = { bl0.st with revDirs := bl0.st.revDirs ++ st.revDirs } ∧
      ListNoSpZero0 bl0.st.revDirs ∧
      bl.st.nextVid = UInt32.ofNat (st.nextVid.toNat + ts.length) ∧
      bl.st.remUses = st.remUses ∧
      bl.st.vslot.size = st.vslot.size + ts.length := by
  intro ts
  induction ts with
  | nil =>
    intro i venv st
    dsimp only [bindEntryArgs0, List.length_nil]
    simp [listNoSpZero0_nil, UInt32.ofNat_toNat]
  | cons t rest ih =>
    intro i venv st
    dsimp only [bindEntryArgs0]
    have h1 := bindOneEntryArg0_acc i t st
    let st10 := bindOneEntryArg0 i t { st with revDirs := [] }
    have ih1 := ih (i + 1) (st.nextVid :: venv)
      { st10 with revDirs := st10.revDirs ++ st.revDirs }
    have ih0 := ih (i + 1) (st.nextVid :: venv) st10
    have hst1 : bindOneEntryArg0 i t st =
        { st10 with revDirs := st10.revDirs ++ st.revDirs } := h1.1
    have hz : { RegaSt0.mk st10.nextVid st10.maxSlots st10.vslot st10.remUses
        (st10.revDirs ++ st.revDirs) with revDirs := [] } =
        { st10 with revDirs := [] } := rfl
    have hz0 : (bindOneEntryArg0 i t { st with revDirs := [] }).nextVid = st.nextVid + 1 := rfl
    rw [hst1]
    refine ⟨?_, ih1.2.1, ih0.2.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ih1.1, hz, ih0.1]
    · rw [ih1.2.2.2.1, u32_ofNat_succ_add]; rfl
    · rw [ih1.2.2.2.2.1, hz, ih0.2.2.2.2.1]
      cases (bindEntryArgs0 rest (i + 1) (st.nextVid :: venv)
        { st10 with revDirs := [] }).st
      simp [List.append_assoc]
    · rw [ih0.2.2.2.2.1]
      exact listNoSpZero0_append ih0.2.2.2.2.2.1 h1.2.1
    · rw [ih1.2.2.2.2.2.2.1, hz0, u32_ofNat_succ_add]; rfl
    · rw [ih1.2.2.2.2.2.2.2.1]; exact h1.2.2.2.2.2
    · rw [ih1.2.2.2.2.2.2.2.2]
      dsimp only [st10, bindOneEntryArg0]
      rw [Array.size_push]
      simp [List.length_cons, Nat.add_assoc, Nat.add_comm 1]

private theorem pushDImm0_spAdd_false (imm : UInt64) (acc : List Dir0) :
    pushDImm0 1 .rsp imm acc = .spAdd false imm :: acc := by
  simp [pushDImm0]

theorem patchEpilogues0_stepTail0 (fSz : UInt64) (fnSym : Sym0) (as : List Ty0)
    (args : List Arg0) (cur : RegaTask0) (st : RegaSt0) :
    patchEpilogues0 fSz (emitFwd0 (stepTail0 fnSym as args cur st).revDirs) [] =
      patchEpilogues0 fSz (emitFwd0 st.revDirs) [] ++
        emitFwd0 (loadRegArgs0 ⟨false, true, cur.venv, st.vslot⟩ as args 0 []) ++
        emitFwd0 (emitSpAdj0 false fSz []) ++ [.jmp (.sym fnSym)] := by
  dsimp only [stepTail0]
  rw [pushDImm0_spAdd_false]
  obtain ⟨hl1, hl2⟩ := loadRegArgs0_acc ⟨false, true, cur.venv, st.vslot⟩ as args 0 st.revDirs
  rw [hl1, emitFwd0_cons, emitFwd0_cons, emitFwd0_append, patchEpilogues0_append,
    patchEpilogues0_append, patchEpilogues0_append]
  have hsp : patchEpilogues0 fSz [.spAdd false 0] [] =
      emitFwd0 (emitSpAdj0 false fSz []) := by
    rw [patchEpilogues0_eq, List.flatMap_singleton, patchDir0, emitFwd0_revDirAux0]
  have hjmp : patchEpilogues0 fSz [.jmp (.sym fnSym)] [] = [.jmp (.sym fnSym)] := by
    rw [patchEpilogues0_eq, List.flatMap_singleton]; rfl
  have hargs : patchEpilogues0 fSz
      (emitFwd0 (loadRegArgs0 ⟨false, true, cur.venv, st.vslot⟩ as args 0 [])) [] =
      emitFwd0 (loadRegArgs0 ⟨false, true, cur.venv, st.vslot⟩ as args 0 []) :=
    patchEpilogues0_of_listNoSpZero0 fSz (listNoSpZero0_reverse hl2)
  rw [hsp, hjmp, hargs]

theorem patchEpilogues0_stepRet0 (fSz : UInt64) (vs : List Arg0) (cur : RegaTask0)
    (st : RegaSt0) :
    patchEpilogues0 fSz (emitFwd0 (stepRet0 vs cur st).revDirs) [] =
      patchEpilogues0 fSz (emitFwd0 st.revDirs) [] ++
        emitFwd0 (loadRegArgs0 ⟨true, false, cur.venv, st.vslot⟩ [] vs 0 []) ++
        emitFwd0 (emitSpAdj0 false fSz []) ++ [.ret] := by
  dsimp only [stepRet0]
  rw [pushDImm0_spAdd_false]
  obtain ⟨hl1, hl2⟩ := loadRegArgs0_acc ⟨true, false, cur.venv, st.vslot⟩ [] vs 0 st.revDirs
  rw [hl1, emitFwd0_cons, emitFwd0_cons, emitFwd0_append, patchEpilogues0_append,
    patchEpilogues0_append, patchEpilogues0_append]
  have hsp : patchEpilogues0 fSz [.spAdd false 0] [] =
      emitFwd0 (emitSpAdj0 false fSz []) := by
    rw [patchEpilogues0_eq, List.flatMap_singleton, patchDir0, emitFwd0_revDirAux0]
  have hret : patchEpilogues0 fSz [.ret] [] = [.ret] := by
    rw [patchEpilogues0_eq, List.flatMap_singleton]; rfl
  have hargs : patchEpilogues0 fSz
      (emitFwd0 (loadRegArgs0 ⟨true, false, cur.venv, st.vslot⟩ [] vs 0 [])) [] =
      emitFwd0 (loadRegArgs0 ⟨true, false, cur.venv, st.vslot⟩ [] vs 0 []) :=
    patchEpilogues0_of_listNoSpZero0 fSz (listNoSpZero0_reverse hl2)
  rw [hsp, hret, hargs]

/-! ## 3. Arrays, `PrePass0` Invariants, & Exact Spine Occurrence Accounting -/

private theorem arrGetU0_eq (arr : Array Nat) (i : UInt32) :
    (arrGetU0 arr i).toNat = arr.getD i.toNat 0 % 2 ^ 32 := by
  dsimp only [arrGetU0]
  rw [u32_toNat_ofNat]

private theorem arrGetU0_of_lt (arr : Array Nat) (i : UInt32)
    (hlt : arr.getD i.toNat 0 < 2 ^ 32) :
    (arrGetU0 arr i).toNat = arr.getD i.toNat 0 := by
  rw [arrGetU0_eq, Nat.mod_eq_of_lt hlt]

private theorem arrSetU0_size (arr : Array Nat) (i v : UInt32) :
    (arrSetU0 arr i v).size = arr.size := by
  dsimp only [arrSetU0, Array.set!]
  exact Array.size_setIfInBounds

private theorem arrSetU0_getD (arr : Array Nat) (i v : UInt32) (hi : i.toNat < arr.size)
    (j : Nat) :
    (arrSetU0 arr i v).getD j 0 = if j = i.toNat then v.toNat else arr.getD j 0 := by
  dsimp only [arrSetU0, Array.set!, Array.getD]
  by_cases hj : j < arr.size
  · have hlt : j < (arr.setIfInBounds i.toNat v.toNat).size := by
      rw [Array.size_setIfInBounds]; exact hj
    simp only [hj, hlt, ↓reduceDIte]
    change (arr.setIfInBounds i.toNat v.toNat)[j] = if j = i.toNat then v.toNat else arr[j]
    rw [Array.getElem_setIfInBounds]
    · split <;> rename_i heq
      · subst heq; simp
      · simp [Ne.symm heq]
    · exact hj
  · have hge : ¬ j < (arr.setIfInBounds i.toNat v.toNat).size := by
      rw [Array.size_setIfInBounds]; exact hj
    simp only [hj, hge, ↓reduceDIte]
    have hne : j ≠ i.toNat := fun h => hj (h ▸ hi)
    simp [hne]

private theorem arrPush_getD {α : Type} (arr : Array α) (x d : α) (j : Nat) :
    (arr.push x).getD j d =
      if j < arr.size then arr.getD j d else if j = arr.size then x else d := by
  dsimp only [Array.getD]
  by_cases hj : j < arr.size
  · have hlt : j < (arr.push x).size := by rw [Array.size_push]; omega
    simp only [hj, hlt, ↓reduceDIte]
    exact Array.getElem_push_lt hj
  · by_cases heq : j = arr.size
    · subst heq
      have hlt : arr.size < (arr.push x).size := by rw [Array.size_push]; omega
      simp only [Nat.lt_irrefl, hlt, ↓reduceDIte]
      exact Array.getElem_push_eq
    · have hge : ¬ j < (arr.push x).size := by rw [Array.size_push]; omega
      simp only [hj, heq, hge, ↓reduceDIte, ite_false]

private theorem arrGetLL0_eq (arr : Array (List UInt32)) (i : UInt32) :
    arrGetLL0 arr i = arr.getD i.toNat [] := rfl

/-- Functional `venv` extension matching `preBindLoop0`, `bindRetsN0`, `bindBlockParams0`,
and `bindEntryArgs0`. -/
@[expose] def pushFreshVids0 : Nat → UInt32 → List UInt32 → List UInt32
  | 0, _, venv => venv
  | n + 1, nxt, venv => pushFreshVids0 n (nxt + 1) (nxt :: venv)

theorem pushFreshVids0_length (n : Nat) (nxt : UInt32) (venv : List UInt32) :
    (pushFreshVids0 n nxt venv).length = venv.length + n := by
  induction n generalizing nxt venv with
  | zero => rfl
  | succ m ih =>
    dsimp only [pushFreshVids0]
    rw [ih, List.length_cons]
    omega

theorem mem_pushFreshVids0 :
    ∀ (n : Nat) (nxt : UInt32) (venv : List UInt32) (v : UInt32),
      v ∈ pushFreshVids0 n nxt venv ↔
        v ∈ venv ∨ ∃ k < n, v = nxt + UInt32.ofNat k
  | 0, _, venv, v => by
    dsimp only [pushFreshVids0]
    exact ⟨Or.inl, fun | Or.inl h => h | Or.inr ⟨_, hk, _⟩ => absurd hk (Nat.not_lt_zero _)⟩
  | m + 1, nxt, venv, v => by
    dsimp only [pushFreshVids0]
    rw [mem_pushFreshVids0 m (nxt + 1) (nxt :: venv) v, List.mem_cons]
    constructor
    · rintro ((rfl | hv) | ⟨k, hk, rfl⟩)
      · exact Or.inr ⟨0, Nat.zero_lt_succ m, (u32_add_zero v).symm⟩
      · exact Or.inl hv
      · exact Or.inr ⟨k + 1, Nat.succ_lt_succ hk, u32_succ_add_ofNat nxt k⟩
    · rintro (hv | ⟨k, hk, rfl⟩)
      · exact Or.inl (Or.inr hv)
      · cases k with
        | zero => exact Or.inl (Or.inl (u32_add_zero nxt))
        | succ k' =>
          exact Or.inr ⟨k', Nat.lt_of_succ_lt_succ hk, (u32_succ_add_ofNat nxt k').symm⟩

private theorem preBindLoop0_zero (scope : UInt32) (venv : List UInt32) (st : PreSt0) :
    preBindLoop0 0 scope venv st = (venv, st) := by
  rw [preBindLoop0.eq_def]; simp

private theorem preBindLoop0_succ {n scope : UInt32} (hn : n ≠ 0) (venv : List UInt32)
    (st : PreSt0) :
    preBindLoop0 n scope venv st =
      preBindLoop0 (n - 1) scope (st.nextVid :: venv)
        { nextVid := st.nextVid + 1
          defScope := st.defScope.push scope.toNat
          uses := st.uses.push 0
          escaped := st.escaped.push 0 } := by
  have h := preBindLoop0.eq_def n scope venv st
  simp only [hn, ↓reduceDIte] at h
  exact h

theorem preBindLoop0_spec :
    ∀ (m : Nat) (n scope : UInt32) (venv : List UInt32) (st : PreSt0),
      n.toNat = m → st.nextVid.toNat + m < 2 ^ 32 →
      st.defScope.size = st.nextVid.toNat →
      st.uses.size = st.nextVid.toNat →
      st.escaped.size = st.nextVid.toNat →
      let out := preBindLoop0 n scope venv st
      out.1 = pushFreshVids0 m st.nextVid venv ∧
      out.2.nextVid.toNat = st.nextVid.toNat + m ∧
      out.2.defScope.size = st.nextVid.toNat + m ∧
      out.2.uses.size = st.nextVid.toNat + m ∧
      out.2.escaped.size = st.nextVid.toNat + m ∧
      (∀ v, out.2.defScope.getD v 0 =
        if v < st.nextVid.toNat then st.defScope.getD v 0
        else if v < st.nextVid.toNat + m then scope.toNat else 0) ∧
      (∀ v, out.2.uses.getD v 0 =
        if v < st.nextVid.toNat then st.uses.getD v 0 else 0) ∧
      (∀ v, out.2.escaped.getD v 0 =
        if v < st.nextVid.toNat then st.escaped.getD v 0 else 0) := by
  intro m
  induction m with
  | zero =>
    intro n scope venv st hn hlt hs1 hs2 hs3
    have hn0 : n = 0 := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hn)
    subst hn0
    dsimp only
    rw [preBindLoop0_zero]
    dsimp only [pushFreshVids0]; rw [Nat.add_zero]
    refine ⟨rfl, rfl, hs1, hs2, hs3, fun v => ?_, fun v => ?_, fun v => ?_⟩
    · by_cases hv : v < st.nextVid.toNat
      · simp [hv]
      · simp only [hv, ↓reduceIte]
        dsimp only [Array.getD]; simp [show ¬ v < st.defScope.size by omega]
    · by_cases hv : v < st.nextVid.toNat
      · simp [hv]
      · simp only [hv, ↓reduceIte]
        dsimp only [Array.getD]; simp [show ¬ v < st.uses.size by omega]
    · by_cases hv : v < st.nextVid.toNat
      · simp [hv]
      · simp only [hv, ↓reduceIte]
        dsimp only [Array.getD]; simp [show ¬ v < st.escaped.size by omega]
  | succ m ih =>
    intro n scope venv st hn hlt hs1 hs2 hs3
    have hn_ne : n ≠ 0 := fun h => by subst h; simp at hn
    have hn1 : (n - 1).toNat = m := by rw [u32_sub1_toNat (by omega), hn]; omega
    have hnv : (st.nextVid + 1).toNat = st.nextVid.toNat + 1 := u32_add1_toNat (by omega)
    dsimp only
    rw [preBindLoop0_succ hn_ne]
    dsimp only [pushFreshVids0]
    let st' : PreSt0 :=
      { nextVid := st.nextVid + 1
        defScope := st.defScope.push scope.toNat
        uses := st.uses.push 0
        escaped := st.escaped.push 0 }
    have hs1' : st'.defScope.size = st'.nextVid.toNat := by
      simp [st', Array.size_push, hs1, hnv]
    have hs2' : st'.uses.size = st'.nextVid.toNat := by
      simp [st', Array.size_push, hs2, hnv]
    have hs3' : st'.escaped.size = st'.nextVid.toNat := by
      simp [st', Array.size_push, hs3, hnv]
    have h_ih := ih (n - 1) scope (st.nextVid :: venv) st' hn1 (by rw [hnv]; omega) hs1' hs2' hs3'
    dsimp only at h_ih
    refine ⟨h_ih.1, ?_, ?_, ?_, ?_, fun v => ?_, fun v => ?_, fun v => ?_⟩
    · rw [h_ih.2.1, hnv]; omega
    · rw [h_ih.2.2.1, hnv]; omega
    · rw [h_ih.2.2.2.1, hnv]; omega
    · rw [h_ih.2.2.2.2.1, hnv]; omega
    · rw [h_ih.2.2.2.2.2.1 v, hnv]
      dsimp only [st']
      rw [arrPush_getD st.defScope scope.toNat 0 v, hs1]
      by_cases hv1 : v < st.nextVid.toNat
      · simp [hv1, show v < st.nextVid.toNat + 1 by omega]
      · by_cases hv2 : v = st.nextVid.toNat
        · subst hv2; simp [show st.nextVid.toNat < st.nextVid.toNat + (m + 1) by omega]
        · have hv3 : ¬ v < st.nextVid.toNat + 1 := by omega
          simp [hv1, hv3, show st.nextVid.toNat + 1 + m = st.nextVid.toNat + (m + 1) by omega]
    · rw [h_ih.2.2.2.2.2.2.1 v, hnv]
      dsimp only [st']
      rw [arrPush_getD st.uses 0 0 v, hs2]
      by_cases hv1 : v < st.nextVid.toNat
      · simp [hv1, show v < st.nextVid.toNat + 1 by omega]
      · by_cases hv2 : v = st.nextVid.toNat
        · subst hv2; simp
        · simp [hv1, show ¬ v < st.nextVid.toNat + 1 by omega]
    · rw [h_ih.2.2.2.2.2.2.2 v, hnv]
      dsimp only [st']
      rw [arrPush_getD st.escaped 0 0 v, hs3]
      by_cases hv1 : v < st.nextVid.toNat
      · simp [hv1, show v < st.nextVid.toNat + 1 by omega]
      · by_cases hv2 : v = st.nextVid.toNat
        · subst hv2; simp
        · simp [hv1, show ¬ v < st.nextVid.toNat + 1 by omega]

theorem bindEntryArgs0_venv :
    ∀ (ts : List Ty0) (i : UInt32) (venv : List UInt32) (st : RegaSt0),
      (bindEntryArgs0 ts i venv st).venv = pushFreshVids0 ts.length st.nextVid venv
  | [], _, venv, _ => rfl
  | t :: rest, i, venv, st => by
    dsimp only [bindEntryArgs0, pushFreshVids0, List.length_cons]
    exact bindEntryArgs0_venv rest (i + 1) (st.nextVid :: venv) (bindOneEntryArg0 i t st)

theorem bindRetsN0_venv (esc : Array Nat) :
    ∀ (m : Nat) (rem idx : UInt32) (bl : BindListOut0),
      rem.toNat = m →
      (bindRetsN0 esc rem idx bl).venv = pushFreshVids0 m bl.st.nextVid bl.venv := by
  intro m
  induction m with
  | zero =>
    intro rem idx bl hr
    have hr0 : rem = 0 := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hr)
    subst hr0; rw [bindRetsN0_zero]; rfl
  | succ k ih =>
    intro rem idx bl hr
    have hpos : 0 < rem.toNat := by omega
    have hne : rem ≠ 0 := fun h => by simp [h] at hpos
    have hsub : (rem - 1).toNat = k := by rw [u32_sub1_toNat hpos, hr]; omega
    rw [bindRetsN0_succ esc hne]
    let bo := bindOneSlot0 esc (abiRegAt0 true idx) bl.st bl.free bl.nxt
    have hvid : bo.vid = bl.st.nextVid := (bindOneSlot0_revDirs _ _ _ _ _).2.2.2.2
    have hnxt : bo.st.nextVid = bl.st.nextVid + 1 := by
      dsimp only [bo, bindOneSlot0]; split <;> rfl
    rw [ih (rem - 1) (idx + 1) ⟨bo.vid :: bl.venv, bo.st, bo.free, bo.nxt⟩ hsub]
    dsimp only
    rw [hvid, hnxt]; dsimp only [pushFreshVids0]

theorem bindBlockParams0_venv :
    ∀ (pts : List Ty0) (venv : List UInt32) (st : RegaSt0) (free : List UInt32) (nxt : UInt32),
      (bindBlockParams0 pts venv st free nxt).venv = pushFreshVids0 pts.length st.nextVid venv
  | [], venv, _, _, _ => rfl
  | _ :: rest, venv, st, free, nxt => by
    dsimp only [bindBlockParams0, pushFreshVids0, List.length_cons, bindOneBlockSlot0]
    exact bindBlockParams0_venv rest (st.nextVid :: venv) _ _ _

/-- Syntactic count of operand uses of `vid` in one `Arg0`. -/
@[expose] def argUses0 (vid : UInt32) (venv : List UInt32) : Arg0 → Nat
  | .var idx => if listGetU32 venv idx = vid then 1 else 0
  | _ => 0

/-- Syntactic count of operand uses of `vid` in a `List Arg0`. -/
@[expose] def argsUses0 (vid : UInt32) (venv : List UInt32) : List Arg0 → Nat
  | [] => 0
  | a :: rest => argUses0 vid venv a + argsUses0 vid venv rest

/-- Syntactic count of operand uses of `vid` in the immediate node `n`. -/
@[expose] def nodeArgsUses0 (vid : UInt32) (venv : List UInt32) : TFlat0 → Nat
  | .let1 _ args _ => argsUses0 vid venv args
  | .let2Umulw64 a b _ => argUses0 vid venv a + argUses0 vid venv b
  | .load _ addr _ => argUses0 vid venv addr
  | .store _ val addr _ => argUses0 vid venv val + argUses0 vid venv addr
  | .call _ _ _ args _ => argsUses0 vid venv args
  | .tailCall _ _ args => argsUses0 vid venv args
  | .jump _ args => argsUses0 vid venv args
  | .ret args => argsUses0 vid venv args
  | .exit _ _ args => argsUses0 vid venv args
  | .jnz c _ _ => argUses0 vid venv c
  | .hlt | .group _ _ => 0

/-- Total same-scope linear spine operand uses of `vid` starting at `(node, venv, nextVid)`. -/
@[expose] def spineUses0 (vid : UInt32) (venv : List UInt32) (nextVid : UInt32) :
    TFlat0 → Nat
  | .let1 _ args k =>
    argsUses0 vid venv args + spineUses0 vid (pushFreshVids0 1 nextVid venv) (nextVid + 1) k
  | .let2Umulw64 a b k =>
    argUses0 vid venv a + argUses0 vid venv b +
      spineUses0 vid (pushFreshVids0 2 nextVid venv) (nextVid + 2) k
  | .load _ addr k =>
    argUses0 vid venv addr + spineUses0 vid (pushFreshVids0 1 nextVid venv) (nextVid + 1) k
  | .store _ val addr k =>
    argUses0 vid venv val + argUses0 vid venv addr + spineUses0 vid venv nextVid k
  | .call _ _ bs args k =>
    argsUses0 vid venv args +
      spineUses0 vid (pushFreshVids0 bs.length nextVid venv)
        (nextVid + UInt32.ofNat bs.length) k
  | node => nodeArgsUses0 vid venv node

theorem nodeArgsUses0_le_argCount0 (vid : UInt32) (venv : List UInt32) (n : TFlat0) :
    nodeArgsUses0 vid venv n ≤ argCount0 n := by
  have ha : ∀ a, argUses0 vid venv a ≤ 1 := fun a => by
    cases a with
    | var idx => dsimp only [argUses0]; split <;> omega
    | immBool _ | immBits _ _ => simp [argUses0]
  have has : ∀ args, argsUses0 vid venv args ≤ args.length := fun args => by
    induction args with
    | nil => exact Nat.le_refl 0
    | cons a rest ih => dsimp only [argsUses0, List.length_cons]; have := ha a; omega
  cases n with
  | let1 _ args k => have := has args; dsimp only [nodeArgsUses0, argCount0]; omega
  | let2Umulw64 a b k =>
    have := ha a; have := ha b; dsimp only [nodeArgsUses0, argCount0]; omega
  | load _ addr k => have := ha addr; dsimp only [nodeArgsUses0, argCount0]; omega
  | store _ v a k =>
    have := ha v; have := ha a; dsimp only [nodeArgsUses0, argCount0]; omega
  | call _ _ _ args k => have := has args; dsimp only [nodeArgsUses0, argCount0]; omega
  | tailCall _ _ args | jump _ args | ret args | exit _ _ args =>
    dsimp only [nodeArgsUses0, argCount0]; exact has args
  | jnz c _ _ => have := ha c; dsimp only [nodeArgsUses0, argCount0]; omega
  | hlt | group _ _ => exact Nat.zero_le _

private theorem argsUses0_le_length (vid : UInt32) (venv : List UInt32) :
    ∀ (args : List Arg0), argsUses0 vid venv args ≤ args.length
  | [] => Nat.le_refl 0
  | a :: rest => by
    have ha : argUses0 vid venv a ≤ 1 := by
      cases a <;> simp [argUses0] <;> try split <;> omega
    have hr := argsUses0_le_length vid venv rest
    dsimp only [argsUses0, List.length_cons]
    omega

theorem spineUses0_le_argCount0 :
    ∀ (vid : UInt32) (venv : List UInt32) (nextVid : UInt32) (n : TFlat0),
      spineUses0 vid venv nextVid n ≤ argCount0 n
  | vid, venv, nv, .let1 _ args k => by
    dsimp only [spineUses0, argCount0]
    have h1 := argsUses0_le_length vid venv args
    have h2 := spineUses0_le_argCount0 vid (pushFreshVids0 1 nv venv) (nv + 1) k
    omega
  | vid, venv, nv, .let2Umulw64 a b k => by
    dsimp only [spineUses0, argCount0]
    have ha : argUses0 vid venv a ≤ 1 := by
      cases a <;> simp [argUses0] <;> try split <;> omega
    have hb : argUses0 vid venv b ≤ 1 := by
      cases b <;> simp [argUses0] <;> try split <;> omega
    have h2 := spineUses0_le_argCount0 vid (pushFreshVids0 2 nv venv) (nv + 2) k
    omega
  | vid, venv, nv, .load _ addr k => by
    dsimp only [spineUses0, argCount0]
    have ha : argUses0 vid venv addr ≤ 1 := by
      cases addr <;> simp [argUses0] <;> try split <;> omega
    have h2 := spineUses0_le_argCount0 vid (pushFreshVids0 1 nv venv) (nv + 1) k
    omega
  | vid, venv, nv, .store _ v addr k => by
    dsimp only [spineUses0, argCount0]
    have hv : argUses0 vid venv v ≤ 1 := by
      cases v <;> simp [argUses0] <;> try split <;> omega
    have ha : argUses0 vid venv addr ≤ 1 := by
      cases addr <;> simp [argUses0] <;> try split <;> omega
    have h2 := spineUses0_le_argCount0 vid venv nv k
    omega
  | vid, venv, nv, .call _ _ bs args k => by
    dsimp only [spineUses0, argCount0]
    have h1 := argsUses0_le_length vid venv args
    have h2 := spineUses0_le_argCount0 vid (pushFreshVids0 bs.length nv venv)
      (nv + UInt32.ofNat bs.length) k
    omega
  | vid, venv, _, .tailCall fnSym as args => nodeArgsUses0_le_argCount0 vid venv _
  | vid, venv, _, .jump j args => nodeArgsUses0_le_argCount0 vid venv _
  | vid, venv, _, .ret args => nodeArgsUses0_le_argCount0 vid venv _
  | vid, venv, _, .exit fnSym as args => nodeArgsUses0_le_argCount0 vid venv _
  | vid, venv, _, .jnz c t e => nodeArgsUses0_le_argCount0 vid venv _
  | vid, venv, _, .hlt => Nat.zero_le _
  | vid, venv, _, .group _ _ => Nat.zero_le _

/-- True iff all `.var idx` operands directly referenced by `n` satisfy `idx.toNat < venvLen`. -/
@[expose] def nodeArgsInVenv0 (venvLen : Nat) : TFlat0 → Prop
  | .let1 _ args _ => ∀ a ∈ args, ∀ idx, a = .var idx → idx.toNat < venvLen
  | .let2Umulw64 a b _ =>
    (∀ idx, a = .var idx → idx.toNat < venvLen) ∧
    (∀ idx, b = .var idx → idx.toNat < venvLen)
  | .load _ addr _ => ∀ idx, addr = .var idx → idx.toNat < venvLen
  | .store _ val addr _ =>
    (∀ idx, val = .var idx → idx.toNat < venvLen) ∧
    (∀ idx, addr = .var idx → idx.toNat < venvLen)
  | .call _ _ _ args _ => ∀ a ∈ args, ∀ idx, a = .var idx → idx.toNat < venvLen
  | .tailCall _ _ args => ∀ a ∈ args, ∀ idx, a = .var idx → idx.toNat < venvLen
  | .jump _ args => ∀ a ∈ args, ∀ idx, a = .var idx → idx.toNat < venvLen
  | .ret args => ∀ a ∈ args, ∀ idx, a = .var idx → idx.toNat < venvLen
  | .exit _ _ args => ∀ a ∈ args, ∀ idx, a = .var idx → idx.toNat < venvLen
  | .jnz c _ _ => ∀ idx, c = .var idx → idx.toNat < venvLen
  | .hlt | .group _ _ => True

private theorem listGet?_some_lt {α : Type} :
    ∀ {xs : List α} {i : Nat} {x : α}, listGet? xs i = some x → i < xs.length
  | [], _, _, h => by dsimp only [listGet?] at h; cases h
  | _ :: _, 0, _, _ => Nat.zero_lt_succ _
  | _ :: rest, k + 1, x, h => Nat.succ_lt_succ (listGet?_some_lt (xs := rest) h)

private theorem checkArg0_lt {venvT : List Ty0} {t : Ty0} {a : Arg0}
    (h : checkArg0 venvT t a = true) : ∀ idx, a = .var idx → idx.toNat < venvT.length := by
  intro idx ha; subst ha
  exact listGet?_some_lt (checkArg0_spec h)

private theorem checkArgs0_lt {venvT : List Ty0} {ts : List Ty0} {args : List Arg0}
    (h : checkArgs0 venvT ts args = true) :
    ∀ a ∈ args, ∀ idx, a = .var idx → idx.toNat < venvT.length := by
  obtain ⟨hlen, hall⟩ := checkArgs0_spec h
  intro a ha idx he; subst he
  obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp ha
  exact checkArg0_lt (hall k (by omega) hk) idx hget

private theorem checkOp0_lt {venvT : List Ty0} {op : OpCode0} {args : List Arg0}
    (h : checkOp0 venvT op args = true) :
    ∀ a ∈ args, ∀ idx, a = .var idx → idx.toNat < venvT.length := by
  cases op with
  | un u t =>
    cases u <;> cases t <;> dsimp only [checkOp0, checkOpArith0] at h <;> try cases h
    all_goals
      rcases args with _ | ⟨a, _ | _⟩ <;> try contradiction
      intro x hx idx heq; simp only [List.mem_singleton] at hx; subst hx
      exact checkArg0_lt h idx heq
  | bin b t =>
    dsimp only [checkOp0, checkOpArith0, checkBinOp0] at h
    rcases args with _ | ⟨a, _ | ⟨bArg, _ | _⟩⟩ <;> try contradiction
    simp only [Bool.and_eq_true] at h
    intro x hx idx heq
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact checkArg0_lt h.1.2 idx heq
    · simp only [List.mem_singleton] at hx'; subst hx'
      exact checkArg0_lt h.2 idx heq
  | select t =>
    dsimp only [checkOp0, checkOpArith0] at h
    rcases args with _ | ⟨c, _ | ⟨a, _ | ⟨bArg, _ | _⟩⟩⟩ <;> try contradiction
    simp only [Bool.and_eq_true] at h
    intro x hx idx heq
    rcases List.mem_cons.mp hx with rfl | hx1
    · exact checkArg0_lt h.1.1 idx heq
    · rcases List.mem_cons.mp hx1 with rfl | hx2
      · exact checkArg0_lt h.1.2 idx heq
      · simp only [List.mem_singleton] at hx2; subst hx2
        exact checkArg0_lt h.2 idx heq
  | cmp _ t =>
    dsimp only [checkOp0] at h
    rcases args with _ | ⟨a, _ | ⟨bArg, _ | _⟩⟩ <;> try contradiction
    simp only [Bool.and_eq_true] at h
    intro x hx idx heq
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact checkArg0_lt h.1.2 idx heq
    · simp only [List.mem_singleton] at hx'; subst hx'
      exact checkArg0_lt h.2 idx heq
  | conv c m n =>
    dsimp only [checkOp0, checkConv0] at h
    rcases args with _ | ⟨a, _ | _⟩ <;> try contradiction
    simp only [Bool.and_eq_true] at h
    intro x hx idx heq; simp only [List.mem_singleton] at hx; subst hx
    exact checkArg0_lt h.2 idx heq
  | div _ w =>
    dsimp only [checkOp0] at h
    rcases args with _ | ⟨a, _ | ⟨bArg, _ | _⟩⟩ <;> try contradiction
    simp only [Bool.and_eq_true] at h
    intro x hx idx heq
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact checkArg0_lt h.1 idx heq
    · simp only [List.mem_singleton] at hx'; subst hx'
      exact checkArg0_lt h.2 idx heq
  | umulw64 => simp [checkOp0] at h

theorem wfNode0_nodeArgsInVenv0 {ctx : LegalCtx0} {venvT : List Ty0} {lenvT : List (List Ty0)}
    {n : TFlat0} (hwf : WfNode0 ctx venvT lenvT n) : nodeArgsInVenv0 venvT.length n := by
  cases hwf with
  | let1 hop _ => exact checkOp0_lt hop
  | let2Umulw64 ha hb _ => exact ⟨checkArg0_lt ha, checkArg0_lt hb⟩
  | load ha _ => exact checkArg0_lt ha
  | store hv ha _ => exact ⟨checkArg0_lt hv, checkArg0_lt ha⟩
  | call _ _ _ hargs _ => exact checkArgs0_lt hargs
  | tailCall _ _ hargs => exact checkArgs0_lt hargs
  | exit _ _ hargs => exact checkArgs0_lt hargs
  | jnz hc _ _ => exact checkArg0_lt hc
  | jump _ hargs => exact checkArgs0_lt hargs
  | ret hvs => exact checkArgs0_lt hvs
  | hlt | group _ _ => trivial

private theorem listGetD_mem {α : Type} :
    ∀ {xs : List α} {i : Nat} {d : α}, i < xs.length → xs.getD i d ∈ xs
  | [], _, _, hi => absurd hi (Nat.not_lt_zero _)
  | _ :: _, 0, _, _ => List.mem_cons_self
  | _ :: xs, _ + 1, _, hi =>
    List.mem_cons_of_mem _ (listGetD_mem (xs := xs) (Nat.lt_of_succ_lt_succ hi))

private theorem preNoteArg0_spec (scope : UInt32) (venv : List UInt32) (st : PreSt0) (a : Arg0)
    (_hs1 : st.defScope.size = st.nextVid.toNat) (hs2 : st.uses.size = st.nextVid.toNat)
    (hs3 : st.escaped.size = st.nextVid.toNat)
    (hvenv : ∀ v ∈ venv, v.toNat < st.nextVid.toNat)
    (ha : ∀ idx, a = .var idx → idx.toNat < venv.length)
    (hmax : ∀ v < st.nextVid.toNat, st.uses.getD v 0 + 1 < 2 ^ 32)
    (hds : ∀ v < st.nextVid.toNat, st.defScope.getD v 0 < 2 ^ 32)
    (hesc : ∀ v < st.nextVid.toNat, st.escaped.getD v 0 = 0 ∨ st.escaped.getD v 0 = 1) :
    let st1 := preNoteArg0 scope venv st a
    st1.nextVid = st.nextVid ∧ st1.defScope = st.defScope ∧
    st1.uses.size = st.nextVid.toNat ∧ st1.escaped.size = st.nextVid.toNat ∧
    (∀ v < st.nextVid.toNat, st1.escaped.getD v 0 = 0 ∨ st1.escaped.getD v 0 = 1) ∧
    (∀ v < st.nextVid.toNat,
      if st.defScope.getD v 0 = scope.toNat then
        st1.uses.getD v 0 = st.uses.getD v 0 + argUses0 (UInt32.ofNat v) venv a ∧
        st1.escaped.getD v 0 = st.escaped.getD v 0
      else
        st1.uses.getD v 0 = st.uses.getD v 0 ∧
        st1.escaped.getD v 0 =
          if 0 < argUses0 (UInt32.ofNat v) venv a then 1 else st.escaped.getD v 0) := by
  cases a with
  | immBool _ | immBits _ _ =>
    refine ⟨rfl, rfl, hs2, hs3, hesc, fun v _ => by split <;> exact ⟨rfl, rfl⟩⟩
  | var idx =>
    dsimp only [preNoteArg0]
    let vid := listGetU32 venv idx
    have hidx : idx.toNat < venv.length := ha idx rfl
    have hvid_mem : vid ∈ venv := by
      dsimp only [vid]; rw [listGetU32_eq_listGetD]; exact listGetD_mem hidx
    have hvid_lt : vid.toNat < st.nextVid.toNat := hvenv vid hvid_mem
    have hds_eq : (arrGetU0 st.defScope vid).toNat = st.defScope.getD vid.toNat 0 :=
      arrGetU0_of_lt st.defScope vid (hds vid.toNat hvid_lt)
    have heq_iff : (arrGetU0 st.defScope vid = scope) ↔
        st.defScope.getD vid.toNat 0 = scope.toNat := by
      constructor
      · intro h; rw [← hds_eq, h]
      · intro h; apply UInt32.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq
        simpa [hds_eq] using h
    by_cases heqs : arrGetU0 st.defScope vid = scope
    · simp only [vid] at heqs ⊢
      simp only [heqs, ↓reduceIte]
      have hu_lt : (arrGetU0 st.uses vid + 1).toNat = st.uses.getD vid.toNat 0 + 1 := by
        have h0 := arrGetU0_of_lt st.uses vid (Nat.lt_trans (Nat.lt_succ_self _)
          (hmax vid.toNat hvid_lt))
        rw [UInt32.toNat_add, UInt32.toNat_one, h0, Nat.mod_eq_of_lt (hmax vid.toNat hvid_lt)]
      refine ⟨trivial, trivial, by rw [arrSetU0_size, hs2], hs3, hesc, fun v hv => ?_⟩
      rw [arrSetU0_getD st.uses vid _ (hs2 ▸ hvid_lt) v]
      have hv_eq : (v = vid.toNat) ↔ (vid = UInt32.ofNat v) := by
        constructor
        · rintro rfl; exact UInt32.ofNat_toNat.symm
        · intro h; have := congrArg UInt32.toNat h; rw [UInt32.toNat_ofNat_of_lt'
            (Nat.lt_trans hv (UInt32.toNat_lt st.nextVid))] at this; exact this.symm
      split
      · by_cases hvv : v = vid.toNat
        · subst hvv
          have hvid_e : listGetU32 venv idx = UInt32.ofNat vid.toNat :=
            UInt32.ofNat_toNat.symm
          simp only [↓reduceIte, argUses0, hvid_e]
          exact ⟨by rw [← hvid_e]; exact hu_lt, trivial⟩
        · have hvid_ne : vid ≠ UInt32.ofNat v := fun h => hvv (hv_eq.mpr h)
          have hne_g : listGetU32 venv idx ≠ UInt32.ofNat v := hvid_ne
          simp only [hvv, ↓reduceIte, argUses0, hne_g, Nat.add_zero]
          exact ⟨trivial, trivial⟩
      · rename_i hvs
        have hvv : v ≠ vid.toNat := fun h => hvs (h ▸ heq_iff.mp heqs)
        have hvid_ne : vid ≠ UInt32.ofNat v := fun h => hvv (hv_eq.mpr h)
        have hne_g : listGetU32 venv idx ≠ UInt32.ofNat v := hvid_ne
        simp only [hvv, ↓reduceIte, argUses0, hne_g, Nat.lt_irrefl]
        exact ⟨trivial, trivial⟩
    · have hne_s : st.defScope.getD vid.toNat 0 ≠ scope.toNat := fun h => heqs (heq_iff.mpr h)
      simp only [vid] at heqs ⊢
      simp only [heqs, ↓reduceIte]
      refine ⟨trivial, trivial, hs2, by rw [arrSetU0_size, hs3], fun v hv => ?_, fun v hv => ?_⟩
      · rw [arrSetU0_getD st.escaped vid 1 (hs3 ▸ hvid_lt) v]
        split
        · exact Or.inr rfl
        · exact hesc v hv
      · rw [arrSetU0_getD st.escaped vid 1 (hs3 ▸ hvid_lt) v]
        have hv_eq : (v = vid.toNat) ↔ (vid = UInt32.ofNat v) := by
          constructor
          · rintro rfl; exact UInt32.ofNat_toNat.symm
          · intro h; have := congrArg UInt32.toNat h; rw [UInt32.toNat_ofNat_of_lt'
              (Nat.lt_trans hv (UInt32.toNat_lt st.nextVid))] at this; exact this.symm
        split
        · rename_i hvs
          have hvv : v ≠ vid.toNat := fun h => hne_s (h ▸ hvs)
          have hvid_ne : vid ≠ UInt32.ofNat v := fun h => hvv (hv_eq.mpr h)
          have hne_g : listGetU32 venv idx ≠ UInt32.ofNat v := hvid_ne
          simp only [hvv, ↓reduceIte, argUses0, hne_g, Nat.add_zero]
          exact ⟨trivial, trivial⟩
        · by_cases hvv : v = vid.toNat
          · subst hvv
            have hvid_e : listGetU32 venv idx = UInt32.ofNat vid.toNat :=
              UInt32.ofNat_toNat.symm
            simp only [↓reduceIte, argUses0, hvid_e, UInt32.toNat_one, Nat.zero_lt_one]
            exact ⟨trivial, trivial⟩
          · have hvid_ne : vid ≠ UInt32.ofNat v := fun h => hvv (hv_eq.mpr h)
            have hne_g : listGetU32 venv idx ≠ UInt32.ofNat v := hvid_ne
            simp only [hvv, ↓reduceIte, argUses0, hne_g, Nat.lt_irrefl]
            exact ⟨trivial, trivial⟩

private theorem preNoteArgs0_spec (scope : UInt32) (venv : List UInt32) :
    ∀ (args : List Arg0) (st : PreSt0),
      st.defScope.size = st.nextVid.toNat → st.uses.size = st.nextVid.toNat →
      st.escaped.size = st.nextVid.toNat →
      (∀ v ∈ venv, v.toNat < st.nextVid.toNat) →
      (∀ a ∈ args, ∀ idx, a = .var idx → idx.toNat < venv.length) →
      (∀ v < st.nextVid.toNat, st.uses.getD v 0 + args.length < 2 ^ 32) →
      (∀ v < st.nextVid.toNat, st.defScope.getD v 0 < 2 ^ 32) →
      (∀ v < st.nextVid.toNat, st.escaped.getD v 0 = 0 ∨ st.escaped.getD v 0 = 1) →
      let st1 := preNoteArgs0 scope venv st args
      st1.nextVid = st.nextVid ∧ st1.defScope = st.defScope ∧
      st1.uses.size = st.nextVid.toNat ∧ st1.escaped.size = st.nextVid.toNat ∧
      (∀ v < st.nextVid.toNat, st1.escaped.getD v 0 = 0 ∨ st1.escaped.getD v 0 = 1) ∧
      (∀ v < st.nextVid.toNat,
        if st.defScope.getD v 0 = scope.toNat then
          st1.uses.getD v 0 = st.uses.getD v 0 + argsUses0 (UInt32.ofNat v) venv args ∧
          st1.escaped.getD v 0 = st.escaped.getD v 0
        else
          st1.uses.getD v 0 = st.uses.getD v 0 ∧
          st1.escaped.getD v 0 =
            if 0 < argsUses0 (UInt32.ofNat v) venv args then 1 else st.escaped.getD v 0)
  | [], st, _, hs2, hs3, _, _, _, _, hesc =>
    ⟨rfl, rfl, hs2, hs3, hesc, fun v _ => by split <;> exact ⟨rfl, rfl⟩⟩
  | a :: rest, st, hs1, hs2, hs3, hvenv, ha, hmax, hds, hesc => by
    dsimp only [preNoteArgs0]
    have h1 := preNoteArg0_spec scope venv st a hs1 hs2 hs3 hvenv (ha a List.mem_cons_self)
      (fun v hv => by have := hmax v hv; simp only [List.length_cons] at this; omega) hds hesc
    dsimp only at h1
    let st1 := preNoteArg0 scope venv st a
    have hmax1 : ∀ v < st1.nextVid.toNat, st1.uses.getD v 0 + rest.length < 2 ^ 32 := by
      intro v hv; dsimp only [st1] at hv ⊢; rw [h1.1] at hv
      have hspec := h1.2.2.2.2.2 v hv
      have hau : argUses0 (UInt32.ofNat v) venv a ≤ 1 := by
        cases a with
        | var _ => dsimp only [argUses0]; split <;> omega
        | immBool _ | immBits _ _ => simp [argUses0]
      split at hspec
      · rw [hspec.1]; have := hmax v hv; simp only [List.length_cons] at this; omega
      · rw [hspec.1]; have := hmax v hv; simp only [List.length_cons] at this; omega
    have ih := preNoteArgs0_spec scope venv rest st1 (by dsimp only [st1]; rw [h1.1, h1.2.1, hs1])
      (by dsimp only [st1]; rw [h1.1, h1.2.2.1]) (by dsimp only [st1]; rw [h1.1, h1.2.2.2.1])
      (by dsimp only [st1]; rw [h1.1]; exact hvenv)
      (fun b hb => ha b (List.mem_cons_of_mem _ hb)) hmax1
      (by dsimp only [st1]; rw [h1.1, h1.2.1]; exact hds)
      (fun v hv => h1.2.2.2.2.1 v (h1.1 ▸ hv))
    refine ⟨ih.1.trans h1.1, ih.2.1.trans h1.2.1, by rw [h1.1] at ih; exact ih.2.2.1,
      by rw [h1.1] at ih; exact ih.2.2.2.1, by rw [h1.1] at ih; exact ih.2.2.2.2.1, fun v hv => ?_⟩
    have hi := ih.2.2.2.2.2 v (h1.1.symm ▸ hv)
    have h1v := h1.2.2.2.2.2 v hv
    rw [h1.2.1] at hi
    dsimp only [argsUses0]
    by_cases heqs : st.defScope.getD v 0 = scope.toNat
    · simp only [heqs, ↓reduceIte] at hi h1v ⊢
      refine ⟨?_, ?_⟩
      · rw [hi.1, h1v.1]; omega
      · rw [hi.2, h1v.2]
    · simp only [heqs, ↓reduceIte] at hi h1v ⊢
      refine ⟨hi.1.trans h1v.1, ?_⟩
      rw [hi.2, h1v.2]
      by_cases ha1 : 0 < argUses0 (UInt32.ofNat v) venv a <;>
        by_cases hr1 : 0 < argsUses0 (UInt32.ofNat v) venv rest
      · simp [hr1, show 0 < argUses0 (UInt32.ofNat v) venv a +
          argsUses0 (UInt32.ofNat v) venv rest by omega]
      · have hr0 : argsUses0 (UInt32.ofNat v) venv rest = 0 := by omega
        simp [ha1, hr0]
      · have ha0 : argUses0 (UInt32.ofNat v) venv a = 0 := by omega
        simp [hr1, ha0]
      · have ha0 : argUses0 (UInt32.ofNat v) venv a = 0 := by omega
        have hr0 : argsUses0 (UInt32.ofNat v) venv rest = 0 := by omega
        simp [ha0, hr0]

theorem preNoteNode0_spec (scope : UInt32) (venv : List UInt32) (node : TFlat0) (st : PreSt0)
    (hs1 : st.defScope.size = st.nextVid.toNat) (hs2 : st.uses.size = st.nextVid.toNat)
    (hs3 : st.escaped.size = st.nextVid.toNat)
    (hvenv : ∀ v ∈ venv, v.toNat < st.nextVid.toNat)
    (hargs : nodeArgsInVenv0 venv.length node)
    (hmax : ∀ v < st.nextVid.toNat, st.uses.getD v 0 + argCount0 node < 2 ^ 32)
    (hds : ∀ v < st.nextVid.toNat, st.defScope.getD v 0 < 2 ^ 32)
    (hesc : ∀ v < st.nextVid.toNat, st.escaped.getD v 0 = 0 ∨ st.escaped.getD v 0 = 1) :
    let st1 := preNoteNode0 scope venv node st
    st1.nextVid = st.nextVid ∧ st1.defScope = st.defScope ∧
    st1.uses.size = st.nextVid.toNat ∧ st1.escaped.size = st.nextVid.toNat ∧
    (∀ v < st.nextVid.toNat, st1.escaped.getD v 0 = 0 ∨ st1.escaped.getD v 0 = 1) ∧
    (∀ v < st.nextVid.toNat,
      if st.defScope.getD v 0 = scope.toNat then
        st1.uses.getD v 0 = st.uses.getD v 0 + nodeArgsUses0 (UInt32.ofNat v) venv node ∧
        st1.escaped.getD v 0 = st.escaped.getD v 0
      else
        st1.uses.getD v 0 = st.uses.getD v 0 ∧
        st1.escaped.getD v 0 =
          if 0 < nodeArgsUses0 (UInt32.ofNat v) venv node then 1 else st.escaped.getD v 0) := by
  have twoArgs : ∀ (a b : Arg0) (nRest : Nat),
      (∀ idx, a = .var idx → idx.toNat < venv.length) →
      (∀ idx, b = .var idx → idx.toNat < venv.length) →
      (∀ v < st.nextVid.toNat, st.uses.getD v 0 + (2 + nRest) < 2 ^ 32) →
      let st1 := preNoteArg0 scope venv (preNoteArg0 scope venv st a) b
      st1.nextVid = st.nextVid ∧ st1.defScope = st.defScope ∧
      st1.uses.size = st.nextVid.toNat ∧ st1.escaped.size = st.nextVid.toNat ∧
      (∀ v < st.nextVid.toNat, st1.escaped.getD v 0 = 0 ∨ st1.escaped.getD v 0 = 1) ∧
      (∀ v < st.nextVid.toNat,
        if st.defScope.getD v 0 = scope.toNat then
          st1.uses.getD v 0 = st.uses.getD v 0 +
            (argUses0 (UInt32.ofNat v) venv a + argUses0 (UInt32.ofNat v) venv b) ∧
          st1.escaped.getD v 0 = st.escaped.getD v 0
        else
          st1.uses.getD v 0 = st.uses.getD v 0 ∧
          st1.escaped.getD v 0 =
            if 0 < argUses0 (UInt32.ofNat v) venv a + argUses0 (UInt32.ofNat v) venv b then 1
            else st.escaped.getD v 0) := by
    intro a b nRest ha hb hm
    have h1 := preNoteArg0_spec scope venv st a hs1 hs2 hs3 hvenv ha
      (fun v hv => by have := hm v hv; omega) hds hesc
    dsimp only at h1
    let stA := preNoteArg0 scope venv st a
    have hmA : ∀ v < stA.nextVid.toNat, stA.uses.getD v 0 + 1 < 2 ^ 32 := by
      intro v hv; dsimp only [stA] at hv ⊢; rw [h1.1] at hv
      have hspec := h1.2.2.2.2.2 v hv
      have hau : argUses0 (UInt32.ofNat v) venv a ≤ 1 := by
        cases a with
        | var _ => dsimp only [argUses0]; split <;> omega
        | immBool _ | immBits _ _ => simp [argUses0]
      split at hspec <;> { rw [hspec.1]; have := hm v hv; omega }
    have h2 := preNoteArg0_spec scope venv stA b (by dsimp only [stA]; rw [h1.1, h1.2.1, hs1])
      (by dsimp only [stA]; rw [h1.1, h1.2.2.1]) (by dsimp only [stA]; rw [h1.1, h1.2.2.2.1])
      (by dsimp only [stA]; rw [h1.1]; exact hvenv)
      hb hmA (by dsimp only [stA]; rw [h1.1, h1.2.1]; exact hds)
      (fun v hv => h1.2.2.2.2.1 v (h1.1 ▸ hv))
    refine ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, by rw [h1.1] at h2; exact h2.2.2.1,
      by rw [h1.1] at h2; exact h2.2.2.2.1, by rw [h1.1] at h2; exact h2.2.2.2.2.1, fun v hv => ?_⟩
    have hi := h2.2.2.2.2.2 v (h1.1.symm ▸ hv)
    have h1v := h1.2.2.2.2.2 v hv
    rw [h1.2.1] at hi
    by_cases heqs : st.defScope.getD v 0 = scope.toNat
    · simp only [heqs, ↓reduceIte] at hi h1v ⊢
      refine ⟨by rw [hi.1, h1v.1]; omega, hi.2.trans h1v.2⟩
    · simp only [heqs, ↓reduceIte] at hi h1v ⊢
      refine ⟨hi.1.trans h1v.1, ?_⟩
      rw [hi.2, h1v.2]
      by_cases ha1 : 0 < argUses0 (UInt32.ofNat v) venv a <;>
        by_cases hb1 : 0 < argUses0 (UInt32.ofNat v) venv b
      · simp [hb1, show 0 < argUses0 (UInt32.ofNat v) venv a +
          argUses0 (UInt32.ofNat v) venv b by omega]
      · have hb0 : argUses0 (UInt32.ofNat v) venv b = 0 := by omega
        simp [ha1, hb0]
      · have ha0 : argUses0 (UInt32.ofNat v) venv a = 0 := by omega
        simp [hb1, ha0]
      · have ha0 : argUses0 (UInt32.ofNat v) venv a = 0 := by omega
        have hb0 : argUses0 (UInt32.ofNat v) venv b = 0 := by omega
        simp [ha0, hb0]
  cases node with
  | let1 _ args k =>
    exact preNoteArgs0_spec scope venv args st hs1 hs2 hs3 hvenv hargs
      (fun v hv => by have := hmax v hv; dsimp only [argCount0] at this; omega) hds hesc
  | let2Umulw64 a b k =>
    exact twoArgs a b (argCount0 k) hargs.1 hargs.2
      (fun v hv => by have := hmax v hv; dsimp only [argCount0] at this; omega)
  | load _ addr k =>
    exact preNoteArg0_spec scope venv st addr hs1 hs2 hs3 hvenv hargs
      (fun v hv => by have := hmax v hv; dsimp only [argCount0] at this; omega) hds hesc
  | store _ val addr k =>
    exact twoArgs val addr (argCount0 k) hargs.1 hargs.2
      (fun v hv => by have := hmax v hv; dsimp only [argCount0] at this; omega)
  | call _ _ _ args k =>
    exact preNoteArgs0_spec scope venv args st hs1 hs2 hs3 hvenv hargs
      (fun v hv => by have := hmax v hv; dsimp only [argCount0] at this; omega) hds hesc
  | tailCall _ _ args | jump _ args | ret args | exit _ _ args =>
    exact preNoteArgs0_spec scope venv args st hs1 hs2 hs3 hvenv hargs
      (fun v hv => by have := hmax v hv; dsimp only [argCount0] at this; exact this) hds hesc
  | jnz c t e =>
    exact preNoteArg0_spec scope venv st c hs1 hs2 hs3 hvenv hargs
      (fun v hv => by have := hmax v hv; dsimp only [argCount0] at this; omega) hds hesc
  | hlt | group _ _ =>
    refine ⟨rfl, rfl, hs2, hs3, hesc, fun v _ => by split <;> exact ⟨rfl, rfl⟩⟩

/-- Equivalence of `venv₁`/`venv₂` wrt whether each slot resolves to `vid`. -/
@[expose] def AgreeBelow0 (vid : UInt32) (venv₁ venv₂ : List UInt32) : Prop :=
  ∀ idx, listGetU32 venv₁ idx = vid ↔ listGetU32 venv₂ idx = vid

theorem agreeBelow0_refl (vid : UInt32) (venv : List UInt32) :
    AgreeBelow0 vid venv venv := fun _ => Iff.rfl

private theorem agreeBelow0_cons {vid x y : UInt32} {xs ys : List UInt32}
    (hx : vid ≠ x) (hy : vid ≠ y) (h : AgreeBelow0 vid xs ys) :
    AgreeBelow0 vid (x :: xs) (y :: ys) := by
  intro idx
  rw [listGetU32_eq_listGetD, listGetU32_eq_listGetD]
  cases hk : idx.toNat with
  | zero =>
    dsimp only [List.getD]
    exact ⟨fun e => absurd e.symm hx, fun e => absurd e.symm hy⟩
  | succ k =>
    have hlt_k : k < 2 ^ 32 := Nat.lt_trans (by omega) (UInt32.toNat_lt idx)
    have hk' := h (UInt32.ofNat k)
    rw [listGetU32_eq_listGetD, listGetU32_eq_listGetD, u32_toNat_ofNat,
      Nat.mod_eq_of_lt hlt_k] at hk'
    rw [List.getD_cons_succ, List.getD_cons_succ]
    exact hk'

theorem agreeBelow0_pushFreshVids0 :
    ∀ (k : Nat) (vid nv₁ nv₂ : UInt32) (venv₁ venv₂ : List UInt32),
      vid.toNat < nv₁.toNat → vid.toNat < nv₂.toNat →
      nv₁.toNat + k < 2 ^ 32 → nv₂.toNat + k < 2 ^ 32 →
      AgreeBelow0 vid venv₁ venv₂ →
      AgreeBelow0 vid (pushFreshVids0 k nv₁ venv₁) (pushFreshVids0 k nv₂ venv₂)
  | 0, _, _, _, _, _, _, _, _, _, h => h
  | m + 1, vid, nv₁, nv₂, v₁, v₂, h1, h2, hb1, hb2, h => by
    dsimp only [pushFreshVids0]
    have hne1 : vid ≠ nv₁ := fun e => by subst e; exact Nat.lt_irrefl _ h1
    have hne2 : vid ≠ nv₂ := fun e => by subst e; exact Nat.lt_irrefl _ h2
    have hnv1 : (nv₁ + 1).toNat = nv₁.toNat + 1 := u32_add1_toNat (by omega)
    have hnv2 : (nv₂ + 1).toNat = nv₂.toNat + 1 := u32_add1_toNat (by omega)
    exact agreeBelow0_pushFreshVids0 m vid (nv₁ + 1) (nv₂ + 1) (nv₁ :: v₁) (nv₂ :: v₂)
      (by omega) (by omega) (by omega) (by omega) (agreeBelow0_cons hne1 hne2 h)

private theorem nodeArgsUses0_congr {vid : UInt32} {v₁ v₂ : List UInt32}
    (h : AgreeBelow0 vid v₁ v₂) (n : TFlat0) :
    nodeArgsUses0 vid v₁ n = nodeArgsUses0 vid v₂ n := by
  have ha : ∀ a, argUses0 vid v₁ a = argUses0 vid v₂ a := fun a => by
    cases a with
    | var idx => simp only [argUses0, h idx]
    | immBool _ | immBits _ _ => rfl
  have has : ∀ args, argsUses0 vid v₁ args = argsUses0 vid v₂ args := fun args => by
    induction args with
    | nil => rfl
    | cons a rest ih => dsimp only [argsUses0]; rw [ha a, ih]
  cases n with
  | let1 _ args _ => exact has args
  | let2Umulw64 a b _ => dsimp only [nodeArgsUses0]; rw [ha a, ha b]
  | load _ addr _ => exact ha addr
  | store _ val addr _ => dsimp only [nodeArgsUses0]; rw [ha val, ha addr]
  | call _ _ _ args _ => exact has args
  | tailCall _ _ args | jump _ args | ret args | exit _ _ args => exact has args
  | jnz c _ _ => exact ha c
  | hlt | group _ _ => rfl

theorem spineUses0_congr :
    ∀ (n : TFlat0) (vid nv₁ nv₂ : UInt32) (v₁ v₂ : List UInt32),
      vid.toNat < nv₁.toNat → vid.toNat < nv₂.toNat →
      nv₁.toNat + binderCount0 n < 2 ^ 32 → nv₂.toNat + binderCount0 n < 2 ^ 32 →
      AgreeBelow0 vid v₁ v₂ →
      spineUses0 vid v₁ nv₁ n = spineUses0 vid v₂ nv₂ n
  | .let1 op args k, vid, nv₁, nv₂, v₁, v₂, h1, h2, hb1, hb2, hag => by
    dsimp only [binderCount0] at hb1 hb2
    dsimp only [spineUses0]
    have hu := nodeArgsUses0_congr hag (.let1 op args k)
    dsimp only [nodeArgsUses0] at hu
    have hag' := agreeBelow0_pushFreshVids0 1 vid nv₁ nv₂ v₁ v₂ h1 h2 (by omega) (by omega) hag
    have h1' : (nv₁ + 1).toNat = nv₁.toNat + 1 := u32_add1_toNat (by omega)
    have h2' : (nv₂ + 1).toNat = nv₂.toNat + 1 := u32_add1_toNat (by omega)
    have ihk := spineUses0_congr k vid (nv₁ + 1) (nv₂ + 1) _ _
      (by omega) (by omega) (by omega) (by omega) hag'
    rw [hu, ihk]
  | .let2Umulw64 a b k, vid, nv₁, nv₂, v₁, v₂, h1, h2, hb1, hb2, hag => by
    dsimp only [binderCount0] at hb1 hb2
    dsimp only [spineUses0]
    have hu := nodeArgsUses0_congr hag (.let2Umulw64 a b k)
    dsimp only [nodeArgsUses0] at hu
    have hag' := agreeBelow0_pushFreshVids0 2 vid nv₁ nv₂ v₁ v₂ h1 h2 (by omega) (by omega) hag
    have h2_1 : (nv₁ + 2).toNat = nv₁.toNat + 2 := by
      rw [UInt32.toNat_add, show (2 : UInt32).toNat = 2 by decide, Nat.mod_eq_of_lt (by omega)]
    have h2_2 : (nv₂ + 2).toNat = nv₂.toNat + 2 := by
      rw [UInt32.toNat_add, show (2 : UInt32).toNat = 2 by decide, Nat.mod_eq_of_lt (by omega)]
    have ihk := spineUses0_congr k vid (nv₁ + 2) (nv₂ + 2) _ _
      (by omega) (by omega) (by omega) (by omega) hag'
    rw [hu, ihk]
  | .load t addr k, vid, nv₁, nv₂, v₁, v₂, h1, h2, hb1, hb2, hag => by
    dsimp only [binderCount0] at hb1 hb2
    dsimp only [spineUses0]
    have hu := nodeArgsUses0_congr hag (.load t addr k)
    dsimp only [nodeArgsUses0] at hu
    have hag' := agreeBelow0_pushFreshVids0 1 vid nv₁ nv₂ v₁ v₂ h1 h2 (by omega) (by omega) hag
    have h1' : (nv₁ + 1).toNat = nv₁.toNat + 1 := u32_add1_toNat (by omega)
    have h2' : (nv₂ + 1).toNat = nv₂.toNat + 1 := u32_add1_toNat (by omega)
    have ihk := spineUses0_congr k vid (nv₁ + 1) (nv₂ + 1) _ _
      (by omega) (by omega) (by omega) (by omega) hag'
    rw [hu, ihk]
  | .store t val addr k, vid, nv₁, nv₂, v₁, v₂, h1, h2, hb1, hb2, hag => by
    dsimp only [binderCount0] at hb1 hb2
    dsimp only [spineUses0]
    have hu := nodeArgsUses0_congr hag (.store t val addr k)
    dsimp only [nodeArgsUses0] at hu
    rw [hu, spineUses0_congr k vid nv₁ nv₂ v₁ v₂ h1 h2 hb1 hb2 hag]
  | .call fnSym as bs args k, vid, nv₁, nv₂, v₁, v₂, h1, h2, hb1, hb2, hag => by
    dsimp only [binderCount0] at hb1 hb2
    dsimp only [spineUses0]
    have hu := nodeArgsUses0_congr hag (.call fnSym as bs args k)
    dsimp only [nodeArgsUses0] at hu
    have hag' := agreeBelow0_pushFreshVids0 bs.length vid nv₁ nv₂ v₁ v₂ h1 h2
      (by omega) (by omega) hag
    have hb1' : (nv₁ + UInt32.ofNat bs.length).toNat = nv₁.toNat + bs.length := by
      rw [UInt32.toNat_add, u32_toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
    have hb2' : (nv₂ + UInt32.ofNat bs.length).toNat = nv₂.toNat + bs.length := by
      rw [UInt32.toNat_add, u32_toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
    have ihk := spineUses0_congr k vid (nv₁ + UInt32.ofNat bs.length) (nv₂ + UInt32.ofNat bs.length)
      _ _ (by omega) (by omega) (by omega) (by omega) hag'
    rw [hu, ihk]
  | .tailCall _ _ _, vid, _, _, _, _, _, _, _, _, hag => nodeArgsUses0_congr hag _
  | .jump _ _, vid, _, _, _, _, _, _, _, _, hag => nodeArgsUses0_congr hag _
  | .ret _, vid, _, _, _, _, _, _, _, _, hag => nodeArgsUses0_congr hag _
  | .exit _ _ _, vid, _, _, _, _, _, _, _, _, hag => nodeArgsUses0_congr hag _
  | .jnz _ _ _, vid, _, _, _, _, _, _, _, _, hag => nodeArgsUses0_congr hag _
  | .hlt, vid, _, _, _, _, _, _, _, _, hag => nodeArgsUses0_congr hag _
  | .group _ _, vid, _, _, _, _, _, _, _, _, hag => nodeArgsUses0_congr hag _
termination_by n => sizeOf n

/-- Structural validity predicate for one `PreItem0` at state `nextVid`. -/
@[expose] def PreItemOk0 (ctx : LegalCtx0) (maxVid : Nat) (p : PreItem0) : Prop :=
  ∃ vT lT, p.venv.length = vT.length ∧ (∀ v ∈ p.venv, v.toNat < maxVid) ∧
    WfNode0 ctx vT lT p.node ∧ p.node.sigLensFitU32 = true ∧
    p.node.singleBlockGroups = true ∧ p.node.noNegBool = true

/-- Sum of `spineUses0` across items matching scope `ds`. -/
@[expose] def sameScopeSpineSum0 (vid : UInt32) (ds : Nat) (nextVid : UInt32) :
    List PreItem0 → Nat
  | [] => 0
  | p :: rest =>
    (if ds = p.scope.toNat then spineUses0 vid p.venv nextVid p.node else 0) +
      sameScopeSpineSum0 vid ds nextVid rest

/-- Full `PrePass0` worklist invariant ensuring no `UInt32` overflows and exact use accounting. -/
structure PreWorkInv0 (ctx : LegalCtx0) (nextSc : UInt32) (st : PreSt0)
    (work : List PreItem0) : Prop where
  defScope_sz : st.defScope.size = st.nextVid.toNat
  uses_sz : st.uses.size = st.nextVid.toNat
  escaped_sz : st.escaped.size = st.nextVid.toNat
  defScope_lt : ∀ v < st.nextVid.toNat, st.defScope.getD v 0 < nextSc.toNat
  escaped_bit : ∀ v < st.nextVid.toNat, st.escaped.getD v 0 = 0 ∨ st.escaped.getD v 0 = 1
  scopes_nodup : (work.map PreItem0.scope).Nodup
  scopes_lt : ∀ p ∈ work, p.scope.toNat < nextSc.toNat
  items_ok : ∀ p ∈ work, PreItemOk0 ctx st.nextVid.toNat p
  nextVid_bound : st.nextVid.toNat + workBinderCount0 (work.map PreItem0.node) < 2 ^ 31
  nextSc_bound : nextSc.toNat + 2 * workNodeCount0 (work.map PreItem0.node) < 2 ^ 31
  argCount_bound : workArgCount0 (work.map PreItem0.node) < 2 ^ 31
  uses_bound : ∀ v < st.nextVid.toNat,
    st.uses.getD v 0 + workArgCount0 (work.map PreItem0.node) < 2 ^ 31

theorem sameScopeSpineSum0_eq_zero {vid : UInt32} {ds : Nat} {nxt : UInt32} :
    ∀ {work : List PreItem0},
      (∀ p ∈ work, p.scope.toNat ≠ ds) → sameScopeSpineSum0 vid ds nxt work = 0
  | [], _ => rfl
  | p :: rest, h => by
    have hp : ds ≠ p.scope.toNat := (h p List.mem_cons_self).symm
    have hr := sameScopeSpineSum0_eq_zero (vid := vid) (ds := ds) (nxt := nxt)
      (fun q hq => h q (List.mem_cons_of_mem _ hq))
    dsimp only [sameScopeSpineSum0]
    simp only [hp, ↓reduceIte, hr]

theorem sameScopeSpineSum0_congr_nv {vid : UInt32} {ds : Nat} {nv₁ nv₂ : UInt32} :
    ∀ {work : List PreItem0},
      vid.toNat < nv₁.toNat → nv₁.toNat ≤ nv₂.toNat →
      nv₂.toNat + workBinderCount0 (work.map PreItem0.node) < 2 ^ 32 →
      sameScopeSpineSum0 vid ds nv₂ work = sameScopeSpineSum0 vid ds nv₁ work
  | [], _, _, _ => rfl
  | p :: rest, h1, hle, hb => by
    rw [List.map_cons] at hb; dsimp only [workBinderCount0] at hb
    dsimp only [sameScopeSpineSum0]
    have hr := sameScopeSpineSum0_congr_nv (ds := ds) (work := rest) h1 hle (by omega)
    rw [hr]
    split
    · have hs := spineUses0_congr p.node vid nv₂ nv₁ p.venv p.venv (by omega) h1
        (by omega) (by omega) (agreeBelow0_refl vid p.venv)
      rw [hs]
    · rfl

theorem wfNode0_group_single_inv {ctx : LegalCtx0} {vT : List Ty0}
    {lT : List (List Ty0)} {bodies : List (List Ty0 × TFlat0)} {k : TFlat0}
    (hwf : WfNode0 ctx vT lT (.group bodies k))
    (hfit : (TFlat0.group bodies k).sigLensFitU32 = true)
    (hsbg : (TFlat0.group bodies k).singleBlockGroups = true)
    (hnb : (TFlat0.group bodies k).noNegBool = true) :
    WfNode0 ctx vT (legalAddSigs0 bodies lT) k ∧
    k.sigLensFitU32 = true ∧ k.singleBlockGroups = true ∧ k.noNegBool = true ∧
    (bodies = [] ∨ ∃ pts b, bodies = [(pts, b)] ∧
      pts.length < 2 ^ 32 ∧
      WfNode0 ctx (pushTys0 pts vT) (legalAddSigs0 bodies lT) b ∧
      b.sigLensFitU32 = true ∧ b.singleBlockGroups = true ∧ b.noNegBool = true) := by
  cases hwf with
  | group hbs hk =>
    dsimp only [TFlat0.sigLensFitU32] at hfit; rw [Bool.and_eq_true] at hfit
    dsimp only [TFlat0.singleBlockGroups] at hsbg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hsbg
    dsimp only [TFlat0.noNegBool] at hnb; rw [Bool.and_eq_true] at hnb
    refine ⟨hk, hfit.2, hsbg.2, hnb.2, ?_⟩
    cases bodies with
    | nil => exact Or.inl rfl
    | cons p rest =>
      rcases p with ⟨pts, b⟩
      cases rest with
      | nil =>
        have hbf := hfit.1
        have hbsg := hsbg.1.2
        have hbnb := hnb.1
        dsimp only [blocksSigLensFitU32, listLenFitsU32] at hbf
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hbf
        dsimp only [blocksSingleBlockGroups] at hbsg; rw [Bool.and_eq_true] at hbsg
        dsimp only [blocksNoNegBool] at hbnb; rw [Bool.and_eq_true] at hbnb
        exact Or.inr ⟨pts, b, rfl, hbf.1.1, hbs (pts, b) List.mem_cons_self,
          hbf.1.2, hbsg.1, hbnb.1⟩
      | cons _ _ =>
        simp only [List.length_cons] at hsbg; omega

private theorem let1_noNegBool {op : OpCode0} {args : List Arg0} {k : TFlat0}
    (h : (TFlat0.let1 op args k).noNegBool = true) : k.noNegBool = true := by
  cases op with
  | un u t =>
    cases u <;> cases t <;>
      (dsimp only [TFlat0.noNegBool] at h; first | exact h | cases h)
  | _ => dsimp only [TFlat0.noNegBool] at h; exact h

theorem pushTypes_length : ∀ (ts acc : List Ty0),
    (pushTypes ts acc).length = acc.length + ts.length
  | [], acc => rfl
  | t :: rest, acc => by
    dsimp only [pushTypes]
    rw [pushTypes_length rest (t :: acc), List.length_cons, List.length_cons]
    omega

theorem wfNode0_lin_inv {ctx : LegalCtx0} {vT : List Ty0} {lT : List (List Ty0)}
    {node : TFlat0} (hwf : WfNode0 ctx vT lT node)
    (hfit : node.sigLensFitU32 = true) (hsbg : node.singleBlockGroups = true)
    (hnb : node.noNegBool = true) (hlin : isTerm0 node = false)
    (hnj : ∀ c t e, node ≠ .jnz c t e) (hng : ∀ bodies k, node ≠ .group bodies k) :
    (linCnt0 node).toNat < 2 ^ 32 ∧
    (legalNextVenv0 node vT).length = vT.length + (linCnt0 node).toNat ∧
    WfNode0 ctx (legalNextVenv0 node vT) lT (linK0 node) ∧
    (linK0 node).sigLensFitU32 = true ∧
    (linK0 node).singleBlockGroups = true ∧
    (linK0 node).noNegBool = true ∧
    binderCount0 (linK0 node) + (linCnt0 node).toNat = binderCount0 node ∧
    argCount0 (linK0 node) ≤ argCount0 node ∧
    nodeCount0 (linK0 node) + 1 = nodeCount0 node ∧
    maxJumpArity0 (linK0 node) = maxJumpArity0 node := by
  cases node with
  | let1 op args k =>
    cases hwf with
    | let1 _ hk =>
      dsimp only [TFlat0.sigLensFitU32] at hfit
      dsimp only [TFlat0.singleBlockGroups] at hsbg
      refine ⟨by simp [linCnt0], by simp [legalNextVenv0, linCnt0], hk, hfit, hsbg,
        let1_noNegBool hnb,
        by dsimp only [linK0, linCnt0, binderCount0]; simp only [UInt32.toNat_one]; omega,
        by dsimp only [linK0, argCount0]; omega,
        by dsimp only [linK0, nodeCount0]; omega, rfl⟩
  | let2Umulw64 a b k =>
    cases hwf with
    | let2Umulw64 _ _ hk =>
      dsimp only [TFlat0.sigLensFitU32] at hfit
      dsimp only [TFlat0.singleBlockGroups] at hsbg
      dsimp only [TFlat0.noNegBool] at hnb
      refine ⟨by simp [linCnt0], by simp [legalNextVenv0, linCnt0], hk, hfit, hsbg, hnb,
        by dsimp only [linK0, linCnt0, binderCount0]
           rw [show (2 : UInt32).toNat = 2 from rfl]; omega,
        by dsimp only [linK0, argCount0]; omega,
        by dsimp only [linK0, nodeCount0]; omega, rfl⟩
  | load t addr k =>
    cases hwf with
    | load _ hk =>
      dsimp only [TFlat0.sigLensFitU32] at hfit
      dsimp only [TFlat0.singleBlockGroups] at hsbg
      dsimp only [TFlat0.noNegBool] at hnb
      refine ⟨by simp [linCnt0], by simp [legalNextVenv0, linCnt0], hk, hfit, hsbg, hnb,
        by dsimp only [linK0, linCnt0, binderCount0]; simp only [UInt32.toNat_one]; omega,
        by dsimp only [linK0, argCount0]; omega,
        by dsimp only [linK0, nodeCount0]; omega, rfl⟩
  | store t val addr k =>
    cases hwf with
    | store _ _ hk =>
      dsimp only [TFlat0.sigLensFitU32] at hfit
      dsimp only [TFlat0.singleBlockGroups] at hsbg
      dsimp only [TFlat0.noNegBool] at hnb
      refine ⟨by simp [linCnt0], by simp [legalNextVenv0, linCnt0], hk, hfit, hsbg, hnb,
        by dsimp only [linK0, linCnt0, binderCount0]; rw [UInt32.toNat_zero, Nat.add_zero],
        by dsimp only [linK0, argCount0]; omega,
        by dsimp only [linK0, nodeCount0]; omega, rfl⟩
  | call fnSym as bs args k =>
    cases hwf with
    | call _ _ _ _ hk =>
      dsimp only [TFlat0.sigLensFitU32, listLenFitsU32] at hfit
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hfit
      dsimp only [TFlat0.singleBlockGroups] at hsbg
      dsimp only [TFlat0.noNegBool] at hnb
      have hcnt : (tyLenU0 bs 0).toNat = bs.length := tyLenU0_eq_of_lt hfit.1.2
      have hvlen : (legalNextVenv0 (.call fnSym as bs args k) vT).length =
          vT.length + bs.length := by
        dsimp only [legalNextVenv0]
        rw [pushTys0_eq_pushTypes, pushTypes_length]
      refine ⟨by simpa only [linCnt0, hcnt] using hfit.1.2, ?_, hk, hfit.2, hsbg, hnb, ?_, ?_, ?_,
        rfl⟩
      · simpa only [linCnt0, hcnt] using hvlen
      · dsimp only [linK0, linCnt0, binderCount0]; rw [hcnt]; omega
      · dsimp only [linK0, argCount0]; omega
      · dsimp only [linK0, nodeCount0]; omega
  | jnz _ _ _ => exact absurd rfl (hnj _ _ _)
  | group _ _ => exact absurd rfl (hng _ _)
  | tailCall _ _ _ | jump _ _ | ret _ | exit _ _ _ | hlt => simp [isTerm0] at hlin

theorem nodeArgsUses0_add_linK0_le (vid : UInt32) (venv : List UInt32)
    {n : TFlat0} (hlin : isTerm0 n = false)
    (hnj : ∀ c t e, n ≠ .jnz c t e) (hng : ∀ bs k, n ≠ .group bs k) :
    nodeArgsUses0 vid venv n + argCount0 (linK0 n) ≤ argCount0 n := by
  have hau : ∀ a, argUses0 vid venv a ≤ 1 := fun a => by
    cases a with
    | var _ => dsimp only [argUses0]; split <;> omega
    | immBool _ | immBits _ _ => simp [argUses0]
  have has : ∀ args, argsUses0 vid venv args ≤ args.length := fun xs => by
    induction xs with
    | nil => exact Nat.le_refl 0
    | cons a rs ihs => dsimp only [argsUses0, List.length_cons]; have := hau a; omega
  cases n with
  | let1 _ args k => have := has args; dsimp only [nodeArgsUses0, linK0, argCount0]; omega
  | let2Umulw64 a b k =>
    have := hau a; have := hau b; dsimp only [nodeArgsUses0, linK0, argCount0]; omega
  | load _ addr k => have := hau addr; dsimp only [nodeArgsUses0, linK0, argCount0]; omega
  | store _ v a k =>
    have := hau v; have := hau a; dsimp only [nodeArgsUses0, linK0, argCount0]; omega
  | call _ _ _ args k => have := has args; dsimp only [nodeArgsUses0, linK0, argCount0]; omega
  | jnz _ _ _ => exact absurd rfl (hnj _ _ _)
  | group _ _ => exact absurd rfl (hng _ _)
  | tailCall _ _ _ | jump _ _ | ret _ | exit _ _ _ | hlt => simp [isTerm0] at hlin

theorem spineUses0_lin (vid : UInt32) (venv : List UInt32) (nv : UInt32)
    {n : TFlat0} (hlin : isTerm0 n = false)
    (hnj : ∀ c t e, n ≠ .jnz c t e) (hng : ∀ bs k, n ≠ .group bs k)
    (hfit : n.sigLensFitU32 = true) :
    spineUses0 vid venv nv n =
      nodeArgsUses0 vid venv n +
        spineUses0 vid (pushFreshVids0 (linCnt0 n).toNat nv venv)
          (nv + UInt32.ofNat (linCnt0 n).toNat) (linK0 n) := by
  cases n with
  | let1 _ _ _ => rfl
  | let2Umulw64 _ _ _ => rfl
  | load _ _ _ => rfl
  | store _ _ _ _ =>
    dsimp only [spineUses0, linCnt0, linK0, nodeArgsUses0, pushFreshVids0]
    rw [UInt32.toNat_zero, u32_add_zero]
    rfl
  | call _ _ bs _ _ =>
    dsimp only [TFlat0.sigLensFitU32, listLenFitsU32] at hfit
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hfit
    dsimp only [spineUses0, linCnt0, linK0, nodeArgsUses0]
    rw [tyLenU0_eq_of_lt hfit.1.2]
  | jnz _ _ _ => exact absurd rfl (hnj _ _ _)
  | group _ _ => exact absurd rfl (hng _ _)
  | tailCall _ _ _ | jump _ _ | ret _ | exit _ _ _ | hlt => simp [isTerm0] at hlin

end LeanQbe.T.Bootstrap0
