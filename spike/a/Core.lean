module

/-
Spike A (core): single-sorted PHOAS SSA IR in which every binder is a plain λ and every
finite family is constructor data, so that

    @prog = fun V L args => denote V L flat (ctx built from args) Ctx.empty

can hold by `rfl`.  Contents: IR, wp, wp_mono, Flat, denote, toFlat, small elaborators.
-/
public meta import Lean
set_option autoImplicit false

@[expose] public section

namespace A

abbrev Val := BitVec 64
abbrev Mem := BitVec 64 → Option (BitVec 64)

inductive BinOp | add | sub | and
  deriving Repr, DecidableEq

def BinOp.eval : BinOp → Val → Val → Val
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .and, a, b => a &&& b

inductive Op (V : Type) : Type
  | const (c : Val) : Op V
  | bin (o : BinOp) (a b : V) : Op V
  | ult (a b : V) : Op V
  | udiv (a b : V) : Op V
  | load (a : V) : Op V
  | store (a v : V) : Op V
  deriving Repr

/-! ## 1. IR encoding -/

/-- Label tuple of a group with signature `sig` (the list of block arities): nested products. -/
@[reducible] def Labels (L : Nat → Type) : List Nat → Type
  | [] => Unit
  | n :: sig => L n × Labels L sig

/-- Jump arguments: nested products, no embedded proofs. -/
@[reducible] def Args (V : Type) : Nat → Type
  | 0 => Unit
  | n + 1 => V × Args V n

mutual
inductive Expr (V : Type) (L : Nat → Type) : Type
  | ret (v : V) : Expr V L
  | let_ (op : Op V) (k : V → Expr V L) : Expr V L
  | ite (c : V) (t e : Expr V L) : Expr V L
  | jump {n : Nat} (j : L n) (args : Args V n) : Expr V L
  | unreachable : Expr V L
  /-- A group of mutually recursive join points.  `bodies` and `k` are ordinary Lean
  functions of the label tuple, so they may mention anything bound outside. -/
  | letRecs (sig : List Nat) (bodies : Labels L sig → Blocks V L sig)
      (k : Labels L sig → Expr V L) : Expr V L
/-- `n` curried parameter binders, then a body. -/
inductive Block (V : Type) (L : Nat → Type) : Nat → Type
  | body (e : Expr V L) : Block V L 0
  | param {n : Nat} (f : V → Block V L n) : Block V L (n + 1)
/-- One block per entry of the signature. -/
inductive Blocks (V : Type) (L : Nat → Type) : List Nat → Type
  | nil : Blocks V L []
  | cons {n : Nat} {sig : List Nat} (b : Block V L n) (bs : Blocks V L sig) :
      Blocks V L (n :: sig)
end

/-! ## 2. Semantics -/

def Op.wp : Op Val → Mem → (Val → Mem → Prop) → Prop
  | .const c, m, post => post c m
  | .bin o a b, m, post => post (o.eval a b) m
  | .ult a b, m, post => post (if a < b then 1 else 0) m
  | .udiv a b, m, post => b ≠ 0 ∧ post (a / b) m
  | .load a, m, post => ∃ v, m a = some v ∧ post v m
  | .store a v, m, post => (m a).isSome ∧ post 0 (fun a' => if a' = a then some v else m a')

abbrev Cont (n : Nat) : Type := Args Val n → Mem → Prop
abbrev Post := Val → Mem → Prop

mutual
def wp (Q : Post) : Expr Val Cont → Mem → Prop
  | .ret v, m => Q v m
  | .let_ op k, m => op.wp m (fun v m' => wp Q (k v) m')
  | .ite c t e, m => (c ≠ 0 → wp Q t m) ∧ (c = 0 → wp Q e m)
  | .jump j args, m => j args m
  | .unreachable, _ => False
  | .letRecs sig bodies k, m =>
      ∀ J : Labels Cont sig, closedBlocks Q (bodies J) J → wp Q (k J) m
/-- `J` is closed under the block: whenever the body's wp holds, so does `J`. -/
def closedBlock (Q : Post) : {n : Nat} → Block Val Cont n → Cont n → Prop
  | _, .body e, J => ∀ m, wp Q e m → J () m
  | _, .param f, J => ∀ v, closedBlock Q (f v) (fun args m => J (v, args) m)
def closedBlocks (Q : Post) : {sig : List Nat} → Blocks Val Cont sig → Labels Cont sig → Prop
  | _, .nil, _ => True
  | _, .cons b bs, J => closedBlock Q b J.1 ∧ closedBlocks Q bs J.2
end

theorem Op.wp_mono {op : Op Val} {m : Mem} {p q : Val → Mem → Prop}
    (h : ∀ v m, p v m → q v m) : op.wp m p → op.wp m q := by
  cases op with
  | const c => exact h _ _
  | bin o a b => exact h _ _
  | ult a b => exact h _ _
  | udiv a b => exact fun ⟨h1, h2⟩ => ⟨h1, h _ _ h2⟩
  | load a => exact fun ⟨v, h1, h2⟩ => ⟨v, h1, h _ _ h2⟩
  | store a v => exact fun ⟨h1, h2⟩ => ⟨h1, h _ _ h2⟩

mutual
/-- Consequence rule for every term, exotic or not, by structural recursion. -/
theorem wp_mono {Q Q' : Post} (hQ : ∀ v m, Q v m → Q' v m) :
    ∀ (e : Expr Val Cont) (m : Mem), wp Q e m → wp Q' e m
  | .ret _, _, h => hQ _ _ h
  | .let_ _ k, _, h => Op.wp_mono (fun v m' => wp_mono hQ (k v) m') h
  | .ite _ t e, m, h => ⟨fun hc => wp_mono hQ t m (h.1 hc), fun hc => wp_mono hQ e m (h.2 hc)⟩
  | .jump _ _, _, h => h
  | .unreachable, _, h => h
  | .letRecs _ bodies k, m, h => fun J hJ =>
      wp_mono hQ (k J) m (h J (closedBlocks_anti hQ (bodies J) J hJ))
theorem closedBlock_anti {Q Q' : Post} (hQ : ∀ v m, Q v m → Q' v m) :
    ∀ {n : Nat} (b : Block Val Cont n) (J : Cont n), closedBlock Q' b J → closedBlock Q b J
  | _, .body e, _, h => fun m hm => h m (wp_mono hQ e m hm)
  | _, .param f, _, h => fun v => closedBlock_anti hQ (f v) _ (h v)
theorem closedBlocks_anti {Q Q' : Post} (hQ : ∀ v m, Q v m → Q' v m) :
    ∀ {sig : List Nat} (bs : Blocks Val Cont sig) (J : Labels Cont sig),
      closedBlocks Q' bs J → closedBlocks Q bs J
  | _, .nil, _, _ => trivial
  | _, .cons b bs, J, h => ⟨closedBlock_anti hQ b J.1 h.1, closedBlocks_anti hQ bs J.2 h.2⟩
end

/-! ## 3. First-order side -/

-- Variables and labels are de Bruijn *levels* (Nat literals). Binders are implicit.
mutual
inductive Flat : Type
  | ret (v : Nat)
  | let_ (op : Op Nat) (k : Flat)
  | ite (c : Nat) (t e : Flat)
  | jump (j : Nat) (args : List Nat)
  | unreachable
  | letRecs (sig : List Nat) (bodies : FBlocks) (k : Flat)
  deriving Repr
inductive FBlocks : Type
  | nil
  | cons (b : Flat) (bs : FBlocks)
  deriving Repr
end

/-- Braun-style trie indexed by level; `setK` is only ever called at index = size. -/
inductive Trie (α : Type) : Type
  | leaf : Trie α
  | node (l : Trie α) (v : α) (r : Trie α) : Trie α

def Trie.get {α : Type} : Trie α → Nat → Option α
  | .leaf, _ => none
  | .node l v r, i =>
    match i with
    | 0 => some v
    | i + 1 => cond (Nat.beq (Nat.mod i 2) 0) (l.get (Nat.div i 2)) (r.get (Nat.div i 2))

/-- `setK t i a k`: store `a` at level `i` and pass the new trie to `k`.
Continuation-passing style on purpose: under call-by-name reduction (kernel `whnf`,
`Meta.whnf`) the trie handed to `k` is already built from constructors, so contexts never
accumulate suspended updates.  Only ever called with `i` = current size. -/
def Trie.setK {α : Type} {β : Sort _} : Trie α → Nat → α → (Trie α → β) → β
  | .leaf, _, a, k => k (.node .leaf a .leaf)
  | .node l v r, i, a, k =>
    match i with
    | 0 => k (.node l a r)
    | i + 1 =>
      cond (Nat.beq (Nat.mod i 2) 0)
        (l.setK (Nat.div i 2) a fun l' => k (.node l' v r))
        (r.setK (Nat.div i 2) a fun r' => k (.node l v r'))

/-- `pushListK t i as k`: store `as` at levels `i, i+1, …`, then continue with `k`. -/
def Trie.pushListK {α : Type} {β : Sort _} : List α → Trie α → Nat → (Trie α → β) → β
  | [], t, _, k => k t
  | a :: as, t, i, k => t.setK i a fun t' => Trie.pushListK as t' (Nat.succ i) k

/-- A label together with its arity. -/
abbrev LEntry (L : Nat → Type) : Type := (n : Nat) × L n

/-
IMPORTANT: the sizes `nv`/`nl` (next fresh level) are passed as separate arguments and never
stored in a structure next to PHOAS variables.  Nat literal folding (kernel GMP acceleration
and `Meta.reduceNat?`) is skipped for terms containing free variables, so every Nat that is
computed with must stay a syntactically closed term.
-/

def denoteOp {V : Type} (vt : Trie V) : Op Nat → Option (Op V)
  | .const c => some (.const c)
  | .bin o a b =>
    match vt.get a, vt.get b with
    | some a, some b => some (.bin o a b)
    | _, _ => none
  | .ult a b =>
    match vt.get a, vt.get b with
    | some a, some b => some (.ult a b)
    | _, _ => none
  | .udiv a b =>
    match vt.get a, vt.get b with
    | some a, some b => some (.udiv a b)
    | _, _ => none
  | .load a =>
    match vt.get a with
    | some a => some (.load a)
    | none => none
  | .store a v =>
    match vt.get a, vt.get v with
    | some a, some v => some (.store a v)
    | _, _ => none

def mkArgs {V : Type} (vt : Trie V) : (n : Nat) → List Nat → Option (Args V n)
  | 0, [] => some ()
  | n + 1, a :: as =>
    match vt.get a, mkArgs vt n as with
    | some v, some r => some (v, r)
    | _, _ => none
  | _, _ => none

/-- Store the labels of a group at levels `nl, nl+1, …`, then continue with `k`. -/
def extendLK {L : Nat → Type} {β : Sort _} :
    (sig : List Nat) → Labels L sig → Nat → Trie (LEntry L) → (Trie (LEntry L) → β) → β
  | [], _, _, lt, k => k lt
  | n :: sig, ls, nl, lt, k =>
    lt.setK nl ⟨n, ls.1⟩ fun lt' => extendLK sig ls.2 (Nat.succ nl) lt' k

/-- `n` parameter binders (levels `nv, nv+1, …`), then the body. -/
def mkBlock {V : Type} {L : Nat → Type} :
    (n : Nat) → (Nat → Trie V → Expr V L) → Nat → Trie V → Block V L n
  | 0, f, nv, vt => .body (f nv vt)
  | n + 1, f, nv, vt => .param fun v => vt.setK nv v fun vt' => mkBlock n f (Nat.succ nv) vt'

def Blocks.dummy {V : Type} {L : Nat → Type} : (sig : List Nat) → Blocks V L sig
  | [] => .nil
  | n :: sig => .cons (mkBlock n (fun _ _ => .unreachable) 0 .leaf) (Blocks.dummy sig)

mutual
/-- Interpret first-order syntax back into PHOAS, for arbitrary `V` and `L`.
`denote V L flat nv vt nl lt`: `vt`/`lt` map levels `< nv`/`< nl` to variables/labels.
An ill-scoped name or an arity mismatch denotes `unreachable`. -/
def denote (V : Type) (L : Nat → Type) :
    Flat → Nat → Trie V → Nat → Trie (LEntry L) → Expr V L
  | .ret v, _, vt, _, _ =>
    match vt.get v with
    | some v => .ret v
    | none => .unreachable
  | .let_ op k, nv, vt, nl, lt =>
    match denoteOp vt op with
    | some op => .let_ op fun v => vt.setK nv v fun vt' => denote V L k (Nat.succ nv) vt' nl lt
    | none => .unreachable
  | .ite c t e, nv, vt, nl, lt =>
    match vt.get c with
    | some c => .ite c (denote V L t nv vt nl lt) (denote V L e nv vt nl lt)
    | none => .unreachable
  | .jump j args, _, vt, _, lt =>
    match lt.get j with
    | some ⟨n, l⟩ =>
      match mkArgs vt n args with
      | some as => .jump l as
      | none => .unreachable
    | none => .unreachable
  | .unreachable, _, _, _, _ => .unreachable
  | .letRecs sig bodies k, nv, vt, nl, lt =>
    .letRecs sig
      (fun ls => extendLK sig ls nl lt fun lt' =>
        denoteBlocks V L bodies sig nv vt (Nat.add nl sig.length) lt')
      (fun ls => extendLK sig ls nl lt fun lt' =>
        denote V L k nv vt (Nat.add nl sig.length) lt')
def denoteBlocks (V : Type) (L : Nat → Type) :
    FBlocks → (sig : List Nat) → Nat → Trie V → Nat → Trie (LEntry L) → Blocks V L sig
  | .nil, sig, _, _, _, _ => Blocks.dummy sig
  | .cons b bs, sig, nv, vt, nl, lt =>
    match sig with
    | [] => .nil
    | n :: sig =>
      .cons (mkBlock n (fun nv' vt' => denote V L b nv' vt' nl lt) nv vt)
        (denoteBlocks V L bs sig nv vt nl lt)
end

/-- Entry point. `nargs` must be written as a literal (`args.length` would contain free
variables and block Nat literal folding). -/
def denoteTop (V : Type) (L : Nat → Type) (flat : Flat) (nargs : Nat) (args : List V) :
    Expr V L :=
  Trie.pushListK args .leaf 0 fun vt => denote V L flat nargs vt 0 .leaf

/-- Names: `V := Nat`, `L n := Nat`. -/
abbrev NL : Nat → Type := fun _ => Nat

def freshLabels : (sig : List Nat) → Nat → Labels NL sig
  | [], _ => ()
  | _ :: sig, nl => (nl, freshLabels sig (nl + 1))

def argsToList : (n : Nat) → Args Nat n → List Nat
  | 0, _ => []
  | n + 1, as => as.1 :: argsToList n as.2

mutual
/-- `toFlat e nv nl`: `nv` / `nl` = number of variables / labels in scope (next fresh level). -/
def toFlat : Expr Nat NL → Nat → Nat → Flat
  | .ret v, _, _ => .ret v
  | .let_ op k, nv, nl => .let_ op (toFlat (k nv) (nv + 1) nl)
  | .ite c t e, nv, nl => .ite c (toFlat t nv nl) (toFlat e nv nl)
  | .jump (n := n) j args, _, _ => .jump j (argsToList n args)
  | .unreachable, _, _ => .unreachable
  | .letRecs sig bodies k, nv, nl =>
    .letRecs sig (blocksToFlat (bodies (freshLabels sig nl)) nv (nl + sig.length))
      (toFlat (k (freshLabels sig nl)) nv (nl + sig.length))
def blockToFlat : {n : Nat} → Block Nat NL n → Nat → Nat → Flat
  | _, .body e, nv, nl => toFlat e nv nl
  | _, .param f, nv, nl => blockToFlat (f nv) (nv + 1) nl
def blocksToFlat : {sig : List Nat} → Blocks Nat NL sig → Nat → Nat → FBlocks
  | _, .nil, _, _ => .nil
  | _, .cons b bs, nv, nl => .cons (blockToFlat b nv nl) (blocksToFlat bs nv nl)
end

/-! ## Small elaborators -/

open Lean Elab Tactic Meta in
/-- Close `lhs = rhs` with `Eq.refl lhs` WITHOUT running the elaborator's `isDefEq`.
The assignment is unchecked here; only the kernel checks it when the declaration is added. -/
elab "kernel_rfl" : tactic => do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let some (α, lhs, _) := tgt.eq?
    | throwError "kernel_rfl: goal is not an equality{indentExpr tgt}"
  let u ← getLevel α
  goal.assign (mkApp2 (mkConst ``Eq.refl [u]) α lhs)
  replaceMainGoal []

open Lean Meta in
/-- Normalize closed first-order data to constructor form with `Meta.whnf`
(no compiled code needed). `BitVec` payloads are left untouched. -/
meta partial def nfData (e : Lean.Expr) : MetaM Lean.Expr := do
  let e ← whnf e
  let fn := e.getAppFn
  match fn with
  | .const c _ =>
    match (← getEnv).find? c with
    | some (.ctorInfo ci) =>
      let args := e.getAppArgs
      let mut args' := args
      for i in [ci.numParams:args.size] do
        let a := args[i]!
        let ty ← whnfR (← inferType a)
        if ty.isAppOf ``BitVec then continue
        args' := args'.set! i (← nfData a)
      return mkAppN fn args'
    | _ => return e
  | _ => return e

open Lean Elab Term Meta in
/-- `reify% t` elaborates `t : Flat` and replaces it by its constructor normal form. -/
elab "reify% " t:term : term => do
  let e ← elabTermEnsuringType t (mkConst ``Flat)
  synthesizeSyntheticMVarsNoPostponing
  nfData (← instantiateMVars e)

open Lean Elab Command in
/-- Wall-clock time of one command (use with `set_option Elab.async false`). -/
elab "#time " tag:str cmd:command : command => do
  let t0 ← IO.monoNanosNow
  elabCommand cmd
  let t1 ← IO.monoNanosNow
  logInfo m!"TIME {tag.getString} {(t1 - t0) / 1000000} ms"

end A
