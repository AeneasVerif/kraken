module

/-
Rega skeleton, encoding E3 (arity-typed mutual PHOAS: `Expr` / `Block n` / `Blocks sig`,
join-point groups `letRecs sig bodies k`), for the D8 comparison with `E1Skel.lean`.

Same mock `Target`, same op set, same lowering design as `E1Skel.lean`: names `V := Nat`,
`L n := Nat`, symbolic register relation `List (Nat × Reg)`, untrusted hints `dest`/`entry`,
checked moves at jumps; join point `ℓ` of arity `n` is instantiated as `LabJ G n ℓ`.
Encoding-independent parts (code placement, mock target, symbolic-state and move lemmas) are
copied verbatim from `E1Skel.lean`.
-/
public meta import Lean
set_option autoImplicit false

@[expose] public section

namespace RegaSkel3

abbrev Val := BitVec 64
abbrev Mem := BitVec 64 → Option Val

/-! ## E3 (from spike A `Core.lean`, op set cut down to E1Skel's) -/

inductive Op (V : Type) : Type
  | const (c : Val)
  | add (a b : V)
  | load (a : V)

/-- Label tuple of a group with signature `sig` (list of block arities). -/
@[reducible] def Labels (L : Nat → Type) : List Nat → Type
  | [] => Unit
  | n :: sig => L n × Labels L sig

/-- Jump arguments. -/
@[reducible] def Args (V : Type) : Nat → Type
  | 0 => Unit
  | n + 1 => V × Args V n

mutual
inductive Expr (V : Type) (L : Nat → Type) : Type
  | let_ (op : Op V) (k : V → Expr V L)
  | store (a v : V) (k : Expr V L)
  | jnz (c : V) (t e : Expr V L)
  | jump {n : Nat} (j : L n) (args : Args V n)
  | ret (vs : List V)
  | hlt
  | letRecs (sig : List Nat) (bodies : Labels L sig → Blocks V L sig)
      (k : Labels L sig → Expr V L)
inductive Block (V : Type) (L : Nat → Type) : Nat → Type
  | body (e : Expr V L) : Block V L 0
  | param {n : Nat} (f : V → Block V L n) : Block V L (n + 1)
inductive Blocks (V : Type) (L : Nat → Type) : List Nat → Type
  | nil : Blocks V L []
  | cons {n : Nat} {sig : List Nat} (b : Block V L n) (bs : Blocks V L sig) :
      Blocks V L (n :: sig)
end

def Op.wp : Op Val → Mem → (Val → Mem → Prop) → Prop
  | .const c, m, post => post c m
  | .add a b, m, post => post (a + b) m
  | .load a, m, post => ∃ v, m a = some v ∧ post v m

def Op.map {V W : Type} (f : V → W) : Op V → Op W
  | .const c => .const c
  | .add a b => .add (f a) (f b)
  | .load a => .load (f a)

def Op.traverse {V W : Type} (f : V → Option W) : Op V → Option (Op W)
  | .const c => some (.const c)
  | .add a b => match f a, f b with
    | some a, some b => some (.add a b)
    | _, _ => none
  | .load a => match f a with
    | some a => some (.load a)
    | none => none

abbrev Cont (n : Nat) : Type := Args Val n → Mem → Prop
abbrev Post := List Val → Mem → Prop

def upd (m : Mem) (a v : Val) : Mem := fun a' => if a' = a then some v else m a'

mutual
def wp (Q : Post) : Expr Val Cont → Mem → Prop
  | .let_ op k, m => op.wp m (fun v m' => wp Q (k v) m')
  | .store a v k, m => (m a).isSome ∧ wp Q k (upd m a v)
  | .jnz c t e, m => (c ≠ 0 → wp Q t m) ∧ (c = 0 → wp Q e m)
  | .jump j as, m => j as m
  | .ret vs, m => Q vs m
  | .hlt, _ => False
  | .letRecs sig bodies k, m =>
      ∀ J : Labels Cont sig, closedBlocks Q (bodies J) J → wp Q (k J) m
def closedBlock (Q : Post) : {n : Nat} → Block Val Cont n → Cont n → Prop
  | _, .body e, J => ∀ m, wp Q e m → J () m
  | _, .param f, J => ∀ v, closedBlock Q (f v) (fun as m => J (v, as) m)
def closedBlocks (Q : Post) : {sig : List Nat} → Blocks Val Cont sig → Labels Cont sig → Prop
  | _, .nil, _ => True
  | _, .cons b bs, J => closedBlock Q b J.1 ∧ closedBlocks Q bs J.2
end

/-- wp of a block applied to its arguments (only for the top-level statement). -/
def wpBlock (Q : Post) : {n : Nat} → Block Val Cont n → Args Val n → Mem → Prop
  | _, .body e, _, m => wp Q e m
  | _, .param f, as, m => wpBlock Q (f as.1) as.2 m

theorem closedBlock_wpBlock {Q : Post} : ∀ {n : Nat} (b : Block Val Cont n) (J : Cont n),
    closedBlock Q b J → ∀ as m, wpBlock Q b as m → J as m
  | _, .body _, _, h, _, m, hw => h m hw
  | _, .param f, J, h, as, m, hw => closedBlock_wpBlock (f as.1) (fun as' m => J (as.1, as') m)
      (h as.1) as.2 m hw

def argsToList {V : Type} : (n : Nat) → Args V n → List V
  | 0, _ => []
  | n + 1, as => as.1 :: argsToList n as.2

inductive OpRel {V₁ V₂ : Type} (R : V₁ → V₂ → Prop) : Op V₁ → Op V₂ → Prop
  | const (c : Val) : OpRel R (.const c) (.const c)
  | add {a₁ b₁ a₂ b₂} : R a₁ a₂ → R b₁ b₂ → OpRel R (.add a₁ b₁) (.add a₂ b₂)
  | load {a₁ a₂} : R a₁ a₂ → OpRel R (.load a₁) (.load a₂)

inductive Forall₂ {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Forall₂ R [] []
  | cons {a b as bs} : R a b → Forall₂ R as bs → Forall₂ R (a :: as) (b :: bs)

/-- A pair of labels of the same arity. -/
abbrev LPair (L₁ L₂ : Nat → Type) : Type := (n : Nat) × L₁ n × L₂ n

def zipL {L₁ L₂ : Nat → Type} : (sig : List Nat) → Labels L₁ sig → Labels L₂ sig → List (LPair L₁ L₂)
  | [], _, _ => []
  | n :: sig, ls₁, ls₂ => ⟨n, ls₁.1, ls₂.1⟩ :: zipL sig ls₁.2 ls₂.2

mutual
inductive Wf {V₁ V₂ : Type} {L₁ L₂ : Nat → Type} :
    List (V₁ × V₂) → List (LPair L₁ L₂) → Expr V₁ L₁ → Expr V₂ L₂ → Prop
  | let_ {G D op₁ op₂ k₁ k₂} : OpRel (fun a b => (a, b) ∈ G) op₁ op₂ →
      (∀ v₁ v₂, Wf ((v₁, v₂) :: G) D (k₁ v₁) (k₂ v₂)) → Wf G D (.let_ op₁ k₁) (.let_ op₂ k₂)
  | store {G D a₁ a₂ v₁ v₂ k₁ k₂} : (a₁, a₂) ∈ G → (v₁, v₂) ∈ G → Wf G D k₁ k₂ →
      Wf G D (.store a₁ v₁ k₁) (.store a₂ v₂ k₂)
  | jnz {G D c₁ c₂ t₁ t₂ e₁ e₂} : (c₁, c₂) ∈ G → Wf G D t₁ t₂ → Wf G D e₁ e₂ →
      Wf G D (.jnz c₁ t₁ e₁) (.jnz c₂ t₂ e₂)
  | jump {G D n} {j₁ : L₁ n} {j₂ : L₂ n} {as₁ as₂} : ⟨n, j₁, j₂⟩ ∈ D →
      Forall₂ (fun a b => (a, b) ∈ G) (argsToList n as₁) (argsToList n as₂) →
      Wf G D (.jump j₁ as₁) (.jump j₂ as₂)
  | ret {G D vs₁ vs₂} : Forall₂ (fun a b => (a, b) ∈ G) vs₁ vs₂ →
      Wf G D (.ret vs₁) (.ret vs₂)
  | hlt {G D} : Wf G D .hlt .hlt
  | letRecs {G D sig b₁ b₂ k₁ k₂} :
      (∀ ls₁ ls₂, WfBs G (zipL sig ls₁ ls₂ ++ D) (b₁ ls₁) (b₂ ls₂)) →
      (∀ ls₁ ls₂, Wf G (zipL sig ls₁ ls₂ ++ D) (k₁ ls₁) (k₂ ls₂)) →
      Wf G D (.letRecs sig b₁ k₁) (.letRecs sig b₂ k₂)
inductive WfB {V₁ V₂ : Type} {L₁ L₂ : Nat → Type} :
    List (V₁ × V₂) → List (LPair L₁ L₂) → {n : Nat} → Block V₁ L₁ n → Block V₂ L₂ n → Prop
  | body {G D e₁ e₂} : Wf G D e₁ e₂ → WfB G D (.body e₁) (.body e₂)
  | param {G D n} {f₁ : V₁ → Block V₁ L₁ n} {f₂ : V₂ → Block V₂ L₂ n} :
      (∀ v₁ v₂, WfB ((v₁, v₂) :: G) D (f₁ v₁) (f₂ v₂)) → WfB G D (.param f₁) (.param f₂)
inductive WfBs {V₁ V₂ : Type} {L₁ L₂ : Nat → Type} :
    List (V₁ × V₂) → List (LPair L₁ L₂) → {sig : List Nat} → Blocks V₁ L₁ sig →
      Blocks V₂ L₂ sig → Prop
  | nil {G D} : WfBs G D .nil .nil
  | cons {G D n sig} {b₁ : Block V₁ L₁ n} {b₂ : Block V₂ L₂ n} {bs₁ : Blocks V₁ L₁ sig}
      {bs₂ : Blocks V₂ L₂ sig} : WfB G D b₁ b₂ → WfBs G D bs₁ bs₂ →
      WfBs G D (.cons b₁ bs₁) (.cons b₂ bs₂)
end

/-! ## Code placement (copied) -/

def InfixAt {α : Type} (c p : List α) (k : Nat) : Prop :=
  ∀ j (h : j < c.length), p[k + j]? = some c[j]

theorem InfixAt.left {α : Type} {a b p : List α} {k : Nat} (h : InfixAt (a ++ b) p k) :
    InfixAt a p k := by
  intro j hj
  have := h j (by simp; omega)
  simpa [List.getElem_append_left hj] using this

theorem InfixAt.right {α : Type} {a b p : List α} {k : Nat} (h : InfixAt (a ++ b) p k) :
    InfixAt b p (k + a.length) := by
  intro j hj
  have := h (a.length + j) (by simp; omega)
  simpa [Nat.add_assoc, List.getElem_append_right] using this

theorem InfixAt.head {α : Type} {a : α} {b p : List α} {k : Nat} (h : InfixAt (a :: b) p k) :
    p[k]? = some a := by
  have := h 0 (by simp)
  simpa only [Nat.add_zero, List.getElem_cons_zero] using this

theorem InfixAt.tail {α : Type} {a : α} {b p : List α} {k : Nat} (h : InfixAt (a :: b) p k) :
    InfixAt b p (k + 1) :=
  InfixAt.right (a := [a]) h

/-! ## Mock target (copied) -/

structure Target where
  Reg : Type
  [deq : DecidableEq Reg]
  Dir : Type
  MData : Type
  get : MData → Reg → Val
  mem : MData → Mem
  alloc : List Reg
  scratch : List Reg
  resRegs : List Reg
  argRegs : List Reg
  Host : Type
  prog : Host → List Dir
  /-- From index `k` of the host program, state `s`, eventually `post` (at the return point). -/
  Ev : Host → (MData → Prop) → Nat → MData → Prop
  label : String → Dir
  jmp : String → Dir
  movS : Reg → Reg → List Dir
  opS : Op Reg → Reg → List Dir
  storeS : Reg → Reg → List Dir
  jzS : Reg → String → List Dir
  retS : List Dir
  ev_label : ∀ {H post} {k : Nat} {s l}, (prog H)[k]? = some (label l) → Ev H post (k + 1) s →
    Ev H post k s
  ev_jmp : ∀ {H post} {i k : Nat} {s l},
    (∀ (i j : Nat) (l : String), (prog H)[i]? = some (label l) → (prog H)[j]? = some (label l) → i = j) →
    (prog H)[i]? = some (jmp l) → (prog H)[k]? = some (label l) → Ev H post k s →
    Ev H post i s
  ev_mov : ∀ {H post i s d r}, InfixAt (movS d r) (prog H) i →
    (∀ s', (∀ r', r' ≠ d → get s' r' = get s r') → get s' d = get s r → mem s' = mem s →
      Ev H post (i + (movS d r).length) s') →
    Ev H post i s
  ev_op : ∀ {H post i s d} (o : Op Reg), InfixAt (opS o d) (prog H) i →
    Op.wp (o.map (get s)) (mem s) (fun v _ => ∀ s',
      (∀ r', r' ≠ d → r' ∉ scratch → get s' r' = get s r') → get s' d = v → mem s' = mem s →
      Ev H post (i + (opS o d).length) s') →
    Ev H post i s
  ev_store : ∀ {H post i s a v}, InfixAt (storeS a v) (prog H) i →
    (mem s (get s a)).isSome →
    (∀ s', (∀ r', r' ∉ scratch → get s' r' = get s r') →
      mem s' = upd (mem s) (get s a) (get s v) → Ev H post (i + (storeS a v).length) s') →
    Ev H post i s
  ev_jz : ∀ {H post} {i k : Nat} {s r l},
    (∀ (i j : Nat) (l : String), (prog H)[i]? = some (label l) → (prog H)[j]? = some (label l) → i = j) →
    InfixAt (jzS r l) (prog H) i → (prog H)[k]? = some (label l) →
    (∀ s', (∀ r', r' ∉ scratch → get s' r' = get s r') → mem s' = mem s →
      (get s r = 0 → Ev H post k s') ∧ (get s r ≠ 0 → Ev H post (i + (jzS r l).length) s')) →
    Ev H post i s
  ev_ret : ∀ {H post i s}, InfixAt retS (prog H) i → post s → Ev H post i s

attribute [instance] Target.deq

variable (T : Target)

def Target.LabelsUnique (H : T.Host) : Prop :=
  ∀ (i j : Nat) (l : String), (T.prog H)[i]? = some (T.label l) → (T.prog H)[j]? = some (T.label l) → i = j

/-! ## The lowering -/

abbrev Sym := List (Nat × T.Reg)

structure Entry where
  live : List (Nat × T.Reg)
  ploc : List T.Reg

structure Hints where
  dest : Nat → Option T.Reg
  entry : Nat → Entry T

/-- No `PL`/`pend` here: parameter registers are an argument of `lowerB`, and a group's labels
are known at `letRecs`. -/
structure St where
  nv : Nat
  nl : Nat
  R : Sym T

def lname (n : Nat) : String := "L" ++ toString n

/-- Names: `L n := Nat`. -/
abbrev NL : Nat → Type := fun _ => Nat

def freshLabels : (sig : List Nat) → Nat → Labels NL sig
  | [], _ => ()
  | _ :: sig, nl => (nl, freshLabels sig (nl + 1))

variable {T}

def lookup (R : Sym T) (x : Nat) : Option T.Reg := (R.find? (fun p => p.1 == x)).map (·.2)

def clob (d : Option T.Reg) (R : Sym T) : Sym T :=
  R.filter (fun p => decide (some p.2 ≠ d) && decide (p.2 ∉ T.scratch))

def bindN (x : Nat) (r : T.Reg) (R : Sym T) : Sym T := (x, r) :: R.filter (fun p => p.1 != x)

def movSym (d s : T.Reg) (R : Sym T) : Sym T :=
  if d = s then R else
    (R.filter (fun p => decide (p.2 = s))).map (fun p => (p.1, d)) ++
      R.filter (fun p => decide (p.2 ≠ d))

def execMoves : List (T.Reg × T.Reg) → Sym T → Option (Sym T)
  | [], R => some R
  | (d, s) :: mv, R => if d ∈ T.alloc then execMoves mv (movSym d s R) else none

def movesCode : List (T.Reg × T.Reg) → List T.Dir
  | [] => []
  | (d, s) :: mv => T.movS d s ++ movesCode mv

/-- Untrusted: naive sequential moves; wrong orders are caught by the check. -/
def pmove (R : Sym T) (tgts : List (Nat × T.Reg)) : List (T.Reg × T.Reg) :=
  tgts.filterMap fun (x, r) => if (x, r) ∈ R then none else (lookup R x).map fun r' => (r, r')

def prepend (pre : List T.Dir) (r : Except String (List T.Dir × Nat × Nat)) :
    Except String (List T.Dir × Nat × Nat) :=
  match r with
  | .ok (c, nv, nl) => .ok (pre ++ c, nv, nl)
  | .error e => .error e

/-- Moves into `tgts`, then check; returns the move code. -/
def shuffle (R : Sym T) (tgts : List (Nat × T.Reg)) : Option (List T.Dir) :=
  let mv := pmove R tgts
  match execMoves mv R with
  | some R' => if tgts.all (fun t => decide (t ∈ R')) then some (movesCode mv) else none
  | none => none

mutual
def lowerE (h : Hints T) : Expr Nat NL → St T → Except String (List T.Dir × Nat × Nat)
  | .let_ op k, st =>
    match h.dest st.nv, op.traverse (lookup st.R) with
    | some d, some o =>
      if d ∈ T.alloc then
        prepend (T.opS o d)
          (lowerE h (k st.nv) ⟨st.nv + 1, st.nl, bindN st.nv d (clob (some d) st.R)⟩)
      else .error "alloc"
    | _, _ => .error "let"
  | .store a v k, st =>
    match lookup st.R a, lookup st.R v with
    | some ra, some rv => prepend (T.storeS ra rv) (lowerE h k ⟨st.nv, st.nl, clob none st.R⟩)
    | _, _ => .error "store"
  | .jnz c t e, st =>
    match lookup st.R c with
    | some rc =>
      match lowerE h t ⟨st.nv, st.nl + 1, clob none st.R⟩ with
      | .ok (ct, nv1, nl1) =>
        prepend (T.jzS rc (lname st.nl) ++ ct ++ [T.label (lname st.nl)])
          (lowerE h e ⟨nv1, nl1, clob none st.R⟩)
      | .error e => .error e
    | none => .error "jnz"
  | .jump (n := n) j as, st =>
    if (argsToList n as).length = (h.entry j).ploc.length then
      match shuffle st.R ((h.entry j).live ++ (argsToList n as).zip (h.entry j).ploc) with
      | some c => .ok (c ++ [T.jmp (lname j)], st.nv, st.nl)
      | none => .error "jump"
    else .error "arity"
  | .ret vs, st =>
    if vs.length = T.resRegs.length then
      match shuffle st.R (vs.zip T.resRegs) with
      | some c => .ok (c ++ T.retS, st.nv, st.nl)
      | none => .error "ret"
    else .error "ret arity"
  | .hlt, st => .ok ([], st.nv, st.nl)
  | .letRecs sig bodies k, st =>
    match lowerE h (k (freshLabels sig st.nl)) ⟨st.nv, st.nl + sig.length, st.R⟩ with
    | .ok (cr, nv1, nl1) =>
      prepend cr (lowerBs h (bodies (freshLabels sig st.nl)) (freshLabels sig st.nl) nv1 nl1)
    | .error e => .error e
/-- A block: bind its parameters to the registers `PL`, then lower the body. -/
def lowerB (h : Hints T) : {n : Nat} → Block Nat NL n → List T.Reg → St T →
    Except String (List T.Dir × Nat × Nat)
  | _, .body e, _, st => lowerE h e st
  | _, .param f, PL, st =>
    match PL with
    | [] => .error "param"
    | r :: PL => lowerB h (f st.nv) PL ⟨st.nv + 1, st.nl, bindN st.nv r st.R⟩
/-- A group's blocks, each after its label, entered with the hinted registers. -/
def lowerBs (h : Hints T) : {sig : List Nat} → Blocks Nat NL sig → Labels NL sig → Nat → Nat →
    Except String (List T.Dir × Nat × Nat)
  | _, .nil, _, nv, nl => .ok ([], nv, nl)
  | _, .cons b bs, ls, nv, nl =>
    match lowerB h b (h.entry ls.1).ploc ⟨nv, nl, (h.entry ls.1).live⟩ with
    | .ok (cb, nv1, nl1) => prepend (T.label (lname ls.1) :: cb) (lowerBs h bs ls.2 nv1 nl1)
    | .error e => .error e
end

/-! ## Invariants -/

def Agree (G : List (Val × Nat)) (R : Sym T) (s : T.MData) : Prop :=
  ∀ x r, (x, r) ∈ R → ∀ v, (v, x) ∈ G → T.get s r = v

def RegsHold (s : T.MData) (rs : List T.Reg) (vs : List Val) : Prop :=
  Forall₂ (fun r v => T.get s r = v) rs vs

def Inv (F : Mem) (s₀ : T.MData) (m : Mem) (s : T.MData) : Prop :=
  (∀ a, T.mem s a = (m a).or (F a)) ∧ (∀ a, m a = none ∨ F a = none) ∧
  (∀ r, r ∉ T.alloc → r ∉ T.scratch → T.get s r = T.get s₀ r)

def FnPost (Q : Post) (F : Mem) (s₀ : T.MData) : T.MData → Prop := fun s =>
  ∃ rets m', Q rets m' ∧ RegsHold s T.resRegs rets ∧ Inv F s₀ m' s

section
variable (H : T.Host) (h : Hints T) (Q : Post) (F : Mem) (s₀ : T.MData)

/-- The join-point predicate: the source continuation chosen for label `ℓ` of arity `n`. -/
def LabJ (G : List (Val × Nat)) (n : Nat) (ℓ : Nat) : Cont n := fun as m =>
  ∃ k, (T.prog H)[k]? = some (T.label (lname ℓ)) ∧
    ∀ s, Agree G (h.entry ℓ).live s → RegsHold s (h.entry ℓ).ploc (argsToList n as) →
      Inv F s₀ m s → T.Ev H (FnPost Q F s₀) k s

/-- The instantiation of a whole group. -/
def labsJ (G : List (Val × Nat)) : (sig : List Nat) → Labels NL sig → Labels Cont sig
  | [], _ => ()
  | n :: sig, ls => (LabJ H h Q F s₀ G n ls.1, labsJ G sig ls.2)

def DOk (G : List (Val × Nat)) (D : List (LPair Cont NL)) : Prop :=
  ∀ n J ℓ, (⟨n, J, ℓ⟩ : LPair Cont NL) ∈ D → ∃ G', (∀ p ∈ G', p ∈ G) ∧ J = LabJ H h Q F s₀ G' n ℓ

end

/-! ## Lemmas about the symbolic state (copied) -/

theorem lookup_mem {R : Sym T} {x : Nat} {r : T.Reg} (h : lookup R x = some r) : (x, r) ∈ R := by
  simp only [lookup, Option.map_eq_some_iff] at h
  obtain ⟨⟨y, r'⟩, hp, rfl⟩ := h
  have := List.mem_of_find?_eq_some hp
  have hx := List.find?_some hp
  simp only [beq_iff_eq] at hx
  subst hx; exact this

theorem traverse_ok {G : List (Val × Nat)} {R : Sym T} {s : T.MData} (hA : Agree G R s)
    {op₁ : Op Val} {op₂ : Op Nat} (hr : OpRel (fun a b => (a, b) ∈ G) op₁ op₂) {o : Op T.Reg}
    (ht : op₂.traverse (lookup R) = some o) : o.map (T.get s) = op₁ := by
  cases hr with
  | const c => simp [Op.traverse] at ht; subst ht; rfl
  | add ha hb =>
    simp only [Op.traverse] at ht
    split at ht <;> simp at ht
    rename_i ra rb hra hrb
    subst ht
    simp [Op.map, hA _ _ (lookup_mem hra) _ ha, hA _ _ (lookup_mem hrb) _ hb]
  | load ha =>
    simp only [Op.traverse] at ht
    split at ht <;> simp at ht
    rename_i ra hra
    subst ht
    simp [Op.map, hA _ _ (lookup_mem hra) _ ha]

theorem Agree.clob {G : List (Val × Nat)} {R : Sym T} {s s' : T.MData} {d : Option T.Reg}
    (hA : Agree G R s) (hs : ∀ r, some r ≠ d → r ∉ T.scratch → T.get s' r = T.get s r) :
    Agree G (clob d R) s' := by
  intro x r hx v hv
  simp only [RegaSkel3.clob, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hx
  rw [hs r hx.2.1 hx.2.2]; exact hA _ _ hx.1 _ hv

theorem Agree.bindN {G : List (Val × Nat)} {R : Sym T} {s : T.MData} {x : Nat} {r : T.Reg}
    {v : Val} (hA : Agree G R s) (hx : ∀ p ∈ G, p.2 < x) (hr : T.get s r = v) :
    Agree ((v, x) :: G) (bindN x r R) s := by
  intro y r' hy w hw
  simp only [RegaSkel3.bindN, List.mem_cons, List.mem_filter, Prod.mk.injEq, bne_iff_ne, ne_eq] at hy hw
  rcases hy with ⟨rfl, rfl⟩ | ⟨hy, hne⟩
  · rcases hw with ⟨rfl, -⟩ | hw
    · exact hr
    · exact absurd (hx _ hw) (by simp)
  · rcases hw with ⟨rfl, rfl⟩ | hw
    · exact absurd rfl hne
    · exact hA _ _ hy _ hw

theorem Agree.movSym {G : List (Val × Nat)} {R : Sym T} {s s' : T.MData} {d r : T.Reg}
    (hA : Agree G R s) (hs : ∀ r', r' ≠ d → T.get s' r' = T.get s r')
    (hd : T.get s' d = T.get s r) : Agree G (movSym d r R) s' := by
  intro x q hx v hv
  unfold RegaSkel3.movSym at hx
  split at hx
  · rename_i hdr
    subst hdr
    by_cases hq : q = d
    · subst hq; rw [hd]; exact hA _ _ hx _ hv
    · rw [hs q hq]; exact hA _ _ hx _ hv
  · simp only [List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq] at hx
    rcases hx with ⟨⟨y, q'⟩, ⟨hy, rfl⟩, he⟩ | ⟨hx, hne⟩
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [hd]; exact hA _ _ hy _ hv
    · rw [hs q hne]; exact hA _ _ hx _ hv

theorem Inv.regs {F : Mem} {s₀ s s' : T.MData} {m : Mem} (hI : Inv F s₀ m s)
    (hm : T.mem s' = T.mem s) (d : Option T.Reg)
    (hs : ∀ r, some r ≠ d → r ∉ T.scratch → T.get s' r = T.get s r)
    (hd : ∀ r, d = some r → r ∈ T.alloc) : Inv F s₀ m s' := by
  refine ⟨fun a => hm ▸ hI.1 a, hI.2.1, fun r h1 h2 => ?_⟩
  rw [hs r (fun e => h1 (hd r e.symm)) h2]; exact hI.2.2 r h1 h2

theorem Inv.store {F : Mem} {s₀ s s' : T.MData} {m : Mem} {a v : Val} (hI : Inv F s₀ m s)
    (ha : (m a).isSome) (hm : T.mem s' = upd (T.mem s) a v)
    (hs : ∀ r, r ∉ T.scratch → T.get s' r = T.get s r) : Inv F s₀ (upd m a v) s' := by
  refine ⟨fun a' => ?_, fun a' => ?_, fun r h1 h2 => ?_⟩
  · rw [hm]; simp only [upd]; split
    · rfl
    · exact hI.1 a'
  · simp only [upd]; split
    · subst a'; rcases hI.2.1 a with h | h
      · simp [h] at ha
      · exact Or.inr h
    · exact hI.2.1 a'
  · rw [hs r h2]; exact hI.2.2 r h1 h2

theorem Inv.load_isSome {F : Mem} {s₀ s : T.MData} {m : Mem} {a : Val} (hI : Inv F s₀ m s)
    (ha : (m a).isSome) : (T.mem s a).isSome := by
  rw [hI.1 a]; cases h : m a <;> simp_all

theorem Op.wp_sub {o : Op Val} {m M : Mem} (hsub : ∀ a v, m a = some v → M a = some v)
    {P : Val → Prop} (h : o.wp m (fun v _ => P v)) : o.wp M (fun v _ => P v) := by
  cases o with
  | const c => exact h
  | add a b => exact h
  | load a => obtain ⟨v, h1, h2⟩ := h; exact ⟨v, hsub _ _ h1, h2⟩

theorem Op.wp_imp {o : Op Val} {m : Mem} {P P' : Val → Mem → Prop}
    (hP : ∀ v m', P v m' → P' v m') (h : o.wp m P) : o.wp m P' := by
  cases o with
  | const c => exact hP _ _ h
  | add a b => exact hP _ _ h
  | load a => obtain ⟨v, h1, h2⟩ := h; exact ⟨v, h1, hP _ _ h2⟩

theorem Op.wp_mem {o : Op Val} {m : Mem} {P : Val → Mem → Prop} (h : o.wp m P) :
    o.wp m (fun v m' => m' = m ∧ P v m') := by
  cases o with
  | const c => exact ⟨rfl, h⟩
  | add a b => exact ⟨rfl, h⟩
  | load a => obtain ⟨v, h1, h2⟩ := h; exact ⟨v, h1, rfl, h2⟩

/-! ## Moves (copied) -/

section
variable {H : T.Host} {post : T.MData → Prop} {F : Mem} {s₀ : T.MData}

theorem movesCode_cons (d r : T.Reg) (mv : List (T.Reg × T.Reg)) :
    movesCode ((d, r) :: mv) = T.movS d r ++ movesCode mv := rfl

theorem moves_ok {G : List (Val × Nat)} {m : Mem} :
    ∀ (mv : List (T.Reg × T.Reg)) (R R' : Sym T) (i : Nat) (s : T.MData),
    execMoves mv R = some R' → InfixAt (movesCode mv) (T.prog H) i →
    Agree G R s → Inv F s₀ m s →
    (∀ s', Agree G R' s' → Inv F s₀ m s' → T.Ev H post (i + (movesCode mv).length) s') →
    T.Ev H post i s
  | [], R, R', i, s, he, _, hA, hI, k => by
    simp only [execMoves, Option.some.injEq] at he; subst he
    simpa [movesCode] using k s hA hI
  | (d, r) :: mv, R, R', i, s, he, hc, hA, hI, k => by
    simp only [execMoves] at he
    split at he
    · rename_i hd
      rw [movesCode_cons] at hc
      refine T.ev_mov hc.left fun s1 hs1 hd1 hm1 => ?_
      refine moves_ok mv _ R' _ s1 he hc.right (hA.movSym hs1 hd1)
        (hI.regs hm1 (some d) (fun r' h1 _ => hs1 r' (fun e => h1 (by rw [e])))
          (fun r' e => by cases e; exact hd)) fun s2 hA2 hI2 => ?_
      have := k s2 hA2 hI2
      rwa [movesCode_cons, List.length_append, ← Nat.add_assoc] at this
    · simp at he

theorem shuffle_ok {G : List (Val × Nat)} {m : Mem} {R : Sym T} {tgts : List (Nat × T.Reg)}
    {c : List T.Dir} {i : Nat} {s : T.MData}
    (hs : shuffle R tgts = some c) (hc : InfixAt c (T.prog H) i)
    (hA : Agree G R s) (hI : Inv F s₀ m s)
    (k : ∀ s', (∀ x r, (x, r) ∈ tgts → ∀ v, (v, x) ∈ G → T.get s' r = v) → Inv F s₀ m s' →
      T.Ev H post (i + c.length) s') :
    T.Ev H post i s := by
  unfold shuffle at hs
  dsimp only at hs
  split at hs
  · rename_i R' hR'
    split at hs
    · rename_i hall
      simp only [Option.some.injEq] at hs; subst hs
      refine moves_ok _ R R' i s hR' hc hA hI fun s' hA' hI' => k s' (fun x r hx v hv => ?_) hI'
      simp only [List.all_eq_true, decide_eq_true_eq] at hall
      exact hA' x r (hall _ hx) v hv
    · simp at hs
  · simp at hs

end

theorem regsHold_of_zip {G : List (Val × Nat)} {s : T.MData} :
    ∀ {vs₁ : List Val} {vs : List Nat} {rs : List T.Reg},
    Forall₂ (fun a b => (a, b) ∈ G) vs₁ vs → vs.length = rs.length →
    (∀ x r, (x, r) ∈ vs.zip rs → ∀ v, (v, x) ∈ G → T.get s r = v) →
    RegsHold s rs vs₁
  | _, _, [], .nil, _, _ => .nil
  | _, _, r :: rs, .cons hab hrest, hl, hz =>
    .cons (hz _ r (by simp) _ hab)
      (regsHold_of_zip hrest (by simpa using hl) fun x r' hx v hv => hz x r' (by simp [hx]) v hv)
  | _, _, [], .cons _ _, hl, _ => by simp at hl
  | _, _, _ :: _, .nil, hl, _ => by simp at hl

theorem prepend_ok {pre : List T.Dir} {r : Except String (List T.Dir × Nat × Nat)}
    {c : List T.Dir} {nv nl : Nat} (h : prepend pre r = .ok (c, nv, nl)) :
    ∃ c', r = .ok (c', nv, nl) ∧ c = pre ++ c' := by
  unfold prepend at h
  split at h <;> simp_all

/-! ## Join-point environment (E3-specific) -/

section
variable {H : T.Host} {h : Hints T} {Q : Post} {F : Mem} {s₀ : T.MData}

theorem DOk.mono {G G' : List (Val × Nat)} {D : List (LPair Cont NL)} (hD : DOk H h Q F s₀ G D)
    (hG : ∀ p ∈ G, p ∈ G') : DOk H h Q F s₀ G' D := by
  intro n J ℓ hJ
  obtain ⟨G'', hG'', rfl⟩ := hD n J ℓ hJ
  exact ⟨G'', fun p hp => hG p (hG'' p hp), rfl⟩

theorem mem_zipL_labsJ {G : List (Val × Nat)} : ∀ {sig : List Nat} {ls : Labels NL sig}
    {n : Nat} {J : Cont n} {ℓ : Nat},
    (⟨n, J, ℓ⟩ : LPair Cont NL) ∈ zipL sig (labsJ H h Q F s₀ G sig ls) ls →
    J = LabJ H h Q F s₀ G n ℓ
  | [], _, _, _, _, hm => by simp [zipL] at hm
  | _ :: _, _, _, _, _, hm => by
    simp only [zipL, labsJ, List.mem_cons] at hm
    rcases hm with he | hm
    · cases he; rfl
    · exact mem_zipL_labsJ hm

theorem DOk.group {G : List (Val × Nat)} {D : List (LPair Cont NL)} (hD : DOk H h Q F s₀ G D)
    (sig : List Nat) (ls : Labels NL sig) :
    DOk H h Q F s₀ G (zipL sig (labsJ H h Q F s₀ G sig ls) ls ++ D) := by
  intro n J ℓ hm
  rcases List.mem_append.1 hm with hm | hm
  · exact ⟨G, fun p hp => hp, mem_zipL_labsJ hm⟩
  · exact hD n J ℓ hm

end

theorem bound_cons {G : List (Val × Nat)} {nv : Nat} (hG : ∀ p ∈ G, p.2 < nv) (v : Val) :
    ∀ p ∈ (v, nv) :: G, p.2 < nv + 1 := by
  intro p hp; simp at hp; rcases hp with rfl | hp
  · simp
  · have := hG _ hp; omega

/-! ## The main lemma: mutual structural recursion on the `Wf` derivation -/

section
variable (H : T.Host) (h : Hints T) (Q : Post) (F : Mem) (s₀ : T.MData)

mutual
theorem lowerE_correct (hu : T.LabelsUnique H) {G : List (Val × Nat)} {D : List (LPair Cont NL)}
    {e₁ : Expr Val Cont} {e₂ : Expr Nat NL} (hwf : Wf G D e₁ e₂) :
    ∀ (st : St T) (code : List T.Dir) (nv' nl' : Nat),
    lowerE h e₂ st = .ok (code, nv', nl') →
    (∀ p ∈ G, p.2 < st.nv) →
    st.nv ≤ nv' ∧
    ∀ (k : Nat) (m : Mem) (s : T.MData),
    InfixAt code (T.prog H) k →
    DOk H h Q F s₀ G D →
    Agree G st.R s → Inv F s₀ m s →
    wp Q e₁ m → T.Ev H (FnPost Q F s₀) k s :=
  match hwf with
  | @Wf.let_ _ _ _ _ G D op₁ op₂ k₁ k₂ hop hk => by
    intro st code nv' nl' hl hG
    simp only [lowerE] at hl
    split at hl
    · rename_i d o hd ho
      split at hl
      · rename_i hda
        obtain ⟨c', hl', rfl⟩ := prepend_ok hl
        have ih' := fun v => lowerE_correct hu (hk v st.nv) _ c' nv' nl' hl' (bound_cons hG v)
        refine ⟨by have := (ih' 0).1; simp at this; omega, ?_⟩
        intro k m s hc hD hA hI hw
        simp only [wp] at hw
        refine T.ev_op o hc.left ?_
        rw [traverse_ok hA hop ho]
        refine Op.wp_sub (fun a v e => ?_) (P := fun v => ∀ s', _ → _ → _ → _)
          (Op.wp_imp (fun v m' hv => ?_) (Op.wp_mem hw))
        · rw [hI.1 a, e]; rfl
        · obtain ⟨rfl, hv⟩ := hv
          intro s' hs' hd' hm'
          refine (ih' v).2 _ _ s' hc.right (hD.mono fun p hp => List.mem_cons_of_mem _ hp) ?_ ?_ hv
          · exact (hA.clob (fun r h1 h2 => hs' r (fun e => h1 (by rw [e])) h2)).bindN
              (fun p hp => hG p hp) hd'
          · exact hI.regs hm' (some d) (fun r h1 h2 => hs' r (fun e => h1 (by rw [e])) h2)
              (fun r e => by cases e; exact hda)
      · simp at hl
    · simp at hl
  | @Wf.store _ _ _ _ G D a₁ a₂ v₁ v₂ k₁ k₂ ha hv hk => by
    intro st code nv' nl' hl hG
    simp only [lowerE] at hl
    split at hl
    · rename_i ra rv hra hrv
      obtain ⟨c', hl', rfl⟩ := prepend_ok hl
      have ih' := lowerE_correct hu hk _ c' nv' nl' hl' hG
      refine ⟨ih'.1, ?_⟩
      intro k m s hc hD hA hI hw
      simp only [wp] at hw
      obtain ⟨hsome, hw⟩ := hw
      have e1 := hA _ _ (lookup_mem hra) _ ha
      have e2 := hA _ _ (lookup_mem hrv) _ hv
      refine T.ev_store hc.left (by rw [e1]; exact hI.load_isSome hsome) fun s' hs' hm' => ?_
      rw [e1, e2] at hm'
      exact ih'.2 _ _ s' hc.right hD (hA.clob (fun r _ h2 => hs' r h2)) (hI.store hsome hm' hs') hw
    · simp at hl
  | @Wf.jnz _ _ _ _ G D c₁ c₂ t₁ t₂ e₁ e₂ hc ht he => by
    intro st code nv' nl' hl hG
    simp only [lowerE] at hl
    split at hl
    · rename_i rc hrc
      split at hl
      · rename_i ct nv1 nl1 hlt
        obtain ⟨c', hl', rfl⟩ := prepend_ok hl
        have iht' := lowerE_correct hu ht _ ct nv1 nl1 hlt hG
        have ihe' := lowerE_correct hu he _ c' nv' nl' hl' (fun p hp => Nat.lt_of_lt_of_le (hG p hp) iht'.1)
        refine ⟨Nat.le_trans iht'.1 ihe'.1, ?_⟩
        intro k m s hcode hD hA hI hw
        simp only [wp] at hw
        obtain ⟨hwt, hwe⟩ := hw
        have e1 := hA _ _ (lookup_mem hrc) _ hc
        have hcode1 := hcode.left
        have hlab : (T.prog H)[k + (T.jzS rc (lname st.nl)).length + ct.length]? =
            some (T.label (lname st.nl)) := by
          have := hcode1.right (a := T.jzS rc (lname st.nl) ++ ct)
          simpa [Nat.add_assoc] using this.head
        refine T.ev_jz hu hcode1.left.left hlab fun s' hs' hm' => ⟨fun h0 => ?_, fun h0 => ?_⟩
        · refine T.ev_label hlab ?_
          have := ihe'.2 _ m s' hcode.right hD (hA.clob (fun r _ h2 => hs' r h2))
            (hI.regs hm' none (fun r _ h2 => hs' r h2) (fun _ e => by cases e))
            (hwe (by rw [← e1]; exact h0))
          simpa [Nat.add_assoc] using this
        · exact iht'.2 _ m s' hcode1.left.right hD
            (hA.clob (fun r _ h2 => hs' r h2))
            (hI.regs hm' none (fun r _ h2 => hs' r h2) (fun _ e => by cases e))
            (hwt (by rw [← e1]; exact h0))
      · simp at hl
    · simp at hl
  | @Wf.jump _ _ _ _ G D n j₁ j₂ as₁ as₂ hj has => by
    intro st code nv' nl' hl hG
    simp only [lowerE] at hl
    split at hl
    · rename_i hlen
      split at hl
      · rename_i c hsh
        simp only [Except.ok.injEq, Prod.mk.injEq] at hl
        obtain ⟨rfl, rfl, rfl⟩ := hl
        refine ⟨Nat.le_refl _, ?_⟩
        intro k m s hcode hD hA hI hw
        obtain ⟨G', hG', rfl⟩ := hD _ _ _ hj
        obtain ⟨kℓ, hkℓ, hJ⟩ := hw
        refine shuffle_ok hsh hcode.left hA hI fun s' ht hI' => ?_
        refine T.ev_jmp hu (hcode.right.head) hkℓ (hJ s' ?_ ?_ hI')
        · intro x r hx v hv
          exact ht x r (List.mem_append_left _ hx) v (hG' _ hv)
        · exact regsHold_of_zip has hlen fun x r hx v hv =>
            ht x r (List.mem_append_right _ hx) v hv
      · simp at hl
    · simp at hl
  | @Wf.ret _ _ _ _ G D vs₁ vs₂ hvs => by
    intro st code nv' nl' hl hG
    simp only [lowerE] at hl
    split at hl
    · rename_i hlen
      split at hl
      · rename_i c hsh
        simp only [Except.ok.injEq, Prod.mk.injEq] at hl
        obtain ⟨rfl, rfl, rfl⟩ := hl
        refine ⟨Nat.le_refl _, ?_⟩
        intro k m s hcode hD hA hI hw
        refine shuffle_ok hsh hcode.left hA hI fun s' ht hI' => ?_
        exact T.ev_ret hcode.right ⟨vs₁, m, hw, regsHold_of_zip hvs hlen ht, hI'⟩
      · simp at hl
    · simp at hl
  | .hlt => by
    intro st code nv' nl' hl hG
    simp only [lowerE, Except.ok.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl, rfl⟩ := hl
    exact ⟨Nat.le_refl _, fun _ _ _ _ _ _ _ hw => by simp [wp] at hw⟩
  | @Wf.letRecs _ _ _ _ G D sig b₁ b₂ k₁ k₂ hb hk => by
    intro st code nv' nl' hl hG
    simp only [lowerE] at hl
    split at hl
    · rename_i cr nv1 nl1 hlr
      obtain ⟨c', hl', rfl⟩ := prepend_ok hl
      have ihk := lowerE_correct hu (hk (labsJ H h Q F s₀ G sig (freshLabels sig st.nl))
        (freshLabels sig st.nl)) _ cr nv1 nl1 hlr hG
      have ihb := lowerBs_correct hu (hb (labsJ H h Q F s₀ G sig (freshLabels sig st.nl))
        (freshLabels sig st.nl)) _ nv1 nl1 c' nv' nl' hl'
        (fun p hp => Nat.lt_of_lt_of_le (hG p hp) ihk.1)
      refine ⟨Nat.le_trans ihk.1 ihb.1, ?_⟩
      intro k m s hcode hD hA hI hw
      have hD' := hD.group sig (freshLabels sig st.nl)
      exact ihk.2 k m s hcode.left hD' hA hI (hw _ (ihb.2 _ hcode.right hD'))
    · simp at hl
termination_by structural hwf

theorem lowerB_correct (hu : T.LabelsUnique H) {G : List (Val × Nat)} {D : List (LPair Cont NL)}
    {n : Nat} {b₁ : Block Val Cont n} {b₂ : Block Nat NL n} (hwf : WfB G D b₁ b₂) :
    ∀ (PL : List T.Reg) (st : St T) (code : List T.Dir) (nv' nl' : Nat),
    lowerB h b₂ PL st = .ok (code, nv', nl') →
    (∀ p ∈ G, p.2 < st.nv) →
    st.nv ≤ nv' ∧
    ∀ (k : Nat) (J : Cont n),
    InfixAt code (T.prog H) k →
    DOk H h Q F s₀ G D →
    (∀ as m, (∀ s, Agree G st.R s → RegsHold s PL (argsToList n as) → Inv F s₀ m s →
      T.Ev H (FnPost Q F s₀) k s) → J as m) →
    closedBlock Q b₁ J :=
  match hwf with
  | .body he => by
    intro PL st code nv' nl' hl hG
    simp only [lowerB] at hl
    have ih := lowerE_correct hu he st code nv' nl' hl hG
    refine ⟨ih.1, fun k J hc hD hJ => ?_⟩
    intro m hw
    exact hJ () m fun s hA _ hI => ih.2 k m s hc hD hA hI hw
  | @WfB.param _ _ _ _ G D n f₁ f₂ hf => by
    intro PL st code nv' nl' hl hG
    simp only [lowerB] at hl
    split at hl
    · simp at hl
    · rename_i r PL'
      have ih := fun v => lowerB_correct hu (hf v st.nv) PL' _ code nv' nl' hl (bound_cons hG v)
      refine ⟨by have := (ih 0).1; simp at this; omega, fun k J hc hD hJ => ?_⟩
      intro v
      refine (ih v).2 k _ hc (hD.mono fun p hp => List.mem_cons_of_mem _ hp)
        fun as m hev => hJ (v, as) m fun s hA hR hI => ?_
      cases hR with
      | cons hr hR => exact hev s (hA.bindN hG hr) hR hI
termination_by structural hwf

theorem lowerBs_correct (hu : T.LabelsUnique H) {G : List (Val × Nat)} {D : List (LPair Cont NL)}
    {sig : List Nat} {bs₁ : Blocks Val Cont sig} {bs₂ : Blocks Nat NL sig} (hwf : WfBs G D bs₁ bs₂) :
    ∀ (ls : Labels NL sig) (nv nl : Nat) (code : List T.Dir) (nv' nl' : Nat),
    lowerBs h bs₂ ls nv nl = .ok (code, nv', nl') →
    (∀ p ∈ G, p.2 < nv) →
    nv ≤ nv' ∧
    ∀ (k : Nat), InfixAt code (T.prog H) k →
    DOk H h Q F s₀ G D →
    closedBlocks Q bs₁ (labsJ H h Q F s₀ G sig ls) :=
  match hwf with
  | .nil => by
    intro ls nv nl code nv' nl' hl hG
    simp only [lowerBs, Except.ok.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl, rfl⟩ := hl
    exact ⟨Nat.le_refl _, fun _ _ _ => trivial⟩
  | .cons hb hbs => by
    intro ls nv nl code nv' nl' hl hG
    simp only [lowerBs] at hl
    split at hl
    · rename_i cb nv1 nl1 hlb
      obtain ⟨c', hl', rfl⟩ := prepend_ok hl
      have ihb := lowerB_correct hu hb _ _ cb nv1 nl1 hlb hG
      have ihs := lowerBs_correct hu hbs ls.2 _ _ c' nv' nl' hl'
        (fun p hp => Nat.lt_of_lt_of_le (hG p hp) ihb.1)
      refine ⟨Nat.le_trans ihb.1 ihs.1, fun k hc hD => ⟨?_, ihs.2 _ hc.right hD⟩⟩
      have hlab := hc.left.head
      exact ihb.2 (k + 1) _ hc.left.tail hD fun as m hev =>
        ⟨k, hlab, fun s hA hR hI => T.ev_label hlab (hev s hA hR hI)⟩
    · simp at hl
termination_by structural hwf
end

/-- Headline: a function is a block whose parameters arrive in `argRegs`. If the source block's
wp holds on the arguments, the lowered code reaches `FnPost`. -/
theorem lower_correct (hu : T.LabelsUnique H) {n : Nat} {b₁ : Block Val Cont n}
    {b₂ : Block Nat NL n} (hwf : WfB [] [] b₁ b₂) {code : List T.Dir} {nv' nl' : Nat}
    (hl : lowerB h b₂ T.argRegs ⟨0, 0, []⟩ = .ok (code, nv', nl')) :
    ∀ (k : Nat) (as : Args Val n) (m : Mem) (s : T.MData),
    InfixAt code (T.prog H) k → RegsHold s T.argRegs (argsToList n as) → Inv F s₀ m s →
    wpBlock Q b₁ as m → T.Ev H (FnPost Q F s₀) k s := by
  intro k as m s hc hR hI hw
  refine closedBlock_wpBlock b₁
    (fun as m => ∀ s, RegsHold s T.argRegs (argsToList n as) → Inv F s₀ m s →
      T.Ev H (FnPost Q F s₀) k s)
    ((lowerB_correct H h Q F s₀ hu hwf _ _ code nv' nl' hl (by simp)).2 k _ hc
      (fun _ _ _ hm => by simp at hm) fun as m hev s hR hI => hev s (by simp [Agree]) hR hI)
    as m hw s hR hI

end

#print axioms lower_correct

/-! ## Kernel-only `rfl` (from spike A `Core.lean`) -/

open Lean Elab Tactic Meta in
/-- Close `lhs = rhs` with `Eq.refl lhs` WITHOUT running the elaborator's `isDefEq`;
only the kernel checks it when the declaration is added. -/
elab "kernel_rfl" : tactic => do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let some (α, lhs, _) := tgt.eq?
    | throwError "kernel_rfl: goal is not an equality{indentExpr tgt}"
  let u ← getLevel α
  goal.assign (mkApp2 (mkConst ``Eq.refl [u]) α lhs)
  replaceMainGoal []

/-! ## Concrete toy instance (trivial semantics) and the even/odd group -/

namespace Toy

deriving instance Repr for Op

inductive Dir
  | label (s : String)
  | jmp (s : String)
  | mov (d r : Nat)
  | op (o : Op Nat) (d : Nat)
  | store (a v : Nat)
  | jz (r : Nat) (s : String)
  | ret
  deriving Repr

def toy : Target where
  Reg := Nat
  Dir := Dir
  MData := Unit
  get _ _ := 0
  mem _ _ := none
  alloc := [0, 1, 2, 3, 4, 5, 6, 7]
  scratch := [8]
  resRegs := [0]
  argRegs := [0]
  Host := Unit
  prog _ := []
  Ev _ _ _ _ := True
  label := Dir.label
  jmp := Dir.jmp
  movS d r := [Dir.mov d r]
  opS o d := [Dir.op o d]
  storeS a v := [Dir.store a v]
  jzS r l := [Dir.jz r l]
  retS := [Dir.ret]
  ev_label := by intros; trivial
  ev_jmp := by intros; trivial
  ev_mov := by intros; trivial
  ev_op := by intros; trivial
  ev_store := by intros; trivial
  ev_jz := by intros; trivial
  ev_ret := by intros; trivial

/-- Every variable in its own register; every label entered with `zero one m1` live in
`r1 r2 r3` and its parameter in `r4`. -/
def hints : Hints toy where
  dest v := some v
  entry _ := ⟨[(1, (1 : Nat)), (2, (2 : Nat)), (3, (3 : Nat))], [(4 : Nat)]⟩

def evenOdd (V : Type) (L : Nat → Type) : Block V L 1 :=
  .param fun n => .body <|
  .let_ (.const 0) fun zero =>
  .let_ (.const 1) fun one =>
  .let_ (.const (-1)) fun m1 =>
  .letRecs [1, 1]
    (fun (even, odd, ()) =>
      .cons (.param fun x => .body <|
        .jnz x (.let_ (.add x m1) fun x' => .jump odd (x', ())) (.ret [one])) <|
      .cons (.param fun x => .body <|
        .jnz x (.let_ (.add x m1) fun x' => .jump even (x', ())) (.ret [zero]))
      .nil)
    (fun (even, _, ()) => .jump even (n, ()))

open Dir in
/-- Expected output (from `#eval`). Labels are written `lname k` so that `rfl` never has to
compute with `String`. -/
def evenOddCode : List toy.Dir :=
  [op (.const 0) 1, op (.const 1) 2, op (.const (-1)) 3, mov 4 0, jmp (lname 0),
   label (lname 0), jz 4 (lname 2), op (.add 4 3) 5, mov 4 5, jmp (lname 1),
   label (lname 2), mov 0 2, ret,
   label (lname 1), jz 4 (lname 3), op (.add 4 3) 7, mov 4 7, jmp (lname 0),
   label (lname 3), mov 0 1, ret]

theorem evenOdd_lower :
    lowerB hints (evenOdd Nat NL) toy.argRegs ⟨0, 0, []⟩ = .ok (evenOddCode, 8, 4) := by
  rfl

theorem evenOdd_lower_kernel :
    lowerB hints (evenOdd Nat NL) toy.argRegs ⟨0, 0, []⟩ = .ok (evenOddCode, 8, 4) := by
  kernel_rfl

end Toy
end RegaSkel3
