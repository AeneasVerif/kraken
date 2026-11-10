module

/-
Rega skeleton, encoding E1: direct lowering from E1 PHOAS with `V := Nat` names, a symbolic
location relation `R : List (Name × Reg)`, untrusted hints, checked at jumps, against a MOCK
target signature. Purpose: test the proof shape of `lower_correct` (plan 2.2) before the real
IR (core C1) and Target (abi A0) exist.
-/
set_option autoImplicit false

@[expose] public section

namespace RegaSkel

abbrev Val := BitVec 64
abbrev Mem := BitVec 64 → Option Val

/-! ## E1 (copied, Op cut down) -/

inductive Op (V : Type) : Type
  | const (c : Val)
  | add (a b : V)
  | load (a : V)

inductive Expr (V L : Type) : Type
  | let_ (op : Op V) (k : V → Expr V L)
  | store (a v : V) (k : Expr V L)
  | jnz (c : V) (t e : Expr V L)
  | jump (j : L) (args : List V)
  | ret (vs : List V)
  | hlt
  | param (f : V → Expr V L)
  | label (f : L → Expr V L)
  | block (b rest : Expr V L)

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

abbrev Cont := List Val → Mem → Prop
abbrev Post := List Val → Mem → Prop

def upd (m : Mem) (a v : Val) : Mem := fun a' => if a' = a then some v else m a'

def wp (Q : Post) : Expr Val Cont → List Val → List Cont → Mem → Prop
  | .let_ op k, args, _, m => args = [] ∧ op.wp m (fun v m' => wp Q (k v) [] [] m')
  | .store a v k, args, _, m => args = [] ∧ (m a).isSome ∧ wp Q k [] [] (upd m a v)
  | .jnz c t e, args, _, m => args = [] ∧ (c ≠ 0 → wp Q t [] [] m) ∧ (c = 0 → wp Q e [] [] m)
  | .jump j as, args, _, m => args = [] ∧ j as m
  | .ret vs, args, _, m => args = [] ∧ Q vs m
  | .hlt, _, _, _ => False
  | .param _, [], _, _ => False
  | .param f, a :: as, _, m => wp Q (f a) as [] m
  | .label f, args, acc, m => args = [] ∧ ∀ J : Cont, wp Q (f J) [] (acc ++ [J]) m
  | .block b rest, args, acc, m =>
      args = [] ∧
      match acc with
      | [] => False
      | J :: acc' => (∀ as m', wp Q b as [] m' → J as m') → wp Q rest [] acc' m

inductive OpRel {V₁ V₂ : Type} (R : V₁ → V₂ → Prop) : Op V₁ → Op V₂ → Prop
  | const (c : Val) : OpRel R (.const c) (.const c)
  | add {a₁ b₁ a₂ b₂} : R a₁ a₂ → R b₁ b₂ → OpRel R (.add a₁ b₁) (.add a₂ b₂)
  | load {a₁ a₂} : R a₁ a₂ → OpRel R (.load a₁) (.load a₂)

inductive Forall₂ {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Forall₂ R [] []
  | cons {a b as bs} : R a b → Forall₂ R as bs → Forall₂ R (a :: as) (b :: bs)

inductive Wf {V₁ V₂ L₁ L₂ : Type} :
    List (V₁ × V₂) → List (L₁ × L₂) → Expr V₁ L₁ → Expr V₂ L₂ → Prop
  | let_ {G D op₁ op₂ k₁ k₂} : OpRel (fun a b => (a, b) ∈ G) op₁ op₂ →
      (∀ v₁ v₂, Wf ((v₁, v₂) :: G) D (k₁ v₁) (k₂ v₂)) → Wf G D (.let_ op₁ k₁) (.let_ op₂ k₂)
  | store {G D a₁ a₂ v₁ v₂ k₁ k₂} : (a₁, a₂) ∈ G → (v₁, v₂) ∈ G → Wf G D k₁ k₂ →
      Wf G D (.store a₁ v₁ k₁) (.store a₂ v₂ k₂)
  | jnz {G D c₁ c₂ t₁ t₂ e₁ e₂} : (c₁, c₂) ∈ G → Wf G D t₁ t₂ → Wf G D e₁ e₂ →
      Wf G D (.jnz c₁ t₁ e₁) (.jnz c₂ t₂ e₂)
  | jump {G D j₁ j₂ as₁ as₂} : (j₁, j₂) ∈ D → Forall₂ (fun a b => (a, b) ∈ G) as₁ as₂ →
      Wf G D (.jump j₁ as₁) (.jump j₂ as₂)
  | ret {G D vs₁ vs₂} : Forall₂ (fun a b => (a, b) ∈ G) vs₁ vs₂ →
      Wf G D (.ret vs₁) (.ret vs₂)
  | hlt {G D} : Wf G D .hlt .hlt
  | param {G D f₁ f₂} : (∀ v₁ v₂, Wf ((v₁, v₂) :: G) D (f₁ v₁) (f₂ v₂)) →
      Wf G D (.param f₁) (.param f₂)
  | label {G D f₁ f₂} : (∀ j₁ j₂, Wf G ((j₁, j₂) :: D) (f₁ j₁) (f₂ j₂)) →
      Wf G D (.label f₁) (.label f₂)
  | block {G D b₁ b₂ r₁ r₂} : Wf G D b₁ b₂ → Wf G D r₁ r₂ →
      Wf G D (.block b₁ r₁) (.block b₂ r₂)

/-! ## Code placement -/

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

/-! ## Mock target -/

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

structure St where
  nv : Nat
  nl : Nat
  R : Sym T
  PL : List T.Reg
  pend : List Nat

def lname (n : Nat) : String := "L" ++ toString n

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

def lower (h : Hints T) : Expr Nat Nat → St T → Except String (List T.Dir × Nat × Nat)
  | .param f, st =>
    match st.PL with
    | [] => .error "param"
    | r :: PL => lower h (f st.nv) ⟨st.nv + 1, st.nl, bindN st.nv r st.R, PL, []⟩
  | .let_ op k, st =>
    match h.dest st.nv, op.traverse (lookup st.R) with
    | some d, some o =>
      if d ∈ T.alloc then
        prepend (T.opS o d)
          (lower h (k st.nv) ⟨st.nv + 1, st.nl, bindN st.nv d (clob (some d) st.R), [], []⟩)
      else .error "alloc"
    | _, _ => .error "let"
  | .store a v k, st =>
    match lookup st.R a, lookup st.R v with
    | some ra, some rv => prepend (T.storeS ra rv) (lower h k ⟨st.nv, st.nl, clob none st.R, [], []⟩)
    | _, _ => .error "store"
  | .jnz c t e, st =>
    match lookup st.R c with
    | some rc =>
      match lower h t ⟨st.nv, st.nl + 1, clob none st.R, [], []⟩ with
      | .ok (ct, nv1, nl1) =>
        prepend (T.jzS rc (lname st.nl) ++ ct ++ [T.label (lname st.nl)])
          (lower h e ⟨nv1, nl1, clob none st.R, [], []⟩)
      | .error e => .error e
    | none => .error "jnz"
  | .jump j as, st =>
    let E := h.entry j
    if as.length = E.ploc.length then
      match shuffle st.R (E.live ++ as.zip E.ploc) with
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
  | .label f, st => lower h (f st.nl) ⟨st.nv, st.nl + 1, st.R, st.PL, st.pend ++ [st.nl]⟩
  | .block b rest, st =>
    match st.pend with
    | [] => .error "block"
    | ℓ :: pend =>
      match lower h rest ⟨st.nv, st.nl, st.R, st.PL, pend⟩ with
      | .ok (cr, nv1, nl1) =>
        prepend (cr ++ [T.label (lname ℓ)])
          (lower h b ⟨nv1, nl1, (h.entry ℓ).live, (h.entry ℓ).ploc, []⟩)
      | .error e => .error e

/-! ## Invariants -/

def Agree (G : List (Val × Nat)) (R : Sym T) (s : T.MData) : Prop :=
  ∀ x r, (x, r) ∈ R → ∀ v, (v, x) ∈ G → T.get s r = v

def RegsHold (s : T.MData) (rs : List T.Reg) (vs : List Val) : Prop :=
  Forall₂ (fun r v => T.get s r = v) rs vs

/-- Frame invariant: the source memory is split off a fixed frame `F`; registers that are
neither allocatable nor scratch keep their entry values. -/
def Inv (F : Mem) (s₀ : T.MData) (m : Mem) (s : T.MData) : Prop :=
  (∀ a, T.mem s a = (m a).or (F a)) ∧ (∀ a, m a = none ∨ F a = none) ∧
  (∀ r, r ∉ T.alloc → r ∉ T.scratch → T.get s r = T.get s₀ r)

def FnPost (Q : Post) (F : Mem) (s₀ : T.MData) : T.MData → Prop := fun s =>
  ∃ rets m', Q rets m' ∧ RegsHold s T.resRegs rets ∧ Inv F s₀ m' s

section
variable (H : T.Host) (h : Hints T) (Q : Post) (F : Mem) (s₀ : T.MData)

/-- The join-point predicate: the source continuation chosen for label `ℓ`. -/
def LabJ (G : List (Val × Nat)) (ℓ : Nat) : Cont := fun as m =>
  ∃ k, (T.prog H)[k]? = some (T.label (lname ℓ)) ∧
    ∀ s, Agree G (h.entry ℓ).live s → RegsHold s (h.entry ℓ).ploc as → Inv F s₀ m s →
      T.Ev H (FnPost Q F s₀) k s

def DOk (G : List (Val × Nat)) (D : List (Cont × Nat)) : Prop :=
  ∀ J ℓ, (J, ℓ) ∈ D → ∃ G', (∀ p ∈ G', p ∈ G) ∧ J = LabJ H h Q F s₀ G' ℓ

end

/-! ## Lemmas about the symbolic state -/

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
  simp only [RegaSkel.clob, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hx
  rw [hs r hx.2.1 hx.2.2]; exact hA _ _ hx.1 _ hv

theorem Agree.bindN {G : List (Val × Nat)} {R : Sym T} {s : T.MData} {x : Nat} {r : T.Reg}
    {v : Val} (hA : Agree G R s) (hx : ∀ p ∈ G, p.2 < x) (hr : T.get s r = v) :
    Agree ((v, x) :: G) (bindN x r R) s := by
  intro y r' hy w hw
  simp only [RegaSkel.bindN, List.mem_cons, List.mem_filter, Prod.mk.injEq, bne_iff_ne, ne_eq] at hy hw
  rcases hy with ⟨rfl, rfl⟩ | ⟨hy, hne⟩
  · rcases hw with ⟨rfl, -⟩ | hw
    · exact hr
    · exact absurd (hx _ hw) (by simp)
  · rcases hw with ⟨rfl, rfl⟩ | hw
    · exact absurd rfl hne
    · exact hA _ _ hy _ hw

theorem Agree.mono {G G' : List (Val × Nat)} {R : Sym T} {s : T.MData} (hA : Agree G R s)
    (hG : ∀ p ∈ G', p ∈ G) : Agree G' R s :=
  fun x r hx v hv => hA x r hx v (hG _ hv)

theorem Agree.movSym {G : List (Val × Nat)} {R : Sym T} {s s' : T.MData} {d r : T.Reg}
    (hA : Agree G R s) (hs : ∀ r', r' ≠ d → T.get s' r' = T.get s r')
    (hd : T.get s' d = T.get s r) : Agree G (movSym d r R) s' := by
  intro x q hx v hv
  unfold RegaSkel.movSym at hx
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

/-! ## Moves -/

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

theorem Forall₂.append_single {α β : Type} {R : α → β → Prop} {a : α} {b : β} :
    ∀ {as : List α} {bs : List β}, Forall₂ R as bs → R a b → Forall₂ R (as ++ [a]) (bs ++ [b])
  | _, _, .nil, h => .cons h .nil
  | _, _, .cons h1 h2, h => .cons h1 (h2.append_single h)

/-! ## The main lemma -/

section
variable (H : T.Host) (h : Hints T) (Q : Post) (F : Mem)
  (s₀ : T.MData)

theorem lower_correct (hu : T.LabelsUnique H) {G : List (Val × Nat)} {D : List (Cont × Nat)}
    {e₁ : Expr Val Cont} {e₂ : Expr Nat Nat} (hwf : Wf G D e₁ e₂) :
    ∀ (st : St T) (code : List T.Dir) (nv' nl' : Nat),
    lower h e₂ st = .ok (code, nv', nl') →
    (∀ p ∈ G, p.2 < st.nv) →
    st.nv ≤ nv' ∧
    ∀ (k : Nat) (args : List Val) (acc : List Cont) (m : Mem) (s : T.MData),
    InfixAt code (T.prog H) k →
    DOk H h Q F s₀ G D →
    Forall₂ (fun J ℓ => J = LabJ H h Q F s₀ G ℓ) acc st.pend →
    Agree G st.R s → RegsHold s st.PL args → Inv F s₀ m s →
    wp Q e₁ args acc m → T.Ev H (FnPost Q F s₀) k s := by
  induction hwf with
  | @let_ G D op₁ op₂ k₁ k₂ hop _ ih =>
    intro st code nv' nl' hl hG
    simp only [lower] at hl
    split at hl
    · rename_i d o hd ho
      split at hl
      · rename_i hda
        obtain ⟨c', hl', rfl⟩ := prepend_ok hl
        have ih' := fun v => ih v st.nv _ c' nv' nl' hl'
        refine ⟨by have := (ih' 0 (by
          intro p hp; simp at hp; rcases hp with rfl | hp
          · simp
          · have := hG _ hp; simp; omega)).1; simp at this; omega, ?_⟩
        intro k args acc m s hc hD hP hA hR hI hw
        simp only [wp] at hw
        obtain ⟨rfl, hw⟩ := hw
        refine T.ev_op o hc.left ?_
        rw [traverse_ok hA hop ho]
        refine Op.wp_sub (fun a v e => ?_) (P := fun v => ∀ s', _ → _ → _ → _)
          (Op.wp_imp (fun v m' hv => ?_) (Op.wp_mem hw))
        · rw [hI.1 a, e]; rfl
        · obtain ⟨rfl, hv⟩ := hv
          intro s' hs' hd' hm'
          have hG' : ∀ p ∈ (v, st.nv) :: G, p.2 < st.nv + 1 := by
            intro p hp; simp at hp; rcases hp with rfl | hp
            · simp
            · have := hG _ hp; omega
          refine (ih' v hG').2 _ [] [] _ s' hc.right ?_ .nil ?_ .nil ?_ hv
          · intro J ℓ hJ
            obtain ⟨G', hG'', rfl⟩ := hD J ℓ hJ
            exact ⟨G', fun p hp => List.mem_cons_of_mem _ (hG'' p hp), rfl⟩
          · exact (hA.clob (fun r h1 h2 => hs' r (fun e => h1 (by rw [e])) h2)).bindN
              (fun p hp => hG p hp) hd'
          · exact hI.regs hm' (some d) (fun r h1 h2 => hs' r (fun e => h1 (by rw [e])) h2)
              (fun r e => by cases e; exact hda)
      · simp at hl
    · simp at hl
  | @store G D a₁ a₂ v₁ v₂ k₁ k₂ ha hv _ ih =>
    intro st code nv' nl' hl hG
    simp only [lower] at hl
    split at hl
    · rename_i ra rv hra hrv
      obtain ⟨c', hl', rfl⟩ := prepend_ok hl
      have ih' := ih _ c' nv' nl' hl' hG
      refine ⟨ih'.1, ?_⟩
      intro k args acc m s hc hD hP hA hR hI hw
      simp only [wp] at hw
      obtain ⟨rfl, hsome, hw⟩ := hw
      have e1 := hA _ _ (lookup_mem hra) _ ha
      have e2 := hA _ _ (lookup_mem hrv) _ hv
      refine T.ev_store hc.left (by rw [e1]; exact hI.load_isSome hsome) fun s' hs' hm' => ?_
      rw [e1, e2] at hm'
      exact ih'.2 _ [] [] _ s' hc.right hD .nil (hA.clob (fun r _ h2 => hs' r h2)) .nil
        (hI.store hsome hm' hs') hw
    · simp at hl
  | @jnz G D c₁ c₂ t₁ t₂ e₁ e₂ hc _ _ iht ihe =>
    intro st code nv' nl' hl hG
    simp only [lower] at hl
    split at hl
    · rename_i rc hrc
      split at hl
      · rename_i ct nv1 nl1 hlt
        obtain ⟨c', hl', rfl⟩ := prepend_ok hl
        have iht' := iht _ ct nv1 nl1 hlt hG
        have ihe' := ihe _ c' nv' nl' hl' (fun p hp => by have := hG p hp; simp at iht' ⊢; omega)
        refine ⟨by simp at iht' ihe'; omega, ?_⟩
        intro k args acc m s hcode hD hP hA hR hI hw
        simp only [wp] at hw
        obtain ⟨rfl, hwt, hwe⟩ := hw
        have e1 := hA _ _ (lookup_mem hrc) _ hc
        have hcode1 := hcode.left
        have hlab : (T.prog H)[k + (T.jzS rc (lname st.nl)).length + ct.length]? =
            some (T.label (lname st.nl)) := by
          have := hcode1.right (a := T.jzS rc (lname st.nl) ++ ct)
          simpa [Nat.add_assoc] using this.head
        refine T.ev_jz hu hcode1.left.left hlab fun s' hs' hm' => ⟨fun h0 => ?_, fun h0 => ?_⟩
        · refine T.ev_label hlab ?_
          have := ihe'.2 _ [] [] m s' hcode.right hD .nil (hA.clob (fun r _ h2 => hs' r h2)) .nil
            (hI.regs hm' none (fun r _ h2 => hs' r h2) (fun _ e => by cases e))
            (hwe (by rw [← e1]; exact h0))
          simpa [Nat.add_assoc] using this
        · exact iht'.2 _ [] [] m s' hcode1.left.right hD .nil
            (hA.clob (fun r _ h2 => hs' r h2)) .nil
            (hI.regs hm' none (fun r _ h2 => hs' r h2) (fun _ e => by cases e))
            (hwt (by rw [← e1]; exact h0))
      · simp at hl
    · simp at hl
  | @jump G D j₁ j₂ as₁ as₂ hj has =>
    intro st code nv' nl' hl hG
    simp only [lower] at hl
    split at hl
    · rename_i hlen
      split at hl
      · rename_i c hsh
        simp only [Except.ok.injEq, Prod.mk.injEq] at hl
        obtain ⟨rfl, rfl, rfl⟩ := hl
        refine ⟨Nat.le_refl _, ?_⟩
        intro k args acc m s hcode hD hP hA hR hI hw
        simp only [wp] at hw
        obtain ⟨rfl, hw⟩ := hw
        obtain ⟨G', hG', rfl⟩ := hD _ _ hj
        obtain ⟨kℓ, hkℓ, hJ⟩ := hw
        refine shuffle_ok hsh hcode.left hA hI fun s' ht hI' => ?_
        refine T.ev_jmp hu (hcode.right.head) hkℓ (hJ s' ?_ ?_ hI')
        · intro x r hx v hv
          exact ht x r (List.mem_append_left _ hx) v (hG' _ hv)
        · exact regsHold_of_zip has hlen fun x r hx v hv =>
            ht x r (List.mem_append_right _ hx) v hv
      · simp at hl
    · simp at hl
  | @ret G D vs₁ vs₂ hvs =>
    intro st code nv' nl' hl hG
    simp only [lower] at hl
    split at hl
    · rename_i hlen
      split at hl
      · rename_i c hsh
        simp only [Except.ok.injEq, Prod.mk.injEq] at hl
        obtain ⟨rfl, rfl, rfl⟩ := hl
        refine ⟨Nat.le_refl _, ?_⟩
        intro k args acc m s hcode hD hP hA hR hI hw
        simp only [wp] at hw
        obtain ⟨rfl, hw⟩ := hw
        refine shuffle_ok hsh hcode.left hA hI fun s' ht hI' => ?_
        exact T.ev_ret hcode.right ⟨vs₁, m, hw, regsHold_of_zip hvs hlen ht, hI'⟩
      · simp at hl
    · simp at hl
  | hlt =>
    intro st code nv' nl' hl hG
    simp only [lower, Except.ok.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl, rfl⟩ := hl
    exact ⟨Nat.le_refl _, fun _ _ _ _ _ _ _ _ _ _ _ hw => by simp [wp] at hw⟩
  | @param G D f₁ f₂ _ ih =>
    intro st code nv' nl' hl hG
    simp only [lower] at hl
    split at hl
    · simp at hl
    · rename_i r PL hPL
      have hG' : ∀ v, ∀ p ∈ (v, st.nv) :: G, p.2 < st.nv + 1 := by
        intro v p hp; simp at hp; rcases hp with rfl | hp
        · simp
        · have := hG _ hp; omega
      refine ⟨by have := (ih 0 st.nv _ code nv' nl' hl (hG' 0)).1; simp at this; omega, ?_⟩
      intro k args acc m s hcode hD hP hA hR hI hw
      rw [hPL] at hR
      cases hR with
      | @cons _ a _ as hra hR =>
        simp only [wp] at hw
        refine (ih a st.nv _ code nv' nl' hl (hG' a)).2 k as [] m s hcode ?_ .nil
          (hA.bindN hG hra) hR hI hw
        intro J ℓ hJ
        obtain ⟨G', hG'', rfl⟩ := hD J ℓ hJ
        exact ⟨G', fun p hp => List.mem_cons_of_mem _ (hG'' p hp), rfl⟩
  | @label G D f₁ f₂ _ ih =>
    intro st code nv' nl' hl hG
    simp only [lower] at hl
    let J := LabJ H h Q F s₀ G st.nl
    have ih' := ih J st.nl _ code nv' nl' hl hG
    refine ⟨ih'.1, ?_⟩
    intro k args acc m s hcode hD hP hA hR hI hw
    simp only [wp] at hw
    obtain ⟨rfl, hw⟩ := hw
    refine ih'.2 k [] (acc ++ [J]) m s hcode ?_ ?_ hA hR hI (hw J)
    · intro J' ℓ hJ'
      simp only [List.mem_cons, Prod.mk.injEq] at hJ'
      rcases hJ' with ⟨rfl, rfl⟩ | hJ'
      · exact ⟨G, fun p hp => hp, rfl⟩
      · exact hD J' ℓ hJ'
    · exact hP.append_single rfl
  | @block G D b₁ b₂ r₁ r₂ _ _ ihb ihr =>
    intro st code nv' nl' hl hG
    simp only [lower] at hl
    split at hl
    · simp at hl
    · rename_i ℓ pend hpend
      split at hl
      · rename_i cr nv1 nl1 hlr
        obtain ⟨c', hl', rfl⟩ := prepend_ok hl
        have ihr' := ihr _ cr nv1 nl1 hlr hG
        have ihb' := ihb _ c' nv' nl' hl' (fun p hp => by have := hG p hp; simp at ihr' ⊢; omega)
        refine ⟨by simp at ihr' ihb'; omega, ?_⟩
        intro k args acc m s hcode hD hP hA hR hI hw
        simp only [wp] at hw
        obtain ⟨rfl, hw⟩ := hw
        rw [hpend] at hP
        cases hP with
        | @cons J _ acc' _ hJ hP =>
          simp only at hw
          have hlab : (T.prog H)[k + cr.length]? = some (T.label (lname ℓ)) :=
            hcode.left.right.head
          refine ihr'.2 k [] acc' m s hcode.left.left hD hP hA hR hI (hw ?_)
          intro as m' hb
          rw [hJ]
          refine ⟨k + cr.length, hlab, fun s' hA' hR' hI' => T.ev_label hlab ?_⟩
          have := ihb'.2 _ as [] m' s' hcode.right hD .nil hA' hR' hI' hb
          simpa [Nat.add_assoc] using this
      · simp at hl

end

#print axioms lower_correct

end RegaSkel
