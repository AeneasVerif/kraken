module

public import LeanQbe.Rega
public import LeanQbe.Wf
public import LeanQbe.AbiLemmas

/-!
# Correctness of `Rega.lower`

`lower_correct`: if the source term `e₁ : Expr Val Cont` and the name term `e₂ : Expr Nat Nat` are
related by `Wf G D`, `lower` succeeds on `e₂` with code placed at index `k` of the host, and the
machine state agrees with the symbolic register file, then the source `wp` implies that the machine
eventually reaches `post`. Generic in the `Target`.

The proof is one induction on `Wf` (plan section 2.2):

* `Agree G R s`: every register entry of `R` holds the value `G` gives its name.
* A join point `ℓ` is instantiated with `LabJ G ℓ`: "label `ℓ` is at some index `k`, and from every
  state agreeing with `ℓ`'s entry map, the machine reaches `post` from `k`". The `label` case picks
  this `J` for the source's `∀ J`; the `block` case proves `J` closed under the block body at its
  own index; the `jump` case uses `J` after the checked moves.
* No liveness, no dominance, no fixpoint: a wrong hint makes `lower` fail.

Two things are hypotheses of the main lemma and discharged once per function (`lowerFn_correct`):
`hret`, what `ret` must establish, and the memory facts `hload`, `hstoreOk`, `hstore` about the
frame `F` (separation logic on Kraken's `Mem 64`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe
namespace Rega

variable {T : Target}

/-! ## Agreement of the symbolic register file -/

/-- Every entry of `R` holds the value of its name (or its constant) in `s`. -/
def Agree (G : List (Val × Nat)) (R : SymRegs T.toIsa) (s : T.MData) : Prop :=
  ∀ a r, (a, r) ∈ R → ∀ a₁, ArgRel G a₁ a → T.get s r = a₁.val

theorem lookup_mem {I : Isa} {R : SymRegs I} {x : Nat} {r : I.Reg} (h : lookup R x = some r) :
    (.var x, r) ∈ R := by
  simp only [lookup, Option.map_eq_some_iff] at h
  obtain ⟨⟨y, r'⟩, hp, rfl⟩ := h
  have := List.mem_of_find?_eq_some hp
  have hx := List.find?_some hp
  simp only [beq_iff_eq] at hx
  subst hx; exact this

theorem argReg_ok {G : List (Val × Nat)} {R : SymRegs T.toIsa} {s : T.MData} (hA : Agree G R s)
    {a₁ : Arg Val} {a : Arg Nat} (hr : ArgRel G a₁ a) {a' : Arg T.Reg} (h : argReg R a = some a') :
    a'.map (T.get s) = a₁ ∧ ∀ r, r ∈ a'.vars → r ∉ T.scratch := by
  cases hr with
  | @var v x hvx =>
    simp only [argReg] at h
    split at h
    · rename_i r hr
      split at h
      · simp at h
      · rename_i hs
        simp only [Option.some.injEq] at h; subst h
        refine ⟨?_, fun r' hr' => ?_⟩
        · simp only [Arg.map]; rw [hA _ _ (lookup_mem hr) _ (.var hvx)]; rfl
        · simp only [Arg.vars, List.mem_singleton] at hr'; subst hr'; exact hs
    · simp at h
  | imm c =>
    simp only [argReg, Option.some.injEq] at h; subst h
    exact ⟨rfl, fun r hr => by simp [Arg.vars] at hr⟩

theorem opRegs_ok {G : List (Val × Nat)} {R : SymRegs T.toIsa} {s : T.MData} (hA : Agree G R s)
    {op₁ : Op Val} {op₂ : Op Nat} (hr : OpRel G op₁ op₂) {o : Op T.Reg}
    (h : opRegs R op₂ = some o) : o.map (T.get s) = op₁ ∧ ∀ r, r ∈ o.vars → r ∉ T.scratch := by
  cases hr with
  | bin k o' ha hb =>
    simp only [opRegs] at h
    split at h
    · rename_i a' b' ha' hb'
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨e1, s1⟩ := argReg_ok hA ha ha'
      obtain ⟨e2, s2⟩ := argReg_ok hA hb hb'
      refine ⟨by simp only [Op.map, e1, e2], fun r hr => ?_⟩
      simp only [Op.vars, List.mem_append] at hr
      exact hr.elim (s1 r) (s2 r)
    · simp at h
  | cmp k o' ha hb =>
    simp only [opRegs] at h
    split at h
    · rename_i a' b' ha' hb'
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨e1, s1⟩ := argReg_ok hA ha ha'
      obtain ⟨e2, s2⟩ := argReg_ok hA hb hb'
      refine ⟨by simp only [Op.map, e1, e2], fun r hr => ?_⟩
      simp only [Op.vars, List.mem_append] at hr
      exact hr.elim (s1 r) (s2 r)
    · simp at h
  | ext k sz sg ha =>
    simp only [opRegs] at h
    split at h
    · rename_i a' ha'
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨e1, s1⟩ := argReg_ok hA ha ha'
      exact ⟨by simp only [Op.map, e1], fun r hr => s1 r (by simpa [Op.vars] using hr)⟩
    · simp at h
  | copy k ha =>
    simp only [opRegs] at h
    split at h
    · rename_i a' ha'
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨e1, s1⟩ := argReg_ok hA ha ha'
      exact ⟨by simp only [Op.map, e1], fun r hr => s1 r (by simpa [Op.vars] using hr)⟩
    · simp at h

theorem Agree.clob {G : List (Val × Nat)} {R : SymRegs T.toIsa} {s s' : T.MData}
    {d : Option T.Reg} (hA : Agree G R s)
    (hs : ∀ r, some r ≠ d → r ∉ T.scratch → T.get s' r = T.get s r) :
    Agree G (Rega.clob d R) s' := by
  intro a r hx a₁ hv
  simp only [Rega.clob, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hx
  rw [hs r hx.2.1 hx.2.2]; exact hA _ _ hx.1 _ hv

theorem _root_.LeanQbe.ArgRel.mono {G G' : List (Val × Nat)} (hG : ∀ p ∈ G, p ∈ G') {a₁ : Arg Val}
    {a : Arg Nat} (h : ArgRel G a₁ a) : ArgRel G' a₁ a := by
  cases h with
  | var h => exact .var (hG _ h)
  | imm c => exact .imm c

theorem _root_.LeanQbe.ArgRel.uncons {G : List (Val × Nat)} {v : Val} {x : Nat} {a₁ : Arg Val} {a : Arg Nat}
    (h : ArgRel ((v, x) :: G) a₁ a) (hne : a ≠ .var x) : ArgRel G a₁ a := by
  cases h with
  | @var v₁ y hy =>
    simp only [List.mem_cons, Prod.mk.injEq] at hy
    rcases hy with ⟨-, rfl⟩ | hy
    · exact absurd rfl hne
    · exact .var hy
  | imm c => exact .imm c

theorem Agree.bindN {G : List (Val × Nat)} {R : SymRegs T.toIsa} {s : T.MData} {x : Nat}
    {r : T.Reg} {v : Val} (hA : Agree G R s) (hx : ∀ p ∈ G, p.2 < x) (hr : T.get s r = v) :
    Agree ((v, x) :: G) (Rega.bindN x r R) s := by
  intro a r' hy a₁ hw
  simp only [Rega.bindN, List.mem_cons, List.mem_filter, Prod.mk.injEq, bne_iff_ne,
    ne_eq] at hy
  rcases hy with ⟨rfl, rfl⟩ | ⟨hy, hne⟩
  · cases hw with
    | @var v₁ _ hy =>
      simp only [List.mem_cons, Prod.mk.injEq] at hy
      rcases hy with ⟨rfl, -⟩ | hy
      · exact hr
      · exact absurd (hx _ hy) (by simp)
  · exact hA _ _ hy _ (hw.uncons hne)

theorem Agree.mono {G G' : List (Val × Nat)} {R : SymRegs T.toIsa} {s : T.MData}
    (hA : Agree G R s) (hG : ∀ p ∈ G', p ∈ G) : Agree G' R s :=
  fun a r hx a₁ hv => hA a r hx a₁ (hv.mono hG)

theorem Agree.movSym_var {G : List (Val × Nat)} {R : SymRegs T.toIsa} {s s' : T.MData}
    {d r : T.Reg} (hA : Agree G R s) (hs : ∀ r', r' ∉ [d] → T.get s' r' = T.get s r')
    (hd : T.get s' d = T.get s r) : Agree G (movSym (d, .var r) R) s' := by
  intro a q hx a₁ hv
  simp only [movSym] at hx
  split at hx
  · rename_i hdr
    subst hdr
    by_cases hq : q = d
    · subst hq; rw [hd]; exact hA _ _ hx _ hv
    · rw [hs q (by simpa using hq)]; exact hA _ _ hx _ hv
  · simp only [List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq] at hx
    rcases hx with ⟨⟨y, q'⟩, ⟨hy, rfl⟩, he⟩ | ⟨hx, hne⟩
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [hd]; exact hA _ _ hy _ hv
    · rw [hs q (by simpa using hne)]; exact hA _ _ hx _ hv

theorem Agree.movSym_imm {G : List (Val × Nat)} {R : SymRegs T.toIsa} {s s' : T.MData}
    {d : T.Reg} {c : Val} (hA : Agree G R s)
    (hs : ∀ r', r' ∉ d :: T.scratch → T.get s' r' = T.get s r') (hd : T.get s' d = c) :
    Agree G (movSym (d, .imm c) R) s' := by
  intro a q hx a₁ hv
  simp only [movSym, List.mem_cons, Prod.mk.injEq] at hx
  rcases hx with ⟨rfl, rfl⟩ | hx
  · cases hv with
    | imm c => exact hd
  · refine (hA.clob (d := some d) (fun r h1 h2 => hs r ?_)) _ _ hx _ hv
    simp only [List.mem_cons, not_or]
    exact ⟨fun e => h1 (by rw [e]), h2⟩

/-! ## The frame invariant -/

/-- Registers that are neither allocatable nor scratch keep their entry values. -/
def Keep (s₀ s : T.MData) : Prop :=
  ∀ r, r ∉ T.allocatable → r ∉ T.scratch → T.get s r = T.get s₀ r

/-- The machine memory is the source memory `m` next to the frame `F`, and `Keep`. -/
def Inv (F : Mem 64 → Prop) (s₀ : T.MData) (m : Mem 64) (s : T.MData) : Prop :=
  (T.mem s =⋆ Eq m ⋆ F) ∧ Keep s₀ s

theorem Inv.regs {F : Mem 64 → Prop} {s₀ s s' : T.MData} {m : Mem 64} (hI : Inv F s₀ m s)
    (hm : T.mem s' = T.mem s)
    (hs : ∀ r, r ∉ T.allocatable → r ∉ T.scratch → T.get s' r = T.get s r) : Inv F s₀ m s' :=
  ⟨hm ▸ hI.1, fun r h1 h2 => (hs r h1 h2).trans (hI.2 r h1 h2)⟩

/-- Writing an allocatable register `d` and the scratch registers preserves `Keep`. -/
theorem keeps_dest {s s' : T.MData} {d : T.Reg} (hd : d ∈ T.allocatable ∨ d ∈ T.scratch)
    (hs : ∀ r, r ∉ d :: T.scratch → T.get s' r = T.get s r) :
    ∀ r, r ∉ T.allocatable → r ∉ T.scratch → T.get s' r = T.get s r := by
  intro r h1 h2
  refine hs r ?_
  simp only [List.mem_cons, not_or]
  exact ⟨fun e => hd.elim (fun h => h1 (e ▸ h)) (fun h => h2 (e ▸ h)), h2⟩

theorem keeps_dest' {s s' : T.MData} {d : T.Reg}
    (hs : ∀ r, r ∉ d :: T.scratch → T.get s' r = T.get s r) :
    ∀ r, some r ≠ some d → r ∉ T.scratch → T.get s' r = T.get s r := by
  intro r h1 h2
  refine hs r ?_
  simp only [List.mem_cons, not_or]
  exact ⟨fun e => h1 (by rw [e]), h2⟩

/-! ## Labels -/

theorem labelAddr_of_unique {h : T.Host} (hu : T.LabelsUnique h) {j : Nat} {l : String}
    (hj : (T.prog h)[j]? = some (T.label l)) : T.labelAddr h l = T.addrOf h j :=
  T.labelAddr_eq hj fun j' hj' e => by have := hu _ _ _ e hj; omega

/-! ## Moves -/

section
variable {h : T.Host} {post : T.State → Prop} {F : Mem 64 → Prop} {s₀ : T.MData}

theorem moves_ok {G : List (Val × Nat)} {m : Mem 64} :
    ∀ (mvs : List (Move T.toIsa)) (R R' : SymRegs T.toIsa) (k : Nat) (s : T.MData),
    execMoves mvs R = some R' → (movesCode mvs).IsInfixAt (T.prog h) k →
    Agree G R s → Inv F s₀ m s →
    (∀ s', Agree G R' s' → Inv F s₀ m s' → T.Run h (k + (movesCode mvs).length) s' post) →
    T.Run h k s post
  | [], R, R', k, s, he, _, hA, hI, kont => by
    simp only [execMoves, Option.some.injEq] at he; subst he
    simpa [movesCode] using kont s hA hI
  | mv :: mvs, R, R', k, s, he, hc, hA, hI, kont => by
    simp only [execMoves] at he
    split at he
    · rename_i hd
      simp only [movesCode] at hc
      have hlen : ∀ s', T.Run h (k + (movesCode (mv :: mvs)).length) s' post →
          T.Run h (k + mv.code.length + (movesCode mvs).length) s' post := by
        intro s' hr; simpa [movesCode, Nat.add_assoc] using hr
      obtain ⟨d, src⟩ := mv
      cases src with
      | var r =>
        refine T.mov_spec (hc.append).1 fun s1 hd1 hs1 hm1 => ?_
        have hs1' : ∀ r', r' ∉ T.allocatable → r' ∉ T.scratch → T.get s1 r' = T.get s r' :=
          fun r' h1 h2 => hs1 r' (by
            simp only [List.mem_singleton]
            exact fun e => hd.elim (fun h => h1 (e ▸ h)) (fun h => h2 (e ▸ h)))
        exact moves_ok mvs _ R' _ s1 he (hc.append).2 (hA.movSym_var hs1 hd1)
          (hI.regs hm1 hs1') fun s2 hA2 hI2 => hlen s2 (kont s2 hA2 hI2)
      | imm c =>
        refine T.movi_spec (hc.append).1 fun s1 hd1 hs1 hm1 => ?_
        exact moves_ok mvs _ R' _ s1 he (hc.append).2 (hA.movSym_imm hs1 hd1)
          (hI.regs hm1 (keeps_dest hd hs1)) fun s2 hA2 hI2 => hlen s2 (kont s2 hA2 hI2)
    · simp at he

/-- Every target `(a, r)` holds after a successful `shuffle`. -/
def Holds (G : List (Val × Nat)) (tgts : SymRegs T.toIsa) (s : T.MData) : Prop :=
  ∀ a r, (a, r) ∈ tgts → ∀ a₁, ArgRel G a₁ a → T.get s r = a₁.val

theorem shuffle_ok {G : List (Val × Nat)} {m : Mem 64} {R tgts : SymRegs T.toIsa}
    {c : List T.Directive} {k : Nat} {s : T.MData}
    (hs : shuffle R tgts = some c) (hc : c.IsInfixAt (T.prog h) k)
    (hA : Agree G R s) (hI : Inv F s₀ m s)
    (kont : ∀ s', Holds G tgts s' → Inv F s₀ m s' → T.Run h (k + c.length) s' post) :
    T.Run h k s post := by
  unfold shuffle at hs
  dsimp only at hs
  split at hs
  · rename_i R' hR'
    split at hs
    · rename_i hall
      simp only [Option.some.injEq] at hs; subst hs
      refine moves_ok _ R R' k s hR' hc hA hI fun s' hA' hI' =>
        kont s' (fun a r hx a₁ hv => ?_) hI'
      simp only [List.all_eq_true, decide_eq_true_eq] at hall
      exact hA' a r (hall _ hx) a₁ hv
    · simp at hs
  · simp at hs

end

theorem valsIn_of_holds {G : List (Val × Nat)} {s : T.MData} :
    ∀ {as₁ : List (Arg Val)} {as : List (Arg Nat)} {rs : List T.Reg},
    Forall₂ (ArgRel G) as₁ as → as.length ≤ rs.length → Holds G (as.zip rs) s →
    T.ValsIn rs (as₁.map Arg.val) s
  | _, _, _, .nil, _, _ => by simp [Target.ValsIn]
  | _, _, r :: rs, .cons hab hrest, hl, hz => by
    have h1 := hz _ r (by simp) _ hab
    have h2 := valsIn_of_holds (rs := rs) hrest (by simpa using hl)
      fun x r' hx v hv => hz x r' (by simp [hx]) v hv
    simp only [Target.ValsIn, List.map_cons, List.length_cons, List.take_succ_cons,
      List.map_cons] at h2 ⊢
    rw [h1, h2]
  | _, _, [], .cons _ _, hl, _ => by simp at hl

theorem valsIn_cons {regs : List T.Reg} {vs : List Val} {s : T.MData} {r : T.Reg} {v : Val} :
    T.ValsIn (r :: regs) (v :: vs) s ↔ T.get s r = v ∧ T.ValsIn regs vs s := by
  simp [Target.ValsIn]

theorem valsIn_nil_cons {vs : List Val} {s : T.MData} {v : Val} :
    ¬ T.ValsIn [] (v :: vs) s := by
  simp [Target.ValsIn]

theorem prepend_ok {I : Isa} {pre : List I.Directive} {r : Res I} {c : List I.Directive}
    {nv nl : Nat} (h : prepend pre r = .ok (c, nv, nl)) :
    ∃ c', r = .ok (c', nv, nl) ∧ c = pre ++ c' := by
  unfold prepend at h
  split at h <;> simp_all

theorem _root_.LeanQbe.Forall₂.append_single {α β : Type} {R : α → β → Prop} {a : α} {b : β} :
    ∀ {as : List α} {bs : List β}, Forall₂ R as bs → R a b → Forall₂ R (as ++ [a]) (bs ++ [b])
  | _, _, .nil, h => .cons h .nil
  | _, _, .cons h1 h2, h => .cons h1 (h2.append_single h)

/-! ## Join points -/

section
variable (h : T.Host) (hints : Hints T.toIsa) (fn : String) (post : T.State → Prop)
  (F : Mem 64 → Prop) (s₀ : T.MData)

/-- The machine meaning of label `ℓ`, chosen for the source join point. -/
def LabJ (G : List (Val × Nat)) (ℓ : Nat) : Cont := fun as m =>
  ∃ k, (T.prog h)[k]? = some (T.label (lname fn ℓ)) ∧
    ∀ s, Agree G (hints.entry ℓ).live s → T.ValsIn (hints.entry ℓ).ploc as s → Inv F s₀ m s →
      T.Run h k s post

/-- Every join point in scope is a `LabJ` of an earlier context. -/
def DOk (G : List (Val × Nat)) (D : List (Cont × Nat)) : Prop :=
  ∀ J ℓ, (J, ℓ) ∈ D → ∃ G', (∀ p ∈ G', p ∈ G) ∧ J = LabJ h hints fn post F s₀ G' ℓ

end

theorem DOk.cons {h : T.Host} {hints : Hints T.toIsa} {fn : String} {post : T.State → Prop}
    {F : Mem 64 → Prop} {s₀ : T.MData} {G : List (Val × Nat)} {D : List (Cont × Nat)}
    (hD : DOk h hints fn post F s₀ G D) (p : Val × Nat) :
    DOk h hints fn post F s₀ (p :: G) D := by
  intro J ℓ hJ
  obtain ⟨G', hG', rfl⟩ := hD J ℓ hJ
  exact ⟨G', fun q hq => List.mem_cons_of_mem _ (hG' q hq), rfl⟩

/-! ## The main lemma -/

section
variable (h : T.Host) (hints : Hints T.toIsa) (fn : String) (Γ : Env) (Q : LeanQbe.Post)
  (X : XPost) (post : T.State → Prop) (F : Mem 64 → Prop) (s₀ : T.MData)

/-- What the function-level proof provides: memory facts about the frame `F`, and `ret`. -/
structure Hyps : Prop where
  unique : T.LabelsUnique h
  hload : ∀ (M m : Mem 64) cl sz sg a v, (M =⋆ Eq m ⋆ F) → loadVal m cl sz sg a = some v →
    loadVal M cl sz sg a = some v
  hstoreOk : ∀ (M m : Mem 64) sz a, (M =⋆ Eq m ⋆ F) → storeOk m sz a → storeOk M sz a
  hstore : ∀ (M m : Mem 64) sz a v, (M =⋆ Eq m ⋆ F) → storeOk m sz a →
    (storeMem M sz a v =⋆ Eq (storeMem m sz a v) ⋆ F)
  hret : ∀ k s rets m, T.ret.IsInfixAt (T.prog h) k → Q rets m → T.ValsIn T.retRegs rets s →
    Inv F s₀ m s → T.Run h k s post

/-- Correctness of `lower`, for every term related by `Wf`. -/
theorem lower_correct (hy : Hyps h Q post F s₀) {G : List (Val × Nat)} {D : List (Cont × Nat)}
    {e₁ : Expr Val Cont} {e₂ : Expr Nat Nat} (hwf : Wf G D e₁ e₂) :
    ∀ (st : St T.toIsa) (code : List T.Directive) (nv' nl' : Nat),
    lower hints fn e₂ st = .ok (code, nv', nl') →
    (∀ p ∈ G, p.2 < st.nv) →
    st.nv ≤ nv' ∧
    ∀ (k : Nat) (args : List Val) (acc : List Cont) (m : Mem 64) (s : T.MData),
    code.IsInfixAt (T.prog h) k →
    DOk h hints fn post F s₀ G D →
    Forall₂ (fun J ℓ => J = LabJ h hints fn post F s₀ G ℓ) acc st.pend →
    Agree G st.R s → T.ValsIn st.PL args s → Inv F s₀ m s →
    wp Γ Q X e₁ args acc m → T.Run h k s post := by
  have fresh : ∀ {G : List (Val × Nat)} {n : Nat}, (∀ p ∈ G, p.2 < n) →
      ∀ v, ∀ p ∈ (v, n) :: G, p.2 < n + 1 := by
    intro G n hG v p hp
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · simp
    · have := hG _ hp; omega
  induction hwf with
  | @let_ G D op₁ op₂ k₁ k₂ hop _ ih =>
    intro st code nv' nl' hl hG
    simp only [lower] at hl
    split at hl
    · rename_i d o hd ho
      split at hl
      · rename_i hda
        split at hl
        · rename_i c hc
          obtain ⟨c', hl', rfl⟩ := prepend_ok hl
          have ih' := fun v => ih v st.nv _ c' nv' nl' hl' (fresh hG v)
          refine ⟨by have := (ih' 0).1; simp at this; omega, ?_⟩
          intro k args acc m s hcode hD hP hA hR hI hw
          simp only [wp] at hw
          obtain ⟨rfl, v, hv, hw⟩ := hw
          obtain ⟨e1, hsc⟩ := opRegs_ok hA hop ho
          refine T.op_spec hc (hcode.append).1 hsc (by rw [e1]; exact hv) fun s' hd' hs' hm' => ?_
          exact (ih' v).2 _ [] [] _ s' (hcode.append).2 (hD.cons _) .nil
            ((hA.clob (keeps_dest' hs')).bindN hG hd') (by simp [Target.ValsIn])
            (hI.regs hm' (keeps_dest (.inl hda) hs')) hw
        · simp at hl
      · simp at hl
    · simp at hl
  | @load G D cl sz sg a₁ a₂ k₁ k₂ ha _ ih =>
    intro st code nv' nl' hl hG
    simp only [lower] at hl
    split at hl
    · rename_i d a' hd ha'
      split at hl
      · rename_i hda
        split at hl
        · rename_i c hc
          obtain ⟨c', hl', rfl⟩ := prepend_ok hl
          have ih' := fun v => ih v st.nv _ c' nv' nl' hl' (fresh hG v)
          refine ⟨by have := (ih' 0).1; simp at this; omega, ?_⟩
          intro k args acc m s hcode hD hP hA hR hI hw
          simp only [wp] at hw
          obtain ⟨rfl, v, hv, hw⟩ := hw
          obtain ⟨e1, hsc⟩ := argReg_ok hA ha ha'
          refine T.load_spec hc (hcode.append).1 hsc
            (by rw [e1]; exact hy.hload _ _ _ _ _ _ _ hI.1 hv) fun s' hd' hs' hm' => ?_
          exact (ih' v).2 _ [] [] _ s' (hcode.append).2 (hD.cons _) .nil
            ((hA.clob (keeps_dest' hs')).bindN hG hd') (by simp [Target.ValsIn])
            (hI.regs hm' (keeps_dest (.inl hda) hs')) hw
        · simp at hl
      · simp at hl
    · simp at hl
  | @store G D sz v₁ v₂ a₁ a₂ k₁ k₂ hv ha _ ih =>
    intro st code nv' nl' hl hG
    simp only [lower] at hl
    split at hl
    · rename_i v' a' hv' ha'
      split at hl
      · rename_i c hc
        obtain ⟨c', hl', rfl⟩ := prepend_ok hl
        have ih' := ih _ c' nv' nl' hl' hG
        refine ⟨ih'.1, ?_⟩
        intro k args acc m s hcode hD hP hA hR hI hw
        simp only [wp] at hw
        obtain ⟨rfl, hok, hw⟩ := hw
        obtain ⟨e1, s1⟩ := argReg_ok hA hv hv'
        obtain ⟨e2, s2⟩ := argReg_ok hA ha ha'
        refine T.store_spec hc (hcode.append).1
          (fun r hr => (List.mem_append.mp hr).elim (s1 r) (s2 r))
          (by rw [e2]; exact hy.hstoreOk _ _ _ _ hI.1 hok) fun s' hs' hm' => ?_
        rw [e1, e2] at hm'
        refine ih'.2 _ [] [] _ s' (hcode.append).2 hD .nil
          (hA.clob (fun r _ h2 => hs' r h2)) (by simp [Target.ValsIn])
          ⟨?_, fun r h1 h2 => (hs' r h2).trans (hI.2 r h1 h2)⟩ hw
        rw [hm']; exact hy.hstore _ _ _ _ _ hI.1 hok
      · simp at hl
    · simp at hl
  | call =>
    intro st code nv' nl' hl hG
    simp [lower] at hl
  | @jnz G D c₁ c₂ t₁ t₂ e₁ e₂ hc _ _ iht ihe =>
    intro st code nv' nl' hl hG
    cases hc with
    | imm c =>
      simp only [lower] at hl
      split at hl
      · rename_i htr
        have iht' := iht _ code nv' nl' hl hG
        refine ⟨iht'.1, ?_⟩
        intro k args acc m s hcode hD hP hA hR hI hw
        simp only [wp] at hw
        obtain ⟨rfl, hwt, -⟩ := hw
        exact iht'.2 k [] [] m s hcode hD .nil hA hR hI (hwt htr)
      · rename_i htr
        have ihe' := ihe _ code nv' nl' hl hG
        refine ⟨ihe'.1, ?_⟩
        intro k args acc m s hcode hD hP hA hR hI hw
        simp only [wp] at hw
        obtain ⟨rfl, -, hwe⟩ := hw
        exact ihe'.2 k [] [] m s hcode hD .nil hA hR hI (hwe htr)
    | @var v x hvx =>
      simp only [lower] at hl
      split at hl
      · rename_i rc hrc
        split at hl
        · rename_i ce nv1 nl1 hle
          obtain ⟨c', hl', rfl⟩ := prepend_ok hl
          have ihe' := ihe _ ce nv1 nl1 hle hG
          have iht' := iht _ c' nv' nl' hl'
            (fun p hp => by have := hG p hp; simp at ihe' ⊢; omega)
          refine ⟨by simp at iht' ihe'; omega, ?_⟩
          intro k args acc m s hcode hD hP hA hR hI hw
          simp only [wp] at hw
          obtain ⟨rfl, hwt, hwe⟩ := hw
          obtain ⟨e1, hsc⟩ := argReg_ok hA (.var hvx) hrc
          simp only [Arg.map, Arg.var.injEq] at e1
          have hc1 := (hcode.append).1
          have hlab : (T.prog h)[k + (T.jnz rc (lname fn st.nl)).length + ce.length]? =
              some (T.label (lname fn st.nl)) := by
            have := (hc1.append).2
            simpa [Nat.add_assoc] using (List.isInfixAt_singleton.mp this)
          refine T.jnz_spec (hc1.append).1.append.1 (labelAddr_of_unique hy.unique hlab)
            (hsc rc (by simp [Arg.vars])) fun s' hs' hm' => ⟨fun h0 => ?_, fun h0 => ?_⟩
          · refine T.label_spec hlab ?_
            have := iht'.2 _ [] [] m s' (hcode.append).2 hD .nil
              (hA.clob (fun r _ h2 => hs' r h2)) (by simp [Target.ValsIn])
              (hI.regs hm' (fun r _ h2 => hs' r h2)) (hwt (by rw [← e1]; exact h0))
            simpa only [Target.Run, List.length_append, List.length_singleton, Nat.add_assoc]
              using this
          · exact ihe'.2 _ [] [] m s' (hc1.append).1.append.2 hD .nil
              (hA.clob (fun r _ h2 => hs' r h2)) (by simp [Target.ValsIn])
              (hI.regs hm' (fun r _ h2 => hs' r h2)) (hwe (by rw [← e1]; exact h0))
        · simp at hl
      · simp at hl
  | @jump G D j₁ j₂ as₁ as₂ hj has =>
    intro st code nv' nl' hl hG
    simp only [lower] at hl
    split at hl
    · rename_i hcond
      obtain ⟨hlen, hnsc⟩ := hcond
      simp only [List.all_eq_true, decide_eq_true_eq] at hnsc
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
        refine shuffle_ok hsh (hcode.append).1 hA hI fun s' ht hI' => ?_
        refine T.jmp_spec (hcode.append).2 (labelAddr_of_unique hy.unique hkℓ)
          fun s'' hs'' hm'' => hJ s'' ?_ ?_ (hI'.regs hm'' (fun r _ h2 => hs'' r h2))
        · intro a r hx a₁ hv
          have hx' := List.mem_append_left (as₂.zip (hints.entry j₂).ploc) hx
          rw [hs'' r (hnsc _ hx')]
          exact ht a r hx' a₁ (hv.mono hG')
        · refine valsIn_of_holds has (by omega) fun a r hx a₁ hv => ?_
          have hx' := List.mem_append_right (hints.entry j₂).live hx
          rw [hs'' r (hnsc _ hx')]
          exact ht a r hx' a₁ hv
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
        refine shuffle_ok hsh (hcode.append).1 hA hI fun s' ht hI' => ?_
        exact hy.hret _ s' _ m (hcode.append).2 hw (valsIn_of_holds hvs (by simpa using hlen) ht) hI'
      · simp at hl
    · simp at hl
  | exit =>
    intro st code nv' nl' hl hG
    simp [lower] at hl
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
      refine ⟨by have := (ih 0 st.nv _ code nv' nl' hl (fresh hG 0)).1; simp at this; omega, ?_⟩
      intro k args acc m s hcode hD hP hA hR hI hw
      rw [hPL] at hR
      cases args with
      | nil => simp [wp] at hw
      | cons a as =>
        obtain ⟨hra, hR⟩ := valsIn_cons.mp hR
        simp only [wp] at hw
        exact (ih a st.nv _ code nv' nl' hl (fresh hG a)).2 k as [] m s hcode (hD.cons _) .nil
          (hA.bindN hG hra) hR hI hw
  | @label G D f₁ f₂ _ ih =>
    intro st code nv' nl' hl hG
    simp only [lower] at hl
    let J := LabJ h hints fn post F s₀ G st.nl
    have ih' := ih J st.nl _ code nv' nl' hl hG
    refine ⟨ih'.1, ?_⟩
    intro k args acc m s hcode hD hP hA hR hI hw
    simp only [wp] at hw
    obtain ⟨rfl, hw⟩ := hw
    refine ih'.2 k [] (acc ++ [J]) m s hcode ?_ (hP.append_single rfl) hA hR hI (hw J)
    intro J' ℓ hJ'
    simp only [List.mem_cons, Prod.mk.injEq] at hJ'
    rcases hJ' with ⟨rfl, rfl⟩ | hJ'
    · exact ⟨G, fun p hp => hp, rfl⟩
    · exact hD J' ℓ hJ'
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
        have ihb' := ihb _ c' nv' nl' hl'
          (fun p hp => by have := hG p hp; simp at ihr' ⊢; omega)
        refine ⟨by simp at ihr' ihb'; omega, ?_⟩
        intro k args acc m s hcode hD hP hA hR hI hw
        simp only [wp] at hw
        obtain ⟨rfl, hw⟩ := hw
        rw [hpend] at hP
        cases hP with
        | @cons J _ acc' _ hJ hP =>
          simp only at hw
          have hlab : (T.prog h)[k + cr.length]? = some (T.label (lname fn ℓ)) :=
            List.isInfixAt_singleton.mp ((hcode.append).1.append).2
          refine ihr'.2 k [] acc' m s ((hcode.append).1.append).1 hD hP hA hR hI (hw ?_)
          intro as m' hb
          rw [hJ]
          refine ⟨k + cr.length, hlab, fun s' hA' hR' hI' => T.label_spec hlab ?_⟩
          have := ihb'.2 _ as [] m' s' (hcode.append).2 hD .nil hA' hR' hI' hb
          simpa only [Target.Run, List.length_append, List.length_singleton, Nat.add_assoc]
            using this
      · simp at hl

end

end Rega
end LeanQbe

namespace LeanQbe
namespace Rega

variable {T : Target}

/-! ## Functions -/

/-- Memory facts about frames, used by `lowerFn_correct`; they hold for every target (`memFacts`). -/
structure MemFacts (T : Target) : Prop where
  load : ∀ (F : Mem 64 → Prop) (M m : Mem 64) cl sz sg a v, (M =⋆ Eq m ⋆ F) →
    loadVal m cl sz sg a = some v → loadVal M cl sz sg a = some v
  storeOk : ∀ (F : Mem 64 → Prop) (M m : Mem 64) sz a, (M =⋆ Eq m ⋆ F) → LeanQbe.storeOk m sz a →
    LeanQbe.storeOk M sz a
  store : ∀ (F : Mem 64 → Prop) (M m : Mem 64) sz a v, (M =⋆ Eq m ⋆ F) → LeanQbe.storeOk m sz a →
    (storeMem M sz a v =⋆ Eq (storeMem m sz a v) ⋆ F)
  exit : ∀ (M m : Mem 64) sp ra n (R : Mem 64 → Prop), n + T.raBytes ≤ 2 ^ 64 →
    (M =⋆ Eq m ⋆ (T.Entry sp ra n ⋆ R)) → (M =⋆ Eq m ⋆ T.Exit sp n ⋆ R)

theorem memFacts (T : Target) : MemFacts T :=
  ⟨fun _ _ _ _ _ _ _ _ hM h => loadVal_frame hM h, fun _ _ _ _ _ hM h => storeOk_frame hM h,
    fun _ _ _ _ _ _ hM h => storeMem_frame hM h _, fun _ _ _ _ _ _ hn => T.exit_of_entry_assoc hn⟩

theorem valsIn_keep {regs : List T.Reg} {vs : List Val} {s s' : T.MData}
    (hk : ∀ r, r ∈ regs → T.get s' r = T.get s r) (h : T.ValsIn regs vs s) : T.ValsIn regs vs s' := by
  unfold Target.ValsIn at h ⊢
  exact (List.map_congr_left fun r hr => hk r (List.mem_of_mem_take hr)).trans h

/-- The compiled function satisfies its source `wp` as a `FnSpec` (leaf functions, version 0). -/
theorem lowerFn_correct (h : T.Host) (hints : Hints T.toIsa) (f : Fn) (Γ : Env) (n : Nat)
    (code : List T.Directive) (k₀ : Nat)
    (hlow : lowerFn hints f = .ok code) (hcode : code.IsInfixAt (T.prog h) k₀)
    (hu : T.LabelsUnique h) (hwf : Func.Wf f.body) (hn : n + T.raBytes ≤ 2 ^ 64) (nX : Nat) :
    T.FnSpec h f.name (Func.spec Γ f.body) n nX := by
  have mf := memFacts T
  intro args m Q X hspec s ra R hargs hra _ hmem
  unfold lowerFn at hlow
  split at hlow
  · rename_i c nv nl hl
    simp only [Except.ok.injEq] at hlow
    subst hlow
    have hlab := (hcode.cons).1
    rw [labelAddr_of_unique hu hlab]
    refine T.label_spec hlab ?_
    have hF : T.mem s =⋆ Eq m ⋆ (T.Entry (T.get s T.sp) ra n ⋆ R) := by
      rw [← Std.ExtHashMap.sep_assoc]; exact hmem
    refine (lower_correct h hints f.name Γ Q X _ (T.Entry (T.get s T.sp) ra n ⋆ R) s ?_
      (hwf Val Nat Cont Nat) (St.init T.toIsa) c nv nl hl (by simp)).2 (k₀ + 1) args [] m s
      (hcode.cons).2 (fun _ _ hJ => by simp at hJ) .nil (fun _ _ hx => by simp [St.init] at hx)
      hargs ⟨hF, fun _ _ _ => rfl⟩ hspec
    refine ⟨hu, mf.load _, mf.storeOk _, mf.store _, ?_⟩
    intro k s' rets m' hret hQ hrets hI
    have hsp' : T.get s' T.sp = T.get s T.sp := hI.2 _ T.sp_not_allocatable T.sp_not_scratch
    have hmem' : T.mem s' =⋆ T.RetAddr (T.get s' T.sp) ra ⋆
        (Eq m' ⋆ (region (T.get s T.sp - BitVec.ofNat 64 n) n ⋆ R)) := by
      have := hI.1
      rw [hsp']
      simp only [Target.Entry] at this
      rwa [Std.ExtHashMap.sep_assoc (region _ _), Std.ExtHashMap.sep_comm_l (region _ _),
        Std.ExtHashMap.sep_comm_l (Eq m')] at this
    refine T.ret_spec hret (T.raReg_congr s s' ra (fun r h1 h2 => hI.2 r h1 h2) hra) hmem'
      fun s'' hs'' hsp'' hm'' => ?_
    refine Eventually.done _ (Or.inl ⟨T.pc_mk _ _, rets, m', hQ, ?_, ⟨?_, ?_⟩, ?_⟩)
    · rw [T.data_mk]
      refine valsIn_keep (fun r hr => hs'' r ?_) hrets
      simp only [List.mem_cons, not_or]
      exact ⟨fun e => T.sp_not_retRegs (e ▸ hr), T.retRegs_not_scratch r hr⟩
    · intro r hr
      rw [T.data_mk, hs'' r ?_]
      · exact hI.2 r (T.calleeSaved_not_allocatable r hr) (T.calleeSaved_not_scratch r hr)
      simp only [List.mem_cons, not_or]
      exact ⟨fun e => T.sp_not_calleeSaved (e ▸ hr), T.calleeSaved_not_scratch r hr⟩
    · rw [T.data_mk, hsp'', hsp']
    · rw [T.data_mk, hm'']; exact mf.exit _ _ _ _ _ _ hn hI.1
  · simp at hlow

end Rega
end LeanQbe
