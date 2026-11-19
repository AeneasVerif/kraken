module

public import LeanQbe.T.OptUtil
public import LeanQbe.T.WfLemmas
public import LeanQbe.T.WPLemmas

/-!
# Shared Mid-End Optimization Transport & Liveness Lemmas (`#015-B1`, `#016-B1`)

Centralizes proof helpers shared across `FoldLemmas`, `GvnLemmas`, `CanonLemmas`, `MemLoadLemmas`,
`IfOptLemmas`, `InlineLemmas`, `DivConstLemmas`, `PeelLemmas`, `SimplifyGroupLemmas1`,
`SimplifyGroupLemmas`, and `DceLemmas`:

* Symbolic `FKey` equality, evaluation environment `FEnv`, and update helpers (`valBeq_iff_eq`,
  `fKeyBeq_iff_eq`, `FKey.fev`, `FKey.FLt`, `fupd`, `fupdTup`, `fupd_eq`, `fupd_ne`,
  `fupdTup_lt`, `FKey.FLt.{le,mono,add}`, `FKey.fev_fupd`, `FKey.fev_fupdTup`).
* Semantic value transport (`flattenArg_val`, `flattenArgs_vals`, `toArgTup_zip_val`,
  `toArgTup_vals`, `ctx_zip_vals`, `tup_zip_vals_val`, `ctx_val_append`, `ctx_val_cons_var`).
* Relational `Wf` transport (`ArgRel.flattenArg`, `TRel.flattenArgs`, `OpRel.flattenOp`,
  `mem_zip_toArgTup`, `TRel.toArgTup_mem`, `toArgTup_trel`, `ctx_argRel_append`,
  `ctx_argRel_append_same`, `ctx_argRel_cons_var`, `mem_zip_argRel`).
* `Trie Unit` liveness and `OptV` binder invariants (`find?_trieUnion`, `TrieSub*`,
  `anyLive_eq_false`, `NoneDead*`, `SomeEq*`, `DceRel*`, `Arg.InSet*`, `ArgsInSet*`,
  `argSweep_*`, `argsSweep_*`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## Symbolic `FKey` equality, valuation updates, and key bounds (`#016-B1`) -/

theorem valBeq_iff_eq : {t : Ty} → {a b : Val t} → valBeq t a b = true ↔ a = b
  | .bool, a, b => by simp [valBeq]
  | .bits _, a, b => by simp [valBeq]
  | .float _, a, b => by simp [valBeq]
  | .pair s u, (a₁, a₂), (b₁, b₂) => by
    simp only [valBeq, Bool.and_eq_true, valBeq_iff_eq (t := s), valBeq_iff_eq (t := u),
      Prod.mk.injEq]

theorem fKeyBeq_iff_eq {t : Ty} : {a b : FKey t} → fKeyBeq a b = true ↔ a = b
  | .var i, .var j => by simp [fKeyBeq]
  | .imm a, .imm b => by simp [fKeyBeq, valBeq_iff_eq]
  | .var _, .imm _ | .imm _, .var _ => by simp [fKeyBeq]

/-- Evaluation environment for symbolic `FKey` variables. -/
abbrev FEnv := (t : Ty) → Nat → Val t

def FKey.fev (ρ : FEnv) : {t : Ty} → FKey t → Val t
  | t, .var i => ρ t i
  | _, .imm c => c

def FKey.FLt (b : Nat) : {t : Ty} → FKey t → Prop
  | _, .var i => i < b
  | _, .imm _ => True

def fupd (ρ : FEnv) {t : Ty} (b : Nat) (v : Val t) : FEnv :=
  fun t' i => if i = b then match tyDecEq t t' with | isTrue h => h ▸ v | isFalse _ => ρ t' i
    else ρ t' i

def fupdTup (ρ : FEnv) (b : Nat) : {ts : List Ty} → Tup Val ts → FEnv
  | [], (), t', i => ρ t' i
  | _ :: _, (x, xs), t', i => fupdTup (fupd ρ b x) (b + 1) xs t' i

theorem fupd_eq (ρ : FEnv) {t : Ty} (b : Nat) (v : Val t) : fupd ρ b v t b = v := by
  simp only [fupd, ↓reduceIte]
  cases h : tyDecEq t t with | isTrue _ => rfl | isFalse hne => exact absurd rfl hne

theorem fupd_ne (ρ : FEnv) {t t' : Ty} {b i : Nat} (v : Val t) (h : i ≠ b) :
    fupd ρ b v t' i = ρ t' i := by
  simp [fupd, h]

theorem fupdTup_lt (ρ : FEnv) :
    {ts : List Ty} → (xs : Tup Val ts) → {b : Nat} → {t' : Ty} → {i : Nat} →
    i < b → fupdTup ρ b xs t' i = ρ t' i
  | [], (), _, _, _, _ => rfl
  | _ :: _, (x, xs), b, t', i, hi => by
    simp only [fupdTup]
    rw [fupdTup_lt (fupd ρ b x) xs (by omega)]
    exact fupd_ne ρ x (by omega)

theorem FKey.FLt.le {b₁ b₂ : Nat} (h : b₁ ≤ b₂) : {t : Ty} → {κ : FKey t} → κ.FLt b₁ → κ.FLt b₂
  | _, .var _, hk => Nat.lt_of_lt_of_le hk h
  | _, .imm _, _ => trivial

theorem FKey.FLt.mono {b : Nat} {t : Ty} {κ : FKey t} (h : κ.FLt b) : κ.FLt (b + 1) :=
  h.le (Nat.le_succ b)

theorem FKey.FLt.add {b k : Nat} {t : Ty} {κ : FKey t} (h : κ.FLt b) : κ.FLt (b + k) :=
  h.le (Nat.le_add_right b k)

theorem FKey.fev_fupd {ρ : FEnv} {b : Nat} {u : Ty} (v : Val u)
    {t : Ty} {κ : FKey t} (h : κ.FLt b) : κ.fev (fupd ρ b v) = κ.fev ρ := by
  cases κ with
  | var _ => exact fupd_ne ρ v (Nat.ne_of_lt h)
  | imm _ => rfl

theorem FKey.fev_fupdTup {ρ : FEnv} {b : Nat}
    {ts : List Ty} (xs : Tup Val ts) {t : Ty} {κ : FKey t} (h : κ.FLt b) :
    κ.fev (fupdTup ρ b xs) = κ.fev ρ := by
  cases κ with
  | var _ => exact fupdTup_lt ρ xs h
  | imm _ => rfl

/-! ## Two-level operand flattening & `toArgTup` semantic transport -/

theorem flattenArg_val {G : Ctx (Arg Val) Val} (hG : ∀ p ∈ G, p.2.1.val = p.2.2)
    {t : Ty} {a₁ : Arg (Arg Val) t} {a₂ : Arg Val t} (ha : ArgRel G t a₁ a₂) :
    (flattenArg a₁).val = a₂.val := by
  cases ha with
  | var hm => exact hG _ hm
  | imm _ => rfl

theorem flattenArgs_vals {G : Ctx (Arg Val) Val} (hG : ∀ p ∈ G, p.2.1.val = p.2.2)
    {ts : List Ty} {as₁ : Tup (Arg (Arg Val)) ts} {as₂ : Tup (Arg Val) ts}
    (h : TRel (ArgRel G) as₁ as₂) : vals (flattenArgs as₁) = vals as₂ :=
  TRel.tupMapArg_vals (fun _ => flattenArg) (fun ha => flattenArg_val hG ha) h

theorem toArgTup_zip_val :
    {ts : List Ty} → (xs : Tup Val ts) → ∀ p ∈ Tup.zip (toArgTup xs) xs, p.2.1.val = p.2.2
  | [], (), _, hp => nomatch hp
  | _ :: _, (_, xs), _, hp => by
    cases hp with
    | head => rfl
    | tail _ hp => exact toArgTup_zip_val xs _ hp

theorem toArgTup_vals : {ts : List Ty} → (xs : Tup Val ts) → vals (toArgTup xs) = xs
  | [], () => rfl
  | _ :: _, (_, xs) => Prod.ext rfl (toArgTup_vals xs)

theorem ctx_zip_vals :
    {ts : List Ty} → (args : Tup (Arg Val) ts) → ∀ p ∈ Tup.zip args (vals args), p.2.1.val = p.2.2
  | [], (), _, hp => nomatch hp
  | _ :: _, (_, args), _, hp => by
    cases hp with
    | head => rfl
    | tail _ hp => exact ctx_zip_vals args _ hp

theorem tup_zip_vals_val {ts : List Ty} :
    ∀ (r₁ : Tup (Arg Val) ts) (r₂ : Tup Val ts), vals r₁ = r₂ →
      ∀ p ∈ Tup.zip r₁ r₂, p.2.1.val = p.2.2 := by
  intro r₁ r₂ h p hp
  induction ts with
  | nil => cases hp
  | cons _ _ ih =>
    cases hp with
    | head => exact (Prod.ext_iff.mp h).1
    | tail _ hp => exact ih _ _ (Prod.ext_iff.mp h).2 hp

theorem ctx_val_append {H G : Ctx (Arg Val) Val}
    (hH : ∀ p ∈ H, p.2.1.val = p.2.2) (hG : ∀ p ∈ G, p.2.1.val = p.2.2) :
    ∀ p ∈ H ++ G, p.2.1.val = p.2.2 := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact hH p hp
  · exact hG p hp

theorem ctx_val_cons_var {G : Ctx (Arg Val) Val} (hG : ∀ p ∈ G, p.2.1.val = p.2.2)
    {t : Ty} (v : Val t) : ∀ p ∈ (⟨t, .var v, v⟩ :: G), p.2.1.val = p.2.2
  | _, .head _ => rfl
  | _, .tail _ hp => hG _ hp

/-! ## Two-level operand flattening & `toArgTup` `Wf` transport -/

theorem ArgRel.flattenArg {V₁ V₂ : Ty → Type}
    {G_body : Ctx (Arg V₁) (Arg V₂)} {G : Ctx V₁ V₂}
    (hG : ∀ p ∈ G_body, ArgRel G p.1 p.2.1 p.2.2)
    {t : Ty} {a₁ : Arg (Arg V₁) t} {a₂ : Arg (Arg V₂) t} :
    ArgRel G_body t a₁ a₂ → ArgRel G t (LeanQbe.T.flattenArg a₁) (LeanQbe.T.flattenArg a₂)
  | .var hm => hG _ hm
  | .imm c => .imm c

theorem TRel.flattenArgs {V₁ V₂ : Ty → Type}
    {G_body : Ctx (Arg V₁) (Arg V₂)} {G : Ctx V₁ V₂}
    (hG : ∀ p ∈ G_body, ArgRel G p.1 p.2.1 p.2.2)
    {ts : List Ty} {as₁ : Tup (Arg (Arg V₁)) ts} {as₂ : Tup (Arg (Arg V₂)) ts} :
    TRel (ArgRel G_body) as₁ as₂ →
    TRel (ArgRel G) (LeanQbe.T.flattenArgs as₁) (LeanQbe.T.flattenArgs as₂) :=
  TRel.tupMapArg_rel (fun _ => LeanQbe.T.flattenArg) (fun _ => LeanQbe.T.flattenArg)
    (fun ha => ha.flattenArg hG)

theorem OpRel.flattenOp {V₁ V₂ : Ty → Type}
    {G_body : Ctx (Arg V₁) (Arg V₂)} {G : Ctx V₁ V₂}
    (hG : ∀ p ∈ G_body, ArgRel G p.1 p.2.1 p.2.2)
    {rs : List Ty} {op₁ : Op (Arg V₁) rs} {op₂ : Op (Arg V₂) rs} :
    OpRel G_body op₁ op₂ → OpRel G (LeanQbe.T.flattenOp op₁) (LeanQbe.T.flattenOp op₂)
  | .mk code hargs => .mk code (TRel.flattenArgs hG hargs)

theorem mem_zip_toArgTup {V₁ V₂ : Ty → Type} :
    {ts : List Ty} → (xs₁ : Tup V₁ ts) → (xs₂ : Tup V₂ ts) →
    ∀ p ∈ Tup.zip (toArgTup xs₁) (toArgTup xs₂), ArgRel (Tup.zip xs₁ xs₂) p.1 p.2.1 p.2.2
  | [], (), (), _, hp => nomatch hp
  | _ :: _, (_, _), (_, _), _, hp => by
    cases hp with
    | head => exact .var List.mem_cons_self
    | tail _ hp =>
      exact (mem_zip_toArgTup _ _ _ hp).weaken (fun _ hq => List.mem_cons_of_mem _ hq)

theorem TRel.toArgTup_mem {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} :
    {ts : List Ty} → (xs₁ : Tup V₁ ts) → (xs₂ : Tup V₂ ts) →
    TRel (ArgRel (Tup.zip xs₁ xs₂ ++ G)) (toArgTup xs₁) (toArgTup xs₂)
  | [], (), () => .nil
  | _ :: _, (_, xs₁), (_, xs₂) =>
    .cons (.var List.mem_cons_self)
      ((TRel.toArgTup_mem xs₁ xs₂).argRel_weaken fun _ h => .tail _ h)

theorem toArgTup_trel {V₁ V₂ : Ty → Type} :
    {ts : List Ty} → (xs₁ : Tup V₁ ts) → (xs₂ : Tup V₂ ts) →
    TRel (ArgRel (Tup.zip xs₁ xs₂)) (toArgTup xs₁) (toArgTup xs₂)
  | [], (), () => .nil
  | _ :: _, (_, xs₁), (_, xs₂) =>
    .cons (.var List.mem_cons_self)
      ((toArgTup_trel xs₁ xs₂).argRel_weaken fun _ h => .tail _ h)

theorem ctx_argRel_append {V₁ V₂ : Ty → Type}
    {H G_body : Ctx (Arg V₁) (Arg V₂)} {G₁ G₂ : Ctx V₁ V₂}
    (hH : ∀ p ∈ H, ArgRel G₁ p.1 p.2.1 p.2.2)
    (hG : ∀ p ∈ G_body, ArgRel G₂ p.1 p.2.1 p.2.2) :
    ∀ p ∈ H ++ G_body, ArgRel (G₁ ++ G₂) p.1 p.2.1 p.2.2 := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact (hH p hp).weaken (fun _ hq => List.mem_append_left _ hq)
  · exact (hG p hp).weaken (fun _ hq => List.mem_append_right _ hq)

theorem ctx_argRel_append_same {V₁ V₂ : Ty → Type}
    {H G_body : Ctx (Arg V₁) (Arg V₂)} {G' : Ctx V₁ V₂}
    (hH : ∀ p ∈ H, ArgRel G' p.1 p.2.1 p.2.2)
    (hG : ∀ p ∈ G_body, ArgRel G' p.1 p.2.1 p.2.2) :
    ∀ p ∈ H ++ G_body, ArgRel G' p.1 p.2.1 p.2.2 := fun p hp =>
  (List.mem_append.1 hp).elim (hH p) (hG p)

theorem ctx_argRel_cons_var {V₁ V₂ : Ty → Type}
    {G_body : Ctx (Arg V₁) (Arg V₂)} {G : Ctx V₁ V₂}
    (hG : ∀ p ∈ G_body, ArgRel G p.1 p.2.1 p.2.2) {t : Ty} (v₁ : V₁ t) (v₂ : V₂ t) :
    ∀ p ∈ (⟨t, .var v₁, .var v₂⟩ :: G_body), ArgRel (⟨t, v₁, v₂⟩ :: G) p.1 p.2.1 p.2.2
  | _, .head _ => .var List.mem_cons_self
  | _, .tail _ hp => (hG _ hp).weaken (fun _ hq => List.mem_cons_of_mem _ hq)

theorem mem_zip_argRel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} :
    {ts : List Ty} → {as₁ : Tup (Arg V₁) ts} → {as₂ : Tup (Arg V₂) ts} →
    TRel (ArgRel G) as₁ as₂ → ∀ p ∈ Tup.zip as₁ as₂, ArgRel G p.1 p.2.1 p.2.2
  | [], (), (), .nil, _, hp => nomatch hp
  | _ :: _, (_, _), (_, _), .cons h hs, _, hp => by
    cases hp with
    | head => exact h
    | tail _ hp => exact mem_zip_argRel hs _ hp

/-! ## `Trie Unit`, `trieUnion`, `anyLive`, and `addArgKeys` lemmas -/

theorem find?_trieUnion : ∀ (t₁ t₂ : Trie Unit) (x : Nat),
    (trieUnion t₁ t₂).find? x = (t₁.find? x).or (t₂.find? x)
  | .empty, t₂, x => by simp [trieUnion]
  | .node _ _ _, .empty, _ => by simp [trieUnion]
  | .node (some ()) _ _, .node _ _ _, 0 => rfl
  | .node none _ _, .node _ _ _, 0 => rfl
  | .node (some ()) e₁ o₁, .node _ e₂ o₂, x + 1 => by
    simp only [trieUnion, Trie.find?]
    split <;> exact find?_trieUnion _ _ (x / 2)
  | .node none e₁ o₁, .node _ e₂ o₂, x + 1 => by
    simp only [trieUnion, Trie.find?]
    split <;> exact find?_trieUnion _ _ (x / 2)

theorem trieMem_union_left {t₁ t₂ : Trie Unit} {x : Nat}
    (h : (t₁.find? x).isSome = true) : ((trieUnion t₁ t₂).find? x).isSome = true := by
  rw [find?_trieUnion]; cases h₁ : t₁.find? x <;> simp_all

theorem trieMem_union_right {t₁ t₂ : Trie Unit} {x : Nat}
    (h : (t₂.find? x).isSome = true) : ((trieUnion t₁ t₂).find? x).isSome = true := by
  rw [find?_trieUnion]; cases h₁ : t₁.find? x <;> simp_all

/-- Subset relation on `Trie Unit` liveness sets. -/
def TrieSub (s₁ s₂ : Trie Unit) : Prop :=
  ∀ x : Nat, (s₁.find? x).isSome = true → (s₂.find? x).isSome = true

theorem TrieSub.refl (s : Trie Unit) : TrieSub s s := fun _ h => h

theorem TrieSub.trans {s₁ s₂ s₃ : Trie Unit} (h12 : TrieSub s₁ s₂) (h23 : TrieSub s₂ s₃) :
    TrieSub s₁ s₃ := fun x hx => h23 x (h12 x hx)

theorem TrieSub.insert (s : Trie Unit) (i : Nat) : TrieSub s (s.insert i ()) := by
  intro x hx; rw [Trie.find?_insert]; split <;> simp [hx]

theorem TrieSub.union_left (s₁ s₂ : Trie Unit) : TrieSub s₁ (trieUnion s₁ s₂) :=
  fun _ h => trieMem_union_left h

theorem TrieSub.union_right (s₁ s₂ : Trie Unit) : TrieSub s₂ (trieUnion s₁ s₂) :=
  fun _ h => trieMem_union_right h

theorem TrieSub.addArgKey {t : Ty} (a : Arg K t) (s : Trie Unit) :
    TrieSub s (LeanQbe.T.addArgKey a s) := by
  cases a with
  | var i => exact TrieSub.insert s i
  | imm _ => exact TrieSub.refl s

theorem TrieSub.addArgKeys :
    {ts : List Ty} → (as : Tup (Arg K) ts) → (s : Trie Unit) →
    TrieSub s (LeanQbe.T.addArgKeys as s)
  | [], (), s => TrieSub.refl s
  | _ :: _, (a, as), s =>
    TrieSub.trans (TrieSub.addArgKeys as s) (TrieSub.addArgKey a (LeanQbe.T.addArgKeys as s))

theorem anyLive_eq_false :
    ∀ (k b : Nat) (s : Trie Unit), anyLive b k s = false →
      ∀ i, b ≤ i → i < b + k → (s.find? i).isSome = false
  | 0, _, _, _, _, h1, h2 => by omega
  | k + 1, b, s, h, i, h1, h2 => by
    simp only [anyLive, Bool.or_eq_false_iff] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact h.1
    · exact anyLive_eq_false k (b + 1) s h.2 i hlt (by omega)

/-! ## `OptV` liveness and binder invariants (`NoneDead`, `SomeEq`, `DceRel`, `argSweep`) -/

/-- Every dropped (`none`) binder level in `Gk` is absent from liveness set `s`. -/
def NoneDead {V : Ty → Type} (s : Trie Unit) (Gk : Ctx K (OptV V)) : Prop :=
  ∀ {t : Ty} {k : Nat} {o : OptV V t}, ⟨t, k, o⟩ ∈ Gk → o = none → (s.find? k).isSome = false

theorem NoneDead.sub {V : Ty → Type} {s₁ s₂ : Trie Unit} {Gk : Ctx K (OptV V)}
    (hsub : TrieSub s₁ s₂) (hnd : NoneDead s₂ Gk) : NoneDead s₁ Gk := by
  intro t k o hm ho
  cases hmem : (s₁.find? k).isSome with
  | false => rfl
  | true =>
    have hmem2 := hsub k hmem
    have hf := hnd hm ho
    rw [hf] at hmem2
    cases hmem2

theorem NoneDead.cons_some {V : Ty → Type} {s : Trie Unit} {Gk : Ctx K (OptV V)}
    (hnd : NoneDead s Gk) {t : Ty} (k : Nat) (v : V t) :
    NoneDead s (⟨t, k, some v⟩ :: Gk) := by
  intro _ _ _ hm ho; cases hm with | head => cases ho | tail _ hm' => exact hnd hm' ho

theorem NoneDead.cons_none {V : Ty → Type} {s : Trie Unit} {Gk : Ctx K (OptV V)}
    (hnd : NoneDead s Gk) {t : Ty} (b : Nat) (hb : (s.find? b).isSome = false) :
    NoneDead s (⟨t, b, none⟩ :: Gk) := by
  intro _ _ _ hm ho; cases hm with | head => exact hb | tail _ hm' => exact hnd hm' ho

theorem NoneDead.append_some {V : Ty → Type} {s : Trie Unit} {Gk : Ctx K (OptV V)}
    (hnd : NoneDead s Gk) :
    {ts : List Ty} → (ks : Tup K ts) → (xs : Tup V ts) →
    NoneDead s (Tup.zip ks (someTup ts xs) ++ Gk)
  | [], (), () => hnd
  | _ :: _, (k, ks), (x, xs) => NoneDead.cons_some (NoneDead.append_some hnd ks xs) k x

theorem NoneDead.append_none {V : Ty → Type} {s : Trie Unit} {Gk : Ctx K (OptV V)}
    (hnd : NoneDead s Gk) :
    {ts : List Ty} → (b : Nat) → (∀ i, b ≤ i → i < b + ts.length → (s.find? i).isSome = false) →
    NoneDead s (Tup.zip (Tup.levels ts b) (noneTup (V := V) ts) ++ Gk)
  | [], _, _ => hnd
  | _ :: ts, b, hfalse => by
    simp only [Tup.levels, noneTup, Tup.zip, List.cons_append]
    intro hm ho
    cases hm with
    | head => exact hfalse _ (Nat.le_refl _) (by simp)
    | tail _ hm' =>
      exact NoneDead.append_none hnd (b + 1)
        (fun i hi1 hi2 =>
          hfalse i (Nat.le_of_succ_le hi1) (by simp only [List.length_cons] at hi2 ⊢; omega))
        hm' ho

/-- Every kept (`some`) binder in `G` agrees with its semantic value in `Val`. -/
def SomeEq (G : Ctx (OptV Val) Val) : Prop :=
  ∀ {t : Ty} {o : OptV Val t} {v : Val t}, ⟨t, o, v⟩ ∈ G → ∀ w, o = some w → w = v

theorem SomeEq.cons_some {G : Ctx (OptV Val) Val} (hG : SomeEq G) {t : Ty} (v : Val t) :
    SomeEq (⟨t, some v, v⟩ :: G) := by
  intro _ _ _ hm w hw
  cases hm with | head => injection hw with h; exact h.symm | tail _ hm' => exact hG hm' w hw

theorem SomeEq.cons_none {G : Ctx (OptV Val) Val} (hG : SomeEq G) {t : Ty} (v : Val t) :
    SomeEq (⟨t, none, v⟩ :: G) := by
  intro _ _ _ hm _ hw; cases hm with | head => cases hw | tail _ hm' => exact hG hm' _ hw

theorem SomeEq.append_some {G : Ctx (OptV Val) Val} (hG : SomeEq G) :
    {ts : List Ty} → (xs : Tup Val ts) → SomeEq (Tup.zip (someTup ts xs) xs ++ G)
  | [], () => hG
  | _ :: _, (x, xs) => SomeEq.cons_some (SomeEq.append_some hG xs) x

theorem SomeEq.append_none {G : Ctx (OptV Val) Val} (hG : SomeEq G) :
    {ts : List Ty} → (xs : Tup Val ts) → SomeEq (Tup.zip (noneTup ts) xs ++ G)
  | [], () => hG
  | _ :: _, (_, xs) => by
    simp only [noneTup, Tup.zip, List.cons_append]
    intro hm w hw
    cases hm with | head => cases hw | tail _ hm' => exact SomeEq.append_none hG xs hm' w hw

/-- Lockstep `Option` binder invariant: both dropped (`none, none`) or both kept (`some`). -/
def DceRel {V₁ V₂ : Ty → Type} (G : Ctx (OptV V₁) (OptV V₂)) (G' : Ctx V₁ V₂) : Prop :=
  ∀ {t : Ty} {o₁ : OptV V₁ t} {o₂ : OptV V₂ t}, ⟨t, o₁, o₂⟩ ∈ G →
    (o₁ = none ∧ o₂ = none) ∨ ∃ v₁ v₂, o₁ = some v₁ ∧ o₂ = some v₂ ∧ ⟨t, v₁, v₂⟩ ∈ G'

theorem DceRel.weaken {V₁ V₂ : Ty → Type} {G : Ctx (OptV V₁) (OptV V₂)} {G₁ G₂ : Ctx V₁ V₂}
    (hsub : ∀ p ∈ G₁, p ∈ G₂) (hrel : DceRel G G₁) : DceRel G G₂ := by
  intro t o₁ o₂ hm
  rcases hrel hm with h | ⟨v₁, v₂, h1, h2, hmem⟩
  · exact Or.inl h
  · exact Or.inr ⟨v₁, v₂, h1, h2, hsub _ hmem⟩

theorem DceRel.cons_some {V₁ V₂ : Ty → Type} {G : Ctx (OptV V₁) (OptV V₂)} {G' : Ctx V₁ V₂}
    (hrel : DceRel G G') {t : Ty} (v₁ : V₁ t) (v₂ : V₂ t) :
    DceRel (⟨t, some v₁, some v₂⟩ :: G) (⟨t, v₁, v₂⟩ :: G') := by
  intro _ _ _ hm
  cases hm with
  | head => exact Or.inr ⟨v₁, v₂, rfl, rfl, List.mem_cons_self⟩
  | tail _ hm' => exact (hrel.weaken (fun _ hp => List.mem_cons_of_mem _ hp)) hm'

theorem DceRel.cons_none {V₁ V₂ : Ty → Type} {G : Ctx (OptV V₁) (OptV V₂)} {G' : Ctx V₁ V₂}
    (hrel : DceRel G G') {t : Ty} : DceRel (⟨t, none, none⟩ :: G) G' := by
  intro _ _ _ hm
  cases hm with | head => exact Or.inl ⟨rfl, rfl⟩ | tail _ hm' => exact hrel hm'

theorem DceRel.append_some {V₁ V₂ : Ty → Type} {G : Ctx (OptV V₁) (OptV V₂)} {G' : Ctx V₁ V₂}
    (hrel : DceRel G G') :
    {ts : List Ty} → (xs₁ : Tup V₁ ts) → (xs₂ : Tup V₂ ts) →
    DceRel (Tup.zip (someTup ts xs₁) (someTup ts xs₂) ++ G) (Tup.zip xs₁ xs₂ ++ G')
  | [], (), () => hrel
  | _ :: _, (x₁, xs₁), (x₂, xs₂) => DceRel.cons_some (DceRel.append_some hrel xs₁ xs₂) x₁ x₂

theorem DceRel.append_none {V₁ V₂ : Ty → Type} {G : Ctx (OptV V₁) (OptV V₂)} {G' : Ctx V₁ V₂}
    (hrel : DceRel G G') :
    {ts : List Ty} → DceRel (Tup.zip (noneTup (V := V₁) ts) (noneTup (V := V₂) ts) ++ G) G'
  | [] => hrel
  | _ :: _ => by
    simp only [noneTup, Tup.zip, List.cons_append]
    intro hm
    cases hm with
    | head => exact Or.inl ⟨rfl, rfl⟩
    | tail _ hm' => exact DceRel.append_none hrel hm'

/-! ## Operand liveness predicates and `argSweep` transport lemmas -/

def Arg.InSet (s : Trie Unit) {t : Ty} : Arg K t → Prop
  | .var k => (s.find? k).isSome = true
  | .imm _ => True

theorem Arg.InSet.mono {s₁ s₂ : Trie Unit} (hsub : TrieSub s₁ s₂) {t : Ty} {a : Arg K t} :
    a.InSet s₁ → a.InSet s₂ := by
  cases a with | var k => exact hsub k | imm _ => exact fun _ => trivial

theorem Arg.InSet.addArgKey {t : Ty} (a : Arg K t) (s : Trie Unit) :
    a.InSet (addArgKey a s) := by
  cases a with | var k => simp [Arg.InSet, LeanQbe.T.addArgKey] | imm _ => trivial

def ArgsInSet (s : Trie Unit) : {ts : List Ty} → Tup (Arg K) ts → Prop
  | [], () => True
  | _ :: _, (a, as) => a.InSet s ∧ ArgsInSet s as

theorem ArgsInSet.mono {s₁ s₂ : Trie Unit} (hsub : TrieSub s₁ s₂) :
    {ts : List Ty} → {as : Tup (Arg K) ts} → ArgsInSet s₁ as → ArgsInSet s₂ as
  | [], (), _ => trivial
  | _ :: _, (_, _), ⟨ha, has⟩ => ⟨ha.mono hsub, ArgsInSet.mono hsub has⟩

theorem ArgsInSet.addArgKeys :
    {ts : List Ty} → (as : Tup (Arg K) ts) → (s : Trie Unit) →
    ArgsInSet (LeanQbe.T.addArgKeys as s) as
  | [], (), _ => trivial
  | _ :: _, (a, as), s =>
    ⟨Arg.InSet.addArgKey a (LeanQbe.T.addArgKeys as s),
     ArgsInSet.mono (TrieSub.addArgKey a (LeanQbe.T.addArgKeys as s))
       (ArgsInSet.addArgKeys as s)⟩

theorem argSweep_val_of_inSet {s : Trie Unit} {Gk : Ctx K (OptV Val)} {G : Ctx (OptV Val) Val}
    (hnd : NoneDead s Gk) (hG : SomeEq G)
    {t : Ty} {ak : Arg K t} {a₁ : Arg (OptV Val) t} {a₂ : Arg Val t}
    (hk : ArgRel Gk t ak a₁) (h12 : ArgRel G t a₁ a₂) (hin : ak.InSet s) :
    (argSweep a₁).val = a₂.val := by
  cases h12 with
  | imm _ => rfl
  | var hm12 =>
    cases hk with
    | var hmk =>
      rename_i o v k
      cases o with
      | some w => have hw : w = v := hG hm12 w rfl; subst hw; rfl
      | none =>
        have hfalse := hnd hmk rfl
        have hkmem : (s.find? k).isSome = true := hin
        rw [hfalse] at hkmem; cases hkmem

theorem argsSweep_vals_of_inSet {s : Trie Unit} {Gk : Ctx K (OptV Val)} {G : Ctx (OptV Val) Val}
    (hnd : NoneDead s Gk) (hG : SomeEq G) :
    {ts : List Ty} → {aks : Tup (Arg K) ts} → {as₁ : Tup (Arg (OptV Val)) ts} →
    {as₂ : Tup (Arg Val) ts} →
    TRel (ArgRel Gk) aks as₁ → TRel (ArgRel G) as₁ as₂ → ArgsInSet s aks →
    vals (argsSweep as₁) = vals as₂
  | [], (), (), (), .nil, .nil, _ => rfl
  | _ :: _, (_, _), (_, _), (_, _), .cons hka hkas, .cons h12a h12as, ⟨ha, has⟩ =>
    Prod.ext (argSweep_val_of_inSet hnd hG hka h12a ha)
      (argsSweep_vals_of_inSet hnd hG hkas h12as has)

theorem argSweep_rel_of_inSet {V₁ V₂ : Ty → Type} {s : Trie Unit}
    {Gk : Ctx K (OptV V₁)} {G : Ctx (OptV V₁) (OptV V₂)} {G' : Ctx V₁ V₂}
    (hnd : NoneDead s Gk) (hrel : DceRel G G')
    {t : Ty} {ak : Arg K t} {a₁ : Arg (OptV V₁) t} {a₂ : Arg (OptV V₂) t}
    (hk : ArgRel Gk t ak a₁) (h12 : ArgRel G t a₁ a₂) (hin : ak.InSet s) :
    ArgRel G' t (argSweep a₁) (argSweep a₂) := by
  cases h12 with
  | imm c => exact .imm c
  | var hm12 =>
    cases hk with
    | var hmk =>
      rename_i o₁ o₂ k
      rcases hrel hm12 with ⟨h1, _⟩ | ⟨v₁, v₂, h1, h2, hmem⟩
      · subst h1
        have hfalse := hnd hmk rfl
        have hkmem : (s.find? k).isSome = true := hin
        rw [hfalse] at hkmem; cases hkmem
      · subst h1 h2; exact .var hmem

theorem TRel.argsSweep_of_inSet {V₁ V₂ : Ty → Type} {s : Trie Unit}
    {Gk : Ctx K (OptV V₁)} {G : Ctx (OptV V₁) (OptV V₂)} {G' : Ctx V₁ V₂}
    (hnd : NoneDead s Gk) (hrel : DceRel G G') :
    {ts : List Ty} → {aks : Tup (Arg K) ts} → {as₁ : Tup (Arg (OptV V₁)) ts} →
    {as₂ : Tup (Arg (OptV V₂)) ts} →
    TRel (ArgRel Gk) aks as₁ → TRel (ArgRel G) as₁ as₂ → ArgsInSet s aks →
    TRel (ArgRel G') (argsSweep as₁) (argsSweep as₂)
  | [], (), (), (), .nil, .nil, _ => .nil
  | _ :: _, (_, _), (_, _), (_, _), .cons hka hkas, .cons h12a h12as, ⟨ha, has⟩ =>
    .cons (argSweep_rel_of_inSet hnd hrel hka h12a ha)
      (TRel.argsSweep_of_inSet hnd hrel hkas h12as has)

end LeanQbe.T
