module

public import LeanQbe.T.IfOpt
public import LeanQbe.T.OptUtilLemmas
public import LeanQbe.T.OpsLemmas

/-!
# Correctness of `ifOpt` (`O-M2`, `MB3`)

* `OpCode.wp_of_isSafeOp`: every whitelisted safe opcode is total and UB-free.
* `emitSelectTup_wp`, `emitSelectTup_wf`: scalar/pair `select` lowering correctness (including
  identical-operand skip via `fKeyBeq_iff_eq`).
* `ifOpt_wf`, `ifOpt_wp`: expression-level `Wf` preservation and WP refinement via `Wf.induct`.
* `Func.ifOpt_wf`, `Func.ifOpt_spec`: closed-function specifications.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

open IfOptImpl

namespace IfOptImpl

/-! ## Safe opcode totality -/

theorem OpCode.wp_of_isSafeOp {sig rs : List Ty} (code : OpCode sig rs)
    (hs : isSafeOp code = true) (args : Tup Val sig) {P : Tup Val rs → Prop}
    (hP : ∀ r, P r) : code.wp args P := by
  cases code with
  | copy _ => exact hP _
  | add t | sub t | mul t | shl t | lshr t | ashr t | rotl t | rotr t =>
    rcases args with ⟨a, b, ⟨⟩⟩
    have hf : t.hasFloat = false := by simpa [isSafeOp] using hs
    simp [OpCode.wp, hf, hP]
  | neg t =>
    rcases args with ⟨a, ⟨⟩⟩
    have hf : t.hasFloat = false := by simpa [isSafeOp] using hs
    simp [OpCode.wp, hf, hP]
  | cmp o t m h =>
    subst h
    rcases args with ⟨a, b, ⟨⟩⟩
    have hf : t.hasFloat = false := by simpa [isSafeOp] using hs
    simp [OpCode.wp, hf, hP]
  | zext m n | sext m n =>
    rcases args with ⟨a, ⟨⟩⟩
    have hle : m ≤ n := by simpa [isSafeOp] using hs
    exact ⟨hle, hP _⟩
  | trunc m n =>
    rcases args with ⟨a, ⟨⟩⟩
    have hle : n ≤ m := by simpa [isSafeOp] using hs
    exact ⟨hle, hP _⟩
  | and _ | or _ | xor _ | not _ | fshl _ | fshr _ | clz _ | cls _ | rbit _ | ctz _ | popcnt _
  | select _ | ofBool _ | addc _ | subb _ | umulw _ | smulw _ | udiv0 _ | sdiv0 _
  | mkpair _ _ | unpair _ _ | bitcast _ _ _ =>
    exact hP _
  | ternlog _ _ | bswap _ | blend _ _ _ | udiv _ | sdiv _ | urem _ | srem _
  | shufd _ _ | shufb _ | alignr _ _ | blendw _ _ | sha256rnds2 | sha256msg1 | sha256msg2
  | fadd _ | fsub _ | fmul _ | fdiv _ | ffma _ | fsqrt _ | fneg _ | fabs _ | fcmp _ _ _ _
  | fptoui _ _ | fptosi _ _ | uitofp _ _ | sitofp _ _ | fcvt _ _ =>
    simp [isSafeOp] at hs

/-! ## Semantic invariant `IGood` over `FEnv` / `FKey` -/

/-- Soundness invariant on `G : Ctx (IVal Val) Val`. -/
def IGood (ρ : FEnv) (b : Nat) (G : Ctx (IVal Val) Val) : Prop :=
  ∀ p ∈ G, p.2.1.1.val = p.2.2 ∧ p.2.1.2.fev ρ = p.2.2 ∧ p.2.1.2.FLt b

theorem IGood.mono {ρ ρ' : FEnv} {b b' : Nat} {G : Ctx (IVal Val) Val}
    (hb : b ≤ b') (hρ : ∀ {u} (k : FKey u), k.FLt b → k.fev ρ' = k.fev ρ)
    (hG : IGood ρ b G) : IGood ρ' b' G := by
  intro p hp
  obtain ⟨h1, h2, h3⟩ := hG p hp
  exact ⟨h1, (hρ p.2.1.2 h3).trans h2, h3.le hb⟩

theorem IGood.upd_all {ρ : FEnv} {b : Nat} {G : Ctx (IVal Val) Val} (hG : IGood ρ b G)
    {ts : List Ty} (xs : Tup Val ts) : IGood (fupdTup ρ b xs) (b + ts.length) G :=
  hG.mono (Nat.le_add_right _ _) (fun _ hk => FKey.fev_fupdTup xs hk)

theorem IGood.append {ρ : FEnv} {b : Nat} {G₁ G₂ : Ctx (IVal Val) Val}
    (h1 : IGood ρ b G₁) (h2 : IGood ρ b G₂) : IGood ρ b (G₁ ++ G₂) := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact h1 p hp
  · exact h2 p hp

private theorem IGood.freshIVals_only (ρ : FEnv) :
    {ts : List Ty} → (xs : Tup Val ts) → (b : Nat) →
    IGood (fupdTup ρ b xs) (b + ts.length) (Tup.zip (freshIVals ts xs b) xs)
  | [], (), _ => fun _ hp => nomatch hp
  | _ :: ts, (x, xs), b => by
    simp only [freshIVals, tupFreshWith, Tup.zip, fupdTup, List.length_cons]
    intro p hp
    cases hp with
    | head =>
      refine ⟨rfl, ?_, by simp [FKey.FLt]⟩
      simp only [FKey.fev]
      rw [fupdTup_lt (fupd ρ b x) xs (by omega), fupd_eq]
    | tail _ hp =>
      have ih := IGood.freshIVals_only (fupd ρ b x) xs (b + 1) p hp
      rw [show b + 1 + ts.length = b + (ts.length + 1) by omega] at ih
      exact ih

theorem IGood.freshIVals {ρ : FEnv} {b : Nat} {G : Ctx (IVal Val) Val} (hG : IGood ρ b G)
    {ts : List Ty} (xs : Tup Val ts) :
    IGood (fupdTup ρ b xs) (b + ts.length) (Tup.zip (freshIVals ts xs b) xs ++ G) :=
  (IGood.freshIVals_only ρ xs b).append (hG.upd_all xs)

theorem IGood.freshOne {ρ : FEnv} {b : Nat} {G : Ctx (IVal Val) Val} (hG : IGood ρ b G)
    {t : Ty} (v : Val t) :
    IGood (fupd ρ b v) (b + 1) (⟨t, (.var v, .var b), v⟩ :: G) :=
  hG.freshIVals (ts := [t]) (v, ())

theorem argRel_iout_val {G : Ctx (IVal Val) Val} {ρ : FEnv} {b : Nat} (hG : IGood ρ b G)
    {t : Ty} {a₁ : Arg (IVal Val) t} {a₂ : Arg Val t} :
    ArgRel G t a₁ a₂ → (iout a₁).val = a₂.val
  | .var h => (hG _ h).1
  | .imm _ => rfl

theorem TRel.iout_vals {G : Ctx (IVal Val) Val} {ρ : FEnv} {b : Nat} (hG : IGood ρ b G)
    {ts : List Ty} {as₁ : Tup (Arg (IVal Val)) ts} {as₂ : Tup (Arg Val) ts}
    (h : TRel (ArgRel G) as₁ as₂) : vals (tupIOut as₁) = vals as₂ :=
  TRel.tupMapArg_vals (fun _ => iout) (fun ha => argRel_iout_val hG ha) h

/-! ## `IArgGood` and `emitSelectTy` / `emitSelectTup` WP soundness -/

def IArgGood (ρ : FEnv) (b : Nat) {t : Ty} (a : Arg (IVal Val) t) (v : Val t) : Prop :=
  (iout a).val = v ∧ (ikey a).fev ρ = v ∧ (ikey a).FLt b

theorem iargGood_mono {ρ ρ' : FEnv} {b₁ b₂ : Nat} (hb : b₁ ≤ b₂)
    (hρ : ∀ {u} (k : FKey u), k.FLt b₁ → k.fev ρ' = k.fev ρ)
    {t : Ty} {a : Arg (IVal Val) t} {v : Val t} (h : IArgGood ρ b₁ a v) :
    IArgGood ρ' b₂ a v :=
  ⟨h.1, (hρ (ikey a) h.2.2).trans h.2.1, h.2.2.le hb⟩

theorem argRel_iargGood {G : Ctx (IVal Val) Val} {ρ : FEnv} {b : Nat} (hG : IGood ρ b G)
    {t : Ty} {a₁ : Arg (IVal Val) t} {a₂ : Arg Val t} :
    ArgRel G t a₁ a₂ → IArgGood ρ b a₁ a₂.val
  | .var h => hG _ h
  | .imm _ => ⟨rfl, rfl, trivial⟩

def IArgsGood (ρ : FEnv) (b : Nat) :
    {ts : List Ty} → Tup (Arg (IVal Val)) ts → Tup Val ts → Prop
  | [], (), () => True
  | _ :: _, (a, as), (v, vs) => IArgGood ρ b a v ∧ IArgsGood ρ b as vs

theorem IArgsGood.of_trel {G : Ctx (IVal Val) Val} {ρ : FEnv} {b : Nat} (hG : IGood ρ b G) :
    {ts : List Ty} → {as₁ : Tup (Arg (IVal Val)) ts} → {as₂ : Tup (Arg Val) ts} →
    TRel (ArgRel G) as₁ as₂ → IArgsGood ρ b as₁ (vals as₂)
  | [], (), (), .nil => trivial
  | _ :: _, (_, _), (_, _), .cons ha has => ⟨argRel_iargGood hG ha, IArgsGood.of_trel hG has⟩

theorem iargsGood_mono {ρ ρ' : FEnv} {b₁ b₂ : Nat} (hb : b₁ ≤ b₂)
    (hρ : ∀ {u} (k : FKey u), k.FLt b₁ → k.fev ρ' = k.fev ρ) :
    {ts : List Ty} → {as : Tup (Arg (IVal Val)) ts} → {vs : Tup Val ts} →
    IArgsGood ρ b₁ as vs → IArgsGood ρ' b₂ as vs
  | [], (), (), _ => trivial
  | _ :: _, (_, _), (_, _), ⟨ha, has⟩ =>
    ⟨iargGood_mono hb hρ ha, iargsGood_mono hb hρ has⟩

private theorem mkPairArg_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {a b : Ty} (x : Arg Val a) (y : Arg Val b) {cont : Arg Val (.pair a b) → Expr Val Cont rs}
    (h : ∀ p : Arg Val (.pair a b), p.val = (x.val, y.val) → wp Γ Q X (cont p) m) :
    wp Γ Q X (mkPairArg x y cont) m := by
  cases x <;> cases y <;> simp only [mkPairArg]
  · exact h _ rfl
  · exact h _ rfl
  · exact h _ rfl
  · exact h _ rfl

private theorem splitPairIVal_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {a b : Ty} (ρ : FEnv) (next : Nat) (p : Arg (IVal Val) (.pair a b)) (v : Val (.pair a b))
    (hp : IArgGood ρ next p v)
    {cont : Nat → Arg (IVal Val) a → Arg (IVal Val) b → Expr Val Cont rs}
    (hcont : ∀ (ρ' : FEnv) (next' : Nat) (p₁ : Arg (IVal Val) a) (p₂ : Arg (IVal Val) b),
      next ≤ next' → (∀ {u} (k : FKey u), k.FLt next → k.fev ρ' = k.fev ρ) →
      IArgGood ρ' next' p₁ v.1 → IArgGood ρ' next' p₂ v.2 →
      wp Γ Q X (cont next' p₁ p₂) m) :
    wp Γ Q X (splitPairIVal next p cont) m := by
  unfold splitPairIVal
  cases hio : iout p with
  | imm c =>
    rcases c with ⟨c₁, c₂⟩
    have hv : (c₁, c₂) = v := by rw [← hp.1, hio]; rfl
    have hc₁ : c₁ = v.1 := congrArg Prod.fst hv
    have hc₂ : c₂ = v.2 := congrArg Prod.snd hv
    exact hcont ρ next (.imm c₁) (.imm c₂) (Nat.le_refl _) (fun _ _ => rfl)
      ⟨hc₁, hc₁, trivial⟩ ⟨hc₂, hc₂, trivial⟩
  | var w =>
    simp only [wp_let_op1, OpCode.wp_unpair]
    have hw : w = v := by rw [← hp.1, hio]; rfl
    subst hw
    let ρ' := fupd (fupd ρ next w.1) (next + 1) w.2
    refine hcont ρ' (next + 2) (.var (.var w.1, .var next)) (.var (.var w.2, .var (next + 1)))
      (by omega) (fun {u} k hk => ?_) ?_ ?_
    · rw [FKey.fev_fupd _ (hk.le (by omega)), FKey.fev_fupd _ hk]
    · refine ⟨rfl, ?_, show next < next + 2 by omega⟩
      simp only [ikey, FKey.fev, ρ']
      rw [fupd_ne _ _ (by omega), fupd_eq]
    · refine ⟨rfl, ?_, show next + 1 < next + 2 by omega⟩
      simp only [ikey, FKey.fev, ρ']
      rw [fupd_eq]

private theorem emitSelectTy_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (c : Arg Val .bool) :
    (t : Ty) → isSelectTy t = true →
    (ρ : FEnv) → (next : Nat) →
    {aT aE : Arg (IVal Val) t} → {vT vE : Val t} →
    IArgGood ρ next aT vT → IArgGood ρ next aE vE →
    {cont : Nat → Arg Val t → Expr Val Cont rs} →
    (∀ next' (r : Arg Val t), next ≤ next' →
      r.val = (if c.val then vT else vE) → wp Γ Q X (cont next' r) m) →
    wp Γ Q X (emitSelectTy c t next aT aE cont) m
  | .bool, _, ρ, next, aT, aE, vT, vE, hT, hE, cont, hcont
  | .bits _, _, ρ, next, aT, aE, vT, vE, hT, hE, cont, hcont => by
    simp only [emitSelectTy]
    cases hbeq : fKeyBeq (ikey aT) (ikey aE)
    · simp only [Bool.false_eq_true, ↓reduceIte, wp_let_op3, OpCode.wp_select]
      exact hcont next _ (Nat.le_refl _) (by rw [hT.1, hE.1]; rfl)
    · have heq : ikey aT = ikey aE := fKeyBeq_iff_eq.1 hbeq
      have hveq : vT = vE := by rw [← hT.2.1, heq, hE.2.1]
      simp only [↓reduceIte]
      exact hcont next _ (Nat.le_refl _) (by rw [hT.1, hveq]; cases c.val <;> rfl)
  | .float _, ht, _, _, _, _, _, _, _, _, _, _ => by simp [isSelectTy, Ty.hasFloat] at ht
  | .pair a b, ht, ρ, next, aT, aE, vT, vE, hT, hE, cont, hcont => by
    simp only [isSelectTy, Ty.hasFloat, Bool.or_eq_false_iff, Bool.not_eq_true'] at ht
    have hta : isSelectTy a = true := by simp [isSelectTy, ht.1]
    have htb : isSelectTy b = true := by simp [isSelectTy, ht.2]
    simp only [emitSelectTy]
    cases hbeq : fKeyBeq (ikey aT) (ikey aE)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine splitPairIVal_wp ρ next aT vT hT fun ρ₁ next₁ aT₁ aT₂ hle₁ hev₁ hT₁ hT₂ => ?_
      have hE' := iargGood_mono hle₁ hev₁ hE
      refine splitPairIVal_wp ρ₁ next₁ aE vE hE' fun ρ₂ next₂ aE₁ aE₂ hle₂ hev₂ hE₁ hE₂ => ?_
      have hT₁' := iargGood_mono hle₂ hev₂ hT₁
      have hT₂' := iargGood_mono hle₂ hev₂ hT₂
      refine emitSelectTy_wp c a hta ρ₂ next₂ hT₁' hE₁ fun next₃ r₁ hle₃ hr₁ => ?_
      refine emitSelectTy_wp c b htb ρ₂ next₃ (iargGood_mono hle₃ (fun _ _ => rfl) hT₂')
        (iargGood_mono hle₃ (fun _ _ => rfl) hE₂) fun next₄ r₂ hle₄ hr₂ => ?_
      refine mkPairArg_wp r₁ r₂ fun r hr => ?_
      refine hcont next₄ r (Nat.le_trans hle₁ (Nat.le_trans hle₂ (Nat.le_trans hle₃ hle₄))) ?_
      rw [hr, hr₁, hr₂]
      cases c.val <;> rfl
    · have heq : ikey aT = ikey aE := fKeyBeq_iff_eq.1 hbeq
      have hveq : vT = vE := by rw [← hT.2.1, heq, hE.2.1]
      simp only [↓reduceIte]
      exact hcont next _ (Nat.le_refl _) (by rw [hT.1, hveq]; cases c.val <;> rfl)

theorem emitSelectTup_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (c : Arg Val .bool) :
    (ts : List Ty) → isSelectSig ts = true → (ρ : FEnv) → (next : Nat) →
    {asT asE : Tup (Arg (IVal Val)) ts} → {vsT vsE : Tup Val ts} →
    IArgsGood ρ next asT vsT → IArgsGood ρ next asE vsE →
    {cont : Tup (Arg Val) ts → Expr Val Cont rs} →
    (∀ (sel : Tup (Arg Val) ts),
      vals sel = (if c.val then vsT else vsE) → wp Γ Q X (cont sel) m) →
    wp Γ Q X (emitSelectTup c ts next asT asE cont) m
  | [], _, _, _, (), (), (), (), _, _, _, hcont => hcont () (by cases c.val <;> rfl)
  | t :: ts, hts, ρ, next, (aT, asT), (aE, asE), (vT, vsT), (vE, vsE),
    ⟨haT, hasT⟩, ⟨haE, hasE⟩, cont, hcont => by
    simp only [isSelectSig, List.all_cons, Bool.and_eq_true] at hts
    simp only [emitSelectTup]
    refine emitSelectTy_wp c t hts.1 ρ next haT haE fun next' r hle hr => ?_
    refine emitSelectTup_wp c ts hts.2 ρ next' (iargsGood_mono hle (fun _ _ => rfl) hasT)
      (iargsGood_mono hle (fun _ _ => rfl) hasE) fun rs' hrs' => ?_
    exact hcont (r, rs') (by simp only [vals, hr, hrs']; cases c.val <;> rfl)

private theorem isSelectTyWith_imp :
    ∀ (bitsOnly : Bool) (t : Ty), isSelectTyWith bitsOnly t = true → isSelectTy t = true
  | false, _, h => h
  | true, .bits _, _ => rfl
  | true, .bool, h | true, .float _, h | true, .pair _ _, h => by
      simp [isSelectTyWith] at h

private theorem isSelectSigWith_imp (bitsOnly : Bool) (ts : List Ty)
    (h : isSelectSigWith bitsOnly ts = true) : isSelectSig ts = true := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [isSelectSigWith, List.all_cons, Bool.and_eq_true] at h
    simp only [isSelectSig, List.all_cons, Bool.and_eq_true]
    exact ⟨isSelectTyWith_imp bitsOnly t h.1, ih h.2⟩

/-! ## `emitSelectTy` / `emitSelectTup` WF preservation -/

section WfSelect
variable {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}

def IValRel (G' : Ctx V₁ V₂) {t : Ty} (a₁ : IVal V₁ t) (a₂ : IVal V₂ t) : Prop :=
  ArgRel G' t a₁.1 a₂.1 ∧ a₁.2 = a₂.2

theorem IValRel.weaken {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂)
    {t : Ty} {a₁ : IVal V₁ t} {a₂ : IVal V₂ t} (h : IValRel G₁ a₁ a₂) : IValRel G₂ a₁ a₂ :=
  ⟨h.1.weaken hsub, h.2⟩

def IRelG (G' : Ctx V₁ V₂) (G : Ctx (IVal V₁) (IVal V₂)) : Prop :=
  ∀ p ∈ G, IValRel G' p.2.1 p.2.2

theorem IRelG.weaken {G₁ G₂ : Ctx V₁ V₂} {G : Ctx (IVal V₁) (IVal V₂)}
    (hG : IRelG G₁ G) (hsub : ∀ p ∈ G₁, p ∈ G₂) : IRelG G₂ G :=
  fun p hp => (hG p hp).weaken hsub

theorem IRelG.cons {G' : Ctx V₁ V₂} {G : Ctx (IVal V₁) (IVal V₂)} (hG : IRelG G' G)
    {t : Ty} {a₁ : IVal V₁ t} {a₂ : IVal V₂ t} (ha : IValRel G' a₁ a₂) :
    IRelG G' (⟨t, a₁, a₂⟩ :: G)
  | _, .head _ => ha
  | _, .tail _ hp => hG _ hp

theorem IRelG.append {G' : Ctx V₁ V₂} {G H : Ctx (IVal V₁) (IVal V₂)}
    (h1 : IRelG G' G) (h2 : IRelG G' H) : IRelG G' (H ++ G) := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact h2 p hp
  · exact h1 p hp

theorem IRelG.freshIVals_only {ts : List Ty} (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts) (b : Nat) :
    IRelG (Tup.zip xs₁ xs₂) (Tup.zip (freshIVals ts xs₁ b) (freshIVals ts xs₂ b)) :=
  mem_tup_zip_tupFreshWith
    (fun {t} (x : V₁ t) n => ((.var x, .var n) : IVal V₁ t))
    (fun {t} (x : V₂ t) n => ((.var x, .var n) : IVal V₂ t))
    (P := fun G' _ a₁ a₂ => IValRel G' a₁ a₂)
    (fun hsub _ _ _ h => h.weaken hsub)
    (fun _ _ _ => ⟨.var List.mem_cons_self, rfl⟩)
    xs₁ xs₂ b

theorem IRelG.freshIVals {G' : Ctx V₁ V₂} {G : Ctx (IVal V₁) (IVal V₂)}
    (hG : IRelG G' G) {ts : List Ty} (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts) (b : Nat) :
    IRelG (Tup.zip xs₁ xs₂ ++ G')
      (Tup.zip (freshIVals ts xs₁ b) (freshIVals ts xs₂ b) ++ G) :=
  (hG.weaken fun _ hq => List.mem_append_right _ hq).append
    ((IRelG.freshIVals_only xs₁ xs₂ b).weaken fun _ hq => List.mem_append_left G' hq)

theorem IRelG.freshOne {G' : Ctx V₁ V₂} {G : Ctx (IVal V₁) (IVal V₂)}
    (hG : IRelG G' G) {t : Ty} (v₁ : V₁ t) (v₂ : V₂ t) (b : Nat) :
    IRelG (⟨t, v₁, v₂⟩ :: G') (⟨t, (.var v₁, .var b), (.var v₂, .var b)⟩ :: G) :=
  (hG.weaken fun _ hq => List.mem_cons_of_mem _ hq).cons ⟨.var List.mem_cons_self, rfl⟩

theorem argRel_iout {G' : Ctx V₁ V₂} {G : Ctx (IVal V₁) (IVal V₂)} (hG : IRelG G' G)
    {t : Ty} {a₁ : Arg (IVal V₁) t} {a₂ : Arg (IVal V₂) t} :
    ArgRel G t a₁ a₂ → ArgRel G' t (iout a₁) (iout a₂)
  | .var h => (hG _ h).1
  | .imm c => .imm c

theorem argRel_ikey_eq {G' : Ctx V₁ V₂} {G : Ctx (IVal V₁) (IVal V₂)} (hG : IRelG G' G)
    {t : Ty} {a₁ : Arg (IVal V₁) t} {a₂ : Arg (IVal V₂) t} :
    ArgRel G t a₁ a₂ → ikey a₁ = ikey a₂
  | .var h => (hG _ h).2
  | .imm _ => rfl

theorem trel_iout {G' : Ctx V₁ V₂} {G : Ctx (IVal V₁) (IVal V₂)} (hG : IRelG G' G)
    {ts : List Ty} {as₁ : Tup (Arg (IVal V₁)) ts} {as₂ : Tup (Arg (IVal V₂)) ts}
    (h : TRel (ArgRel G) as₁ as₂) : TRel (ArgRel G') (tupIOut as₁) (tupIOut as₂) :=
  TRel.tupMapArg_rel (fun _ => IfOptImpl.iout) (fun _ => IfOptImpl.iout)
    (fun ha => argRel_iout hG ha) h

def IArgRel (G' : Ctx V₁ V₂) {t : Ty} (a₁ : Arg (IVal V₁) t) (a₂ : Arg (IVal V₂) t) : Prop :=
  ArgRel G' t (iout a₁) (iout a₂) ∧ ikey a₁ = ikey a₂

theorem iargRel_weaken {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂)
    {t : Ty} {a₁ : Arg (IVal V₁) t} {a₂ : Arg (IVal V₂) t} (h : IArgRel G₁ a₁ a₂) :
    IArgRel G₂ a₁ a₂ :=
  ⟨h.1.weaken hsub, h.2⟩

theorem argRel_iargRel {G' : Ctx V₁ V₂} {G : Ctx (IVal V₁) (IVal V₂)} (hG : IRelG G' G)
    {t : Ty} {a₁ : Arg (IVal V₁) t} {a₂ : Arg (IVal V₂) t} (h : ArgRel G t a₁ a₂) :
    IArgRel G' a₁ a₂ :=
  ⟨argRel_iout hG h, argRel_ikey_eq hG h⟩

theorem trel_iargRel {G' : Ctx V₁ V₂} {G : Ctx (IVal V₁) (IVal V₂)} (hG : IRelG G' G) :
    {ts : List Ty} → {as₁ : Tup (Arg (IVal V₁)) ts} → {as₂ : Tup (Arg (IVal V₂)) ts} →
    TRel (ArgRel G) as₁ as₂ → TRel (fun _ => IArgRel G') as₁ as₂
  | [], (), (), .nil => .nil
  | _ :: _, (_, _), (_, _), .cons ha has => .cons (argRel_iargRel hG ha) (trel_iargRel hG has)

private theorem mkPairArg_wf {rs : List Ty} {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} {a b : Ty}
    {x₁ : Arg V₁ a} {x₂ : Arg V₂ a} {y₁ : Arg V₁ b} {y₂ : Arg V₂ b}
    (hx : ArgRel G' a x₁ x₂) (hy : ArgRel G' b y₁ y₂)
    {cont₁ : Arg V₁ (.pair a b) → Expr V₁ L₁ rs} {cont₂ : Arg V₂ (.pair a b) → Expr V₂ L₂ rs}
    (hcont : ∀ G'' r₁ r₂, (∀ p ∈ G', p ∈ G'') → ArgRel G'' (.pair a b) r₁ r₂ →
      Wf G'' D' (cont₁ r₁) (cont₂ r₂)) :
    Wf G' D' (mkPairArg x₁ y₁ cont₁) (mkPairArg x₂ y₂ cont₂) := by
  cases hx with
  | imm cx =>
    cases hy with
    | imm cy =>
      exact hcont G' (.imm (cx, cy)) (.imm (cx, cy)) (fun _ h => h) (.imm (t := .pair a b) (cx, cy))
    | var hy' =>
      refine .let_ (.mk (.mkpair a b) (.cons (.imm cx) (.cons (.var hy') .nil)))
        fun (p₁, ()) (p₂, ()) => ?_
      exact hcont _ (.var p₁) (.var p₂) (fun _ hq => List.mem_cons_of_mem _ hq)
        (.var List.mem_cons_self)
  | var hx' =>
    cases hy with
    | imm cy =>
      refine .let_ (.mk (.mkpair a b) (.cons (.var hx') (.cons (.imm cy) .nil)))
        fun (p₁, ()) (p₂, ()) => ?_
      exact hcont _ (.var p₁) (.var p₂) (fun _ hq => List.mem_cons_of_mem _ hq)
        (.var List.mem_cons_self)
    | var hy' =>
      refine .let_ (.mk (.mkpair a b) (.cons (.var hx') (.cons (.var hy') .nil)))
        fun (p₁, ()) (p₂, ()) => ?_
      exact hcont _ (.var p₁) (.var p₂) (fun _ hq => List.mem_cons_of_mem _ hq)
        (.var List.mem_cons_self)

private theorem splitPairIVal_wf {rs : List Ty} {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} {a b : Ty}
    (next : Nat) {p₁ : Arg (IVal V₁) (.pair a b)} {p₂ : Arg (IVal V₂) (.pair a b)}
    (hp : IArgRel G' p₁ p₂)
    {cont₁ : Nat → Arg (IVal V₁) a → Arg (IVal V₁) b → Expr V₁ L₁ rs}
    {cont₂ : Nat → Arg (IVal V₂) a → Arg (IVal V₂) b → Expr V₂ L₂ rs}
    (hcont : ∀ G'' next' a₁ a₂ b₁ b₂, (∀ p ∈ G', p ∈ G'') →
      IArgRel G'' a₁ a₂ → IArgRel G'' b₁ b₂ →
      Wf G'' D' (cont₁ next' a₁ b₁) (cont₂ next' a₂ b₂)) :
    Wf G' D' (splitPairIVal next p₁ cont₁) (splitPairIVal next p₂ cont₂) := by
  have hio := hp.1
  simp only [splitPairIVal]
  cases ho1 : iout p₁ <;> cases ho2 : iout p₂ <;> rw [ho1, ho2] at hio
  · next v₁ v₂ =>
    have hv : ⟨.pair a b, v₁, v₂⟩ ∈ G' := ArgRel.var_iff.1 hio
    refine .let_ (.mk (.unpair a b) (.cons (.var hv) .nil)) fun (x₁, y₁, ()) (x₂, y₂, ()) => ?_
    refine hcont (Tup.zip (as := [a, b]) (x₁, y₁, ()) (x₂, y₂, ()) ++ G') (next + 2) _ _ _ _
      (fun _ hq => List.mem_append_right _ hq) ?_ ?_
    · exact ⟨.var List.mem_cons_self, rfl⟩
    · exact ⟨.var (List.mem_cons_of_mem _ List.mem_cons_self), rfl⟩
  · cases hio
  · cases hio
  · next c₁ c₂ =>
    cases ArgRel.imm_iff.1 hio
    exact hcont G' next _ _ _ _ (fun _ h => h) ⟨.imm c₁.1, rfl⟩ ⟨.imm c₁.2, rfl⟩

private theorem emitSelectTy_wf {rs : List Ty} {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂}
    {c₁ : Arg V₁ .bool} {c₂ : Arg V₂ .bool} (hc : ArgRel G' .bool c₁ c₂) :
    (t : Ty) → (next : Nat) →
    {aT₁ aE₁ : Arg (IVal V₁) t} → {aT₂ aE₂ : Arg (IVal V₂) t} →
    IArgRel G' aT₁ aT₂ → IArgRel G' aE₁ aE₂ →
    {cont₁ : Nat → Arg V₁ t → Expr V₁ L₁ rs} →
    {cont₂ : Nat → Arg V₂ t → Expr V₂ L₂ rs} →
    (∀ G'' next' r₁ r₂, (∀ p ∈ G', p ∈ G'') → ArgRel G'' t r₁ r₂ →
      Wf G'' D' (cont₁ next' r₁) (cont₂ next' r₂)) →
    Wf G' D' (emitSelectTy c₁ t next aT₁ aE₁ cont₁) (emitSelectTy c₂ t next aT₂ aE₂ cont₂)
  | .bool, next, aT₁, aE₁, aT₂, aE₂, hT, hE, cont₁, cont₂, hcont
  | .bits _, next, aT₁, aE₁, aT₂, aE₂, hT, hE, cont₁, cont₂, hcont => by
    simp only [emitSelectTy, hT.2, hE.2]
    cases fKeyBeq (ikey aT₂) (ikey aE₂)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine .let_ (.mk (.select _) (.cons hc (.cons hT.1 (.cons hE.1 .nil))))
        fun (r₁, ()) (r₂, ()) => ?_
      exact hcont _ next (.var r₁) (.var r₂) (fun _ hq => List.mem_cons_of_mem _ hq)
        (.var List.mem_cons_self)
    · exact hcont G' next (iout aT₁) (iout aT₂) (fun _ h => h) hT.1
  | .float _, next, _, _, _, _, hT, _, _, _, hcont =>
    hcont G' next _ _ (fun _ h => h) hT.1
  | .pair a b, next, aT₁, aE₁, aT₂, aE₂, hT, hE, cont₁, cont₂, hcont => by
    simp only [emitSelectTy, hT.2, hE.2]
    cases fKeyBeq (ikey aT₂) (ikey aE₂)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine splitPairIVal_wf next hT fun G₁ next₁ aT₁₁ aT₂₁ aT₁₂ aT₂₂ hsub₁ hT₁ hT₂ => ?_
      refine splitPairIVal_wf next₁ (iargRel_weaken hsub₁ hE)
        fun G₂ next₂ aE₁₁ aE₂₁ aE₁₂ aE₂₂ hsub₂ hE₁ hE₂ => ?_
      have hc₂ := hc.weaken (fun p hp => hsub₂ p (hsub₁ p hp))
      refine emitSelectTy_wf hc₂ a next₂ (iargRel_weaken hsub₂ hT₁) hE₁
        fun G₃ next₃ r₁₁ r₂₁ hsub₃ hr₁ => ?_
      have hc₃ := hc₂.weaken hsub₃
      refine emitSelectTy_wf hc₃ b next₃
        (iargRel_weaken (fun p hp => hsub₃ p (hsub₂ p hp)) hT₂) (iargRel_weaken hsub₃ hE₂)
        fun G₄ next₄ r₁₂ r₂₂ hsub₄ hr₂ => ?_
      refine mkPairArg_wf (hr₁.weaken hsub₄) hr₂ fun G₅ r₁ r₂ hsub₅ hr => ?_
      exact hcont G₅ next₄ r₁ r₂
        (fun p hp => hsub₅ p (hsub₄ p (hsub₃ p (hsub₂ p (hsub₁ p hp))))) hr
    · exact hcont G' next (iout aT₁) (iout aT₂) (fun _ h => h) hT.1

private theorem emitSelectTup_wf {rs : List Ty} {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂}
    {c₁ : Arg V₁ .bool} {c₂ : Arg V₂ .bool} (hc : ArgRel G' .bool c₁ c₂) :
    (ts : List Ty) → (next : Nat) →
    {asT₁ asE₁ : Tup (Arg (IVal V₁)) ts} → {asT₂ asE₂ : Tup (Arg (IVal V₂)) ts} →
    TRel (fun _ => IArgRel G') asT₁ asT₂ → TRel (fun _ => IArgRel G') asE₁ asE₂ →
    {cont₁ : Tup (Arg V₁) ts → Expr V₁ L₁ rs} →
    {cont₂ : Tup (Arg V₂) ts → Expr V₂ L₂ rs} →
    (∀ G'' sel₁ sel₂, (∀ p ∈ G', p ∈ G'') → TRel (ArgRel G'') sel₁ sel₂ →
      Wf G'' D' (cont₁ sel₁) (cont₂ sel₂)) →
    Wf G' D' (emitSelectTup c₁ ts next asT₁ asE₁ cont₁)
             (emitSelectTup c₂ ts next asT₂ asE₂ cont₂)
  | [], _, (), (), (), (), .nil, .nil, _, _, hcont =>
    hcont G' () () (fun _ h => h) .nil
  | t :: ts, next, (aT₁, asT₁), (aE₁, asE₁), (aT₂, asT₂), (aE₂, asE₂),
    .cons hT hsT, .cons hE hsE, cont₁, cont₂, hcont => by
    simp only [emitSelectTup]
    refine emitSelectTy_wf hc t next hT hE fun G₁ next' r₁ r₂ hsub₁ hr => ?_
    have hsT' : TRel (fun _ => IArgRel G₁) asT₁ asT₂ :=
      TRel.mono (fun _ _ _ h => iargRel_weaken hsub₁ h) hsT
    have hsE' : TRel (fun _ => IArgRel G₁) asE₁ asE₂ :=
      TRel.mono (fun _ _ _ h => iargRel_weaken hsub₁ h) hsE
    refine emitSelectTup_wf (hc.weaken hsub₁) ts next' hsT' hsE'
      fun G₂ rs₁ rs₂ hsub₂ hrs => ?_
    exact hcont G₂ (r₁, rs₁) (r₂, rs₂) (fun p hp => hsub₂ p (hsub₁ p hp))
      (.cons (hr.weaken hsub₂) hrs)

/-! ## Diamond shape and check/hoist lemmas -/

private def HasArmShape {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (jTs : List Ty) :
    Nat → Expr (IVal V) (JLabel L) rs → Prop
  | 0, .jump (ts := ts) _ _ => ts = jTs
  | n + 1, .let_ _ k => ∀ xs, HasArmShape jTs n (k xs)
  | _, _ => False

private def HasDiamondShape {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (jTs : List Ty) :
    DiamondPlan → Expr (IVal V) (JLabel L) rs → Prop
  | .jnz nT nE, .jnz _ t e => HasArmShape jTs nT t ∧ HasArmShape jTs nE e
  | .let_ rest, .let_ _ k => ∀ xs, HasDiamondShape jTs rest (k xs)
  | .load rest, .load _ _ k => ∀ v, HasDiamondShape jTs rest (k v)
  | .store rest, .store _ _ k => HasDiamondShape jTs rest k
  | .call rest, .call _ _ k => ∀ xs, HasDiamondShape jTs rest (k xs)
  | _, _ => False

private theorem checkArm_eq_of_wf {G : Ctx (IVal V₁) (IVal V₂)} {D : Ctx (JLabel L₁) (JLabel L₂)}
    {rs : List Ty} (jId : Nat) (jTs : List Ty)
    (hD : ∀ p ∈ D, match p.2.1, p.2.2 with
      | .loc d₁, .loc d₂ => (d₁ == jId) = (d₂ == jId)
      | .outer _, .outer _ => True
      | _, _ => False) :
    ∀ (fuel next : Nat) {e₁ : Expr (IVal V₁) (JLabel L₁) rs}
      {e₂ : Expr (IVal V₂) (JLabel L₂) rs},
    Wf G D e₁ e₂ →
    checkArm jId jTs fuel next e₁ = checkArm jId jTs fuel next e₂
  | fuel, next, _, _, .let_ (.mk code _) hk => by
    unfold checkArm
    cases isSafeOp code
    · rfl
    · cases fuel with
      | zero => rfl
      | succ fuel' =>
        dsimp only
        exact congrArg (Option.map (· + 1))
          (checkArm_eq_of_wf jId jTs hD fuel' (next + _)
            (hk (dummyIVals _ next) (dummyIVals _ next)))
  | _, _, _, _, .jump (j₁ := j₁) (j₂ := j₂) hj _ => by
    have hjl := hD _ hj
    dsimp only at hjl
    cases j₁ <;> cases j₂ <;> simp_all [checkArm]
  | _, _, _, _, .load _ _ _ | _, _, _, _, .store _ _ _ | _, _, _, _, .call _ _ _
  | _, _, _, _, .jnz _ _ _ | _, _, _, _, .ret _ | _, _, _, _, .exit _ _
  | _, _, _, _, .hlt | _, _, _, _, .group _ _ => by simp [checkArm]

private theorem checkDiamond_eq_of_wf {G : Ctx (IVal V₁) (IVal V₂)}
    {D : Ctx (JLabel L₁) (JLabel L₂)} {rs : List Ty}
    (bitsOnly : Bool) (jId : Nat) (jTs : List Ty)
    (hD : ∀ p ∈ D, match p.2.1, p.2.2 with
      | .loc d₁, .loc d₂ => (d₁ == jId) = (d₂ == jId)
      | .outer _, .outer _ => True
      | _, _ => False) :
    ∀ (next : Nat) {e₁ : Expr (IVal V₁) (JLabel L₁) rs}
      {e₂ : Expr (IVal V₂) (JLabel L₂) rs},
    Wf G D e₁ e₂ →
    checkDiamondWith bitsOnly jId jTs next e₁ = checkDiamondWith bitsOnly jId jTs next e₂
  | next, _, _, .let_ _ hk => by
    dsimp only [checkDiamondWith]
    exact congrArg (Option.map DiamondPlan.let_)
      (checkDiamond_eq_of_wf bitsOnly jId jTs hD (next + _)
        (hk (dummyIVals _ next) (dummyIVals _ next)))
  | next, _, _, .load _ _ hk => by
    dsimp only [checkDiamondWith]
    exact congrArg (Option.map DiamondPlan.load)
      (checkDiamond_eq_of_wf bitsOnly jId jTs hD (next + 1)
        (hk (.imm default, .var next) (.imm default, .var next)))
  | next, _, _, .store _ _ hk => by
    dsimp only [checkDiamondWith]
    exact congrArg (Option.map DiamondPlan.store)
      (checkDiamond_eq_of_wf bitsOnly jId jTs hD next hk)
  | next, _, _, .call _ _ hk => by
    dsimp only [checkDiamondWith]
    exact congrArg (Option.map DiamondPlan.call)
      (checkDiamond_eq_of_wf bitsOnly jId jTs hD (next + _)
        (hk (dummyIVals _ next) (dummyIVals _ next)))
  | next, _, _, .jnz _ ht he => by
    dsimp only [checkDiamondWith]
    rw [checkArm_eq_of_wf jId jTs hD 4 next ht, checkArm_eq_of_wf jId jTs hD 4 next he]
  | _, _, _, .jump _ _ | _, _, _, .ret _ | _, _, _, .exit _ _
  | _, _, _, .hlt | _, _, _, .group _ _ => rfl

private theorem hasArmShape_of_checkArm {rs : List Ty} (jId : Nat) (jTs : List Ty) :
    ∀ (fuel next n : Nat) {G : Ctx (IVal V₁) (IVal V₂)} {D : Ctx (JLabel L₁) (JLabel L₂)}
      {e₁ : Expr (IVal V₁) (JLabel L₁) rs} {e₂ : Expr (IVal V₂) (JLabel L₂) rs},
    Wf G D e₁ e₂ → checkArm jId jTs fuel next e₁ = some n → HasArmShape jTs n e₂
  | fuel, next, n, _, _, _, _, .let_ (.mk code _) hk, hc => by
    unfold checkArm at hc
    cases hs : isSafeOp code <;> rw [hs] at hc
    · simp at hc
    · cases fuel with
      | zero => simp at hc
      | succ fuel' =>
        simp only [↓reduceIte, Option.map_eq_some_iff] at hc
        rcases hc with ⟨m, hm, rfl⟩
        exact fun xs₂ => hasArmShape_of_checkArm jId jTs fuel' (next + _) m
          (hk (dummyIVals _ next) xs₂) hm
  | _, _, n, _, _, _, _, .jump (ts := ts) (j₁ := j₁) _ _, hc => by
    cases j₁ with
    | outer _ => simp [checkArm] at hc
    | loc id =>
      simp only [checkArm] at hc
      split at hc
      · simp only [Option.some.injEq] at hc
        subst hc
        rename_i hcond
        simp only [Bool.and_eq_true, Ty.listBeq_iff_eq] at hcond
        exact hcond.2
      · simp at hc
  | _, _, _, _, _, _, _, .load _ _ _, hc | _, _, _, _, _, _, _, .store _ _ _, hc
  | _, _, _, _, _, _, _, .call _ _ _, hc | _, _, _, _, _, _, _, .jnz _ _ _, hc
  | _, _, _, _, _, _, _, .ret _, hc | _, _, _, _, _, _, _, .exit _ _, hc
  | _, _, _, _, _, _, _, .hlt, hc | _, _, _, _, _, _, _, .group _ _, hc => by
    simp [checkArm] at hc

private theorem checkDiamond_peel_of_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {rs : List Ty} (bitsOnly : Bool) (jId : Nat) (jTs : List Ty)
    {D : Ctx (JLabel L₁) L₂}
    (P : DiamondPlan → Expr V₂ L₂ rs → Prop)
    (hlet : ∀ {rest ts op k},
      (∀ xs, P rest (k xs)) → P (.let_ rest) (.let_ (ts := ts) op k))
    (hload : ∀ {rest t a k}, (∀ v, P rest (k v)) → P (.load rest) (.load t a k))
    (hstore : ∀ {rest t v a k}, P rest k → P (.store rest) (.store (t := t) v a k))
    (hcall : ∀ {rest f as bs args k},
      (∀ xs, P rest (k xs)) → P (.call rest) (.call f (as := as) (bs := bs) args k))
    (hjnz : ∀ {nT nE c G} {t₁ e₁ : Expr (IVal V₁) (JLabel L₁) rs}
      {t₂ e₂ : Expr V₂ L₂ rs},
      Wf G D t₁ t₂ → Wf G D e₁ e₂ →
      isSelectSigWith bitsOnly jTs = true →
      (∃ next, checkArm jId jTs 4 next t₁ = some nT ∧
        checkArm jId jTs 4 next e₁ = some nE) →
      P (.jnz nT nE) (.jnz c t₂ e₂)) :
    ∀ (next : Nat) (plan : DiamondPlan) {G : Ctx (IVal V₁) V₂}
      {e₁ : Expr (IVal V₁) (JLabel L₁) rs} {e₂ : Expr V₂ L₂ rs},
    Wf G D e₁ e₂ → checkDiamondWith bitsOnly jId jTs next e₁ = some plan → P plan e₂
  | next, _, _, _, _, .let_ _ hk, hc => by
    simp only [checkDiamondWith, Option.map_eq_some_iff] at hc
    rcases hc with ⟨rest, hr, rfl⟩
    exact hlet fun xs₂ =>
      checkDiamond_peel_of_wf bitsOnly jId jTs P hlet hload hstore hcall hjnz
        (next + _) rest (hk (dummyIVals _ next) xs₂) hr
  | next, _, _, _, _, .load _ _ hk, hc => by
    simp only [checkDiamondWith, Option.map_eq_some_iff] at hc
    rcases hc with ⟨rest, hr, rfl⟩
    exact hload fun v₂ =>
      checkDiamond_peel_of_wf bitsOnly jId jTs P hlet hload hstore hcall hjnz
        (next + 1) rest (hk (.imm default, .var next) v₂) hr
  | next, _, _, _, _, .store _ _ hk, hc => by
    simp only [checkDiamondWith, Option.map_eq_some_iff] at hc
    rcases hc with ⟨rest, hr, rfl⟩
    exact hstore
      (checkDiamond_peel_of_wf bitsOnly jId jTs P hlet hload hstore hcall hjnz
        next rest hk hr)
  | next, _, _, _, _, .call _ _ hk, hc => by
    simp only [checkDiamondWith, Option.map_eq_some_iff] at hc
    rcases hc with ⟨rest, hr, rfl⟩
    exact hcall fun xs₂ =>
      checkDiamond_peel_of_wf bitsOnly jId jTs P hlet hload hstore hcall hjnz
        (next + _) rest (hk (dummyIVals _ next) xs₂) hr
  | next, _, _, .jnz _ t₁ e₁, _, .jnz _ ht he, hc => by
    dsimp only [checkDiamondWith] at hc
    cases hsel : isSelectSigWith bitsOnly jTs <;> rw [hsel] at hc
    · simp at hc
    · cases h1 : checkArm jId jTs 4 next t₁ <;> cases h2 : checkArm jId jTs 4 next e₁ <;>
        simp [h1, h2] at hc
      · subst hc
        exact hjnz ht he hsel ⟨next, h1, h2⟩
  | _, _, _, _, _, .jump _ _, hc | _, _, _, _, _, .ret _, hc
  | _, _, _, _, _, .exit _ _, hc | _, _, _, _, _, .hlt, hc
  | _, _, _, _, _, .group _ _, hc => by
    simp [checkDiamondWith] at hc

private theorem hasDiamondShape_of_checkDiamond {rs : List Ty}
    (bitsOnly : Bool) (jId : Nat) (jTs : List Ty)
    (next : Nat) (plan : DiamondPlan) {G : Ctx (IVal V₁) (IVal V₂)}
    {D : Ctx (JLabel L₁) (JLabel L₂)}
    {e₁ : Expr (IVal V₁) (JLabel L₁) rs} {e₂ : Expr (IVal V₂) (JLabel L₂) rs}
    (hwf : Wf G D e₁ e₂) (hc : checkDiamondWith bitsOnly jId jTs next e₁ = some plan) :
    HasDiamondShape jTs plan e₂ :=
  checkDiamond_peel_of_wf bitsOnly jId jTs (HasDiamondShape jTs)
    (fun h => h) (fun h => h) (fun h => h) (fun h => h)
    (fun ht he _ ⟨_, h1, h2⟩ =>
      ⟨hasArmShape_of_checkArm jId jTs 4 _ _ ht h1,
       hasArmShape_of_checkArm jId jTs 4 _ _ he h2⟩)
    next plan hwf hc

private theorem hasArmShape_of_rhs {rs : List Ty} (jTs : List Ty) :
    ∀ (n : Nat) {G : Ctx (IVal V₁) (IVal V₂)} {D : Ctx (JLabel L₁) (JLabel L₂)}
      {e₁ : Expr (IVal V₁) (JLabel L₁) rs} {e₂ : Expr (IVal V₂) (JLabel L₂) rs},
    Wf G D e₁ e₂ → HasArmShape jTs n e₂ → HasArmShape jTs n e₁
  | 0, _, _, _, e₂, hwf, h => by
    cases e₂ with
    | jump _ _ => rcases hwf.rhs_jump with ⟨_, _, rfl, _, _⟩; exact h
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | ret _ | exit _ _
    | hlt | group _ _ => exact False.elim h
  | n + 1, _, _, _, e₂, hwf, h => by
    cases e₂ with
    | let_ _ _ =>
      rcases hwf.rhs_let with ⟨_, _, rfl, _, hk⟩
      exact fun xs₁ => hasArmShape_of_rhs jTs n (hk xs₁ (dummyIVals _ 0)) (h (dummyIVals _ 0))
    | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _
    | hlt | group _ _ => exact False.elim h

private theorem hasDiamondShape_of_rhs {rs : List Ty} (jTs : List Ty) :
    ∀ (plan : DiamondPlan) {G : Ctx (IVal V₁) (IVal V₂)} {D : Ctx (JLabel L₁) (JLabel L₂)}
      {e₁ : Expr (IVal V₁) (JLabel L₁) rs} {e₂ : Expr (IVal V₂) (JLabel L₂) rs},
    Wf G D e₁ e₂ → HasDiamondShape jTs plan e₂ → HasDiamondShape jTs plan e₁
  | .jnz nT nE, _, _, _, e₂, hwf, h => by
    cases e₂ with
    | jnz _ _ _ =>
      rcases hwf.rhs_jnz with ⟨_, _, _, rfl, _, ht, he⟩
      exact ⟨hasArmShape_of_rhs jTs nT ht h.1, hasArmShape_of_rhs jTs nE he h.2⟩
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jump _ _ | ret _ | exit _ _
    | hlt | group _ _ => exact False.elim h
  | .let_ rest, _, _, _, e₂, hwf, h => by
    cases e₂ with
    | let_ _ _ =>
      rcases hwf.rhs_let with ⟨_, _, rfl, _, hk⟩
      exact fun xs₁ =>
        hasDiamondShape_of_rhs jTs rest (hk xs₁ (dummyIVals _ 0)) (h (dummyIVals _ 0))
    | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _
    | hlt | group _ _ => exact False.elim h
  | .load rest, _, _, _, e₂, hwf, h => by
    cases e₂ with
    | load _ _ _ =>
      rcases hwf.rhs_load with ⟨_, _, rfl, _, hk⟩
      exact fun v₁ => hasDiamondShape_of_rhs jTs rest (hk v₁ (.imm default, .var 0))
        (h (.imm default, .var 0))
    | let_ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _
    | hlt | group _ _ => exact False.elim h
  | .store rest, _, _, _, e₂, hwf, h => by
    cases e₂ with
    | store _ _ _ =>
      rcases hwf.rhs_store with ⟨_, _, _, rfl, _, _, hk⟩
      exact hasDiamondShape_of_rhs jTs rest hk h
    | let_ _ _ | load _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _
    | hlt | group _ _ => exact False.elim h
  | .call rest, _, _, _, e₂, hwf, h => by
    cases e₂ with
    | call _ _ _ =>
      rcases hwf.rhs_call with ⟨_, _, rfl, _, hk⟩
      exact fun xs₁ =>
        hasDiamondShape_of_rhs jTs rest (hk xs₁ (dummyIVals _ 0)) (h (dummyIVals _ 0))
    | let_ _ _ | load _ _ _ | store _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _
    | hlt | group _ _ => exact False.elim h

private theorem hoistArm_jump_eq {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (ts : List Ty) (next : Nat) (j : JLabel L ts) (args : Tup (Arg (IVal V)) ts)
    (cont : Nat → Tup (Arg (IVal V)) ts → Expr V L rs) :
    hoistArm ts 0 next (.jump j args) cont = cont next args := by
  simp only [hoistArm]
  cases listTyDecEq ts ts with
  | isFalse hne => exact absurd rfl hne
  | isTrue _ => rfl

private theorem hoistArm_wf {rs : List Ty} (jTs : List Ty) {D' : Ctx L₁ L₂} :
    ∀ (n next : Nat) {G : Ctx (IVal V₁) (IVal V₂)} {G' : Ctx V₁ V₂}
      {D : Ctx (JLabel L₁) (JLabel L₂)}
      {e₁ : Expr (IVal V₁) (JLabel L₁) rs} {e₂ : Expr (IVal V₂) (JLabel L₂) rs},
    Wf G D e₁ e₂ → HasArmShape jTs n e₁ → IRelG G' G →
    {cont₁ : Nat → Tup (Arg (IVal V₁)) jTs → Expr V₁ L₁ rs} →
    {cont₂ : Nat → Tup (Arg (IVal V₂)) jTs → Expr V₂ L₂ rs} →
    (∀ G'' next' args₁ args₂, (∀ p ∈ G', p ∈ G'') → IRelG G'' G →
      TRel (fun _ => IArgRel G'') args₁ args₂ →
      Wf G'' D' (cont₁ next' args₁) (cont₂ next' args₂)) →
    Wf G' D' (hoistArm jTs n next e₁ cont₁) (hoistArm jTs n next e₂ cont₂)
  | 0, next, G, G', D, _, _, hwf, hsh, hG, cont₁, cont₂, hcont => by
    cases hwf with
    | @jump _ _ ts j₁ j₂ args₁ args₂ _ hargs =>
      dsimp only [HasArmShape] at hsh
      subst hsh
      rw [hoistArm_jump_eq, hoistArm_jump_eq]
      exact hcont G' next args₁ args₂ (fun _ h => h) hG (trel_iargRel hG hargs)
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsh
  | n + 1, next, G, G', D, e₁, e₂, hwf, hsh, hG, cont₁, cont₂, hcont => by
    cases hwf with
    | let_ hop hk =>
      cases hop with
      | mk code hargs =>
        simp only [hoistArm]
        refine .let_ (.mk code (trel_iout hG hargs)) fun xs₁ xs₂ => ?_
        have hG'' : IRelG (Tup.zip xs₁ xs₂ ++ G')
            (Tup.zip (freshIVals _ xs₁ next) (freshIVals _ xs₂ next) ++ G) :=
          IRelG.freshIVals hG xs₁ xs₂ next
        refine hoistArm_wf jTs n (next + _) (hk (freshIVals _ xs₁ next) (freshIVals _ xs₂ next))
          (hsh (freshIVals _ xs₁ next)) hG'' fun G₃ next' a₁ a₂ hsub hrel3 ha => ?_
        refine hcont G₃ next' a₁ a₂ (fun p hp => hsub p (List.mem_append_right _ hp)) ?_ ha
        exact fun p hp => hrel3 p (List.mem_append_right _ hp)
    | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsh

private theorem hoistDiamond_wf {rs : List Ty} {jTs : List Ty} {D' : Ctx L₁ L₂}
    {j₁ : L₁ jTs} {j₂ : L₂ jTs} (hj : ⟨jTs, j₁, j₂⟩ ∈ D') :
    ∀ (plan : DiamondPlan) (next : Nat) {G : Ctx (IVal V₁) (IVal V₂)} {G' : Ctx V₁ V₂}
      {D : Ctx (JLabel L₁) (JLabel L₂)}
      {e₁ : Expr (IVal V₁) (JLabel L₁) rs} {e₂ : Expr (IVal V₂) (JLabel L₂) rs},
    Wf G D e₁ e₂ → HasDiamondShape jTs plan e₁ → IRelG G' G →
    Wf G' D' (hoistDiamond j₁ plan next e₁) (hoistDiamond j₂ plan next e₂)
  | .jnz nT nE, next, _, G', _, _, _, hwf, hsh, hG => by
    cases hwf with
    | jnz hc ht he =>
      rcases hsh with ⟨hshT, hshE⟩
      simp only [hoistDiamond]
      refine hoistArm_wf jTs nT next ht hshT hG fun G₁ next₁ argsT₁ argsT₂ hsub₁ hG₁ hargsT => ?_
      refine hoistArm_wf jTs nE next₁ he hshE hG₁ fun G₂ next₂ argsE₁ argsE₂ hsub₂ hG₂ hargsE => ?_
      have hc₂ := (argRel_iout hG hc).weaken (fun p hp => hsub₂ p (hsub₁ p hp))
      have hargsT₂ := TRel.mono (fun _ _ _ h => iargRel_weaken hsub₂ h) hargsT
      refine emitSelectTup_wf hc₂ jTs next₂ hargsT₂ hargsE fun G₃ sel₁ sel₂ _ hsel => ?_
      exact .jump hj hsel
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsh
  | .let_ rest, next, _, G', _, _, _, hwf, hsh, hG => by
    cases hwf with
    | let_ hop hk =>
      cases hop with
      | mk code hargs =>
        simp only [hoistDiamond]
        refine .let_ (.mk code (trel_iout hG hargs)) fun xs₁ xs₂ => ?_
        exact hoistDiamond_wf hj rest (next + _)
          (hk (freshIVals _ xs₁ next) (freshIVals _ xs₂ next))
          (hsh (freshIVals _ xs₁ next)) (hG.freshIVals xs₁ xs₂ next)
    | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsh
  | .load rest, next, _, G', _, _, _, hwf, hsh, hG => by
    cases hwf with
    | load t ha hk =>
      simp only [hoistDiamond]
      refine .load t (argRel_iout hG ha) fun v₁ v₂ => ?_
      exact hoistDiamond_wf hj rest (next + 1) (hk (.var v₁, .var next) (.var v₂, .var next))
        (hsh (.var v₁, .var next)) (hG.freshOne v₁ v₂ next)
    | let_ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsh
  | .store rest, next, _, G', _, _, _, hwf, hsh, hG => by
    cases hwf with
    | store hv ha hk =>
      simp only [hoistDiamond]
      exact .store (argRel_iout hG hv) (argRel_iout hG ha) (hoistDiamond_wf hj rest next hk hsh hG)
    | let_ _ _ | load _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsh
  | .call rest, next, _, G', _, _, _, hwf, hsh, hG => by
    cases hwf with
    | call f hargs hk =>
      simp only [hoistDiamond]
      refine .call f (trel_iout hG hargs) fun xs₁ xs₂ => ?_
      exact hoistDiamond_wf hj rest (next + _)
        (hk (freshIVals _ xs₁ next) (freshIVals _ xs₂ next))
        (hsh (freshIVals _ xs₁ next)) (hG.freshIVals xs₁ xs₂ next)
    | let_ _ _ | load _ _ _ | store _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsh

end WfSelect

/-! ## `ifOpt_wf` via `Wf.induct` -/

private theorem ifOptB_get {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (bitsOnly : Bool) (depth next : Nat) :
    {sig : List (List Ty)} → {ts : List Ty} → (bs : Blocks (IVal V) (JLabel L) rs sig) →
    (i : Member ts sig) → (xs : Tup V ts) →
    (ifOptBWith bitsOnly depth next bs).get i xs =
      ifOptWith bitsOnly depth (next + ts.length) (bs.get i (freshIVals ts xs next))
  | _, _, .cons _ _, .here, _ => rfl
  | _, _, .cons _ bs, .there i, xs => ifOptB_get bitsOnly depth next bs i xs

def OuterD {L₁ L₂ : List Ty → Type} (D : Ctx (JLabel L₁) (JLabel L₂))
    (D' : Ctx L₁ L₂) : Prop :=
  ∀ p ∈ D, match p.2.1, p.2.2 with
    | .outer l₁, .outer l₂ => ⟨p.1, l₁, l₂⟩ ∈ D'
    | _, _ => False

private theorem OuterD.append_outer {L₁ L₂ : List Ty → Type}
    {D : Ctx (JLabel L₁) (JLabel L₂)} {D' : Ctx L₁ L₂} (hD : OuterD D D') :
    {sig : List (List Ty)} → (Js₁ : Tup L₁ sig) → (Js₂ : Tup L₂ sig) →
    OuterD (Tup.zip (Js₁.map fun _ l => .outer l) (Js₂.map fun _ l => .outer l) ++ D)
      (Tup.zip Js₁ Js₂ ++ D')
  | [], (), (), p, hp => by
    have := hD p hp
    cases h1 : p.2.1 <;> cases h2 : p.2.2 <;> simp_all
  | _ :: _, (j₁, Js₁), (j₂, Js₂), p, hp => by
    simp only [Tup.map, Tup.zip, List.cons_append] at hp ⊢
    cases hp with
    | head => exact List.mem_cons_self
    | tail _ hp =>
      have ih := OuterD.append_outer hD Js₁ Js₂ p hp
      cases h1 : p.2.1 <;> cases h2 : p.2.2 <;> simp_all

/-! ## Diamond WP extraction and hoisting soundness -/

private def ArmSpec {rs : List Ty} {jTs : List Ty} (j : Cont jTs) :
    Nat → Expr Val Cont rs → Prop
  | 0, .jump (ts := ts) l _ => ∃ h : ts = jTs, l = h ▸ j
  | n + 1, .let_ op k => isSafeOp op.code = true ∧ ∀ xs, ArmSpec j n (k xs)
  | _, _ => False

private def DiamondSpec {rs : List Ty} {jTs : List Ty} (j : Cont jTs) :
    DiamondPlan → Expr Val Cont rs → Prop
  | .jnz nT nE, .jnz _ t e => isSelectSig jTs = true ∧ ArmSpec j nT t ∧ ArmSpec j nE e
  | .let_ rest, .let_ _ k => ∀ xs, DiamondSpec j rest (k xs)
  | .load rest, .load _ _ k => ∀ v, DiamondSpec j rest (k v)
  | .store rest, .store _ _ k => DiamondSpec j rest k
  | .call rest, .call _ _ k => ∀ xs, DiamondSpec j rest (k xs)
  | _, _ => False

def OuterContD (D : Ctx (JLabel Cont) Cont) : Prop :=
  ∀ p ∈ D, match p.2.1 with | .outer l => l = p.2.2 | .loc _ => False

private theorem OuterContD.append_outer {D : Ctx (JLabel Cont) Cont} (hD : OuterContD D) :
    {sig : List (List Ty)} → (Js : Tup Cont sig) →
    OuterContD (Tup.zip (Js.map fun _ l => .outer l) Js ++ D)
  | [], () => hD
  | _ :: _, (_, Js) => by
    intro p hp
    simp only [Tup.map, Tup.zip, List.cons_append] at hp
    cases hp with
    | head => rfl
    | tail _ hp => exact OuterContD.append_outer hD Js p hp

private theorem armSpec_of_checkArm {rs : List Ty} (jId : Nat) {jTs : List Ty} (j : Cont jTs) :
    ∀ (fuel next n : Nat) {G : Ctx (IVal Val) Val} {D : Ctx (JLabel Cont) Cont}
      {e₁ : Expr (IVal Val) (JLabel Cont) rs} {e₂ : Expr Val Cont rs},
    OuterContD D → Wf G (⟨jTs, .loc jId, j⟩ :: D) e₁ e₂ →
    checkArm jId jTs fuel next e₁ = some n → ArmSpec j n e₂
  | fuel, next, n, _, D, _, _, hD, hwf, hc => by
    cases hwf with
    | let_ hop hk =>
      cases hop with
      | mk code _ =>
        unfold checkArm at hc
        cases hs : isSafeOp code <;> rw [hs] at hc
        · simp at hc
        · cases fuel with
          | zero => simp at hc
          | succ fuel' =>
            simp only [↓reduceIte, Option.map_eq_some_iff] at hc
            rcases hc with ⟨m, hm, rfl⟩
            exact ⟨hs, fun xs₂ =>
              armSpec_of_checkArm jId j fuel' (next + _) m hD (hk (dummyIVals _ next) xs₂) hm⟩
    | @jump _ _ _ j₁ _ _ _ hj _ =>
      cases hj with
      | head =>
        simp only [checkArm, beq_self_eq_true, Bool.true_and] at hc
        cases hbeq : Ty.listBeq jTs jTs with
        | false => simp [hbeq] at hc
        | true =>
          simp only [hbeq, ↓reduceIte, Option.some.injEq] at hc
          subst hc
          exact ⟨rfl, rfl⟩
      | tail _ hmem =>
        have hbad := hD _ hmem
        dsimp only at hbad
        cases j₁ with
        | outer _ => simp [checkArm] at hc
        | loc _ => exact False.elim hbad
    | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | ret _ | exit _ _ | hlt | group _ _ =>
      simp [checkArm] at hc

private theorem diamondSpec_of_checkDiamond {rs : List Ty} (bitsOnly : Bool)
    (jId : Nat) {jTs : List Ty} (j : Cont jTs)
    (next : Nat) (plan : DiamondPlan) {G : Ctx (IVal Val) Val} {D : Ctx (JLabel Cont) Cont}
    {e₁ : Expr (IVal Val) (JLabel Cont) rs} {e₂ : Expr Val Cont rs}
    (hD : OuterContD D) (hwf : Wf G (⟨jTs, .loc jId, j⟩ :: D) e₁ e₂)
    (hc : checkDiamondWith bitsOnly jId jTs next e₁ = some plan) : DiamondSpec j plan e₂ :=
  checkDiamond_peel_of_wf bitsOnly jId jTs (DiamondSpec j)
    (fun h => h) (fun h => h) (fun h => h) (fun h => h)
    (fun ht he hsel ⟨_, h1, h2⟩ =>
      ⟨isSelectSigWith_imp bitsOnly jTs hsel,
       armSpec_of_checkArm jId j 4 _ _ hD ht h1,
       armSpec_of_checkArm jId j 4 _ _ hD he h2⟩)
    next plan hwf hc

private theorem bool_val_cases {c₁ : Arg (IVal Val) .bool} {c₂ : Arg Val .bool}
    (hce : (iout c₁).val = c₂.val) {P : Prop}
    (ht : c₂.val = true → (iout c₁).val = true → P)
    (hf : c₂.val = false → (iout c₁).val = false → P) : P := by
  cases h : c₂.val
  · exact hf h (hce.trans h)
  · exact ht h (hce.trans h)

private theorem hoistArm_taken_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {jTs : List Ty} (j : Cont jTs) :
    ∀ (n next : Nat) {ρ : FEnv} {G : Ctx (IVal Val) Val} {D : Ctx (JLabel Cont) Cont}
      {e₁ : Expr (IVal Val) (JLabel Cont) rs} {e₂ : Expr Val Cont rs},
    Wf G D e₁ e₂ → ArmSpec j n e₂ → IGood ρ next G → wp Γ Q X e₂ m →
    {cont : Nat → Tup (Arg (IVal Val)) jTs → Expr Val Cont rs} →
    (∀ next' ρ' args₁ vs₂, next ≤ next' →
      (∀ {u} (k : FKey u), k.FLt next → k.fev ρ' = k.fev ρ) →
      IArgsGood ρ' next' args₁ vs₂ → j vs₂ m → wp Γ Q X (cont next' args₁) m) →
    wp Γ Q X (hoistArm jTs n next e₁ cont) m
  | 0, next, ρ, G, D, e₁, e₂, hwf, hsp, hG, hwp, cont, hcont => by
    cases hwf with
    | @jump _ _ ts _ _ args₁ args₂ _ hargs =>
      rcases hsp with ⟨rfl, rfl⟩
      rw [hoistArm_jump_eq]
      simp only [wp] at hwp
      exact hcont next ρ args₁ (vals args₂) (Nat.le_refl _) (fun _ _ => rfl)
        (IArgsGood.of_trel hG hargs) hwp
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsp
  | n + 1, next, ρ, G, D, e₁, e₂, hwf, hsp, hG, hwp, cont, hcont => by
    cases hwf with
    | let_ hop hk =>
      cases hop with
      | @mk _ _ code args₁ args₂ hargs =>
        rcases hsp with ⟨_, hsp'⟩
        simp only [hoistArm, wp, Op.wp] at hwp ⊢
        rw [TRel.iout_vals hG hargs]
        refine OpCode.wp_mono code (vals args₂) (fun r hr => ?_) hwp
        refine hoistArm_taken_wp j n (next + _) (hk (freshIVals _ r next) r)
          (hsp' r) (hG.freshIVals r) hr fun next' ρ' args₁ vs₂ hle hev hargs' hj => ?_
        refine hcont next' ρ' args₁ vs₂ (Nat.le_trans (Nat.le_add_right _ _) hle)
          (fun {u} k hk => ?_) hargs' hj
        exact (hev k (hk.le (Nat.le_add_right _ _))).trans (FKey.fev_fupdTup r hk)
    | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsp

private theorem hoistArm_untaken_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {jTs : List Ty} (j : Cont jTs) :
    ∀ (n next : Nat) {ρ : FEnv} {G : Ctx (IVal Val) Val} {D : Ctx (JLabel Cont) Cont}
      {e₁ : Expr (IVal Val) (JLabel Cont) rs} {e₂ : Expr Val Cont rs},
    Wf G D e₁ e₂ → ArmSpec j n e₂ → IGood ρ next G →
    {cont : Nat → Tup (Arg (IVal Val)) jTs → Expr Val Cont rs} →
    (∀ next' ρ' args₁ vs₂, next ≤ next' →
      (∀ {u} (k : FKey u), k.FLt next → k.fev ρ' = k.fev ρ) →
      IArgsGood ρ' next' args₁ vs₂ → wp Γ Q X (cont next' args₁) m) →
    wp Γ Q X (hoistArm jTs n next e₁ cont) m
  | 0, next, ρ, G, D, e₁, e₂, hwf, hsp, hG, cont, hcont => by
    cases hwf with
    | @jump _ _ ts _ _ args₁ args₂ _ hargs =>
      rcases hsp with ⟨rfl, rfl⟩
      rw [hoistArm_jump_eq]
      exact hcont next ρ args₁ (vals args₂) (Nat.le_refl _) (fun _ _ => rfl)
        (IArgsGood.of_trel hG hargs)
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsp
  | n + 1, next, ρ, G, D, e₁, e₂, hwf, hsp, hG, cont, hcont => by
    cases hwf with
    | let_ hop hk =>
      cases hop with
      | @mk _ _ code args₁ args₂ hargs =>
        rcases hsp with ⟨hsafe, hsp'⟩
        simp only [hoistArm, wp, Op.wp]
        refine OpCode.wp_of_isSafeOp code hsafe (vals (tupIOut args₁)) fun r => ?_
        refine hoistArm_untaken_wp j n (next + _) (hk (freshIVals _ r next) r)
          (hsp' r) (hG.freshIVals r) fun next' ρ' args₁ vs₂ hle hev hargs' => ?_
        refine hcont next' ρ' args₁ vs₂ (Nat.le_trans (Nat.le_add_right _ _) hle)
          (fun {u} k hk => ?_) hargs'
        exact (hev k (hk.le (Nat.le_add_right _ _))).trans (FKey.fev_fupdTup r hk)
    | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsp

private theorem hoistDiamond_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {jTs : List Ty}
    (j : Cont jTs) :
    ∀ (plan : DiamondPlan) (next : Nat) {ρ : FEnv} {G : Ctx (IVal Val) Val}
      {D : Ctx (JLabel Cont) Cont} {e₁ : Expr (IVal Val) (JLabel Cont) rs} {e₂ : Expr Val Cont rs},
    Wf G D e₁ e₂ → DiamondSpec j plan e₂ → IGood ρ next G → ∀ m,
    wp Γ Q X e₂ m → wp Γ Q X (hoistDiamond j plan next e₁) m
  | .jnz nT nE, next, ρ, G, D, e₁, e₂, hwf, hsp, hG, m, hwp => by
    cases hwf with
    | jnz hc ht he =>
      rcases hsp with ⟨hsel, hspT, hspE⟩
      simp only [hoistDiamond, wp] at hwp ⊢
      have hce := argRel_iout_val hG hc
      refine bool_val_cases hce (fun hcv hcv1 => ?_) (fun hcv hcv1 => ?_)
      · refine hoistArm_taken_wp j nT next ht hspT hG (hwp.1 hcv)
          fun next₁ ρ₁ argsT vsT hle₁ hev₁ hargsT hjT => ?_
        refine hoistArm_untaken_wp j nE next₁ he hspE (hG.mono hle₁ hev₁)
          fun next₂ ρ₂ argsE vsE hle₂ hev₂ hargsE => ?_
        have hargsT₂ := iargsGood_mono hle₂ hev₂ hargsT
        refine emitSelectTup_wp (iout _) jTs hsel ρ₂ next₂ hargsT₂ hargsE fun sel hsel_eq => ?_
        simp only [wp, hsel_eq, hcv1, ↓reduceIte]
        exact hjT
      · refine hoistArm_untaken_wp j nT next ht hspT hG
          fun next₁ ρ₁ argsT vsT hle₁ hev₁ hargsT => ?_
        refine hoistArm_taken_wp j nE next₁ he hspE (hG.mono hle₁ hev₁) (hwp.2 hcv)
          fun next₂ ρ₂ argsE vsE hle₂ hev₂ hargsE hjE => ?_
        have hargsT₂ := iargsGood_mono hle₂ hev₂ hargsT
        refine emitSelectTup_wp (iout _) jTs hsel ρ₂ next₂ hargsT₂ hargsE fun sel hsel_eq => ?_
        simp only [wp, hsel_eq, hcv1, Bool.false_eq_true, ↓reduceIte]
        exact hjE
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsp
  | .let_ rest, next, ρ, G, D, _, _, hwf, hsp, hG, m, hwp => by
    cases hwf with
    | let_ hop hk =>
      cases hop with
      | @mk _ _ code _ args₂ hargs =>
        simp only [hoistDiamond, wp, Op.wp] at hwp ⊢
        rw [TRel.iout_vals hG hargs]
        exact OpCode.wp_mono code (vals args₂) (fun r hr =>
          hoistDiamond_wp j rest (next + _) (hk (freshIVals _ r next) r)
            (hsp r) (hG.freshIVals r) m hr) hwp
    | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsp
  | .load rest, next, ρ, G, D, _, _, hwf, hsp, hG, m, hwp => by
    cases hwf with
    | load t ha hk =>
      simp only [hoistDiamond, wp] at hwp ⊢
      rcases hwp with ⟨v, hv, hk2⟩
      rw [argRel_iout_val hG ha]
      exact ⟨v, hv, hoistDiamond_wp j rest (next + 1) (hk (.var v, .var next) v)
        (hsp v) (hG.freshOne v) m hk2⟩
    | let_ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsp
  | .store rest, next, ρ, G, D, _, _, hwf, hsp, hG, m, hwp => by
    cases hwf with
    | store hv ha hk =>
      simp only [hoistDiamond, wp] at hwp ⊢
      rw [argRel_iout_val hG hv, argRel_iout_val hG ha]
      exact ⟨hwp.1, hoistDiamond_wp j rest next hk hsp hG _ hwp.2⟩
    | let_ _ _ | load _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsp
  | .call rest, next, ρ, G, D, _, _, hwf, hsp, hG, m, hwp => by
    cases hwf with
    | call f hargs hk =>
      simp only [hoistDiamond, wp] at hwp ⊢
      rcases hwp with ⟨P, E, hΓ, hP, hE⟩
      rw [TRel.iout_vals hG hargs]
      exact ⟨P, E, hΓ, fun r m' hp =>
        hoistDiamond_wp j rest (next + _) (hk (freshIVals _ r next) r)
          (hsp r) (hG.freshIVals r) m' (hP r m' hp), hE⟩
    | let_ _ _ | load _ _ _ | store _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsp

private theorem ifOpt_jump_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} (rs : List Ty)
    {G : Ctx (IVal V₁) (IVal V₂)} {D : Ctx (JLabel L₁) (JLabel L₂)}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} {ts : List Ty}
    {j₁ : JLabel L₁ ts} {j₂ : JLabel L₂ ts}
    {args₁ : Tup (Arg (IVal V₁)) ts} {args₂ : Tup (Arg (IVal V₂)) ts}
    (hj : ⟨ts, j₁, j₂⟩ ∈ D) (hargs : TRel (ArgRel G) args₁ args₂)
    (hG : IRelG G' G) (hD : OuterD D D') (bitsOnly : Bool) (depth next : Nat) :
    Wf G' D' (ifOptWith bitsOnly depth next (.jump (rs := rs) j₁ args₁))
             (ifOptWith bitsOnly depth next (.jump (rs := rs) j₂ args₂)) := by
  have hj' := hD _ hj
  cases j₁ <;> cases j₂ <;> simp_all [ifOptWith]
  exact .jump hj' (trel_iout hG hargs)

private theorem ifOpt_jump_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx (IVal Val) Val} {D : Ctx (JLabel Cont) Cont} {ts : List Ty}
    {j₁ : JLabel Cont ts} {j₂ : Cont ts}
    {args₁ : Tup (Arg (IVal Val)) ts} {args₂ : Tup (Arg Val) ts}
    (hj : ⟨ts, j₁, j₂⟩ ∈ D) (hargs : TRel (ArgRel G) args₁ args₂)
    {ρ : FEnv} {bitsOnly : Bool} {depth next : Nat} (hD : OuterContD D) (hG : IGood ρ next G)
    {m : Mem 64} (hw : wp Γ Q X (.jump j₂ args₂) m) :
    wp Γ Q X (ifOptWith bitsOnly depth next (.jump j₁ args₁)) m := by
  have hj' := hD _ hj
  cases j₁ with
  | outer l =>
    dsimp only at hj'
    simp only [ifOptWith, wp] at hw ⊢
    rw [hj', TRel.iout_vals hG hargs]
    exact hw
  | loc _ => exact False.elim hj'

private theorem outerD_head_compat {L₁ L₂ : List Ty → Type}
    {D : Ctx (JLabel L₁) (JLabel L₂)} {D' : Ctx L₁ L₂} (hD : OuterD D D')
    (jId : Nat) {ts : List Ty} :
    ∀ p ∈ (⟨ts, JLabel.loc jId, JLabel.loc jId⟩ :: D),
      match p.2.1, p.2.2 with
      | .loc d₁, .loc d₂ => (d₁ == jId) = (d₂ == jId)
      | .outer _, .outer _ => True
      | _, _ => False := by
  intro ⟨pts, j₁, j₂⟩ hp
  cases hp with
  | head => simp
  | tail _ hp =>
    have hd := hD _ hp
    cases j₁ <;> cases j₂ <;> simp_all

end IfOptImpl

/-- Well-formedness preservation for `ifOptWith`, proved via `Wf.induct`. -/
theorem ifOptWith_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (bitsOnly : Bool) {G : Ctx (IVal V₁) (IVal V₂)} {D : Ctx (JLabel L₁) (JLabel L₂)}
    {e₁ : Expr (IVal V₁) (JLabel L₁) rs} {e₂ : Expr (IVal V₂) (JLabel L₂) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂},
      IRelG G' G → OuterD D D' → ∀ depth next,
        Wf G' D' (ifOptWith bitsOnly depth next e₁) (ifOptWith bitsOnly depth next e₂) := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
    intro G' D' hG hD depth next
    cases hop with
    | mk code hargs =>
      exact .let_ (.mk code (trel_iout hG hargs)) fun xs₁ xs₂ =>
        ih _ _ (hG.freshIVals xs₁ xs₂ next) hD depth (next + _)
  | load t ha _ ih =>
    intro G' D' hG hD depth next
    exact .load t (argRel_iout hG ha) fun v₁ v₂ =>
      ih _ _ (hG.freshOne v₁ v₂ next) hD depth (next + 1)
  | store hv ha _ ih =>
    intro G' D' hG hD depth next
    exact .store (argRel_iout hG hv) (argRel_iout hG ha) (ih hG hD depth next)
  | call f hargs _ ih =>
    intro G' D' hG hD depth next
    exact .call f (trel_iout hG hargs) fun xs₁ xs₂ =>
      ih _ _ (hG.freshIVals xs₁ xs₂ next) hD depth (next + _)
  | jnz hc _ _ iht ihe =>
    intro G' D' hG hD depth next
    exact .jnz (argRel_iout hG hc) (iht hG hD depth next) (ihe hG hD depth next)
  | jump hj hargs =>
    intro G' D' hG hD depth next
    exact ifOpt_jump_wf _ hj hargs hG hD bitsOnly depth next
  | ret hvs =>
    intro G' _ hG _ _ _
    exact .ret (trel_iout hG hvs)
  | exit f hargs =>
    intro G' _ hG _ _ _
    exact .exit f (trel_iout hG hargs)
  | hlt =>
    intro _ _ _ _ _ _
    exact .hlt
  | @group G D sig b₁ b₂ k₁ k₂ _ hk ihb ihk =>
    intro G' D' hG hD depth next
    cases sig with
    | nil =>
      refine .group (fun Js₁ Js₂ => WfB.of_get fun i => nomatch i) fun Js₁ Js₂ => ?_
      exact ihk (Js₁.map fun _ l => .outer l) (Js₂.map fun _ l => .outer l)
        hG (OuterD.append_outer hD Js₁ Js₂) depth next
    | cons ts sig' =>
      cases sig' with
      | nil =>
        have hchk : checkDiamondWith bitsOnly depth ts next (k₁ (.loc depth, ())) =
            checkDiamondWith bitsOnly depth ts next (k₂ (.loc depth, ())) :=
          checkDiamond_eq_of_wf bitsOnly depth ts (outerD_head_compat hD depth)
            next (hk (.loc depth, ()) (.loc depth, ()))
        simp only [ifOptWith]
        refine .group (fun Js₁ Js₂ => WfB.of_get fun i xs₁ xs₂ => ?_) fun Js₁ Js₂ => ?_
        · rw [ifOptB_get, ifOptB_get]
          exact ihb (Js₁.map fun _ l => .outer l) (Js₂.map fun _ l => .outer l)
            i _ _ (hG.freshIVals xs₁ xs₂ next) (OuterD.append_outer hD Js₁ Js₂)
            (depth + 1) (next + _)
        · rw [hchk]
          cases hplan : checkDiamondWith bitsOnly depth ts next (k₂ (.loc depth, ())) with
          | none =>
            exact ihk (Js₁.map fun _ l => .outer l) (Js₂.map fun _ l => .outer l)
              hG (OuterD.append_outer hD Js₁ Js₂) (depth + 1) next
          | some plan =>
            have hsh_k2 : HasDiamondShape ts plan (k₂ (.outer Js₂.1, ())) :=
              hasDiamondShape_of_checkDiamond bitsOnly depth ts next plan
                (hk (.loc depth, ()) (.outer Js₂.1, ())) (hchk.symm ▸ hplan)
            have hwf_out := hk (.outer Js₁.1, ()) (.outer Js₂.1, ())
            have hsh_k1 : HasDiamondShape ts plan (k₁ (.outer Js₁.1, ())) :=
              hasDiamondShape_of_rhs ts plan hwf_out hsh_k2
            exact hoistDiamond_wf List.mem_cons_self plan next hwf_out hsh_k1 hG
      | cons ts₂ rest =>
        refine .group (fun Js₁ Js₂ => WfB.of_get fun i xs₁ xs₂ => ?_) fun Js₁ Js₂ => ?_
        · rw [ifOptB_get, ifOptB_get]
          exact ihb (Js₁.map fun _ l => .outer l) (Js₂.map fun _ l => .outer l)
            i _ _ (hG.freshIVals xs₁ xs₂ next) (OuterD.append_outer hD Js₁ Js₂)
            (depth + rest.length + 2) (next + _)
        · exact ihk (Js₁.map fun _ l => .outer l) (Js₂.map fun _ l => .outer l)
            hG (OuterD.append_outer hD Js₁ Js₂) (depth + rest.length + 2) next

/-- Well-formedness preservation for `ifOpt`, proved via `Wf.induct`. -/
theorem ifOpt_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx (IVal V₁) (IVal V₂)} {D : Ctx (JLabel L₁) (JLabel L₂)}
    {e₁ : Expr (IVal V₁) (JLabel L₁) rs} {e₂ : Expr (IVal V₂) (JLabel L₂) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂},
      IRelG G' G → OuterD D D' → ∀ depth next,
        Wf G' D' (ifOpt depth next e₁) (ifOpt depth next e₂) :=
  ifOptWith_wf false hwf

/-- Weakest-precondition refinement for `ifOptWith`, proved via `Wf.induct`. -/
theorem ifOptWith_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (bitsOnly : Bool) {G : Ctx (IVal Val) Val} {D : Ctx (JLabel Cont) Cont}
    {e₁ : Expr (IVal Val) (JLabel Cont) rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G D e₁ e₂) :
    OuterContD D → ∀ depth next ρ, IGood ρ next G → ∀ m,
    wp Γ Q X e₂ m → wp Γ Q X (ifOptWith bitsOnly depth next e₁) m := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
    intro hD depth next ρ hG m hw
    cases hop with
    | @mk _ _ code _ args₂ hargs =>
      simp only [ifOptWith, wp, Op.wp] at hw ⊢
      rw [TRel.iout_vals hG hargs]
      exact OpCode.wp_mono code (vals args₂) (fun r hr =>
        ih (freshIVals _ r next) r hD depth (next + _) (fupdTup ρ next r)
          (hG.freshIVals r) m hr) hw
  | load t ha _ ih =>
    intro hD depth next ρ hG m ⟨v, hv, hk⟩
    simp only [ifOptWith, wp]
    rw [argRel_iout_val hG ha]
    exact ⟨v, hv, ih (.var v, .var next) v hD depth (next + 1) (fupd ρ next v)
      (hG.freshOne v) m hk⟩
  | store hv ha _ ih =>
    intro hD depth next ρ hG m ⟨hok, hk⟩
    simp only [ifOptWith, wp]
    rw [argRel_iout_val hG hv, argRel_iout_val hG ha]
    exact ⟨hok, ih hD depth next ρ hG _ hk⟩
  | call f hargs _ ih =>
    intro hD depth next ρ hG m ⟨P, E, hΓ, hP, hE⟩
    simp only [ifOptWith, wp]
    rw [TRel.iout_vals hG hargs]
    exact ⟨P, E, hΓ, fun r m' hp =>
      ih (freshIVals _ r next) r hD depth (next + _) (fupdTup ρ next r)
        (hG.freshIVals r) m' (hP r m' hp), hE⟩
  | jnz hc _ _ iht ihe =>
    intro hD depth next ρ hG m hw
    simp only [ifOptWith, wp] at hw ⊢
    rw [argRel_iout_val hG hc]
    exact ⟨fun h => iht hD depth next ρ hG m (hw.1 h),
           fun h => ihe hD depth next ρ hG m (hw.2 h)⟩
  | jump hj hargs =>
    intro hD depth next ρ hG m hw
    exact ifOpt_jump_wp hj hargs hD hG hw
  | ret hvs =>
    intro _ _ _ ρ hG m hw
    simp only [ifOptWith, wp] at hw ⊢
    rw [TRel.iout_vals hG hvs]
    exact hw
  | exit f hargs =>
    intro _ _ _ ρ hG m hw
    simp only [ifOptWith, wp] at hw ⊢
    rw [TRel.iout_vals hG hargs]
    exact hw
  | hlt =>
    intro _ _ _ _ _ _ hw
    exact hw
  | @group G D sig b₁ b₂ k₁ k₂ _ hk ihb ihk =>
    intro hD depth next ρ hG m hw
    cases sig with
    | nil =>
      simp only [ifOptWith, wp] at hw ⊢
      intro Js hclosed
      refine ihk (Js.map fun _ l => .outer l) Js (OuterContD.append_outer hD Js) depth next ρ hG
        m (hw Js ?_)
      rw [closed_iff] at hclosed ⊢
      intro _ i
      exact nomatch i
    | cons ts sig' =>
      cases sig' with
      | nil =>
        simp only [ifOptWith, wp] at hw ⊢
        intro Js hclosed
        have hclosed₂ : Closed Γ Q X (b₂ Js) Js := by
          rw [closed_iff] at hclosed ⊢
          intro ts' i xs m' hb'
          apply hclosed i xs m'
          rw [ifOptB_get]
          exact ihb (Js.map fun _ l => .outer l) Js i (freshIVals ts' xs next) xs
            (OuterContD.append_outer hD Js) (depth + 1) (next + ts'.length)
            (fupdTup ρ next xs) (hG.freshIVals xs) m' hb'
        have hw₂ := hw Js hclosed₂
        cases hplan : checkDiamondWith bitsOnly depth ts next (k₁ (.loc depth, ())) with
        | none =>
          exact ihk (Js.map fun _ l => .outer l) Js (OuterContD.append_outer hD Js) (depth + 1)
            next ρ hG m hw₂
        | some plan =>
          have hsp := diamondSpec_of_checkDiamond bitsOnly depth Js.1 next plan hD
            (hk (.loc depth, ()) Js) hplan
          exact hoistDiamond_wp Js.1 plan next (hk (.outer Js.1, ()) Js) hsp hG m hw₂
      | cons ts₂ rest =>
        simp only [ifOptWith, wp] at hw ⊢
        intro Js hclosed
        refine ihk (Js.map fun _ l => .outer l) Js (OuterContD.append_outer hD Js)
          (depth + rest.length + 2) next ρ hG m (hw Js ?_)
        rw [closed_iff] at hclosed ⊢
        intro ts' i xs m' hb'
        apply hclosed i xs m'
        rw [ifOptB_get]
        exact ihb (Js.map fun _ l => .outer l) Js i (freshIVals ts' xs next) xs
          (OuterContD.append_outer hD Js) (depth + rest.length + 2) (next + ts'.length)
          (fupdTup ρ next xs) (hG.freshIVals xs) m' hb'

/-- Weakest-precondition refinement for `ifOpt`, proved via `Wf.induct`. -/
theorem ifOpt_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx (IVal Val) Val} {D : Ctx (JLabel Cont) Cont}
    {e₁ : Expr (IVal Val) (JLabel Cont) rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G D e₁ e₂) :
    OuterContD D → ∀ depth next ρ, IGood ρ next G → ∀ m,
    wp Γ Q X e₂ m → wp Γ Q X (ifOpt depth next e₁) m :=
  ifOptWith_wp false hwf

/-! ## Closed functions -/

/-- `Func.ifOptWith` preserves relational well-formedness `Func.Wf`. -/
theorem Func.ifOptWith_wf (bitsOnly : Bool) {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    (Func.ifOptWith bitsOnly f).Wf := by
  intro V₁ V₂ L₁ L₂ xs₁ xs₂
  have hwf := hf (IVal V₁) (IVal V₂) (JLabel L₁) (JLabel L₂)
    (freshIVals as xs₁ 0) (freshIVals as xs₂ 0)
  have hrel : IRelG (Tup.zip xs₁ xs₂) (Tup.zip (freshIVals as xs₁ 0) (freshIVals as xs₂ 0)) := by
    simpa using IRelG.freshIVals (G := []) (G' := []) (fun _ hp => nomatch hp) xs₁ xs₂ 0
  exact LeanQbe.T.ifOptWith_wf bitsOnly hwf hrel (fun _ hp => nomatch hp) 0 as.length

/-- `Func.ifOpt` preserves relational well-formedness `Func.Wf`. -/
theorem Func.ifOpt_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) : (Func.ifOpt f).Wf :=
  Func.ifOptWith_wf false hf

/-- `Func.ifOptBits` preserves relational well-formedness `Func.Wf`. -/
theorem Func.ifOptBits_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    (Func.ifOptBits f).Wf :=
  Func.ifOptWith_wf true hf

/-- `Func.ifOptWith` refines function contracts. -/
theorem Func.ifOptWith_spec (bitsOnly : Bool) {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    {Γ : Env} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.ifOptWith bitsOnly f) xs m Q X := by
  have hwf := hf (IVal Val) Val (JLabel Cont) Cont (freshIVals as xs 0) xs
  have hgood : IGood (fupdTup (fun _ _ => default) 0 xs) as.length
      (Tup.zip (freshIVals as xs 0) xs) := by
    simpa using IGood.freshIVals (ρ := fun _ _ => default) (b := 0) (G := [])
      (fun _ hp => nomatch hp) xs
  exact LeanQbe.T.ifOptWith_wp bitsOnly hwf (fun _ hp => nomatch hp) 0 as.length _ hgood m h

/-- `Func.ifOpt` refines function contracts: any source contract holds on `Func.ifOpt f`. -/
theorem Func.ifOpt_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.ifOpt f) xs m Q X :=
  Func.ifOptWith_spec false hf h

/-- `Func.ifOptBits` refines function contracts on post-`Legal` IR. -/
theorem Func.ifOptBits_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.ifOptBits f) xs m Q X :=
  Func.ifOptWith_spec true hf h

end LeanQbe.T
