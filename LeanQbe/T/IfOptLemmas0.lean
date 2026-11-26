module

public import LeanQbe.T.IfOpt
public import LeanQbe.T.OptUtilLemmas
public import LeanQbe.T.Module
import LeanQbe.T.OpsLemmas
import LeanQbe.T.PassEnvKit

/-!
# Correctness of `ifOpt` — Part 0 (`Wf` & Shape Helpers)

* `OpCode.wp_of_isSafeOp`: every whitelisted safe opcode is total and UB-free.
* `emitSelectTup_wp`, `emitSelectTup_wf`: scalar/pair `select` lowering correctness (including
  identical-operand skip via `fKeyBeq_iff_eq`).
* `ifOpt_wf`, `ifOpt_wp`: expression-level `Wf` preservation and WP refinement via `Wf.induct`.
* `Func.ifOpt_wf`, `Func.ifOpt_spec`: closed-function specifications.
-/

set_option autoImplicit false

public section

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
    dsimp only [isSafeOp] at hs
    have hf : t.hasFloat = false := by cases h : t.hasFloat <;> simp_all
    dsimp only [OpCode.wp]; simp [hf, hP]
  | neg t =>
    rcases args with ⟨a, ⟨⟩⟩
    dsimp only [isSafeOp] at hs
    have hf : t.hasFloat = false := by cases h : t.hasFloat <;> simp_all
    dsimp only [OpCode.wp]; simp [hf, hP]
  | cmp o t m h =>
    subst h
    rcases args with ⟨a, b, ⟨⟩⟩
    dsimp only [isSafeOp] at hs
    have hf : t.hasFloat = false := by cases h : t.hasFloat <;> simp_all
    dsimp only [OpCode.wp]; simp [hf, hP]
  | zext m n | sext m n =>
    rcases args with ⟨a, ⟨⟩⟩
    dsimp only [isSafeOp] at hs
    have hle : m ≤ n := of_decide_eq_true hs
    exact ⟨hle, hP _⟩
  | trunc m n =>
    rcases args with ⟨a, ⟨⟩⟩
    dsimp only [isSafeOp] at hs
    have hle : n ≤ m := of_decide_eq_true hs
    exact ⟨hle, hP _⟩
  | and _ | or _ | xor _ | not _ | ternlog _ _ | fshl _ | fshr _
  | clz _ | cls _ | rbit _ | ctz _ | popcnt _ | select _
  | ofBool _ | addc _ | subb _ | umulw _ | smulw _ | udiv0 _ | sdiv0 _
  | mkpair _ _ | unpair _ _ | bitcast _ _ _ | sha256rnds2 | sha256msg1 | sha256msg2 =>
    exact hP _
  | blend _ _ _ =>
    rw [OpCode.wp_blend]
    exact hP _
  | bswap t =>
    rcases args with ⟨a, ⟨⟩⟩
    dsimp only [isSafeOp] at hs
    rw [OpCode.wp_bswap, hs]
    exact hP _
  | shufd t _ =>
    rcases args with ⟨a, ⟨⟩⟩
    dsimp only [isSafeOp] at hs
    simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hs
    exact ⟨hs.1, hs.2, hP _⟩
  | shufb t | alignr t _ | blendw t _ =>
    rcases args with ⟨a, b, ⟨⟩⟩
    dsimp only [isSafeOp] at hs
    simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hs
    exact ⟨hs.1, hs.2, hP _⟩
  | udiv _ | sdiv _ | urem _ | srem _
  | fadd _ | fsub _ | fmul _ | fdiv _ | ffma _ | fsqrt _ | fneg _ | fabs _ | fcmp _ _ _ _
  | fptoui _ _ | fptosi _ _ | uitofp _ _ | sitofp _ _ | fcvt _ _ =>
    dsimp only [isSafeOp] at hs; cases hs

/-- Every whitelisted safe opcode evaluates deterministically and UB-freely to a unique tuple. -/
theorem OpCode.wp_isSafeOp_iff {sig rs : List Ty} (code : OpCode sig rs)
    (hs : isSafeOp code = true) (args : Tup Val sig) :
    ∃ v : Tup Val rs, ∀ (P : Tup Val rs → Prop), code.wp args P ↔ P v := by
  cases code with
  | copy _ => exact ⟨_, fun _ => Iff.rfl⟩
  | add t | sub t | mul t | shl t | lshr t | ashr t | rotl t | rotr t =>
    rcases args with ⟨a, b, ⟨⟩⟩
    dsimp only [isSafeOp] at hs
    have hf : t.hasFloat = false := by cases h : t.hasFloat <;> simp_all
    dsimp only [OpCode.wp]; simp only [hf, Bool.false_eq_true, ↓reduceIte]
    exact ⟨_, fun _ => Iff.rfl⟩
  | neg t =>
    rcases args with ⟨a, ⟨⟩⟩
    dsimp only [isSafeOp] at hs
    have hf : t.hasFloat = false := by cases h : t.hasFloat <;> simp_all
    dsimp only [OpCode.wp]; simp only [hf, Bool.false_eq_true, ↓reduceIte]
    exact ⟨_, fun _ => Iff.rfl⟩
  | cmp o t m h =>
    subst h
    rcases args with ⟨a, b, ⟨⟩⟩
    dsimp only [isSafeOp] at hs
    have hf : t.hasFloat = false := by cases h : t.hasFloat <;> simp_all
    dsimp only [OpCode.wp]; simp only [hf, Bool.false_eq_true, ↓reduceIte]
    exact ⟨_, fun _ => Iff.rfl⟩
  | zext m n | sext m n =>
    rcases args with ⟨a, ⟨⟩⟩
    dsimp only [isSafeOp] at hs
    have hle : m ≤ n := of_decide_eq_true hs
    exact ⟨_, fun P => ⟨fun hw => hw.2, fun hp => ⟨hle, hp⟩⟩⟩
  | trunc m n =>
    rcases args with ⟨a, ⟨⟩⟩
    dsimp only [isSafeOp] at hs
    have hle : n ≤ m := of_decide_eq_true hs
    exact ⟨_, fun P => ⟨fun hw => hw.2, fun hp => ⟨hle, hp⟩⟩⟩
  | and _ | or _ | xor _ | not _ | ternlog _ _ | fshl _ | fshr _
  | clz _ | cls _ | rbit _ | ctz _ | popcnt _ | select _
  | ofBool _ | addc _ | subb _ | umulw _ | smulw _ | udiv0 _ | sdiv0 _
  | mkpair _ _ | unpair _ _ | bitcast _ _ _ | sha256rnds2 | sha256msg1 | sha256msg2 =>
    exact ⟨_, fun _ => Iff.rfl⟩
  | blend _ _ _ =>
    exact ⟨_, fun P => by rw [OpCode.wp_blend]⟩
  | bswap t =>
    rcases args with ⟨a, ⟨⟩⟩
    dsimp only [isSafeOp] at hs
    dsimp only [OpCode.wp]; simp only [hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact ⟨_, fun _ => Iff.rfl⟩
  | shufd t _ =>
    rcases args with ⟨a, ⟨⟩⟩
    dsimp only [isSafeOp] at hs
    simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hs
    exact ⟨_, fun P => ⟨fun hw => hw.2.2, fun hp => ⟨hs.1, hs.2, hp⟩⟩⟩
  | shufb t | alignr t _ | blendw t _ =>
    rcases args with ⟨a, b, ⟨⟩⟩
    dsimp only [isSafeOp] at hs
    simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hs
    exact ⟨_, fun P => ⟨fun hw => hw.2.2, fun hp => ⟨hs.1, hs.2, hp⟩⟩⟩
  | udiv _ | sdiv _ | urem _ | srem _
  | fadd _ | fsub _ | fmul _ | fdiv _ | ffma _ | fsqrt _ | fneg _ | fabs _ | fcmp _ _ _ _
  | fptoui _ _ | fptosi _ _ | uitofp _ _ | sitofp _ _ | fcvt _ _ =>
    dsimp only [isSafeOp] at hs; cases hs

/-! ## Semantic invariant `IGood` over `FEnv` / `FKey` -/

/-- Soundness invariant on `G : Ctx (IVal Val) Val`. -/
@[expose] def IGood (ρ : FEnv) (b : Nat) (G : Ctx (IVal Val) Val) : Prop :=
  ∀ p ∈ G, p.2.1.1.val = p.2.2 ∧ p.2.1.2.fev ρ = p.2.2 ∧ p.2.1.2.FLt b

private theorem igood_to_fctx {ρ : FEnv} {b : Nat} {G : Ctx (IVal Val) Val} (h : IGood ρ b G) :
    FCtxGood Prod.fst Prod.snd b ρ G :=
  fun p hp => let ⟨h1, h2, h3⟩ := h p hp; ⟨h1, h3, h2⟩

private theorem fctx_to_igood {ρ : FEnv} {b : Nat} {G : Ctx (IVal Val) Val}
    (h : FCtxGood Prod.fst Prod.snd b ρ G) : IGood ρ b G :=
  fun p hp => let ⟨h1, h2, h3⟩ := h p hp; ⟨h1, h3, h2⟩

theorem IGood.mono {ρ ρ' : FEnv} {b b' : Nat} {G : Ctx (IVal Val) Val}
    (hb : b ≤ b') (hρ : ∀ {u} (k : FKey u), k.FLt b → k.fev ρ' = k.fev ρ)
    (hG : IGood ρ b G) : IGood ρ' b' G :=
  fun p hp => let ⟨h1, h2, h3⟩ := hG p hp; ⟨h1, (hρ _ h3).trans h2, h3.le hb⟩

theorem IGood.upd_all {ρ : FEnv} {b : Nat} {G : Ctx (IVal Val) Val} (hG : IGood ρ b G)
    {ts : List Ty} (xs : Tup Val ts) : IGood (fupdTup ρ b xs) (b + ts.length) G :=
  fctx_to_igood (FCtxGood.fupdTup xs (Nat.le_add_right _ _) (Nat.le_refl _) (igood_to_fctx hG))

theorem IGood.append {ρ : FEnv} {b : Nat} {G₁ G₂ : Ctx (IVal Val) Val}
    (h1 : IGood ρ b G₁) (h2 : IGood ρ b G₂) : IGood ρ b (G₁ ++ G₂) :=
  fctx_to_igood (FCtxGood.append (igood_to_fctx h1) (igood_to_fctx h2))

theorem IGood.freshIVals {ρ : FEnv} {b : Nat} {G : Ctx (IVal Val) Val} (hG : IGood ρ b G)
    {ts : List Ty} (xs : Tup Val ts) :
    IGood (fupdTup ρ b xs) (b + ts.length) (Tup.zip (freshIVals ts xs b) xs ++ G) :=
  fctx_to_igood (FCtxGood.freshTup (out := Prod.fst) (key := Prod.snd)
    (fun _ _ => rfl) (fun _ _ => rfl) xs b (igood_to_fctx hG))

theorem IGood.freshOne {ρ : FEnv} {b : Nat} {G : Ctx (IVal Val) Val} (hG : IGood ρ b G)
    {t : Ty} (v : Val t) :
    IGood (fupd ρ b v) (b + 1) (⟨t, (.var v, .var b), v⟩ :: G) :=
  hG.freshIVals (ts := [t]) (v, ())

theorem argRel_iout_val {G : Ctx (IVal Val) Val} {ρ : FEnv} {b : Nat} (hG : IGood ρ b G)
    {t : Ty} {a₁ : Arg (IVal Val) t} {a₂ : Arg Val t}
    (h : ArgRel G t a₁ a₂) : (iout a₁).val = a₂.val := by
  have hr := FCtxGood.argRel_val (out := Prod.fst) (key := Prod.snd) (igood_to_fctx hG) h
  cases a₁ <;> exact hr

theorem TRel.iout_vals {G : Ctx (IVal Val) Val} {ρ : FEnv} {b : Nat} (hG : IGood ρ b G)
    {ts : List Ty} {as₁ : Tup (Arg (IVal Val)) ts} {as₂ : Tup (Arg Val) ts}
    (h : TRel (ArgRel G) as₁ as₂) : vals (tupIOut as₁) = vals as₂ :=
  FCtxGood.trel_vals (out := Prod.fst) (key := Prod.snd)
    (fun _ => iout) (fun a => by cases a <;> rfl) (igood_to_fctx hG) h

/-! ## `IArgGood` and `emitSelectTy` / `emitSelectTup` WP soundness -/

@[expose] def IArgGood (ρ : FEnv) (b : Nat) {t : Ty} (a : Arg (IVal Val) t) (v : Val t) : Prop :=
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

@[expose] def IArgsGood (ρ : FEnv) (b : Nat) :
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

theorem IArgsGood.iout_vals {ρ : FEnv} {b : Nat} :
    {ts : List Ty} → {as : Tup (Arg (IVal Val)) ts} → {vs : Tup Val ts} →
    IArgsGood ρ b as vs → vals (tupIOut as) = vs
  | [], (), (), _ => rfl
  | _ :: _, (_, _), (_, _), ⟨ha, has⟩ =>
    Prod.ext ha.1 (IArgsGood.iout_vals has)

private theorem mkPairIValArg_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {a b : Ty} (ρ : FEnv) (next : Nat)
    {x : Arg (IVal Val) a} {y : Arg (IVal Val) b} {vx : Val a} {vy : Val b}
    (hx : IArgGood ρ next x vx) (hy : IArgGood ρ next y vy)
    {cont : Nat → Arg (IVal Val) (.pair a b) → Expr Val Cont rs}
    (h : ∀ ρ' next' (p : Arg (IVal Val) (.pair a b)), next ≤ next' →
      (∀ {u} (k : FKey u), k.FLt next → k.fev ρ' = k.fev ρ) →
      IArgGood ρ' next' p (vx, vy) → wp Γ Q X (cont next' p) m) :
    wp Γ Q X (mkPairIValArg next x y cont) m := by
  have hemit : ∀ {ox : Arg Val a} {oy : Arg Val b},
      ox.val = vx → oy.val = vy →
      wp Γ Q X (.let_ (op2 (.mkpair a b) ox oy) fun (p, ()) =>
        cont (next + 1) (.var (.var p, .var next))) m := by
    intro ox oy hx1 hy1
    simp only [wp_let_op2, OpCode.wp_mkpair, hx1, hy1]
    refine h (fupd (t := .pair a b) ρ next (vx, vy)) (next + 1)
      (.var (.var (vx, vy), .var next)) (by omega) (fun _ hk => FKey.fev_fupd _ hk)
      ⟨rfl, by simp [ikey, FKey.fev, fupd_eq],
        by dsimp only [ikey, FKey.FLt]; exact Nat.lt_succ_self _⟩
  dsimp only [mkPairIValArg]
  cases hio1 : iout x <;> cases hio2 : iout y
  · exact hemit (hx.1 ▸ congrArg Arg.val hio1.symm) (hy.1 ▸ congrArg Arg.val hio2.symm)
  · exact hemit (hx.1 ▸ congrArg Arg.val hio1.symm) (hy.1 ▸ congrArg Arg.val hio2.symm)
  · exact hemit (hx.1 ▸ congrArg Arg.val hio1.symm) (hy.1 ▸ congrArg Arg.val hio2.symm)
  · next cx cy =>
    have h1 : cx = vx := by rw [← hx.1, hio1]; rfl
    have h2 : cy = vy := by rw [← hy.1, hio2]; rfl
    subst h1 h2
    exact h ρ next (.imm (cx, cy)) (Nat.le_refl _) (fun _ _ => rfl) ⟨rfl, rfl, trivial⟩

private theorem splitPairIVal_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {a b : Ty} (ρ : FEnv) (next : Nat) (p : Arg (IVal Val) (.pair a b)) (v : Val (.pair a b))
    (hp : IArgGood ρ next p v)
    {cont : Nat → Arg (IVal Val) a → Arg (IVal Val) b → Expr Val Cont rs}
    (hcont : ∀ (ρ' : FEnv) (next' : Nat) (p₁ : Arg (IVal Val) a) (p₂ : Arg (IVal Val) b),
      next ≤ next' → (∀ {u} (k : FKey u), k.FLt next → k.fev ρ' = k.fev ρ) →
      IArgGood ρ' next' p₁ v.1 → IArgGood ρ' next' p₂ v.2 →
      wp Γ Q X (cont next' p₁ p₂) m) :
    wp Γ Q X (splitPairIVal next p cont) m := by
  dsimp only [splitPairIVal]
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

private theorem emitSelect_sameKey_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} (c : Arg Val .bool) {t : Ty} (ρ : FEnv) (next : Nat)
    {aT aE : Arg (IVal Val) t} {vT vE : Val t}
    (hT : IArgGood ρ next aT vT) (hE : IArgGood ρ next aE vE)
    (hbeq : fKeyBeq (ikey aT) (ikey aE) = true)
    {cont : Nat → Arg (IVal Val) t → Expr Val Cont rs}
    (hcont : ∀ ρ' next' (r : Arg (IVal Val) t), next ≤ next' →
      (∀ {u} (k : FKey u), k.FLt next → k.fev ρ' = k.fev ρ) →
      IArgGood ρ' next' r (if c.val then vT else vE) → wp Γ Q X (cont next' r) m) :
    wp Γ Q X (cont next aT) m := by
  have heq : ikey aT = ikey aE := fKeyBeq_iff_eq.1 hbeq
  have hveq : vT = vE := by rw [← hT.2.1, heq, hE.2.1]
  have hgood : IArgGood ρ next aT (if c.val then vT else vE) := by
    cases c.val <;> simp only [↓reduceIte, Bool.false_eq_true]
    · exact hveq ▸ hT
    · exact hT
  exact hcont ρ next aT (Nat.le_refl _) (fun _ _ => rfl) hgood

private theorem emitSelectTyIVal_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} (c : Arg Val .bool) :
    (t : Ty) → isSelectTy t = true → (ρ : FEnv) → (next : Nat) →
    {aT aE : Arg (IVal Val) t} → {vT vE : Val t} →
    IArgGood ρ next aT vT → IArgGood ρ next aE vE →
    {cont : Nat → Arg (IVal Val) t → Expr Val Cont rs} →
    (∀ ρ' next' (r : Arg (IVal Val) t), next ≤ next' →
      (∀ {u} (k : FKey u), k.FLt next → k.fev ρ' = k.fev ρ) →
      IArgGood ρ' next' r (if c.val then vT else vE) →
      wp Γ Q X (cont next' r) m) →
    wp Γ Q X (emitSelectTyIVal c t next aT aE cont) m
  | .bool, _, ρ, next, aT, aE, vT, vE, hT, hE, cont, hcont
  | .bits _, _, ρ, next, aT, aE, vT, vE, hT, hE, cont, hcont => by
    dsimp only [emitSelectTyIVal]
    cases hbeq : fKeyBeq (ikey aT) (ikey aE)
    · simp only [Bool.false_eq_true, ↓reduceIte, wp_let_op3, OpCode.wp_select]
      let rv := if c.val then vT else vE
      have hr : (if c.val then (iout aT).val else (iout aE).val) = rv := by
        rw [hT.1, hE.1]
      refine hcont (fupd ρ next rv) (next + 1)
        (.var (.var (if c.val then (iout aT).val else (iout aE).val), .var next)) (by omega)
        (fun _ hk => FKey.fev_fupd _ hk)
        ⟨hr, ?_, by dsimp only [ikey, FKey.FLt]; exact Nat.lt_succ_self _⟩
      dsimp only [ikey, FKey.fev]; rw [fupd_eq]
    · simp only [↓reduceIte]
      exact emitSelect_sameKey_wp c ρ next hT hE hbeq hcont
  | .float _, ht, _, _, _, _, _, _, _, _, _, _ => by simp [isSelectTy, Ty.hasFloat] at ht
  | .pair a b, ht, ρ, next, aT, aE, vT, vE, hT, hE, cont, hcont => by
    simp only [isSelectTy, Ty.hasFloat, Bool.or_eq_false_iff, Bool.not_eq_true'] at ht
    have hta : isSelectTy a = true := by simp [isSelectTy, ht.1]
    have htb : isSelectTy b = true := by simp [isSelectTy, ht.2]
    dsimp only [emitSelectTyIVal]
    cases hbeq : fKeyBeq (ikey aT) (ikey aE)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine splitPairIVal_wp ρ next aT vT hT fun ρ₁ next₁ aT₁ aT₂ hle₁ hev₁ hT₁ hT₂ => ?_
      have hE' := iargGood_mono hle₁ hev₁ hE
      refine splitPairIVal_wp ρ₁ next₁ aE vE hE' fun ρ₂ next₂ aE₁ aE₂ hle₂ hev₂ hE₁ hE₂ => ?_
      have hT₁' := iargGood_mono hle₂ hev₂ hT₁
      have hT₂' := iargGood_mono hle₂ hev₂ hT₂
      refine emitSelectTyIVal_wp c a hta ρ₂ next₂ hT₁' hE₁
        fun ρ₃ next₃ r₁ hle₃ hev₃ hr₁ => ?_
      refine emitSelectTyIVal_wp c b htb ρ₃ next₃
        (iargGood_mono hle₃ hev₃ hT₂') (iargGood_mono hle₃ hev₃ hE₂)
        fun ρ₄ next₄ r₂ hle₄ hev₄ hr₂ => ?_
      refine mkPairIValArg_wp ρ₄ next₄ (iargGood_mono hle₄ hev₄ hr₁) hr₂
        fun ρ₅ next₅ r hle₅ hev₅ hr => ?_
      have hle_all : next ≤ next₅ :=
        Nat.le_trans hle₁ (Nat.le_trans hle₂ (Nat.le_trans hle₃ (Nat.le_trans hle₄ hle₅)))
      have hev_all : ∀ {u} (k : FKey u), k.FLt next → k.fev ρ₅ = k.fev ρ := fun k hk =>
        (hev₅ k (hk.le (Nat.le_trans hle₁ (Nat.le_trans hle₂ (Nat.le_trans hle₃ hle₄))))).trans
        ((hev₄ k (hk.le (Nat.le_trans hle₁ (Nat.le_trans hle₂ hle₃)))).trans
        ((hev₃ k (hk.le (Nat.le_trans hle₁ hle₂))).trans
        ((hev₂ k (hk.le hle₁)).trans (hev₁ k hk))))
      have hr' : IArgGood ρ₅ next₅ r (if c.val then vT else vE) := by
        cases hcv : c.val <;> simpa [hcv] using hr
      exact hcont ρ₅ next₅ r hle_all hev_all hr'
    · simp only [↓reduceIte]
      exact emitSelect_sameKey_wp c ρ next hT hE hbeq hcont

theorem emitSelectTupIVal_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} (c : Arg Val .bool) :
    (ts : List Ty) → isSelectSig ts = true → (ρ : FEnv) → (next : Nat) →
    {asT asE : Tup (Arg (IVal Val)) ts} → {vsT vsE : Tup Val ts} →
    IArgsGood ρ next asT vsT → IArgsGood ρ next asE vsE →
    {cont : Nat → Tup (Arg (IVal Val)) ts → Expr Val Cont rs} →
    (∀ ρ' next' (sel : Tup (Arg (IVal Val)) ts), next ≤ next' →
      (∀ {u} (k : FKey u), k.FLt next → k.fev ρ' = k.fev ρ) →
      IArgsGood ρ' next' sel (if c.val then vsT else vsE) →
      wp Γ Q X (cont next' sel) m) →
    wp Γ Q X (emitSelectTupIVal c ts next asT asE cont) m
  | [], _, ρ, next, (), (), (), (), _, _, _, hcont =>
    hcont ρ next () (Nat.le_refl _) (fun _ _ => rfl) (by cases c.val <;> trivial)
  | t :: ts, hts, ρ, next, (aT, asT), (aE, asE), (vT, vsT), (vE, vsE),
    ⟨haT, hasT⟩, ⟨haE, hasE⟩, cont, hcont => by
    simp only [isSelectSig, List.all_cons, Bool.and_eq_true] at hts
    dsimp only [emitSelectTupIVal]
    refine emitSelectTyIVal_wp c t hts.1 ρ next haT haE fun ρ₁ next₁ r hle₁ hev₁ hr => ?_
    refine emitSelectTupIVal_wp c ts hts.2 ρ₁ next₁
      (iargsGood_mono hle₁ hev₁ hasT) (iargsGood_mono hle₁ hev₁ hasE)
      fun ρ₂ next₂ rs' hle₂ hev₂ hrs' => ?_
    have hev_all : ∀ {u} (k : FKey u), k.FLt next → k.fev ρ₂ = k.fev ρ := fun k hk =>
      (hev₂ k (hk.le hle₁)).trans (hev₁ k hk)
    have hgood : IArgsGood (ts := t :: ts) ρ₂ next₂ (r, rs')
        (if c.val then ((vT, vsT) : Tup Val (t :: ts)) else (vE, vsE)) := by
      have hr' := iargGood_mono hle₂ hev₂ hr
      cases hcv : c.val
      · rw [hcv] at hr' hrs'
        simp only [Bool.false_eq_true, ↓reduceIte] at hr' hrs' ⊢
        exact ⟨hr', hrs'⟩
      · rw [hcv] at hr' hrs'
        simp only [↓reduceIte] at hr' hrs' ⊢
        exact ⟨hr', hrs'⟩
    exact hcont ρ₂ next₂ (r, rs') (Nat.le_trans hle₁ hle₂) hev_all hgood

theorem emitSelectTup_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (c : Arg Val .bool) (ts : List Ty) (hts : isSelectSig ts = true) (ρ : FEnv) (next : Nat)
    {asT asE : Tup (Arg (IVal Val)) ts} {vsT vsE : Tup Val ts}
    (hT : IArgsGood ρ next asT vsT) (hE : IArgsGood ρ next asE vsE)
    {cont : Tup (Arg Val) ts → Expr Val Cont rs}
    (hcont : ∀ (sel : Tup (Arg Val) ts),
      vals sel = (if c.val then vsT else vsE) → wp Γ Q X (cont sel) m) :
    wp Γ Q X (emitSelectTup c ts next asT asE cont) m :=
  emitSelectTupIVal_wp c ts hts ρ next hT hE fun _ _ sel _ _ hsel =>
    hcont (tupIOut sel) (IArgsGood.iout_vals hsel)

theorem isSelectTyWith_imp :
    ∀ (bitsOnly : Bool) (t : Ty), isSelectTyWith bitsOnly t = true → isSelectTy t = true
  | false, _, h => h
  | true, .bits _, _ => rfl
  | true, .bool, h | true, .float _, h | true, .pair _ _, h => by
      dsimp only [isSelectTyWith] at h; cases h

theorem isSelectSigWith_imp (bitsOnly : Bool) (ts : List Ty)
    (h : isSelectSigWith bitsOnly ts = true) : isSelectSig ts = true := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [isSelectSigWith, List.all_cons, Bool.and_eq_true] at h
    simp only [isSelectSig, List.all_cons, Bool.and_eq_true]
    exact ⟨isSelectTyWith_imp bitsOnly t h.1, ih h.2⟩

theorem emitSelectTy_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (c : Arg Val .bool) (t : Ty) (ht : isSelectTy t = true) (ρ : FEnv) (next : Nat)
    {aT aE : Arg (IVal Val) t} {vT vE : Val t}
    (hT : IArgGood ρ next aT vT) (hE : IArgGood ρ next aE vE)
    {cont : Nat → Arg Val t → Expr Val Cont rs}
    (hcont : ∀ next' (sel : Arg Val t), sel.val = (if c.val then vT else vE) →
      wp Γ Q X (cont next' sel) m) :
    wp Γ Q X (emitSelectTy c t next aT aE cont) m :=
  emitSelectTyIVal_wp c t ht ρ next hT hE fun _ next' r _ _ hr =>
    hcont next' (iout r) hr.1

theorem emitSelectTy_ext_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (c : Arg Val .bool) (t : Ty) (ht : isSelectTy t = true) (ρ : FEnv) (next : Nat)
    {aT aE : Arg (IVal Val) t} {vT vE : Val t}
    (hT : IArgGood ρ next aT vT) (hE : IArgGood ρ next aE vE)
    {cont : Nat → Arg Val t → Expr Val Cont rs}
    (hcont : ∀ ρ' next' (sel : Arg Val t), next ≤ next' →
      (∀ {u} (k : FKey u), k.FLt next → k.fev ρ' = k.fev ρ) →
      sel.val = (if c.val then vT else vE) →
      wp Γ Q X (cont next' sel) m) :
    wp Γ Q X (emitSelectTy c t next aT aE cont) m :=
  emitSelectTyIVal_wp c t ht ρ next hT hE fun ρ' next' r hle hev hr =>
    hcont ρ' next' (iout r) hle hev hr.1

/-! ## Store-sinking symbolic key & table helpers -/

@[expose] def fKeysEval (ρ : FEnv) : {ts : List Ty} → Tup FKey ts → Tup Val ts
  | [], () => ()
  | _ :: _, (k, ks) => (k.fev ρ, fKeysEval ρ ks)

@[expose] def fKeysLt (b : Nat) : {ts : List Ty} → Tup FKey ts → Prop
  | [], () => True
  | _ :: _, (k, ks) => k.FLt b ∧ fKeysLt b ks

theorem fKeysBeq_iff_eq : {ts : List Ty} → {a b : Tup FKey ts} → fKeysBeq a b = true ↔ a = b
  | [], (), () => by simp [fKeysBeq]
  | _ :: _, (a, as), (b, bs) => by
    simp only [fKeysBeq, Bool.and_eq_true, fKeyBeq_iff_eq, fKeysBeq_iff_eq, Prod.mk.injEq]

theorem fKeysLt.le {b₁ b₂ : Nat} (h : b₁ ≤ b₂) :
    {ts : List Ty} → {ks : Tup FKey ts} → fKeysLt b₁ ks → fKeysLt b₂ ks
  | [], () => fun _ => trivial
  | _ :: _, (_, _) => fun ⟨h1, h2⟩ => ⟨h1.le h, fKeysLt.le h h2⟩

theorem fKeysLt_freshFKeys : (ts : List Ty) → (n : Nat) →
    fKeysLt (n + ts.length) (freshFKeys ts n)
  | [], _ => trivial
  | _ :: ts, n => by
    dsimp only [freshFKeys, fKeysLt, FKey.FLt]
    refine ⟨?_, ?_⟩
    · show n < n + (ts.length + 1); omega
    · exact (fKeysLt_freshFKeys ts (n + 1)).le
        (by show n + 1 + ts.length ≤ n + (ts.length + 1); omega)

theorem fKeysEval_fupdTup {ρ ρ' : FEnv} {b : Nat}
    (heq : ∀ {u} (k : FKey u), k.FLt b → k.fev ρ' = k.fev ρ) :
    {ts : List Ty} → {ks : Tup FKey ts} → fKeysLt b ks → fKeysEval ρ' ks = fKeysEval ρ ks
  | [], (), _ => rfl
  | _ :: _, (_, _), ⟨h1, h2⟩ => by
    dsimp only [fKeysEval]
    rw [heq _ h1, fKeysEval_fupdTup heq h2]

theorem fKeysEval_freshFKeys (ρ : FEnv) : (ts : List Ty) → (n : Nat) → (r : Tup Val ts) →
    fKeysEval (fupdTup ρ n r) (freshFKeys ts n) = r
  | [], _, () => rfl
  | t :: ts, n, (x, xs) => by
    dsimp only [freshFKeys, fKeysEval, FKey.fev, fupdTup]
    rw [fupdTup_lt (fupd ρ n x) xs (Nat.lt_succ_self n), fupd_eq,
        fKeysEval_freshFKeys (fupd ρ n x) ts (n + 1) xs]

theorem findSymOp_mem : ∀ (ops : List SymOpEntry) (sig ts : List Ty)
    (code : OpCode sig ts) (args : Tup FKey sig) (res : Tup FKey ts),
    findSymOp ops sig ts code args = some res → ⟨sig, ts, code, args, res⟩ ∈ ops
  | [], _, _, _, _, _, h => by simp [findSymOp] at h
  | e :: es, sig, ts, code, args, res, h => by
    dsimp only [findSymOp] at h
    cases hs : listTyDecEq e.sig sig with
    | isFalse _ =>
      rw [hs] at h; exact List.mem_cons_of_mem _ (findSymOp_mem es sig ts code args res h)
    | isTrue hs' =>
      cases hr : listTyDecEq e.ts ts with
      | isFalse _ =>
        rw [hs, hr] at h
        exact List.mem_cons_of_mem _ (findSymOp_mem es sig ts code args res h)
      | isTrue hr' =>
        rcases e with ⟨esig, ets, ecode, eargs, eres⟩
        dsimp only at hs' hr'
        subst hs' hr'
        simp only [hs, hr] at h
        cases hka : fKeysBeq eargs args with
        | false =>
          simp only [hka, Bool.false_eq_true, ↓reduceIte] at h
          exact List.mem_cons_of_mem _ (findSymOp_mem es _ _ code args res h)
        | true =>
          simp only [hka, ↓reduceIte] at h
          rw [fKeysBeq_iff_eq] at hka
          cases hc : decEq ecode code with
          | isFalse _ =>
            rw [hc] at h
            exact List.mem_cons_of_mem _ (findSymOp_mem es _ _ code args res h)
          | isTrue hc' =>
            rw [hc] at h
            simp only [Option.some.injEq] at h
            subst hka hc' h
            exact List.mem_cons_self

theorem findSymLoad_mem : ∀ (loads : List SymLoadEntry) (lt : Ty) (addr : FKey i64)
    (e : SymLoadEntry), findSymLoad loads lt addr = some e →
    e ∈ loads ∧ e.lt = lt ∧ e.addr = addr
  | [], _, _, _, h => by simp [findSymLoad] at h
  | x :: xs, lt, addr, e, h => by
    dsimp only [findSymLoad] at h
    cases ht : tyDecEq x.lt lt with
    | isFalse _ =>
      rw [ht] at h
      have ih := findSymLoad_mem xs lt addr e h
      exact ⟨List.mem_cons_of_mem _ ih.1, ih.2⟩
    | isTrue ht' =>
      rw [ht] at h
      cases ha : fKeyBeq x.addr addr with
      | false =>
        simp only [ha, Bool.false_eq_true, ↓reduceIte] at h
        have ih := findSymLoad_mem xs lt addr e h
        exact ⟨List.mem_cons_of_mem _ ih.1, ih.2⟩
      | true =>
        simp only [ha, ↓reduceIte, Option.some.injEq] at h
        rw [fKeyBeq_iff_eq] at ha
        subst h
        exact ⟨List.mem_cons_self, ht', ha⟩

/-! ## `emitSelectTy` / `emitSelectTup` WF preservation -/

section WfSelect
variable {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}

@[expose] def IValRel (G' : Ctx V₁ V₂) {t : Ty} (a₁ : IVal V₁ t) (a₂ : IVal V₂ t) : Prop :=
  ArgRel G' t a₁.1 a₂.1 ∧ a₁.2 = a₂.2

private def iMetaKit : OutMetaKit IVal FKey where
  out p := p.1
  tag p := p.2
  fresh v k := (.var v, .var k)
  out_fresh _ _ := rfl
  tag_fresh _ _ _ := rfl

theorem IValRel.weaken {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂)
    {t : Ty} {a₁ : IVal V₁ t} {a₂ : IVal V₂ t} (h : IValRel G₁ a₁ a₂) : IValRel G₂ a₁ a₂ :=
  iMetaKit.rel_weaken hsub h

@[expose] def IRelG (G' : Ctx V₁ V₂) (G : Ctx (IVal V₁) (IVal V₂)) : Prop :=
  ∀ p ∈ G, IValRel G' p.2.1 p.2.2

theorem IRelG.weaken {G₁ G₂ : Ctx V₁ V₂} {G : Ctx (IVal V₁) (IVal V₂)}
    (hG : IRelG G₁ G) (hsub : ∀ p ∈ G₁, p ∈ G₂) : IRelG G₂ G :=
  iMetaKit.toRelKit.relG_weaken hsub hG

theorem IRelG.cons {G' : Ctx V₁ V₂} {G : Ctx (IVal V₁) (IVal V₂)} (hG : IRelG G' G)
    {t : Ty} {a₁ : IVal V₁ t} {a₂ : IVal V₂ t} (ha : IValRel G' a₁ a₂) :
    IRelG G' (⟨t, a₁, a₂⟩ :: G) :=
  iMetaKit.toRelKit.relG_cons ha hG

theorem IRelG.append {G' : Ctx V₁ V₂} {G H : Ctx (IVal V₁) (IVal V₂)}
    (h1 : IRelG G' G) (h2 : IRelG G' H) : IRelG G' (H ++ G) :=
  iMetaKit.toRelKit.relG_append h2 h1

theorem IRelG.freshIVals {G' : Ctx V₁ V₂} {G : Ctx (IVal V₁) (IVal V₂)}
    (hG : IRelG G' G) {ts : List Ty} (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts) (b : Nat) :
    IRelG (Tup.zip xs₁ xs₂ ++ G')
      (Tup.zip (freshIVals ts xs₁ b) (freshIVals ts xs₂ b) ++ G) :=
  iMetaKit.toRelKit.relG_freshTup ts xs₁ xs₂ b hG

theorem IRelG.freshOne {G' : Ctx V₁ V₂} {G : Ctx (IVal V₁) (IVal V₂)}
    (hG : IRelG G' G) {t : Ty} (v₁ : V₁ t) (v₂ : V₂ t) (b : Nat) :
    IRelG (⟨t, v₁, v₂⟩ :: G') (⟨t, (.var v₁, .var b), (.var v₂, .var b)⟩ :: G) :=
  iMetaKit.toRelKit.relG_freshOne v₁ v₂ b hG

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

@[expose] def IArgRel (G' : Ctx V₁ V₂) {t : Ty}
    (a₁ : Arg (IVal V₁) t) (a₂ : Arg (IVal V₂) t) : Prop :=
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

private theorem mkPairIValArg_wf {rs : List Ty} {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} {a b : Ty}
    (next : Nat) {x₁ : Arg (IVal V₁) a} {x₂ : Arg (IVal V₂) a}
    {y₁ : Arg (IVal V₁) b} {y₂ : Arg (IVal V₂) b}
    (hx : IArgRel G' x₁ x₂) (hy : IArgRel G' y₁ y₂)
    {cont₁ : Nat → Arg (IVal V₁) (.pair a b) → Expr V₁ L₁ rs}
    {cont₂ : Nat → Arg (IVal V₂) (.pair a b) → Expr V₂ L₂ rs}
    (hcont : ∀ G'' next' r₁ r₂, (∀ p ∈ G', p ∈ G'') → IArgRel G'' r₁ r₂ →
      Wf G'' D' (cont₁ next' r₁) (cont₂ next' r₂)) :
    Wf G' D' (mkPairIValArg next x₁ y₁ cont₁) (mkPairIValArg next x₂ y₂ cont₂) := by
  have hxo := hx.1; have hyo := hy.1
  dsimp only [mkPairIValArg]
  cases hx1 : iout x₁ <;> cases hx2 : iout x₂ <;> rw [hx1, hx2] at hxo <;>
    cases hy1 : iout y₁ <;> cases hy2 : iout y₂ <;> rw [hy1, hy2] at hyo <;>
    dsimp only
  all_goals
    have hxrel := hxo
    have hyrel := hyo
    cases hxo <;> cases hyo
  all_goals first
    | exact hcont G' next (.imm _) (.imm _) (fun _ h => h) ⟨.imm _, rfl⟩
    | (refine .let_ (.mk (.mkpair a b) (.cons hxrel (.cons hyrel .nil)))
         fun (p₁, ()) (p₂, ()) => ?_
       exact hcont (Tup.zip (as := [.pair a b]) (p₁, ()) (p₂, ()) ++ G') (next + 1)
         (.var (.var p₁, .var next)) (.var (.var p₂, .var next))
         (fun _ hq => List.mem_append_right _ hq) ⟨.var List.mem_cons_self, rfl⟩)

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
  dsimp only [splitPairIVal]
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

private theorem emitSelectTyIVal_wf {rs : List Ty} {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂}
    {c₁ : Arg V₁ .bool} {c₂ : Arg V₂ .bool} (hc : ArgRel G' .bool c₁ c₂) :
    (t : Ty) → (next : Nat) →
    {aT₁ aE₁ : Arg (IVal V₁) t} → {aT₂ aE₂ : Arg (IVal V₂) t} →
    IArgRel G' aT₁ aT₂ → IArgRel G' aE₁ aE₂ →
    {cont₁ : Nat → Arg (IVal V₁) t → Expr V₁ L₁ rs} →
    {cont₂ : Nat → Arg (IVal V₂) t → Expr V₂ L₂ rs} →
    (∀ G'' next' r₁ r₂, (∀ p ∈ G', p ∈ G'') → IArgRel G'' r₁ r₂ →
      Wf G'' D' (cont₁ next' r₁) (cont₂ next' r₂)) →
    Wf G' D' (emitSelectTyIVal c₁ t next aT₁ aE₁ cont₁)
             (emitSelectTyIVal c₂ t next aT₂ aE₂ cont₂)
  | .bool, next, aT₁, aE₁, aT₂, aE₂, hT, hE, cont₁, cont₂, hcont
  | .bits _, next, aT₁, aE₁, aT₂, aE₂, hT, hE, cont₁, cont₂, hcont => by
    dsimp only [emitSelectTyIVal]; rw [hT.2, hE.2]
    cases fKeyBeq (ikey aT₂) (ikey aE₂)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine .let_ (.mk (.select _) (.cons hc (.cons hT.1 (.cons hE.1 .nil))))
        fun (r₁, ()) (r₂, ()) => ?_
      exact hcont _ (next + 1) (.var (.var r₁, .var next)) (.var (.var r₂, .var next))
        (fun _ hq => List.mem_cons_of_mem _ hq) ⟨.var List.mem_cons_self, rfl⟩
    · exact hcont G' next aT₁ aT₂ (fun _ h => h) hT
  | .float _, next, _, _, _, _, hT, _, _, _, hcont =>
    hcont G' next _ _ (fun _ h => h) hT
  | .pair a b, next, aT₁, aE₁, aT₂, aE₂, hT, hE, cont₁, cont₂, hcont => by
    dsimp only [emitSelectTyIVal]; rw [hT.2, hE.2]
    cases fKeyBeq (ikey aT₂) (ikey aE₂)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine splitPairIVal_wf next hT fun G₁ next₁ aT₁₁ aT₂₁ aT₁₂ aT₂₂ hsub₁ hT₁ hT₂ => ?_
      refine splitPairIVal_wf next₁ (iargRel_weaken hsub₁ hE)
        fun G₂ next₂ aE₁₁ aE₂₁ aE₁₂ aE₂₂ hsub₂ hE₁ hE₂ => ?_
      have hc₂ := hc.weaken (fun p hp => hsub₂ p (hsub₁ p hp))
      refine emitSelectTyIVal_wf hc₂ a next₂ (iargRel_weaken hsub₂ hT₁) hE₁
        fun G₃ next₃ r₁₁ r₂₁ hsub₃ hr₁ => ?_
      have hc₃ := hc₂.weaken hsub₃
      refine emitSelectTyIVal_wf hc₃ b next₃
        (iargRel_weaken (fun p hp => hsub₃ p (hsub₂ p hp)) hT₂) (iargRel_weaken hsub₃ hE₂)
        fun G₄ next₄ r₁₂ r₂₂ hsub₄ hr₂ => ?_
      refine mkPairIValArg_wf next₄ (iargRel_weaken hsub₄ hr₁) hr₂
        fun G₅ next₅ r₁ r₂ hsub₅ hr => ?_
      exact hcont G₅ next₅ r₁ r₂
        (fun p hp => hsub₅ p (hsub₄ p (hsub₃ p (hsub₂ p (hsub₁ p hp))))) hr
    · exact hcont G' next aT₁ aT₂ (fun _ h => h) hT

theorem emitSelectTy_wf {rs : List Ty} {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂}
    {c₁ : Arg V₁ .bool} {c₂ : Arg V₂ .bool} (hc : ArgRel G' .bool c₁ c₂)
    (t : Ty) (next : Nat) {aT₁ aE₁ : Arg (IVal V₁) t} {aT₂ aE₂ : Arg (IVal V₂) t}
    (hT : IArgRel G' aT₁ aT₂) (hE : IArgRel G' aE₁ aE₂)
    {cont₁ : Nat → Arg V₁ t → Expr V₁ L₁ rs} {cont₂ : Nat → Arg V₂ t → Expr V₂ L₂ rs}
    (hcont : ∀ G'' next' r₁ r₂, (∀ p ∈ G', p ∈ G'') → ArgRel G'' t r₁ r₂ →
      Wf G'' D' (cont₁ next' r₁) (cont₂ next' r₂)) :
    Wf G' D' (emitSelectTy c₁ t next aT₁ aE₁ cont₁)
             (emitSelectTy c₂ t next aT₂ aE₂ cont₂) :=
  emitSelectTyIVal_wf hc t next hT hE fun G'' next' r₁ r₂ hsub hr =>
    hcont G'' next' (iout r₁) (iout r₂) hsub hr.1

theorem emitSelectTupIVal_wf {rs : List Ty} {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂}
    {c₁ : Arg V₁ .bool} {c₂ : Arg V₂ .bool} (hc : ArgRel G' .bool c₁ c₂) :
    (ts : List Ty) → (next : Nat) →
    {asT₁ asE₁ : Tup (Arg (IVal V₁)) ts} → {asT₂ asE₂ : Tup (Arg (IVal V₂)) ts} →
    TRel (fun _ => IArgRel G') asT₁ asT₂ → TRel (fun _ => IArgRel G') asE₁ asE₂ →
    {cont₁ : Nat → Tup (Arg (IVal V₁)) ts → Expr V₁ L₁ rs} →
    {cont₂ : Nat → Tup (Arg (IVal V₂)) ts → Expr V₂ L₂ rs} →
    (∀ G'' next' sel₁ sel₂, (∀ p ∈ G', p ∈ G'') → TRel (fun _ => IArgRel G'') sel₁ sel₂ →
      Wf G'' D' (cont₁ next' sel₁) (cont₂ next' sel₂)) →
    Wf G' D' (emitSelectTupIVal c₁ ts next asT₁ asE₁ cont₁)
             (emitSelectTupIVal c₂ ts next asT₂ asE₂ cont₂)
  | [], next, (), (), (), (), .nil, .nil, _, _, hcont =>
    hcont G' next () () (fun _ h => h) .nil
  | t :: ts, next, (aT₁, asT₁), (aE₁, asE₁), (aT₂, asT₂), (aE₂, asE₂),
    .cons hT hsT, .cons hE hsE, cont₁, cont₂, hcont => by
    dsimp only [emitSelectTupIVal]
    refine emitSelectTyIVal_wf hc t next hT hE fun G₁ next' r₁ r₂ hsub₁ hr => ?_
    have hsT' : TRel (fun _ => IArgRel G₁) asT₁ asT₂ :=
      TRel.mono (fun _ _ _ h => iargRel_weaken hsub₁ h) hsT
    have hsE' : TRel (fun _ => IArgRel G₁) asE₁ asE₂ :=
      TRel.mono (fun _ _ _ h => iargRel_weaken hsub₁ h) hsE
    refine emitSelectTupIVal_wf (hc.weaken hsub₁) ts next' hsT' hsE'
      fun G₂ next'' rs₁ rs₂ hsub₂ hrs => ?_
    exact hcont G₂ next'' (r₁, rs₁) (r₂, rs₂) (fun p hp => hsub₂ p (hsub₁ p hp))
      (.cons (iargRel_weaken hsub₂ hr) hrs)

private theorem trel_iout_of_iargRel {G' : Ctx V₁ V₂} :
    {ts : List Ty} → {as₁ : Tup (Arg (IVal V₁)) ts} → {as₂ : Tup (Arg (IVal V₂)) ts} →
    TRel (fun _ => IArgRel G') as₁ as₂ → TRel (ArgRel G') (tupIOut as₁) (tupIOut as₂)
  | [], (), (), .nil => .nil
  | _ :: _, (_, _), (_, _), .cons h hs => .cons h.1 (trel_iout_of_iargRel hs)

theorem emitSelectTup_wf {rs : List Ty} {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂}
    {c₁ : Arg V₁ .bool} {c₂ : Arg V₂ .bool} (hc : ArgRel G' .bool c₁ c₂)
    (ts : List Ty) (next : Nat)
    {asT₁ asE₁ : Tup (Arg (IVal V₁)) ts} {asT₂ asE₂ : Tup (Arg (IVal V₂)) ts}
    (hT : TRel (fun _ => IArgRel G') asT₁ asT₂)
    (hE : TRel (fun _ => IArgRel G') asE₁ asE₂)
    {cont₁ : Tup (Arg V₁) ts → Expr V₁ L₁ rs} {cont₂ : Tup (Arg V₂) ts → Expr V₂ L₂ rs}
    (hcont : ∀ G'' sel₁ sel₂, (∀ p ∈ G', p ∈ G'') → TRel (ArgRel G'') sel₁ sel₂ →
      Wf G'' D' (cont₁ sel₁) (cont₂ sel₂)) :
    Wf G' D' (emitSelectTup c₁ ts next asT₁ asE₁ cont₁)
             (emitSelectTup c₂ ts next asT₂ asE₂ cont₂) :=
  emitSelectTupIVal_wf hc ts next hT hE fun G'' _ sel₁ sel₂ hsub hsel =>
    hcont G'' (tupIOut sel₁) (tupIOut sel₂) hsub (trel_iout_of_iargRel hsel)

/-! ## Diamond shape and check/hoist lemmas -/

@[expose] def ArmTarget.sig (rs : List Ty) : ArmTarget → List Ty
  | .loc _ jTs => jTs
  | .tag _ jTs => jTs
  | .ret => rs

@[expose] def HasArmShape {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (jTs : List Ty) :
    ArmPlan → Expr V L rs → Prop
  | .jump, .jump (ts := ts) _ _ => ts = jTs
  | .ret, .ret _ => rs = jTs
  | .let_ rest, .let_ _ k => ∀ xs, HasArmShape jTs rest (k xs)
  | .jnz pT pE, .jnz _ t e => HasArmShape jTs pT t ∧ HasArmShape jTs pE e
  | _, _ => False

@[expose] def HasStoreTailShape {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (jTs : List Ty) : StoreTail → Expr V L rs → Prop
  | .jump, .jump (ts := ts) _ _ => ts = jTs
  | .ret, .ret _ => rs = jTs
  | .let_ rest, .let_ _ k => ∀ xs, HasStoreTailShape jTs rest (k xs)
  | _, _ => False

@[expose] def HasStoreStepShape {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (jTs : List Ty) (st : Ty) : StoreStep → Expr V L rs → Prop
  | .let_ rest, .let_ _ k => ∀ xs, HasStoreStepShape jTs st rest (k xs)
  | .loadEmit rest, .load _ _ k => ∀ v, HasStoreStepShape jTs st rest (k v)
  | .loadReuse _ rest, .load _ _ k => ∀ v, HasStoreStepShape jTs st rest (k v)
  | .store tail, .store (t := st') _ _ k => st' = st ∧ HasStoreTailShape jTs tail k
  | _, _ => False

@[expose] def HasDiamondShape {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (jTs : List Ty) :
    DiamondPlan → Expr V L rs → Prop
  | .jnz pT pE, .jnz _ t e => HasArmShape jTs pT t ∧ HasArmShape jTs pE e
  | .jnzStore sp, .jnz _ t e =>
    HasStoreStepShape jTs sp.storeTy sp.armT t ∧ HasStoreStepShape jTs sp.storeTy sp.armE e
  | .let_ rest, .let_ _ k => ∀ xs, HasDiamondShape jTs rest (k xs)
  | .load rest, .load _ _ k => ∀ v, HasDiamondShape jTs rest (k v)
  | .store rest, .store _ _ k => HasDiamondShape jTs rest k
  | .call rest, .call _ _ k => ∀ xs, HasDiamondShape jTs rest (k xs)
  | _, _ => False

@[expose] def IKeyEq {V₁ V₂ : Ty → Type} (G : Ctx (IVal V₁) (IVal V₂)) : Prop :=
  ∀ p ∈ G, p.2.1.2 = p.2.2.2

theorem IKeyEq.dummyIVals {V₁ V₂ : Ty → Type} {G : Ctx (IVal V₁) (IVal V₂)} (hG : IKeyEq G)
    (ts : List Ty) (n : Nat) :
    IKeyEq (Tup.zip (dummyIVals ts n) (dummyIVals ts n) ++ G) := by
  intro p hp
  simp only [List.mem_append] at hp
  rcases hp with h | h
  · induction ts generalizing n with
    | nil => cases h
    | cons _ _ ih =>
      simp only [Tup.zip, List.mem_cons] at h
      rcases h with rfl | h
      · rfl
      · exact ih (n + 1) h
  · exact hG p h

theorem IKeyEq.dummyKeyIVals {V₁ V₂ : Ty → Type} {G : Ctx (IVal V₁) (IVal V₂)} (hG : IKeyEq G) :
    (ts : List Ty) → (ks : Tup FKey ts) →
    IKeyEq (Tup.zip (dummyKeyIVals ts ks) (dummyKeyIVals ts ks) ++ G)
  | [], (), p, hp => hG p hp
  | _ :: ts, (k, ks), p, hp => by
    simp only [Tup.zip, List.cons_append, List.mem_cons] at hp
    rcases hp with rfl | hp
    · rfl
    · exact IKeyEq.dummyKeyIVals hG ts ks p hp

theorem IKeyEq.oneSame {V₁ V₂ : Ty → Type} {G : Ctx (IVal V₁) (IVal V₂)} (hG : IKeyEq G)
    {t : Ty} (a₁ : Arg V₁ t) (a₂ : Arg V₂ t) (k : FKey t) :
    IKeyEq (⟨t, (a₁, k), (a₂, k)⟩ :: G) := by
  intro p hp; cases hp with | head => rfl | tail _ h => exact hG p h

theorem argRel_ikey_of_iKeyEq {V₁ V₂ : Ty → Type} {G : Ctx (IVal V₁) (IVal V₂)} (hG : IKeyEq G)
    {t : Ty} {a₁ : Arg (IVal V₁) t} {a₂ : Arg (IVal V₂) t} :
    ArgRel G t a₁ a₂ → ikey a₁ = ikey a₂
  | .var h => hG _ h
  | .imm _ => rfl

theorem trel_ikey_of_iKeyEq {V₁ V₂ : Ty → Type} {G : Ctx (IVal V₁) (IVal V₂)} (hG : IKeyEq G) :
    {ts : List Ty} → {as₁ : Tup (Arg (IVal V₁)) ts} → {as₂ : Tup (Arg (IVal V₂)) ts} →
    TRel (ArgRel G) as₁ as₂ → tupIKeys as₁ = tupIKeys as₂
  | [], (), (), .nil => rfl
  | _ :: _, (_, _), (_, _), .cons ha has => by
    have ih := trel_ikey_of_iKeyEq hG has
    dsimp only [tupIKeys, tupMapArg] at ih ⊢
    rw [argRel_ikey_of_iKeyEq hG ha, ih]

@[expose] def SLoadsRel (G' : Ctx V₁ V₂)
    (l₁ : List ((t : Ty) × IVal V₁ t)) (l₂ : List ((t : Ty) × IVal V₂ t)) : Prop :=
  l₁.length = l₂.length ∧
  ∀ (i : Nat) {t₁ : Ty} {v₁ : IVal V₁ t₁} {t₂ : Ty} {v₂ : IVal V₂ t₂},
    l₁[i]? = some ⟨t₁, v₁⟩ → l₂[i]? = some ⟨t₂, v₂⟩ →
    ∃ h : t₁ = t₂, IValRel G' (h ▸ v₁) v₂

theorem SLoadsRel.weaken {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂)
    {l₁ : List ((t : Ty) × IVal V₁ t)} {l₂ : List ((t : Ty) × IVal V₂ t)}
    (h : SLoadsRel G₁ l₁ l₂) : SLoadsRel G₂ l₁ l₂ :=
  ⟨h.1, fun i {_} {_} {_} {_} h1 h2 => let ⟨heq, hv⟩ := h.2 i h1 h2; ⟨heq, IValRel.weaken hsub hv⟩⟩

theorem SLoadsRel.append {G' : Ctx V₁ V₂}
    {l₁ : List ((t : Ty) × IVal V₁ t)} {l₂ : List ((t : Ty) × IVal V₂ t)}
    (h : SLoadsRel G' l₁ l₂) {t : Ty} {v₁ : IVal V₁ t} {v₂ : IVal V₂ t}
    (hv : IValRel G' v₁ v₂) :
    SLoadsRel G' (l₁ ++ [⟨t, v₁⟩]) (l₂ ++ [⟨t, v₂⟩]) := by
  refine ⟨by simp [h.1], fun i t₁ x₁ t₂ x₂ h1 h2 => ?_⟩
  by_cases hi : i < l₁.length
  · have hi2 : i < l₂.length := h.1 ▸ hi
    rw [List.getElem?_append_left hi] at h1
    rw [List.getElem?_append_left hi2] at h2
    exact h.2 i h1 h2
  · have hi1 : l₁.length ≤ i := Nat.le_of_not_lt hi
    have hi2 : l₂.length ≤ i := h.1 ▸ hi1
    rw [List.getElem?_append_right hi1] at h1
    rw [List.getElem?_append_right hi2] at h2
    rw [h.1] at h1
    cases hidx : i - l₂.length with
    | zero =>
      simp only [hidx, List.getElem?_cons_zero, Option.some.injEq] at h1 h2
      cases h1; cases h2
      exact ⟨rfl, hv⟩
    | succ k => simp [hidx] at h1

theorem sLoadsRel_lookup {G' : Ctx V₁ V₂}
    {l₁ : List ((t : Ty) × IVal V₁ t)} {l₂ : List ((t : Ty) × IVal V₂ t)}
    (h : SLoadsRel G' l₁ l₂) (i : Nat) :
    (l₁[i]? = none ∧ l₂[i]? = none) ∨
    (∃ (t : Ty), ∃ (v₁ : IVal V₁ t) (v₂ : IVal V₂ t),
      l₁[i]? = some ⟨t, v₁⟩ ∧ l₂[i]? = some ⟨t, v₂⟩ ∧ IValRel G' v₁ v₂) := by
  have hlen := h.1
  cases h1 : l₁[i]? <;> cases h2 : l₂[i]?
  · exact Or.inl ⟨rfl, rfl⟩
  · exfalso
    have hlt := (List.getElem?_eq_some_iff.1 h2).1
    have hge := List.getElem?_eq_none_iff.1 h1
    omega
  · exfalso
    have hlt := (List.getElem?_eq_some_iff.1 h1).1
    have hge := List.getElem?_eq_none_iff.1 h2
    omega
  · rename_i p₁ p₂
    rcases p₁ with ⟨t₁, v₁⟩; rcases p₂ with ⟨t₂, v₂⟩
    obtain ⟨heq, hv⟩ := h.2 i h1 h2
    subst heq
    exact Or.inr ⟨t₁, v₁, v₂, rfl, rfl, hv⟩

theorem checkArm_eq_of_wf {G : Ctx (IVal V₁) (IVal V₂)} {D : Ctx (JLabel L₁) (JLabel L₂)}
    {rs : List Ty} (tgt : ArmTarget)
    {e₁ : Expr (IVal V₁) (JLabel L₁) rs} {e₂ : Expr (IVal V₂) (JLabel L₂) rs}
    (hwf : Wf G D e₁ e₂) :
    (∀ p ∈ D, match p.2.1, p.2.2 with
      | .loc d₁, .loc d₂ => d₁ = d₂
      | .tag id₁ _, .tag id₂ _ => id₁ = id₂
      | .outer _, .outer _ => True
      | _, _ => False) →
    ∀ (jnzFuel letFuel next : Nat),
      checkArm tgt jnzFuel letFuel next e₁ = checkArm tgt jnzFuel letFuel next e₂ := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
    intro hD jnzFuel letFuel next
    cases hop with | mk code _ =>
    unfold checkArm
    cases isSafeOp code
    · rfl
    · cases letFuel with
      | zero => rfl
      | succ letFuel' =>
        simp only [↓reduceIte]
        exact congrArg (Option.map fun (p, r) => (ArmPlan.let_ p, r))
          (ih (dummyIVals _ next) (dummyIVals _ next) hD jnzFuel letFuel' (next + _))
  | @jump _ _ _ j₁ j₂ _ _ hj _ =>
    intro hD _ _ _
    have hjl := hD _ hj
    dsimp only at hjl
    cases j₁ <;> cases j₂ <;> cases tgt <;> simp_all [checkArm]
  | jnz _ _ _ iht ihe =>
    intro hD jnzFuel letFuel next
    cases jnzFuel with
    | zero => unfold checkArm; rfl
    | succ jnzFuel' =>
      dsimp only [checkArm, bind, Option.bind]
      rw [iht hD jnzFuel' letFuel next]
      cases checkArm tgt jnzFuel' letFuel next _ with
      | none => rfl
      | some res => dsimp only; rw [ihe hD jnzFuel' res.2 next]
  | ret _ =>
    intro _ _ _ _; unfold checkArm; rfl
  | load _ _ _ | store _ _ _ | call _ _ _ | exit _ _ | hlt | group _ _ =>
    intro _ _ _ _; unfold checkArm; rfl

theorem checkStoreTail_eq_of_wf {G : Ctx (IVal V₁) (IVal V₂)} {D : Ctx (JLabel L₁) (JLabel L₂)}
    {rs : List Ty} (tgt : ArmTarget)
    {e₁ : Expr (IVal V₁) (JLabel L₁) rs} {e₂ : Expr (IVal V₂) (JLabel L₂) rs}
    (hwf : Wf G D e₁ e₂) :
    (∀ p ∈ D, match p.2.1, p.2.2 with
      | .loc d₁, .loc d₂ => d₁ = d₂
      | .tag id₁ _, .tag id₂ _ => id₁ = id₂
      | .outer _, .outer _ => True
      | _, _ => False) →
    ∀ (letFuel : Nat), checkStoreTail tgt letFuel e₁ = checkStoreTail tgt letFuel e₂ := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
    intro hD letFuel
    cases hop with | mk code _ =>
    unfold checkStoreTail
    cases isSafeOp code
    · rfl
    · cases letFuel with
      | zero => rfl
      | succ letFuel' =>
        simp only [↓reduceIte]
        exact congrArg (Option.map StoreTail.let_)
          (ih (dummyIVals _ 0) (dummyIVals _ 0) hD letFuel')
  | @jump _ _ _ j₁ j₂ _ _ hj _ =>
    intro hD _
    have hjl := hD _ hj
    dsimp only at hjl
    cases j₁ <;> cases j₂ <;> cases tgt <;> simp_all [checkStoreTail]
  | ret _ => intro _ _; unfold checkStoreTail; rfl
  | jnz _ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | exit _ _ | hlt | group _ _ =>
    intro _ _; unfold checkStoreTail; rfl

theorem checkStoreArm_eq_of_wf {G : Ctx (IVal V₁) (IVal V₂)} {D : Ctx (JLabel L₁) (JLabel L₂)}
    {rs : List Ty} (tgt : ArmTarget) (allowNewLoads : Bool)
    {e₁ : Expr (IVal V₁) (JLabel L₁) rs} {e₂ : Expr (IVal V₂) (JLabel L₂) rs}
    (hwf : Wf G D e₁ e₂) :
    IKeyEq G →
    (∀ p ∈ D, match p.2.1, p.2.2 with
      | .loc d₁, .loc d₂ => d₁ = d₂
      | .tag id₁ _, .tag id₂ _ => id₁ = id₂
      | .outer _, .outer _ => True
      | _, _ => False) →
    ∀ (letFuel loadFuel : Nat) (tbl : SymTbl) (hits : List Nat),
      checkStoreArm tgt allowNewLoads letFuel loadFuel tbl hits e₁ =
      checkStoreArm tgt allowNewLoads letFuel loadFuel tbl hits e₂ := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
    intro hG hD letFuel loadFuel tbl hits
    cases hop with | mk code hargs =>
    unfold checkStoreArm
    cases isSafeOp code
    · rfl
    · cases letFuel with
      | zero => rfl
      | succ letFuel' =>
        simp only [↓reduceIte]
        rw [trel_ikey_of_iKeyEq hG hargs]
        exact congrArg (Option.map _)
          (ih (dummyKeyIVals _ _) (dummyKeyIVals _ _) (hG.dummyKeyIVals _ _) hD
            letFuel' loadFuel _ hits)
  | load t ha _ ih =>
    intro hG hD letFuel loadFuel tbl hits
    unfold checkStoreArm
    dsimp only
    rw [argRel_ikey_of_iKeyEq hG ha]
    cases findSymLoad tbl.loads t (ikey _) with
    | some entry =>
      dsimp only
      exact congrArg (Option.map _)
        (ih (.imm default, .var entry.vn) (.imm default, .var entry.vn)
          (hG.oneSame _ _ _) hD letFuel loadFuel tbl
          (if hits.contains entry.slot then hits else entry.slot :: hits))
    | none =>
      dsimp only
      cases allowNewLoads
      · rfl
      · cases loadFuel with
        | zero => rfl
        | succ loadFuel' =>
          dsimp only
          exact congrArg (Option.map _)
            (ih (.imm default, .var tbl.vnNext) (.imm default, .var tbl.vnNext)
              (hG.oneSame _ _ _) hD letFuel loadFuel' _ (tbl.loads.length :: hits))
  | store _ ha hk =>
    intro hG hD letFuel _ tbl hits
    unfold checkStoreArm
    rw [argRel_ikey_of_iKeyEq hG ha, checkStoreTail_eq_of_wf tgt hk hD letFuel]
  | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt | group _ _ =>
    intro _ _ _ _ _ _; unfold checkStoreArm; rfl

theorem checkStoreArms_eq_of_wf {G : Ctx (IVal V₁) (IVal V₂)} {D : Ctx (JLabel L₁) (JLabel L₂)}
    {rs : List Ty} (bitsOnly : Bool) (tgt : ArmTarget) (next : Nat)
    {t₁ e₁ : Expr (IVal V₁) (JLabel L₁) rs} {t₂ e₂ : Expr (IVal V₂) (JLabel L₂) rs}
    (ht : Wf G D t₁ t₂) (he : Wf G D e₁ e₂) (hG : IKeyEq G)
    (hD : ∀ p ∈ D, match p.2.1, p.2.2 with
      | .loc d₁, .loc d₂ => d₁ = d₂
      | .tag id₁ _, .tag id₂ _ => id₁ = id₂
      | .outer _, .outer _ => True
      | _, _ => False) :
    checkStoreArms bitsOnly tgt next t₁ e₁ = checkStoreArms bitsOnly tgt next t₂ e₂ := by
  have htEq := checkStoreArm_eq_of_wf tgt true ht hG hD 12 2 ⟨next, [], []⟩ []
  have heEq : ∀ tbl, checkStoreArm tgt false 12 0 tbl [] e₁ =
      checkStoreArm tgt false 12 0 tbl [] e₂ :=
    fun tbl => checkStoreArm_eq_of_wf tgt false he hG hD 12 0 tbl []
  dsimp only [checkStoreArms, bind, Option.bind]
  simp only [htEq, heEq]

theorem checkDiamond_eq_of_wf {G : Ctx (IVal V₁) (IVal V₂)}
    {D : Ctx (JLabel L₁) (JLabel L₂)} {rs : List Ty}
    (bitsOnly : Bool) (jId : Nat) (jTs : List Ty)
    (hD : ∀ p ∈ D, match p.2.1, p.2.2 with
      | .loc d₁, .loc d₂ => d₁ = d₂
      | .tag id₁ _, .tag id₂ _ => id₁ = id₂
      | .outer _, .outer _ => True
      | _, _ => False) :
    ∀ (next : Nat) {e₁ : Expr (IVal V₁) (JLabel L₁) rs}
      {e₂ : Expr (IVal V₂) (JLabel L₂) rs},
    IKeyEq G → Wf G D e₁ e₂ →
    checkDiamondWith bitsOnly jId jTs next e₁ = checkDiamondWith bitsOnly jId jTs next e₂
  | next, _, _, hG, .let_ _ hk => by
    dsimp only [checkDiamondWith]
    exact congrArg (Option.map DiamondPlan.let_)
      (checkDiamond_eq_of_wf bitsOnly jId jTs hD (next + _)
        (hG.dummyIVals _ next) (hk (dummyIVals _ next) (dummyIVals _ next)))
  | next, _, _, hG, .load _ _ hk => by
    dsimp only [checkDiamondWith]
    exact congrArg (Option.map DiamondPlan.load)
      (checkDiamond_eq_of_wf bitsOnly jId jTs hD (next + 1)
        (hG.oneSame _ _ (.var next)) (hk (.imm default, .var next) (.imm default, .var next)))
  | next, _, _, hG, .store _ _ hk => by
    dsimp only [checkDiamondWith]
    exact congrArg (Option.map DiamondPlan.store)
      (checkDiamond_eq_of_wf bitsOnly jId jTs hD next hG hk)
  | next, _, _, hG, .call _ _ hk => by
    dsimp only [checkDiamondWith]
    exact congrArg (Option.map DiamondPlan.call)
      (checkDiamond_eq_of_wf bitsOnly jId jTs hD (next + _)
        (hG.dummyIVals _ next) (hk (dummyIVals _ next) (dummyIVals _ next)))
  | next, _, _, hG, .jnz _ ht he => by
    dsimp only [checkDiamondWith]
    rw [checkArm_eq_of_wf (.loc jId jTs) ht hD 2 4 next,
        checkArm_eq_of_wf (.loc jId jTs) he hD 2 4 next,
        checkStoreArms_eq_of_wf bitsOnly (.loc jId jTs) next ht he hG hD]
  | _, _, _, _, .jump _ _ | _, _, _, _, .ret _ | _, _, _, _, .exit _ _
  | _, _, _, _, .hlt | _, _, _, _, .group _ _ => rfl

theorem checkArm_peel {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (tgt : ArmTarget) {D : Ctx (JLabel L₁) L₂}
    (P : ArmPlan → Expr V₂ L₂ rs → Prop)
    (hlet : ∀ {rest ts} {op : Op V₂ ts} {k : Tup V₂ ts → Expr V₂ L₂ rs},
      isSafeOp op.code = true → (∀ xs, P rest (k xs)) → P (.let_ rest) (.let_ op k))
    (hjnz : ∀ {pT pE c} {t e : Expr V₂ L₂ rs},
      P pT t → P pE e → P (.jnz pT pE) (.jnz c t e))
    (hjump : ∀ {ts} {j₁ : JLabel L₁ ts} {j₂ : L₂ ts} {args : Tup (Arg V₂) ts},
      ⟨ts, j₁, j₂⟩ ∈ D →
      (match tgt, j₁ with
        | .loc jId jTs, .loc id => id = jId ∧ ts = jTs
        | .tag jId jTs, .tag id _ => id = jId ∧ ts = jTs
        | _, _ => False) →
      P .jump (.jump j₂ args))
    (hret : ∀ {vs : Tup (Arg V₂) rs}, tgt = .ret → P .ret (.ret vs)) :
    ∀ {G : Ctx (IVal V₁) V₂} {e₁ : Expr (IVal V₁) (JLabel L₁) rs} {e₂ : Expr V₂ L₂ rs},
    Wf G D e₁ e₂ →
    ∀ {jnzFuel letFuel next rem : Nat} {p : ArmPlan},
      checkArm tgt jnzFuel letFuel next e₁ = some (p, rem) → P p e₂ := by
  intro G e₁ e₂ hwf
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
    intro jnzFuel letFuel next rem p hc
    cases hop with | mk code _ =>
    unfold checkArm at hc
    cases hs : isSafeOp code <;> rw [hs] at hc
    · simp at hc
    · cases letFuel with
      | zero => simp at hc
      | succ letFuel' =>
        simp only [↓reduceIte, Option.map_eq_some_iff] at hc
        rcases hc with ⟨⟨q, rem'⟩, hq, heq⟩
        cases heq
        exact hlet hs fun xs₂ => ih (dummyIVals _ next) xs₂ hjump hq
  | @jump _ _ ts j₁ j₂ args₁ args₂ hj _ =>
    intro _ _ _ _ _ hc
    cases j₁ with
    | outer _ => cases tgt <;> simp [checkArm] at hc
    | loc id =>
      cases tgt with
      | tag _ _ | ret => simp [checkArm] at hc
      | loc jId jTs =>
        dsimp only [checkArm] at hc
        cases hcond : (id == jId && Ty.listBeq ts jTs) <;> rw [hcond] at hc
        · cases hc
        · simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, _⟩
          simp only [Bool.and_eq_true, beq_iff_eq, Ty.listBeq_iff_eq] at hcond
          exact hjump hj hcond
    | tag id _ =>
      cases tgt with
      | loc _ _ | ret => simp [checkArm] at hc
      | tag jId jTs =>
        dsimp only [checkArm] at hc
        cases hcond : (id == jId && Ty.listBeq ts jTs) <;> rw [hcond] at hc
        · cases hc
        · simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, _⟩
          simp only [Bool.and_eq_true, beq_iff_eq, Ty.listBeq_iff_eq] at hcond
          exact hjump hj hcond
  | ret _ =>
    intro _ _ _ _ _ hc
    cases tgt with
    | loc _ _ | tag _ _ => unfold checkArm at hc; cases hc
    | ret =>
      simp only [checkArm, Option.some.injEq, Prod.mk.injEq] at hc
      rcases hc with ⟨rfl, _⟩
      exact hret rfl
  | jnz _ _ _ iht ihe =>
    intro jnzFuel letFuel next rem p hc
    cases jnzFuel with
    | zero => unfold checkArm at hc; cases hc
    | succ jnzFuel' =>
      dsimp only [checkArm, bind, Option.bind] at hc
      rcases Option.bind_eq_some_iff.1 hc with ⟨⟨pT, rem1⟩, h1, hc2⟩
      rcases Option.bind_eq_some_iff.1 hc2 with ⟨⟨pE, rem2⟩, h2, hret'⟩
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at hret'
      rcases hret' with ⟨rfl, _⟩
      exact hjnz (iht hjump h1) (ihe hjump h2)
  | load _ _ _ | store _ _ _ | call _ _ _ | exit _ _ | hlt | group _ _ =>
    intro _ _ _ _ _ hc; unfold checkArm at hc; cases hc

theorem hasArmShape_of_checkArm {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {rs : List Ty} (tgt : ArmTarget)
    {G : Ctx (IVal V₁) V₂} {D : Ctx (JLabel L₁) L₂}
    {e₁ : Expr (IVal V₁) (JLabel L₁) rs} {e₂ : Expr V₂ L₂ rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ {jnzFuel letFuel next rem : Nat} {p : ArmPlan},
      checkArm tgt jnzFuel letFuel next e₁ = some (p, rem) →
      HasArmShape (tgt.sig rs) p e₂ :=
  checkArm_peel tgt (HasArmShape (tgt.sig rs))
    (fun _ h => h) (fun ht he => ⟨ht, he⟩)
    (fun {_ j₁ _ _} _ hcond => by cases tgt <;> cases j₁ <;> simp_all [ArmTarget.sig, HasArmShape])
    (fun h => by subst h; rfl)
    hwf

theorem checkStoreTail_peel {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (tgt : ArmTarget) {D : Ctx (JLabel L₁) L₂}
    (P : StoreTail → Expr V₂ L₂ rs → Prop)
    (hlet : ∀ {rest ts} {op : Op V₂ ts} {k : Tup V₂ ts → Expr V₂ L₂ rs},
      isSafeOp op.code = true → (∀ xs, P rest (k xs)) → P (.let_ rest) (.let_ op k))
    (hjump : ∀ {ts} {j₁ : JLabel L₁ ts} {j₂ : L₂ ts} {args : Tup (Arg V₂) ts},
      ⟨ts, j₁, j₂⟩ ∈ D →
      (match tgt, j₁ with
        | .loc jId jTs, .loc id => id = jId ∧ ts = jTs
        | .tag jId jTs, .tag id _ => id = jId ∧ ts = jTs
        | _, _ => False) →
      P .jump (.jump j₂ args))
    (hret : ∀ {vs : Tup (Arg V₂) rs}, tgt = .ret → P .ret (.ret vs)) :
    ∀ {G : Ctx (IVal V₁) V₂} {e₁ : Expr (IVal V₁) (JLabel L₁) rs} {e₂ : Expr V₂ L₂ rs},
    Wf G D e₁ e₂ →
    ∀ {letFuel : Nat} {p : StoreTail}, checkStoreTail tgt letFuel e₁ = some p → P p e₂ := by
  intro G e₁ e₂ hwf
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
    intro letFuel p hc
    cases hop with | mk code _ =>
    unfold checkStoreTail at hc
    cases hs : isSafeOp code <;> rw [hs] at hc
    · simp at hc
    · cases letFuel with
      | zero => simp at hc
      | succ letFuel' =>
        simp only [↓reduceIte, Option.map_eq_some_iff] at hc
        rcases hc with ⟨q, hq, rfl⟩
        exact hlet hs fun xs₂ => ih (dummyIVals _ 0) xs₂ hjump hq
  | @jump _ _ ts j₁ j₂ args₁ args₂ hj _ =>
    intro _ _ hc
    cases j₁ with
    | outer _ => cases tgt <;> simp [checkStoreTail] at hc
    | loc id =>
      cases tgt with
      | tag _ _ | ret => simp [checkStoreTail] at hc
      | loc jId jTs =>
        unfold checkStoreTail at hc; dsimp only at hc
        cases hcond : (id == jId && Ty.listBeq ts jTs) <;> rw [hcond] at hc
        · cases hc
        · simp only [↓reduceIte, Option.some.injEq] at hc
          subst hc
          simp only [Bool.and_eq_true, beq_iff_eq, Ty.listBeq_iff_eq] at hcond
          exact hjump hj hcond
    | tag id _ =>
      cases tgt with
      | loc _ _ | ret => simp [checkStoreTail] at hc
      | tag jId jTs =>
        unfold checkStoreTail at hc; dsimp only at hc
        cases hcond : (id == jId && Ty.listBeq ts jTs) <;> rw [hcond] at hc
        · cases hc
        · simp only [↓reduceIte, Option.some.injEq] at hc
          subst hc
          simp only [Bool.and_eq_true, beq_iff_eq, Ty.listBeq_iff_eq] at hcond
          exact hjump hj hcond
  | ret _ =>
    intro _ _ hc
    cases tgt <;> simp [checkStoreTail] at hc
    subst hc; exact hret rfl
  | jnz _ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | exit _ _ | hlt | group _ _ =>
    intro _ _ hc; simp [checkStoreTail] at hc

theorem hasStoreTailShape_of_checkStoreTail {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {rs : List Ty} (tgt : ArmTarget)
    {G : Ctx (IVal V₁) V₂} {D : Ctx (JLabel L₁) L₂}
    {e₁ : Expr (IVal V₁) (JLabel L₁) rs} {e₂ : Expr V₂ L₂ rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ {letFuel : Nat} {p : StoreTail},
      checkStoreTail tgt letFuel e₁ = some p → HasStoreTailShape (tgt.sig rs) p e₂ :=
  checkStoreTail_peel tgt (HasStoreTailShape (tgt.sig rs))
    (fun _ h => h)
    (fun {_ j₁ _ _} _ hcond => by
      cases tgt <;> cases j₁ <;> simp_all [ArmTarget.sig, HasStoreTailShape])
    (fun h => by subst h; rfl)
    hwf

theorem hasStoreStepShape_of_checkStoreArm {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {rs : List Ty} (tgt : ArmTarget) (allowNew : Bool) :
    ∀ {G : Ctx (IVal V₁) V₂} {D : Ctx (JLabel L₁) L₂}
      {e₁ : Expr (IVal V₁) (JLabel L₁) rs} {e₂ : Expr V₂ L₂ rs}
      {letFuel loadFuel : Nat} {tbl tbl' : SymTbl} {hits : List Nat} {ap : StoreArmPlan},
    Wf G D e₁ e₂ →
    checkStoreArm tgt allowNew letFuel loadFuel tbl hits e₁ = some (ap, tbl') →
    HasStoreStepShape (tgt.sig rs) ap.storeTy ap.step e₂ := by
  intro G D e₁ e₂ letFuel loadFuel tbl tbl' hits ap hwf hc
  induction hwf using Wf.induct generalizing letFuel loadFuel tbl tbl' hits ap with
  | let_ hop _ ih =>
    cases hop with | mk code _ =>
    unfold checkStoreArm at hc
    cases hs : isSafeOp code <;> rw [hs] at hc
    · simp at hc
    · cases letFuel with
      | zero => simp at hc
      | succ letFuel' =>
        simp only [↓reduceIte, Option.map_eq_some_iff] at hc
        rcases hc with ⟨⟨ap', tbl''⟩, hq, heq⟩
        cases heq
        exact fun xs₂ => ih (dummyKeyIVals _ _) xs₂ hq
  | load t _ _ ih =>
    unfold checkStoreArm at hc; dsimp only at hc
    cases hf : findSymLoad tbl.loads t (ikey _) with
    | some entry =>
      rw [hf] at hc
      simp only [Option.map_eq_some_iff] at hc
      rcases hc with ⟨⟨ap', tbl''⟩, hq, heq⟩
      cases heq
      exact fun v₂ => ih (.imm default, .var entry.vn) v₂ hq
    | none =>
      rw [hf] at hc
      cases allowNew
      · simp at hc
      · cases loadFuel with
        | zero => simp at hc
        | succ loadFuel' =>
          simp only [↓reduceIte, Option.map_eq_some_iff] at hc
          rcases hc with ⟨⟨ap', tbl''⟩, hq, heq⟩
          cases heq
          exact fun v₂ => ih (.imm default, .var tbl.vnNext) v₂ hq
  | store _ _ hk =>
    unfold checkStoreArm at hc
    simp only [Option.map_eq_some_iff] at hc
    rcases hc with ⟨tp, htp, heq⟩
    cases heq
    exact ⟨rfl, hasStoreTailShape_of_checkStoreTail tgt hk htp⟩
  | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt | group _ _ =>
    simp [checkStoreArm] at hc

theorem hasStoreStepShapes_of_checkStoreArms {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {rs : List Ty} (bitsOnly : Bool) (tgt : ArmTarget) (next : Nat)
    {G : Ctx (IVal V₁) V₂} {D : Ctx (JLabel L₁) L₂}
    {t₁ e₁ : Expr (IVal V₁) (JLabel L₁) rs} {t₂ e₂ : Expr V₂ L₂ rs} {sp : StoreDiamondPlan}
    (ht : Wf G D t₁ t₂) (he : Wf G D e₁ e₂)
    (hsp : checkStoreArms bitsOnly tgt next t₁ e₁ = some sp) :
    HasStoreStepShape (tgt.sig rs) sp.storeTy sp.armT t₂ ∧
    HasStoreStepShape (tgt.sig rs) sp.storeTy sp.armE e₂ := by
  dsimp only [checkStoreArms, bind, Option.bind] at hsp
  cases h1 : checkStoreArm tgt true 12 2 ⟨next, [], []⟩ [] t₁ with
  | none => rw [h1] at hsp; simp at hsp
  | some r1 =>
    rw [h1] at hsp; dsimp only at hsp
    cases hsel : isSelectTyWith bitsOnly r1.1.storeTy with
    | false => rw [hsel] at hsp; simp [guard] at hsp
    | true =>
      rw [hsel] at hsp; simp only [guard, ↓reduceIte, Option.pure_def] at hsp
      cases h2 : checkStoreArm tgt false 12 0 r1.2 [] e₁ with
      | none => rw [h2] at hsp; simp at hsp
      | some r2 =>
        rw [h2] at hsp; dsimp only at hsp
        cases hty : tyDecEq r1.1.storeTy r2.1.storeTy with
        | isFalse _ => rw [hty] at hsp; simp at hsp
        | isTrue heq =>
          rw [hty] at hsp; dsimp only at hsp
          cases hfk : fKeyBeq r1.1.storeAddr r2.1.storeAddr with
          | false => rw [hfk] at hsp; simp at hsp
          | true =>
            rw [hfk] at hsp; simp only [↓reduceIte] at hsp
            cases hhit : (List.range r1.2.loads.length).all fun s => r2.1.hitSlots.contains s with
            | false => rw [hhit] at hsp; simp at hsp
            | true =>
              rw [hhit] at hsp; simp only [↓reduceIte, Option.some.injEq] at hsp
              subst hsp
              refine ⟨hasStoreStepShape_of_checkStoreArm tgt true ht h1, ?_⟩
              have hshE := hasStoreStepShape_of_checkStoreArm tgt false he h2
              rw [heq]; exact hshE

theorem checkDiamond_peel_of_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {rs : List Ty} (bitsOnly : Bool) (jId : Nat) (jTs : List Ty)
    {D : Ctx (JLabel L₁) L₂}
    (P : Nat → Ctx (IVal V₁) V₂ → DiamondPlan → Expr V₂ L₂ rs → Prop)
    (hlet : ∀ {next G rest ts op k},
      (∀ xs, P (next + ts.length) (Tup.zip (dummyIVals ts next) xs ++ G) rest (k xs)) →
      P next G (.let_ rest) (.let_ (ts := ts) op k))
    (hload : ∀ {next G rest t a k},
      (∀ v, P (next + 1) (⟨t, (.imm default, .var next), v⟩ :: G) rest (k v)) →
      P next G (.load rest) (.load t a k))
    (hstore : ∀ {next G rest t v a k}, P next G rest k →
      P next G (.store rest) (.store (t := t) v a k))
    (hcall : ∀ {next G rest f as bs args k},
      (∀ xs, P (next + bs.length) (Tup.zip (dummyIVals bs next) xs ++ G) rest (k xs)) →
      P next G (.call rest) (.call f (as := as) (bs := bs) args k))
    (hjnz : ∀ {pT pE c next G} {t₁ e₁ : Expr (IVal V₁) (JLabel L₁) rs}
      {t₂ e₂ : Expr V₂ L₂ rs},
      Wf G D t₁ t₂ → Wf G D e₁ e₂ →
      isSelectSigWith bitsOnly jTs = true →
      (∃ remT remE, checkArm (.loc jId jTs) 2 4 next t₁ = some (pT, remT) ∧
        checkArm (.loc jId jTs) 2 4 next e₁ = some (pE, remE)) →
      P next G (.jnz pT pE) (.jnz c t₂ e₂))
    (hjnzStore : ∀ {sp c next G} {t₁ e₁ : Expr (IVal V₁) (JLabel L₁) rs}
      {t₂ e₂ : Expr V₂ L₂ rs},
      Wf G D t₁ t₂ → Wf G D e₁ e₂ →
      isSelectSigWith bitsOnly jTs = true →
      checkStoreArms bitsOnly (.loc jId jTs) next t₁ e₁ = some sp →
      P next G (.jnzStore sp) (.jnz c t₂ e₂)) :
    ∀ (next : Nat) (plan : DiamondPlan) {G : Ctx (IVal V₁) V₂}
      {e₁ : Expr (IVal V₁) (JLabel L₁) rs} {e₂ : Expr V₂ L₂ rs},
    Wf G D e₁ e₂ → checkDiamondWith bitsOnly jId jTs next e₁ = some plan → P next G plan e₂
  | next, _, _, _, _, .let_ _ hk, hc => by
    dsimp only [checkDiamondWith] at hc; simp only [Option.map_eq_some_iff] at hc
    rcases hc with ⟨rest, hr, rfl⟩
    exact hlet fun xs₂ =>
      checkDiamond_peel_of_wf bitsOnly jId jTs P hlet hload hstore hcall hjnz hjnzStore
        (next + _) rest (hk (dummyIVals _ next) xs₂) hr
  | next, _, _, _, _, .load _ _ hk, hc => by
    dsimp only [checkDiamondWith] at hc; simp only [Option.map_eq_some_iff] at hc
    rcases hc with ⟨rest, hr, rfl⟩
    exact hload fun v₂ =>
      checkDiamond_peel_of_wf bitsOnly jId jTs P hlet hload hstore hcall hjnz hjnzStore
        (next + 1) rest (hk (.imm default, .var next) v₂) hr
  | next, _, _, _, _, .store _ _ hk, hc => by
    dsimp only [checkDiamondWith] at hc; simp only [Option.map_eq_some_iff] at hc
    rcases hc with ⟨rest, hr, rfl⟩
    exact hstore
      (checkDiamond_peel_of_wf bitsOnly jId jTs P hlet hload hstore hcall hjnz hjnzStore
        next rest hk hr)
  | next, _, _, _, _, .call _ _ hk, hc => by
    dsimp only [checkDiamondWith] at hc; simp only [Option.map_eq_some_iff] at hc
    rcases hc with ⟨rest, hr, rfl⟩
    exact hcall fun xs₂ =>
      checkDiamond_peel_of_wf bitsOnly jId jTs P hlet hload hstore hcall hjnz hjnzStore
        (next + _) rest (hk (dummyIVals _ next) xs₂) hr
  | next, _, _, .jnz _ t₁ e₁, _, .jnz _ ht he, hc => by
    dsimp only [checkDiamondWith] at hc
    cases hsel : isSelectSigWith bitsOnly jTs <;> rw [hsel] at hc
    · simp at hc
    · simp only [↓reduceIte] at hc
      cases h1 : checkArm (.loc jId jTs) 2 4 next t₁ with
      | none =>
        rw [h1] at hc; dsimp only at hc
        simp only [Option.map_eq_some_iff] at hc
        rcases hc with ⟨sp, hsp, rfl⟩
        exact hjnzStore ht he hsel hsp
      | some resT =>
        cases h2 : checkArm (.loc jId jTs) 2 4 next e₁ with
        | none =>
          rw [h1, h2] at hc; dsimp only at hc
          simp only [Option.map_eq_some_iff] at hc
          rcases hc with ⟨sp, hsp, rfl⟩
          exact hjnzStore ht he hsel hsp
        | some resE =>
          rw [h1, h2] at hc; dsimp only at hc
          cases hc
          exact hjnz ht he hsel ⟨resT.2, resE.2, h1, h2⟩
  | _, _, _, _, _, .jump _ _, hc | _, _, _, _, _, .ret _, hc
  | _, _, _, _, _, .exit _ _, hc | _, _, _, _, _, .hlt, hc
  | _, _, _, _, _, .group _ _, hc => by
    dsimp only [checkDiamondWith] at hc; cases hc

theorem hasDiamondShape_of_checkDiamond {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {rs : List Ty} (bitsOnly : Bool) (jId : Nat) (jTs : List Ty)
    (next : Nat) (plan : DiamondPlan) {G : Ctx (IVal V₁) V₂}
    {D : Ctx (JLabel L₁) L₂}
    {e₁ : Expr (IVal V₁) (JLabel L₁) rs} {e₂ : Expr V₂ L₂ rs}
    (hwf : Wf G D e₁ e₂) (hc : checkDiamondWith bitsOnly jId jTs next e₁ = some plan) :
    HasDiamondShape jTs plan e₂ :=
  checkDiamond_peel_of_wf bitsOnly jId jTs (fun _ _ => HasDiamondShape jTs)
    (fun h => h) (fun h => h) (fun h => h) (fun h => h)
    (fun ht he _ ⟨_, _, h1, h2⟩ =>
      ⟨hasArmShape_of_checkArm (.loc jId jTs) ht h1,
       hasArmShape_of_checkArm (.loc jId jTs) he h2⟩)
    (fun ht he _ hsp => hasStoreStepShapes_of_checkStoreArms bitsOnly (.loc jId jTs) _ ht he hsp)
    next plan hwf hc

private theorem hasArmShape_of_rhs {rs : List Ty} (jTs : List Ty) :
    ∀ (p : ArmPlan) {G : Ctx (IVal V₁) (IVal V₂)} {D : Ctx (JLabel L₁) (JLabel L₂)}
      {e₁ : Expr (IVal V₁) (JLabel L₁) rs} {e₂ : Expr (IVal V₂) (JLabel L₂) rs},
    Wf G D e₁ e₂ → HasArmShape jTs p e₂ → HasArmShape jTs p e₁
  | .jump, _, _, _, e₂, hwf, h => by
    cases e₂ <;> first | exact False.elim h | (rcases hwf.rhs_jump with ⟨_, _, rfl, _, _⟩; exact h)
  | .ret, _, _, _, e₂, hwf, h => by
    cases e₂ <;> first | exact False.elim h | (rcases hwf.rhs_ret with ⟨_, rfl, _⟩; exact h)
  | .let_ rest, _, _, _, e₂, hwf, h => by
    cases e₂ <;> first | exact False.elim h |
      (rcases hwf.rhs_let with ⟨_, _, rfl, _, hk⟩;
       exact fun xs₁ => hasArmShape_of_rhs jTs rest (hk xs₁ (dummyIVals _ 0)) (h (dummyIVals _ 0)))
  | .jnz pT pE, _, _, _, e₂, hwf, h => by
    cases e₂ <;> first | exact False.elim h |
      (rcases hwf.rhs_jnz with ⟨_, _, _, rfl, _, ht, he⟩;
       exact ⟨hasArmShape_of_rhs jTs pT ht h.1, hasArmShape_of_rhs jTs pE he h.2⟩)

private theorem hasStoreTailShape_of_rhs {rs : List Ty} (jTs : List Ty) :
    ∀ (p : StoreTail) {G : Ctx (IVal V₁) (IVal V₂)} {D : Ctx (JLabel L₁) (JLabel L₂)}
      {e₁ : Expr (IVal V₁) (JLabel L₁) rs} {e₂ : Expr (IVal V₂) (JLabel L₂) rs},
    Wf G D e₁ e₂ → HasStoreTailShape jTs p e₂ → HasStoreTailShape jTs p e₁
  | .jump, _, _, _, e₂, hwf, h => by
    cases e₂ <;> first | exact False.elim h | (rcases hwf.rhs_jump with ⟨_, _, rfl, _, _⟩; exact h)
  | .ret, _, _, _, e₂, hwf, h => by
    cases e₂ <;> first | exact False.elim h | (rcases hwf.rhs_ret with ⟨_, rfl, _⟩; exact h)
  | .let_ rest, _, _, _, e₂, hwf, h => by
    cases e₂ <;> first | exact False.elim h |
      (rcases hwf.rhs_let with ⟨_, _, rfl, _, hk⟩;
       exact fun xs₁ =>
         hasStoreTailShape_of_rhs jTs rest (hk xs₁ (dummyIVals _ 0)) (h (dummyIVals _ 0)))

theorem hasStoreStepShape_of_rhs {rs : List Ty} (jTs : List Ty) (st : Ty) :
    ∀ (p : StoreStep) {G : Ctx (IVal V₁) (IVal V₂)} {D : Ctx (JLabel L₁) (JLabel L₂)}
      {e₁ : Expr (IVal V₁) (JLabel L₁) rs} {e₂ : Expr (IVal V₂) (JLabel L₂) rs},
    Wf G D e₁ e₂ → HasStoreStepShape jTs st p e₂ → HasStoreStepShape jTs st p e₁
  | .let_ rest, _, _, _, e₂, hwf, h => by
    cases e₂ <;> first | exact False.elim h |
      (rcases hwf.rhs_let with ⟨_, _, rfl, _, hk⟩;
       exact fun xs₁ =>
         hasStoreStepShape_of_rhs jTs st rest (hk xs₁ (dummyIVals _ 0)) (h (dummyIVals _ 0)))
  | .loadEmit rest, _, _, _, e₂, hwf, h
  | .loadReuse _ rest, _, _, _, e₂, hwf, h => by
    cases e₂ <;> first | exact False.elim h |
      (rcases hwf.rhs_load with ⟨_, _, rfl, _, hk⟩;
       exact fun v₁ =>
         hasStoreStepShape_of_rhs jTs st rest
           (hk v₁ (.imm default, .var 0)) (h (.imm default, .var 0)))
  | .store tail, _, _, _, e₂, hwf, h => by
    cases e₂ <;> first | exact False.elim h |
      (rcases hwf.rhs_store with ⟨_, _, _, rfl, _, _, hk⟩;
       exact ⟨h.1, hasStoreTailShape_of_rhs jTs tail hk h.2⟩)

theorem hasDiamondShape_of_rhs {rs : List Ty} (jTs : List Ty) :
    ∀ (plan : DiamondPlan) {G : Ctx (IVal V₁) (IVal V₂)} {D : Ctx (JLabel L₁) (JLabel L₂)}
      {e₁ : Expr (IVal V₁) (JLabel L₁) rs} {e₂ : Expr (IVal V₂) (JLabel L₂) rs},
    Wf G D e₁ e₂ → HasDiamondShape jTs plan e₂ → HasDiamondShape jTs plan e₁
  | .jnz pT pE, _, _, _, e₂, hwf, h => by
    cases e₂ <;> first | exact False.elim h |
      (rcases hwf.rhs_jnz with ⟨_, _, _, rfl, _, ht, he⟩;
       exact ⟨hasArmShape_of_rhs jTs pT ht h.1, hasArmShape_of_rhs jTs pE he h.2⟩)
  | .jnzStore sp, _, _, _, e₂, hwf, h => by
    cases e₂ <;> first | exact False.elim h |
      (rcases hwf.rhs_jnz with ⟨_, _, _, rfl, _, ht, he⟩;
       exact ⟨hasStoreStepShape_of_rhs jTs sp.storeTy sp.armT ht h.1,
              hasStoreStepShape_of_rhs jTs sp.storeTy sp.armE he h.2⟩)
  | .let_ rest, _, _, _, e₂, hwf, h => by
    cases e₂ <;> first | exact False.elim h |
      (rcases hwf.rhs_let with ⟨_, _, rfl, _, hk⟩;
       exact fun xs₁ =>
         hasDiamondShape_of_rhs jTs rest (hk xs₁ (dummyIVals _ 0)) (h (dummyIVals _ 0)))
  | .load rest, _, _, _, e₂, hwf, h => by
    cases e₂ <;> first | exact False.elim h |
      (rcases hwf.rhs_load with ⟨_, _, rfl, _, hk⟩;
       exact fun v₁ =>
         hasDiamondShape_of_rhs jTs rest (hk v₁ (.imm default, .var 0)) (h (.imm default, .var 0)))
  | .store rest, _, _, _, e₂, hwf, h => by
    cases e₂ <;> first | exact False.elim h |
      (rcases hwf.rhs_store with ⟨_, _, _, rfl, _, _, hk⟩;
       exact hasDiamondShape_of_rhs jTs rest hk h)
  | .call rest, _, _, _, e₂, hwf, h => by
    cases e₂ <;> first | exact False.elim h |
      (rcases hwf.rhs_call with ⟨_, _, rfl, _, hk⟩;
       exact fun xs₁ =>
         hasDiamondShape_of_rhs jTs rest (hk xs₁ (dummyIVals _ 0)) (h (dummyIVals _ 0)))


end WfSelect

end IfOptImpl

end LeanQbe.T
