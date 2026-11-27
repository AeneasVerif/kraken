module

public import LeanQbe.T.LeanLCNF.Sem.LowerSound0Bridge
import LeanQbe.T.OpsLemmas
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.MemLemmas

/-!
# `LM` Builder & `LExpr.wp` Simulation Combinators (`LowerSound1`)

Reusable weakest-precondition combinators and fresh-counter monotonicity lemmas for the `LM`
monad builders in `LeanQbe.T.LeanLCNF.Lower` and `Lower1`:
- Core step helpers (`wp_let`, `wp_load`, `wp_store`, `wp_call`, `wp_jnz`, `wp_jump`, `wp_ret`,
  `wp_exit`, `evalArgs_*`, `tupOfBV64s`)
- `VEnvAgreeBelow` and `JEnvAgreeBelow` preservation
- `op1_wp`, `op2_wp`, `add64_wp`..`cmpOp_wp`, `addrOf_wp`, `lm_loadAt_wp`, `storeAt_wp`
- `callN_wp`, `call1_wp`, `call0_wp`, `withJoin_wp`, `withJoin1_wp`
- `convW_wp`, `boxSmall_wp`, `boolToU8_wp`, `isScalarObj_wp`, `rtCall1_wp`, `callFn_reg_wp`
- `LMMono` monotonicity lemmas for all `LM` builders
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF
open LeanQbe.T.Frontend.C0

/-! ## 1. `LM` Monad & `LExpr.wp` Step Helpers -/

theorem lm_pure_run {α : Type} (a : α) (n : Nat) :
    (pure a : LM α).run n = .ok (a, n) := rfl

theorem lm_bind_run {α β : Type} (m : LM α) (f : α → LM β) (n : Nat) {r : β × Nat} :
    (m >>= f).run n = .ok r ↔ ∃ a n1, m.run n = .ok (a, n1) ∧ (f a).run n1 = .ok r := by
  show (Except.bind (m.run n) (fun x => (f x.1).run x.2) = .ok r) ↔ _
  cases hm : m.run n with
  | error e => simp [Except.bind]
  | ok p =>
    rcases p with ⟨a, n1⟩
    simp only [Except.bind, Except.ok.injEq, Prod.mk.injEq]
    constructor
    · intro h; exact ⟨a, n1, ⟨rfl, rfl⟩, h⟩
    · rintro ⟨a', n1', ⟨rfl, rfl⟩, h2⟩; exact h2

theorem wp_let {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {op : LOp} {bs : List Frontend.C0.LVar} {k : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {m : Mem 64}
    (hbs : bs.map (·.ty) = op.rs) {xs : Tup Val op.sig}
    (hev : evalArgs ρ op.sig op.args = some xs)
    (hwp : op.code.wp xs fun r => LExpr.wp Γ Q X k (ρ.bind bs op.rs r) J m) :
    LExpr.wp Γ Q X (.let_ op bs k) ρ J m :=
  ⟨hbs, xs, hev, hwp⟩

theorem wp_load {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {t : Ty} {a : LArg} {b : Frontend.C0.LVar} {k : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {m : Mem 64}
    (ht : b.ty = t) {p : BitVec 64} (hp : LArg.eval ρ i64 a = some p)
    {v : Val t} (hv : loadVal m t p = some v)
    (hk : LExpr.wp Γ Q X k (ρ.set b.id t v) J m) :
    LExpr.wp Γ Q X (.load t a b k) ρ J m :=
  ⟨ht, p, hp, v, hv, hk⟩

theorem wp_store {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {t : Ty} {v a : LArg} {k : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {m : Mem 64}
    {val : Val t} {p : BitVec 64}
    (hv : LArg.eval ρ t v = some val) (hp : LArg.eval ρ i64 a = some p)
    (hok : storeOk m t p) (hk : LExpr.wp Γ Q X k ρ J (storeMem m t p val)) :
    LExpr.wp Γ Q X (.store t v a k) ρ J m :=
  ⟨val, p, hv, hp, hok, hk⟩

theorem wp_call {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {f : Sym} {as bs : List Ty} {args : List LArg} {binders : List Frontend.C0.LVar} {k : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {m : Mem 64}
    (hbs : binders.map (·.ty) = bs) {xs : Tup Val as} (hev : evalArgs ρ as args = some xs)
    {P : Post bs} {E : XPost} (hcall : Γ f as bs xs m P E)
    (hP : ∀ r m', P r m' → LExpr.wp Γ Q X k (ρ.bind binders bs r) J m')
    (hE : ∀ g cs ys m', E g cs ys m' → X g cs ys m') :
    LExpr.wp Γ Q X (.call f as bs args binders k) ρ J m :=
  ⟨hbs, xs, hev, P, E, hcall, hP, hE⟩

theorem wp_jnz {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : LArg} {t e : LExpr} {ρ : Frontend.C0.VEnv} {J : JEnv} {m : Mem 64}
    {b : Bool} (hb : LArg.eval ρ .bool c = some b)
    (ht : b = true → LExpr.wp Γ Q X t ρ J m)
    (hf : b = false → LExpr.wp Γ Q X e ρ J m) :
    LExpr.wp Γ Q X (.jnz c t e) ρ J m :=
  ⟨b, hb, ht, hf⟩

theorem wp_jump {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {lid : Nat} {ts : List Ty} {args : List LArg}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {m : Mem 64}
    {k : Cont ts} {xs : Tup Val ts}
    (hj : J.get lid ts = some k) (hev : evalArgs ρ ts args = some xs) (hk : k xs m) :
    LExpr.wp Γ Q X (.jump lid ts args) ρ J m :=
  ⟨k, xs, hj, hev, hk⟩

theorem wp_ret {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {args : List LArg} {ρ : Frontend.C0.VEnv} {J : JEnv} {m : Mem 64}
    {xs : Tup Val rs} (hev : evalArgs ρ rs args = some xs) (hq : Q xs m) :
    LExpr.wp Γ Q X (.ret rs args) ρ J m :=
  ⟨rfl, xs, hev, hq⟩

theorem wp_exit {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {f : Sym} {as : List Ty} {args : List LArg}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {m : Mem 64}
    {xs : Tup Val as} (hev : evalArgs ρ as args = some xs) (hx : X f as xs m) :
    LExpr.wp Γ Q X (.exit f as args) ρ J m :=
  ⟨xs, hev, hx⟩

theorem evalArgs_nil (ρ : Frontend.C0.VEnv) : evalArgs ρ [] [] = some () := rfl

theorem evalArgs_cons {ρ : Frontend.C0.VEnv} {t : Ty} {ts : List Ty} {a : LArg} {as : List LArg}
    {v : Val t} {vs : Tup Val ts}
    (ha : LArg.eval ρ t a = some v) (has : evalArgs ρ ts as = some vs) :
    evalArgs ρ (t :: ts) (a :: as) = some (v, vs) := by
  rw [evalArgs.eq_2, ha, has]

/-- Canonical `Tup Val` for a list of 64-bit words. -/
@[expose] def tupOfBV64s : (vs : List (BitVec 64)) → Tup Val (List.replicate vs.length i64)
  | [] => ()
  | v :: vs => (v, tupOfBV64s vs)

theorem wordsOfTup_tupOfBV64s :
    ∀ vs : List (BitVec 64), wordsOfTup (tupOfBV64s vs) = vs.map Word.i64
  | [] => wordsOfTup.eq_1
  | v :: vs => by
    dsimp only [tupOfBV64s]
    refine (wordsOfTup.eq_2 i64 (List.replicate vs.length i64) v (tupOfBV64s vs)).trans ?_
    rw [List.map_cons, Word.i64.eq_1, wordsOfTup_tupOfBV64s vs]

private theorem wordsOfTup_inj_i64 :
    ∀ (k : Nat) (t1 t2 : Tup Val (List.replicate k i64)),
      wordsOfTup t1 = wordsOfTup t2 → t1 = t2
  | 0, (), (), _ => rfl
  | k + 1, (a1, r1), (a2, r2), h => by
    rw [wordsOfTup.eq_2, wordsOfTup.eq_2] at h
    simp only [List.cons.injEq, Sigma.mk.injEq, heq_eq_eq, true_and] at h
    rcases h with ⟨rfl, hr⟩
    rw [wordsOfTup_inj_i64 k r1 r2 hr]

theorem evalArgs_replicate_i64 (ρ : Frontend.C0.VEnv) :
    ∀ (args : List LArg) (vs : List (BitVec 64)),
      args.length = vs.length →
      (∀ p ∈ args.zip vs, LArg.eval ρ i64 p.1 = some p.2) →
      ∃ tup : Tup Val (List.replicate args.length i64),
        evalArgs ρ (List.replicate args.length i64) args = some tup ∧
        wordsOfTup tup = vs.map Word.i64
  | [], [], _, _ => ⟨(), rfl, wordsOfTup.eq_1⟩
  | _ :: _, [], hlen, _ => by simp at hlen
  | [], _ :: _, hlen, _ => by simp at hlen
  | a :: as, v :: vs, hlen, hp => by
    have ha : LArg.eval ρ i64 a = some v := hp (a, v) List.mem_cons_self
    have hps : ∀ p ∈ as.zip vs, LArg.eval ρ i64 p.1 = some p.2 :=
      fun p hmem => hp p (List.mem_cons_of_mem _ hmem)
    obtain ⟨tup, hev, hwd⟩ := evalArgs_replicate_i64 ρ as vs (Nat.succ.inj hlen) hps
    refine ⟨(v, tup), evalArgs_cons ha hev, ?_⟩
    refine (wordsOfTup.eq_2 i64 (List.replicate as.length i64) v tup).trans ?_
    rw [List.map_cons, Word.i64.eq_1, hwd]

/-! ## 2. `VEnv` and `JEnv` Agreement Below a Fresh Bound -/

/-- Two `Frontend.C0.VEnv`s agree on all `LArg`s whose variable IDs are `< n`. -/
@[expose] def VEnvAgreeBelow (n : Nat) (ρ' ρ : Frontend.C0.VEnv) : Prop :=
  ∀ a u, argIdsBelow a n → LArg.eval ρ' u a = LArg.eval ρ u a

theorem VEnvAgreeBelow.refl (n : Nat) (ρ : Frontend.C0.VEnv) : VEnvAgreeBelow n ρ ρ :=
  fun _ _ _ => rfl

theorem VEnvAgreeBelow.mono {m n : Nat} {ρ' ρ : Frontend.C0.VEnv}
    (hle : m ≤ n) (h : VEnvAgreeBelow n ρ' ρ) : VEnvAgreeBelow m ρ' ρ :=
  fun a u ha => h a u (argIdsBelow_mono hle ha)

theorem VEnvAgreeBelow.trans {n : Nat} {ρ'' ρ' ρ : Frontend.C0.VEnv}
    (h1 : VEnvAgreeBelow n ρ'' ρ') (h2 : VEnvAgreeBelow n ρ' ρ) : VEnvAgreeBelow n ρ'' ρ :=
  fun a u ha => (h1 a u ha).trans (h2 a u ha)

theorem VEnvAgreeBelow.set {n : Nat} {ρ : Frontend.C0.VEnv} {id : Nat} (hid : n ≤ id)
    (t : Ty) (v : Val t) : VEnvAgreeBelow n (ρ.set id t v) ρ :=
  fun _ _ ha => LArg.eval_set_of_ltBound ha hid

theorem VEnvAgreeBelow.eval {n : Nat} {ρ' ρ : Frontend.C0.VEnv}
    (h : VEnvAgreeBelow n ρ' ρ) {a : LArg} {u : Ty} (ha : argIdsBelow a n) :
    LArg.eval ρ' u a = LArg.eval ρ u a :=
  h a u ha

theorem VEnvAgreeBelow.evalArgs {n : Nat} {ρ' ρ : Frontend.C0.VEnv}
    (h : VEnvAgreeBelow n ρ' ρ) :
    ∀ {ts : List Ty} {as : List LArg},
      (∀ a ∈ as, argIdsBelow a n) → evalArgs ρ' ts as = evalArgs ρ ts as
  | [], [], _ => rfl
  | [], _ :: _, _ => by simp only [evalArgs.eq_3]
  | _ :: _, [], _ => by simp only [evalArgs.eq_3]
  | _ :: ts, a :: as, has => by
    rw [evalArgs.eq_2, evalArgs.eq_2, h.eval (has a List.mem_cons_self),
      h.evalArgs (fun a' ha' => has a' (List.mem_cons_of_mem _ ha'))]

/-- Two `JEnv`s agree on all join-point labels `< n`. -/
@[expose] def JEnvAgreeBelow (n : Nat) (J' J : JEnv) : Prop :=
  ∀ lbl ts, lbl < n → J'.get lbl ts = J.get lbl ts

theorem JEnvAgreeBelow.refl (n : Nat) (J : JEnv) : JEnvAgreeBelow n J J :=
  fun _ _ _ => rfl

theorem JEnvAgreeBelow.mono {m n : Nat} {J' J : JEnv}
    (hle : m ≤ n) (h : JEnvAgreeBelow n J' J) : JEnvAgreeBelow m J' J :=
  fun lbl ts hlt => h lbl ts (Nat.lt_of_lt_of_le hlt hle)

theorem JEnvAgreeBelow.trans {n : Nat} {J'' J' J : JEnv}
    (h1 : JEnvAgreeBelow n J'' J') (h2 : JEnvAgreeBelow n J' J) : JEnvAgreeBelow n J'' J :=
  fun lbl ts hlt => (h1 lbl ts hlt).trans (h2 lbl ts hlt)

theorem JEnvAgreeBelow.set {n : Nat} (J : JEnv) {lbl : Nat} (hlbl : n ≤ lbl)
    (ts : List Ty) (k : Cont ts) : JEnvAgreeBelow n (J.set lbl ts k) J :=
  fun _ us hl => JEnv.get_set_of_lt J hl hlbl ts us k

/-- Monotonicity predicate for `LM` fresh-counter state. -/
@[expose] def LMMono {α : Type} (m : LM α) : Prop :=
  ∀ n a n', m.run n = .ok (a, n') → n ≤ n'

/-! ## 3. Core `LM` Builder WP Combinators -/

theorem op1_wp {Γ : Env} {rs_ret : List Ty} {QT : Post rs_ret} {XT : XPost}
    {t : Ty} {sig : List Ty} {code : OpCode sig [t]} {args : List LArg}
    {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {vs : Tup Val sig}
    (hrun : (LeanLCNF.op1 t code args k).run n = .ok (e, n'))
    (hev : evalArgs ρ sig args = some vs)
    (hwp : ∀ (ek : LExpr),
      (k (vArg { id := n, name := "", ty := t })).run (n + 1) = .ok (ek, n') →
      argIdsBelow (vArg { id := n, name := "", ty := t }) (n + 1) →
      code.wp vs fun (res, ()) =>
        LExpr.wp Γ QT XT ek (ρ.set n t res) J mem) :
    LExpr.wp Γ QT XT e ρ J mem := by
  unfold LeanLCNF.op1 at hrun
  rw [lm_bind_run] at hrun
  rcases hrun with ⟨v, n1, hv, hrest⟩
  rw [freshVar_run] at hv
  injection hv with hvp
  have hv_eq : v = { id := n, name := "", ty := t } := (congrArg Prod.fst hvp).symm
  have hn1 : n1 = n + 1 := (congrArg Prod.snd hvp).symm
  subst hv_eq; subst hn1
  rw [lm_bind_run] at hrest
  rcases hrest with ⟨ek, n2, hek, hpure⟩
  rw [lm_pure_run] at hpure
  injection hpure with hpr
  have he : LExpr.let_ { rs := [t], sig := sig, code := code, args := args }
      [{ id := n, name := "", ty := t }] ek = e := congrArg Prod.fst hpr
  have hn2 : n2 = n' := congrArg Prod.snd hpr
  subst he; subst hn2
  have hcode := hwp ek hek (Nat.lt_succ_self n)
  refine wp_let rfl hev (OpCode.wp_mono code vs (fun ⟨res, u⟩ hres => ?_) hcode)
  cases u
  simpa [Frontend.C0.VEnv.bind, Frontend.C0.VEnv.set] using hres

theorem op2_wp {Γ : Env} {rs_ret : List Ty} {QT : Post rs_ret} {XT : XPost}
    {t u : Ty} {sig : List Ty} {code : OpCode sig [t, u]} {args : List LArg}
    {k : LArg → LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {vs : Tup Val sig}
    (hrun : (LeanLCNF.op2 t u code args k).run n = .ok (e, n'))
    (hev : evalArgs ρ sig args = some vs)
    (hwp : ∀ (ek : LExpr),
      (k (vArg { id := n, name := "", ty := t })
          (vArg { id := n + 1, name := "", ty := u })).run (n + 2) = .ok (ek, n') →
      argIdsBelow (vArg { id := n, name := "", ty := t }) (n + 2) →
      argIdsBelow (vArg { id := n + 1, name := "", ty := u }) (n + 2) →
      code.wp vs fun (r1, r2, ()) =>
        LExpr.wp Γ QT XT ek ((ρ.set n t r1).set (n + 1) u r2) J mem) :
    LExpr.wp Γ QT XT e ρ J mem := by
  unfold LeanLCNF.op2 at hrun
  rw [lm_bind_run] at hrun
  rcases hrun with ⟨v1, n1, hv1, hrest1⟩
  rw [freshVar_run] at hv1
  injection hv1 with hv1p
  have hv1_eq : v1 = { id := n, name := "", ty := t } := (congrArg Prod.fst hv1p).symm
  have hn1 : n1 = n + 1 := (congrArg Prod.snd hv1p).symm
  subst hv1_eq; subst hn1
  rw [lm_bind_run] at hrest1
  rcases hrest1 with ⟨v2, n2, hv2, hrest2⟩
  rw [freshVar_run] at hv2
  injection hv2 with hv2p
  have hv2_eq : v2 = { id := n + 1, name := "", ty := u } := (congrArg Prod.fst hv2p).symm
  have hn2 : n2 = n + 2 := (congrArg Prod.snd hv2p).symm
  subst hv2_eq; subst hn2
  rw [lm_bind_run] at hrest2
  rcases hrest2 with ⟨ek, n3, hek, hpure⟩
  rw [lm_pure_run] at hpure
  injection hpure with hpr
  have he : LExpr.let_ { rs := [t, u], sig := sig, code := code, args := args }
      [{ id := n, name := "", ty := t }, { id := n + 1, name := "", ty := u }] ek = e :=
    congrArg Prod.fst hpr
  have hn3 : n3 = n' := congrArg Prod.snd hpr
  subst he; subst hn3
  have hcode := hwp ek hek (by show n < n + 2; omega) (by show n + 1 < n + 2; omega)
  refine wp_let rfl hev (OpCode.wp_mono code vs (fun ⟨r1, r2, w⟩ hres => ?_) hcode)
  cases w
  simpa [Frontend.C0.VEnv.bind, Frontend.C0.VEnv.set] using hres

theorem add64_wp {Γ : Env} {rs : List Ty} {QT : Post rs} {XT : XPost}
    {a b : LArg} {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {va vb : BitVec 64}
    (hrun : (add64 a b k).run n = .ok (e, n'))
    (ha : LArg.eval ρ i64 a = some va) (hb : LArg.eval ρ i64 b = some vb)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv),
      (k r).run (n + 1) = .ok (ek, n') → argIdsBelow r (n + 1) → VEnvAgreeBelow n ρ' ρ →
      LArg.eval ρ' i64 r = some (va + vb) → LExpr.wp Γ QT XT ek ρ' J mem) :
    LExpr.wp Γ QT XT e ρ J mem := by
  refine op1_wp hrun (evalArgs_cons ha (evalArgs_cons hb (evalArgs_nil ρ))) ?_
  intro ek hek harg
  rw [OpCode.wp_add]
  simpa [lift2] using hk _ ek _ hek harg (VEnvAgreeBelow.set (Nat.le_refl n) i64 (va + vb))
    (LArg.eval_vArg_set_self ρ { id := n, name := "", ty := i64 } (va + vb))

theorem sub64_wp {Γ : Env} {rs : List Ty} {QT : Post rs} {XT : XPost}
    {a b : LArg} {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {va vb : BitVec 64}
    (hrun : (sub64 a b k).run n = .ok (e, n'))
    (ha : LArg.eval ρ i64 a = some va) (hb : LArg.eval ρ i64 b = some vb)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv),
      (k r).run (n + 1) = .ok (ek, n') → argIdsBelow r (n + 1) → VEnvAgreeBelow n ρ' ρ →
      LArg.eval ρ' i64 r = some (va - vb) → LExpr.wp Γ QT XT ek ρ' J mem) :
    LExpr.wp Γ QT XT e ρ J mem := by
  refine op1_wp hrun (evalArgs_cons ha (evalArgs_cons hb (evalArgs_nil ρ))) ?_
  intro ek hek harg
  rw [OpCode.wp_sub]
  simpa [lift2] using hk _ ek _ hek harg (VEnvAgreeBelow.set (Nat.le_refl n) i64 (va - vb))
    (LArg.eval_vArg_set_self ρ { id := n, name := "", ty := i64 } (va - vb))

theorem and64_wp {Γ : Env} {rs : List Ty} {QT : Post rs} {XT : XPost}
    {a b : LArg} {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {va vb : BitVec 64}
    (hrun : (and64 a b k).run n = .ok (e, n'))
    (ha : LArg.eval ρ i64 a = some va) (hb : LArg.eval ρ i64 b = some vb)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv),
      (k r).run (n + 1) = .ok (ek, n') → argIdsBelow r (n + 1) → VEnvAgreeBelow n ρ' ρ →
      LArg.eval ρ' i64 r = some (va &&& vb) → LExpr.wp Γ QT XT ek ρ' J mem) :
    LExpr.wp Γ QT XT e ρ J mem := by
  refine op1_wp hrun (evalArgs_cons ha (evalArgs_cons hb (evalArgs_nil ρ))) ?_
  intro ek hek harg
  rw [OpCode.wp_and]
  simpa [lift2] using hk _ ek _ hek harg (VEnvAgreeBelow.set (Nat.le_refl n) i64 (va &&& vb))
    (LArg.eval_vArg_set_self ρ { id := n, name := "", ty := i64 } (va &&& vb))

theorem or64_wp {Γ : Env} {rs : List Ty} {QT : Post rs} {XT : XPost}
    {a b : LArg} {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {va vb : BitVec 64}
    (hrun : (or64 a b k).run n = .ok (e, n'))
    (ha : LArg.eval ρ i64 a = some va) (hb : LArg.eval ρ i64 b = some vb)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv),
      (k r).run (n + 1) = .ok (ek, n') → argIdsBelow r (n + 1) → VEnvAgreeBelow n ρ' ρ →
      LArg.eval ρ' i64 r = some (va ||| vb) → LExpr.wp Γ QT XT ek ρ' J mem) :
    LExpr.wp Γ QT XT e ρ J mem := by
  refine op1_wp hrun (evalArgs_cons ha (evalArgs_cons hb (evalArgs_nil ρ))) ?_
  intro ek hek harg
  rw [OpCode.wp_or]
  simpa [lift2] using hk _ ek _ hek harg (VEnvAgreeBelow.set (Nat.le_refl n) i64 (va ||| vb))
    (LArg.eval_vArg_set_self ρ { id := n, name := "", ty := i64 } (va ||| vb))

theorem shl64_wp {Γ : Env} {rs : List Ty} {QT : Post rs} {XT : XPost}
    {a b : LArg} {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {va vb : BitVec 64}
    (hrun : (shl64 a b k).run n = .ok (e, n'))
    (ha : LArg.eval ρ i64 a = some va) (hb : LArg.eval ρ i64 b = some vb)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv),
      (k r).run (n + 1) = .ok (ek, n') → argIdsBelow r (n + 1) → VEnvAgreeBelow n ρ' ρ →
      LArg.eval ρ' i64 r = some (va <<< (vb.toNat % 64)) → LExpr.wp Γ QT XT ek ρ' J mem) :
    LExpr.wp Γ QT XT e ρ J mem := by
  refine op1_wp hrun (evalArgs_cons ha (evalArgs_cons hb (evalArgs_nil ρ))) ?_
  intro ek hek harg
  rw [OpCode.wp_shl]
  simpa [lift2] using hk _ ek _ hek harg
    (VEnvAgreeBelow.set (Nat.le_refl n) i64 (va <<< (vb.toNat % 64)))
    (LArg.eval_vArg_set_self ρ { id := n, name := "", ty := i64 } (va <<< (vb.toNat % 64)))

theorem lshr64_wp {Γ : Env} {rs : List Ty} {QT : Post rs} {XT : XPost}
    {a b : LArg} {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {va vb : BitVec 64}
    (hrun : (lshr64 a b k).run n = .ok (e, n'))
    (ha : LArg.eval ρ i64 a = some va) (hb : LArg.eval ρ i64 b = some vb)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv),
      (k r).run (n + 1) = .ok (ek, n') → argIdsBelow r (n + 1) → VEnvAgreeBelow n ρ' ρ →
      LArg.eval ρ' i64 r = some (va >>> (vb.toNat % 64)) → LExpr.wp Γ QT XT ek ρ' J mem) :
    LExpr.wp Γ QT XT e ρ J mem := by
  refine op1_wp hrun (evalArgs_cons ha (evalArgs_cons hb (evalArgs_nil ρ))) ?_
  intro ek hek harg
  rw [OpCode.wp_lshr]
  simpa [lift2] using hk _ ek _ hek harg
    (VEnvAgreeBelow.set (Nat.le_refl n) i64 (va >>> (vb.toNat % 64)))
    (LArg.eval_vArg_set_self ρ { id := n, name := "", ty := i64 } (va >>> (vb.toNat % 64)))

theorem cmpOp_wp {Γ : Env} {rs : List Ty} {QT : Post rs} {XT : XPost}
    {o : CmpOp} {w : Nat} {a b : LArg} {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {va vb : BitVec w}
    (hrun : (cmpOp o w a b k).run n = .ok (e, n'))
    (ha : LArg.eval ρ (Ty.bits w) a = some va)
    (hb : LArg.eval ρ (Ty.bits w) b = some vb)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv),
      (k r).run (n + 1) = .ok (ek, n') → argIdsBelow r (n + 1) → VEnvAgreeBelow n ρ' ρ →
      LArg.eval ρ' .bool r = some (o.evalBits va vb) → LExpr.wp Γ QT XT ek ρ' J mem) :
    LExpr.wp Γ QT XT e ρ J mem := by
  refine op1_wp hrun (evalArgs_cons ha (evalArgs_cons hb (evalArgs_nil ρ))) ?_
  intro ek hek harg
  rw [OpCode.wp_cmp]
  simpa [liftCmp] using hk _ ek _ hek harg
    (VEnvAgreeBelow.set (Nat.le_refl n) .bool (o.evalBits va vb))
    (LArg.eval_vArg_set_self ρ { id := n, name := "", ty := .bool } (o.evalBits va vb))

theorem addrOf_wp {Γ : Env} {rs : List Ty} {QT : Post rs} {XT : XPost}
    {x : LArg} {off : Nat} {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {vx : BitVec 64}
    (hrun : (addrOf x off k).run n = .ok (e, n'))
    (hx : LArg.eval ρ i64 x = some vx) (hnx : argIdsBelow x n)
    (hk : ∀ (a : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (na : Nat),
      n ≤ na → (k a).run na = .ok (ek, n') → argIdsBelow a na → VEnvAgreeBelow n ρ' ρ →
      LArg.eval ρ' i64 a = some (vx + BitVec.ofNat 64 off) →
      LExpr.wp Γ QT XT ek ρ' J mem) :
    LExpr.wp Γ QT XT e ρ J mem := by
  unfold addrOf at hrun
  by_cases h0 : (off == 0) = true
  · rw [ite_eq_left h0] at hrun
    have hzero : off = 0 := beq_iff_eq.mp h0
    subst hzero
    refine hk x e ρ n (Nat.le_refl n) hrun hnx (VEnvAgreeBelow.refl n ρ) ?_
    simpa using hx
  · rw [ite_eq_right h0] at hrun
    refine add64_wp hrun hx (LArg.eval_imm_self ρ i64 (BitVec.ofNat 64 off)) ?_
    intro r ek ρ' hek harg hagr hr
    exact hk r ek ρ' (n + 1) (Nat.le_succ n) hek harg hagr hr

theorem lm_loadAt_wp {Γ : Env} {rs : List Ty} {QT : Post rs} {XT : XPost}
    {t : Ty} {x : LArg} {off : Nat} {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {vx : BitVec 64} {val : Val t}
    (hrun : (loadAt t x off k).run n = .ok (e, n'))
    (hx : LArg.eval ρ i64 x = some vx) (hnx : argIdsBelow x n)
    (hload : loadVal mem t (vx + BitVec.ofNat 64 off) = some val)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (nr : Nat),
      n + 1 ≤ nr → (k r).run nr = .ok (ek, n') → argIdsBelow r nr → VEnvAgreeBelow n ρ' ρ →
      LArg.eval ρ' t r = some val → LExpr.wp Γ QT XT ek ρ' J mem) :
    LExpr.wp Γ QT XT e ρ J mem := by
  unfold loadAt at hrun
  refine addrOf_wp hrun hx hnx ?_
  intro a ek ρ1 na hna hrun1 _ hagr ha
  rw [lm_bind_run] at hrun1
  rcases hrun1 with ⟨v, n1, hv, hrest1⟩
  rw [freshVar_run] at hv
  injection hv with hvp
  have hv_eq : v = { id := na, name := "", ty := t } := (congrArg Prod.fst hvp).symm
  have hn1 : n1 = na + 1 := (congrArg Prod.snd hvp).symm
  subst hv_eq; subst hn1
  rw [lm_bind_run] at hrest1
  rcases hrest1 with ⟨body, n2, hbody, hpure⟩
  rw [lm_pure_run] at hpure
  injection hpure with hpr
  have heq : LExpr.load t a { id := na, name := "", ty := t } body = ek := congrArg Prod.fst hpr
  have hn2 : n2 = n' := congrArg Prod.snd hpr
  subst heq; subst hn2
  refine wp_load rfl ha hload ?_
  have hagr' : VEnvAgreeBelow n (ρ1.set na t val) ρ :=
    (VEnvAgreeBelow.set hna t val).trans hagr
  exact hk _ body _ (na + 1) (by omega) hbody (Nat.lt_succ_self na) hagr'
    (LArg.eval_vArg_set_self ρ1 { id := na, name := "", ty := t } val)

theorem storeAt_wp {Γ : Env} {rs : List Ty} {QT : Post rs} {XT : XPost}
    {t : Ty} {v x : LArg} {off : Nat} {k : LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {vv : Val t} {vx : BitVec 64}
    (hrun : (storeAt t v x off k).run n = .ok (e, n'))
    (hv : LArg.eval ρ t v = some vv) (hnv : argIdsBelow v n)
    (hx : LArg.eval ρ i64 x = some vx) (hnx : argIdsBelow x n)
    (hok : storeOk mem t (vx + BitVec.ofNat 64 off))
    (hk : ∀ (ek : LExpr) (ρ' : Frontend.C0.VEnv) (nk : Nat),
      n ≤ nk → k.run nk = .ok (ek, n') → VEnvAgreeBelow n ρ' ρ →
      LExpr.wp Γ QT XT ek ρ' J (storeMem mem t (vx + BitVec.ofNat 64 off) vv)) :
    LExpr.wp Γ QT XT e ρ J mem := by
  unfold storeAt at hrun
  refine addrOf_wp hrun hx hnx ?_
  intro a ek ρ1 na hna hrun1 _ hagr ha
  rw [lm_bind_run] at hrun1
  rcases hrun1 with ⟨body, n1, hbody, hpure⟩
  rw [lm_pure_run] at hpure
  injection hpure with hpr
  have heq : LExpr.store t v a body = ek := congrArg Prod.fst hpr
  have hn1 : n1 = n' := congrArg Prod.snd hpr
  subst heq; subst hn1
  have hv1 : LArg.eval ρ1 t v = some vv := (hagr.eval hnv).trans hv
  exact wp_store hv1 ha hok (hk body ρ1 na hna hbody hagr)

theorem callN_wp {Γ : Env} {rs_ret : List Ty} {QT : Post rs_ret} {XT : XPost}
    {f : Sym} {as bs : List Ty} {args : List LArg} {k : List LArg → LM LExpr}
    {n n' : Nat} {e : LExpr} {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {xs : Tup Val as}
    (hrun : (callN f as bs args k).run n = .ok (e, n'))
    (hev : evalArgs ρ as args = some xs)
    {P : Post bs} {E : XPost} (hcall : Γ f as bs xs mem P E)
    (hE : ∀ g cs ys m', E g cs ys m' → XT g cs ys m')
    (hk : ∀ (pvs : List Frontend.C0.LVar) (ek : LExpr),
      pvs = mkFreshVars bs n →
      (k (pvs.map vArg)).run (n + bs.length) = .ok (ek, n') →
      ∀ r m', P r m' →
        VEnvAgreeBelow n (ρ.bind pvs bs r) ρ →
        (∀ a ∈ pvs.map vArg, argIdsBelow a (n + bs.length)) →
        LExpr.wp Γ QT XT ek (ρ.bind pvs bs r) J m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  unfold callN at hrun
  rw [lm_bind_run] at hrun
  rcases hrun with ⟨pvs, n1, hpvs, hrest⟩
  simp only [mapM_freshVar_run, Except.ok.injEq, Prod.mk.injEq] at hpvs
  rcases hpvs with ⟨rfl, rfl⟩
  rw [lm_bind_run] at hrest
  rcases hrest with ⟨body, n2, hbody, hpure⟩
  rw [lm_pure_run] at hpure
  injection hpure with hpr
  have he : LExpr.call f as bs args (mkFreshVars bs n) body = e := congrArg Prod.fst hpr
  have hn2 : n2 = n' := congrArg Prod.snd hpr
  subst he; subst hn2
  refine wp_call (mkFreshVars_map_ty bs n) hev hcall (fun r m' hP => ?_) hE
  refine hk (mkFreshVars bs n) body rfl hbody r m' hP ?_ ?_
  · exact fun a u ha => LArg.eval_bind_mkFreshVars_lt ha r
  · intro a ha
    rcases List.mem_map.mp ha with ⟨v, hv, rfl⟩
    exact (mkFreshVars_id_bounds bs n v hv).2

theorem call1_wp {Γ : Env} {rs_ret : List Ty} {QT : Post rs_ret} {XT : XPost}
    {f : Sym} {as : List Ty} {b : Ty} {args : List LArg} {k : LArg → LM LExpr}
    {n n' : Nat} {e : LExpr} {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {xs : Tup Val as}
    (hrun : (call1 f as b args k).run n = .ok (e, n'))
    (hev : evalArgs ρ as args = some xs)
    {P : Post [b]} {E : XPost} (hcall : Γ f as [b] xs mem P E)
    (hE : ∀ g cs ys m', E g cs ys m' → XT g cs ys m')
    (hk : ∀ (r : LArg) (ek : LExpr),
      (k r).run (n + 1) = .ok (ek, n') → argIdsBelow r (n + 1) →
      ∀ rv m', P (rv, ()) m' →
        VEnvAgreeBelow n (ρ.set n b rv) ρ →
        LArg.eval (ρ.set n b rv) b r = some rv →
        LExpr.wp Γ QT XT ek (ρ.set n b rv) J m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  unfold call1 at hrun
  refine callN_wp hrun hev hcall hE ?_
  intro pvs ek hpvs hek ⟨rv, u⟩ m' hP hagr hids
  cases u
  subst hpvs
  have hek' : (k (vArg { id := n, name := "", ty := b })).run (n + 1) = .ok (ek, n') := hek
  have harg : argIdsBelow (vArg { id := n, name := "", ty := b }) (n + 1) :=
    hids _ List.mem_cons_self
  have hbind : ρ.bind (mkFreshVars [b] n) [b] (rv, ()) = ρ.set n b rv := rfl
  rw [hbind] at hagr ⊢
  exact hk _ ek hek' harg rv m' hP hagr
    (LArg.eval_vArg_set_self ρ { id := n, name := "", ty := b } rv)

theorem call0_wp {Γ : Env} {rs_ret : List Ty} {QT : Post rs_ret} {XT : XPost}
    {f : Sym} {as : List Ty} {args : List LArg} {k : LM LExpr}
    {n n' : Nat} {e : LExpr} {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {xs : Tup Val as}
    (hrun : (call0 f as args k).run n = .ok (e, n'))
    (hev : evalArgs ρ as args = some xs)
    {P : Post []} {E : XPost} (hcall : Γ f as [] xs mem P E)
    (hE : ∀ g cs ys m', E g cs ys m' → XT g cs ys m')
    (hk : ∀ (ek : LExpr), k.run n = .ok (ek, n') → ∀ m', P () m' → LExpr.wp Γ QT XT ek ρ J m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  unfold call0 at hrun
  refine callN_wp hrun hev hcall hE ?_
  intro pvs ek hpvs hek r m' hP _ _
  cases r
  subst hpvs
  exact hk ek hek m' hP

theorem withJoin_wp {Γ : Env} {rs_ret : List Ty} {QT : Post rs_ret} {XT : XPost}
    {ts : List Ty} {rest : List LArg → LM LExpr} {pre : (List LArg → LExpr) → LM LExpr}
    {n n' : Nat} {e : LExpr} {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64}
    (Inv : Tup Val ts → Mem 64 → Prop)
    (hrun : (withJoin ts rest pre).run n = .ok (e, n'))
    (hrest_mono : LMMono (rest ((mkFreshVars ts (n + 1)).map vArg)))
    (hrest : ∀ (ps : List Frontend.C0.LVar) (blk : LExpr) (n2 : Nat) (J' : JEnv),
      ps = mkFreshVars ts (n + 1) →
      (rest (ps.map vArg)).run (n + 1 + ts.length) = .ok (blk, n2) →
      JEnvAgreeBelow n J' J →
      ∀ (xs : Tup Val ts) (m1 : Mem 64),
        Inv xs m1 →
        VEnvAgreeBelow n (ρ.bind ps ts xs) ρ →
        (∀ a ∈ ps.map vArg, argIdsBelow a (n + 1 + ts.length)) →
        evalArgs (ρ.bind ps ts xs) ts (ps.map vArg) = some xs →
        LExpr.wp Γ QT XT blk (ρ.bind ps ts xs) J' m1)
    (hpre : ∀ (j : List LArg → LExpr) (body : LExpr) (n2 : Nat) (J' : JEnv),
      n + 1 + ts.length ≤ n2 →
      (pre j).run n2 = .ok (body, n') →
      JEnvAgreeBelow n J' J →
      (∀ (J_cur : JEnv) (args : List LArg) (ρ_j : Frontend.C0.VEnv) (m_j : Mem 64)
          (xs : Tup Val ts),
        JEnvAgreeBelow (n + 1) J_cur J' →
        evalArgs ρ_j ts args = some xs → Inv xs m_j →
        LExpr.wp Γ QT XT (j args) ρ_j J_cur m_j) →
      LExpr.wp Γ QT XT body ρ J' mem) :
    LExpr.wp Γ QT XT e ρ J mem := by
  unfold withJoin at hrun
  rw [lm_bind_run] at hrun
  rcases hrun with ⟨lbl, n1, hlbl, h1⟩
  rw [fresh_run] at hlbl
  injection hlbl with hlp
  have hlbl_eq : lbl = n := (congrArg Prod.fst hlp).symm
  have hn1 : n1 = n + 1 := (congrArg Prod.snd hlp).symm
  subst hn1
  rw [lm_bind_run] at h1
  rcases h1 with ⟨ps, n2, hps, h2⟩
  simp only [mapM_freshVar_run, Except.ok.injEq, Prod.mk.injEq] at hps
  rcases hps with ⟨rfl, rfl⟩
  rw [lm_bind_run] at h2
  rcases h2 with ⟨blk, n3, hblk, h3⟩
  rw [lm_bind_run] at h3
  rcases h3 with ⟨body, n4, hbody, hpure⟩
  rw [lm_pure_run] at hpure
  rw [hlbl_eq] at hbody hpure
  injection hpure with hpr
  have he : LExpr.group [(n, mkFreshVars ts (n + 1), blk)] body = e := congrArg Prod.fst hpr
  have hn4 : n4 = n' := congrArg Prod.snd hpr
  subst he; subst hn4
  have hn_le : n + 1 + ts.length ≤ n3 := hrest_mono (n + 1 + ts.length) blk n3 hblk
  intro Js ⟨hblk_closed, _⟩
  rcases Js with ⟨J_head, u⟩; cases u
  have hmap : (mkFreshVars ts (n + 1)).map (·.ty) = ts := mkFreshVars_map_ty ts (n + 1)
  have hJ'_eq : J.bind (lBlockIds [(n, mkFreshVars ts (n + 1), blk)])
      (lBlockSig [(n, mkFreshVars ts (n + 1), blk)]) (J_head, ()) =
      J.set n ((mkFreshVars ts (n + 1)).map (·.ty)) J_head := by
    have hbindAux : ∀ (ids : List Nat) (sig : List (List Ty)) (ks : Tup Cont sig),
        ids = [n] → sig = [(mkFreshVars ts (n + 1)).map (·.ty)] →
        ks ≍ ((J_head, ()) : Tup Cont [(mkFreshVars ts (n + 1)).map (·.ty)]) →
        J.bind ids sig ks = J.set n ((mkFreshVars ts (n + 1)).map (·.ty)) J_head := by
      rintro ids sig ks rfl rfl hks
      cases hks
      rw [JEnv.bind.eq_1, JEnv.bind.eq_2]
      intro _ _ _ _ _ h; cases h
    exact hbindAux _ _ _ (by rw [lBlockIds.eq_1]; rfl) (by rw [lBlockSig.eq_1]; rfl) HEq.rfl
  let J' := J.set n ((mkFreshVars ts (n + 1)).map (·.ty)) J_head
  have hJagr : JEnvAgreeBelow n J' J := JEnvAgreeBelow.set J (Nat.le_refl n) _ J_head
  refine hpre (fun args => LExpr.jump n ts args) body n3 J' hn_le hbody hJagr ?_
  · intro J_cur args ρ_j m_j xs hJcur hev hInv
    have hget_cur : J_cur.get n ts = J'.get n ts := hJcur n ts (Nat.lt_succ_self n)
    have hJget : J'.get n ts = some (hmap ▸ J_head) := by
      have hself : J'.get n ((mkFreshVars ts (n + 1)).map (·.ty)) = some J_head :=
        JEnv.get_set_self J n ((mkFreshVars ts (n + 1)).map (·.ty)) J_head
      have hcast : ∀ (us : List Ty) (heq : us = ts) (k0 : Cont us),
          (J.set n us k0).get n us = some k0 → (J.set n us k0).get n ts = some (heq ▸ k0) := by
        intro us heq k0 hk0; subst heq; exact hk0
      exact hcast _ hmap J_head hself
    refine wp_jump (hget_cur.trans hJget) hev ?_
    have hclose : ∀ (us : List Ty) (heq : us = ts) (k0 : Cont us),
        (∀ (xs0 : Tup Val us) (m1 : Mem 64),
          LExpr.wp Γ QT XT blk (ρ.bind (mkFreshVars ts (n + 1)) us xs0)
            (J.set n us k0) m1 → k0 xs0 m1) →
        LExpr.wp Γ QT XT blk (ρ.bind (mkFreshVars ts (n + 1)) ts xs)
          (J.set n us k0) m_j → (heq ▸ k0) xs m_j := by
      intro us heq k0 hk0 hwp0
      subst heq
      exact hk0 xs m_j hwp0
    refine hclose _ hmap J_head ?_ ?_
    · intro xs0 m1 hwp0
      apply hblk_closed xs0 m1
      simpa only [hJ'_eq] using hwp0
    · refine hrest (mkFreshVars ts (n + 1)) blk n3 J' rfl hblk hJagr xs m_j hInv ?_ ?_ ?_
      · intro a u ha
        exact LArg.eval_bind_mkFreshVars_lt (argIdsBelow_mono (Nat.le_succ n) ha) xs
      · intro a ha
        rcases List.mem_map.mp ha with ⟨v, hv, rfl⟩
        exact (mkFreshVars_id_bounds ts (n + 1) v hv).2
      · exact evalArgs_bind_mkFreshVars ts (n + 1) ρ xs

theorem withJoin1_wp {Γ : Env} {rs_ret : List Ty} {QT : Post rs_ret} {XT : XPost}
    {t : Ty} {rest : LArg → LM LExpr} {pre : (LArg → LExpr) → LM LExpr}
    {n n' : Nat} {e : LExpr} {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64}
    (Inv : Val t → Mem 64 → Prop)
    (hrun : (withJoin1 t rest pre).run n = .ok (e, n'))
    (hrest_mono : LMMono (rest (vArg { id := n + 1, name := "", ty := t })))
    (hrest : ∀ (r : LArg) (blk : LExpr) (n2 : Nat) (J' : JEnv),
      (rest r).run (n + 2) = .ok (blk, n2) →
      argIdsBelow r (n + 2) →
      JEnvAgreeBelow n J' J →
      ∀ (v : Val t) (m1 : Mem 64),
        Inv v m1 →
        VEnvAgreeBelow n (ρ.set (n + 1) t v) ρ →
        LArg.eval (ρ.set (n + 1) t v) t r = some v →
        LExpr.wp Γ QT XT blk (ρ.set (n + 1) t v) J' m1)
    (hpre : ∀ (j : LArg → LExpr) (body : LExpr) (n2 : Nat) (J' : JEnv),
      n + 2 ≤ n2 →
      (pre j).run n2 = .ok (body, n') →
      JEnvAgreeBelow n J' J →
      (∀ (J_cur : JEnv) (a : LArg) (ρ_j : Frontend.C0.VEnv) (m_j : Mem 64) (v : Val t),
        JEnvAgreeBelow (n + 1) J_cur J' →
        LArg.eval ρ_j t a = some v → Inv v m_j →
        LExpr.wp Γ QT XT (j a) ρ_j J_cur m_j) →
      LExpr.wp Γ QT XT body ρ J' mem) :
    LExpr.wp Γ QT XT e ρ J mem := by
  unfold withJoin1 at hrun
  refine withJoin_wp (fun (xs : Tup Val [t]) m1 => Inv xs.1 m1) hrun hrest_mono ?_ ?_
  · intro ps blk n2 J' hps hblk hJagr ⟨v, u⟩ m1 hInv hagr hids hev
    cases u
    subst hps
    have harg : argIdsBelow (vArg { id := n + 1, name := "", ty := t }) (n + 2) :=
      hids _ List.mem_cons_self
    have hbind : ρ.bind (mkFreshVars [t] (n + 1)) [t] (v, ()) = ρ.set (n + 1) t v := rfl
    rw [hbind] at hagr ⊢
    exact hrest _ blk n2 J' hblk harg hJagr v m1 hInv hagr
      (LArg.eval_vArg_set_self ρ { id := n + 1, name := "", ty := t } v)
  · intro j body n2 J' hn2 hbody hJagr hjok
    refine hpre (fun r => j [r]) body n2 J' hn2 hbody hJagr ?_
    intro J_cur a ρ_j m_j v hJcur ha hInv
    exact hjok J_cur [a] ρ_j m_j (v, ()) hJcur (evalArgs_cons ha (evalArgs_nil ρ_j)) hInv

theorem convW_wp {Γ : Env} {rs : List Ty} {QT : Post rs} {XT : XPost}
    {m w : Nat} {x : LArg} {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {vx : BitVec m}
    (hrun : (convW m w x k).run n = .ok (e, n'))
    (hx : LArg.eval ρ (Ty.bits m) x = some vx) (hnx : argIdsBelow x n)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (nr : Nat),
      n ≤ nr → (k r).run nr = .ok (ek, n') → argIdsBelow r nr → VEnvAgreeBelow n ρ' ρ →
      LArg.eval ρ' (Ty.bits w) r = some (vx.setWidth w) →
      LExpr.wp Γ QT XT ek ρ' J mem) :
    LExpr.wp Γ QT XT e ρ J mem := by
  unfold convW at hrun
  by_cases hmeq : (m == w) = true
  · rw [ite_eq_left hmeq] at hrun
    have hm : m = w := beq_iff_eq.mp hmeq
    subst hm
    refine hk x e ρ n (Nat.le_refl n) hrun hnx (VEnvAgreeBelow.refl n ρ) ?_
    simpa [BitVec.setWidth_eq] using hx
  · rw [ite_eq_right hmeq] at hrun
    have hne : m ≠ w := fun he => hmeq (beq_iff_eq.mpr he)
    by_cases hlt : m < w
    · rw [ite_eq_left hlt] at hrun
      refine op1_wp hrun (evalArgs_cons hx (evalArgs_nil ρ)) ?_
      intro ek hek harg
      rw [OpCode.wp_zext]
      exact ⟨Nat.le_of_lt hlt, hk _ ek _ (n + 1) (Nat.le_succ n) hek harg
        (VEnvAgreeBelow.set (Nat.le_refl n) (Ty.bits w) (vx.setWidth w))
        (LArg.eval_vArg_set_self ρ { id := n, name := "", ty := Ty.bits w } (vx.setWidth w))⟩
    · rw [ite_eq_right hlt] at hrun
      have hgt : w ≤ m := by omega
      refine op1_wp hrun (evalArgs_cons hx (evalArgs_nil ρ)) ?_
      intro ek hek harg
      rw [OpCode.wp_trunc]
      exact ⟨hgt, hk _ ek _ (n + 1) (Nat.le_succ n) hek harg
        (VEnvAgreeBelow.set (Nat.le_refl n) (Ty.bits w) (vx.setWidth w))
        (LArg.eval_vArg_set_self ρ { id := n, name := "", ty := Ty.bits w } (vx.setWidth w))⟩

theorem boxSmall_wp {Γ : Env} {rs : List Ty} {QT : Post rs} {XT : XPost}
    {x : LArg} {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {vx : BitVec 64}
    (hrun : (boxSmall x k).run n = .ok (e, n'))
    (hx : LArg.eval ρ i64 x = some vx)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv),
      (k r).run (n + 2) = .ok (ek, n') → argIdsBelow r (n + 2) → VEnvAgreeBelow n ρ' ρ →
      LArg.eval ρ' i64 r = some ((vx <<< 1) ||| 1#64) →
      LExpr.wp Γ QT XT ek ρ' J mem) :
    LExpr.wp Γ QT XT e ρ J mem := by
  unfold boxSmall at hrun
  refine shl64_wp hrun hx (LArg.eval_imm_self ρ i64 1#64) ?_
  intro s ek1 ρ1 hek1 harg1 hagr1 hs
  refine or64_wp hek1 hs (LArg.eval_imm_self ρ1 i64 1#64) ?_
  intro r ek2 ρ2 hek2 harg2 hagr2 hr
  have h1 : (1#64 : BitVec 64).toNat % 64 = 1 := by decide
  rw [h1] at hr
  exact hk r ek2 ρ2 hek2 harg2 ((hagr2.mono (Nat.le_succ n)).trans hagr1) hr

theorem boolToU8_wp {Γ : Env} {rs : List Ty} {QT : Post rs} {XT : XPost}
    {b : LArg} {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {vb : Bool}
    (hrun : (boolToU8 b k).run n = .ok (e, n'))
    (hb : LArg.eval ρ .bool b = some vb)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv),
      (k r).run (n + 1) = .ok (ek, n') → argIdsBelow r (n + 1) → VEnvAgreeBelow n ρ' ρ →
      LArg.eval ρ' i8 r = some (if vb then 1#8 else 0#8) →
      LExpr.wp Γ QT XT ek ρ' J mem) :
    LExpr.wp Γ QT XT e ρ J mem := by
  unfold boolToU8 at hrun
  refine op1_wp hrun (evalArgs_cons hb (evalArgs_nil ρ)) ?_
  intro ek hek harg
  rw [OpCode.wp_ofBool]
  have hvb : BitVec.ofNat 8 (Bool.toNat vb) = if vb then 1#8 else 0#8 := by cases vb <;> rfl
  have heval := hk _ ek _ hek harg (VEnvAgreeBelow.set (Nat.le_refl n) i8 _)
    (LArg.eval_vArg_set_self ρ { id := n, name := "", ty := i8 } _)
  simpa [hvb] using heval

theorem isScalarObj_wp {Γ : Env} {rs : List Ty} {QT : Post rs} {XT : XPost}
    {x : LArg} {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {vx : BitVec 64}
    (hrun : (LeanLCNF.isScalarObj x k).run n = .ok (e, n'))
    (hx : LArg.eval ρ i64 x = some vx)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv),
      (k r).run (n + 2) = .ok (ek, n') → argIdsBelow r (n + 2) → VEnvAgreeBelow n ρ' ρ →
      LArg.eval ρ' .bool r = some (decide ((vx &&& 1#64) ≠ 0#64)) →
      LExpr.wp Γ QT XT ek ρ' J mem) :
    LExpr.wp Γ QT XT e ρ J mem := by
  unfold LeanLCNF.isScalarObj at hrun
  refine and64_wp hrun hx (LArg.eval_imm_self ρ i64 1#64) ?_
  intro b ek1 ρ1 hek1 harg1 hagr1 hb
  refine cmpOp_wp hek1 hb (LArg.eval_imm_self ρ1 i64 0#64) ?_
  intro r ek2 ρ2 hek2 harg2 hagr2 hr
  have hev : CmpOp.evalBits .ne (vx &&& 1#64) 0#64 = decide ((vx &&& 1#64) ≠ 0#64) := rfl
  rw [hev] at hr
  exact hk r ek2 ρ2 hek2 harg2 ((hagr2.mono (Nat.le_succ n)).trans hagr1) hr

/-! ## 4. `rtCall1`, `callFn`, and `LMMono` Monotonicity Lemmas -/

/-- Evaluation witness for a single runtime-call argument after widening to `i64`. -/
@[expose] def EvalRtArg (ρ : Frontend.C0.VEnv) (a : LArg) (v : BitVec 64) : Prop :=
  ∃ (w : Nat) (bv : BitVec w),
    w = argBitsWidth a ∧ LArg.eval ρ (Ty.bits w) a = some bv ∧ v = bv.setWidth 64

/-- Evaluation witness for a list of runtime-call arguments widened to `i64`. -/
@[expose] def EvalRtArgs (ρ : Frontend.C0.VEnv) (args : List LArg) (vs : List (BitVec 64)) : Prop :=
  args.length = vs.length ∧ ∀ p ∈ args.zip vs, EvalRtArg ρ p.1 p.2

theorem EvalRtArgs.agree {n : Nat} {ρ' ρ : Frontend.C0.VEnv} {args : List LArg}
    {vs : List (BitVec 64)} (hagr : VEnvAgreeBelow n ρ' ρ)
    (hids : ∀ a ∈ args, argIdsBelow a n) (h : EvalRtArgs ρ args vs) :
    EvalRtArgs ρ' args vs := by
  refine ⟨h.1, fun p hp => ?_⟩
  rcases h.2 p hp with ⟨w, bv, hw, hev, hp2⟩
  have hmem : p.1 ∈ args := (List.of_mem_zip hp).1
  exact ⟨w, bv, hw, (hagr.eval (hids p.1 hmem)).trans hev, hp2⟩

theorem rtCall1_go_wp {Γ : Env} {rs_ret : List Ty} {QT : Post rs_ret} {XT : XPost}
    {rtArg : LArg} {fn : Sym} {resW : Nat} {k : LArg → LM LExpr}
    {n n' : Nat} {e : LExpr} {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64}
    {rtVal : BitVec 64}
    (hrt : LArg.eval ρ i64 rtArg = some rtVal) (hnrt : argIdsBelow rtArg n) :
    ∀ (rem acc : List LArg) (remVals accVals : List (BitVec 64)),
      (rtCall1.go rtArg fn resW k rem acc).run n = .ok (e, n') →
      (∀ a ∈ rem, argIdsBelow a n) →
      EvalRtArgs ρ rem remVals →
      acc.length = accVals.length →
      (∀ p ∈ acc.zip accVals, argIdsBelow p.1 n ∧ LArg.eval ρ i64 p.1 = some p.2) →
      (∃ (P : Post [i64]) (E : XPost),
        Γ fn (List.replicate (rtVal :: (accVals ++ remVals)).length i64) [i64]
          (tupOfBV64s (rtVal :: (accVals ++ remVals))) mem P E ∧
        (∀ g cs ys m', E g cs ys m' → XT g cs ys m') ∧
        (∀ (ret : BitVec 64) (m' : Mem 64), P (ret, ()) m' →
          ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (nr : Nat),
            n ≤ nr → (k r).run nr = .ok (ek, n') → argIdsBelow r nr →
            VEnvAgreeBelow n ρ' ρ →
            LArg.eval ρ' (Ty.bits resW) r = some (ret.setWidth resW) →
            LExpr.wp Γ QT XT ek ρ' J m')) →
      LExpr.wp Γ QT XT e ρ J mem := by
  intro rem
  induction rem generalizing n e ρ with
  | nil =>
    intro acc remVals accVals hrun _ hrem hlen hacc ⟨P, E, hΓ, hE, hk⟩
    have hrem0 : remVals = [] := List.length_eq_zero_iff.mp hrem.1.symm
    subst hrem0
    have hcastNil : ∀ l : List (BitVec 64), l = accVals →
        Γ fn (List.replicate (rtVal :: l).length i64) [i64] (tupOfBV64s (rtVal :: l)) mem P E →
        Γ fn (List.replicate (rtVal :: accVals).length i64) [i64]
          (tupOfBV64s (rtVal :: accVals)) mem P E := by
      intro l hl; subst hl; exact id
    replace hΓ := hcastNil (accVals ++ []) (List.append_nil accVals) hΓ
    rw [rtCall1.go.eq_1] at hrun
    obtain ⟨tup, hev, hwd⟩ := evalArgs_replicate_i64 ρ (rtArg :: acc) (rtVal :: accVals)
      (by simp [hlen]) (fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact hrt
        · exact (hacc p hp').2)
    have hlen' : (rtArg :: acc).length = (rtVal :: accVals).length := by simp [hlen]
    have hcast : ∀ (k1 k2 : Nat) (hk0 : k1 = k2)
        (t1 : Tup Val (List.replicate k1 i64)) (t2 : Tup Val (List.replicate k2 i64)),
        wordsOfTup t1 = wordsOfTup t2 →
        Γ fn (List.replicate k2 i64) [i64] t2 mem P E →
        Γ fn (List.replicate k1 i64) [i64] t1 mem P E := by
      intro k1 k2 hk0; subst hk0; intro t1 t2 hwt hg
      rwa [wordsOfTup_inj_i64 k1 t1 t2 hwt]
    have hΓ' : Γ fn (List.replicate (acc.length + 1) i64) [i64] tup mem P E :=
      hcast (acc.length + 1) (rtVal :: accVals).length (by simp [hlen]) tup
        (tupOfBV64s (rtVal :: accVals)) (hwd.trans (wordsOfTup_tupOfBV64s _).symm) hΓ
    refine call1_wp hrun (by simpa using hev) hΓ' hE ?_
    intro r1 ek1 hek1 harg1 ret m' hP hagr1 hr1
    refine convW_wp hek1 hr1 harg1 ?_
    intro r2 ek2 ρ2 nr2 hnr2 hek2 harg2 hagr2 hr2
    exact hk ret m' hP r2 ek2 ρ2 nr2 (by omega) hek2 harg2
      ((hagr2.mono (Nat.le_succ n)).trans hagr1) hr2
  | cons a rest ih =>
    intro acc remVals accVals hrun hrem hremEv hlen hacc ⟨P, E, hΓ, hE, hk⟩
    rcases remVals with _ | ⟨v, restVals⟩
    · simp [EvalRtArgs] at hremEv
    have ha_id : argIdsBelow a n := hrem a List.mem_cons_self
    have ha_ev : EvalRtArg ρ a v := hremEv.2 (a, v) List.mem_cons_self
    rcases ha_ev with ⟨w, bv, hw, hev_a, rfl⟩
    have hrest_ev : EvalRtArgs ρ rest restVals :=
      ⟨Nat.succ.inj hremEv.1, fun p hp => hremEv.2 p (List.mem_cons_of_mem _ hp)⟩
    rw [rtCall1.go.eq_2] at hrun
    rw [← hw] at hrun
    refine convW_wp hrun hev_a ha_id ?_
    intro a64 ek ρ1 n1 hn1 hek ha64 hagr1 ha64_ev
    refine ih ((hagr1.eval hnrt).trans hrt) (argIdsBelow_mono hn1 hnrt)
      (acc ++ [a64]) restVals (accVals ++ [bv.setWidth 64]) hek ?_ ?_ ?_ ?_ ?_
    · intro x hx
      exact argIdsBelow_mono hn1 (hrem x (List.mem_cons_of_mem _ hx))
    · exact hrest_ev.agree hagr1 (fun x hx => hrem x (List.mem_cons_of_mem _ hx))
    · simp [hlen]
    · intro p hp
      have hzip : (acc ++ [a64]).zip (accVals ++ [bv.setWidth 64]) =
          acc.zip accVals ++ [(a64, bv.setWidth 64)] :=
        List.zip_append hlen
      rw [hzip, List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · have hold := hacc p hp
        exact ⟨argIdsBelow_mono hn1 hold.1, (hagr1.eval hold.1).trans hold.2⟩
      · exact ⟨ha64, ha64_ev⟩
    · refine ⟨P, E, ?_, hE, ?_⟩
      · have hcastCons : ∀ l1 l2 : List (BitVec 64), l1 = l2 →
            Γ fn (List.replicate (rtVal :: l1).length i64) [i64]
              (tupOfBV64s (rtVal :: l1)) mem P E →
            Γ fn (List.replicate (rtVal :: l2).length i64) [i64]
              (tupOfBV64s (rtVal :: l2)) mem P E := by
          intro l1 l2 hl; subst hl; exact id
        exact hcastCons _ _ (List.append_assoc accVals [bv.setWidth 64] restVals).symm hΓ
      · intro ret m' hP r ek' ρ' nr hnr hek' har hagr' hr'
        exact hk ret m' hP r ek' ρ' nr (Nat.le_trans hn1 hnr) hek' har
          ((hagr'.mono hn1).trans hagr1) hr'

theorem rtCall1_wp {Γ : Env} {rs_ret : List Ty} {QT : Post rs_ret} {XT : XPost}
    {rtArg : LArg} {fn : Sym} {args : List LArg} {resW : Nat} {k : LArg → LM LExpr}
    {n n' : Nat} {e : LExpr} {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64}
    {rtVal : BitVec 64} {vals : List (BitVec 64)}
    (hrun : (rtCall1 rtArg fn args resW k).run n = .ok (e, n'))
    (hrt : LArg.eval ρ i64 rtArg = some rtVal) (hnrt : argIdsBelow rtArg n)
    (hids : ∀ a ∈ args, argIdsBelow a n) (hevs : EvalRtArgs ρ args vals)
    {P : Post [i64]} {E : XPost}
    (hΓ : Γ fn (List.replicate (rtVal :: vals).length i64) [i64]
      (tupOfBV64s (rtVal :: vals)) mem P E)
    (hE : ∀ g cs ys m', E g cs ys m' → XT g cs ys m')
    (hk : ∀ (ret : BitVec 64) (m' : Mem 64), P (ret, ()) m' →
      ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (nr : Nat),
        n ≤ nr → (k r).run nr = .ok (ek, n') → argIdsBelow r nr →
        VEnvAgreeBelow n ρ' ρ →
        LArg.eval ρ' (Ty.bits resW) r = some (ret.setWidth resW) →
        LExpr.wp Γ QT XT ek ρ' J m') :
    LExpr.wp Γ QT XT e ρ J mem :=
  rtCall1_go_wp hrt hnrt args [] vals [] hrun hids hevs rfl
    (fun _ hp => by simp at hp) ⟨P, E, by simpa using hΓ, hE, hk⟩

theorem callFn_reg_wp {Γ : Env} {rs_ret : List Ty} {QT : Post rs_ret} {XT : XPost}
    {rtArg : LArg} {sym : Sym} {args : List (LArg × Ty)} {ret : Ty} {k : LArg → LM LExpr}
    {n n' : Nat} {e : LExpr} {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64}
    {rtVal : BitVec 64} {xs : Tup Val (args.map Prod.snd)}
    (hlen : args.length ≤ regArgs)
    (hrun : (callFn rtArg sym args ret k).run n = .ok (e, n'))
    (hrt : LArg.eval ρ i64 rtArg = some rtVal)
    (hev : evalArgs ρ (args.map Prod.snd) (args.map Prod.fst) = some xs)
    {P : Post [ret]} {E : XPost}
    (hΓ : Γ sym (i64 :: args.map Prod.snd) [ret] (rtVal, xs) mem P E)
    (hE : ∀ g cs ys m', E g cs ys m' → XT g cs ys m')
    (hk : ∀ (r : LArg) (ek : LExpr),
      (k r).run (n + 1) = .ok (ek, n') → argIdsBelow r (n + 1) →
      ∀ rv m', P (rv, ()) m' →
        VEnvAgreeBelow n (ρ.set n ret rv) ρ →
        LArg.eval (ρ.set n ret rv) ret r = some rv →
        LExpr.wp Γ QT XT ek (ρ.set n ret rv) J m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  unfold callFn at hrun
  have hnot : ¬ (args.length > regArgs + rtExtraSlots) := by unfold rtExtraSlots; omega
  rw [ite_eq_right hnot] at hrun
  have hdrop : args.drop regArgs = [] := List.drop_eq_nil_of_le hlen
  have htake : args.take regArgs = args := List.take_of_length_le hlen
  rw [hdrop, htake] at hrun
  change (call1 sym (i64 :: args.map Prod.snd) ret (rtArg :: args.map Prod.fst) k).run n =
      .ok (e, n') at hrun
  exact call1_wp hrun (evalArgs_cons hrt hev) hΓ hE hk

/-! ## 5. `LMMono` Monotonicity Lemmas -/

theorem op1_mono {t : Ty} {sig : List Ty} {code : OpCode sig [t]} {args : List LArg}
    {k : LArg → LM LExpr} (hk : ∀ a, LMMono (k a)) :
    LMMono (LeanLCNF.op1 t code args k) := by
  intro n e n' hrun
  unfold LeanLCNF.op1 at hrun
  rw [lm_bind_run] at hrun
  rcases hrun with ⟨v, n1, hv, hrest⟩
  rw [freshVar_run] at hv
  injection hv with hvp
  have hn1 : n1 = n + 1 := (congrArg Prod.snd hvp).symm
  subst hn1
  rw [lm_bind_run] at hrest
  rcases hrest with ⟨ek, n2, hek, hpure⟩
  rw [lm_pure_run] at hpure
  injection hpure with hpr
  have hn2 : n2 = n' := congrArg Prod.snd hpr
  subst hn2
  exact Nat.le_trans (Nat.le_succ n) (hk (vArg v) (n + 1) ek n2 hek)

theorem add64_mono {a b : LArg} {k : LArg → LM LExpr} (hk : ∀ r, LMMono (k r)) :
    LMMono (add64 a b k) := op1_mono hk

theorem sub64_mono {a b : LArg} {k : LArg → LM LExpr} (hk : ∀ r, LMMono (k r)) :
    LMMono (sub64 a b k) := op1_mono hk

theorem and64_mono {a b : LArg} {k : LArg → LM LExpr} (hk : ∀ r, LMMono (k r)) :
    LMMono (and64 a b k) := op1_mono hk

theorem or64_mono {a b : LArg} {k : LArg → LM LExpr} (hk : ∀ r, LMMono (k r)) :
    LMMono (or64 a b k) := op1_mono hk

theorem shl64_mono {a b : LArg} {k : LArg → LM LExpr} (hk : ∀ r, LMMono (k r)) :
    LMMono (shl64 a b k) := op1_mono hk

theorem lshr64_mono {a b : LArg} {k : LArg → LM LExpr} (hk : ∀ r, LMMono (k r)) :
    LMMono (lshr64 a b k) := op1_mono hk

theorem cmpOp_mono {o : CmpOp} {w : Nat} {a b : LArg} {k : LArg → LM LExpr}
    (hk : ∀ r, LMMono (k r)) : LMMono (cmpOp o w a b k) := op1_mono hk

theorem addrOf_mono {x : LArg} {off : Nat} {k : LArg → LM LExpr} (hk : ∀ a, LMMono (k a)) :
    LMMono (addrOf x off k) := by
  unfold addrOf
  split
  · exact hk x
  · exact add64_mono hk

theorem loadAt_mono {t : Ty} {x : LArg} {off : Nat} {k : LArg → LM LExpr}
    (hk : ∀ a, LMMono (k a)) : LMMono (loadAt t x off k) := by
  unfold loadAt
  refine addrOf_mono fun a n ek n' hrun => ?_
  rw [lm_bind_run] at hrun
  rcases hrun with ⟨v, n1, hv, hrest⟩
  rw [freshVar_run] at hv
  injection hv with hvp
  have hn1 : n1 = n + 1 := (congrArg Prod.snd hvp).symm
  subst hn1
  rw [lm_bind_run] at hrest
  rcases hrest with ⟨body, n2, hbody, hpure⟩
  rw [lm_pure_run] at hpure
  injection hpure with hpr
  have hn2 : n2 = n' := congrArg Prod.snd hpr
  subst hn2
  exact Nat.le_trans (Nat.le_succ n) (hk (vArg v) (n + 1) body n2 hbody)

theorem storeAt_mono {t : Ty} {v x : LArg} {off : Nat} {k : LM LExpr} (hk : LMMono k) :
    LMMono (storeAt t v x off k) := by
  unfold storeAt
  refine addrOf_mono fun a n ek n' hrun => ?_
  rw [lm_bind_run] at hrun
  rcases hrun with ⟨body, n1, hbody, hpure⟩
  rw [lm_pure_run] at hpure
  injection hpure with hpr
  have hn1 : n1 = n' := congrArg Prod.snd hpr
  subst hn1
  exact hk n body n1 hbody

theorem callN_mono {f : Sym} {as bs : List Ty} {args : List LArg}
    {k : List LArg → LM LExpr} (hk : ∀ rs, LMMono (k rs)) :
    LMMono (callN f as bs args k) := by
  intro n e n' hrun
  unfold callN at hrun
  rw [lm_bind_run] at hrun
  rcases hrun with ⟨pvs, n1, hpvs, hrest⟩
  simp only [mapM_freshVar_run, Except.ok.injEq, Prod.mk.injEq] at hpvs
  rcases hpvs with ⟨rfl, rfl⟩
  rw [lm_bind_run] at hrest
  rcases hrest with ⟨body, n2, hbody, hpure⟩
  rw [lm_pure_run] at hpure
  injection hpure with hpr
  have hn2 : n2 = n' := congrArg Prod.snd hpr
  subst hn2
  exact Nat.le_trans (Nat.le_add_right n bs.length) (hk _ (n + bs.length) body n2 hbody)

theorem call1_mono {f : Sym} {as : List Ty} {b : Ty} {args : List LArg}
    {k : LArg → LM LExpr} (hk : ∀ r, LMMono (k r)) : LMMono (call1 f as b args k) := by
  refine callN_mono fun rs => ?_
  cases rs with
  | nil => intro _ _ _ h; cases h
  | cons r rest => cases rest with
    | nil => exact hk r
    | cons _ _ => intro _ _ _ h; cases h

theorem call0_mono {f : Sym} {as : List Ty} {args : List LArg} {k : LM LExpr} (hk : LMMono k) :
    LMMono (call0 f as args k) := callN_mono fun _ => hk

theorem convW_mono {m w : Nat} {x : LArg} {k : LArg → LM LExpr} (hk : ∀ r, LMMono (k r)) :
    LMMono (convW m w x k) := by
  unfold convW
  split
  · exact hk x
  · split <;> exact op1_mono hk

theorem boxSmall_mono {x : LArg} {k : LArg → LM LExpr} (hk : ∀ r, LMMono (k r)) :
    LMMono (boxSmall x k) := shl64_mono fun _ => or64_mono hk

theorem boolToU8_mono {b : LArg} {k : LArg → LM LExpr} (hk : ∀ r, LMMono (k r)) :
    LMMono (boolToU8 b k) := op1_mono hk

theorem isScalarObj_mono {x : LArg} {k : LArg → LM LExpr} (hk : ∀ r, LMMono (k r)) :
    LMMono (LeanLCNF.isScalarObj x k) := and64_mono fun _ => cmpOp_mono hk

theorem withJoin_mono {ts : List Ty} {rest : List LArg → LM LExpr}
    {pre : (List LArg → LExpr) → LM LExpr}
    (hrest : ∀ args, LMMono (rest args)) (hpre : ∀ j, LMMono (pre j)) :
    LMMono (withJoin ts rest pre) := by
  intro n e n' hrun
  unfold withJoin at hrun
  rw [lm_bind_run] at hrun; rcases hrun with ⟨lbl, n1, hlbl, h1⟩
  rw [fresh_run] at hlbl; injection hlbl with hlp
  have hn1 : n1 = n + 1 := (congrArg Prod.snd hlp).symm; subst hn1
  rw [lm_bind_run] at h1; rcases h1 with ⟨ps, n2, hps, h2⟩
  simp only [mapM_freshVar_run, Except.ok.injEq, Prod.mk.injEq] at hps
  rcases hps with ⟨rfl, rfl⟩
  rw [lm_bind_run] at h2; rcases h2 with ⟨blk, n3, hblk, h3⟩
  rw [lm_bind_run] at h3; rcases h3 with ⟨body, n4, hbody, hpure⟩
  rw [lm_pure_run] at hpure; injection hpure with hpr
  have hn4 : n4 = n' := congrArg Prod.snd hpr; subst hn4
  exact Nat.le_trans (by omega : n ≤ n + 1 + ts.length)
    (Nat.le_trans (hrest _ (n + 1 + ts.length) blk n3 hblk)
      (hpre _ n3 body n4 hbody))

theorem withJoin1_mono {t : Ty} {rest : LArg → LM LExpr} {pre : (LArg → LExpr) → LM LExpr}
    (hrest : ∀ r, LMMono (rest r)) (hpre : ∀ j, LMMono (pre j)) :
    LMMono (withJoin1 t rest pre) := by
  refine withJoin_mono (fun args => ?_) (fun j => hpre fun r => j [r])
  cases args with
  | nil => intro _ _ _ h; cases h
  | cons r restArgs => cases restArgs with
    | nil => exact hrest r
    | cons _ _ => intro _ _ _ h; cases h

theorem rtCall1_go_mono {rtArg : LArg} {fn : Sym} {resW : Nat} {k : LArg → LM LExpr}
    (hk : ∀ r, LMMono (k r)) :
    ∀ rem acc, LMMono (rtCall1.go rtArg fn resW k rem acc)
  | [], _ => call1_mono fun _ => convW_mono hk
  | _ :: rest, acc => convW_mono fun a64 => rtCall1_go_mono hk rest (acc ++ [a64])

theorem rtCall1_mono {rtArg : LArg} {fn : Sym} {args : List LArg} {resW : Nat}
    {k : LArg → LM LExpr} (hk : ∀ r, LMMono (k r)) :
    LMMono (rtCall1 rtArg fn args resW k) :=
  rtCall1_go_mono hk args []

end LeanQbe.T.LeanLCNF.Sem
