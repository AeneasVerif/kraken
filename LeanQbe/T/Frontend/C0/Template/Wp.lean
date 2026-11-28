module

public import LeanQbe.T.Frontend.C0.Template.Snippet
public import LeanQbe.T.WP

/-!
# Weakest-Precondition Rules for C0 Template Combinators

Proves parametric WP composition rules once (`wp_materializeArg`, `wp_materializeArgs`,
`wp_c0UnrollK`, `wp_c0UnrollK_pure`, `wp_c0Unroll`, `wp_c0Unroll_pure`, `wp_exprBind`,
`wp_funcToExprSnippet`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Frontend.C0

open LeanQbe.T

/-- Weakest-precondition rule for `materializeArg`. -/
theorem wp_materializeArg {Γ : Env} {rs : List Ty} {t : Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} (a : Arg Val t) (k : Val t → LeanQbe.T.Expr Val Cont rs)
    (hk : wp Γ Q X (k a.val) m) :
    wp Γ Q X (materializeArg a k) m := by
  cases a with
  | var v => exact hk
  | imm c =>
    simp only [materializeArg, wp, Op.wp, OpCode.wp, vals, Arg.val]
    exact hk

/-- Weakest-precondition rule for `materializeArgs`. -/
theorem wp_materializeArgs {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64} :
    {ts : List Ty} → (args : Tup (Arg Val) ts) → (k : Tup Val ts → LeanQbe.T.Expr Val Cont rs) →
    wp Γ Q X (k (vals args)) m →
    wp Γ Q X (materializeArgs args k) m
  | [], (), k, hk => hk
  | _ :: _, (a, as), k, hk => by
    refine wp_materializeArg a _ ?_
    exact wp_materializeArgs as _ hk

/-- Parametric WP induction principle for `c0UnrollK` over an arbitrary Lean `List α`. -/
theorem wp_c0UnrollK {Γ : Env} {α : Type} {ts rs : List Ty} {Q : Post rs} {X : XPost}
    (xs : List α)
    (step : α → Tup Val ts → (Tup Val ts → LeanQbe.T.Expr Val Cont rs) →
      LeanQbe.T.Expr Val Cont rs)
    (Inv : List α → Tup Val ts → Mem 64 → Prop)
    (hstep : ∀ (x : α) (suf : List α) (st : Tup Val ts) (m : Mem 64)
      (k : Tup Val ts → LeanQbe.T.Expr Val Cont rs),
      (∀ st' m', Inv suf st' m' → wp Γ Q X (k st') m') →
      Inv (x :: suf) st m →
      wp Γ Q X (step x st k) m)
    (init : Tup Val ts) (m : Mem 64) (k : Tup Val ts → LeanQbe.T.Expr Val Cont rs)
    (hk : ∀ st' m', Inv [] st' m' → wp Γ Q X (k st') m')
    (hinit : Inv xs init m) :
    wp Γ Q X (c0UnrollK xs step init k) m := by
  induction xs generalizing init m with
  | nil => exact hk init m hinit
  | cons x rest ih =>
    dsimp only [c0UnrollK]
    exact hstep x rest init m _ (fun st' m' hmid => ih st' m' hmid) hinit

/-- Pure-state specialization of `wp_c0UnrollK` discharging any `xs : List α` via `List.foldl`. -/
theorem wp_c0UnrollK_pure {Γ : Env} {α : Type} {ts rs : List Ty} {Q : Post rs} {X : XPost}
    (xs : List α)
    (step : α → Tup Val ts → (Tup Val ts → LeanQbe.T.Expr Val Cont rs) →
      LeanQbe.T.Expr Val Cont rs)
    (f : Tup Val ts → α → Tup Val ts)
    (hstep : ∀ (x : α) (st : Tup Val ts) (m : Mem 64)
      (k : Tup Val ts → LeanQbe.T.Expr Val Cont rs),
      wp Γ Q X (k (f st x)) m → wp Γ Q X (step x st k) m)
    (init : Tup Val ts) (m : Mem 64) (k : Tup Val ts → LeanQbe.T.Expr Val Cont rs)
    (hk : wp Γ Q X (k (xs.foldl f init)) m) :
    wp Γ Q X (c0UnrollK xs step init k) m := by
  induction xs generalizing init with
  | nil => exact hk
  | cons x rest ih =>
    dsimp only [c0UnrollK]
    exact hstep x init m _ (ih (f init x) (by simpa [List.foldl_cons] using hk))

/-- Parametric WP induction principle for `c0Unroll` over an arbitrary Lean `List α`. -/
theorem wp_c0Unroll {Γ : Env} {α : Type} {ts rs : List Ty} {Q : Post rs} {X : XPost}
    (xs : List α) (step : α → C0StmtSnippet ts)
    (Inv : List α → Tup Val ts → Mem 64 → Prop)
    (hstep : ∀ (x : α) (suf : List α) (st : Tup Val ts) (m : Mem 64)
      (k : Tup Val ts → LeanQbe.T.Expr Val Cont rs),
      (∀ st' m', Inv suf st' m' → wp Γ Q X (k st') m') →
      Inv (x :: suf) st m →
      wp Γ Q X (step x Val Cont rs st k) m)
    (init : Tup Val ts) (m : Mem 64) (k : Tup Val ts → LeanQbe.T.Expr Val Cont rs)
    (hk : ∀ st' m', Inv [] st' m' → wp Γ Q X (k st') m')
    (hinit : Inv xs init m) :
    wp Γ Q X (c0Unroll xs step init k) m :=
  wp_c0UnrollK xs (fun x => step x Val Cont rs) Inv hstep init m k hk hinit

/-- Pure-state specialization of `wp_c0Unroll` discharging any `xs : List α` via `List.foldl`. -/
theorem wp_c0Unroll_pure {Γ : Env} {α : Type} {ts rs : List Ty} {Q : Post rs} {X : XPost}
    (xs : List α) (step : α → C0StmtSnippet ts) (f : Tup Val ts → α → Tup Val ts)
    (hstep : ∀ (x : α) (st : Tup Val ts) (m : Mem 64)
      (k : Tup Val ts → LeanQbe.T.Expr Val Cont rs),
      wp Γ Q X (k (f st x)) m → wp Γ Q X (step x Val Cont rs st k) m)
    (init : Tup Val ts) (m : Mem 64) (k : Tup Val ts → LeanQbe.T.Expr Val Cont rs)
    (hk : wp Γ Q X (k (xs.foldl f init)) m) :
    wp Γ Q X (c0Unroll xs step init k) m :=
  wp_c0UnrollK_pure xs (fun x => step x Val Cont rs) f hstep init m k hk

private theorem floatResultWp_mono (f : Fmt) (res : Float.Model.UnpackedFloat)
    {k k' : BitVec f.width → Prop} (hk : ∀ r, k r → k' r)
    (h : floatResultWp f res k) : floatResultWp f res k' := by
  by_cases hnan : res.isNaN <;> simp only [floatResultWp, hnan] at h ⊢
  · exact fun r hr => hk r (h r hr)
  · exact hk _ h

private theorem liftFloatRel1_mono
    (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    ∀ (t : Ty) (a : Val t) {k k' : Val t → Prop},
      (∀ r, k r → k' r) → liftFloatRel1 op t a k → liftFloatRel1 op t a k'
  | .float f, _, _, _, hk, h => floatResultWp_mono f _ hk h
  | .pair s u, a, _, _, hk, h =>
    liftFloatRel1_mono op s a.1 (fun r1 hr1 =>
      liftFloatRel1_mono op u a.2 (fun r2 hr2 => hk (r1, r2) hr2) hr1) h
  | .bool, _, _, _, _, h => False.elim h
  | .bits _, _, _, _, _, h => False.elim h

private theorem liftFloatRel2_mono
    (op : Float.Model.Format → Float.Model.UnpackedFloat →
      Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    ∀ (t : Ty) (a b : Val t) {k k' : Val t → Prop},
      (∀ r, k r → k' r) → liftFloatRel2 op t a b k → liftFloatRel2 op t a b k'
  | .float f, _, _, _, _, hk, h => floatResultWp_mono f _ hk h
  | .pair s u, a, b, _, _, hk, h =>
    liftFloatRel2_mono op s a.1 b.1 (fun r1 hr1 =>
      liftFloatRel2_mono op u a.2 b.2 (fun r2 hr2 => hk (r1, r2) hr2) hr1) h
  | .bool, _, _, _, _, _, h => False.elim h
  | .bits _, _, _, _, _, _, h => False.elim h

private theorem liftFloatRel3_mono
    (op : Float.Model.Format → Float.Model.UnpackedFloat →
      Float.Model.UnpackedFloat → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    ∀ (t : Ty) (a b c : Val t) {k k' : Val t → Prop},
      (∀ r, k r → k' r) → liftFloatRel3 op t a b c k → liftFloatRel3 op t a b c k'
  | .float f, _, _, _, _, _, hk, h => floatResultWp_mono f _ hk h
  | .pair s u, a, b, c, _, _, hk, h =>
    liftFloatRel3_mono op s a.1 b.1 c.1 (fun r1 hr1 =>
      liftFloatRel3_mono op u a.2 b.2 c.2 (fun r2 hr2 => hk (r1, r2) hr2) hr1) h
  | .bool, _, _, _, _, _, _, h => False.elim h
  | .bits _, _, _, _, _, _, _, h => False.elim h

private theorem convertFloat_mono (src dst : Fmt) (b : BitVec src.width)
    {k k' : BitVec dst.width → Prop} (hk : ∀ r, k r → k' r)
    (h : convertFloat src dst b k) : convertFloat src dst b k' := by
  dsimp only [convertFloat] at *
  cases hu : unpackFloat src b with
  | notANumber =>
    rw [hu] at h
    exact fun r hr => hk r (h r hr)
  | finite _ _ _ _ => rw [hu] at h; exact hk _ h
  | zero _ => rw [hu] at h; exact hk _ h
  | infinity _ => rw [hu] at h; exact hk _ h

private theorem ite_false_mono {b : Bool} {A B : Prop} (hab : A → B) :
    (if b then False else A) → (if b then False else B) := by
  cases b <;> intro h
  · exact hab h
  · exact False.elim h

private theorem opCode_wp_mono :
    {sig rs : List Ty} → (c : OpCode sig rs) → (xs : Tup Val sig) →
    {P Q : Tup Val rs → Prop} → (∀ r, P r → Q r) → OpCode.wp c xs P → OpCode.wp c xs Q
  | _, _, .copy _, (_, ()), _, _, h, hp => h _ hp
  | _, _, .add _, (_, _, ()), _, _, h, hp => ite_false_mono (h _) hp
  | _, _, .sub _, (_, _, ()), _, _, h, hp => ite_false_mono (h _) hp
  | _, _, .mul _, (_, _, ()), _, _, h, hp => ite_false_mono (h _) hp
  | _, _, .neg _, (_, ()), _, _, h, hp => ite_false_mono (h _) hp
  | _, _, .and _, (_, _, ()), _, _, h, hp => h _ hp
  | _, _, .or _, (_, _, ()), _, _, h, hp => h _ hp
  | _, _, .xor _, (_, _, ()), _, _, h, hp => h _ hp
  | _, _, .not _, (_, ()), _, _, h, hp => h _ hp
  | _, _, .ternlog _ _, (_, _, _, ()), _, _, h, hp => h _ hp
  | _, _, .shl _, (_, _, ()), _, _, h, hp => ite_false_mono (h _) hp
  | _, _, .lshr _, (_, _, ()), _, _, h, hp => ite_false_mono (h _) hp
  | _, _, .ashr _, (_, _, ()), _, _, h, hp => ite_false_mono (h _) hp
  | _, _, .rotl _, (_, _, ()), _, _, h, hp => ite_false_mono (h _) hp
  | _, _, .rotr _, (_, _, ()), _, _, h, hp => ite_false_mono (h _) hp
  | _, _, .fshl _, (_, _, _, ()), _, _, h, hp => h _ hp
  | _, _, .fshr _, (_, _, _, ()), _, _, h, hp => h _ hp
  | _, _, .bswap _, (_, ()), _, _, h, hp => ite_false_mono (h _) hp
  | _, _, .clz _, (_, ()), _, _, h, hp => h _ hp
  | _, _, .cls _, (_, ()), _, _, h, hp => h _ hp
  | _, _, .rbit _, (_, ()), _, _, h, hp => h _ hp
  | _, _, .ctz _, (_, ()), _, _, h, hp => h _ hp
  | _, _, .popcnt _, (_, ()), _, _, h, hp => h _ hp
  | _, _, .cmp _ _ _ rfl, (_, _, ()), _, _, h, hp => ite_false_mono (h _) hp
  | _, _, .select _, (_, _, _, ()), _, _, h, hp => h _ hp
  | _, _, .blend _ _ rfl, (_, _, _, ()), _, _, h, hp => h _ hp
  | _, _, .zext _ _, (_, ()), _, _, h, hp => ⟨hp.1, h _ hp.2⟩
  | _, _, .sext _ _, (_, ()), _, _, h, hp => ⟨hp.1, h _ hp.2⟩
  | _, _, .trunc _ _, (_, ()), _, _, h, hp => ⟨hp.1, h _ hp.2⟩
  | _, _, .ofBool _, (_, ()), _, _, h, hp => h _ hp
  | _, _, .addc _, (_, _, _, ()), _, _, h, hp => h _ hp
  | _, _, .subb _, (_, _, _, ()), _, _, h, hp => h _ hp
  | _, _, .umulw _, (_, _, ()), _, _, h, hp => h _ hp
  | _, _, .smulw _, (_, _, ()), _, _, h, hp => h _ hp
  | _, _, .udiv _, (_, _, ()), _, _, h, hp => ⟨hp.1, h _ hp.2⟩
  | _, _, .sdiv _, (_, _, ()), _, _, h, hp => ⟨hp.1, h _ hp.2⟩
  | _, _, .urem _, (_, _, ()), _, _, h, hp => ⟨hp.1, h _ hp.2⟩
  | _, _, .srem _, (_, _, ()), _, _, h, hp => ⟨hp.1, h _ hp.2⟩
  | _, _, .udiv0 _, (_, _, ()), _, _, h, hp => h _ hp
  | _, _, .sdiv0 _, (_, _, ()), _, _, h, hp => h _ hp
  | _, _, .mkpair _ _, (_, _, ()), _, _, h, hp => h _ hp
  | _, _, .unpair _ _, (_, ()), _, _, h, hp => h _ hp
  | _, _, .bitcast _ _ _, (_, ()), _, _, h, hp => h _ hp
  | _, _, .shufd _ _, (_, ()), _, _, h, hp => ⟨hp.1, hp.2.1, h _ hp.2.2⟩
  | _, _, .shufb _, (_, _, ()), _, _, h, hp => ⟨hp.1, hp.2.1, h _ hp.2.2⟩
  | _, _, .alignr _ _, (_, _, ()), _, _, h, hp => ⟨hp.1, hp.2.1, h _ hp.2.2⟩
  | _, _, .blendw _ _, (_, _, ()), _, _, h, hp => ⟨hp.1, hp.2.1, h _ hp.2.2⟩
  | _, _, .sha256rnds2, (_, _, _, ()), _, _, h, hp => h _ hp
  | _, _, .sha256msg1, (_, _, ()), _, _, h, hp => h _ hp
  | _, _, .sha256msg2, (_, _, ()), _, _, h, hp => h _ hp
  | _, _, .fadd t, (a, b, ()), _, _, h, hp =>
    ite_false_mono (liftFloatRel2_mono _ t a b (fun r hr => h (r, ()) hr)) hp
  | _, _, .fsub t, (a, b, ()), _, _, h, hp =>
    ite_false_mono (liftFloatRel2_mono _ t a b (fun r hr => h (r, ()) hr)) hp
  | _, _, .fmul t, (a, b, ()), _, _, h, hp =>
    ite_false_mono (liftFloatRel2_mono _ t a b (fun r hr => h (r, ()) hr)) hp
  | _, _, .fdiv t, (a, b, ()), _, _, h, hp =>
    ite_false_mono (liftFloatRel2_mono _ t a b (fun r hr => h (r, ()) hr)) hp
  | _, _, .ffma t, (a, b, c0, ()), _, _, h, hp =>
    ite_false_mono (liftFloatRel3_mono _ t a b c0 (fun r hr => h (r, ()) hr)) hp
  | _, _, .fsqrt t, (a, ()), _, _, h, hp =>
    ite_false_mono (liftFloatRel1_mono _ t a (fun r hr => h (r, ()) hr)) hp
  | _, _, .fneg _, (_, ()), _, _, h, hp => ite_false_mono (h _) hp
  | _, _, .fabs _, (_, ()), _, _, h, hp => ite_false_mono (h _) hp
  | _, _, .fcmp _ _ _ rfl, (_, _, ()), _, _, h, hp => ite_false_mono (h _) hp
  | _, _, .fptoui f _, (a, ()), _, _, h, hp => by
    dsimp only [OpCode.wp] at hp ⊢
    cases hm : truncToInt (unpackFloat f a) with
    | none => rw [hm] at hp; exact False.elim hp
    | some z => rw [hm] at hp; exact ⟨hp.1, hp.2.1, h _ hp.2.2⟩
  | _, _, .fptosi f _, (a, ()), _, _, h, hp => by
    dsimp only [OpCode.wp] at hp ⊢
    refine ⟨hp.1, ?_⟩
    have hp2 := hp.2
    cases hm : truncToInt (unpackFloat f a) with
    | none => rw [hm] at hp2; exact False.elim hp2
    | some z => rw [hm] at hp2; exact ⟨hp2.1, hp2.2.1, h _ hp2.2.2⟩
  | _, _, .uitofp _ _, (_, ()), _, _, h, hp => h _ hp
  | _, _, .sitofp _ _, (_, ()), _, _, h, hp => h _ hp
  | _, _, .fcvt f g, (a, ()), _, _, h, hp => convertFloat_mono f g a (fun r hr => h (r, ()) hr) hp

private theorem op_wp_mono {rs : List Ty} (op : Op Val rs) {P Q : Tup Val rs → Prop}
    (h : ∀ r, P r → Q r) (hp : Op.wp op P) : Op.wp op Q :=
  opCode_wp_mono op.code (vals op.args) h hp

private theorem op_wp_iff {rs : List Ty} (op : Op Val rs) {P Q : Tup Val rs → Prop}
    (h : ∀ r, P r ↔ Q r) : Op.wp op P ↔ Op.wp op Q :=
  ⟨op_wp_mono op fun r hr => (h r).mp hr, op_wp_mono op fun r hr => (h r).mpr hr⟩

private theorem wp_exprBind_aux {Γ : Env} {as bs : List Ty} {Q : Post bs} {X : XPost}
    (k : Tup (Arg Val) as → LeanQbe.T.Expr Val Cont bs)
    (hk_ext : ∀ (a₁ a₂ : Tup (Arg Val) as), vals a₁ = vals a₂ → ∀ m,
      wp Γ Q X (k a₁) m → wp Γ Q X (k a₂) m) :
    (∀ (e : LeanQbe.T.Expr Val Cont as) (m : Mem 64),
      wp Γ (fun vs m' => ∀ a : Tup (Arg Val) as, vals a = vs → wp Γ Q X (k a) m') X e m ↔
      wp Γ Q X (exprBind e k) m) ∧
    (∀ {sig : List (List Ty)} (blks : LeanQbe.T.Blocks Val Cont as sig) (js : Tup Cont sig),
      Closed Γ (fun vs m' => ∀ a : Tup (Arg Val) as, vals a = vs → wp Γ Q X (k a) m') X
        blks js ↔
      Closed Γ Q X (blocksBind blks k) js) := by
  let P0 : Post as := fun vs m' => ∀ a : Tup (Arg Val) as, vals a = vs → wp Γ Q X (k a) m'
  let M1 (e : LeanQbe.T.Expr Val Cont as) : Prop :=
    ∀ m, wp Γ P0 X e m ↔ wp Γ Q X (exprBind e k) m
  let M2 {sig : List (List Ty)} (blks : LeanQbe.T.Blocks Val Cont as sig) : Prop :=
    ∀ js : Tup Cont sig, Closed Γ P0 X blks js ↔ Closed Γ Q X (blocksBind blks k) js
  have c_let : ∀ {ts} (op : Op Val ts) cont, (∀ r, M1 (cont r)) → M1 (.let_ op cont) := by
    intro ts op cont ih m
    exact op_wp_iff op fun r => ih r m
  have c_load : ∀ t a cont, (∀ v, M1 (cont v)) → M1 (.load t a cont) := by
    intro t a cont ih m
    simp only [wp, exprBind]
    exact exists_congr fun v => and_congr_right fun _ => ih v m
  have c_store : ∀ {t} v a cont, M1 cont → M1 (.store (t := t) v a cont) := by
    intro t v a cont ih m
    simp only [wp, exprBind]
    exact and_congr_right fun _ => ih _
  have c_call : ∀ f {as' bs'} args cont, (∀ r, M1 (cont r)) →
      M1 (.call f (as := as') (bs := bs') args cont) := by
    intro f as' bs' args cont ih m
    simp only [wp, exprBind]
    exact exists_congr fun R => exists_congr fun E =>
      and_congr_right fun _ => and_congr (forall_congr' fun r => forall_congr' fun m' =>
        imp_congr_right fun _ => ih r m') Iff.rfl
  have c_jnz : ∀ c t e, M1 t → M1 e → M1 (.jnz c t e) := by
    intro c t e iht ihe m
    simp only [wp, exprBind]
    exact and_congr (imp_congr_right fun _ => iht m) (imp_congr_right fun _ => ihe m)
  have c_jump : ∀ {ts} j args, M1 (.jump (ts := ts) j args) := by
    intro ts j args m; rfl
  have c_ret : ∀ vs, M1 (.ret vs) := by
    intro vs m
    simp only [wp, exprBind]
    exact ⟨fun h => h vs rfl, fun h a ha => hk_ext vs a ha.symm m h⟩
  have c_exit : ∀ (f : Sym) {as'} args, M1 (.exit f (as := as') args) := by
    intro f as' args m; rfl
  have c_hlt : M1 .hlt := by
    intro m; rfl
  have c_group : ∀ {sig} bodies entry, (∀ js, M2 (bodies js)) → (∀ js, M1 (entry js)) →
      M1 (.group (sig := sig) bodies entry) := by
    intro sig bodies entry ihb ihe m
    simp only [wp, exprBind]
    exact forall_congr' fun js => imp_congr (ihb js js) (ihe js m)
  have c_nil : M2 .nil := fun _ => Iff.rfl
  have c_cons : ∀ {ts sig} b bs, (∀ xs, M1 (b xs)) → M2 bs →
      M2 (.cons (ts := ts) (sig := sig) b bs) := by
    intro ts sig b bs ihb ihbs js
    simp only [Closed, blocksBind]
    exact and_congr
      (forall_congr' fun xs => forall_congr' fun m => imp_congr_left (ihb xs m))
      (ihbs js.2)
  exact ⟨
    LeanQbe.T.Expr.rec c_let c_load c_store c_call c_jnz c_jump c_ret c_exit c_hlt c_group
      c_nil c_cons,
    fun {sig} blks =>
      LeanQbe.T.Blocks.rec c_let c_load c_store c_call c_jnz c_jump c_ret c_exit c_hlt c_group
        c_nil c_cons blks⟩

/-- Composition WP rule for `exprBind`. -/
theorem wp_exprBind {Γ : Env} {as bs : List Ty} {Q : Post bs} {X : XPost} {m : Mem 64}
    (e : LeanQbe.T.Expr Val Cont as) (k : Tup (Arg Val) as → LeanQbe.T.Expr Val Cont bs)
    (hk_ext : ∀ (a₁ a₂ : Tup (Arg Val) as), vals a₁ = vals a₂ → ∀ m',
      wp Γ Q X (k a₁) m' → wp Γ Q X (k a₂) m')
    (h : wp Γ (fun vs m' => ∀ a : Tup (Arg Val) as, vals a = vs → wp Γ Q X (k a) m') X e m) :
    wp Γ Q X (exprBind e k) m :=
  ((wp_exprBind_aux k hk_ext).1 e m).mp h

/-- Composition WP rule for `funcToExprSnippet`. -/
theorem wp_funcToExprSnippet {Γ : Env} {as rs : List Ty} {r : Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} (f : Func as [r]) (args : Tup (Arg Val) as)
    (k : Val r → LeanQbe.T.Expr Val Cont rs)
    (h : Func.wp Γ f (vals args) m (fun (v, ()) m' => wp Γ Q X (k v) m') X) :
    wp Γ Q X (funcToExprSnippet f Val Cont rs args k) m := by
  refine wp_materializeArgs args _ ?_
  refine wp_exprBind (f Val Cont (vals args)) _ ?_ ?_
  · rintro ⟨a₁, ⟨⟩⟩ ⟨a₂, ⟨⟩⟩ hvs m' h1
    have hv : a₁.val = a₂.val := congrArg Prod.fst hvs
    have heq : ∀ (x : Arg Val r) m0,
        wp Γ Q X (materializeArg x k) m0 ↔ wp Γ Q X (k x.val) m0 := by
      intro x m0
      cases x <;> simp [materializeArg, wp, Op.wp, OpCode.wp, vals, Arg.val]
    exact (heq a₂ m').mpr (hv ▸ (heq a₁ m').mp h1)
  · refine wp_mono_post (f Val Cont (vals args)) h ?_
    rintro ⟨v, ⟨⟩⟩ m' hk ⟨a, ⟨⟩⟩ ha
    have hva : a.val = v := congrArg Prod.fst ha
    exact wp_materializeArg a k (hva ▸ hk)
where
  wp_mono_post {Γ : Env} {rs : List Ty} {P P' : Post rs} {X : XPost}
      (e : LeanQbe.T.Expr Val Cont rs) {m : Mem 64}
      (h : wp Γ P X e m) (hmono : ∀ vs m', P vs m' → P' vs m') : wp Γ P' X e m := by
    let M1 (P1 P2 : Post rs) (e1 : LeanQbe.T.Expr Val Cont rs) : Prop :=
      ∀ m1, (∀ vs m', P1 vs m' → P2 vs m') → wp Γ P1 X e1 m1 → wp Γ P2 X e1 m1
    let M2 (P1 P2 : Post rs) (sig : List (List Ty)) (blks : LeanQbe.T.Blocks Val Cont rs sig) :
        Prop :=
      ∀ js : Tup Cont sig, (∀ vs m', P1 vs m' → P2 vs m') →
        Closed Γ P2 X blks js → Closed Γ P1 X blks js
    have c_let : ∀ {P1 P2} {ts} (op : Op Val ts) cont,
        (∀ r, M1 P1 P2 (cont r)) → M1 P1 P2 (.let_ op cont) := by
      intro P1 P2 ts op cont ih m1 hm hp
      exact op_wp_mono op (fun r hr => ih r m1 hm hr) hp
    have c_load : ∀ {P1 P2} t a cont, (∀ v, M1 P1 P2 (cont v)) → M1 P1 P2 (.load t a cont) := by
      intro P1 P2 t a cont ih m1 hm ⟨v, hld, hc⟩
      exact ⟨v, hld, ih v m1 hm hc⟩
    have c_store : ∀ {P1 P2} {t} v a cont, M1 P1 P2 cont → M1 P1 P2 (.store (t := t) v a cont) := by
      intro P1 P2 t v a cont ih m1 hm ⟨hok, hc⟩
      exact ⟨hok, ih _ hm hc⟩
    have c_call : ∀ {P1 P2} f {as' bs'} args cont, (∀ r, M1 P1 P2 (cont r)) →
        M1 P1 P2 (.call f (as := as') (bs := bs') args cont) := by
      intro P1 P2 f as' bs' args cont ih m1 hm ⟨R, E, hcall, hc, hex⟩
      exact ⟨R, E, hcall, fun r m' hr => ih r m' hm (hc r m' hr), hex⟩
    have c_jnz : ∀ {P1 P2} c t e1, M1 P1 P2 t → M1 P1 P2 e1 → M1 P1 P2 (.jnz c t e1) := by
      intro P1 P2 c t e1 iht ihe m1 hm ⟨ht, he1⟩
      exact ⟨fun h1 => iht m1 hm (ht h1), fun h2 => ihe m1 hm (he1 h2)⟩
    have c_jump : ∀ {P1 P2} {ts} j args, M1 P1 P2 (.jump (ts := ts) j args) := by
      intro P1 P2 ts j args m1 hm h1; exact h1
    have c_ret : ∀ {P1 P2} vs, M1 P1 P2 (.ret vs) := by
      intro P1 P2 vs m1 hm h1; exact hm (vals vs) _ h1
    have c_exit : ∀ {P1 P2} (f : Sym) {as'} args, M1 P1 P2 (.exit f (as := as') args) := by
      intro P1 P2 f as' args m1 hm h1; exact h1
    have c_hlt : ∀ {P1 P2}, M1 P1 P2 .hlt := by
      intro P1 P2 m1 hm h1; exact h1
    have c_group : ∀ {P1 P2} {sig} bodies entry, (∀ js, M2 P1 P2 sig (bodies js)) →
        (∀ js, M1 P1 P2 (entry js)) → M1 P1 P2 (.group (sig := sig) bodies entry) := by
      intro P1 P2 sig bodies entry ihb ihe m1 hm h1 js hc
      exact ihe js m1 hm (h1 js (ihb js js hm hc))
    have c_nil : ∀ {P1 P2}, M2 P1 P2 [] .nil := fun _ _ _ => trivial
    have c_cons : ∀ {P1 P2} {ts sig} b bs, (∀ xs, M1 P1 P2 (b xs)) → M2 P1 P2 sig bs →
        M2 P1 P2 (ts :: sig) (.cons (ts := ts) (sig := sig) b bs) := by
      intro P1 P2 ts sig b bs ihb ihbs js hm ⟨hb, hbs⟩
      exact ⟨fun xs m' h2 => hb xs m' (ihb xs m' hm h2), ihbs js.2 hm hbs⟩
    exact LeanQbe.T.Expr.rec (motive_1 := M1 P P') (motive_2 := M2 P P')
      (c_let (P1 := P) (P2 := P')) (c_load (P1 := P) (P2 := P'))
      (c_store (P1 := P) (P2 := P')) (c_call (P1 := P) (P2 := P'))
      (c_jnz (P1 := P) (P2 := P')) (c_jump (P1 := P) (P2 := P'))
      (c_ret (P1 := P) (P2 := P')) (c_exit (P1 := P) (P2 := P'))
      (c_hlt (P1 := P) (P2 := P')) (c_group (P1 := P) (P2 := P'))
      (c_nil (P1 := P) (P2 := P')) (c_cons (P1 := P) (P2 := P')) e m hmono h


end LeanQbe.T.Frontend.C0

end
