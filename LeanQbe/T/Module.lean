module

public import LeanQbe.T.WP
public import LeanQbe.T.Wf

/-!
# Typed IR modules, acyclic `ModuleOk`, and `Env.ofModule`

100%-PHOAS module representation (`Module := {fns, externs, exits}`), acyclic callees-first
`ModuleOk Γ M` (acyclic modules; cyclic recursion is handled separately in `LinkRec`/`LinkScc`),
`wp_env_agree_of_callsOk` via `Wf.induct`, and `Env.ofModule` with signature-isolation lemmas
preventing colliding-signature hazards in `legalEnv`.
-/

set_option autoImplicit false
@[expose] public section
namespace LeanQbe.T

structure Extern where
  name : Sym
  as : List Ty
  rs : List Ty
  deriving DecidableEq, Repr

structure Module where
  fns : List Fn
  externs : List Extern := []
  exits : List Sym := []

abbrev SigEntry := Sym × List Ty × List Ty
def Fn.sig (fn : Fn) : SigEntry := (fn.name, fn.as, fn.rs)
def Extern.sig (ex : Extern) : SigEntry := (ex.name, ex.as, ex.rs)
def Module.sigs (M : Module) : List SigEntry := M.fns.map Fn.sig ++ M.externs.map Extern.sig
def Module.names (M : Module) : List Sym := M.fns.map Fn.name ++ M.externs.map Extern.name
def Module.namesNodup (M : Module) : Prop := M.names.Nodup

mutual
def Expr.callsOk (allowed : List SigEntry) (exits : List Sym) {rs : List Ty} :
    Expr (fun _ => Unit) (fun _ => Unit) rs → Prop
  | .let_ _ k => (k (Tup.units _)).callsOk allowed exits
  | .load _ _ k => (k ()).callsOk allowed exits
  | .store _ _ k => k.callsOk allowed exits
  | .call f (as := as) (bs := bs) _ k => (f, as, bs) ∈ allowed ∧ (k (Tup.units bs)).callsOk allowed exits
  | .jnz _ t e => t.callsOk allowed exits ∧ e.callsOk allowed exits
  | .jump _ _ | .ret _ | .hlt => True
  | .exit f _ => f ∈ exits
  | .group (sig := sig) bodies k =>
      (bodies (Tup.units sig)).callsOk allowed exits ∧ (k (Tup.units sig)).callsOk allowed exits

def Blocks.callsOk (allowed : List SigEntry) (exits : List Sym) {rs : List Ty} :
    {sig : List (List Ty)} → Blocks (fun _ => Unit) (fun _ => Unit) rs sig → Prop
  | _, .nil => True
  | _, .cons b bs => (b (Tup.units _)).callsOk allowed exits ∧ bs.callsOk allowed exits
end

def Fn.callsOk (allowed : List SigEntry) (exits : List Sym) (fn : Fn) : Prop :=
  (fn.body (fun _ => Unit) (fun _ => Unit) (Tup.units fn.as)).callsOk allowed exits

theorem Blocks.callsOk_get {allowed : List SigEntry} {exits : List Sym} {rs : List Ty} :
    {sig : List (List Ty)} → {bs : Blocks (fun _ => Unit) (fun _ => Unit) rs sig} →
    bs.callsOk allowed exits → ∀ {ts} (i : Member ts sig), (bs.get i (Tup.units ts)).callsOk allowed exits
  | _, .cons _ _, h, _, .here => h.1
  | _, .cons _ _, h, _, .there i => Blocks.callsOk_get h.2 i

private theorem floatResultWp_mono {f : Fmt} {res : Float.Model.UnpackedFloat}
    {p q : BitVec f.width → Prop} (h : ∀ r, p r → q r) :
    floatResultWp f res p → floatResultWp f res q := by
  unfold floatResultWp; split
  · exact fun hp r hr => h r (hp r hr)
  · exact h _

private theorem liftFloatRel1_mono (op : Float.Model.Format → Float.Model.UnpackedFloat →
      Float.Model.UnpackedFloat) :
    ∀ (t : Ty) (a : Val t) (p q : Val t → Prop), (∀ r, p r → q r) →
      liftFloatRel1 op t a p → liftFloatRel1 op t a q
  | .float _, _, _, _, h, hp => floatResultWp_mono h hp
  | .pair s u, a, _, _, h, hp =>
      liftFloatRel1_mono op s a.1 _ _
        (fun r1 => liftFloatRel1_mono op u a.2 _ _ (fun r2 => h (r1, r2))) hp
  | .bool, _, _, _, _, hp => hp
  | .bits _, _, _, _, _, hp => hp

private theorem liftFloatRel2_mono (op : Float.Model.Format → Float.Model.UnpackedFloat →
      Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    ∀ (t : Ty) (a b : Val t) (p q : Val t → Prop), (∀ r, p r → q r) →
      liftFloatRel2 op t a b p → liftFloatRel2 op t a b q
  | .float _, _, _, _, _, h, hp => floatResultWp_mono h hp
  | .pair s u, a, b, _, _, h, hp =>
      liftFloatRel2_mono op s a.1 b.1 _ _
        (fun r1 => liftFloatRel2_mono op u a.2 b.2 _ _ (fun r2 => h (r1, r2))) hp
  | .bool, _, _, _, _, _, hp => hp
  | .bits _, _, _, _, _, _, hp => hp

private theorem liftFloatRel3_mono (op : Float.Model.Format → Float.Model.UnpackedFloat →
      Float.Model.UnpackedFloat → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    ∀ (t : Ty) (a b c : Val t) (p q : Val t → Prop), (∀ r, p r → q r) →
      liftFloatRel3 op t a b c p → liftFloatRel3 op t a b c q
  | .float _, _, _, _, _, _, h, hp => floatResultWp_mono h hp
  | .pair s u, a, b, c, _, _, h, hp =>
      liftFloatRel3_mono op s a.1 b.1 c.1 _ _
        (fun r1 => liftFloatRel3_mono op u a.2 b.2 c.2 _ _ (fun r2 => h (r1, r2))) hp
  | .bool, _, _, _, _, _, _, hp => hp
  | .bits _, _, _, _, _, _, _, hp => hp

private theorem convertFloat_mono {src dst : Fmt} {b : BitVec src.width}
    {p q : BitVec dst.width → Prop} (h : ∀ r, p r → q r) :
    convertFloat src dst b p → convertFloat src dst b q := by
  delta convertFloat
  cases unpackFloat src b with
  | notANumber => exact fun hp r hr => h r (hp r hr)
  | finite _ _ _ _ => exact h _
  | _ => exact h _

private theorem opCode_wp_mono {as rs : List Ty} (c : OpCode as rs) (args : Tup Val as)
    {p q : Tup Val rs → Prop} (h : ∀ r, p r → q r) (hp : c.wp args p) : c.wp args q := by
  cases c
  all_goals
    try cases ‹_ = Ty.mask _›
    try obtain ⟨_, _, _, ⟨⟩⟩ := args
    try obtain ⟨_, _, ⟨⟩⟩ := args
    try obtain ⟨_, ⟨⟩⟩ := args
    delta OpCode.wp at hp ⊢
    dsimp only at hp ⊢
    try (split <;> simp only [*] at hp)
  all_goals
    first
      | exact False.elim hp
      | exact False.elim hp.2
      | exact h _ hp
      | exact ⟨hp.1, h _ hp.2⟩
      | exact ⟨hp.1, hp.2.1, h _ hp.2.2⟩
      | exact ⟨hp.1, hp.2.1, hp.2.2.1, h _ hp.2.2.2⟩
      | exact liftFloatRel1_mono _ _ _ _ _ (fun _ => h _) hp
      | exact liftFloatRel2_mono _ _ _ _ _ _ (fun _ => h _) hp
      | exact liftFloatRel3_mono _ _ _ _ _ _ _ (fun _ => h _) hp
      | exact convertFloat_mono (fun _ => h _) hp

mutual
theorem wp_env_agree_of_callsOk {Γ Γ' : Env} {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} {Q : Post rs} {X : XPost} {G : Ctx Val (fun _ => Unit)}
    {D : Ctx Cont (fun _ => Unit)}
    {e₁ : Expr Val Cont rs} {e₂ : Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hwf : Wf G D e₁ e₂) (hcalls : e₂.callsOk allowed exits)
    (hΓ : ∀ f as bs, (f, as, bs) ∈ allowed →
      ∀ xs m P E, Γ f as bs xs m P E → Γ' f as bs xs m P E) :
    ∀ m, wp Γ Q X e₁ m → wp Γ' Q X e₁ m := by
  cases hwf with
  | let_ _ hk =>
    intro m h
    exact opCode_wp_mono _ _
      (fun r => wp_env_agree_of_callsOk (hk r (Tup.units _)) hcalls hΓ m) h
  | load _ _ hk =>
    intro m ⟨v, hv, h⟩
    exact ⟨v, hv, wp_env_agree_of_callsOk (hk v ()) hcalls hΓ m h⟩
  | store _ _ hk =>
    intro m ⟨hok, h⟩
    exact ⟨hok, wp_env_agree_of_callsOk hk hcalls hΓ _ h⟩
  | call f _ hk =>
    intro m ⟨P, E, hG, hP, hE⟩
    exact ⟨P, E, hΓ f _ _ hcalls.1 _ m P E hG,
      fun r m' hr =>
        wp_env_agree_of_callsOk (hk r (Tup.units _)) hcalls.2 hΓ m' (hP r m' hr), hE⟩
  | jnz _ ht he =>
    intro m h
    exact ⟨fun hc => wp_env_agree_of_callsOk ht hcalls.1 hΓ m (h.1 hc),
      fun hc => wp_env_agree_of_callsOk he hcalls.2 hΓ m (h.2 hc)⟩
  | jump _ _ | ret _ | exit _ _ | hlt => intro _ h; exact h
  | group hb hk =>
    intro m h Js hc
    exact wp_env_agree_of_callsOk (hk Js (Tup.units _)) hcalls.2 hΓ m
      (h Js (closed_env_agree_of_callsOk (hb Js (Tup.units _)) hcalls.1 hΓ hc))

private theorem closed_env_agree_of_callsOk {Γ Γ' : Env} {allowed : List SigEntry}
    {exits : List Sym} {rs : List Ty} {Q : Post rs} {X : XPost} {G : Ctx Val (fun _ => Unit)}
    {D : Ctx Cont (fun _ => Unit)}
    {sig : List (List Ty)} {bs₁ : Blocks Val Cont rs sig}
    {bs₂ : Blocks (fun _ => Unit) (fun _ => Unit) rs sig}
    (hwfb : WfB G D bs₁ bs₂) (hcalls : bs₂.callsOk allowed exits)
    (hΓ : ∀ f as bs, (f, as, bs) ∈ allowed →
      ∀ xs m P E, Γ f as bs xs m P E → Γ' f as bs xs m P E)
    {Js : Tup Cont sig} (hc : Closed Γ' Q X bs₁ Js) :
    Closed Γ Q X bs₁ Js := by
  cases hwfb with
  | nil => trivial
  | cons hbh hbs =>
    exact ⟨fun xs m hwp =>
        hc.1 xs m (wp_env_agree_of_callsOk (hbh xs (Tup.units _)) hcalls.1 hΓ m hwp),
      closed_env_agree_of_callsOk hbs hcalls.2 hΓ hc.2⟩
end

def Env.restrict (Γ : Env) (allowed : List SigEntry) : Env :=
  fun f as bs xs m Q X => (f, as, bs) ∈ allowed ∧ Γ f as bs xs m Q X

def Env.ofModule (M : Module) (Γ : Env) : Env := Env.restrict Γ M.sigs

structure ModuleOk (Γ : Env) (M : Module) : Prop where
  nodup : M.namesNodup
  fnsOk : ∀ pre fn post, M.fns = pre ++ fn :: post →
    fn.Wf ∧ fn.callsOk (pre.map Fn.sig ++ M.externs.map Extern.sig) M.exits ∧
      ∀ xs m Q X, Γ fn.name fn.as fn.rs xs m Q X → Func.wp Γ fn.body xs m Q X

theorem ModuleOk.wp_restrict {Γ : Env} {M : Module} (hM : ModuleOk Γ M)
    {pre : List Fn} {fn : Fn} {post : List Fn} (hsplit : M.fns = pre ++ fn :: post)
    {xs : Tup Val fn.as} {m : Mem 64} {Q : Post fn.rs} {X : XPost} (hspec : Γ fn.name fn.as fn.rs xs m Q X) :
    Func.wp (Env.restrict Γ (pre.map Fn.sig ++ M.externs.map Extern.sig)) fn.body xs m Q X :=
  let ⟨hwf, hcalls, hwp⟩ := hM.fnsOk pre fn post hsplit
  wp_env_agree_of_callsOk (hwf Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units fn.as))
    hcalls (fun _ _ _ hmem _ _ _ _ hg => ⟨hmem, hg⟩) m (hwp xs m Q X hspec)

theorem ModuleOk.ofModule {Γ : Env} {M : Module} (hM : ModuleOk Γ M) :
    ModuleOk (Env.ofModule M Γ) M := by
  refine ⟨hM.nodup, fun pre fn post hsplit => ?_⟩
  have ⟨hwf, hcalls, _⟩ := hM.fnsOk pre fn post hsplit
  refine ⟨hwf, hcalls, fun xs m Q X hspec =>
    wp_env_agree_of_callsOk (hwf Val (fun _ => Unit) Cont (fun _ => Unit) xs (Tup.units fn.as))
      hcalls (fun _ _ _ hmem _ _ _ _ hg => ⟨?_, hg.2⟩) m (hM.wp_restrict hsplit hspec.2)⟩
  rcases List.mem_append.mp hmem with hp | he
  · exact List.mem_append_left _
      (by rw [hsplit, List.map_append]; exact List.mem_append_left _ hp)
  · exact List.mem_append_right _ he

private theorem sigs_map_fst (M : Module) : M.sigs.map Prod.fst = M.names := by
  simp [Module.sigs, Module.names, List.map_append, List.map_map, Function.comp_def, Fn.sig, Extern.sig]

private theorem mem_unique_fst : ∀ {xs : List SigEntry}, (xs.map Prod.fst).Nodup →
    ∀ {f as₁ bs₁ as₂ bs₂}, (f, as₁, bs₁) ∈ xs → (f, as₂, bs₂) ∈ xs → as₁ = as₂ ∧ bs₁ = bs₂
  | [], _, _, _, _, _, _, h, _ => nomatch h
  | (_, _, _) :: _, hnd, _, _, _, _, _, h1, h2 => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
    rcases List.mem_cons.mp h1 with e1 | h1 <;> rcases List.mem_cons.mp h2 with e2 | h2
    · cases e1; cases e2; exact ⟨rfl, rfl⟩
    · cases e1; exact absurd rfl (hnd.1 _ h2)
    · cases e2; exact absurd rfl (hnd.1 _ h1)
    · exact mem_unique_fst hnd.2 h1 h2

theorem Env.ofModule_empty_off_sig {M : Module} (hnd : M.namesNodup) (Γ : Env) {fn : Fn} (hfn : fn ∈ M.fns)
    {as bs : List Ty} (hne : (as, bs) ≠ (fn.as, fn.rs)) (xs : Tup Val as) (m : Mem 64) (Q : Post bs) (X : XPost) :
    ¬ Env.ofModule M Γ fn.name as bs xs m Q X := fun h =>
  let ⟨ha, hb⟩ := mem_unique_fst (sigs_map_fst M ▸ hnd) h.1 (List.mem_append_left _ (List.mem_map.mpr ⟨fn, hfn, rfl⟩))
  hne (Prod.ext ha hb)

theorem Env.ofModule_empty_off_extern_sig {M : Module} (hnd : M.namesNodup) (Γ : Env) {ex : Extern} (hex : ex ∈ M.externs)
    {as bs : List Ty} (hne : (as, bs) ≠ (ex.as, ex.rs)) (xs : Tup Val as) (m : Mem 64) (Q : Post bs) (X : XPost) :
    ¬ Env.ofModule M Γ ex.name as bs xs m Q X := fun h =>
  let ⟨ha, hb⟩ := mem_unique_fst (sigs_map_fst M ▸ hnd) h.1 (List.mem_append_right _ (List.mem_map.mpr ⟨ex, hex, rfl⟩))
  hne (Prod.ext ha hb)

theorem Env.ofModule_empty_undeclared {M : Module} (Γ : Env) {f : Sym} (hf : f ∉ M.names)
    (as bs : List Ty) (xs : Tup Val as) (m : Mem 64) (Q : Post bs) (X : XPost) :
    ¬ Env.ofModule M Γ f as bs xs m Q X := fun h =>
  hf (sigs_map_fst M ▸ List.mem_map.mpr ⟨(f, as, bs), h.1, rfl⟩)

def selfRecFn : Fn := ⟨"self", [], [], fun _ _ _ => .call "self" (as := []) (bs := []) () (fun _ => .ret ())⟩

theorem selfRec_not_moduleOk (Γ : Env) (exts : List Extern) (exits : List Sym) :
    ¬ ModuleOk Γ { fns := [selfRecFn], externs := exts, exits := exits } := fun hM => by
  have ⟨_, hcalls, _⟩ := hM.fnsOk [] selfRecFn [] rfl
  simp only [Fn.callsOk, selfRecFn, Expr.callsOk, List.map_nil, List.nil_append, List.mem_map] at hcalls
  obtain ⟨⟨ex, hex, hsig⟩, _⟩ := hcalls
  have hnd := hM.nodup
  simp only [Module.namesNodup, Module.names, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
  exact hnd.1 ex hex (congrArg Prod.fst hsig)


/-! ## Decidable-free `ModuleOk` checker -/

/-- Boolean equality on `SigEntry`, kernel-reducible by `rfl`. -/
def SigEntry.beq (a b : SigEntry) : Bool :=
  (a.1 == b.1) && Ty.listBeq a.2.1 b.2.1 && Ty.listBeq a.2.2 b.2.2

theorem SigEntry.beq_iff_eq {a b : SigEntry} : SigEntry.beq a b = true ↔ a = b := by
  rcases a with ⟨fa, asa, bsa⟩
  rcases b with ⟨fb, asb, bsb⟩
  simp [SigEntry.beq, Bool.and_eq_true, Ty.listBeq_iff_eq, and_assoc]

/-- Boolean `Module.namesNodup` check, kernel-reducible by `rfl`. -/
def Module.checkNamesNodup (M : Module) : Bool :=
  listNodup M.names

theorem Module.namesNodup_of_checkNamesNodup {M : Module}
    (h : M.checkNamesNodup = true) : M.namesNodup :=
  listNodup_nodup h

mutual
def Expr.checkCallsOk (allowed : List SigEntry) (exits : List Sym) {rs : List Ty} :
    Expr (fun _ => Unit) (fun _ => Unit) rs → Bool
  | .let_ _ k => (k (Tup.units _)).checkCallsOk allowed exits
  | .load _ _ k => (k ()).checkCallsOk allowed exits
  | .store _ _ k => k.checkCallsOk allowed exits
  | .call f (as := as) (bs := bs) _ k =>
      allowed.any (SigEntry.beq (f, as, bs)) &&
        (k (Tup.units bs)).checkCallsOk allowed exits
  | .jnz _ t e => t.checkCallsOk allowed exits && e.checkCallsOk allowed exits
  | .jump _ _ | .ret _ | .hlt => true
  | .exit f _ => exits.any (fun e => f == e)
  | .group (sig := sig) bodies k =>
      (bodies (Tup.units sig)).checkCallsOk allowed exits &&
        (k (Tup.units sig)).checkCallsOk allowed exits

def Blocks.checkCallsOk (allowed : List SigEntry) (exits : List Sym) {rs : List Ty} :
    {sig : List (List Ty)} → Blocks (fun _ => Unit) (fun _ => Unit) rs sig → Bool
  | _, .nil => true
  | _, .cons b bs =>
      (b (Tup.units _)).checkCallsOk allowed exits && bs.checkCallsOk allowed exits
end

mutual
theorem Expr.callsOk_of_checkCallsOk {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} :
    (e : Expr (fun _ => Unit) (fun _ => Unit) rs) →
    e.checkCallsOk allowed exits = true →
    e.callsOk allowed exits
  | .let_ _ k, h => Expr.callsOk_of_checkCallsOk (k (Tup.units _)) h
  | .load _ _ k, h => Expr.callsOk_of_checkCallsOk (k ()) h
  | .store _ _ k, h => Expr.callsOk_of_checkCallsOk k h
  | .call f (as := as) (bs := bs) _ k, h => by
    simp only [Expr.checkCallsOk, Bool.and_eq_true, List.any_eq_true, SigEntry.beq_iff_eq] at h
    rcases h with ⟨⟨s, hs, heq⟩, hk⟩
    exact ⟨heq ▸ hs, Expr.callsOk_of_checkCallsOk (k (Tup.units bs)) hk⟩
  | .jnz _ t e, h => by
    simp only [Expr.checkCallsOk, Bool.and_eq_true] at h
    exact ⟨Expr.callsOk_of_checkCallsOk t h.1, Expr.callsOk_of_checkCallsOk e h.2⟩
  | .jump _ _, _ | .ret _, _ | .hlt, _ => trivial
  | .exit f _, h => by
    simp only [Expr.checkCallsOk, List.any_eq_true, beq_iff_eq] at h
    rcases h with ⟨s, hs, rfl⟩
    exact hs
  | .group (sig := sig) bodies k, h => by
    simp only [Expr.checkCallsOk, Bool.and_eq_true] at h
    exact ⟨Blocks.callsOk_of_checkCallsOk (bodies (Tup.units sig)) h.1,
      Expr.callsOk_of_checkCallsOk (k (Tup.units sig)) h.2⟩

theorem Blocks.callsOk_of_checkCallsOk {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} :
    {sig : List (List Ty)} → (bs : Blocks (fun _ => Unit) (fun _ => Unit) rs sig) →
    bs.checkCallsOk allowed exits = true →
    bs.callsOk allowed exits
  | _, .nil, _ => trivial
  | _, .cons b bs, h => by
    simp only [Blocks.checkCallsOk, Bool.and_eq_true] at h
    exact ⟨Expr.callsOk_of_checkCallsOk (b (Tup.units _)) h.1,
      Blocks.callsOk_of_checkCallsOk bs h.2⟩
end

def Fn.checkCallsOk (allowed : List SigEntry) (exits : List Sym) (fn : Fn) : Bool :=
  (fn.body (fun _ => Unit) (fun _ => Unit) (Tup.units fn.as)).checkCallsOk allowed exits

theorem Fn.callsOk_of_checkCallsOk {allowed : List SigEntry} {exits : List Sym} {fn : Fn}
    (h : fn.checkCallsOk allowed exits = true) : fn.callsOk allowed exits :=
  Expr.callsOk_of_checkCallsOk _ h

def Module.checkFnsCallsOk (exits : List Sym) (extSigs : List SigEntry) :
    List SigEntry → List Fn → Bool
  | _, [] => true
  | allowed, fn :: rest =>
      fn.checkCallsOk (allowed ++ extSigs) exits &&
      Module.checkFnsCallsOk exits extSigs (allowed ++ [fn.sig]) rest

theorem Module.checkFnsCallsOk_ok (exits : List Sym) (extSigs : List SigEntry) :
    ∀ (seen rest pre : List Fn) (fn : Fn) (post : List Fn),
    Module.checkFnsCallsOk exits extSigs (seen.map Fn.sig) rest = true →
    rest = pre ++ fn :: post →
    fn.callsOk ((seen ++ pre).map Fn.sig ++ extSigs) exits
  | _, [], pre, _, _, _, hsplit => by cases pre <;> simp at hsplit
  | seen, f :: rest, [], fn, post, hchk, hsplit => by
    simp only [List.nil_append, List.cons.injEq] at hsplit
    rcases hsplit with ⟨rfl, _⟩
    simp only [Module.checkFnsCallsOk, Bool.and_eq_true] at hchk
    simpa [List.append_nil] using Fn.callsOk_of_checkCallsOk hchk.1
  | seen, f :: rest, f' :: pre', fn, post, hchk, hsplit => by
    simp only [List.cons_append, List.cons.injEq] at hsplit
    rcases hsplit with ⟨rfl, hrest⟩
    simp only [Module.checkFnsCallsOk, Bool.and_eq_true] at hchk
    have hnext := hchk.2
    rw [show seen.map Fn.sig ++ [f.sig] = (seen ++ [f]).map Fn.sig by simp] at hnext
    have ih := Module.checkFnsCallsOk_ok exits extSigs (seen ++ [f]) rest pre' fn post hnext hrest
    simpa [List.append_assoc] using ih

/-- Acyclicity + `namesNodup` boolean checker for `Module`, kernel-reducible by `rfl`. -/
def Module.checkAcyclic (M : Module) : Bool :=
  M.checkNamesNodup && Module.checkFnsCallsOk M.exits (M.externs.map Extern.sig) [] M.fns

/-- Construct `ModuleOk Γ M` from `M.checkAcyclic = true` plus per-function `Wf` and `Func.wp`. -/
theorem Module.moduleOk_of_checkAcyclic {Γ : Env} {M : Module}
    (hcheck : M.checkAcyclic = true)
    (hwf : ∀ fn ∈ M.fns, fn.Wf)
    (hwp : ∀ fn ∈ M.fns, ∀ xs m Q X,
      Γ fn.name fn.as fn.rs xs m Q X → Func.wp Γ fn.body xs m Q X) :
    ModuleOk Γ M := by
  simp only [Module.checkAcyclic, Bool.and_eq_true] at hcheck
  refine ⟨Module.namesNodup_of_checkNamesNodup hcheck.1, fun pre fn post hsplit => ?_⟩
  have hmem : fn ∈ M.fns := hsplit ▸ by simp
  refine ⟨hwf fn hmem, ?_, hwp fn hmem⟩
  simpa using Module.checkFnsCallsOk_ok M.exits (M.externs.map Extern.sig)
    [] M.fns pre fn post hcheck.2 hsplit

end LeanQbe.T
