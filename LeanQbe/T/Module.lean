module

public import LeanQbe.T.WPLemmas
public import LeanQbe.T.WfLemmas

/-!
# Typed IR modules, acyclic `ModuleOk`, and `Env.ofModule` (`H2`)

100%-PHOAS module representation (`Module := {fns, externs, exits}`), acyclic callees-first
`ModuleOk Γ M` (rejecting all call cycles/SCCs; `link_rec` deferred post-T16),
`wp_env_agree_of_callsOk` via `Wf.induct`, and `Env.ofModule` with signature-isolation lemmas
resolving Seam 4.4 (`legalEnv` colliding-signature hazard).
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

theorem wp_env_agree_of_callsOk {Γ Γ' : Env} {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} {Q : Post rs} {X : XPost} {G : Ctx Val (fun _ => Unit)} {D : Ctx Cont (fun _ => Unit)}
    {e₁ : Expr Val Cont rs} {e₂ : Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hwf : Wf G D e₁ e₂) (hcalls : e₂.callsOk allowed exits)
    (hΓ : ∀ f as bs, (f, as, bs) ∈ allowed → ∀ xs m P E, Γ f as bs xs m P E → Γ' f as bs xs m P E) :
    ∀ m, wp Γ Q X e₁ m → wp Γ' Q X e₁ m := by
  induction hwf using Wf.induct with
  | let_ _ _ ih => intro m h; exact Op.wp_mono (fun r => ih r (Tup.units _) hcalls m) h
  | load _ _ _ ih => intro m ⟨v, hv, h⟩; exact ⟨v, hv, ih v () hcalls m h⟩
  | store _ _ _ ih => intro m ⟨hok, h⟩; exact ⟨hok, ih hcalls _ h⟩
  | call f _ _ ih =>
    intro m ⟨P, E, hG, hP, hE⟩
    exact ⟨P, E, hΓ f _ _ hcalls.1 _ m P E hG, fun r m' hr => ih r (Tup.units _) hcalls.2 m' (hP r m' hr), hE⟩
  | jnz _ _ _ iht ihe => intro m h; exact ⟨fun hc => iht hcalls.1 m (h.1 hc), fun hc => ihe hcalls.2 m (h.2 hc)⟩
  | jump _ _ | ret _ | exit _ _ | hlt => intro _ h; exact h
  | group _ _ ihb ihk =>
    intro m h Js hc; refine ihk Js (Tup.units _) hcalls.2 m (h Js ?_); rw [closed_iff] at hc ⊢
    exact fun i xs m' hb => hc i xs m' (ihb Js (Tup.units _) i xs (Tup.units _) (Blocks.callsOk_get hcalls.1 i) m' hb)

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

theorem ModuleOk.ofModule {Γ : Env} {M : Module} (hM : ModuleOk Γ M) : ModuleOk (Env.ofModule M Γ) M := by
  refine ⟨hM.nodup, fun pre fn post hsplit => ?_⟩
  have ⟨hwf, hcalls, _⟩ := hM.fnsOk pre fn post hsplit
  refine ⟨hwf, hcalls, fun xs m Q X hspec => wp_env_mono (fun _ _ _ _ _ _ _ hg => ?_) _ m (hM.wp_restrict hsplit hspec.2)⟩
  rcases List.mem_append.mp hg.1 with hp | he
  · exact ⟨List.mem_append_left _ (by rw [hsplit, List.map_append]; exact List.mem_append_left _ hp), hg.2⟩
  · exact ⟨List.mem_append_right _ he, hg.2⟩

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


end LeanQbe.T
