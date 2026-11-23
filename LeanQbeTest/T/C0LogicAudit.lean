module

public import LeanQbe.T.WPLemmas
public import LeanQbe.T.Frontend.C0
meta import LeanQbe.T.Frontend.C0.ToFlat
public import LeanQbe.T.Logic.Rules
public import LeanQbe.T.Logic.C0StepAttr
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.C0Agrees
public import LeanQbe.T.Logic.SepTree
public import LeanQbe.T.Logic.SlabChain
public import LeanQbe.T.Logic.SlabLayoutElab
public import LeanQbe.T.Logic.ControlComb
public import LeanQbe.T.LegalEmit

set_option autoImplicit false

@[expose] public section

/-!
# Audit Specification: C0 Frontend & Separation-Logic Proof Tooling

This file exposes an auditor-facing summary of the C0 frontend elaboration guarantees,
program-logic (`Func.wp` / `Prog`) rules, symbolic stepper (`C0Step` / `C0HeadStep` /
`C0StepAttr` / `C0Agrees`), separation-tree and slab layout automation (`SepTree` /
`SlabChain` / `SlabLayoutElab`), and legality-preserving control/emission combinators
(`ControlComb` / `LegalEmit`).

Every theorem here uses standard Lean logic without trust assumptions beyond
`[propext, Classical.choice, Quot.sound]`, and imports no target-architecture backend
(`Kraken.X64` or `Kraken.AArch64`).

## Trusted Computing Base (Definitions to Inspect)

1. **Core IR & WP Semantics (`LeanQbe.T.Prog`, `LeanQbe.T.WP`):** `Expr`, `Blocks`, `Fn`,
   `Func`, `Module`, `Env`, `Post`, `XPost`, `wp`, `Func.wp`, `ModuleOk`, and `Mem 64`.
2. **Separation Logic Primitives (`LeanQbe.T.Sep`):** separating conjunction `⋆`, `region`,
   `array`, `cell`, and `Mem 64` footprint disjointness.
3. **C0 Frontend Syntax (`LeanQbe.T.Frontend.C0`):** `TFlatFn`, `compileC0Source`, and the
   surface C0 source grammar accepted by the parser.

## What Is Proved Inside Lean

1. **`Func.wp` / `Prog` core sound rules (`WPLemmas`, `Logic.Rules`):**
   - Weakest-precondition monotonicity in postconditions and environments (`wp_mono`,
     `Func.spec_mono`, `wp_env_mono`), mutual-block closure (`closed_iff`), call-spec rule
     (`wp_call_of_spec`), group loop/join rules (`wp_loop_group`, `wp_join_group`), and
     array load/store separation rules (`wp_load_array`, `wp_store_array`).
2. **C0 Frontend, `C0Step`, `C0HeadStep`, `C0StepAttr`, & `C0Agrees`:**
   - Every elaborated `TFlatFn` produces a well-formed `Fn` (`TFlatFn.toFn_wf`).
   - `Env.ofTable` tables satisfy `ModuleOk` via per-function `SpecEntry.Impl` proofs and
     propagate `noExit` uniformly (`Env.ofTable_moduleOk`, `Env.ofTable_of_mem`,
     `Env.ofTable_noExit`, `SpecEntry.Impl.of`).
   - Head-step rules (`head_wp_add`, `head_wp_jnz`, `head_wp_ret`, `c0_hsteps!`) and frame
     preservation combinators (`wp_loop_agreesExcept`, `wp_loop_safety_slice`,
     `SafetySlice.lift_scratchOnly`) are sound against `wp`; `C0StepAttr` only registers
     and indexes proof-automation lemmas without expanding the trusted base.
3. **`SepTree`, `SlabChain`, & `SlabLayoutElab`:**
   - Balanced separation trees support O(log n) focus/unfocus without changing denoted
     memory propositions (`SepTree.eval_eq_focus`, `SepTree.focus`, `SepTree.unfocus_eq`,
     `sepTree_arr_pad_get`, `sepTree_arr_pad_put`).
   - Aligned `SlabChain` segments compile into a balanced `SepTree` and collapse to a
     contiguous `region` (`SlabChain.to_region`, `SlabChain.balancedTree_eval`,
     `SlabChain.balancedTree_to_region`), while `C0Lens` composition preserves `AgreesExcept`
     (`C0Lens.comp`, `C0Lens.agreesExcept_set`).
4. **`ControlComb` & `LegalEmit`:**
   - Stateful branch/join/loop combinators (`wp_jnz_decide`, `wp_join_state`,
     `wp_while_state`, `wp_while_break_state`) and legality-preserving IR emitter combinators
     (`Emit.run_isLegal`, `Emit.run_wf`, `Emit.run_wp`, `Emit.bundle`, `boolCmpEmit_bundle`,
     `ternlogBoolEmit_bundle`).
-/

namespace C0LogicAudit

open LeanQbe.T

/-! ## 1. Core `Func.wp` / `Prog` Soundness Rules -/

theorem audit_wp_mono {Γ : Env} {rs : List Ty} {Q Q' : Post rs} {X X' : XPost}
    (hQ : ∀ vs m, Q vs m → Q' vs m)
    (hX : ∀ f cs xs m, X f cs xs m → X' f cs xs m)
    (e : Expr Val Cont rs) :
    ∀ m, wp Γ Q X e m → wp Γ Q' X' e m :=
  wp_mono hQ hX e

theorem audit_func_spec_mono {as rs : List Ty} (Γ : Env) (f : Func as rs) :
    (Func.spec Γ f).Mono :=
  Func.spec_mono Γ f

theorem audit_wp_env_mono {Γ Γ' : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hΓ : ∀ g as bs xs m P E, Γ g as bs xs m P E → Γ' g as bs xs m P E)
    (e : Expr Val Cont rs) :
    ∀ m, wp Γ Q X e m → wp Γ' Q X e m :=
  wp_env_mono hΓ e

theorem audit_closed_iff (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) :
    {sig : List (List Ty)} → (bs : Blocks Val Cont rs sig) → (Js : Tup Cont sig) →
      (Closed Γ Q X bs Js ↔
        ∀ {ts} (i : Member ts sig) xs m, wp Γ Q X (bs.get i xs) m → Js.get i xs m) :=
  closed_iff Γ Q X

theorem audit_wp_call_spec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {f : Sym} {as bs : List Ty} (args : Tup (Arg Val) as)
    (k : Tup Val bs → Expr Val Cont rs)
    (h : Γ f as bs (vals args) m (fun r m' => wp Γ Q X (k r) m') X) :
    wp Γ Q X (.call f args k) m :=
  wp_call_of_spec args k h

theorem audit_wp_loop_grp {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64}
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    (Inv : Nat → Tup Val ts → Mem 64 → Prop)
    (hbody : ∀ (J : Cont ts) n xs m,
      (∀ n' ys m', n' < n → Inv n' ys m' → J ys m') →
      Inv n xs m → wp Γ Q X (Blocks.get (bodies (J, ())) .here xs) m)
    (hentry : ∀ (J : Cont ts),
      (∀ n xs m, Inv n xs m → J xs m) → wp Γ Q X (entry (J, ())) m) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  wp_loop_group Inv hbody hentry

theorem audit_wp_join_grp {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64}
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    (P : Tup Val ts → Mem 64 → Prop)
    (hbody : ∀ (J : Cont ts) xs m, P xs m →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here xs) m)
    (hentry : ∀ (J : Cont ts),
      (∀ xs m, P xs m → J xs m) → wp Γ Q X (entry (J, ())) m) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  wp_join_group P hbody hentry

theorem audit_wp_load_arr {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {t : Ty} {base : BitVec 64} {xs : List (Val t)} {i : Nat}
    {a : Arg Val i64} {R : Mem 64 → Prop} {m : Mem 64} {k : Val t → Expr Val Cont rs}
    (hb : t.bytes ≤ 2 ^ 64)
    (heq : a.val = base + BitVec.ofNat 64 (t.bytes * i))
    (hi : i < xs.length) (hm : (array base xs ⋆ R) m)
    (hk : wp Γ Q X (k xs[i]) m) :
    wp Γ Q X (.load t a k) m :=
  wp_load_array hb heq hi hm hk

theorem audit_wp_store_arr {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {t : Ty} {base : BitVec 64} {xs : List (Val t)} {i : Nat}
    {v : Arg Val t} {a : Arg Val i64} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Expr Val Cont rs}
    (hb : t.bytes ≤ 2 ^ 64)
    (heq : a.val = base + BitVec.ofNat 64 (t.bytes * i))
    (hi : i < xs.length) (hm : (array base xs ⋆ R) m)
    (hk : ∀ m', (array base (xs.set i v.val) ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (.store v a k) m :=
  wp_store_array hb heq hi hm hk

/-! ## 2. C0 Frontend, `C0Step`, `C0HeadStep`, `C0StepAttr`, & `C0Agrees` -/

#guard (Frontend.C0.compileC0Source [] "int64_t inc(int64_t x) { return x + 1; }").isOk
#guard
  match Frontend.C0.compileC0Source [] "int64_t inc(int64_t x) { return x + 1; }" with
  | .ok [tf] => tf.toFn.name == "inc"
  | _ => false

theorem audit_c0_toFn_wf (tf : Frontend.C0.TFlatFn) : tf.toFn.Wf :=
  Frontend.C0.TFlatFn.toFn_wf tf

theorem audit_ofTable_mod {tbl : List SpecEntry} {M : Module}
    (hchk : M.checkAcyclic = true)
    (hwf : AllFns Fn.Wf M.fns)
    (hok : TableImpl (Env.ofTable tbl) M.fns tbl) :
    ModuleOk (Env.ofTable tbl) M :=
  Env.ofTable_moduleOk hchk hwf hok

theorem audit_ofTable_mem {tbl : List SpecEntry} {e : SpecEntry}
    (he : e ∈ tbl) (hnd : (tbl.map SpecEntry.name).Nodup)
    {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs} {X : XPost}
    (h : e.eff xs m Q X) :
    Env.ofTable tbl e.name e.as e.rs xs m Q X :=
  Env.ofTable_of_mem he hnd h

theorem audit_ofTable_noExit {tbl : List SpecEntry}
    (h : ∀ e ∈ tbl, e.noExit = true) :
    ∀ f as bs xs m Q X X',
      Env.ofTable tbl f as bs xs m Q X → Env.ofTable tbl f as bs xs m Q X' :=
  Env.ofTable_noExit h

theorem audit_specEntry_impl {Γ : Env} {fn : Fn} {spec : Spec fn.as fn.rs}
    {noExit : Bool}
    (h : ∀ xs m Q X, spec xs m Q X → Func.wp Γ fn.body xs m Q X) :
    SpecEntry.Impl Γ fn (.ofFn fn spec noExit) :=
  SpecEntry.Impl.of h

theorem audit_hwp_add {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {n : Nat} {a b : Arg Val (.bits n)} {va vb : BitVec n}
    {k : C0HeadStep.K1 rs (.bits n)} (ha : a.val = va) (hb : b.val = vb)
    (h : wp Γ Q X (k (va + vb, ())) m) :
    wp Γ Q X (.let_ (Op.mk (OpCode.add (.bits n)) (a, b, ())) k) m :=
  C0HeadStep.head_wp_add ha hb h

theorem audit_hwp_load {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {t : Ty} {a : Arg Val i64} {addr : BitVec 64} {k : Val t → Expr Val Cont rs} {v : Val t}
    (ha : a.val = addr) (hl : loadVal m t addr = some v) (hk : wp Γ Q X (k v) m) :
    wp Γ Q X (.load t a k) m :=
  C0HeadStep.head_wp_load ha hl hk

theorem audit_hwp_store {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {t : Ty} {v : Arg Val t} {a : Arg Val i64} {val : Val t} {addr : BitVec 64}
    {k : Expr Val Cont rs} {P R : Mem 64 → Prop}
    (hv : v.val = val) (ha : a.val = addr)
    (hstep : storeOk m t addr ∧ (P ⋆ R) (storeMem m t addr val))
    (hk : ∀ m', (P ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (.store v a k) m :=
  C0HeadStep.head_wp_store hv ha hstep hk

theorem audit_hwp_jnz {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {c : Arg Val .bool} {vc : Bool} {e₁ e₂ : Expr Val Cont rs}
    (hc : c.val = vc) (h₁ : vc = true → wp Γ Q X e₁ m)
    (h₂ : vc = false → wp Γ Q X e₂ m) :
    wp Γ Q X (.jnz c e₁ e₂) m :=
  C0HeadStep.head_wp_jnz hc h₁ h₂

theorem audit_hwp_ret {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {args : Tup (Arg Val) rs} {vs : Tup Val rs} (hvs : vals args = vs) (h : Q vs m) :
    wp Γ Q X (.ret args) m :=
  C0HeadStep.head_wp_ret hvs h

/-- Smoke verification that `c0_hsteps!` discharges a concrete straight-line `wp` goal
    over an `.add` + `.ret` residual automatically. -/
theorem audit_c0_hsteps_smoke (Γ : Env) (m : Mem 64) (x : BitVec 64) :
    wp Γ (fun (r : Tup Val [i64]) m' => r = (x + 1, ()) ∧ m' = m) (fun _ _ _ _ => False)
      (.let_ (Op.mk (OpCode.add i64) (Arg.imm x, Arg.imm 1, ()))
        (fun y => .ret (Arg.var y.1, ()))) m := by
  c0_hsteps!
  exact ⟨rfl, rfl⟩

theorem audit_loop_agrees {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {ts : List Ty} {m : Mem 64} {σ : Type} (mask : σ → σ) (s₀ : σ)
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    (Inv : σ → Tup Val ts → Mem 64 → Prop) (μ : Tup Val ts → Mem 64 → Nat)
    (hentry : ∀ (J : Cont ts),
      (∀ (s' : σ) (xs : Tup Val ts) (ml : Mem 64),
        AgreesExcept mask s₀ s' → Inv s' xs ml → J xs ml) →
      wp Γ Q X (entry (J, ())) m)
    (hbody : ∀ (J : Cont ts) (s' : σ) (xs : Tup Val ts) (ml : Mem 64),
      AgreesExcept mask s₀ s' → Inv s' xs ml →
      (∀ (s'' : σ) (ys : Tup Val ts) (ml' : Mem 64),
        μ ys ml' < μ xs ml → AgreesExcept mask s' s'' → Inv s'' ys ml' → J ys ml') →
      wp Γ Q X ((bodies (J, ())).get .here xs) ml) :
    wp Γ Q X (Expr.group bodies entry) m :=
  wp_loop_agreesExcept mask s₀ Inv μ hentry hbody

theorem audit_loop_safety {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {ts : List Ty}
    {m : Mem 64} {σ κ : Type} (sl : SafetySlice σ κ) (s₀ : σ) (R : Mem 64 → Prop)
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs}
    (Inv : κ → Prop) (hInv : Inv (sl.coreProj s₀))
    (LoopInv : σ → Tup Val ts → Prop) (μ : Tup Val ts → Nat)
    (hentry : ∀ (J : Cont ts),
      (∀ (s' : σ) (xs : Tup Val ts) (ml : Mem 64),
        (sl.mem s' ⋆ R) ml → PreservesCoreSlice sl.coreProj s₀ s' →
        sl.safe s' → LoopInv s' xs → J xs ml) →
      wp Γ Q X (entry (J, ())) m)
    (hbody : ∀ (J : Cont ts) (s' : σ) (xs : Tup Val ts) (ml : Mem 64),
      PreservesCoreSlice sl.coreProj s₀ s' → sl.safe s' → Inv (sl.coreProj s') →
      LoopInv s' xs → (sl.mem s' ⋆ R) ml →
      (∀ (s'' : σ) (ys : Tup Val ts) (ml' : Mem 64),
        (sl.mem s'' ⋆ R) ml' → μ ys < μ xs → PreservesCoreSlice sl.coreProj s' s'' →
        sl.safe s'' → LoopInv s'' ys → J ys ml') →
      wp Γ Q X ((bodies (J, ())).get .here xs) ml) :
    wp Γ Q X (Expr.group bodies entry) m :=
  wp_loop_safety_slice sl s₀ R Inv hInv LoopInv μ hentry hbody

theorem audit_safety_lift {ι κ τ : Type} {as rs : List Ty}
    {coreMem : ι → κ → Mem 64 → Prop} {scratchMem : ι → τ → Mem 64 → Prop}
    {scratchSafe : ι → τ → Prop} {Pre : ι → Tup Val as → τ → Prop}
    {Post : ι → Tup Val as → Tup Val rs → τ → τ → Prop}
    {Γ : Env} {body : Func as rs}
    (hScratch : ∀ (xs : Tup Val as) (m : Mem 64) (Q : LeanQbe.T.Post rs) (X : XPost),
      (∃ c t R, Pre c xs t ∧ scratchSafe c t ∧ (scratchMem c t ⋆ R) m ∧
        ∀ (r : Tup Val rs) (t' : τ) (m' : Mem 64),
          scratchSafe c t' → Post c xs r t t' → (scratchMem c t' ⋆ R) m' → Q r m') →
      Func.wp Γ body xs m Q X)
    (xs : Tup Val as) (m : Mem 64) (Q : LeanQbe.T.Post rs) (X : XPost) :
    SafetySlice.spec (fun c => SafetySlice.ofPair (coreMem c) (scratchMem c) (scratchSafe c))
      (fun c xs p => Pre c xs p.snd) (fun c xs r p p' => Post c xs r p.snd p'.snd)
      xs m Q X →
    Func.wp Γ body xs m Q X :=
  SafetySlice.lift_scratchOnly hScratch xs m Q X

/-! ## 3. `SepTree`, `SlabChain`, & `SlabLayoutElab` -/

#guard align8 0 == 0
#guard align8 9 == 16
#guard SlabChain.totalBytes [.ofCell64 0, .ofArray64 [1, 2, 3] 3 rfl] == 32
#guard (SlabChain.addrList (0 : BitVec 64) [.ofCell64 0, .ofCell64 0]).length == 2

theorem audit_sepTree_focus_eq (t : SepTree) (p : List Bool) :
    t.eval = (t.get p ⋆ t.rest p) :=
  SepTree.eval_eq_focus t p

theorem audit_sepTree_focus {t : SepTree} {R : Mem 64 → Prop} {m : Mem 64} (p : List Bool)
    (hm : (t.eval ⋆ R) m) :
    (t.get p ⋆ (t.rest p ⋆ R)) m :=
  SepTree.focus p hm

theorem audit_sepTree_unfocus {t : SepTree} {P' M' R : Mem 64 → Prop} {m : Mem 64}
    (p : List Bool) (heq : (t.set p P').eval = M')
    (hm : (P' ⋆ (t.rest p ⋆ R)) m) :
    (M' ⋆ R) m :=
  SepTree.unfocus_eq p heq hm

theorem audit_sepTree_arr_get {ty : Ty} {t : SepTree} {p : List Bool} {base : BitVec 64}
    {xs : List (Val ty)} {pad R : Mem 64 → Prop} {m : Mem 64}
    (hget : t.get p = array base xs ⋆ pad) (hb : ty.bytes ≤ 2 ^ 64)
    {i : Nat} (hi : i < xs.length) (hm : (t.eval ⋆ R) m) :
    loadVal m ty (base + BitVec.ofNat 64 (ty.bytes * i)) = some xs[i] :=
  sepTree_arr_pad_get hget hb hi hm

theorem audit_sepTree_arr_put {ty : Ty} {t : SepTree} {p : List Bool} {base : BitVec 64}
    {xs : List (Val ty)} {pad M' R : Mem 64 → Prop} {m : Mem 64}
    (hget : t.get p = array base xs ⋆ pad) (hb : ty.bytes ≤ 2 ^ 64)
    (v : Val ty) {i : Nat} (hi : i < xs.length)
    (heq : (t.set p (array base (xs.set i v) ⋆ pad)).eval = M') (hm : (t.eval ⋆ R) m) :
    storeOk m ty (base + BitVec.ofNat 64 (ty.bytes * i)) ∧
      (M' ⋆ R) (storeMem m ty (base + BitVec.ofNat 64 (ty.bytes * i)) v) :=
  sepTree_arr_pad_put hget hb v hi heq hm

theorem audit_slab_to_region (segs : List SlabSeg) (base : BitVec 64) {m : Mem 64}
    (hfit : SlabChain.totalBytes segs ≤ 2 ^ 64)
    (hm : SlabChain.eval base segs m) :
    region base (SlabChain.totalBytes segs) m :=
  SlabChain.to_region segs base hfit hm

theorem audit_slab_tree_eval (base : BitVec 64) (segs : List SlabSeg) :
    (SlabChain.balancedTree (SlabChain.addrList base segs)).eval = SlabChain.eval base segs :=
  SlabChain.balancedTree_eval base segs

theorem audit_slab_tree_reg (base : BitVec 64) (segs : List SlabSeg) {m : Mem 64}
    (hfit : SlabChain.totalBytes segs ≤ 2 ^ 64)
    (hm : (SlabChain.balancedTree (SlabChain.addrList base segs)).eval m) :
    region base (SlabChain.totalBytes segs) m :=
  SlabChain.balancedTree_to_region base segs hfit hm

theorem audit_lens_comp {α β γ : Type} (l1 : C0Lens α β) (l2 : C0Lens β γ) :
    (C0Lens.comp l1 l2).get = fun a => l2.get (l1.get a) :=
  rfl

theorem audit_lens_agrees {σ α : Type} (l : C0Lens σ α) (mask : σ → σ) (s : σ) (v : α)
    (hm : ∀ (t : σ) (x : α), mask (l.set t x) = mask t) :
    AgreesExcept mask s (l.set s v) :=
  C0Lens.agreesExcept_set l mask s v hm

/-! ## 4. `ControlComb` & `LegalEmit` Legality Proof Combinators -/

theorem audit_wp_jnz_dec {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {c : Arg Val .bool} {e₁ e₂ : Expr Val Cont rs} (P : Prop) [Decidable P]
    (hc : c.val = decide P) (ht : P → wp Γ Q X e₁ m) (hf : ¬P → wp Γ Q X e₂ m) :
    wp Γ Q X (.jnz c e₁ e₂) m :=
  wp_jnz_decide P hc ht hf

theorem audit_wp_join_st {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs} {α : Type}
    (proj : α → Tup Val ts) (Inv : α → Mem 64 → Prop)
    (hbody : ∀ (J : Cont ts) (st : α) (m' : Mem 64),
      Inv st m' → wp Γ Q X ((bodies (J, ())).get .here (proj st)) m')
    (hentry : ∀ (J : Cont ts),
      (∀ (st : α) (m' : Mem 64), Inv st m' → J (proj st) m') → wp Γ Q X (entry (J, ())) m) :
    wp Γ Q X (Expr.group bodies entry) m :=
  wp_join_state proj Inv hbody hentry

theorem audit_wp_while_st {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]}
    {entry : Tup Cont [ts] → Expr Val Cont rs} {α : Type}
    (proj : α → Tup Val ts) (μ : α → Nat) (Inv : α → Mem 64 → Prop)
    (hentry : ∀ (J : Cont ts),
      (∀ (st : α) (m' : Mem 64), Inv st m' → J (proj st) m') → wp Γ Q X (entry (J, ())) m)
    (hbody : ∀ (J : Cont ts) (st : α) (m' : Mem 64), Inv st m' →
      (∀ (st' : α) (m'' : Mem 64), μ st' < μ st → Inv st' m'' → J (proj st') m'') →
      wp Γ Q X ((bodies (J, ())).get .here (proj st)) m') :
    wp Γ Q X (Expr.group bodies entry) m :=
  wp_while_state proj μ Inv hentry hbody

theorem audit_wp_while_brk {Γ : Env} {rs brkTs lpTs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64}
    {outerBodies : Tup Cont [brkTs] → Blocks Val Cont rs [brkTs]}
    {innerBodies : Tup Cont [brkTs] → Tup Cont [lpTs] → Blocks Val Cont rs [lpTs]}
    {innerEntry : Tup Cont [brkTs] → Tup Cont [lpTs] → Expr Val Cont rs}
    {β α : Type}
    (projBrk : β → Tup Val brkTs) (BrkPost : β → Mem 64 → Prop)
    (projLp : α → Tup Val lpTs) (μ : α → Nat) (Inv : α → Mem 64 → Prop)
    (hafter : ∀ (B : Cont brkTs) (bst : β) (m' : Mem 64),
      BrkPost bst m' → wp Γ Q X ((outerBodies (B, ())).get .here (projBrk bst)) m')
    (hbody : ∀ (B : Cont brkTs) (L : Cont lpTs) (st : α) (m' : Mem 64),
      (∀ (bst : β) (m'' : Mem 64), BrkPost bst m'' → B (projBrk bst) m'') →
      (∀ (st' : α) (m'' : Mem 64), μ st' < μ st → Inv st' m'' → L (projLp st') m'') →
      Inv st m' → wp Γ Q X ((innerBodies (B, ()) (L, ())).get .here (projLp st)) m')
    (hentry : ∀ (B : Cont brkTs) (L : Cont lpTs),
      (∀ (bst : β) (m' : Mem 64), BrkPost bst m' → B (projBrk bst) m') →
      (∀ (st : α) (m' : Mem 64), Inv st m' → L (projLp st) m') →
      wp Γ Q X (innerEntry (B, ()) (L, ())) m) :
    wp Γ Q X (Expr.group outerBodies fun oJs =>
      Expr.group (innerBodies oJs) (innerEntry oJs)) m :=
  wp_while_break_state projBrk BrkPost projLp μ Inv hafter hbody hentry

theorem audit_emit_legal (target : LegalTarget) {inTys : List Ty} {t : Ty} (e : Emit inTys t)
    {Γ : List (Ty × VarKind)} {Δ : List (List Ty)} {rs : List Ty} (env : Tup (Arg K) inTys)
    (hleg : Emit.IsLegal target e) (henv : ArgsNormal target Γ env)
    {k : Arg K t → Expr K KL rs}
    (hk : IsLegalCont target Γ Δ (fun Γ' r => ArgNormal target Γ' t r) k) :
    TFlat.isLegal target Γ Δ (toTFlat (e.run env k) Γ.length Δ.length) = true :=
  Emit.run_isLegal target e env hleg henv hk

theorem audit_emit_wf {inTys : List Ty} {t : Ty} (e : Emit inTys t)
    {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {env₁ : Tup (Arg V₁) inTys} {env₂ : Tup (Arg V₂) inTys}
    (henv : TRel (ArgRel G) env₁ env₂)
    {k₁ : Arg V₁ t → Expr V₁ L₁ rs} {k₂ : Arg V₂ t → Expr V₂ L₂ rs}
    (hk : ∀ {G' : Ctx V₁ V₂},
      (∀ p ∈ G, p ∈ G') →
      ∀ (y₁ : Arg V₁ t) (y₂ : Arg V₂ t), ArgRel G' t y₁ y₂ → Wf G' D (k₁ y₁) (k₂ y₂)) :
    Wf G D (e.run env₁ k₁) (e.run env₂ k₂) :=
  Emit.run_wf e henv hk

theorem audit_emit_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {inTys : List Ty} {t : Ty} (e : Emit inTys t) (env : Tup (Arg Val) inTys)
    {k : Arg Val t → Expr Val Cont rs}
    (h : e.wp (valsTup env) fun v => ∀ (r : Arg Val t), r.val = v → wp Γ Q X (k r) m) :
    wp Γ Q X (e.run env k) m :=
  Emit.run_wp e env h

theorem audit_emit_bundle (target : LegalTarget) {inTys : List Ty} {t : Ty} (e : Emit inTys t)
    {sem : Tup Val inTys → (Val t → Prop) → Prop} (hleg : Emit.IsLegal target e)
    (hsem : ∀ (env : Tup Val inTys) (p : Val t → Prop), sem env p → e.wp env p) :
    LegalEmitSpec target e sem :=
  Emit.bundle target e hleg hsem

theorem audit_boolCmp_bundle (target : LegalTarget) (o : CmpOp) :
    LegalEmitSpec target (boolCmpEmit o) fun x p =>
      match x with
      | (a, b, PUnit.unit) => p (o.evalBool a b) :=
  boolCmpEmit_bundle target o

theorem audit_ternlog_bundle (target : LegalTarget) (imm : BitVec 8) :
    LegalEmitSpec target (ternlogBoolEmit imm) fun x p =>
      match x with
      | (a, b, c, PUnit.unit) => p (ternaryLogicBool a b c imm) :=
  ternlogBoolEmit_bundle target imm

theorem audit_maskToN_legal (target : LegalTarget) {n w : Nat} (hw : w ∈ target.bitWidths) :
    (maskToNEmit n w).IsLegal target :=
  maskToNEmit_isLegal target hw

theorem audit_sextToW_legal (target : LegalTarget) {n w : Nat} (hw : w ∈ target.bitWidths) :
    (sextToWEmit n w).IsLegal target :=
  sextToWEmit_isLegal target hw

theorem audit_ternlogBits_b (target : LegalTarget) {w : Nat} (hw : w ∈ target.bitWidths)
    (imm : BitVec 8) :
    LegalEmitSpec target (ternlogBitsEmit w imm)
      (fun (a, b, c, ()) p => p (ternaryLogic a b c imm)) :=
  ternlogBitsEmit_bundle target hw imm

/-! ## 5. `#print axioms` (one line each, `⊆ [propext, Classical.choice, Quot.sound]`) -/

#print axioms audit_wp_mono
#print axioms audit_func_spec_mono
#print axioms audit_wp_env_mono
#print axioms audit_closed_iff
#print axioms audit_wp_call_spec
#print axioms audit_wp_loop_grp
#print axioms audit_wp_join_grp
#print axioms audit_wp_load_arr
#print axioms audit_wp_store_arr
#print axioms audit_c0_toFn_wf
#print axioms audit_ofTable_mod
#print axioms audit_ofTable_mem
#print axioms audit_ofTable_noExit
#print axioms audit_specEntry_impl
#print axioms audit_hwp_add
#print axioms audit_hwp_load
#print axioms audit_hwp_store
#print axioms audit_hwp_jnz
#print axioms audit_hwp_ret
#print axioms audit_c0_hsteps_smoke
#print axioms audit_loop_agrees
#print axioms audit_loop_safety
#print axioms audit_safety_lift
#print axioms audit_sepTree_focus_eq
#print axioms audit_sepTree_focus
#print axioms audit_sepTree_unfocus
#print axioms audit_sepTree_arr_get
#print axioms audit_sepTree_arr_put
#print axioms audit_slab_to_region
#print axioms audit_slab_tree_eval
#print axioms audit_slab_tree_reg
#print axioms audit_lens_comp
#print axioms audit_lens_agrees
#print axioms audit_wp_jnz_dec
#print axioms audit_wp_join_st
#print axioms audit_wp_while_st
#print axioms audit_wp_while_brk
#print axioms audit_emit_legal
#print axioms audit_emit_wf
#print axioms audit_emit_wp
#print axioms audit_emit_bundle
#print axioms audit_boolCmp_bundle
#print axioms audit_ternlog_bundle
#print axioms audit_maskToN_legal
#print axioms audit_sextToW_legal
#print axioms audit_ternlogBits_b

end C0LogicAudit

end
