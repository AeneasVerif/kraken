module

public import LeanQbe.T.Logic.Rules
public import LeanQbe.T.Logic.C0StepAttr
public import LeanQbe.T.Module
public import Kraken.SeparationTactics
public meta import Lean.Elab.Tactic
public meta import LeanQbe.T.Logic.C0StepAttr
public meta import LeanQbe.T.Logic.Rules

/-!
# C0 proof-scaling toolkit: spec tables, framing helpers, and `c0_step` (`X0-proof`)

1. **Spec tables.** `SpecEntry` rows (`name`, `as`, `rs`, `spec`, `noExit`) and `Env.ofTable`, with
   `Env.ofTable_sound` (one `TableImpl` row per function instead of an N-way string `match` plus an
   N-way `rcases`), `Env.ofTable_moduleOk`, and `Env.ofTable_noExit`.
2. **Framing.** `AgreesExcept mask s s'`: `s'` differs from `s` at most in the fields overwritten by
   `mask` (a record update `fun t => { t with f₁ := _, … }`), so loop invariants and specs over a
   multi-field state `structure` never list the unchanged fields.
3. **Rules.** `wp_load_of`, `wp_store_sep`, `wp_jnz_of`, and the measure-based loop rule
   `wp_loop_inv`.
4. **Memory lemmas.** Footprint-indexed `@[c0_load]` / `@[c0_store]` lemmas for `cell`, `array`
   (C0 indexing `a + i * w`), and `array64`, plus the `bv_c0` simp set.
5. **Tactics.** `c0_frame` (Kraken `ecancel`), `c0_bound` (`omega` / `bv_omega` after `bv_c0`),
   `c0_step` (one symbolic-execution step) and `c0_steps` (all straight-line steps, branches, and
   non-recursive joins): unfold the function body, run pure `let`s, discharge each `load` / `store`
   with a `c0_load` / `c0_store` lemma whose frame is found by AC matching against the
   separation-logic hypotheses, split `jnz` with `bv_c0`-normalized conditions (closing infeasible
   branches), inline join points, and stop at loops, calls, and returns.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## 1. Specification tables -/

/-- One row of a specification table: contract `spec` for symbol `name : as → rs`.
With `noExit := true` the row ignores the caller's exit continuation (`X`), as required by
`Compiled.fnSpec_noExit_id`. -/
structure SpecEntry where
  name : Sym
  as : List Ty
  rs : List Ty
  spec : Spec as rs
  noExit : Bool := false

/-- Table row for the module function `fn`. -/
abbrev SpecEntry.ofFn (fn : Fn) (spec : Spec fn.as fn.rs) (noExit : Bool := false) : SpecEntry :=
  ⟨fn.name, fn.as, fn.rs, spec, noExit⟩

/-- Effective contract of a row: `spec`, with `X := ⊥` when `noExit`. -/
def SpecEntry.eff (e : SpecEntry) : Spec e.as e.rs :=
  fun xs m Q X => e.spec xs m Q (if e.noExit then fun _ _ _ _ => False else X)

/-- `e.eff` transported along signature equalities. -/
def SpecEntry.cast (e : SpecEntry) {as bs : List Ty} (ha : e.as = as) (hr : e.rs = bs) :
    Spec as bs :=
  ha ▸ hr ▸ e.eff

/-- First-match environment of a specification table (`False` off the table). -/
def Env.ofTable : List SpecEntry → Env
  | [] => fun _ _ _ _ _ _ _ => False
  | e :: es => fun f as bs xs m Q X =>
    (∃ h : e.name = f ∧ e.as = as ∧ e.rs = bs, e.cast h.2.1 h.2.2 xs m Q X) ∨
      (¬ (e.name = f ∧ e.as = as ∧ e.rs = bs) ∧ Env.ofTable es f as bs xs m Q X)

theorem Env.ofTable_cons_self (e : SpecEntry) (es : List SpecEntry) (xs : Tup Val e.as)
    (m : Mem 64) (Q : Post e.rs) (X : XPost) :
    Env.ofTable (e :: es) e.name e.as e.rs xs m Q X ↔ e.eff xs m Q X :=
  ⟨fun h => h.elim (fun ⟨_, hs⟩ => hs) fun ⟨hn, _⟩ => absurd ⟨rfl, rfl, rfl⟩ hn,
    fun h => Or.inl ⟨⟨rfl, rfl, rfl⟩, h⟩⟩

theorem Env.ofTable_cons_ne {e : SpecEntry} {es : List SpecEntry} {f : Sym} (hf : e.name ≠ f)
    {as bs : List Ty} (xs : Tup Val as) (m : Mem 64) (Q : Post bs) (X : XPost) :
    Env.ofTable (e :: es) f as bs xs m Q X ↔ Env.ofTable es f as bs xs m Q X :=
  ⟨fun h => h.elim (fun ⟨h', _⟩ => absurd h'.1 hf) fun ⟨_, h⟩ => h,
    fun h => Or.inr ⟨fun h' => hf h'.1, h⟩⟩

/-- `fn` implements table row `e` under `Γ` (same signature, body satisfies the contract). -/
def SpecEntry.Impl (Γ : Env) (fn : Fn) (e : SpecEntry) : Prop :=
  ∃ h : e.name = fn.name ∧ e.as = fn.as ∧ e.rs = fn.rs,
    ∀ xs m Q X, e.cast h.2.1 h.2.2 xs m Q X → Func.wp Γ fn.body xs m Q X

/-- Build a row implementation from the usual `*_wp` theorem. -/
theorem SpecEntry.Impl.of {Γ : Env} {fn : Fn} {spec : Spec fn.as fn.rs} {noExit : Bool}
    (h : ∀ xs m Q X, spec xs m Q X → Func.wp Γ fn.body xs m Q X) :
    SpecEntry.Impl Γ fn (.ofFn fn spec noExit) := by
  refine ⟨⟨rfl, rfl, rfl⟩, fun xs m Q X hs => ?_⟩
  cases noExit with
  | false => exact h xs m Q X hs
  | true => exact wp_mono (fun _ _ h => h) (fun _ _ _ _ h => h.elim) _ m (h xs m Q _ hs)

/-- Row-by-row implementation of `fns` by `tbl` (extra trailing rows, e.g. externs, allowed). -/
def TableImpl (Γ : Env) : List Fn → List SpecEntry → Prop
  | [], _ => True
  | _ :: _, [] => False
  | fn :: fs, e :: es => SpecEntry.Impl Γ fn e ∧ TableImpl Γ fs es

/-- Soundness of a specification table: every listed function satisfies its own row. -/
theorem Env.ofTable_sound {Γ : Env} {tbl : List SpecEntry} {fs : List Fn}
    (hnd : (fs.map Fn.name).Nodup) (hok : TableImpl Γ fs tbl) :
    ∀ fn ∈ fs, ∀ xs m Q X,
      Env.ofTable tbl fn.name fn.as fn.rs xs m Q X → Func.wp Γ fn.body xs m Q X := by
  induction fs generalizing tbl with
  | nil => intro _ h; nomatch h
  | cons f fs ih =>
    cases tbl with
    | nil => exact hok.elim
    | cons e es =>
      obtain ⟨⟨he, hwp⟩, hrest⟩ := hok
      rw [List.map_cons, List.nodup_cons] at hnd
      intro fn hfn xs m Q X hs
      rcases List.mem_cons.mp hfn with rfl | hmem
      · rcases hs with ⟨_, hs⟩ | ⟨hn, _⟩
        · exact hwp xs m Q X hs
        · exact absurd he hn
      · have hne : e.name ≠ fn.name := fun h =>
          hnd.1 (he.1 ▸ h ▸ List.mem_map_of_mem hmem)
        exact ih hnd.2 hrest fn hmem xs m Q X ((Env.ofTable_cons_ne hne _ _ _ _).mp hs)

/-- `P` holds for every function of the list (a tuple `⟨h₁, …, hₙ, trivial⟩`). -/
def AllFns (P : Fn → Prop) : List Fn → Prop
  | [] => True
  | fn :: fs => P fn ∧ AllFns P fs

theorem AllFns.mem {P : Fn → Prop} : ∀ {fs : List Fn}, AllFns P fs → ∀ fn ∈ fs, P fn
  | _ :: _, h, _, .head _ => h.1
  | _ :: _, h, fn, .tail _ hm => AllFns.mem h.2 fn hm

/-- `ModuleOk` for a module whose functions are implemented row-by-row by `tbl`
(`hwf` is a plain tuple `⟨f₁_wf, …, fₙ_wf, trivial⟩`). -/
theorem Env.ofTable_moduleOk {tbl : List SpecEntry} {M : Module}
    (hchk : M.checkAcyclic = true) (hwf : AllFns Fn.Wf M.fns)
    (hok : TableImpl (Env.ofTable tbl) M.fns tbl) : ModuleOk (Env.ofTable tbl) M := by
  have hnd : (M.fns.map Fn.name).Nodup := by
    simp only [Module.checkAcyclic, Bool.and_eq_true] at hchk
    exact (List.nodup_append.mp (Module.namesNodup_of_checkNamesNodup hchk.1)).1
  exact Module.moduleOk_of_checkAcyclic hchk hwf.mem
    (Env.ofTable_sound hnd hok)

/-- Look up a row of a table with distinct names. -/
theorem Env.ofTable_of_mem {tbl : List SpecEntry} {e : SpecEntry} (he : e ∈ tbl)
    (hnd : (tbl.map SpecEntry.name).Nodup) {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs}
    {X : XPost} (h : e.eff xs m Q X) : Env.ofTable tbl e.name e.as e.rs xs m Q X := by
  induction tbl with
  | nil => nomatch he
  | cons e' es ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp he with rfl | hmem
    · exact (Env.ofTable_cons_self _ _ _ _ _ _).2 h
    · have hne : e'.name ≠ e.name := fun h' => hnd.1 (h' ▸ List.mem_map_of_mem hmem)
      exact (Env.ofTable_cons_ne hne _ _ _ _).2 (ih hmem hnd.2)

/-- A table of `noExit` rows ignores exit continuations (`Compiled.fnSpec_noExit_id`). -/
theorem Env.ofTable_noExit {tbl : List SpecEntry} (h : ∀ e ∈ tbl, e.noExit = true) :
    ∀ f as bs xs m Q X X',
      Env.ofTable tbl f as bs xs m Q X → Env.ofTable tbl f as bs xs m Q X' := by
  induction tbl with
  | nil => intro _ _ _ _ _ _ _ _ h; exact h.elim
  | cons e es ih =>
    intro f as bs xs m Q X X' hs
    rcases hs with ⟨⟨rfl, rfl, rfl⟩, hs⟩ | ⟨hn, hs⟩
    · refine Or.inl ⟨⟨rfl, rfl, rfl⟩, ?_⟩
      have he := h e List.mem_cons_self
      simp only [SpecEntry.cast, SpecEntry.eff, he, ite_true] at hs ⊢
      exact hs
    · exact Or.inr ⟨hn, ih (fun e' he' => h e' (List.mem_cons_of_mem _ he')) _ _ _ _ _ _ _ _ hs⟩

/-! ## 2. Record-update framing (`AgreesExcept`) -/

/-- `s'` agrees with `s` except on the fields overwritten by `mask`
(e.g. `mask := fun t => { t with cur := 0, steps := 0 }`). -/
def AgreesExcept {σ : Type} (mask : σ → σ) (s s' : σ) : Prop := mask s' = mask s

namespace AgreesExcept

variable {σ : Type} {mask : σ → σ} {s s' s'' : σ}

@[refl, simp] theorem refl (mask : σ → σ) (s : σ) : AgreesExcept mask s s := rfl

theorem trans (h₁ : AgreesExcept mask s s') (h₂ : AgreesExcept mask s' s'') :
    AgreesExcept mask s s'' := Eq.trans h₂ h₁

/-- Overwriting masked fields preserves agreement (side condition closes by `rfl`). -/
theorem update (h : AgreesExcept mask s s') (upd : σ → σ)
    (hu : ∀ t, mask (upd t) = mask t := by intro; rfl) : AgreesExcept mask s (upd s') :=
  (hu s').trans h

/-- Unmasked fields are unchanged (side condition closes by `rfl`). -/
theorem get {α : Type} (h : AgreesExcept mask s s') (f : σ → α)
    (hf : ∀ t, f (mask t) = f t := by intro; rfl) : f s' = f s := by
  rw [← hf s', ← hf s, h]

end AgreesExcept

/-! ## 3. Step rules -/

section Rules
variable {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}

theorem wp_load_of {t : Ty} {a : Arg Val i64} {k : Val t → Expr Val Cont rs} {m : Mem 64}
    {v : Val t} (hl : loadVal m t a.val = some v) (hk : wp Γ Q X (k v) m) :
    wp Γ Q X (.load t a k) m :=
  ⟨v, hl, hk⟩

theorem wp_store_sep {t : Ty} {v : Arg Val t} {a : Arg Val i64} {k : Expr Val Cont rs}
    {m : Mem 64} {P R : Mem 64 → Prop}
    (hs : storeOk m t a.val ∧ (P ⋆ R) (storeMem m t a.val v.val))
    (hk : ∀ m', (P ⋆ R) m' → wp Γ Q X k m') : wp Γ Q X (.store v a k) m :=
  ⟨hs.1, hk _ hs.2⟩

theorem wp_jnz_of {c : Arg Val .bool} {e₁ e₂ : Expr Val Cont rs} {m : Mem 64}
    (h₁ : c.val = true → wp Γ Q X e₁ m) (h₂ : c.val = false → wp Γ Q X e₂ m) :
    wp Γ Q X (.jnz c e₁ e₂) m :=
  ⟨h₁, h₂⟩

/-- Measure-based loop rule for a 1-block `group`: the invariant `Inv` holds on entry and every
back-edge re-establishes it at a smaller measure `μ`. -/
theorem wp_loop_inv {ts : List Ty} {m : Mem 64}
    {bodies : Tup Cont [ts] → Blocks Val Cont rs [ts]} {entry : Tup Cont [ts] → Expr Val Cont rs}
    (Inv : Tup Val ts → Mem 64 → Prop) (μ : Tup Val ts → Mem 64 → Nat)
    (hentry : ∀ J : Cont ts, (∀ xs m, Inv xs m → J xs m) → wp Γ Q X (entry (J, ())) m)
    (hbody : ∀ (J : Cont ts) xs m, Inv xs m →
      (∀ ys m', μ ys m' < μ xs m → Inv ys m' → J ys m') →
      wp Γ Q X (Blocks.get (bodies (J, ())) .here xs) m) :
    wp Γ Q X (.group (sig := [ts]) bodies entry) m :=
  wp_loop_group (fun n xs m => Inv xs m ∧ μ xs m = n)
    (fun J _ xs m hJ ⟨hi, hμ⟩ => hbody J xs m hi fun ys m' hlt hi' =>
      hJ _ ys m' (hμ ▸ hlt) ⟨hi', rfl⟩)
    (fun J hJ => hentry J fun xs m hi => hJ _ xs m ⟨hi, rfl⟩)

end Rules

/-! ## 4. Footprint-indexed memory lemmas and `bv_c0` -/

section Mem
variable {R : Mem 64 → Prop} {m : Mem 64}

theorem c0_mul_ofNat (i : BitVec 64) (b : Nat) :
    i * BitVec.ofNat 64 b = BitVec.ofNat 64 (b * i.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mul_mod_mod, Nat.mul_comm]

@[c0_load] theorem c0_load_cell {t : Ty} {a : BitVec 64} {v : Val t}
    (h : (cell a v ⋆ R) m) (hb : t.bytes ≤ 2 ^ 64) : loadVal m t a = some v :=
  loadVal_cell hb h

@[c0_store] theorem c0_store_cell {t : Ty} {a : BitVec 64} {v0 : Val t} (v : Val t)
    (h : (cell a v0 ⋆ R) m) (hb : t.bytes ≤ 2 ^ 64) :
    storeOk m t a ∧ (cell a v ⋆ R) (storeMem m t a v) :=
  store_cell v hb h

/-- C0 array indexing `((T *)a)[i]` lowers to `a + i * sizeof(T)`. -/
@[c0_load] theorem c0_load_array {t : Ty} {a i w : BitVec 64} {xs : List (Val t)}
    (h : (array a xs ⋆ R) m) (hi : i.toNat < xs.length)
    (hw : w = BitVec.ofNat 64 t.bytes) (hb : t.bytes ≤ 2 ^ 64) :
    loadVal m t (a + i * w) = some (xs[i.toNat]'hi) := by
  rw [hw, c0_mul_ofNat]; exact loadVal_array hb hi h

/-- Byte arrays: `((u8 *)a)[i]` lowers to `a + i`. -/
@[c0_load] theorem c0_load_array8 {a i : BitVec 64} {xs : List (Val i8)}
    (h : (array a xs ⋆ R) m) (hi : i.toNat < xs.length) :
    loadVal m i8 (a + i) = some (xs[i.toNat]'hi) := by
  simpa using c0_load_array (w := 1) h hi rfl (by decide)

@[c0_store] theorem c0_store_array {t : Ty} {a i w : BitVec 64} {xs : List (Val t)} (v : Val t)
    (h : (array a xs ⋆ R) m) (hi : i.toNat < xs.length)
    (hw : w = BitVec.ofNat 64 t.bytes) (hb : t.bytes ≤ 2 ^ 64) :
    storeOk m t (a + i * w) ∧ (array a (xs.set i.toNat v) ⋆ R) (storeMem m t (a + i * w) v) := by
  rw [hw, c0_mul_ofNat]; exact store_array v hb hi h

@[c0_store] theorem c0_store_array8 {a i : BitVec 64} {xs : List (Val i8)} (v : Val i8)
    (h : (array a xs ⋆ R) m) (hi : i.toNat < xs.length) :
    storeOk m i8 (a + i) ∧ (array a (xs.set i.toNat v) ⋆ R) (storeMem m i8 (a + i) v) := by
  simpa using c0_store_array (w := 1) v h hi rfl (by decide)

@[c0_load] theorem c0_load_array64 {a i : BitVec 64} {xs : List (BitVec 64)}
    (h : (array64 a xs ⋆ R) m) (hi : i.toNat < xs.length) :
    loadVal m i64 (a + i * 8) = some (xs[i.toNat]'hi) := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, c0_mul_ofNat]
  exact loadVal_array64 hi h

@[c0_store] theorem c0_store_array64 {a i : BitVec 64} {xs : List (BitVec 64)} (v : BitVec 64)
    (h : (array64 a xs ⋆ R) m) (hi : i.toNat < xs.length) :
    storeOk m i64 (a + i * 8) ∧
      (array64 a (xs.set i.toNat v) ⋆ R) (storeMem m i64 (a + i * 8) v) := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, c0_mul_ofNat]
  exact store_array64 v hi h

end Mem

section BvC0

@[bv_c0] theorem bv_c0_ult_true {n : Nat} (a b : BitVec n) :
    (a.ult b = true) = (a.toNat < b.toNat) := by simp [BitVec.ult]
@[bv_c0] theorem bv_c0_ult_false {n : Nat} (a b : BitVec n) :
    (a.ult b = false) = ¬(a.toNat < b.toNat) := by simp [BitVec.ult]
@[bv_c0] theorem bv_c0_ule_true {n : Nat} (a b : BitVec n) :
    (a.ule b = true) = (a.toNat ≤ b.toNat) := by simp [BitVec.ule]
@[bv_c0] theorem bv_c0_ule_false {n : Nat} (a b : BitVec n) :
    (a.ule b = false) = ¬(a.toNat ≤ b.toNat) := by simp [BitVec.ule]
@[bv_c0] theorem bv_c0_beq_true {n : Nat} (a b : BitVec n) : ((a == b) = true) = (a = b) := by
  simp only [beq_iff_eq]
@[bv_c0] theorem bv_c0_beq_false {n : Nat} (a b : BitVec n) : ((a == b) = false) = ¬(a = b) := by
  simp only [beq_eq_false_iff_ne, ne_eq]
@[bv_c0] theorem bv_c0_bne_true {n : Nat} (a b : BitVec n) : ((a != b) = true) = ¬(a = b) := by
  simp only [bne_iff_ne, ne_eq]
@[bv_c0] theorem bv_c0_bne_false {n : Nat} (a b : BitVec n) : ((a != b) = false) = (a = b) := by
  simp only [bne_eq_false_iff_eq]
@[bv_c0] theorem bv_c0_lt {n : Nat} (a b : BitVec n) : (a < b) = (a.toNat < b.toNat) :=
  propext BitVec.lt_def
@[bv_c0] theorem bv_c0_le {n : Nat} (a b : BitVec n) : (a ≤ b) = (a.toNat ≤ b.toNat) :=
  propext BitVec.le_def

attribute [bv_c0] BitVec.toNat_add BitVec.toNat_sub BitVec.toNat_mul BitVec.toNat_ofNat
  BitVec.toNat_setWidth BitVec.toNat_ofBool BitVec.toNat_ofFin Nat.add_mod_mod Nat.mod_add_mod
  BitVec.signExtend_eq_setWidth_of_msb_false

end BvC0

end LeanQbe.T

/-! ## 5. Tactics -/

namespace LeanQbe.T.C0Step

open Lean Meta Elab Tactic

/-- Frame inference: close `(P ⋆ ?R) m` (or any `⋆`-permutation) from a hypothesis by AC
matching, instantiating metavariables (Kraken `ecancel`). -/
macro "c0_frame" : tactic => `(tactic| ecancel)

/-- Discharge C0 arithmetic side goals (bounds, address equalities, sizes). -/
macro "c0_bound" : tactic => `(tactic| first
  | assumption | rfl | decide | omega | bv_omega
  | (simp only [bv_c0, Nat.reducePow, Nat.reduceMod] at *; omega)
  | (simp only [bv_c0, Nat.reducePow, Nat.reduceMod] at *; done))

/-- Pure-`let` unfolding for `wp` (the `t_wp_unfold` set without `load`/`store`/`jnz`). -/
macro "c0_let_simp" : tactic =>
  `(tactic| simp only [
    LeanQbe.T.op1_eq_mk, LeanQbe.T.op2_eq_mk, LeanQbe.T.op3_eq_mk,
    LeanQbe.T.wp_let_copy_eq, LeanQbe.T.wp_let_add_eq, LeanQbe.T.wp_let_sub_eq,
    LeanQbe.T.wp_let_mul_eq, LeanQbe.T.wp_let_neg_eq, LeanQbe.T.wp_let_and_eq,
    LeanQbe.T.wp_let_or_eq, LeanQbe.T.wp_let_xor_eq, LeanQbe.T.wp_let_not_eq,
    LeanQbe.T.wp_let_shl_eq, LeanQbe.T.wp_let_lshr_eq, LeanQbe.T.wp_let_ashr_eq,
    LeanQbe.T.wp_let_rotl_eq, LeanQbe.T.wp_let_rotr_eq,
    LeanQbe.T.wp_let_clz_eq, LeanQbe.T.wp_let_ctz_eq, LeanQbe.T.wp_let_popcnt_eq,
    LeanQbe.T.wp_let_cmp_eq, LeanQbe.T.wp_let_select_eq, LeanQbe.T.wp_let_zext_eq,
    LeanQbe.T.wp_let_sext_eq, LeanQbe.T.wp_let_trunc_eq, LeanQbe.T.wp_let_ofBool_eq,
    LeanQbe.T.wp_let_udiv0_eq, LeanQbe.T.wp_let_sdiv0_eq, LeanQbe.T.wp_let_mkpair_eq,
    LeanQbe.T.wp_let_unpair_eq, LeanQbe.T.wp_let_bitcast_eq,
    LeanQbe.T.wp_let_udiv_eq, LeanQbe.T.wp_let_urem_eq,
    LeanQbe.T.wp_jump, LeanQbe.T.wp_ret, LeanQbe.T.wp_exit,
    LeanQbe.T.OpCode.eq, LeanQbe.T.OpCode.ne, LeanQbe.T.OpCode.ult, LeanQbe.T.OpCode.ule,
    LeanQbe.T.OpCode.ugt, LeanQbe.T.OpCode.uge, LeanQbe.T.OpCode.slt, LeanQbe.T.OpCode.sle,
    LeanQbe.T.OpCode.sgt, LeanQbe.T.OpCode.sge,
    LeanQbe.T.vals_nil, LeanQbe.T.vals_cons, LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm,
    LeanQbe.T.Blocks.get_here, LeanQbe.T.Blocks.get_there,
    LeanQbe.T.Ty.hasFloat_vec, LeanQbe.T.Ty.hasFloat, LeanQbe.T.Ty.isFloatTree,
    LeanQbe.T.evalBits_eq_beq, LeanQbe.T.evalBits_ne_bne,
    LeanQbe.T.evalBits_ult_eq, LeanQbe.T.evalBits_ule_eq, LeanQbe.T.evalBits_ugt_eq,
    LeanQbe.T.evalBits_uge_eq, LeanQbe.T.evalBits_slt_eq, LeanQbe.T.evalBits_sle_eq,
    LeanQbe.T.evalBits_sgt_eq, LeanQbe.T.evalBits_sge_eq,
    LeanQbe.T.evalBool_eq_beq, LeanQbe.T.evalBool_ne_bne,
    LeanQbe.T.lift1, LeanQbe.T.lift2, LeanQbe.T.lift3, LeanQbe.T.liftCmp,
    LeanQbe.T.shl_three, cast_eq, ite_self, ite_true, ite_false,
    Bool.false_eq_true, Bool.true_eq_false, BitVec.reduceToNat, Nat.reduceMod,
    BitVec.reduceSignExtend, BitVec.reduceSetWidth, BitVec.reduceAdd, BitVec.reduceMul])

/-- Normalize a branch hypothesis with `bv_c0`. -/
macro "c0_cond" h:ident : tactic =>
  `(tactic| (try simp only [bv_c0, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true,
    Bool.not_eq_false, beq_iff_eq, bne_iff_ne, ne_eq] at $h:ident))

/-- Top-level `⋆` clauses of a `sep`-tree predicate (partially applied `sep p q`). -/
private meta partial def sepClauses (e : Lean.Expr) : List Lean.Expr :=
  if e.isAppOf ``Std.ExtHashMap.sep && e.getAppNumArgs ≥ 2 then
    sepClauses (e.getArg! (e.getAppNumArgs - 2)) ++ sepClauses (e.getArg! (e.getAppNumArgs - 1))
  else [e]

/-- Footprint heads occurring in the `⋆` hypotheses of the main goal (newest first). -/
private meta def footprints : TacticM (Array Name) := withMainContext do
  let mut keys : Array Name := #[]
  for d in (← getLCtx).decls.toArray.reverse do
    let some d := d | continue
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if t.isAppOf ``Std.ExtHashMap.sep && t.getAppNumArgs ≥ 3 then
      let p := t.appFn!
      for c in sepClauses p do
        if let some k := c.getAppFn.constName? then
          unless keys.contains k do keys := keys.push k
  return keys

/-- Run `tac` on goal `g`, requiring it to be closed. -/
private meta def closeWith (g : MVarId) (tac : TSyntax `tactic) : TacticM Bool := do
  if ← g.isAssigned then return true
  let s ← saveState
  try
    setGoals [g]
    evalTactic tac
    if (← getUnsolvedGoals).isEmpty then return true
    s.restore; return false
  catch _ => s.restore; return false

/-- Try `apply nm` on `g`, closing frame goals with `c0_frame` and the rest with `c0_bound`. -/
private meta def tryMemLemma (g : MVarId) (nm : Name) : TacticM Bool := do
  let s ← saveState
  try
    let gs ← withReducible <| g.apply (← mkConstWithFreshMVarLevels nm)
    for g' in gs do
      let ty ← instantiateMVars (← g'.getType)
      if ty.isAppOf ``Std.ExtHashMap.sep then
        unless ← withReducible (closeWith g' (← `(tactic| c0_frame))) do throwError "frame"
    for g' in gs do
      if ← g'.isAssigned then continue
      if ← isProp (← g'.getType) then
        unless ← closeWith g' (← `(tactic| c0_bound)) do throwError "side"
    for g' in gs do
      unless ← g'.isAssigned do throwError "unassigned"
    return true
  catch _ => s.restore; return false

/-- Close a `loadVal m t a = some ?v` (`isLoad`) or `storeOk … ∧ (?P ⋆ ?R) (storeMem …)` goal
with a footprint-indexed `c0_load` / `c0_store` lemma. -/
meta def memSolve (isLoad : Bool) (g : MVarId) : TacticM Unit := do
  setGoals [g]
  evalTactic (← `(tactic| try simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm]))
  let g ← getMainGoal
  let keys ← footprints
  let env ← getEnv
  for k in keys do
    for nm in C0Step.c0MemLemmas env isLoad k do
      if ← tryMemLemma g nm then return
  throwError "c0_step: no @[{if isLoad then "c0_load" else "c0_store"}] lemma applies to{
    indentExpr (← g.getType)}\nfootprints: {keys}"

/-- Is `bodies` (a `Tup Cont sig → Blocks …` lambda) free of back-edges (a pure join point)? -/
private meta def isJoin (bodies : Lean.Expr) : Bool :=
  match bodies with
  | .lam _ _ b _ => !b.hasLooseBVars
  | _ => false

/-- Find a join-continuation hypothesis `∀ xs m, wp … → J xs m` for the fvar `J`. -/
private meta def findJoinHyp (J : FVarId) : TacticM (Option Lean.Expr) := withMainContext do
  for d in (← getLCtx).decls.toArray.reverse do
    let some d := d | continue
    let ok ← forallTelescopeReducing d.type fun xs concl => do
      if xs.size < 1 then return false
      let prem ← inferType xs[xs.size - 1]!
      return concl.getAppFn.isFVarOf J && prem.isAppOf ``LeanQbe.T.wp
    if ok then return some d.toExpr
  return none

/-- After a store, drop the `⋆` hypotheses about the old memory `m0` (and `m0` itself). -/
private meta def clearStale (m0 : Lean.Expr) : TacticM Unit := withMainContext do
  let .fvar mId := m0 | return
  for d in (← getLCtx).decls.toArray.reverse do
    let some d := d | continue
    let t ← instantiateMVars d.type
    if t.isAppOf ``Std.ExtHashMap.sep && t.appArg! == m0 then
      try liftMetaTactic1 fun g => some <$> g.clear d.fvarId catch _ => pure ()
  try liftMetaTactic1 fun g => some <$> g.clear mId catch _ => pure ()

/-- One symbolic-execution step on the main goal; `false` if no step applies. -/
meta def stepOnce : TacticM Bool := withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let ty := ty.headBeta
  if ty.isAppOf ``LeanQbe.T.Func.wp && ty.getAppNumArgs ≥ 4 then
    let f := ty.getArg! 3
    let some c := f.getAppFn.constName? | return false
    evalTactic (← `(tactic| (unfold LeanQbe.T.Func.wp $(mkIdent c):ident; try c0_let_simp)))
    return true
  if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 then
    let e := (ty.getArg! 4).headBeta
    match e.getAppFn.constName? with
    | some ``LeanQbe.T.Expr.let_ | some ``LeanQbe.T.Expr.jump | some ``LeanQbe.T.Expr.ret =>
      evalTactic (← `(tactic| c0_let_simp)); return true
    | some ``LeanQbe.T.Expr.load =>
      let gs ← g.apply (← mkConstWithFreshMVarLevels ``LeanQbe.T.wp_load_of)
      let [hl, hk] := gs.take 2 | return false
      memSolve true hl
      setGoals [hk]
      evalTactic (← `(tactic| (try c0_let_simp)))
      return true
    | some ``LeanQbe.T.Expr.store =>
      let m0 := ty.getArg! 5
      let gs ← g.apply (← mkConstWithFreshMVarLevels ``LeanQbe.T.wp_store_sep)
      let [hs, hk] := gs.take 2 | return false
      memSolve false hs
      setGoals [hk]
      let mId := mkIdent `m
      let hmId := mkIdent `hm
      evalTactic (← `(tactic| intro $mId:ident $hmId:ident))
      evalTactic (← `(tactic| try simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm,
        Std.ExtHashMap.sep_emp] at $hmId:ident))
      clearStale m0
      evalTactic (← `(tactic| try c0_let_simp))
      return true
    | some ``LeanQbe.T.Expr.jnz =>
      let hc := mkIdent `hc
      evalTactic (← `(tactic|
        refine LeanQbe.T.wp_jnz_of (fun $hc:ident => ?_) (fun $hc:ident => ?_)))
      evalTactic (← `(tactic| all_goals
        (try simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm] at $hc:ident)
        c0_cond $hc
        try (exfalso; c0_bound)
        try c0_let_simp))
      return true
    | some ``LeanQbe.T.Expr.group =>
      if e.getAppNumArgs == 6 && isJoin (e.getArg! 4) then
        let J := mkIdent `J
        let hJ := mkIdent `hJ
        evalTactic (← `(tactic| refine LeanQbe.T.wp_unroll_group fun $J:ident $hJ:ident => ?_))
        evalTactic (← `(tactic| try c0_let_simp))
        return true
      return false
    | some ``LeanQbe.T.Blocks.get =>
      evalTactic (← `(tactic| c0_let_simp)); return true
    | _ => return false
  if let .fvar J := ty.getAppFn then
    if let some h ← findJoinHyp J then
      let gs ← g.apply h
      setGoals gs
      evalTactic (← `(tactic| (try c0_let_simp)))
      return true
  return false

/-- Repeat `stepOnce` on every goal until no step applies. -/
meta partial def steps (fuel : Nat) : TacticM Unit := do
  if fuel = 0 then return
  let gs ← getUnsolvedGoals
  let mut out : Array MVarId := #[]
  for g in gs do
    if ← g.isAssigned then continue
    setGoals [g]
    let progressed ← try stepOnce catch _ => pure false
    if progressed then
      steps (fuel - 1)
    out := out ++ (← getUnsolvedGoals)
  setGoals out.toList

/-- Discharge a `call` with the environment hypothesis `h : ∀ args m Q X, spec … → Γ f …`;
the remaining goal is the callee contract with the continuation as postcondition. -/
macro "c0_call" h:term : tactic =>
  `(tactic| (refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_); try c0_let_simp))

/-- One C0 symbolic-execution step (see module docs). -/
elab "c0_step" : tactic => do
  unless ← stepOnce do throwError "c0_step: no step applies"

/-- Symbolically execute all straight-line code, branches and join points; stops at loops,
calls, returns, and jumps to loop heads. -/
elab "c0_steps" : tactic => steps 10000

end LeanQbe.T.C0Step
