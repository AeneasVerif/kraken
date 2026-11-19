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
3. **Rules.** `wp_load_of`, `wp_store_sep`, `wp_jnz_of`, `wp_{udiv,urem,sdiv,srem}_of`, and the
   measure-based loop rule `wp_loop_inv`.
4. **Memory lemmas.** Footprint-indexed `@[c0_load]` / `@[c0_store]` lemmas for `cell`, `array`
   (including `i32` / `i64` dynamic-offset `ward` addressing `base + ((off + k) <<< 2)`,
   `base + off * 4 + k * 4`, and `u32`/`u64`-indexed forms), `array64`, slice framing
   (`array_slice_focus` / `ward_slice_focus`), plus the `bv_c0` simp set.
5. **Tactics.** `c0_frame` (Kraken `ecancel`), `c0_bound` (`omega` / `bv_omega` after `bv_c0`),
   `c0_div_bound`, `c0_let_simp` (shared with `Logic/Rules.lean`'s `t_wp_unfold_all`), `c0_step`
   (one symbolic-execution step), `c0_steps` (straight-line steps, branches, non-recursive joins,
   and `trace[c0_step]` / crisp diagnostics on unmatched memory goals), and `c0_steps!` (strict
   memory-goal erroring).
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

theorem wp_udiv_of {n : Nat} {args : Tup (Arg Val) [.bits n, .bits n]}
    {k : Tup Val [.bits n] → Expr Val Cont rs} {m : Mem 64}
    (hb : args.2.1.val ≠ 0) (hk : wp Γ Q X (k (args.1.val / args.2.1.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.udiv n) args) k) m := by
  rw [wp_let_udiv_eq]; exact ⟨hb, hk⟩

theorem wp_urem_of {n : Nat} {args : Tup (Arg Val) [.bits n, .bits n]}
    {k : Tup Val [.bits n] → Expr Val Cont rs} {m : Mem 64}
    (hb : args.2.1.val ≠ 0) (hk : wp Γ Q X (k (args.1.val % args.2.1.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.urem n) args) k) m := by
  rw [wp_let_urem_eq]; exact ⟨hb, hk⟩

theorem wp_sdiv_of {n : Nat} {args : Tup (Arg Val) [.bits n, .bits n]}
    {k : Tup Val [.bits n] → Expr Val Cont rs} {m : Mem 64}
    (hd : sdivDefined args.1.val args.2.1.val = true)
    (hk : wp Γ Q X (k (args.1.val.sdiv args.2.1.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sdiv n) args) k) m := by
  rw [wp_let_sdiv_eq]; exact ⟨hd, hk⟩

theorem wp_srem_of {n : Nat} {args : Tup (Arg Val) [.bits n, .bits n]}
    {k : Tup Val [.bits n] → Expr Val Cont rs} {m : Mem 64}
    (hd : sdivDefined args.1.val args.2.1.val = true)
    (hk : wp Γ Q X (k (args.1.val.srem args.2.1.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.srem n) args) k) m := by
  rw [wp_let_srem_eq]; exact ⟨hd, hk⟩

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

/-! ### Address arithmetic & slice framing (`ward` / `i32` / `i64` arrays) -/

theorem c0_mul_ofNat (i : BitVec 64) (b : Nat) :
    i * BitVec.ofNat 64 b = BitVec.ofNat 64 (b * i.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mul_mod_mod, Nat.mul_comm]

theorem c0_add_mul_ofNat (off k : BitVec 64) (b : Nat) :
    (off + k) * BitVec.ofNat 64 b = BitVec.ofNat 64 (b * (off.toNat + k.toNat)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mul_mod_mod, Nat.mul_comm]

theorem c0_add_shl2_ofNat (off k : BitVec 64) :
    (off + k) <<< 2 = BitVec.ofNat 64 (4 * (off.toNat + k.toNat)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.shiftLeft_eq, Nat.mul_comm, Nat.mul_mod_mod]

theorem c0_add_shl3_ofNat (off k : BitVec 64) :
    (off + k) <<< 3 = BitVec.ofNat 64 (8 * (off.toNat + k.toNat)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.shiftLeft_eq, Nat.mul_comm, Nat.mul_mod_mod]

theorem c0_u32_mul_ofNat (i : BitVec 32) (b : Nat) :
    i.setWidth 64 * BitVec.ofNat 64 b = BitVec.ofNat 64 (b * i.toNat) := by
  rw [c0_mul_ofNat, zext_toNat i (by decide)]

theorem c0_u32_shl2 (i : BitVec 32) :
    i.setWidth 64 <<< 2 = BitVec.ofNat 64 (4 * i.toNat) := by
  rw [shl_two, zext_toNat i (by decide)]

theorem c0_u32_shl3 (i : BitVec 32) :
    i.setWidth 64 <<< 3 = BitVec.ofNat 64 (8 * i.toNat) := by
  rw [shl_three, zext_toNat i (by decide)]

theorem c0_u32_add_shl2 (off k : BitVec 32) :
    (off.setWidth 64 + k.setWidth 64) <<< 2 = BitVec.ofNat 64 (4 * (off.toNat + k.toNat)) := by
  rw [c0_add_shl2_ofNat, zext_toNat off (by decide), zext_toNat k (by decide)]

theorem c0_u32_add_mul_ofNat (off k : BitVec 32) (b : Nat) :
    (off.setWidth 64 + k.setWidth 64) * BitVec.ofNat 64 b =
      BitVec.ofNat 64 (b * (off.toNat + k.toNat)) := by
  rw [c0_add_mul_ofNat, zext_toNat off (by decide), zext_toNat k (by decide)]

theorem c0_ptr_off_mul (a off k : BitVec 64) (b : Nat) :
    a + off * BitVec.ofNat 64 b + k * BitVec.ofNat 64 b =
      a + BitVec.ofNat 64 (b * (off.toNat + k.toNat)) := by
  rw [c0_mul_ofNat, c0_mul_ofNat, ptr_add_ofNat, ← Nat.mul_add]

theorem c0_ptr_off_shl2_mul4 (a off k : BitVec 64) :
    a + (off <<< 2) + k * 4 = a + BitVec.ofNat 64 (4 * (off.toNat + k.toNat)) := by
  rw [shl_two, show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat,
    ptr_add_ofNat, ← Nat.mul_add]

theorem c0_ptr_off_shl2_shl2 (a off k : BitVec 64) :
    a + (off <<< 2) + (k <<< 2) = a + BitVec.ofNat 64 (4 * (off.toNat + k.toNat)) := by
  rw [shl_two, shl_two, ptr_add_ofNat, ← Nat.mul_add]

theorem c0_ptr_off_add4 (a off d : BitVec 64) (hd : d.toNat % 4 = 0) :
    a + off * 4 + d = a + BitVec.ofNat 64 (4 * (off.toNat + d.toNat / 4)) := by
  have hd_eq : d = BitVec.ofNat 64 (4 * (d.toNat / 4)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 4 * (d.toNat / 4) < 2 ^ 64)]
    omega
  conv => lhs; rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat, hd_eq,
    ptr_add_ofNat, ← Nat.mul_add]

theorem c0_ptr_off_shl2_add4 (a off d : BitVec 64) (hd : d.toNat % 4 = 0) :
    a + (off <<< 2) + d = a + BitVec.ofNat 64 (4 * (off.toNat + d.toNat / 4)) := by
  rw [shl_two, show BitVec.ofNat 64 (4 * off.toNat) = off * 4 from
    (c0_mul_ofNat off 4).symm]
  exact c0_ptr_off_add4 a off d hd

/-- Split `array a xs` into the sub-slice `[off, off + len)` at
`a + BitVec.ofNat 64 (t.bytes * off)` and its prefix/suffix frame. -/
theorem array_slice_focus {t : Ty} (a : BitVec 64) (xs : List (Val t))
    {off len : Nat} (hlen : off + len ≤ xs.length) :
    array a xs =
      (array (a + BitVec.ofNat 64 (t.bytes * off)) ((xs.drop off).take len) ⋆
        (array a (xs.take off) ⋆
          array (a + BitVec.ofNat 64 (t.bytes * (off + len)))
            (xs.drop (off + len)))) := by
  have hsplit : xs = xs.take off ++ (xs.drop off).take len ++ xs.drop (off + len) := by
    rw [List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]
  conv => lhs; rw [hsplit]
  rw [array_append, array_append, List.length_append,
    List.length_take_of_le (by omega),
    List.length_take_of_le (by simp only [List.length_drop]; omega)]
  ac_rfl

/-- Rebuild `array a` after replacing the sub-slice `[off, off + len)` with `ys`. -/
theorem array_slice_replace {t : Ty} (a : BitVec 64) (xs ys : List (Val t))
    {off len : Nat} (hlen : off + len ≤ xs.length) (hy : ys.length = len) :
    array a (xs.take off ++ ys ++ xs.drop (off + len)) =
      (array (a + BitVec.ofNat 64 (t.bytes * off)) ys ⋆
        (array a (xs.take off) ⋆
          array (a + BitVec.ofNat 64 (t.bytes * (off + len)))
            (xs.drop (off + len)))) := by
  rw [array_append, array_append, List.length_append,
    List.length_take_of_le (by omega), hy]
  ac_rfl

/-- `D-Plain` 32-bit `ward` arena slice focus at `a + (off <<< 2)`. -/
theorem ward_slice_focus (a : BitVec 64) (xs : List (BitVec 32))
    {off : BitVec 64} {len : Nat} (hlen : off.toNat + len ≤ xs.length) :
    array (t := i32) a xs =
      (array (t := i32) (a + (off <<< 2)) ((xs.drop off.toNat).take len) ⋆
        (array (t := i32) a (xs.take off.toNat) ⋆
          array (t := i32) (a + BitVec.ofNat 64 (4 * (off.toNat + len)))
            (xs.drop (off.toNat + len)))) := by
  rw [shl_two]; exact array_slice_focus (t := i32) a xs hlen

/-- `D-Plain` 32-bit `ward` arena slice rebuild at `a + (off <<< 2)`. -/
theorem ward_slice_replace (a : BitVec 64) (xs ys : List (BitVec 32))
    {off : BitVec 64} {len : Nat} (hlen : off.toNat + len ≤ xs.length) (hy : ys.length = len) :
    array (t := i32) a (xs.take off.toNat ++ ys ++ xs.drop (off.toNat + len)) =
      (array (t := i32) (a + (off <<< 2)) ys ⋆
        (array (t := i32) a (xs.take off.toNat) ⋆
          array (t := i32) (a + BitVec.ofNat 64 (4 * (off.toNat + len)))
            (xs.drop (off.toNat + len)))) := by
  rw [shl_two]; exact array_slice_replace (t := i32) a xs ys hlen hy

/-- `D-Plain` 32-bit `ward` arena slice focus at `a + off * 4`. -/
theorem ward_slice_focus_mul (a : BitVec 64) (xs : List (BitVec 32))
    {off : BitVec 64} {len : Nat} (hlen : off.toNat + len ≤ xs.length) :
    array (t := i32) a xs =
      (array (t := i32) (a + off * 4) ((xs.drop off.toNat).take len) ⋆
        (array (t := i32) a (xs.take off.toNat) ⋆
          array (t := i32) (a + BitVec.ofNat 64 (4 * (off.toNat + len)))
            (xs.drop (off.toNat + len)))) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
  exact array_slice_focus (t := i32) a xs hlen

/-- `D-Plain` 32-bit `ward` arena slice rebuild at `a + off * 4`. -/
theorem ward_slice_replace_mul (a : BitVec 64) (xs ys : List (BitVec 32))
    {off : BitVec 64} {len : Nat} (hlen : off.toNat + len ≤ xs.length) (hy : ys.length = len) :
    array (t := i32) a (xs.take off.toNat ++ ys ++ xs.drop (off.toNat + len)) =
      (array (t := i32) (a + off * 4) ys ⋆
        (array (t := i32) a (xs.take off.toNat) ⋆
          array (t := i32) (a + BitVec.ofNat 64 (4 * (off.toNat + len)))
            (xs.drop (off.toNat + len)))) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
  exact array_slice_replace (t := i32) a xs ys hlen hy

/-- 64-bit word array slice focus at `a + BitVec.ofNat 64 (8 * off)`. -/
theorem array64_slice_focus (a : BitVec 64) (xs : List (BitVec 64))
    {off len : Nat} (hlen : off + len ≤ xs.length) :
    array64 a xs =
      (array64 (a + BitVec.ofNat 64 (8 * off)) ((xs.drop off).take len) ⋆
        (array64 a (xs.take off) ⋆
          array64 (a + BitVec.ofNat 64 (8 * (off + len)))
            (xs.drop (off + len)))) := by
  simp only [array64_eq_array]; exact array_slice_focus (t := i64) a xs hlen

/-- 64-bit word array slice rebuild at `a + BitVec.ofNat 64 (8 * off)`. -/
theorem array64_slice_replace (a : BitVec 64) (xs ys : List (BitVec 64))
    {off len : Nat} (hlen : off + len ≤ xs.length) (hy : ys.length = len) :
    array64 a (xs.take off ++ ys ++ xs.drop (off + len)) =
      (array64 (a + BitVec.ofNat 64 (8 * off)) ys ⋆
        (array64 a (xs.take off) ⋆
          array64 (a + BitVec.ofNat 64 (8 * (off + len)))
            (xs.drop (off + len)))) := by
  simp only [array64_eq_array]; exact array_slice_replace (t := i64) a xs ys hlen hy

/-! ### Cells -/

@[c0_load] theorem c0_load_cell {t : Ty} {a : BitVec 64} {v : Val t}
    (h : (cell a v ⋆ R) m) (hb : t.bytes ≤ 2 ^ 64) : loadVal m t a = some v :=
  loadVal_cell hb h

@[c0_store] theorem c0_store_cell {t : Ty} {a : BitVec 64} {v0 : Val t} (v : Val t)
    (h : (cell a v0 ⋆ R) m) (hb : t.bytes ≤ 2 ^ 64) :
    storeOk m t a ∧ (cell a v ⋆ R) (storeMem m t a v) :=
  store_cell v hb h

/-! ### Generic `array` and `array64` access (registered first for backwards compatibility) -/

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

@[c0_load] theorem c0_load_array_add_zero {t : Ty} {a : BitVec 64} {xs : List (Val t)}
    (h : (array a xs ⋆ R) m) (hi : 0 < xs.length) (hb : t.bytes ≤ 2 ^ 64) :
    loadVal m t (a + 0#64) = some (xs[0]'hi) := by
  simpa using loadVal_array (i := 0) hb hi h

@[c0_store] theorem c0_store_array_add_zero {t : Ty} {a : BitVec 64} {xs : List (Val t)}
    (v : Val t) (h : (array a xs ⋆ R) m) (hi : 0 < xs.length) (hb : t.bytes ≤ 2 ^ 64) :
    storeOk m t (a + 0#64) ∧ (array a (xs.set 0 v) ⋆ R) (storeMem m t (a + 0#64) v) := by
  simpa using store_array (i := 0) v hb hi h

@[c0_load] theorem c0_load_array_add_zero_imm {t : Ty} {a : BitVec 64} {xs : List (Val t)}
    (h : (array a xs ⋆ R) m) (hi : 0 < xs.length) (hb : t.bytes ≤ 2 ^ 64) :
    loadVal m t (a + (0 : BitVec 64)) = some (xs[0]'hi) := by
  simpa using loadVal_array (i := 0) hb hi h

@[c0_store] theorem c0_store_array_add_zero_imm {t : Ty} {a : BitVec 64} {xs : List (Val t)}
    (v : Val t) (h : (array a xs ⋆ R) m) (hi : 0 < xs.length) (hb : t.bytes ≤ 2 ^ 64) :
    storeOk m t (a + (0 : BitVec 64)) ∧
      (array a (xs.set 0 v) ⋆ R) (storeMem m t (a + (0 : BitVec 64)) v) := by
  simpa using store_array (i := 0) v hb hi h

@[c0_load] theorem c0_load_array_zero {t : Ty} {a : BitVec 64} {xs : List (Val t)}
    (h : (array a xs ⋆ R) m) (hi : 0 < xs.length) (hb : t.bytes ≤ 2 ^ 64) :
    loadVal m t a = some (xs[0]'hi) := by
  simpa using loadVal_array (i := 0) hb hi h

@[c0_store] theorem c0_store_array_zero {t : Ty} {a : BitVec 64} {xs : List (Val t)} (v : Val t)
    (h : (array a xs ⋆ R) m) (hi : 0 < xs.length) (hb : t.bytes ≤ 2 ^ 64) :
    storeOk m t a ∧ (array a (xs.set 0 v) ⋆ R) (storeMem m t a v) := by
  simpa using store_array (i := 0) v hb hi h

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

@[c0_load] theorem c0_load_array64_add_zero {a : BitVec 64} {xs : List (BitVec 64)}
    (h : (array64 a xs ⋆ R) m) (hi : 0 < xs.length) :
    loadVal m i64 (a + 0#64) = some (xs[0]'hi) := by
  simpa using loadVal_array64 (i := 0) hi h

@[c0_store] theorem c0_store_array64_add_zero {a : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) (h : (array64 a xs ⋆ R) m) (hi : 0 < xs.length) :
    storeOk m i64 (a + 0#64) ∧ (array64 a (xs.set 0 v) ⋆ R) (storeMem m i64 (a + 0#64) v) := by
  simpa using store_array64 (i := 0) v hi h

@[c0_load] theorem c0_load_array64_add_zero_imm {a : BitVec 64} {xs : List (BitVec 64)}
    (h : (array64 a xs ⋆ R) m) (hi : 0 < xs.length) :
    loadVal m i64 (a + (0 : BitVec 64)) = some (xs[0]'hi) := by
  simpa using loadVal_array64 (i := 0) hi h

@[c0_store] theorem c0_store_array64_add_zero_imm {a : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) (h : (array64 a xs ⋆ R) m) (hi : 0 < xs.length) :
    storeOk m i64 (a + (0 : BitVec 64)) ∧
      (array64 a (xs.set 0 v) ⋆ R) (storeMem m i64 (a + (0 : BitVec 64)) v) := by
  simpa using store_array64 (i := 0) v hi h

@[c0_load] theorem c0_load_array64_zero {a : BitVec 64} {xs : List (BitVec 64)}
    (h : (array64 a xs ⋆ R) m) (hi : 0 < xs.length) :
    loadVal m i64 a = some (xs[0]'hi) := by
  simpa using loadVal_array64 (i := 0) hi h

@[c0_store] theorem c0_store_array64_zero {a : BitVec 64} {xs : List (BitVec 64)} (v : BitVec 64)
    (h : (array64 a xs ⋆ R) m) (hi : 0 < xs.length) :
    storeOk m i64 a ∧ (array64 a (xs.set 0 v) ⋆ R) (storeMem m i64 a v) := by
  simpa using store_array64 (i := 0) v hi h

/-! ### `i32` (`ward` arena) dynamic-offset & `u32`/`u64`-indexed array access -/

@[c0_load] theorem c0_load_array32_u32_off_shl2 {a : BitVec 64} {off k : BitVec 32}
    {xs : List (BitVec 32)} (h : (array (t := i32) a xs ⋆ R) m)
    (hi : off.toNat + k.toNat < xs.length) :
    loadVal m i32 (a + ((off.setWidth 64 + k.setWidth 64) <<< 2)) =
      some (xs[off.toNat + k.toNat]'hi) := by
  rw [c0_u32_add_shl2]; exact loadVal_array (t := i32) (by decide) hi h

@[c0_store] theorem c0_store_array32_u32_off_shl2 {a : BitVec 64} {off k : BitVec 32}
    {xs : List (BitVec 32)} (v : BitVec 32) (h : (array (t := i32) a xs ⋆ R) m)
    (hi : off.toNat + k.toNat < xs.length) :
    storeOk m i32 (a + ((off.setWidth 64 + k.setWidth 64) <<< 2)) ∧
      (array (t := i32) a (xs.set (off.toNat + k.toNat) v) ⋆ R)
        (storeMem m i32 (a + ((off.setWidth 64 + k.setWidth 64) <<< 2)) v) := by
  rw [c0_u32_add_shl2]; exact store_array (t := i32) v (by decide) hi h

@[c0_load] theorem c0_load_array32_u32_add_shl2 {a : BitVec 64} {off k : BitVec 32}
    {xs : List (BitVec 32)} (h : (array (t := i32) a xs ⋆ R) m)
    (hwrap : off.toNat + k.toNat < 2 ^ 32) (hi : off.toNat + k.toNat < xs.length) :
    loadVal m i32 (a + ((off + k).setWidth 64 <<< 2)) =
      some (xs[off.toNat + k.toNat]'hi) := by
  rw [c0_u32_shl2, toNat_add_of_lt hwrap]; exact loadVal_array (t := i32) (by decide) hi h

@[c0_store] theorem c0_store_array32_u32_add_shl2 {a : BitVec 64} {off k : BitVec 32}
    {xs : List (BitVec 32)} (v : BitVec 32) (h : (array (t := i32) a xs ⋆ R) m)
    (hwrap : off.toNat + k.toNat < 2 ^ 32) (hi : off.toNat + k.toNat < xs.length) :
    storeOk m i32 (a + ((off + k).setWidth 64 <<< 2)) ∧
      (array (t := i32) a (xs.set (off.toNat + k.toNat) v) ⋆ R)
        (storeMem m i32 (a + ((off + k).setWidth 64 <<< 2)) v) := by
  rw [c0_u32_shl2, toNat_add_of_lt hwrap]; exact store_array (t := i32) v (by decide) hi h

@[c0_load] theorem c0_load_array32_off_shl2 {a off k : BitVec 64} {xs : List (BitVec 32)}
    (h : (array (t := i32) a xs ⋆ R) m) (hi : off.toNat + k.toNat < xs.length) :
    loadVal m i32 (a + ((off + k) <<< 2)) = some (xs[off.toNat + k.toNat]'hi) := by
  rw [c0_add_shl2_ofNat]; exact loadVal_array (t := i32) (by decide) hi h

@[c0_store] theorem c0_store_array32_off_shl2 {a off k : BitVec 64} {xs : List (BitVec 32)}
    (v : BitVec 32) (h : (array (t := i32) a xs ⋆ R) m) (hi : off.toNat + k.toNat < xs.length) :
    storeOk m i32 (a + ((off + k) <<< 2)) ∧
      (array (t := i32) a (xs.set (off.toNat + k.toNat) v) ⋆ R)
        (storeMem m i32 (a + ((off + k) <<< 2)) v) := by
  rw [c0_add_shl2_ofNat]; exact store_array (t := i32) v (by decide) hi h

@[c0_load] theorem c0_load_array32_u32_shl2 {a : BitVec 64} {i : BitVec 32}
    {xs : List (BitVec 32)} (h : (array (t := i32) a xs ⋆ R) m) (hi : i.toNat < xs.length) :
    loadVal m i32 (a + (i.setWidth 64 <<< 2)) = some (xs[i.toNat]'hi) := by
  rw [c0_u32_shl2]; exact loadVal_array (t := i32) (by decide) hi h

@[c0_store] theorem c0_store_array32_u32_shl2 {a : BitVec 64} {i : BitVec 32}
    {xs : List (BitVec 32)} (v : BitVec 32) (h : (array (t := i32) a xs ⋆ R) m)
    (hi : i.toNat < xs.length) :
    storeOk m i32 (a + (i.setWidth 64 <<< 2)) ∧
      (array (t := i32) a (xs.set i.toNat v) ⋆ R)
        (storeMem m i32 (a + (i.setWidth 64 <<< 2)) v) := by
  rw [c0_u32_shl2]; exact store_array (t := i32) v (by decide) hi h

@[c0_load] theorem c0_load_array32_shl2 {a i : BitVec 64} {xs : List (BitVec 32)}
    (h : (array (t := i32) a xs ⋆ R) m) (hi : i.toNat < xs.length) :
    loadVal m i32 (a + (i <<< 2)) = some (xs[i.toNat]'hi) := by
  rw [shl_two]; exact loadVal_array (t := i32) (by decide) hi h

@[c0_store] theorem c0_store_array32_shl2 {a i : BitVec 64} {xs : List (BitVec 32)}
    (v : BitVec 32) (h : (array (t := i32) a xs ⋆ R) m) (hi : i.toNat < xs.length) :
    storeOk m i32 (a + (i <<< 2)) ∧
      (array (t := i32) a (xs.set i.toNat v) ⋆ R) (storeMem m i32 (a + (i <<< 2)) v) := by
  rw [shl_two]; exact store_array (t := i32) v (by decide) hi h

@[c0_load] theorem c0_load_array32_u32_off_mul {a : BitVec 64} {off k : BitVec 32}
    {xs : List (BitVec 32)} (h : (array (t := i32) a xs ⋆ R) m)
    (hi : off.toNat + k.toNat < xs.length) :
    loadVal m i32 (a + (off.setWidth 64 + k.setWidth 64) * 4) =
      some (xs[off.toNat + k.toNat]'hi) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_u32_add_mul_ofNat]
  exact loadVal_array (t := i32) (by decide) hi h

@[c0_store] theorem c0_store_array32_u32_off_mul {a : BitVec 64} {off k : BitVec 32}
    {xs : List (BitVec 32)} (v : BitVec 32) (h : (array (t := i32) a xs ⋆ R) m)
    (hi : off.toNat + k.toNat < xs.length) :
    storeOk m i32 (a + (off.setWidth 64 + k.setWidth 64) * 4) ∧
      (array (t := i32) a (xs.set (off.toNat + k.toNat) v) ⋆ R)
        (storeMem m i32 (a + (off.setWidth 64 + k.setWidth 64) * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_u32_add_mul_ofNat]
  exact store_array (t := i32) v (by decide) hi h

@[c0_load] theorem c0_load_array32_u32_add_mul {a : BitVec 64} {off k : BitVec 32}
    {xs : List (BitVec 32)} (h : (array (t := i32) a xs ⋆ R) m)
    (hwrap : off.toNat + k.toNat < 2 ^ 32) (hi : off.toNat + k.toNat < xs.length) :
    loadVal m i32 (a + (off + k).setWidth 64 * 4) = some (xs[off.toNat + k.toNat]'hi) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_u32_mul_ofNat, toNat_add_of_lt hwrap]
  exact loadVal_array (t := i32) (by decide) hi h

@[c0_store] theorem c0_store_array32_u32_add_mul {a : BitVec 64} {off k : BitVec 32}
    {xs : List (BitVec 32)} (v : BitVec 32) (h : (array (t := i32) a xs ⋆ R) m)
    (hwrap : off.toNat + k.toNat < 2 ^ 32) (hi : off.toNat + k.toNat < xs.length) :
    storeOk m i32 (a + (off + k).setWidth 64 * 4) ∧
      (array (t := i32) a (xs.set (off.toNat + k.toNat) v) ⋆ R)
        (storeMem m i32 (a + (off + k).setWidth 64 * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_u32_mul_ofNat, toNat_add_of_lt hwrap]
  exact store_array (t := i32) v (by decide) hi h

@[c0_load] theorem c0_load_array32_u32_ptr_mul {a : BitVec 64} {off k : BitVec 32}
    {xs : List (BitVec 32)} (h : (array (t := i32) a xs ⋆ R) m)
    (hi : off.toNat + k.toNat < xs.length) :
    loadVal m i32 (a + off.setWidth 64 * 4 + k.setWidth 64 * 4) =
      some (xs[off.toNat + k.toNat]'hi) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_ptr_off_mul,
    zext_toNat off (by decide), zext_toNat k (by decide)]
  exact loadVal_array (t := i32) (by decide) hi h

@[c0_store] theorem c0_store_array32_u32_ptr_mul {a : BitVec 64} {off k : BitVec 32}
    {xs : List (BitVec 32)} (v : BitVec 32) (h : (array (t := i32) a xs ⋆ R) m)
    (hi : off.toNat + k.toNat < xs.length) :
    storeOk m i32 (a + off.setWidth 64 * 4 + k.setWidth 64 * 4) ∧
      (array (t := i32) a (xs.set (off.toNat + k.toNat) v) ⋆ R)
        (storeMem m i32 (a + off.setWidth 64 * 4 + k.setWidth 64 * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_ptr_off_mul,
    zext_toNat off (by decide), zext_toNat k (by decide)]
  exact store_array (t := i32) v (by decide) hi h

@[c0_load] theorem c0_load_array32_u32_ptr_add {a d : BitVec 64} {off : BitVec 32}
    {xs : List (BitVec 32)} (h : (array (t := i32) a xs ⋆ R) m) (hd : d.toNat % 4 = 0)
    (hi : off.toNat + d.toNat / 4 < xs.length) :
    loadVal m i32 (a + off.setWidth 64 * 4 + d) = some (xs[off.toNat + d.toNat / 4]'hi) := by
  rw [c0_ptr_off_add4 a (off.setWidth 64) d hd, zext_toNat off (by decide)]
  exact loadVal_array (t := i32) (by decide) hi h

@[c0_store] theorem c0_store_array32_u32_ptr_add {a d : BitVec 64} {off : BitVec 32}
    {xs : List (BitVec 32)} (v : BitVec 32) (h : (array (t := i32) a xs ⋆ R) m)
    (hd : d.toNat % 4 = 0) (hi : off.toNat + d.toNat / 4 < xs.length) :
    storeOk m i32 (a + off.setWidth 64 * 4 + d) ∧
      (array (t := i32) a (xs.set (off.toNat + d.toNat / 4) v) ⋆ R)
        (storeMem m i32 (a + off.setWidth 64 * 4 + d) v) := by
  rw [c0_ptr_off_add4 a (off.setWidth 64) d hd, zext_toNat off (by decide)]
  exact store_array (t := i32) v (by decide) hi h

@[c0_load] theorem c0_load_array32_off_mul {a off k : BitVec 64} {xs : List (BitVec 32)}
    (h : (array (t := i32) a xs ⋆ R) m) (hi : off.toNat + k.toNat < xs.length) :
    loadVal m i32 (a + (off + k) * 4) = some (xs[off.toNat + k.toNat]'hi) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_add_mul_ofNat]
  exact loadVal_array (t := i32) (by decide) hi h

@[c0_store] theorem c0_store_array32_off_mul {a off k : BitVec 64} {xs : List (BitVec 32)}
    (v : BitVec 32) (h : (array (t := i32) a xs ⋆ R) m) (hi : off.toNat + k.toNat < xs.length) :
    storeOk m i32 (a + (off + k) * 4) ∧
      (array (t := i32) a (xs.set (off.toNat + k.toNat) v) ⋆ R)
        (storeMem m i32 (a + (off + k) * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_add_mul_ofNat]
  exact store_array (t := i32) v (by decide) hi h

@[c0_load] theorem c0_load_array32_ptr_mul {a off k : BitVec 64} {xs : List (BitVec 32)}
    (h : (array (t := i32) a xs ⋆ R) m) (hi : off.toNat + k.toNat < xs.length) :
    loadVal m i32 (a + off * 4 + k * 4) = some (xs[off.toNat + k.toNat]'hi) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_ptr_off_mul]
  exact loadVal_array (t := i32) (by decide) hi h

@[c0_store] theorem c0_store_array32_ptr_mul {a off k : BitVec 64} {xs : List (BitVec 32)}
    (v : BitVec 32) (h : (array (t := i32) a xs ⋆ R) m) (hi : off.toNat + k.toNat < xs.length) :
    storeOk m i32 (a + off * 4 + k * 4) ∧
      (array (t := i32) a (xs.set (off.toNat + k.toNat) v) ⋆ R)
        (storeMem m i32 (a + off * 4 + k * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_ptr_off_mul]
  exact store_array (t := i32) v (by decide) hi h

@[c0_load] theorem c0_load_array32_ptr_shl2_mul {a off k : BitVec 64} {xs : List (BitVec 32)}
    (h : (array (t := i32) a xs ⋆ R) m) (hi : off.toNat + k.toNat < xs.length) :
    loadVal m i32 (a + (off <<< 2) + k * 4) = some (xs[off.toNat + k.toNat]'hi) := by
  rw [c0_ptr_off_shl2_mul4]; exact loadVal_array (t := i32) (by decide) hi h

@[c0_store] theorem c0_store_array32_ptr_shl2_mul {a off k : BitVec 64} {xs : List (BitVec 32)}
    (v : BitVec 32) (h : (array (t := i32) a xs ⋆ R) m) (hi : off.toNat + k.toNat < xs.length) :
    storeOk m i32 (a + (off <<< 2) + k * 4) ∧
      (array (t := i32) a (xs.set (off.toNat + k.toNat) v) ⋆ R)
        (storeMem m i32 (a + (off <<< 2) + k * 4) v) := by
  rw [c0_ptr_off_shl2_mul4]; exact store_array (t := i32) v (by decide) hi h

@[c0_load] theorem c0_load_array32_ptr_shl2_shl2 {a off k : BitVec 64} {xs : List (BitVec 32)}
    (h : (array (t := i32) a xs ⋆ R) m) (hi : off.toNat + k.toNat < xs.length) :
    loadVal m i32 (a + (off <<< 2) + (k <<< 2)) = some (xs[off.toNat + k.toNat]'hi) := by
  rw [c0_ptr_off_shl2_shl2]; exact loadVal_array (t := i32) (by decide) hi h

@[c0_store] theorem c0_store_array32_ptr_shl2_shl2 {a off k : BitVec 64} {xs : List (BitVec 32)}
    (v : BitVec 32) (h : (array (t := i32) a xs ⋆ R) m) (hi : off.toNat + k.toNat < xs.length) :
    storeOk m i32 (a + (off <<< 2) + (k <<< 2)) ∧
      (array (t := i32) a (xs.set (off.toNat + k.toNat) v) ⋆ R)
        (storeMem m i32 (a + (off <<< 2) + (k <<< 2)) v) := by
  rw [c0_ptr_off_shl2_shl2]; exact store_array (t := i32) v (by decide) hi h

@[c0_load] theorem c0_load_array32_ptr_add {a off d : BitVec 64} {xs : List (BitVec 32)}
    (h : (array (t := i32) a xs ⋆ R) m) (hd : d.toNat % 4 = 0)
    (hi : off.toNat + d.toNat / 4 < xs.length) :
    loadVal m i32 (a + off * 4 + d) = some (xs[off.toNat + d.toNat / 4]'hi) := by
  rw [c0_ptr_off_add4 a off d hd]; exact loadVal_array (t := i32) (by decide) hi h

@[c0_store] theorem c0_store_array32_ptr_add {a off d : BitVec 64} {xs : List (BitVec 32)}
    (v : BitVec 32) (h : (array (t := i32) a xs ⋆ R) m) (hd : d.toNat % 4 = 0)
    (hi : off.toNat + d.toNat / 4 < xs.length) :
    storeOk m i32 (a + off * 4 + d) ∧
      (array (t := i32) a (xs.set (off.toNat + d.toNat / 4) v) ⋆ R)
        (storeMem m i32 (a + off * 4 + d) v) := by
  rw [c0_ptr_off_add4 a off d hd]; exact store_array (t := i32) v (by decide) hi h

@[c0_load] theorem c0_load_array32_ptr_shl2_add {a off d : BitVec 64} {xs : List (BitVec 32)}
    (h : (array (t := i32) a xs ⋆ R) m) (hd : d.toNat % 4 = 0)
    (hi : off.toNat + d.toNat / 4 < xs.length) :
    loadVal m i32 (a + (off <<< 2) + d) = some (xs[off.toNat + d.toNat / 4]'hi) := by
  rw [c0_ptr_off_shl2_add4 a off d hd]; exact loadVal_array (t := i32) (by decide) hi h

@[c0_store] theorem c0_store_array32_ptr_shl2_add {a off d : BitVec 64} {xs : List (BitVec 32)}
    (v : BitVec 32) (h : (array (t := i32) a xs ⋆ R) m) (hd : d.toNat % 4 = 0)
    (hi : off.toNat + d.toNat / 4 < xs.length) :
    storeOk m i32 (a + (off <<< 2) + d) ∧
      (array (t := i32) a (xs.set (off.toNat + d.toNat / 4) v) ⋆ R)
        (storeMem m i32 (a + (off <<< 2) + d) v) := by
  rw [c0_ptr_off_shl2_add4 a off d hd]; exact store_array (t := i32) v (by decide) hi h

@[c0_load] theorem c0_load_array32_u32 {a : BitVec 64} {i : BitVec 32} {xs : List (BitVec 32)}
    (h : (array (t := i32) a xs ⋆ R) m) (hi : i.toNat < xs.length) :
    loadVal m i32 (a + i.setWidth 64 * 4) = some (xs[i.toNat]'hi) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_u32_mul_ofNat]
  exact loadVal_array (t := i32) (by decide) hi h

@[c0_store] theorem c0_store_array32_u32 {a : BitVec 64} {i : BitVec 32} {xs : List (BitVec 32)}
    (v : BitVec 32) (h : (array (t := i32) a xs ⋆ R) m) (hi : i.toNat < xs.length) :
    storeOk m i32 (a + i.setWidth 64 * 4) ∧
      (array (t := i32) a (xs.set i.toNat v) ⋆ R) (storeMem m i32 (a + i.setWidth 64 * 4) v) := by
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_u32_mul_ofNat]
  exact store_array (t := i32) v (by decide) hi h

@[c0_load] theorem c0_load_array32_nat {a : BitVec 64} {i : Nat} {xs : List (BitVec 32)}
    (h : (array (t := i32) a xs ⋆ R) m) (hi : i < xs.length) :
    loadVal m i32 (a + BitVec.ofNat 64 (4 * i)) = some (xs[i]'hi) :=
  loadVal_array (t := i32) (by decide) hi h

@[c0_store] theorem c0_store_array32_nat {a : BitVec 64} {i : Nat} {xs : List (BitVec 32)}
    (v : BitVec 32) (h : (array (t := i32) a xs ⋆ R) m) (hi : i < xs.length) :
    storeOk m i32 (a + BitVec.ofNat 64 (4 * i)) ∧
      (array (t := i32) a (xs.set i v) ⋆ R) (storeMem m i32 (a + BitVec.ofNat 64 (4 * i)) v) :=
  store_array (t := i32) v (by decide) hi h

/-! ### `i64` dynamic-offset & `u32`-indexed `array (t := i64)` access -/

@[c0_load] theorem c0_load_array_i64_u32_off_mul {a : BitVec 64} {off k : BitVec 32}
    {xs : List (BitVec 64)} (h : (array (t := i64) a xs ⋆ R) m)
    (hi : off.toNat + k.toNat < xs.length) :
    loadVal m i64 (a + (off.setWidth 64 + k.setWidth 64) * 8) =
      some (xs[off.toNat + k.toNat]'hi) := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, c0_u32_add_mul_ofNat]
  exact loadVal_array (t := i64) (by decide) hi h

@[c0_store] theorem c0_store_array_i64_u32_off_mul {a : BitVec 64} {off k : BitVec 32}
    {xs : List (BitVec 64)} (v : BitVec 64) (h : (array (t := i64) a xs ⋆ R) m)
    (hi : off.toNat + k.toNat < xs.length) :
    storeOk m i64 (a + (off.setWidth 64 + k.setWidth 64) * 8) ∧
      (array (t := i64) a (xs.set (off.toNat + k.toNat) v) ⋆ R)
        (storeMem m i64 (a + (off.setWidth 64 + k.setWidth 64) * 8) v) := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, c0_u32_add_mul_ofNat]
  exact store_array (t := i64) v (by decide) hi h

@[c0_load] theorem c0_load_array_i64_off_mul {a off k : BitVec 64} {xs : List (BitVec 64)}
    (h : (array (t := i64) a xs ⋆ R) m) (hi : off.toNat + k.toNat < xs.length) :
    loadVal m i64 (a + (off + k) * 8) = some (xs[off.toNat + k.toNat]'hi) := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, c0_add_mul_ofNat]
  exact loadVal_array (t := i64) (by decide) hi h

@[c0_store] theorem c0_store_array_i64_off_mul {a off k : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) (h : (array (t := i64) a xs ⋆ R) m) (hi : off.toNat + k.toNat < xs.length) :
    storeOk m i64 (a + (off + k) * 8) ∧
      (array (t := i64) a (xs.set (off.toNat + k.toNat) v) ⋆ R)
        (storeMem m i64 (a + (off + k) * 8) v) := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, c0_add_mul_ofNat]
  exact store_array (t := i64) v (by decide) hi h

@[c0_load] theorem c0_load_array_i64_ptr_mul {a off k : BitVec 64} {xs : List (BitVec 64)}
    (h : (array (t := i64) a xs ⋆ R) m) (hi : off.toNat + k.toNat < xs.length) :
    loadVal m i64 (a + off * 8 + k * 8) = some (xs[off.toNat + k.toNat]'hi) := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, c0_ptr_off_mul]
  exact loadVal_array (t := i64) (by decide) hi h

@[c0_store] theorem c0_store_array_i64_ptr_mul {a off k : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) (h : (array (t := i64) a xs ⋆ R) m) (hi : off.toNat + k.toNat < xs.length) :
    storeOk m i64 (a + off * 8 + k * 8) ∧
      (array (t := i64) a (xs.set (off.toNat + k.toNat) v) ⋆ R)
        (storeMem m i64 (a + off * 8 + k * 8) v) := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, c0_ptr_off_mul]
  exact store_array (t := i64) v (by decide) hi h

@[c0_load] theorem c0_load_array_i64_off_shl3 {a off k : BitVec 64} {xs : List (BitVec 64)}
    (h : (array (t := i64) a xs ⋆ R) m) (hi : off.toNat + k.toNat < xs.length) :
    loadVal m i64 (a + ((off + k) <<< 3)) = some (xs[off.toNat + k.toNat]'hi) := by
  rw [c0_add_shl3_ofNat]; exact loadVal_array (t := i64) (by decide) hi h

@[c0_store] theorem c0_store_array_i64_off_shl3 {a off k : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) (h : (array (t := i64) a xs ⋆ R) m) (hi : off.toNat + k.toNat < xs.length) :
    storeOk m i64 (a + ((off + k) <<< 3)) ∧
      (array (t := i64) a (xs.set (off.toNat + k.toNat) v) ⋆ R)
        (storeMem m i64 (a + ((off + k) <<< 3)) v) := by
  rw [c0_add_shl3_ofNat]; exact store_array (t := i64) v (by decide) hi h

@[c0_load] theorem c0_load_array_i64_nat_add {a off k : BitVec 64} {xs : List (BitVec 64)}
    (h : (array (t := i64) a xs ⋆ R) m) (hi : off.toNat + k.toNat < xs.length) :
    loadVal m i64 (a + BitVec.ofNat 64 (8 * (off + k).toNat)) =
      some (xs[off.toNat + k.toNat]'hi) := by
  rw [← shl_three, c0_add_shl3_ofNat]; exact loadVal_array (t := i64) (by decide) hi h

@[c0_store] theorem c0_store_array_i64_nat_add {a off k : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) (h : (array (t := i64) a xs ⋆ R) m) (hi : off.toNat + k.toNat < xs.length) :
    storeOk m i64 (a + BitVec.ofNat 64 (8 * (off + k).toNat)) ∧
      (array (t := i64) a (xs.set (off.toNat + k.toNat) v) ⋆ R)
        (storeMem m i64 (a + BitVec.ofNat 64 (8 * (off + k).toNat)) v) := by
  rw [← shl_three, c0_add_shl3_ofNat]; exact store_array (t := i64) v (by decide) hi h

@[c0_load] theorem c0_load_array_i64_u32 {a : BitVec 64} {i : BitVec 32} {xs : List (BitVec 64)}
    (h : (array (t := i64) a xs ⋆ R) m) (hi : i.toNat < xs.length) :
    loadVal m i64 (a + i.setWidth 64 * 8) = some (xs[i.toNat]'hi) := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, c0_u32_mul_ofNat]
  exact loadVal_array (t := i64) (by decide) hi h

@[c0_store] theorem c0_store_array_i64_u32 {a : BitVec 64} {i : BitVec 32} {xs : List (BitVec 64)}
    (v : BitVec 64) (h : (array (t := i64) a xs ⋆ R) m) (hi : i.toNat < xs.length) :
    storeOk m i64 (a + i.setWidth 64 * 8) ∧
      (array (t := i64) a (xs.set i.toNat v) ⋆ R) (storeMem m i64 (a + i.setWidth 64 * 8) v) := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, c0_u32_mul_ofNat]
  exact store_array (t := i64) v (by decide) hi h

@[c0_load] theorem c0_load_array_i64_nat {a : BitVec 64} {i : Nat} {xs : List (BitVec 64)}
    (h : (array (t := i64) a xs ⋆ R) m) (hi : i < xs.length) :
    loadVal m i64 (a + BitVec.ofNat 64 (8 * i)) = some (xs[i]'hi) :=
  loadVal_array (t := i64) (by decide) hi h

@[c0_store] theorem c0_store_array_i64_nat {a : BitVec 64} {i : Nat} {xs : List (BitVec 64)}
    (v : BitVec 64) (h : (array (t := i64) a xs ⋆ R) m) (hi : i < xs.length) :
    storeOk m i64 (a + BitVec.ofNat 64 (8 * i)) ∧
      (array (t := i64) a (xs.set i v) ⋆ R) (storeMem m i64 (a + BitVec.ofNat 64 (8 * i)) v) :=
  store_array (t := i64) v (by decide) hi h

/-! ### Generic `u32`-indexed `array` access -/

@[c0_load] theorem c0_load_array_u32 {t : Ty} {a w : BitVec 64} {i : BitVec 32}
    {xs : List (Val t)} (h : (array a xs ⋆ R) m) (hi : i.toNat < xs.length)
    (hw : w = BitVec.ofNat 64 t.bytes) (hb : t.bytes ≤ 2 ^ 64) :
    loadVal m t (a + i.setWidth 64 * w) = some (xs[i.toNat]'hi) := by
  rw [hw, c0_u32_mul_ofNat]; exact loadVal_array hb hi h

@[c0_store] theorem c0_store_array_u32 {t : Ty} {a w : BitVec 64} {i : BitVec 32}
    {xs : List (Val t)} (v : Val t) (h : (array a xs ⋆ R) m) (hi : i.toNat < xs.length)
    (hw : w = BitVec.ofNat 64 t.bytes) (hb : t.bytes ≤ 2 ^ 64) :
    storeOk m t (a + i.setWidth 64 * w) ∧
      (array a (xs.set i.toNat v) ⋆ R) (storeMem m t (a + i.setWidth 64 * w) v) := by
  rw [hw, c0_u32_mul_ofNat]; exact store_array v hb hi h

@[c0_load] theorem c0_load_array8_u32 {a : BitVec 64} {i : BitVec 32} {xs : List (Val i8)}
    (h : (array a xs ⋆ R) m) (hi : i.toNat < xs.length) :
    loadVal m i8 (a + i.setWidth 64) = some (xs[i.toNat]'hi) := by
  simpa using c0_load_array_u32 (w := 1) h hi rfl (by decide)

@[c0_store] theorem c0_store_array8_u32 {a : BitVec 64} {i : BitVec 32} {xs : List (Val i8)}
    (v : Val i8) (h : (array a xs ⋆ R) m) (hi : i.toNat < xs.length) :
    storeOk m i8 (a + i.setWidth 64) ∧
      (array a (xs.set i.toNat v) ⋆ R) (storeMem m i8 (a + i.setWidth 64) v) := by
  simpa using c0_store_array_u32 (w := 1) v h hi rfl (by decide)

/-! ### `array64` dynamic-offset & `u32`/`Nat`-indexed access -/

@[c0_load] theorem c0_load_array64_u32_off_mul {a : BitVec 64} {off k : BitVec 32}
    {xs : List (BitVec 64)} (h : (array64 a xs ⋆ R) m) (hi : off.toNat + k.toNat < xs.length) :
    loadVal m i64 (a + (off.setWidth 64 + k.setWidth 64) * 8) =
      some (xs[off.toNat + k.toNat]'hi) := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, c0_u32_add_mul_ofNat]
  exact loadVal_array64 hi h

@[c0_store] theorem c0_store_array64_u32_off_mul {a : BitVec 64} {off k : BitVec 32}
    {xs : List (BitVec 64)} (v : BitVec 64) (h : (array64 a xs ⋆ R) m)
    (hi : off.toNat + k.toNat < xs.length) :
    storeOk m i64 (a + (off.setWidth 64 + k.setWidth 64) * 8) ∧
      (array64 a (xs.set (off.toNat + k.toNat) v) ⋆ R)
        (storeMem m i64 (a + (off.setWidth 64 + k.setWidth 64) * 8) v) := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, c0_u32_add_mul_ofNat]
  exact store_array64 v hi h

@[c0_load] theorem c0_load_array64_off_mul {a off k : BitVec 64} {xs : List (BitVec 64)}
    (h : (array64 a xs ⋆ R) m) (hi : off.toNat + k.toNat < xs.length) :
    loadVal m i64 (a + (off + k) * 8) = some (xs[off.toNat + k.toNat]'hi) := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, c0_add_mul_ofNat]
  exact loadVal_array64 hi h

@[c0_store] theorem c0_store_array64_off_mul {a off k : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) (h : (array64 a xs ⋆ R) m) (hi : off.toNat + k.toNat < xs.length) :
    storeOk m i64 (a + (off + k) * 8) ∧
      (array64 a (xs.set (off.toNat + k.toNat) v) ⋆ R)
        (storeMem m i64 (a + (off + k) * 8) v) := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, c0_add_mul_ofNat]
  exact store_array64 v hi h

@[c0_load] theorem c0_load_array64_ptr_mul {a off k : BitVec 64} {xs : List (BitVec 64)}
    (h : (array64 a xs ⋆ R) m) (hi : off.toNat + k.toNat < xs.length) :
    loadVal m i64 (a + off * 8 + k * 8) = some (xs[off.toNat + k.toNat]'hi) := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, c0_ptr_off_mul]
  exact loadVal_array64 hi h

@[c0_store] theorem c0_store_array64_ptr_mul {a off k : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) (h : (array64 a xs ⋆ R) m) (hi : off.toNat + k.toNat < xs.length) :
    storeOk m i64 (a + off * 8 + k * 8) ∧
      (array64 a (xs.set (off.toNat + k.toNat) v) ⋆ R)
        (storeMem m i64 (a + off * 8 + k * 8) v) := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, c0_ptr_off_mul]
  exact store_array64 v hi h

@[c0_load] theorem c0_load_array64_off_shl3 {a off k : BitVec 64} {xs : List (BitVec 64)}
    (h : (array64 a xs ⋆ R) m) (hi : off.toNat + k.toNat < xs.length) :
    loadVal m i64 (a + ((off + k) <<< 3)) = some (xs[off.toNat + k.toNat]'hi) := by
  rw [c0_add_shl3_ofNat]; exact loadVal_array64 hi h

@[c0_store] theorem c0_store_array64_off_shl3 {a off k : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) (h : (array64 a xs ⋆ R) m) (hi : off.toNat + k.toNat < xs.length) :
    storeOk m i64 (a + ((off + k) <<< 3)) ∧
      (array64 a (xs.set (off.toNat + k.toNat) v) ⋆ R)
        (storeMem m i64 (a + ((off + k) <<< 3)) v) := by
  rw [c0_add_shl3_ofNat]; exact store_array64 v hi h

@[c0_load] theorem c0_load_array64_nat_add {a off k : BitVec 64} {xs : List (BitVec 64)}
    (h : (array64 a xs ⋆ R) m) (hi : off.toNat + k.toNat < xs.length) :
    loadVal m i64 (a + BitVec.ofNat 64 (8 * (off + k).toNat)) =
      some (xs[off.toNat + k.toNat]'hi) := by
  rw [← shl_three, c0_add_shl3_ofNat]; exact loadVal_array64 hi h

@[c0_store] theorem c0_store_array64_nat_add {a off k : BitVec 64} {xs : List (BitVec 64)}
    (v : BitVec 64) (h : (array64 a xs ⋆ R) m) (hi : off.toNat + k.toNat < xs.length) :
    storeOk m i64 (a + BitVec.ofNat 64 (8 * (off + k).toNat)) ∧
      (array64 a (xs.set (off.toNat + k.toNat) v) ⋆ R)
        (storeMem m i64 (a + BitVec.ofNat 64 (8 * (off + k).toNat)) v) := by
  rw [← shl_three, c0_add_shl3_ofNat]; exact store_array64 v hi h

@[c0_load] theorem c0_load_array64_u32 {a : BitVec 64} {i : BitVec 32} {xs : List (BitVec 64)}
    (h : (array64 a xs ⋆ R) m) (hi : i.toNat < xs.length) :
    loadVal m i64 (a + i.setWidth 64 * 8) = some (xs[i.toNat]'hi) := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, c0_u32_mul_ofNat]
  exact loadVal_array64 hi h

@[c0_store] theorem c0_store_array64_u32 {a : BitVec 64} {i : BitVec 32} {xs : List (BitVec 64)}
    (v : BitVec 64) (h : (array64 a xs ⋆ R) m) (hi : i.toNat < xs.length) :
    storeOk m i64 (a + i.setWidth 64 * 8) ∧
      (array64 a (xs.set i.toNat v) ⋆ R) (storeMem m i64 (a + i.setWidth 64 * 8) v) := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, c0_u32_mul_ofNat]
  exact store_array64 v hi h

@[c0_load] theorem c0_load_array64_nat {a : BitVec 64} {i : Nat} {xs : List (BitVec 64)}
    (h : (array64 a xs ⋆ R) m) (hi : i < xs.length) :
    loadVal m i64 (a + BitVec.ofNat 64 (8 * i)) = some (xs[i]'hi) :=
  loadVal_array64 hi h

@[c0_store] theorem c0_store_array64_nat {a : BitVec 64} {i : Nat} {xs : List (BitVec 64)}
    (v : BitVec 64) (h : (array64 a xs ⋆ R) m) (hi : i < xs.length) :
    storeOk m i64 (a + BitVec.ofNat 64 (8 * i)) ∧
      (array64 a (xs.set i v) ⋆ R) (storeMem m i64 (a + BitVec.ofNat 64 (8 * i)) v) :=
  store_array64 v hi h

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
@[bv_c0] theorem bv_c0_zext8_64 (x : BitVec 8) : (x.setWidth 64).toNat = x.toNat :=
  zext_toNat x (by decide)
@[bv_c0] theorem bv_c0_zext16_64 (x : BitVec 16) : (x.setWidth 64).toNat = x.toNat :=
  zext_toNat x (by decide)
@[bv_c0] theorem bv_c0_zext32_64 (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat :=
  zext_toNat x (by decide)
@[bv_c0] theorem bv_c0_zext8_32 (x : BitVec 8) : (x.setWidth 32).toNat = x.toNat :=
  zext_toNat x (by decide)
@[bv_c0] theorem bv_c0_zext16_32 (x : BitVec 16) : (x.setWidth 32).toNat = x.toNat :=
  zext_toNat x (by decide)

attribute [bv_c0] BitVec.toNat_add BitVec.toNat_sub BitVec.toNat_mul BitVec.toNat_ofNat
  BitVec.toNat_setWidth BitVec.toNat_ofBool BitVec.toNat_ofFin Nat.add_mod_mod Nat.mod_add_mod
  BitVec.signExtend_eq_setWidth_of_msb_false

end BvC0

end LeanQbe.T

/-! ## 5. Tactics -/

namespace LeanQbe.T.C0Step

open Lean Meta Elab Tactic

meta initialize registerTraceClass `c0_step

/-- Frame inference: close `(P ⋆ ?R) m` (or any `⋆`-permutation) from a hypothesis by AC
matching, instantiating metavariables (Kraken `ecancel`). -/
macro "c0_frame" : tactic => `(tactic| first | assumption | ecancel)

/-- Discharge C0 arithmetic side goals (bounds, address equalities, sizes). -/
macro "c0_bound" : tactic => `(tactic| first
  | assumption | rfl | decide | omega | bv_omega
  | (simp only [bv_c0, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, BitVec.reduceToNat] at *;
      omega)
  | (simp only [bv_c0, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, BitVec.reduceToNat] at *;
      done))

/-- Discharge division/remainder definedness side goals (`b ≠ 0`, `sdivDefined a b = true`). -/
macro "c0_div_bound" : tactic => `(tactic| first
  | c0_bound
  | (refine LeanQbe.T.sdivDefined_of_pos ?_ ?_ <;> (first
      | c0_bound
      | (simp only [BitVec.slt, BitVec.sle, BitVec.reduceToInt, BitVec.toInt_zero,
          decide_eq_true_eq, decide_eq_false_iff_not] at *; omega)
      | (intro h0; have := congrArg BitVec.toInt h0;
          simp only [BitVec.slt, BitVec.sle, BitVec.reduceToInt, BitVec.toInt_zero,
            decide_eq_true_eq, decide_eq_false_iff_not] at *; omega)
      | (simp only [BitVec.slt, BitVec.sle, BitVec.reduceToInt, BitVec.toInt_zero,
          decide_eq_true_eq, decide_eq_false_iff_not] at *; bv_omega)))
  | (rw [LeanQbe.T.sdivDefined_iff]; refine ⟨?_, ?_⟩ <;> (first
      | c0_bound
      | (intro h0; have := congrArg BitVec.toInt h0;
          simp only [BitVec.slt, BitVec.sle, BitVec.reduceToInt, BitVec.toInt_zero,
            decide_eq_true_eq, decide_eq_false_iff_not] at *; omega)
      | (rintro ⟨_, _⟩;
          simp only [BitVec.slt, BitVec.sle, BitVec.reduceToInt, BitVec.toInt_zero,
            decide_eq_true_eq, decide_eq_false_iff_not] at *; bv_omega))))

/-- Lemmas from `t_wp_unfold_all` excluded from straight-line `c0_let_simp` because `stepOnce`
handles them explicitly (`load`, `store`, `jnz`, and UB-guarded `udiv`/`urem`/`sdiv`/`srem`). -/
private meta def c0LetExcluded : Array Name := #[
  ``LeanQbe.T.wp_load, ``LeanQbe.T.wp_store, ``LeanQbe.T.wp_jnz,
  ``LeanQbe.T.wp_let_udiv_eq, ``LeanQbe.T.wp_let_urem_eq,
  ``LeanQbe.T.wp_let_sdiv_eq, ``LeanQbe.T.wp_let_srem_eq
]

private meta def isExcludedSimpArg (stx : Syntax) : Bool :=
  match stx.find? (·.isIdent) with
  | some (.ident _ _ val preresolved) =>
    let base := val.eraseMacroScopes
    c0LetExcluded.any fun nm =>
      nm == base || preresolved.any fun
        | .decl n _ => n == nm
        | _ => false
  | _ => false

/-- Derive `c0_let_simp` directly from `Logic/Rules.lean`'s `t_wp_unfold_all` so the two lemma
lists never drift, filtering out memory/branch/UB-division rules handled by `stepOnce` and
appending C0 `BitVec`/`Nat` reductions. -/
meta def mkC0LetSimpTactic : MacroM (TSyntax `tactic) := do
  let stx ← Lean.expandMacros (← `(tactic| t_wp_unfold_all))
  match stx with
  | `(tactic| simp only [$ls,*]) =>
    let kept := ls.getElems.filter (!isExcludedSimpArg ·.raw)
    let extras ← `(tactic| simp only [
      BitVec.reduceSignExtend, BitVec.reduceSetWidth, BitVec.reduceAdd, BitVec.reduceMul,
      Nat.reduceDiv])
    match extras with
    | `(tactic| simp only [$es,*]) =>
      let all := kept ++ es.getElems
      `(tactic| simp only [$all,*])
    | _ => Macro.throwError "c0_let_simp: unexpected extra simp syntax"
  | _ => Macro.throwError "c0_let_simp: unexpected expansion of `t_wp_unfold_all`"

/-- Pure-`let` unfolding for `wp` (shared with `Logic/Rules.lean`'s `t_wp_unfold_all`, minus
`load`/`store`/`jnz` and UB-guarded `udiv`/`urem`/`sdiv`/`srem`, which `c0_step` handles). -/
elab "c0_let_simp" : tactic => do
  evalTactic (← liftMacroM mkC0LetSimpTactic)

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

private meta def ppGoalType (g : MVarId) : TacticM String :=
  g.withContext do
    return (← Meta.ppExpr (← instantiateMVars (← g.getType))).pretty

private meta inductive MemTryResult where
  | ok
  | applyFailed
  | frameFailed (goalStr : String)
  | sideFailed (goalStr : String)
  | unassigned (goalStr : String)

/-- Try `apply nm` on `g`, closing frame goals with `c0_frame` and the rest with `c0_bound`. -/
private meta def tryMemLemma (g : MVarId) (nm : Name) : TacticM MemTryResult := do
  let s ← saveState
  let gs ← try withReducible <| g.apply (← mkConstWithFreshMVarLevels nm)
    catch _ => s.restore; return .applyFailed
  for g' in gs do
    let ty ← instantiateMVars (← g'.getType)
    if ty.isAppOf ``Std.ExtHashMap.sep then
      unless ← withReducible (closeWith g' (← `(tactic| c0_frame))) do
        let msg ← ppGoalType g'
        s.restore
        return .frameFailed msg
  for g' in gs do
    if ← g'.isAssigned then continue
    if ← isProp (← g'.getType) then
      unless ← closeWith g' (← `(tactic| c0_bound)) do
        let msg ← ppGoalType g'
        s.restore
        return .sideFailed msg
  for g' in gs do
    unless ← g'.isAssigned do
      let msg ← ppGoalType g'
      s.restore
      return .unassigned msg
  return .ok

private meta def formatMemDiag (isLoad : Bool) (goalStr : String) (keys untagged : Array Name)
    (triedCount : Nat) (nearMisses : Array String) : String :=
  let attr := if isLoad then "c0_load" else "c0_store"
  let header := s!"c0_step: no @[{attr}] lemma closed:\n  {goalStr}"
  let fpLine :=
    if keys.isEmpty then
      "\nfootprints: none (no separation-logic `⋆` hypothesis in local context)"
    else
      s!"\nfootprints: {keys}"
  let untaggedLine :=
    if untagged.isEmpty then ""
    else s!"\nuntagged footprints (missing @[{attr}]?): {untagged}"
  let detailLine :=
    if !nearMisses.isEmpty then
      let shown := nearMisses.toList.take 4
      let extra := if nearMisses.size > 4 then s!"\n  ... ({nearMisses.size - 4} more)" else ""
      "\ncandidate failures:\n" ++ String.intercalate "\n" shown ++ extra
    else if triedCount > 0 then
      s!"\nchecked {triedCount} @[{attr}] lemma(s), none matched the goal address/type"
    else ""
  header ++ fpLine ++ untaggedLine ++ detailLine

/-- Close a `loadVal m t a = some ?v` (`isLoad`) or `storeOk … ∧ (?P ⋆ ?R) (storeMem …)` goal
with a footprint-indexed `c0_load` / `c0_store` lemma, returning a crisp diagnostic on failure. -/
private meta def memSolveRes (isLoad : Bool) (g : MVarId) : TacticM (Except String Unit) := do
  setGoals [g]
  evalTactic (← `(tactic| try simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm]))
  let g ← getMainGoal
  let keys ← footprints
  let env ← getEnv
  let mut untagged : Array Name := #[]
  let mut triedCount : Nat := 0
  let mut nearMisses : Array String := #[]
  for k in keys do
    let lems := C0Step.c0MemLemmas env isLoad k
    if lems.isEmpty then
      untagged := untagged.push k
    for nm in lems do
      triedCount := triedCount + 1
      match ← tryMemLemma g nm with
      | .ok => return .ok ()
      | .applyFailed => pure ()
      | .frameFailed s => nearMisses := nearMisses.push s!"  - `{nm}`: frame failed: {s}"
      | .sideFailed s => nearMisses := nearMisses.push s!"  - `{nm}`: side goal failed: {s}"
      | .unassigned s => nearMisses := nearMisses.push s!"  - `{nm}`: unassigned goal: {s}"
  let goalStr ← ppGoalType g
  return .error (formatMemDiag isLoad goalStr keys untagged triedCount nearMisses)

/-- Close a `loadVal m t a = some ?v` (`isLoad`) or `storeOk … ∧ (?P ⋆ ?R) (storeMem …)` goal
with a footprint-indexed `c0_load` / `c0_store` lemma. -/
meta def memSolve (isLoad : Bool) (g : MVarId) : TacticM Unit := do
  match ← memSolveRes isLoad g with
  | .ok () => pure ()
  | .error msg => throwError msg

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

/-- Head `OpCode` constructor name of an `Expr.let_` term, if visible. -/
private meta def letOpCode? (e : Lean.Expr) : Option Name :=
  if e.isAppOf ``LeanQbe.T.Expr.let_ && e.getAppNumArgs == 6 then
    let op := (e.getArg! 4).headBeta
    if op.isAppOf ``LeanQbe.T.Op.mk && op.getAppNumArgs == 5 then
      (op.getArg! 3).getAppFn.constName?
    else if op.isAppOf ``LeanQbe.T.op2 && op.getAppNumArgs == 7 then
      (op.getArg! 4).getAppFn.constName?
    else none
  else none

/-- Step a UB-guarded division/remainder `let_` (`udiv`/`urem`/`sdiv`/`srem`), auto-closing its
definedness side condition with `c0_div_bound` when possible and continuing on the body. -/
private meta def stepDiv (g : MVarId) (lem : Name) : TacticM Bool := do
  let s ← saveState
  try
    setGoals [g]
    evalTactic (← `(tactic| try simp only [LeanQbe.T.op2_eq_mk]))
    let g ← getMainGoal
    let gs ← g.apply (← mkConstWithFreshMVarLevels lem)
    let [hSide, hk] := gs.take 2 | s.restore; return false
    setGoals [hSide]
    evalTactic (← `(tactic| try simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm]))
    let hSide ← getMainGoal
    let sideClosed ← closeWith hSide (← `(tactic| c0_div_bound))
    setGoals [hk]
    evalTactic (← `(tactic| try simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm]))
    evalTactic (← `(tactic| try c0_let_simp))
    let hkRest ← getUnsolvedGoals
    setGoals ((if sideClosed then [] else [hSide]) ++ hkRest)
    return true
  catch _ => s.restore; return false

private meta inductive StepResult where
  | progressed
  | stuck
  | memFailed (msg : String)

/-- Single step returning `.memFailed msg` (with state restored) on unmatched loads/stores. -/
private meta def stepOnceRes : TacticM StepResult := withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let ty := ty.headBeta
  if ty.isAppOf ``LeanQbe.T.Func.wp && ty.getAppNumArgs ≥ 4 then
    let f := ty.getArg! 3
    let some c := f.getAppFn.constName? | return .stuck
    evalTactic (← `(tactic| (unfold LeanQbe.T.Func.wp $(mkIdent c):ident; try c0_let_simp)))
    return .progressed
  if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 then
    let e := (ty.getArg! 4).headBeta
    match e.getAppFn.constName? with
    | some ``LeanQbe.T.Expr.let_ =>
      match letOpCode? e with
      | some ``LeanQbe.T.OpCode.udiv =>
        return if ← stepDiv g ``LeanQbe.T.wp_udiv_of then .progressed else .stuck
      | some ``LeanQbe.T.OpCode.urem =>
        return if ← stepDiv g ``LeanQbe.T.wp_urem_of then .progressed else .stuck
      | some ``LeanQbe.T.OpCode.sdiv =>
        return if ← stepDiv g ``LeanQbe.T.wp_sdiv_of then .progressed else .stuck
      | some ``LeanQbe.T.OpCode.srem =>
        return if ← stepDiv g ``LeanQbe.T.wp_srem_of then .progressed else .stuck
      | _ =>
        let s ← saveState
        try evalTactic (← `(tactic| c0_let_simp)); return .progressed
        catch _ => s.restore; return .stuck
    | some ``LeanQbe.T.Expr.jump | some ``LeanQbe.T.Expr.ret | some ``LeanQbe.T.Expr.exit =>
      let s ← saveState
      try evalTactic (← `(tactic| c0_let_simp)); return .progressed
      catch _ => s.restore; return .stuck
    | some ``LeanQbe.T.Expr.load =>
      let s ← saveState
      let gs ← g.apply (← mkConstWithFreshMVarLevels ``LeanQbe.T.wp_load_of)
      let [hl, hk] := gs.take 2 | s.restore; return .stuck
      match ← memSolveRes true hl with
      | .ok () =>
        setGoals [hk]
        evalTactic (← `(tactic| (try c0_let_simp)))
        return .progressed
      | .error msg =>
        s.restore
        return .memFailed msg
    | some ``LeanQbe.T.Expr.store =>
      let s ← saveState
      let m0 := ty.getArg! 5
      let gs ← g.apply (← mkConstWithFreshMVarLevels ``LeanQbe.T.wp_store_sep)
      let [hs, hk] := gs.take 2 | s.restore; return .stuck
      match ← memSolveRes false hs with
      | .ok () =>
        setGoals [hk]
        let mId := mkIdent `m
        let hmId := mkIdent `hm
        evalTactic (← `(tactic| intro $mId:ident $hmId:ident))
        evalTactic (← `(tactic| try simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm,
          Std.ExtHashMap.sep_emp] at $hmId:ident))
        clearStale m0
        evalTactic (← `(tactic| try c0_let_simp))
        return .progressed
      | .error msg =>
        s.restore
        return .memFailed msg
    | some ``LeanQbe.T.Expr.jnz =>
      let hc := mkIdent `hc
      evalTactic (← `(tactic|
        refine LeanQbe.T.wp_jnz_of (fun $hc:ident => ?_) (fun $hc:ident => ?_)))
      evalTactic (← `(tactic| all_goals
        (try simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm] at $hc:ident)
        c0_cond $hc
        try (exfalso; c0_bound)
        try c0_let_simp))
      return .progressed
    | some ``LeanQbe.T.Expr.group =>
      if e.getAppNumArgs == 6 && isJoin (e.getArg! 4) then
        let J := mkIdent `J
        let hJ := mkIdent `hJ
        evalTactic (← `(tactic| refine LeanQbe.T.wp_unroll_group fun $J:ident $hJ:ident => ?_))
        evalTactic (← `(tactic| try c0_let_simp))
        return .progressed
      return .stuck
    | some ``LeanQbe.T.Blocks.get =>
      let s ← saveState
      try evalTactic (← `(tactic| c0_let_simp)); return .progressed
      catch _ => s.restore; return .stuck
    | _ => return .stuck
  if let .fvar J := ty.getAppFn then
    if let some h ← findJoinHyp J then
      let gs ← g.apply h
      setGoals gs
      evalTactic (← `(tactic| (try c0_let_simp)))
      return .progressed
  return .stuck

/-- One symbolic-execution step on the main goal; `false` if no step applies. -/
meta def stepOnce : TacticM Bool := do
  match ← stepOnceRes with
  | .progressed => return true
  | .stuck => return false
  | .memFailed msg => throwError msg

private meta partial def stepsLoop (strictMem : Bool) (fuel : Nat) :
    TacticM (Bool × Option String) := do
  if fuel = 0 then return (false, none)
  let gs ← getUnsolvedGoals
  let mut out : Array MVarId := #[]
  let mut anyProgressed := false
  let mut firstMemErr : Option String := none
  for g in gs do
    if ← g.isAssigned then continue
    setGoals [g]
    match ← stepOnceRes with
    | .progressed =>
      anyProgressed := true
      let (_, subErr) ← stepsLoop strictMem (fuel - 1)
      if firstMemErr.isNone then firstMemErr := subErr
      out := out ++ (← getUnsolvedGoals)
    | .stuck =>
      out := out ++ (← getUnsolvedGoals)
    | .memFailed msg =>
      trace[c0_step] "{msg}"
      if strictMem then throwError msg
      if firstMemErr.isNone then firstMemErr := some msg
      out := out ++ (← getUnsolvedGoals)
  setGoals out.toList
  return (anyProgressed, firstMemErr)

/-- Repeat `stepOnce` on every goal until no step applies. When `strictMem` is `true`, any
unmatched `loadVal` / `storeMem` goal throws immediately; otherwise `trace[c0_step]` records
the diagnostic and an error is thrown if no step progressed at all. -/
meta def steps (fuel : Nat) (strictMem : Bool := false) : TacticM Unit := do
  let (progressed, err?) ← stepsLoop strictMem fuel
  if !progressed then
    if let some msg := err? then
      throwError msg

/-- Discharge a `call` with the environment hypothesis `h : ∀ args m Q X, spec … → Γ f …`;
the remaining goal is the callee contract with the continuation as postcondition. -/
macro "c0_call" h:term : tactic =>
  `(tactic| (refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_); try c0_let_simp))

/-- One C0 symbolic-execution step (see module docs). -/
elab "c0_step" : tactic => do
  unless ← stepOnce do throwError "c0_step: no step applies"

/-- Symbolically execute all straight-line code, branches and join points; stops at loops,
calls, returns, and jumps to loop heads. Emits `trace[c0_step]` diagnostics on unmatched
`load`/`store` goals and throws if stuck with zero progress on a `load`/`store`. -/
elab "c0_steps" : tactic => steps 10000

/-- Strict `c0_steps`: throws a crisp diagnostic error immediately whenever any `load` or `store`
fails to match a `@[c0_load]` / `@[c0_store]` lemma. -/
elab "c0_steps!" : tactic => steps 10000 (strictMem := true)

end LeanQbe.T.C0Step
