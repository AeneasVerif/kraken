module

public import LeanQbe.T.ZeroPeel
public import LeanQbe.T.Wf
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.GroupLfpLemmas
import LeanQbe.T.WPLemmas
import LeanQbe.T.OptUtilLemmas
import LeanQbe.T.OpsLemmas
import LeanQbe.T.PassFlatKit
import all Kraken.Mem

/-!
# Helper Lemmas for `LeanQbe.T.ZeroPeel` (Part 1)

Syntactic/semantic infrastructure for Section 1 (`shiftTFlat` & contexts), Section 2 (`letBindTup`
& `inlineJump0`), Section 3 (`peelSingle`), byte/memory store-chain lemmas, and WF/WP of
`mkStoreChain` / `mkWideBody` / `mkWideWrapper`.
-/

set_option autoImplicit false

namespace LeanQbe.T

open Std Std.ExtHashMap

namespace ZeroPeel

/-! ## Stack, `pushTup`, `wfCheck`, and `shiftTFlat` helpers -/

public theorem denoteArgs_nil_eq {V : Ty → Type} (vs : List ((t : Ty) × V t)) :
    denoteArgs vs (ts := []) () = some () := rfl

public theorem denoteArgs_cons_eq {V : Ty → Type} (vs : List ((t : Ty) × V t))
    {t : Ty} {ts : List Ty} (a : Arg K t) (as : Tup (Arg K) ts) :
    denoteArgs vs (ts := t :: ts) (a, as) =
      match denoteArg vs a, denoteArgs vs as with
      | some a', some as' => some (a', as')
      | _, _ => none := rfl

public theorem wfCheck_let_eq {rs ts : List Ty} (G : List Ty) (D : List (List Ty))
    (op : Op K ts) (k : TFlat rs) :
    (TFlat.let_ op k).wfCheck G D = (checkArgs G op.args && k.wfCheck (pushTypes ts G) D) := rfl

public theorem wfCheck_load_eq {rs : List Ty} (G : List Ty) (D : List (List Ty))
    (t : Ty) (a : Arg K i64) (k : TFlat rs) :
    (TFlat.load t a k).wfCheck G D = (checkArg G i64 a && k.wfCheck (t :: G) D) := rfl

public theorem wfCheck_store_eq {rs : List Ty} (G : List Ty) (D : List (List Ty))
    {u : Ty} (v : Arg K u) (a : Arg K i64) (k : TFlat rs) :
    (TFlat.store v a k).wfCheck G D =
      (checkArg G u v && checkArg G i64 a && k.wfCheck G D) := rfl

public theorem wfCheck_call_eq {rs as : List Ty} (G : List Ty) (D : List (List Ty))
    (f : Sym) (bs : List Ty) (args : Tup (Arg K) as) (k : TFlat rs) :
    (TFlat.call f bs args k).wfCheck G D =
      (checkArgs G args && k.wfCheck (pushTypes bs G) D) := rfl

public theorem wfCheck_jnz_eq {rs : List Ty} (G : List Ty) (D : List (List Ty))
    (c : Arg K .bool) (t e : TFlat rs) :
    (TFlat.jnz c t e).wfCheck G D =
      (checkArg G .bool c && t.wfCheck G D && e.wfCheck G D) := rfl

public theorem wfCheck_group_eq {rs : List Ty} {sig : List (List Ty)}
    (G : List Ty) (D : List (List Ty)) (bs : TBlocks rs sig) (k : TFlat rs) :
    (TFlat.group bs k).wfCheck G D =
      (bs.wfCheck G (pushTypes sig D) && k.wfCheck G (pushTypes sig D)) := rfl

public theorem wfCheckB_cons_eq {rs : List Ty} {ts : List Ty} {sig : List (List Ty)}
    (G : List Ty) (D : List (List Ty)) (b : TFlat rs) (bs : TBlocks rs sig) :
    (TBlocks.cons (ts := ts) b bs).wfCheck G D =
      (b.wfCheck (pushTypes ts G) D && bs.wfCheck G D) := rfl

public theorem denote_let_eq (V : Ty → Type) (L : List Ty → Type) {rs ts : List Ty}
    (op : Op K ts) (k : TFlat rs) (vs : List ((t : Ty) × V t)) (ls : List ((ts : List Ty) × L ts)) :
    denote V L (.let_ op k) vs ls =
      match denoteArgs vs op.args with
      | some args' => .let_ ⟨op.code, args'⟩ (fun res => denote V L k (pushTup res vs) ls)
      | none => .hlt := rfl

public theorem denote_load_eq (V : Ty → Type) (L : List Ty → Type) {rs : List Ty}
    (t : Ty) (a : Arg K i64) (k : TFlat rs)
    (vs : List ((t : Ty) × V t)) (ls : List ((ts : List Ty) × L ts)) :
    denote V L (.load t a k) vs ls =
      match denoteArg vs a with
      | some a' => .load t a' (fun v => denote V L k (⟨t, v⟩ :: vs) ls)
      | none => .hlt := rfl

public theorem denote_store_eq (V : Ty → Type) (L : List Ty → Type) {rs : List Ty}
    {t : Ty} (v : Arg K t) (a : Arg K i64) (k : TFlat rs)
    (vs : List ((t : Ty) × V t)) (ls : List ((ts : List Ty) × L ts)) :
    denote V L (.store v a k) vs ls =
      match denoteArg vs v, denoteArg vs a with
      | some v', some a' => .store v' a' (denote V L k vs ls)
      | _, _ => .hlt := rfl

public theorem denote_call_eq (V : Ty → Type) (L : List Ty → Type) {rs as : List Ty}
    (f : Sym) (bs : List Ty) (args : Tup (Arg K) as) (k : TFlat rs)
    (vs : List ((t : Ty) × V t)) (ls : List ((ts : List Ty) × L ts)) :
    denote V L (.call f bs args k) vs ls =
      match denoteArgs vs args with
      | some args' => .call f args' (fun (res : Tup V bs) => denote V L k (pushTup res vs) ls)
      | none => .hlt := rfl

public theorem denote_jnz_eq (V : Ty → Type) (L : List Ty → Type) {rs : List Ty}
    (c : Arg K .bool) (t e : TFlat rs)
    (vs : List ((t : Ty) × V t)) (ls : List ((ts : List Ty) × L ts)) :
    denote V L (.jnz c t e) vs ls =
      match denoteArg vs c with
      | some c' => .jnz c' (denote V L t vs ls) (denote V L e vs ls)
      | none => .hlt := rfl

public theorem denote_group_eq (V : Ty → Type) (L : List Ty → Type) {rs : List Ty}
    {sig : List (List Ty)} (bs : TBlocks rs sig) (k : TFlat rs)
    (vs : List ((t : Ty) × V t)) (ls : List ((ts : List Ty) × L ts)) :
    denote V L (.group bs k) vs ls =
      .group (fun Js => denoteB V L bs vs (pushTup Js ls))
        (fun Js => denote V L k vs (pushTup Js ls)) := rfl

public theorem denoteB_cons_eq (V : Ty → Type) (L : List Ty → Type) {rs : List Ty}
    {ts : List Ty} {sig : List (List Ty)} (b : TFlat rs) (bs : TBlocks rs sig)
    (vs : List ((t : Ty) × V t)) (ls : List ((ts : List Ty) × L ts)) :
    denoteB V L (.cons (ts := ts) b bs) vs ls =
      .cons (fun xs => denote V L b (pushTup xs vs) ls) (denoteB V L bs vs ls) := rfl

public theorem wfCheck_jump_eq {rs ts : List Ty} (G : List Ty) (D : List (List Ty))
    (j : Nat) (args : Tup (Arg K) ts) :
    (TFlat.jump (rs := rs) j args).wfCheck G D =
      ((match listGet? D j with
        | some ts' => match listTyDecEq ts' ts with | isTrue _ => true | isFalse _ => false
        | none => false) && checkArgs G args) := rfl

public theorem wfCheck_ret_eq {rs : List Ty} (G : List Ty) (D : List (List Ty))
    (vs : Tup (Arg K) rs) :
    (TFlat.ret vs).wfCheck G D = checkArgs G vs := rfl

public theorem wfCheck_exit_eq {rs as : List Ty} (G : List Ty) (D : List (List Ty))
    (f : Sym) (args : Tup (Arg K) as) :
    (TFlat.exit (rs := rs) f args).wfCheck G D = checkArgs G args := rfl

public theorem wfCheck_hlt_eq {rs : List Ty} (G : List Ty) (D : List (List Ty)) :
    (TFlat.hlt : TFlat rs).wfCheck G D = true := rfl

public theorem wfCheckB_nil_eq {rs : List Ty} (G : List Ty) (D : List (List Ty)) :
    (TBlocks.nil : TBlocks rs []).wfCheck G D = true := rfl

public theorem denote_jump_eq (V : Ty → Type) (L : List Ty → Type) {rs ts : List Ty}
    (j : Nat) (args : Tup (Arg K) ts)
    (vs : List ((t : Ty) × V t)) (ls : List ((ts : List Ty) × L ts)) :
    denote V L (.jump j args : TFlat rs) vs ls =
      match lookupL ls ts j, denoteArgs vs args with
      | some l', some args' => .jump l' args'
      | _, _ => .hlt := rfl

public theorem denote_ret_eq (V : Ty → Type) (L : List Ty → Type) {rs : List Ty}
    (vsA : Tup (Arg K) rs)
    (vs : List ((t : Ty) × V t)) (ls : List ((ts : List Ty) × L ts)) :
    denote V L (.ret vsA) vs ls =
      match denoteArgs vs vsA with | some vs' => .ret vs' | none => .hlt := rfl

public theorem denote_exit_eq (V : Ty → Type) (L : List Ty → Type) {rs as : List Ty}
    (f : Sym) (args : Tup (Arg K) as)
    (vs : List ((t : Ty) × V t)) (ls : List ((ts : List Ty) × L ts)) :
    denote V L (.exit f args : TFlat rs) vs ls =
      match denoteArgs vs args with | some args' => .exit f args' | none => .hlt := rfl

public theorem denote_hlt_eq (V : Ty → Type) (L : List Ty → Type) {rs : List Ty}
    (vs : List ((t : Ty) × V t)) (ls : List ((ts : List Ty) × L ts)) :
    denote V L (.hlt : TFlat rs) vs ls = .hlt := rfl

public theorem denoteB_nil_eq (V : Ty → Type) (L : List Ty → Type) {rs : List Ty}
    (vs : List ((t : Ty) × V t)) (ls : List ((ts : List Ty) × L ts)) :
    denoteB V L (.nil : TBlocks rs []) vs ls = .nil := rfl

public theorem pushTypes_nil_eq {α : Type} (G : List α) : pushTypes [] G = G := rfl

public theorem pushTypes_cons_eq {α : Type} (t : α) (ts G : List α) :
    pushTypes (t :: ts) G = pushTypes ts (t :: G) := rfl

public theorem pushTup_nil_eq {α : Type} {f : α → Type} (acc : List ((x : α) × f x)) :
    pushTup (f := f) (as := []) () acc = acc := rfl

public theorem pushTup_cons_eq {α : Type} {f : α → Type} {t : α} {ts : List α}
    (x : f t) (xs : Tup f ts) (acc : List ((x : α) × f x)) :
    pushTup (f := f) (as := t :: ts) (x, xs) acc = pushTup xs (⟨t, x⟩ :: acc) := rfl

public theorem listGet?_nil_eq {α : Type} (i : Nat) : listGet? ([] : List α) i = none := rfl

public theorem listGet?_cons_zero_eq {α : Type} (x : α) (xs : List α) :
    listGet? (x :: xs) 0 = some x := rfl

public theorem listGet?_cons_succ_eq {α : Type} (x : α) (xs : List α) (i : Nat) :
    listGet? (x :: xs) (i + 1) = listGet? xs i := rfl

public theorem wp_call_eq {Γ : Env} {rs as bs : List Ty} {Q : Post rs} {X : XPost}
    {f : Sym} {args : Tup (Arg Val) as} {k : Tup Val bs → Expr Val Cont rs} {m : Mem 64} :
    wp Γ Q X (.call f args k) m =
      ∃ (P : Post bs) (E : XPost), Γ f as bs (vals args) m P E ∧
        (∀ r m', P r m' → wp Γ Q X (k r) m') ∧
        (∀ g cs xs m', E g cs xs m' → X g cs xs m') := rfl

public theorem pushTup_append {α : Type} {f : α → Type} :
    {ts : List α} → (xs : Tup f ts) → (a b : List ((x : α) × f x)) →
    pushTup xs (a ++ b) = pushTup xs a ++ b
  | [], (), _, _ => rfl
  | _ :: _, (x, xs), a, b => by
    have h := pushTup_append xs (⟨_, x⟩ :: a) b
    dsimp only [pushTup]
    rw [← List.cons_append]
    exact h

public theorem pushTypes_append {α : Type} :
    (ts a b : List α) → pushTypes ts (a ++ b) = pushTypes ts a ++ b
  | [], _, _ => rfl
  | t :: ts, a, b => pushTypes_append ts (t :: a) b

public theorem pushTypes_length {α : Type} :
    (ts G : List α) → (pushTypes ts G).length = G.length + ts.length
  | [], _ => rfl
  | t :: ts, G => by
    have h := pushTypes_length ts (t :: G)
    dsimp only [pushTypes]
    rw [List.length_cons] at h
    rw [List.length_cons]
    omega

public theorem CtxTypes_length {α : Type} {f : α → Type} :
    {G : List α} → {vs : List ((x : α) × f x)} → CtxTypes G vs → vs.length = G.length
  | _, _, .nil => rfl
  | _, _, .cons h => by rw [List.length_cons, List.length_cons, CtxTypes_length h]

public theorem CtxTypes_append {α : Type} {f : α → Type} {G₁ G₂ : List α}
    {vs₁ vs₂ : List ((x : α) × f x)} (h₁ : CtxTypes G₁ vs₁) (h₂ : CtxTypes G₂ vs₂) :
    CtxTypes (G₁ ++ G₂) (vs₁ ++ vs₂) := by
  induction h₁ with
  | nil => exact h₂
  | cons _ ih => exact .cons ih

public theorem listGet?_append_mid_lt {α : Type} :
    (pre mid post : List α) → (i : Nat) → i < pre.length →
    listGet? (pre ++ (mid ++ post)) i = listGet? (pre ++ post) i
  | [], _, _, _, hi => by simp at hi
  | _ :: _, _, _, 0, _ => rfl
  | _ :: pre, mid, post, i + 1, hi =>
    listGet?_append_mid_lt pre mid post i (Nat.lt_of_succ_lt_succ hi)

public theorem listGet?_append_mid_ge {α : Type} :
    (pre mid post : List α) → (i : Nat) → pre.length ≤ i →
    listGet? (pre ++ (mid ++ post)) (i + mid.length) = listGet? (pre ++ post) i
  | [], mid, post, i, _ => by
    simp only [List.nil_append]
    induction mid with
    | nil => rfl
    | cons _ mid ih =>
      show listGet? (_ :: (mid ++ post)) (i + (mid.length + 1)) = listGet? post i
      rw [← Nat.add_assoc]
      exact ih
  | _ :: pre, mid, post, 0, hi => by simp at hi
  | _ :: pre, mid, post, i + 1, hi => by
    have h : (i + 1) + mid.length = (i + mid.length) + 1 := by omega
    rw [h]
    exact listGet?_append_mid_ge pre mid post i (Nat.le_of_succ_le_succ hi)

public theorem lookupV_append_mid {V : Ty → Type} (vsPre vsNew vsPost : List ((t : Ty) × V t))
    (t : Ty) (i : Nat) :
    lookupV (vsPre ++ (vsNew ++ vsPost)) t
        (if i >= vsPre.length then i + vsNew.length else i) =
      lookupV (vsPre ++ vsPost) t i := by
  dsimp only [lookupV]
  by_cases hi : vsPre.length ≤ i
  · simp only [ge_iff_le, hi, ↓reduceIte]
    rw [listGet?_append_mid_ge vsPre vsNew vsPost i hi]
  · have hlt : i < vsPre.length := Nat.lt_of_not_le hi
    simp only [ge_iff_le, hi, ↓reduceIte]
    rw [listGet?_append_mid_lt vsPre vsNew vsPost i hlt]

public theorem denoteArg_shiftArgAbove {V : Ty → Type} (vsPre vsNew vsPost : List ((t : Ty) × V t))
    {t : Ty} (a : Arg K t) :
    denoteArg (vsPre ++ (vsNew ++ vsPost)) (shiftArgAbove vsPre.length vsNew.length a) =
      denoteArg (vsPre ++ vsPost) a := by
  cases a with
  | imm c => rfl
  | var i =>
    dsimp only [shiftArgAbove]
    by_cases hi : vsPre.length ≤ i
    · have h1 := lookupV_append_mid vsPre vsNew vsPost t i
      simp only [ge_iff_le, hi, ↓reduceIte] at h1 ⊢
      dsimp only [denoteArg]; rw [h1]
    · have h1 := lookupV_append_mid vsPre vsNew vsPost t i
      simp only [ge_iff_le, hi, ↓reduceIte] at h1 ⊢
      dsimp only [denoteArg]; rw [h1]

public theorem denoteArgs_shiftTupAbove {V : Ty → Type}
    (vsPre vsNew vsPost : List ((t : Ty) × V t)) :
    {ts : List Ty} → (args : Tup (Arg K) ts) →
    denoteArgs (vsPre ++ (vsNew ++ vsPost)) (shiftTupAbove vsPre.length vsNew.length args) =
      denoteArgs (vsPre ++ vsPost) args
  | [], () => rfl
  | _ :: _, (a, as) => by
    dsimp only [shiftTupAbove]
    rw [denoteArgs_cons_eq, denoteArgs_cons_eq, denoteArg_shiftArgAbove,
      denoteArgs_shiftTupAbove vsPre vsNew vsPost as]

public theorem checkArg_shiftArgAbove (GPre GNew GPost : List Ty) (t : Ty) (a : Arg K t) :
    checkArg (GPre ++ (GNew ++ GPost)) t (shiftArgAbove GPre.length GNew.length a) =
      checkArg (GPre ++ GPost) t a := by
  cases a with
  | imm c => rfl
  | var i =>
    dsimp only [shiftArgAbove]
    by_cases hi : GPre.length ≤ i
    · simp only [ge_iff_le, hi, ↓reduceIte]; dsimp only [checkArg]
      rw [listGet?_append_mid_ge GPre GNew GPost i hi]
    · have hlt : i < GPre.length := Nat.lt_of_not_le hi
      simp only [ge_iff_le, hi, ↓reduceIte]; dsimp only [checkArg]
      rw [listGet?_append_mid_lt GPre GNew GPost i hlt]

public theorem checkArgs_shiftTupAbove (GPre GNew GPost : List Ty) :
    {ts : List Ty} → (args : Tup (Arg K) ts) →
    checkArgs (GPre ++ (GNew ++ GPost)) (shiftTupAbove GPre.length GNew.length args) =
      checkArgs (GPre ++ GPost) args
  | [], () => rfl
  | _ :: _, (a, as) => by
    dsimp only [shiftTupAbove, checkArgs]
    rw [checkArg_shiftArgAbove, checkArgs_shiftTupAbove GPre GNew GPost as]

mutual
public theorem wfCheck_shiftTFlat {rs : List Ty} (GPre GNew GPost : List Ty) (D : List (List Ty)) :
    (tf : TFlat rs) →
    (shiftTFlat GPre.length GNew.length tf).wfCheck (GPre ++ (GNew ++ GPost)) D =
      tf.wfCheck (GPre ++ GPost) D
  | .let_ (ts := ts) ⟨code, args⟩ k => by
    unfold shiftTFlat
    rw [wfCheck_let_eq, wfCheck_let_eq, checkArgs_shiftTupAbove]
    have hk := wfCheck_shiftTFlat (pushTypes ts GPre) GNew GPost D k
    rw [pushTypes_length] at hk
    rw [pushTypes_append, pushTypes_append, hk]
  | .load t a k => by
    unfold shiftTFlat
    rw [wfCheck_load_eq, wfCheck_load_eq, checkArg_shiftArgAbove]
    have hk := wfCheck_shiftTFlat (t :: GPre) GNew GPost D k
    rw [List.cons_append, List.cons_append] at hk
    exact congrArg _ hk
  | .store v a k => by
    unfold shiftTFlat
    rw [wfCheck_store_eq, wfCheck_store_eq, checkArg_shiftArgAbove, checkArg_shiftArgAbove,
      wfCheck_shiftTFlat GPre GNew GPost D k]
  | .call f bs args k => by
    unfold shiftTFlat
    rw [wfCheck_call_eq, wfCheck_call_eq, checkArgs_shiftTupAbove]
    have hk := wfCheck_shiftTFlat (pushTypes bs GPre) GNew GPost D k
    rw [pushTypes_length] at hk
    rw [pushTypes_append, pushTypes_append, hk]
  | .jnz c t e => by
    unfold shiftTFlat
    rw [wfCheck_jnz_eq, wfCheck_jnz_eq, checkArg_shiftArgAbove,
      wfCheck_shiftTFlat GPre GNew GPost D t, wfCheck_shiftTFlat GPre GNew GPost D e]
  | .jump j args => by
    unfold shiftTFlat; rw [wfCheck_jump_eq, wfCheck_jump_eq, checkArgs_shiftTupAbove]
  | .ret vs => by
    unfold shiftTFlat; rw [wfCheck_ret_eq, wfCheck_ret_eq, checkArgs_shiftTupAbove]
  | .exit f args => by
    unfold shiftTFlat; rw [wfCheck_exit_eq, wfCheck_exit_eq, checkArgs_shiftTupAbove]
  | .hlt => by unfold shiftTFlat; rfl
  | .group (sig := sig) bs k => by
    unfold shiftTFlat
    rw [wfCheck_group_eq, wfCheck_group_eq,
      wfCheck_shiftTBlocks GPre GNew GPost (pushTypes sig D) bs,
      wfCheck_shiftTFlat GPre GNew GPost (pushTypes sig D) k]

public theorem wfCheck_shiftTBlocks {rs : List Ty} (GPre GNew GPost : List Ty)
    (D : List (List Ty)) :
    {sig : List (List Ty)} → (bs : TBlocks rs sig) →
    (shiftTBlocks GPre.length GNew.length bs).wfCheck (GPre ++ (GNew ++ GPost)) D =
      bs.wfCheck (GPre ++ GPost) D
  | _, .nil => by unfold shiftTBlocks; rfl
  | _, .cons (ts := ts) b bs => by
    unfold shiftTBlocks
    rw [wfCheckB_cons_eq, wfCheckB_cons_eq]
    have hb := wfCheck_shiftTFlat (pushTypes ts GPre) GNew GPost D b
    have hbs := wfCheck_shiftTBlocks GPre GNew GPost D bs
    rw [pushTypes_length] at hb
    rw [pushTypes_append, pushTypes_append, hb, hbs]
end

mutual
public theorem denote_shiftTFlat (V : Ty → Type) (L : List Ty → Type) {rs : List Ty} :
    (tf : TFlat rs) → (vsPre vsNew vsPost : List ((t : Ty) × V t)) →
    (ls : List ((ts : List Ty) × L ts)) →
    denote V L (shiftTFlat vsPre.length vsNew.length tf) (vsPre ++ (vsNew ++ vsPost)) ls =
      denote V L tf (vsPre ++ vsPost) ls
  | .let_ (ts := ts) ⟨code, args⟩ k, vsPre, vsNew, vsPost, ls => by
    unfold shiftTFlat
    rw [denote_let_eq, denote_let_eq, denoteArgs_shiftTupAbove]
    cases denoteArgs (vsPre ++ vsPost) args with
    | none => rfl
    | some args' =>
      dsimp only
      congr 1; funext res
      have hk := denote_shiftTFlat V L k (pushTup res vsPre) vsNew vsPost ls
      rw [pushTup_length] at hk
      rw [pushTup_append, pushTup_append]
      exact hk
  | .load t a k, vsPre, vsNew, vsPost, ls => by
    unfold shiftTFlat
    rw [denote_load_eq, denote_load_eq, denoteArg_shiftArgAbove]
    cases denoteArg (vsPre ++ vsPost) a with
    | none => rfl
    | some a' =>
      dsimp only
      congr 1; funext v
      have hk := denote_shiftTFlat V L k (⟨t, v⟩ :: vsPre) vsNew vsPost ls
      rw [List.cons_append, List.cons_append] at hk
      exact hk
  | .store v a k, vsPre, vsNew, vsPost, ls => by
    unfold shiftTFlat
    rw [denote_store_eq, denote_store_eq, denoteArg_shiftArgAbove, denoteArg_shiftArgAbove,
      denote_shiftTFlat V L k vsPre vsNew vsPost ls]
  | .call f bs args k, vsPre, vsNew, vsPost, ls => by
    unfold shiftTFlat
    rw [denote_call_eq, denote_call_eq, denoteArgs_shiftTupAbove]
    cases denoteArgs (vsPre ++ vsPost) args with
    | none => rfl
    | some args' =>
      dsimp only
      congr 1; funext res
      have hk := denote_shiftTFlat V L k (pushTup res vsPre) vsNew vsPost ls
      rw [pushTup_length] at hk
      rw [pushTup_append, pushTup_append]
      exact hk
  | .jnz c t e, vsPre, vsNew, vsPost, ls => by
    unfold shiftTFlat
    rw [denote_jnz_eq, denote_jnz_eq, denoteArg_shiftArgAbove,
      denote_shiftTFlat V L t vsPre vsNew vsPost ls,
      denote_shiftTFlat V L e vsPre vsNew vsPost ls]
  | .jump j args, vsPre, vsNew, vsPost, ls => by
    unfold shiftTFlat; rw [denote_jump_eq, denote_jump_eq, denoteArgs_shiftTupAbove]
  | .ret vs, vsPre, vsNew, vsPost, ls => by
    unfold shiftTFlat; rw [denote_ret_eq, denote_ret_eq, denoteArgs_shiftTupAbove]
  | .exit f args, vsPre, vsNew, vsPost, ls => by
    unfold shiftTFlat; rw [denote_exit_eq, denote_exit_eq, denoteArgs_shiftTupAbove]
  | .hlt, _, _, _, _ => by unfold shiftTFlat; rfl
  | .group (sig := sig) bs k, vsPre, vsNew, vsPost, ls => by
    unfold shiftTFlat
    rw [denote_group_eq, denote_group_eq]
    congr 1
    · funext Js; exact denoteB_shiftTBlocks V L bs vsPre vsNew vsPost (pushTup Js ls)
    · funext Js; exact denote_shiftTFlat V L k vsPre vsNew vsPost (pushTup Js ls)

public theorem denoteB_shiftTBlocks (V : Ty → Type) (L : List Ty → Type) {rs : List Ty} :
    {sig : List (List Ty)} → (bs : TBlocks rs sig) →
    (vsPre vsNew vsPost : List ((t : Ty) × V t)) → (ls : List ((ts : List Ty) × L ts)) →
    denoteB V L (shiftTBlocks vsPre.length vsNew.length bs) (vsPre ++ (vsNew ++ vsPost)) ls =
      denoteB V L bs (vsPre ++ vsPost) ls
  | _, .nil, _, _, _, _ => by unfold shiftTBlocks; rfl
  | _, .cons (ts := ts) b bs, vsPre, vsNew, vsPost, ls => by
    unfold shiftTBlocks
    rw [denoteB_cons_eq, denoteB_cons_eq]
    congr 1
    · funext xs
      have hb := denote_shiftTFlat V L b (pushTup xs vsPre) vsNew vsPost ls
      rw [pushTup_length] at hb
      rw [pushTup_append, pushTup_append]
      exact hb
    · exact denoteB_shiftTBlocks V L bs vsPre vsNew vsPost ls
end

/-! ## `letBindTup` lemmas -/

public theorem denoteArgs_singleton_eq {V : Ty → Type} (vs : List ((t : Ty) × V t))
    {t : Ty} (a : Arg K t) :
    denoteArgs vs (ts := [t]) (a, ()) =
      match denoteArg vs a with
      | some a' => some (a', ())
      | none => none := by
  rw [denoteArgs_cons_eq (ts := []), denoteArgs_nil_eq]
  cases denoteArg vs a <;> rfl

public theorem wfCheck_letBindTup {rs : List Ty} {D : List (List Ty)} :
    {ts : List Ty} → (args : Tup (Arg K) ts) → (GAcc GBase : List Ty) → (cont : TFlat rs) →
    checkArgs GBase args = true →
    cont.wfCheck (pushTypes ts (GAcc ++ GBase)) D = true →
    (letBindTup args GAcc.length cont).wfCheck (GAcc ++ GBase) D = true
  | [], (), _, _, _, _, hcont => hcont
  | t :: ts, (a, args), GAcc, GBase, cont, hargs, hcont => by
    dsimp only [checkArgs] at hargs; rw [Bool.and_eq_true] at hargs
    have ha : checkArg (GAcc ++ GBase) t (shiftArgAbove 0 GAcc.length a) = true :=
      (checkArg_shiftArgAbove [] GAcc GBase t a).trans hargs.1
    dsimp only [letBindTup]
    rw [wfCheck_let_eq]
    dsimp only [op1, checkArgs]; rw [Bool.and_true, ha, Bool.true_and]
    rw [pushTypes_cons_eq] at hcont ⊢
    rw [← List.cons_append] at hcont
    exact wfCheck_letBindTup args (t :: GAcc) GBase cont hargs.2 hcont

public theorem denote_letBindTup_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} :
    {ts : List Ty} → (args : Tup (Arg K) ts) → (acc vsBase : List ((t : Ty) × Val t)) →
    (ls : List ((ts : List Ty) × Cont ts)) → (cont : TFlat rs) → (m : Mem 64) →
    {valArgs : Tup (Arg Val) ts} → denoteArgs vsBase args = some valArgs →
    wp Γ Q X (denote Val Cont cont (pushTup (vals valArgs) (acc ++ vsBase)) ls) m →
    wp Γ Q X (denote Val Cont (letBindTup args acc.length cont) (acc ++ vsBase) ls) m
  | [], (), _, _, _, _, _, _, _, hwp => hwp
  | t :: ts, (a, args), acc, vsBase, ls, cont, m, valArgs, hargs, hwp => by
    rw [denoteArgs_cons_eq] at hargs
    cases hda : denoteArg vsBase a with
    | none => rw [hda] at hargs; cases hargs
    | some av =>
      cases hdr : denoteArgs vsBase args with
      | none => rw [hda, hdr] at hargs; cases hargs
      | some rest =>
        rw [hda, hdr] at hargs
        cases hargs
        have ha' : denoteArg (acc ++ vsBase) (shiftArgAbove 0 acc.length a) = some av :=
          (denoteArg_shiftArgAbove [] acc vsBase a).trans hda
        dsimp only [letBindTup]
        rw [denote_let_eq]
        dsimp only [op1]
        rw [denoteArgs_singleton_eq, ha']
        dsimp only
        rw [wp_let]
        dsimp only [Op.wp]; rw [OpCode.wp_copy]
        dsimp only [vals, pushTup] at hwp ⊢
        rw [← List.cons_append] at hwp
        exact denote_letBindTup_wp args (⟨t, av.val⟩ :: acc) vsBase ls cont m hdr hwp

/-! ## `lfp` unrolling and `inlineJump0` / `peelSingle` correctness -/

private theorem diagV_zip : {ts : List Ty} → (xs : Tup Val ts) → {G : Ctx Val Val} → DiagV G →
    DiagV (xs.zip xs ++ G)
  | [], (), _, hG => hG
  | _ :: _, (x, xs), _, hG => fun p hp => by
    simp only [Tup.zip, List.cons_append, List.mem_cons] at hp
    rcases hp with rfl | hp
    · rfl
    · exact diagV_zip xs hG p hp

public theorem lfp_unroll_single {Γ : Env} {rs ts0 : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx Val Val} {D : Ctx Cont Cont}
    {bodies : Tup Cont [ts0] → Blocks Val Cont rs [ts0]}
    (hG : DiagV G) (hD : MonoD D)
    (hwf : ∀ Js₁ Js₂ : Tup Cont [ts0], WfB G (Js₁.zip Js₂ ++ D) (bodies Js₁) (bodies Js₂)) :
    ∀ (xs : Tup Val ts0) (m : Mem 64),
      (lfp Γ Q X bodies).1 xs m → wp Γ Q X ((bodies (lfp Γ Q X bodies)).get .here xs) m := by
  let JsStar := lfp Γ Q X bodies
  let JStep : Tup Cont [ts0] :=
    (fun xs m' => wp Γ Q X ((bodies JsStar).get .here xs) m', ())
  have hclStar := lfp_closed (Γ := Γ) (Q := Q) (X := X) hG hD hwf
  rw [closed_iff] at hclStar
  have hle : ∀ xs m', JStep.1 xs m' → JsStar.1 xs m' := fun xs m' hs => hclStar .here xs m' hs
  have hclStep : Closed Γ Q X (bodies JStep) JStep := by
    rw [closed_iff]
    intro _ i xs m' hb
    cases i with
    | here =>
      have hwfb := hwf JStep JsStar
      have hm : MonoD (JStep.zip JsStar ++ D) := by
        intro p hp
        simp only [Tup.zip, List.cons_append, List.nil_append, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact fun xs' m'' h => hle xs' m'' h
        · exact hD p hp
      have hrel := hwfb.get .here xs xs
      exact wp_label_mono hrel (diagV_zip xs hG) hm m' hb
    | there i => exact nomatch i
  intro xs m h
  exact lfp_le hclStep .here xs m h

public theorem wfCheck_inlineJump0 {rs : List Ty} {ts0 : List Ty} {G : List Ty}
    {D : List (List Ty)} {body : TFlat rs}
    (hbody : body.wfCheck (pushTypes ts0 G) (ts0 :: D) = true) :
    (k : TFlat rs) → {GLocal : List Ty} →
      hasGroup k = false →
      k.wfCheck (GLocal ++ G) (ts0 :: D) = true →
      (inlineJump0 body ts0 GLocal.length k).wfCheck (GLocal ++ G) (ts0 :: D) = true
  | .let_ (ts := ts) op k, GLocal, hg, hk => by
    dsimp only [hasGroup] at hg
    rw [wfCheck_let_eq, Bool.and_eq_true] at hk
    dsimp only [inlineJump0]
    rw [wfCheck_let_eq, Bool.and_eq_true]
    refine ⟨hk.1, ?_⟩
    have hrec := wfCheck_inlineJump0 hbody k (GLocal := pushTypes ts GLocal) hg
      (by rw [← pushTypes_append]; exact hk.2)
    rw [← pushTypes_append, pushTypes_length] at hrec; exact hrec
  | .load t a k, GLocal, hg, hk => by
    dsimp only [hasGroup] at hg
    rw [wfCheck_load_eq, Bool.and_eq_true] at hk
    dsimp only [inlineJump0]
    rw [wfCheck_load_eq, Bool.and_eq_true]
    refine ⟨hk.1, ?_⟩
    have hrec := wfCheck_inlineJump0 hbody k (GLocal := t :: GLocal) hg
      (by rw [List.cons_append]; exact hk.2)
    rw [List.length_cons, List.cons_append] at hrec; exact hrec
  | .store v a k, GLocal, hg, hk => by
    dsimp only [hasGroup] at hg
    rw [wfCheck_store_eq, Bool.and_eq_true] at hk
    dsimp only [inlineJump0]
    rw [wfCheck_store_eq, Bool.and_eq_true]
    exact ⟨hk.1, wfCheck_inlineJump0 hbody k hg hk.2⟩
  | .call f bs args k, GLocal, hg, hk => by
    dsimp only [hasGroup] at hg
    rw [wfCheck_call_eq, Bool.and_eq_true] at hk
    dsimp only [inlineJump0]
    rw [wfCheck_call_eq, Bool.and_eq_true]
    refine ⟨hk.1, ?_⟩
    have hrec := wfCheck_inlineJump0 hbody k (GLocal := pushTypes bs GLocal) hg
      (by rw [← pushTypes_append]; exact hk.2)
    rw [← pushTypes_append, pushTypes_length] at hrec; exact hrec
  | .jnz c t e, GLocal, hg, hk => by
    dsimp only [hasGroup] at hg; rw [Bool.or_eq_false_iff] at hg
    rw [wfCheck_jnz_eq, Bool.and_eq_true, Bool.and_eq_true] at hk
    dsimp only [inlineJump0]
    rw [wfCheck_jnz_eq, Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨hk.1.1, wfCheck_inlineJump0 hbody t hg.1 hk.1.2⟩,
      wfCheck_inlineJump0 hbody e hg.2 hk.2⟩
  | .jump (ts := ts) j args, GLocal, _, hk => by
    dsimp only [inlineJump0]
    split
    · split
      · next h =>
        subst h
        rw [wfCheck_jump_eq, Bool.and_eq_true] at hk
        refine wfCheck_letBindTup args [] (GLocal ++ G) _ hk.2 ?_
        have hsh := wfCheck_shiftTFlat (pushTypes ts []) GLocal G (ts :: D) body
        rw [pushTypes_length, List.length_nil, Nat.zero_add,
          ← pushTypes_append, ← pushTypes_append] at hsh
        rw [List.nil_append] at hsh ⊢
        rw [hsh]; exact hbody
      · exact hk
    · exact hk
  | .ret _, _, _, hk => hk
  | .exit _ _, _, _, hk => hk
  | .hlt, _, _, hk => hk
  | .group _ _, _, hg, _ => by dsimp only [hasGroup] at hg; cases hg

public theorem castListTy_self {L : List Ty → Type} (ts : List Ty) (l : L ts) :
    castListTy ts ts l = some l := by
  dsimp only [castListTy]
  cases listTyDecEq ts ts with
  | isTrue _ => rfl
  | isFalse h => exact absurd rfl h

public theorem inlineJump0_wp {Γ : Env} {rs ts0 : List Ty} {Q : Post rs} {X : XPost}
    {G : List Ty} {D : List (List Ty)}
    {vs : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    (hvs : CtxTypes G vs) (hls : CtxTypes D ls)
    {body : TFlat rs} {JStar : Cont ts0}
    (hUnroll : ∀ xs m, JStar xs m →
      wp Γ Q X (denote Val Cont body (pushTup xs vs) (⟨ts0, JStar⟩ :: ls)) m) :
    (k : TFlat rs) → {GLocal : List Ty} → {vsLocal : List ((t : Ty) × Val t)} → {m : Mem 64} →
      CtxTypes GLocal vsLocal →
      hasGroup k = false →
      k.wfCheck (GLocal ++ G) (ts0 :: D) = true →
      wp Γ Q X (denote Val Cont k (vsLocal ++ vs) (⟨ts0, JStar⟩ :: ls)) m →
      wp Γ Q X (denote Val Cont (inlineJump0 body ts0 GLocal.length k)
        (vsLocal ++ vs) (⟨ts0, JStar⟩ :: ls)) m
  | .let_ (ts := ts) op k, GLocal, vsLocal, m, hvLoc, hg, hk, hwp => by
    dsimp only [hasGroup] at hg
    rw [wfCheck_let_eq, Bool.and_eq_true] at hk
    have hargs := denoteArgs_isSome_of_checkArgs (CtxTypes_append hvLoc hvs) hk.1
    cases hda : denoteArgs (vsLocal ++ vs) op.args with
    | none => rw [hda] at hargs; cases hargs
    | some args' =>
      rw [denote_let_eq, hda, wp_let] at hwp
      dsimp only [inlineJump0]
      rw [denote_let_eq, hda, wp_let]
      refine Op.wp_mono (fun res hr => ?_) hwp
      have hrec := inlineJump0_wp hvs hls hUnroll k (GLocal := pushTypes ts GLocal)
        (vsLocal := pushTup res vsLocal) (CtxTypes.push res hvLoc) hg
        (by rw [← pushTypes_append]; exact hk.2) (by rw [← pushTup_append]; exact hr)
      rw [pushTypes_length, ← pushTup_append] at hrec; exact hrec
  | .load t a k, GLocal, vsLocal, m, hvLoc, hg, hk, hwp => by
    dsimp only [hasGroup] at hg
    rw [wfCheck_load_eq, Bool.and_eq_true] at hk
    have ha := denoteArg_isSome_of_checkArg (CtxTypes_append hvLoc hvs) hk.1
    cases hda : denoteArg (vsLocal ++ vs) a with
    | none => rw [hda] at ha; cases ha
    | some a' =>
      rw [denote_load_eq, hda, wp_load] at hwp
      rcases hwp with ⟨v, hv, hk_wp⟩
      dsimp only [inlineJump0]
      rw [denote_load_eq, hda, wp_load]
      refine ⟨v, hv, ?_⟩
      have hrec := inlineJump0_wp hvs hls hUnroll k (GLocal := t :: GLocal)
        (vsLocal := ⟨t, v⟩ :: vsLocal) (.cons hvLoc) hg
        (by rw [List.cons_append]; exact hk.2) (by rw [List.cons_append]; exact hk_wp)
      rw [List.length_cons, List.cons_append] at hrec; exact hrec
  | .store v a k, GLocal, vsLocal, m, hvLoc, hg, hk, hwp => by
    dsimp only [hasGroup] at hg
    rw [wfCheck_store_eq, Bool.and_eq_true, Bool.and_eq_true] at hk
    have hct := CtxTypes_append hvLoc hvs
    have hv := denoteArg_isSome_of_checkArg hct hk.1.1
    have ha := denoteArg_isSome_of_checkArg hct hk.1.2
    cases hdv : denoteArg (vsLocal ++ vs) v with
    | none => rw [hdv] at hv; cases hv
    | some v' =>
      cases hda : denoteArg (vsLocal ++ vs) a with
      | none => rw [hda] at ha; cases ha
      | some a' =>
        rw [denote_store_eq, hdv, hda, wp_store] at hwp
        dsimp only [inlineJump0]
        rw [denote_store_eq, hdv, hda, wp_store]
        exact ⟨hwp.1, inlineJump0_wp hvs hls hUnroll k hvLoc hg hk.2 hwp.2⟩
  | .call f bs args k, GLocal, vsLocal, m, hvLoc, hg, hk, hwp => by
    dsimp only [hasGroup] at hg
    rw [wfCheck_call_eq, Bool.and_eq_true] at hk
    have hargs := denoteArgs_isSome_of_checkArgs (CtxTypes_append hvLoc hvs) hk.1
    cases hda : denoteArgs (vsLocal ++ vs) args with
    | none => rw [hda] at hargs; cases hargs
    | some args' =>
      rw [denote_call_eq, hda, wp_call_eq] at hwp
      rcases hwp with ⟨P, E, hG', hP, hE⟩
      dsimp only [inlineJump0]
      rw [denote_call_eq, hda, wp_call_eq]
      refine ⟨P, E, hG', fun res m' hres => ?_, hE⟩
      have hrec := inlineJump0_wp hvs hls hUnroll k (GLocal := pushTypes bs GLocal)
        (vsLocal := pushTup res vsLocal) (CtxTypes.push res hvLoc) hg
        (by rw [← pushTypes_append]; exact hk.2)
        (by rw [← pushTup_append]; exact hP res m' hres)
      rw [pushTypes_length, ← pushTup_append] at hrec; exact hrec
  | .jnz c t e, GLocal, vsLocal, m, hvLoc, hg, hk, hwp => by
    dsimp only [hasGroup] at hg; rw [Bool.or_eq_false_iff] at hg
    rw [wfCheck_jnz_eq, Bool.and_eq_true, Bool.and_eq_true] at hk
    have hc := denoteArg_isSome_of_checkArg (CtxTypes_append hvLoc hvs) hk.1.1
    cases hdc : denoteArg (vsLocal ++ vs) c with
    | none => rw [hdc] at hc; cases hc
    | some c' =>
      rw [denote_jnz_eq, hdc, wp_jnz] at hwp
      dsimp only [inlineJump0]
      rw [denote_jnz_eq, hdc, wp_jnz]
      exact ⟨fun h => inlineJump0_wp hvs hls hUnroll t hvLoc hg.1 hk.1.2 (hwp.1 h),
        fun h => inlineJump0_wp hvs hls hUnroll e hvLoc hg.2 hk.2 (hwp.2 h)⟩
  | .jump (ts := ts) j args, GLocal, vsLocal, m, hvLoc, _, hk, hwp => by
    dsimp only [inlineJump0]
    cases j with
    | zero =>
      rw [ite_eq_left (by decide)]
      split
      · next h =>
        subst h
        rw [wfCheck_jump_eq, Bool.and_eq_true] at hk
        have hargs := denoteArgs_isSome_of_checkArgs (CtxTypes_append hvLoc hvs) hk.2
        cases hda : denoteArgs (vsLocal ++ vs) args with
        | none => rw [hda] at hargs; cases hargs
        | some args' =>
          rw [denote_jump_eq, hda] at hwp
          dsimp only [lookupL, listGet?] at hwp
          rw [castListTy_self] at hwp
          dsimp only at hwp
          rw [wp_jump] at hwp
          rw [← CtxTypes_length hvLoc]
          refine denote_letBindTup_wp args [] (vsLocal ++ vs) (⟨ts, JStar⟩ :: ls) _ m hda ?_
          have hsh := denote_shiftTFlat Val Cont body (pushTup (vals args') []) vsLocal vs
            (⟨ts, JStar⟩ :: ls)
          rw [pushTup_length, List.length_nil, Nat.zero_add] at hsh
          rw [pushTup_append (vals args') [] (vsLocal ++ vs), hsh,
            ← pushTup_append (vals args') [] vs]
          exact hUnroll (vals args') m hwp
      · exact hwp
    | succ _ => exact hwp
  | .ret _, _, _, _, _, _, _, hwp => hwp
  | .exit _ _, _, _, _, _, _, _, hwp => hwp
  | .hlt, _, _, _, _, _, _, hwp => hwp
  | .group _ _, _, _, _, _, hg, _, _ => by dsimp only [hasGroup] at hg; cases hg

public theorem wfCheck_peelSingle {cfg : ZeroPeelConfig} {rs ts0 : List Ty}
    {G : List Ty} {D : List (List Ty)} {body k g : TFlat rs}
    (hb : body.wfCheck (pushTypes ts0 G) (ts0 :: D) = true)
    (hk : k.wfCheck G (ts0 :: D) = true)
    (hp : peelSingle cfg ts0 body k = some g) :
    g.wfCheck G D = true := by
  dsimp only [peelSingle] at hp
  split at hp
  · next hcond =>
    cases hp
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
    have hhg : hasGroup k = false := hcond.1.2
    rw [wfCheck_group_eq, wfCheckB_cons_eq, wfCheckB_nil_eq]
    dsimp only [pushTypes]; rw [Bool.and_true, Bool.and_eq_true]
    exact ⟨hb, wfCheck_inlineJump0 hb k (GLocal := []) hhg hk⟩
  · cases hp

public theorem ctx_diagV_of_vs {vs : List ((t : Ty) × Val t)} :
    DiagV (List.map (fun ⟨t, v⟩ => ⟨t, (v, v)⟩) vs) := by
  intro p hp
  rcases List.mem_map.1 hp with ⟨⟨t, v⟩, _, rfl⟩
  rfl

public theorem ctx_monoD_of_ls {ls : List ((ts : List Ty) × Cont ts)} :
    MonoD (List.map (fun ⟨ts, l⟩ => ⟨ts, (l, l)⟩) ls) := by
  intro p hp
  rcases List.mem_map.1 hp with ⟨_, _, rfl⟩
  exact fun _ _ h => h

public theorem ctxRel_refl_vs {V : Ty → Type} {vs : List ((t : Ty) × V t)} :
    CtxRel (List.map (fun ⟨t, v⟩ => ⟨t, (v, v)⟩) vs) vs vs := by
  induction vs with
  | nil => exact .nil
  | cons _ _ ih =>
    exact .cons List.mem_cons_self (CtxRel.mono (fun _ => List.mem_cons_of_mem _) ih)

public theorem ctxRel_refl_ls {L : List Ty → Type} {ls : List ((ts : List Ty) × L ts)} :
    CtxRel (List.map (fun ⟨ts, l⟩ => ⟨ts, (l, l)⟩) ls) ls ls := by
  induction ls with
  | nil => exact .nil
  | cons _ _ ih =>
    exact .cons List.mem_cons_self (CtxRel.mono (fun _ => List.mem_cons_of_mem _) ih)

public theorem peelSingle_wp {cfg : ZeroPeelConfig} {Γ : Env} {rs ts0 : List Ty}
    {Q : Post rs} {X : XPost} {G : List Ty} {D : List (List Ty)}
    {vs : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    (hvs : CtxTypes G vs) (hls : CtxTypes D ls)
    {body k g : TFlat rs} {m : Mem 64}
    (hkWf : k.wfCheck G (ts0 :: D) = true)
    (hp : peelSingle cfg ts0 body k = some g)
    (hSrc : wp Γ Q X (denote Val Cont (.group (sig := [ts0]) (.cons body .nil) k) vs ls) m) :
    wp Γ Q X (denote Val Cont g vs ls) m := by
  dsimp only [peelSingle] at hp
  split at hp
  · next hcond =>
    cases hp
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
    have hhg : hasGroup k = false := hcond.1.2
    let bodies : Tup Cont [ts0] → Blocks Val Cont rs [ts0] := fun Js =>
      denoteB Val Cont (.cons body .nil) vs (pushTup Js ls)
    let kSrc : Tup Cont [ts0] → Expr Val Cont rs := fun Js =>
      denote Val Cont k vs (pushTup Js ls)
    let kPeel : Tup Cont [ts0] → Expr Val Cont rs := fun Js =>
      denote Val Cont (inlineJump0 body ts0 0 k) vs (pushTup Js ls)
    have hG := ctx_diagV_of_vs (vs := vs)
    have hD := ctx_monoD_of_ls (ls := ls)
    have hwfB : ∀ Js₁ Js₂ : Tup Cont [ts0],
        WfB (List.map (fun ⟨t, v⟩ => ⟨t, (v, v)⟩) vs)
          (Js₁.zip Js₂ ++ List.map (fun ⟨ts, l⟩ => ⟨ts, (l, l)⟩) ls)
          (bodies Js₁) (bodies Js₂) := fun Js₁ Js₂ =>
      denoteB_wf (.cons body .nil) ctxRel_refl_vs (ctxRel_pushTup Js₁ Js₂ ctxRel_refl_ls)
    have hwfKSrc : ∀ Js₁ Js₂ : Tup Cont [ts0],
        Wf (List.map (fun ⟨t, v⟩ => ⟨t, (v, v)⟩) vs)
          (Js₁.zip Js₂ ++ List.map (fun ⟨ts, l⟩ => ⟨ts, (l, l)⟩) ls)
          (kSrc Js₁) (kSrc Js₂) := fun Js₁ Js₂ =>
      denote_wf k ctxRel_refl_vs (ctxRel_pushTup Js₁ Js₂ ctxRel_refl_ls)
    have hwfKPeel : ∀ Js₁ Js₂ : Tup Cont [ts0],
        Wf (List.map (fun ⟨t, v⟩ => ⟨t, (v, v)⟩) vs)
          (Js₁.zip Js₂ ++ List.map (fun ⟨ts, l⟩ => ⟨ts, (l, l)⟩) ls)
          (kPeel Js₁) (kPeel Js₂) := fun Js₁ Js₂ =>
      denote_wf (inlineJump0 body ts0 0 k) ctxRel_refl_vs (ctxRel_pushTup Js₁ Js₂ ctxRel_refl_ls)
    rw [denote_group_eq] at hSrc
    rw [denote_group_eq]
    change wp Γ Q X (.group bodies kSrc) m at hSrc
    change wp Γ Q X (.group bodies kPeel) m
    rw [wp_group_iff hG hD hwfB hwfKSrc] at hSrc
    rw [wp_group_iff hG hD hwfB hwfKPeel]
    let JsStar := lfp Γ Q X bodies
    have hUnroll : ∀ xs m', JsStar.1 xs m' →
        wp Γ Q X (denote Val Cont body (pushTup xs vs) (⟨ts0, JsStar.1⟩ :: ls)) m' :=
      fun xs m' hj => lfp_unroll_single hG hD hwfB xs m' hj
    exact inlineJump0_wp hvs hls hUnroll k (GLocal := []) (vsLocal := []) .nil hhg hkWf hSrc
  · cases hp

/-! ## Byte-splatting & `Mem.storeBytes` algebra -/

private theorem toBytes_toInt_eq_toNat (n : Nat) (v : BitVec (8 * n)) :
    Int.toBytes n v.toInt = Int.toBytes n (v.toNat : Int) := by
  rw [← Int.toBytes_emod n v.toInt, ← Int.toBytes_emod n (v.toNat : Int)]
  congr 1
  simp only [Int.take]
  have hlt := v.isLt
  have hc := BitVec.toInt_eq_toNat_cond v
  have hp : ((2 ^ (8 * n) : Nat) : Int) = (2 : Int) ^ (8 * n) := by push_cast; rfl
  rw [← hp]
  split at hc
  · rw [hc]
  · rw [hc]
    have hmod :
        ((v.toNat : Int) - ((2 ^ (8 * n) : Nat) : Int)) % ((2 ^ (8 * n) : Nat) : Int) =
          (v.toNat : Int) % ((2 ^ (8 * n) : Nat) : Int) := by
      have h1 : (v.toNat : Int) - ((2 ^ (8 * n) : Nat) : Int) =
          (v.toNat : Int) + (-1) * ((2 ^ (8 * n) : Nat) : Int) := by omega
      rw [h1, Int.add_mul_emod_self_right]
    rw [hmod]

private theorem toBytes_add (a b : Nat) (x : Nat) :
    Int.toBytes (a + b) (x : Int) =
      Int.toBytes a (x : Int) ++ Int.toBytes b ((x / 256 ^ a : Nat) : Int) := by
  induction a generalizing x with
  | zero => rw [Nat.zero_add, Nat.pow_zero, Nat.div_one]; rfl
  | succ a ih =>
    rw [Nat.succ_add]
    dsimp only [Int.toBytes]
    congr 1
    have hd : ((x : Int) / 256) = ((x / 256 : Nat) : Int) := by omega
    rw [hd, ih (x / 256), Nat.div_div_eq_div_mul, ← Nat.pow_succ']
    rfl

private theorem toBytes_add_mul (a b x y : Nat) (hx : x < 2 ^ (8 * a)) :
    Int.toBytes (a + b) ((x + 2 ^ (8 * a) * y : Nat) : Int) =
      Int.toBytes a (x : Int) ++ Int.toBytes b (y : Int) := by
  have hp : 256 ^ a = 2 ^ (8 * a) := by
    rw [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul]
  rw [toBytes_add, hp]
  congr 1
  · rw [← Int.toBytes_emod a ((x + 2 ^ (8 * a) * y : Nat) : Int), ← Int.toBytes_emod a (x : Int)]
    congr 1
    simp only [Int.take]
    have hpz : ((2 ^ (8 * a) : Nat) : Int) = (2 : Int) ^ (8 * a) := by push_cast; rfl
    rw [← hpz]
    push_cast
    rw [Int.add_mul_emod_self_left]
  · have hd : (x + 2 ^ (8 * a) * y) / 2 ^ (8 * a) = y := by
      rw [Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide)), Nat.div_eq_of_lt hx]; omega
    rw [hd]

private theorem nat_lor_two_mul (a b : Nat) :
    a ||| (2 * b) = 2 * ((a / 2) ||| b) + a % 2 := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ j =>
    rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    have h1 : (2 * b) / 2 = b := by omega
    have h2 : (2 * ((a / 2) ||| b) + a % 2) / 2 = (a / 2) ||| b := by omega
    rw [h1, h2, Nat.testBit_or]

private theorem nat_lor_shiftLeft (k x y : Nat) (hx : x < 2 ^ k) :
    x ||| (y <<< k) = x + 2 ^ k * y := by
  induction k generalizing x y with
  | zero =>
    have hx0 : x = 0 := by omega
    subst hx0; simp
  | succ k ih =>
    have hsh : y <<< (k + 1) = 2 * (y <<< k) := by rw [Nat.shiftLeft_succ, Nat.mul_comm]
    rw [hsh, nat_lor_two_mul, ih (x / 2) y (by rw [Nat.pow_succ] at hx; omega)]
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]
    omega

private theorem dupHalf_toNat_eq (k : Nat) (x : BitVec 64)
    (hk : 2 * (8 * k) ≤ 64) (hx : x.toNat < 2 ^ (8 * k)) :
    (x ||| (x <<< (8 * k))).toNat = x.toNat + 2 ^ (8 * k) * x.toNat := by
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft]
  have hpow : 2 ^ (2 * (8 * k)) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hk
  have hpow2 : (2 ^ (8 * k)) * (2 ^ (8 * k)) = 2 ^ (2 * (8 * k)) := by
    rw [← Nat.pow_add, Nat.two_mul]
  have hsh : x.toNat <<< (8 * k) = 2 ^ (8 * k) * x.toNat := by
    rw [Nat.shiftLeft_eq, Nat.mul_comm]
  have hsh_lt : x.toNat <<< (8 * k) < 2 ^ 64 := by
    rw [hsh]
    calc 2 ^ (8 * k) * x.toNat < 2 ^ (8 * k) * 2 ^ (8 * k) :=
          Nat.mul_lt_mul_of_pos_left hx (Nat.pow_pos (by decide))
      _ = 2 ^ (2 * (8 * k)) := hpow2
      _ ≤ 2 ^ 64 := hpow
  rw [Nat.mod_eq_of_lt hsh_lt, nat_lor_shiftLeft (8 * k) x.toNat x.toNat hx]

private theorem dupHalf_toNat_lt (k : Nat) (x : BitVec 64)
    (hk : 2 * (8 * k) ≤ 64) (hx : x.toNat < 2 ^ (8 * k)) :
    (x ||| (x <<< (8 * k))).toNat < 2 ^ (2 * (8 * k)) := by
  rw [dupHalf_toNat_eq k x hk hx]
  have hpow2 : 2 ^ (2 * (8 * k)) = 2 ^ (8 * k) * 2 ^ (8 * k) := by
    rw [Nat.two_mul, Nat.pow_add]
  rw [hpow2]
  have h1 : x.toNat + 2 ^ (8 * k) * x.toNat < 2 ^ (8 * k) + 2 ^ (8 * k) * x.toNat :=
    Nat.add_lt_add_right hx _
  calc x.toNat + 2 ^ (8 * k) * x.toNat < 2 ^ (8 * k) * (x.toNat + 1) := by
        rw [Nat.mul_add, Nat.mul_one]; omega
    _ ≤ 2 ^ (8 * k) * 2 ^ (8 * k) := Nat.mul_le_mul_left _ hx

private theorem toBytes_bv64_mod (m : Nat) (hm : 8 * m ≤ 64) (x : BitVec 64) :
    Int.toBytes m x.toInt = Int.toBytes m (x.toNat : Int) := by
  rw [← Int.toBytes_emod m x.toInt, ← Int.toBytes_emod m (x.toNat : Int)]
  congr 1
  simp only [Int.take]
  have hc := BitVec.toInt_eq_toNat_cond x
  have hd : ((2 : Int) ^ (8 * m)) ∣ ((2 ^ 64 : Nat) : Int) := by
    refine ⟨(2 : Int) ^ (64 - 8 * m), ?_⟩
    have h1 : (2 : Int) ^ (8 * m) * (2 : Int) ^ (64 - 8 * m) = (2 : Int) ^ 64 := by
      rw [← Int.pow_add, Nat.add_sub_cancel' hm]
    exact_mod_cast h1.symm
  split at hc
  · rw [hc]
  · rw [hc]
    obtain ⟨q, hq⟩ := hd
    have heq : (x.toNat : Int) - ((2 ^ 64 : Nat) : Int) =
        (x.toNat : Int) + (-q) * ((2 : Int) ^ (8 * m)) := by
      rw [hq, Int.sub_eq_add_neg, Int.neg_mul, Int.mul_comm q]
    rw [heq, Int.add_mul_emod_self_right]

private theorem dupHalf_toBytes (k : Nat) (x : BitVec 64)
    (hk : 2 * (8 * k) ≤ 64) (hx : x.toNat < 2 ^ (8 * k)) :
    Int.toBytes (2 * k) (x ||| (x <<< (8 * k))).toInt =
      Int.toBytes k x.toInt ++ Int.toBytes k x.toInt := by
  let y := x ||| (x <<< (8 * k))
  have hy_nat : y.toNat = x.toNat + 2 ^ (8 * k) * x.toNat := dupHalf_toNat_eq k x hk hx
  have hy_bv : Int.toBytes (2 * k) y.toInt = Int.toBytes (2 * k) (y.toNat : Int) :=
    toBytes_bv64_mod (2 * k) (by omega) y
  have hx_bv : Int.toBytes k x.toInt = Int.toBytes k (x.toNat : Int) :=
    toBytes_bv64_mod k (by omega) x
  rw [hy_bv, hy_nat, show 2 * k = k + k by omega, toBytes_add_mul k k x.toNat x.toNat hx, hx_bv]

private theorem setWidth64_toNat_lt {n : Nat} (hn : n ≤ 64) (v : BitVec n) :
    (v.setWidth 64).toNat < 2 ^ n := by
  simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le v.isLt
    (Nat.pow_le_pow_right (by decide) hn))]
  exact v.isLt

private theorem toBytes_setWidth64_eq {n k : Nat} (hn : n ≤ 64) (hmul : 8 * k = n) (v : BitVec n) :
    Int.toBytes k (v.setWidth 64).toInt = Int.toBytes k v.toInt := by
  subst hmul
  rw [toBytes_toInt_eq_toNat k v, toBytes_bv64_mod k hn (v.setWidth 64)]
  have hsw : (v.setWidth 64).toNat = v.toNat := by
    simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le v.isLt
      (Nat.pow_le_pow_right (by decide) hn))]
  rw [hsw]

private theorem list_append_eq {α : Type} (xs ys : List α) : xs.append ys = xs ++ ys := rfl

public theorem splatVal64_spec {t : Ty} (v : Val t) {shift : Nat} {fill64 : BitVec 64}
    (h : splatVal64 v = some (shift, fill64)) :
    shift ≤ 3 ∧ t.bytes = 2 ^ shift ∧ (8 >>> shift) * t.bytes = 8 ∧
    Int.toBytes 8 fill64.toInt =
      List.flatten (List.replicate (8 >>> shift)
        (Int.toBytes t.bytes ((toBits t v).setWidth (8 * t.bytes)).toInt)) := by
  dsimp only [splatVal64] at h
  split at h
  · next v =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    have hx1 : (v.setWidth 64).toNat < 2 ^ 8 := setWidth64_toNat_lt (by decide) v
    have h8 := dupHalf_toBytes 1 (v.setWidth 64) (by decide) hx1
    have hx2_lt : ((v.setWidth 64) ||| ((v.setWidth 64) <<< 8)).toNat < 2 ^ 16 :=
      dupHalf_toNat_lt 1 (v.setWidth 64) (by decide) hx1
    have h16 := dupHalf_toBytes 2 ((v.setWidth 64) ||| ((v.setWidth 64) <<< 8)) (by decide) hx2_lt
    have hx4_lt : (((v.setWidth 64) ||| ((v.setWidth 64) <<< 8)) |||
        (((v.setWidth 64) ||| ((v.setWidth 64) <<< 8)) <<< 16)).toNat < 2 ^ 32 :=
      dupHalf_toNat_lt 2 _ (by decide) hx2_lt
    have h32 := dupHalf_toBytes 4 _ (by decide) hx4_lt
    have hb1 : Int.toBytes 1 (v.setWidth 64).toInt = Int.toBytes 1 v.toInt :=
      toBytes_setWidth64_eq (n := 8) (k := 1) (by decide) rfl v
    have hb1' : Int.toBytes (Ty.bits 8).bytes ((toBits (.bits 8) v).setWidth
        (8 * (Ty.bits 8).bytes)).toInt = Int.toBytes 1 v.toInt := rfl
    refine ⟨by decide, rfl, by decide, ?_⟩
    change Int.toBytes (2 * 4) _ = _
    rw [h32, h16, h8, hb1, ← hb1']
    simp only [show (8 >>> 0 : Nat) = 8 by decide, List.replicate, List.flatten, list_append_eq,
      List.append_assoc, List.append_nil]
  · next v =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    have hx2 : (v.setWidth 64).toNat < 2 ^ 16 := setWidth64_toNat_lt (by decide) v
    have h16 := dupHalf_toBytes 2 (v.setWidth 64) (by decide) hx2
    have hx4_lt : ((v.setWidth 64) ||| ((v.setWidth 64) <<< 16)).toNat < 2 ^ 32 :=
      dupHalf_toNat_lt 2 (v.setWidth 64) (by decide) hx2
    have h32 := dupHalf_toBytes 4 _ (by decide) hx4_lt
    have hb2 : Int.toBytes 2 (v.setWidth 64).toInt = Int.toBytes 2 v.toInt :=
      toBytes_setWidth64_eq (n := 16) (k := 2) (by decide) rfl v
    have hb2' : Int.toBytes (Ty.bits 16).bytes ((toBits (.bits 16) v).setWidth
        (8 * (Ty.bits 16).bytes)).toInt = Int.toBytes 2 v.toInt := rfl
    refine ⟨by decide, rfl, by decide, ?_⟩
    change Int.toBytes (2 * 4) _ = _
    rw [h32, h16, hb2, ← hb2']
    simp only [show (8 >>> 1 : Nat) = 4 by decide, List.replicate, List.flatten, list_append_eq,
      List.append_assoc, List.append_nil]
  · next v =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    have hx4 : (v.setWidth 64).toNat < 2 ^ 32 := setWidth64_toNat_lt (by decide) v
    have h32 := dupHalf_toBytes 4 (v.setWidth 64) (by decide) hx4
    have hb4 : Int.toBytes 4 (v.setWidth 64).toInt = Int.toBytes 4 v.toInt :=
      toBytes_setWidth64_eq (n := 32) (k := 4) (by decide) rfl v
    have hb4' : Int.toBytes (Ty.bits 32).bytes ((toBits (.bits 32) v).setWidth
        (8 * (Ty.bits 32).bytes)).toInt = Int.toBytes 4 v.toInt := rfl
    refine ⟨by decide, rfl, by decide, ?_⟩
    change Int.toBytes (2 * 4) _ = _
    rw [h32, hb4, ← hb4']
    simp only [show (8 >>> 2 : Nat) = 2 by decide, List.replicate, List.flatten, list_append_eq,
      List.append_nil]
  · next v =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    refine ⟨by decide, rfl, by decide, ?_⟩
    simp only [show (8 >>> 3 : Nat) = 1 by decide, List.replicate, List.flatten, list_append_eq,
      List.append_nil, Ty.bytes, toBits]
    rfl
  · cases h

private theorem union_assoc (m₁ m₂ m₃ : Mem 64) :
    (m₁.union m₂).union m₃ = m₁.union (m₂.union m₃) := by
  apply Std.ExtHashMap.ext_getElem?
  intro k
  simp only [Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union]
  cases m₁[k]? <;> cases m₂[k]? <;> simp

public theorem storeBytes_nil (m : Mem 64) (a : BitVec 64) :
    m.storeBytes a [] = m := by
  apply Std.ExtHashMap.ext_getElem?
  intro k
  simp [Mem.storeBytes, List.At, Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union]

public theorem storeBytes_append (m : Mem 64) (a : BitVec 64) (bs1 bs2 : List UInt8)
    (hlen : bs1.length + bs2.length ≤ 2 ^ 64) :
    (m.storeBytes a bs1).storeBytes (a + BitVec.ofNat 64 bs1.length) bs2 =
      m.storeBytes a (bs1 ++ bs2) := by
  simp only [Mem.storeBytes, union_assoc, ← List.At_append bs1 bs2 a hlen]

public theorem storeMem_eq_storeBytes (m : Mem 64) (t : Ty) (a : BitVec 64) (v : Val t) :
    storeMem m t a v =
      m.storeBytes a (Int.toBytes t.bytes ((toBits t v).setWidth (8 * t.bytes)).toInt) := by
  dsimp only [storeMem, Mem.storeInt]

private theorem list_mapM_some_iff {α β : Type} (f : α → Option β) :
    (xs : List α) → (∃ rs, List.mapM f xs = some rs) ↔ ∀ x ∈ xs, (f x).isSome = true
  | [] => by simp
  | x :: xs => by
    constructor
    · rintro ⟨rs, hrs⟩ y hy
      cases hfx : f x with
      | none =>
        have hnone : List.mapM f (x :: xs) = none := by simp [List.mapM_cons, hfx]
        simp [hnone] at hrs
      | some v =>
        simp only [List.mapM_cons, hfx, Option.pure_def, Option.bind_eq_bind,
          Option.bind_some, Option.bind_eq_some_iff] at hrs
        rcases hrs with ⟨rest, hrest, _⟩
        cases hy with
        | head => simp [hfx]
        | tail _ hy => exact (list_mapM_some_iff f xs).1 ⟨rest, hrest⟩ y hy
    · intro h
      have hx := h x List.mem_cons_self
      cases hfx : f x with
      | none => simp [hfx] at hx
      | some v =>
        obtain ⟨rest, hrest⟩ :=
          (list_mapM_some_iff f xs).2 (fun y hy => h y (List.mem_cons_of_mem _ hy))
        exact ⟨v :: rest, by simp [List.mapM_cons, hfx, hrest]⟩

public theorem storeOk_iff_forall_mem (m : Mem 64) (t : Ty) (a : BitVec 64) :
    storeOk m t a ↔ ∀ j < t.bytes, (m.get? (a + BitVec.ofNat 64 j)).isSome = true := by
  have h1 : storeOk m t a ↔ ∃ bs, m.loadBytes a t.bytes = some bs := by
    constructor
    · rintro ⟨i, hi⟩
      simp only [Mem.loadInt, Option.map_eq_some_iff] at hi
      exact ⟨hi.choose, hi.choose_spec.1⟩
    · rintro ⟨bs, hbs⟩
      exact ⟨Int.ofBytes bs, by simp [Mem.loadInt, hbs]⟩
  have hlb : m.loadBytes a t.bytes =
      List.mapM (fun j => m.get? (a + BitVec.ofNat 64 j)) (List.range t.bytes) := by
    simp [Mem.loadBytes, List.mapM_map, Function.comp_def]
  rw [h1, hlb, list_mapM_some_iff]
  constructor
  · intro hall j hj; exact hall j (List.mem_range.2 hj)
  · intro hall j hj; exact hall j (List.mem_range.1 hj)

private theorem get?_storeBytes_isSome_of_all_mem (m : Mem 64) (a : BitVec 64) (bs : List UInt8)
    (hmem : ∀ j < bs.length, (m.get? (a + BitVec.ofNat 64 j)).isSome = true) (k : BitVec 64) :
    ((m.storeBytes a bs).get? k).isSome = (m.get? k).isSome := by
  simp only [Mem.storeBytes, Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.union_eq,
    Std.ExtHashMap.getElem?_union]
  by_cases hkb : k ∈ bs.At a
  · obtain ⟨j, hj, rfl⟩ := (mem_At_iff bs a k).1 hkb
    have hm := hmem j hj
    rw [Std.ExtHashMap.get?_eq_getElem?] at hm
    cases hk1 : m[a + BitVec.ofNat 64 j]? with
    | none => simp [hk1] at hm
    | some v => simp
  · rw [Std.ExtHashMap.getElem?_eq_none hkb, Option.none_or]

public theorem storeOk_storeBytes_iff (m : Mem 64) (a : BitVec 64) (bs : List UInt8)
    (hmem : ∀ j < bs.length, (m.get? (a + BitVec.ofNat 64 j)).isSome = true)
    (u : Ty) (b : BitVec 64) :
    storeOk (m.storeBytes a bs) u b ↔ storeOk m u b := by
  simp only [storeOk_iff_forall_mem, get?_storeBytes_isSome_of_all_mem m a bs hmem]

public theorem storeOk_storeMem_iff (m : Mem 64) (t : Ty) (a : BitVec 64) (v : Val t)
    (hOk : storeOk m t a) (u : Ty) (b : BitVec 64) :
    storeOk (storeMem m t a v) u b ↔ storeOk m u b := by
  rw [storeOk_iff_forall_mem] at hOk
  rw [storeMem_eq_storeBytes]
  exact storeOk_storeBytes_iff m a _ (by simpa [Int.toBytes_length] using hOk) u b

public theorem storeOk_split_8 (m : Mem 64) (t : Ty) (ptr0 : BitVec 64)
    (unrollN k64 : Nat) (hk64 : k64 * t.bytes = 8) (ht_pos : 0 < t.bytes)
    (hScalar : ∀ j < unrollN * k64, storeOk m t (ptr0 + BitVec.ofNat 64 (t.bytes * j))) :
    ∀ r < unrollN, storeOk m i64 (ptr0 + BitVec.ofNat 64 (8 * r)) := by
  intro r hr
  rw [storeOk_iff_forall_mem]
  intro b hb
  change b < 8 at hb
  let j := k64 * r + b / t.bytes
  let rem := b % t.bytes
  have hdiv_lt : b / t.bytes < k64 := by
    refine Nat.div_lt_of_lt_mul ?_
    rw [Nat.mul_comm, hk64]
    exact hb
  have hj_lt : j < unrollN * k64 := by
    calc j = k64 * r + b / t.bytes := rfl
      _ < k64 * r + k64 := Nat.add_lt_add_left hdiv_lt _
      _ = k64 * (r + 1) := by rw [Nat.mul_succ]
      _ ≤ k64 * unrollN := Nat.mul_le_mul_left k64 hr
      _ = unrollN * k64 := Nat.mul_comm _ _
  have hrem_lt : rem < t.bytes := Nat.mod_lt b ht_pos
  have hS := (storeOk_iff_forall_mem m t (ptr0 + BitVec.ofNat 64 (t.bytes * j))).1
    (hScalar j hj_lt) rem hrem_lt
  have hidx : 8 * r + b = t.bytes * j + rem := by
    have hdm : t.bytes * (b / t.bytes) + rem = b := Nat.div_add_mod b t.bytes
    calc 8 * r + b = (k64 * t.bytes) * r + b := by rw [hk64]
      _ = t.bytes * (k64 * r) + (t.bytes * (b / t.bytes) + rem) := by
          rw [Nat.mul_comm k64 t.bytes, Nat.mul_assoc, hdm]
      _ = t.bytes * (k64 * r + b / t.bytes) + rem := by rw [Nat.mul_add, Nat.add_assoc]
  have haddr : (ptr0 + BitVec.ofNat 64 (8 * r)) + BitVec.ofNat 64 b =
      (ptr0 + BitVec.ofNat 64 (t.bytes * j)) + BitVec.ofNat 64 rem := by
    rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add, hidx]
  exact haddr ▸ hS

private theorem list_replicate_add {α : Type} (n m : Nat) (x : α) :
    List.replicate (n + m) x = List.replicate n x ++ List.replicate m x := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.succ_add, List.replicate_succ, List.replicate_succ, ih, List.cons_append]

public theorem flatten_replicate_flatten {α : Type} (n k : Nat) (xs : List α) :
    List.flatten (List.replicate n (List.flatten (List.replicate k xs))) =
      List.flatten (List.replicate (n * k) xs) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, ih, Nat.succ_mul, Nat.add_comm (n * k) k,
      list_replicate_add, List.flatten_append]

/-! ## Symbolic loop-body analysis & `widenFillSingle` proofs -/

public theorem array_getElem!_append_left {α : Type} [Inhabited α] (a b : Array α) (i : Nat)
    (hi : i < a.size) : (a ++ b)[i]! = a[i]! := by
  have hi2 : i < (a ++ b).size := by simp [Array.size_append]; omega
  rw [getElem!_pos (a ++ b) i hi2, getElem!_pos a i hi, Array.getElem_append_left hi]

public theorem array_getElem!_push_last {α : Type} [Inhabited α] (a : Array α) (x : α) :
    (a ++ #[x])[a.size]! = x := by
  have hi : a.size < (a ++ #[x]).size := by simp
  rw [getElem!_pos (a ++ #[x]) a.size hi, Array.getElem_append_right (Nat.le_refl _)]
  simp

public theorem array_getElem!_append_right {α : Type} [Inhabited α] (a b : Array α) (i : Nat)
    (hle : a.size ≤ i) (hlt : i < a.size + b.size) : (a ++ b)[i]! = b[i - a.size]! := by
  have hi : i < (a ++ b).size := by simp [Array.size_append]; exact hlt
  have hb : i - a.size < b.size := by omega
  rw [getElem!_pos (a ++ b) i hi, getElem!_pos b (i - a.size) hb, Array.getElem_append_right hle]

public theorem evalSymOp_len (env : Array Sym64) {ts : List Ty} (op : Op K ts) :
    (evalSymOp env op).length = ts.length := by
  dsimp only [evalSymOp]
  cases evalSymOp1 env op <;> cases ts with
  | nil => rfl
  | cons _ ts' => cases ts' <;> simp only [List.length_map] <;> rfl

public theorem denoteArgs_pair_eq {V : Ty → Type} (vs : List ((t : Ty) × V t))
    {t1 t2 : Ty} (a : Arg K t1) (b : Arg K t2) :
    denoteArgs vs (ts := [t1, t2]) (a, b, ()) =
      match denoteArg vs a, denoteArg vs b with
      | some a', some b' => some (a', b', ())
      | _, _ => none := by
  rw [denoteArgs_cons_eq (ts := [t2]), denoteArgs_singleton_eq]
  cases denoteArg vs a <;> cases denoteArg vs b <;> rfl

public theorem checkArgs_pair_eq (G : List Ty) {t1 t2 : Ty} (a : Arg K t1) (b : Arg K t2) :
    checkArgs G (ts := [t1, t2]) (a, b, ()) = (checkArg G t1 a && checkArg G t2 b) := by
  dsimp only [checkArgs]; rw [Bool.and_true]

public theorem lookupV_append_drop {V : Ty → Type} :
    (vsLocal vsRest : List ((t : Ty) × V t)) → (t : Ty) → (idx : Nat) →
    vsLocal.length ≤ idx →
    lookupV (vsLocal ++ vsRest) t idx = lookupV vsRest t (idx - vsLocal.length)
  | [], _, _, _, _ => rfl
  | _ :: vsLocal, _, _, 0, hi => by simp at hi
  | _ :: vsLocal, vsRest, t, idx + 1, hi => by
    have h1 : idx + 1 - (vsLocal.length + 1) = idx - vsLocal.length := by omega
    rw [List.length_cons, h1]
    exact lookupV_append_drop vsLocal vsRest t idx (Nat.le_of_succ_le_succ hi)

public theorem listGet?_append_drop {α : Type} :
    (GLocal GRest : List α) → (idx : Nat) → GLocal.length ≤ idx →
    listGet? (GLocal ++ GRest) idx = listGet? GRest (idx - GLocal.length)
  | [], _, _, _ => rfl
  | _ :: _, _, 0, hi => by simp at hi
  | _ :: GLocal, GRest, idx + 1, hi => by
    have h1 : idx + 1 - (GLocal.length + 1) = idx - GLocal.length := by omega
    rw [List.length_cons, h1]
    exact listGet?_append_drop GLocal GRest idx (Nat.le_of_succ_le_succ hi)


/-! ## WF of Wide Store Chain & Wrapper (`mkStoreChain`, `mkWideBody`, `mkWideWrapper`) -/

public theorem wfCheck_tArgShift (GLocal GOuter : List Ty) {t : Ty} (a : Arg K t) :
    checkArg (GLocal ++ GOuter) t (tArgShift GLocal.length a) = checkArg GOuter t a := by
  simpa [tArgShift] using checkArg_shiftArgAbove [] GLocal GOuter t a

public theorem wfCheck_mkStoreChainGoRest {rs : List Ty} (fill64 : BitVec 64)
    (stepK : Nat) (DOuter : List (List Ty)) :
    (remStores m curIDepth : Nat) → (GLocal : List Ty) →
    1 ≤ m →
    listGet? GLocal (m - 1) = some i64 →
    listGet? GLocal curIDepth = some i64 →
    (mkStoreChainGoRest (rs := rs) fill64 stepK m remStores curIDepth).wfCheck
      GLocal ([i64] :: DOuter) = true
  | 0, m, curIDepth, GLocal, _, _, hi => by
    dsimp only [mkStoreChainGoRest, op2]
    rw [wfCheck_let_eq]; dsimp only [op2]
    rw [checkArgs_pair_eq, Bool.and_eq_true, Bool.and_eq_true]
    have hci : checkArg GLocal i64 (.var curIDepth) = true := by
      dsimp only [checkArg]; rw [hi]; rfl
    refine ⟨⟨hci, rfl⟩, ?_⟩
    rw [wfCheck_jump_eq]; dsimp only [pushTypes, checkArgs, checkArg, listGet?]
    rw [Bool.and_eq_true, Bool.and_true]; exact ⟨rfl, rfl⟩
  | r + 1, m, curIDepth, GLocal, hm, hp, hi => by
    dsimp only [mkStoreChainGoRest, op2]
    rw [wfCheck_let_eq]; dsimp only [op2]
    rw [checkArgs_pair_eq, Bool.and_eq_true, Bool.and_eq_true]
    have hcp : checkArg GLocal i64 (.var (m - 1)) = true := by
      dsimp only [checkArg]; rw [hp]; rfl
    refine ⟨⟨hcp, rfl⟩, ?_⟩
    rw [wfCheck_store_eq, Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨rfl, by dsimp only [checkArg, pushTypes, listGet?]; rfl⟩, ?_⟩
    have hm1 : 1 ≤ m + 1 := by omega
    have hp1 : listGet? (pushTypes [i64] GLocal) ((m + 1) - 1) = some i64 := by
      have hm_eq : (m + 1) - 1 = (m - 1) + 1 := by omega
      rw [pushTypes_cons_eq, pushTypes_nil_eq, hm_eq]
      exact hp
    have hi1 : listGet? (pushTypes [i64] GLocal) (curIDepth + 1) = some i64 := by
      rw [pushTypes_cons_eq, pushTypes_nil_eq]
      exact hi
    exact wfCheck_mkStoreChainGoRest fill64 stepK DOuter r (m + 1) (curIDepth + 1)
      (i64 :: GLocal) hm1 hp1 hi1

public theorem wfCheck_mkStoreChain {rs : List Ty} (fill64 : BitVec 64)
    (stepK unrollN iDepth : Nat) (DOuter : List (List Ty)) (GLocal : List Ty)
    (hunroll : 0 < unrollN)
    (hp : listGet? GLocal 0 = some i64) (hi : listGet? GLocal iDepth = some i64) :
    (mkStoreChain (rs := rs) fill64 stepK unrollN iDepth).wfCheck
      GLocal ([i64] :: DOuter) = true := by
  cases unrollN with
  | zero => omega
  | succ n =>
    cases n with
    | zero =>
      rw [Nat.zero_add]; dsimp only [mkStoreChain]
      rw [wfCheck_store_eq, Bool.and_eq_true, Bool.and_eq_true]
      refine ⟨⟨rfl, by dsimp only [checkArg]; rw [hp]; rfl⟩, ?_⟩
      rw [wfCheck_let_eq]; dsimp only [op2]
      rw [checkArgs_pair_eq, Bool.and_eq_true, Bool.and_eq_true]
      refine ⟨⟨by dsimp only [checkArg]; rw [hi]; rfl, rfl⟩, ?_⟩
      rw [wfCheck_jump_eq]; dsimp only [pushTypes, checkArgs, checkArg, listGet?]
      rw [Bool.and_eq_true, Bool.and_true]; exact ⟨rfl, rfl⟩
    | succ r =>
      dsimp only [mkStoreChain]
      rw [wfCheck_store_eq, Bool.and_eq_true, Bool.and_eq_true]
      refine ⟨⟨rfl, by dsimp only [checkArg]; rw [hp]; rfl⟩, ?_⟩
      exact wfCheck_mkStoreChainGoRest fill64 stepK DOuter (r + 1) 1 iDepth GLocal
        (Nat.le_refl _) hp hi

public theorem wfCheck_mkWideBody {rs : List Ty} {GOuter : List Ty} {DOuter : List (List Ty)}
    {spec : FillSpec} {unrollN : Nat} (hunroll : 0 < unrollN)
    (hBound : checkArg GOuter i64 spec.bound = true)
    (hBase : checkArg GOuter i64 spec.base = true)
    (hOff : spec.off?.all (checkArg GOuter i64) = true) :
    (mkWideBody (rs := rs) spec unrollN).wfCheck
      (pushTypes [i64] GOuter) ([i64] :: [i64] :: DOuter) = true := by
  dsimp only [mkWideBody]
  rw [wfCheck_let_eq]; dsimp only [op2]
  rw [checkArgs_pair_eq, Bool.and_eq_true, Bool.and_eq_true]
  have hbnd : checkArg (i64 :: GOuter) i64 (tArgShift [i64].length spec.bound) = true := by
    change checkArg ([i64] ++ GOuter) i64 (tArgShift [i64].length spec.bound) = true
    rw [wfCheck_tArgShift [i64] GOuter spec.bound]; exact hBound
  refine ⟨⟨hbnd, by dsimp only [checkArg, pushTypes, listGet?]; rfl⟩, ?_⟩
  rw [wfCheck_let_eq]; dsimp only [op2]
  rw [checkArgs_pair_eq, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨by dsimp only [checkArg, pushTypes, listGet?]; rfl, rfl⟩, ?_⟩
  rw [wfCheck_jnz_eq, Bool.and_eq_true, Bool.and_eq_true]
  have hjFalse : (TFlat.jump (rs := rs) (ts := [i64]) 1 (Arg.var 2, ())).wfCheck
      ([.bool, i64, i64] ++ GOuter) ([i64] :: [i64] :: DOuter) = true := by
    rw [wfCheck_jump_eq]; dsimp only [listGet?, checkArgs, checkArg]
    rw [Bool.and_eq_true, Bool.and_true]; exact ⟨rfl, rfl⟩
  refine ⟨⟨by dsimp only [checkArg, pushTypes, listGet?]; rfl, ?_⟩, hjFalse⟩
  have hBaseAt : ∀ d idxVar GPre, GPre.length = d → 1 ≤ d →
      checkArg (GPre ++ GOuter) i64 idxVar = true →
      listGet? (GPre ++ GOuter) (d - 1) = some i64 →
      (TFlat.let_ (op2 (.add i64) (tArgShift d spec.base) idxVar)
        (mkStoreChain (rs := rs) spec.fill64
          (unrollN * (8 >>> spec.shift)) unrollN d)).wfCheck
        (GPre ++ GOuter) ([i64] :: [i64] :: DOuter) = true := by
    intro d idxVar GPre hd hd_pos hidx hiPrev
    subst hd
    rw [wfCheck_let_eq]; dsimp only [op2]
    rw [checkArgs_pair_eq, Bool.and_eq_true, Bool.and_eq_true]
    have hbase' : checkArg (GPre ++ GOuter) i64 (tArgShift GPre.length spec.base) = true := by
      rw [wfCheck_tArgShift GPre GOuter spec.base]; exact hBase
    refine ⟨⟨hbase', hidx⟩, ?_⟩
    have hp0 : listGet? (pushTypes [i64] (GPre ++ GOuter)) 0 = some i64 := rfl
    have hi0 : listGet? (pushTypes [i64] (GPre ++ GOuter)) GPre.length = some i64 := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : GPre.length ≠ 0)
      rw [hk, Nat.succ_sub_one] at hiPrev
      rw [hk, pushTypes_cons_eq, pushTypes_nil_eq]
      exact hiPrev
    exact wfCheck_mkStoreChain spec.fill64 _ unrollN GPre.length _ (i64 :: GPre ++ GOuter)
      hunroll hp0 hi0
  have hShiftAt : ∀ d idxVar GPre, GPre.length = d → 1 ≤ d →
      checkArg (GPre ++ GOuter) i64 idxVar = true →
      listGet? (GPre ++ GOuter) (d - 1) = some i64 →
      (if (spec.shift == 0) = true then
        TFlat.let_ (op2 (.add i64) (tArgShift d spec.base) idxVar)
          (mkStoreChain (rs := rs) spec.fill64
            (unrollN * (8 >>> spec.shift)) unrollN d)
       else
        TFlat.let_ (op2 (.shl i64) idxVar (.imm (BitVec.ofNat 64 spec.shift)))
          (TFlat.let_ (op2 (.add i64) (tArgShift (d + 1) spec.base) (.var 0))
            (mkStoreChain (rs := rs) spec.fill64
              (unrollN * (8 >>> spec.shift)) unrollN (d + 1)))).wfCheck
        (GPre ++ GOuter) ([i64] :: [i64] :: DOuter) = true := by
    intro d idxVar GPre hd hd_pos hidx hiPrev
    split
    · exact hBaseAt d idxVar GPre hd hd_pos hidx hiPrev
    · rw [wfCheck_let_eq]; dsimp only [op2]
      rw [checkArgs_pair_eq, Bool.and_eq_true, Bool.and_eq_true]
      refine ⟨⟨hidx, rfl⟩, ?_⟩
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
      have hlen1 : (i64 :: GPre).length = d + 1 := by simp [hd]
      have h0 : checkArg ((i64 :: GPre) ++ GOuter) i64 (.var 0) = true := by
        dsimp only [checkArg, listGet?]; rfl
      have hi1 : listGet? ((i64 :: GPre) ++ GOuter) ((d + 1) - 1) = some i64 := by
        rw [hk, Nat.succ_sub_one] at hiPrev
        rw [hk, Nat.add_sub_cancel]
        exact hiPrev
      exact hBaseAt (d + 1) (.var 0) (i64 :: GPre) hlen1 (by omega) h0 hi1
  cases hoff : spec.off? with
  | none =>
    exact hShiftAt 3 (.var 2) [.bool, i64, i64] rfl (by omega)
      (by dsimp only [checkArg, listGet?]; rfl) rfl
  | some off =>
    rw [wfCheck_let_eq]; dsimp only [op2]
    rw [checkArgs_pair_eq, Bool.and_eq_true, Bool.and_eq_true]
    have hvar2 : checkArg ([.bool, i64, i64] ++ GOuter) i64 (.var 2) = true := by
      dsimp only [checkArg, listGet?]; rfl
    have hoff' : checkArg ([.bool, i64, i64] ++ GOuter) i64 (tArgShift 3 off) = true := by
      have h3 : ([.bool, i64, i64] : List Ty).length = 3 := rfl
      rw [← h3, wfCheck_tArgShift]
      simpa [hoff] using hOff
    refine ⟨⟨hvar2, hoff'⟩, ?_⟩
    exact hShiftAt 4 (.var 0) [i64, .bool, i64, i64] rfl (by omega)
      (by dsimp only [checkArg, listGet?]; rfl) rfl

public theorem wfCheck_mkWideWrapper {rs : List Ty} {GOuter : List Ty} {DOuter : List (List Ty)}
    {spec : FillSpec} {unrollN : Nat} {initArg : Arg K i64} (hunroll : 0 < unrollN)
    (hInit : checkArg GOuter i64 initArg = true)
    (hBound : checkArg GOuter i64 spec.bound = true)
    (hBase : checkArg GOuter i64 spec.base = true)
    (hOff : spec.off?.all (checkArg GOuter i64) = true) :
    (mkWideWrapper (rs := rs) spec unrollN initArg).wfCheck
      GOuter ([i64] :: DOuter) = true := by
  dsimp only [mkWideWrapper]
  rw [wfCheck_group_eq, wfCheckB_cons_eq, wfCheckB_nil_eq, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨wfCheck_mkWideBody hunroll hBound hBase hOff, rfl⟩, ?_⟩
  rw [wfCheck_let_eq]; dsimp only [op2]
  rw [checkArgs_pair_eq, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨hInit, hBound⟩, ?_⟩
  rw [wfCheck_jnz_eq, Bool.and_eq_true, Bool.and_eq_true]
  have hshiftInit : checkArg (pushTypes [.bool] GOuter) i64 (tArgShift 1 initArg) = true := by
    rw [pushTypes_cons_eq, pushTypes_nil_eq]
    change checkArg ([Ty.bool] ++ GOuter) i64
      (tArgShift ([Ty.bool] : List Ty).length initArg) = true
    rw [wfCheck_tArgShift]
    exact hInit
  have hj0 : (TFlat.jump (rs := rs) (ts := [i64]) 0 (tArgShift 1 initArg, ())).wfCheck
      (pushTypes [.bool] GOuter) (pushTypes [[i64]] ([i64] :: DOuter)) = true := by
    rw [wfCheck_jump_eq]; dsimp only [pushTypes, listGet?, checkArgs]
    rw [Bool.and_eq_true, Bool.and_true]
    exact ⟨rfl, by rw [pushTypes_cons_eq, pushTypes_nil_eq] at hshiftInit; exact hshiftInit⟩
  have hj1 : (TFlat.jump (rs := rs) (ts := [i64]) 1 (tArgShift 1 initArg, ())).wfCheck
      (pushTypes [.bool] GOuter) (pushTypes [[i64]] ([i64] :: DOuter)) = true := by
    rw [wfCheck_jump_eq]; dsimp only [pushTypes, listGet?, checkArgs]
    rw [Bool.and_eq_true, Bool.and_true]
    exact ⟨rfl, by rw [pushTypes_cons_eq, pushTypes_nil_eq] at hshiftInit; exact hshiftInit⟩
  exact ⟨⟨by dsimp only [pushTypes, checkArg, listGet?]; rfl, hj0⟩, hj1⟩


/-! ## Stack, Tuple & Store-Chain Semantic Helpers -/

public theorem listGet?_eq_getElem? {α : Type} (l : List α) (i : Nat) :
    listGet? l i = l[i]? := by
  induction l generalizing i with
  | nil => rfl
  | cons a xs ih =>
    cases i with
    | zero => rfl
    | succ j => rw [listGet?_cons_succ_eq, List.getElem?_cons_succ]; exact ih j

public theorem castTy_some_eq {f : Ty → Type} :
    {a b : Ty} → {v : f a} → {w : f b} →
    castTy a b v = some w → (⟨a, v⟩ : (t : Ty) × f t) = ⟨b, w⟩
  | .bool, .bool, _, _, h => by cases h; rfl
  | .bits m, .bits n, _, _, h => by
    dsimp only [castTy] at h
    by_cases hmn : m = n
    · subst hmn; rw [dite_eq_left rfl] at h; cases h; rfl
    · rw [dite_eq_right hmn] at h; cases h
  | .float f, .float g, _, _, h => by
    dsimp only [castTy] at h
    by_cases hfg : f = g
    · subst hfg; rw [dite_eq_left rfl] at h; cases h; rfl
    · rw [dite_eq_right hfg] at h; cases h
  | .pair a1 a2, .pair b1 b2, _, _, h => by
    dsimp only [castTy] at h
    cases h1 : tyDecEq a1 b1 with
    | isFalse _ => rw [h1] at h; cases h
    | isTrue ha =>
      cases h2 : tyDecEq a2 b2 with
      | isFalse _ => rw [h1, h2] at h; cases h
      | isTrue hb => subst ha; subst hb; rw [h1, h2] at h; cases h; rfl
  | .bool, .bits _, _, _, h | .bool, .float _, _, _, h | .bool, .pair _ _, _, _, h
  | .bits _, .bool, _, _, h | .bits _, .float _, _, _, h | .bits _, .pair _ _, _, _, h
  | .float _, .bool, _, _, h | .float _, .bits _, _, _, h | .float _, .pair _ _, _, _, h
  | .pair _ _, .bool, _, _, h | .pair _ _, .bits _, _, _, h | .pair _ _, .float _, _, _, h => by
    cases h

public theorem sigma_val_eq {t : Ty} {a b : Val t}
    (h : (⟨t, a⟩ : (t : Ty) × Val t) = ⟨t, b⟩) : a = b := by
  cases h; rfl

public theorem pushTup_eq_append {α : Type} {f : α → Type} {ts : List α}
    (xs : Tup f ts) (acc : List ((x : α) × f x)) :
    pushTup xs acc = pushTup xs [] ++ acc := by
  simpa [List.nil_append] using pushTup_append xs [] acc

public theorem pushTup_append_assoc {α : Type} {f : α → Type} {ts : List α}
    (xs : Tup f ts) (vs1 vs2 : List ((x : α) × f x)) :
    pushTup xs (vs1 ++ vs2) = pushTup xs vs1 ++ vs2 := by
  rw [pushTup_eq_append, pushTup_eq_append xs vs1, List.append_assoc]

public theorem pushTup_length {α : Type} {f : α → Type} :
    ∀ (ts : List α) (xs : Tup f ts) (acc : List ((x : α) × f x)),
      (pushTup xs acc).length = acc.length + ts.length
  | [], _, acc => by cases ‹Tup f []›; rfl
  | _ :: ts, (_, xs), acc => by
    rw [pushTup_cons_eq, pushTup_length ts xs, List.length_cons, List.length_cons]
    omega

public theorem toBytes_length (n : Nat) (z : Int) : (Int.toBytes n z).length = n := by
  induction n generalizing z with
  | zero => rfl
  | succ k ih => dsimp only [Int.toBytes]; rw [List.length_cons, ih]

public theorem length_flatten_replicate {α : Type} (k : Nat) (xs : List α) :
    (List.replicate k xs).flatten.length = k * xs.length := by
  induction k with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih, Nat.succ_mul, Nat.add_comm]

public theorem bv64_shl_add (a b : BitVec 64) (s : Nat) :
    (a + b) <<< s = (a <<< s) + (b <<< s) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, BitVec.toNat_add, Nat.shiftLeft_eq]

public theorem bv64_ofNat_shl (j s : Nat) :
    BitVec.ofNat 64 j <<< s = BitVec.ofNat 64 (j * 2 ^ s) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

public theorem wp_hlt_false {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    (h : wp Γ Q X Expr.hlt m) : False := h


public theorem runScalarMem_step {JLoop : Cont [i64]}
    {t_atom : Ty} {fillAtom : Val t_atom} {sh : Nat} {baseVal bndVal oVal : BitVec 64}
    (hShift : sh ≤ 3) (hBytesEq : t_atom.bytes = 2 ^ sh) (hBytesPos : 0 < t_atom.bytes)
    (hStep : ∀ (i' : BitVec 64) (m' : Mem 64),
      i'.toNat < bndVal.toNat → JLoop (i', ()) m' →
      storeOk m' t_atom (baseVal + ((i' + oVal) <<< sh)) ∧
      JLoop (i' + 1#64, ()) (storeMem m' t_atom (baseVal + ((i' + oVal) <<< sh)) fillAtom))
    (iVal : BitVec 64) (hi : iVal.toNat ≤ bndVal.toNat) (m : Mem 64) (hJ : JLoop (iVal, ()) m) :
    ∀ (k : Nat), k ≤ bndVal.toNat - iVal.toNat → k * t_atom.bytes ≤ 2 ^ 64 →
      let ptr0 := baseVal + ((iVal + oVal) <<< sh)
      let atomBytes :=
        Int.toBytes t_atom.bytes (BitVec.setWidth (8 * t_atom.bytes) (toBits t_atom fillAtom)).toInt
      (∀ (j : Nat), j < k → storeOk m t_atom (ptr0 + BitVec.ofNat 64 (t_atom.bytes * j))) ∧
      JLoop (iVal + BitVec.ofNat 64 k, ()) (m.storeBytes ptr0 (List.replicate k atomBytes).flatten)
  | 0, _, _ =>
    ⟨fun _ hj => by omega, by simpa [storeBytes_nil] using hJ⟩
  | k + 1, hk, hkBnd => by
    dsimp only
    let ptr0 := baseVal + ((iVal + oVal) <<< sh)
    let atomBytes :=
      Int.toBytes t_atom.bytes (BitVec.setWidth (8 * t_atom.bytes) (toBits t_atom fillAtom)).toInt
    have hk' : k ≤ bndVal.toNat - iVal.toNat := by omega
    have hkBnd' : k * t_atom.bytes ≤ 2 ^ 64 := by
      have : k * t_atom.bytes ≤ (k + 1) * t_atom.bytes := Nat.mul_le_mul_right _ (by omega)
      omega
    obtain ⟨hOkPrev, hJk⟩ :=
      runScalarMem_step hShift hBytesEq hBytesPos hStep iVal hi m hJ k hk' hkBnd'
    have hiK : (iVal + BitVec.ofNat 64 k).toNat < bndVal.toNat := by
      have hSum : iVal.toNat + k < bndVal.toNat := by omega
      have hLt64 : iVal.toNat + k < 2 ^ 64 := Nat.lt_trans hSum bndVal.isLt
      have hK64 : k < 2 ^ 64 := by omega
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hK64, Nat.mod_eq_of_lt hLt64]
      exact hSum
    obtain ⟨hOkCur, hJNext⟩ := hStep (iVal + BitVec.ofNat 64 k) _ hiK hJk
    have hAtomLen : atomBytes.length = t_atom.bytes := toBytes_length ..
    have hBsLen : (List.replicate k atomBytes).flatten.length = k * t_atom.bytes := by
      rw [length_flatten_replicate, hAtomLen]
    have hAllMapped : ∀ (j : Nat), j < (List.replicate k atomBytes).flatten.length →
        (Std.ExtHashMap.get? m (ptr0 + BitVec.ofNat 64 j)).isSome = true := by
      intro j hj
      rw [hBsLen] at hj
      have hq : j / t_atom.bytes < k := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
      have hr : j % t_atom.bytes < t_atom.bytes := Nat.mod_lt _ hBytesPos
      have hMem := (storeOk_iff_forall_mem m t_atom
        (ptr0 + BitVec.ofNat 64 (t_atom.bytes * (j / t_atom.bytes)))).mp
        (hOkPrev (j / t_atom.bytes) hq) (j % t_atom.bytes) hr
      have hSplit : t_atom.bytes * (j / t_atom.bytes) + j % t_atom.bytes = j :=
        Nat.div_add_mod j t_atom.bytes
      rwa [BitVec.add_assoc, ← BitVec.ofNat_add, hSplit] at hMem
    have hOkIff := storeOk_storeBytes_iff m ptr0 (List.replicate k atomBytes).flatten hAllMapped
    have hPtrEq : baseVal + (((iVal + BitVec.ofNat 64 k) + oVal) <<< sh) =
        ptr0 + BitVec.ofNat 64 (t_atom.bytes * k) := by
      have hAdd : (iVal + BitVec.ofNat 64 k) + oVal = (iVal + oVal) + BitVec.ofNat 64 k := by
        rw [BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 k) oVal, ← BitVec.add_assoc]
      rw [hAdd, bv64_shl_add, bv64_ofNat_shl, ← hBytesEq, Nat.mul_comm k t_atom.bytes]
      dsimp only [ptr0]; rw [BitVec.add_assoc]
    rw [hPtrEq] at hOkCur hJNext
    refine ⟨fun j hj => ?_, ?_⟩
    · by_cases hjLt : j < k
      · exact hOkPrev j hjLt
      · have hjEq : j = k := by omega
        subst hjEq
        exact (hOkIff t_atom (ptr0 + BitVec.ofNat 64 (t_atom.bytes * j))).mp hOkCur
    · rw [storeMem_eq_storeBytes] at hJNext
      have hOffset : ptr0 + BitVec.ofNat 64 (t_atom.bytes * k) =
          ptr0 + BitVec.ofNat 64 (List.replicate k atomBytes).flatten.length := by
        rw [hBsLen, Nat.mul_comm]
      have hLenBound :
          (List.replicate k atomBytes).flatten.length + atomBytes.length ≤ 2 ^ 64 := by
        rw [hBsLen, hAtomLen]; rwa [Nat.add_mul, Nat.one_mul] at hkBnd
      rw [hOffset, storeBytes_append _ _ _ _ hLenBound] at hJNext
      have hRep : (List.replicate (k + 1) atomBytes).flatten =
          (List.replicate k atomBytes).flatten ++ atomBytes := by
        rw [list_replicate_add k 1 atomBytes, List.flatten_append]; simp
      have hStepI : (iVal + BitVec.ofNat 64 k) + 1#64 = iVal + BitVec.ofNat 64 (k + 1) := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      rwa [hRep, ← hStepI]

public theorem bv64_setWidth_toBits (v : BitVec 64) :
    (BitVec.setWidth (8 * (Ty.bits 64).bytes) (toBits (Ty.bits 64) v)).toInt = v.toInt := rfl

public theorem storeMem_i64_prepend_bytes (mem : Mem 64) (p fill64 : BitVec 64) (k : Nat)
    (hk : 8 * (k + 1) ≤ 2 ^ 64) :
    (storeMem mem i64 p fill64).storeBytes (p + BitVec.ofNat 64 8)
      (List.replicate k (Int.toBytes 8 fill64.toInt)).flatten =
    mem.storeBytes p (List.replicate (k + 1) (Int.toBytes 8 fill64.toInt)).flatten := by
  have hi64B : i64.bytes = 8 := rfl
  have hWLen : (Int.toBytes 8 fill64.toInt).length = 8 := toBytes_length ..
  have hRLen : (List.replicate k (Int.toBytes 8 fill64.toInt)).flatten.length = 8 * k := by
    rw [length_flatten_replicate, hWLen, Nat.mul_comm]
  have hLenBound : (Int.toBytes 8 fill64.toInt).length +
      (List.replicate k (Int.toBytes 8 fill64.toInt)).flatten.length ≤ 2 ^ 64 := by
    rw [hWLen, hRLen]; omega
  have hp8 : p + BitVec.ofNat 64 8 =
      p + BitVec.ofNat 64 (Int.toBytes 8 fill64.toInt).length := by rw [hWLen]
  rw [storeMem_eq_storeBytes, bv64_setWidth_toBits, hi64B, hp8,
    storeBytes_append _ _ _ _ hLenBound, List.replicate_succ, List.flatten_cons]

public theorem mkStoreChainGoRest_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {fill64 : BitVec 64} {stepK : Nat} {JWide : Cont [i64]} {ptr0 iVal : BitVec 64} :
    ∀ (remStores m curIDepth : Nat) (vs : List ((t : Ty) × Val t))
      (ls : List ((ts : List Ty) × Cont ts)) (mem : Mem 64),
      1 ≤ m → 8 * (remStores + 1) ≤ 2 ^ 64 →
      lookupV vs i64 (m - 1) = some ptr0 → lookupV vs i64 curIDepth = some iVal →
      lookupL ls [i64] 0 = some JWide →
      (∀ (r : Nat), r < remStores → storeOk mem i64 (ptr0 + BitVec.ofNat 64 (8 * (m + r)))) →
      JWide (iVal + BitVec.ofNat 64 stepK, ())
        (mem.storeBytes (ptr0 + BitVec.ofNat 64 (8 * m))
          (List.replicate remStores (Int.toBytes 8 fill64.toInt)).flatten) →
      wp Γ Q X (denote Val Cont (mkStoreChainGoRest fill64 stepK m remStores curIDepth) vs ls)
        mem
  | 0, m, curIDepth, vs, ls, mem, _, _, _, hI, hL, _, hPost => by
    dsimp only [mkStoreChainGoRest, op2]
    rw [denote_let_eq, denoteArgs_pair_eq]
    have hVar : denoteArg vs (.var curIDepth : Arg K i64) = some (.var iVal) := by
      dsimp only [denoteArg]; rw [hI]
    have hImm : denoteArg vs (.imm (BitVec.ofNat 64 stepK) : Arg K i64) =
        some (.imm (BitVec.ofNat 64 stepK)) := rfl
    rw [hVar, hImm]
    rw [wp_let]; dsimp only [Op.wp, vals]; rw [OpCode.wp_add]
    dsimp only [lift2, vals, Arg.val, pushTup, i64, Ty.hasFloat]
    rw [denote_jump_eq, denoteArgs_singleton_eq]
    have hVar0 : denoteArg (⟨i64, iVal + BitVec.ofNat 64 stepK⟩ :: vs) (.var 0 : Arg K i64) =
        some (.var (iVal + BitVec.ofNat 64 stepK)) := by
      dsimp only [denoteArg, lookupV, listGet?, castTy]; rfl
    rw [hL, hVar0]
    rw [wp_jump]; dsimp only [vals, Arg.val]
    simpa [storeBytes_nil] using hPost
  | r + 1, m, curIDepth, vs, ls, mem, hmGe, hBnd, hPtr, hI, hL, hOk, hPost => by
    dsimp only [mkStoreChainGoRest, op2]
    rw [denote_let_eq, denoteArgs_pair_eq]
    have hImm : denoteArg vs (.imm (BitVec.ofNat 64 (8 * m)) : Arg K i64) =
        some (.imm (BitVec.ofNat 64 (8 * m))) := rfl
    have hVarM : denoteArg vs (.var (m - 1) : Arg K i64) = some (.var ptr0) := by
      dsimp only [denoteArg]; rw [hPtr]
    rw [hVarM, hImm]
    rw [wp_let]; dsimp only [Op.wp, vals]; rw [OpCode.wp_add]
    dsimp only [lift2, vals, Arg.val, pushTup, i64, Ty.hasFloat]
    rw [denote_store_eq]
    have hVar0 : denoteArg (⟨i64, ptr0 + BitVec.ofNat 64 (8 * m)⟩ :: vs) (.var 0 : Arg K i64) =
        some (.var (ptr0 + BitVec.ofNat 64 (8 * m))) := by
      dsimp only [denoteArg, lookupV, listGet?, castTy]; rfl
    have hImmF : denoteArg (⟨i64, ptr0 + BitVec.ofNat 64 (8 * m)⟩ :: vs)
        (.imm fill64 : Arg K i64) = some (.imm fill64) := rfl
    rw [hImmF, hVar0]
    rw [wp_store]; dsimp only [Arg.val]
    have hOk0 : storeOk mem i64 (ptr0 + BitVec.ofNat 64 (8 * m)) := by
      simpa using hOk 0 (Nat.zero_lt_succ r)
    refine ⟨hOk0, ?_⟩
    let mem₁ := storeMem mem i64 (ptr0 + BitVec.ofNat 64 (8 * m)) fill64
    have hPtr' : lookupV (⟨i64, ptr0 + BitVec.ofNat 64 (8 * m)⟩ :: vs) i64 ((m + 1) - 1) =
        some ptr0 := by
      have hmSub : m = (m - 1) + 1 := by omega
      change lookupV (⟨i64, ptr0 + BitVec.ofNat 64 (8 * m)⟩ :: vs) i64 m = some ptr0
      rw [hmSub]; exact hPtr
    have hOk' : ∀ (r' : Nat), r' < r →
        storeOk mem₁ i64 (ptr0 + BitVec.ofNat 64 (8 * (m + 1 + r'))) := by
      intro r' hr'
      rw [storeOk_storeMem_iff mem i64 (ptr0 + BitVec.ofNat 64 (8 * m)) fill64 hOk0]
      have hR : m + 1 + r' = m + (r' + 1) := by omega
      rw [hR]; exact hOk (r' + 1) (Nat.succ_lt_succ hr')
    have hPost' : JWide (iVal + BitVec.ofNat 64 stepK, ())
        (mem₁.storeBytes (ptr0 + BitVec.ofNat 64 (8 * (m + 1)))
          (List.replicate r (Int.toBytes 8 fill64.toInt)).flatten) := by
      have hPtrNext : ptr0 + BitVec.ofNat 64 (8 * (m + 1)) =
          (ptr0 + BitVec.ofNat 64 (8 * m)) + BitVec.ofNat 64 8 := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add, Nat.mul_one]
      rw [hPtrNext]
      dsimp only [mem₁]
      rwa [storeMem_i64_prepend_bytes mem (ptr0 + BitVec.ofNat 64 (8 * m)) fill64 r (by omega)]
    exact mkStoreChainGoRest_wp r (m + 1) (curIDepth + 1) _ ls mem₁
      (by omega) (by omega) hPtr' hI hL hOk' hPost'

public theorem mkStoreChain_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {fill64 : BitVec 64} {stepK unrollN iDepth : Nat} {JWide : Cont [i64]}
    {ptr0 iVal : BitVec 64} {vs : List ((t : Ty) × Val t)}
    {ls : List ((ts : List Ty) × Cont ts)} {mem : Mem 64}
    (hunroll : 1 ≤ unrollN) (hBnd : 8 * unrollN ≤ 2 ^ 64)
    (hPtr : lookupV vs i64 0 = some ptr0) (hI : lookupV vs i64 iDepth = some iVal)
    (hL : lookupL ls [i64] 0 = some JWide)
    (hOk : ∀ (r : Nat), r < unrollN → storeOk mem i64 (ptr0 + BitVec.ofNat 64 (8 * r)))
    (hPost : JWide (iVal + BitVec.ofNat 64 stepK, ())
      (mem.storeBytes ptr0 (List.replicate unrollN (Int.toBytes 8 fill64.toInt)).flatten)) :
    wp Γ Q X (denote Val Cont (mkStoreChain fill64 stepK unrollN iDepth) vs ls) mem := by
  cases unrollN with
  | zero => omega
  | succ n =>
    cases n with
    | zero =>
      rw [Nat.zero_add]; dsimp only [mkStoreChain]
      rw [denote_store_eq]
      have hVar0 : denoteArg vs (.var 0 : Arg K i64) = some (.var ptr0) := by
        dsimp only [denoteArg]; rw [hPtr]
      have hImmF : denoteArg vs (.imm fill64 : Arg K i64) = some (.imm fill64) := rfl
      rw [hImmF, hVar0]
      rw [wp_store]; dsimp only [Arg.val]
      have hOk0 : storeOk mem i64 ptr0 := by simpa using hOk 0 (by omega)
      refine ⟨hOk0, ?_⟩
      dsimp only [op2]
      rw [denote_let_eq, denoteArgs_pair_eq]
      have hVarI : denoteArg vs (.var iDepth : Arg K i64) = some (.var iVal) := by
        dsimp only [denoteArg]; rw [hI]
      have hImmS : denoteArg vs (.imm (BitVec.ofNat 64 stepK) : Arg K i64) =
          some (.imm (BitVec.ofNat 64 stepK)) := rfl
      rw [hVarI, hImmS]
      rw [wp_let]; dsimp only [Op.wp, vals]; rw [OpCode.wp_add]
      dsimp only [lift2, vals, Arg.val, pushTup, i64, Ty.hasFloat]
      rw [denote_jump_eq, denoteArgs_singleton_eq]
      have hVarNew : denoteArg (⟨i64, iVal + BitVec.ofNat 64 stepK⟩ :: vs) (.var 0 : Arg K i64) =
          some (.var (iVal + BitVec.ofNat 64 stepK)) := by
        dsimp only [denoteArg, lookupV, listGet?, castTy]; rfl
      rw [hL, hVarNew]
      rw [wp_jump]; dsimp only [vals, Arg.val]
      have hi64B : i64.bytes = 8 := rfl
      rw [storeMem_eq_storeBytes, bv64_setWidth_toBits, hi64B]
      simpa using hPost
    | succ r =>
      dsimp only [mkStoreChain]
      rw [denote_store_eq]
      have hVar0 : denoteArg vs (.var 0 : Arg K i64) = some (.var ptr0) := by
        dsimp only [denoteArg]; rw [hPtr]
      have hImmF : denoteArg vs (.imm fill64 : Arg K i64) = some (.imm fill64) := rfl
      rw [hImmF, hVar0]
      rw [wp_store]; dsimp only [Arg.val]
      have hOk0 : storeOk mem i64 ptr0 := by simpa using hOk 0 (by omega)
      refine ⟨hOk0, ?_⟩
      let mem₁ := storeMem mem i64 ptr0 fill64
      have hOkRest : ∀ (r' : Nat), r' < r + 1 →
          storeOk mem₁ i64 (ptr0 + BitVec.ofNat 64 (8 * (1 + r'))) := by
        intro r' hr'
        rw [storeOk_storeMem_iff mem i64 ptr0 fill64 hOk0]
        exact hOk (1 + r') (by omega)
      have hPostRest : JWide (iVal + BitVec.ofNat 64 stepK, ())
          (mem₁.storeBytes (ptr0 + BitVec.ofNat 64 (8 * 1))
            (List.replicate (r + 1) (Int.toBytes 8 fill64.toInt)).flatten) := by
        rw [Nat.mul_one]
        dsimp only [mem₁]
        rwa [storeMem_i64_prepend_bytes mem ptr0 fill64 (r + 1) (by omega)]
      exact mkStoreChainGoRest_wp (r + 1) 1 iDepth vs ls mem₁
        (by omega) (by omega) hPtr hI hL hOkRest hPostRest

public theorem wideBody_withBase_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {spec : FillSpec} {unrollN : Nat} {JWide : Cont [i64]} {idxVar : Arg K i64}
    {vsOuter vsLocal : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    {baseA idxA : Arg Val i64} {iVal oVal : BitVec 64} {mem : Mem 64}
    (hunroll : 1 ≤ unrollN) (hBnd : unrollN ≤ 64)
    (hLen : vsLocal.length ≥ 1)
    (hBase : denoteArg vsOuter spec.base = some baseA)
    (hIdx : denoteArg (vsLocal ++ vsOuter) idxVar = some idxA)
    (hIdxVal : idxA.val = (iVal + oVal) <<< spec.shift)
    (hI : lookupV (vsLocal ++ vsOuter) i64 (vsLocal.length - 1) = some iVal)
    (hOk : ∀ (r : Nat), r < unrollN →
      storeOk mem i64 ((baseA.val + ((iVal + oVal) <<< spec.shift)) + BitVec.ofNat 64 (8 * r)))
    (hPost : JWide (iVal + BitVec.ofNat 64 (unrollN * (8 >>> spec.shift)), ())
      (mem.storeBytes (baseA.val + ((iVal + oVal) <<< spec.shift))
        (List.replicate unrollN (Int.toBytes 8 spec.fill64.toInt)).flatten)) :
    wp Γ Q X (denote Val Cont
      (TFlat.let_ (op2 (OpCode.add i64) (tArgShift vsLocal.length spec.base) idxVar)
        (mkStoreChain spec.fill64 (unrollN * (8 >>> spec.shift)) unrollN vsLocal.length))
      (vsLocal ++ vsOuter) (⟨[i64], JWide⟩ :: ls)) mem := by
  dsimp only [op2]
  rw [denote_let_eq, denoteArgs_pair_eq]
  have hBaseSh : denoteArg (vsLocal ++ vsOuter) (tArgShift vsLocal.length spec.base) =
      some baseA := by
    have hSh := denoteArg_shiftArgAbove (vsPre := []) vsLocal vsOuter spec.base
    simpa [tArgShift] using hSh.trans hBase
  rw [hBaseSh, hIdx]
  rw [wp_let]; dsimp only [Op.wp, vals]; rw [OpCode.wp_add]
  dsimp only [lift2, pushTup, i64, Ty.hasFloat]; rw [hIdxVal]
  let ptr0 := baseA.val + ((iVal + oVal) <<< spec.shift)
  have hPtr0 : lookupV (⟨i64, ptr0⟩ :: (vsLocal ++ vsOuter)) i64 0 = some ptr0 := by
    dsimp only [lookupV, listGet?, castTy]; rfl
  have hISucc : lookupV (⟨i64, ptr0⟩ :: (vsLocal ++ vsOuter)) i64 vsLocal.length = some iVal := by
    have : vsLocal.length = (vsLocal.length - 1) + 1 := by omega
    rw [this]; exact hI
  have hL0 : lookupL (⟨[i64], JWide⟩ :: ls) [i64] 0 = some JWide := by
    dsimp only [lookupL, listGet?]; exact castListTy_self [i64] JWide
  exact mkStoreChain_wp hunroll (by omega) hPtr0 hISucc hL0 hOk hPost


end ZeroPeel

end LeanQbe.T
