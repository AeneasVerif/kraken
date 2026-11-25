module

public import LeanQbe.T.Ops
public import LeanQbe.T.Module
public import LeanQbe.T.WPLemmas
public import LeanQbe.T.WfLemmas
public import LeanQbe.T.Logic.MemLemmas
public import Kraken.Bedrock2.Memory
import all Kraken.Separation

/-!
# Structured Bedrock2 in Typed PHOAS (`LeanQbe.T.Bedrock2.Phoas`)

A structured-control-flow formalization of Bedrock2 in the style of `LeanQbe.T`,
reusing `LeanQbe.T`'s exact `Ty`, `Val`, `Arg`, `Op` (`OpCode`), `Tup`, `Member`,
`Sym`, `i64`, `vals`, `loadVal`, `storeOk`, `storeMem`, `Mem 64`, `ArgRel`, `OpRel`,
and `Kraken.Bedrock2.Memory`'s `anybytes` / `split`:

1. **PHOAS AST** (`Cmd V rs`, `CmdB`, `FuncB as rs`, `FnB`, `ModuleB`): no `L` label
   parameter, no `jump`, no `group`; lexically scoped `stackalloc`, structured
   `seq` / `cond` / `while_`, typed return tuples `rs : List Ty`.
2. **Total-correctness `wp`** (`Cmd.wp`, `FuncB.wp`, `Cmd.wpUnbounded`, `Cmd.wpPure`):
   separation-split `stackalloc` and `interact` matching `Kraken.Bedrock2.Exec`,
   Knaster-Tarski `lfp` `while_` with `wp_conseq`, `wp_mono`, `wp_budget_mono`,
   `wp_while_unfold`, and well-founded measure induction `wp_while_measure`.
3. **Relational well-formedness** (`Cmd.Wf`, `FuncB.Wf`, `FnB.Wf`, `t_b2_wf_tac`).
4. **Acyclic modules** (`ModuleOkB`, `ModuleB.checkAcyclic`,
   `ModuleB.moduleOk_of_checkAcyclic`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Bedrock2

open LeanQbe.T
open Kraken.Bedrock2 (anybytes split)
open Std.ExtHashMap

/-! ## 1. Structured PHOAS Bedrock2 AST -/

/-- Structured Bedrock2 command with typed PHOAS binders `V` and return signature `rs`.
Strictly structured control flow: no label parameter `L`, no `jump`, no `group`. -/
inductive Cmd (V : Ty → Type) : List Ty → Type
  /-- Return a typed tuple of operands (`skip` is `ret ()` at `rs = []`). -/
  | ret {rs : List Ty} (vs : Tup (Arg V) rs) : Cmd V rs
  /-- Execute a pure/relational `LeanQbe.T.Op` and bind its result tuple. -/
  | let_ {rs ts : List Ty} (op : Op V ts) (k : Tup V ts → Cmd V rs) : Cmd V rs
  /-- Load a typed value from address `a` and bind it in `k`. -/
  | load {rs : List Ty} (t : Ty) (a : Arg V i64) (k : V t → Cmd V rs) : Cmd V rs
  /-- Store a typed value `v` to address `a`, then continue with `k`. -/
  | store {rs : List Ty} {t : Ty} (v : Arg V t) (a : Arg V i64) (k : Cmd V rs) : Cmd V rs
  /-- Call global function `f` with typed args, binding its result tuple in `k`. -/
  | call {rs : List Ty} (f : Sym) {as bs : List Ty} (args : Tup (Arg V) as)
      (k : Tup V bs → Cmd V rs) : Cmd V rs
  /-- Perform an external I/O interaction `action`, binding its results in `k`. -/
  | interact {rs : List Ty} (action : Sym) {as bs : List Ty} (args : Tup (Arg V) as)
      (k : Tup V bs → Cmd V rs) : Cmd V rs
  /-- Lexically scoped stack allocation of `nbytes` bytes at address `a : V i64`. -/
  | stackalloc {rs : List Ty} (nbytes : Nat) (body : V i64 → Cmd V rs) : Cmd V rs
  /-- Structured sequencing: run `c₁` returning `mid`, then pass results to `c₂`. -/
  | seq {rs mid : List Ty} (c₁ : Cmd V mid) (c₂ : Tup V mid → Cmd V rs) : Cmd V rs
  /-- Structured conditional branch on a boolean operand. -/
  | cond {rs : List Ty} (c : Arg V .bool) (t e : Cmd V rs) : Cmd V rs
  /-- Structured `while` loop with loop-carried state `st`, condition command `test`,
  loop body `body`, and post-loop continuation `k`. -/
  | while_ {rs st : List Ty} (init : Tup (Arg V) st)
      (test : Tup V st → Cmd V [.bool])
      (body : Tup V st → Cmd V st)
      (k : Tup V st → Cmd V rs) : Cmd V rs
  /-- Unreachable / undefined behaviour. -/
  | hlt {rs : List Ty} : Cmd V rs

/-- Alias matching `FuncB` / `CmdB` naming convention. -/
abbrev CmdB := Cmd

/-- A closed structured Bedrock2 function taking `as` and returning `rs`. -/
abbrev FuncB (as rs : List Ty) : Type 1 :=
  ∀ (V : Ty → Type), Tup V as → Cmd V rs

/-- A named typed structured Bedrock2 function. -/
structure FnB where
  name : Sym
  as : List Ty
  rs : List Ty
  body : FuncB as rs

/-- A structured Bedrock2 module: defined functions and external callees. -/
structure ModuleB where
  fns : List FnB
  externs : List Extern := []

/-! ### Smart constructors -/

/-- No-op command returning `()` at `rs = []`. -/
abbrev Cmd.skip {V : Ty → Type} : Cmd V [] := .ret ()

/-- Return a single operand. -/
abbrev Cmd.ret1 {V : Ty → Type} {t : Ty} (v : Arg V t) : Cmd V [t] := .ret (v, ())

/-- Bind a single-result `Op`. -/
abbrev Cmd.let1 {V : Ty → Type} {t : Ty} {rs : List Ty} (op : Op V [t])
    (k : V t → Cmd V rs) : Cmd V rs :=
  .let_ op fun (x, ()) => k x

/-- Bind a unary single-result `OpCode`. -/
abbrev Cmd.letOp1 {V : Ty → Type} {a t : Ty} {rs : List Ty} (c : OpCode [a] [t])
    (x : Arg V a) (k : V t → Cmd V rs) : Cmd V rs :=
  .let1 (op1 c x) k

/-- Bind a binary single-result `OpCode`. -/
abbrev Cmd.letOp2 {V : Ty → Type} {a b t : Ty} {rs : List Ty} (c : OpCode [a, b] [t])
    (x : Arg V a) (y : Arg V b) (k : V t → Cmd V rs) : Cmd V rs :=
  .let1 (op2 c x y) k

/-- Bind a ternary single-result `OpCode`. -/
abbrev Cmd.letOp3 {V : Ty → Type} {a b d t : Ty} {rs : List Ty} (c : OpCode [a, b, d] [t])
    (x : Arg V a) (y : Arg V b) (z : Arg V d) (k : V t → Cmd V rs) : Cmd V rs :=
  .let1 (op3 c x y z) k

/-- Sequence a unit-returning command `c₁ : Cmd V []` before `c₂`. -/
abbrev Cmd.seq0 {V : Ty → Type} {rs : List Ty} (c₁ : Cmd V []) (c₂ : Cmd V rs) : Cmd V rs :=
  .seq c₁ fun () => c₂

/-- Call a single-result function. -/
abbrev Cmd.call1 {V : Ty → Type} {as : List Ty} {b : Ty} {rs : List Ty} (f : Sym)
    (args : Tup (Arg V) as) (k : V b → Cmd V rs) : Cmd V rs :=
  .call f (as := as) (bs := [b]) args fun (r, ()) => k r

/-- Perform a single-result external interaction. -/
abbrev Cmd.interact1 {V : Ty → Type} {as : List Ty} {b : Ty} {rs : List Ty} (action : Sym)
    (args : Tup (Arg V) as) (k : V b → Cmd V rs) : Cmd V rs :=
  .interact action (as := as) (bs := [b]) args fun (r, ()) => k r

/-! ## 2. Total-Correctness Weakest Precondition (`Cmd.wp` / `FuncB.wp`) -/

/-- Typed external-interaction log item, recording given memory, action, typed
arguments, received memory, and typed return values. -/
structure LogItemB where
  as : List Ty
  bs : List Ty
  mGive : Mem 64
  action : Sym
  args : Tup Val as
  mReceive : Mem 64
  rets : Tup Val bs

/-- Trace of external I/O interactions (most recent first). -/
abbrev TraceB : Type := List LogItemB

/-- External I/O specification indexed by action signature `(as, bs)`. -/
abbrev ExtSpecB : Type :=
  TraceB → (mGive : Mem 64) → (action : Sym) → (as bs : List Ty) →
  (args : Tup Val as) → (post : Mem 64 → Tup Val bs → Prop) → Prop

/-- Well-behavedness conditions for an `ExtSpecB`, mirroring `Kraken.Bedrock2.ExtSpec.Ok`. -/
structure ExtSpecB.Ok (ext : ExtSpecB) : Prop where
  mGive_unique : ∀ t m mGive1 mKeep1 mGive2 mKeep2 a as bs args post1 post2,
    split m mKeep1 mGive1 → split m mKeep2 mGive2 →
    ext t mGive1 a as bs args post1 → ext t mGive2 a as bs args post2 →
    mGive1 = mGive2
  weaken : ∀ t mGive a as bs args (post1 post2 : Mem 64 → Tup Val bs → Prop),
    (∀ mReceive rets, post1 mReceive rets → post2 mReceive rets) →
    ext t mGive a as bs args post1 → ext t mGive a as bs args post2
  intersect : ∀ t mGive a as bs args (post1 post2 : Mem 64 → Tup Val bs → Prop),
    ext t mGive a as bs args post1 → ext t mGive a as bs args post2 →
    ext t mGive a as bs args (fun mReceive rets => post1 mReceive rets ∧ post2 mReceive rets)

/-- Postcondition for a command returning `rs`: return tuple, trace, and memory. -/
abbrev PostB (rs : List Ty) : Type := Tup Val rs → TraceB → Mem 64 → Prop

/-- A Bedrock2 function contract: stack budget, args, trace, memory, postcondition. -/
abbrev SpecB (as rs : List Ty) : Type :=
  Nat → Tup Val as → TraceB → Mem 64 → PostB rs → Prop

/-- Contract environment for global function symbols, indexed by signature `(as, rs)`. -/
abbrev EnvB : Type := Sym → (as rs : List Ty) → SpecB as rs

/-- Total-correctness weakest precondition of `c : Cmd Val rs` under external spec `ext`,
callee environment `Γ`, stack budget `B`, postcondition `Q`, trace `t`, and memory `m`.
`while_` uses Knaster-Tarski least-fixpoint quantification (`∀ I, Closed → I`), matching
`LeanQbe.T.WP`'s `.group` semantics. -/
def Cmd.wp (ext : ExtSpecB) (Γ : EnvB) :
    {rs : List Ty} → Nat → PostB rs → Cmd Val rs → TraceB → Mem 64 → Prop
  | _, _, Q, .ret vs, t, m => Q (vals vs) t m
  | _, B, Q, .let_ op k, t, m => op.wp (fun r => Cmd.wp ext Γ B Q (k r) t m)
  | _, B, Q, .load ty a k, t, m =>
      ∃ v, loadVal m ty a.val = some v ∧ Cmd.wp ext Γ B Q (k v) t m
  | _, B, Q, .store (t := ty) v a k, t, m =>
      storeOk m ty a.val ∧ Cmd.wp ext Γ B Q k t (storeMem m ty a.val v.val)
  | _, B, Q, .call f (as := as) (bs := bs) args k, t, m =>
      ∃ (P : PostB bs), Γ f as bs B (vals args) t m P ∧
        ∀ r t' m', P r t' m' → Cmd.wp ext Γ B Q (k r) t' m'
  | _, B, Q, .interact action (as := as) (bs := bs) args k, t, m =>
      ∃ (mKeep mGive : Mem 64) (mid : Mem 64 → Tup Val bs → Prop),
        split m mKeep mGive ∧
        ext t mGive action as bs (vals args) mid ∧
        ∀ mReceive res, mid mReceive res →
          ∀ m', split m' mKeep mReceive →
            Cmd.wp ext Γ B Q (k res)
              (⟨as, bs, mGive, action, vals args, mReceive, res⟩ :: t) m'
  | _, B, Q, .stackalloc nbytes body, t, mSmall =>
      nbytes ≤ B ∧
      ∀ (a : BitVec 64) (mStack mCombined : Mem 64),
        anybytes a nbytes mStack → split mCombined mSmall mStack →
        Cmd.wp ext Γ (B - nbytes)
          (fun vs t' mCombined' =>
            ∃ mSmall' mStack', anybytes a nbytes mStack' ∧
              split mCombined' mSmall' mStack' ∧ Q vs t' mSmall')
          (body a) t mCombined
  | _, B, Q, .seq c₁ c₂, t, m =>
      Cmd.wp ext Γ B (fun mid t' m' => Cmd.wp ext Γ B Q (c₂ mid) t' m') c₁ t m
  | _, B, Q, .cond c tBr eBr, t, m =>
      (c.val = true → Cmd.wp ext Γ B Q tBr t m) ∧
      (c.val = false → Cmd.wp ext Γ B Q eBr t m)
  | _, B, Q, .while_ (st := st) init test body k, t, m =>
      ∀ (I : Tup Val st → TraceB → Mem 64 → Prop),
        (∀ s t' m',
          Cmd.wp ext Γ (rs := [.bool]) B
            (fun (b, ()) t₁ m₁ =>
              (b = true → Cmd.wp ext Γ B (fun s' t₂ m₂ => I s' t₂ m₂) (body s) t₁ m₁) ∧
              (b = false → Cmd.wp ext Γ B Q (k s) t₁ m₁))
            (test s) t' m' →
          I s t' m') →
        I (vals init) t m
  | _, _, _, .hlt, _, _ => False

/-- Weakest-precondition specification of a closed function `FuncB as rs`. -/
def FuncB.wp {as rs : List Ty} (ext : ExtSpecB) (Γ : EnvB) (f : FuncB as rs) : SpecB as rs :=
  fun B xs t m Q => Cmd.wp ext Γ B Q (f Val xs) t m

/-! ### Stack-unbounded `Cmd.wpUnbounded` (for 64-bit lowering to `LeanQbe.T.wp`) -/

/-- Unbounded-budget Bedrock2 weakest precondition (requiring only `nbytes < 2 ^ 64` at
`stackalloc`, matching 64-bit `LeanQbe.T.wp` where stack bounds are checked separately). -/
def Cmd.wpUnbounded (ext : ExtSpecB) (Γ : Sym → (as rs : List Ty) → Tup Val as →
    TraceB → Mem 64 → PostB rs → Prop) :
    {rs : List Ty} → PostB rs → Cmd Val rs → TraceB → Mem 64 → Prop
  | _, Q, .ret vs, t, m => Q (vals vs) t m
  | _, Q, .let_ op k, t, m => op.wp (fun r => Cmd.wpUnbounded ext Γ Q (k r) t m)
  | _, Q, .load ty a k, t, m =>
      ∃ v, loadVal m ty a.val = some v ∧ Cmd.wpUnbounded ext Γ Q (k v) t m
  | _, Q, .store (t := ty) v a k, t, m =>
      storeOk m ty a.val ∧ Cmd.wpUnbounded ext Γ Q k t (storeMem m ty a.val v.val)
  | _, Q, .call f (as := as) (bs := bs) args k, t, m =>
      ∃ (P : PostB bs), Γ f as bs (vals args) t m P ∧
        ∀ r t' m', P r t' m' → Cmd.wpUnbounded ext Γ Q (k r) t' m'
  | _, Q, .interact action (as := as) (bs := bs) args k, t, m =>
      ∃ (mKeep mGive : Mem 64) (mid : Mem 64 → Tup Val bs → Prop),
        split m mKeep mGive ∧
        ext t mGive action as bs (vals args) mid ∧
        ∀ mReceive res, mid mReceive res →
          ∀ m', split m' mKeep mReceive →
            Cmd.wpUnbounded ext Γ Q (k res)
              (⟨as, bs, mGive, action, vals args, mReceive, res⟩ :: t) m'
  | _, Q, .stackalloc nbytes body, t, mSmall =>
      nbytes < 2 ^ 64 ∧
      ∀ (a : BitVec 64) (mStack mCombined : Mem 64),
        anybytes a nbytes mStack → split mCombined mSmall mStack →
        Cmd.wpUnbounded ext Γ
          (fun vs t' mCombined' =>
            ∃ mSmall' mStack', anybytes a nbytes mStack' ∧
              split mCombined' mSmall' mStack' ∧ Q vs t' mSmall')
          (body a) t mCombined
  | _, Q, .seq c₁ c₂, t, m =>
      Cmd.wpUnbounded ext Γ (fun mid t' m' => Cmd.wpUnbounded ext Γ Q (c₂ mid) t' m') c₁ t m
  | _, Q, .cond c tBr eBr, t, m =>
      (c.val = true → Cmd.wpUnbounded ext Γ Q tBr t m) ∧
      (c.val = false → Cmd.wpUnbounded ext Γ Q eBr t m)
  | _, Q, .while_ (st := st) init test body k, t, m =>
      ∀ (I : Tup Val st → TraceB → Mem 64 → Prop),
        (∀ s t' m',
          Cmd.wpUnbounded ext Γ (rs := [.bool])
            (fun (b, ()) t₁ m₁ =>
              (b = true → Cmd.wpUnbounded ext Γ (fun s' t₂ m₂ => I s' t₂ m₂) (body s) t₁ m₁) ∧
              (b = false → Cmd.wpUnbounded ext Γ Q (k s) t₁ m₁))
            (test s) t' m' →
          I s t' m') →
        I (vals init) t m
  | _, _, .hlt, _, _ => False

/-- Unbounded-budget `wp` for a closed `FuncB`. -/
def FuncB.wpUnbounded {as rs : List Ty} (ext : ExtSpecB)
    (Γ : Sym → (as rs : List Ty) → Tup Val as → TraceB → Mem 64 → PostB rs → Prop)
    (f : FuncB as rs) (xs : Tup Val as) (t : TraceB) (m : Mem 64) (Q : PostB rs) : Prop :=
  Cmd.wpUnbounded ext Γ Q (f Val xs) t m

/-! ### Memory/separation bridges between `Kraken.Bedrock2` and `LeanQbe.T` -/

theorem anybytes_iff_region {a : BitVec 64} {n : Nat} {m : Mem 64} :
    anybytes a n m ↔ region a n m ∧ n ≤ 2 ^ 64 := by
  constructor
  · rintro ⟨bs, rfl, hlen, hle⟩; exact ⟨⟨bs, hlen, rfl⟩, hle⟩
  · rintro ⟨⟨bs, hlen, rfl⟩, hle⟩; exact ⟨bs, rfl, hlen, hle⟩

theorem split_iff_sep {m m1 m2 : Mem 64} : split m m1 m2 ↔ (Eq m1 ⋆ Eq m2) m :=
  ⟨fun ⟨hu, hi⟩ => ⟨m1, m2, hu, hi, rfl, rfl⟩,
   fun ⟨_, _, hu, hi, rfl, rfl⟩ => ⟨hu, hi⟩⟩

theorem split_sep {m m1 m2 : Mem 64} {P Q : Mem 64 → Prop}
    (hs : split m m1 m2) (h1 : P m1) (h2 : Q m2) : (P ⋆ Q) m :=
  ⟨m1, m2, hs.1, hs.2, h1, h2⟩

theorem anybytes8_exists_cell64 {a : BitVec 64} {m : Mem 64} (h : anybytes a 8 m) :
    ∃ v : BitVec 64, cell64 a v m := by
  rcases h with ⟨bs, rfl, hlen, -⟩
  refine ⟨(UInt64.ofBytes bs).toBitVec, ?_⟩
  change ((Int.toBytes 8 (UInt64.ofBytes bs).toBitVec.toInt).At a) = bs.At a
  have hb : Int.toBytes 8 (UInt64.ofBytes bs).toBitVec.toInt = bs := by
    have ht := UInt64.toBytes_ofBytes bs (by omega)
    simpa [UInt64.toBytes, List.take_of_length_le (Nat.le_of_eq hlen)] using ht
  rw [hb]

theorem cell64_anybytes8 {a v : BitVec 64} {m : Mem 64} (h : cell64 a v m) :
    anybytes a 8 m :=
  ⟨Int.toBytes 8 v.toInt, h, Int.toBytes_length 8 v.toInt, by decide⟩

/-! ### Consequence, monotonicity, and loop rules -/

/-- Unified consequence rule for `Cmd.wp` (simultaneously monotone in `ext`, `Γ`, `B`, `Q`). -/
theorem Cmd.wp_conseq {ext ext' : ExtSpecB} {Γ Γ' : EnvB}
    (hext : ∀ t mGive a as bs args mid,
      ext t mGive a as bs args mid → ext' t mGive a as bs args mid)
    (hΓ : ∀ f as bs B args t m P, Γ f as bs B args t m P → Γ' f as bs B args t m P)
    (hΓB : ∀ f as bs B₁ B₂ args t m P,
      B₁ ≤ B₂ → Γ' f as bs B₁ args t m P → Γ' f as bs B₂ args t m P) :
    {rs : List Ty} → (c : Cmd Val rs) → ∀ {B₁ B₂ : Nat}, B₁ ≤ B₂ →
    ∀ {Q Q' : PostB rs}, (∀ vs t m, Q vs t m → Q' vs t m) →
    ∀ t m, Cmd.wp ext Γ B₁ Q c t m → Cmd.wp ext' Γ' B₂ Q' c t m
  | _, .ret vs, _, _, _, _, _, hQ, t, m, h => hQ (vals vs) t m h
  | _, .let_ op k, _, _, hB, _, _, hQ, t, m, h =>
      Op.wp_mono (fun r hr => Cmd.wp_conseq hext hΓ hΓB (k r) hB hQ t m hr) h
  | _, .load _ _ k, _, _, hB, _, _, hQ, t, m, h => by
      rcases h with ⟨v, hv, hk⟩
      exact ⟨v, hv, Cmd.wp_conseq hext hΓ hΓB (k v) hB hQ t m hk⟩
  | _, .store _ _ k, _, _, hB, _, _, hQ, t, _, h => by
      rcases h with ⟨hok, hk⟩
      exact ⟨hok, Cmd.wp_conseq hext hΓ hΓB k hB hQ t _ hk⟩
  | _, .call f _ k, B₁, B₂, hB, _, _, hQ, t, m, h => by
      rcases h with ⟨P, hcall, hk⟩
      exact ⟨P, hΓB f _ _ B₁ B₂ _ t m P hB (hΓ f _ _ B₁ _ t m P hcall),
        fun r t' m' hp => Cmd.wp_conseq hext hΓ hΓB (k r) hB hQ t' m' (hk r t' m' hp)⟩
  | _, .interact _ _ k, _, _, hB, _, _, hQ, _, _, h => by
      rcases h with ⟨mKeep, mGive, mid, hsp, hx, hk⟩
      exact ⟨mKeep, mGive, mid, hsp, hext _ _ _ _ _ _ _ hx,
        fun mRec res hm m' hsp' =>
          Cmd.wp_conseq hext hΓ hΓB (k res) hB hQ _ m' (hk mRec res hm m' hsp')⟩
  | _, .stackalloc nbytes body, _, _, hB, _, _, hQ, t, _, h => by
      rcases h with ⟨hle, hbody⟩
      exact ⟨Nat.le_trans hle hB, fun a mStack mComb hany hsp =>
        Cmd.wp_conseq hext hΓ hΓB (body a) (Nat.sub_le_sub_right hB nbytes)
          (fun vs t' _ ⟨mS', mSt', ha', hs', hq⟩ => ⟨mS', mSt', ha', hs', hQ vs t' mS' hq⟩)
          t mComb (hbody a mStack mComb hany hsp)⟩
  | _, .seq c₁ c₂, _, _, hB, _, _, hQ, t, m, h =>
      Cmd.wp_conseq hext hΓ hΓB c₁ hB
        (fun mid t' m' hm => Cmd.wp_conseq hext hΓ hΓB (c₂ mid) hB hQ t' m' hm) t m h
  | _, .cond _ tBr eBr, _, _, hB, _, _, hQ, t, m, h => by
      rcases h with ⟨ht, he⟩
      exact ⟨fun hc => Cmd.wp_conseq hext hΓ hΓB tBr hB hQ t m (ht hc),
        fun hc => Cmd.wp_conseq hext hΓ hΓB eBr hB hQ t m (he hc)⟩
  | _, .while_ _ test body k, _, _, hB, _, _, hQ, t, m, h =>
      fun I hI => h I fun s t' m' hs =>
        hI s t' m' <| Cmd.wp_conseq hext hΓ hΓB (test s) hB
          (fun (b, ()) t₁ m₁ ⟨ht, hf⟩ =>
            ⟨fun hb => Cmd.wp_conseq hext hΓ hΓB (body s) hB (fun _ _ _ hi => hi) t₁ m₁ (ht hb),
             fun hb => Cmd.wp_conseq hext hΓ hΓB (k s) hB hQ t₁ m₁ (hf hb)⟩)
          t' m' hs
  | _, .hlt, _, _, _, _, _, _, _, _, h => h

/-- Postcondition monotonicity (consequence rule) for `Cmd.wp`, with no side conditions
on `ext` or `Γ`. -/
theorem Cmd.wp_mono {ext : ExtSpecB} {Γ : EnvB} {B : Nat} {rs : List Ty}
    {Q Q' : PostB rs} (hQ : ∀ vs t m, Q vs t m → Q' vs t m) :
    (c : Cmd Val rs) → ∀ t m, Cmd.wp ext Γ B Q c t m → Cmd.wp ext Γ B Q' c t m
  | .ret vs, t, m, h => hQ (vals vs) t m h
  | .let_ op k, t, m, h => Op.wp_mono (fun r hr => Cmd.wp_mono hQ (k r) t m hr) h
  | .load _ _ k, t, m, h => by
      rcases h with ⟨v, hv, hk⟩
      exact ⟨v, hv, Cmd.wp_mono hQ (k v) t m hk⟩
  | .store _ _ k, t, _, h => by
      rcases h with ⟨hok, hk⟩
      exact ⟨hok, Cmd.wp_mono hQ k t _ hk⟩
  | .call _ _ k, _, _, h => by
      rcases h with ⟨P, hcall, hk⟩
      exact ⟨P, hcall, fun r t' m' hp => Cmd.wp_mono hQ (k r) t' m' (hk r t' m' hp)⟩
  | .interact _ _ k, _, _, h => by
      rcases h with ⟨mKeep, mGive, mid, hsp, hx, hk⟩
      exact ⟨mKeep, mGive, mid, hsp, hx,
        fun mRec res hm m' hsp' => Cmd.wp_mono hQ (k res) _ m' (hk mRec res hm m' hsp')⟩
  | .stackalloc _ body, t, _, h => by
      rcases h with ⟨hle, hbody⟩
      exact ⟨hle, fun a mStack mComb hany hsp =>
        Cmd.wp_mono
          (fun vs t' _ ⟨mS', mSt', ha', hs', hq⟩ => ⟨mS', mSt', ha', hs', hQ vs t' mS' hq⟩)
          (body a) t mComb (hbody a mStack mComb hany hsp)⟩
  | .seq c₁ c₂, t, m, h =>
      Cmd.wp_mono (fun mid t' m' hm => Cmd.wp_mono hQ (c₂ mid) t' m' hm) c₁ t m h
  | .cond _ tBr eBr, t, m, h => by
      rcases h with ⟨ht, he⟩
      exact ⟨fun hc => Cmd.wp_mono hQ tBr t m (ht hc),
        fun hc => Cmd.wp_mono hQ eBr t m (he hc)⟩
  | .while_ _ test body k, t, m, h =>
      fun I hI => h I fun s t' m' hs =>
        hI s t' m' <| Cmd.wp_mono
          (fun (b, ()) t₁ m₁ ⟨ht, hf⟩ =>
            ⟨ht, fun hb => Cmd.wp_mono hQ (k s) t₁ m₁ (hf hb)⟩)
          (test s) t' m' hs
  | .hlt, _, _, h => h

/-- Postcondition monotonicity for `Cmd.wpUnbounded`. -/
theorem Cmd.wpUnbounded_mono {ext : ExtSpecB}
    {Γ : Sym → (as rs : List Ty) → Tup Val as → TraceB → Mem 64 → PostB rs → Prop}
    {rs : List Ty} {Q Q' : PostB rs} (hQ : ∀ vs t m, Q vs t m → Q' vs t m) :
    (c : Cmd Val rs) → ∀ t m,
    Cmd.wpUnbounded ext Γ Q c t m → Cmd.wpUnbounded ext Γ Q' c t m
  | .ret vs, t, m, h => hQ (vals vs) t m h
  | .let_ op k, t, m, h => Op.wp_mono (fun r hr => Cmd.wpUnbounded_mono hQ (k r) t m hr) h
  | .load _ _ k, t, m, h => by
      rcases h with ⟨v, hv, hk⟩
      exact ⟨v, hv, Cmd.wpUnbounded_mono hQ (k v) t m hk⟩
  | .store _ _ k, t, _, h => by
      rcases h with ⟨hok, hk⟩
      exact ⟨hok, Cmd.wpUnbounded_mono hQ k t _ hk⟩
  | .call _ _ k, _, _, h => by
      rcases h with ⟨P, hcall, hk⟩
      exact ⟨P, hcall, fun r t' m' hp => Cmd.wpUnbounded_mono hQ (k r) t' m' (hk r t' m' hp)⟩
  | .interact _ _ k, _, _, h => by
      rcases h with ⟨mKeep, mGive, mid, hsp, hx, hk⟩
      exact ⟨mKeep, mGive, mid, hsp, hx,
        fun mRec res hm m' hsp' => Cmd.wpUnbounded_mono hQ (k res) _ m' (hk mRec res hm m' hsp')⟩
  | .stackalloc _ body, t, _, h => by
      rcases h with ⟨hle, hbody⟩
      exact ⟨hle, fun a mStack mComb hany hsp =>
        Cmd.wpUnbounded_mono
          (fun vs t' _ ⟨mS', mSt', ha', hs', hq⟩ => ⟨mS', mSt', ha', hs', hQ vs t' mS' hq⟩)
          (body a) t mComb (hbody a mStack mComb hany hsp)⟩
  | .seq c₁ c₂, t, m, h =>
      Cmd.wpUnbounded_mono (fun mid t' m' hm => Cmd.wpUnbounded_mono hQ (c₂ mid) t' m' hm) c₁ t m h
  | .cond _ tBr eBr, t, m, h => by
      rcases h with ⟨ht, he⟩
      exact ⟨fun hc => Cmd.wpUnbounded_mono hQ tBr t m (ht hc),
        fun hc => Cmd.wpUnbounded_mono hQ eBr t m (he hc)⟩
  | .while_ _ test body k, t, m, h =>
      fun I hI => h I fun s t' m' hs =>
        hI s t' m' <| Cmd.wpUnbounded_mono
          (fun (b, ()) t₁ m₁ ⟨ht, hf⟩ =>
            ⟨ht, fun hb => Cmd.wpUnbounded_mono hQ (k s) t₁ m₁ (hf hb)⟩)
          (test s) t' m' hs
  | .hlt, _, _, h => h

/-- Bridge from budgeted `Cmd.wp` (when `B < 2 ^ 64`) to `Cmd.wpUnbounded`. -/
theorem Cmd.wpUnbounded_of_wp {ext : ExtSpecB} {Γ : EnvB}
    {Γu : Sym → (as rs : List Ty) → Tup Val as → TraceB → Mem 64 → PostB rs → Prop}
    (hΓ : ∀ f as bs B args t m P, B < 2 ^ 64 → Γ f as bs B args t m P → Γu f as bs args t m P) :
    {rs : List Ty} → (c : Cmd Val rs) → ∀ {B : Nat}, B < 2 ^ 64 →
    ∀ {Q : PostB rs} (t : TraceB) (m : Mem 64),
    Cmd.wp ext Γ B Q c t m → Cmd.wpUnbounded ext Γu Q c t m
  | _, .ret _, _, _, _, _, _, h => h
  | _, .let_ _ k, _, hB, _, t, m, h =>
      Op.wp_mono (fun r hr => Cmd.wpUnbounded_of_wp hΓ (k r) hB t m hr) h
  | _, .load _ _ k, _, hB, _, t, m, h => by
      rcases h with ⟨v, hv, hk⟩
      exact ⟨v, hv, Cmd.wpUnbounded_of_wp hΓ (k v) hB t m hk⟩
  | _, .store _ _ k, _, hB, _, t, _, h => by
      rcases h with ⟨hok, hk⟩
      exact ⟨hok, Cmd.wpUnbounded_of_wp hΓ k hB t _ hk⟩
  | _, .call f _ k, B, hB, _, t, m, h => by
      rcases h with ⟨P, hcall, hk⟩
      exact ⟨P, hΓ f _ _ B _ t m P hB hcall,
        fun r t' m' hp => Cmd.wpUnbounded_of_wp hΓ (k r) hB t' m' (hk r t' m' hp)⟩
  | _, .interact _ _ k, _, hB, _, _, _, h => by
      rcases h with ⟨mKeep, mGive, mid, hsp, hx, hk⟩
      exact ⟨mKeep, mGive, mid, hsp, hx, fun mRec res hm m' hsp' =>
        Cmd.wpUnbounded_of_wp hΓ (k res) hB _ m' (hk mRec res hm m' hsp')⟩
  | _, .stackalloc nbytes body, _, hB, _, t, _, h => by
      rcases h with ⟨hle, hbody⟩
      exact ⟨Nat.lt_of_le_of_lt hle hB, fun a mStack mComb hany hsp =>
        Cmd.wpUnbounded_of_wp hΓ (body a) (by omega) t mComb (hbody a mStack mComb hany hsp)⟩
  | _, .seq c₁ c₂, _, hB, _, t, m, h =>
      Cmd.wpUnbounded_of_wp hΓ c₁ hB t m <|
        Cmd.wp_mono (fun mid t' m' hm => Cmd.wpUnbounded_of_wp hΓ (c₂ mid) hB t' m' hm) c₁ t m h
  | _, .cond _ tBr eBr, _, hB, _, t, m, h => by
      rcases h with ⟨ht, he⟩
      exact ⟨fun hc => Cmd.wpUnbounded_of_wp hΓ tBr hB t m (ht hc),
        fun hc => Cmd.wpUnbounded_of_wp hΓ eBr hB t m (he hc)⟩
  | _, .while_ _ test body k, _, hB, _, t, m, h =>
      fun I hI => h I fun s t' m' hs =>
        hI s t' m' <| Cmd.wpUnbounded_of_wp hΓ (test s) hB t' m' <|
          Cmd.wp_mono (fun (b, ()) t₁ m₁ ⟨ht, hf⟩ =>
            ⟨fun hb => Cmd.wpUnbounded_of_wp hΓ (body s) hB t₁ m₁ (ht hb),
             fun hb => Cmd.wpUnbounded_of_wp hΓ (k s) hB t₁ m₁ (hf hb)⟩)
            (test s) t' m' hs
  | _, .hlt, _, _, _, _, _, h => h

/-- Stack-budget monotonicity for `Cmd.wp` (assuming callees in `Γ` are budget-monotone). -/
theorem Cmd.wp_budget_mono {ext : ExtSpecB} {Γ : EnvB}
    (hΓB : ∀ f as bs B₁ B₂ args t m P,
      B₁ ≤ B₂ → Γ f as bs B₁ args t m P → Γ f as bs B₂ args t m P)
    {B₁ B₂ : Nat} (hB : B₁ ≤ B₂) {rs : List Ty} {Q : PostB rs} (c : Cmd Val rs)
    (t : TraceB) (m : Mem 64) :
    Cmd.wp ext Γ B₁ Q c t m → Cmd.wp ext Γ B₂ Q c t m :=
  Cmd.wp_conseq (fun _ _ _ _ _ _ _ h => h) (fun _ _ _ _ _ _ _ _ h => h) hΓB c hB
    (fun _ _ _ h => h) t m

/-- Environment & external-spec monotonicity for `Cmd.wp` (no `hΓB` needed). -/
theorem Cmd.wp_env_ext_mono {ext ext' : ExtSpecB} {Γ Γ' : EnvB}
    (hext : ∀ t mGive a as bs args mid,
      ext t mGive a as bs args mid → ext' t mGive a as bs args mid)
    (hΓ : ∀ f as bs B args t m P, Γ f as bs B args t m P → Γ' f as bs B args t m P) :
    {rs : List Ty} → (c : Cmd Val rs) → ∀ {B : Nat} {Q : PostB rs} (t : TraceB) (m : Mem 64),
    Cmd.wp ext Γ B Q c t m → Cmd.wp ext' Γ' B Q c t m
  | _, .ret _, _, _, _, _, h => h
  | _, .let_ op k, _, _, t, m, h =>
      Op.wp_mono (fun r hr => Cmd.wp_env_ext_mono hext hΓ (k r) t m hr) h
  | _, .load _ _ k, _, _, t, m, h => by
      rcases h with ⟨v, hv, hk⟩
      exact ⟨v, hv, Cmd.wp_env_ext_mono hext hΓ (k v) t m hk⟩
  | _, .store _ _ k, _, _, t, _, h => by
      rcases h with ⟨hok, hk⟩
      exact ⟨hok, Cmd.wp_env_ext_mono hext hΓ k t _ hk⟩
  | _, .call f _ k, B, _, t, m, h => by
      rcases h with ⟨P, hcall, hk⟩
      exact ⟨P, hΓ f _ _ B _ t m P hcall,
        fun r t' m' hp => Cmd.wp_env_ext_mono hext hΓ (k r) t' m' (hk r t' m' hp)⟩
  | _, .interact _ _ k, _, _, _, _, h => by
      rcases h with ⟨mKeep, mGive, mid, hsp, hx, hk⟩
      exact ⟨mKeep, mGive, mid, hsp, hext _ _ _ _ _ _ _ hx,
        fun mRec res hm m' hsp' =>
          Cmd.wp_env_ext_mono hext hΓ (k res) _ m' (hk mRec res hm m' hsp')⟩
  | _, .stackalloc _ body, _, _, t, _, h => by
      rcases h with ⟨hle, hbody⟩
      exact ⟨hle, fun a mStack mComb hany hsp =>
        Cmd.wp_env_ext_mono hext hΓ (body a) t mComb (hbody a mStack mComb hany hsp)⟩
  | _, .seq c₁ c₂, _, _, t, m, h =>
      Cmd.wp_env_ext_mono hext hΓ c₁ t m <|
        Cmd.wp_mono (fun mid t' m' hm => Cmd.wp_env_ext_mono hext hΓ (c₂ mid) t' m' hm) c₁ t m h
  | _, .cond _ tBr eBr, _, _, t, m, h => by
      rcases h with ⟨ht, he⟩
      exact ⟨fun hc => Cmd.wp_env_ext_mono hext hΓ tBr t m (ht hc),
        fun hc => Cmd.wp_env_ext_mono hext hΓ eBr t m (he hc)⟩
  | _, .while_ _ test body k, _, _, t, m, h =>
      fun I hI => h I fun s t' m' hs =>
        hI s t' m' <| Cmd.wp_env_ext_mono hext hΓ (test s) t' m' <|
          Cmd.wp_mono
            (fun (b, ()) t₁ m₁ ⟨ht, hf⟩ =>
              ⟨fun hb => Cmd.wp_env_ext_mono hext hΓ (body s) t₁ m₁ (ht hb),
               fun hb => Cmd.wp_env_ext_mono hext hΓ (k s) t₁ m₁ (hf hb)⟩)
            (test s) t' m' hs
  | _, .hlt, _, _, _, _, h => h

/-- Environment monotonicity for `Cmd.wp`. -/
theorem Cmd.wp_env_mono {ext : ExtSpecB} {Γ Γ' : EnvB}
    (hΓ : ∀ f as bs B args t m P, Γ f as bs B args t m P → Γ' f as bs B args t m P)
    {B : Nat} {rs : List Ty} {Q : PostB rs} (c : Cmd Val rs) (t : TraceB) (m : Mem 64) :
    Cmd.wp ext Γ B Q c t m → Cmd.wp ext Γ' B Q c t m :=
  Cmd.wp_env_ext_mono (fun _ _ _ _ _ _ _ h => h) hΓ c t m

/-- Hoare-style `seq` introduction with an explicit intermediate assertion `mid`. -/
theorem Cmd.wp_seq_mid {ext : ExtSpecB} {Γ : EnvB} {B : Nat} {rs mid : List Ty}
    {Q : PostB rs} {c₁ : Cmd Val mid} {c₂ : Tup Val mid → Cmd Val rs}
    {t : TraceB} {m : Mem 64} (M : PostB mid)
    (h₁ : Cmd.wp ext Γ B M c₁ t m)
    (h₂ : ∀ vs t' m', M vs t' m' → Cmd.wp ext Γ B Q (c₂ vs) t' m') :
    Cmd.wp ext Γ B Q (.seq c₁ c₂) t m :=
  Cmd.wp_mono h₂ c₁ t m h₁

/-- Turn a tuple of variables into a tuple of `Arg.var` operands. -/
def Tup.toArgs {V : Ty → Type} : {ts : List Ty} → Tup V ts → Tup (Arg V) ts
  | [], () => ()
  | _ :: _, (x, xs) => (.var x, Tup.toArgs xs)

@[simp] theorem vals_toArgs : {ts : List Ty} → (xs : Tup Val ts) → vals (Tup.toArgs xs) = xs
  | [], () => rfl
  | _ :: _, (_, xs) => congrArg (_ , ·) (vals_toArgs xs)

/-- Knaster-Tarski fixpoint unfolding of `Cmd.while_`. -/
theorem Cmd.wp_while_unfold {ext : ExtSpecB} {Γ : EnvB} {B : Nat} {rs st : List Ty}
    {Q : PostB rs} (init : Tup (Arg Val) st) (test : Tup Val st → Cmd Val [.bool])
    (body : Tup Val st → Cmd Val st) (k : Tup Val st → Cmd Val rs)
    (t : TraceB) (m : Mem 64) :
    Cmd.wp ext Γ B Q (.while_ init test body k) t m ↔
      Cmd.wp ext Γ (rs := [.bool]) B
        (fun (b, ()) t₁ m₁ =>
          (b = true → Cmd.wp ext Γ B
            (fun s' t₂ m₂ =>
              Cmd.wp ext Γ B Q (.while_ (Tup.toArgs s') test body k) t₂ m₂)
            (body (vals init)) t₁ m₁) ∧
          (b = false → Cmd.wp ext Γ B Q (k (vals init)) t₁ m₁))
        (test (vals init)) t m := by
  let F (I : Tup Val st → TraceB → Mem 64 → Prop) (s : Tup Val st) (t' : TraceB) (m' : Mem 64) :=
    Cmd.wp ext Γ (rs := [.bool]) B
      (fun (b, ()) t₁ m₁ =>
        (b = true → Cmd.wp ext Γ B I (body s) t₁ m₁) ∧
        (b = false → Cmd.wp ext Γ B Q (k s) t₁ m₁))
      (test s) t' m'
  let W (s : Tup Val st) (t' : TraceB) (m' : Mem 64) : Prop :=
    ∀ I, (∀ s₁ t₁ m₁, F I s₁ t₁ m₁ → I s₁ t₁ m₁) → I s t' m'
  have hF_mono : ∀ {I₁ I₂}, (∀ s t' m', I₁ s t' m' → I₂ s t' m') →
      ∀ s t' m', F I₁ s t' m' → F I₂ s t' m' := fun hI s t' m' h =>
    Cmd.wp_mono (fun (b, ()) t₁ m₁ ⟨ht, hf⟩ =>
      ⟨fun hb => Cmd.wp_mono hI (body s) t₁ m₁ (ht hb), hf⟩) (test s) t' m' h
  have hpre : ∀ s t' m', F W s t' m' → W s t' m' := fun s t' m' hFW I hI =>
    hI s t' m' (hF_mono (fun s₁ t₁ m₁ hw => hw I hI) s t' m' hFW)
  have hWeq : ∀ s' t₂ m₂,
      Cmd.wp ext Γ B Q (.while_ (Tup.toArgs s') test body k) t₂ m₂ = W s' t₂ m₂ := by
    intro s' t₂ m₂; simp only [Cmd.wp, vals_toArgs, W, F]
  constructor
  · intro hW
    have hFW : F W (vals init) t m :=
      hW (F W) fun s₁ t₁ m₁ hFF => hF_mono hpre s₁ t₁ m₁ hFF
    exact hF_mono (fun s' t₂ m₂ hw => (hWeq s' t₂ m₂).symm ▸ hw) (vals init) t m hFW
  · intro hFW
    exact hpre (vals init) t m
      (hF_mono (fun s' t₂ m₂ hw => (hWeq s' t₂ m₂) ▸ hw) (vals init) t m hFW)

/-- Well-founded measure induction rule for `Cmd.while_`. -/
theorem Cmd.wp_while_measure {ext : ExtSpecB} {Γ : EnvB} {B : Nat} {rs st : List Ty}
    {Q : PostB rs} {Measure : Type} {lt : Measure → Measure → Prop} (hwf : WellFounded lt)
    (init : Tup (Arg Val) st) (test : Tup Val st → Cmd Val [.bool])
    (body : Tup Val st → Cmd Val st) (k : Tup Val st → Cmd Val rs)
    (Inv : Measure → Tup Val st → TraceB → Mem 64 → Prop)
    {t : TraceB} {m : Mem 64} {v₀ : Measure} (hinit : Inv v₀ (vals init) t m)
    (hstep : ∀ v s t' m', Inv v s t' m' →
      Cmd.wp ext Γ (rs := [.bool]) B
        (fun (b, ()) t₁ m₁ =>
          (b = true → Cmd.wp ext Γ B
            (fun s' t₂ m₂ => ∃ v', lt v' v ∧ Inv v' s' t₂ m₂) (body s) t₁ m₁) ∧
          (b = false → Cmd.wp ext Γ B Q (k s) t₁ m₁))
        (test s) t' m') :
    Cmd.wp ext Γ B Q (.while_ init test body k) t m := by
  intro I hI
  suffices ∀ v s t' m', Inv v s t' m' → I s t' m' from this v₀ (vals init) t m hinit
  intro v
  induction v using hwf.induction with
  | _ v ih =>
    intro s t' m' hinv
    refine hI s t' m' ?_
    refine Cmd.wp_mono (fun (b, ()) t₁ m₁ ⟨ht, hf⟩ => ⟨fun hb => ?_, hf⟩)
      (test s) t' m' (hstep v s t' m' hinv)
    exact Cmd.wp_mono (fun s' t₂ m₂ ⟨v', h_lt, hv'⟩ => ih v' h_lt s' t₂ m₂ hv')
      (body s) t₁ m₁ (ht hb)

/-- Specialized `Nat` rank measure rule for `Cmd.while_`. -/
theorem Cmd.wp_while_nat {ext : ExtSpecB} {Γ : EnvB} {B : Nat} {rs st : List Ty}
    {Q : PostB rs} (init : Tup (Arg Val) st) (test : Tup Val st → Cmd Val [.bool])
    (body : Tup Val st → Cmd Val st) (k : Tup Val st → Cmd Val rs)
    (Inv : Nat → Tup Val st → TraceB → Mem 64 → Prop)
    {t : TraceB} {m : Mem 64} {n₀ : Nat} (hinit : Inv n₀ (vals init) t m)
    (hstep : ∀ n s t' m', Inv n s t' m' →
      Cmd.wp ext Γ (rs := [.bool]) B
        (fun (b, ()) t₁ m₁ =>
          (b = true → Cmd.wp ext Γ B
            (fun s' t₂ m₂ => ∃ n', n' < n ∧ Inv n' s' t₂ m₂) (body s) t₁ m₁) ∧
          (b = false → Cmd.wp ext Γ B Q (k s) t₁ m₁))
        (test s) t' m') :
    Cmd.wp ext Γ B Q (.while_ init test body k) t m :=
  Cmd.wp_while_measure Nat.lt_wfRel.wf init test body k Inv hinit hstep

/-! ### Pure specialization (`wpPure`) aligning with `LeanQbe.T.Spec` -/

/-- Empty external specification (no I/O interactions permitted). -/
def extEmpty : ExtSpecB := fun _ _ _ _ _ _ _ => False

/-- Lift a `LeanQbe.T.Env` (plus exit postcondition `X`) into a Bedrock2 `EnvB` that
ignores stack budget and leaves the trace unchanged. -/
def EnvB.ofTEnv (Γ : Env) (X : XPost) : EnvB :=
  fun f as bs _ args t m P =>
    ∃ (P' : Post bs) (E : XPost),
      Γ f as bs args m P' E ∧
      (∀ r m', P' r m' → P r t m') ∧
      (∀ g cs xs m', E g cs xs m' → X g cs xs m')

/-- Pure specialization of `Cmd.wp`: empty `ext`, unbounded stack (`∃ B`), empty initial
trace, aligning with `LeanQbe.T.wp` and `LeanQbe.T.Spec`. -/
def Cmd.wpPure (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost)
    (c : Cmd Val rs) (m : Mem 64) : Prop :=
  ∃ B : Nat, Cmd.wp extEmpty (EnvB.ofTEnv Γ X) B (fun vs _ m' => Q vs m') c [] m

/-- Pure specialization of `FuncB.wp`, producing a `LeanQbe.T.Spec as rs`. -/
def FuncB.wpPure {as rs : List Ty} (Γ : Env) (f : FuncB as rs) : Spec as rs :=
  fun xs m Q X => Cmd.wpPure Γ Q X (f Val xs) m

theorem Cmd.wpPure_mono {Γ : Env} {rs : List Ty} {Q Q' : Post rs} {X X' : XPost}
    (hQ : ∀ vs m, Q vs m → Q' vs m)
    (hX : ∀ f cs xs m, X f cs xs m → X' f cs xs m)
    (c : Cmd Val rs) (m : Mem 64) :
    Cmd.wpPure Γ Q X c m → Cmd.wpPure Γ Q' X' c m := by
  rintro ⟨B, hB⟩
  refine ⟨B, Cmd.wp_env_ext_mono (fun _ _ _ _ _ _ _ h => h) ?_ c [] m
    (Cmd.wp_mono (fun vs _ m' h => hQ vs m' h) c [] m hB)⟩
  rintro f as bs _ args t m' P ⟨P', E, hΓ, hP, hE⟩
  exact ⟨P', E, hΓ, hP, fun g cs xs m'' he => hX g cs xs m'' (hE g cs xs m'' he)⟩

theorem FuncB.wpPure_mono {as rs : List Ty} (Γ : Env) (f : FuncB as rs) :
    (FuncB.wpPure Γ f).Mono :=
  fun xs m _ _ _ _ hQ hX h => Cmd.wpPure_mono hQ hX (f Val xs) m h

/-! ## 3. Relational Well-Formedness (`Cmd.Wf` / `FuncB.Wf` + `ModuleOkB`) -/

section
variable {V₁ V₂ : Ty → Type}

/-- Two structured Bedrock2 commands are relationally equivalent under typed value
context `G : Ctx V₁ V₂`, reusing `LeanQbe.T.ArgRel` and `LeanQbe.T.OpRel`. -/
inductive Cmd.Wf : {rs : List Ty} → Ctx V₁ V₂ → Cmd V₁ rs → Cmd V₂ rs → Prop
  | ret {rs G vs₁ vs₂} :
      TRel (ArgRel G) vs₁ vs₂ →
      Cmd.Wf (rs := rs) G (.ret vs₁) (.ret vs₂)
  | let_ {rs G ts op₁ op₂ k₁ k₂} :
      OpRel G op₁ op₂ →
      (∀ (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts),
        Cmd.Wf (Tup.zip xs₁ xs₂ ++ G) (k₁ xs₁) (k₂ xs₂)) →
      Cmd.Wf (rs := rs) G (.let_ (ts := ts) op₁ k₁) (.let_ op₂ k₂)
  | load {rs G} (t : Ty) {a₁ a₂ k₁ k₂} :
      ArgRel G i64 a₁ a₂ →
      (∀ (v₁ : V₁ t) (v₂ : V₂ t), Cmd.Wf (⟨t, v₁, v₂⟩ :: G) (k₁ v₁) (k₂ v₂)) →
      Cmd.Wf (rs := rs) G (.load t a₁ k₁) (.load t a₂ k₂)
  | store {rs G t v₁ v₂ a₁ a₂ k₁ k₂} :
      ArgRel G t v₁ v₂ → ArgRel G i64 a₁ a₂ → Cmd.Wf G k₁ k₂ →
      Cmd.Wf (rs := rs) G (.store (t := t) v₁ a₁ k₁) (.store v₂ a₂ k₂)
  | call {rs G} (f : Sym) {as bs args₁ args₂ k₁ k₂} :
      TRel (ArgRel G) args₁ args₂ →
      (∀ (xs₁ : Tup V₁ bs) (xs₂ : Tup V₂ bs),
        Cmd.Wf (Tup.zip xs₁ xs₂ ++ G) (k₁ xs₁) (k₂ xs₂)) →
      Cmd.Wf (rs := rs) G (.call f (as := as) (bs := bs) args₁ k₁) (.call f args₂ k₂)
  | interact {rs G} (action : Sym) {as bs args₁ args₂ k₁ k₂} :
      TRel (ArgRel G) args₁ args₂ →
      (∀ (xs₁ : Tup V₁ bs) (xs₂ : Tup V₂ bs),
        Cmd.Wf (Tup.zip xs₁ xs₂ ++ G) (k₁ xs₁) (k₂ xs₂)) →
      Cmd.Wf (rs := rs) G (.interact action (as := as) (bs := bs) args₁ k₁)
        (.interact action args₂ k₂)
  | stackalloc {rs G} (nbytes : Nat) {b₁ b₂} :
      (∀ (a₁ : V₁ i64) (a₂ : V₂ i64), Cmd.Wf (⟨i64, a₁, a₂⟩ :: G) (b₁ a₁) (b₂ a₂)) →
      Cmd.Wf (rs := rs) G (.stackalloc nbytes b₁) (.stackalloc nbytes b₂)
  | seq {rs mid G c₁ c₁' c₂ c₂'} :
      Cmd.Wf G c₁ c₁' →
      (∀ (xs₁ : Tup V₁ mid) (xs₂ : Tup V₂ mid),
        Cmd.Wf (Tup.zip xs₁ xs₂ ++ G) (c₂ xs₁) (c₂' xs₂)) →
      Cmd.Wf (rs := rs) G (.seq (mid := mid) c₁ c₂) (.seq c₁' c₂')
  | cond {rs G c₁ c₂ t₁ t₂ e₁ e₂} :
      ArgRel G .bool c₁ c₂ → Cmd.Wf G t₁ t₂ → Cmd.Wf G e₁ e₂ →
      Cmd.Wf (rs := rs) G (.cond c₁ t₁ e₁) (.cond c₂ t₂ e₂)
  | while_ {rs st G init₁ init₂ test₁ test₂ body₁ body₂ k₁ k₂} :
      TRel (ArgRel G) init₁ init₂ →
      (∀ (xs₁ : Tup V₁ st) (xs₂ : Tup V₂ st),
        Cmd.Wf (Tup.zip xs₁ xs₂ ++ G) (test₁ xs₁) (test₂ xs₂)) →
      (∀ (xs₁ : Tup V₁ st) (xs₂ : Tup V₂ st),
        Cmd.Wf (Tup.zip xs₁ xs₂ ++ G) (body₁ xs₁) (body₂ xs₂)) →
      (∀ (xs₁ : Tup V₁ st) (xs₂ : Tup V₂ st),
        Cmd.Wf (Tup.zip xs₁ xs₂ ++ G) (k₁ xs₁) (k₂ xs₂)) →
      Cmd.Wf (rs := rs) G (.while_ (st := st) init₁ test₁ body₁ k₁)
        (.while_ init₂ test₂ body₂ k₂)
  | hlt {rs G} : Cmd.Wf (rs := rs) G .hlt .hlt

theorem Cmd.Wf.weaken {rs : List Ty} {G : Ctx V₁ V₂} {c₁ : Cmd V₁ rs} {c₂ : Cmd V₂ rs}
    (h : Cmd.Wf G c₁ c₂) : ∀ {G'}, (∀ p ∈ G, p ∈ G') → Cmd.Wf G' c₁ c₂ := by
  induction h with
  | ret hvs => intro _ hG; exact .ret (TRel.argRel_weaken hG hvs)
  | let_ hop _ ih =>
      intro _ hG; exact .let_ (hop.weaken hG) fun x₁ x₂ => ih x₁ x₂ (append_sub_left _ hG)
  | load t ha _ ih =>
      intro _ hG; exact .load t (ha.weaken hG) fun v₁ v₂ => ih v₁ v₂ (cons_sub hG)
  | store hv ha _ ih => intro _ hG; exact .store (hv.weaken hG) (ha.weaken hG) (ih hG)
  | call f hargs _ ih =>
      intro _ hG
      exact .call f (TRel.argRel_weaken hG hargs) fun x₁ x₂ => ih x₁ x₂ (append_sub_left _ hG)
  | interact act hargs _ ih =>
      intro _ hG
      exact .interact act (TRel.argRel_weaken hG hargs) fun x₁ x₂ =>
        ih x₁ x₂ (append_sub_left _ hG)
  | stackalloc n _ ih =>
      intro _ hG; exact .stackalloc n fun a₁ a₂ => ih a₁ a₂ (cons_sub hG)
  | seq _ _ ih₁ ih₂ =>
      intro _ hG; exact .seq (ih₁ hG) fun x₁ x₂ => ih₂ x₁ x₂ (append_sub_left _ hG)
  | cond hc _ _ iht ihe => intro _ hG; exact .cond (hc.weaken hG) (iht hG) (ihe hG)
  | while_ hinit _ _ _ iht ihb ihk =>
      intro _ hG
      exact .while_ (TRel.argRel_weaken hG hinit)
        (fun x₁ x₂ => iht x₁ x₂ (append_sub_left _ hG))
        (fun x₁ x₂ => ihb x₁ x₂ (append_sub_left _ hG))
        (fun x₁ x₂ => ihk x₁ x₂ (append_sub_left _ hG))
  | hlt => intro _ _; exact .hlt

theorem Cmd.Wf.symm {rs : List Ty} {G : Ctx V₁ V₂} {c₁ : Cmd V₁ rs} {c₂ : Cmd V₂ rs}
    (h : Cmd.Wf G c₁ c₂) : Cmd.Wf G.flip c₂ c₁ := by
  induction h with
  | ret hvs => exact .ret (TRel.argRel_symm hvs)
  | let_ hop _ ih =>
      exact .let_ hop.symm fun x₂ x₁ => by simpa [Ctx.flip_append, Tup.zip_flip] using ih x₁ x₂
  | load t ha _ ih => exact .load t ha.symm fun v₂ v₁ => ih v₁ v₂
  | store hv ha _ ih => exact .store hv.symm ha.symm ih
  | call f hargs _ ih =>
      exact .call f (TRel.argRel_symm hargs) fun x₂ x₁ => by
        simpa [Ctx.flip_append, Tup.zip_flip] using ih x₁ x₂
  | interact act hargs _ ih =>
      exact .interact act (TRel.argRel_symm hargs) fun x₂ x₁ => by
        simpa [Ctx.flip_append, Tup.zip_flip] using ih x₁ x₂
  | stackalloc n _ ih => exact .stackalloc n fun a₂ a₁ => ih a₁ a₂
  | seq _ _ ih₁ ih₂ =>
      exact .seq ih₁ fun x₂ x₁ => by simpa [Ctx.flip_append, Tup.zip_flip] using ih₂ x₁ x₂
  | cond hc _ _ iht ihe => exact .cond hc.symm iht ihe
  | while_ hinit _ _ _ iht ihb ihk =>
      exact .while_ (TRel.argRel_symm hinit)
        (fun x₂ x₁ => by simpa [Ctx.flip_append, Tup.zip_flip] using iht x₁ x₂)
        (fun x₂ x₁ => by simpa [Ctx.flip_append, Tup.zip_flip] using ihb x₁ x₂)
        (fun x₂ x₁ => by simpa [Ctx.flip_append, Tup.zip_flip] using ihk x₁ x₂)
  | hlt => exact .hlt

end

/-- Every two instantiations of a closed `FuncB` at related arguments are `Cmd.Wf`-related. -/
def FuncB.Wf {as rs : List Ty} (f : FuncB as rs) : Prop :=
  ∀ (V₁ V₂ : Ty → Type) (xs₁ : Tup V₁ as) (xs₂ : Tup V₂ as),
    Cmd.Wf (Tup.zip xs₁ xs₂) (f V₁ xs₁) (f V₂ xs₂)

/-- A named function is well-formed when its body is well-formed. -/
def FnB.Wf (fn : FnB) : Prop := FuncB.Wf fn.body

/-- Syntax-directed tactic for small or type-parametric `FuncB.Wf` goals (for concrete
closed functions, prefer `t_b2_wf_reify`). -/
scoped macro "t_b2_wf_tac" : tactic =>
  `(tactic| (
    (try intro _ _ _ _)
    repeat (
      first
        | intro _ _
        | exact TRel.nil'
        | apply TRel.cons'
        | ((try dsimp only); exact ArgRel.imm _)
        | ((try dsimp only); refine ArgRel.var ?_; simp [Tup.zip, *])
        | (focus (simp [Tup.zip, *]; done))
        | refine Cmd.Wf.ret ?_
        | refine Cmd.Wf.let_ ?_ ?_
        | refine Cmd.Wf.load _ ?_ ?_
        | refine Cmd.Wf.store ?_ ?_ ?_
        | refine Cmd.Wf.call _ ?_ ?_
        | refine Cmd.Wf.interact _ ?_ ?_
        | refine Cmd.Wf.stackalloc _ ?_
        | refine Cmd.Wf.seq ?_ ?_
        | refine Cmd.Wf.cond ?_ ?_ ?_
        | refine Cmd.Wf.while_ ?_ ?_ ?_ ?_
        | exact Cmd.Wf.hlt
        | refine OpRel.mk _ ?_)))

/-! ### Acyclic `ModuleOkB` (mirroring `LeanQbe.T.Module`) -/

def FnB.sig (fn : FnB) : SigEntry := (fn.name, fn.as, fn.rs)
def ModuleB.sigs (M : ModuleB) : List SigEntry :=
  M.fns.map FnB.sig ++ M.externs.map Extern.sig
def ModuleB.names (M : ModuleB) : List Sym :=
  M.fns.map FnB.name ++ M.externs.map Extern.name
def ModuleB.namesNodup (M : ModuleB) : Prop := M.names.Nodup

def Cmd.callsOk (allowed : List SigEntry) : {rs : List Ty} → Cmd (fun _ => Unit) rs → Prop
  | _, .ret _ | _, .hlt => True
  | _, .let_ _ k => (k (Tup.units _)).callsOk allowed
  | _, .load _ _ k => (k ()).callsOk allowed
  | _, .store _ _ k => k.callsOk allowed
  | _, .call f (as := as) (bs := bs) _ k =>
      (f, as, bs) ∈ allowed ∧ (k (Tup.units bs)).callsOk allowed
  | _, .interact _ (bs := bs) _ k => (k (Tup.units bs)).callsOk allowed
  | _, .stackalloc _ body => (body ()).callsOk allowed
  | _, .seq (mid := mid) c₁ c₂ =>
      c₁.callsOk allowed ∧ (c₂ (Tup.units mid)).callsOk allowed
  | _, .cond _ t e => t.callsOk allowed ∧ e.callsOk allowed
  | _, .while_ (st := st) _ test body k =>
      (test (Tup.units st)).callsOk allowed ∧
      (body (Tup.units st)).callsOk allowed ∧
      (k (Tup.units st)).callsOk allowed

def FnB.callsOk (allowed : List SigEntry) (fn : FnB) : Prop :=
  (fn.body (fun _ => Unit) (Tup.units fn.as)).callsOk allowed

theorem wp_env_agree_of_callsOkB {ext : ExtSpecB} {Γ Γ' : EnvB}
    {allowed : List SigEntry} {rs : List Ty} {G : Ctx Val (fun _ => Unit)}
    {c₁ : Cmd Val rs} {c₂ : Cmd (fun _ => Unit) rs}
    (hwf : Cmd.Wf G c₁ c₂) (hcalls : c₂.callsOk allowed)
    (hΓ : ∀ f as bs, (f, as, bs) ∈ allowed →
      ∀ B args t m P, Γ f as bs B args t m P → Γ' f as bs B args t m P) :
    ∀ B (Q : PostB rs) t m, Cmd.wp ext Γ B Q c₁ t m → Cmd.wp ext Γ' B Q c₁ t m := by
  induction hwf with
  | ret _ | hlt => intro _ _ _ _ h; exact h
  | let_ _ _ ih =>
      intro B Q t m h
      exact Op.wp_mono (fun r hr => ih r (Tup.units _) hcalls B Q t m hr) h
  | load _ _ _ ih =>
      intro B Q t m ⟨v, hv, hk⟩
      exact ⟨v, hv, ih v () hcalls B Q t m hk⟩
  | store _ _ _ ih =>
      intro B Q t _ ⟨hok, hk⟩
      exact ⟨hok, ih hcalls B Q t _ hk⟩
  | call f _ _ ih =>
      intro B Q t m ⟨P, hcall, hk⟩
      exact ⟨P, hΓ f _ _ hcalls.1 B _ t m P hcall,
        fun r t' m' hp => ih r (Tup.units _) hcalls.2 B Q t' m' (hk r t' m' hp)⟩
  | interact _ _ _ ih =>
      intro B Q _ _ ⟨mKeep, mGive, mid, hsp, hx, hk⟩
      exact ⟨mKeep, mGive, mid, hsp, hx,
        fun mRec res hm m' hsp' =>
          ih res (Tup.units _) hcalls B Q _ m' (hk mRec res hm m' hsp')⟩
  | stackalloc _ _ ih =>
      intro B Q t _ ⟨hle, hbody⟩
      exact ⟨hle, fun a mStack mComb hany hsp =>
        ih a () hcalls (B - _) _ t mComb (hbody a mStack mComb hany hsp)⟩
  | seq _ _ ih₁ ih₂ =>
      intro B Q t m h
      exact ih₁ hcalls.1 B _ t m <|
        Cmd.wp_mono (fun mid t' m' hm => ih₂ mid (Tup.units _) hcalls.2 B Q t' m' hm) _ t m h
  | cond _ _ _ iht ihe =>
      intro B Q t m ⟨ht, he⟩
      exact ⟨fun hc => iht hcalls.1 B Q t m (ht hc),
        fun hc => ihe hcalls.2 B Q t m (he hc)⟩
  | while_ _ _ _ _ iht ihb ihk =>
      intro B Q t m h I hI
      exact h I fun s t' m' hs =>
        hI s t' m' <| iht s (Tup.units _) hcalls.1 B _ t' m' <|
          Cmd.wp_mono
            (fun (b, ()) t₁ m₁ ⟨ht, hf⟩ =>
              ⟨fun hb => ihb s (Tup.units _) hcalls.2.1 B I t₁ m₁ (ht hb),
               fun hb => ihk s (Tup.units _) hcalls.2.2 B Q t₁ m₁ (hf hb)⟩)
            _ t' m' hs

def EnvB.restrict (Γ : EnvB) (allowed : List SigEntry) : EnvB :=
  fun f as bs B args t m Q => (f, as, bs) ∈ allowed ∧ Γ f as bs B args t m Q

def EnvB.ofModule (M : ModuleB) (Γ : EnvB) : EnvB := EnvB.restrict Γ M.sigs

/-- Acyclic module correctness (callees appear before callers), mirroring `ModuleOk`. -/
structure ModuleOkB (ext : ExtSpecB) (Γ : EnvB) (M : ModuleB) : Prop where
  nodup : M.namesNodup
  fnsOk : ∀ pre fn post, M.fns = pre ++ fn :: post →
    fn.Wf ∧ fn.callsOk (pre.map FnB.sig ++ M.externs.map Extern.sig) ∧
      ∀ B xs t m Q, Γ fn.name fn.as fn.rs B xs t m Q → FuncB.wp ext Γ fn.body B xs t m Q

theorem ModuleOkB.wp_restrict {ext : ExtSpecB} {Γ : EnvB} {M : ModuleB}
    (hM : ModuleOkB ext Γ M) {pre : List FnB} {fn : FnB} {post : List FnB}
    (hsplit : M.fns = pre ++ fn :: post) {B : Nat} {xs : Tup Val fn.as} {t : TraceB}
    {m : Mem 64} {Q : PostB fn.rs} (hspec : Γ fn.name fn.as fn.rs B xs t m Q) :
    FuncB.wp ext (EnvB.restrict Γ (pre.map FnB.sig ++ M.externs.map Extern.sig))
      fn.body B xs t m Q :=
  let ⟨hwf, hcalls, hwp⟩ := hM.fnsOk pre fn post hsplit
  wp_env_agree_of_callsOkB (hwf Val (fun _ => Unit) xs (Tup.units fn.as)) hcalls
    (fun _ _ _ hmem _ _ _ _ _ hg => ⟨hmem, hg⟩) B Q t m (hwp B xs t m Q hspec)

theorem ModuleOkB.ofModule {ext : ExtSpecB} {Γ : EnvB} {M : ModuleB}
    (hM : ModuleOkB ext Γ M) : ModuleOkB ext (EnvB.ofModule M Γ) M := by
  refine ⟨hM.nodup, fun pre fn post hsplit => ?_⟩
  have ⟨hwf, hcalls, _⟩ := hM.fnsOk pre fn post hsplit
  refine ⟨hwf, hcalls, fun B xs t m Q hspec =>
    wp_env_agree_of_callsOkB (hwf Val (fun _ => Unit) xs (Tup.units fn.as)) hcalls
      (fun _ _ _ hmem _ _ _ _ _ hg => ⟨?_, hg.2⟩) B Q t m (hM.wp_restrict hsplit hspec.2)⟩
  rcases List.mem_append.mp hmem with hp | he
  · exact List.mem_append_left _
      (by rw [hsplit, List.map_append]; exact List.mem_append_left _ hp)
  · exact List.mem_append_right _ he

/-- Boolean checker for `Cmd.callsOk`, kernel-reducible by `rfl`. -/
def Cmd.checkCallsOk (allowed : List SigEntry) : {rs : List Ty} → Cmd (fun _ => Unit) rs → Bool
  | _, .ret _ | _, .hlt => true
  | _, .let_ _ k => (k (Tup.units _)).checkCallsOk allowed
  | _, .load _ _ k => (k ()).checkCallsOk allowed
  | _, .store _ _ k => k.checkCallsOk allowed
  | _, .call f (as := as) (bs := bs) _ k =>
      allowed.any (SigEntry.beq (f, as, bs)) && (k (Tup.units bs)).checkCallsOk allowed
  | _, .interact _ (bs := bs) _ k => (k (Tup.units bs)).checkCallsOk allowed
  | _, .stackalloc _ body => (body ()).checkCallsOk allowed
  | _, .seq (mid := mid) c₁ c₂ =>
      c₁.checkCallsOk allowed && (c₂ (Tup.units mid)).checkCallsOk allowed
  | _, .cond _ t e => t.checkCallsOk allowed && e.checkCallsOk allowed
  | _, .while_ (st := st) _ test body k =>
      (test (Tup.units st)).checkCallsOk allowed &&
      (body (Tup.units st)).checkCallsOk allowed &&
      (k (Tup.units st)).checkCallsOk allowed

theorem Cmd.callsOk_of_checkCallsOk {allowed : List SigEntry} :
    {rs : List Ty} → (c : Cmd (fun _ => Unit) rs) →
    c.checkCallsOk allowed = true → c.callsOk allowed
  | _, .ret _, _ | _, .hlt, _ => trivial
  | _, .let_ _ k, h => Cmd.callsOk_of_checkCallsOk (k (Tup.units _)) h
  | _, .load _ _ k, h => Cmd.callsOk_of_checkCallsOk (k ()) h
  | _, .store _ _ k, h => Cmd.callsOk_of_checkCallsOk k h
  | _, .call f (as := as) (bs := bs) _ k, h => by
      simp only [Cmd.checkCallsOk, Bool.and_eq_true, List.any_eq_true, SigEntry.beq_iff_eq] at h
      rcases h with ⟨⟨s, hs, heq⟩, hk⟩
      exact ⟨heq ▸ hs, Cmd.callsOk_of_checkCallsOk (k (Tup.units bs)) hk⟩
  | _, .interact _ (bs := bs) _ k, h => Cmd.callsOk_of_checkCallsOk (k (Tup.units bs)) h
  | _, .stackalloc _ body, h => Cmd.callsOk_of_checkCallsOk (body ()) h
  | _, .seq (mid := mid) c₁ c₂, h => by
      simp only [Cmd.checkCallsOk, Bool.and_eq_true] at h
      exact ⟨Cmd.callsOk_of_checkCallsOk c₁ h.1,
        Cmd.callsOk_of_checkCallsOk (c₂ (Tup.units mid)) h.2⟩
  | _, .cond _ t e, h => by
      simp only [Cmd.checkCallsOk, Bool.and_eq_true] at h
      exact ⟨Cmd.callsOk_of_checkCallsOk t h.1, Cmd.callsOk_of_checkCallsOk e h.2⟩
  | _, .while_ (st := st) _ test body k, h => by
      simp only [Cmd.checkCallsOk, Bool.and_eq_true] at h
      exact ⟨Cmd.callsOk_of_checkCallsOk (test (Tup.units st)) h.1.1,
        Cmd.callsOk_of_checkCallsOk (body (Tup.units st)) h.1.2,
        Cmd.callsOk_of_checkCallsOk (k (Tup.units st)) h.2⟩

def FnB.checkCallsOk (allowed : List SigEntry) (fn : FnB) : Bool :=
  (fn.body (fun _ => Unit) (Tup.units fn.as)).checkCallsOk allowed

def ModuleB.checkFnsCallsOk (extSigs : List SigEntry) : List SigEntry → List FnB → Bool
  | _, [] => true
  | allowed, fn :: rest =>
      fn.checkCallsOk (allowed ++ extSigs) &&
      ModuleB.checkFnsCallsOk extSigs (allowed ++ [fn.sig]) rest

theorem ModuleB.checkFnsCallsOk_ok (extSigs : List SigEntry) :
    ∀ (seen rest pre : List FnB) (fn : FnB) (post : List FnB),
    ModuleB.checkFnsCallsOk extSigs (seen.map FnB.sig) rest = true →
    rest = pre ++ fn :: post →
    fn.callsOk ((seen ++ pre).map FnB.sig ++ extSigs)
  | _, [], pre, _, _, _, hsplit => by cases pre <;> simp at hsplit
  | seen, f :: rest, [], fn, post, hchk, hsplit => by
      simp only [List.nil_append, List.cons.injEq] at hsplit
      rcases hsplit with ⟨rfl, _⟩
      simp only [ModuleB.checkFnsCallsOk, Bool.and_eq_true] at hchk
      simpa [FnB.callsOk, List.append_nil] using Cmd.callsOk_of_checkCallsOk _ hchk.1
  | seen, f :: rest, f' :: pre', fn, post, hchk, hsplit => by
      simp only [List.cons_append, List.cons.injEq] at hsplit
      rcases hsplit with ⟨rfl, hrest⟩
      simp only [ModuleB.checkFnsCallsOk, Bool.and_eq_true] at hchk
      have hnext := hchk.2
      rw [show seen.map FnB.sig ++ [f.sig] = (seen ++ [f]).map FnB.sig by simp] at hnext
      have ih := ModuleB.checkFnsCallsOk_ok extSigs (seen ++ [f]) rest pre' fn post hnext hrest
      simpa [List.append_assoc] using ih

/-- Acyclicity + `namesNodup` boolean checker for `ModuleB`. -/
def ModuleB.checkAcyclic (M : ModuleB) : Bool :=
  listNodup M.names && ModuleB.checkFnsCallsOk (M.externs.map Extern.sig) [] M.fns

/-- Construct `ModuleOkB` from `M.checkAcyclic = true` plus per-function `Wf` and `wp`. -/
theorem ModuleB.moduleOk_of_checkAcyclic {ext : ExtSpecB} {Γ : EnvB} {M : ModuleB}
    (hcheck : M.checkAcyclic = true)
    (hwf : ∀ fn ∈ M.fns, fn.Wf)
    (hwp : ∀ fn ∈ M.fns, ∀ B xs t m Q,
      Γ fn.name fn.as fn.rs B xs t m Q → FuncB.wp ext Γ fn.body B xs t m Q) :
    ModuleOkB ext Γ M := by
  simp only [ModuleB.checkAcyclic, Bool.and_eq_true] at hcheck
  refine ⟨listNodup_nodup hcheck.1, fun pre fn post hsplit => ?_⟩
  have hmem : fn ∈ M.fns := hsplit ▸ by simp
  refine ⟨hwf fn hmem, ?_, hwp fn hmem⟩
  simpa using ModuleB.checkFnsCallsOk_ok (M.externs.map Extern.sig)
    [] M.fns pre fn post hcheck.2 hsplit

end LeanQbe.T.Bedrock2
