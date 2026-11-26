/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Flat
public import LeanQbe.T.Module
public meta import LeanQbe.T.Frontend.C0.Elab
public meta import Lean.Elab.Tactic

/-!
# Bitblast Shared C0 Internal Header (`Bitblast/Src/Header.lean`)

Single source of truth for the `BVP1` wire format constants, all `32` exact opcode tags matching
`LeanQbe.T.Examples.Bitblast.Ref.BVProg`, the `128`-byte `BVHdr` layout with `_Static_assert`
checks, and the scoped `bitblast_c0!` / `bitblast_wf_reify` elaboration helpers.

Strictly data-pure (`0` `*Proof*`/`*Spec*`/`*Lemmas*`/`*Audit*`/`Amd64`/`Arm64`/`Kraken` imports).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Src

open LeanQbe.T
open LeanQbe.T.Frontend.C0

@[expose] public section

/-! ## 1. `BVP1` & `BVHdr` Constants -/

/-- `BVP1` wire magic (`"BVP1"` little-endian = `0x31505642`). -/
def bvMagic : Nat := 0x31505642

/-- `BVP1` wire format version (`1`). -/
def bvVersion : Nat := 1

/-- Trivial-SAT sentinel written at `work_base + 0` when root simplifies to constant `1`. -/
def bvTrivialSatMagic : BitVec 64 := 0x4256545249565341#64

/-- Byte size of `BVHdr` (`128` bytes = `16` `u64` words). -/
def bvHdrBytes : Nat := 128

/-- Exclusive DIMACS variable/clause upper bound (`2^28`). -/
def bvDimacsBound : Nat := 268435456

/-! ## 2. Shared C0 Header (`c0_header! "bitblast_internal.h"`) -/

c0_header! "bitblast_internal.h" "
#define BV_MAGIC              0x31505642u
#define BV_VERSION            1u
#define BV_TRIVIAL_SAT_MAGIC  0x4256545249565341ULL
#define BV_HDR_BYTES          128ULL
#define BV_DIMACS_BOUND       268435456ULL
#define BV_MAX_GATES          89478485u

#define BV_OP_VAR             0u
#define BV_OP_CONST           1u
#define BV_OP_EXTRACT         2u
#define BV_OP_AND             3u
#define BV_OP_OR              4u
#define BV_OP_XOR             5u
#define BV_OP_ADD             6u
#define BV_OP_MUL             7u
#define BV_OP_UDIV            8u
#define BV_OP_UMOD            9u
#define BV_OP_NOT             10u
#define BV_OP_ROTL            11u
#define BV_OP_ROTR            12u
#define BV_OP_ASHRC           13u
#define BV_OP_REVERSE         14u
#define BV_OP_CLZ             15u
#define BV_OP_CPOP            16u
#define BV_OP_APPEND          17u
#define BV_OP_REPLICATE       18u
#define BV_OP_SHL             19u
#define BV_OP_USHR            20u
#define BV_OP_ASHR            21u
#define BV_OP_EQ              22u
#define BV_OP_ULT             23u
#define BV_OP_GETLSBD         24u
#define BV_OP_BCONST          25u
#define BV_OP_BNOT            26u
#define BV_OP_GATE_AND        27u
#define BV_OP_GATE_XOR        28u
#define BV_OP_GATE_BEQ        29u
#define BV_OP_GATE_OR         30u
#define BV_OP_ITE             31u

#define BV_VARS_OFF           8ULL
#define BV_CWORDS_OFF(nv)     (8ULL + ((u64)(nv) << 1))
#define BV_NODES_OFF(nv, nc)  (8ULL + ((u64)(nv) << 1) + (u64)(nc))

typedef struct {
  u64 work_base;
  u64 work_end;
  u64 prog_ptr;
  u64 aig_ptr;
  u64 ht_ptr;
  u64 atom_base_ptr;
  u64 slice_off_ptr;
  u64 lits_ptr;
  u64 marks_ptr;
  u64 dimacs_start;
  u32 n_vars;
  u32 n_nodes;
  u32 n_cwords;
  u32 root_node;
  u32 num_atoms;
  u32 aig_len;
  u32 aig_cap;
  u32 ht_mask;
  u32 lits_len;
  u32 lits_cap;
  u32 oom;
  u32 dimacs_len;
} BVHdr;

_Static_assert(sizeof(BVHdr) == 128, \"BVHdr must be 128 bytes\");
_Static_assert(offsetof(BVHdr, work_base) == 0, \"BVHdr.work_base offset\");
_Static_assert(offsetof(BVHdr, work_end) == 8, \"BVHdr.work_end offset\");
_Static_assert(offsetof(BVHdr, prog_ptr) == 16, \"BVHdr.prog_ptr offset\");
_Static_assert(offsetof(BVHdr, aig_ptr) == 24, \"BVHdr.aig_ptr offset\");
_Static_assert(offsetof(BVHdr, ht_ptr) == 32, \"BVHdr.ht_ptr offset\");
_Static_assert(offsetof(BVHdr, atom_base_ptr) == 40, \"BVHdr.atom_base_ptr offset\");
_Static_assert(offsetof(BVHdr, slice_off_ptr) == 48, \"BVHdr.slice_off_ptr offset\");
_Static_assert(offsetof(BVHdr, lits_ptr) == 56, \"BVHdr.lits_ptr offset\");
_Static_assert(offsetof(BVHdr, marks_ptr) == 64, \"BVHdr.marks_ptr offset\");
_Static_assert(offsetof(BVHdr, dimacs_start) == 72, \"BVHdr.dimacs_start offset\");
_Static_assert(offsetof(BVHdr, n_vars) == 80, \"BVHdr.n_vars offset\");
_Static_assert(offsetof(BVHdr, oom) == 120, \"BVHdr.oom offset\");
_Static_assert(offsetof(BVHdr, dimacs_len) == 124, \"BVHdr.dimacs_len offset\");
"

/-! ## 3. Scoped `bitblast_c0!` Elaborator & Kernel `Wf` Tactics -/

meta section
open Lean Elab Command Tactic Meta

/-- Elaborate an acyclic C0 translation unit into `@[expose] public` `<fn>_body`, `<fn>`, and
`<pfx>_fns` declarations (`forceExpose := true`, `emitModule := false`). -/
def elabBitblastC0 (pfx : Name) (src : String) : CommandElabM Unit :=
  elabC0Module (some pfx) src (forceExpose := true) (emitModule := false)

scoped elab "bitblast_c0! " pfx:ident src:str : command =>
  elabBitblastC0 pfx.getId src.getString

/-- Close `lhs = rhs` with `Eq.refl lhs`, checked solely by the Lean kernel (skipping
elaborator `isDefEq` on large PHOAS terms). -/
scoped elab "bitblast_kernel_rfl" : tactic => do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let some (α, lhs, rhs) := tgt.eq?
    | throwError "bitblast_kernel_rfl: goal is not an equality{indentExpr tgt}"
  if lhs.hasExprMVar || rhs.hasExprMVar then
    throwError "bitblast_kernel_rfl: goal still contains metavariables{indentExpr tgt}"
  let u ← getLevel α
  goal.assign (mkApp2 (mkConst ``Eq.refl [u]) α lhs)
  replaceMainGoal []

end

end

/-! ## 4. Self-Contained Data-Pure `Func.Wf` Reification Soundness (`0` `*Lemmas*` Imports) -/

public section

private def ORel {α β : Type} (R : α → β → Prop) : Option α → Option β → Prop
  | none, none => True
  | some a, some b => R a b
  | _, _ => False

private inductive CtxRel {α : Type} {f g : α → Type} (G : Ctx f g) :
    List ((a : α) × f a) → List ((a : α) × g a) → Prop
  | nil : CtxRel G [] []
  | cons {a : α} {x : f a} {y : g a} {vs₁ : List ((b : α) × f b)} {vs₂ : List ((b : α) × g b)} :
      ⟨a, x, y⟩ ∈ G → CtxRel G vs₁ vs₂ → CtxRel G (⟨a, x⟩ :: vs₁) (⟨a, y⟩ :: vs₂)

private theorem CtxRel.mono {α : Type} {f g : α → Type} {G G' : Ctx f g}
    (hsub : ∀ e, e ∈ G → e ∈ G') :
    ∀ {vs₁ vs₂}, CtxRel G vs₁ vs₂ → CtxRel G' vs₁ vs₂
  | _, _, .nil => .nil
  | _, _, .cons hxy hrest => .cons (hsub _ hxy) (hrest.mono hsub)

private theorem ctxRel_pushTup_aux {α : Type} {f g : α → Type} {G' : Ctx f g} :
    {as : List α} → {xs₁ : Tup f as} → {xs₂ : Tup g as} →
    {acc₁ : List ((a : α) × f a)} → {acc₂ : List ((a : α) × g a)} →
    (∀ {a x y}, ⟨a, x, y⟩ ∈ Tup.zip xs₁ xs₂ → ⟨a, x, y⟩ ∈ G') →
    CtxRel G' acc₁ acc₂ →
    CtxRel G' (pushTup xs₁ acc₁) (pushTup xs₂ acc₂)
  | [], (), (), _, _, _, hacc => hacc
  | _ :: _, (_, xs₁), (_, xs₂), _, _, hmem, hacc =>
    ctxRel_pushTup_aux (xs₁ := xs₁) (xs₂ := xs₂)
      (fun hp => hmem (List.mem_cons_of_mem _ hp))
      (.cons (hmem List.mem_cons_self) hacc)

private theorem ctxRel_pushTup {α : Type} {f g : α → Type} {G : Ctx f g} {as : List α}
    (xs₁ : Tup f as) (xs₂ : Tup g as) {vs₁ : List ((a : α) × f a)} {vs₂ : List ((a : α) × g a)}
    (hvs : CtxRel G vs₁ vs₂) :
    CtxRel (Tup.zip xs₁ xs₂ ++ G) (pushTup xs₁ vs₁) (pushTup xs₂ vs₂) :=
  ctxRel_pushTup_aux (fun hp => List.mem_append_left G hp)
    (hvs.mono fun _ hp => List.mem_append_right _ hp)

private theorem listGet?_rel {α : Type} {f g : α → Type} {G : Ctx f g} :
    {vs₁ : List ((a : α) × f a)} → {vs₂ : List ((a : α) × g a)} →
    CtxRel G vs₁ vs₂ → ∀ idx : Nat,
    ORel (fun p q => ∃ a x y, p = ⟨a, x⟩ ∧ q = ⟨a, y⟩ ∧ ⟨a, x, y⟩ ∈ G)
      (listGet? vs₁ idx) (listGet? vs₂ idx)
  | [], [], .nil, idx => by cases idx <;> trivial
  | _ :: _, _ :: _, .cons hxy _, 0 => ⟨_, _, _, rfl, rfl, hxy⟩
  | _ :: _, _ :: _, .cons _ hrest, idx + 1 => listGet?_rel hrest idx

section
variable {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}

private theorem castTy_rel {G : Ctx V₁ V₂} {t' t : Ty} {v₁ : V₁ t'} {v₂ : V₂ t'}
    (h : ⟨t', v₁, v₂⟩ ∈ G) :
    ORel (fun x y => ⟨t, x, y⟩ ∈ G) (castTy t' t v₁) (castTy t' t v₂) := by
  cases t' with
  | bool => cases t <;> first | exact h | trivial
  | bits m =>
    cases t with
    | bits n =>
      dsimp only [castTy]
      split <;> rename_i heq
      · subst heq; exact h
      · trivial
    | _ => trivial
  | float f =>
    cases t with
    | float g =>
      dsimp only [castTy]
      split <;> rename_i heq
      · subst heq; exact h
      · trivial
    | _ => trivial
  | pair a1 b1 =>
    cases t with
    | pair a2 b2 =>
      dsimp only [castTy]
      cases tyDecEq a1 a2 with
      | isFalse _ => trivial
      | isTrue h1 =>
        cases tyDecEq b1 b2 with
        | isFalse _ => trivial
        | isTrue h2 => subst h1; subst h2; exact h
    | _ => trivial

private theorem castListTy_rel {D : Ctx L₁ L₂} {ts' ts : List Ty} {l₁ : L₁ ts'} {l₂ : L₂ ts'}
    (h : ⟨ts', l₁, l₂⟩ ∈ D) :
    ORel (fun x y => ⟨ts, x, y⟩ ∈ D) (castListTy ts' ts l₁) (castListTy ts' ts l₂) := by
  dsimp only [castListTy]
  cases listTyDecEq ts' ts with
  | isTrue heq => subst heq; exact h
  | isFalse _ => trivial

private theorem lookupV_rel {G : Ctx V₁ V₂} {vs₁ vs₂} (hvs : CtxRel G vs₁ vs₂) (t : Ty)
    (idx : Nat) :
    ORel (fun x y => ⟨t, x, y⟩ ∈ G) (lookupV vs₁ t idx) (lookupV vs₂ t idx) := by
  have hg := listGet?_rel hvs idx
  dsimp only [lookupV]
  cases e₁ : listGet? vs₁ idx <;> cases e₂ : listGet? vs₂ idx <;> rw [e₁, e₂] at hg <;>
    dsimp only [ORel] at hg ⊢
  rcases hg with ⟨a, x, y, rfl, rfl, hmem⟩
  exact castTy_rel hmem

private theorem lookupL_rel {D : Ctx L₁ L₂} {ls₁ ls₂} (hls : CtxRel D ls₁ ls₂) (ts : List Ty)
    (idx : Nat) :
    ORel (fun x y => ⟨ts, x, y⟩ ∈ D) (lookupL ls₁ ts idx) (lookupL ls₂ ts idx) := by
  have hg := listGet?_rel hls idx
  dsimp only [lookupL]
  cases e₁ : listGet? ls₁ idx <;> cases e₂ : listGet? ls₂ idx <;> rw [e₁, e₂] at hg <;>
    dsimp only [ORel] at hg ⊢
  rcases hg with ⟨a, x, y, rfl, rfl, hmem⟩
  exact castListTy_rel hmem

private theorem denoteArg_rel {G : Ctx V₁ V₂} {vs₁ vs₂} (hvs : CtxRel G vs₁ vs₂) {t : Ty}
    (a : Arg K t) :
    ORel (ArgRel G t) (denoteArg vs₁ a) (denoteArg vs₂ a) := by
  cases a with
  | var idx =>
    have hl := lookupV_rel hvs t idx
    dsimp only [denoteArg]
    cases e₁ : lookupV vs₁ t idx <;> cases e₂ : lookupV vs₂ t idx <;> rw [e₁, e₂] at hl <;>
      dsimp only [ORel] at hl ⊢
    exact .var hl
  | imm c => exact .imm c

private theorem denoteArgs_rel {G : Ctx V₁ V₂} {vs₁ vs₂} (hvs : CtxRel G vs₁ vs₂) :
    {ts : List Ty} → (as : Tup (Arg K) ts) →
    ORel (TRel (ArgRel G)) (denoteArgs vs₁ as) (denoteArgs vs₂ as)
  | [], () => .nil
  | _ :: _, (a, as) => by
    have ha := denoteArg_rel hvs a
    have has := denoteArgs_rel hvs as
    dsimp only [denoteArgs]
    cases e₁ : denoteArg vs₁ a <;> cases e₂ : denoteArg vs₂ a <;> rw [e₁, e₂] at ha <;>
      dsimp only [ORel] at ha ⊢ <;>
      cases f₁ : denoteArgs vs₁ as <;> cases f₂ : denoteArgs vs₂ as <;> rw [f₁, f₂] at has <;>
      dsimp only [ORel] at has ⊢
    exact .cons ha has

end

mutual
private theorem denote_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    (tf : TFlat rs) → {G : Ctx V₁ V₂} → {D : Ctx L₁ L₂} →
    {vs₁ : List ((t : Ty) × V₁ t)} → {vs₂ : List ((t : Ty) × V₂ t)} →
    {ls₁ : List ((ts : List Ty) × L₁ ts)} → {ls₂ : List ((ts : List Ty) × L₂ ts)} →
    CtxRel G vs₁ vs₂ → CtxRel D ls₁ ls₂ →
    Wf G D (denote V₁ L₁ tf vs₁ ls₁) (denote V₂ L₂ tf vs₂ ls₂)
  | .let_ op k, _, _, vs₁, vs₂, ls₁, ls₂, hvs, hls => by
    have hr := denoteArgs_rel hvs op.args
    dsimp only [denote]
    cases e₁ : denoteArgs vs₁ op.args <;> cases e₂ : denoteArgs vs₂ op.args <;>
      rw [e₁, e₂] at hr <;> dsimp only [ORel] at hr ⊢
    · exact .hlt
    · exact .let_ (.mk op.code hr) fun xs₁ xs₂ =>
        denote_wf k (ctxRel_pushTup xs₁ xs₂ hvs) hls
  | .load t a k, _, _, vs₁, vs₂, ls₁, ls₂, hvs, hls => by
    have hr := denoteArg_rel hvs a
    dsimp only [denote]
    cases e₁ : denoteArg vs₁ a <;> cases e₂ : denoteArg vs₂ a <;>
      rw [e₁, e₂] at hr <;> dsimp only [ORel] at hr ⊢
    · exact .hlt
    · exact .load t hr fun v₁ v₂ =>
        denote_wf k (.cons List.mem_cons_self (hvs.mono fun _ hp => List.mem_cons_of_mem _ hp)) hls
  | .store v a k, _, _, vs₁, vs₂, ls₁, ls₂, hvs, hls => by
    have hv := denoteArg_rel hvs v
    have ha := denoteArg_rel hvs a
    dsimp only [denote]
    cases e₁ : denoteArg vs₁ v <;> cases e₂ : denoteArg vs₂ v <;> rw [e₁, e₂] at hv <;>
      dsimp only [ORel] at hv ⊢ <;>
      cases f₁ : denoteArg vs₁ a <;> cases f₂ : denoteArg vs₂ a <;> rw [f₁, f₂] at ha <;>
      dsimp only [ORel] at ha ⊢ <;>
      first | exact .hlt | exact .store hv ha (denote_wf k hvs hls)
  | .call f _ args k, _, _, vs₁, vs₂, ls₁, ls₂, hvs, hls => by
    have hr := denoteArgs_rel hvs args
    dsimp only [denote]
    cases e₁ : denoteArgs vs₁ args <;> cases e₂ : denoteArgs vs₂ args <;>
      rw [e₁, e₂] at hr <;> dsimp only [ORel] at hr ⊢
    · exact .hlt
    · exact .call f hr fun xs₁ xs₂ =>
        denote_wf k (ctxRel_pushTup xs₁ xs₂ hvs) hls
  | .jnz c t e, _, _, vs₁, vs₂, ls₁, ls₂, hvs, hls => by
    have hr := denoteArg_rel hvs c
    dsimp only [denote]
    cases e₁ : denoteArg vs₁ c <;> cases e₂ : denoteArg vs₂ c <;>
      rw [e₁, e₂] at hr <;> dsimp only [ORel] at hr ⊢
    · exact .hlt
    · exact .jnz hr (denote_wf t hvs hls) (denote_wf e hvs hls)
  | .jump (ts := ts) j args, _, _, vs₁, vs₂, ls₁, ls₂, hvs, hls => by
    have hj := lookupL_rel hls ts j
    have hr := denoteArgs_rel hvs args
    dsimp only [denote]
    cases e₁ : lookupL ls₁ ts j <;> cases e₂ : lookupL ls₂ ts j <;> rw [e₁, e₂] at hj <;>
      dsimp only [ORel] at hj ⊢ <;>
      cases f₁ : denoteArgs vs₁ args <;> cases f₂ : denoteArgs vs₂ args <;> rw [f₁, f₂] at hr <;>
      dsimp only [ORel] at hr ⊢ <;>
      first | exact .hlt | exact .jump hj hr
  | .ret vs, _, _, vs₁, vs₂, _, _, hvs, _ => by
    have hr := denoteArgs_rel hvs vs
    dsimp only [denote]
    cases e₁ : denoteArgs vs₁ vs <;> cases e₂ : denoteArgs vs₂ vs <;>
      rw [e₁, e₂] at hr <;> dsimp only [ORel] at hr ⊢
    · exact .hlt
    · exact .ret hr
  | .exit f args, _, _, vs₁, vs₂, _, _, hvs, _ => by
    have hr := denoteArgs_rel hvs args
    dsimp only [denote]
    cases e₁ : denoteArgs vs₁ args <;> cases e₂ : denoteArgs vs₂ args <;>
      rw [e₁, e₂] at hr <;> dsimp only [ORel] at hr ⊢
    · exact .hlt
    · exact .exit f hr
  | .hlt, _, _, _, _, _, _, _, _ => .hlt
  | .group bodies k, _, _, _, _, _, _, hvs, hls =>
    .group
      (fun Js₁ Js₂ => denoteB_wf bodies hvs (ctxRel_pushTup Js₁ Js₂ hls))
      (fun Js₁ Js₂ => denote_wf k hvs (ctxRel_pushTup Js₁ Js₂ hls))

private theorem denoteB_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) → {G : Ctx V₁ V₂} → {D : Ctx L₁ L₂} →
    {vs₁ : List ((t : Ty) × V₁ t)} → {vs₂ : List ((t : Ty) × V₂ t)} →
    {ls₁ : List ((ts : List Ty) × L₁ ts)} → {ls₂ : List ((ts : List Ty) × L₂ ts)} →
    CtxRel G vs₁ vs₂ → CtxRel D ls₁ ls₂ →
    WfB G D (denoteB V₁ L₁ tb vs₁ ls₁) (denoteB V₂ L₂ tb vs₂ ls₂)
  | _, .nil, _, _, _, _, _, _, _, _ => .nil
  | _, .cons b bs, _, _, _, _, _, _, hvs, hls =>
    .cons (fun xs₁ xs₂ => denote_wf b (ctxRel_pushTup xs₁ xs₂ hvs) hls) (denoteB_wf bs hvs hls)
end

/-- A closed function equal to the denotation of its own `toTFlat` reification is well-formed. -/
theorem bitblast_wf_of_reify {as rs : List Ty} {f : Func as rs}
    (h : f = fun V L xs => denote V L (toTFlat (f K KL (Tup.levels as 0)) as.length 0)
      (pushTup xs []) []) : Func.Wf f := by
  intro V₁ V₂ L₁ L₂ xs₁ xs₂
  let tf := toTFlat (f K KL (Tup.levels as 0)) as.length 0
  have h₁ : f V₁ L₁ xs₁ = denote V₁ L₁ tf (pushTup xs₁ []) [] :=
    congrFun (congrFun (congrFun h V₁) L₁) xs₁
  have h₂ : f V₂ L₂ xs₂ = denote V₂ L₂ tf (pushTup xs₂ []) [] :=
    congrFun (congrFun (congrFun h V₂) L₂) xs₂
  rw [h₁, h₂]
  exact denote_wf tf
    ((ctxRel_pushTup xs₁ xs₂ (.nil (G := []))).mono fun _ hp => by simpa using hp) .nil

/-- Prove `Func.Wf f` for a closed concrete function by reification + kernel `rfl`. -/
scoped macro "bitblast_wf_reify" : tactic =>
  `(tactic| (refine bitblast_wf_of_reify ?_; bitblast_kernel_rfl))

end

end LeanQbe.T.Examples.Bitblast.Src
