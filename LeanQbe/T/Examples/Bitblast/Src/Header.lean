/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Flat
public import LeanQbe.T.Module
public meta import LeanQbe.T.Frontend.C0.Elab
public meta import Lean.Elab.Tactic
import LeanQbe.T.FlatLemmas

/-!
# Bitblast Shared C0 Internal Header (`Bitblast/Src/Header.lean`)

Single source of truth for the `BVP1` wire format constants, all `32` exact opcode tags matching
`LeanQbe.T.Examples.Bitblast.Ref.BVProg`, the `128`-byte `BVHdr` layout with `_Static_assert`
checks, and the scoped `bitblast_c0!` / `bitblast_wf_reify` elaboration helpers.

Strictly data-pure public interface
(`0` public `*Proof*`/`*Spec*`/`*Lemmas*`/`*Audit*`/`Amd64`/`Arm64`/`Kraken` imports).
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

/-! ## 4. `Func.Wf` Reification Soundness (via `LeanQbe.T.FlatLemmas.Func.wf_of_denote`) -/

public section

/-- A closed function equal to the denotation of its own `toTFlat` reification is well-formed. -/
theorem bitblast_wf_of_reify {as rs : List Ty} {f : Func as rs}
    (h : f = fun V L xs => denote V L (toTFlat (f K KL (Tup.levels as 0)) as.length 0)
      (pushTup xs []) []) : Func.Wf f :=
  Func.wf_of_denote _ h

/-- Prove `Func.Wf f` for a closed concrete function by reification + kernel `rfl`. -/
scoped macro "bitblast_wf_reify" : tactic =>
  `(tactic| (refine bitblast_wf_of_reify ?_; bitblast_kernel_rfl))

end

end LeanQbe.T.Examples.Bitblast.Src
