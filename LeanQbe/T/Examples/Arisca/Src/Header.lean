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
# ARiSCA C0 Internal Header & Core Arithmetic (`Arisca/Src/Header.lean`)

Defines:
- `ART` v1 constants (`AR_NONE`, `AR_ART_MAGIC`, `AR_W_RATIO`, `AR_TT_MAX_AND`, `AR_TT_STK`,
  `AR_R_MAXF`, `AR_ACCEPT`, `AR_REJECT`)
- `ArCtx` workspace header/context struct placed at the aligned base of `work_ptr`, with
  `_Static_assert` layout verification
- Scoped `arisca_c0!`, `arisca_kernel_rfl`, and `arisca_wf_reify` elaboration helpers
- Core 128-bit masked modular arithmetic (`u64_mul128` via pure 4×`32×32->64` `u64` ops,
  `ar_cmul`, `ar_cadd`, `ar_csub`, `ar_cneg`, `ar_cfrom_small`, `ar_cpow2`), ART word cursor
  (`ar_rd32`, `ar_next_word`), and bounds-checked bump allocator (`ar_aalloc`).

Strictly data-pure public interface
(`0` public `*Proof*`/`*Spec*`/`*Lemmas*`/`*Audit*`/`Amd64`/`Arm64`/`Kraken` imports).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Arisca.Src

open LeanQbe.T
open LeanQbe.T.Frontend.C0

@[expose] public section

/-! ## 1. Shared C0 Header (`c0_header! "arisca_internal.h"`) -/

c0_header! "arisca_internal.h" "
#define AR_NONE       0xFFFFFFFFu
#define AR_ART_MAGIC  0x31545241u
#define AR_W_RATIO    12ULL
#define AR_TT_MAX_AND 64u
#define AR_TT_STK     160u
#define AR_R_MAXF     24u
#define AR_ACCEPT     20ULL
#define AR_REJECT     0ULL

typedef C0_RET2(bool, u32) ar_bool_u32;
typedef C0_RET2(bool, u64) ar_bool_u64;
typedef C0_RET2(u64, u64) ar_u64_u64;
typedef C0_RET3(bool, u64, u32) ar_bool_u64_u32;

typedef struct {
  u8 *w;
  u64 wlen;
  u64 top;
  u64 mlo;
  u64 mhi;
  u32 *rhs0;
  u32 *rhs1;
  u32 *olit;
  u8 *art;
  u64 nw;
  u64 pos;
  u32 *bind;
  u32 *in_net;
  u32 *out_ref;
  u32 *rule_off;
  u32 *rule_n;
  u32 *partner;
  u8 *flipped;
  u32 *stk_n;
  u32 *stk_p;
  u32 *memo_n;
  u64 *memo_v;
  u64 *dense;
  u32 *gsy;
  u64 *gcl;
  u64 *gch;
  u64 g_lmask[6];
  u64 g_tin[3];
  u64 g_tto[2];
  u32 *rs_m;
  u64 *rs_l;
  u64 *rs_h;
  u32 *rs_pool;
  u64 rs_ptop;
  u64 rs_pcap;
  u32 *tm[2];
  u64 *ts[2];
  u64 *tl[2];
  u64 *th[2];
  u32 *pool[2];
  u64 ptop;
  u64 pcap;
  u32 *qm;
  u64 *qs;
  u64 *ql;
  u64 *qh;
  u32 *ix;
  u32 *ix2;
  u32 *bx;
  u32 *vq_off;
  u32 *vq;
  u8 *vq_skip;
  u32 *rm;
  u32 *rm2;
  u64 *rl;
  u64 *rh;
  u64 *rl2;
  u64 *rh2;
  u32 *rpool;
  u64 rpcap;
  u32 *cur_rm;
  u64 *cur_rl;
  u64 *cur_rh;
  u32 *cur_rp;
  u32 n_out;
  u32 M;
  u32 I;
  u32 A;
  u32 O;
  u32 spec;
  u32 n_in;
  u32 n_nets;
  u32 n_gates;
  u32 n_cones;
  u32 n_main;
  u32 rs_n;
  u32 rs_cap;
  u32 tc;
  u32 tn;
  u32 tcap;
  u32 pc;
  u32 qn;
  u32 qcap;
  u32 rcap;
  u32 cur_nr;
  u32 g_outs[2];
  u32 g_innet[3];
  u32 g_inneg[3];
  u32 g_lnode[6];
  u32 g_vs[4];
  u32 pad_end;
} ArCtx;

_Static_assert(sizeof(ArCtx) == 776, \"ArCtx must be 776 bytes\");
_Static_assert(offsetof(ArCtx, w) == 0, \"ArCtx.w offset\");
_Static_assert(offsetof(ArCtx, g_lmask) == 208, \"ArCtx.g_lmask offset\");
_Static_assert(offsetof(ArCtx, rs_m) == 296, \"ArCtx.rs_m offset\");
_Static_assert(offsetof(ArCtx, tm) == 344, \"ArCtx.tm offset\");
_Static_assert(offsetof(ArCtx, cur_rp) == 608, \"ArCtx.cur_rp offset\");
_Static_assert(offsetof(ArCtx, n_out) == 616, \"ArCtx.n_out offset\");
_Static_assert(offsetof(ArCtx, pad_end) == 772, \"ArCtx.pad_end offset\");
"

/-! ## 2. Scoped `arisca_c0!` Elaborator & Kernel `Wf` Tactics -/

meta section
open Lean Elab Command Tactic Meta

/-- Elaborate an acyclic C0 translation unit into `@[expose] public` `<fn>_body`, `<fn>`, and
`<pfx>_fns` declarations (`forceExpose := true`, `emitModule := false`). -/
def elabAriscaC0 (pfx : Name) (src : String) : CommandElabM Unit :=
  elabC0Module (some pfx) src (forceExpose := true) (emitModule := false)

scoped elab "arisca_c0! " pfx:ident src:str : command =>
  elabAriscaC0 pfx.getId src.getString

/-- Close `lhs = rhs` with `Eq.refl lhs`, checked solely by the Lean kernel. -/
scoped elab "arisca_kernel_rfl" : tactic => do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let some (α, lhs, rhs) := tgt.eq?
    | throwError "arisca_kernel_rfl: goal is not an equality{indentExpr tgt}"
  if lhs.hasExprMVar || rhs.hasExprMVar then
    throwError "arisca_kernel_rfl: goal still contains metavariables{indentExpr tgt}"
  let u ← getLevel α
  goal.assign (mkApp2 (mkConst ``Eq.refl [u]) α lhs)
  replaceMainGoal []

end

end

/-! ## 3. `Func.Wf` Reification Soundness (via `LeanQbe.T.FlatLemmas.Func.wf_of_denote`) -/

public section

/-- A closed function equal to the denotation of its own `toTFlat` reification is well-formed. -/
theorem arisca_wf_of_reify {as rs : List Ty} {f : Func as rs}
    (h : f = fun V L xs => denote V L (toTFlat (f K KL (Tup.levels as 0)) as.length 0)
      (pushTup xs []) []) : Func.Wf f :=
  Func.wf_of_denote _ h

/-- Prove `Func.Wf f` for a closed concrete function by reification + kernel `rfl`. -/
scoped macro "arisca_wf_reify" : tactic =>
  `(tactic| (refine arisca_wf_of_reify ?_; arisca_kernel_rfl))

end

/-! ## 4. Core Header Utilities, Bump Allocator, & 128-bit Arithmetic -/

namespace Header

open LeanQbe.T
open LeanQbe.T.Examples.Arisca.Src

@[expose] public section

arisca_c0! arisca_hdr "
#include \"arisca_internal.h\"

u32 ar_rd32(const u8 *p) {
  u32 b0 = (u32)p[0];
  u32 b1 = (u32)p[1];
  u32 b2 = (u32)p[2];
  u32 b3 = (u32)p[3];
  return b0 | (b1 << 8) | (b2 << 16) | (b3 << 24);
}

ar_bool_u32 ar_next_word(ArCtx *cx) {
  if (cx->pos >= cx->nw) {
    return C0_TUP2(ar_bool_u32, false, 0u);
  }
  u32 v = ar_rd32(cx->art + 4ULL * cx->pos);
  cx->pos = cx->pos + 1ULL;
  return C0_TUP2(ar_bool_u32, true, v);
}

u8 *ar_aalloc(ArCtx *cx, u64 bytes) {
  if (cx->top > cx->wlen) { return NULL; }
  u64 rem0 = cx->wlen - cx->top;
  u64 pad = (8ULL - (cx->top & 7ULL)) & 7ULL;
  if (pad > rem0) { return NULL; }
  u64 t = cx->top + pad;
  if (bytes > cx->wlen - t) { return NULL; }
  cx->top = t + bytes;
  return cx->w + t;
}

ar_u64_u64 u64_mul128(u64 a, u64 b) {
  u64 a0 = a & 0xFFFFFFFFULL;
  u64 a1 = a >> 32;
  u64 b0 = b & 0xFFFFFFFFULL;
  u64 b1 = b >> 32;
  u64 p00 = a0 * b0;
  u64 p01 = a0 * b1;
  u64 p10 = a1 * b0;
  u64 p11 = a1 * b1;
  u64 mid = (p00 >> 32) + (p01 & 0xFFFFFFFFULL) + (p10 & 0xFFFFFFFFULL);
  u64 lo = (p00 & 0xFFFFFFFFULL) | (mid << 32);
  u64 hi = p11 + (p01 >> 32) + (p10 >> 32) + (mid >> 32);
  return C0_TUP2(ar_u64_u64, lo, hi);
}

ar_u64_u64 ar_cmul(ArCtx *cx, u64 al, u64 ah, u64 bl, u64 bh) {
  u64 l = 0ULL;
  u64 h = 0ULL;
  C0_TIE2(l, h, u64_mul128(al, bl));
  h = h + al * bh + ah * bl;
  return C0_TUP2(ar_u64_u64, l & cx->mlo, h & cx->mhi);
}

ar_u64_u64 ar_cadd(ArCtx *cx, u64 al, u64 ah, u64 bl, u64 bh) {
  u64 l = al + bl;
  u64 c = (l < al) ? 1ULL : 0ULL;
  u64 h = ah + bh + c;
  return C0_TUP2(ar_u64_u64, l & cx->mlo, h & cx->mhi);
}

ar_u64_u64 ar_csub(ArCtx *cx, u64 al, u64 ah, u64 bl, u64 bh) {
  u64 l = al - bl;
  u64 b = (al < bl) ? 1ULL : 0ULL;
  u64 h = ah - bh - b;
  return C0_TUP2(ar_u64_u64, l & cx->mlo, h & cx->mhi);
}

ar_u64_u64 ar_cneg(ArCtx *cx, u64 al, u64 ah) {
  u64 l = (~al) + 1ULL;
  u64 c = (l == 0ULL) ? 1ULL : 0ULL;
  u64 h = (~ah) + c;
  return C0_TUP2(ar_u64_u64, l & cx->mlo, h & cx->mhi);
}

ar_u64_u64 ar_cfrom_small(ArCtx *cx, u64 v) {
  u64 hi = ((v >> 63) != 0ULL) ? (~0ULL) : 0ULL;
  return C0_TUP2(ar_u64_u64, v & cx->mlo, hi & cx->mhi);
}

ar_u64_u64 ar_cpow2(ArCtx *cx, u32 e) {
  u64 l = 0ULL;
  u64 h = 0ULL;
  if (e < 64u) {
    l = 1ULL << e;
  } else if (e < 128u) {
    h = 1ULL << (e - 64u);
  }
  return C0_TUP2(ar_u64_u64, l & cx->mlo, h & cx->mhi);
}
"

/-- Ordered live functions of `Arisca/Src/Header.lean` (`10` fns). -/
def fns : List Fn := arisca_hdr_fns

end

public section

theorem ar_rd32_wf : Func.Wf ar_rd32_body := by arisca_wf_reify
theorem ar_next_word_wf : Func.Wf ar_next_word_body := by arisca_wf_reify
theorem ar_aalloc_wf : Func.Wf ar_aalloc_body := by arisca_wf_reify
theorem u64_mul128_wf : Func.Wf u64_mul128_body := by arisca_wf_reify
theorem ar_cmul_wf : Func.Wf ar_cmul_body := by arisca_wf_reify
theorem ar_cadd_wf : Func.Wf ar_cadd_body := by arisca_wf_reify
theorem ar_csub_wf : Func.Wf ar_csub_body := by arisca_wf_reify
theorem ar_cneg_wf : Func.Wf ar_cneg_body := by arisca_wf_reify
theorem ar_cfrom_small_wf : Func.Wf ar_cfrom_small_body := by arisca_wf_reify
theorem ar_cpow2_wf : Func.Wf ar_cpow2_body := by arisca_wf_reify

theorem fns_wf : ∀ f ∈ fns, f.Wf := by
  intro f hf
  simp only [fns, arisca_hdr_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ar_rd32_wf
  · exact ar_next_word_wf
  · exact ar_aalloc_wf
  · exact u64_mul128_wf
  · exact ar_cmul_wf
  · exact ar_cadd_wf
  · exact ar_csub_wf
  · exact ar_cneg_wf
  · exact ar_cfrom_small_wf
  · exact ar_cpow2_wf

end

end Header

end LeanQbe.T.Examples.Arisca.Src
