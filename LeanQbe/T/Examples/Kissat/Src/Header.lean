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
# Kissat Shared C0 Internal Header (`Src/Header.lean`)

Single source of truth for the Kissat C0 struct layouts (`KissatDimacs`, `FullHdr`, `M6HdrExt`,
`FullM6Hdr`), compile-time `_Static_assert` layout checks, and all unanimous `#define` constants
shared across the `40` flat upstream-mirrored `Src/*.lean` files via
`c0_header! "kissat_internal.h"` and `#include "kissat_internal.h"`.

* Mirrors upstream `kissat/src/internal.h` + `kissat/src/kissat.h`.
* Strictly data-pure (`0` `*Proof*`/`*Spec*`/`*Lemmas*`/`*Audit*`/`Amd64`/`Arm64`/`Kraken`
  imports).
* Note on `KM_CORE`: the sole pass-local macro conflict (`0x20000000u` in `full_k6_core_m7` /
  `full_bve_def_k6_m7` vs `0x80000000u` in `full_k6_core_fid` / `full_k6_extract_and_solve_fid`)
  is intentionally excluded here and kept pass-local (`KM_CORE_M7` vs `KM_CORE_FID`) in
  `Src/Definition.lean` so every compiled `T` `Func` AST stays bit-for-bit identical.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src

open LeanQbe.T
open LeanQbe.T.Frontend.C0

@[expose] public section

/-! ## 1. `FullM6Hdr` & `M6HdrExt` Layout Constants (`432` Words = `3,456 B`) -/

/-- Frozen base `FullHdr` word count (`144` `u64` words). -/
def fullM6HdrBaseWords : Nat := 144

/-- Frozen base `FullHdr` byte size (`144 * 8 = 1,152` bytes). -/
def fullM6HdrBaseBytes : Nat := 1152

/-- Extended `M6HdrExt` `u64` word count (`288` `u64` words = `32` control + `256` glue bins). -/
def fullM6ExtWords : Nat := 288

/-- Extended `M6HdrExt` byte size (`288 * 8 = 2,304` bytes). -/
def fullM6ExtBytes : Nat := 2304

/-- Total unified `FullM6Hdr` word count (`288 + 144 = 432` `u64` words). -/
def fullM6HdrTotalWords : Nat := 432

/-- Total unified `FullM6Hdr` byte size (`2304 + 1152 = 3,456` bytes). -/
def fullM6HdrTotalBytes : Nat := 3456

/-- Initialization magic stored at `M6HdrExt` word `0` (`"M6HDREX1"`). -/
def fullM6HdrMagic : BitVec 64 := 0x4D36484452455831#64

/-- Number of glue histogram bins per mode (`0..127`). -/
def fullM6HdrGlueBins : Nat := 128

/-- Word index `0`: `m6_magic` (byte offset `+0`). -/
def m6WMagic : Nat := 0
/-- Word index `1`: `dr_state` `[bit63 | last_sw(7b) | decs(56b)]` (byte offset `+8`). -/
def m6WDrState : Nat := 1
/-- Word indices `2..3`: `dr_prev[2]` (byte offsets `+16`, `+24`). -/
def m6WDrPrev : Nat := 2
/-- Word indices `4..5`: `dr_sb[2]` Q32 EMA biased (byte offsets `+32`, `+40`). -/
def m6WDrSb : Nat := 4
/-- Word indices `6..7`: `dr_se[2]` Q32 EMA exp (byte offsets `+48`, `+56`). -/
def m6WDrSe : Nat := 6
/-- Word indices `8..9`: `tier1[2]` (byte offsets `+64`, `+72`). -/
def m6WTier1 : Nat := 8
/-- Word indices `10..11`: `tier2[2]` (byte offsets `+80`, `+88`). -/
def m6WTier2 : Nat := 10
/-- Word index `12`: `glue_next_confl` (byte offset `+96`). -/
def m6WGlueNext : Nat := 12
/-- Word index `13`: `glue_interval` (byte offset `+104`). -/
def m6WGlueInterval : Nat := 13
/-- Word indices `14..15`: `total_used[2]` (byte offsets `+112`, `+120`). -/
def m6WTotalUsed : Nat := 14
/-- Word indices `16..19`: `delay_cnt[4]` (byte offsets `+128..+152`). -/
def m6WDelayCnt : Nat := 16
/-- Word indices `20..23`: `delay_cur[4]` (byte offsets `+160..+184`). -/
def m6WDelayCur : Nat := 20
/-- Word indices `24..31`: `watermarks[8]` (byte offsets `+192..+248`). -/
def m6WWmBase : Nat := 24
/-- Word indices `32..159`: `used_0[128]` focused glue bins (byte offsets `+256..+1272`). -/
def m6WUsed0 : Nat := 32
/-- Word indices `160..287`: `used_1[128]` stable glue bins (byte offsets `+1280..+2296`). -/
def m6WUsed1 : Nat := 160

/-- Byte offsets inside `M6HdrExt` (relative to `(u64)h - 2304ULL`). -/
def m6HdrOffMagic : Nat := 8 * m6WMagic
def m6HdrOffDrState : Nat := 8 * m6WDrState
def m6HdrOffDrPrev : Nat := 8 * m6WDrPrev
def m6HdrOffDrSb : Nat := 8 * m6WDrSb
def m6HdrOffDrSe : Nat := 8 * m6WDrSe
def m6HdrOffTier1 : Nat := 8 * m6WTier1
def m6HdrOffTier2 : Nat := 8 * m6WTier2
def m6HdrOffGlueNext : Nat := 8 * m6WGlueNext
def m6HdrOffGlueInterval : Nat := 8 * m6WGlueInterval
def m6HdrOffTotalUsed : Nat := 8 * m6WTotalUsed
def m6HdrOffDelayCnt : Nat := 8 * m6WDelayCnt
def m6HdrOffDelayCur : Nat := 8 * m6WDelayCur
def m6HdrOffWmBase : Nat := 8 * m6WWmBase
def m6HdrOffUsed0 : Nat := 8 * m6WUsed0
def m6HdrOffUsed1 : Nat := 8 * m6WUsed1

/-! ## 2. Shared C0 Header (`c0_header! "kissat_internal.h"`) -/

c0_header! "kissat_internal.h" "
typedef struct {
  u64 mv, nc, cur, val;
} KissatDimacs;

typedef struct {
  KissatDimacs d;
  u64 arena_cap, wcap, arena_len, wlen;
  u64 values, mark, level, reason, trail;
  u64 watch_vec, arena, watch_stk, delayed, tmp_lits;
  u64 trail_end, propagated, cur_level, fuel, confl_ref;
  u64 tmp_cnt, tmp_len, heap, pos, score;
  u64 phases, min_stk, min_clr, heap_len, scinc;
  u64 min_depth, min_clr_len, min_clr_full, rel_period, rel_limit;
  u64 rel_wait, rel_u, rel_v, rel_trigger, conflicts;
  u64 learned_lits, min_removed, trail_pos, q_prev, q_next;
  u64 q_stamp, phases_target, phases_best, wsort, shrink_stk;
  u64 red_refs, glue_used, red_cap, delayed_cap, delayed_len;
  u64 wusable, arena_garbage, first_reducible, num_irred, num_redundant;
  u64 num_binary, unflushed, probing, confl_type, confl_lit0;
  u64 confl_lit1, stable, switched, mode_count, mode_confl_lim;
  u64 mode_tick_lim, mode_saved_ticks, search_ticks, q_first, q_last;
  u64 q_search_idx, q_search_stamp, q_cur_stamp, target_assigned, best_assigned;
  u64 rephase_limit, rephased, reduce_limit, reductions, tier1;
  u64 tier2, restarts, restart_limit, ema_fast_biased, ema_fast_exp;
  u64 ema_slow_biased, ema_slow_exp, oom;
  u64 max_vars, cur_vars, bva_cap, unassigned;
  u64 flags, lit_mark, repr, sim_sig;
  u64 frame_trail, frame_dec, work_stk1, work_stk2;
  u64 tarjan_mark, tarjan_reach, walk_vals, walk_best;
  u64 extend_stk, extend_cap, extend_len;
  u64 scratch_buf, scratch_cap, last_learned;
  u64 rng_state, chrono_levels, otfs_cnt, eager_sub_cnt;
  u64 probe_limit, probings, elim_limit, eliminations;
  u64 elim_bound, dense_mode, inconsistent, iterating;
  u64 hbr_cnt, trans_cnt, viv_cnt, subst_cnt;
  u64 cong_cnt, sweep_cnt, bve_cnt, bce_cnt;
  u64 bva_cnt, walk_cnt_stat, fwd_sub_cnt, fwd_str_cnt;
  u64 ant_sz, res_sz;
} FullHdr;

typedef struct {
  u64 m6_magic;
  u64 dr_state;
  u64 dr_prev[2];
  u64 dr_sb[2];
  u64 dr_se[2];
  u64 tier1[2];
  u64 tier2[2];
  u64 glue_next_confl;
  u64 glue_interval;
  u64 total_used[2];
  u64 delay_cnt[4];
  u64 delay_cur[4];
  u64 watermarks[8];
  u64 used_0[128];
  u64 used_1[128];
} M6HdrExt;

typedef struct {
  M6HdrExt ext;
  FullHdr base;
} FullM6Hdr;

_Static_assert(sizeof(KissatDimacs) == 32, \"KissatDimacs must be 32 bytes\");
_Static_assert(sizeof(FullHdr) == 1152, \"FullHdr must be 1152 bytes\");
_Static_assert(sizeof(M6HdrExt) == 2304, \"M6HdrExt must be 2304 bytes\");
_Static_assert(sizeof(FullM6Hdr) == 3456, \"FullM6Hdr must be 3456 bytes\");
_Static_assert(offsetof(FullM6Hdr, ext) == 0, \"FullM6Hdr.ext offset must be 0\");
_Static_assert(offsetof(FullM6Hdr, base) == 2304, \"FullM6Hdr.base offset must be 2304\");
_Static_assert(offsetof(FullHdr, d.val) == 24, \"FullHdr.d.val offset must be 24\");
_Static_assert(offsetof(FullHdr, res_sz) == 1144, \"FullHdr.res_sz offset must be 1144\");

#define PH_GLUE_MASK          0x7FFFFu
#define PH_GARB               0x00080000u
#define PH_VIV                0x00100000u
#define PH_RSN                0x00200000u
#define PH_RED                0x00400000u
#define PH_SHRK               0x00800000u
#define PH_SUBSUME            0x01000000u
#define PH_BVA_Q              0x02000000u
#define PW_BIN_FLAG           0x80000000u
#define PW_LIT_MASK           0x7FFFFFFFu

#define FL_ACTIVE             1u
#define FL_ELIM               2u
#define FL_SUBST              4u
#define FL_SUBSUME            8u
#define FL_ELIM_C             16u
#define FL_FACT_P             32u
#define FL_FACT_N             64u
#define FL_BONE0              128u
#define FL_BONE1              256u
#define FL_TRANS              512u
#define FL_SWEEP              1024u
#define FL_SWEEP_INR          0x20000000u
#define FL_SWEEP_INC          0x40000000u

#define EXT_BLK_FLAG          0x80000000u
#define EXT_COMPACT_FLAG      0x40000000u
#define EXT_CNT_MASK          0x3FFFFFFFu
#define EXT_PERM_FLAG         0x20000000u
#define EXT_PERM_MASK         0x1FFFFFFFu
#define EXT_UNMAPPED          0x7FFFFFFFu

#define M6_EXT_WORDS          288ULL
#define M6_EXT_BYTES          2304ULL
#define M6_HDR_TOTAL_BYTES    3456ULL
#define M6_HDR_MAGIC          0x4D36484452455831ULL

#define M6W_MAGIC             0ULL
#define M6W_DR_STATE          1ULL
#define M6W_DR_PREV           2ULL
#define M6W_DR_SB             4ULL
#define M6W_DR_SE             6ULL
#define M6W_TIER1             8ULL
#define M6W_TIER2             10ULL
#define M6W_GLUE_NEXT         12ULL
#define M6W_GLUE_INTV         13ULL
#define M6W_TOTAL_USED        14ULL
#define M6W_DELAY_CNT         16ULL
#define M6W_DELAY_CUR         20ULL
#define M6W_WM_BASE           24ULL
#define M6W_USED0             32ULL
#define M6W_USED1             160ULL

#define M6_GLUE_BINS          128ULL
#define M6_GLUE_INTERVAL_MAX  65536ULL
#define M6_DELAY_CONGRUENCE   1ULL
#define M6_DELAY_SWEEP        2ULL
#define M6_DELAY_VIVIFYIRR    3ULL
#define M6_WM_PROBE_TICKS     0ULL
#define M6_WM_REDUCE_CONFL    2ULL
#define M6_WM_REDUCE_TICKS    3ULL
#define M6_WM_PROBING_TICKS   5ULL
#define M6_WM_FOCUSED_TICKS   6ULL
#define M6_WM_STABLE_TICKS    7ULL

#define SWP_GU_COMPLETED      28u
#define SWP_GU_INCOMPLETE     29u
#define SWP_GU_CURSOR         30u
#define TUM_GU_ACTIVATED      31ULL
#define SWP_GU_SWEPT          32u

#define M7_SEARCH_MAGIC       0x4D37534541524348ULL
#define M7_GU_MAGIC           36ULL
#define M7_GU_EMA_MASK        38ULL
#define M7_GU_EMA0_FB         40ULL
#define M7_GU_EMA0_FE         42ULL
#define M7_GU_EMA0_SB         44ULL
#define M7_GU_EMA0_SE         46ULL
#define M7_GU_EMA1_FB         48ULL
#define M7_GU_EMA1_FE         50ULL
#define M7_GU_EMA1_SB         52ULL
#define M7_GU_EMA1_SE         54ULL
#define M7_GU_RANDEC_REM      56ULL
#define M7_GU_RANDEC_LIM      58ULL
#define M7_GU_RANDEC_SEQ      60ULL
#define M7_GU_RANDEC_CFL      62ULL

#define CONG_AND_ARITY_MAX    1000000u
#define CONG_AND_USZ_MAX      1000001u
#define CONG_ARITY_MASK       0x0FFFFFFFu

#define PHT_HEAD              256u
#define PHT_SZ                1024u
#define PHT_MASK              1023u
#define PHT_NEXT              1280u

#define M8_OCC_LIM            2001u
#define M8_NEG_OFF            2001u
#define M8_POS_MASK           4002u
#define M8_NEG_MASK           4066u
#define M8_GF_IDX             4130u
#define M8_RG_IDX             4131u
#define M8_ITE_CNT            4132u
#define M8_TMP_OFF            4134u
#define M8_RES_OFF            4192u

#define K6_MAX_V              8192ULL
#define K6_MIN_SCR            24576ULL
#define K6_BIN_FLAG           0x80000000u
#define K6_LIT_MASK           0x7FFFFFFFu
#define K6_BASE               1096u
#define K6_MV                 64u
#define K6_MC                 256u
#define K6_MAX_ORIG           128u

#define K6H_NV                0u
#define K6H_NC                1u
#define K6H_LVL               2u
#define K6H_PROP              3u
#define K6H_TRL_END           4u
#define K6H_UNASS             5u
#define K6H_INCONS            6u
#define K6H_QFIRST            7u
#define K6H_QLAST             8u
#define K6H_QSEARCH           9u
#define K6H_QSTAMP            10u
#define K6H_TICKS             11u
#define K6H_TICK_LIM          12u
#define K6H_ALEN              13u
#define K6H_ACAP              14u
#define K6H_NASSUMP           15u
#define K6H_NKL               16u
#define K6H_NANA              17u
#define K6H_STATUS            18u
#define K6H_PHASE             19u
#define K6H_OPEN              20u
#define K6H_MAX_V             21u
#define K6H_MAX_ORIG          22u
#define K6H_MAX_CL            23u
#define K6H_NEQ               24u

#define FID_K6_MAX_V          8192ULL
#define FID_K6_MIN_SCR        16384ULL
#define FID_K6_TICK_P1        1000000u
#define FID_K6_TICK_P2        10000000u

#define FKH_NV                4192u
#define FKH_NC                4193u
#define FKH_ORIG_NC           4194u
#define FKH_LVL               4195u
#define FKH_PROP              4196u
#define FKH_TRL_END           4197u
#define FKH_UNASS             4198u
#define FKH_INCONS            4199u
#define FKH_QFIRST            4200u
#define FKH_QLAST             4201u
#define FKH_QSEARCH           4202u
#define FKH_QSTAMP            4203u
#define FKH_TICKS             4204u
#define FKH_TICK_LIM          4205u
#define FKH_ALEN              4206u
#define FKH_ACAP              4207u
#define FKH_NANA              4208u
#define FKH_NKL               4209u
#define FKH_NRES              4210u
#define FKH_NUNITS            4211u
#define FKH_OPEN              4212u
#define FKH_PHASE             4213u
#define FKH_MAX_V             4214u
#define FKH_MAX_CL            4215u
#define FKH_MAX_ORIG          4216u

#define KH_NV                 0u
#define KH_NC                 1u
#define KH_ORIG_NC            2u
#define KH_LVL                3u
#define KH_PROP               4u
#define KH_TRL_END            5u
#define KH_UNASS              6u
#define KH_INCONS             7u
#define KH_QFIRST             8u
#define KH_QLAST              9u
#define KH_QSEARCH            10u
#define KH_QSTAMP             11u
#define KH_TICKS              12u
#define KH_TICK_LIM           13u
#define KH_ALEN               14u
#define KH_ACAP               15u
#define KH_NANA               16u
#define KH_NKL                17u
#define KH_NRES               18u
#define KH_NUNITS             19u
#define KH_OPEN               20u
#define KH_PHASE              21u

#define KO_LVL                32u
#define KO_RSN                96u
#define KO_QPREV              160u
#define KO_QNEXT              224u
#define KO_QST                288u
#define KO_TRL                352u
#define KO_FLAGS              416u
#define KO_ANA                480u
#define KO_KL                 544u
#define KO_VALS               608u
#define KO_WHEAD              736u
#define KO_WNEXT              864u
#define KO_WBLIT              1376u
#define KO_CL_OFF             1888u
#define KO_CL_META            2144u
#define KO_CL_AUX             2400u
#define KO_UNITS              2656u
#define KO_RES                2784u
#define KO_ARENA              2912u
#define KM_LRN                0x40000000u
"

/-! ## 3. Scoped Kernel `Wf` Tactics -/

meta section
open Lean Elab Command Tactic Meta

/-- Close `lhs = rhs` with `Eq.refl lhs`, checked solely by the Lean kernel (skipping
elaborator `isDefEq` on large PHOAS terms). -/
scoped elab "kissat_kernel_rfl" : tactic => do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let some (α, lhs, rhs) := tgt.eq?
    | throwError "kissat_kernel_rfl: goal is not an equality{indentExpr tgt}"
  if lhs.hasExprMVar || rhs.hasExprMVar then
    throwError "kissat_kernel_rfl: goal still contains metavariables{indentExpr tgt}"
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
theorem kissat_wf_of_reify {as rs : List Ty} {f : Func as rs}
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

/-- Empty-list base case for generated `fns_wf` theorems. -/
theorem fns_wf_nil : ∀ f ∈ ([] : List Fn), f.Wf :=
  fun _ hf => nomatch hf

/-- Cons step for generated `fns_wf` theorems (`O(1)` per function, zero tactic overhead). -/
theorem fns_wf_cons {fn : Fn} {rest : List Fn}
    (hfn : Func.Wf fn.body) (hrest : ∀ f ∈ rest, f.Wf) :
    ∀ f ∈ fn :: rest, f.Wf := fun _ hf =>
  match hf with
  | .head _ => hfn
  | .tail _ hr => hrest _ hr

/-- Prove `Func.Wf f` for a closed concrete function by reification + kernel `rfl`. -/
scoped macro "kissat_wf_reify" : tactic =>
  `(tactic| (refine kissat_wf_of_reify ?_; kissat_kernel_rfl))

end

/-! ## 5. Scoped `kissat_c0!` & `kissat_src_postlude!` Elaborators (`0` `@[expose]` on Theorems) -/

public section
open Lean Elab Command Meta

private meta def extractFnListConsts (e : Lean.Expr) : Except String (List Name) :=
  match e with
  | .app (.const ``List.nil _) _ => .ok []
  | .app (.app (.app (.const ``List.cons _) _) (.const fnNm _)) rest => do
    let tail ← extractFnListConsts rest
    .ok (fnNm :: tail)
  | _ => .error s!"kissat_src_postlude!: expected `List Fn` literal of constants, got {e}"

/-- Emit `@[expose] public def fns` (unless already declared), per-function `public`
`theorem <fn>_wf : Func.Wf <fn>_body`, and `public theorem fns_wf : ∀ f ∈ fns, f.Wf`. -/
meta def elabKissatSrcPostlude (pfx : Name) : CommandElabM Unit := do
  let ns ← getCurrNamespace
  let fnType := Lean.mkConst ``LeanQbe.T.Fn
  let fnsDefName := ns ++ `fns
  let pfxFnsName := ns ++ Name.mkSimple (pfx.toString ++ "_fns")
  let env ← getEnv
  if !env.contains fnsDefName then
    let fnsTy := mkApp (Lean.mkConst ``List [.one]) fnType
    liftCoreM <| addExposedDecl fnsDefName fnsTy (Lean.mkConst pfxFnsName) (forceExpose := true)
  let some pfxInfo := (← getEnv).find? pfxFnsName
    | throwError "kissat_src_postlude!: missing `{pfxFnsName}`"
  let some pfxVal := pfxInfo.value?
    | throwError "kissat_src_postlude!: `{pfxFnsName}` has no definition body"
  let fnConstNames ← match extractFnListConsts pfxVal with
    | .ok nms => pure nms
    | .error err => throwError err
  let mut wfEntries : List (Name × Name) := []
  for fnName in fnConstNames do
    let Name.str pre base := fnName
      | throwError "kissat_src_postlude!: unexpected function name `{fnName}`"
    let bodyName := Name.str pre (base ++ "_body")
    let wfName := Name.str pre (base ++ "_wf")
    liftTermElabM do
      let ci ← getConstInfo bodyName
      let funcTy := ci.type
      let some (asE, rsE) := funcTy.app2? ``Func
        | throwError "kissat_src_postlude!: `{bodyName}` does not have type `Func as rs`"
      let bodyC := Lean.mkConst bodyName
      let wfTy := mkApp3 (Lean.mkConst ``Func.Wf) asE rsE bodyC
      let u ← getLevel funcTy
      let reflPf := mkApp2 (Lean.mkConst ``Eq.refl [u]) funcTy bodyC
      let wfVal := mkApp4 (Lean.mkConst ``kissat_wf_of_reify) asE rsE bodyC reflPf
      withCurrHeartbeats do
        addDecl <| .thmDecl {
          name := wfName, levelParams := [], type := wfTy, value := wfVal
        }
    wfEntries := wfEntries ++ [(fnName, wfName)]
  liftTermElabM do
    let fnsConst := Lean.mkConst fnsDefName
    let fnsWfTy ← withLocalDeclD `f fnType fun f => do
      let memTy ← mkAppM ``Membership.mem #[fnsConst, f]
      let bodyTy := Lean.mkApp (Lean.mkConst ``Fn.Wf) f
      mkForallFVars #[f] (← mkArrow memTy bodyTy)
    let nilList := mkApp (Lean.mkConst ``List.nil [.one]) fnType
    let (_, fnsWfVal) := wfEntries.foldr
      (init := (nilList, Lean.mkConst ``fns_wf_nil))
      fun (fnName, wfName) (restE, restPf) =>
        let fnC := Lean.mkConst fnName
        let stepPf := mkApp4 (Lean.mkConst ``fns_wf_cons)
          fnC restE (Lean.mkConst wfName) restPf
        let consE := mkApp3 (Lean.mkConst ``List.cons [.one]) fnType fnC restE
        (consE, stepPf)
    withCurrHeartbeats do
      addDecl <| .thmDecl {
        name := ns ++ `fns_wf, levelParams := [], type := fnsWfTy, value := fnsWfVal
      }

/-- Elaborate an acyclic C0 translation unit into `@[expose] public` `<fn>_body`, `<fn>`, and
`<pfx>_fns` declarations (`forceExpose := true`, `emitModule := false`), plus by default the
`fns`, `<fn>_wf`, and `fns_wf` postlude (`0` `@[expose]` on theorems). -/
meta def elabKissatC0 (pfx : Name) (src : String) (emitPostlude : Bool := true) :
    CommandElabM Unit := do
  elabC0Module (some pfx) src (forceExpose := true) (emitModule := false)
  if emitPostlude then
    elabKissatSrcPostlude pfx

scoped elab "kissat_c0! " pfx:ident src:str : command =>
  elabKissatC0 pfx.getId src.getString true

scoped elab "kissat_c0! " "(" &"postlude" " := " &"true" ")" pfx:ident src:str : command =>
  elabKissatC0 pfx.getId src.getString true

scoped elab "kissat_c0! " "(" &"postlude" " := " &"false" ")" pfx:ident src:str : command =>
  elabKissatC0 pfx.getId src.getString false

scoped elab "kissat_src_postlude! " pfx:ident : command =>
  elabKissatSrcPostlude pfx.getId

end

end LeanQbe.T.Examples.Kissat.Src
