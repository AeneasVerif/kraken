module

public import LeanQbe.T.Frontend.C0
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Examples.Kissat.PatchModule
meta import LeanQbe.T.Frontend.C0
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.Examples.Kissat.PatchModule

/-!
# Combined C0 Frontend Extensions Verification & Composition Suite

Verifies all 5 integrated C0 frontend extensions individually and in full composition:
1. Parameterized & variadic `#define` macros (`Lexer.lean`)
2. Scoped `c0_header!` + `#include "name"` (`Lexer.lean`, `Elab.lean`, `LayoutElab.lean`)
3. `_Static_assert` + `offsetof(T, a.b)` + const evaluator (`Syntax`, `Lexer`, `Parser`, `Layout`,
   `Lower`)
4. `#pragma c0_upstream` / `c0_fidelity` / `c0_extension` / `c0_bounded` + `#c0_audit`
   (`Syntax`, `Lexer`, `Parser`, `Elab`)
5. Pure statement-level C99 desugarings: comma `for`, chained `=`, `(void) expr;` (`Parser.lean`)
6. All-5 combined composition (`c0_header!` with parameterized macros + `_Static_assert` +
   `offsetof`, `#pragma` provenance/fidelity/bounded, `(void) expr;`, chained `=`, comma `for`)
   proving 100% bit-identical `reifyFunc` IR by kernel `rfl` and `Func.Wf` via `t_wf_reify`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.C0ExtensionsTest

open LeanQbe.T
open LeanQbe.T.Frontend.C0
open LeanQbe.T.Examples.Kissat.PatchModule (tflatBeq)

instance {rs : List Ty} : BEq (TFlat rs) := ⟨tflatBeq⟩

private def strContains (hay needle : String) : Bool :=
  (hay.splitOn needle).length > 1

/-! ## 1. Extension #1: Parameterized & Variadic `#define` Macros -/

section Ext1Macros

private def testMacroFeatures : Except String Bool := do
  let src := "
#define ADD(a, b) ((a) + (b))
#define MUL(a, b) ((a) * (b))
#define MUL_ADD(a, b, c) ADD(MUL(a, b), c)
#define NEST_CALL(f, x) f(x)
#define DOUBLE(x) ((x) + (x))
#define ZERO() 0u
#define LOG(...)
#define LOG_MSG(fmt, ...)
#if ADD(2, 3) == 5 && ADD(ADD(1, 2), 3) == 6
#ifdef LOG
#if defined(ADD) && defined(LOG)
u32 macro_smoke(u32 a, u32 b, u32 c) {
  LOG(\"debug a=%u, b=%u\", a, b);
  LOG();
  LOG_MSG(\"single\");
  u32 r0 = ADD(ADD(a, b), c);
  u32 r1 = MUL_ADD(a, b, c);
  u32 r2 = NEST_CALL(DOUBLE, c);
  return r0 + r1 + r2 + ZERO();
}
#endif
#endif
#endif
"
  let tu ← parseC0 src
  pure (tu.decls.length == 1)

#guard testMacroFeatures.toOption == some true

-- Recursion guard stops self- and mutual-recursion without infinite loop
#guard match tokenize "#define REC(x) REC(x)\nu32 f(u32 x) { return REC(x); }" with
  | .ok toks => toks.any (·.kind == .ident "REC")
  | .error _ => false

#guard match tokenize
    "#define MA(x) MB(x)\n#define MB(x) MA(x)\nu32 f(u32 x) { return MA(x); }" with
  | .ok toks => toks.any fun t => t.kind == .ident "MA" || t.kind == .ident "MB"
  | .error _ => false

-- Nested same-macro argument expansion inside code + #if
#guard match parseC0
    ("#define ADD(a, b) ((a) + (b))\n" ++
     "#if ADD(ADD(1, 2), 3) == 6\n" ++
     "u32 f(u32 x) { return ADD(ADD(x, 1u), 2u); }\n" ++
     "#endif") with
  | .ok tu => tu.decls.length == 1
  | .error _ => false

-- Negative macro diagnostics
#guard (parseC0 "#define F(a, b u32 foo() { return 0; }").isOk == false
#guard (parseC0 "#define F(123) u32 foo() { return 0; }").isOk == false
#guard (parseC0 "#define F(a, a) ((a)+(a))\nu32 foo() { return 0; }").isOk == false
#guard (parseC0 "#define F(..., a) ((a))\nu32 foo() { return 0; }").isOk == false
#guard (parseC0 "#define F(a,,b) ((a)+(b))\nu32 foo() { return 0; }").isOk == false
#guard (parseC0 "#define F(a, b) ((a)+(b))\nu32 foo() { return F(1u); }").isOk == false
#guard (parseC0 "#define F(a, b) ((a)+(b))\nu32 foo() { return F(1u, 2u, 3u); }").isOk == false
#guard (parseC0 "#define ZERO() 0u\nu32 foo() { return ZERO(1u); }").isOk == false
#guard (parseC0 "#define REQ(a, ...) (a)\nu32 foo() { return REQ(); }").isOk == false
#guard (parseC0 "#define F(a, b) ((a)+(b))\nu32 foo() { return F(1u, 2u; }").isOk == false

end Ext1Macros

/-! ## 2. Extension #2: Scoped `c0_header!` + `#include "name"` -/

section Ext2Include

c0_header! "nested_base.h" "
typedef struct {
  u32 magic;
  u32 version;
} BaseMeta;
"

c0_header! compound_hdr "
#include \"nested_base.h\"
typedef struct {
  BaseMeta meta;
  u64 payload;
} CompoundPacket;
"

-- Shared Kissat header combining types, externs, object/func/variadic macros, and _Static_assert
c0_header! kissat_shared_hdr "
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
} FullHdr;

typedef struct {
  u32 nv, nc, lvl, prop, trl_end, unass, incons;
  u32 qfirst, qlast, qsearch, qstamp;
  u32 ticks, tick_lim, alen, acap, nassump, nkl, nana;
  u32 status, phase, open, max_v, max_orig, max_cl, neq;
} KittenHdr;

_Static_assert(sizeof(KissatDimacs) == 32, \"KissatDimacs size must be 32\");
_Static_assert(sizeof(FullHdr) == 976, \"FullHdr size must be 976\");
_Static_assert(offsetof(FullHdr, d.val) == 24, \"d.val offset must be 24\");
_Static_assert(offsetof(FullHdr, fuel) == 168, \"fuel offset must be 168\");
_Static_assert(offsetof(FullHdr, scratch_buf) == 920, \"scratch_buf offset must be 920\");
_Static_assert(sizeof(KittenHdr) == 100, \"KittenHdr size must be 100\");
_Static_assert(offsetof(KittenHdr, ticks) == 44, \"ticks offset must be 44\");

extern u64 full_m6_max_v(u64 cap);
extern void full_k6_add_ticks(u32 *k, u64 delta);
extern void full_k6_assign(u32 *k, u32 lit, u32 rsn);
extern void full_k6_watch(u32 *k, u32 cid, u32 l0, u32 l1);

#define PH_GLUE_MASK 0x7FFFFu
#define FL_ACTIVE    1u
#define K6H_NC       1u
#define K6H_INCONS   6u
#define K6H_TICKS    11u
#define K6H_ALEN     13u
#define K6H_ACAP     14u
#define K6H_MAX_CL   23u

#define K6_HDR(h, mv) (((u32 *)(h)->scratch_buf) + (1280u + ((mv) << 1)))
#define K6_VALS(k, mv) ((k) + (32u + 10u * (mv)))
#define K6_CL_OFF(k, mv) ((k) + (32u + 30u * (mv)))
#define K6_CL_SZ(k, mv) ((k) + (32u + 34u * (mv)))
#define K6_ARENA(k, mv) ((k) + (32u + 38u * (mv)))
#define K6_INCONS(k) ((k)[K6H_INCONS])
#define INC_FIELD(k, fld) (k)[fld] = (k)[fld] + 1u
#define LOG(...)
"

namespace ModIncCheck

c0_decl! inc_check "
#include <stdint.h>
#include \"c0.h\"
#include \"compound_hdr\"
#if 0
#include \"nonexistent_disabled\"
#endif

u64 get_packet_payload(CompoundPacket *p) {
  if (p->meta.magic == 0x43305052u) {
    return p->payload;
  }
  return 0ULL;
}
"

end ModIncCheck

theorem get_packet_payload_wf : Func.Wf ModIncCheck.get_packet_payload_body := by t_wf_reify

-- Sequential #includes (>100) succeed while cyclic #include fails cleanly
private def testSequentialIncludes : Bool :=
  let hdrs := Std.HashMap.emptyWithCapacity.insert "tiny" "#define ONE 1u"
  let lines := List.replicate 105 "#include \"tiny\""
  let src := String.intercalate "\n" lines ++ "\nu32 f() { return ONE; }"
  match parseC0 src hdrs with
  | .ok tu => tu.decls.length == 1
  | .error _ => false

#guard testSequentialIncludes

#guard match tokenize "#include \"cyc\"\nu32 f() { return 0u; }"
    (Std.HashMap.emptyWithCapacity.insert "cyc" "#include \"cyc\"") with
  | .error e => strContains e "maximum include depth exceeded"
  | .ok _ => false

-- Exact outer line number preserved after #include
#guard match parseC0 "#include \"tiny\"\nu32 f(u32 x) { return x + ; }"
    (Std.HashMap.emptyWithCapacity.insert "tiny" "typedef u32 my_u32;\ntypedef u64 my_u64;") with
  | .error e => strContains e "line 2"
  | .ok _ => false

-- Missing registered header errors cleanly
#guard match tokenize "#include \"unknown_hdr_88\"\nu64 f(u64 x) { return x; }"
    (Std.HashMap.emptyWithCapacity.insert "dummy" "u32 a;") with
  | .error e => strContains e "unknown_hdr_88"
  | .ok _ => false

#guard match expandC0Includes "#include \"unknown_hdr_99\"\nu64 f(u64 x) { return x; }"
    (Std.HashMap.emptyWithCapacity.insert "dummy" "u32 a;") with
  | .error e => strContains e "unknown_hdr_99"
  | .ok _ => false

end Ext2Include

/-! ## 3. Extension #3: `_Static_assert` + `offsetof` & Layout Parity -/

section Ext3Offset

c0_decl! ext3_demo "
#include \"kissat_shared_hdr\"

_Static_assert((~0 & 0xFF) == 0xFF, \"signed bitmask const eval\");
_Static_assert(sizeof(FullHdr) == 976);

u32 k6_get_ticks_manual(u8 *k) { return *(u32 *)(k + 44ULL); }
u32 k6_get_ticks_offsetof(u8 *k) { return *(u32 *)(k + offsetof(KittenHdr, ticks)); }
u32 k6_get_ticks_typed(KittenHdr *k) { return k->ticks; }

u64 full_get_fuel_manual(u8 *h) { return *(u64 *)(h + 168ULL); }
u64 full_get_fuel_offsetof(u8 *h) { return *(u64 *)(h + offsetof(FullHdr, fuel)); }
u64 full_get_fuel_typed(FullHdr *h) { return h->fuel; }

u64 full_get_val_manual(u8 *h) { return *(u64 *)(h + 24ULL); }
u64 full_get_val_offsetof(u8 *h) { return *(u64 *)(h + offsetof(FullHdr, d.val)); }
u64 full_get_val_typed(FullHdr *h) { return h->d.val; }

u64 block_assert_demo(KittenHdr *k) {
  _Static_assert(sizeof(KittenHdr) == 100, \"KittenHdr size in block\");
  _Static_assert(offsetof(KittenHdr, ticks) == 44, \"ticks offset in block\");
  return (u64)k->ticks;
}
"

private theorem k6_ticks_manual_eq :
    reifyFunc k6_get_ticks_manual_body = reifyFunc k6_get_ticks_typed_body := rfl
private theorem k6_ticks_offsetof_eq :
    reifyFunc k6_get_ticks_offsetof_body = reifyFunc k6_get_ticks_typed_body := rfl
private theorem full_fuel_manual_eq :
    reifyFunc full_get_fuel_manual_body = reifyFunc full_get_fuel_typed_body := rfl
private theorem full_fuel_offsetof_eq :
    reifyFunc full_get_fuel_offsetof_body = reifyFunc full_get_fuel_typed_body := rfl
private theorem full_val_manual_eq :
    reifyFunc full_get_val_manual_body = reifyFunc full_get_val_typed_body := rfl
private theorem full_val_offsetof_eq :
    reifyFunc full_get_val_offsetof_body = reifyFunc full_get_val_typed_body := rfl

theorem k6_get_ticks_typed_wf : Func.Wf k6_get_ticks_typed_body := by t_wf_reify
theorem full_get_fuel_typed_wf : Func.Wf full_get_fuel_typed_body := by t_wf_reify
theorem block_assert_demo_wf : Func.Wf block_assert_demo_body := by t_wf_reify

-- Negative _Static_assert / offsetof diagnostics
#guard match parseC0
    ("typedef struct { u32 nv; u32 ticks; } K6T;\n" ++
     "_Static_assert(offsetof(K6T, ticks) == 40, \"ticks offset mismatch\");")
    >>= buildLayoutEnv with
  | .error msg => msg == "static assertion failed: \"ticks offset mismatch\""
  | .ok _ => false

#guard match parseC0
    ("typedef struct { u32 a; u32 b; } S;\n" ++
     "_Static_assert(sizeof(S) == 12, \"struct size mismatch\");")
    >>= buildLayoutEnv with
  | .error msg => msg == "static assertion failed: \"struct size mismatch\""
  | .ok _ => false

#guard match parseC0 "void bad() { _Static_assert(10 * 10 == 99, \"mul failed\"); }"
    >>= lowerTranslationUnit with
  | .error msg => msg == "static assertion failed: \"mul failed\""
  | .ok _ => false

#guard match parseC0
    "typedef struct { u32 a; } S;\n_Static_assert(offsetof(S, missing) == 0, \"bad\");"
    >>= buildLayoutEnv with
  | .error msg => msg == "field 'missing' not found in aggregate"
  | .ok _ => false

-- Test c0_decl_and_layout! with #include + _Static_assert + offsetof
namespace LayoutIncludeDemo
c0_decl_and_layout! hdr_lay "
#include \"nested_base.h\"
_Static_assert(sizeof(BaseMeta) == 8, \"BaseMeta size\");
u32 read_magic(BaseMeta *m) { return *(u32 *)((u8 *)m + offsetof(BaseMeta, magic)); }
"
#guard BaseMeta.sizeof == 8
theorem read_magic_wf : Func.Wf read_magic_body := by t_wf_reify
end LayoutIncludeDemo

end Ext3Offset

/-! ## 4. Extension #4: `#pragma c0_*` Provenance & `#c0_audit` Tick Lint -/

section Ext4Audit

def congBugSrc : String :=
"#pragma c0_upstream \"FullM6CongSubst.lean:1185-1201\" full_cong_subsume
#pragma c0_fidelity
u64 full_cong_subsume_bug(u64* wstk, u64* wvec, u32* tmp, u32 msz,
    u64 cv, u64 ticks, u64 tick_lim) {
  bool subsumed = false;
  u32 k = 0u;
  while (k < msz && !subsumed && ticks < tick_lim) {
    ticks = ticks + 1ULL;
    u32 rk = tmp[k];
    u64 boff = wvec[(u64)rk << 1];
    u64 bend = boff + wvec[((u64)rk << 1) + 1ULL];
    u64 bp = boff;
    while (bp < bend) {
      u64 w0 = wstk[bp];
      if ((w0 & 1ULL) == 0ULL) { bp = bp + 2ULL; continue; }
      bp = bp + 1ULL;
      if ((w0 & 0x7fffffffULL) < (cv << 1)) { subsumed = true; break; }
    }
    k = k + 1u;
  }
  return subsumed ? 1ULL : 0ULL;
}"

#guard (auditC0Fn congBugSrc "full_cong_subsume_bug").toOption.map (·.hasLoopViolations) ==
  some true
#guard (auditC0Fn congBugSrc "full_cong_subsume_bug").toOption.map
  (fun r => r.loops[1]?.map (·.verdict.isOk)) == some (some false)

c0_decl! audit_ir_demo "
#pragma c0_upstream \"FullM6CongSubst.lean:1185-1201\" full_cong_subsume
#pragma c0_fidelity
u64 full_cong_bounded(u64* wstk, u64* wvec, u32* tmp, u32 msz,
    u64 cv, u64 ticks, u64 tick_lim) {
  bool subsumed = false;
  u32 k = 0u;
  while (k < msz && !subsumed && ticks < tick_lim) {
    ticks = ticks + 1ULL;
    u32 rk = tmp[k];
    u64 boff = wvec[(u64)rk << 1];
    u64 bend = boff + wvec[((u64)rk << 1) + 1ULL];
    u64 bp = boff;
    #pragma c0_bounded \"pointer progression guarantees termination: bp < bend\"
    while (bp < bend) {
      u64 w0 = wstk[bp];
      if ((w0 & 1ULL) == 0ULL) { bp = bp + 2ULL; continue; }
      bp = bp + 1ULL;
      if ((w0 & 0x7fffffffULL) < (cv << 1)) { subsumed = true; break; }
    }
    k = k + 1u;
  }
  return subsumed ? 1ULL : 0ULL;
}

u64 full_cong_raw(u64* wstk, u64* wvec, u32* tmp, u32 msz,
    u64 cv, u64 ticks, u64 tick_lim) {
  bool subsumed = false;
  u32 k = 0u;
  while (k < msz && !subsumed && ticks < tick_lim) {
    ticks = ticks + 1ULL;
    u32 rk = tmp[k];
    u64 boff = wvec[(u64)rk << 1];
    u64 bend = boff + wvec[((u64)rk << 1) + 1ULL];
    u64 bp = boff;
    while (bp < bend) {
      u64 w0 = wstk[bp];
      if ((w0 & 1ULL) == 0ULL) { bp = bp + 2ULL; continue; }
      bp = bp + 1ULL;
      if ((w0 & 0x7fffffffULL) < (cv << 1)) { subsumed = true; break; }
    }
    k = k + 1u;
  }
  return subsumed ? 1ULL : 0ULL;
}
"

private theorem cong_bounded_raw_ir_eq :
    reifyFunc full_cong_bounded_body = reifyFunc full_cong_raw_body := rfl
theorem full_cong_bounded_wf : Func.Wf full_cong_bounded_body := by t_wf_reify

-- Fidelity vs extension reachability + mixed-module unannotated helper check
def mixedAuditSrc : String :=
"#pragma c0_extension
u32 ext_dbg(u32 v) { return v + 1u; }
u32 pure_unannotated(u32 x) { return x + 2u; }
#pragma c0_fidelity
u32 fid_ok(u32 x) { return pure_unannotated(x); }
#pragma c0_fidelity
u32 fid_bad_direct(u32 x) { return ext_dbg(x); }
u32 indirect_bridge(u32 x) { return ext_dbg(x); }
#pragma c0_fidelity
u32 fid_bad_trans(u32 x) { return indirect_bridge(x); }
"

#guard (auditC0Fn mixedAuditSrc "fid_ok").toOption.map (·.isFidelityClean) == some true
#guard (auditC0Fn mixedAuditSrc "fid_bad_direct").toOption.map (·.extensionCallsReachable) ==
  some ["ext_dbg"]
#guard (auditC0Fn mixedAuditSrc "fid_bad_trans").toOption.map (·.extensionCallsReachable) ==
  some ["ext_dbg"]

#c0_audit full_cong_bounded
#c0_audit audit_ir_demo

end Ext4Audit

/-! ## 5. Extension #5: Statement-Level Desugarings & Side-Effect Safety -/

section Ext5Stmts

c0_decl! stmts_demo "
u32 side_fn(u32 *p) { *p = *p + 1u; return *p; }

u32 void_call_proto(u32 *p, u32 unused) {
  (void) unused;
  ((void) 0);
  (void) side_fn(p);
  return *p;
}

u32 void_call_manual(u32 *p, u32 unused) {
  side_fn(p);
  return *p;
}

u32 chained_for_proto(u32 *begin, u32 *end, u32 unused) {
  (void) unused;
  u32 first = 0u;
  u32 last = 0u;
  first = last = 0xffffffffu;
  u32 *p = (u32 *)0;
  u32 *q = (u32 *)0;
  for (p = begin, q = begin; p != end; p++, q++) {
    u32 w = *p;
    if (w == 0u) {
      q = q - 1;
      continue;
    }
    if (first == 0xffffffffu) { first = w; }
    last = w;
    *q = w;
  }
  return first + last + (u32)(q - begin);
}

u32 chained_for_manual(u32 *begin, u32 *end, u32 unused) {
  u32 first = 0u;
  u32 last = 0u;
  last = 0xffffffffu;
  first = last;
  u32 *p = (u32 *)0;
  u32 *q = (u32 *)0;
  p = begin;
  q = begin;
  for (; p != end; ) {
    u32 w = *p;
    if (w == 0u) {
      q = q - 1;
      p++;
      q++;
      continue;
    }
    if (first == 0xffffffffu) { first = w; }
    last = w;
    *q = w;
    p++;
    q++;
  }
  return first + last + (u32)(q - begin);
}
"

private theorem void_call_eq :
    reifyFunc void_call_proto_body = reifyFunc void_call_manual_body := rfl
private theorem chained_for_eq :
    reifyFunc chained_for_proto_body = reifyFunc chained_for_manual_body := rfl
#guard (reifyFunc void_call_proto_body == reifyFunc void_call_manual_body) == true
#guard (reifyFunc chained_for_proto_body == reifyFunc chained_for_manual_body) == true
theorem void_call_proto_wf : Func.Wf void_call_proto_body := by t_wf_reify
theorem chained_for_proto_wf : Func.Wf chained_for_proto_body := by t_wf_reify

-- Side-effect / lvalue safety checks
#guard (parseC0 "u32 f(u32 x) { (void)(1u + side(x)); return x; }").isOk == false
#guard (parseC0 "void f(u32 *g()) { u32 a = 0u; a = *g() = 1u; }").isOk == false
#guard (parseC0 "void f(u32 n) { for (u32 i = 0u, j = 1u; i < n; i++) {} }").isOk == false

end Ext5Stmts

/-! ## 6. Combined All-5 Composition Test (Zero IR Drift + Full `Wf`) -/

section All5Combined

-- Test #pragma BEFORE #include "kissat_shared_hdr" (which contains typedefs,
-- _Static_assert(offsetof(...)), extern prototypes, and K6_HDR/LOG/INC_FIELD macros!)
private meta def combinedComposedSrc : String :=
"#pragma c0_upstream \"kissat/sweep.c:120-165\" k6_sweep_compact
#pragma c0_fidelity
#include \"kissat_shared_hdr\"

u32 k6_sweep_compact_ext(FullHdr *h, u32 *begin, u32 *end, u32 tag) {
  LOG(\"enter k6_sweep_compact tag=%u\", tag);
  (void) tag;
  _Static_assert(offsetof(FullHdr, fuel) == 168, \"fuel offset check\");
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u) { return 0u; }
  u32 *k = K6_HDR(h, mv);
  u32 first = 0u;
  u32 last = 0u;
  first = last = 0xffffffffu;
  u32 *p = (u32 *)0;
  u32 *q = (u32 *)0;
  #pragma c0_bounded \"compact pass advances p monotonically over [begin, end)\"
  for (p = begin, q = begin; p != end; p++, q++) {
    u32 w = *p;
    if (w == 0u) {
      q = q - 1;
      continue;
    }
    if (first == 0xffffffffu) { first = w; }
    last = w;
    *q = w;
    INC_FIELD(k, K6H_TICKS);
  }
  LOG(\"exit first=%u last=%u\", first, last);
  return first + last + *(u32 *)((u8 *)h + offsetof(FullHdr, fuel)) + (u32)(q - begin);
}
"

namespace ComposedAll5

c0_decl! composed_mod
"#pragma c0_upstream \"kissat/sweep.c:120-165\" k6_sweep_compact
#pragma c0_fidelity
#include \"kissat_shared_hdr\"

u32 k6_sweep_compact(FullHdr *h, u32 *begin, u32 *end, u32 tag) {
  LOG(\"enter k6_sweep_compact tag=%u\", tag);
  (void) tag;
  _Static_assert(offsetof(FullHdr, fuel) == 168, \"fuel offset check\");
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u) { return 0u; }
  u32 *k = K6_HDR(h, mv);
  u32 first = 0u;
  u32 last = 0u;
  first = last = 0xffffffffu;
  u32 *p = (u32 *)0;
  u32 *q = (u32 *)0;
  #pragma c0_bounded \"compact pass advances p monotonically over [begin, end)\"
  for (p = begin, q = begin; p != end; p++, q++) {
    u32 w = *p;
    if (w == 0u) {
      q = q - 1;
      continue;
    }
    if (first == 0xffffffffu) { first = w; }
    last = w;
    *q = w;
    INC_FIELD(k, K6H_TICKS);
  }
  LOG(\"exit first=%u last=%u\", first, last);
  return first + last + *(u32 *)((u8 *)h + offsetof(FullHdr, fuel)) + (u32)(q - begin);
}
"

end ComposedAll5

namespace ManualBaseline

c0_decl! baseline_mod "
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
} FullHdr;

extern u64 full_m6_max_v(u64 cap);
extern void full_k6_add_ticks(u32 *k, u64 delta);
extern void full_k6_assign(u32 *k, u32 lit, u32 rsn);
extern void full_k6_watch(u32 *k, u32 cid, u32 l0, u32 l1);

u32 k6_sweep_compact(FullHdr *h, u32 *begin, u32 *end, u32 tag) {
  u32 mv = (u32)full_m6_max_v(h->scratch_cap);
  if (mv == 0u) { return 0u; }
  u32 *k = (((u32 *)h->scratch_buf) + (1280u + ((mv) << 1)));
  u32 first = 0u;
  u32 last = 0u;
  last = 0xffffffffu;
  first = last;
  u32 *p = (u32 *)0;
  u32 *q = (u32 *)0;
  p = begin;
  q = begin;
  for (; p != end; ) {
    u32 w = *p;
    if (w == 0u) {
      q = q - 1;
      p++;
      q++;
      continue;
    }
    if (first == 0xffffffffu) { first = w; }
    last = w;
    *q = w;
    (k)[11u] = (k)[11u] + 1u;
    p++;
    q++;
  }
  return first + last + *(u32 *)((u8 *)h + 168ULL) + (u32)(q - begin);
}
"

end ManualBaseline

-- Exact bit-identical TFlat IR between all-5 composed C0 and manual baseline
private theorem composed_all5_ir_eq :
    reifyFunc ComposedAll5.k6_sweep_compact_body =
      reifyFunc ManualBaseline.k6_sweep_compact_body := rfl

#guard (reifyFunc ComposedAll5.k6_sweep_compact_body ==
    reifyFunc ManualBaseline.k6_sweep_compact_body) == true

theorem composed_all5_wf : Func.Wf ComposedAll5.k6_sweep_compact_body := by t_wf_reify

#guard (PrintCpp.ppModule ComposedAll5.composed_mod_fns).isOk

#c0_audit ComposedAll5.k6_sweep_compact
#c0_audit ComposedAll5.composed_mod

-- Verify #pragma before #include attached provenance & fidelity cleanly
private meta def checkAll5Audit : Except String Bool := do
  let hdrs := Std.HashMap.emptyWithCapacity.insert "kissat_shared_hdr" "
typedef struct { u64 mv, nc, cur, val; } KissatDimacs;
typedef struct { KissatDimacs d; u64 pad[17]; u64 fuel; u64 pad2[94];
  u64 scratch_buf; u64 scratch_cap; u64 pad3[5]; } FullHdr;
extern u64 full_m6_max_v(u64 cap);
#define K6H_TICKS 11u
#define K6_HDR(h, mv) (((u32 *)(h)->scratch_buf) + (1280u + ((mv) << 1)))
#define INC_FIELD(k, fld) (k)[fld] = (k)[fld] + 1u
#define LOG(...)
"
  let rep ← auditC0Fn combinedComposedSrc "k6_sweep_compact_ext" hdrs
  pure (rep.provenance == some { loc := "kissat/sweep.c:120-165", upstreamFn := "k6_sweep_compact" }
    && rep.tag == .fidelity && rep.isFidelityClean && !rep.hasLoopViolations
    && rep.loops.length == 1)

#guard checkAll5Audit.toOption == some true

end All5Combined

end LeanQbeTest.T.C0ExtensionsTest
