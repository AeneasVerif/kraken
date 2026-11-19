module

public import LeanQbe.T.Frontend.C0
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Module
public meta import LeanQbe.T.Frontend.C0

/-!
# Kissat C0 DIMACS Parser and Mandatory Model Checker (`X1` Stage A)

C0 implementation of the ASCII DIMACS CNF parser and read-only model verifier (`kissat_check_model`)
matching the exact byte grammar of `LeanQbe.T.Examples.LratBytes.parseDimacs` and literal encoding
of `LeanQbe.T.Examples.Kissat.Core` (`2 * (v - 1)` positive, `2 * (v - 1) + 1` negative).

All functions are non-recursive, take `≤ 5` scalar/pointer arguments, return a single scalar
word or `bool`, and have `exits = []` (zero `.exit`, zero UB).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat

open LeanQbe.T
open LeanQbe.T.Frontend.C0

meta section
open Lean Elab Command

/-- Elaborate an acyclic C0 translation unit into `@[expose] public` `<fn>_body`, `<fn>`, and
`<pfx>_fns` declarations (`forceExpose := true`) so downstream `module` proofs and `t_kernel_rfl`
can unfold definitions across module boundaries. -/
def elabKissatC0 (pfx : Name) (src : String) : CommandElabM Unit :=
  elabC0Module (some pfx) src (forceExpose := true) (emitModule := false)

elab "kissat_c0! " pfx:ident src:str : command =>
  elabKissatC0 pfx.getId src.getString

end

kissat_c0! dimacs "
typedef struct {
  u64 mv;
  u64 nc;
  u64 cur;
  u64 val;
} KissatDimacs;

bool kissat_is_ws(u64 b) {
  return b == 32ULL || (b >= 9ULL && b <= 13ULL);
}

bool kissat_is_digit(u64 b) {
  return b >= 48ULL && b <= 57ULL;
}

u64 kissat_skip_ws_comments(u64 p, u64 end) {
  while (p < end) {
    u64 b = (u64)(*(u8 *)p);
    if (kissat_is_ws(b)) {
      p = p + 1ULL;
    } else if (b == 99ULL) {
      p = p + 1ULL;
      while (p < end) {
        u64 c = (u64)(*(u8 *)p);
        p = p + 1ULL;
        if (c == 10ULL) {
          break;
        }
      }
    } else {
      break;
    }
  }
  return p;
}

bool kissat_skip_ws1(u64 end, KissatDimacs *d) {
  u64 p = d->cur;
  if (p >= end) {
    return false;
  }
  u64 b = (u64)(*(u8 *)p);
  if (!kissat_is_ws(b)) {
    return false;
  }
  p = p + 1ULL;
  while (p < end) {
    u64 c = (u64)(*(u8 *)p);
    if (!kissat_is_ws(c)) {
      break;
    }
    p = p + 1ULL;
  }
  d->cur = p;
  return true;
}

bool kissat_read_nat(u64 end, KissatDimacs *d) {
  u64 p = d->cur;
  if (p >= end) {
    return false;
  }
  u64 b0 = (u64)(*(u8 *)p);
  if (!kissat_is_digit(b0)) {
    return false;
  }
  u64 acc = b0 - 48ULL;
  p = p + 1ULL;
  while (p < end) {
    u64 b = (u64)(*(u8 *)p);
    if (kissat_is_digit(b)) {
      acc = acc * 10ULL + (b - 48ULL);
      if (acc >= 268435456ULL) {
        return false;
      }
      p = p + 1ULL;
    } else if (kissat_is_ws(b)) {
      break;
    } else {
      return false;
    }
  }
  d->cur = p;
  d->val = acc;
  return true;
}

bool kissat_parse_header(u64 cnf_ptr, u64 cnf_end, KissatDimacs *d) {
  u64 p = kissat_skip_ws_comments(cnf_ptr, cnf_end);
  if (p >= cnf_end) {
    return false;
  }
  if ((*(u8 *)p) != (u8)112) {
    return false;
  }
  d->cur = p + 1ULL;
  if (!kissat_skip_ws1(cnf_end, d)) {
    return false;
  }
  p = d->cur;
  if (p > cnf_end || cnf_end - p < 3ULL) {
    return false;
  }
  if ((*(u8 *)p) != (u8)99 || (*(u8 *)(p + 1ULL)) != (u8)110 ||
      (*(u8 *)(p + 2ULL)) != (u8)102) {
    return false;
  }
  d->cur = p + 3ULL;
  if (!kissat_skip_ws1(cnf_end, d)) {
    return false;
  }
  if (!kissat_read_nat(cnf_end, d)) {
    return false;
  }
  u64 mv = d->val;
  if (!kissat_skip_ws1(cnf_end, d)) {
    return false;
  }
  if (!kissat_read_nat(cnf_end, d)) {
    return false;
  }
  u64 nc = d->val;
  d->mv = mv;
  d->nc = nc;
  return true;
}

u64 kissat_next_lit(u64 cnf_end, KissatDimacs *d) {
  u64 p = kissat_skip_ws_comments(d->cur, cnf_end);
  if (p >= cnf_end) {
    return 0ULL;
  }
  u64 b = (u64)(*(u8 *)p);
  if (b == 45ULL) {
    d->cur = p + 1ULL;
    if (!kissat_read_nat(cnf_end, d)) {
      return 0ULL;
    }
    u64 v = d->val;
    if (v < 1ULL || v > d->mv) {
      return 0ULL;
    }
    d->val = ((v - 1ULL) << 1) | 1ULL;
    return 2ULL;
  }
  d->cur = p;
  if (!kissat_read_nat(cnf_end, d)) {
    return 0ULL;
  }
  u64 v = d->val;
  if (v == 0ULL) {
    return 1ULL;
  }
  if (v > d->mv) {
    return 0ULL;
  }
  d->val = (v - 1ULL) << 1;
  return 2ULL;
}

u64 kissat_check_model(u64 cnf_ptr, u64 cnf_end, KissatDimacs *d, i8 *vals, u64 mv_max) {
  if (!kissat_parse_header(cnf_ptr, cnf_end, d)) {
    return 0ULL;
  }
  if (d->mv > mv_max) {
    return 0ULL;
  }
  u64 i = 0ULL;
  while (i < d->nc) {
    bool sat = false;
    while (true) {
      u64 st = kissat_next_lit(cnf_end, d);
      if (st == 0ULL) {
        return 0ULL;
      }
      if (st == 1ULL) {
        break;
      }
      u64 lit = d->val;
      u64 v = lit >> 1;
      i8 vv = vals[v << 1];
      if ((lit & 1ULL) == 0ULL) {
        if (vv > (i8)0) {
          sat = true;
        }
      } else {
        if (vv < (i8)0) {
          sat = true;
        }
      }
    }
    if (!sat) {
      return 0ULL;
    }
    i = i + 1ULL;
  }
  d->cur = kissat_skip_ws_comments(d->cur, cnf_end);
  if (d->cur != cnf_end) {
    return 0ULL;
  }
  return 1ULL;
}
"

/-- Zero-exit acyclic `Module` containing the DIMACS parser and model checker functions. -/
def dimacsModule : LeanQbe.T.Module :=
  { fns := dimacs_fns, externs := [], exits := [] }

theorem kissat_is_ws_wf : Func.Wf kissat_is_ws_body := by t_wf_reify
theorem kissat_is_digit_wf : Func.Wf kissat_is_digit_body := by t_wf_reify
theorem kissat_skip_ws_comments_wf : Func.Wf kissat_skip_ws_comments_body := by t_wf_reify
theorem kissat_skip_ws1_wf : Func.Wf kissat_skip_ws1_body := by t_wf_reify
theorem kissat_read_nat_wf : Func.Wf kissat_read_nat_body := by t_wf_reify
theorem kissat_parse_header_wf : Func.Wf kissat_parse_header_body := by t_wf_reify
theorem kissat_next_lit_wf : Func.Wf kissat_next_lit_body := by t_wf_reify
theorem kissat_check_model_wf : Func.Wf kissat_check_model_body := by t_wf_reify

/-- All 8 functions in `dimacs_fns` satisfy `Fn.Wf`. -/
theorem dimacsFns_wf : ∀ f ∈ dimacs_fns, f.Wf := by
  intro f hf
  simp only [dimacs_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact kissat_is_ws_wf
  · exact kissat_is_digit_wf
  · exact kissat_skip_ws_comments_wf
  · exact kissat_skip_ws1_wf
  · exact kissat_read_nat_wf
  · exact kissat_parse_header_wf
  · exact kissat_next_lit_wf
  · exact kissat_check_model_wf

/-- Acyclic module certificate for `dimacsModule`. -/
theorem dimacsModule_checkAcyclic : dimacsModule.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.Examples.Kissat
