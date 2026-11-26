/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 DIMACS Byte Lexer & Read-Only Model Checker (`Src/Dimacs.lean`)

Mirrors upstream `kissat/src/parse.c (byte lexer), check.c` (`9` live functions, DAG level `L0`):
- `kissat_is_ws` (R4: `kissat_is_ws`)
- `kissat_is_digit` (R4: `kissat_is_digit`)
- `kissat_skip_ws_comments` (R4: `kissat_skip_ws_comments`)
- `kissat_skip_ws1` (R4: `kissat_skip_ws1`)
- `kissat_read_nat` (R4: `kissat_read_nat`)
- `kissat_parse_header` (R4: `kissat_parse_header`)
- `kissat_next_lit` (R4: `kissat_next_lit`)
- `kissat_check_model` (R4: `kissat_check_model`)
- `full_skip_cl` (R4: `kissat_skip_clause`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Dimacs

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

kissat_c0! dimacs "
#include \"kissat_internal.h\"

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

bool full_skip_cl(u64 cnf_end, KissatDimacs *d) {
  while (true) {
    u64 st = kissat_next_lit(cnf_end, d);
    if (st == 0ULL) { return false; }
    if (st == 1ULL) { return true; }
  }
}
"

end

end LeanQbe.T.Examples.Kissat.Src.Dimacs
