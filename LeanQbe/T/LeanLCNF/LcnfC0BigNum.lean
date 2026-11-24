module

public import LeanQbe.T.Frontend.C0
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Module
public import LeanQbe.T.Wf
public meta import LeanQbe.T.Frontend.C0

/-!
# Pure C0 `Nat` & `Int` (`MPZ` / `BigNum`) Runtime (`Milestone R1`)

Self-contained, acyclic pure C0 implementation of Lean runtime `Nat` and `Int` arithmetic
(`lcnf_nat_alloc`, `lcnf_nat_slow`, `lcnf_int_op`) aligned byte-for-byte with R0's
`LcnfC0Rt` (`sizeof = 33672`, extended with trailing `LcnfC0BigNumRt` `{ base; scratch; scratch_cap;
}`)
and `lcnf_alloc` / `lcnf_dec_ref_cold` / `lcnf_panic`.

Design invariants:
- Zero `__uint128_t`, zero `malloc`/`calloc`/`free`, zero stack arrays, zero recursion.
- All temporary limb buffers reside in `rt->scratch` (`u64[rt->scratch_cap]`) with explicit bounds
  checks.
- Strictly acyclic helper decomposition (`checkAcyclic = true`), `Func.Wf` via `t_wf_reify`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.LeanLCNF

open LeanQbe.T
open LeanQbe.T.Frontend.C0

local elab "rt_r1_c0! " pfx:ident src:str : command => do
  let srcId := Lean.mkIdent (pfx.getId.appendAfter "_src")
  Lean.Elab.Command.elabCommand (← `(def $srcId : String := $src))
  LeanQbe.T.Frontend.C0.elabC0DeclAndLayout (some pfx.getId) src.getString
    (exits := ["lcnf_panic"]) (forceExpose := true)

rt_r1_c0! rtR1 "
typedef struct {
  u64 allocs;
  u64 frees;
  u64 live;
  u64 peak_live;
  u64 persistent;
  u64 reused;
  u64 cold_decs;
  u64 bytes;
} LcnfC0BaseStats;

typedef struct {
  u64 large_free;
  u64 ba_empty;
  u64 cur;
  u64 end;
  u64 work;
  u64 work_cap;
  u64 chunks;
  u64 nchunks;
  u64 chunks_cap;
  LcnfC0BaseStats st;
} LcnfC0BaseHdr;

typedef struct {
  u64 extra_args[32];
  u64 globals[4096];
  u64 free_list[64];
  LcnfC0BaseHdr s;
} LcnfC0BaseRt;

typedef struct {
  LcnfC0BaseRt base;
  u64 scratch;
  u64 scratch_cap;
} LcnfC0BigNumRt;

extern void lcnf_panic(u64 rt, u64 code);
extern u64 lcnf_alloc(u64 rt, u64 sz);
extern void lcnf_dec_ref_cold(u64 rt, u64 o);

static inline u64 rt_scratch(u64 rt) {
  return ((LcnfC0BigNumRt *)rt)->scratch;
}

static inline u64 rt_scratch_cap(u64 rt) {
  return ((LcnfC0BigNumRt *)rt)->scratch_cap;
}

u64 lcnf_nat_alloc(u64 rt, u64 nlimbs) {
  if (nlimbs == 0ULL) {
    nlimbs = 1ULL;
  }
  if (nlimbs > 0x01fffffdULL) {
    lcnf_panic(rt, 1ULL);
    return 0ULL;
  }
  u64 sz = 16ULL + 8ULL * nlimbs;
  u64 cs = (sz < 65536ULL) ? sz : 0ULL;
  u64 p = lcnf_alloc(rt, sz);
  *(u64 *)p = 1ULL | (cs << 32) | (250ULL << 56);
  *(u64 *)(p + 8ULL) = nlimbs | (nlimbs << 32);
  u64 i = 0ULL;
  while (i < nlimbs) {
    ((u64 *)p)[2ULL + i] = 0ULL;
    i = i + 1ULL;
  }
  return p;
}

void bn_dec_nat(u64 rt, u64 a) {
  if ((a & 1ULL) == 0ULL) {
    u64 hdr = *(u64 *)a;
    i64 rc = (i64)(i32)(u32)hdr;
    if (rc > 1) {
      *(u64 *)a = (hdr & 0xffffffff00000000ULL) | (u64)(u32)(rc - 1);
    } else if (rc == 1) {
      lcnf_dec_ref_cold(rt, a);
    }
  }
}

u64 bn_require_scratch(u64 rt, u64 need) {
  u64 scr = rt_scratch(rt);
  u64 cap = rt_scratch_cap(rt);
  if (scr == 0ULL || need > cap) {
    lcnf_panic(rt, 2ULL);
    return 0ULL;
  }
  return scr;
}

u64 bn_trim(u64 buf, u64 n) {
  while (n > 0ULL) {
    if (((u64 *)buf)[n - 1ULL] != 0ULL) {
      break;
    }
    n = n - 1ULL;
  }
  return n;
}

void bn_copy(u64 dst, u64 src, u64 n) {
  u64 i = 0ULL;
  while (i < n) {
    ((u64 *)dst)[i] = ((u64 *)src)[i];
    i = i + 1ULL;
  }
}

void bn_zero(u64 dst, u64 n) {
  u64 i = 0ULL;
  while (i < n) {
    ((u64 *)dst)[i] = 0ULL;
    i = i + 1ULL;
  }
}

u64 bn_nat_from_limbs(u64 rt, u64 buf, u64 n) {
  n = bn_trim(buf, n);
  if (n == 0ULL) {
    return 1ULL;
  }
  if (n == 1ULL) {
    u64 v = ((u64 *)buf)[0ULL];
    if (v < (1ULL << 63)) {
      return (v << 1) | 1ULL;
    }
  }
  u64 p = lcnf_nat_alloc(rt, n);
  bn_copy(p + 16ULL, buf, n);
  return p;
}

u64 bn_int_from_limbs(u64 rt, u64 neg, u64 buf, u64 n) {
  n = bn_trim(buf, n);
  if (n == 0ULL) {
    return 1ULL;
  }
  if (n == 1ULL) {
    u64 v = ((u64 *)buf)[0ULL];
    if (neg == 0ULL) {
      if (v < (1ULL << 62)) {
        return (v << 1) | 1ULL;
      }
    } else {
      if (v <= (1ULL << 62)) {
        u64 u = 0ULL - v;
        return (u << 1) | 1ULL;
      }
    }
  }
  u64 p = lcnf_nat_alloc(rt, n);
  if (neg != 0ULL) {
    *(u64 *)p = *(u64 *)p | (1ULL << 48);
  }
  bn_copy(p + 16ULL, buf, n);
  return p;
}

u64 bn_nat_len(u64 a) {
  if ((a & 1ULL) != 0ULL) {
    return ((a >> 1) == 0ULL) ? 0ULL : 1ULL;
  }
  return *(u64 *)(a + 8ULL) >> 32;
}

u64 bn_int_len(u64 a) {
  if ((a & 1ULL) != 0ULL) {
    i64 sv = ((i64)a) >> 1;
    return (sv == 0) ? 0ULL : 1ULL;
  }
  return *(u64 *)(a + 8ULL) >> 32;
}

u64 bn_load_nat(u64 a, u64 dst) {
  if ((a & 1ULL) != 0ULL) {
    u64 v = a >> 1;
    if (v == 0ULL) {
      return 0ULL;
    }
    ((u64 *)dst)[0ULL] = v;
    return 1ULL;
  }
  u64 n = *(u64 *)(a + 8ULL) >> 32;
  bn_copy(dst, a + 16ULL, n);
  return n;
}

u64 bn_load_int(u64 a, u64 dst) {
  if ((a & 1ULL) != 0ULL) {
    i64 sv = ((i64)a) >> 1;
    if (sv == 0) {
      return 0ULL;
    }
    if (sv > 0) {
      ((u64 *)dst)[0ULL] = (u64)sv;
      return 2ULL;
    }
    ((u64 *)dst)[0ULL] = 0ULL - (u64)sv;
    return 3ULL;
  }
  u64 hdr = *(u64 *)a;
  u64 neg = (((hdr >> 48) & 0xffULL) != 0ULL) ? 1ULL : 0ULL;
  u64 n = *(u64 *)(a + 8ULL) >> 32;
  bn_copy(dst, a + 16ULL, n);
  return (n << 1) | neg;
}

i64 bn_cmp_fixed(u64 a, u64 b, u64 n) {
  u64 i = n;
  while (i > 0ULL) {
    i = i - 1ULL;
    u64 x = ((u64 *)a)[i];
    u64 y = ((u64 *)b)[i];
    if (x < y) {
      return -1;
    }
    if (x > y) {
      return 1;
    }
  }
  return 0;
}

i64 bn_cmp(u64 a, u64 na, u64 b, u64 nb) {
  na = bn_trim(a, na);
  nb = bn_trim(b, nb);
  if (na < nb) {
    return -1;
  }
  if (na > nb) {
    return 1;
  }
  return bn_cmp_fixed(a, b, na);
}

u64 bn_add(u64 a, u64 na, u64 b, u64 nb, u64 out) {
  u64 m = (na > nb) ? na : nb;
  bool c = false;
  u64 i = 0ULL;
  while (i < m) {
    u64 x = (i < na) ? ((u64 *)a)[i] : 0ULL;
    u64 y = (i < nb) ? ((u64 *)b)[i] : 0ULL;
    u64 s = 0ULL;
    C0_TIE2(s, c, c0_addc64(x, y, c));
    ((u64 *)out)[i] = s;
    i = i + 1ULL;
  }
  ((u64 *)out)[m] = c ? 1ULL : 0ULL;
  return bn_trim(out, m + 1ULL);
}

u64 bn_add_one(u64 a, u64 na, u64 out) {
  bool c = true;
  u64 i = 0ULL;
  while (i < na) {
    u64 x = ((u64 *)a)[i];
    u64 s = 0ULL;
    C0_TIE2(s, c, c0_addc64(x, 0ULL, c));
    ((u64 *)out)[i] = s;
    i = i + 1ULL;
  }
  ((u64 *)out)[na] = c ? 1ULL : 0ULL;
  return bn_trim(out, na + 1ULL);
}

u64 bn_sub(u64 a, u64 na, u64 b, u64 nb, u64 out) {
  if (na == 0ULL) {
    return 0ULL;
  }
  bool br = false;
  u64 i = 0ULL;
  while (i < na) {
    u64 x = ((u64 *)a)[i];
    u64 y = (i < nb) ? ((u64 *)b)[i] : 0ULL;
    u64 d = 0ULL;
    C0_TIE2(d, br, c0_subb64(x, y, br));
    ((u64 *)out)[i] = d;
    i = i + 1ULL;
  }
  return bn_trim(out, na);
}

u64 bn_sub_one(u64 a, u64 na, u64 out) {
  if (na == 0ULL) {
    return 0ULL;
  }
  bool br = true;
  u64 i = 0ULL;
  while (i < na) {
    u64 x = ((u64 *)a)[i];
    u64 d = 0ULL;
    C0_TIE2(d, br, c0_subb64(x, 0ULL, br));
    ((u64 *)out)[i] = d;
    i = i + 1ULL;
  }
  return bn_trim(out, na);
}

u64 bn_mul(u64 a, u64 na, u64 b, u64 nb, u64 out) {
  bn_zero(out, na + nb);
  if (na == 0ULL || nb == 0ULL) {
    return 0ULL;
  }
  u64 i = 0ULL;
  while (i < na) {
    u64 ai = ((u64 *)a)[i];
    u64 carry = 0ULL;
    u64 j = 0ULL;
    while (j < nb) {
      u64 bj = ((u64 *)b)[j];
      u64 lo = 0ULL;
      u64 hi = 0ULL;
      C0_TIE2(lo, hi, c0_umul128(ai, bj));
      u64 cur = ((u64 *)out)[i + j];
      bool c1 = false;
      bool c2 = false;
      u64 s1 = 0ULL;
      u64 s2 = 0ULL;
      C0_TIE2(s1, c1, c0_addc64(cur, lo, false));
      C0_TIE2(s2, c2, c0_addc64(s1, carry, false));
      ((u64 *)out)[i + j] = s2;
      carry = hi + (c1 ? 1ULL : 0ULL) + (c2 ? 1ULL : 0ULL);
      j = j + 1ULL;
    }
    ((u64 *)out)[i + nb] = carry;
    i = i + 1ULL;
  }
  return bn_trim(out, na + nb);
}

u64 bn_bitwise(u64 op, u64 a, u64 na, u64 b, u64 nb, u64 out) {
  u64 n = (op == 0ULL) ? ((na < nb) ? na : nb) : ((na > nb) ? na : nb);
  u64 i = 0ULL;
  while (i < n) {
    u64 x = (i < na) ? ((u64 *)a)[i] : 0ULL;
    u64 y = (i < nb) ? ((u64 *)b)[i] : 0ULL;
    u64 r = 0ULL;
    if (op == 0ULL) {
      r = x & y;
    } else if (op == 1ULL) {
      r = x | y;
    } else {
      r = x ^ y;
    }
    ((u64 *)out)[i] = r;
    i = i + 1ULL;
  }
  return bn_trim(out, n);
}

u64 bn_shl(u64 a, u64 na, u64 ws, u64 bs, u64 out) {
  if (na == 0ULL) {
    return 0ULL;
  }
  bn_zero(out, ws);
  if (bs == 0ULL) {
    bn_copy(out + 8ULL * ws, a, na);
    ((u64 *)out)[ws + na] = 0ULL;
    return bn_trim(out, ws + na + 1ULL);
  }
  u64 rbs = 64ULL - bs;
  u64 carry = 0ULL;
  u64 i = 0ULL;
  while (i < na) {
    u64 v = ((u64 *)a)[i];
    ((u64 *)out)[ws + i] = (v << bs) | carry;
    carry = v >> rbs;
    i = i + 1ULL;
  }
  ((u64 *)out)[ws + na] = carry;
  return bn_trim(out, ws + na + 1ULL);
}

u64 bn_shr(u64 a, u64 na, u64 ws, u64 bs, u64 out) {
  if (ws >= na) {
    return 0ULL;
  }
  u64 out_n = na - ws;
  if (bs == 0ULL) {
    bn_copy(out, a + 8ULL * ws, out_n);
    return bn_trim(out, out_n);
  }
  u64 lbs = 64ULL - bs;
  u64 i = 0ULL;
  while (i + 1ULL < out_n) {
    ((u64 *)out)[i] = (((u64 *)a)[ws + i] >> bs) | (((u64 *)a)[ws + i + 1ULL] << lbs);
    i = i + 1ULL;
  }
  ((u64 *)out)[out_n - 1ULL] = ((u64 *)a)[ws + out_n - 1ULL] >> bs;
  return bn_trim(out, out_n);
}

void bn_divmod(u64 a, u64 na, u64 b, u64 nb, u64 q, u64 r) {
  if (na == 0ULL || nb == 0ULL) {
    return;
  }
  if (na == 1ULL && nb == 1ULL) {
    u64 av = ((u64 *)a)[0ULL];
    u64 bv = ((u64 *)b)[0ULL];
    ((u64 *)q)[0ULL] = av / bv;
    ((u64 *)r)[0ULL] = av % bv;
    return;
  }
  bn_zero(q, na);
  bn_zero(r, nb);
  u64 w = na;
  while (w > 0ULL) {
    w = w - 1ULL;
    u64 aw = ((u64 *)a)[w];
    u64 qw = 0ULL;
    u64 k = 64ULL;
    while (k > 0ULL) {
      k = k - 1ULL;
      u64 cbit = (aw >> k) & 1ULL;
      u64 j = 0ULL;
      while (j < nb) {
        u64 rj = ((u64 *)r)[j];
        ((u64 *)r)[j] = (rj << 1) | cbit;
        cbit = rj >> 63;
        j = j + 1ULL;
      }
      bool ge = (cbit != 0ULL) || (bn_cmp_fixed(r, b, nb) >= 0);
      if (ge) {
        bool br = false;
        u64 jj = 0ULL;
        while (jj < nb) {
          u64 rj = ((u64 *)r)[jj];
          u64 bj = ((u64 *)b)[jj];
          u64 d = 0ULL;
          C0_TIE2(d, br, c0_subb64(rj, bj, br));
          ((u64 *)r)[jj] = d;
          jj = jj + 1ULL;
        }
        qw = qw | (1ULL << k);
      }
    }
    ((u64 *)q)[w] = qw;
  }
}

u64 bn_nat_pow(u64 rt, u64 a, u64 b) {
  if (b == 1ULL) {
    return 3ULL;
  }
  if (a == 1ULL) {
    return 1ULL;
  }
  if (a == 3ULL) {
    return 3ULL;
  }
  if ((b & 1ULL) == 0ULL) {
    lcnf_panic(rt, 4ULL);
    return 0ULL;
  }
  u64 exp = b >> 1;
  u64 na = bn_nat_len(a);
  if (na > 0x01fffffdULL) {
    lcnf_panic(rt, 2ULL);
    return 0ULL;
  }
  u64 cap = rt_scratch_cap(rt);
  u64 scr = rt_scratch(rt);
  if (scr == 0ULL || cap < 4ULL) {
    lcnf_panic(rt, 2ULL);
    return 0ULL;
  }
  u64 slice = cap / 4ULL;
  if (na > slice) {
    lcnf_panic(rt, 2ULL);
    return 0ULL;
  }
  u64 buf_res = scr;
  u64 buf_base = scr + 8ULL * slice;
  u64 buf_tmp = scr + 16ULL * slice;
  u64 buf_prod = scr + 24ULL * slice;
  ((u64 *)buf_res)[0ULL] = 1ULL;
  u64 rn = 1ULL;
  u64 bn = bn_load_nat(a, buf_base);
  while (exp > 0ULL) {
    if ((exp & 1ULL) != 0ULL) {
      if (rn + bn > slice) {
        lcnf_panic(rt, 4ULL);
        return 0ULL;
      }
      u64 pn = bn_mul(buf_res, rn, buf_base, bn, buf_prod);
      bn_copy(buf_res, buf_prod, pn);
      rn = pn;
    }
    exp = exp >> 1;
    if (exp > 0ULL) {
      if (bn + bn > slice) {
        lcnf_panic(rt, 4ULL);
        return 0ULL;
      }
      bn_copy(buf_tmp, buf_base, bn);
      u64 pn = bn_mul(buf_base, bn, buf_tmp, bn, buf_prod);
      bn_copy(buf_base, buf_prod, pn);
      bn = pn;
    }
  }
  return bn_nat_from_limbs(rt, buf_res, rn);
}

u64 bn_nat_gcd(u64 rt, u64 a, u64 b) {
  u64 na = bn_nat_len(a);
  u64 nb = bn_nat_len(b);
  if (na > 0x01fffffdULL || nb > 0x01fffffdULL) {
    lcnf_panic(rt, 2ULL);
    return 0ULL;
  }
  if (na == 0ULL && nb == 0ULL) {
    return 1ULL;
  }
  if (na == 0ULL) {
    u64 scr = bn_require_scratch(rt, nb);
    nb = bn_load_nat(b, scr);
    return bn_nat_from_limbs(rt, scr, nb);
  }
  if (nb == 0ULL) {
    u64 scr = bn_require_scratch(rt, na);
    na = bn_load_nat(a, scr);
    return bn_nat_from_limbs(rt, scr, na);
  }
  u64 maxn = (na > nb) ? na : nb;
  u64 scr = bn_require_scratch(rt, 4ULL * maxn);
  u64 bufA = scr;
  u64 bufB = scr + 8ULL * maxn;
  u64 bufQ = scr + 16ULL * maxn;
  u64 bufR = scr + 24ULL * maxn;
  na = bn_load_nat(a, bufA);
  nb = bn_load_nat(b, bufB);
  while (nb > 0ULL) {
    if (bn_cmp(bufA, na, bufB, nb) < 0) {
      bn_copy(bufR, bufA, na);
      bn_copy(bufA, bufB, nb);
      bn_copy(bufB, bufR, na);
      u64 tmp = na;
      na = nb;
      nb = tmp;
      continue;
    }
    bn_divmod(bufA, na, bufB, nb, bufQ, bufR);
    u64 rn = bn_trim(bufR, nb);
    bn_copy(bufA, bufB, nb);
    na = nb;
    bn_copy(bufB, bufR, rn);
    nb = rn;
  }
  return bn_nat_from_limbs(rt, bufA, na);
}

u64 lcnf_nat_arith(u64 rt, u64 op, u64 a, u64 b) {
  if (op == 17ULL) {
    if ((a & 1ULL) != 0ULL) {
      u64 v = a >> 1;
      if (v == 0ULL) {
        return 1ULL;
      }
      return ((v - 1ULL) << 1) | 1ULL;
    }
    u64 na = bn_nat_len(a);
    if (na == 0ULL || na > 0x01fffffdULL) {
      if (na == 0ULL) {
        return 1ULL;
      }
      lcnf_panic(rt, 2ULL);
      return 0ULL;
    }
    u64 scr = bn_require_scratch(rt, 2ULL * na);
    na = bn_load_nat(a, scr);
    u64 out_n = bn_sub_one(scr, na, scr + 8ULL * na);
    return bn_nat_from_limbs(rt, scr + 8ULL * na, out_n);
  }
  u64 na = bn_nat_len(a);
  u64 nb = bn_nat_len(b);
  if (na > 0x01fffffdULL || nb > 0x01fffffdULL) {
    lcnf_panic(rt, 2ULL);
    return 0ULL;
  }
  u64 maxn = (na > nb) ? na : nb;
  u64 scr = bn_require_scratch(rt, 2ULL * (na + nb) + 2ULL);
  u64 bufA = scr;
  u64 bufB = scr + 8ULL * na;
  u64 bufOut = scr + 8ULL * (na + nb);
  na = bn_load_nat(a, bufA);
  nb = bn_load_nat(b, bufB);
  if (op == 1ULL) {
    u64 rn = bn_add(bufA, na, bufB, nb, bufOut);
    return bn_nat_from_limbs(rt, bufOut, rn);
  } else if (op == 2ULL) {
    if (bn_cmp(bufA, na, bufB, nb) <= 0) {
      return 1ULL;
    }
    u64 rn = bn_sub(bufA, na, bufB, nb, bufOut);
    return bn_nat_from_limbs(rt, bufOut, rn);
  } else if (op == 3ULL) {
    if (na == 0ULL || nb == 0ULL) {
      return 1ULL;
    }
    u64 rn = bn_mul(bufA, na, bufB, nb, bufOut);
    return bn_nat_from_limbs(rt, bufOut, rn);
  } else if (op == 4ULL) {
    if (nb == 0ULL || bn_cmp(bufA, na, bufB, nb) < 0) {
      return 1ULL;
    }
    u64 bufQ = bufOut;
    u64 bufR = bufOut + 8ULL * na;
    bn_divmod(bufA, na, bufB, nb, bufQ, bufR);
    return bn_nat_from_limbs(rt, bufQ, na);
  } else if (op == 5ULL) {
    if (nb == 0ULL || bn_cmp(bufA, na, bufB, nb) < 0) {
      return bn_nat_from_limbs(rt, bufA, na);
    }
    u64 bufQ = bufOut;
    u64 bufR = bufOut + 8ULL * na;
    bn_divmod(bufA, na, bufB, nb, bufQ, bufR);
    return bn_nat_from_limbs(rt, bufR, nb);
  } else if (op == 6ULL) {
    return (bn_cmp(bufA, na, bufB, nb) == 0) ? 1ULL : 0ULL;
  } else if (op == 7ULL) {
    return (bn_cmp(bufA, na, bufB, nb) < 0) ? 1ULL : 0ULL;
  } else if (op == 8ULL) {
    return (bn_cmp(bufA, na, bufB, nb) <= 0) ? 1ULL : 0ULL;
  }
  lcnf_panic(rt, 5ULL);
  return 0ULL;
}

u64 lcnf_nat_bits(u64 rt, u64 op, u64 a, u64 b) {
  if (op == 13ULL) {
    u64 v = 0ULL;
    if ((a & 1ULL) != 0ULL) {
      v = a >> 1;
    } else {
      u64 na = *(u64 *)(a + 8ULL) >> 32;
      if (na > 0ULL) {
        v = ((u64 *)a)[2ULL];
      }
    }
    if (b == 0ULL) {
      return 0ULL;
    }
    if (b >= 64ULL) {
      return v;
    }
    return v & ((1ULL << b) - 1ULL);
  }
  if (op == 14ULL) {
    if (a < (1ULL << 63)) {
      return (a << 1) | 1ULL;
    }
    u64 p = lcnf_nat_alloc(rt, 1ULL);
    ((u64 *)p)[2ULL] = a;
    return p;
  }
  if (op == 19ULL) {
    if ((a & 1ULL) != 0ULL) {
      u64 v = a >> 1;
      if (v == 0ULL) {
        return 1ULL;
      }
      u64 lg = 63ULL - c0_clz64(v);
      return (lg << 1) | 1ULL;
    }
    u64 na = *(u64 *)(a + 8ULL) >> 32;
    u64 tn = bn_trim(a + 16ULL, na);
    if (tn == 0ULL) {
      return 1ULL;
    }
    u64 hi = ((u64 *)a)[2ULL + tn - 1ULL];
    u64 lg = (tn * 64ULL - 1ULL) - c0_clz64(hi);
    return (lg << 1) | 1ULL;
  }
  if (op == 9ULL) {
    if ((a & 1ULL) != 0ULL) {
      if ((b & 1ULL) == 0ULL) {
        return 1ULL;
      }
      u64 s = b >> 1;
      if (s >= 64ULL) {
        return 1ULL;
      }
      return (((a >> 1) >> s) << 1) | 1ULL;
    }
    if ((b & 1ULL) == 0ULL) {
      return 1ULL;
    }
    u64 s = b >> 1;
    u64 ws = s >> 6;
    u64 bs = s & 63ULL;
    u64 na = bn_nat_len(a);
    if (ws >= na || na > 0x01fffffdULL) {
      if (ws >= na) {
        return 1ULL;
      }
      lcnf_panic(rt, 2ULL);
      return 0ULL;
    }
    u64 scr = bn_require_scratch(rt, 2ULL * na - ws);
    na = bn_load_nat(a, scr);
    u64 rn = bn_shr(scr, na, ws, bs, scr + 8ULL * na);
    return bn_nat_from_limbs(rt, scr + 8ULL * na, rn);
  }
  if (op == 15ULL) {
    u64 na = bn_nat_len(a);
    if (na == 0ULL) {
      return 1ULL;
    }
    if ((b & 1ULL) == 0ULL) {
      lcnf_panic(rt, 3ULL);
      return 0ULL;
    }
    u64 s = b >> 1;
    u64 ws = s >> 6;
    u64 bs = s & 63ULL;
    if (na > 0x01fffffdULL || ws > 0x01fffffcULL || na + ws + 1ULL > 0x01fffffdULL) {
      lcnf_panic(rt, 3ULL);
      return 0ULL;
    }
    u64 scr = bn_require_scratch(rt, 2ULL * na + ws + 1ULL);
    na = bn_load_nat(a, scr);
    u64 rn = bn_shl(scr, na, ws, bs, scr + 8ULL * na);
    return bn_nat_from_limbs(rt, scr + 8ULL * na, rn);
  }
  u64 na = bn_nat_len(a);
  u64 nb = bn_nat_len(b);
  if (na > 0x01fffffdULL || nb > 0x01fffffdULL) {
    lcnf_panic(rt, 2ULL);
    return 0ULL;
  }
  u64 maxn = (na > nb) ? na : nb;
  u64 scr = bn_require_scratch(rt, na + nb + maxn + 1ULL);
  u64 bufA = scr;
  u64 bufB = scr + 8ULL * na;
  u64 bufOut = scr + 8ULL * (na + nb);
  na = bn_load_nat(a, bufA);
  nb = bn_load_nat(b, bufB);
  u64 b_op = op - 10ULL;
  u64 rn = bn_bitwise(b_op, bufA, na, bufB, nb, bufOut);
  return bn_nat_from_limbs(rt, bufOut, rn);
}

u64 lcnf_nat_slow(u64 rt, u64 op, u64 a, u64 b) {
  if ((op >= 1ULL && op <= 8ULL) || op == 17ULL) {
    return lcnf_nat_arith(rt, op, a, b);
  }
  if ((op >= 9ULL && op <= 15ULL) || op == 19ULL) {
    return lcnf_nat_bits(rt, op, a, b);
  }
  if (op == 16ULL) {
    return bn_nat_pow(rt, a, b);
  }
  if (op == 18ULL) {
    return bn_nat_gcd(rt, a, b);
  }
  lcnf_panic(rt, 5ULL);
  return 0ULL;
}

u64 lcnf_int_conv(u64 rt, u64 op, u64 a) {
  if (op == 1ULL) {
    if ((a & 1ULL) != 0ULL) {
      u64 v = a >> 1;
      if (v < (1ULL << 62)) {
        return (v << 1) | 1ULL;
      }
      u64 p = lcnf_nat_alloc(rt, 1ULL);
      ((u64 *)p)[2ULL] = v;
      return p;
    }
    return a;
  }
  if (op == 13ULL) {
    i64 sv = (i64)a;
    i64 lim = (i64)(1ULL << 62);
    if (sv >= -lim && sv < lim) {
      return (((u64)sv) << 1) | 1ULL;
    }
    u64 neg = (sv < 0) ? 1ULL : 0ULL;
    u64 mag = (neg != 0ULL) ? (0ULL - (u64)sv) : (u64)sv;
    u64 p = lcnf_nat_alloc(rt, 1ULL);
    if (neg != 0ULL) {
      *(u64 *)p = *(u64 *)p | (1ULL << 48);
    }
    ((u64 *)p)[2ULL] = mag;
    return p;
  }
  if (op == 16ULL) {
    if ((a & 1ULL) != 0ULL) {
      i64 sv = ((i64)a) >> 1;
      return (sv >= 0) ? 1ULL : 0ULL;
    }
    u64 hdr = *(u64 *)a;
    return (((hdr >> 48) & 0xffULL) == 0ULL) ? 1ULL : 0ULL;
  }
  if (op == 2ULL) {
    if ((a & 1ULL) != 0ULL) {
      u64 v = (a >> 1) + 1ULL;
      if (v <= (1ULL << 62)) {
        u64 u = 0ULL - v;
        return (u << 1) | 1ULL;
      }
      u64 p = lcnf_nat_alloc(rt, 1ULL);
      *(u64 *)p = *(u64 *)p | (1ULL << 48);
      ((u64 *)p)[2ULL] = v;
      return p;
    }
    u64 na = bn_nat_len(a);
    if (na > 0x01fffffdULL) {
      lcnf_panic(rt, 2ULL);
      return 0ULL;
    }
    u64 scr = bn_require_scratch(rt, na + 1ULL);
    u64 out_n = bn_add_one(a + 16ULL, na, scr);
    bn_dec_nat(rt, a);
    return bn_int_from_limbs(rt, 1ULL, scr, out_n);
  }
  u64 na = bn_int_len(a);
  if (na == 0ULL) {
    return 1ULL;
  }
  if (na > 0x01fffffdULL) {
    lcnf_panic(rt, 2ULL);
    return 0ULL;
  }
  u64 scr = bn_require_scratch(rt, na);
  u64 info = bn_load_int(a, scr);
  u64 lenA = info >> 1;
  u64 negA = info & 1ULL;
  if (op == 3ULL) {
    return bn_int_from_limbs(rt, (lenA == 0ULL) ? 0ULL : (1ULL - negA), scr, lenA);
  }
  if (op == 9ULL) {
    return bn_nat_from_limbs(rt, scr, lenA);
  }
  lcnf_panic(rt, 6ULL);
  return 0ULL;
}

u64 lcnf_int_addsub_cmp(u64 rt, u64 op, u64 a, u64 b) {
  u64 na = bn_int_len(a);
  u64 nb = bn_int_len(b);
  if (na > 0x01fffffdULL || nb > 0x01fffffdULL) {
    lcnf_panic(rt, 2ULL);
    return 0ULL;
  }
  u64 maxn = (na > nb) ? na : nb;
  u64 scr = bn_require_scratch(rt, na + nb + maxn + 1ULL);
  u64 bufA = scr;
  u64 bufB = scr + 8ULL * na;
  u64 bufOut = scr + 8ULL * (na + nb);
  u64 infoA = bn_load_int(a, bufA);
  u64 infoB = bn_load_int(b, bufB);
  u64 lenA = infoA >> 1;
  u64 negA = infoA & 1ULL;
  u64 lenB = infoB >> 1;
  u64 negB = infoB & 1ULL;
  if (op == 4ULL || op == 5ULL) {
    u64 negB_eff = negB;
    if (op == 5ULL && lenB > 0ULL) {
      negB_eff = 1ULL - negB;
    }
    if (lenA == 0ULL) {
      return bn_int_from_limbs(rt, negB_eff, bufB, lenB);
    }
    if (lenB == 0ULL) {
      return bn_int_from_limbs(rt, negA, bufA, lenA);
    }
    if (negA == negB_eff) {
      u64 rn = bn_add(bufA, lenA, bufB, lenB, bufOut);
      return bn_int_from_limbs(rt, negA, bufOut, rn);
    }
    i64 c = bn_cmp(bufA, lenA, bufB, lenB);
    if (c == 0) {
      return 1ULL;
    }
    if (c > 0) {
      u64 rn = bn_sub(bufA, lenA, bufB, lenB, bufOut);
      return bn_int_from_limbs(rt, negA, bufOut, rn);
    }
    u64 rn = bn_sub(bufB, lenB, bufA, lenA, bufOut);
    return bn_int_from_limbs(rt, negB_eff, bufOut, rn);
  }
  i64 cmp = 0;
  if (negA != negB) {
    cmp = (negA != 0ULL) ? -1 : 1;
  } else {
    i64 mc = bn_cmp(bufA, lenA, bufB, lenB);
    cmp = (negA != 0ULL) ? -mc : mc;
  }
  if (op == 10ULL) {
    return (cmp == 0) ? 1ULL : 0ULL;
  }
  if (op == 11ULL) {
    return (cmp < 0) ? 1ULL : 0ULL;
  }
  return (cmp <= 0) ? 1ULL : 0ULL;
}

u64 lcnf_int_muldiv(u64 rt, u64 op, u64 a, u64 b) {
  u64 na = bn_int_len(a);
  u64 nb = bn_int_len(b);
  if (na > 0x01fffffdULL || nb > 0x01fffffdULL) {
    lcnf_panic(rt, 2ULL);
    return 0ULL;
  }
  u64 maxn = (na > nb) ? na : nb;
  u64 scr = bn_require_scratch(rt, 2ULL * (na + nb) + maxn + 2ULL);
  u64 bufA = scr;
  u64 bufB = scr + 8ULL * na;
  u64 infoA = bn_load_int(a, bufA);
  u64 infoB = bn_load_int(b, bufB);
  u64 lenA = infoA >> 1;
  u64 negA = infoA & 1ULL;
  u64 lenB = infoB >> 1;
  u64 negB = infoB & 1ULL;
  if (op == 6ULL) {
    if (lenA == 0ULL || lenB == 0ULL) {
      return 1ULL;
    }
    u64 bufOut = scr + 8ULL * (na + nb);
    u64 rn = bn_mul(bufA, lenA, bufB, lenB, bufOut);
    return bn_int_from_limbs(rt, negA ^ negB, bufOut, rn);
  }
  if (lenB == 0ULL) {
    if (op == 7ULL || op == 14ULL) {
      return 1ULL;
    }
    return bn_int_from_limbs(rt, negA, bufA, lenA);
  }
  u64 bufQ = scr + 8ULL * (na + nb);
  u64 bufR = bufQ + 8ULL * na;
  u64 bufOut = bufR + 8ULL * nb;
  u64 qn = 0ULL;
  u64 rn = 0ULL;
  if (bn_cmp(bufA, lenA, bufB, lenB) < 0) {
    bn_copy(bufR, bufA, lenA);
    rn = lenA;
  } else {
    bn_divmod(bufA, lenA, bufB, lenB, bufQ, bufR);
    qn = bn_trim(bufQ, lenA);
    rn = bn_trim(bufR, lenB);
  }
  if (op == 14ULL) {
    return bn_int_from_limbs(rt, (qn == 0ULL) ? 0ULL : (negA ^ negB), bufQ, qn);
  }
  if (op == 15ULL) {
    return bn_int_from_limbs(rt, (rn == 0ULL) ? 0ULL : negA, bufR, rn);
  }
  if (op == 7ULL) {
    if (negA != 0ULL && rn != 0ULL) {
      u64 q1n = bn_add_one(bufQ, qn, bufOut);
      return bn_int_from_limbs(rt, negA ^ negB, bufOut, q1n);
    }
    return bn_int_from_limbs(rt, (qn == 0ULL) ? 0ULL : (negA ^ negB), bufQ, qn);
  }
  if (negA == 0ULL || rn == 0ULL) {
    return bn_int_from_limbs(rt, 0ULL, bufR, rn);
  }
  u64 r1n = bn_sub(bufB, lenB, bufR, rn, bufOut);
  return bn_int_from_limbs(rt, 0ULL, bufOut, r1n);
}

u64 lcnf_int_op(u64 rt, u64 op, u64 a, u64 b) {
  if (op == 1ULL || op == 2ULL || op == 3ULL || op == 9ULL || op == 13ULL || op == 16ULL) {
    return lcnf_int_conv(rt, op, a);
  }
  if (op == 4ULL || op == 5ULL || (op >= 10ULL && op <= 12ULL)) {
    return lcnf_int_addsub_cmp(rt, op, a, b);
  }
  if (op == 6ULL || op == 7ULL || op == 8ULL || op == 14ULL || op == 15ULL) {
    return lcnf_int_muldiv(rt, op, a, b);
  }
  lcnf_panic(rt, 6ULL);
  return 0ULL;
}
"

theorem LcnfC0BaseRt_sizeof_eq : LcnfC0BaseRt.sizeof = 33672 := by decide
theorem LcnfC0BigNumRt_sizeof_eq : LcnfC0BigNumRt.sizeof = 33688 := by decide

theorem rt_scratch_wf : Func.Wf rt_scratch_body := by t_wf_reify
theorem rt_scratch_cap_wf : Func.Wf rt_scratch_cap_body := by t_wf_reify
theorem lcnf_nat_alloc_wf : Func.Wf lcnf_nat_alloc_body := by t_wf_reify
theorem bn_dec_nat_wf : Func.Wf bn_dec_nat_body := by t_wf_reify
theorem bn_require_scratch_wf : Func.Wf bn_require_scratch_body := by t_wf_reify
theorem bn_trim_wf : Func.Wf bn_trim_body := by t_wf_reify
theorem bn_copy_wf : Func.Wf bn_copy_body := by t_wf_reify
theorem bn_zero_wf : Func.Wf bn_zero_body := by t_wf_reify
theorem bn_nat_from_limbs_wf : Func.Wf bn_nat_from_limbs_body := by t_wf_reify
theorem bn_int_from_limbs_wf : Func.Wf bn_int_from_limbs_body := by t_wf_reify
theorem bn_nat_len_wf : Func.Wf bn_nat_len_body := by t_wf_reify
theorem bn_int_len_wf : Func.Wf bn_int_len_body := by t_wf_reify
theorem bn_load_nat_wf : Func.Wf bn_load_nat_body := by t_wf_reify
theorem bn_load_int_wf : Func.Wf bn_load_int_body := by t_wf_reify
theorem bn_cmp_fixed_wf : Func.Wf bn_cmp_fixed_body := by t_wf_reify
theorem bn_cmp_wf : Func.Wf bn_cmp_body := by t_wf_reify
theorem bn_add_wf : Func.Wf bn_add_body := by t_wf_reify
theorem bn_add_one_wf : Func.Wf bn_add_one_body := by t_wf_reify
theorem bn_sub_wf : Func.Wf bn_sub_body := by t_wf_reify
theorem bn_sub_one_wf : Func.Wf bn_sub_one_body := by t_wf_reify
theorem bn_mul_wf : Func.Wf bn_mul_body := by t_wf_reify
theorem bn_bitwise_wf : Func.Wf bn_bitwise_body := by t_wf_reify
theorem bn_shl_wf : Func.Wf bn_shl_body := by t_wf_reify
theorem bn_shr_wf : Func.Wf bn_shr_body := by t_wf_reify
theorem bn_divmod_wf : Func.Wf bn_divmod_body := by t_wf_reify
theorem bn_nat_pow_wf : Func.Wf bn_nat_pow_body := by t_wf_reify
theorem bn_nat_gcd_wf : Func.Wf bn_nat_gcd_body := by t_wf_reify
theorem lcnf_nat_arith_wf : Func.Wf lcnf_nat_arith_body := by t_wf_reify
theorem lcnf_nat_bits_wf : Func.Wf lcnf_nat_bits_body := by t_wf_reify
theorem lcnf_nat_slow_wf : Func.Wf lcnf_nat_slow_body := by t_wf_reify
theorem lcnf_int_conv_wf : Func.Wf lcnf_int_conv_body := by t_wf_reify
theorem lcnf_int_addsub_cmp_wf : Func.Wf lcnf_int_addsub_cmp_body := by t_wf_reify
theorem lcnf_int_muldiv_wf : Func.Wf lcnf_int_muldiv_body := by t_wf_reify
theorem lcnf_int_op_wf : Func.Wf lcnf_int_op_body := by t_wf_reify

theorem rtR1_fns_wf : ∀ f ∈ rtR1_fns, f.Wf := by
  intro f hf
  simp only [rtR1_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact rt_scratch_wf
  · exact rt_scratch_cap_wf
  · exact lcnf_nat_alloc_wf
  · exact bn_dec_nat_wf
  · exact bn_require_scratch_wf
  · exact bn_trim_wf
  · exact bn_copy_wf
  · exact bn_zero_wf
  · exact bn_nat_from_limbs_wf
  · exact bn_int_from_limbs_wf
  · exact bn_nat_len_wf
  · exact bn_int_len_wf
  · exact bn_load_nat_wf
  · exact bn_load_int_wf
  · exact bn_cmp_fixed_wf
  · exact bn_cmp_wf
  · exact bn_add_wf
  · exact bn_add_one_wf
  · exact bn_sub_wf
  · exact bn_sub_one_wf
  · exact bn_mul_wf
  · exact bn_bitwise_wf
  · exact bn_shl_wf
  · exact bn_shr_wf
  · exact bn_divmod_wf
  · exact bn_nat_pow_wf
  · exact bn_nat_gcd_wf
  · exact lcnf_nat_arith_wf
  · exact lcnf_nat_bits_wf
  · exact lcnf_nat_slow_wf
  · exact lcnf_int_conv_wf
  · exact lcnf_int_addsub_cmp_wf
  · exact lcnf_int_muldiv_wf
  · exact lcnf_int_op_wf

def rtR1Mod : LeanQbe.T.Module :=
  { fns := rtR1_fns
    externs :=
      [ { name := "lcnf_alloc", as := [i64, i64], rs := [i64] }
      , { name := "lcnf_dec_ref_cold", as := [i64, i64], rs := [] } ]
    exits := ["lcnf_panic"] }

theorem rtR1_checkAcyclic : rtR1Mod.checkAcyclic = true := by
  t_kernel_rfl

end LeanQbe.T.LeanLCNF
