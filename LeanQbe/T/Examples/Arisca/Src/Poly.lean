/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Arisca.Src.Header
meta import LeanQbe.T.Examples.Arisca.Src.Header

/-!
# ARiSCA Baseline Polynomial Engine (`Arisca/Src/Poly.lean`)

Implements the baseline (`!ARISCA_LSM`) SoA polynomial engine:
- Graded-lex monomial comparison (`ar_mcmp`), binary membership (`ar_mhas_from`), 64-bit Bloom
  signature (`ar_sigbit`, `ar_msig`), registered vanishing-pair check (`ar_mvanish`), and
  monomial union (`ar_munion`)
- Ping-pong monomial pool compaction (`ar_compact`)
- Iterative merge-sort + combine (`ar_sort_combine`), galloping merge (`ar_gallop`,
  `ar_merge_products`), and substitution (`ar_apply`)
- Initial specification polynomial (`ar_add_q`, `ar_build_sp0`), cone rule load/store
  (`ar_load_rule`, `ar_store_rule`), and `FLIP`-aware `R` expansion (`ar_build_R`).

Strictly data-pure (`0` `*Proof*`/`*Spec*`/`*Lemmas*`/`Amd64`/`Arm64`/`Kraken` imports).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Arisca.Src.Poly

open LeanQbe.T
open LeanQbe.T.Examples.Arisca.Src

@[expose] public section

arisca_c0! arisca_poly "
#include \"arisca_internal.h\"

extern ar_u64_u64 ar_cmul(ArCtx *cx, u64 al, u64 ah, u64 bl, u64 bh);
extern ar_u64_u64 ar_cadd(ArCtx *cx, u64 al, u64 ah, u64 bl, u64 bh);
extern ar_u64_u64 ar_cneg(ArCtx *cx, u64 al, u64 ah);
extern ar_u64_u64 ar_cpow2(ArCtx *cx, u32 e);

i32 ar_mcmp(const u32 *a, const u32 *b) {
  u32 la = a[0];
  u32 lb = b[0];
  if (la != lb) {
    return (la < lb) ? -1 : 1;
  }
  u32 i = 1u;
  while (i <= la) {
    if (a[i] != b[i]) {
      return (a[i] < b[i]) ? -1 : 1;
    }
    i = i + 1u;
  }
  return 0;
}

bool ar_mhas_from(const u32 *m, u32 lo, u32 s) {
  u32 hi = m[0] + 1u;
  while (lo < hi) {
    u32 mid = lo + ((hi - lo) >> 1);
    if (m[mid] < s) {
      lo = mid + 1u;
    } else {
      hi = mid;
    }
  }
  return lo <= m[0] && m[lo] == s;
}

u64 ar_sigbit(u32 sym) {
  return 1ULL << ((sym * 0x9E3779B1u) >> 26);
}

u64 ar_msig(const u32 *m) {
  u64 g = 0ULL;
  u32 len = m[0];
  u32 i = 1u;
  while (i <= len) {
    g = g | ar_sigbit(m[i]);
    i = i + 1u;
  }
  return g;
}

bool ar_mvanish(ArCtx *cx, const u32 *m) {
  u32 len = m[0];
  u32 i = 1u;
  while (i <= len) {
    u32 x = m[i];
    if ((x & 1u) == 0u) {
      u32 v = x >> 1;
      if (v < cx->n_nets) {
        u32 p = cx->partner[v];
        if (p != AR_NONE && 2u * p > x && ar_mhas_from(m, i + 1u, 2u * p)) {
          return true;
        }
      }
    }
    i = i + 1u;
  }
  return false;
}

u64 ar_munion(u32 *out, const u32 *a, u32 s, const u32 *b) {
  u32 i = 1u;
  u32 j = 1u;
  u32 k = 1u;
  u32 la = a[0];
  u32 lb = b[0];
  u64 g = 0ULL;
  while (i <= la || j <= lb) {
    if (i <= la && a[i] == s) {
      i = i + 1u;
      continue;
    }
    u32 x = 0u;
    if (j > lb) {
      x = a[i];
      i = i + 1u;
    } else if (i > la) {
      x = b[j];
      j = j + 1u;
    } else if (a[i] < b[j]) {
      x = a[i];
      i = i + 1u;
    } else if (a[i] > b[j]) {
      x = b[j];
      j = j + 1u;
    } else {
      x = a[i];
      i = i + 1u;
      j = j + 1u;
    }
    out[k] = x;
    k = k + 1u;
    g = g | ar_sigbit(x);
  }
  out[0] = k - 1u;
  return g;
}

void ar_compact(ArCtx *cx) {
  u32 *src = cx->pool[cx->pc];
  u32 *dst = cx->pool[cx->pc ^ 1u];
  u32 *tm = cx->tm[cx->tc];
  u64 k = 0ULL;
  u32 i = 0u;
  while (i < cx->tn) {
    const u32 *m = src + tm[i];
    u32 len = m[0];
    u32 j = 0u;
    while (j <= len) {
      dst[k + (u64)j] = m[j];
      j = j + 1u;
    }
    tm[i] = (u32)k;
    k = k + (u64)len + 1ULL;
    i = i + 1u;
  }
  cx->pc = cx->pc ^ 1u;
  cx->ptop = k;
}

u32 ar_sort_combine(ArCtx *cx) {
  u32 n = cx->qn;
  u32 *a = cx->ix;
  u32 *b = cx->ix2;
  const u32 *pool = cx->pool[cx->pc];
  const u32 *qm = cx->qm;
  u32 i = 0u;
  while (i < n) {
    a[i] = i;
    i = i + 1u;
  }
  i = 0u;
  while (i < n) {
    u32 e = ((n - i) < 16u) ? n : (i + 16u);
    u32 j = i + 1u;
    while (j < e) {
      u32 x = a[j];
      u32 q = j;
      while (q > i && ar_mcmp(pool + qm[a[q - 1u]], pool + qm[x]) > 0) {
        a[q] = a[q - 1u];
        q = q - 1u;
      }
      a[q] = x;
      j = j + 1u;
    }
    i = i + 16u;
  }
  u64 w = 16ULL;
  while (w < (u64)n) {
    u64 lo = 0ULL;
    while (lo < (u64)n) {
      u32 mid = ((lo + w) < (u64)n) ? (u32)(lo + w) : n;
      u32 hi = ((lo + 2ULL * w) < (u64)n) ? (u32)(lo + 2ULL * w) : n;
      u32 p = (u32)lo;
      u32 q = mid;
      u32 o = (u32)lo;
      while (p < mid && q < hi) {
        if (ar_mcmp(pool + qm[a[p]], pool + qm[a[q]]) <= 0) {
          b[o] = a[p];
          o = o + 1u;
          p = p + 1u;
        } else {
          b[o] = a[q];
          o = o + 1u;
          q = q + 1u;
        }
      }
      while (p < mid) {
        b[o] = a[p];
        o = o + 1u;
        p = p + 1u;
      }
      while (q < hi) {
        b[o] = a[q];
        o = o + 1u;
        q = q + 1u;
      }
      lo = lo + 2ULL * w;
    }
    u32 *t = a;
    a = b;
    b = t;
    w = w * 2ULL;
  }
  cx->ix = a;
  cx->ix2 = b;
  u32 k = 0u;
  i = 0u;
  while (i < n) {
    u32 h0 = a[i];
    u64 l = cx->ql[h0];
    u64 h = cx->qh[h0];
    u32 j = i + 1u;
    while (j < n && ar_mcmp(pool + qm[a[j]], pool + qm[h0]) == 0) {
      C0_TIE2(l, h, ar_cadd(cx, l, h, cx->ql[a[j]], cx->qh[a[j]]));
      j = j + 1u;
    }
    if (l != 0ULL || h != 0ULL) {
      cx->ql[h0] = l;
      cx->qh[h0] = h;
      a[k] = h0;
      k = k + 1u;
    }
    i = j;
  }
  return k;
}

u32 ar_gallop(const u32 *tm, const u32 *pool, u32 lo, u32 n, const u32 *q) {
  u64 base = (u64)lo;
  u64 step = 1ULL;
  u64 hi = (u64)n;
  while (true) {
    u64 p = base + step - 1ULL;
    if (p >= (u64)n) {
      hi = (u64)n;
      break;
    }
    if (ar_mcmp(pool + tm[p], q) < 0) {
      base = p + 1ULL;
      step = step << 1;
    } else {
      hi = p;
      break;
    }
  }
  u64 l = base;
  u64 h = hi;
  while (l < h) {
    u64 mid = l + ((h - l) >> 1);
    if (ar_mcmp(pool + tm[mid], q) < 0) {
      l = mid + 1ULL;
    } else {
      h = mid;
    }
  }
  return (u32)l;
}

void ar_merge_products(ArCtx *cx, u32 nb) {
  u32 k = ar_sort_combine(cx);
  u32 sidx = cx->tc;
  u32 didx = cx->tc ^ 1u;
  const u32 *sm = cx->tm[sidx];
  const u64 *ss = cx->ts[sidx];
  const u64 *sl = cx->tl[sidx];
  const u64 *sh = cx->th[sidx];
  u32 *dm = cx->tm[didx];
  u64 *ds = cx->ts[didx];
  u64 *dl = cx->tl[didx];
  u64 *dh = cx->th[didx];
  const u32 *pool = cx->pool[cx->pc];
  const u32 *bx = cx->bx;
  u32 n = cx->tn;
  u32 o = 0u;
  u32 cur = 0u;
  u32 bp = 0u;
  u32 pi = 0u;
  while (pi <= k) {
    u32 a = 0u;
    u32 j = n;
    const u32 *qmono = NULL;
    if (pi < k) {
      a = cx->ix[pi];
      qmono = pool + cx->qm[a];
      j = ar_gallop(sm, pool, cur, n, qmono);
    }
    while (cur < j) {
      u32 e = (bp < nb && bx[bp] < j) ? bx[bp] : j;
      u32 i = cur;
      while (i < e) {
        dm[o] = sm[i];
        ds[o] = ss[i];
        dl[o] = sl[i];
        dh[o] = sh[i];
        o = o + 1u;
        i = i + 1u;
      }
      if (e < j) {
        cur = e + 1u;
        bp = bp + 1u;
      } else {
        cur = j;
      }
    }
    if (pi == k) {
      break;
    }
    if (j < n && ar_mcmp(pool + sm[j], qmono) == 0 && !(bp < nb && bx[bp] == j)) {
      u64 l = 0ULL;
      u64 h = 0ULL;
      C0_TIE2(l, h, ar_cadd(cx, sl[j], sh[j], cx->ql[a], cx->qh[a]));
      if (l != 0ULL || h != 0ULL) {
        dm[o] = sm[j];
        ds[o] = ss[j];
        dl[o] = l;
        dh[o] = h;
        o = o + 1u;
      }
      cur = j + 1u;
    } else {
      dm[o] = cx->qm[a];
      ds[o] = cx->qs[a];
      dl[o] = cx->ql[a];
      dh[o] = cx->qh[a];
      o = o + 1u;
    }
    pi = pi + 1u;
  }
  cx->tc = didx;
  cx->tn = o;
}

bool ar_apply(ArCtx *cx, u32 s) {
  const u32 *Rm = cx->cur_rm;
  const u64 *Rl = cx->cur_rl;
  const u64 *Rh = cx->cur_rh;
  const u32 *Rp = cx->cur_rp;
  u32 nR = cx->cur_nr;
  u32 n = cx->tn;
  u32 nb = 0u;
  u64 slB = 0ULL;
  u64 slR = 0ULL;
  u64 bit = ar_sigbit(s);
  const u32 *tm0 = cx->tm[cx->tc];
  const u32 *pool0 = cx->pool[cx->pc];
  const u64 *ts0 = cx->ts[cx->tc];
  u32 *bx = cx->bx;
  u32 i = 0u;
  while (i < n) {
    if ((ts0[i] & bit) != 0ULL) {
      const u32 *m = pool0 + tm0[i];
      if (ar_mhas_from(m, 1u, s)) {
        bx[nb] = i;
        nb = nb + 1u;
        slB = slB + (u64)m[0];
      }
    }
    i = i + 1u;
  }
  if (nb == 0u) {
    return true;
  }
  u32 r = 0u;
  while (r < nR) {
    slR = slR + (u64)Rp[Rm[r]];
    r = r + 1u;
  }
  u64 nprod = (u64)nb * (u64)nR;
  if (nprod > (u64)cx->qcap) { return false; }
  if ((u64)n - (u64)nb + nprod > (u64)cx->tcap) { return false; }
  u64 need = (u64)nR * slB + (u64)nb * slR;
  if (need > cx->pcap) { return false; }
  if (cx->ptop > cx->pcap - need) {
    ar_compact(cx);
    if (cx->ptop > cx->pcap || need > cx->pcap - cx->ptop) {
      return false;
    }
  }
  if ((u64)nR > (u64)cx->qcap) { return false; }
  u64 q = 0ULL;
  r = 0u;
  while (r < nR) {
    const u32 *mr = Rp + Rm[r];
    cx->vq_off[r] = (u32)q;
    u8 sk = ar_mvanish(cx, mr) ? (u8)1 : (u8)0;
    cx->vq_skip[r] = sk;
    if (sk == (u8)0) {
      u32 mlen = mr[0];
      u32 k = 1u;
      while (k <= mlen) {
        u32 x = mr[k];
        if ((x & 1u) == 0u) {
          u32 v = x >> 1;
          if (v < cx->n_nets) {
            u32 p = cx->partner[v];
            if (p != AR_NONE && 2u * p != s) {
              if (q >= cx->pcap) { return false; }
              cx->vq[q] = 2u * p;
              q = q + 1ULL;
            }
          }
        }
        k = k + 1u;
      }
    }
    r = r + 1u;
  }
  cx->vq_off[nR] = (u32)q;

  u32 *pool = cx->pool[cx->pc];
  const u32 *tm = cx->tm[cx->tc];
  const u64 *tl = cx->tl[cx->tc];
  const u64 *th = cx->th[cx->tc];
  u32 qn = 0u;
  u64 pt = cx->ptop;
  u32 b = 0u;
  while (b < nb) {
    u32 ti = bx[b];
    const u32 *m = pool + tm[ti];
    u64 cl = tl[ti];
    u64 ch = th[ti];
    r = 0u;
    while (r < nR) {
      if (cx->vq_skip[r] == (u8)0) {
        u64 l = 0ULL;
        u64 h = 0ULL;
        C0_TIE2(l, h, ar_cmul(cx, cl, ch, Rl[r], Rh[r]));
        if (l != 0ULL || h != 0ULL) {
          u32 q1 = cx->vq_off[r + 1u];
          u32 qq = cx->vq_off[r];
          bool van = false;
          while (qq < q1 && !van) {
            van = ar_mhas_from(m, 1u, cx->vq[qq]);
            qq = qq + 1u;
          }
          if (!van) {
            u32 *out = pool + pt;
            u64 g = ar_munion(out, m, s, Rp + Rm[r]);
            cx->qm[qn] = (u32)pt;
            cx->qs[qn] = g;
            cx->ql[qn] = l;
            cx->qh[qn] = h;
            qn = qn + 1u;
            pt = pt + (u64)out[0] + 1ULL;
          }
        }
      }
      r = r + 1u;
    }
    b = b + 1u;
  }
  cx->ptop = pt;
  cx->qn = qn;
  ar_merge_products(cx, nb);
  return true;
}

bool ar_add_q(ArCtx *cx, u32 len, u32 s0, u32 s1, u64 l, u64 h) {
  if (l == 0ULL && h == 0ULL) {
    return true;
  }
  if (len > 2u || cx->qn >= cx->qcap || cx->ptop > cx->pcap ||
      (u64)len + 1ULL > cx->pcap - cx->ptop) {
    return false;
  }
  u32 *pool = cx->pool[cx->pc];
  u32 *out = pool + cx->ptop;
  out[0] = len;
  if (len >= 1u) { out[1] = s0; }
  if (len >= 2u) { out[2] = s1; }
  if (ar_mvanish(cx, out)) {
    return true;
  }
  cx->qm[cx->qn] = (u32)cx->ptop;
  cx->qs[cx->qn] = ar_msig(out);
  cx->ql[cx->qn] = l;
  cx->qh[cx->qn] = h;
  cx->qn = cx->qn + 1u;
  cx->ptop = cx->ptop + (u64)len + 1ULL;
  return true;
}

bool ar_build_sp0(ArCtx *cx) {
  u32 n = cx->n_in >> 1;
  cx->tn = 0u;
  cx->ptop = 0ULL;
  cx->qn = 0u;
  u32 j = 0u;
  while (j < cx->n_out) {
    u32 rf = cx->out_ref[j];
    u32 sy0 = 2u * (rf >> 1);
    u64 l = 0ULL;
    u64 h = 0ULL;
    C0_TIE2(l, h, ar_cpow2(cx, j));
    if ((rf & 1u) != 0u) {
      if (!ar_add_q(cx, 0u, 0u, 0u, l, h)) { return false; }
      C0_TIE2(l, h, ar_cneg(cx, l, h));
      if (!ar_add_q(cx, 1u, sy0, 0u, l, h)) { return false; }
    } else {
      if (!ar_add_q(cx, 1u, sy0, 0u, l, h)) { return false; }
    }
    j = j + 1u;
  }
  u32 i = 0u;
  while (i < n) {
    u32 k = 0u;
    while (k < n) {
      if (i + k < cx->n_out) {
        u32 xa = 2u * cx->in_net[i];
        u32 xb = 2u * cx->in_net[n + k];
        u64 l = 0ULL;
        u64 h = 0ULL;
        C0_TIE2(l, h, ar_cpow2(cx, i + k));
        bool is_neg = (cx->spec == 1u) && ((i == n - 1u) != (k == n - 1u));
        if (!is_neg) {
          C0_TIE2(l, h, ar_cneg(cx, l, h));
        }
        u32 sy0 = (xa < xb) ? xa : xb;
        u32 sy1 = (xa < xb) ? xb : xa;
        u32 len = (xa == xb) ? 1u : 2u;
        if (!ar_add_q(cx, len, sy0, sy1, l, h)) { return false; }
      }
      k = k + 1u;
    }
    i = i + 1u;
  }
  if (cx->qn > cx->tcap) {
    return false;
  }
  ar_merge_products(cx, 0u);
  return true;
}

bool ar_load_rule(ArCtx *cx, u32 v) {
  u32 off = cx->rule_off[v];
  u32 cnt = cx->rule_n[v];
  cx->tn = 0u;
  cx->ptop = 0ULL;
  cx->qn = 0ULL;
  if (cnt > cx->tcap) {
    return false;
  }
  u32 *pool = cx->pool[cx->pc];
  u32 *tm = cx->tm[cx->tc];
  u64 *ts = cx->ts[cx->tc];
  u64 *tl = cx->tl[cx->tc];
  u64 *th = cx->th[cx->tc];
  u32 i = 0u;
  while (i < cnt) {
    const u32 *m = cx->rs_pool + cx->rs_m[off + i];
    u32 mlen = m[0];
    if (cx->ptop > cx->pcap || (u64)mlen + 1ULL > cx->pcap - cx->ptop) {
      return false;
    }
    u32 j = 0u;
    while (j <= mlen) {
      pool[cx->ptop + (u64)j] = m[j];
      j = j + 1u;
    }
    tm[i] = (u32)cx->ptop;
    ts[i] = ar_msig(m);
    tl[i] = cx->rs_l[off + i];
    th[i] = cx->rs_h[off + i];
    cx->ptop = cx->ptop + (u64)mlen + 1ULL;
    i = i + 1u;
  }
  cx->tn = cnt;
  return true;
}

bool ar_store_rule(ArCtx *cx, u32 v) {
  u32 off = cx->rs_n;
  const u32 *pool = cx->pool[cx->pc];
  const u32 *tm = cx->tm[cx->tc];
  const u64 *tl = cx->tl[cx->tc];
  const u64 *th = cx->th[cx->tc];
  u32 i = 0u;
  while (i < cx->tn) {
    const u32 *m = pool + tm[i];
    u32 mlen = m[0];
    if (cx->rs_n >= cx->rs_cap || cx->rs_ptop > cx->rs_pcap ||
        (u64)mlen + 1ULL > cx->rs_pcap - cx->rs_ptop) {
      return false;
    }
    cx->rs_m[cx->rs_n] = (u32)cx->rs_ptop;
    cx->rs_l[cx->rs_n] = tl[i];
    cx->rs_h[cx->rs_n] = th[i];
    u32 j = 0u;
    while (j <= mlen) {
      cx->rs_pool[cx->rs_ptop + (u64)j] = m[j];
      j = j + 1u;
    }
    cx->rs_ptop = cx->rs_ptop + (u64)mlen + 1ULL;
    cx->rs_n = cx->rs_n + 1u;
    i = i + 1u;
  }
  cx->rule_off[v] = off;
  cx->rule_n[v] = cx->tn;
  return true;
}

bool ar_build_R(ArCtx *cx, u32 v) {
  u32 off = cx->rule_off[v];
  u32 cnt = cx->rule_n[v];
  u8 fv = cx->flipped[v];
  bool fv_b = fv != (u8)0;
  bool any = false;
  u64 bt = fv_b ? 1ULL : 0ULL;
  u64 bw = fv_b ? 1ULL : 0ULL;
  u32 i = 0u;
  while (i < cnt) {
    const u32 *m = cx->rs_pool + cx->rs_m[off + i];
    u32 mlen = m[0];
    u32 f = 0u;
    u32 j = 1u;
    while (j <= mlen) {
      u32 x = m[j];
      if ((x & 1u) == 0u && cx->flipped[x >> 1] != (u8)0) {
        f = f + 1u;
      }
      j = j + 1u;
    }
    if (f > AR_R_MAXF) { return false; }
    if (f != 0u) { any = true; }
    bt = bt + (1ULL << f);
    bw = bw + (1ULL << f) * ((u64)mlen + 1ULL);
    i = i + 1u;
  }
  if (!any && !fv_b) {
    cx->cur_rm = cx->rs_m + off;
    cx->cur_rl = cx->rs_l + off;
    cx->cur_rh = cx->rs_h + off;
    cx->cur_rp = cx->rs_pool;
    cx->cur_nr = cnt;
    return true;
  }
  if (bt > (u64)cx->rcap || bt > (u64)cx->qcap || bw > cx->rpcap) {
    return false;
  }
  u64 rp = 0ULL;
  u32 n = 0u;
  if (fv_b) {
    cx->rpool[0] = 0u;
    cx->rm[0] = 0u;
    cx->rl[0] = 1ULL & cx->mlo;
    cx->rh[0] = 0ULL;
    rp = 1ULL;
    n = 1u;
  }
  i = 0u;
  while (i < cnt) {
    const u32 *m = cx->rs_pool + cx->rs_m[off + i];
    u32 mlen = m[0];
    u64 cl = cx->rs_l[off + i];
    u64 ch = cx->rs_h[off + i];
    u32 f = 0u;
    u32 j = 1u;
    while (j <= mlen) {
      u32 x = m[j];
      if ((x & 1u) == 0u && cx->flipped[x >> 1] != (u8)0) {
        f = f + 1u;
      }
      j = j + 1u;
    }
    u64 nS = 1ULL << f;
    u64 S = 0ULL;
    while (S < nS) {
      u32 *out = cx->rpool + rp;
      u32 k = 1u;
      u32 fi = 0u;
      u32 par = 0u;
      u64 l = cl;
      u64 h = ch;
      j = 1u;
      while (j <= mlen) {
        u32 x = m[j];
        if ((x & 1u) == 0u && cx->flipped[x >> 1] != (u8)0) {
          u32 bitS = (u32)((S >> fi) & 1ULL);
          fi = fi + 1u;
          if (bitS == 0u) {
            j = j + 1u;
            continue;
          }
          x = x + 1u;
          par = par ^ 1u;
        }
        if (k > 1u && out[k - 1u] == x) {
          j = j + 1u;
          continue;
        }
        out[k] = x;
        k = k + 1u;
        j = j + 1u;
      }
      out[0] = k - 1u;
      u32 fvu = fv_b ? 1u : 0u;
      if ((par ^ fvu) != 0u) {
        C0_TIE2(l, h, ar_cneg(cx, l, h));
      }
      cx->rm[n] = (u32)rp;
      cx->rl[n] = l;
      cx->rh[n] = h;
      n = n + 1u;
      rp = rp + (u64)k;
      S = S + 1ULL;
    }
    i = i + 1u;
  }
  u32 *a = cx->ix;
  u32 *b2 = cx->ix2;
  i = 0u;
  while (i < n) {
    a[i] = i;
    i = i + 1u;
  }
  u64 w = 1ULL;
  while (w < (u64)n) {
    u64 lo = 0ULL;
    while (lo < (u64)n) {
      u32 mid = ((lo + w) < (u64)n) ? (u32)(lo + w) : n;
      u32 hi = ((lo + 2ULL * w) < (u64)n) ? (u32)(lo + 2ULL * w) : n;
      u32 p = (u32)lo;
      u32 q = mid;
      u32 o = (u32)lo;
      while (p < mid && q < hi) {
        if (ar_mcmp(cx->rpool + cx->rm[a[p]], cx->rpool + cx->rm[a[q]]) <= 0) {
          b2[o] = a[p];
          o = o + 1u;
          p = p + 1u;
        } else {
          b2[o] = a[q];
          o = o + 1u;
          q = q + 1u;
        }
      }
      while (p < mid) {
        b2[o] = a[p];
        o = o + 1u;
        p = p + 1u;
      }
      while (q < hi) {
        b2[o] = a[q];
        o = o + 1u;
        q = q + 1u;
      }
      lo = lo + 2ULL * w;
    }
    u32 *t = a;
    a = b2;
    b2 = t;
    w = w * 2ULL;
  }
  u32 k2 = 0u;
  i = 0u;
  while (i < n) {
    u32 h0 = a[i];
    u64 l = cx->rl[h0];
    u64 h = cx->rh[h0];
    u32 j = i + 1u;
    while (j < n && ar_mcmp(cx->rpool + cx->rm[a[j]], cx->rpool + cx->rm[h0]) == 0) {
      C0_TIE2(l, h, ar_cadd(cx, l, h, cx->rl[a[j]], cx->rh[a[j]]));
      j = j + 1u;
    }
    if (l != 0ULL || h != 0ULL) {
      cx->rm2[k2] = cx->rm[h0];
      cx->rl2[k2] = l;
      cx->rh2[k2] = h;
      k2 = k2 + 1u;
    }
    i = j;
  }
  cx->cur_rm = cx->rm2;
  cx->cur_rl = cx->rl2;
  cx->cur_rh = cx->rh2;
  cx->cur_rp = cx->rpool;
  cx->cur_nr = k2;
  return true;
}
"

/-- Ordered live functions of `Arisca/Src/Poly.lean` (`16` fns). -/
def fns : List Fn := arisca_poly_fns

end

public section

theorem ar_mcmp_wf : Func.Wf ar_mcmp_body := by arisca_wf_reify
theorem ar_mhas_from_wf : Func.Wf ar_mhas_from_body := by arisca_wf_reify
theorem ar_sigbit_wf : Func.Wf ar_sigbit_body := by arisca_wf_reify
theorem ar_msig_wf : Func.Wf ar_msig_body := by arisca_wf_reify
theorem ar_mvanish_wf : Func.Wf ar_mvanish_body := by arisca_wf_reify
theorem ar_munion_wf : Func.Wf ar_munion_body := by arisca_wf_reify
theorem ar_compact_wf : Func.Wf ar_compact_body := by arisca_wf_reify
theorem ar_sort_combine_wf : Func.Wf ar_sort_combine_body := by arisca_wf_reify
theorem ar_gallop_wf : Func.Wf ar_gallop_body := by arisca_wf_reify
theorem ar_merge_products_wf : Func.Wf ar_merge_products_body := by arisca_wf_reify
theorem ar_apply_wf : Func.Wf ar_apply_body := by arisca_wf_reify
theorem ar_add_q_wf : Func.Wf ar_add_q_body := by arisca_wf_reify
theorem ar_build_sp0_wf : Func.Wf ar_build_sp0_body := by arisca_wf_reify
theorem ar_load_rule_wf : Func.Wf ar_load_rule_body := by arisca_wf_reify
theorem ar_store_rule_wf : Func.Wf ar_store_rule_body := by arisca_wf_reify
theorem ar_build_R_wf : Func.Wf ar_build_R_body := by arisca_wf_reify

theorem fns_wf : ∀ f ∈ fns, f.Wf := by
  intro f hf
  simp only [fns, arisca_poly_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  · exact ar_mcmp_wf
  · exact ar_mhas_from_wf
  · exact ar_sigbit_wf
  · exact ar_msig_wf
  · exact ar_mvanish_wf
  · exact ar_munion_wf
  · exact ar_compact_wf
  · exact ar_sort_combine_wf
  · exact ar_gallop_wf
  · exact ar_merge_products_wf
  · exact ar_apply_wf
  · exact ar_add_q_wf
  · exact ar_build_sp0_wf
  · exact ar_load_rule_wf
  · exact ar_store_rule_wf
  · exact ar_build_R_wf

end

end LeanQbe.T.Examples.Arisca.Src.Poly
