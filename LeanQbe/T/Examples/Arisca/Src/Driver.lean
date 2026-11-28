/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
import LeanQbe.T.Examples.Arisca.Src.Header
meta import LeanQbe.T.Examples.Arisca.Src.Header

/-!
# ARiSCA Gate Validator, Cone Reducer, & Top-Level Entrypoint (`Arisca/Src/Driver.lean`)

Implements:
- `ar_ttsim`: explicit-stack 6-variable `u64` truth-table simulator (64-AND memo budget)
- `ar_dzero`, `ar_dlit`, `ar_dmul`, `ar_daxpy`, `ar_dcanon`, `ar_install_rule`, `ar_mask6`,
  `ar_do_gate`: dense 16-term gate polynomial builder, truth-table validation (incl. explicit-leaf
  mode), and HA vanishing-pair registration
- `ar_do_cone`: cone root load, substitution loop, and rule-store append
- `ar_setup_dynamic`, `ar_check_main`, and exported `arisca_check_bytes(aig_ptr, aig_len, art_ptr,
  art_len, work_ptr, work_len)` returning `20ULL` (accept) or `0ULL` (reject).

Strictly data-pure (`0` `*Proof*`/`*Spec*`/`*Lemmas*`/`Amd64`/`Arm64`/`Kraken` imports).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Arisca.Src.Driver

open LeanQbe.T
open LeanQbe.T.Examples.Arisca.Src

@[expose] public section

arisca_c0! arisca_driver "
#include \"arisca_internal.h\"

extern ar_bool_u32 ar_next_word(ArCtx *cx);
extern u8 *ar_aalloc(ArCtx *cx, u64 bytes);
extern ar_u64_u64 ar_cadd(ArCtx *cx, u64 al, u64 ah, u64 bl, u64 bh);
extern ar_u64_u64 ar_cneg(ArCtx *cx, u64 al, u64 ah);
extern ar_u64_u64 ar_cfrom_small(ArCtx *cx, u64 v);

extern bool ar_parse_aig(ArCtx *cx, const u8 *b, u64 n);
extern bool ar_parse_art_header_and_tables(ArCtx *cx, u8 *art, u64 art_len);

extern i32 ar_mcmp(const u32 *a, const u32 *b);
extern bool ar_mvanish(ArCtx *cx, const u32 *m);
extern bool ar_apply(ArCtx *cx, u32 s);
extern bool ar_build_sp0(ArCtx *cx);
extern bool ar_load_rule(ArCtx *cx, u32 v);
extern bool ar_store_rule(ArCtx *cx, u32 v);
extern bool ar_build_R(ArCtx *cx, u32 v);

ar_bool_u64 ar_ttsim(ArCtx *cx, u32 lit, u32 nleaf, u64 all) {
  u32 sp = 1u;
  u32 nm = 0u;
  u32 nexp = 0u;
  u32 *sn = cx->stk_n;
  u32 *sph = cx->stk_p;
  u32 *mn = cx->memo_n;
  u64 *mv = cx->memo_v;
  sn[0] = lit >> 1;
  sph[0] = 0u;
  while (sp > 0u) {
    u32 nd = sn[sp - 1u];
    bool known = false;
    u32 j = 0u;
    while (j < nleaf) {
      if (cx->g_lnode[j] == nd) { known = true; }
      j = j + 1u;
    }
    if (!known && nd == 0u) { known = true; }
    if (!known) {
      j = 0u;
      while (j < nm) {
        if (mn[j] == nd) { known = true; }
        j = j + 1u;
      }
    }
    if (known) {
      sp = sp - 1u;
      continue;
    }
    if (nd <= cx->I || nd > cx->M) {
      return C0_TUP2(ar_bool_u64, false, 0ULL);
    }
    u32 idx = nd - cx->I - 1u;
    u32 a = cx->rhs0[idx];
    u32 b = cx->rhs1[idx];
    if (sph[sp - 1u] == 0u) {
      sph[sp - 1u] = 1u;
      nexp = nexp + 1u;
      if (nexp > AR_TT_MAX_AND) { return C0_TUP2(ar_bool_u64, false, 0ULL); }
      if (sp + 2u > AR_TT_STK) { return C0_TUP2(ar_bool_u64, false, 0ULL); }
      sn[sp] = a >> 1;
      sph[sp] = 0u;
      sp = sp + 1u;
      sn[sp] = b >> 1;
      sph[sp] = 0u;
      sp = sp + 1u;
    } else {
      u64 va = 0ULL;
      u64 vb = 0ULL;
      u32 an = a >> 1;
      u32 bn = b >> 1;
      bool fa = false;
      bool fb = false;
      j = 0u;
      while (j < nleaf) {
        if (!fa && cx->g_lnode[j] == an) { va = cx->g_lmask[j]; fa = true; }
        if (!fb && cx->g_lnode[j] == bn) { vb = cx->g_lmask[j]; fb = true; }
        j = j + 1u;
      }
      if (!fa && an == 0u) { va = 0ULL; fa = true; }
      if (!fb && bn == 0u) { vb = 0ULL; fb = true; }
      j = 0u;
      while (j < nm) {
        if (!fa && mn[j] == an) { va = mv[j]; fa = true; }
        if (!fb && mn[j] == bn) { vb = mv[j]; fb = true; }
        j = j + 1u;
      }
      if (!fa || !fb) { return C0_TUP2(ar_bool_u64, false, 0ULL); }
      if ((a & 1u) != 0u) { va = (~va) & all; }
      if ((b & 1u) != 0u) { vb = (~vb) & all; }
      if (nm >= AR_TT_MAX_AND) { return C0_TUP2(ar_bool_u64, false, 0ULL); }
      mn[nm] = nd;
      mv[nm] = va & vb;
      nm = nm + 1u;
      sp = sp - 1u;
    }
  }
  u32 nd = lit >> 1;
  bool f = false;
  u64 v = 0ULL;
  u32 j = 0u;
  while (j < nleaf) {
    if (!f && cx->g_lnode[j] == nd) { v = cx->g_lmask[j]; f = true; }
    j = j + 1u;
  }
  if (!f && nd == 0u) { v = 0ULL; f = true; }
  j = 0u;
  while (j < nm) {
    if (!f && mn[j] == nd) { v = mv[j]; f = true; }
    j = j + 1u;
  }
  if (!f) { return C0_TUP2(ar_bool_u64, false, 0ULL); }
  if ((lit & 1u) != 0u) { v = (~v) & all; }
  return C0_TUP2(ar_bool_u64, true, v);
}

void ar_dzero(u64 *d) {
  u32 i = 0u;
  while (i < 16u) {
    d[i] = 0ULL;
    i = i + 1u;
  }
}

void ar_dlit(u64 *d, u32 j, u32 neg) {
  ar_dzero(d);
  if (neg != 0u) {
    d[0] = 1ULL;
    d[1u << j] = 0ULL - 1ULL;
  } else {
    d[1u << j] = 1ULL;
  }
}

void ar_dmul(const u64 *a, const u64 *b, u64 *c) {
  ar_dzero(c);
  u32 i = 0u;
  while (i < 16u) {
    if (a[i] != 0ULL) {
      u32 j = 0u;
      while (j < 16u) {
        c[i | j] = c[i | j] + a[i] * b[j];
        j = j + 1u;
      }
    }
    i = i + 1u;
  }
}

void ar_daxpy(u64 *y, u64 k, const u64 *x) {
  u32 i = 0u;
  while (i < 16u) {
    y[i] = y[i] + k * x[i];
    i = i + 1u;
  }
}

u32 ar_dcanon(ArCtx *cx, const u64 *D) {
  u32 *T = cx->gsy;
  u32 n = 0u;
  u32 mask = 0u;
  while (mask < 16u) {
    if (D[mask] != 0ULL) {
      u64 l = 0ULL;
      u64 h = 0ULL;
      C0_TIE2(l, h, ar_cfrom_small(cx, D[mask]));
      if (l != 0ULL || h != 0ULL) {
        u32 *m = T + 5u * n;
        u32 len = 0u;
        u32 j = 0u;
        while (j < 4u) {
          if (((mask >> j) & 1u) != 0u) {
            u32 x = cx->g_vs[j];
            u32 q = len;
            while (q > 0u && m[q] > x) {
              q = q - 1u;
            }
            if (!(q > 0u && m[q] == x)) {
              u32 k = len;
              while (k > q) {
                m[k + 1u] = m[k];
                k = k - 1u;
              }
              m[q + 1u] = x;
              len = len + 1u;
            }
          }
          j = j + 1u;
        }
        m[0] = len;
        cx->gcl[n] = l;
        cx->gch[n] = h;
        n = n + 1u;
      }
    }
    mask = mask + 1u;
  }
  u32 i = 1u;
  while (i < n) {
    u32 *tmp = T + 80u;
    u64 tl = cx->gcl[i];
    u64 th = cx->gch[i];
    u32 k = 0u;
    while (k < 5u) {
      tmp[k] = T[5u * i + k];
      k = k + 1u;
    }
    u32 j = i;
    while (j > 0u && ar_mcmp(T + 5u * (j - 1u), tmp) > 0) {
      k = 0u;
      while (k < 5u) {
        T[5u * j + k] = T[5u * (j - 1u) + k];
        k = k + 1u;
      }
      cx->gcl[j] = cx->gcl[j - 1u];
      cx->gch[j] = cx->gch[j - 1u];
      j = j - 1u;
    }
    k = 0u;
    while (k < 5u) {
      T[5u * j + k] = tmp[k];
      k = k + 1u;
    }
    cx->gcl[j] = tl;
    cx->gch[j] = th;
    i = i + 1u;
  }
  u32 k = 0u;
  i = 0u;
  while (i < n) {
    u64 l = cx->gcl[i];
    u64 h = cx->gch[i];
    u32 j = i + 1u;
    while (j < n && ar_mcmp(T + 5u * j, T + 5u * i) == 0) {
      C0_TIE2(l, h, ar_cadd(cx, l, h, cx->gcl[j], cx->gch[j]));
      j = j + 1u;
    }
    if (l != 0ULL || h != 0ULL) {
      u32 q = 0u;
      while (q < 5u) {
        T[5u * k + q] = T[5u * i + q];
        q = q + 1u;
      }
      cx->gcl[k] = l;
      cx->gch[k] = h;
      k = k + 1u;
    }
    i = j;
  }
  return k;
}

bool ar_install_rule(ArCtx *cx, u32 o, u32 n) {
  u32 off = cx->rs_n;
  u32 cnt = 0u;
  u32 i = 0u;
  while (i < n) {
    const u32 *m = cx->gsy + 5u * i;
    if (!ar_mvanish(cx, m)) {
      u32 mlen = m[0];
      if (cx->rs_n >= cx->rs_cap || cx->rs_ptop > cx->rs_pcap ||
          (u64)mlen + 1ULL > cx->rs_pcap - cx->rs_ptop) {
        return false;
      }
      cx->rs_m[cx->rs_n] = (u32)cx->rs_ptop;
      cx->rs_l[cx->rs_n] = cx->gcl[i];
      cx->rs_h[cx->rs_n] = cx->gch[i];
      u32 j = 0u;
      while (j <= mlen) {
        cx->rs_pool[cx->rs_ptop + (u64)j] = m[j];
        j = j + 1u;
      }
      cx->rs_ptop = cx->rs_ptop + (u64)mlen + 1ULL;
      cx->rs_n = cx->rs_n + 1u;
      cnt = cnt + 1u;
    }
    i = i + 1u;
  }
  cx->rule_off[o] = off;
  cx->rule_n[o] = cnt;
  return true;
}

u64 ar_mask6(u32 j) {
  if (j == 0u) { return 0xAAAAAAAAAAAAAAAAULL; }
  if (j == 1u) { return 0xCCCCCCCCCCCCCCCCULL; }
  if (j == 2u) { return 0xF0F0F0F0F0F0F0F0ULL; }
  if (j == 3u) { return 0xFF00FF00FF00FF00ULL; }
  if (j == 4u) { return 0xFFFF0000FFFF0000ULL; }
  return 0xFFFFFFFF00000000ULL;
}

bool ar_do_gate(ArCtx *cx) {
  bool ok = false;
  u32 kraw = 0u;
  C0_TIE2(ok, kraw, ar_next_word(cx)); if (!ok) { return false; }
  u32 kind = kraw & 0xFFu;
  u32 expl = (kraw >> 8) & 1u;
  if ((kraw & (~0x1FFu)) != 0u || kind < 1u || kind > 7u) { return false; }
  u32 nout = (kind >= 6u) ? 2u : 1u;
  u32 nin = (kind == 1u || kind == 2u || kind == 3u || kind == 6u) ? 2u : 3u;
  u32 j = 0u;
  while (j < nout) {
    u32 outj = 0u;
    C0_TIE2(ok, outj, ar_next_word(cx)); if (!ok) { return false; }
    cx->g_outs[j] = outj;
    if (outj >= cx->n_nets) { return false; }
    u32 b = cx->bind[outj];
    if (b == AR_NONE || cx->rule_n[outj] != AR_NONE) { return false; }
    if ((b >> 1) >= 1u && (b >> 1) <= cx->I) { return false; }
    j = j + 1u;
  }
  if (nout == 2u && cx->g_outs[0] == cx->g_outs[1]) { return false; }
  j = 0u;
  while (j < nin) {
    u32 wd = 0u;
    C0_TIE2(ok, wd, ar_next_word(cx)); if (!ok) { return false; }
    u32 in_n = wd >> 1;
    cx->g_innet[j] = in_n;
    cx->g_inneg[j] = wd & 1u;
    if (in_n >= cx->n_nets || cx->bind[in_n] == AR_NONE) { return false; }
    cx->g_vs[j] = 2u * in_n;
    j = j + 1u;
  }
  u32 nl = nin;
  if (expl != 0u) {
    C0_TIE2(ok, nl, ar_next_word(cx)); if (!ok) { return false; }
    if (nl < 1u || nl > 6u) { return false; }
  }
  u64 all = (nl == 6u) ? (~0ULL) : ((1ULL << (1u << nl)) - 1ULL);
  j = 0u;
  while (j < nl) {
    u32 b = 0u;
    if (expl != 0u) {
      C0_TIE2(ok, b, ar_next_word(cx)); if (!ok) { return false; }
      if (b > 2u * cx->M + 1u) { return false; }
    } else {
      b = cx->bind[cx->g_innet[j]];
    }
    u32 nd = b >> 1;
    cx->g_lnode[j] = nd;
    u32 q = 0u;
    while (q < j) {
      if (cx->g_lnode[q] == nd) { return false; }
      q = q + 1u;
    }
    cx->g_lmask[j] = (ar_mask6(j) & all) ^ (((b & 1u) != 0u) ? all : 0ULL);
    j = j + 1u;
  }
  j = 0u;
  while (j < nin) {
    if (expl != 0u) {
      u64 tv = 0ULL;
      C0_TIE2(ok, tv, ar_ttsim(cx, cx->bind[cx->g_innet[j]], nl, all));
      if (!ok) { return false; }
      cx->g_tin[j] = tv;
    } else {
      cx->g_tin[j] = ar_mask6(j) & all;
    }
    j = j + 1u;
  }
  cx->g_vs[3] = 2u * cx->g_outs[0];
  if (nin == 2u) { cx->g_vs[2] = 0u; }
  j = 0u;
  while (j < nout) {
    u64 tv = 0ULL;
    C0_TIE2(ok, tv, ar_ttsim(cx, cx->bind[cx->g_outs[j]], nl, all));
    if (!ok) { return false; }
    cx->g_tto[j] = tv;
    j = j + 1u;
  }
  u64 *L0 = cx->dense;
  u64 *L1 = L0 + 16;
  u64 *L2 = L0 + 32;
  u64 *T1 = L0 + 48;
  u64 *T2 = L0 + 64;
  u64 *T3 = L0 + 80;
  u64 *Rc = L0 + 96;
  u64 *Rs = L0 + 112;
  ar_dlit(L0, 0u, cx->g_inneg[0]);
  ar_dlit(L1, 1u, cx->g_inneg[1]);
  if (nin == 3u) { ar_dlit(L2, 2u, cx->g_inneg[2]); } else { ar_dzero(L2); }
  ar_dzero(Rs);
  if (kind == 1u) {
    ar_dmul(L0, L1, Rc);
  } else if (kind == 2u || kind == 3u) {
    ar_dmul(L0, L1, T1);
    ar_dzero(Rc);
    ar_daxpy(Rc, 1ULL, L0);
    ar_daxpy(Rc, 1ULL, L1);
    u64 c23 = (kind == 2u) ? (0ULL - 1ULL) : (0ULL - 2ULL);
    ar_daxpy(Rc, c23, T1);
  } else if (kind == 4u || kind == 5u || kind == 7u) {
    ar_dzero(Rc);
    ar_dmul(L0, L1, T1);
    ar_daxpy(Rc, 1ULL, T1);
    ar_dmul(T1, L2, T3);
    ar_dmul(L0, L2, T2);
    ar_daxpy(Rc, 1ULL, T2);
    ar_dmul(L1, L2, T2);
    ar_daxpy(Rc, 1ULL, T2);
    if (kind == 4u) {
      ar_dzero(T1);
      ar_daxpy(T1, 1ULL, L0);
      ar_daxpy(T1, 1ULL, L1);
      ar_daxpy(T1, 1ULL, L2);
      ar_daxpy(T1, 0ULL - 2ULL, Rc);
      ar_daxpy(T1, 4ULL, T3);
      u32 q = 0u;
      while (q < 16u) {
        Rc[q] = T1[q];
        q = q + 1u;
      }
    } else {
      ar_daxpy(Rc, 0ULL - 2ULL, T3);
      if (kind == 7u) {
        ar_daxpy(Rs, 1ULL, L0);
        ar_daxpy(Rs, 1ULL, L1);
        ar_daxpy(Rs, 1ULL, L2);
        Rs[8] = Rs[8] + (0ULL - 2ULL);
      }
    }
  } else {
    ar_dmul(L0, L1, Rc);
    ar_daxpy(Rs, 1ULL, L0);
    ar_daxpy(Rs, 1ULL, L1);
    Rs[8] = Rs[8] + (0ULL - 2ULL);
  }
  u32 o = 0u;
  u32 ntt = 1u << nl;
  while (o < nout) {
    u32 n = ar_dcanon(cx, (o == 0u) ? Rc : Rs);
    u32 t = 0u;
    while (t < ntt) {
      u64 sl = 0ULL;
      u64 sh = 0ULL;
      u32 i = 0u;
      while (i < n) {
        const u32 *m = cx->gsy + 5u * i;
        u32 mlen = m[0];
        bool one = true;
        u32 k2 = 1u;
        while (k2 <= mlen && one) {
          u32 x = m[k2];
          bool f = false;
          u32 val = 0u;
          j = 0u;
          while (j < nin) {
            if (!f && x == 2u * cx->g_innet[j]) {
              val = (u32)((cx->g_tin[j] >> t) & 1ULL);
              f = true;
            }
            j = j + 1u;
          }
          if (!f && nout == 2u && x == 2u * cx->g_outs[0]) {
            val = (u32)((cx->g_tto[0] >> t) & 1ULL);
            f = true;
          }
          if (!f) { return false; }
          one = (val != 0u);
          k2 = k2 + 1u;
        }
        if (one) {
          C0_TIE2(sl, sh, ar_cadd(cx, sl, sh, cx->gcl[i], cx->gch[i]));
        }
        i = i + 1u;
      }
      if (sh != 0ULL || sl != ((cx->g_tto[o] >> t) & 1ULL)) {
        return false;
      }
      t = t + 1u;
    }
    if (!ar_install_rule(cx, cx->g_outs[o], n)) { return false; }
    o = o + 1u;
  }
  if (kind == 6u) {
    if ((cx->g_tto[0] & cx->g_tto[1]) != 0ULL) { return false; }
    cx->partner[cx->g_outs[0]] = cx->g_outs[1];
    cx->partner[cx->g_outs[1]] = cx->g_outs[0];
  }
  return true;
}

bool ar_do_cone(ArCtx *cx) {
  bool ok = false;
  u32 root = 0u;
  u32 k = 0u;
  C0_TIE2(ok, root, ar_next_word(cx)); if (!ok) { return false; }
  C0_TIE2(ok, k, ar_next_word(cx)); if (!ok) { return false; }
  if (root >= cx->n_nets || cx->rule_n[root] == AR_NONE) { return false; }
  if ((u64)k > cx->nw - cx->pos) { return false; }
  if (k == 0u) { return true; }
  if (!ar_load_rule(cx, root)) { return false; }
  u32 i = 0u;
  while (i < k) {
    u32 v = 0u;
    C0_TIE2(ok, v, ar_next_word(cx)); if (!ok) { return false; }
    if (v >= cx->n_nets || cx->rule_n[v] == AR_NONE || v == root) { return false; }
    u32 off = cx->rule_off[v];
    cx->cur_rm = cx->rs_m + off;
    cx->cur_rl = cx->rs_l + off;
    cx->cur_rh = cx->rs_h + off;
    cx->cur_rp = cx->rs_pool;
    cx->cur_nr = cx->rule_n[v];
    if (!ar_apply(cx, 2u * v)) { return false; }
    i = i + 1u;
  }
  return ar_store_rule(cx, root);
}

bool ar_setup_dynamic(ArCtx *cx) {
  u64 unit = 20ULL + 4ULL * AR_W_RATIO + 56ULL + 8ULL * AR_W_RATIO +
             36ULL + 4ULL + 40ULL + 4ULL * AR_W_RATIO + 5ULL + 4ULL * AR_W_RATIO;
  if (cx->top > cx->wlen) { return false; }
  u64 rem = cx->wlen - cx->top;
  if (rem < 4096ULL) { return false; }
  u64 cap = (rem - 4096ULL) / unit;
  if (cap > 300000000ULL) { cap = 300000000ULL; }
  if (cap < 16ULL) { return false; }
  u64 pw = cap * AR_W_RATIO;
  cx->rs_cap = (u32)cap;
  cx->rs_pcap = pw;
  cx->rs_m = (u32 *)ar_aalloc(cx, 4ULL * cap);
  cx->rs_l = (u64 *)ar_aalloc(cx, 8ULL * cap);
  cx->rs_h = (u64 *)ar_aalloc(cx, 8ULL * cap);
  cx->rs_pool = (u32 *)ar_aalloc(cx, 4ULL * pw);
  cx->tcap = (u32)cap;
  cx->tm[0] = (u32 *)ar_aalloc(cx, 4ULL * cap);
  cx->ts[0] = (u64 *)ar_aalloc(cx, 8ULL * cap);
  cx->tl[0] = (u64 *)ar_aalloc(cx, 8ULL * cap);
  cx->th[0] = (u64 *)ar_aalloc(cx, 8ULL * cap);
  cx->tm[1] = (u32 *)ar_aalloc(cx, 4ULL * cap);
  cx->ts[1] = (u64 *)ar_aalloc(cx, 8ULL * cap);
  cx->tl[1] = (u64 *)ar_aalloc(cx, 8ULL * cap);
  cx->th[1] = (u64 *)ar_aalloc(cx, 8ULL * cap);
  cx->pcap = pw;
  cx->pool[0] = (u32 *)ar_aalloc(cx, 4ULL * pw);
  cx->pool[1] = (u32 *)ar_aalloc(cx, 4ULL * pw);
  cx->qcap = (u32)cap;
  cx->qm = (u32 *)ar_aalloc(cx, 4ULL * cap);
  cx->qs = (u64 *)ar_aalloc(cx, 8ULL * cap);
  cx->ql = (u64 *)ar_aalloc(cx, 8ULL * cap);
  cx->qh = (u64 *)ar_aalloc(cx, 8ULL * cap);
  cx->ix = (u32 *)ar_aalloc(cx, 4ULL * cap);
  cx->ix2 = (u32 *)ar_aalloc(cx, 4ULL * cap);
  cx->bx = (u32 *)ar_aalloc(cx, 4ULL * cap);
  cx->vq_off = (u32 *)ar_aalloc(cx, 4ULL * cap + 4ULL);
  cx->vq = (u32 *)ar_aalloc(cx, 4ULL * pw);
  cx->vq_skip = ar_aalloc(cx, cap);
  cx->rcap = (u32)cap;
  cx->rpcap = pw;
  cx->rm = (u32 *)ar_aalloc(cx, 4ULL * cap);
  cx->rl = (u64 *)ar_aalloc(cx, 8ULL * cap);
  cx->rh = (u64 *)ar_aalloc(cx, 8ULL * cap);
  cx->rm2 = (u32 *)ar_aalloc(cx, 4ULL * cap);
  cx->rl2 = (u64 *)ar_aalloc(cx, 8ULL * cap);
  cx->rh2 = (u64 *)ar_aalloc(cx, 8ULL * cap);
  cx->rpool = (u32 *)ar_aalloc(cx, 4ULL * pw);
  if (cx->rs_m == NULL || cx->rs_l == NULL || cx->rs_h == NULL || cx->rs_pool == NULL ||
      cx->tm[0] == NULL || cx->ts[0] == NULL || cx->tl[0] == NULL || cx->th[0] == NULL ||
      cx->tm[1] == NULL || cx->ts[1] == NULL || cx->tl[1] == NULL || cx->th[1] == NULL ||
      cx->pool[0] == NULL || cx->pool[1] == NULL || cx->qm == NULL || cx->qs == NULL ||
      cx->ql == NULL || cx->qh == NULL || cx->ix == NULL || cx->ix2 == NULL ||
      cx->bx == NULL || cx->vq_off == NULL || cx->vq == NULL || cx->vq_skip == NULL ||
      cx->rm == NULL || cx->rl == NULL || cx->rh == NULL || cx->rm2 == NULL ||
      cx->rl2 == NULL || cx->rh2 == NULL || cx->rpool == NULL) {
    return false;
  }
  return true;
}

bool arisca_check_aig(ArCtx *cx, u8 *art, u64 art_len) {
  if (cx->M > 0x3FFFFFF0u) { return false; }
  if ((u64)cx->I + (u64)cx->A != (u64)cx->M) { return false; }
  u32 maxlit = 2u * cx->M + 1u;
  u32 k = 0u;
  while (k < cx->O) {
    if (cx->olit[k] > maxlit) { return false; }
    k = k + 1u;
  }
  k = 0u;
  while (k < cx->A) {
    u32 nd = cx->I + 1u + k;
    if ((cx->rhs0[k] >> 1) >= nd || (cx->rhs1[k] >> 1) >= nd) { return false; }
    k = k + 1u;
  }
  if (!ar_parse_art_header_and_tables(cx, art, art_len)) { return false; }
  if (!ar_setup_dynamic(cx)) { return false; }
  u32 i = 0u;
  while (i < cx->n_gates) {
    if (!ar_do_gate(cx)) { return false; }
    i = i + 1u;
  }
  i = 0u;
  while (i < cx->n_cones) {
    if (!ar_do_cone(cx)) { return false; }
    i = i + 1u;
  }
  if (!ar_build_sp0(cx)) { return false; }
  i = 0u;
  while (i < cx->n_main) {
    bool ok = false;
    u32 op = 0u;
    C0_TIE2(ok, op, ar_next_word(cx)); if (!ok) { return false; }
    u32 v = op >> 1;
    if (v >= cx->n_nets) { return false; }
    if ((op & 1u) == 0u) {
      if (cx->rule_n[v] == AR_NONE) { return false; }
      if (!ar_build_R(cx, v)) { return false; }
      u32 sym = (cx->flipped[v] != (u8)0) ? (2u * v + 1u) : (2u * v);
      if (!ar_apply(cx, sym)) { return false; }
    } else {
      if (cx->flipped[v] != (u8)0) { return false; }
      cx->rpool[0] = 0u;
      cx->rpool[1] = 1u;
      cx->rpool[2] = 2u * v + 1u;
      cx->rm[0] = 0u;
      cx->rl[0] = 1ULL & cx->mlo;
      cx->rh[0] = 0ULL;
      cx->rm[1] = 1u;
      u64 nl = 0ULL;
      u64 nh = 0ULL;
      C0_TIE2(nl, nh, ar_cneg(cx, 1ULL, 0ULL));
      cx->rl[1] = nl;
      cx->rh[1] = nh;
      cx->cur_rm = cx->rm;
      cx->cur_rl = cx->rl;
      cx->cur_rh = cx->rh;
      cx->cur_rp = cx->rpool;
      cx->cur_nr = 2u;
      if (!ar_apply(cx, 2u * v)) { return false; }
      cx->flipped[v] = (u8)1;
    }
    i = i + 1u;
  }
  if (cx->pos != cx->nw) { return false; }
  if (cx->tn != 0u) { return false; }
  return true;
}

bool ar_check_main(ArCtx *cx, const u8 *aig, u64 aig_len, u8 *art, u64 art_len) {
  if (!ar_parse_aig(cx, aig, aig_len)) { return false; }
  return arisca_check_aig(cx, art, art_len);
}

u64 arisca_check_bytes(u64 aig_ptr, u64 aig_len, u64 art_ptr, u64 art_len,
                       u64 work_ptr, u64 work_len) {
  if (aig_ptr == 0ULL || art_ptr == 0ULL || work_ptr == 0ULL) { return AR_REJECT; }
  if (aig_len > 0xFFFFFFFFFFFFFFFFULL - aig_ptr) { return AR_REJECT; }
  if (art_len > 0xFFFFFFFFFFFFFFFFULL - art_ptr) { return AR_REJECT; }
  if (work_len > 0xFFFFFFFFFFFFFFFFULL - work_ptr) { return AR_REJECT; }
  u64 pad = (8ULL - (work_ptr & 7ULL)) & 7ULL;
  if (work_len < pad + sizeof(ArCtx)) { return AR_REJECT; }
  u64 work_base = work_ptr + pad;
  u64 avail = work_len - pad;
  u8 *zp = (u8 *)work_base;
  u64 zi = 0ULL;
  while (zi < sizeof(ArCtx)) {
    zp[zi] = (u8)0;
    zi = zi + 1ULL;
  }
  ArCtx *cx = (ArCtx *)work_base;
  cx->w = zp;
  cx->wlen = avail;
  cx->top = sizeof(ArCtx);
  if (ar_check_main(cx, (const u8 *)aig_ptr, aig_len, (u8 *)art_ptr, art_len)) {
    return AR_ACCEPT;
  }
  return AR_REJECT;
}
"

/-- Ordered live functions of `Arisca/Src/Driver.lean` (`14` fns). -/
def fns : List Fn := arisca_driver_fns

end

public section

theorem ar_ttsim_wf : Func.Wf ar_ttsim_body := by arisca_wf_reify
theorem ar_dzero_wf : Func.Wf ar_dzero_body := by arisca_wf_reify
theorem ar_dlit_wf : Func.Wf ar_dlit_body := by arisca_wf_reify
theorem ar_dmul_wf : Func.Wf ar_dmul_body := by arisca_wf_reify
theorem ar_daxpy_wf : Func.Wf ar_daxpy_body := by arisca_wf_reify
theorem ar_dcanon_wf : Func.Wf ar_dcanon_body := by arisca_wf_reify
theorem ar_install_rule_wf : Func.Wf ar_install_rule_body := by arisca_wf_reify
theorem ar_mask6_wf : Func.Wf ar_mask6_body := by arisca_wf_reify
theorem ar_do_gate_wf : Func.Wf ar_do_gate_body := by arisca_wf_reify
theorem ar_do_cone_wf : Func.Wf ar_do_cone_body := by arisca_wf_reify
theorem ar_setup_dynamic_wf : Func.Wf ar_setup_dynamic_body := by arisca_wf_reify
theorem arisca_check_aig_wf : Func.Wf arisca_check_aig_body := by arisca_wf_reify
theorem ar_check_main_wf : Func.Wf ar_check_main_body := by arisca_wf_reify
theorem arisca_check_bytes_wf : Func.Wf arisca_check_bytes_body := by arisca_wf_reify

theorem fns_wf : ∀ f ∈ fns, f.Wf := by
  intro f hf
  simp only [fns, arisca_driver_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ar_ttsim_wf
  · exact ar_dzero_wf
  · exact ar_dlit_wf
  · exact ar_dmul_wf
  · exact ar_daxpy_wf
  · exact ar_dcanon_wf
  · exact ar_install_rule_wf
  · exact ar_mask6_wf
  · exact ar_do_gate_wf
  · exact ar_do_cone_wf
  · exact ar_setup_dynamic_wf
  · exact arisca_check_aig_wf
  · exact ar_check_main_wf
  · exact arisca_check_bytes_wf

end

end LeanQbe.T.Examples.Arisca.Src.Driver
