#include "../../Frontend/C0/c0.h"

/* LeanLCNF R2b pure C0 runtime: Strings, Chars, Missing Container Ops, Nat.repr */

extern u64 lcnf_alloc(u64 rt, u64 bytes);
extern void lcnf_free_obj(u64 rt, u64 o);
extern void lcnf_dec_ref_cold(u64 rt, u64 o);
extern void lcnf_mark_persistent(u64 rt, u64 o);
extern void lcnf_panic(u64 rt, u64 code);

extern void r2_inc_obj(u64 o);
extern void r2_dec_obj(u64 rt, u64 o);
extern void r2_mem_copy_bytes(u64 dst, u64 src, u64 len);
extern u64 r2_cmp_byte_slices(u64 ap, u64 la, u64 bp, u64 lb);
extern u64 r2_alloc_sarray(u64 rt, u64 size, u64 cap);
extern u64 r2_alloc_array(u64 rt, u64 size, u64 cap);

u64 r2b_alloc_mpz(u64 rt, u64 cap, u64 sz) {
  if (cap > 33554429ULL) {
    lcnf_panic(rt, 2ULL);
    return 0ULL;
  }
  if (sz > cap) {
    lcnf_panic(rt, 2ULL);
    return 0ULL;
  }
  u64 bytes = 16ULL + 8ULL * cap;
  u64 p = lcnf_alloc(rt, bytes);
  *(u64 *)p = 0xfa00000000000001ULL;
  *(u64 *)(p + 8ULL) = cap | (sz << 32);
  return p;
}

u64 r2b_str_alloc_cap(u64 rt, u64 cap, u64 size, u64 length) {
  if (size >= 268435415ULL) {
    lcnf_panic(rt, 2ULL);
    return 0ULL;
  }
  if (cap <= size) {
    lcnf_panic(rt, 2ULL);
    return 0ULL;
  }
  if (cap > 268435415ULL) {
    lcnf_panic(rt, 2ULL);
    return 0ULL;
  }
  u64 bytes = (32ULL + cap + 7ULL) & (~7ULL);
  u64 p = lcnf_alloc(rt, bytes);
  *(u64 *)p = 0xf901000000000001ULL;
  *(u64 *)(p + 8ULL) = size + 1ULL;
  *(u64 *)(p + 16ULL) = cap;
  *(u64 *)(p + 24ULL) = length;
  *(u8 *)(p + 32ULL + size) = (u8)0ULL;
  return p;
}

u64 r2b_utf8_len(u64 cp) {
  if (cp <= 0x7fULL) {
    return 1ULL;
  }
  if (cp <= 0x7ffULL) {
    return 2ULL;
  }
  if (cp <= 0xffffULL) {
    return 3ULL;
  }
  return 4ULL;
}

u64 r2b_utf8_write(u64 dst, u64 cp) {
  if (cp <= 0x7fULL) {
    *(u8 *)dst = (u8)cp;
    return 1ULL;
  }
  if (cp <= 0x7ffULL) {
    *(u8 *)dst = (u8)(0xc0ULL | (cp >> 6));
    *(u8 *)(dst + 1ULL) = (u8)(0x80ULL | (cp & 0x3fULL));
    return 2ULL;
  }
  if (cp <= 0xffffULL) {
    *(u8 *)dst = (u8)(0xe0ULL | (cp >> 12));
    *(u8 *)(dst + 1ULL) = (u8)(0x80ULL | ((cp >> 6) & 0x3fULL));
    *(u8 *)(dst + 2ULL) = (u8)(0x80ULL | (cp & 0x3fULL));
    return 3ULL;
  }
  *(u8 *)dst = (u8)(0xf0ULL | ((cp >> 18) & 0x07ULL));
  *(u8 *)(dst + 1ULL) = (u8)(0x80ULL | ((cp >> 12) & 0x3fULL));
  *(u8 *)(dst + 2ULL) = (u8)(0x80ULL | ((cp >> 6) & 0x3fULL));
  *(u8 *)(dst + 3ULL) = (u8)(0x80ULL | (cp & 0x3fULL));
  return 4ULL;
}

u64 r2b_utf8_decode_step(u64 data, u64 sz, u64 idx) {
  if (idx >= sz) {
    return 0ULL;
  }
  u64 b0 = (u64)(*(u8 *)(data + idx));
  if ((b0 & 0x80ULL) == 0ULL) {
    return 1ULL;
  }
  if ((b0 & 0xe0ULL) == 0xc0ULL) {
    if (sz - idx > 1ULL) {
      return 2ULL;
    }
    return 1ULL;
  }
  if ((b0 & 0xf0ULL) == 0xe0ULL) {
    if (sz - idx > 2ULL) {
      return 3ULL;
    }
    return 1ULL;
  }
  if ((b0 & 0xf8ULL) == 0xf0ULL) {
    if (sz - idx > 3ULL) {
      return 4ULL;
    }
    return 1ULL;
  }
  return 1ULL;
}

u64 r2b_utf8_decode_cp(u64 data, u64 sz, u64 idx) {
  if (idx >= sz) {
    return 0ULL;
  }
  u64 b0 = (u64)(*(u8 *)(data + idx));
  if ((b0 & 0x80ULL) == 0ULL) {
    return b0;
  }
  if ((b0 & 0xe0ULL) == 0xc0ULL) {
    if (sz - idx > 1ULL) {
      u64 b1 = (u64)(*(u8 *)(data + idx + 1ULL));
      return ((b0 & 0x1fULL) << 6) | (b1 & 0x3fULL);
    }
    return 0ULL;
  }
  if ((b0 & 0xf0ULL) == 0xe0ULL) {
    if (sz - idx > 2ULL) {
      u64 b1 = (u64)(*(u8 *)(data + idx + 1ULL));
      u64 b2 = (u64)(*(u8 *)(data + idx + 2ULL));
      return ((b0 & 0x0fULL) << 12) | ((b1 & 0x3fULL) << 6) | (b2 & 0x3fULL);
    }
    return 0ULL;
  }
  if ((b0 & 0xf8ULL) == 0xf0ULL) {
    if (sz - idx > 3ULL) {
      u64 b1 = (u64)(*(u8 *)(data + idx + 1ULL));
      u64 b2 = (u64)(*(u8 *)(data + idx + 2ULL));
      u64 b3 = (u64)(*(u8 *)(data + idx + 3ULL));
      u64 hi = ((b0 & 0x07ULL) << 18) | ((b1 & 0x3fULL) << 12);
      u64 lo = ((b2 & 0x3fULL) << 6) | (b3 & 0x3fULL);
      return hi | lo;
    }
    return 0ULL;
  }
  return 0ULL;
}

u64 lcnf_str_alloc(u64 rt, u64 size, u64 length) {
  if (size >= 268435415ULL) {
    lcnf_panic(rt, 2ULL);
    return 0ULL;
  }
  return r2b_str_alloc_cap(rt, size + 1ULL, size, length);
}

u64 lcnf_char_op(u64 rt, u64 op, u64 arg) {
  if (op == 0ULL) {
    if ((arg & 1ULL) == 0ULL) {
      return 0ULL;
    }
    u64 v = arg >> 1;
    if (v < 0xd800ULL) {
      return v;
    }
    if (v >= 0xe000ULL) {
      if (v < 0x110000ULL) {
        return v;
      }
    }
    return 0ULL;
  }
  if (op == 1ULL) {
    u64 c = arg & 0xffffffffULL;
    u64 len = r2b_utf8_len(c);
    return (len << 1) | 1ULL;
  }
  lcnf_panic(rt, 1ULL);
  return 0ULL;
}

u64 lcnf_string_push(u64 rt, u64 s, u64 c) {
  u64 sz_with_nul = *(u64 *)(s + 8ULL);
  u64 sz = sz_with_nul - 1ULL;
  u64 cap = *(u64 *)(s + 16ULL);
  u64 len = *(u64 *)(s + 24ULL);
  u64 hdr = *(u64 *)s;
  u64 rc = hdr & 0xffffffffULL;
  u64 cp = c & 0xffffffffULL;
  u64 clen = r2b_utf8_len(cp);
  if (sz >= 268435415ULL - clen) {
    lcnf_panic(rt, 2ULL);
    return 0ULL;
  }
  u64 new_sz = sz + clen;
  if (rc == 1ULL) {
    if (new_sz + 1ULL <= cap) {
      r2b_utf8_write(s + 32ULL + sz, cp);
      *(u8 *)(s + 32ULL + new_sz) = (u8)0ULL;
      *(u64 *)(s + 8ULL) = new_sz + 1ULL;
      *(u64 *)(s + 24ULL) = len + 1ULL;
      return s;
    }
  }
  u64 new_cap = new_sz + 1ULL;
  if (rc == 1ULL) {
    u64 doubled = cap * 2ULL;
    if (doubled > new_cap) {
      new_cap = doubled;
    }
    if (new_cap > 268435415ULL) {
      new_cap = 268435415ULL;
    }
  }
  u64 dst = r2b_str_alloc_cap(rt, new_cap, new_sz, len + 1ULL);
  r2_mem_copy_bytes(dst + 32ULL, s + 32ULL, sz);
  r2b_utf8_write(dst + 32ULL + sz, cp);
  r2_dec_obj(rt, s);
  return dst;
}

u64 lcnf_string_append(u64 rt, u64 s1, u64 s2) {
  u64 sz2_with_nul = *(u64 *)(s2 + 8ULL);
  u64 sz2 = sz2_with_nul - 1ULL;
  if (sz2 == 0ULL) {
    return s1;
  }
  u64 sz1 = *(u64 *)(s1 + 8ULL) - 1ULL;
  u64 cap1 = *(u64 *)(s1 + 16ULL);
  u64 len1 = *(u64 *)(s1 + 24ULL);
  u64 len2 = *(u64 *)(s2 + 24ULL);
  if (sz2 >= 268435415ULL) {
    lcnf_panic(rt, 2ULL);
    return 0ULL;
  }
  if (sz1 >= 268435415ULL - sz2) {
    lcnf_panic(rt, 2ULL);
    return 0ULL;
  }
  u64 new_sz = sz1 + sz2;
  u64 hdr1 = *(u64 *)s1;
  u64 rc1 = hdr1 & 0xffffffffULL;
  if (rc1 == 1ULL) {
    if (new_sz + 1ULL <= cap1) {
      r2_mem_copy_bytes(s1 + 32ULL + sz1, s2 + 32ULL, sz2);
      *(u8 *)(s1 + 32ULL + new_sz) = (u8)0ULL;
      *(u64 *)(s1 + 8ULL) = new_sz + 1ULL;
      *(u64 *)(s1 + 24ULL) = len1 + len2;
      return s1;
    }
  }
  u64 new_cap = new_sz + 1ULL;
  if (rc1 == 1ULL) {
    u64 doubled = cap1 * 2ULL;
    if (doubled > new_cap) {
      new_cap = doubled;
    }
    if (new_cap > 268435415ULL) {
      new_cap = 268435415ULL;
    }
  }
  u64 dst = r2b_str_alloc_cap(rt, new_cap, new_sz, len1 + len2);
  r2_mem_copy_bytes(dst + 32ULL, s1 + 32ULL, sz1);
  r2_mem_copy_bytes(dst + 32ULL + sz1, s2 + 32ULL, sz2);
  r2_dec_obj(rt, s1);
  return dst;
}

u64 lcnf_string_cmp_op(u64 rt, u64 op, u64 s1, u64 s2) {
  if (op > 2ULL) {
    lcnf_panic(rt, 1ULL);
    return 0ULL;
  }
  if (s1 == s2) {
    if (op == 0ULL) {
      return 1ULL;
    }
    if (op == 1ULL) {
      return 0ULL;
    }
    if (op == 2ULL) {
      return 1ULL;
    }
    lcnf_panic(rt, 1ULL);
    return 0ULL;
  }
  u64 sz1 = *(u64 *)(s1 + 8ULL) - 1ULL;
  u64 sz2 = *(u64 *)(s2 + 8ULL) - 1ULL;
  if (op == 0ULL) {
    if (sz1 != sz2) {
      return 0ULL;
    }
    u64 ord0 = r2_cmp_byte_slices(s1 + 32ULL, sz1, s2 + 32ULL, sz2);
    if (ord0 == 1ULL) {
      return 1ULL;
    }
    return 0ULL;
  }
  if (op == 1ULL) {
    u64 ord1 = r2_cmp_byte_slices(s1 + 32ULL, sz1, s2 + 32ULL, sz2);
    if (ord1 == 0ULL) {
      return 1ULL;
    }
    return 0ULL;
  }
  if (op == 2ULL) {
    return r2_cmp_byte_slices(s1 + 32ULL, sz1, s2 + 32ULL, sz2);
  }
  lcnf_panic(rt, 1ULL);
  return 0ULL;
}

u64 lcnf_string_pos_op(u64 rt, u64 op, u64 s, u64 idx_v, u64 end_v) {
  u64 sz = *(u64 *)(s + 8ULL) - 1ULL;
  if (op == 0ULL) {
    if ((idx_v & 1ULL) == 0ULL) {
      return 0ULL;
    }
    u64 idx0 = idx_v >> 1;
    if (idx0 >= sz) {
      return 0ULL;
    }
    return r2b_utf8_decode_cp(s + 32ULL, sz, idx0);
  }
  if (op == 1ULL) {
    if ((idx_v & 1ULL) == 0ULL) {
      r2_inc_obj(idx_v);
      return idx_v;
    }
    u64 idx1 = idx_v >> 1;
    if (idx1 >= sz) {
      return idx_v;
    }
    u64 step = r2b_utf8_decode_step(s + 32ULL, sz, idx1);
    return ((idx1 + step) << 1) | 1ULL;
  }
  if (op == 2ULL) {
    if ((idx_v & 1ULL) == 0ULL) {
      return 1ULL;
    }
    u64 idx2 = idx_v >> 1;
    if (idx2 >= sz) {
      return 1ULL;
    }
    return 0ULL;
  }
  if (op == 3ULL) {
    u64 b = sz;
    if ((idx_v & 1ULL) != 0ULL) {
      b = idx_v >> 1;
      if (b > sz) {
        b = sz;
      }
    }
    u64 e = sz;
    if ((end_v & 1ULL) != 0ULL) {
      e = end_v >> 1;
      if (e > sz) {
        e = sz;
      }
    }
    if (b >= e) {
      return r2b_str_alloc_cap(rt, 1ULL, 0ULL, 0ULL);
    }
    u64 new_sz = e - b;
    u64 new_len = 0ULL;
    u64 pos = b;
    while (pos < e) {
      u64 st = r2b_utf8_decode_step(s + 32ULL, e, pos);
      pos = pos + st;
      new_len = new_len + 1ULL;
    }
    u64 dst = r2b_str_alloc_cap(rt, new_sz + 1ULL, new_sz, new_len);
    r2_mem_copy_bytes(dst + 32ULL, s + 32ULL + b, new_sz);
    return dst;
  }
  if (op == 4ULL) {
    if ((idx_v & 1ULL) == 0ULL) {
      return 0ULL;
    }
    u64 idx4 = idx_v >> 1;
    if (idx4 >= sz) {
      return 0ULL;
    }
    return (u64)(*(u8 *)(s + 32ULL + idx4));
  }
  if (op == 5ULL) {
    if ((idx_v & 1ULL) == 0ULL) {
      return 0ULL;
    }
    u64 idx5 = idx_v >> 1;
    if (idx5 > sz) {
      return 0ULL;
    }
    if (idx5 == sz) {
      return 1ULL;
    }
    u64 b5 = (u64)(*(u8 *)(s + 32ULL + idx5));
    if ((b5 & 0xc0ULL) != 0x80ULL) {
      return 1ULL;
    }
    return 0ULL;
  }
  lcnf_panic(rt, 1ULL);
  return 0ULL;
}

u64 lcnf_string_to_list(u64 rt, u64 s) {
  u64 sz = *(u64 *)(s + 8ULL) - 1ULL;
  u64 rev = 1ULL;
  u64 pos = 0ULL;
  while (pos < sz) {
    u64 cp = r2b_utf8_decode_cp(s + 32ULL, sz, pos);
    u64 step = r2b_utf8_decode_step(s + 32ULL, sz, pos);
    u64 node = lcnf_alloc(rt, 24ULL);
    *(u64 *)node = 0x0102001800000001ULL;
    *(u64 *)(node + 8ULL) = (cp << 1) | 1ULL;
    *(u64 *)(node + 16ULL) = rev;
    rev = node;
    pos = pos + step;
  }
  r2_dec_obj(rt, s);
  u64 res = 1ULL;
  while ((rev & 1ULL) == 0ULL) {
    u64 next = *(u64 *)(rev + 16ULL);
    *(u64 *)(rev + 16ULL) = res;
    res = rev;
    rev = next;
  }
  return res;
}

u64 lcnf_string_mk(u64 rt, u64 cs) {
  u64 total_bytes = 0ULL;
  u64 char_len = 0ULL;
  u64 cur = cs;
  while ((cur & 1ULL) == 0ULL) {
    u64 hd = *(u64 *)(cur + 8ULL);
    u64 cp = (hd >> 1) & 0xffffffffULL;
    u64 b = r2b_utf8_len(cp);
    if (total_bytes + b >= 268435415ULL) {
      lcnf_panic(rt, 2ULL);
      return 0ULL;
    }
    total_bytes = total_bytes + b;
    char_len = char_len + 1ULL;
    cur = *(u64 *)(cur + 16ULL);
  }
  u64 dst = r2b_str_alloc_cap(rt, total_bytes + 1ULL, total_bytes, char_len);
  u64 pos = 0ULL;
  cur = cs;
  while ((cur & 1ULL) == 0ULL) {
    u64 hd2 = *(u64 *)(cur + 8ULL);
    u64 cp2 = (hd2 >> 1) & 0xffffffffULL;
    u64 bw = r2b_utf8_write(dst + 32ULL + pos, cp2);
    pos = pos + bw;
    cur = *(u64 *)(cur + 16ULL);
  }
  r2_dec_obj(rt, cs);
  return dst;
}

u64 lcnf_ba_data(u64 rt, u64 ba) {
  u64 sz = *(u64 *)(ba + 8ULL);
  if (sz > 33554428ULL) {
    lcnf_panic(rt, 2ULL);
    return 0ULL;
  }
  u64 arr = r2_alloc_array(rt, sz, sz);
  u64 i = 0ULL;
  while (i < sz) {
    u64 b = (u64)(*(u8 *)(ba + 24ULL + i));
    *(u64 *)(arr + 24ULL + 8ULL * i) = (b << 1) | 1ULL;
    i = i + 1ULL;
  }
  r2_dec_obj(rt, ba);
  return arr;
}

u64 lcnf_array_mk(u64 rt, u64 list) {
  u64 n = 0ULL;
  u64 cur = list;
  while ((cur & 1ULL) == 0ULL) {
    if (n >= 33554428ULL) {
      lcnf_panic(rt, 2ULL);
      return 0ULL;
    }
    n = n + 1ULL;
    cur = *(u64 *)(cur + 16ULL);
  }
  u64 arr = r2_alloc_array(rt, n, n);
  u64 i = 0ULL;
  cur = list;
  while ((cur & 1ULL) == 0ULL) {
    u64 v = *(u64 *)(cur + 8ULL);
    r2_inc_obj(v);
    *(u64 *)(arr + 24ULL + 8ULL * i) = v;
    i = i + 1ULL;
    cur = *(u64 *)(cur + 16ULL);
  }
  r2_dec_obj(rt, list);
  return arr;
}

u64 lcnf_array_to_list(u64 rt, u64 arr) {
  u64 n = *(u64 *)(arr + 8ULL);
  u64 res = 1ULL;
  u64 i = n;
  while (i > 0ULL) {
    i = i - 1ULL;
    u64 v = *(u64 *)(arr + 24ULL + 8ULL * i);
    r2_inc_obj(v);
    u64 node = lcnf_alloc(rt, 24ULL);
    *(u64 *)node = 0x0102001800000001ULL;
    *(u64 *)(node + 8ULL) = v;
    *(u64 *)(node + 16ULL) = res;
    res = node;
  }
  r2_dec_obj(rt, arr);
  return res;
}

u64 lcnf_array_replicate(u64 rt, u64 n, u64 v) {
  if ((n & 1ULL) == 0ULL) {
    lcnf_panic(rt, 2ULL);
    return 0ULL;
  }
  u64 cnt = n >> 1;
  if (cnt > 33554428ULL) {
    lcnf_panic(rt, 2ULL);
    return 0ULL;
  }
  u64 arr = r2_alloc_array(rt, cnt, cnt);
  if (cnt == 0ULL) {
    r2_dec_obj(rt, v);
    return arr;
  }
  if (cnt > 1ULL) {
    if (v != 0ULL) {
      if ((v & 1ULL) == 0ULL) {
        u64 hdr = *(u64 *)v;
        u64 rc = hdr & 0xffffffffULL;
        if (rc != 0ULL) {
          if (cnt - 1ULL <= 0x7fffffffULL - rc) {
            *(u64 *)v = hdr + (cnt - 1ULL);
          } else {
            lcnf_mark_persistent(rt, v);
          }
        }
      }
    }
  }
  u64 i = 0ULL;
  while (i < cnt) {
    *(u64 *)(arr + 24ULL + 8ULL * i) = v;
    i = i + 1ULL;
  }
  return arr;
}

u64 lcnf_nat_to_str(u64 rt, u64 n) {
  if ((n & 1ULL) != 0ULL) {
    u64 v = n >> 1;
    if (v == 0ULL) {
      u64 s0 = r2b_str_alloc_cap(rt, 2ULL, 1ULL, 1ULL);
      *(u8 *)(s0 + 32ULL) = (u8)48ULL;
      return s0;
    }
    u64 t1 = v;
    u64 len = 0ULL;
    while (t1 > 0ULL) {
      len = len + 1ULL;
      t1 = t1 / 10ULL;
    }
    u64 s1 = r2b_str_alloc_cap(rt, len + 1ULL, len, len);
    u64 t2 = v;
    u64 pos = len;
    while (pos > 0ULL) {
      pos = pos - 1ULL;
      u64 d = t2 % 10ULL;
      t2 = t2 / 10ULL;
      *(u8 *)(s1 + 32ULL + pos) = (u8)(48ULL + d);
    }
    return s1;
  }
  u64 meta = *(u64 *)(n + 8ULL);
  u64 nsz = meta >> 32;
  u64 cn = nsz;
  u64 trim_go = 1ULL;
  while (trim_go != 0ULL) {
    if (cn > 0ULL) {
      u64 top = *(u64 *)(n + 16ULL + 8ULL * (cn - 1ULL));
      if (top == 0ULL) {
        cn = cn - 1ULL;
      } else {
        trim_go = 0ULL;
      }
    } else {
      trim_go = 0ULL;
    }
  }
  if (cn == 0ULL) {
    u64 szero = r2b_str_alloc_cap(rt, 2ULL, 1ULL, 1ULL);
    *(u8 *)(szero + 32ULL) = (u8)48ULL;
    r2_dec_obj(rt, n);
    return szero;
  }
  if (cn > 13421770ULL) {
    lcnf_panic(rt, 2ULL);
    return 0ULL;
  }
  u64 tmp_mpz = r2b_alloc_mpz(rt, cn, cn);
  u64 k = 0ULL;
  while (k < cn) {
    *(u64 *)(tmp_mpz + 16ULL + 8ULL * k) = *(u64 *)(n + 16ULL + 8ULL * k);
    k = k + 1ULL;
  }
  r2_dec_obj(rt, n);
  u64 max_digits = 20ULL * cn;
  u64 rev = r2_alloc_sarray(rt, 0ULL, max_digits);
  u64 dlen = 0ULL;
  u64 cur_cn = cn;
  while (cur_cn > 0ULL) {
    u64 rem = 0ULL;
    u64 j = cur_cn;
    while (j > 0ULL) {
      j = j - 1ULL;
      u64 w = *(u64 *)(tmp_mpz + 16ULL + 8ULL * j);
      u64 hi = (rem << 32) | (w >> 32);
      u64 q_hi = hi / 10ULL;
      u64 r_hi = hi % 10ULL;
      u64 lo = (r_hi << 32) | (w & 0xffffffffULL);
      u64 q_lo = lo / 10ULL;
      rem = lo % 10ULL;
      *(u64 *)(tmp_mpz + 16ULL + 8ULL * j) = (q_hi << 32) | q_lo;
    }
    if (dlen < max_digits) {
      *(u8 *)(rev + 24ULL + dlen) = (u8)(48ULL + rem);
      dlen = dlen + 1ULL;
    } else {
      cur_cn = 0ULL;
    }
    u64 zgo = 1ULL;
    while (zgo != 0ULL) {
      if (cur_cn > 0ULL) {
        u64 wtop = *(u64 *)(tmp_mpz + 16ULL + 8ULL * (cur_cn - 1ULL));
        if (wtop == 0ULL) {
          cur_cn = cur_cn - 1ULL;
        } else {
          zgo = 0ULL;
        }
      } else {
        zgo = 0ULL;
      }
    }
  }
  *(u64 *)(rev + 8ULL) = dlen;
  u64 s = r2b_str_alloc_cap(rt, dlen + 1ULL, dlen, dlen);
  u64 idx = 0ULL;
  while (idx < dlen) {
    u8 ch = *(u8 *)(rev + 24ULL + (dlen - 1ULL - idx));
    *(u8 *)(s + 32ULL + idx) = ch;
    idx = idx + 1ULL;
  }
  lcnf_free_obj(rt, rev);
  lcnf_free_obj(rt, tmp_mpz);
  return s;
}
