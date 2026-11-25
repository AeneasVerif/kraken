/*
 * Pure acyclic C0 runtime Milestone R2 Part 1:
 *   ByteArray (tag 248, m_other = 1) & Array (tag 246) COW primitives + lcnf_oob.
 *
 * Callees precede callers; zero alloca, zero VLAs, zero recursion, zero indirect calls.
 * Matches R0 `LcnfC0Rt` layout byte-for-byte (`sizeof = 33672`, `s.ba_empty @ 33544`).
 * Verified via `Func.wp` (`ModuleOk`) in `LcnfC0ContainersProof*.lean`.
 */

typedef struct {
  u64 allocs;
  u64 frees;
  u64 live;
  u64 peak_live;
  u64 persistent;
  u64 reused;
  u64 cold_decs;
  u64 bytes;
} LcnfC0Stats;

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
  LcnfC0Stats st;
} LcnfC0Hdr;

typedef struct {
  u64 extra_args[32];
  u64 globals[4096];
  u64 free_list[64];
  LcnfC0Hdr s;
} LcnfC0Rt;

extern void lcnf_panic(u64 rt, u64 code);
extern u64 lcnf_alloc(u64 rt, u64 sz);
extern void lcnf_free_obj(u64 rt, u64 o);
extern void lcnf_dec_ref_cold(u64 rt, u64 o);
extern void lcnf_mark_persistent(u64 rt, u64 o);

/* ---- RC & memory helpers ---- */

void r2_inc_obj(u64 o) {
  if (o != 0ULL && (o & 1ULL) == 0ULL) {
    u64 hdr = *(u64 *)o;
    u64 rc = hdr & 0xffffffffULL;
    if (rc != 0ULL && rc < 2147483647ULL) {
      *(u64 *)o = hdr + 1ULL;
    }
  }
}

void r2_dec_obj(u64 rt, u64 o) {
  if (o != 0ULL && (o & 1ULL) == 0ULL) {
    u64 hdr = *(u64 *)o;
    u64 rc = hdr & 0xffffffffULL;
    if (rc == 1ULL) {
      lcnf_dec_ref_cold(rt, o);
    } else if (rc > 1ULL && rc < 2147483648ULL) {
      *(u64 *)o = hdr - 1ULL;
    }
  }
}

void r2_mem_copy_bytes(u64 dst, u64 src, u64 len) {
  u64 i = 0ULL;
  while (i < len) {
    u8 b = *(u8 *)(src + i);
    *(u8 *)(dst + i) = b;
    i = i + 1ULL;
  }
}

u64 r2_cmp_byte_slices(u64 ap, u64 la, u64 bp, u64 lb) {
  u64 m = la;
  if (lb < la) {
    m = lb;
  }
  u64 i = 0ULL;
  while (i < m) {
    u64 ba = (u64)(*(u8 *)(ap + i));
    u64 bb = (u64)(*(u8 *)(bp + i));
    if (ba < bb) {
      return 0ULL;
    }
    if (ba > bb) {
      return 2ULL;
    }
    i = i + 1ULL;
  }
  if (la < lb) {
    return 0ULL;
  }
  if (la > lb) {
    return 2ULL;
  }
  return 1ULL;
}

/* ---- Bounds panic helper ---- */

u64 lcnf_oob(u64 rt, u64 dv) {
  r2_inc_obj(dv);
  return dv;
}

/* ---- ByteArray (tag 248, m_other = 1) internal helpers & primitives ---- */

u64 r2_alloc_sarray(u64 rt, u64 size, u64 cap) {
  if (cap > 268435416ULL || size > cap) {
    lcnf_panic(rt, 2ULL);
    return 0ULL;
  }
  u64 sz = (24ULL + cap + 7ULL) & 0xfffffffffffffff8ULL;
  u64 p = lcnf_alloc(rt, sz);
  *(u64 *)p = 0xf801000000000001ULL; /* rc=1, cs_sz=0, other=1, tag=248 */
  *(u64 *)(p + 8ULL) = size;
  *(u64 *)(p + 16ULL) = cap;
  return p;
}

u64 r2_ensure_excl_ba(u64 rt, u64 ba, u64 expand) {
  u64 hdr = *(u64 *)ba;
  u64 rc = hdr & 0xffffffffULL;
  u64 sz = *(u64 *)(ba + 8ULL);
  u64 cap = *(u64 *)(ba + 16ULL);
  if (rc == 1ULL && (expand == 0ULL || sz < cap)) {
    return ba;
  }
  u64 new_cap = cap;
  if (expand != 0ULL) {
    if (cap == 0ULL) {
      if (sz >= 8ULL) {
        lcnf_panic(rt, 2ULL);
        return 0ULL;
      }
      new_cap = 8ULL;
    } else if (sz < cap) {
      new_cap = cap;
    } else {
      if (cap >= 268435416ULL || sz > 268435416ULL) {
        lcnf_panic(rt, 2ULL);
        return 0ULL;
      }
      new_cap = cap * 2ULL;
      if (new_cap > 268435416ULL) {
        new_cap = 268435416ULL;
      }
      if (sz >= new_cap) {
        new_cap = sz + 1ULL;
        if (new_cap > 268435416ULL) {
          lcnf_panic(rt, 2ULL);
          return 0ULL;
        }
      }
    }
  }
  u64 r = r2_alloc_sarray(rt, sz, new_cap);
  r2_mem_copy_bytes(r + 24ULL, ba + 24ULL, sz);
  if (rc == 1ULL) {
    lcnf_free_obj(rt, ba);
  } else if (rc > 1ULL && rc < 2147483648ULL) {
    *(u64 *)ba = hdr - 1ULL;
  }
  return r;
}

u64 lcnf_ba_empty(u64 rt) {
  LcnfC0Rt *r = (LcnfC0Rt *)rt;
  u64 empty = r->s.ba_empty;
  if (empty == 0ULL) {
    u64 p = r2_alloc_sarray(rt, 0ULL, 0ULL);
    lcnf_mark_persistent(rt, p);
    LcnfC0Rt *r2 = (LcnfC0Rt *)rt;
    r2->s.ba_empty = p;
    return p;
  }
  return empty;
}

u64 lcnf_ba_mk_empty(u64 rt, u64 cap) {
  u64 c = 0ULL;
  if ((cap & 1ULL) != 0ULL) {
    c = cap >> 1;
  }
  return r2_alloc_sarray(rt, 0ULL, c);
}

u64 lcnf_ba_mk(u64 rt, u64 arr) {
  u64 n = *(u64 *)(arr + 8ULL);
  u64 ba = r2_alloc_sarray(rt, n, n);
  u64 i = 0ULL;
  while (i < n) {
    u64 elem = *(u64 *)(arr + 24ULL + 8ULL * i);
    *(u8 *)(ba + 24ULL + i) = (u8)(elem >> 1);
    i = i + 1ULL;
  }
  r2_dec_obj(rt, arr);
  return ba;
}

u64 lcnf_ba_get(u64 rt, u64 ba, u64 idx, u64 unboxed) {
  u64 sz = *(u64 *)(ba + 8ULL);
  u64 i = sz;
  if (unboxed != 0ULL) {
    i = idx;
  } else if ((idx & 1ULL) != 0ULL) {
    i = idx >> 1;
  }
  if (i < sz) {
    return (u64)(*(u8 *)(ba + 24ULL + i));
  }
  return 0ULL;
}

u64 lcnf_ba_set(u64 rt, u64 ba, u64 idx, u64 b, u64 unboxed) {
  u64 sz = *(u64 *)(ba + 8ULL);
  u64 i = sz;
  if (unboxed != 0ULL) {
    i = idx;
  } else if ((idx & 1ULL) != 0ULL) {
    i = idx >> 1;
  }
  if (i >= sz) {
    return ba;
  }
  u64 r = r2_ensure_excl_ba(rt, ba, 0ULL);
  *(u8 *)(r + 24ULL + i) = (u8)b;
  return r;
}

u64 lcnf_ba_push(u64 rt, u64 ba, u64 b) {
  u64 r = r2_ensure_excl_ba(rt, ba, 1ULL);
  u64 sz = *(u64 *)(r + 8ULL);
  *(u8 *)(r + 24ULL + sz) = (u8)b;
  *(u64 *)(r + 8ULL) = sz + 1ULL;
  return r;
}

u64 lcnf_ba_cmp_op(u64 rt, u64 op, u64 a, u64 b) {
  if (a == b) {
    if (op == 0ULL) {
      return 1ULL;
    }
    if (op == 1ULL) {
      return 0ULL;
    }
    return 1ULL;
  }
  u64 la = *(u64 *)(a + 8ULL);
  u64 lb = *(u64 *)(b + 8ULL);
  if (op == 0ULL && la != lb) {
    return 0ULL;
  }
  u64 ord = r2_cmp_byte_slices(a + 24ULL, la, b + 24ULL, lb);
  if (op == 0ULL) {
    if (ord == 1ULL) {
      return 1ULL;
    }
    return 0ULL;
  }
  if (op == 1ULL) {
    if (ord == 0ULL) {
      return 1ULL;
    }
    return 0ULL;
  }
  return ord;
}

/* ---- Array (tag 246) internal helpers & primitives ---- */

u64 r2_alloc_array(u64 rt, u64 size, u64 cap) {
  if (cap > 33554428ULL || size > cap) {
    lcnf_panic(rt, 2ULL);
    return 0ULL;
  }
  u64 sz = 24ULL + 8ULL * cap;
  u64 p = lcnf_alloc(rt, sz);
  *(u64 *)p = 0xf600000000000001ULL; /* rc=1, cs_sz=0, other=0, tag=246 */
  *(u64 *)(p + 8ULL) = size;
  *(u64 *)(p + 16ULL) = cap;
  return p;
}

u64 r2_ensure_excl_array(u64 rt, u64 a, u64 expand) {
  u64 hdr = *(u64 *)a;
  u64 rc = hdr & 0xffffffffULL;
  u64 sz = *(u64 *)(a + 8ULL);
  u64 cap = *(u64 *)(a + 16ULL);
  if (rc == 1ULL && (expand == 0ULL || sz < cap)) {
    return a;
  }
  u64 new_cap = cap;
  if (expand != 0ULL) {
    if (cap == 0ULL) {
      if (sz >= 4ULL) {
        lcnf_panic(rt, 2ULL);
        return 0ULL;
      }
      new_cap = 4ULL;
    } else if (sz < cap) {
      new_cap = cap;
    } else {
      if (cap >= 33554428ULL || sz > 33554428ULL) {
        lcnf_panic(rt, 2ULL);
        return 0ULL;
      }
      new_cap = cap * 2ULL;
      if (new_cap > 33554428ULL) {
        new_cap = 33554428ULL;
      }
      if (sz >= new_cap) {
        new_cap = sz + 1ULL;
        if (new_cap > 33554428ULL) {
          lcnf_panic(rt, 2ULL);
          return 0ULL;
        }
      }
    }
  }
  u64 r = r2_alloc_array(rt, sz, new_cap);
  u64 i = 0ULL;
  while (i < sz) {
    u64 v = *(u64 *)(a + 24ULL + 8ULL * i);
    if (rc != 1ULL) {
      r2_inc_obj(v);
    }
    *(u64 *)(r + 24ULL + 8ULL * i) = v;
    i = i + 1ULL;
  }
  if (rc == 1ULL) {
    lcnf_free_obj(rt, a);
  } else if (rc > 1ULL && rc < 2147483648ULL) {
    *(u64 *)a = hdr - 1ULL;
  }
  return r;
}

u64 lcnf_array_mk_empty(u64 rt, u64 cap) {
  u64 c = 0ULL;
  if ((cap & 1ULL) != 0ULL) {
    c = cap >> 1;
  }
  return r2_alloc_array(rt, 0ULL, c);
}

u64 lcnf_array_get(u64 rt, u64 dv, u64 arr, u64 idx, u64 flags) {
  u64 borrowed = flags & 1ULL;
  u64 unboxed = flags & 2ULL;
  u64 sz = *(u64 *)(arr + 8ULL);
  if (unboxed != 0ULL) {
    if (idx >= sz) {
      lcnf_panic(rt, 7ULL);
      return 0ULL;
    }
    u64 v = *(u64 *)(arr + 24ULL + 8ULL * idx);
    if (borrowed == 0ULL) {
      r2_inc_obj(v);
    }
    return v;
  }
  if ((idx & 1ULL) != 0ULL) {
    u64 i = idx >> 1;
    if (i < sz) {
      u64 v = *(u64 *)(arr + 24ULL + 8ULL * i);
      if (borrowed == 0ULL) {
        r2_inc_obj(v);
      }
      return v;
    }
  }
  if (borrowed == 0ULL) {
    r2_inc_obj(dv);
  }
  return dv;
}

u64 lcnf_array_set(u64 rt, u64 arr, u64 idx, u64 v, u64 unboxed) {
  u64 sz = *(u64 *)(arr + 8ULL);
  u64 i = sz;
  if (unboxed != 0ULL) {
    i = idx;
  } else if ((idx & 1ULL) != 0ULL) {
    i = idx >> 1;
  }
  if (i >= sz) {
    r2_dec_obj(rt, v);
    return arr;
  }
  u64 r = r2_ensure_excl_array(rt, arr, 0ULL);
  u64 old = *(u64 *)(r + 24ULL + 8ULL * i);
  *(u64 *)(r + 24ULL + 8ULL * i) = v;
  r2_dec_obj(rt, old);
  return r;
}

u64 lcnf_array_push(u64 rt, u64 arr, u64 v) {
  u64 r = r2_ensure_excl_array(rt, arr, 1ULL);
  u64 sz = *(u64 *)(r + 8ULL);
  *(u64 *)(r + 24ULL + 8ULL * sz) = v;
  *(u64 *)(r + 8ULL) = sz + 1ULL;
  return r;
}

u64 lcnf_array_pop(u64 rt, u64 arr) {
  u64 r = r2_ensure_excl_array(rt, arr, 0ULL);
  u64 sz = *(u64 *)(r + 8ULL);
  if (sz == 0ULL) {
    return r;
  }
  sz = sz - 1ULL;
  *(u64 *)(r + 8ULL) = sz;
  u64 old = *(u64 *)(r + 24ULL + 8ULL * sz);
  r2_dec_obj(rt, old);
  return r;
}

u64 lcnf_array_swap(u64 rt, u64 arr, u64 i, u64 j, u64 check_bounds) {
  u64 sz = *(u64 *)(arr + 8ULL);
  if ((i & 1ULL) == 0ULL || (j & 1ULL) == 0ULL) {
    if (check_bounds != 0ULL) {
      return arr;
    }
    lcnf_panic(rt, 7ULL);
    return 0ULL;
  }
  u64 ui = i >> 1;
  u64 uj = j >> 1;
  if (ui >= sz || uj >= sz) {
    if (check_bounds != 0ULL) {
      return arr;
    }
    lcnf_panic(rt, 7ULL);
    return 0ULL;
  }
  u64 r = r2_ensure_excl_array(rt, arr, 0ULL);
  u64 a = *(u64 *)(r + 24ULL + 8ULL * ui);
  u64 b = *(u64 *)(r + 24ULL + 8ULL * uj);
  *(u64 *)(r + 24ULL + 8ULL * ui) = b;
  *(u64 *)(r + 24ULL + 8ULL * uj) = a;
  return r;
}
