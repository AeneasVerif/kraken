#include "../../LeanQbe/T/Frontend/C0/c0.h"

/* Lean Tier-0 runtime RC + iterative worklist dec + forward goto + multi-return + short-circuit */

typedef struct {
  i32 m_rc;
  u16 m_cs_sz;
  u8 m_other;
  u8 m_tag;
} lean_object;

typedef struct {
  lean_object m_header;
  u64 m_objs[];
} lean_ctor_object;

extern void c0_free_obj(lean_object *o);

static inline bool lean_is_scalar_impl(lean_object *o) {
  return ((u64)o & 1ULL) != 0ULL;
}

bool lean_is_scalar(lean_object *o) {
  return lean_is_scalar_impl(o);
}

lean_object *lean_box(u64 n) {
  return (lean_object *)((n << 1) | 1ULL);
}

u64 lean_unbox(lean_object *o) {
  return (u64)o >> 1;
}

void lean_inc(lean_object *o) {
  if (!lean_is_scalar_impl(o) && o->m_rc > 0) {
    o->m_rc = o->m_rc + 1;
  }
}

void lean_dec_ref_cold(lean_object *o) {
  u64 todo = 0ULL;
  lean_object *cur = o;
  while (cur != NULL) {
    u64 hdr = *(u64 *)cur;
    u8 tag = (u8)((hdr >> 56) & 0xFFULL);
    if (tag <= (u8)243) {
      u32 nobjs = (u32)((hdr >> 48) & 0xFFULL);
      lean_ctor_object *ctor = (lean_ctor_object *)cur;
      u32 i = 0u;
      while (i < nobjs) {
        u64 child_raw = ctor->m_objs[i];
        lean_object *child = (lean_object *)child_raw;
        if ((child_raw & 1ULL) == 0ULL && child != NULL) {
          i32 crc = child->m_rc;
          if (crc > 1) {
            child->m_rc = crc - 1;
          } else if (crc == 1) {
            /* Push child onto intrusive 48-bit worklist, preserving top 16 bits (m_other, m_tag) */
            u64 chdr = *(u64 *)child;
            *(u64 *)child = (chdr & 0xFFFF000000000000ULL) | (todo & 0x0000FFFFFFFFFFFFULL);
            todo = (u64)child;
          }
        }
        i = i + 1u;
      }
    }
    lean_object *next = (lean_object *)todo;
    if (next != NULL) {
      u64 nhdr = *(u64 *)next;
      todo = nhdr & 0x0000FFFFFFFFFFFFULL;
    }
    c0_free_obj(cur);
    cur = next;
  }
}

void lean_dec(lean_object *o) {
  if (!lean_is_scalar_impl(o)) {
    i32 rc = o->m_rc;
    if (rc > 1) {
      o->m_rc = rc - 1;
    } else if (rc == 1) {
      lean_dec_ref_cold(o);
    }
  }
}

/* Forward goto DONE idiom (Kissat analyze.c pattern) */
u32 analyze_goto_demo(u32 *buf, u32 n, u32 limit) {
  u32 acc = 0u;
  u32 i = 0u;
  if (n == 0u) {
    acc = 1u;
    goto DONE;
  }
  while (i < n) {
    u32 v = buf[i];
    if (v == 0xFFFFFFFFu) {
      acc = acc + 100u;
      goto DONE;
    }
    acc = acc + v;
    if (acc >= limit) {
      goto DONE;
    }
    i = i + 1u;
  }
  acc = acc + 7u;
DONE:
  return acc ^ (i << 8);
}

/* Multi-return C0 function using C0_RET2 / C0_TUP2 / C0_TIE2 */
typedef C0_RET2(u32, u32) u32_pair;

u32_pair divmod_u32(u32 a, u32 b) {
  check(b != 0u);
  u32 q = a / b;
  u32 r = a % b;
  return C0_TUP2(u32_pair, q, r);
}

u32 sum_divmod_u32(u32 a, u32 b) {
  u32 q = 0u;
  u32 r = 0u;
  C0_TIE2(q, r, divmod_u32(a, b));
  return q * 100u + r;
}

/* Short-circuit guarded load right at end-of-buffer boundary */
i32 find_guarded(i32 *arr, u64 n, i32 target) {
  u64 i = 0ULL;
  while (i < n && arr[i] != target) {
    i = i + 1ULL;
  }
  if (i < n && arr[i] == target) {
    return (i32)i;
  }
  return (i32)-1;
}
