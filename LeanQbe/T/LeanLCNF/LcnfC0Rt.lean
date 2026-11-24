module

public import LeanQbe.T.LeanLCNF.Lower
public import LeanQbe.T.Frontend.C0
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Logic.C0Step
public meta import LeanQbe.T.Frontend.C0

/-!
# Additive C0 Slab Allocator & Worklist Perceus RC Runtime (`LcnfC0Rt`, Milestone R0)

Purely additive C0 runtime module targeting `LeanQbe.T` cleanly without modifying the core
`LeanQbe.T` compiler or existing C runtime harness (`test/lcnf/lcnf_rt.{h,c}`):

* **Unified `LcnfC0Rt` slab layout (`33672` bytes header)**:
  - bytes `0..255`: `extra_args[32]` (`rtExtraOff = 0`)
  - bytes `256..33023`: `globals[4096]` (`rtGlobalsOff = 256`)
  - bytes `33024..33535`: `free_list[64]` (64 size-class freelists covering `16..504B`)
  - bytes `33536..33671`: `LcnfC0Hdr s` (`large_free`, `ba_empty`, `cur`, `end`, `work`,
    `work_cap`, `chunks`, `nchunks`, `chunks_cap`, `LcnfC0Stats st`)
* **Acyclic R0 runtime functions** matching `Lower.rtCalls`:
  1. `lcnf_alloc(rt, sz) -> u64`: 8-byte aligned allocator with 64 size-class freelists
     (`16..504B`), exact-match `large_free` scan (`>= 512B`), and bump pointer `[cur, end)`
     exiting cleanly via `lcnf_panic` (`.exit "lcnf_panic"`) on invalid size or OOM.
  2. `lcnf_free_obj(rt, o) -> void`: computes dynamic object size for ctors (`<= 244`),
     closures (`245`), `Array` (`246`), `SArray`/`ByteArray` (`248`), `String` (`249`), and
     `MPZ` (`250`), clears the header, returns the cell to `free_list`/`large_free`, and updates
     `frees`/`live` telemetry.
  3. `lcnf_dec_ref_cold(rt, o) -> void`: iterative worklist DFS (`r->s.work[0..work_cap-1]`)
     cascading `m_rc == 1` drops and decrementing shared `m_rc > 1` children, freeing cells via
     `lcnf_free_obj`.
  4. `lcnf_mark_persistent(rt, o) -> void`: iterative worklist DFS marking `o` and all
     non-persistent reachable heap objects persistent (`m_rc := 0`).
  5. `lcnf_clo_under(rt, f, k) -> u64`: allocates extended closure (`nfix + k` slots), copies
     captured fields, and either frees exclusive `f` via `lcnf_free_obj` or increments positive
     captured objects and decrements `f`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.LeanLCNF

open LeanQbe.T
open LeanQbe.T.Frontend.C0

/-- Pure C0 struct definitions shared between `c0_layout_lemmas!` and `elabC0Module`. -/
meta def lcnfC0LayoutSrc : String := "
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
"

/-- Full C0 source of the R0 runtime module (acyclic, callees before callers). -/
meta def lcnfC0RtSrc : String := lcnfC0LayoutSrc ++ "
extern void lcnf_panic(u64 rt, u64 code);

u64 lcnf_alloc(u64 rt, u64 sz) {
  LcnfC0Rt *r = (LcnfC0Rt *)rt;
  if (sz > 268435448ULL) {
    lcnf_panic(rt, 2ULL);
    return 0ULL;
  }
  u64 bytes = (sz + 7ULL) & 0xfffffffffffffff8ULL;
  if (bytes < 16ULL) {
    lcnf_panic(rt, 2ULL);
    return 0ULL;
  }
  u64 cls = bytes >> 3;
  u64 p = 0ULL;
  if (cls < 64ULL) {
    p = r->free_list[cls];
    if (p != 0ULL) {
      r->free_list[cls] = *(u64 *)(p + 8ULL);
      r->s.st.reused = r->s.st.reused + 1ULL;
    } else {
      u64 cur = r->s.cur;
      u64 end = r->s.end;
      if (end < cur || bytes > end - cur) {
        lcnf_panic(rt, 3ULL);
        return 0ULL;
      }
      p = cur;
      r->s.cur = cur + bytes;
    }
  } else {
    u64 prev = 0ULL;
    u64 lcur = r->s.large_free;
    while (lcur != 0ULL) {
      if (*(u64 *)(lcur + 16ULL) == bytes) {
        u64 nxt = *(u64 *)(lcur + 8ULL);
        if (prev != 0ULL) {
          *(u64 *)(prev + 8ULL) = nxt;
        } else {
          r->s.large_free = nxt;
        }
        p = lcur;
        r->s.st.reused = r->s.st.reused + 1ULL;
        break;
      }
      prev = lcur;
      lcur = *(u64 *)(lcur + 8ULL);
    }
    if (p == 0ULL) {
      u64 cur = r->s.cur;
      u64 end = r->s.end;
      if (end < cur || bytes > end - cur) {
        lcnf_panic(rt, 3ULL);
        return 0ULL;
      }
      p = cur;
      r->s.cur = cur + bytes;
    }
  }
  r->s.st.allocs = r->s.st.allocs + 1ULL;
  r->s.st.bytes = r->s.st.bytes + bytes;
  u64 live = r->s.st.live + 1ULL;
  r->s.st.live = live;
  if (live > r->s.st.peak_live) {
    r->s.st.peak_live = live;
  }
  return p;
}

void lcnf_free_obj(u64 rt, u64 o) {
  if ((o & 1ULL) != 0ULL) return;
  LcnfC0Rt *r = (LcnfC0Rt *)rt;
  u64 hdr = *(u64 *)o;
  u64 tag = hdr >> 56;
  u64 bytes = 0ULL;
  if (tag == 246ULL) {
    u64 cap = *(u64 *)(o + 16ULL);
    if (cap > 33554428ULL) {
      lcnf_panic(rt, 5ULL);
      return;
    }
    bytes = 24ULL + 8ULL * cap;
  } else if (tag == 248ULL) {
    u64 esz = (hdr >> 48) & 127ULL;
    u64 cap = *(u64 *)(o + 16ULL);
    if (cap > 268435455ULL) {
      lcnf_panic(rt, 5ULL);
      return;
    }
    bytes = (24ULL + esz * cap + 7ULL) & 0xfffffffffffffff8ULL;
  } else if (tag == 249ULL) {
    u64 cap = *(u64 *)(o + 16ULL);
    if (cap > 268435415ULL) {
      lcnf_panic(rt, 5ULL);
      return;
    }
    bytes = (32ULL + cap + 7ULL) & 0xfffffffffffffff8ULL;
  } else if (tag == 250ULL) {
    u64 cap = *(u64 *)(o + 8ULL) & 0xffffffffULL;
    if (cap > 33554429ULL) {
      lcnf_panic(rt, 5ULL);
      return;
    }
    bytes = 16ULL + 8ULL * cap;
  } else {
    bytes = (hdr >> 32) & 0xffffULL;
  }
  if ((bytes & 7ULL) != 0ULL || bytes < 16ULL || bytes >= 268435456ULL) {
    lcnf_panic(rt, 5ULL);
    return;
  }
  u64 cls = bytes >> 3;
  *(u64 *)o = 0ULL;
  if (cls < 64ULL) {
    *(u64 *)(o + 8ULL) = r->free_list[cls];
    r->free_list[cls] = o;
  } else {
    *(u64 *)(o + 8ULL) = r->s.large_free;
    *(u64 *)(o + 16ULL) = bytes;
    r->s.large_free = o;
  }
  r->s.st.frees = r->s.st.frees + 1ULL;
  r->s.st.live = r->s.st.live - 1ULL;
}

void lcnf_dec_ref_cold(u64 rt, u64 o) {
  LcnfC0Rt *r = (LcnfC0Rt *)rt;
  r->s.st.cold_decs = r->s.st.cold_decs + 1ULL;
  if ((o & 1ULL) != 0ULL) return;
  u64 w = r->s.work;
  u64 cap = r->s.work_cap;
  if (cap == 0ULL) {
    lcnf_panic(rt, 4ULL);
    return;
  }
  ((u64 *)w)[0ULL] = o;
  u64 len = 1ULL;
  while (len > 0ULL) {
    len = len - 1ULL;
    u64 x = ((u64 *)w)[len];
    u64 hdr = *(u64 *)x;
    u64 tag = hdr >> 56;
    u64 n = 0ULL;
    u64 off = 8ULL;
    if (tag == 245ULL) {
      u64 cmeta = *(u64 *)(x + 16ULL);
      n = (cmeta >> 16) & 0xffffULL;
      off = 24ULL;
    } else if (tag == 246ULL) {
      n = *(u64 *)(x + 8ULL);
      off = 24ULL;
    } else if (tag <= 244ULL) {
      n = (hdr >> 48) & 0xffULL;
      off = 8ULL;
    }
    u64 i = 0ULL;
    while (i < n) {
      u64 c = *(u64 *)(x + off + 8ULL * i);
      if ((c & 1ULL) == 0ULL) {
        u64 chdr = *(u64 *)c;
        u64 crc = chdr & 0xffffffffULL;
        if (crc == 1ULL) {
          if (len == cap) {
            lcnf_panic(rt, 4ULL);
            return;
          }
          ((u64 *)w)[len] = c;
          len = len + 1ULL;
        } else if (crc > 1ULL && crc < 2147483648ULL) {
          *(u64 *)c = chdr - 1ULL;
        }
      }
      i = i + 1ULL;
    }
    lcnf_free_obj(rt, x);
  }
}

void lcnf_mark_persistent(u64 rt, u64 o) {
  if ((o & 1ULL) != 0ULL) return;
  u64 hdr0 = *(u64 *)o;
  if ((hdr0 & 0xffffffffULL) == 0ULL) return;
  LcnfC0Rt *r = (LcnfC0Rt *)rt;
  *(u64 *)o = hdr0 & 0xffffffff00000000ULL;
  r->s.st.persistent = r->s.st.persistent + 1ULL;
  u64 w = r->s.work;
  u64 cap = r->s.work_cap;
  if (cap == 0ULL) {
    lcnf_panic(rt, 4ULL);
    return;
  }
  ((u64 *)w)[0ULL] = o;
  u64 len = 1ULL;
  while (len > 0ULL) {
    len = len - 1ULL;
    u64 x = ((u64 *)w)[len];
    u64 hdr = *(u64 *)x;
    u64 tag = hdr >> 56;
    u64 n = 0ULL;
    u64 off = 8ULL;
    if (tag == 245ULL) {
      u64 cmeta = *(u64 *)(x + 16ULL);
      n = (cmeta >> 16) & 0xffffULL;
      off = 24ULL;
    } else if (tag == 246ULL) {
      n = *(u64 *)(x + 8ULL);
      off = 24ULL;
    } else if (tag <= 244ULL) {
      n = (hdr >> 48) & 0xffULL;
      off = 8ULL;
    }
    u64 i = 0ULL;
    while (i < n) {
      u64 c = *(u64 *)(x + off + 8ULL * i);
      if ((c & 1ULL) == 0ULL) {
        u64 chdr = *(u64 *)c;
        if ((chdr & 0xffffffffULL) != 0ULL) {
          *(u64 *)c = chdr & 0xffffffff00000000ULL;
          r->s.st.persistent = r->s.st.persistent + 1ULL;
          if (len == cap) {
            lcnf_panic(rt, 4ULL);
            return;
          }
          ((u64 *)w)[len] = c;
          len = len + 1ULL;
        }
      }
      i = i + 1ULL;
    }
  }
}

u64 lcnf_clo_under(u64 rt, u64 f, u64 k) {
  u64 fmeta = *(u64 *)(f + 16ULL);
  u64 arity = fmeta & 0xffffULL;
  u64 nfix = (fmeta >> 16) & 0xffffULL;
  if (k > 8188ULL || nfix + k > 8188ULL) {
    lcnf_panic(rt, 6ULL);
    return 0ULL;
  }
  u64 n2 = nfix + k;
  u64 sz = 24ULL + 8ULL * n2;
  u64 c = lcnf_alloc(rt, sz);
  *(u64 *)c = 1ULL | (sz << 32) | (245ULL << 56);
  *(u64 *)(c + 8ULL) = *(u64 *)(f + 8ULL);
  *(u64 *)(c + 16ULL) = arity | (n2 << 16);
  u64 i = 0ULL;
  while (i < nfix) {
    *(u64 *)(c + 24ULL + 8ULL * i) = *(u64 *)(f + 24ULL + 8ULL * i);
    i = i + 1ULL;
  }
  u64 fhdr = *(u64 *)f;
  u64 frc = fhdr & 0xffffffffULL;
  if (frc == 1ULL) {
    lcnf_free_obj(rt, f);
  } else {
    u64 j = 0ULL;
    while (j < nfix) {
      u64 cap = *(u64 *)(f + 24ULL + 8ULL * j);
      if ((cap & 1ULL) == 0ULL) {
        u64 chdr = *(u64 *)cap;
        u64 crc = chdr & 0xffffffffULL;
        if (crc != 0ULL && crc < 2147483647ULL) {
          *(u64 *)cap = chdr + 1ULL;
        }
      }
      j = j + 1ULL;
    }
    if (frc > 1ULL && frc < 2147483648ULL) {
      *(u64 *)f = fhdr - 1ULL;
    }
  }
  return c;
}
"

section ElabLayoutAndCode
open Lean Elab Command in
elab "lcnf_c0_r0_rt!" : command =>
  elabC0DeclAndLayout (some `rtR0) lcnfC0RtSrc (exits := ["lcnf_panic"])
    (forceExpose := true) (emitModule := false)

lcnf_c0_r0_rt!
end ElabLayoutAndCode

/-- Exact byte size of `LcnfC0Rt` (`32*8 + 4096*8 + 64*8 + 17*8 = 33672`), matching `LcnfRt` in
`test/lcnf/lcnf_rt.h` byte-for-byte. -/
theorem LcnfC0Rt_sizeof_eq : LcnfC0Rt.sizeof = 33672 := rfl

/-- R0 verified C0 runtime module (`externs = []`, `exits = ["lcnf_panic"]`). -/
def rtR0Mod : Module :=
  { fns := rtR0_fns, externs := [], exits := ["lcnf_panic"] }

theorem lcnf_alloc_wf : Func.Wf lcnf_alloc_body := by t_wf_reify
theorem lcnf_free_obj_wf : Func.Wf lcnf_free_obj_body := by t_wf_reify
theorem lcnf_dec_ref_cold_wf : Func.Wf lcnf_dec_ref_cold_body := by t_wf_reify
theorem lcnf_mark_persistent_wf : Func.Wf lcnf_mark_persistent_body := by t_wf_reify
theorem lcnf_clo_under_wf : Func.Wf lcnf_clo_under_body := by t_wf_reify

theorem rtR0Mod_wf : ∀ fn ∈ rtR0Mod.fns, Fn.Wf fn := by
  intro fn hfn
  simp only [rtR0Mod, rtR0_fns, List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl | rfl | rfl | rfl
  · exact lcnf_alloc_wf
  · exact lcnf_free_obj_wf
  · exact lcnf_dec_ref_cold_wf
  · exact lcnf_mark_persistent_wf
  · exact lcnf_clo_under_wf

theorem rtR0Mod_checkAcyclic : rtR0Mod.checkAcyclic = true := by decide

end LeanQbe.T.LeanLCNF
