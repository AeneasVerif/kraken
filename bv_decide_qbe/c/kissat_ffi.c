#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#define LEANQBE_BV_MAGIC 0x31505642u
#define LEANQBE_BV_VERSION 1u
#define LEANQBE_BV_HDR_BYTES 128u
#define LEANQBE_BV_TRIVIAL_SAT_MAGIC 0x4256545249565341ULL
#define LEANQBE_BV_DIMACS_BOUND 268435456ULL
#define LEANQBE_PLAIN_HDR_BYTES 768u
#define LEANQBE_ALIGN_PAD 64u

extern uint64_t bv_solve_bytes(const uint8_t *prog_ptr, uint64_t prog_len,
                               uint8_t *work_ptr, uint64_t work_cap,
                               uint64_t fuel);

static inline uint32_t read_u32_le(const uint8_t *p, size_t word_idx) {
  size_t o = word_idx * 4u;
  return (uint32_t)p[o] | ((uint32_t)p[o + 1u] << 8) |
         ((uint32_t)p[o + 2u] << 16) | ((uint32_t)p[o + 3u] << 24);
}

/* Replicates bv_init_workspace capacity checks to distinguish invalid BVP1 (.unknown)
 * from insufficient workspace (.workTooSmall) when BVHdr remains uninitialized. */
static int is_bv_init_oom(const uint8_t *prog_ptr, size_t prog_len, uint64_t avail) {
  if (prog_ptr == NULL || prog_len < 32u || (prog_len & 3u) != 0u) {
    return 0;
  }
  uint32_t magic = read_u32_le(prog_ptr, 0u);
  uint32_t ver = read_u32_le(prog_ptr, 1u);
  if (magic != LEANQBE_BV_MAGIC || ver != LEANQBE_BV_VERSION) {
    return 0;
  }
  uint32_t n_vars = read_u32_le(prog_ptr, 2u);
  uint32_t n_nodes = read_u32_le(prog_ptr, 3u);
  uint32_t n_cwords = read_u32_le(prog_ptr, 4u);
  uint32_t root = read_u32_le(prog_ptr, 5u);
  if (n_nodes == 0u || root >= n_nodes) {
    return 0;
  }
  uint64_t total_words =
      8ULL + ((uint64_t)n_vars << 1) + (uint64_t)n_cwords + (uint64_t)n_nodes * 5ULL;
  if ((total_words << 2) != (uint64_t)prog_len) {
    return 0;
  }
  uint64_t atom_end = 1ULL;
  for (uint32_t k = 0u; k < n_vars; k++) {
    uint32_t vw = read_u32_le(prog_ptr, 8u + (size_t)((uint64_t)k << 1) + 1u);
    if ((uint64_t)vw >= LEANQBE_BV_DIMACS_BOUND ||
        atom_end > LEANQBE_BV_DIMACS_BOUND - 1ULL - (uint64_t)vw) {
      return 0;
    }
    atom_end += (uint64_t)vw;
  }
  uint64_t num_atoms = atom_end - 1ULL;
  uint64_t atom_bytes = (((uint64_t)n_vars << 2) + 7ULL) & ~7ULL;
  uint64_t slice_bytes = (((uint64_t)n_nodes << 2) + 7ULL) & ~7ULL;
  uint64_t fixed_bytes = (uint64_t)LEANQBE_BV_HDR_BYTES + atom_bytes + slice_bytes;
  if (avail <= fixed_bytes || avail - fixed_bytes < 64ULL) {
    return 1;
  }
  uint64_t rem = avail - fixed_bytes;
  uint64_t acap64 = rem >> 5;
  if (acap64 >= LEANQBE_BV_DIMACS_BOUND) {
    acap64 = LEANQBE_BV_DIMACS_BOUND - 1ULL;
  }
  if (num_atoms >= acap64) {
    return 1;
  }
  uint64_t aig_bytes = acap64 << 3;
  uint64_t ht_budget = rem >> 1;
  uint64_t ht_slots = 1ULL;
  while ((ht_slots << 3) <= ht_budget && ht_slots < 0x40000000ULL) {
    ht_slots <<= 1;
  }
  uint64_t ht_bytes = ht_slots << 2;
  if (rem < aig_bytes + ht_bytes) {
    return 1;
  }
  return 0;
}

LEAN_EXPORT lean_obj_res leanqbe_alloc_work_buf(uint64_t n) {
  size_t sz = (size_t)n;
  lean_obj_res arr = lean_alloc_sarray(1, sz, sz);
  if (sz > 0) {
    memset(lean_sarray_cptr(arr), 0, sz);
  }
  return arr;
}

LEAN_EXPORT lean_obj_res leanqbe_solve_bv_bytes(b_lean_obj_arg prog,
                                                 lean_obj_arg work,
                                                 uint64_t fuel) {
  size_t prog_len = lean_sarray_size(prog);
  const uint8_t *prog_ptr = lean_sarray_cptr(prog);
  size_t wsize = lean_sarray_size(work);

  if (wsize < (size_t)(LEANQBE_ALIGN_PAD + LEANQBE_PLAIN_HDR_BYTES)) {
    lean_dec_ref(work);
    return lean_box(3); /* .workTooSmall */
  }

  if (!lean_is_exclusive(work)) {
    lean_dec_ref(work);
    work = lean_alloc_sarray(1, wsize, wsize);
    if (wsize > 0) {
      memset(lean_sarray_cptr(work), 0, wsize);
    }
  }

  uintptr_t raw_addr = (uintptr_t)lean_sarray_cptr(work);
  uintptr_t aligned = (raw_addr + 63u) & ~(uintptr_t)63u;
  uint8_t *work_ptr = (uint8_t *)aligned;
  uint64_t work_cap = (uint64_t)(wsize - LEANQBE_ALIGN_PAD);

  if (fuel == 0ULL) {
    lean_dec_ref(work);
    return lean_box(2); /* .unknown */
  }

  memset(work_ptr, 0, LEANQBE_PLAIN_HDR_BYTES);
  uint64_t rc = bv_solve_bytes(prog_ptr, (uint64_t)prog_len, work_ptr,
                               work_cap, fuel);

  if (rc == 20ULL) {
    lean_dec_ref(work);
    return lean_box(0); /* .unsat */
  }

  const uint64_t *hdr = (const uint64_t *)work_ptr;

  if (rc == 10ULL) {
    if (hdr[0] == LEANQBE_BV_TRIVIAL_SAT_MAGIC) {
      lean_obj_res empty_model = lean_alloc_sarray(1, 0, 0);
      lean_dec_ref(work);
      lean_obj_res res = lean_alloc_ctor(1, 1, 0);
      lean_ctor_set(res, 0, empty_model);
      return res; /* .sat empty */
    }
    uint64_t mv = hdr[0];
    uintptr_t vals_ptr = (uintptr_t)hdr[8];
    uintptr_t ws_lo = (uintptr_t)work_ptr + (uintptr_t)LEANQBE_PLAIN_HDR_BYTES;
    uintptr_t ws_hi = (uintptr_t)work_ptr + (uintptr_t)work_cap;
    if (vals_ptr < ws_lo || vals_ptr > ws_hi ||
        mv > (uint64_t)(ws_hi - vals_ptr) / 2ULL) {
      lean_dec_ref(work);
      return lean_box(2); /* .unknown */
    }
    lean_obj_res model = lean_alloc_sarray(1, (size_t)mv, (size_t)mv);
    const int8_t *vals = (const int8_t *)vals_ptr;
    uint8_t *dst = lean_sarray_cptr(model);
    for (uint64_t i = 0; i < mv; i++) {
      dst[i] = (vals[2 * i] > 0) ? 1 : 0;
    }
    lean_dec_ref(work);
    lean_obj_res res = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(res, 0, model);
    return res; /* .sat model */
  }

  if (rc == 0ULL) {
    const uint32_t *hdr32 = (const uint32_t *)work_ptr;
    uint64_t work_addr = (uint64_t)(uintptr_t)work_ptr;
    uint64_t mv = hdr[0];
    uint64_t expected_values = work_addr + (uint64_t)LEANQBE_PLAIN_HDR_BYTES;
    uint64_t vals_bytes = ((mv << 1) + 7ULL) & ~7ULL;
    uint64_t mark_bytes = (mv + 7ULL) & ~7ULL;
    uint64_t u32_var_bytes = ((mv << 2) + 7ULL) & ~7ULL;
    int plain_active =
        (mv < LEANQBE_BV_DIMACS_BOUND) &&
        (hdr[8] == expected_values) &&
        (hdr[9] == expected_values + vals_bytes) &&
        (hdr[10] == hdr[9] + (mark_bytes << 2)) &&
        (hdr[11] == hdr[10] + u32_var_bytes);
    uint32_t tag = 2u; /* .unknown */
    if (plain_active) {
      uint64_t p_oom = hdr[95];
      uint64_t p_fuel = hdr[21];
      uint64_t p_arena_cap = hdr[4];
      uint64_t p_wcap = hdr[5];
      uint64_t p_arena_len = hdr[6];
      uint64_t p_wlen = hdr[7];
      if (p_oom != 0ULL) {
        tag = 3u;
      } else if (p_fuel == 0ULL) {
        tag = 2u; /* fuel exhaustion -> .unknown */
      } else if (hdr[2] != work_addr + work_cap ||
                 p_arena_len + hdr[20] + 16ULL >= p_arena_cap ||
                 p_wlen * 2ULL + 4ULL >= p_wcap) {
        tag = 3u; /* parse OOM or arena/watch cap exhausted -> .workTooSmall */
      }
    } else {
      if (hdr32[31] != 0u || hdr32[30] != 0u ||
          (hdr[1] != 0ULL && hdr[8] != 0ULL) ||
          (hdr[1] == 0ULL && is_bv_init_oom(prog_ptr, prog_len, work_cap))) {
        tag = 3u; /* BV bitblaster/init/dimacs OOM -> .workTooSmall */
      }
    }
    lean_dec_ref(work);
    return lean_box(tag);
  }

  lean_dec_ref(work);
  return lean_box(2); /* .unknown */
}
