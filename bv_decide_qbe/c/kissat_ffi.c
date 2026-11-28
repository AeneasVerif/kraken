#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#define LEANQBE_BV_MAGIC 0x31505642u
#define LEANQBE_BV_VERSION 1u
#define LEANQBE_BV_HDR_BYTES 128u
#define LEANQBE_BV_TRIVIAL_SAT_MAGIC 0x4256545249565341ULL
#define LEANQBE_BV_DIMACS_BOUND 268435456ULL
#define LEANQBE_M6_EXT_BYTES 2304u
#define LEANQBE_FULL_HDR_BYTES 1152u
#define LEANQBE_M6_HDR_TOTAL_BYTES 3456u
#define LEANQBE_M6_HDR_MAGIC 0x4D36484452455831ULL
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

/* Allocate unzeroed scratch workspace (lazy page commit).
 * `leanqbe_solve_bv_bytes` zeroes the 3456 B header (`LEANQBE_M6_HDR_TOTAL_BYTES`),
 * and verified `bv_solve_bytes` / Kissat `full_zero_tables1` initialize all live
 * state under `bvSolveBytesSpec` (`region workPtr workCap`, arbitrary bytes). */
LEAN_EXPORT lean_obj_res leanqbe_alloc_work_buf(uint64_t n) {
  size_t sz = (size_t)n;
  return lean_alloc_sarray(1, sz, sz);
}

LEAN_EXPORT lean_obj_res leanqbe_solve_bv_bytes(b_lean_obj_arg prog,
                                                 lean_obj_arg work,
                                                 uint64_t fuel) {
  size_t prog_len = lean_sarray_size(prog);
  const uint8_t *prog_ptr = lean_sarray_cptr(prog);
  size_t wsize = lean_sarray_size(work);

  if (wsize < (size_t)(LEANQBE_ALIGN_PAD + LEANQBE_M6_HDR_TOTAL_BYTES)) {
    lean_dec_ref(work);
    return lean_box(3); /* .workTooSmall */
  }

  if (fuel == 0ULL) {
    lean_dec_ref(work);
    return lean_box(4); /* .timeout */
  }

  if (!lean_is_exclusive(work)) {
    lean_dec_ref(work);
    work = lean_alloc_sarray(1, wsize, wsize);
  }

  uintptr_t raw_addr = (uintptr_t)lean_sarray_cptr(work);
  uintptr_t aligned = (raw_addr + 63u) & ~(uintptr_t)63u;
  uint8_t *work_ptr = (uint8_t *)aligned;
  uint64_t work_cap = (uint64_t)(wsize - LEANQBE_ALIGN_PAD);

  memset(work_ptr, 0, LEANQBE_M6_HDR_TOTAL_BYTES);
  uint64_t rc = bv_solve_bytes(prog_ptr, (uint64_t)prog_len, work_ptr,
                               work_cap, fuel);

  if (rc == 20ULL) {
    lean_dec_ref(work);
    return lean_box(0); /* .unsat */
  }

  const uint64_t *ext = (const uint64_t *)work_ptr;

  if (rc == 10ULL) {
    if (ext[0] == LEANQBE_BV_TRIVIAL_SAT_MAGIC) {
      lean_obj_res empty_model = lean_alloc_sarray(1, 0, 0);
      lean_dec_ref(work);
      lean_obj_res res = lean_alloc_ctor(1, 1, 0);
      lean_ctor_set(res, 0, empty_model);
      return res; /* .sat empty */
    }
    if (ext[0] != LEANQBE_M6_HDR_MAGIC) {
      lean_dec_ref(work);
      return lean_box(2); /* .unknown */
    }
    const uint64_t *hdr =
        (const uint64_t *)(work_ptr + LEANQBE_M6_EXT_BYTES);
    uint64_t mv = hdr[0];
    uintptr_t vals_ptr = (uintptr_t)hdr[8];
    uintptr_t ws_lo = (uintptr_t)work_ptr + (uintptr_t)LEANQBE_M6_HDR_TOTAL_BYTES;
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
    uint32_t tag = 2u; /* .unknown */
    if (ext[0] == LEANQBE_M6_HDR_MAGIC) {
      const uint64_t *hdr =
          (const uint64_t *)(work_ptr + LEANQBE_M6_EXT_BYTES);
      uint64_t p_oom = hdr[95];
      uint64_t p_fuel = hdr[21];
      uint64_t p_arena_cap = hdr[4];
      uint64_t p_wcap = hdr[5];
      uint64_t p_arena_len = hdr[6];
      uint64_t p_wlen = hdr[7];
      uint64_t p_tmp_len = hdr[24];
      if (p_oom != 0ULL) {
        tag = 3u; /* Kissat explicit OOM -> .workTooSmall */
      } else if (p_fuel == 0ULL) {
        tag = 4u; /* fuel exhaustion -> .timeout */
      } else if (hdr[2] != work_addr + work_cap ||
                 p_arena_len >= p_arena_cap ||
                 p_tmp_len > (p_arena_cap - p_arena_len) ||
                 (p_arena_cap - p_arena_len) - p_tmp_len <= 16ULL ||
                 p_wlen >= p_wcap ||
                 (p_wcap - p_wlen) <= p_wlen + 32ULL) {
        tag = 3u; /* parse OOM or arena/watch cap exhausted -> .workTooSmall */
      }
    } else {
      if (hdr32[31] != 0u || hdr32[30] != 0u ||
          (ext[1] != 0ULL && ext[8] != 0ULL) ||
          (ext[1] == 0ULL && is_bv_init_oom(prog_ptr, prog_len, work_cap))) {
        tag = 3u; /* BV bitblaster/init/dimacs or full_m6_mem_init OOM -> .workTooSmall */
      }
    }
    lean_dec_ref(work);
    return lean_box(tag);
  }

  lean_dec_ref(work);
  return lean_box(2); /* .unknown */
}
