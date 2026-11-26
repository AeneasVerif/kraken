#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#define LEANQBE_M6_HDR_MAGIC 0x4D36484452455831ULL
#define LEANQBE_M6_EXT_BYTES 2304u
#define LEANQBE_M6_HDR_TOTAL_BYTES 3456u
#define LEANQBE_ALIGN_PAD 64u
#define LEANQBE_HDR_OOM_IDX 95u

extern uint64_t kissat_solve_bytes(const uint8_t *cnf_ptr, uint64_t cnf_len,
                                   uint8_t *work_ptr, uint64_t work_cap,
                                   uint64_t fuel);

LEAN_EXPORT lean_obj_res leanqbe_alloc_work_buf(uint64_t n) {
  size_t sz = (size_t)n;
  lean_obj_res arr = lean_alloc_sarray(1, sz, sz);
  if (sz > 0) {
    memset(lean_sarray_cptr(arr), 0, sz);
  }
  return arr;
}

LEAN_EXPORT lean_obj_res leanqbe_solve_dimacs_bytes(b_lean_obj_arg cnf,
                                                    lean_obj_arg work,
                                                    uint64_t fuel) {
  size_t cnf_len = lean_sarray_size(cnf);
  const uint8_t *cnf_ptr = lean_sarray_cptr(cnf);
  size_t wsize = lean_sarray_size(work);

  if (wsize < (size_t)(LEANQBE_ALIGN_PAD + LEANQBE_M6_HDR_TOTAL_BYTES)) {
    lean_dec_ref(work);
    return lean_box(3); /* .workTooSmall */
  }

  if (!lean_is_exclusive(work)) {
    lean_dec_ref(work);
    work = lean_alloc_sarray(1, wsize, wsize);
  }

  uintptr_t raw_addr = (uintptr_t)lean_sarray_cptr(work);
  uintptr_t aligned = (raw_addr + 63u) & ~(uintptr_t)63u;
  uint8_t *work_ptr = (uint8_t *)aligned;
  uint64_t work_cap = (uint64_t)(wsize - LEANQBE_ALIGN_PAD);

  memset(work_ptr, 0, 8);
  uint64_t rc = kissat_solve_bytes(cnf_ptr, (uint64_t)cnf_len, work_ptr,
                                   work_cap, fuel);

  if (rc == 20ULL) {
    lean_dec_ref(work);
    return lean_box(0); /* .unsat */
  }

  const uint64_t *hdr = (const uint64_t *)(work_ptr + LEANQBE_M6_EXT_BYTES);

  if (rc == 10ULL) {
    uint64_t mv = hdr[0];
    uintptr_t vals_ptr = (uintptr_t)hdr[8];
    uintptr_t ws_lo = (uintptr_t)hdr + 72ULL;
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
    uint64_t magic = 0;
    memcpy(&magic, work_ptr, sizeof(magic));
    uint32_t tag = (magic != LEANQBE_M6_HDR_MAGIC ||
                    hdr[LEANQBE_HDR_OOM_IDX] != 0ULL)
                       ? 3u
                       : 2u;
    lean_dec_ref(work);
    return lean_box(tag);
  }

  lean_dec_ref(work);
  return lean_box(2); /* .unknown */
}
