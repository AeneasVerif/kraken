#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>
#include "../guarded_buf.h"
#include "kissat_cases.h"
#include "kissat_verify.h"

extern uint64_t kissat_solve_bytes(
    const uint8_t *cnf_ptr, uint64_t cnf_len,
    uint8_t *work_ptr, uint64_t work_len, uint64_t fuel);

int main(void) {
  size_t pg = (size_t)sysconf(_SC_PAGESIZE);
  for (size_t i = 0; i < kKissatCaseCount; i++) {
    const KissatDiffCase *tc = &kKissatCases[i];
    guarded_buf_t gc = alloc_guarded((const uint8_t *)tc->cnf, tc->cnf_len, 0);
    guarded_buf_t gw = alloc_guarded(NULL, tc->work_len, 1);
    uint8_t *w_mid = (uint8_t *)gw.base + pg;
    if (tc->work_len > 0) {
      memset(gw.ptr, 0xA5, tc->work_len);
    }

    uint64_t got = kissat_solve_bytes(gc.ptr, tc->cnf_len, gw.ptr, tc->work_len, tc->fuel);
    if (got != tc->expected) {
      fprintf(stderr, "FAIL %s: got=%llu exp=%llu\n", tc->name,
              (unsigned long long)got, (unsigned long long)tc->expected);
      return 1;
    }
    for (uint8_t *p = w_mid; p < gw.ptr; p++) {
      if (*p != 0xAA) {
        fprintf(stderr, "FAIL %s: wrote before work_ptr!\n", tc->name);
        return 1;
      }
    }
    if (got == 10ULL) {
      uintptr_t wp = (uintptr_t)gw.ptr;
      uintptr_t pad = (wp & 7u) ? (8u - (wp & 7u)) : 0u;
      const uint64_t *hdr = (const uint64_t *)(gw.ptr + pad);
      uint64_t mv = hdr[0];
      uintptr_t vp = (uintptr_t)hdr[8];
      assert(vp >= (uintptr_t)(gw.ptr + pad + 200u));
      assert(vp + mv * 2ULL <= (uintptr_t)(gw.ptr + tc->work_len));
      const int8_t *vals = (const int8_t *)vp;
      if (!kissat_verify_dimacs_model(tc->cnf, tc->cnf_len, vals, mv)) {
        fprintf(stderr, "FAIL %s: invalid SAT model!\n", tc->name);
        return 1;
      }
    }
    printf("CASE %s = %llu\n", tc->name, (unsigned long long)got);
    free_guarded(gw);
    free_guarded(gc);
  }
  printf("PASS: native guarded suite (%zu cases)\n", kKissatCaseCount);
  return 0;
}
