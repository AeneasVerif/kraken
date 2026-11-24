#ifndef GUARDED_BUF_H_
#define GUARDED_BUF_H_

#include <assert.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

typedef struct {
  void *base;
  size_t total;
  uint8_t *ptr;
  size_t len;
} guarded_buf_t;

static inline guarded_buf_t alloc_guarded(const uint8_t *init, size_t len, int writable) {
  size_t pg = (size_t)sysconf(_SC_PAGESIZE);
  size_t data_pages = ((len == 0 ? 1 : len) + pg - 1) / pg;
  size_t total = (data_pages + 2) * pg;
  uint8_t *base = (uint8_t *)mmap(NULL, total, PROT_NONE,
      MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  assert(base != MAP_FAILED);
  uint8_t *mid = base + pg;
  int rc = mprotect(mid, data_pages * pg, PROT_READ | PROT_WRITE);
  assert(rc == 0);
  uint8_t *ptr = mid + data_pages * pg - len;
  size_t prefix = (size_t)(ptr - mid);
  if (prefix > 0) {
    /* Only fill the <1-page pre-buffer slack; MAP_ANONYMOUS pages are already OS-zeroed. */
    memset(mid, 0xAA, prefix);
  }
  if (init && len > 0) {
    memcpy(ptr, init, len);
  }
  if (!writable) {
    rc = mprotect(mid, data_pages * pg, PROT_READ);
    assert(rc == 0);
  }
  guarded_buf_t g = { base, total, ptr, len };
  return g;
}

static inline void free_guarded(guarded_buf_t g) {
  int rc = munmap(g.base, g.total);
  assert(rc == 0);
}

#endif /* GUARDED_BUF_H_ */
