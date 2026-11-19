#ifndef LEANQBE_TEST_KISSAT_VERIFY_H
#define LEANQBE_TEST_KISSAT_VERIFY_H

#include <stdint.h>
#include <stddef.h>

static inline int kv_is_ws(uint8_t b) {
  return b == 32u || (b >= 9u && b <= 13u);
}

static inline int kv_is_dig(uint8_t b) {
  return b >= 48u && b <= 57u;
}

static inline uint64_t kv_skip_wsc(const uint8_t *s, uint64_t p, uint64_t n) {
  while (p < n) {
    if (kv_is_ws(s[p])) {
      p++;
    } else if (s[p] == (uint8_t)'c') {
      p++;
      while (p < n && s[p] != 10u) p++;
      if (p < n) p++;
    } else {
      break;
    }
  }
  return p;
}

static inline int kv_read_u64(const uint8_t *s, uint64_t *pp, uint64_t n, uint64_t *out) {
  uint64_t p = *pp;
  if (p >= n || !kv_is_dig(s[p])) return 0;
  uint64_t acc = (uint64_t)(s[p] - 48u);
  p++;
  while (p < n) {
    if (kv_is_dig(s[p])) {
      acc = acc * 10ULL + (uint64_t)(s[p] - 48u);
      if (acc >= 268435456ULL) return 0;
      p++;
    } else if (kv_is_ws(s[p])) {
      break;
    } else {
      return 0;
    }
  }
  *pp = p;
  *out = acc;
  return 1;
}

static inline int kissat_verify_dimacs_model(
    const char *cnf, uint64_t len, const int8_t *vals, uint64_t mv_max) {
  const uint8_t *s = (const uint8_t *)cnf;
  uint64_t p = kv_skip_wsc(s, 0ULL, len);
  if (p >= len || s[p] != (uint8_t)'p') return 0;
  p++;
  if (p >= len || !kv_is_ws(s[p])) return 0;
  while (p < len && kv_is_ws(s[p])) p++;
  if (len - p < 3ULL || s[p] != 'c' || s[p + 1] != 'n' || s[p + 2] != 'f') return 0;
  p += 3ULL;
  if (p >= len || !kv_is_ws(s[p])) return 0;
  while (p < len && kv_is_ws(s[p])) p++;
  uint64_t mv = 0ULL;
  uint64_t nc = 0ULL;
  if (!kv_read_u64(s, &p, len, &mv)) return 0;
  if (p >= len || !kv_is_ws(s[p])) return 0;
  while (p < len && kv_is_ws(s[p])) p++;
  if (!kv_read_u64(s, &p, len, &nc)) return 0;
  if (mv > mv_max) return 0;
  for (uint64_t v = 0ULL; v < mv; v++) {
    int8_t pos = vals[v * 2ULL];
    int8_t neg = vals[v * 2ULL + 1ULL];
    if (!((pos == 1 && neg == -1) || (pos == -1 && neg == 1))) return 0;
  }
  for (uint64_t i = 0ULL; i < nc; i++) {
    int sat = 0;
    while (1) {
      p = kv_skip_wsc(s, p, len);
      if (p >= len) return 0;
      int neg = 0;
      if (s[p] == (uint8_t)'-') {
        neg = 1;
        p++;
      }
      uint64_t v = 0ULL;
      if (!kv_read_u64(s, &p, len, &v)) return 0;
      if (v == 0ULL) {
        if (neg) return 0;
        break;
      }
      if (v > mv) return 0;
      int8_t vv = vals[(v - 1ULL) * 2ULL];
      if ((neg == 0 && vv > 0) || (neg != 0 && vv < 0)) sat = 1;
    }
    if (!sat) return 0;
  }
  p = kv_skip_wsc(s, p, len);
  return p == len ? 1 : 0;
}

#endif
