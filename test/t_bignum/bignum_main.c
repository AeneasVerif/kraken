#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern void mul4x4(uint64_t out[8], const uint64_t a[4], const uint64_t b[4]);
extern void addMod25519(uint64_t out[4], const uint64_t a[4], const uint64_t b[4]);
extern void subMod25519(uint64_t out[4], const uint64_t a[4], const uint64_t b[4]);

static const uint64_t P25519[4] = {
  0xffffffffffffffedULL,
  0xffffffffffffffffULL,
  0xffffffffffffffffULL,
  0x7fffffffffffffffULL,
};

static const uint64_t GUARD_CANARY = 0xfeedfacecafebeefULL;

static int cmp4(const uint64_t a[4], const uint64_t b[4]) {
  for (int i = 3; i >= 0; i--) {
    if (a[i] < b[i]) return -1;
    if (a[i] > b[i]) return 1;
  }
  return 0;
}

static void add4(uint64_t out[4], const uint64_t a[4], const uint64_t b[4]) {
  __uint128_t c = 0;
  for (int i = 0; i < 4; i++) {
    __uint128_t s = (__uint128_t)a[i] + b[i] + c;
    out[i] = (uint64_t)s;
    c = s >> 64;
  }
}

static void sub4(uint64_t out[4], const uint64_t a[4], const uint64_t b[4]) {
  uint64_t borrow = 0;
  for (int i = 0; i < 4; i++) {
    __uint128_t rhs = (__uint128_t)b[i] + borrow;
    if ((__uint128_t)a[i] >= rhs) {
      out[i] = (uint64_t)((__uint128_t)a[i] - rhs);
      borrow = 0;
    } else {
      out[i] = (uint64_t)(((__uint128_t)1 << 64) + a[i] - rhs);
      borrow = 1;
    }
  }
}

static void ref_mul4x4(uint64_t out[8], const uint64_t a[4], const uint64_t b[4]) {
  uint64_t acc[8];
  memset(acc, 0, sizeof(acc));
  for (int i = 0; i < 4; i++) {
    __uint128_t carry = 0;
    for (int j = 0; j < 4; j++) {
      __uint128_t cur = (__uint128_t)a[j] * (__uint128_t)b[i] + acc[i + j] + carry;
      acc[i + j] = (uint64_t)cur;
      carry = cur >> 64;
    }
    acc[i + 4] = (uint64_t)carry;
  }
  memcpy(out, acc, sizeof(acc));
}

static void ref_addMod25519(uint64_t out[4], const uint64_t a[4], const uint64_t b[4]) {
  uint64_t s[4];
  add4(s, a, b);
  if (cmp4(s, P25519) >= 0) {
    sub4(out, s, P25519);
  } else {
    memcpy(out, s, 4 * sizeof(uint64_t));
  }
}

static void ref_subMod25519(uint64_t out[4], const uint64_t a[4], const uint64_t b[4]) {
  if (cmp4(a, b) >= 0) {
    sub4(out, a, b);
  } else {
    uint64_t ap[4];
    add4(ap, a, P25519);
    sub4(out, ap, b);
  }
}

static uint64_t splitmix64(uint64_t *state) {
  uint64_t z = (*state += 0x9e3779b97f4a7c15ULL);
  z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
  z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
  return z ^ (z >> 31);
}

static void print_limbs(const char *label, const uint64_t *v, int n) {
  fprintf(stderr, "%s = [", label);
  for (int i = 0; i < n; i++) {
    fprintf(stderr, "%s0x%016" PRIx64, i ? ", " : "", v[i]);
  }
  fprintf(stderr, "]\n");
}

static void check_mul(const char *tag, int idx, const uint64_t a_in[4], const uint64_t b_in[4]) {
  uint64_t a[4], b[4], ref[8];
  uint64_t out_guard[10];
  memcpy(a, a_in, sizeof(a));
  memcpy(b, b_in, sizeof(b));
  out_guard[0] = GUARD_CANARY;
  out_guard[9] = GUARD_CANARY;
  memset(out_guard + 1, 0xa5, 8 * sizeof(uint64_t));

  mul4x4(out_guard + 1, a, b);
  ref_mul4x4(ref, a_in, b_in);

  if (out_guard[0] != GUARD_CANARY || out_guard[9] != GUARD_CANARY) {
    fprintf(stderr, "FAIL mul4x4 (%s #%d): guard canary corrupted\n", tag, idx);
    exit(1);
  }
  if (memcmp(a, a_in, sizeof(a)) != 0 || memcmp(b, b_in, sizeof(b)) != 0) {
    fprintf(stderr, "FAIL mul4x4 (%s #%d): input buffer modified\n", tag, idx);
    exit(1);
  }
  if (memcmp(out_guard + 1, ref, sizeof(ref)) != 0) {
    fprintf(stderr, "FAIL mul4x4 (%s #%d): mismatch\n", tag, idx);
    print_limbs("  a  ", a_in, 4);
    print_limbs("  b  ", b_in, 4);
    print_limbs("  got", out_guard + 1, 8);
    print_limbs("  ref", ref, 8);
    exit(1);
  }
}

static void check_mod(const char *tag, int idx, const uint64_t a_in[4], const uint64_t b_in[4]) {
  if (cmp4(a_in, P25519) >= 0 || cmp4(b_in, P25519) >= 0) {
    fprintf(stderr, "INTERNAL ERROR (%s #%d): input >= p25519\n", tag, idx);
    exit(2);
  }
  uint64_t a[4], b[4], ref_add[4], ref_sub[4];
  uint64_t out_add[6], out_sub[6];
  memcpy(a, a_in, sizeof(a));
  memcpy(b, b_in, sizeof(b));

  out_add[0] = GUARD_CANARY;
  out_add[5] = GUARD_CANARY;
  memset(out_add + 1, 0x5a, 4 * sizeof(uint64_t));
  addMod25519(out_add + 1, a, b);
  ref_addMod25519(ref_add, a_in, b_in);

  if (out_add[0] != GUARD_CANARY || out_add[5] != GUARD_CANARY ||
      memcmp(a, a_in, sizeof(a)) != 0 || memcmp(b, b_in, sizeof(b)) != 0 ||
      memcmp(out_add + 1, ref_add, sizeof(ref_add)) != 0 ||
      cmp4(out_add + 1, P25519) >= 0) {
    fprintf(stderr, "FAIL addMod25519 (%s #%d)\n", tag, idx);
    print_limbs("  a  ", a_in, 4);
    print_limbs("  b  ", b_in, 4);
    print_limbs("  got", out_add + 1, 4);
    print_limbs("  ref", ref_add, 4);
    exit(1);
  }

  out_sub[0] = GUARD_CANARY;
  out_sub[5] = GUARD_CANARY;
  memset(out_sub + 1, 0x3c, 4 * sizeof(uint64_t));
  subMod25519(out_sub + 1, a, b);
  ref_subMod25519(ref_sub, a_in, b_in);

  if (out_sub[0] != GUARD_CANARY || out_sub[5] != GUARD_CANARY ||
      memcmp(a, a_in, sizeof(a)) != 0 || memcmp(b, b_in, sizeof(b)) != 0 ||
      memcmp(out_sub + 1, ref_sub, sizeof(ref_sub)) != 0 ||
      cmp4(out_sub + 1, P25519) >= 0) {
    fprintf(stderr, "FAIL subMod25519 (%s #%d)\n", tag, idx);
    print_limbs("  a  ", a_in, 4);
    print_limbs("  b  ", b_in, 4);
    print_limbs("  got", out_sub + 1, 4);
    print_limbs("  ref", ref_sub, 4);
    exit(1);
  }
}

typedef struct { uint64_t v[4]; } Limb4;

int main(void) {
  static const Limb4 MUL_EDGES[] = {
    {{0ULL, 0ULL, 0ULL, 0ULL}},
    {{1ULL, 0ULL, 0ULL, 0ULL}},
    {{19ULL, 0ULL, 0ULL, 0ULL}},
    {{~0ULL, 0ULL, 0ULL, 0ULL}},
    {{0ULL, 1ULL, 0ULL, 0ULL}},
    {{~0ULL, ~0ULL, 0ULL, 0ULL}},
    {{~0ULL, ~0ULL, ~0ULL, 0ULL}},
    {{0ULL, 0ULL, 0ULL, 1ULL << 63}},
    {{0xffffffffffffffecULL, ~0ULL, ~0ULL, 0x7fffffffffffffffULL}}, /* p25519 - 1 */
    {{0xffffffffffffffedULL, ~0ULL, ~0ULL, 0x7fffffffffffffffULL}}, /* p25519 */
    {{0xffffffffffffffeeULL, ~0ULL, ~0ULL, 0x7fffffffffffffffULL}}, /* p25519 + 1 */
    {{~0ULL, ~0ULL, ~0ULL, ~0ULL}},                                 /* 2^256 - 1 */
    {{~0ULL, 0ULL, ~0ULL, 0ULL}},
    {{0ULL, ~0ULL, 0ULL, ~0ULL}},
    {{0xaaaaaaaaaaaaaaaaULL, 0x5555555555555555ULL,
      0xaaaaaaaaaaaaaaaaULL, 0x5555555555555555ULL}},
    {{0x8000000000000000ULL, 0x8000000000000000ULL,
      0x8000000000000000ULL, 0x8000000000000000ULL}},
  };
  const int n_mul_edges = (int)(sizeof(MUL_EDGES) / sizeof(MUL_EDGES[0]));
  int mul_count = 0;
  for (int i = 0; i < n_mul_edges; i++) {
    for (int j = 0; j < n_mul_edges; j++) {
      check_mul("edge", mul_count++, MUL_EDGES[i].v, MUL_EDGES[j].v);
    }
  }

  static const Limb4 MOD_EDGES[] = {
    {{0ULL, 0ULL, 0ULL, 0ULL}},
    {{1ULL, 0ULL, 0ULL, 0ULL}},
    {{18ULL, 0ULL, 0ULL, 0ULL}},
    {{19ULL, 0ULL, 0ULL, 0ULL}},
    {{20ULL, 0ULL, 0ULL, 0ULL}},
    {{0xffffffffffffffedULL, 0ULL, 0ULL, 0ULL}},
    {{~0ULL, 0ULL, 0ULL, 0ULL}},
    {{0ULL, 1ULL, 0ULL, 0ULL}},
    {{~0ULL, ~0ULL, 0ULL, 0ULL}},
    {{~0ULL, ~0ULL, ~0ULL, 0ULL}},
    {{0ULL, 0ULL, 0ULL, 1ULL << 62}},
    {{0xfffffffffffffff6ULL, ~0ULL, ~0ULL, 0x3fffffffffffffffULL}}, /* (p25519 - 1) / 2 */
    {{0xfffffffffffffff7ULL, ~0ULL, ~0ULL, 0x3fffffffffffffffULL}}, /* (p25519 + 1) / 2 */
    {{0xffffffffffffffebULL, ~0ULL, ~0ULL, 0x7fffffffffffffffULL}}, /* p25519 - 2 */
    {{0xffffffffffffffecULL, ~0ULL, ~0ULL, 0x7fffffffffffffffULL}}, /* p25519 - 1 */
    {{0ULL, ~0ULL, 0ULL, 0x7fffffffffffffffULL}},
    {{0xffffffffffffffecULL, 0ULL, ~0ULL, 0x7fffffffffffffffULL}},
  };
  const int n_mod_edges = (int)(sizeof(MOD_EDGES) / sizeof(MOD_EDGES[0]));
  int mod_count = 0;
  for (int i = 0; i < n_mod_edges; i++) {
    for (int j = 0; j < n_mod_edges; j++) {
      check_mod("edge", mod_count++, MOD_EDGES[i].v, MOD_EDGES[j].v);
    }
  }

  uint64_t rng = 0x123456789abcdef0ULL;
  for (int t = 0; t < 1000; t++) {
    uint64_t a[4], b[4];
    for (int k = 0; k < 4; k++) {
      a[k] = splitmix64(&rng);
      b[k] = splitmix64(&rng);
    }
    check_mul("rand", mul_count++, a, b);

    a[3] &= 0x7fffffffffffffffULL;
    b[3] &= 0x7fffffffffffffffULL;
    if (cmp4(a, P25519) >= 0) sub4(a, a, P25519);
    if (cmp4(b, P25519) >= 0) sub4(b, b, P25519);
    check_mod("rand", mod_count++, a, b);
  }

  printf("PASS t_bignum: mul4x4 (%d cases), addMod25519 (%d cases), subMod25519 (%d cases)\n",
         mul_count, mod_count, mod_count);
  return 0;
}
