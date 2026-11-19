#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern void chacha20Block(uint8_t out[64], const uint8_t inp[64]);

static uint32_t rotl32(uint32_t v, int n) {
  return (v << n) | (v >> (32 - n));
}

static uint32_t load_le32(const uint8_t *p) {
  return ((uint32_t)p[0]) | ((uint32_t)p[1] << 8) |
         ((uint32_t)p[2] << 16) | ((uint32_t)p[3] << 24);
}

static void store_le32(uint8_t *p, uint32_t w) {
  p[0] = (uint8_t)(w & 0xff);
  p[1] = (uint8_t)((w >> 8) & 0xff);
  p[2] = (uint8_t)((w >> 16) & 0xff);
  p[3] = (uint8_t)((w >> 24) & 0xff);
}

static void qr(uint32_t x[16], int a, int b, int c, int d) {
  x[a] += x[b]; x[d] ^= x[a]; x[d] = rotl32(x[d], 16);
  x[c] += x[d]; x[b] ^= x[c]; x[b] = rotl32(x[b], 12);
  x[a] += x[b]; x[d] ^= x[a]; x[d] = rotl32(x[d], 8);
  x[c] += x[d]; x[b] ^= x[c]; x[b] = rotl32(x[b], 7);
}

static void ref_chacha20Block(uint8_t out[64], const uint8_t inp[64]) {
  uint32_t st[16], x[16];
  for (int i = 0; i < 16; i++) {
    st[i] = load_le32(inp + 4 * i);
    x[i] = st[i];
  }
  for (int r = 0; r < 10; r++) {
    qr(x, 0, 4,  8, 12);
    qr(x, 1, 5,  9, 13);
    qr(x, 2, 6, 10, 14);
    qr(x, 3, 7, 11, 15);
    qr(x, 0, 5, 10, 15);
    qr(x, 1, 6, 11, 12);
    qr(x, 2, 7,  8, 13);
    qr(x, 3, 4,  9, 14);
  }
  for (int i = 0; i < 16; i++) {
    store_le32(out + 4 * i, x[i] + st[i]);
  }
}

static void dump_hex(const char *label, const uint8_t *buf, size_t n) {
  fprintf(stderr, "%s:", label);
  for (size_t i = 0; i < n; i++) {
    fprintf(stderr, "%s%02x", (i % 16 == 0) ? "\n  " : " ", buf[i]);
  }
  fprintf(stderr, "\n");
}

static void run_case(const char *tag, size_t align_off, const uint8_t inp[64]) {
  uint8_t inp_buf[80];
  uint8_t out_buf[96];
  uint8_t ref[64];

  memset(inp_buf, 0xaa, sizeof(inp_buf));
  memset(out_buf, 0x55, sizeof(out_buf));
  uint8_t *pinp = inp_buf + align_off;
  uint8_t *pout = out_buf + 16 + align_off;
  memcpy(pinp, inp, 64);

  chacha20Block(pout, pinp);
  ref_chacha20Block(ref, inp);

  if (memcmp(pinp, inp, 64) != 0) {
    fprintf(stderr, "FAIL (%s): input modified\n", tag);
    exit(1);
  }
  for (size_t i = 0; i < 16 + align_off; i++) {
    if (out_buf[i] != 0x55) {
      fprintf(stderr, "FAIL (%s): leading guard byte %zu corrupted\n", tag, i);
      exit(1);
    }
  }
  for (size_t i = 16 + align_off + 64; i < sizeof(out_buf); i++) {
    if (out_buf[i] != 0x55) {
      fprintf(stderr, "FAIL (%s): trailing guard byte %zu corrupted\n", tag, i);
      exit(1);
    }
  }
  if (memcmp(pout, ref, 64) != 0) {
    fprintf(stderr, "FAIL (%s): output mismatch vs reference C\n", tag);
    dump_hex("got", pout, 64);
    dump_hex("ref", ref, 64);
    exit(1);
  }
}

int main(void) {
  /* RFC 8439 §2.3.2 initial 64-byte state ("expand 32-byte k" || key || counter=1 || nonce). */
  static const uint32_t RFC_WORDS[16] = {
    0x61707865u, 0x3320646eu, 0x79622d32u, 0x6b206574u,
    0x03020100u, 0x07060504u, 0x0b0a0908u, 0x0f0e0d0cu,
    0x13121110u, 0x17161514u, 0x1b1a1918u, 0x1f1e1d1cu,
    0x00000001u, 0x09000000u, 0x4a000000u, 0x00000000u,
  };
  static const uint8_t RFC_EXPECTED[64] = {
    0x10, 0xf1, 0xe7, 0xe4, 0xd1, 0x3b, 0x59, 0x15,
    0x50, 0x0f, 0xdd, 0x1f, 0xa3, 0x20, 0x71, 0xc4,
    0xc7, 0xd1, 0xf4, 0xc7, 0x33, 0xc0, 0x68, 0x03,
    0x04, 0x22, 0xaa, 0x9a, 0xc3, 0xd4, 0x6c, 0x4e,
    0xd2, 0x82, 0x64, 0x46, 0x07, 0x9f, 0xaa, 0x09,
    0x14, 0xc2, 0xd7, 0x05, 0xd9, 0x8b, 0x02, 0xa2,
    0xb5, 0x12, 0x9c, 0xd1, 0xde, 0x16, 0x4e, 0xb9,
    0xcb, 0xd0, 0x83, 0xe8, 0xa2, 0x50, 0x3c, 0x4e,
  };

  uint8_t rfc_inp[64];
  uint8_t rfc_out[64];
  for (int i = 0; i < 16; i++) {
    store_le32(rfc_inp + 4 * i, RFC_WORDS[i]);
  }
  chacha20Block(rfc_out, rfc_inp);
  if (memcmp(rfc_out, RFC_EXPECTED, 64) != 0) {
    fprintf(stderr, "FAIL (RFC 8439 §2.3.2): exact output mismatch\n");
    dump_hex("got", rfc_out, 64);
    dump_hex("exp", RFC_EXPECTED, 64);
    return 1;
  }
  run_case("rfc8439-aligned", 0, rfc_inp);
  run_case("rfc8439-unaligned", 3, rfc_inp);

  uint8_t zeros[64] = {0};
  uint8_t ones[64];
  memset(ones, 0xff, sizeof(ones));
  run_case("zeros", 0, zeros);
  run_case("ones", 1, ones);

  uint64_t rng = 0x9e3779b97f4a7c15ULL;
  for (int t = 0; t < 200; t++) {
    uint8_t rand_inp[64];
    for (int i = 0; i < 64; i++) {
      rng ^= rng >> 12;
      rng ^= rng << 25;
      rng ^= rng >> 27;
      rand_inp[i] = (uint8_t)((rng * 0x2545F4914F6CDD1DULL) >> 56);
    }
    char tag[32];
    snprintf(tag, sizeof(tag), "rand-%d", t);
    run_case(tag, (size_t)(t % 16), rand_inp);
  }

  printf("PASS t_chacha: RFC 8439 s2.3.2 exact + 204 differential blocks passed\n");
  return 0;
}
