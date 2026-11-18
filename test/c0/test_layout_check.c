#include "test_layout.c"

#include <stdio.h>
#include <stdlib.h>

#define CHECK_EQ(expr, expected)                                             \
  do {                                                                       \
    u64 _v = (u64)(expr);                                                    \
    u64 _e = (u64)(expected);                                                \
    if (_v != _e) {                                                          \
      fprintf(stderr, "LAYOUT MISMATCH %s: got %llu, expected %llu\n",       \
              #expr, (unsigned long long)_v, (unsigned long long)_e);        \
      return 1;                                                              \
    }                                                                        \
  } while (0)

int main(void) {
  CHECK_EQ(sizeof(watch), 4);
  CHECK_EQ(__alignof__(watch), 4);

  CHECK_EQ(sizeof(struct clause), 12);
  CHECK_EQ(__alignof__(struct clause), 4);
  CHECK_EQ(offsetof(struct clause, searched), 4);
  CHECK_EQ(offsetof(struct clause, size), 8);
  CHECK_EQ(offsetof(struct clause, lits), 12);

  struct clause c;
  memset(&c, 0, sizeof(c));
  set_clause_bits(&c, 0x54321u, true, 19u);
  CHECK_EQ(read_clause_header_word(&c), 0x54321u | (1u << 19) | (19u << 27));
  const u8 *cb = (const u8 *)&c;
  /* garbage is byte 2, bit 3 (0x08) */
  CHECK_EQ((cb[2] >> 3) & 1u, 1u);

  CHECK_EQ(pack_watch_bin(0x123456u, true), 0x80123456u);
  CHECK_EQ(pack_watch_bin(0x123456u, false), 0x00123456u);

  CHECK_EQ(sizeof(struct assigned), 16);
  CHECK_EQ(__alignof__(struct assigned), 4);
  CHECK_EQ(offsetof(struct assigned, trail), 8);
  CHECK_EQ(offsetof(struct assigned, reason), 12);
  struct assigned a;
  memset(&a, 0, sizeof(a));
  a.analyzed = 2u;
  a.poison = true;
  a.reason_flag = false;
  a.redundant = true;
  a.shrinkable = true;
  const u8 *ab = (const u8 *)&a;
  CHECK_EQ(ab[4], (2u | (1u << 2) | (0u << 3) | (1u << 4) | (1u << 5)));

  CHECK_EQ(sizeof(struct lean_object), 8);
  CHECK_EQ(__alignof__(struct lean_object), 4);
  CHECK_EQ(offsetof(struct lean_object, m_rc), 0);
  CHECK_EQ(offsetof(struct lean_object, m_cs_sz), 4);
  CHECK_EQ(offsetof(struct lean_object, m_other), 6);
  CHECK_EQ(offsetof(struct lean_object, m_tag), 7);
  struct lean_object lo;
  lo.m_rc = 0x11223344;
  lo.m_cs_sz = 0x5566u;
  lo.m_other = 0x77u;
  lo.m_tag = 0x88u;
  CHECK_EQ(read_lean_header_word(&lo), 0x8877556611223344ULL);

  CHECK_EQ(sizeof(struct mixed_bf), 16);
  CHECK_EQ(__alignof__(struct mixed_bf), 8);
  struct mixed_bf mb;
  memset(&mb, 0, sizeof(mb));
  mb.tag = 0xAAu;
  mb.flag = true;
  mb.val = 0xBCDEFu;
  mb.wide = 0x123456789AULL;
  const u64 *mw = (const u64 *)&mb;
  CHECK_EQ(mw[1], 0x123456789AULL);

  printf("V1 C99 layout parity passed.\n");
  return 0;
}
