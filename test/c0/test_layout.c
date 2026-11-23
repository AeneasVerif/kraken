#include "../../LeanQbe/T/Frontend/C0/c0.h"

/* Layout parity fixtures matching Kissat & Lean 4 LP64 layouts */

typedef union {
  struct {
    u32 lit : 31;
    u32 binary : 1;
  } b;
  u32 raw;
} watch;

struct clause {
  u32 glue : 19;
  bool garbage : 1;
  bool quotient : 1;
  bool reason : 1;
  bool redundant : 1;
  bool shrunken : 1;
  bool subsume : 1;
  bool swept : 1;
  bool vivify : 1;
  u32 used : 5;
  u32 searched;
  u32 size;
  u32 lits[];
};

struct assigned {
  u32 level;
  u32 analyzed : 2;
  bool poison : 1;
  bool reason_flag : 1;
  bool redundant : 1;
  bool shrinkable : 1;
  u32 trail;
  u32 reason;
};

struct lean_object {
  i32 m_rc;
  u16 m_cs_sz;
  u8 m_other;
  u8 m_tag;
};

struct mixed_bf {
  u8 tag;
  bool flag : 1;
  u32 val : 20;
  u64 wide : 40;
};

u32 pack_watch_bin(u32 lit, bool bin) {
  watch w = {0};
  w.b.lit = lit;
  w.b.binary = bin ? 1u : 0u;
  return w.raw;
}

void set_clause_bits(struct clause *c, u32 glue, bool garbage, u32 used) {
  c->glue = glue;
  c->garbage = garbage;
  c->used = used;
}

u32 read_clause_header_word(struct clause *c) {
  u32 *p = (u32 *)c;
  return *p;
}

u64 read_lean_header_word(struct lean_object *o) {
  u64 *p = (u64 *)o;
  return *p;
}
