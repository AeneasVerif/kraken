#include "../../LeanQbe/T/Frontend/C0/c0.h"

/* V2: C0 port of Kissat watch-list propagation (proplit.h, COMPACT mode) */

typedef union {
  struct {
    u32 lit : 31;
    u32 binary : 1;
  } b;
  u32 raw;
} watch;

typedef struct clause {
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
} clause;

typedef struct {
  u32 level;
  u32 analyzed : 2;
  bool poison : 1;
  bool reason_flag : 1;
  bool redundant : 1;
  bool shrinkable : 1;
  u32 trail;
  u32 reason;
} assigned;

typedef struct {
  u64 *begin;
  u64 *end;
  u64 *allocated;
} ward_stack;

typedef struct {
  u32 *begin;
  u32 *end;
  u32 *allocated;
} u32_stack;

typedef struct {
  u32 offset;
  u32 size;
} vector;

typedef struct {
  u32_stack stack;
} vectors;

typedef struct {
  u32 *begin;
  u32 *end;
  u32 *allocated;
} trail_array;

typedef struct {
  vector *watches;
  vectors vectors;
  ward_stack arena;
  assigned *assigned;
  i8 *values;
  u32_stack delayed;
  trail_array trail;
  clause *conflict;
  u64 ticks;
  u32 level;
  u32 unassigned;
} kissat;

static inline u64 *stack_begin(ward_stack *s) {
  return s->begin;
}

static inline u32 stack_size(ward_stack *s) {
  return (u32)(s->end - s->begin);
}

static inline u32 *vector_begin(kissat *solver, vector *v) {
  return solver->vectors.stack.begin + v->offset;
}

static inline u32 *vector_end(kissat *solver, vector *v) {
  return solver->vectors.stack.begin + v->offset + v->size;
}

static inline u32 vector_size(vector *v) {
  return v->size;
}

static inline void vector_set_end(kissat *solver, vector *v, u32 *q) {
  u32 *b = solver->vectors.stack.begin + v->offset;
  v->size = (u32)(q - b);
}

static inline u64 cache_lines(u32 n, u32 elem_bytes) {
  u64 bytes = (u64)n * (u64)elem_bytes;
  if (bytes == 0ULL) return 0ULL;
  return (bytes + 63ULL) >> 6;
}

static inline clause *binary_conflict(kissat *solver, u32 a, u32 b) {
  clause *res = solver->conflict;
  res->size = 2u;
  res->lits[0] = a;
  res->lits[1] = b;
  return res;
}

static inline void fast_binary_assign(kissat *solver, u32 level, i8 *values,
                                      assigned *asg, u32 lit, u32 other) {
  values[lit] = (i8)1;
  values[lit ^ 1u] = (i8)-1;
  u32 idx = lit >> 1;
  asg[idx].level = level;
  asg[idx].reason = other;
  asg[idx].reason_flag = true;
  u32 pos = (u32)(solver->trail.end - solver->trail.begin);
  asg[idx].trail = pos;
  check(solver->trail.end < solver->trail.allocated);
  *solver->trail.end = lit;
  solver->trail.end = solver->trail.end + 1;
  solver->unassigned = solver->unassigned - 1u;
}

static inline void fast_assign_reference(kissat *solver, i8 *values, assigned *asg,
                                         u32 lit, ref r, clause *c) {
  values[lit] = (i8)1;
  values[lit ^ 1u] = (i8)-1;
  u32 idx = lit >> 1;
  asg[idx].level = solver->level;
  asg[idx].reason = r;
  asg[idx].reason_flag = false;
  u32 pos = (u32)(solver->trail.end - solver->trail.begin);
  asg[idx].trail = pos;
  check(solver->trail.end < solver->trail.allocated);
  *solver->trail.end = lit;
  solver->trail.end = solver->trail.end + 1;
  solver->unassigned = solver->unassigned - 1u;
  if (c->redundant && c->used < 31u) {
    c->used = c->used + 1u;
  }
}

static inline void delay_watching_large(kissat *solver, u32_stack *delayed,
                                        u32 lit, u32 other, ref r) {
  check(solver != NULL);
  u32 *end = delayed->end;
  check(end + 3 <= delayed->allocated);
  watch w = {0};
  w.b.lit = other;
  w.b.binary = 0u;
  end[0] = lit;
  end[1] = w.raw;
  end[2] = r;
  delayed->end = end + 3;
}

static inline void watch_large_delayed(kissat *solver, vector *all_watches,
                                       u32_stack *delayed) {
  u32 *d_begin = delayed->begin;
  u32 *d_end = delayed->end;
  u32 *d = d_begin;
  while (d < d_end) {
    u32 lit = d[0];
    u32 w_raw = d[1];
    ref r = d[2];
    d = d + 3;
    vector *ws = all_watches + lit;
    u32 sz = ws->size;
    u32 *old_begin = solver->vectors.stack.begin + ws->offset;
    u32 *stack_end = solver->vectors.stack.end;
    if (old_begin + sz == stack_end) {
      check(stack_end + 2 <= solver->vectors.stack.allocated);
      stack_end[0] = w_raw;
      stack_end[1] = r;
      ws->size = sz + 2u;
      solver->vectors.stack.end = stack_end + 2;
    } else {
      u32 *dst = stack_end;
      check(dst + sz + 2 <= solver->vectors.stack.allocated);
      u32 new_off = (u32)(dst - solver->vectors.stack.begin);
      u32 i = 0u;
      while (i < sz) {
        dst[i] = old_begin[i];
        i = i + 1u;
      }
      dst[sz] = w_raw;
      dst[sz + 1u] = r;
      ws->offset = new_off;
      ws->size = sz + 2u;
      solver->vectors.stack.end = dst + sz + 2u;
    }
  }
  delayed->end = d_begin;
}

clause *search_propagate_literal(kissat *solver, u32 lit) {
  vector *all_watches = solver->watches;
  u64 *arena = stack_begin(&solver->arena);
  assigned *asg = solver->assigned;
  i8 *values = solver->values;
  u32 not_lit = lit ^ 1u;
  vector *ws = all_watches + not_lit;
  watch *begin = (watch *)vector_begin(solver, ws);
  watch *end = (watch *)vector_end(solver, ws);
  watch *q = begin;
  watch *p = begin;
  u64 ticks = 1ULL + cache_lines(vector_size(ws), 4u);
  u32 level = asg[lit >> 1].level;
  clause *res = NULL;
  while (p != end) {
    watch head = *p;
    *q = head;
    p = p + 1;
    q = q + 1;
    u32 blocking = head.b.lit;
    i8 bval = values[blocking];
    watch tail = head;
    if (!head.b.binary) {
      tail = *p;
      *q = tail;
      p = p + 1;
      q = q + 1;
    }
    if (bval > 0) continue;
    if (head.b.binary) {
      if (bval < 0) {
        res = binary_conflict(solver, not_lit, blocking);
        break;
      }
      fast_binary_assign(solver, level, values, asg, blocking, not_lit);
      ticks = ticks + 1ULL;
      continue;
    }
    ref r0 = tail.raw;
    check(r0 < stack_size(&solver->arena));
    clause *c = (clause *)(arena + r0);
    ticks = ticks + 1ULL;
    if (c->garbage) {
      q = q - 2;
      continue;
    }
    u32 *lits = c->lits;
    u32 other = lits[0] ^ lits[1] ^ not_lit;
    i8 oval = values[other];
    if (oval > 0) {
      q[-2].b.lit = other;
      continue;
    }
    u32 *endl = lits + c->size;
    u32 *srch = lits + c->searched;
    u32 *r = srch;
    u32 repl = 0xffffffffu;
    i8 rval = (i8)-1;
    while (r != endl) {
      repl = *r;
      rval = values[repl];
      if (rval >= 0) break;
      r = r + 1;
    }
    if (rval < 0) {
      r = lits + 2;
      while (r != srch) {
        repl = *r;
        rval = values[repl];
        if (rval >= 0) break;
        r = r + 1;
      }
    }
    if (rval >= 0) {
      c->searched = (u32)(r - lits);
      q = q - 2;
      lits[0] = other;
      lits[1] = repl;
      *r = not_lit;
      delay_watching_large(solver, &solver->delayed, repl, other, r0);
      ticks = ticks + 1ULL;
    } else if (oval != 0) {
      res = c;
      break;
    } else {
      fast_assign_reference(solver, values, asg, other, r0, c);
      ticks = ticks + 1ULL;
    }
  }
  solver->ticks = solver->ticks + ticks;
  while (p != end) {
    *q = *p;
    q = q + 1;
    p = p + 1;
  }
  vector_set_end(solver, ws, (u32 *)q);
  watch_large_delayed(solver, all_watches, &solver->delayed);
  return res;
}
