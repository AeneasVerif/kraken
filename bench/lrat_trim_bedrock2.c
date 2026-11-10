#include <stdint.h>
_Noreturn void lrat_fail(uintptr_t, uintptr_t, uintptr_t, uintptr_t, uintptr_t);

#include <stdint.h>
#if UINTPTR_MAX != 0xFFFFFFFFFFFFFFFFu
#error "this module requires 64-bit words"
#endif
// Generated from Bedrock code. Avoid editing directly.
#include <stdint.h>
#include <string.h>
#include <assert.h>
#include <limits.h>

#define BR_WORD_MAX UINTPTR_MAX
typedef uintptr_t br_word_t;
typedef intptr_t br_signed_t;

static_assert(sizeof(br_word_t) == sizeof(br_signed_t), "signed size");
static_assert(UINTPTR_MAX <= BR_WORD_MAX, "pointer fits in int");
static_assert(~(br_signed_t)0 == -(br_signed_t)1, "two's complement");
static_assert(sizeof(br_word_t) <= 8, "word fits in 64 bits");
static_assert(UINTPTR_MAX >= UINT_MAX, "no promotion to int");
static_assert(UINT_MAX >= 0xffffffff, "int has at least 32 bits");
static_assert(BR_WORD_MAX == UINT32_MAX ? sizeof(br_word_t) == 4 :
              BR_WORD_MAX == UINT64_MAX && sizeof(br_word_t) == 8, "word is 32 or 64 bits");
static_assert(_Generic((uint8_t)0, unsigned char: 1, default: 0), "uint8_t is unsigned char");
static_assert((br_signed_t)BR_WORD_MAX == -1, "modular conversion to signed");
static_assert(((br_signed_t)-1 >> 1) == -1, "arithmetic right shift");

#if defined(linux) || defined(unix)
  #error "compile with -std=c11 or later (not gnu*)"
#endif

#if __STDC_VERSION__ >= 202311L && __has_include(<stdbit.h>)
  #include <stdbit.h>
  static_assert(__STDC_ENDIAN_NATIVE__ == __STDC_ENDIAN_LITTLE__, "little-endian");
#elif defined(__GNUC__) && defined(__BYTE_ORDER__) && defined(__ORDER_LITTLE_ENDIAN__)
  static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__, "little-endian");
#elif defined(_MSC_VER) && !defined(__clang__) &&                              \
    (defined(_M_IX86) || defined(_M_X64) || defined(_M_ARM) || defined(_M_ARM64))
  // these MSVC targets are little-endian
#else
  #error "failed to confirm that target is little-endian"
#endif

// "An object shall have its stored value accessed only ... a character type."
static inline br_word_t _br_load1(br_word_t a) {
  return *((uint8_t *)a);
}

static inline br_word_t _br_load2(br_word_t a) {
  uint16_t r = 0;
  memcpy(&r, (void *)a, sizeof(r));
  return r;
}

static inline br_word_t _br_load4(br_word_t a) {
  uint32_t r = 0;
  memcpy(&r, (void *)a, sizeof(r));
  return r;
}

static inline br_word_t _br_load8(br_word_t a) {
  uint64_t r = 0;
  memcpy(&r, (void *)a, sizeof(r));
  return (br_word_t)r;
}

static inline void _br_store1(br_word_t a, br_word_t v) {
  *((uint8_t *)a) = (uint8_t)v;
}

static inline void _br_store2(br_word_t a, br_word_t v) {
  uint16_t r = (uint16_t)v;
  memcpy((void *)a, &r, sizeof(r));
}

static inline void _br_store4(br_word_t a, br_word_t v) {
  uint32_t r = (uint32_t)v;
  memcpy((void *)a, &r, sizeof(r));
}

static inline void _br_store8(br_word_t a, br_word_t v) {
  uint64_t r = (uint64_t)v;
  memcpy((void *)a, &r, sizeof(r));
}

#if defined(_MSC_VER)
  #include <intrin.h>
#endif

static inline br_word_t _br_mulhuu(br_word_t a, br_word_t b) {
  #if BR_WORD_MAX == UINT32_MAX
	  return ((uint64_t)a * b) >> 32;
  #elif BR_WORD_MAX == UINT64_MAX && (defined(__GNUC__) || defined(__clang__))
    return ((unsigned __int128)a * b) >> 64;
  #elif defined(_M_X64)
    uint64_t hi;
    _umul128(a, b, &hi);
    return hi;
  #elif defined(_M_ARM64)
    return __umulh(a, b);
  #else
    // See full_mul.v
    br_word_t hh, lh, hl, second_halfword_w_oflow, n, ll, M;
    n = ((((0u-(br_word_t)0x1)>>27)&0x3f)+0x1)>>1;
    M = ((br_word_t)0x1<<n)-0x1;
    ll = (a&M)*(b&M);
    lh = (a&M)*(b>>n);
    hl = (a>>n)*(b&M);
    hh = (a>>n)*(b>>n);
    second_halfword_w_oflow = ((ll>>n)+(lh&M))+(hl&M);
    return ((hh+(lh>>n))+(hl>>n))+(second_halfword_w_oflow>>n);
  #endif
}

static inline br_word_t _br_divu(br_word_t a, br_word_t b) {
  if (!b) return -1;
  return a/b;
}

static inline br_word_t _br_remu(br_word_t a, br_word_t b) {
  if (!b) return a;
  return a%b;
}

void br_trim_proof(br_word_t st);
void br_check_proof(br_word_t st);
void br_check_clause(br_word_t st, br_word_t id, br_word_t literals, br_word_t antecedents);
static br_word_t br_is_original_clause(br_word_t first_proof_id, br_word_t id);
static br_word_t br_mark_used(br_word_t st, br_word_t id, br_word_t used_where);
static void br_assign_literal(br_word_t st, br_word_t lit);
static void br_unassign_literal(br_word_t st, br_word_t lit);
static void br_backtrack(br_word_t st);
static br_word_t br_assigned_literal(br_word_t st, br_word_t lit);
void br_check_clause_non_strictly_by_propagation(br_word_t st, br_word_t id, br_word_t literals, br_word_t antecedents);
static void br_check_clause_strictly_by_resolution(br_word_t st, br_word_t id, br_word_t literals, br_word_t antecedents);

void br_trim_proof(br_word_t st) {
  br_word_t trimming, empty_clause, work_begin, antecedents_begin, used_begin, w, id, used_before, first_proof_id, was_used, is_orig, work_end, p, other, raw, stat_trimmed_cnf, stat_trimmed_prf;
  trimming = _br_load8(st+88);
  if (trimming) {
    empty_clause = (br_word_t)((br_signed_t)((_br_load8(st+64))<<((br_word_t)32&(sizeof(br_word_t)*8-1)))>>((br_word_t)32&(sizeof(br_word_t)*8-1)));
    if (empty_clause) {
      used_begin = _br_load8(st);
      antecedents_begin = _br_load8(st+8);
      work_begin = _br_load8(st+56);
      work_end = work_begin;
      first_proof_id = (br_word_t)((br_signed_t)((_br_load8(st+72))<<((br_word_t)32&(sizeof(br_word_t)*8-1)))>>((br_word_t)32&(sizeof(br_word_t)*8-1)));
      stat_trimmed_cnf = _br_load8(st+112);
      stat_trimmed_prf = _br_load8(st+120);
      w = used_begin+(empty_clause<<2);
      used_before = (br_word_t)((br_signed_t)((_br_load4(w))<<((br_word_t)32&(sizeof(br_word_t)*8-1)))>>((br_word_t)32&(sizeof(br_word_t)*8-1)));
      if ((br_word_t)(((br_word_t)((br_signed_t)used_before<(br_signed_t)empty_clause))==(br_word_t)0)) {
        was_used = (br_word_t)1;
      } else {
        _br_store4(w, empty_clause);
        if (used_before) {
          was_used = (br_word_t)1;
        } else {
          is_orig = ((br_word_t)(first_proof_id==(br_word_t)0))|((br_word_t)((br_signed_t)empty_clause<(br_signed_t)first_proof_id));
          if (is_orig) {
            stat_trimmed_cnf = stat_trimmed_cnf+1;
          } else {
            stat_trimmed_prf = stat_trimmed_prf+1;
          }
          was_used = (br_word_t)0;
        }
      }
      if (((br_word_t)(first_proof_id==(br_word_t)0))|((br_word_t)((br_signed_t)empty_clause<(br_signed_t)first_proof_id))) {
        /*skip*/
      } else {
        _br_store4(work_end, empty_clause);
        work_end = work_end+4;
      }
      while ((br_word_t)(((br_word_t)(work_end==work_begin))==(br_word_t)0)) {
        work_end = work_end-4;
        id = (br_word_t)((br_signed_t)((_br_load4(work_end))<<((br_word_t)32&(sizeof(br_word_t)*8-1)))>>((br_word_t)32&(sizeof(br_word_t)*8-1)));
        p = _br_load8(antecedents_begin+(id<<3));
        raw = (br_word_t)((br_signed_t)((_br_load4(p))<<((br_word_t)32&(sizeof(br_word_t)*8-1)))>>((br_word_t)32&(sizeof(br_word_t)*8-1)));
        other = ((br_word_t)((br_signed_t)raw<(br_signed_t)(br_word_t)0)) ? (0u-raw) : raw;
        while (other) {
          w = used_begin+(other<<2);
          used_before = (br_word_t)((br_signed_t)((_br_load4(w))<<((br_word_t)32&(sizeof(br_word_t)*8-1)))>>((br_word_t)32&(sizeof(br_word_t)*8-1)));
          if ((br_word_t)(((br_word_t)((br_signed_t)used_before<(br_signed_t)id))==(br_word_t)0)) {
            was_used = (br_word_t)1;
          } else {
            _br_store4(w, id);
            if (used_before) {
              was_used = (br_word_t)1;
            } else {
              is_orig = ((br_word_t)(first_proof_id==(br_word_t)0))|((br_word_t)((br_signed_t)other<(br_signed_t)first_proof_id));
              if (is_orig) {
                stat_trimmed_cnf = stat_trimmed_cnf+1;
              } else {
                stat_trimmed_prf = stat_trimmed_prf+1;
              }
              was_used = (br_word_t)0;
            }
          }
          if ((br_word_t)(was_used==(br_word_t)0)) {
            if ((br_word_t)(is_orig==(br_word_t)0)) {
              _br_store4(work_end, other);
              work_end = work_end+4;
            } else {
              /*skip*/
            }
          } else {
            /*skip*/
          }
          p = p+4;
          raw = (br_word_t)((br_signed_t)((_br_load4(p))<<((br_word_t)32&(sizeof(br_word_t)*8-1)))>>((br_word_t)32&(sizeof(br_word_t)*8-1)));
          other = ((br_word_t)((br_signed_t)raw<(br_signed_t)(br_word_t)0)) ? (0u-raw) : raw;
        }
      }
      _br_store8(st+112, stat_trimmed_cnf);
      _br_store8(st+120, stat_trimmed_prf);
    } else {
      /*skip*/
    }
  } else {
    /*skip*/
  }
}

void br_check_proof(br_word_t st) {
  br_word_t checking, forward, first_proof_id, empty_clause, trimming, used_begin, used_where, literals_begin, antecedents_begin, l, a, id;
  checking = _br_load8(st+96);
  forward = _br_load8(st+104);
  empty_clause = (br_word_t)((br_signed_t)((_br_load8(st+64))<<((br_word_t)32&(sizeof(br_word_t)*8-1)))>>((br_word_t)32&(sizeof(br_word_t)*8-1)));
  first_proof_id = (br_word_t)((br_signed_t)((_br_load8(st+72))<<((br_word_t)32&(sizeof(br_word_t)*8-1)))>>((br_word_t)32&(sizeof(br_word_t)*8-1)));
  if (checking) {
    if ((br_word_t)(forward==(br_word_t)0)) {
      if (empty_clause) {
        if (first_proof_id) {
          trimming = _br_load8(st+88);
          used_begin = _br_load8(st);
          literals_begin = _br_load8(st+16);
          antecedents_begin = _br_load8(st+8);
          id = first_proof_id;
          while ((br_word_t)(((br_word_t)((br_signed_t)empty_clause<(br_signed_t)id))==(br_word_t)0)) {
            if (trimming) {
              used_where = (br_word_t)((br_signed_t)((_br_load4(used_begin+(id<<2)))<<((br_word_t)32&(sizeof(br_word_t)*8-1)))>>((br_word_t)32&(sizeof(br_word_t)*8-1)));
            } else {
              used_where = 0u-(br_word_t)1;
            }
            if (used_where) {
              l = _br_load8(literals_begin+(id<<3));
              a = _br_load8(antecedents_begin+(id<<3));
              br_check_clause(st, id, l, a);
            } else {
              /*skip*/
            }
            id = id+1;
          }
        } else {
          /*skip*/
        }
      } else {
        /*skip*/
      }
    } else {
      /*skip*/
    }
  } else {
    /*skip*/
  }
}

void br_check_clause(br_word_t st, br_word_t id, br_word_t literals, br_word_t antecedents) {
  br_word_t strict;
  _br_store8(st+128, (_br_load8(st+128))+1);
  if ((br_word_t)((_br_load4(literals))==(br_word_t)0)) {
    _br_store8(st+136, (_br_load8(st+136))+1);
  } else {
    /*skip*/
  }
  strict = _br_load8(st+80);
  if (strict) {
    br_check_clause_strictly_by_resolution(st, id, literals, antecedents);
  } else {
    br_check_clause_non_strictly_by_propagation(st, id, literals, antecedents);
  }
}

static br_word_t br_is_original_clause(br_word_t first_proof_id, br_word_t id) {
  br_word_t res, abs_id;
  abs_id = ((br_word_t)((br_signed_t)id<(br_signed_t)(br_word_t)0)) ? (0u-id) : id;
  res = (((br_word_t)(abs_id==(br_word_t)0))|((br_word_t)(first_proof_id==(br_word_t)0)))|((br_word_t)((br_signed_t)abs_id<(br_signed_t)first_proof_id));
  return res;
}

static br_word_t br_mark_used(br_word_t st, br_word_t id, br_word_t used_where) {
  br_word_t used_begin, w, used_before, first_proof_id, is_orig, res;
  used_begin = _br_load8(st);
  w = used_begin+(id<<2);
  used_before = (br_word_t)((br_signed_t)((_br_load4(w))<<((br_word_t)32&(sizeof(br_word_t)*8-1)))>>((br_word_t)32&(sizeof(br_word_t)*8-1)));
  if ((br_word_t)(((br_word_t)((br_signed_t)used_before<(br_signed_t)used_where))==(br_word_t)0)) {
    res = (br_word_t)1;
  } else {
    _br_store4(w, used_where);
    if (used_before) {
      res = (br_word_t)1;
    } else {
      first_proof_id = (br_word_t)((br_signed_t)((_br_load8(st+72))<<((br_word_t)32&(sizeof(br_word_t)*8-1)))>>((br_word_t)32&(sizeof(br_word_t)*8-1)));
      is_orig = br_is_original_clause(first_proof_id, id);
      if (is_orig) {
        _br_store8(st+112, (_br_load8(st+112))+1);
      } else {
        _br_store8(st+120, (_br_load8(st+120))+1);
      }
      res = (br_word_t)0;
    }
  }
  return res;
}

static void br_assign_literal(br_word_t st, br_word_t lit) {
  br_word_t values_begin, idx, val, trail_end;
  idx = ((br_word_t)((br_signed_t)lit<(br_signed_t)(br_word_t)0)) ? (0u-lit) : lit;
  val = ((br_word_t)((br_signed_t)lit>>((br_word_t)63&(sizeof(br_word_t)*8-1))))|1;
  values_begin = _br_load8(st+24);
  _br_store1(values_begin+idx, val);
  trail_end = _br_load8(st+48);
  _br_store4(trail_end, lit);
  _br_store8(st+48, trail_end+4);
  _br_store8(st+152, (_br_load8(st+152))+1);
}

static void br_unassign_literal(br_word_t st, br_word_t lit) {
  br_word_t values_begin, idx;
  idx = ((br_word_t)((br_signed_t)lit<(br_signed_t)(br_word_t)0)) ? (0u-lit) : lit;
  values_begin = _br_load8(st+24);
  _br_store1(values_begin+idx, (br_word_t)0);
}

static void br_backtrack(br_word_t st) {
  br_word_t trail_end, lit, values_begin, idx, t, trail_begin;
  values_begin = _br_load8(st+24);
  trail_begin = _br_load8(st+40);
  trail_end = _br_load8(st+48);
  t = trail_begin;
  while ((br_word_t)(((br_word_t)(t==trail_end))==(br_word_t)0)) {
    lit = (br_word_t)((br_signed_t)((_br_load4(t))<<((br_word_t)32&(sizeof(br_word_t)*8-1)))>>((br_word_t)32&(sizeof(br_word_t)*8-1)));
    idx = ((br_word_t)((br_signed_t)lit<(br_signed_t)(br_word_t)0)) ? (0u-lit) : lit;
    _br_store1(values_begin+idx, (br_word_t)0);
    t = t+4;
  }
  _br_store8(st+48, trail_begin);
}

static br_word_t br_assigned_literal(br_word_t st, br_word_t lit) {
  br_word_t values_begin, idx, res;
  idx = ((br_word_t)((br_signed_t)lit<(br_signed_t)(br_word_t)0)) ? (0u-lit) : lit;
  values_begin = _br_load8(st+24);
  res = (br_word_t)((br_signed_t)((_br_load1(values_begin+idx))<<((br_word_t)56&(sizeof(br_word_t)*8-1)))>>((br_word_t)56&(sizeof(br_word_t)*8-1)));
  if ((br_word_t)((br_signed_t)lit<(br_signed_t)(br_word_t)0)) {
    res = 0u-res;
  } else {
    /*skip*/
  }
  return res;
}

void br_check_clause_non_strictly_by_propagation(br_word_t st, br_word_t id, br_word_t literals, br_word_t antecedents) {
  br_word_t literals_begin, als, val, idx, lit, l, unit, aid, a, checked, tlit, values_begin, tidx, t, trail_begin, trail_end, stat_resolved, stat_lit_assigned;
  literals_begin = _br_load8(st+16);
  values_begin = _br_load8(st+24);
  trail_begin = _br_load8(st+40);
  trail_end = _br_load8(st+48);
  stat_resolved = (_br_load8(st+144))+1;
  stat_lit_assigned = _br_load8(st+152);
  checked = (br_word_t)0;
  l = literals;
  lit = (br_word_t)((br_signed_t)((_br_load4(l))<<((br_word_t)32&(sizeof(br_word_t)*8-1)))>>((br_word_t)32&(sizeof(br_word_t)*8-1)));
  while (lit) {
    idx = ((br_word_t)((br_signed_t)lit<(br_signed_t)(br_word_t)0)) ? (0u-lit) : lit;
    val = (br_word_t)((br_signed_t)((_br_load1(values_begin+idx))<<((br_word_t)56&(sizeof(br_word_t)*8-1)))>>((br_word_t)56&(sizeof(br_word_t)*8-1)));
    if ((br_word_t)((br_signed_t)lit<(br_signed_t)(br_word_t)0)) {
      val = 0u-val;
    } else {
      /*skip*/
    }
    if ((br_word_t)((br_signed_t)val<(br_signed_t)(br_word_t)0)) {
      l = l+4;
      lit = (br_word_t)((br_signed_t)((_br_load4(l))<<((br_word_t)32&(sizeof(br_word_t)*8-1)))>>((br_word_t)32&(sizeof(br_word_t)*8-1)));
    } else {
      if ((br_word_t)((br_signed_t)(br_word_t)0<(br_signed_t)val)) {
        checked = (br_word_t)1;
        lit = (br_word_t)0;
      } else {
        _br_store1(values_begin+idx, ((br_word_t)((br_signed_t)(0u-lit)>>((br_word_t)63&(sizeof(br_word_t)*8-1))))|1);
        _br_store4(trail_end, 0u-lit);
        trail_end = trail_end+4;
        stat_lit_assigned = stat_lit_assigned+1;
        l = l+4;
        lit = (br_word_t)((br_signed_t)((_br_load4(l))<<((br_word_t)32&(sizeof(br_word_t)*8-1)))>>((br_word_t)32&(sizeof(br_word_t)*8-1)));
      }
    }
  }
  if ((br_word_t)(checked==(br_word_t)0)) {
    a = antecedents;
    aid = (br_word_t)((br_signed_t)((_br_load4(a))<<((br_word_t)32&(sizeof(br_word_t)*8-1)))>>((br_word_t)32&(sizeof(br_word_t)*8-1)));
    while (aid) {
      if ((br_word_t)((br_signed_t)aid<(br_signed_t)(br_word_t)0)) {
        _br_store8(st+48, trail_end);
        _br_store8(st+144, stat_resolved);
        _br_store8(st+152, stat_lit_assigned);
        lrat_fail((br_word_t)1, id, aid, (br_word_t)0, (br_word_t)0);
      } else {
        /*skip*/
      }
      als = _br_load8(literals_begin+(aid<<3));
      stat_resolved = stat_resolved+1;
      unit = (br_word_t)0;
      l = als;
      lit = (br_word_t)((br_signed_t)((_br_load4(l))<<((br_word_t)32&(sizeof(br_word_t)*8-1)))>>((br_word_t)32&(sizeof(br_word_t)*8-1)));
      while (lit) {
        idx = ((br_word_t)((br_signed_t)lit<(br_signed_t)(br_word_t)0)) ? (0u-lit) : lit;
        val = (br_word_t)((br_signed_t)((_br_load1(values_begin+idx))<<((br_word_t)56&(sizeof(br_word_t)*8-1)))>>((br_word_t)56&(sizeof(br_word_t)*8-1)));
        if ((br_word_t)((br_signed_t)lit<(br_signed_t)(br_word_t)0)) {
          val = 0u-val;
        } else {
          /*skip*/
        }
        if ((br_word_t)((br_signed_t)val<(br_signed_t)(br_word_t)0)) {
          if ((br_word_t)(unit==(0u-lit))) {
            _br_store8(st+48, trail_end);
            _br_store8(st+144, stat_resolved);
            _br_store8(st+152, stat_lit_assigned);
            lrat_fail((br_word_t)2, id, aid, (br_word_t)0, (br_word_t)0);
          } else {
            /*skip*/
          }
        } else {
          if (unit) {
            if ((br_word_t)(((br_word_t)(unit==lit))==(br_word_t)0)) {
              _br_store8(st+48, trail_end);
              _br_store8(st+144, stat_resolved);
              _br_store8(st+152, stat_lit_assigned);
              lrat_fail((br_word_t)2, id, aid, (br_word_t)0, (br_word_t)0);
            } else {
              /*skip*/
            }
          } else {
            /*skip*/
          }
          unit = lit;
          if ((br_word_t)(val==(br_word_t)0)) {
            _br_store1(values_begin+idx, ((br_word_t)((br_signed_t)lit>>((br_word_t)63&(sizeof(br_word_t)*8-1))))|1);
            _br_store4(trail_end, lit);
            trail_end = trail_end+4;
            stat_lit_assigned = stat_lit_assigned+1;
          } else {
            /*skip*/
          }
        }
        l = l+4;
        lit = (br_word_t)((br_signed_t)((_br_load4(l))<<((br_word_t)32&(sizeof(br_word_t)*8-1)))>>((br_word_t)32&(sizeof(br_word_t)*8-1)));
      }
      if ((br_word_t)(unit==(br_word_t)0)) {
        checked = (br_word_t)1;
        aid = (br_word_t)0;
      } else {
        a = a+4;
        aid = (br_word_t)((br_signed_t)((_br_load4(a))<<((br_word_t)32&(sizeof(br_word_t)*8-1)))>>((br_word_t)32&(sizeof(br_word_t)*8-1)));
      }
    }
  } else {
    /*skip*/
  }
  if ((br_word_t)(checked==(br_word_t)0)) {
    _br_store8(st+48, trail_end);
    _br_store8(st+144, stat_resolved);
    _br_store8(st+152, stat_lit_assigned);
    lrat_fail((br_word_t)3, id, (br_word_t)0, (br_word_t)0, (br_word_t)0);
  } else {
    /*skip*/
  }
  t = trail_begin;
  while ((br_word_t)(((br_word_t)(t==trail_end))==(br_word_t)0)) {
    tlit = (br_word_t)((br_signed_t)((_br_load4(t))<<((br_word_t)32&(sizeof(br_word_t)*8-1)))>>((br_word_t)32&(sizeof(br_word_t)*8-1)));
    tidx = ((br_word_t)((br_signed_t)tlit<(br_signed_t)(br_word_t)0)) ? (0u-tlit) : tlit;
    _br_store1(values_begin+tidx, (br_word_t)0);
    t = t+4;
  }
  trail_end = trail_begin;
  _br_store8(st+48, trail_end);
  _br_store8(st+144, stat_resolved);
  _br_store8(st+152, stat_lit_assigned);
}

static void br_check_clause_strictly_by_resolution(br_word_t st, br_word_t id, br_word_t literals, br_word_t antecedents) {
  br_word_t a, literals_begin, als, aid, unit, stat_resolved, first, marks_begin, idx, mark, m, lit, l, resolvent_size;
  a = antecedents;
  aid = (br_word_t)((br_signed_t)((_br_load4(a))<<((br_word_t)32&(sizeof(br_word_t)*8-1)))>>((br_word_t)32&(sizeof(br_word_t)*8-1)));
  while (aid) {
    if ((br_word_t)((br_signed_t)aid<(br_signed_t)(br_word_t)0)) {
      lrat_fail((br_word_t)1, id, aid, (br_word_t)0, (br_word_t)0);
    } else {
      /*skip*/
    }
    a = a+4;
    aid = (br_word_t)((br_signed_t)((_br_load4(a))<<((br_word_t)32&(sizeof(br_word_t)*8-1)))>>((br_word_t)32&(sizeof(br_word_t)*8-1)));
  }
  literals_begin = _br_load8(st+16);
  marks_begin = _br_load8(st+32);
  stat_resolved = _br_load8(st+144);
  resolvent_size = (br_word_t)0;
  first = (br_word_t)1;
  while ((br_word_t)(((br_word_t)(a==antecedents))==(br_word_t)0)) {
    a = a-4;
    aid = (br_word_t)((br_signed_t)((_br_load4(a))<<((br_word_t)32&(sizeof(br_word_t)*8-1)))>>((br_word_t)32&(sizeof(br_word_t)*8-1)));
    als = _br_load8(literals_begin+(aid<<3));
    stat_resolved = stat_resolved+1;
    unit = (br_word_t)0;
    l = als;
    lit = (br_word_t)((br_signed_t)((_br_load4(l))<<((br_word_t)32&(sizeof(br_word_t)*8-1)))>>((br_word_t)32&(sizeof(br_word_t)*8-1)));
    while (lit) {
      idx = ((br_word_t)((br_signed_t)lit<(br_signed_t)(br_word_t)0)) ? (0u-lit) : lit;
      m = marks_begin+idx;
      mark = (br_word_t)((br_signed_t)((_br_load1(m))<<((br_word_t)56&(sizeof(br_word_t)*8-1)))>>((br_word_t)56&(sizeof(br_word_t)*8-1)));
      if ((br_word_t)(mark==(br_word_t)0)) {
        _br_store1(m, ((br_word_t)((br_signed_t)lit>>((br_word_t)63&(sizeof(br_word_t)*8-1))))|1);
        resolvent_size = resolvent_size+1;
      } else {
        if ((br_word_t)((br_signed_t)lit<(br_signed_t)(br_word_t)0)) {
          mark = 0u-mark;
        } else {
          /*skip*/
        }
        if ((br_word_t)(((br_word_t)((br_signed_t)(br_word_t)0<(br_signed_t)mark))==(br_word_t)0)) {
          if (unit) {
            _br_store8(st+144, stat_resolved);
            lrat_fail((br_word_t)4, id, unit, lit, aid);
          } else {
            /*skip*/
          }
          unit = lit;
        } else {
          /*skip*/
        }
      }
      l = l+4;
      lit = (br_word_t)((br_signed_t)((_br_load4(l))<<((br_word_t)32&(sizeof(br_word_t)*8-1)))>>((br_word_t)32&(sizeof(br_word_t)*8-1)));
    }
    if (first) {
      if (unit) {
        _br_store8(st+144, stat_resolved);
        lrat_fail((br_word_t)4, id, 0u-unit, unit, aid);
      } else {
        /*skip*/
      }
      first = (br_word_t)0;
    } else {
      if ((br_word_t)(unit==(br_word_t)0)) {
        _br_store8(st+144, stat_resolved);
        lrat_fail((br_word_t)5, id, aid, (br_word_t)0, (br_word_t)0);
      } else {
        resolvent_size = resolvent_size-1;
        idx = ((br_word_t)((br_signed_t)unit<(br_signed_t)(br_word_t)0)) ? (0u-unit) : unit;
        m = marks_begin+idx;
        _br_store1(m, (br_word_t)0);
      }
    }
  }
  _br_store8(st+144, stat_resolved);
  if (first) {
    lrat_fail((br_word_t)3, id, (br_word_t)0, (br_word_t)0, (br_word_t)0);
  } else {
    /*skip*/
  }
  l = literals;
  lit = (br_word_t)((br_signed_t)((_br_load4(l))<<((br_word_t)32&(sizeof(br_word_t)*8-1)))>>((br_word_t)32&(sizeof(br_word_t)*8-1)));
  while (lit) {
    idx = ((br_word_t)((br_signed_t)lit<(br_signed_t)(br_word_t)0)) ? (0u-lit) : lit;
    m = marks_begin+idx;
    mark = (br_word_t)((br_signed_t)((_br_load1(m))<<((br_word_t)56&(sizeof(br_word_t)*8-1)))>>((br_word_t)56&(sizeof(br_word_t)*8-1)));
    if ((br_word_t)(mark==(br_word_t)0)) {
      lrat_fail((br_word_t)6, id, lit, (br_word_t)0, (br_word_t)0);
    } else {
      /*skip*/
    }
    if ((br_word_t)((br_signed_t)lit<(br_signed_t)(br_word_t)0)) {
      mark = 0u-mark;
    } else {
      /*skip*/
    }
    if ((br_word_t)((br_signed_t)mark<(br_signed_t)(br_word_t)0)) {
      lrat_fail((br_word_t)7, id, lit, (br_word_t)0, (br_word_t)0);
    } else {
      /*skip*/
    }
    _br_store1(m, (br_word_t)0);
    resolvent_size = resolvent_size-1;
    l = l+4;
    lit = (br_word_t)((br_signed_t)((_br_load4(l))<<((br_word_t)32&(sizeof(br_word_t)*8-1)))>>((br_word_t)32&(sizeof(br_word_t)*8-1)));
  }
  if (resolvent_size) {
    lrat_fail((br_word_t)8, id, resolvent_size, (br_word_t)0, (br_word_t)0);
  } else {
    /*skip*/
  }
}
