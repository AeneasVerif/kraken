#pragma once

#include "c0_layout.hpp"
#include "c0_proplit.hpp"
#include "c0_leanrc.hpp"
#include "c0_v4.hpp"
#include "c0_extra.hpp"

#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <limits>
#include <tuple>
#include <vector>

/* Global freed-pointer logs for lean_dec_ref_cold */
static std::vector<uint64_t> g_c_freed;
static std::vector<uint64_t> g_cpp_freed;

extern "C" {

/* V1 native C99 symbols */
uint32_t pack_watch_bin(uint32_t lit, bool bin);
void set_clause_bits(void *c, uint32_t glue, bool garbage, uint32_t used);
uint32_t read_clause_header_word(void *c);
uint64_t read_lean_header_word(void *o);

/* V2 native C99 symbol */
void *search_propagate_literal(void *solver, uint32_t lit);

/* V3 native C99 symbols + extern hook */
void c0_free_obj(void *o) {
  g_c_freed.push_back(reinterpret_cast<uint64_t>(o));
}
bool lean_is_scalar(void *o);
void *lean_box(uint64_t n);
uint64_t lean_unbox(void *o);
void lean_inc(void *o);
void lean_dec_ref_cold(void *o);
void lean_dec(void *o);
uint32_t analyze_goto_demo(uint32_t *buf, uint32_t n, uint32_t limit);
struct c0_u32_pair { uint32_t _0; uint32_t _1; };
c0_u32_pair divmod_u32(uint32_t a, uint32_t b);
uint32_t sum_divmod_u32(uint32_t a, uint32_t b);
int32_t find_guarded(int32_t *arr, uint64_t n, int32_t target);

/* V4 & Extra native C99 symbols */
uint64_t sum_pos64(int64_t *arr, uint64_t n);
uint32_t test_intrinsics(uint32_t x32, uint64_t x64, double d);
struct c0_u32_t3 { uint32_t _0; uint32_t _1; uint32_t _2; };
c0_u32_t3 test_switch_loops(uint32_t mode, uint32_t n);

} // extern "C"

void c0_free_obj(::tqbe::Mem &mem, ::tqbe::bits<64> o) {
  (void)mem;
  g_cpp_freed.push_back(o.data);
}

#define D2_CHECK(cond, msg)                                                   \
  do {                                                                        \
    if (!(cond)) {                                                            \
      std::fprintf(stderr, "D2 FAIL (%s:%d): %s\n", __FILE__, __LINE__, msg); \
      std::abort();                                                           \
    }                                                                         \
  } while (0)

#define D2_EQ(a, b, msg)                                                      \
  do {                                                                        \
    auto _va = (a);                                                           \
    auto _vb = (b);                                                           \
    if (!(_va == _vb)) {                                                      \
      std::fprintf(stderr, "D2 MISMATCH (%s:%d): %s\n", __FILE__, __LINE__,   \
                   msg);                                                      \
      std::abort();                                                           \
    }                                                                         \
  } while (0)

namespace d2 {

inline void read_mem_bytes(const ::tqbe::Mem &mem, uint64_t addr, uint8_t *dst,
                           size_t len) {
  for (size_t i = 0; i < len; ++i) {
    dst[i] = mem.read_byte(addr + i);
  }
}

template <typename T>
inline void read_mem_vec(const ::tqbe::Mem &mem, const std::vector<T> &orig,
                         std::vector<T> &out) {
  out.resize(orig.size());
  if (!orig.empty()) {
    read_mem_bytes(mem, reinterpret_cast<uint64_t>(orig.data()),
                   reinterpret_cast<uint8_t *>(out.data()),
                   orig.size() * sizeof(T));
  }
}

template <typename T>
inline void map_vec(::tqbe::Mem &mem, const std::vector<T> &v) {
  if (!v.empty()) {
    mem.map_bytes(reinterpret_cast<uint64_t>(v.data()),
                  reinterpret_cast<const uint8_t *>(v.data()),
                  v.size() * sizeof(T));
  }
}

/* ============================================================================
 * V1: Layout functions differential check
 * ============================================================================ */

inline void run_v1_tests() {
  ::tqbe::Mem mem;
  for (uint32_t lit : {0u, 1u, 42u, 0x123456u, 0x7FFFFFFFu}) {
    for (bool b : {false, true}) {
      uint32_t c_res = pack_watch_bin(lit, b);
      uint32_t cpp_res = static_cast<uint32_t>(
          c0_layout::pack_watch_bin(mem, ::tqbe::bits<32>(lit), b).data);
      D2_EQ(c_res, cpp_res, "pack_watch_bin");
    }
  }

  struct ClauseBuf { uint32_t w0, searched, size, lits[2]; };
  ClauseBuf c_buf{};
  uint64_t c_addr = reinterpret_cast<uint64_t>(&c_buf);
  mem.map_bytes(c_addr, reinterpret_cast<const uint8_t *>(&c_buf), sizeof(c_buf));

  c0_layout::set_clause_bits(mem, ::tqbe::bits<64>(c_addr),
                             ::tqbe::bits<32>(0x54321u), true,
                             ::tqbe::bits<32>(19u));
  set_clause_bits(&c_buf, 0x54321u, true, 19u);

  uint32_t cpp_w0 = static_cast<uint32_t>(
      c0_layout::read_clause_header_word(mem, ::tqbe::bits<64>(c_addr)).data);
  uint32_t c_w0 = read_clause_header_word(&c_buf);
  D2_EQ(c_w0, cpp_w0, "set_clause_bits/read_clause_header_word");
  ClauseBuf cpp_buf{};
  read_mem_bytes(mem, c_addr, reinterpret_cast<uint8_t *>(&cpp_buf), sizeof(cpp_buf));
  D2_CHECK(std::memcmp(&c_buf, &cpp_buf, sizeof(c_buf)) == 0, "clause bytes");

  struct LeanObjBuf { int32_t m_rc; uint16_t m_cs_sz; uint8_t m_other; uint8_t m_tag; };
  LeanObjBuf lo{0x11223344, 0x5566u, 0x77u, 0x88u};
  uint64_t lo_addr = reinterpret_cast<uint64_t>(&lo);
  mem.map_bytes(lo_addr, reinterpret_cast<const uint8_t *>(&lo), sizeof(lo));
  uint64_t c_hdr = read_lean_header_word(&lo);
  uint64_t cpp_hdr =
      c0_layout::read_lean_header_word(mem, ::tqbe::bits<64>(lo_addr)).data;
  D2_EQ(c_hdr, cpp_hdr, "read_lean_header_word");

  std::printf("V1 differential layout check passed.\n");
}

/* ============================================================================
 * V2: Kissat search_propagate_literal D2 differential suite (>= 25 cases)
 * ============================================================================ */

struct C0WardStack { uint64_t *begin; uint64_t *end; uint64_t *allocated; };
struct C0U32Stack { uint32_t *begin; uint32_t *end; uint32_t *allocated; };
struct C0Vector { uint32_t offset; uint32_t size; };
struct C0Assigned {
  uint32_t level;
  uint32_t flags;
  uint32_t trail;
  uint32_t reason;
};
struct C0Kissat {
  C0Vector *watches;
  C0U32Stack vectors_stack;
  C0WardStack arena;
  C0Assigned *assigned;
  int8_t *values;
  C0U32Stack delayed;
  C0U32Stack trail;
  void *conflict;
  uint64_t ticks;
  uint32_t level;
  uint32_t unassigned;
};

static_assert(sizeof(C0Vector) == 8);
static_assert(sizeof(C0Assigned) == 16);
static_assert(sizeof(C0Kissat) == 144);

inline uint32_t make_watch_bin(uint32_t lit) {
  return (lit & 0x7FFFFFFFu) | 0x80000000u;
}
inline uint32_t make_watch_large(uint32_t blocking) {
  return blocking & 0x7FFFFFFFu;
}
inline uint32_t make_clause_hdr(uint32_t glue, bool garbage, bool redundant,
                                uint32_t used) {
  uint32_t w = glue & ((1u << 19) - 1u);
  if (garbage) w |= (1u << 19);
  if (redundant) w |= (1u << 22);
  w |= ((used & 31u) << 27);
  return w;
}

struct ProplitFixture {
  static constexpr uint32_t NVARS = 16;
  static constexpr uint32_t NLITS = NVARS * 2;

  std::vector<C0Vector> watches;
  std::vector<uint32_t> stack_buf;
  std::vector<uint64_t> arena_buf;
  std::vector<C0Assigned> assigned;
  std::vector<int8_t> values;
  std::vector<uint32_t> delayed_buf;
  std::vector<uint32_t> trail_buf;
  std::vector<uint32_t> conflict_buf; // 6 u32s = 24 bytes (clause hdr + 2 lits + slack)
  C0Kissat solver{};

  uint32_t stack_used = 0;
  uint32_t arena_used = 0;
  uint32_t trail_used = 0;

  explicit ProplitFixture()
      : watches(NLITS, C0Vector{0, 0}),
        stack_buf(256, 0),
        arena_buf(256, 0),
        assigned(NVARS, C0Assigned{0, 0, 0, 0}),
        values(NLITS, 0),
        delayed_buf(128, 0),
        trail_buf(64, 0),
        conflict_buf(8, 0) {
    rebind();
  }

  void rebind() {
    solver.watches = watches.data();
    solver.vectors_stack.begin = stack_buf.data();
    solver.vectors_stack.end = stack_buf.data() + stack_used;
    solver.vectors_stack.allocated = stack_buf.data() + stack_buf.size();
    solver.arena.begin = arena_buf.data();
    solver.arena.end = arena_buf.data() + arena_used;
    solver.arena.allocated = arena_buf.data() + arena_buf.size();
    solver.assigned = assigned.data();
    solver.values = values.data();
    solver.delayed.begin = delayed_buf.data();
    solver.delayed.end = delayed_buf.data();
    solver.delayed.allocated = delayed_buf.data() + delayed_buf.size();
    solver.trail.begin = trail_buf.data();
    solver.trail.end = trail_buf.data() + trail_used;
    solver.trail.allocated = trail_buf.data() + trail_buf.size();
    solver.conflict = conflict_buf.data();
    solver.ticks = 100ULL;
    solver.level = 3u;
    solver.unassigned = NVARS;
  }

  void set_true(uint32_t lit, uint32_t lvl = 2u) {
    values[lit] = 1;
    values[lit ^ 1u] = -1;
    assigned[lit >> 1].level = lvl;
    if (solver.unassigned > 0) solver.unassigned--;
  }

  void set_false(uint32_t lit, uint32_t lvl = 2u) {
    set_true(lit ^ 1u, lvl);
  }

  uint32_t alloc_clause(const std::vector<uint32_t> &lits, uint32_t searched = 2,
                        bool garbage = false, bool redundant = false,
                        uint32_t used = 0, uint32_t glue = 7) {
    uint32_t ref = arena_used;
    uint32_t u32s = 3u + static_cast<uint32_t>(lits.size());
    uint32_t u64s = (u32s + 1u) / 2u;
    uint32_t *dst = reinterpret_cast<uint32_t *>(arena_buf.data() + ref);
    dst[0] = make_clause_hdr(glue, garbage, redundant, used);
    dst[1] = searched;
    dst[2] = static_cast<uint32_t>(lits.size());
    for (size_t i = 0; i < lits.size(); ++i) dst[3 + i] = lits[i];
    arena_used += u64s;
    rebind();
    return ref;
  }

  void set_watches(uint32_t lit, const std::vector<uint32_t> &words) {
    watches[lit].offset = stack_used;
    watches[lit].size = static_cast<uint32_t>(words.size());
    for (uint32_t w : words) stack_buf[stack_used++] = w;
    rebind();
  }

  void run_and_compare(const char *name, uint32_t lit) {
    rebind();
    ::tqbe::Mem mem;
    mem.map_bytes(reinterpret_cast<uint64_t>(&solver),
                  reinterpret_cast<const uint8_t *>(&solver), sizeof(solver));
    map_vec(mem, watches);
    map_vec(mem, stack_buf);
    map_vec(mem, arena_buf);
    map_vec(mem, assigned);
    map_vec(mem, values);
    map_vec(mem, delayed_buf);
    map_vec(mem, trail_buf);
    map_vec(mem, conflict_buf);

    uint64_t cpp_res = c0_proplit::search_propagate_literal(
        mem, ::tqbe::bits<64>(reinterpret_cast<uint64_t>(&solver)),
        ::tqbe::bits<32>(lit)).data;

    C0Kissat cpp_solver{};
    read_mem_bytes(mem, reinterpret_cast<uint64_t>(&solver),
                   reinterpret_cast<uint8_t *>(&cpp_solver), sizeof(cpp_solver));
    std::vector<C0Vector> cpp_watches;
    std::vector<uint32_t> cpp_stack;
    std::vector<uint64_t> cpp_arena;
    std::vector<C0Assigned> cpp_assigned;
    std::vector<int8_t> cpp_values;
    std::vector<uint32_t> cpp_delayed;
    std::vector<uint32_t> cpp_trail;
    std::vector<uint32_t> cpp_conflict;
    read_mem_vec(mem, watches, cpp_watches);
    read_mem_vec(mem, stack_buf, cpp_stack);
    read_mem_vec(mem, arena_buf, cpp_arena);
    read_mem_vec(mem, assigned, cpp_assigned);
    read_mem_vec(mem, values, cpp_values);
    read_mem_vec(mem, delayed_buf, cpp_delayed);
    read_mem_vec(mem, trail_buf, cpp_trail);
    read_mem_vec(mem, conflict_buf, cpp_conflict);

    void *c_res_ptr = search_propagate_literal(&solver, lit);
    uint64_t c_res = reinterpret_cast<uint64_t>(c_res_ptr);

    D2_EQ(c_res, cpp_res, name);
    D2_CHECK(std::memcmp(&solver, &cpp_solver, sizeof(solver)) == 0, name);
    D2_CHECK(watches.size() == cpp_watches.size() &&
                 std::memcmp(watches.data(), cpp_watches.data(),
                             watches.size() * sizeof(C0Vector)) == 0,
             name);
    D2_CHECK(stack_buf == cpp_stack, name);
    D2_CHECK(arena_buf == cpp_arena, name);
    D2_CHECK(assigned.size() == cpp_assigned.size() &&
                 std::memcmp(assigned.data(), cpp_assigned.data(),
                             assigned.size() * sizeof(C0Assigned)) == 0,
             name);
    D2_CHECK(values == cpp_values, name);
    D2_CHECK(delayed_buf == cpp_delayed, name);
    D2_CHECK(trail_buf == cpp_trail, name);
    D2_CHECK(conflict_buf == cpp_conflict, name);
  }
};

inline void run_v2_tests() {
  int cases = 0;

  // 1. Empty watch list
  {
    ProplitFixture f;
    f.set_true(2);
    f.run_and_compare("v2_01_empty", 2);
    cases++;
  }
  // 2. Binary watch, blocking lit already true -> no assign
  {
    ProplitFixture f;
    f.set_true(2);
    f.set_true(4);
    f.set_watches(3, {make_watch_bin(4)});
    f.run_and_compare("v2_02_bin_blocking_true", 2);
    cases++;
  }
  // 3. Binary watch, blocking lit false -> binary_conflict
  {
    ProplitFixture f;
    f.set_true(2);
    f.set_false(4);
    f.set_watches(3, {make_watch_bin(4)});
    f.run_and_compare("v2_03_bin_conflict", 2);
    cases++;
  }
  // 4. Binary watch, blocking lit unassigned -> fast_binary_assign
  {
    ProplitFixture f;
    f.set_true(2);
    f.set_watches(3, {make_watch_bin(4)});
    f.run_and_compare("v2_04_bin_assign", 2);
    cases++;
  }
  // 5. Multiple binary watches: blocking true, assign, second assign
  {
    ProplitFixture f;
    f.set_true(2);
    f.set_true(4);
    f.set_watches(3, {make_watch_bin(4), make_watch_bin(6), make_watch_bin(8)});
    f.run_and_compare("v2_05_multi_bin_assign", 2);
    cases++;
  }
  // 6. Binary assign then conflict, leaving third watch copied by tail loop
  {
    ProplitFixture f;
    f.set_true(2);
    f.set_false(6);
    f.set_watches(3, {make_watch_bin(4), make_watch_bin(6), make_watch_bin(8)});
    f.run_and_compare("v2_06_bin_assign_then_conflict_tail_copy", 2);
    cases++;
  }
  // 7. Large clause garbage=1 -> removed (q -= 2)
  {
    ProplitFixture f;
    f.set_true(2);
    uint32_t r = f.alloc_clause({3, 4, 6}, 2, true);
    f.set_watches(3, {make_watch_large(4), r});
    f.run_and_compare("v2_07_large_garbage_only", 2);
    cases++;
  }
  // 8. Garbage large clause followed by binary assign -> watch list compacted
  {
    ProplitFixture f;
    f.set_true(2);
    uint32_t r = f.alloc_clause({3, 4, 6}, 2, true);
    f.set_watches(3, {make_watch_large(4), r, make_watch_bin(8)});
    f.run_and_compare("v2_08_garbage_then_bin_compact", 2);
    cases++;
  }
  // 9. Large clause: blocking unassigned, other true -> q[-2].b.lit = other!
  {
    ProplitFixture f;
    f.set_true(2);
    f.set_true(6);
    uint32_t r = f.alloc_clause({3, 6, 8});
    f.set_watches(3, {make_watch_large(4), r});
    f.run_and_compare("v2_09_other_true_update_blocking", 2);
    cases++;
  }
  // 10. Large clause: blocking false, other true -> q[-2].b.lit = other!
  {
    ProplitFixture f;
    f.set_true(2);
    f.set_false(4);
    f.set_true(6);
    uint32_t r = f.alloc_clause({6, 3, 8});
    f.set_watches(3, {make_watch_large(4), r});
    f.run_and_compare("v2_10_blocking_false_other_true", 2);
    cases++;
  }
  // 11. Large replacement in [searched .. size) at searched
  {
    ProplitFixture f;
    f.set_true(2);
    f.set_false(4);
    f.set_false(6);
    uint32_t r = f.alloc_clause({3, 6, 8, 10}, 2);
    f.set_watches(3, {make_watch_large(4), r});
    f.run_and_compare("v2_11_repl_at_searched", 2);
    cases++;
  }
  // 12. Large replacement in [searched .. size) at last literal (size-1)
  {
    ProplitFixture f;
    f.set_true(2);
    f.set_false(4);
    f.set_false(6);
    f.set_false(8);
    f.set_false(10);
    f.set_true(12);
    uint32_t r = f.alloc_clause({6, 3, 8, 10, 12}, 2);
    f.set_watches(3, {make_watch_large(4), r});
    f.run_and_compare("v2_12_repl_at_end_other_at_lits0", 2);
    cases++;
  }
  // 13. Circular wrap replacement in [2 .. searched) at lits[2]
  {
    ProplitFixture f;
    f.set_true(2);
    f.set_false(4);
    f.set_false(6);
    f.set_false(10);
    f.set_false(12);
    uint32_t r = f.alloc_clause({3, 6, 8, 10, 12}, 3);
    f.set_watches(3, {make_watch_large(4), r});
    f.run_and_compare("v2_13_repl_wrap_at_2", 2);
    cases++;
  }
  // 14. Circular wrap replacement in [2 .. searched) right before searched
  {
    ProplitFixture f;
    f.set_true(2);
    f.set_false(4);
    f.set_false(6);
    f.set_false(8);
    f.set_false(12);
    f.set_false(14);
    uint32_t r = f.alloc_clause({3, 6, 8, 10, 12, 14}, 4);
    f.set_watches(3, {make_watch_large(4), r});
    f.run_and_compare("v2_14_repl_wrap_before_searched", 2);
    cases++;
  }
  // 15. Circular scan searched == size (immediately wraps to [2..size))
  {
    ProplitFixture f;
    f.set_true(2);
    f.set_false(4);
    f.set_false(6);
    f.set_false(8);
    uint32_t r = f.alloc_clause({3, 6, 8, 10}, 4);
    f.set_watches(3, {make_watch_large(4), r});
    f.run_and_compare("v2_15_repl_searched_at_size", 2);
    cases++;
  }
  // 16. Large unit assignment (non-redundant)
  {
    ProplitFixture f;
    f.set_true(2);
    f.set_false(4);
    f.set_false(8);
    f.set_false(10);
    uint32_t r = f.alloc_clause({3, 6, 8, 10}, 2, false, false, 0);
    f.set_watches(3, {make_watch_large(4), r});
    f.run_and_compare("v2_16_large_assign_irred", 2);
    cases++;
  }
  // 17. Large unit assignment (redundant, used increments 5 -> 6)
  {
    ProplitFixture f;
    f.set_true(2);
    f.set_false(4);
    f.set_false(8);
    f.set_false(10);
    uint32_t r = f.alloc_clause({3, 6, 8, 10}, 2, false, true, 5, 0x55555u);
    f.set_watches(3, {make_watch_large(4), r});
    f.run_and_compare("v2_17_large_assign_red_used_inc", 2);
    cases++;
  }
  // 18. Large unit assignment (redundant, used saturates at 31)
  {
    ProplitFixture f;
    f.set_true(2);
    f.set_false(4);
    f.set_false(8);
    f.set_false(10);
    uint32_t r = f.alloc_clause({6, 3, 8, 10}, 2, false, true, 31, 0x7FFFFu);
    f.set_watches(3, {make_watch_large(4), r});
    f.run_and_compare("v2_18_large_assign_red_used_sat", 2);
    cases++;
  }
  // 19. Large conflict (all literals false)
  {
    ProplitFixture f;
    f.set_true(2);
    f.set_false(4);
    f.set_false(6);
    f.set_false(8);
    f.set_false(10);
    uint32_t r = f.alloc_clause({3, 6, 8, 10}, 3);
    f.set_watches(3, {make_watch_large(4), r});
    f.run_and_compare("v2_19_large_conflict", 2);
    cases++;
  }
  // 20. watch_large_delayed relocation (repl's vector NOT at stack end)
  {
    ProplitFixture f;
    f.set_true(2);
    f.set_false(4);
    f.set_false(6);
    f.set_watches(8, {make_watch_bin(12)}); // sits BEFORE ws[3] on stack!
    uint32_t r = f.alloc_clause({3, 6, 8, 10}, 2);
    f.set_watches(3, {make_watch_large(4), r});
    f.run_and_compare("v2_20_delayed_relocate", 2);
    cases++;
  }
  // 21. Two delayed watches on same target lit: first relocates, second extends in-place
  {
    ProplitFixture f;
    f.set_true(2);
    f.set_false(4);
    f.set_false(6);
    f.set_false(10);
    f.set_watches(8, {make_watch_bin(12)});
    uint32_t r1 = f.alloc_clause({3, 6, 8, 10}, 2);
    uint32_t r2 = f.alloc_clause({3, 10, 8, 6}, 2);
    f.set_watches(3, {make_watch_large(4), r1, make_watch_large(4), r2});
    f.run_and_compare("v2_21_delayed_reloc_then_inplace", 2);
    cases++;
  }
  // 22. Large blocking literal TRUE -> skips loading clause
  {
    ProplitFixture f;
    f.set_true(2);
    f.set_true(4);
    uint32_t r = f.alloc_clause({3, 6, 8, 10});
    f.set_watches(3, {make_watch_large(4), r});
    f.run_and_compare("v2_22_large_blocking_true", 2);
    cases++;
  }
  // 23. cache_lines boundary: vector_size == 16 (64 bytes -> 1 line)
  {
    ProplitFixture f;
    f.set_true(2);
    f.set_true(4);
    std::vector<uint32_t> ws(16, make_watch_bin(4));
    f.set_watches(3, ws);
    f.run_and_compare("v2_23_cache_lines_16", 2);
    cases++;
  }
  // 24. cache_lines boundary: vector_size == 17 (68 bytes -> 2 lines)
  {
    ProplitFixture f;
    f.set_true(2);
    f.set_true(4);
    std::vector<uint32_t> ws(17, make_watch_bin(4));
    f.set_watches(3, ws);
    f.run_and_compare("v2_24_cache_lines_17", 2);
    cases++;
  }
  // 25. Mixed sequence: garbage + blocking_true + other_true + bin_assign + wrap_repl + large_assign
  {
    ProplitFixture f;
    f.set_true(2);
    f.set_true(4);
    f.set_false(6);
    f.set_true(14);
    f.set_false(18);
    f.set_false(20);
    f.set_watches(22, {make_watch_bin(4)}); // forces relocation on 22
    uint32_t rg = f.alloc_clause({3, 6, 8}, 2, true);
    uint32_t r_ot = f.alloc_clause({3, 14, 16}, 2);
    uint32_t r_rep = f.alloc_clause({3, 18, 22, 20}, 3);
    uint32_t r_asg = f.alloc_clause({3, 24, 18, 20}, 2, false, true, 12);
    f.set_watches(3, {
        make_watch_large(6), rg,
        make_watch_large(4), rg,
        make_watch_large(6), r_ot,
        make_watch_bin(10),
        make_watch_large(6), r_rep,
        make_watch_large(6), r_asg,
        make_watch_bin(26)
    });
    f.run_and_compare("v2_25_mixed_assign_chain", 2);
    cases++;
  }
  // 26. Replacement + garbage + trailing conflict (verifies delayed drained before returning conflict!)
  {
    ProplitFixture f;
    f.set_true(2);
    f.set_false(4);
    f.set_false(6);
    f.set_false(8);
    f.set_false(12);
    f.set_watches(10, {make_watch_bin(4)});
    uint32_t r_rep = f.alloc_clause({3, 6, 10, 8}, 2);
    uint32_t rg = f.alloc_clause({3, 6, 8}, 2, true);
    uint32_t r_conf = f.alloc_clause({3, 8, 12, 6}, 2);
    f.set_watches(3, {
        make_watch_large(4), r_rep,
        make_watch_large(4), rg,
        make_watch_large(4), r_conf,
        make_watch_bin(14)
    });
    f.run_and_compare("v2_26_repl_then_large_conflict_tail_copy", 2);
    cases++;
  }
  // 27. Duplicate literal propagated after earlier binary assign made blocking lit true
  {
    ProplitFixture f;
    f.set_true(2);
    f.set_watches(3, {make_watch_bin(10), make_watch_bin(10)});
    f.run_and_compare("v2_27_dup_bin_watch_same_lit", 2);
    cases++;
  }
  // 28. Binary assign of X then large clause with X as `other` hits `oval > 0`.
  {
    ProplitFixture f;
    f.set_true(2);
    f.set_false(6);
    uint32_t r = f.alloc_clause({3, 10, 6}, 2);
    f.set_watches(3, {make_watch_bin(10), make_watch_large(6), r});
    f.run_and_compare("v2_28_bin_assign_helps_later_large_other_true", 2);
    cases++;
  }
  // 29. Binary assign of X^1 then large clause conflicts because X is false!
  {
    ProplitFixture f;
    f.set_true(2);
    f.set_false(6);
    uint32_t r = f.alloc_clause({3, 10, 6}, 2);
    f.set_watches(3, {make_watch_bin(11), make_watch_large(6), r});
    f.run_and_compare("v2_29_bin_assign_triggers_large_conflict", 2);
    cases++;
  }
  // 30. Large 2-literal clause (size == 2) without replacement scan match -> assigns other
  {
    ProplitFixture f;
    f.set_true(2);
    f.set_false(6);
    uint32_t r = f.alloc_clause({3, 12}, 2, false, true, 0);
    f.set_watches(3, {make_watch_large(6), r});
    f.run_and_compare("v2_30_size2_large_assign", 2);
    cases++;
  }
  // 31..40: Deterministic pseudo-random watch-list propagation trials
  uint32_t rng = 0xCAFEBABEu;
  auto next_rng = [&]() -> uint32_t {
    rng ^= rng << 13;
    rng ^= rng >> 17;
    rng ^= rng << 5;
    return rng;
  };
  for (int t = 0; t < 10; ++t) {
    ProplitFixture f;
    uint32_t prop_lit = 2u + (next_rng() % 4u) * 2u;
    f.set_true(prop_lit);
    uint32_t not_lit = prop_lit ^ 1u;
    for (uint32_t v = 0; v < ProplitFixture::NVARS; ++v) {
      if ((v * 2u) == prop_lit || (v * 2u + 1u) == prop_lit) continue;
      uint32_t r = next_rng() % 4u;
      if (r == 0) f.set_true(v * 2u);
      else if (r == 1) f.set_false(v * 2u);
    }
    // Pre-populate another watch vector so relocations happen naturally
    f.set_watches(not_lit ^ 2u, {make_watch_bin(0), make_watch_bin(2)});
    std::vector<uint32_t> wl;
    int nw = 3 + static_cast<int>(next_rng() % 5u);
    for (int i = 0; i < nw; ++i) {
      if ((next_rng() % 3u) == 0u) {
        uint32_t blk = next_rng() % ProplitFixture::NLITS;
        if ((blk >> 1) == (prop_lit >> 1)) blk ^= 2u;
        wl.push_back(make_watch_bin(blk));
      } else {
        uint32_t other = next_rng() % ProplitFixture::NLITS;
        if ((other >> 1) == (prop_lit >> 1)) other ^= 2u;
        uint32_t sz = 3u + (next_rng() % 4u);
        std::vector<uint32_t> lits;
        bool swap01 = (next_rng() & 1u) != 0u;
        lits.push_back(swap01 ? other : not_lit);
        lits.push_back(swap01 ? not_lit : other);
        for (uint32_t j = 2; j < sz; ++j) {
          uint32_t lj = next_rng() % ProplitFixture::NLITS;
          if ((lj >> 1) == (prop_lit >> 1)) lj ^= 2u;
          lits.push_back(lj);
        }
        uint32_t srch = 2u + (next_rng() % (sz - 1u));
        bool garb = (next_rng() % 6u) == 0u;
        bool red = (next_rng() % 2u) == 0u;
        uint32_t used = next_rng() % 32u;
        uint32_t cref = f.alloc_clause(lits, srch, garb, red, used);
        uint32_t blk = lits[next_rng() % 2u];
        wl.push_back(make_watch_large(blk));
        wl.push_back(cref);
      }
    }
    f.set_watches(not_lit, wl);
    f.run_and_compare("v2_rand_stress", prop_lit);
    cases++;
  }

  D2_CHECK(cases >= 25, "V2 requires >= 25 test cases");
  std::printf("V2 proplit D2 differential suite passed (%d cases).\n", cases);
}

/* ============================================================================
 * V3: Lean Tier-0 RC, forward goto, multi-return, and guarded ASan load
 * ============================================================================ */

struct C0LeanCtor {
  int32_t m_rc;
  uint16_t m_cs_sz;
  uint8_t m_other;
  uint8_t m_tag;
  uint64_t m_objs[4];
};

inline void run_v3_lean_rc_graph() {
  // Build a DAG with shared node, unique chain, scalar boxed child, null child,
  // persistent node (m_rc=0), and external tag (tag=245 > 243).
  std::vector<C0LeanCtor> nodes(24);
  std::memset(nodes.data(), 0, nodes.size() * sizeof(C0LeanCtor));

  auto ptr_u64 = [&](size_t idx) -> uint64_t {
    return reinterpret_cast<uint64_t>(&nodes[idx]);
  };

  // nodes[1]: leaf unique (rc=1, tag=0)
  nodes[1].m_rc = 1; nodes[1].m_other = 0; nodes[1].m_tag = 0;
  // nodes[2]: shared (rc=2, tag=1, 1 child -> nodes[1])
  nodes[2].m_rc = 2; nodes[2].m_other = 1; nodes[2].m_tag = 1;
  nodes[2].m_objs[0] = ptr_u64(1);
  // nodes[3]: persistent (rc=0, tag=0, 1 child -> nodes[1])
  nodes[3].m_rc = 0; nodes[3].m_other = 1; nodes[3].m_tag = 0;
  nodes[3].m_objs[0] = ptr_u64(1);
  // nodes[4]: external/non-ctor (rc=1, tag=245 > 243; m_other=3 shouldn't be traversed!)
  nodes[4].m_rc = 1; nodes[4].m_other = 3; nodes[4].m_tag = 245;
  nodes[4].m_objs[0] = ptr_u64(2);
  // Linear chain nodes[5..19] (each unique rc=1 pointing to next)
  for (size_t i = 5; i <= 19; ++i) {
    nodes[i].m_rc = 1;
    nodes[i].m_other = (i < 19) ? 1 : 0;
    nodes[i].m_tag = 2;
    if (i < 19) nodes[i].m_objs[0] = ptr_u64(i + 1);
  }
  // Root nodes[0]: (rc=1, tag=5, 4 children: scalar, shared[2], persistent[3], unique chain[5])
  nodes[0].m_rc = 1;
  nodes[0].m_other = 4;
  nodes[0].m_tag = 5;
  nodes[0].m_objs[0] = (42ULL << 1) | 1ULL; // scalar
  nodes[0].m_objs[1] = ptr_u64(2);          // shared rc=2 -> decrements to 1
  nodes[0].m_objs[2] = ptr_u64(3);          // persistent rc=0 -> untouched
  nodes[0].m_objs[3] = ptr_u64(5);          // chain root rc=1 -> queued + freed

  std::vector<C0LeanCtor> cpp_nodes = nodes;
  // Map nodes at nodes.data() address into mem
  ::tqbe::Mem mem;
  map_vec(mem, nodes);

  g_c_freed.clear();
  g_cpp_freed.clear();

  // Exercise lean_is_scalar / lean_box / lean_unbox / lean_inc differential
  void *b_c = lean_box(12345ULL);
  uint64_t b_cpp = c0_leanrc::lean_box(mem, ::tqbe::bits<64>(12345ULL)).data;
  D2_EQ(reinterpret_cast<uint64_t>(b_c), b_cpp, "lean_box");
  D2_EQ(lean_is_scalar(b_c),
        c0_leanrc::lean_is_scalar(mem, ::tqbe::bits<64>(b_cpp)),
        "lean_is_scalar(boxed)");
  D2_EQ(lean_is_scalar(&nodes[0]),
        c0_leanrc::lean_is_scalar(mem, ::tqbe::bits<64>(ptr_u64(0))),
        "lean_is_scalar(ptr)");
  D2_EQ(lean_unbox(b_c),
        c0_leanrc::lean_unbox(mem, ::tqbe::bits<64>(b_cpp)).data,
        "lean_unbox");

  // lean_inc on scalar, persistent (rc=0), and shared node[2] (rc 2 -> 3)
  c0_leanrc::lean_inc(mem, ::tqbe::bits<64>(b_cpp));
  c0_leanrc::lean_inc(mem, ::tqbe::bits<64>(ptr_u64(3)));
  c0_leanrc::lean_inc(mem, ::tqbe::bits<64>(ptr_u64(2)));
  // Dec back node[2] once (3 -> 2) via lean_dec
  c0_leanrc::lean_dec(mem, ::tqbe::bits<64>(ptr_u64(2)));
  // Dec scalar & persistent (no-ops)
  c0_leanrc::lean_dec(mem, ::tqbe::bits<64>(b_cpp));
  c0_leanrc::lean_dec(mem, ::tqbe::bits<64>(ptr_u64(3)));
  // Dec root[0] and external[4]
  c0_leanrc::lean_dec(mem, ::tqbe::bits<64>(ptr_u64(0)));
  c0_leanrc::lean_dec(mem, ::tqbe::bits<64>(ptr_u64(4)));

  read_mem_vec(mem, nodes, cpp_nodes);

  // Now run native C99
  lean_inc(b_c);
  lean_inc(&nodes[3]);
  lean_inc(&nodes[2]);
  lean_dec(&nodes[2]);
  lean_dec(b_c);
  lean_dec(&nodes[3]);
  lean_dec(&nodes[0]);
  lean_dec(&nodes[4]);

  D2_CHECK(g_c_freed == g_cpp_freed, "lean_dec_ref_cold freed sequence");
  D2_EQ(g_c_freed.size(), static_cast<size_t>(17), "freed 17 objects (0, 5..19, 4)");
  D2_CHECK(std::memcmp(nodes.data(), cpp_nodes.data(),
                       nodes.size() * sizeof(C0LeanCtor)) == 0,
           "lean_dec_ref_cold memory parity");
}

inline void run_v3_tests() {
  run_v3_lean_rc_graph();

  // Forward goto DONE tests
  {
    ::tqbe::Mem mem;
    std::vector<uint32_t> empty;
    D2_EQ(analyze_goto_demo(nullptr, 0u, 10u),
          static_cast<uint32_t>(
              c0_leanrc::analyze_goto_demo(mem, ::tqbe::bits<64>(0),
                                           ::tqbe::bits<32>(0u),
                                           ::tqbe::bits<32>(10u)).data),
          "analyze_goto_demo empty");

    std::vector<uint32_t> arr = {5u, 7u, 20u, 0xFFFFFFFFu, 9u};
    map_vec(mem, arr);
    uint64_t ap = reinterpret_cast<uint64_t>(arr.data());
    D2_EQ(analyze_goto_demo(arr.data(), 5u, 15u),
          static_cast<uint32_t>(
              c0_leanrc::analyze_goto_demo(mem, ::tqbe::bits<64>(ap),
                                           ::tqbe::bits<32>(5u),
                                           ::tqbe::bits<32>(15u)).data),
          "analyze_goto_demo early limit");

    std::vector<uint32_t> arr2 = {3u, 4u, 0xFFFFFFFFu, 100u};
    map_vec(mem, arr2);
    uint64_t ap2 = reinterpret_cast<uint64_t>(arr2.data());
    D2_EQ(analyze_goto_demo(arr2.data(), 4u, 999u),
          static_cast<uint32_t>(
              c0_leanrc::analyze_goto_demo(mem, ::tqbe::bits<64>(ap2),
                                           ::tqbe::bits<32>(4u),
                                           ::tqbe::bits<32>(999u)).data),
          "analyze_goto_demo sentinel");

    std::vector<uint32_t> arr3 = {3u, 4u, 5u};
    map_vec(mem, arr3);
    uint64_t ap3 = reinterpret_cast<uint64_t>(arr3.data());
    D2_EQ(analyze_goto_demo(arr3.data(), 3u, 100u),
          static_cast<uint32_t>(
              c0_leanrc::analyze_goto_demo(mem, ::tqbe::bits<64>(ap3),
                                           ::tqbe::bits<32>(3u),
                                           ::tqbe::bits<32>(100u)).data),
          "analyze_goto_demo fallthrough");
  }

  // Multi-return divmod_u32 / sum_divmod_u32 + c0_abort check
  {
    ::tqbe::Mem mem;
    for (uint32_t a : {0u, 7u, 100u, 0xFFFFFFFFu}) {
      for (uint32_t b : {1u, 3u, 17u, 1000u}) {
        c0_u32_pair c_dm = divmod_u32(a, b);
        auto cpp_dm = c0_leanrc::divmod_u32(mem, ::tqbe::bits<32>(a),
                                            ::tqbe::bits<32>(b));
        D2_EQ(c_dm._0, static_cast<uint32_t>(std::get<0>(cpp_dm).data), "divmod q");
        D2_EQ(c_dm._1, static_cast<uint32_t>(std::get<1>(cpp_dm).data), "divmod r");

        uint32_t c_sdm = sum_divmod_u32(a, b);
        uint32_t cpp_sdm = static_cast<uint32_t>(
            c0_leanrc::sum_divmod_u32(mem, ::tqbe::bits<32>(a),
                                      ::tqbe::bits<32>(b)).data);
        D2_EQ(c_sdm, cpp_sdm, "sum_divmod_u32");
      }
    }
    bool caught_abort = false;
    try {
      (void)c0_leanrc::divmod_u32(mem, ::tqbe::bits<32>(10u), ::tqbe::bits<32>(0u));
    } catch (const ::tqbe::ExitException &ex) {
      caught_abort = (ex.target == "c0_abort");
    }
    D2_CHECK(caught_abort, "divmod_u32(10, 0) must trigger c0_abort ExitException");
  }

  // Short-circuit guarded load right against ASan exact-size heap allocation
  {
    for (uint64_t n : {0ULL, 1ULL, 5ULL, 16ULL}) {
      int32_t *exact = n == 0 ? nullptr
                              : static_cast<int32_t *>(std::malloc(n * sizeof(int32_t)));
      for (uint64_t i = 0; i < n; ++i) exact[i] = static_cast<int32_t>(i * 10 + 7);
      ::tqbe::Mem mem;
      if (n > 0) {
        mem.map_bytes(reinterpret_cast<uint64_t>(exact),
                      reinterpret_cast<const uint8_t *>(exact),
                      n * sizeof(int32_t));
      }
      uint64_t ap = reinterpret_cast<uint64_t>(exact);
      // Missing target scans all the way to i == n; arr[n] MUST NOT be loaded!
      int32_t c_miss = find_guarded(exact, n, 99999);
      int32_t cpp_miss = static_cast<int32_t>(
          c0_leanrc::find_guarded(mem, ::tqbe::bits<64>(ap),
                                  ::tqbe::bits<64>(n),
                                  ::tqbe::bits<32>(99999)).data);
      D2_EQ(c_miss, -1, "find_guarded miss == -1");
      D2_EQ(c_miss, cpp_miss, "find_guarded miss parity");

      if (n > 0) {
        int32_t last_val = exact[n - 1];
        int32_t c_hit = find_guarded(exact, n, last_val);
        int32_t cpp_hit = static_cast<int32_t>(
            c0_leanrc::find_guarded(mem, ::tqbe::bits<64>(ap),
                                    ::tqbe::bits<64>(n),
                                    ::tqbe::bits<32>(static_cast<uint32_t>(last_val))).data);
        D2_EQ(c_hit, static_cast<int32_t>(n - 1), "find_guarded last element");
        D2_EQ(c_hit, cpp_hit, "find_guarded hit parity");
      }
      std::free(exact);
    }
  }

  std::printf("V3 lean_rc + goto + multi-ret + ASan short-circuit checks passed.\n");
}

/* ============================================================================
 * V4 & Extra: sum_pos64, intrinsics, switch/fallthrough/do-while/for
 * ============================================================================ */

inline void run_v4_and_extra_tests() {
  {
    std::vector<int64_t> xs = {0, -5, 10, std::numeric_limits<int64_t>::min(),
                               std::numeric_limits<int64_t>::max(), 42, -1};
    ::tqbe::Mem mem;
    map_vec(mem, xs);
    uint64_t ap = reinterpret_cast<uint64_t>(xs.data());
    for (uint64_t n : {uint64_t{0}, uint64_t{1}, uint64_t{3}, static_cast<uint64_t>(xs.size())}) {
      uint64_t c_res = sum_pos64(xs.data(), n);
      uint64_t cpp_res = c0_v4::sum_pos64(mem, ::tqbe::bits<64>(ap),
                                          ::tqbe::bits<64>(n)).data;
      D2_EQ(c_res, cpp_res, "sum_pos64");
    }
  }

  {
    ::tqbe::Mem mem;
    const double ds[] = {
        0.0, -0.0, 1.5, -3.5, 42.75, 1e20,
        std::numeric_limits<double>::infinity(),
        -std::numeric_limits<double>::infinity(),
        std::numeric_limits<double>::quiet_NaN()
    };
    const uint32_t x32s[] = {0u, 1u, 2u, 3u, 0x80000000u, 0xDEADBEEFu};
    const uint64_t x64s[] = {0ULL, 1ULL, 150ULL, 0x100000000ULL,
                             0x8000000000000000ULL, 0xFFFFFFFFFFFFFFFFULL};
    for (size_t i = 0; i < sizeof(ds) / sizeof(ds[0]); ++i) {
      uint32_t x32 = x32s[i % (sizeof(x32s) / sizeof(x32s[0]))];
      uint64_t x64 = x64s[i % (sizeof(x64s) / sizeof(x64s[0]))];
      double d = ds[i];
      uint64_t dbits = 0;
      std::memcpy(&dbits, &d, sizeof(dbits));
      uint32_t c_res = test_intrinsics(x32, x64, d);
      uint32_t cpp_res = static_cast<uint32_t>(
          c0_extra::test_intrinsics(
              mem, ::tqbe::bits<32>(x32), ::tqbe::bits<64>(x64),
              ::tqbe::fval<::tqbe::Fmt::d>{::tqbe::bits<64>(dbits)}).data);
      D2_EQ(c_res, cpp_res, "test_intrinsics");
    }
  }

  {
    ::tqbe::Mem mem;
    for (uint32_t mode = 0; mode < 8; ++mode) {
      for (uint32_t n : {0u, 1u, 2u, 5u, 8u}) {
        c0_u32_t3 c_res = test_switch_loops(mode, n);
        auto cpp_res = c0_extra::test_switch_loops(
            mem, ::tqbe::bits<32>(mode), ::tqbe::bits<32>(n));
        D2_EQ(c_res._0, static_cast<uint32_t>(std::get<0>(cpp_res).data), "sw._0");
        D2_EQ(c_res._1, static_cast<uint32_t>(std::get<1>(cpp_res).data), "sw._1");
        D2_EQ(c_res._2, static_cast<uint32_t>(std::get<2>(cpp_res).data), "sw._2");
      }
    }
  }

  std::printf("V4 & Extra differential checks passed.\n");
}

} // namespace d2

inline int run_d2_tests() {
  d2::run_v1_tests();
  d2::run_v2_tests();
  d2::run_v3_tests();
  d2::run_v4_and_extra_tests();
  std::printf("ALL D2 DIFFERENTIAL TESTS PASSED.\n");
  return 0;
}
