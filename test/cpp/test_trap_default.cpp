#ifdef TQBE_CATCH_UB
#error "test_trap_default.cpp must NOT define TQBE_CATCH_UB"
#endif

#include "gen_suite.hpp"

#include <cstdio>
#include <cstdlib>
#include <sys/wait.h>
#include <unistd.h>

using tqbe::Fmt;
using tqbe::Mem;
using tqbe::bits;
using tqbe::fval;

#define ASSERT_EQ(a, b)                                                       \
  do {                                                                        \
    auto _va = (a);                                                           \
    auto _vb = (b);                                                           \
    if (!(_va == _vb)) {                                                      \
      std::fprintf(stderr, "ASSERT_EQ failed at line %d\n", __LINE__);        \
      std::abort();                                                           \
    }                                                                         \
  } while (0)

#define ASSERT_TRUE(cond)                                                     \
  do {                                                                        \
    if (!(cond)) {                                                            \
      std::fprintf(stderr, "ASSERT_TRUE failed at line %d: %s\n", __LINE__,   \
                   #cond);                                                    \
      std::abort();                                                           \
    }                                                                         \
  } while (0)

namespace {

template <typename Fn>
void expect_traps(const char* name, Fn&& fn) {
  std::fflush(nullptr);
  pid_t pid = ::fork();
  if (pid < 0) {
    std::perror("fork");
    std::abort();
  }
  if (pid == 0) {
    try {
      (void)fn();
    } catch (const tqbe::UbException&) {
      // Must never throw UbException when TQBE_CATCH_UB is not defined.
      ::_exit(125);
    } catch (...) {
      ::_exit(124);
    }
    // Must NEVER silently return or elide trap under -O2.
    ::_exit(123);
  }
  int status = 0;
  if (::waitpid(pid, &status, 0) != pid) {
    std::perror("waitpid");
    std::abort();
  }
  if (!WIFSIGNALED(status)) {
    std::fprintf(stderr,
                 "TRAP CHECK FAILED (%s): expected signal, got exited(%d)\n",
                 name, WIFEXITED(status) ? WEXITSTATUS(status) : -1);
    std::abort();
  }
  int sig = WTERMSIG(status);
  if (sig != SIGILL && sig != SIGTRAP && sig != SIGABRT) {
    std::fprintf(stderr,
                 "TRAP CHECK UNEXPECTED SIGNAL (%s): sig=%d\n", name, sig);
    std::abort();
  }
}

} // namespace

int main() {
  Mem mem;

  // 1. Happy paths succeed normally without -DTQBE_CATCH_UB
  {
    Mem uf_mem;
    uf_mem.alloc(0x10000, 16 * 8, 0);
    for (uint64_t i = 0; i < 16; ++i) {
      tqbe::store<bits<64>>(uf_mem, bits<64>(0x10000 + i * 8), bits<64>(i));
    }
    uf_pre::fn_union(uf_mem, bits<64>(0x10000), bits<64>(2), bits<64>(5));
    ASSERT_EQ(uf_pre::find(uf_mem, bits<64>(0x10000), bits<64>(2)).data,
              uf_pre::find(uf_mem, bits<64>(0x10000), bits<64>(5)).data);
    ASSERT_EQ(uf_aarch64::find(uf_mem, bits<64>(0x10000), bits<64>(2)).data,
              uf_aarch64::find(uf_mem, bits<64>(0x10000), bits<64>(5)).data);

    ASSERT_EQ(edge_pre::jnz_hlt(mem, true, bits<64>(10)).data, 52ULL);
    ASSERT_EQ(edge_aarch64::jnz_hlt(mem, true, bits<64>(10)).data, 52ULL);

    bits<64> i64min(0x8000000000000000ULL);
    bits<64> neg1(0xFFFFFFFFFFFFFFFFULL);
    auto [sd0, ud0, sd4, sr] =
        edge_pre::div_edge(mem, i64min, neg1, bits<4>(0));
    ASSERT_EQ(sd0, i64min);
    ASSERT_EQ(ud0.data, 0ULL);
    ASSERT_EQ(sd4.data, 8ULL);
    ASSERT_EQ(sr.data, 0xFFFFFFFFFFFFFFFFULL);

    bits<64> shx(0x8000000000000003ULL);
    auto r0 = edge_pre::shift_edge(mem, shx, bits<64>(0));
    ASSERT_EQ(std::get<0>(r0), shx);

    Mem pm;
    pm.alloc(0x2000, 2, 0x5A);
    pm.alloc(0x3000, 1, 0x5A);
    auto [p1, p2, pAdd, pCmp, pSwap] =
        edge_pre::pair_edge(pm, bits<64>(0x2000), bits<64>(0x3000));
    ASSERT_EQ(p1.first, true);
    ASSERT_EQ(p1.second.data, 0xAAULL);
    ASSERT_EQ(p2.first, true);
    ASSERT_EQ(p2.second, false);
    ASSERT_EQ(pAdd.second.data, 0ULL);
    ASSERT_EQ(pCmp.first, true);
    ASSERT_EQ(pSwap.first.data, 0x3412ULL);

    fval<Fmt::q> q_neg05{bits<128>::from_words({0ULL, 0xBFFE000000000000ULL})};
    ASSERT_EQ(edge_pre::quad_huge_fptoui(mem, q_neg05).data, 0ULL);
  }

  // 2. .hlt and UB paths MUST execute __builtin_trap() under -O2
  {
    volatile bool cond = false;
    expect_traps("edge_pre::jnz_hlt(false)", [&]() {
      return edge_pre::jnz_hlt(mem, cond, bits<64>(10));
    });
    expect_traps("edge_aarch64::jnz_hlt(false)", [&]() {
      return edge_aarch64::jnz_hlt(mem, cond, bits<64>(10));
    });
  }

  {
    bits<64> i64min(0x8000000000000000ULL);
    bits<64> neg1(0xFFFFFFFFFFFFFFFFULL);
    expect_traps("div_edge sdiv(INT64_MIN,-1)", [&]() {
      return edge_pre::div_edge(mem, i64min, neg1, bits<4>(1));
    });
    expect_traps("div_edge sdiv(1,0)", [&]() {
      return edge_pre::div_edge(mem, bits<64>(1), bits<64>(0), bits<4>(1));
    });
    expect_traps("div_edge udiv(1,0)", [&]() {
      return edge_pre::div_edge(mem, bits<64>(1), bits<64>(0), bits<4>(2));
    });
    expect_traps("div_edge srem(1,0)", [&]() {
      return edge_pre::div_edge(mem, bits<64>(1), bits<64>(0), bits<4>(3));
    });
  }

  {
    Mem mm;
    mm.map_byte(0x4002, 2);
    mm.alloc(0x4100, 7, 0x77);
    expect_traps("mem_ub_edge invalid bool byte 2", [&]() {
      return edge_pre::mem_ub_edge(mm, true, bits<64>(0x4002));
    });
    expect_traps("mem_ub_edge unmapped byte", [&]() {
      return edge_pre::mem_ub_edge(mm, true, bits<64>(0x4003));
    });
    expect_traps("mem_ub_edge 7-byte buffer for 8-byte store", [&]() {
      return edge_pre::mem_ub_edge(mm, false, bits<64>(0x4100));
    });
  }

  for (uint64_t mode = 1; mode <= 5; ++mode) {
    expect_traps("dead_dynamic_ub", [&]() {
      return edge_pre::dead_dynamic_ub(mem, bits<8>(mode));
    });
  }

  {
    fval<Fmt::q> q_1e100{bits<128>::from_words({0ULL, 0x4149000000000000ULL})};
    fval<Fmt::q> q_neg1{bits<128>::from_words({0ULL, 0xBFFF000000000000ULL})};
    expect_traps("quad_huge_fptoui(2^332)", [&]() {
      return edge_pre::quad_huge_fptoui(mem, q_1e100);
    });
    expect_traps("quad_huge_fptoui(-1.0)", [&]() {
      return edge_pre::quad_huge_fptoui(mem, q_neg1);
    });
  }

  std::printf("ALL DEFAULT-TRAP (Rule A6) TESTS PASSED\n");
  return 0;
}
