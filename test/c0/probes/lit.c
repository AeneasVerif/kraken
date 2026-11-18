#include "c0.h"
#define NEG1U (-1u)
#define M1 (-1)
#define BIGU 0xFFFFFFFFu
#define BIGD 4294967295
#define NEGD -3000000000
enum { EA, EB = 5, EC, ENEG = -1 };
//T l1 u64 : :
u64 l1(void) { return 0xFFFFFFFF; }
//T l2 i64 : :
i64 l2(void) { return 0xFFFFFFFF; }
//T l3 i64 : :
i64 l3(void) { return -1; }
//T l4 u64 : :
u64 l4(void) { return -1; }
//T l5 u64 : :
u64 l5(void) { return 1 << 31; }
//T l6 u64 : :
u64 l6(void) { return 1u << 31; }
//T l7 i64 : :
i64 l7(void) { return 2147483648; }
//T l8 i64 : :
i64 l8(void) { return -2147483648; }
//T l9 i64 : :
i64 l9(void) { return 4294967295; }
//T l10 i64 : :
i64 l10(void) { return -4294967295; }
//T l11 i64 : :
i64 l11(void) { return 3000000000 * 2; }
//T l12 u64 : :
u64 l12(void) { return 0x7FFFFFFF + 1; }
//T l13 u64 : :
u64 l13(void) { return 0x80000000 + 0x80000000; }
//T l14 u64 : :
u64 l14(void) { return -1u; }
//T l15 u64 : :
u64 l15(void) { return -1L; }
//T l16 u64 : :
u64 l16(void) { return 1ULL << 63; }
//T l17 u64 : :
u64 l17(void) { return 5000000000; }
//T l18 i64 : :
i64 l18(void) { return 0x100000000; }
//T l19 bool : :
bool l19(void) { return -1 < 0u; }
//T l20 bool : :
bool l20(void) { return -1 < 0x80000000; }
//T l20d bool : :
bool l20d(void) { return -1 < 2147483648; }
//T l21 i32 : :
i32 l21(void) { return 'a' + '\n' * 2 + '\0' + '\\' * 3 + '\'' * 5 + '\x41' * 7 + '\t' + '\r' + '"'; }
//T l22 u64 : :
u64 l22(void) { return sizeof('a'); }
//T l23 u64 : i32 i32 : 1 2
u64 l23(i32 a, i32 b) { return sizeof(a < b) * 100u + sizeof(!a) * 10u + sizeof(a && b); }
//T l23b u64 : :
u64 l23b(void) { return sizeof(true); }
//T l24 u64 : :
u64 l24(void) { return 077 + 0b101 * 1000; }
//T l25 i64 : :
i64 l25(void) { return 2147483647 + 1; }
//T l26 i64 : :
i64 l26(void) { return 0xFFFFFFFFu + 1; }
//T l27 i64 : :
i64 l27(void) { return 4294967296; }
//T l28 u64 : :
u64 l28(void) { return 18446744073709551615u; }
//T l29 i64 : :
i64 l29(void) { return 9223372036854775807; }
//T l30 i64 : :
i64 l30(void) { return 1l << 40; }
//T l31 u64 : :
u64 l31(void) { return 0x80000000 >> 31; }
//T l32 i64 : :
i64 l32(void) { return (-2147483647 - 1) >> 31; }
//T l33 i64 : :
i64 l33(void) { return 2147483648 >> 1; }
//T l34 bool : u32 : 5
bool l34(u32 x) { return x < 4294967296; }
//T l35 i64 : i32 : -1 | 5
i64 l35(i32 x) { return x + 4294967295; }
//T l36 i64 : i32 : -1 | 5
i64 l36(i32 x) { return x * 3000000000; }
//T l37 u64 : :
u64 l37(void) { return 4294967295U + 1; }
//T l38 u64 : :
u64 l38(void) { return 4294967296U; }
//T l39 u64 : :
u64 l39(void) { return ~0; }
//T l40 u64 : :
u64 l40(void) { return ~0u; }
//T l41 u64 : :
u64 l41(void) { return ~0x80000000; }
//T l42 i64 : :
i64 l42(void) { return ~2147483648; }
//T d1 u64 : :
u64 d1(void) { return NEG1U; }
//T d2 u64 : :
u64 d2(void) { return M1; }
//T d3 u64 : :
u64 d3(void) { return BIGU + 1; }
//T d4 i64 : :
i64 d4(void) { return BIGD; }
//T d4b i64 : :
i64 d4b(void) { return BIGD + 1; }
//T d5 i64 : :
i64 d5(void) { return NEGD; }
//T d6 i64 : i64 : 10
i64 d6(i64 x) { return x - M1; }
//T e1 u64 : :
u64 e1(void) { return EC * 100 + EB * 10 + EA; }
//T e2 u64 : :
u64 e2(void) { return ENEG; }
//T e3 u32 : u32 : 9
u32 e3(u32 EB) { return EB; }
//T e4 u32 : u32 : 9
u32 e4(u32 x) { u32 EC = x + 1u; return EC; }
