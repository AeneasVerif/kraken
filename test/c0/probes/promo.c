#include "c0.h"
//T avg8 u32 : u8 u8 : 0 0 | 255 255 | 200 100 | 255 1
u32 avg8(u8 a, u8 b) { return (a + b) >> 1; }
//T mul16 u32 : u16 u16 : 65535 65535 | 256 256 | 0 5
u32 mul16(u16 a, u16 b) { return a * b; }
//T mul16w u64 : u16 u16 : 65535 65535 | 300 300 | 46341 46341
u64 mul16w(u16 a, u16 b) { return a * b; }
//T not8 u32 : u8 : 0 | 1 | 255 | 0x80
u32 not8(u8 a) { return ~a; }
//T not8n u8 : u8 : 0 | 1 | 255 | 0x80
u8 not8n(u8 a) { return ~a; }
//T not8w u64 : u8 : 0 | 255
u64 not8w(u8 a) { return ~a; }
//T not16cmp bool : u16 : 0 | 0xffff
bool not16cmp(u16 a) { return ~a == 0xffff; }
//T neg8 i32 : u8 : 0 | 1 | 255
i32 neg8(u8 a) { return -a; }
//T neg8w u64 : u8 : 0 | 1 | 255
u64 neg8w(u8 a) { return -a; }
//T negu32w u64 : u32 : 0 | 1 | 0xffffffff
u64 negu32w(u32 a) { return -a; }
//T cmp_i32_u32 bool : i32 u32 : -1 1 | 1 2 | 2 1 | -2 0xfffffffe | 0 0
bool cmp_i32_u32(i32 a, u32 b) { return a < b; }
//T cmp_i64_u32 bool : i64 u32 : -1 1 | 1 2 | 0x100000000 5
bool cmp_i64_u32(i64 a, u32 b) { return a < b; }
//T cmp_i8_u8 bool : i8 u8 : -1 1 | 1 200 | -128 255
bool cmp_i8_u8(i8 a, u8 b) { return a < b; }
//T cmp_u16_i32 bool : u16 i32 : 65535 -1 | 1 2
bool cmp_u16_i32(u16 a, i32 b) { return a < b; }
//T cmp_i32_u64 bool : i32 u64 : -1 1 | 1 2
bool cmp_i32_u64(i32 a, u64 b) { return a < b; }
//T cmp_i16_u32 bool : i16 u32 : -1 1 | 1 2
bool cmp_i16_u32(i16 a, u32 b) { return a > b; }
//T eq_u8_m1 bool : u8 : 255 | 0
bool eq_u8_m1(u8 a) { return a == -1; }
//T eq_i8_u32 bool : i8 u32 : -1 0xffffffff | -1 255
bool eq_i8_u32(i8 a, u32 b) { return a == b; }
//T mixw u64 : u32 i32 : 0 -1 | 5 -6 | 0xffffffff 1
u64 mixw(u32 a, i32 b) { return a + b; }
//T mixw2 u64 : u32 i64 : 0 -1 | 0xffffffff 1
u64 mixw2(u32 a, i64 b) { return a + b; }
//T mixw3 i64 : i32 u32 : 1 2 | -1 0
i64 mixw3(i32 a, u32 b) { return a - b; }
//T mixw4 i64 : i32 i16 : 1 2 | -2147483648 1
i64 mixw4(i32 a, i16 b) { return a - b; }
//T mixw5 u64 : u8 i64 : 255 -256
u64 mixw5(u8 a, i64 b) { return a + b; }
//T cadd u8 : u8 : 0 | 255 | 200
u8 cadd(u8 x) { x += 300; return x; }
//T cadd2 u32 : u8 : 0 | 255 | 200
u32 cadd2(u8 a) { u8 x = a; x += 300; return x; }
//T csub i32 : i8 : 0 | -100 | 127
i32 csub(i8 x) { x -= 200; return x; }
//T cshl u32 : u8 : 0xff | 0x1f
u32 cshl(u8 x) { x <<= 4; return x; }
//T cshr i32 : i8 : -128 | -1 | 64
i32 cshr(i8 x) { x >>= 1; return x; }
//T cmul u32 : u16 : 0xffff | 300
u32 cmul(u16 x) { x *= x; return x; }
//T cdiv i32 : i8 : -128 | 127 | -1
i32 cdiv(i8 x) { x /= -1; return x; }
//T cxor u64 : u32 i32 : 0 -1 | 0xf0f0 0x0f0f
u64 cxor(u32 x, i32 m) { u64 r = 0ULL; r ^= x; r |= m; return r; }
//T cand u64 : u64 u32 : 0xffffffffffffffff 0xfffffff0
u64 cand(u64 x, u32 m) { x &= m; return x; }
//T candn u64 : u64 u32 : 0xffffffffffffffff 0x0f
u64 candn(u64 x, u32 m) { x &= ~m; return x; }
//T candi u64 : u64 : 0xffffffffffffffff
u64 candi(u64 x) { x &= ~1; return x; }
//T candu u64 : u64 : 0xffffffffffffffff
u64 candu(u64 x) { x &= ~1u; return x; }
//T divmix u32 : i32 u32 : -7 2 | 7 2
u32 divmix(i32 a, u32 b) { return a / b; }
//T shmix u64 : i32 u32 : -8 1
u64 shmix(i32 a, u32 b) { return a >> b; }
//T chain bool : i32 i32 i32 : 3 2 1 | 1 2 3 | -5 -4 0
bool chain(i32 a, i32 b, i32 c) { return a < b < c; }
//T boolarith u32 : bool bool : 1 1 | 0 1 | 1 0 | 0 0
u32 boolarith(bool a, bool b) { return (a + b) * 10u + (a & b) + (a | b) * 100u + (a ^ b) * 1000u; }
//T boolnot i32 : bool : 0 | 1
i32 boolnot(bool a) { return ~a; }
//T boolneg i64 : bool : 0 | 1
i64 boolneg(bool a) { return -a; }
//T boolcomp bool : bool : 0 | 1
bool boolcomp(bool b) { b -= 1; return b; }
//T ctypes i64 : i64 : 200 | -1 | 0x1234567890
i64 ctypes(i64 v) { char c = (char)v; unsigned char uc = (unsigned char)v; short s = (short)v; unsigned short us = (unsigned short)v; int i = (int)v; unsigned int ui = (unsigned int)v; long l = v; unsigned long ul = (unsigned long)v; long long ll = v; signed char sc = (signed char)v; const u32 k = 3u;
  return c + uc * 2 + s * 3 + us * 5 + i * 7LL + ui * 11LL + l * 13 + (i64)(ul >> 60) + ll + sc + k; }
