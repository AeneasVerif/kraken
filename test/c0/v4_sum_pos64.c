#include "../../LeanQbe/T/Frontend/C0/c0.h"

u64 sum_pos64(i64 *arr, u64 n) {
  u64 i = 0ULL;
  u64 acc = 0ULL;
  while (i < n) {
    i64 v = arr[i];
    if (v > 0) {
      acc = acc + (u64)v;
    }
    i = i + 1ULL;
  }
  return acc;
}
