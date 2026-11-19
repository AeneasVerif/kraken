module

public import LeanQbe.T.Examples.Bignum
public import LeanQbe.T.Examples.ChaCha
public import LeanQbe.T.Examples.LitmusProgs
public import LeanQbe.T.Examples.LratBytes
public import LeanQbe.T.Examples.LratTrim
public import LeanQbe.T.Examples.UnionFind

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! # Target-Neutral Benchmark and Litmus Programs -/

/-- Named example and benchmark programs for the target-neutral CLI and QBE
round-trip tests. -/
def programs : List (String × List Fn) :=
  [ ("tracer",           [Examples.Litmus.tracer])
  , ("ifelse",           [Examples.Litmus.ifelse])
  , ("sumto",            [Examples.Litmus.sumto])
  , ("evenodd",          [Examples.Litmus.evenodd])
  , ("nested",           [Examples.Litmus.nested])
  , ("swap",             [Examples.Litmus.swap])
  , ("spill10",          [Examples.Litmus.spill10])
  , ("callinc",          [Examples.Litmus.inc, Examples.Litmus.callinc])
  , ("twice",            [Examples.Litmus.check, Examples.Litmus.twice])
  , ("sumcall",          [Examples.Litmus.inc, Examples.Litmus.sumcall])
  , ("uf",               Examples.UnionFind.ufFns)
  , ("unionfind",        Examples.UnionFind.ufFns)
  , ("uf_bench",         Examples.UnionFind.ufFns)
  , ("lrat_trim",        Examples.LratTrim.lratTrimFns)
  , ("lrat_bytes",       Examples.LratBytes.lratBytesFns)
  , ("bignum_mul4x4",    [Examples.Bignum.mul4x4Fn])
  , ("bignum_add25519",  [Examples.Bignum.addMod25519Fn])
  , ("bignum_sub25519",  [Examples.Bignum.subMod25519Fn])
  , ("chacha20",         [Examples.ChaCha.chacha20Fn])
  ]

end LeanQbe.T
