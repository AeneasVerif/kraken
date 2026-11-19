module

public import LeanQbe.T.PrintQbe
public import LeanQbe.T.Legal
public import LeanQbe.T.Examples.UnionFind
public import LeanQbe.T.Examples.LratBytes
public import LeanQbe.T.Examples.LratTrim
public import LeanQbe.T.Examples.ChaCha
meta import LeanQbe.T.PrintQbe
meta import LeanQbe.T.Legal
meta import LeanQbe.T.Examples.UnionFind
meta import LeanQbe.T.Examples.LratBytes
meta import LeanQbe.T.Examples.LratTrim
meta import LeanQbe.T.Examples.ChaCha

/-!
# Tests and Stock-QBE `.ssa` Emitter for `LeanQbe.T.PrintQbe` and `LratTrim`

Covers:
1. `#guard` unit checks on `PrintQbe.fn`, `PrintQbe.fns`, and `PrintQbe.module` across
   `UnionFind`, `LratBytes`, `LratTrim`, legalized (`scalar64` and `aarch64`) variants,
   scalar/multi-result edge cases, and unsupported-feature error rejections.
2. CLI entrypoint (`main <out-dir>`) generating `.ssa` files for end-to-end compilation via
   stock QBE and execution against `test/uf_main.c`, `test/lrat_bytes_main.c`,
   `test/lrat_trim_main.c`, and an edge-case C harness.
-/

set_option autoImplicit false

namespace LeanQbeTest.T.PrintQbeTest

open LeanQbe.T

/-- Local `Module` wrapper for `UnionFind.ufFns`. -/
def ufModule : Module :=
  { fns := LeanQbe.T.Examples.UnionFind.ufFns, externs := [], exits := [] }

def containsSubstr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

def mustOk (r : Except String String) : Bool :=
  match r with
  | .ok s => !s.isEmpty
  | .error _ => false

def mustErr (r : Except String String) (needle : String := "") : Bool :=
  match r with
  | .ok _ => false
  | .error msg => needle.isEmpty || containsSubstr msg needle

def checkErrs : List (Except String String × String) → Bool
  | [] => true
  | (r, needle) :: rest => mustErr r needle && checkErrs rest

/-! ## Edge-case functions exercising `PrintQbe` coverage -/

/-- Parallel swap via block parameters + `%L0_p0`/`%L0_p1` sequential jump copies. -/
def parallelSwapFn : Fn where
  name := "tq_parallel_swap"
  as := [i64, i64, i64]
  rs := [i64]
  body := fun _ _ args =>
    let a := args.1
    let b := args.2.1
    let n := args.2.2.1
    .group (sig := [[i64, i64, i64]])
      (fun ls => .cons (fun xs =>
        let x := xs.1
        let y := xs.2.1
        let k := xs.2.2.1
        .let_ (op2 (.cmp .eq i64) (.var k) (.imm 0#64)) fun c =>
          .jnz (.var c.1)
            (.ret (.var x, ()))
            (.let_ (op2 (.sub i64) (.var k) (.imm 1#64)) fun k1 =>
              .let_ (op2 (.add i64) (.var x) (.imm 1#64)) fun x1 =>
                .jump ls.1 (.var y, .var x1.1, .var k1.1, ()))) .nil)
      (fun ls => .jump ls.1 (.var a, .var b, .var n, ()))

/-- Scalar `addc 64` + `subb 64` returning `(sum + bout)` mixed with carries. -/
def addcSubb64Fn : Fn where
  name := "tq_addc_subb64"
  as := [i64, i64, Ty.bool]
  rs := [i64]
  body := fun _ _ args =>
    let a := args.1
    let b := args.2.1
    let cin := args.2.2.1
    .let_ (op3 (.addc 64) (.var a) (.var b) (.var cin)) fun r1 =>
      .let_ (op3 (.subb 64) (.var r1.1) (.var b) (.var r1.2.1)) fun r2 =>
        .let_ (op1 (.ofBool 64) (.var r2.2.1)) fun b64 =>
          .let_ (op2 (.xor i64) (.var r2.1) (.var b64.1)) fun out =>
            .ret (.var out.1, ())

/-- Double-width `umulw 64` high half. -/
def umulhi64Fn : Fn where
  name := "tq_umulhi64"
  as := [i64, i64]
  rs := [i64]
  body := fun _ _ args =>
    .let_ (op2 (.umulw 64) (.var args.1) (.var args.2.1)) fun r =>
      .ret (.var r.2.1, ())

/-- Double-width `smulw 64` high half. -/
def smulhi64Fn : Fn where
  name := "tq_smulhi64"
  as := [i64, i64]
  rs := [i64]
  body := fun _ _ args =>
    .let_ (op2 (.smulw 64) (.var args.1) (.var args.2.1)) fun r =>
      .ret (.var r.2.1, ())

/-- Total `udiv0 64` / `sdiv0 64` (including `b = 0` and `INT64_MIN / -1`). -/
def div0TestFn : Fn where
  name := "tq_div0"
  as := [i64, i64, i64]
  rs := [i64]
  body := fun _ _ args =>
    let mode := args.1
    let a := args.2.1
    let b := args.2.2.1
    .let_ (op2 (.cmp .eq i64) (.var mode) (.imm 0#64)) fun isU =>
      .jnz (.var isU.1)
        (.let_ (op2 (.udiv0 64) (.var a) (.var b)) fun q => .ret (.var q.1, ()))
        (.let_ (op2 (.sdiv0 64) (.var a) (.var b)) fun q => .ret (.var q.1, ()))

/-- Rotate, `select`, `ternlog`, `.bool` signed comparisons, and sub-32 `i8` arithmetic. -/
def boolAndBitsEdgeFn : Fn where
  name := "tq_bool_bits_edge"
  as := [i64, i64, i64]
  rs := [i64]
  body := fun _ _ args =>
    let a := args.1
    let b := args.2.1
    let s := args.2.2.1
    .let_ (op2 (.cmp .ne i64) (.var a) (.imm 0#64)) fun ba =>
      .let_ (op2 (.cmp .ne i64) (.var b) (.imm 0#64)) fun bb =>
        .let_ (op2 (.cmp .slt .bool) (.var ba.1) (.var bb.1)) fun bslt =>
          .let_ (op2 (.rotl i64) (.var a) (.var s)) fun rl =>
            .let_ (op2 (.rotr i64) (.var rl.1) (.var s)) fun rr =>
              .let_ (op3 (.ternlog i64 (BitVec.ofNat 8 0xCA)) (.var rr.1) (.var b) (.imm 0xFF#64)) fun tl =>
                .let_ (op1 (.trunc 64 8) (.var a)) fun a8 =>
                  .let_ (op1 (.neg i8) (.var a8.1)) fun na8 =>
                    .let_ (op1 (.zext 8 64) (.var na8.1)) fun nz64 =>
                      .let_ (op3 (.select i64) (.var bslt.1) (.var nz64.1) (.var tl.1)) fun sel =>
                        .ret (.var sel.1, ())

/-- Sub-word `load`/`store` (`bool`, `i8`, `i16`, `i32`, `i64`) round-trip test. -/
def memWidthsFn : Fn where
  name := "tq_mem_widths"
  as := [i64]
  rs := [i64]
  body := fun _ _ args =>
    let p := args.1
    .store (t := .bool) (.imm true) (.var p) <|
    .load .bool (.var p) fun v0 =>
    .let_ (op1 (.ofBool 64) (.var v0)) fun b0 =>
    .let_ (op2 (.add i64) (.var p) (.imm 2#64)) fun p2 =>
    .store (t := i16) (.imm 0xBEEF#16) (.var p2.1) <|
    .load i16 (.var p2.1) fun v16 =>
    .let_ (op1 (.zext 16 64) (.var v16)) fun z16 =>
    .let_ (op2 (.shl i64) (.var z16.1) (.imm 1#64)) fun s16 =>
    .let_ (op2 (.or i64) (.var b0.1) (.var s16.1)) fun out =>
    .ret (.var out.1, ())

/-- Helper building an `if op == k then t else e` chain in `i64`. -/
private def switchOp {V : Ty → Type} {L : List Ty → Type}
    (op : V i64) (cases : List (Nat × Expr V L [i64])) (dflt : Expr V L [i64]) :
    Expr V L [i64] :=
  match cases with
  | [] => dflt
  | (k, br) :: rest =>
    .let_ (op2 (.cmp .eq i64) (.var op) (.imm (BitVec.ofNat 64 k))) fun c =>
      .jnz (.var c.1) br (switchOp op rest dflt)

/-- Immediate rotates (`rotr`/`rotl` at 32/64) and large shift immediates (`>= 256`). -/
def rotShiftImmEdgeFn : Fn where
  name := "tq_rot_shift_imm"
  as := [i32, i64, i64]
  rs := [i64]
  body := fun _ _ args =>
    let x := args.1
    let y := args.2.1
    let mode := args.2.2.1
    switchOp mode
      [ (0, .let_ (op2 (.rotr i32) (.var x) (.imm 16#32)) fun r =>
              .let_ (op1 (.zext 32 64) (.var r.1)) fun z => .ret (.var z.1, ()))
      , (1, .let_ (op2 (.rotl i32) (.var x) (.imm 12#32)) fun r =>
              .let_ (op1 (.zext 32 64) (.var r.1)) fun z => .ret (.var z.1, ()))
      , (2, .let_ (op2 (.rotr i32) (.var x) (.imm 0#32)) fun r =>
              .let_ (op1 (.zext 32 64) (.var r.1)) fun z => .ret (.var z.1, ()))
      , (3, .let_ (op2 (.rotl i64) (.var y) (.imm 5#64)) fun r => .ret (.var r.1, ()))
      , (4, .let_ (op2 (.rotr i64) (.var y) (.imm 0#64)) fun r => .ret (.var r.1, ()))
      , (5, .let_ (op2 (.shl i64) (.var y) (.imm 300#64)) fun r => .ret (.var r.1, ()))
      , (6, .let_ (op2 (.ashr i64) (.var y) (.imm 300#64)) fun r => .ret (.var r.1, ()))
      ]
      (.let_ (op2 (.lshr i32) (.var x) (.imm 300#32)) fun r =>
        .let_ (op1 (.zext 32 64) (.var r.1)) fun z => .ret (.var z.1, ()))

/-- Non-standard `.bits 48` arithmetic, shifts/rotates, division, and 48-bit comparisons. -/
def bits48EdgeFn : Fn where
  name := "tq_bits48"
  as := [i64, i64, i64]
  rs := [i64]
  body := fun V L args =>
    let op := args.1
    let a64 := args.2.1
    let b64 := args.2.2.1
    .let_ (op1 (.trunc 64 48) (.var a64)) fun a =>
    .let_ (op1 (.trunc 64 48) (.var b64)) fun b =>
    let ret48 (r : V (.bits 48)) : Expr V L [i64] :=
      .let_ (op1 (.zext 48 64) (.var r)) fun z => .ret (.var z.1, ())
    let retBool (c : V Ty.bool) : Expr V L [i64] :=
      .let_ (op1 (.ofBool 64) (.var c)) fun z => .ret (.var z.1, ())
    switchOp op
      [ (0,  .let_ (op2 (.add (.bits 48)) (.var a.1) (.var b.1)) fun r => ret48 r.1)
      , (1,  .let_ (op2 (.sub (.bits 48)) (.var a.1) (.var b.1)) fun r => ret48 r.1)
      , (2,  .let_ (op2 (.mul (.bits 48)) (.var a.1) (.var b.1)) fun r => ret48 r.1)
      , (3,  .let_ (op1 (.not (.bits 48)) (.var a.1)) fun r => ret48 r.1)
      , (4,  .let_ (op2 (.shl (.bits 48)) (.var a.1) (.var b.1)) fun r => ret48 r.1)
      , (5,  .let_ (op2 (.rotr (.bits 48)) (.var a.1) (.var b.1)) fun r => ret48 r.1)
      , (6,  .let_ (op2 (.ashr (.bits 48)) (.var a.1) (.var b.1)) fun r => ret48 r.1)
      , (7,  .let_ (op2 (.udiv0 48) (.var a.1) (.var b.1)) fun r => ret48 r.1)
      , (8,  .let_ (op2 (.sdiv0 48) (.var a.1) (.var b.1)) fun r => ret48 r.1)
      , (9,  .let_ (op2 (.cmp .eq (.bits 48)) (.var a.1) (.var b.1)) fun r => retBool r.1)
      , (10, .let_ (op2 (.cmp .ult (.bits 48)) (.var a.1) (.var b.1)) fun r => retBool r.1)
      ]
      (.let_ (op2 (.cmp .slt (.bits 48)) (.var a.1) (.var b.1)) fun r => retBool r.1)

/-- 1-bit `.bits 1` arithmetic, shifts/rotates, division, and signed/unsigned comparisons. -/
def bits1EdgeFn : Fn where
  name := "tq_bits1"
  as := [i64, i64, i64]
  rs := [i64]
  body := fun V L args =>
    let op := args.1
    let a64 := args.2.1
    let b64 := args.2.2.1
    .let_ (op1 (.trunc 64 1) (.var a64)) fun a =>
    .let_ (op1 (.trunc 64 1) (.var b64)) fun b =>
    let ret1 (r : V (.bits 1)) : Expr V L [i64] :=
      .let_ (op1 (.zext 1 64) (.var r)) fun z => .ret (.var z.1, ())
    let retBool (c : V Ty.bool) : Expr V L [i64] :=
      .let_ (op1 (.ofBool 64) (.var c)) fun z => .ret (.var z.1, ())
    switchOp op
      [ (0,  .let_ (op2 (.add (.bits 1)) (.var a.1) (.var b.1)) fun r => ret1 r.1)
      , (1,  .let_ (op2 (.mul (.bits 1)) (.var a.1) (.var b.1)) fun r => ret1 r.1)
      , (2,  .let_ (op1 (.neg (.bits 1)) (.var a.1)) fun r => ret1 r.1)
      , (3,  .let_ (op1 (.not (.bits 1)) (.var a.1)) fun r => ret1 r.1)
      , (4,  .let_ (op2 (.shl (.bits 1)) (.var a.1) (.var b.1)) fun r => ret1 r.1)
      , (5,  .let_ (op2 (.rotr (.bits 1)) (.var a.1) (.var b.1)) fun r => ret1 r.1)
      , (6,  .let_ (op2 (.ashr (.bits 1)) (.var a.1) (.var b.1)) fun r => ret1 r.1)
      , (7,  .let_ (op2 (.udiv0 1) (.var a.1) (.var b.1)) fun r => ret1 r.1)
      , (8,  .let_ (op2 (.sdiv0 1) (.var a.1) (.var b.1)) fun r => ret1 r.1)
      , (9,  .let_ (op2 (.cmp .eq (.bits 1)) (.var a.1) (.var b.1)) fun r => retBool r.1)
      , (10, .let_ (op2 (.cmp .ult (.bits 1)) (.var a.1) (.var b.1)) fun r => retBool r.1)
      ]
      (.let_ (op2 (.cmp .slt (.bits 1)) (.var a.1) (.var b.1)) fun r => retBool r.1)

def chacha20Fn : Fn where
  name := "tq_chacha20_block"
  as := [i64, i64]
  rs := []
  body := LeanQbe.T.Examples.ChaCha.chacha20Block

def chacha20Module : Module where
  fns := [chacha20Fn.legal LegalTarget.scalar64]
  externs := []
  exits := []

def edgeScalarModule : Module where
  fns :=
    [ parallelSwapFn
    , addcSubb64Fn
    , umulhi64Fn
    , smulhi64Fn
    , div0TestFn
    , boolAndBitsEdgeFn
    , memWidthsFn
    , rotShiftImmEdgeFn
    , bits48EdgeFn
    , bits1EdgeFn
    ]
  externs := []
  exits := []

/-! ## Rejection test cases -/

def multiRetFn : Fn where
  name := "bad_multi_ret"
  as := [i64]
  rs := [i64, i64]
  body := fun _ _ args => .ret (.var args.1, .var args.1, ())

def multiCallFn : Fn where
  name := "bad_multi_call"
  as := []
  rs := [i64]
  body := fun _ _ _ =>
    .call "callee" (as := []) (bs := [i64, i64]) () fun r => .ret (.var r.1, ())

def floatFn : Fn where
  name := "bad_float"
  as := [Ty.float .d]
  rs := [Ty.float .d]
  body := fun _ _ args => .let_ (op2 (.fadd (Ty.float .d)) (.var args.1) (.var args.1)) fun r => .ret (.var r.1, ())

def pairFn : Fn where
  name := "bad_pair"
  as := [i64, i64]
  rs := [i64]
  body := fun _ _ args =>
    .let_ (op2 (.mkpair i64 i64) (.var args.1) (.var args.2.1)) fun p =>
      .let_ (op1 (.unpair i64 i64) (.var p.1)) fun u =>
        .ret (.var u.1, ())

def wideBitsFn : Fn where
  name := "bad_wide"
  as := [.bits 128]
  rs := [.bits 128]
  body := fun _ _ args => .ret (.var args.1, ())

def oddLoadFn : Fn where
  name := "bad_load24"
  as := [i64]
  rs := [.bits 24]
  body := fun _ _ args => .load (.bits 24) (.var args.1) fun v => .ret (.var v, ())

def dupModule : Module where
  fns := [umulhi64Fn, umulhi64Fn]
  externs := []
  exits := []

def dupExternModule : Module where
  fns := [umulhi64Fn]
  externs := [{ name := "tq_umulhi64", as := [i64, i64], rs := [i64] }]
  exits := []

/-! ## Checks -/

#guard LeanQbe.T.Examples.LratBytes.lratBytesModule.checkAcyclic = true
#guard LeanQbe.T.Examples.LratTrim.lratTrimModule.checkAcyclic = true

#guard (PrintQbe.fns LeanQbe.T.Examples.UnionFind.ufFns).isOk = true
#guard (PrintQbe.module LeanQbe.T.Examples.LratBytes.lratBytesModule).isOk = true
#guard (PrintQbe.module LeanQbe.T.Examples.LratTrim.lratTrimModule).isOk = true

#guard (PrintQbe.fns (LeanQbe.T.Examples.UnionFind.ufFns.map (Fn.legal LegalTarget.scalar64))).isOk = true
#guard (PrintQbe.fns (LeanQbe.T.Examples.LratBytes.lratBytesModule.fns.map (Fn.legal LegalTarget.scalar64))).isOk = true
#guard (PrintQbe.fns (LeanQbe.T.Examples.LratTrim.lratTrimFns.map (Fn.legal LegalTarget.scalar64))).isOk = true
#guard (PrintQbe.fns (LeanQbe.T.Examples.LratTrim.lratTrimFns.map (Fn.legal LegalTarget.aarch64))).isOk = true

#guard match PrintQbe.module LeanQbe.T.Examples.LratTrim.lratTrimModule with
  | .ok s =>
    ((s.splitOn "export function $br_trim_proof(l %p0)").length > 1) &&
    ((s.splitOn "export function $br_check_proof(l %p0)").length > 1) &&
    ((s.splitOn "export function $br_check_clause(l %p0, l %p1, l %p2, l %p3)").length > 1) &&
    ((s.splitOn "call $lrat_fail(").length > 1) &&
    ((s.splitOn "\thlt").length > 1)
  | .error _ => false

#guard match PrintQbe.fns LeanQbe.T.Examples.UnionFind.ufFns with
  | .ok s =>
    ((s.splitOn "export function l $find(l %p0, l %p1)").length > 1) &&
    ((s.splitOn "export function $union(l %p0, l %p1, l %p2)").length > 1)
  | .error _ => false

#guard ufModule.checkAcyclic = true
#guard edgeScalarModule.checkAcyclic = true
#guard chacha20Module.checkAcyclic = true
#guard mustOk (PrintQbe.module ufModule)
#guard mustOk (PrintQbe.module edgeScalarModule)
#guard mustOk (PrintQbe.module chacha20Module)
#guard mustErr (PrintQbe.fn chacha20Fn) "unsupported load type"
#guard checkErrs
  [ (PrintQbe.fn multiRetFn, "at most 1")
  , (PrintQbe.fn multiCallFn, "at most 1")
  , (PrintQbe.fn floatFn, "floating-point")
  , (PrintQbe.fn pairFn, "pair/vector")
  , (PrintQbe.fn wideBitsFn, "> 64")
  , (PrintQbe.fn oddLoadFn, "unsupported load type")
  , (PrintQbe.module dupModule, "duplicate symbol")
  , (PrintQbe.module dupExternModule, "duplicate symbol")
  , (PrintQbe.fn { parallelSwapFn with name := "" }, "empty")
  ]

/-! ## CLI `.ssa` Generator -/

def writeSsa (outDir : System.FilePath) (filename : String)
    (res : Except String String) : IO Bool := do
  match res with
  | .error err =>
    IO.eprintln s!"PrintQbe error for {filename}: {err}"
    pure false
  | .ok text =>
    IO.FS.writeFile (outDir / filename) text
    pure true

/-- Generate stock-QBE `.ssa` artifacts into `outDir`. Returns `0` on success, `1` on failure. -/
public def runGenerate (outDir : System.FilePath) : IO UInt32 := do
  IO.FS.createDirAll outDir
  let uf := ufModule
  let lb := LeanQbe.T.Examples.LratBytes.lratBytesModule
  let lt := LeanQbe.T.Examples.LratTrim.lratTrimModule
  let jobs : List (String × Except String String) :=
    [ ("uf.ssa", PrintQbe.module uf)
    , ("uf_legal64.ssa", PrintQbe.fns (uf.fns.map (Fn.legal LegalTarget.scalar64)))
    , ("lrat_bytes.ssa", PrintQbe.module lb)
    , ("lrat_bytes_legal64.ssa", PrintQbe.fns (lb.fns.map (Fn.legal LegalTarget.scalar64)))
    , ("lrat_trim.ssa", PrintQbe.module lt)
    , ("lrat_trim_legal64.ssa", PrintQbe.fns (lt.fns.map (Fn.legal LegalTarget.scalar64)))
    , ("lrat_trim_legal_a64.ssa", PrintQbe.fns (lt.fns.map (Fn.legal LegalTarget.aarch64)))
    , ("edge_scalar.ssa", PrintQbe.module edgeScalarModule)
    , ("chacha20_legal64.ssa", PrintQbe.module chacha20Module)
    ]
  let mut ok := true
  for (name, res) in jobs do
    let b ← writeSsa outDir name res
    if !b then ok := false
  pure (if ok then 0 else 1)

/-- Entry point for `lake env lean --run LeanQbeTest/T/PrintQbeTest.lean <out-dir>`. -/
public def main (args : List String) : IO UInt32 :=
  let outDir := match args with
    | d :: _ => System.FilePath.mk d
    | [] => System.FilePath.mk "/tmp/leanqbe-printqbe"
  runGenerate outDir

end LeanQbeTest.T.PrintQbeTest

public def main (args : List String) : IO UInt32 :=
  LeanQbeTest.T.PrintQbeTest.main args
