module

public import LeanQbe.T.Examples.ChaCha
public import LeanQbe.T.Examples.Bignum
public import LeanQbe.T.Examples.UnionFindLemmas
import LeanQbe.T.Logic.MemLemmas
meta import LeanQbe.T.Examples.ChaCha
meta import LeanQbe.T.Examples.Bignum
meta import LeanQbe.T.Examples.UnionFind

/-!
# Verified Workloads (`ChaCha20`, `Curve25519 Bignum`, `UnionFind`) — Source Specification Audit

Self-contained source-level specification and typed-IR correctness audit covering three verified
systems/cryptographic workloads in `LeanQbe.T`. Architecture-independent (imports neither
`Kraken.X64` nor `Kraken.AArch64`).

## What This Workstream Proves
1. **ChaCha20 block (`Examples.ChaCha`)**:
   * RFC 8439 §2.1.1 quarter-round and §2.3.2 block test vectors (`audit_chacha_qr`,
     `audit_chacha_vec`).
   * Row-SIMD `v4i32` `chacha20Block` computes `(rfcChaCha20Core init).toRows` into `out` while
     preserving `inp` and caller frame `R` (`audit_chacha_ir`, `audit_chacha_mod`), with a
     concrete RFC 8439 §2.3.2 corollary (`audit_chacha_rfc`).
2. **Curve25519 Bignum kernels (`Examples.Bignum`)**:
   * `mul4x4`: 4×4-limb schoolbook multiplication producing an 8-limb result whose natural-number
     value satisfies `limbsVal rs = limbsVal as * limbsVal bs` (`audit_mul4x4_ir`).
   * `addMod25519` & `subMod25519`: branch-free constant-time modular addition and subtraction mod
     `p25519 = 2 ^ 255 - 19` (`audit_add25519_ir`, `audit_sub25519_ir`, `audit_bignum_mod`).
3. **Disjoint-Set Union-Find (`Examples.UnionFind`)**:
   * Path-halving `find` returns `rep x` while preserving the abstract forest `uf p n rep ⋆ R`
     (`audit_uf_find_ir`).
   * Call-based `union` and inlined `unionInline` transform `uf p n rep ⋆ R` into
     `uf p n (merge rep x y) ⋆ R` (`audit_uf_union_ir`, `audit_uf_in_ir`, `audit_uf_mod`).

## Inputs / Assumptions
* Disjoint separation-logic memory ownership (`array` / `array64` / `uf`) of input, output, and
  caller frame `R`; canonical inputs `< p25519` for modular add/sub; in-bounds element indices
  `x.toNat < n` / `y.toNat < n` for Union-Find.

## Trusted Computing Base (TCB)
* Lean 4 kernel (`propext`, `Classical.choice`, `Quot.sound`).
* Functional mathematical models (`rfcChaCha20Core`, `limbsVal`, `p25519`, `Forest` / `merge`) and
  typed-IR weakest-precondition semantics `LeanQbe.T.Semantics.wp` (discharged to machine code in
  `WorkloadsAuditX64.lean` and `WorkloadsAuditArm64.lean`).
-/

set_option autoImplicit false

public section

namespace WorkloadsAuditSpec

open Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil
open LeanQbe.T.Examples

/-! ## 1. ChaCha20 Block (`v4i32` Row-SIMD) -/

theorem audit_chacha_qr :
    ChaCha.quarterRound 0x11111111#32 0x01020304#32 0x9b8d6f43#32 0x01234567#32 =
      (0xea2a92f4#32, 0xcb1cf8ce#32, 0x4581472e#32, 0x5881c4bb#32) :=
  ChaCha.rfc8439_quarterRound_test

theorem audit_chacha_vec :
    (ChaCha.rfcChaCha20Core ChaCha.rfc8439_test_init).toWords = ChaCha.rfc8439_expected_words ∧
    (ChaCha.rfcChaCha20Core ChaCha.rfc8439_test_init).toBytes = ChaCha.rfc8439_expected_bytes :=
  ⟨ChaCha.rfc8439_test_vector_words, ChaCha.rfc8439_test_vector_bytes⟩

theorem audit_chacha_ir (Γ : Env) (out inp : BitVec 64) (init : ChaCha.State)
    (old : List ChaCha.Row) (R : Mem 64 → Prop) (m : Mem 64) (hold : old.length = 4)
    (hm : (array (t := v4i32) out old ⋆ array (t := v4i32) inp init.toRows ⋆ R) m) :
    Func.spec Γ ChaCha.chacha20Block (out, inp, ()) m
      (fun _ m' =>
        (array (t := v4i32) out (ChaCha.rfcChaCha20Core init).toRows ⋆
          array (t := v4i32) inp init.toRows ⋆ R) m')
      (fun _ _ _ _ => False) :=
  ChaCha.chacha20Block_correct Γ (out, inp, ()) m _ _ ⟨init, old, R, hold, hm, fun _ hm' => hm'⟩

theorem audit_chacha_rfc (Γ : Env) (out inp : BitVec 64) (old : List ChaCha.Row)
    (R : Mem 64 → Prop) (m : Mem 64) (hold : old.length = 4)
    (hm : (array (t := v4i32) out old ⋆
      array (t := v4i32) inp ChaCha.rfc8439_test_init.toRows ⋆ R) m) :
    Func.spec Γ ChaCha.chacha20Block (out, inp, ()) m
      (fun _ m' => ∃ res : ChaCha.State,
        res.toWords = ChaCha.rfc8439_expected_words ∧
        res.toBytes = ChaCha.rfc8439_expected_bytes ∧
        (array (t := v4i32) out res.toRows ⋆
          array (t := v4i32) inp ChaCha.rfc8439_test_init.toRows ⋆ R) m')
      (fun _ _ _ _ => False) :=
  ChaCha.chacha20Block_rfc8439_vector Γ out inp old R m hold hm

theorem audit_chacha_mod : ModuleOk ChaCha.chacha20Env ChaCha.chacha20Module :=
  ChaCha.chacha20_moduleOk

/-! ## 2. Curve25519 Bignum Kernels (`mul4x4`, `addMod25519`, `subMod25519`) -/

theorem audit_mul4x4_ir (Γ : Env) (out pa pb : BitVec 64)
    (as bs out0 : List (BitVec 64)) (R : Mem 64 → Prop) (m : Mem 64)
    (has : as.length = 4) (hbs : bs.length = 4) (hout : out0.length = 8)
    (hm : (array64 out out0 ⋆ array64 pa as ⋆ array64 pb bs ⋆ R) m) :
    Func.spec Γ Bignum.mul4x4 (out, pa, pb, ()) m
      (fun _ m' => ∃ rs : List (BitVec 64), rs.length = 8 ∧
        limbsVal rs = limbsVal as * limbsVal bs ∧
        (array64 out rs ⋆ array64 pa as ⋆ array64 pb bs ⋆ R) m')
      (fun _ _ _ _ => False) :=
  Bignum.mul4x4_correct Γ (out, pa, pb, ()) m _ _
    ⟨as, bs, out0, R, has, hbs, hout, hm, fun rs _ hrs hmul hm' => ⟨rs, hrs, hmul, hm'⟩⟩

theorem audit_add25519_ir (Γ : Env) (out pa pb : BitVec 64)
    (as bs out0 : List (BitVec 64)) (R : Mem 64 → Prop) (m : Mem 64)
    (has : as.length = 4) (hbs : bs.length = 4) (hout : out0.length = 4)
    (ha_lt : limbsVal as < Bignum.p25519) (hb_lt : limbsVal bs < Bignum.p25519)
    (hm : (array64 out out0 ⋆ array64 pa as ⋆ array64 pb bs ⋆ R) m) :
    Func.spec Γ Bignum.addMod25519 (out, pa, pb, ()) m
      (fun _ m' => ∃ rs : List (BitVec 64), rs.length = 4 ∧
        limbsVal rs = (limbsVal as + limbsVal bs) % Bignum.p25519 ∧
        limbsVal rs < Bignum.p25519 ∧
        (array64 out rs ⋆ array64 pa as ⋆ array64 pb bs ⋆ R) m')
      (fun _ _ _ _ => False) :=
  Bignum.addMod25519_correct Γ (out, pa, pb, ()) m _ _
    ⟨as, bs, out0, R, has, hbs, hout, ha_lt, hb_lt, hm,
      fun rs _ hrs hmod hlt hm' => ⟨rs, hrs, hmod, hlt, hm'⟩⟩

theorem audit_sub25519_ir (Γ : Env) (out pa pb : BitVec 64)
    (as bs out0 : List (BitVec 64)) (R : Mem 64 → Prop) (m : Mem 64)
    (has : as.length = 4) (hbs : bs.length = 4) (hout : out0.length = 4)
    (ha_lt : limbsVal as < Bignum.p25519) (hb_lt : limbsVal bs < Bignum.p25519)
    (hm : (array64 out out0 ⋆ array64 pa as ⋆ array64 pb bs ⋆ R) m) :
    Func.spec Γ Bignum.subMod25519 (out, pa, pb, ()) m
      (fun _ m' => ∃ rs : List (BitVec 64), rs.length = 4 ∧
        limbsVal rs = (if limbsVal bs ≤ limbsVal as then limbsVal as - limbsVal bs
                       else limbsVal as + Bignum.p25519 - limbsVal bs) ∧
        limbsVal rs < Bignum.p25519 ∧
        (array64 out rs ⋆ array64 pa as ⋆ array64 pb bs ⋆ R) m')
      (fun _ _ _ _ => False) :=
  Bignum.subMod25519_correct Γ (out, pa, pb, ()) m _ _
    ⟨as, bs, out0, R, has, hbs, hout, ha_lt, hb_lt, hm,
      fun rs _ hrs hsub hlt hm' => ⟨rs, hrs, hsub, hlt, hm'⟩⟩

theorem audit_bignum_mod :
    ModuleOk Bignum.bignumEnv Bignum.mul4x4Module ∧
    ModuleOk Bignum.bignumEnv Bignum.addMod25519Module ∧
    ModuleOk Bignum.bignumEnv Bignum.subMod25519Module :=
  ⟨Bignum.mul4x4_moduleOk, Bignum.addMod25519_moduleOk, Bignum.subMod25519_moduleOk⟩

/-! ## 3. Union-Find (`find`, `union`, `unionInline`) -/

theorem audit_uf_find_ir (Γ : Env) (p x : BitVec 64) (n : Nat)
    (rep : BitVec 64 → BitVec 64) (R : Mem 64 → Prop) (m : Mem 64)
    (hm : (UnionFind.uf p n rep ⋆ R) m) (hx : x.toNat < n) :
    Func.spec Γ UnionFind.find (p, x, ()) m
      (fun r m' => r = (rep x, ()) ∧ (UnionFind.uf p n rep ⋆ R) m')
      (fun _ _ _ _ => False) :=
  UnionFind.find_correct Γ (p, x, ()) m _ _ ⟨n, rep, R, hm, hx, fun _ hm' => ⟨rfl, hm'⟩⟩

theorem audit_uf_union_ir (p x y : BitVec 64) (n : Nat)
    (rep : BitVec 64 → BitVec 64) (R : Mem 64 → Prop) (m : Mem 64)
    (hm : (UnionFind.uf p n rep ⋆ R) m) (hx : x.toNat < n) (hy : y.toNat < n) :
    Func.spec UnionFind.ufEnv UnionFind.union (p, x, y, ()) m
      (fun _ m' => (UnionFind.uf p n (UnionFind.merge rep x y) ⋆ R) m')
      (fun _ _ _ _ => False) :=
  UnionFind.union_correct UnionFind.ufEnv (fun _ _ _ _ h => h) (p, x, y, ()) m _ _
    ⟨n, rep, R, hm, hx, hy, fun _ hm' => hm'⟩

theorem audit_uf_in_ir (Γ : Env) (p x y : BitVec 64) (n : Nat)
    (rep : BitVec 64 → BitVec 64) (R : Mem 64 → Prop) (m : Mem 64)
    (hm : (UnionFind.uf p n rep ⋆ R) m) (hx : x.toNat < n) (hy : y.toNat < n) :
    Func.spec Γ UnionFind.unionInline (p, x, y, ()) m
      (fun _ m' => (UnionFind.uf p n (UnionFind.merge rep x y) ⋆ R) m')
      (fun _ _ _ _ => False) :=
  UnionFind.unionInline_correct Γ (p, x, y, ()) m _ _ ⟨n, rep, R, hm, hx, hy, fun _ hm' => hm'⟩

theorem audit_uf_mod : ModuleOk UnionFind.ufEnv UnionFind.ufModule :=
  UnionFind.ufEnv_moduleOk

/-! ## 4. Concrete `#guard` Sanity Checks -/

#guard (ChaCha.rfcChaCha20Core ChaCha.rfc8439_test_init).toBytes == ChaCha.rfc8439_expected_bytes
#guard limbsVal [Bignum.p0, Bignum.p1, Bignum.p2, Bignum.p3] == Bignum.p25519
#guard UnionFind.merge id 1#64 2#64 1#64 == UnionFind.merge id 1#64 2#64 2#64
#guard UnionFind.merge id 1#64 2#64 0#64 != UnionFind.merge id 1#64 2#64 1#64

/-! ## 5. Logical Foundations Audit (`#print axioms`) -/

#print axioms audit_chacha_qr
#print axioms audit_chacha_vec
#print axioms audit_chacha_ir
#print axioms audit_chacha_rfc
#print axioms audit_chacha_mod
#print axioms audit_mul4x4_ir
#print axioms audit_add25519_ir
#print axioms audit_sub25519_ir
#print axioms audit_bignum_mod
#print axioms audit_uf_find_ir
#print axioms audit_uf_union_ir
#print axioms audit_uf_in_ir
#print axioms audit_uf_mod

end WorkloadsAuditSpec
