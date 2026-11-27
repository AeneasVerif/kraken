module

public import LeanQbe.T.Logic.C0Grind
public import LeanQbe.T.Logic.SepTree

/-!
# `C0GrindTest`: Realistic Spatial-Noise Test Suite for `c0_grind` & `c0_bv_bit_grind`

Tests modeled on real Kissat, ARiSCA, Bitblast, and XED WP goals, each carrying a 25-atom
`Mem 64` separation-logic hypothesis, a `SepTree` spatial hypothesis, and a C0/IL `wp`/`Expr`
continuation in the local context to verify fast spatial pruning and pure `std3` closure:

1. `BitVec 32 <-> 64` (`setWidth`, `signExtend`, `add`, `mul`, `shl`, `ushiftRight`, `ult`/`ule`)
   and `UInt32`/`UInt64` bounds via `c0_grind` (including `c0_grind [extra]`).
2. `List.getD` read-over-write chains across `3–8` `xs.set` mutations via `c0_grind`.
3. Kissat `pword` clause-header bitfield pack/unpack & orthogonal mask preservation (`PH_GLUE`,
   `PH_GARB`, `PH_RED`, and general `(w &&& ~~~m1) ||| (v <<< s)`) via `c0_grind`/`c0_bv_bit_grind`.
4. XED-style ModRM / SIB / REX byte bitfield packing & extraction via `c0_bv_bit_grind`.
5. `#print axioms` and `#grind_lint` confirming strict `<= std3` axioms and zero E-match loops.
-/

set_option autoImplicit false

namespace LeanQbeTest.T.C0GrindTest

open LeanQbe.T LeanQbe.T.C0Grind Std.ExtHashMap

public section

/-! ## Shared 25-Atom `Mem 64` Spatial + `wp` / `Expr` Noise Fixture -/

/-- 25-atom `Mem 64` separation-logic footprint mimicking a realistic Kissat/ARiSCA/Bitblast WP
goal context (`array64`, `array`, `cell64`, `bytes`, `region`, and nested `⋆`). -/
abbrev SpatialNoise25 (p : Fin 25 → BitVec 64) (xs : Fin 25 → List (BitVec 64))
    (ys : List (Val i32)) (v : BitVec 64) (bs : List UInt8) : Mem 64 → Prop :=
  array64 (p 0) (xs 0) ⋆ array64 (p 1) (xs 1) ⋆ array64 (p 2) (xs 2) ⋆
  array64 (p 3) (xs 3) ⋆ array64 (p 4) (xs 4) ⋆ array64 (p 5) (xs 5) ⋆
  array64 (p 6) (xs 6) ⋆ array64 (p 7) (xs 7) ⋆ array64 (p 8) (xs 8) ⋆
  array64 (p 9) (xs 9) ⋆ array64 (p 10) (xs 10) ⋆ array64 (p 11) (xs 11) ⋆
  array64 (p 12) (xs 12) ⋆ array64 (p 13) (xs 13) ⋆ array64 (p 14) (xs 14) ⋆
  array64 (p 15) (xs 15) ⋆ array64 (p 16) (xs 16) ⋆ array64 (p 17) (xs 17) ⋆
  array64 (p 18) (xs 18) ⋆ array64 (p 19) (xs 19) ⋆ array64 (p 20) (xs 20) ⋆
  cell64 (p 21) v ⋆ bytes (p 22) bs ⋆ region (p 23) 4096 ⋆ array (t := i32) (p 24) ys

abbrev PH_GLUE_MASK : BitVec 32 := 0x7FFFF#32
abbrev PH_GARB : BitVec 32 := 0x00080000#32
abbrev PH_RED : BitVec 32 := 0x00400000#32

def auxDouble (n : Nat) : Nat := n + n

theorem auxDouble_eq (n : Nat) : auxDouble n = 2 * n := by
  unfold auxDouble; omega

/-! ## 1. `BitVec 32 <-> 64` & `UInt32`/`UInt64` Arithmetic Under Spatial/AST Noise -/

theorem test_bv32_64_add_setWidth
    (m : Mem 64) (p : Fin 25 → BitVec 64) (xs : Fin 25 → List (BitVec 64))
    (ys : List (Val i32)) (v : BitVec 64) (bs : List UInt8)
    (_hmem : SpatialNoise25 p xs ys v bs m)
    (Γ : Env) (Q : Post [i64]) (X : XPost) (k : Expr Val Cont [i64]) (_hwp : wp Γ Q X k m)
    (a b : BitVec 32) (ha : a.toNat < 2 ^ 30) (hb : b.toNat < 2 ^ 30) :
    ((a + b).setWidth 64).toNat = a.toNat + b.toNat := by
  c0_grind

theorem test_bv32_64_wrap_add_mul_truncate
    (m : Mem 64) (p : Fin 25 → BitVec 64) (xs : Fin 25 → List (BitVec 64))
    (ys : List (Val i32)) (v : BitVec 64) (bs : List UInt8)
    (_hmem : SpatialNoise25 p xs ys v bs m)
    (Γ : Env) (Q : Post [i64]) (X : XPost) (k : Expr Val Cont [i64]) (_hwp : wp Γ Q X k m)
    (a b : BitVec 32) :
    ((a.setWidth 64) + (b.setWidth 64)).truncate 32 = a + b ∧
    ((a.setWidth 64) * (b.setWidth 64)).truncate 32 = a * b := by
  c0_grind

theorem test_bv32_64_signExtend_nonneg_and_neg
    (m : Mem 64) (p : Fin 25 → BitVec 64) (xs : Fin 25 → List (BitVec 64))
    (ys : List (Val i32)) (v : BitVec 64) (bs : List UInt8)
    (_hmem : SpatialNoise25 p xs ys v bs m)
    (t : SepTree) (_hsep : SepTree.eval t m)
    (a b : BitVec 32) (ha : a.toNat < 2 ^ 31) (hb : 2 ^ 31 ≤ b.toNat) :
    (a.signExtend 64).toNat = a.toNat ∧
    a.signExtend 64 = a.setWidth 64 ∧
    (b.signExtend 64).toNat = 2 ^ 64 - 2 ^ 32 + b.toNat := by
  c0_grind

theorem test_bv32_64_shl_ushiftRight_and_arena_ptr
    (m : Mem 64) (p : Fin 25 → BitVec 64) (xs : Fin 25 → List (BitVec 64))
    (ys : List (Val i32)) (v : BitVec 64) (bs : List UInt8)
    (_hmem : SpatialNoise25 p xs ys v bs m)
    (Γ : Env) (Q : Post [i64]) (X : XPost) (k : Expr Val Cont [i64]) (_hwp : wp Γ Q X k m)
    (base : BitVec 64) (cref sz : BitVec 32)
    (hcr : cref.toNat < 2 ^ 28) (hsz : sz.toNat < 2 ^ 20) :
    ((cref <<< 2#32).setWidth 64).toNat = 4 * cref.toNat ∧
    ((cref <<< 3#32).setWidth 64 >>> 3#64) = cref.setWidth 64 ∧
    base + ((cref.setWidth 64 + 3#64 + sz.setWidth 64) <<< 2) =
      base + BitVec.ofNat 64 (4 * (cref.toNat + 3 + sz.toNat)) := by
  c0_grind

theorem test_bv_ult_ule_uint_and_extra_param
    (m : Mem 64) (p : Fin 25 → BitVec 64) (xs : Fin 25 → List (BitVec 64))
    (ys : List (Val i32)) (v : BitVec 64) (bs : List UInt8)
    (_hmem : SpatialNoise25 p xs ys v bs m)
    (Γ : Env) (Q : Post [i64]) (X : XPost) (k : Expr Val Cont [i64]) (_hwp : wp Γ Q X k m)
    (a b : BitVec 64) (u : UInt32) (hult : a.ult b = true) (hule : b.ule 1000#64 = true)
    (hu : u.toNat < 1000) :
    auxDouble a.toNat < 2 * b.toNat ∧
    (u.toUInt64 + UInt64.ofNat a.toNat).toNat = u.toNat + a.toNat := by
  c0_grind [auxDouble_eq]

/-! ## 2. `List.getD` Read-Over-Write Chains Under Spatial/AST Noise -/

theorem test_list_getD_set_chain5_ne
    (m : Mem 64) (p : Fin 25 → BitVec 64) (xs : Fin 25 → List (BitVec 64))
    (ys : List (Val i32)) (v : BitVec 64) (bs : List UInt8)
    (_hmem : SpatialNoise25 p xs ys v bs m)
    (Γ : Env) (Q : Post [i64]) (X : XPost) (k : Expr Val Cont [i64]) (_hwp : wp Γ Q X k m)
    (arr : List (BitVec 32)) (i a b c d e : Nat) (v1 v2 v3 v4 v5 df : BitVec 32)
    (h1 : i ≠ a) (h2 : i ≠ b) (h3 : i ≠ c) (h4 : i ≠ d) (h5 : i ≠ e) :
    (((((arr.set a v1).set b v2).set c v3).set d v4).set e v5).getD i df = arr.getD i df := by
  c0_grind

theorem test_list_getD_set_chain4_hit
    (m : Mem 64) (p : Fin 25 → BitVec 64) (xs : Fin 25 → List (BitVec 64))
    (ys : List (Val i32)) (v : BitVec 64) (bs : List UInt8)
    (_hmem : SpatialNoise25 p xs ys v bs m)
    (Γ : Env) (Q : Post [i64]) (X : XPost) (k : Expr Val Cont [i64]) (_hwp : wp Γ Q X k m)
    (arr : List (BitVec 32)) (a b c d : Nat) (v1 v2 v3 v4 df : BitVec 32)
    (ha : a < arr.length) (h2 : a ≠ b) (h3 : a ≠ c) (h4 : a ≠ d) :
    ((((arr.set a v1).set b v2).set c v3).set d v4).getD a df = v1 := by
  c0_grind

theorem test_list_getD_set_chain3_bv32_indices
    (m : Mem 64) (p : Fin 25 → BitVec 64) (xs : Fin 25 → List (BitVec 64))
    (ys : List (Val i32)) (v : BitVec 64) (bs : List UInt8)
    (_hmem : SpatialNoise25 p xs ys v bs m)
    (arr : List (BitVec 32)) (idx q : BitVec 32) (v1 v2 v3 df : BitVec 32)
    (hlen : arr.length ≤ 2 ^ 32) (h1 : idx.toNat + 3 < arr.length)
    (hq0 : q.toNat ≠ idx.toNat) (hq1 : q.toNat ≠ idx.toNat + 1)
    (hq2 : q.toNat ≠ idx.toNat + 2) :
    let arr' := ((arr.set idx.toNat v1).set (idx + 1#32).toNat v2).set (idx + 2#32).toNat v3
    arr'.length = arr.length ∧
    arr'.getD (idx + 1#32).toNat df = v2 ∧
    arr'.getD q.toNat df = arr.getD q.toNat df := by
  c0_grind

theorem test_list_getD_getElem_and_oob
    (m : Mem 64) (p : Fin 25 → BitVec 64) (xs : Fin 25 → List (BitVec 64))
    (ys : List (Val i32)) (v : BitVec 64) (bs : List UInt8)
    (_hmem : SpatialNoise25 p xs ys v bs m)
    (arr : List (BitVec 32)) (i j k : Nat) (v1 df : BitVec 32)
    (hi : i < arr.length) (hne : i ≠ j) (hk : arr.length ≤ k) :
    (arr.set j v1).getD i df = arr[i]'hi ∧ arr.getD k df = df := by
  c0_grind

theorem test_list_getD_getElem_and_chain8
    (m : Mem 64) (p : Fin 25 → BitVec 64) (xs : Fin 25 → List (BitVec 64))
    (ys : List (Val i32)) (v : BitVec 64) (bs : List UInt8)
    (_hmem : SpatialNoise25 p xs ys v bs m)
    (arr : List (BitVec 32)) (i a1 a2 a3 a4 a5 a6 a7 a8 : Nat)
    (v1 v2 v3 v4 v5 v6 v7 v8 df : BitVec 32) (hi : i < arr.length)
    (h1 : i ≠ a1) (h2 : i ≠ a2) (h3 : i ≠ a3) (h4 : i ≠ a4)
    (h5 : i ≠ a5) (h6 : i ≠ a6) (h7 : i ≠ a7) (h8 : i ≠ a8) :
    ((((((((arr.set a1 v1).set a2 v2).set a3 v3).set a4 v4).set a5 v5).set a6 v6).set a7 v7).set
      a8 v8).getD i df = arr[i]'hi := by
  c0_grind (gen := 10) (ematch := 10)

/-! ## 3. Kissat `pword` & Clause-Header Bitfield Pack/Unpack & Orthogonality -/

theorem test_kissat_hdr_glue_pack_unpack
    (m : Mem 64) (p : Fin 25 → BitVec 64) (xs : Fin 25 → List (BitVec 64))
    (ys : List (Val i32)) (v : BitVec 64) (bs : List UInt8)
    (_hmem : SpatialNoise25 p xs ys v bs m)
    (Γ : Env) (Q : Post [i64]) (X : XPost) (k : Expr Val Cont [i64]) (_hwp : wp Γ Q X k m)
    (w g : BitVec 32) (hg : g.toNat < 2 ^ 19) :
    (((w &&& ~~~PH_GLUE_MASK) ||| g) &&& PH_GLUE_MASK) = g := by
  c0_bv_bit_grind

theorem test_kissat_hdr_glue_preserves_garb_and_red
    (m : Mem 64) (p : Fin 25 → BitVec 64) (xs : Fin 25 → List (BitVec 64))
    (ys : List (Val i32)) (v : BitVec 64) (bs : List UInt8)
    (_hmem : SpatialNoise25 p xs ys v bs m)
    (Γ : Env) (Q : Post [i64]) (X : XPost) (k : Expr Val Cont [i64]) (_hwp : wp Γ Q X k m)
    (w g : BitVec 32) (hg : g.toNat < 2 ^ 19) :
    (((w &&& ~~~PH_GLUE_MASK) ||| g) &&& PH_GARB) = (w &&& PH_GARB) ∧
    (((w &&& ~~~PH_GLUE_MASK) ||| g) &&& PH_RED) = (w &&& PH_RED) := by
  constructor <;> c0_bv_bit_grind

theorem test_kissat_hdr_mark_garb_clear_red_orthog
    (m : Mem 64) (p : Fin 25 → BitVec 64) (xs : Fin 25 → List (BitVec 64))
    (ys : List (Val i32)) (v : BitVec 64) (bs : List UInt8)
    (_hmem : SpatialNoise25 p xs ys v bs m)
    (w : BitVec 32) :
    ((w ||| PH_GARB) &&& PH_RED) = (w &&& PH_RED) ∧
    ((w ||| PH_GARB) &&& PH_GLUE_MASK) = (w &&& PH_GLUE_MASK) ∧
    ((w &&& ~~~PH_RED) &&& PH_GARB) = (w &&& PH_GARB) ∧
    ((w &&& ~~~PH_RED) &&& PH_GLUE_MASK) = (w &&& PH_GLUE_MASK) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> c0_bv_bit_grind

theorem test_kissat_hdr_glue_bound_c0_grind
    (m : Mem 64) (p : Fin 25 → BitVec 64) (xs : Fin 25 → List (BitVec 64))
    (ys : List (Val i32)) (v : BitVec 64) (bs : List UInt8)
    (_hmem : SpatialNoise25 p xs ys v bs m)
    (hdr : BitVec 32) :
    ((hdr &&& PH_GLUE_MASK).setWidth 64).toNat < 2 ^ 19 := by
  c0_grind

theorem test_pword_symbolic_shift_and_orthogonal_mask
    (m : Mem 64) (p : Fin 25 → BitVec 64) (xs : Fin 25 → List (BitVec 64))
    (ys : List (Val i32)) (v : BitVec 64) (bs : List UInt8)
    (_hmem : SpatialNoise25 p xs ys v bs m)
    (w val m1 m2 : BitVec 32) (s : Nat)
    (hdisj : (m1 &&& m2) = 0#32) (hsub : ((val <<< s) &&& m1) = (val <<< s)) :
    (((w &&& ~~~m1) ||| (val <<< s)) &&& m2) = (w &&& m2) := by
  c0_bv_bit_grind

theorem test_pword64_shifted_field_pack_unpack
    (m : Mem 64) (p : Fin 25 → BitVec 64) (xs : Fin 25 → List (BitVec 64))
    (ys : List (Val i32)) (v : BitVec 64) (bs : List UInt8)
    (_hmem : SpatialNoise25 p xs ys v bs m)
    (w tag : BitVec 64) (htag : tag.toNat < 2 ^ 16) :
    let mask : BitVec 64 := 0xFFFF#64 <<< 48
    let w' := (w &&& ~~~mask) ||| (tag <<< 48)
    (w' >>> 48) = tag ∧ (w' &&& 0x0000FFFFFFFFFFFF#64) = (w &&& 0x0000FFFFFFFFFFFF#64) := by
  intro mask w'
  constructor <;> c0_bv_bit_grind

/-! ## 4. XED-Style ModRM / SIB / REX Byte Bitfields -/

theorem test_xed_modrm_pack_unpack_and_update
    (m : Mem 64) (p : Fin 25 → BitVec 64) (xs : Fin 25 → List (BitVec 64))
    (ys : List (Val i32)) (v : BitVec 64) (bs : List UInt8)
    (_hmem : SpatialNoise25 p xs ys v bs m)
    (Γ : Env) (Q : Post [i64]) (X : XPost) (k : Expr Val Cont [i64]) (_hwp : wp Γ Q X k m)
    (md reg rm reg' : BitVec 8)
    (hmd : md.toNat < 4) (hreg : reg.toNat < 8) (hrm : rm.toNat < 8) (hreg' : reg' < 8#8) :
    let byte := (md <<< 6) ||| (reg <<< 3) ||| rm
    let byte' := (byte &&& ~~~0x38#8) ||| (reg' <<< 3)
    (byte >>> 6) = md ∧
    ((byte >>> 3) &&& 7#8) = reg ∧
    (byte &&& 7#8) = rm ∧
    (byte' >>> 6) = md ∧
    ((byte' >>> 3) &&& 7#8) = reg' ∧
    (byte' &&& 7#8) = rm := by
  intro byte byte'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> c0_bv_bit_grind

theorem test_xed_sib_pack_unpack
    (m : Mem 64) (p : Fin 25 → BitVec 64) (xs : Fin 25 → List (BitVec 64))
    (ys : List (Val i32)) (v : BitVec 64) (bs : List UInt8)
    (_hmem : SpatialNoise25 p xs ys v bs m)
    (scale idx base : BitVec 8)
    (hs : scale.toNat < 4) (hi : idx.toNat < 8) (hb : base.toNat < 8) :
    let sib := (scale <<< 6) ||| (idx <<< 3) ||| base
    ((sib &&& 0xC0#8) >>> 6) = scale ∧
    ((sib &&& 0x38#8) >>> 3) = idx ∧
    (sib &&& 0x07#8) = base := by
  intro sib
  refine ⟨?_, ?_, ?_⟩ <;> c0_bv_bit_grind

theorem test_kissat_hdr_raw_noncontig_mask
    (m : Mem 64) (p : Fin 25 → BitVec 64) (xs : Fin 25 → List (BitVec 64))
    (ys : List (Val i32)) (v : BitVec 64) (bs : List UInt8)
    (_hmem : SpatialNoise25 p xs ys v bs m)
    (w g : BitVec 32) (hg : g.toNat < 2 ^ 19) :
    (((w &&& 0xFFF80000#32) ||| g) &&& 0x00480000#32) = (w &&& 0x00480000#32) := by
  c0_bv_bit_grind

theorem test_xed_rex_byte_pack_unpack
    (m : Mem 64) (p : Fin 25 → BitVec 64) (xs : Fin 25 → List (BitVec 64))
    (ys : List (Val i32)) (v : BitVec 64) (bs : List UInt8)
    (_hmem : SpatialNoise25 p xs ys v bs m)
    (W R X B : BitVec 8)
    (hW : W.toNat < 2) (hR : R.toNat < 2) (hX : X.toNat < 2) (hB : B.toNat < 2) :
    let rex := 0x40#8 ||| (W <<< 3) ||| (R <<< 2) ||| (X <<< 1) ||| B
    (rex >>> 4) = 4#8 ∧
    ((rex >>> 3) &&& 1#8) = W ∧
    ((rex >>> 2) &&& 1#8) = R ∧
    ((rex >>> 1) &&& 1#8) = X ∧
    (rex &&& 1#8) = B := by
  intro rex
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> c0_bv_bit_grind

abbrev BvEq32 (a b : BitVec 32) : Prop := a = b

theorem test_c0_bv_bit_grind_after_have_let_and_abbrev_eq
    (m : Mem 64) (p : Fin 25 → BitVec 64) (xs : Fin 25 → List (BitVec 64))
    (ys : List (Val i32)) (v : BitVec 64) (bs : List UInt8)
    (_hmem : SpatialNoise25 p xs ys v bs m)
    (w g : BitVec 32) (hg : g.toNat < 2 ^ 19) :
    BvEq32 (((w &&& 0xFFF80000#32) ||| g) &&& 0x00480000#32) (w &&& 0x00480000#32) := by
  have _hg2 : g.toNat < 2 ^ 20 := by omega
  let _dummy : Nat := 1
  c0_bv_bit_grind

theorem test_c0_bv_bit_grind_unintrod_let_and_abbrev_hyp
    (m : Mem 64) (p : Fin 25 → BitVec 64) (xs : Fin 25 → List (BitVec 64))
    (ys : List (Val i32)) (v : BitVec 64) (bs : List UInt8)
    (_hmem : SpatialNoise25 p xs ys v bs m)
    (w val m1 m2 : BitVec 32) (hdisj : BvEq32 (m1 &&& m2) 0#32) (hsub : BvEq32 (val &&& m1) val) :
    let w' := (w &&& ~~~m1) ||| val
    (w' &&& m2) = (w &&& m2) := by
  c0_bv_bit_grind

theorem test_uint8_16_32_64_bit_grind
    (m : Mem 64) (p : Fin 25 → BitVec 64) (xs : Fin 25 → List (BitVec 64))
    (ys : List (Val i32)) (v : BitVec 64) (bs : List UInt8)
    (_hmem : SpatialNoise25 p xs ys v bs m)
    (w16 : UInt16) (w32 : UInt32) (md reg rm : UInt8)
    (hmd : md.toNat < 4) (hreg : reg.toNat < 8) (hrm : rm.toNat < 8) :
    ((((w32 &&& 0xFF) ||| 0x0100) &&& 0xFF00) : UInt32) = 0x0100 ∧
    ((((w16 &&& 0xFF) ||| 0x0100) &&& 0xFF00) : UInt16) = 0x0100 ∧
    ((((md <<< 6) ||| (reg <<< 3) ||| rm) >>> 6) : UInt8) = md := by
  refine ⟨?_, ?_, ?_⟩ <;> c0_bv_bit_grind

def DEF_PH_GARB : BitVec 32 := 0x00080000#32

theorem test_c0_bv_bit_grind_def_mask_huge_shift_and_extract
    (m : Mem 64) (p : Fin 25 → BitVec 64) (xs : Fin 25 → List (BitVec 64))
    (ys : List (Val i32)) (v : BitVec 64) (bs : List UInt8)
    (_hmem : SpatialNoise25 p xs ys v bs m)
    (w g : BitVec 32) (hg : g.toNat < 2 ^ 19) (md reg rm : BitVec 8)
    (hrm : rm.toNat < 8) :
    (((w &&& ~~~PH_GLUE_MASK) ||| g) &&& DEF_PH_GARB) = (w &&& DEF_PH_GARB) ∧
    (w &&& (1#32 <<< 10000000)) = 0#32 ∧
    (w &&& (0xFFFF#32 >>> 10000000)) = 0#32 ∧
    BitVec.extractLsb 5 3 ((md <<< 6) ||| (reg <<< 3) ||| rm) = reg.truncate 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> c0_bv_bit_grind

/-! ## 5. Strict `<= std3` Axiom & E-Match Lint Checks -/

#grind_lint check in LeanQbe.T.C0Grind

#print axioms test_c0_bv_bit_grind_after_have_let_and_abbrev_eq
#print axioms test_c0_bv_bit_grind_unintrod_let_and_abbrev_hyp
#print axioms test_uint8_16_32_64_bit_grind
#print axioms test_c0_bv_bit_grind_def_mask_huge_shift_and_extract

#print axioms test_bv32_64_add_setWidth
#print axioms test_bv32_64_wrap_add_mul_truncate
#print axioms test_bv32_64_signExtend_nonneg_and_neg
#print axioms test_bv32_64_shl_ushiftRight_and_arena_ptr
#print axioms test_bv_ult_ule_uint_and_extra_param
#print axioms test_list_getD_set_chain5_ne
#print axioms test_list_getD_set_chain4_hit
#print axioms test_list_getD_set_chain3_bv32_indices
#print axioms test_list_getD_getElem_and_oob
#print axioms test_list_getD_getElem_and_chain8
#print axioms test_kissat_hdr_glue_pack_unpack
#print axioms test_kissat_hdr_glue_preserves_garb_and_red
#print axioms test_kissat_hdr_mark_garb_clear_red_orthog
#print axioms test_kissat_hdr_glue_bound_c0_grind
#print axioms test_kissat_hdr_raw_noncontig_mask
#print axioms test_pword_symbolic_shift_and_orthogonal_mask
#print axioms test_pword64_shifted_field_pack_unpack
#print axioms test_xed_modrm_pack_unpack_and_update
#print axioms test_xed_sib_pack_unpack
#print axioms test_xed_rex_byte_pack_unpack

end

end LeanQbeTest.T.C0GrindTest
