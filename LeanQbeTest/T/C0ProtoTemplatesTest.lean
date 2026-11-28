module

public import LeanQbe.T.Frontend.C0.Template.Snippet
public import LeanQbe.T.Frontend.C0.Template.Wp
public import LeanQbe.T.Frontend.C0.Template.Elab
public meta import LeanQbe.T.Frontend.C0.Template.Elab
public import LeanQbe.T.Flat
public meta import LeanQbe.T.Flat
import LeanQbe.T.FlatLemmas
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe

/-!
# Prototype Tests & Parametric WP Proofs for Static PHOAS C0 Templates

Exercises C0 Extension 6 (`c0_fn_template!`, `c0_expr_template!`, `c0_stmt_template!`):
1. Value splices: `BitVec w`, `BitVec 64`, `Nat` (e.g. `(bv$(w))$(n)`), `Bool`
2. Type/width splices: `bv$(w)` / `u$(w)` / `sbv$(w)` / `i$(w)` (concrete + symbolic `w`), `ty$(t)`
3. Code/operator splices: `OpCode`, `CmpOp`, `C0ExprSnippet`, `funcToExprSnippet`,
   `C0StmtSnippet`, and `#unroll (x in $(xs : List α)) { ... }`
4. Parametric WP theorems proved ONCE (axioms `<= std3`) across widths/ops/constants/lists,
   concrete `Fn.Wf` (`t_wf_reify`), QBE/C++ printing, and concrete compilation inputs shared with
   `C0ProtoTemplatesX64Test` and `C0ProtoTemplatesArm64Test` (`Kraken.X64` and `Kraken.AArch64`
   cannot be imported into the same Lean environment due to `instToExprCondCode` collision).

## Candid Prototype Boundaries Observed
* Dependent casts/indices at symbolic width `w`: `(bv$(w))$(n)` works via `BitVec.ofNat w n`,
  and `(bv$(w))0` emits `0#w`; however `*(bv$(w)*)(base + i * $(stride) + $(off))` requires
  an explicit byte `$(stride)` because `Layout.typeSizeAlign` sees a dummy placeholder bitwidth
  (`1000000 + 8 * idx`), so symbolic `arr[i]` and `sizeof(bv$(w))` are rejected statically.
* Non-zero C integer literals at symbolic `bv$(w)` cannot be synthesized without a known width;
  users must pass `$(k : BitVec w)` or `(bv$(w))$(n : Nat)`.
* Opaque `ty$(t)` supports parameters, loads/stores, copies, and `$(op)` / `$(snip)`, but rejects
  numeric literals and built-in C0 `<` / `==` (whose `.cmp` proof `t.mask = .bool` fails when
  `t` is opaque).
* `c0_stmt_template!` and `#unroll` abstract local state explicitly via `Tup V ts` / `c0UnrollK`
  and reject non-local control exits (`return`, `break`, `continue`, `goto`).
* Concrete instances of `c0_fn_template!` elaborate directly to PHOAS `Func`/`Fn` ASTs without
  raw `kissat_c0!` C string literals, so `bench/kissat/extract_c0_direct.py` does not extract them;
  they still pretty-print via `PrintQbe` and `PrintCpp`.
-/

set_option autoImplicit false

namespace LeanQbeTest.T.C0ProtoTemplatesTest

open LeanQbe.T
open LeanQbe.T.Frontend.C0

public section

/-! ## 1. Splice Coverage & Template Definitions -/

/-- Value + cast + boolean + unsigned/signed width splices. -/
@[expose] def valAndCastTpl :
    (w : Nat) → Nat → Bool → BitVec 64 → Func [.bits 64, .bits w] [.bits w] :=
  c0_fn_template! (w : Nat) (n : Nat) (b : Bool) (off : BitVec 64) => "
    u$(w) val_cast_demo(u64 base, sbv$(w) x) {
      i$(w) bias = (bv$(w))$(n);
      u$(w) loaded = *((u$(w)*)(base + $(off)));
      if ($(b)) {
        return x + bias;
      } else {
        return loaded ^ x;
      }
    }
  "

/-- Type-opaque `ty$(t)` parameter/memory swap template. -/
@[expose] def opaqueSwapTpl : (t : Ty) → BitVec 64 → Func [.bits 64, t] [t] :=
  c0_fn_template! (t : Ty) (off : BitVec 64) => "
    ty$(t) opaque_swap(u64 ptr, ty$(t) v) {
      ty$(t) old = *((ty$(t)*)(ptr + $(off)));
      *((ty$(t)*)(ptr + $(off))) = v;
      return old;
    }
  "

/-- Inline comparator snippet (`c0_expr_template!`). -/
@[expose] def cmpXorZeroSnip :
    (w : Nat) → BitVec w → C0ExprSnippet [.bits w, .bits w] .bool :=
  c0_expr_template! (w : Nat) (mask : BitVec w) => "
    bool cmp_xor_zero(bv$(w) a, bv$(w) b) {
      bv$(w) z = (bv$(w))0;
      return ((a ^ b) & $(mask)) == z;
    }
  "

/-- Statement snippet (`c0_stmt_template!`) parameterized by width, `OpCode`, and salt. -/
@[expose] def addSaltStmtSnip :
    (w : Nat) → OpCode [.bits w, .bits w] [.bits w] → BitVec w →
    C0StmtSnippet [.bits w, .bits w] :=
  c0_stmt_template! (w : Nat) (op : OpCode [.bits w, .bits w] [.bits w]) (salt : BitVec w) => "
    void step(bv$(w) acc, bv$(w) x) {
      acc = $(op)(acc, x ^ $(salt));
    }
  "

/-- Standalone `c0_fn_template!` comparator bridged via `funcToExprSnippet`. -/
@[expose] def ltFnCmp : (w : Nat) → Func [.bits w, .bits w] [.bool] :=
  c0_fn_template! (w : Nat) => "
    bool lt_fn(bv$(w) a, bv$(w) b) {
      return a < b;
    }
  "

/-- Template invoking a `C0StmtSnippet` as a statement call. -/
@[expose] def stmtCallerTpl :
    (w : Nat) → OpCode [.bits w, .bits w] [.bits w] → BitVec w →
    Func [.bits w, .bits w] [.bits w] :=
  c0_fn_template! (w : Nat) (op : OpCode [.bits w, .bits w] [.bits w]) (salt : BitVec w) => "
    bv$(w) call_stmt_snip(bv$(w) acc, bv$(w) x) {
      $(addSaltStmtSnip w op salt)(acc, x);
      return acc;
    }
  "

/-- Generic `find_if` kernel parameterized by width `w`, comparator `cmp`, `target`, byte `stride`,
and byte offset `off`. -/
@[expose] def findIfKernel :
    (w : Nat) → CmpOp → BitVec w → BitVec 64 → BitVec 64 →
    Func [.bits 64, .bits 64] [.bits 64] :=
  c0_fn_template! (w : Nat) (cmp : CmpOp) (target : BitVec w)
      (stride : BitVec 64) (off : BitVec 64) => "
    u64 find_if(u64 base, u64 len) {
      u64 i = 0;
      while (i < len) {
        bv$(w) elem = *((bv$(w)*)(base + i * $(stride) + $(off)));
        if ($(cmp)(elem, $(target))) {
          return i;
        }
        i = i + 1;
      }
      return len;
    }
  "

/-- Generic `find_if` kernel parameterized by an arbitrary `C0ExprSnippet` predicate. -/
@[expose] def findIfSnippetKernel :
    (w : Nat) → C0ExprSnippet [.bits w, .bits w] .bool → BitVec w → BitVec 64 → BitVec 64 →
    Func [.bits 64, .bits 64] [.bits 64] :=
  c0_fn_template! (w : Nat) (pred : C0ExprSnippet [.bits w, .bits w] .bool)
      (target : BitVec w) (stride : BitVec 64) (off : BitVec 64) => "
    u64 find_if_snip(u64 base, u64 len) {
      u64 i = 0;
      while (i < len) {
        bv$(w) elem = *((bv$(w)*)(base + i * $(stride) + $(off)));
        if ($(pred)(elem, $(target))) {
          return i;
        }
        i = i + 1;
      }
      return len;
    }
  "

/-- Generic masked array fold kernel parameterized by width `w`, binary `OpCode`, `init`, `mask`,
byte `stride`, and byte offset `off`. -/
@[expose] def foldMaskedKernel :
    (w : Nat) → OpCode [.bits w, .bits w] [.bits w] → BitVec w → BitVec w →
    BitVec 64 → BitVec 64 → Func [.bits 64, .bits 64] [.bits w] :=
  c0_fn_template! (w : Nat) (op : OpCode [.bits w, .bits w] [.bits w])
      (init : BitVec w) (mask : BitVec w) (stride : BitVec 64) (off : BitVec 64) => "
    bv$(w) fold_masked(u64 base, u64 len) {
      bv$(w) acc = $(init);
      u64 i = 0;
      while (i < len) {
        bv$(w) elem = *((bv$(w)*)(base + i * $(stride) + $(off)));
        bv$(w) masked = elem & $(mask);
        acc = $(op)(acc, masked);
        i = i + 1;
      }
      return acc;
    }
  "

/-- Static `#unroll` mix kernel parameterized by width `w`, arbitrary Lean `List (BitVec w)`,
binary `OpCode`, and `salt`. -/
@[expose] def unrollMixKernel :
    (w : Nat) → List (BitVec w) → OpCode [.bits w, .bits w] [.bits w] → BitVec w →
    Func [.bits w] [.bits w] :=
  c0_fn_template! (w : Nat) (ks : List (BitVec w))
      (op : OpCode [.bits w, .bits w] [.bits w]) (salt : BitVec w) => "
    bv$(w) unroll_mix(bv$(w) acc) {
      #unroll (k in $(ks : List (BitVec w))) {
        acc = $(op)(acc, $(k) ^ $(salt));
      }
      return acc;
    }
  "

/-- Concrete instantiations (`w = 32`, `w = 64`) for `Fn.Wf`, printing, and backend tests. -/
@[expose] def findEq32 : Func [.bits 64, .bits 64] [.bits 64] :=
  findIfKernel 32 .eq 42#32 4#64 0#64

@[expose] def findUlt64 : Func [.bits 64, .bits 64] [.bits 64] :=
  findIfKernel 64 .ult 100#64 8#64 16#64

@[expose] def foldXor32 : Func [.bits 64, .bits 64] [.bits 32] :=
  foldMaskedKernel 32 (.xor (.bits 32)) 0#32 0xff#32 4#64 0#64

@[expose] def foldAdd64 : Func [.bits 64, .bits 64] [.bits 64] :=
  foldMaskedKernel 64 (.add (.bits 64)) 1#64 0xffffffff#64 8#64 0#64

@[expose] def unrollAdd32 : Func [.bits 32] [.bits 32] :=
  unrollMixKernel 32 [1#32, 3#32, 7#32] (.add (.bits 32)) 0xa5#32

@[expose] def findXorZeroSnip64 : Func [.bits 64, .bits 64] [.bits 64] :=
  findIfSnippetKernel 64 (cmpXorZeroSnip 64 0xff#64) 0x11#64 8#64 0#64

@[expose] def findLtFnSnip32 : Func [.bits 64, .bits 64] [.bits 64] :=
  findIfSnippetKernel 32 (funcToExprSnippet (ltFnCmp 32)) 10#32 4#64 0#64

@[expose] def concreteTFlatFns : List TFlatFn :=
  [ ⟨"find_eq32", [.bits 64, .bits 64], [.bits 64], reifyFunc findEq32⟩
  , ⟨"find_ult64", [.bits 64, .bits 64], [.bits 64], reifyFunc findUlt64⟩
  , ⟨"fold_xor32", [.bits 64, .bits 64], [.bits 32], reifyFunc foldXor32⟩
  , ⟨"fold_add64", [.bits 64, .bits 64], [.bits 64], reifyFunc foldAdd64⟩
  , ⟨"unroll_add32", [.bits 32], [.bits 32], reifyFunc unrollAdd32⟩
  , ⟨"find_xor_zero_snip64", [.bits 64, .bits 64], [.bits 64], reifyFunc findXorZeroSnip64⟩
  , ⟨"find_lt_fn_snip32", [.bits 64, .bits 64], [.bits 64], reifyFunc findLtFnSnip32⟩ ]

@[expose] def concreteFns : List Fn := concreteTFlatFns.map TFlatFn.toFn

end

public section

/-! ## 2. Specifications & Parametric WP Theorems (Proved ONCE) -/

/-- Specification helper for `find_if`: first index in `[idx, idx + fuel)` within `[0, len)`
satisfying `p`, else `len`. -/
def firstMatchFrom {α : Type} (p : α → Bool) (xs : Nat → α) (len : Nat) :
    Nat → Nat → BitVec 64
  | 0, _ => BitVec.ofNat 64 len
  | fuel + 1, idx =>
    if idx < len then
      if p (xs idx) then BitVec.ofNat 64 idx
      else firstMatchFrom p xs len fuel (idx + 1)
    else BitVec.ofNat 64 len

/-- Specification helper for `fold_masked`: folds `f` over masked elements from `idx`. -/
def foldSpec {w : Nat} (f : BitVec w → BitVec w → BitVec w) (mask : BitVec w)
    (xs : Nat → BitVec w) (init : BitVec w) : Nat → Nat → BitVec w
  | 0, _ => init
  | fuel + 1, idx => foldSpec f mask xs (f init (xs idx &&& mask)) fuel (idx + 1)

/-- Total array-memory view matching C0 element loads at `(base + idx * stride + off)`. -/
def MemArray (m : Mem 64) (w : Nat) (base len stride off : BitVec 64)
    (xs : Nat → BitVec w) : Prop :=
  ∀ k : Nat, k < len.toNat →
    loadVal m (.bits w) (base + BitVec.ofNat 64 k * stride + off) = some (xs k)

/-- Parametric WP Theorem 1 (proved ONCE): `findIfKernel` finds the first element matching `cmp`
against `target`, or returns `len` if none match, for all widths `w`, `cmp`, `target`, `stride`,
and `off`. -/
theorem findIfKernel_wp (Γ : Env) (m : Mem 64) (X : XPost)
    (w : Nat) (cmp : CmpOp) (target : BitVec w) (stride off base len : BitVec 64)
    (xs : Nat → BitVec w)
    (hmem : MemArray m w base len stride off xs) :
    Func.wp Γ (findIfKernel w cmp target stride off) (base, len, ()) m
      (fun (r, ()) m' =>
        m' = m ∧ r = firstMatchFrom (fun v => cmp.evalBits v target) xs len.toNat len.toNat 0)
      X := by
  have hsext32 : ∀ (v : Val (.bits 32)) k,
      OpCode.wp (.sext 32 64) (v, ()) k ↔ (32 ≤ 64 ∧ k (v.signExtend 64, ())) := fun _ _ => Iff.rfl
  have hult64 : ∀ (a b : Val (.bits 64)) k,
      OpCode.wp (.cmp .ult i64 .bool rfl) (a, b, ()) k ↔ k (a.ult b, ()) := fun _ _ _ => Iff.rfl
  have hmul64 : ∀ (a b : Val (.bits 64)) k,
      OpCode.wp (.mul i64) (a, b, ()) k ↔ k (a * b, ()) := fun _ _ _ => Iff.rfl
  have hadd64 : ∀ (a b : Val (.bits 64)) k,
      OpCode.wp (.add i64) (a, b, ()) k ↔ k (a + b, ()) := fun _ _ _ => Iff.rfl
  have hcmpw : ∀ (a b : Val (.bits w)) k,
      OpCode.wp (.cmp cmp (.bits w) .bool rfl) (a, b, ()) k ↔ k (cmp.evalBits a b, ()) :=
    fun _ _ _ => Iff.rfl
  dsimp only [findIfKernel, Func.wp]
  simp only [wp, Op.wp, vals, Arg.val]
  rw [hsext32]
  refine ⟨by decide, ?_⟩
  intro js hclosed
  let spec := firstMatchFrom (fun v => cmp.evalBits v target) xs len.toNat len.toNat 0
  have hstep : ∀ (rem : Nat) (i : BitVec 64),
      i.toNat ≤ len.toNat → rem = len.toNat - i.toNat →
      firstMatchFrom (fun v => cmp.evalBits v target) xs len.toNat rem i.toNat = spec →
      js.1 (i, ()) m := by
    intro rem
    induction rem with
    | zero =>
      intro i hi hrem hspec
      have hge : len.toNat ≤ i.toNat := by omega
      have hult : i.ult len = false := by
        simp [BitVec.ult]; omega
      apply hclosed.1 (i, ()) m
      dsimp only
      simp only [wp, Op.wp, vals, Arg.val]
      rw [hult64]
      refine ⟨fun htrue => absurd htrue (by rw [hult]; decide), fun _ => ?_⟩
      refine ⟨trivial, ?_⟩
      dsimp only [firstMatchFrom] at hspec
      simpa [BitVec.ofNat_toNat] using hspec
    | succ rem' ih =>
      intro i hi hrem hspec
      have hlt : i.toNat < len.toNat := by omega
      have hult : i.ult len = true := by
        simp [BitVec.ult]; exact hlt
      have hload := hmem i.toNat hlt
      have hpow : len.toNat < 2 ^ 64 := len.isLt
      have hinc : (i + 1#64).toNat = i.toNat + 1 := by
        rw [BitVec.toNat_add]
        simp [Nat.mod_eq_of_lt (by omega : i.toNat + 1 < 2 ^ 64)]
      apply hclosed.1 (i, ()) m
      dsimp only
      simp only [wp, Op.wp, vals, Arg.val]
      rw [hult64]
      refine ⟨fun _ => ?_, fun hfalse => absurd hfalse (by rw [hult]; decide)⟩
      rw [hmul64, hadd64, hadd64]
      have haddr : base + i * stride + off =
          base + BitVec.ofNat 64 i.toNat * stride + off := by
        simp [BitVec.ofNat_toNat]
      rw [haddr]
      refine ⟨xs i.toNat, hload, ?_⟩
      rw [hcmpw]
      by_cases hmatch : cmp.evalBits (xs i.toNat) target = true
      · refine ⟨fun _ => ⟨trivial, ?_⟩, fun hf => absurd hmatch (by dsimp only at hf; simp [hf])⟩
        dsimp only [firstMatchFrom] at hspec
        simp only [hlt, hmatch, ↓reduceIte] at hspec
        simpa [BitVec.ofNat_toNat] using hspec
      · refine ⟨fun ht => absurd ht hmatch, fun _ => ?_⟩
        rw [hsext32]
        refine ⟨by decide, ?_⟩
        rw [hadd64]
        have hb : cmp.evalBits (xs i.toNat) target = false := by
          cases hb0 : cmp.evalBits (xs i.toNat) target <;> simp_all
        dsimp only [firstMatchFrom] at hspec
        simp only [hlt, hb, Bool.false_eq_true, ↓reduceIte] at hspec
        rw [← hinc] at hspec
        rw [show BitVec.signExtend 64 (1 : Val (.bits 32)) = 1#64 by decide]
        exact ih (i + 1#64) (by omega) (by omega) hspec
  rw [show BitVec.signExtend 64 (0 : Val (.bits 32)) = 0#64 by decide]
  exact hstep len.toNat 0#64 (Nat.zero_le _) (by simp) rfl

/-- Parametric WP Theorem 2 (proved ONCE): `foldMaskedKernel` folds any binary `OpCode` `op`
satisfying `hop` over masked elements `(xs k &&& mask)` for all widths `w`, ops, constants `init`
and `mask`, byte `stride`, and offset `off`. -/
theorem foldMaskedKernel_wp (Γ : Env) (m : Mem 64) (X : XPost)
    (w : Nat) (op : OpCode [.bits w, .bits w] [.bits w])
    (f : BitVec w → BitVec w → BitVec w)
    (hop : ∀ (a b : BitVec w) (p : Tup Val [.bits w] → Prop),
      OpCode.wp op (a, b, ()) p ↔ p (f a b, ()))
    (init mask : BitVec w) (stride off base len : BitVec 64)
    (xs : Nat → BitVec w)
    (hmem : MemArray m w base len stride off xs) :
    Func.wp Γ (foldMaskedKernel w op init mask stride off) (base, len, ()) m
      (fun (r, ()) m' => m' = m ∧ r = foldSpec f mask xs init len.toNat 0)
      X := by
  have hsext32 : ∀ (v : Val (.bits 32)) k,
      OpCode.wp (.sext 32 64) (v, ()) k ↔ (32 ≤ 64 ∧ k (v.signExtend 64, ())) := fun _ _ => Iff.rfl
  have hult64 : ∀ (a b : Val (.bits 64)) k,
      OpCode.wp (.cmp .ult i64 .bool rfl) (a, b, ()) k ↔ k (a.ult b, ()) := fun _ _ _ => Iff.rfl
  have hmul64 : ∀ (a b : Val (.bits 64)) k,
      OpCode.wp (.mul i64) (a, b, ()) k ↔ k (a * b, ()) := fun _ _ _ => Iff.rfl
  have hadd64 : ∀ (a b : Val (.bits 64)) k,
      OpCode.wp (.add i64) (a, b, ()) k ↔ k (a + b, ()) := fun _ _ _ => Iff.rfl
  have handw : ∀ (a b : Val (.bits w)) k,
      OpCode.wp (.and (.bits w)) (a, b, ()) k ↔ k (a &&& b, ()) := fun _ _ _ => Iff.rfl
  dsimp only [foldMaskedKernel, Func.wp]
  simp only [wp, Op.wp, vals, Arg.val]
  rw [hsext32]
  refine ⟨by decide, ?_⟩
  intro js hclosed
  let spec := foldSpec f mask xs init len.toNat 0
  have hstep : ∀ (rem : Nat) (acc : BitVec w) (i : BitVec 64),
      i.toNat ≤ len.toNat → rem = len.toNat - i.toNat →
      foldSpec f mask xs acc rem i.toNat = spec →
      js.1 (acc, i, ()) m := by
    intro rem
    induction rem with
    | zero =>
      intro acc i hi hrem hspec
      have hge : len.toNat ≤ i.toNat := by omega
      have hult : i.ult len = false := by
        simp [BitVec.ult]; omega
      apply hclosed.1 (acc, i, ()) m
      dsimp only
      simp only [wp, Op.wp, vals, Arg.val]
      rw [hult64]
      refine ⟨fun htrue => absurd htrue (by rw [hult]; decide), fun _ => ?_⟩
      refine ⟨trivial, ?_⟩
      dsimp only [foldSpec] at hspec
      exact hspec
    | succ rem' ih =>
      intro acc i hi hrem hspec
      have hlt : i.toNat < len.toNat := by omega
      have hult : i.ult len = true := by
        simp [BitVec.ult]; exact hlt
      have hload := hmem i.toNat hlt
      have hpow : len.toNat < 2 ^ 64 := len.isLt
      have hinc : (i + 1#64).toNat = i.toNat + 1 := by
        rw [BitVec.toNat_add]
        simp [Nat.mod_eq_of_lt (by omega : i.toNat + 1 < 2 ^ 64)]
      apply hclosed.1 (acc, i, ()) m
      dsimp only
      simp only [wp, Op.wp, vals, Arg.val]
      rw [hult64]
      refine ⟨fun _ => ?_, fun hfalse => absurd hfalse (by rw [hult]; decide)⟩
      rw [hmul64, hadd64, hadd64]
      have haddr : base + i * stride + off =
          base + BitVec.ofNat 64 i.toNat * stride + off := by
        simp [BitVec.ofNat_toNat]
      rw [haddr]
      refine ⟨xs i.toNat, hload, ?_⟩
      rw [handw, hop acc (xs i.toNat &&& mask), hsext32]
      refine ⟨by decide, ?_⟩
      rw [hadd64]
      dsimp only [foldSpec] at hspec
      rw [← hinc] at hspec
      rw [show BitVec.signExtend 64 (1 : Val (.bits 32)) = 1#64 by decide]
      exact ih (f acc (xs i.toNat &&& mask)) (i + 1#64) (by omega) (by omega) hspec
  rw [show BitVec.signExtend 64 (0 : Val (.bits 32)) = 0#64 by decide]
  exact hstep len.toNat init 0#64 (Nat.zero_le _) (by simp) rfl

/-- Parametric WP Theorem 3 (proved ONCE): `unrollMixKernel` computes `List.foldl` over an
arbitrary Lean list `ks : List (BitVec w)` via `wp_c0UnrollK_pure`, with zero runtime loops. -/
theorem unrollMixKernel_wp (Γ : Env) (m : Mem 64) (X : XPost)
    (w : Nat) (ks : List (BitVec w)) (op : OpCode [.bits w, .bits w] [.bits w])
    (f : BitVec w → BitVec w → BitVec w)
    (hop : ∀ (a b : BitVec w) (p : Tup Val [.bits w] → Prop),
      OpCode.wp op (a, b, ()) p ↔ p (f a b, ()))
    (salt init : BitVec w) :
    Func.wp Γ (unrollMixKernel w ks op salt) (init, ()) m
      (fun (r, ()) m' => m' = m ∧ r = ks.foldl (fun acc k => f acc (k ^^^ salt)) init)
      X := by
  have hxor : ∀ (a b : Val (.bits w)) k,
      OpCode.wp (.xor (.bits w)) (a, b, ()) k ↔ k (a ^^^ b, ()) := fun _ _ _ => Iff.rfl
  dsimp only [unrollMixKernel, Func.wp]
  refine wp_c0UnrollK_pure (ts := [.bits w]) ks _
    (fun (acc, ()) k => (f acc (k ^^^ salt), ())) ?_ (init, ()) m _ ?_
  · intro x ⟨acc, ⟨⟩⟩ m' kcont hk
    dsimp only
    simp only [wp, Op.wp, vals, Arg.val]
    rw [hxor, hop acc (x ^^^ salt)]
    exact hk
  · simp only [wp, vals, Arg.val]
    refine ⟨trivial, ?_⟩
    induction ks generalizing init with
    | nil => rfl
    | cons hd tl ih => exact ih (f init (hd ^^^ salt))

/-- Parametric WP Theorem 4 (proved ONCE): `findIfSnippetKernel` is parameterized by an arbitrary
pure binary `C0ExprSnippet` `pred`, discharged via predicate specification `hpred`. -/
theorem findIfSnippetKernel_wp (Γ : Env) (m : Mem 64) (X : XPost)
    (w : Nat) (pred : C0ExprSnippet [.bits w, .bits w] .bool)
    (p : BitVec w → BitVec w → Bool)
    (hpred : ∀ (a b : Arg Val (.bits w)) (k : Bool → LeanQbe.T.Expr Val Cont [.bits 64]) m0
        {Q : Post [.bits 64]},
      wp Γ Q X (k (p a.val b.val)) m0 → wp Γ Q X (pred Val Cont [.bits 64] (a, b, ()) k) m0)
    (target : BitVec w) (stride off base len : BitVec 64)
    (xs : Nat → BitVec w)
    (hmem : MemArray m w base len stride off xs) :
    Func.wp Γ (findIfSnippetKernel w pred target stride off) (base, len, ()) m
      (fun (r, ()) m' =>
        m' = m ∧ r = firstMatchFrom (fun v => p v target) xs len.toNat len.toNat 0)
      X := by
  dsimp only [findIfSnippetKernel, Func.wp]
  simp only [wp, Op.wp, OpCode.wp, vals, Arg.val]
  refine ⟨by decide, ?_⟩
  intro js hclosed
  let spec := firstMatchFrom (fun v => p v target) xs len.toNat len.toNat 0
  have hstep : ∀ (rem : Nat) (i : BitVec 64),
      i.toNat ≤ len.toNat → rem = len.toNat - i.toNat →
      firstMatchFrom (fun v => p v target) xs len.toNat rem i.toNat = spec →
      js.1 (i, ()) m := by
    intro rem
    induction rem with
    | zero =>
      intro i hi hrem hspec
      have hge : len.toNat ≤ i.toNat := by omega
      have hult : i.ult len = false := by
        simp [BitVec.ult]; omega
      apply hclosed.1 (i, ()) m
      dsimp only
      simp only [wp, Op.wp, OpCode.wp, vals, Arg.val, liftCmp, CmpOp.evalBits, Ty.hasFloat,
        Bool.false_eq_true, ite_false]
      refine ⟨fun htrue => absurd htrue (by rw [hult]; decide), fun _ => ?_⟩
      refine ⟨trivial, ?_⟩
      dsimp only [firstMatchFrom] at hspec
      simpa [BitVec.ofNat_toNat] using hspec
    | succ rem' ih =>
      intro i hi hrem hspec
      have hlt : i.toNat < len.toNat := by omega
      have hult : i.ult len = true := by
        simp [BitVec.ult]; exact hlt
      have hload := hmem i.toNat hlt
      have hpow : len.toNat < 2 ^ 64 := len.isLt
      have hinc : (i + 1#64).toNat = i.toNat + 1 := by
        rw [BitVec.toNat_add]
        simp [Nat.mod_eq_of_lt (by omega : i.toNat + 1 < 2 ^ 64)]
      apply hclosed.1 (i, ()) m
      dsimp only
      simp only [wp, Op.wp, OpCode.wp, vals, Arg.val, liftCmp, CmpOp.evalBits, lift2, Ty.hasFloat,
        Bool.false_eq_true, ite_false]
      refine ⟨fun _ => ?_, fun hfalse => absurd hfalse (by rw [hult]; decide)⟩
      have haddr : base + i * stride + off =
          base + BitVec.ofNat 64 i.toNat * stride + off := by
        simp [BitVec.ofNat_toNat]
      rw [haddr]
      refine ⟨xs i.toNat, hload, ?_⟩
      refine hpred _ _ _ m ?_
      dsimp only [Arg.val]
      simp only [wp, Op.wp, OpCode.wp, vals, Arg.val, lift2, Ty.hasFloat, Bool.false_eq_true,
        ite_false]
      by_cases hmatch : p (xs i.toNat) target = true
      · refine ⟨fun _ => ⟨trivial, ?_⟩, fun hf => absurd hmatch (by simp [hf])⟩
        dsimp only [firstMatchFrom] at hspec
        simp only [hlt, hmatch, ↓reduceIte] at hspec
        simpa [BitVec.ofNat_toNat] using hspec
      · refine ⟨fun ht => absurd ht hmatch, fun _ => ?_⟩
        refine ⟨by decide, ?_⟩
        have hb : p (xs i.toNat) target = false := by
          cases hb0 : p (xs i.toNat) target <;> simp_all
        dsimp only [firstMatchFrom] at hspec
        simp only [hlt, hb, Bool.false_eq_true, ↓reduceIte] at hspec
        rw [← hinc] at hspec
        rw [show BitVec.signExtend 64 (1 : Val (.bits 32)) = 1#64 by decide]
        exact ih (i + 1#64) (by omega) (by omega) hspec
  rw [show BitVec.signExtend 64 (0 : Val (.bits 32)) = 0#64 by decide]
  exact hstep len.toNat 0#64 (Nat.zero_le _) (by simp) rfl

/-! ## 3. Static AST Checks, `Fn.Wf`, and QBE/C++ Printing -/

#guard Func.checkTFlat (valAndCastTpl 32 7 true 8#64)
#guard Func.checkTFlat (valAndCastTpl 64 13 false 16#64)
#guard Func.checkTFlat (opaqueSwapTpl (.bits 32) 0#64)
#guard Func.checkTFlat (stmtCallerTpl 32 (.add (.bits 32)) 5#32)

theorem findEq32_wf : Func.Wf findEq32 := by t_wf_reify
theorem findUlt64_wf : Func.Wf findUlt64 := by t_wf_reify
theorem foldXor32_wf : Func.Wf foldXor32 := by t_wf_reify
theorem foldAdd64_wf : Func.Wf foldAdd64 := by t_wf_reify
theorem unrollAdd32_wf : Func.Wf unrollAdd32 := by t_wf_reify
theorem findXorZeroSnip64_wf : Func.Wf findXorZeroSnip64 := by t_wf_reify
theorem findLtFnSnip32_wf : Func.Wf findLtFnSnip32 := by t_wf_reify

#guard (PrintQbe.fns concreteFns).isOk
#guard (PrintCpp.ppModule concreteFns).isOk

#print axioms findIfKernel_wp
#print axioms foldMaskedKernel_wp
#print axioms unrollMixKernel_wp
#print axioms findIfSnippetKernel_wp

end

end LeanQbeTest.T.C0ProtoTemplatesTest
