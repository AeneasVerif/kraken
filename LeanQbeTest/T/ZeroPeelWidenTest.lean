module

public import LeanQbe.T.ZeroPeel
public import LeanQbe.T.ZeroPeelLemmas
public import LeanQbe.T.MainFlat
public import LeanQbe.T.MainFlatLemmas
public import LeanQbe.T.MainCertCore
public import LeanQbe.T.MainCertProof
public import LeanQbe.T.MainCertFlat
public import LeanQbe.T.MainCertInline
public import LeanQbe.T.Amd64.Targ
public import LeanQbe.T.Amd64.TargLemmas
public import LeanQbe.T.Amd64.PrintAsm0
public import LeanQbe.T.Logic.MemLemmas
public import LeanQbe.T.Examples.Kissat.FullM6Sweep
public import LeanQbe.T.Examples.Kissat.Full1
import LeanQbe.T.FlatLemmas
import LeanQbe.T.WPLemmas
public meta import Lean
public meta import LeanQbe.T.MainCertElab
public meta import LeanQbe.T.MainCertFlatElab
public meta import LeanQbe.T.MainCertInline
public meta import LeanQbe.T.Amd64.Targ
public meta import LeanQbe.T.Amd64.PrintAsm0
public meta import LeanQbe.T.MainFlat
public meta import LeanQbe.T.Examples.Kissat.FullM6Sweep
public meta import LeanQbe.T.Examples.Kissat.Full1

/-!
# `u32` IV & Multi-Store `ZeroPeel` Widening / Unrolling Regression Tests (`ZeroPeelWidenTest`)

Covers:
1. Positive `u32`-IV single-store widening (`u32Zero8`, `u32Zero32`): `zpLoops == 2`, `checkTFlat`,
   `Wf`, `callsOk`, and `Func.zeroPeel_spec` over `array`.
2. Positive `u32`-IV 2-store runtime-guarded widening (`u32MultiFill2`, matching `full_k6_init`
   Loop 2): `zpLoops == 2`, disjoint widening + overlapping-base scalar fallback soundness proof
   (`u32MultiFill2_zeroPeel_overlap_spec`).
3. `full_k6_init`-shaped 6-store `u32` loop (`k6Loop1Shape`) 4x unrolling and real Kissat
   `full_k6_init`, `full_zero_tables1`, and `full_m6_els_fold` IR / x86-64 asm reduction `#guard`
   checks.
4. Negative tests (`u32SubNeg`, `u32Step2Neg`, `u32SignedLtNeg`): wrapping/unsafe `u32` IVs stay
   untouched and sound.
5. Certified SysV x64 compilation (`compile_linked_chunks! (flat := false)` vs `(flat := true)`
   `code = rfl`, `bounds = rfl`), machine execution (`Eventually (x64Target.mach.step ...)` for
   both disjoint and overlapping buffers), and `<= std3` `#print axioms`.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.ZeroPeelWidenTest

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Amd64 Kraken

/-! ## Helpers -/

@[expose] def countStoresTFlat {rs : List Ty} : TFlat rs → Nat
  | .let_ _ k | .load _ _ k => countStoresTFlat k
  | .store _ _ k => 1 + countStoresTFlat k
  | .call _ _ _ k => countStoresTFlat k
  | .jnz _ t e => countStoresTFlat t + countStoresTFlat e
  | .group bs k => countStoresBs bs + countStoresTFlat k
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => 0
where
  countStoresBs {rs : List Ty} : {sig : List (List Ty)} → TBlocks rs sig → Nat
    | _, .nil => 0
    | _, .cons b bs => countStoresTFlat b + countStoresBs bs

@[expose] def countAsmLines (asm : String) (sub : String) : Nat :=
  ((asm.splitOn "\n").filter fun s => (s.splitOn sub).length > 1).length

@[expose] def hasSubstring (asm sub : String) : Bool :=
  (asm.splitOn sub).length > 1

@[expose] def compileX64Asm (name : String) (as rs : List Ty) (body : Func as rs) :
    Except String String := do
  let tf := reifyFunc body
  let h := Fn.computeHints x64Target.toIsa x64LegalTarget ⟨name, as, rs, body⟩
  let ds ← compileFlatFn x64Target.toIsa x64LegalTarget h ⟨name, as, rs, tf⟩
  pure (printAsm0 ds)

/-! ## 1. `u32`-IV Single-Store Widening (`u32Zero8`, `u32Zero32`) -/

/-- `u32` IV (`0 ..< n`) filling `u8` array with `0#8` via `.zext 32 64`. -/
@[expose] def u32Zero8 : Func [i64, i32] [i64] := fun _ _ (ptr, n, ()) =>
  loop1 (ts := [i32])
    (fun loop (i, ()) =>
      .let_ (op2 (.ult i32) (.var i) (.var n)) fun (c, ()) =>
      .jnz (.var c)
        (.let_ (op1 (.zext 32 64) (.var i)) fun (i64v, ()) =>
         .let_ (op2 (.add i64) (.var ptr) (.var i64v)) fun (addr, ()) =>
         .store (t := .bits 8) (.imm 0#8) (.var addr)
           (.let_ (op2 (.add i32) (.var i) (.imm 1#32)) fun (i', ()) =>
            .jump loop (.var i', ())))
        (.ret (.var ptr, ())))
    (fun loop => .jump loop (.imm 0#32, ()))

/-- `u32` IV (`0 ..< n`) filling `u32` array with `0#32` via `.zext 32 64` + `.shl 64 ... 2`. -/
@[expose] def u32Zero32 : Func [i64, i32] [i64] := fun _ _ (ptr, n, ()) =>
  loop1 (ts := [i32])
    (fun loop (i, ()) =>
      .let_ (op2 (.ult i32) (.var i) (.var n)) fun (c, ()) =>
      .jnz (.var c)
        (.let_ (op1 (.zext 32 64) (.var i)) fun (i64v, ()) =>
         .let_ (op2 (.shl i64) (.var i64v) (.imm 2#64)) fun (off, ()) =>
         .let_ (op2 (.add i64) (.var ptr) (.var off)) fun (addr, ()) =>
         .store (t := i32) (.imm 0#32) (.var addr)
           (.let_ (op2 (.add i32) (.var i) (.imm 1#32)) fun (i', ()) =>
            .jump loop (.var i', ())))
        (.ret (.var ptr, ())))
    (fun loop => .jump loop (.imm 0#32, ()))

theorem u32Zero8_wf : u32Zero8.Wf := by t_wf_reify
theorem u32Zero32_wf : u32Zero32.Wf := by t_wf_reify
theorem u32Zero8_zeroPeel_wf : (Func.zeroPeel u32Zero8).Wf := Func.zeroPeel_wf u32Zero8_wf
theorem u32Zero32_zeroPeel_wf : (Func.zeroPeel u32Zero32).Wf := Func.zeroPeel_wf u32Zero32_wf

#guard ZeroPeel.zpLoops (reifyFunc (Func.zeroPeel u32Zero8)) == 2
#guard ZeroPeel.zpLoops (reifyFunc (Func.zeroPeel u32Zero32)) == 2
#guard Func.checkTFlat (Func.zeroPeel u32Zero8)
#guard Func.checkTFlat (Func.zeroPeel u32Zero32)
#guard countStoresTFlat (TFlat.zeroPeelWith {} (reifyFunc u32Zero8)) == 9
#guard countStoresTFlat (TFlat.zeroPeelWith {} (reifyFunc u32Zero32)) == 9

theorem u32Zero8_array_spec (Γ : Env) (ptr : BitVec 64) (xs : List (Val (.bits 8)))
    (hxs : xs.length < 2 ^ 32) (R : Mem 64 → Prop) (m : Mem 64)
    (hm : (array ptr xs ⋆ R) m) (X : XPost) :
    Func.spec Γ u32Zero8 (ptr, BitVec.ofNat 32 xs.length, ()) m
      (fun (r, ()) m' =>
        r = ptr ∧ ∃ ys : List (Val (.bits 8)),
          ys.length = xs.length ∧ (∀ k < xs.length, ys[k]? = some 0#8) ∧
          (array ptr ys ⋆ R) m') X := by
  dsimp only [Func.spec, Func.wp, u32Zero8]
  refine wp_loop1 _ _
    (fun cnt (x : Tup Val [i32]) m' =>
      x.1.toNat + cnt = xs.length ∧
      ∃ ys : List (Val (.bits 8)),
        ys.length = xs.length ∧ (∀ k < x.1.toNat, ys[k]? = some 0#8) ∧ (array ptr ys ⋆ R) m')
    ?_ ?_
  · rintro J cnt ⟨i, ⟨⟩⟩ m' hJ ⟨hsum, ys, hlen, hzero, hmem⟩
    dsimp only at hsum hzero; wp_unfold
    have hn : (BitVec.ofNat 32 xs.length).toNat = xs.length := by
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hxs]
    by_cases hlt : i < BitVec.ofNat 32 xs.length
    · have hc : BitVec.ult i (BitVec.ofNat 32 xs.length) = true := BitVec.ult_iff_lt.mpr hlt
      have hilt : i.toNat < xs.length := by rw [← hn]; exact BitVec.lt_def.mp hlt
      simp only [hc, true_implies]
      have haddr : ptr + i.setWidth 64 = ptr + BitVec.ofNat 64 ((Ty.bits 8).bytes * i.toNat) := by
        rw [show (Ty.bits 8).bytes = 1 by decide, Nat.one_mul]
        congr 1; apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_setWidth,
          Nat.mod_eq_of_lt (Nat.lt_trans i.isLt (by decide) : i.toNat < 2 ^ 64)]
      obtain ⟨hok, hm''⟩ := store_array 0#8 (by decide) (by omega : i.toNat < ys.length) hmem
      refine ⟨⟨haddr ▸ hok, ?_⟩, fun h => False.elim (by cases h)⟩
      refine hJ (cnt - 1) (i + 1#32, ()) _ (by omega) ?_
      have hadd : (i + 1#32).toNat = i.toNat + 1 := by
        rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (by omega)]
      refine ⟨by dsimp only; rw [hadd]; omega, ys.set i.toNat 0#8, by simp [hlen], ?_, haddr ▸ hm''⟩
      intro k hk; dsimp only at hk; rw [hadd] at hk
      rw [List.getElem?_set]; split
      · have : i.toNat < ys.length := by omega
        simp [this]
      · exact hzero k (by omega)
    · have hcf : BitVec.ult i (BitVec.ofNat 32 xs.length) = false :=
        Bool.eq_false_iff.mpr fun h => hlt (BitVec.ult_iff_lt.mp h)
      have hige : xs.length ≤ i.toNat := by
        rw [← hn]; exact Nat.le_of_not_lt fun h => hlt (BitVec.lt_def.mpr h)
      simp only [hcf, false_implies, Bool.false_eq_true, true_implies, true_and]
      exact ⟨ys, hlen, fun k hk => hzero k (by omega), hmem⟩
  · intro J hJ; wp_unfold
    refine hJ xs.length (0#32, ()) m ⟨by simp, xs, rfl, ?_, hm⟩
    intro _ hk; simp at hk

theorem u32Zero8_zp_spec (Γ : Env) (ptr : BitVec 64) (xs : List (Val (.bits 8)))
    (hxs : xs.length < 2 ^ 32) (R : Mem 64 → Prop) (m : Mem 64)
    (hm : (array ptr xs ⋆ R) m) (X : XPost) :
    Func.spec Γ (Func.zeroPeel u32Zero8) (ptr, BitVec.ofNat 32 xs.length, ()) m
      (fun (r, ()) m' =>
        r = ptr ∧ ∃ ys : List (Val (.bits 8)),
          ys.length = xs.length ∧ (∀ k < xs.length, ys[k]? = some 0#8) ∧
          (array ptr ys ⋆ R) m') X :=
  Func.zeroPeel_spec u32Zero8_wf {} (u32Zero8_array_spec Γ ptr xs hxs R m hm X)

/-! ## 2. Multi-Store `u32` Widening (`u32MultiFill2`) & Overlap Soundness -/

/-- `full_k6_init` Loop 2 shape: `u32` IV filling 2 `u32` arrays (`0` and `-1`). -/
@[expose] def u32MultiFill2 : Func [i64, i64, i32] [i64] := fun _ _ (p0, p1, n, ()) =>
  loop1 (ts := [i32])
    (fun loop (i, ()) =>
      .let_ (op2 (.ult i32) (.var i) (.var n)) fun (c, ()) =>
      .jnz (.var c)
        (.let_ (op1 (.zext 32 64) (.var i)) fun (i64v, ()) =>
         .let_ (op2 (.shl i64) (.var i64v) (.imm 2#64)) fun (off, ()) =>
         .let_ (op2 (.add i64) (.var p0) (.var off)) fun (a0, ()) =>
         .store (t := i32) (.imm 0#32) (.var a0)
           (.let_ (op2 (.add i64) (.var p1) (.var off)) fun (a1, ()) =>
            .store (t := i32) (.imm 0xffffffff#32) (.var a1)
              (.let_ (op2 (.add i32) (.var i) (.imm 1#32)) fun (i', ()) =>
               .jump loop (.var i', ()))))
        (.ret (.var p0, ())))
    (fun loop => .jump loop (.imm 0#32, ()))

theorem u32MultiFill2_wf : u32MultiFill2.Wf := by t_wf_reify
theorem u32MultiFill2_zeroPeel_wf : (Func.zeroPeel u32MultiFill2).Wf :=
  Func.zeroPeel_wf u32MultiFill2_wf

#guard ZeroPeel.zpLoops (reifyFunc (Func.zeroPeel u32MultiFill2)) == 2
#guard Func.checkTFlat (Func.zeroPeel u32MultiFill2)
#guard countStoresTFlat (TFlat.zeroPeelWith {} (reifyFunc u32MultiFill2)) == 10

@[expose] def zeroNegList (n : Nat) : List (Val i32) :=
  List.replicate n 0#32 ++ [0xffffffff#32]

private theorem shift2_zext_eq (i : BitVec 32) :
    (i.setWidth 64 <<< 2#64) = BitVec.ofNat 64 (i32.bytes * i.toNat) := by
  change (i.setWidth 64 <<< (2 : Nat)) = _
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have hi : i.toNat < 2 ^ 32 := i.isLt
  have hlt1 : i.toNat < 2 ^ 64 := Nat.lt_trans hi (by decide)
  rw [Nat.mod_eq_of_lt hlt1, Nat.shiftLeft_eq, Nat.mul_comm,
    show i32.bytes = 4 from rfl, show 2 ^ 2 = 4 from rfl,
    Nat.mod_eq_of_lt (by omega : 4 * i.toNat < 2 ^ 64)]

/-- Disjoint specification for `u32MultiFill2`: fills `xs0` with `0#32` and `xs1` with
`0xffffffff#32`. -/
theorem u32MultiFill2_disjoint_spec (Γ : Env) (p0 p1 : BitVec 64) (xs0 xs1 : List (Val i32))
    (hxs : xs0.length = xs1.length) (h32 : xs0.length < 2 ^ 32)
    (R : Mem 64 → Prop) (m : Mem 64) (hm : (array p0 xs0 ⋆ array p1 xs1 ⋆ R) m) (X : XPost) :
    Func.spec Γ u32MultiFill2 (p0, p1, BitVec.ofNat 32 xs0.length, ()) m
      (fun (r, ()) m' =>
        r = p0 ∧ ∃ ys0 ys1 : List (Val i32),
          ys0.length = xs0.length ∧ ys1.length = xs1.length ∧
          (∀ k < xs0.length, ys0[k]? = some 0#32 ∧ ys1[k]? = some 0xffffffff#32) ∧
          (array p0 ys0 ⋆ array p1 ys1 ⋆ R) m') X := by
  dsimp only [Func.spec, Func.wp, u32MultiFill2]
  refine wp_loop1 _ _
    (fun cnt (x : Tup Val [i32]) m' =>
      x.1.toNat + cnt = xs0.length ∧ ∃ ys0 ys1 : List (Val i32),
        ys0.length = xs0.length ∧ ys1.length = xs1.length ∧
        (∀ k < x.1.toNat, ys0[k]? = some 0#32 ∧ ys1[k]? = some 0xffffffff#32) ∧
        (array p0 ys0 ⋆ array p1 ys1 ⋆ R) m') ?_ ?_
  · rintro J cnt ⟨i, ⟨⟩⟩ m' hJ ⟨hsum, ys0, ys1, hl0, hl1, hprev, hmem⟩
    dsimp only at hsum hprev; wp_unfold
    have hn : (BitVec.ofNat 32 xs0.length).toNat = xs0.length := by
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h32]
    by_cases hlt : i < BitVec.ofNat 32 xs0.length
    · have hc : BitVec.ult i (BitVec.ofNat 32 xs0.length) = true := BitVec.ult_iff_lt.mpr hlt
      have hilt : i.toNat < xs0.length := by rw [← hn]; exact BitVec.lt_def.mp hlt
      simp only [hc, true_implies, Bool.true_eq_false, false_implies, and_true]
      have hsh := shift2_zext_eq i
      rw [sep_assoc] at hmem
      obtain ⟨hok0, hm1⟩ := store_array (a := p0) (xs := ys0) (R := array p1 ys1 ⋆ R) 0#32
        (by decide) (by omega : i.toNat < ys0.length) hmem
      rw [← sep_assoc, sep_comm (array p0 _), sep_assoc] at hm1
      obtain ⟨hok1, hm2⟩ := store_array (a := p1) (xs := ys1)
        (R := array p0 (ys0.set i.toNat 0#32) ⋆ R)
        0xffffffff#32 (by decide) (by omega : i.toNat < ys1.length) hm1
      refine ⟨hsh ▸ hok0, hsh ▸ hok1, ?_⟩
      refine hJ (cnt - 1) (i + 1#32, ()) _ (by omega) ?_
      have hadd : (i + 1#32).toNat = i.toNat + 1 := by
        rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (by omega)]
      refine ⟨by dsimp only; rw [hadd]; omega, ys0.set i.toNat 0#32, ys1.set i.toNat 0xffffffff#32,
        by simp [hl0], by simp [hl1], ?_, ?_⟩
      · intro k hk; dsimp only at hk; rw [hadd] at hk
        rw [List.getElem?_set, List.getElem?_set]; split
        · simp [show i.toNat < ys0.length by omega, show i.toNat < ys1.length by omega]
        · exact hprev k (by omega)
      · rw [← sep_assoc, sep_comm (array p1 _)] at hm2
        exact hsh ▸ hm2
    · have hcf : BitVec.ult i (BitVec.ofNat 32 xs0.length) = false :=
        Bool.eq_false_iff.mpr fun h => hlt (BitVec.ult_iff_lt.mp h)
      have hige : xs0.length ≤ i.toNat := by
        rw [← hn]; exact Nat.le_of_not_lt fun h => hlt (BitVec.lt_def.mpr h)
      simp only [hcf, false_implies, Bool.false_eq_true, true_implies, true_and]
      exact ⟨ys0, ys1, hl0, hl1, fun k hk => hprev k (by omega), hmem⟩
  · intro J hJ; wp_unfold
    refine hJ xs0.length (0#32, ()) m ⟨by simp, xs0, xs1, rfl, rfl, ?_, hm⟩
    intro _ hk; simp at hk

theorem u32Fill2_zp_disj (Γ : Env) (p0 p1 : BitVec 64)
    (xs0 xs1 : List (Val i32)) (hxs : xs0.length = xs1.length) (h32 : xs0.length < 2 ^ 32)
    (R : Mem 64 → Prop) (m : Mem 64) (hm : (array p0 xs0 ⋆ array p1 xs1 ⋆ R) m) (X : XPost) :
    Func.spec Γ (Func.zeroPeel u32MultiFill2) (p0, p1, BitVec.ofNat 32 xs0.length, ()) m
      (fun (r, ()) m' =>
        r = p0 ∧ ∃ ys0 ys1 : List (Val i32),
          ys0.length = xs0.length ∧ ys1.length = xs1.length ∧
          (∀ k < xs0.length, ys0[k]? = some 0#32 ∧ ys1[k]? = some 0xffffffff#32) ∧
          (array p0 ys0 ⋆ array p1 ys1 ⋆ R) m') X :=
  Func.zeroPeel_spec u32MultiFill2_wf {}
    (u32MultiFill2_disjoint_spec Γ p0 p1 xs0 xs1 hxs h32 R m hm X)

/-- Raw overlapping specification for `u32MultiFill2` when `p1 = p0 + 4#64`: preserves exact
sequential overwrite order. -/
theorem u32MultiFill2_overlap_raw_spec (Γ : Env) (p0 : BitVec 64) (n : Nat) (hn0 : 0 < n)
    (hn32 : n < 2 ^ 32) (xs : List (Val i32)) (hxs : xs.length = n + 1)
    (R : Mem 64 → Prop) (m : Mem 64) (hm : (array p0 xs ⋆ R) m) (X : XPost) :
    Func.spec Γ u32MultiFill2 (p0, p0 + 4#64, BitVec.ofNat 32 n, ()) m
      (fun (r, ()) m' => r = p0 ∧ (array p0 (zeroNegList n) ⋆ R) m') X := by
  dsimp only [Func.spec, Func.wp, u32MultiFill2]
  refine wp_loop1 _ _
    (fun cnt (x : Tup Val [i32]) m' =>
      x.1.toNat + cnt = n ∧ ∃ ys : List (Val i32),
        ys.length = n + 1 ∧
        (∀ k < x.1.toNat, ys[k]? = some 0#32) ∧
        (0 < x.1.toNat → ys[x.1.toNat]? = some 0xffffffff#32) ∧
        (array p0 ys ⋆ R) m') ?_ ?_
  · rintro J cnt ⟨i, ⟨⟩⟩ m' hJ ⟨hsum, ys, hlen, hzero, hlast, hmem⟩
    dsimp only at hsum hzero hlast; wp_unfold
    have hnEq : (BitVec.ofNat 32 n).toNat = n := by
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn32]
    by_cases hlt : i < BitVec.ofNat 32 n
    · have hc : BitVec.ult i (BitVec.ofNat 32 n) = true := BitVec.ult_iff_lt.mpr hlt
      have hilt : i.toNat < n := by rw [← hnEq]; exact BitVec.lt_def.mp hlt
      simp only [hc, true_implies, Bool.true_eq_false, false_implies, and_true]
      have hsh := shift2_zext_eq i
      have hsh1 : p0 + 4#64 + (i.setWidth 64 <<< 2#64) =
          p0 + BitVec.ofNat 64 (i32.bytes * (i.toNat + 1)) := by
        rw [hsh, BitVec.add_assoc, show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
          ← BitVec.ofNat_add, show i32.bytes = 4 from rfl,
          show 4 + 4 * i.toNat = 4 * (i.toNat + 1) by omega]
      obtain ⟨hok0, hm1⟩ := store_array (a := p0) (xs := ys) (R := R) 0#32
        (by decide) (by omega : i.toNat < ys.length) hmem
      rw [← hsh] at hm1
      have hi1 : i.toNat + 1 < (ys.set i.toNat 0#32).length := by simp [hlen]; omega
      obtain ⟨hok1, hm2⟩ := store_array (a := p0) (xs := ys.set i.toNat 0#32) (R := R)
        0xffffffff#32 (by decide) hi1 hm1
      refine ⟨hsh ▸ hok0, hsh1 ▸ hok1, ?_⟩
      refine hJ (cnt - 1) (i + 1#32, ()) _ (by omega) ?_
      have hadd : (i + 1#32).toNat = i.toNat + 1 := by
        rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl,
          Nat.mod_eq_of_lt (by omega)]
      refine ⟨by dsimp only; rw [hadd]; omega,
        (ys.set i.toNat 0#32).set (i.toNat + 1) 0xffffffff#32, by simp [hlen], ?_, ?_,
        hsh1 ▸ hm2⟩
      · intro k hk; dsimp only at hk; rw [hadd] at hk
        rw [List.getElem?_set, List.getElem?_set]
        have hkne : i.toNat + 1 ≠ k := by omega
        simp only [hkne, ↓reduceIte]; split
        · simp [show i.toNat < ys.length by omega]
        · exact hzero k (by omega)
      · intro _; dsimp only; rw [hadd, List.getElem?_set]
        simp [show i.toNat + 1 < ys.length by omega]
    · have hcf : BitVec.ult i (BitVec.ofNat 32 n) = false :=
        Bool.eq_false_iff.mpr fun h => hlt (BitVec.ult_iff_lt.mp h)
      have hieq : i.toNat = n := by
        have hle : n ≤ i.toNat := by
          rw [← hnEq]; exact Nat.le_of_not_lt fun h => hlt (BitVec.lt_def.mpr h)
        omega
      simp only [hcf, false_implies, Bool.false_eq_true, true_implies, true_and]
      have hEqL : ys = zeroNegList n := by
        dsimp only [zeroNegList]
        apply List.ext_getElem (by simp [hlen])
        intro k hk1 hk2
        have hlast' := hlast (by omega)
        have hzero' : ∀ j < n, ys[j]? = some 0#32 := fun j hj => hzero j (by omega)
        by_cases hk : k < n
        · have hz := hzero' k hk
          rw [List.getElem?_eq_getElem hk1, Option.some.injEq] at hz
          rw [hz, List.getElem_append_left (by simp [hk]), List.getElem_replicate]
        · have hkn : k = n := by simp at hk2; omega
          rw [hieq, ← hkn] at hlast'
          rw [List.getElem?_eq_getElem hk1, Option.some.injEq] at hlast'
          subst hkn
          rw [hlast', List.getElem_append_right (by simp)]; simp
      rwa [hEqL] at hmem
  · intro J hJ; wp_unfold
    refine hJ n (0#32, ()) m ⟨by simp, xs, hxs, ?_, ?_, hm⟩
    · intro _ hk; simp at hk
    · intro h0; simp at h0

theorem u32Fill2_zp_ovlp (Γ : Env) (p0 : BitVec 64) (n : Nat) (hn0 : 0 < n)
    (hn32 : n < 2 ^ 32) (xs : List (Val i32)) (hxs : xs.length = n + 1)
    (R : Mem 64 → Prop) (m : Mem 64) (hm : (array p0 xs ⋆ R) m) (X : XPost) :
    Func.spec Γ (Func.zeroPeel u32MultiFill2) (p0, p0 + 4#64, BitVec.ofNat 32 n, ()) m
      (fun (r, ()) m' => r = p0 ∧ (array p0 (zeroNegList n) ⋆ R) m') X :=
  Func.zeroPeel_spec u32MultiFill2_wf {}
    (u32MultiFill2_overlap_raw_spec Γ p0 n hn0 hn32 xs hxs R m hm X)

/-! ## 3. `full_k6_init` 6-Store `u32` Unrolling, Kissat IR & x86-64 Reduction `#guard`s -/

/-- Synthetic `full_k6_init` Loop 1 shape (`u32` IV storing 6 `u32` arrays including `i+1`). -/
@[expose] def k6Loop1Shape : Func [i64, i64, i64, i64, i64, i64, i32] [i32] :=
  fun _ _ (a0, a1, a2, a3, a4, a5, n, ()) =>
    loop1 (ts := [i32])
      (fun loop (i, ()) =>
        .let_ (op2 (.ult i32) (.var i) (.var n)) fun (c, ()) =>
        .jnz (.var c)
          (.let_ (op1 (.zext 32 64) (.var i)) fun (i64v, ()) =>
           .let_ (op2 (.shl i64) (.var i64v) (.imm 2#64)) fun (off, ()) =>
           .let_ (op2 (.add i64) (.var a0) (.var off)) fun (p0, ()) =>
           .store (t := i32) (.imm 0#32) (.var p0)
             (.let_ (op2 (.add i64) (.var a1) (.var off)) fun (p1, ()) =>
              .store (t := i32) (.imm 0xffffffff#32) (.var p1)
                (.let_ (op2 (.add i64) (.var a2) (.var off)) fun (p2, ()) =>
                 .store (t := i32) (.imm 0#32) (.var p2)
                   (.let_ (op2 (.add i32) (.var i) (.imm 1#32)) fun (i1, ()) =>
                    .let_ (op2 (.add i64) (.var a3) (.var off)) fun (p3, ()) =>
                    .store (t := i32) (.var i1) (.var p3)
                      (.let_ (op2 (.sub i32) (.var i) (.imm 1#32)) fun (im1, ()) =>
                       .let_ (op2 (.add i64) (.var a4) (.var off)) fun (p4, ()) =>
                       .store (t := i32) (.var im1) (.var p4)
                         (.let_ (op2 (.add i64) (.var a5) (.var off)) fun (p5, ()) =>
                          .store (t := i32) (.var i) (.var p5)
                            (.jump loop (.var i1, ()))))))))
          (.ret (.var n, ())))
      (fun loop => .jump loop (.imm 0#32, ()))

theorem k6Loop1Shape_wf : k6Loop1Shape.Wf := by t_wf_reify
theorem k6Loop1Shape_zeroPeel_wf : (Func.zeroPeel k6Loop1Shape).Wf :=
  Func.zeroPeel_wf k6Loop1Shape_wf

#guard Func.checkTFlat (Func.zeroPeel k6Loop1Shape)
#guard countStoresTFlat (TFlat.zeroPeelWith {} (reifyFunc k6Loop1Shape)) == 30
#guard countStoresTFlat (TFlat.zeroPeelWith { unrollN := 0, peelBudget := 0 }
  (reifyFunc k6Loop1Shape)) == 6

#guard ZeroPeel.zpLoops
  (reifyFunc (Func.zeroPeel Examples.Kissat.FullM6Sweep.full_k6_init_body)) == 6
#guard ZeroPeel.zpLoops (TFlat.zeroPeelWith { unrollN := 0, peelBudget := 0 }
  (reifyFunc Examples.Kissat.FullM6Sweep.full_k6_init_body)) == 3
#guard countStoresTFlat (reifyFunc (Func.zeroPeel Examples.Kissat.FullM6Sweep.full_k6_init_body)) >
  countStoresTFlat (TFlat.zeroPeelWith { unrollN := 0, peelBudget := 0 }
    (reifyFunc Examples.Kissat.FullM6Sweep.full_k6_init_body))

#guard match compileX64Asm "full_k6_init" [i64, i32] []
    Examples.Kissat.FullM6Sweep.full_k6_init_body with
  | .ok optAsm =>
    countAsmLines optAsm "movq $0," == 12 &&
    countAsmLines optAsm "movq $-1," == 4 &&
    hasSubstring optAsm "addl $4,"
  | .error _ => false

#guard match compileX64Asm "full_zero_tables1" [i64] []
    Examples.Kissat.Full.full_zero_tables1_body with
  | .ok optAsm => countAsmLines optAsm "movq $0," >= 4
  | .error _ => false

#guard countStoresTFlat
    (reifyFunc (Func.zeroPeel Examples.Kissat.FullM6Sweep.full_m6_els_fold_body)) >
  countStoresTFlat (TFlat.zeroPeelWith { unrollN := 0, peelBudget := 0 }
    (reifyFunc Examples.Kissat.FullM6Sweep.full_m6_els_fold_body))
#guard (compileX64Asm "full_m6_els_fold" [i64, i32] [.bool]
  Examples.Kissat.FullM6Sweep.full_m6_els_fold_body).isOk

#guard match compileX64Asm "u32_multi_fill2" [i64, i64, i32] [i64] u32MultiFill2 with
  | .ok optAsm =>
    countAsmLines optAsm "movq $0," == 4 && countAsmLines optAsm "movq $-1," == 4
  | .error _ => false

/-! ## 4. Negative Tests (Wrapping / Non-Unit / Signed `u32` IVs Stay Untouched) -/

/-- Decrementing `sub 32` IV (must not trigger widening or unrolling). -/
@[expose] def u32SubNeg : Func [i64, i32] [i64] := fun _ _ (ptr, n, ()) =>
  loop1 (ts := [i32])
    (fun loop (i, ()) =>
      .let_ (op2 (.ult i32) (.imm 0#32) (.var i)) fun (c, ()) =>
      .jnz (.var c)
        (.let_ (op2 (.sub i32) (.var i) (.imm 1#32)) fun (i', ()) =>
         .let_ (op1 (.zext 32 64) (.var i')) fun (i64v, ()) =>
         .let_ (op2 (.add i64) (.var ptr) (.var i64v)) fun (addr, ()) =>
         .store (t := .bits 8) (.imm 0#8) (.var addr) (.jump loop (.var i', ())))
        (.ret (.var ptr, ())))
    (fun loop => .jump loop (.var n, ()))

/-- Non-unit step `add 32 i 2` (must not widen or unroll). -/
@[expose] def u32Step2Neg : Func [i64, i32] [i64] := fun _ _ (ptr, n, ()) =>
  loop1 (ts := [i32])
    (fun loop (i, ()) =>
      .let_ (op2 (.ult i32) (.var i) (.var n)) fun (c, ()) =>
      .jnz (.var c)
        (.let_ (op1 (.zext 32 64) (.var i)) fun (i64v, ()) =>
         .let_ (op2 (.add i64) (.var ptr) (.var i64v)) fun (addr, ()) =>
         .store (t := .bits 8) (.imm 0#8) (.var addr)
           (.let_ (op2 (.add i32) (.var i) (.imm 2#32)) fun (i', ()) =>
            .jump loop (.var i', ())))
        (.ret (.var ptr, ())))
    (fun loop => .jump loop (.imm 0#32, ()))

/-- Signed `slt` comparison (`i <s n`, unsafe under `u32` wrap semantics): untouched. -/
@[expose] def u32SignedLtNeg : Func [i64, i32] [i64] := fun _ _ (ptr, n, ()) =>
  loop1 (ts := [i32])
    (fun loop (i, ()) =>
      .let_ (op2 (.slt i32) (.var i) (.var n)) fun (c, ()) =>
      .jnz (.var c)
        (.let_ (op1 (.zext 32 64) (.var i)) fun (i64v, ()) =>
         .let_ (op2 (.add i64) (.var ptr) (.var i64v)) fun (addr, ()) =>
         .store (t := .bits 8) (.imm 0#8) (.var addr)
           (.let_ (op2 (.add i32) (.var i) (.imm 1#32)) fun (i', ()) =>
            .jump loop (.var i', ())))
        (.ret (.var ptr, ())))
    (fun loop => .jump loop (.imm 0#32, ()))

theorem u32SubNeg_unchanged :
    Func.zeroPeelWith { peelBudget := 0 } u32SubNeg = u32SubNeg := by t_kernel_rfl
theorem u32Step2Neg_unchanged :
    Func.zeroPeelWith { peelBudget := 0 } u32Step2Neg = u32Step2Neg := by t_kernel_rfl
theorem u32SignedLtNeg_unchanged :
    Func.zeroPeelWith { peelBudget := 0 } u32SignedLtNeg = u32SignedLtNeg := by t_kernel_rfl

/-! ## 5. Certified x86-64 Compilation & Concrete Machine Execution (`disjoint` + `overlap`) -/

@[expose] def fnU32Zero8 : Fn := ⟨"u32_zero8", [i64, i32], [i64], u32Zero8⟩
@[expose] def fnU32MultiFill2 : Fn := ⟨"u32_multi_fill2", [i64, i64, i32], [i64], u32MultiFill2⟩

@[expose] def widenX64SrcMod : Module where
  fns := [fnU32Zero8, fnU32MultiFill2]

inline_mod! widenX64Mod widenX64SrcMod {} (compile := false)

theorem widenX64SrcMod_acyclic : widenX64SrcMod.checkAcyclic = true := by t_kernel_rfl

theorem widenX64SrcMod_wf : ∀ f ∈ widenX64SrcMod.fns, f.Wf := by
  intro f hf
  simp only [widenX64SrcMod, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact u32Zero8_wf
  · exact u32MultiFill2_wf

compile_linked_chunks! widenX64Leg
  x64Target x64Layout x64LegalTarget x64LabelClean widenX64Mod 2 (flat := false)

compile_linked_chunks! widenX64Flat
  x64Target x64Layout x64LegalTarget x64LabelClean widenX64Mod 2 (flat := true)

compile_linked_chunks! widenX64Exec
  x64Target x64Layout x64LegalTarget x64LabelClean widenX64SrcMod 2

theorem x64_widen_code_eq : widenX64Leg.code = widenX64Flat.code := rfl
theorem x64_widen_bounds_eq : widenX64Leg.bounds = widenX64Flat.bounds := rfl

noncomputable def widenX64FlatCast :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      (widenX64SrcMod.optInlinePolicy {}) [] [] 0 2048 :=
  widenX64Flat.castModule widenX64Mod.eq

@[expose] def multiFill2Spec : Spec [i64, i64, i32] [i64] :=
  fun (p0, p1, n, ()) m Q _ =>
    (∃ (xs0 xs1 : List (Val i32)) (R : Mem 64 → Prop),
      xs0.length = xs1.length ∧ xs0.length < 2 ^ 32 ∧
      n = BitVec.ofNat 32 xs0.length ∧ (array p0 xs0 ⋆ array p1 xs1 ⋆ R) m ∧
      ∀ ys0 ys1 : List (Val i32), ys0.length = xs0.length → ys1.length = xs1.length →
        (∀ k < xs0.length, ys0[k]? = some 0#32 ∧ ys1[k]? = some 0xffffffff#32) →
        ∀ m', (array p0 ys0 ⋆ array p1 ys1 ⋆ R) m' → Q (p0, ()) m') ∨
    (∃ (nNat : Nat) (xs : List (Val i32)) (R : Mem 64 → Prop),
      0 < nNat ∧ nNat < 2 ^ 32 ∧
      p1 = p0 + 4#64 ∧ n = BitVec.ofNat 32 nNat ∧ xs.length = nNat + 1 ∧
      (array p0 xs ⋆ R) m ∧
      ∀ m', (array p0 (zeroNegList nNat) ⋆ R) m' → Q (p0, ()) m')

@[expose] def widenX64Γ : Env
  | "u32_multi_fill2", [.bits 64, .bits 64, .bits 32], [.bits 64], args, m, Q, X =>
    multiFill2Spec args m Q X
  | _, _, _, _, _, _, _ => False

theorem widenX64SrcMod_wp : ∀ f ∈ widenX64SrcMod.fns, ∀ xs m Q X,
    widenX64Γ f.name f.as f.rs xs m Q X → Func.wp widenX64Γ f.body xs m Q X := by
  intro f hf xs m Q X hspec
  simp only [widenX64SrcMod, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact False.elim hspec
  · rcases xs with ⟨p0, p1, n, ⟨⟩⟩
    dsimp only [widenX64Γ, multiFill2Spec] at hspec
    rcases hspec with
      ⟨xs0, xs1, R, hxs, h32, hn, hm, hQ⟩ | ⟨nNat, xs, R, hn0, hn32, hp1, hn, hxs, hm, hQ⟩
    · dsimp only at hn hm hQ
      rw [hn]
      refine wp_mono (fun (r, ()) m' ⟨hr, ys0, ys1, hl0, hl1, hy, hm'⟩ => ?_)
        (fun _ _ _ _ h => h) _ m
        (u32MultiFill2_disjoint_spec widenX64Γ p0 p1 xs0 xs1 hxs h32 R m hm X)
      rw [hr]; exact hQ ys0 ys1 hl0 hl1 hy m' hm'
    · dsimp only at hp1 hn hm hQ
      rw [hp1, hn]
      refine wp_mono (fun (r, ()) m' ⟨hr, hm'⟩ => ?_) (fun _ _ _ _ h => h) _ m
        (u32MultiFill2_overlap_raw_spec widenX64Γ p0 nNat hn0 hn32 xs hxs R m hm X)
      rw [hr]; exact hQ m' hm'

theorem x64_fill2_disj_runs :
    let xs : List (Val i32) := List.replicate 10 7#32
    let mid : List (Val i32) := List.replicate 6 9#32
    let z10 : List (Val i32) := List.replicate 10 0#32
    let n10 : List (Val i32) := List.replicate 10 0xffffffff#32
    let bs := bytesOf (xs ++ mid ++ xs)
    Eventually (x64Target.mach.step widenX64Exec.host)
      (fun st => x64Target.mach.pc st = x64Init.ra0 ∧
        x64Target.mach.getGpr (x64Target.mach.data st) x64Init.ret0 = 0x1000#64 ∧
        (x64Target.mach.mem (x64Target.mach.data st) =⋆
          (array 0x1000#64 z10 ⋆ array 0x1040#64 n10 ⋆ array 0x1028#64 mid) ⋆
          x64Target.Exit x64Init.sp0 (widenX64Exec.bound "u32_multi_fill2") ⋆ emp))
      (x64Target.mach.mkState
        (x64Init.initState (as := [i64, i64, i32]) (widenX64Exec.bound "u32_multi_fill2") bs
          (0x1000#64, 0x1040#64, 10#32, ()))
        (x64Target.mach.labelAddr widenX64Exec.host "u32_multi_fill2")) := by
  intro xs mid z10 n10 bs
  have hm0 : (array 0x1000#64 xs ⋆ array 0x1040#64 xs ⋆ array 0x1028#64 mid)
      (bs.At 0x1000#64) := by
    have ha := array_bytes 0x1000#64 (xs ++ mid ++ xs) (by decide)
    change array 0x1000#64 (xs ++ mid ++ xs) (bs.At 0x1000#64) at ha
    rw [array_append, array_append] at ha
    have h1 : 0x1000#64 + BitVec.ofNat 64 (i32.bytes * xs.length) = 0x1028#64 := by decide
    have h2 : 0x1000#64 + BitVec.ofNat 64 (i32.bytes * (xs ++ mid).length) = 0x1040#64 := by
      decide
    rw [h1, h2] at ha; rwa [sep_assoc, sep_comm (array 0x1028#64 mid), ← sep_assoc] at ha
  refine widenX64Exec.eventually_ret1_sep_i64 x64Init widenX64Γ
    widenX64SrcMod_acyclic widenX64SrcMod_wf widenX64SrcMod_wp
    (f := fnU32MultiFill2) (by simp [widenX64SrcMod])
    rfl rfl rfl (fun _ _ _ _ _ hx => hx) bs (0x1000#64, 0x1040#64, 10#32, ()) 0x1000#64
    (array 0x1000#64 z10 ⋆ array 0x1040#64 n10 ⋆ array 0x1028#64 mid)
    (by decide) rfl
    (Q := fun rets m' => rets = (0x1000#64, ()) ∧
      (array 0x1000#64 z10 ⋆ array 0x1040#64 n10 ⋆ array 0x1028#64 mid) m')
    ?_ (fun _ _ h => h) (by decide)
  dsimp only [widenX64Γ, fnU32MultiFill2, multiFill2Spec]
  left
  refine ⟨xs, xs, array 0x1028#64 mid, rfl, by decide, rfl, hm0, ?_⟩
  intro ys0 ys1 hl0 hl1 hy m' hm'
  have h0 : ys0 = z10 :=
    List.ext_getElem (by simpa [xs, z10] using hl0) fun k hk hk' => by
      have hxs : k < xs.length := by
        have hlen : z10.length = xs.length := by decide
        omega
      have hk0 := (hy k hxs).1
      rw [List.getElem?_eq_getElem hk, Option.some.injEq] at hk0
      rw [hk0]; dsimp only [z10]; rw [List.getElem_replicate]
  have h1 : ys1 = n10 :=
    List.ext_getElem (by simpa [xs, n10] using hl1) fun k hk hk' => by
      have hxs : k < xs.length := by
        have hlen : n10.length = xs.length := by decide
        omega
      have hk1 := (hy k hxs).2
      rw [List.getElem?_eq_getElem hk, Option.some.injEq] at hk1
      rw [hk1]; dsimp only [n10]; rw [List.getElem_replicate]
  rw [h0, h1] at hm'; exact ⟨rfl, hm'⟩

theorem x64_fill2_ovlp_runs :
    let xs : List (Val i32) := List.replicate 7 7#32
    let bs := bytesOf xs
    Eventually (x64Target.mach.step widenX64Exec.host)
      (fun st => x64Target.mach.pc st = x64Init.ra0 ∧
        x64Target.mach.getGpr (x64Target.mach.data st) x64Init.ret0 = 0x1000#64 ∧
        (x64Target.mach.mem (x64Target.mach.data st) =⋆
          (array 0x1000#64 (zeroNegList 6) ⋆ emp) ⋆
          x64Target.Exit x64Init.sp0 (widenX64Exec.bound "u32_multi_fill2") ⋆ emp))
      (x64Target.mach.mkState
        (x64Init.initState (as := [i64, i64, i32]) (widenX64Exec.bound "u32_multi_fill2") bs
          (0x1000#64, 0x1004#64, 6#32, ()))
        (x64Target.mach.labelAddr widenX64Exec.host "u32_multi_fill2")) := by
  intro xs bs
  refine widenX64Exec.eventually_ret1_sep_i64 x64Init widenX64Γ
    widenX64SrcMod_acyclic widenX64SrcMod_wf widenX64SrcMod_wp
    (f := fnU32MultiFill2) (by simp [widenX64SrcMod])
    rfl rfl rfl (fun _ _ _ _ _ hx => hx) bs (0x1000#64, 0x1004#64, 6#32, ()) 0x1000#64
    (array 0x1000#64 (zeroNegList 6) ⋆ emp) (by decide) rfl
    (Q := fun rets m' => rets = (0x1000#64, ()) ∧ (array 0x1000#64 (zeroNegList 6) ⋆ emp) m')
    ?_ (fun _ _ h => h) (by decide)
  dsimp only [widenX64Γ, fnU32MultiFill2, multiFill2Spec]
  right
  refine ⟨6, xs, emp, by decide, by decide, by decide, rfl, rfl, ?_, fun m' hm' => ⟨rfl, hm'⟩⟩
  simpa [sep_emp] using array_bytes 0x1000#64 xs (by decide)

theorem x64_fill2_flat_eq (h : x64Target.toIsa.Hints) :
    compileFlatFn x64Target.toIsa x64LegalTarget h
        ⟨fnU32MultiFill2.name, fnU32MultiFill2.as, fnU32MultiFill2.rs,
          reifyFunc fnU32MultiFill2.body⟩ =
      compileFn x64Target.toIsa x64LegalTarget h fnU32MultiFill2 :=
  compileFlatFn_eq_compileFn _ _ _ _ (PassFlatKit.reifyFunc_wfCheck u32MultiFill2_wf)

#print axioms LeanQbe.T.TFlat.wfCheck_zeroPeelWith
#print axioms LeanQbe.T.Func.zeroPeel_wf
#print axioms LeanQbe.T.Func.zeroPeel_spec
#print axioms LeanQbe.T.Func.zeroPeel_callsOk
#print axioms u32Zero8_zp_spec
#print axioms u32Fill2_zp_disj
#print axioms u32Fill2_zp_ovlp
#print axioms x64_widen_code_eq
#print axioms x64_widen_bounds_eq
#print axioms x64_fill2_disj_runs
#print axioms x64_fill2_ovlp_runs
#print axioms x64_fill2_flat_eq

end LeanQbeTest.T.ZeroPeelWidenTest
