module

public import LeanQbe.T.Amd64.Isa
import LeanQbe.T.Amd64.IselLemmas5
import LeanQbe.T.Amd64.IselVecLemmas3
import LeanQbe.T.Amd64.FrameLemmas

/-!
# SysV x64 `Target` Assembly & Legalization Parity (`T12i`)

Assembles `x64Target : Target` from the pure `x64Isa` components and private verification theorems
(`x64_gprSpec`, `x64_vecSpec`, `x64_frameSpec`), preserving a strict module-system firewall against
downstream rebuilds when `*Lemmas*` proofs change.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64

open LeanQbe.T

/-! ## 1. Target Assembly (`x64Target`) behind Module-System Proof Firewall -/

/-- Firewall theorem exposing `x64GprSpec` without exporting `*Lemmas*` proof terms. -/
public theorem x64_gprSpec : GprTarget x64Mach x64Gpr x64Scratch :=
  x64GprSpec

/-- Firewall theorem exposing `x64VecSpec` without exporting `*Lemmas*` proof terms. -/
public theorem x64_vecSpec :
    VecTarget x64Mach x64Vec x64CondReads x64Frame.sp x64Scratch x64FramePreds.spOk :=
  x64VecSpec

/-- Firewall theorem exposing `x64FrameSpec.spec` without exporting `FrameLemmas`. -/
public theorem x64_frameSpec : FrameSpec x64Mach x64Frame x64CondReads x64FramePreds :=
  x64FrameSpec.spec

/-- SysV x64 `FrameTarget` built from public `x64FramePreds` and `x64_frameSpec`. -/
def x64FrameTarget : FrameTarget x64Mach x64Frame x64CondReads where
  toFramePreds := x64FramePreds
  spec := x64_frameSpec

/-- Verified SysV x64 `Target` bundling scalar GPR, vector (`xmm`/`ymm`/`zmm`), and stack frame
specifications. -/
@[reducible] def x64Target : Target where
  toIsa := x64Isa
  mach := x64Mach
  gprSpec := x64_gprSpec
  frameSpec := x64FrameTarget
  vecSpec := x64_vecSpec

theorem x64Target_toIsa :
    x64Target.toIsa =
      { Reg := Reg64, VReg := RegMm, Cond := CondCode, Directive := Directive,
        gpr := x64Gpr, vec := x64Vec, frame := x64Frame,
        supportsAddrDisp := x64SupportsAddrDisp,
        supportsAddrIdx := x64SupportsAddrIdx,
        supportsTestFuse := true,
        supportsCmpMem := x64SupportsCmpMem,
        supportsTestMem := x64SupportsCmpMem } :=
  rfl

/-! ## 2. Parity Theorems (`x64LegalTarget` ↔ `x64Target.toIsa`) & Kernel Checks -/

theorem x64IsI32Vec_eq (t : Ty) : x64IsI32Vec t = isI32Vec t := by
  induction t with
  | bool | float _ => rfl
  | bits n =>
    by_cases hn : n = 32
    · subst hn; rfl
    · unfold x64IsI32Vec isI32Vec; simp [hn]
  | pair a b iha _ => simp [x64IsI32Vec, isI32Vec, iha]

theorem x64IsF32Vec_eq (t : Ty) : x64IsF32Vec t = isF32Vec t := by
  induction t with
  | bool | bits _ => rfl
  | float f => cases f <;> rfl
  | pair a b iha _ => simp [x64IsF32Vec, isF32Vec, iha]

private theorem matchVecOf_i32_f32_some_iff :
    ∀ t : Ty, (matchVecOf [i32, f32] t).isSome = (isI32Vec t || isF32Vec t)
  | .bool => rfl
  | .bits n => by
    by_cases hn : n = 32
    · subst hn; simp [matchVecOf, isI32Vec]
    · simp [matchVecOf, i32, f32, isI32Vec, isF32Vec, hn]
  | .float f => by
    cases f <;> simp [matchVecOf, i32, f32, isI32Vec, isF32Vec]
  | .pair a b => by
    have hnot : Ty.pair a b ∉ [i32, f32] := by simp [i32, f32]
    have iha := matchVecOf_i32_f32_some_iff a
    simp only [matchVecOf, hnot, ↓reduceIte, isI32Vec, isF32Vec]
    by_cases hab : a == b
    · cases hma : matchVecOf [i32, f32] a with
      | none =>
        have hfalse : (isI32Vec a || isF32Vec a) = false := by
          simpa [hma] using iha.symm
        simp only [Bool.or_eq_false_iff] at hfalse
        simp [hab, hfalse.1, hfalse.2]
      | some _ =>
        have htrue : (isI32Vec a || isF32Vec a) = true := by
          simpa [hma] using iha.symm
        rcases Bool.or_eq_true_iff.mp htrue with h1 | h2
        · simp [hab, h1]
        · simp [hab, h2]
    · simp [hab]

private theorem hasLegalLeaves_of_i32_f32 :
    ∀ u : Ty, (isI32Vec u || isF32Vec u) = true → x64LegalTarget.hasLegalLeaves u = true
  | .bool, h => by simp [isI32Vec, isF32Vec] at h
  | .bits n, h => by
    have hn : n = 32 := by
      by_cases hn32 : n = 32
      · exact hn32
      · simp [isI32Vec, isF32Vec, hn32] at h
    subst hn; decide
  | .float f, h => by
    cases f <;> simp [isI32Vec, isF32Vec] at h
    decide
  | .pair a b, h => by
    simp only [isI32Vec, isF32Vec] at h
    rcases Bool.or_eq_true_iff.mp h with hx | hx <;>
      simp only [Bool.and_eq_true, beq_iff_eq] at hx <;>
      obtain ⟨rfl, hx'⟩ := hx
    · have hl := hasLegalLeaves_of_i32_f32 a (by simp [hx'])
      simp [LegalTarget.hasLegalLeaves, hl]
    · have hl := hasLegalLeaves_of_i32_f32 a (by simp [hx'])
      simp [LegalTarget.hasLegalLeaves, hl]

theorem x64KeepsPacked_iff (t : Ty) :
    x64LegalTarget.keepsPacked t = true ↔ ∃ a b, t = .pair a b ∧ x64IsPackedWidth t = true := by
  cases t with
  | bool | bits _ | float _ =>
    simp [LegalTarget.keepsPacked, PackOracle.isPackedPair]
  | pair a b =>
    have hms := matchVecOf_i32_f32_some_iff (.pair a b)
    simp only [LegalTarget.keepsPacked, x64LegalTarget, LegalTarget.x64,
      PackOracle.isPackedPair, PackOracle.g13, x64IsPackedWidth, x64IsVecBits,
      x64IsI32Vec_eq, x64IsF32Vec_eq]
    constructor
    · intro h
      simp only [Bool.and_eq_true] at h
      rcases h with ⟨⟨_, hpack⟩, _⟩
      cases hm : matchVecOf [i32, f32] (.pair a b) with
      | none => simp [hm] at hpack
      | some _ =>
        simp only [hm] at hpack
        have hvec : (isI32Vec (.pair a b) || isF32Vec (.pair a b)) = true := by
          simpa [hm] using hms.symm
        refine ⟨a, b, rfl, ?_⟩
        rw [Bool.and_eq_true]
        exact ⟨hvec, by simpa [List.contains_eq_mem, or_assoc] using hpack⟩
    · rintro ⟨a', b', heq, hpw⟩
      rw [Ty.pair.injEq] at heq
      rcases heq with ⟨rfl, rfl⟩
      simp only [Bool.and_eq_true] at hpw
      obtain ⟨hvec, hsz⟩ := hpw
      have hms' : (matchVecOf [i32, f32] (.pair a b)).isSome = true := by rw [hms]; exact hvec
      obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hms'
      rw [Bool.and_eq_true, Bool.and_eq_true]
      refine ⟨⟨rfl, ?_⟩, hasLegalLeaves_of_i32_f32 _ hvec⟩
      simp only [hp]
      simpa [List.contains_eq_mem, or_assoc] using hsz

/-- Parity theorem tying `x64LegalTarget.isLegalOp` on packed vectors and `x64Vec.supportsVecOp`. -/
theorem x64SupportsOp_parity (t : Ty) (hp : x64LegalTarget.keepsPacked t = true)
    (imm : BitVec 8)
    (u1 : Tup (Arg (fun _ => Unit)) [t])
    (u2 : Tup (Arg (fun _ => Unit)) [t, t])
    (u3 : Tup (Arg (fun _ => Unit)) [t, t, t])
    (uSha1 : Tup (Arg (fun _ => Unit)) [v4i32, v4i32, v4i32])
    (uSha2 : Tup (Arg (fun _ => Unit)) [v4i32, v4i32]) :
    (x64Target.toIsa.supportsOp (.copy t) u1 = true ↔
      x64LegalTarget.isLegalOp (.copy t) false = true) ∧
    (x64Target.toIsa.supportsOp (.add t) u2 = true ↔
      x64LegalTarget.isLegalOp (.add t) false = true) ∧
    (x64Target.toIsa.supportsOp (.and t) u2 = true ↔
      x64LegalTarget.isLegalOp (.and t) false = true) ∧
    (x64Target.toIsa.supportsOp (.or t) u2 = true ↔
      x64LegalTarget.isLegalOp (.or t) false = true) ∧
    (x64Target.toIsa.supportsOp (.xor t) u2 = true ↔
      x64LegalTarget.isLegalOp (.xor t) false = true) ∧
    (x64Target.toIsa.supportsOp (.not t) u1 = true ↔
      x64LegalTarget.isLegalOp (.not t) false = true) ∧
    (x64Target.toIsa.supportsOp (.ternlog t imm) u3 = true ↔
      x64LegalTarget.isLegalOp (.ternlog t imm) false = true) ∧
    (x64Target.toIsa.supportsOp (.shufd t imm) u1 = true ↔
      x64LegalTarget.isLegalOp (.shufd t imm) false = true) ∧
    (x64Target.toIsa.supportsOp (.shufb t) u2 = true ↔
      x64LegalTarget.isLegalOp (.shufb t) false = true) ∧
    (x64Target.toIsa.supportsOp (.alignr t imm) u2 = true ↔
      x64LegalTarget.isLegalOp (.alignr t imm) false = true) ∧
    (x64Target.toIsa.supportsOp (.blendw t imm) u2 = true ↔
      x64LegalTarget.isLegalOp (.blendw t imm) false = true) ∧
    (x64Target.toIsa.supportsOp (.fadd t) u2 = true ↔
      x64LegalTarget.isLegalOp (.fadd t) false = true) ∧
    (x64Target.toIsa.supportsOp (.fsub t) u2 = true ↔
      x64LegalTarget.isLegalOp (.fsub t) false = true) ∧
    (x64Target.toIsa.supportsOp .sha256rnds2 uSha1 = false ∧
      x64LegalTarget.isLegalOp .sha256rnds2 false = false) ∧
    (x64Target.toIsa.supportsOp .sha256msg1 uSha2 = false ∧
      x64LegalTarget.isLegalOp .sha256msg1 false = false) ∧
    (x64Target.toIsa.supportsOp .sha256msg2 uSha2 = false ∧
      x64LegalTarget.isLegalOp .sha256msg2 false = false) := by
  obtain ⟨a, b, rfl, hpw⟩ := (x64KeepsPacked_iff t).mp hp
  have hpw' := hpw
  simp only [x64IsPackedWidth, Bool.and_eq_true] at hpw'
  have hslot : (x64VecSlotWidth (.pair a b)).isSome = true := by
    simp only [x64VecSlotWidth, hpw'.1, ↓reduceIte]
    rcases Bool.or_eq_true_iff.mp hpw'.2 with h1 | h2
    · rcases Bool.or_eq_true_iff.mp h1 with h128 | h256
      · rw [beq_iff_eq.mp h128]; rfl
      · rw [beq_iff_eq.mp h256]; rfl
    · rw [beq_iff_eq.mp h2]; rfl
  have hbank : x64Target.toIsa.hasBank (.pair a b) = true := hslot
  have hsz_mod : ((Ty.pair a b).size != 0 && (Ty.pair a b).size % 128 == 0) = true := by
    rcases Bool.or_eq_true_iff.mp hpw'.2 with h1 | h2
    · rcases Bool.or_eq_true_iff.mp h1 with h128 | h256
      · rw [beq_iff_eq.mp h128]; rfl
      · rw [beq_iff_eq.mp h256]; rfl
    · rw [beq_iff_eq.mp h2]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ([a.pair b].all x64Target.toIsa.hasBank &&
        [a.pair b].all x64Target.toIsa.hasBank &&
        (false || x64IsPackedWidth (a.pair b))) = true ↔
      x64LegalTarget.keepsPacked (a.pair b) = true
    simp only [List.all_cons, List.all_nil, Bool.and_true, hbank, Bool.false_or, hpw, hp]
  · change ([a.pair b, a.pair b].all x64Target.toIsa.hasBank &&
        [a.pair b].all x64Target.toIsa.hasBank &&
        (false || (x64IsI32Vec (a.pair b) &&
          ((a.pair b).size == 128 || (a.pair b).size == 256 || (a.pair b).size == 512)))) = true ↔
      (x64LegalTarget.keepsPacked (a.pair b) && isI32Vec (a.pair b)) = true
    simp only [List.all_cons, List.all_nil, Bool.and_true, hbank, Bool.false_or, hp,
      x64IsI32Vec_eq, hpw'.2, Bool.and_true, Bool.true_and]
  · change ([a.pair b, a.pair b].all x64Target.toIsa.hasBank &&
        [a.pair b].all x64Target.toIsa.hasBank &&
        (false || x64IsPackedWidth (a.pair b))) = true ↔
      (x64LegalTarget.keepsPacked (a.pair b) && true) = true
    simp only [List.all_cons, List.all_nil, Bool.and_true, hbank, Bool.false_or, hpw, hp]
  · change ([a.pair b, a.pair b].all x64Target.toIsa.hasBank &&
        [a.pair b].all x64Target.toIsa.hasBank &&
        (false || x64IsPackedWidth (a.pair b))) = true ↔
      (x64LegalTarget.keepsPacked (a.pair b) && true) = true
    simp only [List.all_cons, List.all_nil, Bool.and_true, hbank, Bool.false_or, hpw, hp]
  · change ([a.pair b, a.pair b].all x64Target.toIsa.hasBank &&
        [a.pair b].all x64Target.toIsa.hasBank &&
        (false || x64IsPackedWidth (a.pair b))) = true ↔
      (x64LegalTarget.keepsPacked (a.pair b) && true) = true
    simp only [List.all_cons, List.all_nil, Bool.and_true, hbank, Bool.false_or, hpw, hp]
  · change ([a.pair b].all x64Target.toIsa.hasBank &&
        [a.pair b].all x64Target.toIsa.hasBank &&
        (false || x64IsPackedWidth (a.pair b))) = true ↔
      (x64LegalTarget.keepsPacked (a.pair b) && true) = true
    simp only [List.all_cons, List.all_nil, Bool.and_true, hbank, Bool.false_or, hpw, hp]
  · change ([a.pair b, a.pair b, a.pair b].all x64Target.toIsa.hasBank &&
        [a.pair b].all x64Target.toIsa.hasBank &&
        (false || x64IsPackedWidth (a.pair b))) = true ↔
      (x64LegalTarget.keepsPacked (a.pair b) && true) = true
    simp only [List.all_cons, List.all_nil, Bool.and_true, hbank, Bool.false_or, hpw, hp]
  · change ([a.pair b].all x64Target.toIsa.hasBank &&
        [a.pair b].all x64Target.toIsa.hasBank &&
        (false || (x64IsVecBits (a.pair b) && (a.pair b).size == 128))) = true ↔
      (x64LegalTarget.keepsPacked (a.pair b) && (a.pair b).size != 0 &&
        (a.pair b).size % 128 == 0 && (a.pair b).size == 128) = true
    simp only [List.all_cons, List.all_nil, Bool.and_true, hbank, Bool.false_or, hpw'.1,
      Bool.true_and, hp]
    cases h128 : (a.pair b).size == 128
    · simp
    · simp [hsz_mod]
  · change ([a.pair b, a.pair b].all x64Target.toIsa.hasBank &&
        [a.pair b].all x64Target.toIsa.hasBank &&
        (false || (x64IsVecBits (a.pair b) && (a.pair b).size == 128))) = true ↔
      (x64LegalTarget.keepsPacked (a.pair b) && (a.pair b).size != 0 &&
        (a.pair b).size % 128 == 0 && (a.pair b).size == 128) = true
    simp only [List.all_cons, List.all_nil, Bool.and_true, hbank, Bool.false_or, hpw'.1,
      Bool.true_and, hp]
    cases h128 : (a.pair b).size == 128
    · simp
    · simp [hsz_mod]
  · change ([a.pair b, a.pair b].all x64Target.toIsa.hasBank &&
        [a.pair b].all x64Target.toIsa.hasBank &&
        (false || (x64IsVecBits (a.pair b) && (a.pair b).size == 128))) = true ↔
      (x64LegalTarget.keepsPacked (a.pair b) && (a.pair b).size != 0 &&
        (a.pair b).size % 128 == 0 && (a.pair b).size == 128) = true
    simp only [List.all_cons, List.all_nil, Bool.and_true, hbank, Bool.false_or, hpw'.1,
      Bool.true_and, hp]
    cases h128 : (a.pair b).size == 128
    · simp
    · simp [hsz_mod]
  · change ([a.pair b, a.pair b].all x64Target.toIsa.hasBank &&
        [a.pair b].all x64Target.toIsa.hasBank &&
        (false || (x64IsVecBits (a.pair b) && (a.pair b).size == 128))) = true ↔
      (x64LegalTarget.keepsPacked (a.pair b) && (a.pair b).size != 0 &&
        (a.pair b).size % 128 == 0 && (a.pair b).size == 128) = true
    simp only [List.all_cons, List.all_nil, Bool.and_true, hbank, Bool.false_or, hpw'.1,
      Bool.true_and, hp]
    cases h128 : (a.pair b).size == 128
    · simp
    · simp [hsz_mod]
  · change ([a.pair b, a.pair b].all x64Target.toIsa.hasBank &&
        [a.pair b].all x64Target.toIsa.hasBank &&
        (false || (x64IsF32Vec (a.pair b) && (a.pair b).size == 128))) = true ↔
      (x64LegalTarget.keepsPacked (a.pair b) &&
        (isF32Vec (a.pair b) && (a.pair b).size == 128)) = true
    simp only [List.all_cons, List.all_nil, Bool.and_true, hbank, Bool.false_or, hp,
      x64IsF32Vec_eq, Bool.true_and]
  · change ([a.pair b, a.pair b].all x64Target.toIsa.hasBank &&
        [a.pair b].all x64Target.toIsa.hasBank &&
        (false || (x64IsF32Vec (a.pair b) && (a.pair b).size == 128))) = true ↔
      (x64LegalTarget.keepsPacked (a.pair b) &&
        (isF32Vec (a.pair b) && (a.pair b).size == 128)) = true
    simp only [List.all_cons, List.all_nil, Bool.and_true, hbank, Bool.false_or, hp,
      x64IsF32Vec_eq, Bool.true_and]
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

abbrev v8i32 := Ty.vec 3 i32
abbrev v16i32 := Ty.vec 4 i32
abbrev v2i32 := Ty.vec 1 i32
abbrev v2f32 := Ty.vec 1 f32
abbrev v8f32 := Ty.vec 3 f32
abbrev v16f32 := Ty.vec 4 f32

/-- Kernel `rfl` checks aligning `x64LegalTarget` and `x64Target.toIsa` (`[128, 256, 512]`
`i32`/`f32` vectors, 128-bit SSE/float restrictions, no SHA-NI, and `[8, 16, 32, 64]` scalar). -/
theorem x64SupportsOp_checks :
    x64LegalTarget.valid = true ∧
    x64LegalTarget.keepsPacked v4i32 = true ∧
    x64LegalTarget.keepsPacked v8i32 = true ∧
    x64LegalTarget.keepsPacked v16i32 = true ∧
    x64LegalTarget.keepsPacked v4f32 = true ∧
    x64LegalTarget.keepsPacked v8f32 = true ∧
    x64LegalTarget.keepsPacked v16f32 = true ∧
    x64LegalTarget.keepsPacked v2i32 = false ∧
    x64LegalTarget.keepsPacked v2f32 = false ∧
    x64LegalTarget.supportsTy (.float .s) = true ∧
    x64LegalTarget.supportsTy (.float .d) = false ∧
    x64LegalTarget.isLegalOp .sha256rnds2 false = false ∧
    x64Target.toIsa.supportsOp .sha256rnds2 (.var (), .var (), .var (), ()) = false ∧
    x64LegalTarget.isLegalOp .sha256msg1 false = false ∧
    x64Target.toIsa.supportsOp .sha256msg1 (.var (), .var (), ()) = false ∧
    x64LegalTarget.isLegalOp .sha256msg2 false = false ∧
    x64Target.toIsa.supportsOp .sha256msg2 (.var (), .var (), ()) = false ∧
    x64LegalTarget.isLegalOp (.shufd v4i32 0x4e#8) false = true ∧
    x64LegalTarget.isLegalOp (.shufd v8i32 0x4e#8) false = false ∧
    x64LegalTarget.isLegalOp (.shufd v16i32 0x4e#8) false = false ∧
    x64LegalTarget.isLegalOp (.shufb v4i32) false = true ∧
    x64LegalTarget.isLegalOp (.shufb v8i32) false = false ∧
    x64LegalTarget.isLegalOp (.alignr v4i32 8#8) false = true ∧
    x64LegalTarget.isLegalOp (.alignr v8i32 8#8) false = false ∧
    x64LegalTarget.isLegalOp (.blendw v4i32 0xf0#8) false = true ∧
    x64LegalTarget.isLegalOp (.blendw v8i32 0xf0#8) false = false ∧
    x64LegalTarget.isLegalOp (.fadd v4f32) false = true ∧
    x64LegalTarget.isLegalOp (.fadd v8f32) false = false ∧
    x64Target.toIsa.supportsOp (.fadd v8f32) (.var (), .var (), ()) = false ∧
    x64LegalTarget.isLegalOp (.fsub v4f32) false = true ∧
    x64LegalTarget.isLegalOp (.fsub v16f32) false = false ∧
    x64LegalTarget.isLegalOp (.rotr v8i32) true = true ∧
    x64Target.toIsa.supportsOp (.rotr v8i32)
      (.var (), .imm (((7#32, 7#32), (7#32, 7#32)), ((7#32, 7#32), (7#32, 7#32))), ()) = true ∧
    x64Target.toIsa.supportsOp (.lshr v4i32)
      (.var (), .imm ((1#32, 1#32), (2#32, 2#32)), ()) = false ∧
    x64Gpr.supportsScalarOp (.add i8) (.var (), .var (), ()) = true ∧
    x64Gpr.supportsScalarOp (.add i64) (.var (), .var (), ()) = true ∧
    x64Gpr.supportsScalarOp (.bswap i8) (.var (), ()) = false ∧
    x64Gpr.supportsScalarOp (.bswap i16) (.var (), ()) = true ∧
    x64Gpr.supportsScalarOp (.addc 32) (.var (), .var (), .var (), ()) = true ∧
    x64Gpr.supportsScalarOp (.addc 16) (.var (), .var (), .var (), ()) = false ∧
    x64Gpr.supportsScalarOp (.umulw 64) (.var (), .var (), ()) = true ∧
    x64Gpr.supportsScalarOp (.fshl 32) (.var (), .var (), .var (), ()) = true ∧
    x64Gpr.supportsScalarOp (.clz 8) (.var (), ()) = true ∧
    x64Gpr.supportsScalarOp (.clz 16) (.var (), ()) = true ∧
    x64Gpr.supportsScalarOp (.clz 32) (.var (), ()) = true ∧
    x64Gpr.supportsScalarOp (.clz 64) (.var (), ()) = true ∧
    x64Gpr.supportsScalarOp (.cls 8) (.var (), ()) = true ∧
    x64Gpr.supportsScalarOp (.cls 64) (.var (), ()) = true ∧
    x64Gpr.supportsScalarOp (.ctz 8) (.var (), ()) = true ∧
    x64Gpr.supportsScalarOp (.ctz 16) (.var (), ()) = true ∧
    x64Gpr.supportsScalarOp (.ctz 32) (.var (), ()) = true ∧
    x64Gpr.supportsScalarOp (.ctz 64) (.var (), ()) = true ∧
    x64Gpr.supportsScalarOp (.popcnt 8) (.var (), ()) = true ∧
    x64Gpr.supportsScalarOp (.popcnt 16) (.var (), ()) = true ∧
    x64Gpr.supportsScalarOp (.popcnt 32) (.var (), ()) = true ∧
    x64Gpr.supportsScalarOp (.popcnt 64) (.var (), ()) = true ∧
    x64Gpr.supportsScalarOp (.rbit 64) (.var (), ()) = false ∧
    x64LegalTarget.isLegalOp (.clz 8) false = true ∧
    x64Target.toIsa.supportsOp (.clz 8) (.var (), ()) = true ∧
    x64LegalTarget.isLegalOp (.cls 64) false = true ∧
    x64Target.toIsa.supportsOp (.cls 64) (.var (), ()) = true ∧
    x64LegalTarget.isLegalOp (.ctz 16) false = true ∧
    x64Target.toIsa.supportsOp (.ctz 16) (.var (), ()) = true ∧
    x64LegalTarget.isLegalOp (.popcnt 32) false = true ∧
    x64Target.toIsa.supportsOp (.popcnt 32) (.var (), ()) = true ∧
    x64Target.toIsa.supportsOp (.rbit 64) (.var (), ()) = false ∧
    x64Gpr.supportsScalarOp (.udiv0 64) (.var (), .var (), ()) = false ∧
    x64Gpr.supportsScalarOp (.fadd (.float .s)) (.var (), .var (), ()) = false := by
  repeat' (first | refine ⟨rfl, ?_⟩ | exact rfl)

end LeanQbe.T.Amd64
