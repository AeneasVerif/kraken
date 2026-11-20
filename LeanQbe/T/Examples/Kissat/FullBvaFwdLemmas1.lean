module

public import LeanQbe.T.Examples.Kissat.Full
public import LeanQbe.T.Examples.Kissat.FullArena
public import LeanQbe.T.Examples.Kissat.FullSpec3
public import LeanQbe.T.Logic.C0Step
public import LeanQbe.T.Logic.C0Agrees
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Forward Subsumption & BVA Specs and Lemmas — Part 1 (`Stage 4`)

Defines:
1. Canonical shared Stage-4 invariants (`FullLitMarksClear`, `FullArenaVarsNodup`,
   `FullLastLearnedWf`, `FullExtScratchOk`, `FullSparseInv`, `FullDenseInv`) and parametric
   callee + exported `Spec`s in `namespace FullBvaFwdSpecs`.
2. Strictly scoped `FullBvaFwdTactics` (`bf_steps`, bitvector arithmetic helpers).
3. Pure entailment / resolution / BVA fresh-variable soundness lemmas (`entails_unit_of_bin_pair`,
   `entails_strengthen_of_bin`, `entails_strengthen_of_clause`, `bvaExtendFormula`,
   `extUnsatSound_bvaExtendFormula`).
4. Dense watch-slice compaction, arena-shrinking (`PH_SHRK` + `0xFFFFFFFF#32` sentinel),
   garbage-marking at level 0, `fullArenaScanRefs` successor, and fresh-variable initialization
   preservation lemmas for `FullDenseInv`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Canonical Stage-4 invariants & `FullBvaFwdSpecs` -/

namespace FullBvaFwdSpecs

abbrev FullLitMarksClear := LeanQbe.T.Examples.Kissat.Full.FullLitMarksClear
abbrev FullArenaVarsNodup := LeanQbe.T.Examples.Kissat.Full.FullArenaVarsNodup
abbrev FullLastLearnedWf := LeanQbe.T.Examples.Kissat.Full.FullLastLearnedWf
abbrev FullExtScratchOk := LeanQbe.T.Examples.Kissat.Full.FullExtScratchOk
abbrev FullSparseInv := LeanQbe.T.Examples.Kissat.Full.FullSparseInv
abbrev FullDenseInv := LeanQbe.T.Examples.Kissat.Full.FullDenseInv
abbrev fullArenaNextSpec := LeanQbe.T.Examples.Kissat.Full.fullArenaNextSpec
abbrev fullHeapPushSpec := LeanQbe.T.Examples.Kissat.Full.fullHeapPushSpec
abbrev fullUnwatchLargeSpec := LeanQbe.T.Examples.Kissat.Full.fullUnwatchLargeSpec
abbrev fullHasBinSpec := LeanQbe.T.Examples.Kissat.Full.fullHasBinSpec
abbrev fullAddUnitSpec := LeanQbe.T.Examples.Kissat.Full.fullAddUnitSpec
abbrev fullAddBinSpec := LeanQbe.T.Examples.Kissat.Full.fullAddBinSpec
abbrev fullDeleteBinarySpec := LeanQbe.T.Examples.Kissat.Full.fullDeleteBinarySpec
abbrev fullFwdDedupBinsSpec := LeanQbe.T.Examples.Kissat.Full.fullFwdDedupBinsSpec
abbrev fullFwdCheckClSpec := LeanQbe.T.Examples.Kissat.Full.fullFwdCheckClSpec
abbrev fullForwardSubSpec := LeanQbe.T.Examples.Kissat.Full.fullForwardSubSpec
abbrev fullInitFreshVarSpec := LeanQbe.T.Examples.Kissat.Full.fullInitFreshVarSpec
abbrev fullBvaTryLitSpec := LeanQbe.T.Examples.Kissat.Full.fullBvaTryLitSpec
abbrev fullFactorSpec := LeanQbe.T.Examples.Kissat.Full.fullFactorSpec

end FullBvaFwdSpecs

/-! ## 2. Scoped tactic & bitvector helpers (`FullBvaFwdTactics`) -/

namespace FullBvaFwdTactics

theorem strip_le_32_64 {P : Prop} (h : P) : 32 ≤ 64 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_32 {P : Prop} (h : P) : 8 ≤ 32 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_64 {P : Prop} (h : P) : 8 ≤ 64 ∧ P := ⟨by decide, h⟩

scoped macro "bf_strip" : tactic =>
  `(tactic| first | apply strip_le_32_64 | apply strip_le_8_32 | apply strip_le_8_64)
scoped macro "bf_unmdata" : tactic =>
  `(tactic| first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)
scoped macro "bf_step" : tactic => `(tactic| ((try bf_unmdata); (repeat bf_strip); c0_step))
scoped macro "bf_steps" : tactic =>
  `(tactic| (
      (try bf_unmdata)
      (repeat bf_strip)
      c0_steps
      repeat (any_goals (bf_strip; repeat bf_strip); c0_steps)))

theorem strip_wp {Γ rs Q X e m} (h : wp (rs := rs) Γ Q X e m) : wp Γ Q X e m := h
theorem strip_fwp {as rs Γ f args m Q X}
    (h : Func.wp (as := as) (rs := rs) Γ f args m Q X) : Func.wp Γ f args m Q X := h
theorem strip_le_wp {a b : Nat} {P : Prop} (h : a ≤ b) (hp : P) : a ≤ b ∧ P := ⟨h, hp⟩

section BfFastWp
variable {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
local notation "K " t => Tup Val [t] → Expr Val Cont rs
theorem bf_wp_copy {t} {a : Arg Val t} {k : K t} (h : wp Γ Q X (k (a.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.copy t) (a, ())) k) m := by simpa only [wp_let_copy_eq] using h
theorem bf_wp_add {n} {a b : Arg Val (.bits n)} {k : K (.bits n)}
    (h : wp Γ Q X (k (a.val + b.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.add _) (a, b, ())) k) m := by
  simpa only [wp_let_add_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2] using h
theorem bf_wp_sub {n} {a b : Arg Val (.bits n)} {k : K (.bits n)}
    (h : wp Γ Q X (k (a.val - b.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sub _) (a, b, ())) k) m := by
  simpa only [wp_let_sub_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2] using h
theorem bf_wp_mul {n} {a b : Arg Val (.bits n)} {k : K (.bits n)}
    (h : wp Γ Q X (k (a.val * b.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.mul _) (a, b, ())) k) m := by
  simpa only [wp_let_mul_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2] using h
theorem bf_wp_and {n} {a b : Arg Val (.bits n)} {k : K (.bits n)}
    (h : wp Γ Q X (k (a.val &&& b.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.and _) (a, b, ())) k) m := by simpa only [wp_let_and_eq, lift2] using h
theorem bf_wp_or {n} {a b : Arg Val (.bits n)} {k : K (.bits n)}
    (h : wp Γ Q X (k (a.val ||| b.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.or _) (a, b, ())) k) m := by simpa only [wp_let_or_eq, lift2] using h
theorem bf_wp_xor {n} {a b : Arg Val (.bits n)} {k : K (.bits n)}
    (h : wp Γ Q X (k (a.val ^^^ b.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.xor _) (a, b, ())) k) m := by simpa only [wp_let_xor_eq, lift2] using h
theorem bf_wp_not {n} {a : Arg Val (.bits n)} {k : K (.bits n)}
    (h : wp Γ Q X (k (~~~a.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.not _) (a, ())) k) m := by simpa only [wp_let_not_eq, lift1] using h
theorem bf_wp_shl {n} {a b : Arg Val (.bits n)} {k : K (.bits n)}
    (h : wp Γ Q X (k (a.val <<< (b.val.toNat % n), ())) m) :
    wp Γ Q X (.let_ (Op.mk (.shl _) (a, b, ())) k) m := by
  simpa only [wp_let_shl_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2] using h
theorem bf_wp_shl1_64 {a : Arg Val (.bits 64)} {k : K (.bits 64)}
    (h : wp Γ Q X (k (a.val <<< (1 : Nat), ())) m) :
    wp Γ Q X (.let_ (Op.mk (.shl _) (a, Arg.imm 1#64, ())) k) m :=
  bf_wp_shl (by simpa only [Arg.val_imm, BitVec.reduceToNat, Nat.reduceMod] using h)
theorem bf_wp_shl1_64_v {a : Arg Val (.bits 64)} {k : K (.bits 64)}
    (h : wp Γ Q X (k (a.val <<< (1 : Nat), ())) m) :
    wp Γ Q X (.let_ (Op.mk (.shl _) (a, Arg.var 1#64, ())) k) m :=
  bf_wp_shl (by simpa only [Arg.val_var, BitVec.reduceToNat, Nat.reduceMod] using h)
theorem bf_wp_shl2_64 {a : Arg Val (.bits 64)} {k : K (.bits 64)}
    (h : wp Γ Q X (k (a.val <<< (2 : Nat), ())) m) :
    wp Γ Q X (.let_ (Op.mk (.shl _) (a, Arg.imm 2#64, ())) k) m :=
  bf_wp_shl (by simpa only [Arg.val_imm, BitVec.reduceToNat, Nat.reduceMod] using h)
theorem bf_wp_shl2_64_v {a : Arg Val (.bits 64)} {k : K (.bits 64)}
    (h : wp Γ Q X (k (a.val <<< (2 : Nat), ())) m) :
    wp Γ Q X (.let_ (Op.mk (.shl _) (a, Arg.var 2#64, ())) k) m :=
  bf_wp_shl (by simpa only [Arg.val_var, BitVec.reduceToNat, Nat.reduceMod] using h)
theorem bf_wp_shl1_32 {a : Arg Val (.bits 32)} {k : K (.bits 32)}
    (h : wp Γ Q X (k (a.val <<< (1 : Nat), ())) m) :
    wp Γ Q X (.let_ (Op.mk (.shl _) (a, Arg.imm 1#32, ())) k) m :=
  bf_wp_shl (by simpa only [Arg.val_imm, BitVec.reduceToNat, Nat.reduceMod] using h)
theorem bf_wp_shl1_32_v {a : Arg Val (.bits 32)} {k : K (.bits 32)}
    (h : wp Γ Q X (k (a.val <<< (1 : Nat), ())) m) :
    wp Γ Q X (.let_ (Op.mk (.shl _) (a, Arg.var 1#32, ())) k) m :=
  bf_wp_shl (by simpa only [Arg.val_var, BitVec.reduceToNat, Nat.reduceMod] using h)
theorem bf_wp_lshr1_32 {a : Arg Val (.bits 32)} {k : K (.bits 32)}
    (h : wp Γ Q X (k (a.val >>> 1, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.lshr _) (a, Arg.imm 1#32, ())) k) m := by
  simpa only [wp_let_lshr_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val_imm,
    BitVec.reduceToNat, Nat.reduceMod] using h
theorem bf_wp_lshr1_32_v {a : Arg Val (.bits 32)} {k : K (.bits 32)}
    (h : wp Γ Q X (k (a.val >>> 1, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.lshr _) (a, Arg.var 1#32, ())) k) m := by
  simpa only [wp_let_lshr_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val_var,
    BitVec.reduceToNat, Nat.reduceMod] using h
theorem bf_wp_zext32_64 {a : Arg Val (.bits 32)} {k : K (.bits 64)}
    (h : wp Γ Q X (k (a.val.setWidth 64, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.zext 32 64) (a, ())) k) m := by
  rw [wp_let_zext_eq]; exact ⟨by decide, h⟩
theorem bf_wp_zext8_32 {a : Arg Val (.bits 8)} {k : K (.bits 32)}
    (h : wp Γ Q X (k (a.val.setWidth 32, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.zext 8 32) (a, ())) k) m := by
  rw [wp_let_zext_eq]; exact ⟨by decide, h⟩
theorem bf_wp_zext8_32_0 {k : K (.bits 32)} (h : wp Γ Q X (k (0#32, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.zext 8 32) (Arg.imm 0#8, ())) k) m := by
  simpa only [wp_let_zext_eq] using ⟨by decide, h⟩
theorem bf_wp_zext8_32_0_v {k : K (.bits 32)} (h : wp Γ Q X (k (0#32, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.zext 8 32) (Arg.var 0#8, ())) k) m := by
  simpa only [wp_let_zext_eq] using ⟨by decide, h⟩
theorem bf_wp_sext32_64 {a : Arg Val (.bits 32)} {k : K (.bits 64)}
    (h : wp Γ Q X (k (a.val.signExtend 64, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sext 32 64) (a, ())) k) m := by
  rw [wp_let_sext_eq]; exact ⟨by decide, h⟩
theorem bf_wp_sext32_64_0 {k : K (.bits 64)} (h : wp Γ Q X (k (0#64, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sext 32 64) (Arg.imm 0#32, ())) k) m := by
  simpa only [wp_let_sext_eq] using ⟨by decide, h⟩
theorem bf_wp_sext32_64_1 {k : K (.bits 64)} (h : wp Γ Q X (k (1#64, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sext 32 64) (Arg.imm 1#32, ())) k) m := by
  simpa only [wp_let_sext_eq] using ⟨by decide, h⟩
theorem bf_wp_sext32_64_2 {k : K (.bits 64)} (h : wp Γ Q X (k (2#64, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sext 32 64) (Arg.imm 2#32, ())) k) m := by
  simpa only [wp_let_sext_eq] using ⟨by decide, h⟩
theorem bf_wp_sext32_64_64 {k : K (.bits 64)} (h : wp Γ Q X (k (64#64, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sext 32 64) (Arg.imm 64#32, ())) k) m := by
  simpa only [wp_let_sext_eq] using ⟨by decide, h⟩
theorem bf_wp_sext32_64_192 {k : K (.bits 64)} (h : wp Γ Q X (k (192#64, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sext 32 64) (Arg.imm 192#32, ())) k) m := by
  simpa only [wp_let_sext_eq] using ⟨by decide, h⟩
theorem bf_wp_sext32_64_193 {k : K (.bits 64)} (h : wp Γ Q X (k (193#64, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sext 32 64) (Arg.imm 193#32, ())) k) m := by
  simpa only [wp_let_sext_eq] using ⟨by decide, h⟩
theorem bf_wp_sext8_32 {a : Arg Val (.bits 8)} {k : K (.bits 32)}
    (h : wp Γ Q X (k (a.val.signExtend 32, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sext 8 32) (a, ())) k) m := by
  simpa only [wp_let_sext_eq] using ⟨by decide, h⟩
theorem bf_wp_sext8_32_0 {k : K (.bits 32)} (h : wp Γ Q X (k (0#32, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sext 8 32) (Arg.imm 0#8, ())) k) m := by
  simpa only [wp_let_sext_eq] using ⟨by decide, h⟩
theorem bf_wp_sext8_32_0_v {k : K (.bits 32)} (h : wp Γ Q X (k (0#32, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sext 8 32) (Arg.var 0#8, ())) k) m := by
  simpa only [wp_let_sext_eq] using ⟨by decide, h⟩
theorem bf_wp_trunc64_32 {a : Arg Val (.bits 64)} {k : K (.bits 32)}
    (h : wp Γ Q X (k (a.val.setWidth 32, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.trunc 64 32) (a, ())) k) m := by
  simpa only [wp_let_trunc_eq] using ⟨by decide, h⟩
theorem bf_wp_trunc32_8 {a : Arg Val (.bits 32)} {k : K (.bits 8)}
    (h : wp Γ Q X (k (a.val.setWidth 8, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.trunc 32 8) (a, ())) k) m := by
  simpa only [wp_let_trunc_eq] using ⟨by decide, h⟩
theorem bf_wp_trunc32_8_0 {k : K (.bits 8)} (h : wp Γ Q X (k (0#8, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.trunc 32 8) (Arg.imm 0#32, ())) k) m := by
  simpa only [wp_let_trunc_eq] using ⟨by decide, h⟩
theorem bf_wp_trunc32_8_1 {k : K (.bits 8)} (h : wp Γ Q X (k (1#8, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.trunc 32 8) (Arg.imm 1#32, ())) k) m := by
  simpa only [wp_let_trunc_eq] using ⟨by decide, h⟩
theorem bf_wp_cmp {o n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : wp Γ Q X (k (o.evalBits a.val b.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp o (.bits n) .bool rfl) (a, b, ())) k) m := by
  simpa only [wp_let_cmp_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, cast_eq, liftCmp] using h
theorem bf_wp_cmp_eq {n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : wp Γ Q X (k ((a.val == b.val), ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .eq (.bits n) .bool rfl) (a, b, ())) k) m :=
  bf_wp_cmp (evalBits_eq_beq a.val b.val ▸ h)
theorem bf_wp_cmp_ne {n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : wp Γ Q X (k ((a.val != b.val), ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ne (.bits n) .bool rfl) (a, b, ())) k) m :=
  bf_wp_cmp (evalBits_ne_bne a.val b.val ▸ h)
theorem bf_wp_cmp_ult {n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : wp Γ Q X (k (a.val.ult b.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ult (.bits n) .bool rfl) (a, b, ())) k) m :=
  bf_wp_cmp (evalBits_ult_eq a.val b.val ▸ h)
theorem bf_wp_cmp_ule {n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : wp Γ Q X (k (a.val.ule b.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ule (.bits n) .bool rfl) (a, b, ())) k) m :=
  bf_wp_cmp (evalBits_ule_eq a.val b.val ▸ h)
theorem bf_wp_cmp_ugt {n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : wp Γ Q X (k (b.val.ult a.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ugt (.bits n) .bool rfl) (a, b, ())) k) m :=
  bf_wp_cmp (evalBits_ugt_eq a.val b.val ▸ h)
theorem bf_wp_cmp_uge {n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : wp Γ Q X (k (b.val.ule a.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .uge (.bits n) .bool rfl) (a, b, ())) k) m :=
  bf_wp_cmp (evalBits_uge_eq a.val b.val ▸ h)
theorem bf_wp_cmp_slt {n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : wp Γ Q X (k (a.val.slt b.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .slt (.bits n) .bool rfl) (a, b, ())) k) m :=
  bf_wp_cmp (evalBits_slt_eq a.val b.val ▸ h)
theorem bf_wp_cmp_sge {n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : wp Γ Q X (k (b.val.sle a.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .sge (.bits n) .bool rfl) (a, b, ())) k) m :=
  bf_wp_cmp (evalBits_sge_eq a.val b.val ▸ h)
theorem bf_wp_jump0 {L : Cont []} (h : L () m) : wp (rs := rs) Γ Q X (.jump L ()) m := h
theorem bf_wp_jump1 {t} {L : Cont [t]} {a : Arg Val t} (h : L (a.val, ()) m) :
    wp (rs := rs) Γ Q X (.jump L (a, ())) m := h
theorem bf_wp_jump2 {t1 t2} {L : Cont [t1, t2]} {a : Arg Val t1} {b : Arg Val t2}
    (h : L (a.val, b.val, ()) m) : wp (rs := rs) Γ Q X (.jump L (a, b, ())) m := h
theorem bf_wp_jump3 {t1 t2 t3} {L : Cont [t1, t2, t3]} {a : Arg Val t1} {b : Arg Val t2}
    {c : Arg Val t3} (h : L (a.val, b.val, c.val, ()) m) :
    wp (rs := rs) Γ Q X (.jump L (a, b, c, ())) m := h
theorem bf_wp_jump4 {t1 t2 t3 t4} {L : Cont [t1, t2, t3, t4]} {a : Arg Val t1} {b : Arg Val t2}
    {c : Arg Val t3} {d : Arg Val t4} (h : L (a.val, b.val, c.val, d.val, ()) m) :
    wp (rs := rs) Γ Q X (.jump L (a, b, c, d, ())) m := h
theorem bf_wp_jump5 {t1 t2 t3 t4 t5} {L : Cont [t1, t2, t3, t4, t5]} {a : Arg Val t1}
    {b : Arg Val t2} {c : Arg Val t3} {d : Arg Val t4} {e : Arg Val t5}
    (h : L (a.val, b.val, c.val, d.val, e.val, ()) m) :
    wp (rs := rs) Γ Q X (.jump L (a, b, c, d, e, ())) m := h
end BfFastWp

theorem bf_wp_ret0 {Γ X m} {Q : Post []} (h : Q () m) : wp Γ Q X (.ret ()) m := h
theorem bf_wp_ret1 {Γ X m t} {Q : Post [t]} {a : Arg Val t} (h : Q (a.val, ()) m) :
    wp Γ Q X (.ret (a, ())) m := h

private meta def bfReduceProjOnce (e : Lean.Expr) : Lean.Expr :=
  e.replace fun sub =>
    match sub with
    | .proj ``Prod 0 arg => if arg.isAppOfArity ``Prod.mk 4 then some (arg.getArg! 2) else none
    | .proj ``Prod 1 arg => if arg.isAppOfArity ``Prod.mk 4 then some (arg.getArg! 3) else none
    | _ =>
      if sub.isAppOfArity ``Prod.fst 3 && sub.appArg!.isAppOfArity ``Prod.mk 4 then
        some (sub.appArg!.getArg! 2)
      else if sub.isAppOfArity ``Prod.snd 3 && sub.appArg!.isAppOfArity ``Prod.mk 4 then
        some (sub.appArg!.getArg! 3)
      else if sub.isAppOf ``Arg.val && sub.getAppNumArgs ≥ 1 then
        let arg := sub.appArg!
        if (arg.isAppOf ``Arg.var || arg.isAppOf ``Arg.imm) && arg.getAppNumArgs ≥ 1 then
          some arg.appArg!
        else none
      else none

private meta def bfReduceHeadE (e : Lean.Expr) : Lean.Expr :=
  bfReduceProjOnce (bfReduceProjOnce (bfReduceProjOnce e.headBeta))
private meta def bfNormWpGoal (g : Lean.MVarId) : Lean.Elab.Tactic.TacticM Lean.MVarId := do
  let ty := (← Lean.instantiateMVars (← g.getType)).headBeta
  if ty.isAppOf ``wp && ty.getAppNumArgs == 6 then
    let e := ty.getArg! 4; let e' := bfReduceHeadE e
    if e' != e then return ← g.change (Lean.mkAppN ty.getAppFn (ty.getAppArgs.set! 4 e'))
  return g
private meta def bfNat? (e : Lean.Expr) : Option Nat :=
  e.rawNatLit?.orElse fun () => e.nat?
private meta def bfArgNat? (a : Lean.Expr) : Option (Bool × Nat) :=
  let a := a.consumeMData
  if (a.isAppOf ``Arg.imm || a.isAppOf ``Arg.var) && a.getAppNumArgs ≥ 1 then
    let isVar := a.isAppOf ``Arg.var
    let v := a.appArg!.consumeMData
    if v.isAppOf ``BitVec.ofNat && v.getAppNumArgs == 2 then
      (bfNat? (v.getArg! 1)).map (isVar, ·)
    else if v.isAppOf ``OfNat.ofNat && v.getAppNumArgs == 3 then
      (bfNat? (v.getArg! 1)).map (isVar, ·)
    else none
  else none
private meta def bfTyBits? (ty : Lean.Expr) : Option Nat :=
  let ty := ty.consumeMData
  if ty.isAppOf ``Ty.bits && ty.getAppNumArgs == 1 then bfNat? (ty.getArg! 0)
  else if ty.isConstOf ``i64 then some 64
  else if ty.isConstOf ``i32 then some 32
  else if ty.isConstOf ``i8 then some 8
  else none
private meta def bfFastLetLemma? (op : Lean.Expr) : Option Lean.Name :=
  if op.isAppOf ``Op.mk && op.getAppNumArgs == 5 then
    let code := op.getArg! 3; let args := op.getArg! 4
    let a1? := if args.isAppOfArity ``Prod.mk 4 then some (args.getArg! 2) else none
    let a2? := if args.isAppOfArity ``Prod.mk 4 && (args.getArg! 3).isAppOfArity ``Prod.mk 4 then
      some ((args.getArg! 3).getArg! 2) else none
    match code.getAppFn.constName? with
    | some ``OpCode.copy => some ``bf_wp_copy
    | some ``OpCode.add => some ``bf_wp_add
    | some ``OpCode.sub => some ``bf_wp_sub
    | some ``OpCode.mul => some ``bf_wp_mul
    | some ``OpCode.and => some ``bf_wp_and
    | some ``OpCode.or => some ``bf_wp_or
    | some ``OpCode.xor => some ``bf_wp_xor
    | some ``OpCode.not => some ``bf_wp_not
    | some ``OpCode.shl =>
      let w := if code.getAppNumArgs == 1 then bfTyBits? (code.getArg! 0) else none
      match w, a2?.bind bfArgNat? with
      | some 64, some (false, 1) => some ``bf_wp_shl1_64
      | some 64, some (true, 1) => some ``bf_wp_shl1_64_v
      | some 64, some (false, 2) => some ``bf_wp_shl2_64
      | some 64, some (true, 2) => some ``bf_wp_shl2_64_v
      | some 32, some (false, 1) => some ``bf_wp_shl1_32
      | some 32, some (true, 1) => some ``bf_wp_shl1_32_v
      | _, _ => some ``bf_wp_shl
    | some ``OpCode.lshr =>
      match a2?.bind bfArgNat? with
      | some (true, 1) => some ``bf_wp_lshr1_32_v
      | _ => some ``bf_wp_lshr1_32
    | some ``OpCode.zext =>
      if code.getAppNumArgs != 2 then none
      else if (code.getArg! 0).nat? == some 32 && (code.getArg! 1).nat? == some 64 then
        some ``bf_wp_zext32_64
      else if (code.getArg! 0).nat? == some 8 && (code.getArg! 1).nat? == some 32 then
        match a1?.bind bfArgNat? with
        | some (false, 0) => some ``bf_wp_zext8_32_0
        | some (true, 0) => some ``bf_wp_zext8_32_0_v
        | _ => some ``bf_wp_zext8_32
      else none
    | some ``OpCode.sext =>
      if code.getAppNumArgs != 2 then none
      else if (code.getArg! 0).nat? == some 32 && (code.getArg! 1).nat? == some 64 then
        match a1?.bind bfArgNat? with
        | some (false, 0) => some ``bf_wp_sext32_64_0
        | some (false, 1) => some ``bf_wp_sext32_64_1
        | some (false, 2) => some ``bf_wp_sext32_64_2
        | some (false, 64) => some ``bf_wp_sext32_64_64
        | some (false, 192) => some ``bf_wp_sext32_64_192
        | some (false, 193) => some ``bf_wp_sext32_64_193
        | _ => some ``bf_wp_sext32_64
      else if (code.getArg! 0).nat? == some 8 && (code.getArg! 1).nat? == some 32 then
        match a1?.bind bfArgNat? with
        | some (false, 0) => some ``bf_wp_sext8_32_0
        | some (true, 0) => some ``bf_wp_sext8_32_0_v
        | _ => some ``bf_wp_sext8_32
      else none
    | some ``OpCode.trunc =>
      if code.getAppNumArgs != 2 then none
      else if (code.getArg! 0).nat? == some 64 && (code.getArg! 1).nat? == some 32 then
        some ``bf_wp_trunc64_32
      else if (code.getArg! 0).nat? == some 32 && (code.getArg! 1).nat? == some 8 then
        match a1?.bind bfArgNat? with
        | some (false, 0) => some ``bf_wp_trunc32_8_0
        | some (false, 1) => some ``bf_wp_trunc32_8_1
        | _ => some ``bf_wp_trunc32_8
      else none
    | some ``OpCode.cmp =>
      if code.getAppNumArgs == 4 then
        match (code.getArg! 0).getAppFn.constName? with
        | some ``CmpOp.eq => some ``bf_wp_cmp_eq | some ``CmpOp.ne => some ``bf_wp_cmp_ne
        | some ``CmpOp.ult => some ``bf_wp_cmp_ult | some ``CmpOp.ule => some ``bf_wp_cmp_ule
        | some ``CmpOp.ugt => some ``bf_wp_cmp_ugt | some ``CmpOp.uge => some ``bf_wp_cmp_uge
        | some ``CmpOp.slt => some ``bf_wp_cmp_slt | some ``CmpOp.sge => some ``bf_wp_cmp_sge
        | _ => none
      else none
    | _ => none
  else none

private meta def bfClearStale (m0 : Lean.Expr) : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
    let .fvar mId := m0 | return
    for d in (← Lean.getLCtx).decls.toArray.reverse do
      let some d := d | continue
      let t ← Lean.instantiateMVars d.type
      if t.isAppOf ``Std.ExtHashMap.sep && t.appArg! == m0 then
        try Lean.Elab.Tactic.liftMetaTactic1 fun g => some <$> g.clear d.fvarId catch _ => pure ()
    try Lean.Elab.Tactic.liftMetaTactic1 fun g => some <$> g.clear mId catch _ => pure ()
private meta def bfFindJoinHyp (J : Lean.FVarId) :
    Lean.Elab.Tactic.TacticM (Option Lean.Expr) :=
  Lean.Elab.Tactic.withMainContext do
    for d in (← Lean.getLCtx).decls.toArray.reverse do
      let some d := d | continue
      let ok ← Lean.Meta.forallTelescopeReducing d.type fun xs concl => do
        if xs.size < 1 then return false
        return concl.getAppFn.isFVarOf J && (← Lean.Meta.inferType xs[xs.size - 1]!).isAppOf ``wp
      if ok then return some d.toExpr
    return none
private meta def bfStepOnce (unrollGroup : Bool := true) : Lean.Elab.Tactic.TacticM Bool :=
  Lean.Elab.Tactic.withMainContext do
    let g ← Lean.Elab.Tactic.getMainGoal
    let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData.headBeta
    if ty.isAppOf ``And then
      let s ← Lean.Elab.Tactic.saveState
      try Lean.Elab.Tactic.evalTactic (← `(tactic| refine strip_le_wp (by decide) ?_)); return true
      catch _ => s.restore; return false
    if ty.isAppOf ``wp && ty.getAppNumArgs == 6 then
      let e := (ty.getArg! 4).consumeMData.headBeta
      match e.getAppFn.constName? with
      | some ``Expr.let_ =>
        if e.getAppNumArgs != 6 then return false
        if let some lem := bfFastLetLemma? (e.getArg! 4).headBeta then
          let s ← Lean.Elab.Tactic.saveState
          try
            let [hk] ← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels lem)
              | s.restore; return false
            Lean.Elab.Tactic.setGoals [← bfNormWpGoal hk]; return true
          catch _ => s.restore
        return false
      | some ``Expr.load =>
        let s ← Lean.Elab.Tactic.saveState
        try
          let [hl, hk] := (← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``wp_load_of)).take 2
            | s.restore; return false
          LeanQbe.T.C0Step.memSolve true hl
          Lean.Elab.Tactic.setGoals [← bfNormWpGoal hk]; return true
        catch _ => s.restore; return false
      | some ``Expr.store =>
        let s ← Lean.Elab.Tactic.saveState
        try
          let m0 := ty.getArg! 5
          let [hs, hk] := (← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``wp_store_sep)).take 2
            | s.restore; return false
          LeanQbe.T.C0Step.memSolve false hs; Lean.Elab.Tactic.setGoals [hk]
          let mId := Lean.mkIdent `m; let hmId := Lean.mkIdent `hm
          Lean.Elab.Tactic.evalTactic (← `(tactic| intro $mId:ident $hmId:ident;
            try simp only [Arg.val_var, Arg.val_imm, Std.ExtHashMap.sep_emp] at $hmId:ident))
          bfClearStale m0; return true
        catch _ => s.restore; return false
      | some ``Expr.jnz =>
        let hc := Lean.mkIdent `hc
        Lean.Elab.Tactic.evalTactic (← `(tactic|
          (refine wp_jnz_of (fun $hc:ident => ?_) (fun $hc:ident => ?_)) <;> (
            try simp only [Arg.val_var, Arg.val_imm] at $hc:ident; c0_cond $hc
            try (first | exact ($hc).elim | exact absurd rfl $hc | exact $hc rfl
                       | exact absurd trivial $hc | contradiction))))
        return true
      | some ``Expr.jump | some ``Expr.ret =>
        let lems := if e.isAppOf ``Expr.ret then #[``bf_wp_ret0, ``bf_wp_ret1]
          else #[``bf_wp_jump0, ``bf_wp_jump1, ``bf_wp_jump2, ``bf_wp_jump3,
                 ``bf_wp_jump4, ``bf_wp_jump5]
        for lem in lems do
          let s2 ← Lean.Elab.Tactic.saveState
          try
            let [hk] ← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels lem) | s2.restore; continue
            let hkTy ← Lean.instantiateMVars (← hk.getType)
            let hkTy' := bfReduceProjOnce (bfReduceProjOnce hkTy)
            Lean.Elab.Tactic.setGoals [← if hkTy' != hkTy then hk.change hkTy' else pure hk]
            return true
          catch _ => s2.restore
        return false
      | some ``Expr.group =>
        if unrollGroup && e.getAppNumArgs == 6 then
          if let .lam _ _ b _ := e.getArg! 4 then
            if !b.hasLooseBVars then
              let J := Lean.mkIdent `J; let hJ := Lean.mkIdent `hJ
              Lean.Elab.Tactic.evalTactic (← `(tactic|
                refine wp_unroll_group fun $J:ident $hJ:ident => ?_))
              return true
        return false
      | some ``Blocks.get =>
        if e.getAppNumArgs == 8 then
          let bs := (e.getArg! 5).headBeta
          if bs.isAppOf ``Blocks.cons && bs.getAppNumArgs == 7 &&
              (e.getArg! 6).isAppOf ``Member.here then
            let newE := bfReduceHeadE (Lean.mkApp (bs.getArg! 5) (e.getArg! 7))
            let newTy := Lean.mkAppN ty.getAppFn (ty.getAppArgs.set! 4 newE)
            Lean.Elab.Tactic.setGoals [← g.change newTy]; return true
        return false
      | _ => return false
    if let .fvar J := ty.getAppFn then
      if let some h ← bfFindJoinHyp J then
        Lean.Elab.Tactic.setGoals (← (← g.apply h).mapM bfNormWpGoal); return true
    return false

private meta partial def bfStepsLoop (unrollGroup : Bool) (fuel : Nat) :
    Lean.Elab.Tactic.TacticM Unit := do
  if fuel = 0 then return
  let mut out : Array Lean.MVarId := #[]
  for g in (← Lean.Elab.Tactic.getUnsolvedGoals) do
    if ← g.isAssigned then continue
    Lean.Elab.Tactic.setGoals [g]
    if ← bfStepOnce unrollGroup then bfStepsLoop unrollGroup (fuel - 1)
    out := out ++ (← Lean.Elab.Tactic.getUnsolvedGoals)
  Lean.Elab.Tactic.setGoals out.toList

/-- O(1)-per-step symbolic executor avoiding `simp` over `Expr.let_` continuations. -/
scoped elab "bf_fast" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| try (first | refine strip_fwp ?_ | refine strip_wp ?_)))
  bfStepsLoop true 2000

scoped elab "bf_fast_nogrp" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| try (first | refine strip_fwp ?_ | refine strip_wp ?_)))
  bfStepsLoop false 2000

@[scoped bv_c0] theorem bv64_shl2_nat (x : BitVec 64) :
    (x <<< (2 : Nat)).toNat = (4 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

@[scoped bv_c0] theorem bv32_shl1_nat (x : BitVec 32) :
    (x <<< (1 : Nat)).toNat = (2 * x.toNat) % 2 ^ 32 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

private theorem nat_or1_of_even {n : Nat} (he : n % 2 = 0) : n ||| 1 = n + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero => simp [Nat.testBit_zero, he]; omega
  | succ j =>
    rw [Nat.testBit_or, show Nat.testBit 1 (j + 1) = false by rw [Nat.testBit_succ]; simp,
      Bool.or_false, Nat.testBit_succ, Nat.testBit_succ, show (n + 1) / 2 = n / 2 by omega]

theorem bv32_or1_of_even {x : BitVec 32} (he : x.toNat % 2 = 0) :
    (x ||| 1#32).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_or, show (1#32).toNat = 1 from rfl]; exact nat_or1_of_even he

theorem bv64_or1_of_even {x : BitVec 64} (he : x.toNat % 2 = 0) :
    (x ||| 1#64).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_or, show (1#64).toNat = 1 from rfl]; exact nat_or1_of_even he

theorem bv32_and_mask_eq {x : BitVec 32} (hlt : x.toNat < 2 ^ 31) :
    (x &&& 0x7FFFFFFF#32) = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hlt]

theorem bv32_and_bin_eq_zero_of_lt {x : BitVec 32} (hlt : x.toNat < 0x80000000) :
    (x &&& 0x80000000#32) = 0#32 := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_zero]
  by_cases h31 : i = 31
  · subst h31
    have hf : x[31] = false := by
      rw [BitVec.getElem_eq_testBit_toNat, Nat.testBit_eq_decide_div_mod_eq]
      simp [show x.toNat / 2 ^ 31 = 0 by omega]
    simp [hf]
  · have hmask : (0x80000000#32 : BitVec 32)[i] = false := by
      rw [BitVec.getElem_eq_testBit_toNat]
      change Nat.testBit (2 ^ 31) i = false
      rw [Nat.testBit_two_pow]; exact decide_eq_false (Ne.symm h31)
    simp [hmask]

private theorem bit31_bin : (0x80000000#32 : BitVec 32)[31] = true := by decide
private theorem bit19_garb : (0x00080000#32 : BitVec 32)[19] = true := by decide
private theorem bit23_shrk : (0x00800000#32 : BitVec 32)[23] = true := by decide

theorem bv32_and_bin_ne_zero_iff (x : BitVec 32) :
    (x &&& 0x80000000#32) ≠ 0#32 ↔ 0x80000000 ≤ x.toNat := by
  constructor
  · intro hne
    exact Classical.byContradiction fun hlt =>
      hne (bv32_and_bin_eq_zero_of_lt (Nat.lt_of_not_ge hlt))
  · intro hge heq
    have h31 := congrArg (·[31]) heq
    have hx31 : x[31] = true := by
      rw [BitVec.getElem_eq_testBit_toNat, Nat.testBit_eq_decide_div_mod_eq]
      have hlt : x.toNat < 2 ^ 32 := x.isLt
      simp [show x.toNat / 2 ^ 31 = 1 by omega]
    simp [BitVec.getElem_and, hx31, bit31_bin] at h31

theorem bv32_xor1_toNat (x : BitVec 32) : (x ^^^ 1#32).toNat = x.toNat ^^^ 1 := by
  rw [BitVec.toNat_xor]; rfl

theorem bv8_slt0_iff_eq_ff {b : BitVec 8}
    (hd : b = 0#8 ∨ b = 1#8 ∨ b = 0xFF#8) :
    (b.signExtend 32).slt 0#32 = true ↔ b = 0xFF#8 := by
  rcases hd with rfl | rfl | rfl <;> decide

theorem bv8_sge0_iff_ne_ff {b : BitVec 8}
    (hd : b = 0#8 ∨ b = 1#8 ∨ b = 0xFF#8) :
    (0#32).sle (b.signExtend 32) = true ↔ b ≠ 0xFF#8 := by
  rcases hd with rfl | rfl | rfl <;> decide

end FullBvaFwdTactics

open FullBvaFwdTactics

/-! ## 3. Pure resolution, strengthening, and fresh-variable BVA soundness lemmas -/

namespace FullBvaFwdHelpers

/-- Hyper-unary resolution on binary watches: `F ⊨ [l, ot]` and `F ⊨ [l, ot ^ 1]` entail `[l]`. -/
theorem entails_unit_of_bin_pair {f : CNF Nat} {l ot : Nat}
    (h1 : f.EntailsClause (cnfClause [l, ot]))
    (h2 : f.EntailsClause (cnfClause [l, ot ^^^ 1])) :
    f.EntailsClause (cnfClause [l]) := by
  rw [CNF.entails_clause_def]
  intro α hα
  have s1 := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp h1 α hα)
  have s2 := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp h2 α hα)
  rw [← clauseEvalVal_iff]
  simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false] at s1 s2 ⊢
  have hneg : evalLitVal α (ot ^^^ 1) = !(evalLitVal α ot) := by
    simpa [litNeg] using evalLitVal_litNeg α ot
  rw [hneg] at s2
  cases hl : evalLitVal α l <;> cases hot : evalLitVal α ot <;> simp_all

/-- Binary self-subsuming strengthening: `l ∈ C`, `drop ≠ l`, `F ⊨ C`, `F ⊨ [l, drop ^ 1]`
entail `C.filter (· ≠ drop)`. -/
theorem entails_strengthen_of_bin {f : CNF Nat} {C : List Nat} {l drop : Nat}
    (hl : l ∈ C) (hne : drop ≠ l)
    (hC : f.EntailsClause (cnfClause C))
    (hbin : f.EntailsClause (cnfClause [l, drop ^^^ 1])) :
    f.EntailsClause (cnfClause (C.filter (· != drop))) := by
  rw [CNF.entails_clause_def]
  intro α hα
  rw [← clauseEvalVal_iff, clauseEvalVal, List.any_eq_true]
  by_cases hd : evalLitVal α drop = true
  · have hb := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp hbin α hα)
    simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false] at hb
    have hneg : evalLitVal α (drop ^^^ 1) = false := by
      have h := evalLitVal_litNeg α drop
      simp only [litNeg] at h; rw [h, hd]; rfl
    rw [hneg, Bool.or_false] at hb
    exact ⟨l, List.mem_filter.mpr ⟨hl, by simp [Ne.symm hne]⟩, hb⟩
  · have hcs := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp hC α hα)
    simp only [clauseEvalVal, List.any_eq_true] at hcs
    obtain ⟨x, hx, hxt⟩ := hcs
    have hxd : x ≠ drop := fun he => by subst he; exact hd hxt
    exact ⟨x, List.mem_filter.mpr ⟨hx, by simp [hxd]⟩, hxt⟩

/-- Clause self-subsuming strengthening: given `F ⊨ C`, `F ⊨ D`, variable-distinct `D`
(`(D.map (· / 2)).Nodup`), `cand ^ 1 ∈ D`, and every `dl ∈ D` either in `C`, falsified at level 0
(`F ⊨ [dl ^ 1]`), or equal to `cand ^ 1`, we have `F ⊨ C.filter (· ≠ cand)`. -/
theorem entails_strengthen_of_clause {f : CNF Nat} {C D : List Nat} {cand : Nat}
    (hC : f.EntailsClause (cnfClause C))
    (hD : f.EntailsClause (cnfClause D))
    (hnd : (D.map (· / 2)).Nodup)
    (hneg_mem : (cand ^^^ 1) ∈ D)
    (hsub : ∀ dl ∈ D, dl ∈ C ∨ f.EntailsClause (cnfClause [dl ^^^ 1]) ∨ dl = cand ^^^ 1) :
    f.EntailsClause (cnfClause (C.filter (· != cand))) := by
  have hcand_not_D : cand ∉ D := by
    intro hcm
    obtain ⟨i, hi, heqi⟩ := List.mem_iff_getElem.mp hcm
    obtain ⟨j, hj, heqj⟩ := List.mem_iff_getElem.mp hneg_mem
    have hij : i = j := by
      have hm := List.pairwise_iff_getElem.mp hnd
      by_cases hlt : i < j
      · have hne := hm i j (by simp [hi]) (by simp [hj]) hlt
        simp only [List.getElem_map, heqi, heqj, fullInv_var_xor1] at hne
        exact absurd rfl hne
      · by_cases hgt : j < i
        · have hne := hm j i (by simp [hj]) (by simp [hi]) hgt
          simp only [List.getElem_map, heqi, heqj, fullInv_var_xor1] at hne
          exact absurd rfl hne
        · omega
    subst hij
    rw [heqi] at heqj
    exact absurd heqj.symm (litNeg_ne_self cand)
  rw [CNF.entails_clause_def]
  intro α hα
  rw [← clauseEvalVal_iff, clauseEvalVal, List.any_eq_true]
  by_cases hc : evalLitVal α cand = true
  · have hDs := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp hD α hα)
    simp only [clauseEvalVal, List.any_eq_true] at hDs
    obtain ⟨dl, hdlD, hdlt⟩ := hDs
    rcases hsub dl hdlD with hdlC | hfals | hdlneg
    · have hne : dl ≠ cand := fun h => hcand_not_D (h ▸ hdlD)
      exact ⟨dl, List.mem_filter.mpr ⟨hdlC, by simp [hne]⟩, hdlt⟩
    · have hns := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp hfals α hα)
      simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false] at hns
      have hneg := evalLitVal_litNeg α dl
      simp only [litNeg] at hneg
      rw [hneg, hdlt] at hns; cases hns
    · subst hdlneg
      have hneg := evalLitVal_litNeg α cand
      simp only [litNeg] at hneg
      rw [hneg, hc] at hdlt; cases hdlt
  · have hCs := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp hC α hα)
    simp only [clauseEvalVal, List.any_eq_true] at hCs
    obtain ⟨x, hx, hxt⟩ := hCs
    have hne : x ≠ cand := fun h => by subst h; exact hc hxt
    exact ⟨x, List.mem_filter.mpr ⟨hx, by simp [hne]⟩, hxt⟩

/-- Fresh-variable BVA binary extension formula: keeps `F_cur` verbatim and adjoins
`[2 * fv, f]` (`f ∈ L`) and `[2 * fv + 1, q]` (`q ∈ Q`). -/
def bvaExtendFormula (fv : Nat) (L Q : List Nat) (F_cur : List (List Nat)) : List (List Nat) :=
  L.map (fun f => [2 * fv, f]) ++ Q.map (fun q => [2 * fv + 1, q]) ++ F_cur

theorem bvaExtendFormula_entails_orig (fv : Nat) (L Q : List Nat) (F_cur : List (List Nat)) :
    (cnfOfClauses (bvaExtendFormula fv L Q F_cur)).Entails (cnfOfClauses F_cur) := by
  rw [CNF.entails_def]
  intro α hα
  rw [cnf_sat_cnfOfClauses_iff] at hα ⊢
  intro cl hcl
  exact hα cl (List.mem_append_right _ hcl)

theorem bvaExtendFormula_entails_pos {fv : Nat} {L Q : List Nat} {F_cur : List (List Nat)}
    {f : Nat} (hf : f ∈ L) :
    (cnfOfClauses (bvaExtendFormula fv L Q F_cur)).EntailsClause (cnfClause [2 * fv, f]) :=
  entails_mem_cnfOfClauses
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨f, hf, rfl⟩)))

theorem bvaExtendFormula_entails_neg {fv : Nat} {L Q : List Nat} {F_cur : List (List Nat)}
    {q : Nat} (hq : q ∈ Q) :
    (cnfOfClauses (bvaExtendFormula fv L Q F_cur)).EntailsClause (cnfClause [2 * fv + 1, q]) :=
  entails_mem_cnfOfClauses
    (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨q, hq, rfl⟩)))

/-- Fresh-variable BVA UNSAT soundness for `bvaExtendFormula`: any model `α` of `F_cur` extends
to a model `substUpdate α fv b` of `bvaExtendFormula fv L Q F_cur` by setting `fv := true` when
all `q ∈ Q` are true under `α`, and `fv := false` otherwise (in which case all `f ∈ L` are true
via `F_cur ⊨ [f, q0]`). -/
theorem extUnsatSound_bvaExtendFormula {F0 : CNF Nat} {mv_cur : Nat} {F_cur : List (List Nat)}
    {L Q : List Nat} (hs : ExtUnsatSound F0 mv_cur F_cur)
    (hL : ∀ f ∈ L, f < 2 * mv_cur) (hQ : ∀ q ∈ Q, q < 2 * mv_cur)
    (hprod : ∀ f ∈ L, ∀ q ∈ Q, (cnfOfClauses F_cur).EntailsClause (cnfClause [f, q])) :
    ExtUnsatSound F0 (mv_cur + 1) (bvaExtendFormula mv_cur L Q F_cur) := by
  refine ⟨fun c hc l hl => ?_, fun hu => hs.2 ?_⟩
  · unfold bvaExtendFormula at hc
    simp only [List.mem_append, List.mem_map] at hc
    rcases hc with (⟨f, hf, rfl⟩ | ⟨q, hq, rfl⟩) | hmem
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · simp [litVar]
      · have := hL l hf; simp [litVar]; omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · simp [litVar]; omega
      · have := hQ l hq; simp [litVar]; omega
    · exact Nat.lt_succ_of_lt (hs.1 c hmem l hl)
  · rw [CNF.unsat_iff_not_sat] at hu ⊢
    intro α hα
    let b : Bool := Q.all (evalLitVal α)
    let α' : Nat → Bool := substUpdate α mv_cur b
    have hfresh_lit : ∀ x < 2 * mv_cur, evalLitVal α' x = evalLitVal α x := fun x hx => by
      have hne : litVar x ≠ mv_cur := by simp [litVar]; omega
      simp [evalLitVal, α', substUpdate_ne α b hne]
    apply hu α'
    rw [cnf_sat_cnfOfClauses_iff]
    intro c hc
    unfold bvaExtendFormula at hc
    simp only [List.mem_append, List.mem_map] at hc
    rcases hc with (⟨f, hf, rfl⟩ | ⟨q, hq, rfl⟩) | hmem
    · rw [← clauseEvalVal_iff, clauseEvalVal]
      simp only [List.any_cons, List.any_nil, Bool.or_false, hfresh_lit f (hL f hf)]
      have hpos : evalLitVal α' (2 * mv_cur) = b := by
        simp [evalLitVal, litVar, litSign, α']
      rw [hpos]
      cases hb : b
      · simp only [Bool.false_or]
        have hex : ∃ q0 ∈ Q, evalLitVal α q0 = false := by
          have := List.all_eq_false.mp hb
          obtain ⟨q0, hq0, hq0f⟩ := this; exact ⟨q0, hq0, Bool.eq_false_iff.mpr hq0f⟩
        obtain ⟨q0, hq0, hq0f⟩ := hex
        have hfq := (clauseEvalVal_iff α _).mpr (CNF.entails_clause_def.mp (hprod f hf q0 hq0) α hα)
        simp only [clauseEvalVal, List.any_cons, List.any_nil, Bool.or_false, hq0f,
          Bool.or_false] at hfq
        exact hfq
      · simp
    · rw [← clauseEvalVal_iff, clauseEvalVal]
      simp only [List.any_cons, List.any_nil, Bool.or_false, hfresh_lit q (hQ q hq)]
      have hneg : evalLitVal α' (2 * mv_cur + 1) = !b := by
        have hv : litVar (2 * mv_cur + 1) = mv_cur := by simp [litVar]; omega
        have hs : litSign (2 * mv_cur + 1) = true := by simp [litSign]
        simp [evalLitVal, hv, hs, α']
      rw [hneg]
      cases hb : b
      · simp
      · simp only [Bool.not_true, Bool.false_or]
        exact List.all_eq_true.mp hb q hq
    · have hcs := (cnf_sat_cnfOfClauses_iff α F_cur).mp hα c hmem
      exact (clause_sat_substUpdate_fresh b fun x hx hv => by
        have hlt := hs.1 c hmem x hx; omega).mpr hcs

/-! ## 4. `DenseWatchSliceOk` structural, traversal, and compaction lemmas -/

theorem denseWatchSliceOk_append {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p len1 len2 : Nat}
    (h1 : DenseWatchSliceOk F_cur k lit p len1)
    (h2 : DenseWatchSliceOk F_cur k lit (p + len1) len2) :
    DenseWatchSliceOk F_cur k lit p (len1 + len2) := by
  induction h1 with
  | @empty p => simpa using h2
  | @bin p rem w0 hp hf hne hlt hent _ ih =>
    have hadd : p + (rem + 1) = (p + 1) + rem := by omega
    rw [hadd] at h2
    have hres := ih h2
    have hadd2 : rem + 1 + len2 = (rem + len2) + 1 := by omega
    rw [hadd2]; exact .bin hp hf hne hlt hent hres
  | @occ p rem w0 cr hp hp1 hf hsz hlt hr _ ih =>
    have hadd : p + (rem + 2) = (p + 2) + rem := by omega
    rw [hadd] at h2
    have hres := ih h2
    have hadd2 : rem + 2 + len2 = (rem + len2) + 2 := by omega
    rw [hadd2]; exact .occ hp hp1 hf hsz hlt hr hres

/-- Every binary-flagged word in a valid `DenseWatchSliceOk` slice holds a literal `< 2 * cur_vars`
entailed with `lit`, and no `occ` word (header or `cref`) has `PW_BIN_FLAG` set. -/
theorem denseWatchSliceOk_bin_word_props {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} (h : DenseWatchSliceOk F_cur k lit p rem) :
    ∀ idx, p ≤ idx → idx < p + rem →
      let w := k.wstk[idx]?.getD 0#32
      (w &&& 0x80000000#32) ≠ 0#32 →
        (w &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w &&& 0x7FFFFFFF#32).toNat]) := by
  induction h with
  | empty => intro idx h1 h2; omega
  | @bin p rem w0 hp hflag _ hlt hent _ ih =>
    intro idx h1 h2
    by_cases he : idx = p
    · subst he; simp only [hp, Option.getD_some]; exact fun _ => ⟨hlt, hent⟩
    · exact ih idx (by omega) (by omega)
  | @occ p rem w0 cr hp hp1 hflag _ hlt _ _ ih =>
    intro idx h1 h2
    by_cases h0 : idx = p
    · subst h0; simp only [hp, Option.getD_some]; exact fun hne => absurd hflag hne
    · by_cases h1' : idx = p + 1
      · subst h1'; simp only [hp1, Option.getD_some]
        exact fun hne => absurd (bv32_and_bin_eq_zero_of_lt hlt) hne
      · exact ih idx (by omega) (by omega)

/-- Inversion of a non-empty `DenseWatchSliceOk` into its head `bin` or `occ` entry. -/
theorem denseWatchSliceOk_step {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} (h : DenseWatchSliceOk F_cur k lit p rem) (hpos : 0 < rem) :
    (∃ w0, k.wstk[p]? = some w0 ∧ (w0 &&& 0x80000000#32) ≠ 0#32 ∧ w0 ≠ 0xFFFFFFFF#32 ∧
      (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
      DenseWatchSliceOk F_cur k lit (p + 1) (rem - 1)) ∨
    (∃ w0 cr, 2 ≤ rem ∧ k.wstk[p]? = some w0 ∧ k.wstk[p + 1]? = some cr ∧
      (w0 &&& 0x80000000#32) = 0#32 ∧ 3 ≤ w0.toNat ∧ cr.toNat < 0x80000000 ∧
      cr.toNat ∈ fullArenaClauseRefsCore k ∧
      DenseWatchSliceOk F_cur k lit (p + 2) (rem - 2)) := by
  cases h with
  | empty => omega
  | @bin _ r w0 hp hf hne hlt hent hrest =>
    exact Or.inl ⟨w0, hp, hf, hne, hlt, hent, by simpa using hrest⟩
  | @occ _ r w0 cr hp hp1 hf hsz hlt hr hrest =>
    exact Or.inr ⟨w0, cr, by omega, hp, hp1, hf, hsz, hlt, hr, by simpa using hrest⟩

/-- Updating a single literal `l`'s dense watch slice in place (`wstk` mutated only in
`[off..off+sz)`, new length `nsz ≤ sz` stored in `wvec[2*l+1]`, `wusable`/`num_binary` updated)
preserves `FullWitnessInv c F0 F_cur` and `FullDenseInv c F0`. -/
theorem fullWitnessInv_update_dense_slice {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hlen : k.LengthsOk c) (hw : FullWitnessInv c F0 F_cur k)
    (hdm : k.dense_mode ≠ 0#64) {l nsz : Nat} (hl : l < 2 * k.cur_vars)
    {wstk' : List (BitVec 32)} {wu' nb' : BitVec 64}
    (hwstk_len : wstk'.length = c.wcap)
    (hnsz_le : nsz ≤ fullWatchSizeCore k l)
    (hout : ∀ idx, idx < fullWatchOffCore k l ∨
      fullWatchOffCore k l + fullWatchSizeCore k l ≤ idx → wstk'[idx]? = k.wstk[idx]?)
    (hslice' : DenseWatchSliceOk F_cur
      { k with
        wstk := wstk'
        wvec := k.wvec.set (2 * l + 1) (BitVec.ofNat 32 nsz)
        wusable := wu'
        num_binary := nb' } l (fullWatchOffCore k l) nsz) :
    let k' : FullCoreState :=
      { k with
        wstk := wstk'
        wvec := k.wvec.set (2 * l + 1) (BitVec.ofNat 32 nsz)
        wusable := wu'
        num_binary := nb' }
    k'.LengthsOk c ∧ FullWitnessInv c F0 F_cur k' := by
  intro k'
  have hdw : DenseWatchesInv F_cur k := by
    have h := hw.watches; unfold ModeWatchesInv at h; rwa [ite_eq_right hdm] at h
  have hwlen_lt32 : k.wlen < 2 ^ 32 := by
    have := hlen.wlen_le; have := c.hwcap; unfold dimacsBound at *; omega
  have hnsz_lt32 : nsz < 2 ^ 32 := by
    have := hdw.layout.bounds l hl; omega
  have hwv_len : 2 * l + 1 < k.wvec.length := by
    have := hlen.wvec_len; have := hlen.cur_vars_le; omega
  have hoff_eq : ∀ j < 2 * k.cur_vars, fullWatchOffCore k' j = fullWatchOffCore k j := fun j _ => by
    unfold fullWatchOffCore; dsimp only [k']
    rw [List.getElem?_set_ne (by omega)]
  have hsz_eq : ∀ j < 2 * k.cur_vars,
      fullWatchSizeCore k' j = if j = l then nsz else fullWatchSizeCore k j := fun j _ => by
    unfold fullWatchSizeCore; dsimp only [k']
    by_cases hjl : j = l
    · subst hjl
      rw [List.getElem?_set_self hwv_len, Option.getD_some, bv32_ofNat_toNat hnsz_lt32]
      simp
    · rw [List.getElem?_set_ne (by omega), ite_eq_right hjl]
  have hdw' : DenseWatchesInv F_cur k' := by
    refine DenseWatchesInv.of_slices ?_ ?_ ?_ ?_
    · intro j hj
      rw [hoff_eq j hj, hsz_eq j hj]
      have hb := hdw.layout.bounds j hj
      by_cases hjl : j = l
      · subst hjl; simp only [↓reduceIte]; dsimp only [k']; omega
      · simp only [hjl, ↓reduceIte]; exact hb
    · intro j hj hpos
      rw [hoff_eq j hj]; rw [hsz_eq j hj] at hpos
      apply hdw.layout.pos_off j hj
      by_cases hjl : j = l
      · subst hjl; simp only [↓reduceIte] at hpos; omega
      · simp only [hjl, ↓reduceIte] at hpos; exact hpos
    · intro j1 j2 h1 h2 hne hp1 hp2
      rw [hoff_eq j1 h1, hoff_eq j2 h2, hsz_eq j1 h1, hsz_eq j2 h2]
      rw [hsz_eq j1 h1] at hp1; rw [hsz_eq j2 h2] at hp2
      have h1le : (if j1 = l then nsz else fullWatchSizeCore k j1) ≤ fullWatchSizeCore k j1 := by
        by_cases h : j1 = l
        · subst h; simp only [↓reduceIte]; exact hnsz_le
        · simp [h]
      have h2le : (if j2 = l then nsz else fullWatchSizeCore k j2) ≤ fullWatchSizeCore k j2 := by
        by_cases h : j2 = l
        · subst h; simp only [↓reduceIte]; exact hnsz_le
        · simp [h]
      have hd := hdw.layout.disjoint j1 j2 h1 h2 hne (by omega) (by omega)
      omega
    · intro j hj
      rw [hoff_eq j hj, hsz_eq j hj]
      by_cases hjl : j = l
      · subst hjl; simp only [↓reduceIte]; exact hslice'
      · simp only [hjl, ↓reduceIte]
        have hsj := hdw.slices j hj
        refine DenseWatchSliceOk.mono (k := k) (k' := k')
          (by rw [CNF.entails_def]; exact fun _ h => h) (Nat.le_refl _) (fun _ r => r)
          (fun idx hi1 hi2 => ?_) hsj
        have hposj : 0 < fullWatchSizeCore k j := by omega
        by_cases hposl : 0 < fullWatchSizeCore k l
        · have hdisj := hdw.layout.disjoint j l hj hl hjl hposj hposl
          exact hout idx (by rcases hdisj with h1 | h2 <;> omega)
        · exact hout idx (by omega)
  refine ⟨{ hlen with
      wvec_len := by simp [k', hlen.wvec_len]
      wstk_len_arr := hwstk_len },
    { hw with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := by unfold ModeWatchesInv; rw [ite_eq_right hdm]; exact hdw' }⟩

/-! ## 5. Arena scan-next, level-0 garbage marking, and `PH_SHRK` strengthening lemmas -/

/-- If `r` is in `fullArenaScanRefs`, its successor `fullArenaNextOff` is either `alen` or also in
`fullArenaScanRefs` (assuming `refs_wf` chain property). -/
theorem fullArenaScanRefs_next_mem {ar : List (BitVec 32)} {alen : Nat} :
    ∀ {fuel pos r : Nat}, alen - pos ≤ fuel →
      r ∈ fullArenaScanRefs ar alen pos fuel →
      (fullArenaNextOff ar alen r = alen ∨ fullArenaNextOff ar alen r + 3 ≤ alen) →
      fullArenaNextOff ar alen r = alen ∨
        fullArenaNextOff ar alen r ∈ fullArenaScanRefs ar alen pos fuel
  | 0, pos, r, hfl, hr, _ => by simp [fullArenaScanRefs] at hr
  | fuel + 1, pos, r, hfl, hr, hch => by
    unfold fullArenaScanRefs at hr ⊢
    split at hr
    · rename_i hle
      simp only [hle, ↓reduceIte, List.mem_cons] at hr ⊢
      have hnb := fullArenaNextOff_bounds (ar := ar) (alen := alen) (cref := pos) hle
      rcases hr with rfl | hrest
      · rcases hch with he | h3
        · exact Or.inl he
        · refine Or.inr (Or.inr ?_)
          cases fuel with
          | zero => omega
          | succ f' => simp [fullArenaScanRefs, h3]
      · rcases fullArenaScanRefs_next_mem (by omega) hrest hch with he | hm
        · exact Or.inl he
        · exact Or.inr (Or.inr hm)
    · simp at hr

theorem fullArenaClauseRefs_next_mem {c : FullCfg} {F_cur : List (List Nat)} {k : FullCoreState}
    (ha : FullArenaClausesInv c F_cur k) {r : Nat} (hr : r ∈ fullArenaClauseRefsCore k) :
    fullArenaNextOff k.arena k.arena_len r = k.arena_len ∨
      fullArenaNextOff k.arena k.arena_len r ∈ fullArenaClauseRefsCore k :=
  fullArenaScanRefs_next_mem (by omega) hr (ha.refs_wf r hr).2.2.2.2

/-- Marking `cref` as `PH_GARB` at `cur_level = 0` (optionally after overwriting literals inside
`cref + 3 .. cref + 3 + sz - 1`) preserves `FullWitnessInv c F0 F_cur`, `fullArenaClauseRefsCore`,
`FullArenaVarsNodup`, and `FullLastLearnedWf`. -/
theorem fullWitnessInv_markGarb_at_root {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hlen : k.LengthsOk c) (hw : FullWitnessInv c F0 F_cur k)
    (hl0 : k.cur_level = 0) {cref : Nat} (href : cref ∈ fullArenaClauseRefsCore k)
    {arena' : List (BitVec 32)} {ag' : BitVec 64}
    (hal : arena'.length = c.arena_cap)
    (h0 : arena'[cref]? = some (fullArenaHdrCore k cref ||| 0x00080000#32))
    (hout : ∀ i, i ≠ cref → (i < cref + 3 ∨ cref + 3 + fullArenaClauseSizeCore k cref ≤ i) →
      arena'[i]? = k.arena[i]?) :
    let k' : FullCoreState := { k with arena := arena', arena_garbage := ag' }
    k'.LengthsOk c ∧
    fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧
    FullWitnessInv c F0 F_cur k' ∧
    (∀ r ∈ fullArenaClauseRefsCore k, r ≠ cref →
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r) ∧
    fullArenaClauseGarbCore k' cref = true := by
  intro k'
  have hcref_wf := hw.arena.refs_wf cref href
  have hcref_sz : 3 ≤ fullArenaClauseSizeCore k cref := hcref_wf.2.1
  have har_len : cref < k.arena.length := by
    have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
  have hget_cref : k.arena[cref]? = some (fullArenaHdrCore k cref) := by
    unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem har_len, Option.getD_some]
  have hbit23 : ∀ x : BitVec 32,
      ((x ||| 0x00080000#32) &&& 0x00800000#32) = (x &&& 0x00800000#32) := fun x => by
    ext i hi
    have hz : ((0x00080000#32)[i] && (0x00800000#32)[i]) = false := by
      rw [← BitVec.getElem_and]; exact BitVec.getElem_zero hi
    simp only [BitVec.getElem_and, BitVec.getElem_or]
    rw [Bool.and_or_distrib_right, hz, Bool.or_false]
  have hbit19 : ∀ x : BitVec 32, ((x ||| 0x00080000#32) &&& 0x00080000#32) ≠ 0#32 := fun x h => by
    have h19 := congrArg (·[19]) h
    revert h19; simp [FullBvaFwdTactics.bit19_garb]
  have hne_outside : ∀ r ∈ fullArenaClauseRefsCore k, r ≠ cref →
      (r + 3 + fullArenaClauseSizeCore k r ≤ cref ∧ fullArenaNextOff k.arena k.arena_len r ≤ cref) ∨
      (cref + 3 + fullArenaClauseSizeCore k cref ≤ r ∧
        fullArenaNextOff k.arena k.arena_len cref ≤ r) := by
    intro r hr hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨by have := fullArenaScanRefs_disjoint hr href hlt
                       have := (hw.arena.refs_wf r hr).2.2.1; omega,
        fullArenaScanRefs_disjoint hr href hlt⟩
    · exact Or.inr ⟨by have := fullArenaScanRefs_disjoint href hr hgt; omega,
        fullArenaScanRefs_disjoint href hr hgt⟩
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaNextOff arena' k.arena_len r = fullArenaNextOff k.arena k.arena_len r := by
    intro r hr
    by_cases hrc : r = cref
    · subst r
      have h2eq : arena'[cref + 2]? = k.arena[cref + 2]? :=
        hout (cref + 2) (by omega) (Or.inl (by omega))
      have h1 : ¬ (cref + 3 > k.arena_len) := by omega
      have h2 : ¬ (cref + 3 + (k.arena[cref + 2]?.getD 0#32).toNat > k.arena_len) := by
        unfold fullArenaClauseSizeCore at hcref_wf; omega
      unfold fullArenaNextOff
      simp only [h1, ↓reduceIte, h2eq, h2, h0, Option.getD_some]
      rw [hbit23, show fullArenaHdrCore k cref = k.arena[cref]?.getD 0#32 from rfl]
      split
      · exact fullArenaSkipShrk_congr fun i hi _ =>
          hout i (by omega) (Or.inr (by unfold fullArenaClauseSizeCore; exact hi))
      · rfl
    · refine fullArenaNextOff_congr_block ?_ ?_ ?_
      · rcases hne_outside r hr hrc with ⟨hlt, _⟩ | ⟨hge, _⟩
        · exact hout r hrc (Or.inl (by omega))
        · exact hout r hrc (Or.inr (by omega))
      · rcases hne_outside r hr hrc with ⟨hlt, _⟩ | ⟨hge, _⟩
        · have := (hw.arena.refs_wf r hr).2.1
          exact hout (r + 2) (by omega) (Or.inl (by omega))
        · exact hout (r + 2) (by omega) (Or.inr (by omega))
      · intro i hi1 hi2
        rcases hne_outside r hr hrc with ⟨_, hle⟩ | ⟨hge, _⟩
        · exact hout i (by omega) (Or.inl (by omega))
        · exact hout i (by omega) (Or.inr (by omega))
  have hrefs : fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hsz_eq : ∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r := fun r hr => by
    unfold fullArenaClauseSizeCore; dsimp only [k']
    by_cases hrc : r = cref
    · subst r; rw [hout (cref + 2) (by omega) (Or.inl (by omega))]
    · rcases hne_outside r hr hrc with ⟨hlt, _⟩ | ⟨hge, _⟩
      · have := (hw.arena.refs_wf r hr).2.1
        rw [hout (r + 2) (by omega) (Or.inl (by omega))]
      · rw [hout (r + 2) (by omega) (Or.inr (by omega))]
  have hgarb_eq : ∀ r ∈ fullArenaClauseRefsCore k, r ≠ cref →
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r := fun r hr hne => by
    unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [k']
    rcases hne_outside r hr hne with ⟨hlt, _⟩ | ⟨hge, _⟩
    · rw [hout r hne (Or.inl (by omega))]
    · rw [hout r hne (Or.inr (by omega))]
  have hlits_eq : ∀ r ∈ fullArenaClauseRefsCore k, r ≠ cref →
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r := fun r hr hne => by
    have hwf := hw.arena.refs_wf r hr
    have hbd1 : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena.length := by
      have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
    have hbd2 : r + 3 + fullArenaClauseSizeCore k r ≤ k'.arena.length := by
      have := hlen.arena_len_le; dsimp only [k']; omega
    refine fullArenaClauseLitsCore_eq_of_hold hbd1 hbd2 (hsz_eq r hr) fun j hj => ?_
    dsimp only [k']
    rcases hne_outside r hr hne with ⟨hlt, _⟩ | ⟨hge, _⟩
    · exact hout (r + 3 + j) (by omega) (Or.inl (by omega))
    · exact hout (r + 3 + j) (by omega) (Or.inr (by omega))
  have hgarb_cref : fullArenaClauseGarbCore k' cref = true := by
    unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [k']
    rw [h0, Option.getD_some]; exact bne_iff_ne.mpr (hbit19 _)
  have harena' : FullArenaClausesInv c F_cur k' := by
    refine ⟨hw.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; dsimp only [k'] at hnxt ⊢
      rw [hnxt r hr, hsz_eq r hr]; exact hw.arena.refs_wf r hr
    · intro r hr hsh; rw [hrefs] at hr
      have hsh0 : (fullArenaHdrCore k r &&& 0x00800000#32) ≠ 0#32 := by
        by_cases hrc : r = cref
        · subst r; unfold fullArenaHdrCore at hsh ⊢
          simpa [k', h0, hget_cref, hbit23] using hsh
        · unfold fullArenaHdrCore at hsh ⊢; dsimp only [k'] at hsh
          rcases hne_outside r hr hrc with ⟨hlt, _⟩ | ⟨hge, _⟩
          · rwa [hout r hrc (Or.inl (by omega))] at hsh
          · rwa [hout r hrc (Or.inr (by omega))] at hsh
      obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
      have hget_r : k.arena[r]? = some (fullArenaHdrCore k r) := by
        have hr3 := (hw.arena.refs_wf r hr).1
        have : r < k.arena.length := by
          have := hlen.arena_len_le; have := hlen.arena_len_arr; omega
        unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem this, Option.getD_some]
      have hsh_ar : (k.arena[r]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 := by
        rw [hget_r, Option.getD_some]; exact hsh0
      obtain ⟨t0, ht0_lo, _, ht0_nxt, ht0_sent⟩ :=
        fullArenaNextOff_hits_sentinel (hw.arena.refs_wf r hr).1 hsh_ar ht1 ht2 hsent
      refine ⟨t0, by rw [hsz_eq r hr]; exact ht0_lo, by dsimp only [k']; omega, ?_⟩
      dsimp only [k']
      by_cases hrc : r = cref
      · subst r
        have ht0_lo' : cref + 3 + fullArenaClauseSizeCore k cref ≤ t0 := ht0_lo
        rw [hout t0 (by omega) (Or.inr ht0_lo')]; exact ht0_sent
      · rcases hne_outside r hr hrc with ⟨_, hle⟩ | ⟨hge, _⟩
        · rw [hout t0 (by omega) (Or.inl (by omega))]; exact ht0_sent
        · rw [hout t0 (by omega) (Or.inr (by omega))]; exact ht0_sent
    · intro r hr hng l hl; rw [hrefs] at hr
      have hne : r ≠ cref := by rintro rfl; rw [hgarb_cref] at hng; cases hng
      rw [hgarb_eq r hr hne] at hng; rw [hlits_eq r hr hne] at hl
      exact hw.arena.lits_lt r hr hng l hl
    · intro r hr hng; rw [hrefs] at hr
      have hne : r ≠ cref := by rintro rfl; rw [hgarb_cref] at hng; cases hng
      rw [hgarb_eq r hr hne] at hng; rw [hlits_eq r hr hne]
      exact hw.arena.entails r hr hng
  have hno_rsn : ∀ idx < k.trail_end,
      k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 :=
    fun idx hidx => hw.level0_rsn_none idx hidx (by have := hw.lvl_le idx hidx; omega)
  refine ⟨{ hlen with arena_len_arr := hal }, hrefs,
    { hw with
      arena := harena'
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hrefs ▸ hr)
      reason_inv := fun idx hidx hne => absurd (hno_rsn idx hidx) hne
      reason_lit_mem := fun idx hidx hne _ => absurd (hno_rsn idx hidx) hne },
    fun r hr hne => ⟨hgarb_eq r hr hne, hlits_eq r hr hne⟩, hgarb_cref⟩

theorem bv32_add_toNat {a b : BitVec 32} (h : a.toNat + b.toNat < 2 ^ 32) :
    (a + b).toNat = a.toNat + b.toNat := by rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem bv64_add_toNat {a b : BitVec 64} (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem bv64_zext32_toNat (x : BitVec 32) : (BitVec.setWidth 64 x).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

theorem bv64_shl1_toNat {x : BitVec 64} (h : 2 * x.toNat < 2 ^ 64) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega

theorem bv64_lt_add_of_hc {a b c : BitVec 64}
    (hc : a.toNat < (b.toNat + c.toNat) % 2 ^ 64) (h : b.toNat + c.toNat < 2 ^ 64) :
    a.toNat < b.toNat + c.toNat := by rwa [Nat.mod_eq_of_lt h] at hc

theorem bva_slice_bin_info {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} (h : DenseWatchSliceOk F_cur k lit p rem)
    (hp_lt : 0 < rem) (hp_ws : p < k.wstk.length)
    (hflag : (k.wstk[p]'hp_ws &&& 0x80000000#32) ≠ 0#32) :
    let ot := k.wstk[p]'hp_ws &&& 0x7FFFFFFF#32
    ot.toNat < 2 * k.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, ot.toNat]) ∧
    DenseWatchSliceOk F_cur k lit (p + 1) (rem - 1) := by
  rcases denseWatchSliceOk_step h hp_lt with
    ⟨w0, hw0_some, _, _, hot_lt, hent, hrest⟩ | ⟨w0, _, _, hw0_some, _, hbin_eq, _, _, _, _⟩
  · have hw0_val : k.wstk[p]'hp_ws = w0 := by
      rw [List.getElem?_eq_getElem hp_ws] at hw0_some; exact Option.some.inj hw0_some
    rw [hw0_val]; exact ⟨hot_lt, hent, hrest⟩
  · have hw0_val : k.wstk[p]'hp_ws = w0 := by
      rw [List.getElem?_eq_getElem hp_ws] at hw0_some; exact Option.some.inj hw0_some
    exact absurd (hw0_val.symm ▸ hbin_eq) hflag

theorem bva_slice_occ_info {F_cur : List (List Nat)} {k : FullCoreState} {lit p rem : Nat}
    (h : DenseWatchSliceOk F_cur k lit p rem) (hp_lt : 0 < rem) (hp_ws : p < k.wstk.length)
    (hflag : (k.wstk[p]'hp_ws &&& 0x80000000#32) = 0#32) :
    2 ≤ rem ∧ DenseWatchSliceOk F_cur k lit (p + 2) (rem - 2) := by
  rcases denseWatchSliceOk_step h hp_lt with
    ⟨w0, hw0_some, hbin_ne, _, _, _, _⟩ | ⟨_, _, h2le, _, _, _, _, _, _, hrest⟩
  · have hw0_val : k.wstk[p]'hp_ws = w0 := by
      rw [List.getElem?_eq_getElem hp_ws] at hw0_some; exact Option.some.inj hw0_some
    exact absurd (hw0_val ▸ hflag) hbin_ne
  · exact ⟨h2le, hrest⟩

theorem fwd_slice_occ_info {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} (h : DenseWatchSliceOk F_cur k lit p rem)
    (hp_lt : 0 < rem) (hp_ws : p < k.wstk.length) (hp1_ws : p + 1 < k.wstk.length)
    (hflag : (k.wstk[p]'hp_ws &&& 0x80000000#32) = 0#32) :
    2 ≤ rem ∧ (k.wstk[p + 1]'hp1_ws).toNat ∈ fullArenaClauseRefsCore k ∧
    DenseWatchSliceOk F_cur k lit (p + 2) (rem - 2) := by
  rcases denseWatchSliceOk_step h hp_lt with
    ⟨w0, hw0_some, hbin_ne, _, _, _, _⟩ | ⟨_, w1, h2le, _, hw1_some, _, _, _, hcr_mem, hrest⟩
  · have hw0_val : k.wstk[p]'hp_ws = w0 := by
      rw [List.getElem?_eq_getElem hp_ws] at hw0_some; exact Option.some.inj hw0_some
    exact absurd (hw0_val ▸ hflag) hbin_ne
  · have hw1_val : k.wstk[p + 1]'hp1_ws = w1 := by
      rw [List.getElem?_eq_getElem hp1_ws] at hw1_some; exact Option.some.inj hw1_some
    exact ⟨h2le, hw1_val ▸ hcr_mem, hrest⟩

theorem fwd_entails_false_lit {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hl0 : k.cur_level = 0)
    {dl : Nat} (hdl : dl < 2 * k.cur_vars)
    (hneg : ¬ (0#32).sle ((k.vals[dl]?.getD 0#8).signExtend 32) = true) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [dl ^^^ 1]) := by
  have hff : k.vals[dl]?.getD 0#8 = 0xFF#8 := by
    have hiff := FullBvaFwdTactics.bv8_sge0_iff_ne_ff (hw.vals_domain dl hdl)
    exact Classical.byContradiction fun hne => hneg (hiff.mpr hne)
  obtain ⟨idx, hidx, heq⟩ := (hw.vals_false_iff dl hdl).mp hff
  have hlvl := hw.lvl_le idx hidx
  have hsound := hw.level0_sound idx hidx (by omega)
  rwa [heq] at hsound

theorem fwd_unsat_of_empty_entails {F0 : CNF Nat} {F_cur : List (List Nat)} {mv : Nat}
    (hext : ExtUnsatSound F0 mv F_cur)
    (hemp : (cnfOfClauses F_cur).EntailsClause (cnfClause [])) :
    (cnfOfClauses F_cur).Unsat ∧ F0.Unsat := by
  have hu : (cnfOfClauses F_cur).Unsat := by
    rw [CNF.unsat_iff_not_sat]; intro α hα
    have h := (clauseEvalVal_iff α []).mpr (CNF.entails_clause_def.mp hemp α hα)
    simp [clauseEvalVal] at h
  exact ⟨hu, hext.2 hu⟩

theorem fullDenseInv_of_fwd_call {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (hinv : FullDenseInv c F0 s) (hlen' : s'.LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur s'.core) (hl0' : s'.core.cur_level = 0)
    (har' : s'.core.arena = s.core.arena) (hal' : s'.core.arena_len = s.core.arena_len)
    (hmrk' : s'.core.mrk = s.core.mrk) (hlm' : s'.core.lit_mark = s.core.lit_mark)
    (hdm' : s'.core.dense_mode = s.core.dense_mode)
    (hll' : s'.scratch.last_learned = s.scratch.last_learned)
    (hext' : s'.scratch.extend_len = s.scratch.extend_len) :
    FullDenseInv c F0 s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s := by
  have hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s := by
    unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har', hal']
  refine ⟨⟨⟨hlen', F_cur, hw'⟩,
    ⟨fun v hv => by rw [hmrk']; exact hinv.2.1.1 v hv,
     fun l hl => by rw [hlm']; exact hinv.2.1.2 l hl⟩,
    fun r hr hng => by
      rw [hrefs] at hr
      have hng0 : fullArenaClauseGarb s r = false := by
        simpa only [fullArenaClauseGarb, fullArenaClauseGarbCore, fullArenaHdrCore, har'] using hng
      have hlits : fullArenaClauseLits s' r = fullArenaClauseLits s r := by
        unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [har']
      rw [hlits]; exact hinv.2.2.1 r hr hng0,
    ⟨fun i hi => by dsimp only; rw [hll', hrefs]; exact hinv.2.2.2.1.1 i hi,
     by rw [hext']; exact hinv.2.2.2.1.2⟩, hl0', hdm' ▸ hinv.2.2.2.2.2⟩, hrefs⟩

theorem fullDenseInv_of_unwatchLarge {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInv c F0 s) {wvec' wstk' : List (BitVec 32)}
    {wu' cnt' : BitVec 64}
    (hlen' : ({ core := { s.core with wvec := wvec', wstk := wstk', wusable := wu' }
                scratch := { s.scratch with fwd_str_cnt := cnt' } } : FullState).LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur { s.core with wvec := wvec', wstk := wstk', wusable := wu' }) :
    let s' : FullState :=
      { core := { s.core with wvec := wvec', wstk := wstk', wusable := wu' }
        scratch := { s.scratch with fwd_str_cnt := cnt' } }
    FullDenseInv c F0 s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s :=
  ⟨⟨⟨hlen', F_cur, hw'⟩, hinv.2.1, hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2⟩, rfl⟩

theorem garb_false_of_and_garb_red_eq_zero {hdr : BitVec 32}
    (h : (hdr &&& (524288#32 ||| 4194304#32)) = 0#32) :
    ((hdr &&& 0x00080000#32) != 0#32) = false := by
  have hmask : ((524288#32 ||| 4194304#32) &&& 0x00080000#32) = 0x00080000#32 := by decide
  have hz : (hdr &&& 0x00080000#32) = 0#32 := by rw [← hmask, ← BitVec.and_assoc, h]; rfl
  simp [hz]

theorem filter_length_lt_of_mem {l : List Nat} {x : Nat} (hx : x ∈ l) :
    (l.filter (· != x)).length < l.length := by
  induction l with
  | nil => cases hx
  | cons a tl ih =>
    simp only [List.mem_cons] at hx; simp only [List.filter_cons, List.length_cons]
    by_cases ha : (a != x) = true
    · simp only [ha, ↓reduceIte, List.length_cons]
      rcases hx with rfl | htl
      · simp at ha
      · exact Nat.succ_lt_succ (ih htl)
    · simp only [Bool.not_eq_true] at ha; rw [ha]; simp only [Bool.false_eq_true, ↓reduceIte]
      exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem take_succ_filter_eq {l : List Nat} {i : Nat} {x : Nat} (hi : i < l.length) :
    (l.take (i + 1)).filter (· != x) =
      (l.take i).filter (· != x) ++ if l[i] != x then [l[i]] else [] := by
  rw [List.take_succ_eq_append_getElem hi, List.filter_append, List.filter_cons, List.filter_nil]

theorem fullArenaClauseLitsCore_getElem {k : FullCoreState} {r j : Nat}
    (hj : j < fullArenaClauseSizeCore k r) (hb : r + 3 + j < k.arena.length) :
    (fullArenaClauseLitsCore k r)[j]? = some (k.arena[r + 3 + j]'hb).toNat := by
  unfold fullArenaClauseLitsCore
  rw [List.getElem?_map, List.getElem?_take_of_lt hj, List.getElem?_drop,
    List.getElem?_eq_getElem hb, Option.map_some]

theorem fullArenaClauseLitsCore_length {k : FullCoreState} {r : Nat}
    (hb : r + 3 + fullArenaClauseSizeCore k r ≤ k.arena.length) :
    (fullArenaClauseLitsCore k r).length = fullArenaClauseSizeCore k r := by
  unfold fullArenaClauseLitsCore; simp only [List.length_map, List.length_take, List.length_drop]
  omega

theorem fwd_shrink_litsCore_eq {st_u : FullState} {cref nsz : Nat}
    {arena' : List (BitVec 32)} {C : List Nat} {drop : Nat}
    (hsz' : arena'[cref + 2]? = some (BitVec.ofNat 32 nsz)) (hnsz_small : nsz < 2 ^ 32)
    (hfilt_len : (C.filter (· != drop)).length = nsz)
    (hC_eq : fullArenaClauseLitsCore st_u.core cref = C)
    (hfilt_elem : ∀ t < nsz,
      arena'[cref + 3 + t]?.map BitVec.toNat = (C.filter (· != drop))[t]?)
    (harena_len : cref + 3 + nsz ≤ arena'.length) :
    fullArenaClauseLitsCore { st_u.core with arena := arena' } cref =
      (fullArenaClauseLitsCore st_u.core cref).filter (· != drop) := by
  have hsz_new : fullArenaClauseSizeCore { st_u.core with arena := arena' } cref = nsz := by
    unfold fullArenaClauseSizeCore; dsimp only
    rw [hsz', Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnsz_small]
  apply List.ext_getElem?; intro t; rw [hC_eq]
  by_cases ht : t < nsz
  · unfold fullArenaClauseLitsCore
    rw [hsz_new, List.getElem?_map, List.getElem?_take_of_lt ht, List.getElem?_drop]
    exact hfilt_elem t ht
  · rw [List.getElem?_eq_none (by
        rw [fullArenaClauseLitsCore_length (by rw [hsz_new]; exact harena_len), hsz_new]; omega),
      List.getElem?_eq_none (by rw [hfilt_len]; omega)]

def fwdLmMask (t : FullState) : FullState := { t with core := { t.core with lit_mark := [] } }
theorem fwd_lm_reconstruct {s st : FullState} (h : AgreesExcept fwdLmMask s st) :
    st = { s with core := { s.core with lit_mark := st.core.lit_mark } } := by
  have hsc : st.scratch = s.scratch := h.get FullState.scratch
  have hc : st.core = { s.core with lit_mark := st.core.lit_mark } := by
    have h1 := congrArg FullState.core h; cases st; cases s; rename_i c1 _ c2 _
    cases c1; cases c2; simp only [fwdLmMask] at h1; cases h1; rfl
  cases st; cases s; simp only at hsc hc; rw [hsc]; exact congrArg (fun x => FullState.mk x _) hc

def fwdArenaMask (t : FullState) : FullState := { t with core := { t.core with arena := [] } }
theorem fwd_arena_reconstruct {s st : FullState} (h : AgreesExcept fwdArenaMask s st) :
    st = { s with core := { s.core with arena := st.core.arena } } := by
  have hsc : st.scratch = s.scratch := h.get FullState.scratch
  have hc : st.core = { s.core with arena := st.core.arena } := by
    have h1 := congrArg FullState.core h; cases st; cases s; rename_i c1 _ c2 _
    cases c1; cases c2; simp only [fwdArenaMask] at h1; cases h1; rfl
  cases st; cases s; simp only at hsc hc; rw [hsc]; exact congrArg (fun x => FullState.mk x _) hc

def FwdDropOk (F_cur : List (List Nat)) (C : List Nat) (drop : BitVec 32) : Prop :=
  drop ≠ 0xFFFFFFFF#32 →
    drop.toNat ∈ C ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause (C.filter (· != drop.toNat)))

theorem fwd_drop_of_bin {F_cur : List (List Nat)} {C : List Nat} {l ot : BitVec 32}
    (hl : l.toNat ∈ C) (hC : (cnfOfClauses F_cur).EntailsClause (cnfClause C))
    (hbin : (cnfOfClauses F_cur).EntailsClause (cnfClause [l.toNat, ot.toNat]))
    (hne : (ot ^^^ 1#32) ≠ l) (hmem : (ot ^^^ 1#32).toNat ∈ C) :
    FwdDropOk F_cur C (ot ^^^ 1#32) := fun _ => ⟨hmem, by
  have hne_n : (ot ^^^ 1#32).toNat ≠ l.toNat := fun h => hne (BitVec.eq_of_toNat_eq h)
  have hneg : (ot ^^^ 1#32).toNat ^^^ 1 = ot.toNat := by
    rw [FullBvaFwdTactics.bv32_xor1_toNat]; exact litNeg_litNeg ot.toNat
  exact entails_strengthen_of_bin hl hne_n hC (by rwa [hneg])⟩

theorem fwd_drop_of_clause {F_cur : List (List Nat)} {C D : List Nat} {cand : BitVec 32}
    (hC : (cnfOfClauses F_cur).EntailsClause (cnfClause C))
    (hD : (cnfOfClauses F_cur).EntailsClause (cnfClause D)) (hnd : (D.map (· / 2)).Nodup)
    (hmemC : cand.toNat ∈ C) (hmemD : (cand.toNat ^^^ 1) ∈ D) (hsub : ∀ t < D.length,
      let dl := D[t]?.getD 0
      dl ∈ C ∨ (cnfOfClauses F_cur).EntailsClause (cnfClause [dl ^^^ 1]) ∨ dl = cand.toNat ^^^ 1) :
    FwdDropOk F_cur C cand := fun _ => ⟨hmemC, entails_strengthen_of_clause hC hD hnd hmemD
  fun _ hdl => by obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.mp hdl
                  simpa only [List.getElem?_eq_getElem ht, Option.getD_some] using hsub t ht⟩

theorem fullDenseInv_of_markGarb {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInv c F0 s) (hw : FullWitnessInv c F0 F_cur s.core)
    {cref : Nat} (href : cref ∈ fullArenaClauseRefsCore s.core)
    {arena' : List (BitVec 32)} {ag' cnt' : BitVec 64} (hal : arena'.length = c.arena_cap)
    (h0 : arena'[cref]? = some (fullArenaHdrCore s.core cref ||| 0x00080000#32))
    (hout : ∀ i, i ≠ cref → (i < cref + 3 ∨ cref + 3 + fullArenaClauseSizeCore s.core cref ≤ i) →
      arena'[i]? = s.core.arena[i]?) :
    let s' : FullState := { core := { s.core with arena := arena', arena_garbage := ag' },
                            scratch := { s.scratch with fwd_sub_cnt := cnt' } }
    FullWitnessInv c F0 F_cur s'.core ∧ FullDenseInv c F0 s' ∧
    fullArenaClauseRefs s' = fullArenaClauseRefs s := by
  intro s'
  have ⟨hclen', hrefs', hw', hother, hgarb_cref⟩ := fullWitnessInv_markGarb_at_root (ag' := ag')
    hinv.1.lengths.core_ok hw hinv.2.2.2.2.1 href hal h0 hout
  have hnodup' : FullArenaVarsNodup s' := fun r hr hng => by
    change r ∈ fullArenaClauseRefsCore s'.core at hr; rw [hrefs'] at hr
    have hne : r ≠ cref := by rintro rfl; change fullArenaClauseGarbCore s'.core r = false at hng
                              rw [hgarb_cref] at hng; cases hng
    have ⟨hg, hl⟩ := hother r hr hne
    have hng0 : fullArenaClauseGarb s r = false := by
      change fullArenaClauseGarbCore s'.core r = false at hng; rwa [hg] at hng
    rw [show fullArenaClauseLits s' r = fullArenaClauseLits s r from hl]
    exact hinv.2.2.1 r hr hng0
  refine ⟨hw', ⟨⟨⟨hclen', { hinv.1.lengths.scratch_ok with
    scratch_buf_len := hinv.1.lengths.scratch_ok.scratch_buf_len }⟩, F_cur, hw'⟩,
    hinv.2.1, hnodup', ⟨fun i hi => by
      unfold fullArenaClauseRefs; rw [hrefs']; exact hinv.2.2.2.1.1 i hi, hinv.2.2.2.1.2⟩,
    hinv.2.2.2.2.1, hinv.2.2.2.2.2⟩, hrefs'⟩

end FullBvaFwdHelpers

end LeanQbe.T.Examples.Kissat.Full
