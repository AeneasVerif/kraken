module

public import LeanQbe.T.Bootstrap0.Compiler0
public import LeanQbe.T.Bootstrap0.Bridge0
public import LeanQbe.T.Amd64.ScalarTarg
public import LeanQbe.T.Amd64.PrintAsm0
public import Kraken.X64.PrintATT
import LeanQbe.T.FlatLemmas
import LeanQbe.T.OpsLemmas
import LeanQbe.T.TargetLemmas
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Amd64.FrameLemmas
import LeanQbe.T.Amd64.IselLemmas1
import LeanQbe.T.Amd64.IselLemmas2
import LeanQbe.T.Amd64.IselLemmas3
import LeanQbe.T.Amd64.IselLemmas4
import LeanQbe.T.Amd64.PrintAsm0Lemmas

/-!
# Bootstrap Stage B (`Sound0Part1`): `PrintAsm0` Envelope, `Bridge0`, `Legal0`, & `Isel0`

Foundations for the verified semantic soundness of `leanqbe0Compile`, explicitly tracking:
* **Bug A guard (`singleBlockGroups`)**: every `.group bodies k` has `bodies.length ≤ 1`
  (while `PrePass0.preStepGroup0` / `preEnqueueGroup0` on `main` already match `Rega0` block order,
  retaining this guard keeps downstream `PrePass0` invariants uniform; also verified in tests).
* **Bug B guard (`noNegBool`)**: no `.let1 (.un .neg .bool) _ _` appears, matching
  `x64Gpr.supportsScalarOp` (now also rejected by `Compiler0.checkOpArith0`).

Contents:
1. `PrintAsm0` envelope equivalence (`toAmd64Program_printAsm0` / `toAmd64Program_printModule0`).
2. First-order `wp0` semantics for `TFlat0`, canonical 64-bit value invariants, and `Bridge0`
   preservation (`tflatToTFlat0_wp`).
3. `Legal0` validation soundness and AST worklist step bounds (`legalMod0_sound`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Bootstrap0

open LeanQbe.T
open LeanQbe.T.Amd64
open Std Std.ExtHashMap

/-! ## 1. `PrintAsm0` Envelope & `Dir0` Forward-List Decomposition -/

private theorem moviD_dirSubset0 (r : Reg64) (c : BitVec 64) : DirSubset0 (moviD r c) := by
  dsimp only [moviD, moviI, DirSubset0]
  split <;> simp [isDir0, isOp0, isRm0, isOpd0, isConst0]

private theorem dir0ToAmd64_dirSubset0 (symName : Sym0 → Sym) (d0 : Dir0) :
    ∀ d ∈ dir0ToAmd64 symName d0, DirSubset0 d := by
  cases d0 with
  | label _ | jmp _ | callSym _ | ret =>
    intro d hd; simp only [dir0ToAmd64, List.mem_singleton] at hd; subst hd
    simp [DirSubset0, isDir0, isOp0, isTarget0, isConst0, x64JmpD, x64CallD, x64RetD]
  | jcc _ _ | setcc _ _ =>
    intro d hd; simp only [dir0ToAmd64, List.mem_singleton] at hd; subst hd
    simp [DirSubset0, isDir0, isOp0, isRm0]
  | shMaskCl _ | testbRR _ _ | mulq _ | ldSlot _ _ | stSlot _ _ | ldSlotIdx _ _
  | stSlotIdx _ _ =>
    intro d hd; simp only [dir0ToAmd64, List.mem_singleton] at hd; subst hd
    simp [DirSubset0, isDir0, isOp0, isRm0, isOpd0, isAddr0, isConst0]
  | spAdd isSub _ | spAddReg isSub _ =>
    cases isSub <;> intro d hd <;> simp only [dir0ToAmd64, List.mem_singleton] at hd <;>
      subst hd <;> simp [DirSubset0, isDir0, isOp0, isRm0, isOpd0, isConst0, x64SubSpD,
        x64AddSpD]
  | movRR w _ _ | cmpRR w _ _ | cmovcc w _ _ _ =>
    cases w <;> intro d hd <;> simp only [dir0ToAmd64, List.mem_singleton] at hd <;>
      subst hd <;> simp [DirSubset0, isDir0, isOp0, isRm0, isOpd0, insW]
  | unary w isNeg _ =>
    cases w <;> cases isNeg <;> intro d hd <;>
      simp only [dir0ToAmd64, List.mem_singleton] at hd <;> subst hd <;>
      simp [DirSubset0, isDir0, isOp0, isRm0, insW]
  | movRI rd imm =>
    intro d hd; simp only [dir0ToAmd64, List.mem_singleton] at hd; subst hd
    exact moviD_dirSubset0 _ _
  | movzx32 w _ _ | ldMem w _ _ | stMem w _ _ =>
    cases w <;> intro d hd <;> simp only [dir0ToAmd64, List.mem_singleton] at hd <;>
      subst hd <;> simp [DirSubset0, isDir0, isOp0, isRm0, isOpd0, isAddr0, isConst0, insW]
  | movsx wDst _ wSrc _ =>
    cases wDst <;> cases wSrc <;> intro d hd <;>
      simp only [dir0ToAmd64, List.mem_singleton] at hd <;> subst hd <;>
      simp [DirSubset0, isDir0, isOp0, isRm0, isOpd0, insW]
  | aluRR w k _ _ =>
    cases w <;> cases k <;> intro d hd <;>
      simp only [dir0ToAmd64, List.mem_singleton] at hd <;> subst hd <;>
      simp [DirSubset0, isDir0, isOp0, isRm0, isOpd0, alu0ToOp, insW]
  | shiftCl w k _ =>
    cases w <;> cases k <;> intro d hd <;>
      simp only [dir0ToAmd64, List.mem_singleton] at hd <;> subst hd <;>
      simp [DirSubset0, isDir0, isOp0, isRm0, isCount0, shift0ToOp, insW]
  | divCore w isS _ =>
    cases w <;> cases isS <;> intro d hd <;>
      simp only [dir0ToAmd64, List.mem_cons, List.not_mem_nil, or_false] at hd
    all_goals
      rcases hd with rfl | rfl | rfl
      all_goals
        first
        | exact moviD_dirSubset0 _ _
        | simp [DirSubset0, isDir0, isOp0, isRm0, isOpd0, isCount0, isConst0, insW]

private theorem toAmd64Program_dirSubset0 (symName : Sym0 → Sym) (dirs : List Dir0) :
    ∀ d ∈ toAmd64Program symName dirs, DirSubset0 d := by
  intro d hd
  dsimp only [toAmd64Program] at hd
  rw [List.mem_flatMap] at hd
  obtain ⟨d0, _, hd0⟩ := hd
  exact dir0ToAmd64_dirSubset0 symName d0 d hd0

/-- `PrintAsm0.printAsm0` matches `Kraken.X64.toATT` on every program emitted by `Bridge0`. -/
theorem toAmd64Program_printAsm0 (symName : Sym0 → Sym) (dirs : List Dir0) :
    printAsm0 (toAmd64Program symName dirs) =
      Kraken.X64.toATT (toAmd64Program symName dirs) :=
  printAsm0_eq_toATT _ (toAmd64Program_dirSubset0 symName dirs)

/-- `PrintAsm0.printModule0` matches `.text` + `.globl` + `Kraken.X64.toATT` on `Bridge0` output. -/
theorem toAmd64Program_printModule0 (fnNames : List String) (symName : Sym0 → Sym)
    (dirs : List Dir0) :
    printModule0 fnNames (toAmd64Program symName dirs) =
      ".text\n" ++
        String.join (fnNames.map fun n => s!".globl {n}\n") ++
        if (toAmd64Program symName dirs).isEmpty then ""
        else Kraken.X64.toATT (toAmd64Program symName dirs) ++ "\n" :=
  printModule0_eq_toATT fnNames _ (toAmd64Program_dirSubset0 symName dirs)

theorem toAmd64Program_append (symName : Sym0 → Sym) (xs ys : List Dir0) :
    toAmd64Program symName (xs ++ ys) =
      toAmd64Program symName xs ++ toAmd64Program symName ys := by
  dsimp only [toAmd64Program]; exact List.flatMap_append

theorem revDirAux0_eq (xs acc : List Dir0) : revDirAux0 xs acc = xs.reverse ++ acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons d xs ih => dsimp only [revDirAux0]; rw [ih, List.reverse_cons, List.append_assoc]; rfl

/-- Single-directive `patchEpilogues0` substitution rule. -/
@[expose] def patchDir0 (bytes : UInt64) : Dir0 → List Dir0
  | .spAdd false 0 => revDirAux0 (emitSpAdj0 false bytes []) []
  | d => [d]

private theorem patchDir0_ne {bytes : UInt64} {d : Dir0} (hd : d ≠ .spAdd false 0) :
    patchDir0 bytes d = [d] := by
  cases d with
  | spAdd isSub imm =>
    cases isSub
    · simp only [patchDir0]
    · rfl
  | _ => rfl

private theorem patchEpilogues0_cons_ne (bytes : UInt64) {d : Dir0} (hd : d ≠ .spAdd false 0)
    (rest acc : List Dir0) :
    patchEpilogues0 bytes (d :: rest) acc = patchEpilogues0 bytes rest (d :: acc) := by
  cases d with
  | spAdd isSub imm =>
    cases isSub
    · obtain ⟨⟨⟨v, hv⟩⟩⟩ := imm
      cases v with
      | zero => exact absurd rfl hd
      | succ k => rfl
    · rfl
  | _ => rfl

private theorem emitSpAdj0_append (isSub : Bool) (bytes : UInt64) (acc : List Dir0) :
    emitSpAdj0 isSub bytes acc = emitSpAdj0 isSub bytes [] ++ acc := by
  dsimp only [emitSpAdj0]
  cases isSub <;> split <;> simp [pushDImm0, pushDUnary0]

private theorem patchEpilogues0_eq_aux (bytes : UInt64) (xs acc : List Dir0) :
    patchEpilogues0 bytes xs acc = acc.reverse ++ xs.flatMap (patchDir0 bytes) := by
  induction xs generalizing acc with
  | nil =>
    dsimp only [patchEpilogues0]
    rw [revDirAux0_eq, List.flatMap_nil, List.append_nil]
  | cons d rest ih =>
    by_cases hd : d = .spAdd false 0
    · subst hd
      dsimp only [patchEpilogues0]
      rw [ih, emitSpAdj0_append false bytes acc, List.reverse_append, List.append_assoc]
      congr 1
      simp only [List.flatMap_cons, patchDir0, revDirAux0_eq, List.append_nil]
    · rw [patchEpilogues0_cons_ne bytes hd, ih, List.flatMap_cons, patchDir0_ne hd,
        List.reverse_cons, List.append_assoc]

theorem patchEpilogues0_eq (bytes : UInt64) (xs : List Dir0) :
    patchEpilogues0 bytes xs [] = xs.flatMap (patchDir0 bytes) := by
  simpa only [List.reverse_nil, List.nil_append] using patchEpilogues0_eq_aux bytes xs []

theorem patchEpilogues0_append (bytes : UInt64) (xs ys : List Dir0) :
    patchEpilogues0 bytes (xs ++ ys) [] =
      patchEpilogues0 bytes xs [] ++ patchEpilogues0 bytes ys [] := by
  rw [patchEpilogues0_eq, patchEpilogues0_eq, patchEpilogues0_eq, List.flatMap_append]

/-! ## 2. `Ty0`, Canonical 64-Bit Representations, `wp0`, & `Bridge0` Equivalence -/

/-- Convert Stage-0 `Ty0` to `LeanQbe.T.Ty`. -/
@[expose] def ty0ToTy : Ty0 → Ty
  | .bool => .bool
  | .b8 => .bits 8
  | .b16 => .bits 16
  | .b32 => .bits 32
  | .b64 => .bits 64

/-- Map `List Ty0` to `List Ty`. -/
@[expose] def ty0ListToTy (ts : List Ty0) : List Ty :=
  ts.map ty0ToTy

/-- Encode a `Val (ty0ToTy t)` to its canonical zero-extended 64-bit GPR word. -/
@[expose] def toCanon64 : (t : Ty0) → Val (ty0ToTy t) → BitVec 64
  | .bool, b => BitVec.ofNat 64 b.toNat
  | .b8, v => v.setWidth 64
  | .b16, v => v.setWidth 64
  | .b32, v => v.setWidth 64
  | .b64, v => v

theorem ty0ToTy_tyWidth0 (t : Ty0) (ht : t ≠ .bool) :
    ty0ToTy t = .bits (tyWidth0 t).bits := by
  cases t <;> first | exact absurd rfl ht | rfl

theorem tyWidth0_bits_le (t : Ty0) : (tyWidth0 t).bits ≤ 64 := by
  cases t <;> decide

theorem abiGprHolds_ty0_iff (rv : BitVec 64) (t : Ty0) (v : Val (ty0ToTy t)) :
    AbiGprHolds rv (ty0ToTy t) v ↔ rv = toCanon64 t v := by
  cases t with
  | bool | b8 | b16 | b32 => simp [AbiGprHolds, ty0ToTy, toCanon64]
  | b64 =>
    dsimp only [ty0ToTy, Val] at v
    simp [AbiGprHolds, ty0ToTy, toCanon64]

theorem abiGprHolds_of_canon64 {rv : BitVec 64} {t : Ty0} {v : Val (ty0ToTy t)}
    (h : rv = toCanon64 t v) : AbiGprHolds rv (ty0ToTy t) v :=
  (abiGprHolds_ty0_iff rv t v).2 h

theorem toCanon64_toGprHolds (t : Ty0) (v : Val (ty0ToTy t)) :
    GprHolds (toCanon64 t v) (ty0ToTy t) v :=
  (abiGprHolds_of_canon64 (rv := toCanon64 t v) rfl).toGprHolds

theorem canon64_of_gprHolds {rv : BitVec 64} {t : Ty0} {v : Val (ty0ToTy t)}
    (h : GprHolds rv (ty0ToTy t) v) :
    (rv.setWidth (tyWidth0 t).bits).setWidth 64 = toCanon64 t v := by
  cases t with
  | bool =>
    dsimp only [GprHolds, ty0ToTy, tyWidth0, Width.bits, toCanon64] at h ⊢
    rw [h]; cases v <;> rfl
  | b8 | b16 | b32 =>
    dsimp only [GprHolds, ty0ToTy, tyWidth0, Width.bits, toCanon64] at h ⊢
    rw [h.2]
  | b64 =>
    dsimp only [ty0ToTy, Val] at v
    dsimp only [GprHolds, ty0ToTy, tyWidth0, Width.bits, toCanon64] at h ⊢
    rw [BitVec.setWidth_eq, BitVec.setWidth_eq]
    exact h.2

mutual
/-- True iff `fn.body` contains no `.group` with `≥ 2` block bodies (Bug A guard). -/
@[expose] def TFlat0.singleBlockGroups : TFlat0 → Bool
  | .let1 _ _ k | .let2Umulw64 _ _ k | .load _ _ k | .store _ _ _ k | .call _ _ _ _ k =>
    k.singleBlockGroups
  | .jnz _ t e => t.singleBlockGroups && e.singleBlockGroups
  | .group bodies k =>
    decide (bodies.length ≤ 1) && blocksSingleBlockGroups bodies && k.singleBlockGroups
  | _ => true

@[expose] def blocksSingleBlockGroups : List (List Ty0 × TFlat0) → Bool
  | [] => true
  | (_, b) :: rest => b.singleBlockGroups && blocksSingleBlockGroups rest
end

mutual
/-- True iff `fn.body` contains no `.let1 (.un .neg .bool) _ _` (Bug B guard). -/
@[expose] def TFlat0.noNegBool : TFlat0 → Bool
  | .let1 (.un .neg .bool) _ _ => false
  | .let1 _ _ k | .let2Umulw64 _ _ k | .load _ _ k | .store _ _ _ k | .call _ _ _ _ k =>
    k.noNegBool
  | .jnz _ t e => t.noNegBool && e.noNegBool
  | .group bodies k => blocksNoNegBool bodies && k.noNegBool
  | _ => true

@[expose] def blocksNoNegBool : List (List Ty0 × TFlat0) → Bool
  | [] => true
  | (_, b) :: rest => b.noNegBool && blocksNoNegBool rest
end

/-- Combined Stage-A soundness guard predicate on a `TFlatFn0`. -/
@[expose] def TFlatFn0.okGuards (fn : TFlatFn0) : Bool :=
  fn.body.singleBlockGroups && fn.body.noNegBool

/-- Operand signature for `OpCode0`. -/
@[expose] def op0ArgTys : OpCode0 → List Ty0
  | .un _ t => [t]
  | .bin _ t => [t, t]
  | .cmp _ t => [t, t]
  | .select t => [.bool, t, t]
  | .conv .ofBool _ _ => [.bool]
  | .conv _ m _ => [widthTy0 m]
  | .div _ w => [widthTy0 w, widthTy0 w]
  | .umulw64 => [.b64, .b64]

/-- Result `List Ty0` for `OpCode0` (`[.b64, .b64]` for `.umulw64`, `[opRetTy0 op]` otherwise). -/
@[expose] def op0RetTys : OpCode0 → List Ty0
  | .umulw64 => [.b64, .b64]
  | op => [opRetTy0 op]

@[expose] def castWidthBool0 (w : Width) (x : OpCode [.bool] [.bits w.bits]) :
    OpCode [.bool] [ty0ToTy (widthTy0 w)] :=
  match w, x with
  | .W8, x => x | .W16, x => x | .W32, x => x | .W64, x => x

@[expose] def castWidth2Op0 (m n : Width) (x : OpCode [.bits m.bits] [.bits n.bits]) :
    OpCode [ty0ToTy (widthTy0 m)] [ty0ToTy (widthTy0 n)] :=
  match m, n, x with
  | .W8, .W8, x | .W8, .W16, x | .W8, .W32, x | .W8, .W64, x
  | .W16, .W8, x | .W16, .W16, x | .W16, .W32, x | .W16, .W64, x
  | .W32, .W8, x | .W32, .W16, x | .W32, .W32, x | .W32, .W64, x
  | .W64, .W8, x | .W64, .W16, x | .W64, .W32, x | .W64, .W64, x => x

@[expose] def castWidthDiv0 (w : Width) (x : OpCode [.bits w.bits, .bits w.bits] [.bits w.bits]) :
    OpCode [ty0ToTy (widthTy0 w), ty0ToTy (widthTy0 w)] [ty0ToTy (widthTy0 w)] :=
  match w, x with
  | .W8, x => x | .W16, x => x | .W32, x => x | .W64, x => x

/-- Map `OpCode0` to canonical `LeanQbe.T.OpCode` on `ty0ToTy` types. -/
@[expose] def op0ToOpCode :
    (op : OpCode0) → OpCode (ty0ListToTy (op0ArgTys op)) (ty0ListToTy (op0RetTys op))
  | .un .copy t => .copy (ty0ToTy t)
  | .un .neg t => .neg (ty0ToTy t)
  | .un .not t => .not (ty0ToTy t)
  | .bin .add t => .add (ty0ToTy t)
  | .bin .sub t => .sub (ty0ToTy t)
  | .bin .mul t => .mul (ty0ToTy t)
  | .bin .and t => .and (ty0ToTy t)
  | .bin .or t => .or (ty0ToTy t)
  | .bin .xor t => .xor (ty0ToTy t)
  | .bin .shl t => .shl (ty0ToTy t)
  | .bin .lshr t => .lshr (ty0ToTy t)
  | .bin .ashr t => .ashr (ty0ToTy t)
  | .bin .rotl t => .rotl (ty0ToTy t)
  | .bin .rotr t => .rotr (ty0ToTy t)
  | .cmp co t => .cmp co (ty0ToTy t) .bool (by cases t <;> rfl)
  | .select t => .select (ty0ToTy t)
  | .conv .ofBool _ n => castWidthBool0 n (.ofBool n.bits)
  | .conv .zext m n => castWidth2Op0 m n (.zext m.bits n.bits)
  | .conv .sext m n => castWidth2Op0 m n (.sext m.bits n.bits)
  | .conv .trunc m n => castWidth2Op0 m n (.trunc m.bits n.bits)
  | .div .udiv w => castWidthDiv0 w (.udiv w.bits)
  | .div .urem w => castWidthDiv0 w (.urem w.bits)
  | .div .sdiv w => castWidthDiv0 w (.sdiv w.bits)
  | .div .srem w => castWidthDiv0 w (.srem w.bits)
  | .umulw64 => .umulw 64

/-- Typed evaluation of one `Arg0` at target `t : Ty` in runtime environment `vs`. -/
@[expose] def evalArg0Ty (vs : List ((t : Ty) × Val t)) : (t : Ty) → Arg0 → Option (Val t)
  | t, .var idx => lookupV vs t idx.toNat
  | .bool, .immBool b => some b
  | .bits 8, .immBits .W8 val => some (BitVec.ofNat 8 val.toNat)
  | .bits 16, .immBits .W16 val => some (BitVec.ofNat 16 val.toNat)
  | .bits 32, .immBits .W32 val => some (BitVec.ofNat 32 val.toNat)
  | .bits 64, .immBits .W64 val => some (BitVec.ofNat 64 val.toNat)
  | _, _ => none

/-- Typed evaluation of `List Arg0` against `ts : List Ty` into `Tup Val ts`. -/
@[expose] def evalArgs0Ty (vs : List ((t : Ty) × Val t)) :
    (ts : List Ty) → List Arg0 → Option (Tup Val ts)
  | [], [] => some ()
  | t :: ts, a :: args =>
    match evalArg0Ty vs t a, evalArgs0Ty vs ts args with
    | some v, some rest => some (v, rest)
    | _, _ => none
  | _, _ => none

/-- Map a heterogeneous `Tup Cont (bodies.map (ty0ListToTy ·.1))` onto a label stack. -/
@[expose] def pushConts0 :
    (bodies : List (List Ty0 × TFlat0)) →
    Tup Cont (bodies.map (fun p => ty0ListToTy p.1)) →
    List ((ts : List Ty) × Cont ts) →
    List ((ts : List Ty) × Cont ts)
  | [], (), ls => ls
  | p :: rest, (j, js), ls => pushConts0 rest js (⟨ty0ListToTy p.1, j⟩ :: ls)

mutual
/-- Total-correctness weakest precondition `wp0` directly on Stage-0 `TFlat0` (including `.tailCall`
and `.group`), parameterized by `Γ : Env`, `symName : Sym0 → Sym`, return signature `curRs`,
and value/label contexts `vs`, `ls`. -/
def wp0 (Γ : Env) (symName : Sym0 → Sym) (curRs : List Ty0) (vs : List ((t : Ty) × Val t))
    (ls : List ((ts : List Ty) × Cont ts)) (Q : Post (ty0ListToTy curRs)) (X : XPost) :
    TFlat0 → Mem 64 → Prop
  | .let1 op args k, m =>
    match evalArgs0Ty vs (ty0ListToTy (op0ArgTys op)) args with
    | some argv =>
      OpCode.wp (op0ToOpCode op) argv fun rvs =>
        wp0 Γ symName curRs (pushTup rvs vs) ls Q X k m
    | none => False
  | .let2Umulw64 a b k, m =>
    match evalArg0Ty vs (.bits 64) a, evalArg0Ty vs (.bits 64) b with
    | some va, some vb =>
      OpCode.wp (OpCode.umulw 64) (va, vb, ()) fun rvs =>
        wp0 Γ symName curRs (pushTup rvs vs) ls Q X k m
    | _, _ => False
  | .load t addr k, m =>
    match evalArg0Ty vs (.bits 64) addr with
    | some a => ∃ v, loadVal m (ty0ToTy t) a = some v ∧
        wp0 Γ symName curRs (⟨ty0ToTy t, v⟩ :: vs) ls Q X k m
    | none => False
  | .store t val addr k, m =>
    match evalArg0Ty vs (ty0ToTy t) val, evalArg0Ty vs (.bits 64) addr with
    | some v, some a =>
      storeOk m (ty0ToTy t) a ∧ wp0 Γ symName curRs vs ls Q X k (storeMem m (ty0ToTy t) a v)
    | _, _ => False
  | .call fnSym as bs args k, m =>
    match evalArgs0Ty vs (ty0ListToTy as) args with
    | some argv =>
      ∃ (P : Post (ty0ListToTy bs)) (E : XPost),
        Γ (symName fnSym) (ty0ListToTy as) (ty0ListToTy bs) argv m P E ∧
        (∀ r m', P r m' → wp0 Γ symName curRs (pushTup r vs) ls Q X k m') ∧
        (∀ g cs xs m', E g cs xs m' → X g cs xs m')
    | none => False
  | .tailCall fnSym as args, m =>
    match evalArgs0Ty vs (ty0ListToTy as) args with
    | some argv =>
      Γ (symName fnSym) (ty0ListToTy as) (ty0ListToTy curRs) argv m Q X
    | none => False
  | .jnz c t e, m =>
    match evalArg0Ty vs .bool c with
    | some cv =>
      (cv = true → wp0 Γ symName curRs vs ls Q X t m) ∧
      (cv = false → wp0 Γ symName curRs vs ls Q X e m)
    | none => False
  | .jump j args, m =>
    match listGet? ls j.toNat with
    | some ⟨ts, J⟩ =>
      match evalArgs0Ty vs ts args with
      | some argv => J argv m
      | none => False
    | none => False
  | .ret vs', m =>
    match evalArgs0Ty vs (ty0ListToTy curRs) vs' with
    | some rvs => Q rvs m
    | none => False
  | .exit fnSym as args, m =>
    match evalArgs0Ty vs (ty0ListToTy as) args with
    | some argv => X (symName fnSym) (ty0ListToTy as) argv m
    | none => False
  | .hlt, _ => False
  | .group bodies k, m =>
    ∀ (Js : Tup Cont (bodies.map (fun p => ty0ListToTy p.1))),
      closed0 Γ symName curRs vs (pushConts0 bodies Js ls) Q X bodies Js →
      wp0 Γ symName curRs vs (pushConts0 bodies Js ls) Q X k m

def closed0 (Γ : Env) (symName : Sym0 → Sym) (curRs : List Ty0) (vs : List ((t : Ty) × Val t))
    (ls : List ((ts : List Ty) × Cont ts)) (Q : Post (ty0ListToTy curRs)) (X : XPost) :
    (bodies : List (List Ty0 × TFlat0)) →
    Tup Cont (bodies.map (fun p => ty0ListToTy p.1)) → Prop
  | [], () => True
  | (pts, b) :: rest, (j, js) =>
    (∀ (xs : Tup Val (ty0ListToTy pts)) m,
      wp0 Γ symName curRs (pushTup xs vs) ls Q X b m → j xs m) ∧
    closed0 Γ symName curRs vs ls Q X rest js
end

/-! ### `Bridge0` Equivalence (`tflatToTFlat0` → `wp0`) -/

@[expose] def argIdxLtU32 {t : Ty} : Arg K t → Bool
  | .var i => decide (i < UInt32.size)
  | .imm _ => true

@[expose] def argsIdxLtU32 : {ts : List Ty} → Tup (Arg K) ts → Bool
  | [], () => true
  | _ :: _, (a, rest) => argIdxLtU32 a && argsIdxLtU32 rest

mutual
/-- Decidable check that all de Bruijn var/label indices fit in `UInt32` (for `Bridge0`). -/
@[expose] def tflatIdxLtU32 {rs : List Ty} : TFlat rs → Bool
  | .let_ op k => argsIdxLtU32 op.args && tflatIdxLtU32 k
  | .load _ a k => argIdxLtU32 a && tflatIdxLtU32 k
  | .store v a k => argIdxLtU32 v && argIdxLtU32 a && tflatIdxLtU32 k
  | .call _ _ args k => argsIdxLtU32 args && tflatIdxLtU32 k
  | .jnz c t e => argIdxLtU32 c && tflatIdxLtU32 t && tflatIdxLtU32 e
  | .jump j args => decide (j < UInt32.size) && argsIdxLtU32 args
  | .ret vs => argsIdxLtU32 vs
  | .exit _ args => argsIdxLtU32 args
  | .hlt => true
  | .group bodies k => tblocksIdxLtU32 bodies && tflatIdxLtU32 k

@[expose] def tblocksIdxLtU32 {rs : List Ty} : {sig : List (List Ty)} → TBlocks rs sig → Bool
  | _, .nil => true
  | _, .cons b bs => tflatIdxLtU32 b && tblocksIdxLtU32 bs
end

private theorem except_bind_ok {ε α β : Type _} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

private theorem except_bind_err {ε α β : Type _} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = .error e := rfl

private theorem ty0ToTy_tyToTy0 {t : Ty} {t0 : Ty0} (h : tyToTy0 t = .ok t0) :
    ty0ToTy t0 = t := by
  cases t with
  | bool => cases h; rfl
  | bits n =>
    by_cases h8 : n = 8
    · subst h8; cases h; rfl
    · by_cases h16 : n = 16
      · subst h16; cases h; rfl
      · by_cases h32 : n = 32
        · subst h32; cases h; rfl
        · by_cases h64 : n = 64
          · subst h64; cases h; rfl
          · simp [tyToTy0, h8, h16, h32, h64] at h
  | float _ | pair _ _ => cases h

private theorem ty0ListToTy_tyListToTy0 :
    ∀ {ts : List Ty} {ts0 : List Ty0}, tyListToTy0 ts = .ok ts0 → ty0ListToTy ts0 = ts
  | [], [], _ => rfl
  | [], _ :: _, h => by dsimp only [tyListToTy0] at h; cases h
  | t :: ts, ts0, h => by
    dsimp only [tyListToTy0] at h
    cases ht : tyToTy0 t with
    | error _ => simp [ht, except_bind_err] at h
    | ok t0 =>
      cases hts : tyListToTy0 ts with
      | error _ => simp [ht, hts, except_bind_ok, except_bind_err] at h
      | ok rest0 =>
        simp only [ht, hts, except_bind_ok, Except.ok.injEq] at h
        subst h
        simp only [ty0ListToTy, List.map_cons, ty0ToTy_tyToTy0 ht]
        exact congrArg (t :: ·) (ty0ListToTy_tyListToTy0 hts)

private theorem bitsToWidth0_spec {n : Nat} {w : Width} (h : bitsToWidth0 n = .ok w) :
    w.bits = n ∧ ty0ToTy (widthTy0 w) = .bits n := by
  dsimp only [bitsToWidth0] at h
  split at h <;> cases h <;> exact ⟨rfl, rfl⟩

private theorem evalArg0Ty_argToArg0 {vs : List ((t : Ty) × Val t)} {t : Ty}
    {a : Arg K t} {a0 : Arg0} (harg : argToArg0 t a = .ok a0)
    (hi : argIdxLtU32 a = true) :
    evalArg0Ty vs t a0 = (denoteArg vs a).map Arg.val := by
  cases a with
  | var i =>
    simp only [argToArg0, Except.ok.injEq] at harg
    subst harg
    simp only [argIdxLtU32, decide_eq_true_eq] at hi
    dsimp only [evalArg0Ty, denoteArg]
    rw [UInt32.toNat_ofNat_of_lt' hi]
    cases lookupV vs t i <;> rfl
  | imm c =>
    cases t with
    | bool =>
      simp only [argToArg0, Except.ok.injEq] at harg; subst harg; rfl
    | bits n =>
      dsimp only [argToArg0] at harg
      cases hw : bitsToWidth0 n with
      | error _ => simp [hw, except_bind_err] at harg
      | ok w =>
        simp only [hw, except_bind_ok, Except.ok.injEq] at harg
        subst harg
        have ⟨hwb, _⟩ := bitsToWidth0_spec hw
        subst hwb
        cases w with
        | W8 =>
          have h64 : UInt64.toNat (UInt64.ofNat c.toNat) = c.toNat :=
            UInt64.toNat_ofNat_of_lt' (Nat.lt_trans c.isLt (by decide))
          simp only [evalArg0Ty, denoteArg, Option.map, Arg.val]
          congr 1; apply BitVec.eq_of_toNat_eq
          rw [h64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt c.isLt]
        | W16 =>
          have h64 : UInt64.toNat (UInt64.ofNat c.toNat) = c.toNat :=
            UInt64.toNat_ofNat_of_lt' (Nat.lt_trans c.isLt (by decide))
          simp only [evalArg0Ty, denoteArg, Option.map, Arg.val]
          congr 1; apply BitVec.eq_of_toNat_eq
          rw [h64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt c.isLt]
        | W32 =>
          have h64 : UInt64.toNat (UInt64.ofNat c.toNat) = c.toNat :=
            UInt64.toNat_ofNat_of_lt' (Nat.lt_trans c.isLt (by decide))
          simp only [evalArg0Ty, denoteArg, Option.map, Arg.val]
          congr 1; apply BitVec.eq_of_toNat_eq
          rw [h64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt c.isLt]
        | W64 =>
          have h64 : UInt64.toNat (UInt64.ofNat c.toNat) = c.toNat :=
            UInt64.toNat_ofNat_of_lt' (by simpa using c.isLt)
          simp only [evalArg0Ty, denoteArg, Option.map, Arg.val]
          congr 1; apply BitVec.eq_of_toNat_eq
          rw [h64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt c.isLt]
    | float _ | pair _ _ => simp [argToArg0] at harg

private theorem evalArgs0Ty_tupArgsToList0 {vs : List ((t : Ty) × Val t)} :
    ∀ {ts : List Ty} {as : Tup (Arg K) ts} {as0 : List Arg0},
      tupArgsToList0 ts as = .ok as0 →
      argsIdxLtU32 as = true →
      evalArgs0Ty vs ts as0 = (denoteArgs vs as).map vals
  | [], (), as0, h, _ => by
    dsimp only [tupArgsToList0] at h; cases h; rfl
  | t :: ts, (a, rest), as0, h, hi => by
    dsimp only [tupArgsToList0] at h
    dsimp only [argsIdxLtU32] at hi
    rw [Bool.and_eq_true] at hi
    cases ha : argToArg0 t a with
    | error _ => simp [ha, except_bind_err] at h
    | ok a0 =>
      cases hrest : tupArgsToList0 ts rest with
      | error _ => simp [ha, hrest, except_bind_ok, except_bind_err] at h
      | ok rest0 =>
        simp only [ha, hrest, except_bind_ok, Except.ok.injEq] at h
        subst h
        have ha' := evalArg0Ty_argToArg0 (vs := vs) ha hi.1
        have hr' := evalArgs0Ty_tupArgsToList0 (vs := vs) hrest hi.2
        dsimp only [evalArgs0Ty, denoteArgs]
        rw [ha', hr']
        cases denoteArg vs a <;> cases denoteArgs vs rest <;> rfl

private theorem lookupSymId?_symNameOf_aux :
    ∀ {tbl : List (Sym × Sym0)},
      (tbl.map Prod.fst).Nodup → (tbl.map Prod.snd).Nodup →
      ∀ {s : Sym} {id : Sym0}, lookupSymId? tbl s = some id → symNameOf tbl id = s
  | [], _, _, _, _, h => by dsimp only [lookupSymId?] at h; cases h
  | (n, i) :: rest, hnd1, hnd2, s, id, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd1 hnd2
    dsimp only [lookupSymId?] at h
    by_cases hns : (n == s) = true
    · have h1 := beq_iff_eq.mp hns; subst h1
      simp only [hns, ↓reduceIte, Option.some.injEq] at h; subst h
      simp [symNameOf]
    · simp only [hns, Bool.false_eq_true, ↓reduceIte] at h
      have hid := lookupSymId?_symNameOf_aux hnd1.2 hnd2.2 h
      have hne : i ≠ id := by
        have hmem : (s, id) ∈ rest := by
          clear hid hns hnd1 hnd2
          induction rest with
          | nil => dsimp only [lookupSymId?] at h; cases h
          | cons p ps ih =>
            rcases p with ⟨n', i'⟩
            dsimp only [lookupSymId?] at h
            split at h
            · rename_i heq; have hns' := beq_iff_eq.mp heq; subst hns'; cases h
              exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (ih h)
        intro heq; subst heq; exact hnd2.1 (s, i) hmem rfl
      have hbeq : (i == id) = false :=
        Bool.eq_false_iff.mpr fun hb => hne (beq_iff_eq.mp hb)
      dsimp only [symNameOf, List.find?]
      simp only [hbeq]
      exact hid

theorem lookupSymId?_symNameOf (tbl : List (Sym × Sym0))
    (hnd1 : (tbl.map Prod.fst).Nodup) (hnd2 : (tbl.map Prod.snd).Nodup)
    {s : Sym} {id : Sym0} (h : lookupSymId? tbl s = some id) :
    symNameOf tbl id = s :=
  lookupSymId?_symNameOf_aux hnd1 hnd2 h

private theorem opCodeToTFlat0_umulw {n : Nat} {args0 : List Arg0} {k0 node0 : TFlat0}
    (h : opCodeToTFlat0 (OpCode.umulw n) args0 k0 = .ok node0) :
    n = 64 ∧ ∃ a b, args0 = [a, b] ∧ node0 = .let2Umulw64 a b k0 := by
  by_cases hn : n = 64
  · subst hn
    rcases args0 with _ | ⟨a, _ | ⟨b, _ | c⟩⟩ <;> dsimp only [opCodeToTFlat0] at h <;> cases h
    exact ⟨rfl, a, b, rfl, rfl⟩
  · unfold opCodeToTFlat0 opCodeToTFlat0.match_1 opCodeToTFlat0._sparseCasesOn_1 at h
    dsimp only [OpCode.rec] at h
    rw [dite_eq_right_of_eq_false (eq_false hn)] at h
    cases h

theorem wp0_let1 (Γ : Env) (symName : Sym0 → Sym) (curRs : List Ty0)
    (vs : List ((t : Ty) × Val t)) (ls : List ((ts : List Ty) × Cont ts))
    (Q : Post (ty0ListToTy curRs)) (X : XPost) (op : OpCode0) (args : List Arg0) (k : TFlat0)
    (m : Mem 64) :
    wp0 Γ symName curRs vs ls Q X (.let1 op args k) m =
      match evalArgs0Ty vs (ty0ListToTy (op0ArgTys op)) args with
      | some argv => OpCode.wp (op0ToOpCode op) argv fun rvs =>
          wp0 Γ symName curRs (pushTup rvs vs) ls Q X k m
      | none => False := by
  dsimp only [wp0]; cases evalArgs0Ty vs (ty0ListToTy (op0ArgTys op)) args <;> rfl

theorem wp0_let2Umulw64 (Γ : Env) (symName : Sym0 → Sym) (curRs : List Ty0)
    (vs : List ((t : Ty) × Val t)) (ls : List ((ts : List Ty) × Cont ts))
    (Q : Post (ty0ListToTy curRs)) (X : XPost) (a b : Arg0) (k : TFlat0) (m : Mem 64) :
    wp0 Γ symName curRs vs ls Q X (.let2Umulw64 a b k) m =
      match evalArg0Ty vs (.bits 64) a, evalArg0Ty vs (.bits 64) b with
      | some va, some vb => OpCode.wp (OpCode.umulw 64) (va, vb, ()) fun rvs =>
          wp0 Γ symName curRs (pushTup rvs vs) ls Q X k m
      | _, _ => False := by
  dsimp only [wp0]; cases evalArg0Ty vs (.bits 64) a <;> cases evalArg0Ty vs (.bits 64) b <;> rfl

theorem wp0_load (Γ : Env) (symName : Sym0 → Sym) (curRs : List Ty0)
    (vs : List ((t : Ty) × Val t)) (ls : List ((ts : List Ty) × Cont ts))
    (Q : Post (ty0ListToTy curRs)) (X : XPost) (t : Ty0) (addr : Arg0) (k : TFlat0)
    (m : Mem 64) :
    wp0 Γ symName curRs vs ls Q X (.load t addr k) m =
      match evalArg0Ty vs (.bits 64) addr with
      | some a => ∃ v, loadVal m (ty0ToTy t) a = some v ∧
          wp0 Γ symName curRs (⟨ty0ToTy t, v⟩ :: vs) ls Q X k m
      | none => False := by
  dsimp only [wp0]; cases evalArg0Ty vs (.bits 64) addr <;> rfl

theorem wp0_store (Γ : Env) (symName : Sym0 → Sym) (curRs : List Ty0)
    (vs : List ((t : Ty) × Val t)) (ls : List ((ts : List Ty) × Cont ts))
    (Q : Post (ty0ListToTy curRs)) (X : XPost) (t : Ty0) (val addr : Arg0) (k : TFlat0)
    (m : Mem 64) :
    wp0 Γ symName curRs vs ls Q X (.store t val addr k) m =
      match evalArg0Ty vs (ty0ToTy t) val, evalArg0Ty vs (.bits 64) addr with
      | some v, some a =>
        storeOk m (ty0ToTy t) a ∧ wp0 Γ symName curRs vs ls Q X k (storeMem m (ty0ToTy t) a v)
      | _, _ => False := by
  dsimp only [wp0]
  cases evalArg0Ty vs (ty0ToTy t) val <;> cases evalArg0Ty vs (.bits 64) addr <;> rfl

theorem wp0_call (Γ : Env) (symName : Sym0 → Sym) (curRs : List Ty0)
    (vs : List ((t : Ty) × Val t)) (ls : List ((ts : List Ty) × Cont ts))
    (Q : Post (ty0ListToTy curRs)) (X : XPost) (fnSym : Sym0) (as bs : List Ty0)
    (args : List Arg0) (k : TFlat0) (m : Mem 64) :
    wp0 Γ symName curRs vs ls Q X (.call fnSym as bs args k) m =
      match evalArgs0Ty vs (ty0ListToTy as) args with
      | some argv =>
        ∃ (P : Post (ty0ListToTy bs)) (E : XPost),
          Γ (symName fnSym) (ty0ListToTy as) (ty0ListToTy bs) argv m P E ∧
          (∀ r m', P r m' → wp0 Γ symName curRs (pushTup r vs) ls Q X k m') ∧
          (∀ g cs xs m', E g cs xs m' → X g cs xs m')
      | none => False := by
  dsimp only [wp0]; cases evalArgs0Ty vs (ty0ListToTy as) args <;> rfl

theorem wp0_tailCall (Γ : Env) (symName : Sym0 → Sym) (curRs : List Ty0)
    (vs : List ((t : Ty) × Val t)) (ls : List ((ts : List Ty) × Cont ts))
    (Q : Post (ty0ListToTy curRs)) (X : XPost) (fnSym : Sym0) (as : List Ty0) (args : List Arg0)
    (m : Mem 64) :
    wp0 Γ symName curRs vs ls Q X (.tailCall fnSym as args) m =
      match evalArgs0Ty vs (ty0ListToTy as) args with
      | some argv => Γ (symName fnSym) (ty0ListToTy as) (ty0ListToTy curRs) argv m Q X
      | none => False := by
  dsimp only [wp0]; cases evalArgs0Ty vs (ty0ListToTy as) args <;> rfl

theorem wp0_jnz (Γ : Env) (symName : Sym0 → Sym) (curRs : List Ty0)
    (vs : List ((t : Ty) × Val t)) (ls : List ((ts : List Ty) × Cont ts))
    (Q : Post (ty0ListToTy curRs)) (X : XPost) (c : Arg0) (t e : TFlat0) (m : Mem 64) :
    wp0 Γ symName curRs vs ls Q X (.jnz c t e) m =
      match evalArg0Ty vs .bool c with
      | some cv => (cv = true → wp0 Γ symName curRs vs ls Q X t m) ∧
          (cv = false → wp0 Γ symName curRs vs ls Q X e m)
      | none => False := by
  dsimp only [wp0]; cases evalArg0Ty vs .bool c <;> rfl

theorem wp0_jump (Γ : Env) (symName : Sym0 → Sym) (curRs : List Ty0)
    (vs : List ((t : Ty) × Val t)) (ls : List ((ts : List Ty) × Cont ts))
    (Q : Post (ty0ListToTy curRs)) (X : XPost) (j : UInt32) (args : List Arg0) (m : Mem 64) :
    wp0 Γ symName curRs vs ls Q X (.jump j args) m =
      match listGet? ls j.toNat with
      | some ⟨ts, J⟩ =>
        match evalArgs0Ty vs ts args with
        | some argv => J argv m
        | none => False
      | none => False := by
  dsimp only [wp0]
  cases listGet? ls j.toNat with
  | none => rfl
  | some p => cases evalArgs0Ty vs p.1 args <;> rfl

theorem wp0_ret (Γ : Env) (symName : Sym0 → Sym) (curRs : List Ty0)
    (vs : List ((t : Ty) × Val t)) (ls : List ((ts : List Ty) × Cont ts))
    (Q : Post (ty0ListToTy curRs)) (X : XPost) (vs' : List Arg0) (m : Mem 64) :
    wp0 Γ symName curRs vs ls Q X (.ret vs') m =
      match evalArgs0Ty vs (ty0ListToTy curRs) vs' with
      | some rvs => Q rvs m
      | none => False := by
  dsimp only [wp0]; cases evalArgs0Ty vs (ty0ListToTy curRs) vs' <;> rfl

theorem wp0_exit (Γ : Env) (symName : Sym0 → Sym) (curRs : List Ty0)
    (vs : List ((t : Ty) × Val t)) (ls : List ((ts : List Ty) × Cont ts))
    (Q : Post (ty0ListToTy curRs)) (X : XPost) (fnSym : Sym0) (as : List Ty0) (args : List Arg0)
    (m : Mem 64) :
    wp0 Γ symName curRs vs ls Q X (.exit fnSym as args) m =
      match evalArgs0Ty vs (ty0ListToTy as) args with
      | some argv => X (symName fnSym) (ty0ListToTy as) argv m
      | none => False := by
  dsimp only [wp0]; cases evalArgs0Ty vs (ty0ListToTy as) args <;> rfl

theorem wp0_hlt (Γ : Env) (symName : Sym0 → Sym) (curRs : List Ty0)
    (vs : List ((t : Ty) × Val t)) (ls : List ((ts : List Ty) × Cont ts))
    (Q : Post (ty0ListToTy curRs)) (X : XPost) (m : Mem 64) :
    wp0 Γ symName curRs vs ls Q X .hlt m = False := by dsimp only [wp0]

theorem wp0_group (Γ : Env) (symName : Sym0 → Sym) (curRs : List Ty0)
    (vs : List ((t : Ty) × Val t)) (ls : List ((ts : List Ty) × Cont ts))
    (Q : Post (ty0ListToTy curRs)) (X : XPost) (bodies : List (List Ty0 × TFlat0)) (k : TFlat0)
    (m : Mem 64) :
    wp0 Γ symName curRs vs ls Q X (.group bodies k) m =
      ∀ (Js : Tup Cont (bodies.map (fun p => ty0ListToTy p.1))),
        closed0 Γ symName curRs vs (pushConts0 bodies Js ls) Q X bodies Js →
        wp0 Γ symName curRs vs (pushConts0 bodies Js ls) Q X k m := by dsimp only [wp0]

theorem closed0_nil (Γ : Env) (symName : Sym0 → Sym) (curRs : List Ty0)
    (vs : List ((t : Ty) × Val t)) (ls : List ((ts : List Ty) × Cont ts))
    (Q : Post (ty0ListToTy curRs)) (X : XPost) :
    closed0 Γ symName curRs vs ls Q X [] () = True := by dsimp only [closed0]

theorem closed0_cons (Γ : Env) (symName : Sym0 → Sym) (curRs : List Ty0)
    (vs : List ((t : Ty) × Val t)) (ls : List ((ts : List Ty) × Cont ts))
    (Q : Post (ty0ListToTy curRs)) (X : XPost) (pts : List Ty0) (b : TFlat0)
    (rest : List (List Ty0 × TFlat0)) (j : Cont (ty0ListToTy pts))
    (js : Tup Cont (rest.map (fun p => ty0ListToTy p.1))) :
    closed0 Γ symName curRs vs ls Q X ((pts, b) :: rest) (j, js) =
      ((∀ (xs : Tup Val (ty0ListToTy pts)) m,
          wp0 Γ symName curRs (pushTup xs vs) ls Q X b m → j xs m) ∧
        closed0 Γ symName curRs vs ls Q X rest js) := by dsimp only [closed0]

private theorem opCodeToTFlat0_bitcast {t u : Ty} {hcast : t.size = u.size}
    {args0 : List Arg0} {k0 node0 : TFlat0}
    (h : opCodeToTFlat0 (OpCode.bitcast t u hcast) args0 k0 = .ok node0) :
    ∃ (n : Nat) (t0 : Ty0), t = .bits n ∧ u = .bits n ∧
      tyToTy0 (.bits n) = .ok t0 ∧ node0 = .let1 (.un .copy t0) args0 k0 := by
  cases t <;> cases u <;> try (dsimp only [opCodeToTFlat0] at h; cases h)
  rename_i m n
  by_cases hmn : m = n
  · subst hmn
    dsimp only [opCodeToTFlat0] at h
    simp only [beq_self_eq_true, ↓reduceIte] at h
    cases ht : tyToTy0 (.bits m) with
    | error _ => simp [ht, except_bind_err] at h
    | ok t0 =>
      simp only [ht, except_bind_ok, Except.ok.injEq] at h
      subst h
      exact ⟨m, t0, rfl, rfl, ht, rfl⟩
  · dsimp only [opCodeToTFlat0] at h
    have hneq : (m == n) = false := beq_false_of_ne hmn
    simp only [hneq, Bool.false_eq_true, ↓reduceIte] at h
    cases h

/-- Decomposition of `opCodeToTFlat0` results (avoids `opCodeToTFlat0.match_1.splitter`). -/
theorem opCodeToTFlat0_cases {sig rs : List Ty} (code : OpCode sig rs)
    (args0 : List Arg0) (k0 tf0 : TFlat0)
    (h : opCodeToTFlat0 code args0 k0 = .ok tf0) :
    (∃ op args, tf0 = .let1 op args k0) ∨ (∃ a b, tf0 = .let2Umulw64 a b k0) := by
  cases code with
  | umulw n =>
    obtain ⟨_, a, b, _, hnd⟩ := opCodeToTFlat0_umulw h
    exact Or.inr ⟨a, b, hnd⟩
  | bitcast t u hcast =>
    obtain ⟨_, _, _, _, _, hnd⟩ := opCodeToTFlat0_bitcast h
    exact Or.inl ⟨_, _, hnd⟩
  | copy _ | neg _ | not _ | add _ | sub _ | mul _ | and _ | or _ | xor _
  | shl _ | lshr _ | ashr _ | rotl _ | rotr _ | cmp _ _ _ _ | select _ =>
    dsimp only [opCodeToTFlat0] at h
    cases ht : tyToTy0 _ with
    | error e => rw [ht, except_bind_err] at h; cases h
    | ok t0 => rw [ht, except_bind_ok] at h; cases h; exact Or.inl ⟨_, _, rfl⟩
  | ofBool _ | udiv _ | urem _ | sdiv _ | srem _ =>
    dsimp only [opCodeToTFlat0] at h
    cases hw : bitsToWidth0 _ with
    | error e => rw [hw, except_bind_err] at h; cases h
    | ok w => rw [hw, except_bind_ok] at h; cases h; exact Or.inl ⟨_, _, rfl⟩
  | zext _ _ | sext _ _ | trunc _ _ =>
    dsimp only [opCodeToTFlat0] at h
    cases hm : bitsToWidth0 _ with
    | error e => rw [hm, except_bind_err] at h; cases h
    | ok wm =>
      rw [hm, except_bind_ok] at h
      cases hn : bitsToWidth0 _ with
      | error e => rw [hn, except_bind_err] at h; cases h
      | ok wn => rw [hn, except_bind_ok] at h; cases h; exact Or.inl ⟨_, _, rfl⟩
  | _ => dsimp only [opCodeToTFlat0] at h; cases h

private theorem opCodeToTFlat0_wp {Γ : Env} {symName : Sym0 → Sym} {curRs : List Ty0}
    {vs : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    {Q : Post (ty0ListToTy curRs)} {X : XPost} {m : Mem 64} :
    ∀ {sig rs : List Ty} (code : OpCode sig rs) (args : Tup (Arg K) sig)
      (k : TFlat (ty0ListToTy curRs)) (k0 node0 : TFlat0),
      opToTFlat0 code args k0 = .ok node0 →
      argsIdxLtU32 args = true →
      (∀ argv (rs' : Tup Val rs),
        denoteArgs vs args = some argv →
        wp Γ Q X (denote Val Cont k (pushTup rs' vs) ls) m →
        wp0 Γ symName curRs (pushTup rs' vs) ls Q X k0 m) →
      wp Γ Q X (denote Val Cont (.let_ ⟨code, args⟩ k) vs ls) m →
      wp0 Γ symName curRs vs ls Q X node0 m := by
  intro sig rs code args k k0 node0 hop hi hk hwp
  dsimp only [denote] at hwp
  cases hd : denoteArgs vs args with
  | none => rw [hd] at hwp; exact absurd hwp (by dsimp only [wp]; exact id)
  | some argv =>
    rw [hd] at hwp
    dsimp only [wp, Op.wp] at hwp
    dsimp only [opToTFlat0] at hop
    cases hargs0 : tupArgsToList0 sig args with
    | error _ => simp [hargs0, except_bind_err] at hop
    | ok args0 =>
      simp only [hargs0, except_bind_ok] at hop
      have hev := evalArgs0Ty_tupArgsToList0 (vs := vs) hargs0 hi
      rw [hd] at hev
      dsimp only [Option.map] at hev
      have hk' : ∀ (rs' : Tup Val rs),
          wp Γ Q X (denote Val Cont k (pushTup rs' vs) ls) m →
          wp0 Γ symName curRs (pushTup rs' vs) ls Q X k0 m := fun rs' => hk argv rs' hd
      cases code with
      | copy t | neg t | not t | add t | sub t | mul t | and t | or t | xor t | shl t
      | lshr t | ashr t | rotl t | rotr t | select t =>
        dsimp only [opCodeToTFlat0] at hop
        cases ht : tyToTy0 t with
        | error _ => simp [ht, except_bind_err] at hop
        | ok t0 =>
          simp only [ht, except_bind_ok, Except.ok.injEq] at hop
          subst hop
          have hty := ty0ToTy_tyToTy0 ht
          subst hty
          rw [wp0_let1]
          cases t0 <;> (
            dsimp only [op0ArgTys, op0RetTys, op0ToOpCode] at hev ⊢
            dsimp only [ty0ListToTy, List.map, ty0ToTy] at hev ⊢
            rw [hev]; exact OpCode.wp_mono _ _ (fun rs' => hk' rs') hwp)
      | cmp co t t' he =>
        subst he
        dsimp only [opCodeToTFlat0] at hop
        cases ht : tyToTy0 t with
        | error _ => simp [ht, except_bind_err] at hop
        | ok t0 =>
          simp only [ht, except_bind_ok, Except.ok.injEq] at hop
          subst hop
          have hty := ty0ToTy_tyToTy0 ht
          subst hty
          rw [wp0_let1]
          cases t0 <;> (
            dsimp only [op0ArgTys, op0RetTys, op0ToOpCode] at hev ⊢
            dsimp only [ty0ListToTy, List.map, ty0ToTy] at hev ⊢
            rw [hev]; exact OpCode.wp_mono _ _ (fun rs' => hk' rs') hwp)
      | ofBool n =>
        dsimp only [opCodeToTFlat0] at hop
        cases hw : bitsToWidth0 n with
        | error _ => simp [hw, except_bind_err] at hop
        | ok w =>
          simp only [hw, except_bind_ok, Except.ok.injEq] at hop
          subst hop
          have ⟨hwb, _⟩ := bitsToWidth0_spec hw
          subst hwb
          rw [wp0_let1]
          cases w <;>
            (dsimp only [op0ArgTys, op0RetTys, op0ToOpCode, ty0ListToTy, List.map, ty0ToTy,
               castWidthBool0, widthTy0, Width.bits] at hev ⊢;
             rw [hev]; exact OpCode.wp_mono _ _ (fun rs' => hk' rs') hwp)
      | zext m' n | sext m' n | trunc m' n =>
        dsimp only [opCodeToTFlat0] at hop
        cases hm : bitsToWidth0 m' with
        | error _ => simp [hm, except_bind_err] at hop
        | ok wm =>
          cases hn : bitsToWidth0 n with
          | error _ => simp [hm, hn, except_bind_ok, except_bind_err] at hop
          | ok wn =>
            simp only [hm, hn, except_bind_ok, Except.ok.injEq] at hop
            subst hop
            have ⟨hmb, _⟩ := bitsToWidth0_spec hm
            have ⟨hnb, _⟩ := bitsToWidth0_spec hn
            subst hmb; subst hnb
            rw [wp0_let1]
            cases wm <;> cases wn <;>
              (dsimp only [op0ArgTys, op0RetTys, op0ToOpCode, ty0ListToTy, List.map, ty0ToTy,
                 castWidth2Op0, widthTy0, Width.bits] at hev ⊢;
               rw [hev]; exact OpCode.wp_mono _ _ (fun rs' => hk' rs') hwp)
      | udiv n | urem n | sdiv n | srem n =>
        dsimp only [opCodeToTFlat0] at hop
        cases hw : bitsToWidth0 n with
        | error _ => simp [hw, except_bind_err] at hop
        | ok w =>
          simp only [hw, except_bind_ok, Except.ok.injEq] at hop
          subst hop
          have ⟨hwb, _⟩ := bitsToWidth0_spec hw
          subst hwb
          rw [wp0_let1]
          cases w <;>
            (dsimp only [op0ArgTys, op0RetTys, op0ToOpCode, ty0ListToTy, List.map, ty0ToTy,
               castWidthDiv0, widthTy0, Width.bits] at hev ⊢;
             rw [hev]; exact OpCode.wp_mono _ _ (fun rs' => hk' rs') hwp)
      | umulw n =>
        obtain ⟨rfl, a0, b0, rfl, rfl⟩ := opCodeToTFlat0_umulw hop
        rcases args with ⟨a', b', ⟨⟩⟩
        dsimp only [argsIdxLtU32] at hi
        simp only [Bool.and_eq_true] at hi
        dsimp only [tupArgsToList0] at hargs0
        cases ha1 : argToArg0 i64 a' with
        | error _ => simp [ha1, except_bind_err] at hargs0
        | ok a1 =>
          cases hb1 : argToArg0 i64 b' with
          | error _ => simp [ha1, hb1, except_bind_ok, except_bind_err] at hargs0
          | ok b1 =>
            simp only [ha1, hb1, except_bind_ok, Except.ok.injEq, List.cons.injEq,
              and_true] at hargs0
            obtain ⟨rfl, rfl⟩ := hargs0
            cases ha' : denoteArg vs a' with
            | none => dsimp only [denoteArgs] at hd; rw [ha'] at hd; cases hd
            | some va =>
              cases hb' : denoteArg vs b' with
              | none => dsimp only [denoteArgs] at hd; rw [ha', hb'] at hd; cases hd
              | some vb =>
                dsimp only [denoteArgs] at hd
                rw [ha', hb'] at hd
                cases hd
                rw [wp0_let2Umulw64]
                have hea := evalArg0Ty_argToArg0 (vs := vs) ha1 hi.1
                have heb := evalArg0Ty_argToArg0 (vs := vs) hb1 hi.2.1
                rw [ha'] at hea; rw [hb'] at heb
                simp only [Option.map] at hea heb
                rw [hea, heb]
                exact OpCode.wp_mono _ _ (fun rs' => hk' rs') hwp
      | bitcast t u hcast =>
        obtain ⟨nb, t0, rfl, rfl, hm, rfl⟩ := opCodeToTFlat0_bitcast hop
        have hty := ty0ToTy_tyToTy0 hm
        rw [wp0_let1]
        rcases argv with ⟨va, ⟨⟩⟩
        dsimp only [vals, OpCode.wp] at hwp
        have hcast_id : ofBits (.bits nb) ((toBits (.bits nb) va.val).cast hcast) = va.val :=
          BitVec.eq_of_toNat_eq rfl
        rw [hcast_id] at hwp
        cases t0 with
        | bool => cases hty
        | b8 | b16 | b32 | b64 =>
          dsimp only [ty0ToTy] at hty
          cases hty
          dsimp only [op0ArgTys, op0RetTys, op0ToOpCode, ty0ListToTy, List.map, ty0ToTy] at hev ⊢
          rw [hev]
          exact hk' (va.val, ()) hwp
      | _ => dsimp only [opCodeToTFlat0] at hop; cases hop

def mapConts0 {bodies : List (List Ty0 × TFlat0)} :
    {sig : List (List Ty)} → sig = bodies.map (fun p => ty0ListToTy p.1) →
    Tup Cont (bodies.map (fun p => ty0ListToTy p.1)) → Tup Cont sig
  | _, rfl, Js => Js

private theorem pushConts0_eq {bodies : List (List Ty0 × TFlat0)} {sig : List (List Ty)}
    (hsig : sig = bodies.map (fun p => ty0ListToTy p.1))
    (Js : Tup Cont (bodies.map (fun p => ty0ListToTy p.1)))
    (ls : List ((ts : List Ty) × Cont ts)) :
    pushTup (mapConts0 hsig Js) ls = pushConts0 bodies Js ls := by
  subst hsig; induction bodies generalizing ls with
  | nil => rfl
  | cons p rest ih => rcases Js with ⟨j, js⟩; exact ih js _

private theorem closed_mapConts0_nil {Γ : Env} {rs : List Ty}
    {vs : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    {Q : Post rs} {X : XPost}
    (hc : [] = List.map (fun p : List Ty0 × TFlat0 => ty0ListToTy p.1) []) :
    Closed Γ Q X (denoteB Val Cont (TBlocks.nil (rs := rs)) vs ls) (mapConts0 hc ()) := by
  trivial

private theorem closed_mapConts0_cons {Γ : Env} {rs : List Ty}
    {vs : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    {Q : Post rs} {X : XPost}
    {ts : List Ty} {sig : List (List Ty)} {b : TFlat rs} {bs : TBlocks rs sig}
    {ts0 : List Ty0} {b0 : TFlat0} {rest0 : List (List Ty0 × TFlat0)}
    (hts : ty0ListToTy ts0 = ts)
    (hsig : sig = rest0.map (fun p => ty0ListToTy p.1))
    (hc : ts :: sig = ((ts0, b0) :: rest0).map (fun p => ty0ListToTy p.1))
    {j : Cont (ty0ListToTy ts0)} {js : Tup Cont (rest0.map (fun p => ty0ListToTy p.1))} :
    (∀ (xs : Tup Val (ty0ListToTy ts0)) m,
      wp Γ Q X (denote Val Cont b (pushTup xs vs) ls) m → j xs m) →
    Closed Γ Q X (denoteB Val Cont bs vs ls) (mapConts0 hsig js) →
    Closed Γ Q X (denoteB Val Cont (.cons b bs) vs ls) (mapConts0 hc (j, js)) := by
  subst hts; subst hsig; intro h1 h2; exact ⟨h1, h2⟩

theorem bridge_tblocksToList0_sig {tbl : List (Sym × Sym0)} {rs : List Ty} :
    ∀ {sig : List (List Ty)} {bodies : TBlocks rs sig} {bs0 : List (List Ty0 × TFlat0)},
      tblocksToList0 tbl bodies = .ok bs0 → sig = bs0.map (fun p => ty0ListToTy p.1)
  | _, .nil, bs0, h => by
    dsimp only [tblocksToList0] at h; cases h; rfl
  | _, .cons (ts := ts) b bs, bs0, h => by
    dsimp only [tblocksToList0] at h
    cases hts : tyListToTy0 ts with
    | error _ => simp [hts, except_bind_err] at h
    | ok ts0 =>
      cases hb : tflatToTFlat0 tbl b with
      | error _ => simp [hts, hb, except_bind_ok, except_bind_err] at h
      | ok b0 =>
        cases hrest : tblocksToList0 tbl bs with
        | error _ => simp [hts, hb, hrest, except_bind_ok, except_bind_err] at h
        | ok rest0 =>
          simp only [hts, hb, hrest, except_bind_ok, Except.ok.injEq] at h
          subst h
          simp only [List.map_cons, ty0ListToTy_tyListToTy0 hts]
          exact congrArg (ts :: ·) (bridge_tblocksToList0_sig hrest)

mutual
theorem bridge_tflatToTFlat0_wp_aux {tbl : List (Sym × Sym0)} {Γ : Env}
    (hsym : ∀ s fid, lookupSymId? tbl s = some fid → symNameOf tbl fid = s)
    {rs0 : List Ty0} (tf : TFlat (ty0ListToTy rs0)) (tf0 : TFlat0)
    (htf : tflatToTFlat0 tbl tf = .ok tf0) (hi : tflatIdxLtU32 tf = true)
    (vs : List ((t : Ty) × Val t)) (ls : List ((ts : List Ty) × Cont ts))
    (Q : Post (ty0ListToTy rs0)) (X : XPost) (m : Mem 64)
    (hwp : wp Γ Q X (denote Val Cont tf vs ls) m) :
    wp0 Γ (symNameOf tbl) rs0 vs ls Q X tf0 m := by
  match tf with
  | .let_ op k =>
    dsimp only [tflatToTFlat0, tflatIdxLtU32] at htf hi
    simp only [Bool.and_eq_true] at hi
    cases hk0 : tflatToTFlat0 tbl k with
    | error _ => simp [hk0, except_bind_err] at htf
    | ok k0 =>
      simp only [hk0, except_bind_ok] at htf
      exact opCodeToTFlat0_wp op.code op.args k k0 tf0 htf hi.1
        (fun _ rs' _ hk' => bridge_tflatToTFlat0_wp_aux hsym k k0 hk0 hi.2 _ _ Q X m hk') hwp
  | .load t a k =>
    dsimp only [tflatToTFlat0, tflatIdxLtU32] at htf hi
    simp only [Bool.and_eq_true] at hi
    cases ht0 : tyToTy0 t with
    | error _ => simp [ht0, except_bind_err] at htf
    | ok t0 =>
      cases ha0 : argToArg0 i64 a with
      | error _ => simp [ht0, ha0, except_bind_ok, except_bind_err] at htf
      | ok a0 =>
        cases hk0 : tflatToTFlat0 tbl k with
        | error _ => simp [ht0, ha0, hk0, except_bind_ok, except_bind_err] at htf
        | ok k0 =>
          simp only [ht0, ha0, hk0, except_bind_ok, Except.ok.injEq] at htf
          subst htf
          have hty := ty0ToTy_tyToTy0 ht0
          dsimp only [denote] at hwp
          cases hda : denoteArg vs a with
          | none => rw [hda] at hwp; exact absurd hwp (by dsimp only [wp]; exact id)
          | some a' =>
            rw [hda] at hwp; dsimp only [wp] at hwp
            rcases hwp with ⟨v, hlv, hk'⟩
            have hev := evalArg0Ty_argToArg0 (vs := vs) ha0 hi.1
            rw [hda] at hev; dsimp only [Option.map] at hev
            rw [wp0_load, hev, hty]
            exact ⟨v, hlv, bridge_tflatToTFlat0_wp_aux hsym k k0 hk0 hi.2 _ _ Q X m hk'⟩
  | .store (t := t) v a k =>
    dsimp only [tflatToTFlat0, tflatIdxLtU32] at htf hi
    simp only [Bool.and_eq_true] at hi
    cases ht0 : tyToTy0 t with
    | error _ => simp [ht0, except_bind_err] at htf
    | ok t0 =>
      cases hv0 : argToArg0 t v with
      | error _ => simp [ht0, hv0, except_bind_ok, except_bind_err] at htf
      | ok v0 =>
        cases ha0 : argToArg0 i64 a with
        | error _ => simp [ht0, hv0, ha0, except_bind_ok, except_bind_err] at htf
        | ok a0 =>
          cases hk0 : tflatToTFlat0 tbl k with
          | error _ => simp [ht0, hv0, ha0, hk0, except_bind_ok, except_bind_err] at htf
          | ok k0 =>
            simp only [ht0, hv0, ha0, hk0, except_bind_ok, Except.ok.injEq] at htf
            subst htf
            have hty := ty0ToTy_tyToTy0 ht0
            dsimp only [denote] at hwp
            cases hdv : denoteArg vs v with
            | none => rw [hdv] at hwp; exact absurd hwp (by dsimp only [wp]; exact id)
            | some v' =>
              cases hda : denoteArg vs a with
              | none => rw [hdv, hda] at hwp; exact absurd hwp (by dsimp only [wp]; exact id)
              | some a' =>
                rw [hdv, hda] at hwp; dsimp only [wp] at hwp
                have hev1 := evalArg0Ty_argToArg0 (vs := vs) hv0 hi.1.1
                have hev2 := evalArg0Ty_argToArg0 (vs := vs) ha0 hi.1.2
                rw [hdv] at hev1; rw [hda] at hev2
                dsimp only [Option.map] at hev1 hev2
                subst hty
                rw [wp0_store, hev1, hev2]
                exact ⟨hwp.1, bridge_tflatToTFlat0_wp_aux hsym k k0 hk0 hi.2 _ _ Q X _ hwp.2⟩
  | .call f (as := as) bs args k =>
    dsimp only [tflatToTFlat0, tflatIdxLtU32] at htf hi
    simp only [Bool.and_eq_true] at hi
    cases hfid : lookupSymId? tbl f with
    | none => simp [hfid] at htf
    | some fid =>
      cases has0 : tyListToTy0 as with
      | error _ => simp [hfid, has0, except_bind_err] at htf
      | ok as0 =>
        cases hbs0 : tyListToTy0 bs with
        | error _ => simp [hfid, has0, hbs0, except_bind_ok, except_bind_err] at htf
        | ok bs0 =>
          cases hargs0 : tupArgsToList0 as args with
          | error _ => simp [hfid, has0, hbs0, hargs0, except_bind_ok, except_bind_err] at htf
          | ok args0 =>
            cases hk0 : tflatToTFlat0 tbl k with
            | error _ =>
              simp [hfid, has0, hbs0, hargs0, hk0, except_bind_ok, except_bind_err] at htf
            | ok k0 =>
              simp only [hfid, has0, hbs0, hargs0, hk0, except_bind_ok, Except.ok.injEq] at htf
              subst htf
              have has_eq := ty0ListToTy_tyListToTy0 has0
              have hbs_eq := ty0ListToTy_tyListToTy0 hbs0
              subst has_eq; subst hbs_eq
              dsimp only [denote] at hwp
              cases hda : denoteArgs vs args with
              | none => rw [hda] at hwp; exact absurd hwp (by dsimp only [wp]; exact id)
              | some argv =>
                rw [hda] at hwp; dsimp only [wp] at hwp
                rcases hwp with ⟨P, E, hΓ, hP, hE⟩
                have hev := evalArgs0Ty_tupArgsToList0 (vs := vs) hargs0 hi.1
                rw [hda] at hev; dsimp only [Option.map] at hev
                rw [wp0_call, hev, hsym f fid hfid]
                exact ⟨P, E, hΓ, fun r m' hr =>
                  bridge_tflatToTFlat0_wp_aux hsym k k0 hk0 hi.2 _ _ Q X m' (hP r m' hr), hE⟩
  | .jnz c t e =>
    dsimp only [tflatToTFlat0, tflatIdxLtU32] at htf hi
    simp only [Bool.and_eq_true] at hi
    cases hc0 : argToArg0 .bool c with
    | error _ => simp [hc0, except_bind_err] at htf
    | ok c0 =>
      cases ht0 : tflatToTFlat0 tbl t with
      | error _ => simp [hc0, ht0, except_bind_ok, except_bind_err] at htf
      | ok t0 =>
        cases he0 : tflatToTFlat0 tbl e with
        | error _ => simp [hc0, ht0, he0, except_bind_ok, except_bind_err] at htf
        | ok e0 =>
          simp only [hc0, ht0, he0, except_bind_ok, Except.ok.injEq] at htf
          subst htf
          dsimp only [denote] at hwp
          cases hdc : denoteArg vs c with
          | none => rw [hdc] at hwp; exact absurd hwp (by dsimp only [wp]; exact id)
          | some c' =>
            rw [hdc] at hwp; dsimp only [wp] at hwp
            have hev := evalArg0Ty_argToArg0 (vs := vs) hc0 hi.1.1
            rw [hdc] at hev; dsimp only [Option.map] at hev
            rw [wp0_jnz, hev]
            exact ⟨fun h => bridge_tflatToTFlat0_wp_aux hsym t t0 ht0 hi.1.2 _ _ Q X m (hwp.1 h),
                   fun h => bridge_tflatToTFlat0_wp_aux hsym e e0 he0 hi.2 _ _ Q X m (hwp.2 h)⟩
  | .jump (ts := ts) j args =>
    dsimp only [tflatToTFlat0, tflatIdxLtU32] at htf hi
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
    cases hargs0 : tupArgsToList0 ts args with
    | error _ => simp [hargs0, except_bind_err] at htf
    | ok args0 =>
      simp only [hargs0, except_bind_ok, Except.ok.injEq] at htf
      subst htf
      dsimp only [denote] at hwp
      cases hl : lookupL ls ts j with
      | none => rw [hl] at hwp; exact absurd hwp (by dsimp only [wp]; exact id)
      | some J =>
        cases hda : denoteArgs vs args with
        | none => rw [hl, hda] at hwp; exact absurd hwp (by dsimp only [wp]; exact id)
        | some argv =>
          rw [hl, hda] at hwp; dsimp only [wp] at hwp
          dsimp only [lookupL] at hl
          cases hlg : listGet? ls j with
          | none => simp [hlg] at hl
          | some p =>
            rcases p with ⟨ts', J'⟩
            simp only [hlg] at hl
            dsimp only [castListTy] at hl
            cases hdec : listTyDecEq ts' ts with
            | isFalse _ => simp [hdec] at hl
            | isTrue heq =>
              subst heq
              simp only [hdec, Option.some.injEq] at hl
              subst hl
              have hev := evalArgs0Ty_tupArgsToList0 (vs := vs) hargs0 hi.2
              rw [hda] at hev; dsimp only [Option.map] at hev
              rw [wp0_jump, UInt32.toNat_ofNat_of_lt' hi.1, hlg]
              dsimp only
              rw [hev]
              exact hwp
  | .ret vs' =>
    dsimp only [tflatToTFlat0, tflatIdxLtU32] at htf hi
    cases hvs0 : tupArgsToList0 (ty0ListToTy rs0) vs' with
    | error _ => simp [hvs0, except_bind_err] at htf
    | ok vs0 =>
      simp only [hvs0, except_bind_ok, Except.ok.injEq] at htf
      subst htf
      dsimp only [denote] at hwp
      cases hda : denoteArgs vs vs' with
      | none => rw [hda] at hwp; exact absurd hwp (by dsimp only [wp]; exact id)
      | some rvs =>
        rw [hda] at hwp; dsimp only [wp] at hwp
        have hev := evalArgs0Ty_tupArgsToList0 (vs := vs) hvs0 hi
        rw [hda] at hev; dsimp only [Option.map] at hev
        rw [wp0_ret, hev]
        exact hwp
  | .exit f (as := as) args =>
    dsimp only [tflatToTFlat0, tflatIdxLtU32] at htf hi
    cases hfid : lookupSymId? tbl f with
    | none => simp [hfid] at htf
    | some fid =>
      cases has0 : tyListToTy0 as with
      | error _ => simp [hfid, has0, except_bind_err] at htf
      | ok as0 =>
        cases hargs0 : tupArgsToList0 as args with
        | error _ => simp [hfid, has0, hargs0, except_bind_ok, except_bind_err] at htf
        | ok args0 =>
          simp only [hfid, has0, hargs0, except_bind_ok, Except.ok.injEq] at htf
          subst htf
          have has_eq := ty0ListToTy_tyListToTy0 has0
          subst has_eq
          dsimp only [denote] at hwp
          cases hda : denoteArgs vs args with
          | none => rw [hda] at hwp; exact absurd hwp (by dsimp only [wp]; exact id)
          | some argv =>
            rw [hda] at hwp; dsimp only [wp] at hwp
            have hev := evalArgs0Ty_tupArgsToList0 (vs := vs) hargs0 hi
            rw [hda] at hev; dsimp only [Option.map] at hev
            rw [wp0_exit, hev, hsym f fid hfid]
            exact hwp
  | .hlt =>
    dsimp only [tflatToTFlat0] at htf; cases htf
    exact absurd hwp (by dsimp only [denote, wp]; exact id)
  | .group (sig := sig) bodies k =>
    dsimp only [tflatToTFlat0, tflatIdxLtU32] at htf hi
    simp only [Bool.and_eq_true] at hi
    cases hbs0 : tblocksToList0 tbl bodies with
    | error _ => simp [hbs0, except_bind_err] at htf
    | ok bs0 =>
      cases hk0 : tflatToTFlat0 tbl k with
      | error _ => simp [hbs0, hk0, except_bind_ok, except_bind_err] at htf
      | ok k0 =>
        simp only [hbs0, hk0, except_bind_ok, Except.ok.injEq] at htf
        subst htf
        have hsig := bridge_tblocksToList0_sig hbs0
        rw [wp0_group]
        intro Js hcl0
        dsimp only [denote, wp] at hwp
        have hcl : Closed Γ Q X (denoteB Val Cont bodies vs (pushTup (mapConts0 hsig Js) ls))
            (mapConts0 hsig Js) := by
          rw [pushConts0_eq hsig Js ls]
          exact bridge_tblocksToList0_closed_aux hsym bodies bs0 hbs0 hi.1 hsig vs
            (pushConts0 bs0 Js ls) Q X Js hcl0
        exact bridge_tflatToTFlat0_wp_aux hsym k k0 hk0 hi.2 vs (pushConts0 bs0 Js ls) Q X m
          (by rw [← pushConts0_eq hsig Js ls]; exact hwp (mapConts0 hsig Js) hcl)

theorem bridge_tblocksToList0_closed_aux {tbl : List (Sym × Sym0)} {Γ : Env}
    (hsym : ∀ s fid, lookupSymId? tbl s = some fid → symNameOf tbl fid = s)
    {rs0 : List Ty0}
    {sig : List (List Ty)} (bodies : TBlocks (ty0ListToTy rs0) sig)
    (bs0 : List (List Ty0 × TFlat0)) :
    tblocksToList0 tbl bodies = .ok bs0 → tblocksIdxLtU32 bodies = true →
    (hsig : sig = bs0.map (fun p => ty0ListToTy p.1)) →
    ∀ (vs : List ((t : Ty) × Val t)) (ls : List ((ts : List Ty) × Cont ts))
      (Q : Post (ty0ListToTy rs0)) (X : XPost)
      (Js : Tup Cont (bs0.map (fun p => ty0ListToTy p.1))),
      closed0 Γ (symNameOf tbl) rs0 vs ls Q X bs0 Js →
      Closed Γ Q X (denoteB Val Cont bodies vs ls) (mapConts0 hsig Js) := by
  cases bodies with
  | nil =>
    intro hbs _ hsig vs ls Q X Js _
    cases bs0 with
    | nil =>
      rcases Js with ⟨⟩
      exact closed_mapConts0_nil hsig
    | cons _ _ => dsimp only [tblocksToList0] at hbs; cases hbs
  | @cons ts _ b bs =>
    intro hbs hi hsig vs ls Q X Js hcl
    cases bs0 with
    | nil =>
      dsimp only [tblocksToList0] at hbs
      cases hts : tyListToTy0 ts <;> simp [hts, except_bind_err] at hbs
      cases hb : tflatToTFlat0 tbl b <;> simp [hb, except_bind_ok, except_bind_err] at hbs
      cases hr : tblocksToList0 tbl bs <;> simp [hr, except_bind_ok, except_bind_err] at hbs
    | cons p rest0 =>
      rcases Js with ⟨j, js⟩
      dsimp only [tblocksToList0, tblocksIdxLtU32] at hbs hi
      simp only [Bool.and_eq_true] at hi
      cases hts : tyListToTy0 ts with
      | error _ => simp [hts, except_bind_err] at hbs
      | ok ts0 =>
        cases hb : tflatToTFlat0 tbl b with
        | error _ => simp [hts, hb, except_bind_ok, except_bind_err] at hbs
        | ok b0 =>
          cases hrest : tblocksToList0 tbl bs with
          | error _ => simp [hts, hb, hrest, except_bind_ok, except_bind_err] at hbs
          | ok rest0' =>
            simp only [hts, hb, hrest, except_bind_ok, Except.ok.injEq] at hbs
            cases hbs
            rw [closed0_cons] at hcl
            exact closed_mapConts0_cons (ty0ListToTy_tyListToTy0 hts)
              (bridge_tblocksToList0_sig hrest) hsig
              (fun xs m hw =>
                hcl.1 xs m (bridge_tflatToTFlat0_wp_aux hsym b b0 hb hi.1 _ ls Q X m hw))
              (bridge_tblocksToList0_closed_aux hsym bs rest0 hrest hi.2 _ vs ls Q X js hcl.2)
end

/-- `Bridge0.tflatToTFlat0` preserves `wp` as `wp0` on every well-bounded `TFlat`. -/
theorem bridge_tflatToTFlat0_wp {tbl : List (Sym × Sym0)} {Γ : Env}
    (hsym : ∀ s fid, lookupSymId? tbl s = some fid → symNameOf tbl fid = s)
    {rs : List Ty} {rs0 : List Ty0} (hrs : ty0ListToTy rs0 = rs)
    (tf : TFlat rs) (tf0 : TFlat0)
    (htf : tflatToTFlat0 tbl tf = .ok tf0) (hi : tflatIdxLtU32 tf = true)
    (vs : List ((t : Ty) × Val t)) (ls : List ((ts : List Ty) × Cont ts))
    (Q : Post rs) (X : XPost) (m : Mem 64)
    (hwp : wp Γ Q X (denote Val Cont tf vs ls) m) :
    wp0 Γ (symNameOf tbl) rs0 vs ls (hrs ▸ Q) X tf0 m := by
  subst hrs
  exact bridge_tflatToTFlat0_wp_aux hsym tf tf0 htf hi vs ls Q X m hwp

/-- `Bridge0.tblocksToList0` preserves `closed0` as `Closed`. -/
theorem bridge_tblocksToList0_closed {tbl : List (Sym × Sym0)} {Γ : Env}
    (hsym : ∀ s fid, lookupSymId? tbl s = some fid → symNameOf tbl fid = s)
    {rs : List Ty} {rs0 : List Ty0} (hrs : ty0ListToTy rs0 = rs)
    {sig : List (List Ty)} (bodies : TBlocks rs sig) (bs0 : List (List Ty0 × TFlat0))
    (hbs : tblocksToList0 tbl bodies = .ok bs0) (hi : tblocksIdxLtU32 bodies = true)
    (hsig : sig = bs0.map (fun p => ty0ListToTy p.1))
    (vs : List ((t : Ty) × Val t)) (ls : List ((ts : List Ty) × Cont ts))
    (Q : Post rs) (X : XPost) (Js : Tup Cont (bs0.map (fun p => ty0ListToTy p.1)))
    (hcl : closed0 Γ (symNameOf tbl) rs0 vs ls (hrs ▸ Q) X bs0 Js) :
    Closed Γ Q X (denoteB Val Cont bodies vs ls) (mapConts0 hsig Js) := by
  subst hrs
  exact bridge_tblocksToList0_closed_aux hsym bodies bs0 hbs hi hsig vs ls Q X Js hcl

/-! ## 3. `Legal0` Validation Soundness & AST Worklist Step Bounds -/

mutual
/-- Total AST node count matching `legalWorkLoop0`, `preWorkLoop0`, and `regaWorkLoop0` pops. -/
@[expose] def nodeCount0 : TFlat0 → Nat
  | .let1 _ _ k => 1 + nodeCount0 k
  | .let2Umulw64 _ _ k => 1 + nodeCount0 k
  | .load _ _ k => 1 + nodeCount0 k
  | .store _ _ _ k => 1 + nodeCount0 k
  | .call _ _ _ _ k => 1 + nodeCount0 k
  | .jnz _ t e => 1 + nodeCount0 t + nodeCount0 e
  | .group bodies k => 1 + blocksNodeCount0 bodies + nodeCount0 k
  | _ => 1

@[expose] def blocksNodeCount0 : List (List Ty0 × TFlat0) → Nat
  | [] => 0
  | (_, b) :: rest => nodeCount0 b + blocksNodeCount0 rest
end

/-- Total AST worklist step count across a `LegalItem0` list. -/
def legalWorkCount0 : List LegalItem0 → Nat
  | [] => 0
  | item :: rest => nodeCount0 item.node + legalWorkCount0 rest

/-- Structural well-typedness of `node` under `LegalCtx0`, `venv`, `lenv` (`legalMod0 = 0`). -/
inductive WfNode0 (ctx : LegalCtx0) : List Ty0 → List (List Ty0) → TFlat0 → Prop
  | let1 {venv lenv op args k} :
      checkOp0 venv op args = true →
      WfNode0 ctx (opRetTy0 op :: venv) lenv k →
      WfNode0 ctx venv lenv (.let1 op args k)
  | let2Umulw64 {venv lenv a b k} :
      checkArg0 venv .b64 a = true → checkArg0 venv .b64 b = true →
      WfNode0 ctx (.b64 :: .b64 :: venv) lenv k →
      WfNode0 ctx venv lenv (.let2Umulw64 a b k)
  | load {venv lenv t addr k} :
      checkArg0 venv .b64 addr = true →
      WfNode0 ctx (t :: venv) lenv k →
      WfNode0 ctx venv lenv (.load t addr k)
  | store {venv lenv t val addr k} :
      checkArg0 venv t val = true → checkArg0 venv .b64 addr = true →
      WfNode0 ctx venv lenv k →
      WfNode0 ctx venv lenv (.store t val addr k)
  | call {venv lenv fnSym as bs args k} :
      as.length ≤ 6 → bs.length ≤ 7 →
      hasSig0 ctx.sigs fnSym as bs = true → checkArgs0 venv as args = true →
      WfNode0 ctx (pushTys0 bs venv) lenv k →
      WfNode0 ctx venv lenv (.call fnSym as bs args k)
  | tailCall {venv lenv fnSym as args} :
      as.length ≤ 6 →
      hasSig0 ctx.sigs fnSym as ctx.curRs = true → checkArgs0 venv as args = true →
      WfNode0 ctx venv lenv (.tailCall fnSym as args)
  | exit {venv lenv fnSym as args} :
      as.length ≤ 6 →
      hasExit0 ctx.exits fnSym = true → checkArgs0 venv as args = true →
      WfNode0 ctx venv lenv (.exit fnSym as args)
  | jnz {venv lenv c t e} :
      checkArg0 venv .bool c = true →
      WfNode0 ctx venv lenv t → WfNode0 ctx venv lenv e →
      WfNode0 ctx venv lenv (.jnz c t e)
  | jump {venv lenv j args pts} :
      listGetSig0 lenv j = some pts → checkArgs0 venv pts args = true →
      WfNode0 ctx venv lenv (.jump j args)
  | ret {venv lenv vs} :
      checkArgs0 venv ctx.curRs vs = true →
      WfNode0 ctx venv lenv (.ret vs)
  | hlt {venv lenv} : WfNode0 ctx venv lenv .hlt
  | group {venv lenv bodies k} :
      (∀ p ∈ bodies, WfNode0 ctx (pushTys0 p.1 venv) (legalAddSigs0 bodies lenv) p.2) →
      WfNode0 ctx venv (legalAddSigs0 bodies lenv) k →
      WfNode0 ctx venv lenv (.group bodies k)

/-- Decidable bound ensuring no `List.length` checked by `tyLenU0` wraps `2^32`. -/
@[expose] def listLenFitsU32 {α : Type} (xs : List α) : Bool :=
  decide (xs.length < 2 ^ 32)

mutual
@[expose] def TFlat0.sigLensFitU32 : TFlat0 → Bool
  | .let1 _ _ k | .let2Umulw64 _ _ k | .load _ _ k | .store _ _ _ k => k.sigLensFitU32
  | .call _ as bs _ k => listLenFitsU32 as && listLenFitsU32 bs && k.sigLensFitU32
  | .tailCall _ as _ => listLenFitsU32 as
  | .exit _ as _ => listLenFitsU32 as
  | .jnz _ t e => t.sigLensFitU32 && e.sigLensFitU32
  | .group bodies k => blocksSigLensFitU32 bodies && k.sigLensFitU32
  | _ => true

@[expose] def blocksSigLensFitU32 : List (List Ty0 × TFlat0) → Bool
  | [] => true
  | (pts, b) :: rest => listLenFitsU32 pts && b.sigLensFitU32 && blocksSigLensFitU32 rest
end

@[expose] def TFlatFn0.sigLensFitU32 (fn : TFlatFn0) : Bool :=
  listLenFitsU32 fn.as && listLenFitsU32 fn.rs && fn.body.sigLensFitU32

@[expose] def TFlatModule0.sigLensFitU32 (mod : TFlatModule0) : Bool :=
  mod.fns.all TFlatFn0.sigLensFitU32 &&
    mod.externs.all (fun ex => listLenFitsU32 ex.as && listLenFitsU32 ex.rs)

private theorem tyLenU0_eq (xs : List Ty0) (acc : UInt32) :
    (tyLenU0 xs acc).toNat = (acc.toNat + xs.length) % 2 ^ 32 := by
  induction xs generalizing acc with
  | nil =>
    dsimp only [tyLenU0, List.length_nil]
    rw [Nat.add_zero, Nat.mod_eq_of_lt (UInt32.toNat_lt acc)]
  | cons _ xs ih =>
    dsimp only [tyLenU0, List.length_cons]
    rw [ih, UInt32.toNat_add, UInt32.toNat_ofNat]
    simp [Nat.add_assoc, Nat.add_comm 1]

theorem tyLenU0_eq_of_lt {xs : List Ty0} (hlt : xs.length < 2 ^ 32) :
    (tyLenU0 xs 0).toNat = xs.length := by
  rw [tyLenU0_eq xs 0, UInt32.toNat_zero, Nat.zero_add, Nat.mod_eq_of_lt hlt]

theorem tyLenU0_le_of_decide {xs : List Ty0} {k : Nat} (hk : k < 2 ^ 32)
    (hlt : xs.length < 2 ^ 32)
    (h : decide (tyLenU0 xs 0 ≤ UInt32.ofNat k) = true) : xs.length ≤ k := by
  have hle : (tyLenU0 xs 0).toNat ≤ (UInt32.ofNat k).toNat := by
    simpa [UInt32.le_iff_toNat_le] using decide_eq_true_eq.mp h
  rw [UInt32.toNat_ofNat_of_lt' hk, tyLenU0_eq_of_lt hlt] at hle
  exact hle

theorem listGetSig0_eq_listGet? : ∀ (lenv : List (List Ty0)) (j : UInt32),
    listGetSig0 lenv j = listGet? lenv j.toNat
  | [], _ => rfl
  | x :: rest, j => by
    dsimp only [listGetSig0]
    by_cases hj : j = 0
    · subst hj; rfl
    · have hnz : j.toNat ≠ 0 := fun hz => hj (by
        calc j = UInt32.ofNat j.toNat := UInt32.ofNat_toNat.symm
          _ = UInt32.ofNat 0 := by rw [hz]
          _ = 0 := rfl)
      have h1 : (1 : UInt32) ≤ j := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hnz)
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hnz
      simp only [hj, ↓reduceIte]
      rw [listGetSig0_eq_listGet? rest (j - 1), UInt32.toNat_sub_of_le j 1 h1, hm,
        UInt32.toNat_one, Nat.succ_sub_one]
      rfl

theorem listGetTyCode0_eq_listGet? : ∀ (venv : List Ty0) (idx : UInt32),
    listGetTyCode0 venv idx =
      match listGet? venv idx.toNat with
      | some t => ty0Code t
      | none => 99
  | [], _ => rfl
  | x :: rest, idx => by
    dsimp only [listGetTyCode0]
    by_cases hi : idx = 0
    · subst hi; rfl
    · have hnz : idx.toNat ≠ 0 := fun hz => hi (by
        calc idx = UInt32.ofNat idx.toNat := UInt32.ofNat_toNat.symm
          _ = UInt32.ofNat 0 := by rw [hz]
          _ = 0 := rfl)
      have h1 : (1 : UInt32) ≤ idx := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hnz)
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hnz
      simp only [hi, ↓reduceIte]
      rw [listGetTyCode0_eq_listGet? rest (idx - 1), UInt32.toNat_sub_of_le idx 1 h1, hm,
        UInt32.toNat_one, Nat.succ_sub_one]
      rfl

theorem ty0Code_inj {a b : Ty0} (h : ty0Code a = ty0Code b) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem checkArg0_spec {venv : List Ty0} {expT : Ty0} {a : Arg0}
    (h : checkArg0 venv expT a = true) :
    match a with
    | .var idx => listGet? venv idx.toNat = some expT
    | .immBool _ => expT = .bool
    | .immBits w _ => widthTy0 w = expT := by
  cases a with
  | var idx =>
    dsimp only
    dsimp only [checkArg0] at h
    rw [listGetTyCode0_eq_listGet?] at h
    cases hl : listGet? venv idx.toNat with
    | none => rw [hl] at h; exact absurd (decide_eq_true_eq.mp h) (by cases expT <;> decide)
    | some t' =>
      rw [hl] at h
      have heq := ty0Code_inj (decide_eq_true_eq.mp h)
      rw [heq]
  | immBool _ =>
    dsimp only
    dsimp only [checkArg0, ty0Eq] at h
    exact ty0Code_inj (decide_eq_true_eq.mp h)
  | immBits w _ =>
    dsimp only
    dsimp only [checkArg0, ty0Eq] at h
    exact ty0Code_inj (decide_eq_true_eq.mp h)

theorem checkArgs0_spec {venv : List Ty0} :
    ∀ {ts : List Ty0} {args : List Arg0},
      checkArgs0 venv ts args = true →
      ts.length = args.length ∧
      ∀ (k : Nat) (hk : k < ts.length) (hka : k < args.length),
        checkArg0 venv ts[k] args[k] = true
  | [], [], _ => ⟨rfl, fun _ hk _ => absurd hk (Nat.not_lt_zero _)⟩
  | [], _ :: _, h => by dsimp only [checkArgs0] at h; cases h
  | _ :: _, [], h => by dsimp only [checkArgs0] at h; cases h
  | t :: ts, a :: args, h => by
    dsimp only [checkArgs0] at h
    cases ha : checkArg0 venv t a with
    | false => rw [ha] at h; cases h
    | true =>
      rw [ha] at h
      obtain ⟨hl, hall⟩ := checkArgs0_spec h
      refine ⟨congrArg Nat.succ hl, fun k hk hka => ?_⟩
      cases k with
      | zero => exact ha
      | succ k' =>
        simpa only [List.getElem_cons_succ] using
          hall k' (Nat.lt_of_succ_lt_succ hk) (Nat.lt_of_succ_lt_succ hka)

theorem pushTys0_eq_pushTypes (ts acc : List Ty0) : pushTys0 ts acc = pushTypes ts acc := by
  induction ts generalizing acc with
  | nil => rfl
  | cons t rest ih => exact ih (t :: acc)

theorem legalAddSigs0_eq_pushTypes (bodies : List (List Ty0 × TFlat0)) (acc : List (List Ty0)) :
    legalAddSigs0 bodies acc = pushTypes (bodies.map Prod.fst) acc := by
  induction bodies generalizing acc with
  | nil => rfl
  | cons p rest ih => exact ih (p.1 :: acc)

private theorem nodeCount0_pos (n : TFlat0) : 0 < nodeCount0 n := by
  cases n <;> dsimp only [nodeCount0] <;> omega

private theorem legalWorkCount0_advance (cur : LegalItem0) (rest : List LegalItem0) :
    legalWorkCount0 (legalAdvance0 cur rest) + 1 = legalWorkCount0 (cur :: rest) := by
  have pushLen : ∀ (bs : List (List Ty0 × TFlat0)) (v : List Ty0) (l : List (List Ty0))
      (w : List LegalItem0),
      legalWorkCount0 (legalPushGroup0 bs v l w) = blocksNodeCount0 bs + legalWorkCount0 w := by
    intro bs v l w
    induction bs generalizing w with
    | nil => dsimp only [legalPushGroup0, blocksNodeCount0]; exact (Nat.zero_add _).symm
    | cons p bs' ih =>
      rcases p with ⟨_, b⟩
      dsimp only [legalPushGroup0, blocksNodeCount0]
      rw [ih]; dsimp only [legalWorkCount0]; omega
  rcases cur with ⟨nd, venv, lenv⟩
  cases nd with
  | tailCall _ _ _ | jump _ _ | ret _ | exit _ _ _ | hlt =>
    dsimp only [legalAdvance0, isTerm0]
    simp only [↓reduceIte]
    dsimp only [legalWorkCount0, nodeCount0]; omega
  | jnz _ t e =>
    dsimp only [legalAdvance0, isTerm0]
    simp only [Bool.false_eq_true, ↓reduceIte]
    dsimp only [legalAdvJnz0, legalWorkCount0, nodeCount0]; omega
  | group bodies k =>
    dsimp only [legalAdvance0, isTerm0]
    simp only [Bool.false_eq_true, ↓reduceIte]
    dsimp only [legalAdvGroup0, legalWorkCount0, nodeCount0]
    rw [pushLen]; omega
  | let1 _ _ k | let2Umulw64 _ _ k | load _ _ k | store _ _ _ k | call _ _ _ _ k =>
    dsimp only [legalAdvance0, isTerm0]
    simp only [Bool.false_eq_true, ↓reduceIte]
    dsimp only [legalAdvLin0, linK0, legalWorkCount0, nodeCount0]; omega

private theorem hasFnSym0_mem {fns : List TFlatFn0} {sym : Sym0} :
    hasFnSym0 fns sym = true ↔ sym ∈ fns.map TFlatFn0.name := by
  induction fns with
  | nil =>
    dsimp only [hasFnSym0, List.map_nil]
    exact ⟨fun h => Bool.noConfusion h, fun h => nomatch h⟩
  | cons f rest ih =>
    dsimp only [hasFnSym0, List.map_cons, List.mem_cons]
    by_cases h : f.name = sym
    · subst h; simp
    · simp only [h, ↓reduceIte]
      exact ih.trans (by simp [Ne.symm h])

/-- Combined well-typedness + `sigLensFitU32` item invariant for `legalWorkLoop0`. -/
private def LegalWorkPred (ctx : LegalCtx0) (work : List LegalItem0) : Prop :=
  ∀ item ∈ work, item.node.sigLensFitU32 = true →
    WfNode0 ctx item.venv item.lenv item.node

private theorem legalPushGroup0_wf {ctx : LegalCtx0} {bodies : List (List Ty0 × TFlat0)}
    {venv : List Ty0} {lenv' : List (List Ty0)} {work : List LegalItem0}
    (hsub : ∀ item ∈ legalPushGroup0 bodies venv lenv' work,
      item.node.sigLensFitU32 = true → WfNode0 ctx item.venv item.lenv item.node) :
    (∀ p ∈ bodies, p.2.sigLensFitU32 = true → WfNode0 ctx (pushTys0 p.1 venv) lenv' p.2) ∧
      LegalWorkPred ctx work := by
  induction bodies generalizing work with
  | nil => exact ⟨(fun _ hp => nomatch hp), hsub⟩
  | cons p bs ih =>
    dsimp only [legalPushGroup0] at hsub
    obtain ⟨hbs, hwk⟩ := ih hsub
    refine ⟨fun q hq hfit => ?_, fun item hmem => hwk item (List.mem_cons_of_mem _ hmem)⟩
    rcases List.mem_cons.mp hq with rfl | hq'
    · exact hwk ⟨q.2, pushTys0 q.1 venv, lenv'⟩ List.mem_cons_self hfit
    · exact hbs q hq' hfit

private theorem legalWorkLoop0_sound_aux (fuel : UInt32) (ctx : LegalCtx0)
    (work : List LegalItem0) (hloop : legalWorkLoop0 fuel ctx work = 0) :
    LegalWorkPred ctx work ∧ legalWorkCount0 work < fuel.toNat := by
  by_cases hf0 : fuel = 0
  · rw [legalWorkLoop0.eq_def] at hloop; simp [hf0] at hloop
  · have hlt : (fuel - 1).toNat < fuel.toNat := u32Sub1Lt0 fuel hf0
    have hpos : 0 < fuel.toNat := Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
    have hsub : (fuel - 1).toNat = fuel.toNat - 1 :=
      UInt32.toNat_sub_of_le fuel 1 (Nat.succ_le_of_lt hpos)
    rw [legalWorkLoop0.eq_def] at hloop
    simp only [hf0, ↓reduceDIte] at hloop
    cases work with
    | nil => exact ⟨(fun _ hm _ => nomatch hm), hpos⟩
    | cons cur rest =>
      dsimp only at hloop
      split at hloop
      · rename_i hec
        obtain ⟨hadv, hcnt⟩ := legalWorkLoop0_sound_aux (fuel - 1) ctx
          (legalAdvance0 cur rest) hloop
        have hcnt' : legalWorkCount0 (cur :: rest) < fuel.toNat := by
          rw [← legalWorkCount0_advance cur rest]; rw [hsub] at hcnt; omega
        refine ⟨?_, hcnt'⟩
        intro item hm hfit
        rcases List.mem_cons.mp hm with rfl | hrest
        · cases hnd : item.node with
          | let1 op args k =>
            have hop : checkOp0 item.venv op args = true := by
              dsimp only [legalCheckNode0, checkLegalOp0] at hec
              rw [hnd] at hec; dsimp only at hec
              split at hec <;> first | assumption | contradiction
            have hk := hadv ⟨k, legalNextVenv0 item.node item.venv, item.lenv⟩
              (by simp [legalAdvance0, isTerm0, legalAdvLin0, linK0, hnd])
              (by rw [hnd] at hfit; dsimp only [TFlat0.sigLensFitU32] at hfit; exact hfit)
            simp only [legalNextVenv0, hnd] at hk
            exact .let1 hop hk
          | let2Umulw64 a b k =>
            have hargs : checkArg0 item.venv .b64 a = true ∧
                checkArg0 item.venv .b64 b = true := by
              dsimp only [legalCheckNode0, checkLegalOp0] at hec
              rw [hnd] at hec; dsimp only at hec
              split at hec
              · exact (Bool.and_eq_true _ _).mp (by assumption)
              · contradiction
            have hk := hadv ⟨k, legalNextVenv0 item.node item.venv, item.lenv⟩
              (by simp [legalAdvance0, isTerm0, legalAdvLin0, linK0, hnd])
              (by rw [hnd] at hfit; dsimp only [TFlat0.sigLensFitU32] at hfit; exact hfit)
            simp only [legalNextVenv0, hnd] at hk
            exact .let2Umulw64 hargs.1 hargs.2 hk
          | load t addr k =>
            have ha : checkArg0 item.venv .b64 addr = true := by
              dsimp only [legalCheckNode0, checkLegalOp0] at hec
              rw [hnd] at hec; dsimp only at hec
              split at hec <;> first | assumption | contradiction
            have hk := hadv ⟨k, legalNextVenv0 item.node item.venv, item.lenv⟩
              (by simp [legalAdvance0, isTerm0, legalAdvLin0, linK0, hnd])
              (by rw [hnd] at hfit; dsimp only [TFlat0.sigLensFitU32] at hfit; exact hfit)
            simp only [legalNextVenv0, hnd] at hk
            exact .load ha hk
          | store t val addr k =>
            have hva : checkArg0 item.venv t val = true ∧
                checkArg0 item.venv .b64 addr = true := by
              dsimp only [legalCheckNode0, checkLegalOp0] at hec
              rw [hnd] at hec; dsimp only at hec
              split at hec
              · exact (Bool.and_eq_true _ _).mp (by assumption)
              · contradiction
            have hk := hadv ⟨k, legalNextVenv0 item.node item.venv, item.lenv⟩
              (by simp [legalAdvance0, isTerm0, legalAdvLin0, linK0, hnd])
              (by rw [hnd] at hfit; dsimp only [TFlat0.sigLensFitU32] at hfit; exact hfit)
            simp only [legalNextVenv0, hnd] at hk
            exact .store hva.1 hva.2 hk
          | call fnSym as bs args k =>
            have hc : (decide (tyLenU0 as 0 ≤ 6) && decide (tyLenU0 bs 0 ≤ 7) &&
                hasSig0 ctx.sigs fnSym as bs && checkArgs0 item.venv as args) = true := by
              dsimp only [legalCheckNode0, checkLegalCall0] at hec
              rw [hnd] at hec; dsimp only at hec
              split at hec <;> first | assumption | contradiction
            simp only [Bool.and_eq_true] at hc
            have hfs : (listLenFitsU32 as = true ∧ listLenFitsU32 bs = true) ∧
                k.sigLensFitU32 = true := by
              rw [hnd] at hfit
              dsimp only [TFlat0.sigLensFitU32] at hfit
              simpa only [Bool.and_eq_true] using hfit
            have has6 := tyLenU0_le_of_decide (by decide) (decide_eq_true_eq.mp hfs.1.1) hc.1.1.1
            have hbs7 := tyLenU0_le_of_decide (by decide) (decide_eq_true_eq.mp hfs.1.2) hc.1.1.2
            have hk := hadv ⟨k, legalNextVenv0 item.node item.venv, item.lenv⟩
              (by simp [legalAdvance0, isTerm0, legalAdvLin0, linK0, hnd]) hfs.2
            simp only [legalNextVenv0, hnd] at hk
            exact .call has6 hbs7 hc.1.2 hc.2 hk
          | tailCall fnSym as args =>
            have hc : (decide (tyLenU0 as 0 ≤ 6) && hasSig0 ctx.sigs fnSym as ctx.curRs &&
                checkArgs0 item.venv as args) = true := by
              dsimp only [legalCheckNode0, checkLegalCall0] at hec
              rw [hnd] at hec; dsimp only at hec
              split at hec <;> first | assumption | contradiction
            simp only [Bool.and_eq_true] at hc
            have hfs : as.length < 2 ^ 32 := by
              rw [hnd] at hfit
              dsimp only [TFlat0.sigLensFitU32, listLenFitsU32] at hfit
              exact decide_eq_true_eq.mp hfit
            exact .tailCall (tyLenU0_le_of_decide (by decide) hfs hc.1.1) hc.1.2 hc.2
          | exit fnSym as args =>
            have hc : (decide (tyLenU0 as 0 ≤ 6) && hasExit0 ctx.exits fnSym &&
                checkArgs0 item.venv as args) = true := by
              dsimp only [legalCheckNode0, checkLegalCall0] at hec
              rw [hnd] at hec; dsimp only at hec
              split at hec <;> first | assumption | contradiction
            simp only [Bool.and_eq_true] at hc
            have hfs : as.length < 2 ^ 32 := by
              rw [hnd] at hfit
              dsimp only [TFlat0.sigLensFitU32, listLenFitsU32] at hfit
              exact decide_eq_true_eq.mp hfit
            exact .exit (tyLenU0_le_of_decide (by decide) hfs hc.1.1) hc.1.2 hc.2
          | jnz c t e =>
            have hc : checkArg0 item.venv .bool c = true := by
              dsimp only [legalCheckNode0, checkLegalCtrl0] at hec
              rw [hnd] at hec; dsimp only at hec
              split at hec <;> first | assumption | contradiction
            have hfs : t.sigLensFitU32 = true ∧ e.sigLensFitU32 = true := by
              rw [hnd] at hfit
              dsimp only [TFlat0.sigLensFitU32] at hfit
              exact Bool.and_eq_true _ _ |>.mp hfit
            have ht := hadv ⟨t, item.venv, item.lenv⟩
              (by simp [legalAdvance0, isTerm0, legalAdvJnz0, hnd]) hfs.1
            have he := hadv ⟨e, item.venv, item.lenv⟩
              (by simp [legalAdvance0, isTerm0, legalAdvJnz0, hnd]) hfs.2
            exact .jnz hc ht he
          | jump j args =>
            dsimp only [legalCheckNode0, checkLegalCtrl0] at hec
            rw [hnd] at hec; dsimp only at hec
            cases hlg : listGetSig0 item.lenv j with
            | none => simp [hlg] at hec
            | some pts =>
              simp only [hlg] at hec
              split at hec <;> try contradiction
              exact .jump hlg (by assumption)
          | ret vs =>
            dsimp only [legalCheckNode0, checkLegalCtrl0] at hec
            rw [hnd] at hec; dsimp only at hec
            split at hec <;> try contradiction
            exact .ret (by assumption)
          | hlt => exact .hlt
          | group bodies k =>
            have hfs : blocksSigLensFitU32 bodies = true ∧ k.sigLensFitU32 = true := by
              rw [hnd] at hfit
              dsimp only [TFlat0.sigLensFitU32] at hfit
              exact Bool.and_eq_true _ _ |>.mp hfit
            have hk := hadv ⟨k, item.venv, legalAddSigs0 bodies item.lenv⟩
              (by simp [legalAdvance0, isTerm0, legalAdvGroup0, hnd]) hfs.2
            have hpush : LegalWorkPred ctx (legalPushGroup0 bodies item.venv
                (legalAddSigs0 bodies item.lenv) rest) := fun witem hw =>
              hadv witem (by
                simp only [legalAdvance0, isTerm0, legalAdvGroup0, hnd, Bool.false_eq_true,
                  ↓reduceIte, List.mem_cons]
                exact Or.inr hw)
            obtain ⟨hbs, _⟩ := legalPushGroup0_wf hpush
            refine .group (fun p hp => hbs p hp ?_) hk
            have hbf : blocksSigLensFitU32 bodies = true := hfs.1
            clear hbs hpush hadv hcnt hk hec hnd hfs
            induction bodies with
            | nil => nomatch hp
            | cons q qs ih =>
              dsimp only [blocksSigLensFitU32] at hbf
              simp only [Bool.and_eq_true] at hbf
              rcases List.mem_cons.mp hp with rfl | hq
              · exact hbf.1.2
              · exact ih hq hbf.2
        · have hadv_rest : LegalWorkPred ctx rest := by
            cases hnd : cur.node with
            | tailCall _ _ _ | jump _ _ | ret _ | exit _ _ _ | hlt =>
              simpa [legalAdvance0, isTerm0, hnd] using hadv
            | jnz _ t e =>
              intro x hx; exact hadv x (by simp [legalAdvance0, isTerm0, legalAdvJnz0, hnd, hx])
            | group bodies k =>
              have hpush : LegalWorkPred ctx (legalPushGroup0 bodies cur.venv
                  (legalAddSigs0 bodies cur.lenv) rest) := fun witem hw =>
                hadv witem (by
                  simp only [legalAdvance0, isTerm0, legalAdvGroup0, hnd, Bool.false_eq_true,
                    ↓reduceIte, List.mem_cons]
                  exact Or.inr hw)
              exact (legalPushGroup0_wf hpush).2
            | let1 _ _ k | let2Umulw64 _ _ k | load _ _ k | store _ _ _ k | call _ _ _ _ k =>
              intro x hx; exact hadv x (by simp [legalAdvance0, isTerm0, legalAdvLin0, hnd, hx])
          exact hadv_rest item hrest hfit
      · contradiction
termination_by fuel.toNat

theorem legalWorkLoop0_sound (ctx : LegalCtx0) (venv : List Ty0) (body : TFlat0)
    (hfit : body.sigLensFitU32 = true)
    (h : legalWorkLoop0 0x7fffffff ctx [LegalItem0.mk body venv []] = 0) :
    WfNode0 ctx venv [] body ∧ nodeCount0 body < 0x7fffffff := by
  obtain ⟨hw, hc⟩ := legalWorkLoop0_sound_aux 0x7fffffff ctx [LegalItem0.mk body venv []] h
  dsimp only [legalWorkCount0, Nat.add_zero] at hc
  exact ⟨hw _ List.mem_cons_self hfit, hc⟩

private theorem allValidExts0_sound :
    ∀ {exts : List ExtSig0},
      allValidExts0 exts = true →
      (∀ ex ∈ exts, listLenFitsU32 ex.as = true ∧ listLenFitsU32 ex.rs = true) →
      ∀ ex ∈ exts, ex.as.length ≤ 6 ∧ ex.rs.length ≤ 7
  | [], _, _, _, hex => nomatch hex
  | e :: rest, h, hfit, ex, hex => by
    dsimp only [allValidExts0] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      rcases List.mem_cons.mp hex with rfl | hex'
      · have he := hfit ex List.mem_cons_self
        exact ⟨tyLenU0_le_of_decide (by decide) (decide_eq_true_eq.mp he.1) hc.1,
               tyLenU0_le_of_decide (by decide) (decide_eq_true_eq.mp he.2) hc.2⟩
      · exact allValidExts0_sound h (fun q hq => hfit q (List.mem_cons_of_mem _ hq)) ex hex'
    · cases h

private theorem legalFnsLoop0_sound (exits : List Sym0) (sigs : List ExtSig0) :
    ∀ {fns : List TFlatFn0} {idx : UInt32},
      legalFnsLoop0 exits sigs fns idx = 0 →
      fns.all TFlatFn0.sigLensFitU32 = true →
      (fns.map TFlatFn0.name).Nodup ∧
      ∀ fn ∈ fns,
        fn.as.length ≤ 6 ∧ fn.rs.length ≤ 7 ∧
        WfNode0 (LegalCtx0.mk sigs exits fn.rs) (pushTys0 fn.as []) [] fn.body ∧
        nodeCount0 fn.body < 0x7fffffff
  | [], _, _, _ => ⟨List.nodup_nil, fun _ hf => nomatch hf⟩
  | fn :: rest, idx, h, hfit => by
    simp only [List.all_cons, Bool.and_eq_true] at hfit
    dsimp only [legalFnsLoop0] at h
    split at h
    · rename_i hec
      obtain ⟨hnd, hrest⟩ := legalFnsLoop0_sound exits sigs h hfit.2
      dsimp only [checkOneFn0] at hec
      split at hec
      · rename_i hdr
        dsimp only [checkFnHdr0] at hdr
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hdr
        have hfitFn := hfit.1
        simp only [TFlatFn0.sigLensFitU32, listLenFitsU32, Bool.and_eq_true, decide_eq_true_eq]
          at hfitFn
        have has := tyLenU0_le_of_decide (by decide) hfitFn.1.1 hdr.1.2
        have hrs := tyLenU0_le_of_decide (by decide) hfitFn.1.2 hdr.2
        have hnot : fn.name ∉ rest.map TFlatFn0.name := fun hm => by
          rw [← hasFnSym0_mem, hdr.1.1] at hm; cases hm
        obtain ⟨hwf, hcnt⟩ := legalWorkLoop0_sound (LegalCtx0.mk sigs exits fn.rs)
          (pushTys0 fn.as []) fn.body hfitFn.2 hec
        refine ⟨List.nodup_cons.mpr ⟨hnot, hnd⟩, fun g hg => ?_⟩
        rcases List.mem_cons.mp hg with rfl | hg'
        · exact ⟨has, hrs, hwf, hcnt⟩
        · exact hrest g hg'
      · contradiction
    · rename_i hnz
      have hor : (UInt32.toUInt64 (checkOneFn0 exits sigs rest fn) <<< 32 |||
          idx.toUInt64) = 0 := by assumption
      exfalso
      apply hnz
      have hb : ((checkOneFn0 exits sigs rest fn).toUInt64 <<< 32).toBitVec = 0#64 := by
        have ho := congrArg UInt64.toBitVec hor
        simp only [UInt64.toBitVec_or] at ho
        apply BitVec.eq_of_getLsbD_eq; intro k hk
        have hk0 := congrArg (fun x : BitVec 64 => x.getLsbD k) ho
        simp_all
      have ha : (checkOneFn0 exits sigs rest fn).toUInt64.toNat * 2 ^ 32 % 2 ^ 64 = 0 := by
        have h1 := congrArg BitVec.toNat hb
        simpa [UInt64.toNat_shiftLeft, Nat.shiftLeft_eq] using h1
      have hlt : (checkOneFn0 exits sigs rest fn).toNat * 2 ^ 32 < 2 ^ 64 := by
        have h32 : (checkOneFn0 exits sigs rest fn).toNat < 2 ^ 32 :=
          (checkOneFn0 exits sigs rest fn).toBitVec.isLt
        omega
      rw [UInt32.toNat_toUInt64, Nat.mod_eq_of_lt hlt] at ha
      apply UInt32.eq_of_toBitVec_eq
      apply BitVec.eq_of_toNat_eq
      exact (Nat.mul_eq_zero.mp ha).elim id (fun h0 => absurd h0 (by decide))

theorem legalMod0_sound (mod : TFlatModule0) (h : legalMod0 mod = 0)
    (hfit : mod.sigLensFitU32 = true) :
    let sigs := prepSigsFns0 mod.fns (prepSigsExts0 mod.externs [])
    (∀ ex ∈ mod.externs, ex.as.length ≤ 6 ∧ ex.rs.length ≤ 7) ∧
    (mod.fns.map TFlatFn0.name).Nodup ∧
    ∀ fn ∈ mod.fns,
      fn.as.length ≤ 6 ∧ fn.rs.length ≤ 7 ∧
      WfNode0 (LegalCtx0.mk sigs mod.exits fn.rs) (pushTys0 fn.as []) [] fn.body ∧
      nodeCount0 fn.body < 0x7fffffff := by
  have hfit' : mod.fns.all TFlatFn0.sigLensFitU32 = true ∧
      mod.externs.all (fun ex => listLenFitsU32 ex.as && listLenFitsU32 ex.rs) = true := by
    simpa [TFlatModule0.sigLensFitU32, Bool.and_eq_true] using hfit
  dsimp only [legalMod0] at h
  split at h
  · rename_i hext
    have hnd_fns := legalFnsLoop0_sound mod.exits
      (prepSigsFns0 mod.fns (prepSigsExts0 mod.externs [])) h hfit'.1
    refine ⟨?_, hnd_fns.1, hnd_fns.2⟩
    refine allValidExts0_sound hext fun ex hex => ?_
    have hm := List.all_eq_true.mp hfit'.2 ex hex
    exact Bool.and_eq_true .. |>.mp hm
  · exfalso
    have h2 : (UInt64.shiftLeft 2 32 : UInt64) = 0 := h
    have hv := congrArg UInt64.toNat h2
    revert hv; decide

end LeanQbe.T.Bootstrap0

