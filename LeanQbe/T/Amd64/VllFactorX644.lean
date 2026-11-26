module

public import LeanQbe.T.Amd64.VllFactorX643
public import LeanQbe.T.Amd64.VllAsmX64

/-!
# BedrockMach SysV x86-64 State Transport, Move/Shuffle Parity, & Lowering
  (`Amd64.VllFactorX644`)

Part 2a of the exact `asmX64List` lowering equality proof between `vllX64Isa` (`vllX64Target`) and
`x64Isa` (`x64Target`), factored cleanly so every file stays well below `2,500` LOC:
* `@[reducible] def vllX64IsaR` (`vllX64IsaR = vllX64Isa := rfl`) backed by concrete-typed
  `vllX64GprR`/`vllX64VecR`/`vllX64FrameR` so `Reg`/`VReg`/`Cond`/`Directive` match
  `{Reg64, RegMm, CondCode, Instr x64Arch}` at `@reducible` transparency and `simp` never unfolds
  projections back into semireducible `vllX64Isa`.
* `DecidableEq`/`BEq` congruence lemmas isolating `vllX64Isa.decEq*` from `x64Isa.decEq*`.
* `hintsNoRsp`/`regsNoRsp`/`savedNoRsp`/`locsNoRsp` invariants, symbolic state transport
  (`symStToX64`, `mapOptSt`, `mapRes`), ABI slot assignment invariants, and lockstep lemmas for
  `execMove`, `execMoves`, `execClearFlags`, `stepPre`, `pmoveAux`, `shuffle`, `canonAbiCode`,
  `saveCs`, and `restoreCs`.

Zero `Arm64` / `Kraken.AArch64` imports, zero `@[expose]` on proof theorems/lemmas.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

open LeanQbe.T
open LeanQbe.T.Vll
open Std Std.ExtHashMap

/-! ## 0. Reducible `vllX64IsaR` View & `DecidableEq` Congruence Toolkit -/

/-- Semireducible concrete-typed view of `vllX64Isa.gpr` (`= vllX64Isa.gpr`). -/
@[expose] def vllX64GprR : GprIsa Reg64 RegMm CondCode (Instr x64Arch) := vllX64Isa.gpr

/-- Semireducible concrete-typed view of `vllX64Isa.vec` (`= vllX64Isa.vec`). -/
@[expose] def vllX64VecR : VecIsa Reg64 RegMm CondCode (Instr x64Arch) := vllX64Isa.vec

/-- Semireducible concrete-typed view of `vllX64Isa.frame` (`= vllX64Isa.frame`). -/
@[expose] def vllX64FrameR : FrameIsa Reg64 (Instr x64Arch) := vllX64Isa.frame

/-- Reducible view of `vllX64Isa` with concrete carrier types `{Reg64, RegMm, CondCode,
Instr x64Arch}` and semireducible sub-records so `@reducible` unfolding never falls back to
semireducible `vllX64Isa`. -/
@[expose, reducible] def vllX64IsaR : Isa where
  Reg := Reg64
  VReg := RegMm
  Cond := CondCode
  Directive := Instr x64Arch
  decEqReg := vllX64Isa.decEqReg
  decEqVReg := vllX64Isa.decEqVReg
  decEqCond := vllX64Isa.decEqCond
  gpr := vllX64GprR
  vec := vllX64VecR
  frame := vllX64FrameR
  supportsAddrDisp := x64SupportsAddrDisp
  supportsAddrIdx := x64SupportsAddrIdx
  supportsTestFuse := true
  supportsCmpMem := x64SupportsCmpMem
  supportsTestMem := x64SupportsCmpMem
  supportsAddrZextIdx := fun _ _ _ => false

theorem vllX64IsaR_eq : vllX64IsaR = vllX64Isa := rfl

private theorem reg64_eq_of_beq {r₁ r₂ : Reg64} (h : (r₁ == r₂) = true) : r₁ = r₂ := by
  cases r₁ <;> cases r₂ <;> first | rfl | cases h

private theorem reg64_beq_false_of_ne {r₁ r₂ : Reg64} (h : r₁ ≠ r₂) : (r₁ == r₂) = false := by
  cases hab : (r₁ == r₂) with
  | false => rfl
  | true => exact absurd (reg64_eq_of_beq hab) h

private theorem reg64_bne_of_ne {r₁ r₂ : Reg64} (h : r₁ ≠ r₂) : (r₁ != r₂) = true := by
  change !(r₁ == r₂) = true
  rw [reg64_beq_false_of_ne h]; rfl

theorem decEq_beq_congr {α : Type} (i₁ i₂ : DecidableEq α) (a b : α) :
    @BEq.beq α (@instBEqOfDecidableEq α i₁) a b =
    @BEq.beq α (@instBEqOfDecidableEq α i₂) a b := by
  by_cases hab : a = b
  · exact (@decide_eq_true (a = b) (i₁ a b) hab).trans
      (@decide_eq_true (a = b) (i₂ a b) hab).symm
  · exact (@decide_eq_false (a = b) (i₁ a b) hab).trans
      (@decide_eq_false (a = b) (i₂ a b) hab).symm

theorem list_elem_decEq_congr {α : Type} (i₁ i₂ : DecidableEq α) (x : α) (xs : List α) :
    @List.elem α (@instBEqOfDecidableEq α i₁) x xs =
    @List.elem α (@instBEqOfDecidableEq α i₂) x xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    dsimp only [List.elem]
    rw [decEq_beq_congr i₁ i₂ x y, ih]

theorem list_contains_decEq_congr {α : Type} (i₁ i₂ : DecidableEq α) (xs : List α) (x : α) :
    @List.contains α (@instBEqOfDecidableEq α i₁) xs x =
    @List.contains α (@instBEqOfDecidableEq α i₂) xs x :=
  list_elem_decEq_congr i₁ i₂ x xs

private theorem list_all_congr {α : Type} {p q : α → Bool} (hpq : ∀ a, p a = q a)
    (xs : List α) : xs.all p = xs.all q := by
  induction xs with
  | nil => rfl
  | cons y ys ih => simp only [List.all_cons, hpq y, ih]

private theorem list_any_congr {α : Type} {p q : α → Bool} (hpq : ∀ a, p a = q a)
    (xs : List α) : xs.any p = xs.any q := by
  induction xs with
  | nil => rfl
  | cons y ys ih => simp only [List.any_cons, hpq y, ih]

private theorem list_filterMap_congr {α β : Type} {f g : α → Option β} (h : ∀ a, f a = g a)
    (xs : List α) : xs.filterMap f = xs.filterMap g := by
  induction xs with
  | nil => rfl
  | cons y ys ih => dsimp only [List.filterMap]; rw [h y, ih]

private theorem list_findSome_congr {α β : Type} {f g : α → Option β} (h : ∀ a, f a = g a)
    (xs : List α) : xs.findSome? f = xs.findSome? g := by
  induction xs with
  | nil => rfl
  | cons y ys ih => dsimp only [List.findSome?]; rw [h y, ih]

private theorem list_foldl_congr {α β : Type} {f g : α → β → α} (h : ∀ a b, f a b = g a b)
    (xs : List β) (init : α) : xs.foldl f init = xs.foldl g init := by
  induction xs generalizing init with
  | nil => rfl
  | cons y ys ih => simp only [List.foldl_cons, h init y, ih]

theorem vllR_assignSig_eq (ts : List Ty) (gs : List Reg64) (vs : List RegMm) :
    vllX64IsaR.assignSig ts gs vs = x64Isa.assignSig ts gs vs :=
  vllX64_assignSig_eq ts gs vs

theorem vllR_assignArgs_eq (as : List Ty) :
    vllX64IsaR.assignArgs as = x64Isa.assignArgs as :=
  vllX64_assignArgs_eq as

theorem vllR_assignRets_eq (rs : List Ty) :
    vllX64IsaR.assignRets rs = x64Isa.assignRets rs :=
  vllX64_assignRets_eq rs

theorem vllR_clearFlags_eq :
    asmX64List vllX64GprR.clearFlags = x64Isa.gpr.clearFlags :=
  vllX64_clearFlags_eq

theorem vllR_mov_eq (d s : Reg64) :
    asmX64List (vllX64GprR.mov d s) = x64Isa.gpr.mov d s :=
  vllX64_mov_eq d s

theorem vllR_movi_eq (d : Reg64) (cb : BitVec 64) :
    asmX64List (vllX64GprR.movi d cb) = x64Isa.gpr.movi d cb :=
  vllX64_movi_eq d cb

theorem vllR_setcc_eq (d : Reg64) (cc : CondCode) :
    asmX64List (vllX64GprR.setcc d cc) = x64Isa.gpr.setcc d cc :=
  vllX64_setcc_eq d cc

theorem vllR_jmp_eq (l : Sym) :
    asmX64List (vllX64GprR.jmp l) = x64Isa.gpr.jmp l :=
  vllX64_jmp_eq l

theorem vllR_jcc_eq (cc : CondCode) (l : Sym) :
    asmX64List (vllX64GprR.jcc cc l) = x64Isa.gpr.jcc cc l :=
  vllX64_jcc_eq cc l

theorem vllR_jnzGpr_eq (r : Reg64) (l : Sym) :
    (asmX64List (vllX64GprR.jnzGpr r l).1, (vllX64GprR.jnzGpr r l).2) =
      x64Isa.gpr.jnzGpr r l :=
  vllX64_jnzGpr_eq r l

theorem vllR_jnzGprInv_eq (r : Reg64) (inv : Bool) (l : Sym) :
    (asmX64List (vllX64JnzGprInv r inv l).1, (vllX64JnzGprInv r inv l).2) =
      x64JnzGpr r inv l :=
  vllX64_jnzGprInv_eq r inv l

theorem vllR_label_eq (l : Sym) :
    asmX64List [vllX64FrameR.label l] = [x64Isa.frame.label l] :=
  vllX64_label_eq l

theorem vllR_prologue_eq (ns : Nat) :
    asmX64List (vllX64FrameR.prologue ns).1 = (x64Isa.frame.prologue ns).1 :=
  vllX64_prologue_eq ns

theorem vllR_epilogue_eq (ns : Nat) :
    asmX64List (vllX64FrameR.epilogue ns).1 = (x64Isa.frame.epilogue ns).1 :=
  vllX64_epilogue_eq ns

theorem vllR_slotSt_eq (i : Nat) (r : Reg64) :
    asmX64List (vllX64FrameR.slotSt i r) = x64Isa.frame.slotSt i r :=
  vllX64_slotSt_eq i r

theorem vllR_slotLd_eq (r : Reg64) (i : Nat) :
    asmX64List (vllX64FrameR.slotLd r i) = x64Isa.frame.slotLd r i :=
  vllX64_slotLd_eq r i

theorem vllR_canonAbi_eq (t : Ty) (r : Reg64) :
    asmX64List (vllX64FrameR.canonAbi t r).1 = (x64Isa.frame.canonAbi t r).1 :=
  vllX64_canonAbi_eq t r

theorem vllR_call_eq (f : Sym) :
    asmX64List (vllX64FrameR.call f) = x64Isa.frame.call f :=
  vllX64_call_eq f

theorem vllR_exitJmp_eq (f : Sym) :
    asmX64List (vllX64FrameR.exitJmp f) = x64Isa.frame.exitJmp f :=
  vllX64_exitJmp_eq f

theorem vllR_ret_eq :
    asmX64List vllX64FrameR.ret = x64Isa.frame.ret :=
  vllX64_ret_eq

theorem vllR_vmov_eq (w : SlotWidth) (d s : RegMm) :
    asmX64List (vllX64VecR.vmov w d s) = x64Isa.vec.vmov w d s :=
  vllX64_vmov_eq w d s

theorem vllR_vmovi_eq (w : SlotWidth) (d : RegMm) (cb : BitVec 512) :
    (vllX64VecR.vmovi w d cb).map asmX64List = x64Isa.vec.vmovi w d cb :=
  vllX64_vmovi_eq w d cb

theorem vllR_vslotSt_eq (w : SlotWidth) (i : Nat) (s : RegMm) :
    asmX64List (vllX64VecR.vslotSt w i s) = x64Isa.vec.vslotSt w i s :=
  vllX64_vslotSt_eq w i s

theorem vllR_vslotLd_eq (w : SlotWidth) (d : RegMm) (i : Nat) :
    asmX64List (vllX64VecR.vslotLd w d i) = x64Isa.vec.vslotLd w d i :=
  vllX64_vslotLd_eq w d i

theorem vllR_vop_eq {sig rs : List Ty} (code : OpCode sig rs)
    (pas : Tup (PArg Reg64 RegMm CondCode) sig) (dsts : Tup (PDst Reg64 RegMm CondCode) rs)
    (vh : VariantHint) :
    (vllX64VecR.vop code pas dsts vh).map (fun (d, cl) => (asmX64List d, cl)) =
      x64Isa.vec.vop code pas dsts vh :=
  vllX64_vop_eq code pas dsts vh

theorem vllR_vload_eq (t : Ty) (d : RegMm) (a : AddrArg Reg64) :
    (vllX64VecR.vload t d a).map (fun (d, cl) => (asmX64List d, cl)) =
      x64Isa.vec.vload t d a :=
  vllX64_vload_eq t d a

theorem vllR_vstore_eq (t : Ty) (s : RegMm) (a : AddrArg Reg64) :
    (vllX64VecR.vstore t s a).map (fun (d, cl) => (asmX64List d, cl)) =
      x64Isa.vec.vstore t s a :=
  vllX64_vstore_eq t s a

theorem vllR_testOp_eq (w : Nat) (neg : Bool) (pa pb : PArg Reg64 RegMm CondCode (.bits w))
    (pd : PDst Reg64 RegMm CondCode .bool) :
    (vllX64GprR.testOp w neg pa pb pd).map (fun (c0, cl) => (asmX64List c0, cl)) =
      x64Isa.gpr.testOp w neg pa pb pd :=
  vllX64_testOp_eq w neg pa pb pd

theorem vllR_cmpMem_eq (co : CmpOp) (w : Nat) (a : AddrArg Reg64)
    (pb : PArg Reg64 RegMm CondCode (.bits w)) (pd : PDst Reg64 RegMm CondCode .bool) :
    (vllX64GprR.cmpMem co w a pb pd).map (fun (c0, cl) => (asmX64List c0, cl)) =
      x64Isa.gpr.cmpMem co w a pb pd :=
  vllX64_cmpMem_eq co w a pb pd

theorem vllR_testMem_eq (w : Nat) (neg : Bool) (a : AddrArg Reg64)
    (pb : PArg Reg64 RegMm CondCode (.bits w)) (pd : PDst Reg64 RegMm CondCode .bool) :
    (vllX64GprR.testMem w neg a pb pd).map (fun (c0, cl) => (asmX64List c0, cl)) =
      x64Isa.gpr.testMem w neg a pb pd :=
  vllX64_testMem_eq w neg a pb pd

theorem vllR_aluMem_eq (w : Nat) (code : OpCode [.bits w, .bits w] [.bits w]) (memRhs : Bool)
    (a : AddrArg Reg64) (pb : PArg Reg64 RegMm CondCode (.bits w)) (rd : Reg64) :
    (vllX64GprR.aluMem w code memRhs a pb rd).map (fun (c0, cl) => (asmX64List c0, cl)) =
      x64Isa.gpr.aluMem w code memRhs a pb rd :=
  vllX64_aluMem_eq w code memRhs a pb rd

theorem vllR_jnzMem_eq (a : AddrArg Reg64) (inv : Bool) (l : Sym) :
    (vllX64GprR.jnzMem a inv l).map (fun (c0, cl) => (asmX64List c0, cl)) =
      x64Isa.gpr.jnzMem a inv l :=
  vllX64_jnzMem_eq a inv l

theorem vllR_rmwMem_eq (w : Nat) (code : OpCode [.bits w, .bits w] [.bits w])
    (a : AddrArg Reg64) (pb : PArg Reg64 RegMm CondCode (.bits w)) :
    (vllX64GprR.rmwMem w code a pb).map (fun (c0, cl) => (asmX64List c0, cl)) =
      x64Isa.gpr.rmwMem w code a pb :=
  vllX64_rmwMem_eq w code a pb

theorem vllR_leaArith_eq (w : Nat) (base? : Option Reg64) (idx : Reg64) (sc : AddrScale)
    (disp : Int64) (rd : Reg64) :
    (vllX64GprR.leaArith w base? idx sc disp rd).map (fun (c0, cl) => (asmX64List c0, cl)) =
      x64Isa.gpr.leaArith w base? idx sc disp rd :=
  vllX64_leaArith_eq w base? idx sc disp rd

theorem vllR_loadSext_eq (m n : Nat) (rd : Reg64) (a : AddrArg Reg64) :
    (vllX64GprR.loadSext m n rd a).map (fun (c0, cl) => (asmX64List c0, cl)) =
      x64Isa.gpr.loadSext m n rd a :=
  vllX64_loadSext_eq m n rd a

theorem vllR_store_eq (t : Ty) (pa : PArg Reg64 RegMm CondCode t) (a : AddrArg Reg64)
    (ha : x64AddrValid a = true) :
    (vllX64GprR.store t pa a).map (fun (c0, cl) => (asmX64List c0, cl)) =
      x64Isa.gpr.store t pa a :=
  vllX64_store_eq t pa a ha

theorem vllR_store_eq_of_x64 {t : Ty} {pa : PArg Reg64 RegMm CondCode t} {a : AddrArg Reg64}
    {ds : List _root_.Directive} {cl : FlagMask} (hx : x64Isa.gpr.store t pa a = some (ds, cl)) :
    ∃ cs, vllX64GprR.store t pa a = some (cs, cl) ∧ asmX64List cs = ds :=
  vllX64_store_eq_of_x64 hx

theorem vllR_load_eq (t : Ty) (rd : Reg64) (a : AddrArg Reg64) (ha : x64AddrValid a = true) :
    (vllX64GprR.load t rd a).map (fun (c0, cl) => (asmX64List c0, cl)) =
      x64Isa.gpr.load t rd a :=
  vllX64_load_eq t rd a ha

theorem vllR_load_eq_of_x64 {t : Ty} {rd : Reg64} {a : AddrArg Reg64}
    {ds : List _root_.Directive} {cl : FlagMask} (hx : x64Isa.gpr.load t rd a = some (ds, cl)) :
    ∃ cs, vllX64GprR.load t rd a = some (cs, cl) ∧ asmX64List cs = ds :=
  vllX64_load_eq_of_x64 hx

theorem vllR_op_eq {sig rs : List Ty} (code : OpCode sig rs)
    (pas : Tup (PArg Reg64 RegMm CondCode) sig) (dsts : Tup (PDst Reg64 RegMm CondCode) rs)
    (vh : VariantHint) (hok : opNoSameExt code = true) :
    (vllX64GprR.op code pas dsts vh).map (fun (c0, cl) => (asmX64List c0, cl)) =
      x64Isa.gpr.op code pas dsts vh :=
  vllX64_op_eq code pas dsts vh hok

theorem vllR_op_eq_of_x64 {sig rs : List Ty} (code : OpCode sig rs)
    (pas : Tup (PArg Reg64 RegMm CondCode) sig) (dsts : Tup (PDst Reg64 RegMm CondCode) rs)
    (vh : VariantHint) {ds : List _root_.Directive} {cl : FlagMask}
    (hx : x64Isa.gpr.op code pas dsts vh = some (ds, cl)) :
    ∃ cs, vllX64GprR.op code pas dsts vh = some (cs, cl) ∧ asmX64List cs = ds :=
  vllX64_op_eq_of_x64 code pas dsts vh hx

theorem vllR_scratch_eq : vllX64FrameR.scratch = x64Isa.frame.scratch := rfl
theorem vllR_vecScratch_eq : vllX64VecR.vecScratch = x64Isa.vec.vecScratch := rfl
theorem vllR_saveRegs_eq : vllX64FrameR.saveRegs? = none := rfl
theorem vllR_restoreRegs_eq : vllX64FrameR.restoreRegs? = none := rfl
theorem vllR_zeroFlags_eq : vllX64GprR.zeroFlags = x64Isa.gpr.zeroFlags := rfl
theorem vllR_condReads_eq : vllX64GprR.condReads = x64Isa.gpr.condReads := rfl
theorem vllR_condOfCmp_eq : vllX64GprR.condOfCmp? = x64Isa.gpr.condOfCmp? := rfl

/-! ## 2a. `hintsNoRsp` Invariants, State Transport, and Move/Shuffle/ABI Parity -/

/-- `true` when `loc` is not `.gpr .rsp`. -/
@[expose] def locNoRsp : Loc Reg64 RegMm CondCode → Bool
  | .gpr r => r != .rsp
  | _ => true

/-- `true` when a block entry mentions no `.gpr .rsp`. -/
@[expose] def entryNoRsp (e : Entry Reg64 RegMm CondCode) : Bool :=
  e.live.all (fun p => locNoRsp p.2) && e.ploc.all locNoRsp

/-- Universal `Trie` check over all stored nodes. -/
@[expose] def trieAll {α : Type} (p : α → Bool) : Trie α → Bool
  | .empty => true
  | .node v e o => (match v with | some x => p x | none => true) && trieAll p e && trieAll p o

/-- Precondition ensuring `Rega.lowerFn` never places `.rsp` in live GPR state, matching `x64Load`'s
`x64AddrValid` guard. -/
@[expose] def hintsNoRsp (h : x64Isa.Hints) : Bool :=
  trieAll entryNoRsp h.entry

/-- Symbolic register file invariant: `.rsp` never tracks an IR argument or variable. -/
@[expose] def regsNoRsp (R : List (SymArg × Rega.RegLoc Reg64 RegMm CondCode)) : Bool :=
  R.all fun (_, rl) => match rl with | .gpr r | .gprZ r => r != .rsp | _ => true

/-- Saved-register validity matching `Rega.lowerFn`'s prologue check (`calleeSaved`). -/
@[expose] def savedNoRsp (saved : List Reg64) : Bool :=
  saved.all (x64Frame.calleeSaved.contains ·)

/-- ABI register tuple invariant: `.rsp` never appears in ABI GPR slots. -/
@[expose] def locsNoRsp : {ts : List Ty} → Tup (AbiReg Reg64 RegMm) ts → Bool
  | [], () => true
  | _ :: _, (.gpr r, ls) => r != .rsp && locsNoRsp ls
  | _ :: _, (.vec _, ls) => locsNoRsp ls

/-- Map symbolic allocation state cleanly between `vllX64IsaR` and `x64Isa`. -/
@[expose, reducible] def symStToX64 (st : Rega.SymState vllX64IsaR) : Rega.SymState x64Isa where
  regs := st.regs
  slots := st.slots
  defs := st.defs
  vecWidths := st.vecWidths
  memDefs := st.memDefs
  zeroExt32 := st.zeroExt32
  flags := st.flags

@[expose] def mapOptSt :
    Option (List vllX64IsaR.Directive × Rega.SymState vllX64IsaR) →
    Option (List _root_.Directive × Rega.SymState x64Isa) :=
  Option.map fun (c0, st) => (asmX64List c0, symStToX64 st)

@[expose] def mapRes : Rega.Res vllX64IsaR → Rega.Res x64Isa
  | .ok (c0, nv, nl, ip) => .ok (asmX64List c0, nv, nl, ip)
  | .error e => .error e

theorem mapRes_prepend (pre : List vllX64IsaR.Directive) (r : Rega.Res vllX64IsaR) :
    mapRes (Rega.prepend pre r) = Rega.prepend (asmX64List pre) (mapRes r) := by
  cases r with
  | error _ => rfl
  | ok _ => simp [Rega.prepend, mapRes, asmX64List_append]

theorem trieAll_find? {α : Type} {p : α → Bool} :
    ∀ {t : Trie α} {k : Nat} {v : α}, trieAll p t = true → t.find? k = some v → p v = true
  | .empty, _, _, _, h => by cases h
  | .node val e o, 0, v, ht, hf => by
    simp only [Trie.find?] at hf; subst hf
    simp only [trieAll, Bool.and_eq_true] at ht; exact ht.1.1
  | .node _ e o, n + 1, v, ht, hf => by
    simp only [trieAll, Bool.and_eq_true] at ht
    simp only [Trie.find?] at hf
    split at hf
    · exact trieAll_find? ht.1.2 hf
    · exact trieAll_find? ht.2 hf

theorem savedNoRsp_mem {saved : List Reg64} (hs : savedNoRsp saved = true) {r : Reg64}
    (hr : r ∈ saved) : r ≠ .rsp := by
  have hm : x64Frame.calleeSaved.contains r = true := List.all_eq_true.mp hs r hr
  intro e; subst e; cases hm

theorem vllR_isAllocGpr_eq (saved : List Reg64) (r : Reg64) :
    Rega.isAllocGpr vllX64IsaR saved r = Rega.isAllocGpr x64Isa saved r := by
  dsimp only [Rega.isAllocGpr]
  simp only [list_contains_decEq_congr vllX64IsaR.decEqReg x64Isa.decEqReg]
  rfl

theorem vllR_isMoveGpr_eq (saved : List Reg64) (r : Reg64) :
    Rega.isMoveGpr vllX64IsaR saved r = Rega.isMoveGpr x64Isa saved r := by
  dsimp only [Rega.isMoveGpr]
  rw [vllR_isAllocGpr_eq, list_contains_decEq_congr vllX64IsaR.decEqReg x64Isa.decEqReg]
  rfl

theorem vllR_isAllocVec_eq (v : RegMm) :
    Rega.isAllocVec vllX64IsaR v = Rega.isAllocVec x64Isa v := by
  dsimp only [Rega.isAllocVec]
  simp only [list_contains_decEq_congr vllX64IsaR.decEqVReg x64Isa.decEqVReg]
  rfl

theorem vllR_isMoveVec_eq (v : RegMm) :
    Rega.isMoveVec vllX64IsaR v = Rega.isMoveVec x64Isa v := by
  dsimp only [Rega.isMoveVec]
  rw [vllR_isAllocVec_eq, list_contains_decEq_congr vllX64IsaR.decEqVReg x64Isa.decEqVReg]
  rfl

private theorem isAllocGpr_x64_ne_rsp {saved : List Reg64} (hs : savedNoRsp saved = true)
    {r : Reg64} (h : Rega.isAllocGpr x64Isa saved r = true) : r ≠ .rsp := by
  intro e; subst e
  simp only [Rega.isAllocGpr, Bool.or_eq_true, x64Isa, x64Frame] at h
  rcases h with ((h1 | h2) | h3) | h4
  · cases h1
  · induction saved with
    | nil => cases h2
    | cons y ys ih =>
      simp only [savedNoRsp, List.all_cons, Bool.and_eq_true] at hs
      dsimp only [List.contains, List.elem] at h2
      cases hy : @BEq.beq Reg64 (@instBEqOfDecidableEq Reg64 x64Isa.decEqReg) .rsp y
      · rw [hy] at h2; exact ih hs.2 h2
      · have heq : Reg64.rsp = y := by
          have : @decide (Reg64.rsp = y) (x64Isa.decEqReg .rsp y) = true := hy
          exact of_decide_eq_true this
        subst heq; cases hs.1
  · cases h3
  · cases h4

theorem isAllocGpr_ne_rsp {saved : List Reg64} (hs : savedNoRsp saved = true) {r : Reg64}
    (h : Rega.isAllocGpr vllX64IsaR saved r = true) : r ≠ .rsp := by
  rw [vllR_isAllocGpr_eq] at h
  exact isAllocGpr_x64_ne_rsp hs h

theorem isMoveGpr_ne_rsp {saved : List Reg64} (hs : savedNoRsp saved = true) {r : Reg64}
    (h : Rega.isMoveGpr vllX64IsaR saved r = true) : r ≠ .rsp := by
  rw [vllR_isMoveGpr_eq] at h
  simp only [Rega.isMoveGpr, Bool.or_eq_true] at h
  rcases h with h1 | h2
  · exact isAllocGpr_x64_ne_rsp hs h1
  · intro e; subst e; cases h2

theorem regsNoRsp_cons_gpr {sa : SymArg} {r : Reg64} {R}
    (hr : r ≠ .rsp) (hR : regsNoRsp R = true) : regsNoRsp ((sa, .gpr r) :: R) = true := by
  simp only [regsNoRsp, List.all_cons, reg64_bne_of_ne hr, Bool.true_and]
  exact hR

theorem regsNoRsp_cons_gprZ {sa : SymArg} {r : Reg64} {R}
    (hr : r ≠ .rsp) (hR : regsNoRsp R = true) : regsNoRsp ((sa, .gprZ r) :: R) = true := by
  simp only [regsNoRsp, List.all_cons, reg64_bne_of_ne hr, Bool.true_and]
  exact hR

theorem regsNoRsp_cons_vec {sa : SymArg} {v : RegMm} {R}
    (hR : regsNoRsp R = true) : regsNoRsp ((sa, .vec v) :: R) = true := by
  simp only [regsNoRsp, List.all_cons, Bool.true_and]; exact hR

theorem regsNoRsp_cons_flag {sa : SymArg} {cc : CondCode} {R}
    (hR : regsNoRsp R = true) : regsNoRsp ((sa, .flag cc) :: R) = true := by
  simp only [regsNoRsp, List.all_cons, Bool.true_and]; exact hR

theorem regsNoRsp_append {R₁ R₂} (h1 : regsNoRsp R₁ = true) (h2 : regsNoRsp R₂ = true) :
    regsNoRsp (R₁ ++ R₂) = true := by
  simp only [regsNoRsp, List.all_append, Bool.and_eq_true] at *; exact ⟨h1, h2⟩

theorem regsNoRsp_map_gprTagged {f : SymArg × Bool → SymArg × Rega.RegLoc Reg64 RegMm CondCode}
    (hf : ∀ p, match (f p).2 with | .gpr r | .gprZ r => r ≠ .rsp | _ => True)
    (l : List (SymArg × Bool)) : regsNoRsp (l.map f) = true := by
  simp only [regsNoRsp, List.all_eq_true]
  intro x hx
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
  have hp := hf p
  cases h2 : (f p).2 <;> simp only [h2] at hp ⊢
  · exact reg64_bne_of_ne hp
  · exact reg64_bne_of_ne hp

theorem regsNoRsp_map {α : Type} {f : α → SymArg × Rega.RegLoc Reg64 RegMm CondCode}
    (hf : ∀ x, match (f x).2 with | .gpr r | .gprZ r => r ≠ .rsp | _ => True)
    (l : List α) : regsNoRsp (l.map f) = true := by
  simp only [regsNoRsp, List.all_eq_true]
  intro y hy
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
  have hx := hf x
  cases h2 : (f x).2 <;> simp only [h2] at hx ⊢
  · exact reg64_bne_of_ne hx
  · exact reg64_bne_of_ne hx

theorem regsNoRsp_filter {p : SymArg × Rega.RegLoc Reg64 RegMm CondCode → Bool} {R}
    (hR : regsNoRsp R = true) : regsNoRsp (R.filter p) = true := by
  simp only [regsNoRsp, List.all_eq_true] at hR ⊢
  intro x hx
  exact hR x (List.mem_filter.mp hx).1

theorem regsNoRsp_killRegs {g : List Reg64} {v : List RegMm} (f : FlagMask)
    {R : List (SymArg × Rega.RegLoc Reg64 RegMm CondCode)}
    (h : regsNoRsp R = true) : regsNoRsp (Rega.killRegs vllX64IsaR g v f R) = true :=
  regsNoRsp_filter h

theorem keepRegLoc_eq (g : List Reg64) (v : List RegMm) (f : FlagMask)
    (rl : Rega.RegLoc Reg64 RegMm CondCode) :
    Rega.keepRegLoc vllX64IsaR g v f rl = Rega.keepRegLoc x64Isa g v f rl := by
  cases rl with
  | gpr r | gprZ r =>
    dsimp only [Rega.keepRegLoc]
    rw [list_contains_decEq_congr vllX64IsaR.decEqReg x64Isa.decEqReg]
  | vec vr =>
    dsimp only [Rega.keepRegLoc]
    rw [list_contains_decEq_congr vllX64IsaR.decEqVReg x64Isa.decEqVReg]
  | flag _ => rfl

theorem killRegs_eq (g : List Reg64) (v : List RegMm) (f : FlagMask)
    (R : List (SymArg × Rega.RegLoc Reg64 RegMm CondCode)) :
    Rega.killRegs vllX64IsaR g v f R = Rega.killRegs x64Isa g v f R := by
  dsimp only [Rega.killRegs]
  induction R with
  | nil => rfl
  | cons p ps ih =>
    dsimp only [List.filter]
    rw [keepRegLoc_eq, ih]

theorem killZeroExt_eq (g z : List Reg64) :
    @Rega.killZeroExt vllX64IsaR.Reg vllX64IsaR.decEqReg g z =
    @Rega.killZeroExt x64Isa.Reg x64Isa.decEqReg g z := by
  dsimp only [Rega.killZeroExt]
  induction z with
  | nil => rfl
  | cons r rs ih =>
    dsimp only [List.filter]
    rw [list_contains_decEq_congr vllX64IsaR.decEqReg x64Isa.decEqReg g r, ih]

theorem gprEntries_eq (r : Reg64) (R : List (SymArg × Rega.RegLoc Reg64 RegMm CondCode)) :
    Rega.gprEntries (I := vllX64IsaR) r R = Rega.gprEntries (I := x64Isa) r R := by
  refine list_filterMap_congr (fun ⟨sa, rl⟩ => ?_) R
  cases rl with
  | vec _ | flag _ => rfl
  | gpr r' | gprZ r' =>
    dsimp only
    rw [decEq_beq_congr vllX64IsaR.decEqReg x64Isa.decEqReg r' r]

theorem gprTaggedEntries_eq (r : Reg64)
    (R : List (SymArg × Rega.RegLoc Reg64 RegMm CondCode)) :
    Rega.gprTaggedEntries (I := vllX64IsaR) r R = Rega.gprTaggedEntries (I := x64Isa) r R := by
  refine list_filterMap_congr (fun ⟨sa, rl⟩ => ?_) R
  cases rl with
  | vec _ | flag _ => rfl
  | gpr r' | gprZ r' =>
    dsimp only
    rw [decEq_beq_congr vllX64IsaR.decEqReg x64Isa.decEqReg r' r]

theorem vecEntries_eq (vw : Trie SlotWidth) (w : SlotWidth) (v : RegMm)
    (R : List (SymArg × Rega.RegLoc Reg64 RegMm CondCode)) :
    Rega.vecEntries (I := vllX64IsaR) vw w v R = Rega.vecEntries (I := x64Isa) vw w v R := by
  refine list_filterMap_congr (fun ⟨sa, rl⟩ => ?_) R
  cases rl with
  | gpr _ | gprZ _ | flag _ => rfl
  | vec v' =>
    dsimp only
    rw [decEq_beq_congr vllX64IsaR.decEqVReg x64Isa.decEqVReg v' v]

theorem flagEntries_eq (cc : CondCode) (R : List (SymArg × Rega.RegLoc Reg64 RegMm CondCode)) :
    Rega.flagEntries (I := vllX64IsaR) cc R = Rega.flagEntries (I := x64Isa) cc R := by
  refine list_filterMap_congr (fun ⟨sa, rl⟩ => ?_) R
  cases rl with
  | gpr _ | gprZ _ | vec _ => rfl
  | flag c' =>
    dsimp only
    rw [decEq_beq_congr vllX64IsaR.decEqCond x64Isa.decEqCond c' cc]

theorem findGprFor_eq (b : Bool) (R : List (SymArg × Rega.RegLoc Reg64 RegMm CondCode))
    (sa : SymArg) :
    Rega.findGprFor vllX64IsaR b R sa = Rega.findGprFor x64Isa b R sa := by
  refine list_findSome_congr (fun ⟨sa', rl⟩ => ?_) R
  cases rl with
  | vec _ | flag _ => rfl
  | gpr r | gprZ r =>
    dsimp only
    rw [list_contains_decEq_congr vllX64IsaR.decEqReg x64Isa.decEqReg, vllR_scratch_eq]

theorem findVecFor_eq (b : Bool) (R : List (SymArg × Rega.RegLoc Reg64 RegMm CondCode))
    (sa : SymArg) :
    Rega.findVecFor vllX64IsaR b R sa = Rega.findVecFor x64Isa b R sa := by
  refine list_findSome_congr (fun ⟨sa', rl⟩ => ?_) R
  cases rl with
  | gpr _ | gprZ _ | flag _ => rfl
  | vec v =>
    dsimp only
    rw [list_contains_decEq_congr vllX64IsaR.decEqVReg x64Isa.decEqVReg, vllR_vecScratch_eq]

theorem findFlagFor_eq (R : List (SymArg × Rega.RegLoc Reg64 RegMm CondCode)) (sa : SymArg) :
    Rega.findFlagFor vllX64IsaR R sa = Rega.findFlagFor x64Isa R sa := by
  refine list_findSome_congr (fun ⟨sa', rl⟩ => ?_) R
  cases rl <;> rfl

theorem findGprFor_ne_rsp (noScr : Bool)
    {R : List (SymArg × Rega.RegLoc Reg64 RegMm CondCode)} {sa : SymArg} {r : Reg64}
    (hR : regsNoRsp R = true) (h : Rega.findGprFor vllX64IsaR noScr R sa = some r) :
    r ≠ .rsp := by
  rw [findGprFor_eq] at h
  dsimp only [Rega.findGprFor] at h
  induction R with
  | nil => dsimp only [List.findSome?] at h; cases h
  | cons hd tl ih =>
    rcases hd with ⟨sa', rl⟩
    simp only [regsNoRsp, List.all_cons, Bool.and_eq_true] at hR
    cases rl with
    | vec _ | flag _ => exact ih hR.2 h
    | gpr r' | gprZ r' =>
      dsimp only [List.findSome?] at h
      split at h
      · rename_i b hif
        split at hif <;> cases hif
        dsimp only at h hR; cases h; intro e; rw [e] at hR; exact absurd hR.1 (by decide)
      · exact ih hR.2 h

theorem holdsLoc_eq (st : Rega.SymState vllX64IsaR) (sa : SymArg) (loc : vllX64IsaR.Loc) :
    Rega.holdsLoc vllX64IsaR st sa loc = Rega.holdsLoc x64Isa (symStToX64 st) sa loc := by
  cases loc with
  | slot _ _ => rfl
  | gpr r =>
    refine list_any_congr (fun ⟨sa', rl⟩ => ?_) st.regs
    cases rl with
    | vec _ | flag _ => rfl
    | gpr r' | gprZ r' =>
      dsimp only; rw [decEq_beq_congr vllX64IsaR.decEqReg x64Isa.decEqReg r' r]
  | vec v =>
    refine list_any_congr (fun ⟨sa', rl⟩ => ?_) st.regs
    cases rl with
    | gpr _ | gprZ _ | flag _ => rfl
    | vec v' =>
      dsimp only; rw [decEq_beq_congr vllX64IsaR.decEqVReg x64Isa.decEqVReg v' v]
  | flag cc =>
    refine list_any_congr (fun ⟨sa', rl⟩ => ?_) st.regs
    cases rl with
    | gpr _ | gprZ _ | vec _ => rfl
    | flag c' =>
      dsimp only; rw [decEq_beq_congr vllX64IsaR.decEqCond x64Isa.decEqCond c' cc]

theorem moveFor_eq (nslots : Nat) (st : Rega.SymState vllX64IsaR) (sa : SymArg)
    (loc : vllX64IsaR.Loc) :
    Rega.moveFor vllX64IsaR nslots st sa loc =
      Rega.moveFor x64Isa nslots (symStToX64 st) sa loc := by
  cases loc with
  | flag _ => rfl
  | gpr d =>
    cases sa with
    | immBits _ _ | immBool _ | immVec _ _ => rfl
    | var _ =>
      dsimp only [Rega.moveFor, symStToX64]
      rw [findGprFor_eq, findFlagFor_eq]
  | vec vd =>
    cases sa with
    | immVec _ _ | immBits _ _ | immBool _ => rfl
    | var _ =>
      dsimp only [Rega.moveFor, symStToX64]
      cases Rega.symArgWidth st.vecWidths _ with
      | none => rfl
      | some w => dsimp only; rw [findVecFor_eq]
  | slot i w =>
    dsimp only [Rega.moveFor, symStToX64]
    cases Rega.symArgWidth st.vecWidths sa with
    | some _ => dsimp only; rw [findVecFor_eq]
    | none => dsimp only; rw [findGprFor_eq]

theorem regLocEq_eq (rl₁ rl₂ : Rega.RegLoc Reg64 RegMm CondCode) :
    Rega.regLocEq (I := vllX64IsaR) rl₁ rl₂ = Rega.regLocEq (I := x64Isa) rl₁ rl₂ := by
  cases rl₁ <;> cases rl₂ <;> first
    | rfl
    | exact decEq_beq_congr vllX64IsaR.decEqReg x64Isa.decEqReg _ _
    | exact decEq_beq_congr vllX64IsaR.decEqVReg x64Isa.decEqVReg _ _
    | exact decEq_beq_congr vllX64IsaR.decEqCond x64Isa.decEqCond _ _

theorem regLocMatchesGpr_eq (rl : Rega.RegLoc Reg64 RegMm CondCode) (r : Reg64) :
    Rega.regLocMatchesGpr (I := vllX64IsaR) rl r = Rega.regLocMatchesGpr (I := x64Isa) rl r := by
  cases rl <;> first
    | rfl
    | exact decEq_beq_congr vllX64IsaR.decEqReg x64Isa.decEqReg _ _

theorem locEq_eq (l₁ l₂ : vllX64IsaR.Loc) :
    Rega.locEq (I := vllX64IsaR) l₁ l₂ = Rega.locEq (I := x64Isa) l₁ l₂ := by
  cases l₁ <;> cases l₂ <;> first
    | rfl
    | exact decEq_beq_congr vllX64IsaR.decEqReg x64Isa.decEqReg _ _
    | exact decEq_beq_congr vllX64IsaR.decEqVReg x64Isa.decEqVReg _ _
    | exact decEq_beq_congr vllX64IsaR.decEqCond x64Isa.decEqCond _ _

theorem locBlocked_eq (st : Rega.SymState vllX64IsaR) (pend : List (SymArg × vllX64IsaR.Loc))
    (loc : vllX64IsaR.Loc) :
    Rega.locBlocked vllX64IsaR st pend loc = Rega.locBlocked x64Isa (symStToX64 st) pend loc := by
  dsimp only [Rega.locBlocked, symStToX64]
  refine list_any_congr (fun ⟨sa, d'⟩ => ?_) pend
  rw [locEq_eq]
  refine congrArg (_ && ·) ?_
  cases loc with
  | flag _ | slot _ _ => rfl
  | gpr r =>
    dsimp only
    rw [list_all_congr (fun p => congrArg (_ || ·) (regLocMatchesGpr_eq p.2 r)) st.regs,
      list_any_congr (fun p => congrArg (_ && ·) (regLocMatchesGpr_eq p.2 r)) st.regs]
  | vec v =>
    dsimp only
    rw [list_all_congr (fun p => congrArg (_ || ·) (regLocEq_eq p.2 (.vec v))) st.regs,
      list_any_congr (fun p => congrArg (_ && ·) (regLocEq_eq p.2 (.vec v))) st.regs]

theorem vecWidthAt_eq (st : Rega.SymState vllX64IsaR) (vd : RegMm) :
    Rega.vecWidthAt vllX64IsaR st vd = Rega.vecWidthAt x64Isa (symStToX64 st) vd := by
  dsimp only [Rega.vecWidthAt, symStToX64]
  refine list_foldl_congr (fun w ⟨sa, rl⟩ => ?_) st.regs (@SlotWidth.w64)
  cases rl with
  | gpr _ | gprZ _ | flag _ => rfl
  | vec v =>
    dsimp only; rw [decEq_beq_congr vllX64IsaR.decEqVReg x64Isa.decEqVReg v vd]

private theorem assignSig_locsNoRsp :
    ∀ {ts : List Ty} {gs : List Reg64} {vs : List RegMm}
      {locs : Tup (AbiReg Reg64 RegMm) ts},
      (∀ r ∈ gs, r ≠ .rsp) →
      x64Isa.assignSig ts gs vs = some locs → locsNoRsp locs = true
  | [], _, _, (), _, _ => rfl
  | .bool :: _, [], _, _, _, h => by cases h
  | .bool :: ts, r :: gs, vs, locs, hgs, h => by
    dsimp only [Isa.assignSig] at h
    cases h' : x64Isa.assignSig ts gs vs with
    | none => rw [h'] at h; cases h
    | some locs' =>
      rw [h'] at h; cases h
      exact Bool.and_eq_true_iff.mpr ⟨reg64_bne_of_ne (hgs r List.mem_cons_self),
        @assignSig_locsNoRsp ts gs vs locs'
          (fun x hx => hgs x (List.mem_cons_of_mem _ hx)) h'⟩
  | .bits n :: _, [], _, _, _, h => by cases h
  | .bits n :: ts, r :: gs, vs, locs, hgs, h => by
    dsimp only [Isa.assignSig] at h
    split at h
    · cases h' : x64Isa.assignSig ts gs vs with
      | none => rw [h'] at h; cases h
      | some locs' =>
        rw [h'] at h; cases h
        exact Bool.and_eq_true_iff.mpr ⟨reg64_bne_of_ne (hgs r List.mem_cons_self),
          @assignSig_locsNoRsp ts gs vs locs'
            (fun x hx => hgs x (List.mem_cons_of_mem _ hx)) h'⟩
    · cases h
  | .float _ :: _, _, _, _, _, h => by cases h
  | .pair a b :: _, _, [], _, _, h => by cases h
  | .pair a b :: ts, gs, _ :: vs, locs, hgs, h => by
    dsimp only [Isa.assignSig] at h
    split at h
    · cases h' : x64Isa.assignSig ts gs vs with
      | none => rw [h'] at h; cases h
      | some locs' =>
        simp only [h', Option.map_some, Option.some.injEq] at h; subst h
        exact @assignSig_locsNoRsp ts gs vs locs' hgs h'
    · cases h

theorem assignArgs_locsNoRsp {as : List Ty} {locs : Tup (AbiReg Reg64 RegMm) as}
    (h : vllX64IsaR.assignArgs as = some locs) : locsNoRsp locs = true := by
  rw [vllR_assignArgs_eq] at h
  exact assignSig_locsNoRsp (fun r hr => by
    have : r ∈ [Reg64.rdi, .rsi, .rdx, .rcx, .r8, .r9] := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) h

theorem assignRets_locsNoRsp {rs : List Ty} {locs : Tup (AbiReg Reg64 RegMm) rs}
    (h : vllX64IsaR.assignRets rs = some locs) : locsNoRsp locs = true := by
  rw [vllR_assignRets_eq] at h
  exact assignSig_locsNoRsp (fun r hr => by
    have : r ∈ [Reg64.rax, .rdx, .rcx, .rsi, .rdi, .r8, .r9] := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) h

private theorem vllR_mov_ne_nil (d s : Reg64) :
    asmX64List (vllX64IsaR.gpr.mov d s) ≠ [] := by
  rw [vllR_mov_eq]
  dsimp only [x64Isa, x64Gpr, emitClean, movI]
  intro h; simp [x64InsI] at h

private theorem vllR_movi_ne_nil (d : Reg64) (cb : BitVec 64) :
    asmX64List (vllX64IsaR.gpr.movi d cb) ≠ [] := by
  rw [vllR_movi_eq]
  dsimp only [x64Isa, x64Gpr, emitClean, moviI, moviD]
  intro h; split at h <;> cases h

private theorem vllR_slotLd_ne_nil (d : Reg64) (i : Nat) :
    asmX64List (vllX64IsaR.frame.slotLd d i) ≠ [] := by
  rw [vllR_slotLd_eq]
  dsimp only [x64Isa, x64Frame, x64SlotLd, x64SlotLdIns, emitClean]
  intro h; split at h <;> cases h

private theorem vllR_slotSt_ne_nil (i : Nat) (s : Reg64) :
    asmX64List (vllX64IsaR.frame.slotSt i s) ≠ [] := by
  rw [vllR_slotSt_eq]
  dsimp only [x64Isa, x64Frame, x64SlotSt, x64SlotStIns, emitClean]
  intro h; split at h <;> cases h

private theorem vllR_setcc_ne_nil (d : Reg64) (cc : CondCode) :
    asmX64List (vllX64IsaR.gpr.setcc d cc) ≠ [] := by
  rw [vllR_setcc_eq]
  dsimp only [x64Isa, x64Gpr, setccOnly, setccOnlyIns, emitClean]
  intro h; cases h

private theorem vllR_vmov_ne_nil (w : SlotWidth) (d s : RegMm) :
    asmX64List (vllX64IsaR.vec.vmov w d s) ≠ [] := by
  rw [vllR_vmov_eq]
  cases w <;> cases d <;> cases s <;> decide

private theorem vllR_vslotLd_ne_nil (w : SlotWidth) (d : RegMm) (i : Nat) :
    asmX64List (vllX64IsaR.vec.vslotLd w d i) ≠ [] := by
  rw [vllR_vslotLd_eq]
  dsimp only [x64Isa, x64Vec, x64VslotLd, x64VslotLdIns, emitClean]
  intro h
  simp only [List.map_append, List.map_cons, List.map_nil, List.append_eq_nil_iff,
    List.cons_ne_nil, and_false] at h

private theorem vllR_vslotSt_ne_nil (w : SlotWidth) (i : Nat) (s : RegMm) :
    asmX64List (vllX64IsaR.vec.vslotSt w i s) ≠ [] := by
  rw [vllR_vslotSt_eq]
  dsimp only [x64Isa, x64Vec, x64VslotSt, x64VslotStIns, emitClean]
  intro h
  simp only [List.map_append, List.map_cons, List.map_nil, List.append_eq_nil_iff,
    List.cons_ne_nil, and_false] at h

theorem execMove_eq_and_noRsp {nslots : Nat} {saved : List Reg64}
    (hs : savedNoRsp saved = true) (mv : vllX64IsaR.Move) (st : Rega.SymState vllX64IsaR)
    (hno : regsNoRsp st.regs = true) :
    mapOptSt (Rega.execMove vllX64IsaR nslots saved mv st) =
      Rega.execMove x64Isa nslots saved mv (symStToX64 st) ∧
    (∀ c0 st', Rega.execMove vllX64IsaR nslots saved mv st = some (c0, st') →
      regsNoRsp st'.regs = true ∧ (asmX64List c0 = [] → c0 = [])) := by
  cases mv with
  | mov d s =>
    dsimp only [Rega.execMove]
    rw [vllR_isMoveGpr_eq]
    cases hm : Rega.isMoveGpr x64Isa saved d with
    | false => exact ⟨rfl, fun _ _ h => by cases h⟩
    | true =>
      have hd : d ≠ .rsp := isMoveGpr_ne_rsp hs (by rw [vllR_isMoveGpr_eq]; exact hm)
      simp only [Bool.not_true]
      rw [decEq_beq_congr vllX64IsaR.decEqReg x64Isa.decEqReg d s]
      cases hds : @BEq.beq x64Isa.Reg (@instBEqOfDecidableEq x64Isa.Reg x64Isa.decEqReg) d s with
      | true =>
        simp only [Bool.false_eq_true, ↓reduceIte, mapOptSt, Option.map_some, symStToX64]
        refine ⟨?_, fun _ _ heq => by
          cases heq; exact ⟨hno, fun h => absurd h (vllR_mov_ne_nil d s)⟩⟩
        rw [vllR_mov_eq]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, mapOptSt, Option.map_some]
        refine ⟨?_, fun _ _ heq => by
          cases heq
          exact ⟨regsNoRsp_append (regsNoRsp_map_gprTagged (fun p => by
            cases p.2 <;> exact hd) _) (regsNoRsp_killRegs _ hno),
            fun h => absurd h (vllR_mov_ne_nil d s)⟩⟩
        dsimp only [symStToX64]
        rw [vllR_mov_eq, list_contains_decEq_congr vllX64IsaR.decEqReg x64Isa.decEqReg,
          killZeroExt_eq, gprTaggedEntries_eq, killRegs_eq]
  | movi d cb =>
    dsimp only [Rega.execMove]
    rw [vllR_isMoveGpr_eq]
    cases hm : Rega.isMoveGpr x64Isa saved d with
    | false => exact ⟨rfl, fun _ _ h => by cases h⟩
    | true =>
      have hd : d ≠ .rsp := isMoveGpr_ne_rsp hs (by rw [vllR_isMoveGpr_eq]; exact hm)
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, mapOptSt, Option.map_some]
      refine ⟨?_, fun _ _ heq => by
        cases heq
        exact ⟨regsNoRsp_cons_gpr hd (regsNoRsp_killRegs _ hno),
          fun h => absurd h (vllR_movi_ne_nil d cb)⟩⟩
      dsimp only [symStToX64]
      rw [vllR_movi_eq, vllR_scratch_eq, killZeroExt_eq, killRegs_eq]
  | ld d i =>
    dsimp only [Rega.execMove]
    rw [vllR_isAllocGpr_eq]
    cases hok : Rega.isAllocGpr x64Isa saved d && Nat.ble (i + 1) nslots with
    | false => exact ⟨rfl, fun _ _ h => by cases h⟩
    | true =>
      have ha := (Bool.and_eq_true_iff.mp hok).1
      have hd : d ≠ .rsp := isAllocGpr_x64_ne_rsp hs ha
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, mapOptSt, Option.map_some]
      refine ⟨?_, fun _ _ heq => by
        cases heq
        have hc : regsNoRsp (match st.slots.find? i with
            | some (.gpr sas) => sas.map (·, Rega.RegLoc.gpr d)
            | some (.gprZ sas) => sas.map fun p => (p.1, if p.2 then .gprZ d else .gpr d)
            | _ => []) = true := by
          cases st.slots.find? i with
          | none => rfl
          | some se => cases se with
            | vec _ _ => rfl
            | gpr sas => exact regsNoRsp_map (fun _ => hd) sas
            | gprZ sas =>
              exact regsNoRsp_map_gprTagged (fun p => by cases p.2 <;> exact hd) sas
        exact ⟨regsNoRsp_append hc (regsNoRsp_killRegs _ hno),
          fun h => absurd h (vllR_slotLd_ne_nil d i)⟩⟩
      dsimp only [symStToX64]
      rw [vllR_slotLd_eq, vllR_scratch_eq, killZeroExt_eq, killRegs_eq]
  | st i s =>
    dsimp only [Rega.execMove]
    rw [list_contains_decEq_congr vllX64IsaR.decEqReg x64Isa.decEqReg]
    have hsc : vllX64FrameR.scratch = x64Scratch := rfl
    rw [hsc]
    split
    · exact ⟨rfl, fun _ _ h => by cases h⟩
    · simp only [mapOptSt, Option.map_some]
      refine ⟨?_, fun _ _ heq => by
        cases heq
        exact ⟨regsNoRsp_killRegs _ hno, fun h => absurd h (vllR_slotSt_ne_nil i s)⟩⟩
      dsimp only [symStToX64]
      rw [vllR_slotSt_eq, killZeroExt_eq, gprTaggedEntries_eq, killRegs_eq]
  | setcc d cc =>
    dsimp only [Rega.execMove]
    rw [vllR_isAllocGpr_eq]
    cases ha : Rega.isAllocGpr x64Isa saved d with
    | false => exact ⟨rfl, fun _ _ h => by cases h⟩
    | true =>
      have hd : d ≠ .rsp := isAllocGpr_x64_ne_rsp hs ha
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, mapOptSt, Option.map_some]
      refine ⟨?_, fun _ _ heq => by
        cases heq
        exact ⟨regsNoRsp_append (regsNoRsp_map (fun _ => hd) _) (regsNoRsp_killRegs _ hno),
          fun h => absurd h (vllR_setcc_ne_nil d cc)⟩⟩
      dsimp only [symStToX64]
      rw [vllR_setcc_eq, vllR_scratch_eq, flagEntries_eq, killZeroExt_eq, killRegs_eq]
  | vmov w d s =>
    dsimp only [Rega.execMove]
    rw [vllR_isMoveVec_eq]
    cases hm : Rega.isMoveVec x64Isa d with
    | false => exact ⟨rfl, fun _ _ h => by cases h⟩
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, mapOptSt, Option.map_some]
      refine ⟨?_, fun _ _ heq => by
        cases heq
        exact ⟨regsNoRsp_append (regsNoRsp_map (fun _ => trivial) _) (regsNoRsp_killRegs _ hno),
          fun h => absurd h (vllR_vmov_ne_nil w d s)⟩⟩
      dsimp only [symStToX64]
      rw [vllR_vmov_eq, vecEntries_eq, killRegs_eq]
  | vmovi w d cb =>
    dsimp only [Rega.execMove]
    rw [vllR_isAllocVec_eq]
    cases ha : Rega.isAllocVec x64Isa d with
    | false => exact ⟨rfl, fun _ _ h => by cases h⟩
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have hvm := vllR_vmovi_eq w d cb
      cases hvi : vllX64VecR.vmovi w d cb with
      | none =>
        rw [hvi] at hvm
        dsimp only [Option.map] at hvm
        rw [← hvm]
        exact ⟨rfl, fun _ _ h => by cases h⟩
      | some code =>
        rw [hvi] at hvm
        dsimp only [Option.map] at hvm
        rw [← hvm]
        simp only [mapOptSt, Option.map_some, symStToX64]
        refine ⟨?_, fun c0 st' heq => by
          cases heq
          refine ⟨regsNoRsp_cons_vec (regsNoRsp_killRegs _ hno), fun h => ?_⟩
          dsimp only [vllX64VecR, vllX64Isa, vllIsa, vllX64Policy, vllIsaOfHooks,
            vllX64NativeHooks, vllX64Vec] at hvi
          rcases Option.map_eq_some_iff.mp hvi with ⟨ds, _, rfl⟩
          rw [asmX64List_map_native] at h; subst h; rfl⟩
        rw [vllR_scratch_eq, vllR_vecScratch_eq, killZeroExt_eq, killRegs_eq]
  | vld w d i =>
    dsimp only [Rega.execMove]
    rw [vllR_isAllocVec_eq]
    cases hok : Rega.isAllocVec x64Isa d && Nat.ble (i + w.slots) nslots with
    | false => exact ⟨rfl, fun _ _ h => by cases h⟩
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, mapOptSt, Option.map_some]
      refine ⟨?_, fun _ _ heq => by
        cases heq
        have hc : regsNoRsp (match st.slots.find? i with
            | some (.vec w' sas) =>
              if Rega.slotWidthEq w' w then sas.map (·, Rega.RegLoc.vec d) else []
            | _ => []) = true := by
          cases st.slots.find? i with
          | none => rfl
          | some se => cases se with
            | gpr _ | gprZ _ => rfl
            | vec w' sas =>
              dsimp only
              cases hsw : Rega.slotWidthEq w' w
              · simp only [Bool.false_eq_true, ↓reduceIte]; rfl
              · simp only [↓reduceIte]
                exact regsNoRsp_map (f := fun sa => (sa, Rega.RegLoc.vec d))
                  (fun _ => trivial) sas
        exact ⟨regsNoRsp_append hc (regsNoRsp_killRegs _ hno),
          fun h => absurd h (vllR_vslotLd_ne_nil w d i)⟩⟩
      dsimp only [symStToX64]
      rw [vllR_vslotLd_eq, vllR_scratch_eq, vllR_vecScratch_eq, killZeroExt_eq, killRegs_eq]
  | vst w i s =>
    dsimp only [Rega.execMove]
    rw [list_contains_decEq_congr vllX64IsaR.decEqVReg x64Isa.decEqVReg]
    have hvsc : vllX64VecR.vecScratch = x64VecScratch := rfl
    rw [hvsc]
    split
    · exact ⟨rfl, fun _ _ h => by cases h⟩
    · simp only [mapOptSt, Option.map_some]
      refine ⟨?_, fun _ _ heq => by
        cases heq
        exact ⟨regsNoRsp_killRegs _ hno, fun h => absurd h (vllR_vslotSt_ne_nil w i s)⟩⟩
      dsimp only [symStToX64]
      rw [vllR_vslotSt_eq, vllR_scratch_eq, vecEntries_eq, killZeroExt_eq, killRegs_eq]

theorem execMoves_eq_and_noRsp {nslots : Nat} {saved : List Reg64}
    (hs : savedNoRsp saved = true) :
    ∀ (mvs : List vllX64IsaR.Move) (st : Rega.SymState vllX64IsaR),
      regsNoRsp st.regs = true →
      mapOptSt (Rega.execMoves vllX64IsaR nslots saved mvs st) =
        Rega.execMoves x64Isa nslots saved mvs (symStToX64 st) ∧
      (∀ c0 st', Rega.execMoves vllX64IsaR nslots saved mvs st = some (c0, st') →
        regsNoRsp st'.regs = true ∧ (asmX64List c0 = [] → c0 = []))
  | [], st, hno =>
    ⟨rfl, fun _ _ h => by cases h; exact ⟨hno, fun _ => rfl⟩⟩
  | mv :: mvs, st, hno => by
    obtain ⟨hm1, hp1⟩ := execMove_eq_and_noRsp hs mv st hno
    dsimp only [Rega.execMoves]
    cases h1 : Rega.execMove vllX64IsaR nslots saved mv st with
    | none =>
      have h1x : Rega.execMove x64Isa nslots saved mv (symStToX64 st) = none := by
        rw [← hm1, h1]; rfl
      rw [h1x]
      exact ⟨rfl, fun _ _ h => by cases h⟩
    | some p1 =>
      rcases p1 with ⟨c1, st1⟩
      obtain ⟨hno1, hnil1⟩ := hp1 c1 st1 h1
      have h1x : Rega.execMove x64Isa nslots saved mv (symStToX64 st) =
          some (asmX64List c1, symStToX64 st1) := by
        rw [← hm1, h1]; rfl
      obtain ⟨hm2, hp2⟩ := execMoves_eq_and_noRsp hs mvs st1 hno1
      dsimp only [Option.bind]
      rw [h1x]
      dsimp only [Option.bind]
      cases h2 : Rega.execMoves vllX64IsaR nslots saved mvs st1 with
      | none =>
        have h2x : Rega.execMoves x64Isa nslots saved mvs (symStToX64 st1) = none := by
          rw [← hm2, h2]; rfl
        rw [h2x]
        exact ⟨rfl, fun _ _ h => by cases h⟩
      | some p2 =>
        rcases p2 with ⟨c2, st2⟩
        obtain ⟨hno2, hnil2⟩ := hp2 c2 st2 h2
        have h2x : Rega.execMoves x64Isa nslots saved mvs (symStToX64 st1) =
            some (asmX64List c2, symStToX64 st2) := by
          rw [← hm2, h2]; rfl
        rw [h2x]
        dsimp only [mapOptSt, Option.map_some]
        refine ⟨?_, fun c0 st' heq => by
          cases heq
          refine ⟨hno2, fun ha => ?_⟩
          rw [asmX64List_append, List.append_eq_nil_iff] at ha
          rw [hnil1 ha.1, hnil2 ha.2]; rfl⟩
        rw [asmX64List_append]

theorem execClearFlags_eq_and_noRsp (st : Rega.SymState vllX64IsaR)
    (hno : regsNoRsp st.regs = true) :
    (asmX64List (Rega.execClearFlags vllX64IsaR st).1,
      symStToX64 (Rega.execClearFlags vllX64IsaR st).2) =
      Rega.execClearFlags x64Isa (symStToX64 st) ∧
    regsNoRsp (Rega.execClearFlags vllX64IsaR st).2.regs = true ∧
    asmX64List (Rega.execClearFlags vllX64IsaR st).1 ≠ [] := by
  refine ⟨?_, regsNoRsp_append (regsNoRsp_map (fun _ => trivial) _) (regsNoRsp_killRegs _ hno),
    fun h => by
      dsimp only [Rega.execClearFlags] at h
      rw [vllR_clearFlags_eq] at h; cases h⟩
  dsimp only [Rega.execClearFlags, symStToX64]
  rw [vllR_clearFlags_eq, vllR_zeroFlags_eq, vllR_scratch_eq, killRegs_eq, killZeroExt_eq]

theorem stepPre_eq_and_noRsp (h : x64Isa.Hints) (ip : Nat)
    (hs : savedNoRsp h.saved = true) (st : Rega.SymState vllX64IsaR)
    (hno : regsNoRsp st.regs = true) :
    mapOptSt (Rega.stepPre vllX64IsaR h ip st) = Rega.stepPre x64Isa h ip (symStToX64 st) ∧
    (∀ c0 st', Rega.stepPre vllX64IsaR h ip st = some (c0, st') →
      regsNoRsp st'.regs = true ∧ (asmX64List c0 = [] → c0 = [])) := by
  dsimp only [Rega.stepPre]
  cases hf : h.pre.find? ip with
  | none =>
    dsimp only [mapOptSt, Option.map_some, symStToX64]
    exact ⟨rfl, fun _ _ h0 => by cases h0; exact ⟨hno, fun _ => rfl⟩⟩
  | some ps =>
    dsimp only
    obtain ⟨hm, hp⟩ := execMoves_eq_and_noRsp hs ps.moves st hno
    cases h1 : Rega.execMoves vllX64IsaR h.nslots h.saved ps.moves st with
    | none =>
      have h1x : Rega.execMoves x64Isa h.nslots h.saved ps.moves (symStToX64 st) = none := by
        rw [← hm, h1]; rfl
      rw [h1x]
      exact ⟨rfl, fun _ _ h0 => by cases h0⟩
    | some p1 =>
      rcases p1 with ⟨mc, st1⟩
      obtain ⟨hno1, hnil1⟩ := hp mc st1 h1
      have h1x : Rega.execMoves x64Isa h.nslots h.saved ps.moves (symStToX64 st) =
          some (asmX64List mc, symStToX64 st1) := by
        rw [← hm, h1]; rfl
      dsimp only [Option.map]
      rw [h1x]
      dsimp only [Option.map]
      cases hcf : ps.clearFlags with
      | false =>
        dsimp only [Bool.false_eq_true, ↓reduceIte, mapOptSt, Option.map_some]
        exact ⟨rfl, fun _ _ h0 => by cases h0; exact ⟨hno1, hnil1⟩⟩
      | true =>
        dsimp only [↓reduceIte, mapOptSt, Option.map_some]
        obtain ⟨hce, hcno, hcne⟩ := execClearFlags_eq_and_noRsp st1 hno1
        refine ⟨?_, fun _ _ h0 => by
          cases h0
          refine ⟨hcno, fun h => ?_⟩
          rw [asmX64List_append, List.append_eq_nil_iff] at h
          exact absurd h.2 hcne⟩
        have hce1 : asmX64List (Rega.execClearFlags vllX64IsaR st1).1 =
            (Rega.execClearFlags x64Isa (symStToX64 st1)).1 := congrArg Prod.fst hce
        have hce2 : symStToX64 (Rega.execClearFlags vllX64IsaR st1).2 =
            (Rega.execClearFlags x64Isa (symStToX64 st1)).2 := congrArg Prod.snd hce
        simp only [↓reduceIte]
        rw [asmX64List_append, hce1, hce2]

private theorem slotBusy_eq (st : Rega.SymState vllX64IsaR)
    (pend : List (SymArg × vllX64IsaR.Loc)) (i k : Nat) :
    Rega.slotBusy vllX64IsaR st pend i k =
      Rega.slotBusy x64Isa (symStToX64 st) pend i k := by
  dsimp only [Rega.slotBusy]
  have hscan : ∀ (j fuel : Nat),
      Rega.slotBusy.scan vllX64IsaR st i k j fuel =
      Rega.slotBusy.scan x64Isa (symStToX64 st) i k j fuel := by
    intro j fuel
    induction fuel generalizing j with
    | zero => rfl
    | succ f ih => dsimp only [Rega.slotBusy.scan, symStToX64]; rw [ih (j + 1)]
  rw [hscan (i - 7) (k + 7)]
  refine congrArg (· || Rega.slotBusy.scan x64Isa (symStToX64 st) i k (i - 7) (k + 7)) ?_
  refine list_any_congr (fun p => ?_) pend
  cases p.2 <;> rfl

private theorem findFreeSlot_eq (nslots : Nat) (st : Rega.SymState vllX64IsaR)
    (pend : List (SymArg × vllX64IsaR.Loc)) (k : Nat) :
    Rega.findFreeSlot vllX64IsaR nslots st pend k =
      Rega.findFreeSlot x64Isa nslots (symStToX64 st) pend k := by
  dsimp only [Rega.findFreeSlot]
  suffices h : ∀ (i fuel : Nat),
      Rega.findFreeSlot.go vllX64IsaR nslots st pend k i fuel =
      Rega.findFreeSlot.go x64Isa nslots (symStToX64 st) pend k i fuel from h 0 nslots
  intro i fuel
  induction fuel generalizing i with
  | zero => rfl
  | succ f ih =>
    dsimp only [Rega.findFreeSlot.go]
    rw [slotBusy_eq]
    split
    · rfl
    · exact ih (i + 1)

private theorem find_bridge {R1 V1 C1 R2 V2 C2 : Type}
    {p : SymArg × Loc R1 V1 C1 → Bool} {q : SymArg × Loc R2 V2 C2 → Bool}
    {xs : List (SymArg × Loc R1 V1 C1)} {ys : List (SymArg × Loc R2 V2 C2)}
    {a : Option (SymArg × Loc R1 V1 C1)} {b : Option (SymArg × Loc R2 V2 C2)}
    (h1 : xs.find? p = a) (h2 : ys.find? q = b)
    (hR : R1 = R2) (hV : V1 = V2) (hC : C1 = C2) (hxy : HEq xs ys)
    (hpGpr : ∀ sa r1 r2, HEq r1 r2 → p (sa, .gpr r1) = q (sa, .gpr r2))
    (hpVec : ∀ sa v1 v2, HEq v1 v2 → p (sa, .vec v1) = q (sa, .vec v2))
    (hpFlag : ∀ sa c1 c2, HEq c1 c2 → p (sa, .flag c1) = q (sa, .flag c2))
    (hpSlot : ∀ sa i w, p (sa, .slot i w) = q (sa, .slot i w)) :
    HEq a b := by
  subst hR; subst hV; subst hC; cases eq_of_heq hxy
  have hpq : p = q := funext fun ⟨sa, l⟩ => by
    cases l with
    | gpr r => exact hpGpr sa r r HEq.rfl
    | vec v => exact hpVec sa v v HEq.rfl
    | flag c => exact hpFlag sa c c HEq.rfl
    | slot i w => exact hpSlot sa i w
  subst hpq
  exact heq_of_eq (h1.symm.trans h2)

private theorem find_absurd {R1 V1 C1 R2 V2 C2 : Type}
    {p : SymArg × Loc R1 V1 C1 → Bool} {q : SymArg × Loc R2 V2 C2 → Bool}
    {xs : List (SymArg × Loc R1 V1 C1)} {ys : List (SymArg × Loc R2 V2 C2)}
    {a : Option (SymArg × Loc R1 V1 C1)} {b : Option (SymArg × Loc R2 V2 C2)}
    (h1 : xs.find? p = a) (hne : ys.find? q = b → False)
    (hR : R1 = R2) (hV : V1 = V2) (hC : C1 = C2)
    (hxy : HEq xs ys) (hab : HEq a b)
    (hpGpr : ∀ sa r1 r2, HEq r1 r2 → p (sa, .gpr r1) = q (sa, .gpr r2))
    (hpVec : ∀ sa v1 v2, HEq v1 v2 → p (sa, .vec v1) = q (sa, .vec v2))
    (hpFlag : ∀ sa c1 c2, HEq c1 c2 → p (sa, .flag c1) = q (sa, .flag c2))
    (hpSlot : ∀ sa i w, p (sa, .slot i w) = q (sa, .slot i w)) : False :=
  hne (eq_of_heq
    ((find_bridge h1 rfl hR hV hC hxy hpGpr hpVec hpFlag hpSlot).symm.trans hab))

private theorem heq_some_gpr_eq {R1 V1 C1 R2 V2 C2 : Type}
    {sa1 sa2 : SymArg} {d1 : R1} {d2 : R2} (hR : R1 = R2) (hV : V1 = V2) (hC : C1 = C2)
    (h : HEq (some (sa1, @Loc.gpr R1 V1 C1 d1)) (some (sa2, @Loc.gpr R2 V2 C2 d2))) :
    HEq d1 d2 := by
  subst hR; subst hV; subst hC
  exact heq_of_eq (Loc.gpr.inj (Prod.ext_iff.mp (Option.some.inj (eq_of_heq h))).2)

private theorem heq_some_vec_eq {R1 V1 C1 R2 V2 C2 : Type}
    {sa1 sa2 : SymArg} {v1 : V1} {v2 : V2} (hR : R1 = R2) (hV : V1 = V2) (hC : C1 = C2)
    (h : HEq (some (sa1, @Loc.vec R1 V1 C1 v1)) (some (sa2, @Loc.vec R2 V2 C2 v2))) :
    HEq v1 v2 := by
  subst hR; subst hV; subst hC
  exact heq_of_eq (Loc.vec.inj (Prod.ext_iff.mp (Option.some.inj (eq_of_heq h))).2)

private theorem pmoveAux_eq (nslots : Nat) (saved : List Reg64) (hs : savedNoRsp saved = true) :
    ∀ (fuel : Nat) (st : Rega.SymState vllX64IsaR) (tgts : List (SymArg × vllX64IsaR.Loc))
      (acc : List vllX64IsaR.Move),
      regsNoRsp st.regs = true →
      Rega.pmoveAux vllX64IsaR nslots saved fuel st tgts acc =
        Rega.pmoveAux x64Isa nslots saved fuel (symStToX64 st) tgts acc
  | 0, _, _, _, _ => rfl
  | fuel + 1, st, targets, acc, hno => by
    dsimp only [Rega.pmoveAux]
    simp only [holdsLoc_eq]
    cases hpend : targets.filter
        (fun (sa, loc) => !Rega.holdsLoc x64Isa (symStToX64 st) sa loc) with
    | nil => rfl
    | cons hd tl =>
      simp only [locBlocked_eq]
      have hf1 :
          @List.find? (SymArg × vllX64IsaR.Loc)
            (fun x => Rega.isVarSymArg x.fst &&
              !(Rega.locBlocked x64Isa (symStToX64 st) (hd :: tl) x.snd)) (hd :: tl) =
          @List.find? (SymArg × x64Isa.Loc)
            (fun x => Rega.isVarSymArg x.fst &&
              !(Rega.locBlocked x64Isa (symStToX64 st) (hd :: tl) x.snd)) (hd :: tl) := rfl
      rw [hf1]
      cases @List.find? (SymArg × x64Isa.Loc)
          (fun x => Rega.isVarSymArg x.fst &&
            !(Rega.locBlocked x64Isa (symStToX64 st) (hd :: tl) x.snd)) (hd :: tl) with
      | some p1 =>
        rcases p1 with ⟨sa1, loc1⟩; dsimp only
        rw [moveFor_eq]
        cases Rega.moveFor x64Isa nslots (symStToX64 st) sa1 loc1 with
        | none => dsimp only
        | some mv =>
          dsimp only
          obtain ⟨hm, hp⟩ := execMove_eq_and_noRsp hs mv st hno
          cases hmv : Rega.execMove vllX64IsaR nslots saved mv st with
          | none =>
            have hmx : Rega.execMove x64Isa nslots saved mv (symStToX64 st) = none := by
              rw [← hm, hmv]; rfl
            rw [hmx]
          | some p0 =>
            rcases p0 with ⟨c1, st1⟩
            obtain ⟨hno1, _⟩ := hp c1 st1 hmv
            have hmx : Rega.execMove x64Isa nslots saved mv (symStToX64 st) =
                some (asmX64List c1, symStToX64 st1) := by
              rw [← hm, hmv]; rfl
            rw [hmx]; dsimp only
            exact pmoveAux_eq nslots saved hs fuel st1 (hd :: tl) (mv :: acc) hno1
      | none =>
        dsimp only
        split
        · rename_i sa2 d h2l
          refine Eq.symm ?_
          split
          · rename_i sa2' d' h2r
            have hd : d = d' := eq_of_heq (heq_some_gpr_eq rfl rfl rfl (by
              refine find_bridge h2l h2r rfl rfl rfl ?_ ?_ ?_ ?_ ?_ <;>
                (intros; first | exact HEq.rfl | rfl | (dsimp only; split <;> rfl))))
            subst hd
            refine Eq.symm ?_
            rw [vllR_scratch_eq]
            have hft :
                @List.find? vllX64IsaR.Reg
                  (fun tmp => !(Rega.locBlocked x64Isa (symStToX64 st) (hd :: tl) (.gpr tmp)))
                  x64Isa.frame.scratch =
                @List.find? x64Isa.Reg
                  (fun tmp => !(Rega.locBlocked x64Isa (symStToX64 st) (hd :: tl) (.gpr tmp)))
                  x64Isa.frame.scratch := rfl
            rw [hft]
            cases @List.find? x64Isa.Reg
                (fun tmp => !(Rega.locBlocked x64Isa (symStToX64 st) (hd :: tl) (.gpr tmp)))
                x64Isa.frame.scratch with
            | some tmp =>
              dsimp only
              let mv : Move Reg64 RegMm CondCode := .mov tmp d
              obtain ⟨hm, hp⟩ := execMove_eq_and_noRsp hs mv st hno
              cases hmv : Rega.execMove vllX64IsaR nslots saved mv st with
              | none =>
                have hmx : Rega.execMove x64Isa nslots saved mv (symStToX64 st) = none := by
                  rw [← hm, hmv]; rfl
                rw [hmx]
              | some p0 =>
                rcases p0 with ⟨c1, st1⟩
                obtain ⟨hno1, _⟩ := hp c1 st1 hmv
                have hmx : Rega.execMove x64Isa nslots saved mv (symStToX64 st) =
                    some (asmX64List c1, symStToX64 st1) := by
                  rw [← hm, hmv]; rfl
                rw [hmx]; dsimp only
                exact pmoveAux_eq nslots saved hs fuel st1 (hd :: tl) (mv :: acc) hno1
            | none =>
              dsimp only
              rw [findFreeSlot_eq]
              cases Rega.findFreeSlot x64Isa nslots (symStToX64 st) (hd :: tl) 1 with
              | none => dsimp only
              | some sl =>
                dsimp only
                rw [list_contains_decEq_congr vllX64IsaR.decEqReg x64Isa.decEqReg _ d]
                split
                · let mv : Move Reg64 RegMm CondCode := .st sl d
                  obtain ⟨hm, hp⟩ := execMove_eq_and_noRsp hs mv st hno
                  cases hmv : Rega.execMove vllX64IsaR nslots saved mv st with
                  | none =>
                    have hmx : Rega.execMove x64Isa nslots saved mv (symStToX64 st) = none := by
                      rw [← hm, hmv]; rfl
                    rw [hmx]
                  | some p0 =>
                    rcases p0 with ⟨c1, st1⟩
                    obtain ⟨hno1, _⟩ := hp c1 st1 hmv
                    have hmx : Rega.execMove x64Isa nslots saved mv (symStToX64 st) =
                        some (asmX64List c1, symStToX64 st1) := by
                      rw [← hm, hmv]; rfl
                    rw [hmx]; dsimp only
                    exact pmoveAux_eq nslots saved hs fuel st1 (hd :: tl) (mv :: acc) hno1
                · rfl
          · rename_i xR h2ne
            exact False.elim (by
              refine find_absurd h2l (h2ne sa2 d) rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ <;>
                (intros; first | exact HEq.rfl | rfl | (dsimp only; split <;> rfl)))
        · rename_i xL h2ne
          refine Eq.symm ?_
          split
          · rename_i sa2' d' h2r
            exact False.elim (by
              refine find_absurd h2r (h2ne sa2' d') rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ <;>
                (intros; first | exact HEq.rfl | rfl | (dsimp only; split <;> rfl)))
          · refine Eq.symm ?_
            split
            · rename_i sa3 vd h3l
              refine Eq.symm ?_
              split
              · rename_i sa3' vd' h3r
                have hvd : vd = vd' := eq_of_heq (heq_some_vec_eq rfl rfl rfl (by
                  refine find_bridge h3l h3r rfl rfl rfl ?_ ?_ ?_ ?_ ?_ <;>
                    (intros; first | exact HEq.rfl | rfl | (dsimp only; split <;> rfl))))
                subst hvd
                refine Eq.symm ?_
                rw [vllR_vecScratch_eq, vecWidthAt_eq]
                have hfv :
                    @List.find? vllX64IsaR.VReg
                      (fun vtmp => !(Rega.locBlocked x64Isa (symStToX64 st) (hd :: tl)
                        (.vec vtmp))) x64Isa.vec.vecScratch =
                    @List.find? x64Isa.VReg
                      (fun vtmp => !(Rega.locBlocked x64Isa (symStToX64 st) (hd :: tl)
                        (.vec vtmp))) x64Isa.vec.vecScratch := rfl
                rw [hfv]
                cases @List.find? x64Isa.VReg
                    (fun vtmp => !(Rega.locBlocked x64Isa (symStToX64 st) (hd :: tl)
                      (.vec vtmp))) x64Isa.vec.vecScratch with
                | some vtmp =>
                  dsimp only
                  let mv : Move Reg64 RegMm CondCode :=
                    .vmov (Rega.vecWidthAt x64Isa (symStToX64 st) vd) vtmp vd
                  obtain ⟨hm, hp⟩ := execMove_eq_and_noRsp hs mv st hno
                  cases hmv : Rega.execMove vllX64IsaR nslots saved mv st with
                  | none =>
                    have hmx : Rega.execMove x64Isa nslots saved mv (symStToX64 st) = none := by
                      rw [← hm, hmv]; rfl
                    rw [hmx]
                  | some p0 =>
                    rcases p0 with ⟨c1, st1⟩
                    obtain ⟨hno1, _⟩ := hp c1 st1 hmv
                    have hmx : Rega.execMove x64Isa nslots saved mv (symStToX64 st) =
                        some (asmX64List c1, symStToX64 st1) := by
                      rw [← hm, hmv]; rfl
                    rw [hmx]; dsimp only
                    exact pmoveAux_eq nslots saved hs fuel st1 (hd :: tl) (mv :: acc) hno1
                | none =>
                  dsimp only
                  rw [findFreeSlot_eq]
                  cases Rega.findFreeSlot x64Isa nslots (symStToX64 st) (hd :: tl)
                      (Rega.vecWidthAt x64Isa (symStToX64 st) vd).slots with
                  | none => dsimp only
                  | some sl =>
                    dsimp only
                    rw [list_contains_decEq_congr vllX64IsaR.decEqVReg x64Isa.decEqVReg _ vd]
                    split
                    · let mv : Move Reg64 RegMm CondCode :=
                        .vst (Rega.vecWidthAt x64Isa (symStToX64 st) vd) sl vd
                      obtain ⟨hm, hp⟩ := execMove_eq_and_noRsp hs mv st hno
                      cases hmv : Rega.execMove vllX64IsaR nslots saved mv st with
                      | none =>
                        have hmx :
                            Rega.execMove x64Isa nslots saved mv (symStToX64 st) = none := by
                          rw [← hm, hmv]; rfl
                        rw [hmx]
                      | some p0 =>
                        rcases p0 with ⟨c1, st1⟩
                        obtain ⟨hno1, _⟩ := hp c1 st1 hmv
                        have hmx : Rega.execMove x64Isa nslots saved mv (symStToX64 st) =
                            some (asmX64List c1, symStToX64 st1) := by
                          rw [← hm, hmv]; rfl
                        rw [hmx]; dsimp only
                        exact pmoveAux_eq nslots saved hs fuel st1 (hd :: tl) (mv :: acc) hno1
                    · rfl
              · rename_i xR3 h3ne
                exact False.elim (by
                  refine find_absurd h3l (h3ne sa3 vd) rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ <;>
                    (intros; first | exact HEq.rfl | rfl | (dsimp only; split <;> rfl)))
            · rename_i xL3 h3ne
              refine Eq.symm ?_
              split
              · rename_i sa3' vd' h3r
                exact False.elim (by
                  refine find_absurd h3r (h3ne sa3' vd') rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ <;>
                    (intros; first | exact HEq.rfl | rfl | (dsimp only; split <;> rfl)))
              · refine Eq.symm ?_
                dsimp only [List.head?]
                rw [moveFor_eq]
                cases Rega.moveFor x64Isa nslots (symStToX64 st) hd.1 hd.2 with
                | none => dsimp only
                | some mv =>
                  dsimp only
                  obtain ⟨hm, hp⟩ := execMove_eq_and_noRsp hs mv st hno
                  cases hmv : Rega.execMove vllX64IsaR nslots saved mv st with
                  | none =>
                    have hmx : Rega.execMove x64Isa nslots saved mv (symStToX64 st) = none := by
                      rw [← hm, hmv]; rfl
                    rw [hmx]
                  | some p0 =>
                    rcases p0 with ⟨c1, st1⟩
                    obtain ⟨hno1, _⟩ := hp c1 st1 hmv
                    have hmx : Rega.execMove x64Isa nslots saved mv (symStToX64 st) =
                        some (asmX64List c1, symStToX64 st1) := by
                      rw [← hm, hmv]; rfl
                    rw [hmx]; dsimp only
                    exact pmoveAux_eq nslots saved hs fuel st1 (hd :: tl) (mv :: acc) hno1

theorem shuffle_eq_and_noRsp {nslots : Nat} {saved : List Reg64}
    (hs : savedNoRsp saved = true) (st : Rega.SymState vllX64IsaR)
    (tgts : List (SymArg × vllX64IsaR.Loc)) (hno : regsNoRsp st.regs = true) :
    mapOptSt (Rega.shuffle vllX64IsaR nslots saved st tgts) =
      Rega.shuffle x64Isa nslots saved (symStToX64 st) tgts ∧
    (∀ c0 st', Rega.shuffle vllX64IsaR nslots saved st tgts = some (c0, st') →
      regsNoRsp st'.regs = true ∧ (asmX64List c0 = [] → c0 = [])) := by
  dsimp only [Rega.shuffle]
  have h0 : (tgts.all fun (sa, loc) => Rega.holdsLoc vllX64IsaR st sa loc) =
      (tgts.all fun (sa, loc) => Rega.holdsLoc x64Isa (symStToX64 st) sa loc) :=
    list_all_congr (fun ⟨sa, loc⟩ => holdsLoc_eq st sa loc) tgts
  rw [h0]
  split
  · simp only [mapOptSt, Option.map_some, symStToX64]
    exact ⟨rfl, fun _ _ h => by cases h; exact ⟨hno, fun _ => rfl⟩⟩
  · rw [pmoveAux_eq nslots saved hs (2 * tgts.length + 4) st tgts [] hno]
    let mvs := Rega.pmoveAux x64Isa nslots saved (2 * tgts.length + 4) (symStToX64 st) tgts []
    obtain ⟨hm, hp⟩ := execMoves_eq_and_noRsp hs mvs st hno
    cases h1 : Rega.execMoves vllX64IsaR nslots saved mvs st with
    | none =>
      have h1x : Rega.execMoves x64Isa nslots saved mvs (symStToX64 st) = none := by
        rw [← hm, h1]; rfl
      rw [h1x]
      exact ⟨rfl, fun _ _ h => by cases h⟩
    | some p1 =>
      rcases p1 with ⟨c1, st1⟩
      obtain ⟨hno1, hnil1⟩ := hp c1 st1 h1
      have h1x : Rega.execMoves x64Isa nslots saved mvs (symStToX64 st) =
          some (asmX64List c1, symStToX64 st1) := by
        rw [← hm, h1]; rfl
      dsimp only
      rw [h1x]
      dsimp only
      have h1_all : (tgts.all fun (sa, loc) => Rega.holdsLoc vllX64IsaR st1 sa loc) =
          (tgts.all fun (sa, loc) => Rega.holdsLoc x64Isa (symStToX64 st1) sa loc) :=
        list_all_congr (fun ⟨sa, loc⟩ => holdsLoc_eq st1 sa loc) tgts
      rw [h1_all]
      split
      · simp only [mapOptSt, Option.map_some]
        exact ⟨trivial, fun _ _ h => by cases h; exact ⟨hno1, hnil1⟩⟩
      · exact ⟨rfl, fun _ _ h => by cases h⟩

theorem canonAbiCode_eq :
    ∀ {ts : List Ty} (locs : Tup (AbiReg Reg64 RegMm) ts) (sk : List Bool),
      asmX64List (Rega.canonAbiCode vllX64IsaR locs sk) = Rega.canonAbiCode x64Isa locs sk
  | [], (), _ => rfl
  | t :: _, (.gpr r, locs), sk => by
    dsimp only [Rega.canonAbiCode]
    rw [asmX64List_append, canonAbiCode_eq locs sk.tail]
    split
    · rfl
    · rw [vllR_canonAbi_eq]
  | _ :: _, (.vec _, locs), sk => by
    dsimp only [Rega.canonAbiCode]; exact canonAbiCode_eq locs sk.tail

private theorem saveCsList_eq (base : Nat) :
    ∀ (rs : List Reg64),
      asmX64List (Rega.saveCsList vllX64IsaR base rs) = Rega.saveCsList x64Isa base rs
  | [] => rfl
  | r :: rs => by
    dsimp only [Rega.saveCsList]
    rw [asmX64List_append, vllR_slotSt_eq, saveCsList_eq (base + 1) rs]

private theorem restoreCsList_eq (base : Nat) :
    ∀ (rs : List Reg64),
      asmX64List (Rega.restoreCsList vllX64IsaR base rs) = Rega.restoreCsList x64Isa base rs
  | [] => rfl
  | r :: rs => by
    dsimp only [Rega.restoreCsList]
    rw [asmX64List_append, vllR_slotLd_eq, restoreCsList_eq (base + 1) rs]

theorem saveCs_eq (base : Nat) (rs : List Reg64) :
    asmX64List (Rega.saveCs vllX64IsaR base rs) = Rega.saveCs x64Isa base rs := by
  cases rs with
  | nil => rfl
  | cons _ _ => dsimp only [Rega.saveCs]; rw [vllR_saveRegs_eq]; exact saveCsList_eq base _

theorem restoreCs_eq (base : Nat) (rs : List Reg64) :
    asmX64List (Rega.restoreCs vllX64IsaR base rs) = Rega.restoreCs x64Isa base rs := by
  cases rs with
  | nil => rfl
  | cons _ _ => dsimp only [Rega.restoreCs]; rw [vllR_restoreRegs_eq]; exact restoreCsList_eq base _

/-! ## 2b1. `opNoSameExt` Closure, `mapOptCl` Toolkit, and `lowerOp` Parity -/

mutual
/-- Inductive `opNoSameExt` invariant over PHOAS `Expr` (independent of `nv`/`nl` re-indexing). -/
inductive ExprNoSameExt : {rs : List Ty} → Expr Rega.VNat Rega.LNat rs → Prop where
  | let_ {rs ts : List Ty} {op : Op Rega.VNat ts}
      {k : Tup Rega.VNat ts → Expr Rega.VNat Rega.LNat rs} :
      opNoSameExt op.code = true → (∀ xs, ExprNoSameExt (k xs)) → ExprNoSameExt (.let_ op k)
  | load {rs : List Ty} {t : Ty} {a : Arg Rega.VNat i64}
      {k : Nat → Expr Rega.VNat Rega.LNat rs} :
      (∀ x, ExprNoSameExt (k x)) → ExprNoSameExt (.load t a k)
  | store {rs : List Ty} {t : Ty} {v : Arg Rega.VNat t} {a : Arg Rega.VNat i64}
      {k : Expr Rega.VNat Rega.LNat rs} :
      ExprNoSameExt k → ExprNoSameExt (.store v a k)
  | call {rs as : List Ty} {f : Sym} {bs : List Ty} {args : Tup (Arg Rega.VNat) as}
      {k : Tup Rega.VNat bs → Expr Rega.VNat Rega.LNat rs} :
      (∀ xs, ExprNoSameExt (k xs)) → ExprNoSameExt (.call f args k)
  | jnz {rs : List Ty} {c : Arg Rega.VNat .bool} {t e : Expr Rega.VNat Rega.LNat rs} :
      ExprNoSameExt t → ExprNoSameExt e → ExprNoSameExt (.jnz c t e)
  | jump {rs ts : List Ty} {j : Nat} {args : Tup (Arg Rega.VNat) ts} :
      ExprNoSameExt (.jump j args)
  | ret {rs : List Ty} {vs : Tup (Arg Rega.VNat) rs} : ExprNoSameExt (.ret vs)
  | exit {rs as : List Ty} {f : Sym} {args : Tup (Arg Rega.VNat) as} :
      ExprNoSameExt (.exit f args)
  | hlt {rs : List Ty} : ExprNoSameExt (.hlt (rs := rs))
  | group {rs : List Ty} {sig : List (List Ty)}
      {bodies : Tup Rega.LNat sig → Blocks Rega.VNat Rega.LNat rs sig}
      {k : Tup Rega.LNat sig → Expr Rega.VNat Rega.LNat rs} :
      (∀ ls, BlocksNoSameExt (bodies ls)) → (∀ ls, ExprNoSameExt (k ls)) →
      ExprNoSameExt (.group bodies k)

/-- Block-list companion of `ExprNoSameExt`. -/
inductive BlocksNoSameExt :
    {rs : List Ty} → {sig : List (List Ty)} → Blocks Rega.VNat Rega.LNat rs sig → Prop where
  | nil {rs : List Ty} : BlocksNoSameExt (.nil (rs := rs))
  | cons {rs ts : List Ty} {sig : List (List Ty)}
      {b : Tup Rega.VNat ts → Expr Rega.VNat Rega.LNat rs}
      {bs : Blocks Rega.VNat Rega.LNat rs sig} :
      (∀ xs, ExprNoSameExt (b xs)) → BlocksNoSameExt bs → BlocksNoSameExt (.cons b bs)
end

theorem x64AddrValid_baseIdxDisp {rb ri : Reg64} {sc : AddrScale} {d : Int64} (h : ri ≠ .rsp) :
    x64AddrValid (.baseIdxDisp rb ri sc d) = true := by
  cases ri <;> first | exact absurd rfl h | rfl

theorem vllR_sp_eq : vllX64FrameR.sp = x64Isa.frame.sp := rfl
theorem vllR_spAddr_eq (idx : Nat) : Rega.spAddr vllX64IsaR idx = Rega.spAddr x64Isa idx := rfl
theorem vllR_isGprTy_eq (t : Ty) : Rega.isGprTy vllX64IsaR t = Rega.isGprTy x64Isa t := by
  cases t <;> rfl
theorem vllR_vecWidth?_eq (t : Ty) : Rega.vecWidth? vllX64IsaR t = Rega.vecWidth? x64Isa t := by
  cases t <;> rfl
theorem vllR_toSymArg_eq {t : Ty} (a : Arg Rega.VNat t) :
    Rega.toSymArg vllX64IsaR t a = Rega.toSymArg x64Isa t a := by
  cases t <;> cases a <;> rfl
theorem vllR_elideZext32_eq : vllX64GprR.elideZext32 = x64Isa.gpr.elideZext32 := rfl
theorem vllR_zeroUpper32Op_eq {sig rs : List Ty} (code : OpCode sig rs)
    (pas : Tup (PArg Reg64 RegMm CondCode) sig) (dsts : Tup (PDst Reg64 RegMm CondCode) rs) :
    vllX64GprR.zeroUpper32Op code pas dsts = x64Isa.gpr.zeroUpper32Op code pas dsts := rfl
theorem vllR_zeroUpper32Load_eq : vllX64GprR.zeroUpper32Load = x64Isa.gpr.zeroUpper32Load := rfl
theorem vllR_zeroExtLoad_eq : vllX64GprR.zeroExtLoad = x64Isa.gpr.zeroExtLoad := rfl
theorem vllR_zeroUpper32AluMem_eq :
    vllX64GprR.zeroUpper32AluMem = x64Isa.gpr.zeroUpper32AluMem := rfl
theorem vllR_zeroUpper32LeaArith_eq :
    vllX64GprR.zeroUpper32LeaArith = x64Isa.gpr.zeroUpper32LeaArith := rfl
theorem vllR_hasTestFlags_eq : vllX64GprR.hasTestFlags = x64Isa.gpr.hasTestFlags := rfl
theorem vllR_cmpFlagsOut?_eq : vllX64GprR.cmpFlagsOut? = x64Isa.gpr.cmpFlagsOut? := rfl
theorem vllR_cmpMemFlagsOut?_eq :
    vllX64GprR.cmpMemFlagsOut? = x64Isa.gpr.cmpMemFlagsOut? := rfl
theorem vllR_boolFlagOut?_eq {sig : List Ty} (c : OpCode sig [.bool])
    (pas : Tup (PArg Reg64 RegMm CondCode) sig) (pd : PDst Reg64 RegMm CondCode .bool) :
    vllX64GprR.boolFlagOut? c pas pd = x64Isa.gpr.boolFlagOut? c pas pd := rfl
theorem vllR_aluZeroOut?_eq (w : Nat) {sig : List Ty} (c : OpCode sig [.bits w])
    (pd : PDst Reg64 RegMm CondCode (.bits w)) :
    vllX64GprR.aluZeroOut? w c pd = x64Isa.gpr.aluZeroOut? w c pd := rfl
theorem vllR_negCond_eq : vllX64GprR.negCond = x64Isa.gpr.negCond := rfl
theorem vllR_cmpZeroJcc_eq (co : CmpOp) (w : Nat) (r : Reg64) (l : Sym) :
    vllX64GprR.cmpZeroJcc co w r l = none := rfl
theorem vllR_testJcc_eq (neg : Bool) (w : Nat) (r : Reg64) (m : BitVec w) (l : Sym) :
    vllX64GprR.testJcc neg w r m l = none := rfl
theorem vllR_loadZextIdx_none (t : Ty) (rd rb ri : Reg64) (sc : AddrScale) (d : Int64) :
    vllX64GprR.loadZextIdx t rd rb ri sc d = none := rfl
theorem x64_loadZextIdx_none (t : Ty) (rd rb ri : Reg64) (sc : AddrScale) (d : Int64) :
    x64Isa.gpr.loadZextIdx t rd rb ri sc d = none := rfl
theorem vllR_loadSextZextIdx_none (m n : Nat) (rd rb ri : Reg64) (sc : AddrScale) (d : Int64) :
    vllX64GprR.loadSextZextIdx m n rd rb ri sc d = none := rfl
theorem x64_loadSextZextIdx_none (m n : Nat) (rd rb ri : Reg64) (sc : AddrScale) (d : Int64) :
    x64Isa.gpr.loadSextZextIdx m n rd rb ri sc d = none := rfl
theorem vllR_storeZextIdx_none (t : Ty) (pa : PArg Reg64 RegMm CondCode t)
    (rb ri : Reg64) (sc : AddrScale) (d : Int64) :
    vllX64GprR.storeZextIdx t pa rb ri sc d = none := rfl
theorem x64_storeZextIdx_none (t : Ty) (pa : PArg Reg64 RegMm CondCode t)
    (rb ri : Reg64) (sc : AddrScale) (d : Int64) :
    x64Isa.gpr.storeZextIdx t pa rb ri sc d = none := rfl
theorem vllR_leaArithZext_none (rb? : Option Reg64) (ri : Reg64) (sh : Nat)
    (d : Int64) (rd : Reg64) :
    vllX64GprR.leaArithZext rb? ri sh d rd = none := rfl
theorem x64_leaArithZext_none (rb? : Option Reg64) (ri : Reg64) (sh : Nat)
    (d : Int64) (rd : Reg64) :
    x64Isa.gpr.leaArithZext rb? ri sh d rd = none := rfl
theorem vllR_supportsTestFuse_eq : vllX64IsaR.supportsTestFuse = x64Isa.supportsTestFuse := rfl
theorem vllR_leafZeroFrame_eq : vllX64FrameR.leafZeroFrame = x64Isa.frame.leafZeroFrame := rfl
theorem vllR_frameSize_eq : vllX64FrameR.frameSize = x64Isa.frame.frameSize := rfl

theorem vllR_jnzGprInv_some_eq :
    vllX64GprR.jnzGprInv? = some vllX64JnzGprInv := rfl

theorem x64_jnzGprInv_some_eq :
    x64Isa.gpr.jnzGprInv? = some x64JnzGpr := rfl

theorem vllR_cmpZeroJcc_none_x64 (co : CmpOp) (w : Nat) (r : Reg64) (l : Sym) :
    x64Isa.gpr.cmpZeroJcc co w r l = none := rfl

theorem vllR_testJcc_none_x64 (neg : Bool) (w : Nat) (r : Reg64) (m : BitVec w) (l : Sym) :
    x64Isa.gpr.testJcc neg w r m l = none := rfl

private theorem option_bind_const_none {α β : Type} :
    ∀ o : Option α, o.bind (fun _ => (none : Option β)) = none
  | none | some _ => rfl

theorem vllR_tryAddrZext_none (st : Rega.SymState vllX64IsaR) {α : Type}
    (a : Arg Rega.VNat i64) :
    Rega.tryAddrZext vllX64IsaR st a (fun _ _ _ _ => (none : Option α)) = none := by
  dsimp only [Rega.tryAddrZext]
  cases a with
  | imm _ => rfl
  | var x =>
    dsimp only
    cases st.defs.find? x with
    | none => rfl
    | some df =>
      cases df with
      | addrSum b idx sh d =>
        dsimp only
        cases Rega.zextAddrSumVar? st.defs b idx sh with
        | none => rfl
        | some p => dsimp only; simp only [option_bind_const_none]
      | _ => rfl

theorem x64_tryAddrZext_none (st : Rega.SymState x64Isa) {α : Type}
    (a : Arg Rega.VNat i64) :
    Rega.tryAddrZext x64Isa st a (fun _ _ _ _ => (none : Option α)) = none := by
  dsimp only [Rega.tryAddrZext]
  cases a with
  | imm _ => rfl
  | var x =>
    dsimp only
    cases st.defs.find? x with
    | none => rfl
    | some df =>
      cases df with
      | addrSum b idx sh d =>
        dsimp only
        cases Rega.zextAddrSumVar? st.defs b idx sh with
        | none => rfl
        | some p => dsimp only; simp only [option_bind_const_none]
      | _ => rfl

theorem vllR_tryLeaArithZext_none (st : Rega.SymState vllX64IsaR) {sig ts : List Ty}
    (code : OpCode sig ts) (args : Tup (Arg Rega.VNat) sig)
    (dsts : Tup (PDst Reg64 RegMm CondCode) ts) :
    Rega.tryLeaArithZext vllX64IsaR st code args dsts = none := by
  dsimp only [Rega.tryLeaArithZext]
  split
  · cases Rega.extractLeaZext64 st.defs _ args with
    | none => rfl
    | some _ =>
      simp only [vllR_leaArithZext_none, Option.map_none, option_bind_const_none]
  · rfl

theorem x64_tryLeaArithZext_none (st : Rega.SymState x64Isa) {sig ts : List Ty}
    (code : OpCode sig ts) (args : Tup (Arg Rega.VNat) sig)
    (dsts : Tup (PDst Reg64 RegMm CondCode) ts) :
    Rega.tryLeaArithZext x64Isa st code args dsts = none := by
  dsimp only [Rega.tryLeaArithZext]
  split
  · cases Rega.extractLeaZext64 st.defs _ args with
    | none => rfl
    | some _ =>
      have hlz : ∀ (rb? : Option Reg64) (ri : Reg64) (sh : Nat) (d : Int64) (rd : Reg64),
          x64Isa.gpr.leaArithZext rb? ri sh d rd = none := x64_leaArithZext_none
      dsimp only [x64Isa] at hlz ⊢
      simp only [hlz, Option.map_none, option_bind_const_none]
  · rfl

@[expose] def mapOptCl {α : Type} :
    Option (List (Instr x64Arch) × α) → Option (List _root_.Directive × α) :=
  Option.map fun (c0, x) => (asmX64List c0, x)

theorem mapOptCl_none {α : Type} : mapOptCl (α := α) none = none := rfl

theorem mapOptCl_some {α : Type} (c : List (Instr x64Arch)) (a : α) :
    mapOptCl (some (c, a)) = some (asmX64List c, a) := rfl

theorem mapOptCl_or {α : Type} (a b : Option (List (Instr x64Arch) × α)) :
    mapOptCl (a <|> b) = (mapOptCl a <|> mapOptCl b) := by
  cases a <;> rfl

theorem mapOptCl_or_congr {α : Type} {a : Option (List (Instr x64Arch) × α)}
    {a' : Option (List _root_.Directive × α)} {b : Option (List (Instr x64Arch) × α)}
    {b' : Option (List _root_.Directive × α)}
    (ha : mapOptCl a = a') (hb : mapOptCl b = b') :
    mapOptCl (a <|> b) = (a' <|> b') := by
  cases a with
  | none => subst ha; exact hb
  | some p => rw [← ha]; rfl

theorem mapOptCl_map {α β : Type} (f : α → β) (a : Option (List (Instr x64Arch) × α)) :
    mapOptCl (a.map fun (c, x) => (c, f x)) = (mapOptCl a).map fun (d, x) => (d, f x) := by
  cases a <;> rfl

theorem mapOptCl_bind {α β : Type} (o : Option β) (f : β → Option (List (Instr x64Arch) × α)) :
    mapOptCl (o.bind f) = o.bind (fun x => mapOptCl (f x)) := by
  cases o <;> rfl

theorem mapOptCl_findSome? {α β : Type} (f : β → Option (List (Instr x64Arch) × α)) :
    ∀ (xs : List β), mapOptCl (xs.findSome? f) = xs.findSome? (fun x => mapOptCl (f x))
  | [] => rfl
  | x :: xs => by
    dsimp only [List.findSome?]
    cases hfx : f x with
    | none => simp only [mapOptCl_none]; exact mapOptCl_findSome? f xs
    | some p => rfl

theorem mapOptCl_tryFlag {α : Type} (R : List (SymArg × Rega.RegLoc Reg64 RegMm CondCode))
    (pref : List CondCode) (sa : SymArg) {k₁ : CondCode → Option (List (Instr x64Arch) × α)}
    {k₂ : CondCode → Option (List _root_.Directive × α)} (hk : ∀ cd, mapOptCl (k₁ cd) = k₂ cd) :
    mapOptCl (Rega.tryFlag vllX64IsaR R pref sa k₁) = Rega.tryFlag x64Isa R pref sa k₂ := by
  dsimp only [Rega.tryFlag]
  refine mapOptCl_or_congr ?_ ?_
  · rw [mapOptCl_findSome?]
    refine list_findSome_congr (fun cd => ?_) pref
    rw [list_any_congr (fun p => congrArg (_ && ·) (regLocEq_eq p.2 (.flag cd))) R]
    split
    · exact hk cd
    · rfl
  · rw [mapOptCl_findSome?]
    refine list_findSome_congr (fun ⟨sa', rl⟩ => ?_) R
    cases rl with
    | gpr _ | gprZ _ | vec _ => rfl
    | flag cd =>
      dsimp only; split
      · exact hk cd
      · rfl

theorem mapOptCl_tryGpr {α : Type} (R : List (SymArg × Rega.RegLoc Reg64 RegMm CondCode))
    (sa : SymArg) {k₁ : Reg64 → Option (List (Instr x64Arch) × α)}
    {k₂ : Reg64 → Option (List _root_.Directive × α)} (hk : ∀ r, mapOptCl (k₁ r) = k₂ r) :
    mapOptCl (Rega.tryGpr vllX64IsaR R sa k₁) = Rega.tryGpr x64Isa R sa k₂ := by
  dsimp only [Rega.tryGpr]
  rw [mapOptCl_findSome?]
  refine list_findSome_congr (fun ⟨sa', rl⟩ => ?_) R
  cases rl with
  | vec _ | flag _ => rfl
  | gpr r | gprZ r =>
    dsimp only
    rw [list_contains_decEq_congr vllX64IsaR.decEqReg x64Isa.decEqReg, vllR_scratch_eq]
    split
    · exact hk r
    · rfl

theorem mapOptCl_tryVec {α : Type} (R : List (SymArg × Rega.RegLoc Reg64 RegMm CondCode))
    (sa : SymArg) {k₁ : RegMm → Option (List (Instr x64Arch) × α)}
    {k₂ : RegMm → Option (List _root_.Directive × α)} (hk : ∀ v, mapOptCl (k₁ v) = k₂ v) :
    mapOptCl (Rega.tryVec vllX64IsaR R sa k₁) = Rega.tryVec x64Isa R sa k₂ := by
  dsimp only [Rega.tryVec]
  rw [mapOptCl_findSome?]
  refine list_findSome_congr (fun ⟨sa', rl⟩ => ?_) R
  cases rl with
  | gpr _ | gprZ _ | flag _ => rfl
  | vec v =>
    dsimp only
    rw [list_contains_decEq_congr vllX64IsaR.decEqVReg x64Isa.decEqVReg, vllR_vecScratch_eq]
    split
    · exact hk v
    · rfl

theorem mapOptCl_tryArg {α : Type} (st : Rega.SymState vllX64IsaR) (pref : List CondCode)
    (t : Ty) (a : Arg Rega.VNat t)
    {k₁ : PArg Reg64 RegMm CondCode t → Option (List (Instr x64Arch) × α)}
    {k₂ : PArg Reg64 RegMm CondCode t → Option (List _root_.Directive × α)}
    (hk : ∀ pa, mapOptCl (k₁ pa) = k₂ pa) :
    mapOptCl (Rega.tryArg vllX64IsaR st pref t a k₁) =
      Rega.tryArg x64Isa (symStToX64 st) pref t a k₂ := by
  cases t with
  | bool =>
    cases a with
    | var _ =>
      dsimp only [Rega.tryArg, symStToX64]
      exact mapOptCl_or_congr (mapOptCl_tryFlag _ _ _ fun cd => hk (.flag cd))
        (mapOptCl_tryGpr _ _ fun r => hk (.gpr r))
    | imm _ =>
      dsimp only [Rega.tryArg, symStToX64]
      exact mapOptCl_or_congr (mapOptCl_tryFlag _ _ _ fun cd => hk (.flag cd))
        (mapOptCl_or_congr (hk (.imm _)) (mapOptCl_tryGpr _ _ fun r => hk (.gpr r)))
  | bits _ =>
    cases a with
    | var _ =>
      dsimp only [Rega.tryArg, symStToX64]
      exact mapOptCl_tryGpr _ _ fun r => hk (.gpr r)
    | imm _ =>
      dsimp only [Rega.tryArg, symStToX64]
      refine mapOptCl_or_congr (hk (.imm _)) ?_
      split
      · exact mapOptCl_tryGpr _ _ fun r => hk (.gpr r)
      · rfl
  | float _ => cases a <;> rfl
  | pair _ _ =>
    cases a with
    | var _ =>
      dsimp only [Rega.tryArg, symStToX64]
      exact mapOptCl_tryVec _ _ fun v => hk (.vec v)
    | imm _ =>
      dsimp only [Rega.tryArg, symStToX64]
      refine mapOptCl_or_congr (hk (.imm _)) ?_
      rw [vllR_vecWidth?_eq]
      cases Rega.vecWidth? x64Isa _ with
      | none => rfl
      | some _ => dsimp only; exact mapOptCl_tryVec _ _ fun v => hk (.vec v)

theorem mapOptCl_pickPArgs {α : Type} (st : Rega.SymState vllX64IsaR) (pref : List CondCode) :
    ∀ {sig : List Ty} (args : Tup (Arg Rega.VNat) sig)
      {k₁ : Tup (PArg Reg64 RegMm CondCode) sig → Option (List (Instr x64Arch) × α)}
      {k₂ : Tup (PArg Reg64 RegMm CondCode) sig → Option (List _root_.Directive × α)},
      (∀ pas, mapOptCl (k₁ pas) = k₂ pas) →
      mapOptCl (Rega.pickPArgs vllX64IsaR st pref args k₁) =
        Rega.pickPArgs x64Isa (symStToX64 st) pref args k₂
  | [], (), _, _, hk => hk ()
  | t :: ts, (a, as), k₁, k₂, hk => by
    dsimp only [Rega.pickPArgs]
    exact mapOptCl_tryArg st pref t a (fun pa =>
      mapOptCl_pickPArgs st pref as (fun pas => hk (pa, pas)))

theorem mapOptCl_tryAddr {α : Type} (st : Rega.SymState vllX64IsaR) (vh : VariantHint)
    (a : Arg Rega.VNat i64) (hno : regsNoRsp st.regs = true)
    {k₁ : AddrArg Reg64 → Option (List (Instr x64Arch) × α)}
    {k₂ : AddrArg Reg64 → Option (List _root_.Directive × α)}
    (hk : ∀ aa, x64AddrValid aa = true → mapOptCl (k₁ aa) = k₂ aa) :
    mapOptCl (Rega.tryAddr vllX64IsaR st vh a k₁) =
      Rega.tryAddr x64Isa (symStToX64 st) vh a k₂ := by
  cases a with
  | imm c =>
    dsimp only [Rega.tryAddr, symStToX64]
    refine mapOptCl_or_congr (hk (.imm c) rfl) ?_
    rw [mapOptCl_bind, findGprFor_eq]
    cases Rega.findGprFor x64Isa true st.regs (.immBits 64 c) with
    | none => rfl
    | some r => exact hk _ rfl
  | var x =>
    dsimp only [Rega.tryAddr, symStToX64]
    have hfold :
        mapOptCl
          (match vh, st.defs.find? x with
           | .disp off, some (.addImm64 base d) =>
             if d == off.toBitVec then
               (Rega.findGprFor vllX64IsaR true st.regs (.var base)).bind fun rb =>
                 k₁ (.baseDisp rb off)
             else none
           | _, _ => none) =
        (match vh, st.defs.find? x with
         | .disp off, some (.addImm64 base d) =>
           if d == off.toBitVec then
             (Rega.findGprFor x64Isa true st.regs (.var base)).bind fun rb =>
               k₂ (.baseDisp rb off)
           else none
         | _, _ => none) := by
      cases vh <;> try rfl
      rename_i off
      cases st.defs.find? x with
      | none => rfl
      | some df =>
        cases df with
        | addImm64 base d =>
          dsimp only; split
          · rw [mapOptCl_bind, findGprFor_eq]
            cases Rega.findGprFor x64Isa true st.regs (.var base) with
            | none => rfl
            | some rb => exact hk _ rfl
          · rfl
        | _ => rfl
    have hvar :
        mapOptCl ((Rega.findGprFor vllX64IsaR true st.regs (.var x)).bind fun rx =>
          k₁ (.baseDisp rx 0)) =
        ((Rega.findGprFor x64Isa true st.regs (.var x)).bind fun rx => k₂ (.baseDisp rx 0)) := by
      rw [mapOptCl_bind, findGprFor_eq]
      cases Rega.findGprFor x64Isa true st.regs (.var x) with
      | none => rfl
      | some rx => exact hk _ rfl
    have hdef :
        mapOptCl
          (match st.defs.find? x with
           | some (.addImm64 base d) =>
             (Rega.findGprFor vllX64IsaR true st.regs (.var base)).bind fun rb =>
               k₁ (.baseDisp rb (Int64.ofBitVec d))
           | some (.addrSum base idx sh d) =>
             (AddrScale.ofShift? sh).bind fun sc =>
               (Rega.findGprFor vllX64IsaR true st.regs (.var base)).bind fun rb =>
                 (Rega.findGprFor vllX64IsaR true st.regs (.var idx)).bind fun ri =>
                   k₁ (.baseIdxDisp rb ri sc (Int64.ofBitVec d))
           | some (.imm64 c) => k₁ (.imm c)
           | _ => none) =
        (match st.defs.find? x with
         | some (.addImm64 base d) =>
           (Rega.findGprFor x64Isa true st.regs (.var base)).bind fun rb =>
             k₂ (.baseDisp rb (Int64.ofBitVec d))
         | some (.addrSum base idx sh d) =>
           (AddrScale.ofShift? sh).bind fun sc =>
             (Rega.findGprFor x64Isa true st.regs (.var base)).bind fun rb =>
               (Rega.findGprFor x64Isa true st.regs (.var idx)).bind fun ri =>
                 k₂ (.baseIdxDisp rb ri sc (Int64.ofBitVec d))
         | some (.imm64 c) => k₂ (.imm c)
         | _ => none) := by
      cases st.defs.find? x with
      | none => rfl
      | some df =>
        cases df with
        | imm64 c => exact hk _ rfl
        | addImm64 base d =>
          dsimp only; rw [mapOptCl_bind, findGprFor_eq]
          cases Rega.findGprFor x64Isa true st.regs (.var base) with
          | none => rfl
          | some rb => exact hk _ rfl
        | addrSum base idx sh d =>
          dsimp only; rw [mapOptCl_bind]
          cases AddrScale.ofShift? sh with
          | none => rfl
          | some sc =>
            change mapOptCl ((Rega.findGprFor vllX64IsaR true st.regs (.var base)).bind _) =
              (Rega.findGprFor x64Isa true st.regs (.var base)).bind _
            rw [mapOptCl_bind, findGprFor_eq]
            cases Rega.findGprFor x64Isa true st.regs (.var base) with
            | none => rfl
            | some rb =>
              change mapOptCl ((Rega.findGprFor vllX64IsaR true st.regs (.var idx)).bind _) =
                (Rega.findGprFor x64Isa true st.regs (.var idx)).bind _
              rw [mapOptCl_bind, findGprFor_eq]
              cases hri : Rega.findGprFor x64Isa true st.regs (.var idx) with
              | none => rfl
              | some ri =>
                have hne := findGprFor_ne_rsp true hno (by rw [findGprFor_eq]; exact hri)
                exact hk _ (x64AddrValid_baseIdxDisp hne)
        | _ => rfl
    exact mapOptCl_or_congr hfold (mapOptCl_or_congr hvar hdef)

@[expose] def dstsNoRsp : {ts : List Ty} → Tup (PDst Reg64 RegMm CondCode) ts → Bool
  | [], () => true
  | _ :: _, (.gpr r, ds) => r != .rsp && dstsNoRsp ds
  | _ :: _, (_, ds) => dstsNoRsp ds

theorem resolveDsts_eq_and_noRsp (h : x64Isa.Hints) (hs : savedNoRsp h.saved = true) :
    ∀ (ts : List Ty) (nv : Nat),
      Rega.resolveDsts vllX64IsaR h ts nv = Rega.resolveDsts x64Isa h ts nv ∧
      (∀ dsts, Rega.resolveDsts vllX64IsaR h ts nv = some dsts → dstsNoRsp dsts = true)
  | [], _ => ⟨rfl, fun _ h0 => by cases h0; rfl⟩
  | t :: ts, nv => by
    dsimp only [Rega.resolveDsts]
    obtain ⟨hrest, hno⟩ := resolveDsts_eq_and_noRsp h hs ts (nv + 1)
    cases hf : h.dest.find? nv with
    | none => exact ⟨rfl, fun _ h0 => by cases h0⟩
    | some loc =>
      cases hres : Rega.resolveDsts x64Isa h ts (nv + 1) with
      | none =>
        have hresv : Rega.resolveDsts vllX64IsaR h ts (nv + 1) = none := hrest.trans hres
        rw [hresv]; cases loc <;> exact ⟨rfl, fun _ h0 => by cases h0⟩
      | some rest =>
        have hresv : Rega.resolveDsts vllX64IsaR h ts (nv + 1) = some rest := hrest.trans hres
        have hrno := hno rest hresv
        rw [hresv]
        cases loc with
        | gpr r =>
          dsimp only
          rw [vllR_isAllocGpr_eq, vllR_isGprTy_eq]
          cases ha : Rega.isAllocGpr x64Isa h.saved r && Rega.isGprTy x64Isa t with
          | false => exact ⟨rfl, fun _ h0 => by cases h0⟩
          | true =>
            have har := (Bool.and_eq_true_iff.mp ha).1
            have hne := isAllocGpr_x64_ne_rsp hs har
            exact ⟨rfl, fun _ h0 => by
              cases h0
              exact Bool.and_eq_true_iff.mpr ⟨reg64_bne_of_ne hne, hrno⟩⟩
        | vec v =>
          dsimp only
          rw [vllR_isAllocVec_eq, vllR_vecWidth?_eq]
          split
          · exact ⟨rfl, fun _ h0 => by cases h0; exact hrno⟩
          · exact ⟨rfl, fun _ h0 => by cases h0⟩
        | flag cd =>
          cases t <;> exact ⟨rfl, fun _ h0 => by cases h0 <;> exact hrno⟩
        | slot _ _ => exact ⟨rfl, fun _ h0 => by cases h0⟩

theorem bindDsts_eq :
    ∀ {ts : List Ty} (dsts : Tup (PDst Reg64 RegMm CondCode) ts) (nv : Nat)
      (acc : List (SymArg × Rega.RegLoc Reg64 RegMm CondCode) × Trie SlotWidth),
      Rega.bindDsts vllX64IsaR dsts nv acc = Rega.bindDsts x64Isa dsts nv acc
  | [], (), _, _ => rfl
  | t :: _, (d, ds), nv, (regs, vw) => by
    cases d with
    | gpr _ | flag _ => exact bindDsts_eq ds (nv + 1) _
    | vec _ =>
      dsimp only [Rega.bindDsts]
      rw [vllR_vecWidth?_eq]
      exact bindDsts_eq ds (nv + 1) _

theorem bindDsts_noRsp :
    ∀ {ts : List Ty} (dsts : Tup (PDst Reg64 RegMm CondCode) ts) (nv : Nat)
      (acc : List (SymArg × Rega.RegLoc Reg64 RegMm CondCode) × Trie SlotWidth),
      dstsNoRsp dsts = true → regsNoRsp acc.1 = true →
      regsNoRsp (Rega.bindDsts vllX64IsaR dsts nv acc).1 = true
  | [], (), _, _, _, hr => hr
  | _ :: _, (d, ds), nv, (regs, vw), hd, hr => by
    dsimp only [Rega.bindDsts]
    cases d with
    | gpr r =>
      simp only [dstsNoRsp, Bool.and_eq_true] at hd
      exact bindDsts_noRsp ds (nv + 1) _ hd.2
        (Bool.and_eq_true_iff.mpr ⟨hd.1, hr⟩)
    | vec _ =>
      exact bindDsts_noRsp ds (nv + 1) _ hd
        (Bool.and_eq_true_iff.mpr ⟨rfl, hr⟩)
    | flag _ =>
      exact bindDsts_noRsp ds (nv + 1) _ hd
        (Bool.and_eq_true_iff.mpr ⟨rfl, hr⟩)

theorem killFlags_eq (cl : FlagMask) (fl : Option Rega.FlagFact) :
    Rega.killFlags vllX64IsaR cl fl = Rega.killFlags x64Isa cl fl := by
  cases fl <;> rfl

theorem elideZext32?_eq (R : List (SymArg × Rega.RegLoc Reg64 RegMm CondCode))
    (z : List Reg64) {sig ts : List Ty} (code : OpCode sig ts) (args : Tup (Arg Rega.VNat) sig)
    (dsts : Tup (PDst Reg64 RegMm CondCode) ts) :
    Rega.elideZext32? vllX64IsaR R z code args dsts =
      Rega.elideZext32? x64Isa R z code args dsts := by
  have hz : ∀ (v : Nat) (r : Reg64),
      Rega.hasVarGprZ vllX64IsaR R v r = Rega.hasVarGprZ x64Isa R v r := fun v r => by
    dsimp only [Rega.hasVarGprZ]
    exact list_any_congr (fun p => by rw [regLocEq_eq]) R
  have hg : ∀ (v : Nat) (r : Reg64),
      Rega.hasVarGpr vllX64IsaR R v r = Rega.hasVarGpr x64Isa R v r := fun v r => by
    dsimp only [Rega.hasVarGpr]
    exact list_any_congr (fun p => by rw [regLocMatchesGpr_eq]) R
  cases code <;> try rfl
  rcases args with ⟨a, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
  cases a <;> cases pd <;> try rfl
  dsimp only [Rega.elideZext32?]
  rw [vllR_elideZext32_eq, list_contains_decEq_congr vllX64IsaR.decEqReg x64Isa.decEqReg, hz, hg]

theorem elideTrunc?_eq (R : List (SymArg × Rega.RegLoc Reg64 RegMm CondCode))
    {sig ts : List Ty} (code : OpCode sig ts) (args : Tup (Arg Rega.VNat) sig)
    (dsts : Tup (PDst Reg64 RegMm CondCode) ts) :
    Rega.elideTrunc? vllX64IsaR R code args dsts = Rega.elideTrunc? x64Isa R code args dsts := by
  have hg : ∀ (v : Nat) (r : Reg64),
      Rega.hasVarGpr vllX64IsaR R v r = Rega.hasVarGpr x64Isa R v r := fun v r => by
    dsimp only [Rega.hasVarGpr]
    exact list_any_congr (fun p => by rw [regLocMatchesGpr_eq]) R
  cases code <;> try rfl
  rcases args with ⟨a, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
  cases a <;> cases pd <;> try rfl
  dsimp only [Rega.elideTrunc?]
  rw [vllR_elideZext32_eq, vllR_zeroUpper32Op_eq, hg]

theorem testBoolExtra?_eq (neg : Bool) (cl : FlagMask)
    (pd : PDst Reg64 RegMm CondCode .bool) :
    Rega.testBoolExtra? vllX64IsaR neg cl pd = Rega.testBoolExtra? x64Isa neg cl pd := by
  dsimp only [Rega.testBoolExtra?]
  rw [vllR_hasTestFlags_eq, vllR_condOfCmp_eq]
  cases pd <;> rfl

theorem cmpMemRes_eq (st : Rega.SymState vllX64IsaR) (co : CmpOp) (w : Nat)
    (lhs rhs : SymArg) (pd : PDst Reg64 RegMm CondCode .bool) (c : List (Instr x64Arch))
    (cl : FlagMask) :
    let r := Rega.cmpMemRes vllX64IsaR st co w lhs rhs pd c cl
    (asmX64List r.1, r.2) =
      Rega.cmpMemRes x64Isa (symStToX64 st) co w lhs rhs pd (asmX64List c) cl := by
  dsimp only [Rega.cmpMemRes, symStToX64]
  rw [vllR_cmpMemFlagsOut?_eq, vllR_condOfCmp_eq, killFlags_eq]
  cases x64Isa.gpr.cmpMemFlagsOut? co pd with
  | none => rfl
  | some _ => cases pd <;> rfl

theorem extCmpMemRes_eq (co : CmpOp) (pd : PDst Reg64 RegMm CondCode .bool)
    (d : List (Instr x64Arch)) (cl : FlagMask) :
    let r := Rega.extCmpMemRes vllX64IsaR co pd d cl
    (asmX64List r.1, r.2) = Rega.extCmpMemRes x64Isa co pd (asmX64List d) cl := by
  dsimp only [Rega.extCmpMemRes]
  rw [vllR_cmpMemFlagsOut?_eq, vllR_condOfCmp_eq]
  cases pd <;> rfl

end LeanQbe.T.Amd64
