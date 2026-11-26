module

public import LeanQbe.T.Vll.FactorX642
public import LeanQbe.T.Vll.AsmX64

/-!
# BedrockMach SysV x86-64 Callback Parity (`Vll.FactorX643`)

Part 1 of the exact `asmX64List` lowering equality proof between `vllX64Isa` (`vllX64Target`) and
`x64Isa` (`x64Target`), factored cleanly so every file stays well below `2,500` LOC:
* 1:1 `asmX64List` callback parity for every `GprIsa`, `VecIsa`, `FrameIsa`, and `Isa` method
  (`gpr.load`/`gpr.store` under `x64AddrValid a = true`, plus unconditional `_of_x64` versions and
  `gpr.op` under `opNoSameExt` / unconditional `vllX64_op_eq_of_x64`).

Zero `Arm64` / `Kraken.AArch64` imports, zero `@[expose]` on proof theorems/lemmas.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Vll

open LeanQbe.T
open LeanQbe.T.Amd64
open Std Std.ExtHashMap

/-! ## 1. 1:1 `asmX64List` Callback Parity (`vllX64Isa` vs `x64Isa`) -/

private theorem reg64_eq_of_beq {r₁ r₂ : Reg64} (h : (r₁ == r₂) = true) : r₁ = r₂ := by
  cases r₁ <;> cases r₂ <;> first | rfl | cases h

private theorem reg64_beq_self (r : Reg64) : (r == r) = true := by
  cases r <;> rfl

private theorem reg64_bne_self (r : Reg64) : (r != r) = false := by
  cases r <;> rfl

private theorem reg64_beq_false_of_ne {r₁ r₂ : Reg64} (h : r₁ ≠ r₂) : (r₁ == r₂) = false := by
  cases hab : (r₁ == r₂) with
  | false => rfl
  | true => exact absurd (reg64_eq_of_beq hab) h

private theorem reg64_bne_of_ne {r₁ r₂ : Reg64} (h : r₁ ≠ r₂) : (r₁ != r₂) = true := by
  change !(r₁ == r₂) = true
  rw [reg64_beq_false_of_ne h]; rfl

private theorem condCode_beq_self (cc : CondCode) : (cc == cc) = true := by
  cases cc <;> rfl

private theorem condCode_eq_of_beq {c₁ c₂ : CondCode} (h : (c₁ == c₂) = true) : c₁ = c₂ := by
  cases c₁ <;> cases c₂ <;> first | rfl | cases h

private theorem condCode_beq_false_of_ne {c₁ c₂ : CondCode} (h : c₁ ≠ c₂) :
    (c₁ == c₂) = false := by
  cases hab : (c₁ == c₂) with
  | false => rfl
  | true => exact absurd (condCode_eq_of_beq hab) h

theorem asmX64List_nil : asmX64List [] = [] := rfl

theorem asmX64List_append (a b : List (Instr x64Arch)) :
    asmX64List (a ++ b) = asmX64List a ++ asmX64List b :=
  List.flatMap_append

theorem asmX64List_map_native (ds : List _root_.Directive) :
    asmX64List (ds.map (Instr.native (A := x64Arch))) = ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.map_cons, asmX64List, List.flatMap_cons, asmX64]
    exact congrArg (d :: ·) ih

theorem asmX64List_nativePair {x : Option (List _root_.Directive × FlagMask)} :
    (x64NativePair x).map (fun (c, cl) => (asmX64List c, cl)) = x := by
  cases x with
  | none => rfl
  | some p =>
    rcases p with ⟨ds, cl⟩
    dsimp only [x64NativePair, Option.map]
    rw [asmX64List_map_native]

private theorem addrToExprIns_clob (a : AddrArg Reg64) : (addrToExprIns a).2.2 = maskNone := by
  cases a with
  | baseDisp _ _ => dsimp only [addrToExprIns]; repeat' (split <;> try rfl)
  | baseIdxDisp _ _ _ _ => dsimp only [addrToExprIns]; repeat' (split <;> try rfl)
  | imm _ => rfl

private theorem width_bits_toX64 : ∀ w : Width, w.bits = w.toX64.bits
  | .w8 => rfl | .w16 => rfl | .w32 => rfl | .w64 => rfl

private theorem bitvec_setWidth_64_roundtrip (w : Width) (cb : BitVec w.bits) :
    (cb.setWidth 64).setWidth w.bits = cb := by
  rw [BitVec.setWidth_setWidth_of_le _ w.bits_le_64, BitVec.setWidth_eq]

theorem vllX64_legalTarget_eq : vllX64LegalTarget = x64LegalTarget := rfl

theorem vllX64_assignSig_eq :
    ∀ (ts : List Ty) (gs : List Reg64) (vs : List RegMm),
      vllX64Isa.assignSig ts gs vs = x64Isa.assignSig ts gs vs
  | [], _, _ => rfl
  | .bool :: ts, [], _ => rfl
  | .bool :: ts, r :: gs, vs => by
    simp only [Isa.assignSig]; rw [vllX64_assignSig_eq ts gs vs]; rfl
  | .bits n :: ts, [], _ => rfl
  | .bits n :: ts, r :: gs, vs => by
    change (if x64BitWidths.contains n then (vllX64Isa.assignSig ts gs vs).map _ else none) =
      if x64BitWidths.contains n then (x64Isa.assignSig ts gs vs).map _ else none
    rw [vllX64_assignSig_eq ts gs vs]; rfl
  | .float _ :: _, _, _ => rfl
  | .pair a b :: ts, _, [] => rfl
  | .pair a b :: ts, gs, v :: vs => by
    change (if x64IsAbiVec (.pair a b) then (vllX64Isa.assignSig ts gs vs).map _ else none) =
      if x64IsAbiVec (.pair a b) then (x64Isa.assignSig ts gs vs).map _ else none
    rw [vllX64_assignSig_eq ts gs vs]; rfl

theorem vllX64_assignArgs_eq (as : List Ty) :
    vllX64Isa.assignArgs as = x64Isa.assignArgs as :=
  vllX64_assignSig_eq as _ _

theorem vllX64_assignRets_eq (rs : List Ty) :
    vllX64Isa.assignRets rs = x64Isa.assignRets rs :=
  vllX64_assignSig_eq rs _ _

theorem vllX64_clearFlags_eq :
    asmX64List vllX64Isa.gpr.clearFlags = x64Isa.gpr.clearFlags := rfl

theorem vllX64_mov_eq (d s : Reg64) :
    asmX64List (vllX64Isa.gpr.mov d s) = x64Isa.gpr.mov d s := rfl

theorem vllX64_movi_eq (d : Reg64) (cb : BitVec 64) :
    asmX64List (vllX64Isa.gpr.movi d cb) = x64Isa.gpr.movi d cb := rfl

theorem vllX64_setcc_eq (d : Reg64) (cc : CondCode) :
    asmX64List (vllX64Isa.gpr.setcc d cc) = x64Isa.gpr.setcc d cc := rfl

theorem vllX64_jmp_eq (l : Sym) :
    asmX64List (vllX64Isa.gpr.jmp l) = x64Isa.gpr.jmp l := rfl

theorem vllX64_jcc_eq (cc : CondCode) (l : Sym) :
    asmX64List (vllX64Isa.gpr.jcc cc l) = x64Isa.gpr.jcc cc l := rfl

theorem vllX64_jnzGpr_eq (r : Reg64) (l : Sym) :
    (asmX64List (vllX64Isa.gpr.jnzGpr r l).1, (vllX64Isa.gpr.jnzGpr r l).2) =
      x64Isa.gpr.jnzGpr r l := rfl

theorem vllX64_jnzGprInv_eq (r : Reg64) (inv : Bool) (l : Sym) :
    (asmX64List (vllX64JnzGprInv r inv l).1, (vllX64JnzGprInv r inv l).2) =
      x64JnzGpr r inv l := by
  cases inv
  · rfl
  · dsimp only [vllX64JnzGprInv]
    simp only [↓reduceIte]
    rw [asmX64List_map_native]

theorem vllX64_label_eq (l : Sym) :
    asmX64List [vllX64Isa.frame.label l] = [x64Isa.frame.label l] := rfl

theorem vllX64_prologue_eq (ns : Nat) :
    asmX64List (vllX64Isa.frame.prologue ns).1 = (x64Isa.frame.prologue ns).1 := by
  dsimp only [vllX64Isa, vllIsa, vllX64Policy, vllIsaOfHooks, vllFrameIsaOfHooks, vllFrameIsa]
  simp only [asmX64List, List.flatMap_cons, List.flatMap_nil, List.append_nil, asmX64]

theorem vllX64_epilogue_eq (ns : Nat) :
    asmX64List (vllX64Isa.frame.epilogue ns).1 = (x64Isa.frame.epilogue ns).1 := by
  dsimp only [vllX64Isa, vllIsa, vllX64Policy, vllIsaOfHooks, vllFrameIsaOfHooks, vllFrameIsa]
  simp only [asmX64List, List.flatMap_cons, List.flatMap_nil, List.append_nil, asmX64]

theorem vllX64_slotSt_eq (i : Nat) (r : Reg64) :
    asmX64List (vllX64Isa.frame.slotSt i r) = x64Isa.frame.slotSt i r := by
  dsimp only [vllX64Isa, vllIsa, vllX64Policy, vllIsaOfHooks, vllFrameIsaOfHooks, vllFrameIsa]
  simp only [asmX64List, List.flatMap_cons, List.flatMap_nil, List.append_nil, asmX64]

theorem vllX64_slotLd_eq (r : Reg64) (i : Nat) :
    asmX64List (vllX64Isa.frame.slotLd r i) = x64Isa.frame.slotLd r i := by
  dsimp only [vllX64Isa, vllIsa, vllX64Policy, vllIsaOfHooks, vllFrameIsaOfHooks, vllFrameIsa]
  simp only [asmX64List, List.flatMap_cons, List.flatMap_nil, List.append_nil, asmX64]

theorem vllX64_canonAbi_eq (t : Ty) (r : Reg64) :
    asmX64List (vllX64Isa.frame.canonAbi t r).1 = (x64Isa.frame.canonAbi t r).1 := by
  dsimp only [vllX64Isa, vllIsa, vllX64Policy, vllIsaOfHooks, vllFrameIsaOfHooks, vllFrameIsa]
  simp only [asmX64List, List.flatMap_cons, List.flatMap_nil, List.append_nil, asmX64]

theorem vllX64_call_eq (f : Sym) :
    asmX64List (vllX64Isa.frame.call f) = x64Isa.frame.call f := rfl

theorem vllX64_exitJmp_eq (f : Sym) :
    asmX64List (vllX64Isa.frame.exitJmp f) = x64Isa.frame.exitJmp f := rfl

theorem vllX64_ret_eq :
    asmX64List vllX64Isa.frame.ret = x64Isa.frame.ret := rfl

theorem vllX64_vmov_eq (w : SlotWidth) (d s : RegMm) :
    asmX64List (vllX64Isa.vec.vmov w d s) = x64Isa.vec.vmov w d s :=
  asmX64List_map_native _

theorem vllX64_vmovi_eq (w : SlotWidth) (d : RegMm) (cb : BitVec 512) :
    (vllX64Isa.vec.vmovi w d cb).map asmX64List = x64Isa.vec.vmovi w d cb := by
  dsimp only [vllX64Isa, vllIsa, vllX64Policy, vllIsaOfHooks, vllX64NativeHooks, vllX64Vec, x64Isa,
    x64Vec]
  cases x64Vmovi w d cb with
  | none => rfl
  | some ds => dsimp only [Option.map]; rw [asmX64List_map_native]

theorem vllX64_vslotSt_eq (w : SlotWidth) (i : Nat) (s : RegMm) :
    asmX64List (vllX64Isa.vec.vslotSt w i s) = x64Isa.vec.vslotSt w i s :=
  asmX64List_map_native _

theorem vllX64_vslotLd_eq (w : SlotWidth) (d : RegMm) (i : Nat) :
    asmX64List (vllX64Isa.vec.vslotLd w d i) = x64Isa.vec.vslotLd w d i :=
  asmX64List_map_native _

theorem vllX64_vop_eq {sig rs : List Ty} (code : OpCode sig rs)
    (pas : Tup (PArg Reg64 RegMm CondCode) sig) (dsts : Tup (PDst Reg64 RegMm CondCode) rs)
    (vh : VariantHint) :
    (vllX64Isa.vec.vop code pas dsts vh).map (fun (d, cl) => (asmX64List d, cl)) =
      x64Isa.vec.vop code pas dsts vh := by
  dsimp only [vllX64Isa, vllIsa, vllX64Policy, vllIsaOfHooks, vllX64NativeHooks, vllX64Vec, x64Isa,
    x64Vec]
  cases x64Vop code pas dsts vh with
  | none => rfl
  | some p =>
    rcases p with ⟨ds, cl⟩; dsimp only [Option.map]; rw [asmX64List_map_native]

theorem vllX64_vload_eq (t : Ty) (d : RegMm) (a : AddrArg Reg64) :
    (vllX64Isa.vec.vload t d a).map (fun (ds, cl) => (asmX64List ds, cl)) =
      x64Isa.vec.vload t d a := by
  dsimp only [vllX64Isa, vllIsa, vllX64Policy, vllIsaOfHooks, vllX64NativeHooks, vllX64Vec, x64Isa,
    x64Vec]
  cases x64Vload t d a with
  | none => rfl
  | some p =>
    rcases p with ⟨ds, cl⟩; dsimp only [Option.map]; rw [asmX64List_map_native]

theorem vllX64_vstore_eq (t : Ty) (s : RegMm) (a : AddrArg Reg64) :
    (vllX64Isa.vec.vstore t s a).map (fun (ds, cl) => (asmX64List ds, cl)) =
      x64Isa.vec.vstore t s a := by
  dsimp only [vllX64Isa, vllIsa, vllX64Policy, vllIsaOfHooks, vllX64NativeHooks, vllX64Vec, x64Isa,
    x64Vec]
  cases x64Vstore t s a with
  | none => rfl
  | some p =>
    rcases p with ⟨ds, cl⟩; dsimp only [Option.map]; rw [asmX64List_map_native]

theorem vllX64_testOp_eq (w : Nat) (neg : Bool) (pa pb : PArg Reg64 RegMm CondCode (.bits w))
    (pd : PDst Reg64 RegMm CondCode .bool) :
    (vllX64Isa.gpr.testOp w neg pa pb pd).map (fun (c0, cl) => (asmX64List c0, cl)) =
      x64Isa.gpr.testOp w neg pa pb pd :=
  asmX64List_nativePair

theorem vllX64_cmpMem_eq (co : CmpOp) (w : Nat) (a : AddrArg Reg64)
    (pb : PArg Reg64 RegMm CondCode (.bits w)) (pd : PDst Reg64 RegMm CondCode .bool) :
    (vllX64Isa.gpr.cmpMem co w a pb pd).map (fun (c0, cl) => (asmX64List c0, cl)) =
      x64Isa.gpr.cmpMem co w a pb pd :=
  asmX64List_nativePair

theorem vllX64_testMem_eq (w : Nat) (neg : Bool) (a : AddrArg Reg64)
    (pb : PArg Reg64 RegMm CondCode (.bits w)) (pd : PDst Reg64 RegMm CondCode .bool) :
    (vllX64Isa.gpr.testMem w neg a pb pd).map (fun (c0, cl) => (asmX64List c0, cl)) =
      x64Isa.gpr.testMem w neg a pb pd :=
  asmX64List_nativePair

theorem vllX64_aluMem_eq (w : Nat) (code : OpCode [.bits w, .bits w] [.bits w])
    (memRhs : Bool) (a : AddrArg Reg64) (pb : PArg Reg64 RegMm CondCode (.bits w)) (rd : Reg64) :
    (vllX64Isa.gpr.aluMem w code memRhs a pb rd).map (fun (c0, cl) => (asmX64List c0, cl)) =
      x64Isa.gpr.aluMem w code memRhs a pb rd :=
  asmX64List_nativePair

theorem vllX64_jnzMem_eq (a : AddrArg Reg64) (inv : Bool) (l : Sym) :
    (vllX64Isa.gpr.jnzMem a inv l).map (fun (c0, cl) => (asmX64List c0, cl)) =
      x64Isa.gpr.jnzMem a inv l :=
  asmX64List_nativePair

theorem vllX64_rmwMem_eq (w : Nat) (code : OpCode [.bits w, .bits w] [.bits w])
    (a : AddrArg Reg64) (pb : PArg Reg64 RegMm CondCode (.bits w)) :
    (vllX64Isa.gpr.rmwMem w code a pb).map (fun (c0, cl) => (asmX64List c0, cl)) =
      x64Isa.gpr.rmwMem w code a pb :=
  asmX64List_nativePair

theorem vllX64_leaArith_eq (w : Nat) (base? : Option Reg64) (idx : Reg64) (sc : AddrScale)
    (disp : Int64) (rd : Reg64) :
    (vllX64Isa.gpr.leaArith w base? idx sc disp rd).map (fun (c0, cl) => (asmX64List c0, cl)) =
      x64Isa.gpr.leaArith w base? idx sc disp rd :=
  asmX64List_nativePair

theorem vllX64_loadSext_eq (m n : Nat) (rd : Reg64) (a : AddrArg Reg64) :
    (vllX64Isa.gpr.loadSext m n rd a).map (fun (c0, cl) => (asmX64List c0, cl)) =
      x64Isa.gpr.loadSext m n rd a := by
  dsimp only [vllX64Isa, vllIsa, vllX64Policy, vllIsaOfHooks, vllGprIsaOfHooks,
    vllX64NativeHooks, vllX64LoadSext, x64Isa, x64Gpr, x64LoadSext, x64LoadSextIns, emitCleanPair]
  cases hok : x64AddrValid a && Nat.blt m n && Nat.ble n 64 with
  | false => simp only [Bool.not_false, ↓reduceIte]; rfl
  | true =>
    have ha : x64AddrValid a = true := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hok).1).1
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have h8 : m = 8 ∨ m = 16 ∨ m = 32 ∨ (m ≠ 8 ∧ m ≠ 16 ∧ m ≠ 32) := by omega
    rcases h8 with rfl | rfl | rfl | ⟨hn8, hn16, hn32⟩
    · simp only [Option.map, asmX64List, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        asmX64, Width.bits, x64LoadSext, x64LoadSextIns, emitCleanPair, ha, Bool.true_and,
        Nat.blt, addrToExprIns_clob]
      rfl
    · simp only [Option.map, asmX64List, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        asmX64, Width.bits, x64LoadSext, x64LoadSextIns, emitCleanPair, ha, Bool.true_and,
        Nat.blt, addrToExprIns_clob]
      rfl
    · simp only [Option.map, asmX64List, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        asmX64, Width.bits, x64LoadSext, x64LoadSextIns, emitCleanPair, ha, Bool.true_and,
        Nat.blt, addrToExprIns_clob]
      rfl
    · split <;> first
        | exact absurd rfl hn8 | exact absurd rfl hn16 | exact absurd rfl hn32
        | (split <;> first
            | exact absurd rfl hn8 | exact absurd rfl hn16 | exact absurd rfl hn32 | rfl)

private theorem vllStore_hook_fb_eq (t : Ty) (pa : PArg Reg64 RegMm CondCode t) (a : AddrArg Reg64)
    (hhook : vllX64StoreHook t pa a = x64NativePair (x64Store t pa a))
    (hnone : x64Store t pa a = none → vllCoreStore x64Arch t pa a = none) :
    (vllX64Isa.gpr.store t pa a).map (fun (c0, cl) => (asmX64List c0, cl)) =
      x64Isa.gpr.store t pa a := by
  dsimp only [vllX64Isa, vllIsa, vllX64Policy, vllIsaOfHooks, vllGprIsaOfHooks,
    vllX64NativeHooks, x64Isa, x64Gpr]
  rw [hhook]
  cases hx : x64Store t pa a with
  | none => dsimp only [x64NativePair, Option.map]; rw [hnone hx]
  | some p =>
    rcases p with ⟨ds, cl⟩; dsimp only [x64NativePair, Option.map]; rw [asmX64List_map_native]

theorem vllX64_store_eq (t : Ty) (pa : PArg Reg64 RegMm CondCode t) (a : AddrArg Reg64)
    (ha : x64AddrValid a = true) :
    (vllX64Isa.gpr.store t pa a).map (fun (c0, cl) => (asmX64List c0, cl)) =
      x64Isa.gpr.store t pa a := by
  cases t with
  | float _ | pair _ _ =>
    refine vllStore_hook_fb_eq _ pa a (by dsimp only [vllX64StoreHook]; simp [ha]) fun _ => rfl
  | bool =>
    cases pa with
    | vec v =>
      refine vllStore_hook_fb_eq .bool (.vec v) a
        (by dsimp only [vllX64StoreHook]; simp [ha]) fun _ => rfl
    | imm b =>
      refine vllStore_hook_fb_eq .bool (.imm b) a
        (by dsimp only [vllX64StoreHook]; simp [ha]) fun hx => ?_
      exfalso; dsimp only [x64Store, x64StoreIns, emitCleanPair] at hx; rw [ha] at hx; cases hx
    | flag cc =>
      refine vllStore_hook_fb_eq .bool (.flag cc) a
        (by dsimp only [vllX64StoreHook]; simp [ha]) fun hx => ?_
      exfalso; dsimp only [x64Store, x64StoreIns, emitCleanPair] at hx; rw [ha] at hx; cases hx
    | gpr r =>
      dsimp only [vllX64Isa, vllIsa, vllX64Policy, vllIsaOfHooks, vllGprIsaOfHooks,
        vllX64NativeHooks, vllX64StoreHook, vllCoreStore, x64Isa, x64Gpr]
      simp only [Option.map, asmX64List, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        asmX64, Width.toTy, Width.bits, x64Store, x64StoreIns, emitCleanPair, ha, Bool.true_and,
        Bool.not_true, Bool.false_eq_true, ↓reduceIte, addrToExprIns_clob]
      rfl
  | bits n =>
    by_cases hbw : ([8, 16, 32, 64] : List Nat).contains n = true
    · have hmn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 := by simpa [List.contains_eq_mem] using hbw
      rcases hmn with rfl | rfl | rfl | rfl <;> cases pa with
      | vec v =>
        refine vllStore_hook_fb_eq (.bits _) (.vec v) a
          (by dsimp only [vllX64StoreHook]; simp [ha, x64BitWidths]) fun _ => rfl
      | imm cb =>
        refine vllStore_hook_fb_eq (.bits _) (.imm cb) a
          (by dsimp only [vllX64StoreHook]; simp [ha, x64BitWidths]) fun hx => ?_
        exfalso
        dsimp only [x64Store, x64StoreIns, Amd64.withWidth, emitCleanPair] at hx
        rw [ha] at hx; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hx
        split at hx <;> cases hx
      | gpr r =>
        dsimp only [vllX64Isa, vllIsa, vllX64Policy, vllIsaOfHooks, vllGprIsaOfHooks,
          vllX64NativeHooks, vllX64StoreHook, vllCoreStore, vllCoreStoreW, withWidth, x64Arch,
          x64Frame, x64Isa, x64Gpr]
        simp only [hbw, x64BitWidths, Bool.true_and, ↓reduceIte, Option.map, asmX64List,
          List.flatMap_cons, List.flatMap_nil, List.append_nil, asmX64, Width.toTy, Width.bits,
          x64Store, x64StoreIns, Amd64.withWidth, emitCleanPair, ha, Bool.not_true,
          Bool.false_eq_true, addrToExprIns_clob]
        rfl
    · have hbwf : x64BitWidths.contains n = false := Bool.eq_false_iff.mpr hbw
      refine vllStore_hook_fb_eq (.bits n) pa a
        (by dsimp only [vllX64StoreHook]
            simp only [hbwf, Bool.and_false, Bool.false_eq_true, ↓reduceIte]) fun _ => by
        dsimp only [vllCoreStore, x64Arch, x64Frame]
        rw [show ([8, 16, 32, 64] : List Nat).contains n = false from hbwf]; rfl

theorem vllX64_store_eq_of_x64 {t : Ty} {pa : PArg Reg64 RegMm CondCode t} {a : AddrArg Reg64}
    {ds : List _root_.Directive} {cl : FlagMask}
    (hx : x64Isa.gpr.store t pa a = some (ds, cl)) :
    ∃ cs, vllX64Isa.gpr.store t pa a = some (cs, cl) ∧ asmX64List cs = ds := by
  have ha : x64AddrValid a = true := by
    cases h : x64AddrValid a
    · exfalso
      cases t with
      | float _ | pair _ _ => cases hx
      | bool =>
        dsimp only [x64Isa, x64Gpr, x64Store, x64StoreIns, emitCleanPair] at hx; rw [h] at hx
        cases hx
      | bits n =>
        dsimp only [x64Isa, x64Gpr, x64Store, x64StoreIns, emitCleanPair] at hx; rw [h] at hx
        cases hx
    · rfl
  have heq := vllX64_store_eq t pa a ha
  rw [hx] at heq
  rcases Option.map_eq_some_iff.mp heq with ⟨⟨cs, cl'⟩, hcs, hpe⟩
  cases hpe
  exact ⟨cs, hcs, rfl⟩

private theorem asmX64_load_zx_of_valid (w : Width) (rd : Reg64) (a : AddrArg Reg64)
    (ha : x64AddrValid a = true) :
    some (asmX64List [.load w .zx rd a], maskNone) = x64Load w.toTy rd a := by
  simp only [asmX64List, List.flatMap_cons, List.flatMap_nil, List.append_nil, asmX64]
  cases w <;>
    (dsimp only [Width.toTy, x64Load, x64LoadIns, emitCleanPair]
     rw [ha]
     simp [addrToExprIns_clob])

private theorem x64Load_none_of_not_bw {n : Nat} (rd : Reg64) (a : AddrArg Reg64)
    (hbw : ([8, 16, 32, 64] : List Nat).contains n = false) :
    x64Load (.bits n) rd a = none := by
  suffices h : ∀ t : Ty, t = .bits n → x64LoadIns t rd a = none by
    simp only [x64Load, emitCleanPair, h (.bits n) rfl, Option.map_none]
  intro t ht
  dsimp only [x64LoadIns]
  cases t with
  | bool | float _ | pair _ _ => cases ht
  | bits m =>
    cases ht
    split
    · rfl
    · split
      · cases ‹_›
      · rename_i heq; cases heq; cases hbw
      · rename_i heq; cases heq; cases hbw
      · rename_i heq; cases heq; cases hbw
      · rename_i heq; cases heq; cases hbw
      · rfl

theorem vllX64_load_eq (t : Ty) (rd : Reg64) (a : AddrArg Reg64)
    (ha : x64AddrValid a = true) :
    (vllX64Isa.gpr.load t rd a).map (fun (c0, cl) => (asmX64List c0, cl)) =
      x64Isa.gpr.load t rd a := by
  dsimp only [vllX64Isa, vllIsa, vllX64Policy, vllIsaOfHooks, vllGprIsaOfHooks,
    vllX64NativeHooks, vllCoreLoad, x64Isa, x64Gpr]
  cases t with
  | float _ | pair _ _ => dsimp only [x64Load, x64LoadIns, emitCleanPair]; rw [ha]; rfl
  | bool =>
    dsimp only [vllCoreLoad, Option.map]
    exact asmX64_load_zx_of_valid .w8 rd a ha
  | bits n =>
    dsimp only [x64Arch, x64Frame]
    by_cases hbw : ([8, 16, 32, 64] : List Nat).contains n = true
    · have hmn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 := by
        simpa [List.contains_eq_mem] using hbw
      rcases hmn with rfl | rfl | rfl | rfl
      · exact asmX64_load_zx_of_valid .w8 rd a ha
      · exact asmX64_load_zx_of_valid .w16 rd a ha
      · exact asmX64_load_zx_of_valid .w32 rd a ha
      · exact asmX64_load_zx_of_valid .w64 rd a ha
    · have hbwf : ([8, 16, 32, 64] : List Nat).contains n = false := Bool.eq_false_iff.mpr hbw
      rw [hbwf]; simp only [Bool.false_eq_true, ↓reduceIte, Option.map]
      exact (x64Load_none_of_not_bw rd a hbwf).symm

theorem vllX64_load_eq_of_x64 {t : Ty} {rd : Reg64} {a : AddrArg Reg64}
    {ds : List _root_.Directive} {cl : FlagMask}
    (hx : x64Isa.gpr.load t rd a = some (ds, cl)) :
    ∃ cs, vllX64Isa.gpr.load t rd a = some (cs, cl) ∧ asmX64List cs = ds := by
  have ha : x64AddrValid a = true := by
    cases h : x64AddrValid a
    · exfalso; dsimp only [x64Isa, x64Gpr, x64Load, x64LoadIns, emitCleanPair] at hx
      rw [h] at hx; cases hx
    · rfl
  have heq := vllX64_load_eq t rd a ha
  rw [hx] at heq
  rcases Option.map_eq_some_iff.mp heq with ⟨⟨cs, cl'⟩, hcs, hpe⟩
  cases hpe
  exact ⟨cs, hcs, rfl⟩

private theorem movSubWI_eq_movWI_wide {w : _root_.Width} (hw : w = .W32 ∨ w = .W64)
    (rd rs : Reg64) : movSubWI w rd rs = movWI w rd rs := by
  rcases hw with rfl | rfl <;> rfl

private theorem opBinLeaReg_none_of_not_add {w : _root_.Width} {k : AluBinKind}
    (hk : k ≠ .add) (ra rb rd : Reg64) : opBinLeaReg? w k ra rb rd = none := by
  cases k with
  | add => exact absurd rfl hk
  | sub | and | or | xor | mul => rfl

private theorem opBinLeaImm_none_of_logic {w : _root_.Width} {k : AluBinKind}
    (hk : k ≠ .add ∧ k ≠ .sub) (ra : Reg64) (cb : BitVec w.bits) (rd : Reg64) :
    opBinLeaImm? w k ra cb rd = none := by
  cases k <;> simp_all [opBinLeaImm?]

private theorem asmX64List_aluBin_hook_gpr_logic (w : Width) (k : AluBinKind) (rd ra rb : Reg64)
    (hk : k = .and ∨ k = .or ∨ k = .xor)
    (hwide : (ra == rd) = true ∨ w = .w32 ∨ w = .w64) :
    let op : CoreAlu := match k with
      | .add => .add | .sub => .sub | .and => .and | .or => .or | .xor => .xor | .mul => .mul
    some (asmX64List [.alu op w rd ra (.reg rb) true], maskAll) =
      emitCleanPair (opBinIns w.toX64 k
        (cast (congrArg (fun n => PArg Reg64 RegMm CondCode (.bits n)) (width_bits_toX64 w))
          (.gpr ra))
        (cast (congrArg (fun n => PArg Reg64 RegMm CondCode (.bits n)) (width_bits_toX64 w))
          (.gpr rb))
        rd .default) := by
  have hk_ne_add : k ≠ .add := by rcases hk with rfl | rfl | rfl <;> intro h <;> cases h
  have hk_comm : k.isComm = true := by rcases hk with rfl | rfl | rfl <;> rfl
  have hk_ne_sub : (k == .sub) = false := by rcases hk with rfl | rfl | rfl <;> rfl
  cases w <;> dsimp only [asmX64List, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    opBinIns, emitCleanPair, Width.toX64]
  all_goals
    by_cases hrr : (ra == rd) = true
    · rcases hk with rfl | rfl | rfl <;>
        simp [hrr, asmX64, asmX64AluIns, asmX64AluBinIns, asmX64BinCoreIns]
    · have hrrf : (ra == rd) = false := Bool.eq_false_iff.mpr hrr
      rcases hwide with h | h | h
      · exact absurd h hrr
      all_goals try cases h
      all_goals
        by_cases hrb : (rb == rd) = true
        · rcases hk with rfl | rfl | rfl <;>
            simp [hrrf, hrb, hk_comm, asmX64, asmX64AluIns, asmX64AluBinIns, asmX64BinCoreIns]
        · have hrbf : (rb == rd) = false := Bool.eq_false_iff.mpr hrb
          have hrbne : (rb != rd) = true := by change !(rb == rd) = true; rw [hrbf]; rfl
          rcases hk with rfl | rfl | rfl <;>
            simp [hrrf, hrbf, hrbne, hk_comm, hk_ne_sub, opBinLeaReg_none_of_not_add hk_ne_add,
              asmX64, asmX64AluIns, asmX64AluBinIns, asmX64BinCoreIns, movSubWI, regW]

private theorem asmX64List_aluBin_hook_imm_logic (w : Width) (k : AluBinKind) (rd ra : Reg64)
    (cb : BitVec w.bits) (hk : k = .and ∨ k = .or ∨ k = .xor)
    (hwide : (ra == rd) = true ∨ w = .w32 ∨ w = .w64) :
    let op : CoreAlu := match k with
      | .add => .add | .sub => .sub | .and => .and | .or => .or | .xor => .xor | .mul => .mul
    some (asmX64List [.alu op w rd ra (.imm (cb.setWidth 64)) true], maskAll) =
      emitCleanPair (opBinIns w.toX64 k
        (cast (congrArg (fun n => PArg Reg64 RegMm CondCode (.bits n)) (width_bits_toX64 w))
          (.gpr ra))
        (cast (congrArg (fun n => PArg Reg64 RegMm CondCode (.bits n)) (width_bits_toX64 w))
          (.imm cb))
        rd .default) := by
  have hk_ne : k ≠ .add ∧ k ≠ .sub := by
    rcases hk with rfl | rfl | rfl <;> exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
  have hcb := bitvec_setWidth_64_roundtrip w cb
  have hw8 : (_root_.Width.W8 != _root_.Width.W64) = true := rfl
  have hw16 : (_root_.Width.W16 != _root_.Width.W64) = true := rfl
  have hw32 : (_root_.Width.W32 != _root_.Width.W64) = true := rfl
  have hw64 : (_root_.Width.W64 != _root_.Width.W64) = false := rfl
  cases w <;> dsimp only [asmX64List, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    opBinIns, emitCleanPair, Width.toX64]
  have opBinLeaImm_self_none : ∀ (w : _root_.Width) (k : AluBinKind) (rd : Reg64)
      (cb : BitVec w.bits), opBinLeaImm? w k rd cb rd = none := by
    intro w' k' rd' cb'
    dsimp only [opBinLeaImm?]; simp [reg64_bne_self]
  all_goals
    by_cases hrr : (ra == rd) = true
    · rcases hk with rfl | rfl | rfl <;>
        (simp only [hrr, opBinLeaImm_none_of_logic hk_ne, Option.map, List.flatMap_cons,
           List.flatMap_nil, List.append_nil, asmX64, asmX64AluIns, asmX64AluBinIns,
           asmX64BinCoreIns, Width.toX64, cast_eq, hcb, ↓reduceIte, Option.getD_none]
         try rw [hw8]
         try rw [hw16]
         try rw [hw32]
         try rw [hw64]
         simp only [Bool.true_or, Bool.false_or, ↓reduceIte]
         try (by_cases hf : fitsImm32 cb <;> simp [hf]))
    · have hrrf : (ra == rd) = false := Bool.eq_false_iff.mpr hrr
      rcases hwide with h | h | h
      · exact absurd h hrr
      all_goals try cases h
      all_goals
        rcases hk with rfl | rfl | rfl <;>
          (simp only [hrrf, opBinLeaImm_none_of_logic hk_ne, Option.map, List.flatMap_cons,
             List.flatMap_nil, List.append_nil, asmX64, asmX64AluIns, asmX64AluBinIns,
             asmX64BinCoreIns, Width.toX64, cast_eq, hcb, movSubWI, regW, Bool.false_eq_true,
             ↓reduceIte, Option.getD_none]
           try rw [hw32]
           try rw [hw64]
           simp only [Bool.true_or, Bool.false_or, ↓reduceIte]
           try (by_cases hf : fitsImm32 cb <;> simp [hf]))

private theorem asmX64List_aluBin_hook_eq (w : Width) (k : AluBinKind) (rd ra : Reg64)
    (pb : PArg Reg64 RegMm CondCode (.bits w.bits))
    (hwide : (ra == rd) = true ∨ w = .w32 ∨ w = .w64)
    (hk : (k = .add ∧ ra = rd) ∨ (k = .sub ∧ ra = rd) ∨ k = .and ∨ k = .or ∨ k = .xor) :
    let op : CoreAlu := match k with
      | .add => .add | .sub => .sub | .and => .and | .or => .or | .xor => .xor | .mul => .mul
    let xw := w.toX64
    let pa' : PArg Reg64 RegMm CondCode (.bits xw.bits) :=
      cast (congrArg (fun n => PArg Reg64 RegMm CondCode (.bits n)) (width_bits_toX64 w)) (.gpr ra)
    let pb' : PArg Reg64 RegMm CondCode (.bits xw.bits) :=
      cast (congrArg (fun n => PArg Reg64 RegMm CondCode (.bits n)) (width_bits_toX64 w)) pb
    (match pb with
     | .gpr rb => some (asmX64List [.alu op w rd ra (.reg rb) true], maskAll)
     | .imm cb => some (asmX64List [.alu op w rd ra (.imm (cb.setWidth 64)) true], maskAll)
     | .vec _ => none) =
      emitCleanPair (opBinIns xw k pa' pb' rd .default) := by
  have hlea_self : ∀ (w' : _root_.Width) (k' : AluBinKind) (rd' : Reg64)
      (cb' : BitVec w'.bits), opBinLeaImm? w' k' rd' cb' rd' = none := by
    intro w' k' rd' cb'; dsimp only [opBinLeaImm?]; simp [reg64_bne_self]
  have hw8 : (_root_.Width.W8 != _root_.Width.W64) = true := rfl
  have hw16 : (_root_.Width.W16 != _root_.Width.W64) = true := rfl
  have hw32 : (_root_.Width.W32 != _root_.Width.W64) = true := rfl
  have hw64 : (_root_.Width.W64 != _root_.Width.W64) = false := rfl
  rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl | rfl | rfl
  · cases pb with
    | vec _ => cases w <;> rfl
    | gpr rb =>
      cases w <;> simp [asmX64List, asmX64, asmX64AluIns, asmX64AluBinIns, asmX64BinCoreIns,
        opBinIns, emitCleanPair, Width.toX64, reg64_beq_self]
    | imm cb =>
      have hcb := bitvec_setWidth_64_roundtrip w cb
      cases w <;>
        (simp only [asmX64List, List.flatMap_cons, List.flatMap_nil, List.append_nil, asmX64,
           asmX64AluIns, asmX64AluBinIns, asmX64BinCoreIns, opBinIns, hlea_self, emitCleanPair,
           Option.map, Width.toX64, cast_eq, reg64_beq_self, hcb, ↓reduceIte, Option.getD_none]
         try rw [hw8]
         try rw [hw16]
         try rw [hw32]
         try rw [hw64]
         simp only [Bool.true_or, Bool.false_or, ↓reduceIte]
         try (by_cases hf : fitsImm32 cb <;> simp [hf]))
  · cases pb with
    | vec _ => cases w <;> rfl
    | gpr rb =>
      cases w <;> simp [asmX64List, asmX64, asmX64AluIns, asmX64AluBinIns, asmX64BinCoreIns,
        opBinIns, emitCleanPair, Width.toX64, reg64_beq_self]
    | imm cb =>
      have hcb := bitvec_setWidth_64_roundtrip w cb
      cases w <;>
        (simp only [asmX64List, List.flatMap_cons, List.flatMap_nil, List.append_nil, asmX64,
           asmX64AluIns, asmX64AluBinIns, asmX64BinCoreIns, opBinIns, hlea_self, emitCleanPair,
           Option.map, Width.toX64, cast_eq, reg64_beq_self, hcb, ↓reduceIte, Option.getD_none]
         try rw [hw8]
         try rw [hw16]
         try rw [hw32]
         try rw [hw64]
         simp only [Bool.true_or, Bool.false_or, ↓reduceIte]
         try (by_cases hf : fitsImm32 cb <;> simp [hf]))
  · cases pb with
    | vec _ => cases w <;> rfl
    | gpr rb => exact asmX64List_aluBin_hook_gpr_logic w .and rd ra rb (Or.inl rfl) hwide
    | imm cb => exact asmX64List_aluBin_hook_imm_logic w .and rd ra cb (Or.inl rfl) hwide
  · cases pb with
    | vec _ => cases w <;> rfl
    | gpr rb =>
      exact asmX64List_aluBin_hook_gpr_logic w .or rd ra rb (Or.inr (Or.inl rfl)) hwide
    | imm cb =>
      exact asmX64List_aluBin_hook_imm_logic w .or rd ra cb (Or.inr (Or.inl rfl)) hwide
  · cases pb with
    | vec _ => cases w <;> rfl
    | gpr rb =>
      exact asmX64List_aluBin_hook_gpr_logic w .xor rd ra rb (Or.inr (Or.inr rfl)) hwide
    | imm cb =>
      exact asmX64List_aluBin_hook_imm_logic w .xor rd ra cb (Or.inr (Or.inr rfl)) hwide

private theorem asmX64List_mul_core_eq (w : Width) (hw : w = .w16 ∨ w = .w32 ∨ w = .w64)
    (rd : Reg64) (pb : PArg Reg64 RegMm CondCode (.bits w.bits)) (vh : VariantHint) :
    ((vllCoreAlu x64Arch .mul w (.gpr rd) pb rd).map
        (fun (c0, cl) => (asmX64List c0, cl))) =
      emitCleanPair (opBinIns w.toX64 .mul
        (cast (congrArg (fun n => PArg Reg64 RegMm CondCode (.bits n)) (width_bits_toX64 w))
          (.gpr rd))
        (cast (congrArg (fun n => PArg Reg64 RegMm CondCode (.bits n)) (width_bits_toX64 w)) pb)
        rd vh) := by
  have hmul_vh : ∀ w' (pa' pb' : PArg Reg64 RegMm CondCode (.bits w'.bits)) rd' vh',
      opBinIns w' .mul pa' pb' rd' vh' = opBinIns w' .mul pa' pb' rd' .default := by
    intro w' pa' pb' rd' vh'
    dsimp only [opBinIns]
    cases vh' with
    | default | adcx | adox | mulxFast | decInc => rfl
    | disp off =>
      dsimp only
      cases ((w' == _root_.Width.W32 || w' == _root_.Width.W64) && fitsImm32 off.toBitVec) <;>
        cases pa' <;> cases pb' <;> rfl
  have hw16 : (_root_.Width.W16 != _root_.Width.W64) = true := rfl
  have hw32 : (_root_.Width.W32 != _root_.Width.W64) = true := rfl
  have hw64 : (_root_.Width.W64 != _root_.Width.W64) = false := rfl
  rcases hw with rfl | rfl | rfl
  · cases pb with
    | vec _ => rw [hmul_vh]; simp [vllCoreAlu, vllRegOfPArg, vllSrcOfPArg, opBinIns, emitCleanPair]
    | gpr rb =>
      rw [hmul_vh]; simp [vllCoreAlu, vllRegOfPArg, vllSrcOfPArg, asmX64List, asmX64,
        asmX64AluIns, asmX64AluMulIns, asmX64BinCoreIns, opBinIns, emitCleanPair, Width.toX64,
        reg64_beq_self]
    | imm cb =>
      have hcb := bitvec_setWidth_64_roundtrip .w16 cb
      rw [hmul_vh]
      simp [vllCoreAlu, vllRegOfPArg, vllSrcOfPArg, asmX64List, asmX64, asmX64AluIns,
        asmX64AluMulIns, asmX64BinCoreIns, opBinIns, emitCleanPair, opBinLeaImm?, Width.toX64,
        reg64_beq_self, hcb, hw16]
  · cases pb with
    | vec _ => rw [hmul_vh]; simp [vllCoreAlu, vllRegOfPArg, vllSrcOfPArg, opBinIns, emitCleanPair]
    | gpr rb =>
      rw [hmul_vh]; simp [vllCoreAlu, vllRegOfPArg, vllSrcOfPArg, asmX64List, asmX64,
        asmX64AluIns, asmX64AluMulIns, asmX64BinCoreIns, opBinIns, emitCleanPair, Width.toX64,
        reg64_beq_self]
    | imm cb =>
      have hcb := bitvec_setWidth_64_roundtrip .w32 cb
      rw [hmul_vh]
      simp [vllCoreAlu, vllRegOfPArg, vllSrcOfPArg, asmX64List, asmX64, asmX64AluIns,
        asmX64AluMulIns, asmX64BinCoreIns, opBinIns, emitCleanPair, opBinLeaImm?, Width.toX64,
        reg64_beq_self, hcb, hw32]
  · cases pb with
    | vec _ => rw [hmul_vh]; simp [vllCoreAlu, vllRegOfPArg, vllSrcOfPArg, opBinIns, emitCleanPair]
    | gpr rb =>
      rw [hmul_vh]; simp [vllCoreAlu, vllRegOfPArg, vllSrcOfPArg, asmX64List, asmX64,
        asmX64AluIns, asmX64AluMulIns, asmX64BinCoreIns, opBinIns, emitCleanPair, Width.toX64,
        reg64_beq_self]
    | imm cb =>
      rw [hmul_vh]
      simp only [vllCoreAlu, vllRegOfPArg, vllSrcOfPArg, List.nil_append, opBinIns, emitCleanPair,
        opBinLeaImm?, Width.toX64, cast_eq, reg64_beq_self, hw64, Option.map, ↓reduceIte,
        Bool.false_or, BitVec.setWidth_eq, Option.some.injEq]
      by_cases hf : fitsImm32 cb <;>
        simp [asmX64List, asmX64, asmX64AluIns, asmX64AluMulIns, asmX64BinCoreIns, Width.toX64,
          reg64_beq_self, hw64, hf]

private theorem asmX64List_cmp_core_eq (co : CmpOp) (w : Width) (rx : Reg64)
    (pb : PArg Reg64 RegMm CondCode (.bits w.bits)) (pd : PDst Reg64 RegMm CondCode .bool)
    (hpd : (∃ rd, pd = .gpr rd) ∨ pd = .flag (condOf co)) :
    (vllCoreCmpW x64Arch (some ∘ condOf) co w (.gpr rx) pb pd).map
        (fun (c0, cl) => (asmX64List c0, cl)) =
      emitCleanPair (opCmpIns w.toX64 co
        (cast (congrArg (fun n => PArg Reg64 RegMm CondCode (.bits n)) (width_bits_toX64 w))
          (.gpr rx))
        (cast (congrArg (fun n => PArg Reg64 RegMm CondCode (.bits n)) (width_bits_toX64 w)) pb)
        pd) := by
  have hcy := bitvec_setWidth_64_roundtrip
  have hcc : (condOf co == condOf co) = true := condCode_beq_self (condOf co)
  cases pb with
  | vec _ =>
    rcases hpd with ⟨rd, rfl⟩ | rfl
    · cases w <;> simp [vllCoreCmpW, vllRegOfPArg, vllSrcOfPArg, opCmpIns, cmpDirectIns,
        emitCleanPair]
    · cases w <;> simp [vllCoreCmpW, vllRegOfPArg, vllSrcOfPArg, opCmpIns, cmpDirectIns,
        emitCleanPair, hcc]
  | gpr ry =>
    rcases hpd with ⟨rd, rfl⟩ | rfl <;> cases w
    · simp [vllCoreCmpW, vllRegOfPArg, vllSrcOfPArg, asmX64List, asmX64, srcToPArg, opCmpIns,
        cmpDirectIns, emitCleanPair, emitClean, setccOnly, setccOnlyIns, Width.toX64]
    · simp [vllCoreCmpW, vllRegOfPArg, vllSrcOfPArg, asmX64List, asmX64, srcToPArg, opCmpIns,
        cmpDirectIns, emitCleanPair, emitClean, setccOnly, setccOnlyIns, Width.toX64]
    · simp [vllCoreCmpW, vllRegOfPArg, vllSrcOfPArg, asmX64List, asmX64, srcToPArg, opCmpIns,
        cmpDirectIns, emitCleanPair, emitClean, setccOnly, setccOnlyIns, Width.toX64]
    · simp [vllCoreCmpW, vllRegOfPArg, vllSrcOfPArg, asmX64List, asmX64, srcToPArg, opCmpIns,
        cmpDirectIns, emitCleanPair, emitClean, setccOnly, setccOnlyIns, Width.toX64]
    · simp [vllCoreCmpW, vllRegOfPArg, vllSrcOfPArg, asmX64List, asmX64, srcToPArg, opCmpIns,
        cmpDirectIns, emitCleanPair, emitClean, Width.toX64, hcc]
    · simp [vllCoreCmpW, vllRegOfPArg, vllSrcOfPArg, asmX64List, asmX64, srcToPArg, opCmpIns,
        cmpDirectIns, emitCleanPair, emitClean, Width.toX64, hcc]
    · simp [vllCoreCmpW, vllRegOfPArg, vllSrcOfPArg, asmX64List, asmX64, srcToPArg, opCmpIns,
        cmpDirectIns, emitCleanPair, emitClean, Width.toX64, hcc]
    · simp [vllCoreCmpW, vllRegOfPArg, vllSrcOfPArg, asmX64List, asmX64, srcToPArg, opCmpIns,
        cmpDirectIns, emitCleanPair, emitClean, Width.toX64, hcc]
  | imm cy =>
    rcases hpd with ⟨rd, rfl⟩ | rfl <;> cases w
    · simp [vllCoreCmpW, vllRegOfPArg, vllSrcOfPArg, asmX64List, asmX64, srcToPArg, opCmpIns,
        cmpDirectIns, emitCleanPair, emitClean, setccOnly, setccOnlyIns, Width.toX64, hcy .w8]
    · simp [vllCoreCmpW, vllRegOfPArg, vllSrcOfPArg, asmX64List, asmX64, srcToPArg, opCmpIns,
        cmpDirectIns, emitCleanPair, emitClean, setccOnly, setccOnlyIns, Width.toX64, hcy .w16]
    · simp [vllCoreCmpW, vllRegOfPArg, vllSrcOfPArg, asmX64List, asmX64, srcToPArg, opCmpIns,
        cmpDirectIns, emitCleanPair, emitClean, setccOnly, setccOnlyIns, Width.toX64, hcy .w32]
    · simp [vllCoreCmpW, vllRegOfPArg, vllSrcOfPArg, asmX64List, asmX64, srcToPArg, opCmpIns,
        cmpDirectIns, emitCleanPair, emitClean, setccOnly, setccOnlyIns, Width.toX64]
    · simp [vllCoreCmpW, vllRegOfPArg, vllSrcOfPArg, asmX64List, asmX64, srcToPArg, opCmpIns,
        cmpDirectIns, emitCleanPair, emitClean, Width.toX64, hcy .w8, hcc]
    · simp [vllCoreCmpW, vllRegOfPArg, vllSrcOfPArg, asmX64List, asmX64, srcToPArg, opCmpIns,
        cmpDirectIns, emitCleanPair, emitClean, Width.toX64, hcy .w16, hcc]
    · simp [vllCoreCmpW, vllRegOfPArg, vllSrcOfPArg, asmX64List, asmX64, srcToPArg, opCmpIns,
        cmpDirectIns, emitCleanPair, emitClean, Width.toX64, hcy .w32, hcc]
    · simp [vllCoreCmpW, vllRegOfPArg, vllSrcOfPArg, asmX64List, asmX64, srcToPArg, opCmpIns,
        cmpDirectIns, emitCleanPair, emitClean, Width.toX64, hcc]

/-- `true` when `code` does not use equal widths in `zext`/`sext`/`trunc` (`x64Op` requires
strict width change while `vllCoreOp` allows `m = n`). -/
@[expose] def opNoSameExt : {sig rs : List Ty} → OpCode sig rs → Bool
  | _, _, .zext m n | _, _, .sext m n | _, _, .trunc m n => m != n
  | _, _, _ => true

private theorem vllGprOp_hook_fb_eq {sig rs : List Ty} {code : OpCode sig rs}
    {pas : Tup (PArg Reg64 RegMm CondCode) sig} {dsts : Tup (PDst Reg64 RegMm CondCode) rs}
    {vh : VariantHint}
    (hhook : vllX64OpHook code pas dsts vh = x64NativePair (x64Op code pas dsts vh))
    (hnone : x64Op code pas dsts vh = none →
      vllCoreOp x64Arch (some ∘ condOf) code pas dsts vh = none) :
    (vllX64Isa.gpr.op code pas dsts vh).map (fun (c0, cl) => (asmX64List c0, cl)) =
      x64Isa.gpr.op code pas dsts vh := by
  dsimp only [vllX64Isa, vllIsa, vllX64Policy, vllIsaOfHooks, vllGprIsaOfHooks,
    vllX64NativeHooks, x64Isa, x64Gpr]
  rw [hhook]
  cases hx : x64Op code pas dsts vh with
  | none =>
    dsimp only [x64NativePair, Option.map]
    rw [hnone hx]
  | some p =>
    rcases p with ⟨ds, cl⟩
    dsimp only [x64NativePair, Option.map]
    rw [asmX64List_map_native]

private theorem vllGprOp_hook_none_eq {sig rs : List Ty} {code : OpCode sig rs}
    {pas : Tup (PArg Reg64 RegMm CondCode) sig} {dsts : Tup (PDst Reg64 RegMm CondCode) rs}
    {vh : VariantHint} (hhook : vllX64OpHook code pas dsts vh = none)
    (hcore : (vllCoreOp x64Arch (some ∘ condOf) code pas dsts vh).map
        (fun (c0, cl) => (asmX64List c0, cl)) = x64Op code pas dsts vh) :
    (vllX64Isa.gpr.op code pas dsts vh).map (fun (c0, cl) => (asmX64List c0, cl)) =
      x64Isa.gpr.op code pas dsts vh := by
  dsimp only [vllX64Isa, vllIsa, vllX64Policy, vllIsaOfHooks, vllGprIsaOfHooks,
    vllX64NativeHooks, x64Isa, x64Gpr]
  rw [hhook]
  exact hcore

private theorem vllGprOp_hook_some_eq {sig rs : List Ty} {code : OpCode sig rs}
    {pas : Tup (PArg Reg64 RegMm CondCode) sig} {dsts : Tup (PDst Reg64 RegMm CondCode) rs}
    {vh : VariantHint} (cs : List (Instr x64Arch)) (cl : FlagMask)
    (hhook : vllX64OpHook code pas dsts vh = some (cs, cl))
    (heq : some (asmX64List cs, cl) = x64Op code pas dsts vh) :
    (vllX64Isa.gpr.op code pas dsts vh).map (fun (c0, cl) => (asmX64List c0, cl)) =
      x64Isa.gpr.op code pas dsts vh := by
  dsimp only [vllX64Isa, vllIsa, vllX64Policy, vllIsaOfHooks, vllGprIsaOfHooks,
    vllX64NativeHooks, x64Isa, x64Gpr]
  rw [hhook]
  exact heq

private theorem opBinIns_isSome (w : _root_.Width) (k : AluBinKind)
    (pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)) (rd : Reg64) (vh : VariantHint)
    (ha : ∀ v, pa ≠ .vec v) (hb : ∀ v, pb ≠ .vec v) :
    ∃ res, opBinIns w k pa pb rd vh = some res := by
  dsimp only [opBinIns]
  split
  · exact ⟨_, rfl⟩
  · split
    · exact ⟨_, rfl⟩
    · cases pa with
      | vec v => exact absurd rfl (ha v)
      | gpr ra =>
        cases pb with
        | vec v => exact absurd rfl (hb v)
        | imm _ => exact ⟨_, rfl⟩
        | gpr _ => repeat' (first | exact ⟨_, rfl⟩ | split)
      | imm ca =>
        cases pb with
        | vec v => exact absurd rfl (hb v)
        | imm _ => exact ⟨_, rfl⟩
        | gpr _ => repeat' (first | exact ⟨_, rfl⟩ | split)

private theorem opShiftIns_isSome (w : _root_.Width) (sk : ShiftKind)
    (hk : sk = .shl ∨ sk = .lshr ∨ sk = .ashr)
    (pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)) (rd : Reg64)
    (ha : ∀ v, pa ≠ .vec v) (hb : ∀ v, pb ≠ .vec v) :
    ∃ res, opShiftIns w sk pa pb rd = some res := by
  cases pb with
  | vec v => exact absurd rfl (hb v)
  | imm cb =>
    cases pa with
    | vec v => exact absurd rfl (ha v)
    | gpr _ | imm _ =>
      cases w <;>
        (dsimp only [opShiftIns, opCopyBitsIns]; repeat' (first | exact ⟨_, rfl⟩ | split))
  | gpr rb =>
    cases pa with
    | vec v => exact absurd rfl (ha v)
    | gpr _ | imm _ =>
      cases w <;> rcases hk with rfl | rfl | rfl <;>
        (dsimp only [opShiftIns]; repeat' (first | exact ⟨_, rfl⟩ | split))

private theorem vllCoreBinBits_none_of_not_bw (op : CoreAlu) (n : Nat)
    (hbw : ([8, 16, 32, 64] : List Nat).contains n = false)
    (pa pb : PArg Reg64 RegMm CondCode (.bits n)) (rd : Reg64) :
    vllCoreBinBits x64Arch op n pa pb rd = none := by
  dsimp only [vllCoreBinBits, x64Arch, x64Frame]; rw [hbw]; rfl

private theorem vllX64WidthOfBits_eq_opt {n : Nat} {w : Width}
    (hw : vllX64WidthOfBits? n = some w) : n = w.bits := by
  unfold vllX64WidthOfBits? at hw; split at hw <;> cases hw <;> rfl

private theorem withWidth_parg {α : Type} (w : _root_.Width)
    (x : PArg Reg64 RegMm CondCode (.bits w.bits))
    (k : ∀ w' : _root_.Width, PArg Reg64 RegMm CondCode (.bits w'.bits) → Option α) :
    Amd64.withWidth (F := fun m => PArg Reg64 RegMm CondCode (.bits m)) w.bits x k =
      k w x := by
  cases w <;> rfl

private theorem withWidth_parg2 {α : Type} (w : _root_.Width)
    (x : PArg Reg64 RegMm CondCode (.bits w.bits) × PArg Reg64 RegMm CondCode (.bits w.bits))
    (k : ∀ w' : _root_.Width, PArg Reg64 RegMm CondCode (.bits w'.bits) ×
      PArg Reg64 RegMm CondCode (.bits w'.bits) → Option α) :
    Amd64.withWidth (F := fun m => PArg Reg64 RegMm CondCode (.bits m) ×
      PArg Reg64 RegMm CondCode (.bits m)) w.bits x k = k w x := by
  cases w <;> rfl

private theorem withWidth_vll_parg2 {α : Type} (w : Width)
    (x : PArg Reg64 RegMm CondCode (.bits w.bits) × PArg Reg64 RegMm CondCode (.bits w.bits))
    (k : ∀ w' : _root_.Width, PArg Reg64 RegMm CondCode (.bits w'.bits) ×
      PArg Reg64 RegMm CondCode (.bits w'.bits) → Option α) :
    Amd64.withWidth (F := fun m => PArg Reg64 RegMm CondCode (.bits m) ×
      PArg Reg64 RegMm CondCode (.bits m)) w.bits x k =
      k w.toX64
        (cast (congrArg (fun n => PArg Reg64 RegMm CondCode (.bits n)) (width_bits_toX64 w)) x.1,
         cast (congrArg (fun n => PArg Reg64 RegMm CondCode (.bits n)) (width_bits_toX64 w))
           x.2) := by
  cases w <;> rfl

private theorem withWidth_parg32 {α : Type}
    (x : PArg Reg64 RegMm CondCode (.bits 32))
    (k : ∀ w' : _root_.Width, PArg Reg64 RegMm CondCode (.bits w'.bits) → Option α) :
    Amd64.withWidth (F := fun m => PArg Reg64 RegMm CondCode (.bits m)) 32 x k = k .W32 x := rfl

private theorem withWidth_parg64 {α : Type}
    (x : PArg Reg64 RegMm CondCode (.bits 64))
    (k : ∀ w' : _root_.Width, PArg Reg64 RegMm CondCode (.bits w'.bits) → Option α) :
    Amd64.withWidth (F := fun m => PArg Reg64 RegMm CondCode (.bits m)) 64 x k = k .W64 x := rfl

private theorem vll_withWidth_none {α : Type} (n : Nat)
    (hn : n ≠ 8 ∧ n ≠ 16 ∧ n ≠ 32 ∧ n ≠ 64)
    (k : ∀ w : Width, n = w.bits → Option α) : withWidth n k = none := by
  unfold withWidth
  split <;> first
    | exact absurd rfl hn.1 | exact absurd rfl hn.2.1
    | exact absurd rfl hn.2.2.1 | exact absurd rfl hn.2.2.2 | rfl

private theorem vll_withWidth_at_bits {α : Type} (w : Width)
    (k : ∀ w' : Width, w.bits = w'.bits → Option α) :
    withWidth w.bits k = k w rfl := by
  cases w <;> rfl

private theorem boolArgTo8I_ne_none (rd : Reg64) (pa : PArg Reg64 RegMm CondCode .bool)
    (hv : ∀ v, pa ≠ .vec v) : ∃ i, boolArgTo8I rd pa = some i := by
  cases pa with
  | vec v => exact absurd rfl (hv v)
  | gpr _ | imm _ | flag _ => exact ⟨_, rfl⟩

private theorem opBoolBinIns_ne_none_local (op : Bool → Bool → Bool)
    (insFn : Dst .W8 → Operand .W8 → Operation .W8)
    (pa pb : PArg Reg64 RegMm CondCode .bool) (rd : Reg64)
    (ha : ∀ v, pa ≠ .vec v) (hb : ∀ v, pb ≠ .vec v) :
    opBoolBinIns op insFn pa pb (.gpr rd) ≠ none := by
  have hself : ∀ (other : PArg Reg64 RegMm CondCode .bool), (∀ v, other ≠ .vec v) →
      boolBinSelfIns insFn rd other ≠ none := by
    intro other ho h
    dsimp only [boolBinSelfIns] at h
    cases other with
    | vec v => exact absurd rfl (ho v)
    | gpr _ => cases h
    | imm _ | flag _ =>
      obtain ⟨d2, hd2⟩ := boolArgTo8I_ne_none .r10 _ ho
      rw [hd2] at h; cases h
  have hdst : ∀ (a b : PArg Reg64 RegMm CondCode .bool),
      (∀ v, a ≠ .vec v) → (∀ v, b ≠ .vec v) → boolBinDstIns insFn rd a b ≠ none := by
    intro a b ha0 hb0 h
    dsimp only [boolBinDstIns] at h
    obtain ⟨d1, hd1⟩ := boolArgTo8I_ne_none rd a ha0
    rw [hd1] at h
    cases b with
    | vec v => exact absurd rfl (hb0 v)
    | gpr _ => cases h
    | imm _ | flag _ =>
      obtain ⟨d2, hd2⟩ := boolArgTo8I_ne_none .r10 _ hb0
      rw [hd2] at h; cases h
  intro hx
  dsimp only [opBoolBinIns] at hx
  cases pa with
  | vec v => exact absurd rfl (ha v)
  | gpr ra =>
    by_cases hra : (ra == rd) = true
    · simp only [hra, ↓reduceIte] at hx; exact hself pb hb hx
    · simp only [hra, Bool.false_eq_true, ↓reduceIte] at hx
      cases pb with
      | vec v => exact absurd rfl (hb v)
      | gpr rb =>
        by_cases hrb : (rb == rd) = true
        · simp only [hrb, ↓reduceIte] at hx; exact hself (.gpr ra) ha hx
        · simp only [hrb, Bool.false_eq_true, ↓reduceIte] at hx
          exact hdst (.gpr ra) (.gpr rb) ha hb hx
      | imm _ | flag _ => exact hdst _ _ hb ha hx
  | imm a =>
    cases pb with
    | vec v => exact absurd rfl (hb v)
    | imm b => cases hx
    | gpr rb =>
      by_cases hrb : (rb == rd) = true
      · simp only [hrb, ↓reduceIte] at hx; exact hself (.imm a) ha hx
      · simp only [hrb, Bool.false_eq_true, ↓reduceIte] at hx
        exact hdst (.imm a) (.gpr rb) ha hb hx
    | flag cc => exact hdst (.imm a) (.flag cc) ha hb hx
  | flag ca =>
    cases pb with
    | vec v => exact absurd rfl (hb v)
    | gpr rb =>
      by_cases hrb : (rb == rd) = true
      · simp only [hrb, ↓reduceIte] at hx; exact hself (.flag ca) ha hx
      · simp only [hrb, Bool.false_eq_true, ↓reduceIte] at hx
        exact hdst (.flag ca) (.gpr rb) ha hb hx
    | imm b => exact hdst (.flag ca) (.imm b) ha hb hx
    | flag cb => exact hdst (.flag ca) (.flag cb) ha hb hx

private theorem hnone_bool_bin_core (op : CoreAlu) (fn : Bool → Bool → Bool)
    (insFn : Dst .W8 → Operand .W8 → Operation .W8)
    (hop : (op = .and ∧ x64Op (.and .bool) =
        fun pas dsts _ => emitCleanPair (opBoolBinIns fn insFn pas.1 pas.2.1 dsts.1)) ∨
      (op = .or ∧ x64Op (.or .bool) =
        fun pas dsts _ => emitCleanPair (opBoolBinIns fn insFn pas.1 pas.2.1 dsts.1)) ∨
      (op = .xor ∧ x64Op (.xor .bool) =
        fun pas dsts _ => emitCleanPair (opBoolBinIns fn insFn pas.1 pas.2.1 dsts.1))) :
    ∀ pa' pb' pd' vh,
      x64Op (match op with | .and => .and .bool | .or => .or .bool | _ => .xor .bool)
        (pa', pb', ()) (pd', ()) vh = none →
      vllCoreBoolOrBits x64Arch op .bool pa' pb' pd' = none := by
  intro pa' pb' pd' vh hx
  cases pd' with
  | vec _ | flag _ => rfl
  | gpr rd =>
    by_cases ha : ∃ v, pa' = .vec v
    · rcases ha with ⟨v, rfl⟩; cases pb' <;> rfl
    · by_cases hb : ∃ v, pb' = .vec v
      · rcases hb with ⟨v, rfl⟩; cases pa' <;> rfl
      · exfalso
        apply opBoolBinIns_ne_none_local fn insFn pa' pb' rd
          (fun v e => ha ⟨v, e⟩) (fun v e => hb ⟨v, e⟩)
        rcases hop with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;>
          · dsimp only at hx; rw [h] at hx
            dsimp only [emitCleanPair, Option.map] at hx
            cases hres : opBoolBinIns fn insFn pa' pb' (.gpr rd)
            · rfl
            · rw [hres] at hx; cases hx

private theorem hnone_bin_core (op : CoreAlu) (k : AluBinKind) (n : Nat)
    (hk : (op = .mul ∧ k = .mul) ∨ (op = .add ∧ k = .add) ∨ (op = .sub ∧ k = .sub) ∨
          (op = .and ∧ k = .and) ∨ (op = .or ∧ k = .or) ∨ (op = .xor ∧ k = .xor))
    (pa' pb' : PArg Reg64 RegMm CondCode (.bits n)) (pd' : PDst Reg64 RegMm CondCode (.bits n))
    (vh : VariantHint)
    (hx : x64Op (match op with
        | .mul => .mul (.bits n) | .add => .add (.bits n) | .sub => .sub (.bits n)
        | .and => .and (.bits n) | .or => .or (.bits n) | .xor => .xor (.bits n)
        | _ => .add (.bits n)) (pa', pb', ()) (pd', ()) vh = none) :
    vllCoreBinTy x64Arch op (.bits n) pa' pb' pd' = none := by
  cases pd' with
  | vec _ => rfl
  | gpr rd =>
    by_cases hbw : ([8, 16, 32, 64] : List Nat).contains n = true
    · have hmn : ∃ xw : _root_.Width, n = xw.bits := by
        rcases (by simpa [List.contains_eq_mem] using hbw :
            n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) with rfl | rfl | rfl | rfl
        · exact ⟨.W8, rfl⟩
        · exact ⟨.W16, rfl⟩
        · exact ⟨.W32, rfl⟩
        · exact ⟨.W64, rfl⟩
      rcases hmn with ⟨xw, rfl⟩
      by_cases ha : ∃ v, pa' = .vec v
      · rcases ha with ⟨v, rfl⟩
        rcases hk with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;>
          cases xw <;> rfl
      · by_cases hb : ∃ v, pb' = .vec v
        · rcases hb with ⟨v, rfl⟩
          rcases hk with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;>
            cases xw <;> cases pa' <;> rfl
        · exfalso
          rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
            ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            cases xw <;>
              · dsimp only [x64Op, emitCleanPair, x64OpIns, Option.map] at hx
                rw [withWidth_parg2 _ (pa', pb')] at hx
                obtain ⟨res, hres⟩ := opBinIns_isSome _ _ pa' pb' rd vh
                  (fun v e => ha ⟨v, e⟩) (fun v e => hb ⟨v, e⟩)
                rw [hres] at hx; cases hx
    · exact vllCoreBinBits_none_of_not_bw op n (Bool.eq_false_iff.mpr hbw) pa' pb' rd

private theorem x64Op_copy_bool_gpr_ne_none (rs rd : Reg64) (vh : VariantHint) :
    x64Op (.copy .bool) (.gpr rs, ()) (.gpr rd, ()) vh ≠ none := by
  intro hx
  dsimp only [x64Op, x64OpIns, opCopyBoolIns, emitCleanPair, Option.map] at hx
  cases hc : (rs == rd)
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hx; cases hx
  · simp only [hc, ↓reduceIte] at hx; cases hx

private theorem x64Op_copy_bits_gpr_ne_none (xw : _root_.Width) (rs rd : Reg64)
    (vh : VariantHint) :
    x64Op (.copy (.bits xw.bits)) (.gpr rs, ()) (.gpr rd, ()) vh ≠ none := by
  intro hx
  dsimp only [x64Op, x64OpIns, emitCleanPair, Option.map] at hx
  rw [withWidth_parg xw (.gpr rs)] at hx
  dsimp only [opCopyBitsIns] at hx
  cases hc : (rs == rd)
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hx; cases hx
  · simp only [hc, ↓reduceIte] at hx; cases hx

private theorem x64Op_bitcast_bits_gpr_ne_none (xw : _root_.Width) (rs rd : Reg64)
    (vh : VariantHint) :
    x64Op (.bitcast (.bits xw.bits) (.bits xw.bits) rfl) (.gpr rs, ()) (.gpr rd, ()) vh ≠
      none := by
  intro hx
  have hbw : x64BitWidths.contains xw.bits = true := by cases xw <;> rfl
  dsimp only [x64Op, x64OpIns, emitCleanPair, Option.map] at hx
  rw [hbw] at hx
  simp only [↓reduceIte] at hx
  rw [withWidth_parg xw (.gpr rs)] at hx
  dsimp only [opCopyBitsIns] at hx
  cases hc : (rs == rd)
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hx; cases hx
  · simp only [hc, ↓reduceIte] at hx; cases hx

theorem vllX64_op_eq {sig rs : List Ty} (code : OpCode sig rs)
    (pas : Tup (PArg Reg64 RegMm CondCode) sig)
    (dsts : Tup (PDst Reg64 RegMm CondCode) rs) (vh : VariantHint)
    (hok : opNoSameExt code = true) :
    (vllX64Isa.gpr.op code pas dsts vh).map (fun (c0, cl) => (asmX64List c0, cl)) =
      x64Isa.gpr.op code pas dsts vh := by
  cases code with
  | copy t =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t with
    | float _ | pair _ _ =>
      exact vllGprOp_hook_fb_eq rfl fun _ => rfl
    | bool =>
      cases pd with
      | vec _ | flag _ =>
        exact vllGprOp_hook_fb_eq rfl fun _ => rfl
      | gpr rd =>
        cases pa with
        | vec v =>
          exact vllGprOp_hook_fb_eq rfl fun _ => rfl
        | gpr rs =>
          exact vllGprOp_hook_fb_eq rfl fun hx => absurd hx (x64Op_copy_bool_gpr_ne_none rs rd vh)
        | imm b =>
          exact vllGprOp_hook_none_eq rfl rfl
        | flag cc =>
          exact vllGprOp_hook_none_eq rfl rfl
    | bits n =>
      cases pd with
      | vec v =>
        exact vllGprOp_hook_fb_eq rfl fun _ => rfl
      | gpr rd =>
        by_cases hbw : ([8, 16, 32, 64] : List Nat).contains n = true
        · have hmn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 := by
            simpa [List.contains_eq_mem] using hbw
          have hbw' : x64BitWidths.contains n = true := hbw
          rcases hmn with rfl | rfl | rfl | rfl
          · cases pa with
            | vec v =>
              exact vllGprOp_hook_fb_eq rfl fun _ => rfl
            | gpr rs =>
              exact vllGprOp_hook_fb_eq rfl fun hx =>
                absurd hx (x64Op_copy_bits_gpr_ne_none .W8 rs rd vh)
            | imm cb =>
              exact vllGprOp_hook_none_eq rfl rfl
          · cases pa with
            | vec v =>
              exact vllGprOp_hook_fb_eq rfl fun _ => rfl
            | gpr rs =>
              exact vllGprOp_hook_fb_eq rfl fun hx =>
                absurd hx (x64Op_copy_bits_gpr_ne_none .W16 rs rd vh)
            | imm cb =>
              exact vllGprOp_hook_none_eq rfl rfl
          · cases pa with
            | vec v =>
              exact vllGprOp_hook_fb_eq rfl fun _ => rfl
            | imm cb =>
              exact vllGprOp_hook_none_eq rfl rfl
            | gpr rs =>
              by_cases hne : rs = rd
              · subst rs
                exact vllGprOp_hook_fb_eq
                  (by dsimp only [vllX64OpHook]
                      simp only [reg64_bne_self, x64BitWidths, Bool.and_false,
                        Bool.false_eq_true, ↓reduceIte]; try rfl)
                  fun hx => absurd hx (x64Op_copy_bits_gpr_ne_none .W32 rd rd vh)
              · have hbn : (rs != rd) = true := reg64_bne_of_ne hne
                have hbeq : (rs == rd) = false := reg64_beq_false_of_ne hne
                refine vllGprOp_hook_none_eq
                  (by dsimp only [vllX64OpHook]; simp only [hbn]; rfl) ?_
                dsimp only [vllCoreOp, vllCoreCopy, vllCoreCopyW, x64Arch, x64Frame,
                  Option.map, x64Op, x64OpIns, emitCleanPair]
                rw [show ([8, 16, 32, 64] : List Nat).contains 32 = true from rfl,
                  vll_withWidth_at_bits .w32, withWidth_parg32 (.gpr rs)]
                simp only [↓reduceIte, opCopyBitsIns, asmX64List, List.flatMap_cons,
                  List.flatMap_nil, List.append_nil, asmX64, Width.toX64, movSubWI, regW, hbeq,
                  Bool.false_eq_true]
                rfl
          · cases pa with
            | vec v =>
              exact vllGprOp_hook_fb_eq rfl fun _ => rfl
            | imm cb =>
              exact vllGprOp_hook_none_eq rfl rfl
            | gpr rs =>
              by_cases hne : rs = rd
              · subst rs
                exact vllGprOp_hook_fb_eq
                  (by dsimp only [vllX64OpHook]
                      simp only [reg64_bne_self, x64BitWidths, Bool.and_false,
                        Bool.false_eq_true, ↓reduceIte]; try rfl)
                  fun hx => absurd hx (x64Op_copy_bits_gpr_ne_none .W64 rd rd vh)
              · have hbn : (rs != rd) = true := reg64_bne_of_ne hne
                have hbeq : (rs == rd) = false := reg64_beq_false_of_ne hne
                refine vllGprOp_hook_none_eq
                  (by dsimp only [vllX64OpHook]; simp only [hbn]; rfl) ?_
                dsimp only [vllCoreOp, vllCoreCopy, vllCoreCopyW, x64Arch, x64Frame,
                  Option.map, x64Op, x64OpIns, emitCleanPair]
                rw [show ([8, 16, 32, 64] : List Nat).contains 64 = true from rfl,
                  vll_withWidth_at_bits .w64, withWidth_parg64 (.gpr rs)]
                simp only [↓reduceIte, opCopyBitsIns, asmX64List, List.flatMap_cons,
                  List.flatMap_nil, List.append_nil, asmX64, Width.toX64, movSubWI, regW, hbeq,
                  Bool.false_eq_true]
                rfl
        · have hbwf : ([8, 16, 32, 64] : List Nat).contains n = false := Bool.eq_false_iff.mpr hbw
          have hbwf' : x64BitWidths.contains n = false := hbwf
          refine vllGprOp_hook_fb_eq (by dsimp only [vllX64OpHook]; rw [hbwf']; rfl) fun _ => by
            dsimp only [vllCoreOp, vllCoreCopy, x64Arch, x64Frame]
            rw [hbwf]; rfl
  | bitcast t u hb =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t with
    | bool | float _ | pair _ _ =>
      exact vllGprOp_hook_fb_eq rfl fun _ => rfl
    | bits m =>
      cases u with
      | bool | float _ | pair _ _ =>
        exact vllGprOp_hook_fb_eq rfl fun _ => rfl
      | bits n =>
        have hmn : m = n := by simpa [Ty.size] using hb
        subst hmn
        cases pd with
        | vec v =>
          exact vllGprOp_hook_fb_eq rfl fun _ => rfl
        | gpr rd =>
          by_cases hbm : ([8, 16, 32, 64] : List Nat).contains m = true
          · have hm : m = 8 ∨ m = 16 ∨ m = 32 ∨ m = 64 := by
              simpa [List.contains_eq_mem] using hbm
            have hbm' : x64BitWidths.contains m = true := hbm
            rcases hm with rfl | rfl | rfl | rfl
            · cases pa with
              | vec v =>
                exact vllGprOp_hook_fb_eq rfl fun _ => rfl
              | gpr rs =>
                exact vllGprOp_hook_fb_eq rfl fun hx =>
                  absurd hx (x64Op_bitcast_bits_gpr_ne_none .W8 rs rd vh)
              | imm cb =>
                exact vllGprOp_hook_none_eq rfl rfl
            · cases pa with
              | vec v =>
                exact vllGprOp_hook_fb_eq rfl fun _ => rfl
              | gpr rs =>
                exact vllGprOp_hook_fb_eq rfl fun hx =>
                  absurd hx (x64Op_bitcast_bits_gpr_ne_none .W16 rs rd vh)
              | imm cb =>
                exact vllGprOp_hook_none_eq rfl rfl
            · cases pa with
              | vec v =>
                exact vllGprOp_hook_fb_eq rfl fun _ => rfl
              | imm cb =>
                exact vllGprOp_hook_none_eq rfl rfl
              | gpr rs =>
                by_cases hne : rs = rd
                · subst rs
                  exact vllGprOp_hook_fb_eq
                    (by dsimp only [vllX64OpHook]
                        simp only [reg64_bne_self, x64BitWidths, Bool.and_false,
                          Bool.false_eq_true, ↓reduceIte]; try rfl)
                    fun hx => absurd hx (x64Op_bitcast_bits_gpr_ne_none .W32 rd rd vh)
                · have hbn2 : (rs != rd) = true := reg64_bne_of_ne hne
                  have hbeq : (rs == rd) = false := reg64_beq_false_of_ne hne
                  refine vllGprOp_hook_none_eq
                    (by dsimp only [vllX64OpHook]; simp only [hbn2]; rfl) ?_
                  dsimp only [vllCoreOp, vllCoreBitcast, vllCoreCopyW, x64Arch, x64Frame,
                    Option.map, x64Op, x64OpIns, emitCleanPair]
                  rw [show ([8, 16, 32, 64] : List Nat).contains 32 = true from rfl,
                    show x64BitWidths.contains 32 = true from rfl, vll_withWidth_at_bits .w32]
                  simp only [↓reduceIte]
                  rw [withWidth_parg32 (.gpr rs)]
                  simp only [opCopyBitsIns, asmX64List, List.flatMap_cons,
                    List.flatMap_nil, List.append_nil, asmX64, Width.toX64, movSubWI, regW, hbeq,
                    Bool.false_eq_true, ↓reduceIte]
                  rfl
            · cases pa with
              | vec v =>
                exact vllGprOp_hook_fb_eq rfl fun _ => rfl
              | imm cb =>
                exact vllGprOp_hook_none_eq rfl rfl
              | gpr rs =>
                by_cases hne : rs = rd
                · subst rs
                  exact vllGprOp_hook_fb_eq
                    (by dsimp only [vllX64OpHook]
                        simp only [reg64_bne_self, x64BitWidths, Bool.and_false,
                          Bool.false_eq_true, ↓reduceIte]; try rfl)
                    fun hx => absurd hx (x64Op_bitcast_bits_gpr_ne_none .W64 rd rd vh)
                · have hbn2 : (rs != rd) = true := reg64_bne_of_ne hne
                  have hbeq : (rs == rd) = false := reg64_beq_false_of_ne hne
                  refine vllGprOp_hook_none_eq
                    (by dsimp only [vllX64OpHook]; simp only [hbn2]; rfl) ?_
                  dsimp only [vllCoreOp, vllCoreBitcast, vllCoreCopyW, x64Arch, x64Frame,
                    Option.map, x64Op, x64OpIns, emitCleanPair]
                  rw [show ([8, 16, 32, 64] : List Nat).contains 64 = true from rfl,
                    show x64BitWidths.contains 64 = true from rfl, vll_withWidth_at_bits .w64]
                  simp only [↓reduceIte]
                  rw [withWidth_parg64 (.gpr rs)]
                  simp only [opCopyBitsIns, asmX64List, List.flatMap_cons,
                    List.flatMap_nil, List.append_nil, asmX64, Width.toX64, movSubWI, regW, hbeq,
                    Bool.false_eq_true, ↓reduceIte]
                  rfl
          · have hbmf : ([8, 16, 32, 64] : List Nat).contains m = false := Bool.eq_false_iff.mpr hbm
            have hbmf' : x64BitWidths.contains m = false := hbmf
            refine vllGprOp_hook_fb_eq (by dsimp only [vllX64OpHook]; rw [hbmf']; rfl) fun _ => by
              dsimp only [vllCoreOp, vllCoreBitcast, x64Arch, x64Frame]
              rw [hbmf]; rfl
  | trunc m n =>
    have hne_mn : m ≠ n := by simpa [opNoSameExt] using hok
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    have hnone_trunc : ∀ pd' pa',
        x64Op (.trunc m n) (pa', ()) (pd', ()) vh = none →
        vllCoreOp x64Arch (some ∘ condOf) (.trunc m n) (pa', ()) (pd', ()) vh = none := by
      intro pd' pa' hx
      cases pd' with
      | vec _ => rfl
      | gpr rd =>
        dsimp only [vllCoreOp, vllCoreTrunc]
        cases hw_m : Width.ofBits? m with
        | none => rfl
        | some wm =>
          simp only [Option.isSome, ↓reduceIte]
          dsimp only [x64Arch, x64Frame]
          by_cases hm_bw : ([8, 16, 32, 64] : List Nat).contains m = true
          · by_cases hn_bw : ([8, 16, 32, 64] : List Nat).contains n = true
            · have hm_mem : m = 8 ∨ m = 16 ∨ m = 32 ∨ m = 64 := by
                simpa [List.contains_eq_mem] using hm_bw
              have hn_mem : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 := by
                simpa [List.contains_eq_mem] using hn_bw
              by_cases hlt : Nat.ble (n + 1) m = true
              · cases pa' with
                | vec v =>
                  have hvec : ∀ wn : Width, vllCoreTruncW x64Arch m wn (.vec v) rd = none :=
                    fun wn => by dsimp only [vllCoreTruncW]; split <;> rfl
                  rcases hn_mem with rfl | rfl | rfl | rfl <;>
                    (dsimp only [withWidth]; exact hvec _)
                | imm _ =>
                  exfalso
                  have hlt_le := Nat.ble_eq.mp hlt
                  have hm_bw' : x64BitWidths.contains m = true := hm_bw
                  have hn_bw' : x64BitWidths.contains n = true := hn_bw
                  dsimp only [x64Op, x64OpIns, opTruncIns, emitCleanPair] at hx
                  simp only [hm_bw', hn_bw', hlt, Bool.true_and, Bool.not_true,
                    Bool.false_eq_true, ↓reduceIte, Option.map] at hx
                  rcases hn_mem with rfl | rfl | rfl | rfl <;> first | omega | cases hx
                | gpr r =>
                  exfalso
                  have hlt_le := Nat.ble_eq.mp hlt
                  have hm_bw' : x64BitWidths.contains m = true := hm_bw
                  have hn_bw' : x64BitWidths.contains n = true := hn_bw
                  dsimp only [x64Op, x64OpIns, opTruncIns, emitCleanPair] at hx
                  simp only [hm_bw', hn_bw', hlt, Bool.true_and, Bool.not_true,
                    Bool.false_eq_true, ↓reduceIte, Option.map] at hx
                  rcases hn_mem with rfl | rfl | rfl | rfl <;> first
                    | omega
                    | (cases h : (r == rd) <;>
                        simp only [h, Bool.false_eq_true, ↓reduceIte] at hx <;> cases hx)
              · have hltf : Nat.ble n m = false := by
                  cases h1 : Nat.ble n m
                  · rfl
                  · exfalso; apply hlt; apply Nat.ble_eq.mpr; have := Nat.ble_eq.mp h1; omega
                rcases hn_mem with rfl | rfl | rfl | rfl <;>
                  (dsimp only [withWidth, vllCoreTruncW, x64Arch, x64Frame]
                   simp only [hm_bw, hn_bw, hltf, Bool.true_and, Bool.and_false,
                     Bool.false_eq_true, ↓reduceIte])
            · have hn_f := Bool.eq_false_iff.mpr hn_bw
              by_cases hn8 : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64
              · rcases hn8 with rfl | rfl | rfl | rfl <;>
                  (dsimp only [withWidth, vllCoreTruncW, x64Arch, x64Frame]
                   simp only [hm_bw, hn_f, Bool.true_and, Bool.false_and,
                     Bool.false_eq_true, ↓reduceIte])
              · have hn' : n ≠ 8 ∧ n ≠ 16 ∧ n ≠ 32 ∧ n ≠ 64 :=
                  ⟨fun e => hn8 (Or.inl e), fun e => hn8 (Or.inr (Or.inl e)),
                   fun e => hn8 (Or.inr (Or.inr (Or.inl e))),
                   fun e => hn8 (Or.inr (Or.inr (Or.inr e)))⟩
                exact vll_withWidth_none n hn' _
          · have hm_f := Bool.eq_false_iff.mpr hm_bw
            by_cases hn8 : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64
            · rcases hn8 with rfl | rfl | rfl | rfl <;>
                (dsimp only [withWidth, vllCoreTruncW, x64Arch, x64Frame]
                 simp only [hm_f, Bool.false_and, Bool.false_eq_true, ↓reduceIte])
            · have hn' : n ≠ 8 ∧ n ≠ 16 ∧ n ≠ 32 ∧ n ≠ 64 :=
                ⟨fun e => hn8 (Or.inl e), fun e => hn8 (Or.inr (Or.inl e)),
                 fun e => hn8 (Or.inr (Or.inr (Or.inl e))),
                 fun e => hn8 (Or.inr (Or.inr (Or.inr e)))⟩
              exact vll_withWidth_none n hn' _
    cases pd with
    | vec v =>
      exact vllGprOp_hook_fb_eq rfl (hnone_trunc _ _)
    | gpr rd =>
      by_cases hm64 : m = 64 <;> by_cases hn32 : n = 32
      · subst hm64 hn32
        cases pa with
        | vec v =>
          exact vllGprOp_hook_fb_eq rfl (hnone_trunc _ _)
        | imm cb =>
          exact vllGprOp_hook_none_eq rfl rfl
        | gpr rs =>
          by_cases hne : rs = rd
          · subst rs
            exact vllGprOp_hook_fb_eq
              (by dsimp only [vllX64OpHook]
                  simp only [reg64_bne_self, Bool.false_eq_true, ↓reduceIte]; try rfl)
              (hnone_trunc _ _)
          · have hbn : (rs != rd) = true := reg64_bne_of_ne hne
            have hbeq : (rs == rd) = false := reg64_beq_false_of_ne hne
            refine vllGprOp_hook_none_eq
              (by dsimp only [vllX64OpHook]; simp only [hbn, ↓reduceIte]; try rfl) ?_
            dsimp only [vllCoreOp, vllCoreTrunc, vllCoreTruncW, withWidth, x64Arch, x64Frame,
              x64Op, x64OpIns, opTruncIns, emitCleanPair, Option.map]
            rw [hbeq]
            rfl
      · have hcf : (m == 64 && n == 32) = false := by
          cases h1 : (m == 64) <;> cases h2 : (n == 32) <;> try rfl
          exact absurd (beq_iff_eq.mp h2) hn32
        exact vllGprOp_hook_fb_eq
          (by dsimp only [vllX64OpHook]; simp only [hcf, Bool.false_eq_true, ↓reduceIte]; try rfl)
          (hnone_trunc _ _)
      · have hcf : (m == 64 && n == 32) = false := by
          cases h1 : (m == 64) <;> cases h2 : (n == 32) <;> try rfl
          exact absurd (beq_iff_eq.mp h1) hm64
        exact vllGprOp_hook_fb_eq
          (by dsimp only [vllX64OpHook]; simp only [hcf, Bool.false_eq_true, ↓reduceIte]; try rfl)
          (hnone_trunc _ _)
      · have hcf : (m == 64 && n == 32) = false := by
          cases h1 : (m == 64) <;> cases h2 : (n == 32) <;> try rfl
          exact absurd (beq_iff_eq.mp h1) hm64
        exact vllGprOp_hook_fb_eq
          (by dsimp only [vllX64OpHook]; simp only [hcf, Bool.false_eq_true, ↓reduceIte]; try rfl)
          (hnone_trunc _ _)
  | mul t =>
    cases t with
    | bool | float _ | pair _ _ =>
      rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
      exact vllGprOp_hook_fb_eq rfl fun _ => rfl
    | bits n =>
      rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
      have hn : ∀ pa' pb' pd',
          x64Op (.mul (.bits n)) (pa', pb', ()) (pd', ()) vh = none →
          vllCoreOp x64Arch (some ∘ condOf) (.mul (.bits n)) (pa', pb', ()) (pd', ()) vh = none :=
        fun pa' pb' pd' hx => hnone_bin_core .mul .mul n (Or.inl ⟨rfl, rfl⟩) pa' pb' pd' vh hx
      cases pd with
      | vec v =>
        exact vllGprOp_hook_fb_eq rfl (hn _ _ _)
      | gpr rd =>
        by_cases hwn : n = 16 ∨ n = 32 ∨ n = 64
        · have hcond : (n == 16 || n == 32 || n == 64) = true := by
            rcases hwn with rfl | rfl | rfl <;> rfl
          cases pa with
          | vec v =>
            exact vllGprOp_hook_fb_eq
              (by dsimp only [vllX64OpHook]; simp only [hcond, ↓reduceIte]; try rfl) (hn _ _ _)
          | imm ca =>
            exact vllGprOp_hook_fb_eq
              (by dsimp only [vllX64OpHook]; simp only [hcond, ↓reduceIte]; try rfl) (hn _ _ _)
          | gpr ra =>
            by_cases hrr : ra = rd
            · subst ra
              cases pb with
              | vec v =>
                exact vllGprOp_hook_fb_eq
                  (by dsimp only [vllX64OpHook]; simp only [hcond, ↓reduceIte]; try rfl)
                  (hn _ _ _)
              | gpr rb =>
                refine vllGprOp_hook_none_eq
                  (by dsimp only [vllX64OpHook]
                      simp only [hcond, reg64_beq_self, ↓reduceIte]; try rfl) ?_
                have hxw : ∃ xw : Width, n = xw.bits ∧ (xw = .w16 ∨ xw = .w32 ∨ xw = .w64) := by
                  rcases hwn with rfl | rfl | rfl
                  · exact ⟨.w16, rfl, Or.inl rfl⟩
                  · exact ⟨.w32, rfl, Or.inr (Or.inl rfl)⟩
                  · exact ⟨.w64, rfl, Or.inr (Or.inr rfl)⟩
                obtain ⟨xw, rfl, hxw'⟩ := hxw
                have hbw' : ([8, 16, 32, 64] : List Nat).contains xw.bits = true := by
                  rcases hxw' with rfl | rfl | rfl <;> rfl
                dsimp only [vllCoreOp, vllCoreBinTy, vllCoreBinBits, x64Arch, x64Frame, x64Op,
                  x64OpIns]
                rw [show ([8, 16, 32, 64] : List Nat).contains xw.bits = true from by
                    cases xw <;> rfl,
                  vll_withWidth_at_bits xw, withWidth_vll_parg2 xw (.gpr rd, .gpr rb)]
                simpa only [↓reduceIte, cast_eq] using
                  asmX64List_mul_core_eq xw hxw' rd (.gpr rb) vh
              | imm cb =>
                refine vllGprOp_hook_none_eq
                  (by dsimp only [vllX64OpHook]
                      simp only [hcond, reg64_beq_self, ↓reduceIte]; try rfl) ?_
                have hxw : ∃ xw : Width, n = xw.bits ∧ (xw = .w16 ∨ xw = .w32 ∨ xw = .w64) := by
                  rcases hwn with rfl | rfl | rfl
                  · exact ⟨.w16, rfl, Or.inl rfl⟩
                  · exact ⟨.w32, rfl, Or.inr (Or.inl rfl)⟩
                  · exact ⟨.w64, rfl, Or.inr (Or.inr rfl)⟩
                obtain ⟨xw, rfl, hxw'⟩ := hxw
                have hbw' : ([8, 16, 32, 64] : List Nat).contains xw.bits = true := by
                  rcases hxw' with rfl | rfl | rfl <;> rfl
                dsimp only [vllCoreOp, vllCoreBinTy, vllCoreBinBits, x64Arch, x64Frame, x64Op,
                  x64OpIns]
                rw [show ([8, 16, 32, 64] : List Nat).contains xw.bits = true from by
                    cases xw <;> rfl,
                  vll_withWidth_at_bits xw, withWidth_vll_parg2 xw (.gpr rd, .imm cb)]
                simpa only [↓reduceIte, cast_eq] using
                  asmX64List_mul_core_eq xw hxw' rd (.imm cb) vh
            · have hrf : (ra == rd) = false := reg64_beq_false_of_ne hrr
              cases pb with
              | vec v =>
                exact vllGprOp_hook_fb_eq
                  (by dsimp only [vllX64OpHook]; simp only [hcond, ↓reduceIte]; try rfl)
                  (hn _ _ _)
              | gpr rb =>
                exact vllGprOp_hook_fb_eq
                  (by dsimp only [vllX64OpHook]
                      simp only [hcond, hrf, Bool.false_eq_true, ↓reduceIte]; try rfl) (hn _ _ _)
              | imm cb =>
                exact vllGprOp_hook_fb_eq
                  (by dsimp only [vllX64OpHook]
                      simp only [hcond, hrf, Bool.false_eq_true, ↓reduceIte]; try rfl) (hn _ _ _)
        · have hnot : (n == 16 || n == 32 || n == 64) = false := by
            cases h16 : (n == 16) <;> cases h32 : (n == 32) <;> cases h64 : (n == 64) <;> try rfl
            · exact absurd (Or.inr (Or.inr (beq_iff_eq.mp h64))) hwn
            · exact absurd (Or.inr (Or.inl (beq_iff_eq.mp h32))) hwn
            · exact absurd (Or.inr (Or.inl (beq_iff_eq.mp h32))) hwn
            all_goals exact absurd (Or.inl (beq_iff_eq.mp h16)) hwn
          exact vllGprOp_hook_fb_eq
            (by dsimp only [vllX64OpHook]; simp only [hnot, Bool.false_eq_true, ↓reduceIte]
                try rfl) (hn _ _ _)
  | add t =>
    cases t with
    | bool | float _ | pair _ _ =>
      rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
      exact vllGprOp_hook_fb_eq rfl fun _ => rfl
    | bits n =>
      rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
      have hn : ∀ pa' pb' pd',
          x64Op (.add (.bits n)) (pa', pb', ()) (pd', ()) vh = none →
          vllCoreOp x64Arch (some ∘ condOf) (.add (.bits n)) (pa', pb', ()) (pd', ()) vh = none :=
        fun pa' pb' pd' hx => hnone_bin_core .add .add n (Or.inr (Or.inl ⟨rfl, rfl⟩)) _ _ _ vh hx
      cases pd with
      | vec v =>
        exact vllGprOp_hook_fb_eq rfl (hn _ _ _)
      | gpr rd =>
        cases hw : vllX64WidthOfBits? n with
        | none =>
          exact vllGprOp_hook_fb_eq (by dsimp only [vllX64OpHook]; rw [hw]; try rfl) (hn _ _ _)
        | some w =>
          obtain rfl := vllX64WidthOfBits_eq_opt hw
          cases vh with
          | adcx | adox | mulxFast | decInc | disp _ =>
            exact vllGprOp_hook_fb_eq (by dsimp only [vllX64OpHook]; rw [hw]; try rfl) (hn _ _ _)
          | default =>
            cases pa with
            | imm ca =>
              exact vllGprOp_hook_fb_eq (by dsimp only [vllX64OpHook]; rw [hw]; try rfl) (hn _ _ _)
            | vec v =>
              exact vllGprOp_hook_fb_eq (by dsimp only [vllX64OpHook]; rw [hw]; try rfl) (hn _ _ _)
            | gpr ra =>
              by_cases hrr : ra = rd
              · subst ra
                cases pb with
                | vec v =>
                  exact vllGprOp_hook_fb_eq
                    (by dsimp only [vllX64OpHook]; rw [hw]
                        simp only [reg64_beq_self, ↓reduceIte]; try rfl) (hn _ _ _)
                | gpr rb =>
                  refine vllGprOp_hook_some_eq [.alu .add w rd rd (.reg rb) true] maskAll
                    (by dsimp only [vllX64OpHook]; rw [hw]
                        simp only [reg64_beq_self, ↓reduceIte]; try rfl) ?_
                  dsimp only [x64Op, x64OpIns]
                  rw [withWidth_vll_parg2 w (.gpr rd, .gpr rb)]
                  exact asmX64List_aluBin_hook_eq w .add rd rd (.gpr rb)
                    (Or.inl (reg64_beq_self rd)) (Or.inl ⟨rfl, rfl⟩)
                | imm cb =>
                  refine vllGprOp_hook_some_eq
                    [.alu .add w rd rd (.imm (cb.setWidth 64)) true] maskAll
                    (by dsimp only [vllX64OpHook]; rw [hw]
                        simp only [reg64_beq_self, ↓reduceIte]; try rfl) ?_
                  dsimp only [x64Op, x64OpIns]
                  rw [withWidth_vll_parg2 w (.gpr rd, .imm cb)]
                  exact asmX64List_aluBin_hook_eq w .add rd rd (.imm cb)
                    (Or.inl (reg64_beq_self rd)) (Or.inl ⟨rfl, rfl⟩)
              · have hrf : (ra == rd) = false := reg64_beq_false_of_ne hrr
                exact vllGprOp_hook_fb_eq
                  (by dsimp only [vllX64OpHook]; rw [hw]
                      simp only [hrf, Bool.false_eq_true, ↓reduceIte]; try rfl) (hn _ _ _)
  | sub t =>
    cases t with
    | bool | float _ | pair _ _ =>
      rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
      exact vllGprOp_hook_fb_eq rfl fun _ => rfl
    | bits n =>
      rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
      have hn : ∀ pa' pb' pd',
          x64Op (.sub (.bits n)) (pa', pb', ()) (pd', ()) vh = none →
          vllCoreOp x64Arch (some ∘ condOf) (.sub (.bits n)) (pa', pb', ()) (pd', ()) vh = none :=
        fun pa' pb' pd' hx =>
          hnone_bin_core .sub .sub n (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) _ _ _ vh hx
      cases pd with
      | vec v =>
        exact vllGprOp_hook_fb_eq rfl (hn _ _ _)
      | gpr rd =>
        cases hw : vllX64WidthOfBits? n with
        | none =>
          exact vllGprOp_hook_fb_eq (by dsimp only [vllX64OpHook]; rw [hw]; try rfl) (hn _ _ _)
        | some w =>
          obtain rfl := vllX64WidthOfBits_eq_opt hw
          cases vh with
          | adcx | adox | mulxFast | decInc | disp _ =>
            exact vllGprOp_hook_fb_eq (by dsimp only [vllX64OpHook]; rw [hw]; try rfl) (hn _ _ _)
          | default =>
            cases pa with
            | imm ca =>
              exact vllGprOp_hook_fb_eq (by dsimp only [vllX64OpHook]; rw [hw]; try rfl) (hn _ _ _)
            | vec v =>
              exact vllGprOp_hook_fb_eq (by dsimp only [vllX64OpHook]; rw [hw]; try rfl) (hn _ _ _)
            | gpr ra =>
              by_cases hrr : ra = rd
              · subst ra
                cases pb with
                | vec v =>
                  exact vllGprOp_hook_fb_eq
                    (by dsimp only [vllX64OpHook]; rw [hw]
                        simp only [reg64_beq_self, ↓reduceIte]; try rfl) (hn _ _ _)
                | gpr rb =>
                  refine vllGprOp_hook_some_eq [.alu .sub w rd rd (.reg rb) true] maskAll
                    (by dsimp only [vllX64OpHook]; rw [hw]
                        simp only [reg64_beq_self, ↓reduceIte]; try rfl) ?_
                  dsimp only [x64Op, x64OpIns]
                  rw [withWidth_vll_parg2 w (.gpr rd, .gpr rb)]
                  exact asmX64List_aluBin_hook_eq w .sub rd rd (.gpr rb)
                    (Or.inl (reg64_beq_self rd)) (Or.inr (Or.inl ⟨rfl, rfl⟩))
                | imm cb =>
                  refine vllGprOp_hook_some_eq
                    [.alu .sub w rd rd (.imm (cb.setWidth 64)) true] maskAll
                    (by dsimp only [vllX64OpHook]; rw [hw]
                        simp only [reg64_beq_self, ↓reduceIte]; try rfl) ?_
                  dsimp only [x64Op, x64OpIns]
                  rw [withWidth_vll_parg2 w (.gpr rd, .imm cb)]
                  exact asmX64List_aluBin_hook_eq w .sub rd rd (.imm cb)
                    (Or.inl (reg64_beq_self rd)) (Or.inr (Or.inl ⟨rfl, rfl⟩))
              · have hrf : (ra == rd) = false := reg64_beq_false_of_ne hrr
                exact vllGprOp_hook_fb_eq
                  (by dsimp only [vllX64OpHook]; rw [hw]
                      simp only [hrf, Bool.false_eq_true, ↓reduceIte]; try rfl) (hn _ _ _)
  | and t =>
    have hnone_and : ∀ pa' pb' pd',
        x64Op (.and t) (pa', pb', ()) (pd', ()) vh = none →
        vllCoreOp x64Arch (some ∘ condOf) (.and t) (pa', pb', ()) (pd', ()) vh = none := by
      intro pa' pb' pd' hx
      cases t with
      | float _ | pair _ _ => rfl
      | bool =>
        exact hnone_bool_bin_core .and (· && ·) .and (Or.inl ⟨rfl, rfl⟩) pa' pb' pd' vh hx
      | bits n =>
        have h1 := hnone_bin_core .and .and n (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
          pa' pb' pd' vh hx
        cases pd' with
        | vec _ => rfl
        | gpr _ => exact h1
    cases t with
    | bool | float _ | pair _ _ =>
      rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
      exact vllGprOp_hook_fb_eq rfl (hnone_and _ _ _)
    | bits n =>
      rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
      cases pd with
      | vec v =>
        exact vllGprOp_hook_fb_eq rfl (hnone_and _ _ _)
      | gpr rd =>
        cases hw : vllX64WidthOfBits? n with
        | none =>
          exact vllGprOp_hook_fb_eq
            (by dsimp only [vllX64OpHook]; rw [hw]; try rfl) (hnone_and _ _ _)
        | some w =>
          obtain rfl := vllX64WidthOfBits_eq_opt hw
          cases vh with
          | adcx | adox | mulxFast | decInc | disp _ =>
            exact vllGprOp_hook_fb_eq
              (by dsimp only [vllX64OpHook]; rw [hw]; try rfl) (hnone_and _ _ _)
          | default =>
            cases pa with
            | imm ca =>
              exact vllGprOp_hook_fb_eq
                (by dsimp only [vllX64OpHook]; rw [hw]; try rfl) (hnone_and _ _ _)
            | vec v =>
              exact vllGprOp_hook_fb_eq
                (by dsimp only [vllX64OpHook]; rw [hw]; try rfl) (hnone_and _ _ _)
            | gpr ra =>
              by_cases hcond : (ra == rd || w.bits == 32 || w.bits == 64) = true
              · have hwide : (ra == rd) = true ∨ w = .w32 ∨ w = .w64 := by
                  by_cases hrr : (ra == rd) = true
                  · exact Or.inl hrr
                  · cases w <;> simp only [hrr, Bool.false_or] at hcond <;> first
                      | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)
                      | (exfalso; revert hcond; decide)
                cases pb with
                | vec v =>
                  exact vllGprOp_hook_fb_eq
                    (by dsimp only [vllX64OpHook]; rw [hw]
                        simp only [hcond, ↓reduceIte]; try rfl) (hnone_and _ _ _)
                | gpr rb =>
                  refine vllGprOp_hook_some_eq [.alu .and w rd ra (.reg rb) true] maskAll
                    (by dsimp only [vllX64OpHook]; rw [hw]
                        simp only [hcond, ↓reduceIte]; try rfl) ?_
                  dsimp only [x64Op, x64OpIns]
                  rw [withWidth_vll_parg2 w (.gpr ra, .gpr rb)]
                  exact asmX64List_aluBin_hook_eq w .and rd ra (.gpr rb) hwide
                    (Or.inr (Or.inr (Or.inl rfl)))
                | imm cb =>
                  refine vllGprOp_hook_some_eq
                    [.alu .and w rd ra (.imm (cb.setWidth 64)) true] maskAll
                    (by dsimp only [vllX64OpHook]; rw [hw]
                        simp only [hcond, ↓reduceIte]; try rfl) ?_
                  dsimp only [x64Op, x64OpIns]
                  rw [withWidth_vll_parg2 w (.gpr ra, .imm cb)]
                  exact asmX64List_aluBin_hook_eq w .and rd ra (.imm cb) hwide
                    (Or.inr (Or.inr (Or.inl rfl)))
              · have hcf : (ra == rd || w.bits == 32 || w.bits == 64) = false :=
                  Bool.eq_false_iff.mpr hcond
                exact vllGprOp_hook_fb_eq
                  (by dsimp only [vllX64OpHook]; rw [hw]
                      simp only [hcf, Bool.false_eq_true, ↓reduceIte]; try rfl) (hnone_and _ _ _)
  | or t =>
    have hnone_or : ∀ pa' pb' pd',
        x64Op (.or t) (pa', pb', ()) (pd', ()) vh = none →
        vllCoreOp x64Arch (some ∘ condOf) (.or t) (pa', pb', ()) (pd', ()) vh = none := by
      intro pa' pb' pd' hx
      cases t with
      | float _ | pair _ _ => rfl
      | bool =>
        exact hnone_bool_bin_core .or (· || ·) .or (Or.inr (Or.inl ⟨rfl, rfl⟩)) pa' pb' pd' vh hx
      | bits n =>
        have h1 := hnone_bin_core .or .or n
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))) pa' pb' pd' vh hx
        cases pd' with
        | vec _ => rfl
        | gpr _ => exact h1
    cases t with
    | bool | float _ | pair _ _ =>
      rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
      exact vllGprOp_hook_fb_eq rfl (hnone_or _ _ _)
    | bits n =>
      rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
      cases pd with
      | vec v =>
        exact vllGprOp_hook_fb_eq rfl (hnone_or _ _ _)
      | gpr rd =>
        cases hw : vllX64WidthOfBits? n with
        | none =>
          exact vllGprOp_hook_fb_eq
            (by dsimp only [vllX64OpHook]; rw [hw]; try rfl) (hnone_or _ _ _)
        | some w =>
          obtain rfl := vllX64WidthOfBits_eq_opt hw
          cases vh with
          | adcx | adox | mulxFast | decInc | disp _ =>
            exact vllGprOp_hook_fb_eq
              (by dsimp only [vllX64OpHook]; rw [hw]; try rfl) (hnone_or _ _ _)
          | default =>
            cases pa with
            | imm ca =>
              exact vllGprOp_hook_fb_eq
                (by dsimp only [vllX64OpHook]; rw [hw]; try rfl) (hnone_or _ _ _)
            | vec v =>
              exact vllGprOp_hook_fb_eq
                (by dsimp only [vllX64OpHook]; rw [hw]; try rfl) (hnone_or _ _ _)
            | gpr ra =>
              by_cases hcond : (ra == rd || w.bits == 32 || w.bits == 64) = true
              · have hwide : (ra == rd) = true ∨ w = .w32 ∨ w = .w64 := by
                  by_cases hrr : (ra == rd) = true
                  · exact Or.inl hrr
                  · cases w <;> simp only [hrr, Bool.false_or] at hcond <;> first
                      | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)
                      | (exfalso; revert hcond; decide)
                cases pb with
                | vec v =>
                  exact vllGprOp_hook_fb_eq
                    (by dsimp only [vllX64OpHook]; rw [hw]
                        simp only [hcond, ↓reduceIte]; try rfl) (hnone_or _ _ _)
                | gpr rb =>
                  refine vllGprOp_hook_some_eq [.alu .or w rd ra (.reg rb) true] maskAll
                    (by dsimp only [vllX64OpHook]; rw [hw]
                        simp only [hcond, ↓reduceIte]; try rfl) ?_
                  dsimp only [x64Op, x64OpIns]
                  rw [withWidth_vll_parg2 w (.gpr ra, .gpr rb)]
                  exact asmX64List_aluBin_hook_eq w .or rd ra (.gpr rb) hwide
                    (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
                | imm cb =>
                  refine vllGprOp_hook_some_eq
                    [.alu .or w rd ra (.imm (cb.setWidth 64)) true] maskAll
                    (by dsimp only [vllX64OpHook]; rw [hw]
                        simp only [hcond, ↓reduceIte]; try rfl) ?_
                  dsimp only [x64Op, x64OpIns]
                  rw [withWidth_vll_parg2 w (.gpr ra, .imm cb)]
                  exact asmX64List_aluBin_hook_eq w .or rd ra (.imm cb) hwide
                    (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
              · have hcf : (ra == rd || w.bits == 32 || w.bits == 64) = false :=
                  Bool.eq_false_iff.mpr hcond
                exact vllGprOp_hook_fb_eq
                  (by dsimp only [vllX64OpHook]; rw [hw]
                      simp only [hcf, Bool.false_eq_true, ↓reduceIte]; try rfl) (hnone_or _ _ _)
  | xor t =>
    have hnone_xor : ∀ pa' pb' pd',
        x64Op (.xor t) (pa', pb', ()) (pd', ()) vh = none →
        vllCoreOp x64Arch (some ∘ condOf) (.xor t) (pa', pb', ()) (pd', ()) vh = none := by
      intro pa' pb' pd' hx
      cases t with
      | float _ | pair _ _ => rfl
      | bool =>
        exact hnone_bool_bin_core .xor (· ^^ ·) .xor (Or.inr (Or.inr ⟨rfl, rfl⟩)) pa' pb' pd' vh hx
      | bits n =>
        have h1 := hnone_bin_core .xor .xor n
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))) pa' pb' pd' vh hx
        cases pd' with
        | vec _ => rfl
        | gpr _ => exact h1
    cases t with
    | bool | float _ | pair _ _ =>
      rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
      exact vllGprOp_hook_fb_eq rfl (hnone_xor _ _ _)
    | bits n =>
      rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
      cases pd with
      | vec v =>
        exact vllGprOp_hook_fb_eq rfl (hnone_xor _ _ _)
      | gpr rd =>
        cases hw : vllX64WidthOfBits? n with
        | none =>
          exact vllGprOp_hook_fb_eq
            (by dsimp only [vllX64OpHook]; rw [hw]; try rfl) (hnone_xor _ _ _)
        | some w =>
          obtain rfl := vllX64WidthOfBits_eq_opt hw
          cases vh with
          | adcx | adox | mulxFast | decInc | disp _ =>
            exact vllGprOp_hook_fb_eq
              (by dsimp only [vllX64OpHook]; rw [hw]; try rfl) (hnone_xor _ _ _)
          | default =>
            cases pa with
            | imm ca =>
              exact vllGprOp_hook_fb_eq
                (by dsimp only [vllX64OpHook]; rw [hw]; try rfl) (hnone_xor _ _ _)
            | vec v =>
              exact vllGprOp_hook_fb_eq
                (by dsimp only [vllX64OpHook]; rw [hw]; try rfl) (hnone_xor _ _ _)
            | gpr ra =>
              by_cases hcond : (ra == rd || w.bits == 32 || w.bits == 64) = true
              · have hwide : (ra == rd) = true ∨ w = .w32 ∨ w = .w64 := by
                  by_cases hrr : (ra == rd) = true
                  · exact Or.inl hrr
                  · cases w <;> simp only [hrr, Bool.false_or] at hcond <;> first
                      | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)
                      | (exfalso; revert hcond; decide)
                cases pb with
                | vec v =>
                  exact vllGprOp_hook_fb_eq
                    (by dsimp only [vllX64OpHook]; rw [hw]
                        simp only [hcond, ↓reduceIte]; try rfl) (hnone_xor _ _ _)
                | gpr rb =>
                  refine vllGprOp_hook_some_eq [.alu .xor w rd ra (.reg rb) true] maskAll
                    (by dsimp only [vllX64OpHook]; rw [hw]
                        simp only [hcond, ↓reduceIte]; try rfl) ?_
                  dsimp only [x64Op, x64OpIns]
                  rw [withWidth_vll_parg2 w (.gpr ra, .gpr rb)]
                  exact asmX64List_aluBin_hook_eq w .xor rd ra (.gpr rb) hwide
                    (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
                | imm cb =>
                  refine vllGprOp_hook_some_eq
                    [.alu .xor w rd ra (.imm (cb.setWidth 64)) true] maskAll
                    (by dsimp only [vllX64OpHook]; rw [hw]
                        simp only [hcond, ↓reduceIte]; try rfl) ?_
                  dsimp only [x64Op, x64OpIns]
                  rw [withWidth_vll_parg2 w (.gpr ra, .imm cb)]
                  exact asmX64List_aluBin_hook_eq w .xor rd ra (.imm cb) hwide
                    (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
              · have hcf : (ra == rd || w.bits == 32 || w.bits == 64) = false :=
                  Bool.eq_false_iff.mpr hcond
                exact vllGprOp_hook_fb_eq
                  (by dsimp only [vllX64OpHook]; rw [hw]
                      simp only [hcf, Bool.false_eq_true, ↓reduceIte]; try rfl) (hnone_xor _ _ _)
  | cmp co t m hm =>
    cases hm; rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    have hnone_cmp : ∀ t' pa' pb' pd',
        x64Op (.cmp co t') (pa', pb', ()) (pd', ()) vh = none →
        vllCoreOp x64Arch (some ∘ condOf) (.cmp co t') (pa', pb', ()) (pd', ()) vh = none := by
      intro t' pa' pb' pd' hx
      cases t' with
      | bool | float _ | pair _ _ => rfl
      | bits n =>
        by_cases hbw : ([8, 16, 32, 64] : List Nat).contains n = true
        · have hmn : ∃ xw : Width, n = xw.bits := by
            rcases (by simpa [List.contains_eq_mem] using hbw :
                n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) with rfl | rfl | rfl | rfl
            · exact ⟨.w8, rfl⟩
            · exact ⟨.w16, rfl⟩
            · exact ⟨.w32, rfl⟩
            · exact ⟨.w64, rfl⟩
          rcases hmn with ⟨xw, rfl⟩
          cases pd' with
          | vec _ =>
            dsimp only [vllCoreOp, vllCoreCmp, x64Arch, x64Frame]
            rw [show ([8, 16, 32, 64] : List Nat).contains xw.bits = true from hbw,
              vll_withWidth_at_bits xw]
            simp only [↓reduceIte, vllCoreCmpW]
            cases pa' <;> cases pb' <;> rfl
          | gpr rd =>
            by_cases ha : ∃ v, pa' = .vec v
            · rcases ha with ⟨v, rfl⟩
              dsimp only [vllCoreOp, vllCoreCmp, x64Arch, x64Frame]
              rw [show ([8, 16, 32, 64] : List Nat).contains xw.bits = true from hbw,
                vll_withWidth_at_bits xw]
              simp only [↓reduceIte, vllCoreCmpW]
              cases pb' <;> rfl
            · by_cases hb : ∃ v, pb' = .vec v
              · rcases hb with ⟨v, rfl⟩
                dsimp only [vllCoreOp, vllCoreCmp, x64Arch, x64Frame]
                rw [show ([8, 16, 32, 64] : List Nat).contains xw.bits = true from hbw,
                  vll_withWidth_at_bits xw]
                simp only [↓reduceIte, vllCoreCmpW]
                cases pa' <;> rfl
              · exfalso
                have hclean : ∀ {o : Option (List _root_.Instr × FlagMask)},
                    (emitCleanPair o : Option (List _root_.Directive × FlagMask)) = none →
                    o = none := by
                  intro o ho; cases o <;> simp only [emitCleanPair, Option.map] at ho <;>
                    first | rfl | cases ho
                cases xw <;> cases pa' <;> cases pb' <;> first
                  | exact ha ⟨_, rfl⟩ | exact hb ⟨_, rfl⟩
                  | (dsimp only [x64Op, x64OpIns] at hx
                     rw [withWidth_vll_parg2 _ _] at hx
                     simp only [cast_eq] at hx
                     replace hx := hclean hx
                     dsimp only [opCmpIns, cmpDirectIns] at hx
                     first | cases hx | (split at hx <;> cases hx))
          | flag cf =>
            by_cases hcf : cf = condOf co
            · subst hcf
              have hcc : (condOf co == condOf co) = true := condCode_beq_self (condOf co)
              by_cases ha : ∃ v, pa' = .vec v
              · rcases ha with ⟨v, rfl⟩
                dsimp only [vllCoreOp, vllCoreCmp, x64Arch, x64Frame]
                rw [show ([8, 16, 32, 64] : List Nat).contains xw.bits = true from hbw,
                  vll_withWidth_at_bits xw]
                simp only [↓reduceIte, vllCoreCmpW]
                cases pb' <;> rfl
              · by_cases hb : ∃ v, pb' = .vec v
                · rcases hb with ⟨v, rfl⟩
                  dsimp only [vllCoreOp, vllCoreCmp, x64Arch, x64Frame]
                  rw [show ([8, 16, 32, 64] : List Nat).contains xw.bits = true from hbw,
                    vll_withWidth_at_bits xw]
                  simp only [↓reduceIte, vllCoreCmpW]
                  cases pa' <;> rfl
                · exfalso
                  have hclean : ∀ {o : Option (List _root_.Instr × FlagMask)},
                      (emitCleanPair o : Option (List _root_.Directive × FlagMask)) = none →
                      o = none := by
                    intro o ho; cases o <;> simp only [emitCleanPair, Option.map] at ho <;>
                      first | rfl | cases ho
                  cases xw <;> cases pa' <;> cases pb' <;> first
                    | exact ha ⟨_, rfl⟩ | exact hb ⟨_, rfl⟩
                    | (dsimp only [x64Op, x64OpIns] at hx
                       rw [withWidth_vll_parg2 _ _] at hx
                       simp only [cast_eq] at hx
                       replace hx := hclean hx
                       dsimp only [opCmpIns, cmpDirectIns] at hx
                       try simp only [hcc, ↓reduceIte] at hx
                       first | cases hx | (split at hx <;> cases hx))
            · cases pa' <;> cases pb' <;>
                (dsimp only [vllCoreOp, vllCoreCmp, x64Arch, x64Frame]
                 rw [show ([8, 16, 32, 64] : List Nat).contains xw.bits = true from hbw,
                   vll_withWidth_at_bits xw]
                 first
                 | rfl
                 | (dsimp only [vllCoreCmpW, Function.comp_apply,
                      vllRegOfPArg, vllSrcOfPArg, x64Scratch, List.head?, Option.map]
                    simp only [↓reduceIte]
                    split
                    · rename_i heq
                      exfalso
                      simp only [BEq.beq, decide_eq_true_eq] at heq
                      exact hcf heq
                    · rfl))
        · have hbwf : ([8, 16, 32, 64] : List Nat).contains n = false := Bool.eq_false_iff.mpr hbw
          dsimp only [vllCoreOp, vllCoreCmp, x64Arch, x64Frame]; rw [hbwf]; rfl
    cases t with
    | bool | float _ | pair _ _ =>
      exact vllGprOp_hook_fb_eq rfl (hnone_cmp _ _ _ _)
    | bits n =>
      by_cases hbw : ([8, 16, 32, 64] : List Nat).contains n = true
      · have hmn : ∃ xw : Width, n = xw.bits := by
          rcases (by simpa [List.contains_eq_mem] using hbw :
              n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) with rfl | rfl | rfl | rfl
          · exact ⟨.w8, rfl⟩
          · exact ⟨.w16, rfl⟩
          · exact ⟨.w32, rfl⟩
          · exact ⟨.w64, rfl⟩
        rcases hmn with ⟨xw, rfl⟩
        have hbw' : x64BitWidths.contains xw.bits = true := hbw
        cases pa with
        | vec v =>
          exact vllGprOp_hook_fb_eq
            (by dsimp only [vllX64OpHook]; simp only [hbw', ↓reduceIte]; try rfl)
            (hnone_cmp (.bits xw.bits) _ _ _)
        | imm ca =>
          exact vllGprOp_hook_fb_eq
            (by dsimp only [vllX64OpHook]; simp only [hbw', ↓reduceIte]; try rfl)
            (hnone_cmp (.bits xw.bits) _ _ _)
        | gpr rx =>
          cases pb with
          | vec v =>
            exact vllGprOp_hook_fb_eq
              (by dsimp only [vllX64OpHook]; simp only [hbw', ↓reduceIte]; try rfl)
              (hnone_cmp (.bits xw.bits) _ _ _)
          | gpr ry =>
            cases pd with
            | vec v =>
              exact vllGprOp_hook_fb_eq
                (by dsimp only [vllX64OpHook]; simp only [hbw', ↓reduceIte]; try rfl)
                (hnone_cmp (.bits xw.bits) _ _ _)
            | gpr rd =>
              refine vllGprOp_hook_none_eq
                (by dsimp only [vllX64OpHook]; simp only [hbw', ↓reduceIte]; try rfl) ?_
              dsimp only [vllCoreOp, vllCoreCmp, x64Arch, x64Frame, x64Op, x64OpIns]
              rw [show ([8, 16, 32, 64] : List Nat).contains xw.bits = true from by
                  cases xw <;> rfl,
                vll_withWidth_at_bits xw, withWidth_vll_parg2 xw (.gpr rx, .gpr ry)]
              simpa only [↓reduceIte, cast_eq] using
                asmX64List_cmp_core_eq co xw rx (.gpr ry) (.gpr rd) (Or.inl ⟨rd, rfl⟩)
            | flag cf =>
              by_cases hcf : cf = condOf co
              · subst hcf
                refine vllGprOp_hook_none_eq
                  (by dsimp only [vllX64OpHook]
                      simp only [hbw', condCode_beq_self, ↓reduceIte]; try rfl) ?_
                dsimp only [vllCoreOp, vllCoreCmp, x64Arch, x64Frame, x64Op, x64OpIns]
                rw [show ([8, 16, 32, 64] : List Nat).contains xw.bits = true from by
                    cases xw <;> rfl,
                  vll_withWidth_at_bits xw, withWidth_vll_parg2 xw (.gpr rx, .gpr ry)]
                simpa only [↓reduceIte, cast_eq] using
                  asmX64List_cmp_core_eq co xw rx (.gpr ry) (.flag (condOf co)) (Or.inr rfl)
              · have hcf' : (cf == condOf co) = false := condCode_beq_false_of_ne hcf
                exact vllGprOp_hook_fb_eq
                  (by dsimp only [vllX64OpHook]
                      simp only [hbw', hcf', Bool.false_eq_true, ↓reduceIte]; try rfl)
                  (hnone_cmp _ _ _ _)
          | imm cy =>
            cases pd with
            | vec v =>
              exact vllGprOp_hook_fb_eq
                (by dsimp only [vllX64OpHook]; simp only [hbw', ↓reduceIte]; try rfl)
                (hnone_cmp _ _ _ _)
            | gpr rd =>
              refine vllGprOp_hook_none_eq
                (by dsimp only [vllX64OpHook]; simp only [hbw', ↓reduceIte]; try rfl) ?_
              dsimp only [vllCoreOp, vllCoreCmp, x64Arch, x64Frame, x64Op, x64OpIns]
              rw [show ([8, 16, 32, 64] : List Nat).contains xw.bits = true from by
                  cases xw <;> rfl,
                vll_withWidth_at_bits xw, withWidth_vll_parg2 xw (.gpr rx, .imm cy)]
              simpa only [↓reduceIte, cast_eq] using
                asmX64List_cmp_core_eq co xw rx (.imm cy) (.gpr rd) (Or.inl ⟨rd, rfl⟩)
            | flag cf =>
              by_cases hcf : cf = condOf co
              · subst hcf
                refine vllGprOp_hook_none_eq
                  (by dsimp only [vllX64OpHook]
                      simp only [hbw', condCode_beq_self, ↓reduceIte]; try rfl) ?_
                dsimp only [vllCoreOp, vllCoreCmp, x64Arch, x64Frame, x64Op, x64OpIns]
                rw [show ([8, 16, 32, 64] : List Nat).contains xw.bits = true from by
                    cases xw <;> rfl,
                  vll_withWidth_at_bits xw, withWidth_vll_parg2 xw (.gpr rx, .imm cy)]
                simpa only [↓reduceIte, cast_eq] using
                  asmX64List_cmp_core_eq co xw rx (.imm cy) (.flag (condOf co)) (Or.inr rfl)
              · have hcf' : (cf == condOf co) = false := condCode_beq_false_of_ne hcf
                exact vllGprOp_hook_fb_eq
                  (by dsimp only [vllX64OpHook]
                      simp only [hbw', hcf', Bool.false_eq_true, ↓reduceIte]; try rfl)
                  (hnone_cmp _ _ _ _)
      · have hbwf : x64BitWidths.contains n = false := Bool.eq_false_iff.mpr hbw
        exact vllGprOp_hook_fb_eq
          (by dsimp only [vllX64OpHook]; rw [hbwf]; try rfl) (hnone_cmp _ _ _ _)
  | neg t =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    refine vllGprOp_hook_fb_eq rfl fun hx => ?_
    cases t with
    | bool | float _ | pair _ _ => rfl
    | bits n =>
      cases pd with
      | vec _ => rfl
      | gpr rd =>
        by_cases hbw : ([8, 16, 32, 64] : List Nat).contains n = true
        · have hmn : ∃ xw : _root_.Width, n = xw.bits := by
            rcases (by simpa [List.contains_eq_mem] using hbw :
                n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) with rfl | rfl | rfl | rfl
            · exact ⟨.W8, rfl⟩
            · exact ⟨.W16, rfl⟩
            · exact ⟨.W32, rfl⟩
            · exact ⟨.W64, rfl⟩
          rcases hmn with ⟨xw, rfl⟩
          cases pa with
          | vec _ => cases xw <;> rfl
          | gpr r =>
            exfalso
            dsimp only [x64Op, x64OpIns, emitCleanPair, Option.map] at hx
            rw [withWidth_parg xw (.gpr r)] at hx
            cases xw <;> cases hx
          | imm c =>
            exfalso
            dsimp only [x64Op, x64OpIns, emitCleanPair, Option.map] at hx
            rw [withWidth_parg xw (.imm c)] at hx
            cases xw <;> cases hx
        · have hbwf : ([8, 16, 32, 64] : List Nat).contains n = false := Bool.eq_false_iff.mpr hbw
          dsimp only [vllCoreOp, vllCoreNeg, x64Arch, x64Frame]; rw [hbwf]; rfl
  | not t =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    refine vllGprOp_hook_fb_eq rfl fun hx => ?_
    cases t with
    | float _ | pair _ _ => rfl
    | bool =>
      cases pd with
      | vec _ | flag _ => rfl
      | gpr rd =>
        cases pa with
        | vec _ => rfl
        | imm _ | flag _ => cases hx
        | gpr r =>
          dsimp only [x64Op, x64OpIns, opBoolNotIns, emitCleanPair, Option.map] at hx
          cases hrr : (r == rd)
          · simp only [hrr, Bool.false_eq_true, ↓reduceIte] at hx; cases hx
          · simp only [hrr, ↓reduceIte] at hx; cases hx
    | bits n =>
      cases pd with
      | vec _ => rfl
      | gpr rd =>
        by_cases hbw : ([8, 16, 32, 64] : List Nat).contains n = true
        · have hmn : ∃ xw : _root_.Width, n = xw.bits := by
            rcases (by simpa [List.contains_eq_mem] using hbw :
                n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) with rfl | rfl | rfl | rfl
            · exact ⟨.W8, rfl⟩
            · exact ⟨.W16, rfl⟩
            · exact ⟨.W32, rfl⟩
            · exact ⟨.W64, rfl⟩
          rcases hmn with ⟨xw, rfl⟩
          cases pa with
          | vec _ => cases xw <;> rfl
          | gpr r =>
            exfalso
            dsimp only [x64Op, x64OpIns, emitCleanPair, Option.map] at hx
            rw [withWidth_parg xw (.gpr r)] at hx
            cases xw <;> cases hx
          | imm c =>
            exfalso
            dsimp only [x64Op, x64OpIns, emitCleanPair, Option.map] at hx
            rw [withWidth_parg xw (.imm c)] at hx
            cases xw <;> cases hx
        · have hbwf : ([8, 16, 32, 64] : List Nat).contains n = false := Bool.eq_false_iff.mpr hbw
          dsimp only [vllCoreOp, vllCoreNot, x64Arch, x64Frame]; rw [hbwf]; rfl
  | shl t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    refine vllGprOp_hook_fb_eq rfl fun hx => ?_
    cases t with
    | bool | float _ | pair _ _ => rfl
    | bits n =>
      cases pd with
      | vec _ => rfl
      | gpr rd =>
        by_cases hbw : ([8, 16, 32, 64] : List Nat).contains n = true
        · have hmn : ∃ xw : _root_.Width, n = xw.bits := by
            rcases (by simpa [List.contains_eq_mem] using hbw :
                n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) with rfl | rfl | rfl | rfl
            · exact ⟨.W8, rfl⟩
            · exact ⟨.W16, rfl⟩
            · exact ⟨.W32, rfl⟩
            · exact ⟨.W64, rfl⟩
          rcases hmn with ⟨xw, rfl⟩
          by_cases ha : ∃ v, pa = .vec v
          · rcases ha with ⟨v, rfl⟩; cases xw <;> rfl
          · by_cases hb : ∃ v, pb = .vec v
            · rcases hb with ⟨v, rfl⟩; cases xw <;> cases pa <;> rfl
            · exfalso
              obtain ⟨res, hres⟩ := opShiftIns_isSome xw .shl (Or.inl rfl) pa pb rd
                (fun v e => ha ⟨v, e⟩) (fun v e => hb ⟨v, e⟩)
              dsimp only [x64Op, emitCleanPair, x64OpIns, Option.map] at hx
              rw [withWidth_parg2 xw (pa, pb), hres] at hx; cases hx
        · exact vllCoreBinBits_none_of_not_bw _ n (Bool.eq_false_iff.mpr hbw) _ _ rd
  | lshr t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    refine vllGprOp_hook_fb_eq rfl fun hx => ?_
    cases t with
    | bool | float _ | pair _ _ => rfl
    | bits n =>
      cases pd with
      | vec _ => rfl
      | gpr rd =>
        by_cases hbw : ([8, 16, 32, 64] : List Nat).contains n = true
        · have hmn : ∃ xw : _root_.Width, n = xw.bits := by
            rcases (by simpa [List.contains_eq_mem] using hbw :
                n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) with rfl | rfl | rfl | rfl
            · exact ⟨.W8, rfl⟩
            · exact ⟨.W16, rfl⟩
            · exact ⟨.W32, rfl⟩
            · exact ⟨.W64, rfl⟩
          rcases hmn with ⟨xw, rfl⟩
          by_cases ha : ∃ v, pa = .vec v
          · rcases ha with ⟨v, rfl⟩; cases xw <;> rfl
          · by_cases hb : ∃ v, pb = .vec v
            · rcases hb with ⟨v, rfl⟩; cases xw <;> cases pa <;> rfl
            · exfalso
              obtain ⟨res, hres⟩ := opShiftIns_isSome xw .lshr (Or.inr (Or.inl rfl)) pa pb rd
                (fun v e => ha ⟨v, e⟩) (fun v e => hb ⟨v, e⟩)
              dsimp only [x64Op, emitCleanPair, x64OpIns, Option.map] at hx
              rw [withWidth_parg2 xw (pa, pb), hres] at hx; cases hx
        · exact vllCoreBinBits_none_of_not_bw _ n (Bool.eq_false_iff.mpr hbw) _ _ rd
  | ashr t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    refine vllGprOp_hook_fb_eq rfl fun hx => ?_
    cases t with
    | bool | float _ | pair _ _ => rfl
    | bits n =>
      cases pd with
      | vec _ => rfl
      | gpr rd =>
        by_cases hbw : ([8, 16, 32, 64] : List Nat).contains n = true
        · have hmn : ∃ xw : _root_.Width, n = xw.bits := by
            rcases (by simpa [List.contains_eq_mem] using hbw :
                n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64) with rfl | rfl | rfl | rfl
            · exact ⟨.W8, rfl⟩
            · exact ⟨.W16, rfl⟩
            · exact ⟨.W32, rfl⟩
            · exact ⟨.W64, rfl⟩
          rcases hmn with ⟨xw, rfl⟩
          by_cases ha : ∃ v, pa = .vec v
          · rcases ha with ⟨v, rfl⟩; cases xw <;> rfl
          · by_cases hb : ∃ v, pb = .vec v
            · rcases hb with ⟨v, rfl⟩; cases xw <;> cases pa <;> rfl
            · exfalso
              obtain ⟨res, hres⟩ := opShiftIns_isSome xw .ashr (Or.inr (Or.inr rfl)) pa pb rd
                (fun v e => ha ⟨v, e⟩) (fun v e => hb ⟨v, e⟩)
              dsimp only [x64Op, emitCleanPair, x64OpIns, Option.map] at hx
              rw [withWidth_parg2 xw (pa, pb), hres] at hx; cases hx
        · exact vllCoreBinBits_none_of_not_bw _ n (Bool.eq_false_iff.mpr hbw) _ _ rd
  | zext m n =>
    have hne_mn : m ≠ n := by simpa [opNoSameExt] using hok
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    refine vllGprOp_hook_fb_eq rfl fun hx => ?_
    cases pd with
    | vec _ => rfl
    | gpr rd =>
      cases hm_w : Width.ofBits? m with
      | none =>
        dsimp only [vllCoreOp, vllCoreZext, x64Arch, x64Frame]
        rw [hm_w]
        simp only [Option.isSome, Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      | some wm =>
        cases hn_w : Width.ofBits? n with
        | none =>
          dsimp only [vllCoreOp, vllCoreZext, x64Arch, x64Frame]
          rw [hm_w, hn_w]
          simp only [Option.isSome, Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        | some wn =>
          dsimp only [vllCoreOp, vllCoreZext]
          rw [hm_w, hn_w]
          simp only [Option.isSome]
          dsimp only [x64Arch, x64Frame]
          by_cases hm_bw : ([8, 16, 32, 64] : List Nat).contains m = true
          · by_cases hn_bw : ([8, 16, 32, 64] : List Nat).contains n = true
            · have hm_mem : m = 8 ∨ m = 16 ∨ m = 32 ∨ m = 64 := by
                simpa [List.contains_eq_mem] using hm_bw
              have hn_mem : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 := by
                simpa [List.contains_eq_mem] using hn_bw
              by_cases hlt : Nat.ble (m + 1) n = true
              · cases pa with
                | vec _ => dsimp only; split <;> rfl
                | imm _ | gpr _ =>
                  exfalso
                  have hlt_le := Nat.ble_eq.mp hlt
                  have hbw' : (x64BitWidths.contains m && x64BitWidths.contains n) = true := by
                    simp only [Bool.and_eq_true]; exact ⟨hm_bw, hn_bw⟩
                  dsimp only [x64Op, x64OpIns, opZextIns, emitCleanPair] at hx
                  rw [hbw', hlt] at hx
                  simp only [Bool.and_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                    Option.map] at hx
                  rcases hm_mem with rfl | rfl | rfl | rfl
                  · cases hx
                  · cases hx
                  · cases hx
                  · rcases hn_mem with rfl | rfl | rfl | rfl <;> omega
              · have hltf : Nat.ble m n = false := by
                  cases h1 : Nat.ble m n
                  · rfl
                  · exfalso; apply hlt; apply Nat.ble_eq.mpr; have := Nat.ble_eq.mp h1; omega
                simp only [hm_bw, hn_bw, hltf, Bool.true_and, Bool.and_false,
                  Bool.false_eq_true, ↓reduceIte]
            · have hn_f := Bool.eq_false_iff.mpr hn_bw
              simp only [hm_bw, hn_f, Bool.true_and, Bool.false_and, Bool.false_eq_true,
                ↓reduceIte]
          · have hm_f := Bool.eq_false_iff.mpr hm_bw
            simp only [hm_f, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  | sext m n =>
    have hne_mn : m ≠ n := by simpa [opNoSameExt] using hok
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    refine vllGprOp_hook_fb_eq rfl fun hx => ?_
    cases pd with
    | vec _ => rfl
    | gpr rd =>
      dsimp only [vllCoreOp, vllCoreSext]
      cases hm_w : Width.ofBits? m
      · dsimp only [Option.isSome, Bool.false_eq_true, ↓reduceIte]; rfl
      · simp only [Option.isSome, ↓reduceIte]
        by_cases hm_bw : ([8, 16, 32, 64] : List Nat).contains m = true
        · by_cases hn_bw : ([8, 16, 32, 64] : List Nat).contains n = true
          · have hm_mem : m = 8 ∨ m = 16 ∨ m = 32 ∨ m = 64 := by
              simpa [List.contains_eq_mem] using hm_bw
            have hn_mem : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 := by
              simpa [List.contains_eq_mem] using hn_bw
            by_cases hlt : Nat.ble (m + 1) n = true
            · cases pa with
              | vec v =>
                have hvec : ∀ wn : Width, vllCoreSextW x64Arch m wn (.vec v) rd = none :=
                  fun wn => by dsimp only [vllCoreSextW]; split <;> rfl
                rcases hn_mem with rfl | rfl | rfl | rfl <;>
                  (dsimp only [withWidth]; exact hvec _)
              | imm _ | gpr _ =>
                exfalso
                have hlt_le := Nat.ble_eq.mp hlt
                have hbw' : (x64BitWidths.contains m && x64BitWidths.contains n) = true := by
                  simp only [Bool.and_eq_true]; exact ⟨hm_bw, hn_bw⟩
                dsimp only [x64Op, x64OpIns, opSextIns, emitCleanPair] at hx
                rw [hbw', hlt] at hx
                simp only [Bool.and_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                  Option.map] at hx
                rcases hm_mem with rfl | rfl | rfl | rfl <;>
                  (rcases hn_mem with rfl | rfl | rfl | rfl <;> first | omega | cases hx)
            · have hltf : Nat.ble m n = false := by
                cases h1 : Nat.ble m n
                · rfl
                · exfalso; apply hlt; apply Nat.ble_eq.mpr; have := Nat.ble_eq.mp h1; omega
              rcases hn_mem with rfl | rfl | rfl | rfl <;>
                (dsimp only [withWidth, vllCoreSextW, x64Arch, x64Frame]
                 simp only [hm_bw, hn_bw, hltf, Bool.true_and, Bool.and_false,
                   Bool.false_eq_true, ↓reduceIte])
          · have hn_f := Bool.eq_false_iff.mpr hn_bw
            have hn' : n ≠ 8 ∧ n ≠ 16 ∧ n ≠ 32 ∧ n ≠ 64 :=
              ⟨fun e => hn_bw (by subst e; rfl), fun e => hn_bw (by subst e; rfl),
               fun e => hn_bw (by subst e; rfl), fun e => hn_bw (by subst e; rfl)⟩
            exact vll_withWidth_none n hn' _
        · have hm_f := Bool.eq_false_iff.mpr hm_bw
          by_cases hn8 : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64
          · rcases hn8 with rfl | rfl | rfl | rfl <;>
              (dsimp only [withWidth, vllCoreSextW, x64Arch, x64Frame]
               simp only [hm_f, Bool.false_and, Bool.false_eq_true, ↓reduceIte])
          · have hn' : n ≠ 8 ∧ n ≠ 16 ∧ n ≠ 32 ∧ n ≠ 64 :=
              ⟨fun e => hn8 (Or.inl e), fun e => hn8 (Or.inr (Or.inl e)),
               fun e => hn8 (Or.inr (Or.inr (Or.inl e))),
               fun e => hn8 (Or.inr (Or.inr (Or.inr e)))⟩
            exact vll_withWidth_none n hn' _
  | ofBool n =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    refine vllGprOp_hook_fb_eq rfl fun hx => ?_
    cases pd with
    | vec _ => rfl
    | gpr rd =>
      by_cases hbw : ([8, 16, 32, 64] : List Nat).contains n = true
      · have hmn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 := by
          simpa [List.contains_eq_mem] using hbw
        have hbw' : x64BitWidths.contains n = true := hbw
        rcases hmn with rfl | rfl | rfl | rfl <;> cases pa with
          | vec _ => rfl
          | imm _ | gpr _ | flag _ =>
            dsimp only [x64Op, x64OpIns, opOfBoolIns, emitCleanPair, Option.map] at hx
            rw [hbw'] at hx; simp only [↓reduceIte] at hx; cases hx
      · have hbwf : ([8, 16, 32, 64] : List Nat).contains n = false := Bool.eq_false_iff.mpr hbw
        dsimp only [vllCoreOp, vllCoreOfBool, x64Arch, x64Frame]; rw [hbwf]; rfl
  | _ =>
    exact vllGprOp_hook_fb_eq rfl fun _ => rfl

theorem vllX64_op_eq_of_x64 {sig rs : List Ty} (code : OpCode sig rs)
    (pas : Tup (PArg Reg64 RegMm CondCode) sig)
    (dsts : Tup (PDst Reg64 RegMm CondCode) rs) (vh : VariantHint)
    {ds : List _root_.Directive} {cl : FlagMask}
    (hx : x64Isa.gpr.op code pas dsts vh = some (ds, cl)) :
    ∃ cs, vllX64Isa.gpr.op code pas dsts vh = some (cs, cl) ∧ asmX64List cs = ds := by
  by_cases hok : opNoSameExt code = true
  · have h := vllX64_op_eq code pas dsts vh hok
    rw [hx] at h
    rcases Option.map_eq_some_iff.mp h with ⟨p, hp, hpe⟩
    rcases p with ⟨cs, cl'⟩
    cases hpe
    exact ⟨cs, hp, rfl⟩
  · exfalso
    cases code <;> try simp [opNoSameExt] at hok
    all_goals
      rename_i m n
      have hmn : m = n := by simpa [opNoSameExt] using hok
      subst hmn
      rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
      cases pd with
      | vec _ => cases hx
      | gpr rd =>
        dsimp only [x64Isa, x64Gpr, x64Op, x64OpIns, opZextIns, opSextIns, opTruncIns,
          emitCleanPair] at hx
        have hlt : Nat.ble (m + 1) m = false := by
          cases h : Nat.ble (m + 1) m
          · rfl
          · have := Nat.ble_eq.mp h; omega
        rw [hlt] at hx
        simp at hx

end LeanQbe.T.Vll
