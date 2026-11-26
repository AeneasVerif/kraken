module

public import LeanQbe.T.Arm64.VllFactorArm641
import LeanQbe.T.Arm64.VllFactorArm640

/-!
# `BedrockMach` L1 AArch64 Pointwise 1:1 `asmArm64List` Parity (`Arm64.VllFactorArm642`)

Proves pointwise 1:1 `asmArm64List` directive parity for every `vllArmStrictGpr` and
`vllArmNativeHooks` callback (`saveRegs`, `restoreRegs`, `loadSext`, `load`, `store`, `op`) against
`Arm64.armGpr`.

Imported privately by `Arm64.VllFactorArm64` to keep every module well under `2,500` LOC.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open LeanQbe.T
open LeanQbe.T.Vll

private theorem setWidth_setWidth_self64 {n : Nat} (hn : n ≤ 64) (v : BitVec n) :
    (v.setWidth 64).setWidth n = v := by
  rw [BitVec.setWidth_setWidth_of_le _ hn, BitVec.setWidth_eq]

private theorem armMemScale_bits_none {n : Nat} (hn : ¬(n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64)) :
    armMemScale (.bits n) = none := by
  unfold armMemScale; split <;> first | rfl | (exfalso; apply hn; simp_all)

/-! ## 3. Pointwise 1:1 Parity, Full `Rega` Factoring, & `Unified.Factoring` -/

theorem asmArm64List_nil : asmArm64List [] = [] := rfl

theorem asmArm64List_cons (i : Instr arm64Arch) (is : List (Instr arm64Arch)) :
    asmArm64List (i :: is) = asmArm64 i ++ asmArm64List is := rfl

theorem asmArm64List_append (a b : List (Instr arm64Arch)) :
    asmArm64List (a ++ b) = asmArm64List a ++ asmArm64List b :=
  List.flatMap_append

theorem asmArm64List_one (i : Instr arm64Arch) :
    asmArm64List [i] = asmArm64 i :=
  List.append_nil _

private theorem asmArm64List_two (i1 i2 : Instr arm64Arch) :
    asmArm64List [i1, i2] = asmArm64 i1 ++ asmArm64 i2 := by
  simp [asmArm64List]

theorem asmArm64List_map_native (ds : List _root_.Directive) :
    asmArm64List (ds.map .native) = ds := by
  induction ds with
  | nil => rfl
  | cons d rest ih => simp [asmArm64List_cons, asmArm64, ih]

theorem wrapArmNative_asm (res : Option (List _root_.Directive × FlagMask)) :
    (wrapArmNative res).map (fun p => (asmArm64List p.1, p.2)) = res := by
  cases res with
  | none => rfl
  | some p =>
    rcases p with ⟨ds, cl⟩
    dsimp only [wrapArmNative, Option.map_some]
    rw [asmArm64List_map_native]

private theorem strict_eq {a : Option (List _root_.Directive × FlagMask)}
    {b : Option (List (Instr arm64Arch) × FlagMask)}
    (h : b.map (fun p => (asmArm64List p.1, p.2)) = a) :
    ((if a.isSome then b else none).map fun p => (asmArm64List p.1, p.2)) = a := by
  cases a with
  | none => rfl
  | some p => simpa using h

private theorem strict_eq_some {a : Option (List _root_.Directive × FlagMask)}
    {b : Option (List (Instr arm64Arch) × FlagMask)}
    (h : ∀ p, a = some p → b.map (fun q => (asmArm64List q.1, q.2)) = some p) :
    ((if a.isSome then b else none).map fun p => (asmArm64List p.1, p.2)) = a := by
  cases a with
  | none => rfl
  | some p => exact h p rfl

private theorem movi_pair_eq (d : XReg) (v : BitVec 64) (fl : FlagMask) :
    (some ([Instr.movi (A := arm64Arch) (.reg d) v], fl)).map (fun p => (asmArm64List p.1, p.2)) =
      some (emitClean (armMovImmI d v), fl) := by
  dsimp only [Option.map_some]
  rw [asmArm64List_one]; rfl

theorem vllArmSaveRegs_asm :
    ∀ i rs, asmArm64List (vllArmSaveRegs i rs) = armSaveRegs i rs
  | _, [] => rfl
  | i, [r] => by
    simp [vllArmSaveRegs, asmArm64List, asmArm64, armSaveRegs, armSaveRegsIns, armSlotSt]
  | i, .reg r1 :: .reg r2 :: rs => by
    dsimp only [vllArmSaveRegs, armSaveRegs, armSaveRegsIns]
    rw [asmArm64List_append, vllArmSaveRegs_asm (i + 2) rs, emitClean_append]
    congr 1
    dsimp only [armStpSpXRegIns]
    cases hfit : armFitsPairOff (8 * i) <;>
      simp only [Bool.false_eq_true, ↓reduceIte]
    · simp only [asmArm64List_cons, asmArm64List_nil, List.append_nil, asmArm64, armSlotSt,
        armSlotStIns, emitClean_append, show 8 * (i + 1) = 8 * i + 8 by omega]
    · simp [asmArm64List, asmArm64, emitClean]
  | i, .SP :: r2 :: rs => by
    simp only [vllArmSaveRegs, asmArm64List_cons, asmArm64, armSaveRegs, armSaveRegsIns,
      emitClean_append, armSlotSt]
    rw [vllArmSaveRegs_asm (i + 1) (r2 :: rs)]; rfl
  | i, .reg r1 :: .SP :: rs => by
    simp only [vllArmSaveRegs, asmArm64List_cons, asmArm64, armSaveRegs, armSaveRegsIns,
      emitClean_append, armSlotSt]
    rw [vllArmSaveRegs_asm (i + 1) (.SP :: rs)]; rfl

theorem vllArmRestoreRegs_asm :
    ∀ i rs, asmArm64List (vllArmRestoreRegs i rs) = armRestoreRegs i rs
  | _, [] => rfl
  | i, [r] => by
    simp [vllArmRestoreRegs, asmArm64List, asmArm64, armRestoreRegs, armRestoreRegsIns, armSlotLd]
  | i, .reg r1 :: .reg r2 :: rs => by
    dsimp only [vllArmRestoreRegs, armRestoreRegs, armRestoreRegsIns]
    rw [asmArm64List_append, vllArmRestoreRegs_asm (i + 2) rs, emitClean_append]
    congr 1
    dsimp only [armLdpSpXRegIns]
    cases hfit : armFitsPairOff (8 * i) <;>
      simp only [Bool.false_eq_true, ↓reduceIte]
    · simp only [asmArm64List_cons, asmArm64List_nil, List.append_nil, asmArm64, armSlotLd,
        armSlotLdIns, emitClean_append, show 8 * (i + 1) = 8 * i + 8 by omega]
    · simp [asmArm64List, asmArm64, emitClean]
  | i, .SP :: r2 :: rs => by
    simp only [vllArmRestoreRegs, asmArm64List_cons, asmArm64, armRestoreRegs, armRestoreRegsIns,
      emitClean_append, armSlotLd]
    rw [vllArmRestoreRegs_asm (i + 1) (r2 :: rs)]; rfl
  | i, .reg r1 :: .SP :: rs => by
    simp only [vllArmRestoreRegs, asmArm64List_cons, asmArm64, armRestoreRegs, armRestoreRegsIns,
      emitClean_append, armSlotLd]
    rw [vllArmRestoreRegs_asm (i + 1) (.SP :: rs)]; rfl

theorem vllArmLoadSext_asm (m n : Nat) (rd : Arm64.Reg) (a : AddrArg Arm64.Reg) :
    (vllArmLoadSext m n rd a).map (fun p => (asmArm64List p.1, p.2)) = armLoadSext m n rd a := by
  dsimp only [vllArmLoadSext, armLoadSext, armLoadSextIns, emitCleanPair]
  cases hok : (!(m == 8 || m == 16) || !Nat.blt m n || !Nat.ble n 64) <;>
    simp only [Bool.false_eq_true, ↓reduceIte]
  · have hm : m = 8 ∨ m = 16 := by
      simp only [Bool.or_eq_false_iff, Bool.not_eq_false', Bool.or_eq_true, beq_iff_eq] at hok
      exact hok.1.1
    rcases hm with rfl | rfl
    · cases hv : armAddrValid 1 a <;>
        simp [hv, armMemScale, armLoadSextTailIns, armLoadSextDirI, asmArm64List, asmArm64,
          asmLoadIns, armSetupAddrTotalIns, asmLoadDirI, emitClean] <;>
        cases rd <;> rfl
    · cases hv : armAddrValid 2 a <;>
        simp [hv, armMemScale, armLoadSextTailIns, armLoadSextDirI, asmArm64List, asmArm64,
          asmLoadIns, armSetupAddrTotalIns, asmLoadDirI, emitClean] <;>
        cases rd <;> rfl
  · rfl

theorem vllArmStrictLoad_asm (t : Ty) (rd : Arm64.Reg) (a : AddrArg Arm64.Reg) :
    (vllArmStrictGpr.load t rd a).map (fun p => (asmArm64List p.1, p.2)) = armLoad t rd a := by
  dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
  refine strict_eq_some fun p hp => ?_
  dsimp only [armLoad, armLoadIns, emitCleanPair] at hp
  cases t with
  | bool =>
    cases hv : armAddrValid 1 a
    · simp [hv, armMemScale] at hp
    · cases rd <;> (
        dsimp only [armMemScale, Bind.bind, Option.bind, armLoadTailIns, armLoadDirI,
          Option.map_some] at hp
        simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hp
        cases hp
        dsimp only [vllCoreLoad, Option.map_some]
        rw [asmArm64List_one]
        dsimp only [asmArm64, asmLoadIns, armSetupAddrTotalIns, asmLoadDirI, emitClean]
        simp only [hv, ↓reduceIte]; rfl)
  | bits n =>
    by_cases hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64
    · rcases hn with rfl | rfl | rfl | rfl
      · cases hv : armAddrValid 1 a
        · simp [hv, armMemScale] at hp
        · cases rd <;> (
            dsimp only [armMemScale, Bind.bind, Option.bind, armLoadTailIns, armLoadDirI,
              Option.map_some] at hp
            simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hp
            cases hp
            show (some ([Instr.load .w8 .zx _ a], FlagMask.none)).map
              (fun q => (asmArm64List q.1, q.2)) = _
            dsimp only [Option.map_some]; rw [asmArm64List_one]
            dsimp only [asmArm64, asmLoadIns, armSetupAddrTotalIns, asmLoadDirI, emitClean]
            simp only [hv, ↓reduceIte]; rfl)
      · cases hv : armAddrValid 2 a
        · simp [hv, armMemScale] at hp
        · cases rd <;> (
            dsimp only [armMemScale, Bind.bind, Option.bind, armLoadTailIns, armLoadDirI,
              Option.map_some] at hp
            simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hp
            cases hp
            show (some ([Instr.load .w16 .zx _ a], FlagMask.none)).map
              (fun q => (asmArm64List q.1, q.2)) = _
            dsimp only [Option.map_some]; rw [asmArm64List_one]
            dsimp only [asmArm64, asmLoadIns, armSetupAddrTotalIns, asmLoadDirI, emitClean]
            simp only [hv, ↓reduceIte]; rfl)
      · cases hv : armAddrValid 4 a
        · simp [hv, armMemScale] at hp
        · cases rd <;> (
            dsimp only [armMemScale, Bind.bind, Option.bind, armLoadTailIns, armLoadDirI,
              Option.map_some] at hp
            simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hp
            cases hp
            show (some ([Instr.load .w32 .zx _ a], FlagMask.none)).map
              (fun q => (asmArm64List q.1, q.2)) = _
            dsimp only [Option.map_some]; rw [asmArm64List_one]
            dsimp only [asmArm64, asmLoadIns, armSetupAddrTotalIns, asmLoadDirI, emitClean]
            simp only [hv, ↓reduceIte]; rfl)
      · cases hv : armAddrValid 8 a
        · simp [hv, armMemScale] at hp
        · cases rd <;> (
            dsimp only [armMemScale, Bind.bind, Option.bind, armLoadTailIns, armLoadDirI,
              Option.map_some] at hp
            simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hp
            cases hp
            show (some ([Instr.load .w64 .zx _ a], FlagMask.none)).map
              (fun q => (asmArm64List q.1, q.2)) = _
            dsimp only [Option.map_some]; rw [asmArm64List_one]
            dsimp only [asmArm64, asmLoadIns, armSetupAddrTotalIns, asmLoadDirI, emitClean]
            simp only [hv, ↓reduceIte]; rfl)
    · rw [armMemScale_bits_none hn] at hp; cases hp
  | float _ | pair _ _ => simp [armMemScale] at hp

theorem vllArmStrictStore_asm (t : Ty) (pa : PArg Arm64.Reg Empty ArmCond t)
    (a : AddrArg Arm64.Reg) :
    (vllArmStrictGpr.store t pa a).map (fun p => (asmArm64List p.1, p.2)) = armStore t pa a := by
  have hfb : vllArmStoreHook t pa a = wrapArmNative (armStore t pa a) →
      (vllArmStrictGpr.store t pa a).map (fun p => (asmArm64List p.1, p.2)) = armStore t pa a := by
    intro h
    dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
    refine strict_eq_some fun p hp => ?_
    rw [h, hp]; rcases p with ⟨ds, cl⟩
    dsimp only [wrapArmNative, Option.map_some]
    rw [asmArm64List_map_native]
  cases t with
  | float _ | pair _ _ => exact hfb rfl
  | bool => cases pa with
    | vec v => exact v.elim
    | imm _ | flag _ => exact hfb rfl
    | gpr r => cases r with
      | SP => exact hfb rfl
      | reg rx =>
        dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
        refine strict_eq_some fun p hp => ?_
        dsimp only [armStore, armStoreIns, emitCleanPair] at hp
        cases hv : armAddrValid 1 a
        · simp [hv, armMemScale] at hp
        · dsimp only [armMemScale, Bind.bind, Option.bind, armStoreValInIns, armStoreDirI,
            Option.map_some] at hp
          simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hp
          cases hp
          dsimp only [vllArmStoreHook, vllCoreStore, Option.map_some]
          rw [asmArm64List_one]
          dsimp only [asmArm64, asmStoreIns, armSetupAddrTotalIns, asmStoreDirI, emitClean]
          simp only [hv, ↓reduceIte]; rfl
  | bits n =>
    by_cases hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64
    · rcases hn with rfl | rfl | rfl | rfl
      · cases pa with
        | vec v => exact v.elim
        | imm _ => exact hfb rfl
        | gpr r => cases r with
          | SP => exact hfb rfl
          | reg rx =>
            dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
            refine strict_eq_some fun p hp => ?_
            dsimp only [armStore, armStoreIns, emitCleanPair] at hp
            cases hv : armAddrValid 1 a
            · simp [hv, armMemScale] at hp
            · dsimp only [armMemScale, Bind.bind, Option.bind, armStoreValInIns, armStoreDirI,
                Option.map_some] at hp
              simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hp
              cases hp
              show (some ([Instr.store (A := arm64Arch) .w8 (.reg rx) a], FlagMask.none)).map
                (fun q => (asmArm64List q.1, q.2)) = _
              dsimp only [Option.map_some]; rw [asmArm64List_one]
              dsimp only [asmArm64, asmStoreIns, armSetupAddrTotalIns, asmStoreDirI, emitClean]
              simp only [hv, ↓reduceIte]; rfl
      · cases pa with
        | vec v => exact v.elim
        | imm _ => exact hfb rfl
        | gpr r => cases r with
          | SP => exact hfb rfl
          | reg rx =>
            dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
            refine strict_eq_some fun p hp => ?_
            dsimp only [armStore, armStoreIns, emitCleanPair] at hp
            cases hv : armAddrValid 2 a
            · simp [hv, armMemScale] at hp
            · dsimp only [armMemScale, Bind.bind, Option.bind, armStoreValInIns, armStoreDirI,
                Option.map_some] at hp
              simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hp
              cases hp
              show (some ([Instr.store (A := arm64Arch) .w16 (.reg rx) a], FlagMask.none)).map
                (fun q => (asmArm64List q.1, q.2)) = _
              dsimp only [Option.map_some]; rw [asmArm64List_one]
              dsimp only [asmArm64, asmStoreIns, armSetupAddrTotalIns, asmStoreDirI, emitClean]
              simp only [hv, ↓reduceIte]; rfl
      · cases pa with
        | vec v => exact v.elim
        | imm _ => exact hfb rfl
        | gpr r => cases r with
          | SP => exact hfb rfl
          | reg rx =>
            dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
            refine strict_eq_some fun p hp => ?_
            dsimp only [armStore, armStoreIns, emitCleanPair] at hp
            cases hv : armAddrValid 4 a
            · simp [hv, armMemScale] at hp
            · dsimp only [armMemScale, Bind.bind, Option.bind, armStoreValInIns, armStoreDirI,
                Option.map_some] at hp
              simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hp
              cases hp
              show (some ([Instr.store (A := arm64Arch) .w32 (.reg rx) a], FlagMask.none)).map
                (fun q => (asmArm64List q.1, q.2)) = _
              dsimp only [Option.map_some]; rw [asmArm64List_one]
              dsimp only [asmArm64, asmStoreIns, armSetupAddrTotalIns, asmStoreDirI, emitClean]
              simp only [hv, ↓reduceIte]; rfl
      · cases pa with
        | vec v => exact v.elim
        | imm _ => exact hfb rfl
        | gpr r => cases r with
          | SP => exact hfb rfl
          | reg rx =>
            dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
            refine strict_eq_some fun p hp => ?_
            dsimp only [armStore, armStoreIns, emitCleanPair] at hp
            cases hv : armAddrValid 8 a
            · simp [hv, armMemScale] at hp
            · dsimp only [armMemScale, Bind.bind, Option.bind, armStoreValInIns, armStoreDirI,
                Option.map_some] at hp
              simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hp
              cases hp
              show (some ([Instr.store (A := arm64Arch) .w64 (.reg rx) a], FlagMask.none)).map
                (fun q => (asmArm64List q.1, q.2)) = _
              dsimp only [Option.map_some]; rw [asmArm64List_one]
              dsimp only [asmArm64, asmStoreIns, armSetupAddrTotalIns, asmStoreDirI, emitClean]
              simp only [hv, ↓reduceIte]; rfl
    · have hhook : vllArmStoreHook (.bits n) pa a = wrapArmNative (armStore (.bits n) pa a) := by
        unfold vllArmStoreHook; split <;> first | rfl | (exfalso; apply hn; simp_all)
      exact hfb hhook

theorem vllArmCmpCore_asm (o : CmpOp) (w : Width) (ra : XReg) (rhs : Src arm64Arch)
    (dst : PDst Arm64.Reg Empty ArmCond .bool) :
    (vllArmCmpCore o w ra rhs dst).map (fun p => (asmArm64List p.1, p.2)) =
      match dst with
      | .flag cf =>
        if cf == armCmpCond o then some (emitClean (asmCmpIns w (.reg ra) rhs), maskNZCV) else none
      | .gpr (.reg d) =>
        some (emitClean (asmCmpIns w (.reg ra) rhs) ++ [armCset64 d (armCmpCond o)], maskNZCV)
      | .gpr .SP | .vec _ => none := by
  cases dst with
  | vec v => exact v.elim
  | flag cf =>
    dsimp only [vllArmCmpCore]
    cases hc : (cf == armCmpCond o) <;> simp [asmArm64List, asmArm64]
  | gpr r => cases r with
    | SP => rfl
    | reg d =>
      simp [vllArmCmpCore, asmArm64List, asmArm64, armSetcc, armSetccIns, emitClean, armCset64]

private theorem addImm_asm {n : Nat} (hn : n = 32 ∨ n = 64) (d ra : XReg) (cb : BitVec n)
    (vh : VariantHint) :
    ((vllGprIsaOfHooks arm64Arch vllArmNativeHooks).op (.add (.bits n))
        (.gpr (.reg ra), .imm cb, ()) (.gpr (.reg d), ()) vh).map
      (fun p => (asmArm64List p.1, p.2)) =
      armOp (.add (.bits n)) (.gpr (.reg ra), .imm cb, ()) (.gpr (.reg d), ()) vh := by
  rcases hn with rfl | rfl <;> (
    dsimp only [vllGprIsaOfHooks, vllArmNativeHooks, vllArmOpHook, armOp, armOpIns, armBinOpIns,
      armAddSubImmI?, armWidthOf, emitCleanPair]
    try rw [show (32 == 64) = false from rfl]
    try rw [show (64 == 64) = true from rfl]
    try rw [show (32 == 32 || 32 == 64) = true from rfl]
    try rw [show (64 == 32 || 64 == 64) = true from rfl]
    cases h1 : armImm12? cb with
    | some ei =>
      simp only [Option.isSome_some, Bool.true_or, ↓reduceIte]
      show Option.map (fun p => (asmArm64List p.1, p.2))
        (some ([Instr.alu (A := arm64Arch) .add _ (.reg d) (.reg ra)
          (.imm (cb.setWidth 64)) false], FlagMask.none)) = _
      dsimp only [Option.map_some]; rw [asmArm64List_one]
      dsimp only [asmArm64, asmAluIns, asmAluImmFastIns?, widthToRegWidth]
      rw [setWidth_setWidth_self64 (by decide) cb, h1]; rfl
    | none => cases h2 : armImm12? (-cb) with
      | some ei =>
        simp only [Option.isSome_none, Option.isNone_some, Bool.false_or, Bool.false_eq_true,
          ↓reduceIte]
        show Option.map (fun p => (asmArm64List p.1, p.2))
          (some ([Instr.alu (A := arm64Arch) .sub _ (.reg d) (.reg ra)
            (.imm ((-cb).setWidth 64)) false], maskNone)) = _
        dsimp only [Option.map_some]; rw [asmArm64List_one]
        dsimp only [asmArm64, asmAluIns, asmAluImmFastIns?, widthToRegWidth]
        rw [setWidth_setWidth_self64 (by decide) (-cb), h2]; rfl
      | none =>
        simp only [Option.isSome_none, Option.isNone_none, Bool.false_or, ↓reduceIte]
        show Option.map (fun p => (asmArm64List p.1, p.2))
          (some ([Instr.alu (A := arm64Arch) .add _ (.reg d) (.reg ra)
            (.imm (cb.setWidth 64)) false], FlagMask.none)) = _
        dsimp only [Option.map_some]; rw [asmArm64List_one]
        dsimp only [asmArm64, asmAluIns, asmAluImmFastIns?, armSrcToXIns, armRhsToXIns,
          asmAluCoreIns, asmAluWideRegI, widthToRegWidth]
        rw [setWidth_setWidth_self64 (by decide) cb, h1]; rfl)

private theorem subImm_asm {n : Nat} (hn : n = 32 ∨ n = 64) (d ra : XReg) (cb : BitVec n)
    (vh : VariantHint) :
    ((vllGprIsaOfHooks arm64Arch vllArmNativeHooks).op (.sub (.bits n))
        (.gpr (.reg ra), .imm cb, ()) (.gpr (.reg d), ()) vh).map
      (fun p => (asmArm64List p.1, p.2)) =
      armOp (.sub (.bits n)) (.gpr (.reg ra), .imm cb, ()) (.gpr (.reg d), ()) vh := by
  rcases hn with rfl | rfl <;> (
    dsimp only [vllGprIsaOfHooks, vllArmNativeHooks, vllArmOpHook, armOp, armOpIns, armBinOpIns,
      armAddSubImmI?, armWidthOf, emitCleanPair]
    try rw [show (32 == 64) = false from rfl]
    try rw [show (64 == 64) = true from rfl]
    try rw [show (32 == 32 || 32 == 64) = true from rfl]
    try rw [show (64 == 32 || 64 == 64) = true from rfl]
    cases h1 : armImm12? cb with
    | some ei =>
      simp only [Option.isSome_some, Bool.true_or, ↓reduceIte]
      show Option.map (fun p => (asmArm64List p.1, p.2))
        (some ([Instr.alu (A := arm64Arch) .sub _ (.reg d) (.reg ra)
          (.imm (cb.setWidth 64)) false], FlagMask.none)) = _
      dsimp only [Option.map_some]; rw [asmArm64List_one]
      dsimp only [asmArm64, asmAluIns, asmAluImmFastIns?, widthToRegWidth]
      rw [setWidth_setWidth_self64 (by decide) cb, h1]; rfl
    | none => cases h2 : armImm12? (-cb) with
      | some ei =>
        simp only [Option.isSome_none, Option.isNone_some, Bool.false_or, Bool.false_eq_true,
          ↓reduceIte]
        show Option.map (fun p => (asmArm64List p.1, p.2))
          (some ([Instr.alu (A := arm64Arch) .add _ (.reg d) (.reg ra)
            (.imm ((-cb).setWidth 64)) false], maskNone)) = _
        dsimp only [Option.map_some]; rw [asmArm64List_one]
        dsimp only [asmArm64, asmAluIns, asmAluImmFastIns?, widthToRegWidth]
        rw [setWidth_setWidth_self64 (by decide) (-cb), h2]; rfl
      | none =>
        simp only [Option.isSome_none, Option.isNone_none, Bool.false_or, ↓reduceIte]
        show Option.map (fun p => (asmArm64List p.1, p.2))
          (some ([Instr.alu (A := arm64Arch) .sub _ (.reg d) (.reg ra)
            (.imm (cb.setWidth 64)) false], FlagMask.none)) = _
        dsimp only [Option.map_some]; rw [asmArm64List_one]
        dsimp only [asmArm64, asmAluIns, asmAluImmFastIns?, armSrcToXIns, armRhsToXIns,
          asmAluCoreIns, asmAluWideRegI, widthToRegWidth]
        rw [setWidth_setWidth_self64 (by decide) cb, h1]; rfl)

theorem vllArmStrictOp_asm {sig rs : List Ty} (code : OpCode sig rs)
    (pas : Tup (PArg Arm64.Reg Empty ArmCond) sig)
    (dsts : Tup (PDst Arm64.Reg Empty ArmCond) rs) (vh : VariantHint) :
    (vllArmStrictGpr.op code pas dsts vh).map (fun p => (asmArm64List p.1, p.2)) =
      armOp code pas dsts vh := by
  have hfb : vllArmOpHook code pas dsts vh = wrapArmNative (armOp code pas dsts vh) →
      (vllArmStrictGpr.op code pas dsts vh).map (fun p => (asmArm64List p.1, p.2)) =
        armOp code pas dsts vh := by
    intro h
    dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
    refine strict_eq_some fun p hp => ?_
    rw [h, hp]; rcases p with ⟨ds, cl⟩
    dsimp only [wrapArmNative, Option.map_some]
    rw [asmArm64List_map_native]
  cases code with
  | copy t =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t with
    | float _ | pair _ _ => exact hfb rfl
    | bool => cases pd with
      | vec v => exact v.elim | flag _ => exact hfb rfl | gpr rd => cases rd with
        | SP => exact hfb rfl | reg d => cases pa with
          | vec v => exact v.elim
          | gpr r => cases r with | SP => exact hfb rfl | reg rx =>
            dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
            exact strict_eq rfl
          | imm b =>
            dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
            exact strict_eq (movi_pair_eq d _ _)
          | flag cf =>
            dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
            exact strict_eq rfl
    | bits n => cases pd with
      | vec v => exact v.elim | gpr rd => cases rd with
        | SP => exact hfb rfl | reg d => cases pa with
          | vec v => exact v.elim
          | gpr r => cases r with | SP => exact hfb rfl | reg rx =>
            by_cases hn : n = 8 ∨ n = 16 ∨ n = 32
            · rcases hn with rfl | rfl | rfl <;> (
                dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
                exact strict_eq rfl)
            · have hnot : (n == 8 || n == 16 || n == 32) = false := by
                simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega
              exact hfb (by dsimp only [vllArmOpHook]; simp only [hnot, Bool.false_eq_true,
                ↓reduceIte])
          | imm cv =>
            by_cases hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64
            · rcases hn with rfl | rfl | rfl | rfl <;> (
                dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
                exact strict_eq (movi_pair_eq d _ _))
            · have hnot : [8, 16, 32, 64].contains n = false := by
                simp only [List.contains_eq_mem, decide_eq_false_iff_not, List.mem_cons,
                  List.not_mem_nil, or_false]; omega
              exact hfb (by dsimp only [vllArmOpHook]; simp only [hnot, Bool.false_eq_true,
                ↓reduceIte])
  | bitcast t u hsz =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t with | bool | float _ | pair _ _ => exact hfb rfl | bits m =>
    cases u with | bool | float _ | pair _ _ => exact hfb rfl | bits n =>
    have hmn : m = n := hsz; subst hmn
    cases pd with | vec v => exact v.elim | gpr rd => cases rd with
      | SP => exact hfb rfl | reg d => cases pa with
        | vec v => exact v.elim
        | gpr r => cases r with | SP => exact hfb rfl | reg rx =>
          by_cases hm : m = 8 ∨ m = 16 ∨ m = 32
          · rcases hm with rfl | rfl | rfl <;> (
              dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
              exact strict_eq rfl)
          · have hnot : (m == 8 || m == 16 || m == 32) = false := by
              simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega
            exact hfb (by dsimp only [vllArmOpHook]; simp only [hnot, Bool.and_false,
              Bool.false_eq_true, ↓reduceIte])
        | imm cv =>
          by_cases hm : m = 8 ∨ m = 16 ∨ m = 32 ∨ m = 64
          · rcases hm with rfl | rfl | rfl | rfl <;> (
              dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
              exact strict_eq (movi_pair_eq d _ _))
          · have hnot : [8, 16, 32, 64].contains m = false := by
              simp only [List.contains_eq_mem, decide_eq_false_iff_not, List.mem_cons,
                List.not_mem_nil, or_false]; omega
            exact hfb (by dsimp only [vllArmOpHook]; simp only [hnot, Bool.false_and,
              Bool.false_eq_true, ↓reduceIte])
  | zext m n =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd with | vec v => exact v.elim | gpr rd => cases rd with
      | SP => exact hfb rfl | reg d => cases pa with
        | vec v => exact v.elim
        | imm cv =>
          cases hc : ([8, 16, 32, 64].contains m && [8, 16, 32, 64].contains n && Nat.ble m n)
          · exact hfb (by dsimp only [vllArmOpHook]; simp only [hc, Bool.false_eq_true, ↓reduceIte])
          · have hm : m = 8 ∨ m = 16 ∨ m = 32 ∨ m = 64 := by
              simp only [Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq, List.mem_cons,
                List.not_mem_nil, or_false] at hc; exact hc.1.1
            have hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 := by
              simp only [Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq, List.mem_cons,
                List.not_mem_nil, or_false] at hc; exact hc.1.2
            have hle : Nat.ble m n = true := by simp only [Bool.and_eq_true] at hc; exact hc.2
            rcases hm with rfl | rfl | rfl | rfl <;> rcases hn with rfl | rfl | rfl | rfl <;>
              first
              | exact absurd hle (by decide)
              | (dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
                 exact strict_eq (movi_pair_eq d _ _))
        | gpr r => cases r with | SP => exact hfb rfl | reg rx =>
          cases hc : ([8, 16, 32, 64].contains m && [8, 16, 32, 64].contains n && Nat.ble m n)
          · exact hfb (by dsimp only [vllArmOpHook]; simp only [hc, Bool.false_eq_true, ↓reduceIte])
          · by_cases hm : m = 8 ∨ m = 16 ∨ m = 32
            · rcases hm with rfl | rfl | rfl <;> (
                dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
                refine strict_eq ?_
                dsimp only [vllArmOpHook, armOp, armOpIns, armZextOpIns, emitCleanPair]
                simp only [hc, ↓reduceIte]; rfl)
            · have hnot : (m == 8) = false ∧ (m == 16) = false ∧ (m == 32) = false := by
                simp only [beq_eq_false_iff_ne]; omega
              exact hfb (by dsimp only [vllArmOpHook]; simp only [hc, hnot.1, hnot.2.1, hnot.2.2,
                Bool.false_eq_true, ↓reduceIte])
  | trunc m n =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd with | vec v => exact v.elim | gpr rd => cases rd with
      | SP => exact hfb rfl | reg d => cases pa with
        | vec v => exact v.elim
        | imm cv =>
          cases hc : ([8, 16, 32, 64].contains m && [8, 16, 32, 64].contains n && Nat.ble n m)
          · exact hfb (by dsimp only [vllArmOpHook]; simp only [hc, Bool.false_eq_true, ↓reduceIte])
          · have hm : m = 8 ∨ m = 16 ∨ m = 32 ∨ m = 64 := by
              simp only [Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq, List.mem_cons,
                List.not_mem_nil, or_false] at hc; exact hc.1.1
            have hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 := by
              simp only [Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq, List.mem_cons,
                List.not_mem_nil, or_false] at hc; exact hc.1.2
            have hle : Nat.ble n m = true := by simp only [Bool.and_eq_true] at hc; exact hc.2
            rcases hm with rfl | rfl | rfl | rfl <;> rcases hn with rfl | rfl | rfl | rfl <;>
              first
              | exact absurd hle (by decide)
              | (dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
                 exact strict_eq (movi_pair_eq d _ _))
        | gpr r => cases r with | SP => exact hfb rfl | reg rx =>
          cases hc : ([8, 16, 32, 64].contains m && [8, 16, 32, 64].contains n && Nat.ble n m)
          · exact hfb (by dsimp only [vllArmOpHook]; simp only [hc, Bool.false_and,
              Bool.false_eq_true, ↓reduceIte])
          · by_cases hn : n = 8 ∨ n = 16 ∨ n = 32
            · rcases hn with rfl | rfl | rfl <;> (
                dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
                refine strict_eq ?_
                dsimp only [vllArmOpHook, armOp, armOpIns, armTruncOpIns, emitCleanPair]
                simp only [hc]; rfl)
            · have hnot : (n == 8 || n == 16 || n == 32) = false := by
                simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega
              exact hfb (by dsimp only [vllArmOpHook]; simp only [hc, hnot, Bool.and_false,
                Bool.false_eq_true, ↓reduceIte])
  | ofBool n =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd with | vec v => exact v.elim | gpr rd => cases rd with
      | SP => exact hfb rfl | reg d =>
        by_cases hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64
        · rcases hn with rfl | rfl | rfl | rfl <;> (cases pa with
            | vec v => exact v.elim
            | imm _ =>
              dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
              exact strict_eq (movi_pair_eq d _ _)
            | flag _ =>
              dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
              exact strict_eq rfl
            | gpr r => cases r with
              | SP => exact hfb rfl
              | reg _ =>
                dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
                exact strict_eq rfl)
        · have hnot : [8, 16, 32, 64].contains n = false := by
            simp only [List.contains_eq_mem, decide_eq_false_iff_not, List.mem_cons,
              List.not_mem_nil, or_false]; omega
          exact hfb (by
            cases pa with
            | vec v => exact v.elim
            | imm _ => dsimp only [vllArmOpHook]; simp only [hnot, Bool.false_eq_true, ↓reduceIte]
            | flag _ => dsimp only [vllArmOpHook]; simp only [hnot, Bool.false_eq_true, ↓reduceIte]
            | gpr r => cases r with
              | SP => rfl
              | reg _ =>
                dsimp only [vllArmOpHook]; simp only [hnot, Bool.false_eq_true, ↓reduceIte])
  | not t =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t with
    | float _ | pair _ _ => exact hfb rfl
    | bool => cases pd with
      | vec v => exact v.elim | flag _ => exact hfb rfl | gpr rd => cases rd with
        | SP => exact hfb rfl | reg d => cases pa with
          | vec v => exact v.elim
          | imm _ =>
            dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
            exact strict_eq (movi_pair_eq d _ _)
          | flag _ =>
            dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
            exact strict_eq rfl
          | gpr r => cases r with | SP => exact hfb rfl | reg rx =>
            dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
            exact strict_eq rfl
    | bits n => cases pd with
      | vec v => exact v.elim | gpr rd => cases rd with
        | SP => exact hfb rfl | reg d => cases pa with
          | vec v => exact v.elim | gpr _ => exact hfb rfl | imm _ =>
            cases hc : [8, 16, 32, 64].contains n
            · exact hfb (by dsimp only [vllArmOpHook]; simp only [hc, Bool.false_eq_true,
                ↓reduceIte])
            · dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
              refine strict_eq ?_
              dsimp only [vllArmOpHook, armOp, armOpIns, emitCleanPair]
              simp only [hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              exact movi_pair_eq d _ _
  | neg t =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t with
    | bool | float _ | pair _ _ => exact hfb rfl
    | bits n => cases pd with
      | vec v => exact v.elim | gpr rd => cases rd with
        | SP => exact hfb rfl | reg d => cases pa with
          | vec v => exact v.elim | gpr _ => exact hfb rfl | imm _ =>
            cases hc : [8, 16, 32, 64].contains n
            · exact hfb (by dsimp only [vllArmOpHook]; simp only [hc, Bool.false_eq_true,
                ↓reduceIte])
            · dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
              refine strict_eq ?_
              dsimp only [vllArmOpHook, armOp, armOpIns, emitCleanPair]
              simp only [hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              exact movi_pair_eq d _ _
  | add t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t with | bool | float _ | pair _ _ => exact hfb rfl | bits n =>
    cases pd with | vec v => exact v.elim | gpr rd => cases rd with
      | SP => exact hfb rfl | reg d => cases pa with
        | vec v => exact v.elim | imm _ => exact hfb rfl | gpr r1 => cases r1 with
          | SP => exact hfb rfl | reg ra => cases pb with
            | vec v => exact v.elim
            | gpr r2 => cases r2 with | SP => exact hfb rfl | reg rb =>
              by_cases hn : n = 32 ∨ n = 64
              · rcases hn with rfl | rfl <;> (
                  dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
                  exact strict_eq rfl)
              · have hnot : (n == 32 || n == 64) = false := by
                  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega
                exact hfb (by dsimp only [vllArmOpHook]; simp only [hnot, Bool.false_eq_true,
                  ↓reduceIte])
            | imm cb =>
              by_cases hn : n = 32 ∨ n = 64
              · dsimp only [vllArmStrictGpr, armGpr]
                exact strict_eq (addImm_asm hn d ra cb vh)
              · have hnot : (n == 32 || n == 64) = false := by
                  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega
                exact hfb (by dsimp only [vllArmOpHook]; simp only [hnot, Bool.false_eq_true,
                  ↓reduceIte])
  | sub t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t with | bool | float _ | pair _ _ => exact hfb rfl | bits n =>
    cases pd with | vec v => exact v.elim | gpr rd => cases rd with
      | SP => exact hfb rfl | reg d => cases pa with
        | vec v => exact v.elim | imm _ => exact hfb rfl | gpr r1 => cases r1 with
          | SP => exact hfb rfl | reg ra => cases pb with
            | vec v => exact v.elim
            | gpr r2 => cases r2 with | SP => exact hfb rfl | reg rb =>
              by_cases hn : n = 32 ∨ n = 64
              · rcases hn with rfl | rfl <;> (
                  dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
                  exact strict_eq rfl)
              · have hnot : (n == 32 || n == 64) = false := by
                  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega
                exact hfb (by dsimp only [vllArmOpHook]; simp only [hnot, Bool.false_eq_true,
                  ↓reduceIte])
            | imm cb =>
              by_cases hn : n = 32 ∨ n = 64
              · dsimp only [vllArmStrictGpr, armGpr]
                exact strict_eq (subImm_asm hn d ra cb vh)
              · have hnot : (n == 32 || n == 64) = false := by
                  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega
                exact hfb (by dsimp only [vllArmOpHook]; simp only [hnot, Bool.false_eq_true,
                  ↓reduceIte])
  | mul t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t with | bool | float _ | pair _ _ => exact hfb rfl | bits n =>
    cases pd with | vec v => exact v.elim | gpr rd => cases rd with
      | SP => exact hfb rfl | reg d => cases pa with
        | vec v => exact v.elim | imm _ => exact hfb rfl | gpr r1 => cases r1 with
          | SP => exact hfb rfl | reg ra => cases pb with
            | vec v => exact v.elim | imm _ => exact hfb rfl | gpr r2 => cases r2 with
              | SP => exact hfb rfl | reg rb =>
                by_cases hn : n = 32 ∨ n = 64
                · rcases hn with rfl | rfl <;> (
                    dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
                    exact strict_eq rfl)
                · have hnot : (n == 32 || n == 64) = false := by
                    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega
                  exact hfb (by dsimp only [vllArmOpHook]; simp only [hnot, Bool.false_eq_true,
                    ↓reduceIte])
  | and t | or t | xor t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t with | bool | float _ | pair _ _ => exact hfb rfl | bits n =>
    cases pd with | vec v => exact v.elim | gpr rd => cases rd with
      | SP => exact hfb rfl | reg d => cases pa with
        | vec v => exact v.elim | imm _ => exact hfb rfl | gpr r1 => cases r1 with
          | SP => exact hfb rfl | reg ra => cases pb with
            | vec v => exact v.elim
            | gpr r2 => cases r2 with | SP => exact hfb rfl | reg rb =>
              by_cases hn : n = 32 ∨ n = 64
              · rcases hn with rfl | rfl <;> (
                  dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
                  exact strict_eq rfl)
              · have hnot : (n == 32 || n == 64) = false := by
                  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega
                exact hfb (by dsimp only [vllArmOpHook]; simp only [hnot, Bool.false_eq_true,
                  ↓reduceIte])
            | imm cb =>
              by_cases hn : n = 32 ∨ n = 64
              · rcases hn with rfl | rfl <;> (
                  dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
                  refine strict_eq ?_
                  refine Eq.trans ?_ (by rfl)
                  show (some ([Instr.alu (A := arm64Arch) _ _ (.reg d) (.reg ra)
                      (.imm (cb.setWidth 64)) false], maskNone)).map
                    (fun p => (asmArm64List p.1, p.2)) = _
                  dsimp only [Option.map_some]; rw [asmArm64List_one]
                  dsimp only [asmArm64, asmAluIns, asmAluImmFastIns?, armSrcToXIns, armRhsToXIns,
                    asmAluCoreIns, asmAluWideRegI, widthToRegWidth, Width.bits, armOp, armOpIns,
                    armBinOpIns, armArgInIns, armBinDirI, armLogicImmDirI, armWidthOf,
                    emitCleanPair]
                  try rw [show (32 == 64) = false from rfl]
                  try rw [show (64 == 64) = true from rfl]
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  rw [setWidth_setWidth_self64 (by decide) cb]
                  cases armIsValidLogicalImm _ (cb.setWidth 64) <;> rfl)
              · have hnot : (n == 32 || n == 64) = false := by
                  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega
                exact hfb (by dsimp only [vllArmOpHook]; simp only [hnot, Bool.false_eq_true,
                  ↓reduceIte])
  | shl t | lshr t | ashr t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t with | bool | float _ | pair _ _ => exact hfb rfl | bits n =>
    cases pd with | vec v => exact v.elim | gpr rd => cases rd with
      | SP => exact hfb rfl | reg d => cases pa with
        | vec v => exact v.elim
        | gpr r1 => cases r1 with | SP => exact hfb rfl | reg ra => cases pb with
          | vec v => exact v.elim
          | gpr r2 => cases r2 with | SP => exact hfb rfl | reg rb =>
            by_cases hn : n = 32 ∨ n = 64
            · rcases hn with rfl | rfl <;> (
                dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
                exact strict_eq rfl)
            · have hnot : (n == 32 || n == 64) = false := by
                simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega
              exact hfb (by dsimp only [vllArmOpHook]; simp only [hnot, Bool.false_eq_true,
                ↓reduceIte])
          | imm cb =>
            by_cases hn : n = 32 ∨ n = 64
            · rcases hn with rfl | rfl <;> (
                dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
                refine strict_eq ?_
                show (some ([Instr.alu (A := arm64Arch) _ _ (.reg d) (.reg ra)
                    (.imm (cb.setWidth 64)) false], maskNone)).map
                  (fun p => (asmArm64List p.1, p.2)) = _
                dsimp only [Option.map_some]; rw [asmArm64List_one]
                dsimp only [asmArm64, asmAluIns, asmAluImmFastIns?, widthToRegWidth]
                rw [setWidth_setWidth_self64 (by decide) cb]; rfl)
            · have hnot : (n == 32 || n == 64) = false := by
                simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega
              exact hfb (by dsimp only [vllArmOpHook]; simp only [hnot, Bool.false_eq_true,
                ↓reduceIte])
        | imm ca => cases pb with
          | vec v => exact v.elim | imm _ => exact hfb rfl | gpr r2 => cases r2 with
            | SP => exact hfb rfl | reg rb =>
              by_cases hn : n = 32 ∨ n = 64
              · rcases hn with rfl | rfl <;> (
                  dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
                  refine strict_eq ?_
                  show (some ([Instr.movi (A := arm64Arch) (.reg .X16) (ca.setWidth 64),
                      Instr.alu (A := arm64Arch) _ _ (.reg d) (.reg .X16)
                        (.reg (.reg rb)) false], maskNone)).map
                    (fun p => (asmArm64List p.1, p.2)) = _
                  dsimp only [Option.map_some]; rw [asmArm64List_two]
                  dsimp only [asmArm64, armMovi, armMoviIns, asmAluIns, armSrcToXIns, armRhsToXIns,
                    asmAluCoreIns, asmAluWideRegI, widthToRegWidth, armOp, armOpIns, armShiftOpIns,
                    armArgInIns, armWidthOf, emitCleanPair, Bind.bind, Option.bind]
                  simp only [Bool.not_false, ↓reduceIte, List.nil_append, List.append_nil,
                    ← emitClean_append]; rfl)
              · have hnot : (n == 32 || n == 64) = false := by
                  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega
                exact hfb (by dsimp only [vllArmOpHook]; simp only [hnot, Bool.false_eq_true,
                  ↓reduceIte])
  | cmp o t m hm =>
    subst hm; rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨dst, ⟨⟩⟩
    cases t with | bool | float _ | pair _ _ => exact hfb rfl | bits n =>
    cases pa with | vec v => exact v.elim | imm _ => exact hfb rfl | gpr r1 => cases r1 with
      | SP => exact hfb rfl | reg ra => cases pb with
        | vec v => exact v.elim
        | gpr r2 => cases r2 with | SP => exact hfb rfl | reg rb =>
          by_cases hn : n = 32 ∨ n = 64
          · rcases hn with rfl | rfl <;> (
              dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
              refine strict_eq_some fun p hp => ?_
              cases dst with
              | vec v => exact v.elim
              | flag cf =>
                dsimp only [armOp, armOpIns, armCmpOpIns, emitCleanPair] at hp
                dsimp only [vllArmOpHook, vllArmCmpCore]
                cases hc : (cf == armCmpCond o) <;>
                  simp only [hc, Bool.false_eq_true, ↓reduceIte] at hp ⊢
                · cases hp
                · cases hp; rfl
              | gpr rd => cases rd with
                | SP =>
                  dsimp only [armOp, armOpIns, armCmpOpIns, emitCleanPair] at hp
                  cases hp
                | reg d =>
                  dsimp only [armOp, armOpIns, armCmpOpIns, emitCleanPair] at hp
                  cases hp; rfl)
          · have hnot : (n == 32 || n == 64) = false := by
              simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega
            exact hfb (by dsimp only [vllArmOpHook]; simp only [hnot, Bool.false_eq_true,
              ↓reduceIte])
        | imm cb =>
          cases hcond : ((n == 32 || n == 64) &&
              (cb != 0#n || (armZeroCmpIns? o n ra dst).isNone) &&
              ((armImm12? cb).isSome || cb == 0#n || (armImm12? (-cb)).isNone))
          · exact hfb (by dsimp only [vllArmOpHook]; simp only [hcond, Bool.false_eq_true,
              ↓reduceIte])
          · have hn : n = 32 ∨ n = 64 := by
              simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hcond; exact hcond.1.1
            have hzc : cb = 0#n → armZeroCmpIns? o n ra dst = none := by
              intro h0
              simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, Option.isNone_iff_eq_none]
                at hcond
              exact hcond.1.2.resolve_left (fun hne => hne h0)
            have hneg : armImm12? cb = none → cb ≠ 0#n → armImm12? (-cb) = none := by
              intro h1 h0
              simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Option.isSome_iff_exists,
                Option.isNone_iff_eq_none] at hcond
              rcases hcond.2 with (⟨_, he⟩ | h0') | h2
              · rw [h1] at he; cases he
              · exact absurd h0' h0
              · exact h2
            rcases hn with rfl | rfl <;> (
              dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
              refine strict_eq_some fun p hp => ?_
              dsimp only [armOp, armOpIns, armCmpOpIns, emitCleanPair] at hp
              dsimp only [vllArmOpHook]
              simp only [hcond, ↓reduceIte] at hp ⊢
              try rw [show (32 == 64) = false from rfl] at hp ⊢
              try rw [show (64 == 64) = true from rfl] at hp ⊢
              try rw [show (32 == 32 || 32 == 64) = true from rfl] at hp ⊢
              try rw [show (64 == 32 || 64 == 64) = true from rfl] at hp ⊢
              simp only [Bool.false_eq_true, ↓reduceIte] at hp ⊢
              by_cases h0 : cb = 0#_
              · have h0imm : armImm12? cb =
                    some (.imm { imm := .int64 0, shift := .S0 }) := by rw [h0]; rfl
                have h0b : (cb == 0#_) = true := beq_iff_eq.mpr h0
                have hzc0 := hzc h0
                rw [h0b, hzc0] at hp
                cases dst with
                | vec v => exact v.elim
                | flag cf =>
                  dsimp only [armCmpImmIns?, armWidthOf] at hp
                  dsimp only [armCmpImmIns?, armWidthOf, vllArmCmpCore]
                  rw [h0imm] at hp
                  cases hc : (cf == armCmpCond o) <;>
                    simp only [hc, Bool.false_eq_true, ↓reduceIte] at hp ⊢
                  · cases hp
                  · cases hp; dsimp only [Option.map_some]; rw [asmArm64List_one]
                    dsimp only [asmArm64, asmCmpIns, widthToRegWidth]
                    rw [setWidth_setWidth_self64 (by decide) cb, h0imm]; rfl
                | gpr rd => cases rd with
                  | SP =>
                    dsimp only [armCmpImmIns?, armWidthOf] at hp
                    rw [h0imm] at hp; cases hp
                  | reg d =>
                    dsimp only [armCmpImmIns?, armWidthOf] at hp
                    rw [h0imm] at hp; cases hp
                    dsimp only [armCmpImmIns?, armWidthOf, vllArmCmpCore, Option.map_some]
                    rw [asmArm64List_two]
                    dsimp only [asmArm64, asmCmpIns, widthToRegWidth, armSetcc, armSetccIns]
                    rw [setWidth_setWidth_self64 (by decide) cb, h0imm, ← emitClean_append]
                    rfl
              · have h0b : (cb == 0#_) = false := beq_false_of_ne h0
                cases h1 : armImm12? cb with
                | some ei =>
                  cases dst with
                  | vec v => exact v.elim
                  | flag cf =>
                    dsimp only [armCmpImmIns?, armWidthOf] at hp
                    dsimp only [armCmpImmIns?, armWidthOf, vllArmCmpCore]
                    rw [h0b, h1] at hp
                    cases hc : (cf == armCmpCond o) <;>
                      simp only [hc, Bool.false_eq_true, ↓reduceIte] at hp ⊢
                    · cases hp
                    · cases hp; dsimp only [Option.map_some]; rw [asmArm64List_one]
                      dsimp only [asmArm64, asmCmpIns, widthToRegWidth]
                      rw [setWidth_setWidth_self64 (by decide) cb, h1]; rfl
                  | gpr rd => cases rd with
                    | SP =>
                      dsimp only [armCmpImmIns?, armWidthOf] at hp
                      rw [h0b, h1] at hp; cases hp
                    | reg d =>
                      dsimp only [armCmpImmIns?, armWidthOf] at hp
                      rw [h0b, h1] at hp; cases hp
                      dsimp only [armCmpImmIns?, armWidthOf, vllArmCmpCore, Option.map_some]
                      rw [asmArm64List_two]
                      dsimp only [asmArm64, asmCmpIns, widthToRegWidth, armSetcc, armSetccIns]
                      rw [setWidth_setWidth_self64 (by decide) cb, h1, ← emitClean_append]
                      rfl
                | none =>
                  have h2 := hneg h1 h0
                  cases dst with
                  | vec v => exact v.elim
                  | flag cf =>
                    dsimp only [armCmpImmIns?, armWidthOf, armArgInIns] at hp
                    dsimp only [armCmpImmIns?, armWidthOf, armArgInIns, vllArmCmpCore]
                    rw [h0b, h1, h2] at hp
                    cases hc : (cf == armCmpCond o) <;>
                      simp only [hc, Bool.false_eq_true, ↓reduceIte] at hp ⊢
                    · cases hp
                    · cases hp; dsimp only [Option.map_some]; rw [asmArm64List_one]
                      dsimp only [asmArm64, asmCmpIns, armSrcToXIns, armRhsToXIns,
                        widthToRegWidth]
                      rw [setWidth_setWidth_self64 (by decide) cb, h1]; rfl
                  | gpr rd => cases rd with
                    | SP =>
                      dsimp only [armCmpImmIns?, armWidthOf, armArgInIns] at hp
                      rw [h0b, h1, h2] at hp; cases hp
                    | reg d =>
                      dsimp only [armCmpImmIns?, armWidthOf, armArgInIns] at hp
                      rw [h0b, h1, h2] at hp; cases hp
                      dsimp only [armCmpImmIns?, armWidthOf, armArgInIns, vllArmCmpCore,
                        Option.map_some]
                      rw [asmArm64List_two]
                      dsimp only [asmArm64, asmCmpIns, armSrcToXIns, armRhsToXIns,
                        widthToRegWidth, armSetcc, armSetccIns]
                      rw [setWidth_setWidth_self64 (by decide) cb, h1, ← emitClean_append]
                      rfl)
  | _ => exact hfb rfl

/-! ## 4. Pure `vllArmStrictIsa` ↔ `armIsa` Equalities & Core `Rega` Factoring Lemmas -/

@[expose, reducible] def liftSt (st : Rega.SymState vllArmStrictIsa) : Rega.SymState armIsa :=
  { regs := st.regs, slots := st.slots, defs := st.defs, vecWidths := st.vecWidths,
    memDefs := st.memDefs, zeroExt32 := st.zeroExt32, flags := st.flags }

@[expose] def liftJnz : Rega.JnzCond vllArmStrictIsa → Rega.JnzCond armIsa
  | .flag c => .flag c
  | .gpr r => .gpr r
  | .slot i => .slot i
  | .cmpZero co w r => .cmpZero co w r
  | .cmpZeroMem co w x a cnd => .cmpZeroMem co w x a cnd
  | .cmpZeroFlag co w x r cnd => .cmpZeroFlag co w x r cnd
  | .testImm neg w r m => .testImm neg w r m

theorem optMap_alt {α β : Type} (f : α → β) (x y : Option α) :
    (x <|> y).map f = (x.map f <|> y.map f) := by
  cases x <;> rfl

theorem optMap_bind {α β γ : Type} (f : β → γ) (x : Option α) (k : α → Option β) :
    (x.bind k).map f = x.bind (fun a => (k a).map f) := by
  cases x <;> rfl

theorem orElse_congr {α : Type} {a1 a2 b1 b2 : Option α}
    (ha : a1 = a2) (hb : b1 = b2) : (a1 <|> b1) = (a2 <|> b2) := by
  rw [ha, hb]

theorem listFindSome_map {α β γ : Type} (f : β → γ) (xs : List α) (k : α → Option β) :
    (xs.findSome? k).map f = xs.findSome? (fun a => (k a).map f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.findSome?_cons]
    cases k x with
    | none => exact ih
    | some _ => rfl

theorem strict_scratch : vllArmStrictIsa.frame.scratch = armScratch := rfl
theorem strict_alloc : vllArmStrictIsa.frame.allocatable = armFrame.allocatable := rfl
theorem strict_cs : vllArmStrictIsa.frame.calleeSaved = armFrame.calleeSaved := rfl
theorem strict_argRegs : vllArmStrictIsa.frame.argRegs = armFrame.argRegs := rfl
theorem strict_retRegs : vllArmStrictIsa.frame.retRegs = armFrame.retRegs := rfl
theorem strict_bitWidths : vllArmStrictIsa.frame.bitWidths = armFrame.bitWidths := rfl
theorem strict_frameSize : vllArmStrictIsa.frame.frameSize = armFrame.frameSize := rfl
theorem strict_leafZero : vllArmStrictIsa.frame.leafZeroFrame = armFrame.leafZeroFrame := rfl
theorem strict_condReads : vllArmStrictIsa.gpr.condReads = armCondReads := rfl
theorem strict_negCond : vllArmStrictIsa.gpr.negCond = armNegCond := rfl
theorem strict_zeroFlags : vllArmStrictIsa.gpr.zeroFlags = armZeroFlags := rfl
theorem strict_condOfCmp? : vllArmStrictIsa.gpr.condOfCmp? = armIsa.gpr.condOfCmp? := rfl
theorem strict_zeroUpper32Load :
    vllArmStrictIsa.gpr.zeroUpper32Load = armIsa.gpr.zeroUpper32Load := rfl
theorem strict_zeroExtLoad : vllArmStrictIsa.gpr.zeroExtLoad = armIsa.gpr.zeroExtLoad := rfl
theorem strict_zeroUpper32Op {sig rs : List Ty} (c : OpCode sig rs)
    (pas : Tup (PArg Arm64.Reg Empty ArmCond) sig) (dsts : Tup (PDst Arm64.Reg Empty ArmCond) rs) :
    vllArmStrictIsa.gpr.zeroUpper32Op c pas dsts = armIsa.gpr.zeroUpper32Op c pas dsts := rfl
theorem strict_elideZext32 : vllArmStrictIsa.gpr.elideZext32 = armIsa.gpr.elideZext32 := rfl
theorem strict_cmpFlagsOut? : vllArmStrictIsa.gpr.cmpFlagsOut? = armIsa.gpr.cmpFlagsOut? := rfl
theorem strict_boolFlagOut? {sig : List Ty} (c : OpCode sig [.bool])
    (ps : Tup (PArg Arm64.Reg Empty ArmCond) sig) (pd : PDst Arm64.Reg Empty ArmCond .bool) :
    vllArmStrictIsa.gpr.boolFlagOut? c ps pd = armIsa.gpr.boolFlagOut? c ps pd := rfl
theorem strict_aluZeroOut? {sig : List Ty} (w : Nat) (c : OpCode sig [.bits w])
    (pd : PDst Arm64.Reg Empty ArmCond (.bits w)) :
    vllArmStrictIsa.gpr.aluZeroOut? w c pd = armIsa.gpr.aluZeroOut? w c pd := rfl
theorem strict_hasTestFlags : vllArmStrictIsa.gpr.hasTestFlags = armIsa.gpr.hasTestFlags := rfl
theorem strict_cmpMemFlagsOut? :
    vllArmStrictIsa.gpr.cmpMemFlagsOut? = armIsa.gpr.cmpMemFlagsOut? := rfl

theorem strict_mov_asm (d s : Arm64.Reg) :
    asmArm64List (vllArmStrictIsa.gpr.mov d s) = armIsa.gpr.mov d s := by
  dsimp only [vllArmStrictIsa, vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, Option.getD]
  rw [asmArm64List_one]; rfl

theorem strict_movi_asm (d : Arm64.Reg) (c : BitVec 64) :
    asmArm64List (vllArmStrictIsa.gpr.movi d c) = armIsa.gpr.movi d c := by
  dsimp only [vllArmStrictIsa, vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, Option.getD]
  rw [asmArm64List_one]; rfl

theorem strict_slotLd_asm (d : Arm64.Reg) (i : Nat) :
    asmArm64List (vllArmStrictIsa.frame.slotLd d i) = armIsa.frame.slotLd d i := by
  dsimp only [vllArmStrictIsa, vllFrameIsaOfHooks, vllFrameIsa]
  rw [asmArm64List_one]; rfl

theorem strict_slotSt_asm (i : Nat) (s : Arm64.Reg) :
    asmArm64List (vllArmStrictIsa.frame.slotSt i s) = armIsa.frame.slotSt i s := by
  dsimp only [vllArmStrictIsa, vllFrameIsaOfHooks, vllFrameIsa]
  rw [asmArm64List_one]; rfl

theorem strict_setcc_asm (d : Arm64.Reg) (c : ArmCond) :
    asmArm64List (vllArmStrictIsa.gpr.setcc d c) = armIsa.gpr.setcc d c := by
  dsimp only [vllArmStrictIsa, vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, Option.getD]
  rw [asmArm64List_one]; rfl

theorem strict_clearFlags_asm :
    asmArm64List vllArmStrictIsa.gpr.clearFlags = armIsa.gpr.clearFlags := by
  dsimp only [vllArmStrictIsa, vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, Option.getD]
  rw [asmArm64List_one]; rfl

theorem strict_jmp_asm (l : Sym) :
    asmArm64List (vllArmStrictIsa.gpr.jmp l) = armIsa.gpr.jmp l := by
  dsimp only [vllArmStrictIsa, vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, Option.getD]
  rw [asmArm64List_one]; rfl

theorem strict_jcc_asm (c : ArmCond) (l : Sym) :
    asmArm64List (vllArmStrictIsa.gpr.jcc c l) = armIsa.gpr.jcc c l := by
  dsimp only [vllArmStrictIsa, vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, Option.getD]
  rw [asmArm64List_one]; rfl

theorem strict_jnzGpr_fst (r : Arm64.Reg) (l : Sym) :
    asmArm64List (vllArmStrictIsa.gpr.jnzGpr r l).1 = (armIsa.gpr.jnzGpr r l).1 :=
  asmArm64List_map_native (armJnzGpr r l).1

theorem strict_jnzGpr_snd (r : Arm64.Reg) (l : Sym) :
    (vllArmStrictIsa.gpr.jnzGpr r l).2 = (armIsa.gpr.jnzGpr r l).2 := rfl

theorem strict_canonAbi_fst (t : Ty) (r : Arm64.Reg) :
    asmArm64List (vllArmStrictIsa.frame.canonAbi t r).1 = (armIsa.frame.canonAbi t r).1 := by
  dsimp only [vllArmStrictIsa, vllFrameIsaOfHooks, vllFrameIsa]
  rw [asmArm64List_one]; rfl

theorem strict_prologue_fst (ns : Nat) :
    asmArm64List (vllArmStrictIsa.frame.prologue ns).1 = (armIsa.frame.prologue ns).1 := by
  dsimp only [vllArmStrictIsa, vllFrameIsaOfHooks, vllFrameIsa]
  rw [asmArm64List_one]; rfl

theorem strict_epilogue_fst (ns : Nat) :
    asmArm64List (vllArmStrictIsa.frame.epilogue ns).1 = (armIsa.frame.epilogue ns).1 := by
  dsimp only [vllArmStrictIsa, vllFrameIsaOfHooks, vllFrameIsa]
  rw [asmArm64List_one]; rfl

theorem strict_call_asm (f : Sym) :
    asmArm64List (vllArmStrictIsa.frame.call f) = armIsa.frame.call f := by
  dsimp only [vllArmStrictIsa, vllFrameIsaOfHooks, vllFrameIsa]
  rw [asmArm64List_one]; rfl

theorem strict_exitJmp_asm (f : Sym) :
    asmArm64List (vllArmStrictIsa.frame.exitJmp f) = armIsa.frame.exitJmp f := by
  dsimp only [vllArmStrictIsa, vllFrameIsaOfHooks, vllFrameIsa]
  rw [asmArm64List_one]; rfl

theorem strict_ret_asm :
    asmArm64List vllArmStrictIsa.frame.ret = armIsa.frame.ret := by
  dsimp only [vllArmStrictIsa, vllFrameIsaOfHooks, vllFrameIsa]
  rw [asmArm64List_one]; rfl

theorem strict_locEq (a b : armIsa.Loc) :
    @Rega.locEq vllArmStrictIsa a b = @Rega.locEq armIsa a b := by
  cases a <;> cases b <;> rfl

theorem strict_regLocEq (a b : Rega.RegLoc Arm64.Reg Empty ArmCond) :
    @Rega.regLocEq vllArmStrictIsa a b = @Rega.regLocEq armIsa a b := by
  cases a <;> cases b <;> rfl

theorem strict_regLocMatchesGpr (rl : Rega.RegLoc Arm64.Reg Empty ArmCond) (r : Arm64.Reg) :
    @Rega.regLocMatchesGpr vllArmStrictIsa rl r = @Rega.regLocMatchesGpr armIsa rl r := by
  cases rl <;> rfl

theorem strict_preEmpty (h : armIsa.Hints) (ip : Nat) :
    @Rega.preEmpty vllArmStrictIsa h ip = @Rega.preEmpty armIsa h ip := by
  dsimp only [Rega.preEmpty]; cases h.pre.find? ip <;> rfl

theorem strict_isAllocGpr (saved : List Arm64.Reg) (r : Arm64.Reg) :
    Rega.isAllocGpr vllArmStrictIsa saved r = Rega.isAllocGpr armIsa saved r := rfl

theorem strict_isMoveGpr (saved : List Arm64.Reg) (r : Arm64.Reg) :
    Rega.isMoveGpr vllArmStrictIsa saved r = Rega.isMoveGpr armIsa saved r := rfl

theorem strict_isGprTy (t : Ty) :
    Rega.isGprTy vllArmStrictIsa t = Rega.isGprTy armIsa t := by
  cases t <;> rfl

theorem strict_vecWidth? (t : Ty) :
    Rega.vecWidth? vllArmStrictIsa t = Rega.vecWidth? armIsa t := by
  cases t <;> rfl

theorem strict_toSymArg (t : Ty) (a : Arg Rega.VNat t) :
    Rega.toSymArg vllArmStrictIsa t a = Rega.toSymArg armIsa t a := by
  cases t <;> cases a <;> rfl

theorem strict_findGprFor (noScr : Bool)
    (R : List (SymArg × Rega.RegLoc Arm64.Reg Empty ArmCond)) (sa : SymArg) :
    Rega.findGprFor vllArmStrictIsa noScr R sa = Rega.findGprFor armIsa noScr R sa := by
  dsimp only [Rega.findGprFor]
  congr 1; funext p; cases p.2 <;> first | rfl | (dsimp only; rw [strict_scratch])

theorem strict_findFlagFor
    (R : List (SymArg × Rega.RegLoc Arm64.Reg Empty ArmCond)) (sa : SymArg) :
    Rega.findFlagFor vllArmStrictIsa R sa = Rega.findFlagFor armIsa R sa := by
  dsimp only [Rega.findFlagFor]; congr 1; funext ⟨_, rl⟩; cases rl <;> rfl

theorem strict_findVecFor (noScr : Bool)
    (R : List (SymArg × Rega.RegLoc Arm64.Reg Empty ArmCond)) (sa : SymArg) :
    Rega.findVecFor vllArmStrictIsa noScr R sa = Rega.findVecFor armIsa noScr R sa := by
  dsimp only [Rega.findVecFor]; congr 1; funext ⟨_, rl⟩
  cases rl with | vec v => exact v.elim | _ => rfl

theorem strict_keepRegLoc (gc : List Arm64.Reg) (vc : List Empty) (fc : FlagMask)
    (rl : Rega.RegLoc Arm64.Reg Empty ArmCond) :
    Rega.keepRegLoc vllArmStrictIsa gc vc fc rl = Rega.keepRegLoc armIsa gc vc fc rl := by
  cases rl <;> rfl

theorem strict_killRegs (gc : List Arm64.Reg) (vc : List Empty) (fc : FlagMask)
    (R : List (SymArg × Rega.RegLoc Arm64.Reg Empty ArmCond)) :
    Rega.killRegs vllArmStrictIsa gc vc fc R = Rega.killRegs armIsa gc vc fc R := by
  dsimp only [Rega.killRegs]
  congr 1; funext p; exact strict_keepRegLoc gc vc fc p.2

theorem strict_keepFlagCmp (fc : FlagMask) (eqNe : Bool) :
    Rega.keepFlagCmp vllArmStrictIsa fc eqNe = Rega.keepFlagCmp armIsa fc eqNe := by
  cases eqNe <;> rfl

theorem strict_killFlags (fc : FlagMask) (fl : Option Rega.FlagFact) :
    Rega.killFlags vllArmStrictIsa fc fl = Rega.killFlags armIsa fc fl := by
  cases fl with
  | none => rfl
  | some ff => cases ff; dsimp only [Rega.killFlags]; rw [strict_keepFlagCmp]

theorem strict_holdsLoc (st : Rega.SymState vllArmStrictIsa) (sa : SymArg)
    (loc : armIsa.Loc) :
    Rega.holdsLoc vllArmStrictIsa st sa loc = Rega.holdsLoc armIsa (liftSt st) sa loc := by
  cases loc with
  | gpr r => dsimp only [Rega.holdsLoc, liftSt]; congr 1; funext ⟨_, rl⟩; cases rl <;> rfl
  | vec v => exact v.elim
  | flag c => dsimp only [Rega.holdsLoc, liftSt]; congr 1; funext ⟨_, rl⟩; cases rl <;> rfl
  | slot i w => rfl

theorem strict_locBlocked (st : Rega.SymState vllArmStrictIsa)
    (pend : List (SymArg × armIsa.Loc)) (loc : armIsa.Loc) :
    Rega.locBlocked vllArmStrictIsa st pend loc =
      Rega.locBlocked armIsa (liftSt st) pend loc := by
  dsimp only [Rega.locBlocked, liftSt]; congr 1; funext ⟨sa, d'⟩
  rw [strict_locEq]; cases loc with
  | vec v => exact v.elim
  | flag _ | slot _ _ => rfl
  | gpr r =>
    dsimp only; congr 1; congr 1
    · congr 1; funext ⟨_, rl⟩; rw [strict_regLocMatchesGpr]
    · congr 1; funext ⟨_, rl⟩; rw [strict_regLocMatchesGpr]

theorem strict_gprTaggedEntries (r : Arm64.Reg)
    (R : List (SymArg × Rega.RegLoc Arm64.Reg Empty ArmCond)) :
    @Rega.gprTaggedEntries vllArmStrictIsa r R = @Rega.gprTaggedEntries armIsa r R := by
  dsimp only [Rega.gprTaggedEntries]; congr 1; funext ⟨_, rl⟩; dsimp only; cases rl <;> rfl

theorem strict_flagEntries (c : ArmCond)
    (R : List (SymArg × Rega.RegLoc Arm64.Reg Empty ArmCond)) :
    @Rega.flagEntries vllArmStrictIsa c R = @Rega.flagEntries armIsa c R := by
  dsimp only [Rega.flagEntries]; congr 1; funext ⟨_, rl⟩; dsimp only; cases rl <;> rfl

theorem strict_moveFor (nslots : Nat) (st : Rega.SymState vllArmStrictIsa)
    (sa : SymArg) (loc : armIsa.Loc) :
    Rega.moveFor vllArmStrictIsa nslots st sa loc =
      Rega.moveFor armIsa nslots (liftSt st) sa loc := by
  cases loc with
  | flag _ => rfl
  | vec v => exact v.elim
  | gpr d =>
    cases sa with
    | var _ => dsimp only [Rega.moveFor, liftSt]; rw [strict_findGprFor, strict_findFlagFor]
    | immBool _ | immBits _ _ | immVec _ _ => rfl
  | slot i w =>
    dsimp only [Rega.moveFor, liftSt]
    cases Rega.symArgWidth st.vecWidths sa with
    | none => dsimp only; rw [strict_findGprFor]
    | some _ => dsimp only; rw [strict_findVecFor]

theorem strict_slotBusy (st : Rega.SymState vllArmStrictIsa)
    (pend : List (SymArg × armIsa.Loc)) (i k : Nat) :
    Rega.slotBusy vllArmStrictIsa st pend i k =
      Rega.slotBusy armIsa (liftSt st) pend i k := by
  have hscan : ∀ fuel j,
      Rega.slotBusy.scan vllArmStrictIsa st i k j fuel =
        Rega.slotBusy.scan armIsa (liftSt st) i k j fuel := by
    intro fuel; induction fuel with
    | zero => intro _; rfl
    | succ f ih => intro j; dsimp only [Rega.slotBusy.scan, liftSt]; rw [ih]
  dsimp only [Rega.slotBusy]; rw [hscan]; congr 1; congr 1; funext ⟨_, loc⟩; dsimp only
  cases loc <;> rfl

theorem strict_findFreeSlot (nslots : Nat) (st : Rega.SymState vllArmStrictIsa)
    (pend : List (SymArg × armIsa.Loc)) (k : Nat) :
    Rega.findFreeSlot vllArmStrictIsa nslots st pend k =
      Rega.findFreeSlot armIsa nslots (liftSt st) pend k := by
  dsimp only [Rega.findFreeSlot]
  have hgo : ∀ (fuel i : Nat),
      Rega.findFreeSlot.go vllArmStrictIsa nslots st pend k i fuel =
        Rega.findFreeSlot.go armIsa nslots (liftSt st) pend k i fuel := by
    intro fuel
    induction fuel with
    | zero => intro _; rfl
    | succ fuel ih =>
      intro i; dsimp only [Rega.findFreeSlot.go]
      rw [strict_slotBusy, ih]
  exact hgo nslots 0

theorem strict_abiTargets :
    ∀ {ts : List Ty} (args : Tup (Arg Rega.VNat) ts) (locs : Tup (AbiReg Arm64.Reg Empty) ts),
      Rega.abiTargets vllArmStrictIsa args locs = Rega.abiTargets armIsa args locs
  | [], (), () => rfl
  | t :: _, (a, as), (loc, locs) => by
    dsimp only [Rega.abiTargets]
    rw [strict_toSymArg, strict_abiTargets as locs]
    cases Rega.toSymArg armIsa t a <;> cases Rega.abiTargets armIsa as locs <;>
      first | rfl | (cases loc with | gpr _ => rfl | vec v => exact v.elim)

theorem strict_hasVarGpr (R : List (SymArg × Rega.RegLoc Arm64.Reg Empty ArmCond))
    (x : Nat) (rd : Arm64.Reg) :
    Rega.hasVarGpr vllArmStrictIsa R x rd = Rega.hasVarGpr armIsa R x rd := by
  dsimp only [Rega.hasVarGpr]; congr 1; funext ⟨_, rl⟩; dsimp only; rw [strict_regLocMatchesGpr]

theorem strict_hasVarGprZ (R : List (SymArg × Rega.RegLoc Arm64.Reg Empty ArmCond))
    (x : Nat) (rd : Arm64.Reg) :
    Rega.hasVarGprZ vllArmStrictIsa R x rd = Rega.hasVarGprZ armIsa R x rd := by
  dsimp only [Rega.hasVarGprZ]; congr 1; funext ⟨_, rl⟩; dsimp only; rw [strict_regLocEq]

theorem strict_abiHeld (R : List (SymArg × Rega.RegLoc Arm64.Reg Empty ArmCond))
    (z : List Arm64.Reg) (t : Ty) (r : Arm64.Reg) (sa : SymArg) :
    Rega.abiHeld vllArmStrictIsa R z t r sa = Rega.abiHeld armIsa R z t r sa := by
  cases sa with
  | var _ =>
    dsimp only [Rega.abiHeld]; rw [strict_hasVarGpr]; congr 1; congr 1; funext ⟨_, rl⟩
    dsimp only; rw [strict_regLocEq]
  | immBits _ _ =>
    dsimp only [Rega.abiHeld]; congr 1; funext ⟨_, rl⟩; dsimp only; rw [strict_regLocMatchesGpr]
  | immBool _ =>
    dsimp only [Rega.abiHeld]; congr 1; funext ⟨_, rl⟩; dsimp only; rw [strict_regLocMatchesGpr]
  | immVec _ _ => rfl

theorem strict_abiSkips (R : List (SymArg × Rega.RegLoc Arm64.Reg Empty ArmCond))
    (z : List Arm64.Reg) :
    ∀ {ts : List Ty} (args : Tup (Arg Rega.VNat) ts) (locs : Tup (AbiReg Arm64.Reg Empty) ts),
      Rega.abiSkips vllArmStrictIsa R z args locs = Rega.abiSkips armIsa R z args locs
  | [], (), () => rfl
  | t :: _, (a, as), (loc, locs) => by
    dsimp only [Rega.abiSkips]
    rw [strict_toSymArg, strict_abiSkips R z as locs]
    congr 1; cases loc with
    | vec v => exact v.elim
    | gpr r => cases Rega.toSymArg armIsa t a with
      | none => rfl
      | some sa => exact strict_abiHeld R z t r sa

theorem strict_resolveDsts (h : armIsa.Hints) :
    ∀ (ts : List Ty) (nv : Nat),
      Rega.resolveDsts vllArmStrictIsa h ts nv = Rega.resolveDsts armIsa h ts nv
  | [], _ => rfl
  | t :: ts, nv => by
    dsimp only [Rega.resolveDsts]
    rw [strict_resolveDsts h ts (nv + 1)]
    cases h.dest.find? nv with
    | none => rfl
    | some loc =>
      dsimp only
      cases Rega.resolveDsts armIsa h ts (nv + 1) with
      | none => cases loc <;> rfl
      | some rest => cases loc with
        | gpr r => dsimp only; rw [strict_isAllocGpr, strict_isGprTy]
        | vec v => exact v.elim
        | flag c => rfl
        | slot _ _ => rfl

theorem strict_bindDsts :
    ∀ {ts : List Ty} (dsts : Tup (PDst Arm64.Reg Empty ArmCond) ts) (nv : Nat)
      (acc : List (SymArg × Rega.RegLoc Arm64.Reg Empty ArmCond) × Trie SlotWidth),
      Rega.bindDsts vllArmStrictIsa dsts nv acc = Rega.bindDsts armIsa dsts nv acc
  | [], (), _, _ => rfl
  | _ :: _, (d, ds), nv, (regs, vw) => by
    dsimp only [Rega.bindDsts]
    cases d with
    | vec v => exact v.elim
    | gpr _ | flag _ => exact strict_bindDsts ds (nv + 1) _

theorem strict_elideZext32? (R : List (SymArg × Rega.RegLoc Arm64.Reg Empty ArmCond))
    (z : List Arm64.Reg) {sig ts : List Ty} (code : OpCode sig ts)
    (args : Tup (Arg Rega.VNat) sig) (dsts : Tup (PDst Arm64.Reg Empty ArmCond) ts) :
    Rega.elideZext32? vllArmStrictIsa R z code args dsts =
      Rega.elideZext32? armIsa R z code args dsts := by
  cases code with
  | zext m n =>
    rcases args with ⟨a, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases a with | imm _ => rfl | var x =>
    cases pd with | vec v => exact v.elim | gpr rd =>
      dsimp only [Rega.elideZext32?]
      rw [strict_elideZext32, strict_hasVarGprZ, strict_hasVarGpr]
  | _ => rfl

theorem strict_elideTrunc? (R : List (SymArg × Rega.RegLoc Arm64.Reg Empty ArmCond))
    {sig ts : List Ty} (code : OpCode sig ts) (args : Tup (Arg Rega.VNat) sig)
    (dsts : Tup (PDst Arm64.Reg Empty ArmCond) ts) :
    Rega.elideTrunc? vllArmStrictIsa R code args dsts =
      Rega.elideTrunc? armIsa R code args dsts := by
  cases code with
  | trunc m n =>
    rcases args with ⟨a, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases a with | imm _ => rfl | var x =>
    cases pd with | vec v => exact v.elim | gpr rd =>
      dsimp only [Rega.elideTrunc?]
      rw [strict_hasVarGpr, strict_elideZext32, strict_zeroUpper32Op]
  | _ => rfl

theorem strict_normCmpOp :
    ∀ {ts : List Ty} (op : Op Rega.VNat ts) (dsts : Tup (PDst Arm64.Reg Empty ArmCond) ts),
      Rega.normCmpOp (I := vllArmStrictIsa) op dsts = Rega.normCmpOp (I := armIsa) op dsts
  | [.bool], ⟨code, args⟩, (pd, ()) => by
    cases code with
    | cmp co ty m hm =>
      cases ty with
      | bits n =>
        cases pd with | gpr _ => rfl | flag _ => rfl | vec v => exact v.elim
      | bool | float _ => rfl
      | pair _ _ => cases hm
    | _ => rfl
  | [], _, _ => rfl
  | [.bits _], _, _ => rfl
  | [.float _], _, _ => rfl
  | [.pair _ _], _, _ => rfl
  | t1 :: _ :: _, _, _ => by cases t1 <;> rfl

theorem strict_opProducesZ32 {sig : List Ty} :
    ∀ {ts : List Ty} (code : OpCode sig ts) (pas : Tup (PArg Arm64.Reg Empty ArmCond) sig)
      (dsts : Tup (PDst Arm64.Reg Empty ArmCond) ts),
      Rega.opProducesZ32 vllArmStrictIsa code pas dsts =
        Rega.opProducesZ32 armIsa code pas dsts
  | [], _, _, _ => rfl
  | [.bool], _, _, _ => rfl
  | [.float _], _, _, _ => rfl
  | [.pair _ _], _, _, _ => rfl
  | [.bits _], _, _, (.gpr _, ()) => rfl
  | [.bits _], _, _, (.vec v, ()) => v.elim
  | t1 :: _ :: _, _, _, _ => by cases t1 <;> rfl

theorem strict_cmpOpFlags? (st : Rega.SymState vllArmStrictIsa) :
    ∀ {sig ts : List Ty} (code : OpCode sig ts) (args : Tup (Arg Rega.VNat) sig)
      (pas : Tup (PArg Arm64.Reg Empty ArmCond) sig)
      (dsts : Tup (PDst Arm64.Reg Empty ArmCond) ts) (nv : Nat) (cl : FlagMask),
      Rega.cmpOpFlags? vllArmStrictIsa st code args pas dsts nv cl =
        Rega.cmpOpFlags? armIsa (liftSt st) code args pas dsts nv cl
  | _, [], _, _, _, _, _, _ => by dsimp only [Rega.cmpOpFlags?]; rw [strict_killFlags]
  | _, t1 :: _ :: _, _, _, _, _, _, _ => by
    cases t1 <;> (dsimp only [Rega.cmpOpFlags?]; rw [strict_killFlags])
  | _, [.float _], _, _, _, _, _, _ => by dsimp only [Rega.cmpOpFlags?]; rw [strict_killFlags]
  | _, [.pair _ _], _, _, _, _, _, _ => by dsimp only [Rega.cmpOpFlags?]; rw [strict_killFlags]
  | _, [.bits w], code, args, pas, (pd, ()), nv, cl => by
    dsimp only [Rega.cmpOpFlags?]
    rw [strict_aluZeroOut?, strict_killFlags]
  | _, [.bool], code, args, pas, (pd, PUnit.unit), nv, cl => by
    cases code with
    | cmp co ty m hm =>
      cases ty with
      | bits w =>
        rcases args with ⟨a, b, ⟨⟩⟩; rcases pas with ⟨pa, pb, ⟨⟩⟩; cases hm
        cases pd with
        | vec v => exact v.elim
        | flag cf =>
          change (if Nat.ble w 64 then
              match vllArmStrictIsa.gpr.cmpFlagsOut? co w pa pb (.flag cf),
                  Rega.toSymArg vllArmStrictIsa (.bits w) a,
                  Rega.toSymArg vllArmStrictIsa (.bits w) b with
              | some lf, some sa, some sb =>
                some (.cmp w (if lf then sa else sb) (if lf then sb else sa) false)
              | _, _, _ => Rega.killFlags vllArmStrictIsa cl st.flags
            else Rega.killFlags vllArmStrictIsa cl st.flags, none) =
            (if Nat.ble w 64 then
              match armIsa.gpr.cmpFlagsOut? co w pa pb (.flag cf),
                  Rega.toSymArg armIsa (.bits w) a,
                  Rega.toSymArg armIsa (.bits w) b with
              | some lf, some sa, some sb =>
                some (.cmp w (if lf then sa else sb) (if lf then sb else sa) false)
              | _, _, _ => Rega.killFlags armIsa cl (liftSt st).flags
            else Rega.killFlags armIsa cl (liftSt st).flags, none)
          rw [strict_cmpFlagsOut?, strict_toSymArg, strict_toSymArg, strict_killFlags]
        | gpr rd =>
          change (if Nat.ble w 64 then
              match vllArmStrictIsa.gpr.cmpFlagsOut? co w pa pb (.gpr rd),
                  Rega.toSymArg vllArmStrictIsa (.bits w) a,
                  Rega.toSymArg vllArmStrictIsa (.bits w) b with
              | some lf, some sa, some sb =>
                some (.cmp w (if lf then sa else sb) (if lf then sb else sa) false)
              | _, _, _ => Rega.killFlags vllArmStrictIsa cl st.flags
            else Rega.killFlags vllArmStrictIsa cl st.flags,
            if Nat.ble w 64 then
              (vllArmStrictIsa.gpr.cmpFlagsOut? co w pa pb (.gpr rd)).bind fun lf =>
                vllArmStrictIsa.gpr.condOfCmp? (if lf then co else co.swap)
            else none) =
            (if Nat.ble w 64 then
              match armIsa.gpr.cmpFlagsOut? co w pa pb (.gpr rd),
                  Rega.toSymArg armIsa (.bits w) a,
                  Rega.toSymArg armIsa (.bits w) b with
              | some lf, some sa, some sb =>
                some (.cmp w (if lf then sa else sb) (if lf then sb else sa) false)
              | _, _, _ => Rega.killFlags armIsa cl (liftSt st).flags
            else Rega.killFlags armIsa cl (liftSt st).flags,
            if Nat.ble w 64 then
              (armIsa.gpr.cmpFlagsOut? co w pa pb (.gpr rd)).bind fun lf =>
                armIsa.gpr.condOfCmp? (if lf then co else co.swap)
            else none)
          rw [strict_cmpFlagsOut?, strict_toSymArg, strict_toSymArg, strict_killFlags,
            strict_condOfCmp?]
      | bool | float _ =>
        cases hm; cases pd with
        | vec v => exact v.elim
        | flag _ =>
          change (Rega.killFlags vllArmStrictIsa cl st.flags, none) =
            (Rega.killFlags armIsa cl (liftSt st).flags, none)
          rw [strict_killFlags]
        | gpr rd =>
          change (Rega.killFlags vllArmStrictIsa cl st.flags,
              vllArmStrictIsa.gpr.boolFlagOut? _ pas (.gpr rd)) =
            (Rega.killFlags armIsa cl (liftSt st).flags,
              armIsa.gpr.boolFlagOut? _ pas (.gpr rd))
          rw [strict_killFlags, strict_boolFlagOut?]
      | pair _ _ => cases hm
    | _ => cases pd with
      | vec v => exact v.elim
      | flag _ =>
        change (Rega.killFlags vllArmStrictIsa cl st.flags, none) =
          (Rega.killFlags armIsa cl (liftSt st).flags, none)
        rw [strict_killFlags]
      | gpr rd =>
        change (Rega.killFlags vllArmStrictIsa cl st.flags,
            vllArmStrictIsa.gpr.boolFlagOut? _ pas (.gpr rd)) =
          (Rega.killFlags armIsa cl (liftSt st).flags,
            armIsa.gpr.boolFlagOut? _ pas (.gpr rd))
        rw [strict_killFlags, strict_boolFlagOut?]

theorem strict_jumpTargets :
    ∀ {ts : List Ty} (args : Tup (Arg Rega.VNat) ts) (locs : List armIsa.Loc),
      Rega.jumpTargets vllArmStrictIsa args locs = Rega.jumpTargets armIsa args locs
  | [], (), [] => rfl
  | t :: _, (a, as), loc :: locs => by
    dsimp only [Rega.jumpTargets]
    rw [strict_toSymArg, strict_jumpTargets as locs]
    cases Rega.toSymArg armIsa t a <;> cases Rega.jumpTargets armIsa as locs <;> rfl
  | [], (), _ :: _ | _ :: _, _, [] => rfl

theorem strict_jumpLocOk (nslots : Nat) (loc : armIsa.Loc) :
    Rega.jumpLocOk vllArmStrictIsa nslots loc = Rega.jumpLocOk armIsa nslots loc := by
  cases loc <;> rfl

theorem strict_zeroMoveJump? {rs : List Ty} (h : armIsa.Hints) (ip : Nat)
    (st : Rega.SymState vllArmStrictIsa) (e : Expr Rega.VNat Rega.LNat rs) :
    Rega.zeroMoveJump? vllArmStrictIsa h ip st e =
      Rega.zeroMoveJump? armIsa h ip (liftSt st) e := by
  cases e with
  | jump j args =>
    dsimp only [Rega.zeroMoveJump?]
    rw [strict_preEmpty]
    split
    · rfl
    · cases h.entry.find? j with
      | none => rfl
      | some en =>
        dsimp only [Option.bind_some]
        rw [strict_jumpTargets]
        cases Rega.jumpTargets armIsa args en.ploc with
        | none => rfl
        | some argTgts =>
          dsimp only [Option.bind_some]
          have hall : (en.live ++ argTgts).all (fun (sa, loc) =>
              Rega.jumpLocOk vllArmStrictIsa h.nslots loc &&
                Rega.holdsLoc vllArmStrictIsa st sa loc) =
            (en.live ++ argTgts).all (fun (sa, loc) =>
              Rega.jumpLocOk armIsa h.nslots loc &&
                Rega.holdsLoc armIsa (liftSt st) sa loc) := by
            congr 1; funext ⟨sa, loc⟩; dsimp only; rw [strict_jumpLocOk, strict_holdsLoc]
          rw [hall]
  | _ => rfl

theorem strict_jnzMode {rs : List Ty} (h : armIsa.Hints) (ipT ipE : Nat)
    (st : Rega.SymState vllArmStrictIsa) (canInv : Bool)
    (t e : Expr Rega.VNat Rega.LNat rs) (ft : Option Nat) (fwd : Trie Nat) :
    Rega.jnzMode vllArmStrictIsa h ipT ipE st canInv t e ft fwd =
      Rega.jnzMode armIsa h ipT ipE (liftSt st) canInv t e ft fwd := by
  dsimp only [Rega.jnzMode]
  rw [strict_zeroMoveJump?, strict_zeroMoveJump?]

theorem strict_gprThread? {rs : List Ty} (h : armIsa.Hints) (fn : Sym) (ipT : Nat)
    (st1 : Rega.SymState vllArmStrictIsa) (r : Arm64.Reg) (arm : Expr Rega.VNat Rega.LNat rs)
    (fwd : Trie Nat) :
    Rega.gprThread? vllArmStrictIsa h fn ipT st1 r arm fwd =
      Rega.gprThread? armIsa h fn ipT (liftSt st1) r arm fwd := by
  cases arm with
  | jump j args =>
    dsimp only [Rega.gprThread?]
    rw [strict_zeroMoveJump?]
    dsimp only [liftSt]
    rw [strict_jnzGpr_snd, strict_scratch, strict_killRegs, strict_killFlags]
  | _ => rfl

theorem strict_isZeroLeaf (h : armIsa.Hints) (E : Rega.Ext) :
    Rega.isZeroLeaf vllArmStrictIsa h E = Rega.isZeroLeaf armIsa h E := rfl

theorem strict_effFrame (h : armIsa.Hints) (E : Rega.Ext) :
    Rega.effFrame vllArmStrictIsa h E = Rega.effFrame armIsa h E := rfl

theorem strict_assignSig :
    ∀ (ts : List Ty) (gs : List Arm64.Reg) (vs : List Empty),
      vllArmStrictIsa.assignSig ts gs vs = armIsa.assignSig ts gs vs
  | [], _, _ => rfl
  | .bool :: ts, _ :: gs, vs => by
    dsimp only [Isa.assignSig]; rw [strict_assignSig ts gs vs]
  | .bits _ :: ts, _ :: gs, vs => by
    dsimp only [Isa.assignSig]; rw [strict_bitWidths, strict_assignSig ts gs vs]
  | .pair _ _ :: _, _, v :: _ => v.elim
  | .bool :: _, [], _ | .bits _ :: _, [], _ | .pair _ _ :: _, _, [] | .float _ :: _, _, _ => rfl

theorem strict_assignArgs (ts : List Ty) :
    vllArmStrictIsa.assignArgs ts = armIsa.assignArgs ts := by
  dsimp only [Isa.assignArgs]; rw [strict_argRegs]; exact strict_assignSig ts _ []

theorem strict_assignRets (ts : List Ty) :
    vllArmStrictIsa.assignRets ts = armIsa.assignRets ts := by
  dsimp only [Isa.assignRets]; rw [strict_retRegs]; exact strict_assignSig ts _ []

theorem strict_reuseCmpPair? (defs : Trie Rega.DefFact) (w : Nat) (lhs rhs : SymArg)
    (n : Nat) (co : CmpOp) (a b : Arg Rega.VNat (.bits n)) :
    Rega.reuseCmpPair? vllArmStrictIsa defs w lhs rhs n co a b =
      Rega.reuseCmpPair? armIsa defs w lhs rhs n co a b := by
  dsimp only [Rega.reuseCmpPair?]
  simp only [strict_toSymArg]

theorem strict_cmpZeroFlagCond? (defs : Trie Rega.DefFact) (fl : Option Rega.FlagFact)
    (co : CmpOp) (w y : Nat) :
    Rega.cmpZeroFlagCond? vllArmStrictIsa defs fl co w y =
      Rega.cmpZeroFlagCond? armIsa defs fl co w y := by
  cases fl with
  | none => rfl
  | some ff =>
    cases ff with
    | cmp w' lhs rhs eqNe =>
      dsimp only [Rega.cmpZeroFlagCond?]
      rw [strict_reuseCmpPair?]
      cases Rega.reuseCmpPair? armIsa defs w' lhs rhs w co (.var y) (.imm 0#w) with
      | none => rfl
      | some p =>
        dsimp only [Option.bind_some]
        split
        · dsimp only [Option.bind_some]
          split <;> first | rfl | exact congrFun strict_condOfCmp? _
        · split
          · dsimp only [Option.bind_some]
            split <;> first | rfl | exact congrFun strict_condOfCmp? _
          · rfl

theorem strict_testBoolExtra? (neg : Bool) (cl : FlagMask)
    (pd : PDst Arm64.Reg Empty ArmCond .bool) :
    Rega.testBoolExtra? vllArmStrictIsa neg cl pd =
      Rega.testBoolExtra? armIsa neg cl pd := by
  cases pd with
  | vec v => exact v.elim
  | flag _ =>
    dsimp only [Rega.testBoolExtra?, vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks]; rfl
  | gpr _ =>
    dsimp only [Rega.testBoolExtra?, vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks]; rfl

theorem tryReuseFlagCmp_factor (st : Rega.SymState vllArmStrictIsa)
    {sig ts : List Ty} (code : OpCode sig ts) (args : Tup (Arg Rega.VNat) sig)
    (dsts : Tup (PDst Arm64.Reg Empty ArmCond) ts) :
    (Rega.tryReuseFlagCmp vllArmStrictIsa st code args dsts).map
      (fun (c, cl, fl, ex) => (asmArm64List c, cl, fl, ex)) =
      Rega.tryReuseFlagCmp armIsa (liftSt st) code args dsts := by
  dsimp only [Rega.tryReuseFlagCmp, liftSt]
  cases st.flags with
  | none => rfl
  | some ff =>
    cases ff with
    | cmp w lhs rhs eqNe =>
      cases code with
      | cmp co ty m hm =>
        subst hm; cases ty with
        | bool | float _ | pair _ _ => rfl
        | bits n =>
          rcases args with ⟨a, b, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
          dsimp only
          rw [strict_reuseCmpPair?]
          cases Rega.reuseCmpPair? armIsa st.defs w lhs rhs n co a b with
          | none => rfl
          | some p =>
            rcases p with ⟨coBase, sa, sb⟩
            simp only [Option.bind_some]
            cases (if Rega.symArgEq sa lhs && Rega.symArgEq sb rhs then some coBase
                else if Rega.symArgEq sa rhs && Rega.symArgEq sb lhs then some coBase.swap
                else none) with
            | none => rfl
            | some coUsed =>
              dsimp only [Option.bind_some]
              split
              · rfl
              · dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks,
                  Function.comp_def]
                simp only [Option.bind_some]
                cases pd with
                | vec v => exact v.elim
                | flag cd =>
                  cases heq : (cd == armCmpCond coUsed) <;>
                    simp only [heq, Bool.false_eq_true, ↓reduceIte,
                      Option.map_none, Option.map_some] <;> rfl
                | gpr rd =>
                  cases rd with
                  | SP =>
                    dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks,
                      armOp, armOpIns, emitCleanPair]
                    rfl
                  | reg d =>
                    dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks,
                      armOp, armOpIns, armBoolOpIns, emitCleanPair, vllArmOpHook, vllCoreOp,
                      vllCoreCopy]
                    simp only [Option.isSome_some, ↓reduceIte, Option.map_some]
                    rw [strict_killFlags, asmArm64List_one]; rfl
      | _ => rfl

private theorem armMovImmI_ne_nil (d : XReg) (c : BitVec 64) : armMovImmI d c ≠ [] := by
  unfold armMovImmI
  split; · simp
  split; · simp
  split; · simp
  split; · simp
  split; · simp
  split; · simp
  split <;> simp

private theorem armMovi_ne_nil (d : Arm64.Reg) (c : BitVec 64) : armMovi d c ≠ [] := by
  cases d with
  | reg x =>
    simp only [armMovi, armMoviIns, emitClean, ne_eq, List.map_eq_nil_iff]
    exact armMovImmI_ne_nil x c
  | SP => simp [armMovi, armMoviIns, emitClean]

private theorem armSlotSt_ne_nil (i : Nat) (r : Arm64.Reg) : armSlotSt i r ≠ [] := by
  cases r <;> (dsimp only [armSlotSt, armSlotStIns, armStSpXRegIns]; split <;> simp [emitClean])

private theorem armSlotLd_ne_nil (d : Arm64.Reg) (i : Nat) : armSlotLd d i ≠ [] := by
  cases d <;> (dsimp only [armSlotLd, armSlotLdIns, armLdSpXRegIns]; split <;> simp [emitClean])

private theorem armSetcc_ne_nil (d : Arm64.Reg) (c : ArmCond) : armSetcc d c ≠ [] := by
  cases d <;> simp [armSetcc, armSetccIns, emitClean]

theorem tryFlag_map {α β : Type} (f : α → β)
    (R : List (SymArg × Rega.RegLoc Arm64.Reg Empty ArmCond)) (pref : List ArmCond)
    (sa : SymArg) (k : ArmCond → Option α) :
    (Rega.tryFlag vllArmStrictIsa R pref sa k).map f =
      Rega.tryFlag armIsa R pref sa (fun c => (k c).map f) := by
  dsimp only [Rega.tryFlag]
  rw [optMap_alt, listFindSome_map, listFindSome_map]
  refine orElse_congr ?_ ?_
  · congr 1; funext c
    have hrl : (R.any fun (sa', rl) => Rega.symArgEq sa' sa &&
        @Rega.regLocEq vllArmStrictIsa rl (.flag c)) =
      (R.any fun (sa', rl) => Rega.symArgEq sa' sa &&
        @Rega.regLocEq armIsa rl (.flag c)) := by
      congr 1; funext ⟨_, rl⟩; dsimp only; rw [strict_regLocEq]
    rw [hrl]; split <;> rfl
  · congr 1; funext ⟨sa', rl⟩; cases rl <;> first | rfl | (dsimp only; split <;> rfl)

theorem tryGpr_map {α β : Type} (f : α → β)
    (R : List (SymArg × Rega.RegLoc Arm64.Reg Empty ArmCond)) (sa : SymArg)
    (k : Arm64.Reg → Option α) :
    (Rega.tryGpr vllArmStrictIsa R sa k).map f =
      Rega.tryGpr armIsa R sa (fun r => (k r).map f) := by
  dsimp only [Rega.tryGpr]; rw [listFindSome_map]
  congr 1; funext ⟨sa', rl⟩
  cases rl <;> first | rfl | (dsimp only; rw [strict_scratch]; split <;> rfl)

theorem tryArg_map {α β : Type} (f : α → β) (st : Rega.SymState vllArmStrictIsa)
    (pref : List ArmCond) (t : Ty) (a : Arg Rega.VNat t)
    (k : PArg Arm64.Reg Empty ArmCond t → Option α) :
    (Rega.tryArg vllArmStrictIsa st pref t a k).map f =
      Rega.tryArg armIsa (liftSt st) pref t a (fun pa => (k pa).map f) := by
  cases t <;> cases a <;> dsimp only [Rega.tryArg, liftSt]
  · rw [optMap_alt]; exact orElse_congr (tryFlag_map ..) (tryGpr_map ..)
  · rw [optMap_alt, optMap_alt]
    exact orElse_congr (tryFlag_map ..) (orElse_congr rfl (tryGpr_map ..))
  · exact tryGpr_map f st.regs _ _
  · rw [optMap_alt]; refine orElse_congr rfl ?_
    split
    · exact tryGpr_map f st.regs _ _
    · rfl
  · rfl
  · rfl
  · dsimp only [Rega.tryVec]; rw [listFindSome_map]
    congr 1; funext ⟨_, rl⟩; cases rl with | vec v => exact v.elim | _ => rfl
  · rw [optMap_alt]; exact orElse_congr rfl rfl

theorem pickPArgs_map {α β : Type} (f : α → β) (st : Rega.SymState vllArmStrictIsa)
    (pref : List ArmCond) :
    ∀ {sig : List Ty} (args : Tup (Arg Rega.VNat) sig)
      (k : Tup (PArg Arm64.Reg Empty ArmCond) sig → Option α),
      (Rega.pickPArgs vllArmStrictIsa st pref args k).map f =
        Rega.pickPArgs armIsa (liftSt st) pref args (fun pas => (k pas).map f)
  | [], (), _ => rfl
  | t :: _, (a, as), k => by
    dsimp only [Rega.pickPArgs]
    rw [tryArg_map f st pref t a]; congr 1; funext pa
    exact pickPArgs_map f st pref as (fun pas => k (pa, pas))

theorem tryAddr_map {α β : Type} (f : α → β) (st : Rega.SymState vllArmStrictIsa)
    (vh : VariantHint) (a : Arg Rega.VNat i64) (k : AddrArg Arm64.Reg → Option α) :
    (Rega.tryAddr vllArmStrictIsa st vh a k).map f =
      Rega.tryAddr armIsa (liftSt st) vh a (fun aa => (k aa).map f) := by
  cases a with
  | imm c =>
    dsimp only [Rega.tryAddr, liftSt]
    rw [optMap_alt, optMap_bind, strict_findGprFor]
  | var x =>
    dsimp only [Rega.tryAddr, liftSt]
    rw [optMap_alt, optMap_alt]
    refine orElse_congr ?_ (orElse_congr ?_ ?_)
    · cases vh with
      | default | adcx | adox | mulxFast | decInc => rfl
      | disp off =>
        cases st.defs.find? x with
        | none => rfl
        | some df => cases df with
          | addImm64 base d =>
            dsimp only; split
            · rw [optMap_bind, strict_findGprFor]
            · rfl
          | _ => rfl
    · rw [optMap_bind, strict_findGprFor]
    · cases st.defs.find? x with
      | none => rfl
      | some df => cases df with
        | addImm64 base d => dsimp only; rw [optMap_bind, strict_findGprFor]
        | addrSum base idx sh d =>
          dsimp only
          rw [optMap_bind]; congr 1; funext sc
          rw [optMap_bind, strict_findGprFor]; congr 1; funext rb
          rw [optMap_bind, strict_findGprFor]
        | imm64 _ => rfl
        | _ => rfl

theorem tryAddrZext_map {α β : Type} (f : α → β) (st : Rega.SymState vllArmStrictIsa)
    (a : Arg Rega.VNat i64) (k : Arm64.Reg → Arm64.Reg → AddrScale → Int64 → Option α) :
    (Rega.tryAddrZext vllArmStrictIsa st a k).map f =
      Rega.tryAddrZext armIsa (liftSt st) a (fun rb ri sc d => (k rb ri sc d).map f) := by
  cases a with
  | imm _ => rfl
  | var x =>
    dsimp only [Rega.tryAddrZext, liftSt]
    cases st.defs.find? x with
    | none => rfl
    | some df => cases df with
      | addrSum b i sh d =>
        dsimp only
        cases Rega.zextAddrSumVar? st.defs b i sh with
        | none => rfl
        | some p =>
          rcases p with ⟨rbVar, ridxVar, _⟩
          dsimp only
          rw [optMap_bind]; congr 1; funext sc
          rw [optMap_bind, strict_findGprFor]; congr 1; funext rb
          rw [optMap_bind, strict_findGprFor]
      | _ => rfl

theorem execMove_factor {deadHint : Bool} (nslots : Nat) (saved : List Arm64.Reg)
    (mv : armIsa.Move) (st : Rega.SymState vllArmStrictIsa) :
    (Rega.execMove vllArmStrictIsa nslots saved mv st deadHint).map
      (fun (c, st') => (asmArm64List c, liftSt st')) =
      Rega.execMove armIsa nslots saved mv (liftSt st) deadHint := by
  cases mv with
  | mov d s =>
    dsimp only [Rega.execMove, liftSt]
    rw [strict_isMoveGpr]; split
    · rfl
    · split
      · dsimp only [Option.map_some]; rw [strict_mov_asm]
      · dsimp only [Option.map_some, liftSt]
        rw [strict_mov_asm, strict_gprTaggedEntries, strict_killRegs]
  | movi d c =>
    dsimp only [Rega.execMove, liftSt]
    rw [strict_isMoveGpr]; split
    · rfl
    · have hmd1 : vllArmStrictIsa.gpr.moviDeadFlags? = none := rfl
      have hm1 : Rega.execMovi vllArmStrictIsa st deadHint d c =
          (vllArmStrictIsa.gpr.movi d c, FlagMask.none) := by
        dsimp only [Rega.execMovi]; rw [hmd1]
      have hm2 : Rega.execMovi armIsa (liftSt st) deadHint d c =
          (armIsa.gpr.movi d c, FlagMask.none) := rfl
      simp only [Option.map_some, hm1, hm2, beq_self_eq_true, ↓reduceIte]
      rw [strict_movi_asm, strict_scratch, strict_killRegs]
  | ld d i =>
    dsimp only [Rega.execMove, liftSt]
    rw [strict_isAllocGpr]; split
    · rfl
    · dsimp only [Option.map_some, liftSt]; rw [strict_slotLd_asm, strict_scratch, strict_killRegs]
  | st i s =>
    dsimp only [Rega.execMove, liftSt]
    rw [strict_scratch]; split
    · rfl
    · dsimp only [Option.map_some, liftSt]
      rw [strict_slotSt_asm, strict_gprTaggedEntries, strict_killRegs]
  | setcc d c =>
    dsimp only [Rega.execMove, liftSt]
    rw [strict_isAllocGpr]; split
    · rfl
    · dsimp only [Option.map_some, liftSt]
      rw [strict_setcc_asm, strict_flagEntries, strict_scratch, strict_killRegs]
  | vmov _ d _ | vmovi _ d _ | vld _ d _ | vst _ _ d => exact d.elim

theorem execMove_asm_ne_nil {deadHint : Bool} {nslots : Nat} {saved : List Arm64.Reg}
    {mv : armIsa.Move} {st st' : Rega.SymState vllArmStrictIsa} {c : List (Instr arm64Arch)}
    (h : Rega.execMove vllArmStrictIsa nslots saved mv st deadHint = some (c, st')) :
    asmArm64List c ≠ [] := by
  cases mv with
  | mov d s =>
    dsimp only [Rega.execMove] at h; split at h; · cases h
    split at h <;> (
      cases h; rw [strict_mov_asm]; simp [armMov, armMovIns, emitClean])
  | movi d cv =>
    dsimp only [Rega.execMove, Rega.execMovi] at h; split at h; · cases h
    have hmd1 : vllArmStrictGpr.moviDeadFlags? = none := rfl
    rw [hmd1] at h
    cases h; rw [strict_movi_asm]; exact armMovi_ne_nil d cv
  | ld d i =>
    dsimp only [Rega.execMove] at h; split at h; · cases h
    cases h; rw [strict_slotLd_asm]; exact armSlotLd_ne_nil d i
  | st i s =>
    dsimp only [Rega.execMove] at h; split at h; · cases h
    cases h; rw [strict_slotSt_asm]; exact armSlotSt_ne_nil i s
  | setcc d cf =>
    dsimp only [Rega.execMove] at h; split at h; · cases h
    cases h; rw [strict_setcc_asm]; exact armSetcc_ne_nil d cf
  | vmov _ d _ | vmovi _ d _ | vld _ d _ | vst _ _ d => exact d.elim

theorem execMoves_factor {deadHint : Bool} (nslots : Nat) (saved : List Arm64.Reg) :
    ∀ (mvs : List armIsa.Move) (st : Rega.SymState vllArmStrictIsa),
      (Rega.execMoves vllArmStrictIsa nslots saved mvs st deadHint).map
        (fun (c, st') => (asmArm64List c, liftSt st')) =
        Rega.execMoves armIsa nslots saved mvs (liftSt st) deadHint
  | [], _ => rfl
  | mv :: mvs, st => by
    dsimp only [Rega.execMoves]
    rw [← execMove_factor (deadHint := deadHint) nslots saved mv st]
    cases Rega.execMove vllArmStrictIsa nslots saved mv st deadHint with
    | none => rfl
    | some p =>
      rcases p with ⟨c1, st1⟩
      dsimp only [Option.bind_some, Option.map_some]
      rw [← execMoves_factor (deadHint := deadHint) nslots saved mvs st1]
      cases Rega.execMoves vllArmStrictIsa nslots saved mvs st1 deadHint with
      | none => rfl
      | some p2 =>
        rcases p2 with ⟨c2, st2⟩
        simp [asmArm64List_append]

theorem execMoves_nil_iff {deadHint : Bool} {nslots : Nat} {saved : List Arm64.Reg} :
    ∀ {mvs : List armIsa.Move} {st st' : Rega.SymState vllArmStrictIsa}
      {c : List (Instr arm64Arch)},
      Rega.execMoves vllArmStrictIsa nslots saved mvs st deadHint = some (c, st') →
      (asmArm64List c = [] ↔ c = [])
  | [], _, _, _, h => by cases h; simp [asmArm64List_nil]
  | mv :: mvs, st, st', c, h => by
    dsimp only [Rega.execMoves] at h
    cases h1 : Rega.execMove vllArmStrictIsa nslots saved mv st deadHint with
    | none => simp [h1] at h
    | some p1 =>
      rcases p1 with ⟨c1, st1⟩; rw [h1] at h; dsimp only [Option.bind_some] at h
      cases h2 : Rega.execMoves vllArmStrictIsa nslots saved mvs st1 deadHint with
      | none => simp [h2] at h
      | some p2 =>
        rcases p2 with ⟨c2, st2⟩; rw [h2] at h; cases h
        have hne := execMove_asm_ne_nil h1
        have hc1 : c1 ≠ [] := fun he => hne (he ▸ rfl)
        rw [asmArm64List_append]
        exact ⟨fun he => absurd (List.append_eq_nil_iff.mp he).1 hne,
          fun he => absurd (List.append_eq_nil_iff.mp he).1 hc1⟩

theorem stepPre_factor (h : armIsa.Hints) (ip : Nat) (st : Rega.SymState vllArmStrictIsa) :
    (Rega.stepPre vllArmStrictIsa h ip st).map (fun (c, st') => (asmArm64List c, liftSt st')) =
      Rega.stepPre armIsa h ip (liftSt st) := by
  dsimp only [Rega.stepPre]
  cases h.pre.find? ip with
  | none => rfl
  | some ps =>
    dsimp only
    rw [← execMoves_factor (deadHint := h.deadFlags.getD ip false) h.nslots h.saved ps.moves st]
    cases Rega.execMoves vllArmStrictIsa h.nslots h.saved ps.moves st
        (h.deadFlags.getD ip false) with
    | none => rfl
    | some p =>
      rcases p with ⟨mc, st1⟩
      dsimp only [Option.map_some]
      cases ps.clearFlags with
      | false => rfl
      | true =>
        simp only [↓reduceIte]
        dsimp only [Rega.execClearFlags, liftSt]
        rw [asmArm64List_append, strict_clearFlags_asm, strict_zeroFlags, strict_scratch,
          strict_killRegs]

theorem stepPre_nil_iff {h : armIsa.Hints} {ip : Nat}
    {st st' : Rega.SymState vllArmStrictIsa} {c : List (Instr arm64Arch)}
    (hs : Rega.stepPre vllArmStrictIsa h ip st = some (c, st')) :
    asmArm64List c = [] ↔ c = [] := by
  dsimp only [Rega.stepPre] at hs
  cases hfind : h.pre.find? ip with
  | none => rw [hfind] at hs; cases hs; simp [asmArm64List_nil]
  | some ps =>
    rw [hfind] at hs; dsimp only at hs
    cases hm : Rega.execMoves vllArmStrictIsa h.nslots h.saved ps.moves st
        (h.deadFlags.getD ip false) with
    | none => rw [hm] at hs; cases hs
    | some p =>
      rcases p with ⟨mc, st1⟩; rw [hm] at hs
      cases hcf : ps.clearFlags <;> simp only [hcf, Bool.false_eq_true, ↓reduceIte,
        Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
      · rcases hs with ⟨rfl, rfl⟩; exact execMoves_nil_iff hm
      · rcases hs with ⟨rfl, rfl⟩
        rw [asmArm64List_append]
        have hne : asmArm64List (Rega.execClearFlags vllArmStrictIsa st1).1 ≠ [] := by
          dsimp only [Rega.execClearFlags]; rw [strict_clearFlags_asm]
          simp [armClearFlags, armClearFlagsIns, emitClean]
        have hne' : (Rega.execClearFlags vllArmStrictIsa st1).1 ≠ [] := fun he => hne (he ▸ rfl)
        exact ⟨fun he => absurd (List.append_eq_nil_iff.mp he).2 hne,
          fun he => absurd (List.append_eq_nil_iff.mp he).2 hne'⟩

theorem pmoveAux_factor (nslots : Nat) (saved : List Arm64.Reg) :
    ∀ (fuel : Nat) (st : Rega.SymState vllArmStrictIsa)
      (tgts : List (SymArg × armIsa.Loc)) (acc : List armIsa.Move),
      Rega.pmoveAux vllArmStrictIsa nslots saved fuel st tgts acc =
        Rega.pmoveAux armIsa nslots saved fuel (liftSt st) tgts acc
  | 0, _, _, _ => rfl
  | fuel + 1, st, tgts, acc => by
    dsimp only [Rega.pmoveAux]
    have hfilt :
        (tgts.filter fun (sa, loc) => !Rega.holdsLoc vllArmStrictIsa st sa loc) =
          (tgts.filter fun (sa, loc) => !Rega.holdsLoc armIsa (liftSt st) sa loc) := by
      congr 1; funext ⟨sa, loc⟩; dsimp only; rw [strict_holdsLoc]
    rw [hfilt]
    cases (tgts.filter fun (sa, loc) => !Rega.holdsLoc armIsa (liftSt st) sa loc) with
    | nil => rfl
    | cons hd tl =>
      dsimp only
      have hfind1 :
          ((hd :: tl).find? fun (sa, loc) =>
              Rega.isVarSymArg sa && !(Rega.locBlocked vllArmStrictIsa st (hd :: tl) loc)) =
            ((hd :: tl).find? fun (sa, loc) =>
              Rega.isVarSymArg sa && !(Rega.locBlocked armIsa (liftSt st) (hd :: tl) loc)) := by
        congr 1; funext ⟨sa, loc⟩; dsimp only; rw [strict_locBlocked]
      rw [hfind1]
      split
      · rename_i sa loc h1; rw [h1]; dsimp only
        rw [strict_moveFor]
        cases Rega.moveFor armIsa nslots (liftSt st) sa loc with
        | none => rfl
        | some mv =>
          dsimp only; rw [← execMove_factor nslots saved mv st]
          cases Rega.execMove vllArmStrictIsa nslots saved mv st with
          | none => rfl
          | some p => exact pmoveAux_factor nslots saved fuel p.2 (hd :: tl) (mv :: acc)
      · rename_i h1; rw [h1]; dsimp only
        split
        · rename_i sa1 d h2
          symm; split
          · rename_i sa2 d' h2'
            have heq : (some (sa1, .gpr d) : Option (SymArg × armIsa.Loc)) =
                some (sa2, .gpr d') := by
              rw [← h2, ← h2']
              first | rfl | (congr 1; funext ⟨_, loc⟩; cases loc <;> rfl)
            cases heq; symm
            have hscr :
                (vllArmStrictIsa.frame.scratch.find? fun tmp =>
                    !(Rega.locBlocked vllArmStrictIsa st (hd :: tl) (.gpr tmp))) =
                  (armIsa.frame.scratch.find? fun tmp =>
                    !(Rega.locBlocked armIsa (liftSt st) (hd :: tl) (.gpr tmp))) := by
              rw [strict_scratch]; congr 1; funext tmp; rw [strict_locBlocked]
            rw [hscr]
            split
            · rename_i tmp h3; rw [h3]; dsimp only
              rw [← execMove_factor nslots saved (.mov tmp d) st]
              cases Rega.execMove vllArmStrictIsa nslots saved (.mov tmp d) st with
              | none => rfl
              | some p =>
                exact pmoveAux_factor nslots saved fuel p.2 (hd :: tl) (.mov tmp d :: acc)
            · rename_i h3; rw [h3]; dsimp only; rw [strict_findFreeSlot]
              cases Rega.findFreeSlot armIsa nslots (liftSt st) (hd :: tl) 1 with
              | none => rfl
              | some sl =>
                dsimp only; rw [strict_scratch]
                split
                · rw [← execMove_factor nslots saved (.st sl d) st]
                  cases Rega.execMove vllArmStrictIsa nslots saved (.st sl d) st with
                  | none => rfl
                  | some p =>
                    exact pmoveAux_factor nslots saved fuel p.2 (hd :: tl) (.st sl d :: acc)
                · rfl
          · rename_i h2'
            exact absurd
              (by rw [← h2]; first | rfl | (congr 1; funext ⟨_, loc⟩; cases loc <;> rfl))
              (h2' sa1 d)
        · rename_i h2
          symm; split
          · rename_i sa2 d' h2'
            exact absurd
              (by rw [← h2']; first | rfl | (congr 1; funext ⟨_, loc⟩; cases loc <;> rfl))
              (h2 sa2 d')
          · symm; dsimp only [List.head?_cons]
            split
            · rename_i _ vd _; exact vd.elim
            · symm; split
              · rename_i _ vd _; exact vd.elim
              · symm; rw [strict_moveFor]
                cases Rega.moveFor armIsa nslots (liftSt st) hd.1 hd.2 with
                | none => rfl
                | some mv =>
                  dsimp only; rw [← execMove_factor nslots saved mv st]
                  cases Rega.execMove vllArmStrictIsa nslots saved mv st with
                  | none => rfl
                  | some p => exact pmoveAux_factor nslots saved fuel p.2 (hd :: tl) (mv :: acc)

theorem shuffle_factor (nslots : Nat) (saved : List Arm64.Reg)
    (st : Rega.SymState vllArmStrictIsa) (tgts : List (SymArg × armIsa.Loc)) :
    (Rega.shuffle vllArmStrictIsa nslots saved st tgts).map
      (fun (c, st') => (asmArm64List c, liftSt st')) =
      Rega.shuffle armIsa nslots saved (liftSt st) tgts := by
  dsimp only [Rega.shuffle]
  have hall : (tgts.all fun (sa, loc) => Rega.holdsLoc vllArmStrictIsa st sa loc) =
      (tgts.all fun (sa, loc) => Rega.holdsLoc armIsa (liftSt st) sa loc) := by
    congr 1; funext ⟨sa, loc⟩; dsimp only; rw [strict_holdsLoc]
  rw [hall]
  split
  · rfl
  · rw [← pmoveAux_factor nslots saved (2 * tgts.length + 4) st tgts [],
      ← execMoves_factor nslots saved _ st]
    cases Rega.execMoves vllArmStrictIsa nslots saved _ st with
    | none => rfl
    | some p =>
      rcases p with ⟨c, st'⟩
      dsimp only [Option.map_some]
      have hall' : (tgts.all fun (sa, loc) => Rega.holdsLoc vllArmStrictIsa st' sa loc) =
          (tgts.all fun (sa, loc) => Rega.holdsLoc armIsa (liftSt st') sa loc) := by
        congr 1; funext ⟨sa, loc⟩; dsimp only; rw [strict_holdsLoc]
      rw [hall']; split <;> rfl

theorem shuffle_nil_iff {nslots : Nat} {saved : List Arm64.Reg}
    {st st' : Rega.SymState vllArmStrictIsa} {tgts : List (SymArg × armIsa.Loc)}
    {c : List (Instr arm64Arch)}
    (hs : Rega.shuffle vllArmStrictIsa nslots saved st tgts = some (c, st')) :
    asmArm64List c = [] ↔ c = [] := by
  dsimp only [Rega.shuffle] at hs
  split at hs
  · cases hs; simp [asmArm64List_nil]
  · cases hm : Rega.execMoves vllArmStrictIsa nslots saved _ st with
    | none => rw [hm] at hs; cases hs
    | some p =>
      rcases p with ⟨code, st1⟩; rw [hm] at hs; dsimp only at hs
      split at hs
      · cases hs; exact execMoves_nil_iff hm
      · cases hs

theorem canonAbiCode_factor :
    ∀ {ts : List Ty} (locs : Tup (AbiReg Arm64.Reg Empty) ts) (sk : List Bool),
      asmArm64List (Rega.canonAbiCode vllArmStrictIsa locs sk) =
        Rega.canonAbiCode armIsa locs sk
  | [], (), _ => rfl
  | t :: _, (.gpr r, locs), sk => by
    dsimp only [Rega.canonAbiCode]
    rw [asmArm64List_append, canonAbiCode_factor locs sk.tail]
    congr 1; cases sk.headD false with
    | true => rfl
    | false => exact strict_canonAbi_fst t r
  | _ :: _, (.vec v, _), _ => v.elim

theorem saveCs_factor (base : Nat) (rs : List Arm64.Reg) :
    asmArm64List (Rega.saveCs vllArmStrictIsa base rs) = Rega.saveCs armIsa base rs := by
  cases rs with
  | nil => rfl
  | cons _ _ => exact vllArmSaveRegs_asm base _

theorem restoreCs_factor (base : Nat) (rs : List Arm64.Reg) :
    asmArm64List (Rega.restoreCs vllArmStrictIsa base rs) = Rega.restoreCs armIsa base rs := by
  cases rs with
  | nil => rfl
  | cons _ _ => exact vllArmRestoreRegs_asm base _

end LeanQbe.T.Arm64
