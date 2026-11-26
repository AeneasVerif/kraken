module

public import LeanQbe.T.Arm64.VllFactorArm641
public import LeanQbe.T.Unified.Driver
public import LeanQbe.T.Main
import LeanQbe.T.Arm64.VllFactorArm640
import LeanQbe.T.Arm64.VllFactorArm642
import LeanQbe.T.Unified.DriverLemmas
import LeanQbe.T.RegaLemmas
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.TargetLemmas
import LeanQbe.T.AbiLemmas

/-!
# `BedrockMach` L1 AArch64 Factoring & Byte-Exact Parity (`Arm64.VllFactorArm64`)

Proves full structural `Rega` factoring (`vllArmStrict_lowerFn_factor`,
`vllArmStrict_compileFn_factor`, `vllArmStrict_compile_factor`,
`vllArmStrict_compileModule_factor`), constructs
`arm64Factoring : (Fn → armIsa.Hints) → Unified.Factoring Fn Directive (Instr arm64Arch)`,
`arm64LowerFactoring`, and `arm64FactoringAuto`, and connects `vllArmTarget`/`vllArmStrictTarget`
(`vllLowerFn_correct`) directly to `armTarget.FnSpec` (`vllArmStrict_to_armTarget_fnSpec`,
`vllArmStrict_transport_cert`, `vllArmStrict_same_bytes`).

Zero `Amd64` or `Kraken.X64` imports; zero public `*Lemmas*` imports; zero `@[expose]` on proof
lemmas/theorems.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open LeanQbe.T
open LeanQbe.T.Vll

/-! ### 3.1 Structural `Rega` Instruction/Block/Function Factoring (`vllArmStrictIsa` ↦ `armIsa`) -/

private theorem strict_checkAndBoundExt (exits : List Sym) (nX : Nat)
    (bs : List (SigEntry × Nat)) (h : armIsa.Hints) (ext : Rega.Ext) :
    checkAndBoundExt vllArmStrictIsa 0 exits nX bs h ext =
      checkAndBoundExt armIsa 0 exits nX bs h ext := by
  dsimp only [checkAndBoundExt]; rw [strict_effFrame]

private theorem wrapArmNative_isSome (o : Option (List _root_.Directive × FlagMask)) :
    (wrapArmNative o).isSome = o.isSome := by
  cases o <;> rfl

private theorem listFindSome_none {α β : Type} :
    ∀ (l : List α), l.findSome? (fun _ => (none : Option β)) = none
  | [] => rfl
  | _ :: xs => listFindSome_none xs

private theorem optBind_none {α β : Type} (o : Option α) :
    o.bind (fun _ => (none : Option β)) = none := by
  cases o <;> rfl

private theorem wrapArmNative_map_z {α : Type}
    (f : List _root_.Directive × FlagMask → α) (g : List (Instr arm64Arch) × FlagMask → α)
    (hfg : ∀ c cl, g (c, cl) = f (asmArm64List c, cl))
    (o : Option (List _root_.Directive × FlagMask)) :
    (wrapArmNative o).map g = o.map f := by
  cases o with
  | none => rfl
  | some p =>
    rcases p with ⟨c, cl⟩
    dsimp only [wrapArmNative, Option.map_some]
    rw [hfg, asmArm64List_map_native]

private theorem optBind_map_some {α β γ : Type} (o : Option α) (f : α → β) (k : β → Option γ) :
    (o.map f).bind k = o.bind (fun a => k (f a)) := by
  cases o <;> rfl

private theorem listFindSome_eq_none {α β : Type} (f : α → Option β) (hf : ∀ x, f x = none) :
    ∀ (l : List α), l.findSome? f = none
  | [] => rfl
  | a :: xs => by simp only [List.findSome?, hf, listFindSome_eq_none f hf xs]

private theorem tryFlag_none {I : Isa} {α : Type} (ex : List I.Cond) (sa : SymArg)
    (R : List (SymArg × Rega.RegLoc I.Reg I.VReg I.Cond)) :
    Rega.tryFlag I R ex sa (fun _ => (none : Option α)) = none := by
  dsimp only [Rega.tryFlag]
  rw [listFindSome_eq_none _ (fun _ => by simp only [ite_self]),
    listFindSome_eq_none _ (fun ⟨_, rl⟩ => by cases rl <;> simp only [ite_self])]; rfl

private theorem tryGpr_none {I : Isa} {α : Type} (sa : SymArg)
    (R : List (SymArg × Rega.RegLoc I.Reg I.VReg I.Cond)) :
    Rega.tryGpr I R sa (fun _ => (none : Option α)) = none := by
  dsimp only [Rega.tryGpr]
  exact listFindSome_eq_none _ (fun ⟨_, rl⟩ => by cases rl <;> simp only [ite_self]) _

private theorem tryVec_none {I : Isa} {α : Type} (sa : SymArg)
    (R : List (SymArg × Rega.RegLoc I.Reg I.VReg I.Cond)) :
    Rega.tryVec I R sa (fun _ => (none : Option α)) = none := by
  dsimp only [Rega.tryVec]
  exact listFindSome_eq_none _ (fun ⟨_, rl⟩ => by cases rl <;> simp only [ite_self]) _

private theorem tryArg_none {I : Isa} {α : Type} (st : Rega.SymState I) (ex : List I.Cond)
    (t : Ty) (a : Arg Rega.VNat t) :
    Rega.tryArg I st ex t a (fun _ => (none : Option α)) = none := by
  cases t <;> cases a
  · dsimp only [Rega.tryArg, Function.comp_def]; rw [tryFlag_none, tryGpr_none]; rfl
  · dsimp only [Rega.tryArg, Function.comp_def]; rw [tryFlag_none, tryGpr_none]; rfl
  · exact tryGpr_none _ _
  · dsimp only [Rega.tryArg, Function.comp_def]; rw [tryGpr_none]; simp only [ite_self]; rfl
  · rfl
  · rfl
  · exact tryVec_none _ _
  · dsimp only [Rega.tryArg, Function.comp_def]
    cases Rega.vecWidth? I _ with
    | none => rfl
    | some _ => dsimp only; rw [tryVec_none]; rfl

private theorem tryArg_emptyVec {I : Isa} {α : Type} (hV : I.VReg → False)
    (st : Rega.SymState I) (ex : List I.Cond) (a b : Ty) (v : Arg Rega.VNat (.pair a b))
    (k : PArg I.Reg I.VReg I.Cond (.pair a b) → Option α)
    (hk : ∀ pa, (∀ vs, pa ≠ .vec vs) → k pa = none) :
    Rega.tryArg I st ex (.pair a b) v k = none := by
  have hkn : k = fun _ => none := by
    funext pa
    cases pa with
    | vec vs => exact (hV vs).elim
    | _ => exact hk _ (fun _ h => by cases h)
  rw [hkn, tryArg_none]

private theorem tryTestFuse_factor (st : Rega.SymState vllArmStrictIsa) (neg : Bool) (n t : Nat)
    (pd : PDst Arm64.Reg Empty ArmCond .bool) :
    (Rega.tryTestFuse vllArmStrictIsa st neg n t pd).map (fun p => (asmArm64List p.1, p.2)) =
      Rega.tryTestFuse armIsa (liftSt st) neg n t pd := by
  dsimp only [Rega.tryTestFuse, liftSt]
  have htmv : ∀ x other,
      (Rega.tryTestMemVar vllArmStrictIsa st neg n x other pd).map
        (fun p => (asmArm64List p.1, p.2)) =
        Rega.tryTestMemVar armIsa (liftSt st) neg n x other pd := by
    intro x other; dsimp only [Rega.tryTestMemVar, liftSt]
    cases st.memDefs.find? x with
    | none => rfl
    | some p =>
      rcases p with ⟨ty, addr⟩; cases ty with
      | bool | float _ | pair _ _ => rfl
      | bits m =>
        dsimp only; split
        · rw [tryAddr_map]; congr 1; funext aa
          rw [tryArg_map]; congr 1
        · rfl
  cases st.defs.find? t with
  | none => rfl
  | some df => cases df with
    | andVarImm w x c =>
      dsimp only; split
      · rfl
      · rw [optMap_alt]; refine orElse_congr (htmv ..) ?_
        rw [tryArg_map]; congr 1; funext pa; exact wrapArmNative_asm _
    | andVarVar w x y =>
      dsimp only; split
      · rfl
      · rw [optMap_alt, optMap_alt]
        refine orElse_congr (htmv ..) (orElse_congr (htmv ..) ?_)
        rw [tryArg_map]; congr 1; funext pa
        rw [tryArg_map]; congr 1; funext pb; exact wrapArmNative_asm _
    | _ => rfl

private theorem tryExtCmp_factor (st : Rega.SymState vllArmStrictIsa) (vh : VariantHint)
    (co : CmpOp) (n t : Nat) (c : BitVec n) (pd : PDst Arm64.Reg Empty ArmCond .bool) :
    (Rega.tryExtCmp vllArmStrictIsa st vh co n t c pd).map
      (fun (d, cl, fl, ex) => (asmArm64List d, cl, fl, ex)) =
      Rega.tryExtCmp armIsa (liftSt st) vh co n t c pd := by
  dsimp only [Rega.tryExtCmp]
  cases st.defs.find? t with
  | none => rfl
  | some df => cases df with
    | sextVar m _ x | zextVar m _ x =>
      dsimp only; split
      · rfl
      · rw [optMap_alt]
        refine orElse_congr ?_ ?_
        · dsimp only [liftSt]
          cases st.memDefs.find? x with
          | none => rfl
          | some p =>
            rcases p with ⟨ty, addr⟩; cases ty with
            | bool | float _ | pair _ _ => rfl
            | bits m' =>
              dsimp only; split
              · rw [tryAddr_map]; congr 1
              · rfl
        · change Option.map _ (if true then _ else none) = (if true then _ else none)
          simp only [↓reduceIte]
          rw [tryGpr_map]; congr 1; funext rx
          rw [Option.map_map,
            ← vllArmStrictOp_asm (.cmp co (.bits m)) (.gpr rx, .imm (c.truncate m), ())
              (pd, ()) vh]
          cases vllArmStrictGpr.op (.cmp co (.bits m)) (.gpr rx, .imm (c.truncate m), ())
              (pd, ()) vh with
          | none => rfl
          | some p =>
            rcases p with ⟨d, cl⟩
            have hcf1 : vllArmStrictIsa.gpr.cmpFlagsOut? co m (.gpr rx) (.imm (c.truncate m)) pd =
                none := rfl
            dsimp only [Option.map_some, Function.comp_def]
            rw [hcf1]; dsimp only [Option.bind]; rw [strict_killFlags]
            cases pd with | vec v => exact v.elim | gpr _ | flag _ => rfl
    | _ => rfl

private theorem tryFuseCmp_factor (st : Rega.SymState vllArmStrictIsa) (vh : VariantHint)
    {sig ts : List Ty} (code : OpCode sig ts) (args : Tup (Arg Rega.VNat) sig)
    (dsts : Tup (PDst Arm64.Reg Empty ArmCond) ts) :
    (Rega.tryFuseCmp vllArmStrictIsa st vh code args dsts).map
      (fun (d, cl, fl, ex) => (asmArm64List d, cl, fl, ex)) =
      Rega.tryFuseCmp armIsa (liftSt st) vh code args dsts := by
  cases code with
  | cmp co t m hm =>
    subst hm; cases t with | bool | float _ | pair _ _ => rfl | bits n =>
    rcases args with ⟨a, b, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    dsimp only [Rega.tryFuseCmp]
    split; · rfl
    rw [optMap_alt, optMap_alt]
    have hcmv : ∀ co' x other,
        (Rega.tryCmpMemVar vllArmStrictIsa st co' n x other pd).map
          (fun p => (asmArm64List p.1, p.2)) =
          Rega.tryCmpMemVar armIsa (liftSt st) co' n x other pd := by
      intro co' x other; dsimp only [Rega.tryCmpMemVar, liftSt]
      cases st.memDefs.find? x with
      | none => rfl
      | some p =>
        rcases p with ⟨ty, addr⟩; cases ty with
        | bool | float _ | pair _ _ => rfl
        | bits m =>
          dsimp only; split
          · rw [tryAddr_map]; congr 1; funext aa
            rw [tryArg_map]; congr 1
          · rfl
    refine orElse_congr ?_ (orElse_congr ?_ ?_)
    · split
      · cases a <;> cases b <;> try rfl
        · dsimp only; split
          · rw [Option.map_map, ← tryTestFuse_factor]
            cases Rega.tryTestFuse vllArmStrictIsa st _ n _ pd with
            | none => rfl
            | some p =>
              dsimp only [Option.map_some, Function.comp_def]; rw [strict_killFlags]; rfl
          · rfl
        · dsimp only; split
          · rw [Option.map_map, ← tryTestFuse_factor]
            cases Rega.tryTestFuse vllArmStrictIsa st _ n _ pd with
            | none => rfl
            | some p =>
              dsimp only [Option.map_some, Function.comp_def]; rw [strict_killFlags]; rfl
          · rfl
      · rfl
    · cases a <;> cases b <;> first | rfl | exact tryExtCmp_factor ..
    · rw [optMap_alt]
      refine orElse_congr ?_ ?_
      · cases a with
        | imm _ => rfl
        | var x =>
          dsimp only; rw [Option.map_map, ← hcmv co x b]
          cases Rega.tryCmpMemVar vllArmStrictIsa st co n x b pd with
          | none => rfl
          | some p =>
            dsimp only [Option.map_some, Function.comp_def]
            rw [strict_toSymArg]
            cases Rega.toSymArg armIsa (.bits n) b with
            | none => dsimp only; rw [strict_killFlags]
            | some sb =>
              have hcm1 : vllArmStrictIsa.gpr.cmpMemFlagsOut? co pd = none := rfl
              dsimp only [Rega.cmpMemRes, liftSt]
              rw [hcm1]; dsimp only [Option.bind]; rw [strict_killFlags]
      · cases b with
        | imm _ => rfl
        | var y =>
          dsimp only; rw [Option.map_map, ← hcmv co.swap y a]
          cases Rega.tryCmpMemVar vllArmStrictIsa st co.swap n y a pd with
          | none => rfl
          | some p =>
            dsimp only [Option.map_some, Function.comp_def]
            rw [strict_toSymArg]
            cases Rega.toSymArg armIsa (.bits n) a with
            | none => dsimp only; rw [strict_killFlags]
            | some sa =>
              have hcm1 : vllArmStrictIsa.gpr.cmpMemFlagsOut? co.swap pd = none := rfl
              dsimp only [Rega.cmpMemRes, liftSt]
              rw [hcm1]; dsimp only [Option.bind]; rw [strict_killFlags]
  | _ => rfl

private theorem tryLoadSext_factor (st : Rega.SymState vllArmStrictIsa) (vh : VariantHint)
    {sig ts : List Ty} (code : OpCode sig ts) (args : Tup (Arg Rega.VNat) sig)
    (dsts : Tup (PDst Arm64.Reg Empty ArmCond) ts) :
    (Rega.tryLoadSext vllArmStrictIsa st vh code args dsts).map
      (fun p => (asmArm64List p.1, p.2)) =
      Rega.tryLoadSext armIsa (liftSt st) vh code args dsts := by
  cases code with
  | sext m n =>
    rcases args with ⟨a, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases a with | imm _ => rfl | var x =>
    cases pd with | vec v => exact v.elim | gpr rd =>
    dsimp only [Rega.tryLoadSext, liftSt]
    cases st.memDefs.find? x with
    | none => rfl
    | some p =>
      rcases p with ⟨ty, addr⟩; cases ty with
      | bool | float _ | pair _ _ => rfl
      | bits m' =>
        dsimp only; split
        · rw [optMap_alt]
          refine orElse_congr ?_ ?_
          · rw [tryAddr_map]; congr 1; funext aa; exact vllArmLoadSext_asm m n rd aa
          · rw [tryAddrZext_map]; congr 1; funext rb ri sc d; exact wrapArmNative_asm _
        · rfl
  | _ => rfl

private theorem tryLeaArithZext_ne64 (I : Isa) (st : Rega.SymState I) {sig ts : List Ty}
    {w : Nat} (hts : ts = [.bits w]) (hw : w ≠ 64) (code : OpCode sig ts)
    (args : Tup (Arg Rega.VNat) sig) (dsts : Tup (PDst I.Reg I.VReg I.Cond) ts) :
    Rega.tryLeaArithZext I st code args dsts = none := by
  dsimp only [Rega.tryLeaArithZext]
  split
  · cases hts; exact absurd rfl hw
  · rfl

private theorem tryLeaArith_factor (st : Rega.SymState vllArmStrictIsa)
    {sig ts : List Ty} (code : OpCode sig ts) (args : Tup (Arg Rega.VNat) sig)
    (dsts : Tup (PDst Arm64.Reg Empty ArmCond) ts) :
    (Rega.tryLeaArith vllArmStrictIsa st code args dsts).map
      (fun (c, cl, z) => (asmArm64List c, cl, z)) =
      Rega.tryLeaArith armIsa (liftSt st) code args dsts := by
  cases ts with
  | nil => rfl
  | cons t ts' => cases ts' with
    | cons _ _ => cases t <;> rfl
    | nil => cases t with
      | bool | float _ | pair _ _ => rfl
      | bits w =>
        rcases dsts with ⟨pd, ⟨⟩⟩
        cases pd with | vec v => exact v.elim | gpr rd =>
        dsimp only [Rega.tryLeaArith, liftSt]
        rw [optMap_alt]
        refine orElse_congr ?_ ?_
        · rw [optMap_bind]; congr 1; funext ⟨base?, idx, sc, disp⟩; dsimp only
          cases base? with
          | none =>
            dsimp only [Option.bind_some]
            rw [optMap_bind, strict_findGprFor]; congr 1; funext ri
            dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
            rw [Option.map_map]
            exact wrapArmNative_map_z _ _ (fun _ _ => rfl) _
          | some b =>
            dsimp only
            rw [optBind_map_some, optBind_map_some, optMap_bind, strict_findGprFor]
            congr 1; funext rb
            rw [optMap_bind, strict_findGprFor]; congr 1; funext ri
            dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
            rw [Option.map_map]
            exact wrapArmNative_map_z _ _ (fun _ _ => rfl) _
        · by_cases hw : w = 64
          · subst hw
            change Option.map _ ((Rega.extractLeaZext64 st.defs code args).bind _) =
              (Rega.extractLeaZext64 st.defs code args).bind _
            rw [optMap_bind]; congr 1; funext ⟨base?, idx, sh, disp⟩; dsimp only
            cases base? with
            | none =>
              dsimp only [Option.bind_some]
              rw [optMap_bind, strict_findGprFor]; congr 1; funext ri
              dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
              rw [Option.map_map]
              exact wrapArmNative_map_z _ _ (fun _ _ => rfl) _
            | some b =>
              dsimp only
              rw [optBind_map_some, optBind_map_some, optMap_bind, strict_findGprFor]
              congr 1; funext rb
              rw [optMap_bind, strict_findGprFor]; congr 1; funext ri
              dsimp only [vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks, armGpr]
              rw [Option.map_map]
              exact wrapArmNative_map_z _ _ (fun _ _ => rfl) _
          · rw [tryLeaArithZext_ne64 vllArmStrictIsa st rfl hw,
              tryLeaArithZext_ne64 armIsa (liftSt st) rfl hw]; rfl

private theorem trySlotOp_none_of_noMem {I : Isa}
    (htest : ∀ neg n a pa pd, I.gpr.testMem neg n a pa pd = none)
    (hcmp : ∀ co n a pa pd, I.gpr.cmpMem co n a pa pd = none)
    (halu : ∀ n (c : OpCode [.bits n, .bits n] [.bits n]) sw a pa rd,
      I.gpr.aluMem n c sw a pa rd = none)
    (h : I.Hints) (st : Rega.SymState I) {sig ts : List Ty}
    (code : OpCode sig ts) (args : Tup (Arg Rega.VNat) sig)
    (dsts : Tup (PDst I.Reg I.VReg I.Cond) ts) :
    Rega.trySlotOp I h st code args dsts = none := by
  have hts : ∀ neg n t pd, Rega.tryTestSlot I h st neg n t pd = none := by
    intro neg n t pd; dsimp only [Rega.tryTestSlot]; split; · rfl
    cases st.defs.find? t with
    | none => rfl
    | some df => cases df with
      | andVarImm _ _ _ =>
        dsimp only; split
        · simp only [htest, optBind_none]
        · rfl
      | andVarVar _ _ _ =>
        dsimp only; split
        · simp only [htest, tryArg_none, optBind_none]; rfl
        · rfl
      | _ => rfl
  have hes : ∀ co n t c pd, Rega.tryExtSlot I h st co n t c pd = none := by
    intro co n t c pd; dsimp only [Rega.tryExtSlot]
    cases st.defs.find? t with
    | none => rfl
    | some df => cases df with
      | sextVar _ _ _ | zextVar _ _ _ =>
        dsimp only; split
        · simp only [hcmp, optBind_none]
        · rfl
      | _ => rfl
  have hal : ∀ n (c : OpCode [.bits n, .bits n] [.bits n]) a b rd,
      Rega.tryAluSlot I h st n c a b rd = none := by
    intro n c a b rd; dsimp only [Rega.tryAluSlot]; split; · rfl
    cases a <;> cases b <;> simp only [halu, tryArg_none, optBind_none] <;> rfl
  cases code with
  | cmp co t m hm =>
    subst hm; cases t with | bool | float _ | pair _ _ => rfl | bits n =>
    rcases args with ⟨a, b, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    dsimp only [Rega.trySlotOp]; split; · rfl
    cases a <;> cases b <;>
      simp only [hts, hes, hcmp, Option.map_none, tryArg_none, optBind_none, ite_self] <;>
      cases (!Rega.isStdBitWidth n) <;> rfl
  | add t | sub t | mul t | and t | or t | xor t =>
    cases t with | bool | float _ | pair _ _ => rfl | bits n =>
    rcases args with ⟨a, b, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd with | gpr rd => dsimp only [Rega.trySlotOp]; rw [hal]; rfl | vec _ => rfl
  | _ => rfl

private theorem trySlotOp_factor (h : armIsa.Hints) (st : Rega.SymState vllArmStrictIsa)
    {sig ts : List Ty} (code : OpCode sig ts) (args : Tup (Arg Rega.VNat) sig)
    (dsts : Tup (PDst Arm64.Reg Empty ArmCond) ts) :
    (Rega.trySlotOp vllArmStrictIsa h st code args dsts).map
      (fun (c, cl, z, fl, ex) => (asmArm64List c, cl, z, fl, ex)) =
      Rega.trySlotOp armIsa h (liftSt st) code args dsts := by
  rw [trySlotOp_none_of_noMem (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
        (fun _ _ _ _ _ _ => rfl),
      trySlotOp_none_of_noMem (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
        (fun _ _ _ _ _ _ => rfl)]; rfl

private theorem strict_tupDstFlags :
    ∀ {ts : List Ty} (dsts : Tup (PDst Arm64.Reg Empty ArmCond) ts),
      Rega.tupDstFlags (I := vllArmStrictIsa) dsts = Rega.tupDstFlags (I := armIsa) dsts
  | [], () => rfl
  | _ :: _, (pd, ds) => by
    cases pd with
    | vec v => exact v.elim
    | gpr _ | flag _ => dsimp only [Rega.tupDstFlags]; rw [strict_tupDstFlags ds]

private theorem lowerOp_pick_factor (h : armIsa.Hints) (nv ip : Nat)
    (st1 : Rega.SymState vllArmStrictIsa) {ts : List Ty} (opN : Op Rega.VNat ts)
    (dsts : Tup (PDst Arm64.Reg Empty ArmCond) ts) :
    (Rega.pickPArgs vllArmStrictIsa st1 (Rega.tupDstFlags dsts) opN.args fun pas =>
      if (tupDstVecs dsts).isEmpty && (tupArgVecs pas).isEmpty then
        ((vllArmStrictIsa.gpr.op opN.code pas dsts (h.variant.getD ip .default)).map
          fun (c, cl) =>
            let (fl, ex) :=
              Rega.cmpOpFlags? vllArmStrictIsa st1 opN.code opN.args pas dsts nv cl
            (c, cl, false, Rega.opProducesZ32 vllArmStrictIsa opN.code pas dsts, fl, ex)) <|>
        ((vllArmStrictIsa.vec.vop opN.code pas dsts (h.variant.getD ip .default)).map
          fun (c, cl) =>
            (c, cl, true, false, Rega.killFlags vllArmStrictIsa cl st1.flags, none))
      else (vllArmStrictIsa.vec.vop opN.code pas dsts (h.variant.getD ip .default)).map
        fun (c, cl) =>
          (c, cl, true, false, Rega.killFlags vllArmStrictIsa cl st1.flags, none)).map
      (fun (c, cl, iv, z, fl, ex) => (asmArm64List c, cl, iv, z, fl, ex)) =
    Rega.pickPArgs armIsa (liftSt st1) (Rega.tupDstFlags dsts) opN.args fun pas =>
      if (tupDstVecs dsts).isEmpty && (tupArgVecs pas).isEmpty then
        ((armIsa.gpr.op opN.code pas dsts (h.variant.getD ip .default)).map
          fun (c, cl) =>
            let (fl, ex) :=
              Rega.cmpOpFlags? armIsa (liftSt st1) opN.code opN.args pas dsts nv cl
            (c, cl, false, Rega.opProducesZ32 armIsa opN.code pas dsts, fl, ex)) <|>
        ((armIsa.vec.vop opN.code pas dsts (h.variant.getD ip .default)).map
          fun (c, cl) =>
            (c, cl, true, false, Rega.killFlags armIsa cl (liftSt st1).flags, none))
      else (armIsa.vec.vop opN.code pas dsts (h.variant.getD ip .default)).map
        fun (c, cl) =>
          (c, cl, true, false, Rega.killFlags armIsa cl (liftSt st1).flags, none) := by
  rw [pickPArgs_map, strict_tupDstFlags]
  apply congrArg (Rega.pickPArgs armIsa (liftSt st1) (Rega.tupDstFlags (I := armIsa) dsts) opN.args)
  funext pas
  split
  · rw [optMap_alt]
    refine orElse_congr ?_ rfl
    have hop : (vllArmStrictIsa.gpr.op opN.code pas dsts (h.variant.getD ip .default)).map
        (fun p => (asmArm64List p.1, p.2)) =
      armIsa.gpr.op opN.code pas dsts (h.variant.getD ip .default) :=
      vllArmStrictOp_asm opN.code pas dsts (h.variant.getD ip .default)
    rw [Option.map_map, ← hop]
    cases vllArmStrictIsa.gpr.op opN.code pas dsts (h.variant.getD ip .default) with
    | none => rfl
    | some p =>
      rcases p with ⟨c, cl⟩
      dsimp only [Option.map_some, Function.comp_def]
      rw [strict_cmpOpFlags?, strict_opProducesZ32]
  · rfl

private abbrev VllArmCode := List (Instr arm64Arch)
private abbrev ArmDirCode := List _root_.Directive

private theorem lowerOp_try6_factor (h : armIsa.Hints) (nv ip : Nat)
    (st1 : Rega.SymState vllArmStrictIsa) {ts : List Ty} (op opN : Op Rega.VNat ts)
    (dsts : Tup (PDst Arm64.Reg Empty ArmCond) ts) :
    ((((Rega.tryReuseFlagCmp vllArmStrictIsa st1 op.code op.args dsts <|>
        Rega.tryReuseFlagCmp vllArmStrictIsa st1 opN.code opN.args dsts).map
      fun ((c, cl, fl, ex) : VllArmCode × FlagMask × Option Rega.FlagFact × Option ArmCond) =>
        (c, cl, false, false, fl, ex)) <|>
     ((Rega.tryFuseCmp vllArmStrictIsa st1 (h.variant.getD ip .default)
        opN.code opN.args dsts).map
      fun ((c, cl, fl, ex) : VllArmCode × FlagMask × Option Rega.FlagFact × Option ArmCond) =>
        (c, cl, false, false, fl, ex)) <|>
     ((Rega.tryLoadSext vllArmStrictIsa st1 (h.variant.getD ip .default)
        opN.code opN.args dsts).map
      fun ((c, cl) : VllArmCode × FlagMask) =>
        (c, cl, false, false, Rega.killFlags vllArmStrictIsa cl st1.flags, none)) <|>
     ((Rega.tryLeaArith vllArmStrictIsa st1 opN.code opN.args dsts).map
      fun ((c, cl, z32) : VllArmCode × FlagMask × Bool) =>
        (c, cl, false, z32, Rega.killFlags vllArmStrictIsa cl st1.flags, none)) <|>
     (Rega.pickPArgs vllArmStrictIsa st1 (Rega.tupDstFlags dsts) opN.args fun pas =>
      if (tupDstVecs dsts).isEmpty && (tupArgVecs pas).isEmpty then
        ((vllArmStrictIsa.gpr.op opN.code pas dsts (h.variant.getD ip .default)).map
          fun ((c, cl) : VllArmCode × FlagMask) =>
            let (fl, ex) :=
              Rega.cmpOpFlags? vllArmStrictIsa st1 opN.code opN.args pas dsts nv cl
            (c, cl, false, Rega.opProducesZ32 vllArmStrictIsa opN.code pas dsts, fl, ex)) <|>
        ((vllArmStrictIsa.vec.vop opN.code pas dsts (h.variant.getD ip .default)).map
          fun ((c, cl) : VllArmCode × FlagMask) =>
            (c, cl, true, false, Rega.killFlags vllArmStrictIsa cl st1.flags, none))
      else (vllArmStrictIsa.vec.vop opN.code pas dsts (h.variant.getD ip .default)).map
        fun ((c, cl) : VllArmCode × FlagMask) =>
          (c, cl, true, false, Rega.killFlags vllArmStrictIsa cl st1.flags, none)) <|>
     ((Rega.trySlotOp vllArmStrictIsa h st1 opN.code opN.args dsts).map
      fun ((c, cl, z32, fl, ex) :
          VllArmCode × FlagMask × Bool × Option Rega.FlagFact × Option ArmCond) =>
        (c, cl, false, z32, fl, ex))).map
      (fun ((c, cl, iv, z, fl, ex) :
          VllArmCode × FlagMask × Bool × Bool × Option Rega.FlagFact × Option ArmCond) =>
        (asmArm64List c, cl, iv, z, fl, ex))) =
    (((Rega.tryReuseFlagCmp armIsa (liftSt st1) op.code op.args dsts <|>
        Rega.tryReuseFlagCmp armIsa (liftSt st1) opN.code opN.args dsts).map
      fun ((c, cl, fl, ex) : ArmDirCode × FlagMask × Option Rega.FlagFact × Option ArmCond) =>
        (c, cl, false, false, fl, ex)) <|>
     ((Rega.tryFuseCmp armIsa (liftSt st1) (h.variant.getD ip .default)
        opN.code opN.args dsts).map
      fun ((c, cl, fl, ex) : ArmDirCode × FlagMask × Option Rega.FlagFact × Option ArmCond) =>
        (c, cl, false, false, fl, ex)) <|>
     ((Rega.tryLoadSext armIsa (liftSt st1) (h.variant.getD ip .default)
        opN.code opN.args dsts).map
      fun ((c, cl) : ArmDirCode × FlagMask) =>
        (c, cl, false, false, Rega.killFlags armIsa cl (liftSt st1).flags, none)) <|>
     ((Rega.tryLeaArith armIsa (liftSt st1) opN.code opN.args dsts).map
      fun ((c, cl, z32) : ArmDirCode × FlagMask × Bool) =>
        (c, cl, false, z32, Rega.killFlags armIsa cl (liftSt st1).flags, none)) <|>
     (Rega.pickPArgs armIsa (liftSt st1) (Rega.tupDstFlags dsts) opN.args fun pas =>
      if (tupDstVecs dsts).isEmpty && (tupArgVecs pas).isEmpty then
        ((armIsa.gpr.op opN.code pas dsts (h.variant.getD ip .default)).map
          fun ((c, cl) : ArmDirCode × FlagMask) =>
            let (fl, ex) :=
              Rega.cmpOpFlags? armIsa (liftSt st1) opN.code opN.args pas dsts nv cl
            (c, cl, false, Rega.opProducesZ32 armIsa opN.code pas dsts, fl, ex)) <|>
        ((armIsa.vec.vop opN.code pas dsts (h.variant.getD ip .default)).map
          fun ((c, cl) : ArmDirCode × FlagMask) =>
            (c, cl, true, false, Rega.killFlags armIsa cl (liftSt st1).flags, none))
      else (armIsa.vec.vop opN.code pas dsts (h.variant.getD ip .default)).map
        fun ((c, cl) : ArmDirCode × FlagMask) =>
          (c, cl, true, false, Rega.killFlags armIsa cl (liftSt st1).flags, none)) <|>
     ((Rega.trySlotOp armIsa h (liftSt st1) opN.code opN.args dsts).map
      fun ((c, cl, z32, fl, ex) :
          ArmDirCode × FlagMask × Bool × Option Rega.FlagFact × Option ArmCond) =>
        (c, cl, false, z32, fl, ex))) := by
  rw [optMap_alt]; refine orElse_congr ?_ ?_
  · rw [(strict_tryReuseFlagCmp_none st1 op.code op.args dsts).1,
      (strict_tryReuseFlagCmp_none st1 opN.code opN.args dsts).1,
      (strict_tryReuseFlagCmp_none st1 op.code op.args dsts).2,
      (strict_tryReuseFlagCmp_none st1 opN.code opN.args dsts).2]; rfl
  · rw [optMap_alt]; refine orElse_congr ?_ ?_
    · rw [Option.map_map, ← tryFuseCmp_factor st1 (h.variant.getD ip .default)
        opN.code opN.args dsts]
      cases Rega.tryFuseCmp vllArmStrictIsa st1 (h.variant.getD ip .default)
        opN.code opN.args dsts <;> rfl
    · rw [optMap_alt]; refine orElse_congr ?_ ?_
      · rw [Option.map_map, ← tryLoadSext_factor st1 (h.variant.getD ip .default)
          opN.code opN.args dsts]
        cases Rega.tryLoadSext vllArmStrictIsa st1 (h.variant.getD ip .default)
          opN.code opN.args dsts with
        | none => rfl
        | some p => dsimp only [Option.map_some, Function.comp_def]; rw [strict_killFlags]
      · rw [optMap_alt]; refine orElse_congr ?_ ?_
        · rw [Option.map_map, ← tryLeaArith_factor st1 opN.code opN.args dsts]
          cases Rega.tryLeaArith vllArmStrictIsa st1 opN.code opN.args dsts with
          | none => rfl
          | some p => dsimp only [Option.map_some, Function.comp_def]; rw [strict_killFlags]
        · rw [optMap_alt]; refine orElse_congr (lowerOp_pick_factor h nv ip st1 opN dsts) ?_
          rw [Option.map_map, ← trySlotOp_factor h st1 opN.code opN.args dsts]
          cases Rega.trySlotOp vllArmStrictIsa h st1 opN.code opN.args dsts <;> rfl

private theorem lowerOp_factor (h : armIsa.Hints) (nv ip : Nat)
    (st1 : Rega.SymState vllArmStrictIsa) {ts : List Ty} (op : Op Rega.VNat ts)
    (df : Bool := false) :
    (Rega.lowerOp vllArmStrictIsa h nv ip st1 op df).map
      (fun (c, st') => (asmArm64List c, liftSt st')) =
      Rega.lowerOp armIsa h nv ip (liftSt st1) op df := by
  dsimp only [Rega.lowerOp]
  cases df
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split
    · cases Rega.recordDef st1.defs op.code op.args <;> rfl
    · rw [optMap_bind, strict_resolveDsts]; congr 1; funext dsts
      rw [strict_elideZext32?, strict_elideTrunc?]
      split
      · rename_i hel; clear hel
        cases ts <;> first | rfl | (rename_i _ ts'; cases ts' <;> first | rfl |
          (rcases dsts with ⟨pd, ⟨⟩⟩; cases pd <;> rfl))
      · split
        · rename_i h1 h2; clear h1 h2
          cases ts <;> first | rfl | (rename_i _ ts'; cases ts' <;> first | rfl |
            (rcases dsts with ⟨pd, ⟨⟩⟩; cases pd <;> rfl))
        · rename_i hne1 hne2; clear hne1 hne2
          let opN := Rega.normCmpOp (I := vllArmStrictIsa) op dsts
          have hnorm : opN = Rega.normCmpOp (I := armIsa) op dsts := strict_normCmpOp op dsts
          have h6 := lowerOp_try6_factor h nv ip st1 op opN dsts
          change (Option.map _ _).map _ = _
          rw [← hnorm, ← h6]
          cases ((((Rega.tryReuseFlagCmp vllArmStrictIsa st1 op.code op.args dsts <|>
              Rega.tryReuseFlagCmp vllArmStrictIsa st1 opN.code opN.args dsts).map _) <|> _)) with
          | none => rfl
          | some r =>
            rcases r with ⟨code, clob, isVec, z32, fl, ex⟩
            dsimp only [Option.map_some, liftSt]
            have hvs : (vllEmptyVecIsa arm64Arch Empty.elim).vecScratch =
                (VecIsa.empty Arm64.Reg ArmCond _root_.Directive).vecScratch := rfl
            rw [strict_scratch, strict_killRegs, hvs]
            cases z32
            · cases isVec <;>
                (simp only [Bool.false_eq_true, ↓reduceIte, strict_bindDsts]
                 congr 1; congr 1; congr 1; split <;> rfl)
            · cases isVec <;>
                (simp only [Bool.false_eq_true, ↓reduceIte, strict_bindDsts]
                 congr 1; congr 1; congr 1
                 · split <;> split <;> rfl
                 · split <;> rfl
                 · split <;> rfl)
  · simp only [↓reduceIte, optMap_alt]
    cases Rega.recordBoolDef st1.defs op.code op.args <;>
      cases Rega.recordDef st1.defs op.code op.args <;> rfl

private theorem lowerLoad_factor (h : armIsa.Hints) (nv ip : Nat)
    (st1 : Rega.SymState vllArmStrictIsa) (t : Ty) (a : Arg Rega.VNat i64) (fuse : Bool := false) :
    (Rega.lowerLoad vllArmStrictIsa h nv ip st1 t a fuse).map
      (fun (c, st') => (asmArm64List c, liftSt st')) =
      Rega.lowerLoad armIsa h nv ip (liftSt st1) t a fuse := by
  dsimp only [Rega.lowerLoad]
  split
  · rw [strict_isGprTy]; split <;> rfl
  · cases h.dest.find? nv with
    | none => rfl
    | some loc => cases loc with
      | flag _ | slot _ _ => rfl
      | vec vd => exact vd.elim
      | gpr d =>
        dsimp only; rw [strict_isAllocGpr, strict_isGprTy]
        split; · rfl
        have hld : (Rega.tryAddr vllArmStrictIsa st1 (h.variant.getD ip .default) a
              (vllArmStrictIsa.gpr.load t d) <|>
            Rega.tryAddrZext vllArmStrictIsa st1 a (vllArmStrictIsa.gpr.loadZextIdx t d)).map
              (fun p => (asmArm64List p.1, p.2)) =
            (Rega.tryAddr armIsa (liftSt st1) (h.variant.getD ip .default) a
              (armIsa.gpr.load t d) <|>
            Rega.tryAddrZext armIsa (liftSt st1) a (armIsa.gpr.loadZextIdx t d)) := by
          rw [optMap_alt]
          refine orElse_congr ?_ ?_
          · rw [tryAddr_map]; congr 1; funext aa; exact vllArmStrictLoad_asm t d aa
          · rw [tryAddrZext_map]; congr 1; funext rb ri sc disp; exact wrapArmNative_asm _
        rw [Option.map_map, ← hld]
        cases (Rega.tryAddr vllArmStrictIsa st1 _ a _ <|>
          Rega.tryAddrZext vllArmStrictIsa st1 a _) with
        | none => rfl
        | some p =>
          rcases p with ⟨c, clob⟩
          dsimp only [Option.map_some, Function.comp_def, liftSt]
          rw [strict_zeroUpper32Load, strict_zeroExtLoad, strict_scratch, strict_killRegs,
            strict_killFlags]

private theorem lowerStore_factor (st1 : Rega.SymState vllArmStrictIsa) (vh : VariantHint)
    (t : Ty) (v : Arg Rega.VNat t) (addr : Arg Rega.VNat i64) :
    (Rega.lowerStore vllArmStrictIsa st1 vh t v addr).map
      (fun (c, st') => (asmArm64List c, liftSt st')) =
      Rega.lowerStore armIsa (liftSt st1) vh t v addr := by
  have hrmw : (Rega.tryRmwStore vllArmStrictIsa st1 vh t v addr).map
      (fun p => (asmArm64List p.1, p.2)) = Rega.tryRmwStore armIsa (liftSt st1) vh t v addr := by
    have hhalf : ∀ n op x other,
        (Rega.tryRmwHalf vllArmStrictIsa st1 vh n op x other addr).map
          (fun p => (asmArm64List p.1, p.2)) =
          Rega.tryRmwHalf armIsa (liftSt st1) vh n op x other addr := by
      intro n op x other; dsimp only [Rega.tryRmwHalf, liftSt]
      cases st1.memDefs.find? x with
      | none => rfl
      | some p =>
        rcases p with ⟨ty, loadAddr⟩; cases ty with
        | bool | float _ | pair _ _ => rfl
        | bits m =>
          dsimp only; split
          · rw [tryAddr_map]; congr 1; funext aa1
            rw [tryAddr_map]; congr 1; funext aa2
            split
            · rw [tryArg_map]; congr 1
            · rfl
          · rfl
    cases t with
    | bits n => cases v with
      | imm _ => rfl
      | var y =>
        dsimp only [Rega.tryRmwStore, liftSt]; split; · rfl
        cases st1.defs.find? y with
        | none => rfl
        | some df =>
          dsimp only; rw [optMap_bind]; congr 1; funext ⟨op, x, rhs⟩
          rw [optMap_alt]
          refine orElse_congr (hhalf ..) ?_
          split
          · cases rhs with | var z => exact hhalf n op z (.var x) | imm _ => rfl
          · rfl
    | _ => rfl
  cases t with
  | pair a b =>
    dsimp only [Rega.lowerStore]
    rw [tryArg_emptyVec (I := vllArmStrictIsa) Empty.elim st1 [] a b v _
        (fun pa hp => by cases pa with | vec vs => exact absurd rfl (hp vs) | _ => rfl),
      tryArg_emptyVec (I := armIsa) Empty.elim (liftSt st1) [] a b v _
        (fun pa hp => by cases pa with | vec vs => exact absurd rfl (hp vs) | _ => rfl)]; rfl
  | bool | bits _ | float _ =>
    dsimp only [Rega.lowerStore]
    rw [strict_isGprTy]; split; · rfl
    have hst : ((Rega.tryArg vllArmStrictIsa st1 [] _ v fun pa =>
          Rega.tryAddr vllArmStrictIsa st1 vh addr (vllArmStrictIsa.gpr.store _ pa) <|>
          Rega.tryAddrZext vllArmStrictIsa st1 addr (vllArmStrictIsa.gpr.storeZextIdx _ pa)) <|>
        Rega.tryRmwStore vllArmStrictIsa st1 vh _ v addr).map
          (fun p => (asmArm64List p.1, p.2)) =
        ((Rega.tryArg armIsa (liftSt st1) [] _ v fun pa =>
          Rega.tryAddr armIsa (liftSt st1) vh addr (armIsa.gpr.store _ pa) <|>
          Rega.tryAddrZext armIsa (liftSt st1) addr (armIsa.gpr.storeZextIdx _ pa)) <|>
        Rega.tryRmwStore armIsa (liftSt st1) vh _ v addr) := by
      rw [optMap_alt]
      refine orElse_congr ?_ hrmw
      rw [tryArg_map]; congr 1; funext pa
      rw [optMap_alt]
      refine orElse_congr ?_ ?_
      · rw [tryAddr_map]; first | rfl | (congr 1; funext aa; exact vllArmStrictStore_asm _ pa aa)
      · rw [tryAddrZext_map]
        first | rfl | (congr 1; funext rb ri sc disp; exact wrapArmNative_asm _)
    rw [Option.map_map, ← hst]
    cases ((Rega.tryArg vllArmStrictIsa st1 [] _ v _) <|>
      Rega.tryRmwStore vllArmStrictIsa st1 vh _ v addr) with
    | none => rfl
    | some p =>
      rcases p with ⟨c, clob⟩
      dsimp only [Option.map_some, Function.comp_def, liftSt]
      rw [strict_scratch, strict_killRegs, strict_killFlags]

private theorem findJnzCond_factor (nslots : Nat) (st : Rega.SymState vllArmStrictIsa) (x : Nat) :
    (Rega.findJnzCond vllArmStrictIsa nslots st x).map liftJnz =
      Rega.findJnzCond armIsa nslots (liftSt st) x := by
  dsimp only [Rega.findJnzCond, liftSt]
  rw [optMap_alt, optMap_alt, optMap_alt, optMap_alt]
  refine orElse_congr ?_ (orElse_congr ?_ (orElse_congr ?_ (orElse_congr ?_ ?_)))
  · rw [Option.map_map, strict_findFlagFor]; rfl
  · cases st.defs.find? x with
    | some df => cases df with
      | cmpZeroVar co w y =>
        dsimp only; rw [Option.map_map, strict_cmpZeroFlagCond?]; rfl
      | _ => rfl
    | none => rfl
  · rw [Option.map_map, strict_findGprFor]; rfl
  · cases st.defs.find? x with
    | none => rfl
    | some df => cases df with
      | cmpZeroVar co w y =>
        dsimp only; rw [optMap_alt]
        refine orElse_congr ?_ ?_
        · cases st.memDefs.find? y with
          | none => rfl
          | some p =>
            rcases p with ⟨ty, addr⟩; cases ty with
            | bool | float _ | pair _ _ => rfl
            | bits m => dsimp only; split <;> rfl
        · rw [optMap_bind, strict_findGprFor]; congr 1; funext r
          have hcz : (vllArmStrictIsa.gpr.cmpZeroJcc co w r (Rega.lname "" 0)).isSome =
              (armIsa.gpr.cmpZeroJcc co w r (Rega.lname "" 0)).isSome := by
            dsimp only [vllArmStrictIsa, vllArmStrictGpr, vllGprIsaOfHooks, vllArmNativeHooks,
              armIsa, armGpr]
            rw [← wrapArmNative_asm (armCmpZeroJcc co w r (Rega.lname "" 0))]
            cases wrapArmNative (armCmpZeroJcc co w r (Rega.lname "" 0)) <;> rfl
          rw [hcz]; split
          · rfl
          · split <;> rfl
      | testBitVar neg w y c =>
        dsimp only; rw [Option.map_map, strict_findGprFor]; rfl
      | _ => rfl
  · rw [Option.map_map]; rfl

private theorem fuseJnzChoice_factor {rs : List Ty} (h : armIsa.Hints) (fn : Sym)
    (nl ipT ipE : Nat) (st1 : Rega.SymState vllArmStrictIsa) (t e : Expr Rega.VNat Rega.LNat rs)
    (ft : Option Nat) (fwd : Trie Nat)
    (emitV : Bool → Sym → Option (List (Instr arm64Arch) × FlagMask))
    (emitA : Bool → Sym → Option (List _root_.Directive × FlagMask))
    (hemit : ∀ inv l, (emitV inv l).map (fun p => (asmArm64List p.1, p.2)) = emitA inv l) :
    (Rega.fuseJnzChoice vllArmStrictIsa h fn nl ipT ipE st1 t e ft emitV fwd).map
      (fun (inv, tgt?, br, st') => (inv, tgt?, asmArm64List br, liftSt st')) =
      Rega.fuseJnzChoice armIsa h fn nl ipT ipE (liftSt st1) t e ft emitA fwd := by
  have hthr : ∀ ipA inv (arm : Expr Rega.VNat Rega.LNat rs),
      (Rega.threadFusedArm vllArmStrictIsa h fn ipA st1 (emitV inv) arm fwd).map
        (fun (j, br, st') => (j, asmArm64List br, liftSt st')) =
        Rega.threadFusedArm armIsa h fn ipA (liftSt st1) (emitA inv) arm fwd := by
    intro ipA inv arm
    cases arm with
    | jump j args =>
      dsimp only [Rega.threadFusedArm]
      rw [← hemit inv (Rega.lname fn (Rega.tgtLab fwd j))]
      cases emitV inv (Rega.lname fn (Rega.tgtLab fwd j)) with
      | none => rfl
      | some p =>
        rcases p with ⟨br, cl⟩
        dsimp only [Option.map_some, Option.bind_some]
        rw [strict_zeroMoveJump?]
        dsimp only [liftSt]
        rw [strict_scratch, strict_killRegs, strict_killFlags]
        split <;> rfl
    | _ => rfl
  dsimp only [Rega.fuseJnzChoice]
  rw [← hemit (h.invertJnz.getD (ipE - 1) false) (Rega.lname fn nl)]
  cases emitV (h.invertJnz.getD (ipE - 1) false) (Rega.lname fn nl) with
  | none => rfl
  | some p =>
    rcases p with ⟨brNl, clNl⟩
    dsimp only [Option.map_some]
    rw [← hthr ipT false t, ← hthr ipE true e]
    cases Rega.threadFusedArm vllArmStrictIsa h fn ipT st1 (emitV false) t fwd with
    | none =>
      cases Rega.threadFusedArm vllArmStrictIsa h fn ipE st1 (emitV true) e fwd with
      | none =>
        dsimp only [Option.map_none, liftSt]
        rw [strict_scratch, strict_killRegs, strict_killFlags]
      | some _ => rfl
    | some _ =>
      cases Rega.threadFusedArm vllArmStrictIsa h fn ipE st1 (emitV true) e fwd with
      | none => rfl
      | some _ => dsimp only [Option.map_some]; split <;> rfl

private theorem jnzSetup_factor {rs : List Ty} (h : armIsa.Hints) (fn : Sym) (nl ipT ipE : Nat)
    (st1 : Rega.SymState vllArmStrictIsa) (t e : Expr Rega.VNat Rega.LNat rs) (ft : Option Nat)
    (cond : Rega.JnzCond vllArmStrictIsa) (fwd : Trie Nat) :
    (Rega.jnzSetup vllArmStrictIsa h fn nl ipT ipE st1 t e ft cond fwd).map
      (fun (inv, tgt?, br, st') => (inv, tgt?, asmArm64List br, liftSt st')) =
      Rega.jnzSetup armIsa h fn nl ipT ipE (liftSt st1) t e ft (liftJnz cond) fwd := by
  cases cond with
  | flag cnd =>
    dsimp only [Rega.jnzSetup, liftJnz, Option.map_some]
    rw [strict_jnzMode, strict_jcc_asm, strict_negCond]
    dsimp only [liftSt]; rw [strict_scratch, strict_killRegs, strict_killFlags]
  | gpr r =>
    change Option.map _ (some _) = some _
    dsimp only [Option.map_some, liftSt]
    rw [strict_gprThread?, strict_jnzGpr_fst, strict_jnzGpr_snd,
      strict_scratch, strict_killRegs, strict_killFlags]
  | slot _ => rfl
  | cmpZero co w r =>
    dsimp only [Rega.jnzSetup, liftJnz]
    exact fuseJnzChoice_factor h fn nl ipT ipE st1 t e ft fwd _ _
      (fun inv l => wrapArmNative_asm _)
  | cmpZeroMem _ _ _ _ _ => rfl
  | cmpZeroFlag co w x r cnd =>
    dsimp only [Rega.jnzSetup, liftJnz]
    rw [Option.map_map,
      ← vllArmStrictOp_asm (.cmp co (.bits w)) (.gpr r, .imm 0#w, ()) (.flag cnd, ()) .default]
    cases vllArmStrictGpr.op (.cmp co (.bits w)) (.gpr r, .imm 0#w, ())
        (.flag cnd, ()) .default with
    | none => rfl
    | some p =>
      rcases p with ⟨cmpCode, cl⟩
      dsimp only [Option.map_some, Function.comp_def, Rega.finishCmpJnz]
      rw [asmArm64List_append, strict_jnzMode, strict_jcc_asm, strict_negCond]
      dsimp only [liftSt]
      rw [strict_scratch, strict_killRegs, strict_killFlags, strict_killRegs, strict_killFlags]
      cases Nat.ble w 64 <;> rfl
  | testImm neg w r mask =>
    dsimp only [Rega.jnzSetup, liftJnz]
    exact fuseJnzChoice_factor h fn nl ipT ipE st1 t e ft fwd _ _
      (fun inv l => wrapArmNative_asm _)

private theorem fusesLoad_factor {ts : List Ty} (h : armIsa.Hints)
    (st : Rega.SymState vllArmStrictIsa) (nv' ip' : Nat) (op : Op Rega.VNat ts) :
    Rega.fusesLoad vllArmStrictIsa h st nv' ip' op =
      Rega.fusesLoad armIsa h (liftSt st) nv' ip' op := by
  dsimp only [Rega.fusesLoad]
  rw [strict_resolveDsts]
  congr 1; cases Rega.resolveDsts armIsa h ts nv' with
  | none => rfl
  | some dsts =>
    dsimp only
    rw [← tryFuseCmp_factor st (h.variant.getD ip' .default) op.code op.args dsts,
      ← tryLoadSext_factor st (h.variant.getD ip' .default) op.code op.args dsts]
    cases Rega.tryFuseCmp vllArmStrictIsa st _ op.code op.args dsts <;>
      cases Rega.tryLoadSext vllArmStrictIsa st _ op.code op.args dsts <;> rfl

private theorem strict_jumpAvoids {rs : List Ty} (h : armIsa.Hints) (x : Nat)
    (e : Expr Rega.VNat Rega.LNat rs) :
    Rega.jumpAvoids (I := vllArmStrictIsa) h x e = Rega.jumpAvoids (I := armIsa) h x e := by
  cases e with
  | jump j args => dsimp only [Rega.jumpAvoids]; cases h.entry.find? j <;> rfl
  | _ => rfl

private theorem loadSextNext_factor {rs : List Ty} (h : armIsa.Hints) (nv ip : Nat)
    (st : Rega.SymState vllArmStrictIsa) (t : Ty) (a : Arg Rega.VNat i64)
    (e : Expr Rega.VNat Rega.LNat rs) :
    Rega.loadSextNext vllArmStrictIsa h nv ip st t a e =
      Rega.loadSextNext armIsa h nv ip (liftSt st) t a e := by
  let st' : Rega.SymState vllArmStrictIsa := { st with memDefs := st.memDefs.insert nv (t, a) }
  have hsext : ∀ ip' nv' (e' : Expr Rega.VNat Rega.LNat rs),
      (match e' with
       | .let_ op _ =>
         match Rega.sextVar? op.code op.args with
         | some (_, _, x) =>
           Nat.beq x nv && h.dest.find? nv' == h.dest.find? nv &&
             Rega.fusesLoad vllArmStrictIsa h st' nv' ip' op
         | none => false
       | _ => false) =
      (match e' with
       | .let_ op _ =>
         match Rega.sextVar? op.code op.args with
         | some (_, _, x) =>
           Nat.beq x nv && h.dest.find? nv' == h.dest.find? nv &&
             Rega.fusesLoad armIsa h (liftSt st') nv' ip' op
         | none => false
       | _ => false) := by
    intro ip' nv' e'; cases e' with
    | let_ op _ =>
      dsimp only
      cases Rega.sextVar? op.code op.args with
      | none => rfl
      | some p => dsimp only; rw [← fusesLoad_factor h st' nv' ip' op]
    | _ => rfl
  dsimp only [Rega.loadSextNext]
  change (Rega.isGprTy vllArmStrictIsa t && _) = (Rega.isGprTy armIsa t && _)
  rw [strict_isGprTy]
  congr 1; congr 1
  · exact hsext (ip + 1) (nv + 1) e
  · cases e with
    | let_ op k =>
      dsimp only
      rw [← fusesLoad_factor h st' (nv + 1) (ip + 1) op]
      cases h.dest.find? (nv + 1) with
      | none =>
        cases k (Tup.levels _ (nv + 1)) with
        | jnz c tt ee => cases c with
          | imm _ => rfl
          | var cx =>
            dsimp only
            rw [strict_jumpAvoids, strict_jumpAvoids]
            congr 1; congr 1; congr 1
            · congr 1; exact hsext (ip + 3) (nv + 2) ee
            · congr 1; exact hsext (ip + 4) (nv + 2) tt
        | _ => rfl
      | some loc =>
        cases loc with
        | vec v => exact v.elim
        | gpr _ | flag _ | slot _ _ =>
          cases k (Tup.levels _ (nv + 1)) with
          | jnz c tt ee => cases c with
            | imm _ => rfl
            | var cx =>
              dsimp only
              rw [strict_jumpAvoids, strict_jumpAvoids]
              congr 1; congr 1; congr 1
              · congr 1; exact hsext (ip + 3) (nv + 2) ee
              · congr 1; exact hsext (ip + 4) (nv + 2) tt
          | _ => rfl
    | _ => rfl

private theorem deferJnzNext_factor {rs : List Ty} (h : armIsa.Hints) (fn : Sym) (nv nl ip : Nat)
    (st1 : Rega.SymState vllArmStrictIsa) {ts : List Ty} (op : Op Rega.VNat ts)
    (k' : Expr Rega.VNat Rega.LNat rs) :
    Rega.deferJnzNext vllArmStrictIsa h fn nv nl ip st1 op k' =
      Rega.deferJnzNext armIsa h fn nv nl ip (liftSt st1) op k' := by
  cases ts with
  | nil => rfl
  | cons t ts' => cases ts' with
    | cons _ _ => cases t <;> rfl
    | nil => cases t with
      | bool => cases k' with
        | jnz c _ _ => cases c with
          | imm _ => rfl
          | var cx =>
            dsimp only [Rega.deferJnzNext]
            congr 1
            rw [← lowerOp_factor h nv ip st1 op true]
            cases Rega.lowerOp vllArmStrictIsa h nv ip st1 op true with
            | none => rfl
            | some p2 =>
              dsimp only [Option.map_some]
              rw [← stepPre_factor h (ip + 1) p2.2]
              cases Rega.stepPre vllArmStrictIsa h (ip + 1) p2.2 with
              | none => rfl
              | some p3 =>
                dsimp only [Option.map_some]
                rw [← findJnzCond_factor h.nslots p3.2 nv]
                cases Rega.findJnzCond vllArmStrictIsa h.nslots p3.2 nv with
                | none => rfl
                | some jc => cases jc with
                  | cmpZero co w r =>
                    exact wrapArmNative_isSome (armCmpZeroJcc co w r (Rega.lname fn nl))
                  | testImm neg w r mask =>
                    exact wrapArmNative_isSome (armTestJcc neg w r mask (Rega.lname fn nl))
                  | _ => rfl
        | _ => rfl
      | _ => rfl

private theorem deferLeaNext_factor {rs : List Ty} (h : armIsa.Hints) (nv ip : Nat)
    (st1 : Rega.SymState vllArmStrictIsa) {ts : List Ty} (op : Op Rega.VNat ts)
    (k' : Expr Rega.VNat Rega.LNat rs) :
    Rega.deferLeaNext vllArmStrictIsa h nv ip st1 op k' =
      Rega.deferLeaNext armIsa h nv ip (liftSt st1) op k' := by
  dsimp only [Rega.deferLeaNext]
  split; · rfl
  cases ts with
  | nil => rfl
  | cons t ts' => cases ts' with
    | cons _ _ => rfl
    | nil => cases k' with
      | let_ op2 _ =>
        dsimp only
        cases Rega.recordDef st1.defs op.code op.args with
        | none => rfl
        | some df =>
          dsimp only
          rw [← stepPre_factor h (ip + 1) { st1 with defs := st1.defs.insert nv df }]
          cases Rega.stepPre vllArmStrictIsa h (ip + 1)
              { st1 with defs := st1.defs.insert nv df } with
          | none => rfl
          | some p =>
            dsimp only [Option.map_some]
            rw [strict_resolveDsts]
            cases Rega.resolveDsts armIsa h _ (nv + 1) with
            | none => rfl
            | some dsts2 =>
              dsimp only
              rw [← tryLeaArith_factor p.2 op2.code op2.args dsts2]
              cases Rega.tryLeaArith vllArmStrictIsa p.2 op2.code op2.args dsts2 <;> rfl
      | _ => rfl

private theorem buildEntryBase_factor (nslots : Nat) (vw : Trie SlotWidth) :
    ∀ (live : List (SymArg × armIsa.Loc)) (st : Rega.SymState vllArmStrictIsa),
      (Rega.buildEntryBase vllArmStrictIsa nslots vw live st).map liftSt =
        Rega.buildEntryBase armIsa nslots vw live (liftSt st)
  | [], _ => rfl
  | (sa, .gpr r) :: rest, st => by
    dsimp only [Rega.buildEntryBase]; rw [strict_scratch]
    split
    · exact buildEntryBase_factor nslots vw rest _
    · rfl
  | (_, .vec v) :: _, _ => v.elim
  | (_, .flag _) :: rest, st => buildEntryBase_factor nslots vw rest _
  | (sa, .slot i w) :: rest, st => by
    dsimp only [Rega.buildEntryBase]
    split
    · rfl
    · rw [optMap_bind]; congr 1; funext sl'
      exact buildEntryBase_factor nslots vw rest _

private theorem bindBlockParams_factor (nslots : Nat) :
    ∀ (ts : List Ty) (locs : List armIsa.Loc) (nv : Nat) (st : Rega.SymState vllArmStrictIsa),
      (Rega.bindBlockParams vllArmStrictIsa nslots ts locs nv st).map liftSt =
        Rega.bindBlockParams armIsa nslots ts locs nv (liftSt st)
  | [], [], _, _ => rfl
  | t :: ts, loc :: locs, nv, st => by
    dsimp only [Rega.bindBlockParams]
    cases loc with
    | gpr r =>
      dsimp only; rw [strict_scratch, strict_isGprTy]
      split
      · exact bindBlockParams_factor nslots ts locs (nv + 1) _
      · rfl
    | vec v => exact v.elim
    | flag c => cases t <;> first | exact bindBlockParams_factor nslots ts locs (nv + 1) _ | rfl
    | slot i w =>
      dsimp only; rw [strict_isGprTy, strict_vecWidth?]
      split
      · rfl
      · rw [optMap_bind]; congr 1; funext sl'
        exact bindBlockParams_factor nslots ts locs (nv + 1) _
  | [], _ :: _, _, _ | _ :: _, [], _, _ => rfl

private theorem bindAbiParams_factor :
    ∀ {ts : List Ty} (locs : Tup (AbiReg Arm64.Reg Empty) ts) (nv : Nat)
      (st : Rega.SymState vllArmStrictIsa),
      (Rega.bindAbiParams vllArmStrictIsa locs nv st).map liftSt =
        Rega.bindAbiParams armIsa locs nv (liftSt st)
  | [], (), _, _ => rfl
  | t :: _, (.gpr r, locs), nv, st => by
    dsimp only [Rega.bindAbiParams]; rw [strict_isGprTy]
    split
    · exact bindAbiParams_factor locs (nv + 1) _
    · rfl
  | _ :: _, (.vec v, _), _, _ => v.elim

private theorem blockTrampoline?_factor {rs : List Ty} (h : armIsa.Hints)
    (defs : Trie Rega.DefFact) (vw : Trie SlotWidth) (lid nv ip : Nat)
    {ts : List Ty} (b : Tup Rega.VNat ts → Expr Rega.VNat Rega.LNat rs) :
    Rega.blockTrampoline? vllArmStrictIsa h defs vw lid nv ip b =
      Rega.blockTrampoline? armIsa h defs vw lid nv ip b := by
  dsimp only [Rega.blockTrampoline?]
  cases h.entry.find? lid with
  | none => rfl
  | some en =>
    dsimp only
    have hsc : Rega.entryScopeOk (I := vllArmStrictIsa) nv en =
        Rega.entryScopeOk (I := armIsa) nv en := rfl
    rw [hsc]; split; · rfl
    rw [← buildEntryBase_factor h.nslots vw en.live
      { regs := [], slots := .empty, defs := defs, vecWidths := vw }]
    cases Rega.buildEntryBase vllArmStrictIsa h.nslots vw en.live _ with
    | none => rfl
    | some baseSt =>
      dsimp only [Option.map_some]
      rw [← bindBlockParams_factor h.nslots ts en.ploc nv baseSt]
      cases Rega.bindBlockParams vllArmStrictIsa h.nslots ts en.ploc nv baseSt with
      | none => rfl
      | some initSt =>
        dsimp only [Option.map_some]
        cases b (Tup.levels ts nv) with
        | jump j' args' =>
          dsimp only
          cases hpre : Rega.stepPre vllArmStrictIsa h ip initSt with
          | none =>
            have hp' := stepPre_factor h ip initSt; rw [hpre] at hp'; rw [← hp']; rfl
          | some p1 =>
            rcases p1 with ⟨mc, st1⟩
            have hp' := stepPre_factor h ip initSt; rw [hpre] at hp'; rw [← hp']
            have hnil := stepPre_nil_iff hpre
            cases hmc : mc with
            | cons a as =>
              rw [hmc] at hnil
              have hne : asmArm64List (a :: as) ≠ [] := fun e => by
                have := hnil.mp e; cases this
              dsimp only [Option.map_some]
              cases hma : asmArm64List (a :: as) with
              | nil => exact absurd hma hne
              | cons _ _ => rfl
            | nil =>
              simp only [asmArm64List_nil, Option.map_some]
              cases h.entry.find? j' with
              | none => rfl
              | some en' =>
                dsimp only; rw [strict_jumpTargets]
                cases Rega.jumpTargets armIsa args' en'.ploc with
                | none => rfl
                | some argTgts =>
                  dsimp only
                  have hok : ((en'.live ++ argTgts).all fun (_, loc) =>
                      Rega.jumpLocOk vllArmStrictIsa h.nslots loc) =
                    ((en'.live ++ argTgts).all fun (_, loc) =>
                      Rega.jumpLocOk armIsa h.nslots loc) := by
                    congr 1; funext ⟨_, loc⟩; exact strict_jumpLocOk h.nslots loc
                  rw [hok]; split; · rfl
                  cases hsh : Rega.shuffle vllArmStrictIsa h.nslots h.saved st1
                      (en'.live ++ argTgts) with
                  | none =>
                    have hs' := shuffle_factor h.nslots h.saved st1 (en'.live ++ argTgts)
                    rw [hsh] at hs'; rw [← hs']; rfl
                  | some p2 =>
                    rcases p2 with ⟨sc, st2⟩
                    have hs' := shuffle_factor h.nslots h.saved st1 (en'.live ++ argTgts)
                    rw [hsh] at hs'; rw [← hs']
                    have hsnil := shuffle_nil_iff hsh
                    cases hsc2 : sc with
                    | nil => simp [asmArm64List_nil, Option.map_some]
                    | cons a as =>
                      rw [hsc2] at hsnil
                      have hne : asmArm64List (a :: as) ≠ [] := fun e => by
                        have := hsnil.mp e; cases this
                      dsimp only [Option.map_some]
                      cases hsa : asmArm64List (a :: as) with
                      | nil => exact absurd hsa hne
                      | cons _ _ => rfl
        | _ => rfl

private theorem collectRawFwds_factor {rs : List Ty} (h : armIsa.Hints)
    (defs : Trie Rega.DefFact) (vw : Trie SlotWidth) (fwd : Trie Nat) (fwdTgts : Trie Bool) :
    ∀ {sig : List (List Ty)} (bs : Blocks Rega.VNat Rega.LNat rs sig)
      (lid nv nl ip : Nat) (raw : Trie Nat) (lids : List Nat),
      Rega.collectRawFwds vllArmStrictIsa h defs vw fwd fwdTgts bs lid nv nl ip raw lids =
        Rega.collectRawFwds armIsa h defs vw fwd fwdTgts bs lid nv nl ip raw lids
  | _, .nil, _, _, _, _, _, _ => rfl
  | _, .cons b bs, lid, nv, nl, ip, raw, lids => by
    dsimp only [Rega.collectRawFwds]
    rw [blockTrampoline?_factor h defs vw lid nv ip b]
    exact collectRawFwds_factor h defs vw fwd fwdTgts bs (lid + 1) _ _ _ _ _

private theorem findGroupFwds_factor {rs : List Ty} (h : armIsa.Hints)
    (st : Rega.SymState vllArmStrictIsa) {sig : List (List Ty)}
    (bodies : Blocks Rega.VNat Rega.LNat rs sig) (k : Expr Rega.VNat Rega.LNat rs)
    (nv nl ip : Nat) (fwd : Trie Nat) (fwdTgts : Trie Bool) :
    Rega.findGroupFwds vllArmStrictIsa h st bodies k nv nl ip fwd fwdTgts =
      Rega.findGroupFwds armIsa h (liftSt st) bodies k nv nl ip fwd fwdTgts := by
  dsimp only [Rega.findGroupFwds, liftSt]
  rw [collectRawFwds_factor]

private def liftRes (r : Rega.Res vllArmStrictIsa) : Rega.Res armIsa :=
  r.map fun (c, nv, nl, ip) => (asmArm64List c, nv, nl, ip)

private theorem liftRes_prepend (pre : List (Instr arm64Arch)) (r : Rega.Res vllArmStrictIsa) :
    liftRes (Rega.prepend pre r) = Rega.prepend (asmArm64List pre) (liftRes r) := by
  cases r with
  | error _ => rfl
  | ok p =>
    rcases p with ⟨c, nv, nl, ip⟩
    simp only [liftRes, Rega.prepend, Except.map, asmArm64List_append]

private theorem lowerTail_factor {ts : List Ty} (h : armIsa.Hints) (E : Rega.Ext)
    (st1 : Rega.SymState vllArmStrictIsa) (mc tail : List (Instr arm64Arch))
    (args : Tup (Arg Rega.VNat) ts) (locs : Tup (AbiReg Arm64.Reg Empty) ts) (nv nl ip : Nat) :
    liftRes (Rega.lowerTail vllArmStrictIsa h E st1 mc tail args locs nv nl ip) =
      Rega.lowerTail armIsa h E (liftSt st1) (asmArm64List mc) (asmArm64List tail)
        args locs nv nl ip := by
  dsimp only [Rega.lowerTail]
  rw [strict_abiTargets]
  cases Rega.abiTargets armIsa args locs with
  | none => rfl
  | some tgts =>
    dsimp only
    rw [← shuffle_factor h.nslots h.saved st1 tgts]
    cases Rega.shuffle vllArmStrictIsa h.nslots h.saved st1 tgts with
    | none => rfl
    | some p =>
      rcases p with ⟨sc, st'⟩
      dsimp only [liftRes, Except.map, Option.map_some, liftSt]
      congr 1; congr 1
      simp only [asmArm64List_append, canonAbiCode_factor, strict_abiSkips, restoreCs_factor]
      congr 1; congr 1
      dsimp only [Rega.fnEpilogue]
      rw [strict_isZeroLeaf]
      cases Rega.isZeroLeaf armIsa h E with
      | true => rfl
      | false => exact strict_epilogue_fst h.totalSlots

private theorem lowerExpr_jump_nil_iff {rs ts : List Ty} {h : armIsa.Hints} {E : Rega.Ext}
    {fn : Sym} {j : Nat} {args : Tup (Arg Rega.VNat) ts} {nv nl ip : Nat}
    {st : Rega.SymState vllArmStrictIsa} {ft : Option Nat} {fwd : Trie Nat × Trie Bool}
    {c : List (Instr arm64Arch)} {nv' nl' ip' : Nat}
    (hl : Rega.lowerExpr vllArmStrictIsa h E fn (.jump j args : Expr Rega.VNat Rega.LNat rs)
      nv nl ip st ft fwd.1 fwd.2 = .ok (c, nv', nl', ip')) :
    (asmArm64List c).isEmpty = c.isEmpty := by
  dsimp only [Rega.lowerExpr] at hl
  cases hpre : Rega.stepPre vllArmStrictIsa h ip st with
  | none => rw [hpre] at hl; cases hl
  | some p1 =>
    rcases p1 with ⟨mc, st1⟩; rw [hpre] at hl; dsimp only at hl
    cases hen : h.entry.find? j with
    | none => rw [hen] at hl; cases hl
    | some en =>
      rw [hen] at hl; dsimp only at hl
      cases hjt : Rega.jumpTargets vllArmStrictIsa args en.ploc with
      | none => rw [hjt] at hl; cases hl
      | some argTgts =>
        rw [hjt] at hl; dsimp only at hl
        split at hl; · cases hl
        cases hsh : Rega.shuffle vllArmStrictIsa h.nslots h.saved st1 (en.live ++ argTgts) with
        | none => rw [hsh] at hl; cases hl
        | some p2 =>
          rcases p2 with ⟨sc, _⟩; rw [hsh] at hl; cases hl
          have h1 := stepPre_nil_iff hpre
          have h2 := shuffle_nil_iff hsh
          have hj : asmArm64List
              (vllArmStrictIsa.gpr.jmp (Rega.lname fn (Rega.tgtLab fwd.1 j))) ≠ [] := by
            rw [strict_jmp_asm]; simp [armJmp, armJmpIns, emitClean]
          have hj' : vllArmStrictIsa.gpr.jmp (Rega.lname fn (Rega.tgtLab fwd.1 j)) ≠ [] :=
            fun he => hj (he ▸ rfl)
          let body := mc ++ sc ++
            if ft == some (Rega.tgtLab fwd.1 j) then []
            else vllArmStrictIsa.gpr.jmp (Rega.lname fn (Rega.tgtLab fwd.1 j))
          have hiff : asmArm64List body = [] ↔ body = [] := by
            dsimp only [body]
            rw [asmArm64List_append, asmArm64List_append, List.append_eq_nil_iff,
              List.append_eq_nil_iff, List.append_eq_nil_iff, List.append_eq_nil_iff, h1, h2]
            cases (ft == some (Rega.tgtLab fwd.1 j)) <;> simp [asmArm64List_nil, hj, hj']
          change (asmArm64List body).isEmpty = body.isEmpty
          cases ha : asmArm64List body with
          | nil =>
            have hb := hiff.mp ha
            rw [hb]; rfl
          | cons _ _ =>
            cases hb : body with
            | nil => exact absurd (hiff.mpr hb) (by rw [ha]; simp)
            | cons _ _ => rfl

mutual
private theorem lowerExpr_factor {rs : List Ty} (h : armIsa.Hints) (E : Rega.Ext) (fn : Sym) :
    ∀ (e : Expr Rega.VNat Rega.LNat rs) (nv nl ip : Nat) (st : Rega.SymState vllArmStrictIsa)
      (ft : Option Nat) (fwd : Trie Nat) (fwdTgts : Trie Bool),
      liftRes (Rega.lowerExpr vllArmStrictIsa h E fn e nv nl ip st ft fwd fwdTgts) =
        Rega.lowerExpr armIsa h E fn e nv nl ip (liftSt st) ft fwd fwdTgts
  | .let_ op k, nv, nl, ip, st, ft, fwd, fwdTgts => by
    unfold Rega.lowerExpr; dsimp only
    rw [← stepPre_factor h ip st]
    cases Rega.stepPre vllArmStrictIsa h ip st with
    | none => rfl
    | some p1 =>
      rcases p1 with ⟨mc, st1⟩
      dsimp only [Option.map_some]
      rw [← deferJnzNext_factor h fn nv nl ip st1 op _, ← deferLeaNext_factor h nv ip st1 op _,
        ← lowerOp_factor h nv ip st1 op _]
      cases Rega.lowerOp vllArmStrictIsa h nv ip st1 op _ with
      | none => rfl
      | some p2 =>
        rcases p2 with ⟨c, st2⟩
        dsimp only [Option.map_some]
        rw [liftRes_prepend, asmArm64List_append,
          lowerExpr_factor h E fn _ _ _ _ st2 ft fwd fwdTgts]
  | .load t a k, nv, nl, ip, st, ft, fwd, fwdTgts => by
    dsimp only [Rega.lowerExpr]
    rw [← stepPre_factor h ip st]
    cases Rega.stepPre vllArmStrictIsa h ip st with
    | none => rfl
    | some p1 =>
      rcases p1 with ⟨mc, st1⟩
      dsimp only [Option.map_some]
      rw [← loadSextNext_factor h nv ip st1 t a (k nv), ← lowerLoad_factor h nv ip st1 t a _]
      cases Rega.lowerLoad vllArmStrictIsa h nv ip st1 t a _ with
      | none => rfl
      | some p2 =>
        rcases p2 with ⟨c, st2⟩
        dsimp only [Option.map_some]
        rw [liftRes_prepend, asmArm64List_append,
          lowerExpr_factor h E fn _ _ _ _ st2 ft fwd fwdTgts]
  | .store v a k, nv, nl, ip, st, ft, fwd, fwdTgts => by
    dsimp only [Rega.lowerExpr]
    rw [← stepPre_factor h ip st]
    cases Rega.stepPre vllArmStrictIsa h ip st with
    | none => rfl
    | some p1 =>
      rcases p1 with ⟨mc, st1⟩
      dsimp only [Option.map_some]
      rw [← lowerStore_factor st1 (h.variant.getD ip .default) _ v a]
      cases Rega.lowerStore vllArmStrictIsa st1 (h.variant.getD ip .default) _ v a with
      | none => rfl
      | some p2 =>
        rcases p2 with ⟨c, st2⟩
        dsimp only [Option.map_some]
        rw [liftRes_prepend, asmArm64List_append,
          lowerExpr_factor h E fn k nv nl (ip + 1) st2 ft fwd fwdTgts]
  | .call f args k, nv, nl, ip, st, ft, fwd, fwdTgts => by
    dsimp only [Rega.lowerExpr]
    rw [← stepPre_factor h ip st]
    cases Rega.stepPre vllArmStrictIsa h ip st with
    | none => rfl
    | some p1 =>
      rcases p1 with ⟨mc, st1⟩
      dsimp only [Option.map_some]
      split; · rfl
      rw [strict_assignArgs, strict_assignRets]
      cases armIsa.assignArgs _ with
      | none => rfl
      | some argLocs => cases armIsa.assignRets _ with
        | none => rfl
        | some retLocs =>
          dsimp only; rw [strict_abiTargets]
          cases Rega.abiTargets armIsa args argLocs with
          | none => rfl
          | some tgts =>
            dsimp only
            rw [← shuffle_factor h.nslots h.saved st1 tgts]
            cases Rega.shuffle vllArmStrictIsa h.nslots h.saved st1 tgts with
            | none => rfl
            | some p2 =>
              rcases p2 with ⟨sc, st2⟩
              dsimp only [Option.map_some]
              have hac : liftSt (Rega.afterCallState vllArmStrictIsa h.saved st2) =
                  Rega.afterCallState armIsa h.saved (liftSt st2) := by
                dsimp only [Rega.afterCallState, liftSt]
                congr 1; congr 1; funext ⟨_, rl⟩; dsimp only; cases rl <;> rfl
              rw [← hac, ← bindAbiParams_factor retLocs nv
                (Rega.afterCallState vllArmStrictIsa h.saved st2)]
              cases Rega.bindAbiParams vllArmStrictIsa retLocs nv _ with
              | none => rfl
              | some st4 =>
                dsimp only [Option.map_some]
                rw [liftRes_prepend, lowerExpr_factor h E fn _ _ _ _ st4 ft fwd fwdTgts]
                congr 1
                rw [asmArm64List_append, asmArm64List_append, asmArm64List_append,
                  canonAbiCode_factor, strict_abiSkips]
                exact congrArg (fun x => _ ++ x) (strict_call_asm f)
  | .jnz (.imm b) t e, nv, nl, ip, st, ft, fwd, fwdTgts => by
    dsimp only [Rega.lowerExpr]
    rw [← stepPre_factor h ip st]
    cases Rega.stepPre vllArmStrictIsa h ip st with
    | none => rfl
    | some p1 =>
      rcases p1 with ⟨mc, st1⟩
      dsimp only [Option.map_some]
      rw [liftRes_prepend]
      cases b with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [lowerExpr_factor h E fn e nv nl (ip + 1) st1 ft fwd fwdTgts]
      | true =>
        simp only [↓reduceIte]
        rw [lowerExpr_factor h E fn t nv nl (ip + 1) st1 ft fwd fwdTgts]
  | .jnz (.var cx) t e, nv, nl, ip, st, ft, fwd, fwdTgts => by
    dsimp only [Rega.lowerExpr]
    rw [← stepPre_factor h ip st]
    cases Rega.stepPre vllArmStrictIsa h ip st with
    | none => rfl
    | some p1 =>
      rcases p1 with ⟨mc, st1⟩
      dsimp only [Option.map_some]
      rw [← findJnzCond_factor h.nslots st1 cx]
      cases Rega.findJnzCond vllArmStrictIsa h.nslots st1 cx with
      | none => rfl
      | some cond =>
        dsimp only [Option.map_some]
        rw [← jnzSetup_factor h fn nl (Rega.jnzIpT nv nl ip t e) (ip + 1) st1 t e ft cond fwd]
        cases Rega.jnzSetup vllArmStrictIsa h fn nl (Rega.jnzIpT nv nl ip t e) (ip + 1) st1
            t e ft cond fwd with
        | none => rfl
        | some p2 =>
          rcases p2 with ⟨inv, tgt?, br, stBr⟩
          dsimp only [Option.map_some]
          cases inv <;> cases tgt? <;> simp only [Bool.false_eq_true, ↓reduceIte]
          · have hle := lowerExpr_factor h E fn e nv (nl + 1) (ip + 1) stBr none fwd fwdTgts
            rw [← hle]
            cases he : Rega.lowerExpr vllArmStrictIsa h E fn e nv (nl + 1) (ip + 1) stBr
                none fwd fwdTgts with
            | error err => rfl
            | ok pe =>
              rcases pe with ⟨ce, nv1, nl1, ip1⟩
              dsimp only [liftRes, Except.map]
              have hlt := lowerExpr_factor h E fn t nv1 nl1 ip1 stBr ft fwd fwdTgts
              rw [← hlt]
              cases ht : Rega.lowerExpr vllArmStrictIsa h E fn t nv1 nl1 ip1 stBr
                  ft fwd fwdTgts with
              | error err => rfl
              | ok pt =>
                rcases pt with ⟨ct, nv2, nl2, ip2⟩
                dsimp only [liftRes, Except.map, Rega.finishJnzBranch, Rega.prepend]
                simp only [asmArm64List_append, asmArm64List_one, asmArm64,
                  vllFrameIsaOfHooks, vllFrameIsa, armIsa, armFrame]
          · rename_i j
            have hle := lowerExpr_factor h E fn e nv (nl + 1) (ip + 1) stBr ft fwd fwdTgts
            rw [← hle]
            cases he : Rega.lowerExpr vllArmStrictIsa h E fn e nv (nl + 1) (ip + 1) stBr
                ft fwd fwdTgts with
            | error err => rfl
            | ok pe =>
              rcases pe with ⟨ce, nv1, nl1, ip1⟩
              dsimp only [liftRes, Except.map]
              have hlt := lowerExpr_factor h E fn t nv1 nl1 ip1 stBr
                (some (Rega.tgtLab fwd j)) fwd fwdTgts
              rw [← hlt]
              cases ht : Rega.lowerExpr vllArmStrictIsa h E fn t nv1 nl1 ip1 stBr
                  (some (Rega.tgtLab fwd j)) fwd fwdTgts with
              | error err => rfl
              | ok pt =>
                rcases pt with ⟨ct, nv2, nl2, ip2⟩
                change liftRes (Rega.prepend mc _) = _
                rw [liftRes_prepend]; congr 1
                dsimp only [Rega.finishJnzBranch]
                cases t with
                | jump j' args' =>
                  have hemp := lowerExpr_jump_nil_iff (fwd := (fwd, fwdTgts)) ht
                  dsimp only; rw [hemp]
                  split <;> simp [liftRes, Except.map, asmArm64List_append]
                | _ => rfl
          · have hle := lowerExpr_factor h E fn e nv (nl + 1) (ip + 1) stBr ft fwd fwdTgts
            rw [← hle]
            cases he : Rega.lowerExpr vllArmStrictIsa h E fn e nv (nl + 1) (ip + 1) stBr
                ft fwd fwdTgts with
            | error err => rfl
            | ok pe =>
              rcases pe with ⟨ce, nv1, nl1, ip1⟩
              dsimp only [liftRes, Except.map]
              have hlt := lowerExpr_factor h E fn t nv1 nl1 ip1 stBr none fwd fwdTgts
              rw [← hlt]
              cases ht : Rega.lowerExpr vllArmStrictIsa h E fn t nv1 nl1 ip1 stBr
                  none fwd fwdTgts with
              | error err => rfl
              | ok pt =>
                rcases pt with ⟨ct, nv2, nl2, ip2⟩
                dsimp only [liftRes, Except.map, Rega.finishJnzBranch, Rega.prepend]
                simp only [asmArm64List_append, asmArm64List_one, asmArm64,
                  vllFrameIsaOfHooks, vllFrameIsa, armIsa, armFrame]
          · rename_i j
            have hle := lowerExpr_factor h E fn e nv (nl + 1) (ip + 1) stBr
              (some (Rega.tgtLab fwd j)) fwd fwdTgts
            rw [← hle]
            cases he : Rega.lowerExpr vllArmStrictIsa h E fn e nv (nl + 1) (ip + 1) stBr
                (some (Rega.tgtLab fwd j)) fwd fwdTgts with
            | error err => rfl
            | ok pe =>
              rcases pe with ⟨ce, nv1, nl1, ip1⟩
              dsimp only [liftRes, Except.map]
              have hlt := lowerExpr_factor h E fn t nv1 nl1 ip1 stBr ft fwd fwdTgts
              rw [← hlt]
              cases ht : Rega.lowerExpr vllArmStrictIsa h E fn t nv1 nl1 ip1 stBr
                  ft fwd fwdTgts with
              | error err => rfl
              | ok pt =>
                rcases pt with ⟨ct, nv2, nl2, ip2⟩
                change liftRes (Rega.prepend mc _) = _
                rw [liftRes_prepend]; congr 1
                dsimp only [Rega.finishJnzBranch]
                cases e with
                | jump j' args' =>
                  have hemp := lowerExpr_jump_nil_iff (fwd := (fwd, fwdTgts)) he
                  dsimp only; rw [hemp]
                  split <;> simp [liftRes, Except.map, asmArm64List_append]
                | _ => rfl
  | .jump j args, nv, nl, ip, st, ft, fwd, fwdTgts => by
    dsimp only [Rega.lowerExpr]
    rw [← stepPre_factor h ip st]
    cases Rega.stepPre vllArmStrictIsa h ip st with
    | none => rfl
    | some p1 =>
      rcases p1 with ⟨mc, st1⟩
      dsimp only [Option.map_some]
      cases h.entry.find? j with
      | none => rfl
      | some en =>
        dsimp only; rw [strict_jumpTargets]
        cases Rega.jumpTargets armIsa args en.ploc with
        | none => rfl
        | some argTgts =>
          dsimp only
          have hok : ((en.live ++ argTgts).all fun (_, loc) =>
              Rega.jumpLocOk vllArmStrictIsa h.nslots loc) =
            ((en.live ++ argTgts).all fun (_, loc) =>
              Rega.jumpLocOk armIsa h.nslots loc) := by
            congr 1; funext ⟨_, loc⟩; exact strict_jumpLocOk h.nslots loc
          rw [hok]; split; · rfl
          rw [← shuffle_factor h.nslots h.saved st1 (en.live ++ argTgts)]
          cases Rega.shuffle vllArmStrictIsa h.nslots h.saved st1 (en.live ++ argTgts) with
          | none => rfl
          | some p2 =>
            rcases p2 with ⟨sc, _⟩
            dsimp only [liftRes, Except.map, Option.map_some]
            congr 1; congr 1
            rw [asmArm64List_append, asmArm64List_append]
            congr 1; split
            · rfl
            · exact strict_jmp_asm _
  | .ret vs, nv, nl, ip, st, _, _, _ => by
    dsimp only [Rega.lowerExpr]
    rw [← stepPre_factor h ip st]
    cases Rega.stepPre vllArmStrictIsa h ip st with
    | none => rfl
    | some p1 =>
      rcases p1 with ⟨mc, st1⟩
      dsimp only [Option.map_some]; rw [strict_assignRets]
      cases armIsa.assignRets rs with
      | none => rfl
      | some retLocs =>
        have hr := lowerTail_factor h E st1 mc vllArmStrictIsa.frame.ret vs retLocs nv nl ip
        rw [strict_ret_asm] at hr; exact hr
  | .exit f args, nv, nl, ip, st, _, _, _ => by
    dsimp only [Rega.lowerExpr]
    rw [← stepPre_factor h ip st]
    cases Rega.stepPre vllArmStrictIsa h ip st with
    | none => rfl
    | some p1 =>
      rcases p1 with ⟨mc, st1⟩
      dsimp only [Option.map_some]; rw [strict_assignArgs]
      cases armIsa.assignArgs _ with
      | none => rfl
      | some argLocs =>
        dsimp only; split; · rfl
        have hr := lowerTail_factor h E st1 mc (vllArmStrictIsa.frame.exitJmp f)
          args argLocs nv nl ip
        rw [strict_exitJmp_asm] at hr; exact hr
  | .hlt, _, _, _, _, _, _, _ => rfl
  | .group (sig := sig) bodies k, nv, nl, ip, st, ft, fwd, fwdTgts => by
    dsimp only [Rega.lowerExpr]
    rw [findGroupFwds_factor h st (bodies (Tup.levels sig nl))
      (k (Tup.levels sig nl)) nv nl ip fwd fwdTgts]
    let p := Rega.findGroupFwds armIsa h (liftSt st) (bodies (Tup.levels sig nl))
      (k (Tup.levels sig nl)) nv nl ip fwd fwdTgts
    cases hk : Rega.lowerExpr vllArmStrictIsa h E fn (k (Tup.levels sig nl)) nv (nl + sig.length)
        ip st (Rega.firstNonFwd p.1 (bodies (Tup.levels sig nl)) nl ft) p.1 p.2 with
    | error err =>
      have hlk := lowerExpr_factor h E fn (k (Tup.levels sig nl)) nv (nl + sig.length)
        ip st (Rega.firstNonFwd p.1 (bodies (Tup.levels sig nl)) nl ft) p.1 p.2
      rw [hk] at hlk; rw [← hlk]; rfl
    | ok pk =>
      rcases pk with ⟨ck, nv1, nl1, ip1⟩
      have hlk := lowerExpr_factor h E fn (k (Tup.levels sig nl)) nv (nl + sig.length)
        ip st (Rega.firstNonFwd p.1 (bodies (Tup.levels sig nl)) nl ft) p.1 p.2
      rw [hk] at hlk; rw [← hlk]
      rw [liftRes_prepend]
      exact congrArg (Rega.prepend (asmArm64List ck))
        (lowerBlocks_factor h E fn (bodies (Tup.levels sig nl)) nl nv1 nl1 ip1
          st.defs st.vecWidths ft p.1 p.2)

private theorem lowerBlocks_factor {rs : List Ty} (h : armIsa.Hints) (E : Rega.Ext) (fn : Sym) :
    ∀ {sig : List (List Ty)} (bs : Blocks Rega.VNat Rega.LNat rs sig)
      (lid nv nl ip : Nat) (defs : Trie Rega.DefFact) (vw : Trie SlotWidth)
      (ft : Option Nat) (fwd : Trie Nat) (fwdTgts : Trie Bool),
      liftRes (Rega.lowerBlocks vllArmStrictIsa h E fn bs lid nv nl ip defs vw ft fwd fwdTgts) =
        Rega.lowerBlocks armIsa h E fn bs lid nv nl ip defs vw ft fwd fwdTgts
  | _, .nil, _, _, _, _, _, _, _, _, _ => rfl
  | _, .cons (ts := ts) b bs, lid, nv, nl, ip, defs, vw, ft, fwd, fwdTgts => by
    dsimp only [Rega.lowerBlocks]
    cases fwd.find? lid with
    | some fwdTgt =>
      dsimp only; rw [blockTrampoline?_factor h defs vw lid nv ip b]
      cases Rega.blockTrampoline? armIsa h defs vw lid nv ip b with
      | none => rfl
      | some j' =>
        dsimp only; split; · rfl
        exact lowerBlocks_factor h E fn bs (lid + 1) (nv + ts.length) nl (ip + 1)
          defs vw ft fwd fwdTgts
    | none => cases h.entry.find? lid with
      | none => rfl
      | some en =>
        dsimp only
        have hsc : Rega.entryScopeOk (I := vllArmStrictIsa) nv en =
            Rega.entryScopeOk (I := armIsa) nv en := rfl
        rw [hsc]; split; · rfl
        rw [← buildEntryBase_factor h.nslots vw en.live
          { regs := [], slots := .empty, defs := defs, vecWidths := vw }]
        cases Rega.buildEntryBase vllArmStrictIsa h.nslots vw en.live _ with
        | none => rfl
        | some baseSt =>
          dsimp only [Option.map_some]
          rw [← bindBlockParams_factor h.nslots ts en.ploc nv baseSt]
          cases Rega.bindBlockParams vllArmStrictIsa h.nslots ts en.ploc nv baseSt with
          | none => rfl
          | some initSt =>
            dsimp only [Option.map_some]
            let ftB := Rega.firstNonFwd fwd bs (lid + 1) ft
            cases hb : Rega.lowerExpr vllArmStrictIsa h E fn (b (Tup.levels ts nv))
                (nv + ts.length) nl ip initSt ftB fwd fwdTgts with
            | error err =>
              have hlb := lowerExpr_factor h E fn (b (Tup.levels ts nv))
                (nv + ts.length) nl ip initSt ftB fwd fwdTgts
              rw [hb] at hlb; rw [← hlb]; rfl
            | ok pb =>
              rcases pb with ⟨cb, nv1, nl1, ip1⟩
              have hlb := lowerExpr_factor h E fn (b (Tup.levels ts nv))
                (nv + ts.length) nl ip initSt ftB fwd fwdTgts
              rw [hb] at hlb; rw [← hlb]
              rw [liftRes_prepend]
              have hlab : asmArm64List (vllArmStrictIsa.frame.label (Rega.lname fn lid) :: cb) =
                  armIsa.frame.label (Rega.lname fn lid) :: asmArm64List cb := by
                simp only [asmArm64List_cons, asmArm64, vllArmStrictIsa, vllFrameIsaOfHooks,
                  vllFrameIsa, armIsa, armFrame, List.singleton_append]
              rw [hlab]
              exact congrArg (Rega.prepend _)
                (lowerBlocks_factor h E fn bs (lid + 1) nv1 nl1 ip1 defs vw ft fwd fwdTgts)
end

/-- **1:1 `Rega.lowerFn` factoring theorem:** assembling the `BedrockMach` L1 AArch64 output of
`Rega.lowerFn vllArmStrictTarget.toIsa` via `asmArm64List` equals `Rega.lowerFn armTarget.toIsa`
identically (exact directive equality on `.ok`, identical error string on `.error`). -/
theorem vllArmStrict_lowerFn_factor (h : armIsa.Hints) (E : Rega.Ext) (f : Fn) :
    (Rega.lowerFn vllArmStrictTarget.toIsa h E f).map asmArm64List =
      Rega.lowerFn armTarget.toIsa h E f := by
  dsimp only [vllArmStrictTarget, armTarget, Rega.lowerFn]
  rw [strict_cs]; split; · rfl
  rw [strict_assignArgs, strict_assignRets]
  cases armIsa.assignArgs f.as with
  | none => rfl
  | some argLocs => cases armIsa.assignRets f.rs with
    | none => rfl
    | some _ =>
      dsimp only
      rw [← bindAbiParams_factor argLocs 0
        { regs := [], slots := .empty, defs := .empty, vecWidths := .empty }]
      cases Rega.bindAbiParams vllArmStrictIsa argLocs 0 _ with
      | none => rfl
      | some st0 =>
        dsimp only [Option.map_some]
        cases hl : Rega.lowerExpr vllArmStrictIsa h E f.name
            (f.body Rega.VNat Rega.LNat (Tup.levels f.as 0)) f.as.length 0 0 st0 none with
        | error err =>
          have hle := lowerExpr_factor h E f.name
            (f.body Rega.VNat Rega.LNat (Tup.levels f.as 0)) f.as.length 0 0 st0 none .empty .empty
          rw [hl] at hle; rw [← hle]; rfl
        | ok p =>
          rcases p with ⟨c, _, _, _⟩
          have hle := lowerExpr_factor h E f.name
            (f.body Rega.VNat Rega.LNat (Tup.levels f.as 0)) f.as.length 0 0 st0 none .empty .empty
          rw [hl] at hle; rw [← hle]
          dsimp only [liftRes, Except.map]
          congr 1
          have hpro : asmArm64List (Rega.fnPrologue vllArmStrictIsa h E) =
              Rega.fnPrologue armIsa h E := by
            dsimp only [Rega.fnPrologue]
            rw [strict_isZeroLeaf]
            cases Rega.isZeroLeaf armIsa h E with
            | true => rfl
            | false => exact strict_prologue_fst h.totalSlots
          rw [asmArm64List_cons, asmArm64List_append, asmArm64List_append, hpro, saveCs_factor]
          rfl

/-- **1:1 `compileFn` factoring theorem** for `vllArmStrictTarget` vs `armTarget`. -/
theorem vllArmStrict_compileFn_factor (h : armIsa.Hints) (f : Fn) :
    (compileFn vllArmStrictTarget.toIsa armLegalTarget h f).map asmArm64List =
      compileFn armTarget.toIsa armLegalTarget h f :=
  vllArmStrict_lowerFn_factor h (f.mid armLegalTarget).ext (f.mid armLegalTarget)

/-- **1:1 `compile` factoring theorem** over multi-function lists. -/
theorem vllArmStrict_compile_factor :
    ∀ (fs : List Fn) (hs : List armIsa.Hints),
      (compile vllArmStrictTarget.toIsa armLegalTarget fs hs).map asmArm64List =
        compile armTarget.toIsa armLegalTarget fs hs
  | [], [] => rfl
  | f :: fs, h :: hs => by
    dsimp only [compile]
    rw [← vllArmStrict_compileFn_factor h f, ← vllArmStrict_compile_factor fs hs]
    cases compileFn vllArmStrictTarget.toIsa armLegalTarget h f with
    | error _ => rfl
    | ok c => cases compile vllArmStrictTarget.toIsa armLegalTarget fs hs with
      | error _ => rfl
      | ok cs => simp [Except.map, asmArm64List_append]
  | [], _ :: _ | _ :: _, [] => rfl

/-- **1:1 `compileModule` factoring theorem** over complete acyclic modules. -/
theorem vllArmStrict_compileModule_factor (extCallees : List (SigEntry × Nat))
    (exits : List Sym) (nX : Nat) :
    ∀ (fs : List Fn) (hs : List armIsa.Hints),
      (compileModule vllArmStrictTarget.toIsa armLegalTarget 0 extCallees exits nX fs hs).map
          (fun (c, bs) => (asmArm64List c, bs)) =
        compileModule armTarget.toIsa armLegalTarget 0 extCallees exits nX fs hs
  | [], [] => rfl
  | f :: fs, h :: hs => by
    dsimp only [compileModule]
    split
    · rw [← vllArmStrict_lowerFn_factor h _ _, strict_checkAndBoundExt]
      cases Rega.lowerFn vllArmStrictTarget.toIsa h _ _ with
      | error _ => rfl
      | ok c =>
        cases checkAndBoundExt armIsa 0 exits nX extCallees h _ with
        | none => rfl
        | some b =>
          dsimp only [Except.map]
          rw [← vllArmStrict_compileModule_factor ((_, b) :: extCallees) exits nX fs hs]
          cases compileModule vllArmStrictTarget.toIsa armLegalTarget 0
              ((_, b) :: extCallees) exits nX fs hs with
          | error _ => rfl
          | ok p => simp [Except.map, asmArm64List_append]
    · rfl
  | [], _ :: _ | _ :: _, [] => rfl

/-- Universe-polymorphic factoring witness lifting `Unified.Factoring` to `Src : Type u`
(supporting `Fn : Type 1` directly alongside `Unified.Factoring` at `Type 0`). -/
structure FactoringU.{u} (Src : Type u) (D I : Type) : Type u where
  direct : Src → Except String (List D)
  vll : Src → Except String (List I)
  asm : I → List D
  factor : ∀ f, (vll f).map (·.flatMap asm) = direct f

/-- Transport any production certificate along a universe-polymorphic `FactoringU`. -/
theorem FactoringU.transport.{u} {Src : Type u} {D I : Type} (F : FactoringU Src D I)
    (Cert : Src → List D → Prop) (hc : ∀ f ds, F.direct f = .ok ds → Cert f ds) :
    ∀ f is, F.vll f = .ok is → Cert f (is.flatMap F.asm) := by
  intro f is h; apply hc; rw [← F.factor f, h]; rfl

/-- Byte-identical output between `F.direct` and `F.vll` followed by `F.asm`. -/
theorem FactoringU.same_bytes.{u} {Src : Type u} {D I : Type} (F : FactoringU Src D I)
    (f : Src) (is : List I) (h : F.vll f = .ok is) : F.direct f = .ok (is.flatMap F.asm) := by
  rw [← F.factor f, h]; rfl

/-- **`FactoringU` witness for `compileFn`** over ALL `Fn : Type 1` (parameterized by `hints`). -/
@[expose] def arm64Factoring (hints : Fn → armIsa.Hints) :
    FactoringU Fn _root_.Directive (Instr arm64Arch) where
  direct f := compileFn armTarget.toIsa armLegalTarget (hints f) f
  vll f := compileFn vllArmStrictTarget.toIsa armLegalTarget (hints f) f
  asm := asmArm64
  factor f := vllArmStrict_compileFn_factor (hints f) f

/-- **`FactoringU` witness for `Rega.lowerFn`** over ALL `Fn : Type 1` (fixed hints & externs). -/
@[expose] def arm64LowerFactoring (hints : armIsa.Hints) (E : Rega.Ext) :
    FactoringU Fn _root_.Directive (Instr arm64Arch) where
  direct f := Rega.lowerFn armTarget.toIsa hints E f
  vll f := Rega.lowerFn vllArmStrictTarget.toIsa hints E f
  asm := asmArm64
  factor f := vllArmStrict_lowerFn_factor hints E f

/-- **`FactoringU` witness with automatic `Spill.hints`** on `f.mid armLegalTarget`. -/
@[expose] def arm64FactoringAuto :
    FactoringU Fn _root_.Directive (Instr arm64Arch) :=
  arm64Factoring fun f => Spill.hints armIsa (f.mid armLegalTarget)

/-- Direct `Unified.Factoring` witness (`Type 0`) for any concrete function `f : Fn`. -/
@[expose] def arm64FactoringOn (hints : Fn → armIsa.Hints) (f : Fn) :
    Unified.Factoring PUnit _root_.Directive (Instr arm64Arch) where
  direct _ := compileFn armTarget.toIsa armLegalTarget (hints f) f
  vll _ := compileFn vllArmStrictTarget.toIsa armLegalTarget (hints f) f
  asm := asmArm64
  factor _ := vllArmStrict_compileFn_factor (hints f) f

/-- Direct `Unified.Factoring` witness (`Type 0`) for `Rega.lowerFn` on any concrete `f : Fn`. -/
@[expose] def arm64LowerFactoringOn (hints : armIsa.Hints) (E : Rega.Ext) (f : Fn) :
    Unified.Factoring PUnit _root_.Directive (Instr arm64Arch) where
  direct _ := Rega.lowerFn armTarget.toIsa hints E f
  vll _ := Rega.lowerFn vllArmStrictTarget.toIsa hints E f
  asm := asmArm64
  factor _ := vllArmStrict_lowerFn_factor hints E f

/-- Direct `Unified.Factoring` witness (`Type 0`) across any finite function list `fs : List Fn`
(e.g. all `413` `FullM7Fidelity` functions via `Fin fs.length`). -/
@[expose] def arm64FactoringList (hints : Fn → armIsa.Hints) (fs : List Fn) :
    Unified.Factoring (Fin fs.length) _root_.Directive (Instr arm64Arch) where
  direct i := compileFn armTarget.toIsa armLegalTarget (hints (fs.get i)) (fs.get i)
  vll i := compileFn vllArmStrictTarget.toIsa armLegalTarget (hints (fs.get i)) (fs.get i)
  asm := asmArm64
  factor i := vllArmStrict_compileFn_factor (hints (fs.get i)) (fs.get i)

/-- Direct `Unified.Factoring` witness with automatic `Spill.hints` over any `fs : List Fn`. -/
@[expose] def arm64FactoringAutoList (fs : List Fn) :
    Unified.Factoring (Fin fs.length) _root_.Directive (Instr arm64Arch) :=
  arm64FactoringList (fun f => Spill.hints armIsa (f.mid armLegalTarget)) fs

/-! ## 4. End-to-End Semantic Soundness & `FnSpec` Bridge -/

/-- End-to-end L1 soundness of `vllArmTarget` (`vllTarget arm64Arch arm64Arch_wf vllArmPolicy`),
specializing `vllLowerFn_correct`. -/
theorem vllArmTarget_lowerFn_correct (host : VllHost arm64Arch)
    (hints : vllArmTarget.toIsa.Hints) (E : Rega.Ext) (f : Fn)
    (Γ : Env) (n nX : Nat) (bound : Sym → Nat) {code : List (Instr arm64Arch)} {k₀ : Nat}
    (hf : f.Wf) (hl : vllLowerFn arm64Arch vllArmPolicy hints E f = .ok code)
    (hc : code.IsInfixAt host.prog k₀) (hu : vllArmTarget.LabelsUnique host)
    (hfr : Rega.effFrame vllArmTarget.toIsa hints E ≤ n)
    (hn : n + arm64Arch.abi.raBytes ≤ 2 ^ 64)
    (hcal : ∀ g as bs, (g, as, bs) ∈ E.callees →
      vllArmTarget.FnSpec host g (Γ g as bs) (bound g) nX ∧
      Rega.effFrame vllArmTarget.toIsa hints E + arm64Arch.abi.raBytes + bound g ≤ n)
    (hex : ∀ g, g ∈ E.exits → vllArmTarget.Defined host g ∧ nX ≤ n) :
    vllArmTarget.FnSpec host f.name (Func.spec Γ f.body) n nX :=
  vllLowerFn_correct arm64Arch arm64Arch_wf vllArmPolicy host hints E f Γ n nX bound
    hf hl hc hu hfr hn hcal hex

/-- End-to-end L1 soundness of `vllArmStrictTarget` directly over `vllMach arm64Arch`. -/
theorem vllArmStrict_lowerFn_correct (host : VllHost arm64Arch)
    (hints : armIsa.Hints) (E : Rega.Ext) (f : Fn)
    (Γ : Env) (n nX : Nat) (bound : Sym → Nat) {code : List (Instr arm64Arch)} {k₀ : Nat}
    (hf : f.Wf) (hl : Rega.lowerFn vllArmStrictTarget.toIsa hints E f = .ok code)
    (hc : code.IsInfixAt host.prog k₀) (hu : vllArmStrictTarget.LabelsUnique host)
    (hfr : Rega.effFrame vllArmStrictTarget.toIsa hints E ≤ n)
    (hn : n + 0 ≤ 2 ^ 64)
    (hcal : ∀ g as bs, (g, as, bs) ∈ E.callees →
      vllArmStrictTarget.FnSpec host g (Γ g as bs) (bound g) nX ∧
      Rega.effFrame vllArmStrictTarget.toIsa hints E + 0 + bound g ≤ n)
    (hex : ∀ g, g ∈ E.exits → vllArmStrictTarget.Defined host g ∧ nX ≤ n) :
    vllArmStrictTarget.FnSpec host f.name (Func.spec Γ f.body) n nX :=
  Rega.lowerFn_correct vllArmStrictTarget host hints E f Γ n nX bound
    hf hl hc hu hfr hn hcal hex

/-- **Semantic bridge (`vllArmStrictTarget` → `armTarget.FnSpec`):** any function lowered through
`BedrockMach` L1 (`vllArmStrictTarget`) and assembled via `asmArm64List` inherits the full
Kraken AArch64 `armTarget.FnSpec` certificate on every Kraken `Host` containing `asmArm64List code`.
-/
theorem vllArmStrict_to_armTarget_fnSpec (host : Host)
    (hints : armIsa.Hints) (E : Rega.Ext) (f : Fn)
    (Γ : Env) (n nX : Nat) (bound : Sym → Nat) {code : List (Instr arm64Arch)} {k₀ : Nat}
    (hf : f.Wf) (hl : Rega.lowerFn vllArmStrictTarget.toIsa hints E f = .ok code)
    (hc : (asmArm64List code).IsInfixAt (armMach.prog host) k₀)
    (hu : armTarget.LabelsUnique host)
    (hfr : Rega.effFrame armTarget.toIsa hints E ≤ n)
    (hn : n + 0 ≤ 2 ^ 64)
    (hcal : ∀ g as bs, (g, as, bs) ∈ E.callees →
      armTarget.FnSpec host g (Γ g as bs) (bound g) nX ∧
      Rega.effFrame armTarget.toIsa hints E + 0 + bound g ≤ n)
    (hex : ∀ g, g ∈ E.exits → armTarget.Defined host g ∧ nX ≤ n) :
    armTarget.FnSpec host f.name (Func.spec Γ f.body) n nX :=
  Rega.lowerFn_correct armTarget host hints E f Γ n nX bound hf
    ((arm64LowerFactoring hints E).same_bytes f code hl) hc hu hfr hn hcal hex

/-- Transport any Kraken AArch64 production certificate `Cert` along `arm64Factoring hints`. -/
theorem vllArmStrict_transport_cert (hints : Fn → armIsa.Hints)
    (Cert : Fn → List _root_.Directive → Prop)
    (hc : ∀ f ds, compileFn armTarget.toIsa armLegalTarget (hints f) f = .ok ds → Cert f ds) :
    ∀ f is, compileFn vllArmStrictTarget.toIsa armLegalTarget (hints f) f = .ok is →
      Cert f (asmArm64List is) :=
  (arm64Factoring hints).transport Cert hc

/-- Byte-exact directive identity specialization of `Unified.Factoring.same_bytes`. -/
theorem vllArmStrict_same_bytes (hints : Fn → armIsa.Hints) (f : Fn)
    (is : List (Instr arm64Arch))
    (h : compileFn vllArmStrictTarget.toIsa armLegalTarget (hints f) f = .ok is) :
    compileFn armTarget.toIsa armLegalTarget (hints f) f = .ok (asmArm64List is) :=
  (arm64Factoring hints).same_bytes f is h

end LeanQbe.T.Arm64
