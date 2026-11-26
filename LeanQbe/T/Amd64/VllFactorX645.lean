module

public import LeanQbe.T.Amd64.VllFactorX644
import LeanQbe.T.Amd64.VllFactorX64Zero

/-!
# BedrockMach SysV x86-64 `lowerOp` Parity (`Amd64.VllFactorX645`)

Part 2b1 of the exact `asmX64List` lowering equality proof between `vllX64Isa` (`vllX64Target`) and
`x64Isa` (`x64Target`): fused test/cmp/ext/slot/loadSext/LEA helpers, flag-cmp reuse, `normCmpOp`,
and `lowerOp_eq_and_noRsp` / `lowerOp_of_x64_some`.

Zero `Arm64` / `Kraken.AArch64` imports, zero `@[expose]` on proof theorems/lemmas.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

open LeanQbe.T
open LeanQbe.T.Vll
open Std Std.ExtHashMap

private theorem mapOptCl_option_map {α γ : Type}
    {o₁ : Option (List (Instr x64Arch) × α)} {o₂ : Option (List _root_.Directive × α)}
    (ho : mapOptCl o₁ = o₂)
    {f₁ : List (Instr x64Arch) × α → List (Instr x64Arch) × γ}
    {f₂ : List _root_.Directive × α → List _root_.Directive × γ}
    (hf : ∀ c a,
      (asmX64List (f₁ (c, a)).1, (f₁ (c, a)).2) = f₂ (asmX64List c, a)) :
    mapOptCl (o₁.map f₁) = o₂.map f₂ := by
  cases o₁ with
  | none => subst ho; rfl
  | some p =>
    rcases p with ⟨c, a⟩
    subst ho
    dsimp only [mapOptCl, Option.map]
    exact congrArg some (hf c a)

private theorem mapOptCl_bind_congr {α β : Type} {o : Option α}
    {f₁ : α → Option (List (Instr x64Arch) × β)}
    {f₂ : α → Option (List _root_.Directive × β)}
    (hf : ∀ x, mapOptCl (f₁ x) = f₂ x) :
    mapOptCl (o.bind f₁) = o.bind f₂ := by
  cases o with
  | none => rfl
  | some x => exact hf x

private theorem mapOptCl_bind_congr' {α β : Type} {o₁ o₂ : Option α} (ho : o₁ = o₂)
    {f₁ : α → Option (List (Instr x64Arch) × β)}
    {f₂ : α → Option (List _root_.Directive × β)}
    (hf : ∀ x, mapOptCl (f₁ x) = f₂ x) :
    mapOptCl (o₁.bind f₁) = o₂.bind f₂ := by
  subst ho
  exact mapOptCl_bind_congr hf

private theorem option_bind_const_none' {α β : Type} :
    ∀ o : Option α, o.bind (fun _ => (none : Option β)) = none
  | none | some _ => rfl

private theorem tryFlag_const_none (I : Isa) (R : List (SymArg × Rega.RegLoc I.Reg I.VReg I.Cond))
    (pref : List I.Cond) (sa : SymArg) {α : Type} (k : I.Cond → Option α)
    (hk : ∀ c, k c = none) :
    Rega.tryFlag I R pref sa k = none := by
  dsimp only [Rega.tryFlag]
  have h1 : (pref.findSome? fun c =>
      if R.any (fun (sa', rl) => Rega.symArgEq sa' sa &&
          Rega.regLocEq (I := I) rl (.flag c)) then k c else none) = none := by
    induction pref with
    | nil => rfl
    | cons c cs ih =>
      dsimp only [List.findSome?]; rw [hk c]
      cases R.any (fun (sa', rl) => Rega.symArgEq sa' sa &&
        Rega.regLocEq (I := I) rl (.flag c)) <;> exact ih
  have h2 : (R.findSome? fun x => match x.2 with
      | .flag c => if Rega.symArgEq x.1 sa then k c else none
      | _ => none) = none := by
    clear h1
    induction R with
    | nil => rfl
    | cons p rest ih =>
      rcases p with ⟨sa', rl⟩
      dsimp only [List.findSome?]
      cases rl with
      | gpr _ | gprZ _ | vec _ => exact ih
      | flag c => dsimp only; rw [hk c]; cases Rega.symArgEq sa' sa <;> exact ih
  rw [h1]; exact h2

private theorem tryGpr_const_none (I : Isa) (R : List (SymArg × Rega.RegLoc I.Reg I.VReg I.Cond))
    (sa : SymArg) {α : Type} (k : I.Reg → Option α) (hk : ∀ r, k r = none) :
    Rega.tryGpr I R sa k = none := by
  dsimp only [Rega.tryGpr]
  induction R with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨sa', rl⟩
    dsimp only [List.findSome?]
    cases rl with
    | vec _ | flag _ => exact ih
    | gpr r | gprZ r =>
      dsimp only; rw [hk r]
      cases !(I.frame.scratch.contains r) && Rega.symArgMatchesGpr sa' sa <;> exact ih

private theorem tryVec_const_none (I : Isa) (R : List (SymArg × Rega.RegLoc I.Reg I.VReg I.Cond))
    (sa : SymArg) {α : Type} (k : I.VReg → Option α) (hk : ∀ v, k v = none) :
    Rega.tryVec I R sa k = none := by
  dsimp only [Rega.tryVec]
  induction R with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨sa', rl⟩
    dsimp only [List.findSome?]
    cases rl with
    | gpr _ | gprZ _ | flag _ => exact ih
    | vec v =>
      dsimp only; rw [hk v]
      cases !(I.vec.vecScratch.contains v) && Rega.symArgEq sa' sa <;> exact ih

private theorem tryArg_const_none (I : Isa) (st : Rega.SymState I) (pref : List I.Cond)
    (t : Ty) (a : Arg Rega.VNat t) {α : Type}
    (k : PArg I.Reg I.VReg I.Cond t → Option α) (hk : ∀ pa, k pa = none) :
    Rega.tryArg I st pref t a k = none := by
  cases t with
  | bool =>
    cases a with
    | var _ =>
      dsimp only [Rega.tryArg]
      rw [tryFlag_const_none I _ _ _ (k ∘ PArg.flag) (fun _ => hk _),
        tryGpr_const_none I _ _ (k ∘ PArg.gpr) (fun _ => hk _)]
      rfl
    | imm _ =>
      dsimp only [Rega.tryArg]
      rw [tryFlag_const_none I _ _ _ (k ∘ PArg.flag) (fun _ => hk _), hk,
        tryGpr_const_none I _ _ (k ∘ PArg.gpr) (fun _ => hk _)]
      rfl
  | bits _ =>
    cases a with
    | var _ =>
      dsimp only [Rega.tryArg]
      exact tryGpr_const_none I st.regs _ (k ∘ PArg.gpr) (fun _ => hk _)
    | imm _ =>
      dsimp only [Rega.tryArg]; rw [hk]
      split
      · rw [tryGpr_const_none I _ _ (k ∘ PArg.gpr) (fun _ => hk _)]; rfl
      · rfl
  | float _ => cases a <;> rfl
  | pair _ _ =>
    cases a with
    | var _ =>
      dsimp only [Rega.tryArg]
      exact tryVec_const_none I st.regs _ (k ∘ PArg.vec) (fun _ => hk _)
    | imm _ =>
      dsimp only [Rega.tryArg]; rw [hk]
      cases Rega.vecWidth? I _ with
      | none => rfl
      | some _ => dsimp only; rw [tryVec_const_none I _ _ (k ∘ PArg.vec) (fun _ => hk _)]; rfl

private theorem pickPArgs_const_none (I : Isa) (st : Rega.SymState I) (pref : List I.Cond)
    {α : Type} :
    ∀ {sig : List Ty} (args : Tup (Arg Rega.VNat) sig)
      (k : Tup (PArg I.Reg I.VReg I.Cond) sig → Option α),
      (∀ pas, k pas = none) →
      Rega.pickPArgs I st pref args k = none
  | [], (), _, hk => hk ()
  | t :: _, (a, as), k, hk => by
    dsimp only [Rega.pickPArgs]
    exact tryArg_const_none I st pref t a _ (fun pa =>
      pickPArgs_const_none I st pref as (fun pas => k (pa, pas)) (fun pas => hk (pa, pas)))

theorem tryTestMemVar_eq (st : Rega.SymState vllX64IsaR) (neg : Bool) (n x : Nat)
    (other : Arg Rega.VNat (.bits n)) (pd : PDst Reg64 RegMm CondCode .bool)
    (hno : regsNoRsp st.regs = true) :
    mapOptCl (Rega.tryTestMemVar vllX64IsaR st neg n x other pd) =
      Rega.tryTestMemVar x64Isa (symStToX64 st) neg n x other pd := by
  dsimp only [Rega.tryTestMemVar, symStToX64]
  cases st.memDefs.find? x with
  | none => rfl
  | some p =>
    rcases p with ⟨ty, addr⟩
    cases ty with
    | bool | float _ | pair _ _ => rfl
    | bits m =>
      dsimp only; split
      · exact mapOptCl_tryAddr st .default addr hno (fun aa _ =>
          mapOptCl_tryArg st [] (.bits n) other (fun pb => vllR_testMem_eq n neg aa pb pd))
      · rfl

theorem tryTestFuse_eq (st : Rega.SymState vllX64IsaR) (neg : Bool) (n t : Nat)
    (pd : PDst Reg64 RegMm CondCode .bool) (hno : regsNoRsp st.regs = true) :
    mapOptCl (Rega.tryTestFuse vllX64IsaR st neg n t pd) =
      Rega.tryTestFuse x64Isa (symStToX64 st) neg n t pd := by
  dsimp only [Rega.tryTestFuse, symStToX64]
  cases st.defs.find? t with
  | none => rfl
  | some df =>
    cases df with
    | andVarImm w x c =>
      dsimp only; split
      · rfl
      · exact mapOptCl_or_congr (tryTestMemVar_eq st neg n x (.imm (c.setWidth n)) pd hno)
          (mapOptCl_tryArg st [] (.bits n) (.var x) fun pa =>
            vllR_testOp_eq n neg pa (.imm (c.setWidth n)) pd)
    | andVarVar w x y =>
      dsimp only; split
      · rfl
      · exact mapOptCl_or_congr (tryTestMemVar_eq st neg n x (.var y) pd hno)
          (mapOptCl_or_congr (tryTestMemVar_eq st neg n y (.var x) pd hno)
            (mapOptCl_tryArg st [] (.bits n) (.var x) fun pa =>
              mapOptCl_tryArg st [] (.bits n) (.var y) fun pb => vllR_testOp_eq n neg pa pb pd))
    | _ => rfl

private theorem tryExtCmpMem_eq (st : Rega.SymState vllX64IsaR) (co : CmpOp)
    {m : Nat} (x : Nat) (cm : BitVec m) (pd : PDst Reg64 RegMm CondCode .bool)
    (hno : regsNoRsp st.regs = true) :
    mapOptCl
      (match st.memDefs.find? x with
       | some (.bits m', addr) =>
         if Nat.beq m' m then
           Rega.tryAddr vllX64IsaR st .default addr fun aa =>
             (vllX64IsaR.gpr.cmpMem co m aa (.imm cm) pd).map fun (d, cl) =>
               Rega.cmpMemRes vllX64IsaR st co m (.var x) (.immBits m (cm.setWidth 64)) pd d cl
         else none
       | _ => none) =
    (match (symStToX64 st).memDefs.find? x with
     | some (.bits m', addr) =>
       if Nat.beq m' m then
         Rega.tryAddr x64Isa (symStToX64 st) .default addr fun aa =>
           (x64Isa.gpr.cmpMem co m aa (.imm cm) pd).map fun (d, cl) =>
             Rega.cmpMemRes x64Isa (symStToX64 st) co m (.var x) (.immBits m (cm.setWidth 64))
               pd d cl
       else none
     | _ => none) := by
  dsimp only [symStToX64]
  cases st.memDefs.find? x with
  | none => rfl
  | some p =>
    rcases p with ⟨ty, addr⟩
    cases ty with
    | bool | float _ | pair _ _ => rfl
    | bits m' =>
      dsimp only; split
      · exact mapOptCl_tryAddr st .default addr hno (fun aa _ =>
          mapOptCl_option_map (vllR_cmpMem_eq co m aa (.imm cm) pd) fun cs cl =>
            cmpMemRes_eq st co m (.var x) (.immBits m (cm.setWidth 64)) pd cs cl)
      · rfl

theorem tryExtCmp_eq (st : Rega.SymState vllX64IsaR) (vh : VariantHint) (co : CmpOp)
    (n t : Nat) (c : BitVec n) (pd : PDst Reg64 RegMm CondCode .bool)
    (hno : regsNoRsp st.regs = true) :
    mapOptCl (Rega.tryExtCmp vllX64IsaR st vh co n t c pd) =
      Rega.tryExtCmp x64Isa (symStToX64 st) vh co n t c pd := by
  dsimp only [Rega.tryExtCmp, symStToX64]
  cases st.defs.find? t with
  | none => rfl
  | some df =>
    cases df with
    | sextVar m n' x | zextVar m n' x =>
      dsimp only; split
      · rfl
      · refine mapOptCl_or_congr (tryExtCmpMem_eq st co x (c.truncate m) pd hno) ?_
        rw [ite_eq_left (rfl : true = true), ite_eq_left (rfl : true = true)]
        refine mapOptCl_tryGpr st.regs (.var x) fun rx => ?_
        refine mapOptCl_option_map
          (vllR_op_eq (.cmp co (.bits m)) (.gpr rx, .imm (c.truncate m), ()) (pd, ()) vh rfl)
          fun _ _ => ?_
        dsimp only
        rw [vllR_cmpFlagsOut?_eq, vllR_condOfCmp_eq, killFlags_eq]
        cases pd <;> first | exact rfl | (dsimp only [x64Isa]; rfl)
    | _ => rfl

theorem tryCmpMemVar_eq (st : Rega.SymState vllX64IsaR) (co : CmpOp) (n x : Nat)
    (other : Arg Rega.VNat (.bits n)) (pd : PDst Reg64 RegMm CondCode .bool)
    (hno : regsNoRsp st.regs = true) :
    mapOptCl (Rega.tryCmpMemVar vllX64IsaR st co n x other pd) =
      Rega.tryCmpMemVar x64Isa (symStToX64 st) co n x other pd := by
  dsimp only [Rega.tryCmpMemVar, symStToX64]
  cases st.memDefs.find? x with
  | none => rfl
  | some p =>
    rcases p with ⟨ty, addr⟩
    cases ty with
    | bool | float _ | pair _ _ => rfl
    | bits m =>
      dsimp only; split
      · exact mapOptCl_tryAddr st .default addr hno (fun aa _ =>
          mapOptCl_tryArg st [] (.bits n) other (fun pb => vllR_cmpMem_eq co n aa pb pd))
      · rfl

theorem tryTestSlot_eq (h : x64Isa.Hints) (st : Rega.SymState vllX64IsaR) (neg : Bool)
    (n t : Nat) (pd : PDst Reg64 RegMm CondCode .bool) :
    mapOptCl (Rega.tryTestSlot vllX64IsaR h st neg n t pd) =
      Rega.tryTestSlot x64Isa h (symStToX64 st) neg n t pd := by
  dsimp only [Rega.tryTestSlot, symStToX64]
  split
  · rfl
  · cases st.defs.find? t with
    | none => rfl
    | some df =>
      cases df with
      | andVarImm w x c =>
        dsimp only; split
        · refine mapOptCl_bind_congr (fun idx => ?_)
          rw [vllR_spAddr_eq]; exact vllR_testMem_eq n neg _ _ pd
        · rfl
      | andVarVar w x y =>
        dsimp only; split
        · refine mapOptCl_or_congr ?_ ?_
          · refine mapOptCl_bind_congr (fun idx => ?_)
            rw [vllR_spAddr_eq]
            exact mapOptCl_tryArg st [] (.bits n) (.var y) fun pb => vllR_testMem_eq n neg _ pb pd
          · refine mapOptCl_bind_congr (fun idx => ?_)
            rw [vllR_spAddr_eq]
            exact mapOptCl_tryArg st [] (.bits n) (.var x) fun pa => vllR_testMem_eq n neg _ pa pd
        · rfl
      | _ => rfl

theorem tryExtSlot_eq (h : x64Isa.Hints) (st : Rega.SymState vllX64IsaR) (co : CmpOp)
    (n t : Nat) (c : BitVec n) (pd : PDst Reg64 RegMm CondCode .bool) :
    mapOptCl (Rega.tryExtSlot vllX64IsaR h st co n t c pd) =
      Rega.tryExtSlot x64Isa h (symStToX64 st) co n t c pd := by
  dsimp only [Rega.tryExtSlot, symStToX64]
  cases st.defs.find? t with
  | none => rfl
  | some df =>
    cases df with
    | sextVar m n' x | zextVar m n' x =>
      dsimp only; split
      · refine mapOptCl_bind_congr (fun idx => ?_)
        rw [vllR_spAddr_eq]; exact vllR_cmpMem_eq co m _ _ pd
      · rfl
    | _ => rfl

theorem tryAluSlot_eq (h : x64Isa.Hints) (st : Rega.SymState vllX64IsaR) (n : Nat)
    (code : OpCode [.bits n, .bits n] [.bits n]) (a b : Arg Rega.VNat (.bits n)) (rd : Reg64) :
    mapOptCl (Rega.tryAluSlot vllX64IsaR h st n code a b rd) =
      Rega.tryAluSlot x64Isa h (symStToX64 st) n code a b rd := by
  dsimp only [Rega.tryAluSlot, symStToX64]
  split
  · rfl
  · refine mapOptCl_option_map (mapOptCl_or_congr ?_ ?_) (fun _ _ => ?_)
    · cases a with
      | imm _ => rfl
      | var x =>
        refine mapOptCl_bind_congr (fun idx => ?_)
        rw [vllR_spAddr_eq]
        exact mapOptCl_tryArg st [] (.bits n) b fun pb =>
          vllR_aluMem_eq n code false (Rega.spAddr x64Isa idx) pb rd
    · cases b with
      | imm _ => rfl
      | var y =>
        refine mapOptCl_bind_congr (fun idx => ?_)
        rw [vllR_spAddr_eq]
        exact mapOptCl_tryArg st [] (.bits n) a fun pa =>
          vllR_aluMem_eq n code true (Rega.spAddr x64Isa idx) pa rd
    · dsimp only
      rw [vllR_zeroUpper32AluMem_eq]

private theorem mapOptCl_tryAluSlot (h : x64Isa.Hints) (st : Rega.SymState vllX64IsaR) (n : Nat)
    (code : OpCode [.bits n, .bits n] [.bits n]) (a b : Arg Rega.VNat (.bits n)) (rd : Reg64) :
    mapOptCl
      ((Rega.tryAluSlot vllX64IsaR h st n code a b rd).map fun (c, cl, z32) =>
        (c, cl, z32, Rega.killFlags vllX64IsaR cl st.flags, (none : Option CondCode))) =
    (Rega.tryAluSlot x64Isa h (symStToX64 st) n code a b rd).map fun (c, cl, z32) =>
      (c, cl, z32, Rega.killFlags x64Isa cl (symStToX64 st).flags, (none : Option CondCode)) := by
  refine mapOptCl_option_map (tryAluSlot_eq h st n code a b rd) fun cs p => ?_
  dsimp only
  rw [killFlags_eq]

private theorem tryTestSlot_cmp_eq (h : x64Isa.Hints) (st : Rega.SymState vllX64IsaR)
    (co : CmpOp) (n : Nat) (a b : Arg Rega.VNat (.bits n))
    (pd : PDst Reg64 RegMm CondCode .bool) :
    mapOptCl
      (if (co == .eq || co == .ne) = true then
         let neg := co == .ne
         let res? := match a, b with
           | .var t, .imm c =>
             if c == 0#n then Rega.tryTestSlot vllX64IsaR h st neg n t pd else none
           | .imm c, .var t =>
             if c == 0#n then Rega.tryTestSlot vllX64IsaR h st neg n t pd else none
           | _, _ => none
         res?.map fun (c, cl) =>
           (c, cl, Rega.killFlags vllX64IsaR cl st.flags, Rega.testBoolExtra? vllX64IsaR neg cl pd)
       else none) =
    (if (co == .eq || co == .ne) = true then
       let neg := co == .ne
       let res? := match a, b with
         | .var t, .imm c =>
           if c == 0#n then Rega.tryTestSlot x64Isa h (symStToX64 st) neg n t pd else none
         | .imm c, .var t =>
           if c == 0#n then Rega.tryTestSlot x64Isa h (symStToX64 st) neg n t pd else none
         | _, _ => none
       res?.map fun (c, cl) =>
         (c, cl, Rega.killFlags x64Isa cl (symStToX64 st).flags,
           Rega.testBoolExtra? x64Isa neg cl pd)
     else none) := by
  split
  · have hr :
        mapOptCl
          (match a, b with
           | .var t, .imm c =>
             if c == 0#n then Rega.tryTestSlot vllX64IsaR h st (co == .ne) n t pd else none
           | .imm c, .var t =>
             if c == 0#n then Rega.tryTestSlot vllX64IsaR h st (co == .ne) n t pd else none
           | _, _ => none) =
        (match a, b with
         | .var t, .imm c =>
           if c == 0#n then Rega.tryTestSlot x64Isa h (symStToX64 st) (co == .ne) n t pd else none
         | .imm c, .var t =>
           if c == 0#n then Rega.tryTestSlot x64Isa h (symStToX64 st) (co == .ne) n t pd else none
         | _, _ => none) := by
      cases a <;> cases b <;> try rfl
      · dsimp only; split
        · exact tryTestSlot_eq h st _ n _ pd
        · rfl
      · dsimp only; split
        · exact tryTestSlot_eq h st _ n _ pd
        · rfl
    refine mapOptCl_option_map hr fun cs cl => ?_
    dsimp only
    rw [killFlags_eq, testBoolExtra?_eq]
  · rfl

private theorem tryExtSlot_cmp_eq (h : x64Isa.Hints) (st : Rega.SymState vllX64IsaR)
    (co : CmpOp) (n : Nat) (a b : Arg Rega.VNat (.bits n))
    (pd : PDst Reg64 RegMm CondCode .bool) :
    mapOptCl
      (match a, b with
       | .var t, .imm c =>
         (Rega.tryExtSlot vllX64IsaR h st co n t c pd).map fun (d, cl) =>
           let r := Rega.extCmpMemRes vllX64IsaR co pd d cl
           (r.1, r.2.1, Rega.killFlags vllX64IsaR r.2.1 st.flags, r.2.2)
       | .imm c, .var t =>
         (Rega.tryExtSlot vllX64IsaR h st co.swap n t c pd).map fun (d, cl) =>
           let r := Rega.extCmpMemRes vllX64IsaR co.swap pd d cl
           (r.1, r.2.1, Rega.killFlags vllX64IsaR r.2.1 st.flags, r.2.2)
       | _, _ => none) =
    (match a, b with
     | .var t, .imm c =>
       (Rega.tryExtSlot x64Isa h (symStToX64 st) co n t c pd).map fun (d, cl) =>
         let r := Rega.extCmpMemRes x64Isa co pd d cl
         (r.1, r.2.1, Rega.killFlags x64Isa r.2.1 (symStToX64 st).flags, r.2.2)
     | .imm c, .var t =>
       (Rega.tryExtSlot x64Isa h (symStToX64 st) co.swap n t c pd).map fun (d, cl) =>
         let r := Rega.extCmpMemRes x64Isa co.swap pd d cl
         (r.1, r.2.1, Rega.killFlags x64Isa r.2.1 (symStToX64 st).flags, r.2.2)
     | _, _ => none) := by
  cases a <;> cases b <;> try rfl
  · refine mapOptCl_option_map (tryExtSlot_eq h st co n _ _ pd) fun cs cl => ?_
    have hr := extCmpMemRes_eq co pd cs cl
    dsimp only at hr ⊢
    rw [killFlags_eq]
    have hp : ∀ {α : Type} {a₁ a₂ : α} {b₁ b₂ : FlagMask} {c₁ c₂ : Option CondCode},
        (a₁, b₁, c₁) = (a₂, b₂, c₂) →
        (a₁, b₁, Rega.killFlags x64Isa b₁ st.flags, c₁) =
          (a₂, b₂, Rega.killFlags x64Isa b₂ st.flags, c₂) := by
      intro α a₁ a₂ b₁ b₂ c₁ c₂ he
      cases he; rfl
    exact hp hr
  · refine mapOptCl_option_map (tryExtSlot_eq h st co.swap n _ _ pd) fun cs cl => ?_
    have hr := extCmpMemRes_eq co.swap pd cs cl
    dsimp only at hr ⊢
    rw [killFlags_eq]
    have hp : ∀ {α : Type} {a₁ a₂ : α} {b₁ b₂ : FlagMask} {c₁ c₂ : Option CondCode},
        (a₁, b₁, c₁) = (a₂, b₂, c₂) →
        (a₁, b₁, Rega.killFlags x64Isa b₁ st.flags, c₁) =
          (a₂, b₂, Rega.killFlags x64Isa b₂ st.flags, c₂) := by
      intro α a₁ a₂ b₁ b₂ c₁ c₂ he
      cases he; rfl
    exact hp hr

private theorem trySlotCmpMemHalf_eq (h : x64Isa.Hints) (st : Rega.SymState vllX64IsaR)
    (co' : CmpOp) (n : Nat) (v other : Arg Rega.VNat (.bits n))
    (pd : PDst Reg64 RegMm CondCode .bool) :
    mapOptCl
      (match v with
       | .var x =>
         (Rega.findSlotGpr h.nslots st.slots x).bind fun idx =>
           Rega.tryArg vllX64IsaR st [] (.bits n) other fun pb =>
             (vllX64IsaR.gpr.cmpMem co' n (Rega.spAddr vllX64IsaR idx) pb pd).map fun (d, cl) =>
               match Rega.toSymArg vllX64IsaR (.bits n) other with
               | some sb => Rega.cmpMemRes vllX64IsaR st co' n (.var x) sb pd d cl
               | none => (d, cl, Rega.killFlags vllX64IsaR cl st.flags, none)
       | _ => none) =
    (match v with
     | .var x =>
       (Rega.findSlotGpr h.nslots st.slots x).bind fun idx =>
         Rega.tryArg x64Isa (symStToX64 st) [] (.bits n) other fun pb =>
           (x64Isa.gpr.cmpMem co' n (Rega.spAddr x64Isa idx) pb pd).map fun (d, cl) =>
             match Rega.toSymArg x64Isa (.bits n) other with
             | some sb => Rega.cmpMemRes x64Isa (symStToX64 st) co' n (.var x) sb pd d cl
             | none => (d, cl, Rega.killFlags x64Isa cl (symStToX64 st).flags, none)
     | _ => none) := by
  cases v with
  | imm _ => rfl
  | var x =>
    refine mapOptCl_bind_congr (fun idx => ?_)
    refine mapOptCl_tryArg st [] (.bits n) other fun pb =>
      mapOptCl_option_map (by rw [vllR_spAddr_eq]; exact vllR_cmpMem_eq co' n _ pb pd)
        fun cs cl => by
        dsimp only
        rw [vllR_toSymArg_eq]
        cases Rega.toSymArg x64Isa (.bits n) other with
        | none => rw [killFlags_eq]
        | some sb => exact cmpMemRes_eq st co' n (.var x) sb pd cs cl

theorem trySlotOp_eq (h : x64Isa.Hints) (st : Rega.SymState vllX64IsaR) {sig ts : List Ty}
    (code : OpCode sig ts) (args : Tup (Arg Rega.VNat) sig)
    (dsts : Tup (PDst Reg64 RegMm CondCode) ts) :
    mapOptCl (Rega.trySlotOp vllX64IsaR h st code args dsts) =
      Rega.trySlotOp x64Isa h (symStToX64 st) code args dsts := by
  cases code with
  | add t | sub t | mul t | and t | or t | xor t =>
    cases t with
    | bool | float _ | pair _ _ => rcases args with ⟨_, _, ⟨⟩⟩; rcases dsts with ⟨_, ⟨⟩⟩; rfl
    | bits n =>
      rcases args with ⟨a, b, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
      cases pd with | vec _ => rfl | gpr rd => exact mapOptCl_tryAluSlot h st n _ a b rd
  | cmp co t m hpf =>
    cases t with
    | bool | float _ | pair _ _ => rcases args with ⟨_, _, ⟨⟩⟩; rcases dsts with ⟨_, ⟨⟩⟩; rfl
    | bits n =>
      cases hpf
      rcases args with ⟨a, b, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
      dsimp only [Rega.trySlotOp]
      split
      · rfl
      · refine mapOptCl_option_map
          (mapOptCl_or_congr (tryTestSlot_cmp_eq h st co n a b pd)
            (mapOptCl_or_congr (tryExtSlot_cmp_eq h st co n a b pd) ?_))
          (fun _ _ => rfl)
        split
        · rfl
        · exact mapOptCl_or_congr (trySlotCmpMemHalf_eq h st co n a b pd)
            (trySlotCmpMemHalf_eq h st co.swap n b a pd)
  | _ => rfl

private theorem tryTestFuse_cmp_eq (st : Rega.SymState vllX64IsaR)
    (co : CmpOp) (n : Nat) (a b : Arg Rega.VNat (.bits n))
    (pd : PDst Reg64 RegMm CondCode .bool) (hno : regsNoRsp st.regs = true) :
    mapOptCl
      (if (co == .eq || co == .ne) = true then
         let neg := co == .ne
         let res? := match a, b with
           | .var t, .imm c => if c == 0#n then Rega.tryTestFuse vllX64IsaR st neg n t pd else none
           | .imm c, .var t => if c == 0#n then Rega.tryTestFuse vllX64IsaR st neg n t pd else none
           | _, _ => none
         res?.map fun (c, cl) =>
           (c, cl, Rega.killFlags vllX64IsaR cl st.flags, Rega.testBoolExtra? vllX64IsaR neg cl pd)
       else none) =
    (if (co == .eq || co == .ne) = true then
       let neg := co == .ne
       let res? := match a, b with
         | .var t, .imm c =>
           if c == 0#n then Rega.tryTestFuse x64Isa (symStToX64 st) neg n t pd else none
         | .imm c, .var t =>
           if c == 0#n then Rega.tryTestFuse x64Isa (symStToX64 st) neg n t pd else none
         | _, _ => none
       res?.map fun (c, cl) =>
         (c, cl, Rega.killFlags x64Isa cl (symStToX64 st).flags,
           Rega.testBoolExtra? x64Isa neg cl pd)
     else none) := by
  split
  · have hr :
        mapOptCl
          (match a, b with
           | .var t, .imm c =>
             if c == 0#n then Rega.tryTestFuse vllX64IsaR st (co == .ne) n t pd else none
           | .imm c, .var t =>
             if c == 0#n then Rega.tryTestFuse vllX64IsaR st (co == .ne) n t pd else none
           | _, _ => none) =
        (match a, b with
         | .var t, .imm c =>
           if c == 0#n then Rega.tryTestFuse x64Isa (symStToX64 st) (co == .ne) n t pd else none
         | .imm c, .var t =>
           if c == 0#n then Rega.tryTestFuse x64Isa (symStToX64 st) (co == .ne) n t pd else none
         | _, _ => none) := by
      cases a <;> cases b <;> try rfl
      · dsimp only; split
        · exact tryTestFuse_eq st _ n _ pd hno
        · rfl
      · dsimp only; split
        · exact tryTestFuse_eq st _ n _ pd hno
        · rfl
    refine mapOptCl_option_map hr fun cs cl => ?_
    dsimp only
    rw [killFlags_eq, testBoolExtra?_eq]
  · rfl

private theorem tryFuseCmpMemHalf_eq (st : Rega.SymState vllX64IsaR) (co' : CmpOp) (n : Nat)
    (v other : Arg Rega.VNat (.bits n)) (pd : PDst Reg64 RegMm CondCode .bool)
    (hno : regsNoRsp st.regs = true) :
    mapOptCl
      (match v with
       | .var x =>
         (Rega.tryCmpMemVar vllX64IsaR st co' n x other pd).map fun (c, cl) =>
           match Rega.toSymArg vllX64IsaR (.bits n) other with
           | some sb => Rega.cmpMemRes vllX64IsaR st co' n (.var x) sb pd c cl
           | none => (c, cl, Rega.killFlags vllX64IsaR cl st.flags, none)
       | _ => none) =
    (match v with
     | .var x =>
       (Rega.tryCmpMemVar x64Isa (symStToX64 st) co' n x other pd).map fun (c, cl) =>
         match Rega.toSymArg x64Isa (.bits n) other with
         | some sb => Rega.cmpMemRes x64Isa (symStToX64 st) co' n (.var x) sb pd c cl
         | none => (c, cl, Rega.killFlags x64Isa cl (symStToX64 st).flags, none)
     | _ => none) := by
  cases v with
  | imm _ => rfl
  | var x =>
    refine mapOptCl_option_map (tryCmpMemVar_eq st co' n x other pd hno) fun cs cl => ?_
    dsimp only
    rw [vllR_toSymArg_eq]
    cases Rega.toSymArg x64Isa (.bits n) other with
    | none => rw [killFlags_eq]
    | some sb => exact cmpMemRes_eq st co' n (.var x) sb pd cs cl

theorem tryFuseCmp_eq (st : Rega.SymState vllX64IsaR) (vh : VariantHint) {sig ts : List Ty}
    (code : OpCode sig ts) (args : Tup (Arg Rega.VNat) sig)
    (dsts : Tup (PDst Reg64 RegMm CondCode) ts) (hno : regsNoRsp st.regs = true) :
    mapOptCl (Rega.tryFuseCmp vllX64IsaR st vh code args dsts) =
      Rega.tryFuseCmp x64Isa (symStToX64 st) vh code args dsts := by
  cases code with
  | cmp co t m hpf =>
    cases t with
    | bool | float _ | pair _ _ => rfl
    | bits n =>
      cases hpf
      rcases args with ⟨a, b, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
      dsimp only [Rega.tryFuseCmp]
      split
      · rfl
      · refine mapOptCl_or_congr (tryTestFuse_cmp_eq st co n a b pd hno)
          (mapOptCl_or_congr ?_ (mapOptCl_or_congr
            (tryFuseCmpMemHalf_eq st co n a b pd hno)
            (tryFuseCmpMemHalf_eq st co.swap n b a pd hno)))
        cases a <;> cases b <;> try rfl
        · exact tryExtCmp_eq st vh co n _ _ pd hno
        · exact tryExtCmp_eq st vh co.swap n _ _ pd hno
  | _ => rfl

theorem tryLoadSext_eq (st : Rega.SymState vllX64IsaR) (vh : VariantHint) {sig ts : List Ty}
    (code : OpCode sig ts) (args : Tup (Arg Rega.VNat) sig)
    (dsts : Tup (PDst Reg64 RegMm CondCode) ts) (hno : regsNoRsp st.regs = true) :
    mapOptCl (Rega.tryLoadSext vllX64IsaR st vh code args dsts) =
      Rega.tryLoadSext x64Isa (symStToX64 st) vh code args dsts := by
  cases code with
  | sext m n =>
    rcases args with ⟨a, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases a with
    | imm _ => rfl
    | var x =>
      cases pd with
      | vec _ => rfl
      | gpr rd =>
        dsimp only [Rega.tryLoadSext, symStToX64]
        cases st.memDefs.find? x with
        | none => rfl
        | some p =>
          rcases p with ⟨ty, addr⟩
          cases ty with
          | bool | float _ | pair _ _ => rfl
          | bits m' =>
            dsimp only; split
            · refine mapOptCl_or_congr
                (mapOptCl_tryAddr st vh addr hno fun aa _ => vllR_loadSext_eq m n rd aa) ?_
              have hf1 : vllX64GprR.loadSextZextIdx m n rd = fun _ _ _ _ => none :=
                funext fun rb => funext fun ri => funext fun sc => funext fun d =>
                  vllR_loadSextZextIdx_none m n rd rb ri sc d
              have hf2 : x64Isa.gpr.loadSextZextIdx m n rd = fun _ _ _ _ => none :=
                funext fun rb => funext fun ri => funext fun sc => funext fun d =>
                  x64_loadSextZextIdx_none m n rd rb ri sc d
              have h1 : Rega.tryAddrZext vllX64IsaR st addr (vllX64GprR.loadSextZextIdx m n rd) =
                  none := by rw [hf1]; exact vllR_tryAddrZext_none st addr
              have h2 : Rega.tryAddrZext x64Isa (symStToX64 st) addr
                  (x64Isa.gpr.loadSextZextIdx m n rd) = none := by
                rw [hf2]; exact x64_tryAddrZext_none (symStToX64 st) addr
              dsimp only [symStToX64, x64Isa] at h2 ⊢
              rw [h1, h2]; rfl
            · rfl
  | _ => rfl

theorem tryLeaArith_eq (st : Rega.SymState vllX64IsaR) {sig ts : List Ty}
    (code : OpCode sig ts) (args : Tup (Arg Rega.VNat) sig)
    (dsts : Tup (PDst Reg64 RegMm CondCode) ts) :
    mapOptCl (Rega.tryLeaArith vllX64IsaR st code args dsts) =
      Rega.tryLeaArith x64Isa (symStToX64 st) code args dsts := by
  unfold Rega.tryLeaArith
  split
  · dsimp only [symStToX64]
    refine mapOptCl_or_congr ?_ ?_
    · refine mapOptCl_bind_congr (fun ext => ?_)
      rcases ext with ⟨base?, idx, sc, disp⟩
      have hrb :
          (match base? with
           | some b => (Rega.findGprFor vllX64IsaR true st.regs (.var b)).map some
           | none => some none) =
          (match base? with
           | some b => (Rega.findGprFor x64Isa true st.regs (.var b)).map some
           | none => some none) := by
        cases base? with
        | none => rfl
        | some b => dsimp only; rw [findGprFor_eq]
      refine mapOptCl_bind_congr' hrb (fun _ => ?_)
      refine mapOptCl_bind_congr' (findGprFor_eq true st.regs (.var idx)) (fun ri => ?_)
      refine mapOptCl_option_map (vllR_leaArith_eq _ _ ri sc disp _) fun _ _ => ?_
      dsimp only
      rw [vllR_zeroUpper32LeaArith_eq]
    · rw [vllR_tryLeaArithZext_none, x64_tryLeaArithZext_none]; rfl
  · rfl

private theorem normCmpOp_bits (I : Isa) (co : CmpOp) (n : Nat) {hpf}
    (a b : Arg Rega.VNat (.bits n)) (pd : PDst I.Reg I.VReg I.Cond .bool) :
    Rega.normCmpOp (I := I) ⟨.cmp co (.bits n) .bool hpf, (a, b, ())⟩ (pd, ()) =
      let (co', a', b') := Rega.normCmpExpr co n a b
      let ok := match pd with
        | .gpr _ => true
        | .flag cd => I.gpr.condOfCmp? co' == some cd
        | .vec _ => false
      if ok then ⟨.cmp co' (.bits n) .bool hpf, (a', b', ())⟩
      else ⟨.cmp co (.bits n) .bool hpf, (a, b, ())⟩ := rfl

theorem normCmpOp_eq {ts : List Ty} (op : Op Rega.VNat ts)
    (dsts : Tup (PDst Reg64 RegMm CondCode) ts) :
    Rega.normCmpOp (I := vllX64IsaR) op dsts = Rega.normCmpOp (I := x64Isa) op dsts := by
  cases ts with
  | nil => rfl
  | cons t ts' =>
    cases ts' with
    | cons _ _ => cases t <;> rfl
    | nil =>
      cases t with
      | bits _ | float _ | pair _ _ => rfl
      | bool =>
        cases op with
        | mk code args =>
          cases code with
          | cmp co t1 _ h =>
            cases t1 with
            | bool | float _ | pair _ _ =>
              rcases args with ⟨_, ⟨_, ⟨⟩⟩⟩; rcases dsts with ⟨_, ⟨⟩⟩; rfl
            | bits n =>
              rcases args with ⟨a, ⟨b, ⟨⟩⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
              rw [normCmpOp_bits, normCmpOp_bits]
              generalize Rega.normCmpExpr co n a b = p
              rcases p with ⟨co', a', b'⟩
              cases pd with
              | gpr _ => rfl
              | vec _ => rfl
              | flag cd =>
                dsimp only [vllX64IsaR, x64Isa]
                rw [vllR_condOfCmp_eq]
                dsimp only [x64Isa]
                rfl
          | _ => rcases dsts with ⟨_, ⟨⟩⟩; rfl

theorem opNoSameExt_normCmpOp {ts : List Ty} (op : Op Rega.VNat ts)
    (dsts : Tup (PDst Reg64 RegMm CondCode) ts) (hok : opNoSameExt op.code = true) :
    opNoSameExt (Rega.normCmpOp (I := vllX64IsaR) op dsts).code = true := by
  cases ts with
  | nil => exact hok
  | cons t ts' =>
    cases ts' with
    | cons _ _ => cases t <;> exact hok
    | nil =>
      cases t with
      | bits _ | float _ | pair _ _ => exact hok
      | bool =>
        cases op with
        | mk code args =>
          cases code with
          | cmp co t1 _ h =>
            cases t1 with
            | bool | float _ | pair _ _ =>
              rcases args with ⟨_, ⟨_, ⟨⟩⟩⟩; rcases dsts with ⟨_, ⟨⟩⟩; exact hok
            | bits n =>
              rcases args with ⟨a, ⟨b, ⟨⟩⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
              rw [normCmpOp_bits]
              generalize Rega.normCmpExpr co n a b = p
              rcases p with ⟨co', a', b'⟩
              cases pd with
              | gpr _ => rfl
              | vec _ => exact hok
              | flag cd =>
                dsimp only
                have hite : ∀ cflag : Bool,
                    opNoSameExt (if cflag then (⟨.cmp co' (.bits n) .bool h, (a', b', ())⟩ :
                        Op Rega.VNat [.bool])
                      else ⟨.cmp co (.bits n) .bool h, (a, b, ())⟩).code = true :=
                  fun cflag => by cases cflag with | false => exact hok | true => rfl
                exact hite _
          | _ => rcases dsts with ⟨_, ⟨⟩⟩; exact hok

private theorem cmpOpFlags?_cmp (I : Isa) (st : Rega.SymState I) (co : CmpOp) (w : Nat) {hpf}
    (a b : Arg Rega.VNat (.bits w)) (pas : Tup (PArg I.Reg I.VReg I.Cond) [.bits w, .bits w])
    (pd : PDst I.Reg I.VReg I.Cond .bool) (nv : Nat) (cl : FlagMask) :
    Rega.cmpOpFlags? I st (OpCode.cmp co (.bits w) .bool hpf) (a, b, ()) pas (pd, ()) nv cl =
      (if Nat.ble w 64 then
         match I.gpr.cmpFlagsOut? co w pas.1 pas.2.1 pd,
           Rega.toSymArg I (.bits w) a, Rega.toSymArg I (.bits w) b with
         | some lf, some sa, some sb =>
           some (.cmp w (if lf then sa else sb) (if lf then sb else sa) false)
         | _, _, _ => Rega.killFlags I cl st.flags
       else Rega.killFlags I cl st.flags,
       match pd with
       | .gpr _ => if Nat.ble w 64 then
           (I.gpr.cmpFlagsOut? co w pas.1 pas.2.1 pd).bind fun lf =>
             I.gpr.condOfCmp? (if lf then co else co.swap)
         else none
       | _ => none) := rfl

private theorem cmpOpFlags?_bits (I : Isa) (st : Rega.SymState I) (w : Nat) {sig : List Ty}
    (c : OpCode sig [.bits w]) (args : Tup (Arg Rega.VNat) sig)
    (pas : Tup (PArg I.Reg I.VReg I.Cond) sig) (pd : PDst I.Reg I.VReg I.Cond (.bits w))
    (nv : Nat) (cl : FlagMask) :
    Rega.cmpOpFlags? I st c args pas (pd, ()) nv cl =
      (if Nat.ble w 64 && !(cl == FlagMask.none) then
         match I.gpr.aluZeroOut? w c pd with
         | some eqNe => some (.cmp w (.var nv) (.immBits w 0#64) eqNe)
         | none => Rega.killFlags I cl st.flags
       else Rega.killFlags I cl st.flags, none) := rfl

private theorem cmpOpFlags?_boolGpr_step {sig : List Ty} (st : Rega.SymState vllX64IsaR)
    (c : OpCode sig [.bool]) (args : Tup (Arg Rega.VNat) sig)
    (pas : Tup (PArg Reg64 RegMm CondCode) sig) (rd : Reg64) (nv : Nat) (cl : FlagMask)
    (h1 : Rega.cmpOpFlags? vllX64IsaR st c args pas (PDst.gpr rd, ()) nv cl =
      (Rega.killFlags vllX64IsaR cl st.flags, vllX64GprR.boolFlagOut? c pas (.gpr rd)))
    (h2 : Rega.cmpOpFlags? x64Isa (symStToX64 st) c args pas (PDst.gpr rd, ()) nv cl =
      (Rega.killFlags x64Isa cl (symStToX64 st).flags, x64Isa.gpr.boolFlagOut? c pas (.gpr rd))) :
    Rega.cmpOpFlags? vllX64IsaR st c args pas (PDst.gpr rd, ()) nv cl =
      Rega.cmpOpFlags? x64Isa (symStToX64 st) c args pas (PDst.gpr rd, ()) nv cl := by
  rw [h1, h2]; dsimp only [symStToX64]; rw [killFlags_eq, vllR_boolFlagOut?_eq]
  all_goals (first | exact rfl | (dsimp only [x64Isa]; rfl))

theorem cmpOpFlags?_eq (st : Rega.SymState vllX64IsaR) {sig ts : List Ty}
    (code : OpCode sig ts) (args : Tup (Arg Rega.VNat) sig)
    (pas : Tup (PArg Reg64 RegMm CondCode) sig) (dsts : Tup (PDst Reg64 RegMm CondCode) ts)
    (nv : Nat) (cl : FlagMask) :
    Rega.cmpOpFlags? vllX64IsaR st code args pas dsts nv cl =
      Rega.cmpOpFlags? x64Isa (symStToX64 st) code args pas dsts nv cl := by
  cases ts with
  | nil =>
    rw [show Rega.cmpOpFlags? vllX64IsaR st code args pas dsts nv cl =
        (Rega.killFlags vllX64IsaR cl st.flags, none) from rfl,
      show Rega.cmpOpFlags? x64Isa (symStToX64 st) code args pas dsts nv cl =
        (Rega.killFlags x64Isa cl (symStToX64 st).flags, none) from rfl]
    dsimp only [symStToX64]; rw [killFlags_eq]
  | cons t ts' =>
    cases ts' with
    | cons _ _ =>
      rw [show Rega.cmpOpFlags? vllX64IsaR st code args pas dsts nv cl =
          (Rega.killFlags vllX64IsaR cl st.flags, none) from (by cases t <;> rfl),
        show Rega.cmpOpFlags? x64Isa (symStToX64 st) code args pas dsts nv cl =
          (Rega.killFlags x64Isa cl (symStToX64 st).flags, none) from (by cases t <;> rfl)]
      dsimp only [symStToX64]; rw [killFlags_eq]
    | nil =>
      cases t with
      | float _ | pair _ _ =>
        rw [show Rega.cmpOpFlags? vllX64IsaR st code args pas dsts nv cl =
            (Rega.killFlags vllX64IsaR cl st.flags, none) from rfl,
          show Rega.cmpOpFlags? x64Isa (symStToX64 st) code args pas dsts nv cl =
            (Rega.killFlags x64Isa cl (symStToX64 st).flags, none) from rfl]
        dsimp only [symStToX64]; rw [killFlags_eq]
      | bits w =>
        rcases dsts with ⟨pd, ⟨⟩⟩
        rw [cmpOpFlags?_bits vllX64IsaR, cmpOpFlags?_bits x64Isa]
        dsimp only [symStToX64]; rw [killFlags_eq, vllR_aluZeroOut?_eq w code pd]
        all_goals (first | exact rfl | (dsimp only [x64Isa]; rfl))
      | bool =>
        cases code with
        | cmp co t1 _ h =>
          cases t1 with
          | bits w =>
            rcases args with ⟨a, ⟨b, ⟨⟩⟩⟩
            rcases pas with ⟨pa, ⟨pb, ⟨⟩⟩⟩
            rcases dsts with ⟨pd, ⟨⟩⟩
            rw [cmpOpFlags?_cmp vllX64IsaR, cmpOpFlags?_cmp x64Isa]
            dsimp only [symStToX64]
            rw [vllR_cmpFlagsOut?_eq, vllR_toSymArg_eq, vllR_toSymArg_eq,
              vllR_condOfCmp_eq, killFlags_eq]
            cases pd <;> (first | exact rfl | (dsimp only [x64Isa]; rfl))
          | bool | float _ | pair _ _ =>
            rcases dsts with ⟨pd, ⟨⟩⟩
            cases pd with
            | gpr rd => exact cmpOpFlags?_boolGpr_step st _ args pas rd nv cl rfl rfl
            | vec _ | flag _ =>
              rw [show Rega.cmpOpFlags? vllX64IsaR st _ args pas _ nv cl =
                  (Rega.killFlags vllX64IsaR cl st.flags, none) from rfl,
                show Rega.cmpOpFlags? x64Isa (symStToX64 st) _ args pas _ nv cl =
                  (Rega.killFlags x64Isa cl (symStToX64 st).flags, none) from rfl]
              dsimp only [symStToX64]; rw [killFlags_eq]
        | _ =>
          rcases dsts with ⟨pd, ⟨⟩⟩
          cases pd with
          | gpr rd => exact cmpOpFlags?_boolGpr_step st _ args pas rd nv cl rfl rfl
          | vec _ | flag _ =>
            rw [show Rega.cmpOpFlags? vllX64IsaR st _ args pas _ nv cl =
                (Rega.killFlags vllX64IsaR cl st.flags, none) from rfl,
              show Rega.cmpOpFlags? x64Isa (symStToX64 st) _ args pas _ nv cl =
                (Rega.killFlags x64Isa cl (symStToX64 st).flags, none) from rfl]
            dsimp only [symStToX64]; rw [killFlags_eq]

theorem opProducesZ32_eq {sig rs : List Ty} (code : OpCode sig rs)
    (pas : Tup (PArg Reg64 RegMm CondCode) sig) (dsts : Tup (PDst Reg64 RegMm CondCode) rs) :
    Rega.opProducesZ32 vllX64IsaR code pas dsts = Rega.opProducesZ32 x64Isa code pas dsts := by
  unfold Rega.opProducesZ32
  split
  · split
    · rw [vllR_zeroUpper32Op_eq]
    · rfl
  · rfl

theorem reuseCmpPair?_eq (defs : Trie Rega.DefFact) (w : Nat) (lhs rhs : SymArg)
    (n : Nat) (co : CmpOp) (a b : Arg Rega.VNat (.bits n)) :
    Rega.reuseCmpPair? vllX64IsaR defs w lhs rhs n co a b =
      Rega.reuseCmpPair? x64Isa defs w lhs rhs n co a b := by
  dsimp only [Rega.reuseCmpPair?]
  simp only [vllR_toSymArg_eq]

theorem tryReuseFlagCmp_eq (st : Rega.SymState vllX64IsaR) {sig ts : List Ty}
    (code : OpCode sig ts) (args : Tup (Arg Rega.VNat) sig)
    (dsts : Tup (PDst Reg64 RegMm CondCode) ts) :
    mapOptCl (Rega.tryReuseFlagCmp vllX64IsaR st code args dsts) =
      Rega.tryReuseFlagCmp x64Isa (symStToX64 st) code args dsts := by
  dsimp only [Rega.tryReuseFlagCmp, symStToX64]
  split
  · refine mapOptCl_bind_congr' (by rw [reuseCmpPair?_eq]) fun p => ?_
    rcases p with ⟨coBase, sa, sb⟩
    refine mapOptCl_bind_congr fun coUsed => ?_
    split
    · rfl
    · refine mapOptCl_bind_congr' (congrFun vllR_condOfCmp_eq coUsed) fun cc => ?_
      split
      · rw [decEq_beq_congr vllX64IsaR.decEqCond x64Isa.decEqCond]
        split <;> rfl
      · refine mapOptCl_option_map
          (vllR_op_eq (.copy .bool) (.flag cc, ()) (.gpr _, ()) .default rfl)
          fun _ _ => ?_
        dsimp only
        rw [vllR_condReads_eq, killFlags_eq]
      · rfl
  · rfl

private theorem tupDstFlags_eq :
    ∀ {ts : List Ty} (dsts : Tup (PDst Reg64 RegMm CondCode) ts),
      Rega.tupDstFlags (I := vllX64IsaR) dsts = Rega.tupDstFlags (I := x64Isa) dsts
  | [], () => rfl
  | _ :: _, (pd, dsts) => by
    cases pd with
    | gpr _ | vec _ => exact tupDstFlags_eq dsts
    | flag _ => exact congrArg (_ :: ·) (tupDstFlags_eq dsts)

private theorem tryMoviZero_eq (h : x64Isa.Hints) (ip : Nat) (st : Rega.SymState vllX64IsaR)
    {sig ts : List Ty} (code : OpCode sig ts) (args : Tup (Arg Rega.VNat) sig)
    (dsts : Tup (PDst Reg64 RegMm CondCode) ts) :
    (Rega.tryMoviZero vllX64IsaR h ip st code args dsts).map
        (fun (c, cl, z) => (asmX64List c, cl, z)) =
      Rega.tryMoviZero x64Isa h ip (symStToX64 st) code args dsts := by
  dsimp only [Rega.tryMoviZero]
  have hst : Rega.stHasFlagReg (I := vllX64IsaR) st.regs =
      Rega.stHasFlagReg (I := x64Isa) st.regs := by
    dsimp only [Rega.stHasFlagReg]
    exact congrArg (List.any st.regs) (funext fun p => by cases p.2 <;> rfl)
  have hfl : Rega.flagsDeadAt vllX64IsaR h (some ip) st =
      Rega.flagsDeadAt x64Isa h (some ip) (symStToX64 st) := by
    dsimp only [Rega.flagsDeadAt, symStToX64]; rw [hst]
  rw [hfl]
  split
  · rfl
  · have h1 : vllX64GprR.moviDeadFlags? = some vllX64MoviDeadFlags := rfl
    have h2 : x64Gpr.moviDeadFlags? = some x64MoviDeadFlags := rfl
    have hbw : vllX64FrameR.bitWidths = [8, 16, 32, 64] := rfl
    have hemit1 : ∀ rd,
        asmX64List (vllX64MoviDeadFlags rd 0#64).1 = (x64MoviDeadFlags rd 0#64).1 :=
      fun rd => congrArg Prod.fst (asmX64List_vllX64MoviDeadFlags rd 0#64)
    have hemit2 : ∀ rd, (vllX64MoviDeadFlags rd 0#64).2 = (x64MoviDeadFlags rd 0#64).2 :=
      fun rd => congrArg Prod.snd (asmX64List_vllX64MoviDeadFlags rd 0#64)
    cases code with
    | copy t =>
      cases t with
      | bits n =>
        rcases args with ⟨a, ⟨⟩⟩; rcases dsts with ⟨d0, ⟨⟩⟩
        cases a <;> cases d0 <;> try rfl
        dsimp only; rw [h1, h2, hbw]; dsimp only
        split <;> first | rfl | simp only [Option.map_some, hemit1, hemit2]
      | bool =>
        rcases args with ⟨a, ⟨⟩⟩; rcases dsts with ⟨d0, ⟨⟩⟩
        cases a with
        | var _ => rfl
        | imm b =>
          cases b <;> cases d0 <;> first
            | rfl
            | simp only [h1, h2, hbw, Option.map_some, hemit1, hemit2]
      | float _ | pair _ _ => rfl
    | ofBool n =>
      rcases args with ⟨a, ⟨⟩⟩; rcases dsts with ⟨d0, ⟨⟩⟩
      cases a with
      | var _ => rfl
      | imm b =>
        cases b <;> cases d0 <;> try rfl
        dsimp only; rw [h1, h2, hbw]; dsimp only
        split <;> first | rfl | simp only [Option.map_some, hemit1, hemit2]
    | bitcast t u _ =>
      cases t <;> cases u <;> try rfl
      rcases args with ⟨a, ⟨⟩⟩; rcases dsts with ⟨d0, ⟨⟩⟩
      cases a <;> cases d0 <;> try rfl
      dsimp only; rw [h1, h2, hbw]; dsimp only
      split <;> first | rfl | simp only [Option.map_some, hemit1, hemit2]
    | _ => rfl

private theorem mapOptCl_lowerOpBody (st1 : Rega.SymState vllX64IsaR) (h : x64Isa.Hints)
    (nv ip : Nat) {ts : List Ty} (op : Op Rega.VNat ts)
    (dsts : Tup (PDst Reg64 RegMm CondCode) ts)
    (hno : regsNoRsp st1.regs = true) (hok : opNoSameExt op.code = true) :
    let vh := h.variant.getD ip .default
    let dstVecs := tupDstVecs dsts
    let opN := Rega.normCmpOp (I := vllX64IsaR) op dsts
    let opNx := Rega.normCmpOp (I := x64Isa) op dsts
    mapOptCl
      ((((Rega.tryReuseFlagCmp vllX64IsaR st1 op.code op.args dsts <|>
           Rega.tryReuseFlagCmp vllX64IsaR st1 opN.code opN.args dsts).map
          fun (c, cl, fl, ex) => (c, cl, false, false, fl, ex)) <|>
        ((Rega.tryFuseCmp vllX64IsaR st1 vh opN.code opN.args dsts).map
          fun (c, cl, fl, ex) => (c, cl, false, false, fl, ex)) <|>
        ((Rega.tryLoadSext vllX64IsaR st1 vh opN.code opN.args dsts).map
          fun (c, cl) => (c, cl, false, false, Rega.killFlags vllX64IsaR cl st1.flags, none)) <|>
        ((Rega.tryLeaArith vllX64IsaR st1 opN.code opN.args dsts).map
          fun (c, cl, z32) =>
            (c, cl, false, z32, Rega.killFlags vllX64IsaR cl st1.flags, none)) <|>
        ((Rega.tryMoviZero vllX64IsaR h ip st1 opN.code opN.args dsts).map
          fun (c, cl, z32) =>
            (c, cl, false, z32, Rega.killFlags vllX64IsaR cl st1.flags, none)) <|>
        (Rega.pickPArgs vllX64IsaR st1 (Rega.tupDstFlags dsts) opN.args fun pas =>
          if dstVecs.isEmpty && (tupArgVecs pas).isEmpty then
            ((vllX64IsaR.gpr.op opN.code pas dsts vh).map fun (c, cl) =>
              let (fl, ex) := Rega.cmpOpFlags? vllX64IsaR st1 opN.code opN.args pas dsts nv cl
              (c, cl, false, Rega.opProducesZ32 vllX64IsaR opN.code pas dsts, fl, ex)) <|>
            ((vllX64IsaR.vec.vop opN.code pas dsts vh).map fun (c, cl) =>
              (c, cl, true, false, Rega.killFlags vllX64IsaR cl st1.flags, none))
          else (vllX64IsaR.vec.vop opN.code pas dsts vh).map fun (c, cl) =>
            (c, cl, true, false, Rega.killFlags vllX64IsaR cl st1.flags, none)) <|>
        ((Rega.trySlotOp vllX64IsaR h st1 opN.code opN.args dsts).map
          fun (c, cl, z32, fl, ex) => (c, cl, false, z32, fl, ex))) :
        Option (List vllX64IsaR.Directive × FlagMask × Bool × Bool × Option Rega.FlagFact ×
          Option vllX64IsaR.Cond)) =
    ((((Rega.tryReuseFlagCmp x64Isa (symStToX64 st1) op.code op.args dsts <|>
         Rega.tryReuseFlagCmp x64Isa (symStToX64 st1) opNx.code opNx.args dsts).map
        fun (c, cl, fl, ex) => (c, cl, false, false, fl, ex)) <|>
      ((Rega.tryFuseCmp x64Isa (symStToX64 st1) vh opNx.code opNx.args dsts).map
        fun (c, cl, fl, ex) => (c, cl, false, false, fl, ex)) <|>
      ((Rega.tryLoadSext x64Isa (symStToX64 st1) vh opNx.code opNx.args dsts).map
        fun (c, cl) =>
          (c, cl, false, false, Rega.killFlags x64Isa cl (symStToX64 st1).flags, none)) <|>
      ((Rega.tryLeaArith x64Isa (symStToX64 st1) opNx.code opNx.args dsts).map
        fun (c, cl, z32) =>
          (c, cl, false, z32, Rega.killFlags x64Isa cl (symStToX64 st1).flags, none)) <|>
      ((Rega.tryMoviZero x64Isa h ip (symStToX64 st1) opNx.code opNx.args dsts).map
        fun (c, cl, z32) =>
          (c, cl, false, z32, Rega.killFlags x64Isa cl (symStToX64 st1).flags, none)) <|>
      (Rega.pickPArgs x64Isa (symStToX64 st1) (Rega.tupDstFlags dsts) opNx.args fun pas =>
        if dstVecs.isEmpty && (tupArgVecs pas).isEmpty then
          ((x64Isa.gpr.op opNx.code pas dsts vh).map fun (c, cl) =>
            let (fl, ex) :=
              Rega.cmpOpFlags? x64Isa (symStToX64 st1) opNx.code opNx.args pas dsts nv cl
            (c, cl, false, Rega.opProducesZ32 x64Isa opNx.code pas dsts, fl, ex)) <|>
          ((x64Isa.vec.vop opNx.code pas dsts vh).map fun (c, cl) =>
            (c, cl, true, false, Rega.killFlags x64Isa cl (symStToX64 st1).flags, none))
        else (x64Isa.vec.vop opNx.code pas dsts vh).map fun (c, cl) =>
          (c, cl, true, false, Rega.killFlags x64Isa cl (symStToX64 st1).flags, none)) <|>
      ((Rega.trySlotOp x64Isa h (symStToX64 st1) opNx.code opNx.args dsts).map
        fun (c, cl, z32, fl, ex) => (c, cl, false, z32, fl, ex))) :
        Option (List x64Isa.Directive × FlagMask × Bool × Bool × Option Rega.FlagFact ×
          Option x64Isa.Cond)) := by
  dsimp only
  have hnorm : Rega.normCmpOp (I := vllX64IsaR) op dsts = Rega.normCmpOp (I := x64Isa) op dsts :=
    normCmpOp_eq op dsts
  have hokN : opNoSameExt (Rega.normCmpOp (I := vllX64IsaR) op dsts).code = true :=
    opNoSameExt_normCmpOp op dsts hok
  let vh := h.variant.getD ip .default
  let dstVecs := tupDstVecs dsts
  let opN := Rega.normCmpOp (I := vllX64IsaR) op dsts
  have hpick :
      mapOptCl
        (Rega.pickPArgs vllX64IsaR st1 (Rega.tupDstFlags dsts) opN.args fun pas =>
          if dstVecs.isEmpty && (tupArgVecs pas).isEmpty then
            ((vllX64IsaR.gpr.op opN.code pas dsts vh).map fun (c, cl) =>
              let (fl, ex) := Rega.cmpOpFlags? vllX64IsaR st1 opN.code opN.args pas dsts nv cl
              (c, cl, false, Rega.opProducesZ32 vllX64IsaR opN.code pas dsts, fl, ex)) <|>
            ((vllX64IsaR.vec.vop opN.code pas dsts vh).map fun (c, cl) =>
              (c, cl, true, false, Rega.killFlags vllX64IsaR cl st1.flags, none))
          else (vllX64IsaR.vec.vop opN.code pas dsts vh).map fun (c, cl) =>
            (c, cl, true, false, Rega.killFlags vllX64IsaR cl st1.flags, none)) =
      Rega.pickPArgs x64Isa (symStToX64 st1) (Rega.tupDstFlags dsts) opN.args fun pas =>
        if dstVecs.isEmpty && (tupArgVecs pas).isEmpty then
          ((x64Isa.gpr.op opN.code pas dsts vh).map fun (c, cl) =>
            let (fl, ex) :=
              Rega.cmpOpFlags? x64Isa (symStToX64 st1) opN.code opN.args pas dsts nv cl
            (c, cl, false, Rega.opProducesZ32 x64Isa opN.code pas dsts, fl, ex)) <|>
          ((x64Isa.vec.vop opN.code pas dsts vh).map fun (c, cl) =>
            (c, cl, true, false, Rega.killFlags x64Isa cl (symStToX64 st1).flags, none))
        else (x64Isa.vec.vop opN.code pas dsts vh).map fun (c, cl) =>
          (c, cl, true, false, Rega.killFlags x64Isa cl (symStToX64 st1).flags, none) := by
    rw [← tupDstFlags_eq dsts]
    apply mapOptCl_pickPArgs
    intro pas
    cases (dstVecs.isEmpty && (tupArgVecs pas).isEmpty) with
    | true =>
      dsimp only [↓reduceIte]
      exact mapOptCl_or_congr
        (mapOptCl_option_map (vllR_op_eq _ pas dsts _ hokN) fun _ _ => by
          dsimp only; rw [cmpOpFlags?_eq, opProducesZ32_eq])
        (mapOptCl_option_map (vllR_vop_eq _ pas dsts _) fun _ _ => by
          dsimp only; rw [killFlags_eq])
    | false =>
      dsimp only [Bool.false_eq_true, ↓reduceIte]
      exact mapOptCl_option_map (vllR_vop_eq _ pas dsts _) fun _ _ => by
        dsimp only; rw [killFlags_eq]
  rw [← hnorm]
  exact mapOptCl_or_congr
    (mapOptCl_option_map
      (mapOptCl_or_congr (tryReuseFlagCmp_eq st1 op.code op.args dsts)
        (tryReuseFlagCmp_eq st1 _ _ dsts))
      (fun _ _ => rfl))
    (mapOptCl_or_congr
      (mapOptCl_option_map (tryFuseCmp_eq st1 _ _ _ dsts hno) fun _ _ => rfl)
      (mapOptCl_or_congr
        (mapOptCl_option_map (tryLoadSext_eq st1 _ _ _ dsts hno) fun _ _ => by
          dsimp only; rw [killFlags_eq])
        (mapOptCl_or_congr
          (mapOptCl_option_map (tryLeaArith_eq st1 _ _ dsts) fun _ ⟨cl, z32⟩ => by
            dsimp only; rw [killFlags_eq])
          (mapOptCl_or_congr
            (mapOptCl_option_map (tryMoviZero_eq h ip st1 _ _ dsts) fun _ ⟨cl, z32⟩ => by
              dsimp only; rw [killFlags_eq])
            (mapOptCl_or_congr hpick
              (mapOptCl_option_map (trySlotOp_eq h st1 _ _ dsts) fun _ _ => rfl))))))

theorem lowerOp_eq_and_noRsp (h : x64Isa.Hints) (hs : savedNoRsp h.saved = true)
    (nv ip : Nat) (st1 : Rega.SymState vllX64IsaR) {ts : List Ty} (op : Op Rega.VNat ts)
    (deferFuse : Bool) (hno : regsNoRsp st1.regs = true) (hok : opNoSameExt op.code = true) :
    mapOptSt (Rega.lowerOp vllX64IsaR h nv ip st1 op deferFuse) =
      Rega.lowerOp x64Isa h nv ip (symStToX64 st1) op deferFuse ∧
    (∀ c0 st', Rega.lowerOp vllX64IsaR h nv ip st1 op deferFuse = some (c0, st') →
      regsNoRsp st'.regs = true) := by
  dsimp only [Rega.lowerOp]
  cases deferFuse with
  | true =>
    try dsimp only [↓reduceIte, Bool.true_eq_false]
    cases Rega.recordBoolDef st1.defs op.code op.args with
    | some df =>
      refine ⟨rfl, fun _ _ he => by cases he; exact hno⟩
    | none =>
      cases Rega.recordDef st1.defs op.code op.args with
      | none => exact ⟨rfl, fun _ _ he => by cases he⟩
      | some df =>
        refine ⟨rfl, fun _ _ he => by cases he; exact hno⟩
  | false =>
    try dsimp only [Bool.false_eq_true, ↓reduceIte]
    cases h.elide.getD ip false with
    | true =>
      cases Rega.recordDef st1.defs op.code op.args with
      | none => exact ⟨rfl, fun _ _ he => by cases he⟩
      | some df => exact ⟨rfl, fun _ _ he => by cases he; exact hno⟩
    | false =>
      obtain ⟨hd_eq, hd_no⟩ := resolveDsts_eq_and_noRsp h hs ts nv
      cases hd : Rega.resolveDsts vllX64IsaR h ts nv with
      | none =>
        have hdx : Rega.resolveDsts x64Isa h ts nv = none := by rw [← hd_eq, hd]
        rw [hdx]; exact ⟨rfl, fun _ _ he => by cases he⟩
      | some dsts =>
        have hdn : dstsNoRsp dsts = true := hd_no dsts hd
        have hdx : Rega.resolveDsts x64Isa h ts nv = some dsts := by rw [← hd_eq, hd]
        dsimp only [Option.bind]
        rw [hdx]
        dsimp only [Option.bind, symStToX64]
        rw [elideZext32?_eq, elideTrunc?_eq]
        cases hez : Rega.elideZext32? x64Isa st1.regs st1.zeroExt32 op.code op.args dsts with
        | true =>
          simp only [Bool.false_eq_true, ↓reduceIte, mapOptSt, Option.map_some, symStToX64,
            asmX64List, List.flatMap, List.map_nil, List.flatten_nil]
          cases ts with
          | nil => exact ⟨rfl, fun _ _ he => by cases he; exact hno⟩
          | cons t ts' =>
            cases ts' with
            | cons _ _ => exact ⟨rfl, fun _ _ he => by cases he; exact hno⟩
            | nil =>
              rcases dsts with ⟨pd, ⟨⟩⟩
              cases pd with
              | gpr rd =>
                exact ⟨rfl, fun _ _ he => by
                  cases he; exact Bool.and_eq_true_iff.mpr ⟨(Bool.and_eq_true_iff.mp hdn).1, hno⟩⟩
              | vec _ | flag _ => exact ⟨rfl, fun _ _ he => by cases he; exact hno⟩
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          cases het : Rega.elideTrunc? x64Isa st1.regs op.code op.args dsts with
          | true =>
            simp only [↓reduceIte, mapOptSt, Option.map_some, symStToX64, asmX64List,
              List.flatMap, List.map_nil, List.flatten_nil]
            cases ts with
            | nil => exact ⟨rfl, fun _ _ he => by cases he; exact hno⟩
            | cons t ts' =>
              cases ts' with
              | cons _ _ => exact ⟨rfl, fun _ _ he => by cases he; exact hno⟩
              | nil =>
                rcases dsts with ⟨pd, ⟨⟩⟩
                cases pd with
                | gpr rd =>
                  exact ⟨rfl, fun _ _ he => by
                    cases he
                    exact Bool.and_eq_true_iff.mpr ⟨(Bool.and_eq_true_iff.mp hdn).1, hno⟩⟩
                | vec _ | flag _ => exact ⟨rfl, fun _ _ he => by cases he; exact hno⟩
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            have hbody := mapOptCl_lowerOpBody st1 h nv ip op dsts hno hok
            cases hres :
                ((((Rega.tryReuseFlagCmp vllX64IsaR st1 op.code op.args dsts <|>
                     Rega.tryReuseFlagCmp vllX64IsaR st1
                       (Rega.normCmpOp (I := vllX64IsaR) op dsts).code
                       (Rega.normCmpOp (I := vllX64IsaR) op dsts).args dsts).map
                    fun (c, cl, fl, ex) => (c, cl, false, false, fl, ex)) <|>
                  ((Rega.tryFuseCmp vllX64IsaR st1 (h.variant.getD ip .default)
                      (Rega.normCmpOp (I := vllX64IsaR) op dsts).code
                      (Rega.normCmpOp (I := vllX64IsaR) op dsts).args dsts).map
                    fun (c, cl, fl, ex) => (c, cl, false, false, fl, ex)) <|>
                  ((Rega.tryLoadSext vllX64IsaR st1 (h.variant.getD ip .default)
                      (Rega.normCmpOp (I := vllX64IsaR) op dsts).code
                      (Rega.normCmpOp (I := vllX64IsaR) op dsts).args dsts).map
                    fun (c, cl) =>
                      (c, cl, false, false, Rega.killFlags vllX64IsaR cl st1.flags, none)) <|>
                  ((Rega.tryLeaArith vllX64IsaR st1
                      (Rega.normCmpOp (I := vllX64IsaR) op dsts).code
                      (Rega.normCmpOp (I := vllX64IsaR) op dsts).args dsts).map
                    fun (c, cl, z32) =>
                      (c, cl, false, z32, Rega.killFlags vllX64IsaR cl st1.flags, none)) <|>
                  ((Rega.tryMoviZero vllX64IsaR h ip st1
                      (Rega.normCmpOp (I := vllX64IsaR) op dsts).code
                      (Rega.normCmpOp (I := vllX64IsaR) op dsts).args dsts).map
                    fun (c, cl, z32) =>
                      (c, cl, false, z32, Rega.killFlags vllX64IsaR cl st1.flags, none)) <|>
                  (Rega.pickPArgs vllX64IsaR st1 (Rega.tupDstFlags dsts)
                      (Rega.normCmpOp (I := vllX64IsaR) op dsts).args fun pas =>
                    if (tupDstVecs dsts).isEmpty && (tupArgVecs pas).isEmpty then
                      ((vllX64IsaR.gpr.op (Rega.normCmpOp (I := vllX64IsaR) op dsts).code
                          pas dsts (h.variant.getD ip .default)).map fun (c, cl) =>
                        let (fl, ex) := Rega.cmpOpFlags? vllX64IsaR st1
                          (Rega.normCmpOp (I := vllX64IsaR) op dsts).code
                          (Rega.normCmpOp (I := vllX64IsaR) op dsts).args pas dsts nv cl
                        (c, cl, false, Rega.opProducesZ32 vllX64IsaR
                          (Rega.normCmpOp (I := vllX64IsaR) op dsts).code pas dsts, fl, ex)) <|>
                      ((vllX64IsaR.vec.vop (Rega.normCmpOp (I := vllX64IsaR) op dsts).code
                          pas dsts (h.variant.getD ip .default)).map fun (c, cl) =>
                        (c, cl, true, false, Rega.killFlags vllX64IsaR cl st1.flags, none))
                    else (vllX64IsaR.vec.vop (Rega.normCmpOp (I := vllX64IsaR) op dsts).code
                        pas dsts (h.variant.getD ip .default)).map fun (c, cl) =>
                      (c, cl, true, false, Rega.killFlags vllX64IsaR cl st1.flags, none)) <|>
                  ((Rega.trySlotOp vllX64IsaR h st1
                      (Rega.normCmpOp (I := vllX64IsaR) op dsts).code
                      (Rega.normCmpOp (I := vllX64IsaR) op dsts).args dsts).map
                    fun (c, cl, z32, fl, ex) => (c, cl, false, z32, fl, ex))) :
                  Option (List vllX64IsaR.Directive × FlagMask × Bool × Bool ×
                    Option Rega.FlagFact × Option vllX64IsaR.Cond)) with
            | none =>
              rw [← hbody, hres, mapOptCl_none]
              exact ⟨rfl, fun _ _ he => by cases he⟩
            | some r =>
              rcases r with ⟨code, clob, isVec, z32, flagsPost, extraBool?⟩
              rw [← hbody, hres, mapOptCl_some]
              dsimp only [Option.map, mapOptSt, symStToX64]
              have hk : regsNoRsp (Rega.killRegs vllX64IsaR
                  (tupDstGprs dsts ++ vllX64FrameR.scratch)
                  (if isVec then tupDstVecs dsts ++ vllX64VecR.vecScratch else [])
                  clob st1.regs) = true := regsNoRsp_killRegs _ hno
              have hbd := bindDsts_noRsp dsts nv
                (Rega.killRegs vllX64IsaR (tupDstGprs dsts ++ vllX64FrameR.scratch)
                  (if isVec then tupDstVecs dsts ++ vllX64VecR.vecScratch else [])
                  clob st1.regs, st1.vecWidths) hdn hk
              refine ⟨?_, fun _ _ he => by
                cases he
                cases ts with
                | nil => cases z32 <;> exact hbd
                | cons t ts' =>
                  cases ts' with
                  | cons _ _ =>
                    cases t <;> cases z32 <;> first
                      | exact hbd
                      | (dsimp only; split <;> first | simp_all | exact hbd)
                  | nil =>
                    rcases dsts with ⟨pd, ⟨⟩⟩
                    cases t with
                    | bool =>
                      cases extraBool? with
                      | none => cases z32 <;> exact hbd
                      | some _ => cases z32 <;> exact regsNoRsp_cons_flag hbd
                    | float _ | pair _ _ => cases z32 <;> exact hbd
                    | bits w =>
                      cases z32 with
                      | false => exact hbd
                      | true =>
                        cases pd with
                        | vec _ =>
                          dsimp only; split <;> first | simp_all | exact hbd
                        | gpr rd =>
                          by_cases hw : w = 32
                          · subst hw
                            exact regsNoRsp_cons_gprZ
                              (by intro h; subst h; exact absurd hdn (by decide)) hk
                          · dsimp only; split <;> first | exact hbd | simp_all⟩
              rw [vllR_scratch_eq, vllR_vecScratch_eq, killRegs_eq, killZeroExt_eq, bindDsts_eq]
              dsimp only [x64Isa, x64Frame, x64Vec]
              cases ts with
              | nil => rfl
              | cons t ts' =>
                cases ts' with
                | cons _ _ =>
                  cases z32 <;> cases extraBool? <;>
                    (dsimp only; first | rfl | (split <;> first | rfl | simp_all))
                | nil =>
                  rcases dsts with ⟨pd, ⟨⟩⟩
                  cases t with
                  | bool => cases extraBool? <;> rfl
                  | float _ | pair _ _ => rfl
                  | bits w =>
                    by_cases hw : w = 32
                    · subst hw; cases z32 <;> cases pd <;> rfl
                    · cases z32 <;> cases pd <;>
                        first
                        | rfl
                        | (simp only [↓reduceIte] <;>
                           first | rfl | (split <;> first
                             | rfl
                             | (rename_i _ _ h1 _; cases h1 <;> exact absurd rfl hw)))

private theorem opNoSameExt_false_x64_tryGprOp_none {sig ts : List Ty}
    (code : OpCode sig ts) (pas : Tup (PArg Reg64 RegMm CondCode) sig)
    (dsts : Tup (PDst Reg64 RegMm CondCode) ts) (vh : VariantHint)
    (hfalse : opNoSameExt code = false) :
    x64Isa.gpr.op code pas dsts vh = none := by
  cases h : x64Isa.gpr.op code pas dsts vh with
  | none => rfl
  | some p =>
    exfalso
    cases code <;> try simp [opNoSameExt] at hfalse
    all_goals
      rename_i m n
      have hmn : m = n := by simpa [opNoSameExt] using hfalse
      subst hmn
      rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
      cases pd with
      | vec _ => cases h
      | gpr rd =>
        dsimp only [x64Isa, x64Gpr, x64Op, x64OpIns, opZextIns, opSextIns, opTruncIns,
          emitCleanPair] at h
        have hlt : Nat.ble (m + 1) m = false := by
          cases h1 : Nat.ble (m + 1) m
          · rfl
          · have := Nat.ble_eq.mp h1; omega
        rw [hlt] at h; simp at h

private theorem opNoSameExt_false_normCmpOp {ts : List Ty} (I : Isa) (op : Op Rega.VNat ts)
    (dsts : Tup (PDst I.Reg I.VReg I.Cond) ts) (hfalse : opNoSameExt op.code = false) :
    Rega.normCmpOp (I := I) op dsts = op := by
  cases op with
  | mk code args =>
    cases code <;> try simp [opNoSameExt] at hfalse
    all_goals
      rename_i m n
      have hmn : m = n := by simpa [opNoSameExt] using hfalse
      subst hmn
      rfl

private theorem opNoSameExt_false_tryReuseFlagCmp_none (I : Isa) (st : Rega.SymState I)
    {sig ts : List Ty} (code : OpCode sig ts) (args : Tup (Arg Rega.VNat) sig)
    (dsts : Tup (PDst I.Reg I.VReg I.Cond) ts) (hfalse : opNoSameExt code = false) :
    Rega.tryReuseFlagCmp I st code args dsts = none := by
  cases code <;> try simp [opNoSameExt] at hfalse
  all_goals
    rcases args with ⟨_, ⟨⟩⟩
    rcases dsts with ⟨_, ⟨⟩⟩
    simp [Rega.tryReuseFlagCmp]

private theorem opNoSameExt_false_tryFuseCmp_none (I : Isa) (st : Rega.SymState I)
    (vh : VariantHint) {sig ts : List Ty} (code : OpCode sig ts) (args : Tup (Arg Rega.VNat) sig)
    (dsts : Tup (PDst I.Reg I.VReg I.Cond) ts) (hfalse : opNoSameExt code = false) :
    Rega.tryFuseCmp I st vh code args dsts = none := by
  cases code <;> try simp [opNoSameExt] at hfalse
  all_goals rfl

private theorem opNoSameExt_false_trySlotOp_none (I : Isa) (h : I.Hints) (st : Rega.SymState I)
    {sig ts : List Ty} (code : OpCode sig ts) (args : Tup (Arg Rega.VNat) sig)
    (dsts : Tup (PDst I.Reg I.VReg I.Cond) ts) (hfalse : opNoSameExt code = false) :
    Rega.trySlotOp I h st code args dsts = none := by
  cases code <;> try simp [opNoSameExt] at hfalse
  all_goals rfl

private theorem opNoSameExt_false_x64_tryLeaArith_none (st : Rega.SymState x64Isa)
    {sig ts : List Ty} (code : OpCode sig ts) (args : Tup (Arg Rega.VNat) sig)
    (dsts : Tup (PDst Reg64 RegMm CondCode) ts) (hfalse : opNoSameExt code = false) :
    Rega.tryLeaArith x64Isa st code args dsts = none := by
  cases code <;> try simp [opNoSameExt] at hfalse
  all_goals
    rename_i m n
    have hmn : m = n := by simpa [opNoSameExt] using hfalse
    subst hmn
    rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd with
    | vec _ => rfl
    | gpr rd =>
      dsimp only [Rega.tryLeaArith]
      rw [x64_tryLeaArithZext_none]
      rw [show Rega.extractLea64 st.defs _ args = none from rfl,
          show Rega.extractLea32 st.defs _ args = none from rfl]
      simp

private theorem opNoSameExt_false_x64_pickPArgs_none (st : Rega.SymState x64Isa) (nv : Nat)
    (vh : VariantHint) {sig ts : List Ty} (code : OpCode sig ts) (args : Tup (Arg Rega.VNat) sig)
    (dsts : Tup (PDst Reg64 RegMm CondCode) ts) (hfalse : opNoSameExt code = false) :
    Rega.pickPArgs x64Isa st (Rega.tupDstFlags dsts) args (fun pas =>
      if (tupDstVecs dsts).isEmpty && (tupArgVecs pas).isEmpty then
        ((x64Isa.gpr.op code pas dsts vh).map fun (c, cl) =>
          let (fl, ex) := Rega.cmpOpFlags? x64Isa st code args pas dsts nv cl
          (c, cl, false, Rega.opProducesZ32 x64Isa code pas dsts, fl, ex)) <|>
        ((x64Isa.vec.vop code pas dsts vh).map fun (c, cl) =>
          (c, cl, true, false, Rega.killFlags x64Isa cl st.flags, none))
      else
        (x64Isa.vec.vop code pas dsts vh).map fun (c, cl) =>
          (c, cl, true, false, Rega.killFlags x64Isa cl st.flags, none)) = none := by
  have hk : ∀ pas,
      (if (tupDstVecs dsts).isEmpty && (tupArgVecs pas).isEmpty then
        ((x64Isa.gpr.op code pas dsts vh).map fun (c, cl) =>
          let (fl, ex) := Rega.cmpOpFlags? x64Isa st code args pas dsts nv cl
          (c, cl, false, Rega.opProducesZ32 x64Isa code pas dsts, fl, ex)) <|>
        ((x64Isa.vec.vop code pas dsts vh).map fun (c, cl) =>
          (c, cl, true, false, Rega.killFlags x64Isa cl st.flags, none))
      else
        (x64Isa.vec.vop code pas dsts vh).map fun (c, cl) =>
          (c, cl, true, false, Rega.killFlags x64Isa cl st.flags, none)) = none := by
    intro pas
    have hg := opNoSameExt_false_x64_tryGprOp_none code pas dsts vh hfalse
    have hv : x64Isa.vec.vop code pas dsts vh = none := by
      cases code <;> try simp [opNoSameExt] at hfalse
      all_goals rfl
    rw [hg, hv]
    split <;> rfl
  exact pickPArgs_const_none x64Isa st _ args _ hk

private theorem opNoSameExt_false_tryMoviZero_none (I : Isa) (h : I.Hints) (ip : Nat)
    (st : Rega.SymState I) {sig ts : List Ty} (code : OpCode sig ts)
    (args : Tup (Arg Rega.VNat) sig) (dsts : Tup (PDst I.Reg I.VReg I.Cond) ts)
    (hfalse : opNoSameExt code = false) :
    Rega.tryMoviZero I h ip st code args dsts = none := by
  dsimp only [Rega.tryMoviZero]
  split
  · rfl
  · cases I.gpr.moviDeadFlags?
    · rfl
    · cases code <;> simp [opNoSameExt] at hfalse <;> rfl

theorem lowerOp_of_x64_some (h : x64Isa.Hints) (hs : savedNoRsp h.saved = true)
    (nv ip : Nat) (st1 : Rega.SymState vllX64IsaR) {ts : List Ty} (op : Op Rega.VNat ts)
    (deferFuse : Bool) (hno : regsNoRsp st1.regs = true)
    {ds : List _root_.Directive} {stx' : Rega.SymState x64Isa}
    (hx : Rega.lowerOp x64Isa h nv ip (symStToX64 st1) op deferFuse = some (ds, stx')) :
    ∃ cs st', Rega.lowerOp vllX64IsaR h nv ip st1 op deferFuse = some (cs, st') ∧
      asmX64List cs = ds ∧ symStToX64 st' = stx' ∧ regsNoRsp st'.regs = true := by
  by_cases hok : opNoSameExt op.code = true
  · obtain ⟨hl, hp⟩ := lowerOp_eq_and_noRsp h hs nv ip st1 op deferFuse hno hok
    rw [hx] at hl
    rcases Option.map_eq_some_iff.mp hl with ⟨⟨cs, st'⟩, hcs, hpe⟩
    cases hpe
    exact ⟨cs, st', hcs, rfl, rfl, hp cs st' hcs⟩
  · have hfalse : opNoSameExt op.code = false := Bool.eq_false_iff.mpr hok
    cases op with
    | mk code args =>
      dsimp only [opNoSameExt] at hfalse
      dsimp only [Rega.lowerOp] at hx ⊢
      cases deferFuse with
      | true =>
        cases hrb : Rega.recordBoolDef st1.defs code args <;> simp [hrb] at hx
        · cases hrec : Rega.recordDef st1.defs code args <;> simp [hrec] at hx
          rcases hx with ⟨rfl, rfl⟩
          exact ⟨[], _, rfl, rfl, rfl, hno⟩
        · rcases hx with ⟨rfl, rfl⟩
          exact ⟨[], _, rfl, rfl, rfl, hno⟩
      | false =>
        cases he : h.elide.getD ip false with
        | true =>
          simp only [he, ↓reduceIte] at hx ⊢
          cases hrec : Rega.recordDef st1.defs code args <;> simp [hrec] at hx
          rcases hx with ⟨rfl, rfl⟩
          exact ⟨[], { st1 with defs := st1.defs.insert nv _ }, rfl, rfl, rfl, hno⟩
        | false =>
          simp only [he, Bool.false_eq_true, ↓reduceIte] at hx ⊢
          obtain ⟨hd_eq, hd_no⟩ := resolveDsts_eq_and_noRsp h hs ts nv
          cases hdx : Rega.resolveDsts x64Isa h ts nv with
          | none => rw [hdx] at hx; cases hx
          | some dsts =>
            have hd : Rega.resolveDsts vllX64IsaR h ts nv = some dsts := by rw [hd_eq, hdx]
            have hdn := hd_no dsts hd
            rw [hdx] at hx; rw [hd]
            dsimp only [Option.bind] at hx ⊢
            rw [elideZext32?_eq, elideTrunc?_eq]
            cases hez : Rega.elideZext32? x64Isa st1.regs st1.zeroExt32 code args dsts with
            | true =>
              simp only [hez, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hx
              simp only [↓reduceIte]
              rcases hx with ⟨rfl, rfl⟩
              cases ts with
              | nil => exact ⟨[], _, rfl, rfl, by dsimp only [symStToX64], hno⟩
              | cons _ ts' =>
                cases ts' with
                | cons _ _ => exact ⟨[], _, rfl, rfl, by dsimp only [symStToX64], hno⟩
                | nil =>
                  rcases dsts with ⟨pd, ⟨⟩⟩
                  cases pd with
                  | gpr rd =>
                    refine ⟨[], _, rfl, rfl, by dsimp only [symStToX64], ?_⟩
                    exact Bool.and_eq_true_iff.mpr ⟨(Bool.and_eq_true_iff.mp hdn).1, hno⟩
                  | vec _ | flag _ =>
                    exact ⟨[], _, rfl, rfl, by dsimp only [symStToX64], hno⟩
            | false =>
              simp only [hez, Bool.false_eq_true, ↓reduceIte] at hx ⊢
              cases het : Rega.elideTrunc? x64Isa st1.regs code args dsts with
              | true =>
                simp only [het, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hx
                simp only [↓reduceIte]
                rcases hx with ⟨rfl, rfl⟩
                cases ts with
                | nil => exact ⟨[], _, rfl, rfl, by dsimp only [symStToX64], hno⟩
                | cons _ ts' =>
                  cases ts' with
                  | cons _ _ => exact ⟨[], _, rfl, rfl, by dsimp only [symStToX64], hno⟩
                  | nil =>
                    rcases dsts with ⟨pd, ⟨⟩⟩
                    cases pd with
                    | gpr rd =>
                      refine ⟨[], _, rfl, rfl, by dsimp only [symStToX64], ?_⟩
                      exact Bool.and_eq_true_iff.mpr ⟨(Bool.and_eq_true_iff.mp hdn).1, hno⟩
                    | vec _ | flag _ =>
                      exact ⟨[], _, rfl, rfl, by dsimp only [symStToX64], hno⟩
              | false =>
                simp only [het, Bool.false_eq_true, ↓reduceIte] at hx ⊢
                have hnv := opNoSameExt_false_normCmpOp vllX64IsaR ⟨code, args⟩ dsts hfalse
                have hnx := opNoSameExt_false_normCmpOp x64Isa ⟨code, args⟩ dsts hfalse
                rw [hnx] at hx; rw [hnv]
                rw [opNoSameExt_false_tryReuseFlagCmp_none x64Isa (symStToX64 st1) code args dsts
                    hfalse,
                  opNoSameExt_false_tryFuseCmp_none x64Isa (symStToX64 st1) _ code args dsts
                    hfalse] at hx
                rw [opNoSameExt_false_tryReuseFlagCmp_none vllX64IsaR st1 code args dsts hfalse,
                  opNoSameExt_false_tryFuseCmp_none vllX64IsaR st1 _ code args dsts hfalse]
                simp only [Option.map_none] at hx ⊢
                have hx_ls := tryLoadSext_eq st1 (h.variant.getD ip .default) code args dsts hno
                cases hls : Rega.tryLoadSext vllX64IsaR st1 (h.variant.getD ip .default) code args
                    dsts with
                | none =>
                  have hlsx : Rega.tryLoadSext x64Isa (symStToX64 st1) (h.variant.getD ip .default)
                      code args dsts = none := by rw [← hx_ls, hls]; rfl
                  rw [hlsx,
                    opNoSameExt_false_x64_tryLeaArith_none (symStToX64 st1) code args dsts hfalse,
                    opNoSameExt_false_tryMoviZero_none x64Isa h ip (symStToX64 st1) code args dsts
                      hfalse,
                    opNoSameExt_false_x64_pickPArgs_none (symStToX64 st1) nv _ code args dsts
                      hfalse,
                    opNoSameExt_false_trySlotOp_none x64Isa h (symStToX64 st1) code args dsts
                      hfalse] at hx
                  simp at hx
                | some p =>
                  rcases p with ⟨cs0, cl⟩
                  have hlsx : Rega.tryLoadSext x64Isa (symStToX64 st1) (h.variant.getD ip .default)
                      code args dsts = some (asmX64List cs0, cl) := by rw [← hx_ls, hls]; rfl
                  rw [hlsx] at hx
                  dsimp only [Option.map] at hx ⊢
                  rcases Option.some.inj hx with ⟨rfl, rfl⟩
                  refine ⟨cs0, _, rfl, rfl, ?_, ?_⟩
                  · cases ts with
                    | nil =>
                      dsimp only [symStToX64]
                      rw [vllR_scratch_eq, vllR_vecScratch_eq, killRegs_eq, killFlags_eq,
                        killZeroExt_eq, bindDsts_eq]
                      all_goals (first | exact rfl | (dsimp only [x64Isa, x64Frame, x64Vec]; rfl))
                    | cons t ts' =>
                      cases ts' with
                      | cons _ _ =>
                        cases t <;>
                        (dsimp only [symStToX64]
                         rw [vllR_scratch_eq, vllR_vecScratch_eq, killRegs_eq, killFlags_eq,
                           killZeroExt_eq, bindDsts_eq]
                         all_goals
                           (first | exact rfl | (dsimp only [x64Isa, x64Frame, x64Vec]; rfl)))
                      | nil =>
                        cases t <;>
                        (rcases dsts with ⟨pd, ⟨⟩⟩; cases pd <;>
                         (dsimp only [symStToX64]
                          rw [vllR_scratch_eq, vllR_vecScratch_eq, killRegs_eq, killFlags_eq,
                            killZeroExt_eq, bindDsts_eq]
                          all_goals
                            (first | exact rfl | (dsimp only [x64Isa, x64Frame, x64Vec]; rfl))))
                  · dsimp only
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    have hk : regsNoRsp (Rega.killRegs vllX64IsaR
                        (tupDstGprs dsts ++ vllX64FrameR.scratch) [] cl st1.regs) = true :=
                      regsNoRsp_killRegs _ hno
                    have hbd := bindDsts_noRsp dsts nv
                      (Rega.killRegs vllX64IsaR (tupDstGprs dsts ++ vllX64FrameR.scratch) []
                        cl st1.regs, st1.vecWidths) hdn hk
                    cases ts with
                    | nil => exact hbd
                    | cons t ts' =>
                      cases ts' with
                      | cons _ _ => cases t <;> exact hbd
                      | nil =>
                        rcases dsts with ⟨pd, ⟨⟩⟩
                        cases t <;> cases pd <;> exact hbd

end LeanQbe.T.Amd64
